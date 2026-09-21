$(
###############################################################################
  BASIC ORDER THEORY
###############################################################################
$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Dual of an order structure
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c ODual $.

  $( Class function defining dual orders. $)
  codu $a class ODual $.

  $( Define the dual of an ordered structure, which replaces the order
     component of the structure with its reverse.  See ~ odubas , ~ oduleval ,
     and ~ oduleg for its principal properties.

     _EDITORIAL_: likely usable to simplify many lattice proofs, as it allows
     for duality arguments to be formalized; for instance ~ latmass .
     (Contributed by Stefan O'Rear, 29-Jan-2015.) $)
  df-odu $a |- ODual = ( w e. _V |->
      ( w sSet <. ( le ` ndx ) , `' ( le ` w ) >. ) ) $.

  ${
    $d D a $.  $d .<_ a $.  $d O a $.  $d G a $.  $d A a $.  $d B a $.
    oduval.d $e |- D = ( ODual ` O ) $.

    ${
      oduval.l $e |- .<_ = ( le ` O ) $.
      $( Value of an order dual structure.  (Contributed by Stefan O'Rear,
         29-Jan-2015.) $)
      oduval $p |- D = ( O sSet <. ( le ` ndx ) , `' .<_ >. ) $=
        ( va codu cfv cnx cple ccnv cop csts co cvv wcel wceq cv id fveq2 fvmpt
        cnveqd opeq2d oveq12d df-odu ovex wn c0 reldmsets ovprc1 eqtr4d pm2.61i
        fvprc cnveqi opeq2i oveq2i 3eqtr4i ) CGHZCIJHZCJHZKZLZMNZACUSBKZLZMNCOP
        ZURVCQFCFRZUSVGJHZKZLZMNVCOGVGCQZVGCVJVBMVKSVKVIVAUSVKVHUTVGCJTUBUCUDFU
        ECVBMUFUAVFUGURUHVCCGUMCVBMUIUJUKULDVEVBCMVDVAUSBUTEUNUOUPUQ $.

      $( Value of the less-equal relation in an order dual structure.
         (Contributed by Stefan O'Rear, 29-Jan-2015.) $)
      oduleval $p |- `' .<_ = ( le ` D ) $=
        ( cple cfv ccnv cnx cop csts co cvv wcel wceq fvex cnvex pleid setsid
        c0 mpan2 str0 fvprc cnveqd cnv0 eqtrdi reldmsets ovprc1 3eqtr4a pm2.61i
        wn fveq2d cnveqi eqid oduval fveq2i 3eqtr4i ) CFGZHZCIFGZUSJZKLZFGZBHAF
        GCMNZUSVCOZVDUSMNVEURCFPQMUSFMCRSUAVDUKZTTFGUSVCFUTRUBVFUSTHTVFURTCFUCU
        DUEUFVFVBTFCVAKUGUHULUIUJBUREUMAVBFAURCDURUNUOUPUQ $.

      oduleg.g $e |- G = ( le ` D ) $.
      $( Truth of the less-equal relation in an order dual structure.
         (Contributed by Stefan O'Rear, 29-Jan-2015.) $)
      oduleg $p |- ( ( A e. V /\ B e. W ) -> ( A G B <-> B .<_ A ) ) $=
        ( wbr ccnv wcel wa cple cfv oduleval eqtr4i breqi brcnvg bitrid ) ABDLA
        BEMZLAGNBHNOBAELABDUCDCPQUCKCEFIJRSTABGHEUAUB $.
    $}

    odubas.b $e |- B = ( Base ` O ) $.
    $( Base set of an order dual structure.  (Contributed by Stefan O'Rear,
       29-Jan-2015.)  (Proof shortened by AV, 12-Nov-2024.) $)
    odubas $p |- B = ( Base ` D ) $=
      ( cbs cfv cnx cple ccnv csts co baseid plendxnbasendx necomi setsnid eqid
      cop oduval fveq2i 3eqtr4i ) CFGCHIGZCIGZJZRKLZFGABFGUDUBFCMUBHFGNOPEBUEFB
      UCCDUCQSTUA $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Preordered sets and directed sets
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c Proset Dirset $.

  $( Extend class notation with the class of all prosets. $)
  cproset $a class Proset $.

  $( Extend class notation with the class of all directed sets. $)
  cdrs $a class Dirset $.

  ${
    $d f b r x y z $.
    $( Define the class of preordered sets, or prosets.  A proset is a set
       equipped with a preorder, that is, a transitive and reflexive relation.

       Preorders are a natural generalization of partial orders which need not
       be antisymmetric: there may be pairs of elements such that each is "less
       than or equal to" the other, so that both elements have the same
       order-theoretic properties (in some sense, there is a "tie" among them).

       If a preorder is required to be antisymmetric, that is, there is no such
       "tie", then one obtains a partial order.  If a preorder is required to
       be symmetric, that is, all comparable elements are tied, then one
       obtains an equivalence relation.

       Every preorder naturally factors into these two notions: the "tie"
       relation on a proset is an equivalence relation, and the quotient under
       that equivalence relation is a partial order.  (Contributed by FL,
       17-Nov-2014.)  (Revised by Stefan O'Rear, 31-Jan-2015.) $)
    df-proset $a |- Proset = { f | [. ( Base ` f ) / b ].
          [. ( le ` f ) / r ].
                A. x e. b A. y e. b A. z e. b ( x r x
                 /\ ( ( x r y /\ y r z ) -> x r z ) ) } $.

    $( Define the class of directed sets.  A directed set is a nonempty
       preordered set where every pair of elements have some upper bound.  Note
       that it is not required that there exist a _least_ upper bound.

       There is no consensus in the literature over whether directed sets are
       allowed to be empty.  It is slightly more convenient for us if they are
       not.  (Contributed by Stefan O'Rear, 1-Feb-2015.) $)
    df-drs $a |- Dirset = { f e. Proset | [. ( Base ` f ) / b ].
        [. ( le ` f ) / r ]. ( b =/= (/) /\ A. x e. b A. y e. b E. z e. b
            ( x r z /\ y r z ) ) } $.
  $}

  ${
    $d K f b r x y z $.  $d B f b r x y z $.  $d .<_ f b r x y z $.
    $d X x y z $.  $d Y x y z $.  $d Z x y z $.
    isprs.b $e |- B = ( Base ` K ) $.
    isprs.l $e |- .<_ = ( le ` K ) $.
    $( Property of being a preordered set.  (Contributed by Stefan O'Rear,
       31-Jan-2015.) $)
    isprs $p |- ( K e. Proset <-> ( K e. _V /\ A. x e. B A. y e. B A. z e. B
          ( x .<_ x /\ ( ( x .<_ y /\ y .<_ z ) -> x .<_ z ) ) ) ) $=
      ( vr vb cv wbr wa wral cple cfv wsbc cbs wceq breq vf wi cproset sbceqbid
      fveq2 sbceq1d wb eqtr3 mpan2 raleq raleqbi1dv syl anbi12d imbi12d ralbidv
      fvex 2ralbidv sylan9bb sbc2ie bitrdi df-proset elab4g ) AKZVCIKZLZVCBKZVD
      LZVFCKZVDLZMZVCVHVDLZUBZMZCJKZNZBVNNZAVNNZIUAKZOPZQZJVRRPZQZVCVCFLZVCVFFL
      ZVFVHFLZMZVCVHFLZUBZMZCDNZBDNADNZUAEUCVRESZWBVQIEOPZQZJERPZQWKWLVTWNJWAWO
      VRERUEWLVQIVSWMVREOUEUFUDVQWKJIWOWMERUPEOUPVNWOSZVQVMCDNZBDNZADNZVDWMSZWK
      WPVNDSZVQWSUGWPDWOSXAGVNDWOUHUIVPWRAVNDVOWQBVNDVMCVNDUJUKUKULWTVDFSZWSWKU
      GWTFWMSXBHVDFWMUHUIXBWQWJABDDXBVMWICDXBVEWCVLWHVCVCVDFTXBVJWFVKWGXBVGWDVI
      WEVCVFVDFTVFVHVDFTUMVCVHVDFTUNUMUOUQULURUSUTABCUAIJVAVB $.

    $( Lemma for ~ prsref and ~ prstr .  (Contributed by Mario Carneiro,
       1-Feb-2015.) $)
    prslem $p |- ( ( K e. Proset /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
        ( X .<_ X /\ ( ( X .<_ Y /\ Y .<_ Z ) -> X .<_ Z ) ) ) $=
      ( vx vy vz wcel cv wbr wa wi wral wceq breq1 breq2 cproset w3a simprbi wb
      cvv isprs breq12 anidms anbi1d imbi12d anbi12d imbi1d anbi2d rspc3v mpan9
      ) BUALZIMZUQCNZUQJMZCNZUSKMZCNZOZUQVACNZPZOZKAQJAQIAQZDALEALFALUBDDCNZDEC
      NZEFCNZOZDFCNZPZOZUPBUELVGIJKABCGHUFUCVFVNVHDUSCNZVBOZDVACNZPZOVHVIEVACNZ
      OZVQPZOIJKDEFAAAUQDRZURVHVEVRWBURVHUDUQDUQDCUGUHWBVCVPVDVQWBUTVOVBUQDUSCS
      UIUQDVACSUJUKUSERZVRWAVHWCVPVTVQWCVOVIVBVSUSEDCTUSEVACSUKULUMVAFRZWAVMVHW
      DVTVKVQVLWDVSVJVIVAFECTUMVAFDCTUJUMUNUO $.

    $( "Less than or equal to" is reflexive in a proset.  (Contributed by
       Stefan O'Rear, 1-Feb-2015.) $)
    prsref $p |- ( ( K e. Proset /\ X e. B ) -> X .<_ X ) $=
      ( cproset wcel wa wbr wi w3a id 3jca prslem sylan2 simpld ) BGHZDAHZIDDCJ
      ZTTITKZSRSSSLTUAISSSSSMZUBUBNABCDDDEFOPQ $.

    $( "Less than or equal to" is transitive in a proset.  (Contributed by
       Stefan O'Rear, 1-Feb-2015.) $)
    prstr $p |- ( ( K e. Proset /\ ( X e. B /\ Y e. B /\ Z e. B ) /\
          ( X .<_ Y /\ Y .<_ Z ) ) -> X .<_ Z ) $=
      ( cproset wcel w3a wbr wa wi prslem simprd 3impia ) BIJZDAJEAJFAJKZDECLEF
      CLMZDFCLZRSMDDCLTUANABCDEFGHOPQ $.
  $}

  ${
    $d x y z D $.  $d x y z K $.
    oduprs.d $e |- D = ( ODual ` K ) $.
    $( Being a proset is a self-dual property.  (Contributed by Thierry Arnoux,
       13-Sep-2018.) $)
    oduprs $p |- ( K e. Proset -> D e. Proset ) $=
      ( vx vy vz cproset wcel cvv cv wbr wa wral isprs r19.21bi vex brcnv an32s
      wi ralrimiva cple cfv ccnv cbs eqid simprbi simpld sylibr simprd anbi12ci
      ex imp 3imtr4g jca codu fvexi jctil odubas oduleval ) BGHZAIHZDJZVBBUAUBZ
      UCZKZVBEJZVDKZVFFJZVDKZLZVBVHVDKZSZLZFBUDUBZMZEVNMZDVNMZLAGHUTVQVAUTVPDVN
      UTVBVNHZLZVOEVNVSVFVNHZLZVMFVNWAVHVNHZLZVEVLWCVBVBVCKZVEWCWDVBVFVCKVFVHVC
      KLVBVHVCKSZWAWDWELZFVNVSWFFVNMZEVNUTWGEVNMZDVNUTBIHZWHDVNMDEFVNBVCVNUEZVC
      UEZNUFOOOUGVBVBVCDPZWLQUHWCVHVFVCKZVFVBVCKZLZVHVBVCKZVJVKVSWBVTWOWPSZVSWB
      LVTWQUTWBVRVTWQSUTWBLZVRLVTWQWRVTVRWQWRVTLZVRLVHVHVCKZWQWSWTWQLZDVNWRXADV
      NMZEVNUTXBEVNMZFVNUTWIXCFVNMFEDVNBVCWJWKNUFOOOUIRUKRULRVGWNVIWMVBVFVCWLEP
      ZQVFVHVCXDFPZQUJVBVHVCWLXEQUMUNTTTABUOCUPUQDEFVNAVDVNABCWJURAVCBCWKUSNUH
      $.
  $}

  ${
    $d K f b r x y z $.  $d B f b r x y z $.  $d .<_ f b r x y z $.
    $d X x y z $.  $d Y x y z $.
    isdrs.b $e |- B = ( Base ` K ) $.
    isdrs.l $e |- .<_ = ( le ` K ) $.
    $( Property of being a directed set.  (Contributed by Stefan O'Rear,
       1-Feb-2015.) $)
    isdrs $p |- ( K e. Dirset <-> ( K e. Proset /\ B =/= (/) /\
          A. x e. B A. y e. B E. z e. B ( x .<_ z /\ y .<_ z ) ) ) $=
      ( vb vr vf c0 cv wbr wa wral cple cfv wsbc cbs cdrs wcel cproset wne wrex
      w3a fveq2 eqtr4di sbceq1d sbceqbid fvexi wb neeq1 adantr rexeq raleqbi1dv
      wceq anbi12d rexbidv 2ralbidv sylan9bb sbc2ie bitrdi df-drs elrab2 3anass
      breq bitr4i ) EUAUBEUCUBZDLUDZAMZCMZFNZBMZVLFNZOZCDUEZBDPADPZOZOVIVJVRUFI
      MZLUDZVKVLJMZNZVNVLWBNZOZCVTUEZBVTPZAVTPZOZJKMZQRZSZIWJTRZSZVSKEUCUAWJEUQ
      ZWNWIJFSZIDSVSWOWLWPIWMDWOWMETRDWJETUGGUHWOWIJWKFWOWKEQRFWJEQUGHUHUIUJWIV
      SIJDFDETGUKFEQHUKVTDUQZWBFUQZOWAVJWHVRWQWAVJULWRVTDLUMUNWQWHWECDUEZBDPZAD
      PWRVRWGWTAVTDWFWSBVTDWECVTDUOUPUPWRWSVQABDDWRWEVPCDWRWCVMWDVOVKVLWBFVGVNV
      LWBFVGURUSUTVAURVBVCABCKJIVDVEVIVJVRVFVH $.

    $( Direction of a directed set.  (Contributed by Stefan O'Rear,
       1-Feb-2015.) $)
    drsdir $p |- ( ( K e. Dirset /\ X e. B /\ Y e. B ) ->
        E. z e. B ( X .<_ z /\ Y .<_ z ) ) $=
      ( vx vy cdrs wcel cv wbr wa wrex wral wceq breq1 rexbidv cproset c0 isdrs
      wne simp3bi anbi1d anbi2d rspc2v syl5com 3impib ) CKLZEBLZFBLZEAMZDNZFUND
      NZOZABPZUKIMZUNDNZJMZUNDNZOZABPZJBQIBQZULUMOURUKCUALBUBUDVEIJABCDGHUCUEVD
      URUOVBOZABPIJEFBBUSERZVCVFABVGUTUOVBUSEUNDSUFTVAFRZVFUQABVHVBUPUOVAFUNDSU
      GTUHUIUJ $.
  $}

  ${
    $d K x y z $.  $d B x y z $.

    $( A directed set is a proset.  (Contributed by Stefan O'Rear,
       1-Feb-2015.) $)
    drsprs $p |- ( K e. Dirset -> K e. Proset ) $=
      ( vx vz vy cdrs wcel cproset cbs cfv c0 wne cv cple wbr wa wrex wral eqid
      isdrs simp1bi ) AEFAGFAHIZJKBLCLZAMIZNDLUBUCNOCUAPDUAQBUAQBDCUAAUCUARUCRS
      T $.

    drsbn0.b $e |- B = ( Base ` K ) $.
    $( The base of a directed set is not empty.  (Contributed by Stefan O'Rear,
       1-Feb-2015.) $)
    drsbn0 $p |- ( K e. Dirset -> B =/= (/) ) $=
      ( vx vz vy cdrs wcel cproset c0 wne cv cple cfv wbr wrex wral eqid isdrs
      wa simp2bi ) BGHBIHAJKDLELZBMNZOFLUBUCOTEAPFAQDAQDFEABUCCUCRSUA $.

    drsdirfi.l $e |- .<_ = ( le ` K ) $.
    $d K a b c x y z $.  $d .<_ a b c x y z $.  $d B a b c x y z $.
    $d X a b c x y z $.
    $( Any _finite_ number of elements in a directed set have a common upper
       bound.  Here is where the nonemptiness constraint in ~ df-drs first
       comes into play; without it we would need an additional constraint that
       ` X ` not be empty.  (Contributed by Stefan O'Rear, 1-Feb-2015.) $)
    drsdirfi $p |- ( ( K e. Dirset /\ X C_ B /\ X e. Fin ) ->
        E. y e. B A. z e. X z .<_ y ) $=
      ( va wcel wss cv wbr wral wrex wa wi c0 wceq sseq1 vb vc cdrs cfn csn cun
      anbi2d raleq rexbidv imbi12d wne drsbn0 ral0 jctr eximi n0 df-rex 3imtr4i
      wex adantr ssun1 sstr mpan anim2i ralbidv cbvrexvw simplrr cproset drsprs
      breq2 ad5antr ad2antlr sselda simp-4r simprl ad2antrr simpr simprrl prstr
      syl syl132anc ex ralimdva adantlrr mpd simprrr breq1 ralsn sylibr syl2anc
      vex ralun simpll snss drsdir syl3anc reximddv rexlimdvaa biimtrid embantd
      ssun2 com12 a1i findcard2 3impia ) DUCJZFCKZFUDJZBLZALZEMZBFNZACOZXHXFXGP
      ZXMXFILZCKZPZXKBXONZACOZQXFRCKZPZXKBRNZACOZQXFUALZCKZPZXKBYDNZACOZQZXFYDU
      BLZUEZUFZCKZPZXKBYLNZACOZQZXNXMQIUAUBFXORSZXQYAXSYCYRXPXTXFXORCTUGYRXRYBA
      CXKBXORUHUIUJXOYDSZXQYFXSYHYSXPYEXFXOYDCTUGYSXRYGACXKBXOYDUHUIUJXOYLSZXQY
      NXSYPYTXPYMXFXOYLCTUGYTXRYOACXKBXOYLUHUIUJXOFSZXQXNXSXMUUAXPXGXFXOFCTUGUU
      AXRXLACXKBXOFUHUIUJXFYCXTXFCRUKZYCCDGULXJCJZAUSUUCYBPZAUSUUBYCUUCUUDAUUCY
      BXKBUMUNUOACUPYBACUQURVTUTYIYQQYDUDJYNYIYPYNYFYHYPYMYEXFYDYLKYMYEYDYKVAYD
      YLCVBVCZVDYHXIXOEMZBYDNZICOYNYPYGUUGAICXJXOSXKUUFBYDXJXOXIEVJVEVFYNUUGYPI
      CYNXOCJZUUGPZPZXOXJEMZYJXJEMZPZYOACUUJUUCUUMPZPZYGXKBYKNZYOUUOUUGYGYNUUHU
      UGUUNVGYNUUHUUNUUGYGQUUGYNUUHPZUUNPZUUFXKBYDUURXIYDJZPZUUFXKUUTUUFPDVHJZX
      ICJZUUHUUCUUFUUKXKXFUVAYMUUHUUNUUSUUFDVIVKUUTUVBUUFUURYDCXIUUQYEUUNYMYEXF
      UUHUUEVLUTVMUTYNUUHUUNUUSUUFVNUURUUCUUSUUFUUQUUCUUMVOVPUUTUUFVQUURUUKUUSU
      UFUUQUUCUUKUULVRVPCDEXIXOXJGHVSWAWBWCWDWEUUOUULUUPUUJUUCUUKUULWFXKUULBYJU
      BWKZXIYJXJEWGWHWIXKBYDYKWLWJUUJXFUUHYJCJZUUMACOXFYMUUIWMYNUUHUUGVOYMUVDXF
      UUIYMYKCKZUVDYKYLKYMUVEYKYDXAYKYLCVBVCYJCUVCWNWIVLACDEXOYJGHWOWPWQWRWSWTX
      BXCXDXBXE $.

    $( Directed sets may be defined in terms of finite subsets.  Again, without
       nonemptiness we would need to restrict to nonempty subsets here.
       (Contributed by Stefan O'Rear, 1-Feb-2015.) $)
    isdrs2 $p |- ( K e. Dirset <-> ( K e. Proset /\
          A. x e. ( ~P B i^i Fin ) E. y e. B A. z e. x z .<_ y ) ) $=
      ( va vb wcel cv wbr wral wrex cfn wa simpl adantl c0 cdrs cproset cpw cin
      drsprs wss elinel1 elpwid elinel2 drsdirfi syl3anc ralrimiva jca wi 0elpw
      wne 0fi elini wceq raleq rexbidv rspcv ax-mp rexn0 syl cpr simplr prelpwi
      a1i elind rspcdva vex breq1 ralpr rexbii sylib ralrimivva isdrs syl3anbrc
      prfi impbii ) EUAKZEUBKZCLZBLZFMZCALZNZBDOZADUCZPUDZNZQZWBWCWLEUEWBWIAWKW
      BWGWKKZQWBWGDUFZWGPKZWIWBWNRWNWOWBWNWGDWGWJPUGUHSWNWPWBWGWJPUISBCDEFWGGHU
      JUKULUMWMWCDTUPZILZWEFMZJLZWEFMZQZBDOZJDNIDNWBWCWLRWLWQWCWLWFCTNZBDOZWQTW
      KKWLXEUNTWJPDUOUQURWIXEATWKWGTUSWHXDBDWFCWGTUTVAVBVCXDBDVDVESWMXCIJDDWMWR
      DKWTDKQZQZWFCWRWTVFZNZBDOZXCXGWIXJAWKXHWGXHUSWHXIBDWFCWGXHUTVAWCWLXFVGXFX
      HWKKWMXFWJPXHWRWTDVHXHPKXFWRWTVTVIVJSVKXIXBBDWFWSXACWRWTIVLJVLWDWRWEFVMWD
      WTWEFVMVNVOVPVQIJBDEFGHVRVSWA $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Partially ordered sets (posets)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c Poset $.
  $c lt $.
  $c lub $.
  $c glb $.
  $c join $.
  $c meet $.

  $( Extend class notation with the class of posets. $)
  cpo $a class Poset $.

  $( Extend class notation with less-than for posets. $)
  cplt $a class lt $.

  $( Extend class notation with poset least upper bound. $)
  club $a class lub $.

  $( Extend class notation with poset greatest lower bound. $)
  cglb $a class glb $.

  $( Extend class notation with poset join. $)
  cjn $a class join $.

  $( Extend class notation with poset meet. $)
  cmee $a class meet $.

  ${
    $d f b r x y z $.
    $( Define the class of partially ordered sets (posets).  A poset is a set
       equipped with a partial order, that is, a binary relation which is
       reflexive, antisymmetric, and transitive.  Unlike a total order, in a
       partial order there may be pairs of elements where neither precedes the
       other.  Definition of poset in [Crawley] p. 1.  Note that
       Crawley-Dilworth require that a poset base set be nonempty, but we
       follow the convention of most authors who don't make this a requirement.

       In our formalism of extensible structures, the base set of a poset ` f `
       is denoted by ` ( Base `` f ) ` and its partial order by ` ( le `` f ) `
       (for "less than or equal to").  The quantifiers ` E. b E. r ` provide a
       notational shorthand to allow to refer to the base and ordering relation
       as ` b ` and ` r ` in the definition rather than having to repeat
       ` ( Base `` f ) ` and ` ( le `` f ) ` throughout.  These quantifiers can
       be eliminated with ~ ceqsex2v and related theorems.  (Contributed by NM,
       18-Oct-2012.) $)
    df-poset $a |- Poset = { f | E. b E. r
              ( b = ( Base ` f )
               /\ r = ( le ` f )
               /\ A. x e. b A. y e. b A. z e. b ( x r x
                 /\ ( ( x r y /\ y r x ) -> x = y )
                 /\ ( ( x r y /\ y r z ) -> x r z ) ) ) } $.
  $}

  ${
    $d b p r x y z B $.  $d b p r K $.  $d b p r x y z .<_ $.
    ispos.b $e |- B = ( Base ` K ) $.
    ispos.l $e |- .<_ = ( le ` K ) $.
    $( The predicate "is a poset".  (Contributed by NM, 18-Oct-2012.)  (Revised
       by Mario Carneiro, 4-Nov-2013.) $)
    ispos $p |- ( K e. Poset <-> ( K e. _V
            /\ A. x e. B A. y e. B A. z e. B ( x .<_ x
                 /\ ( ( x .<_ y /\ y .<_ x ) -> x = y )
                 /\ ( ( x .<_ y /\ y .<_ z ) -> x .<_ z ) ) ) ) $=
      ( vb vr cv wceq wbr wa wi w3a wral wex cbs breq vp cpo wcel cvv cfv fveq2
      cple eqtr4di eqeq2d 3anbi12d 2exbidv elab4g fvexi raleq raleqbi1dv imbi1d
      df-poset anbi12d imbi12d 3anbi123d ralbidv 2ralbidv ceqsex2v anbi2i bitri
      ) EUBUCEUDUCZIKZDLZJKZFLZAKZVKVIMZVKBKZVIMZVMVKVIMZNZVKVMLZOZVNVMCKZVIMZN
      ZVKVSVIMZOZPZCVGQZBVGQZAVGQZPZJRIRZNVFVKVKFMZVKVMFMZVMVKFMZNZVQOZWKVMVSFM
      ZNZVKVSFMZOZPZCDQZBDQADQZNVGUAKZSUEZLZVIXBUGUEZLZWGPZJRIRWIUAEUBXBELZXGWH
      IJXHXDVHXFVJWGXHXCDVGXHXCESUEDXBESUFGUHUIXHXEFVIXHXEEUGUEFXBEUGUFHUHUIUJU
      KABCUAJIUQULWIXAVFWGWDCDQZBDQZADQXAIJDFDESGUMFEUGHUMWFXJAVGDWEXIBVGDWDCVG
      DUNUOUOVJXIWTABDDVJWDWSCDVJVLWJVRWNWCWRVKVKVIFTVJVPWMVQVJVNWKVOWLVKVMVIFT
      ZVMVKVIFTURUPVJWAWPWBWQVJVNWKVTWOXKVMVSVIFTURVKVSVIFTUSUTVAVBVCVDVE $.
  $}

  ${
    $d K x y z $.  $d B x y z $.  $d .<_ x y z $.
    ispos2.b $e |- B = ( Base ` K ) $.
    ispos2.l $e |- .<_ = ( le ` K ) $.
    $( A poset is an antisymmetric proset.

       _EDITORIAL_: could become the definition of poset.  (Contributed by
       Stefan O'Rear, 1-Feb-2015.) $)
    ispos2 $p |- ( K e. Poset <-> ( K e. Proset /\ A. x e. B A. y e. B
          ( ( x .<_ y /\ y .<_ x ) -> x = y ) ) ) $=
      ( vz cvv wcel cv wbr wa weq wi w3a wral ralbii bitri anbi2i cproset ispos
      cpo 3anan32 r19.26 2ralbii r19.26-2 rr19.3v isprs anbi1i anass 3bitr4i )
      DIJZAKZUNELZUNBKZELZUPUNELMABNOZUQUPHKZELMUNUSELOZPZHCQZBCQACQZMUMUOUTMZH
      CQZBCQACQZURBCQZACQZMZMZDUCJDUAJZVHMZVCVIUMVCVEURHCQZMZBCQACQZVIVBVNABCCV
      BVDURMZHCQVNVAVPHCUOURUTUDRVDURHCUESUFVOVFVMBCQZACQZMVIVEVMABCCUGVRVHVFVQ
      VGACURBHCUHRTSSTABHCDEFGUBVLUMVFMZVHMVJVKVSVHABHCDEFGUIUJUMVFVHUKSUL $.
  $}

  ${
    $d K x y $.
    $( A poset is a proset.  (Contributed by Stefan O'Rear, 1-Feb-2015.) $)
    posprs $p |- ( K e. Poset -> K e. Proset ) $=
      ( vx vy cpo wcel cproset cv cple cfv wbr weq cbs wral eqid ispos2 simplbi
      wa wi ) ADEAFEBGZCGZAHIZJTSUAJQBCKRCALIZMBUBMBCUBAUAUBNUANOP $.
  $}

  ${
    $d x y z B $.  $d x y z .<_ $.  $d x y z X $.  $d y z Y $.  $d z Z $.
    posi.b $e |- B = ( Base ` K ) $.
    posi.l $e |- .<_ = ( le ` K ) $.
    $( Lemma for poset properties.  (Contributed by NM, 11-Sep-2011.) $)
    posi $p |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) )
                -> ( X .<_ X
                 /\ ( ( X .<_ Y /\ Y .<_ X ) -> X = Y )
                 /\ ( ( X .<_ Y /\ Y .<_ Z ) -> X .<_ Z ) ) ) $=
      ( vx vy vz wcel wbr wa wceq wi w3a breq1 breq2 imbi12d cpo wral cvv ispos
      simprbi bitrd anbi12d eqeq1 anbi1d 3anbi123d eqeq2 imbi1d 3anbi23d anbi2d
      cv 3anbi3d rspc3v mpan9 ) BUALZIUOZUTCMZUTJUOZCMZVBUTCMZNZUTVBOZPZVCVBKUO
      ZCMZNZUTVHCMZPZQZKAUBJAUBIAUBZDALEALFALQDDCMZDECMZEDCMZNZDEOZPZVPEFCMZNZD
      FCMZPZQZUSBUCLVNIJKABCGHUDUEVMWEVODVBCMZVBDCMZNZDVBOZPZWFVINZDVHCMZPZQVOV
      TVPEVHCMZNZWLPZQIJKDEFAAAUTDOZVAVOVGWJVLWMWQVADUTCMVOUTDUTCRUTDDCSUFWQVEW
      HVFWIWQVCWFVDWGUTDVBCRZUTDVBCSUGUTDVBUHTWQVJWKVKWLWQVCWFVIWRUIUTDVHCRTUJV
      BEOZWJVTWMWPVOWSWHVRWIVSWSWFVPWGVQVBEDCSZVBEDCRUGVBEDUKTWSWKWOWLWSWFVPVIW
      NWTVBEVHCRUGULUMVHFOZWPWDVOVTXAWOWBWLWCXAWNWAVPVHFECSUNVHFDCSTUPUQUR $.

    $( A poset ordering is reflexive.  (Contributed by NM, 11-Sep-2011.)
       (Proof shortened by OpenAI, 25-Mar-2020.) $)
    posref $p |- ( ( K e. Poset /\ X e. B ) -> X .<_ X ) $=
      ( cpo wcel cproset wbr posprs prsref sylan ) BGHBIHDAHDDCJBKABCDEFLM $.

    $( A poset ordering is asymmetric.  (Contributed by NM, 21-Oct-2011.) $)
    posasymb $p |- ( ( K e. Poset /\ X e. B /\ Y e. B )
                -> ( ( X .<_ Y /\ Y .<_ X ) <-> X = Y ) ) $=
      ( cpo wcel w3a wbr wa wceq wi simp1 simp2 simp3 posi syl13anc syl5ibcom
      simp2d posref breq2 breq1 jcad 3adant3 impbid ) BHIZDAIZEAIZJZDECKZEDCKZL
      ZDEMZUKDDCKZUNUONZULEECKLULNZUKUHUIUJUJUPUQURJUHUIUJOUHUIUJPUHUIUJQZUSABC
      DEEFGRSUAUHUIUOUNNUJUHUILZUOULUMUTUPUOULABCDFGUBZDEDCUCTUTUPUOUMVADEDCUDT
      UEUFUG $.

    $( A poset ordering is transitive.  (Contributed by NM, 11-Sep-2011.) $)
    postr $p |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) )
                -> ( ( X .<_ Y /\ Y .<_ Z ) -> X .<_ Z ) ) $=
      ( cpo wcel w3a wa wbr wceq wi posi simp3d ) BIJDAJEAJFAJKLDDCMDECMZEDCMLD
      ENOREFCMLDFCMOABCDEFGHPQ $.
  $}

  ${
    $d a b c $.
    $( Technical lemma to simplify the statement of ~ ipopos .  The empty set
       is (rather pathologically) a poset under our definitions, since it has
       an empty base set ( ~ str0 ) and any relation partially orders an empty
       set.  (Contributed by Stefan O'Rear, 30-Jan-2015.)  (Proof shortened by
       AV, 13-Oct-2024.) $)
    0pos $p |- (/) e. Poset $=
      ( va vb vc c0 cpo wcel cvv cv wbr wa weq w3a wral 0ex ral0 base0 cple cnx
      wi cfv pleid str0 ispos mpbir2an ) DEFDGFAHZUEDIUEBHZDIZUFUEDIJABKSUGUFCH
      ZDIJUEUHDISLCDMBDMZADMNUIAOABCDDDPQRQTUAUBUCUD $.
  $}

  ${
    $d x y z B $.  $d x y z K $.  $d x y z ph $.
    isposd.k $e |- ( ph -> K e. V ) $.
    isposd.b $e |- ( ph -> B = ( Base ` K ) ) $.
    isposd.l $e |- ( ph -> .<_ = ( le ` K ) ) $.
    isposd.1 $e |- ( ( ph /\ x e. B ) -> x .<_ x ) $.
    isposd.2 $e |- ( ( ph /\ x e. B /\ y e. B ) ->
                   ( ( x .<_ y /\ y .<_ x ) -> x = y ) ) $.
    isposd.3 $e |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) ->
                   ( ( x .<_ y /\ y .<_ z ) -> x .<_ z ) ) $.
    $( Properties that determine a poset (implicit structure version).
       (Contributed by Mario Carneiro, 29-Apr-2014.)  (Revised by AV,
       26-Apr-2024.) $)
    isposd $p |- ( ph -> K e. Poset ) $=
      ( wcel wbr wa wi wral breqd cvv cv cple cfv wceq w3a cbs cpo elexd adantr
      adantrr 3expb 3exp2 imp42 3jca ralrimiva anbi12d imbi1d imbi12d 3anbi123d
      ralrimivva raleqbidv anbi2d mpbi2and eqid ispos sylibr ) AFUAOZBUBZVIFUCU
      DZPZVICUBZVJPZVLVIVJPZQZVIVLUEZRZVMVLDUBZVJPZQZVIVRVJPZRZUFZDFUGUDZSZCWDS
      ZBWDSZQZFUHOAVHVIVIGPZVIVLGPZVLVIGPZQZVPRZWJVLVRGPZQZVIVRGPZRZUFZDESZCESZ
      BESZWHAFHIUIAWSBCEEAVIEOZVLEOZQQZWRDEXDVREOZQWIWMWQXDWIXEAXBWIXCLUKUJXDWM
      XEAXBXCWMMULUJAXBXCXEWQAXBXCXEWQNUMUNUOUPVAAXAWGVHAWTWFBEWDJAWSWECEWDJAWR
      WCDEWDJAWIVKWMVQWQWBAGVJVIVIKTAWLVOVPAWJVMWKVNAGVJVIVLKTZAGVJVLVIKTUQURAW
      OVTWPWAAWJVMWNVSXFAGVJVLVRKTUQAGVJVIVRKTUSUTVBVBVBVCVDBCDWDFVJWDVEVJVEVFV
      G $.
  $}

  ${
    $d x y z B $.  $d x y z .<_ $.
    isposi.k $e |- K e. _V $.
    isposi.b $e |- B = ( Base ` K ) $.
    isposi.l $e |- .<_ = ( le ` K ) $.
    isposi.1 $e |- ( x e. B -> x .<_ x ) $.
    isposi.2 $e |- ( ( x e. B /\ y e. B ) ->
                   ( ( x .<_ y /\ y .<_ x ) -> x = y ) ) $.
    isposi.3 $e |- ( ( x e. B /\ y e. B /\ z e. B ) ->
                   ( ( x .<_ y /\ y .<_ z ) -> x .<_ z ) ) $.
    $( Properties that determine a poset (implicit structure version).
       (Contributed by NM, 11-Sep-2011.) $)
    isposi $p |- K e. Poset $=
      ( cpo wcel cv wbr wa wi w3a wral cvv 3ad2ant1 3adant3 3jca rgen3 mpbir2an
      weq ispos ) EMNEUANAOZUIFPZUIBOZFPZUKUIFPQABUGRZULUKCOZFPQUIUNFPRZSZCDTBD
      TADTGUPABCDDDUIDNZUKDNZUNDNZSUJUMUOUQURUJUSJUBUQURUMUSKUCLUDUEABCDEFHIUHU
      F $.
  $}

  ${
    $d x y z B $.  $d x y z .<_ $.
    isposix.a $e |- B e. _V $.
    isposix.b $e |- .<_ e. _V $.
    isposix.k $e |- K = { <. ( Base ` ndx ) , B >. ,
         <. ( le ` ndx ) , .<_ >. } $.
    isposix.1 $e |- ( x e. B -> x .<_ x ) $.
    isposix.2 $e |- ( ( x e. B /\ y e. B ) ->
                   ( ( x .<_ y /\ y .<_ x ) -> x = y ) ) $.
    isposix.3 $e |- ( ( x e. B /\ y e. B /\ z e. B ) ->
                   ( ( x .<_ y /\ y .<_ z ) -> x .<_ z ) ) $.
    $( Properties that determine a poset (explicit structure version).  Note
       that the numeric indices of the structure components are not mentioned
       explicitly in either the theorem or its proof.  (Contributed by NM,
       9-Nov-2012.)  (Proof shortened by AV, 30-Oct-2024.) $)
    isposix $p |- K e. Poset $=
      ( cnx cbs cfv cop cple cvv wcel wceq cpr eqeltri basendxltplendx plendxnn
      prex 2strbas ax-mp pleid 2strop isposi ) ABCDEFEMNODPZMQOZFPZUARIUKUMUEUB
      DRSDENOTGDFEULRIUCUDUFUGFRSFEQOTHDFQEULRIUCUDUHUIUGJKLUJ $.
  $}

  ${
    $d B x y a b c $.  $d ph x y a b c $.  $d K x y a b c $.  $d L x y a b c $.
    pospropd.kv $e |- ( ph -> K e. V ) $.
    pospropd.lv $e |- ( ph -> L e. W ) $.
    pospropd.kb $e |- ( ph -> B = ( Base ` K ) ) $.
    pospropd.lb $e |- ( ph -> B = ( Base ` L ) ) $.
    pospropd.xy $e |- ( ( ph /\ ( x e. B /\ y e. B ) ) ->
        ( x ( le ` K ) y <-> x ( le ` L ) y ) ) $.
    $( Posethood is determined only by structure components and only by the
       value of the relation within the base set.  (Contributed by Stefan
       O'Rear, 29-Jan-2015.) $)
    pospropd $p |- ( ph -> ( K e. Poset <-> L e. Poset ) ) $=
      ( va vb vc wbr wa wral wb cvv wcel cv cple cfv weq w3a cbs cpo ralrimivva
      simp1 jca breq1 bibi12d breq2 rspc2va sylan 3adantl3 3simpb 3comr anbi12d
      wi imbi1d 3adantl1 3anbi123d sylan2 ancoms 3exp2 imp42 ralbidva 2ralbidva
      imbi12d wceq raleq raleqbi1dv 3bitr3d elexd biantrurd eqid ispos 3bitr4g
      syl ) AEUAUBZNUCZWDEUDUEZQZWDOUCZWEQZWGWDWEQZRZNOUFZVBZWHWGPUCZWEQZRZWDWM
      WEQZVBZUGZPEUHUEZSZOWSSZNWSSZRZFUAUBZWDWDFUDUEZQZWDWGXEQZWGWDXEQZRZWKVBZX
      GWGWMXEQZRZWDWMXEQZVBZUGZPFUHUEZSZOXPSZNXPSZRZEUIUBFUIUBAXBXSXCXTAWRPDSZO
      DSZNDSZXOPDSZODSZNDSZXBXSAYAYDNODDAWDDUBZWGDUBZRRWRXOPDAYGYHWMDUBZWRXOTZA
      YGYHYIYJYGYHYIUGZAYJAYKBUCZCUCZWEQZYLYMXEQZTZCDSBDSZYJAYPBCDDMUJYKYQRZWFX
      FWLXJWQXNYKYGYGRYQWFXFTZYKYGYGYGYHYIUKZYTULYPYSWDYMWEQZWDYMXEQZTZBCWDWDDD
      BNUFYNUUAYOUUBYLWDYMWEUMYLWDYMXEUMUNZCNUFZUUAWFUUBXFYMWDWDWEUOYMWDWDXEUOU
      NUPUQYRWJXIWKYRWHXGWIXHYGYHYQWHXGTZYIYPUUFUUCBCWDWGDDUUDCOUFUUAWHUUBXGYMW
      GWDWEUOYMWGWDXEUOUNUPURZYKYHYGRZYQWIXHTZYHYIYGUUHYHYIYGUSUTYPUUIWGYMWEQZW
      GYMXEQZTZBCWGWDDDBOUFYNUUJYOUUKYLWGYMWEUMYLWGYMXEUMUNZUUEUUJWIUUKXHYMWDWG
      WEUOYMWDWGXEUOUNUPUQVAVCYRWOXLWPXMYRWHXGWNXKUUGYHYIYQWNXKTZYGYPUUNUULBCWG
      WMDDUUMCPUFZUUJWNUUKXKYMWMWGWEUOYMWMWGXEUOUNUPVDVAYKYGYIRYQWPXMTZYGYHYIUS
      YPUUPUUCBCWDWMDDUUDUUOUUAWPUUBXMYMWMWDWEUOYMWMWDXEUOUNUPUQVLVEVFVGVHVIVJV
      KADWSVMYCXBTKYBXANDWSYAWTODWSWRPDWSVNVOVOWBADXPVMYFXSTLYEXRNDXPYDXQODXPXO
      PDXPVNVOVOWBVPAWCXBAEGIVQVRAXDXSAFHJVQVRVPNOPWSEWEWSVSWEVSVTNOPXPFXEXPVSX
      EVSVTWA $.
  $}

  ${
    $d D a b c $.  $d O a b c $.  $d V a b c $.
    odupos.d $e |- D = ( ODual ` O ) $.
    $( Being a poset is a self-dual property.  (Contributed by Stefan O'Rear,
       29-Jan-2015.) $)
    odupos $p |- ( O e. Poset -> D e. Poset ) $=
      ( va vb vc wcel cbs cfv cple cvv a1i wceq eqid cv wa wbr vex brcnv w3a wi
      cpo ccnv fvexi odubas oduleval posref sylibr weq anbi12ci posasymb biimpd
      codu biimtrid 3anrev postr sylan2b 3imtr4g isposd ) BUBGZDEFBHIZABJIZUCZK
      AKGUTABUMCUDLVAAHIMUTVAABCVANZUELVCAJIMUTAVBBCVBNZUFLUTDOZVAGZPVFVFVBQVFV
      FVCQVABVBVFVDVEUGVFVFVBDRZVHSUHVFEOZVCQZVIVFVCQZPVFVIVBQZVIVFVBQZPZUTVGVI
      VAGZTZDEUIZVJVMVKVLVFVIVBVHERZSZVIVFVBVRVHSUJVPVNVQVABVBVFVIVDVEUKULUNUTV
      GVOFOZVAGZTZPVTVIVBQZVMPZVTVFVBQZVJVIVTVCQZPVFVTVCQWBUTWAVOVGTWDWEUAVGVOW
      AUOVABVBVTVIVFVDVEUPUQVJVMWFWCVSVIVTVBVRFRZSUJVFVTVBVHWGSURUS $.

    $( Being a poset is a self-dual property.  (Contributed by Stefan O'Rear,
       29-Jan-2015.) $)
    oduposb $p |- ( O e. V -> ( O e. Poset <-> D e. Poset ) ) $=
      ( va vb wcel cpo odupos codu cfv eqid cbs odubas a1i cv cple wbr wa ccnv
      cvv fvexd id wceq eqidd oduleval eqcomi breqi vex brcnv pospropd imbitrid
      wb 3bitri impbid2 ) BCGZBHGZAHGZABDIURAJKZHGUPUQUSAUSLZIUPEFBMKZUSBUACUPA
      JUBUPUCVAUSMKUDUPVAUSAUTVAABDVALNNOUPVAUEEPZFPZUSQKZRZVBVCBQKZRZUMUPVBVAG
      VCVAGSSVEVBVCVFTZTZRVCVBVHRVGVBVCVDVIVIVDUSVHAUTAVFBDVFLUFUFUGUHVBVCVHEUI
      ZFUIZUJVCVBVFVKVJUJUNOUKULUO $.
  $}

  $( Define less-than ordering for posets and related structures.  Unlike
     ~ df-base and ~ df-ple , this is a derived component extractor and not an
     extensible structure component extractor that defines the poset.
     (Contributed by NM, 12-Oct-2011.)  (Revised by Mario Carneiro,
     8-Feb-2015.) $)
  df-plt $a |- lt = ( p e. _V |-> ( ( le ` p ) \ _I ) ) $.

  ${
    $d p K $.  $d p .<_ $.
    pltval.l $e |- .<_ = ( le ` K ) $.
    pltval.s $e |- .< = ( lt ` K ) $.
    $( Value of the less-than relation.  (Contributed by Mario Carneiro,
       8-Feb-2015.) $)
    pltfval $p |- ( K e. A -> .< = ( .<_ \ _I ) ) $=
      ( vp wcel cplt cfv cid cdif cvv wceq elex cv cple fveq2 eqtr4di difeq1d
      df-plt fvexi difexi fvmpt syl eqtrid ) CAHZBCIJZDKLZFUGCMHUHUINCAOGCGPZQJ
      ZKLUIMIUJCNZUKDKULUKCQJDUJCQRESTGUADKDCQEUBUCUDUEUF $.

    $( Less-than relation.  ( ~ df-pss analog.)  (Contributed by NM,
       12-Oct-2011.) $)
    pltval $p |- ( ( K e. A /\ X e. B /\ Y e. C )
        -> ( X .< Y <-> ( X .<_ Y /\ X =/= Y ) ) ) $=
      ( wcel wbr wne wa wb cid cdif pltfval breqd wn brdif adantl anbi2d bitrid
      ideqg necon3bbid sylan9bb 3impb ) EAKZGBKZHCKZGHDLZGHFLZGHMZNZOUIULGHFPQZ
      LZUJUKNZUOUIDUPGHADEFIJRSUQUMGHPLZTZNURUOGHFPUAURUTUNUMUKUTUNOUJUKUSGHGHC
      UEUFUBUCUDUGUH $.

    $( "Less than" implies "less than or equal to".  ( ~ pssss analog.)
       (Contributed by NM, 4-Dec-2011.) $)
    pltle $p |- ( ( K e. A /\ X e. B /\ Y e. C ) -> ( X .< Y -> X .<_ Y ) ) $=
      ( wcel w3a wbr wne pltval simprbda ex ) EAKGBKHCKLZGHDMZGHFMZRSTGHNABCDEF
      GHIJOPQ $.
  $}

  ${
    pltne.s $e |- .< = ( lt ` K ) $.
    $( The "less than" relation is not reflexive.  ( ~ df-pss analog.)
       (Contributed by NM, 2-Dec-2011.) $)
    pltne $p |- ( ( K e. A /\ X e. B /\ Y e. C )
        -> ( X .< Y -> X =/= Y ) ) $=
      ( wcel w3a wbr wne cple cfv eqid pltval simplbda ex ) EAIFBIGCIJZFGDKZFGL
      ZSTFGEMNZKUAABCDEUBFGUBOHPQR $.

    $( The "less than" relation is not reflexive.  ( ~ pssirr analog.)
       (Contributed by NM, 7-Feb-2012.) $)
    pltirr $p |- ( ( K e. A /\ X e. B ) -> -. X .< X ) $=
      ( wcel wa wceq wbr wn eqid wne wi pltne 3anidm23 necon2bd mpi ) DAGZEBGZH
      ZEEIEECJZKELUAUBEESTUBEEMNABBCDEEFOPQR $.
  $}

  ${
    pleval2.b $e |- B = ( Base ` K ) $.
    pleval2.l $e |- .<_ = ( le ` K ) $.
    pleval2.s $e |- .< = ( lt ` K ) $.
    $( One direction of ~ pleval2 .  (Contributed by Mario Carneiro,
       8-Feb-2015.) $)
    pleval2i $p |- ( ( X e. B /\ Y e. B ) ->
      ( X .<_ Y -> ( X .< Y \/ X = Y ) ) ) $=
      ( wcel wa wbr wceq wo wne cbs cdm wb cfv elfvdm eleq2s adantr pltval expr
      3expb mpancom biimpar necon1bd orrd ex ) EAJZFAJZKZEFDLZEFBLZEFMZNUMUNKZU
      OUPUQUOEFUMUNEFOZUOUMUOUNURKZCPQZJZUMUOUSRZUKVAULVAECPSAECPTGUAUBVAUKULVB
      UTAABCDEFHIUCUEUFUGUDUHUIUJ $.

    $( "Less than or equal to" in terms of "less than".  ( ~ sspss analog.)
       (Contributed by NM, 17-Oct-2011.)  (Revised by Mario Carneiro,
       8-Feb-2015.) $)
    pleval2 $p |- ( ( K e. Poset /\ X e. B /\ Y e. B )
        -> ( X .<_ Y <-> ( X .< Y \/ X = Y ) ) ) $=
      ( cpo wcel w3a wbr wceq wo wi pleval2i 3adant1 pltle posref 3adant3 breq2
      syl5ibcom jaod impbid ) CJKZEAKZFAKZLZEFDMZEFBMZEFNZOZUGUHUJUMPUFABCDEFGH
      IQRUIUKUJULJAABCDEFHISUIEEDMZULUJUFUGUNUHACDEGHTUAEFEDUBUCUDUE $.

    $( "Less than" implies not converse "less than or equal to".  (Contributed
       by NM, 18-Oct-2011.) $)
    pltnle $p |- ( ( ( K e. Poset /\ X e. B /\ Y e. B ) /\ X .< Y )
                    -> -. Y .<_ X ) $=
      ( cpo wcel w3a wbr wn wne wa pltval wceq posasymb biimpd expdimp necon3ad
      expimpd sylbid imp ) CJKEAKFAKLZEFBMZFEDMZNZUFUGEFDMZEFOZPUIJAABCDEFHIQUF
      UJUKUIUFUJPUHEFUFUJUHEFRZUFUJUHPULACDEFGHSTUAUBUCUDUE $.

    $( Alternate expression for the "less than" relation.  ( ~ dfpss3 analog.)
       (Contributed by NM, 4-Nov-2011.) $)
    pltval3 $p |- ( ( K e. Poset /\ X e. B /\ Y e. B )
        -> ( X .< Y <-> ( X .<_ Y /\ -. Y .<_ X ) ) ) $=
      ( cpo wcel w3a wbr wne wa wn pltval wceq wi posref breq1 syl5ibcom adantr
      3adant3 posasymb biimpd expdimp impbid necon3abid pm5.32da bitrd ) CJKZEA
      KZFAKZLZEFBMEFDMZEFNZOUPFEDMZPZOJAABCDEFHIQUOUPUQUSUOUPOZUREFUTEFRZURUOVA
      URSUPUOEEDMZVAURULUMVBUNACDEGHTUDEFEDUAUBUCUOUPURVAUOUPUROVAACDEFGHUEUFUG
      UHUIUJUK $.
  $}

  ${
    pltnlt.b $e |- B = ( Base ` K ) $.
    pltnlt.s $e |- .< = ( lt ` K ) $.
    $( The less-than relation implies the negation of its inverse.
       (Contributed by NM, 18-Oct-2011.) $)
    pltnlt $p |- ( ( ( K e. Poset /\ X e. B /\ Y e. B ) /\ X .< Y )
                  -> -. Y .< X ) $=
      ( cpo wcel w3a wbr wa cple cfv eqid pltnle wi pltle 3com23 adantr mtod )
      CHIZDAIZEAIZJZDEBKZLEDBKZEDCMNZKZABCUHDEFUHOZGPUEUGUIQZUFUBUDUCUKHAABCUHE
      DUJGRSTUA $.

    $( The less-than relation has no 2-cycle loops.  ( ~ pssn2lp analog.)
       (Contributed by NM, 2-Dec-2011.) $)
    pltn2lp $p |- ( ( K e. Poset /\ X e. B /\ Y e. B )
        -> -. ( X .< Y /\ Y .< X ) ) $=
      ( cpo wcel w3a wbr wn wi wa cple cfv eqid pltnle ex pltle 3com23 nsyld
      imnan sylib ) CHIZDAIZEAIZJZDEBKZEDBKZLMUIUJNLUHUIEDCOPZKZUJUHUIULLABCUKD
      EFUKQZGRSUEUGUFUJULMHAABCUKEDUMGTUAUBUIUJUCUD $.

    $( The less-than relation is transitive.  ( ~ psstr analog.)  (Contributed
       by NM, 2-Dec-2011.) $)
    plttr $p |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) )
        -> ( ( X .< Y /\ Y .< Z ) -> X .< Z ) ) $=
      ( cpo wcel w3a wa wbr cple cfv wne wi pltle 3adant3r3 wn eqid postr breq2
      3adant3r1 syl2and wceq pltn2lp anbi2d notbid syl5ibcom necon2ad wb pltval
      jcad 3adant3r2 sylibrd ) CIJZDAJZEAJZFAJZKLZDEBMZEFBMZLZDFCNOZMZDFPZLZDFB
      MZVAVDVFVGVAVBDEVEMZVCEFVEMZVFUQURUSVBVJQUTIAABCVEDEVEUAZHRSUQUSUTVCVKQUR
      IAABCVEEFVLHRUDACVEDEFGVLUBUEVAVDDFVAVBEDBMZLZTZDFUFZVDTUQURUSVOUTABCDEGH
      UGSVPVNVDVPVMVCVBDFEBUCUHUIUJUKUNUQURUTVIVHULUSIAABCVEDFVLHUMUOUP $.
  $}

  ${
    pltletr.b $e |- B = ( Base ` K ) $.
    pltletr.l $e |- .<_ = ( le ` K ) $.
    pltletr.s $e |- .< = ( lt ` K ) $.
    $( Transitive law for chained "less than" and "less than or equal to".
       ( ~ psssstr analog.)  (Contributed by NM, 2-Dec-2011.) $)
    pltletr $p |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) )
        -> ( ( X .< Y /\ Y .<_ Z ) -> X .< Z ) ) $=
      ( cpo wcel w3a wa wbr wceq wo wb pleval2 3adant3r1 plttr expdimp wi breq2
      adantr biimpcd adantl jaod sylbid expimpd ) CKLZEALZFALZGALZMNZEFBOZFGDOZ
      EGBOZUOUPNZUQFGBOZFGPZQZURUOUQVBRZUPUKUMUNVCULABCDFGHIJSTUEUSUTURVAUOUPUT
      URABCEFGHJUAUBUPVAURUCUOVAUPURFGEBUDUFUGUHUIUJ $.

    $( Transitive law for chained "less than or equal to" and "less than".
       ( ~ sspsstr analog.)  (Contributed by NM, 2-May-2012.) $)
    plelttr $p |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) )
        -> ( ( X .<_ Y /\ Y .< Z ) -> X .< Z ) ) $=
      ( cpo wcel w3a wa wbr wceq wo wi wb pleval2 3adant3r3 plttr breq1 biimprd
      expd a1i jaod sylbid impd ) CKLZEALZFALZGALZMNZEFDOZFGBOZEGBOZUNUOEFBOZEF
      PZQZUPUQRZUJUKULUOUTSUMABCDEFHIJTUAUNURVAUSUNURUPUQABCEFGHJUBUEUSVARUNUSU
      QUPEFGBUCUDUFUGUHUI $.
  $}

  ${
    $d x y z .< $.  $d x y z .<_ $.  $d x y z B $.  $d x y z K $.
    $d x y z V $.
    pospo.b $e |- B = ( Base ` K ) $.
    pospo.l $e |- .<_ = ( le ` K ) $.
    pospo.s $e |- .< = ( lt ` K ) $.
    $( Write a poset structure in terms of the proper-class poset predicate
       (strict less than version).  (Contributed by Mario Carneiro,
       8-Feb-2015.) $)
    pospo $p |- ( K e. V ->
      ( K e. Poset <-> ( .< Po B /\ ( _I |` B ) C_ .<_ ) ) ) $=
      ( vx vy vz wcel wa cv a1i wceq wbr simpl syl2anc wi cpo wpo cid wss plttr
      cres pltirr ispod relres cop copab opabresid eqcomi eleq2i opabidw bitr3i
      wrel posref df-br bitr3id syl5ibrcom expimpd biimtrid relssdv jca cbs cfv
      breq2 cple equid wb simpr resieq mpbiri simplrr ssbrd mpd w3a wo pleval2i
      3adant1 ancoms simprl po2nr syl3an1 pm2.21d equcomd ccased syl2and simpr1
      wn 3impb simpr2 simpr3 potr sylan simpll pltle syl3anc syld breq1 biimpar
      syl5 biimpac syldan eqtr breq2d syl5ibcom isposd ex impbid2 ) CELZCUALZAB
      UBZUCAUFZDUDZMZXMXNXPXMIJKABUAABCINZHUGABCXRJNZKNZFHUEUHXMIJXODXOUQXMUCAU
      IOXRXSUJZXOLZXRALZXSXRPZMZXMYADLZYBYAYEIJUKZLYEYGXOYAXOYGIJAULUMUNYEIJUOU
      PXMYCYDYFXMYCMYFYDXRXRDQZACDXRFGURYFXRXSDQZYDYHXRXSDUSXSXRXRDVHUTVAVBVCVD
      VEXLXQXMXLXQMZIJKACDEXLXQRACVFVGPYJFODCVIVGPYJGOYJYCMZXRXRXOQZYHYKYLXRXRP
      ZIVJYKYCYCYLYMVKYJYCVLZYNAXRXRVMSVNYKXODXRXRXLXNXPYCVOVPVQZYJYCXSALZVRZYI
      XRXSBQZXRXSPZVSZXSXRDQZXSXRBQZYDVSZYSYCYPYIYTTZYJABCDXRXSFGHVTZWAYCYPUUAU
      UCTZYJYPYCUUFABCDXSXRFGHVTWBWAYQYRUUBYSYDYSYQYRUUBMZYSYJXNYCYPUUGWKZXLXNX
      PWCZXNYCYPUUHAXRXSBWDWLWEWFYSUUBMYSTYQYSUUBROYRYDMZYSTYQUUJJIYRYDVLWGOYSY
      DMYSTYQYSYDROWHWIYJYCYPXTALZVRZMZYIYTXSXTDQZXSXTBQZXSXTPZVSZXRXTDQZUUMYCY
      PUUDYJYCYPUUKWJZYJYCYPUUKWMZUUESUUMYPUUKUUNUUQTUUTYJYCYPUUKWNZABCDXSXTFGH
      VTSUUMYRUUOYSUUPUURUUMYRUUOMZXRXTBQZUURYJXNUULUVBUVCTUUIAXRXSXTBWOWPUUMXL
      YCUUKUVCUURTXLXQUULWQUUSUVAEAABCDXRXTGHWRWSZWTYSUUOMUVCUUMUURYSUVCUUOXRXS
      XTBXAXBUVDXCYRUUPMUVCUUMUURUUPYRUVCXSXTXRBVHXDUVDXCUUMYHYSUUPMZUURYJUULYC
      YHUUSYOXEUVEXRXTXRDXRXSXTXFXGXHWHWIXIXJXK $.
  $}

  ${
    $d p s x y z $.
    $( Define the least upper bound (LUB) of a set of (poset) elements.  The
       domain is restricted to exclude sets ` s ` for which the LUB doesn't
       exist uniquely.  (Contributed by NM, 12-Sep-2011.)  (Revised by NM,
       6-Sep-2018.) $)
    df-lub $a |- lub = ( p e. _V |-> ( ( s e. ~P ( Base ` p )
        |-> ( iota_ x e. ( Base ` p ) ( A. y e. s y ( le ` p ) x
                /\ A. z e. ( Base ` p )
                  ( A. y e. s y ( le ` p ) z -> x ( le ` p ) z ) ) ) )
        |` { s | E! x e. ( Base ` p ) ( A. y e. s y ( le ` p ) x
                /\ A. z e. ( Base ` p )
                  ( A. y e. s y ( le ` p ) z -> x ( le ` p ) z ) ) } ) ) $.

    $( Define the greatest lower bound (GLB) of a set of (poset) elements.  The
       domain is restricted to exclude sets ` s ` for which the GLB doesn't
       exist uniquely.  (Contributed by NM, 12-Sep-2011.)  (Revised by NM,
       6-Sep-2018.) $)
    df-glb $a |- glb = ( p e. _V |-> ( ( s e. ~P ( Base ` p )
        |-> ( iota_ x e. ( Base ` p ) ( A. y e. s x ( le ` p ) y
                /\ A. z e. ( Base ` p )
                  ( A. y e. s z ( le ` p ) y -> z ( le ` p ) x ) ) ) )
        |` { s | E! x e. ( Base ` p ) ( A. y e. s x ( le ` p ) y
                /\ A. z e. ( Base ` p )
                  ( A. y e. s z ( le ` p ) y -> z ( le ` p ) x ) ) } ) ) $.

    $( Define poset join.  (Contributed by NM, 12-Sep-2011.)  (Revised by Mario
       Carneiro, 3-Nov-2015.) $)
    df-join $a |- join = ( p e. _V
       |-> { <. <. x , y >. , z >. | { x , y } ( lub ` p ) z } ) $.

    $( Define poset meet.  (Contributed by NM, 12-Sep-2011.)  (Revised by NM,
       8-Sep-2018.) $)
    df-meet $a |- meet = ( p e. _V
       |-> { <. <. x , y >. , z >. | { x , y } ( glb ` p ) z } ) $.
  $}

  ${
    $d p s x z B $.  $d p s x y z K $.  $d p .<_ $.
    lubfval.b $e |- B = ( Base ` K ) $.
    lubfval.l $e |- .<_ = ( le ` K ) $.
    lubfval.u $e |- U = ( lub ` K ) $.
    lubfval.p $e |- ( ps
   <-> ( A. y e. s y .<_ x /\ A. z e. B ( A. y e. s y .<_ z -> x .<_ z ) ) ) $.
    lubfval.k $e |- ( ph -> K e. V ) $.
    $( Value of the least upper bound function of a poset.  (Contributed by NM,
       12-Sep-2011.)  (Revised by NM, 6-Sep-2018.) $)
    lubfval $p |- ( ph -> U = ( ( s e. ~P B
        |-> ( iota_ x e. B ps ) ) |` { s | E! x e. B ps } ) ) $=
      ( cfv cv wbr wral vp wcel cvv cpw crio cmpt wreu cab cres wceq elex wi wa
      club cbs cple fveq2 eqtr4di pweqd breqd ralbidv imbi12d raleqbidv anbi12d
      riotaeqbidv mpteq12dv reubidv wb reueq1 bitrd abbidv reseq12d df-lub pwex
      syl fvexi mptex resex fvmpt a1i riotabiia mpteq2i reubii reseq12i 3eqtr4g
      abbii 3syl ) AHJUBHUCUBZGKFUDZBCFUEZUFZBCFUGZKUHZUIZUJPHJUKWHHUNQKWIDRZCR
      ZISZDKRZTZWOERZISZDWRTZWPWTISZULZEFTZUMZCFUEZUFZXFCFUGZKUHZUIZGWNUAHKUARZ
      UOQZUDZWOWPXLUPQZSZDWRTZWOWTXOSZDWRTZWPWTXOSZULZEXMTZUMZCXMUEZUFZYCCXMUGZ
      KUHZUIXKUCUNXLHUJZYEXHYGXJYHKXNYDWIXGYHXMFYHXMHUOQFXLHUOUQLURZUSYHYCXFCXM
      FYIYHXQWSYBXEYHXPWQDWRYHXOIWOWPYHXOHUPQIXLHUPUQMURZUTVAYHYAXDEXMFYIYHXSXB
      XTXCYHXRXADWRYHXOIWOWTYJUTVAYHXOIWPWTYJUTVBVCVDZVEVFYHYFXIKYHYFXFCXMUGZXI
      YHYCXFCXMYKVGYHXMFUJYLXIVHYIXFCXMFVIVOVJVKVLCDEKUAVMXHXJKWIXGFFHUOLVPVNVQ
      VRVSNWKXHWMXJKWIWJXGBXFCFBXFVHWPFUBOVTWAWBWLXIKBXFCFOWCWFWDWEWG $.

    $( Domain of the least upper bound function of a poset.  (Contributed by
       NM, 6-Sep-2018.) $)
    lubdm $p |- ( ph -> dom U = { s e. ~P B | E! x e. B ps } ) $=
      ( cdm cpw crio cin cmpt wreu cab cres lubfval dmeqd riotaex dmmpti ineq2i
      crab eqid dmres dfrab2 3eqtr4i eqtrdi ) AGQKFRZBCFSZUAZBCFUBZKUCZUDZQZUSK
      UPUJZAGVAABCDEFGHIJKLMNOPUEUFUTURQZTUTUPTVBVCVDUPUTKUPUQURBCFUGURUKUHUIUR
      UTULUSKUPUMUNUO $.
  $}

  ${
    $d s x y z K $.
    lubfun.u $e |- U = ( lub ` K ) $.
    $( The LUB is a function.  (Contributed by NM, 9-Sep-2018.) $)
    lubfun $p |- Fun U $=
      ( vs vy vx vz cvv wcel wfun cbs cfv cv wbr wral eqid funeqd mpbiri club
      c0 cpw cple wi wa crio cmpt wreu cres funmpt funres ax-mp biid id lubfval
      cab wn fun0 fvprc eqtrid pm2.61i ) BHIZAJZVAVBDBKLZUAZEMZFMZBUBLZNEDMZOVE
      GMZVGNEVHOVFVIVGNUCGVCOUDZFVCUEZUFZVJFVCUGDUOZUHZJZVLJVODVDVKUIVMVLUJUKVA
      AVNVAVJFEGVCABVGHDVCPVGPCVJULVAUMUNQRVAUPZVBTJUQVPATVPABSLTCBSURUSQRUT $.
  $}

  ${
    $d s x z B $.  $d s x y z K $.  $d s x y z S $.  $d s ps $.
    lubeldm.b $e |- B = ( Base ` K ) $.
    lubeldm.l $e |- .<_ = ( le ` K ) $.
    lubeldm.u $e |- U = ( lub ` K ) $.
    lubeldm.p $e |- ( ps
   <-> ( A. y e. S y .<_ x /\ A. z e. B ( A. y e. S y .<_ z -> x .<_ z ) ) ) $.
    lubeldm.k $e |- ( ph -> K e. V ) $.
    $( Member of the domain of the least upper bound function of a poset.
       (Contributed by NM, 7-Sep-2018.) $)
    lubeldm $p |- ( ph -> ( S e. dom U <-> ( S C_ B /\ E! x e. B ps ) ) ) $=
      ( vs cv wral wa cdm wcel wbr wi wreu cpw crab wss biid lubdm eleq2d raleq
      wceq imbi1d ralbidv anbi12d reubidv reubii bitr4di elrab cbs fvexi anbi1i
      elpw2 bitri bitrdi ) AGHUAZUBGDRZCRZJUCZDQRZSZVHERZJUCZDVKSZVIVMJUCZUDZEF
      SZTZCFUEZQFUFZUGZUBZGFUHZBCFUEZTZAVGWBGAVSCDEFHIJKQLMNVSUIPUJUKWCGWAUBZWE
      TWFVTWEQGWAVKGUMZVTVJDGSZVNDGSZVPUDZEFSZTZCFUEWEWHVSWMCFWHVLWIVRWLVJDVKGU
      LWHVQWKEFWHVOWJVPVNDVKGULUNUOUPUQBWMCFOURUSUTWGWDWEGFFIVALVBVDVCVEVF $.
  $}

  ${
    $d x z B $.  $d x y z K $.  $d x y z S $.
    lubs.b $e |- B = ( Base ` K ) $.
    lubs.l $e |- .<_ = ( le ` K ) $.
    lubs.u $e |- U = ( lub ` K ) $.
    lubs.k $e |- ( ph -> K e. V ) $.
    lubs.s $e |- ( ph -> S e. dom U ) $.
    $( A member of the domain of the least upper bound function is a subset of
       the base set.  (Contributed by NM, 7-Sep-2018.) $)
    lubelss $p |- ( ph -> S C_ B ) $=
      ( vy vx vz wss cv wbr wral wa wi wreu cdm wcel biid lubeldm mpbid simpld
      ) ACBPZMQZNQZFRMCSUJOQZFRMCSUKULFRUAOBSTZNBUBZACDUCUDUIUNTLAUMNMOBCDEFGHI
      JUMUEKUFUGUH $.
  $}

  ${
    $d s x z B $.  $d s x y z K $.  $d s x y z S $.  $d s ps $.
    lubval.b $e |- B = ( Base ` K ) $.
    lubval.l $e |- .<_ = ( le ` K ) $.
    lubval.u $e |- U = ( lub ` K ) $.
    lubval.p $e |- ( ps <->
       ( A. y e. S y .<_ x /\ A. z e. B ( A. y e. S y .<_ z -> x .<_ z ) ) ) $.
    lubval.k $e |- ( ph -> K e. V ) $.

    ${
      lubeleu.s $e |- ( ph -> S e. dom U ) $.
      $( Unique existence proper of a member of the domain of the least upper
         bound function of a poset.  (Contributed by NM, 7-Sep-2018.) $)
      lubeu $p |- ( ph -> E! x e. B ps ) $=
        ( wss wreu cdm wcel wa lubeldm mpbid simprd ) AGFRZBCFSZAGHTUAUFUGUBQAB
        CDEFGHIJKLMNOPUCUDUE $.
    $}

    lubval.s $e |- ( ph -> S C_ B ) $.
    $( Value of the least upper bound function of a poset.  Out-of-domain
       arguments (those not satisfying ` S e. dom U ` ) are allowed for
       convenience, evaluating to the empty set.  (Contributed by NM,
       12-Sep-2011.)  (Revised by NM, 9-Sep-2018.) $)
    lubval $p |- ( ph -> ( U ` S ) = ( iota_ x e. B ps ) ) $=
      ( vs wceq wral cdm wcel cfv crio wa cpw cv wbr wi cmpt wreu cab cres biid
      adantr lubfval fveq1d simpr imbi1d ralbidv anbi12d bitr4di reubidv fvresd
      lubeu raleq elabd wss cbs fvexi elpw2 sylibr riotabidv eqid riotaex fvmpt
      syl 3eqtrd wn ndmfv adantl lubeldm biimprd mpand con3dimp riotaund eqtr4d
      c0 pm2.61dan ) AGHUAZUBZGHUCZBCFUDZSAWKUEZWLGRFUFZDUGZCUGZJUHZDRUGZTZWPEU
      GZJUHZDWSTZWQXAJUHZUIZEFTZUEZCFUDZUJZXGCFUKZRULZUMZUCGXIUCZWMWNGHXLWNXGCD
      EFHIJKRLMNXGUNAIKUBWKPUOZUPUQWNGXKXIWNXJBCFUKZRGWJAWKURZWNBCDEFGHIJKLMNOX
      NXPVEWSGSZXGBCFXQXGWRDGTZXBDGTZXDUIZEFTZUEBXQWTXRXFYAWRDWSGVFXQXEXTEFXQXC
      XSXDXBDWSGVFUSUTVAOVBZVCVGVDWNGWOUBZXMWMSWNGFVHZYCAYDWKQUOGFFIVILVJVKVLRG
      XHWMWOXIXQXGBCFYBVMXIVNBCFVOVPVQVRAWKVSZUEZWLWHWMYEWLWHSAGHVTWAYFXOVSWMWH
      SAXOWKAYDXOWKQAWKYDXOUEABCDEFGHIJKLMNOPWBWCWDWEBCFWFVQWGWI $.
  $}

  ${
    $d x z B $.  $d x y z K $.  $d x y z S $.
    lubcl.b $e |- B = ( Base ` K ) $.
    lubcl.u $e |- U = ( lub ` K ) $.
    lubcl.k $e |- ( ph -> K e. V ) $.
    lubcl.s $e |- ( ph -> S e. dom U ) $.
    $( The least upper bound function value belongs to the base set.
       (Contributed by NM, 7-Sep-2018.) $)
    lubcl $p |- ( ph -> ( U ` S ) e. B ) $=
      ( vy vx vz cfv cv cple wbr wral wi wa crio eqid biid lubelss lubval lubeu
      wreu wcel riotacl syl eqeltrd ) ACDNKOZLOZEPNZQKCRULMOZUNQKCRUMUOUNQSMBRT
      ZLBUAZBAUPLKMBCDEUNFGUNUBZHUPUCZIABCDEUNFGURHIJUDUEAUPLBUGUQBUHAUPLKMBCDE
      UNFGURHUSIJUFUPLBUIUJUK $.
  $}

  ${
    $d x z B $.  $d x y z K $.  $d x y z S $.  $d x y .<_ $.  $d x y z U $.
    $d y X $.
    lubprop.b $e |- B = ( Base ` K ) $.
    lubprop.l $e |- .<_ = ( le ` K ) $.
    lubprop.u $e |- U = ( lub ` K ) $.
    lubprop.k $e |- ( ph -> K e. V ) $.
    lubprop.s $e |- ( ph -> S e. dom U ) $.
    $( Properties of greatest lower bound of a poset.  (Contributed by NM,
       22-Oct-2011.)  (Revised by NM, 7-Sep-2018.) $)
    lubprop $p |- ( ph -> ( A. y e. S y .<_ ( U ` S )
          /\ A. z e. B ( A. y e. S y .<_ z -> ( U ` S ) .<_ z ) ) ) $=
      ( vx cv wbr wral wi wa cfv crio wceq biid lubelss lubval eqcomd wcel wreu
      wb lubcl lubeu breq2 ralbidv breq1 imbi2d anbi12d riota2 syl2anc mpbird )
      ABPZEFUAZHQZBERZVACPZHQBERZVBVEHQZSZCDRZTZVAOPZHQZBERZVFVKVEHQZSZCDRZTZOD
      UBZVBUCZAVBVRAVQOBCDEFGHIJKLVQUDZMADEFGHIJKLMNUEUFUGAVBDUHVQODUIVJVSUJADE
      FGIJLMNUKAVQOBCDEFGHIJKLVTMNULVQVJODVBVKVBUCZVMVDVPVIWAVLVCBEVKVBVAHUMUNW
      AVOVHCDWAVNVGVFVKVBVEHUOUPUNUQURUSUT $.

    luble.x $e |- ( ph -> X e. S ) $.
    $( The greatest lower bound is the least element.  (Contributed by NM,
       22-Oct-2011.)  (Revised by NM, 7-Sep-2018.) $)
    luble $p |- ( ph -> X .<_ ( U ` S ) ) $=
      ( vy vz cv cfv wbr wral breq1 wi lubprop simpld rspcdva ) AOQZCDRZFSZHUGF
      SOCHUFHUGFUAAUHOCTUFPQZFSOCTUGUIFSUBPBTAOPBCDEFGIJKLMUCUDNUE $.
  $}

  ${
    $d w x y z .<_ $.  $d w x y z B $.  $d w x z K $.  $d w x y z X $.
    $d w x ph $.
    lublecl.b $e |- B = ( Base ` K ) $.
    lublecl.l $e |- .<_ = ( le ` K ) $.
    lublecl.u $e |- U = ( lub ` K ) $.
    lublecl.k $e |- ( ph -> K e. Poset ) $.
    lublecl.x $e |- ( ph -> X e. B ) $.
    $( Lemma for ~ lublecl and ~ lubid .  (Contributed by NM, 8-Sep-2018.) $)
    lublecllem $p |- ( ( ph /\ x e. B )
    -> ( ( A. z e. { y e. B | y .<_ X } z .<_ x
       /\ A. w e. B ( A. z e. { y e. B | y .<_ X } z .<_ w -> x .<_ w ) )
          <-> x = X ) ) $=
      ( wbr wral wi wa breq1 cv crab wcel wceq ralrab imbi1i ralbii anbi12i cpo
      posref syl2anc imbi12d rspcva syl5com mpand adantr idd rgen breq2 ralbidv
      imbi2d rspcv syl wb simpr posasymb syl3anc biimpd ancomsd syl2and biimprd
      ralrimivw adantl pm5.5 bicomd sylan9bb imbitrid adantlr jca impbid bitrid
      mpii ex ) DUAZBUAZIPZDCUAZJIPZCFUBZQZWDEUAZIPZDWIQZWEWKIPZRZEFQZSWDJIPZWF
      RZDFQZWQWLRZDFQZWNRZEFQZSZAWEFUCZSZWEJUDZWJWSWPXCWHWQWFDCFWGWDJITZUEWOXBE
      FWMXAWNWHWQWLDCFXHUEUFUGUHXFXDXGXFWSJWEIPZXCWEJIPZXGAWSXIRXEAJFUCZWSXIOAJ
      JIPZXKWSSXIAHUIUCZXKXLNOFHIJKLUJUKZWRXLXIRDJFWDJUDZWQXLWFXIWDJJITZWDJWEIT
      ULUMUNUOUPAXCXJRXEAXCWQWQRZDFQZXJXQDFWDFUCWQUQURAXKXCXRXJRZROXBXSEJFWKJUD
      ZXAXRWNXJXTWTXQDFXTWLWQWQWKJWDIUSVAUTWKJWEIUSULVBVCWBUPXFXJXIXGXFXJXISZXG
      XFXMXEXKYAXGVDAXMXENUPAXEVEAXKXEOUPFHIWEJKLVFVGVHVIVJXFXGXDXFXGSWSXCXGWSX
      FXGWRDFXGWFWQWEJWDIUSVKVLVMAXGXCXEAXGSZXBEFYBXKXAWNAXKXGOUPXKXASXLJWKIPZR
      ZYBWNWTYDDJFXOWQXLWLYCXPWDJWKITULUMAYDYCXGWNAXLYDYCVDXNXLYCVNVCXGWNYCWEJW
      KITVOVPVQUOVLVRVSWCVTWA $.

    $( The set of all elements less than a given element has an LUB.
       (Contributed by NM, 8-Sep-2018.) $)
    lublecl $p |- ( ph -> { y e. B | y .<_ X } e. dom U ) $=
      ( vz vx vw cv wbr crab wcel wral cdm wss wi wa wreu ssrab2 a1i lublecllem
      wceq wb ralrimiva reu6i syl2anc cpo biid lubeldm mpbir2and ) ABPGFQZBCRZD
      UASUSCUBZMPZNPZFQMUSTVAOPZFQMUSTVBVCFQUCOCTUDZNCUEZUTAURBCUFUGAGCSVDVBGUI
      UJZNCTVELAVFNCANBMOCDEFGHIJKLUHUKVDNCGULUMAVDNMOCUSDEFUNHIJVDUOKUPUQ $.
  $}

  ${
    $d w x y z .<_ $.  $d w x y z B $.  $d w x z K $.  $d w x y z X $.
    $d w x ph $.
    lubid.b $e |- B = ( Base ` K ) $.
    lubid.l $e |- .<_ = ( le ` K ) $.
    lubid.u $e |- U = ( lub ` K ) $.
    lubid.k $e |- ( ph -> K e. Poset ) $.
    lubid.x $e |- ( ph -> X e. B ) $.
    $( The LUB of elements less than or equal to a fixed value equals that
       value.  (Contributed by NM, 19-Oct-2011.)  (Revised by NM,
       7-Sep-2018.) $)
    lubid $p |- ( ph -> ( U ` { y e. B | y .<_ X } ) = X ) $=
      ( vz vx vw cv wbr crab cfv wral wi wa crio cpo biid wss ssrab2 a1i lubval
      lublecllem riota5 eqtrd ) ABPGFQZBCRZDSMPZNPZFQMUNTUOOPZFQMUNTUPUQFQUAOCT
      UBZNCUCGAURNMOCUNDEFUDHIJURUEKUNCUFAUMBCUGUHUIAURNCGLANBMOCDEFGHIJKLUJUKU
      L $.
  $}

  ${
    $d p s x z B $.  $d p s x y z K $.  $d p .<_ $.
    glbfval.b $e |- B = ( Base ` K ) $.
    glbfval.l $e |- .<_ = ( le ` K ) $.
    glbfval.g $e |- G = ( glb ` K ) $.
    glbfval.p $e |- ( ps
   <-> ( A. y e. s x .<_ y /\ A. z e. B ( A. y e. s z .<_ y -> z .<_ x ) ) ) $.
    glbfval.k $e |- ( ph -> K e. V ) $.
    $( Value of the greatest lower function of a poset.  (Contributed by NM,
       12-Sep-2011.)  (Revised by NM, 6-Sep-2018.) $)
    glbfval $p |- ( ph -> G = ( ( s e. ~P B
        |-> ( iota_ x e. B ps ) ) |` { s | E! x e. B ps } ) ) $=
      ( cfv cv wbr wral vp wcel cvv cpw crio cmpt wreu cab cres wceq elex wi wa
      cglb cbs cple fveq2 eqtr4di pweqd breqd ralbidv imbi12d raleqbidv anbi12d
      riotaeqbidv mpteq12dv reubidv wb reueq1 bitrd abbidv reseq12d df-glb pwex
      syl fvexi mptex resex fvmpt a1i riotabiia mpteq2i reubii reseq12i 3eqtr4g
      abbii 3syl ) AHJUBHUCUBZGKFUDZBCFUEZUFZBCFUGZKUHZUIZUJPHJUKWHHUNQKWICRZDR
      ZISZDKRZTZERZWPISZDWRTZWTWOISZULZEFTZUMZCFUEZUFZXFCFUGZKUHZUIZGWNUAHKUARZ
      UOQZUDZWOWPXLUPQZSZDWRTZWTWPXOSZDWRTZWTWOXOSZULZEXMTZUMZCXMUEZUFZYCCXMUGZ
      KUHZUIXKUCUNXLHUJZYEXHYGXJYHKXNYDWIXGYHXMFYHXMHUOQFXLHUOUQLURZUSYHYCXFCXM
      FYIYHXQWSYBXEYHXPWQDWRYHXOIWOWPYHXOHUPQIXLHUPUQMURZUTVAYHYAXDEXMFYIYHXSXB
      XTXCYHXRXADWRYHXOIWTWPYJUTVAYHXOIWTWOYJUTVBVCVDZVEVFYHYFXIKYHYFXFCXMUGZXI
      YHYCXFCXMYKVGYHXMFUJYLXIVHYIXFCXMFVIVOVJVKVLCDEKUAVMXHXJKWIXGFFHUOLVPVNVQ
      VRVSNWKXHWMXJKWIWJXGBXFCFBXFVHWOFUBOVTWAWBWLXIKBXFCFOWCWFWDWEWG $.

    $( Domain of the greatest lower bound function of a poset.  (Contributed by
       NM, 6-Sep-2018.) $)
    glbdm $p |- ( ph -> dom G = { s e. ~P B | E! x e. B ps } ) $=
      ( cdm cpw crio cin cmpt wreu cab cres glbfval dmeqd riotaex dmmpti ineq2i
      crab eqid dmres dfrab2 3eqtr4i eqtrdi ) AGQKFRZBCFSZUAZBCFUBZKUCZUDZQZUSK
      UPUJZAGVAABCDEFGHIJKLMNOPUEUFUTURQZTUTUPTVBVCVDUPUTKUPUQURBCFUGURUKUHUIUR
      UTULUSKUPUMUNUO $.
  $}

  ${
    $d s x y z K $.
    glbfun.g $e |- G = ( glb ` K ) $.
    $( The GLB is a function.  (Contributed by NM, 9-Sep-2018.) $)
    glbfun $p |- Fun G $=
      ( vs vx vy vz cvv wcel wfun cbs cfv cv wbr wral eqid funeqd mpbiri cglb
      c0 cpw cple wi wa crio cmpt wreu cres funmpt funres ax-mp biid id glbfval
      cab wn fun0 fvprc eqtrid pm2.61i ) BHIZAJZVAVBDBKLZUAZEMZFMZBUBLZNFDMZOGM
      ZVFVGNFVHOVIVEVGNUCGVCOUDZEVCUEZUFZVJEVCUGDUOZUHZJZVLJVODVDVKUIVMVLUJUKVA
      AVNVAVJEFGVCABVGHDVCPVGPCVJULVAUMUNQRVAUPZVBTJUQVPATVPABSLTCBSURUSQRUT $.
  $}

  ${
    $d s x z B $.  $d s x y z K $.  $d s x y z S $.  $d s ps $.
    glbeldm.b $e |- B = ( Base ` K ) $.
    glbeldm.l $e |- .<_ = ( le ` K ) $.
    glbeldm.g $e |- G = ( glb ` K ) $.
    glbeldm.p $e |- ( ps
   <-> ( A. y e. S x .<_ y /\ A. z e. B ( A. y e. S z .<_ y -> z .<_ x ) ) ) $.
    glbeldm.k $e |- ( ph -> K e. V ) $.
    $( Member of the domain of the greatest lower bound function of a poset.
       (Contributed by NM, 7-Sep-2018.) $)
    glbeldm $p |- ( ph -> ( S e. dom G <-> ( S C_ B /\ E! x e. B ps ) ) ) $=
      ( vs cv wral wa cdm wcel wbr wi wreu cpw crab wss biid glbdm eleq2d raleq
      wceq imbi1d ralbidv anbi12d reubidv reubii bitr4di elrab cbs fvexi anbi1i
      elpw2 bitri bitrdi ) AGHUAZUBGCRZDRZJUCZDQRZSZERZVIJUCZDVKSZVMVHJUCZUDZEF
      SZTZCFUEZQFUFZUGZUBZGFUHZBCFUEZTZAVGWBGAVSCDEFHIJKQLMNVSUIPUJUKWCGWAUBZWE
      TWFVTWEQGWAVKGUMZVTVJDGSZVNDGSZVPUDZEFSZTZCFUEWEWHVSWMCFWHVLWIVRWLVJDVKGU
      LWHVQWKEFWHVOWJVPVNDVKGULUNUOUPUQBWMCFOURUSUTWGWDWEGFFIVALVBVDVCVEVF $.
  $}

  ${
    $d x z B $.  $d x y z K $.  $d x y z S $.
    glbs.b $e |- B = ( Base ` K ) $.
    glbs.l $e |- .<_ = ( le ` K ) $.
    glbs.g $e |- G = ( glb ` K ) $.
    glbs.k $e |- ( ph -> K e. V ) $.
    glbs.s $e |- ( ph -> S e. dom G ) $.
    $( A member of the domain of the greatest lower bound function is a subset
       of the base set.  (Contributed by NM, 7-Sep-2018.) $)
    glbelss $p |- ( ph -> S C_ B ) $=
      ( vx vy vz wss cv wbr wral wa wi wreu cdm wcel biid glbeldm mpbid simpld
      ) ACBPZMQZNQZFRNCSOQZUKFRNCSULUJFRUAOBSTZMBUBZACDUCUDUIUNTLAUMMNOBCDEFGHI
      JUMUEKUFUGUH $.
  $}

  ${
    $d s x z B $.  $d s x y z K $.  $d s x y z S $.  $d s ps $.
    glbval.b $e |- B = ( Base ` K ) $.
    glbval.l $e |- .<_ = ( le ` K ) $.
    glbval.g $e |- G = ( glb ` K ) $.
    glbval.p $e |- ( ps
   <-> ( A. y e. S x .<_ y /\ A. z e. B ( A. y e. S z .<_ y -> z .<_ x ) ) ) $.
    glbva.k $e |- ( ph -> K e. V ) $.
    ${
      glbval.s $e |- ( ph -> S e. dom G ) $.
      $( Unique existence proper of a member of the domain of the greatest
         lower bound function of a poset.  (Contributed by NM, 7-Sep-2018.) $)
      glbeu $p |- ( ph -> E! x e. B ps ) $=
        ( wss wreu cdm wcel wa glbeldm mpbid simprd ) AGFRZBCFSZAGHTUAUFUGUBQAB
        CDEFGHIJKLMNOPUCUDUE $.
    $}

    glbval.ss $e |- ( ph -> S C_ B ) $.
    $( Value of the greatest lower bound function of a poset.  Out-of-domain
       arguments (those not satisfying ` S e. dom U ` ) are allowed for
       convenience, evaluating to the empty set on both sides of the equality.
       (Contributed by NM, 12-Sep-2011.)  (Revised by NM, 9-Sep-2018.) $)
    glbval $p |- ( ph -> ( G ` S ) = ( iota_ x e. B ps ) ) $=
      ( vs wceq wral cdm wcel cfv crio wa cpw cv wbr wi cmpt wreu cab cres biid
      adantr glbfval fveq1d simpr imbi1d ralbidv anbi12d bitr4di reubidv fvresd
      glbeu raleq elabd wss cbs fvexi elpw2 sylibr riotabidv eqid riotaex fvmpt
      syl 3eqtrd wn ndmfv adantl glbeldm biimprd mpand con3dimp riotaund eqtr4d
      c0 pm2.61dan ) AGHUAZUBZGHUCZBCFUDZSAWKUEZWLGRFUFZCUGZDUGZJUHZDRUGZTZEUGZ
      WQJUHZDWSTZXAWPJUHZUIZEFTZUEZCFUDZUJZXGCFUKZRULZUMZUCGXIUCZWMWNGHXLWNXGCD
      EFHIJKRLMNXGUNAIKUBWKPUOZUPUQWNGXKXIWNXJBCFUKZRGWJAWKURZWNBCDEFGHIJKLMNOX
      NXPVEWSGSZXGBCFXQXGWRDGTZXBDGTZXDUIZEFTZUEBXQWTXRXFYAWRDWSGVFXQXEXTEFXQXC
      XSXDXBDWSGVFUSUTVAOVBZVCVGVDWNGWOUBZXMWMSWNGFVHZYCAYDWKQUOGFFIVILVJVKVLRG
      XHWMWOXIXQXGBCFYBVMXIVNBCFVOVPVQVRAWKVSZUEZWLWHWMYEWLWHSAGHVTWAYFXOVSWMWH
      SAXOWKAYDXOWKQAWKYDXOUEABCDEFGHIJKLMNOPWBWCWDWEBCFWFVQWGWI $.
  $}

  ${
    $d x z B $.  $d x y z K $.  $d x y z S $.
    glbc.b $e |- B = ( Base ` K ) $.
    glbc.g $e |- G = ( glb ` K ) $.
    glbc.k $e |- ( ph -> K e. V ) $.
    glbc.s $e |- ( ph -> S e. dom G ) $.
    $( The least upper bound function value belongs to the base set.
       (Contributed by NM, 7-Sep-2018.) $)
    glbcl $p |- ( ph -> ( G ` S ) e. B ) $=
      ( vx vy vz cfv cv cple wbr wral wi wa crio eqid biid glbelss glbval glbeu
      wreu wcel riotacl syl eqeltrd ) ACDNKOZLOZEPNZQLCRMOZUMUNQLCRUOULUNQSMBRT
      ZKBUAZBAUPKLMBCDEUNFGUNUBZHUPUCZIABCDEUNFGURHIJUDUEAUPKBUGUQBUHAUPKLMBCDE
      UNFGURHUSIJUFUPKBUIUJUK $.
  $}

  ${
    $d x z B $.  $d x y z K $.  $d x y z S $.  $d x y .<_ $.  $d x y z U $.
    $d y X $.
    glbprop.b $e |- B = ( Base ` K ) $.
    glbprop.l $e |- .<_ = ( le ` K ) $.
    glbprop.u $e |- U = ( glb ` K ) $.
    glbprop.k $e |- ( ph -> K e. V ) $.
    glbprop.s $e |- ( ph -> S e. dom U ) $.
    $( Properties of greatest lower bound of a poset.  (Contributed by NM,
       7-Sep-2018.) $)
    glbprop $p |- ( ph -> ( A. y e. S ( U ` S ) .<_ y
          /\ A. z e. B ( A. y e. S z .<_ y -> z .<_ ( U ` S ) ) ) ) $=
      ( vx cv wbr wral wi wa cfv crio wceq biid glbelss glbval eqcomd wcel wreu
      wb glbcl glbeu breq1 ralbidv breq2 imbi2d anbi12d riota2 syl2anc mpbird )
      AEFUAZBPZHQZBERZCPZVBHQBERZVEVAHQZSZCDRZTZOPZVBHQZBERZVFVEVKHQZSZCDRZTZOD
      UBZVAUCZAVAVRAVQOBCDEFGHIJKLVQUDZMADEFGHIJKLMNUEUFUGAVADUHVQODUIVJVSUJADE
      FGIJLMNUKAVQOBCDEFGHIJKLVTMNULVQVJODVAVKVAUCZVMVDVPVIWAVLVCBEVKVAVBHUMUNW
      AVOVHCDWAVNVGVFVKVAVEHUOUPUNUQURUSUT $.

    glble.x $e |- ( ph -> X e. S ) $.
    $( The greatest lower bound is the least element.  (Contributed by NM,
       22-Oct-2011.)  (Revised by NM, 7-Sep-2018.) $)
    glble $p |- ( ph -> ( U ` S ) .<_ X ) $=
      ( vy vz cfv cv wbr wral breq2 wi glbprop simpld rspcdva ) ACDQZORZFSZUFHF
      SOCHUGHUFFUAAUHOCTPRZUGFSOCTUIUFFSUBPBTAOPBCDEFGIJKLMUCUDNUE $.
  $}

  ${
    $d p x y z K $.  $d p z U $.
    joinfval.u $e |- U = ( lub ` K ) $.
    joinfval.j $e |- .\/ = ( join ` K ) $.
    $( Value of join function for a poset.  (Contributed by NM, 12-Sep-2011.)
       (Revised by NM, 9-Sep-2018.)  TODO: prove ~ joinfval2 first to reduce
       net proof size (existence part)? $)
    joinfval $p |- ( K e. V
             -> .\/ = { <. <. x , y >. , z >. | { x , y } U z } ) $=
      ( vp wcel cvv cv coprab wceq cfv wa eqid wal alrimiv cpr wbr elex cjn cbs
      fvex wmo moeq a1i oprabex wi wss cdm wfun wb lubfun funbrfv2b ax-mp simpl
      cple simpr lubelss ex vex prss imbitrrdi eqcom anim12d1 biimtrid ssoprab2
      biimpi syl ssexd club fveq2 eqtr4di breqd oprabbidv df-join fvmptg eqtrid
      mpdan ) FGKFLKZEAMZBMZUAZCMZDUBZABCNZOFGUCWCEFUDPZWIIWCWILKWJWIOWCWIWDFUE
      PZKWEWKKQZWGWFDPZOZQZABCNZLWPLKWCWNABCWKWKWPFUEUFZWQWNCUGWLCWMUHUIWPRUJUI
      WCWHWOUKZCSZBSZASWIWPULWCWTAWCWSBWCWRCWHWFDUMKZWMWGOZQZWCWODUNWHXCUODFHUP
      WFWGDUQURWCXAWLXBWNWCXAWFWKULZWLWCXAXDWCXAQWKWFDFFUTPZLWKRXERHWCXAUSWCXAV
      AVBVCWDWEWKAVDBVDVEVFXBWNWMWGVGVKVHVITTTWHWOABCVJVLVMJFWFWGJMZVNPZUBZABCN
      WILLUDXFFOZXHWHABCXIXGDWFWGXIXGFVNPDXFFVNVOHVPVQVRABCJVSVTWBWAVL $.

    $( Value of join function for a poset-type structure.  (Contributed by NM,
       12-Sep-2011.)  (Revised by NM, 9-Sep-2018.) $)
    joinfval2 $p |- ( K e. V
           -> .\/ = { <. <. x , y >. , z >. | ( { x , y } e. dom U
               /\ z = ( U ` { x , y } ) ) } ) $=
      ( wcel cv cpr wbr coprab cdm cfv wceq wa joinfval wfun wb funbrfv2b ax-mp
      lubfun eqcom anbi2i bitri oprabbii eqtrdi ) FGJEAKBKLZCKZDMZABCNUJDOJZUKU
      JDPZQZRZABCNABCDEFGHISULUPABCULUMUNUKQZRZUPDTULURUADFHUDUJUKDUBUCUQUOUMUN
      UKUEUFUGUHUI $.

    $( Domain of join function for a poset-type structure.  (Contributed by NM,
       16-Sep-2018.) $)
    joindm $p |- ( K e. V
            -> dom .\/ = { <. x , y >. | { x , y } e. dom U } ) $=
      ( vz wcel cdm cv cpr cfv wceq wa coprab copab joinfval2 wex dmeqd dmoprab
      fvex isseti 19.42v mpbiran2 opabbii eqtri eqtrdi ) EFJZDKALBLMZCKJZILUKCN
      ZOZPZABIQZKZULABRZUJDUPABICDEFGHSUAUQUOITZABRURUOABIUBUSULABUSULUNITIUMUK
      CUCUDULUNIUEUFUGUHUI $.
  $}

  ${
    $d x y z K $.  $d x y z U $.  $d x y z X $.  $d x y z Y $.
    joindef.u $e |- U = ( lub ` K ) $.
    joindef.j $e |- .\/ = ( join ` K ) $.
    joindef.k $e |- ( ph -> K e. V ) $.
    joindef.x $e |- ( ph -> X e. W ) $.
    joindef.y $e |- ( ph -> Y e. Z ) $.
    $( Two ways to say that a join is defined.  (Contributed by NM,
       9-Sep-2018.) $)
    joindef $p |- ( ph
       -> ( <. X , Y >. e. dom .\/ <-> { X , Y } e. dom U ) ) $=
      ( vx vy cdm wcel cv cpr cop copab wb joindm eleq2d syl preq1 eleq1d preq2
      wceq opelopabg syl2anc bitrd ) AGHUAZCQZRZUNOSZPSZTZBQZRZOPUBZRZGHTZUTRZA
      DERZUPVCUCLVFUOVBUNOPBCDEJKUDUEUFAGFRHIRVCVEUCMNVAGURTZUTRVEOPGHFIUQGUJUS
      VGUTUQGURUGUHURHUJVGVDUTURHGUIUHUKULUM $.

    $( Join value.  Since both sides evaluate to ` (/) ` when they don't exist,
       for convenience we drop the ` { X , Y } e. dom U ` requirement.
       (Contributed by NM, 9-Sep-2018.) $)
    joinval $p |- ( ph -> ( X .\/ Y ) = ( U ` { X , Y } ) ) $=
      ( vx vy vz wcel wceq wa cpr cdm co cv coprab joinfval2 oveqd adantr simpr
      cfv syl eqidd wi cvv fvexd w3a preq12 eleq1d 3adant3 simp3 fveq2d eqeq12d
      wb anbi12d moeq moani ovigg syl3anc mp2and eqtrd wn c0 cop joindef notbid
      eqid df-ov ndmfv eqtrid biimtrrdi imp adantl eqtr4d pm2.61dan ) AGHUAZBUB
      ZRZGHCUCZWEBUJZSAWGTZWHGHOUDZPUDZUAZWFRZQUDZWMBUJZSZTZOPQUEZUCZWIAWHWTSWG
      ACWSGHADERCWSSLOPQBCDEJKUFUKUGUHWJWGWIWISZWTWISZAWGUIWJWIULAWGXATZXBUMZWG
      AGFRHIRWIUNRXDMNAWEBUOWRXCOPQGHWIWSFIUNWKGSZWLHSZWOWISZUPZWNWGWQXAXEXFWNW
      GVCXGXEXFTZWMWEWFWKWLGHUQZURUSXHWOWIWPWIXEXFXGUTXEXFWPWISXGXIWMWEBXJVAUSV
      BVDWQWNQQWPVEVFWSVPVGVHUHVIVJAWGVKZTWHVLWIAXKWHVLSZAXKGHVMZCUBRZVKZXLAXNW
      GABCDEFGHIJKLMNVNVOXOWHXMCUJVLGHCVQXMCVRVSVTWAXKWIVLSAWEBVRWBWCWD $.
  $}

  ${
    joincl.b $e |- B = ( Base ` K ) $.
    joincl.j $e |- .\/ = ( join ` K ) $.
    joincl.k $e |- ( ph -> K e. V ) $.
    joincl.x $e |- ( ph -> X e. B ) $.
    joincl.y $e |- ( ph -> Y e. B ) $.
    joincl.e $e |- ( ph -> <. X , Y >. e. dom .\/ ) $.
    $( Closure of join of elements in the domain.  (Contributed by NM,
       12-Sep-2018.) $)
    joincl $p |- ( ph -> ( X .\/ Y ) e. B ) $=
      ( co cpr club cfv eqid cdm wcel joinval cop joindef mpbid lubcl eqeltrd )
      AFGCNFGOZDPQZQBAUHCDEBFGBUHRZIJKLUAABUGUHDEHUIJAFGUBCSTUGUHSTMAUHCDEBFGBU
      IIJKLUCUDUEUF $.
  $}

  ${
    $d x y .\/ $.  $d x y B $.  $d x y K $.  $d x y ph $.
    joindmss.b $e |- B = ( Base ` K ) $.
    joindmss.j $e |- .\/ = ( join ` K ) $.
    joindmss.k $e |- ( ph -> K e. V ) $.
    $( Subset property of domain of join.  (Contributed by NM, 12-Sep-2018.) $)
    joindmss $p |- ( ph -> dom .\/ C_ ( B X. B ) ) $=
      ( vx vy cdm wrel cv cfv wcel eqid cvv vex a1i wa club copab relopabv wceq
      cxp cpr joindm syl releqd mpbiri cop joindef cple adantr simpr lubelss ex
      wss prss opelxpi sylbir syl6 sylbid relssdv ) AIJCKZBBUEZAVELIMZJMZUFZDUA
      NZKOZIJUBZLVKIJUCAVEVLADEOZVEVLUDHIJVJCDEVJPZGUGUHUIUJAVGVHUKZVEOVKVOVFOZ
      AVJCDEQVGVHQVNGHVGQOAIRZSVHQOAJRZSULAVKVIBURZVPAVKVSAVKTBVIVJDDUMNZEFVTPV
      NAVMVKHUNAVKUOUPUQVSVGBOVHBOTVPVGVHBVQVRUSVGVHBBUTVAVBVCVD $.
  $}

  ${
    $d x z B $.  $d x z .\/ $.  $d x y z K $.  $d y .<_ $.  $d x y z X $.
    $d x y z Y $.
    joinval2.b $e |- B = ( Base ` K ) $.
    joinval2.l $e |- .<_ = ( le ` K ) $.
    joinval2.j $e |- .\/ = ( join ` K ) $.
    joinval2.k $e |- ( ph -> K e. V ) $.
    joinval2.x $e |- ( ph -> X e. B ) $.
    joinval2.y $e |- ( ph -> Y e. B ) $.
    $( Lemma for ~ joinval2 and ~ joineu .  (Contributed by NM, 12-Sep-2018.)
       TODO: combine this through ~ joineu into ~ joinlem ? $)
    joinval2lem $p |- ( ( X e. B /\ Y e. B )
  -> ( ( A. y e. { X , Y } y .<_ x
        /\ A. z e. B ( A. y e. { X , Y } y .<_ z -> x .<_ z ) )
  <-> ( ( X .<_ x /\ Y .<_ x )
        /\ A. z e. B ( ( X .<_ z /\ Y .<_ z ) -> x .<_ z ) ) ) ) $=
      ( wbr wral breq1 wcel wa cv cpr wi ralprg imbi1d ralbidv anbi12d ) JEUAKE
      UAUBZCUCZBUCZHRZCJKUDZSJULHRZKULHRZUBUKDUCZHRZCUNSZULUQHRZUEZDESJUQHRZKUQ
      HRZUBZUTUEZDESUMUOUPCJKEEUKJULHTUKKULHTUFUJVAVEDEUJUSVDUTURVBVCCJKEEUKJUQ
      HTUKKUQHTUFUGUHUI $.

    $( Value of join for a poset with LUB expanded.  (Contributed by NM,
       16-Sep-2011.)  (Revised by NM, 11-Sep-2018.) $)
    joinval2 $p |- ( ph ->
      ( X .\/ Y ) = ( iota_ x e. B ( ( X .<_ x /\ Y .<_ x )
              /\ A. z e. B ( ( X .<_ z /\ Y .<_ z ) -> x .<_ z ) ) ) ) $=
      ( vy wbr wral wa co cpr club cfv cv wi crio eqid joinval biid lubval wcel
      prssd wceq joinval2lem riotabidv syl2anc 3eqtrd ) AIJEUAIJUBZFUCUDZUDQUEZ
      BUEZGRQUSSVACUEZGRQUSSVBVCGRZUFCDSTZBDUGZIVBGRJVBGRTIVCGRJVCGRTVDUFCDSTZB
      DUGZAUTEFHDIJDUTUHZMNOPUIAVEBQCDUSUTFGHKLVIVEUJNAIJDOPUMUKAIDULZJDULZVFVH
      UNOPVJVKTVEVGBDABQCDEFGHIJKLMNOPUOUPUQUR $.

    $d x ph $.
    joinlem.e $e |- ( ph -> <. X , Y >. e. dom .\/ ) $.
    $( Uniqueness of join of elements in the domain.  (Contributed by NM,
       12-Sep-2018.) $)
    joineu $p |- ( ph -> E! x e. B ( ( X .<_ x /\ Y .<_ x )
              /\ A. z e. B ( ( X .<_ z /\ Y .<_ z ) -> x .<_ z ) ) ) $=
      ( vy wcel wbr cop cdm cv wa wi wral wreu cpr club cfv eqid joindef adantr
      biid simpr lubeu ex wb joinval2lem syl2anc reubidv sylibd sylbid mpd ) AI
      JUAEUBSZIBUCZGTJVFGTUDICUCZGTJVGGTUDVFVGGTZUECDUFUDZBDUGZQAVEIJUHZFUIUJZU
      BSZVJAVLEFHDIJDVLUKZMNOPULAVMRUCZVFGTRVKUFVOVGGTRVKUFVHUECDUFUDZBDUGZVJAV
      MVQAVMUDVPBRCDVKVLFGHKLVNVPUNAFHSVMNUMAVMUOUPUQAVPVIBDAIDSJDSVPVIUROPABRC
      DEFGHIJKLMNOPUSUTVAVBVCVD $.

    $d x .<_ $.
    $( Lemma for join properties.  (Contributed by NM, 16-Sep-2011.)  (Revised
       by NM, 12-Sep-2018.) $)
    joinlem $p |- ( ph -> ( ( X .<_ ( X .\/ Y ) /\ Y .<_ ( X .\/ Y ) )
            /\ A. z e. B ( ( X .<_ z /\ Y .<_ z ) -> ( X .\/ Y ) .<_ z ) ) ) $=
      ( vx cv wbr wa wi wral co wsbc crio wreu joineu riotasbc joinval2 sbceq1d
      syl mpbird ovex wceq breq2 anbi12d breq1 imbi2d ralbidv sbcie sylib ) AHQ
      RZFSZIVBFSZTZHBRZFSIVFFSTZVBVFFSZUAZBCUBZTZQHIDUCZUDZHVLFSZIVLFSZTZVGVLVF
      FSZUAZBCUBZTZAVMVKQVKQCUEZUDZAVKQCUFWBAQBCDEFGHIJKLMNOPUGVKQCUHUKAVKQVLWA
      AQBCDEFGHIJKLMNOUIUJULVKVTQVLHIDUMVBVLUNZVEVPVJVSWCVCVNVDVOVBVLHFUOVBVLIF
      UOUPWCVIVRBCWCVHVQVGVBVLVFFUQURUSUPUTVA $.

    $( A join's first argument is less than or equal to the join.  (Contributed
       by NM, 16-Sep-2011.) $)
    lejoin1 $p |- ( ph -> X .<_ ( X .\/ Y ) ) $=
      ( vz co wbr cv wa wi wral joinlem simplld ) AGGHCQZERHUEERGPSZERHUFERTUEU
      FERUAPBUBAPBCDEFGHIJKLMNOUCUD $.

    $( A join's second argument is less than or equal to the join.
       (Contributed by NM, 16-Sep-2011.) $)
    lejoin2 $p |- ( ph -> Y .<_ ( X .\/ Y ) ) $=
      ( vz co wbr cv wa wi wral joinlem simplrd ) AGGHCQZERHUEERGPSZERHUFERTUEU
      FERUAPBUBAPBCDEFGHIJKLMNOUCUD $.
  $}

  ${
    $d z B $.  $d z .\/ $.  $d z K $.  $d z .<_ $.  $d z X $.  $d z Y $.
    $d z Z $.
    joinle.b $e |- B = ( Base ` K ) $.
    joinle.l $e |- .<_ = ( le ` K ) $.
    joinle.j $e |- .\/ = ( join ` K ) $.
    joinle.k $e |- ( ph -> K e. Poset ) $.
    joinle.x $e |- ( ph -> X e. B ) $.
    joinle.y $e |- ( ph -> Y e. B ) $.
    joinle.z $e |- ( ph -> Z e. B ) $.
    joinle.e $e |- ( ph -> <. X , Y >. e. dom .\/ ) $.
    $( A join is less than or equal to a third value iff each argument is less
       than or equal to the third value.  (Contributed by NM, 16-Sep-2011.) $)
    joinle $p |- ( ph -> ( ( X .<_ Z /\ Y .<_ Z ) <-> ( X .\/ Y ) .<_ Z ) ) $=
      ( wbr wa cpo wcel vz co cv wceq breq2 anbi12d imbi12d wral joinlem simprd
      wi rspcdva lejoin1 joincl postr syl13anc mpand lejoin2 jcad impbid ) AFHE
      QZGHEQZRZFGCUBZHEQZAFUAUCZEQZGVFEQZRZVDVFEQZUKZVCVEUKUABHVFHUDZVIVCVJVEVL
      VGVAVHVBVFHFEUEVFHGEUEUFVFHVDEUEUGAFVDEQZGVDEQZRVKUABUHAUABCDESFGIJKLMNPU
      IUJOULAVEVAVBAVMVEVAABCDESFGIJKLMNPUMADSTZFBTVDBTZHBTZVMVERVAUKLMABCDSFGI
      KLMNPUNZOBDEFVDHIJUOUPUQAVNVEVBABCDESFGIJKLMNPURAVOGBTVPVQVNVERVBUKLNVROB
      DEGVDHIJUOUPUQUSUT $.
  $}

  ${
    $d p x y z K $.  $d p z G $.
    meetfval.u $e |- G = ( glb ` K ) $.
    meetfval.m $e |- ./\ = ( meet ` K ) $.
    $( Value of meet function for a poset.  (Contributed by NM, 12-Sep-2011.)
       (Revised by NM, 9-Sep-2018.)  TODO: prove ~ meetfval2 first to reduce
       net proof size (existence part)? $)
    meetfval $p |- ( K e. V
             -> ./\ = { <. <. x , y >. , z >. | { x , y } G z } ) $=
      ( vp wcel cvv cv coprab wceq cfv wa eqid wal alrimiv cpr wbr elex cbs wmo
      cmee fvex moeq a1i oprabex wi wss cdm wfun wb glbfun funbrfv2b ax-mp cple
      simpl simpr glbelss vex imbitrrdi eqcom biimpi anim12d1 biimtrid ssoprab2
      ex prss syl ssexd cglb fveq2 eqtr4di breqd oprabbidv df-meet fvmptg mpdan
      eqtrid ) EGKELKZFAMZBMZUAZCMZDUBZABCNZOEGUCWCFEUFPZWIIWCWILKWJWIOWCWIWDEU
      DPZKWEWKKQZWGWFDPZOZQZABCNZLWPLKWCWNABCWKWKWPEUDUGZWQWNCUEWLCWMUHUIWPRUJU
      IWCWHWOUKZCSZBSZASWIWPULWCWTAWCWSBWCWRCWHWFDUMKZWMWGOZQZWCWODUNWHXCUODEHU
      PWFWGDUQURWCXAWLXBWNWCXAWFWKULZWLWCXAXDWCXAQWKWFDEEUSPZLWKRXERHWCXAUTWCXA
      VAVBVJWDWEWKAVCBVCVKVDXBWNWMWGVEVFVGVHTTTWHWOABCVIVLVMJEWFWGJMZVNPZUBZABC
      NWILLUFXFEOZXHWHABCXIXGDWFWGXIXGEVNPDXFEVNVOHVPVQVRABCJVSVTWAWBVL $.

    $( Value of meet function for a poset.  (Contributed by NM, 12-Sep-2011.)
       (Revised by NM, 9-Sep-2018.) $)
    meetfval2 $p |- ( K e. V
           -> ./\ = { <. <. x , y >. , z >. | ( { x , y } e. dom G
               /\ z = ( G ` { x , y } ) ) } ) $=
      ( wcel cv cpr wbr coprab cdm cfv wceq wa meetfval wfun wb funbrfv2b ax-mp
      glbfun eqcom anbi2i bitri oprabbii eqtrdi ) EGJFAKBKLZCKZDMZABCNUJDOJZUKU
      JDPZQZRZABCNABCDEFGHISULUPABCULUMUNUKQZRZUPDTULURUADEHUDUJUKDUBUCUQUOUMUN
      UKUEUFUGUHUI $.

    $( Domain of meet function for a poset-type structure.  (Contributed by NM,
       16-Sep-2018.) $)
    meetdm $p |- ( K e. V
            -> dom ./\ = { <. x , y >. | { x , y } e. dom G } ) $=
      ( vz wcel cdm cv cpr cfv wceq wa coprab copab meetfval2 wex dmeqd dmoprab
      fvex isseti 19.42v mpbiran2 opabbii eqtri eqtrdi ) DFJZEKALBLMZCKJZILUKCN
      ZOZPZABIQZKZULABRZUJEUPABICDEFGHSUAUQUOITZABRURUOABIUBUSULABUSULUNITIUMUK
      CUCUDULUNIUEUFUGUHUI $.
  $}

  ${
    $d x y z K $.  $d x y z G $.  $d x y z X $.  $d x y z Y $.
    meetdef.u $e |- G = ( glb ` K ) $.
    meetdef.m $e |- ./\ = ( meet ` K ) $.
    meetdef.k $e |- ( ph -> K e. V ) $.
    meetdef.x $e |- ( ph -> X e. W ) $.
    meetdef.y $e |- ( ph -> Y e. Z ) $.
    $( Two ways to say that a meet is defined.  (Contributed by NM,
       9-Sep-2018.) $)
    meetdef $p |- ( ph
       -> ( <. X , Y >. e. dom ./\ <-> { X , Y } e. dom G ) ) $=
      ( vx vy cdm wcel cv cpr cop copab wb meetdm eleq2d syl preq1 eleq1d preq2
      wceq opelopabg syl2anc bitrd ) AGHUAZDQZRZUNOSZPSZTZBQZRZOPUBZRZGHTZUTRZA
      CERZUPVCUCLVFUOVBUNOPBCDEJKUDUEUFAGFRHIRVCVEUCMNVAGURTZUTRVEOPGHFIUQGUJUS
      VGUTUQGURUGUHURHUJVGVDUTURHGUIUHUKULUM $.

    $( Meet value.  Since both sides evaluate to ` (/) ` when they don't exist,
       for convenience we drop the ` { X , Y } e. dom G ` requirement.
       (Contributed by NM, 9-Sep-2018.) $)
    meetval $p |- ( ph -> ( X ./\ Y ) = ( G ` { X , Y } ) ) $=
      ( vx vy vz wcel wceq wa cpr cdm co cv coprab meetfval2 oveqd adantr simpr
      cfv syl eqidd wi cvv fvexd w3a preq12 eleq1d 3adant3 simp3 fveq2d eqeq12d
      wb anbi12d moeq moani ovigg syl3anc mp2and eqtrd wn c0 cop meetdef notbid
      eqid df-ov ndmfv eqtrid biimtrrdi imp adantl eqtr4d pm2.61dan ) AGHUAZBUB
      ZRZGHDUCZWEBUJZSAWGTZWHGHOUDZPUDZUAZWFRZQUDZWMBUJZSZTZOPQUEZUCZWIAWHWTSWG
      ADWSGHACERDWSSLOPQBCDEJKUFUKUGUHWJWGWIWISZWTWISZAWGUIWJWIULAWGXATZXBUMZWG
      AGFRHIRWIUNRXDMNAWEBUOWRXCOPQGHWIWSFIUNWKGSZWLHSZWOWISZUPZWNWGWQXAXEXFWNW
      GVCXGXEXFTZWMWEWFWKWLGHUQZURUSXHWOWIWPWIXEXFXGUTXEXFWPWISXGXIWMWEBXJVAUSV
      BVDWQWNQQWPVEVFWSVPVGVHUHVIVJAWGVKZTWHVLWIAXKWHVLSZAXKGHVMZDUBRZVKZXLAXNW
      GABCDEFGHIJKLMNVNVOXOWHXMDUJVLGHDVQXMDVRVSVTWAXKWIVLSAWEBVRWBWCWD $.
  $}

  ${
    meetcl.b $e |- B = ( Base ` K ) $.
    meetcl.m $e |- ./\ = ( meet ` K ) $.
    meetcl.k $e |- ( ph -> K e. V ) $.
    meetcl.x $e |- ( ph -> X e. B ) $.
    meetcl.y $e |- ( ph -> Y e. B ) $.
    meetcl.e $e |- ( ph -> <. X , Y >. e. dom ./\ ) $.
    $( Closure of meet of elements in the domain.  (Contributed by NM,
       12-Sep-2018.) $)
    meetcl $p |- ( ph -> ( X ./\ Y ) e. B ) $=
      ( co cpr cglb cfv eqid cdm wcel meetval cop meetdef mpbid glbcl eqeltrd )
      AFGDNFGOZCPQZQBAUHCDEBFGBUHRZIJKLUAABUGUHCEHUIJAFGUBDSTUGUHSTMAUHCDEBFGBU
      IIJKLUCUDUEUF $.
  $}

  ${
    $d x y ./\ $.  $d x y B $.  $d x y K $.  $d x y ph $.
    meetdmss.b $e |- B = ( Base ` K ) $.
    meetdmss.j $e |- ./\ = ( meet ` K ) $.
    meetdmss.k $e |- ( ph -> K e. V ) $.
    $( Subset property of domain of meet.  (Contributed by NM, 12-Sep-2018.) $)
    meetdmss $p |- ( ph -> dom ./\ C_ ( B X. B ) ) $=
      ( vx vy cdm wrel cv cfv wcel eqid cvv vex a1i wa cglb copab relopabv wceq
      cxp cpr meetdm syl releqd mpbiri cop meetdef cple adantr simpr glbelss ex
      wss prss opelxpi sylbir syl6 sylbid relssdv ) AIJDKZBBUEZAVELIMZJMZUFZCUA
      NZKOZIJUBZLVKIJUCAVEVLACEOZVEVLUDHIJVJCDEVJPZGUGUHUIUJAVGVHUKZVEOVKVOVFOZ
      AVJCDEQVGVHQVNGHVGQOAIRZSVHQOAJRZSULAVKVIBURZVPAVKVSAVKTBVIVJCCUMNZEFVTPV
      NAVMVKHUNAVKUOUPUQVSVGBOVHBOTVPVGVHBVQVRUSVGVHBBUTVAVBVCVD $.
  $}

  ${
    $d x z B $.  $d x z ./\ $.  $d x y z K $.  $d y .<_ $.  $d x y z X $.
    $d x y z Y $.
    meetval2.b $e |- B = ( Base ` K ) $.
    meetval2.l $e |- .<_ = ( le ` K ) $.
    meetval2.m $e |- ./\ = ( meet ` K ) $.
    meetval2.k $e |- ( ph -> K e. V ) $.
    meetval2.x $e |- ( ph -> X e. B ) $.
    meetval2.y $e |- ( ph -> Y e. B ) $.
    $( Lemma for ~ meetval2 and ~ meeteu .  (Contributed by NM, 12-Sep-2018.)
       TODO: combine this through ~ meeteu into ~ meetlem ? $)
    meetval2lem $p |- ( ( X e. B /\ Y e. B )
  -> ( ( A. y e. { X , Y } x .<_ y
        /\ A. z e. B ( A. y e. { X , Y } z .<_ y -> z .<_ x ) )
  <-> ( ( x .<_ X /\ x .<_ Y )
        /\ A. z e. B ( ( z .<_ X /\ z .<_ Y ) -> z .<_ x ) ) ) ) $=
      ( wbr wral breq2 wcel wa cv cpr wi ralprg imbi1d ralbidv anbi12d ) JEUAKE
      UAUBZBUCZCUCZGRZCJKUDZSUKJGRZUKKGRZUBDUCZULGRZCUNSZUQUKGRZUEZDESUQJGRZUQK
      GRZUBZUTUEZDESUMUOUPCJKEEULJUKGTULKUKGTUFUJVAVEDEUJUSVDUTURVBVCCJKEEULJUQ
      GTULKUQGTUFUGUHUI $.

    $( Value of meet for a poset with LUB expanded.  (Contributed by NM,
       16-Sep-2011.)  (Revised by NM, 11-Sep-2018.) $)
    meetval2 $p |- ( ph ->
      ( X ./\ Y ) = ( iota_ x e. B ( ( x .<_ X /\ x .<_ Y )
              /\ A. z e. B ( ( z .<_ X /\ z .<_ Y ) -> z .<_ x ) ) ) ) $=
      ( vy wbr wral wa co cpr cglb cfv cv wi crio eqid meetval biid glbval wcel
      prssd wceq meetval2lem riotabidv syl2anc 3eqtrd ) AIJGUAIJUBZEUCUDZUDBUEZ
      QUEZFRQUSSCUEZVBFRQUSSVCVAFRZUFCDSTZBDUGZVAIFRVAJFRTVCIFRVCJFRTVDUFCDSTZB
      DUGZAUTEGHDIJDUTUHZMNOPUIAVEBQCDUSUTEFHKLVIVEUJNAIJDOPUMUKAIDULZJDULZVFVH
      UNOPVJVKTVEVGBDABQCDEFGHIJKLMNOPUOUPUQUR $.

    $d x ph $.
    meetlem.e $e |- ( ph -> <. X , Y >. e. dom ./\ ) $.
    $( Uniqueness of meet of elements in the domain.  (Contributed by NM,
       12-Sep-2018.) $)
    meeteu $p |- ( ph -> E! x e. B ( ( x .<_ X /\ x .<_ Y )
              /\ A. z e. B ( ( z .<_ X /\ z .<_ Y ) -> z .<_ x ) ) ) $=
      ( vy wcel wbr cop cdm cv wa wi wral wreu cpr cglb cfv eqid meetdef adantr
      biid simpr glbeu ex wb meetval2lem syl2anc reubidv sylibd sylbid mpd ) AI
      JUAGUBSZBUCZIFTVFJFTUDCUCZIFTVGJFTUDVGVFFTZUECDUFUDZBDUGZQAVEIJUHZEUIUJZU
      BSZVJAVLEGHDIJDVLUKZMNOPULAVMVFRUCZFTRVKUFVGVOFTRVKUFVHUECDUFUDZBDUGZVJAV
      MVQAVMUDVPBRCDVKVLEFHKLVNVPUNAEHSVMNUMAVMUOUPUQAVPVIBDAIDSJDSVPVIUROPABRC
      DEFGHIJKLMNOPUSUTVAVBVCVD $.

    $d x .<_ $.
    $( Lemma for meet properties.  (Contributed by NM, 16-Sep-2011.)  (Revised
       by NM, 12-Sep-2018.) $)
    meetlem $p |- ( ph -> ( ( ( X ./\ Y ) .<_ X /\ ( X ./\ Y ) .<_ Y )
            /\ A. z e. B ( ( z .<_ X /\ z .<_ Y ) -> z .<_ ( X ./\ Y ) ) ) ) $=
      ( vx cv wbr wa wi wral co wsbc crio wreu meeteu riotasbc meetval2 sbceq1d
      syl mpbird ovex wceq breq1 anbi12d breq2 imbi2d ralbidv sbcie sylib ) AQR
      ZHESZVBIESZTZBRZHESVFIESTZVFVBESZUAZBCUBZTZQHIFUCZUDZVLHESZVLIESZTZVGVFVL
      ESZUAZBCUBZTZAVMVKQVKQCUEZUDZAVKQCUFWBAQBCDEFGHIJKLMNOPUGVKQCUHUKAVKQVLWA
      AQBCDEFGHIJKLMNOUIUJULVKVTQVLHIFUMVBVLUNZVEVPVJVSWCVCVNVDVOVBVLHEUOVBVLIE
      UOUPWCVIVRBCWCVHVQVGVBVLVFEUQURUSUPUTVA $.

    $( A meet's first argument is less than or equal to the meet.  (Contributed
       by NM, 16-Sep-2011.)  (Revised by NM, 12-Sep-2018.) $)
    lemeet1 $p |- ( ph -> ( X ./\ Y ) .<_ X ) $=
      ( vz co wbr cv wa wi wral meetlem simplld ) AGHEQZGDRUEHDRPSZGDRUFHDRTUFU
      EDRUAPBUBAPBCDEFGHIJKLMNOUCUD $.

    $( A meet's second argument is less than or equal to the meet.
       (Contributed by NM, 16-Sep-2011.)  (Revised by NM, 12-Sep-2018.) $)
    lemeet2 $p |- ( ph -> ( X ./\ Y ) .<_ Y ) $=
      ( vz co wbr cv wa wi wral meetlem simplrd ) AGHEQZGDRUEHDRPSZGDRUFHDRTUFU
      EDRUAPBUBAPBCDEFGHIJKLMNOUCUD $.
  $}

  ${
    $d z B $.  $d z ./\ $.  $d z K $.  $d z .<_ $.  $d z X $.  $d z Y $.
    $d z Z $.
    meetle.b $e |- B = ( Base ` K ) $.
    meetle.l $e |- .<_ = ( le ` K ) $.
    meetle.m $e |- ./\ = ( meet ` K ) $.
    meetle.k $e |- ( ph -> K e. Poset ) $.
    meetle.x $e |- ( ph -> X e. B ) $.
    meetle.y $e |- ( ph -> Y e. B ) $.
    meetle.z $e |- ( ph -> Z e. B ) $.
    meetle.e $e |- ( ph -> <. X , Y >. e. dom ./\ ) $.
    $( A meet is less than or equal to a third value iff each argument is less
       than or equal to the third value.  (Contributed by NM, 16-Sep-2011.)
       (Revised by NM, 12-Sep-2018.) $)
    meetle $p |- ( ph -> ( ( Z .<_ X /\ Z .<_ Y ) <-> Z .<_ ( X ./\ Y ) ) ) $=
      ( wbr wa cpo wcel vz co cv wceq breq1 anbi12d imbi12d wral meetlem simprd
      wi rspcdva lemeet1 meetcl postr syl13anc mpan2d lemeet2 jcad impbid ) AHF
      DQZHGDQZRZHFGEUBZDQZAUAUCZFDQZVFGDQZRZVFVDDQZUKZVCVEUKUABHVFHUDZVIVCVJVEV
      LVGVAVHVBVFHFDUEVFHGDUEUFVFHVDDUEUGAVDFDQZVDGDQZRVKUABUHAUABCDESFGIJKLMNP
      UIUJOULAVEVAVBAVEVMVAABCDESFGIJKLMNPUMACSTZHBTZVDBTZFBTVEVMRVAUKLOABCESFG
      IKLMNPUNZMBCDHVDFIJUOUPUQAVEVNVBABCDESFGIJKLMNPURAVOVPVQGBTVEVNRVBUKLOVRN
      BCDHVDGIJUOUPUQUSUT $.
  $}

  ${
    joincom.b $e |- B = ( Base ` K ) $.
    joincom.j $e |- .\/ = ( join ` K ) $.
    $( The join of a poset is commutative.  (This may not be a theorem under
       other definitions of meet.)  (Contributed by NM, 16-Sep-2011.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    joincomALT $p |- ( ( K e. V /\ X e. B /\ Y e. B ) -> ( X .\/ Y ) =
              ( Y .\/ X ) ) $=
      ( wcel w3a cpr club cfv co wceq prcom fveq2i a1i eqid joinval simp1 simp3
      simp2 3eqtr4rd ) CDIZEAIZFAIZJZFEKZCLMZMZEFKZUJMZFEBNEFBNUKUMOUHUIULUJFEP
      QRUHUJBCDAFEAUJSZHUEUFUGUAZUEUFUGUBZUEUFUGUCZTUHUJBCDAEFAUNHUOUQUPTUD $.

    $( The join of a poset is commutative.  (The antecedent
       ` <. X , Y >. e. dom .\/ /\ <. Y , X >. e. dom .\/ ` i.e., "the joins
       exist" could be omitted as an artifact of our particular join
       definition, but other definitions may require it.)  (Contributed by NM,
       16-Sep-2011.)  (Revised by NM, 12-Sep-2018.) $)
    joincom $p |- ( ( ( K e. Poset /\ X e. B /\ Y e. B ) /\
   ( <. X , Y >. e. dom .\/ /\ <. Y , X >. e. dom .\/ ) )
           -> ( X .\/ Y ) = ( Y .\/ X ) ) $=
      ( cpo wcel w3a co wceq cop cdm wa joincomALT adantr ) CHIDAIEAIJDEBKEDBKL
      DEMBNZIEDMRIOABCHDEFGPQ $.
  $}

  ${
    meetcom.b $e |- B = ( Base ` K ) $.
    meetcom.m $e |- ./\ = ( meet ` K ) $.
    $( The meet of a poset is commutative.  (This may not be a theorem under
       other definitions of meet.)  (Contributed by NM, 17-Sep-2011.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    meetcomALT $p |- ( ( K e. V /\ X e. B /\ Y e. B ) -> ( X ./\ Y ) =
              ( Y ./\ X ) ) $=
      ( wcel w3a cpr cglb cfv co wceq prcom fveq2i a1i eqid meetval simp1 simp3
      simp2 3eqtr4rd ) BDIZEAIZFAIZJZFEKZBLMZMZEFKZUJMZFECNEFCNUKUMOUHUIULUJFEP
      QRUHUJBCDAFEAUJSZHUEUFUGUAZUEUFUGUBZUEUFUGUCZTUHUJBCDAEFAUNHUOUQUPTUD $.

    $( The meet of a poset is commutative.  (The antecedent
       ` <. X , Y >. e. dom ./\ /\ <. Y , X >. e. dom ./\ ` i.e., "the meets
       exist" could be omitted as an artifact of our particular join
       definition, but other definitions may require it.)  (Contributed by NM,
       17-Sep-2011.)  (Revised by NM, 12-Sep-2018.) $)
    meetcom $p |- ( ( ( K e. Poset /\ X e. B /\ Y e. B ) /\
   ( <. X , Y >. e. dom ./\ /\ <. Y , X >. e. dom ./\ ) )
           -> ( X ./\ Y ) = ( Y ./\ X ) ) $=
      ( cpo wcel w3a co wceq cop cdm wa meetcomALT adantr ) BHIDAIEAIJDECKEDCKL
      DEMCNZIEDMRIOABCHDEFGPQ $.
  $}

  ${
    $d x y z w $.
    $( Lemma for ~ odumeet .  (Contributed by Stefan O'Rear, 29-Jan-2015.) $)
    join0 $p |- ( join ` (/) ) = (/) $=
      ( vx vy vz vw c0 cfv cv wbr cvv wceq 0ex eqid ax-mp cop wa wex wral eqtri
      cab nex cjn cpr club coprab wcel joinfval df-oprab br0 cpw cple crio cmpt
      wi wreu cres base0 biid lubfval reu0 abf reseq2i res0 breqi mtbir intnan
      id ) EUAFZAGZBGZUBZCGZEUCFZHZABCUDZEEIUEZVGVNJKABCVLVGEIVLLZVGLUFMVNDGZVH
      VINVKNJZVMOZCPZBPZAPZDSEVMABCDUGWBDWAAVTBVSCVMVRVMVJVKEHVJVKUHVJVKVLEVLDE
      UIVHVKEUJFZHAVQQVHVIWCHAVQQVKVIWCHUMBEQOZCEUKULZWDCEUNZDSZUOZEVOVLWHJKVOW
      DCABEVLEWCIDUPWCLVPWDUQVOVFURMWHWEEUOEWGEWEWFDWDCUSUTVAWEVBRRVCVDVETTTUTR
      R $.

    $( Lemma for ~ odujoin .  (Contributed by Stefan O'Rear, 29-Jan-2015.)
       TODO ( ~ df-riota update):  This proof increased from 152 bytes to 547
       bytes after the ~ df-riota change.  Any way to shorten it? ~ join0
       also. $)
    meet0 $p |- ( meet ` (/) ) = (/) $=
      ( vx vy vz vw c0 cfv cv wbr cvv wceq 0ex eqid ax-mp cop wa wex wral eqtri
      cab nex cmee cpr cglb coprab wcel meetfval df-oprab br0 cple wi crio cmpt
      cpw wreu cres base0 biid glbfval reu0 abf reseq2i res0 breqi mtbir intnan
      id ) EUAFZAGZBGZUBZCGZEUCFZHZABCUDZEEIUEZVGVNJKABCVLEVGIVLLZVGLUFMVNDGZVH
      VINVKNJZVMOZCPZBPZAPZDSEVMABCDUGWBDWAAVTBVSCVMVRVMVJVKEHVJVKUHVJVKVLEVLAE
      UMVIVKEUIFZHCVHQVQVKWCHCVHQVQVIWCHUJDEQOZBEUKULZWDBEUNZASZUOZEVOVLWHJKVOW
      DBCDEVLEWCIAUPWCLVPWDUQVOVFURMWHWEEUOEWGEWEWFAWDBUSUTVAWEVBRRVCVDVETTTUTR
      R $.
  $}

  ${
    $d D a b c d $.  $d L a b c d $.  $d U a b c d $.  $d O a b c d $.
    $d V a b c d $.  $d .\/ a b $.  $d ./\ a b $.
    oduglb.d $e |- D = ( ODual ` O ) $.

    ${
      odulub.l $e |- L = ( glb ` O ) $.
      $( Least upper bounds in a dual order are greatest lower bounds in the
         original order.  (Contributed by Stefan O'Rear, 29-Jan-2015.) $)
      odulub $p |- ( O e. V -> L = ( lub ` D ) ) $=
        ( va vb vc vd wcel cfv cv wbr wral wi vex brcnv ralbii eqid cglb cbs wa
        club cpw cple crio cmpt wreu cab cres ccnv wb imbi12i anbi12i riotabiia
        a1i mpteq2i reubii abbii reseq12i eqcomi biid id glbfval cvv wceq fvexi
        codu odubas oduleval lubfval mp1i 3eqtr4a eqtrid ) CDKZBCUALZAUDLZFVPGC
        UBLZUEZHMZIMZCUFLZNZIGMZOZJMZWBWCNZIWEOZWGWAWCNZPZJVSOZUCZHVSUGZUHZWMHV
        SUIZGUJZUKZGVTWBWAWCULZNZIWEOZWBWGWSNZIWEOZWAWGWSNZPZJVSOZUCZHVSUGZUHZX
        GHVSUIZGUJZUKZVQVRXLWRXIWOXKWQGVTXHWNXGWMHVSXGWMUMWAVSKXAWFXFWLWTWDIWEW
        BWAWCIQZHQZRSXEWKJVSXCWIXDWJXBWHIWEWBWGWCXMJQZRSWAWGWCXNXORUNSUOZUQUPUR
        XJWPGXGWMHVSXPUSUTVAVBVPWMHIJVSVQCWCDGVSTZWCTZVQTWMVCVPVDVEAVFKZVRXLVGV
        PACVIEVHXSXGHIJVSVRAWSVFGVSACEXQVJAWCCEXRVKVRTXGVCXSVDVLVMVNVO $.
    $}

    ${
      odujoin.m $e |- ./\ = ( meet ` O ) $.
      $( Joins in a dual order are meets in the original.  (Contributed by
         Stefan O'Rear, 29-Jan-2015.) $)
      odujoin $p |- ./\ = ( join ` D ) $=
        ( va vb vc cmee cfv cjn cvv wcel wceq cv wbr coprab eqid codu c0 odulub
        cglb club breqd oprabbidv meetfval fvexi joinfval mp1i 3eqtr4d wn fvprc
        cpr eqtrid fveq2d join0 eqtrdi eqtr4d pm2.61i eqtri ) BCIJZAKJZECLMZVAV
        BNVCFOGOUMZHOZCUBJZPZFGHQVDVEAUCJZPZFGHQZVAVBVCVGVIFGHVCVFVHVDVEAVFCLDV
        FRZUAUDUEFGHVFCVALVKVARUFALMVBVJNVCACSDUGFGHVHVBALVHRVBRUHUIUJVCUKZVATV
        BCIULVLVBTKJTVLATKVLACSJTDCSULUNUOUPUQURUSUT $.
    $}

    ${
      oduglb.l $e |- U = ( lub ` O ) $.
      $( Greatest lower bounds in a dual order are least upper bounds in the
         original order.  (Contributed by Stefan O'Rear, 29-Jan-2015.) $)
      oduglb $p |- ( O e. V -> U = ( glb ` D ) ) $=
        ( va vc vb vd wcel cfv cv wbr wral wi vex brcnv ralbii eqid club cbs wa
        cglb cpw cple crio cmpt wreu cab cres ccnv wb imbi12i anbi12i riotabiia
        a1i mpteq2i reubii abbii reseq12i eqcomi biid id lubfval cvv wceq fvexi
        codu odubas oduleval glbfval mp1i 3eqtr4a eqtrid ) CDKZBCUALZAUDLZFVPGC
        UBLZUEZHMZIMZCUFLZNZHGMZOZWAJMZWCNZHWEOZWBWGWCNZPZJVSOZUCZIVSUGZUHZWMIV
        SUIZGUJZUKZGVTWBWAWCULZNZHWEOZWGWAWSNZHWEOZWGWBWSNZPZJVSOZUCZIVSUGZUHZX
        GIVSUIZGUJZUKZVQVRXLWRXIWOXKWQGVTXHWNXGWMIVSXGWMUMWBVSKXAWFXFWLWTWDHWEW
        BWAWCIQZHQZRSXEWKJVSXCWIXDWJXBWHHWEWGWAWCJQZXNRSWGWBWCXOXMRUNSUOZUQUPUR
        XJWPGXGWMIVSXPUSUTVAVBVPWMIHJVSVQCWCDGVSTZWCTZVQTWMVCVPVDVEAVFKZVRXLVGV
        PACVIEVHXSXGIHJVSVRAWSVFGVSACEXQVJAWCCEXRVKVRTXGVCXSVDVLVMVNVO $.
    $}

    ${
      odumeet.j $e |- .\/ = ( join ` O ) $.
      $( Meets in a dual order are joins in the original.  (Contributed by
         Stefan O'Rear, 29-Jan-2015.) $)
      odumeet $p |- .\/ = ( meet ` D ) $=
        ( va vb vc cjn cfv cmee cvv wcel wceq cv wbr coprab eqid codu c0 oduglb
        club cglb breqd oprabbidv joinfval fvexi meetfval mp1i 3eqtr4d wn fvprc
        cpr eqtrid fveq2d meet0 eqtrdi eqtr4d pm2.61i eqtri ) BCIJZAKJZECLMZVAV
        BNVCFOGOUMZHOZCUBJZPZFGHQVDVEAUCJZPZFGHQZVAVBVCVGVIFGHVCVFVHVDVEAVFCLDV
        FRZUAUDUEFGHVFVACLVKVARUFALMVBVJNVCACSDUGFGHVHAVBLVHRVBRUHUIUJVCUKZVATV
        BCIULVLVBTKJTVLATKVLACSJTDCSULUNUOUPUQURUSUT $.
    $}
  $}

  ${
    $d .<_ x y z w $.  $d B x y z w $.  $d K x y z w $.  $d S x y z w $.
    poslubmo.l $e |- .<_ = ( le ` K ) $.
    poslubmo.b $e |- B = ( Base ` K ) $.
    $( Least upper bounds in a poset are unique if they exist.  (Contributed by
       Stefan O'Rear, 31-Jan-2015.)  (Revised by NM, 16-Jun-2017.) $)
    poslubmo $p |- ( ( K e. Poset /\ S C_ B ) -> E* x e. B
  ( A. y e. S y .<_ x /\ A. z e. B ( A. y e. S y .<_ z -> x .<_ z ) ) ) $=
      ( vw wcel wa cv wbr wral wi weq breq2 ralbidv imbi12d cpo simprrl simprlr
      wss wrmo simplrr rspcdva mpd simprll simprrr simplrl wb posasymb ad4ant13
      3expb mpbi2and ex ralrimivva breq1 imbi2d anbi12d rmo4 sylibr ) FUAKZEDUD
      ZLZBMZAMZGNZBEOZVGCMZGNZBEOZVHVKGNZPZCDOZLZVGJMZGNZBEOZVMVRVKGNZPZCDOZLZL
      ZAJQZPZJDOADOVQADUEVFWGAJDDVFVHDKZVRDKZLZLZWEWFWKWELZVHVRGNZVRVHGNZWFWLVT
      WMWKVQVTWCUBWLVOVTWMPCDVRCJQZVMVTVNWMWOVLVSBEVKVRVGGRSVKVRVHGRTWKVJVPWDUC
      VFWHWIWEUFUGUHWLVJWNWKVJVPWDUIWLWBVJWNPCDVHCAQZVMVJWAWNWPVLVIBEVKVHVGGRSV
      KVHVRGRTWKVQVTWCUJVFWHWIWEUKUGUHVDWJWMWNLWFULZVEWEVDWHWIWQDFGVHVRIHUMUOUN
      UPUQURVQWDAJDWFVJVTVPWCWFVIVSBEVHVRVGGRSWFVOWBCDWFVNWAVMVHVRVKGUSUTSVAVBV
      C $.

    $( Greatest lower bounds in a poset are unique if they exist.  (Contributed
       by NM, 20-Sep-2018.) $)
    posglbmo $p |- ( ( K e. Poset /\ S C_ B ) -> E* x e. B
  ( A. y e. S x .<_ y /\ A. z e. B ( A. y e. S z .<_ y -> z .<_ x ) ) ) $=
      ( vw wcel wa cv wbr wral wi weq breq1 ralbidv imbi12d cpo simprrl simprlr
      wss wrmo simplrr rspcdva simprll simprrr simplrl wb ancom posasymb bitrid
      mpd w3a 3expb ad4ant13 mpbi2and ex ralrimivva breq2 imbi2d anbi12d sylibr
      rmo4 ) FUAKZEDUDZLZAMZBMZGNZBEOZCMZVKGNZBEOZVNVJGNZPZCDOZLZJMZVKGNZBEOZVP
      VNWAGNZPZCDOZLZLZAJQZPZJDOADOVTADUEVIWJAJDDVIVJDKZWADKZLZLZWHWIWNWHLZWAVJ
      GNZVJWAGNZWIWOWCWPWNVTWCWFUBWOVRWCWPPCDWACJQZVPWCVQWPWRVOWBBEVNWAVKGRSVNW
      AVJGRTWNVMVSWGUCVIWKWLWHUFUGUOWOVMWQWNVMVSWGUHWOWEVMWQPCDVJCAQZVPVMWDWQWS
      VOVLBEVNVJVKGRSVNVJWAGRTWNVTWCWFUIVIWKWLWHUJUGUOVGWMWPWQLZWIUKZVHWHVGWKWL
      XAWTWQWPLVGWKWLUPWIWPWQULDFGVJWAIHUMUNUQURUSUTVAVTWGAJDWIVMWCVSWFWIVLWBBE
      VJWAVKGRSWIVRWECDWIVQWDVPVJWAVNGVBVCSVDVFVE $.
  $}

  ${
    $d .<_ x y z $.  $d B x y z $.  $d K x y z $.  $d S x y z $.  $d U x y z $.
    $d T x y z $.  $d ph x y z $.
    poslubd.l $e |- .<_ = ( le ` K ) $.
    poslubd.b $e |- B = ( Base ` K ) $.
    poslubd.u $e |- U = ( lub ` K ) $.
    poslubd.k $e |- ( ph -> K e. Poset ) $.
    poslubd.s $e |- ( ph -> S C_ B ) $.
    poslubd.t $e |- ( ph -> T e. B ) $.
    poslubd.ub $e |- ( ( ph /\ x e. S ) -> x .<_ T ) $.
    poslubd.le $e |- ( ( ph /\ y e. B /\ A. x e. S x .<_ y ) -> T .<_ y ) $.
    $( Properties which determine the least upper bound in a poset.
       (Contributed by Stefan O'Rear, 31-Jan-2015.) $)
    poslubd $p |- ( ph -> ( U ` S ) = T ) $=
      ( vz wbr wral cfv cv wi wa crio cpo biid lubval wceq ralrimiva 3expia jca
      wcel wreu wrex wrmo breq2 ralbidv breq1 imbi2d anbi12d rspcev syl2anc wss
      wb poslubmo reu5 sylanbrc riota2 mpbid eqtrd ) AEGUABUBZRUBZISZBETZVLCUBZ
      ISBETZVMVPISZUCZCDTZUDZRDUEZFAWARBCDEGHIUFKJLWAUGMNUHAVLFISZBETZVQFVPISZU
      CZCDTZUDZWBFUIZAWDWGAWCBEPUJAWFCDAVPDUMVQWEQUKUJULZAFDUMZWARDUNZWHWIVEOAW
      ARDUOZWARDUPZWLAWKWHWMOWJWAWHRFDVMFUIZVOWDVTWGWOVNWCBEVMFVLIUQURWOVSWFCDW
      OVRWEVQVMFVPIUSUTURVAZVBVCAHUFUMEDVDWNMNRBCDEHIJKVFVCWARDVGVHWAWHRDFWPVIV
      CVJVK $.
  $}

  ${
    $d .<_ x y $.  $d B x y $.  $d K x y $.  $d S x y $.  $d U x y $.
    $d T x y $.  $d ph x y $.
    poslubdg.l $e |- .<_ = ( le ` K ) $.
    poslubdg.b $e |- ( ph -> B = ( Base ` K ) ) $.
    poslubdg.u $e |- ( ph -> U = ( lub ` K ) ) $.
    poslubdg.k $e |- ( ph -> K e. Poset ) $.
    poslubdg.s $e |- ( ph -> S C_ B ) $.
    poslubdg.t $e |- ( ph -> T e. B ) $.
    poslubdg.ub $e |- ( ( ph /\ x e. S ) -> x .<_ T ) $.
    poslubdg.le $e |- ( ( ph /\ y e. B /\ A. x e. S x .<_ y ) -> T .<_ y ) $.
    $( Properties which determine the least upper bound in a poset.
       (Contributed by Stefan O'Rear, 31-Jan-2015.) $)
    poslubdg $p |- ( ph -> ( U ` S ) = T ) $=
      ( cfv eqid cv club fveq1d cbs sseqtrd eleqtrd wcel eleq2d biimpar 3adant3
      wbr wral syld3an2 poslubd eqtrd ) AEGREHUARZRFAEGUOLUBABCHUCRZEFUOHIJUPSU
      OSMAEDUPNKUDAFDUPOKUEPACTZDUFZUQUPUFZBTUQIUJBEUKZFUQIUJAUSURUTAURUSADUPUQ
      KUGUHUIQULUMUN $.
  $}

  ${
    $d .<_ x y $.  $d B x y $.  $d K x y $.  $d S x y $.  $d G x y $.
    $d T x y $.  $d ph x y $.
    posglbdg.l $e |- .<_ = ( le ` K ) $.
    posglbdg.b $e |- ( ph -> B = ( Base ` K ) ) $.
    posglbdg.g $e |- ( ph -> G = ( glb ` K ) ) $.
    posglbdg.k $e |- ( ph -> K e. Poset ) $.
    posglbdg.s $e |- ( ph -> S C_ B ) $.
    posglbdg.t $e |- ( ph -> T e. B ) $.
    posglbdg.lb $e |- ( ( ph /\ x e. S ) -> T .<_ x ) $.
    posglbdg.gt $e |- ( ( ph /\ y e. B /\ A. x e. S y .<_ x ) -> y .<_ T ) $.
    $( Properties which determine the greatest lower bound in a poset.
       (Contributed by Stefan O'Rear, 31-Jan-2015.) $)
    posglbdg $p |- ( ph -> ( G ` S ) = T ) $=
      ( cfv wcel wbr codu ccnv eqid oduleval cbs odubas eqtrdi cglb club odulub
      cpo wceq syl eqtrd odupos cv wa cvv vex brcnvg sylancr adantr mpbird wral
      wb w3a brcnv ralbii syl3an3b sylancl 3ad2ant1 poslubdg ) ABCDEFGHUARZIUBZ
      VMIHVMUCZJUDADHUERZVMUERKVPVMHVOVPUCUFUGAGHUHRZVMUIRZLAHUKSZVQVRULMVMVQHU
      KVOVQUCUJUMUNAVSVMUKSMVMHVOUOUMNOABUPZESZUQVTFVNTZFVTITZPAWBWCVEZWAAVTURS
      FDSZWDBUSZOVTFURDIUTVAVBVCACUPZDSZVTWGVNTZBEVDZVFFWGVNTZWGFITZWJAWHWGVTIT
      ZBEVDWLWIWMBEVTWGIWFCUSZVGVHQVIAWHWKWLVEZWJAWEWGURSWOOWNFWGDURIUTVJVKVCVL
      $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Totally ordered sets (tosets)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c Toset $.

  $( Extend class notation with the class of all tosets. $)
  ctos $a class Toset $.

  ${
    $d f b r x y $.
    $( Define the class of totally ordered sets (tosets).  (Contributed by FL,
       17-Nov-2014.) $)
    df-toset $a |- Toset = { f e. Poset | [. ( Base ` f ) / b ].
      [. ( le ` f ) / r ]. A. x e. b A. y e. b ( x r y \/ y r x ) } $.
  $}

  ${
    $d b f r x y B $.  $d b f r K $.  $d b f r x y .<_ $.
    istos.b $e |- B = ( Base ` K ) $.
    istos.l $e |- .<_ = ( le ` K ) $.
    $( The predicate "is a toset".  (Contributed by FL, 17-Nov-2014.) $)
    istos $p |- ( K e. Toset <-> ( K e. Poset
               /\ A. x e. B A. y e. B ( x .<_ y \/ y .<_ x ) ) ) $=
      ( vr vb vf cv wbr wo wral cple cfv wsbc cbs wceq wi ctos sbceq1d sbceqbid
      cpo fveq2 fvex wb wa eqtr breq orbi12d 2ralbidv raleq raleqbi1dv sylan9bb
      ex syl expcom eqcoms ax-mp syl5com imp sbc2ie bitrdi df-toset elrab2 ) AK
      ZBKZHKZLZVHVGVILZMZBIKZNAVMNZHJKZOPZQZIVORPZQZVGVHELZVHVGELZMZBCNZACNZJDU
      DUAVODSZVSVNHDOPZQZIDRPZQWDWEVQWGIVRWHVODRUEWEVNHVPWFVODOUEUBUCVNWDIHWHWF
      DRUFDOUFVMWHSZVIWFSZVNWDUGZCWHSWIWJWKTZTZFWMWHCWIWHCSZWLWIWNUHVMCSZWJWKVM
      WHCUIEWFSWJWOWKTZTZGWQWFEWJWFESZWPWJWRUHVIESZWPVIWFEUIWSWOWKWSVNWBBVMNZAV
      MNWOWDWSVLWBABVMVMWSVJVTVKWAVGVHVIEUJVHVGVIEUJUKULWTWCAVMCWBBVMCUMUNUOUPU
      QURUSUTVAURUSUTVBVCVDABJHIVEVF $.
  $}

  ${
    $d x y B $.  $d x y K $.  $d x y .<_ $.  $d x y .< $.
    tosso.b $e |- B = ( Base ` K ) $.
    tosso.l $e |- .<_ = ( le ` K ) $.
    tosso.s $e |- .< = ( lt ` K ) $.
    $( Write the totally ordered set structure predicate in terms of the proper
       class strict order predicate.  (Contributed by Mario Carneiro,
       8-Feb-2015.) $)
    tosso $p |- ( K e. V ->
      ( K e. Toset <-> ( .< Or B /\ ( _I |` B ) C_ .<_ ) ) ) $=
      ( vx vy wcel cv wbr wo wral wa weq wb pleval2 bitri cpo wpo cid cres ctos
      wss w3o wor 3expb equcom orbi2i bitrdi 3com23 orbi12d df-3or or32 orordir
      w3a bitr4di 2ralbidva pm5.32i pospo anbi1d bitrid istos df-so anbi1i an32
      3bitr4g ) CEKZCUAKZILZJLZDMZVMVLDMZNZJAOIAOZPZABUBZUCAUDDUFZPZVLVMBMZIJQZ
      VMVLBMZUGZJAOIAOZPZCUEKABUHZVTPZVRVKWFPVJWGVKVQWFVKVPWEIJAAVKVLAKZVMAKZPP
      ZVPWBWCNZWDWCNZNZWEWLVNWMVOWNVKWJWKVNWMRABCDVLVMFGHSUIVKWJWKVOWNRZVKWKWJW
      PVKWKWJURVOWDJIQZNWNABCDVMVLFGHSWQWCWDJIUJUKULUMUIUNWEWMWDNZWOWBWCWDUOWRW
      BWDNWCNWOWBWCWDUPWBWDWCUQTTUSUTVAVJVKWAWFABCDEFGHVBVCVDIJACDFGVEWIVSWFPZV
      TPWGWHWSVTIJABVFVGVSWFVTVHTVI $.
  $}

  ${
    $d x y F $.
    $( A Toset is a Poset.  (Contributed by Thierry Arnoux, 20-Jan-2018.) $)
    tospos $p |- ( F e. Toset -> F e. Poset ) $=
      ( vx vy ctos wcel cpo cv cple cfv wbr wo cbs wral eqid istos simplbi ) AD
      EAFEBGZCGZAHIZJRQSJKCALIZMBTMBCTASTNSNOP $.
  $}

  ${
    $d x y B $.  $d x y X $.  $d y Y $.  $d x y .<_ $.
    tleile.b $e |- B = ( Base ` K ) $.
    tleile.l $e |- .<_ = ( le ` K ) $.
    $( In a Toset, any two elements are comparable.  (Contributed by Thierry
       Arnoux, 11-Feb-2018.) $)
    tleile $p |- ( ( K e. Toset /\ X e. B /\ Y e. B )
      -> ( X .<_ Y \/ Y .<_ X ) ) $=
      ( vx vy ctos wcel w3a cv wbr wo wral wceq breq1 breq2 orbi12d simp2 simp3
      cpo istos simprbi 3ad2ant1 rspc2va syl21anc ) BJKZDAKZEAKZLUJUKHMZIMZCNZU
      MULCNZOZIAPHAPZDECNZEDCNZOZUIUJUKUAUIUJUKUBUIUJUQUKUIBUCKUQHIABCFGUDUEUFU
      PUTDUMCNZUMDCNZOHIDEAAULDQUNVAUOVBULDUMCRULDUMCSTUMEQVAURVBUSUMEDCSUMEDCR
      TUGUH $.

    tltnle.s $e |- .< = ( lt ` K ) $.
    $( In a Toset, "less than" is equivalent to the negation of the converse of
       "less than or equal to", see ~ pltnle .  (Contributed by Thierry Arnoux,
       11-Feb-2018.) $)
    tltnle $p |- ( ( K e. Toset /\ X e. B /\ Y e. B )
      -> ( X .< Y <-> -. Y .<_ X ) ) $=
      ( ctos wcel w3a wbr wn wa cpo wb tospos pltval3 syl3an1 wo tleile bitr2di
      ibar pm5.61 syl bitrd ) CJKZEAKZFAKZLZEFBMZEFDMZFEDMZNZOZUOUHCPKUIUJULUPQ
      CRABCDEFGHISTUKUMUNUAZUPUOQACDEFGHUBUQUOUQUOOUPUQUOUDUMUNUEUCUFUG $.
  $}

  $c 1. $.
  $c 0. $.
  $c Lat $.

  $( Extend class notation with poset zero. $)
  cp0 $a class 0. $.

  $( Extend class notation with poset unit. $)
  cp1 $a class 1. $.

  $( Define poset zero.  (Contributed by NM, 12-Oct-2011.) $)
  df-p0 $a |- 0. = ( p e. _V |-> ( ( glb ` p ) ` ( Base ` p ) ) ) $.

  $( Define poset unit.  (Contributed by NM, 22-Oct-2011.) $)
  df-p1 $a |- 1. = ( p e. _V |-> ( ( lub ` p ) ` ( Base ` p ) ) ) $.

  ${
    $d p B $.  $d p G $.  $d p K $.
    p0val.b $e |- B = ( Base ` K ) $.
    p0val.g $e |- G = ( glb ` K ) $.
    p0val.z $e |- .0. = ( 0. ` K ) $.
    $( Value of poset zero.  (Contributed by NM, 12-Oct-2011.) $)
    p0val $p |- ( K e. V -> .0. = ( G ` B ) ) $=
      ( vp wcel cvv cfv wceq elex cp0 cv cbs cglb fveq2 eqtr4di df-p0 fvmpt syl
      fveq12d fvex eqtrid ) CDJCKJZEABLZMCDNUGECOLUHHICIPZQLZUIRLZLUHKOUICMZUJA
      UKBULUKCRLBUICRSGTULUJCQLAUICQSFTUDIUAABUEUBUFUC $.
  $}

  ${
    $d k B $.  $d k K $.  $d k U $.
    p1val.b $e |- B = ( Base ` K ) $.
    p1val.u $e |- U = ( lub ` K ) $.
    p1val.t $e |- .1. = ( 1. ` K ) $.
    $( Value of poset zero.  (Contributed by NM, 22-Oct-2011.) $)
    p1val $p |- ( K e. V -> .1. = ( U ` B ) ) $=
      ( vk wcel cvv cfv wceq elex cp1 cv cbs club fveq2 eqtr4di df-p1 fvmpt syl
      fveq12d fvex eqtrid ) DEJDKJZCABLZMDENUGCDOLUHHIDIPZQLZUIRLZLUHKOUIDMZUJA
      UKBULUKDRLBUIDRSGTULUJDQLAUIDQSFTUDIUAABUEUBUFUC $.
  $}

  ${
    p0le.b $e |- B = ( Base ` K ) $.
    p0le.g $e |- G = ( glb ` K ) $.
    p0le.l $e |- .<_ = ( le ` K ) $.
    p0le.0 $e |- .0. = ( 0. ` K ) $.
    p0le.k $e |- ( ph -> K e. V ) $.
    p0le.x $e |- ( ph -> X e. B ) $.
    p0le.d $e |- ( ph -> B e. dom G ) $.
    $( Any element is less than or equal to a poset's upper bound (if defined).
       (Contributed by NM, 22-Oct-2011.)  (Revised by NM, 13-Sep-2018.) $)
    p0le $p |- ( ph -> .0. .<_ X ) $=
      ( cfv wcel wceq p0val syl glble eqbrtrd ) AHBCPZGEADFQHUCRMBCDFHIJLSTABBC
      DEFGIKJMONUAUB $.
  $}

  ${
    ple1.b $e |- B = ( Base ` K ) $.
    ple1.u $e |- U = ( lub ` K ) $.
    ple1.l $e |- .<_ = ( le ` K ) $.
    ple1.1 $e |- .1. = ( 1. ` K ) $.
    ple1.k $e |- ( ph -> K e. V ) $.
    ple1.x $e |- ( ph -> X e. B ) $.
    ple1.d $e |- ( ph -> B e. dom U ) $.
    $( Any element is less than or equal to a poset's upper bound (if defined).
       (Contributed by NM, 22-Oct-2011.)  (Revised by NM, 13-Sep-2018.) $)
    ple1 $p |- ( ph -> X .<_ .1. ) $=
      ( cfv luble wcel wceq p1val syl breqtrrd ) AHBCPZDFABBCEFGHIKJMONQAEGRDUC
      SMBCDEGIJLTUAUB $.
  $}

  ${
    $d x y z A $.  $d x y z F $.
    $( The restriction of a Poset is a Poset.  (Contributed by Thierry Arnoux,
       20-Jan-2018.) $)
    resspos $p |- ( ( F e. Poset /\ A e. V ) -> ( F |`s A ) e. Poset ) $=
      ( vx vy vz cpo wcel wa cress cvv cv cple cfv wbr wi wral eqid ssralv breq
      co wceq w3a cbs ovexd wss cin ressbas inss2 eqsstrrdi adantl ispos adantr
      simprbi ralimdv syld sylc ressle anbi12d imbi1d imbi12d 3anbi123d ralbidv
      wb 2ralbidv syl mpbid sylanbrc ) BGHZACHZIZBAJUAZKHDLZVMVLMNZOZVMELZVNOZV
      PVMVNOZIZVMVPUBZPZVQVPFLZVNOZIZVMWBVNOZPZUCZFVLUDNZQZEWHQDWHQZVLGHVKBAJUE
      VKVMVMBMNZOZVMVPWKOZVPVMWKOZIZVTPZWMVPWBWKOZIZVMWBWKOZPZUCZFWHQZEWHQZDWHQ
      ZWJVKWHBUDNZUFZXAFXEQZEXEQZDXEQZXDVJXFVIVJWHAXEUGXEAXEVLCBVLRZXERZUHAXEUI
      UJUKVIXIVJVIBKHXIDEFXEBWKXKWKRZULUNUMXFXIXCDXEQXDXFXHXCDXEXFXHXBEXEQXCXFX
      GXBEXEXAFWHXESUOXBEWHXESUPUOXCDWHXESUPUQVKWKVNUBZXDWJVDVJXMVIABWKCVLXJXLU
      RUKXMXBWIDEWHWHXMXAWGFWHXMWLVOWPWAWTWFVMVMWKVNTXMWOVSVTXMWMVQWNVRVMVPWKVN
      TZVPVMWKVNTUSUTXMWRWDWSWEXMWMVQWQWCXNVPWBWKVNTUSVMWBWKVNTVAVBVCVEVFVGDEFW
      HVLVNWHRVNRULVH $.

    $d x y V $.
    $( The restriction of a Toset is a Toset.  (Contributed by Thierry Arnoux,
       20-Jan-2018.) $)
    resstos $p |- ( ( F e. Toset /\ A e. V ) -> ( F |`s A ) e. Toset ) $=
      ( vx vy ctos wcel cpo cv cple cfv wbr wo cbs wral eqid adantl istos breqd
      ssralv wa cress co tospos resspos sylan wss cin ressbas eqsstrrdi simprbi
      inss2 adantr ralimdv syld sylc wb ressle orbi12d 2ralbidv mpbid sylanbrc
      ) BFGZACGZUAZBAUBUCZHGZDIZEIZVFJKZLZVIVHVJLZMZEVFNKZODVNOZVFFGVCBHGZVDVGB
      UDABCUEUFVEVHVIBJKZLZVIVHVQLZMZEVNOZDVNOZVOVEVNBNKZUGZVTEWCOZDWCOZWBVDWDV
      CVDVNAWCUHWCAWCVFCBVFPZWCPZUIAWCULUJQVCWFVDVCVPWFDEWCBVQWHVQPZRUKUMWDWFWE
      DVNOWBWEDVNWCTWDWEWADVNVTEVNWCTUNUOUPVDWBVOUQVCVDVTVMDEVNVNVDVRVKVSVLVDVQ
      VJVHVIABVQCVFWGWIURZSVDVQVJVIVHWJSUSUTQVADEVNVFVJVNPVJPRVB $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Lattices
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Lattices
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Extend class notation with the class of all lattices. $)
  clat $a class Lat $.

  $( Define the class of all lattices.  A lattice is a poset in which the join
     and meet of any two elements always exists.  (Contributed by NM,
     18-Oct-2012.)  (Revised by NM, 12-Sep-2018.) $)
  df-lat $a |- Lat = { p e. Poset |
       ( dom ( join ` p ) = ( ( Base ` p ) X. ( Base ` p ) )
      /\ dom ( meet ` p ) = ( ( Base ` p ) X. ( Base ` p ) ) ) } $.

  ${
    $d l B $.  $d l .\/ $.  $d l K $.  $d l ./\ $.
    islat.b $e |- B = ( Base ` K ) $.
    islat.j $e |- .\/ = ( join ` K ) $.
    islat.m $e |- ./\ = ( meet ` K ) $.
    $( The predicate "is a lattice".  (Contributed by NM, 18-Oct-2012.)
       (Revised by NM, 12-Sep-2018.) $)
    islat $p |- ( K e. Lat <-> ( K e. Poset /\
          ( dom .\/ = ( B X. B ) /\ dom ./\ = ( B X. B ) ) ) ) $=
      ( vl cjn cfv cdm cbs cxp wceq cmee wa fveq2 eqtr4di dmeqd eqeq12d cv clat
      cpo sqxpeqd anbi12d df-lat elrab2 ) HUAZIJZKZUHLJZUKMZNZUHOJZKZULNZPBKZAA
      MZNZDKZURNZPHCUCUBUHCNZUMUSUPVAVBUJUQULURVBUIBVBUICIJBUHCIQFRSVBUKAVBUKCL
      JAUHCLQERUDZTVBUOUTULURVBUNDVBUNCOJDUHCOQGRSVCTUEHUFUG $.
  $}

  ${
    odulat.d $e |- D = ( ODual ` O ) $.
    $( Being a lattice is self-dual.  (Contributed by Stefan O'Rear,
       29-Jan-2015.) $)
    odulatb $p |- ( O e. V -> ( O e. Lat <-> D e. Lat ) ) $=
      ( wcel cpo cjn cfv cdm cbs cxp wceq cmee wa clat oduposb ancom eqid islat
      wb a1i anbi12d odubas odujoin odumeet 3bitr4g ) BCEZBFEZBGHZIBJHZUJKZLZBM
      HZIUKLZNZNAFEZUNULNZNBOEAOEUGUHUPUOUQABCDPUOUQTUGULUNQUAUBUJUIBUMUJRZUIRZ
      UMRZSUJUMAUIUJABDURUCAUMBDUTUDAUIBDUSUESUF $.

    $( Being a lattice is self-dual.  (Contributed by Stefan O'Rear,
       29-Jan-2015.) $)
    odulat $p |- ( O e. Lat -> D e. Lat ) $=
      ( clat wcel odulatb ibi ) BDEADEABDCFG $.
  $}

  ${
    latcl2.b $e |- B = ( Base ` K ) $.
    latcl2.j $e |- .\/ = ( join ` K ) $.
    latcl2.m $e |- ./\ = ( meet ` K ) $.
    latcl2.k $e |- ( ph -> K e. Lat ) $.
    latcl2.x $e |- ( ph -> X e. B ) $.
    latcl2.y $e |- ( ph -> Y e. B ) $.
    $( The join and meet of any two elements exist.  (Contributed by NM,
       14-Sep-2018.) $)
    latcl2 $p |- ( ph ->
        ( <. X , Y >. e. dom .\/ /\ <. X , Y >. e. dom ./\ ) ) $=
      ( cop cdm wcel cxp wceq wa eleqtrrd opelxpd cpo islat simprld simprrd jca
      clat sylib ) AFGNZCOZPUIEOZPAUIBBQZUJAFGBBLMUAZADUBPZUJULRZUKULRZADUGPUNU
      OUPSSKBCDEHIJUCUHZUDTAUIULUKUMAUNUOUPUQUETUF $.
  $}

  ${
    latlem.b $e |- B = ( Base ` K ) $.
    latlem.j $e |- .\/ = ( join ` K ) $.
    latlem.m $e |- ./\ = ( meet ` K ) $.
    $( Lemma for lattice properties.  (Contributed by NM, 14-Sep-2011.) $)
    latlem $p |- ( ( K e. Lat /\ X e. B /\ Y e. B ) ->
           ( ( X .\/ Y ) e. B /\ ( X ./\ Y ) e. B ) ) $=
      ( clat wcel w3a co simp1 cdm wceq wa sylbi 3ad2ant1 eleqtrrd simp2 simprl
      simp3 cop cxp opelxpi 3adant1 cpo islat joincl simprr meetcl jca ) CJKZEA
      KZFAKZLZEFBMAKEFDMAKUQABCJEFGHUNUOUPNZUNUOUPUAZUNUOUPUCZUQEFUDZAAUEZBOZUO
      UPVAVBKUNEFAAUFUGZUNUOVCVBPZUPUNCUHKZVEDOZVBPZQQZVEABCDGHIUIZVFVEVHUBRSTU
      JUQACDJEFGIURUSUTUQVAVBVGVDUNUOVHUPUNVIVHVJVFVEVHUKRSTULUM $.
  $}

  $( A lattice is a poset.  (Contributed by NM, 17-Sep-2011.) $)
  latpos $p |- ( K e. Lat -> K e. Poset ) $=
    ( clat wcel cpo cjn cfv cdm cbs cxp wceq cmee wa eqid islat simplbi ) ABCAD
    CAEFZGAHFZQIZJAKFZGRJLQPASQMPMSMNO $.

  ${
    latjcl.b $e |- B = ( Base ` K ) $.
    latjcl.j $e |- .\/ = ( join ` K ) $.
    $( Closure of join operation in a lattice.  ( ~ chjcom analog.)
       (Contributed by NM, 14-Sep-2011.) $)
    latjcl $p |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X .\/ Y ) e. B ) $=
      ( clat wcel w3a co cmee cfv eqid latlem simpld ) CHIDAIEAIJDEBKAIDECLMZKA
      IABCQDEFGQNOP $.
  $}

  ${
    latmcl.b $e |- B = ( Base ` K ) $.
    latmcl.m $e |- ./\ = ( meet ` K ) $.
    $( Closure of meet operation in a lattice.  ( ~ incom analog.)
       (Contributed by NM, 14-Sep-2011.) $)
    latmcl $p |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X ./\ Y ) e. B ) $=
      ( clat wcel w3a cjn cfv co eqid latlem simprd ) BHIDAIEAIJDEBKLZMAIDECMAI
      AQBCDEFQNGOP $.
  $}

  ${
    latref.b $e |- B = ( Base ` K ) $.
    latref.l $e |- .<_ = ( le ` K ) $.
    $( A lattice ordering is reflexive.  ( ~ ssid analog.)  (Contributed by NM,
       8-Oct-2011.) $)
    latref $p |- ( ( K e. Lat /\ X e. B ) -> X .<_ X ) $=
      ( clat wcel cpo wbr latpos posref sylan ) BGHBIHDAHDDCJBKABCDEFLM $.

    $( A lattice ordering is asymmetric.  ( ~ eqss analog.)  (Contributed by
       NM, 22-Oct-2011.) $)
    latasymb $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
                -> ( ( X .<_ Y /\ Y .<_ X ) <-> X = Y ) ) $=
      ( clat wcel cpo wbr wa wceq wb latpos posasymb syl3an1 ) BHIBJIDAIEAIDECK
      EDCKLDEMNBOABCDEFGPQ $.

    $( A lattice ordering is asymmetric.  ( ~ eqss analog.)  (Contributed by
       NM, 8-Oct-2011.) $)
    latasym $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
                -> ( ( X .<_ Y /\ Y .<_ X ) -> X = Y ) ) $=
      ( clat wcel w3a wbr wa wceq latasymb biimpd ) BHIDAIEAIJDECKEDCKLDEMABCDE
      FGNO $.

    $( A lattice ordering is transitive.  ( ~ sstr analog.)  (Contributed by
       NM, 17-Nov-2011.) $)
    lattr $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) )
                -> ( ( X .<_ Y /\ Y .<_ Z ) -> X .<_ Z ) ) $=
      ( clat wcel cpo w3a wbr wa wi latpos postr sylan ) BIJBKJDAJEAJFAJLDECMEF
      CMNDFCMOBPABCDEFGHQR $.
  $}

  ${
    latasymd.b $e |- B = ( Base ` K ) $.
    latasymd.l $e |- .<_ = ( le ` K ) $.
    latasymd.3 $e |- ( ph -> K e. Lat ) $.
    latasymd.4 $e |- ( ph -> X e. B ) $.
    latasymd.5 $e |- ( ph -> Y e. B ) $.
    latasymd.6 $e |- ( ph -> X .<_ Y ) $.
    latasymd.7 $e |- ( ph -> Y .<_ X ) $.
    $( Deduce equality from lattice ordering.  ( ~ eqssd analog.)  (Contributed
       by NM, 18-Nov-2011.) $)
    latasymd $p |- ( ph -> X = Y ) $=
      ( wbr wceq clat wcel wa wb latasymb syl3anc mpbi2and ) AEFDNZFEDNZEFOZLMA
      CPQEBQFBQUCUDRUESIJKBCDEFGHTUAUB $.
  $}

  ${
    lattrd.b $e |- B = ( Base ` K ) $.
    lattrd.l $e |- .<_ = ( le ` K ) $.
    lattrd.1 $e |- ( ph -> K e. Lat ) $.
    lattrd.2 $e |- ( ph -> X e. B ) $.
    lattrd.3 $e |- ( ph -> Y e. B ) $.
    lattrd.4 $e |- ( ph -> Z e. B ) $.
    lattrd.5 $e |- ( ph -> X .<_ Y ) $.
    lattrd.6 $e |- ( ph -> Y .<_ Z ) $.
    $( A lattice ordering is transitive.  Deduction version of ~ lattr .
       (Contributed by NM, 3-Sep-2012.) $)
    lattrd $p |- ( ph -> X .<_ Z ) $=
      ( wbr clat wcel wa wi lattr syl13anc mp2and ) AEFDPZFGDPZEGDPZNOACQREBRFB
      RGBRUDUESUFTJKLMBCDEFGHIUAUBUC $.
  $}

  ${
    latjcom.b $e |- B = ( Base ` K ) $.
    latjcom.j $e |- .\/ = ( join ` K ) $.
    $( The join of a lattice commutes.  ( ~ chjcom analog.)  (Contributed by
       NM, 16-Sep-2011.) $)
    latjcom $p |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X .\/ Y ) =
              ( Y .\/ X ) ) $=
      ( clat wcel w3a cop cdm wa co wceq cxp opelxpi 3adant1 cpo eleqtrrd islat
      cmee cfv eqid simprl sylbi 3ad2ant1 ancoms latpos joincom syl3anl1 mpdan
      jca ) CHIZDAIZEAIZJZDEKZBLZIZEDKZUSIZMZDEBNEDBNOZUQUTVBUQURAAPZUSUOUPURVE
      IUNDEAAQRUNUOUSVEOZUPUNCSIZVFCUBUCZLVEOZMMVFABCVHFGVHUDUAVGVFVIUEUFUGZTUQ
      VAVEUSUOUPVAVEIZUNUPUOVKEDAAQUHRVJTUMUNVGUOUPVCVDCUIABCDEFGUJUKUL $.
  $}

  ${
    latlej.b $e |- B = ( Base ` K ) $.
    latlej.l $e |- .<_ = ( le ` K ) $.
    latlej.j $e |- .\/ = ( join ` K ) $.
    $( A join's first argument is less than or equal to the join.  ( ~ chub1
       analog.)  (Contributed by NM, 17-Sep-2011.) $)
    latlej1 $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
            -> X .<_ ( X .\/ Y ) ) $=
      ( clat wcel w3a simp1 simp2 simp3 cop cdm cmee cfv eqid latcl2 lejoin1
      simpld ) CJKZEAKZFAKZLZABCDJEFGHIUDUEUFMZUDUEUFNZUDUEUFOZUGEFPZBQKUKCRSZQ
      KUGABCULEFGIULTUHUIUJUAUCUB $.

    $( A join's second argument is less than or equal to the join.  ( ~ chub2
       analog.)  (Contributed by NM, 17-Sep-2011.) $)
    latlej2 $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
            -> Y .<_ ( X .\/ Y ) ) $=
      ( clat wcel w3a simp1 simp2 simp3 cop cdm cmee cfv eqid latcl2 lejoin2
      simpld ) CJKZEAKZFAKZLZABCDJEFGHIUDUEUFMZUDUEUFNZUDUEUFOZUGEFPZBQKUKCRSZQ
      KUGABCULEFGIULTUHUIUJUAUCUB $.

    $( A join is less than or equal to a third value iff each argument is less
       than or equal to the third value.  ( ~ chlub analog.)  (Contributed by
       NM, 17-Sep-2011.) $)
    latjle12 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) )
                      -> ( ( X .<_ Z /\ Y .<_ Z ) <-> ( X .\/ Y ) .<_ Z ) ) $=
      ( clat wcel w3a wa cpo latpos adantr simpr1 simpr2 cdm cop cmee cfv simpl
      simpr3 eqid latcl2 simpld joinle ) CKLZEALZFALZGALZMZNZABCDEFGHIJUJCOLUNC
      PQUJUKULUMRZUJUKULUMSZUJUKULUMUEUOEFUAZBTLURCUBUCZTLUOABCUSEFHJUSUFUJUNUD
      UPUQUGUHUI $.

    $( "Less than or equal to" in terms of join.  ( ~ chlejb1 analog.)
       (Contributed by NM, 21-Oct-2011.) $)
    latleeqj1 $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
            -> ( X .<_ Y <-> ( X .\/ Y ) = Y ) ) $=
      ( clat wcel w3a wbr co wa wceq latref biantrud wb bitrd simp1 simp2 simp3
      3adant2 latjle12 syl13anc latlej2 latpos 3ad2ant1 latjcl posasymb syl3anc
      cpo ) CJKZEAKZFAKZLZEFDMZEFBNZFDMZFUSDMZOZUSFPZUQURUTVBUQURURFFDMZOZUTUQV
      DURUNUPVDUOACDFGHQUDRUQUNUOUPUPVEUTSUNUOUPUAUNUOUPUBUNUOUPUCZVFABCDEFFGHI
      UEUFTUQVAUTABCDEFGHIUGRTUQCUMKZUSAKUPVBVCSUNUOVGUPCUHUIABCEFGIUJVFACDUSFG
      HUKULT $.

    $( "Less than or equal to" in terms of join.  ( ~ chlejb2 analog.)
       (Contributed by NM, 14-Nov-2011.) $)
    latleeqj2 $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
            -> ( X .<_ Y <-> ( Y .\/ X ) = Y ) ) $=
      ( clat wcel w3a wbr co wceq latleeqj1 latjcom eqeq1d bitrd ) CJKEAKFAKLZE
      FDMEFBNZFOFEBNZFOABCDEFGHIPTUAUBFABCEFGIQRS $.

    $( Add join to both sides of a lattice ordering.  ( ~ chlej1i analog.)
       (Contributed by NM, 8-Nov-2011.) $)
    latjlej1 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) )
       -> ( X .<_ Y -> ( X .\/ Z ) .<_ ( Y .\/ Z ) ) ) $=
      ( clat wcel w3a wa wbr co latlej1 3adant3r1 wi simpl simpr1 simpr2 latjcl
      lattr syl13anc mpan2d latlej2 jctird simpr3 3jca latjle12 syldan sylibd
      wb ) CKLZEALZFALZGALZMZNZEFDOZEFGBPZDOZGVBDOZNZEGBPVBDOZUTVAVCVDUTVAFVBDO
      ZVCUOUQURVGUPABCDFGHIJQRUTUOUPUQVBALZVAVGNVCSUOUSTUOUPUQURUAZUOUPUQURUBUO
      UQURVHUPABCFGHJUCRZACDEFVBHIUDUEUFUOUQURVDUPABCDFGHIJUGRUHUOUSUPURVHMVEVF
      UNUTUPURVHVIUOUPUQURUIVJUJABCDEGVBHIJUKULUM $.

    $( Add join to both sides of a lattice ordering.  ( ~ chlej2i analog.)
       (Contributed by NM, 8-Nov-2011.) $)
    latjlej2 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) )
       -> ( X .<_ Y -> ( Z .\/ X ) .<_ ( Z .\/ Y ) ) ) $=
      ( clat wcel w3a wa wbr co latjlej1 wceq latjcom 3adant3r2 breq12d sylibd
      3adant3r1 ) CKLZEALZFALZGALZMNZEFDOEGBPZFGBPZDOGEBPZGFBPZDOABCDEFGHIJQUHU
      IUKUJULDUDUEUGUIUKRUFABCEGHJSTUDUFUGUJULRUEABCFGHJSUCUAUB $.

    $( Add join to both sides of a lattice ordering.  ( ~ chlej12i analog.)
       (Contributed by NM, 8-Nov-2011.) $)
    latjlej12 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B )
          /\ ( Z e. B /\ W e. B ) ) -> ( ( X .<_ Y /\ Z .<_ W )
             -> ( X .\/ Z ) .<_ ( Y .\/ W ) ) ) $=
      ( clat wcel wa wbr co wi syl13anc latjcl syl3anc w3a simp2l simp2r simp3l
      simp1 latjlej1 simp3r latjlej2 lattr syl2and ) CLMZFAMZGAMZNZHAMZEAMZNZUA
      ZFGDOZFHBPZGHBPZDOZHEDOZVAGEBPZDOZUTVDDOZURUKULUMUOUSVBQUKUNUQUEZUKULUMUQ
      UBZUKULUMUQUCZUKUNUOUPUDZABCDFGHIJKUFRURUKUOUPUMVCVEQVGVJUKUNUOUPUGZVIABC
      DHEGIJKUHRURUKUTAMZVAAMZVDAMZVBVENVFQVGURUKULUOVLVGVHVJABCFHIKSTURUKUMUOV
      MVGVIVJABCGHIKSTURUKUMUPVNVGVIVKABCGEIKSTACDUTVAVDIJUIRUJ $.

    $( An idiom to express that a lattice element differs from two others.
       (Contributed by NM, 28-May-2012.) $)
    latnlej $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B )
         /\ -. X .<_ ( Y .\/ Z ) ) -> ( X =/= Y /\ X =/= Z ) ) $=
      ( clat wcel wbr wne wa wceq 3adant3r1 breq1 syl5ibrcom necon3bd w3a co wn
      latlej1 latlej2 jcad 3impia ) CKLZEALZFALZGALZUAZEFGBUBZDMZUCZEFNZEGNZOUH
      ULOZUOUPUQURUNEFURUNEFPFUMDMZUHUJUKUSUIABCDFGHIJUDQEFUMDRSTURUNEGURUNEGPG
      UMDMZUHUJUKUTUIABCDFGHIJUEQEGUMDRSTUFUG $.

    $( An idiom to express that a lattice element differs from two others.
       (Contributed by NM, 19-Jul-2012.) $)
    latnlej1l $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B )
         /\ -. X .<_ ( Y .\/ Z ) ) -> X =/= Y ) $=
      ( clat wcel w3a co wbr wn wne latnlej simpld ) CKLEALFALGALMEFGBNDOPMEFQE
      GQABCDEFGHIJRS $.

    $( An idiom to express that a lattice element differs from two others.
       (Contributed by NM, 19-Jul-2012.) $)
    latnlej1r $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B )
         /\ -. X .<_ ( Y .\/ Z ) ) -> X =/= Z ) $=
      ( clat wcel w3a co wbr wn wne latnlej simprd ) CKLEALFALGALMEFGBNDOPMEFQE
      GQABCDEFGHIJRS $.

    $( An idiom to express that a lattice element differs from two others.
       (Contributed by NM, 10-Jul-2012.) $)
    latnlej2 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B )
         /\ -. X .<_ ( Y .\/ Z ) ) -> ( -. X .<_ Y /\ -. X .<_ Z ) ) $=
      ( wcel wbr wn wa 3adant3r1 wi lattr syl13anc mpan2d con3d clat co latlej1
      w3a simpl simpr1 simpr2 latjcl latlej2 simpr3 jcad 3impia ) CUAKZEAKZFAKZ
      GAKZUDZEFGBUBZDLZMZEFDLZMZEGDLZMZNUMUQNZUTVBVDVEVAUSVEVAFURDLZUSUMUOUPVFU
      NABCDFGHIJUCOVEUMUNUOURAKZVAVFNUSPUMUQUEZUMUNUOUPUFZUMUNUOUPUGUMUOUPVGUNA
      BCFGHJUHOZACDEFURHIQRSTVEVCUSVEVCGURDLZUSUMUOUPVKUNABCDFGHIJUIOVEUMUNUPVG
      VCVKNUSPVHVIUMUNUOUPUJVJACDEGURHIQRSTUKUL $.

    $( An idiom to express that a lattice element differs from two others.
       (Contributed by NM, 19-Jul-2012.) $)
    latnlej2l $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B )
         /\ -. X .<_ ( Y .\/ Z ) ) -> -. X .<_ Y ) $=
      ( clat wcel w3a co wbr wn latnlej2 simpld ) CKLEALFALGALMEFGBNDOPMEFDOPEG
      DOPABCDEFGHIJQR $.

    $( An idiom to express that a lattice element differs from two others.
       (Contributed by NM, 19-Jul-2012.) $)
    latnlej2r $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B )
         /\ -. X .<_ ( Y .\/ Z ) ) -> -. X .<_ Z ) $=
      ( clat wcel w3a co wbr wn latnlej2 simprd ) CKLEALFALGALMEFGBNDOPMEFDOPEG
      DOPABCDEFGHIJQR $.
  $}

  ${
    latjidm.b $e |- B = ( Base ` K ) $.
    latjidm.j $e |- .\/ = ( join ` K ) $.
    $( Lattice join is idempotent.  Analogue of ~ unidm .  (Contributed by NM,
       8-Oct-2011.) $)
    latjidm $p |- ( ( K e. Lat /\ X e. B ) -> ( X .\/ X ) = X ) $=
      ( clat wcel wa cple cfv co eqid simpl latjcl 3anidm23 simpr wbr latref wb
      latjle12 syl13anc mpbi2and latlej1 latasymd ) CGHZDAHZIZACCJKZDDBLZDEUIMZ
      UFUGNZUFUGUJAHABCDDEFOPUFUGQZUHDDUIRZUNUJDUIRZACUIDEUKSZUPUHUFUGUGUGUNUNI
      UOTULUMUMUMABCUIDDDEUKFUAUBUCUFUGDUJUIRABCUIDDEUKFUDPUE $.
  $}

  ${
    latmcom.b $e |- B = ( Base ` K ) $.
    latmcom.m $e |- ./\ = ( meet ` K ) $.
    $( The join of a lattice commutes.  (Contributed by NM, 6-Nov-2011.) $)
    latmcom $p |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X ./\ Y ) =
              ( Y ./\ X ) ) $=
      ( clat wcel w3a cop cdm wa co wceq cxp opelxpi 3adant1 cpo eleqtrrd islat
      cjn cfv eqid simprr sylbi 3ad2ant1 ancoms latpos meetcom syl3anl1 mpdan
      jca ) BHIZDAIZEAIZJZDEKZCLZIZEDKZUSIZMZDECNEDCNOZUQUTVBUQURAAPZUSUOUPURVE
      IUNDEAAQRUNUOUSVEOZUPUNBSIZBUBUCZLVEOZVFMMVFAVHBCFVHUDGUAVGVIVFUEUFUGZTUQ
      VAVEUSUOUPVAVEIZUNUPUOVKEDAAQUHRVJTUMUNVGUOUPVCVDBUIABCDEFGUJUKUL $.
  $}

  ${
    latmle.b $e |- B = ( Base ` K ) $.
    latmle.l $e |- .<_ = ( le ` K ) $.
    latmle.m $e |- ./\ = ( meet ` K ) $.
    $( A meet is less than or equal to its first argument.  (Contributed by NM,
       21-Oct-2011.) $)
    latmle1 $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
            -> ( X ./\ Y ) .<_ X ) $=
      ( clat wcel w3a simp1 simp2 simp3 cop cjn cfv cdm eqid latcl2 lemeet1
      simprd ) BJKZEAKZFAKZLZABCDJEFGHIUDUEUFMZUDUEUFNZUDUEUFOZUGEFPZBQRZSKUKDS
      KUGAULBDEFGULTIUHUIUJUAUCUB $.

    $( A meet is less than or equal to its second argument.  (Contributed by
       NM, 21-Oct-2011.) $)
    latmle2 $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
            -> ( X ./\ Y ) .<_ Y ) $=
      ( clat wcel w3a simp1 simp2 simp3 cop cjn cfv cdm eqid latcl2 lemeet2
      simprd ) BJKZEAKZFAKZLZABCDJEFGHIUDUEUFMZUDUEUFNZUDUEUFOZUGEFPZBQRZSKUKDS
      KUGAULBDEFGULTIUHUIUJUAUCUB $.

    $( An element is less than or equal to a meet iff the element is less than
       or equal to each argument of the meet.  (Contributed by NM,
       21-Oct-2011.) $)
    latlem12 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) )
                      -> ( ( X .<_ Y /\ X .<_ Z ) <-> X .<_ ( Y ./\ Z ) ) ) $=
      ( clat wcel w3a wa cpo latpos adantr simpr2 simpr3 cdm simpr1 cop cjn cfv
      eqid simpl latcl2 simprd meetle ) BKLZEALZFALZGALZMZNZABCDFGEHIJUJBOLUNBP
      QUJUKULUMRZUJUKULUMSZUJUKULUMUAUOFGUBZBUCUDZTLURDTLUOAUSBDFGHUSUEJUJUNUFU
      PUQUGUHUI $.

    $( "Less than or equal to" in terms of meet.  (Contributed by NM,
       7-Nov-2011.) $)
    latleeqm1 $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
            -> ( X .<_ Y <-> ( X ./\ Y ) = X ) ) $=
      ( clat wcel w3a wbr co wa wceq latref biantrurd wb bitrd 3adant3 latlem12
      simp1 simp2 syl13anc latmle1 cpo latpos 3ad2ant1 latmcl posasymb syl3anc
      simp3 ) BJKZEAKZFAKZLZEFCMZEFDNZECMZEUSCMZOZUSEPZUQURVAVBUQUREECMZUROZVAU
      QVDURUNUOVDUPABCEGHQUARUQUNUOUOUPVEVASUNUOUPUCUNUOUPUDZVFUNUOUPUMABCDEEFG
      HIUBUETUQUTVAABCDEFGHIUFRTUQBUGKZUSAKUOVBVCSUNUOVGUPBUHUIABDEFGIUJVFABCUS
      EGHUKULT $.

    $( "Less than or equal to" in terms of meet.  (Contributed by NM,
       7-Nov-2011.) $)
    latleeqm2 $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
            -> ( X .<_ Y <-> ( Y ./\ X ) = X ) ) $=
      ( clat wcel w3a wbr co wceq latleeqm1 latmcom eqeq1d bitrd ) BJKEAKFAKLZE
      FCMEFDNZEOFEDNZEOABCDEFGHIPTUAUBEABDEFGIQRS $.

    $( Add meet to both sides of a lattice ordering.  (Contributed by NM,
       10-Nov-2011.) $)
    latmlem1 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) )
       -> ( X .<_ Y -> ( X ./\ Z ) .<_ ( Y ./\ Z ) ) ) $=
      ( clat wcel w3a wa wbr co latmle1 3adant3r2 wi simpl latmcl simpr1 simpr2
      lattr syl13anc mpand latmle2 jctird wb simpr3 3jca latlem12 syldan sylibd
      ) BKLZEALZFALZGALZMZNZEFCOZEGDPZFCOZVBGCOZNZVBFGDPCOZUTVAVCVDUTVBECOZVAVC
      UOUPURVGUQABCDEGHIJQRUTUOVBALZUPUQVGVANVCSUOUSTUOUPURVHUQABDEGHJUARZUOUPU
      QURUBUOUPUQURUCZABCVBEFHIUDUEUFUOUPURVDUQABCDEGHIJUGRUHUOUSVHUQURMVEVFUIU
      TVHUQURVIVJUOUPUQURUJUKABCDVBFGHIJULUMUN $.

    $( Add meet to both sides of a lattice ordering.  ( ~ sslin analog.)
       (Contributed by NM, 10-Nov-2011.) $)
    latmlem2 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) )
       -> ( X .<_ Y -> ( Z ./\ X ) .<_ ( Z ./\ Y ) ) ) $=
      ( clat wcel w3a wa wbr co latmlem1 wceq latmcom 3adant3r2 breq12d sylibd
      3adant3r1 ) BKLZEALZFALZGALZMNZEFCOEGDPZFGDPZCOGEDPZGFDPZCOABCDEFGHIJQUHU
      IUKUJULCUDUEUGUIUKRUFABDEGHJSTUDUFUGUJULRUEABDFGHJSUCUAUB $.

    $( Add join to both sides of a lattice ordering.  ( ~ ss2in analog.)
       (Contributed by NM, 10-Nov-2011.) $)
    latmlem12 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B )
          /\ ( Z e. B /\ W e. B ) ) -> ( ( X .<_ Y /\ Z .<_ W )
             -> ( X ./\ Z ) .<_ ( Y ./\ W ) ) ) $=
      ( clat wcel wa wbr co wi syl13anc latmcl syl3anc w3a simp2l simp2r simp3l
      simp1 latmlem1 simp3r latmlem2 lattr syl2and ) BLMZFAMZGAMZNZHAMZEAMZNZUA
      ZFGCOZFHDPZGHDPZCOZHECOZVAGEDPZCOZUTVDCOZURUKULUMUOUSVBQUKUNUQUEZUKULUMUQ
      UBZUKULUMUQUCZUKUNUOUPUDZABCDFGHIJKUFRURUKUOUPUMVCVEQVGVJUKUNUOUPUGZVIABC
      DHEGIJKUHRURUKUTAMZVAAMZVDAMZVBVENVFQVGURUKULUOVLVGVHVJABDFHIKSTURUKUMUOV
      MVGVIVJABDGHIKSTURUKUMUPVNVGVIVKABDGEIKSTABCUTVAVDIJUIRUJ $.
  $}

  ${
    latnlemlt.b $e |- B = ( Base ` K ) $.
    latnlemlt.l $e |- .<_ = ( le ` K ) $.
    latnlemlt.s $e |- .< = ( lt ` K ) $.
    latnlemlt.m $e |- ./\ = ( meet ` K ) $.
    $( Negation of "less than or equal to" expressed in terms of meet and
       less-than.  ( ~ nssinpss analog.)  (Contributed by NM, 5-Feb-2012.) $)
    latnlemlt $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
            -> ( -. X .<_ Y <-> ( X ./\ Y ) .< X ) ) $=
      ( clat wcel w3a co wne wbr wa wn latmle1 biantrurd latleeqm1 simp1 latmcl
      necon3bbid wb simp2 pltval syl3anc 3bitr4d ) CLMZFAMZGAMZNZFGEOZFPZUOFDQZ
      UPRZFGDQZSUOFBQZUNUQUPACDEFGHIKTUAUNUSUOFACDEFGHIKUBUEUNUKUOAMULUTURUFUKU
      LUMUCACEFGHKUDUKULUMUGLAABCDUOFIJUHUIUJ $.
  $}

  ${
    latnle.b $e |- B = ( Base ` K ) $.
    latnle.l $e |- .<_ = ( le ` K ) $.
    latnle.s $e |- .< = ( lt ` K ) $.
    latnle.j $e |- .\/ = ( join ` K ) $.
    $( Equivalent expressions for "not less than" in a lattice.  ( ~ chnle
       analog.)  (Contributed by NM, 16-Nov-2011.) $)
    latnle $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
       -> ( -. Y .<_ X <-> X .< ( X .\/ Y ) ) ) $=
      ( clat wcel w3a co wne wbr wa wceq wb wn biantrurd latleeqj1 3com23 eqcom
      latlej1 bitrdi latjcom eqeq2d bitr4d necon3bbid latjcl syld3an3 3bitr4d
      pltval ) DLMZFAMZGAMZNZFFGCOZPZFUTEQZVARZGFEQZUAFUTBQZUSVBVAACDEFGHIKUFUB
      USVDFUTUSVDFGFCOZSZFUTSUSVDVFFSZVGUPURUQVDVHTACDEGFHIKUCUDVFFUEUGUSUTVFFA
      CDFGHKUHUIUJUKUPUQURUTAMVEVCTACDFGHKULLAABDEFUTIJUOUMUN $.
  $}

  ${
    latmidm.b $e |- B = ( Base ` K ) $.
    latmidm.m $e |- ./\ = ( meet ` K ) $.
    $( Lattice meet is idempotent.  Analogue of ~ inidm .  (Contributed by NM,
       8-Nov-2011.) $)
    latmidm $p |- ( ( K e. Lat /\ X e. B ) -> ( X ./\ X ) = X ) $=
      ( clat wcel wa cple cfv co simpl latmcl 3anidm23 simpr wbr latmle1 latref
      eqid wb latlem12 syl13anc mpbi2and latasymd ) BGHZDAHZIZABBJKZDDCLZDEUITZ
      UFUGMZUFUGUJAHABCDDEFNOUFUGPZUFUGUJDUIQABUICDDEUKFROUHDDUIQZUNDUJUIQZABUI
      DEUKSZUPUHUFUGUGUGUNUNIUOUAULUMUMUMABUICDDDEUKFUBUCUDUE $.
  $}

  ${
    latabs1.b $e |- B = ( Base ` K ) $.
    latabs1.j $e |- .\/ = ( join ` K ) $.
    latabs1.m $e |- ./\ = ( meet ` K ) $.
    $( Lattice absorption law.  From definition of lattice in [Kalmbach] p. 14.
       ( ~ chabs1 analog.)  (Contributed by NM, 8-Nov-2011.) $)
    latabs1 $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
              -> ( X .\/ ( X ./\ Y ) ) = X ) $=
      ( clat wcel w3a co cple cfv wbr wceq eqid latmle1 wb latmcl 3com23 mpbid
      latleeqj2 syld3an3 ) CJKZEAKZFAKZLEFDMZECNOZPZEUIBMEQZACUJDEFGUJRZISUFUGU
      HUIAKZUKULTZACDEFGIUAUFUNUGUOABCUJUIEGUMHUDUBUEUC $.

    $( Lattice absorption law.  From definition of lattice in [Kalmbach] p. 14.
       ( ~ chabs2 analog.)  (Contributed by NM, 8-Nov-2011.) $)
    latabs2 $p |- ( ( K e. Lat /\ X e. B /\ Y e. B )
              -> ( X ./\ ( X .\/ Y ) ) = X ) $=
      ( clat wcel w3a co cple cfv wbr wceq eqid latlej1 wb latleeqm1 syld3an3
      latjcl mpbid ) CJKZEAKZFAKZLEEFBMZCNOZPZEUHDMEQZABCUIEFGUIRZHSUEUFUGUHAKU
      JUKTABCEFGHUCACUIDEUHGULIUAUBUD $.
  $}

  ${
    latledi.b $e |- B = ( Base ` K ) $.
    latledi.l $e |- .<_ = ( le ` K ) $.
    latledi.j $e |- .\/ = ( join ` K ) $.
    latledi.m $e |- ./\ = ( meet ` K ) $.
    $( An ortholattice is distributive in one ordering direction.  ( ~ ledi
       analog.)  (Contributed by NM, 7-Nov-2011.) $)
    latledi $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
                 ( ( X ./\ Y ) .\/ ( X ./\ Z ) ) .<_ ( X ./\ ( Y .\/ Z ) ) ) $=
      ( wcel w3a wa co wbr latmle1 3adant3r3 3adant3r2 latmcl latjle12 mpbi2and
      clat wb simpr1 syldan latmle2 wi simpr2 simpr3 latjlej12 syl122anc mp2and
      3jca simpl latjcl syl3anc 3adant3r1 latlem12 syl13anc ) CUDMZFAMZGAMZHAMZ
      NZOZFGEPZFHEPZBPZFDQZVJGHBPZDQZVJFVLEPDQZVGVHFDQZVIFDQZVKVBVCVDVOVEACDEFG
      IJLRSVBVCVEVPVDACDEFHIJLRTVBVFVHAMZVIAMZVCNVOVPOVKUEVGVQVRVCVBVCVDVQVEACE
      FGILUASZVBVCVEVRVDACEFHILUATZVBVCVDVEUFZUOABCDVHVIFIJKUBUGUCVGVHGDQZVIHDQ
      ZVMVBVCVDWBVEACDEFGIJLUHSVBVCVEWCVDACDEFHIJLUHTVGVBVQVDVRVEWBWCOVMUIVBVFU
      PZVSVBVCVDVEUJVTVBVCVDVEUKABCDHVHGVIIJKULUMUNVGVBVJAMZVCVLAMZVKVMOVNUEWDV
      GVBVQVRWEWDVSVTABCVHVIIKUQURWAVBVDVEWFVCABCGHIKUQUSACDEVJFVLIJLUTVAUC $.

    $( Ordering of a meet and join with a common variable.  (Contributed by NM,
       4-Oct-2012.) $)
    latmlej11 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
      ( X ./\ Y ) .<_ ( X .\/ Z ) ) $=
      ( clat wcel w3a wa co 3adant3r3 3adant3r2 wbr simpl latmcl simpr1 latmle1
      latjcl latlej1 lattrd ) CMNZFANZGANZHANZOZPACDFGEQZFFHBQZIJUHULUAUHUIUJUM
      ANUKACEFGILUBRUHUIUJUKUCUHUIUKUNANUJABCFHIKUESUHUIUJUMFDTUKACDEFGIJLUDRUH
      UIUKFUNDTUJABCDFHIJKUFSUG $.

    $( Ordering of a meet and join with a common variable.  (Contributed by NM,
       4-Oct-2012.) $)
    latmlej12 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
      ( X ./\ Y ) .<_ ( Z .\/ X ) ) $=
      ( clat wcel w3a wa co latmlej11 wceq latjcom 3adant3r2 breqtrd ) CMNZFANZ
      GANZHANZOPFGEQFHBQZHFBQZDABCDEFGHIJKLRUCUDUFUGUHSUEABCFHIKTUAUB $.

    $( Ordering of a meet and join with a common variable.  (Contributed by NM,
       4-Oct-2012.) $)
    latmlej21 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
      ( Y ./\ X ) .<_ ( X .\/ Z ) ) $=
      ( clat wcel w3a wa co wceq latmcom 3adant3r3 latmlej11 eqbrtrrd ) CMNZFAN
      ZGANZHANZOPFGEQZGFEQZFHBQDUCUDUEUGUHRUFACEFGILSTABCDEFGHIJKLUAUB $.

    $( Ordering of a meet and join with a common variable.  (Contributed by NM,
       4-Oct-2012.) $)
    latmlej22 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
      ( Y ./\ X ) .<_ ( Z .\/ X ) ) $=
      ( clat wcel w3a wa co wceq latmcom 3adant3r3 latmlej12 eqbrtrrd ) CMNZFAN
      ZGANZHANZOPFGEQZGFEQZHFBQDUCUDUEUGUHRUFACEFGILSTABCDEFGHIJKLUAUB $.
  $}

  ${
    lubsn.b $e |- B = ( Base ` K ) $.
    lubsn.u $e |- U = ( lub ` K ) $.
    $( The least upper bound of a singleton.  ( ~ chsupsn analog.)
       (Contributed by NM, 20-Oct-2011.) $)
    lubsn $p |- ( ( K e. Lat /\ X e. B ) -> ( U ` { X } ) = X ) $=
      ( clat wcel wa csn cfv cjn co cpr dfsn2 fveq2i eqid simpl simpr joinval
      eqtr4id latjidm eqtrd ) CGHZDAHZIZDJZBKZDDCLKZMZDUFUHDDNZBKUJUGUKBDOPUFBU
      ICGADDAFUIQZUDUERUDUESZUMTUAAUICDEULUBUC $.
  $}

  ${
    latjass.b $e |- B = ( Base ` K ) $.
    latjass.j $e |- .\/ = ( join ` K ) $.
    $( Lattice join is associative.  Lemma 2.2 in [MegPav2002] p. 362.
       ( ~ chjass analog.)  (Contributed by NM, 17-Sep-2011.) $)
    latjass $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
             ( ( X .\/ Y ) .\/ Z ) = ( X .\/ ( Y .\/ Z ) ) ) $=
      ( wcel wa co latjcl syl3anc wbr latlej1 latlej2 lattrd latjle12 syl13anc
      wb clat cple eqid simpl 3adant3r3 simpr3 simpr1 3adant3r1 simpr2 mpbi2and
      w3a cfv latasymd ) CUAIZDAIZEAIZFAIZUKZJZACCUBULZDEBKZFBKZDEFBKZBKZGUTUCZ
      UNURUDZUSUNVAAIZUQVBAIZVFUNUOUPVGUQABCDEGHLUEZUNUOUPUQUFZABCVAFGHLMZUSUNU
      OVCAIZVDAIZVFUNUOUPUQUGZUNUPUQVLUOABCEFGHLUHZABCDVCGHLMZUSVAVDUTNZFVDUTNZ
      VBVDUTNZUSDVDUTNZEVDUTNZVQUSUNUOVLVTVFVNVOABCUTDVCGVEHOMUSACUTEVCVDGVEVFU
      NUOUPUQUIZVOVPUNUPUQEVCUTNUOABCUTEFGVEHOUHUSUNUOVLVCVDUTNVFVNVOABCUTDVCGV
      EHPMZQUSUNUOUPVMVTWAJVQTVFVNWBVPABCUTDEVDGVEHRSUJUSACUTFVCVDGVEVFVJVOVPUN
      UPUQFVCUTNUOABCUTEFGVEHPUHWCQUSUNVGUQVMVQVRJVSTVFVIVJVPABCUTVAFVDGVEHRSUJ
      USDVBUTNZVCVBUTNZVDVBUTNZUSACUTDVAVBGVEVFVNVIVKUNUOUPDVAUTNUQABCUTDEGVEHO
      UEUSUNVGUQVAVBUTNVFVIVJABCUTVAFGVEHOMZQUSEVBUTNZFVBUTNZWEUSACUTEVAVBGVEVF
      WBVIVKUNUOUPEVAUTNUQABCUTDEGVEHPUEWGQUSUNVGUQWIVFVIVJABCUTVAFGVEHPMUSUNUP
      UQVHWHWIJWETVFWBVJVKABCUTEFVBGVEHRSUJUSUNUOVLVHWDWEJWFTVFVNVOVKABCUTDVCVB
      GVEHRSUJUM $.

    $( Swap 1st and 2nd members of lattice join.  ( ~ chj12 analog.)
       (Contributed by NM, 4-Jun-2012.) $)
    latj12 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
             ( X .\/ ( Y .\/ Z ) ) = ( Y .\/ ( X .\/ Z ) ) ) $=
      ( clat wcel w3a wa co wceq latjcom 3adant3r3 oveq1d latjass simpl simpr2
      simpr1 simpr3 syl13anc 3eqtr3d ) CIJZDAJZEAJZFAJZKZLZDEBMZFBMEDBMZFBMZDEF
      BMBMEDFBMBMZUJUKULFBUEUFUGUKULNUHABCDEGHOPQABCDEFGHRUJUEUGUFUHUMUNNUEUISU
      EUFUGUHTUEUFUGUHUAUEUFUGUHUBABCEDFGHRUCUD $.

    $( Swap 2nd and 3rd members of lattice join.  Lemma 2.2 in [MegPav2002]
       p. 362.  (Contributed by NM, 2-Dec-2011.) $)
    latj32 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
             ( ( X .\/ Y ) .\/ Z ) = ( ( X .\/ Z ) .\/ Y ) ) $=
      ( clat wcel w3a wa co wceq latjcom 3adant3r1 oveq2d latjass simpr1 simpr3
      simpr2 3jca syldan 3eqtr4d ) CIJZDAJZEAJZFAJZKZLZDEFBMZBMDFEBMZBMZDEBMFBM
      DFBMEBMZUJUKULDBUEUGUHUKULNUFABCEFGHOPQABCDEFGHRUEUIUFUHUGKUNUMNUJUFUHUGU
      EUFUGUHSUEUFUGUHTUEUFUGUHUAUBABCDFEGHRUCUD $.

    $( Swap 1st and 3rd members of lattice join.  (Contributed by NM,
       4-Jun-2012.) $)
    latj13 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
             ( X .\/ ( Y .\/ Z ) ) = ( Z .\/ ( Y .\/ X ) ) ) $=
      ( clat wcel w3a wa co wceq simpl simpr2 simpr3 latjcl latjcom syl3anc
      simpr1 latj32 syl13anc 3adant3r1 3eqtr4d ) CIJZDAJZEAJZFAJZKZLZEFBMZDBMZE
      DBMZFBMZDULBMZFUNBMZUKUFUHUIUGUMUONUFUJOZUFUGUHUIPZUFUGUHUIQZUFUGUHUIUAZA
      BCEFDGHUBUCUKUFUGULAJZUPUMNURVAUFUHUIVBUGABCEFGHRUDABCDULGHSTUKUFUIUNAJZU
      QUONURUTUKUFUHUGVCURUSVAABCEDGHRTABCFUNGHSTUE $.

    $( Swap 2nd and 3rd members of lattice join.  Lemma 2.2 in [MegPav2002]
       p. 362.  (Contributed by NM, 23-Jun-2012.) $)
    latj31 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
             ( ( X .\/ Y ) .\/ Z ) = ( ( Z .\/ Y ) .\/ X ) ) $=
      ( clat wcel w3a wa co wceq simpl simpr3 simpr1 latjcl latjcom syl3anc
      simpr2 latj12 syl13anc 3adant3r3 3eqtr4d ) CIJZDAJZEAJZFAJZKZLZFDEBMZBMZD
      FEBMZBMZULFBMZUNDBMZUKUFUIUGUHUMUONUFUJOZUFUGUHUIPZUFUGUHUIQZUFUGUHUIUAZA
      BCFDEGHUBUCUKUFULAJZUIUPUMNURUFUGUHVBUIABCDEGHRUDUSABCULFGHSTUKUFUNAJZUGU
      QUONURUKUFUIUHVCURUSVAABCFEGHRTUTABCUNDGHSTUE $.

    $( Rotate lattice join of 3 classes.  (Contributed by NM, 23-Jul-2012.) $)
    latjrot $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
             ( ( X .\/ Y ) .\/ Z ) = ( ( Z .\/ X ) .\/ Y ) ) $=
      ( clat wcel w3a wa co latj31 wceq simpl simpr3 simpr2 simpr1 latj32 eqtrd
      syl13anc ) CIJZDAJZEAJZFAJZKZLZDEBMFBMFEBMDBMZFDBMEBMZABCDEFGHNUHUCUFUEUD
      UIUJOUCUGPUCUDUEUFQUCUDUEUFRUCUDUEUFSABCFEDGHTUBUA $.

    $( Rearrangement of lattice join of 4 classes.  ( ~ chj4 analog.)
       (Contributed by NM, 14-Jun-2012.) $)
    latj4 $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B )
               /\ ( Z e. B /\ W e. B ) )
      -> ( ( X .\/ Y ) .\/ ( Z .\/ W ) ) = ( ( X .\/ Z ) .\/ ( Y .\/ W ) ) ) $=
      ( clat wcel wa w3a co wceq simp1 syl13anc latjcl syl3anc latjass 3eqtr4d
      simp2r simp3l simp3r latj12 oveq2d simp2l ) CJKZEAKZFAKZLZGAKZDAKZLZMZEFG
      DBNZBNZBNZEGFDBNZBNZBNZEFBNUPBNZEGBNUSBNZUOUQUTEBUOUHUJULUMUQUTOUHUKUNPZU
      HUIUJUNUBZUHUKULUMUCZUHUKULUMUDZABCFGDHIUEQUFUOUHUIUJUPAKZVBUROVDUHUIUJUN
      UGZVEUOUHULUMVHVDVFVGABCGDHIRSABCEFUPHITQUOUHUIULUSAKZVCVAOVDVIVFUOUHUJUM
      VJVDVEVGABCFDHIRSABCEGUSHITQUA $.

    $( Rotate lattice join of 4 classes.  (Contributed by NM, 11-Jul-2012.) $)
    latj4rot $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B )
               /\ ( Z e. B /\ W e. B ) )
      -> ( ( X .\/ Y ) .\/ ( Z .\/ W ) ) = ( ( W .\/ X ) .\/ ( Y .\/ Z ) ) ) $=
      ( clat wcel wa w3a co wceq simp1 simp3l simp3r latjcom syl3anc oveq2d jca
      latj4 syld3an3 simp2l oveq1d 3eqtrd ) CJKZEAKZFAKZLZGAKZDAKZLZMZEFBNZGDBN
      ZBNUPDGBNZBNZEDBNZFGBNZBNZDEBNZVABNUOUQURUPBUOUHULUMUQUROUHUKUNPZUHUKULUM
      QZUHUKULUMRZABCGDHISTUAUHUKUNUMULLUSVBOUOUMULVFVEUBABCGEFDHIUCUDUOUTVCVAB
      UOUHUIUMUTVCOVDUHUIUJUNUEVFABCEDHISTUFUG $.

    $( Lattice join distributes over itself.  (Contributed by NM,
       30-Jul-2012.) $)
    latjjdi $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
             ( X .\/ ( Y .\/ Z ) ) = ( ( X .\/ Y ) .\/ ( X .\/ Z ) ) ) $=
      ( clat wcel w3a wa co wceq simpr1 latjidm syldan oveq1d simpl simpr2
      simpr3 latj4 syl122anc eqtr3d ) CIJZDAJZEAJZFAJZKZLZDDBMZEFBMZBMZDULBMDEB
      MDFBMBMZUJUKDULBUEUIUFUKDNUEUFUGUHOZABCDGHPQRUJUEUFUFUGUHUMUNNUEUISUOUOUE
      UFUGUHTUEUFUGUHUAABCFDDEGHUBUCUD $.

    $( Lattice join distributes over itself.  (Contributed by NM,
       2-Aug-2012.) $)
    latjjdir $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
             ( ( X .\/ Y ) .\/ Z ) = ( ( X .\/ Z ) .\/ ( Y .\/ Z ) ) ) $=
      ( clat wcel w3a wa co wceq latjidm 3ad2antr3 oveq2d simpl simpr1 simpr2
      simpr3 latj4 syl122anc eqtr3d ) CIJZDAJZEAJZFAJZKZLZDEBMZFFBMZBMZUKFBMDFB
      MEFBMBMZUJULFUKBUEUFUHULFNUGABCFGHOPQUJUEUFUGUHUHUMUNNUEUIRUEUFUGUHSUEUFU
      GUHTUEUFUGUHUAZUOABCFDEFGHUBUCUD $.
  $}

  ${
    modle.b $e |- B = ( Base ` K ) $.
    modle.l $e |- .<_ = ( le ` K ) $.
    modle.j $e |- .\/ = ( join ` K ) $.
    modle.m $e |- ./\ = ( meet ` K ) $.
    $( The weak direction of the modular law (e.g., ~ pmod1i , ~ atmod1i1 )
       that holds in any lattice.  (Contributed by NM, 11-May-2012.) $)
    mod1ile $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
        ( X .<_ Z -> ( X .\/ ( Y ./\ Z ) ) .<_ ( ( X .\/ Y ) ./\ Z ) ) ) $=
      ( wcel wa wbr co syl3anc wb syl13anc mpbi2and clat simpll simplr1 simplr2
      w3a latlej1 latjcl simplr3 latlem12 latmlej12 latmle2 latmcl latjle12 ex
      simpr ) CUAMZFAMZGAMZHAMZUEZNZFHDOZFGHEPZBPFGBPZHEPZDOZVAVBNZFVEDOZVCVEDO
      ZVFVGFVDDOZVBVHVGUPUQURVJUPUTVBUBZUQURUSUPVBUCZUQURUSUPVBUDZABCDFGIJKUFQV
      AVBUOVGUPUQVDAMZUSVJVBNVHRVKVLVGUPUQURVNVKVLVMABCFGIKUGQZUQURUSUPVBUHZACD
      EFVDHIJLUISTVGVCVDDOZVCHDOZVIVGUPURUSUQVQVKVMVPVLABCDEGHFIJKLUJSVGUPURUSV
      RVKVMVPACDEGHIJLUKQVGUPVCAMZVNUSVQVRNVIRVKVGUPURUSVSVKVMVPACEGHILULQZVOVP
      ACDEVCVDHIJLUISTVGUPUQVSVEAMZVHVINVFRVKVLVTVGUPVNUSWAVKVOVPACEVDHILULQABC
      DFVCVEIJKUMSTUN $.

    $( The weak direction of the modular law (e.g., ~ pmod2iN ) that holds in
       any lattice.  (Contributed by NM, 11-May-2012.) $)
    mod2ile $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
        ( Z .<_ X -> ( ( X ./\ Y ) .\/ Z ) .<_ ( X ./\ ( Y .\/ Z ) ) ) ) $=
      ( wcel w3a wa wbr co wceq latmcom syl3anc clat simpll simplr3 simplr2 jca
      simplr1 3jca simpr mod1ile sylc oveq1d latmcl latjcom eqtrd oveq2d latjcl
      3brtr4d ex ) CUAMZFAMZGAMZHAMZNZOZHFDPZFGEQZHBQZFGHBQZEQZDPVDVEOZHGFEQZBQ
      ZHGBQZFEQZVGVIDVJUSVBVAUTNZOVEVLVNDPVJUSVOUSVCVEUBZVJVBVAUTUTVAVBUSVEUCZU
      TVAVBUSVEUDZUTVAVBUSVEUFZUGUEVDVEUHABCDEHGFIJKLUIUJVJVGVKHBQZVLVJVFVKHBVJ
      USUTVAVFVKRVPVSVRACEFGILSTUKVJUSVKAMZVBVTVLRVPVJUSVAUTWAVPVRVSACEGFILULTV
      QABCVKHIKUMTUNVJVIFVMEQZVNVJVHVMFEVJUSVAVBVHVMRVPVRVQABCGHIKUMTUOVJUSUTVM
      AMZWBVNRVPVSVJUSVBVAWCVPVQVRABCHGIKUPTACEFVMILSTUNUQUR $.
  $}

  ${
    latmass.b $e |- B = ( Base ` K ) $.
    latmass.m $e |- ./\ = ( meet ` K ) $.
    $( Lattice meet is associative.  (Contributed by Stefan O'Rear,
       30-Jan-2015.) $)
    latmass $p |- ( ( K e. Lat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
        ( ( X ./\ Y ) ./\ Z ) = ( X ./\ ( Y ./\ Z ) ) ) $=
      ( clat wcel codu cfv w3a co wceq eqid odulat odubas odujoin latjass sylan
      ) BIJBKLZIJDAJEAJFAJMDECNFCNDEFCNCNOUBBUBPZQACUBDEFAUBBUCGRUBCBUCHSTUA $.
  $}

  ${
    $d u v w x y z K $.  $d u v w x y z B $.  $d u v w x y z .\/ $.
    $d u v w x y z ./\ $.
    latdisd.b $e |- B = ( Base ` K ) $.
    latdisd.j $e |- .\/ = ( join ` K ) $.
    latdisd.m $e |- ./\ = ( meet ` K ) $.
    $( Lemma for ~ latdisd .  (Contributed by Stefan O'Rear, 30-Jan-2015.) $)
    latdisdlem $p |- ( K e. Lat ->
        ( A. u e. B A. v e. B A. w e. B ( u .\/ ( v ./\ w ) ) =
          ( ( u .\/ v ) ./\ ( u .\/ w ) ) ->
        A. x e. B A. y e. B A. z e. B ( x ./\ ( y .\/ z ) ) =
          ( ( x ./\ y ) .\/ ( x ./\ z ) ) ) ) $=
      ( wcel cv co wceq oveq1 oveq2d syl3anc clat wa wi latmcl 3adant3r3 simpr1
      wral w3a simpr3 oveq12d eqeq12d weq oveq2 oveq1d rspc3v imp simpl latjcom
      latabs1 eqtrd adantr simpr2 latjcl latmass syl13anc latabs2 3eqtrrd an32s
      eqtr3d ralrimivvva ex ) IUANZFOZEOZDOZJPZHPZVMVNHPZVMVOHPZJPZQZDGUGEGUGFG
      UGZAOZBOZCOZHPZJPZWCWDJPZWCWEJPZHPZQZCGUGBGUGAGUGVLWBUBWKABCGGGVLWCGNZWDG
      NZWEGNZUHZWBWKVLWOUBZWBUBZWJWHWCHPZWHWEHPZJPZWCWEWHHPZJPZWGWPWBWJWTQZWPWH
      GNZWLWNWBXCUCVLWLWMXDWNGIJWCWDKMUDUEZVLWLWMWNUFZVLWLWMWNUIZWAXCWHVPHPZWHV
      NHPZWHVOHPZJPZQWHWCVOJPZHPZWRXJJPZQFEDWHWCWEGGGVMWHQZVQXHVTXKVMWHVPHRXOVR
      XIVSXJJVMWHVNHRVMWHVOHRUJUKEAULZXHXMXKXNXPVPXLWHHVNWCVOJRZSXPXIWRXJJVNWCW
      HHUMUNUKDCULZXMWJXNWTXRXLWIWHHVOWEWCJUMSXRXJWSWRJVOWEWHHUMSUKUOTUPWPWTXBQ
      WBWPWRWCWSXAJWPWRWCWHHPZWCWPVLXDWLWRXSQVLWOUQZXEXFGHIWHWCKLURTVLWLWMXSWCQ
      WNGHIJWCWDKLMUSUEUTWPVLXDWNWSXAQXTXEXGGHIWHWEKLURTUJVAWQXBWCWEWCHPZWEWDHP
      ZJPZJPZWGWQXAYCWCJWPWBXAYCQZWPWNWLWMWBYEUCXGXFVLWLWMWNVBZWAYEWEVPHPZWEVNH
      PZWEVOHPZJPZQWEXLHPZYAYIJPZQFEDWEWCWDGGGFCULZVQYGVTYJVMWEVPHRYMVRYHVSYIJV
      MWEVNHRVMWEVOHRUJUKXPYGYKYJYLXPVPXLWEHXQSXPYHYAYIJVNWCWEHUMUNUKDBULZYKXAY
      LYCYNXLWHWEHVOWDWCJUMSYNYIYBYAJVOWDWEHUMSUKUOTUPSWPYDWGQWBWPWCYAJPZYBJPZY
      DWGWPVLWLYAGNZYBGNZYPYDQXTXFWPVLWNWLYQXTXGXFGHIWEWCKLVCTWPVLWNWMYRXTXGYFG
      HIWEWDKLVCTGIJWCYAYBKMVDVEWPYOWCYBWFJWPYOWCWCWEHPZJPZWCWPYAYSWCJWPVLWNWLY
      AYSQXTXGXFGHIWEWCKLURTSWPVLWLWNYTWCQXTXFXGGHIJWCWEKLMVFTUTWPVLWNWMYBWFQXT
      XGYFGHIWEWDKLURTUJVIVAUTVGVHVJVK $.

    $( In a lattice, joins distribute over meets if and only if meets
       distribute over joins; the distributive property is self-dual.
       (Contributed by Stefan O'Rear, 29-Jan-2015.) $)
    latdisd $p |- ( K e. Lat ->
        ( A. x e. B A. y e. B A. z e. B ( x .\/ ( y ./\ z ) ) =
          ( ( x .\/ y ) ./\ ( x .\/ z ) ) <->
        A. x e. B A. y e. B A. z e. B ( x ./\ ( y .\/ z ) ) =
          ( ( x ./\ y ) .\/ ( x ./\ z ) ) ) ) $=
      ( vu vv vw cv co wceq wral weq oveq1 eqeq12d clat wcel latdisdlem codu wi
      cfv eqid odulat odubas odujoin odumeet impbid oveq12d oveq2d oveq2 oveq1d
      syl cbvral3vw bitrdi ) FUAUBZANZBNZCNZGOEOVAVBEOVAVCEOGOPCDQBDQADQZKNZLNZ
      MNZEOZGOZVEVFGOZVEVGGOZEOZPZMDQLDQKDQZVAVBVCEOZGOZVAVBGOZVAVCGOZEOZPZCDQB
      DQADQUTVDVNKLMCBADEFGHIJUCUTFUDUFZUAUBVNVDUEWAFWAUGZUHABCMLKDGWAEDWAFWBHU
      IWAGFWBJUJWAEFWBIUKUCUQULVMVTVAVHGOZVAVFGOZVAVGGOZEOZPVAVBVGEOZGOZVQWEEOZ
      PKLMABCDDDKARZVIWCVLWFVEVAVHGSWJVJWDVKWEEVEVAVFGSVEVAVGGSUMTLBRZWCWHWFWIW
      KVHWGVAGVFVBVGESUNWKWDVQWEEVFVBVAGUOUPTMCRZWHVPWIVSWLWGVOVAGVGVCVBEUOUNWL
      WEVRVQEVGVCVAGUOUNTURUS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Complete lattices
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c CLat $.

  $( Extend class notation with complete lattices. $)
  ccla $a class CLat $.

  $( Define the class of all complete lattices, where every subset of the base
     set has an LUB and a GLB. (Contributed by NM, 18-Oct-2012.)  (Revised by
     NM, 12-Sep-2018.) $)
  df-clat $a |- CLat = { p e. Poset | ( dom ( lub ` p ) = ~P ( Base ` p )
             /\ dom ( glb ` p ) = ~P ( Base ` p ) ) } $.

  ${
    $d l B $.  $d l G $.  $d l K $.  $d l U $.
    isclat.b $e |- B = ( Base ` K ) $.
    isclat.u $e |- U = ( lub ` K ) $.
    isclat.g $e |- G = ( glb ` K ) $.
    $( The predicate "is a complete lattice".  (Contributed by NM,
       18-Oct-2012.)  (Revised by NM, 12-Sep-2018.) $)
    isclat $p |- ( K e. CLat
             <-> ( K e. Poset /\ ( dom U = ~P B /\ dom G = ~P B ) ) ) $=
      ( vl club cfv cdm cbs cpw wceq cglb wa fveq2 eqtr4di dmeqd eqeq12d cv cpo
      ccla pweqd anbi12d df-clat elrab2 ) HUAZIJZKZUHLJZMZNZUHOJZKZULNZPBKZAMZN
      ZCKZURNZPHDUBUCUHDNZUMUSUPVAVBUJUQULURVBUIBVBUIDIJBUHDIQFRSVBUKAVBUKDLJAU
      HDLQERUDZTVBUOUTULURVBUNCVBUNDOJCUHDOQGRSVCTUEHUFUG $.
  $}

  $( A complete lattice is a poset.  (Contributed by NM, 8-Sep-2018.) $)
  clatpos $p |- ( K e. CLat -> K e. Poset ) $=
    ( ccla wcel cpo club cfv cdm cbs cpw wceq cglb wa eqid isclat simplbi ) ABC
    ADCAEFZGAHFZIZJAKFZGRJLQPSAQMPMSMNO $.

  ${
    clatlem.b $e |- B = ( Base ` K ) $.
    clatlem.u $e |- U = ( lub ` K ) $.
    clatlem.g $e |- G = ( glb ` K ) $.
    $( Lemma for properties of a complete lattice.  (Contributed by NM,
       14-Sep-2011.) $)
    clatlem $p |- ( ( K e. CLat /\ S C_ B ) ->
           ( ( U ` S ) e. B /\ ( G ` S ) e. B ) ) $=
      ( ccla wcel wss wa cfv simpl cpw cdm cbs fvexi wceq eleqtrrd elpw2 isclat
      bilanri cpo birani simprld lubcl simprrd glbcl jca ) EIJZBAKZLZBCMAJBDMAJ
      UMABCEIFGUKULNZUMBAOZCPZBUOJULUKBAAEQFRUAUCZUMEUDJZUPUOSZDPZUOSZUKURUSVAL
      LULACDEFGHUBUEZUFTUGUMABDEIFHUNUMBUOUTUQUMURUSVAVBUHTUIUJ $.
  $}

  ${
    clatlubcl.b $e |- B = ( Base ` K ) $.
    clatlubcl.u $e |- U = ( lub ` K ) $.
    $( Any subset of the base set has an LUB in a complete lattice.
       (Contributed by NM, 14-Sep-2011.) $)
    clatlubcl $p |- ( ( K e. CLat /\ S C_ B ) -> ( U ` S ) e. B ) $=
      ( ccla wcel wss wa cfv cglb eqid clatlem simpld ) DGHBAIJBCKAHBDLKZKAHABC
      PDEFPMNO $.
    $( Any subset of the base set has an LUB in a complete lattice.
       (Contributed by NM, 13-Sep-2018.) $)
    clatlubcl2 $p |- ( ( K e. CLat /\ S C_ B ) -> S e. dom U ) $=
      ( ccla wcel wss wa cpw cdm cbs fvexi elpw2 bilanri wceq cpo cglb cfv eqid
      isclat simprl sylbi adantr eleqtrrd ) DGHZBAIZJBAKZCLZBUIHUHUGBAADMENOPUG
      UJUIQZUHUGDRHZUKDSTZLUIQZJJUKACUMDEFUMUAUBULUKUNUCUDUEUF $.
  $}

  ${
    clatglbcl.b $e |- B = ( Base ` K ) $.
    clatglbcl.g $e |- G = ( glb ` K ) $.
    $( Any subset of the base set has a GLB in a complete lattice.
       (Contributed by NM, 14-Sep-2011.) $)
    clatglbcl $p |- ( ( K e. CLat /\ S C_ B ) -> ( G ` S ) e. B ) $=
      ( ccla wcel wss wa club cfv eqid clatlem simprd ) DGHBAIJBDKLZLAHBCLAHABP
      CDEPMFNO $.
    $( Any subset of the base set has a GLB in a complete lattice.
       (Contributed by NM, 13-Sep-2018.) $)
    clatglbcl2 $p |- ( ( K e. CLat /\ S C_ B ) -> S e. dom G ) $=
      ( ccla wcel wss wa cpw cdm cbs fvexi elpw2 bilanri wceq cpo club cfv eqid
      isclat simprr sylbi adantr eleqtrrd ) DGHZBAIZJBAKZCLZBUIHUHUGBAADMENOPUG
      UJUIQZUHUGDRHZDSTZLUIQZUKJJUKAUMCDEUMUAFUBULUNUKUCUDUEUF $.
  $}

  ${
    oduclatb.d $e |- D = ( ODual ` O ) $.
    $( Being a complete lattice is self-dual.  (Contributed by Stefan O'Rear,
       29-Jan-2015.) $)
    oduclatb $p |- ( O e. CLat <-> D e. CLat ) $=
      ( ccla wcel cvv c0 club cfv eqid codu cpo cdm wceq cglb wa eqeq1d anbi12d
      dmeqd isclat elex wn noel wss ssid base0 clatlubcl mpan2 mto fvprc eqtrid
      eleq1d mtbiri con4i cbs oduposb ancom odulub oduglb bitrid odubas 3bitr4g
      cpw pm5.21nii ) BDEZBFEZADEZBDUAVFVGVFUBZVGGDEZVIGGHIZIZGEZVKUCVIGGUDVLGU
      EGGVJGUFVJJUGUHUIVHAGDVHABKIGCBKUJUKULUMUNVFBLEZBHIZMZBUOIZVCZNZBOIZMZVQN
      ZPZPALEZAHIZMZVQNZAOIZMZVQNZPZPVEVGVFVMWCWBWJABFCUPWBWAVRPVFWJVRWAUQVFWAW
      FVRWIVFVTWEVQVFVSWDAVSBFCVSJZURSQVFVOWHVQVFVNWGAVNBFCVNJZUSSQRUTRVPVNVSBV
      PJZWLWKTVPWDWGAVPABCWMVAWDJWGJTVBVD $.
  $}

  ${
    $d x y K $.
    $( A complete lattice is a lattice.  (Contributed by NM, 18-Sep-2011.)
       TODO: use ~ eqrelrdv2 to shorten proof and eliminate ~ joindmss and
       ~ meetdmss ? $)
    clatl $p |- ( K e. CLat -> K e. Lat ) $=
      ( vx vy cpo wcel cfv cdm wceq wa eqid simpl a1i cv wi vex eleq2 imbitrrid
      adantl cvv sylibrd club cbs cpw cglb cjn cxp cmee ccla clat joindmss wrel
      relxp cop cpr opelxp prss sylbb prex elpw sylibr joindef relssdv eqssd ex
      wss meetdmss meetdef anim12d imdistani isclat islat 3imtr4i ) ADEZAUAFZGZ
      AUBFZUCZHZAUDFZGZVQHZIZIVMAUEFZGZVPVPUFZHZAUGFZGZWEHZIZIAUHEAUIEVMWBWJVMV
      RWFWAWIVMVRWFVMVRIZWDWEWKVPWCADVPJZWCJZVMVRKZUJWKBCWEWDWEUKZWKVPVPULZLWKB
      MZCMZUMZWEEZWQWRUNZVOEZWSWDEVRWTXBNVMWTXBVRXAVQEZWTXAVPVEZXCWTWQVPEWRVPEI
      XDWQWRVPVPUOWQWRVPBOZCOZUPUQXAVPWQWRURUSUTZVOVQXAPQRWKVNWCADSWQWRSVNJZWMW
      NWQSEZWKXELWRSEZWKXFLVATVBVCVDVMWAWIVMWAIZWHWEXKVPAWGDWLWGJZVMWAKZVFXKBCW
      EWHWOXKWPLXKWTXAVTEZWSWHEWAWTXNNVMWTXNWAXCXGVTVQXAPQRXKVSAWGDSWQWRSVSJZXL
      XMXIXKXELXJXKXFLVGTVBVCVDVHVIVPVNVSAWLXHXOVJVPWCAWGWLWMXLVKVL $.
  $}

  ${
    $d h .<_ $.  $d h x B $.  $d h x y H $.  $d h x y K $.  $d x y ph $.
    $d h x y S $.
    isglbd.b $e |- B = ( Base ` K ) $.
    isglbd.l $e |- .<_ = ( le ` K ) $.
    isglbd.g $e |- G = ( glb ` K ) $.
    isglbd.1 $e |- ( ( ph /\ y e. S ) -> H .<_ y ) $.
    isglbd.2 $e |- ( ( ph /\ x e. B /\ A. y e. S x .<_ y ) -> x .<_ H ) $.
    isglbd.3 $e |- ( ph -> K e. CLat ) $.
    isglbd.4 $e |- ( ph -> S C_ B ) $.
    isglbd.5 $e |- ( ph -> H e. B ) $.
    $( Properties that determine the greatest lower bound of a complete
       lattice.  (Contributed by Mario Carneiro, 19-Mar-2014.) $)
    isglbd $p |- ( ph -> ( G ` S ) = H ) $=
      ( vh wbr wral cfv cv wi wa crio ccla biid glbval wceq ralrimiva wcel 3exp
      ralrimiv wreu wss cdm clatglbcl2 syl2anc glbeu breq1 ralbidv breq2 imbi2d
      wb anbi12d riota2 mpbi2and eqtrd ) AEFUARUBZCUBZISZCETZBUBZVJISCETZVMVIIS
      ZUCZBDTZUDZRDUEZGAVRRCBDEFHIUFJKLVRUGZOPUHAGVJISZCETZVNVMGISZUCZBDTZVSGUI
      ZAWACEMUJAWDBDAVMDUKVNWCNULUMAGDUKVRRDUNWBWEUDZWFVDQAVRRCBDEFHIUFJKLVTOAH
      UFUKEDUOEFUPUKOPDEFHJLUQURUSVRWGRDGVIGUIZVLWBVQWEWHVKWACEVIGVJIUTVAWHVPWD
      BDWHVOWCVNVIGVMIVBVCVAVEVFURVGVH $.
  $}

  ${
    $d z B $.  $d y z K $.  $d y z S $.  $d y z U $.  $d y z .<_ $.
    lublem.b $e |- B = ( Base ` K ) $.
    lublem.l $e |- .<_ = ( le ` K ) $.
    lublem.u $e |- U = ( lub ` K ) $.
    $( Lemma for the least upper bound properties in a complete lattice.
       (Contributed by NM, 19-Oct-2011.) $)
    lublem $p |- ( ( K e. CLat /\ S C_ B ) -> ( A. y e. S y .<_ ( U ` S )
                  /\ A. z e. B ( A. y e. S y .<_ z -> ( U ` S ) .<_ z ) ) ) $=
      ( ccla wcel wss wa simpl clatlubcl2 lubprop ) FKLZDCMZNABCDEFGKHIJRSOCDEF
      HJPQ $.

    $d y z X $.
    $( The LUB of a complete lattice subset is an upper bound.  (Contributed by
       NM, 19-Oct-2011.) $)
    lubub $p |- ( ( K e. CLat /\ S C_ B /\ X e. S ) -> X .<_ ( U ` S ) ) $=
      ( vy vz ccla wcel wss cv cfv wbr wral wa wi lublem simpld rspccva stoic3
      breq1 ) DLMZBANZJOZBCPZEQZJBRZFBMFUIEQZUFUGSUKUHKOZEQJBRUIUMEQTKARJKABCDE
      GHIUAUBUJULJFBUHFUIEUEUCUD $.

    $( The LUB of a complete lattice subset is the least bound.  (Contributed
       by NM, 19-Oct-2011.) $)
    lubl $p |- ( ( K e. CLat /\ S C_ B /\ X e. B )
          -> ( A. y e. S y .<_ X -> ( U ` S ) .<_ X ) ) $=
      ( vz ccla wcel wss cv wbr wral cfv wi breq2 wa lublem simprd wceq ralbidv
      imbi12d rspccva stoic3 ) ELMZCBNZAOZKOZFPZACQZCDRZULFPZSZKBQZGBMUKGFPZACQ
      ZUOGFPZSZUIUJUAUKUOFPACQURAKBCDEFHIJUBUCUQVBKGBULGUDZUNUTUPVAVCUMUSACULGU
      KFTUEULGUOFTUFUGUH $.

    $d y B $.  $d y T $.
    $( Subset law for least upper bounds.  ( ~ chsupss analog.)  (Contributed
       by NM, 20-Oct-2011.) $)
    lubss $p |- ( ( K e. CLat /\ T C_ B /\ S C_ T )
          -> ( U ` S ) .<_ ( U ` T ) ) $=
      ( vy ccla wcel wss w3a cfv cv wbr wral simp1 sstr2 impcom 3adant1 3adant3
      clatlubcl 3jca simpl1 simpl2 ssel2 3ad2antl3 lubub syl3anc ralrimiva lubl
      wa sylc ) EKLZCAMZBCMZNZUPBAMZCDOZALZNJPZVAFQZJBRBDOVAFQUSUPUTVBUPUQURSUQ
      URUTUPURUQUTBCATUAUBUPUQVBURACDEGIUDUCUEUSVDJBUSVCBLZUNUPUQVCCLZVDUPUQURV
      EUFUPUQURVEUGURUPVEVFUQBCVCUHUIACDEFVCGHIUJUKULJABDEFVAGHIUMUO $.

    $( An element of a set is less than or equal to the least upper bound of
       the set.  (Contributed by NM, 21-Oct-2011.) $)
    lubel $p |- ( ( K e. CLat /\ X e. S /\ S C_ B ) -> X .<_ ( U ` S ) ) $=
      ( ccla wcel wss w3a csn cfv wceq clat wa clatl ssel lubsn 3impb wbr snssi
      impcom syl2an lubss syl3an3 3com23 eqbrtrrd ) DJKZFBKZBALZMFNZCOZFBCOZEUK
      ULUMUOFPZUKDQKFAKZUQULUMRDSUMULURBAFTUEACDFGIUAUFUBUKUMULUOUPEUCZULUKUMUN
      BLUSFBUDAUNBCDEGHIUGUHUIUJ $.
  $}

  ${
    $d x y z B $.  $d x y z .\/ $.  $d x y z K $.  $d x y z S $.  $d x y z T $.
    $d x y z U $.
    lubun.b $e |- B = ( Base ` K ) $.
    lubun.j $e |- .\/ = ( join ` K ) $.
    lubun.u $e |- U = ( lub ` K ) $.
    $( The LUB of a union.  (Contributed by NM, 5-Mar-2012.) $)
    lubun $p |- ( ( K e. CLat /\ S C_ B /\ T C_ B )
                      -> ( U ` ( S u. T ) ) = ( ( U ` S ) .\/ ( U ` T ) ) ) $=
      ( vy vx vz wcel wbr wral wi wa syl3anc syl2anc adantr ccla wss w3a cun cv
      cfv cple crio co eqid biid simp1 unss biimpi 3adant1 lubval clat 3ad2ant1
      clatl clatlubcl 3adant3 latjcl wceq simpl1 syl simpl2 simpr sseldd simpl3
      3adant2 lubel latlej1 lattrd ralrimiva latlej2 ralunb breq2 ralbidv rspcv
      sylanbrc imbi12d mpid imp ad2ant2rl lubl anim12d latjle12 syl13anc sylibd
      wb biimtrid adantrr latasymb mpbi2and ex elun jaodan sylan2b breq1 imbi2d
      wo anbi12d biimprcd impbid riota5 eqtrd ) FUAMZBAUBZCAUBZUCZBCUDZDUFJUEZK
      UEZFUGUFZNZJXKOZXLLUEZXNNZJXKOZXMXQXNNZPZLAOZQZKAUHBDUFZCDUFZEUIZXJYCKJLA
      XKDFXNUAGXNUJZIYCUKXGXHXIULXHXIXKAUBZXGXHXIQYHBCAUMUNUOUPXJYCKAYFXJFUQMZY
      DAMZYEAMZYFAMZXGXHYIXIFUSZURZXGXHYJXIABDFGIUTZVAZXGXIYKXHACDFGIUTZVJZAEFY
      DYEGHVBZRZXJXMAMZQZYCXMYFVCZUUBYCUUCUUBYCQXMYFXNNZYFXMXNNZUUCXJYBUUDUUAXP
      XJYBUUDXJYBXLYFXNNZJXKOZUUDXJUUFJBOUUFJCOUUGXJUUFJBXJXLBMZQZAFXNXLYDYFGYG
      UUIXGYIXGXHXIUUHVDZYMVEZUUIBAXLXGXHXIUUHVFZXJUUHVGZVHUUIXGXHYJUUJUULYOSZU
      UIYIYJYKYLUUKUUNUUIXGXIYKUUJXGXHXIUUHVIYQSZYSRUUIXGUUHXHXLYDXNNUUJUUMUULA
      BDFXNXLGYGIVKRUUIYIYJYKYDYFXNNUUKUUNUUOAEFXNYDYEGYGHVLRVMZVNXJUUFJCXJXLCM
      ZQZAFXNXLYEYFGYGXJYIUUQYNTZUURCAXLXGXHXIUUQVIZXJUUQVGZVHUURXGXIYKXGXHXIUU
      QVDZUUTYQSZXJYLUUQYTTUURXGUUQXIXLYEXNNUVBUVAUUTACDFXNXLGYGIVKRUURYIYJYKYE
      YFXNNUUSUURXGXHYJUVBXGXHXIUUQVFYOSUVCAEFXNYDYEGYGHVORVMZVNUUFJBCVPVTXJYLY
      BUUGUUDPZPYTYAUVELYFAXQYFVCZXSUUGXTUUDUVFXRUUFJXKXQYFXLXNVQVRXQYFXMXNVQWA
      VSVEWBWCWDUUBXPUUEYBUUBXPUUEXPXOJBOZXOJCOZQZUUBUUEXOJBCVPUUBUVIYDXMXNNZYE
      XMXNNZQZUUEUUBUVGUVJUVHUVKUUBXGXHUUAUVGUVJPXGXHXIUUAVDZXGXHXIUUAVFXJUUAVG
      ZJABDFXNXMGYGIWERUUBXGXIUUAUVHUVKPUVMXGXHXIUUAVIUVNJACDFXNXMGYGIWERWFUUBY
      IYJYKUUAUVLUUEWJUUBXGYIUVMYMVEZXJYJUUAYPTXJYKUUAYRTUVNAEFXNYDYEXMGYGHWGWH
      WIWKWCWLUUBUUDUUEQUUCWJZYCUUBYIUUAYLUVPUVOUVNXJYLUUAYTTAFXNXMYFGYGWMRTWNW
      OXJUUCYCPZUUAXJUUGXSYFXQXNNZPZLAOZUVQXJUUFJXKXLXKMXJUUHUUQXAUUFXLBCWPXJUU
      HUUFUUQUUPUVDWQWRVNXJUVSLAXJXQAMZQZXSYDXQXNNZYEXQXNNZQZUVRXSXRJBOZXRJCOZQ
      UWBUWEXRJBCVPUWBUWFUWCUWGUWDUWBXGXHUWAUWFUWCPXGXHXIUWAVDZXGXHXIUWAVFZXJUW
      AVGZJABDFXNXQGYGIWERUWBXGXIUWAUWGUWDPUWHXGXHXIUWAVIZUWJJACDFXNXQGYGIWERWF
      WKUWBYIYJYKUWAUWEUVRWJUWBXGYIUWHYMVEUWBXGXHYJUWHUWIYOSUWBXGXIYKUWHUWKYQSU
      WJAEFXNYDYEXQGYGHWGWHWIVNUUCYCUUGUVTQUUCXPUUGYBUVTUUCXOUUFJXKXMYFXLXNVQVR
      UUCYAUVSLAUUCXTUVRXSXMYFXQXNWSWTVRXBXCSTXDXEXF $.
  $}

  ${
    $d y z B $.  $d y z G $.  $d y z K $.  $d y z .<_ $.  $d y z S $.
    clatglb.b $e |- B = ( Base ` K ) $.
    clatglb.l $e |- .<_ = ( le ` K ) $.
    clatglb.g $e |- G = ( glb ` K ) $.
    $( Properties of greatest lower bound of a complete lattice.  (Contributed
       by NM, 5-Dec-2011.) $)
    clatglb $p |- ( ( K e. CLat /\ S C_ B ) -> ( A. y e. S ( G ` S ) .<_ y
               /\ A. z e. B ( A. y e. S z .<_ y -> z .<_ ( G ` S ) ) ) ) $=
      ( ccla wcel wss wa simpl clatglbcl2 glbprop ) FKLZDCMZNABCDEFGKHIJRSOCDEF
      HJPQ $.

    $d y z X $.
    $( The greatest lower bound is the least element.  (Contributed by NM,
       5-Dec-2011.) $)
    clatglble $p |- ( ( K e. CLat /\ S C_ B /\ X e. S )
          -> ( G ` S ) .<_ X ) $=
      ( ccla wcel wss w3a simp1 cdm clatglbcl2 3adant3 simp3 glble ) DJKZBALZFB
      KZMABCDEJFGHITUAUBNTUABCOKUBABCDGIPQTUAUBRS $.

    $( Two ways of expressing "less than or equal to the greatest lower bound."
       (Contributed by NM, 5-Dec-2011.) $)
    clatleglb $p |- ( ( K e. CLat /\ X e. B /\ S C_ B )
     -> ( X .<_ ( G ` S ) <-> A. y e. S X .<_ y ) ) $=
      ( vz ccla wcel wss wbr cv wral wa wi breq1 w3a cfv clatglble 3expa simpl1
      3adantl2 clat clatl syl simpl2 clatglbcl 3adant2 adantr ssel 3ad2ant3 imp
      syl13anc mpan2d ralrimdva clatglb wceq ralbidv imbi12d rspccv simpl2im ex
      lattr com23 3imp impbid ) ELMZGBMZCBNZUAZGCDUBZFOZGAPZFOZACQZVNVPVRACVNVQ
      CMZRZVPVOVQFOZVRVKVMVTWBVLVKVMVTWBBCDEFVQHIJUCUDUFWAEUGMZVLVOBMZVQBMZVPWB
      RVRSWAVKWCVKVLVMVTUEEUHUIVKVLVMVTUJVNWDVTVKVMWDVLBCDEHJUKULUMVNVTWEVMVKVT
      WESVLCBVQUNUOUPBEFGVOVQHIVGUQURUSVKVLVMVSVPSZVKVMVLWFVKVMVLWFSZVKVMRWBACQ
      KPZVQFOZACQZWHVOFOZSZKBQWGAKBCDEFHIJUTWLWFKGBWHGVAZWJVSWKVPWMWIVRACWHGVQF
      TVBWHGVOFTVCVDVEVFVHVIVJ $.

    $d y T $.
    $( Subset law for greatest lower bound.  (Contributed by Mario Carneiro,
       16-Apr-2014.) $)
    clatglbss $p |- ( ( K e. CLat /\ T C_ B /\ S C_ T )
          -> ( G ` T ) .<_ ( G ` S ) ) $=
      ( vy ccla wcel wss w3a cfv wbr cv wral wa syl3anc simpl1 simpl2 clatglble
      simp3 sselda ralrimiva wb clatglbcl 3adant3 sstr ancoms 3adant1 clatleglb
      simp1 mpbird ) EKLZCAMZBCMZNZCDOZBDOFPZUTJQZFPZJBRZUSVCJBUSVBBLZSUPUQVBCL
      VCUPUQURVEUAUPUQURVEUBUSBCVBUPUQURUDUEACDEFVBGHIUCTUFUSUPUTALZBAMZVAVDUGU
      PUQURUNUPUQVFURACDEGIUHUIUQURVGUPURUQVGBCAUJUKULJABDEFUTGHIUMTUO $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Distributive lattices
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c DLat $.

  $( The class of distributive lattices. $)
  cdlat $a class DLat $.

  ${
    $d k b j m x y z $.
    $( A _distributive lattice_ is a lattice in which meets distribute over
       joins, or equivalently ( ~ latdisd ) joins distribute over meets.
       (Contributed by Stefan O'Rear, 30-Jan-2015.) $)
    df-dlat $a |- DLat = { k e. Lat | [. ( Base ` k ) / b ].
        [. ( join ` k ) / j ]. [. ( meet ` k ) / m ]. A. x e. b A. y e. b
          A. z e. b ( x m ( y j z ) ) = ( ( x m y ) j ( x m z ) ) } $.
  $}

  ${
    $d k b j m x y z K $.  $d k b j m x y z B $.  $d k b j m x y z .\/ $.
    $d k b j m x y z ./\ $.
    isdlat.b $e |- B = ( Base ` K ) $.
    isdlat.j $e |- .\/ = ( join ` K ) $.
    isdlat.m $e |- ./\ = ( meet ` K ) $.
    $( Property of being a distributive lattice.  (Contributed by Stefan
       O'Rear, 30-Jan-2015.) $)
    isdlat $p |- ( K e. DLat <-> ( K e. Lat /\ A. x e. B A. y e. B A. z e. B
        ( x ./\ ( y .\/ z ) ) = ( ( x ./\ y ) .\/ ( x ./\ z ) ) ) ) $=
      ( vj vm vb cv co wceq wral cmee cfv wsbc cjn cbs clat cdlat fveq2 eqtr4di
      vk sbceqbid fvexi wb wa raleq raleqbi1dv simpr eqidd simpl oveqd oveq123d
      sbceq1d eqeq12d ralbidv 2ralbidv sylan9bb sbc3ie bitrdi df-dlat elrab2
      3impb ) ANZBNZCNZKNZOZLNZOZVIVJVNOZVIVKVNOZVLOZPZCMNZQZBVTQZAVTQZLUGNZRSZ
      TZKWDUASZTZMWDUBSZTZVIVJVKEOZGOZVIVJGOZVIVKGOZEOZPZCDQZBDQADQZUGFUCUDWDFP
      ZWJWCLGTZKETZMDTWRWSWHXAMWIDWSWIFUBSDWDFUBUEHUFWSWFWTKWGEWSWGFUASEWDFUAUE
      IUFWSWCLWEGWSWEFRSGWDFRUEJUFUSUHUHWCWRMKLDEGDFUBHUIEFUAIUIGFRJUIVTDPZVLEP
      ZVNGPZWCWRUJXBWCVSCDQZBDQZADQXCXDUKZWRWBXFAVTDWAXEBVTDVSCVTDULUMUMXGXEWQA
      BDDXGVSWPCDXGVOWLVRWOXGVIVIVMWKVNGXCXDUNZXGVIUOXGVLEVJVKXCXDUPZUQURXGVPWM
      VQWNVLEXIXGVNGVIVJXHUQXGVNGVIVKXHUQURUTVAVBVCVHVDVEABCKUGLMVFVG $.

    $d X x y z $.  $d Y x y z $.  $d Z x y z $.

    $( In a distributive lattice, meets distribute over joins.  (Contributed by
       Stefan O'Rear, 30-Jan-2015.) $)
    dlatmjdi $p |- ( ( K e. DLat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
        ( X ./\ ( Y .\/ Z ) ) = ( ( X ./\ Y ) .\/ ( X ./\ Z ) ) ) $=
      ( vx vy vz wcel cv co wceq wral oveq1 eqeq12d clat isdlat simprbi oveq12d
      cdlat w3a oveq2d oveq2 oveq1d rspc3v mpan9 ) CUENZKOZLOZMOZBPZDPZUMUNDPZU
      MUODPZBPZQZMARLARKARZEANFANGANUFEFGBPZDPZEFDPZEGDPZBPZQZULCUANVBKLMABCDHI
      JUBUCVAVHEUPDPZEUNDPZEUODPZBPZQEFUOBPZDPZVEVKBPZQKLMEFGAAAUMEQZUQVIUTVLUM
      EUPDSVPURVJUSVKBUMEUNDSUMEUODSUDTUNFQZVIVNVLVOVQUPVMEDUNFUOBSUGVQVJVEVKBU
      NFEDUHUITUOGQZVNVDVOVGVRVMVCEDUOGFBUHUGVRVKVFVEBUOGEDUHUGTUJUK $.
  $}

  ${
    $d K x y z $.
    $( A distributive lattice is a lattice.  (Contributed by Stefan O'Rear,
       30-Jan-2015.) $)
    dlatl $p |- ( K e. DLat -> K e. Lat ) $=
      ( vx vy vz cdlat wcel clat cjn cfv cmee wceq cbs wral eqid isdlat simplbi
      cv co ) AEFAGFBQZCQZDQZAHIZRAJIZRSTUCRSUAUCRUBRKDALIZMCUDMBUDMBCDUDUBAUCU
      DNUBNUCNOP $.
  $}

  ${
    $d K x y z $.  $d D x y z $.  $d V x y z $.
    odudlat.d $e |- D = ( ODual ` K ) $.
    $( The dual of a distributive lattice is a distributive lattice and
       conversely.  (Contributed by Stefan O'Rear, 30-Jan-2015.) $)
    odudlatb $p |- ( K e. V -> ( K e. DLat <-> D e. DLat ) ) $=
      ( vx vy vz wcel clat cv cjn cfv co cmee wceq wral wa cdlat eqid isdlat
      cbs latdisd bicomd pm5.32i odulatb anbi1d bitrid odujoin odumeet 3bitr4g
      odubas ) BCHZBIHZEJZFJZGJZBKLZMBNLZMUNUOURMUNUPURMUQMOGBUALZPFUSPEUSPZQZA
      IHZUNUOUPURMUQMUNUOUQMUNUPUQMURMOGUSPFUSPEUSPZQZBRHARHVAUMVCQULVDUMUTVCUM
      VCUTEFGUSUQBURUSSZUQSZURSZUBUCUDULUMVBVCABCDUEUFUGEFGUSUQBURVEVFVGTEFGUSU
      RAUQUSABDVEUKAURBDVGUHAUQBDVFUITUJ $.
  $}

  ${
    dlatjmdi.b $e |- B = ( Base ` K ) $.
    dlatjmdi.j $e |- .\/ = ( join ` K ) $.
    dlatjmdi.m $e |- ./\ = ( meet ` K ) $.
    $( In a distributive lattice, joins distribute over meets.  (Contributed by
       Stefan O'Rear, 30-Jan-2015.) $)
    dlatjmdi $p |- ( ( K e. DLat /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
        ( X .\/ ( Y ./\ Z ) ) = ( ( X .\/ Y ) ./\ ( X .\/ Z ) ) ) $=
      ( cdlat wcel codu cfv w3a co wceq eqid odudlatb ibi odujoin odumeet sylan
      odubas dlatmjdi ) CKLZCMNZKLZEALFALGALOEFGDPBPEFBPEGBPDPQUFUHUGCKUGRZSTAD
      UGBEFGAUGCUIHUDUGDCUIJUAUGBCUIIUBUEUC $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Subset order structures
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c toInc $.

  $( Class function defining inclusion posets. $)
  cipo $a class toInc $.

  ${
    $d f o x y $.
    $( For any family of sets, define the poset of that family ordered by
       inclusion.  See ~ ipobas , ~ ipolerval , and ~ ipole for its contract.

       _EDITORIAL_:  I'm not thrilled with the name.  Any suggestions?
       (Contributed by Stefan O'Rear, 30-Jan-2015.)
       (New usage is discouraged.) $)
    df-ipo $a |- toInc = ( f e. _V |-> [_ { <. x , y >. |
            ( { x , y } C_ f /\ x C_ y ) } / o ]_
    ( { <. ( Base ` ndx ) , f >. , <. ( TopSet ` ndx ) , ( ordTop ` o ) >. } u.
      { <. ( le ` ndx ) , o >. , <. ( oc ` ndx ) , ( x e. f |->
           U. { y e. f | ( y i^i x ) = (/) } ) >. } ) ) $.
  $}

  $( The structure of ~ df-ipo is a structure defining indices up to 11.
     (Contributed by Mario Carneiro, 25-Oct-2015.) $)
  ipostr $p |- ( { <. ( Base ` ndx ) , B >. , <. ( TopSet ` ndx ) , J >. } u.
                 { <. ( le ` ndx ) , .<_ >. , <. ( oc ` ndx ) , ._|_ >. } )
               Struct <. 1 , ; 1 1 >. $=
    ( c1 c9 cc0 cdc cnx cbs cfv cop cts cpr cple coc 1nn basendx strle2 1nn0
    1lt9 9nn tsetndx 10nn plendx 0nn0 0lt1 declt decnncl ocndx 9lt10 strleun )
    EFEGHZEEHZIJKZALIMKZBLNIOKZCLIPKZDLNUOUPEFABQRUAUBUCSUQURUMUNCDUDUEEGETUFQU
    GUHEETQUIUJSUKUL $.

  ${
    $d f o x y F $.  $d x y I $.  $d f o .<_ $.  $d x y V $.  $d x y X $.
    $d x y Y $.
    ipoval.i $e |- I = ( toInc ` F ) $.
    ${
      ipoval.l $e |- .<_ = { <. x , y >. | ( { x , y } C_ F /\ x C_ y ) } $.
      $( Value of the inclusion poset.  (Contributed by Stefan O'Rear,
         30-Jan-2015.) $)
      ipoval $p |- ( F e. V -> I = ( { <. ( Base ` ndx ) , F >. ,
          <. ( TopSet ` ndx ) , ( ordTop ` .<_ ) >. } u.
        { <. ( le ` ndx ) , .<_ >. , <. ( oc ` ndx ) , ( x e. F |->
           U. { y e. F | ( y i^i x ) = (/) } ) >. } ) ) $=
        ( vf vo wcel cvv cnx cfv cop cpr cv wceq wa opeq2d cbs cts cple coc cin
        cordt c0 crab cuni cmpt cun elex cipo wss csb cxp vex xpex prss biranri
        copab ssopab2i df-xp sseqtrri ssexi sseq2 anbi1d opabbidv eqtr4di simpl
        a1i simpr fveq2d preq12d unieqd mpteq12dv adantr uneq12d csbied2 df-ipo
        id rabeq prex unex fvmpt eqtrid syl ) CFKCLKZDMUANZCOZMUBNZEUFNZOZPZMUC
        NZEOZMUDNZACBQZAQZUEUGRZBCUHZUIZUJZOZPZUKZRCFULWHDCUMNXFGICJWSWRPZIQZUN
        ZWSWRUNZSZABVAZWIXHOZWKJQZUFNZOZPZWOXNOZWQAXHWTBXHUHZUIZUJZOZPZUKZUOXFL
        UMXHCRZJXLEYDXFLXLLKYEXLXHXHUPZXHXHIUQZYGURXLWSXHKWRXHKSZABVAYFXKYHABYH
        XIXJWSWRXHAUQBUQUSUTVBABXHXHVCVDVEVKYEXLXGCUNZXJSZABVAEYEXKYJABYEXIYIXJ
        XHCXGVFVGVHHVIYEXNERZSZXQWNYCXEYLXMWJXPWMYLXHCWIYEYKVJTYLXOWLWKYLXNEUFY
        EYKVLZVMTVNYLXRWPYBXDYLXNEWOYMTYLYAXCWQYEYAXCRYKYEAXHXTCXBYEWAYEXSXAWTB
        XHCWBVOVPVQTVNVRVSABIJVTWNXEWJWMWCWPXDWCWDWEWFWG $.
    $}

    $( Base set of the inclusion poset.  (Contributed by Stefan O'Rear,
       30-Jan-2015.)  (Revised by Mario Carneiro, 25-Oct-2015.) $)
    ipobas $p |- ( F e. V -> F = ( Base ` I ) ) $=
      ( vx vy wcel cnx cbs cfv cop cts cv cpr wss wa copab cordt cple c1 coc c0
      cin wceq crab cuni cmpt cun cdc ipostr csn snsspr1 ssun1 sstri strfv eqid
      baseid ipoval fveq2d eqtr4d ) ACGZAHIJAKZHLJEMZFMZNAOVCVDOPEFQZRJZKZNZHSJ
      VEKHUAJEAVDVCUCUBUDFAUEUFUGZKNZUHZIJBIJAVKICTTTUIKAVFVEVIUJUQVBUKVHVKVBVG
      ULVHVJUMUNUOVABVKIEFABVECDVEUPURUSUT $.

    $( Relation of the inclusion poset.  (Contributed by Stefan O'Rear,
       30-Jan-2015.) $)
    ipolerval $p |- ( F e. V ->
          { <. x , y >. | ( { x , y } C_ F /\ x C_ y ) } = ( le ` I ) ) $=
      ( wcel cv cpr wss wa copab cnx cfv cop cple wceq cvv vex c1 cbs cts cordt
      coc cin c0 crab cuni cmpt cun cxp biranri ssopab2i df-xp sseqtrri sqxpexg
      prss ssexg sylancr cdc ipostr pleid snsspr1 ssun2 sstri strfv eqid ipoval
      csn syl fveq2d eqtr4d ) CEGZAHZBHZICJZVNVOJZKZABLZMUANCOMUBNVSUCNZOIZMPNV
      SOZMUDNACVOVNUEUFQBCUGUHUIZOZIZUJZPNZDPNVMVSRGZVSWGQVMVSCCUKZJWIRGWHVSVNC
      GVOCGKZABLWIVRWJABWJVPVQVNVOCASBSUQULUMABCCUNUOCEUPVSWIRURUSVSWFPRTTTUTOC
      VTVSWCVAVBWBVIWEWFWBWDVCWEWAVDVEVFVJVMDWFPABCDVSEFVSVGVHVKVL $.

    ipole.l $e |- .<_ = ( le ` I ) $.
    $( Topology of the inclusion poset.  (Contributed by Mario Carneiro,
       24-Oct-2015.) $)
    ipotset $p |- ( F e. V -> ( ordTop ` .<_ ) = ( TopSet ` I ) ) $=
      ( vx vy wcel cv cpr wss cordt cfv cnx cop cts cple wceq c1 wa cbs coc cin
      copab c0 crab cuni cmpt cun cvv cdc ipostr tsetid csn snsspr2 ssun1 sstri
      fvex strfv ax-mp ipolerval eqtr4id fveq2d eqid ipoval 3eqtr4a ) ADIZGJZHJ
      ZKALVIVJLUAGHUEZMNZOUBNAPZOQNVLPZKZORNVKPOUCNGAVJVIUDUFSHAUGUHUIZPKZUJZQN
      ZCMNBQNVLUKIVLVSSVKMUSVLVRQUKTTTULPAVLVKVPUMUNVNUOVOVRVMVNUPVOVQUQURUTVAV
      HCVKMVHCBRNVKFGHABDEVBVCVDVHBVRQGHABVKDEVKVEVFVDVG $.

    $d .<_ x y $.  $d X x y $.  $d Y x y $.
    $( Weak order condition of the inclusion poset.  (Contributed by Stefan
       O'Rear, 30-Jan-2015.) $)
    ipole $p |- ( ( F e. V /\ X e. F /\ Y e. F ) -> ( X .<_ Y <-> X C_ Y ) ) $=
      ( vx vy wcel w3a cv cpr wss wa wbr wb wceq 3adant1 copab preq12 eqid cple
      sseq1d sseq12 anbi12d brabga cfv ipolerval breqd 3ad2ant1 prssi biantrurd
      eqtr4id 3bitr4d ) ADKZEAKZFAKZLZEFIMZJMZNZAOZVAVBOZPZIJUAZQZEFNZAOZEFOZPZ
      EFCQZVKURUSVHVLRUQVFVLIJEFVGAAVAESVBFSPZVDVJVEVKVNVCVIAVAVBEFUBUEVAEVBFUF
      UGVGUCUHTUQURVMVHRUSUQCVGEFUQCBUDUIVGHIJABDGUJUOUKULUTVJVKURUSVJUQEFAUMTU
      NUP $.
  $}

  ${
    ipolt.i $e |- I = ( toInc ` F ) $.
    ipolt.l $e |- .< = ( lt ` I ) $.
    $( Strict order condition of the inclusion poset.  (Contributed by Stefan
       O'Rear, 30-Jan-2015.) $)
    ipolt $p |- ( ( F e. V /\ X e. F /\ Y e. F ) -> ( X .< Y <-> X C. Y ) ) $=
      ( wcel w3a cple cfv wbr wne wa wss wpss eqid wb cvv anbi1d pltval 3adant1
      ipole cipo fvexi mp3an1 df-pss a1i 3bitr4d ) BDIZEBIZFBIZJZEFCKLZMZEFNZOZ
      EFPZUQOZEFAMZEFQZUNUPUSUQBCUODEFGUORZUDUAULUMVAURSZUKCTIULUMVDCBUEGUFTBBA
      CUOEFVCHUBUGUCVBUTSUNEFUHUIUJ $.
  $}

  ${
    $d F a b c $.  $d I a b c $.
    ipopos.i $e |- I = ( toInc ` F ) $.
    $( The inclusion poset on a family of sets is actually a poset.
       (Contributed by Stefan O'Rear, 30-Jan-2015.) $)
    ipopos $p |- I e. Poset $=
      ( va vb vc cvv wcel cpo cfv cipo a1i cv wa wbr wss wb ipole w3a anbi12d
      cple fvexi ipobas eqidd ssid 3anidm23 mpbiri weq 3com23 simpl simpr eqssd
      eqid biimtrdi wi 3adant3r3 3adant3r1 3adant3r2 3imtr4d isposd wn c0 fvprc
      sstr eqtrid 0pos eqeltrdi pm2.61i ) AGHZBIHVIDEFABBUAJZGBGHVIBAKCUBLABGCU
      CVIVJUDVIDMZAHZNVKVKVJOZVKVKPZVKUEVIVLVMVNQABVJGVKVKCVJUMZRUFUGVIVLEMZAHZ
      SZVKVPVJOZVPVKVJOZNVKVPPZVPVKPZNZDEUHVRVSWAVTWBABVJGVKVPCVORZVIVQVLVTWBQA
      BVJGVPVKCVORUITWCVKVPWAWBUJWAWBUKULUNVIVLVQFMZAHZSNZWAVPWEPZNZVKWEPZVSVPW
      EVJOZNVKWEVJOZWIWJUOWGVKVPWEVDLWGVSWAWKWHVIVLVQVSWAQWFWDUPVIVQWFWKWHQVLAB
      VJGVPWECVORUQTVIVLWFWLWJQVQABVJGVKWECVORURUSUTVIVAZBVBIWMBAKJVBCAKVCVEVFV
      GVH $.
  $}

  ${
    $d A w z $.  $d A x y $.  $d X w z $.  $d x z $.  $d y z $.
    $( Condition for a family of sets to be directed by inclusion.
       (Contributed by Stefan O'Rear, 2-Apr-2015.) $)
    isipodrs $p |- ( ( toInc ` A ) e. Dirset <-> ( A e. _V /\ A =/= (/) /\
            A. x e. A A. y e. A E. z e. A ( x u. y ) C_ z ) ) $=
      ( cipo cfv wcel cvv c0 wne cv wss wrex wral w3a cbs eqid wa wb anbi12d wn
      cdrs cun wceq drsbn0 neneqd fvprc fveq2d base0 eqtr4di nsyl2 cproset cple
      simp1 wbr isdrs cpo ipopos posprs mp1i 2thd ipobas neeq1 rexeq raleqbi1dv
      id syl simpll simplrl simpr ipole syl3anc simplrr unss rexbidva 2ralbidva
      bitrdi anbi2d bitr3d 3anass 3bitr4g bitrid pm5.21nii ) DEFZUBGZDHGZWFDIJZ
      AKZBKZUCCKZLZCDMZBDNADNZOZWEWDPFZIUDWFWEWOIWOWDWOQZUEUFWFUAZWOIPFIWQWDIPD
      EUGUHUIUJUKWFWGWMUNWEWDULGZWOIJZWHWJWDUMFZUOZWIWJWTUOZRZCWOMZBWONZAWONZOZ
      WFWNABCWOWDWTWPWTQZUPWFWRWSXFRZRWFWGWMRZRXGWNWFWRWFXIXJWFWRWFWDUQGWRWFDWD
      WDQZURWDUSUTWFVFVAWFWGXCCDMZBDNZADNZRZXIXJWFDWOUDZXOXISDWDHXKVBXPWGWSXNXF
      DWOIVCXMXEADWOXLXDBDWOXCCDWOVDVEVETVGWFXNWMWGWFXLWLABDDWFWHDGZWIDGZRZRZXC
      WKCDXTWJDGZRZXCWHWJLZWIWJLZRWKYBXAYCXBYDYBWFXQYAXAYCSWFXSYAVHZWFXQXRYAVIX
      TYAVJZDWDWTHWHWJXKXHVKVLYBWFXRYAXBYDSYEWFXQXRYAVMYFDWDWTHWIWJXKXHVKVLTWHW
      IWJVNVQVOVPVRVSTWRWSXFVTWFWGWMVTWAWBWC $.

    $( Direction by inclusion as used here implies sethood.  (Contributed by
       Stefan O'Rear, 2-Apr-2015.) $)
    ipodrscl $p |- ( ( toInc ` A ) e. Dirset -> A e. _V ) $=
      ( vx vy vz cipo cfv cdrs wcel cvv c0 wne cv cun wss wrex isipodrs simp1bi
      wral ) AEFGHAIHAJKBLCLMDLNDAOCARBARBCDAPQ $.

    $( Finite upper bound property for directed collections of sets.
       (Contributed by Stefan O'Rear, 2-Apr-2015.) $)
    ipodrsfi $p |- ( ( ( toInc ` A ) e. Dirset /\ X C_ A /\ X e. Fin ) ->
        E. z e. A U. X C_ z ) $=
      ( vw cipo cfv cdrs wcel wss cfn w3a cv cple wbr wral wrex cvv 3ad2ant1 wa
      eqid cbs cuni simp2 ipodrscl ipobas syl sseqtrd drsdirfi syld3an2 rexeqdv
      wceq wb adantr sselda adantrl simprl ipole syl3anc anassrs unissb bitr4di
      ralbidva rexbidva bitr3d mpbid ) BEFZGHZCBIZCJHZKZDLZALZVFMFZNZDCOZAVFUAF
      ZPZCUBVLIZABPZVGCVPIVHVIVQVJCBVPVGVHVIUCZVGVHBVPUKZVIVGBQHZWABUDZBVFQVFTZ
      UEUFRZUGADVPVFVMCVPTVMTZUHUIVJVOABPVQVSVJVOABVPWEUJVJVOVRABVJVLBHZSZVOVKV
      LIZDCOVRWHVNWIDCVJWGVKCHZVNWIULZVJWGWJSZSWBVKBHZWGWKVJWBWLVGVHWBVIWCRUMVJ
      WJWMWGVJCBVKVTUNUOVJWGWJUPBVFVMQVKVLWDWFUQURUSVBDCVLUTVAVCVDVE $.

    $( The finite subsets of any set are directed by inclusion.  (Contributed
       by Stefan O'Rear, 2-Apr-2015.) $)
    fpwipodrs $p |- ( A e. V -> ( toInc ` ( ~P A i^i Fin ) ) e. Dirset ) $=
      ( vx vy vz wcel cpw cfn cin cvv c0 wne cv cun wss wrex wral cipo wa elin
      cfv cdrs pwexg inex1g 0elpw elini ne0i mp1i pwuncl ad2ant2r unfi ad2ant2l
      syl 0fi elind syl2anb ssid sseq2 rspcev sylancl rgen2 isipodrs syl3anbrc
      a1i ) ABFZAGZHIZJFZVGKLZCMZDMZNZEMZOZEVGPZDVGQCVGQZVGRUAUBFVEVFJFVHABUCVF
      HJUDUMKVGFVIVEKVFHAUEUNUFVGKUGUHVPVEVOCDVGVGVJVGFZVKVGFZSVLVGFZVLVLOZVOVQ
      VJVFFZVJHFZSZVKVFFZVKHFZSZVSVRVJVFHTVKVFHTWCWFSVFHVLWAWDVLVFFWBWEVJVKAUIU
      JWBWEVLHFWAWDVJVKUKULUOUPVLUQVNVTEVLVGVMVLVLURUSUTVAVDCDEVGVBVC $.
  $}

  ${
    $d ph a b c u v $.  $d A a b c u v $.  $d A x y z $.  $d B a b c z $.
    $d B x y $.  $d F a b c u v $.  $d F x y z $.  $d a x y $.  $d b y $.
    ipodrsima.f $e |- ( ph -> F Fn ~P A ) $.
    ipodrsima.m $e |- ( ( ph /\ ( u C_ v /\ v C_ A ) ) ->
        ( F ` u ) C_ ( F ` v ) ) $.
    ipodrsima.d $e |- ( ph -> ( toInc ` B ) e. Dirset ) $.
    ipodrsima.s $e |- ( ph -> B C_ ~P A ) $.
    ipodrsima.a $e |- ( ph -> ( F " B ) e. V ) $.
    $( The monotone image of a directed set.  (Contributed by Stefan O'Rear,
       2-Apr-2015.) $)
    ipodrsima $p |- ( ph -> ( toInc ` ( F " B ) ) e. Dirset ) $=
      ( vz va vb vc cv wss wral wa vx vy cima cvv wcel c0 wne cun wrex cipo cfv
      cdrs elexd w3a isipodrs simp2d cpw wfn wceq wb fnimaeq0 syl2anc necon3bid
      sylib mpbird simp3d wi simplll simpr ad2antrr simprr sseldd elpwid adantr
      vex weq sseq12 sseq1 adantl anbi12d anbi2d syl2an imbi12d vtocl2 syl12anc
      fveq2 ex anim12d unss 3imtr3g anassrs reximdva ralimdva mpd uneq1 rexbidv
      sseq1d ralbidv ralima uneq2 sseq2 rexima bitrd syl3anbrc ) AFEUCZUDUEXEUF
      UGZUAQZUBQZUHZMQZRZMXEUIZUBXESZUAXESZXEUJUKULUEAXEGLUMAXFEUFUGZAEUDUEZXON
      QZOQZUHPQZRZPEUIZOESZNESZAEUJUKULUEXPXOYCUNJNOPEUOVDZUPAXEUFEUFAFDUQZURZE
      YERZXEUFUSEUFUSUTHKYEEFVAVBVCVEAXNXQFUKZXRFUKZUHZXSFUKZRZPEUIZOESZNESZAYC
      YOAXPXOYCYDVFAYBYNNEAXQEUEZTZYAYMOEYQXREUEZTXTYLPEYQYRXSEUEZXTYLVGYQYRYST
      ZTZXQXSRZXRXSRZTYHYKRZYIYKRZTXTYLUUAUUBUUDUUCUUEUUAUUBUUDUUAUUBTAUUBXSDRZ
      UUDAYPYTUUBVHUUAUUBVIUUAUUFUUBUUAXSDUUAEYEXSAYGYPYTKVJYQYRYSVKVLVMZVNACQZ
      BQZRZUUIDRZTZTZUUHFUKZUUIFUKZRZVGZAUUBUUFTZTZUUDVGCBXQXSNVOPVOZCNVPZBPVPZ
      TZUUMUUSUUPUUDUVCUULUURAUVCUUJUUBUUKUUFUUHXQUUIXSVQUVBUUKUUFUTZUVAUUIXSDV
      RZVSVTWAUVAUUNYHUSUUOYKUSZUUPUUDUTUVBUUHXQFWFUUIXSFWFZUUNYHUUOYKVQWBWCIWD
      WEWGUUAUUCUUEUUAUUCTAUUCUUFUUEAYPYTUUCVHUUAUUCVIUUAUUFUUCUUGVNUUQAUUCUUFT
      ZTZUUEVGCBXRXSOVOUUTCOVPZUVBTZUUMUVIUUPUUEUVKUULUVHAUVKUUJUUCUUKUUFUUHXRU
      UIXSVQUVBUVDUVJUVEVSVTWAUVJUUNYIUSUVFUUPUUEUTUVBUUHXRFWFUVGUUNYIUUOYKVQWB
      WCIWDWEWGWHXQXRXSWIYHYIYKWIWJWKWLWMWMWNAXNYHXHUHZXJRZMXEUIZUBXESZNESZYOAY
      FYGXNUVPUTHKXMUVOUANYEEFXGYHUSZXLUVNUBXEUVQXKUVMMXEUVQXIUVLXJXGYHXHWOWQWP
      WRWSVBAUVOYNNEAUVOYJXJRZMXEUIZOESZYNAYFYGUVOUVTUTHKUVNUVSUBOYEEFXHYIUSZUV
      MUVRMXEUWAUVLYJXJXHYIYHWTWQWPWSVBAUVSYMOEAYFYGUVSYMUTHKUVRYLMPYEEFXJYKYJX
      AXBVBWRXCWRXCVEUAUBMXEUOXD $.
  $}

  ${
    $d C s t x y $.  $d F s t x y $.  $d X s t x y $.  $d Y s t $.  $d S s $.
    $( An algebraic closure system satisfies ~ isacs3 .  (Contributed by Stefan
       O'Rear, 2-Apr-2015.) $)
    isacs3lem $p |- ( C e. ( ACS ` X ) -> ( C e. ( Moore ` X ) /\
          A. s e. ~P C ( ( toInc ` s ) e. Dirset -> U. s e. C ) ) ) $=
      ( vx vy cfv wcel cv cuni cpw wral wss cfn cin elpwid wrex ad2antrr adantl
      wa sstrd cacs cmre cipo cdrs acsmre cmrc mresspw syl sspwd sselda sspwuni
      wi sylib adantr elinel1 elinel2 fissuni syl2anc ad2antll ad3antrrr simprr
      unissd ad2antrl mrcssd simpl ipodrsfi syl3anc elpwi simprl sseldd mrcsscl
      eqid wel elssuni rexlimddv anassrs adantrr ralrimiva wb acsfiel mpbir2and
      adantlrr ex jca ) ABUAFGZABUBFGZCHZUCFUDGZWGIZAGZULZCAJZKABUEZWEWKCWLWEWG
      WLGZSZWHWJWOWHSZWJWIBLZDHZAUFFZFZWILZDWIJZMNZKZWOWQWHWOWGBJZLWQWOWGXEWEWL
      XEJWGWEAXEWEWFAXELWMABUGUHUIUJOWGBUKUMZUNWPXADXCWOWHWRXCGZXAWOWHXGSZSZWRE
      HZIZLZXAEWGJZMNZXGXLEXNPZWOWHXGWRWILZWRMGXOXGWRWIWRXBMUOOWRXBMUPWRWGEUQUR
      USXIXJXNGZXLSZSZWTXKWSFZWIXSAWRWSXKBWEWFWNXHXRWMUTWSVLZXIXQXLVAXSXKWIBXQX
      KWILXIXLXQXJWGXQXJWGXJXMMUOOZVBVCWOWQXHXRXFQTVDWOWHXRXTWILZXGWPXQYCXLWOWH
      XQYCWOWHXQSZSZXKWRLZYCDWGYDYFDWGPZWOYDWHXJWGLZXJMGZYGWHXQVEXQYHWHYBRXQYIW
      HXJXMMUPRDWGXJVFVGRYEDCVMZYFSZSZXTWRWIYLWFYFWRAGXTWRLWEWFWNYDYKWMUTYEYJYF
      VAYLWGAWRWOWGALZYDYKWNYMWEWGAVHRQYEYJYFVIVJAXKWSWRBYAVKVGYJXPYEYFWRWGVNVC
      TVOVPVQWBTVOVPVRWEWJWQXDSVSWNWHDAWIWSBYAVTQWAWCVRWD $.

    $( An algebraic closure system contains all directed unions of closed sets.
       (Contributed by Stefan O'Rear, 2-Apr-2015.) $)
    acsdrsel $p |- ( ( C e. ( ACS ` X ) /\ Y C_ C /\
          ( toInc ` Y ) e. Dirset ) -> U. Y e. C ) $=
      ( vs cacs cfv wcel wss cipo cdrs cuni wa cv cpw wceq fveq2 eleq1d imbi12d
      wi unieq wral cmre isacs3lem simprd adantr elpw2g biimpar rspcdva 3impia
      ) ABEFZGZCAHZCIFZJGZCKZAGZUKULLDMZIFZJGZUQKZAGZSZUNUPSDANZCUQCOZUSUNVAUPV
      DURUMJUQCIPQVDUTUOAUQCTQRUKVBDVCUAZULUKABUBFGVEABDUCUDUEUKCVCGULCAUJUFUGU
      HUI $.

    acsdrscl.f $e |- F = ( mrCls ` C ) $.
    $( In a closure system in which directed unions of closed sets are closed,
       closure commutes with directed unions.  (Contributed by Stefan O'Rear,
       2-Apr-2015.) $)
    isacs4lem $p |- ( ( C e. ( Moore ` X ) /\
          A. s e. ~P C ( ( toInc ` s ) e. Dirset -> U. s e. C ) ) ->
        ( C e. ( Moore ` X ) /\ A. t e. ~P ~P X ( ( toInc ` t ) e. Dirset ->
              ( F ` U. t ) = U. ( F " t ) ) ) ) $=
      ( vy vx cfv wcel cv cipo cdrs cuni wi cpw wral wceq wa wss elpwi ad2antrl
      cmre cima simpll mrcuni syl2anc cvv mrcf ffnd adantr simprl simprr mrcssd
      wfn cmrc fvexi imaex a1i ipodrsima adantlr fveq2 eleq1d unieq imbi12d crn
      simplr imassrn frnd sstrid elpw sylibr ad2antrr rspcdva mrcid eqtrd exp32
      mpd ralrimiv ex imdistani ) BDUCIJZEKZLIZMJZWCNZBJZOZEBPZQZAKZLIMJZWKNCIZ
      CWKUDZNZRZOZADPZPZQZWBWJWTWBWJSZWQAWSXAWKWSJZWLWPXAXBWLSZSZWMWOCIZWOXDWBW
      KWRTZWMXERWBWJXCUEZXBXFXAWLWKWRUAZUBBWKCDFUFUGXDWBWOBJZXEWORXGXDWNLIZMJZX
      IWBXCXKWJWBXCSZGHDWKCUHWBCWRUOXCWBWRBCBCDFUIZUJUKXLHKZGKZTZXODTZSZSBXNCXO
      DWBXCXRUEFXLXPXQULXLXPXQUMUNWBXBWLUMXBXFWBWLXHUBWNUHJXLCWKCBUPFUQURZUSUTV
      AXDWHXKXIOEWIWNWCWNRZWEXKWGXIXTWDXJMWCWNLVBVCXTWFWOBWCWNVDVCVEWBWJXCVGWBW
      NWIJZWJXCWBWNBTYAWBWNCVFBCWKVHWBWRBCXMVIVJWNBXSVKVLVMVNVRBWOCDFVOUGVPVQVS
      VTWA $.

    $( If closure commutes with directed unions, then the closure of a set is
       the closure of its finite subsets.  (Contributed by Stefan O'Rear,
       2-Apr-2015.) $)
    isacs5lem $p |- ( ( C e. ( Moore ` X ) /\
          A. t e. ~P ~P X ( ( toInc ` t ) e. Dirset ->
              ( F ` U. t ) = U. ( F " t ) ) ) -> ( C e. ( Moore ` X ) /\
          A. s e. ~P X ( F ` s ) = U. ( F " ( ~P s i^i Fin ) ) ) ) $=
      ( cfv wcel cv cipo cdrs cuni cima wceq wi cpw wral cfn wa cvv cmre unifpw
      cin fveq2i fpwipodrs mp1i fveq2 eleq1d unieq fveq2d imaeq2 unieqd eqeq12d
      vex imbi12d simplr wss inss1 elpwi sspwd adantl sstrid vpwex inex1 sylibr
      elpw adantlr rspcdva mpd eqtr3id ralrimiva ex imdistani ) BDUAGHZAIZJGZKH
      ZVOLZCGZCVOMZLZNZOZADPZPZQZEIZCGZCWGPZRUCZMZLZNZEWDQZVNWFWNVNWFSZWMEWDWOW
      GWDHZSZWHWJLZCGZWLWRWGCWGUBUDWQWJJGZKHZWSWLNZWGTHXAWQEUNWGTUEUFWQWCXAXBOA
      WEWJVOWJNZVQXAWBXBXCVPWTKVOWJJUGUHXCVSWSWAWLXCVRWRCVOWJUIUJXCVTWKVOWJCUKU
      LUMUOVNWFWPUPVNWPWJWEHZWFVNWPSZWJWDUQXDXEWJWIWDWIRURWPWIWDUQVNWPWGDWGDUSU
      TVAVBWJWDWIREVCVDVFVEVGVHVIVJVKVLVM $.

    $( In an algebraic closure system, closure commutes with directed unions.
       (Contributed by Stefan O'Rear, 2-Apr-2015.) $)
    acsdrscl $p |- ( ( C e. ( ACS ` X ) /\ Y C_ ~P X /\
          ( toInc ` Y ) e. Dirset ) -> ( F ` U. Y ) = U. ( F " Y ) ) $=
      ( vt vs cacs cfv wcel cpw cipo cdrs cuni cima wceq wa cv wi wral wss cmre
      fveq2 eleq1d fveq2d imaeq2 unieqd eqeq12d imbi12d isacs3lem isacs4lem syl
      unieq simprd adantr cdm cvv wb elfvdm pwexg elpw2g biimpar rspcdva 3impia
      3syl ) ACHIJZDCKZUAZDLIZMJZDNZBIZBDOZNZPZVFVHQFRZLIZMJZVPNZBIZBVPOZNZPZSZ
      VJVOSFVGKZDVPDPZVRVJWCVOWFVQVIMVPDLUCUDWFVTVLWBVNWFVSVKBVPDUMUEWFWAVMVPDB
      UFUGUHUIVFWDFWETZVHVFACUBIJZWGVFWHGRZLIMJWINAJSGAKTQWHWGQACGUJFABCGEUKULU
      NUOVFDWEJZVHVFCHUPZJVGUQJWJVHURACHUSCWKUTDVGUQVAVEVBVCVD $.

    $( A closure in an algebraic closure system is the union of the closures of
       finite subsets.  (Contributed by Stefan O'Rear, 2-Apr-2015.) $)
    acsficl $p |- ( ( C e. ( ACS ` X ) /\ S C_ X ) ->
        ( F ` S ) = U. ( F " ( ~P S i^i Fin ) ) ) $=
      ( vs vt cacs cfv wcel wa cv cpw cfn cin cima cuni wceq wral cipo wss pweq
      fveq2 ineq1d imaeq2d unieqd eqeq12d cmre wi isacs3lem isacs4lem isacs5lem
      cdrs 3syl simprd adantr cdm wb elfvdm elpw2g syl biimpar rspcdva ) ADHIJZ
      BDUAZKFLZCIZCVFMZNOZPZQZRZBCIZCBMZNOZPZQZRFDMZBVFBRZVGVMVKVQVFBCUCVSVJVPV
      SVIVOCVSVHVNNVFBUBUDUEUFUGVDVLFVRSZVEVDADUHIJZVTVDWAVFTIUMJVFQAJUIFAMSKWA
      GLZTIUMJWBQCICWBPQRUIGVRMSKWAVTKADFUJGACDFEUKGACDFEULUNUOUPVDBVRJZVEVDDHU
      QZJWCVEURADHUSBDWDUTVAVBVC $.

    $( A closure system is algebraic iff the closure of a generating set is the
       union of the closures of its finite subsets.  (Contributed by Stefan
       O'Rear, 2-Apr-2015.) $)
    isacs5 $p |- ( C e. ( ACS ` X ) <-> ( C e. ( Moore ` X ) /\
          A. s e. ~P X ( F ` s ) = U. ( F " ( ~P s i^i Fin ) ) ) ) $=
      ( vt cfv wcel cv cpw cima cuni wceq wral wa cipo cdrs wi 3syl wss cfn cin
      cacs cmre isacs3lem isacs4lem isacs5lem simpl elpwi mrcidb2 sylan2 adantr
      wb ciun simpr wfun mrcf ffun funiunfv ad2antrr eqtr4d sseq1d iunss bitrdi
      wf bitrd ex ralimdva imp isacs2 sylanbrc impbii ) ACUCGHZACUDGHZDIZBGZBVO
      JUAUBZKLZMZDCJZNZOZVMVNVOPGQHVOLAHRDAJNOVNFIZPGQHWCLBGBWCKLMRFVTJNOWBACDU
      EFABCDEUFFABCDEUGSWBVNVOAHZWCBGZVOTFVQNZUMZDVTNZVMVNWAUHVNWAWHVNVSWGDVTVN
      VOVTHZOZVSWGWJVSOZWDVPVOTZWFWJWDWLUMZVSWIVNVOCTWMVOCUIAVOBCEUJUKULWKWLFVQ
      WEUNZVOTWFWKVPWNVOWKVPVRWNWJVSUOVNWNVRMZWIVSVNVTABVEBUPWOABCEUQVTABURFVQB
      USSUTVAVBFVQWEVOVCVDVFVGVHVIFABCDEVJVKVL $.

    $( A closure system is algebraic iff closure commutes with directed unions.
       (Contributed by Stefan O'Rear, 2-Apr-2015.) $)
    isacs4 $p |- ( C e. ( ACS ` X ) <-> ( C e. ( Moore ` X ) /\
          A. s e. ~P ~P X ( ( toInc ` s ) e. Dirset ->
              ( F ` U. s ) = U. ( F " s ) ) ) ) $=
      ( vt cacs cfv wcel cmre cv cipo cdrs cuni cima wceq wi cpw wral wa isacs5
      isacs3lem isacs4lem syl cfn cin isacs5lem sylibr impbii ) ACGHIZACJHIZDKZ
      LHMIULNBHBULONPQDCRZRSTZUJUKFKZLHMIUONAIQFARSTUNACFUBDABCFEUCUDUNUKUOBHBU
      ORUEUFONPFUMSTUJDABCFEUGABCFEUAUHUI $.
  $}

  ${
    $d C s t $.  $d X s t $.
    $( A closure system is algebraic iff directed unions of closed sets are
       closed.  (Contributed by Stefan O'Rear, 2-Apr-2015.) $)
    isacs3 $p |- ( C e. ( ACS ` X ) <-> ( C e. ( Moore ` X ) /\
          A. s e. ~P C ( ( toInc ` s ) e. Dirset -> U. s e. C ) ) ) $=
      ( vt cacs cfv wcel cmre cv cipo cdrs cuni wi cpw wral isacs3lem cmrc cima
      wa wceq eqid isacs4lem isacs4 sylibr impbii ) ABEFGZABHFGZCIZJFKGUHLAGMCA
      NOSZABCPUIUGDIZJFKGUJLAQFZFUKUJRLTMDBNNOSUFDAUKBCUKUAZUBAUKBDULUCUDUE $.
  $}

  ${
    acsficld.1 $e |- ( ph -> A e. ( ACS ` X ) ) $.
    acsficld.2 $e |- N = ( mrCls ` A ) $.
    acsficld.3 $e |- ( ph -> S C_ X ) $.
    $( In an algebraic closure system, the closure of a set is the union of the
       closures of its finite subsets.  Deduction form of ~ acsficl .
       (Contributed by David Moews, 1-May-2017.) $)
    acsficld $p |- ( ph -> ( N ` S ) = U. ( N " ( ~P S i^i Fin ) ) ) $=
      ( cacs cfv wcel wss cpw cfn cin cima cuni wceq acsficl syl2anc ) ABEIJKCE
      LCDJDCMNOPQRFHBCDEGST $.

    $d S x $.  $d A w z $.  $d w X z $.  $d w z N $.  $d x Y $.  $d x N $.
    $( In an algebraic closure system, an element is in the closure of a set if
       and only if it is in the closure of a finite subset.  Alternate form of
       ~ acsficl .  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
    acsficl2d $p |- ( ph -> ( Y e. ( N ` S ) <->
                              E. x e. ( ~P S i^i Fin ) Y e. ( N ` x ) ) ) $=
      ( vz vw cfv wcel cpw cfn cin cima cv wfun cuni wrex acsficld cmre acsmred
      eleq2d wb crab cint cmpt funmpt mrcfval funeqd mpbiri eluniima 3syl bitrd
      wss ) AGDEMZNGEDOPQZRUAZNZGBSEMNBUTUBZAUSVAGACDEFHIJUCUFACFUDMNZETZVBVCUG
      ACFHUEVDVEKFOZKSLSURLCUHUIZUJZTKVFVGUKVDEVHKCEFLIULUMUNBUTGEUOUPUQ $.
  $}

  ${
    $d A x $.  $d s S t x $.  $d s t x ph $.  $d s t x I $.  $d s t N $.
    acsfiindd.1 $e |- ( ph -> A e. ( ACS ` X ) ) $.
    acsfiindd.2 $e |- N = ( mrCls ` A ) $.
    acsfiindd.3 $e |- I = ( mrInd ` A ) $.
    acsfiindd.4 $e |- ( ph -> S C_ X ) $.
    $( In an algebraic closure system, a set is independent if and only if all
       its finite subsets are independent.  Part of Proposition 4.1.3 in
       [FaureFrolicher] p. 83.  (Contributed by David Moews, 1-May-2017.) $)
    acsfiindd $p |- ( ph -> ( S e. I <-> ( ~P S i^i Fin ) C_ I ) ) $=
      ( vs vt wcel cfn wss wa cfv simpr adantr wn vx cpw cin wral cmre ad2antrr
      cv acsmred simplr elin1d elpwid mrissmrid ralrimiva dfss3 sylibr csn cdif
      cun elfpw sylib simpld difss2d snssd unssd simprd snfi unfi sylanbrc wceq
      sylancl ad4antr simpllr snidg 3syl eleqtrrd ismri2dad ad3antrrr neldifsnd
      elun2 ssneldd difsnb ssun1 sseqtrrid ssdifd eqsstrrd sstrd eqsstrd mrcssd
      wi ssdifssd sseld mtod rspcimdv biimtrid impancom ralrimiv wrex acsficl2d
      ex wb notbid ralnex bitr4di mpbird an32s ismri2dd impbida ) ACDMZCUBZNUCZ
      DOZAXHPZKUGZDMZKXJUDZXKXLXNKXJXLXMXJMZPZBCXMDEFABFUEQMZXHXPABFGUHZUFHIAXH
      XPUIXQXMCXQXINXMXLXPRUJUKULUMKXJDUNZUOAXKPZUABCDEFHIAXRXKXSSACFOZXKJSYAUA
      UGZCYCUPZUQZEQMZTZUACAYCCMZXKYGAYHPZXKPZYGYCLUGZEQZMZTZLYEUBNUCZUDZYJYNLY
      OYIYKYOMZXKYNXKXOYIYQPZYNXTYRXNYNKYKYDURZXJYRYSCOZYSNMZYSXJMYRYKYDCYRYKCY
      DYRYKYEOZYKNMZYRYQUUBUUCPYIYQRYKYEUSUTZVAZVBYRYCCAYHYQUIVCVDZYRUUCYDNMUUA
      YRUUBUUCUUDVEYCVFYKYDVGVJYSCUSVHYRXMYSVIZPZXNYNUUHXNPZYMYCXMYDUQZEQZMZUUI
      BXMDEFYCHIAXRYHYQUUGXNXSVKUUHXNRUUHYCXMMXNUUHYCYSXMUUHYHYCYDMYCYSMAYHYQUU
      GVLYCCVMYCYDYKVSVNYRUUGRZVOSVPUUHYMUULWIXNUUHYLUUKYCUUHBYKEUUJFAXRYHYQUUG
      XSVQHUUHYKYKYDUQZUUJUUHYCYKMTUUNYKVIUUHYKYEYCYRUUBUUGUUESUUHYCCVRVTYCYKWA
      UTUUHYKXMYDUUHYSYKXMYKYDWBUUMWCWDWEUUHXMFYDUUHXMYSFUUMUUHYSCFYRYTUUGUUFSA
      YBYHYQUUGJVQWFWGWJWHWKSWLWSWMWNWOWPAYGYPWTYHXKAYGYMLYOWQZTYPAYFUUOALBYEEF
      YCGHACFYDJWJWRXAYMLYOXBXCUFXDXEUMXFXG $.
  $}

  ${
    $d T f x $.  $d f x ph $.  $d S f x y $.  $d f x y N $.
    acsmapd.1 $e |- ( ph -> A e. ( ACS ` X ) ) $.
    acsmapd.2 $e |- N = ( mrCls ` A ) $.
    acsmapd.3 $e |- ( ph -> S C_ X ) $.
    acsmapd.4 $e |- ( ph -> T C_ ( N ` S ) ) $.
    $( In an algebraic closure system, if ` T ` is contained in the closure of
       ` S ` , there is a map ` f ` from ` T ` into the set of finite subsets
       of ` S ` such that the closure of ` U. ran f ` contains ` T ` .  This is
       proven by applying ~ acsficl2d to each element of ` T ` .  See Section
       II.5 in [Cohn] p. 81 to 82.  (Contributed by David Moews,
       1-May-2017.) $)
    acsmapd $p |- ( ph -> E. f
                   ( f : T --> ( ~P S i^i Fin ) /\ T C_ ( N ` U. ran f ) ) ) $=
      ( vx vy cv cfv wcel wral wa cuni wss cpw cfn cin wf wex crn cvv wrex fvex
      ssex syl sseld acsficl2d sylibd ralrimiv wceq fveq2 eleq2d sylc simprl wi
      ac6sg wal nfv nfra1 nfan csn cacs ad2antrr acsmred ffnd fnfvelrn sylancom
      wfn simplrl snssd unissd frn unifpw sseqtrdi sstrd mrcssd simprr r19.21bi
      unisn fveq2i eleqtrrdi sseldd ex alrimi df-ss sylibr jca eximdv mpd ) ADC
      UAUBUCZENZUDZLNZWSWQOZFOZPZLDQZRZEUEZWRDWQUFZSZFOZTZRZEUEADUGPZWSMNZFOZPZ
      MWPUHZLDQXEADCFOZTXKKDXPCFUIUJUKAXOLDAWSDPZWSXPPXOADXPWSKULAMBCFGWSHIJUMU
      NUOXNXBLMDWPEUGXLWTUPXMXAWSXLWTFUQURVBUSAXDXJEAXDXJAXDRZWRXIAWRXCUTXRXQWS
      XHPZVAZLVCXIXRXTLAXDLALVDWRXCLWRLVDXBLDVEVFVFXRXQXSXRXQRZWTVGZSZFOZXHWSYA
      BYCFXGGYABGABGVHOPXDXQHVIVJIYAYBXFYAWTXFXRXQWQDVNWTXFPYADWPWQAWRXCXQVOZVK
      DWSWQVLVMVPVQYAXGCGYAWRXGCTYEWRXGWPSCWRXFWPDWPWQVRVQCVSVTUKACGTXDXQJVIWAW
      BYAWSXAYDXRXBLDAWRXCWCWDYCWTFWTWSWQUIWEWFWGWHWIWJLDXHWKWLWMWIWNWO $.
  $}

  ${
    $d S f $.  $d T f $.  $d f ph $.  $d f N $.
    acsmap2d.1 $e |- ( ph -> A e. ( ACS ` X ) ) $.
    acsmap2d.2 $e |- N = ( mrCls ` A ) $.
    acsmap2d.3 $e |- I = ( mrInd ` A ) $.
    acsmap2d.4 $e |- ( ph -> S e. I ) $.
    acsmap2d.5 $e |- ( ph -> T C_ X ) $.
    acsmap2d.6 $e |- ( ph -> ( N ` S ) = ( N ` T ) ) $.
    $( In an algebraic closure system, if ` S ` and ` T ` have the same closure
       and ` S ` is independent, then there is a map ` f ` from ` T ` into the
       set of finite subsets of ` S ` such that ` S ` equals the union of
       ` ran f ` .  This is proven by taking the map ` f ` from ~ acsmapd and
       observing that, since ` S ` and ` T ` have the same closure, the closure
       of ` U. ran f ` must contain ` S ` .  Since ` S ` is independent, by
       ~ mrissmrcd , ` U. ran f ` must equal ` S ` .  See Section II.5 in
       [Cohn] p. 81 to 82.  (Contributed by David Moews, 1-May-2017.) $)
    acsmap2d $p |- ( ph -> E. f
                     ( f : T --> ( ~P S i^i Fin ) /\ S = U. ran f ) ) $=
      ( cuni cfv wss wa wex adantr cpw cfn cin crn wceq acsmred mrissd mrcssidd
      sseqtrrd acsmapd simprl cmre wcel simprr mrcssvd mrcssd frn unissd unifpw
      cv wf sseqtrdi ad2antrl sstrd mrcidmd sseqtrd eqsstrd mrissmrcd ex eximdv
      jca mpd ) ADCUAUBUCZEUTZVAZDVNUDZOZGPZQZRZESVOCVQUEZRZESABCDEGHIJABCFHKAB
      HIUFZLUGADDGPZCGPZABDGHWCJMUHNUIUJAVTWBEAVTWBAVTRZVOWAAVOVSUKWFBCVQFGHABH
      ULPUMVTWCTZJKWFCWEVRWFBCGHWGJWFBCFHKWGACFUMVTLTZUGZUHWFWEWDVRAWEWDUEVTNTW
      FWDVRGPVRWFBDGVRHWGJAVOVSUNWFBVQGHWGJUOUPWFBVQGHWGJWFVQCHVOVQCQAVSVOVQVMO
      CVOVPVMDVMVNUQURCUSVBVCZWIVDVEVFVGVDWJWHVHVKVIVJVL $.

    acsinfd.7 $e |- ( ph -> -. S e. Fin ) $.
    $( In an algebraic closure system, if ` S ` and ` T ` have the same closure
       and ` S ` is infinite independent, then ` T ` is infinite.  This follows
       from applying ~ unirnffid to the map given in ~ acsmap2d .  See Section
       II.5 in [Cohn] p. 81 to 82.  (Contributed by David Moews,
       1-May-2017.) $)
    acsinfd $p |- ( ph -> -. T e. Fin ) $=
      ( vf cfn wf wa wcel wn cpw cin crn cuni wceq acsmap2d simplrr wss simplrl
      cv inss2 fss sylancl simpr unirnffid eqeltrd ad2antrr pm2.65da exlimddv )
      ADCUAZPUBZOUJZQZCVBUCUDZUEZRZDPSZTOABCDOEFGHIJKLMUFAVFRZVGCPSZVHVGRZCVDPA
      VCVEVGUGVJDVBVJVCVAPUHDPVBQAVCVEVGUIUTPUKDVAPVBULUMVHVGUNUOUPAVITVFVGNUQU
      RUS $.

    $( In an algebraic closure system, if ` S ` and ` T ` have the same closure
       and ` S ` is infinite independent, then ` T ` dominates ` S ` .  This
       follows from applying ~ acsinfd and then applying ~ unirnfdomd to the
       map given in ~ acsmap2d .  See Section II.5 in [Cohn] p. 81 to 82.
       (Contributed by David Moews, 1-May-2017.) $)
    acsdomd $p |- ( ph -> S ~<_ T ) $=
      ( vf cfn wf wa cdom adantr cpw cin cv crn cuni wbr acsmap2d simprr simprl
      wceq cvv wss inss2 fss sylancl wcel acsinfd cacs elfvexd ssexd unirnfdomd
      wn cfv eqbrtrd exlimddv ) ADCUAZPUBZOUCZQZCVHUDUEZUJZRZCDSUFOABCDOEFGHIJK
      LMUGAVLRZCVJDSAVIVKUHVMDVHUKVMVIVGPULDPVHQAVIVKUIVFPUMDVGPVHUNUOADPUPVBVL
      ABCDEFGHIJKLMNUQTVMDGUKVMBURGABGURVCUPVLHTUSADGULVLLTUTVAVDVE $.
  $}

  ${
    acsinfdimd.1 $e |- ( ph -> A e. ( ACS ` X ) ) $.
    acsinfdimd.2 $e |- N = ( mrCls ` A ) $.
    acsinfdimd.3 $e |- I = ( mrInd ` A ) $.
    acsinfdimd.4 $e |- ( ph -> S e. I ) $.
    acsinfdimd.5 $e |- ( ph -> T e. I ) $.
    acsinfdimd.6 $e |- ( ph -> ( N ` S ) = ( N ` T ) ) $.
    acsinfdimd.7 $e |- ( ph -> -. S e. Fin ) $.
    $( In an algebraic closure system, if two independent sets have equal
       closure and one is infinite, then they are equinumerous.  This is proven
       by using ~ acsdomd twice with ~ acsinfd .  See Section II.5 in [Cohn]
       p. 81 to 82.  (Contributed by David Moews, 1-May-2017.) $)
    acsinfdimd $p |- ( ph -> S ~~ T ) $=
      ( cdom wbr cen mrissd acsdomd cfv acsmred eqcomd acsinfd sbth syl2anc ) A
      CDOPDCOPCDQPABCDEFGHIJKABDEGJABGHUAZLRZMNSABDCEFGHIJLABCEGJUFKRACFTDFTMUB
      ABCDEFGHIJKUGMNUCSCDUDUE $.
  $}

  ${
    $d s S y z $.  $d s X y z $.  $d s ph y z $.  $d s y I z $.  $d s y z N $.
    acsexdimd.1 $e |- ( ph -> A e. ( ACS ` X ) ) $.
    acsexdimd.2 $e |- N = ( mrCls ` A ) $.
    acsexdimd.3 $e |- I = ( mrInd ` A ) $.
    acsexdimd.4 $e |- ( ph -> A. s e. ~P X A. y e. X
                        A. z e. ( ( N ` ( s u. { y } ) ) \ ( N ` s ) )
                        y e. ( N ` ( s u. { z } ) ) ) $.
    acsexdimd.5 $e |- ( ph -> S e. I ) $.
    acsexdimd.6 $e |- ( ph -> T e. I ) $.
    acsexdimd.7 $e |- ( ph -> ( N ` S ) = ( N ` T ) ) $.
    $( In an algebraic closure system whose closure operator has the exchange
       property, if two independent sets have equal closure, they are
       equinumerous.  See ~ mreexfidimd for the finite case and ~ acsinfdimd
       for the infinite case.  This is a special case of Theorem 4.2.2 in
       [FaureFrolicher] p. 87.  (Contributed by David Moews, 1-May-2017.) $)
    acsexdimd $p |- ( ph -> S ~~ T ) $=
      ( wcel cfv adantr cfn cen wbr wa cmre acsmred csn cun cdif wral cpw simpr
      cv wceq mreexfidimd wn cacs acsinfdimd pm2.61dan ) AEUARZEFUBUCAUTUDBCDEF
      GHIJADIUESRUTADIKUFTLMABUMZJUMZCUMUGUHHSRCVBVAUGUHHSVBHSUIUJBIUJJIUKUJUTN
      TAEGRZUTOTAFGRZUTPTAUTULAEHSFHSUNZUTQTUOAUTUPZUDDEFGHIADIUQSRVFKTLMAVCVFO
      TAVDVFPTAVEVFQTAVFULURUS $.
  $}

  ${
    $d I x y $.  $d C x y $.  $d G x y $.  $d L x y $.  $d U x y $.
    $d F x y $.  $d X x y $.
    mreclat.i $e |- I = ( toInc ` C ) $.

    ${
      mrelatglb.g $e |- G = ( glb ` I ) $.
      $( Greatest lower bounds in a Moore space are realized by intersections.
         (Contributed by Stefan O'Rear, 31-Jan-2015.)  See ~ mrelatglbALT for
         an alternate proof. $)
      mrelatglb $p |- ( ( C e. ( Moore ` X ) /\ U C_ C /\ U =/= (/) ) ->
          ( G ` U ) = |^| U ) $=
        ( vx vy cfv wcel wss w3a wceq 3ad2ant1 wa wbr wb ipole syl3anc cmre wne
        c0 cint cple eqid cbs ipobas cglb a1i cpo ipopos mreintcl intss1 adantl
        simp2 cv simpl1 adantr sselda mpbird wral simplr simpl2 biimpd ralimdva
        simpll1 3impia ssint sylibr simp11 posglbdg ) AEUAJZKZBALZBUCUBZMZHIABB
        UDZCDDUEJZVSUFZVNVOADUGJNVPADVMFUHOCDUIJNVQGUJDUKKVQADFULUJVNVOVPUPZABE
        UMZVQHUQZBKZPZVRWCVSQZVRWCLZWDWGVQWCBUNUOWEVNVRAKZWCAKZWFWGRVNVOVPWDURV
        QWHWDWBUSVQBAWCWAUTADVSVMVRWCFVTSTVAVQIUQZAKZWJWCVSQZHBVBZMZWJVRVSQZWJV
        RLZWNWJWCLZHBVBZWPVQWKWMWRVQWKPZWLWQHBWSWDPZWLWQWTVNWKWIWLWQRVNVOVPWKWD
        VGVQWKWDVCWSBAWCVNVOVPWKVDUTADVSVMWJWCFVTSTVEVFVHHWJBVIVJWNVNWKWHWOWPRV
        NVOVPWKWMVKVQWKWMUPVQWKWHWMWBOADVSVMWJVRFVTSTVAVL $.

      $( The empty intersection in a Moore space is realized by the base set.
         (Contributed by Stefan O'Rear, 31-Jan-2015.) $)
      mrelatglb0 $p |- ( C e. ( Moore ` X ) -> ( G ` (/) ) = X ) $=
        ( vx vy cmre cfv wcel c0 cple eqid ipobas cglb a1i wss cv wbr wceq ral0
        cpo ipopos 0ss mre1cl rspec adantl wral wa mress wb adantr ipole mpbird
        mpd3an3 3adant3 posglbdg ) ADIJZKZGHALDBCCMJZVANZACUSEOBCPJUAUTFQCUCKUT
        ACEUDQLARUTAUEQADUFZGSZLKDVDVATZUTVEGLVEGUBUGUHUTHSZAKZVFDVATZVFVDVATGL
        UIUTVGUJVHVFDRZAVFDUKUTVGDAKZVHVIULUTVJVGVCUMACVAUSVFDEVBUNUPUOUQUR $.
    $}

    ${
      mrelatlub.f $e |- F = ( mrCls ` C ) $.
      mrelatlub.l $e |- L = ( lub ` I ) $.
      $( Least upper bounds in a Moore space are realized by the closure of the
         union.  (Contributed by Stefan O'Rear, 31-Jan-2015.)  See
         ~ mrelatlubALT for an alternate proof. $)
      mrelatlub $p |- ( ( C e. ( Moore ` X ) /\ U C_ C ) ->
          ( L ` U ) = ( F ` U. U ) ) $=
        ( vx cfv wcel wss wa wceq adantr wbr wb ipole syl3anc vy cmre cuni cple
        eqid cbs ipobas club a1i ipopos simpr uniss adantl mreuni sseqtrd mrccl
        cpo syldan cv elssuni mrcssid sylan9ssr simpll sselda mpbird w3a simp1l
        wral simplll simplr biimpd ralimdva 3impia unissb sylibr simp2 3ad2ant1
        mrcsscl poslubdg ) AFUBKZLZBAMZNZJUAABBUCZCKZEDDUDKZWFUEZWAADUFKOWBADVT
        GUGPEDUHKOWCIUIDUQLWCADGUJUIWAWBUKZWAWBWDFMZWEALZWCWDAUCZFWBWDWKMWABAUL
        UMWAWKFOWBAFUNPUOZAWDCFHUPURZWCJUSZBLZNZWNWEWFQZWNWEMZWOWCWNWDWEWNBUTWA
        WBWIWDWEMWLAWDCFHVAURVBWPWAWNALZWJWQWRRWAWBWOVCWCBAWNWHVDWCWJWOWMPADWFV
        TWNWEGWGSTVEWCUAUSZALZWNWTWFQZJBVHZVFZWEWTWFQZWEWTMZXDWAWDWTMZXAXFWAWBX
        AXCVGZXDWNWTMZJBVHZXGWCXAXCXJWCXANZXBXIJBXKWONZXBXIXLWAWSXAXBXIRWAWBXAW
        OVIXKBAWNWAWBXAVJVDWCXAWOVJADWFVTWNWTGWGSTVKVLVMJBWTVNVOWCXAXCVPZAWDCWT
        FHVRTXDWAWJXAXEXFRXHWCXAWJXCWMVQXMADWFVTWEWTGWGSTVEVS $.
    $}

    $( A Moore space is a complete lattice under inclusion.  (Contributed by
       Stefan O'Rear, 31-Jan-2015.)  TODO ( ~ df-riota update): Finish this
       proof using the new ~ isclat then use it to replace ~ mreclatBAD
       below. $)
$(
    mreclat $p |- ( C e. ( Moore ` X ) -> I e. CLat ) $=
      ( vy vx vs vz cfv wcel cpo cdm wceq wa cv wbr wral eqid jca sylibr ipopos
      cmre club cbs cpw cglb ccla a1i cple wi wreu crab biid lubdm wss vex elpw
      wrex wrmo adantr simpr poslubmo syl sylan2b ralrimiva rabid2 eqtr4d glbdm
      reu5 posglbmo isclat ) ACUBIJZBKJZBUCIZLZBUDIZUEZMZBUFIZLZVQMZNZNBUGJVLVM
      WBVMVLABDUAUHZVLVRWAVLVOEOZFOZBUIIZPEGOZQWDHOZWFPEWGQWEWHWFPUJHVPQNZFVPUK
      ZGVQULZVQVLWIFEHVPVNBWFKGVPRZWFRZVNRZWIUMWCUNVLWJGVQQVQWKMVLWJGVQWGVQJZVL
      WGVPUOZWJWGVPGUPUQZVLWPNZWIFVPURZWIFVPUSZNWJWRWSWT?WRVMWPNZWTWRVMWPVLVMWP
      WCUTVLWPVASZFEHVPWGBWFWMWLVBVCSWIFVPVITVDVEWJGVQVFTVGVLVTWEWDWFPEWGQWHWDW
      FPEWGQWHWEWFPUJHVPQNZFVPUKZGVQULZVQVLXCFEHVPVSBWFKGWLWMVSRZXCUMWCVHVLXDGV
      QQVQXEMVLXDGVQWOVLWPXDWQWRXCFVPURZXCFVPUSZNXDWRXGXH?WRXAXHXBFEHVPWGBWFWMW
      LVJVCSXCFVPVITVDVEXDGVQVFTVGSSVPVNVSBWLWNXFVKT $.
$)

    $( This hypothesis is the instance of the old ~ isclat that is needed.
       Remove it and ~ mreclatBAD when mreclat above is finished. $)
    isclatBAD. $e |- ( I e. CLat
       <-> ( I e. Poset /\ A. x ( x C_ ( Base ` I )
      -> ( ( ( lub ` I ) ` x ) e. ( Base ` I )
           /\ ( ( glb ` I ) ` x ) e. ( Base ` I ) ) ) ) ) $.
    $( A Moore space is a complete lattice under inclusion.  (Contributed by
       Stefan O'Rear, 31-Jan-2015.)  TODO ( ~ df-riota update):  Reprove using
       ~ isclat instead of the isclatBAD. hypothesis.  See commented-out
       mreclat above.  See ~ mreclat for a good version. $)
    mreclatBAD $p |- ( C e. ( Moore ` X ) -> I e. CLat ) $=
      ( cmre cfv wcel wss wa wi cuni eqid adantl wceq eqeltrd c0 ad2antrr eleq2
      cpo cbs club cglb wal ccla ipopos a1i cmrc mrelatlub uniss mreuni sseqtrd
      cv adantr mrccl syldan fveq2 mrelatglb0 mre1cl wne w3a mrelatglb mreintcl
      eqtrd cint 3expa pm2.61dane jca ex ipobas sseq2 anbi12d imbi12d syl mpbid
      wb alrimiv sylanbrc ) BDGHZIZCUAIZAUNZCUBHZJZWCCUCHZHZWDIZWCCUDHZHZWDIZKZ
      LZAUECUFIWBWABCEUGUHWAWMAWAWCBJZWGBIZWJBIZKZLZWMWAWNWQWAWNKZWOWPWSWGWCMZB
      UIHZHZBBWCXACWFDEXANZWFNUJWAWNWTDJXBBIWSWTBMZDWNWTXDJWAWCBUKOWAXDDPWNBDUL
      UOUMBWTXADXCUPUQQWSWPWCRWSWCRPZKZWJDBXFWJRWIHZDXEWJXGPWSWCRWIUROWAXGDPWNX
      EBWICDEWINZUSSVEWADBIWNXEBDUTSQWAWNWCRVAZWPWAWNXIVBWJWCVFBBWCWICDEXHVCBWC
      DVDQVGVHVIVJWABWDPZWRWMVQBCVTEVKXJWNWEWQWLBWDWCVLXJWOWHWPWKBWDWGTBWDWJTVM
      VNVOVPVRFVS $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Posets, directed sets, and lattices as relations
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Posets and lattices as relations
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  See commented-out notes for lattices as relations.

$)

  $c PosetRel $.
  $c TosetRel $.

  $( Extend class notation with the class of all posets. $)
  cps $a class PosetRel $.

  $( Extend class notation with the class of all totally ordered sets. $)
  ctsr $a class TosetRel $.

  $( Define the class of all posets (partially ordered sets) with weak ordering
     (e.g., "less than or equal to" instead of "less than").  A poset is a
     relation which is transitive, reflexive, and antisymmetric.  (Contributed
     by NM, 11-May-2008.) $)
  df-ps $a |- PosetRel = { r | ( Rel r /\ ( r o. r ) C_ r /\
              ( r i^i `' r ) = ( _I |` U. U. r ) ) } $.

  $( Define the class of all totally ordered sets.  (Contributed by FL,
     1-Nov-2009.) $)
  df-tsr $a |- TosetRel = { r e. PosetRel |
                ( dom r X. dom r ) C_ ( r u. `' r ) } $.

  ${
    $d r R $.
    $( The predicate "is a poset" i.e. a transitive, reflexive, antisymmetric
       relation.  (Contributed by NM, 11-May-2008.) $)
    isps $p |- ( R e. A -> ( R e. PosetRel <-> ( Rel R /\ ( R o. R ) C_ R /\
                ( R i^i `' R ) = ( _I |` U. U. R ) ) ) ) $=
      ( vr cv wrel ccom wss ccnv cin cid cuni cres wceq releq coeq1 coeq2 eqtrd
      w3a cps id sseq12d cnveq ineq12d unieqd reseq2d eqeq12d 3anbi123d elab2g
      unieq df-ps ) CDZEZUKUKFZUKGZUKUKHZIZJUKKZKZLZMZRBEZBBFZBGZBBHZIZJBKZKZLZ
      MZRCBSAUKBMZULVAUNVCUTVIUKBNVJUMVBUKBVJUMBUKFVBUKBUKOUKBBPQVJTZUAVJUPVEUS
      VHVJUKBUOVDVKUKBUBUCVJURVGJVJUQVFUKBUIUDUEUFUGCUJUH $.
  $}

  $( A poset is a relation.  (Contributed by NM, 12-May-2008.) $)
  psrel $p |- ( A e. PosetRel -> Rel A ) $=
    ( cps wcel wrel ccom wss ccnv cin cid cuni cres wceq w3a isps ibi simp1d )
    ABCZADZAAEAFZAAGHIAJJKLZQRSTMBANOP $.

  $( A poset is antisymmetric and reflexive.  (Contributed by FL,
     3-Aug-2009.) $)
  psref2 $p |- ( R e. PosetRel -> ( R i^i `' R ) = ( _I |` U. U. R ) ) $=
    ( cps wcel wrel ccom wss ccnv cin cid cuni cres wceq w3a isps ibi simp3d )
    ABCZADZAAEAFZAAGHIAJJKLZQRSTMBANOP $.

  $( A poset is transitive.  (Contributed by FL, 3-Aug-2009.) $)
  pstr2 $p |- ( R e. PosetRel -> ( R o. R ) C_ R ) $=
    ( cps wcel wrel ccom wss ccnv cin cid cuni cres wceq w3a isps ibi simp2d )
    ABCZADZAAEAFZAAGHIAJJKLZQRSTMBANOP $.

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z R $.
    $( Lemma for ~ psref and others.  (Contributed by NM, 12-May-2008.)
       (Revised by Mario Carneiro, 30-Apr-2015.) $)
    pslem $p |- ( R e. PosetRel -> ( ( ( A R B /\ B R C ) -> A R C ) /\
      ( A e. U. U. R -> A R A ) /\ ( ( A R B /\ B R A ) -> A = B ) ) ) $=
      ( vx vy vz wcel wbr wa wi cuni wceq cvv cv wal sylan adantr wb breq12 cps
      wrel psrel brrelex12 brrelex2 anim12dan ccom wss pstr2 cotr sylib 3adant3
      simpr w3a 3adant1 anbi12d 3adant2 imbi12d spc3gv 3expa syl3c ccnv cin cid
      ex cres wral psref2 asymref2 simplbi anidms rspccv adantrr simprbi ancoms
      3syl syl eqeq12 spc2gv 3jca ) DUAHZABDIZBCDIZJZACDIZKZADLLZHAADIZKZWBBADI
      ZJZABMZKZWAWDWEWAWDJANHZBNHZJZCNHZJEOZFOZDIZWSGOZDIZJZWRXADIZKZGPFPEPZWDW
      EWAWBWPWCWQWADUBZWBWPDUCZABDUDQZWAXGWCWQXHBCDUEQUFWAXFWDWADDUGDUHXFDUIEFG
      DUJUKRWAWDUMWNWOWQXFWFKXEWFEFGABCNNNWRAMZWSBMZXACMZUNZXCWDXDWEXMWTWBXBWCX
      JXKWTWBSXLWRAWSBDTZULXKXLXBWCSXJWSBXACDTUOUPXJXLXDWESXKWRAXACDTUQURUSUTVA
      VEWADDVBVCVDWGVFMZWRWRDIZEWGVGZWIDVHZXOXQWTWSWRDIZJZWRWSMZKZFPEPZEFDVIZVJ
      XPWHEAWGXJXPWHSWRAWRADTVKVLVPWAWKWLWAWKJWPYCWKWLWAWBWPWJXIVMWAYCWKWAXOYCX
      RXOXQYCYDVNVQRWAWKUMYBWMEFABNNXJXKJZXTWKYAWLYEWTWBXSWJXNXKXJXSWJSWSBWRADT
      VOUPWRAWSBVRURVSVAVEVT $.

    $( The domain and range of a poset equal its field.  (Contributed by NM,
       13-May-2008.) $)
    psdmrn $p |- ( R e. PosetRel -> ( dom R = U. U. R /\ ran R = U. U. R ) ) $=
      ( vx cps wcel cdm cuni wceq crn wss cun ssun1 dmrnssfld sstri a1i cv syl6
      wbr wi ssrdv eqssd wa pslem simp2d vex breldm ssun2 brelrn jca ) ACDZAEZA
      FFZGAHZUKGUIUJUKUJUKIUIUJUJULJZUKUJULKALZMNUIBUKUJUIBOZUKDZUOUOAQZUOUJDUI
      UQUQUAZUQRUPUQRURUOUOGRUOUOUOAUBUCZUOUOABUDZUTUEPSTUIULUKULUKIUIULUMUKULU
      JUFUNMNUIBUKULUIUPUQUOULDUSUOUOAUTUTUGPSTUH $.
  $}

  ${
    psref.1 $e |- X = dom R $.
    $( A poset is reflexive.  (Contributed by NM, 13-May-2008.) $)
    psref $p |- ( ( R e. PosetRel /\ A e. X ) -> A R A ) $=
      ( cps wcel wbr cuni cdm wceq crn psdmrn simpld eqtrid eleq2d wa wi simp2d
      pslem sylbid imp ) BEFZACFZAABGZUBUCABHHZFZUDUBCUEAUBCBIZUEDUBUGUEJBKUEJB
      LMNOUBUDUDPZUDQUFUDQUHAAJQAAABSRTUA $.

    $( The range of a poset equals it domain.  (Contributed by NM,
       7-Jul-2008.) $)
    psrn $p |- ( R e. PosetRel -> X = ran R ) $=
      ( cps wcel cdm crn cuni wceq wa psdmrn eqtr3 syl eqtrid ) ADEZBAFZAGZCOPA
      HHZIQRIJPQIAKPQRLMN $.
  $}

  $( A poset is antisymmetric.  (Contributed by NM, 12-May-2008.) $)
  psasym $p |- ( ( R e. PosetRel /\ A R B /\ B R A ) -> A = B ) $=
    ( cps wcel wbr wceq wa wi cuni pslem simp3d 3impib ) CDEZABCFZBACFZABGZNOPH
    ZAACFZIACJJESIRQIABACKLM $.

  $( A poset is transitive.  (Contributed by NM, 12-May-2008.)  (Revised by
     Mario Carneiro, 30-Apr-2015.) $)
  pstr $p |- ( ( R e. PosetRel /\ A R B /\ B R C ) -> A R C ) $=
    ( cps wcel wbr wa wi cuni wceq pslem simp1d 3impib ) DEFZABDGZBCDGZACDGZOPQ
    HRIADJJFAADGIPBADGHABKIABCDLMN $.

  $( The converse of a poset is a poset.  In the general case
     ` ( ``' R e. PosetRel -> R e. PosetRel ) ` is not true.  See ~ cnvpsb for
     a special case where the property holds.  (Contributed by FL, 5-Jan-2009.)
     (Proof shortened by Mario Carneiro, 3-Sep-2015.) $)
  cnvps $p |- ( R e. PosetRel -> `' R e. PosetRel ) $=
    ( cps wcel ccnv wrel ccom wss cin cid cuni cres wceq relcnv a1i cnvco pstr2
    cnvss syl eqsstrrid cvv psrel dfrel2 ineq2d eqtrdi psref2 relcnvfld reseq2d
    sylib incom 3eqtrd w3a wb cnvexg isps mpbir3and ) ABCZADZBCZUQEZUQUQFZUQGZU
    QUQDZHZIUQJJZKZLZUSUPAMNUPUTAAFZDZUQAAOUPVGAGVHUQGAPVGAQRSUPVCAUQHZIAJJZKVE
    UPVCUQAHVIUPVBAUQUPAEZVBALAUAZAUBUHUCUQAUIUDAUEUPVJVDIUPVKVJVDLVLAUFRUGUJUP
    UQTCURUSVAVFUKULABUMTUQUNRUO $.

  $( The converse of a poset is a poset.  (Contributed by FL, 5-Jan-2009.) $)
  cnvpsb $p |- ( Rel R -> ( R e. PosetRel <-> `' R e. PosetRel ) ) $=
    ( wrel cps wcel ccnv cnvps wceq wi dfrel2 eleq1 biimpd sylbi syl5 impbid2 )
    ABZACDZAEZCDZAFRQEZCDZOPQFOSAGZTPHAIUATPSACJKLMN $.

  ${
    $d A x y $.  $d R x y $.
    $( Any subset of a partially ordered set is partially ordered.
       (Contributed by FL, 24-Jan-2010.) $)
    psss $p |- ( R e. PosetRel -> ( R i^i ( A X. A ) ) e. PosetRel ) $=
      ( vx vy cps wcel cin wrel ccom wss cuni wceq mpsyl syl cv wbr wral wa wal
      uniin cxp ccnv cid inss1 psrel relss pstr2 trinxp wi unissi sstri unixpid
      cres elin eleq2i simprr cdm crn psdmrn simpld eleq2d biimpar psref syldan
      eqid adantrr brinxp2 syl21anbrc expr biimtrid expimpd ssralv ssbri psasym
      ralrimiv 3expib syl2ani alrimivv asymref2 sylanbrc cvv w3a wb inex1g isps
      mpbir3and ) BEFZBAAUAZGZEFZWIHZWIWIIWIJZWIWIUBGUCWIKZKZUMLZWIBJWGBHWKBWHU
      DZBUEWIBUFMWGBBIBJWLBUGABUHNWGCOZWQWIPZCWNQZWQDOZWIPZWTWQWIPZRWQWTLZUIZDS
      CSWOWNBKZKZWHKZKZGZJWGWRCXIQWSWNXEXGGZKXIWMXJBWHTUJXEXGTUKWGWRCXIWQXIFWQX
      FFZWQXHFZRWGWRWQXFXHUNWGXKXLWRXLWQAFZWGXKRWRXHAWQAULUOWGXKXMWRWGXKXMRRXMX
      MWQWQBPZWRWGXKXMUPZXOWGXKXNXMWGXKWQBUQZFZXNWGXQXKWGXPXFWQWGXPXFLBURXFLBUS
      UTVAVBWQBXPXPVEVCVDVFAAWQWQBVGVHVIVJVKVJVOWRCWNXIVLMWGXDCDXAWGWQWTBPZWTWQ
      BPZXCXBWIBWQWTWPVMWIBWTWQWPVMWGXRXSXCWQWTBVNVPVQVRCDWIVSVTWGWIWAFWJWKWLWO
      WBWCBWHEWDWAWIWENWF $.
  $}

  ${
    $d A x $.  $d R x $.  $d X x $.
    psssdm.1 $e |- X = dom R $.
    $( Field of a subposet.  (Contributed by Mario Carneiro, 9-Sep-2015.) $)
    psssdm2 $p |- ( R e. PosetRel ->
      dom ( R i^i ( A X. A ) ) = ( X i^i A ) ) $=
      ( vx cps wcel cxp cin cdm wss eqcomi dmxpid ineq12i sseqtri a1i cv wa wbr
      dmin simpr elin2d elinel1 psref sylan2 brinxp2 syl21anbrc vex syl eqelssd
      breldm ) BFGZEBAAHZIZJZCAIZUOUPKULUOBJZUMJZIUPBUMTUQCURACUQDLAMNOPULEQZUP
      GZRZUSUSUNSZUSUOGVAUSAGZVCUSUSBSZVBVACAUSULUTUAUBZVEUTULUSCGVDUSCAUCUSBCD
      UDUEAAUSUSBUFUGUSUSUNEUHZVFUKUIUJ $.

    $( Field of a subposet.  (Contributed by FL, 19-Sep-2011.)  (Revised by
       Mario Carneiro, 9-Sep-2015.) $)
    psssdm $p |- ( ( R e. PosetRel /\ A C_ X )
      -> dom ( R i^i ( A X. A ) ) = A ) $=
      ( cps wcel wss cxp cin cdm psssdm2 wceq sseqin2 biimpi sylan9eq ) BEFACGZ
      BAAHIJCAIZAABCDKPQALACMNO $.
  $}

  ${
    $d x y A $.  $d y B $.  $d r x y R $.  $d r x y X $.
    istsr.1 $e |- X = dom R $.
    $( The predicate is a toset.  (Contributed by FL, 1-Nov-2009.)  (Revised by
       Mario Carneiro, 22-Nov-2013.) $)
    istsr $p |- ( R e. TosetRel <->
        ( R e. PosetRel /\ ( X X. X ) C_ ( R u. `' R ) ) ) $=
      ( vr cv cdm cxp ccnv cun wss ctsr wceq dmeq eqtr4di sqxpeqd cnveq uneq12d
      cps id sseq12d df-tsr elrab2 ) DEZFZUDGZUCUCHZIZJBBGZAAHZIZJDARKUCALZUEUH
      UGUJUKUDBUKUDAFBUCAMCNOUKUCAUFUIUKSUCAPQTDUAUB $.

    $( The predicate is a toset.  (Contributed by FL, 1-Nov-2009.)  (Revised by
       Mario Carneiro, 22-Nov-2013.) $)
    istsr2 $p |- ( R e. TosetRel <->
        ( R e. PosetRel /\ A. x e. X A. y e. X ( x R y \/ y R x ) ) ) $=
      ( ctsr wcel cps cxp ccnv cun wss wa cv wbr wo wral istsr qfto anbi2i
      bitri ) CFGCHGZDDICCJKLZMUBANZBNZCOUEUDCOPBDQADQZMCDERUCUFUBABDDCSTUA $.

    $( A toset is a linear order.  (Contributed by Mario Carneiro,
       9-Sep-2015.) $)
    tsrlin $p |- ( ( R e. TosetRel /\ A e. X /\ B e. X ) ->
      ( A R B \/ B R A ) ) $=
      ( vx vy ctsr wcel wbr wo cv wral wa cps istsr2 wceq breq1 breq2 orbi12d
      simprbi rspc2v syl5com 3impib ) CHIZADIZBDIZABCJZBACJZKZUEFLZGLZCJZULUKCJ
      ZKZGDMFDMZUFUGNUJUECOIUPFGCDEPUAUOUJAULCJZULACJZKFGABDDUKAQUMUQUNURUKAULC
      RUKAULCSTULBQUQUHURUIULBACSULBACRTUBUCUD $.

    $( Two ways of saying a number is less than or equal to the maximum of two
       others.  (Contributed by Mario Carneiro, 9-Sep-2015.) $)
    tsrlemax $p |- ( ( R e. TosetRel /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
        ( A R if ( B R C , C , B ) <-> ( A R B \/ A R C ) ) ) $=
      ( wbr wo wb wcel wa wceq breq2 bibi1d wi pstr 3expib syl adantr expdimp
      cif ctsr w3a olc cps cdm cxp ccnv cun wss eqid istsr simplbi impancom idd
      jaod impbid2 wn orc tsrlin 3adant3r1 orcanai syldan ifbothda ) BCDGZACDGZ
      ABDGZVFHZIVGVHIAVECBUAZDGZVHIDUBJZAEJZBEJZCEJZUCZKZCBCVILVFVJVHCVIADMNBVI
      LVGVJVHBVIADMNVPVEKZVFVHVFVGUDVQVGVFVFVPVGVEVFVPVGVEVFVKVGVEKVFOZVOVKDUEJ
      ZVRVKVSDUFZVTUGDDUHUIUJDVTVTUKULUMZVSVGVEVFABCDPQRSTUNVQVFUOUPUQVPVEURZKZ
      VGVHVGVFUSWCVGVGVFWCVGUOVPWBCBDGZVFVGOVPVEWDVKVMVNVEWDHVLBCDEFUTVAVBVPVFW
      DVGVPVFWDVGVKVFWDKVGOZVOVKVSWEWAVSVFWDVGACBDPQRSTUNVCUPUQVD $.
  $}

  $( A toset is a poset.  (Contributed by Mario Carneiro, 9-Sep-2015.) $)
  tsrps $p |- ( R e. TosetRel -> R e. PosetRel ) $=
    ( ctsr wcel cps cdm cxp ccnv cun wss eqid istsr simplbi ) ABCADCAEZMFAAGHIA
    MMJKL $.

  $( The converse of a toset is a toset.  (Contributed by Mario Carneiro,
     3-Sep-2015.) $)
  cnvtsr $p |- ( R e. TosetRel -> `' R e. TosetRel ) $=
    ( ctsr wcel ccnv cps crn cxp cun wss tsrps cnvps syl cdm eqid istsr simprbi
    wceq psrn sqxpeqd wrel psrel dfrel2 sylib uneq2d eqtr2di 3sstr3d sylanbrc
    uncom df-rn ) ABCZADZECZAFZUMGZUKUKDZHZIUKBCUJAECZULAJZAKLUJAMZUSGZAUKHZUNU
    PUJUQUTVAIAUSUSNZOPUJUSUMUJUQUSUMQURAUSVBRLSUJUPUKAHVAUJUOAUKUJATZUOAQUJUQV
    CURAUALAUBUCUDUKAUHUEUFUKUMAUIOUG $.

  ${
    $d A x y $.  $d R x y $.
    $( Any subset of a totally ordered set is totally ordered.  (Contributed by
       FL, 24-Jan-2010.)  (Proof shortened by Mario Carneiro, 21-Nov-2013.) $)
    tsrss $p |- ( R e. TosetRel -> ( R i^i ( A X. A ) ) e. TosetRel ) $=
      ( vx vy cps wcel cv wbr wo cdm wral wa ctsr wss wi dmss ssralv mp2b sseli
      wb cxp cin psss inss1 ralimi syl inss2 ax-mp dmxpid sseqtri brinxp ancoms
      orbi12d syl2an ralbidva ralbiia sylib anim12i eqid istsr2 3imtr4i ) BEFZC
      GZDGZBHZVDVCBHZIZDBJZKZCVHKZLBAAUAZUBZEFZVCVDVLHZVDVCVLHZIZDVLJZKZCVQKZLB
      MFVLMFVBVMVJVSABUCVJVGDVQKZCVQKZVSVJVICVQKZWAVLBNZVQVHNZVJWBOBVKUDZVLBPZV
      ICVQVHQRVIVTCVQWCWDVIVTOWEWFVGDVQVHQRUEUFVTVRCVQVCVQFZVGVPDVQWGVCAFZVDAFZ
      VGVPTVDVQFVQAVCVQVKJZAVLVKNVQWJNBVKUGVLVKPUHAUIUJZSVQAVDWKSWHWILVEVNVFVOV
      CVDAABUKWIWHVFVOTVDVCAABUKULUMUNUOUPUQURCDBVHVHUSUTCDVLVQVQUSUTVA $.
  $}

$(
  @{
    @d r w x y z R @.  @d r w x y z X @.  @d r w x y z A @.
    spwval2.1 @e |- X = U. U. R @.
    @( Value of supremum under a weak ordering.  Read ` R supw A ` as "the
       ` R ` -supremum of ` A ` ".  ` U. U. R ` is the field of a relation
       ` R ` by ~ relfld .  Unlike ~ df-sup for strong orderings, the supremum
       exists iff ` R supw A ` belongs to the field.  (Contributed by NM,
       13-May-2008.)  (Revised by Mario Carneiro, 20-Nov-2013.) @)
    spwval2 @p |- ( ( R e. PosetRel /\ A e. V ) -> ( R supw A ) =
                    ( iota_ x e. X ( A. y e. A y R x /\
                      A. y e. X ( A. z e. A z R y -> x R y ) ) ) ) @=
      ( vr vw wcel cv wbr wral wi wa crio wceq cuni breq cps cspw co elex unieq
      unieqd eqtr4di ralbidv imbi12d raleqbidv anbi12d riotaeqbidv raleq imbi1d
      cvv riotabidv df-spw riotaex ovmpo sylan2 ) DFKEUAKDUOKEDUBUCBLZALZEMZBD
      NZCLZVAEMZCDNZVBVAEMZOZBGNZPZAGQZRDFUDIJEDUAUOVAVBILZMZBJLZNZVEVAVMMZCVON
      ZVBVAVMMZOZBVMSZSZNZPZAWBQVLUBVCBVONZVFCVONZVHOZBGNZPZAGQVMERZWDWIAWBGWJW
      BESZSGWJWAWKVMEUEUFHUGZWJVPWEWCWHWJVNVCBVOVAVBVMETUHWJVTWGBWBGWLWJVRWFVSV
      HWJVQVFCVOVEVAVMETUHVBVAVMETUIUJUKULVODRZWIVKAGWMWEVDWHVJVCBVODUMWMWGVIBG
      WMWFVGVHVFCVODUMUNUHUKUPJABCIUQVKAGURUSUT @.
  @}

  @{
    @d r w x y z R @.  @d r w x y X @.  @d w x y z A @.
    spwval.1 @e |- X = dom R @.
    @( Value of supremum under a weak ordering.  Read ` R supw A ` as "the
       ` R ` -supremum of ` A ` ".  ` U. U. R ` is the field of a relation
       ` R ` by ~ relfld .  Unlike ~ df-sup for strong orderings, the supremum
       exists iff ` R supw A ` belongs to the field.  (Contributed by NM,
       13-May-2008.)  (Revised by Mario Carneiro, 20-Nov-2013.) @)
    spwval @p |- ( ( R e. PosetRel /\ A e. V ) -> ( R supw A ) =
                    ( iota_ x e. X ( A. y e. A y R x /\
                      A. y e. X ( A. z e. A z R y -> x R y ) ) ) ) @=
      ( cps wcel wa cspw co cv wbr wral wi cuni crio wceq spwval2 psdmrn simpld
      eqid cdm crn eqtrid raleqdv anbi2d riotaeqbidv adantr eqtr4d ) EIJZDFJZKE
      DLMBNZANZEOBDPZCNUOEOCDPUPUOEOQZBERRZPZKZAUSSZUQURBGPZKZAGSZABCDEFUSUSUDU
      AUMVEVBTUNUMVDVAAGUSUMGEUEZUSHUMVFUSTEUFUSTEUBUCUGZUMVCUTUQUMURBGUSVGUHUI
      UJUKUL @.
  @}

  @{
    @d w x y z A @.  @d y z B @.  @d y z C @.  @d w x y z R @.  @d w x y X @.
    @d y U @.  @d y W @.
    spwmo.1 @e |- ( ph
         <-> ( A. y e. A y R x /\ A. y e. X ( A. z e. A z R y -> x R y ) ) ) @.
    @( A poset has at most one supremum.  (Contributed by NM, 13-May-2008.)
       (Revised by NM, 16-Jun-2017.) @)
    spwmo @p |- ( R e. PosetRel -> E* x e. X ph ) @=
      ( vw wcel cv wa wmo wbr wral wi weq breq1 breq2 ralbidv cps cbvralv rspcv
      wrmo wal impd im2anan9r psasym 3expib syl9 com13 exp43 com4r sylbi imp43
      imbi12d com3r imp com12 alrimivv anbi2i mobii eleq1 bitrdi imbi2d anbi12d
      an4s mo4 bitri sylibr df-rmo ) FUAJZBKZGJZALZBMZABGUDVLVNCKZVMFNZCEOZDKZV
      QFNZDEOZVMVQFNZPZCGOZLZLZIKZGJZVTWHFNZDEOZWBWHVQFNZPZCGOZLZLZLZBIQZPZIUEB
      UEZVPVLWSBIWQVLWRVNWIWFWOVLWRPZVNWILZWFWOLZXAXCVLXBWRVSWEWKWNVLXBWRPPZVSV
      TVMFNZDEOZWEWKWNXDPPPVRXECDEVQVTVMFRUBWEWKWNXFXDWEWKWNXFXDXBVLWEWKLZWNXFL
      ZLZWRXBXIVMWHFNZWHVMFNZLVLWRWIXGXJVNXHXKWIWEWKXJWDWKXJPCWHGCIQZWBWKWCXJXL
      WAWJDEVQWHVTFSTVQWHVMFSUPUCUFVNWNXFXKWMXFXKPCVMGCBQZWBXFWLXKXMWAXEDEVQVMV
      TFSTVQVMWHFSUPUCUFUGVLXJXKWRVMWHFUHUIUJUKULUMUNUOUQURVGUSUTVPWGBMWTVOWGBA
      WFVNHVAVBWGWPBIWRVNWIWFWOVMWHGVCWRVSWKWEWNWRVSVQWHFNZCEOWKWRVRXNCEVMWHVQF
      STXNWJCDEVQVTWHFRUBVDWRWDWMCGWRWCWLWBVMWHVQFRVETVFVFVHVIVJABGVKVJ @.

    @( A supremum is unique.  (Contributed by NM, 15-May-2008.) @)
    spweu @p |- ( ( R e. PosetRel /\ E. x e. X ph ) -> E! x e. X ph ) @=
      ( wrex cps wcel wreu wa wrmo spwmo anim2i reu5 sylibr ancoms ) ABGIZFJKZA
      BGLZTUAMTABGNZMUBUAUCTABCDEFGHOPABGQRS @.

    @( Property of supremum defining condition for an unordered pair.
       (Contributed by NM, 24-Jun-2008.) @)
    spwpr2 @p |- ( ( ( R e. T /\ A = { B , C } ) /\ ( B e. U /\ C e. W ) )
       -> ( ph <->
     ( ( B R x /\ C R x ) /\ A. y e. X ( ( B R y /\ C R y ) -> x R y ) ) ) ) @=
      ( cv wbr wral wi wa wcel breq1 cpr wceq wb ralprg sylan9bb imbi1d ralbidv
      raleq anbi12d adantll bitrid ) ACNZBNZHOZCEPZDNZULHOZDEPZUMULHOZQZCLPZRZH
      ISZEFGUAZUBZRFJSGKSRZRFUMHOZGUMHOZRZFULHOZGULHOZRZUSQZCLPZRZMVEVFVBVOUCVC
      VEVFRZUOVIVAVNVEUOUNCVDPVFVIUNCEVDUHUNVGVHCFGJKULFUMHTULGUMHTUDUEVPUTVMCL
      VPURVLUSVEURUQDVDPVFVLUQDEVDUHUQVJVKDFGJKUPFULHTUPGULHTUDUEUFUGUIUJUK @.
  @}

  @{
    @d x y z A @.  @d x y z R @.  @d x y X @.
    spwex.1 @e |- X = dom R @.
    spwex.2 @e |- ( ph <->
         ( A. y e. A y R x /\ A. y e. X ( A. z e. A z R y -> x R y ) ) ) @.
    @( A supremum exists iff ` R supw A ` belongs to the domain of ` R ` .
       (Contributed by NM, 15-May-2008.)  (Revised by Mario Carneiro,
       20-Nov-2013.) @)
    spwex @p |- ( ( R e. PosetRel /\ A e. V )
               -> ( E. x e. X ph <-> ( R supw A ) e. X ) ) @=
      ( cps wcel wa wreu cv wbr wral wb cvv adantr wi crio wrex cspw reubii cdm
      co dmexg eqeltrid riotaclbgBAD syl bitrid spweu reurex impbid1 spwval
      eleq1d
      ex 3bitr4d ) FKLZEGLZMZABHNZCOZBOZFPCEQDOVDFPDEQVEVDFPUACHQMZBHUBZHLZABHU
      CZFEUDUGZHLUTVCVHRVAVCVFBHNZUTVHAVFBHJUEUTHSLVKVHRUTHFUFSIFKUHUIVFBHSUJUK
      ULTUTVIVCRVAUTVIVCUTVIVCABCDEFHJUMURABHUNUOTVBVJVGHBCDEFGHIUPUQUS @.

    @( Closure of a supremum.  (Contributed by NM, 15-May-2008.)  (Revised by
       Mario Carneiro, 20-Nov-2013.) @)
    spwcl @p |- ( ( R e. PosetRel /\ A e. V /\ E. x e. X ph )
           -> ( R supw A ) e. X ) @=
      ( cps wcel wrex cspw co spwex biimp3a ) FKLEGLABHMFENOHLABCDEFGHIJPQ @.
  @}

  @{
    @d x y z A @.  @d x y z B @.  @d x y z C @.  @d x y z R @.  @d x y z X @.
    spwpr4.1 @e |- X = dom R @.
    @( Supremum of an unordered pair.  (Contributed by NM, 7-Jul-2008.)
       (Revised by Mario Carneiro, 20-Nov-2013.) @)
    spwpr4 @p |- ( ( R e. PosetRel /\ ( A R C /\ B R C ) /\
   A. x e. X ( ( A R x /\ B R x ) -> C R x ) ) -> ( R supw { A , B } ) = C ) @=
      ( vy vz wcel wa wbr cv wi wral wceq 3adant3 cvv wb syl2anc cps cspw simpl
      cpr co crn wrel psrel relelrn sylan psrn adantr eleqtrrd adantrr jca crio
     w3a simp1l prex spwval sylancl simpll brrelex1 ex anim12d syl adantlr eqid
      biid spwpr2 mpanl2 riotabidv 3simpc wreu simp1r wrex breq2 anbi12d imbi2d
      imp breq1 ralbidv rspcev 3impb 3adant1l rexbidv mpbird spweu mpbid riota2
      reubidv 3eqtrd syld3an1 ) EUAJZDFJZKZBDELZCDELZKZWNBAMZELCWTELKZDWTELZNZA
      FOZEBCUDZUBUEZDPWNWSWPXDWNWSKWNWOWNWSUCWNWQWOWRWNWQKDEUFZFWNEUGZWQDXGJEUH
      ZBDEUIUJWNFXGPWQEFGUKULUMUNUOQWPWSXDUQZXFWTHMZELAXEOIMWTELIXEOXKWTELZNAFO
      KZHFUPZBXKELZCXKELZKZXAXLNZAFOZKZHFUPZDXJWNXERJXFXNPWNWOWSXDURZBCUSHAIXEE
      RFGUTVAWPWSXNYAPXDWPWSKZXMXTHFYCWNBRJZCRJZKZXMXTSZWNWOWSVBWNWSYFWOWNWSYFW
      NXHWSYFNXIXHWQYDWRYEXHWQYDBDEVCVDXHWRYECDEVCVDVEVFVTVGWNXEXEPYFYGXEVHXMHA
      IXEBCEUARRFXMVIZVJVKTZVLQXJWSXDKZYADPZWPWSXDVMXJWOXTHFVNZYJYKSWNWOWSXDVOX
      JXMHFVNZYLXJWNXMHFVPZYMYBXJYNXTHFVPZWOWSXDYOWNWOWSXDYOXTYJHDFXKDPZXQWSXSX
      DYPXOWQXPWRXKDBEVQXKDCEVQVRYPXRXCAFYPXLXBXAXKDWTEWAVSWBVRZWCWDWEWPWSYNYOS
      XDYCXMXTHFYIWFQWGXMHAIXEEFYHWHTWPWSYMYLSXDYCXMXTHFYIWKQWIXTYJHFDYQWJTWIWL
      WM @.
  @}

  @{
    @d x A @.  @d x B @.  @d x R @.
    @( Supremum of an unordered pair of comparable elements.  (Contributed by
       NM, 7-Jul-2008.) @)
    spwpr4c @p |- ( ( R e. PosetRel /\ A R B ) -> ( R supw { A , B } ) = B ) @=
      ( vx cps wcel wbr wa cv wi cdm wral cpr cspw co wceq simpl simpr crn wrel
      psrel relelrn sylan eqid adantr eleqtrrd psref syldan rgenw a1i syl121anc
      psrn spwpr4 ) CEFZABCGZHZUNUOBBCGZADIZCGZBURCGZHUTJZDCKZLZCABMNOBPUNUOQUN
      UORUNUOBVBFUQUPBCSZVBUNCTUOBVDFCUAABCUBUCUNVBVDPUOCVBVBUDZULUEUFBCVBVEUGU
      HVCUPVADVBUSUTRUIUJDABBCVBVEUMUK @.
  @}

  @{
    @d x y A @.  @d y B @.  @d r x y R @.  @d r x y X @.
    isla.1 @e |- X = dom R @.
    @( The predicate "is a lattice" i.e. a poset in which any two elements have
       upper and lower bounds.  (Contributed by NM, 12-Jun-2008.) @)
    isla @p |- ( R e. LatRel <-> ( R e. PosetRel /\ A. x e. X A. y e. X
      ( ( R supw { x , y } ) e. X /\ ( R infw { x , y } ) e. X ) ) ) @=
      ( vr cv cpr cspw co cdm wcel cinf wa wral cps cla oveq1 eleq12d raleqbidv
      wceq dmeq eqtr4di anbi12d df-lar elrab2 ) FGZAGBGHZIJZUGKZLZUGUHMJZUJLZNZ
      BUJOZAUJOCUHIJZDLZCUHMJZDLZNZBDOZADOFCPQUGCUAZUOVAAUJDVBUJCKDUGCUBEUCZVBU
      NUTBUJDVCVBUKUQUMUSVBUIUPUJDUGCUHIRVCSVBULURUJDUGCUHMRVCSUDTTABFUEUF @.

    @( Closure of the supremum (join) of two lattice elements.  (Contributed by
       NM, 12-Jun-2008.) @)
    laspwcl @p |- ( ( R e. LatRel /\ A e. X /\ B e. X )
                -> ( R supw { A , B } ) e. X ) @=
      ( vx vy cla wcel cpr cspw co cv wral wa cps ralimi wceq oveq2d eleq1d
      cinf isla simpl adantl sylbi preq1 preq2 rspc2v mpan9 3impb ) CHIZADIZBDI
      ZCABJZKLZDIZUKCFMZGMZJZKLZDIZGDNZFDNZULUMOUPUKCPIZVACUSUALDIZOZGDNZFDNZOV
      CFGCDEUBVHVCVDVGVBFDVFVAGDVAVEUCQQUDUEVAUPCAURJZKLZDIFGABDDUQARZUTVJDVKUS
      VICKUQAURUFSTURBRZVJUODVLVIUNCKURBAUGSTUHUIUJ @.

    @( Closure of the infimum (meet) of two lattice elements.  (Contributed by
       NM, 20-Jun-2008.) @)
    lanfwcl @p |- ( ( R e. LatRel /\ A e. X /\ B e. X )
                -> ( R infw { A , B } ) e. X ) @=
      ( vx vy cla wcel cpr cinf co cv wral wa cps ralimi wceq oveq2d eleq1d
      cspw isla simpr adantl sylbi preq1 preq2 rspc2v mpan9 3impb ) CHIZADIZBDI
      ZCABJZKLZDIZUKCFMZGMZJZKLZDIZGDNZFDNZULUMOUPUKCPIZCUSUALDIZVAOZGDNZFDNZOV
      CFGCDEUBVHVCVDVGVBFDVFVAGDVEVAUCQQUDUEVAUPCAURJZKLZDIFGABDDUQARZUTVJDVKUS
      VICKUQAURUFSTURBRZVJUODVLVIUNCKURBAUGSTUHUIUJ @.
  @}

  @{
    @d x y R @.
    @( A lattice is a poset.  (Contributed by NM, 12-Jun-2008.) @)
    laps @p |- ( R e. LatRel -> R e. PosetRel ) @=
      ( vx vy cla wcel cps cv cpr cspw co cdm cinf wa wral eqid isla simplbi )
      ADEAFEABGCGHZIJAKZEARLJSEMCSNBSNBCASSOPQ @.
  @}
$)

  $( The domain of ` <_ ` is ` RR* ` .  (Contributed by FL, 2-Aug-2009.)
     (Revised by Mario Carneiro, 4-May-2015.) $)
  ledm $p |- RR* = dom <_ $=
    ( vx cxr cle cdm cv wcel wbr xrleid lerel releldmi syl cxp wss lerelxr dmss
    ssriv ax-mp dmxpss sstri eqssi ) BCDZABUAAEZBFUBUBCGUBUAFUBHUBUBCIJKPUABBLZ
    DZBCUCMUAUDMNCUCOQBBRST $.

  $( The range of ` <_ ` is ` RR* ` .  (Contributed by FL, 2-Aug-2009.)
     (Revised by Mario Carneiro, 3-Sep-2015.) $)
  lern $p |- RR* = ran <_ $=
    ( vx cxr cle crn wcel wbr xrleid lerel relelrni syl ssriv cxp lerelxr rnssi
    cv rnxpss sstri eqssi ) BCDZABSAOZBETTCFTSETGTTCHIJKSBBLZDBCUAMNBBPQR $.

  $( The field of the 'less or equal to' relationship on the extended real.
     (Contributed by FL, 2-Aug-2009.)  (Revised by Mario Carneiro,
     4-May-2015.) $)
  lefld $p |- RR* = U. U. <_ $=
    ( cle cuni cdm crn cun wrel wceq lerel relfld ax-mp ledm lern uneq12i unidm
    cxr 3eqtr2ri ) ABBZACZADZEZOOEOAFQTGHAIJOROSKLMONP $.

  ${
    $d x y z $.
    $( The "less than or equal to" relationship on the extended reals is a
       toset.  (Contributed by FL, 2-Aug-2009.)  (Revised by Mario Carneiro,
       3-Sep-2015.) $)
    letsr $p |- <_ e. TosetRel $=
      ( vx vy vz cle wcel cxr wss cuni wceq cv wbr wa wal lerelxr simpld simprd
      w3a brel adantl wb ctsr cps cxp ccnv cun wrel ccom cin cid cres wi adantr
      lerel 3jca xrletr mpcom ax-gen mpbir asymref simpr xrletri3 sylan2 mpbird
      gen2 cotr ex xrleid jca breq2 breq1 anbi12d syl5ibcom impbid lefld eqcomi
      alrimiv eleq2s mprgbir cvv xrex xpex ssexi isps ax-mp mpbir3an wo xrletri
      wral rgen2 qfto ledm istsr mpbir2an ) DUAEDUBEZFFUCZDDUDZUEGZWNDUFZDDUGDG
      ZDWPUHUIDHHZUJIZUMWSAJZBJZDKZXCCJZDKZLZXBXEDKZUKZCMZBMAMXJABXICXBFEZXCFEZ
      XEFEZQXGXHXGXKXLXMXGXKXLXDXKXLLXFXBXCFFDNRULZOXGXKXLXNPXFXMXDXFXLXMXCXEFF
      DNRPSUNXBXCXEUOUPUQVDABCDVEURXAXDXCXBDKZLZXBXCIZTZBMZAWTABDUSXSXBFWTXKXRB
      XKXPXQXKXPXQXKXPLXQXPXKXPUTXPXKXLXQXPTXOXLXDXOXLXKXCXBFFDNROSXBXCVAVBVCVF
      XKXBXBDKZXTLXQXPXKXTXTXBVGZYAVHXQXTXDXTXOXBXCXBDVIXBXCXBDVJVKVLVMVPFWTVNV
      OVQVRDVSEWNWRWSXAQTDWOFFVTVTWANWBVSDWCWDWEWQXDXOWFZBFWHAFWHYBABFFXBXCWGWI
      ABFFDWJURDFWKWLWM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Directed sets, nets
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c DirRel $.
  $( Extend class notation with the class of directed sets. $)
  cdir $a class DirRel $.

  $c tail $.
  $( Extend class notation with the tail function for directed sets. $)
  ctail $a class tail $.

  $( Define the class of directed sets (the order relation itself is sometimes
     called a direction, and a directed set is a set equipped with a
     direction).  (Contributed by Jeff Hankins, 25-Nov-2009.) $)
  df-dir $a |- DirRel = { r | ( ( Rel r /\ ( _I |` U. U. r ) C_ r ) /\
     ( ( r o. r ) C_ r /\ ( U. U. r X. U. U. r ) C_ ( `' r o. r ) ) ) } $.

  ${
    $d r x $.
    $( Define the tail function for directed sets.  (Contributed by Jeff
       Hankins, 25-Nov-2009.) $)
    df-tail $a |- tail = ( r e. DirRel |->
                  ( x e. U. U. r |-> ( r " { x } ) ) ) $.
  $}

  ${
    $d r A $.  $d r R $.
    isdir.1 $e |- A = U. U. R $.
    $( A condition for a relation to be a direction.  (Contributed by Jeff
       Hankins, 25-Nov-2009.)  (Revised by Mario Carneiro, 22-Nov-2013.) $)
    isdir $p |- ( R e. V -> ( R e. DirRel <-> ( ( Rel R /\ ( _I |` A ) C_ R )
                 /\ ( ( R o. R ) C_ R /\ ( A X. A ) C_ ( `' R o. R ) ) ) ) ) $=
      ( vr cv wrel cid cuni cres wss wa ccom cxp ccnv cdir wceq sseq12d anbi12d
      coeq12d releq unieq unieqd eqtr4di reseq2d id sqxpeqd cnveq df-dir elab2g
      ) EFZGZHUKIZIZJZUKKZLZUKUKMZUKKZUNUNNZUKOZUKMZKZLZLBGZHAJZBKZLZBBMZBKZAAN
      ZBOZBMZKZLZLEBPCUKBQZUQVHVDVOVPULVEUPVGUKBUAVPUOVFUKBVPUNAHVPUNBIZIAVPUMV
      QUKBUBUCDUDZUEVPUFZRSVPUSVJVCVNVPURVIUKBVPUKBUKBVSVSTVSRVPUTVKVBVMVPUNAVR
      UGVPVAVLUKBUKBUHVSTRSSEUIUJ $.
  $}

  $( A direction is a relation.  (Contributed by Jeff Hankins, 25-Nov-2009.)
     (Revised by Mario Carneiro, 22-Nov-2013.) $)
  reldir $p |- ( R e. DirRel -> Rel R ) $=
    ( cdir wcel wrel cid cuni cres wss ccom cxp ccnv wa eqid isdir ibi simplld
    ) ABCZADZEAFFZGAHZAAIAHSSJAKAIHLZQRTLUALSABSMNOP $.

  $( A direction's domain is equal to its field.  (Contributed by Jeff Hankins,
     25-Nov-2009.)  (Revised by Mario Carneiro, 22-Nov-2013.) $)
  dirdm $p |- ( R e. DirRel -> dom R = U. U. R ) $=
    ( cdir wcel cdm cuni wss crn cun ssun1 dmrnssfld sstri a1i cres dmresi wrel
    cid ccom cxp ccnv wa eqid isdir ibi simplrd dmss syl eqsstrrid eqssd ) ABCZ
    ADZAEEZUJUKFUIUJUJAGZHUKUJULIAJKLUIUKPUKMZDZUJUKNUIUMAFZUNUJFUIAOZUOAAQAFUK
    UKRASAQFTZUIUPUOTUQTUKABUKUAUBUCUDUMAUEUFUGUH $.

  ${
    dirref.1 $e |- X = dom R $.
    $( A direction is reflexive.  (Contributed by Jeff Hankins, 25-Nov-2009.)
       (Revised by Mario Carneiro, 22-Nov-2013.) $)
    dirref $p |- ( ( R e. DirRel /\ A e. X ) -> A R A ) $=
      ( cdir wcel cid cres wbr cuni cdm dirdm eqtrid reseq2d wrel wss ccom eqid
      cxp wa ccnv isdir ibi simplrd eqsstrd ssbrd wb resieq anidms mpbiri impel
      wceq ) BEFZAAGCHZIZAABIACFZUMUNBAAUMUNGBJJZHZBUMCUQGUMCBKUQDBLMNUMBOZURBP
      ZBBQBPUQUQSBUABQPTZUMUSUTTVATUQBEUQRUBUCUDUEUFUPUOAAULZARUPUOVBUGCAAUHUIU
      JUK $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z R $.
    $( A direction is transitive.  (Contributed by Jeff Hankins, 25-Nov-2009.)
       (Revised by Mario Carneiro, 22-Nov-2013.) $)
    dirtr $p |- ( ( ( R e. DirRel /\ C e. V ) /\ ( A R B /\ B R C ) )
               -> A R C ) $=
      ( vx vy vz cdir wcel wbr wa cvv wi cv wal wss wceq wb breq12 wrel anim12d
      reldir brrelex1 ex syl w3a ccom cid cuni cres cxp ccnv eqid isdir simprld
      ibi cotr sylib 3adant3 3adant1 anbi12d 3adant2 imbi12d spc3gv syl5 3expia
      com4t mpdd imp31 an32s ) DIJZABDKZBCDKZLZCEJZACDKZVLVOVPVQVLVOAMJZBMJZLZV
      PVQNVLDUAZVOVTNDUCWAVMVRVNVSWAVMVRABDUDUEWAVNVSBCDUDUEUBUFVTVPVLVOVQVRVSV
      PVLVOVQNZNVLFOZGOZDKZWDHOZDKZLZWCWFDKZNZHPGPFPZVRVSVPUGWBVLDDUHDQZWKVLWAU
      IDUJUJZUKDQLZWLWMWMULDUMDUHQZVLWNWLWOLLWMDIWMUNUOUQUPFGHDURUSWJWBFGHABCMM
      EWCARZWDBRZWFCRZUGZWHVOWIVQWSWEVMWGVNWPWQWEVMSWRWCAWDBDTUTWQWRWGVNSWPWDBW
      FCDTVAVBWPWRWIVQSWQWCAWFCDTVCVDVEVFVGVHVIVJVK $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z R $.  $d x y z X $.
    dirge.1 $e |- X = dom R $.
    $( For any two elements of a directed set, there exists a third element
       greater than or equal to both.  Note that this does not say that the two
       elements have a _least_ upper bound.  (Contributed by Jeff Hankins,
       25-Nov-2009.)  (Revised by Mario Carneiro, 22-Nov-2013.) $)
    dirge $p |- ( ( R e. DirRel /\ A e. X /\ B e. X )
              -> E. x e. X ( A R x /\ B R x ) ) $=
      ( vy vz cdir wcel cv wbr wa wex cuni eleq2d wral ccom wss wceq wrex dirdm
      cdm eqtrid anbi12d cxp ccnv wrel cid cres isdir simprrd codir sylib breq1
      eqid ibi anbi1d exbidv anbi2d rspc2v syl5com sylbid crn reldir relelrn ex
      sylan cun ssun2 dmrnssfld sstri sseqtrrid sseld syld adantrd ancrd eximdv
      df-rex imbitrrdi 3impib ) DIJZBEJZCEJZBAKZDLZCWEDLZMZAEUAZWBWCWDMZWHANZWI
      WBWJBDOOZJZCWLJZMZWKWBWCWMWDWNWBEWLBWBEDUCZWLFDUBUDZPWBEWLCWQPUEWBGKZWEDL
      ZHKZWEDLZMZANZHWLQGWLQZWOWKWBWLWLUFDUGDRSZXDWBDUHZUIWLUJDSMZDDRDSZXEWBXGX
      HXEMMWLDIWLUPUKUQULGHAWLWLDUMUNXCWKWFXAMZANGHBCWLWLWRBTZXBXIAXJWSWFXAWRBW
      EDUOURUSWTCTZXIWHAXKXAWGWFWTCWEDUOUTUSVAVBVCWBWKWEEJZWHMZANWIWBWHXMAWBWHX
      LWBWFXLWGWBWFWEDVDZJZXLWBWFXOWBXFWFXODVEBWEDVFVHVGWBXNEWEWBWLXNEXNWPXNVIW
      LXNWPVJDVKVLWQVMVNVOVPVQVRWHAEVSVTVOWA $.
  $}

  $( A totally ordered set is a directed set.  (Contributed by Jeff Hankins,
     25-Nov-2009.)  (Revised by Mario Carneiro, 22-Nov-2013.) $)
  tsrdir $p |- ( A e. TosetRel -> A e. DirRel ) $=
    ( ctsr wcel cdir wrel cid cuni cres wss ccom cxp ccnv cps syl jca wceq eqid
    wa eqsstrrid eqsstrrd tsrps psrel cin psref2 inss1 eqsstrrdi cdm crn psdmrn
    pstr2 simpld sqxpeqd cun istsr simprbi relcoi2 cnvresid cnvss coss1 relcoi1
    relcnv ax-mp relcnvfld reseq2d coss2 unssd sstrd isdir mpbir2and ) ABCZADCA
    EZFAGGZHZAIZRAAJAIZVLVLKZALZAJZIZRVJVKVNVJAMCZVKAUAZAUBNZVJVTVNWAVTVMAVQUCA
    AUDAVQUEUFNZOVJVOVSVJVTVOWAAUJNVJVPAUGZWDKZVRVJWDVLVJWDVLPZAUHVLPZVJVTWFWGR
    WAAUINUKULVJWEAVQUMZVRVJVTWEWHIAWDWDQUNUOVJAVQVRVJAVMAJZVRVJVKWIAPWBAUPNVJV
    MVQIWIVRIVJVMVMLZVQVLUQVJVNWJVQIWCVMAURNSVMVQAUSNTVJVQVQFVQGGZHZJZVRVQEWMVQ
    PAVAVQUTVBVJWLAIWMVRIVJWLVMAVJVLWKFVJVKVLWKPWBAVCNVDWCTWLAVQVENSVFVGTOVLABV
    LQVHVI $.


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Chains
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c Chain $.

  $( Extend class notation with the class of (finite) chains. $)
  cchn $a class ( .< Chain A ) $.

  ${
    $d A c n $.  $d .< c n $.
    $( Define the class of (finite) chains.  A chain is defined to be a
       sequence of objects, where each object is less than the next one in the
       sequence.  The term "chain" is usually used in order theory.  In the
       context of algebra, chains are often called "towers", for example for
       fields, or "series", for example for subgroup or subnormal series.
       (Contributed by Thierry Arnoux, 19-Jun-2025.) $)
    df-chn $a |- ( .< Chain A ) = { c e. Word A |
        A. n e. ( dom c \ { 0 } ) ( c ` ( n - 1 ) ) .< ( c ` n ) } $.
  $}

  ${
    $d .< c n $.  $d A c n $.  $d C c n $.  $d c ph $.  $d N n $.
    $( Property of being a chain.  (Contributed by Thierry Arnoux,
       19-Jun-2025.) $)
    ischn $p |- ( C e. ( .< Chain A ) <-> ( C e. Word A
             /\ A. n e. ( dom C \ { 0 } ) ( C ` ( n - 1 ) ) .< ( C ` n ) ) ) $=
      ( vc cv c1 cmin co cfv wbr cdm cc0 csn cdif wral cword cchn wceq fveq1
      dmeq difeq1d breq12d raleqbidv df-chn elrab2 ) DFZGHIZEFZJZUGUIJZCKZDUILZ
      MNZOZPUHBJZUGBJZCKZDBLZUNOZPEBAQACRUIBSZULURDUOUTVAUMUSUNUIBUAUBVAUJUPUKU
      QCUHUIBTUGUIBTUCUDACDEUEUF $.

    chnwrd.1 $e |- ( ph -> C e. ( .< Chain A ) ) $.
    $( A chain is an ordered sequence, i.e. a word.  (Contributed by Thierry
       Arnoux, 19-Jun-2025.) $)
    chnwrd $p |- ( ph -> C e. Word A ) $=
      ( vn cchn wcel cword cv c1 cmin co cfv wbr cdm cc0 csn cdif wral simplbi
      ischn syl ) ACBDGHZCBIHZEUDUEFJZKLMCNUFCNDOFCPQRSTBCDFUBUAUC $.

    ${
      chnltm1.2 $e |- ( ph -> N e. ( dom C \ { 0 } ) ) $.
      $( Basic property of a chain.  (Contributed by Thierry Arnoux,
         19-Jun-2025.) $)
      chnltm1 $p |- ( ph -> ( C ` ( N - 1 ) ) .< ( C ` N ) ) $=
        ( vn cv c1 cmin co cfv wbr cdm cc0 csn cdif wceq wcel fvoveq1 wral cchn
        fveq2 breq12d cword wa ischn sylib simprd rspcdva ) AHIZJKLCMZULCMZDNZE
        JKLCMZECMZDNHCOPQRZEULESUMUPUNUQDULEJCKUAULECUDUEACBUFTZUOHURUBZACBDUCT
        USUTUGFBCDHUHUIUJGUK $.
    $}

    ${
      $d L n $.  $d n ph $.
      pfxchn.2 $e |- ( ph -> L e. ( 0 ... ( # ` C ) ) ) $.
      $( A prefix of a chain is still a chain.  (Contributed by Thierry Arnoux,
         19-Jun-2025.) $)
      pfxchn $p |- ( ph -> ( C prefix L ) e. ( .< Chain A ) ) $=
        ( vn co wcel c1 cmin cfv cdm cc0 syl adantr chash cfzo wceq cpfx cv wbr
        cword csn cdif wral cchn chnwrd pfxcl wa cfz cuz wss elfzuz3 3syl simpr
        fzoss2 eldifad pfxlen syl2anc eqcomd wrdfd fdmd eleqtrd sseldd eleqtrrd
        eqidd wne eldifsni eldifsnd chnltm1 elfzelzd fzossrbm1 fzom1ne1 syl3anc
        cz pfxfv 3brtr4d ralrimiva ischn sylanbrc ) ACEUAIZBUDZJZHUBZKLIZWCMZWF
        WCMZDUCZHWCNZOUEZUFZUGWCBDUHZJACWDJZWEABCDFUIZBCEUJPZAWJHWMAWFWMJZUKZWG
        CMZWFCMZWHWIDWSBCDWFACWNJWRFQWSWFCNZOWSWFOCRMZSIZXBWSOESIZXDWFWSEOXCULI
        JZXCEUMMJXEXDUNAXFWRGQZEOXCUOEOXCURUPWSWFWKXEWSWFWKWLAWRUQZUSWSXEBWCWSB
        EWCWSWCRMZEWSWOXFXIETAWOWRWPQZXGBCEUTVAVBAWEWRWQQVCVDVEZVFWSXDBCWSBXCCW
        SXCVHXJVCVDVGWSWRWFOVIZXHWFWKOVJPZVKVLWSWOXFWGXEJWHWTTXJXGWSOEKLISIZXEW
        GWSEVQJXNXEUNWSEOXCXGVMEVNPWSWFXEJZXLWGXNJXKXMWFOEVOVAVFWGEBCVRVPWSWOXF
        XOWIXATXJXGXKWFEBCVRVPVSVTBWCDHWAWB $.
    $}
  $}

  ${
    $d .< z n $.  $d ph z n $.  $d A z n $.  $d x z n $.
    nfchnd.1 $e |- ( ph -> F/_ x .< ) $.
    nfchnd.2 $e |- ( ph -> F/_ x A ) $.
    $( Bound-variable hypothesis builder for chain collection constructor.
       (Contributed by Ender Ting, 20-Jan-2026.) $)
    nfchnd $p |- ( ph -> F/_ x ( .< Chain A ) ) $=
      ( vn vz cv wral wcel wa cn0 nfcvd wss nfcv nfraldw nfxfrd nfand nfcxfrd
      cchn c1 cmin co cfv wbr cdm cc0 csn cdif cword crab df-chn cab df-rab nfv
      wnfc wnf cfzo wf wrex df-word wfn crn df-f wfun wceq df-fn wrel ccnv ccom
      cid df-fun cvv cxp df-rel dfss3f a1i nfcrd nfvd nfrexdw nfabdw nfcr nfbrd
      syl ) ABCDUAGIZUBUCUDHIZUEZWFWGUEZDUFZGWGUGZUHUIUJZJZHCUKZULZCDGHUMABWOWG
      WNKZWMLZHUNWMHWNUOAWQBHAHUPZAWPWMBABWNUQWPBURABWNUHWFUSUDZCWGUTZGMVAZHUNH
      CGVBAXABHWRAWTBGMAGUPZABMNWTWGWSVCZWGVDZCOZLABWSCWGVEAXCXEBXCWGVFZWKWSVGZ
      LABWGWSVHAXFXGBXFWGVIZWGWGVJVKVLOZLABWGVMAXHXIBXHWGVNVNVOZOZABWGVPXKWFXJK
      ZGWGJABGWGXJGWGPGXJPVQAXLBGWGXBBWGUQABWGPVRABGXJABXJNVSQRRAXIBVTSRAXGBVTS
      RXEWFCKZGXDJABGXDCGXDPGCPVQAXMBGXDXBABXDNABGCFVSQRSRWAWBTBHWNWCWEAWJBGWLX
      BABWLNABWHWIDABWHNEABWINWDQSWBTT $.
  $}

  ${
    $d .< x c $.  $d R x c $.  $d A x c $.  $d B x c $.

    $( Equality theorem for chains.  (Contributed by Ender Ting,
       17-Jan-2026.) $)
    chneq1 $p |- ( .< = R -> ( .< Chain A ) = ( R Chain A ) ) $=
      ( vx vc wceq cv c1 cmin co cfv wbr cdm cc0 csn cdif wral crab cchn df-chn
      cword breq ralbidv rabbidv 3eqtr4g ) CBFZDGZHIJEGZKZUGUHKZCLZDUHMNOPZQZEA
      UAZRUIUJBLZDULQZEUNRACSABSUFUMUPEUNUFUKUODULUIUJCBUBUCUDACDETABDETUE $.

    $( Equality theorem for chains.  (Contributed by Ender Ting,
       17-Jan-2026.) $)
    chneq2 $p |- ( A = B -> ( .< Chain A ) = ( .< Chain B ) ) $=
      ( vx vc wceq cv c1 cmin cfv wbr cdm cc0 csn cdif cword crab cchn df-chn
      co wral wrdeq rabeq syl 3eqtr4g ) ABFZDGZHITEGZJUGUHJCKDUHLMNOUAZEAPZQZUI
      EBPZQZACRBCRUFUJULFUKUMFABUBUIEUJULUCUDACDESBCDESUE $.

    $( Equality theorem for chains.  (Contributed by Ender Ting,
       17-Jan-2026.) $)
    chneq12 $p |- ( ( .< = R /\ A = B ) -> ( .< Chain A ) = ( R Chain B ) ) $=
      ( wceq cchn chneq1 chneq2 sylan9eq ) DCEABEADFACFBCFACDGABCHI $.

    $( Chains under a relation are also chains under any superset relation.
       (Contributed by Ender Ting, 20-Jan-2026.) $)
    chnrss $p |- ( .< C_ R -> ( .< Chain A ) C_ ( R Chain A ) ) $=
      ( vx vc wss cchn cv cword wcel c1 cmin co cfv wbr cdm cc0 wral wa ischn
      csn cdif ssbr ralimdv anim2d 3imtr4g ssrdv ) CBFZDACGZABGZUHDHZAIJZEHZKLM
      UKNZUMUKNZCOZEUKPQUAUBZRZSULUNUOBOZEUQRZSUKUIJUKUJJUHURUTULUHUPUSEUQCBUNU
      OUCUDUEAUKCETAUKBETUFUG $.

    $( Chains with an alphabet are also chains with any superset alphabet.
       (Contributed by Ender Ting, 20-Jan-2026.) $)
    chndss $p |- ( A C_ B -> ( .< Chain A ) C_ ( .< Chain B ) ) $=
      ( vx vc wss cchn cv cword wcel c1 cmin co cfv wbr cdm cc0 csn wa ischn
      cdif wral sswrd sseld anim1d 3imtr4g ssrdv ) ABFZDACGZBCGZUHDHZAIZJZEHZKL
      MUKNUNUKNCOEUKPQRUAUBZSUKBIZJZUOSUKUIJUKUJJUHUMUQUOUHULUPUKABUCUDUEAUKCET
      BUKCETUFUG $.

    $( Subset theorem for chains.  (Contributed by Ender Ting, 20-Jan-2026.) $)
    chnrdss $p |- ( ( .< C_ R /\ A C_ B ) -> ( .< Chain A ) C_ ( R Chain B ) )
      $=
      ( wss cchn chnrss chndss sstr syl2an ) DCEADFZACFZELBCFZEKMEABEACDGABCHKL
      MIJ $.
  $}

  ${
    $d .< x $.  $d A x $.

    $( Chains with a set given for range form a set.  (Contributed by Ender
       Ting, 21-Nov-2024.)  (Revised by Ender Ting, 17-Jan-2026.) $)
    chnexg $p |- ( A e. V -> ( .< Chain A ) e. _V ) $=
      ( vx wcel cchn cword wss cvv wa wrdexg cv id chnwrd ssriv jctil ssexg syl
      ) ACEZABFZAGZHZUAIEZJTIESUCUBACKDTUADLZTEZAUDBUEMNOPTUAIQR $.

    $( Empty set is an increasing chain for every range and every relation.
       (Contributed by Ender Ting, 19-Nov-2024.)  (Revised by Ender Ting,
       17-Jan-2026.) $)
    nulchn $p |- (/) e. ( .< Chain A ) $=
      ( vx c0 cchn wcel cword cv c1 cmin co cfv wbr cdm cc0 csn cdif wral wrd0
      wa wceq dm0 difeq1i 0dif eqtri rzal ax-mp pm3.2i ischn mpbir ) DABEFDAGFZ
      CHZIJKDLULDLBMZCDNZOPZQZRZTUKUQASUPDUAUQUPDUOQDUNDUOUBUCUOUDUEUMCUPUFUGUH
      ADBCUIUJ $.
  $}

  ${
    $d .< n $.  $d A n $.  $d X n $.  $d n ph $.
    s1chn.1 $e |- ( ph -> X e. A ) $.
    $( A singleton word is always a chain.  (Contributed by Thierry Arnoux,
       19-Oct-2025.) $)
    s1chn $p |- ( ph -> <" X "> e. ( .< Chain A ) ) $=
      ( vn cs1 cword wcel cv c1 cmin co cfv wbr cdm cc0 cdif wral c0 cchn s1cld
      csn ral0 s1dm difeq1i difid eqtri raleqi mpbir ischn sylanblrc ) ADGZBHIF
      JZKLMUMNUNUMNCOZFUMPZQUCZRZSZUMBCUAIADBEUBUSUOFTSUOFUDUOFURTURUQUQRTUPUQU
      QDUEUFUQUGUHUIUJBUMCFUKUL $.
  $}

  ${
    $d .< c d i x $.  $d .< d i j x $.  $d A c d i x $.  $d A i j $.
    $d C c i $.  $d c d i ph x $.  $d c et $.  $d c i th $.  $d c ta $.
    $d d ps x $.  $d i j ph $.  $d i j th $.
    chnind.1 $e |- ( c = (/) -> ( ps <-> ch ) ) $.
    chnind.2 $e |- ( c = d -> ( ps <-> th ) ) $.
    chnind.3 $e |- ( c = ( d ++ <" x "> ) -> ( ps <-> ta ) ) $.
    chnind.4 $e |- ( c = C -> ( ps <-> et ) ) $.
    chnind.6 $e |- ( ph -> C e. ( .< Chain A ) ) $.
    chnind.7 $e |- ( ph -> ch ) $.
    chnind.8 $e |- ( ( ( ( ( ph /\ d e. ( .< Chain A ) ) /\ x e. A )
                      /\ ( d = (/) \/ ( lastS ` d ) .< x ) ) /\ th ) -> ta ) $.
    $( Induction over a chain.  See ~ nnind for an explanation about the
       hypotheses.  (Contributed by Thierry Arnoux, 19-Jun-2025.) $)
    chnind $p |- ( ph -> et ) $=
      ( cfv vi vj cword wcel cv c1 cmin co wbr cdm cc0 cdif wral chnwrd id cchn
      csn wa ischn sylib simprd wi c0 cconcat wceq dmeq difeq1d fveq1 raleqbidv
      cs1 breq12d anbi2d imbi12d weq adantr clsw wo simpllr simpll simplr s1cld
      simp-4l ccatdmss ssdifd sselda fvoveq1 fveq2 adantl rspcdv imp chash cfzo
      wb ad2antrr cz wss cn0 lencl syl nn0zd fzossrbm1 eldifad eqidd wrdfd fdmd
      fzossz eleqtrd sselid eldifsni fzo1fzo0n0 sylanbrc elfzom1b biimpa sseldd
      wne syl21anc ccatval1 syl3anc 3brtr3d an32s adantllr ralrimiva simp-4r wn
      jca lsw ad5antr caddc fzonn0p1 3syl ccatws1len eqcomd ccatws1cl ad3antrrr
      ad4antr eleqtrrd neqned hasheq0 ex expl necon3bid biimpar syl2anc elnnne0
      eldifsnd fzo0end ccats1val2 eqbrtrd an42ds orrd simpr syl1111anc cbvralvw
      cn sylibr a2and wrdind syl12anc ) AIHUCZUDZAUAUEZUFUGUHZITZUVAITZJUIZUAIU
      JZUKUQZULZUMZFAHIJQUNAUOAUUTUVIAIHJUPZUDUUTUVIURQHIJUAUSUTVAUUTAUVIURZFAU
      VBKUEZTZUVAUVLTZJUIZUAUVLUJZUVGULZUMZURZBVBAUVBVCTZUVAVCTZJUIZUAVCUJZUVGU
      LZUMZURZCVBAUVBLUEZTZUVAUWGTZJUIZUAUWGUJZUVGULZUMZURZDVBAUVBUWGGUEZVJZVDU
      HZTZUVAUWQTZJUIZUAUWQUJZUVGULZUMZURZEVBUVKFVBKLGIHUVLVCVEZUVSUWFBCUXEUVRU
      WEAUXEUVOUWBUAUVQUWDUXEUVPUWCUVGUVLVCVFVGUXEUVMUVTUVNUWAJUVBUVLVCVHUVAUVL
      VCVHVKVIVLMVMKLVNZUVSUWNBDUXFUVRUWMAUXFUVOUWJUAUVQUWLUXFUVPUWKUVGUVLUWGVF
      VGUXFUVMUWHUVNUWIJUVBUVLUWGVHUVAUVLUWGVHVKVIVLNVMUVLUWQVEZUVSUXDBEUXGUVRU
      XCAUXGUVOUWTUAUVQUXBUXGUVPUXAUVGUVLUWQVFVGUXGUVMUWRUVNUWSJUVBUVLUWQVHUVAU
      VLUWQVHVKVIVLOVMUVLIVEZUVSUVKBFUXHUVRUVIAUXHUVOUVEUAUVQUVHUXHUVPUVFUVGUVL
      IVFVGUXHUVMUVCUVNUVDJUVBUVLIVHUVAUVLIVHVKVIVLPVMACUWERVOUWGUUSUDZUWOHUDZU
      RZAUWMEDUXCUXKAUXCDEVBUXKAURZUXCURZDEUXMDURZAUWGUVJUDZURUXJUWGVCVEZUWGVPT
      ZUWOJUIZVQDEUXNAUXOUXKAUXCDVRUXNUXIUBUEZUFUGUHZUWGTZUXSUWGTZJUIZUBUWLUMZU
      XOUXIUXJAUXCDWBUXLDUXCUYDUXLDURUXCURUYCUBUWLUXLUXCUXSUWLUDZUYCDUXLUYEUXCU
      YCUXLUYEURZUXCURZUXTUWQTZUXSUWQTZUYAUYBJUYFUXCUYHUYIJUIZUYFUWTUYJUAUXSUXB
      UXLUWLUXBUXSUXLUWKUXAUVGUXLUWGUWPHUXIUXJAVSZUXLUWOHUXIUXJAVTZWAZWCWDWEUAU
      BVNZUWTUYJWMUYFUYNUWRUYHUWSUYIJUVAUXSUFUWQUGWFUVAUXSUWQWGVKWHWIWJUYGUXIUW
      PUUSUDZUXTUKUWGWKTZWLUHZUDUYHUYAVEUXIUXJAUYEUXCWBZUXLUYOUYEUXCUYMWNZUYGUK
      UYPUFUGUHZWLUHZUYQUXTUYGUYPWOUDZVUAUYQWPUYGUYPUYGUXIUYPWQUDZUYRHUWGWRZWSW
      TZUYPXAWSUYGUXSWOUDZVUBUXSUFUYPWLUHUDZUXTVUAUDZUYGUYQWOUXSUKUYPXFUYGUXSUW
      KUYQUYGUXSUWKUVGUXLUYEUXCVTZXBUYGUYQHUWGUYGHUYPUWGUYGUYPXCUYRXDXEXGZXHVUE
      UYGUXSUYQUDZUXSUKXOZVUGVUJUYGUYEVULVUIUXSUWKUKXIWSUXSUYPXJXKVUFVUBURVUGVU
      HUXSUYPXLXMXPXNHHUWGUWPUXTXQXRUYGUXIUYOVUKUYIUYBVEUYRUYSVUJHHUWGUWPUXSXQX
      RXSXTZYAYBXTHUWGJUBUSXKYEUXIUXJAUXCDYCUXNUXPUXRUXNUXPYDZUXRUXLVUNDUXCUXRU
      XLVUNURDURZUXCURZUXQUYTUWGTZUWOJUXIUXQVUQVEUXJAVUNDUXCUWGUUSYFYGVUPUYTUWQ
      TZUYPUWQTZVUQUWOJVUOUXCVURVUSJUIZVUOUWTVUTUAUYPUXBVUOUYPUXAUKVUOUYPUKUYPU
      FYHUHZWLUHZUXAVUOUXIVUCUYPVVBUDUXIUXJAVUNDWBZVUDUYPYIYJVUOVVBHUWQVUOHVVAU
      WQVUOUWQWKTZVVAUXIVVDVVAVEUXJAVUNDHUWGUWOYKYOYLUXKUWQUUSUDAVUNDHUWGUWOYMY
      NXDXEYPVUOUXIUWGVCXOZUYPUKXOZVVCVUOUWGVCUXLVUNDVTYQUXIVVFVVEUXIUYPUKUWGVC
      UWGUUSYRUUAUUBUUCZUUEUVAUYPVEZUWTVUTWMVUOVVHUWRVURUWSVUSJUVAUYPUFUWQUGWFU
      VAUYPUWQWGVKWHWIWJVUPUXIUYOUYTUYQUDZVURVUQVEUXLUXIVUNDUXCUYKYNZUXLUYOVUND
      UXCUYMYNVUPUYPUUNUDZVVIVUPVUCVVFVVKVUPUXIVUCVVJVUDWSVUOVVFUXCVVGVOUYPUUDX
      KUYPUUFWSHHUWGUWPUYTXQXRVUPUXIUXJUYPUYPVEVUSUWOVEVVJUXLUXJVUNDUXCUYLYNVUP
      UYPXCUWOUYPHUWGUUGXRXSUUHUUIYSUUJUXMDUUKSUULYSYTUXKAUXCUWMUXMUYDUWMUXMUYC
      UBUWLVUMYBUWJUYCUAUBUWLUYNUWHUYAUWIUYBJUVAUXSUFUWGUGWFUVAUXSUWGWGVKUUMUUO
      YTUUPUUQWJUUR $.
  $}

  ${
    $d .< c d x $.  $d .< d i j x $.  $d A c d i j $.  $d A x $.  $d C c i j $.
    $d C d x $.  $d I i $.  $d c ph $.  $d d ph x $.  $d i j ph $.
    chnub.1 $e |- ( ph -> .< Po A ) $.
    chnub.2 $e |- ( ph -> C e. ( .< Chain A ) ) $.
    chnub.3 $e |- ( ph -> I e. ( 0 ..^ ( ( # ` C ) - 1 ) ) ) $.
    $( In a chain, the last element is an upper bound.  (Contributed by Thierry
       Arnoux, 19-Jun-2025.) $)
    chnub $p |- ( ph -> ( C ` I ) .< ( lastS ` C ) ) $=
      ( vi cfv wbr cc0 c1 cmin co cfzo wceq fveq2 c0 wcel vc vd vj vx cv breq1d
      clsw chash wral cs1 cconcat oveq1d oveq2d fveq1 raleqbidv cbvralvw bitrid
      breq12d ral0 cle hash0 oveq1i cneg df-neg neg1rr neg1lt0 eqbrtrri eqbrtri
      0re ltleii cz wb 0z eqeltri 1z zsubcl mp2an fzon mpbi raleqi mpbir a1i wa
      cchn caddc cword simp-6r chnwrd ccatws1len syl simpr fveq2d eqtrdi 3eqtrd
      wo 0p1e1 1m1e0 fzo0 simplr ne0d pm2.21ddne wne wpo ad7antr adantr simp-5r
      w3a ccatws1cl syl2anc cuz wss cn0 lencl nn0zd zsubcld peano2zd cn hasheq0
      1zzd necon3bid biimpar elnnne0 sylanbrc nnred ltm1d ltp1d lttrd syl3anbrc
      zred ltled eluz2 fzoss2 sselda eleqtrrd wrdsymbcl lswcl lswccats1 eleqtrd
      simp-4r rspcdva eqeltrd 3jca nncnd pncand eqtrd ccats1val1 eqbrtrd neneqd
      1cnd orcnd breqtrrd imp syl22anc fzo0end ccatval1 syl3anc 3eqtr4d 3brtr4d
      potr lsw csn cun fveq2i nnuz eqtr4i eleqtrrdi fzosplitsnm1 sylancr elunsn
      s1cld ibi mpjaodan pm2.61dane ralrimiva chnind ) AIUEZCJZCUGJZDKZECJZUVRD
      KILCUHJZMNOZPOZEUVPEQUVQUVTUVRDUVPECRUFAUVPUAUEZJZUWDUGJZDKZILUWDUHJZMNOZ
      POZUIZUVPSJZSUGJZDKZILSUHJZMNOZPOZUIZUVPUBUEZJZUWSUGJZDKZILUWSUHJZMNOZPOZ
      UIZUCUEZUWSUDUEZUJZUKOZJZUXJUGJZDKZUCLUXJUHJZMNOZPOZUIZUVSIUWCUIUDBCDUAUB
      UWDSQZUWGUWNIUWJUWQUXRUWIUWPLPUXRUWHUWOMNUWDSUHRULUMUXRUWEUWLUWFUWMDUVPUW
      DSUNUWDSUGRURUOUWDUWSQZUWGUXBIUWJUXEUXSUWIUXDLPUXSUWHUXCMNUWDUWSUHRULUMUX
      SUWEUWTUWFUXADUVPUWDUWSUNUWDUWSUGRURUOUWKUXGUWDJZUWFDKZUCUWJUIUWDUXJQZUXQ
      UWGUYAIUCUWJUVPUXGQZUWEUXTUWFDUVPUXGUWDRUFUPUYBUYAUXMUCUWJUXPUYBUWIUXOLPU
      YBUWHUXNMNUWDUXJUHRULUMUYBUXTUXKUWFUXLDUXGUWDUXJUNUWDUXJUGRURUOUQUWDCQZUW
      GUVSIUWJUWCUYDUWIUWBLPUYDUWHUWAMNUWDCUHRULUMUYDUWEUVQUWFUVRDUVPUWDCUNUWDC
      UGRURUOGUWRAUWRUWNISUIUWNIUSUWNIUWQSUWPLUTKZUWQSQZUWPLMNOZLUTUWOLMNVAVBMV
      CZUYGLUTMVDUYHLVEVIVFVJVGVHLVKTZUWPVKTZUYEUYFVLVMUWOVKTMVKTUYJUWOLVKVAVMV
      NVOUWOMVPVQLUWPVRVQVSVTWAWBAUWSBDWDTZWCZUXHBTZWCZUWSSQZUXAUXHDKZWOZWCZUXF
      WCZUXMUCUXPUYSUXGUXPTZWCZUXMUWSSVUAUYOWCZUXMUXPSVUBUXPLLPOSVUBUXOLLPVUBUX
      OMMNOLVUBUXNMMNVUBUXNUXCMWEOZLMWEOZMVUBUWSBWFZTZUXNVUCQZVUBBUWSDAUYKUYMUY
      QUXFUYTUYOWGWHBUWSUXHWIZWJVUBUXCLMWEVUBUXCUWOLVUBUWSSUHVUAUYOWKWLVAWMULVU
      DMQVUBWPWBWNULWQWMUMLWRWMVUBUXPUXGUYSUYTUYOWSWTXAVUAUWSSXBZWCZUXGUXETZUXM
      UXGUXDQZVUJVUKWCZBDXCZUXKBTZUXABTZUXLBTZXGZUXKUXADKZUXAUXLDKZUXMAVUNUYKUY
      MUYQUXFUYTVUIVUKFXDVUMVUOVUPVUQVUMUXJVUETZUXGLUXNPOZTVUOVUMVUFUYMVVAVUJVU
      FVUKVUJBUWSDAUYKUYMUYQUXFUYTVUIWGWHZXEZVUJUYMVUKUYLUYMUYQUXFUYTVUIXFZXEZB
      UWSUXHXHXIVUMUXGLVUCPOZVVBVUJUXEVVGUXGVUJVUCUXDXJJTZUXEVVGXKVUJUXDVKTVUCV
      KTUXDVUCUTKVVHVUJUXCMVUJUXCVUJVUFUXCXLTZVVCBUWSXMWJZXNZVUJXSXOZVUJUXCVVKX
      PZVUJUXDVUCVUJUXDVVLYIZVUJVUCVVMYIZVUJUXDUXCVUCVVNVUJUXCVUJVVIUXCLXBZUXCX
      QTZVVJVUJVUFVUIVVPVVCVUAVUIWKZVUFVVPVUIVUFUXCLUWSSUWSVUEXRXTYAXIUXCYBYCZY
      DZVVOVUJUXCVVTYEVUJUXCVVTYFYGYJUXDVUCYKYHUXDLVUCYLWJYMVUMUXNVUCLPVUMVUFVU
      GVVDVUHWJUMYNUXGBUXJYOXIVUMVUFVUIVUPVVDVUAVUIVUKWSBUWSYPXIVUMUXLUXHBVUJUX
      LUXHQZVUKVUJVUFUYMVWAVVCVVEUXHBUWSYQXIZXEZVVFUUAUUBVUMUXKUXGUWSJZUXADVUMV
      UFUXGLUXCPOZTZUXKVWDQVVDVUJVWFVUKVUJUXGUXPVWEUYSUYTVUIWSVUJUXOUXCLPVUJUXO
      VUCMNOZUXCVUJVUFUXOVWGQVVCVUFUXNVUCMNVUHULWJVUJUXCMVUJUXCVVSUUCVUJUUIUUDU
      UEUMYRZXEUXHUXGBUWSUUFXIVUMUXBVWDUXADKIUXEUXGUYCUWTVWDUXADUVPUXGUWSRUFUYR
      UXFUYTVUIVUKYSVUJVUKWKYTUUGVUMUXAUXHUXLDVUJUYPVUKVUJUYOUYPUYNUYQUXFUYTVUI
      YSVUJUWSSVVRUUHUUJZXEVWCUUKVUNVURWCVUSVUTWCUXMBUXKUXAUXLDUUSUULUUMVUJVULW
      CZUXAUXHUXKUXLDVUJUYPVULVWIXEVWJUXDUXJJZUXDUWSJZUXKUXAVWJVUFUXIVUETUXDVWE
      TZVWKVWLQVUJVUFVULVVCXEZVWJUXHBUYLUYMUYQUXFUYTVUIVULWGUVJVWJVVQVWMVUJVVQV
      ULVVSXEUXCUUNWJBBUWSUXIUXDUUOUUPVWJUXGUXDUXJVUJVULWKWLVWJVUFUXAVWLQVWNUWS
      VUEUUTWJUUQVUJVWAVULVWBXEUURVUJUXGUXEUXDUVAUVBZTZVUKVULWOZVUJUXGVWEVWOVWH
      VUJUYIUXCVUDXJJZTVWEVWOQVMVUJUXCXQVWRVVSVWRMXJJXQVUDMXJWPUVCUVDUVEUVFLUXC
      UVGUVHYRVWPVWQUXGUXEUXDVWOUVIUVKWJUVLUVMUVNUVOHYT $.
  $}

  ${
    chnlt.1 $e |- ( ph -> .< Po A ) $.
    chnlt.2 $e |- ( ph -> C e. ( .< Chain A ) ) $.
    chnlt.3 $e |- ( ph -> J e. ( 0 ..^ ( # ` C ) ) ) $.
    chnlt.4 $e |- ( ph -> I e. ( 0 ..^ J ) ) $.
    $( Compare any two elements in a chain.  (Contributed by Thierry Arnoux,
       19-Jun-2025.) $)
    chnlt $p |- ( ph -> ( C ` I ) .< ( C ` J ) ) $=
      ( c1 co cfv cc0 cfzo wcel syl wceq syl2anc cn0 caddc cpfx clsw cfz pfxchn
      chash fzofzp1 cmin fzossz sselid zcnd cword chnwrd pfxlen mvrraddd oveq2d
      cz 1cnd eleqtrrd chnub wss fzo0ssnn0 fzossfzop1 sseldd syl3anc fz0add1fz1
      pfxfv lencl pfxfvlsw pncand fveq2d eqtrd 3brtr3d ) AECFKUALZUBLZMZVOUCMZE
      CMZFCMZDABVODEGABCDVNHAFNCUFMZOLZPZVNNVTUDLPZINVTFUGQZUEAENFOLZNVOUFMZKUH
      LZOLJAWGFNOAWFFKAFAWAUQFNVTUIIUJUKZAURZACBULPZWCWFVNRABCDHUMZWDBCVNUNSUOU
      PUSUTAWJWCENVNOLZPVPVRRWKWDAWEWLEAFTPWEWLVAAWATFVTVBIUJFVCQJVDEVNBCVGVEAV
      QVNKUHLZCMZVSAWJVNKVTUDLPZVQWNRWKAVTTPZWBWOAWJWPWKBCVHQIVTFVFSVNBCVISAWMF
      CAFKWHWIVJVKVLVM $.
  $}

  ${
    $d .< x y $.  $d .< i j x y $.  $d .< n $.  $d A i j n $.  $d A x y $.
    $d C x y $.  $d C i j $.  $d C n $.
    $( A chain induces a total order.  (Contributed by Thierry Arnoux,
       19-Jun-2025.) $)
    chnso $p |- ( ( .< Po A /\ C e. ( .< Chain A ) ) -> .< Or ran C ) $=
      ( vn vi vj wcel wa cc0 cfv cfzo co cv wceq cz simp-4r simplr adantr simpr
      wbr vx vy wpo cchn crn wss chash eqidd cword cmin cdm csn cdif wral ischn
      c1 bilani simpld wrdfd frnd simpl poss sylc w3o clt fzossz sselid lttri4d
      zred simp-8l simp-8r simpllr cuz elfzouz ad5antlr syl3anbrc chnlt 3brtr3d
      elfzo2 ex fveq2d 3eqtr3d ad3antlr 3orim123d mpd wrex ffnd ad4antr fvelrnb
      wfn biimpa syl2anc r19.29a ad2antrr anasss issod ) ACUCZBACUDGZHZUAUBBUEZ
      CWSWTAUFWQWTCUCWSIBUGJZKLZABWSAXABWSXAUHWSBAUIGZDMZUPUJLBJXDBJCTDBUKIULUM
      UNZWRXCXEHWQABCDUOUQURUSZUTWQWRVAWTACVBVCWSUAMZWTGZUBMZWTGZXGXICTZXGXINZX
      IXGCTZVDZWSXHHZXJHZEMZBJZXGNZXNEXBXPXQXBGZHZXSHZFMZBJZXINZXNFXBYBYCXBGZHZ
      YEHZXQYCVETZXQYCNZYCXQVETZVDXNYHXQYCYHXQYHXBOXQIXAVFZXPXTXSYFYEPZVGZVIYHY
      CYHXBOYCYLYBYFYEQVGZVIVHYHYIXKYJXLYKXMYHYIXKYHYIHZXRYDXGXICYPABCXQYCWQWRX
      HXJXTXSYFYEYIVJWQWRXHXJXTXSYFYEYIVKYBYFYEYIVLYPXQIVMJZGZYCOGZYIXQIYCKLGXT
      YRXPXSYFYEYIXQIXAVNVOYHYSYIYORYHYISXQIYCVSVPVQYAXSYFYEYIPYGYEYIQVRVTYHYJX
      LYHYJHZXRYDXGXIYTXQYCBYHYJSWAYAXSYFYEYJPYGYEYJQWBVTYHYKXMYHYKHZYDXRXIXGCU
      UAABCYCXQWQWRXHXJXTXSYFYEYKVJWQWRXHXJXTXSYFYEYKVKYHXTYKYMRUUAYCYQGZXQOGZY
      KYCIXQKLGYFUUBYBYEYKYCIXAVNWCYHUUCYKYNRYHYKSYCIXQVSVPVQYGYEYKQYAXSYFYEYKP
      VRVTWDWEYBBXBWJZXJYEFXBWFZWSUUDXHXJXTXSWSXBABXFWGZWHXOXJXTXSVLUUDXJUUEFXB
      XIBWIWKWLWMXPUUDXHXSEXBWFZWSUUDXHXJUUFWNWSXHXJQUUDXHUUGEXBXGBWIWKWLWMWOWP
      $.
  $}

  ${
    $d .< n $.  $d A n $.  $d T n $.  $d X n $.  $d n ph $.
    chnccats1.1 $e |- ( ph -> X e. A ) $.
    chnccats1.2 $e |- ( ph -> T e. ( .< Chain A ) ) $.
    chnccats1.3 $e |- ( ph -> ( T = (/) \/ ( lastS ` T ) .< X ) ) $.
    $( Extend a chain with a single element.  (Contributed by Thierry Arnoux,
       19-Oct-2025.) $)
    chnccats1 $p |- ( ph -> ( T ++ <" X "> ) e. ( .< Chain A ) ) $=
      ( vn co wcel c1 cfv cc0 cdif wa wceq adantr syl c0 cs1 cconcat cword cmin
      cv wbr cdm csn wral cchn chnwrd s1cld syl2anc chash cfzo eqidd wrdfd fdmd
      ccatcl difeq1d eleq2d biimpar ischn sylib simprd r19.21bi simpr cn0 lencl
      syldan elfzodif0 ccats1val1 eldifad 3brtr4d adantlr clsw noel fveq2 hash0
      eqtrdi adantl sneqd difid mtbiri pm2.21dd elsnd oveq1d fveq2d ad2antrr cn
      eqeltrrd eldifbd eldifd dfn2 eleqtrrdi fzo0end eqeltrd 3eqtr4d ccats1val2
      lsw syl3anc eqtrd mpjaodan cun caddc ccatws1len eqcomd cuz nn0uz eleqtrdi
      wo fzosplitsn difundir biimpa elun ralrimiva sylanbrc ) ADEUAZUBJZBUCZKZI
      UEZLUDJZXSMZYBXSMZCUFZIXSUGZNUHZOZUIXSBCUJZKADXTKZXRXTKYAABDCGUKZAEBFULBD
      XRUSUMZAYFIYIAYBYIKZPZYBNDUNMZUOJZYHOZKZYFYBYPUHZYHOZKZAYSYFYNAYSPZYCDMZY
      BDMZYDYECAYSYBDUGZYHOZKZUUDUUECUFZAUUHYSAUUGYRYBAUUFYQYHAYQBDABYPDAYPUPYL
      UQURUTVAVBAUUIIUUGAYKUUIIUUGUIZADYJKYKUUJPGBDCIVCVDVEVFVJUUCYKYCYQKZYDUUD
      QZAYKYSYLRZUUCYBYPAYSVGZUUCYKYPVHKZUUMBDVIZSVKEYCBDVLZUMUUCYKYBYQKYEUUEQU
      UMUUCYBYQYHUUNVMEYBBDVLUMVNVOAUUBYFYNAUUBPZDTQZYFDVPMZECUFZUURUUSPZUUBYFU
      URUUBUUSAUUBVGZRUVBUUBYBTKYBVQUVBUUATYBUVBUUAYHYHOTUVBYTYHYHUVBYPNUUSYPNQ
      UURUUSYPTUNMNDTUNVRVSVTWAWBUTYHWCVTVAWDWEUURUVAPZUUTEYDYECUURUVAVGUVDUUDY
      PLUDJZDMZYDUUTUVDYCUVEDUURYCUVEQUVAUURYBYPLUDUURYBYPUURYBYTYHUVCVMWFZWGZR
      WHUVDYKUUKUULAYKUUBUVAYLWIZUURUUKUVAUURYCUVEYQUVHUURYPWJKUVEYQKUURYPVHYHO
      WJUURYPVHYHUURYKUUOAYKUUBYLRUUPSUURYPYTYHUURYBYPUUAUVGUVCWKWLWMWNWOYPWPSW
      QRUUQUMUVDYKUUTUVFQUVIDXTWTSWRUVDYEYPXSMZEUVDYBYPXSUURYBYPQUVAUVGRWHUVDYK
      EBKZYPYPQUVJEQUVIAUVKUUBUVAFWIUVDYPUPEYPBDWSXAXBVNAUUSUVAXKUUBHRXCVOYOYBY
      RUUAXDZKZYSUUBXKAYNUVMAYIUVLYBAYIYQYTXDZYHOUVLAYGUVNYHAYGNYPLXEJZUOJZUVNA
      UVPBXSABUVOXSAXSUNMZUVOAYKUVQUVOQYLBDEXFSXGYMUQURAYPNXHMZKUVPUVNQAYPVHUVR
      AYKUUOYLUUPSXIXJNYPXLSXBUTYQYTYHXMVTVAXNYBYRUUAXOVDXCXPBXSCIVCXQ $.
  $}

  ${
    $d .< n $.  $d A n $.  $d T n $.  $d U n $.  $d n ph $.
    chnccat.1 $e |- ( ph -> T e. ( .< Chain A ) ) $.
    chnccat.2 $e |- ( ph -> U e. ( .< Chain A ) ) $.
    chnccat.3 $e |- ( ph -> ( T = (/) \/ U = (/) \/ ( lastS ` T ) .< ( U ` 0 )
      ) ) $.
    $( Concatenate two chains.  (Contributed by Ender Ting, 20-Jan-2026.) $)
    chnccat $p |- ( ph -> ( T ++ U ) e. ( .< Chain A ) ) $=
      ( co wcel c1 cfv cc0 cdif wa wceq adantr adantl syl c0 cconcat cword cmin
      vn wbr cdm csn wral cchn chnwrd ccatcl syl2anc chash cfzo caddc cpr eqidd
      cv wrdfd difeq1d eleq2d biimpar wss snsspr1 sscon ax-mp sseli ischn sylib
      fdmd simprd r19.21bi sylan2 syldan lencl elfzodif0 ccatval1 syl3anc simpr
      eldifad 3brtr4d adantlr clsw fveq2 hash0 eqtrdi sneqd difpr difid difeq1i
      cn0 noel 0dif 3eqtri mtbiri pm2.21dd eldifi elsnd ad2antlr cvv vex eldifn
      wn oveq2d cc eqtrd preq2d oveq1d cn eldifd fveq2d wne jca sylanbrc sylibr
      3syl ex w3a eqcomd 3ad2ant1 w3o mpjao3dan cz zcn 1cnd nn0z cle clt necomd
      zred wb mpbid cr ccatval2 wo eldif simplrr idd jctird imbitrrdi a1i nn0cn
      addridd neleqtrd nelpr2 pm2.21ddne eldifbd dfn2 eleqtrrdi fzo0end eqeltrd
      eqeltrrd lsw eqtr4d prid2g addrid eleqtrrd snssd ssdif0 nel02 mt2d neqned
      elnnne0 lbfzo0 addlid ccatval3 elfzoelz sub32d fzosubel3 eldifsni subne0d
      simpl nelsn chnltm1 eqbrtrd elfzole1 velsn biimpri necon3bi simp1r simp1l
      simp2 simp3 leneltd simp1 ancomd zltp1le 1red lesub1d pncand breq1d bitrd
      peano2re peano2rem zaddcld ltm1d elfzolt2 lttrd peano2zm mpbir2and fzonel
      elfzo ccatlen mtoi difsn eqtr4di bitrdi exmidd jctild orim12d mpd anim1ci
      orcd olcd adantrr fzospliti mpjaodan sylbida 3orass ralrimiva ) ADEUAIZBU
      BZJZUDURZKUCIZUYALZUYDUYALZCUEZUDUYAUFZMUGZNZUHUYABCUIZJADUYBJZEUYBJZUYCA
      BDCFUJZABECGUJZBDEUKULZAUYHUDUYKAUYDUYKJZOZUYDMDUMLZUNIZMUYTEUMLZUOIZUPZN
      ZJZUYHUYDUYTUGZVUDNZJZUYDUYTVUCUNIZVUGNZVUDNJZAVUFUYHUYRAVUFOZUYEDLZUYDDL
      ZUYFUYGCAVUFUYDDUFZVUDNZJZVUNVUOCUEZAVURVUFAVUQVUEUYDAVUPVUAVUDAVUABDABUY
      TDAUYTUQUYOUSVJUTVAVBVURAUYDVUPUYJNZJVUSVUQVUTUYDUYJVUDVCZVUQVUTVCMVUCVDZ
      UYJVUDVUPVEVFVGAVUSUDVUTAUYMVUSUDVUTUHZADUYLJUYMVVCOFBDCUDVHVIVKVLVMVNVUM
      UYMUYNUYEVUAJZUYFVUNPZAUYMVUFUYOQZAUYNVUFUYPQZVUMUYDUYTVUFUYDVUAUYJNZJAVU
      EVVHUYDVVAVUEVVHVCVVBUYJVUDVUAVEVFVGRAUYTWKJZVUFAUYMVVIUYOBDVOZSQVPBBDEUY
      EVQZVRVUMUYMUYNUYDVUAJZUYGVUOPVVFVVGVUMUYDVUAVUDAVUFVSVTBBDEUYDVQVRWAWBAV
      UIUYHUYRAVUIOZDTPZUYHETPZDWCLZMELZCUEZVVMVVNOZVUIUYHVVMVUIVVNAVUIVSZQVVSV
      UIUYDTJUYDWLVVSVUHTUYDVVSVUHUYJVUDNZTVVSVUGUYJVUDVVSUYTMVVNUYTMPVVMVVNUYT
      TUMLZMDTUMWDWEWFRWGUTVWAUYJUYJNZVUCUGZNTVWDNTUYJMVUCWHVWCTVWDUYJWIWJVWDWM
      WNWFVAWOWPVVMVVOOZUYHUYDUYTVUIUYDUYTPZAVVOVUIUYDUYTUYDVUGVUDWQWRZWSVWEUYD
      MUYTWTUYDWTJVWEUDXAUUAVWEVUDMUYTUPZUYDVUIUYDVUDJXCZAVVOUYDVUGVUDXBWSVWEVU
      CUYTMVWEVUCUYTMUOIZUYTVWEVUBMUYTUOVVOVUBMPZVVMVVOVUBVWBMETUMWDWEWFRXDVWEU
      YTVVMUYTXEJZVVOAVWLVUIAUYMVVIVWLUYOVVJUYTUUBZXPZQQUUCXFXGUUDUUEUUFVVMVVRO
      ZVVPVVQUYFUYGCVVMVVRVSVWOUYFVUNVVPVWOUYMUYNVVDVVEVVMUYMVVRAUYMVUIUYOQZQZV
      VMUYNVVRAUYNVUIUYPQQZVVMVVDVVRVVMUYEUYTKUCIZVUAVVMUYDUYTKUCVVMUYDUYTVVMUY
      DVUGVUDVVTVTWRZXHVVMUYTXIJVWSVUAJVVMUYTWKUYJNXIVVMUYTWKUYJVVMUYMVVIVWPVVJ
      SVUIUYTUYJJXCAVUIUYTVUGUYJVUIUYDUYTVUGUYJNZVWGVUHVXAUYDVVAVUHVXAVCVVBUYJV
      UDVUGVEVFVGUULUUGRXJUUHUUIUYTUUJSUUKQVVKVRVVMVUNVVPPVVRVVMVUNVWSDLZVVPVVM
      UYEVWSDVUIUYEVWSPAVUIUYDUYTKUCVWGXHRXKVVMUYMVVPVXBPVWPDUYBUUMSUUNQXFVWOUY
      GUYTUYALZVVQVWOUYDUYTUYAVVMVWFVVRVWTQXKVWOUYMUYNMMVUBUNIZJZVXCVVQPVWQVWRV
      WOVUBXIJZVXEVVMVXFVVRVVMVUBWKJZVUBMXLVXFAVXGVUIAUYNVXGUYPBEVOZSQVVMVUBMVV
      MVWKVUIVVTVVMVWKVUIXCZVVMVWKOZVWLVWKOZVUHTPZVXIVXJVWLVWKVXJUYMVVIVWLVVMUY
      MVWKVWPQVVJVWMXPVVMVWKVSXMVXKVUGVUDVCVXLVXKUYTVUDVXKUYTVWHVUDVWLUYTVWHJVW
      KMUYTXEUUOQVXKVUCUYTMVXKVUCVWJUYTVXKVUBMUYTUOVWLVWKVSXDVWLVWJUYTPVWKUYTUU
      PQXFXGUUQUURVUGVUDUUSVIVUHUYDUUTXPXQUVAUVBVUBUVCXNQVUBUVDXOUYMUYNVXEXRVXC
      MUYTUOIZUYALZVVQUYMUYNVXCVXNPZVXEUYMVVIVWLVXOVVJVWMVWLUYTVXMUYAVWLVXMUYTU
      YTUVEXSXKXPXTBDEMUVFXFVRXFWAAVVNVVOVVRYAVUIHQYBWBAVULUYHUYRAVULOZUYEUYTUC
      IZELZUYDUYTUCIZELZUYFUYGCVXPVXRVXSKUCIZELVXTCVXPVXQVYAEVXPUYDKUYTVXPVULUY
      DYCJZUYDXEJZAVULVSZVULUYDVUJJZVYBVULUYDVUJVUGUYDVUKVUDWQZVTZUYDUYTVUCUVGZ
      SUYDYDZXPVXPYEAVWLVULVWNQUVHXKVXPBECVXSAEUYLJVULGQAVULVXSVXDUYJNZJZVXSEUF
      ZUYJNZJZVXPVXSVXDUYJVXPVYEVUBYCJZVXSVXDJVULVYEAVYGRZAVYOVULAUYNVXGVYOUYPV
      XHVUBYFXPZQUYDUYTVUBUVIULVXPAUYDVUKJZOZVXSMXLVXSUYJJXCVXPAVYRAVULUVLVXPUY
      DVUKVUDVYDVTXMVYSUYDUYTVYRVYCAVYRVYEVYBVYCUYDVUJVUGWQZVYHVYIXPRAVWLVYRVWN
      QVYRUYDUYTXLAUYDVUJUYTUVJRUVKVXSMUVMXPXJAVYNVYKAVYMVYJVXSAVYLVXDUYJAVXDBE
      ABVUBEAVUBUQUYPUSVJUTVAVBVNUVNUVOVXPUYMUYNUYEVUJJZUYFVXRPAUYMVULUYOQZAUYN
      VULUYPQZVULAVYRWUAVYFVYSWUAUYTUYEYGUEZUYEVUCYHUEZVYSVYBUYTYCJZOZUYTUYDYGU
      EZUYTUYDXLZWUDVYSVYBWUFVYRVYBAVYRVYEVYBVYTVYHSRZAWUFVYRAUYMVVIWUFUYOVVJUY
      TYFXPZQZXMVYRWUHAVYRVYEWUHVYTUYDUYTVUCUVPSRVYRWUIAVYRUYDVUGJZXCZWUIUYDVUJ
      VUGXBWUNUYDUYTWUMUYDUYTWUMVWFUDUYTUVQUVRUVSYISRWUGWUHWUIXRZUYTKUOIZUYDYGU
      EZWUDWUOUYTUYDYHUEZWUQWUOUYTUYDWUOUYTVYBWUFWUHWUIUVTYJZWUOUYDVYBWUFWUHWUI
      UWAYJZWUGWUHWUIUWBWUOUYTUYDWUGWUHWUIUWCYIUWDWUOWUFVYBOWURWUQYKWUOVYBWUFWU
      GWUHWUIUWEUWFUYTUYDUWGSYLWUOWUQWUPKUCIZUYEYGUEWUDWUOWUPUYDKWUOUYTYMJWUPYM
      JWUSUYTUWMSWUTWUOUWHUWIWUOWVAUYTUYEYGWUGWUHWVAUYTPZWUIWUFWVBVYBWUFUYTKUYT
      YDWUFYEUWJRXTUWKUWLYLVRVYSUYEUYDVUCVYSUYDYMJUYEYMJVYSUYDWUJYJZUYDUWNSWVCV
      YSVUCAVUCYCJZVYRAUYTVUBWUKVYQUWOQZYJVYSUYDWVCUWPVYRUYDVUCYHUEZAVYRVYEWVFV
      YTUYDUYTVUCUWQSRUWRVYSUYEYCJZWUFWVDWUAWUDWUEOYKVYSVYBWVGWUJUYDUWSSWULWVEU
      YEUYTVUCUXBVRUWTVMBDEUYEYNVRVXPUYMUYNVYEUYGVXTPWUBWUCVYPBDEUYDYNVRWAWBUYS
      VUFVUIVULYOZYOZVUFVUIVULYAAUYRUYDMVUCUNIZJZVWIOZWVIAUYRUYDWVJVUDNZJWVLAUY
      KWVMUYDAUYKWVJUYJNZWVMAUYIWVJUYJAWVJBUYAABVUCUYAAUYAUMLZVUCAUYMUYNWVOVUCP
      UYOUYPBBDEUXCULXSUYQUSVJUTAWVNWVNVWDNZWVMAVUCWVNJZXCZWVNWVPPAWVQVUCWVJJZM
      VUCUXAAWVQWVSAWVQOVUCWVJUYJAWVQVSVTXQUXDWVRWVPWVNVUCWVNUXEXSSWVJMVUCWHUXF
      XFVAUYDWVJVUDYPUXGAWVLOZVVLWVIVYEWVTVVLOZVUFWVHWWAUYDVUAVUDWVTVVLVSAWVKVW
      IVVLYQXJUXMWVTVYEOZWVHVUFWWBWUMWUNYOWVHWWBWUMUXHWWBWUMVUIWUNVULWWBWUMWUMV
      WIOVUIWWBWUMWUMVWIWWBWUMYRAWVKVWIVYEYQZYSUYDVUGVUDYPYTWWBWUNVYRVWIOVULWWB
      WUNVYRVWIWWBWUNVYEWUNOVYRWWBWUNWUNVYEWWBWUNYRWVTVYEVSUXIUYDVUJVUGYPYTWWCY
      SUYDVUKVUDYPYTUXJUXKUXNWVTWVKWUFOZVVLVYEYOAWVKWWDVWIAWUFWVKWUKUXLUXOUYDMV
      UCUYTUXPSUXQUXRVUFVUIVULUXSXOYBUXTBUYACUDVHXN $.
  $}

  ${
    $d .< n $.  $d A n $.  $d B n $.
    $( Reverse of a chain is chain under the converse relation and same domain.
       (Contributed by Ender Ting, 20-Jan-2026.) $)
    chnrev $p |- ( B e. ( .< Chain A ) -> ( reverse ` B ) e. ( `' .< Chain A )
      ) $=
      ( vn cchn wcel cfv cmin wbr cc0 syl cfzo cfz wceq cn0 syl2anc 3brtr4d cle
      c1 co creverse cword cv ccnv cdm cdif wral id chnwrd revcl wa chash simpl
      csn wss fzossfz a1i wrddm revlen eqcomd oveq2d ssdifd sselda adantr lencl
      3sstr4d fz0dif1 eleqtrd ubmelfzo eleqtrrd nn0cnd cz cc eldifi anim2i 3syl
      eleq2d biimpa elfzoelz zcn wnel wne wrdlndm eqidd neleq12d mpbid elnelne2
      adantl necomd subne0d eldifsnd chnltm1 1cnd sub32d fveq2d nnncan2d sylibr
      brcnv caddc cn elfzonn0 eldifsni elnnne0 sylanbrc nnm1nn0 elfzo0le npcand
      fvex nn0p1elfzo syl3anc revfv eqtrd imbitrid imp ralrimiva ischn ) BACEFZ
      BUAGZAUBZFZDUCZSHTZXRGZYAXRGZCUDZIZDXRUEZJUNZUFZUGXRAYEEFXQBXSFZXTXQABCXQ
      UHUIZABUJZKZXQYFDYIXQYAYIFZUKZBULGZSHTZYBHTZBGZYQYAHTZBGZYCYDYEYOUUAYSCIY
      SUUAYEIYOYPYAHTZSHTZBGUUBBGUUAYSCYOABCUUBXQYNUMYOUUBBUEZJYOUUBJYPLTZUUDYO
      YASYPMTZFUUBUUEFYOYAJYPMTZYHUFZUUFXQYIUUHYAXQYGUUGYHXQJXRULGZLTZJUUIMTZYG
      UUGUUJUUKUOXQJUUIUPUQXQXTYGUUJNZYMAXRURZKXQYPUUIJMXQUUIYPXQYJUUIYPNZYKABU
      SZKZUTVAVFVBVCYOYPOFZUUHUUFNYOYJUUQXQYJYNYKVDZABVEKZYPVGKVHYAYPVIKYOYJUUD
      UUENUURABURKVJYOYPYAYOYPUUSVKZYOXQYAYGFZUKZYAVLFZYAVMFYNUVAXQYAYGYHVNZVOU
      VBYAUUJFZUVCXQUVAUVEXQYGUUJYAXQYJXTUULYKYLUUMVPZVQVRYAJUUIVSKYAVTVPZYOYAY
      PYOUVAYPYGWAZYAYPWBYNUVAXQUVDWHZYOUUIYGWAZUVHYOXTUVJYOYJXTUURYLKZAXRWCKYO
      UUIYPYGYGYOYJUUNUURUUOKZYOYGWDWEWFYAYPYGWGPWIWJWKWLYOYTUUCBYOYPSYAUUTYOWM
      ZUVGWNWOYOYRUUBBYOYPYASUUTUVGUVMWPWOQYSUUACYRBXHYTBXHWRWQYOYJYBUUEFZYCYSN
      UURYOYBOFZUUQYBSWSTZYPRIUVNYOYAWTFZUVOYOYAOFZYAJWBZUVQYOUVEUVRYOYAYGUUJUV
      IYOXTUULUVKUUMKVHZYAUUIXAKYNUVSXQYAYGJXBWHYAXCXDYAXEKUUSYOYAUUIUVPYPRYOUV
      EYAUUIRIUVTYAUUIXFKYOYASUVGUVMXGYOUUIYPUVLUTQYBYPXIXJABYBXKPYOYJYAUUEFZYD
      UUANUURXQYNUWAYNUVAXQUWAUVDXQYGUUEYAXQYGUUJUUEUVFXQUUIYPJLUUPVAXLVQXMXNAB
      YAXKPQXOAXRYEDXPXD $.
  $}

  ${
    $d A a $.  $d T a $.  $d .< a $.
    $( There is a finite number of chains with fixed length over finite
       alphabet.  Trivially holds for invalid lengths as there're no matching
       sequences.  (Contributed by Ender Ting, 5-Jan-2025.)  (Revised by Ender
       Ting, 17-Jan-2026.) $)
    chnflenfi $p |- ( A e. Fin -> { a e. ( .< Chain A ) | ( # ` a ) = T } e.
      Fin ) $=
      ( cfn wcel chash cfv wceq cword crab cchn wss wrdnfi wtru chnwrd ad2antrl
      cv id rabss3d mptru ssfi sylancl ) AEFDRZGHCIZDAJZKZEFUEDABLZKZUGMZUIEFDC
      ANUJOUEDUHUFUDUHFZUDUFFOUEUKAUDBUKSPQTUAUGUIUBUC $.
  $}

  $( A chain is a zero-based finite sequence with a recoverable upper limit.
     (Contributed by Ender Ting, 20-Jan-2026.) $)
  chnf $p |- ( B e. ( .< Chain A ) -> B : ( 0 ..^ ( # ` B ) ) --> A ) $=
    ( cchn wcel cword cc0 chash cfv cfzo co wf id chnwrd wrdf syl ) BACDEZBAFEG
    BHIJKABLQABCQMNABOP $.

  ${
    $d ph i j $.  $d B i j $.
    chnpof1.1 $e |- ( ph -> .< Po A ) $.
    chnpof1.2 $e |- ( ph -> B e. ( .< Chain A ) ) $.
    $( A chain under relation which orders the alphabet is a one-to-one
       function from its domain to alphabet.  (Contributed by Ender Ting,
       20-Jan-2026.) $)
    chnpof1 $p |- ( ph -> B : ( 0 ..^ ( # ` B ) ) -1-1-> A ) $=
      ( vi vj cc0 cfv cfzo co wa wcel syl wbr wn adantr simpr jca chash wf wceq
      cv weq wral wf1 cchn chnf clt wpo wne ffvelcdm syl2anc adantrr adantl cn0
      wi w3a simplrl elfzonn0 elfzoelz 3jca elfzo0z sylibr chnlt syl3anc neneqd
      cz po2ne ex con2d imp simplrr necomd cr zred anim12i lttri4 3orcoma sylib
      w3o ecase23d ralrimivva dff13 ) AICUAJZKLZBCUBZGUDZCJZHUDZCJZUCZGHUEZURZH
      WGUFGWGUFZMWGBCUGAWHWPACBDUHNZWHFBCDUIZOZAWOGHWGWGAWIWGNZWKWGNZMZMZWMWNXC
      WMMZWNWIWKUJPZWKWIUJPZXCWMXEQXCXEWMXCXEWMQZXCXEMZWJWLXHBDUKZWJBNZWLBNZMZW
      JWLDPWJWLULZXCXIXEAXIXBERZRZXCXLXEXCXJXKAWTXJXAAWTMZWHWTXJXPWQWHAWQWTFRWR
      OAWTSWGBWICUMUNUOZXCWHXAXKAWHXBWSRXBXAAWTXASUPZWGBWKCUMUNZTRXHBCDWIWKXOXC
      WQXEAWQXBFRZRXCXAXEXRRZXHWIUQNZWKVINZXEUSWIIWKKLNXHYBYCXEXHWTYBAWTXAXEUTW
      IWFVAOXHXAYCYAWKIWFVBZOXCXESVCWIWKVDVEVFWJWLDBVJVGVHVKVLVMXCWMXFQXCXFWMXC
      XFXGXCXFMZWJWLYEXIXKXJMZWLWJDPZXMXCXIXFXNRZXCYFXFXCXKXJXSXQTRYEBCDWKWIYHX
      CWQXFXTRAWTXAXFUTZYEWKUQNZWIVINZXFUSWKIWIKLNYEYJYKXFYEXAYJAWTXAXFVNWKWFVA
      OYEWTYKYIWIIWFVBZOXCXFSVCWKWIVDVEVFXIYFYGUSWLWJWLWJDBVJVOVGVHVKVLVMXDXEWN
      XFWBZWNXEXFWBXDWIVPNZWKVPNZMZYMXCYPWMXBYPAWTYNXAYOWTWIYLVQXAWKYDVQVRUPRWI
      WKVSOXEWNXFVTWAWCVKWDTGHWGBCWEVE $.
  $}

  ${
    chnpoadomd.1 $e |- ( ph -> .< Po A ) $.
    chnpoadomd.2 $e |- ( ph -> B e. ( .< Chain A ) ) $.
    chnpoadomd.3 $e |- ( ph -> A e. V ) $.
    $( A chain under relation which orders the alphabet cannot have more
       elements than the alphabet itself.  (Contributed by Ender Ting,
       20-Jan-2026.) $)
    chnpoadomd $p |- ( ph -> ( 0 ..^ ( # ` B ) ) ~<_ A ) $=
      ( cc0 chash cfv cfzo co wf1 cdom wbr chnpof1 wcel wi f1domg syl mpd ) AIC
      JKLMZBCNZUCBOPZABCDFGQABERUDUESHUCBECTUAUB $.

    $( A chain under relation which orders the alphabet has at most alphabet's
       size elements in it.  (Contributed by Ender Ting, 20-Jan-2026.) $)
    chnpolleha $p |- ( ph -> ( # ` B ) <_ ( # ` A ) ) $=
      ( chash cfv cc0 cfzo co cle cn0 wcel wceq cword chnwrd syl lencl hashfzo0
      eqcomd cchn wf1 wbr chnpof1 hashf1dmcdm syl3anc eqbrtrd ) ACIJZKUKLMZIJZB
      IJZNAUKOPZUKUMQACBRPUOABCDGSBCUATUOUMUKUKUBUCTACBDUDZPBEPULBCUEUMUNNUFGHA
      BCDFGUGULBCUPEUHUIUJ $.
  $}

  ${
    chnpolfz.1 $e |- ( ph -> .< Po A ) $.
    chnpolfz.2 $e |- ( ph -> B e. ( .< Chain A ) ) $.
    chnpolfz.3 $e |- ( ph -> A e. Fin ) $.
    $( Provided that chain's relation is a partial order, the chain length is
       restricted to a specific integer range.  (Contributed by Ender Ting,
       20-Jan-2026.) $)
    chnpolfz $p |- ( ph -> ( # ` B ) e. ( 0 ... ( # ` A ) ) ) $=
      ( chash cfv cc0 0zd cfn wcel cn0 hashcl syl nn0zd cword chnwrd lencl cchn
      cle wbr hashge0 chnpolleha elfzd ) ACHIZJBHIZAKAUHABLMUHNMGBOPQAUGACBRMUG
      NMABCDFSBCTPQACBDUAZMJUGUBUCFCUIUDPABCDLEFGUEUF $.
  $}

  ${
    $d A n x $.  $d .< n x $.

    $( There is a finite number of chains over finite domain, as long as the
       relation orders it.  (Contributed by Ender Ting, 20-Jan-2026.) $)
    chnfi $p |- ( ( A e. Fin /\ .< Po A ) -> ( .< Chain A ) e. Fin ) $=
      ( vn vx cfn wcel wpo wa cchn cc0 chash cfv cfz wceq crab ciun wrex iunrab
      co cv simplr simpr simpll chnpolfz risset eqcom bitri sylib rabeqcda wral
      rexbii eqtr2id fzfid chnflenfi adantr ralrimivw iunfi syl2anc eqeltrd ) A
      EFZABGZHZABIZCJAKLZMSZDTZKLZCTZNZDVCOZPZEVBVKVICVEQZDVCOVCVICDVEVCRVBVLDV
      CVBVFVCFZHZVGVEFZVLVNAVFBUTVAVMUAVBVMUBUTVAVMUCUDVOVHVGNZCVEQVLCVGVEUEVPV
      ICVEVHVGUFUKUGUHUIULVBVEEFVJEFZCVEUJVKEFVBJVDUMVBVQCVEUTVQVAABVHDUNUOUPCV
      EVJUQURUS $.
  $}

  ${
    $d .< x y $.  $d A x y $.

    $( There is an infinite number of chains for any infinite alphabet and any
       relation.  For instance, all the singletons of alphabet characters
       match.  (Contributed by Ender Ting, 20-Jan-2026.) $)
    chninf $p |- ( A e/ Fin -> ( .< Chain A ) e/ Fin ) $=
      ( vy vx cfn wnel cchn wi wtru wcel cv cs1 cmpt wf1 wral wceq weq wa s1chn
      id rgen s111 biimpd rgen2 pm3.2i eqid s1eq f1mpt mpbir mpan2 a1i nelcon3d
      f1fi mptru ) AEFABGZEFHIUOEAEUOEJZAEJZHIUPAUOCACKZLZMZNZUQVAUSUOJZCAOZUSD
      KZLZPZCDQZHZDAOCAOZRVCVIVBCAURAJZABURVJTSUAVHCDAAVJVDAJRVFVGAURVDUBUCUDUE
      CDAUOUSVEUTUTUFURVDUGUHUIAUOUTUMUJUKULUN $.
  $}

  $( Given a partial order, the set of chains is finite iff the alphabet is
     finite.  (Contributed by Ender Ting, 20-Jan-2026.) $)
  chnfibg $p |- ( .< Po A -> ( A e. Fin <-> ( .< Chain A ) e. Fin ) ) $=
    ( wpo cfn wcel cchn chnfi expcom wnel chninf df-nel 3imtr3i con4i impbid1
    wn ) ABCZADEZABFZDEZQPSABGHQSADIRDIQOSOABJADKRDKLMN $.

  $( Example: a doubleton of twos is a valid chain under the identity relation
     and domain of integers.  (Contributed by Ender Ting, 17-Jan-2026.) $)
  ex-chn1 $p |- <" 2 2 "> e. ( _I Chain ZZ ) $=
    ( vx c2 cz cid wcel c1 cmin co cfv wbr cc0 csn cdif 2z wceq 2ex fveq2 ax-mp
    cvv eqtr2di cs2 cchn cword cv cdm wral s2cl mp2an cpr difeq1i eleq2i biimpi
    s2dm difprsnss sseli elsnd eqid ideq mpbir a1i oveq1 1m1e0 eqtrdi s2fv0 syl
    s2fv1 3brtr3d 3syl rgen ischn mpbir2an ) BBUAZCDUBEVLCUCEZAUDZFGHZVLIZVNVLI
    ZDJZAVLUEZKLZMZUFBCEZWBVMNNBBCUGUHVRAWAVNWAEZVNKFUIZVTMZEZVNFOZVRWCWFWAWEVN
    VSWDVTBBUMUJUKULWFVNFWEFLVNKFUNUOUPWGBBVPVQDBBDJZWGWHBBOBUQBBPURUSUTWGVOKOZ
    BVPOWGVOFFGHKVNFFGVAVBVCWIVPKVLIZBVOKVLQBSEZWJBOPBBSVDRTVEWGVQFVLIZBVNFVLQW
    KWLBOPBBSVFRTVGVHVICVLDAVJVK $.

  $( Example: sequence <" ZZ NN QQ "> is a valid chain under the equinumerosity
     relation in universal domain.  (Contributed by Ender Ting,
     17-Jan-2026.) $)
  ex-chn2 $p |- <" ZZ NN QQ "> e. ( ~~ Chain _V ) $=
    ( vx cz cn cq cvv cen wcel c1 cmin co cfv wbr cc0 cdif c2 wceq eqtrdi ax-mp
    ctp zex cs3 cchn cword cv cdm csn wral s3cli cpr wo wfn nnex qex s3fn mp3an
    fndmi difeq1i tprot wne ax-1ne0 2ne0 mp2an 3eqtri eleq2i biimpi elpri znnen
    diftpsn3 a1i oveq1 1m1e0 fveq2d s3fv0 fveq2 s3fv1 3brtr4d qnnen 2m1e1 s3fv2
    ensymi jaoi 3syl rgen ischn mpbir2an ) BCDUAZEFUBGWFEUCGAUDZHIJZWFKZWGWFKZF
    LZAWFUEZMUFZNZUGBCDUHWKAWNWGWNGZWGHOUIZGZWGHPZWGOPZUJWKWOWQWNWPWGWNMHOSZWMN
    HOMSZWMNZWPWLWTWMWTWFBEGZCEGZDEGZWFWTUKTULUMBCDEUNUOUPUQWTXAWMMHOURUQHMUSOM
    USXBWPPUTVAHOMVHVBVCVDVEWGHOVFWRWKWSWRBCWIWJFBCFLWRVGVIWRWIMWFKZBWRWHMWFWRW
    HHHIJMWGHHIVJVKQVLXCXFBPTBCDEVMRQWRWJHWFKZCWGHWFVNXDXGCPULBCDEVORZQVPWSCDWI
    WJFCDFLWSDCVQVTVIWSWIXGCWSWHHWFWSWHOHIJHWGOHIVJVRQVLXHQWSWJOWFKZDWGOWFVNXEX
    IDPUMBCDEVSRQVPWAWBWCEWFFAWDWE $.


