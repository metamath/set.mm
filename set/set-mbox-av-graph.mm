$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Graph theory (extension)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Closed neighborhood of a vertex
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c ClNeighbVtx $.

  $( Extend class notation with closed neighborhoods (of a vertex in a
     graph). $)
  cclnbgr $a class ClNeighbVtx $.

  ${
    $d e g n v $.
    $( Define the closed _neighborhood_ resp. the class of all neighbors of a
       vertex (in a graph) and the vertex itself, see definition in section I.1
       of [Bollobas] p. 3.  The closed neighborhood of a vertex is the set of
       all vertices which are connected with this vertex by an edge and the
       vertex itself (in contrast to an open neighborhood, see ~ df-nbgr ).
       Alternatively, a closed neighborhood of a vertex could have been defined
       as its open neighborhood enhanced by the vertex itself, see
       ~ dfclnbgr4 .  This definition is applicable even for arbitrary
       hypergraphs.  (Contributed by AV, 7-May-2025.) $)
    df-clnbgr $a |- ClNeighbVtx = ( g e. _V , v e. ( Vtx ` g )
                   |-> ( { v } u. { n e. ( Vtx ` g ) |
                                    E. e e. ( Edg ` g ) { v , n } C_ e } ) ) $.

    $( The closed neighborhood is empty if the graph ` G ` or the vertex ` N `
       are proper classes.  (Contributed by AV, 7-May-2025.) $)
    clnbgrprc0 $p |- ( -. ( G e. _V /\ N e. _V )
                       -> ( G ClNeighbVtx N ) = (/) ) $=
      ( vg vv vn ve cclnbgr cvv cv cvtx cfv csn cpr wss cedg wrex cun df-clnbgr
      crab reldmmpo ovprc ) ABGCDHCIZJKZDIZLUDEIMFINFUBOKPEUCSQGDFCERTUA $.
  $}

  ${
    $d G g $.  $d X g $.  $d e g n v $.
    clnbgrcl.v $e |- V = ( Vtx ` G ) $.
    $( If a class ` X ` has at least one element in its closed neighborhood,
       this class must be a vertex.  (Contributed by AV, 7-May-2025.) $)
    clnbgrcl $p |- ( N e. ( G ClNeighbVtx X ) -> X e. V ) $=
      ( vg vv vn ve cclnbgr co wcel cvv cv cvtx cfv csb csn cpr wss cedg eqtr4i
      wrex crab cun df-clnbgr mpoxeldm csbfv eleq2i biimpi simpl2im ) BADJKLAML
      DFAFNZOPZQZLZDCLZFGMUMGNZRUQHNSINTIULUAPUCHUMUDUEJBADGIFHUFUGUOUPUNCDUNAO
      PCFAOUHEUBUIUJUK $.
  $}

  ${
    $d E e g v $.  $d G e g n v $.  $d N e g n v $.  $d V e g n v $.
    clnbgrval.v $e |- V = ( Vtx ` G ) $.
    clnbgrval.e $e |- E = ( Edg ` G ) $.
    $( The closed neighborhood of a vertex ` V ` in a graph ` G ` .
       (Contributed by AV, 7-May-2025.) $)
    clnbgrval $p |- ( N e. V -> ( G ClNeighbVtx N )
                      = ( { N } u. { n e. V | E. e e. E { N , n } C_ e } ) ) $=
      ( vg vv wcel cclnbgr cvv cv cvtx cfv cedg wceq fveq2 adantl csn wrex crab
      cpr wss cun co df-clnbgr 1vgrex eqcoms eqtrid eleq2d biimpac wa vsnex a1i
      cmpo fvex rabexg mp1i unexd sneq eqtr4di adantr wb preq1 sseq1d rexeqbidv
      rabeqbidv uneq12d ovmpodv2 mpi ) EFKZLIJMINZOPZJNZUAZVPBNZUDZANZUEZAVNQPZ
      UBZBVOUCZUFZUQRDELUGEUAZEVRUDZVTUEZACUBZBFUCZUFZRJAIBUHVMIJDEMVOWEWKLMDEF
      GUIVNDRZVMEVOKWLFVOEWLFDOPZVOGWMVORDVNDVNOSUJUKULUMVMWLVPERZUNZUNZVQWDMMV
      QMKWPJUOUPVOMKWDMKWPVNOURWCBVOMUSUTVAWOWEWKRVMWOVQWFWDWJWNVQWFRWLVPEVBTWO
      WCWIBVOFWLVOFRWNWLVOWMFVNDOSGVCVDWOWAWHAWBCWLWBCRWNWLWBDQPCVNDQSHVCVDWNWA
      WHVEWLWNVSWGVTVPEVRVFVGTVHVIVJTVKVL $.

    $( Alternate definition of the closed neighborhood of a vertex breaking up
       the subset relationship of an unordered pair.  (Contributed by AV,
       7-May-2025.) $)
    dfclnbgr2 $p |- ( N e. V -> ( G ClNeighbVtx N )
                = ( { N } u. { n e. V | E. e e. E ( N e. e /\ n e. e ) } ) ) $=
      ( wcel cclnbgr co csn cv cpr wss wrex crab cun wel wa clnbgrval cvv prssg
      wb elvd bicomd rexbidv rabbidv uneq2d eqtrd ) EFIZDEJKELZEBMZNAMZOZACPZBF
      QZRULEUNIBASTZACPZBFQZRABCDEFGHUAUKUQUTULUKUPUSBFUKUOURACUKURUOUKURUOUDBE
      UMUNFUBUCUEUFUGUHUIUJ $.
  $}

  ${
    $d G e n $.  $d N e n $.  $d V e n $.
    dfclnbgr4.v $e |- V = ( Vtx ` G ) $.
    $( Alternate definition of the closed neighborhood of a vertex as union of
       the vertex with its open neighborhood.  (Contributed by AV,
       8-May-2025.) $)
    dfclnbgr4 $p |- ( N e. V -> ( G ClNeighbVtx N )
                                = ( { N } u. ( G NeighbVtx N ) ) ) $=
      ( ve vn wcel cclnbgr co csn cv wel wa cedg cfv wrex crab cun cnbgr cdif
      dfclnbgr2 undif2 rabdif uneq2i eqtr3i dfnbgr2 eqcomd uneq2d eqtrid eqtrd
      eqid ) BCGZABHIBJZBEKGFELMEANOZPZFCQZRZUMABSIZRZEFUNABCDUNUKZUAULUQUMUOFC
      UMTQZRZUSUMUPUMTZRUQVBUMUPUBVCVAUMUOFCUMUCUDUEULVAURUMULURVAEFUNABCDUTUFU
      GUHUIUJ $.
  $}

  $( An element of the closed neighborhood of a vertex which is not the vertex
     itself is an element of the open neighborhood of the vertex.  (Contributed
     by AV, 24-Sep-2025.) $)
  elclnbgrelnbgr $p |- ( ( X e. ( G ClNeighbVtx N ) /\ X =/= N )
                         -> X e. ( G NeighbVtx N ) ) $=
    ( cclnbgr co wcel wne cnbgr wi csn cun cvtx cfv wceq clnbgrcl dfclnbgr4 syl
    eqid eleq2d wo elun eqneqall biimtrdi ax1w jaod biimtrid sylbid pm2.43i imp
    elsng ) CABDEZFZCBGZCABHEZFZULUMUOIZULULCBJZUNKZFZUPULUKURCULBALMZFUKURNACU
    TBUTRZOABUTVAPQSUSCUQFZUOTULUPCUQUNUAULVBUPUOULVBCBNUPCBUKUJUOCBUBUCULUOUMU
    DUEUFUGUHUI $.

  ${
    $d G e n $.  $d I e i n $.  $d N e i n $.  $d V e n $.
    dfclnbgr3.v $e |- V = ( Vtx ` G ) $.
    dfclnbgr3.i $e |- I = ( iEdg ` G ) $.
    $( Alternate definition of the closed neighborhood of a vertex using the
       edge function instead of the edges themselves (see also ~ clnbgrval ).
       (Contributed by AV, 8-May-2025.) $)
    dfclnbgr3 $p |- ( ( N e. V /\ Fun I ) -> ( G ClNeighbVtx N )
          = ( { N } u. { n e. V | E. i e. dom I { N , n } C_ ( I ` i ) } ) ) $=
      ( ve wcel wfun wa cv wss cfv crn wrex crab cun eqcomi cclnbgr csn cpr cdm
      co ciedg wceq edgval clnbgrval adantr rneqi rexeqi wfn funfn bilani sseq2
      cedg wb rexrn syl bitrid rabbidv uneq2d eqtrd ) EFJZDKZLZCEUAUEZEUBZEBMUC
      ZIMZNZICUFOZPZQZBFRZSZVIVJAMDOZNZADUDZQZBFRZSVEVHVQUGVFIBVNCEFGCUQOVNCUHT
      UIUJVGVPWBVIVGVOWABFVOVLIDPZQZVGWAVLIVNWCVMDDVMHTUKULVGDVTUMZWDWAURVFWEVE
      DUNUOVLVSIAVTDVKVRVJUPUSUTVAVBVCVD $.
  $}

  ${
    $d e g n v $.  $d G g $.  $d X g $.
    clnbgrel.v $e |- V = ( Vtx ` G ) $.
    $( If a class ` X ` is not a vertex of a graph ` G ` , then it has an empty
       closed neighborhood in ` G ` .  (Contributed by AV, 8-May-2025.) $)
    clnbgrnvtx0 $p |- ( X e/ V -> ( G ClNeighbVtx X ) = (/) ) $=
      ( vg vv vn ve wnel cvv cv cvtx cfv csb wo cclnbgr co c0 wceq wb csbfv csn
      eqtr4i neleq2 ax-mp biimpi olcd cpr wss cedg wrex cun df-clnbgr mpoxneldm
      crab syl ) CBIZAJIZCEAEKZLMZNZIZOACPQRSUQVBURUQVBBVASUQVBTBALMVADEALUAUCB
      VACUDUEUFUGEFJUTFKZUBVCGKUHHKUIHUSUJMUKGUTUOULPACFHEGUMUNUP $.

    $d E e n $.  $d G e n $.  $d N e n $.  $d X e n $.  $d V e n $.
    clnbgrel.e $e |- E = ( Edg ` G ) $.
    $( Characterization of a member ` N ` of the closed neighborhood of a
       vertex ` X ` in a graph ` G ` .  (Contributed by AV, 9-May-2025.) $)
    clnbgrel $p |- ( N e. ( G ClNeighbVtx X ) <-> ( ( N e. V /\ X e. V )
                                /\ ( N = X \/ E. e e. E { X , N } C_ e ) ) ) $=
      ( vn wcel wa wceq cpr cv wss wrex wo a1i orc wi cclnbgr clnbgrcl pm4.71ri
      co csn crab cun clnbgrval eleq2d elun elsn2g preq2 sseq1d rexbidv orbi12d
      wb elrab bitrid eleq1 biimparc adantl jca ex anim2i expimpd impbid 3bitrd
      olc jaod pm5.32i anass bicomi ancom bianbi 3bitri ) DCFUAUDZJZFEJZVQKVRDE
      JZDFLZFDMZANZOZABPZQZKZKZVSVRKZWEKVQVRCDEFGUBUCVRVQWFVRVQDFUEZFINZMZWBOZA
      BPZIEUFZUGZJZVTVSWDKZQZWFVRVPWODAIBCFEGHUHUIWPDWIJZDWNJZQVRWRDWIWNUJVRWSV
      TWTWQDFEUKWTWQUPVRWMWDIDEWJDLZWLWCABXAWKWAWBWJDFULUMUNUQRUOURVRWRWFVRVTWF
      WQVRVTWFVRVTKVSWEVTVSVRDFEUSUTVTWEVRVTWDSVAVBVCWQWFTVRWDWEVSWDVTVHVDRVIVR
      VSWEWRVRVSKZVTWRWDVTWRTXBVTWQSRVSWDWRTVRVSWDWRWQVTVHVCVAVIVEVFVGVJWGXBWEW
      HXBWEKWGVRVSWEVKVLVRVSVMVNVO $.
  $}

  ${
    $d G e $.  $d K e $.  $d V e $.
    clnbgrvtxel.v $e |- V = ( Vtx ` G ) $.
    $( Every vertex ` K ` is a member of its closed neighborhood.  (Contributed
       by AV, 10-May-2025.) $)
    clnbgrvtxel $p |- ( K e. V -> K e. ( G ClNeighbVtx K ) ) $=
      ( ve wcel wceq cpr cv wss cedg cfv wrex wo cclnbgr co id eqidd orcd eqid
      clnbgrel syl21anbrc ) BCFZUCUCBBGZBBHEIJEAKLZMZNBABOPFUCQZUGUCUDUFUCBRSEU
      EABCBDUETUAUB $.

    $d N e $.
    $( Every member ` N ` of the closed neighborhood of a vertex ` K ` is a
       vertex.  (Contributed by AV, 9-May-2025.) $)
    clnbgrisvtx $p |- ( N e. ( G ClNeighbVtx K ) -> N e. V ) $=
      ( ve cclnbgr co wcel wa wceq cpr cv wss cedg cfv wrex wo eqid clnbgrel
      simpll sylbi ) CABGHICDIZBDIZJCBKBCLFMNFAOPZQRZJUCFUEACDBEUESTUCUDUFUAUB
      $.

    $d G n $.  $d K n $.  $d V n $.
    $( The closed neighborhood of a vertex ` K ` in a graph is a subset of all
       vertices of the graph.  (Contributed by AV, 9-May-2025.) $)
    clnbgrssvtx $p |- ( G ClNeighbVtx K ) C_ V $=
      ( vn cclnbgr co cv clnbgrisvtx ssriv ) EABFGCABEHCDIJ $.
  $}

  ${
    clnbgrn0.v $e |- V = ( Vtx ` G ) $.
    $( The closed neighborhood of a vertex is never empty.  (Contributed by AV,
       16-May-2025.) $)
    clnbgrn0 $p |- ( N e. V -> ( G ClNeighbVtx N ) =/= (/) ) $=
      ( wcel cclnbgr co c0 wne clnbgrvtxel ne0i syl ) BCEBABFGZEMHIABCDJMBKL $.
  $}

  ${
    $d E n $.  $d G n $.  $d N n $.  $d V n $.
    clnbuhgr.v $e |- V = ( Vtx ` G ) $.
    clnbuhgr.e $e |- E = ( Edg ` G ) $.
    $( The closed neighborhood of a vertex in a pseudograph.  (Contributed by
       AV, 10-May-2025.) $)
    clnbupgr $p |- ( ( G e. UPGraph /\ N e. V )
         -> ( G ClNeighbVtx N ) = ( { N } u. { n e. V | { N , n } e. E } ) ) $=
      ( cupgr wcel wa cclnbgr co csn cnbgr cun cv cpr cdif crab wceq adantl a1i
      dfclnbgr4 nbupgr uneq2d rabdif eqcomi uneq2i undif2 eqtri 3eqtrd ) CHIZDE
      IZJZCDKLZDMZCDNLZOZUPDAPQBIZAEUPRSZOZUPUSAESZOZUMUOURTULCDEFUCUAUNUQUTUPA
      BCDEFGUDUEVAVCTUNVAUPVBUPRZOVCUTVDUPVDUTUSAEUPUFUGUHUPVBUIUJUBUK $.

    $d K n $.
    $( A member of the closed neighborhood of a vertex in a pseudograph.
       (Contributed by AV, 10-May-2025.) $)
    clnbupgrel $p |- ( ( G e. UPGraph /\ K e. V /\ N e. V )
           -> ( N e. ( G ClNeighbVtx K ) <-> ( N = K \/ { N , K } e. E ) ) ) $=
      ( vn cupgr wcel w3a cclnbgr co csn cpr wceq wa wo wb 3ad2ant3 cv crab cun
      clnbupgr eleq2d 3adant3 elun preq2 eleq1d elrab orbi2i bitri elsng orbi1d
      bitrid ibar prcom eleq1i bitr3di orbi2d 3bitrd ) BIJZCEJZDEJZKZDBCLMZJZDC
      NZCHUAZOZAJZHEUBZUCZJZDCPZVDCDOZAJZQZRZVODCOZAJZRZVBVCVGVNSVDVBVCQVFVMDHA
      BCEFGUDUEUFVNDVHJZVRRZVEVSVNWCDVLJZRWDDVHVLUGWEVRWCVKVQHDEVIDPVJVPAVIDCUH
      UIUJUKULVEWCVOVRVDVBWCVOSVCDCEUMTUNUOVDVBVSWBSVCVDVRWAVOVDVQVRWAVDVQUPVPV
      TACDUQURUSUTTVA $.
  $}

  ${
    clnbupgreli.e $e |- E = ( Edg ` G ) $.
    $( A member of the closed neighborhood of a vertex in a pseudograph.
       (Contributed by AV, 28-Dec-2025.) $)
    clnbupgreli $p |- ( ( G e. UPGraph /\ N e. ( G ClNeighbVtx K ) )
                        -> ( N = K \/ { N , K } e. E ) ) $=
      ( cupgr wcel cclnbgr co wa wceq cpr wo simpr cvtx cfv simpl eqid adantl
      wb clnbgrcl clnbgrisvtx clnbupgrel syl3anc mpbid ) BFGZDBCHIGZJZUGDCKDCLA
      GMZUFUGNUHUFCBOPZGZDUJGZUGUITUFUGQUGUKUFBDUJCUJRZUASUGULUFBCDUJUMUBSABCDU
      JUMEUCUDUE $.
  $}

  $( In a null graph (with no vertices), all closed neighborhoods are empty.
     (Contributed by AV, 15-Nov-2020.) $)
  clnbgr0vtx $p |- ( ( Vtx ` G ) = (/) -> ( G ClNeighbVtx K ) = (/) ) $=
    ( cvtx c0 wceq wnel cclnbgr co wcel wn nel02 df-nel sylibr eqid clnbgrnvtx0
    cfv syl ) ACPZDEZBRFZABGHDESBRIJTRBKBRLMARBRNOQ $.

  $( In an empty graph (with no edges), all closed neighborhoods consists of a
     single vertex.  (Contributed by AV, 10-May-2025.) $)
  clnbgr0edg $p |- ( ( ( Edg ` G ) = (/) /\ K e. ( Vtx ` G ) )
                     -> ( G ClNeighbVtx K ) = { K } ) $=
    ( cedg cfv c0 wceq cvtx wcel wa cclnbgr csn cnbgr cun eqid dfclnbgr4 adantl
    co nbgr0edg adantr uneq2d un0 a1i 3eqtrd ) ACDEFZBAGDZHZIZABJQZBKZABLQZMZUI
    EMZUIUFUHUKFUDABUEUENOPUGUJEUIUDUJEFUFABRSTULUIFUGUIUAUBUC $.

  ${
    $d G e $.  $d K e $.  $d N e $.
    $( In a graph, the closed neighborhood relation is symmetric: a vertex
       ` N ` in a graph ` G ` is a neighbor of a second vertex ` K ` iff the
       second vertex ` K ` is a neighbor of the first vertex ` N ` .
       (Contributed by AV, 10-May-2025.) $)
    clnbgrsym $p |- ( N e. ( G ClNeighbVtx K )
                      <-> K e. ( G ClNeighbVtx N ) ) $=
      ( ve cvtx cfv wcel wa wceq cpr cv wss cedg wrex wo cclnbgr ancom clnbgrel
      co eqid eqcom prcom sseq1i rexbii orbi12i anbi12i 3bitr4i ) CAEFZGZBUHGZH
      ZCBIZBCJZDKZLZDAMFZNZOZHUJUIHZBCIZCBJZUNLZDUPNZOZHCABPSGBACPSGUKUSURVDUIU
      JQULUTUQVCCBUAUOVBDUPUMVAUNBCUBUCUDUEUFDUPACUHBUHTZUPTZRDUPABUHCVEVFRUG
      $.
  $}

  ${
    $d E e $.  $d G e $.  $d N e $.  $d V e $.  $d X e $.
    predgclnbgrel.v $e |- V = ( Vtx ` G ) $.
    predgclnbgrel.e $e |- E = ( Edg ` G ) $.
    $( If a (not necessarily proper) unordered pair containing a vertex is an
       edge, the other vertex is in the closed neighborhood of the first
       vertex.  (Contributed by AV, 23-Aug-2025.) $)
    predgclnbgrel $p |- ( ( N e. V /\ X e. V /\ { X , N } e. E )
                         -> N e. ( G ClNeighbVtx X ) ) $=
      ( ve wcel cpr w3a wa wceq cv wss wrex wo cclnbgr co 3simpa simp3 wb sseq2
      adantl ssidd rspcedvd olcd clnbgrel sylanbrc ) CDIZEDIZECJZAIZKZUJUKLCEMZ
      ULHNZOZHAPZQCBERSIUJUKUMTUNURUOUNUQULULOZHULAUJUKUMUAUPULMUQUSUBUNUPULULU
      CUDUNULUEUFUGHABCDEFGUHUI $.
  $}

  ${
    $d E e $.  $d G e $.  $d K e $.  $d X e $.  $d Y e $.
    clnbgredg.e $e |- E = ( Edg ` G ) $.
    clnbgredg.n $e |- N = ( G ClNeighbVtx X ) $.
    $( A vertex connected by an edge with another vertex is a neighbor of that
       vertex.  (Contributed by AV, 24-Aug-2025.) $)
    clnbgredg $p |- ( ( G e. UHGraph /\ ( K e. E /\ X e. K /\ Y e. K ) )
                        -> Y e. N ) $=
      ( ve wcel w3a wa cfv wceq wss eleq2i jca anim2i 3anass sylibr cclnbgr cpr
      cuhgr co cvtx cv wrex wo cedg biimpi 3ad2ant1 simp3 uhgredgrnv syl simpr1
      simp2 sseq2 adantl prssi 3adant1 rspcedvd olcd eqid clnbgrel syl21anbrc
      wb ) BUCJZCAJZECJZFCJZKZLZFBEUAUDZJZFDJVLFBUEMZJZEVOJZFENZEFUBZIUFZOZIAUG
      ZUHVNVLVGCBUIMZJZVJKZVPVLVGWDVJLZLWEVKWFVGVKWDVJVHVIWDVJVHWDAWCCGPUJUKZVH
      VIVJULQRVGWDVJSTCBFUMUNVLVGWDVIKZVQVLVGWDVILZLWHVKWIVGVKWDVIWGVHVIVJUPQRV
      GWDVISTCBEUMUNVLWBVRVLWAVSCOZICAVGVHVIVJUOVTCNWAWJVFVLVTCVSUQURVKWJVGVIVJ
      WJVHEFCUSUTURVAVBIABFVOEVOVCGVDVEDVMFHPT $.
  $}

  ${
    $d E v $.  $d K v $.  $d N v $.  $d G v $.  $d X v $.
    clnbgrssedg.e $e |- E = ( Edg ` G ) $.
    clnbgrssedg.n $e |- N = ( G ClNeighbVtx X ) $.
    $( The vertices connected by an edge are a subset of the neighborhood of
       each of these vertices.  (Contributed by AV, 26-May-2025.)  (Proof
       shortened by AV, 24-Aug-2025.) $)
    clnbgrssedg $p |- ( ( G e. UHGraph /\ K e. E /\ X e. K ) -> K C_ N ) $=
      ( vv cuhgr wcel w3a cv wi clnbgredg 3exp2 3imp ssrdv ) BIJZCAJZECJZKHCDRS
      THLZCJZUADJZMRSTUBUCABCDEUAFGNOPQ $.
  $}

  ${
    $d E e $.  $d U e $.
    clnbusgrf1o.v $e |- V = ( Vtx ` G ) $.
    clnbusgrf1o.e $e |- E = ( Edg ` G ) $.
    $( The size of the closed neighborhood of a vertex in a simple graph is
       finite iff the number of edges having this vertex as endpoint is finite.
       (Contributed by AV, 10-May-2025.) $)
    edgusgrclnbfin $p |- ( ( G e. USGraph /\ U e. V )
          -> ( ( G ClNeighbVtx U ) e. Fin <-> { e e. E | U e. e } e. Fin ) ) $=
      ( cusgr wcel wa cclnbgr co cfn csn cnbgr cun cv crab wb dfclnbgr4 3bitr4g
      eleq1d adantl edgusgrnbfin anbi2d unfib snfi biantrur bitrd ) DHIZAEIZJZD
      AKLZMIZANZDAOLZPZMIZABQIBCRMIZUKUNURSUJUKUMUQMDAEFTUBUCULUOMIZUPMIZJUTUSJ
      URUSULVAUSUTABCDEFGUDUEUOUPUFUTUSAUGUHUAUI $.

    $( The closed neighborhood of a vertex in a simple graph with a finite
       number of edges is a finite set.  (Contributed by AV, 10-May-2025.) $)
    clnbusgrfi $p |- ( ( G e. USGraph /\ E e. Fin /\ U e. V )
                       -> ( G ClNeighbVtx U ) e. Fin ) $=
      ( ve cusgr wcel cfn cclnbgr co crab rabfi 3ad2ant2 edgusgrclnbfin 3adant2
      w3a cv wb mpbird ) CHIZBJIZADIZRCAKLJIZAGSIZGBMJIZUCUBUGUDUFGBNOUBUDUEUGT
      UCAGBCDEFPQUA $.
  $}

  $( The closed neighborhood of a vertex in a finite simple graph is a finite
     set.  (Contributed by AV, 10-May-2025.) $)
  clnbfiusgrfi $p |- ( ( G e. FinUSGraph /\ N e. ( Vtx ` G ) )
                       -> ( G ClNeighbVtx N ) e. Fin ) $=
    ( cfusgr wcel cvtx cfv wa cusgr cfn cclnbgr fusgrusgr adantr fusgrfis simpr
    cedg co eqid clnbusgrfi syl3anc ) ACDZBAEFZDZGAHDZAOFZIDZUBABJPIDTUCUBAKLTU
    EUBAMLTUBNBUDAUAUAQUDQRS $.

  ${
    clnbgrlevtx.v $e |- V = ( Vtx ` G ) $.
    $( The size of the closed neighborhood of a vertex is at most the number of
       vertices of a graph.  (Contributed by AV, 10-May-2025.) $)
    clnbgrlevtx $p |- ( # ` ( G ClNeighbVtx U ) ) <_ ( # ` V ) $=
      ( cvv wcel cclnbgr co wss chash cfv cle wbr cvtx fvexi clnbgrssvtx hashss
      mp2an ) CEFBAGHZCISJKCJKLMCBNDOBACDPCSEQR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Semiclosed and semiopen neighborhoods (experimental)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  We have already definitions for open and closed neighborhoods of a vertex,
  which differs only in the fact that the first never contains the vertex,
  and the latter always contains the vertex. One of these definitions, however,
  cannot be simply derived from the other.  This would be possible if a
  definition of a semiclosed neighborhood was available, see ~ dfsclnbgr2 .
  The definitions for open and closed neighborhoods could be derived from such
  a more simple, but otherwise probably useless definition, see ~ dfnbgr5 and
  ~ dfclnbgr5 . Depending on the existence of certain edges, a vertex belongs
  to its semiclosed neighborhood or not.

  An alternate approach is to introduce semiopen neighborhoods, see
  ~ dfvopnbgr2 .  The definitions for open and closed neighborhoods could also
  be derived from such a definition, see ~ dfnbgr6 and ~ dfclnbgr6 .  Like with
  semiclosed neighborhood, depending on the existence of certain edges, a
  vertex belongs to its semiopen neighborhood or not.

  It is unclear if either definition is/will be useful, and in contrast to
  ~ dfsclnbgr2 , the definition of semiopen neighborhoods is much more complex.

$)

  ${
    $d N e n $.  $d V e n $.
    dfsclnbgr2.v $e |- V = ( Vtx ` G ) $.
    dfsclnbgr2.s $e |- S = { n e. V | E. e e. E { N , n } C_ e } $.
    dfsclnbgr2.e $e |- E = ( Edg ` G ) $.
    $( Alternate definition of the semiclosed neighborhood of a vertex breaking
       up the subset relationship of an unordered pair.  A _semiclosed
       neighborhood_ ` S ` of a vertex ` N ` is the set of all vertices
       incident with edges which join the vertex ` N ` with a vertex.
       Therefore, a vertex is contained in its semiclosed neighborhood if it is
       connected with any vertex by an edge (see ~ sclnbgrelself ), even only
       with itself (i.e., by a loop).  (Contributed by AV, 16-May-2025.) $)
    dfsclnbgr2 $p |- ( N e. V
                        -> S = { n e. V | E. e e. E ( N e. e /\ n e. e ) } ) $=
      ( wcel cv cpr wss wrex crab wel wa prssg bicomd rexbidv rabbidva eqtrid )
      FGKZAFCLZMBLZNZBDOZCGPFUFKCBQRZBDOZCGPIUDUHUJCGUDUEGKRZUGUIBDUKUIUGFUEUFG
      GSTUAUBUC $.

    $d E e n $.  $d X e n $.
    $( Characterization of a member ` X ` of the semiclosed neighborhood of a
       vertex ` N ` in a graph ` G ` .  (Contributed by AV, 16-May-2025.) $)
    sclnbgrel $p |- ( X e. S <-> ( X e. V /\ E. e e. E { N , X } C_ e ) ) $=
      ( wcel cv cpr wss wrex crab wa eleq2i wceq preq2 sseq1d rexbidv elrab
      bitri ) HALHFCMZNZBMZOZBDPZCGQZLHGLFHNZUHOZBDPZRAUKHJSUJUNCHGUFHTZUIUMBDU
      OUGULUHUFHFUAUBUCUDUE $.

    $( A vertex ` N ` is a member of its semiclosed neighborhood iff there is
       an edge joining the vertex with a vertex.  (Contributed by AV,
       16-May-2025.) $)
    sclnbgrelself $p |- ( N e. S <-> ( N e. V /\ E. e e. E N e. e ) ) $=
      ( wcel cpr cv wss wrex wa sclnbgrel csn dfsn2 eqcomi sseq1i snssg bitr4id
      rexbidv pm5.32i bitri ) FAKFGKZFFLZBMZNZBDOZPUGFUIKZBDOZPABCDEFGFHIJQUGUK
      UMUGUJULBDUGUJFRZUINULUHUNUIUNUHFSTUAFUIGUBUCUDUEUF $.

    $( Every member ` X ` of the semiclosed neighborhood of a vertex ` N ` is a
       vertex.  (Contributed by AV, 16-May-2025.) $)
    sclnbgrisvtx $p |- ( X e. S -> X e. V ) $=
      ( wcel cpr cv wss wrex sclnbgrel simplbi ) HALHGLFHMBNOBDPABCDEFGHIJKQR
      $.

    $d G e n $.
    $( Alternate definition of the closed neighborhood of a vertex as union of
       the vertex with its semiclosed neighborhood.  (Contributed by AV,
       16-May-2025.) $)
    dfclnbgr5 $p |- ( N e. V -> ( G ClNeighbVtx N ) = ( { N } u. S ) ) $=
      ( wcel cclnbgr co csn cv wel wa wrex crab cun dfclnbgr2 dfsclnbgr2 uneq2d
      eqtr4d ) FGKZEFLMFNZFBOKCBPQBDRCGSZTUFATBCDEFGHJUAUEAUGUFABCDEFGHIJUBUCUD
      $.

    $( Alternate definition of the (open) neighborhood of a vertex as a
       semiclosed neighborhood without itself.  (Contributed by AV,
       16-May-2025.) $)
    dfnbgr5 $p |- ( N e. V -> ( G NeighbVtx N ) = ( S \ { N } ) ) $=
      ( wcel cv wel wa wrex csn cdif crab cnbgr co dfnbgr2 dfsclnbgr2 difeq1d
      rabdif eqcomi 3eqtr4a ) FGKZFBLKCBMNBDOZCGFPZQRZUHCGRZUIQZEFSTAUIQULUJUHC
      GUIUDUEBCDEFGHJUAUGAUKUIABCDEFGHIJUBUCUF $.

    $( Subset chain for different kinds of neighborhoods of a vertex.
       (Contributed by AV, 16-May-2025.) $)
    dfnbgrss $p |- ( N e. V -> ( ( G NeighbVtx N ) C_ S
                                /\ S C_ ( G ClNeighbVtx N ) ) ) $=
      ( wcel cnbgr co wss cclnbgr csn cdif dfnbgr5 difss eqsstrdi cun dfclnbgr5
      ssun2 sseqtrrid jca ) FGKZEFLMZANAEFOMZNUFUGAFPZQAABCDEFGHIJRAUISTUFUIAUA
      AUHAUIUCABCDEFGHIJUBUDUE $.

  $}

  ${
    $d E e $.  $d G e $.  $d N e n $.  $d V e n $.
    dfvopnbgr2.v $e |- V = ( Vtx ` G ) $.
    dfvopnbgr2.e $e |- E = ( Edg ` G ) $.
    dfvopnbgr2.u $e |- U = { n e. V | ( n e. ( G NeighbVtx N )
                                     \/ E. e e. E ( N = n /\ e = { N } ) ) } $.
    $( Alternate definition of the semiopen neighborhood of a vertex breaking
       up the subset relationship of an unordered pair.  A _semiopen
       neighborhood_ ` U ` of a vertex ` N ` is its open neighborhood together
       with itself if there is a loop at this vertex.  (Contributed by AV,
       15-May-2025.) $)
    dfvopnbgr2 $p |- ( N e. V -> U = { n e. V | E. e e. E
           ( ( n =/= N /\ N e. e /\ n e. e ) \/ ( n = N /\ e = { n } ) ) } ) $=
      ( wcel cv wceq csn wa wrex wo crab wb a1i cnbgr co wne wel w3a cpr nbgrel
      wss orbi1d df-3an r19.42v bitr4i orbi1i r19.43 bitr4di bitrd anass ancoms
      ibar adantr prssg bicomd anbi2d 3anass 3bitr2d eqcom anbi1i eqcoms eqeq2d
      sneq pm5.32i bitri orbi12d rexbidva rabbidva eqtrid ) FGKZACLZEFUAUBKZFVR
      MZBLZFNZMZOZBDPZQZCGRVRFUCZFWAKZCBUDZUEZVRFMZWAVRNZMZOZQZBDPZCGRJVQWFWPCG
      VQVRGKZOZWFWQVQOZWGOZFVRUFWAUHZOZWDQZBDPZWPWRWFWSWGXABDPZUEZWEQZXDWRVSXFW
      EVSXFSWRBDEVRGFHIUGTUIWRXGXBBDPZWEQZXDXGXISWRXFXHWEXFWTXEOXHWSWGXEUJWTXAB
      DUKULUMTXBWDBDUNUOUPWRXCWOBDWRWADKZOZXBWJWDWNXKXBWSWGXAOZOZXLWJXBXMSXKWSW
      GXAUQTWRXLXMSZXJWQVQXNWSXLUSURUTXKXLWGWHWIOZOWJXKXAXOWGWRXAXOSXJWRXOXAFVR
      WAGGVAVBUTVCWGWHWIVDUOVEWDWNSXKWDWKWCOWNVTWKWCFVRVFVGWKWCWMWKWBWLWAWBWLMF
      VRFVRVJVHVIVKVLTVMVNUPVOVP $.

    $d E n $.  $d X e n $.
    $( Characterization of a member ` X ` of the semiopen neighborhood of a
       vertex ` N ` in a graph ` G ` .  (Contributed by AV, 16-May-2025.) $)
    vopnbgrel $p |- ( N e. V -> ( X e. U <-> ( X e. V /\ E. e e. E
         ( ( X =/= N /\ N e. e /\ X e. e ) \/ ( X = N /\ e = { X } ) ) ) ) ) $=
      ( wcel cv wne w3a wceq csn wa wo wrex wel crab dfvopnbgr2 eleq2d 3anbi13d
      neeq1 eleq1 eqeq1 sneq eqeq2d anbi12d orbi12d rexbidv elrab bitrdi ) FGLZ
      HALHCMZFNZFBMZLZCBUAZOZUQFPZUSUQQZPZRZSZBDTZCGUBZLHGLHFNZUTHUSLZOZHFPZUSH
      QZPZRZSZBDTZRUPAVIHABCDEFGIJKUCUDVHVRCHGUQHPZVGVQBDVSVBVLVFVPVSURVJVAVKUT
      UQHFUFUQHUSUGUEVSVCVMVEVOUQHFUHVSVDVNUSUQHUIUJUKULUMUNUO $.

    $( A vertex ` N ` is a member of its semiopen neighborhood iff there is a
       loop joining the vertex with itself.  (Contributed by AV,
       16-May-2025.) $)
    vopnbgrelself $p |- ( N e. V -> ( N e. U <-> E. e e. E e = { N } ) ) $=
      ( wcel wne cv w3a wceq csn wa wo wrex wi ibar wb eqid jctl eqneqall ax-mp
      olcd 3impib simpr jaoi impbii a1i rexbidv vopnbgrel 3bitr4rd ) FGKZFFLZFB
      MZKZUSNZFFOZURFPOZQZRZBDSZUPVEQVBBDSFAKUPVEUAUPVBVDBDVBVDUBUPVBVDVBVCUTVB
      VAFUCZUDUGUTVBVCUQUSUSVBVAUQUSUSQVBTZTVFVGFFUEUFUHVAVBUIUJUKULUMABCDEFGFH
      IJUNUO $.

    $d E e n v $.  $d G n $.  $d N v $.  $d V v $.
    $( Alternate definition of the closed neighborhood of a vertex as union of
       the vertex with its semiopen neighborhood.  (Contributed by AV,
       17-May-2025.) $)
    dfclnbgr6 $p |- ( N e. V -> ( G ClNeighbVtx N ) = ( { N } u. U ) ) $=
      ( vv wcel csn cv wa wrex cun wceq wo wb wel wne w3a cclnbgr co wi orc a1d
      crab simpl anim1i 3anass sylibr orcd 3simpc a1i vsnid eleq2 mpbiri adantl
      ex eleq1 adantr mpbid jca jaod impbid rexbidv anbi2d olcd pm2.61ine sylib
      orbidi elun velsn elrab orbi12i bitri neeq1 3anbi13d eqeq1 eqeq2d anbi12d
      weq sneq orbi12d 3bitr4g eqrdv dfclnbgr2 dfvopnbgr2 uneq2d 3eqtr4d ) FGLZ
      FMZFBNZLZCBUAZOZBDPZCGUIZQZWNCNZFUBZWPWQUCZXBFRZWOXBMZRZOZSZBDPZCGUIZQZEF
      UDUEWNAQWMKXAXLWMKNZFRZXMGLZWPKBUAZOZBDPZOZSZXNXOXMFUBZWPXPUCZXNWOXMMZRZO
      ZSZBDPZOZSZXMXALZXMXLLZWMXNXSYHTZSZXTYITWMYMUFXMFXNYMWMXNYLUGUHYAWMYMYAWM
      OZYLXNYNXRYGXOYNXQYFBDYNXQYFYNXQYFYNXQOZYBYEYOYAXQOYBYNYAXQYAWMUJUKYAWPXP
      ULUMUNVAYNYBXQYEYBXQUFYNYAWPXPUOUPYEXQUFYNYEWPXPYEXPWPYDXPXNYDXPXMYCLKUQW
      OYCXMURUSUTZXNXPWPTYDXMFWOVBVCVDYPVEUPVFVGVHVIVJVAVKXNXSYHVMVLYJXMWNLZXMW
      TLZSXTXMWNWTVNYQXNYRXSKFVOZWSXRCXMGCKWDZWRXQBDYTWQXPWPXBXMWOVBZVIVHVPVQVR
      YKYQXMXKLZSYIXMWNXKVNYQXNUUBYHYSXJYGCXMGYTXIYFBDYTXDYBXHYEYTXCYAWQXPWPXBX
      MFVSUUAVTYTXEXNXGYDXBXMFWAYTXFYCWOXBXMWEWBWCWFVHVPVQVRWGWHBCDEFGHIWIWMAXK
      WNABCDEFGHIJWJWKWL $.

    $( Alternate definition of the (open) neighborhood of a vertex as a
       difference of its semiopen neighborhood and the singleton of itself.
       (Contributed by AV, 17-May-2025.) $)
    dfnbgr6 $p |- ( N e. V -> ( G NeighbVtx N ) = ( U \ { N } ) ) $=
      ( vv wcel cv wa wrex csn cdif crab wceq rexbidv wel wo cnbgr co rabdif wb
      wne w3a 3anass biimpri orcd ex 3simpc a1i eqneqall com12 impd jaod impbid
      wi anbi2d pm5.32ri wn eldif weq elequ1 elrab velsn necon3bbii bitri neeq1
      anbi12i 3anbi13d eqeq1 sneq anbi12d orbi12d 3bitr4g eqrdv eqtr3id dfnbgr2
      eqeq2d dfvopnbgr2 difeq1d 3eqtr4d ) FGLZFBMZLZCBUAZNZBDOZCGFPZQRZCMZFUGZW
      HWIUHZWNFSZWGWNPZSZNZUBZBDOZCGRZWLQZEFUCUDAWLQWFWMWKCGRZWLQZXDWKCGWLUEWFK
      XFXDWFKMZGLZWHKBUAZNZBDOZNZXGFUGZNZXHXMWHXIUHZXGFSZWGXGPZSZNZUBZBDOZNZXMN
      ZXGXFLZXGXDLZXNYCUFWFXMXLYBXMXKYAXHXMXJXTBDXMXJXTXMXJXTXMXJNZXOXSXOYFXMWH
      XIUIUJUKULXMXOXJXSXOXJUTXMXMWHXIUMUNXMXPXRXJXPXMXRXJUTZYGXGFUOUPUQURUSTVA
      VBUNYDXGXELZXGWLLZVCZNXNXGXEWLVDYHXLYJXMWKXKCXGGCKVEZWJXJBDYKWIXIWHCKBVFZ
      VATVGYIXGFKFVHVIZVLVJYEXGXCLZYJNYCXGXCWLVDYNYBYJXMXBYACXGGYKXAXTBDYKWPXOW
      TXSYKWOXMWIXIWHWNXGFVKYLVMYKWQXPWSXRWNXGFVNYKWRXQWGWNXGVOWBVPVQTVGYMVLVJV
      RVSVTBCDEFGHIWAWFAXCWLABCDEFGHIJWCWDWE $.

    dfsclnbgr6.s $e |- S = { n e. V | E. e e. E { N , n } C_ e } $.
    $( Alternate definition of a semiclosed neighborhood of a vertex as a union
       of a semiopen neighborhood and the vertex itself if there is a loop at
       this vertex.  (Contributed by AV, 17-May-2025.) $)
    dfsclnbgr6 $p |- ( N e. V
                       -> S = ( U u. { n e. { N } | E. e e. E n e. e } ) ) $=
      ( wcel wa wrex crab wo cun wi a1i cv wel wne w3a wceq simpr anim1i expcom
      olcd 3anass biimpri orcd ex pm2.61ine 3simpc vsnid eleq2 mpbird adantl wb
      csn eleq1 bicomd adantr jaod biimpac simpl impbid2 rexbidv r19.43 r19.41v
      jca biancomi orbi2d 3bitrd rabbidv unrab rabsneq eqcomd uneq2d dfsclnbgr2
      eqtr3id eqtrd dfvopnbgr2 uneq1d 3eqtr4d ) GHMZGCUAZMZDCUBZNZCEOZDHPZDUAZG
      UCZWIWJUDZWNGUEZWHWNVAZUEZNZQZCEOZDHPZWJCEOZDGVAPZRZABXERWGWMXBWQXDNZQZDH
      PZXFWGWLXHDHWGWLXAWJWQNZQZCEOZXBXJCEOZQZXHWGWKXKCEWGWKXKWKXKSWNGWKWQXKWKW
      QNXJXAWKWJWQWIWJUFUGUIUHWOWKXKWOWKNZXAXJXOWPWTWPXOWOWIWJUJUKULULUMUNWGXAW
      KXJWGWPWKWTWPWKSWGWOWIWJUOTWGWTWKWGWTNWIWJWTWIWGWTWIWJWSWJWQWSWJWNWRMZXPW
      SDUPTWHWRWNUQURUSZWQWIWJUTWSWQWJWIWNGWHVBZVCVDURUSWTWJWGXQUSVLUMVEXJWKSWG
      XJWIWJWQWJWIXRVFWJWQVGVLTVEVHVIXLXNUTWGXAXJCEVJTWGXMXGXBXMXGUTWGXMWQXDWJW
      QCEVKVMTVNVOVPWGXIXCXGDHPZRXFXBXGDHVQWGXSXEXCWGXEXSXDDGHVRVSVTWBWCACDEFGH
      ILJWAWGBXCXEBCDEFGHIJKWDWEWF $.

    $( Subset chain for different kinds of neighborhoods of a vertex.
       (Contributed by AV, 16-May-2025.) $)
    dfnbgrss2 $p |- ( N e. V -> ( ( G NeighbVtx N ) C_ U /\ U C_ S
                                  /\ S C_ ( G ClNeighbVtx N ) ) ) $=
      ( wcel cnbgr co wss cclnbgr csn cdif dfnbgr6 difss eqsstrdi wel wrex crab
      cun ssun1 dfsclnbgr6 sseqtrrid dfnbgrss simprd 3jca ) GHMZFGNOZBPBAPAFGQO
      PZUMUNBGRZSBBCDEFGHIJKTBUPUAUBUMBDCUCCEUDDUPUEZUFBABUQUGABCDEFGHIJKLUHUIU
      MUNAPUOACDEFGHILJUJUKUL $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Induced subgraphs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c ISubGr $.

  $( Extend class notation with induced subgraphs. $)
  cisubgr $a class ISubGr $.

  ${
    $d e g v x $.
    $( Define the function mapping graphs and subsets of their vertices to
       their induced subgraphs.  A _subgraph induced by a subset of vertices_
       of a graph is a subgraph of the graph which contains all edges of the
       graph that join vertices of the subgraph (see section I.1 in [Bollobas]
       p. 2 or section 1.1 in [Diestel] p. 4).  Although a graph may be given
       in any meaningful representation, its induced subgraphs are always
       ordered pairs of vertices and edges.  (Contributed by AV,
       27-Apr-2025.) $)
    df-isubgr $a |- ISubGr = ( g e. _V , v e. ~P ( Vtx ` g )
                    |-> <. v , [_ ( iEdg ` g ) / e ]_
                               ( e |` { x e. dom e | ( e ` x ) C_ v } ) >. ) $.
  $}

  ${
    $d E e g v x $.  $d G e g v x $.  $d S e g v x $.  $d V e g v x $.
    isisubgr.v $e |- V = ( Vtx ` G ) $.
    isisubgr.e $e |- E = ( iEdg ` G ) $.
    $( The subgraph induced by a subset of vertices.  (Contributed by AV,
       12-May-2025.) $)
    isisubgr $p |- ( ( G e. W /\ S C_ V ) -> ( G ISubGr S )
                      = <. S , ( E |` { x e. dom E | ( E ` x ) C_ S } ) >. ) $=
      ( vg vv ve wcel wss cvv cv cfv wceq cvtx adantl ciedg wa cpw cdm crab cop
      cres cisubgr co elex adantr fvexi a1i id sselpwd csb simpr fvexd wb fveq2
      opex eqtr4di eqeq2d wi dmeq fveq1 simpl sseq12d rabeqbidv reseq12d sylbid
      ex imp csbied opeq12d pweqd df-isubgr ovmpox syl3anc ) DFLZBEMZUAZDNLZBEU
      BZLZBCAOZCPZBMZACUCZUDZUFZUEZNLZDBUGUHWKQVSWBVTDFUIUJVTWDVSVTBENENLVTEDRG
      UKULVTUMUNSWLWABWJUTULIJDBNIOZRPZUBJOZKWMTPZKOZWEWQPZWOMZAWQUCZUDZUFZUOZU
      EWKUGNWCWMDQZWOBQZUAZWOBXCWJXDXEUPXFKWPXBWJNXFWMTUQXFWQWPQZXBWJQZXFXGWQCQ
      ZXHXDXGXIURXEXDWPCWQXDWPDTPCWMDTUSHVAVBUJXEXIXHVCXDXEXIXHXEXIUAZWQCXAWIXE
      XIUPXJWSWGAWTWHXIWTWHQXEWQCVDSXJWRWFWOBXIWRWFQXEWEWQCVESXEXIVFVGVHVIVKSVJ
      VLVMVNXDWNEXDWNDRPEWMDRUSGVAVOAJKIVPVQVR $.
  $}

  ${
    $d E x $.  $d G x $.  $d S x $.  $d V x $.
    isubgriedg.v $e |- V = ( Vtx ` G ) $.
    isubgriedg.e $e |- E = ( iEdg ` G ) $.
    $( The edges of an induced subgraph.  (Contributed by AV, 12-May-2025.) $)
    isubgriedg $p |- ( ( G e. W /\ S C_ V ) -> ( iEdg ` ( G ISubGr S ) )
                                = ( E |` { x e. dom E | ( E ` x ) C_ S } ) ) $=
      ( wcel wss wa cisubgr co ciedg cfv cv cdm crab cvv fvexi cres fveq2d wceq
      cop isisubgr cvtx ssex a1i resexd opiedgfv syl2an2 eqtrd ) DFIZBEJZKZDBLM
      ZNOBCAPCOBJACQRZUAZUDZNOZURUOUPUSNABCDEFGHUEUBUNBSIUMURSIUTURUCBEEDUFGTUG
      UOCUQSCSIUOCDNHTUHUIURBSSUJUKUL $.

    $( The subgraph induced by the full set of vertices of a hypergraph.
       (Contributed by AV, 12-May-2025.) $)
    isubgrvtxuhgr $p |- ( G e. UHGraph -> ( G ISubGr V ) = <. V , E >. ) $=
      ( vx cuhgr wcel cisubgr co cv cfv wss cdm crab cres cop wceq ssidd syl c0
      isisubgr mpdan wrel wfun uhgrfun funrel cpw csn cdif wf uhgrf wa ffvelcdm
      eldifi elpwid rabeqcda eqimsscd relssres syl2anc opeq2d eqtrd ) BGHZBCIJZ
      CAFKZALZCMZFANZOZPZQZCAQVCCCMVDVKRVCCSFCABCGDEUBUCVCVJACVCAUDZVHVIMZVJARV
      CAUEVLABEUFAUGTVCVHCUHZUAUIZUJZAUKZVMABCDEULVQVIVHVQVGFVHVQVEVHHUMVFVPHZV
      GVHVPVEAUNVRVFCVFVNVOUOUPTUQURTAVIUSUTVAVB $.
  $}

  ${
    $d G x $.  $d S x $.  $d V x $.
    isubgredg.v $e |- V = ( Vtx ` G ) $.
    isubgredg.e $e |- E = ( Edg ` G ) $.
    isubgredg.h $e |- H = ( G ISubGr S ) $.
    isubgredg.i $e |- I = ( Edg ` H ) $.
    $( The edges of an induced subgraph of a graph are edges of the graph.
       (Contributed by AV, 24-Sep-2025.) $)
    isubgredgss $p |- ( ( G e. W /\ S C_ V ) -> I C_ E ) $=
      ( vx wcel wss ciedg cfv crn cedg edgval eqtri wa cv cdm crab cres cisubgr
      co fveq2i eqid isubgriedg eqtrid rneqd resss rnss mp1i eqsstrd 3sstr4g )
      CGMAFNUAZDOPZQZCOPZQZEBURUTVALUBVAPANLVAUCUDZUEZQZVBURUSVDURUSCAUFUGZOPVD
      DVFOJUHLAVACFGHVAUIUJUKULVDVANVEVBNURVAVCUMVDVAUNUOUPEDRPUTKDSTBCRPVBICST
      UQ $.

    $d G i x $.  $d K x $.  $d S i $.  $d V i $.
    $( An edge of an induced subgraph of a hypergraph is an edge of the
       hypergraph connecting vertices of the subgraph.  (Contributed by AV,
       24-Sep-2025.) $)
    isubgredg $p |- ( ( G e. UHGraph /\ S C_ V )
                      -> ( K e. I <-> ( K e. E /\ K C_ S ) ) ) $=
      ( vi vx wcel wss wa ciedg cfv wceq adantr cuhgr crn cv cdm crab cres wrex
      cisubgr co fveq2i eqid isubgriedg eqtrid rneqd eleq2d wfn wb cpw csn cdif
      c0 wf uhgrf ffnd ssrab2 a1i fnssresd fvelrnb fvres adantl eqeq1d wi fveq2
      syl weq sseq1d elrab wfun uhgrfun simpl fvelrn syl2anr simpr jca ex sylbi
      impcom eleq1 anbi12d syl5ibcom sylbid rexlimdva cedg edgval eqcomi eleq2i
      sseq1 edgiedgb bitrid wex simprl biimpcd sylanbrc eqcomd sylan9eqr eximdv
      imp mpdan df-rex 3imtr4g com23 impd impbid 3bitrd eqtri anbi1i 3bitr4g )
      CUANZAGOZPZFDQRZUBZNZFCQRZUBZNZFAOZPZFENFBNZYGPXTYCFYDLUCZYDRZAOZLYDUDZUE
      ZUFZUBZNZMUCZYORZFSZMYNUGZYHXTYBYPFXTYAYOXTYACAUHUIZQRYODUUBQJUJLAYDCGUAH
      YDUKZULUMUNUOXTYOYNUPYQUUAUQXTYMYNYDXTYMGURVAUSUTZYDXRYMUUDYDVBXSYDCGHUUC
      VCTVDYNYMOXTYLLYMVEVFVGMYNFYOVHVNXTUUAYHXTYTYHMYNXTYRYNNZPZYTYRYDRZFSZYHU
      UFYSUUGFUUEYSUUGSXTYRYNYDVIZVJVKUUFUUGYENZUUGAOZPZUUHYHUUEXTUULUUEYRYMNZU
      UKPZXTUULVLYLUUKLYRYMLMVOYKUUGAYJYRYDVMVPVQZUUNXTUULUUNXTPUUJUUKXTYDVRZUU
      MUUJUUNXRUUPXSYDCUUCVSZTUUMUUKVTYRYDWAWBUUNUUKXTUUMUUKWCTWDWEWFWGUUHUUJYF
      UUKYGUUGFYEWHUUGFAWQWIWJWKWLXTYFYGUUAXTYFFUUGSZMYMUGZYGUUAVLXRYFUUSUQZXSX
      RUUPUUTUUQYFFCWMRZNUUPUUSYEUVAFUVAYECWNZWOWPMFCYDUUCWRWSVNTXTYGUUSUUAXTYG
      UUSUUAVLXTYGPZUUMUURPZMWTUUEYTPZMWTUUSUUAUVCUVDUVEMUVCUVDUVEUVCUVDPZUUEUV
      EUVFUUMUUKUUEUVCUUMUURXAUVCUVDUUKYGUVDUUKVLXTUVDYGUUKUVDFUUGAUUMUURWCZVPX
      BVJXGUUOXCUVFUUEPUUEYTUVFUUEWCUUEUVFYSUUGFUUIUVDUUHUVCUVDFUUGUVGXDVJXEWDX
      HWEXFUURMYMXIYTMYNXIXJWEXKWKXLXMXNEYBFEDWMRYBKDWNXOWPYIYFYGBYEFBUVAYEIUVB
      XOWPXPXQ $.
  $}

  ${
    $d G x $.  $d S x $.  $d V x $.
    isubgrvtx.v $e |- V = ( Vtx ` G ) $.
    $( The vertices of an induced subgraph.  (Contributed by AV,
       12-May-2025.) $)
    isubgrvtx $p |- ( ( G e. W /\ S C_ V ) -> ( Vtx ` ( G ISubGr S ) ) = S ) $=
      ( vx wcel wss wa cisubgr co cvtx cfv ciedg cv cdm crab cres cop cvv fvexi
      eqid isisubgr fveq2d wceq ssex fvexd resexd opvtxfv syl2an2 eqtrd ) BDGZA
      CHZIZBAJKZLMABNMZFOUPMAHFUPPQZRZSZLMZAUNUOUSLFAUPBCDEUPUBUCUDUMATGULURTGU
      TAUEACCBLEUAUFUNUPUQTUNBNUGUHURATTUIUJUK $.

    $d G y $.  $d S y $.  $d V y $.  $d x y $.
    $( An induced subgraph of a hypergraph is a hypergraph.  (Contributed by
       AV, 13-May-2025.) $)
    isubgruhgr $p |- ( ( G e. UHGraph /\ S C_ V )
                       -> ( G ISubGr S ) e. UHGraph ) $=
      ( vx vy cuhgr wcel wss wa cfv cdm cpw c0 cdif wf eqid adantr syl cvv cvtx
      cisubgr co ciedg csn cv crab cres uhgrf dmresss a1i cima imadmres wral wi
      wne ffvelcdm eldifsni ex fvexd id elpwd anim12ci eldifsn sylibr ralrimiva
      imp wceq fveq2 sseq1d ralrab wfun wb ffun ssrab2 jctir funimass4 eqsstrid
      mpbird fssrescdmd resdmres feq1i isubgriedg dmeqd isubgrvtx pweqd difeq1d
      eqcomi feq123d ovexd isuhgr ) BGHZACIZJZBAUBUCZGHZWOUDKZLZWOUAKZMZNUEZOZW
      QPZWNXCBUDKZEUFZXDKZAIZEXDLZUGZUHZLZAMZXAOZXJPZWNXKXMXDXKUHZPXNWNXHCMZXAO
      ZXKXMXDWLXHXQXDPZWMXDBCDXDQZUIZRXKXHIWNXDXIUJUKWNXDXKULXDXIULZXMXDXIUMWNY
      AXMIZFUFZXDKZXMHZFXIUNZWNYDAIZYEUOZFXHUNYFWNYHFXHWNYCXHHZJZYGYEYJYGJYDXLH
      ZYDNUPZJYEYJYLYGYKWNYIYLWLYIYLUOZWMWLXRYMXTXRYIYLXRYIJYDXQHYLXHXQYCXDUQYD
      XPNURSUSSRVGYGYDATYGYCXDUTYGVAVBVCYDXLNVDVEUSVFXGYGYEFEXHXEYCVHXFYDAXEYCX
      DVIVJVKVEWNXDVLZXIXHIZJZYBYFVMWLYPWMWLXRYPXTXRYNYOXHXQXDVNXGEXHVOVPSRFXIX
      MXDVQSVSVRVTXKXMXJXOXOXJXDXIWAWHWBVEWNWRXKXBXMWQXJEAXDBCGDXSWCZWNWQXJYQWD
      WNWTXLXAWNWSAABCGDWEWFWGWIVSWNWOTHWPXCVMWNBAUBWJTWQWOWSWSQWQQWKSVS $.

    $( An induced subgraph of a hypergraph is a subgraph of the hypergraph.
       (Contributed by AV, 14-May-2025.) $)
    isubgrsubgr $p |- ( ( G e. UHGraph /\ S C_ V )
                        -> ( G ISubGr S ) SubGraph G ) $=
      ( vx cuhgr wcel wss wa cisubgr co csubgr wbr cvtx ciedg isubgrvtx eqsstrd
      cfv simpr eqid cv cdm crab cres isubgriedg resss eqsstrdi wfun wb uhgrfun
      simpl adantr isubgruhgr uhgrissubgr syl3anc mpbir2and ) BFGZACHZIZBAJKZBL
      MZUTNRZCHZUTORZBORZHZUSVBACABCFDPUQURSQUSVDVEEUAVERAHEVEUBUCZUDVEEAVEBCFD
      VETZUEVEVGUFUGUSUQVEUHZUTFGVAVCVFIUIUQURUKUQVIURVEBVHUJULABCDUMCVEUTBVDVB
      FVBTDVDTVHUNUOUP $.
  $}

  ${
    isubgrupgr.v $e |- V = ( Vtx ` G ) $.
    $( An induced subgraph of a pseudograph is a pseudograph.  (Contributed by
       AV, 14-May-2025.) $)
    isubgrupgr $p |- ( ( G e. UPGraph /\ S C_ V )
                       -> ( G ISubGr S ) e. UPGraph ) $=
      ( cupgr wcel wss cisubgr co csubgr wbr cuhgr upgruhgr isubgrsubgr subupgr
      sylan syldan ) BEFZACGZBAHIZBJKZTEFRBLFSUABMABCDNPTBOQ $.

    $( An induced subgraph of a multigraph is a multigraph.  (Contributed by
       AV, 15-May-2025.) $)
    isubgrumgr $p |- ( ( G e. UMGraph /\ S C_ V )
                       -> ( G ISubGr S ) e. UMGraph ) $=
      ( cumgr wcel wss cisubgr co csubgr wbr cuhgr umgruhgr isubgrsubgr subumgr
      sylan syldan ) BEFZACGZBAHIZBJKZTEFRBLFSUABMABCDNPTBOQ $.

    $( An induced subgraph of a simple graph is a simple graph.  (Contributed
       by AV, 15-May-2025.) $)
    isubgrusgr $p |- ( ( G e. USGraph /\ S C_ V )
                       -> ( G ISubGr S ) e. USGraph ) $=
      ( cusgr wcel wss cisubgr co csubgr wbr cuhgr usgruhgr isubgrsubgr subusgr
      sylan syldan ) BEFZACGZBAHIZBJKZTEFRBLFSUABMABCDNPTBOQ $.
  $}

  ${
    $d G x $.
    $( The subgraph induced by an empty set of vertices of a hypergraph.
       (Contributed by AV, 13-May-2025.) $)
    isubgr0uhgr $p |- ( G e. UHGraph -> ( G ISubGr (/) ) = <. (/) , (/) >. ) $=
      ( vx cuhgr wcel c0 cisubgr ciedg cfv wss cdm crab cres cop cvtx wceq eqid
      co cv cin syl 0ss isisubgr mpan2 inrab2 inidm ss0b rabbieq eqtri ineqcomi
      rabeqi wn wral cpw csn wf uhgrf wa wne ffvelcdm eldifsni neneqd ralrimiva
      cdif sylan rabeq0 sylibr eqtrid wfn uhgrfun funfnd fnresdisj mpbid opeq2d
      wb eqtrd ) ACDZAEFQZEAGHZBRZVRHZEIZBVRJZKZLZMZEEMVPEANHZIVQWEOWFUABEVRAWF
      CWFPZVRPZUBUCVPWDEEVPWBWCSZEOZWDEOZVPWIVTEOZBWBKZEWCWBWMWCWBSWABWBWBSZKZW
      MWABWBWBUDWAWLBWBWOWABWNWBWBUEUJVTUFUGUHUIVPWLUKZBWBULWMEOVPWPBWBVPWBWFUM
      ZEUNVCZVRUOZVSWBDZWPVRAWFWGWHUPWSWTUQZVTEXAVTWRDVTEURWBWRVSVRUSVTWQEUTTVA
      VDVBWLBWBVEVFVGVPVRWBVHWJWKVNVPVRVRAWHVIVJWBWCVRVKTVLVMVO $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Isomorphisms of graphs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  This section is about isomorphisms of graphs, whereby the term "isomorphism"
  is used in both of its meanings (according to the Meriam-Webster dictionary,
  see ~ https://www.merriam-webster.com/dictionary/isomorphism ): "1: the
  quality or state of being isomorphic." and "2: a one-to-one correspondence
  between two mathematical sets".

  At first, an operation ` GraphIso ` is defined (see ~ df-grim ) which
  provides the graph isomorphisms (as "one-to-one correspondence") between two
  given graphs. This definition, however, is applicable for any two sets, but
  is meaningful only if these sets have "vertices" and "edges".

  Afterwards, a binary relation ` ~=gr ` is defined (see ~ df-gric ) which is
  true for two graphs iff there is a graph isomorphisms between these graphs.
  Then these graphs are called "isomorphic".  Therefore, this relation is also
  called "is isomorphic to" relation.  More formally, ` A ~=gr B <-> `
  ` E. f f e. ( A GraphIso B ) ` resp. ` A ~=gr B <-> `
  ` ( A GraphIso B ) =/= (/) `.  Notice that there can be multiple isomorphisms
  between two graphs. For example, let ` <. { A , B } , { { A , B } } >. ` and
  ` <. { { M , N } , { { M , N } } >. ` be two graphs with two vertices and one
  edge, then ` A |-> M , B |-> N ` and ` A |-> N , B |-> M ` are two different
  isomorphisms between these graphs.

  The names and symbols are chosen analogously to group isomorphisms ` GrpIso `
  (see ~ df-gim ) resp. isomorphism between groups ` ~=g ` (see ~ df-gic ).

  The general definition of graph isomorphisms and the relation "is isomorphic
  to" for graphs is specialized for simple hypergraphs ( ~ gricushgr ) and
  simple pseudographs ( ~ gricuspgr ).  The latter corresponds to the
  definition in [Bollobas] p. 3.  It is shown that the relation "is isomorphic
  to" for graphs is an equivalence relation, see ~ gricer .  Finally,
  isomorphic graphs with different representations are studied ( ~ opstrgric ,
  ~ ushggricedg ).

  Another approach could be to define a category of graphs (there are maybe
  multiple ones), where graph morphisms are couples consisting of a function on
  vertices and a function on edges with required compatibilities, as used
  in the definition of ` GraphIso `.  And then, a graph isomorphism is defined
  as an isomorphism in the category of graphs (something like "GraphIsom
  = ( Iso `` GraphCat )" ).  Then general category theory theorems could be
  used, e.g., to show that graph isomorphism is an equivalence relation.

$)

  $( Introduce new constant symbols. $)
  $c GraphIsom $. $( Graph isomorphisms. $)
  $c GraphIso $. $( Graph isomorphisms. $)
  $c ~=gr $. $( Relation "is isomorphic to" for graphs $)

  $( Extend class notation to include the graph ispmorphisms as pair. $)
  cgrisom $a class GraphIsom $.

  $( Extend class notation to include the graph ispmorphisms. $)
  cgrim $a class GraphIso $.

  $( Extend class notation to include the "is isomorphic to" relation for
     graphs. $)
  cgric $a class ~=gr $.

  ${
    $d f g i x y $.
    $( Define the class of all isomorphisms between two graphs.  In contrast to
       ` ( F GraphIso H ) ` , which is a set of functions between the vertices,
       ` ( F GraphIsom H ) ` is a set of pairs of functions: a function between
       the vertices, and a function between the (indices of the) edges.

       It is not clear if such a definition is useful.  In the definition by
       [Diestel] p. 3, for example, the bijection between the vertices is
       called an isomorphism, as formalized in ~ df-grim .  (Contributed by AV,
       11-Dec-2022.)  (New usage is discouraged.) $)
    df-grisom $a |- GraphIsom = ( x e. _V , y e. _V |-> { <. f , g >. |
                       ( f : ( Vtx ` x ) -1-1-onto-> ( Vtx ` y )
                      /\ g : dom ( iEdg ` x ) -1-1-onto-> dom ( iEdg ` y )
                      /\ A. i e. dom ( iEdg ` x ) ( f " ( ( iEdg ` x ) ` i ) )
                                        = ( ( iEdg ` y ) ` ( g ` i ) ) ) } ) $.
  $}

  ${
    $d d e f g h i j $.
    $( An isomorphism between two graphs is a bijection between the sets of
       vertices of the two graphs that preserves adjacency, see definition in
       [Diestel] p. 3.  (Contributed by AV, 19-Apr-2025.) $)
    df-grim $a |- GraphIso = ( g e. _V , h e. _V
             |-> { f | ( f : ( Vtx ` g ) -1-1-onto-> ( Vtx ` h )
                   /\ E. j [. ( iEdg ` g ) / e ]. [. ( iEdg ` h ) / d ].
            ( j : dom e -1-1-onto-> dom d
              /\ A. i e. dom e ( d ` ( j ` i ) ) = ( f " ( e ` i ) ) ) ) } ) $.

    $( The graph isomorphism function is a well-defined function.  (Contributed
       by AV, 28-Apr-2025.) $)
    grimfn $p |- GraphIso Fn ( _V X. _V ) $=
      ( vg vh vf ve vd vj vi cvv cv cvtx cfv wf1o cdm cima wceq ciedg wsbc cmap
      wa fvex wral wex cab cgrim df-grim co wcel wf f1of elmap sylibr ovex abex
      adantr fnmpoi ) ABHHAIZJKZBIZJKZCIZLZDIZMZEIZMFIZLGIZVEKVDKUTVFVBKNOGVCUA
      SEURPKQDUPPKQFUBZSZCUCUDDCABGFEUEVHCUSUQRUFZVAUTVIUGZVGVAUQUSUTUHVJUQUSUT
      UIUSUQUTURJTUPJTUJUKUNUSUQRULUMUO $.

    $( The domain of the graph isomorphism function is a relation.
       (Contributed by AV, 28-Apr-2025.) $)
    grimdmrel $p |- Rel dom GraphIso $=
      ( vg vh vf ve vd vj vi cvv cv cvtx cfv wf1o cdm cima wceq wral ciedg wsbc
      wa wex cab cgrim df-grim reldmmpo ) ABHHAIZJKBIZJKCIZLDIZMZEIZMFIZLGIZUKK
      UJKUGULUHKNOGUIPSEUFQKRDUEQKRFTSCUAUBDCABGFEUCUD $.
  $}

  $( Two graphs are said to be isomorphic iff they are connected by at least
     one isomorphism, see definition in [Diestel] p. 3 and definition in
     [Bollobas] p. 3.  Isomorphic graphs share all global graph properties like
     order and size.  (Contributed by AV, 11-Nov-2022.)  (Revised by AV,
     19-Apr-2025.) $)
  df-gric $a |- ~=gr = ( `' GraphIso " ( _V \ 1o ) ) $.

  ${
    $d D d f $.  $d E f $.  $d F d e f g h i j $.  $d G d e f g h i j $.
    $d H d e f g h i j $.  $d V f $.  $d W f $.  $d X g h $.  $d Y g h $.
    $d Z g h $.
    isgrim.v $e |- V = ( Vtx ` G ) $.
    isgrim.w $e |- W = ( Vtx ` H ) $.
    isgrim.e $e |- E = ( iEdg ` G ) $.
    isgrim.d $e |- D = ( iEdg ` H ) $.
    $( An isomorphism of graphs is a bijection between their vertices that
       preserves adjacency.  (Contributed by AV, 19-Apr-2025.) $)
    isgrim $p |- ( ( G e. X /\ H e. Y /\ F e. Z )
                   -> ( F e. ( G GraphIso H ) <-> ( F : V -1-1-onto-> W
                /\ E. j ( j : dom E -1-1-onto-> dom D
              /\ A. i e. dom E ( D ` ( j ` i ) ) = ( F " ( E ` i ) ) ) ) ) ) $=
      ( wcel cfv wceq wa vf vg vh ve vd w3a cgrim co cvtx cv wf1o cdm cima wral
      ciedg wex cab wsbc df-grim elex 3ad2ant1 3ad2ant2 cmap wf f1of fvex elmap
      cvv sylibr adantr ovex abex eqidd fveq2 adantl f1oeq123d fvexd dmeq fveq1
      a1i wb imaeq2d eqeqan12rd raleqbidv anbi12d adantll sbcied2 exbidv abbidv
      biidd bitrd elovmpod eqcomi dmeqi fveq1i imaeq12d eqeq12d elabg 3ad2ant3
      id ) FJQZGKQZELQZUFZEFGUGUHQEFUIRZGUIRZUAUJZUKZFUORZULZGUORZULZCUJZUKZBUJ
      ZXMRZXKRZXGXOXIRZUMZSZBXJUNZTZCUPZTZUAUQZQZHIEUKZDULZAULZXMUKZXPARZEXODRZ
      UMZSZBYHUNZTZCUPZTZXDVHVHUBUJZUIRZUCUJZUIRZXGUKZUDUJZULZUEUJZULZXMUKZXPUU
      FRZXGXOUUDRZUMZSZBUUEUNZTZUEUUAUORZURZUDYSUORZURZCUPZTZUAUQYEEUGVHFGUBUCU
      DUAUBUCBCUEUSXAXBFVHQXCFJUTVAXBXAGVHQXCGKUTVBYEVHQXDYDUAXFXEVCUHZXHXGUVAQ
      ZYCXHXEXFXGVDUVBXEXFXGVEXFXEXGGUIVFFUIVFVGVIVJXFXEVCVKVLVTYSFSZUUAGSZTZUU
      TYDUAUVEUUCXHUUSYCUVEYTXEUUBXFXGXGUVEXGVMUVCYTXESUVDYSFUIVNVJUVDUUBXFSUVC
      UUAGUIVNVOVPUVEUURYBCUVEUURYBYBUVEUUPYBUDUUQXIVHUVEYSUOVQUVCUUQXISUVDYSFU
      OVNVJUVEUUDXISZTZUUNYBUEUUOXKVHUVGUUAUOVQUVEUUOXKSZUVFUVDUVHUVCUUAGUOVNVO
      VJUVFUUFXKSZUUNYBWAUVEUVFUVITZUUHXNUUMYAUVJUUEXJUUGXLXMXMUVJXMVMUVFUUEXJS
      UVIUUDXIVRVJZUVIUUGXLSUVFUUFXKVRVOVPUVJUULXTBUUEXJUVKUVIUVFUUIXQUUKXSXPUU
      FXKVSUVFUUJXRXGXOUUDXIVSWBWCWDWEWFWGWGUVEYBWJWKWHWEWIWLXCXAYFYRWAXBYDYRUA
      ELXGESZXHYGYCYQUVLXEHXFIXGEUVLWTZXEHSUVLHXEMWMVTXFISUVLIXFNWMVTVPUVLYBYPC
      UVLXNYJYAYOUVLXJYHXLYIXMXMUVLXMVMXJYHSUVLXIDDXIOWMZWNVTZXLYISUVLXKAAXKPWM
      ZWNVTVPUVLXTYNBXJYHUVOUVLXQYKXSYMXQYKSUVLXPXKAUVPWOVTUVLXGEXRYLUVMXRYLSUV
      LXOXIDUVNWOVTWPWQWDWEWHWEWRWSWK $.
  $}

  ${
    $d F i j $.  $d G i j $.  $d H i j $.
    grimprop.v $e |- V = ( Vtx ` G ) $.
    grimprop.w $e |- W = ( Vtx ` H ) $.
    ${
      grimprop.e $e |- E = ( iEdg ` G ) $.
      grimprop.d $e |- D = ( iEdg ` H ) $.
      $( Properties of an isomorphism of graphs.  (Contributed by AV,
         29-Apr-2025.) $)
      grimprop $p |- ( F e. ( G GraphIso H )
           -> ( F : V -1-1-onto-> W /\ E. j ( j : dom E -1-1-onto-> dom D
                /\ A. i e. dom E ( D ` ( j ` i ) ) = ( F " ( E ` i ) ) ) ) ) $=
        ( cvv wcel cgrim wf1o cdm cv cfv co w3a cima wceq wral wa wex grimdmrel
        ovrcl simpld simprd id 3jca isgrim biimpd mpcom ) FNOZGNOZEFGPUAZOZUBZU
        THIEQDRZARCSZQBSZVCTATEVDDTUCUDBVBUEUFCUGUFZUTUQURUTUTUQURFGEPUHUIZUJUT
        UQURVFUKUTULUMVAUTVEABCDEFGHINNUSJKLMUNUOUP $.
    $}

    $( An isomorphism of graphs is a bijection between their vertices.
       (Contributed by AV, 29-Apr-2025.) $)
    grimf1o $p |- ( F e. ( G GraphIso H ) -> F : V -1-1-onto-> W ) $=
      ( vj vi cgrim co wcel wf1o ciedg cfv cdm cv cima wceq eqid wral wa simpld
      wex grimprop ) ABCJKLDEAMBNOZPZCNOZPHQZMIQZUIOUHOAUJUFORSIUGUAUBHUDUHIHUF
      ABCDEFGUFTUHTUEUC $.
  $}

  ${
    $d G i j $.  $d H i j $.  $d i ph $.
    grimidvtxsdg.g $e |- ( ph -> G e. UHGraph ) $.
    grimidvtxsdg.h $e |- ( ph -> H e. V ) $.
    grimidvtxsdg.v $e |- ( ph -> ( Vtx ` G ) = ( Vtx ` H ) ) $.
    grimidvtxsdg.e $e |- ( ph -> ( iEdg ` G ) = ( iEdg ` H ) ) $.
    $( The identity relation restricted to the set of vertices of a graph is a
       graph isomorphism between the graph and a graph with the same vertices
       and edges.  (Contributed by AV, 4-May-2025.) $)
    grimidvtxedg $p |- ( ph -> ( _I |` ( Vtx ` G ) ) e. ( G GraphIso H ) ) $=
      ( vj vi cid cvtx cfv wcel wf1o ciedg wceq wa cvv eqid cres cgrim cdm cima
      co cv wral wex f1oi f1oeq3d mpbii wfun funi fvex dmex resfunexg mp2an a1i
      dmeqd fvresi adantl fveq2d eqcomd fveq1d adantr wss cuhgr resiima 3eqtr4d
      uhgrss sylan syl ralrimiva jca f1oeq1 fveq1 ralbidv anbi12d spcedv isgrim
      fveqeq2d wb syl3anc mpbir2and ) AKBLMZUAZBCUBUENZWECLMZWFOZBPMZUCZCPMZUCZ
      IUFZOZJUFZWNMZWLMWFWPWJMZUDZQZJWKUGZRZIUHZAWEWEWFOWIWEUIAWEWHWEWFGUJUKAXB
      WKWMKWKUAZOZWPXDMZWLMZWSQZJWKUGZRISXDXDSNZAKULZWKSNXJUMWJBPUNUOKWKSUPUQUR
      AXEXIAWKWKXDOXEWKUIAWKWMWKXDAWJWLHUSUJUKAXHJWKAWPWKNZRZXFWJMZWRXGWSXMXFWP
      WJXLXFWPQAWKWPUTVAVBAXGXNQXLAXFWLWJAWJWLHVCVDVEXMWRWEVFZWSWRQABVGNZXLXOEW
      JWPBWEWETZWJTZVJVKWEWRVHVLVIVMVNWNXDQZWOXEXAXIWKWMWNXDVOXSWTXHJWKXSWQXFWS
      WLWPWNXDVPWAVQVRVSAXPCDNWFSNZWGWIXCRWBEFXTAXKWESNXTUMBLUNKWESUPUQURWLJIWJ
      WFBCWEWHVGDSXQWHTXRWLTVTWCWD $.
  $}

  ${
    $( The identity relation restricted to the set of vertices of a graph is a
       graph isomorphism between the graph and itself.  (Contributed by AV,
       29-Apr-2025.)  (Prove shortened by AV, 5-May-2025.) $)
    grimid $p |- ( G e. UHGraph
                   -> ( _I |` ( Vtx ` G ) ) e. ( G GraphIso G ) ) $=
      ( cuhgr wcel id cvtx cfv eqidd ciedg grimidvtxedg ) ABCZAABJDZKJAEFGJAHFG
      I $.
  $}

  ${
    $d F i j x y $.  $d S i j x y $.  $d T i j x y $.
    $( If there is a graph isomorphism between a hypergraph and a class with an
       edge function, the class is also a hypergraph.  (Contributed by AV,
       2-May-2025.) $)
    grimuhgr $p |- ( ( S e. UHGraph /\ F e. ( S GraphIso T )
                       /\ Fun ( iEdg ` T ) ) -> T e. UHGraph ) $=
      ( vj vi vx vy cfv wcel wi wa c0 cv wceq eqid adantr ex adantl wne cvv cdm
      ciedg wfun cgrim co cuhgr cvtx cpw csn cdif wf wf1o cima wex grimprop w3a
      wral crn fdmrn biimpi 3ad2ant3 wfn wss funfn wrex f1ofo 3ad2ant2 3ad2ant1
      wfo foelcdmi sylan 2fveq3 fveq2 imaeq2d eqeq12d f1ofun fvex a1i funimaexg
      rspcv syl2an2r f1of fimassd elpwd cin ineq1d ffvelcdm eldifsn elpw bianbi
      f1odm sseqin2 simpr eqnetrd biimtrid syld imp 3adant2 imadisjlnd sylanbrc
      eleq1 mpbird eleq1d syl5ibcom com23 3imp rexlimdv ralrimiv com35 fnfvrnss
      3exp impd fssd exlimdv syl impcom grimdmrel ovrcl isuhgr imbi12d 3imp31
      wb ) BUBHZUCZCABUDUEIZAUFIZBUFIZYDYEYFYGJZYDYEKYHAUBHZUAZAUGHZUHZLUIZUJZY
      IUKZYCUAZBUGHZUHZYMUJZYCUKZJZYEYDUUAYEYKYQCULZYJYPDMZULZEMZUUCHYCHZCUUEYI
      HZUMZNZEYJUQZKZDUNZKYDUUAJZYCEDYICABYKYQYKOZYQOZYIOZYCOZUOUUBUULUUMUUBUUK
      UUMDUUBUUKYDUUAUUBUUKYDUPZYOYTUURYOKYPYCURZYSYCUURYPUUSYCUKZYOYDUUBUUTUUK
      YDUUTYCUSUTVAPUURYCYPVBZYOFMZYCHZYSIZFYPUQZUUSYSVCYDUUBUVAUUKYDUVAYCVDUTV
      AUURYOUVEUUBUUKYDYOUVEJZUUBUUDUUJYDUVFJUUBUUDYOYDUUJUVEUUBUUDYOYDUUJUVEJJ
      UUBUUDYOUPZYDUUJUVEUVGYDUUJUPZUVDFYPUVHUVBYPIZGMZUUCHZUVBNZGYJVEZUVDUVHUV
      IUVMUVHYJYPUUCVIZUVIUVMUVGYDUVNUUJUUDUUBUVNYOYJYPUUCVFVGVHGYJYPUUCUVBVJVK
      QUVHUVLUVDGYJUVGYDUUJUVJYJIZUVLUVDJZJZUVGYDUUJUVQJUVGYDKZUVOUUJUVPUVRUVOU
      UJUVPJUVRUVOKZUUJUVKYCHZCUVJYIHZUMZNZUVPUVOUUJUWCJUVRUUIUWCEUVJYJUUEUVJNZ
      UUFUVTUUHUWBUUEUVJYCUUCVLUWDUUGUWACUUEUVJYIVMVNVOVTRUVSUWCUVPUVSUWCKZUVTY
      SIZUVLUVDUWEUWFUWBYSIZUVSUWGUWCUVSUWBYRIUWBLSUWGUVSUWBYQTUVRCUCZUVOUWATIZ
      UWBTIUVGUWHYDUUBUUDUWHYOYKYQCVPVHPUWIUVSUVJYIVQZVRCUWATVSWAUVRUWBYQVCZUVO
      UVGUWKYDUUBUUDUWKYOUUBYKYQCUWAYKYQCWBWCVHPPWDUVSCUWAUVRUVOCUAZUWAWEZLSZUV
      GUVOUWNJZYDUUBYOUWOUUDUUBYOKZUVOUWNUWPUVOKZUWMYKUWAWEZLUWQUWLYKUWAUWPUWLY
      KNZUVOUUBUWSYOYKYQCWKPPWFUWPUVOUWRLSZUWPUVOUWAYNIZUWTYOUVOUXAJUUBYOUVOUXA
      YJYNUVJYIWGQRUXAUWAYKVCZUWALSZKZUWPUWTUXAUWAYLIUXCUXBUWAYLLWHUWAYKUWJWIWJ
      UXDUWTJUWPUXDUWRUWALUXBUWRUWANZUXCUXBUXEUWAYKWLUTPUXBUXCWMWNVRWOWPWQWNQWR
      PWQWSUWBYRLWHWTPUWCUWFUWGYBUVSUVTUWBYSXARXBUVLUVTUVCYSUVKUVBYCVMXCXDQWPQX
      EQXFXGWPXHXKXKXIXLXFWQFYPYSYCXJWAXMQXKXNWQXOXPYEYHUUAYBZYDYEATIZBTIZKZUXF
      ABCUDXQXRUXIYFYOYGYTUXGYFYOYBUXHTYIAYKUUNUUPXSPUXHYGYTYBUXGTYCBYQUUOUUQXS
      RXTXORXBQYA $.
  $}

  ${
    $d F f j x $.  $d F i j x y $.  $d S f j x $.  $d S i j x y $.
    $d T f j x $.  $d T i j x y $.
    $( The converse of a graph isomorphism is a graph isomorphism.
       (Contributed by AV, 1-May-2025.) $)
    grimcnv $p |- ( S e. UHGraph -> ( F e. ( S GraphIso T )
                                      -> `' F e. ( T GraphIso S ) ) ) $=
      ( vj vi vf vx vy wcel cgrim wa cfv wf1o cv cima wceq eqid cvv wi ex cuhgr
      co ccnv cvtx cdm wral wex grimprop adantl f1ocnv ad2antrl vex cnvexg mp1i
      ciedg wrex wfo f1ofo foelcdmi sylan fveq2 imaeq2d eqeq12d rspcv f1ocnvfv1
      2fveq3 ad4ant23 fveq2d wf1 wss ad2antlr uhgrss ad5ant15 f1imacnv syl2an2r
      f1of1 eqcomd adantr eqtrd adantlr syld com23 impr eleq1 imbi12d syl5ibcom
      simplr imbi2d com24 imp31 rexlimdva mpd ralrimiva f1oeq1 fveqeq2d ralbidv
      jca fveq1 anbi12d spcedv exlimdv wb grimdmrel ovrcl simprd simpld syl3anc
      isgrim mpbir2and mpdan ) AUAIZCABJUBZIZCUCZBAJUBIZXKXMKZAUDLZBUDLZCMZAUOL
      ZUEZBUOLZUEZDNZMZENZYDLYBLZCYFXTLZOZPZEYAUFZKZDUGZKZXOXMYNXKYBEDXTCABXQXR
      XQQZXRQZXTQZYBQZUHUIXPYNKXOXRXQXNMZYCYAFNZMZGNZYTLZXTLXNUUBYBLZOZPZGYCUFZ
      KZFUGZXSYSXPYMXQXRCUJUKXPXSYMUUIXPXSKZYLUUIDUUJYLUUIUUJYLKZUUHYCYAYDUCZMZ
      UUBUULLZXTLZUUEPZGYCUFZKFRUULYDRIUULRIUUKDULYDRUMUNUUKUUMUUQYEUUMUUJYKYAY
      CYDUJUKUUKUUPGYCUUKUUBYCIZKZHNZYDLZUUBPZHYAUPZUUPUUKYAYCYDUQZUURUVCYEUVDU
      UJYKYAYCYDURUKHYAYCYDUUBUSUTUUSUVBUUPHYAUUKUURUUTYAIZUVBUUPSUUKUVBUVEUURU
      UPUUKUVEUVAYCIZUVAUULLZXTLZXNUVAYBLZOZPZSZSZUVBUVEUURUUPSZSUUJYEYKUVMUUJY
      EKZUVEYKUVLUVOUVEYKUVLSUVOUVEKZYKUVICUUTXTLZOZPZUVLUVEYKUVSSUVOYJUVSEUUTY
      AYFUUTPZYGUVIYIUVRYFUUTYBYDVFUVTYHUVQCYFUUTXTVAVBVCVDUIUVPUVSUVLUVPUVSKZU
      VFUVKUWAUVFKZUVHXNUVROZUVJUVPUVFUVHUWCPUVSUVPUVFKZUVHUVQUWCUWDUVGUUTXTYEU
      VEUVGUUTPUUJUVFYAYCUUTYDVEVGVHUVPUVQUWCPUVFUVPUWCUVQUVOXQXRCVIZUVEUVQXQVJ
      ZUWCUVQPXSUWEXPYEXQXRCVPVKXKUVEUWFXMXSYEXTUUTAXQYOYQVLVMXQXRUVQCVNVOVQVRV
      SVTUWBUVRUVIXNUWBUVIUVRUVPUVSUVFWGVQVBVSTTWATWBWCUVBUVLUVNUVEUVBUVFUURUVK
      UUPUVAUUBYCWDUVBUVHUUOUVJUUEUVAUUBXTUULVFUVBUVIUUDXNUVAUUBYBVAVBVCWEWHWFW
      IWJWKWLWMWQYTUULPZUUAUUMUUGUUQYCYAYTUULWNUWGUUFUUPGYCUWGUUCUUNUUEXTUUBYTU
      ULWRWOWPWSWTTXAWCXMXOYSUUIKXBZXKYNXMBRIZARIZXNRIUWHXMUWJUWIABCJXCXDZXEXMU
      WJUWIUWKXFCXLUMXTGFYBXNBAXRXQRRRYPYOYRYQXHXGVKXIXJT $.
  $}

  ${
    $d F f g i j $.  $d F f g i x $.  $d G f g i j $.  $d G f g i y $.
    $d S f g i j $.  $d S f g i y $.  $d T f g i x $.  $d T f g i y $.
    $d U f g i j $.  $d U f g i x $.
    $( The composition of graph isomorphisms is a graph isomorphism.
       (Contributed by AV, 3-May-2025.) $)
    grimco $p |- ( ( F e. ( T GraphIso U ) /\ G e. ( S GraphIso T ) )
                   -> ( F o. G ) e. ( S GraphIso U ) ) $=
      ( vi vf vg cgrim wcel wa cfv wf1o cv cima wceq eqid wi cvv adantr vj ccom
      vx vy co cvtx ciedg cdm wral wex grimprop f1oco ad2ant2r vex coex a1i a1d
      expcom impd imp adantl 2fveq3 fveq2 imaeq2d eqeq12d rspcv f1of ffvelcdmda
      wf syl simpr fvco3d fveq2d eqtrd ex syld impr imaeq2 imaco sylan9eq exp31
      eqtr4di com24 expimpd imp32 ralrimiv f1oeq1 fveq1 fveqeq2d ralbidv spcedv
      anbi12d exp32 exlimdv com23 imp31 syl2an wb grimdmrel ovrcl simpld simprd
      jca coexg isgrim syl3anc mpbird ) DBCIUEZJZEABIUEZJZKZDEUBZACIUEJZAUFLZCU
      FLZXMMZAUGLZUHZCUGLZUHZUANZMZFNZYBLZXTLXMYDXRLZOZPZFXSUIZKZUAUJZKZXIBUFLZ
      XPDMZBUGLZUHZYAGNZMZUCNZYQLXTLZDYSYOLZOZPZUCYPUIZKZGUJZKZXOYMEMZXSYPHNZMZ
      UDNZUUILYOLZEUUKXRLZOZPZUDXSUIZKZHUJZKZYLXKXTUCGYODBCYMXPYMQZXPQZYOQZXTQZ
      UKYOUDHXREABXOYMXOQZUUTXRQZUVBUKUUGUUSKXQYKYNUUHXQUUFUURXOYMXPDEULUMYNUUF
      UUSYKYNUUEUUSYKRGYNUUSUUEYKYNUUHUURUUEYKRZYNUUHKZUUQUVFHUVGUUQUUEYKUVGUUQ
      UUEKZKZYJXSYAYQUUIUBZMZYDUVJLZXTLZYGPZFXSUIZKUASUVJUVJSJUVIYQUUIGUNHUNUOU
      PUVIUVKUVOUVHUVKUVGUUQUUEUVKUUJUUEUVKRUUPUUJYRUUDUVKYRUUJUUDUVKRYRUUJKUVK
      UUDXSYPYAYQUUIULUQURUSTUTVAUVIUVNFXSUVGUUQUUEYDXSJZUVNRZUVGUUJUUPUUEUVQRU
      VGUUJKZUVPUUEUUPUVNUVRUVPUUEUUPUVNRUVRUVPKZUUEKZUUPYDUUILZYOLZEYFOZPZUVNU
      VSUUPUWDRZUUEUVPUWEUVRUUOUWDUDYDXSUUKYDPZUULUWBUUNUWCUUKYDYOUUIVBUWFUUMYF
      EUUKYDXRVCVDVEVFVATUVTUWDUVNUVTUWDUVMDUWBOZYGUVSYRUUDUVMUWGPZUVSYRKZUUDUW
      AYQLZXTLZUWGPZUWHUWIUWAYPJZUUDUWLRUVSUWMYRUVRXSYPYDUUIUUJXSYPUUIVIZUVGXSY
      PUUIVGVAZVHTUUCUWLUCUWAYPYSUWAPZYTUWKUUBUWGYSUWAXTYQVBUWPUUAUWBDYSUWAYOVC
      VDVEVFVJUWIUWLUWHUWIUWLKZUVMUWKUWGUWQUVLUWJXTUWIUVLUWJPUWLUWIXSYPYDYQUUIU
      VSUWNYRUVRUWNUVPUWOTTUVSUVPYRUVRUVPVKTVLTVMUWIUWLVKVNVOVPVQUWDUWGDUWCOYGU
      WBUWCDVRDEYFVSWBVTVOVPWAWCWDWEWFXCYBUVJPZYCUVKYIUVOXSYAYBUVJWGUWRYHUVNFXS
      UWRYEUVLYGXTYDYBUVJWHWIWJWLWKWMWNWDWOWNWPXCWQXLASJZCSJZXMSJXNYLWRXKUWSXIX
      KUWSBSJZABEIWSWTXAVAXIUWTXKXIUXAUWTBCDIWSWTXBTDEXHXJXDXTFUAXRXMACXOXPSSSU
      VDUVAUVEUVCXEXFXG $.
  $}

  ${
    $d D j k $.  $d E j $.  $d F i j k $.  $d G i j k $.  $d H i j k $.
    $d K j k $.
    uhgrimedgi.e $e |- E = ( Edg ` G ) $.
    uhgrimedgi.d $e |- D = ( Edg ` H ) $.
    $( An isomorphism between graphs preserves edges, i.e. if there is an edge
       in one graph connecting vertices then there is an edge in the other
       graph connecting the corresponding vertices.  (Contributed by AV,
       25-Oct-2025.) $)
    uhgrimedgi $p |- ( ( ( G e. UHGraph /\ H e. UHGraph )
                         /\ ( F e. ( G GraphIso H ) /\ K e. E ) )
                       -> ( F " K ) e. D ) $=
      ( vj vi vk wcel wa cima wi cfv cv eqid wb ex cuhgr cgrim co cvtx wf1o cdm
      ciedg wceq wral wex grimprop wrex cedg eleq2i uhgrfun edgiedgb syl bitrid
      wfun adantr w3a simplr weq 2fveq3 fveq2 imaeq2d eqeq12d rspcv ad3antlr wf
      adantl ffvelcdmd iedgedg syl2an2r eleqtrrdi eleq1 eqcoms syl5ibrcom syl5d
      f1of impd 3imp imaeq2 eleq1d 3ad2ant1 mpbird rexlimdva sylbid imp exlimdv
      3exp expimpd syl5 impcomd ) DUALZEUALZMZCDEUBUCLZFBLZMCFNZALZWQWSWRXAWQWS
      WRXAOWRDUDPZEUDPZCUEZDUGPZUFZEUGPZUFZIQZUEZJQZXIPXGPZCXKXEPZNZUHZJXFUIZMZ
      IUJZMWQWSMZXAXGJIXECDEXBXCXBRXCRXERZXGRZUKXSXDXRXAXSXDMXQXAIXSXDXQXAOZWQW
      SXDYBOZWQWSFKQZXEPZUHZKXFULZYCWOWSYGSWPWSFDUMPZLZWOYGBYHFGUNWOXEUSYIYGSXE
      DXTUOKFDXEXTUPUQURUTWQYFYCKXFWQYDXFLZMZYFYCYKYFMZXDXQXAYLXDXQVAXACYENZALZ
      YLXDXQYNYKXDXQYNOZOYFYKXDYOYKXDMZXJXPYNYPXPYDXIPZXGPZYMUHZXJYNYPYJXPYSOWQ
      YJXDVBZXOYSJYDXFJKVCZXLYRXNYMXKYDXGXIVDUUAXMYECXKYDXEVEVFVGVHUQYPXJYSYNOY
      PXJMZYNYSYRALZUUBYREUMPZAYPXGUSZXJYQXHLYRUUDLWPUUEWOYJXDXGEYAUOVIUUBXFXHY
      DXIXJXFXHXIVJYPXFXHXIVTVKYPYJXJYTUTVLXGEYQYAVMVNHVOYNUUCSYMYRYMYRAVPVQVRT
      VSWATUTWBYLXDXAYNSZXQYFUUFYKYFWTYMAFYECWCWDVKWEWFWKTWGWHWIWIWJWLWMTWNWI
      $.

    $( An isomorphism between graphs preserves edges, i.e. there is an edge in
       one graph connecting vertices iff there is an edge in the other graph
       connecting the corresponding vertices.  (Contributed by AV,
       25-Oct-2025.) $)
    uhgrimedg $p |- ( ( ( G e. UHGraph /\ H e. UHGraph )
                        /\ F e. ( G GraphIso H ) /\ K C_ ( Vtx ` G ) )
                      -> ( K e. E <-> ( F " K ) e. D ) ) $=
      ( cuhgr wcel wa cgrim co cvtx cfv cima anim1i uhgrimedgi syl2an2r syl wss
      w3a simp1 simp2 ccnv wf1 wceq wf1o eqid grimf1o f1of1 3ad2ant2 jca adantr
      simp3 f1imacnv pm3.22 3ad2ant1 simpl 3adant3 grimcnv imp eqeltrrd impbida
      ) DIJZEIJZKZCDELMJZFDNOZUAZUBZFBJZCFPZAJZVKVGVLVHVLKVNVGVHVJUCVKVHVLVGVHV
      JUDQABCDEFGHRSVKVNKZCUEZVMPZFBVOVIENOZCUFZVJKZVQFUGVKVTVNVKVSVJVHVGVSVJVH
      VIVRCUHVSCDEVIVRVIUIVRUIUJVIVRCUKTULVGVHVJUOUMUNVIVRFCUPTVKVFVEKZVNVPEDLM
      JZVNKVQBJVGVHWAVJVEVFUQURVKWBVNVKVEVHKZWBVGVHWCVJVGVEVHVEVFUSQUTVEVHWBDEC
      VAVBTQBAVPEDVMHGRSVCVD $.

    $d F x y $.  $d G x y $.  $d H x y $.  $d V y $.
    uhgrimprop.v $e |- V = ( Vtx ` G ) $.
    uhgrimprop.w $e |- W = ( Vtx ` H ) $.
    $( An isomorphism between hypergraphs is a bijection between their vertices
       that preserves adjacency for simple edges, i.e. there is a simple edge
       in one graph connecting one or two vertices iff there is a simple edge
       in the other graph connecting the vertices which are the images of the
       vertices.  (Contributed by AV, 27-Apr-2025.)  (Revised by AV,
       25-Oct-2025.) $)
    uhgrimprop $p |- ( ( G e. UHGraph /\ H e. UHGraph
                         /\ F e. ( G GraphIso H ) )
                       -> ( F : V -1-1-onto-> W /\ A. x e. V A. y e. V
                   ( { x , y } e. E <-> { ( F ` x ) , ( F ` y ) } e. D ) ) ) $=
      ( cuhgr wcel w3a cv cpr cfv wa cgrim wf1o wral grimf1o 3ad2ant3 cima cvtx
      co wss 3simpa simp3 prssi sseqtrdi uhgrimedg syl2an3an wfn wceq f1ofn syl
      wb anim1i 3anass sylibr fnimapr eleq1d bitrd ralrimivva jca ) FNOZGNOZEFG
      UAUHOZPZHIEUBZAQZBQZRZDOZVNESVOESRZCOZUTZBHUCAHUCVKVIVMVJEFGHILMUDZUEVLVT
      ABHHVLVNHOZVOHOZTZTZVQEVPUFZCOZVSVLVIVJTVKWDVPFUGSZUIVQWGUTVIVJVKUJVIVJVK
      UKWDVPHWHVNVOHULLUMCDEFGVPJKUNUOWEWFVRCWEEHUPZWBWCPZWFVRUQWEWIWDTWJVLWIWD
      VKVIWIVJVKVMWIWAHIEURUSUEVAWIWBWCVBVCHVNVOEVDUSVEVFVGVH $.
  $}

  ${
    $d D d i $.  $d E i x $.  $d F i x $.  $d G i $.  $d H i $.  $d V i $.
    $d W i $.  $d X i $.
    isusgrim.v $e |- V = ( Vtx ` G ) $.
    isusgrim.w $e |- W = ( Vtx ` H ) $.
    isusgrim.e $e |- E = ( Edg ` G ) $.
    isusgrim.d $e |- D = ( Edg ` H ) $.
    ${
      $d D x y $.  $d E y $.  $d F y $.  $d G x y $.  $d H x y $.
      $d I i x y $.  $d J i x y $.  $d M i x y $.  $d N i $.  $d V x y $.
      $d W x y $.  $d X x y $.
      isuspgrim0lem.i $e |- I = ( iEdg ` G ) $.
      isuspgrim0lem.j $e |- J = ( iEdg ` H ) $.
      isuspgrim0lem.m $e |- M = ( x e. E |-> ( F " x ) ) $.
      isuspgrim0lem.n $e |- N = ( x e. dom I
                                  |-> ( `' J ` ( M ` ( I ` x ) ) ) ) $.
      $( An isomorphism of simple pseudographs is a bijection between their
         vertices which induces a bijection between their edges.  (Contributed
         by AV, 21-Apr-2025.) $)
      isuspgrim0lem $p |- ( ( ( ( G e. USPGraph /\ H e. USPGraph /\ F e. X )
                              /\ F : V -1-1-onto-> W ) /\ M : E -1-1-onto-> D )
             -> ( N : dom I -1-1-onto-> dom J
                  /\ A. i e. dom I ( J ` ( N ` i ) ) = ( F " ( I ` i ) ) ) ) $=
        ( vy cuspgr wcel w3a wf1o wa cdm cv cfv cima wceq wral ccnv uspgrf1oedg
        wreu cedg 3ad2ant2 ad2antrr wf f1of adantl wfun cuhgr uspgruhgr uhgrfun
        adantr syl crn ciedg edgval eqcomi rneqi 3eqtri feq3 ax-mp fdmrn bitr4i
        wb sylibr 3ad2ant1 ffvelcdmda ffvelcdmd eleqtrdi f1ocnvdm syl2an2r wrex
        ralrimiva wi 2fveq3 eqeq2d f1oeq2 bilani f1oeq3 simpll1 simpr f1ocnvfv2
        fveq2d eqtr2d rspcedvdw eqtr2 wf1 f1of1 iedgedg sylan eleqtrrdi anim12d
        ex ad3antrrr imp f1fveq f1veqaeq syl5 ralrimivva reu4 sylanbrc reubidva
        sylbid mpbird simplr adantlr bicomd syl12anc f1ompt cvv fvmptd2 imaeq2d
        fvexd simp3 imaexd 3eqtrd jca ) FUDUEZGUDUEZENUEZUFZLMEUGZUHZDBJUGZUHZH
        UIZIUIZKUGZCUJZKUKZIUKZEUUEHUKZULZUMZCUUBUNUUAAUJZHUKZJUKZIUOZUKZUUCUEZ
        AUUBUNUUEUUOUMZAUUBUQZCUUCUNUUDUUAUUPAUUBUUAUUCGURUKZIUGZUUKUUBUEZUUMUU
        SUEZUUPYQUUTYRYTYOYNUUTYPIGTUPUSZUTZUUAUVAUHZUUMBUUSUVEDBUULJUUADBJVAZU
        VAYTUVFYSDBJVBVCZVHUUAUUBDUUKHYQUUBDHVAZYRYTYNYOUVHYPYNHVDZUVHYNFVEUEUV
        IFVFHFSVGVIZUVHUUBHVJZHVAZUVIDUVKUMUVHUVLVTDFURUKZFVKUKZVJUVKQFVLUVNHHU
        VNSVMVNVODUVKUUBHVPVQHVRVSWAWBZUTZWCWDRWEUUCUUSUUMIWFWGZWIUUAUURCUUCUUA
        UUEUUCUEZUHZUURUUEIUKZUUOIUKZUMZAUUBUQZUVSUWCUVTUUMUMZAUUBUQZUVSUWDAUUB
        WHUWDUVTUCUJZHUKZJUKZUMZUHZUUKUWFUMZWJZUCUUBUNAUUBUNUWEUVSUWDUVTUVTJUOU
        KZHUOUKZHUKZJUKZUMAUWNUUBUUKUWNUMUUMUWPUVTUUKUWNJHWKWLUUAUUBUVMHUGZUVRU
        WMUVMUEZUWNUUBUEYQUWQYRYTYNYOUWQYPHFSUPZWBUTUUAUVMBJUGZUVRUVTBUEZUWRYTU
        WTYSDUVMUMYTUWTVTQDUVMBJWMVQWNUUAUUCBUUEIUUAUUCBIUGZUUCBIVAUUAUUTUXBUVD
        BUUSUMUXBUUTVTRBUUSUUCIWOVQWAUUCBIVBVIWCZUVMBUVTJWFWGUUBUVMUWMHWFWGUVSU
        WPUWMJUKZUVTUVSUWOUWMJUUAUWQUVRUWRUWOUWMUMUUAYNUWQYNYOYPYRYTWPUWSVIUVSU
        WMDUVMUUAYTUVRUXAUWMDUEYSYTWQZUXCDBUVTJWFWGQWEUUBUVMUWMHWRWGWSUUAYTUVRU
        XAUXDUVTUMUXEUXCDBUVTJWRWGWTXAUVSUWLAUCUUBUUBUWJUUMUWHUMZUVSUVAUWFUUBUE
        ZUHZUHZUWKUVTUUMUWHXBUXIUXFUULUWGUMZUWKUVSDBJXCZUXHUULDUEZUWGDUEZUHZUXF
        UXJVTUUAUXKUVRYTUXKYSDBJXDVCVHUVSUXHUXNYQUXHUXNWJZYRYTUVRYNYOUXOYPYNUVA
        UXLUXGUXMYNUVAUXLYNUVAUHUULUVMDYNUVIUVAUULUVMUEUVJHFUUKSXEXFQXGXIYNUXGU
        XMYNUXGUHUWGUVMDYNUVIUXGUWGUVMUEUVJHFUWFSXEXFQXGXIXHWBXJXKDBUULUWGJXLWG
        UVSUUBUVMHXCZUXHUXJUWKWJYQUXPYRYTUVRYNYOUXPYPYNUWQUXPUWSUUBUVMHXDVIWBXJ
        UUBUVMUUKUWFHXMXFXSXNXOUWDUWIAUCUUBUWKUUMUWHUVTUUKUWFJHWKWLXPXQUVSUWBUW
        DAUUBUVSUVAUHZUWAUUMUVTUVSUUTUVAUVBUWAUUMUMYQUUTYRYTUVRUVCXJUXQUUMBUUSU
        XQDBUULJUUAUVFUVRUVAUVGUTUVSUUBDUUKHYQUVHYRYTUVRUVOXJWCWDRWEUUCUUSUUMIW
        RWGWLXRXTUVSUUQUWBAUUBUXQUUCUUSIXCZUVRUUPUUQUWBVTUXQUUTUXRUUAUUTUVRUVAU
        VDUTUUCUUSIXDVIUUAUVRUVAYAUUAUVAUUPUVRUVQYBUXRUVRUUPUHUHUWBUUQUUCUUSUUE
        UUOIXLYCYDXRXTWIACUUBUUCUUOKUBYEXQUUAUUJCUUBUUAUUEUUBUEZUHZUUGUUHJUKZUU
        NUKZIUKZUYAUUIUXTUUFUYBIUXTAUUEUUOUYBUUBKYFUBUUKUUEUMZUUOUYBUMUXTUYDUUM
        UYAUUNUUKUUEJHWKWSVCUUAUXSWQUXTUYAUUNYIYGWSUUAUUTUXSUYAUUSUEUYCUYAUMUVD
        UXTUYABUUSUXTDBUUHJUUAUVFUXSUVGVHUUAUUBDUUEHUVPWCZWDRWEUUCUUSUYAIWRWGUX
        TAUUHEUUKULUUIDJYFUAUXTUUKUUHUMZUHUUKUUHEUXTUYFWQYHUYEUXTEUUHNYQYPYRYTU
        XSYNYOYPYJXJYKYGYLWIYM $.
    $}

    $d D e j k $.  $d E d e j k x $.  $d F d e j k $.  $d G d e j k $.
    $d H d e j k $.  $d V d e i j k $.  $d W d e i j k $.  $d X d e i j k $.
    $( An isomorphism of simple pseudographs is a bijection between their
       vertices which induces a bijection between their edges.  (Contributed by
       AV, 21-Apr-2025.) $)
    isuspgrim0 $p |- ( ( G e. USPGraph /\ H e. USPGraph /\ F e. X )
                       -> ( F e. ( G GraphIso H ) <-> ( F : V -1-1-onto-> W
                         /\ ( e e. E |-> ( F " e ) ) : E -1-1-onto-> D ) ) ) $=
      ( vi vk wcel cfv wceq wa wb vj vx vd cuspgr w3a cgrim wf1o ciedg cdm cima
      co wral wex cmpt eqid isgrim wreu wrex cedg eleq2i uspgruhgr uhgredgiedgb
      cv cuhgr syl bitrid 3ad2ant1 ad2antrr biimpa 2fveq3 fveq2 imaeq2d eqeq12d
      wi adantl wfun uhgrfun 3ad2ant2 ad3antrrr f1of ffvelcdmda iedgedg syl2anc
      rspcv wf sylibr eleq1 syl5ibcom syld ex impr adantr imp imaeq2 syl5ibrcom
      com23 eleq1d rexlimdva mpd ralrimiva ccnv simprl f1ocnvdm sylan f1ocnvfv2
      rspccv fveqeq2d eqeq2 simpll1 uspgriedgedg syl2an2r eqcom reubii ad4antlr
      wf1 wss f1of1 cupgr uspgrupgr jca upgrss cvtx cpw c0 wne chash c2 cle wbr
      biimpi edgupgr syl2an simp1d elpwid sseqtrrdi mpbird sylbid f1oeq1 bitrd
      cvv f1imaeq syl12anc reubidva eqeq1 reubidv ralrimiv f1ompt sylanbrc fvex
      cbvmptv exlimdv dmex mptex a1i isuspgrim0lem fveq1 ralbidv anbi12d spcedv
      impbid mp1i pm5.32da ) EUDPZFUDPZDIPZUEZDEFUFUKPGHDUGZEUHQZUIZFUHQZUIZUAV
      CZUGZNVCZUVLQZUVJQZDUVNUVHQZUJZRZNUVIULZSZUAUMZSUVGCABCDBVCZUJZUNZUGZSUVJ
      NUAUVHDEFGHUDUDIJKUVHUOZUVJUOZUPUVFUVGUWBUWFUVFUVGSZUWBCAUBCDUBVCZUJZUNZU
      GZUWFUWIUWBUWMUWIUWAUWMUAUWIUWAUWMUWIUWASZUWDAPZBCULUCVCZUWDRZBCUQZUCAULU
      WMUWNUWOBCUWNUWCCPZSZUWCOVCZUVHQZRZOUVIURZUWOUWNUWSUXDUVFUWSUXDTZUVGUWAUV
      CUVDUXEUVEUWSUWCEUSQZPZUVCUXDCUXFUWCLUTZUVCEVDPUXGUXDTEVAOUWCEUVHUWGVBVEV
      FVGVHVIUWTUXCUWOOUVIUWTUXAUVIPZSUWOUXCDUXBUJZAPZUWTUXIUXKUWNUXIUXKVNZUWSU
      WIUVMUVTUXLUWIUVMSZUXIUVTUXKUXMUXIUVTUXKVNUXMUXISZUVTUXAUVLQZUVJQZUXJRZUX
      KUXIUVTUXQVNUXMUVSUXQNUXAUVIUVNUXARZUVPUXPUVRUXJUVNUXAUVJUVLVJUXRUVQUXBDU
      VNUXAUVHVKVLVMWDVOUXNUXPAPZUXQUXKUXNUXPFUSQZPZUXSUXNUVJVPZUXOUVKPUYAUVFUY
      BUVGUVMUXIUVDUVCUYBUVEUVDFVDPZUYBFVAZUVJFUWHVQVEVRVSUXMUVIUVKUXAUVLUVMUVI
      UVKUVLWEUWIUVIUVKUVLVTVOWAUVJFUXOUWHWBWCAUXTUXPMUTWFUXPUXJAWGWHWIWJWPWKWL
      WMUXCUWDUXJAUWCUXBDWNWQWOWRWSWTUWNUWRUCAUWNUWPAPZUWPUXAUVJQZRZOUVKURZUWRU
      VFUYEUYHTZUVGUWAUVDUVCUYIUVEUYEUWPUXTPZUVDUYHAUXTUWPMUTUVDUYCUYJUYHTUYDOU
      WPFUVJUWHVBVEVFVRVHUWNUYGUWROUVKUWNUXAUVKPZSZUXAUVLXAQZUVIPZUYGUWRVNZUWNU
      VMUYKUYNUWIUVMUVTXBZUVIUVKUXAUVLXCXDZUYLUYNUYMUVLQZUVJQZDUYMUVHQZUJZRZUYO
      UWNUYNVUBVNZUYKUWAVUCUWIUVTVUCUVMUVSVUBNUYMUVIUVNUYMRZUVPUYSUVRVUAUVNUYMU
      VJUVLVJVUDUVQUYTDUVNUYMUVHVKVLVMXFVOVOWLUYLVUBUYFVUARZUYOUYLUYRUXAVUAUVJU
      WNUVMUYKUYRUXARUYPUVIUVKUXAUVLXEXDXGUYLVUEUYOUYLVUESZUYGUWPVUARZUWRVUEUYG
      VUGTUYLUYFVUAUWPXHVOVUFVUGUWRVUFVUGSUWRVUAUWDRZBCUQZUYLVUIVUEVUGUYLVUIUYT
      UWCRZBCUQZUYLUWCUYTRZBCUQZVUKUWNUVCUYKUYNVUMUVCUVDUVEUVGUWAXIUYQBCEUVHUYM
      LUWGXJXKVUJVULBCUYTUWCXLXMWFUYLVUHVUJBCUYLUWSSZGHDXOZUYTGXPZUWCGXPVUHVUJT
      UVGVUOUVFUWAUYKUWSGHDXQXNVUNEXRPZUYNSZVUPUYLVURUWSUYLVUQUYNUVFVUQUVGUWAUY
      KUVCUVDVUQUVEEXSVGVSZUYQXTWLUVHUYMEGJUWGYAVEVUNUWCEYBQZGVUNUWCVUTVUNUWCVU
      TYCPZUWCYDYEZUWCYFQYGYHYIZUYLVUQUXGVVAVVBVVCUEUWSVUSUWSUXGUXHYJUWCEYKYLYM
      YNJYOGHUYTUWCDUUAUUBUUCYPVHVUGUWRVUITVUFVUGUWQVUHBCUWPVUAUWDUUDUUEVOYPWJY
      QWJYQWIWSWRYQUUFBUCCAUWDUWLUBBCUWKUWDUWJUWCDWNUUJZUUGUUHWJUUKUWIUWMUWBUWI
      UWMSZUWAUVIUVKBUVIUWCUVHQUWLQUVJXAQZUNZUGZUVNVVGQZUVJQUVRRZNUVIULZSUAYTVV
      GVVGYTPVVEBUVIVVFUVHEUHUUIUULUUMUUNBANCDEFUVHUVJUWLVVGGHIJKLMUWGUWHVVDVVG
      UOUUOUVLVVGRZUVMVVHUVTVVKUVIUVKUVLVVGYRVVLUVSVVJNUVIVVLUVOVVIUVRUVJUVNUVL
      VVGUUPXGUUQUURUUSWJUUTUWLUWERUWMUWFTUWIVVDCAUWLUWEYRUVAYSUVBYS $.

    $d D a b m n $.  $d D x y $.  $d E a b m n $.  $d E y $.  $d F a b m n $.
    $d F y $.  $d G a b d e m n x y $.  $d H a b m n $.  $d H x y $.
    $d V a b m n $.  $d V x y $.  $d W a b m n $.
    $( Lemma for ~ isuspgrim .  (Contributed by AV, 27-Apr-2025.) $)
    isuspgrimlem $p |- ( ( ( ( G e. USPGraph /\ H e. USPGraph )
                             /\ F : V -1-1-onto-> W ) /\ A. x e. V A. y e. V
                        ( { x , y } e. E <-> { ( F ` x ) , ( F ` y ) } e. D ) )
                         -> ( e e. E |-> ( F " e ) ) : E -1-1-onto-> D ) $=
      ( wcel wa wceq adantr wi adantl vd va vb vm vn cuspgr wf1o cv cpr wb wral
      cfv cima wreu cmpt wrex cupgr uspgrupgr upgredg sylan preq12 eleq1d fveq2
      weq preq12d bibi12d rspc2gv com12 imp f1ofn ad3antlr simprl simpr fnimapr
      syl3anc eqcomd bitrd biimpd eleq1 imaeq2 imbi12d mpbird exp31 com23 com24
      wfn rexlimdvv mpd ralrimiv wfo f1ofo foelrn anim12d syl eqeq2d ancoms w3a
      ex anim1i 3anass sylibr reueq bilani eqcom reubii wf1 wss f1of1 ad3antrrr
      prssi cuhgr cedg cpw uspgruhgr eleq2i biimpi cvtx edguhgr pweqi eleqtrrdi
      syl2an elpwid f1imaeq syl12anc reubidva sylbird bibi2d reubidv syl5ibrcom
      eqeq1 syld impancom impl sylbid exp32 rexlimdva impd ralrimiva f1ompt
      eqid sylanbrc ) GUFOZHUFOZPZIJFUGZPZAUHZBUHZUIZEOZUUGFULZUUHFULZUIZCOZUJZ
      BIUKAIUKZPZFDUHZUMZCOZDEUKUAUHZUUSQZDEUNZUACUKECDEUUSUOZUGUUQUUTDEUUQUURE
      OZUUTUUQUVEPZUURUBUHZUCUHZUIZQZUCIUPUBIUPZUUTUUQGUQOZUVEUVKUUFUVLUUPUUDUV
      LUUEUUBUVLUUCGURRRRUUREGIUBUCKMUSUTUVFUVJUUTUBUCIIUUQUVEUVGIOZUVHIOZPZUVJ
      UUTSSUUQUVJUVOUVEUUTUUQUVOUVJUVEUUTSZUUQUVOUVJUVPUUQUVOPZUVJPZUVPUVIEOZFU
      VIUMZCOZSZUVRUVSUWAUVQUVSUWAUJUVJUVQUVSUVGFULZUVHFULZUIZCOZUWAUUQUVOUVSUW
      FUJZUUPUVOUWGSUUFUVOUUPUWGUUOUWGABUVGUVHIIAUBVDZBUCVDZPZUUJUVSUUNUWFUWJUU
      IUVIEUUGUUHUVGUVHVAVBUWJUUMUWECUWJUUKUWCUULUWDUWHUUKUWCQUWIUUGUVGFVCRUWIU
      ULUWDQUWHUUHUVHFVCTVEVBVFVGVHTVIUVQUWEUVTCUVQUVTUWEUVQFIWFZUVMUVNUVTUWEQU
      UEUWKUUDUUPUVOIJFVJZVKUUQUVMUVNVLUVOUVNUUQUVMUVNVMTIUVGUVHFVNVOVPVBVQRVRU
      VJUVPUWBUJUVQUVJUVEUVSUUTUWAUURUVIEVSUVJUUSUVTCUURUVIFVTVBWATWBWCWDWEVIWG
      WHWRWIUUQUVCUACUUQUVACOZPZUVAUVIQZUCJUPUBJUPZUVCUUQHUQOZUWMUWPUUCUWQUUBUU
      EUUPHURVKUVACHJUBUCLNUSUTUWNUWOUVCUBUCJJUUQUVGJOZUVHJOZPZUWMUWOUVCSUUQUWT
      PZUWOUWMUVCUXAUVGUDUHZFULZQZUDIUPZUVHUEUHZFULZQZUEIUPZPZUWOUWMUVCSZSZUUQU
      WTUXJUUFUWTUXJSZUUPUUEUXMUUDUUEIJFWJZUXMIJFWKUXNUWRUXEUWSUXIUXNUWRUXEUDIJ
      UVGFWLWRUXNUWSUXIUEIJUVHFWLWRWMWNTRVIUXAUXEUXIUXLUXAUXDUXIUXLSUDIUXAUXBIO
      ZPZUXIUXDUXLUXPUXHUXDUXLSUEIUXPUXFIOZPZUXHUXDUXLUXRUXHUXDPZPUWOUVAUXCUXGU
      IZQZUXKUXSUWOUYAUJZUXRUXDUXHUYBUXDUXHPUVIUXTUVAUVGUVHUXCUXGVAWOWPTUXRUYAU
      XKSUXSUXRUXKUYAUXTCOZUXTUUSQZDEUNZSZUXAUXOUXQUYFUUQUXOUXQPZUYFSUWTUUFUYGU
      UPUYFUUFUYGPZUUPUXBUXFUIZEOZUYCUJZUYFUYGUUPUYKSUUFUUOUYKABUXBUXFIIAUDVDZB
      UEVDZPZUUJUYJUUNUYCUYNUUIUYIEUUGUUHUXBUXFVAVBUYNUUMUXTCUYNUUKUXCUULUXGUYL
      UUKUXCQUYMUUGUXBFVCRUYMUULUXGQUYLUUHUXFFVCTVEVBVFVGTUYHUXTFUYIUMZQZUYKUYF
      SZUYHUYOUXTUYHUWKUXOUXQWQZUYOUXTQUYHUWKUYGPUYRUUFUWKUYGUUEUWKUUDUWLTWSUWK
      UXOUXQWTXAIUXBUXFFVNWNVPUYHUYQUYPUYJUYOCOZUJZUYSUYOUUSQZDEUNZSZSUYHUYTVUC
      UYHUYTPUYSUYJVUBUYHUYTVMUYHUYJVUBSUYTUYHUYJVUBUYHUYJPZVUBUYIUURQZDEUNZVUD
      UURUYIQZDEUNZVUFUYJVUHUYHDEUYIXBXCVUEVUGDEUYIUURXDXEXAVUDVUAVUEDEVUDUVEPZ
      IJFXFZUYIIXGZUURIXGVUAVUEUJUUFVUJUYGUYJUVEUUEVUJUUDIJFXHTXIUYGVUKUUFUYJUV
      EUXBUXFIXJVKVUIUURIVUDGXKOZUURGXLULZOZUURIXMZOUVEUUDVULUUEUYGUYJUUBVULUUC
      GXNRXIUVEVUNEVUMUURMXOXPVULVUNPUURGXQULZXMVUOUURGXRIVUPKXSXTYAYBIJUYIUURF
      YCYDYEWBWRRYFWRUYPUYKUYTUYFVUCUYPUYCUYSUYJUXTUYOCVSZYGUYPUYCUYSUYEVUBVUQU
      YPUYDVUADEUXTUYOUUSYJYHWAWAYIWHYKYLRYMUYAUWMUYCUVCUYEUVAUXTCVSUYAUVBUYDDE
      UVAUXTUUSYJYHWAYIRYNYOYPWDYPYQWHWDYLWGWHYRDUAECUUSUVDUVDYTYSUUA $.

    $( A class is an isomorphism of simple pseudographs iff it is a bijection
       between their vertices that preserves adjacency, i.e. there is an edge
       in one graph connecting one or two vertices iff there is an edge in the
       other graph connecting the vertices which are the images of the
       vertices.  This corresponds to the formal definition in [Bollobas] p. 3
       and the definition in [Diestel] p. 3.  (Contributed by AV,
       27-Apr-2025.) $)
    isuspgrim $p |- ( ( G e. USPGraph /\ H e. USPGraph )
                      -> ( F e. ( G GraphIso H )
                           <-> ( F : V -1-1-onto-> W /\ A. x e. V A. y e. V
                 ( { x , y } e. E <-> { ( F ` x ) , ( F ` y ) } e. D ) ) ) ) $=
      ( ve cuspgr wcel wa wf1o cv cvv cgrim co cpr cfv wral cuhgr w3a uspgruhgr
      wb anim12i anim1i df-3an sylibr uhgrimprop syl ex wi f1of cvtx fvexi fexd
      a1i cima cmpt simpllr isuspgrimlem adantlr isuspgrim0 ad5ant124 mpbir2and
      adantl mpdan expimpd impbid ) FOPZGOPZQZEFGUAUBPZHIERZASZBSZUCDPVTEUDWAEU
      DUCCPUIBHUEAHUEZQZVQVRWCVQVRQZFUFPZGUFPZVRUGZWCWDWEWFQZVRQWGVQWHVRVOWEVPW
      FFUHGUHUJUKWEWFVRULUMABCDEFGHILMJKUNUOUPVQVSWBVRVQVSQZETPZWBVRUQVSWJVQVSH
      ITEHIEURHTPVSHFUSJUTVBVAVKWIWJQZWBVRWKWBQVRVSDCNDENSVCVDRZVQVSWJWBVEWIWBW
      LWJABCNDEFGHIJKLMVFVGVOVPWJVRVSWLQUIVSWBCNDEFGHITJKLMVHVIVJUPVLVMVN $.
  $}

  ${
    upgrimwlk.i $e |- I = ( iEdg ` G ) $.
    upgrimwlk.j $e |- J = ( iEdg ` H ) $.
    upgrimwlk.g $e |- ( ph -> G e. USPGraph ) $.
    upgrimwlk.h $e |- ( ph -> H e. USPGraph ) $.
    upgrimwlk.n $e |- ( ph -> N e. ( G GraphIso H ) ) $.
    upgrimwlk.e $e |- E = ( x e. dom F
                            |-> ( `' J ` ( N " ( I ` ( F ` x ) ) ) ) ) $.
    ${
      $d F x $.  $d J x $.  $d ph x $.
      upgrimwlk.f $e |- ( ph -> F e. Word dom I ) $.
      $( Lemma 1 for ~ upgrimwlk and ~ upgrimwlklen .  (Contributed by AV,
         25-Oct-2025.) $)
      upgrimwlklem1 $p |- ( ph -> ( # ` E ) = ( # ` F ) ) $=
        ( chash cfv wfn wcel cdm wceq cv cima ccnv cmpt wral wa fvexd ralrimiva
        cvv eqid fnmpt syl fneq1i sylibr hashfn cword cfzo co wf wfun wrdf ffun
        cc0 3syl funfnd eqtr4d ) ACQRZDUAZQRZDQRZACVJSZVIVKUBABVJIBUCZDRGRUDZHU
        EZRZUFZVJSZVMAVQUKTZBVJUGVSAVTBVJAVNVJTUHVOVPUIUJBVJVQVRUKVRULUMUNVJCVR
        OUOUPVJCUQUNADVJSVLVKUBADADGUAZURTVEVLUSUTZWADVADVBPWADVCWBWADVDVFVGVJD
        UQUNVH $.

      $( Lemma 2 for ~ upgrimwlk .  (Contributed by AV, 25-Oct-2025.) $)
      upgrimwlklem2 $p |- ( ph -> E e. Word dom J ) $=
        ( cfv wf wcel syl cc0 chash cfzo co cdm cword cv cima ccnv wa cedg wf1o
        cuspgr adantr uspgrf1oedg cuhgr cgrim uspgruhgr wfun uhgrfun wrdf ffdmd
        ffvelcdmda iedgedg syl2anc eqid uhgrimedgi syl12anc fmptd upgrimwlklem1
        jca f1ocnvdm oveq2d wceq iswrdb eqcomd sylbi eqtrd feq2d mpbird sylibr
        fdm ) AUACUBQZUCUDZHUEZCRZCWEUFSAWFDUEZWECRABWGIBUGZDQZGQZUHZHUIQZWECAW
        HWGSZUJZWEFUKQZHULZWKWOSZWLWESWNFUMSZWPAWRWMMUNHFKUOTWNEUPSZFUPSZUJZIEF
        UQUDSZWJEUKQZSZWQAXAWMAWSWTAEUMSWSLEURTZAWRWTMFURTVKUNAXBWMNUNWNGUSZWIG
        UEZSXDAXFWMAWSXFXEGEJUTTUNAWGXGWHDADXGUFSZWGXGDRPXHUADUBQZUCUDZXGDXGDVA
        VBTVCGEWIJVDVEWOXCIEFWJXCVFWOVFVGVHWEWOWKHVLVEOVIAWDWGWECAWDXJWGAWCXIUA
        UCABCDEFGHIJKLMNOPVJVMAXHXJWGVNZPXHXJXGDRZXKXGDVOXLWGXJXJXGDWBVPVQTVRVS
        VTWECVOWA $.

      $d E x $.  $d I x $.  $d N x $.  $d X x $.
      $( Lemma 3 for ~ upgrimwlk .  (Contributed by AV, 25-Oct-2025.) $)
      upgrimwlklem3 $p |- ( ( ph /\ X e. ( 0 ..^ ( # ` E ) ) )
                          -> ( J ` ( E ` X ) ) = ( N " ( I ` ( F ` X ) ) ) ) $=
        ( cfv wcel syl cc0 chash cfzo co cima ccnv cdm cvv cmpt wceq a1i 2fveq3
        wa cv imaeq2d fveq2d adantl upgrimwlklem1 oveq2d cword fdm eqcomd eqtrd
        wf wrdf eleq2d biimpa fvexd fvmptd cedg cuspgr adantr uspgrf1oedg cuhgr
        wf1o cgrim uspgruhgr wfun uhgrfun wrdfd ffvelcdmda iedgedg syl2anc eqid
        jca uhgrimedgi syl12anc f1ocnvfv2 ) AJUACUBRZUCUDZSZUMZJCRZHRIJDRZGRZUE
        ZHUFZRZHRZWPWLWMWRHWLBJIBUNZDRGRZUEZWQRZWRDUGZCUHCBXDXCUIUJWLPUKWTJUJZX
        CWRUJWLXEXBWPWQXEXAWOIWTJGDULUOUPUQAWKJXDSAWJXDJAWJUADUBRZUCUDZXDAWIXFU
        AUCABCDEFGHIKLMNOPQURZUSADGUGZUTSZXGXDUJZQXJXGXIDVDZXKXIDVEXLXDXGXGXIDV
        AVBTTVCVFVGWLWPWQVHVIUPWLHUGZFVJRZHVOZWPXNSZWSWPUJWLFVKSZXOAXQWKNVLHFLV
        MTWLEVNSZFVNSZUMZIEFVPUDSZWOEVJRZSZXPAXTWKAXRXSAEVKSXRMEVQTZAXQXSNFVQTW
        EVLAYAWKOVLWLGVRZWNXISYCAYEWKAXRYEYDGEKVSTVLAWJXIJDAXIWIDXHQVTWAGEWNKWB
        WCXNYBIEFWOYBWDXNWDWFWGXMXNWPHWHWCVC $.

      upgrimwlklem.p $e |- ( ph -> P : ( 0 ... ( # ` F ) ) --> ( Vtx ` G ) ) $.
      $( Lemma 4 for ~ upgrimwlk .  (Contributed by AV, 28-Oct-2025.) $)
      upgrimwlklem4 $p |- ( ph -> ( N o. P ) :
                                ( 0 ... ( # ` E ) ) --> ( Vtx ` H ) ) $=
        ( cc0 cfv chash co cvtx cgrim wcel wf1o eqid grimf1o f1of upgrimwlklem1
        cfz wf 3syl oveq2d feq2d mpbird fcod ) ASDUATZUKUBZFUCTZGUCTZJCAJFGUDUB
        UEUTVAJUFUTVAJULOJFGUTVAUTUGVAUGUHUTVAJUIUMAUSUTCULSEUATZUKUBZUTCULRAUS
        VCUTCAURVBSUKABDEFGHIJKLMNOPQUJUNUOUPUQ $.
    $}

    $d F x $.  $d G x $.  $d I x $.  $d J x $.  $d P x $.  $d ph x $.
    ${
      $d ph i x $.
      upgrimwlk.w $e |- ( ph -> F ( Walks ` G ) P ) $.
      $( Lemma 5 for ~ upgrimwlk .  (Contributed by AV, 28-Oct-2025.) $)
      upgrimwlklem5 $p |- ( ( ph /\ i e. ( 0 ..^ ( # ` E ) ) )
                  -> ( N " ( I ` ( F ` i ) ) )
                     = { ( ( N o. P ) ` i ) , ( ( N o. P ) ` ( i + 1 ) ) } ) $=
        ( cfv wcel cv cc0 chash cfzo co cima ccom c1 caddc cpr wceq cwlks cword
        wbr cdm wlkf syl upgrimwlklem1 oveq2d eleq2d cupgr uspgrupgr upgrwlkedg
        wral cuspgr syl2anc wi wa weq 2fveq3 fveq2 fvoveq1 preq12d rspcv adantl
        eqeq12d imaeq2 cvtx wfn cgrim wf1o eqid grimf1o 3syl adantr cfz wf wlkp
        f1ofn elfzofz ffvelcdmd fzofzp1 fnimapr syl3anc fvco3d eqtr4d sylan9eqr
        ex syld mpid sylbid imp ) ADUAZUBEUCSZUDUEZTZKXCFSISZUFZXCKCUGZSZXCUHUI
        UEZXISZUJZUKZAXFXCUBFUCSZUDUEZTZXNAXEXPXCAXDXOUBUDABEFGHIJKLMNOPQAFCGUL
        SUNZFIUOUMTRCFGILUPUQURUSUTAXQBUAZFSISZXSCSZXSUHUIUECSZUJZUKZBXPVDZXNAG
        VATZXRYEAGVETYFNGVBUQRCBFGILVCVFAXQYEXNVGAXQVHZYEXGXCCSZXKCSZUJZUKZXNXQ
        YEYKVGAYDYKBXCXPBDVIZXTXGYCYJXSXCIFVJYLYAYHYBYIXSXCCVKXSXCUHCUIVLVMVPVN
        VOYGYKXNYKYGXHKYJUFZXMXGYJKVQYGYMYHKSZYIKSZUJZXMYGKGVRSZVSZYHYQTYIYQTYM
        YPUKAYRXQAKGHVTUETYQHVRSZKWAYRPKGHYQYSYQWBZYSWBWCYQYSKWIWDWEYGUBXOWFUEZ
        YQXCCAUUAYQCWGZXQAXRUUBRCFGYQYTWHZUQWEZXQXCUUATAXCUBXOWJVOZWKYGUUAYQXKC
        UUDXQXKUUATAUBXOXCWLVOZWKYQYHYIKWMWNYGXJYNXLYOYGUUAYQXCKCYGXRUUBAXRXQRW
        EUUCUQUUEWOYGUUAYQXKKCUUDUUFWOVMWPWQWRWSWRWTXAXB $.

      $d E i x $.  $d H i $.  $d J i $.  $d N i x $.  $d P i $.
      $( Graph isomorphisms between simple pseudographs map walks onto walks.
         (Contributed by AV, 28-Oct-2025.) $)
      upgrimwlk $p |- ( ph -> E ( Walks ` H ) ( N o. P ) ) $=
        ( vi cfv wcel ccom cwlks wbr cdm cword cc0 chash co cvtx wf cv c1 caddc
        wceq cfzo wral wlkf upgrimwlklem2 eqid wlkp upgrimwlklem4 upgrimwlklem3
        cfz cpr syl wa upgrimwlklem5 eqtrd ralrimiva cuspgr cupgr w3a uspgrupgr
        cima wb upgriswlk 3syl mpbir3and ) ADJCUAZGUBSUCZDIUDUETZUFDUGSZVCUHGUI
        SZVSUJZRUKZDSISZWEVSSWEULUMUHVSSVDZUNZRUFWBUOUHZUPZABDEFGHIJKLMNOPAECFU
        BSUCZEHUDUETQCEFHKUQVEZURABCDEFGHIJKLMNOPWLAWKUFEUGSVCUHFUISZCUJQCEFWMW
        MUSUTVEVAAWHRWIAWEWITVFWFJWEESHSVNWGABDEFGHIJWEKLMNOPWLVBABCRDEFGHIJKLM
        NOPQVGVHVIAGVJTGVKTVTWAWDWJVLVONGVMVSRDGIWCWCUSLVPVQVR $.

      $( Graph isomorphisms between simple pseudographs map walks onto walks of
         the same length.  (Contributed by AV, 6-Nov-2025.) $)
      upgrimwlklen $p |- ( ph -> ( E ( Walks ` H ) ( N o. P )
                                   /\ ( # ` E ) = ( # ` F ) ) ) $=
        ( cwlks cfv wbr ccom chash wceq upgrimwlk cword wcel wlkf upgrimwlklem1
        cdm syl jca ) ADJCUAGRSTDUBSEUBSUCABCDEFGHIJKLMNOPQUDABDEFGHIJKLMNOPAEC
        FRSTEHUIUEUFQCEFHKUGUJUHUK $.
    $}

    ${
      upgrimtrls.t $e |- ( ph -> F ( Trails ` G ) P ) $.
      $( Lemma 1 for ~ upgrimtrls .  (Contributed by AV, 29-Oct-2025.) $)
      upgrimtrlslem1 $p |- ( ( ph /\ X e. dom F )
                             -> ( N " ( I ` ( F ` X ) ) ) e. ( Edg ` H ) ) $=
        ( wcel cfv cdm wa cuhgr cgrim cedg cima cuspgr uspgruhgr syl jca adantr
        co wfun uhgrfun ctrls wbr cwlks trliswlk cword wlkf cc0 chash cfzo wrdf
        wf ffdmd 3syl ffvelcdmda iedgedg syl2an2r eqid uhgrimedgi syl12anc ) AK
        EUAZSZUBFUCSZGUCSZUBZJFGUDULSZKETZHTZFUETZSZJWAUFGUETZSAVRVOAVPVQAFUGSV
        PNFUHUIZAGUGSVQOGUHUIUJUKAVSVOPUKAHUMZVOVTHUAZSWCAVPWFWEHFLUNUIAVNWGKEA
        ECFUOTUPECFUQTUPZVNWGEVEZRCEFURWHEWGUSSZWICEFHLUTWJVAEVBTVCULWGEWGEVDVF
        UIVGVHHFVTLVIVJWDWBJFGWAWBVKWDVKVLVM $.

      $( Lemma 2 for ~ upgrimtrls .  (Contributed by AV, 29-Oct-2025.) $)
      upgrimtrlslem2 $p |- ( ( ph /\ ( x e. dom F /\ y e. dom F ) )
                      -> ( ( `' J ` ( N " ( I ` ( F ` x ) ) ) )
                         = ( `' J ` ( N " ( I ` ( F ` y ) ) ) ) -> x = y ) ) $=
        ( wcel cfv cv cdm wa cima ccnv wceq weq cedg wf1 crn cuspgr uspgrf1oedg
        wf1o f1of1 3syl upgrimtrlslem1 ciedg edgval eqcomi rneqi eqtri eleqtrdi
        wi anim12dan f1ocnvfvrneq syl2an2r cvtx wss wb cgrim eqid grimf1o cuhgr
        co uspgruhgr syl ctrls wbr cwlks wf trliswlk cword chash cfzo wlkf wrdf
        cc0 id ffdmd ffvelcdmda uhgrss f1imaeq trlf1 f1f fdm eqcomd biimpcd mpd
        f1eq2 jca f1cofveqaeq sylan sylbid syld ) ABUAZFUBZSZCUAZXFSZUCZUCZKXEF
        TZITZUDZJUEZTKXHFTZITZUDZXOTUFZXNXRUFZBCUGZAJUBZHUHTZJUIZXJXNJUJZSZXRYE
        SZUCXSXTVCAHUKSYBYCJUMYDOJHMULYBYCJUNUOAXGYFXIYGAXGUCXNYCYEABDEFGHIJKXE
        LMNOPQRUPYCHUQTZUJYEHURYHJJYHMUSUTVAZVBAXIUCXRYCYEABDEFGHIJKXHLMNOPQRUP
        YIVBVDYBYCXNXRJVEVFXKXTXMXQUFZYAAGVGTZHVGTZKUIZXJXMYKVHZXQYKVHZUCXTYJVI
        AKGHVJVNSYKYLKUMYMPKGHYKYLYKVKZYLVKVLYKYLKUNUOAXGYNXIYOAGVMSZXGXLIUBZSY
        NAGUKSZYQNGVOVPZAXFYRXEFAFDGVQTVRZFDGVSTVRZXFYRFVTZRDFGWAUUBFYRWBSWGFWC
        TWDVNZYRFVTZUUCDFGILWEYRFWFUUEUUDYRFUUEWHWIUOUOZWJIXLGYKYPLWKVFAYQXIXPY
        RSYOYTAXFYRXHFUUFWJIXPGYKYPLWKVFVDYKYLXMXQKWLVFAYRGUHTZIUIZXFYRFUIZUCXJ
        YJYAVCAUUHUUIAYSYRUUGIUMUUHNIGLULYRUUGIUNUOAUUAUUDYRFUIZUUIRDFGILWMUUJU
        UDXFUFZUUIUUJUUEUUKUUDYRFWNUUEXFUUDUUDYRFWOWPVPUUKUUJUUIUUDXFYRFWSWQWRU
        OWTXFYRUUGIFXEXHXAXBXCXD $.

      $d E x y $.  $d F y $.  $d I y $.  $d J y $.  $d N x y $.  $d ph y $.
      $( Graph isomorphisms between simple pseudographs map trails onto trails.
         (Contributed by AV, 29-Oct-2025.) $)
      upgrimtrls $p |- ( ph -> E ( Trails ` H ) ( N o. P ) ) $=
        ( vy cfv wcel ccom cwlks wbr ccnv wfun ctrls trliswlk syl upgrimwlk cc0
        chash cfzo co cdm wf1 cv cima wral wceq weq wi wa cedg wf1o uspgrf1oedg
        cuspgr adantr upgrimtrlslem1 f1ocnvdm syl2anc upgrimtrlslem2 ralrimivva
        ralrimiva 2fveq3 imaeq2d fveq2d f1mpt sylanbrc eqidd wlkf upgrimwlklem1
        cword 3syl oveq2d wrddm eqtr4d f1eq123d mpbird wf df-f1 simprbi istrl )
        ADJCUAZGUBSUCDUDUEZDWMGUFSUCABCDEFGHIJKLMNOPAECFUFSUCZECFUBSUCZQCEFUGZU
        HUIAUJDUKSZULUMZIUNZDUOZWNAXAEUNZWTDUOZAJBUPZESHSZUQZIUDZSZWTTZBXBURXHJ
        RUPZESHSZUQZXGSZUSBRUTZVAZRXBURBXBURXCAXIBXBAXDXBTZVBZWTGVCSZIVDZXFXRTX
        IXQGVFTZXSAXTXPNVGIGLVEUHABCDEFGHIJXDKLMNOPQVHWTXRXFIVIVJVMAXOBRXBXBABR
        CDEFGHIJKLMNOPQVKVLBRXBWTXHXMDPXNXFXLXGXNXEXKJXDXJHEVNVOVPVQVRAWSXBWTWT
        DDADVSAWSUJEUKSZULUMZXBAWRYAUJULABDEFGHIJKLMNOPAWOWPEHUNZWBTZQWQCEFHKVT
        ZWCWAWDAWOXBYBUSZQWOWPYDYFWQYEYCEWEWCUHWFAWTVSWGWHXAWSWTDWIWNWSWTDWJWKU
        HWMDGWLVR $.
    $}

    ${
      upgrimpths.p $e |- ( ph -> F ( Paths ` G ) P ) $.
      $( Lemma 1 for ~ upgrimpths .  (Contributed by AV, 30-Oct-2025.) $)
      upgrimpthslem1 $p |- ( ph
                           -> Fun `' ( ( N o. P ) |` ( 1 ..^ ( # ` F ) ) ) ) $=
        ( cfv ccnv wfun c1 chash cfzo co cres ccom cpths wbr ctrls cc0 cpr cima
        cin wceq ispth simp2bi syl cgrim wcel cvtx wf1o eqid grimf1o wfo dff1o3
        c0 simprbi 3syl funco syl2anc resco cnveqi cnvco eqtri funeqi sylibr )
        ACUAEUBRZUCUDZUEZSZJSZUFZTZJCUFVRUEZSZTAVTTZWATZWCAECFUGRUHZWFQWHECFUIR
        UHWFCUJVQUKULCVRULUMVFUNCEFUOUPUQAJFGURUDUSFUTRZGUTRZJVAZWGOJFGWIWJWIVB
        WJVBVCWKWIWJJVDWGWIWJJVEVGVHVTWAVIVJWEWBWEJVSUFZSWBWDWLJCVRVKVLJVSVMVNV
        OVP $.

      $( Lemma 2 for ~ upgrimpths .  (Contributed by AV, 31-Oct-2025.) $)
      upgrimpthslem2 $p |- ( ( ph /\ X e. ( 1 ..^ ( # ` F ) ) )
                 -> ( -. ( ( N o. P ) ` X ) = ( ( N o. P ) ` 0 )
                   /\ -. ( ( N o. P ) ` X ) = ( ( N o. P ) ` ( # ` F ) ) ) ) $=
        ( cfv cc0 c1 chash cfzo co wcel wa ccom wne wceq wn cvtx wf1 cgrim wf1o
        eqid grimf1o f1of1 3syl adantr cpths wbr cwlks wi pthiswlk wlkp fzo0ss1
        cfz wf fzossfz sstri sseli adantl ffvelcdmd imp cn0 wlkcl 0elfz syl cle
        ex simpr elfzole1 cz elfzoelz zgt0ge1 gt0ne0d sylbird pthdivtx syl13anc
        clt wb dff14i nn0fz0 sylib zred elfzolt2 ltned fvco3d neeq12d mpbir2and
        mpd anbi12d df-ne anbi12i ) AKUAEUBSZUCUDZUEZUFZKJCUGZSZTXISZUHZXJXEXIS
        ZUHZUFZXJXKUIUJZXJXMUIUJZUFXHXOKCSZJSZTCSZJSZUHZXSXECSZJSZUHZXHFUKSZGUK
        SZJULZXRYFUEZXTYFUEZXRXTUHZYBAYHXGAJFGUMUDUEYFYGJUNYHPJFGYFYGYFUOZYGUOU
        PYFYGJUQURUSZAXGYIAECFUTSVAZECFVBSVAZXGYIVCRCEFVDZYOXGYIYOXGUFTXEVGUDZY
        FKCYOYQYFCVHZXGCEFYFYLVEZUSXGKYQUEZYOXFYQKXFTXEUCUDYQXEVFTXEVIVJVKZVLVM
        VTURVNZAYJXGAYNYOYJRYPYOYQYFTCYSYOXEVOUEZTYQUEZCEFVPZXEVQZVRVMURUSXHYNX
        GUUDKTUHZYKAYNXGRUSZAXGWAZAUUDXGAUUCUUDAYNYOUUCRYPUUEURZUUFVRUSZXGUUGAX
        GUAKVSVAZUUGKUAXEWBXGUULTKWJVAZUUGXGKWCUEUUMUULWKKUAXEWDZKWEVRXGUUMUUGX
        GUUMUFKXGUUMWAWFVTWGXAVLCEFKTWHWIYFYGJXRXTWLWIXHYHYIYCYFUEZXRYCUHZYEYMU
        UBAUUOXGAYNYOUUORYPYOYQYFXECYSYOUUCXEYQUEZUUEXEWMZWNVMURUSXHYNXGUUQKXEU
        HZUUPUUHUUIAUUQXGAUUCUUQUUJUURWNUSZXGUUSAXGKXEXGKUUNWOKUAXEWPWQVLCEFKXE
        WHWIYFYGJXRYCWLWIXHXLYBXNYEXHXJXSXKYAXHYQYFKJCAYRXGAYNYOYRRYPYSURUSZXGY
        TAUUAVLWRZXHYQYFTJCUVAUUKWRWSXHXJXSXMYDUVBXHYQYFXEJCUVAUUTWRWSXBWTXLXPX
        NXQXJXKXCXJXMXCXDWN $.

      $d E x y $.  $d F y $.  $d N x y $.  $d P y $.  $d ph y $.
      $( Graph isomorphisms between simple pseudographs map paths onto paths.
         (Contributed by AV, 31-Oct-2025.) $)
      upgrimpths $p |- ( ph -> E ( Paths ` H ) ( N o. P ) ) $=
        ( cfv cc0 wcel vy ccom ctrls wbr chash cfzo cres ccnv wfun cpr cima cin
        c1 co c0 wceq w3a cpths pthistrl syl upgrimtrls upgrimpthslem1 cv wn wo
        wral cfz wfn cvtx cwlks cdm cword pthiswlk wlkf 3syl eqid upgrimwlklem4
        wf wlkp ffnd cn0 upgrimwlklem1 wlkcl 0elfz nn0fz0 sylib oveq2d eleqtrrd
        eqeltrd fnimapr syl3anc eleq2d vex elpr bitrdi wa upgrimpthslem2 simpld
        wrex eqeq2 notbid syl5ibrcom simprd impancom nrexdv eqcomd feq2d mpbird
        jaod imp adantr wss fzo0ss1 fzossfz sstri a1i fvelimabd mtbird ralrimiv
        ex sylbid disj sylibr reseq2d cnveqd funeqd preq2 imaeq2d oveq2 ineq12d
        wb eqeq1d 3anbi23d mpbir3and ispth ) ADJCUBZGUCRUDZYPUMDUERZUFUNZUGZUHZ
        UIZYPSYRUJZUKZYPYSUKZULZUOUPZUQZDYPGURRUDAUUHYQYPUMEUERZUFUNZUGZUHZUIZY
        PSUUIUJZUKZYPUUJUKZULZUOUPZABCDEFGHIJKLMNOPAECFURRUDZECFUCRUDQCEFUSUTVA
        ABCDEFGHIJKLMNOPQVBABVCZUUPTZVDZBUUOVFUURAUVBBUUOAUUTUUOTZUUTSYPRZUPZUU
        TUUIYPRZUPZVEZUVBAUVCUUTUVDUVFUJZTUVHAUUOUVIUUTAYPSYRVGUNZVHSUVJTZUUIUV
        JTUUOUVIUPAUVJGVIRZYPABCDEFGHIJKLMNOPAUUSECFVJRUDZEHVKVLTQCEFVMZCEFHKVN
        VOZAUUSUVMSUUIVGUNZFVIRZCVRQUVNCEFUVQUVQVPVSVOVQZVTAYRWATUVKAYRUUIWAABD
        EFGHIJKLMNOPUVOWBZAUUSUVMUUIWATZQUVNCEFWCVOZWIYRWDUTAUUIUVPUVJAUVTUUIUV
        PTUWAUUIWEWFAYRUUISVGUVSWGWHUVJSUUIYPWJWKWLUUTUVDUVFBWMWNWOAUVHUVBAUVHW
        PZUVAUAVCZYPRZUUTUPZUAUUJWSUWBUWEUAUUJUWBUWCUUJTZUWEVDZAUWFUVHUWGAUWFWP
        ZUVEUWGUVGUWHUWGUVEUWDUVDUPZVDZUWHUWJUWDUVFUPZVDZABCDEFGHIJUWCKLMNOPQWQ
        ZWRUVEUWEUWIUUTUVDUWDWTXAXBUWHUWGUVGUWLUWHUWJUWLUWMXCUVGUWEUWKUUTUVFUWD
        WTXAXBXIXDXJXEUWBUAUVPUUJUUTYPAYPUVPVHUVHAUVPUVLYPAUVPUVLYPVRUVJUVLYPVR
        UVRAUVPUVJUVLYPAUUIYRSVGAYRUUIUVSXFWGXGXHVTXKUUJUVPXLUWBUUJSUUIUFUNUVPU
        UIXMSUUIXNXOXPXQXRXTYAXSBUUOUUPYBYCAUUBUUMUUGUURYQAUUAUULAYTUUKAYSUUJYP
        AYRUUIUMUFUVSWGYDYEYFAYRUUIUPZUUGUURYKUVSUWNUUFUUQUOUWNUUDUUOUUEUUPUWNU
        UCUUNYPYRUUISYGYHUWNYSUUJYPYRUUIUMUFYIYHYJYLUTYMYNYPDGYOYC $.
    $}

    ${
      $d E x $.  $d N x $.
      upgrimspths.s $e |- ( ph -> F ( SPaths ` G ) P ) $.
      $( Graph isomorphisms between simple pseudographs map simple paths onto
         simple paths.  (Contributed by AV, 31-Oct-2025.) $)
      upgrimspths $p |- ( ph -> E ( SPaths ` H ) ( N o. P ) ) $=
        ( cfv wbr wfun ccom ctrls ccnv cpths spthispth pthistrl 3syl upgrimtrls
        cspths isspth simprbi cgrim co wcel cvtx wf1o eqid grimf1o dff1o3 funco
        syl wfo syl2anc cnvco funeqi sylibr sylanbrc ) ADJCUAZGUBRSVHUCZTZDVHGU
        IRSABCDEFGHIJKLMNOPAECFUIRSZECFUDRSECFUBRSZQCEFUECEFUFUGUHACUCZJUCZUAZT
        ZVJAVMTZVNTZVPAVKVQQVKVLVQCEFUJUKVAAJFGULUMUNFUORZGUORZJUPZVROJFGVSVTVS
        UQVTUQURWAVSVTJVBVRVSVTJUSUKUGVMVNUTVCVIVOJCVDVEVFVHDGUJVG $.
    $}

    ${
      $d E x $.  $d N x $.
      upgrimcycls.c $e |- ( ph -> F ( Cycles ` G ) P ) $.
      $( Graph isomorphisms between simple pseudographs map cycles onto cycles.
         (Contributed by AV, 31-Oct-2025.) $)
      upgrimcycls $p |- ( ph -> E ( Cycles ` H ) ( N o. P ) ) $=
        ( cfv wbr cc0 ccom cpths chash wceq ccycls cyclispth upgrimpths simprbi
        syl iscycl fveq2d cfz co cvtx cwlks cycliswlk eqid wlkp 3syl wcel wlkcl
        wf cn0 0elfz fvco3d cword wlkf upgrimwlklem1 nn0fz0 sylib eqtrd 3eqtr4d
        cdm sylanbrc ) ADJCUAZGUBRSTVORZDUCRZVORZUDDVOGUERSABCDEFGHIJKLMNOPAECF
        UERSZECFUBRSZQCEFUFUIUGATCRZJREUCRZCRZJRZVPVRAWAWCJAVSWAWCUDZQVSVTWECEF
        UJUHUIUKATWBULUMZFUNRZTJCAVSECFUORSZWFWGCVBQCEFUPZCEFWGWGUQURUSZAWBVCUT
        ZTWFUTAVSWHWKQWICEFVAUSZWBVDUIVEAVRWBVORWDAVQWBVOABDEFGHIJKLMNOPAVSWHEH
        VMVFUTQWICEFHKVGUSVHUKAWFWGWBJCWJAWKWBWFUTWLWBVIVJVEVKVLVODGUJVN $.
    $}
  $}

  $( The relation "is isomorphic to" for graphs.  (Contributed by AV,
     28-Apr-2025.) $)
  brgric $p |- ( R ~=gr S <-> ( R GraphIso S ) =/= (/) ) $=
    ( cgric cgrim cvv cxp df-gric grimfn brwitnlem ) ABCDEEFGHI $.

  $( Prove that two graphs are isomorphic by an explicit isomorphism.
     (Contributed by AV, 28-Apr-2025.) $)
  brgrici $p |- ( F e. ( R GraphIso S ) -> R ~=gr S ) $=
    ( cgrim co wcel c0 wne cgric wbr ne0i brgric sylibr ) CABDEZFNGHABIJNCKABLM
    $.

  $( Reverse closure of the "is isomorphic to" relation for graphs.
     (Contributed by AV, 12-Jun-2025.) $)
  gricrcl $p |- ( G ~=gr S -> ( G e. _V /\ S e. _V ) ) $=
    ( cgric wbr cgrim co c0 wne cvv wcel brgric grimdmrel ovprc necon1ai sylbi
    wa ) BACDBAEFZGHBIJAIJPZBAKRQGBAELMNO $.

  ${
    $d A f g i $.  $d B f g i $.  $d I i $.  $d X f $.  $d Y f $.
    dfgric2.v $e |- V = ( Vtx ` A ) $.
    dfgric2.w $e |- W = ( Vtx ` B ) $.
    dfgric2.i $e |- I = ( iEdg ` A ) $.
    dfgric2.j $e |- J = ( iEdg ` B ) $.
    ${
      $( Alternate, explicit definition of the "is isomorphic to" relation for
         two graphs.  (Contributed by AV, 11-Nov-2022.)  (Revised by AV,
         5-May-2025.) $)
      dfgric2 $p |- ( ( A e. X /\ B e. Y ) -> ( A ~=gr B
          <-> E. f ( f : V -1-1-onto-> W
                     /\ E. g ( g : dom I -1-1-onto-> dom J /\ A. i e. dom I
                               ( f " ( I ` i ) ) = ( J ` ( g ` i ) ) ) ) ) ) $=
        ( cv wcel wex wa cfv cgric wbr cgrim wf1o cdm cima wceq wral wne brgric
        co c0 n0 bitri cvv wb vex w3a isgrim ralbii anbi2i bitrdi mp3an3 exbidv
        eqcom exbii bitrid ) ABUAUBZCPZABUCUKZQZCRZAJQZBKQZSZHIVIUDZFUEZGUEDPZU
        DZVIEPZFTUFZVTVRTGTZUGZEVQUHZSZDRZSZCRVHVJULUIVLABUJCVJUMUNVOVKWGCVMVNV
        IUOQZVKWGUPCUQVMVNWHURVKVPVSWBWAUGZEVQUHZSZDRZSWGGEDFVIABHIJKUOLMNOUSWL
        WFVPWKWEDWJWDVSWIWCEVQWBWAVEUTVAVFVAVBVCVDVG $.
    $}

    $( Implications of two graphs being isomorphic.  (Contributed by AV,
       11-Nov-2022.)  (Revised by AV, 5-May-2025.)  (Proof shortened by AV,
       12-Jun-2025.) $)
    gricbri $p |- ( A ~=gr B -> E. f ( f : V -1-1-onto-> W
      /\ E. g ( g : dom I -1-1-onto-> dom J
                /\ A. i e. dom I ( f " ( I ` i ) ) = ( J ` ( g ` i ) ) ) ) ) $=
      ( cv wf1o cdm cfv wa wex cvv cgric cima wceq wral wcel wb gricrcl dfgric2
      wbr syl ibi ) ABUAUIZHICNZOFPZGPDNZOUMENZFQUBUPUOQGQUCEUNUDRDSRCSZULATUEB
      TUERULUQUFBAUGABCDEFGHITTJKLMUHUJUK $.
  $}

  ${
    $d A e f g h i j $.  $d B e f g h i j $.  $d E e g h i $.  $d K g h i j $.
    $d V e g h i j $.  $d W e g h i j $.
    gricushgr.v $e |- V = ( Vtx ` A ) $.
    gricushgr.w $e |- W = ( Vtx ` B ) $.
    gricushgr.e $e |- E = ( Edg ` A ) $.
    gricushgr.k $e |- K = ( Edg ` B ) $.
    $( The "is isomorphic to" relation for two simple hypergraphs.
       (Contributed by AV, 28-Nov-2022.) $)
    gricushgr $p |- ( ( A e. USHGraph /\ B e. USHGraph ) -> ( A ~=gr B
                   <-> E. f ( f : V -1-1-onto-> W /\ E. g ( g : E -1-1-onto-> K
                                  /\ A. e e. E ( f " e ) = ( g ` e ) ) ) ) ) $=
      ( wcel wa wf1o cfv wceq ccom syl vh vi vj cushgr cgric wbr ciedg cdm cima
      cv wral wex eqid dfgric2 ccnv cvv fvex vex cnvex coex a1i crn cpw c0 cdif
      csn wf1 ushgrf f1f1orn wb cedg edgval eqtri f1oeq3 sylibr ad3antlr simprl
      ax-mp f1ocnv ad3antrrr f1oco syl2anc eleq2i wrex wfn f1fn fvelrnb imaeq2d
      fveq2 2fveq3 eqeq12d rspccv ad2antll imp coass eqcomi fveq1i dff1o4 sylib
      wi simprd ad4antr wf f1of ffvelcdmda fvco2 f1ocnvfv1 sylan f1ofn ad2antrl
      fveq2d 3eqtrd eqtr2id ad2antrr imaeq2 eqcoms simpr sylan9eqr adantl mpdan
      3eqtr4d rexlimdva jca f1oeq1 eqeq2d ralbidv anbi12d spcedv exlimdv biimpi
      ex fveq1 wfun ffund adantr anim12ci fnfco ad5antlr fco anim1i f1oeq23 cid
      sylbid biimtrid ralrimiv fvelrn raleqi rspccva cres feq3 simplr funcocnv2
      mp2an eqcomd coeq1d fveq1d eqtrdi feq23i syl2anr ffvelcdm fvresi 3eqtr3rd
      fvco3 eqtrd ralrimiva impbid pm5.32da exbidv bitrd ) AUDNZBUDNZOZABUEUFHI
      DUJZPZAUGQZUHZBUGQZUHZUAUJZPZUVMUBUJZUVOQZUIZUWAUVSQZUVQQZRZUBUVPUKZOZUAU
      LZOZDULUVNFGEUJZPZUVMCUJZUIZUWMUWKQZRZCFUKZOZEULZOZDULABDUAUBUVOUVQHIUDUD
      JKUVOUMZUVQUMZUNUVLUWJUWTDUVLUVNUWIUWSUVLUVNOZUWIUWSUXCUWHUWSUAUXCUWHUWSU
      XCUWHOZUWRFGUVQUVSUVOUOZSZSZPZUWNUWMUXGQZRZCFUKZOEUPUXGUXGUPNUXDUVQUXFBUG
      UQZUVSUXEUAURUVOAUGUQZUSUTUTVAUXDUXHUXKUXDUVRGUVQPZFUVRUXFPZUXHUVKUXNUVJU
      VNUWHUVKUVRUVQVBZUVQPZUXNUVKUVRIVCVDVFZVEZUVQVGUXQUVQBIKUXBVHUVRUXSUVQVIT
      ZGUXPRZUXNUXQVJGBVKQUXPMBVLVMZGUXPUVRUVQVNVRVOZVPUXDUVTFUVPUXEPZUXOUXCUVT
      UWGVQUVJUYDUVKUVNUWHUVJUVPFUVOPZUYDUVJUVPUVOVBZUVOPZUYEUVJUVPHVCUXRVEZUVO
      VGZUYGUVOAHJUXAVHZUVPUYHUVOVITZFUYFRZUYEUYGVJFAVKQUYFLAVLVMZFUYFUVPUVOVNV
      RVOZUVPFUVOVSTVTFUVPUVRUVSUXEWAWBFUVRGUVQUXFWAWBUXDUXJCFUWMFNUWMUYFNZUXDU
      XJFUYFUWMUYMWCUXDUYOUCUJZUVOQZUWMRZUCUVPWDZUXJUVJUYOUYSVJZUVKUVNUWHUVJUVO
      UVPWEZUYTUVJUYIVUAUYJUVPUYHUVOWFTUCUVPUWMUVOWGTVTUXDUYRUXJUCUVPUXDUYPUVPN
      ZOZUVMUYQUIZUYPUVSQUVQQZRZUYRUXJWTUXDVUBVUFUWGVUBVUFWTUXCUVTUWFVUFUBUYPUV
      PUWAUYPRZUWCVUDUWEVUEVUGUWBUYQUVMUWAUYPUVOWIWHUWAUYPUVQUVSWJWKWLWMWNVUCVU
      FOZUYRUXJVUHUYROVUEUYQUXGQZUWNUXIVUCVUEVUIRVUFUYRVUCVUIUYQUVQUVSSZUXESZQZ
      VUEUYQUXGVUKVUKUXGUVQUVSUXEWOWPWQVUCVULUYQUXEQZVUJQZUYPVUJQZVUEVUCUXEUYFW
      EZUYQUYFNVULVUNRUVJVUPUVKUVNUWHVUBUVJVUAVUPUVJUYGVUAVUPOUYKUVPUYFUVOWRWSX
      AXBUXDUVPUYFUYPUVOUVJUVPUYFUVOXCZUVKUVNUWHUVJUYGVUQUYKUVPUYFUVOXDTZVTXEUY
      FVUJUXEUYQXFWBVUCVUMUYPVUJUXDUYEVUBVUMUYPRUVJUYEUVKUVNUWHUYNVTUVPFUYPUVOX
      GXHXKUXDUVSUVPWEZVUBVUOVUERUVTVUSUXCUWGUVPUVRUVSXIXJUVPUVQUVSUYPXFXHXLXMX
      NUYRVUHUWNVUDVUEUWNVUDRUWMUYQUWMUYQUVMXOXPVUCVUFXQXRUYRUXIVUIRZVUHVUTUWMU
      YQUWMUYQUXGWIXPXSYAYKXTYBUUCUUDUUEYCUWKUXGRZUWLUXHUWQUXKFGUWKUXGYDVVAUWPU
      XJCFVVAUWOUXIUWNUWMUWKUXGYLYEYFYGYHYKYIUXCUWRUWIEUXCUWRUWIUXCUWROZUWHUVPU
      VRUVQUOZUWKUVOSZSZPZUWCUWAVVEQZUVQQZRZUBUVPUKZOUAUPVVEVVEUPNVVBVVCVVDUVQU
      XLUSUWKUVOEURUXMUTUTVAVVBVVFVVJVVBUXPUVRVVCPZUVPUXPVVDPZVVFVVBUXQVVKUVKUX
      QUVJUVNUWRUXTVPUVRUXPUVQVSTVVBUYFUXPUWKPZUYGVVLUWLVVMUXCUWQUWLVVMUYLUYAUW
      LVVMVJUYMUYBFUYFGUXPUWKUUAUUMYJXJUVJUYGUVKUVNUWRUYKVTUVPUYFUXPUWKUVOWAWBU
      VPUXPUVRVVCVVDWAWBVVBVVIUBUVPVVBUWAUVPNZOZUWBUYFNZVVIVVBUVOYMZVVNVVPUXCVV
      QUWRUXCUVPUYFUVOUVJVUQUVKUVNVURXNYNYOUWAUVOUUFXHVVOVVPOZUWCUWBUWKQZUWAUVQ
      VVESZQZVVHVVOUWPCUYFUKZVVPUWCVVSRZVVBVWBVVNUWQVWBUXCUWLUWQVWBUWPCFUYFUYMU
      UGYJWMYOUWPVWCCUWBUYFUWMUWBRUWNUWCUWOVVSUWMUWBUVMXOUWMUWBUWKWIWKUUHXHVVRU
      WAUUBUXPUUIZVVDSZQZUWAVVDQZVWDQZVWAVVSVVRVVDUVPWEZVVNVWFVWHRVVRUWKFWEZUVP
      FUVOXCZOZVWIVVBVWLVVNVVPUXCVWKUWRVWJUVJVWKUVKUVNUVJVUQVWKVURUYLVWKVUQVJUY
      MFUYFUVPUVOUUJVRVOXNZUWLVWJUWQFGUWKXIYOYPXNFUVPUWKUVOYQTVVBVVNVVPUUKZUVPV
      WDVVDUWAXFWBVVRVWFUWAUVQVVCSZVVDSZQVWAVVRUWAVWEVWPVVRVWDVWOVVDUVKVWDVWORU
      VJUVNUWRVVNVVPUVKVWOVWDUVKUVQYMVWOVWDRUVKUVRGUVQUVKUXNUVRGUVQXCUYCUVRGUVQ
      XDTYNUVQUULTUUNYRUUOUUPUWAVWPVVTUVQVVCVVDWOWQUUQVVRVWHVWGVVSVVRVWGUXPNZVW
      HVWGRVVRUVPUXPVVDXCZVVNOZVWQVVOVWSVVPVVBVWRVVNUWRFUXPUWKXCZVWKVWRUXCUWLVW
      TUWQUWLFGUWKXCZVWTFGUWKXDZFGFUXPUWKFUMUYBUURWSYOUVJVWKUVKUVNUVJUYEVWKUYNU
      VPFUVOXDTZXNUVPFUXPUWKUVOYSUUSYTYOUVPUXPUWAVVDUUTTUXPVWGUVATVVRVWKVVNOZVW
      GVVSRVVOVXDVVPVVBVWKVVNUVJVWKUVKUVNUWRVXCVTYTYOUVPFUWAUWKUVOUVCTUVDUVBVVR
      VVEUVPWEZVVNVWAVVHRVVRVVCGWEZUVPGVVDXCZVXEUVKVXFUVJUVNUWRVVNVVPUVKUVQUVRW
      EZVXFUVKUXNVXHVXFOUYCUVRGUVQWRWSXAYRVVRVXAVWKOZVXGVVBVXIVVNVVPUXCVWKUWRVX
      AVWMUWLVXAUWQVXBYOYPXNUVPFGUWKUVOYSTGUVPVVCVVDYQWBVWNUVPUVQVVEUWAXFWBXLXT
      UVEYCUVSVVERZUVTVVFUWGVVJUVPUVRUVSVVEYDVXJUWFVVIUBUVPVXJUWEVVHUWCVXJUWDVV
      GUVQUWAUVSVVEYLXKYEYFYGYHYKYIUVFUVGUVHUVI $.

    $d A a b $.  $d B a b $.  $d E a b f $.  $d K a b $.  $d V a b $.
    $d W a b $.
    $( The "is isomorphic to" relation for two simple pseudographs.  This
       corresponds to the definition in [Bollobas] p. 3.  (Contributed by AV,
       1-Dec-2022.)  (Proof shortened by AV, 5-May-2025.) $)
    gricuspgr $p |- ( ( A e. USPGraph /\ B e. USPGraph ) -> ( A ~=gr B
                      <-> E. f ( f : V -1-1-onto-> W /\ A. a e. V A. b e. V
                 ( { a , b } e. E <-> { ( f ` a ) , ( f ` b ) } e. K ) ) ) ) $=
      ( cuspgr wcel wa cv wex cpr cfv cgric wbr cgrim co wf1o wb wral c0 brgric
      wne n0 bitri a1i isuspgrim exbidv bitrd ) ANOBNOPZABUAUBZCQZABUCUDZOZCRZF
      GUSUEHQZIQZSDOVCUSTVDUSTSEOUFIFUGHFUGPZCRURVBUFUQURUTUHUJVBABUICUTUKULUMU
      QVAVECHIEDUSABFGJKLMUNUOUP $.
  $}

  $( The "is isomorphic to" relation for graphs is a relation.  (Contributed by
     AV, 11-Nov-2022.)  (Revised by AV, 5-May-2025.) $)
  gricrel $p |- Rel ~=gr $=
    ( cgric cvv cxp wss wrel cgrim ccnv cdif cima df-gric cnvimass grimfn fndmi
    c1o cdm sseqtri eqsstri relxp relss mp2 ) ABBCZDUAEAEAFGBNHZIZUAJUCFOUAFUBK
    UAFLMPQBBRAUAST $.

  $( Graph isomorphism is reflexive for hypergraphs.  (Contributed by AV,
     11-Nov-2022.)  (Revised by AV, 29-Apr-2025.) $)
  gricref $p |- ( G e. UHGraph -> G ~=gr G ) $=
    ( cuhgr wcel cid cvtx cfv cres cgrim co cgric wbr grimid brgrici syl ) ABCD
    AEFGZAAHICAAJKALAAOMN $.

  ${
    $d G f $.  $d S f $.
    $( Graph isomorphism is symmetric for hypergraphs.  (Contributed by AV,
       11-Nov-2022.)  (Revised by AV, 3-May-2025.) $)
    gricsym $p |- ( G e. UHGraph -> ( G ~=gr S -> S ~=gr G ) ) $=
      ( vf cgric wbr cv cgrim co wcel wex cuhgr c0 brgric n0 bitri ccnv grimcnv
      wne brgrici syl6 exlimdv biimtrid ) BADEZCFZBAGHZIZCJZBKIZABDEZUCUELRUGBA
      MCUENOUHUFUICUHUFUDPZABGHIUIBAUDQABUJSTUAUB $.
  $}

  $( Graph isomorphism is symmetric in both directions for hypergraphs.
     (Contributed by AV, 11-Nov-2022.)  (Proof shortened by AV, 3-May-2025.) $)
  gricsymb $p |- ( ( A e. UHGraph /\ B e. UHGraph )
                  -> ( A ~=gr B <-> B ~=gr A ) ) $=
    ( cuhgr wcel cgric wbr gricsym anbiim ) ACDBCDABEFBAEFBAGABGH $.

  ${
    $d R f g $.  $d S f g $.  $d T f g $.
    $( Graph isomorphism is transitive.  (Contributed by AV, 5-Dec-2022.)
       (Revised by AV, 3-May-2025.) $)
    grictr $p |- ( ( R ~=gr S /\ S ~=gr T ) -> R ~=gr T ) $=
      ( vg vf cgric wbr cgrim co c0 wne brgric cv wcel n0 exdistrv ccom syl2anb
      wex wa grimco ancoms brgrici syl exlimivv sylbir ) ABFGABHIZJKZBCHIZJKZAC
      FGZBCFGABLBCLUHDMZUGNZDSZEMZUINZESZUKUJDUGOEUIOUNUQTUMUPTZESDSUKUMUPDEPUR
      UKDEURUOULQZACHINZUKUPUMUTABCUOULUAUBACUSUCUDUEUFRR $.
  $}

  ${
    $d g h k $.
    $( Isomorphism is an equivalence relation on hypergraphs.  (Contributed by
       AV, 3-May-2025.)  (Proof shortened by AV, 11-Jul-2025.) $)
    gricer $p |- ( ~=gr i^i ( UHGraph X. UHGraph ) ) Er UHGraph $=
      ( vg vh vk cgric cuhgr cv gricref gricsym wbr wa wcel grictr a1i brinxper
      wi ) ABCDEAFZGBFZPHPQDIQCFZDIJPRDIOPEKPQRLMN $.
  $}

  ${
    $d B f $.  $d C f $.  $d R f $.  $d S f $.
    gricen.b $e |- B = ( Vtx ` R ) $.
    gricen.c $e |- C = ( Vtx ` S ) $.
    $( Isomorphic graphs have equinumerous sets of vertices.  (Contributed by
       AV, 3-May-2025.) $)
    gricen $p |- ( R ~=gr S -> B ~~ C ) $=
      ( vf cgric wbr cgrim co c0 wne cen brgric cv wcel wex n0 sylbi wf1o fvexi
      grimf1o cvtx f1oen syl exlimiv ) CDHICDJKZLMZABNIZCDOUIGPZUHQZGRUJGUHSULU
      JGULABUKUAUJUKCDABEFUCABUKACUDEUBUEUFUGTT $.
  $}

  ${
    opstrgric.g $e |- G = <. V , E >. $.
    opstrgric.h $e |- H = { <. ( Base ` ndx ) , V >. ,
                               <. ( .ef ` ndx ) , E >. } $.
    $( A graph represented as an extensible structure with vertices as base set
       and indexed edges is isomorphic to a hypergraph represented as ordered
       pair with the same vertices and edges.  (Contributed by AV,
       11-Nov-2022.)  (Revised by AV, 4-May-2025.) $)
    opstrgric $p |- ( ( G e. UHGraph /\ V e. X /\ E e. Y ) -> G ~=gr H ) $=
      ( wcel cvv cvtx cfv wceq ciedg cnx cop a1i 3adant1 fveq2i wa w3a wbr prex
      cuhgr cgric simp1 cbs cedgf eqeltri opvtxfv struct2grvtx 3eqtr4d opiedgfv
      cpr struct2griedg cid cres cgrim simpl adantr adantl grimidvtxedg brgrici
      co simpr syl syl22anc ) BUDIZDEIZAFIZUAZVHCJIZBKLZCKLZMZBNLZCNLZMZBCUEUBZ
      VHVIVJUFVLVKCOUGLDPZOUHLAPZUNJHVTWAUCUIQVKDAPZKLZDVMVNVIVJWCDMVHADEFUJRVM
      WCMVKBWBKGSQVIVJVNDMVHACDEFHUKRULVKWBNLZAVPVQVIVJWDAMVHADEFUMRVPWDMVKBWBN
      GSQVIVJVQAMVHACDEFHUORULVHVLTZVOVRTZTZUPVMUQZBCURVDIVSWGBCJWEVHWFVHVLUSUT
      WEVLWFVHVLVEUTWFVOWEVOVRUSVAWFVRWEVOVRVEVAVBBCWHVCVFVG $.
  $}

  ${
    $d G f g i $.  $d H f g i $.  $d V f g i $.
    ushggricedg.v $e |- V = ( Vtx ` G ) $.
    ushggricedg.e $e |- E = ( Edg ` G ) $.
    ushggricedg.s $e |- H = <. V , ( _I |` E ) >. $.
    $( A simple hypergraph (with arbitrarily indexed edges) is isomorphic to a
       graph with the same vertices and the same edges, indexed by the edges
       themselves.  (Contributed by AV, 11-Nov-2022.) $)
    ushggricedg $p |- ( G e. USHGraph -> G ~=gr H ) $=
      ( vf vg vi wcel cvtx cfv wf1o ciedg wceq wa cvv a1i syl cushgr wbr cv cdm
      cgric cima wral wex cid cres fvexi resiexd f1oi fveq2i cedg resiexg ax-mp
      cop pm3.2i opvtxfv mp1i eqtrid f1oeq3d mpbird fvexd crn cpw csn cdif eqid
      c0 ushgrf f1f1orn opiedgfv sylancr dmeqd dmresi edgval eqtrdi eqtrd cuhgr
      wf1 wss ushgruhgr uhgrss sylan resiima wfun wf f1f ffund fvelrn eleqtrrdi
      eqtri fvresi eqtr2id fveq1d 3eqtr2d ralrimiva f1oeq1 fveq1 fveq2d ralbidv
      eqeq2d anbi12d spcedv imaeq1 eqeq1d anbi2d exbidv wb opex eqeltri dfgric2
      jca mpan2 ) BUAKZBCUEUBZDCLMZHUCZNZBOMZUDZCOMZUDZIUCZNZXTJUCZYBMZUFZYHYFM
      ZYDMZPZJYCUGZQZIUHZQZHUHZXQYQDXSUIDUJZNZYGYSYIUFZYLPZJYCUGZQZIUHZQHRYSXQD
      RDRKZXQDBLEUKZSULXQYTUUEXQYTDDYSNZUUHXQDUMSXQXSDDYSXQXSDUIAUJZURZLMZDCUUJ
      LGUNUUFUUIRKZQUUKDPXQUUFUULUUGARKZUULABUOFUKZARUPUQUSUUIDRRUTVAVBVCVDXQUU
      DYCYEYBNZUUAYIYDMZPZJYCUGZQIRYBXQBOVEXQUUOUURXQUUOYCYBVFZYBNZXQYCDVGVKVHV
      IZYBWBZUUTYBBDEYBVJZVLZYCUVAYBVMTXQYEUUSYCYBXQYEUUIUDZUUSXQYDUUIXQYDUUJOM
      ZUUICUUJOGUNZXQUUFUULUVFUUIPZUUGXQARUUMXQUUNSULUUIDRRVNZVOVBVPXQUVEAUUSAV
      QXQABUOMZUUSAUVJPXQFSBVRZVSVBVTVCVDXQUUQJYCXQYHYCKZQZUUAYIYIUUIMZUUPUVMYI
      DWCZUUAYIPXQBWAKUVLUVOBWDYBYHBDEUVCWEWFDYIWGTUVMYIAKUVNYIPUVMYIUUSAXQYBWH
      UVLYIUUSKXQYCUVAYBXQUVBYCUVAYBWIUVDYCUVAYBWJTWKYHYBWLWFAUVJUUSFUVKWNWMAYI
      WOTUVMYIUUIYDUVMYDUVFUUIUVGUVMUUFUULUVHUUGUVMARUUMUVMUUNSULUVIVOWPWQWRWSX
      OYFYBPZYGUUOUUCUURYCYEYFYBWTUVPUUBUUQJYCUVPYLUUPUUAUVPYKYIYDYHYFYBXAXBXDX
      CXEXFXOXTYSPZYAYTYPUUEDXSXTYSWTUVQYOUUDIUVQYNUUCYGUVQYMUUBJYCUVQYJUUAYLXT
      YSYIXGXHXCXIXJXEXFXQCRKXRYRXKCUUJRGDUUIXLXMBCHIJYBYDDXSUAREXSVJUVCYDVJXNX
      PVD $.
  $}

  ${
    $d G f g i j p q $.  $d G f g i j q x $.  $d H f g i j p q $.  $d H x $.
    $d N f g i j p q $.
    $( Two simple pseudographs are not isomorphic if one has a cycle and the
       other has no cycle of the same length.  (Contributed by AV,
       6-Nov-2025.) $)
    cycldlenngric $p |- ( ( G e. USPGraph /\ H e. USPGraph )
                     -> ( ( E. p E. f ( f ( Cycles ` G ) p /\ ( # ` f ) = N )
                      /\ -. E. p E. f ( f ( Cycles ` H ) p /\ ( # ` f ) = N ) )
                        -> -. G ~=gr H ) ) $=
      ( vg vq vi vx vj wcel wa cv cfv wbr chash wceq wex adantl wb cuspgr cgric
      ccycls wn wi cgrim co wne brgric wrex n0rex cdm ciedg cima ccnv cmpt ccom
      cwlks eqid simprll simprlr simpl 2fveq3 imaeq2d fveq2d cycliswlk ad2antrl
      c0 cbvmptv upgrimwlklen simprrl upgrimcycls simp3 simp2r simprrr 3ad2ant1
      w3a eqtrd coex dmex breq12 ancoms fveqeq2 anbi12d spc2ev syl2anc mpd3an23
      vex mptex rexlimivw syl sylbi expdcom exlimdvv cbvex2vw imbitrrdi expimpd
      ex imp con3d ) BUAKZCUAKZLZAMZEMZBUCNOZXDPNZDQZLZARERZXDXECUCNZOZXHLZARER
      ZUDBCUBOZUDXCXJLZXOXNXPXOFMZGMZXKOZXQPNDQZLZFRGRZXNXCXJXOYBUEZXCXIYCEAXOX
      CXIYBXOBCUFUGZVHUHZXCXILZYBUEZBCUIYEHMZYDKZHYDUJYGHYDUKYIYGHYDYIYFYBYIYFL
      ZIXDULZYHIMZXDNBUMNZNZUNZCUMNZUOZNZUPZYHXEUQZCURNOZYSPNZXGQZLZYSYTXKOZYBY
      JJXEYSXDBCYMYPYHYMUSZYPUSZYIXAXBXIUTZYIXAXBXIVAZYIYFVBZIJYKYRYHJMZXDNYMNZ
      UNZYQNYLUUKQZYOUUMYQUUNYNUULYHYLUUKYMXDVCVDVEVIZYFXDXEBURNOZYIXFUUPXCXHXE
      XDBVFVGSVJYJJXEYSXDBCYMYPYHUUFUUGUUHUUIUUJUUOYIXCXFXHVKVLYJUUDUUEVQZUUEUU
      BDQZYBYJUUDUUEVMUUQUUBXGDYJUUAUUCUUEVNYJUUDXHUUEYIXCXFXHVOVPVRYAUUEUURLGF
      YTYSYHXEHWHEWHVSIYKYRXDAWHVTWIXRYTQZXQYSQZLXSUUEXTUURUUTUUSXSUUETXQYSXRYT
      XKWAWBUUTXTUURTUUSXQYSDPWCSWDWEWFWGWRWJWKWLWMWNWSXMYAEAGFXEXRQZXDXQQZLXLX
      SXHXTUVBUVAXLXSTXDXQXEXRXKWAWBUVBXHXTTUVAXDXQDPWCSWDWOWPWTWQ $.
  $}

  ${
    $d G f g i $.  $d G x $.  $d H f g i $.  $d H x $.  $d I x $.  $d J x $.
    $d M f g i $.  $d M x $.  $d N f g i $.  $d N x $.  $d T f g i $.
    $d U f g i $.  $d V f g i $.  $d V x $.  $d W f g i $.  $d W x $.
    $d K i $.  $d L i $.
    isubgrgrim.v $e |- V = ( Vtx ` G ) $.
    isubgrgrim.w $e |- W = ( Vtx ` H ) $.
    isubgrgrim.i $e |- I = ( iEdg ` G ) $.
    isubgrgrim.j $e |- J = ( iEdg ` H ) $.
    isubgrgrim.k $e |- K = { x e. dom I | ( I ` x ) C_ N } $.
    isubgrgrim.l $e |- L = { x e. dom J | ( J ` x ) C_ M } $.
    $( Isomorphic subgraphs induced by subsets of vertices of two graphs.
       (Contributed by AV, 29-May-2025.) $)
    isubgrgrim $p |- ( ( ( G e. U /\ H e. T ) /\ ( N C_ V /\ M C_ W ) )
                       -> ( ( G ISubGr N ) ~=gr ( H ISubGr M )
         <-> E. f ( f : N -1-1-onto-> M /\ E. g ( g : K -1-1-onto-> L
                  /\ A. i e. K ( f " ( I ` i ) ) = ( J ` ( g ` i ) ) ) ) ) ) $=
      ( wcel wa wss cisubgr co cgric wbr cvtx cfv wf1o ciedg cdm cima wceq wral
      cv wex wb ovex pm3.2i eqid dfgric2 mp1i eqidd isubgrvtx ad2ant2r ad2ant2l
      cvv f1oeq123d crab cres isubgriedg dmeqd ssrab2 a1i ssdmres eqcomi 3eqtrd
      sylib anbi1d reseq2d eqtrd fveq1d imaeq2d reseq2i eqtrdi raleqbidv adantr
      eqeq12d fvres adantl adantlr wf ffvelcdmda fvresd ralbidva bitrd pm5.32da
      f1of exbidv anbi12d ) GCUCZHBUCZUDNOUEZMPUEZUDUDZGNUFUGZHMUFUGZUHUIZXIUJU
      KZXJUJUKZDURZULZXIUMUKZUNZXJUMUKZUNZEURZULZXNFURZXPUKZUOZYBXTUKZXRUKZUPZF
      XQUQZUDZEUSZUDZDUSZNMXNULZKLXTULZXNYBIUKZUOZYEJUKZUPZFKUQZUDZEUSZUDZDUSXI
      VJUCZXJVJUCZUDXKYLUTXHUUCUUDGNUFVAHMUFVAVBXIXJDEFXPXRXLXMVJVJXLVCXMVCXPVC
      XRVCVDVEXHYKUUBDXHXOYMYJUUAXHXLNXMMXNXNXHXNVFXDXFXLNUPXEXGNGOCQVGVHXEXGXM
      MUPXDXFMHPBRVGVIVKXHYIYTEXHYIYNYHUDYTXHYAYNYHXHXQKXSLXTXTXHXTVFXHXQIAURZI
      UKNUEZAIUNZVLZVMZUNZUUHKXHXPUUIXDXFXPUUIUPXEXGANIGOCQSVNVHZVOXHUUHUUGUEZU
      UJUUHUPUULXHUUFAUUGVPVQUUHIVRWAUUHKUPXHKUUHUAVSVQZVTZXHXSJUUEJUKMUEZAJUNZ
      VLZVMZUNZUUQLXHXRUURXEXGXRUURUPXDXFAMJHPBRTVNVIZVOXHUUQUUPUEZUUSUUQUPUVAX
      HUUOAUUPVPVQUUQJVRWAUUQLUPXHLUUQUBVSZVQVTVKWBXHYNYHYSXHYNUDZYHXNYBIKVMZUK
      ZUOZYEJLVMZUKZUPZFKUQZYSXHYHUVJUTYNXHYGUVIFXQKUUNXHYDUVFYFUVHXHYCUVEXNXHY
      BXPUVDXHXPUUIUVDUUKXHUUHKIUUMWCWDWEWFXHYEXRUVGXHXRUURUVGUUTUUQLJUVBWGWHWE
      WKWIWJUVCUVIYRFKUVCYBKUCZUDZUVFYPUVHYQXHUVKUVFYPUPYNXHUVKUDUVEYOXNUVKUVEY
      OUPXHYBKIWLWMWFWNUVLYELJUVCKLYBXTYNKLXTWOXHKLXTXAWMWPWQWKWRWSWTWSXBXCXBWS
      $.
  $}

  ${
    $d A i k $.  $d B k $.  $d F i k $.  $d G i k $.  $d H i k $.  $d I i k $.
    $d J i k $.  $d N k $.  $d V k $.  $d W k $.
    $( Lemma for ~ uhgrimisgrgric .  (Contributed by AV, 31-May-2025.) $)
    uhgrimisgrgriclem $p |- ( ( ( F : V -1-1-onto-> W /\ G : A --> ~P V )
                           /\ ( N C_ V /\ I : A -1-1-onto-> B )
                           /\ A. i e. A ( H ` ( I ` i ) ) = ( F " ( G ` i ) ) )
                  -> ( ( J e. B /\ ( H ` J ) C_ ( F " N ) )
                       <-> E. k e. A ( ( G ` k ) C_ N /\ ( I ` k ) = J ) ) ) $=
      ( wa wss cfv cima wceq wi adantl ex wf1o cpw wf wral wcel wrex ccnv fveq2
      cv w3a sseq1d fveqeq2 anbi12d simpr 3ad2ant2 simpl f1ocnvdm syl2an 2fveq3
      imaeq2d eqeq12d rspcv f1ocnvfv2 syl2anr fveqeq2d sseq1 wf1 f1of1 3ad2ant1
      wb adantr simp1lr simp1r ffvelcdmd elpwid 3ad2ant3 f1imass syl12anc com24
      biimpd 3exp sylbid com25 imp42 com23 syld 3imp1 mpd rspcedvdw simp2 simp3
      jca f1of imass2 eqsstrd 3impia 3imp eleq1 mpbi2and rexlimdv3a impbid ) KL
      EUAZAKUBZFUCZMZJKNZABHUAZMZCUIZHOGOZEXIFOZPZQZCAUDZUJZIBUEZIGOZEJPZNZMZDU
      IZFOZJNZYAHOZIQZMZDAUFZXOXTYGXOXTMZYFIHUGOZFOZJNZYIHOZIQZMDYIAYAYIQZYCYKY
      EYMYNYBYJJYAYIFUHUKYAYIIHULUMXOXGXPYIAUEZXTXHXEXGXNXFXGUNZUOZXPXSUPZABIHU
      QURZYHYKYMYHYOYKYSXEXHXNXTYOYKRXEYOXNXTXHYKXEYOXNXTXHYKRZRZRXEYOMZXNYLGOZ
      EYJPZQZUUAYOXNUUERXEXMUUECYIAXIYIQZXJUUCXLUUDXIYIGHUSUUFXKYJEXIYIFUHUTVAV
      BSUUBXTUUEYTUUBXTUUEYTRUUBXTMZXHUUEYKUUGXHUUEYKRUUGXHMZUUEXQUUDQZYKUUHYLI
      UUDGXHXGXPYMUUGYPXTXPUUBYRSABIHVCZVDVEUUBXPXSXHUUIYKRUUBUUIXSXHXPYKUUBUUI
      XSXHXPYKRRZRUUBUUIMXSUUDXRNZUUKUUIXSUULVJUUBXQUUDXRVFSUUBUULUUKRUUIUUBXPX
      HUULYKUUBXPXHUULYKRUUBXPXHUJZUULYKUUMKLEVGZYJKNXFUULYKVJUUBXPUUNXHXEUUNYO
      XBUUNXDKLEVHVKVKVIUUMYJKUUMAXCYIFXBXDYOXPXHVLXEYOXPXHVMVNVOXHUUBXFXPXFXGU
      PVPKLYJJEVQVRVTWAVSVKWBTWCWDWBTWETWEWFTWCWGWHXOXGXPYMXTYQYRUUJURWLWITXOYF
      XTDAXOYAAUEZYFUJZYDBUEZYDGOZXRNZXTUUPABYAHXOUUOABHUCZYFXHXEUUTXNXGUUTXFAB
      HWMSUOVIXOUUOYFWJVNXOUUOYFUUSXEXHXNUUOYFUUSRZRXEXHMZUUOXNUVAUVBUUOXNUVARU
      VBUUOMZXNUUREYBPZQZUVAUUOXNUVERUVBXMUVECYAAXIYAQZXJUURXLUVDXIYAGHUSUVFXKY
      BEXIYAFUHUTVAVBSUVCYFUVEUUSUVCYFUVEUUSUVCYFUVEUJUURUVDXRUVCYFUVEWKYFUVCUV
      DXRNZUVEYCUVGYEYBJEWNVKUOWOWAWEWFTWEWPWQYFXOUUQUUSMXTVJZUUOYEUVHYCYEUUQXP
      UUSXSYDIBWRYEUURXQXRYDIGUHUKUMSVPWSWTXA $.
  $}

  ${
    $d F f h i x $.  $d F g h i $.  $d F g i j k $.  $d G f h i x $.
    $d G g h i $.  $d G g i j k $.  $d H f h i x $.  $d H g h i $.
    $d H g i j k $.  $d N f h i x $.  $d N g h i $.  $d N g i j k $.
    $d V f h i x $.  $d V g h i $.  $d V g i j k $.  $d j k x $.
    uhgrimisgrgric.v $e |- V = ( Vtx ` G ) $.
    $( For isomorphic hypergraphs, the induced subgraph of a subset of vertices
       of one graph is isomorphic to the subgraph induced by the image of the
       subset.  (Contributed by AV, 31-May-2025.) $)
    uhgrimisgrgric $p |- ( ( G e. UHGraph /\ F e. ( G GraphIso H ) /\ N C_ V )
                           -> ( G ISubGr N ) ~=gr ( H ISubGr ( F " N ) ) ) $=
      ( vg vi vx vh vk wcel wss cvv wa wi cfv wf1o cv wceq vf vj cuhgr cgrim co
      w3a cisubgr cima cgric wbr grimdmrel ovrcl 3ad2ant2 cvtx cdm wex grimprop
      ciedg wral eqid crab cres wfun f1ofun 3ad2ant1 fvexi resfunexg syl2an wf1
      ssex f1of1 f1ores sylan simpr vex a1i adantr ad2antrr ssrab2 sylancl wrex
      resex cpw wf wb c0 csn cdif uhgrf id difssd fssd syl anim2i simp2l anim1i
      3adant2 ancomd simpl2r uhgrimisgrgriclem syl3anc fveq2 sseq1d bitr4di wfn
      rexrab elrab f1ofn jctir fvelimab 3bitr4d eqrdv f1oeq3d mpbird ax-mp elex
      ssralv 3anim3i fvres ad2antlr fveq2d weq simprbi resima2 3eqtr4rd sylanl1
      ex ralimdva syl5 expimpd 3exp1 com25 3imp1 imp jca f1oeq1 ralbidv anbi12d
      fveq1 spcedv eqeq2d mpdan imaeq1 eqeq1d anbi2d exbidv simpl3 f1of fimassd
      a1d isubgrgrim syl12anc exlimdv expd com12 com34 3imp adantld mpd ) BUCLZ
      ABCUDUELZDEMZUFZBNLZCNLZOZBDUGUECADUHZUGUEUIUJZUVAUUTUVFUVBBCAUDUKULUMUVC
      UVEUVHUVDUUTUVAUVBUVEUVHPUUTUVAUVEUVBUVHUVAUUTUVEUVBUVHPZPUVAUUTUVEUVIUVA
      ECUNQZARZBURQZUOZCURQZUOZGSZRZHSZUVPQZUVNQZAUVRUVLQZUHZTZHUVMUSZOZGUPZOUU
      TUVEOZUVIPZUVNHGUVLABCEUVJFUVJUTZUVLUTZUVNUTZUQUVKUWFUWHUVKUWEUWHGUVKUWEU
      WGUVBUVHUVKUWEUWGUFZUVBOZUVHDUVGUASZRZISZUVLQZDMZIUVMVAZUWPUVNQZUVGMZIUVO
      VAZJSZRZUWNUWAUHZUVRUXCQZUVNQZTZHUWSUSZOZJUPZOZUAUPZUWMUXLDUVGADVBZRZUXDU
      XNUWAUHZUXGTZHUWSUSZOZJUPZOZUANUXNUWLAVCZDNLUXNNLUVBUVKUWEUYBUWGEUVJAVDVE
      DEEBUNFVFVJADNVGVHUWMUXOUYAUWLEUVJAVIZUVBUXOUVKUWEUYCUWGEUVJAVKVEEUVJDAVL
      VMUWMUXOOZUXOUXTUWMUXOVNUYDUXSUWSUXBUVPUWSVBZRZUXPUVRUYEQZUVNQZTZHUWSUSZO
      JNUYEUYENLUYDUVPUWSGVOWBVPUYDUYFUYJUYDUYFUWSUVPUWSUHZUYERZUYDUVMUVOUVPVIZ
      UWSUVMMZUYLUWLUYMUVBUXOUWEUVKUYMUWGUVQUYMUWDUVMUVOUVPVKVQUMVRUWRIUVMVSZUV
      MUVOUWSUVPVLVTUYDUXBUYKUWSUYEUYDUBUXBUYKUYDUBSZUVOLUYPUVNQZUVGMZOZKSZUVPQ
      UYPTZKUWSWAZUYPUXBLZUYPUYKLZUYDUYSUYTUVLQZDMZVUAOKUVMWAZVUBUYDUVKUVMEWCZU
      VLWDZOZUVBUVQOUWDUYSVUGWEUWLVUJUVBUXOUVKUWGVUJUWEUWGVUIUVKUUTVUIUVEUUTUVM
      VUHWFWGZWHZUVLWDZVUIUVLBEFUWJWIVUMUVMVULVUHUVLVUMWJVUMVUHVUKWKWLWMVQWNWQV
      RUYDUVQUVBUWMUVQUVBOUXOUWLUVQUVBUVKUVQUWDUWGWOWPVQWRUWMUWDUXOUVQUWDUVKUWG
      UVBWSVQUVMUVOHKAUVLUVNUVPUYPDEUVJWTXAUWRVUFVUAKIUVMUWPUYTTUWQVUEDUWPUYTUV
      LXBXCXFXDVUCUYSWEUYDUXAUYRIUYPUVOUWPUYPTUWTUYQUVGUWPUYPUVNXBXCXGVPUYDUVPU
      VMXEZUYNOZVUDVUBWEUWLVUOUVBUXOUWEUVKVUOUWGUVQVUOUWDUVQVUNUYNUVMUVOUVPXHUY
      OXIVQUMVRKUVMUWSUYPUVPXJWMXKXLXMXNUWMUXOUYJUVKUWEUWGUVBUXOUYJPUVKUXOUWGUV
      BUWEUYJUVKUXOUWGUVBUWEUYJPUVKUXOUWGUFZUVBOZUVQUWDUYJUWDUWCHUWSUSZVUQUVQOZ
      UYJUYNUWDVURPUYOUWCHUWSUVMXQXOVUSUWCUYIHUWSVUQUVKUXOUVFUFZUVBOZUVQUVRUWSL
      ZUWCUYIPVUPVUTUVBUWGUVFUVKUXOUUTUVDUVEBUCXPWPXRWPVVAUVQOZVVBOZUWCUYIVVDUW
      COZUVTUWBUYHUXPVVDUWCVNVVEUYGUVSUVNVVBUYGUVSTVVCUWCUVRUWSUVPXSXTYAVVEUWAD
      MZUXPUWBTVVBVVFVVCUWCVVBUVRUVMLVVFUWRVVFIUVRUVMIHYBUWQUWADUWPUVRUVLXBXCXG
      YCXTAUWADYDWMYEYGYFYHYIYJYKYLYMYNYOUXCUYETZUXDUYFUXRUYJUWSUXBUXCUYEYPVVGU
      XQUYIHUWSVVGUXGUYHUXPVVGUXFUYGUVNUVRUXCUYEYSYAUUAYQYRYTYOUUBUWNUXNTZUWOUX
      OUXKUXTDUVGUWNUXNYPVVHUXJUXSJVVHUXIUXRUXDVVHUXHUXQHUWSVVHUXEUXPUXGUWNUXNU
      WAUUCUUDYQUUEUUFYRYTUWMUWGUVBUVGUVJMZUVHUXMWEUVKUWEUWGUVBUUGUWLUVBVNUWLUV
      BVVIUVKUWEUVBVVIPUWGUVKVVIUVBUVKEUVJADEUVJAUUHUUIUUJVEYNINUCUAJHBCUVLUVNU
      WSUXBUVGDEUVJFUWIUWJUWKUWSUTUXBUTUUKUULXNYKUUMYNWMUUNUUOUUPUUQUURUUS $.
  $}

  ${
    $d G f g i $.  $d G x $.  $d H f g i $.  $d H x $.  $d I x $.  $d J x $.
    $d M f g i $.  $d M x $.  $d N f g i $.  $d N x $.  $d T f g i $.
    $d U f g i $.  $d K i $.  $d L i $.
    clnbgrisubgrgrim.i $e |- I = ( iEdg ` G ) $.
    clnbgrisubgrgrim.j $e |- J = ( iEdg ` H ) $.
    clnbgrisubgrgrim.n $e |- N = ( G ClNeighbVtx X ) $.
    clnbgrisubgrgrim.m $e |- M = ( H ClNeighbVtx Y ) $.
    clnbgrisubgrgrim.k $e |- K = { x e. dom I | ( I ` x ) C_ N } $.
    clnbgrisubgrgrim.l $e |- L = { x e. dom J | ( J ` x ) C_ M } $.
    $( Isomorphic subgraphs induced by closed neighborhoods of vertices of two
       graphs.  (Contributed by AV, 29-May-2025.) $)
    clnbgrisubgrgrim $p |- ( ( G e. U /\ H e. T )
                  -> ( ( G ISubGr N ) ~=gr ( H ISubGr M )
         <-> E. f ( f : N -1-1-onto-> M /\ E. g ( g : K -1-1-onto-> L
                  /\ A. i e. K ( f " ( I ` i ) ) = ( J ` ( g ` i ) ) ) ) ) ) $=
      ( wcel wa cvtx cfv wss cisubgr co cgric wbr cv wf1o cima wceq wral wex wb
      cclnbgr eqid clnbgrssvtx eqsstri isubgrgrim mpanr12 ) GCUCHBUCUDNGUEUFZUG
      MHUEUFZUGGNUHUIHMUHUIUJUKNMDULZUMKLEULZUMVGFULZIUFUNVIVHUFJUFUOFKUPUDEUQU
      DDUQURNGOUSUIVESGOVEVEUTZVAVBMHPUSUIVFTHPVFVFUTZVAVBABCDEFGHIJKLMNVEVFVJV
      KQRUAUBVCVD $.
  $}

  ${
    $d F e g i j k n $.  $d G e g i j k n $.  $d H e g i j k n $.
    $d V e g j k n $.  $d X e g j k n $.
    clnbgrgrim.v $e |- V = ( Vtx ` G ) $.
    ${
      $d E j n $.  $d K j k n $.  $d W e j k n $.  $d Y e j k n $.
      clnbgrgrimlem.w $e |- W = ( Vtx ` H ) $.
      clnbgrgrimlem.e $e |- E = ( Edg ` H ) $.
      $( Lemma for ~ clnbgrgrim :  For two isomorphic hypergraphs, if there is
         an edge connecting the image of a vertex of the first graph with a
         vertex of the second graph, the vertex of the second graph is the
         image of a neighbor of the vertex of the first graph.  (Contributed by
         AV, 2-Jun-2025.) $)
      clnbgrgrimlem $p |- ( ( ( G e. UHGraph /\ H e. UHGraph )
                             /\ F e. ( G GraphIso H ) /\ ( X e. V /\ Y e. W ) )
              -> ( ( K e. E /\ { ( F ` X ) , Y } C_ K )
                         -> E. n e. ( G ClNeighbVtx X ) ( F ` n ) = Y ) ) $=
        ( wcel wa cfv wss wceq wi adantr vj vi vk ve cuhgr cgrim co w3a cclnbgr
        cpr cv wrex ccnv wf1o ciedg cdm cima wral wex wb cedg eqid uhgredgiedgb
        eleq2i bitrid adantl 3ad2ant3 sseq2 wo simp1 simpr anim12i f1ocnvdm syl
        simpl jca ad2antrr uhgrfun simpl2l sylan iedgedg 2fveq3 imaeq2d eqeq12d
        wfun fveq2 rspcv f1ocnvfv2 fveqeq2d f1ofn simpr3l fnimapr preq2d eqtr2d
        wfn 3jca sseq1d wf1 f1of1 simpr2l uhgrss f1imass syl12anc biimpd sylbid
        prssd ex syld com23 3exp2 com25 expimpd 3imp1 imp mpd rspcedvd clnbgrel
        sylanbrc rexlimdva 3exp1 exlimdv grimprop syl11 fveqeq2 grimf1o 3adant1
        olcd impd ) DUENZEUENZOZCDEUFUGNZIGNZJHNZOZUHZFBNZICPZJUJZFQZOZAUKZCPJR
        ZADIUIUGZULYPUUAOZUUCJCUMPZCPZJRZAUUFUUDYKYLYOUUAUUFUUDNZGHCUNZDUOPZUPZ
        EUOPZUPZUAUKZUNZUBUKZUUOPUUMPZCUUQUUKPZUQZRZUBUULURZOZUAUSZOYKYOUUAUUIS
        ZSZYLUUJUVDYKUVFSZUUJUVCUVGUAUUJUVCYKYOUVEUUJUVCYKUHZYOOZYQYTUUIUVIYQFU
        CUKZUUMPZRZUCUUNULZYTUUISZUVHYQUVMUTZYOYKUUJUVOUVCYJUVOYIYQFEVAPZNYJUVM
        BUVPFMVDUCFEUUMUUMVBZVCVEVFVGTUVIUVLUVNUCUUNUVIUVJUUNNZOZUVLUVNUVSUVLOY
        TYSUVKQZUUIUVLYTUVTUTUVSFUVKYSVHVFUVSUVTUUISUVLUVSUVTUUIUVSUVTOZUUFGNZY
        MOZUUFIRZIUUFUJZUDUKZQZUDDVAPZULZVIUUIUVIUWCUVRUVTUVIUWBYMUVIUUJYNOZUWB
        UVHUUJYOYNUUJUVCYKVJYMYNVKZVLGHJCVMZVNYOYMUVHYMYNVOVFVPVQUWAUWIUWDUWAUW
        GUWEUVJUUOUMPZUUKPZQZUDUWNUWHUVSUWNUWHNZUVTUVSUUKWEZUWMUULNZOUWPUVSUWQU
        WRUVHUWQYOUVRYKUUJUWQUVCYIUWQYJUUKDUUKVBZVRTVGVQUVIUUPUVRUWRUUPUVBUUJYK
        YOVSUULUUNUVJUUOVMVTZVPUUKDUWMUWSWAVNTUWFUWNRUWGUWOUTUWAUWFUWNUWEVHVFUV
        SUVTUWOUVSUWRUVTUWOSZUWTUVIUVRUWRUXASZUUJUVCYKYOUVRUXBSZUUJUUPUVBYKYOUX
        CSSUUJUUPOZUVRYKYOUVBUXBUXDUVRYKYOUVBUXBSUXDUVRYKYOUHZOZUWRUVBUXAUXFUWR
        UVBUXASUXFUWROZUVBUWMUUOPZUUMPZCUWNUQZRZUXAUWRUVBUXKSUXFUVAUXKUBUWMUULU
        UQUWMRZUURUXIUUTUXJUUQUWMUUMUUOWBUXLUUSUWNCUUQUWMUUKWFWCWDWGVFUXGUXKUVK
        UXJRZUXAUXGUXHUVJUXJUUMUXGUUPUVROZUXHUVJRUXFUXNUWRUXDUUPUXEUVRUUJUUPVKU
        VRYKYOVJVLTUULUUNUVJUUOWHVNWIUXGUXMUXAUXGUXMOUVTYSUXJQZUWOUXMUVTUXOUTUX
        GUVKUXJYSVHVFUXGUXOUWOSUXMUXGUXOCUWEUQZUXJQZUWOUXGYSUXPUXJUXGUXPYRUUGUJ
        ZYSUXGCGWOZYMUWBUHZUXPUXRRUXFUXTUWRUXFUXSYMUWBUUJUXSUUPUXEGHCWJVQYMYNUV
        RYKUXDWKZUXFUWJUWBUXDUUJUXEYNUUJUUPVOYOUVRYNYKUWKVGVLZUWLVNZWPTGIUUFCWL
        VNUXGUUGJYRUXGUWJUUHUXFUWJUWRUYBTGHJCWHZVNWMWNWQUXGUXQUWOUXGGHCWRZUWEGQ
        ZUWNGQZUXQUWOUTUXDUYEUXEUWRUUJUYEUUPGHCWSTVQUXFUYFUWRUXFIUUFGUYAUYCXFTU
        XFYIUWRUYGYIYJUVRYOUXDWTUUKUWMDGKUWSXAVTGHUWEUWNCXBXCXDXETXEXGXEXHXGXIX
        JXKXLXMXNXOXNXPYGUDUWHDUUFGIKUWHVBXQXRXGTXEXGXSXEYHXTYAXNUUMUBUAUUKCDEG
        HKLUWSUVQYBYCXMUUBUUFRUUCUUHUTUUEUUBUUFJCYDVFUUEUWJUUHYPUWJUUAYLYOUWJYK
        YLUUJYOYNCDEGHKLYEUWKVLYFTUYDVNXPXG $.
    $}

    $d F e n x $.  $d G x $.  $d H x $.  $d V x $.  $d X x $.
    $( Graph isomorphisms between hypergraphs map closed neighborhoods onto
       closed neighborhoods.  (Contributed by AV, 2-Jun-2025.) $)
    clnbgrgrim $p |- ( ( ( ( G e. UHGraph /\ H e. UHGraph )
                           /\ F e. ( G GraphIso H ) ) /\ X e. V )
              -> ( H ClNeighbVtx ( F ` X ) ) = ( F " ( G ClNeighbVtx X ) ) ) $=
      ( ve vn wcel wa cfv cv wceq wss wrex wb wi w3a adantr adantl cclnbgr cima
      vx vg vi vk vj cuhgr cgrim co cvtx cpr cedg wo clnbgrvtxel 3ad2ant3 eqidd
      fveqeq2 rspcedvdw eqeq2 rexbidv syl5ibrcom simpl2 simpl1 simp3 simpl eqid
      anim12i clnbgrgrimlem syl3anc expd rexlimdv jaod wf1o ciedg wral grimprop
      expimpd cdm wex f1of 3ad2ant1 ad2antrr clnbgrisvtx ffvelcdmd eleq1 eqcoms
      wf mpbird clnbgrel fveq2 orcd uhgredgiedgb 3ad2ant2 biimpa 2fveq3 imaeq2d
      2a1d eqeq12d rspcv sseq2 wfun uhgrfun ffvelcdmda iedgedg syl2an2r 3adant2
      wfn pm3.22 3anass sylibr fnimapr syl imass2 eqsstrrd simp1r sseqtrrd 3exp
      f1ofn 3adant3 sylbid syld com34 com25 exlimdv imp 3imp imp31 rexlimdva ex
      mpd com14 olcd com12 jaoi impcom sylbi eqeq1 preq2 a1i sseq1d clnbgrssvtx
      orbi12d jca31 syl3an1 impbid grimf1o fvelimab syl2an 3bitr4d eqrdv ) BUHI
      ZCUHIZJZABCUIUJIZJZEDIZJZUCCEAKZUAUJZABEUAUJZUBZUURUCLZCUKKZIZUUSUVDIZJZU
      VCUUSMZUUSUVCULZGLZNZGCUMKZOZUNZJZHLZAKZUVCMZHUVAOZUVCUUTIZUVCUVBIZUUPUUQ
      UVOUVSPZUUOUUNUUQUWBQUUOUUNUUQUWBUUOUUNUUQRZUVOUVSUWCUVGUVNUVSUWCUVGJZUVH
      UVSUVMUWDUVSUVHUVQUUSMZHUVAOZUWCUWFUVGUWCUWEUUSUUSMHEUVAUVPEUUSAURUUQUUOE
      UVAIUUNBEDFUOUPUWCUUSUQUSSUVHUVRUWEHUVAUVCUUSUVQUTVAVBUWDUVKUVSGUVLUWDUVJ
      UVLIZUVKUVSUWDUUNUUOUUQUVEJUWGUVKJUVSQUUOUUNUUQUVGVCUUOUUNUUQUVGVDUWCUUQU
      VGUVEUUOUUNUUQVEUVEUVFVFVHHUVLABCUVJDUVDEUVCFUVDVGZUVLVGZVIVJVKVLVMVRUUOD
      UVDAVNZBVOKZVSZCVOKZVSZUDLZVNZUELZUWOKUWMKZAUWQUWKKZUBZMZUEUWLVPZJZUDVTZJ
      ZUUNUUQUVSUVOQUWMUEUDUWKABCDUVDFUWHUWKVGZUWMVGZVQUXEUUNUUQRZUVRUVOHUVAUXH
      UVPUVAIZJZUVRUVOUXJUVRJZUVEUVFUVNUXKUVEUVQUVDIZUXKDUVDUVPAUXHDUVDAWHZUXIU
      VRUXEUUNUXMUUQUWJUXMUXDDUVDAWASWBZWCUXJUVPDIZUVRUXIUXOUXHBEUVPDFWDTSWEUVR
      UVEUXLPZUXJUXPUVCUVQUVCUVQUVDWFWGTWIUXHUVFUXIUVRUXHDUVDEAUXNUXEUUNUUQVEWE
      WCUXKUVNUWEUUSUVQULZUVJNZGUVLOZUNZUXJUXTUVRUXIUXHUXTUXIUXOUUQJZUVPEMZEUVP
      ULZUFLZNZUFBUMKZOZUNZJUXHUXTQZUFUYFBUVPDEFUYFVGWJUYHUYAUYIUYBUYAUYIQUYGUY
      BUXTUYAUXHUYBUWEUXSUVPEAWKWLWRUYAUYGUYIUYAUYEUYIUFUYFUYAUYDUYFIZJZUYEUXHU
      XTUYKUYEUXHRUXSUWEUYKUYEUXHUXSUYAUYJUYEUXHUXSQQUXHUYJUYEUYAUXSUXHUYJUYEUY
      AUXSQZQZUXHUYJJZUYDUGLZUWKKZMZUGUWLOZUYMUXHUYJUYRUUNUXEUYJUYRPZUUQUULUYSU
      UMUGUYDBUWKUXFWMSWNWOUYNUYQUYMUGUWLUXHUYJUYOUWLIZUYQUYMQZUXEUUNUUQUYJUYTV
      UAQZQZUWJUXDUUNUUQVUCQQZUWJUXCVUDUDUWJUWPUXBVUDUWJUWPJZUYJUUNUUQUXBVUBVUE
      UYJUUNUUQUXBVUBQQVUEUYJUUNRZUUQUYTUXBVUAVUFUUQUYTUXBVUAQVUFUUQUYTRZUXBUYO
      UWOKZUWMKZAUYPUBZMZVUAUYTVUFUXBVUKQUUQUXAVUKUEUYOUWLUWQUYOMZUWRVUIUWTVUJU
      WQUYOUWMUWOWPVULUWSUYPAUWQUYOUWKWKWQWSWTUPVUGVUKUYQUYMVUGVUKUYQRUYEUYCUYP
      NZUYLUYQVUGUYEVUMPVUKUYDUYPUYCXAUPVUGVUKVUMUYLQUYQVUGVUKJZVUMUYAUXSVUNVUM
      UYARZUXRUXQVUINGVUIUVLUVJVUIUXQXAVUNVUMVUIUVLIZUYAVUGVUPVUKVUFUYTVUPUUQVU
      FUWMXBZUYTVUHUWNIVUPUUNVUEVUQUYJUUMVUQUULUWMCUXGXCTUPVUFUWLUWNUYOUWOVUEUY
      JUWLUWNUWOWHZUUNUWPVURUWJUWLUWNUWOWATWBXDUWMCVUHUXGXEXFXGSWBVUOUXQVUJVUIV
      UOUXQAUYCUBZVUJVUOADXHZUUQUXORZVUSUXQMVUOVUTUUQUXOJZJZVVAVUNUYAVVCVUMVUNV
      UTUYAVVBVUGVUTVUKVUFUUQVUTUYTVUEUYJVUTUUNUWJVUTUWPDUVDAXSZSWBWBSUXOUUQXIV
      HXGVUTUUQUXOXJXKDEUVPAXLXMVUMVUNVUSVUJNUYAUYCUYPAXNWNXOVUGVUKVUMUYAXPXQUS
      XRXTYAXRYBXRYCXRYDVRYEYFYGYHYIYKYJYLYFYGYMXRYIYNYOYPYQYPSUVRUVNUXTPZUXJVV
      EUVCUVQUVCUVQMZUVHUWEUVMUXSUVCUVQUUSYRVVFUVKUXRGUVLVVFUVIUXQUVJUVCUVQUUSY
      SUUAVAUUCWGTWIUUDYJYIUUEUUFXRYPYFUVTUVOPUURGUVLCUVCUVDUUSUWHUWIWJYTUUPVUT
      UVADNZUWAUVSPUUQUUOVUTUUNUUOUWJVUTABCDUVDFUWHUUGVVDXMTVVGUUQBEDFUUBYTHDUV
      AUVCAUUHUUIUUJUUK $.
  $}

  ${
    $d E j k $.  $d F i j k l $.  $d G i j k l $.  $d H i j k l $.
    $d I j k l $.  $d K j k l $.  $d V j k l $.
    grimedg.v $e |- V = ( Vtx ` G ) $.
    grimedg.i $e |- I = ( Edg ` G ) $.
    grimedg.e $e |- E = ( Edg ` H ) $.
    $( For two isomorphic graphs, a set of vertices is an edge in one graph iff
       its image by a graph isomorphism is an edge of the other graph.
       (Contributed by AV, 7-Jun-2025.) $)
    grimedg $p |- ( ( G e. UHGraph /\ H e. UHGraph /\ F e. ( G GraphIso H ) )
                    -> ( K e. I <-> ( ( F " K ) e. E /\ K C_ V ) ) ) $=
      ( vi vk wcel wss wa wb cfv wceq wi adantl vj vl cuhgr cgrim co cima ciedg
      cvtx wf1o cdm cv wral wex eqid grimprop wrex eleq2i uhgredgiedgb ad2antll
      cedg bitrid 2fveq3 fveq2 imaeq2d eqeq12d rspcv wfun uhgrfun ad2antrr f1of
      wf simplr ffvelcdmd iedgedg eleqtrrdi syl2an2r eleq1 eqcoms syl5ibrcom ex
      com23 syld impr impl adantr imaeq2 eleq1d mpbird uhgrss imp jca rexlimdva
      com13 sseq1 sylbid ad2antrl wfo f1ofo ad2antlr foelrn sylan simpl simplrr
      w3a eqeq2d mpbid eqeq2 wf1 f1of1 ad3antrrr syl2an anim1ci f1imaeq syl2anc
      mpd exp31 com24 3imp expdimp syl5d 3exp com25 impd impbid exlimdv expd
      syl ) CUCMZDUCMZBCDUDUEMZFEMZBFUFZAMZFGNZOZPZYJYIYHYPYJYIYHYPYJGDUHQZBUIZ
      CUGQZUJZDUGQZUJZUAUKZUIZKUKZUUCQUUAQZBUUEYSQZUFZRZKYTULZOZUAUMZOYIYHOZYPS
      ZUUAKUAYSBCDGYQHYQUNZYSUNZUUAUNZUOYRUULUUNYRUUKUUNUAYRUUKUUMYPYRUUKOZUUMO
      ZYKYOUUSYKFLUKZYSQZRZLYTUPZYOYKFCUTQZMZUUSUVCEUVDFIUQYHUVEUVCPUURYILFCYSU
      UPURUSVAUUSUVBYOLYTUUSUUTYTMZOZUVBYOUVGUVBOZYMYNUVHYMBUVAUFZAMZUVGUVJUVBU
      URUUMUVFUVJYRUUDUUJUUMUVFOZUVJSUVKUUJYRUUDOZUVJUVKUUJUUTUUCQZUUAQZUVIRZUV
      LUVJSUVFUUJUVOSUUMUUIUVOKUUTYTUUEUUTRZUUFUVNUUHUVIUUEUUTUUAUUCVBUVPUUGUVA
      BUUEUUTYSVCVDVEVFTUVKUVLUVOUVJUVKUVLUVOUVJSUVKUVLOZUVJUVOUVNAMZUVKUUAVGZU
      VLUVMUUBMZUVRYIUVSYHUVFUUADUUQVHVIUVQYTUUBUUTUUCUUDYTUUBUUCVKUVKYRYTUUBUU
      CVJUSUUMUVFUVLVLVMUVSUVTOUVNDUTQZAUUADUVMUUQVNJVOVPUVJUVRPUVIUVNUVIUVNAVQ
      VRVSVTWAWBWMWCWDWEUVBYMUVJPUVGUVBYLUVIAFUVABWFWGTWHUVHYNUVAGNZUVGUWBUVBUU
      SUVFUWBYHUVFUWBSUURYIYHUVFUWBYSUUTCGHUUPWIVTUSWJWEUVBYNUWBPUVGFUVAGWNTWHW
      KVTWLWOUUSYMYNYKUUSYMYLUUTUUAQZRZLUUBUPZYNYKSZYMYLUWAMZUUSUWEAUWAYLJUQYIU
      WGUWEPUURYHLYLDUUAUUQURWPVAUUSUWDUWFLUUBUUSUUTUUBMZOUUTUBUKZUUCQZRZUBYTUP
      ZUWDUWFSZUUSYTUUBUUCWQZUWHUWLUUKUWNYRUUMUUDUWNUUJYTUUBUUCWRWEWSUBYTUUBUUT
      UUCWTXAUURUUMUWHUWLUWMSZYRUUDUUJUUMUWHOZUWOSUVLUWDUWPUWLUUJUWFUVLUWDUWPUW
      LUUJUWFSZSUVLUWDUWPXDZUWKUWQUBYTUWRUWIYTMZOUUJUWJUUAQZBUWIYSQZUFZRZUWKUWF
      UWSUUJUXCSUWRUUIUXCKUWIYTUUEUWIRZUUFUWTUUHUXBUUEUWIUUAUUCVBUXDUUGUXABUUEU
      WIYSVCVDVEVFTUWRUWSUWKUXCUWFSZUVLUWDUWPUWSUWKOZUXESUVLUXFUWPUWDUXEUVLUWPU
      XFUWDUXESZUVLUWPUXFUXGUVLUWPOZUXFOZUWDYLUWTRZUXEUWKUWDUXJPUXHUWSUWKUWCUWT
      YLUUTUWJUUAVCXEUSUXIUXCUXJUWFUXIUXCUXJUWFUXIUXCOZUXJOZYLYQNZUWFUXLUXMUWTY
      QNZUXIUXNUXCUXJUXHYIUXFUWJUUBMZUXNUUMYIUVLUWHYIYHXBWPUXIUWHUXOUVLUUMUWHUX
      FXCUWKUWHUXOPUXHUWSUUTUWJUUBVQUSXFUUAUWJDYQUUOUUQWIVPVIUXJUXMUXNPUXKYLUWT
      YQWNTWHUXKUXJUXMUWFSZUXKUXJYLUXBRZUXPUXCUXJUXQPUXIUWTUXBYLXGTUXKUXMUXQUWF
      UXKUXMUXQUWFSUXKUXMOZYNUXQYKUXRYNUXQYKSUXRYNOZUXQFUXARZYKUXSGYQBXHZYNUXAG
      NZOUXQUXTPUXIUYAUXCUXMYNYRUYAUUDUWPUXFGYQBXIXJXJUXRUYBYNUXIUYBUXCUXMUXHYH
      UWSUYBUXFUWPYHUVLYIYHUWHVLTUWSUWKXBZYSUWICGHUUPWIXKVIXLGYQFUXABXMXNUXIUXT
      YKSUXCUXMYNUXIYKUXTUXAEMUXIUXAUVDEUXHYSVGZUWSUXAUVDMUXFUWPUYDUVLYHUYDYIUW
      HYSCUUPVHWSTUYCYSCUWIUUPVNXKIVOFUXAEVQVSXJWOVTWAVTWAWOWJXOXPWAWOXPWAXQXRX
      SXTWLYAYBWCWDXOWLWOYCYDXPYEWJYGYFWMXR $.

    $( Graph isomorphisms map edges onto the corresponding edges.  (Contributed
       by AV, 30-Dec-2025.) $)
    grimedgi $p |- ( ( G e. UHGraph /\ H e. UHGraph /\ F e. ( G GraphIso H ) )
                     -> ( K e. I -> ( F " K ) e. E ) ) $=
      ( cuhgr wcel cgrim co w3a cima wss wa grimedg simpl biimtrdi ) CKLDKLBCDM
      NLOFELBFPALZFGQZRUBABCDEFGHIJSUBUCTUA $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Triangles in graphs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

   Usually, a "triangle" in graph theory is a complete graph consisting of
   three vertices (denoted by " K_3 "), see the definition in [Diestel] p. 3 or
   the definition in [Bollobas] p. 5.  This corresponds to the definition of a
   "triangle graph" (which is a more precise term) in Wikipedia "Triangle
   graph", ~ https://en.wikipedia.org/wiki/Triangle_graph , 27-Jul-2025: "In
   the mathematical field of graph theory, the _triangle graph_ is a planar
   undirected graph with 3 vertices and 3 edges, in the form of a triangle.
   The triangle graph is also known as the cycle graph C_3 and the complete
   graph K_3."

   Often, however, the term "triangle" is also used to denote a corresponding
   subgraph of a given graph ("triangle in a graph"), see, for example,
   Wikipedia "Triangle-free graph", 28-Jul-2025,
   ~ https://en.wikipedia.org/wiki/Triangle-free_graph : "In the mathematical
   area of graph theory, a triangle-free graph is an undirected graph in which
   no three vertices form a triangle of edges."

   In this subsection, a triangle (in a graph) is defined as a set of three
   vertices of a given graph.  In this meaning, a triangle ` T ` with
   ` ( T e. ( GrTriangles `` G ) `) is neither a graph nor a subgraph, but it
   induces a triangle graph ` ( G ISubGr T ) ` as subgraph of the given graph
   ` G `.

   We require that there are three (different) edges connecting the three
   (different) vertices of the triangle.  Therefore, it is not sufficient for
   arbitrary hypergraphs to say "a triangle is a set of three (different)
   vertices connected with each other (by edges)", because there might be only
   one or two multiedges fulfilling this statement.  We do not regard such
   degenerate cases as "triangle".

   The definition ~ df-grtri is designed for a special purpose, namely to
   provide a criterion for two graphs being not isomorphic (see ~ grimgrtri ).
   For other purposes, a more general definition might be useful, e.g.,
   ComplSubGr ` = ( g e. _V , n e. NN |-> { t e. ~P v | ( ( # `` t ) = n `
   ` /\ ( g ISubGr t ) e. ComplGraph ) } ) ` for complete subgraphs of a given
   size (proposed by TA).  With such a definition, we would have
   ` ( GrTriangles `` G ) =  ( G ` ComplSubGr ` 3 ) ` (at least for simple
   graphs), and the definition ~ df-grtri may become obsolete.

$)

  $c GrTriangles $.

  $( Extend class notation with triangles (in a graph). $)
  cgrtri $a class GrTriangles $.

  ${
    $d e f g t v $.
    $( Definition of a triangles in a graph.  A triangle in a graph is a set of
       three (different) vertices completely connected with each other.  Such
       vertices induce a closed walk of length 3, see ~ grtriclwlk3 , and the
       vertices of a cycle of size 3 are a triangle in a graph, see
       ~ cycl3grtri .  (Contributed by AV, 20-Jul-2025.) $)
    df-grtri $a |- GrTriangles = ( g e. _V
                    |-> [_ ( Vtx ` g ) / v ]_ [_ ( Edg ` g ) / e ]_
                        { t e. ~P v | E. f ( f : ( 0 ..^ 3 ) -1-1-onto-> t
                                 /\ ( { ( f ` 0 ) , ( f ` 1 ) } e. e
                                   /\ { ( f ` 0 ) , ( f ` 2 ) } e. e
                                   /\ { ( f ` 1 ) , ( f ` 2 ) } e. e ) ) } ) $.
  $}

  $( Lemma for ~ grtriprop .  (Contributed by AV, 23-Jul-2025.) $)
  grtriproplem $p |- ( ( f : ( 0 ..^ 3 ) -1-1-onto-> { x , y , z }
         /\ ( { ( f ` 0 ) , ( f ` 1 ) } e. E /\ { ( f ` 0 ) , ( f ` 2 ) } e. E
           /\ { ( f ` 1 ) , ( f ` 2 ) } e. E ) )
                 -> ( { x , y } e. E /\ { x , z } e. E /\ { y , z } e. E ) ) $=
    ( cpr wcel w3a wceq simp1 simp2 preq12d eleq1d simp3 3anbi123d prcom eleq1i
    cv sylbb biimtrdi cc0 c3 cfzo co ctp wf1o cfv c1 c2 wf1 wo w3o f1of1 fvf1tp
    wi biimpd 3ancoma 3anbi3i jaoi 3ancomb 3anbi1i 3anrot biid 3anbi123i sylbbr
    3anrev 3jaoi 3syl imp ) UAUBUCUDZARZBRZCRZUEZDRZUFZUAVOUGZUHVOUGZFZEGZVQUIV
    OUGZFZEGZVRWAFZEGZHZVKVLFZEGZVKVMFZEGZVLVMFZEGZHZVPVJVNVOUJVQVKIZVRVLIZWAVM
    IZHZWNVRVMIZWAVLIZHZUKZVQVLIZVRVKIZWPHZXBWRWAVKIZHZUKZVQVMIZXCWSHZXHWOXEHZU
    KZULWFWMUOZVJVNVOUMVOVKVLVMUNXAXLXGXKWQXLWTWQWFWMWQVTWHWCWJWEWLWQVSWGEWQVQV
    KVRVLWNWOWPJZWNWOWPKZLMWQWBWIEWQVQVKWAVMXMWNWOWPNZLMWQWDWKEWQVRVLWAVMXNXOLM
    OUPWTWFWJWHVMVLFZEGZHZWMWTVTWJWCWHWEXQWTVSWIEWTVQVKVRVMWNWRWSJZWNWRWSKZLMWT
    WBWGEWTVQVKWAVLXSWNWRWSNZLMWTWDXPEWTVRVMWAVLXTYALMOXRWHWJXQHWMWJWHXQUQXQWLW
    HWJXPWKEVMVLPQZURSTUSXDXLXFXDWFVLVKFZEGZWLWJHZWMXDVTYDWCWLWEWJXDVSYCEXDVQVL
    VRVKXBXCWPJZXBXCWPKZLMXDWBWKEXDVQVLWAVMYFXBXCWPNZLMXDWDWIEXDVRVKWAVMYGYHLMO
    YEYDWJWLHWMYDWLWJUTYDWHWJWLYCWGEVLVKPQZVASTXFWFWLYDVMVKFZEGZHZWMXFVTWLWCYDW
    EYKXFVSWKEXFVQVLVRVMXBWRXEJZXBWRXEKZLMXFWBYCEXFVQVLWAVKYMXBWRXENZLMXFWDYJEX
    FVRVMWAVKYNYOLMOYLYDYKWLHWMWLYDYKVBYDWHYKWJWLWLYIYJWIEVMVKPQZWLVCVDSTUSXIXL
    XJXIWFYKXQWHHZWMXIVTYKWCXQWEWHXIVSYJEXIVQVMVRVKXHXCWSJZXHXCWSKZLMXIWBXPEXIV
    QVMWAVLYRXHXCWSNZLMXIWDWGEXIVRVKWAVLYSYTLMOWMWJWLWHHYQWHWJWLVBWJYKWLXQWHWHW
    IYJEVKVMPQWKXPEVLVMPQWHVCVDVETXJWFXQYKYDHZWMXJVTXQWCYKWEYDXJVSXPEXJVQVMVRVL
    XHWOXEJZXHWOXEKZLMXJWBYJEXJVQVMWAVKUUBXHWOXENZLMXJWDYCEXJVRVLWAVKUUCUUDLMOU
    UAYDYKXQHWMXQYKYDVFYDWHYKWJXQWLYIYPYBVDSTUSVGVHVI $.

  ${
    $d E e f g t v $.  $d G e f g t v $.  $d V e f g t v $.  $d W g $.
    grtri.v $e |- V = ( Vtx ` G ) $.
    grtri.e $e |- E = ( Edg ` G ) $.
    $( The triangles in a graph.  (Contributed by AV, 20-Jul-2025.) $)
    grtri $p |- ( G e. W -> ( GrTriangles ` G ) = { t e. ~P V |
                                E. f ( f : ( 0 ..^ 3 ) -1-1-onto-> t
                                 /\ ( { ( f ` 0 ) , ( f ` 1 ) } e. E
                                   /\ { ( f ` 0 ) , ( f ` 2 ) } e. E
                                   /\ { ( f ` 1 ) , ( f ` 2 ) } e. E ) ) } ) $=
      ( vg vv ve wcel cv cvtx cfv cedg wa csb cvv wceq cc0 c3 cfzo co c1 cpr c2
      wf1o w3a wex cpw crab cgrtri df-grtri a1i fveq2 eqtr4di csbeq1d csbeq12dv
      cmpt adantl fvexi pweq adantr wb 3anbi123d anbi2d exbidv rabeqbidv csbie2
      eleq2 eqtrdi elex pweqi fvex pwex eqeltri rabex fvmptd ) DFLZIDJIMZNOZKWA
      POZUAUBUCUDAMBMZUHZUAWDOZUEWDOZUFZKMZLZWFUGWDOZUFZWILZWGWKUFZWILZUIZQZBUJ
      ZAJMZUKZULZRZRZWEWHCLZWLCLZWNCLZUIZQZBUJZAEUKZULZSUMSUMISXCUTTVTJAKBIUNUO
      VTWADTZQXCJEKCXARZRZXKXLXCXNTVTXLJWBXBEXMXLWBDNOZEWADNUPGUQXLKWCCXAXLWCDP
      OCWADPUPHUQURUSVAJKECXAXKEDNGVBCDPHVBWSETZWICTZQWRXIAWTXJXPWTXJTXQWSEVCVD
      XQWRXIVEXPXQWQXHBXQWPXGWEXQWJXDWMXEWOXFWICWHVKWICWLVKWICWNVKVFVGVHVAVIVJV
      LDFVMXKSLVTXIAXJXJXOUKSEXOGVNXODNVOVPVQVRUOVS $.

    $d E x y z $.  $d T f t x y z $.  $d V x y z $.
    $( The properties of a triangle.  (Contributed by AV, 25-Jul-2025.) $)
    grtriprop $p |- ( T e. ( GrTriangles ` G ) -> E. x e. V E. y e. V E. z e. V
             ( T = { x , y , z } /\ ( # ` T ) = 3
               /\ ( { x , y } e. E /\ { x , z } e. E /\ { y , z } e. E ) ) ) $=
      ( vf vt cfv wcel cv wceq c3 cpr wrex wa wi cgrtri ctp w3a cpw cc0 cfzo co
      chash wf1o c1 c2 wex crab cvv elfvex grtri syl eleq2d f1oeq3 anbi1d elrab
      exbidv bitrdi ovexd simpr hasheqf1od cn0 3nn0 hashfzo0 mp1i eqeq2d bitrid
      eqcom wne wb hash3tpb adantr biimpa wss elpwi ss2rexv ssrexv reximdv syld
      simprr simp-5r grtriproplem 2a1d a1d biimtrdi adantld imp4c adantl impcom
      ex 3jca reximdva reximdvva com23 mpd sylbid expimpd exlimdv imp pm2.43i )
      DFUALZMZDANZBNZCNZUBZOZDUHLZPOZXHXIQEMXHXJQEMXIXJQEMUCZUCZCGRZBGRAGRZXGXG
      DGUDZMZUEPUFUGZDJNZUIZUEYBLZUJYBLZQEMYDUKYBLZQEMYEYFQEMUCZSZJULZSZXRXGXGD
      YAKNZYBUIZYGSZJULZKXSUMZMYJXGXFYODXGFUNMXFYOODFUAUOKJEFGUNHIUPUQURYNYIKDX
      SYKDOZYMYHJYPYLYCYGYKDYAYBUSUTVBVAVCXTYIXRXTYHXRJXTYCYGXRXTYCSZYAUHLZXMOZ
      YGXRTZYQYADUNYBYQUEPUFVDXTYCVEVFYQYSXNYTYSXMYROYQXNYRXMVMYQYRPXMPVGMYRPOY
      QVHPVIVJVKVLYQXNYTYQXNSZXHXIVNXHXJVNXIXJVNUCZXLSZCDRZBDRADRZYTYQXNUUEXTXN
      UUEVOYCDXSABCVPVQVRUUAUUEUUCCGRZBGRZAGRZYTYQUUEUUHTZXNXTUUIYCXTDGVSZUUIDG
      VTUUJUUEUUDBGRZAGRUUHUUDABDGWAUUJUUKUUGAGUUJUUDUUFBGUUCCDGWBWCWCWDUQVQVQU
      UAYGUUHXRUUAYGUUHXRTUUAYGSZUUFXQABGGUULXHGMXIGMSZSZUUCXPCGUUNXJGMZSZUUCXP
      UUPUUCSXLXNXOUUPUUBXLWEYQXNYGUUMUUOUUCWFUUCUUPXOXLUUPXOTUUBXLUULUUMUUOXOX
      LYQXNYGUUMUUOXOTTZXLYCXNYGUUQTZTZXTXLYCYAXKYBUIZUUSDXKYAYBUSUUTUURXNUUTYG
      UUQUUTYGSXOUUMUUOABCJEWGWHWOWIWJWKWLWLWMWNWPWOWQWRWOWSWDWTWOXAWTXBXCXDWJX
      E $.

    ${
      $d F x y z $.
      $( Any bijection onto a triangle preserves the edges of the triangle.
         (Contributed by AV, 25-Jul-2025.) $)
      grtrif1o $p |- ( ( T e. ( GrTriangles ` G )
                         /\ F : ( 0 ..^ 3 ) -1-1-onto-> T )
                                 -> ( { ( F ` 0 ) , ( F ` 1 ) } e. E
                                   /\ { ( F ` 0 ) , ( F ` 2 ) } e. E
                                   /\ { ( F ` 1 ) , ( F ` 2 ) } e. E ) ) $=
        ( cfv wcel cpr w3a wceq preq12 eleq1d 3adant3 3adant2 3adant1 3anbi123d
        wa wb vx vy vz cgrtri cc0 c3 cfzo co wf1o c1 c2 cv chash wrex grtriprop
        ctp wi f1oeq3 adantr w3o biimprd 3ancoma prcom eleq1i 3anbi3i imbitrrid
        wo sylbb jaoi 3ancomb 3anbi1i 3anrot biid 3anbi123i sylbb1 3anrev 3jaoi
        wf1 f1of1 fvf1tp syl syl11 adantl sylbid a1i rexlimivv rexlimivw imp )
        ADUDHIZUEUFUGUHZACUIZUECHZUJCHZJZBIZWLUKCHZJZBIZWMWPJZBIZKZWIAUAULZUBUL
        ZUCULZUPZLZAUMHUFLZXBXCJZBIZXBXDJZBIZXCXDJZBIZKZKZUCEUNUBEUNZUAEUNWKXAU
        QZUAUBUCABDEFGUOXPXQUAEXOXQUBUCEEXOXQUQXCEIXDEISXFXNXQXGXFXNSWKWJXECUIZ
        XAXFWKXRTXNAXEWJCURUSXNXRXAUQXFWLXBLZWMXCLZWPXDLZKZXSWMXDLZWPXCLZKZVGZW
        LXCLZWMXBLZYAKZYGYCWPXBLZKZVGZWLXDLZYHYDKZYMXTYJKZVGZUTZXNXAXRYFXNXAUQZ
        YLYPYBYRYEYBXAXNYBWOXIWRXKWTXMXSXTWOXITYAXSXTSWNXHBWLWMXBXCMNOXSYAWRXKT
        XTXSYASWQXJBWLWPXBXDMNPXTYAWTXMTXSXTYASWSXLBWMWPXCXDMNQRVAXNXAYEXKXIXDX
        CJZBIZKZXNXKXIXMKUUAXIXKXMVBXMYTXKXIXLYSBXCXDVCVDZVEVHYEWOXKWRXIWTYTXSY
        CWOXKTYDXSYCSWNXJBWLWMXBXDMNOXSYDWRXITYCXSYDSWQXHBWLWPXBXCMNPYCYDWTYTTX
        SYCYDSWSYSBWMWPXDXCMNQRVFVIYIYRYKXNXAYIXCXBJZBIZXMXKKZXNXIXMXKKUUEXIXKX
        MVJXIUUDXMXKXHUUCBXBXCVCVDZVKVHYIWOUUDWRXMWTXKYGYHWOUUDTYAYGYHSWNUUCBWL
        WMXCXBMNOYGYAWRXMTYHYGYASWQXLBWLWPXCXDMNPYHYAWTXKTYGYHYASWSXJBWMWPXBXDM
        NQRVFXNXAYKXMUUDXDXBJZBIZKZXMXIXKKXNUUIXMXIXKVLXMXMXIUUDXKUUHXMVMUUFXJU
        UGBXBXDVCVDZVNVOYKWOXMWRUUDWTUUHYGYCWOXMTYJYGYCSWNXLBWLWMXCXDMNOYGYJWRU
        UDTYCYGYJSWQUUCBWLWPXCXBMNPYCYJWTUUHTYGYCYJSWSUUGBWMWPXDXBMNQRVFVIYNYRY
        OXNXAYNUUHYTXIKZXNXKXMXIKUUKXIXKXMVLXKUUHXMYTXIXIUUJUUBXIVMVNVHYNWOUUHW
        RYTWTXIYMYHWOUUHTYDYMYHSWNUUGBWLWMXDXBMNOYMYDWRYTTYHYMYDSWQYSBWLWPXDXCM
        NPYHYDWTXITYMYHYDSWSXHBWMWPXBXCMNQRVFXNXAYOYTUUHUUDKZXNXMXKXIKUULXIXKXM
        VPXMYTXKUUHXIUUDUUBUUJUUFVNVHYOWOYTWRUUHWTUUDYMXTWOYTTYJYMXTSWNYSBWLWMX
        DXCMNOYMYJWRUUHTXTYMYJSWQUUGBWLWPXDXBMNPXTYJWTUUDTYMXTYJSWSUUCBWMWPXCXB
        MNQRVFVIVQXRWJXECVRYQWJXECVSCXBXCXDVTWAWBWCWDPWEWFWGWAWH $.
    $}

    $d G x y z $.  $d V f i x y z $.
    $( A triangle in a graph.  (Contributed by AV, 20-Jul-2025.) $)
    isgrtri $p |- ( T e. ( GrTriangles ` G ) <-> E. x e. V E. y e. V E. z e. V
            ( T = { x , y , z } /\ ( # ` T ) = 3
              /\ ( { x , y } e. E /\ { x , z } e. E /\ { y , z } e. E ) ) ) $=
      ( vf vi cfv wcel cv wceq cpr wa cc0 preq12d eleq1d vt cgrtri ctp chash c3
      w3a wrex grtriprop cpw cfzo co wf1o c1 c2 wex csn prelpwi snelpwi anim12i
      cun df-tp anasss pwuncl syl eqeltrid adantr wb 3ad2ant1 adantl mpbird cif
      eleq1 cmpt cvv ovex mptex a1i 3anass biimpri fveq2 simp2 eqtrd eqid tpf1o
      eqcomd syl2an f1oeq3 wi tpf1ofv0 tpf1ofv1 tpf1ofv2 3anbi123d biimpd 3imp2
      2a1d jca f1oeq1 fveq1 spcedv crab 1vgrex grtri eleq2d anbi1d exbidv elrab
      anbi12d bitrdi ex rexlimdvva rexlimiv impbii ) DFUBLZMZDANZBNZCNZUCZOZDUD
      LZUEOZXOXPPZEMZXOXQPZEMZXPXQPZEMZUFZUFZCGUGBGUGZAGUGABCDEFGHIUHYJXNAGXOGM
      ZYIXNBCGGYKXPGMZXQGMZQZQZYIXNYOYIQZXNDGUIZMZRUEUJUKZDJNZULZRYTLZUMYTLZPZE
      MZUUBUNYTLZPZEMZUUCUUFPZEMZUFZQZJUOZQZYPYRUUMYPYRXRYQMZYOUUOYIYOXRYBXQUPZ
      UTZYQXOXPXQVAYOYBYQMZUUPYQMZQZUUQYQMYKYLYMUUTYKYLQUURYMUUSXOXPGUQXQGURUSV
      BYBUUPGVCVDVEVFYIYRUUOVGZYOXSYAUVAYHDXRYQVLVHVIVJYPUULYSDKYSKNZROXOUVBUMO
      XPXQVKVKZVMZULZRUVDLZUMUVDLZPZEMZUVFUNUVDLZPZEMZUVGUVJPZEMZUFZQJVNUVDUVDV
      NMYPKYSUVCRUEUJVOVPVQYPUVEUVOYPUVEYSXRUVDULZYOYKYLYMUFZXRUDLZUEOUVPYIUVQY
      OYKYLYMVRVSYIUVRXTUEXSYAUVRXTOYHXSXTUVRDXRUDVTWEVHXSYAYHWAWBKXOXPXQXRUVDG
      UVDWCZXRWCWDWFYIUVEUVPVGZYOXSYAUVTYHDXRYSUVDWGVHVIVJYOXSYAYHUVOYOYHUVOWHX
      SYAYOYHUVOYOYCUVIYEUVLYGUVNYOYBUVHEYOUVHYBYOUVFXOUVGXPYKUVFXOOYNKXOXPXQUV
      DGUVSWIVFZYNUVGXPOZYKYLUWBYMKXOXPXQUVDGUVSWJVFVIZSWETYOYDUVKEYOUVKYDYOUVF
      XOUVJXQUWAYNUVJXQOZYKYMUWDYLKXOXPXQUVDGUVSWKVIVIZSWETYOYFUVMEYOUVMYFYOUVG
      XPUVJXQUWCUWESWETWLWMWOWNWPYTUVDOZUUAUVEUUKUVOYSDYTUVDWQUWFUUEUVIUUHUVLUU
      JUVNUWFUUDUVHEUWFUUBUVFUUCUVGRYTUVDWRZUMYTUVDWRZSTUWFUUGUVKEUWFUUBUVFUUFU
      VJUWGUNYTUVDWRZSTUWFUUIUVMEUWFUUCUVGUUFUVJUWHUWISTWLXGWSWPYOXNUUNVGZYIYKU
      WJYNYKXNDYSUANZYTULZUUKQZJUOZUAYQWTZMZUUNYKFVNMZXNUWPVGFXOGHXAUWQXMUWODUA
      JEFGVNHIXBXCVDUWNUUMUADYQUWKDOZUWMUULJUWRUWLUUAUUKUWKDYSYTWGXDXEXFXHVFVFV
      JXIXJXKXL $.
  $}

  ${
    $d G x y z $.  $d T x y z $.  $d V x y z $.
    grtrissvtx.v $e |- V = ( Vtx ` G ) $.
    $( A triangle is a subset of the vertices (of a graph).  (Contributed by
       AV, 26-Jul-2025.) $)
    grtrissvtx $p |- ( T e. ( GrTriangles ` G ) -> T C_ V ) $=
      ( vx vy vz cgrtri cfv wcel cv ctp wceq chash c3 cpr w3a wrex wss wa tpssi
      cedg grtriprop 3expa wb sseq1 3ad2ant1 syl5ibrcom rexlimdva rexlimivv syl
      eqid ) ABHIJAEKZFKZGKZLZMZANIOMZUMUNPBUBIZJUMUOPUSJUNUOPUSJQZQZGCRZFCRECR
      ACSZEFGAUSBCDUSULUCVBVCEFCCUMCJZUNCJZTZVAVCGCVFUOCJZTVCVAUPCSZVDVEVGVHUMU
      NUOCUAUDUQURVCVHUEUTAUPCUFUGUHUIUJUK $.
  $}

  ${
    $d G i $.  $d P i $.  $d ph i $.
    grtriclwlk3.t $e |- ( ph -> T e. ( GrTriangles ` G ) ) $.
    grtriclwlk3.p $e |- ( ph -> P : ( 0 ..^ 3 ) -1-1-onto-> T ) $.
    $( A triangle induces a closed walk of length 3 .  (Contributed by AV,
       26-Jul-2025.) $)
    grtriclwlk3 $p |- ( ph -> P e. ( 3 ClWWalksN G ) ) $=
      ( vi c3 co wcel cfv c1 cpr cc0 cfzo wceq wa 3syl adantr c2 cclwwlkn cword
      cvtx cv caddc cedg chash cmin wral clsw w3a wfn f1ofn hashfn cn0 hashfzo0
      wf1o 3nn0 mp1i eqtrd wf wss f1of syl cgrtri eqid grtrissvtx jca iswrdi wb
      oveq1 3m1e2 eqtrdi oveq2d fzo0to2pr eleq2d adantl wo grtrif1o simp1 fveq2
      fss fv0p1e1 preq12d eleq1d imbitrrid simp3 1p1e2 fveq2d jaoi elpri sylbid
      wi syl11 ralrimiv cvv ovexd fex lsw preq1d eleq1i biimpi 3ad2ant2 eqeltrd
      prcom 3jca simpr mpdan cn 3nn isclwwlknx mpbird ) ABHDUAIJZBDUCKZUBJZGUDZ
      BKZXPLUEIZBKZMZDUFKZJZGNBUGKZLUHIZOIZUIZBUJKZNBKZMZYAJZUKZYCHPZQZAYLYMAYC
      NHOIZUGKZHAYNCBUQZBYNULYCYOPFYNCBUMYNBUNRHUOJYOHPAURHUPUSUTAYLQZYKYLYQXOY
      FYJYQYNCBVAZCXNVBZQZYNXNBVAXOAYTYLAYRYSAYPYRFYNCBVCZVDACDVEKJZYSECDXNXNVF
      ZVGVDVHSYNCXNBWBXNHBVIRYQYBGYEYQXPYEJZXPNLMZJZYBYLUUDUUFVJAYLYEUUEXPYLYEN
      TOIUUEYLYDTNOYLYDHLUHITYCHLUHVKVLVMZVNVOVMVPVQXPNPZXPLPZVRYQYBUUFUUHYQYBW
      MUUIYQYBUUHYHLBKZMZYAJZAUULYLAUUBYPQZUULYHTBKZMZYAJZUUJUUNMZYAJZUKZUULAUU
      BYPEFVHZCYABDXNUUCYAVFZVSZUULUUPUURVTRSUUHXTUUKYAUUHXQYHXSUUJXPNBWABXPWCW
      DWEWFYQYBUUIUURAUURYLAUUMUUSUURUUTUVBUULUUPUURWGRSUUIXTUUQYAUUIXQUUJXSUUN
      XPLBWAUUIXRTBUUIXRLLUEITXPLLUEVKWHVMWIWDWEWFWJXPNLWKWNWLWOYQYIUUNYHMZYAYQ
      YGUUNYHYQYGYDBKZUUNYQBWPJZYGUVDPAUVEYLAYPYRYNWPJZQUVEFYPYRUVFUUAYPNHOWQVH
      YNCWPBWRRSBWPWSVDYLUVDUUNPAYLYDTBUUGWIVQUTWTAUVCYAJZYLAUUMUUSUVGUUTUVBUUP
      UULUVGUURUUPUVGUUOUVCYAYHUUNXEXAXBXCRSXDXFAYLXGVHXHHXIJXMYMVJAXJGYADHXNBU
      UCUVAXKUSXL $.
  $}

  ${
    $d F x $.  $d G x $.  $d P x $.
    $( Lemma for ~ cycl3grtri .  (Contributed by AV, 5-Oct-2025.) $)
    cycl3grtrilem $p |- ( ( ( G e. UPGraph /\ F ( Paths ` G ) P )
                        /\ ( ( P ` 0 ) = ( P ` ( # ` F ) ) /\ ( # ` F ) = 3 ) )
                          -> ( { ( P ` 0 ) , ( P ` 1 ) } e. ( Edg ` G )
                            /\ { ( P ` 0 ) , ( P ` 2 ) } e. ( Edg ` G )
                            /\ { ( P ` 1 ) , ( P ` 2 ) } e. ( Edg ` G ) ) ) $=
      ( vx wcel cfv wa cc0 wceq c3 c1 caddc co cpr cfzo c2 eqtrdi adantl eleq1d
      fveq2 cupgr cpths wbr chash cv cedg wral w3a cwlks pthiswlk upgrwlkvtxedg
      eqid sylan2 adantr ctp oveq2 fzo0to3tp raleqdv wi eqeq2d c0ex 1ex fv0p1e1
      preq12d oveq1 1p1e2 fveq2d 2p1e3 raltp simpr1 preq2 prcom eqtr3di biimpcd
      2ex 3ad2ant3 impcom simpr2 3jca ex biimtrid biimtrdi sylbid mpd ) CUAEZBA
      CUBFUCZGZHAFZBUDFZAFZIZWIJIZGZGZDUEZAFZWOKLMZAFZNZCUFFZEZDHWIOMZUGZWHKAFZ
      NZWTEZWHPAFZNZWTEZXDXGNZWTEZUHZWGXCWMWFWEBACUIFUCXCABCUJADWTBCWTULUKUMUNW
      NXCXADHKPUOZUGZXLWNXADXBXMWMXBXMIZWGWLXOWKWLXBHJOMXMWIJHOUPUQQRRURWMXNXLU
      SZWGWLWKXPWLWKWHJAFZIZXPWLWJXQWHWIJATUTXNXFXKXGXQNZWTEZUHZXRXLXAXFXKXTDHK
      PVAVBVOWOHIZWSXEWTYBWPWHWRXDWOHATAWOVCVDSWOKIZWSXJWTYCWPXDWRXGWOKATYCWQPA
      YCWQKKLMPWOKKLVEVFQVGVDSWOPIZWSXSWTYDWPXGWRXQWOPATYDWQJAYDWQPKLMJWOPKLVEV
      HQVGVDSVIXRYAXLXRYAGXFXIXKXRXFXKXTVJYAXRXIXTXFXRXIUSXKXRXTXIXRXSXHWTXRXGW
      HNXSXHWHXQXGVKXGWHVLVMSVNVPVQXRXFXKXTVRVSVTWAWBVQRWCWD $.
  $}

  ${
    $d G x y z $.  $d P x y z $.
    cycl3grtri.g $e |- ( ph -> G e. UPGraph ) $.
    cycl3grtri.c $e |- ( ph -> F ( Cycles ` G ) P ) $.
    cycl3grtri.n $e |- ( ph -> ( # ` F ) = 3 ) $.
    $( The vertices of a cycle of size 3 are a triangle in a graph.
       (Contributed by AV, 5-Oct-2025.) $)
    cycl3grtri $p |- ( ph -> ran P e. ( GrTriangles ` G ) ) $=
      ( cfv c3 wceq wbr wcel cc0 wi cpr w3a c1 c2 eleq1d adantl vx vy vz ccycls
      chash crn cgrtri cpths wa cyclprop cv ctp cedg cvtx tpeq1 eqeq2d 3anbi12d
      wrex preq1 3anbi13d tpeq2 preq2 tpeq3 3anbi23d cwlks cfz co pthiswlk eqid
      wf wlkp simpl 3nn0 0elfz ax-mp oveq2 eleqtrrid ad2antll ffvelcdmd ex 3syl
      cn0 imp cle 1nn0 1le3 elfz2nn0 mpbir3an 2nn0 2re 3re 2lt3 ltleii cima csn
      cun cdm fdm cfzo elnn0uz mpbi fzisfzounsn fzo0to3tp uneq1i eqtri sylan9eq
      cuz eqtrdi imaeq2d imadmrn imaundi 3eqtr3g wfn ffn adantr fnimatpd nn0fz0
      fnsnfv syl2an eqcomd uneq12d fveq2 sneq eqcoms uneq2d wss snsstp1 ssequn2
      a1i sylib eqtrd biimtrdi impcom 3eqtrd mpbiri ad2antrr cyclnumvtx syl2anc
      breq2 cupgr cycl3grtrilem 3jca 3rspcedvdw sylibr exp32 com23 expcom com24
      sylanl1 isgrtri syl com13 mp2d ) ACUEHZIJZCBDUDHKZBUFZDUGHLZGFUUPUUOAUURU
      UPCBDUHHKZMBHZUUNBHZJZUIUUOAUURNNZBCDUJUUSUVBUVCUUSAUUOUVBUURAUUSUUOUVBUU
      RNNAUUSUIZUVBUUOUURUVDUVBUUOUURUVDUVBUUOUIZUIZUUQUAUKZUBUKZUCUKZULZJZUUQU
      EHZIJZUVGUVHOZDUMHZLZUVGUVIOZUVOLZUVHUVIOZUVOLZPZPZUCDUNHZURUBUWCURUAUWCU
      RUURUVFUWBUUQUUTUVHUVIULZJZUVMUUTUVHOZUVOLZUUTUVIOZUVOLZUVTPZPUUQUUTQBHZU
      VIULZJZUVMUUTUWKOZUVOLZUWIUWKUVIOZUVOLZPZPUUQUUTUWKRBHZULZJZUVMUWOUUTUWSO
      ZUVOLZUWKUWSOZUVOLZPZPUAUBUCUUTUWKUWSUWCUWCUWCUVGUUTJZUVKUWEUWAUWJUVMUXGU
      VJUWDUUQUVGUUTUVHUVIUOUPUXGUVPUWGUVRUWIUVTUXGUVNUWFUVOUVGUUTUVHUSSUXGUVQU
      WHUVOUVGUUTUVIUSSUQUTUVHUWKJZUWEUWMUWJUWRUVMUXHUWDUWLUUQUVHUWKUUTUVIVAUPU
      XHUWGUWOUVTUWQUWIUXHUWFUWNUVOUVHUWKUUTVBSUXHUVSUWPUVOUVHUWKUVIUSSUTUTUVIU
      WSJZUWMUXAUWRUXFUVMUXIUWLUWTUUQUVIUWSUUTUWKVCUPUXIUWIUXCUWQUXEUWOUXIUWHUX
      BUVOUVIUWSUUTVBSUXIUWPUXDUVOUVIUWSUWKVBSVDUTUVDUVEUUTUWCLZUUSUVEUXJNZAUUS
      CBDVEHKZMUUNVFVGZUWCBVJZUXKBCDVHZBCDUWCUWCVIZVKZUXNUVEUXJUXNUVEUIZUXMUWCM
      BUXNUVEVLZUUOMUXMLUXNUVBUUOMMIVFVGZUXMIWBLZMUXTLVMIVNVOUUNIMVFVPZVQVRZVSV
      TWATWCUVDUVEUWKUWCLZUUSUVEUYDNZAUUSUXLUXNUYEUXOUXQUXNUVEUYDUXRUXMUWCQBUXS
      UUOQUXMLUXNUVBUUOQUXTUXMQUXTLQWBLUYAQIWDKZWEVMWFQIWGWHUYBVQVRZVSVTWATWCUV
      DUVEUWSUWCLZUUSUVEUYHNZAUUSUXLUXNUYIUXOUXQUXNUVEUYHUXRUXMUWCRBUXSUUORUXML
      UXNUVBUUORUXTUXMRUXTLRWBLUYARIWDKWIVMRIWJWKWLWMRIWGWHUYBVQVRZVSVTWATWCUVF
      UXAUVMUXFUVDUVEUXAUUSUVEUXANZAUUSUXLUXNUYKUXOUXQUXNUVEUXAUXRUUQBMQRULZWNZ
      BIWOZWNZWPZUWTIBHZWOZWPZUWTUXRBBWQZWNBUYLUYNWPZWNUUQUYPUXRUYTVUABUXNUVEUY
      TUXMVUAUXMUWCBWRUUOUXMVUAJUVBUUOUXMUXTVUAUYBUXTMIWSVGZUYNWPZVUAIMXGHLZUXT
      VUCJUYAVUDVMIWTXAMIXBVOVUBUYLUYNXCXDXEXHTXFXIBXJBUYLUYNXKXLUXRUYMUWTUYOUY
      RUXRMQRUXMBUXNBUXMXMZUVEUXMUWCBXNZXOUYCUYGUYJXPUXRUYRUYOUXNVUEIUXMLZUYRUY
      OJUVEVUFUUOVUGUVBUUOIUXTUXMUYAIUXTLVMIXQXAUYBVQTUXMIBXRXSXTYAUVEUYSUWTJZU
      XNUUOUVBVUHUUOUVBUUTUYQJZVUHUUOUVAUYQUUTUUNIBYBUPVUIUYSUWTUUTWOZWPZUWTVUI
      UYRVUJUWTUYRVUJJUYQUUTUYQUUTYCYDYEVUIVUJUWTYFZVUKUWTJVULVUIUUTUWKUWSYGYIV
      UJUWTYHYJYKYLYMTYNVTWATWCUVFUVLUUNIUVFQUUNWDKZUUPUVLUUNJUUOVUMUVDUVBUUOVU
      MUYFWFUUNIQWDYSYOVRAUUPUUSUVEFYPBCDYQYRAUUOUUSUVEGYPYKADYTLUUSUVEUXFEBCDU
      UAUUIUUBUUCUAUBUCUUQUVODUWCUXPUVOVIUUJUUDUUEUUFUUGUUHWCUUKUULUUM $.
  $}

  $( Conditions for mapping triangles onto triangles.  Lemma for ~ grimgrtri
     and ~ grlimgrtri .  (Contributed by AV, 23-Aug-2025.) $)
  grtrimap $p |- ( F : V -1-1-> W -> ( ( ( a e. V /\ b e. V /\ c e. V )
                                    /\ ( T = { a , b , c } /\ ( # ` T ) = 3 ) )
                    -> ( ( ( F ` a ) e. W /\ ( F ` b ) e. W /\ ( F ` c ) e. W )
                         /\ ( F " T ) = { ( F ` a ) , ( F ` b ) , ( F ` c ) }
                         /\ ( # ` ( F " T ) ) = 3 ) ) ) $=
    ( cv wcel w3a ctp wceq cfv c3 wa ffvelcdmda ex ad2antrl adantl cvv wf1 cima
    chash f1f 3anim123d adantrd imp imaeq2 f1fn adantr simprl1 simprl2 fnimatpd
    wfn simprl3 eqtrd wss simpl tpssi wb sseq1 mpbird tpex eleq1 mpbiri cen wbr
    f1imaeng hasheni syl eqcomd syl3anc simprrr eqtr3d 3jca ) CDBUAZEHZCIZFHZCI
    ZGHZCIZJZAVQVSWAKZLZAUCMZNLZOZOZVQBMZDIZVSBMZDIZWABMZDIZJZBAUBZWJWLWNKZLZWQ
    UCMZNLZJVPWIOZWPWSXAVPWIWPVPWCWPWHVPVRWKVTWMWBWOVPVRWKVPCDVQBCDBUDZPQVPVTWM
    VPCDVSBXCPQVPWBWOVPCDWABXCPQUEUFUGXBWQBWDUBZWRWIWQXDLZVPWEXEWCWGAWDBUHRSXBV
    QVSWACBVPBCUNWICDBUIUJVRVTWBWHVPUKVRVTWBWHVPULVRVTWBWHVPUOUMUPXBWFWTNXBVPAC
    UQZATIZWFWTLVPWIURWIXFVPWIXFWDCUQZWCXHWHVQVSWACUSUJWEXFXHUTWCWGAWDCVARVBSWI
    XGVPWEXGWCWGWEXGWDTIVQVSWAVCAWDTVDVERSVPXFXGJZWTWFXIWQAVFVGWTWFLCDABTVHWQAV
    IVJVKVLVPWCWEWGVMVNVOQ $.

  ${
    $d F a b c x y z $.  $d G a b c $.  $d H a b c x y z $.
    $d T a b c x y z $.  $d a b c ph $.
    grimgrtri.g $e |- ( ph -> G e. UHGraph ) $.
    grimgrtri.h $e |- ( ph -> H e. UHGraph ) $.
    grimgrtri.n $e |- ( ph -> F e. ( G GraphIso H ) ) $.
    grimgrtri.t $e |- ( ph -> T e. ( GrTriangles ` G ) ) $.
    $( Graph isomorphisms map triangles onto triangles.  (Contributed by AV,
       27-Jul-2025.)  (Proof shortened by AV, 24-Aug-2025.) $)
    grimgrtri $p |- ( ph -> ( F " T ) e. ( GrTriangles ` H ) ) $=
      ( va cv wceq cfv cpr wcel w3a wrex wa wi eleq1d vx vy vz vb vc cima chash
      ctp c3 cedg cvtx cgrtri eqid grtriprop syl wf1 cgrim co wf1o grimf1o 3syl
      f1of1 ad3antrrr adantr simprr simplr 3jca 3simpa adantl grtrimap syl12anc
      simplrl imp cuhgr wss grimedg 3anbi123d wfn f1ofn simprll simprlr fnimapr
      simpl syl3anc biimpd adantrd 3anim123d ex com23 3ad2ant3 sylbid 2a1d impl
      3impd tpeq1 eqeq2d preq1 3anbi12d 3anbi13d tpeq2 preq2 tpeq3 rspc3ev 3imp
      3anbi23d 3exp2 sylc rexlimdva2 rexlimdvva mpd isgrtri sylibr ) ACBUFZUAKZ
      UBKZUCKZUHZLZXMUGMUILZXNXONZEUJMZOZXNXPNZYAOZXOXPNZYAOZPZPZUCEUKMZQUBYIQU
      AYIQZXMEULMOABJKZUDKZUEKZUHLZBUGMUILZYKYLNZDUJMZOZYKYMNZYQOZYLYMNZYQOZPZP
      ZUEDUKMZQZUDUUEQJUUEQZYJABDULMOUUGIJUDUEBYQDUUEUUEUMZYQUMZUNUOAUUFYJJUDUU
      EUUEAYKUUEOZYLUUEOZRZRZUUDYJUEUUEUUMYMUUEOZRZUUDRZYKCMZYIOYLCMZYIOYMCMZYI
      OPZXMUUQUURUUSUHZLZXSPZUUQUURNZYAOZUUQUUSNZYAOZUURUUSNZYAOZPZYJUUPUUEYICU
      PZUUJUUKUUNPZYNYORZUVCAUVKUULUUNUUDACDEUQUROZUUEYICUSZUVKHCDEUUEYIUUHYIUM
      ZUTZUUEYICVBVAVCUUPUUJUUKUUNUUOUUJUUDAUUJUUKUUNVLVDUUOUUKUUDUUMUUKUUNAUUJ
      UUKVEVDVDUUMUUNUUDVFVGUUDUVMUUOYNYOUUCVHVIUVKUVLUVMRUVCBCUUEYIJUDUEVJVMVK
      UUOUUDUVJAUULUUNUUDUVJSZADVNOZEVNOZUVNUULUUNRZUVRSFGHUVSUVTUVNPZUUDUWAUVJ
      UWBYNYOUUCUWAUVJSZUWBUUCUWCSYNYOUWBUUCCYPUFZYAOZYPUUEVOZRZCYSUFZYAOZYSUUE
      VOZRZCUUAUFZYAOZUUAUUEVOZRZPZUWCUWBYRUWGYTUWKUUBUWOYACDEYQYPUUEUUHUUIYAUM
      ZVPYACDEYQYSUUEUUHUUIUWQVPYACDEYQUUAUUEUUHUUIUWQVPVQUVNUVSUWPUWCSZUVTUVNU
      VOCUUEVRZUWRUVQUUEYICVSUWSUWAUWPUVJUWSUWAUWPUVJSUWSUWARZUWGUVEUWKUVGUWOUV
      IUWTUWEUVEUWFUWTUWEUVEUWTUWDUVDYAUWTUWSUUJUUKUWDUVDLUWSUWAWCZUWSUUJUUKUUN
      VTZUWSUUJUUKUUNWAZUUEYKYLCWBWDTWEWFUWTUWIUVGUWJUWTUWIUVGUWTUWHUVFYAUWTUWS
      UUJUUNUWHUVFLUXAUXBUWSUULUUNVEZUUEYKYMCWBWDTWEWFUWTUWMUVIUWNUWTUWMUVIUWTU
      WLUVHYAUWTUWSUUKUUNUWLUVHLUXAUXCUXDUUEYLYMCWBWDTWEWFWGWHWIVAWJWKWLWNWIWDW
      MVMUUTUVBXSUVJYJSUUTUVBXSUVJYJYHUVBXSUVJPXMUUQXOXPUHZLZXSUUQXONZYAOZUUQXP
      NZYAOZYFPZPXMUUQUURXPUHZLZXSUVEUXJUURXPNZYAOZPZPUAUBUCUUQUURUUSYIYIYIXNUU
      QLZXRUXFYGUXKXSUXQXQUXEXMXNUUQXOXPWOWPUXQYBUXHYDUXJYFUXQXTUXGYAXNUUQXOWQT
      UXQYCUXIYAXNUUQXPWQTWRWSXOUURLZUXFUXMUXKUXPXSUXRUXEUXLXMXOUURUUQXPWTWPUXR
      UXHUVEYFUXOUXJUXRUXGUVDYAXOUURUUQXATUXRYEUXNYAXOUURXPWQTWSWSXPUUSLZUXMUVB
      UXPUVJXSUXSUXLUVAXMXPUUSUUQUURXBWPUXSUXJUVGUXOUVIUVEUXSUXIUVFYAXPUUSUUQXA
      TUXSUXNUVHYAXPUUSUURXATXEWSXCXFXDXGXHXIXJUAUBUCXMYAEYIUVPUWQXKXL $.
  $}

  ${
    $d E a b c t y z $.  $d G a b c t y z $.  $d N b c t y z $.
    $d V a b c t y z $.
    usgrgrtrirex.v $e |- V = ( Vtx ` G ) $.
    usgrgrtrirex.e $e |- E = ( Edg ` G ) $.
    usgrgrtrirex.n $e |- N = ( G NeighbVtx a ) $.
    $( Conditions for a simple graph to contain a triangle.  (Contributed by
       AV, 7-Aug-2025.) $)
    usgrgrtrirex $p |- ( G e. USGraph -> ( E. t t e. ( GrTriangles ` G )
                                           <-> E. a e. V E. b e. N E. c e. N
                                           ( b =/= c /\ { b , c } e. E ) ) ) $=
      ( vy vz wcel wceq cpr w3a wrex wa cvv cv cgrtri cfv wex ctp chash isgrtri
      c3 cusgr wne exbii rexcom4 wi wb fveqeq2 adantl neeq1 preq1 anbi12d neeq2
      eleq1d preq2 cnbgr prcom eleq1i nbusgreledg biimprcd sylbi 3ad2ant1 com12
      adantr a1d 3imp eleqtrrdi 3ad2ant2 hashtpg bicomd el3v simp2bi simp33 jca
      co 2rspcedvdw 3exp sylbid 3impd rexlimdvva exlimdv eleq2i bitrid tpex a1i
      tpeq2 eqeq2d 3anbi13d tpeq3 3anbi23d cvtx cuhgr usgruhgr birani vex prid1
      ex uhgredgrnv syl3an bilani eqidd usgredgne necomd ad2ant2r 3adant3 simpl
      cedg 3ad2ant3 ad2ant2rl sylib simpr eqeq1 3anbi12d 2rexbidv spcedv impbid
      3jca rexlimdvv rexbidva bitr3id ) AUAZCUBUCNZAUDYHFUAZLUAZMUAZUEZOZYHUFUC
      UHOZYJYKPZBNZYJYLPZBNZYKYLPZBNZQZQZMERLERZFERZAUDZCUINZGUAZHUAZUJZUUHUUIP
      ZBNZSZHDRGDRZFERZYIUUEAFLMYHBCEIJUGUKUUFUUDAUDZFERUUGUUOUUDFAEULUUGUUPUUN
      FEUUGYJENZSZUUPUUNUURUUDUUNAUURUUCUUNLMEEUURYKENYLENSZSZYNYOUUBUUNUUTYNYO
      UUBUUNUMZUMUUTYNSYOYMUFUCUHOZUVAYNYOUVBUNUUTYHYMUHUFUOUPUUTUVBUVAUMYNUUTU
      VBUUBUUNUUTUVBUUBQZUUMYKUUIUJZYKUUIPZBNZSYKYLUJZUUASGHYKYLDDUUHYKOZUUJUVD
      UULUVFUUHYKUUIUQUVHUUKUVEBUUHYKUUIURVAUSUUIYLOZUVDUVGUVFUUAUUIYLYKUTUVIUV
      EYTBUUIYLYKVBVAUSUVCYKCYJVCWBZDUUTUVBUUBYKUVJNZUUTUUBUVKUMZUVBUURUVLUUSUU
      GUVLUUQUUBUUGUVKYQYSUUGUVKUMZUUAYQYKYJPZBNZUVMYPUVNBYJYKVDVEUUGUVKUVOBCYJ
      YKJVFVGVHVIVJVKVKVLVMKVNUVCYLUVJDUUTUVBUUBYLUVJNZUUTUUBUVPUMZUVBUURUVQUUS
      UUGUVQUUQUUBUUGUVPYSYQUUGUVPUMZUUAYSYLYJPZBNZUVRYRUVSBYJYLVDVEUUGUVPUVTBC
      YJYLJVFVGVHVOVJVKVKVLVMKVNUVCUVGUUAUVBUUTUVGUUBUVBYJYKUJZUVGYLYJUJZUVBUWA
      UVGUWBQZUNFLMYJTNYKTNYLTNQUWCUVBYJYKYLTTTVPVQVRVSVOUUTUVBYQYSUUAVTWAWCWDV
      KWEXDWFWGWHUURUUMUUPGHDDUURUUHDNZUUIDNZSZUUHYJPZBNZUUIYJPZBNZSZUUMUUPUMUU
      GUWFUWKUNUUQUUGUWDUWHUWEUWJUWDUUHUVJNUUGUWHDUVJUUHKWIBCYJUUHJVFWJUWEUUIUV
      JNUUGUWJDUVJUUIKWIBCYJUUIJVFWJUSVKUURUWKUUMUUPUURUWKUUMQZUUDYJUUHUUIUEZYM
      OZUWMUFUCUHOZUUBQZMERLERATUWMUWMTNUWLYJUUHUUIWKWLUWLUWPUWMYJUUHYLUEZOZUWO
      YJUUHPZBNZYSUUHYLPZBNZQZQUWMUWMOZUWOUWTYJUUIPZBNZUULQZQLMUUHUUIEEYKUUHOZU
      WNUWRUUBUXCUWOUXHYMUWQUWMYKUUHYJYLWMWNUXHYQUWTUUAUXBYSUXHYPUWSBYKUUHYJVBV
      AUXHYTUXABYKUUHYLURVAWOWOYLUUIOZUWRUXDUXCUXGUWOUXIUWQUWMUWMYLUUIYJUUHWPWN
      UXIYSUXFUXBUULUWTUXIYRUXEBYLUUIYJVBVAUXIUXAUUKBYLUUIUUHVBVAWQWOUWLUUHCWRU
      CZEUURCWSNZUWKUWGCXNUCZNZUUMUUHUWGNZUUHUXJNUUGUXKUUQCWTVKZUWHUXMUWJBUXLUW
      GJWIXAUXNUUMUUHYJGXBXCWLUWGCUUHXEXFIVNUWLUUIUXJEUURUXKUWKUWIUXLNZUUMUUIUW
      INZUUIUXJNUXOUWJUXPUWHBUXLUWIJWIXGUXQUUMUUIYJHXBXCWLUWICUUIXEXFIVNUWLUXDU
      WOUXGUWLUWMXHUWLYJUUHUJZUUJUUIYJUJZQZUWOUWLUXRUUJUXSUURUWKUXRUUMUUGUWHUXR
      UUQUWJUUGUWHSUUHYJBCUUHYJJXIXJXKXLUUMUURUUJUWKUUJUULXMXOUURUWKUXSUUMUUGUW
      JUXSUUQUWHBCUUIYJJXIXPXLYDUXTUWOUNFGHYJUUHUUITTTVPVRXQUWLUWTUXFUULUWKUURU
      WTUUMUWHUWTUWJUWGUWSBUUHYJVDVEXAVOUWKUURUXFUUMUWJUXFUWHUWIUXEBUUIYJVDVEXG
      VOUUMUURUULUWKUUJUULXRXOYDYDWCYHUWMOZUUCUWPLMEEUYAYNUWNYOUWOUUBYHUWMYMXSY
      HUWMUHUFUOXTYAYBWDWEYEYCYFYGWJ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Star graphs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

   According to Wikipedia "Star (graph theory)", 10-Sep-2025,
   ~ https://en.wikipedia.org/wiki/Star_(graph_theory) : "In graph theory, the
   star S_k is the complete bipartite graph K(1,k), that is, it is a tree with
   one internal node and k leaves.  Alternatively, some authors define S_k to
   be the tree of order k with maximum diameter 2, in which case a star of
   k > 2 has k - 1 leaves.".

$)

  $c StarGr $.

  $( Extend class notation with star graphs. $)
  cstgr $a class StarGr $.

  ${
    $d e n x $.
    $( Definition of star graphs according to the first definition in
       Wikipedia, so that ` ( StarGr `` N ) ` has size ` N ` , and order
       ` N + 1 ` : ` ( StarGr `` 0 ) ` will be a single vertex (graph without
       edges), see ~ stgr0 , ` ( StarGr `` 1 ) ` will be a single edge (graph
       with two vertices connected by an edge), see ~ stgr1 , and
       ` ( StarGr `` 3 ) ` will be a 3-star or "claw" (a star with 3 edges).
       (Contributed by AV, 10-Sep-2025.) $)
    df-stgr $a |- StarGr = ( n e. NN0
                       |-> { <. ( Base ` ndx ) , ( 0 ... n ) >. ,
                             <. ( .ef ` ndx ) , ( _I |` { e e. ~P ( 0 ... n ) |
                                E. x e. ( 1 ... n ) e = { 0 , x } } ) >. } ) $.
  $}

  ${
    $d N e n x $.
    $( The star graph S_N. (Contributed by AV, 10-Sep-2025.) $)
    stgrfv $p |- ( N e. NN0 -> ( StarGr ` N )
                         = { <. ( Base ` ndx ) , ( 0 ... N ) >. ,
                             <. ( .ef ` ndx ) , ( _I |` { e e. ~P ( 0 ... N ) |
                                E. x e. ( 1 ... N ) e = { 0 , x } } ) >. } ) $=
      ( vn cn0 wcel cnx cfv cc0 cv cfz co cop cid cpr wceq c1 wrex cpw crab cbs
      cedgf cres cstgr cvv df-stgr oveq2 opeq2d pweqd rexeqdv rabeqbidv reseq2d
      cmpt a1i preq12d adantl id prex fvmptd ) CEFZDCGUAHZIDJZKLZMZGUBHZNBJIAJO
      PZAQVBKLZRZBVCSZTZUCZMZOZVAICKLZMZVENVFAQCKLZRZBVNSZTZUCZMZOZEUDUEUDDEVMU
      MPUTABDUFUNVBCPZVMWBPUTWCVDVOVLWAWCVCVNVAVBCIKUGZUHWCVKVTVEWCVJVSNWCVHVQB
      VIVRWCVCVNWDUIWCVFAVGVPVBCQKUGUJUKULUHUOUPUTUQWBUEFUTVOWAURUNUS $.
  $}

  ${
    $d N e x $.
    $( The vertices of the star graph S_N. (Contributed by AV, 11-Sep-2025.) $)
    stgrvtx $p |- ( N e. NN0 -> ( Vtx ` ( StarGr ` N ) ) = ( 0 ... N ) ) $=
      ( ve vx cn0 wcel cstgr cfv cvtx cnx cbs cc0 cfz co cop cedgf cpr wceq cvv
      cv eqid cid c1 wrex cpw crab cres stgrfv fveq2d ovex pwexg rabexd resiexd
      wa ax-mp pm3.2i struct2grvtx mp1i eqtrd ) ADEZAFGZHGIJGKALMZNIOGUABSKCSPQ
      CUBALMUCZBVAUDZUEZUFZNPZHGZVAUSUTVFHCBAUGUHVAREZVEREZUMVGVAQUSVHVIKALUIZV
      HVIVJVHVDRVHVBBVCVDRVDTVARUJUKULUNUOVEVFVARRVFTUPUQUR $.

    $( The indexed edges of the star graph S_N. (Contributed by AV,
       11-Sep-2025.) $)
    stgriedg $p |- ( N e. NN0 -> ( iEdg ` ( StarGr ` N ) )
                             = ( _I |` { e e. ~P ( 0 ... N ) |
                                    E. x e. ( 1 ... N ) e = { 0 , x } } ) ) $=
      ( cn0 wcel cstgr cfv ciedg cnx cbs cc0 cfz co cop cedgf cpr wceq cvv eqid
      cv cid c1 wrex crab cres stgrfv fveq2d wa ovex pwexg rabexd resiexd ax-mp
      cpw pm3.2i struct2griedg mp1i eqtrd ) CDEZCFGZHGIJGKCLMZNIOGUABTKATPQAUBC
      LMUCZBVAUNZUDZUEZNPZHGZVEUSUTVFHABCUFUGVAREZVEREZUHVGVEQUSVHVIKCLUIZVHVIV
      JVHVDRVHVBBVCVDRVDSVARUJUKULUMUOVEVFVARRVFSUPUQUR $.

    $( The edges of the star graph S_N. (Contributed by AV, 11-Sep-2025.) $)
    stgredg $p |- ( N e. NN0 -> ( Edg ` ( StarGr ` N ) )
            = { e e. ~P ( 0 ... N ) | E. x e. ( 1 ... N ) e = { 0 , x } } ) $=
      ( cn0 wcel cstgr cfv cedg ciedg crn cv cc0 cpr wceq c1 cfz wrex cpw crab
      co edgval cid cres stgriedg rneqd rnresi eqtrdi eqtrid ) CDEZCFGZHGUJIGZJ
      ZBKLAKMNAOCPTQBLCPTRSZUJUAUIULUBUMUCZJUMUIUKUNABCUDUEUMUFUGUH $.

    $d E e x $.
    $( An edge of the star graph S_N. (Contributed by AV, 11-Sep-2025.) $)
    stgredgel $p |- ( N e. NN0 -> ( E e. ( Edg ` ( StarGr ` N ) )
           <-> ( E C_ ( 0 ... N ) /\ E. x e. ( 1 ... N ) E = { 0 , x } ) ) ) $=
      ( ve cn0 wcel cstgr cfv cedg cv cc0 cpr wceq c1 cfz co wrex cpw crab cvv
      wss wa stgredg eleq2d eqeq1 rexbidv elrab wb wi prex eleq1 mpbiri syl a1i
      elpwg rexlimiv bianim bitrdi ) CEFZBCGHIHZFBDJZKAJZLZMZANCOPZQZDKCOPZRZSZ
      FZBVGUAZBVCMZAVEQZUBUSUTVIBADCUCUDVJBVHFZVMVKVFVMDBVHVABMVDVLAVEVABVCUEUF
      UGVLVNVKUHZAVEVLVOUIVBVEFVLBTFZVOVLVPVCTFKVBUJBVCTUKULBVGTUOUMUNUPUQUR $.

    $( The edges of the star graph S_N as indexed union.  (Contributed by AV,
       29-Sep-2025.) $)
    stgredgiun $p |- ( N e. NN0 -> ( Edg ` ( StarGr ` N ) )
                                    = U_ x e. ( 1 ... N ) { { 0 , x } } ) $=
      ( ve cn0 wcel cstgr cfv cedg c1 cfz co cc0 cv cpr csn wss wrex wa wb a1i
      ciun stgredgel eliun velsn 0elfz adantr fz1ssfz0 sseli adantl prssd sseq1
      wceq syl5ibrcom pm4.71rd bitr2id rexbidva r19.42v 3bitr2rd bitrd eqrdv )
      BDEZCBFGHGZAIBJKZLAMZNZOZUAZVACMZVBEVHLBJKZPZVHVEULZAVCQRZVHVGEZAVHBUBVAV
      MVHVFEZAVCQZVJVKRZAVCQZVLVMVOSVAAVHVCVFUCTVAVPVNAVCVNVKVAVDVCEZRZVPCVEUDV
      SVKVJVSVJVKVEVIPVSLVDVIVALVIEVRBUEUFVRVDVIEVAVCVIVDBUGUHUIUJVHVEVIUKUMUNU
      OUPVQVLSVAVJVKAVCUQTURUSUT $.
  $}

  ${
    $d N e k x $.
    $( The star graph S_N is a simple graph.  (Contributed by AV,
       11-Sep-2025.) $)
    stgrusgra $p |- ( N e. NN0 -> ( StarGr ` N ) e. USGraph ) $=
      ( ve vx vk wcel cstgr cfv cdm cv chash wceq cpw crab wf1 cc0 cfz mp1i cvv
      c2 wa cn0 cusgr ciedg cvtx cpr c1 co wrex cid cres wss wf1o f1of1 simpllr
      f1oi fveq2 wne 0red elfznn nngt0d ltned wb c0ex vex pm3.2i hashprg adantl
      mpbid sylan9eqr jca rexlimdva expimpd eqeq1 rexbidv elrab fveqeq2 3imtr4g
      weq ssrdv f1ss syl2anc stgriedg dmeqd dmresi eqtrdi stgrvtx pweqd rabeqdv
      ex f1eq123d mpbird fvex eqid isusgrs ) AUAEZAFGZUBEZWPUCGZHZBIZJGSKZBWPUD
      GZLZMZWRNZWOXEWTOCIZUEZKZCUFAPUGZUHZBOAPUGZLZMZXABXLMZUIXMUJZNZWOXMXMXONZ
      XMXNUKXPXMXMXOULXQWOXMUOXMXMXOUMQWODXMXNWODIZXLEZXRXGKZCXIUHZTXSXRJGZSKZT
      ZXRXMEXRXNEWOXSYAYDWOXSTZXTYDCXIYEXFXIEZTZXTYDYGXTTXSYCWOXSYFXTUNXTYGYBXG
      JGZSXRXGJUPYFYHSKZYEYFOXFUQZYIYFOXFYFURYFXFXFAUSUTVAOREZXFREZTYJYIVBYFYKY
      LVCCVDVEOXFRRVFQVHVGVIVJWIVKVLXJYABXRXLBDVRXHXTCXIWTXRXGVMVNVOXAYCBXRXLWT
      XRSJVPVOVQVSXMXMXNXOVTWAWOWSXMXDXNWRXOCBAWBZWOWSXOHXMWOWRXOYMWCXMWDWEWOXA
      BXCXLWOXBXKAWFWGWHWJWKWPREWQXEVBWOAFWLBRWRWPXBXBWMWRWMWNQWK $.
  $}

  ${
    $d e x $.
    $( The star graph S_0 consists of a single vertex without edges.
       (Contributed by AV, 11-Sep-2025.) $)
    stgr0 $p |- ( StarGr ` 0 ) = { <. ( Base ` ndx ) , { 0 } >. ,
                                   <. ( .ef ` ndx ) , (/) >. } $=
      ( ve vx cc0 cstgr cfv cnx cbs cfz co cop cid cv cpr wceq cres wcel opeq2i
      c0 wn eqtri cedgf c1 wrex cpw crab csn cn0 0nn0 stgrfv ax-mp fz0sn rabeq0
      wral wi noel pm2.21i fz10 eleq2s a1i ralrimiv ralnex mprgbir reseq2i res0
      sylib preq12i ) CDEZFGEZCCHIZJZFUAEZKALZCBLZMNZBUBCHIZUCZAVIUDZUEZOZJZMZV
      HCUFZJZVKRJZMCUGPVGWANUHBACUIUJVJWCVTWDVIWBVHUKQVSRVKVSKRORVRRKVRRNVPSZAV
      QVPAVQULVLVQPZVNSZBVOUMWEWFWGBVOVMVOPWGUNWFWGVMRVOVMRPWGVMUOUPUQURUSUTVNB
      VOVAVEVBVCKVDTQVFT $.

    $( The star graph S_1 consists of a single simple edge.  (Contributed by
       AV, 11-Sep-2025.) $)
    stgr1 $p |- ( StarGr ` 1 ) = { <. ( Base ` ndx ) , { 0 , 1 } >. ,
                             <. ( .ef ` ndx ) , ( _I |` { { 0 , 1 } } ) >. } $=
      ( ve vx c1 cfv cnx cc0 cfz co cop cid cpr wceq wrex cres csn ax-mp fz01pr
      cv wcel opeq2i cstgr cbs cedgf cpw crab cn0 1nn0 stgrfv wa wi elsni preq2
      cab eqeq2d biimpd syl cz 1z fzsn eleq2s rexlimiv 0elpr01 eleqtrri 1elpr01
      adantl prelpwi mp2an eqid rexeqi 1ex rexsn bitri mpbir pm3.2i eleq1 eqeq1
      rexbidv anbi12d mpbiri impbii abbii df-rab df-sn 3eqtr4i reseq2i preq12i
      eqtri ) CUADZEUBDZFCGHZIZEUCDZJARZFBRZKZLZBCCGHZMZAWJUDZUEZNZIZKZWIFCKZIZ
      WLJXDOZNZIZKCUFSWHXCLUGBACUHPWKXEXBXHWJXDWIQTXAXGWLWTXFJWMWSSZWRUIZAUMWMX
      DLZAUMWTXFXJXKAXJXKWRXKXIWPXKBWQWPXKUJZWNCOZWQWNXMSWNCLZXLWNCUKXNWPXKXNWO
      XDWMWNCFULZUNUOUPCUQSWQXMLURCUSPZUTVAVEXKXJXDWSSZXDWOLZBWQMZUIXQXSFWJSCWJ
      SXQFXDWJVBQVCCXDWJVDQVCFCWJVFVGXSXDXDLZXDVHXSXRBXMMXTXRBWQXMXPVIXRXTBCVJX
      NWOXDXDXOUNVKVLVMVNXKXIXQWRXSWMXDWSVOXKWPXRBWQWMXDWOVPVQVRVSVTWAWRAWSWBAX
      DWCWDWETWFWG $.
  $}

  ${
    stgrvtx0.g $e |- G = ( StarGr ` N ) $.
    stgrvtx0.v $e |- V = ( Vtx ` G ) $.
    $( The center ("internal node") of a star graph S_N. (Contributed by AV,
       12-Sep-2025.) $)
    stgrvtx0 $p |- ( N e. NN0 -> 0 e. V ) $=
      ( cn0 wcel cstgr cfv cvtx cc0 cfz co wceq fveq2i eqtri eqeq1i 0elfz eleq2
      stgrvtx syl5ibrcom biimtrrid mpd ) BFGZBHIZJIZKBLMZNZKCGZBTUHCUGNZUDUICUF
      UGCAJIUFEAUEJDOPQUDUIUJKUGGBRCUGKSUAUBUC $.

    $( The order of a star graph S_N. (Contributed by AV, 12-Sep-2025.) $)
    stgrorder $p |- ( N e. NN0 -> ( # ` V ) = ( N + 1 ) ) $=
      ( cn0 wcel chash cfv cc0 cfz co c1 caddc cstgr cvtx fveq2i stgrvtx eqtrid
      eqtri fveq2d hashfz0 eqtrd ) BFGZCHIJBKLZHIBMNLUDCUEHUDCBOIZPIZUECAPIUGEA
      UFPDQTBRSUABUBUC $.

    $d G e x $.  $d N e n x $.  $d V e n x $.
    $( All vertices of a star graph S_N except the center are in the (open)
       neighborhood of the center.  (Contributed by AV, 12-Sep-2025.) $)
    stgrnbgr0 $p |- ( N e. NN0 -> ( G NeighbVtx 0 ) = ( V \ { 0 } ) ) $=
      ( ve vx vn wcel cc0 co cv wa cedg cfv wrex cdif wceq cpr cvtx cn0 wel csn
      cnbgr crab stgrvtx0 eqid dfnbgr2 syl eleq2 anbi12d cfz wss 0elfz fz1ssfz0
      adantr cstgr fveq2i stgrvtx eqtrid difeq1d fz0dif1 eqimssd eqsstrd sselda
      c1 eqtri sselid prssd preq2 eqeq2d eqidd rspcedvdw wb stgredgel mpbir2and
      weq eleq2i bitrid prid2g adantl c0ex prid1 jctil rabeqcda eqtrd ) BUAIZAJ
      UDKZJFLZIZGFUBZMZFANOZPZGCJUCZQZUEZWPWGJCIWHWQRABCDEUFFGWMAJCEWMUGUHUIWGW
      NGWPWGGLZWPIZMZWLJJWRSZIZWRXAIZMFXAWMWIXARWJXBWKXCWIXAJUJWIXAWRUJUKWTXAWM
      IZXAJBULKZUMZXAJHLZSZRZHVFBULKZPZWTJWRXEWGJXEIWSBUNUPWTXJXEWRBUOWGWPXJWRW
      GWPXEWOQZXJWGCXEWOWGCBUQOZTOZXECATOXNEAXMTDURVGBUSUTVAWGXLXJBVBVCVDVEZVHV
      IWTXIXAXARHWRXJHGVQXHXAXAXGWRJVJVKXOWTXAVLVMXDXAXMNOZIZWTXFXKMZWMXPXAAXMN
      DURVRWGXQXRVNWSHXABVOUPVSVPWTXCXBWSXCWGJWRWPVTWAJWRWBWCWDVMWEWF $.

    $( All vertices of a star graph S_N are in the closed neighborhood of the
       center.  (Contributed by AV, 12-Sep-2025.) $)
    stgrclnbgr0 $p |- ( N e. NN0 -> ( G ClNeighbVtx 0 ) = V ) $=
      ( cn0 wcel cc0 cclnbgr co csn cnbgr cun cdif stgrvtx0 dfclnbgr4 stgrnbgr0
      wceq syl uneq2d wss snssd undif sylib 3eqtrd ) BFGZAHIJZHKZAHLJZMZUHCUHNZ
      MZCUFHCGUGUJRABCDEOZAHCEPSUFUIUKUHABCDEQTUFUHCUAULCRUFHCUMUBUHCUCUDUE $.
  $}

  ${
    isubgr3stgr.v $e |- V = ( Vtx ` G ) $.
    isubgr3stgr.u $e |- U = ( G NeighbVtx X ) $.
    isubgr3stgr.c $e |- C = ( G ClNeighbVtx X ) $.
    ${
      isubgr3stgr.f $e |- F = ( H u. { <. X , Y >. } ) $.
      $( Lemma 1 for ~ isubgr3stgr .  (Contributed by AV, 16-Sep-2025.) $)
      isubgr3stgrlem1 $p |- ( ( H : U -1-1-onto-> R /\ X e. V
                              /\ ( Y e. W /\ Y e/ R ) )
                            -> F : C -1-1-onto-> ( R u. { Y } ) ) $=
        ( wf1o wcel wnel wa csn cun w3a cnbgr co wceq wb f1oeq2 biimpi 3ad2ant1
        ax-mp anim2i 3adant1 nbgrnself2 a1i f1ounsn syl112anc cclnbgr dfclnbgr4
        simpl simp3r 3ad2ant2 uncom eqtrdi eqtrid f1oeq2d mpbird ) CBFOZIGPZJHP
        ZJBQZRZUAZABJSTZDOEIUBUCZISZTZVLDOZVKVMBFOZVGVHRZIVMQZVIVPVFVGVQVJVFVQC
        VMUDVFVQUELCVMBFUFUIUGUHVGVJVRVFVJVHVGVHVIURUJUKVSVKEIULUMVFVGVHVIUSVMB
        DFGHIJNUNUOVKAVOVLDVKAEIUPUCZVOMVKVTVNVMTZVOVGVFVTWAUDVJEIGKUQUTVNVMVAV
        BVCVDVE $.
    $}

    $d U f $.  $d W f $.
    isubgr3stgr.n $e |- N e. NN0 $.
    isubgr3stgr.s $e |- S = ( StarGr ` N ) $.
    isubgr3stgr.w $e |- W = ( Vtx ` S ) $.
    $( Lemma 2 for ~ isubgr3stgr .  (Contributed by AV, 16-Sep-2025.) $)
    isubgr3stgrlem2 $p |- ( ( G e. USGraph /\ X e. V /\ ( # ` U ) = N )
                            -> E. f f : U -1-1-onto-> ( W \ { 0 } ) ) $=
      ( c1 wceq wcel cn0 cvv chash cfv caddc co cusgr w3a cc0 csn cdif wf1o wex
      cv stgrorder ax-mp wa cmin oveq1 cc nn0cn pncan1 syl mp1i eqtrd peano2nn0
      adantr cfn eleq1 mpbiri wb cvtx hashclb mpbird stgrvtx0 hashdifsn sylancl
      fvexi simpr3 3eqtr4rd 3ad2ant3 cnbgr ovexi diffi hasheqf1o syl2an2 mpbid
      mpan ) HUAUBZFPUCUDZQZEUERZIGRZCUAUBZFQZUFZCHUGUHZUIZDULUJDUKZFSRZWIMBFHN
      OUMUNWIWNUOZWLWPUAUBZQZWQWSWGPUPUDZFWTWLWIXBFQWNWIXBWHPUPUDZFWGWHPUPUQWRX
      CFQZWIMWRFURRXDFUSFUTVAVBVCVEWSHVFRZUGHRZWTXBQWSXEWGSRZWIXGWNWIXGWHSRZWRX
      HMFVDUNWGWHSVGVHVEHTRXEXGVIWSHBVJOVPHTVKVBVLZWRXFMBFHNOVMUNHUGVNVOWIWJWKW
      MVQVRWNCVFRZWIWPVFRZXAWQVIWNXJWLSRZWMWJXLWKWMXLWRMWLFSVGVHVSCTRXJXLVIWNCE
      IVTKWACTVKVBVLWSXEXKXIHWOWBVACWPDWCWDWEWF $.

    $d C f g $.  $d G f $.  $d N f $.  $d V f $.  $d W g $.  $d X f g $.
    $( Lemma 3 for ~ isubgr3stgr .  (Contributed by AV, 17-Sep-2025.) $)
    isubgr3stgrlem3 $p |- ( ( G e. USGraph /\ X e. V /\ ( # ` U ) = N )
                          -> E. g ( g : C -1-1-onto-> W /\ ( g ` X ) = 0 ) ) $=
      ( vf wcel wceq cc0 cvv cusgr cfv w3a csn cdif cv wf1o wex isubgr3stgrlem2
      chash wa cdm f1odm cun cop wi wnel simpr simpl2 c0ex a1i neldifsnd df-nel
      wn sylibr eqid isubgr3stgrlem1 syl112anc ex wf f1of 3ad2ant2 cclnbgr fexd
      ovexi wss stgrvtx0 snssd undifr sylib f1oeq3d biimpa 3adant3 simp12 cnbgr
      cn0 mp1i co nbgrnself2 eleq2i xchbinxr mpbi eleq2 notbid 3ad2ant3 fsnunfv
      wb mpbiri syl3anc jca f1oeq1 eqeq1d anbi12d spcedv 3exp syld mpdi exlimdv
      fveq1 mpd ) EUAQZIGQZCUJUBFRZUCZCHSUDZUEZPUFZUGZPUHAHDUFZUGZIXSUBZSRZUKZD
      UHZABCPEFGHIJKLMNOUIXNXRYDPXNXRXQULZCRZYDCXPXQUMXNXRAXPXOUNZXQISUOUDUNZUG
      ZYFYDUPXNXRYIXNXRUKZXRXLSTQZSXPUQZYIXNXRURXKXLXMXRUSYKYJUTVAYJSXPQVDYLYJS
      HVBSXPVCVEAXPCYHEXQGTISJKLYHVFVGVHVIXNYIYFYDXNYIYFUCZYCAHYHUGZIYHUBZSRZUK
      DTYHYMAYGTYHYIXNAYGYHVJYFAYGYHVKVLATQYMAEIVMLVOVAVNYMYNYPXNYIYNYFXNYIYNXN
      YGHAYHXNXOHVPYGHRXNSHFWFQSHQXNMBFHNOVQWGVRXOHVSVTWAWBWCYMXLYKIYEQZVDZYPXK
      XLXMYIYFWDYKYMUTVAYMYRICQZVDZIEIWEWHZUQZYTEIWIUUBIUUAQYSIUUAVCCUUAIKWJWKW
      LYFXNYRYTWQYIYFYQYSYECIWMWNWOWRXQGTISWPWSWTXSYHRZXTYNYBYPAHXSYHXAUUCYAYOS
      IXSYHXIXBXCXDXEXFXGXHXJ $.

    $d A z $.  $d B a b $.  $d B z $.  $d C a b $.  $d C f g $.  $d C z $.
    $d F a b $.  $d F z $.  $d G f $.  $d N f $.  $d N z $.  $d U f $.
    $d V f $.  $d W f g $.  $d W z $.  $d X a b $.  $d X f g $.  $d X z $.
    isubgr3stgr.e $e |- E = ( Edg ` G ) $.
    $( Lemma 4 for ~ isubgr3stgr .  (Contributed by AV, 24-Sep-2025.) $)
    isubgr3stgrlem4 $p |- ( ( A = X /\ ( F : C -1-1-onto-> W /\ ( F ` X ) = 0 )
                                    /\ ( A =/= B /\ A e. C /\ B e. C ) )
                      -> E. z e. ( 1 ... N ) ( F " { A , B } ) = { 0 , z } ) $=
      ( va vb wceq wf1o cfv cc0 wa wne wcel w3a cpr cima cv c1 co wrex wi preq2
      cfz eqeq2d wf f1of adantr simpr3 ffvelcdmd wo csn cun cvtx fveq2i stgrvtx
      cstgr ax-mp 3eqtri eleq2i fz0sn0fz1 elun fvex elsn orbi1i bitri 3bitri wb
      cn0 eqeq2 adantl wf1 f1of1 wral simpl simpr neeq12d fveq2 imbi12d rspc2gv
      dff14a 3adant1 id eqneqall eqcoms com12 syl6com 3ad2ant1 adantld biimtrid
      syld syl5com imp sylbird idd jaod mpd f1ofn 3simpc anim12i 3anass fnimapr
      wfn sylibr syl preq1d eqtrd rspcedvdw neeq1 eleq1 3anbi12d imaeq2d eqeq1d
      ex preq1 rexbidv imbitrrid 3imp ) BMUCZDLHUDZMHUEZUFUCZUGZBCUHZBDUIZCDUIZ
      UJZHBCUKZULZUFAUMZUKZUCZAUNJUSUOZUPZYRUUBUUIUQYNMCUHZMDUIZUUAUJZHMCUKZULZ
      UUFUCZAUUHUPZUQYRUULUUPYRUULUGZUUOUUNUFCHUEZUKZUCAUURUUHUUEUURUCUUFUUSUUN
      UUEUURUFURUTUUQUURLUIZUURUUHUIZUUQDLCHYRDLHVAZUULYOUVBYQDLHVBVCVCYRUUJUUK
      UUAVDVEUUTUURUFUCZUVAVFZUUQUVAUUTUURUFJUSUOZUIUURUFVGZUUHVHZUIZUVDLUVEUUR
      LEVIUEJVLUEZVIUEZUVESEUVIVIRVJJWDUIZUVJUVEUCQJVKVMVNVOUVEUVGUURUVKUVEUVGU
      CQJVPVMVOUVHUURUVFUIZUVAVFUVDUURUVFUUHVQUVLUVCUVAUURUFCHVRVSVTWAWBUUQUVCU
      VAUVAUUQUVCUURYPUCZUVAYRUVMUVCWCZUULYQUVNYOYPUFUURWEWFVCYRUULUVMUVAUQZYOU
      ULUVOUQYQYODLHWGZUULUVODLHWHUVPUVBUAUMZUBUMZUHZUVQHUEZUVRHUEZUHZUQZUBDWIU
      ADWIZUGUULUVOUAUBDLHWPUULUWDUVOUVBUULUWDUUJYPUURUHZUQZUVOUUKUUAUWDUWFUQUU
      JUWCUWFUAUBMCDDUVQMUCZUVRCUCZUGZUVSUUJUWBUWEUWIUVQMUVRCUWGUWHWJUWGUWHWKWL
      UWIUVTYPUWAUURUWGUVTYPUCUWHUVQMHWMVCUWHUWAUURUCUWGUVRCHWMWFWLWNWOWQUUJUUK
      UWFUVOUQUUAUWFUUJUWEUVOUWFWRUVMUWEUVAUWEUVAUQYPUURUVAYPUURWSWTXAXBXCXFXDX
      EXGVCXHXIUUQUVAXJXKXEXLUUQUUNYPUURUKZUUSUUQHDXRZUUKUUAUJZUUNUWJUCUUQUWKUU
      KUUAUGZUGUWLYRUWKUULUWMYOUWKYQDLHXMVCUUJUUKUUAXNXOUWKUUKUUAXPXSDMCHXQXTUU
      QYPUFUURYRYQUULYOYQWKVCYAYBYCYIYNUUBUULUUIUUPYNYSUUJYTUUKUUABMCYDBMDYEYFY
      NUUGUUOAUUHYNUUDUUNUUFYNUUCUUMHBMCYJYGYHYKWNYLYM $.

    ${
      $d C i $.  $d F i $.  $d I i $.  $d W i $.  $d Y i $.
      isubgr3stgr.i $e |- I = ( Edg ` ( G ISubGr C ) ) $.
      isubgr3stgr.h $e |- H = ( i e. I |-> ( F " i ) ) $.
      $( Lemma 5 for ~ isubgr3stgr .  (Contributed by AV, 24-Sep-2025.) $)
      isubgr3stgrlem5 $p |- ( ( F : C --> W /\ Y e. I )
                              -> ( H ` Y ) = ( F " Y ) ) $=
        ( wf wcel wa cv cima cvv cmpt wceq imaeq2 adantl simpr id cclnbgr ovexi
        a1i fexd adantr imaexd fvmptd ) ALFUDZNIUEZUFZDNFDUGZUHZFNUHZIHUIHDIVGU
        JUKVEUCURVFNUKVGVHUKVEVFNFULUMVCVDUNVEFNUIVCFUIUEVDVCALUIFVCUOAUIUEVCAG
        MUPQUQURUSUTVAVB $.

      $d C a b i z $.  $d E a b i x y $.  $d F e z $.  $d G a b i $.
      $d N a b i $.  $d N e i $.  $d U a b i x y $.  $d V a b i $.  $d W a b $.
      $d X a b i $.
      $( Lemma 6 for ~ isubgr3stgr .  (Contributed by AV, 24-Sep-2025.) $)
      isubgr3stgrlem6 $p |- ( ( ( ( G e. USGraph /\ X e. V )
                   /\ ( ( # ` U ) = N /\ A. x e. U A. y e. U { x , y } e/ E ) )
                   /\ ( F : C -1-1-onto-> W /\ ( F ` X ) = 0 ) )
                              -> H : I --> ( Edg ` ( StarGr ` N ) ) ) $=
        ( vz va vb cusgr wcel wa chash cfv wceq cv cpr wnel wral wf1o cc0 cstgr
        cima cedg wss cuhgr usgruhgr adantr cclnbgr clnbgrssvtx eqsstri cisubgr
        wb co a1i eqid isubgredg syl2an cfz c1 wrex wf f1of cvtx fveq2i stgrvtx
        cn0 ax-mp 3eqtri eqimssi fssd ad2antrl fimassd simplll simpl usgredg wi
        wne vex prss w3a elclnbgrelnbgr expcom eleq2i 3imtr4g im2anan9r 3adant3
        cnbgr imp preq1 eqidd neleq12d preq2 rspc2v syl pm2.24nel 3ad2ant3 syld
        adantl 3exp com24 adantld adantrd imp4c simpllr simplrl simprrr simprrl
        necomd isubgr3stgrlem4 syl113anc prcom imaeq2i eqeq1i rexbii pm2.61iine
        sylibr ex biimtrrid exp32 com23 imbi12d sseq1 eleq1 imaeq2 eqeq1d imp32
        rexbidv mpbird a1d rexlimdvv mpd stgredgel sylanbrc sylbida fmptd ) IUH
        UIZOMUIZUJZEUKULLUMZAUNZBUNZUOZGUPZBEUQAEUQZUJZUJZCNHURZOHULUSUMZUJZUJZ
        FKHFUNZVAZLUTULZVBULZJUVIUVJKUIZUVJGUIZUVJCVCZUJZUVKUVMUIZUVEIVDUIZCMVC
        ZUVNUVQVKUVHUUQUVSUVDUUOUVSUUPIVEVFVFUVTUVHCIOVGVLZMRIOMPVHVIVMCGIICVJV
        LZKUVJMPUBUWBVNUCVOVPUVIUVQUJZUVKUSLVQVLZVCZUVKUSUEUNUOZUMZUEVRLVQVLZVS
        ZUVRUWCCUWDHUVJUVICUWDHVTZUVQUVFUWJUVEUVGUVFCNUWDHCNHWANUWDVCUVFNUWDNDW
        BULUVLWBULZUWDUADUVLWBTWCLWEUIZUWKUWDUMSLWDWFWGWHVMWIWJVFWKUWCUFUNZUGUN
        ZWPZUVJUWMUWNUOZUMZUJZUGMVSUFMVSZUWIUVIUUOUVOUWSUVQUUOUUPUVDUVHWLUVOUVP
        WMUVJGIMUFUGPUBWNVPUWCUWRUWIUFUGMMUWCUWRUWIWOZUWMMUIUWNMUIUJUVIUVOUVPUW
        TUVIUWRUVPUVOUWIUVIUWRUVPUVOUWIWOZWOZUVIUWRUJZUXBUWPCVCZUWPGUIZHUWPVAZU
        WFUMZUEUWHVSZWOZWOZUXCUXEUXDUXHUVIUWRUXEUXDUXHWOZWOZUVIUWOUXLUWQUVIUWOU
        XEUXKUXDUWMCUIZUWNCUIZUJZUVIUWOUXEUJZUJZUXHUWMUWNCUFWQUGWQWRUXQUXOUXHUX
        QUXOUJZUXHWOUWNUWMOOUWNOWPZUWMOWPZUJZUVIUXPUXOUXHUYAUVEUXPUXOUXHWOWOZUV
        HUYAUVDUYBUUQUYAUVCUYBUURUYAUXOUXPUVCUXHUYAUXOUXPUVCUXHWOUYAUXOUXPWSZUV
        CUWPGUPZUXHUYCUWMEUIZUWNEUIZUJZUVCUYDWOUYAUXOUYGUXPUYAUXOUYGUXTUXMUYEUX
        SUXNUYFUXTUWMUWAUIZUWMIOXFVLZUIZUXMUYEUYHUXTUYJIOUWMWTXACUWAUWMRXBEUYIU
        WMQXBXCUXSUWNUWAUIZUWNUYIUIZUXNUYFUYKUXSUYLIOUWNWTXACUWAUWNRXBEUYIUWNQX
        BXCXDXGXEUVBUYDUWMUUTUOZGUPABUWMUWNEEUUSUWMUMZUVAUYMGGUUSUWMUUTXHUYNGXI
        XJUUTUWNUMZUYMUWPGGUUTUWNUWMXKUYOGXIXJXLXMUXPUYAUYDUXHWOZUXOUXEUYPUWOUX
        HUWPGXNXQXOXPXRXSXTXTYAYBUWNOUMZUXRUXHUYQUXRUJZHUWNUWMUOZVAZUWFUMZUEUWH
        VSZUXHUYRUYQUVHUWNUWMWPZUXNUXMVUBUYQUXRWMUXRUVHUYQUVEUVHUXPUXOYCZXQUXRV
        UCUYQUXRUWMUWNUVIUWOUXEUXOYDZYGXQUYQUXQUXMUXNYEUYQUXQUXMUXNYFUEUWNUWMCD
        EGHILMNOPQRSTUAUBYHYIUXGVUAUEUWHUXFUYTUWFUWPUYSHUWMUWNYJYKYLYMYOYPUWMOU
        MZUXRUXHVUFUXRUJVUFUVHUWOUXMUXNUXHVUFUXRWMUXRUVHVUFVUDXQUXRUWOVUFVUEXQV
        UFUXQUXMUXNYFVUFUXQUXMUXNYEUEUWMUWNCDEGHILMNOPQRSTUAUBYHYIYPYNYPYQYRYAX
        GYSUWRUXBUXJVKZUVIUWQVUGUWOUWQUVPUXDUXAUXIUVJUWPCUUAUWQUVOUXEUWIUXHUVJU
        WPGUUBUWQUWGUXGUEUWHUWQUVKUXFUWFUVJUWPHUUCUUDUUFYTYTXQXQUUGYPXSUUEUUHUU
        IUUJUWLUVRUWEUWIUJVKSUEUVKLUUKWFUULUUMUDUUN $.

      $d C y $.  $d F y $.  $d G y $.  $d I y $.  $d J y $.  $d N y $.
      $d V y $.  $d W y $.  $d X y $.
      $( Lemma 7 for ~ isubgr3stgr .  (Contributed by AV, 29-Sep-2025.) $)
      isubgr3stgrlem7 $p |- ( ( ( G e. USGraph /\ X e. V )
                                /\ ( F : C -1-1-onto-> W /\ ( F ` X ) = 0 )
                                /\ J e. ( Edg ` ( StarGr ` N ) ) )
                              -> ( `' F " J ) e. I ) $=
        ( vy cusgr wcel wa wf1o cfv cc0 wceq cstgr cedg ccnv cima cfz co wss cv
        cpr c1 wrex cn0 wb stgredgel mp1i wi wfn w3a cvv a1i prssg sylan f1ocnv
        c0ex f1ofn fveq2i stgrvtx ax-mp 3eqtri fneq2i sylib syl ad2antrl adantr
        cvtx anim1i 3anass sylibr ex sylbird fnimapr cclnbgr clnbgrvtxel adantl
        imp eleqtrrdi simpl anim12ci simprr jca f1ocnvfv ad3antlr f1of fz1ssfz0
        wf sseli ffvelcdmd wo eleq2i cupgr usgrupgr ad2antrr clnbgrssvtx sselid
        eqsstri df-3an sylanbrc clnbupgrel eqeq2 wf1 f1of1 0elfz eleqtrri jctir
        bitrid f1veqaeq syl2an cn elfznn wne nnne0 eqneqall syl5com syld eleq1i
        prcom sylbid eleq1d mpbird biimpi jaod impr prssi mpidan sseq1d anbi12d
        preq1 mpdan cuhgr ad3antrrr cisubgr eqid isubgredg eqeltrd sseq1 imaeq2
        usgruhgr imbi12d syl5ibrcom rexlimdva impcomd 3impia ) GUEUFZNLUFZUGZAM
        FUHZNFUIUJUKZUGZJKULUIZUMUIUFZFUNZJUOZIUFZUVFUVIUGZUVKJUJKUPUQZURZJUJUD
        USZUTZUKZUDVAKUPUQZVBZUGZUVNKVCUFZUVKUWCVDUVORUDJKVEVFUVOUWBUVQUVNUVOUV
        TUVQUVNVGZUDUWAUVOUVRUWAUFZUGZUWEUVTUVSUVPURZUVLUVSUOZIUFZVGUWGUWHUWJUW
        GUWHUGZUWIUJUVLUIZUVRUVLUIZUTZIUWKUVLUVPVHZUJUVPUFZUVRUVPUFZVIZUWIUWNUK
        UWGUWHUWRUWGUWHUWPUWQUGZUWRUVOUJVJUFZUWFUWSUWHVDUWTUVOVOVKUJUVRUVPVJUWA
        VLVMUWGUWSUWRUWGUWSUGUWOUWSUGUWRUWGUWOUWSUVOUWOUWFUVGUWOUVFUVHUVGMAUVLU
        HZUWOAMFVNZUXAUVLMVHUWOMAUVLVPMUVPUVLMBWFUIUVJWFUIZUVPTBUVJWFSVQUWDUXCU
        VPUKRKVRVSVTZWAWBWCWDWEWGUWOUWPUWQWHWIWJWKWPUVPUJUVRUVLWLWCUWKUWNIUFZUW
        NEUFZUWNAURZUGZUWGUXHUWHUWGUWLNUKZUXHUWGUVGNAUFZUGZUVHUGZUXIUVOUXLUWFUV
        OUXKUVHUVFUXJUVIUVGUVFNGNWMUQZAUVENUXMUFUVDGNLOWNZWOQWQUVGUVHWRWSUVFUVG
        UVHWTXAWEUXKUVHUXIAMNUJFXBWPWCUWGUXIUGZUXHNUWMUTZEUFZUXPAURZUGZUWGUXIUX
        JUWMAUFZUGZUXSUWGUXJUXTUVEUXJUVDUVIUWFUVENUXMAUXNQWQXCUWGMAUVRUVLUVOMAU
        VLXFZUWFUVGUYBUVFUVHUVGUXAUYBUXBMAUVLXDWCWDWEUWFUVRMUFZUVOUWFUVRUVPMUWA
        UVPUVRKXEXGUXDWQZWOXHZXAUXOUYAUGUXQUXRUXOUXJUXTUXQUXOUXJUGZUXTUWMNUKZUW
        MNUTZEUFZXIZUXQUXTUWMUXMUFZUYFUYJAUXMUWMQXJUYFGXKUFZUVEUWMLUFZVIZUYKUYJ
        VDUWGUYNUXIUXJUWGUYLUVEUGZUYMUYNUVFUYOUVIUWFUVDUYLUVEGXLWGXMUWGALUWMAUX
        MLQGNLOXNXPZUYEXOUYLUVEUYMXQXRXMEGNUWMLOUAXSWCYFUYFUYGUXQUYIUXOUYGUXQVG
        UXJUXOUYGUWMUWLUKZUXQUXIUYQUYGVDUWGUWLNUWMXTWOUWGUYQUXQVGUXIUWGUYQUVRUJ
        UKZUXQUVOMAUVLYAZUYCUJMUFZUGUYQUYRVGUWFUVGUYSUVFUVHUVGUXAUYSUXBMAUVLYBW
        CWDUWFUYCUYTUYDUJUVPMUWDUWPRKYCVSUXDYDYEMAUVRUJUVLYGYHUWFUYRUXQVGZUVOUW
        FUVRYIUFZVUAUVRKYJVUBUVRUJYKUYRUXQUVRYLUXQUVRUJYMYNWCWOYOWEWKWEUYIUXQVG
        UYFUYIUXQUYHUXPEUWMNYQYPUUAVKUUBYRUUCUYAUXRUXONUWMAUUDWOXAUUEUXIUXHUXSV
        DUWGUXIUXFUXQUXGUXRUXIUWNUXPEUWLNUWMUUHZYSUXIUWNUXPAVUCUUFUUGWOYTUUIWEU
        WGGUUJUFZALURZUXEUXHVDUWHUVDVUDUVEUVIUWFGUURUUKVUEUWHUYPVKAEGGAUULUQZIU
        WNLOUAVUFUUMUBUUNYHYTUUOWJUVTUVQUWHUVNUWJJUVSUVPUUPUVTUVMUWIIJUVSUVLUUQ
        YSUUSUUTUVAUVBYRUVC $.

      $d C i j k y $.  $d E j k $.  $d F j k $.  $d G j k $.  $d I j k $.
      $d N j k $.  $d U j k x $.  $d V j k $.  $d W j k $.  $d X j k $.
      $( Lemma 8 for ~ isubgr3stgr .  (Contributed by AV, 29-Sep-2025.) $)
      isubgr3stgrlem8 $p |- ( ( ( ( G e. USGraph /\ X e. V )
                   /\ ( ( # ` U ) = N /\ A. x e. U A. y e. U { x , y } e/ E ) )
                   /\ ( F : C -1-1-onto-> W /\ ( F ` X ) = 0 ) )
                             -> H : I -1-1-onto-> ( Edg ` ( StarGr ` N ) ) ) $=
        ( vk vj cusgr wcel wa chash cfv wceq cpr wnel wral wf1o cstgr cedg cima
        cv cc0 ccnv cmpt imaeq2 cbvmptv eqtri wf ad2antrl isubgr3stgrlem5 sylan
        isubgr3stgrlem6 ffvelcdmda eqeltrrd isubgr3stgrlem7 ad4ant134 wfo f1ofo
        f1of wss stgrusgra mp1i simpr c2 cvtx fveq2i eqid edgssv2 simpld syl2an
        cn0 foimacnv syl2an2r eqcomd sylan9req f1of1 wi cuhgr usgruhgr ad2antrr
        wf1 wb cclnbgr clnbgrssvtx eqsstri a1i cisubgr isubgredg biimtrdi imp32
        co a1d f1imacnv sylan9eqr impbida f1o2d ) IUGUHZOMUHZUIZEUJUKLULAUTBUTU
        MGUNBEUOAEUOUIZUIZCNHUPZOHUKVAULZUIZUIZUEUFKLUQUKZURUKZHUEUTZUSZHVBZUFU
        TZUSZJJFKHFUTZUSZVCUEKYHVCUDFUEKYMYHYLYGHVDVEVFYDYGKUHZUIYGJUKZYHYFYDCN
        HVGZYNYOYHULYAYPXTYBCNHVRVHCDEFGHIJKLMNOYGPQRSTUAUBUCUDVIVJYDKYFYGJABCD
        EFGHIJKLMNOPQRSTUAUBUCUDVKVLVMXRYCYJYFUHZYKKUHXSCDEFGHIJKYJLMNOPQRSTUAU
        BUCUDVNVOYDYNYQUIZUIZYGYKULZYJYHULZYSYTYJHYKUSZYHYDCNHVPZYRYJNVSZUUBYJU
        LYAUUCXTYBCNHVQVHYDYEUGUHZYQUUDYRLWJUHUUEYDSLVTWAYNYQWBUUEYQUIUUDYJUJUK
        WCULYJYFYENNDWDUKYEWDUKUADYEWDTWEVFYFWFWGWHWICNYJHWKWLYTYHUUBYGYKHVDWMW
        NYSUUAUIYKYGUUAYSYKYIYHUSZYGYJYHYIVDYDCNHWTZYRYGCVSZUUFYGULYAUUGXTYBCNH
        WOVHYDYNYQUUHYDYNYGIURUKZUHZUUHUIZYQUUHWPXTIWQUHZCMVSZYNUUKXAYCXPUULXQX
        SIWRWSUUMYCCIOXBXJMRIOMPXCXDXECUUIIICXFXJZKYGMPUUIWFUUNWFUCXGWIUUKUUHYQ
        UUJUUHWBXKXHXICNYGHXLWLXMWMXNXO $.

      $d C e $.  $d E e $.  $d G e $.  $d U e x y $.  $d V e $.  $d W e $.
      $d X e $.
      $( Lemma 9 for ~ isubgr3stgr .  (Contributed by AV, 29-Sep-2025.) $)
      isubgr3stgrlem9 $p |- ( ( ( ( G e. USGraph /\ X e. V )
                   /\ ( ( # ` U ) = N /\ A. x e. U A. y e. U { x , y } e/ E ) )
                   /\ ( F : C -1-1-onto-> W /\ ( F ` X ) = 0 ) )
                              -> ( H : I -1-1-onto-> ( Edg ` ( StarGr ` N ) )
                                   /\ A. e e. I ( F " e ) = ( H ` e ) ) ) $=
        ( cusgr wcel wa chash cfv wceq cpr wnel wral wf1o cstgr isubgr3stgrlem8
        cv cc0 cedg cima wf ad2antrl isubgr3stgrlem5 eqcomd sylan ralrimiva jca
        f1of ) JUFUGPNUGUHEUIUJMUKAURBURULHUMBEUNAEUNUHUHZCOIUOZPIUJUSUKZUHUHZL
        MUPUJUTUJKUOIFURZVAZVNKUJZUKZFLUNABCDEGHIJKLMNOPQRSTUAUBUCUDUEUQVMVQFLV
        MCOIVBZVNLUGZVQVKVRVJVLCOIVIVCVRVSUHVPVOCDEGHIJKLMNOPVNQRSTUAUBUCUDUEVD
        VEVFVGVH $.
    $}

    $d C e i y $.  $d E e f i x y $.  $d G e g i y $.  $d N e f g i x y $.
    $d U e i x y $.  $d V e i y $.  $d W e i y $.  $d X e i y $.
    $( If a vertex of a simple graph has exactly ` N ` (different) neighbors,
       and none of these neighbors are connected by an edge, then the (closed)
       neighborhood of this vertex induces a subgraph which is isomorphic to an
       ` N `-star.  (Contributed by AV, 29-Sep-2025.) $)
    isubgr3stgr $p |- ( ( G e. USGraph /\ X e. V )
             -> ( ( ( # ` U ) = N /\ A. x e. U A. y e. U { x , y } e/ E )
                  -> ( G ISubGr C ) ~=gr ( StarGr ` N ) ) ) $=
      ( wcel cfv vf vg ve vi cusgr wa chash wceq cv cpr wnel wral cisubgr cstgr
      co cgric wbr cvtx wf1o cedg wex cc0 simpl simpr isubgr3stgrlem3 syl2an3an
      cima wss cclnbgr clnbgrssvtx eqsstri a1i anim2i adantr syl eqcomd f1oeq2d
      isubgrvtx biimpd adantrd imp cmpt cvv fvexd mptexd isubgr3stgrlem9 f1oeq1
      eqid fveq1 eqeq2d ralbidv anbi12d spcedv jca eximdv mpd cushgr isubgrusgr
      ex cuspgr usgruspgr uspgrushgr cn0 stgrusgra ax-mp fveq2i eqtri gricushgr
      wb 3syl sylancl mpbird ) GUESZKISZUFZEUGTHUHZAUIBUIUJFUKBEULAEULZUFZGCUMU
      OZHUNTZUPUQZXOXRUFZYAXSURTZJUAUIZUSZXSUTTZXTUTTZUBUIZUSZYDUCUIZVGZYJYHTZU
      HZUCYFULZUFZUBVAZUFZUAVAZYBCJYDUSZKYDTVBUHZUFZUAVAZYRXOXMXNXRXPUUBXMXNVCX
      MXNVDXPXQVCCDEUAGHIJKLMNOPQVEVFYBUUAYQUAYBUUAYQYBUUAUFZYEYPYBUUAYEYBYSYEY
      TYBYSYEYBCYCJYDYBYCCYBXMCIVHZUFZYCCUHXOUUEXRXNUUDXMUUDXNCGKVIUOINGKILVJVK
      VLVMZVNCGIUELVRVOVPVQVSVTWAUUCYOYFYGUDYFYDUDUIVGZWBZUSZYKYJUUHTZUHZUCYFUL
      ZUFUBWCUUHUUCUDYFUUGWCUUCXSUTWDWEABCDEUCUDFYDGUUHYFHIJKLMNOPQRYFWHZUUHWHW
      FYHUUHUHZYIUUIYNUULYFYGYHUUHWGUUNYMUUKUCYFUUNYLUUJYKYJYHUUHWIWJWKWLWMWNWS
      WOWPXOYAYRXIZXRXOXSWQSZXTWQSZUUOXOXSUESZXSWTSUUPXOUUEUURUUFCGILWRVOXSXAXS
      XBXJHXCSZUUQOUUSXTUESXTWTSUUQHXDXTXAXTXBXJXEXSXTUCUAUBYFYGYCJYCWHJDURTXTU
      RTQDXTURPXFXGUUMYGWHXHXKVNXLWS $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Local isomorphisms of graphs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  This section is about local isomorphisms of graphs, which are a
  generalization of isomorphisms of graphs, i.e., every isomorphism between two
  graphs is also a local isomorphism between these graphs, see ~ uhgrimgrlim .

  This definition is according to a chat in mathoverflow
  ( ~ https://mathoverflow.net/questions/491133/locally-isomorphic-graphs ):
  roughly speaking, it restricts the correspondence of two graphs to their
  neighborhoods.

  Additionally, a binary relation ` ~=lgr ` is defined (see ~ df-grlic ) which
  is true for two graphs iff there is a local isomorphism between these graphs.
  Then these graphs are called "locally isomorphic".  Therefore, this relation
  is also called "is locally isomorphic to" relation.  As a main result of this
  section, it is shown that the "is locally isomorphic to" relation is an
  equivalence relation (for hypergraphs), see ~ grlicer .

  The names and symbols are chosen analogously to group isomorphisms ` GrpIso `
  (see ~ df-gim ) and graph isomorphisms ` GraphIso ` (see ~ df-grim ) resp.
  isomorphism between groups ` ~=g ` (see ~ df-gic ) and isomorphism between
  graphs ` ~=gr ` (see ~ df-gric ).

  As discussed in the above mentioned chat in mathoverflow, it is shown that
  there are local isomorphisms between two graphs which are not (ordinary)
  isomorphisms between these graphs.  In other words, there are two different
  locally isomorphic graphs which are not isomorphic, see ~ lgricngricex .
  Such two graphs are the two generalized Petersen graphs G(5,K) of order 10
  (see definition ~ df-gpg ), which are the Petersen graph G(5,2) and the
  5-prism G(5,1), see ~ gpg5ngric .

$)

  $c GraphLocIso $.
  $c ~=lgr $.

  $( The class of graph local isomorphism sets. $)
  cgrlim $a class GraphLocIso $.

  $( The class of the graph local isomorphism relation. $)
  cgrlic $a class ~=lgr $.

  ${
    $d f g h v $.
    $( A local isomorphism of graphs is a bijection between the sets of
       vertices of two graphs that preserves local adjacency, i.e. the subgraph
       induced by the closed neighborhood of a vertex of the first graph and
       the subgraph induced by the closed neighborhood of the associated vertex
       of the second graph are isomorphic.  See the following chat in
       mathoverflow:
       ~ https://mathoverflow.net/questions/491133/locally-isomorphic-graphs .
       (Contributed by AV, 27-Apr-2025.) $)
    df-grlim $a |- GraphLocIso = ( g e. _V , h e. _V
                           |-> { f | ( f : ( Vtx ` g ) -1-1-onto-> ( Vtx ` h )
       /\ A. v e. ( Vtx ` g ) ( g ISubGr ( g ClNeighbVtx v ) )
                         ~=gr ( h ISubGr ( h ClNeighbVtx ( f ` v ) ) ) ) } ) $.

    $( The graph local isomorphism function is a well-defined function.
       (Contributed by AV, 20-May-2025.) $)
    grlimfn $p |- GraphLocIso Fn ( _V X. _V ) $=
      ( vg vh vf vv cvv cv cvtx cfv wf1o cclnbgr co cisubgr cgric wbr wa cgrlim
      wral cab df-grlim wcel fvex wf f1of ad2antrl fvexd id fabexd ax-mp fnmpoi
      ) ABEEAFZGHZBFZGHZCFZIZUJUJDFZJKLKULULUPUNHJKLKMNDUKQZOZCRZPDCABSUMETZUSE
      TULGUAUTURCEEUKUMUOUKUMUNUBUTUQUKUMUNUCUDUTUJGUEUTUFUGUHUI $.

    $( The domain of the graph local isomorphism function is a relation.
       (Contributed by AV, 20-May-2025.) $)
    grlimdmrel $p |- Rel dom GraphLocIso $=
      ( vg vh vf vv cvv cv cvtx cfv wf1o cclnbgr co cisubgr cgric wbr wa cgrlim
      wral cab df-grlim reldmmpo ) ABEEAFZGHZBFZGHCFZIUAUADFZJKLKUCUCUEUDHJKLKM
      NDUBQOCRPDCABST $.
  $}

  $( Two graphs are said to be locally isomorphic iff they are connected by at
     least one local isomorphism.  (Contributed by AV, 27-Apr-2025.) $)
  df-grlic $a |- ~=lgr = ( `' GraphLocIso " ( _V \ 1o ) ) $.

  ${
    $d F f g h v $.  $d G f g h v $.  $d H f g h v $.  $d V v $.  $d X f g h $.
    $d Y f g h $.  $d Z f g h $.
    isgrlim.v $e |- V = ( Vtx ` G ) $.
    isgrlim.w $e |- W = ( Vtx ` H ) $.
    $( A local isomorphism of graphs is a bijection between their vertices that
       preserves neighborhoods.  (Contributed by AV, 20-May-2025.) $)
    isgrlim $p |- ( ( G e. X /\ H e. Y /\ F e. Z )
                   -> ( F e. ( G GraphLocIso H ) <-> ( F : V -1-1-onto-> W
                 /\ A. v e. V ( G ISubGr ( G ClNeighbVtx v ) )
                         ~=gr ( H ISubGr ( H ClNeighbVtx ( F ` v ) ) ) ) ) ) $=
      ( vf wcel co cvtx cfv cclnbgr cisubgr cvv wceq vg vh cgrlim cv wf1o cgric
      w3a wbr wral wa cab df-grlim elex 3ad2ant1 3ad2ant2 wf f1of adantr adantl
      fvexd fabexd eqidd fveq2 f1oeq123d id oveq12d breqan12d raleqbidv anbi12d
      oveq1 abbidv elovmpod wb f1oeq1 fveq1 oveq2d breq2d ralbidv elabg f1oeq23
      3ad2ant3 mp2an raleqi anbi12i bitr4di bitrd ) CGMZDHMZBIMZUGZBCDUCNMBCOPZ
      DOPZLUDZUEZCCAUDZQNZRNZDDWOWMPZQNZRNZUFUHZAWKUIZUJZLUKZMZEFBUEZWQDDWOBPZQ
      NZRNZUFUHZAEUIZUJZWJSSUAUDZOPZUBUDZOPZWMUEZXMXMWOQNZRNZXOXOWRQNZRNZUFUHZA
      XNUIZUJZLUKXDBUCSCDUAUBALUAUBULWGWHCSMWICGUMUNWHWGDSMWIDHUMUOWJXCLSSWKWLX
      CWKWLWMUPZWJWNYEXBWKWLWMUQURUSWJCOUTWJDOUTVAXMCTZXODTZUJZYDXCLYHXQWNYCXBY
      HXNWKXPWLWMWMYHWMVBYFXNWKTYGXMCOVCURZYGXPWLTYFXODOVCUSVDYHYBXAAXNWKYIYFYG
      XSWQYAWTUFYFXMCXRWPRYFVEXMCWOQVJVFYGXODXTWSRYGVEXODWRQVJVFVGVHVIVKVLWJXEW
      KWLBUEZXJAWKUIZUJZXLWIWGXEYLVMWHXCYLLBIWMBTZWNYJXBYKWKWLWMBVNYMXAXJAWKYMW
      TXIWQUFYMWSXHDRYMWRXGDQWOWMBVOVPVPVQVRVIVSWAXFYJXKYKEWKTFWLTXFYJVMJKEWKFW
      LBVTWBXJAEWKJWCWDWEWF $.

    $d G i $.  $d G x $.  $d H i $.  $d H x $.  $d I x $.  $d J x $.  $d K i $.
    $d L i $.  $d M f g i $.  $d M x $.  $d N f g i $.  $d N x $.  $d X i v $.
    $d Y i v $.  $d Z v $.
    isgrlim2.n $e |- N = ( G ClNeighbVtx v ) $.
    isgrlim2.m $e |- M = ( H ClNeighbVtx ( F ` v ) ) $.
    isgrlim2.i $e |- I = ( iEdg ` G ) $.
    isgrlim2.j $e |- J = ( iEdg ` H ) $.
    isgrlim2.k $e |- K = { x e. dom I | ( I ` x ) C_ N } $.
    isgrlim2.l $e |- L = { x e. dom J | ( J ` x ) C_ M } $.
    $( A local isomorphism of graphs is a bijection between their vertices that
       preserves neighborhoods.  Definitions expanded.  (Contributed by AV,
       29-May-2025.) $)
    isgrlim2 $p |- ( ( G e. X /\ H e. Y /\ F e. Z )
                     -> ( F e. ( G GraphLocIso H ) <-> ( F : V -1-1-onto-> W
                /\ A. v e. V E. f ( f : N -1-1-onto-> M
                /\ E. g ( g : K -1-1-onto-> L
                /\ A. i e. K ( f " ( I ` i ) ) = ( J ` ( g ` i ) ) ) ) ) ) ) $=
      ( wcel w3a cgrlim co wf1o cv cclnbgr cisubgr cfv cgric wbr wral cima wceq
      wa wex isgrlim eqcomi oveq2i breq12i a1i clnbgrisubgrgrim 3adant3 ralbidv
      wb bitrd anbi2d ) GQUHZHRUHZFSUHZUIZFGHUJUKUHOPFULZGGBUMZUNUKZUOUKZHHVTFU
      PZUNUKZUOUKZUQURZBOUSZVBVSNMCUMZULKLDUMZULWHEUMZIUPUTWJWIUPJUPVAEKUSVBDVC
      VBCVCZBOUSZVBBFGHOPQRSTUAVDVRWGWLVSVRWFWKBOVRWFGNUOUKZHMUOUKZUQURZWKWFWOV
      LVRWBWMWEWNUQWANGUONWAUBVEVFWDMHUOMWDUCVEVFVGVHVOVPWOWKVLVQARQCDEGHIJKLMN
      VTWCUDUEUBUCUFUGVIVJVMVKVNVM $.
  $}

  ${
    $d F v $.  $d G v $.  $d H v $.  $d V v $.
    grlimprop.v $e |- V = ( Vtx ` G ) $.
    grlimprop.w $e |- W = ( Vtx ` H ) $.
    $( Properties of a local isomorphism of graphs.  (Contributed by AV,
       21-May-2025.) $)
    grlimprop $p |- ( F e. ( G GraphLocIso H ) -> ( F : V -1-1-onto-> W
                   /\ A. v e. V ( G ISubGr ( G ClNeighbVtx v ) )
                           ~=gr ( H ISubGr ( H ClNeighbVtx ( F ` v ) ) ) ) ) $=
      ( cvv wcel cgrlim co w3a wf1o cv cclnbgr cisubgr cfv cgric wbr grlimdmrel
      wral wa ovrcl simpld simprd id 3jca isgrlim biimpd mpcom ) CIJZDIJZBCDKLZ
      JZMZUOEFBNCCAOZPLQLDDUQBRPLQLSTAEUBUCZUOULUMUOUOULUMCDBKUAUDZUEUOULUMUSUF
      UOUGUHUPUOURABCDEFIIUNGHUIUJUK $.

    $( A local isomorphism of graphs is a bijection between their vertices.
       (Contributed by AV, 21-May-2025.) $)
    grlimf1o $p |- ( F e. ( G GraphLocIso H ) -> F : V -1-1-onto-> W ) $=
      ( vv cgrlim co wcel wf1o cv cclnbgr cisubgr cfv cgric wbr wral grlimprop
      simpld ) ABCIJKDEALBBHMZNJOJCCUBAPNJOJQRHDSHABCDEFGTUA $.

    $d F f g v $.  $d G f g i x $.  $d H f g i x $.  $d I x $.  $d J x $.
    $d K i $.  $d L i $.  $d M f g i x $.  $d N f g i x $.  $d i v $.
    grlimprop2.n $e |- N = ( G ClNeighbVtx v ) $.
    grlimprop2.m $e |- M = ( H ClNeighbVtx ( F ` v ) ) $.
    grlimprop2.i $e |- I = ( iEdg ` G ) $.
    grlimprop2.j $e |- J = ( iEdg ` H ) $.
    grlimprop2.k $e |- K = { x e. dom I | ( I ` x ) C_ N } $.
    grlimprop2.l $e |- L = { x e. dom J | ( J ` x ) C_ M } $.
    $( Properties of a local isomorphism of graphs.  (Contributed by AV,
       29-May-2025.) $)
    grlimprop2 $p |- ( F e. ( G GraphLocIso H ) -> ( F : V -1-1-onto-> W
                  /\ A. v e. V E. f ( f : N -1-1-onto-> M
                  /\ E. g ( g : K -1-1-onto-> L
                  /\ A. i e. K ( f " ( I ` i ) ) = ( J ` ( g ` i ) ) ) ) ) ) $=
      ( cgrlim co wcel wf1o cv cfv cima wceq wa wex cvv w3a wb grlimdmrel ovrcl
      wral id df-3an sylanbrc isgrlim2 syl ibi ) FGHUEUFZUGZOPFUHNMCUIZUHKLDUIZ
      UHVIEUIZIUJUKVKVJUJJUJULEKUTUMDUNUMCUNBOUTUMZVHGUOUGZHUOUGZVHUPZVHVLUQVHV
      MVNUMVHVOGHFUEURUSVHVAVMVNVHVBVCABCDEFGHIJKLMNOPUOUOVGQRSTUAUBUCUDVDVEVF
      $.
  $}

  ${
    $d F v $.  $d G v $.  $d H v $.
    $( An isomorphism of hypergraphs is a local isomorphism between the two
       graphs.  (Contributed by AV, 2-Jun-2025.) $)
    uhgrimgrlim $p |- ( ( G e. UHGraph /\ H e. UHGraph
                    /\ F e. ( G GraphIso H ) ) -> F e. ( G GraphLocIso H ) ) $=
      ( vv cuhgr wcel cgrim co w3a cgrlim cvtx cfv cv cclnbgr cisubgr cgric wbr
      wf1o eqid wa wral grimf1o 3ad2ant3 cima wss simpl1 simpl3 clnbgrssvtx a1i
      uhgrimisgrgric syl3anc df-3an clnbgrgrim sylanb oveq2d breqtrrd ralrimiva
      wceq isgrlim mpbir2and ) BEFZCEFZABCGHZFZIZABCJHFBKLZCKLZARZBBDMZNHZOHZCC
      VIALNHZOHZPQZDVFUAVDVAVHVBABCVFVGVFSZVGSZUBUCVEVNDVFVEVIVFFZTZVKCAVJUDZOH
      ZVMPVRVAVDVJVFUEZVKVTPQVAVBVDVQUFVAVBVDVQUGWAVRBVIVFVOUHUIABCVJVFVOUJUKVR
      VLVSCOVEVAVBTVDTVQVLVSURVAVBVDULABCVFVIVOUMUNUOUPUQDABCVFVGEEVCVOVPUSUT
      $.
  $}

  ${
    $d H x y z $.  $d J x y $.  $d M x y z $.
    uspgrlimlem1.m $e |- M = ( H ClNeighbVtx X ) $.
    uspgrlimlem1.j $e |- J = ( Edg ` H ) $.
    uspgrlimlem1.l $e |- L = { x e. J | x C_ M } $.
    $( Lemma 1 for ~ uspgrlim .  (Contributed by AV, 16-Aug-2025.) $)
    uspgrlimlem1 $p |- ( H e. USPGraph
                 -> L = ( ( iEdg ` H ) " { x e. dom ( iEdg ` H )
                                           | ( ( iEdg ` H ) ` x ) C_ M } ) ) $=
      ( vz vy wcel cv wss crab cfv wceq a1i wa sseq1 cuspgr ciedg cdm cima wrex
      cedg wf wf1o eqid uspgrf1oedg f1of syl ssrab2 fimarab eqcomi fveq2 sseq1d
      sylancl rexrab ccnv biimpac f1ocnv 3syl ffvelcdmda adantr f1ocnvfv2 sylan
      wi wb eqcoms biimpcd adantl ancrd mpd fveqeq2 rspceb2dv bitrid rabeqbidva
      anbi12d cbvrabv 3eqtrrd eqtrid ) BUALZDAMZENZACOZBUBPZWDWGPZENZAWGUCZOZUD
      ZIWCWLJMZWGPZKMZQZJWKUEZKBUFPZOZWOENZKCOZWFWCWJWRWGUGZWKWJNWLWSQWCWJWRWGU
      HZXBWGBWGUIUJZWJWRWGUKULWIAWJUMJKWJWRWGWKUNURWCWQWTKWRCWRCQWCCWRHUORWQWNE
      NZWPSZJWJUEWCWOWRLZSZWTWIXEWPJAWJWDWMQWHWNEWDWMWGUPUQUSXHXFWTWOWGUTZPZWGP
      ZENZXKWOQZSZJXJWJXFWTVHXHWMWJLSWPXEWTWNWOETVARXHXJWJLWTWCWRWJWOXIWCXCWRWJ
      XIUHWRWJXIUGXDWJWRWGVBWRWJXIUKVCVDVEXHWTSZXMXNXHXMWTWCXCXGXMXDWJWRWOWGVFV
      GVEXOXMXLWTXMXLVHXHXMWTXLWTXLVIWOXKWOXKETVJVKVLVMVNWMXJQZXEXLWPXMXPWNXKEW
      MXJWGUPUQWMXJWOWGVOVSVPVQVRXAWFQWCWTWEKACWOWDETVTRWAWB $.

    $d L x y $.
    $( Lemma 2 for ~ uspgrlim .  (Contributed by AV, 16-Aug-2025.) $)
    uspgrlimlem2 $p |- ( H e. USPGraph -> ( `' ( iEdg ` H ) " L )
                   = { x e. dom ( iEdg ` H ) | ( ( iEdg ` H ) ` x ) C_ M } ) $=
      ( vy wcel cfv cv wceq crab wss wf wf1o wa wi ccnv cima wrex cdm cedg eqid
      cuspgr ciedg uspgrf1oedg f1ocnv rabeqi eqtri ssrab3 fimarab sylancl sseq1
      f1of elrab2 eleq2i biimpi f1ocnvfv2 syl2an eqcomd sseq1d biimpd ex adantr
      3syl imp32 3adant3 wb fveq2 3ad2ant3 mpbid 3exp biimtrid rexlimdv fveqeq2
      w3a eqcomi feq23i ffvelcdmda anim1i elrab2w sylibr f1ocnvfv1 sylan impbid
      rspcedvdw rabbidva eqtrd ) BUGKZBUHLZUAZDUBZJMZWNLZAMZNZJDUCZAWMUDZOZWRWM
      LZEPZAXAOWLBUELZXAWNQZDXEPWOXBNWLXAXEWMRZXEXAWNRXFWMBWMUFUIZXAXEWMUJXEXAW
      NUQVHWREPZAXEDDXIACOXIAXEOIXIACXEHUKULUMJAXEXAWNDUNUOWLWTXDAXAWLWRXAKZSZW
      TXDXKWSXDJDWPDKWPCKZWPEPZSZXKWSXDTXIXMAWPCDWRWPEUPZIURXKXNWSXDXKXNWSVSWQW
      MLZEPZXDXKXNXQWSXKXLXMXQWLXLXMXQTZTXJWLXLXRWLXLSZXMXQXSWPXPEXSXPWPWLXGWPX
      EKZXPWPNXLXHXLXTCXEWPHUSUTXAXEWPWMVAVBVCVDVEVFVGVIVJWSXKXQXDVKXNWSXPXCEWQ
      WRWMVLVDVMVNVOVPVQXKXDWTXKXDSZWSXCWNLWRNZJXCDWPXCWRWNVRYAXCCKZXDSXCDKXKYC
      XDWLXACWRWMWLXGXAXEWMQZXACWMQZXHXAXEWMUQYDYEXAXEXACWMXAUFCXEHVTWAUTVHWBWC
      XIXMXDAJXCCDXOWPXCEUPIWDWEXKYBXDWLXGXJYBXHXAXEWRWMWFWGVGWIVFWHWJWK $.
  $}

  ${
    $d G i x $.  $d H i x $.  $d I x $.  $d J x $.  $d M x $.  $d N i x $.
    $d e i x $.  $d f i $.  $d h i $.
    uspgrlim.v $e |- V = ( Vtx ` G ) $.
    uspgrlim.w $e |- W = ( Vtx ` H ) $.
    uspgrlim.n $e |- N = ( G ClNeighbVtx v ) $.
    uspgrlim.m $e |- M = ( H ClNeighbVtx ( F ` v ) ) $.
    uspgrlim.i $e |- I = ( Edg ` G ) $.
    uspgrlim.j $e |- J = ( Edg ` H ) $.
    uspgrlim.k $e |- K = { x e. I | x C_ N } $.
    uspgrlim.l $e |- L = { x e. J | x C_ M } $.
    $( Lemma 3 for ~ uspgrlim .  (Contributed by AV, 16-Aug-2025.) $)
    uspgrlimlem3 $p |- ( ( G e. USPGraph
            /\ h : { x e. dom ( iEdg ` G ) | ( ( iEdg ` G ) ` x ) C_ N }
                   -1-1-onto-> R
            /\ A. i e. { x e. dom ( iEdg ` G ) | ( ( iEdg ` G ) ` x ) C_ N }
                ( f " ( ( iEdg ` G ) ` i ) ) = ( ( iEdg ` H ) ` ( h ` i ) ) )
               -> ( e e. K -> ( f " e )
                  = ( ( ( ( iEdg ` H ) o. h ) o. `' ( iEdg ` G ) ) ` e ) ) ) $=
      ( cv wcel wss cuspgr ciedg cfv cdm crab wf1o cima wceq wral w3a ccom ccnv
      wa sseq1 elrab2 cedg wf eqid uspgrf1oedg f1ocnv f1of 3syl 3ad2ant1 eleq2i
      birani fvco3 syl2an wi f1ocnvdm f1ocnvfv2 simprr eqsstrd jca fveq2 sseq1d
      adantlr elrab sylibr imaeq2d 2fveq3 eqeq12d rspcv syl eqcom fvco3d eqcomd
      ad2antlr adantr biimpd biimtrid syld ex com23 3imp1 eqtr2d ) DUGZMUHXEKUH
      ZXEPUIZVBZIUJUHZAUGZIUKULZULZPUIZAXKUMZUNZCFUGZUOZEUGZGUGZXKULZUPZXSXPULJ
      UKULZULZUQZGXOURZUSZXRXEUPZXEYBXPUTZXKVAZUTULZUQZXJPUIXGAXEKMXJXEPVCUEVDY
      FXHYKYFXHVBYJXEYIULZYHULZYGYFIVEULZXNYIVFZXEYNUHZYJYMUQXHXIXQYOYEXIXNYNXK
      UOZYNXNYIUOYOXKIXKVGVHZXNYNXKVIYNXNYIVJVKVLXFYPXGKYNXEUCVMVNZYNXNXEYHYIVO
      VPXIXQYEXHYMYGUQZXIXQYEXHYTVQVQXIXQVBZXHYEYTUUAXHYEYTVQUUAXHVBZYEXRYLXKUL
      ZUPZYLXPULYBULZUQZYTUUBYLXOUHZYEUUFVQUUBYLXNUHZUUCPUIZVBZUUGXIXHUUJXQXIXH
      VBZUUHUUIXIYQYPUUHXHYRYSXNYNXEXKVRVPUUKUUCXEPXIYQYPUUCXEUQZXHYRYSXNYNXEXK
      VSZVPXIXFXGVTWAWBWEXMUUIAYLXNXJYLUQXLUUCPXJYLXKWCWDWFWGZYDUUFGYLXOXSYLUQZ
      YAUUDYCUUEUUOXTUUCXRXSYLXKWCWHXSYLYBXPWIWJWKWLUUFUUEUUDUQZUUBYTUUDUUEWMUU
      BUUPYTUUBUUEYMUUDYGUUBYMUUEUUBXOCYLYBXPXQXOCXPVFXIXHXOCXPVJWPUUNWNWOUUBUU
      CXEXRUUAYQYPUULXHXIYQXQYRWQYSUUMVPWHWJWRWSWTXAXBXAXCXDXAWS $.

    $d G e i x $.  $d K e x $.  $d L x $.  $d e f i $.  $d e g $.
    $( Lemma 4 for ~ uspgrlim .  (Contributed by AV, 16-Aug-2025.) $)
    uspgrlimlem4 $p |- ( ( ( G e. USPGraph /\ H e. USPGraph )
                /\ ( g : K -1-1-onto-> L /\ A. e e. K ( f " e ) = ( g ` e ) ) )
                    -> ( ( i e. dom ( iEdg ` G ) /\ ( ( iEdg ` G ) ` i ) C_ N )
                         -> ( f " ( ( iEdg ` G ) ` i ) )
                            = ( ( iEdg ` H ) ` ( ( ( `' ( iEdg ` H ) o. g )
                                               o. ( iEdg ` G ) ) ` i ) ) ) ) $=
      ( cuspgr wcel wa cv wf1o cima cfv wceq wral ciedg cdm ccnv ccom cedg eqid
      wss uspgrf1oedg f1of syl ad2antrr simpl fvco3 fveq2d syl2an ad3antlr crab
      wf ssrab2 eqcomi 3sstr4i adantr adantl wfun ffund iedgedg eleqtrrdi sseq1
      simprr elrab2 sylanbrc ffvelcdmd sselid f1ocnvfv2 syl2anc wi ax-mp biimpi
      wb feq3 imaeq2 fveq2 eqeq12d rspcv ex com23 adantld imp31 3eqtr4d eqtr2d
      3syl ) HUFUGZIUFUGZUHZLMEUIZUJZDUIZCUIZUKZXLXIULZUMZCLUNZUHZUHZFUIZHUOULZ
      UPZUGZXSXTULZOVAZUHZXKYCUKZXSIUOULZUQZXIURZXTURULZYGULZUMXRYEUHZYKYCYIULZ
      YGULZYFXRYAHUSULZXTVLZYBYKYNUMYEXFYPXGXQXFYAYOXTUJZYPXTHXTUTZVBZYAYOXTVCZ
      VDVEZYBYDVFZYPYBUHYJYMYGYAYOXSYIXTVGVHVIYLYCXIULZYHULZYGULZUUCYNYFYLYGUPZ
      IUSULZYGUJZUUCUUGUGUUEUUCUMXGUUHXFXQYEYGIYGUTVBVJYLMUUGUUCAUIZNVAZAKVKKMU
      UGUUJAKVMUEKUUGUCVNVOYLLMYCXIXRLMXIVLZYEXQUUKXHXJUUKXPLMXIVCVPVQVPZYLYCJU
      GZYDYCLUGZYLYCYOJXRXTVRYBYCYOUGYEXRYAYOXTUUAVSUUBXTHXSYRVTVIUBWAXRYBYDWCU
      UIOVAYDAYCJLUUIYCOWBUDWDZWEZWFWGUUFUUGUUCYGWHWIYLUUKUUNYNUUEUMUULUUPUUKUU
      NUHYMUUDYGLMYCYHXIVGVHWIXHXQYEYFUUCUMZXHXPYEUUQWJXJXHYEXPUUQXHYEXPUUQWJZX
      HYEUHZUUNUURUUSUUMYDUUNUUSYAJXSXTXFYAJXTVLZXGYEXFYQYPUUTYSYTYPUUTYOJUMYPU
      UTWMJYOUBVNYOJYAXTWNWKWLXEVEYEYBXHUUBVQWFXHYBYDWCUUOWEXOUUQCYCLXLYCUMXMYF
      XNUUCXLYCXKWOXLYCXIWPWQWRVDWSWTXAXBXCXDWS $.

    $d F f h v $.  $d G f g h v $.  $d H e f g h v $.  $d K g h i $.
    $d L g h i $.  $d M e f g h i $.  $d N e f g h $.  $d V v $.  $d Z f h v $.
    $d i v $.  $d g h x $.
    $( A local isomorphism of simple pseudographs is a bijection between their
       vertices that preserves neighborhoods, expressed by properties of their
       edges (not edge functions as in ~ isgrlim2 ).  (Contributed by AV,
       15-Aug-2025.) $)
    uspgrlim $p |- ( ( G e. USPGraph /\ H e. USPGraph /\ F e. Z )
                     -> ( F e. ( G GraphLocIso H ) <-> ( F : V -1-1-onto-> W
                      /\ A. v e. V E. f ( f : N -1-1-onto-> M
                      /\ E. g ( g : K -1-1-onto-> L
                                /\ A. e e. K ( f " e ) = ( g ` e ) ) ) ) ) ) $=
      ( vh vi cuspgr wcel w3a cgrlim co wf1o cv cfv wss cdm crab cima wceq wral
      ciedg wa wex eqid isgrlim2 wb ccom ccnv cvv fvex vex coex a1i uspgrf1oedg
      cedg ad2antrr simprl ad2antlr ssrab2 pm3.2i 3f1oss1 syl31anc uspgrlimlem1
      cnvex f1oeq123d mpbird wi simpll simprr uspgrlimlem3 syl3anc ralrimiv jca
      eqidd f1oeq1 fveq1 eqeq2d ralbidv anbi12d spcedv ex exlimdv rabeqi ssrab3
      eqtri 3f1oss2 uspgrlimlem2 mpbid fveq2 sseq1d elrab uspgrlimlem4 biimtrid
      fveq2d impbid anbi2d exbidv 3adant3 bitrd ) GUHUIZHUHUIZFQUIZUJFGHUKULUIO
      PFUMZNMDUNZUMZAUNZGVBUOZUOZNUPZAYHUQZURZYGHVBUOZUOMUPZAYMUQZURZUFUNZUMZYE
      UGUNZYHUOZUSZYSYQUOZYMUOZUTZUGYLVAZVCZUFVDZVCZDVDZBOVAZVCZYDYFKLEUNZUMZYE
      CUNZUSZUUNUULUOZUTZCKVAZVCZEVDZVCZDVDZBOVAZVCZABDUFUGFGHYHYMYLYPMNOPUHUHQ
      RSTUAYHVEZYMVEZYLVEYPVEVFYAYBUUKUVDVGYCYAYBVCZUUJUVCYDUVGUUIUVBBOUVGUUHUV
      ADUVGUUGUUTYFUVGUUGUUTUVGUUFUUTUFUVGUUFUUTUVGUUFVCZUUSKLYMYQVHZYHVIZVHZUM
      ZUUOUUNUVKUOZUTZCKVAZVCEVJUVKUVKVJUIUVHUVIUVJYMYQHVBVKZUFVLVMYHGVBVKZWEVM
      VNUVHUVLUVOUVHUVLYHYLUSZYMYPUSZUVKUMZUVHYKGVPUOZYHUMZYRYOHVPUOZYMUMZYLYKU
      PZYPYOUPZVCZUVTYAUWBYBUUFYHGUVEVOZVQUVGYRUUEVRZYBUWDYAUUFYMHUVFVOZVSUWGUV
      HUWEUWFYJAYKVTYNAYOVTWAVNYKUWAYLYPYOYHYQYMUWCWBWCUVHKUVRLUVSUVKUVKUVHUVKW
      OYAKUVRUTYBUUFAGIKNBUNZTUBUDWDVQYBLUVSUTYAUUFAHJLMUWKFUOZUAUCUEWDVSWFWGUV
      HUVNCKUVHYAYRUUEUUNKUIUVNWHYAYBUUFWIUWIUVGYRUUEWJABYPCDUFUGFGHIJKLMNOPRST
      UAUBUCUDUEWKWLWMWNUULUVKUTZUUMUVLUURUVOKLUULUVKWPUWMUUQUVNCKUWMUUPUVMUUOU
      UNUULUVKWQWRWSWTXAXBXCUVGUUSUUGEUVGUUSUUGUVGUUSVCZUUFYLYPYMVIZUULVHZYHVHZ
      UMZUUAYSUWQUOZYMUOZUTZUGYLVAZVCUFVJUWQUWQVJUIUWNUWPYHUWOUULYMUVPWEEVLVMUV
      QVMVNUWNUWRUXBUWNUVJKUSZUWOLUSZUWQUMZUWRUWNUWBUUMUWDKUWAUPZLUWCUPZVCZUXEY
      AUWBYBUUSUWHVQUVGUUMUURVRYBUWDYAUUSUWJVSUXHUWNUXFUXGYGNUPZAUWAKKUXIAIURUX
      IAUWAURUDUXIAIUWAUBXDXFXEYGMUPZAUWCLLUXJAJURUXJAUWCURUEUXJAJUWCUCXDXFXEWA
      VNYKUWAKLYOYHUULYMUWCXGWCUWNUXCYLUXDYPUWQUWQUWNUWQWOYAUXCYLUTYBUUSAGIKNUW
      KTUBUDXHVQYBUXDYPUTYAUUSAHJLMUWLUAUCUEXHVSWFXIUWNUXAUGYLYSYLUIYSYKUIYTNUP
      ZVCUWNUXAYJUXKAYSYKYGYSUTYIYTNYGYSYHXJXKXLABCDEUGFGHIJKLMNOPRSTUAUBUCUDUE
      XMXNWMWNYQUWQUTZYRUWRUUEUXBYLYPYQUWQWPUXLUUDUXAUGYLUXLUUCUWTUUAUXLUUBUWSY
      MYSYQUWQWQXOWRWSWTXAXBXCXPXQXRWSXQXSXT $.
  $}

  ${
    $d F f v $.  $d G e f g v x $.  $d H e f g v x $.  $d I x $.  $d J x $.
    $d K e g x $.  $d L g x $.  $d M e f g x $.  $d N e f g x $.  $d V v $.
    usgrlimprop.v $e |- V = ( Vtx ` G ) $.
    usgrlimprop.w $e |- W = ( Vtx ` H ) $.
    usgrlimprop.n $e |- N = ( G ClNeighbVtx v ) $.
    usgrlimprop.m $e |- M = ( H ClNeighbVtx ( F ` v ) ) $.
    usgrlimprop.i $e |- I = ( Edg ` G ) $.
    usgrlimprop.j $e |- J = ( Edg ` H ) $.
    usgrlimprop.k $e |- K = { x e. I | x C_ N } $.
    usgrlimprop.l $e |- L = { x e. J | x C_ M } $.
    $( Properties of a local isomorphism of simple pseudographs.  (Contributed
       by AV, 17-Aug-2025.) $)
    usgrlimprop $p |- ( ( G e. USPGraph /\ H e. USPGraph
                          /\ F e. ( G GraphLocIso H ) )
               -> ( F : V -1-1-onto-> W /\ A. v e. V E. f ( f : N -1-1-onto-> M
                        /\ E. g ( g : K -1-1-onto-> L
                                  /\ A. e e. K ( f " e ) = ( g ` e ) ) ) ) ) $=
      ( cuspgr wcel cgrlim co w3a wf1o cv cima cfv wceq wral wex simp3 uspgrlim
      wa mpbid ) GUEUFZHUEUFZFGHUGUHZUFZUIVDOPFUJNMDUKZUJKLEUKZUJVECUKZULVGVFUM
      UNCKUOUSEUPUSDUPBOUOUSVAVBVDUQABCDEFGHIJKLMNOPVCQRSTUAUBUCUDURUT $.
  $}

  ${
    $d E x $.  $d I x $.  $d N x $.
    clnbgrvtxedg.n $e |- N = ( G ClNeighbVtx A ) $.
    clnbgrvtxedg.i $e |- I = ( Edg ` G ) $.
    clnbgrvtxedg.k $e |- K = { x e. I | x C_ N } $.
    $( An edge ` E ` containing a vertex ` A ` is an edge in the closed
       neighborhood of this vertex ` A ` .  (Contributed by AV,
       25-Dec-2025.) $)
    clnbgrvtxedg $p  |- ( ( G e. UHGraph /\ E e. I /\ A e. E ) -> E e. K ) $=
      ( cuhgr wcel w3a wss simp2 clnbgrssedg cv sseq1 elrab2 sylanbrc ) DKLZCEL
      ZBCLZMUBCGNZCFLUAUBUCOEDCGBIHPAQZGNUDACEFUECGRJST $.

    $d A e g x $.  $d A f v $.  $d E e f g $.  $d F e g $.  $d F f v $.
    $d F v x y $.  $d G e f g y $.  $d G e g v y $.  $d G e g x $.
    $d H e f g $.  $d H v $.  $d H x y $.  $d I e g v y $.  $d I f $.
    $d J g v $.  $d J x y $.  $d V y $.
    grlimedgclnbgr.m $e |- M = ( H ClNeighbVtx ( F ` A ) ) $.
    grlimedgclnbgr.j $e |- J = ( Edg ` H ) $.
    grlimedgclnbgr.l $e |- L = { x e. J | x C_ M } $.
    $( For two locally isomorphic graphs ` G ` and ` H ` and a vertex ` A ` of
       ` G ` there are two bijections ` f ` and ` g ` mapping the closed
       neighborhood ` N ` of ` A ` onto the closed neighborhood ` M ` of
       ` ( F `` A ) ` and the edges between the vertices in ` N ` onto the
       edges between the vertices in ` M ` , so that the mapped vertices of an
       edge ` E ` containing the vertex ` A ` is an edge between the vertices
       in ` M ` .  (Contributed by AV, 25-Dec-2025.) $)
    grlimedgclnbgr $p  |- ( ( ( G e. USPGraph /\ H e. USPGraph )
                              /\ F e. ( G GraphLocIso H )
                              /\ ( E e. I /\ A e. E ) )
                            -> E. f E. g ( f : N -1-1-onto-> M
                                           /\ g : K -1-1-onto-> L
                                           /\ ( f " E ) = ( g ` E ) ) ) $=
      ( vv ve vy cuspgr wcel wa cgrlim co w3a cvtx cfv wf1o cv cclnbgr wss crab
      cima wceq wral simp1l simp1r simp2 eqid sseq1 cbvrabv usgrlimprop syl3anc
      wex wi cuhgr cedg uspgruhgr adantr 3ad2ant1 eleq2i birani 3ad2ant3 simp3r
      uhgredgrnv eqidd oveq2 fveq2 oveq2d sseq2d rabbidv raleqdv anbi12d exbidv
      f1oeq123d rspcv syl weq wb a1i ax-mp biimpri adantl sseq2i rabbieq simp3l
      id clnbgrvtxedg imaeq2 eqeq12d adantld imp 3jca eximdv expimpd syld mpd
      ex ) GUDUEZHUDUEZUFZFGHUGUHUEZEIUEZBEUEZUFZUIZGUJUKZHUJUKZFULZGUAUMZUNUHZ
      HYDFUKZUNUHZCUMZULZAUMZYEUOZAIUPZYJYGUOZAJUPZDUMZULZYHUBUMZUQZYQYOUKZURZU
      BYLUSZUFZDVHZUFZCVHZUAYAUSZUFZNMYHULZKLYOULZYHEUQZEYOUKZURZUIZDVHZCVHZXTX
      MXNXPUUGXMXNXPXSUTXMXNXPXSVAXOXPXSVBUCUAUBCDFGHIJYLYNYGYEYAYBYAVCYBVCYEVC
      YGVCPSYKUCUMZYEUOAUCIYJUUPYEVDVEYMUUPYGUOAUCJYJUUPYGVDVEVFVGXTUUFUUOYCXTU
      UFGBUNUHZHBFUKZUNUHZYHULZYJUUQUOZAIUPZYJUUSUOZAJUPZYOULZYTUBUVBUSZUFZDVHZ
      UFZCVHZUUOXTBYAUEZUUFUVJVIXTGVJUEZEGVKUKZUEZXRUVKXOXPUVLXSXMUVLXNGVLVMVNZ
      XSXOUVNXPXQUVNXRIUVMEPVOVPVQXOXPXQXRVRZEGBVSVGUUEUVJUABYAYDBURZUUDUVICUVQ
      YIUUTUUCUVHUVQYEUUQYGUUSYHYHUVQYHVTYDBGUNWAZUVQYFUURHUNYDBFWBWCZWIUVQUUBU
      VGDUVQYPUVEUUAUVFUVQYLUVBYNUVDYOYOUVQYOVTUVQYKUVAAIUVQYEUUQYJUVRWDWEZUVQY
      MUVCAJUVQYGUUSYJUVSWDWEWIUVQYTUBYLUVBUVTWFWGWHWGWHWJWKXTUVIUUNCXTUUTUVHUU
      NXTUUTUFZUVGUUMDUWAUVGUUMUWAUVGUFUUHUUIUULUWAUUHUVGUUTUUHXTUUHUUTCCWLZUUH
      UUTWMYHVCUWBNUUQMUUSYHYHUWBXANUUQURUWBOWNMUUSURUWBRWNWIWOWPWQVMUVGUUIUWAU
      VEUUIUVFUUIUVEDDWLZUUIUVEWMYOVCUWCKUVBLUVDYOYOUWCXAKUVBURUWCYJNUOUVAAIKQN
      UUQYJOWRWSWNLUVDURUWCYJMUOUVCAJLTMUUSYJRWRWSWNWIWOWPVMWQUWAUVGUULXTUVGUUL
      VIUUTXTUVFUULUVEXTEUVBUEZUVFUULVIXTUVLXQXRUWDUVOXOXPXQXRWTUVPABEGIUVBUUQU
      UQVCPUVBVCXBVGYTUULUBEUVBYQEURYRUUJYSUUKYQEYHXCYQEYOWBXDWJWKXEVMXFXGXLXHX
      IXHXJXEXK $.

    $d B f g $.  $d B x $.  $d V f g $.  $d W f g $.
    $( For two locally isomorphic graphs ` G ` and ` H ` and a vertex ` A ` of
       ` G ` there are two bijections ` f ` and ` g ` mapping the closed
       neighborhood ` N ` of ` A ` onto the closed neighborhood ` M ` of
       ` ( F `` A ) ` and the edges between the vertices in ` N ` onto the
       edges between the vertices in ` M ` , so that the mapped vertices of an
       edge ` { A , B } ` containing the vertex ` A ` is an edge between the
       vertices in ` M ` .  (Contributed by AV, 25-Dec-2025.) $)
    grlimprclnbgr $p  |- ( ( ( G e. USPGraph /\ H e. USPGraph )
                             /\ F e. ( G GraphLocIso H )
                             /\ ( A e. V /\ B e. W /\ { A , B } e. I ) )
         -> E. f E. g ( f : N -1-1-onto-> M
                        /\ g : K -1-1-onto-> L
                        /\ { ( f ` A ) , ( f ` B ) } = ( g ` { A , B } ) ) ) $=
      ( cuspgr wcel wa cgrlim co cpr w3a cv wf1o cima cfv wceq wex simp3 prid1g
      3ad2ant1 jca grlimedgclnbgr syl3an3 simpr1 simpr2 wi f1ofn adantl cclnbgr
      wfn cvtx cuhgr uspgruhgr adantr eleq2i biimpi 3ad2ant3 uhgredgrnv syl3anc
      cedg eqid clnbgrvtxel syl eleqtrrdi wo prcom eleq1i olcd uspgrupgr prid2g
      cupgr wb 3ad2ant2 3jca clnbupgrel mpbird fnimapr eqeq1d biimpd ex 2eximdv
      a1d 3imp2 mpd ) GUCUDZHUCUDZUEZFGHUFUGUDZBOUDZCPUDZBCUHZIUDZUIZUIZNMDUJZU
      KZKLEUJZUKZXMXIULZXIXOUMZUNZUIZEUODUOZXNXPBXMUMCXMUMUHZXRUNZUIZEUODUOXKXE
      XFXJBXIUDZUEYAXKXJYEXGXHXJUPXGXHYEXJBCOUQURZUSABDEXIFGHIJKLMNQRSTUAUBUTVA
      XLXTYDDEXLXTYDXLXTUEXNXPYCXLXNXPXSVBXLXNXPXSVCXLXNXPXSYCXLXNXPXSYCVDZVDXL
      XNUEZYGXPYHXSYCYHXQYBXRYHXMNVHZBNUDCNUDXQYBUNXNYIXLNMXMVEVFYHBGBVGUGZNYHB
      GVIUMZUDZBYJUDXLYLXNXLGVJUDZXIGVRUMZUDZYEYLXEXFYMXKXCYMXDGVKVLURZXKXEYOXF
      XJXGYOXHXJYOIYNXIRVMVNVOVOZXKXEYEXFYFVOXIGBVPVQZVLGBYKYKVSZVTWAQWBYHCYJNY
      HCYJUDZCBUNZCBUHZIUDZWCZYHUUCUUAXLUUCXNXKXEUUCXFXJXGUUCXHXJUUCXIUUBIBCWDW
      EVNVOVOVLWFYHGWIUDZYLCYKUDZUIZYTUUDWJXLUUGXNXLUUEYLUUFXEXFUUEXKXCUUEXDGWG
      VLURYRXLYMYOCXIUDZUUFYPYQXKXEUUHXFXHXGUUHXJBCPWHWKVOXIGCVPVQWLVLIGBCYKYSR
      WMWAWNQWBNBCXMWOVQWPWQWTWRXAWLWRWSXB $.

    $d L g $.  $d M g $.  $d N g $.
    $( For two locally isomorphic graphs ` G ` and ` H ` and a vertex ` A ` of
       ` G ` there is a bijection ` f ` mapping the closed neighborhood ` N `
       of ` A ` onto the closed neighborhood ` M ` of ` ( F `` A ) ` , so that
       the mapped vertices of an edge ` { A , B } ` containing the vertex ` A `
       is an edge between the vertices in ` M ` .  (Contributed by AV,
       27-Dec-2025.) $)
    grlimprclnbgredg $p  |- ( ( ( G e. USPGraph /\ H e. USPGraph )
                                /\ F e. ( G GraphLocIso H )
                                /\ ( A e. V /\ B e. W /\ { A , B } e. I ) )
                              -> E. f ( f : N -1-1-onto-> M
                                       /\ { ( f ` A ) , ( f ` B ) } e. L ) ) $=
      ( vg cuspgr wcel wa cgrlim cpr w3a wf1o cfv wceq wex grlimprclnbgr simpr1
      co cv wf 3ad2ant2 adantl uspgruhgr adantr 3ad2ant1 simp33 prid1g 3ad2ant3
      f1of cuhgr 3jca clnbgrvtxedg syl ffvelcdmd wb eleq1 mpbird jca ex exlimdv
      eximdv mpd ) FUCUDZGUCUDZUEZEFGUFUOUDZBNUDZCOUDZBCUGZHUDZUHZUHZMLDUPZUIZJ
      KUBUPZUIZBWJUJCWJUJUGZWFWLUJZUKZUHZUBULZDULWKWNKUDZUEZDULABCDUBEFGHIJKLMN
      OPQRSTUAUMWIWRWTDWIWQWTUBWIWQWTWIWQUEZWKWSWIWKWMWPUNXAWSWOKUDZXAJKWFWLWQJ
      KWLUQZWIWMWKXCWPJKWLVFURUSXAFVGUDZWGBWFUDZUHZWFJUDWIXFWQWIXDWGXEWBWCXDWHV
      TXDWAFUTVAVBWBWCWDWEWGVCWHWBXEWCWDWEXEWGBCNVDVBVEVHVAABWFFHJMPQRVIVJVKWQW
      SXBVLZWIWPWKXGWMWNWOKVMVEUSVNVOVPVQVRVS $.

    $d M x $.  $d f x $.
    $( For two locally isomorphic graphs ` G ` and ` H ` and a vertex ` A ` of
       ` G ` there is a bijection ` f ` mapping the closed neighborhood ` N `
       of ` A ` onto the closed neighborhood ` M ` of ` ( F `` A ) ` , so that
       the mapped vertices of an edge ` { A , B } ` containing the vertex ` A `
       is an edge in ` H ` .  (Contributed by AV, 27-Dec-2025.) $)
    grlimpredg $p  |- ( ( ( G e. USPGraph /\ H e. USPGraph )
                                /\ F e. ( G GraphLocIso H )
                                /\ ( A e. V /\ B e. W /\ { A , B } e. I ) )
                              -> E. f ( f : N -1-1-onto-> M
                                       /\ { ( f ` A ) , ( f ` B ) } e. J ) ) $=
      ( cuspgr wcel wa cgrlim co cpr w3a cv wf1o cfv wex grlimprclnbgredg sseq1
      wss elrab2 wi simpl a1i biimtrid imdistanda eximdv mpd ) FUBUCGUBUCUDEFGU
      EUFUCBNUCCOUCBCUGHUCUHUHZMLDUIZUJZBVEUKCVEUKUGZKUCZUDZDULVFVGIUCZUDZDULAB
      CDEFGHIJKLMNOPQRSTUAUMVDVIVKDVDVFVHVJVHVJVGLUOZUDZVDVFUDZVJAUIZLUOVLAVGIK
      VOVGLUNUAUPVMVJUQVNVJVLURUSUTVAVBVC $.

    $( For two locally isomorphic graphs ` G ` and ` H ` and a vertex ` A ` of
       ` G ` there is a bijection ` f ` mapping the closed neighborhood ` N `
       of ` A ` onto the closed neighborhood ` M ` of ` ( F `` A ) ` , so that
       the mapped vertices of an edge ` { A , B } ` containing the vertex ` A `
       is an edge between the vertices in ` M ` containing the vertex
       ` ( F `` A ) ` .  (Contributed by AV, 28-Dec-2025.) $)
    grlimprclnbgrvtx $p  |- ( ( ( G e. USPGraph /\ H e. USPGraph )
                                /\ F e. ( G GraphLocIso H )
                                /\ ( A e. V /\ B e. W /\ { A , B } e. I ) )
                         -> E. f ( f : N -1-1-onto-> M
                                   /\ ( { ( F ` A ) , ( f ` B ) } e. L
                                     \/ { ( F ` A ) , ( f ` A ) } e. L ) ) ) $=
      ( cuspgr wcel wa cgrlim co cpr w3a cv wf1o cfv wo grlimprclnbgredg simprl
      wex sseq1 elrab2 bilani adantl fvex prss wceq cupgr wi uspgrupgr 3ad2ant1
      wss ad2antrr cclnbgr eleq2i clnbupgreli ex biimtrid anim12d syl imp prcom
      preq1 eqtrid eleq1d biimpcd eleq1i cvtx pm3.2i simpr 3jca eqid upgrpredgv
      cvv 3syl clnbgrvtxel sylibr simplrr prssd sylanbrc orim12d orcomd adantld
      a1i mpd biimtrrid expimpd jca eximdv ) FUBUCZGUBUCZUDZEFGUEUFUCZBNUCCOUCB
      CUGHUCUHZUHZMLDUIZUJZBXKUKZCXKUKZUGZKUCZUDZDUOXLBEUKZXNUGZKUCZXRXMUGZKUCZ
      ULZUDZDUOABCDEFGHIJKLMNOPQRSTUAUMXJXQYDDXJXQYDXJXQUDZXLYCXJXLXPUNYEXOIUCZ
      XOLVGZUDZYCXQYHXJXPYHXLAUIZLVGZYGAXOIKYIXOLUPUAUQURUSYEYFYGYCYGXMLUCZXNLU
      CZUDZYEYFUDZYCXMXNLBXKUTCXKUTZVAYNYMYCYNYMUDZXMXRVBXMXRUGIUCULZXNXRVBZXNX
      RUGZIUCZULZUDZYCYNYMUUBYNGVCUCZYMUUBVDXJUUCXQYFXGXHUUCXIXFUUCXEGVEUSVFVHZ
      UUCYKYQYLUUAYKXMGXRVIUFZUCZUUCYQLUUEXMSVJUUCUUFYQIGXRXMTVKVLVMYLXNUUEUCZU
      UCUUALUUEXNSVJUUCUUGUUAIGXRXNTVKVLVMVNVOVPYPUUAYCYQYPUUAYCYPUUAUDYBXTYPUU
      AYBXTULYPYRYBYTXTYEYRYBVDZYFYMXQUUHXJXPUUHXLYRXPYBYRXOYAKYRXOXNXMUGYAXMXN
      VQXNXRXMVRVSVTWAUSUSVHYPYTXTYPYTUDZXSIUCZXSLVGZXTYTUUJYPYSXSIXNXRVQWBURUU
      IXRXNLUUIXRGWCUKZUCZXRLUCZUUIUUCXNWIUCZXRWIUCZUDZYTUHXNUULUCZUUMUDUUMUUIU
      UCUUQYTYNUUCYMYTUUDVHUUQUUIUUOUUPYOBEUTWDWSYPYTWEWFWIIGXNXRUULWIUULWGZTWH
      UURUUMWEWJUUMXRUUEUCUUNGXRUULUUSWKLUUEXRSVJWLVOYNYKYLYTWMWNYJUUKAXSIKYIXS
      LUPUAUQWOVLWPVPWQVLWRWTVLXAXBWTXCVLXDWT $.
  $}

  ${
    $d A f v x $.  $d B f v x $.  $d E f v x $.  $d F f v x $.  $d G f v x $.
    $d H f v x $.  $d I f x $.  $d V f v $.  $d X f $.  $d Y f $.  $d ph f v $.
    grlimgredgex.i $e |- I = ( Edg ` G ) $.
    grlimgredgex.e $e |- E = ( Edg ` H ) $.
    grlimgredgex.v $e |- V = ( Vtx ` H ) $.
    grlimgredgex.a $e |- ( ph -> A e. X ) $.
    grlimgredgex.b $e |- ( ph -> B e. Y ) $.
    grlimgredgex.p $e |- ( ph -> { A , B } e. I ) $.
    grlimgredgex.g $e |- ( ph -> G e. USPGraph ) $.
    grlimgredgex.h $e |- ( ph -> H e. USPGraph ) $.
    grlimgredgex.f $e |- ( ph -> F e. ( G GraphLocIso H ) ) $.
    $( Local isomorphisms between simple pseudographs map an edge onto an edge
       with an endpoint being the image of one of the endpoints of the first
       edge under the local isomorphism.  (Contributed by AV, 28-Dec-2025.) $)
    grlimgredgex $p |- ( ph -> E. v e. V { ( F ` A ) , v } e. E ) $=
      ( vf vx cclnbgr co cfv cv wf1o cpr wss crab wcel wo wa wrex cuspgr cgrlim
      wex eqid grlimprclnbgrvtx syl213anc wf f1of adantl cvtx w3a uspgrupgr syl
      cupgr jca 3jca upgrpredgv simpr 3syl simpl predgclnbgrel adantr ffvelcdmd
      syl3anc clnbgrisvtx wceq wb preq2 eleq1d sseq1 elrab rspcedvd clnbgrvtxel
      simplbi ex jaod expimpd exlimdv mpd ) AGCUDUEZHCFUFZUDUEZUBUGZUHZWPDWRUFZ
      UIZUCUGZWQUJZUCEUKZULZWPCWRUFZUIZXDULZUMZUNZUBURZWPBUGZUIZEULZBJUOZAGUPUL
      ZHUPULFGHUQUEULCKULZDLULZCDUIIULZXKSTUAPQRUCCDUBFGHIEXBWOUJUCIUKZXDWQWOKL
      WOUSMXTUSWQUSNXDUSUTVAAXJXOUBAWSXIXOAWSUNZXEXOXHYAXEXOYAXEUNZXNXAEULZBWTJ
      YAWTJULZXEYAWTWQULYDYAWOWQDWRWSWOWQWRVBAWOWQWRVCVDZADWOULZWSADGVEUFZULZCY
      GULZXSYFAGVIULZXQXRUNZXSVFZYIYHUNZYHAYJYKXSAXPYJSGVGVHAXQXRPQVJRVKZKIGCDY
      GLYGUSZMVLZYIYHVMVNAYLYMYIYNYPYIYHVOVNZRIGDYGCYOMVPVSVQVRHWPWTJOVTVHVQXLW
      TWAZXNYCWBYBYRXMXAEXLWTWPWCWDVDXEYCYAXEYCXAWQUJZXCYSUCXAEXBXAWQWEWFWIVDWG
      WJYAXHXOYAXHUNZXNXGEULZBXFJYAXFJULZXHYAXFWQULUUBYAWOWQCWRYEACWOULZWSAYIUU
      CYQGCYGYOWHVHVQVRHWPXFJOVTVHVQXLXFWAZXNUUAWBYTUUDXMXGEXLXFWPWCWDVDXHUUAYA
      XHUUAXGWQUJZXCUUEUCXGEXBXGWQWEWFWIVDWGWJWKWLWMWN $.
  $}

  ${
    $d I x $.  $d N x $.  $d a x $.  $d b x $.  $d c x $.
    grlimgrtrilem1.v $e |- V = ( Vtx ` G ) $.
    grlimgrtrilem1.n $e |- N = ( G ClNeighbVtx a ) $.
    grlimgrtrilem1.i $e |- I = ( Edg ` G ) $.
    grlimgrtrilem1.k $e |- K = { x e. I | x C_ N } $.
    $( Lemma 3 for ~ grlimgrtri .  (Contributed by AV, 24-Aug-2025.)  (Proof
       shortened by AV, 27-Dec-2025.) $)
    grlimgrtrilem1 $p  |- ( ( G e. UHGraph /\ ( { a , b } e. I
                                        /\ { a , c } e. I /\ { b , c } e. I ) )
                 -> ( { a , b } e. K /\ { a , c } e. K /\ { b , c } e. K ) ) $=
      ( wcel cv cpr w3a vex a1i 3jca cuhgr wa simpl adantl clnbgrvtxedg syl3anc
      simp1 prid1 simp2 wss simpr3 prid2 clnbgredg sylan2 prssd elrab2 sylanbrc
      sseq1 ) BUANZGOZHOZPZCNZUTIOZPZCNZVAVDPZCNZQZUBZVBDNZVEDNZVGDNZVJUSVCUTVB
      NZVKUSVIUCZVIVCUSVCVFVHUGZUDVNVJUTVAGRZUHZSAUTVBBCDEKLMUEUFVJUSVFUTVENZVL
      VOVIVFUSVCVFVHUIZUDVSVJUTVDVQUHZSAUTVEBCDEKLMUEUFVJVHVGEUJZVMUSVCVFVHUKVJ
      VAVDEVIUSVCVNVAVBNZQVAENVIVCVNWCVPVNVIVRSWCVIUTVAHRULSTCBVBEUTVALKUMUNVIU
      SVFVSVDVENZQVDENVIVFVSWDVTVSVIWASWDVIUTVDIRULSTCBVEEUTVDLKUMUNUOAOZEUJWBA
      VGCDWEVGEURMUPUQT $.

    $d J x $.  $d K i $.  $d b i $.  $d c i $.  $d f i $.  $d g i $.
    grlimgrtrilem2.m $e |- M = ( H ClNeighbVtx ( F ` a ) ) $.
    grlimgrtrilem2.j $e |- J = ( Edg ` H ) $.
    grlimgrtrilem2.l $e |- L = { x e. J | x C_ M } $.
    $( Lemma 3 for ~ grlimgrtri .  (Contributed by AV, 23-Aug-2025.) $)
    grlimgrtrilem2 $p  |- ( ( ( f : N -1-1-onto-> M /\ g : K -1-1-onto-> L )
                         /\ A. i e. K ( f " i ) = ( g ` i ) /\ { b , c } e. K )
                            -> { ( f ` b ) , ( f ` c ) } e. J ) $=
      ( cv cpr wcel cima cfv wceq wral wf1o wa imaeq2 fveq2 eqeq12d rspcv f1ofn
      wfn adantr adantl wss crab eleq2i sseq1 elrab bitri vex prss simpl sylbir
      wi simplbiim simpr fnimapr syl3anc eqeq1d ssrab2 eqsstri ffvelcdmd sselid
      wf f1of eleq1 syl5ibrcom sylbid ex com23 syld 3imp31 ) PUEZQUEZUFZJUGZBUE
      ZDUEZUHZWPCUEZUIZUJZDJUKZMLWOULZJKWRULZUMZWKWOUIWLWOUIUFZIUGZWNXAWOWMUHZW
      MWRUIZUJZXDXFVLWTXIDWMJWPWMUJWQXGWSXHWPWMWOUNWPWMWRUOUPUQWNXDXIXFWNXDXIXF
      VLWNXDUMZXIXEXHUJZXFXJXGXEXHXJWOMUSZWKMUGZWLMUGZXGXEUJXDXLWNXBXLXCMLWOURU
      TVAWNXMXDWNWMHUGZWMMVBZXMWNWMAUEZMVBZAHVCZUGXOXPUMJXSWMUAVDXRXPAWMHXQWMMV
      EVFVGZXPXMXNUMZXMWKWLMPVHQVHVIZXMXNVJVKVMUTWNXNXDWNXOXPXNXTXPYAXNYBXMXNVN
      VKVMUTMWKWLWOVOVPVQXJXFXKXHIUGXJKIXHKXQLVBZAIVCIUDYCAIVRVSXJJKWMWRXDJKWRW
      BZWNXCYDXBJKWRWCVAVAWNXDVJVTWAXEXHIWDWEWFWGWHWIWJ $.
  $}

  ${
    $d F a b c f g i v x y z $.  $d G a b c f g v i x y $.
    $d H a b c f g i t v x y z $.  $d T a b c f g x y z $.  $d ph a b c f g $.
    grlimgrtri.g $e |- ( ph -> G e. USPGraph ) $.
    grlimgrtri.h $e |- ( ph -> H e. USPGraph ) $.
    grlimgrtri.n $e |- ( ph -> F e. ( G GraphLocIso H ) ) $.
    grlimgrtri.t $e |- ( ph -> T e. ( GrTriangles ` G ) ) $.
    $( If one of two locally isomorphic graphs has a triangle, so does the
       other.  The triangle in the other graph is not necessarily the image
       ` ( F " T ) ` of the triangle ` T ` in the first graph.  (Contributed by
       AV, 24-Aug-2025.) $)
    grlimgrtri $p |- ( ph -> E. t t e. ( GrTriangles ` H ) ) $=
      ( vy va cv wceq cfv cpr wcel w3a wi wa vx vz vb vc vv vf vg vi chash cedg
      ctp c3 cvtx wrex wex cgrtri eqid grtriprop syl cuspgr cgrlim wf1o cclnbgr
      co crab cima wral 3jca sseq1 cbvrabv usgrlimprop eqidd oveq2 fveq2 oveq2d
      wss f1oeq123d sseq2d rabbidv raleqdv anbi12d exbidv rspcv 3ad2ant1 adantl
      cvv a1i wf1 f1of1 3ad2ant2 clnbgrvtxel adantr simplr simpll predgclnbgrel
      tpex simpr syl3anc 2a1d ex 3impd 3adant3 imp 3adant2 3imp 3simpa 3ad2ant3
      a1d grtrimap sylc tpeq1 eqeq2d preq1 eleq1d 3anbi12d 3anbi13d tpeq2 preq2
      jca tpeq3 3anbi23d clnbgrisvtx eqcoms simp3 eqtrd cuhgr uspgruhgr anim12i
      grlimgrtrilem1 grlimgrtrilem2 3expia anasss ancoms 3rspcedvdw mpdan eqeq1
      3anim123d mpd fveqeq2 exlimdv rexbidv 2rexbidv spcedv 3expd impcomd com13
      3exp syld 3syl anabsi5 rexlimdvvva isgrtri exbii sylibr ) ABMZUAMZKMZUBMZ
      UKZNZUUOUIOULNZUUPUUQPZFUJOZQZUUPUURPZUVCQZUUQUURPZUVCQZRZRZUBFUMOZUNZKUV
      KUNUAUVKUNZBUOZUUOFUPOQZBUOACLMZUCMZUDMZUKNZCUIOULNZUVPUVQPZEUJOZQZUVPUVR
      PZUWBQZUVQUVRPZUWBQZRZRZUDEUMOZUNUCUWJUNLUWJUNZUVNACEUPOQUWKJLUCUDCUWBEUW
      JUWJUQZUWBUQZURUSAUWIUVNLUCUDUWJUWJUWJAUVPUWJQZUVQUWJQZUVRUWJQZRZUWIUVNSZ
      AEUTQZFUTQZDEFVAVDQZRUWJUVKDVBZEUEMZVCVDZFUXCDOZVCVDZUFMZVBZUUQUXDVPZKUWB
      VEZUUQUXFVPZKUVCVEZUGMZVBZUXGUHMZVFUXOUXMONZUHUXJVGZTZUGUOZTZUFUOZUEUWJVG
      ZTAUWQTZUWRSZAUWSUWTUXAGHIVHUAUEUHUFUGDEFUWBUVCUXJUXLUXFUXDUWJUVKUWLUVKUQ
      ZUXDUQUXFUQUWMUVCUQZUXIUUPUXDVPKUAUWBUUQUUPUXDVIVJUXKUUPUXFVPKUAUVCUUQUUP
      UXFVIVJVKUXBUYBUYDUYCUYBUXBUWRUYCUYBEUVPVCVDZFUVPDOZVCVDZUXGVBZUUQUYGVPZK
      UWBVEZUUQUYIVPZKUVCVEZUXMVBZUXPUHUYLVGZTZUGUOZTZUFUOZUXBUWRSZUWQUYBUYTSZA
      UWNUWOVUBUWPUYAUYTUEUVPUWJUXCUVPNZUXTUYSUFVUCUXHUYJUXSUYRVUCUXDUYGUXFUYIU
      XGUXGVUCUXGVLUXCUVPEVCVMZVUCUXEUYHFVCUXCUVPDVNVOZVQVUCUXRUYQUGVUCUXNUYOUX
      QUYPVUCUXJUYLUXLUYNUXMUXMVUCUXMVLVUCUXIUYKKUWBVUCUXDUYGUUQVUDVRVSZVUCUXKU
      YMKUVCVUCUXFUYIUUQVUEVRVSVQVUCUXPUHUXJUYLVUFVTWAWBWAWBWCWDWEUYCUYSVUAUFUY
      CUYRUYJVUAUYCUYQUYJVUASUGUYCUYQUYJUXBUWRUYCUYQUYJUXBRZUWIUVNUYCVUGUWIRZUV
      MUVPUXGOZUVQUXGOZUVRUXGOZUKZUUSNZVULUIOZULNZUVIRZUBUVKUNZKUVKUNUAUVKUNZBW
      FVULVULWFQVUHVUIVUJVUKWPWGVUHVUIUYIQZVUJUYIQZVUKUYIQZRZUXGCVFZVULNZVVCUIO
      ZULNZRZVURVUHUYGUYIUXGWHZUVPUYGQZUVQUYGQZUVRUYGQZRZUVSUVTTZTVVGVUGUYCVVHU
      WIUYJUYQVVHUXBUYGUYIUXGWIWJWJVUHVVLVVMUYCVUGUWIVVLUWQVUGUWIVVLSZSAUWQVVNV
      UGUWQUVSUVTUWHVVLUWQUWHVVLSUVSUVTUWQUWHVVLUWQUWHTVVIVVJVVKUWQVVIUWHUWNUWO
      VVIUWPEUVPUWJUWLWKWDWLUWQUWHVVJUWNUWOUWHVVJSUWPUWNUWOTZUWCUWEUWGVVJVVOUWC
      UWEUWGVVJSSVVOUWCTZVVJUWEUWGVVPUWOUWNUWCVVJUWNUWOUWCWMUWNUWOUWCWNVVOUWCWQ
      UWBEUVQUWJUVPUWLUWMWOWRWSWTXAXBXCUWQUWHVVKUWNUWPUWHVVKSUWOUWNUWPTZUWCUWEU
      WGVVKVVQUWEUWGVVKSZSUWCVVQUWEVVRVVQUWETZVVKUWGVVSUWPUWNUWEVVKUWNUWPUWEWMU
      WNUWPUWEWNVVQUWEWQUWBEUVRUWJUVPUWLUWMWOWRXHWTXHXAXDXCVHWTWSXAXHWEXEUWIUYC
      VVMVUGUVSUVTUWHXFXGXSCUXGUYGUYILUCUDXIXJVUHVVGTZVUPVULVUIUUQUURUKZNZVUOVU
      IUUQPZUVCQZVUIUURPZUVCQZUVHRZRVULVUIVUJUURUKZNZVUOVUIVUJPZUVCQZVWFVUJUURP
      ZUVCQZRZRVULVULNZVUOVWKVUIVUKPZUVCQZVUJVUKPZUVCQZRZRUAKUBVUIVUJVUKUVKUVKU
      VKUUPVUINZVUMVWBUVIVWGVUOVXAUUSVWAVULUUPVUIUUQUURXKXLVXAUVDVWDUVFVWFUVHVX
      AUVBVWCUVCUUPVUIUUQXMXNVXAUVEVWEUVCUUPVUIUURXMXNXOXPUUQVUJNZVWBVWIVWGVWNV
      UOVXBVWAVWHVULUUQVUJVUIUURXQXLVXBVWDVWKUVHVWMVWFVXBVWCVWJUVCUUQVUJVUIXRXN
      VXBUVGVWLUVCUUQVUJUURXMXNXPXPUURVUKNZVWIVWOVWNVWTVUOVXCVWHVULVULUURVUKVUI
      VUJXTXLVXCVWFVWQVWMVWSVWKVXCVWEVWPUVCUURVUKVUIXRXNVXCVWLVWRUVCUURVUKVUJXR
      XNYAXPVVGVUIUVKQZVUHVVBVVDVXDVVFVUSVUTVXDVVAFUYHVUIUVKUYEYBWDWDWEVVGVUJUV
      KQZVUHVVBVVDVXEVVFVUTVUSVXEVVAFUYHVUJUVKUYEYBWJWDWEVVGVUKUVKQZVUHVVBVVDVX
      FVVFVVAVUSVXFVUTFUYHVUKUVKUYEYBXGWDWEVVTVWOVUOVWTVVTVULVLVVGVUOVUHVVGVUNV
      VEULVVDVVBVUNVVENZVVFVXGVULVVCVULVVCUIVNYCWJVVBVVDVVFYDYEWEVVTUWAUYLQZUWD
      UYLQZUWFUYLQZRZVWTVVTEYFQZUWHTZVXKVUHVXMVVGUYCUWIVXMVUGUYCVXLUWIUWHAVXLUW
      QAUWSVXLGEYGUSWLUVSUVTUWHYDYHXDWLKEUWBUYLUYGUWJLUCUDUWLUYGUQZUWMUYLUQZYIU
      SVUHVXKVWTSZVVGVUGUYCVXPUWIUYQUYJVXPUXBUYJUYQVXPUYJUYOUYPVXPUYJUYOTZUYPTV
      XHVWKVXIVWQVXJVWSVXQUYPVXHVWKKUFUGUHDEFUWBUVCUYLUYNUYIUYGUWJLLUCUWLVXNUWM
      VXOUYIUQZUYFUYNUQZYJYKVXQUYPVXIVWQKUFUGUHDEFUWBUVCUYLUYNUYIUYGUWJLLUDUWLV
      XNUWMVXOVXRUYFVXSYJYKVXQUYPVXJVWSKUFUGUHDEFUWBUVCUYLUYNUYIUYGUWJLUCUDUWLV
      XNUWMVXOVXRUYFVXSYJYKYQYLYMXBWJWLYRVHYNYOUUOVULNZUVLVUQUAKUVKUVKVXTUVJVUP
      UBUVKVXTUUTVUMUVAVUOUVIUUOVULUUSYPUUOVULULUIYSXOUUAUUBUUCUUGUUDYTUUEYTUUH
      UUFXCUUIUUJUUKYRUVOUVMBUAKUBUUOUVCFUVKUYEUYFUULUUMUUN $.
  $}

  $( The relation "is locally isomorphic to" for graphs.  (Contributed by AV,
     9-Jun-2025.) $)
  brgrlic $p |- ( R ~=lgr S <-> ( R GraphLocIso S ) =/= (/) ) $=
    ( cgrlic cgrlim cvv cxp df-grlic grlimfn brwitnlem ) ABCDEEFGHI $.

  $( Prove that two graphs are locally isomorphic by an explicit local
     isomorphism.  (Contributed by AV, 9-Jun-2025.) $)
  brgrilci $p |- ( F e. ( R GraphLocIso S ) -> R ~=lgr S ) $=
    ( cgrlim co wcel c0 wne cgrlic wbr ne0i brgrlic sylibr ) CABDEZFNGHABIJNCKA
    BLM $.

  $( The "is locally isomorphic to" relation for graphs is a relation.
     (Contributed by AV, 9-Jun-2025.) $)
  grlicrel $p |- Rel ~=lgr $=
    ( cgrlic cvv cxp wss wrel cgrlim ccnv c1o cdif cima df-grlic cnvimass fndmi
    cdm grlimfn sseqtri eqsstri relxp relss mp2 ) ABBCZDUAEAEAFGBHIZJZUAKUCFNUA
    FUBLUAFOMPQBBRAUAST $.

  $( Reverse closure of the "is locally isomorphic to" relation for graphs.
     (Contributed by AV, 9-Jun-2025.) $)
  grlicrcl $p |- ( G ~=lgr S -> ( G e. _V /\ S e. _V ) ) $=
    ( cgrlic wbr cgrlim co c0 wne cvv wcel wa brgrlic grlimdmrel ovprc necon1ai
    sylbi ) BACDBAEFZGHBIJAIJKZBALRQGBAEMNOP $.

  ${
    $d G f v $.  $d H f v $.  $d V v $.  $d X f $.  $d Y f $.
    dfgrlic2.v $e |- V = ( Vtx ` G ) $.
    dfgrlic2.w $e |- W = ( Vtx ` H ) $.
    $( Alternate, explicit definition of the "is locally isomorphic to"
       relation for two graphs.  (Contributed by AV, 9-Jun-2025.) $)
    dfgrlic2 $p |- ( ( G e. X /\ H e. Y )
                       -> ( G ~=lgr H <-> E. f ( f : V -1-1-onto-> W
                 /\ A. v e. V ( G ISubGr ( G ClNeighbVtx v ) )
                         ~=gr ( H ISubGr ( H ClNeighbVtx ( f ` v ) ) ) ) ) ) $=
      ( cgrlic wbr cv cgrlim co wcel wex wa cclnbgr cisubgr wf1o cfv cgric wral
      c0 wne brgrlic n0 bitri wb cvv isgrlim el3v3 exbidv bitrid ) CDKLZBMZCDNO
      ZPZBQZCGPZDHPZRZEFUQUACCAMZSOTODDVDUQUBSOTOUCLAEUDRZBQUPURUEUFUTCDUGBURUH
      UIVCUSVEBVAVBUSVEUJBAUQCDEFGHUKIJULUMUNUO $.

    $( Implications of two graphs being locally isomorphic.  (Contributed by
       AV, 9-Jun-2025.) $)
    grilcbri $p |- ( G ~=lgr H -> E. f ( f : V -1-1-onto-> W
                   /\ A. v e. V ( G ISubGr ( G ClNeighbVtx v ) )
                           ~=gr ( H ISubGr ( H ClNeighbVtx ( f ` v ) ) ) ) ) $=
      ( cgrlic wbr cv wf1o cclnbgr co cisubgr cfv cgric wa cvv wcel wral wex wb
      grlicrcl dfgrlic2 syl ibi ) CDIJZEFBKZLCCAKZMNONDDUJUIPMNONQJAEUARBUBZUHC
      STDSTRUHUKUCDCUDABCDEFSSGHUEUFUG $.

    $d G f g i j v $.  $d G x $.  $d H g i j $.  $d H x $.  $d I i x $.
    $d J i x $.  $d K i $.  $d X g j v $.
    dfgrlic3.i $e |- I = ( iEdg ` G ) $.
    dfgrlic3.j $e |- J = ( iEdg ` H ) $.
    ${
      $d L i $.  $d M g i j $.  $d M x $.  $d N g i j $.  $d N x $.  $d X i $.
      $d Y i j g v $.
      dfgrlic3.n $e |- N = ( G ClNeighbVtx v ) $.
      dfgrlic3.m $e |- M = ( H ClNeighbVtx ( f ` v ) ) $.
      dfgrlic3.k $e |- K = { x e. dom I | ( I ` x ) C_ N } $.
      dfgrlic3.l $e |- L = { x e. dom J | ( J ` x ) C_ M } $.
      $( Alternate, explicit definition of the "is locally isomorphic to"
         relation for two graphs.  (Contributed by AV, 9-Jun-2025.) $)
      dfgrlic3 $p |- ( ( G e. X /\ H e. Y )
                       -> ( G ~=lgr H <-> E. f ( f : V -1-1-onto-> W
                                  /\ A. v e. V E. j ( j : N -1-1-onto-> M
                                  /\ E. g ( g : K -1-1-onto-> L
                                  /\ A. i e. K ( j " ( I ` i ) )
                                               = ( J ` ( g ` i ) ) ) ) ) ) ) $=
        ( cgrlic wbr cv cgrlim co wcel wex wa wf1o cfv cima wceq c0 wne brgrlic
        wral n0 bitri wb cvv isgrlim2 el3v3 exbidv bitrid ) GHUGUHZCUIZGHUJUKZU
        LZCUMZGQULZHRULZUNZOPVLUONMFUIZUOKLDUIZUOVSEUIZIUPUQWAVTUPJUPUREKVBUNDU
        MUNFUMBOVBUNZCUMVKVMUSUTVOGHVACVMVCVDVRVNWBCVPVQVNWBVECABFDEVLGHIJKLMNO
        PQRVFSTUCUDUAUBUEUFVGVHVIVJ $.
    $}

    $d I v $.  $d J v $.  $d K v $.  $d L v $.  $d M v $.  $d N v $.  $d X x $.
    $d f v x $.
    grilcbri2.n $e |- N = ( G ClNeighbVtx X ) $.
    grilcbri2.m $e |- M = ( H ClNeighbVtx ( f ` X ) ) $.
    grilcbri2.k $e |- K = { x e. dom I | ( I ` x ) C_ N } $.
    grilcbri2.l $e |- L = { x e. dom J | ( J ` x ) C_ M } $.
    $( Implications of two graphs being locally isomorphic.  (Contributed by
       AV, 9-Jun-2025.) $)
    grilcbri2 $p |- ( G ~=lgr H -> E. f ( f : V -1-1-onto-> W
                      /\ ( X e. V -> E. j ( j : N -1-1-onto-> M
                                  /\ E. g ( g : K -1-1-onto-> L
                                  /\ A. i e. K ( j " ( I ` i ) )
                                               = ( J ` ( g ` i ) ) ) ) ) ) ) $=
      ( vv cvv wcel wa cgrlic wbr cv wf1o cfv cima wceq wex wi cgrlim co c0 wne
      wral brgrlic grlimdmrel ovprc necon1ai cclnbgr wss cdm crab eqid dfgrlic3
      sylbi eqidd oveq2 eqtr4di oveq2d f1oeq123d sseq2d rabbidv raleqdv anbi12d
      fveq2 exbidv rspcv com12 a1i anim2d eximdv sylbid mpcom ) FUFUGGUFUGUHZFG
      UIUJZNOBUKZULZPNUGZMLEUKZULZJKCUKZULZWQDUKZHUMUNXAWSUMIUMUOZDJVBZUHZCUPZU
      HZEUPZUQZUHZBUPZWMFGURUSZUTVAWLFGVCWLXKUTFGURVDVEVFVMWLWMWOFUEUKZVGUSZGXL
      WNUMZVGUSZWQULZAUKZHUMZXMVHZAHVIZVJZXQIUMZXOVHZAIVIZVJZWSULZXBDYAVBZUHZCU
      PZUHZEUPZUENVBZUHZBUPXJAUEBCDEFGHIYAYEXOXMNOUFUFQRSTXMVKXOVKYAVKYEVKVLWLY
      MXIBWLYLXHWOYLXHUQWLWPYLXGYKXGUEPNXLPUOZYJXFEYNXPWRYIXEYNXMMXOLWQWQYNWQVN
      YNXMFPVGUSMXLPFVGVOUAVPZYNXOGPWNUMZVGUSLYNXNYPGVGXLPWNWCVQUBVPZVRYNYHXDCY
      NYFWTYGXCYNYAJYEKWSWSYNWSVNYNYAXRMVHZAXTVJJYNXSYRAXTYNXMMXRYOVSVTUCVPZYNY
      EYBLVHZAYDVJKYNYCYTAYDYNXOLYBYQVSVTUDVPVRYNXBDYAJYSWAWBWDWBWDWEWFWGWHWIWJ
      WK $.
  $}

  ${
    $d G f v $.
    $( Graph local isomorphism is reflexive for hypergraphs.  (Contributed by
       AV, 9-Jun-2025.) $)
    grlicref $p |- ( G e. UHGraph -> G ~=lgr G ) $=
      ( vf vv cuhgr wcel cgrlic wbr cvtx cfv cv wf1o cclnbgr cisubgr cgric wral
      co wa cvv oveq2d breq2d wex cid cres fvexd resiexd clnbgrssvtx isubgruhgr
      wss eqid a1i sylan2 gricref ralrimiva f1oi jctil wceq f1oeq1 fveq1 fvresi
      syl sylan9bb ralbidva anbi12d spcedv wb dfgrlic2 anidms mpbird ) ADEZAAFG
      ZAHIZVKBJZKZAACJZLPZMPZAAVNVLIZLPZMPZNGZCVKOZQZBUAZVIWBVKVKUBVKUCZKZVPVPN
      GZCVKOZQBRWDVIVKRVIAHUDUEVIWGWEVIWFCVKVIVNVKEZQVPDEZWFWHVIVOVKUHZWIWJWHAV
      NVKVKUIZUFUJVOAVKWKUGUKVPULUTUMVKUNUOVLWDUPZVMWEWAWGVKVKVLWDUQWLVTWFCVKWL
      VTVPAAVNWDIZLPZMPZNGWHWFWLVSWOVPNWLVRWNAMWLVQWMALVNVLWDURSSTWHWOVPVPNWHWN
      VOAMWHWMVNALVKVNUSSSTVAVBVCVDVIVJWCVECBAAVKVKDDWKWKVFVGVH $.

    $d S f g v w $.  $d G g w $.
    $( Graph local isomorphism is symmetric for hypergraphs.  (Contributed by
       AV, 9-Jun-2025.) $)
    grlicsym $p |- ( G e. UHGraph -> ( G ~=lgr S -> S ~=lgr G ) ) $=
      ( vf vv vg vw wbr wcel cfv cv wf1o cclnbgr co cisubgr cgric wa cvv oveq2d
      wral wi cgrlic cuhgr cvtx wex eqid grilcbri grlicrcl w3a ccnv cnvexg mp1i
      f1ocnv ad2antrr f1ocnvdm 3adant3 wceq oveq2 fveq2 breq12d rspcv f1ocnvfv2
      vex syl breq2d wss simp3 clnbgrssvtx isubgruhgr sylancl gricsym syld 3exp
      sylbid com24 imp31 ralrimiv jca f1oeq1 ralbidv anbi12d spcedv wb dfgrlic2
      fveq1 ancoms 3ad2ant3 mpbird com23 exlimiv sylc com12 ) BAUAGZBUBHZABUAGZ
      WLBUCIZAUCIZCJZKZBBDJZLMZNMZAAWSWQIZLMZNMZOGZDWOSZPZCUDBQHZAQHZPZWMWNTZDC
      BAWOWPWOUEZWPUEZUFABUGXGXJXKTCXGWMXJWNXGWMXJWNXGWMXJUHWNWPWOEJZKZAAFJZLMZ
      NMZBBXPXNIZLMZNMZOGZFWPSZPZEUDZXGWMYEXJXGWMPZYDWPWOWQUIZKZXRBBXPYGIZLMZNM
      ZOGZFWPSZPEQYGWQQHYGQHYFCVBWQQUJUKYFYHYMWRYHXFWMWOWPWQULUMYFYLFWPWRXFWMXP
      WPHZYLTWRYNWMXFYLWRYNWMXFYLTWRYNWMUHZXFYKAAYIWQIZLMZNMZOGZYLYOYIWOHZXFYST
      WRYNYTWMWOWPXPWQUNUOXEYSDYIWOWSYIUPZXAYKXDYROUUAWTYJBNWSYIBLUQRUUAXCYQANU
      UAXBYPALWSYIWQURRRUSUTVCYOYSYKXROGZYLYOYRXRYKOYOYQXQANYOYPXPALWRYNYPXPUPW
      MWOWPXPWQVAUORRVDYOYKUBHZUUBYLTYOWMYJWOVEUUCWRYNWMVFBYIWOXLVGYJBWOXLVHVIX
      RYKVJVCVMVKVLVNVOVPVQXNYGUPZXOYHYCYMWPWOXNYGVRUUDYBYLFWPUUDYAYKXROUUDXTYJ
      BNUUDXSYIBLXPXNYGWDRRVDVSVTWAUOXJXGWNYEWBZWMXIXHUUEFEABWPWOQQXMXLWCWEWFWG
      VLWHWIWJWK $.
  $}

  $( Graph local isomorphism is symmetric in both directions for hypergraphs.
     (Contributed by AV, 9-Jun-2025.) $)
  grlicsymb $p |- ( ( A e. UHGraph /\ B e. UHGraph )
                    -> ( A ~=lgr B <-> B ~=lgr A ) ) $=
    ( cuhgr wcel cgrlic wbr grlicsym anbiim ) ACDBCDABEFBAEFBAGABGH $.

  ${
    $d R f g h r $.  $d S g h r s $.  $d T f g h r s $.
    $( Graph local isomorphism is transitive.  (Contributed by AV,
       10-Jun-2025.) $)
    grlictr $p |- ( ( R ~=lgr S /\ S ~=lgr T ) -> R ~=lgr T ) $=
      ( vf vr vg vh vs wbr wa cvv wcel cfv cv cclnbgr co cisubgr cgric oveq2d
      wi cgrlic grlicrcl anim12i cvtx wf1o wral wex eqid grilcbri ccom vex coex
      a1i f1oco ad2ant2r f1of ffvelcdmda oveq2 fveq2 breq12d rspcv syl wf fvco3
      sylan eqcomd breq2d sylibd ex com3r imp31 anim1ci grictr ralimdva expimpd
      wceq adantl imp f1oeq1 fveq1 ralbidv anbi12d spcedv exlimiv syl2an adantr
      jca com12 wb dfgrlic2 ad2ant2rl mpbird mpdan ) ABUAIZBCUAIZJZAKLZBKLZJZWR
      CKLZJZJZACUAIZWNWSWOXABAUBCBUBUCWPXBJXCAUDMZCUDMZDNZUEZAAENZOPQPZCCXHXFMZ
      OPZQPZRIZEXDUFZJZDUGZWPXPXBWNXDBUDMZFNZUEZXIBBXHXRMZOPZQPZRIZEXDUFZJZFUGZ
      XQXEGNZUEZBBHNZOPZQPZCCYIYGMZOPZQPZRIZHXQUFZJZGUGZXPWOEFABXDXQXDUHZXQUHZU
      IHGBCXQXEYTXEUHZUIYFYRXPYEYRXPTFYRYEXPYQYEXPTGYQYEXPYQYEJZXOXDXEYGXRUJZUE
      ZXICCXHUUCMZOPZQPZRIZEXDUFZJDKUUCUUCKLUUBYGXRGUKFUKULUMUUBUUDUUIYHXSUUDYP
      YDXDXQXEYGXRUNUOYQYEUUIYPYEUUITYHYPXSYDUUIYPXSJZYCUUHEXDUUJXHXDLZJZYCUUHU
      ULYCJYCYBUUGRIZJUUHUULUUMYCYPXSUUKUUMXSUUKYPUUMXSUUKYPUUMTXSUUKJZYPYBCCXT
      YGMZOPZQPZRIZUUMUUNXTXQLYPUURTXSXDXQXHXRXDXQXRUPZUQYOUURHXTXQYIXTVPZYKYBY
      NUUQRUUTYJYABQYIXTBOURSUUTYMUUPCQUUTYLUUOCOYIXTYGUSSSUTVAVBUUNUUQUUGYBRUU
      NUUPUUFCQUUNUUOUUECOUUNUUEUUOXSXDXQXRVCUUKUUEUUOVPUUSXDXQXHYGXRVDVEVFSSVG
      VHVIVJVKVLXIYBUUGVMVBVIVNVOVQVRWGXFUUCVPZXGUUDXNUUIXDXEXFUUCVSUVAXMUUHEXD
      UVAXLUUGXIRUVAXKUUFCQUVAXJUUECOXHXFUUCVTSSVGWAWBWCVIWDWHWDVRWEWFXBXCXPWIZ
      WPWQWTUVBWRWREDACXDXEKKYSUUAWJWKVQWLWM $.
  $}

  ${
    $d f g h $.
    $( Local isomorphism is an equivalence relation on hypergraphs.
       (Contributed by AV, 11-Jun-2025.) $)
    grlicer $p |- ( ~=lgr i^i ( UHGraph X. UHGraph ) ) Er UHGraph $=
      ( vf vg vh cgrlic cuhgr cv grlicref grlicsym wbr wa wcel grlictr brinxper
      wi a1i ) ABCDEAFZGBFZPHPQDIQCFZDIJPRDINPEKPQRLOM $.
  $}

  ${
    $d B f $.  $d C f $.  $d R f $.  $d S f $.
    grlicen.b $e |- B = ( Vtx ` R ) $.
    grlicen.c $e |- C = ( Vtx ` S ) $.
    $( Locally isomorphic graphs have equinumerous sets of vertices.
       (Contributed by AV, 11-Jun-2025.) $)
    grlicen $p |- ( R ~=lgr S -> B ~~ C ) $=
      ( vf cgrlic wbr cgrlim co c0 wne cen brgrlic cv wcel wex n0 sylbi exlimiv
      wf1o grlimf1o cvtx fvexi f1oen syl ) CDHICDJKZLMZABNIZCDOUIGPZUHQZGRUJGUH
      SULUJGULABUKUBUJUKCDABEFUCABUKACUDEUEUFUGUATT $.
  $}

  ${
    $d G i $.  $d H i $.
    $( Isomorphic hypergraphs are locally isomorphic.  (Contributed by AV,
       12-Jun-2025.)  (Proof shortened by AV, 11-Jul-2025.) $)
    gricgrlic $p |- ( ( G e. UHGraph /\ H e. UHGraph )
                      -> ( G ~=gr H -> G ~=lgr H ) ) $=
      ( vi cgric wbr cuhgr wcel wa cgrlic cgrim co c0 wne wi brgric cv n0 sylbi
      wex w3a cgrlim uhgrimgrlim brgrilci syl 3expa expcom exlimiv com12 ) ABDE
      ZAFGZBFGZHZABIEZUIABJKZLMZULUMNZABOUOCPZUNGZCSUPCUNQURUPCULURUMUJUKURUMUJ
      UKURTUQABUAKGUMUQABUBABUQUCUDUEUFUGRRUH $.
  $}

  ${
    $d F x y $.  $d G x $.  $d H x y $.  $d N x y $.  $d V x $.  $d W x y $.
    clnbgr3stgrgrlim.n $e |- N e. NN0 $.
    clnbgr3stgrgrlim.v $e |- V = ( Vtx ` G ) $.
    clnbgr3stgrgrlim.w $e |- W = ( Vtx ` H ) $.
    $( If all (closed) neighborhoods of the vertices in two simple graphs with
       the same order induce a subgraph which is isomorphic to an ` N `-star,
       then any bijection between the vertices is a local isomorphism between
       the two graphs.  (Contributed by AV, 28-Dec-2025.) $)
    clnbgr3stgrgrlim $p |- ( ( ( G e. USGraph /\ H e. USGraph
                                 /\ F : V -1-1-onto-> W )
            /\ A. x e. V ( G ISubGr ( G ClNeighbVtx x ) ) ~=gr ( StarGr ` N )
            /\ A. y e. W ( H ISubGr ( H ClNeighbVtx y ) ) ~=gr ( StarGr ` N ) )
                            -> F e. ( G GraphLocIso H ) ) $=
      ( cusgr wcel cclnbgr co cisubgr cgric wbr wa cvv wf1o w3a cv cstgr cgrlim
      cfv wral simp13 cuhgr wss usgruhgr 3ad2ant2 adantr clnbgrssvtx isubgruhgr
      wi a1i syl2an2r wf f1of 3ad2ant3 ffvelcdmda oveq2 oveq2d breq1d rspcv syl
      wceq impancom imp gricsym sylc anim1ci grictr ex ralimdva com23 3imp cvtx
      wb fvexi fexd 3anim3i 3ad2ant1 isgrlim mpbir2and ) DLMZELMZGHCUAZUBZDDAUC
      ZNOPOZFUDUFZQRZAGUGZEEBUCZNOZPOZWMQRZBHUGZUBZCDEUEOMZWIWLEEWKCUFZNOZPOZQR
      ZAGUGZWGWHWIWOWTUHWJWOWTXGWJWTWOXGWJWTWOXGUPWJWTSZWNXFAGXHWKGMZSZWNXFXJWN
      SWNWMXEQRZSXFXJXKWNXJXEUIMZXEWMQRZXKXHEUIMZXIXDHUJZXLWJXNWTWHWGXNWIEUKULU
      MXOXJEXCHKUNUQXDEHKUOURXHXIXMWJXIWTXMWJXISXCHMWTXMUPWJGHWKCWIWGGHCUSWHGHC
      UTZVAVBWSXMBXCHWPXCVHZWRXEWMQXQWQXDEPWPXCENVCVDVEVFVGVIVJWMXEVKVLVMWLWMXE
      VNVGVOVPVOVQVRXAWGWHCTMZUBZXBWIXGSVTWJWOXSWTWIXRWGWHWIGHTCXPGTMWIGDVSJWAU
      QWBWCWDACDEGHLLTJKWEVGWF $.

    $d G f x y $.  $d H f $.  $d N f $.  $d V f $.  $d W f $.
    $( If all (closed) neighborhoods of the vertices in two simple graphs with
       the same order induce a subgraph which is isomorphic to an ` N `-star,
       then the two graphs are locally isomorphic.  (Contributed by AV,
       29-Sep-2025.) $)
    clnbgr3stgrgrlic $p |- ( ( ( G e. USGraph /\ H e. USGraph /\ V ~~ W )
            /\ A. x e. V ( G ISubGr ( G ClNeighbVtx x ) ) ~=gr ( StarGr ` N )
            /\ A. y e. W ( H ISubGr ( H ClNeighbVtx y ) ) ~=gr ( StarGr ` N ) )
                            -> G ~=lgr H ) $=
      ( vf cusgr wcel wbr w3a cclnbgr co cgric wa wi cen cisubgr cstgr cfv wral
      cv cgrlic wf1o wex cvv wb cvtx fvexi pm3.2i breng mp1i cuhgr wss usgruhgr
      adantl 3ad2ant1 clnbgrssvtx a1i isubgruhgr syl2an2r wf 3ad2ant2 ffvelcdmd
      f1of simp3 wceq oveq2 oveq2d breq1d rspcv syl com34 3imp1 gricsym anim1ci
      3exp sylc grictr ex ralimdva com24 imp32 ancld eximdv com23 sylbid 3impia
      3impib dfgrlic2 3adant3 mpbird ) CLMZDLMZFGUANZOZCCAUFZPQUBQZEUCUDZRNZAFU
      EZDDBUFZPQZUBQZXCRNZBGUEZOCDUGNZFGKUFZUHZXBDDXAXLUDZPQZUBQZRNZAFUEZSZKUIZ
      WTXEXJXTWQWRWSXEXJSZXTTZWQWRSZWSXMKUIZYBFUJMZGUJMZSWSYDUKYCYEYFFCULIUMGDU
      LJUMUNFGKUJUJUOUPYCYAYDXTYCYAYDXTTYCYASZXMXSKYGXMXRYCXEXJXMXRTYCXMXJXEXRY
      CXMXJXEXRTYCXMXJOZXDXQAFYHXAFMZSZXDXQYJXDSXDXCXPRNZSXQYJYKXDYJXPUQMZXPXCR
      NZYKYHDUQMZYIXOGURZYLYCXMYNXJWRYNWQDUSUTVAYOYJDXNGJVBVCXODGJVDVEYCXMXJYIY
      MYCXMYIXJYMYCXMYIXJYMTZYCXMYIOZXNGMYPYQFGXAXLXMYCFGXLVFYIFGXLVIVGYCXMYIVJ
      VHXIYMBXNGXFXNVKZXHXPXCRYRXGXODUBXFXNDPVLVMVNVOVPWAVQVRXCXPVSWBVTXBXCXPWC
      VPWDWEWAWFWGWHWIWDWJWKWLWMWTXEXKXTUKZXJWQWRYSWSAKCDFGLLIJWNWOVAWP $.
  $}

  ${
    $d V e $.
    usgrexmpl1.v $e |- V = ( 0 ... 5 ) $.
    usgrexmpl1.e $e |- E = <" { 0 , 1 } { 0 , 2 } { 1 , 2 } { 0 , 3 }
                              { 3 , 4 } { 3 , 5 } { 4 , 5 } "> $.
    $( Lemma for ~ usgrexmpl1 .  (Contributed by AV, 2-Aug-2025.) $)
    usgrexmpl1lem $p |- E : dom E -1-1-> { e e. ~P V | ( # ` e ) = 2 } $=
      ( cc0 c1 cvv wcel c2 c3 c4 c5 wne wa cn0 wo pm3.2i prneimg mp2 cpr w3a cv
      cs7 wceq cdm chash cfv cpw crab wf1 prex 3pm3.2i 0nn0 1nn0 2nn0 1ne2 olci
      ax-1ne0 0ne1 0ne2 orci 3nn0 1re 1lt3 ltneii 4nn0 3pos 4pos 5nn0 5pos 2ne0
      0re 2re 2lt3 1lt4 1lt5 3re 3lt4 necomi 4re 4lt5 3lt5 ctp csn cun wss wf1o
      cfzo co c7 s7f1o imp wb s7len oveq2i f1oeq2 ax-mp dmeqi cword s7cli wrddm
      sylibr eqtri f1of1 syl wral cfz 0elfz cle wbr 5re elfz2nn0 mpbir3an prssi
      ltleii mp2an 2lt5 sseq1 raltpg ralsn mpbir ralunb nn0fz0 mpbi pwssb pweqi
      mpbir2an sseqtrri prhash2ex c0ex 2ex hashprb 1ex fveqeq2 elexi ssrab f1ss
      3ex cr sylancl ) FGUAZHIZFJUAZHIZGJUAZHIZUBZFKUAZHIZKLUAZHIZKMUAZHIZLMUAZ
      HIZUBZUBZUUBUUDNZUUBUUFNZUUBUUINZUBZUUBUUKNZUUBUUMNZUUBUUONZUBZOZUUDUUFNZ
      UUDUUINZOZUUDUUKNZUUDUUMNZUUDUUONZUBZOZUUFUUINZUUFUUKNZUUFUUMNZUUFUUONZUB
      ZOZUBZUUIUUKNZUUIUUMNZUUIUUONZUBZUUKUUMNZUUKUUONZUUMUUONZUBZOZOZOZBUUBUUD
      UUFUUIUUKUUMUUOUDZUEZBUFZAUCZUGUHJUEZACUIZUJZBUKZUURUWLUUHUUJUUQUUCUUEUUG
      FGULFJULGJULUMZFKULZUULUUNUUPKLULKMULLMULUMZUMUWBUWKUVGUVOUWAUVBUVFUUSUUT
      UVAFPIZGPIZOZUXEJPIZOZOFFNZFJNZOZGFNZGJNZOZQUUSUXGUXIUXEUXFUNUORZUXEUXHUN
      UPRZRUXOUXLUXMUXNUSUQRURFGFJPPPPSTUXGUXFUXHOZOFGNZUXKOZGGNUXNOZQUUTUXGUXR
      UXPUXFUXHUOUPRZRUXTUYAUXSUXKUTVARZVBFGGJPPPPSTUXGUXEKPIZOZOUXJFKNZOZUXMGK
      NZOZQUVAUXGUYEUXPUXEUYDUNVCRZRUYIUYGUXMUYHUSGKVDVEVFZRZURFGFKPPPPSTUMUVCU
      VDUVEUXGUYDLPIZOZOUYFFLNZOZUYHGLNZOZQUVCUXGUYNUXPUYDUYMVCVGRZRUYPUYRUYFUY
      OFKVMVHVFZFLVMVIVFZRZVBFGKLPPPPSTUXGUYDMPIZOZOUYFFMNZOZUYHGMNZOZQUVDUXGVU
      DUXPUYDVUCVCVJRZRVUFVUHUYFVUEUYTFMVMVKVFZRZVBFGKMPPPPSTUXGUYMVUCOZOUYOVUE
      OZUYQVUGOZQUVEUXGVULUXPUYMVUCVGVJRZRVUMVUNUYOVUEVUAVUJRZVBFGLMPPPPSTUMRUV
      JUVNUVHUVIUXIUXROUXTJGNJJNOZQUVHUXIUXRUXQUYBRUXTVUQUYCVBFJGJPPPPSTUXIUYEO
      UYGJFNZJKNZOZQUVIUXIUYEUXQUYJRVUTUYGVURVUSVLJKVNVOVFRURFJFKPPPPSTRUVKUVLU
      VMUXIUYNOUYPVUSJLNZOZQUVKUXIUYNUXQUYSRUYPVVBVUBVBFJKLPPPPSTUXIVUDOVUFVUSJ
      MNZOZQUVLUXIVUDUXQVUIRVUFVVDVUKVBFJKMPPPPSTUXIVULOVUMVVAVVCOZQUVMUXIVULUX
      QVUORVUMVVEVUPVBFJLMPPPPSTUMRUVPUVTUXRUYEOUYIVUTQUVPUXRUYEUYBUYJRUYIVUTUY
      LVBGJFKPPPPSTUVQUVRUVSUXRUYNOUYRVVBQUVQUXRUYNUYBUYSRUYRVVBUYHUYQUYKGLVDVP
      VFZRVBGJKLPPPPSTUXRVUDOVUHVVDQUVRUXRVUDUYBVUIRVUHVVDUYHVUGUYKGMVDVQVFZRVB
      GJKMPPPPSTUXRVULOVUNVVEQUVSUXRVULUYBVUORVUNVVEUYQVUGVVFVVGRVBGJLMPPPPSTUM
      RUMUWFUWJUWCUWDUWEUYEUYNOUYPKKNZKLNZOZQUWCUYEUYNUYJUYSRUYPVVJVUBVBFKKLPPP
      PSTUYEVUDOVUFVVHKMNZOZQUWDUYEVUDUYJVUIRVUFVVLVUKVBFKKMPPPPSTUYEVULOVUMVVI
      VVKOZQUWEUYEVULUYJVUORVUMVVMVUPVBFKLMPPPPSTUMUWGUWHUWIUYNVUDOVVLLKNZLMNZO
      ZQUWGUYNVUDUYSVUIRVVPVVLVVNVVOKLKLVRVSVFZVTLMWAWBVFZRURKLKMPPPPSTUYNVULOV
      VMLLNVVOOZQUWHUYNVULUYSVUORVVMVVSVVIVVKVVQKMVRWCVFZRZVBKLLMPPPPSTVUDVULOV
      VMMLNMMNOZQUWIVUDVULVUIVUORVVMVWBVWAVBKMLMPPPPSTUMRRREUWMUWOOZUWPUUBUUDUU
      FWDZUUIWEZWFZUUKUUMUUOWDZWFZBUKZVWHUWTWGZUXAVWCUWPVWHBWHZVWIVWCFUWNUGUHZW
      IWJZVWHBWHZVWKVWCFWKWIWJZVWHBWHZVWNUWMUWOVWPUUBUUDUUFUUIUUKUUMUUOBHWLWMVW
      MVWOUEVWNVWPWNVWLWKFWIUUBUUDUUFUUIUUKUUMUUOWOWPVWMVWOVWHBWQWRXCUWPVWMUEVW
      KVWNWNUWPUWNUFZVWMBUWNEWSUWNHWTIVWQVWMUEUUBUUDUUFUUIUUKUUMUUOXAHUWNXBWRXD
      UWPVWMVWHBWQWRXCUWPVWHBXEXFVWJVWHUWSWGUWRAVWHXGZVWHFMXHWJZUIZUWSVWHVWTWGU
      WQVWSWGZAVWHXGZVXBVXAAVWFXGZVXAAVWGXGZVXCVXAAVWDXGZVXAAVWEXGZVXEUUBVWSWGZ
      UUDVWSWGZUUFVWSWGZFVWSIZGVWSIZVXGVUCVXJVJMXIWRZVXKUXFVUCGMXJXKUOVJGMVDXLV
      QXPGMXMXNZFGVWSXOXQVXJJVWSIZVXHVXLVXNUXHVUCJMXJXKUPVJJMVNXLXRXPJMXMXNZFJV
      WSXOXQVXKVXNVXIVXMVXOGJVWSXOXQUUHVXEVXGVXHVXIUBWNUXBVXAVXGVXHVXIAUUBUUDUU
      FHHHUWQUUBVWSXSUWQUUDVWSXSUWQUUFVWSXSXTWRXNVXFUUIVWSWGZVXJKVWSIZVXPVXLVXQ
      UYDVUCKMXJXKVCVJKMVRXLWCXPKMXMXNZFKVWSXOXQVXAVXPAUUIUXCUWQUUIVWSXSYAYBVXA
      AVWDVWEYCYHVXDUUKVWSWGZUUMVWSWGZUUOVWSWGZVXQLVWSIZVXSVXRVYBUYMVUCLMXJXKVG
      VJLMWAXLWBXPLMXMXNZKLVWSXOXQVXQMVWSIZVXTVXRVUCVYDVJMYDYEZKMVWSXOXQVYBVYDV
      YAVYCVYELMVWSXOXQUUQVXDVXSVXTVYAUBWNUXDVXAVXSVXTVYAAUUKUUMUUOHHHUWQUUKVWS
      XSUWQUUMVWSXSUWQUUOVWSXSXTWRXNVXAAVWFVWGYCYHAVWHVWSYFYBCVWSDYGYIVWRUWRAVW
      FXGZUWRAVWGXGZVYFUWRAVWDXGZUWRAVWEXGZVYHUUBUGUHJUEZUUDUGUHJUEZUUFUGUHJUEZ
      YJFHIZJHIZUXKUBVYKVYMVYNUXKYKYLVAUMFJYMYEGHIZVYNUXNUBVYLVYOVYNUXNYNYLUQUM
      GJYMYEUUHVYHVYJVYKVYLUBWNUXBUWRVYJVYKVYLAUUBUUDUUFHHHUWQUUBJUGYOUWQUUDJUG
      YOUWQUUFJUGYOXTWRXNVYIUUIUGUHJUEZVYMKHIZUYFUBVYPVYMVYQUYFYKYSUYTUMFKYMYEU
      WRVYPAUUIUXCUWQUUIJUGYOYAYBUWRAVWDVWEYCYHVYGUUKUGUHJUEZUUMUGUHJUEZUUOUGUH
      JUEZVYQLHIZVVIUBVYRVYQWUAVVIYSLYTWAYPZVVQUMKLYMYEVYQMHIZVVKUBVYSVYQWUCVVK
      YSMYTXLYPZVVTUMKMYMYEWUAWUCVVOUBVYTWUAWUCVVOWUBWUDVVRUMLMYMYEUUQVYGVYRVYS
      VYTUBWNUXDUWRVYRVYSVYTAUUKUUMUUOHHHUWQUUKJUGYOUWQUUMJUGYOUWQUUOJUGYOXTWRX
      NUWRAVWFVWGYCYHUWRAUWSVWHYQYHUWPVWHUWTBYRUUAXQ $.

    $d E e $.
    usgrexmpl1.g $e |- G = <. V , E >. $.
    $( ` G ` is a simple graph of six vertices ` 0 , 1 , 2 , 3 , 4 , 5 ` , with
       edges ` { 0 , 1 } , { 1 , 2 } , { 0 , 2 } , { 0 , 3 } , { 3 , 4 } , `
       ` { 3 , 5 } , { 4 , 5 } ` .  (Contributed by AV, 3-Aug-2025.) $)
    usgrexmpl1 $p |- G e. USGraph $=
      ( ve cusgr wcel cdm cv chash c2 cvv cc0 c5 c1 cpr c3 c4 cfv wceq cpw crab
      wf1 usgrexmpl1lem cop eleq1i cword cfz ovexi s7cli eqeltri isusgrop mp2an
      wb cs7 bitri mpbir ) BHIZAJGKLUAMUBGCUCUDAUEZGACDEUFUTCAUGZHIZVABVBHFUHCN
      IANUIZIVCVAUPCOPUJDUKAOQRZOMRZQMRZOSRZSTRZSPRZTPRZUQVDEVEVFVGVHVIVJVKULUM
      ACNVDGUNUOURUS $.

    $( The vertices ` 0 , 1 , 2 , 3 , 4 , 5 ` of the graph
       ` G = <. V , E >. ` .  (Contributed by AV, 3-Aug-2025.) $)
    usgrexmpl1vtx $p |- ( Vtx ` G ) = ( { 0 , 1 , 2 } u. { 3 , 4 , 5 } ) $=
      ( cvtx cfv cc0 c5 cfz co c1 c2 ctp c3 c4 cvv wcel cpr cun cop fveq2i wceq
      cword ovexi cs7 s7cli eqeltri opvtxfv mp2an eqtri fz0to5un2tp 3eqtri ) BG
      HZCIJKLIMNOPQJOUAUOCAUBZGHZCBUPGFUCCRSARUEZSUQCUDCIJKDUFAIMTZINTZMNTZIPTZ
      PQTZPJTZQJTZUGUREUSUTVAVBVCVDVEUHUIACRURUJUKULDUMUN $.

    $( The edges ` { 0 , 1 } , { 1 , 2 } , { 0 , 2 } , { 0 , 3 } , `
       ` { 3 , 4 } , { 3 , 5 } , { 4 , 5 } ` of the graph ` G = <. V , E >. ` .
       (Contributed by AV, 3-Aug-2025.) $)
    usgrexmpl1edg $p |- ( Edg ` G ) = ( { { 0 , 3 } }
                              u. ( { { 0 , 1 } , { 0 , 2 } , { 1 , 2 } }
                                u. { { 3 , 4 } , { 3 , 5 } , { 4 , 5 } } ) ) $=
      ( cfv ciedg cc0 c3 cpr c1 c2 c4 c5 cun cvv wcel prex a1i cedg crn csn ctp
      edgval cop fveq2i cword wceq cfz ovexi s7cli eqeltri opiedgfv mp2an eqtri
      cs7 rneqi id s7rn ax-mp uncom uneq1i unass 3eqtri ) BUAGBHGZUBAUBZIJKZUCZ
      ILKZIMKZLMKZUDZJNKZJOKZNOKZUDZPPZBUEVFAVFCAUFZHGZABVSHFUGCQRAQUHZRVTAUICI
      OUJDUKAVJVKVLVHVNVOVPUQZWAEVJVKVLVHVNVOVPULUMACQWAUNUOUPURVGWBUBZVMVIPZVQ
      PZVRAWBEURVJQRZWCWEUIILSWFVJVKVLVHVNVOVPQWFUSVKQRWFIMSTVLQRWFLMSTVHQRWFIJ
      STVNQRWFJNSTVOQRWFJOSTVPQRWFNOSTUTVAWEVIVMPZVQPVRWDWGVQVMVIVBVCVIVMVQVDUP
      VEVE $.

    $d G x y z $.
    $( ` G ` contains a triangle ` 0 , 1 , 2 ` , with corresponding edges
       ` { 0 , 1 } , { 1 , 2 } , { 0 , 2 } ` .  (Contributed by AV,
       3-Aug-2025.) $)
    usgrexmpl1tri $p |- { 0 , 1 , 2 } e. ( GrTriangles ` G ) $=
      ( cc0 c1 c2 ctp wcel wceq c3 cpr w3a wo orci elun mpbir eleq1d cgrtri cfv
      vx vy vz cv chash csn c4 c5 cun wrex c0ex tpid1 1eltp012 2ex 3pm3.2i eqid
      tpid3 ex-hash prex olci tpid2 tpeq1 eqeq2d preq1 biidd 3anbi123d 3anbi13d
      tpeq2 preq2 tpeq3 rspc3ev cvtx usgrexmpl1vtx eqcomi usgrexmpl1edg isgrtri
      mp2an cedg ) GHIJZBUAUBKWAUCUFZUDUFZUEUFZJZLZWAUGUBMLZWBWCNZGMNUHZGHNZGIN
      ZHINZJZMUINMUJNUIUJNJZUKZUKZKZWBWDNZWPKZWCWDNZWPKZOZOZUEWAMUIUJJZUKZULUDX
      EULUCXEULZGXEKZHXEKZIXEKZOWAWALZWGWJWPKZWKWPKZWLWPKZOZOZXFXGXHXIXGGWAKZGX
      DKZPXPXQGHIUMUNQGWAXDRSXHHWAKZHXDKZPXRXSUOQHWAXDRSXIIWAKZIXDKZPXTYAGHIUPU
      SQIWAXDRSUQXJWGXNWAURUTXKXLXMXKWJWIKZWJWOKZPYCYBYCWJWMKZWJWNKZPYDYEWJWKWL
      GHVAUNQWJWMWNRSVBWJWIWORSXLWKWIKZWKWOKZPYGYFYGWKWMKZWKWNKZPYHYIWJWKWLGIVA
      VCQWKWMWNRSVBWKWIWORSXMWLWIKZWLWOKZPYKYJYKWLWMKZWLWNKZPYLYMWJWKWLHIVAUSQW
      LWMWNRSVBWLWIWORSUQUQXCXOWAGWCWDJZLZWGGWCNZWPKZGWDNZWPKZXAOZOWAGHWDJZLZWG
      XKYSHWDNZWPKZOZOUCUDUEGHIXEXEXEWBGLZWFYOXBYTWGUUFWEYNWAWBGWCWDVDVEUUFWQYQ
      WSYSXAXAUUFWHYPWPWBGWCVFTUUFWRYRWPWBGWDVFTUUFXAVGVHVIWCHLZYOUUBYTUUEWGUUG
      YNUUAWAWCHGWDVJVEUUGYQXKXAUUDYSUUGYPWJWPWCHGVKTUUGWTUUCWPWCHWDVFTVIVIWDIL
      ZUUBXJUUEXNWGUUHUUAWAWAWDIGHVLVEUUHXKXKYSXLUUDXMUUHXKVGUUHYRWKWPWDIGVKTUU
      HUUCWLWPWDIHVKTVHVIVMVSUCUDUEWAWPBXEBVNUBXEABCDEFVOVPBVTUBWPABCDEFVQVPVRS
      $.
  $}

  ${
    $d V e $.
    usgrexmpl2.v $e |- V = ( 0 ... 5 ) $.
    usgrexmpl2.e $e |- E = <" { 0 , 1 } { 1 , 2 } { 2 , 3 } { 3 , 4 }
                              { 4 , 5 } { 0 , 3 } { 0 , 5 } "> $.
    $( Lemma for ~ usgrexmpl2 .  (Contributed by AV, 3-Aug-2025.) $)
    usgrexmpl2lem $p |- E : dom E -1-1-> { e e. ~P V | ( # ` e ) = 2 } $=
      ( cc0 c1 wcel c2 c3 c4 c5 wne wa cn0 wo pm3.2i orci prneimg mp2 cpr chash
      cvv w3a cs7 wceq cdm cv cfv cpw crab wf1 prex 3pm3.2i 0nn0 1nn0 2nn0 0ne1
      0ne2 3nn0 0re 3pos ltneii 4nn0 4pos 5nn0 5pos ax-1ne0 1lt3 olci 1lt5 1ne2
      1re 1lt4 2re 2lt3 2lt4 2lt5 2ne0 3re 3lt4 3lt5 4ne0 3ne0 4re 4lt5 ctp csn
      necomi cun wss wf1o cfzo co c7 s7f1o imp s7len oveq2i f1oeq2 ax-mp sylibr
      dmeqi cword s7cli wrddm eqtri f1of1 syl wral cfz 0elfz cle wbr 5re ltleii
      wb elfz2nn0 mpbir3an prssi mp2an sseq1 raltp ralsn mpbir ralunb prhash2ex
      mpbir2an leidi pwssb pweqi sseqtrri 1ex 2ex hashprb mpbi 3ex fveqeq2 c0ex
      elexi ssrab f1ss sylancl ) FGUAZUCHZGIUAZUCHZIJUAZUCHZUDZJKUAZUCHZKLUAZUC
      HZFJUAZUCHZFLUAZUCHZUDZUDZUUDUUFMZUUDUUHMZUUDUUKMZUDZUUDUUMMZUUDUUOMZUUDU
      UQMZUDZNZUUFUUHMZUUFUUKMZNZUUFUUMMZUUFUUOMZUUFUUQMZUDZNZUUHUUKMZUUHUUMMZU
      UHUUOMZUUHUUQMZUDZNZUDZUUKUUMMZUUKUUOMZUUKUUQMZUDZUUMUUOMZUUMUUQMZUUOUUQM
      ZUDZNZNZNZBUUDUUFUUHUUKUUMUUOUUQUEZUFZBUGZAUHZUBUIIUFZACUJZUKZBULZUUTUWNU
      UJUULUUSUUEUUGUUIFGUMZGIUMZIJUMZUNJKUMZUUNUUPUURKLUMZFJUMZFLUMZUNUNUWDUWM
      UVIUVQUWCUVDUVHUVAUVBUVCFOHZGOHZNZUXLIOHZNZNFGMZFIMZNZGGMGIMZNZPUVAUXMUXO
      UXKUXLUOUPQZUXLUXNUPUQQZQUXRUXTUXPUXQURUSQRFGGIOOOOSTUXMUXNJOHZNZNUXQFJMZ
      NZUXSGJMZNZPUVBUXMUYDUYAUXNUYCUQUTQZQUYFUYHUXQUYEUSFJVAVBVCZQRFGIJOOOOSTU
      XMUYCKOHZNZNUYEFKMZNZUYGGKMZNZPUVCUXMUYLUYAUYCUYKUTVDQZQUYNUYPUYEUYMUYJFK
      VAVEVCZQRFGJKOOOOSTUNUVEUVFUVGUXMUYKLOHZNZNUYMFLMZNZUYOGLMZNZPUVEUXMUYTUY
      AUYKUYSVDVFQZQVUBVUDUYMVUAUYRFLVAVGVCZQRFGKLOOOOSTUXMUXKUYCNZNFFMZUYENZGF
      MZUYGNZPUVFUXMVUGUYAUXKUYCUOUTQZQVUKVUIVUJUYGVHGJVMVIVCZQZVJFGFJOOOOSTUXM
      UXKUYSNZNVUHVUANZVUJVUCNZPUVGUXMVUOUYAUXKUYSUOVFQZQVUQVUPVUJVUCVHGLVMVKVC
      ZQZVJFGFLOOOOSTUNQUVLUVPUVJUVKUXOUYDNUYHIIMIJMZNZPUVJUXOUYDUYBUYIQUYHVVBU
      XSUYGVLVUMQRGIIJOOOOSTUXOUYLNUYPVVAIKMZNZPUVKUXOUYLUYBUYQQUYPVVDUYGUYOVUM
      GKVMVNVCZQRGIJKOOOOSTQUVMUVNUVOUXOUYTNVUDVVCILMZNZPUVMUXOUYTUYBVUEQVUDVVG
      UYOVUCVVEVUSQRGIKLOOOOSTUXOVUGNVUKIFMZVVANZPUVNUXOVUGUYBVULQVUKVVIVUNRGIF
      JOOOOSTUXOVUONVUQVVHVVFNZPUVOUXOVUOUYBVURQVUQVVJVUTRGIFLOOOOSTUNQUVRUWBUY
      DUYLNVVDJJMZJKMZNZPUVRUYDUYLUYIUYQQVVDVVMVVAVVCIJVOVPVCZIKVOVQVCZQRIJJKOO
      OOSTUVSUVTUWAUYDUYTNVVGVVLJLMZNZPUVSUYDUYTUYIVUEQVVGVVQVVCVVFVVOILVOVRVCZ
      QRIJKLOOOOSTUYDVUGNVVIJFMZVVKNZPUVTUYDVUGUYIVULQVVIVVTVVHVVAVSVVNQRIJFJOO
      OOSTUYDVUONVVJVVSVVPNZPUWAUYDVUOUYIVURQVVJVWAVVHVVFVSVVRQRIJFLOOOOSTUNQUN
      UWHUWLUWEUWFUWGUYLUYTNVVQKKMKLMZNZPUWEUYLUYTUYQVUEQVVQVWCVVLVVPJKVTWAVCZJ
      LVTWBVCZQRJKKLOOOOSTUYLVUGNVVTKFMZKJMZNZPUWFUYLVUGUYQVULQVWHVVTVWFVWGWCJK
      VWDWIQZVJJKFJOOOOSTUYLVUONVWAVWFVWBNZPUWGUYLVUOUYQVURQVWAVWJVVSVVPWDVWEQZ
      RJKFLOOOOSTUNUWIUWJUWKUYTVUGNVWHLFMZLJMNZPUWIUYTVUGVUEVULQVWHVWMVWIRKLFJO
      OOOSTUYTVUONVWJVWLLLMNZPUWJUYTVUOVUEVURQVWJVWNVWFVWBWCKLWEWFVCZQRKLFLOOOO
      STVUGVUONVUPVWAPUWKVUGVUOVULVURQVWAVUPVWKVJFJFLOOOOSTUNQQQEUWOUWQNZUWRUUD
      UUFUUHWGZUUKWHZWJZUUMUUOUUQWGZWJZBULZVXAUXBWKZUXCVWPUWRVXABWLZVXBVWPFUWPU
      BUIZWMWNZVXABWLZVXDVWPFWOWMWNZVXABWLZVXGUWOUWQVXIUUDUUFUUHUUKUUMUUOUUQBUC
      WPWQVXFVXHUFVXGVXIXQVXEWOFWMUUDUUFUUHUUKUUMUUOUUQWRWSVXFVXHVXABWTXAXBUWRV
      XFUFVXDVXGXQUWRUWPUGZVXFBUWPEXCUWPUCXDHVXJVXFUFUUDUUFUUHUUKUUMUUOUUQXEUCU
      WPXFXAXGUWRVXFVXABWTXAXBUWRVXABXHXIVXCVXAUXAWKUWTAVXAXJZVXAFLXKWNZUJZUXAV
      XAVXMWKUWSVXLWKZAVXAXJZVXOVXNAVWSXJZVXNAVWTXJZVXPVXNAVWQXJZVXNAVWRXJZVXRU
      UDVXLWKZUUFVXLWKZUUHVXLWKZFVXLHZGVXLHZVXTUYSVYCVFLXLXAZVYDUXLUYSGLXMXNUPV
      FGLVMXOVKXPGLXRXSZFGVXLXTYAVYDIVXLHZVYAVYFVYGUXNUYSILXMXNUQVFILVOXOVRXPIL
      XRXSZGIVXLXTYAVYGJVXLHZVYBVYHVYIUYCUYSJLXMXNUTVFJLVTXOWBXPJLXRXSZIJVXLXTY
      AVXNVXTVYAVYBAUUDUUFUUHUXDUXEUXFUWSUUDVXLYBUWSUUFVXLYBUWSUUHVXLYBYCXSVXSU
      UKVXLWKZVYIKVXLHZVYKVYJVYLUYKUYSKLXMXNVDVFKLWEXOWFXPKLXRXSZJKVXLXTYAVXNVY
      KAUUKUXGUWSUUKVXLYBYDYEVXNAVWQVWRYFYHVXQUUMVXLWKZUUOVXLWKZUUQVXLWKZVYLLVX
      LHZVYNVYMVYQUYSUYSLLXMXNVFVFLXOYILLXRXSZKLVXLXTYAVYCVYIVYOVYEVYJFJVXLXTYA
      VYCVYQVYPVYEVYRFLVXLXTYAVXNVYNVYOVYPAUUMUUOUUQUXHUXIUXJUWSUUMVXLYBUWSUUOV
      XLYBUWSUUQVXLYBYCXSVXNAVWSVWTYFYHAVXAVXLYJYECVXLDYKYLVXKUWTAVWSXJZUWTAVWT
      XJZVYSUWTAVWQXJZUWTAVWRXJZWUAUUDUBUIIUFZUUFUBUIIUFZUUHUBUIIUFZYGGUCHZIUCH
      ZUXSUDWUDWUFWUGUXSYMYNVLUNGIYOYPWUGJUCHZVVAUDWUEWUGWUHVVAYNYQVVNUNIJYOYPU
      WTWUCWUDWUEAUUDUUFUUHUXDUXEUXFUWSUUDIUBYRUWSUUFIUBYRUWSUUHIUBYRYCXSWUBUUK
      UBUIIUFZWUHKUCHZVVLUDWUIWUHWUJVVLYQKOVDYTZVWDUNJKYOYPUWTWUIAUUKUXGUWSUUKI
      UBYRYDYEUWTAVWQVWRYFYHVYTUUMUBUIIUFZUUOUBUIIUFZUUQUBUIIUFZWUJLUCHZVWBUDWU
      LWUJWUOVWBWUKLOVFYTZVWOUNKLYOYPFUCHZWUHUYEUDWUMWUQWUHUYEYSYQUYJUNFJYOYPWU
      QWUOVUAUDWUNWUQWUOVUAYSWUPVUFUNFLYOYPUWTWULWUMWUNAUUMUUOUUQUXHUXIUXJUWSUU
      MIUBYRUWSUUOIUBYRUWSUUQIUBYRYCXSUWTAVWSVWTYFYHUWTAUXAVXAUUAYHUWRVXAUXBBUU
      BUUCYA $.

    $d E e $.
    usgrexmpl2.g $e |- G = <. V , E >. $.
    $( ` G ` is a simple graph of six vertices ` 0 , 1 , 2 , 3 , 4 , 5 ` , with
       edges ` { 0 , 1 } , { 1 , 2 } , { 2 , 3 } , { 0 , 3 } , { 3 , 4 } , `
       ` { 4 , 5 } , { 0 , 5 } ` .  (Contributed by AV, 3-Aug-2025.) $)
    usgrexmpl2 $p |- G e. USGraph $=
      ( ve cusgr wcel cdm cv chash c2 cvv cc0 c5 c1 cpr c3 c4 cfv wceq cpw crab
      wf1 usgrexmpl2lem cop eleq1i cword cfz ovexi s7cli eqeltri isusgrop mp2an
      wb cs7 bitri mpbir ) BHIZAJGKLUAMUBGCUCUDAUEZGACDEUFUTCAUGZHIZVABVBHFUHCN
      IANUIZIVCVAUPCOPUJDUKAOQRZQMRZMSRZSTRZTPRZOSRZOPRZUQVDEVEVFVGVHVIVJVKULUM
      ACNVDGUNUOURUS $.

    $( The vertices ` 0 , 1 , 2 , 3 , 4 , 5 ` of the graph
       ` G = <. V , E >. ` .  (Contributed by AV, 3-Aug-2025.) $)
    usgrexmpl2vtx $p |- ( Vtx ` G ) = ( { 0 , 1 , 2 } u. { 3 , 4 , 5 } ) $=
      ( cvtx cfv cc0 c5 cfz co c1 c2 ctp c3 c4 cvv wcel cpr cun cop fveq2i wceq
      cword ovexi cs7 s7cli eqeltri opvtxfv mp2an eqtri fz0to5un2tp 3eqtri ) BG
      HZCIJKLIMNOPQJOUAUOCAUBZGHZCBUPGFUCCRSARUEZSUQCUDCIJKDUFAIMTZMNTZNPTZPQTZ
      QJTZIPTZIJTZUGUREUSUTVAVBVCVDVEUHUIACRURUJUKULDUMUN $.

    $( The edges ` { 0 , 1 } , { 1 , 2 } , { 2 , 3 } , { 0 , 3 } , `
       ` { 3 , 4 } , { 4 , 5 } , { 0 , 5 } ` of the graph ` G = <. V , E >. ` .
       (Contributed by AV, 3-Aug-2025.) $)
    usgrexmpl2edg $p |- ( Edg ` G ) = ( { { 0 , 3 } }
                              u. ( { { 0 , 1 } , { 1 , 2 } , { 2 , 3 } }
                                u. { { 3 , 4 } , { 4 , 5 } , { 0 , 5 } } ) ) $=
      ( cc0 c3 cpr csn c1 c5 cun cvv wcel prex a1i unass uneq2i 3eqtri cedg cfv
      ciedg crn c2 ctp edgval cop fveq2i cword wceq cfz ovexi cs7 s7cli eqeltri
      c4 opiedgfv mp2an eqtri rneqi id ax-mp df-tp df-pr uneq1i equncomi eqtr4i
      s7rn uncom 3eqtrri ) BUAUBBUCUBZUDAUDZGHIZJZGKIZKUEIZUEHIZUFZHUQIZUQLIZGL
      IZUFZMZMZBUGVLAVLCAUHZUCUBZABWFUCFUICNOANUJZOWGAUKCGLULDUMAVPVQVRVTWAVNWB
      UNZWHEVPVQVRVTWAVNWBUOUPACNWHURUSUTVAVMWIUDZVSVTJZMWAVNWBUFZMZWEAWIEVAVPN
      OZWJWMUKGKPWNVPVQVRVTWAVNWBNWNVBVQNOWNKUEPQVRNOWNUEHPQVTNOWNHUQPQWANOWNUQ
      LPQVNNOWNGHPQWBNOWNGLPQVIVCWMVSWKWLMZMZVOWCMZVSMZWEVSWKWLRWPVSWQWOWQVSWOW
      KWAJZVOMZWBJZMZMZVOXAWSMZWKMZMZWQWLXBWKWLWAVNIZXAMXBWAVNWBVDXGWTXAWAVNVEV
      FUTSXCWKVOXDMZMXHWKMXFXBXHWKXBWSVOXAMZMXIWSMXHWSVOXARWSXIVJVOXAWSRTSWKXHV
      JVOXDWKRTXEWCVOWCVTWAIZXAMXAXJMZXEVTWAWBVDXJXAVJXKXAWSWKMZMXEXJXLXAXJWKWS
      VTWAVEVGSXAWSWKRVHVKSTSVGWRVOWCVSMZMWEVOWCVSRWDXMVOVSWCVJSVHTTT $.

    $d G n $.
    ${
      $d K n $.
      $( Lemma for ~ usgrexmpl2nb0 etc.  (Contributed by AV, 9-Aug-2025.) $)
      usgrexmpl2nblem $p |- ( K e. ( { 0 , 1 , 2 } u. { 3 , 4 , 5 } )
                                -> ( G NeighbVtx K )
                                   = { n e. ( { 0 , 1 , 2 } u. { 3 , 4 , 5 } )
                                       | { K , n } e. ( { { 0 , 3 } }
                         u. ( { { 0 , 1 } , { 1 , 2 } , { 2 , 3 } }
                            u. { { 3 , 4 } , { 4 , 5 } , { 0 , 5 } } ) ) } ) $=
        ( wcel cc0 c1 c2 ctp c3 c4 c5 cun cpr cfv eqcomi cusgr cnbgr co cv crab
        wceq usgrexmpl2 cvtx usgrexmpl2vtx cedg usgrexmpl2edg nbusgrvtx mpan
        csn ) CUAIDJKLMNOPMQZICDUBUCDAUDRJNRUNJKRKLRLNRMNOROPRJPRMQQZIAUOUEUFBC
        EFGHUGAUPCDUOCUHSUOBCEFGHUITCUJSUPBCEFGHUKTULUM $.
    $}

    $( The neighborhood of the first vertex of graph ` G ` .  (Contributed by
       AV, 9-Aug-2025.) $)
    usgrexmpl2nb0 $p |- ( G NeighbVtx 0 ) = { 1 , 3 , 5 } $=
      ( cc0 cpr c3 c1 c2 c4 c5 wcel wceq wo wa cvv wne pm3.2i cnbgr csn ctp cun
      vn co crab c0ex tpid1 orci elun mpbir usgrexmpl2nblem ax-mp 1eltp012 olci
      cv 3ex cn0 5nn0 elexi tpid3 w3a tpssi w3o 3orcoma 3orass bitr3i eltp prex
      wb vex el7g a1i elex preq2b 3orrot 1ex 2ex 0ne1 0ne2 prneimg mp2 neii 0re
      wn id 3pos ltneii 3bior2fd bitri 4nn0 4pos orbi12i 3bitr4i eqrrabd eqtr4i
      5pos mp3an ) BGUAUFZGUEUQZHZGIHZUBGJHZJKHZKIHZUCILHZLMHZGMHZUCUDUDNZUEGJK
      UCZILMUCZUDZUGZJIMUCZGXMNZWTXNOXPGXKNZGXLNZPXQXRGJKUHUIUJGXKXLUKULUEABGCD
      EFUMUNJXMNZIXMNZMXMNZXOXNOXSJXKNZJXLNZPYBYCUOUJJXKXLUKULXTIXKNZIXLNZPYEYD
      ILMURUIUPIXKXLUKULYAMXKNZMXLNZPYGYFILMMUSUTVAVBUPMXKXLUKULXSXTYAVCZXJUEXM
      XOJIMXMVDXAXONZXJVKYHXAXMNQXAJOZXAIOZXAMOZVEZYKYJYLPZPZYIXJYMYKYJYLVEYOYK
      YJYLVFYKYJYLVGVHXAJIMUEVLZVIXJXBXCOZXBXDOZXBXEOZXBXFOZVEZXBXGOZXBXHOZXBXI
      OZVEZPZPZYOXBRNXJUUGVKGXAVJXCXDXEXFXGXHXIRXBVMUNYQYKUUFYNIRNZYQYKVKURUUHX
      AIGRRXARNZUUHYPVNIRVOVPUNUUAYJUUEYLUUAYSYTYRVEZYJYRYSYTVQUUJYRYJYSWFZYRUU
      JVKXBXEGRNZUUIQZJRNZKRNZQZQGJSZGKSZQZXAJSXAKSZQZPXBXESUUMUUPUULUUIUHYPTZU
      UNUUOVRVSTTUUSUVAUUQUURVTWATUJGXAJKRRRRWBWCWDUUKYRYTYSUUKWGYTWFUUKXBXFUUM
      UUOUUHQZQUURGISZQZUUTXAISZQZPXBXFSUUMUVCUVBUUOUUHVSURTTUVEUVGUURUVDWAGIWE
      WHWIZTUJGXAKIRRRRWBWCWDVNWJUNUUNYRYJVKVRUUNXAJGRRUUIUUNYPVNJRVOVPUNVHWKUU
      EUUDYLUUBWFZUUDUUEVKXBXGUUMUUHLUSNZQZQUVDGLSZQZUVFXALSZQZPXBXGSUUMUVKUVBU
      UHUVJURWLTTUVMUVOUVDUVLUVHGLWEWMWIZTUJGXAILRRRUSWBWCWDUVIUUDUUCUUBUVIWGUU
      CWFUVIXBXHUUMUVJMUSNZQZQUVLGMSZQZUVNXAMSQZPXBXHSUUMUVRUVBUVJUVQWLUTTTUVTU
      WAUVLUVSUVPGMWEWRWITUJGXALMRRUSUSWBWCWDVNWJUNUVQUUDYLVKUTUVQXAMGRRUUIUVQY
      PVNMUSVOVPUNVHWNWNWKWOVNWPWSWQ $.

    $( The neighborhood of the second vertex of graph ` G ` .  (Contributed by
       AV, 9-Aug-2025.) $)
    usgrexmpl2nb1 $p |- ( G NeighbVtx 1 ) = { 0 , 2 } $=
      ( c1 cpr cc0 c3 c2 c4 c5 wcel wceq wo wa cvv wne pm3.2i cnbgr csn ctp cun
      vn co crab 1eltp012 orci elun mpbir usgrexmpl2nblem ax-mp tpid1 2ex tpid3
      cv c0ex prssi wb w3o cr 1re vex 3ex 1ne2 1lt3 ltneii prneimg neii biorfri
      mp2 a1i elex preq2b prcom eqeq2i bitr3i bicomd orbi12i df-3or 3bitr4i cn0
      4nn0 1lt4 5nn0 1lt5 ax-1ne0 3pm3.2ni biorfi 3bitri elpr prex el7g eqrrabd
      eqcomd mp2an eqtri ) BGUAUFZGUEUQZHZIJHZUBIGHZGKHZKJHZUCJLHZLMHZIMHZUCUDU
      DNZUEIGKUCZJLMUCZUDZUGZIKHZGXLNZWSXMOXOGXJNZGXKNZPXPXQUHUIGXJXKUJUKUEABGC
      DEFULUMIXLNZKXLNZXMXNOXRIXJNZIXKNZPXTYAIGKURUNUIIXJXKUJUKXSKXJNZKXKNZPYBY
      CIGKUOUPUIKXJXKUJUKXRXSQZXNXMYDXIUEXLXNIKXLUSWTXNNZXIUTYDWTXLNQWTIOZWTKOZ
      PZXAXBOZXAXCOZXAXDOZXAXEOZVAZXAXFOZXAXGOZXAXHOZVAZPZPZYEXIYHYMYRYSYJYKPZY
      TYLPYHYMYLYTXAXEGVBNZWTRNZQZKRNZJRNZQZQGKSZGJSZQZWTKSWTJSZQZPXAXESUUCUUFU
      UAUUBVCUEVDZTZUUDUUEUOVETTUUIUUKUUGUUHVFGJVCVGVHZTUIGWTKJVBRRRVIVLVJVKYFY
      JYGYKYFXAGIHZOZYJIRNZUUPYFUTURUUQWTIGRRUUBUUQUULVMIRVNVOUMUUOXCXAGIVPVQVR
      UUDYGYKUTUOUUDYKYGUUDWTKGRRUUBUUDUULVMKRVNVOVSUMVTYJYKYLWAWBYQYMYNYOYPXAX
      FUUCUUELWCNZQZQUUHGLSZQZUUJWTLSZQZPXAXFSUUCUUSUUMUUEUURVEWDTTUVAUVCUUHUUT
      UUNGLVCWEVHZTUIGWTJLVBRRWCVIVLVJXAXGUUCUURMWCNZQZQUUTGMSZQZUVBWTMSZQZPXAX
      GSUUCUVFUUMUURUVEWDWFTTUVHUVJUUTUVGUVDGMVCWGVHZTUIGWTLMVBRWCWCVIVLVJXAXHU
      UCUUQUVEQZQGISZUVGQZWTISZUVIQZPXAXHSUUCUVLUUMUUQUVEURWFTTUVNUVPUVMUVGWHUV
      KTUIGWTIMVBRRWCVIVLVJWIVKYIYRXAXBUUCUUQUUEQZQUVMUUHQZUVOUUJQZPXAXBSUUCUVQ
      UUMUUQUUEURVETTUVRUVSUVMUUHWHUUNTUIGWTIJVBRRRVIVLVJWJWKWTIKUULWLXARNXIYSU
      TGWTWMXBXCXDXEXFXGXHRXAWNUMWBVMWOWPWQWR $.

    $( The neighborhood of the third vertex of graph ` G ` .  (Contributed by
       AV, 9-Aug-2025.) $)
    usgrexmpl2nb2 $p |- ( G NeighbVtx 2 ) = { 1 , 3 } $=
      ( c2 cpr cc0 c3 c1 c4 c5 wcel wceq wo wa cvv wne pm3.2i cnbgr csn ctp cun
      vn co crab 2ex tpid3 orci elun mpbir usgrexmpl2nblem ax-mp 1eltp012 tpid1
      cv 3ex olci prssi wb w3o vex c0ex 1ex 2ne0 1ne2 necomi prneimg mp2 biorfi
      neii prcom eqeq2i a1i id preq2b bitr2i 3nn0 bicomd orbi12i 3orass 3bitr4i
      cn0 2re 4nn0 2lt3 ltneii 2lt4 5nn0 2lt5 3pm3.2ni biorfri 3bitri elpr prex
      cr el7g eqrrabd eqcomd mp2an eqtri ) BGUAUFZGUEUQZHZIJHZUBIKHZKGHZGJHZUCJ
      LHZLMHZIMHZUCUDUDNZUEIKGUCZJLMUCZUDZUGZKJHZGXPNZXCXQOXSGXNNZGXONZPXTYAIKG
      UHUIUJGXNXOUKULUEABGCDEFUMUNKXPNZJXPNZXQXROYBKXNNZKXONZPYDYEUOUJKXNXOUKUL
      YCJXNNZJXONZPYGYFJLMURUPUSJXNXOUKULYBYCQZXRXQYHXMUEXPXRKJXPUTXDXRNZXMVAYH
      XDXPNQXDKOZXDJOZPZXEXFOZXEXGOZXEXHOZXEXIOZVBZXEXJOZXEXKOZXEXLOZVBZPZPZYIX
      MYLYQUUBUUCYOYPPZYNUUDPYLYQYNUUDXEXGGRNZXDRNZQZIRNZKRNZQZQGISZGKSZQZXDISZ
      XDKSQZPXEXGSUUGUUJUUEUUFUHUEVCZTUUHUUIVDVETTUUMUUOUUKUULVFKGVGVHTUJGXDIKR
      RRRVIVJVLVKYJYOYKYPYOXEGKHZOZYJXHUUQXEKGVMVNUUIUURYJVAVEUUIXDKGRRUUFUUIUU
      PVOUUIVPVQUNVRJWDNZYKYPVAVSUUSYPYKUUSXDJGRWDUUFUUSUUPVOUUSVPVQVTUNWAYNYOY
      PWBWCUUAYQYRYSYTXEXJGWQNZUUFQZJRNZLWDNZQZQGJSZGLSZQZXDJSZXDLSZQZPXEXJSUVA
      UVDUUTUUFWEUUPTZUVBUVCURWFTTUVGUVJUVEUVFGJWEWGWHZGLWEWIWHZTUJGXDJLWQRRWDV
      IVJVLXEXKUVAUVCMWDNZQZQUVFGMSZQZUVIXDMSZQZPXEXKSUVAUVOUVKUVCUVNWFWJTTUVQU
      VSUVFUVPUVMGMWEWKWHZTUJGXDLMWQRWDWDVIVJVLXEXLUVAUUHUVNQZQUUKUVPQZUUNUVRQZ
      PXEXLSUVAUWAUVKUUHUVNVDWJTTUWBUWCUUKUVPVFUVTTUJGXDIMWQRRWDVIVJVLWLWMYMUUB
      XEXFUVAUUHUVBQZQUUKUVEQZUUNUVHQZPXEXFSUVAUWDUVKUUHUVBVDURTTUWEUWFUUKUVEVF
      UVLTUJGXDIJWQRRRVIVJVLVKWNXDKJUUPWOXERNXMUUCVAGXDWPXFXGXHXIXJXKXLRXEWRUNW
      CVOWSWTXAXB $.

    $( The neighborhood of the forth vertex of graph ` G ` .  (Contributed by
       AV, 9-Aug-2025.) $)
    usgrexmpl2nb3 $p |- ( G NeighbVtx 3 ) = { 0 , 2 , 4 } $=
      ( c3 cpr cc0 c1 c2 c4 c5 wcel wceq wo wa cvv wne pm3.2i cnbgr csn ctp cun
      vn co cv crab tpid1 olci elun mpbir usgrexmpl2nblem ax-mp c0ex orci tpid3
      3ex 2ex cn0 4nn0 elexi tpid2 w3a tpssi wb w3o 3orass eltp prex el7g prcom
      vex eqeq2i a1i elex preq2b bitri 3orrot wn cr 1re 1lt3 gtneii 2re prneimg
      2lt3 mp2 neii id 3ne0 3bior2fd 3orcomb 3bitr2i 5nn0 3re 3lt4 3lt5 orbi12i
      ltneii 3bitr4i eqrrabd mp3an eqtr4i ) BGUAUFZGUEUGZHZIGHZUBIJHZJKHZKGHZUC
      GLHZLMHZIMHZUCUDUDNZUEIJKUCZGLMUCZUDZUHZIKLUCZGXRNZXEXSOYAGXPNZGXQNZPYCYB
      GLMURUIUJGXPXQUKULUEABGCDEFUMUNIXRNZKXRNZLXRNZXTXSOYDIXPNZIXQNZPYGYHIJKUO
      UIUPIXPXQUKULYEKXPNZKXQNZPYIYJIJKUSUQUPKXPXQUKULYFLXPNZLXQNZPYLYKGLMLUTVA
      VBVCUJLXPXQUKULYDYEYFVDZXOUEXRXTIKLXRVEXFXTNZXOVFYMXFXRNQXFIOZXFKOZXFLOZV
      GYOYPYQPZPZYNXOYOYPYQVHXFIKLUEVMZVIXOXGXHOZXGXIOZXGXJOZXGXKOZVGZXGXLOZXGX
      MOZXGXNOZVGZPZPZYSXGRNXOUUKVFGXFVJXHXIXJXKXLXMXNRXGVKUNUUAYOUUJYRUUAXGGIH
      ZOZYOXHUULXGIGVLVNIRNZUUMYOVFUOUUNXFIGRRXFRNZUUNYTVOIRVPVQUNVRUUEYPUUIYQU
      UEUUCUUDUUBVGZUUDYPUUBUUCUUDVSUUDUUCUUBUUDVGZUUPUUCVTZUUDUUQVFXGXJGRNZUUO
      QZJWANZKRNZQZQGJSZGKSZQZXFJSZXFKSQZPXGXJSUUTUVCUUSUUOURYTTZUVAUVBWBUSTTUV
      FUVHUVDUVEJGWBWCWDZKGWEWGWDTUPGXFJKRRWARWFWHWIUURUUDUUBUUCUURWJUUBVTUURXG
      XIUUTUUNUVAQZQGISZUVDQZXFISZUVGQZPXGXISUUTUVKUVIUUNUVAUOWBTTUVMUVOUVLUVDW
      KUVJTUPGXFIJRRRWAWFWHWIVOWLUNUUCUUBUUDWMVRUUDXGGKHZOZYPXKUVPXGKGVLVNUVBUV
      QYPVFUSUVBXFKGRRUUOUVBYTVOKRVPVQUNVRWNUUIUUGUUHUUFVGZUUFYQUUFUUGUUHVSUUGV
      TZUUFUVRVFXGXMUUTLUTNZMUTNZQZQGLSZGMSZQZXFLSXFMSZQZPXGXMSUUTUWBUVIUVTUWAV
      AWOTTUWEUWGUWCUWDGLWPWQWTGMWPWRWTZTUPGXFLMRRUTUTWFWHWIUVSUUFUUHUUGUVSWJUU
      HVTUVSXGXNUUTUUNUWAQZQUVLUWDQZUVNUWFQZPXGXNSUUTUWIUVIUUNUWAUOWOTTUWJUWKUV
      LUWDWKUWHTUPGXFIMRRRUTWFWHWIVOWLUNUVTUUFYQVFVAUVTXFLGRRUUOUVTYTVOLUTVPVQU
      NWNWSWSVRXAVOXBXCXD $.

    $( The neighborhood of the fifth vertex of graph ` G ` .  (Contributed by
       AV, 9-Aug-2025.) $)
    usgrexmpl2nb4 $p |- ( G NeighbVtx 4 ) = { 3 , 5 } $=
      ( c4 cpr cc0 c3 c1 c5 wcel wceq wo cr wa cvv wne pm3.2i vn cnbgr co cv c2
      csn ctp cun crab 4re elexi tpid2 olci mpbir usgrexmpl2nblem ax-mp 3ex 5re
      elun tpid1 tpid3 prssi wb w3o vex c0ex 4ne0 4lt5 ltneii orci prneimg neii
      mp2 biorfri prcom eqeq2i a1i id preq2b bicomi orbi12i df-3or 3bitr4i 1lt4
      bitri 1re gtneii 2re 2lt4 3re 3lt4 3pm3.2ni biorfi elpr prex el7g eqrrabd
      eqcomd mp2an eqtri ) BGUBUCZGUAUDZHZIJHZUFIKHZKUEHZUEJHZUGJGHZGLHZILHZUGU
      HUHMZUAIKUEUGZJGLUGZUHZUIZJLHZGXNMZXAXONXQGXLMZGXMMZOXSXRJGLGPUJUKZULUMGX
      LXMUSUNUAABGCDEFUOUPJXNMZLXNMZXOXPNYAJXLMZJXMMZOYDYCJGLUQUTUMJXLXMUSUNYBL
      XLMZLXMMZOYFYEJGLLPURUKVAUMLXLXMUSUNYAYBQZXPXOYGXKUAXNXPJLXNVBXBXPMZXKVCY
      GXBXNMQXBJNZXBLNZOZXCXDNZXCXENZXCXFNZXCXGNZVDZXCXHNZXCXINZXCXJNZVDZOZOZYH
      XKYKUUAUUBYKYTUUAYQYROZUUCYSOYKYTYSUUCXCXJGPMZXBRMZQZIRMZLPMZQZQGISZGLSZQ
      ZXBISZXBLSQZOXCXJSUUFUUIUUDUUEUJUAVEZTZUUGUUHVFURTTUULUUNUUJUUKVGGLUJVHVI
      TVJGXBILPRRPVKVMVLVNYIYQYJYRYQYIYQXCGJHZNZYIXHUUQXCJGVOVPJRMZUURYIVCUQUUS
      XBJGRRUUEUUSUUOVQUUSVRVSUPWEVTYRYJUUHYRYJVCURUUHXBLGRPUUEUUHUUOVQUUHVRVSU
      PVTWAYQYRYSWBWCYPYTYMYNYOXCXEGRMZUUEQZUUGKPMZQZQUUJGKSZQZUUMXBKSZQZOXCXES
      UVAUVCUUTUUEXTUUOTUUGUVBVFWFTTUVEUVGUUJUVDVGKGWFWDWGZTVJGXBIKRRRPVKVMVLXC
      XFUUFUVBUEPMZQZQUVDGUESZQZUVFXBUESZQZOXCXFSUUFUVJUUPUVBUVIWFWHTTUVLUVNUVD
      UVKUVHUEGWHWIWGZTVJGXBKUEPRPPVKVMVLXCXGUUFUVIUUSQZQUVKGJSZQZUVMXBJSZQZOXC
      XGSUUFUVPUUPUVIUUSWHUQTTUVRUVTUVKUVQUVOJGWJWKWGZTVJGXBUEJPRPRVKVMVLWLWMWE
      YLUUAXCXDUUFUUGUUSQZQUUJUVQQZUUMUVSQZOXCXDSUUFUWBUUPUUGUUSVFUQTTUWCUWDUUJ
      UVQVGUWATVJGXBIJPRRRVKVMVLWMWEXBJLUUOWNXCRMXKUUBVCGXBWOXDXEXFXGXHXIXJRXCW
      PUPWCVQWQWRWSWT $.

    $( The neighborhood of the sixth vertex of graph ` G ` .  (Contributed by
       AV, 10-Aug-2025.) $)
    usgrexmpl2nb5 $p |- ( G NeighbVtx 5 ) = { 0 , 4 } $=
      ( c5 cpr cc0 c3 c1 c4 wcel wceq wo cr wa cvv wne pm3.2i vn cnbgr co cv c2
      csn ctp crab elexi tpid3 olci elun mpbir usgrexmpl2nblem ax-mp c0ex tpid1
      cun 5re orci 4re tpid2 prssi wb w3o vex 3re 3lt5 gtneii 4lt5 prneimg neii
      mp2 biorfi orcom prcom eqeq2i a1i id preq2b bitr2i orbi12i 3orass 3bitr4i
      bitri 0re 1re 5pos 1lt5 2lt5 3pm3.2ni elpr prex el7g eqrrabd eqcomd mp2an
      2re eqtri ) BGUBUCZGUAUDZHZIJHZUFIKHZKUEHZUEJHZUGJLHZLGHZIGHZUGURURMZUAIK
      UEUGZJLGUGZURZUHZILHZGXMMZWTXNNXPGXKMZGXLMZOXRXQJLGGPUSUIUJUKGXKXLULUMUAA
      BGCDEFUNUOIXMMZLXMMZXNXONXSIXKMZIXLMZOYAYBIKUEUPUQUTIXKXLULUMXTLXKMZLXLMZ
      OYDYCJLGLPVAUIVBUKLXKXLULUMXSXTQZXOXNYEXJUAXMXOILXMVCXAXOMZXJVDYEXAXMMQXA
      INZXALNZOZXBXCNZXBXDNZXBXENZXBXFNZVEZXBXGNZXBXHNZXBXINZVEZOZOZYFXJYIYSYTY
      IYRYSYPYQOZYOUUAOYIYRYOUUAXBXGGPMZXARMZQZJPMZLPMZQZQGJSZGLSZQZXAJSZXALSQZ
      OXBXGSUUDUUGUUBUUCUSUAVFZTZUUEUUFVGVATTUUJUULUUHUUIJGVGVHVIZLGVAVJVITUTGX
      AJLPRPPVKVMVLVNYIYHYGOUUAYGYHVOYHYPYGYQYPXBGLHZNZYHXHUUPXBLGVPVQUUFUUQYHV
      DVAUUFXALGRPUUCUUFUUMVRUUFVSVTUOWAYQXBGIHZNZYGXIUURXBIGVPVQIRMZUUSYGVDUPU
      UTXAIGRRUUCUUTUUMVRUUTVSVTUOWAWBWEYOYPYQWCWDYNYRYKYLYMXBXDUUDIPMZKPMZQZQG
      ISZGKSZQZXAISZXAKSZQZOXBXDSUUDUVCUUNUVAUVBWFWGTTUVFUVIUVDUVEIGWFWHVIZKGWG
      WIVIZTUTGXAIKPRPPVKVMVLXBXEUUDUVBUEPMZQZQUVEGUESZQZUVHXAUESZQZOXBXESUUDUV
      MUUNUVBUVLWGWRTTUVOUVQUVEUVNUVKUEGWRWJVIZTUTGXAKUEPRPPVKVMVLXBXFUUDUVLUUE
      QZQUVNUUHQZUVPUUKQZOXBXFSUUDUVSUUNUVLUUEWRVGTTUVTUWAUVNUUHUVRUUOTUTGXAUEJ
      PRPPVKVMVLWKVNWEYJYSXBXCUUDUVAUUEQZQUVDUUHQZUVGUUKQZOXBXCSUUDUWBUUNUVAUUE
      WFVGTTUWCUWDUVDUUHUVJUUOTUTGXAIJPRPPVKVMVLVNWEXAILUUMWLXBRMXJYTVDGXAWMXCX
      DXEXFXGXHXIRXBWNUOWDVRWOWPWQWS $.

    $d G a b c t $.
    $( ` G ` is triangle-free.  (Contributed by AV, 10-Aug-2025.) $)
    usgrexmpl2trifr $p |- -. E. t t e. ( GrTriangles ` G ) $=
      ( cc0 c3 c1 c2 c4 c5 wa orcd adantr neneqd adantl olcd jca vb cgrtri wcel
      vc va cv cfv wex wne cpr csn ctp cun cnbgr co wrex wceq w3a usgrexmpl2nb0
      wn wo wral w3o eleq2i vex eltp bitri eqtr3 ax-1ne0 neeq1 mpbiri 3ne0 2lt3
      2re gtneii 1re 1lt3 1ne2 3jca ltneii 1lt4 1lt5 jca31 5pos 3jaodan necon2i
      0re 2lt5 4re 4lt5 3lt4 3lt5 3jaoian syl2anb rgen2 usgrexmpl2nb1 elpr 2ne0
      3re 4pos 2lt4 ccase usgrexmpl2nb2 c0ex 1ex 2ex raleqdv raleqbidv mpbir3an
      oveq2 raltp usgrexmpl2nb3 usgrexmpl2nb4 usgrexmpl2nb5 3ex 4nn0 elexi 5nn0
      cn0 ralunb mpbir2an ianor nne anbi12i 3anbi123i preq12b 3orbi123i orbi12i
      ioran 3ioran orbi2i xchnxbir elun prex elsn bitr2i 3ralbii ralnex3 eqcomi
      mpbi cusgr wb usgrexmpl2 cvtx usgrexmpl2vtx cedg usgrexmpl2edg eqid ax-mp
      usgrgrtrirex mtbir ) AUFCUBUGUCAUHZUAUFZUDUFZUIZUUMUUNUJZHIUJZUKZHJUJZJKU
      JZKIUJZULZILUJZLMUJZHMUJZULZUMZUMZUCZNZUDCUEUFZUNUOZUPUAUVLUPUEHJKULZILMU
      LZUMZUPZUUMUUNUQZUUMHUQZUTZUUNIUQZUTZVAZUUMIUQZUTZUUNHUQZUTZVAZNZUVSUUNJU
      QZUTZVAZUUMJUQZUTZUWFVAZNZUWMUUNKUQZUTZVAZUUMKUQZUTZUWJVAZNZUWTUWAVAZUWDU
      WQVAZNZURZUWDUUNLUQZUTZVAZUUMLUQZUTZUWAVAZNZUXKUUNMUQZUTZVAZUUMMUQZUTZUXH
      VAZNZUVSUXOVAZUXRUWFVAZNZURZNZNZVAZUDUVLVBZUAUVLVBZUEUVOVBZUVPUTZUYJUYIUE
      UVMVBZUYIUEUVNVBZUYLUYGUDCHUNUOZVBZUAUYNVBZUYGUDCJUNUOZVBZUAUYQVBZUYGUDCK
      UNUOZVBZUAUYTVBZUYGUAUDUYNUYNUUMUYNUCZUWLUWCUXQVCZUWIUVTUXNVCZUYGUUNUYNUC
      ZVUCUUMJIMULZUCVUDUYNVUGUUMBCDEFGUSZVDUUMJIMUAVEZVFVGVUFUUNVUGUCVUEUYNVUG
      UUNVUHVDUUNJIMUDVEZVFVGUWLVUEUYGUWCUXQUWLUWIUYGUVTUXNUWLUWINUVQUYFUUMUUNJ
      VHOZUWLUVTNZUYFUVQVULUWBUWGUYEVULUVSUWAVULUUMHUWLUUMHUIZUVTUWLVUMJHUIZVIU
      UMJHVJVKZPQZOVULUWFUWDVULUUNHUVTUUNHUIZUWLUVTVUQIHUIZVLUUNIHVJVKZRQZSVULU
      XFUYDVULUWOUXBUXEVULUWKUWNVULUVSUWJVUPOVULUWFUWMVUTSTVULUWRUXAVULUWQUWMVU
      LUUNKUVTUUNKUIZUWLUVTVVAIKUIZKIVNVMVOZUUNIKVJVKZRQZSVULUWJUWTVULUUNJUVTUU
      NJUIZUWLUVTVVFIJUIJIVPVQVOUUNIJVJVKZRQSTVULUXCUXDVULUWTUWAVULUUMKUWLUUMKU
      IZUVTUWLVVHJKUIZVRUUMJKVJVKZPQOVULUWQUWDVVESTVSVULUXMUXTUYCVULUXIUXLVULUW
      DUXHVULUUMIUWLUUMIUIZUVTUWLVVKJIUIJIVPVQVTUUMJIVJVKZPQOVULUXKUWAVULUUMLUW
      LUUMLUIZUVTUWLVVMJLUIZJLVPWAVTZUUMJLVJVKZPQZOTVULUXPUXSVULUXKUXOVVQOVULUX
      RUXHVULUUMMUWLUUMMUIZUVTUWLVVRJMUIZJMVPWBVTZUUMJMVJVKZPQOTVULUYAUYBVULUVS
      UXOVUPOVULUWFUXRVUTSTVSTWCSZUWLUXNNZUYFUVQVWCUWBUWGUYEVWCUVSUWAVWCUUMHUWL
      VUMUXNVUOPQZOVWCUWDUWFVWCUUMIUWLVVKUXNVVLPQZOVWCUXFUYDVWCUWOUXBUXEVWCUWKU
      WNVWCUVSUWJVWDOVWCUWFUWMVWCUUNHUXNVUQUWLUXNVUQMHUIZHMWGWDVOZUUNMHVJVKZRQZ
      STVWCUWRUXAVWCUWQUWMVWCUUNKUXNVVAUWLUXNVVAMKUIZKMVNWHVOZUUNMKVJVKZRQSVWCU
      WTUWJVWCUUMKUWLVVHUXNVVJPQZOTVWCUXCUXDVWCUWTUWAVWMOVWCUWDUWQVWEOTVSVWCUXM
      UXTUYCVWCUXIUXLVWCUWDUXHVWEOVWCUXKUWAVWCUUMLUWLVVMUXNVVPPQZOTVWCUXPUXSVWC
      UXKUXOVWNOVWCUXRUXHVWCUUMMUWLVVRUXNVWAPQOTVWCUYAUYBVWCUVSUXOVWDOVWCUWFUXR
      VWISTVSTWCSWEUWCUWIUYGUVTUXNUWCUWINZUYFUVQVWOUWBUWGUYEVWOUVSUWAVWOUUMHUWC
      VUMUWIUWCVUMVURVLUUMIHVJVKZPQZOVWOUWFUWDVWOUUNHUWIVUQUWCUWIVUQVUNVIUUNJHV
      JVKZRQZSVWOUXFUYDVWOUWOUXBUXEVWOUWKUWNVWOUVSUWJVWQOVWOUWFUWMVWSSTVWOUWRUX
      AVWOUWMUWQVWOUUMJUWCUUMJUIZUWIUUMJUUMIVVLWFZPQOVWOUWTUWJVWOUUMKUWCVVHUWIU
      WCVVHVVBVVCUUMIKVJVKZPQZOTVWOUXCUXDVWOUWTUWAVXCOVWOUWQUWDVWOUUNKUWIVVAUWC
      UWIVVAVVIVRUUNJKVJVKZRQSTVSVWOUXMUXTUYCVWOUXIUXLVWOUXHUWDVWOUUNLUWIUUNLUI
      ZUWCUWIVXEVVNVVOUUNJLVJVKZRQZSVWOUWAUXKVWOUUNIUWIUUNIUIZUWCUUNIUUNJVVGWFZ
      RQSTVWOUXPUXSVWOUXOUXKVWOUUNMUWIUUNMUIZUWCUWIVXJVVSVVTUUNJMVJVKZRQSVWOUXH
      UXRVXGSTVWOUYAUYBVWOUVSUXOVWQOVWOUWFUXRVWSSTVSTWCSZUWCUVTNUVQUYFUUMUUNIVH
      OZUWCUXNNZUYFUVQVXNUWBUWGUYEVXNUVSUWAVXNUUMHUWCVUMUXNVWPPQZOVXNUWFUWDVXNU
      UNHUXNVUQUWCVWHRQZSVXNUXFUYDVXNUWOUXBUXEVXNUWKUWNVXNUVSUWJVXOOVXNUWFUWMVX
      PSTVXNUWRUXAVXNUWMUWQVXNUUMJUWCVWTUXNVXAPQOVXNUWJUWTVXNUUNJUXNVVFUWCUUNJU
      UNMVXKWFRQSTVXNUXCUXDVXNUWTUWAVXNUUMKUWCVVHUXNVXBPQOVXNUWQUWDVXNUUNKUXNVV
      AUWCVWLRQSTVSVXNUXMUXTUYCVXNUXIUXLVXNUXHUWDVXNUUNLUXNVXEUWCUXNVXEMLUIZLMW
      IWJVOZUUNMLVJVKZRQZSVXNUXKUWAVXNUUMLUWCVVMUXNUWCVVMILUIZILWSWKVTZUUMILVJV
      KZPQZOTVXNUXPUXSVXNUXKUXOVYDOVXNUXHUXRVXTSTVXNUYAUYBVXNUVSUXOVXOOVXNUWFUX
      RVXPSTVSTWCSZWEUXQUWIUYGUVTUXNUXQUWINZUYFUVQVYFUWBUWGUYEVYFUWAUVSVYFUUNIU
      WIVXHUXQVXIRQZSVYFUWFUWDVYFUUNHUWIVUQUXQVWRRQZSVYFUXFUYDVYFUWOUXBUXEVYFUW
      KUWNVYFUVSUWJVYFUUMHUXQVUMUWIUXQVUMVWFVWGUUMMHVJVKZPQZOVYFUWFUWMVYHSTVYFU
      WRUXAVYFUWMUWQVYFUUMJUXQVWTUWIUUMJUUMMVWAWFZPQOVYFUWTUWJVYFUUMKUXQVVHUWIU
      XQVVHVWJVWKUUMMKVJVKZPQOTVYFUXCUXDVYFUWAUWTVYGSVYFUWQUWDVYFUUNKUWIVVAUXQV
      XDRQSTVSVYFUXMUXTUYCVYFUXIUXLVYFUWDUXHVYFUUMIUXQVVKUWIUXQVVKMIUIIMWSWLVOU
      UMMIVJVKZPQOVYFUWAUXKVYGSTVYFUXPUXSVYFUXOUXKVYFUUNMUWIVXJUXQVXKRQSVYFUXHU
      XRVYFUUNLUWIVXEUXQVXFRQSTVYFUYAUYBVYFUVSUXOVYJOVYFUWFUXRVYHSTVSTWCSUXQUVT
      NZUYFUVQVYNUWBUWGUYEVYNUVSUWAVYNUUMHUXQVUMUVTVYIPQZOVYNUWFUWDVYNUUNHUVTVU
      QUXQVUSRQZSVYNUXFUYDVYNUWOUXBUXEVYNUWKUWNVYNUVSUWJVYOOVYNUWFUWMVYPSTVYNUW
      RUXAVYNUWMUWQVYNUUMJUXQVWTUVTVYKPQOVYNUWJUWTVYNUUNJUVTVVFUXQVVGRQSTVYNUXC
      UXDVYNUWTUWAVYNUUMKUXQVVHUVTVYLPQOVYNUWDUWQVYNUUMIUXQVVKUVTVYMPQZOTVSVYNU
      XMUXTUYCVYNUXIUXLVYNUWDUXHVYQOVYNUXKUWAVYNUUMLUXQVVMUVTUXQVVMVXQVXRUUMMLV
      JVKZPQZOTVYNUXPUXSVYNUXKUXOVYSOVYNUXHUXRVYNUUNLUVTVXEUXQUVTVXEVYAVYBUUNIL
      VJVKZRQSTVYNUYAUYBVYNUVSUXOVYOOVYNUWFUXRVYPSTVSTWCSZUXQUXNNUVQUYFUUMUUNMV
      HOZWEWMWNWOUYGUAUDUYQUYQUUMUYQUCZUVRUWSVAZUWEUWPVAZUYGUUNUYQUCZWUCUUMHKUJ
      ZUCWUDUYQWUGUUMBCDEFGWPZVDUUMHKVUIWQVGWUFUUNWUGUCWUEUYQWUGUUNWUHVDUUNHKVU
      JWQVGUVRUWEUWSUWPUYGUVRUWENUVQUYFUUMUUNHVHOZUWSUWENZUYFUVQWUJUWBUWGUYEWUJ
      UVSUWAWUJUUMHUWSVUMUWEUWSVUMKHUIZWRUUMKHVJVKZPQZOWUJUWDUWFWUJUUMIUWSVVKUW
      EUUMIUUMKVXBWFZPQZOWUJUXFUYDWUJUWOUXBUXEWUJUWKUWNWUJUVSUWJWUMOWUJUWMUWFWU
      JUUMJUWSVWTUWEUUMJUUMKVVJWFZPQZOTWUJUWRUXAWUJUWMUWQWUQOWUJUWJUWTWUJUUNJUW
      EVVFUWSUUNJUUNHVWRWFZRQSTWUJUXCUXDWUJUWAUWTWUJUUNIUWEVXHUWSUUNIUUNHVUSWFZ
      RQZSWUJUWDUWQWUOOTVSWUJUXMUXTUYCWUJUXIUXLWUJUWDUXHWUOOWUJUWAUXKWUTSTWUJUX
      PUXSWUJUXOUXKWUJUUNMUWEVXJUWSUUNMUUNHVWHWFZRQSWUJUXHUXRWUJUUNLUWEVXEUWSUW
      EVXEHLUIZHLWGWTVTZUUNHLVJVKZRQSTWUJUYAUYBWUJUVSUXOWUMOWUJUXRUWFWUJUUMMUWS
      VVRUWEUUMMUUMKVYLWFZPQOTVSTWCSZUVRUWPNZUYFUVQWVGUWBUWGUYEWVGUWAUVSWVGUUNI
      UWPVXHUVRUUNIUUNKVVDWFZRQZSWVGUWFUWDWVGUUNHUWPVUQUVRUWPVUQWUKWRUUNKHVJVKZ
      RQZSWVGUXFUYDWVGUWOUXBUXEWVGUWKUWNWVGUWJUVSWVGUUNJUWPVVFUVRUUNJUUNKVXDWFZ
      RQSWVGUWFUWMWVKSTWVGUWRUXAWVGUWMUWQWVGUUMJUVRVWTUWPUUMJUUMHVUOWFZPQOWVGUW
      TUWJWVGUUMKUVRVVHUWPUUMKUUMHWULWFZPQOTWVGUXCUXDWVGUWAUWTWVISWVGUWDUWQWVGU
      UMIUVRVVKUWPUUMIUUMHVWPWFZPQZOTVSWVGUXMUXTUYCWVGUXIUXLWVGUWDUXHWVPOWVGUWA
      UXKWVISTWVGUXPUXSWVGUXKUXOWVGUUMLUVRVVMUWPUVRVVMWVBWVCUUMHLVJVKZPQOWVGUXR
      UXHWVGUUMMUVRVVRUWPUUMMUUMHVYIWFZPQOTWVGUYAUYBWVGUXOUVSWVGUUNMUWPVXJUVRUU
      NMUUNKVWLWFZRQSWVGUWFUXRWVKSTVSTWCSZUWSUWPNZUYFUVQWWAUWBUWGUYEWWAUVSUWAWW
      AUUMHUWSVUMUWPWULPQZOWWAUWFUWDWWAUUNHUWPVUQUWSWVJRQZSWWAUXFUYDWWAUWOUXBUX
      EWWAUWKUWNWWAUVSUWJWWBOWWAUWFUWMWWCSTWWAUWRUXAWWAUWMUWQWWAUUMJUWSVWTUWPWU
      PPQOWWAUWJUWTWWAUUNJUWPVVFUWSWVLRQSTWWAUXCUXDWWAUWAUWTWWAUUNIUWPVXHUWSWVH
      RQSWWAUWDUWQWWAUUMIUWSVVKUWPWUNPQZOTVSWWAUXMUXTUYCWWAUXIUXLWWAUWDUXHWWDOW
      WAUXKUWAWWAUUMLUWSVVMUWPUWSVVMKLUIZKLVNXAVTZUUMKLVJVKZPQZOTWWAUXPUXSWWAUX
      KUXOWWHOWWAUXRUXHWWAUUMMUWSVVRUWPWVEPQOTWWAUYAUYBWWAUVSUXOWWBOWWAUWFUXRWW
      CSTVSTWCSZXBWNWOUYGUAUDUYTUYTUUMUYTUCZUWLUWCVAZUWIUVTVAZUYGUUNUYTUCZWWJUU
      MJIUJZUCWWKUYTWWNUUMBCDEFGXCZVDUUMJIVUIWQVGWWMUUNWWNUCWWLUYTWWNUUNWWOVDUU
      NJIVUJWQVGUWLUWIUWCUVTUYGVUKVXLVWBVXMXBWNWOUYIUYPUYSVUBUEHJKXDXEXFUVKHUQZ
      UYHUYOUAUVLUYNUVKHCUNXJZWWPUYGUDUVLUYNWWQXGXHUVKJUQZUYHUYRUAUVLUYQUVKJCUN
      XJZWWRUYGUDUVLUYQWWSXGXHUVKKUQZUYHVUAUAUVLUYTUVKKCUNXJZWWTUYGUDUVLUYTWXAX
      GXHXKXIUYMUYGUDCIUNUOZVBZUAWXBVBZUYGUDCLUNUOZVBZUAWXEVBZUYGUDCMUNUOZVBZUA
      WXHVBZUYGUAUDWXBWXBUUMWXBUCZUVRUWSUXJVCZUWEUWPUXGVCZUYGUUNWXBUCZWXKUUMHKL
      ULZUCWXLWXBWXOUUMBCDEFGXLZVDUUMHKLVUIVFVGWXNUUNWXOUCWXMWXBWXOUUNWXPVDUUNH
      KLVUJVFVGUVRWXMUYGUWSUXJUVRUWEUYGUWPUXGWUIWVTUVRUXGNZUYFUVQWXQUWBUWGUYEWX
      QUWAUVSWXQUUNIUXGVXHUVRUUNIUUNLVYTWFZRQZSWXQUWDUWFWXQUUMIUVRVVKUXGWVOPQZO
      WXQUXFUYDWXQUWOUXBUXEWXQUWKUWNWXQUWJUVSWXQUUNJUXGVVFUVRUUNJUUNLVXFWFZRQSW
      XQUWMUWFWXQUUMJUVRVWTUXGWVMPQZOTWXQUWRUXAWXQUWMUWQWYBOWXQUWTUWJWXQUUMKUVR
      VVHUXGWVNPQOTWXQUXCUXDWXQUWAUWTWXSSWXQUWDUWQWXTOTVSWXQUXMUXTUYCWXQUXIUXLW
      XQUWDUXHWXTOWXQUWAUXKWXSSTWXQUXPUXSWXQUXKUXOWXQUUMLUVRVVMUXGWVQPQOWXQUXRU
      XHWXQUUMMUVRVVRUXGWVRPQOTWXQUYAUYBWXQUXOUVSWXQUUNMUXGVXJUVRUUNMUUNLVXSWFR
      QSWXQUWFUXRWXQUUNHUXGVUQUVRUUNHUUNLWVDWFZRQSTVSTWCSZWEUWSUWEUYGUWPUXGWVFW
      WIUWSUXGNZUYFUVQWYEUWBUWGUYEWYEUVSUWAWYEUUMHUWSVUMUXGWULPQZOWYEUWFUWDWYEU
      UNHUXGVUQUWSWYCRQZSWYEUXFUYDWYEUWOUXBUXEWYEUWKUWNWYEUVSUWJWYFOWYEUWFUWMWY
      GSTWYEUWRUXAWYEUWMUWQWYEUUMJUWSVWTUXGWUPPQOWYEUWJUWTWYEUUNJUXGVVFUWSWYARQ
      STWYEUXCUXDWYEUWAUWTWYEUUNIUXGVXHUWSWXRRQZSWYEUWDUWQWYEUUMIUWSVVKUXGWUNPQ
      ZOTVSWYEUXMUXTUYCWYEUXIUXLWYEUWDUXHWYIOWYEUWAUXKWYHSTWYEUXPUXSWYEUXKUXOWY
      EUUMLUWSVVMUXGWWGPQOWYEUXRUXHWYEUUMMUWSVVRUXGWVEPQOTWYEUYAUYBWYEUVSUXOWYF
      OWYEUWFUXRWYGSTVSTWCSWEUXJUWEUYGUWPUXGUXJUWENZUYFUVQWYJUWBUWGUYEWYJUVSUWA
      WYJUUMHUXJVUMUWEUUMHUUMLWVQWFZPQZOWYJUWDUWFWYJUUMIUXJVVKUWEUUMIUUMLVYCWFZ
      PQZOWYJUXFUYDWYJUWOUXBUXEWYJUWKUWNWYJUVSUWJWYLOWYJUWMUWFWYJUUMJUXJVWTUWEU
      UMJUUMLVVPWFZPQOTWYJUWRUXAWYJUWQUWMWYJUUNKUWEVVAUXJUUNKUUNHWVJWFRQSWYJUWJ
      UWTWYJUUNJUWEVVFUXJWURRQSTWYJUXCUXDWYJUWAUWTWYJUUNIUWEVXHUXJWUSRQZSWYJUWD
      UWQWYNOTVSWYJUXMUXTUYCWYJUXIUXLWYJUWDUXHWYNOWYJUWAUXKWYPSTWYJUXPUXSWYJUXO
      UXKWYJUUNMUWEVXJUXJWVARQSWYJUXHUXRWYJUUNLUWEVXEUXJWVDRQSTWYJUYAUYBWYJUVSU
      XOWYLOWYJUXRUWFWYJUUMMUXJVVRUWEUUMMUUMLVYRWFPQOTVSTWCSZUXJUWPNZUYFUVQWYRU
      WBUWGUYEWYRUVSUWAWYRUUMHUXJVUMUWPWYKPQZOWYRUWFUWDWYRUUNHUWPVUQUXJWVJRQZSW
      YRUXFUYDWYRUWOUXBUXEWYRUWKUWNWYRUVSUWJWYSOWYRUWFUWMWYTSTWYRUWRUXAWYRUWMUW
      QWYRUUMJUXJVWTUWPWYOPQOWYRUWJUWTWYRUUNJUWPVVFUXJWVLRQSTWYRUXCUXDWYRUWTUWA
      WYRUUMKUXJVVHUWPUUMKUUMLWWGWFPQOWYRUWDUWQWYRUUMIUXJVVKUWPWYMPQZOTVSWYRUXM
      UXTUYCWYRUXIUXLWYRUWDUXHXUAOWYRUWAUXKWYRUUNIUWPVXHUXJWVHRQSTWYRUXPUXSWYRU
      XOUXKWYRUUNMUWPVXJUXJWVSRQSWYRUXHUXRWYRUUNLUWPVXEUXJUWPVXEWWEWWFUUNKLVJVK
      RQSTWYRUYAUYBWYRUVSUXOWYSOWYRUWFUXRWYTSTVSTWCSUXJUXGNUVQUYFUUMUUNLVHOZWEW
      MWNWOUYGUAUDWXEWXEUUMWXEUCZUWCUXQVAZUVTUXNVAZUYGUUNWXEUCZXUCUUMIMUJZUCXUD
      WXEXUGUUMBCDEFGXMZVDUUMIMVUIWQVGXUFUUNXUGUCXUEWXEXUGUUNXUHVDUUNIMVUJWQVGU
      WCUVTUXQUXNUYGVXMWUAVYEWUBXBWNWOUYGUAUDWXHWXHUUMWXHUCZUVRUXJVAZUWEUXGVAZU
      YGUUNWXHUCZXUIUUMHLUJZUCXUJWXHXUMUUMBCDEFGXNZVDUUMHLVUIWQVGXULUUNXUMUCXUK
      WXHXUMUUNXUNVDUUNHLVUJWQVGUVRUWEUXJUXGUYGWUIWYQWYDXUBXBWNWOUYIWXDWXGWXJUE
      ILMXOLXSXPXQZMXSXRXQZUVKIUQZUYHWXCUAUVLWXBUVKICUNXJZXUQUYGUDUVLWXBXURXGXH
      UVKLUQZUYHWXFUAUVLWXEUVKLCUNXJZXUSUYGUDUVLWXEXUTXGXHUVKMUQZUYHWXIUAUVLWXH
      UVKMCUNXJZXVAUYGUDUVLWXHXVBXGXHXKXIUYIUEUVMUVNXTYAUYJUVJUTZUDUVLVBUAUVLVB
      UEUVOVBUYKUYGXVCUEUAUDUVOUVLUVLXVCUUOUTZUVIUTZVAUYGUUOUVIYBXVDUVQXVEUYFUU
      MUUNYCUVRUVTNZUWCUWENZVAZUUPUUSUQZUUPUUTUQZUUPUVAUQZVCZUUPUVCUQZUUPUVDUQZ
      UUPUVEUQZVCZVAZVAZUYFUVIXVHUVRUWINZUWLUWENZVAZUWLUWPNZUWSUWINZVAZUWSUVTNZ
      UWCUWPNZVAZVCZUWCUXGNZUXJUVTNZVAZUXJUXNNZUXQUXGNZVAZUVRUXNNZUXQUWENZVAZVC
      ZVAZVAZUYFXVRXWTUTXVHUTZXWSUTZNUYFXVHXWSYIXXAUWHXXBUYEXXAXVFUTZXVGUTZNUWH
      XVFXVGYIXXCUWBXXDUWGUVRUVTYBUWCUWEYBYDVGXXBXWHUTZXWRUTZNUYEXWHXWRYIXXEUXF
      XXFUYDXXEXWAUTZXWDUTZXWGUTZURUXFXWAXWDXWGYJXXGUWOXXHUXBXXIUXEXXGXVSUTZXVT
      UTZNUWOXVSXVTYIXXJUWKXXKUWNUVRUWIYBUWLUWEYBYDVGXXHXWBUTZXWCUTZNUXBXWBXWCY
      IXXLUWRXXMUXAUWLUWPYBUWSUWIYBYDVGXXIXWEUTZXWFUTZNUXEXWEXWFYIXXNUXCXXOUXDU
      WSUVTYBUWCUWPYBYDVGYEVGXXFXWKUTZXWNUTZXWQUTZURUYDXWKXWNXWQYJXXPUXMXXQUXTX
      XRUYCXXPXWIUTZXWJUTZNUXMXWIXWJYIXXSUXIXXTUXLUWCUXGYBUXJUVTYBYDVGXXQXWLUTZ
      XWMUTZNUXTXWLXWMYIXYAUXPXYBUXSUXJUXNYBUXQUXGYBYDVGXXRXWOUTZXWPUTZNUYCXWOX
      WPYIXYCUYAXYDUYBUVRUXNYBUXQUWEYBYDVGYEVGYDVGYDVGXVQXWSXVHXVLXWHXVPXWRXVIX
      WAXVJXWDXVKXWGUUMUUNHJVUIVUJXDXEYFUUMUUNJKVUIVUJXEXFYFUUMUUNKIVUIVUJXFXOY
      FYGXVMXWKXVNXWNXVOXWQUUMUUNILVUIVUJXOXUOYFUUMUUNLMVUIVUJXUOXUPYFUUMUUNHMV
      UIVUJXDXUPYFYGYHYKYLUVIUUPUURUCZUUPUVGUCZVAXVRUUPUURUVGYMXYEXVHXYFXVQXYEU
      UPUUQUQXVHUUPUUQUUMUUNYNZYOUUMUUNHIVUIVUJXDXOYFVGXYFUUPUVBUCZUUPUVFUCZVAX
      VQUUPUVBUVFYMXYHXVLXYIXVPUUPUUSUUTUVAXYGVFUUPUVCUVDUVEXYGVFYHVGYHVGYLYHYP
      YQUVJUEUAUDUVOUVLUVLYRVGYTCUUAUCUULUVPUUBBCDEFGUUCAUVHCUVLUVOUEUAUDCUUDUG
      UVOBCDEFGUUEYSCUUFUGUVHBCDEFGUUGYSUVLUUHUUJUUIUUK $.

    $d G f t $.  $d H f $.
    usgrexmpl1.k $e |- K = <" { 0 , 1 } { 0 , 2 } { 1 , 2 } { 0 , 3 }
                              { 3 , 4 } { 3 , 5 } { 4 , 5 } "> $.
    usgrexmpl1.h $e |- H = <. V , K >. $.
    $( The graphs ` H ` and ` G ` are not isomorphic ( ` H ` contains a
       triangle, see ~ usgrexmpl1tri , whereas ` G ` does not, see
       ~ usgrexmpl2trifr .  (Contributed by AV, 10-Aug-2025.) $)
    usgrexmpl12ngric $p |- -. G ~=gr H $=
      ( vf vt cgric wbr cgrtri cfv wcel wn wi ax-mp cc0 c1 ctp cuhgr usgrexmpl2
      c2 cusgr usgruhgr gricsym usgrexmpl1tri cv cgrim co wex c0 brgric n0 cima
      wne bitri usgrexmpl2trifr wa usgrexmpl1 a1i simpl simpr grimgrtri wal cvv
      ex alnex vex imaex id wceq wb eleq1 notbid adantl spcdv pm2.21d mpsylsyld
      sylbir exlimiv sylbi mpisyl pm2.01i ) BCMNZWHCBMNZUAUBUFUCZCOPQZWHRZBUDQZ
      WHWISBUGQWMABEFGHUEBUHTZCBUITDCEFIJUJWIKUKZCBULUMZQZKUNZWKWLSZWIWPUOUSWRC
      BUPKWPUQUTWQWSKLUKZBOPZQZLUNRZWQWKWOWJURZXAQZWLLABEFGHVAWQWKXEWQWKVBZWJWO
      CBCUDQZXFCUGQXGDCEFIJVCCUHTVDWMXFWNVDWQWKVEWQWKVFVGVJXCXBRZLVHZXEWLSXBLVK
      XIXEWLXDVIQZXIXERZSWOWJKVLVMXJXHXKLXDVIXJVNWTXDVOZXHXKVPXJXLXBXEWTXDXAVQV
      RVSVTTWAWCWBWDWEWFWG $.

    $( The graphs ` H ` and ` G ` are not locally isomorphic ( ` H ` contains a
       triangle, see ~ usgrexmpl1tri , whereas ` G ` does not, see
       ~ usgrexmpl2trifr .  (Contributed by AV, 24-Aug-2025.) $)
    usgrexmpl12ngrlic $p |- -. G ~=lgr H $=
      ( vf vt cgrlic wbr cgrtri cfv wcel wn cusgr wi cc0 c1 c2 cuhgr usgrexmpl2
      ctp usgruhgr grlicsym usgrexmpl1tri cv cgrlim co wex c0 wne brgrlic bitri
      mp2b n0 usgrexmpl2trifr cuspgr usgrexmpl1 usgruspgr mp1i simpl grlimgrtri
      wa simpr ex pm2.21 mpsylsyld exlimiv sylbi mpisyl pm2.01i ) BCMNZVPCBMNZU
      AUBUCUFZCOPQZVPRZBSQZBUDQVPVQTABEFGHUEZBUGCBUHURDCEFIJUIVQKUJZCBUKULZQZKU
      MZVSVTTZVQWDUNUOWFCBUPKWDUSUQWEWGKLUJBOPQLUMZRWEVSWHVTLABEFGHUTWEVSWHWEVS
      VGZLVRWCCBCSQCVAQWIDCEFIJVBCVCVDWABVAQWIWBBVCVDWEVSVEWEVSVHVFVIWHVTVJVKVL
      VMVNVO $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Generalized Petersen graphs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

   According to Wikipedia "Generalized Petersen graph", 26-Aug-2025,
   ~ https://en.wikipedia.org/wiki/Generalized_Petersen_graph : "In graph
   theory, the _generalized Petersen graphs_ are a family of cubic graphs
   formed by connecting the vertices of a regular polygon to the corresponding
   vertices of a star polygon.  They include the Petersen graph and generalize
   one of the ways of constructing the Petersen graph. ...  Among the
   generalized Petersen graphs are the n-prism, ...".

   The vertices of the regular polygon are called "outside vertices", the
   vertices of the star polygon "inside vertices" (see A. Steimle, W. Stanton,
   "The isomorphism classes of the generalized Petersen graphs", Discrete
   Mathematics Volume 309, Issue 1, 6 January 2009, Pages 231-237:
   ~ https://doi.org/10.1016/j.disc.2007.12.074 ).  Since regular polygons are
   also considered as star polygons (with density 1), many theorems for
   "inside vertices" (with labels containing the fragment "vtx1") can be
   specialized for "outside vertices" (with labels containing the fragment
   "vtx0").

$)

  $c gPetersenGr $.

  $( Extend class notation with generalized Petersen graphs. $)
  cgpg $a class gPetersenGr $.

  ${
    $d e k n x $.
    $( Definition of generalized Petersen graphs according to Wikipedia
       "Generalized Petersen graph", 26-Aug-2025,
       ~ https://en.wikipedia.org/wiki/Generalized_Petersen_graph :  "In
       Watkins' notation, ` G ( n , k ) ` is a graph with vertex set { u_0,
       u_1, ... , u_n-1, v_0, v_1, ... , v_n-1 } and edge set { u_i u_i+1 , u_i
       v_i , v_i v_i+k | ` 0 <_ i <_ ( n - 1 ) ` } where subscripts are to be
       read modulo n and where ` k < ( n / 2 ) ` .  Some authors use the
       notation GPG(n,k)."

       Instead of ` n e. NN ` , we could restrict the first argument to
       ` n e. ( ZZ>= `` 3 ) ` (i.e., ` 3 <_ n ` ), because for ` n <_ 2 ` , the
       definition is not meaningful (since then ` ( |^ `` ( n / 2 ) ) <_ 1 `
       and therefore ` ( 1 ..^ ( |^ `` ( n / 2 ) ) ) = (/) ` , so that there
       would be no fitting second argument).  (Contributed by AV,
       26-Aug-2025.) $)
    df-gpg $a |- gPetersenGr = ( n e. NN , k e. ( 1 ..^ ( |^ ` ( n / 2 ) ) )
      |-> { <. ( Base ` ndx ) , ( { 0 , 1 } X. ( 0 ..^ n ) ) >. ,
            <. ( .ef ` ndx ) , ( _I |` { e e. ~P ( { 0 , 1 } X. ( 0 ..^ n ) ) |
      E. x e. ( 0 ..^ n ) ( e = { <. 0 , x >. , <. 0 , ( ( x + 1 ) mod n ) >. }
         \/ e = { <. 0 , x >. , <. 1 , x >. }
         \/ e = { <. 1 , x >. , <. 1 , ( ( x + k ) mod n ) >. } ) } ) >. } ) $.
  $}

  ${
    $d I e k n x $.  $d J k n $.  $d K e k n x $.  $d N e k n x $.
    gpgov.j $e |- J = ( 1 ..^ ( |^ ` ( N / 2 ) ) ) $.
    gpgov.i $e |- I = ( 0 ..^ N ) $.
    $( The generalized Petersen graph GPG(N,K).  (Contributed by AV,
       26-Aug-2025.) $)
    gpgov $p |- ( ( N e. NN /\ K e. J ) -> ( N gPetersenGr K )
                  = { <. ( Base ` ndx ) , ( { 0 , 1 } X. I ) >. ,
                      <. ( .ef ` ndx ) , ( _I |` { e e. ~P ( { 0 , 1 } X. I ) |
                E. x e. I ( e = { <. 0 , x >. , <. 0 , ( ( x + 1 ) mod N ) >. }
         \/ e = { <. 0 , x >. , <. 1 , x >. }
         \/ e = { <. 1 , x >. , <. 1 , ( ( x + K ) mod N ) >. } ) } ) >. } ) $=
      ( cfv cc0 c1 cpr cop cv caddc co cmo wceq cfzo opeq2d vn wcel cnx cbs cxp
      vk cn cedgf cid w3o wrex cpw crab cres cgpg prex c2 cdiv cceil wa eqtr4di
      cvv oveq2 xpeq2d adantr pweqd wb rexeqdv preq2d eqeq2d biidd adantl simpl
      oveq12d 3orbi123d rexbidv rabeqbidv reseq2d preq12d fvoveq1 oveq2d df-gpg
      bitrd ovmpox mp3an3 ) FUGUBEDUBUCUDIZJKLZCUEZMZUCUHIZUIBNZJANZMZJWLKOPZFQ
      PZMZLZRZWKWMKWLMZLRZWKWSKWLEOPZFQPZMZLZRZUJZACUKZBWHULZUMZUNZMZLZVBUBFEUO
      PXLRWIXKUPUAUFFEUGKUANZUQURPUSIZSPZWFWGJXMSPZUEZMZWJUIWKWMJWNXMQPZMZLZRZW
      TWKWSKWLUFNZOPZXMQPZMZLZRZUJZAXPUKZBXQULZUMZUNZMZLXLUOVBDXMFRZYCERZUTZXRW
      IYNXKYOXRWIRYPYOXQWHWFYOXPCWGYOXPJFSPCXMFJSVCHVAZVDZTVEYQYMXJWJYQYLXIUIYQ
      YJXGBYKXHYOYKXHRYPYOXQWHYSVFVEYQYJYIACUKZXGYOYJYTVGYPYOYIAXPCYRVHVEYQYIXF
      ACYQYBWRWTWTYHXEYQYAWQWKYOYAWQRYPYOXTWPWMYOXSWOJXMFWNQVCTVIVEVJYQWTVKYQYG
      XDWKYQYFXCWSYQYEXBKYQYDXAXMFQYPYDXARYOYCEWLOVCVLYOYPVMVNTVIVJVOVPWCVQVRTV
      SYOXOKFUQURPUSIZSPDYOXNUUAKSXMFUQUSURVTWAGVAABUFUAWBWDWE $.

    $( The vertices of the generalized Petersen graph GPG(N,K).  (Contributed
       by AV, 26-Aug-2025.) $)
    gpgvtx $p |- ( ( N e. NN /\ K e. J )
                   -> ( Vtx ` ( N gPetersenGr K ) ) = ( { 0 , 1 } X. I ) ) $=
      ( ve vx wcel wa co cvtx cfv cc0 c1 cpr cop wceq cvv cfzo cgpg cnx cbs cxp
      cn cedgf cid cv caddc cmo w3o wrex crab cres gpgov fveq2d prex ovexi xpex
      cpw eqid a1i ovexd eqeltrid xpexd pwexd rabexd resiexd ax-mp struct2grvtx
      pm3.2i mp1i eqtrd ) DUEICBIJZDCUAKZLMUBUCMNOPZAUDZQUBUFMUGGUHZNHUHZQZNVSO
      UIKDUJKQPRVRVTOVSQZPRVRWAOVSCUIKDUJKQPRUKHAULZGVQUTZUMZUNZQPZLMZVQVNVOWFL
      HGABCDEFUOUPVQSIZWESIZJWGVQRVNWHWIVPANOUQZANDTFURUSANDTKZRZWIFWLWDSWLWBGW
      CWDSWDVAWLVQSWLVPASSVPSIWLWJVBWLAWKSFWLNDTVCVDVEVFVGVHVIVKWEWFVQSSWFVAVJV
      LVM $.

    $( The indexed edges of the generalized Petersen graph GPG(N,K).
       (Contributed by AV, 26-Aug-2025.) $)
    gpgiedg $p |- ( ( N e. NN /\ K e. J ) -> ( iEdg ` ( N gPetersenGr K ) )
                             = ( _I |` { e e. ~P ( { 0 , 1 } X. I ) | E. x e. I
               ( e = { <. 0 , x >. , <. 0 , ( ( x + 1 ) mod N ) >. }
              \/ e = { <. 0 , x >. , <. 1 , x >. }
              \/ e = { <. 1 , x >. , <. 1 , ( ( x + K ) mod N ) >. } ) } ) ) $=
      ( wcel wa co ciedg cfv cc0 c1 cpr cop wceq cvv cfzo cn cgpg cnx cbs cedgf
      cxp cid cv caddc cmo w3o wrex crab cres gpgov fveq2d prex ovexi xpex eqid
      cpw a1i ovexd eqeltrid xpexd pwexd rabexd ax-mp pm3.2i struct2griedg mp1i
      resiexd eqtrd ) FUAIEDIJZFEUBKZLMUCUDMNOPZCUFZQUCUEMUGBUHZNAUHZQZNVSOUIKF
      UJKQPRVRVTOVSQZPRVRWAOVSEUIKFUJKQPRUKACULZBVQVAZUMZUNZQPZLMZWEVNVOWFLABCD
      EFGHUOUPVQSIZWESIZJWGWERVNWHWIVPCNOUQZCNFTHURUSCNFTKZRZWIHWLWDSWLWBBWCWDS
      WDUTWLVQSWLVPCSSVPSIWLWJVBWLCWKSHWLNFTVCVDVEVFVGVLVHVIWEWFVQSSWFUTVJVKVM
      $.

    $( The edges of the generalized Petersen graph GPG(N,K).  (Contributed by
       AV, 26-Aug-2025.) $)
    gpgedg $p |- ( ( N e. NN /\ K e. J ) -> ( Edg ` ( N gPetersenGr K ) )
                                     = { e e. ~P ( { 0 , 1 } X. I ) | E. x e. I
                 ( e = { <. 0 , x >. , <. 0 , ( ( x + 1 ) mod N ) >. }
                \/ e = { <. 0 , x >. , <. 1 , x >. }
                \/ e = { <. 1 , x >. , <. 1 , ( ( x + K ) mod N ) >. } ) } ) $=
      ( wcel co cfv crn cv cc0 cop c1 caddc cmo cpr wceq cn cgpg cedg ciedg w3o
      wa wrex cxp cpw crab edgval cid cres gpgiedg rneqd rnresi eqtrdi eqtrid )
      FUAIEDIUFZFEUBJZUCKUTUDKZLZBMZNAMZOZNVDPQJFRJOSTVCVEPVDOZSTVCVFPVDEQJFRJO
      STUEACUGBNPSCUHUIUJZUTUKUSVBULVGUMZLVGUSVAVHABCDEFGHUNUOVGUPUQUR $.
  $}

  ${
    $d I x $.  $d J x $.  $d K x $.  $d N x $.  $d Y x $.
    gpgvtxel.i $e |- I = ( 0 ..^ N ) $.
    gpgvtxel.j $e |- J = ( 1 ..^ ( |^ ` ( N / 2 ) ) ) $.
    $( Lemma for ~ gpgiedgdmel and ~ gpgedgel .  (Contributed by AV,
       2-Nov-2025.) $)
    gpgiedgdmellem $p |- ( ( N e. NN /\ K e. J ) -> ( E. x e. I
                        ( Y = { <. 0 , x >. , <. 0 , ( ( x + 1 ) mod N ) >. }
                       \/ Y = { <. 0 , x >. , <. 1 , x >. }
                       \/ Y = { <. 1 , x >. , <. 1 , ( ( x + K ) mod N ) >. } )
                           -> Y e. ~P ( { 0 , 1 } X. I ) ) ) $=
      ( wcel cc0 cop c1 co cpr wceq cvv prex a1i opelxpd cz cn wa caddc cmo w3o
      cxp cpw 0elpr01 simpr cfzo elfzoelz eleq2s adantl peano2zd simpll zmodfzo
      cv syl2anc eleqtrrdi prssd elpwd eleq1 syl5ibrcom 1elpr01 c2 cfv ad2antlr
      cdiv cceil zaddcld 3jaod rexlimdva ) EUAIZDCIZUBZFJAUQZKZJVPLUCMZEUDMZKZN
      ZOZFVQLVPKZNZOZFWCLVPDUCMZEUDMZKZNZOZUEFJLNZBUFZUGZIZABVOVPBIZUBZWBWNWEWJ
      WPWNWBWAWMIWPWAWLPWAPIWPVQVTQRWPVQVTWLWPJVPWKBJWKIWPUHRZVOWOUIZSZWPJVSWKB
      WQWPVSJEUJMZBWPVRTIVMVSWTIWPVPWOVPTIZVOXAVPWTBVPJEUKGULUMZUNVMVNWOUOZVREU
      PURGUSSUTVAFWAWMVBVCWPWNWEWDWMIWPWDWLPWDPIWPVQWCQRWPVQWCWLWSWPLVPWKBLWKIW
      PVDRZWRSZUTVAFWDWMVBVCWPWNWJWIWMIWPWIWLPWIPIWPWCWHQRWPWCWHWLXEWPLWGWKBXDW
      PWGWTBWPWFTIVMWGWTIWPVPDXBVNDTIZVMWOXFDLEVEVHMVIVFZUJMCDLXGUKHULVGVJXCWFE
      UPURGUSSUTVAFWIWMVBVCVKVL $.

    gpgvtxel.g $e |- G = ( N gPetersenGr K ) $.
    ${
      $d I y $.  $d X x y $.
      gpgvtxel.v $e |- V = ( Vtx ` G ) $.
      $( A vertex in a generalized Petersen graph ` G ` .  (Contributed by AV,
         29-Aug-2025.) $)
      gpgvtxel $p |- ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
             -> ( X e. V <-> E. x e. { 0 , 1 } E. y e. I X = <. x , y >. ) ) $=
        ( c3 cfv wcel wa cv wrex cvtx cuz cc0 c1 cpr cxp cop wceq cgpg co eqtri
        fveq2i eleq2i cn wb eluz3nn gpgvtx eleq2d sylan bitrid elxp2 bitrdi ) G
        NUAOPZFEPZQZIHPZIUBUCUDZDUEZPZIARBRUFUGBDSAVFSVEIGFUHUIZTOZPZVDVHHVJIHC
        TOVJMCVITLUKUJULVBGUMPZVCVKVHUNGUOVLVCQVJVGIDEFGKJUPUQURUSABIVFDUTVA $.

      $( The second component of a vertex in a generalized Petersen graph
         ` G ` .  (Contributed by AV, 30-Aug-2025.) $)
      gpgvtxel2 $p |- ( ( ( N e. ( ZZ>= ` 3 ) /\ K e. J ) /\ X e. V )
                        -> ( 2nd ` X ) e. I ) $=
        ( vx vy c3 cfv wcel wa cv wrex vex cuz c2nd cop wceq cc0 gpgvtxel simpr
        c1 cpr op2ndd eleq1d syl5ibrcom rexlimivv biimtrdi imp ) ENUAOPDCPQZGFP
        ZGUBOZBPZUPUQGLRZMRZUCUDZMBSLUEUHUIZSUSLMABCDEFGHIJKUFVBUSLMVCBUTVCPZVA
        BPZQUSVBVEVDVEUGVBURVABUTVAGLTMTUJUKULUMUNUO $.
    $}

    $d I e $.  $d K e $.  $d N e $.  $d X e x $.
    $( An index of edges of the generalized Petersen graph GPG(N,K).
       (Contributed by AV, 2-Nov-2025.) $)
    gpgiedgdmel $p |- ( ( N e. NN /\ K e. J )
                        -> ( X e. dom ( iEdg ` G ) <-> E. x e. I
                 ( X = { <. 0 , x >. , <. 0 , ( ( x + 1 ) mod N ) >. }
                \/ X = { <. 0 , x >. , <. 1 , x >. }
                \/ X = { <. 1 , x >. , <. 1 , ( ( x + K ) mod N ) >. } ) ) ) $=
      ( ve wcel ciedg cc0 cop c1 co cpr wceq eqeq1 cn wa cfv cdm cid cv cmo w3o
      caddc wrex cxp cpw crab cres cgpg fveq2i gpgiedg eqtrid eleq2d dmresi a1i
      dmeqd 3orbi123d rexbidv elrab gpgiedgdmellem pm4.71rd bitr4id 3bitrd ) FU
      ALEDLUBZGBMUCZUDZLGUEKUFZNAUFZOZNVNPUIQFUGQORZSZVMVOPVNOZRZSZVMVRPVNEUIQF
      UGQORZSZUHZACUJZKNPRCUKULZUMZUNZUDZLGWFLZGVPSZGVSSZGWASZUHZACUJZVJVLWHGVJ
      VKWGVJVKFEUOQZMUCWGBWOMJUPAKCDEFIHUQURVBUSVJWHWFGWHWFSVJWFUTVAUSVJWIGWELZ
      WNUBWNWDWNKGWEVMGSZWCWMACWQVQWJVTWKWBWLVMGVPTVMGVSTVMGWATVCVDVEVJWNWPACDE
      FGHIVFVGVHVI $.

    $d Y e $.
    gpgedgel.e $e |- E = ( Edg ` G ) $.
    $( An edge in a generalized Petersen graph ` G ` .  (Contributed by AV,
       29-Aug-2025.)  (Proof shortened by AV, 8-Nov-2025.) $)
    gpgedgel $p |- ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
                     -> ( Y e. E <-> E. x e. I
                 ( Y = { <. 0 , x >. , <. 0 , ( ( x + 1 ) mod N ) >. }
                \/ Y = { <. 0 , x >. , <. 1 , x >. }
                \/ Y = { <. 1 , x >. , <. 1 , ( ( x + K ) mod N ) >. } ) ) ) $=
      ( ve cfv wcel cop c1 co cpr wceq c3 cuz wa cc0 caddc cmo w3o wrex cxp cpw
      cv crab cgpg cedg fveq2i eqtri eleq2i cn gpgedg sylan eleq2d bitrid eqeq1
      eluz3nn 3orbi123d rexbidv elrab wi anim1i gpgiedgdmellem pm4.71rd bitr4id
      syl bitrd ) GUAUBNOZFEOZUCZHBOZHMUKZUDAUKZPZUDVTQUERGUFRPSZTZVSWAQVTPZSZT
      ZVSWDQVTFUERGUFRPSZTZUGZADUHZMUDQSDUIUJZULZOZHWBTZHWETZHWGTZUGZADUHZVRHGF
      UMRZUNNZOVQWMBWTHBCUNNWTLCWSUNKUOUPUQVQWTWLHVOGUROZVPWTWLTGVDZAMDEFGJIUSU
      TVAVBVQWMHWKOZWRUCWRWJWRMHWKVSHTZWIWQADXDWCWNWFWOWHWPVSHWBVCVSHWEVCVSHWGV
      CVEVFVGVQWRXCVQXAVPUCWRXCVHVOXAVPXBVIADEFGHIJVJVMVKVLVN $.
  $}

  ${
    $d I x $.  $d N x $.  $d X x $.
    gpgprismgriedgdmel.i $e |- I = ( 0 ..^ N ) $.
    gpgprismgriedgdmel.g $e |- G = ( N gPetersenGr 1 ) $.
    $( An index of edges of the generalized Petersen graph GPG(N,1).
       (Contributed by AV, 2-Nov-2025.) $)
    gpgprismgriedgdmel $p |- ( N e. ( ZZ>= ` 3 )
                        -> ( X e. dom ( iEdg ` G ) <-> E. x e. I
                 ( X = { <. 0 , x >. , <. 0 , ( ( x + 1 ) mod N ) >. }
                \/ X = { <. 0 , x >. , <. 1 , x >. }
                \/ X = { <. 1 , x >. , <. 1 , ( ( x + 1 ) mod N ) >. } ) ) ) $=
      ( c3 cuz cfv wcel cn c1 c2 cdiv co cc0 cop cpr wceq cceil ciedg cdm caddc
      cfzo cv cmo w3o wrex wb eluz3nn 1elfzo1ceilhalf1 eqid gpgiedgdmel syl2anc
      ) DHIJKDLKMMDNOPUAJUEPZKEBUBJUCKEQAUFZRZQUQMUDPDUGPZRSTEURMUQRZSTEUTMUSRS
      TUHACUIUJDUKDULABCUPMDEFUPUMGUNUO $.
  $}

  ${
    $d N x $.
    $( A subset of the index of edges of the generalized Petersen graph
       GPG(N,1).  (Contributed by AV, 2-Nov-2025.) $)
    gpgprismgriedgdmss $p |- ( N e. ( ZZ>= ` 3 )
       -> ( { { <. 0 , 0 >. , <. 0 , 1 >. } , { <. 0 , 0 >. , <. 1 , 0 >. } }
         u. { { <. 1 , 1 >. , <. 0 , 1 >. } , { <. 1 , 1 >. , <. 1 , 0 >. } } )
                               C_ dom ( iEdg ` ( N gPetersenGr 1 ) ) ) $=
      ( vx wcel cc0 cop c1 cpr co wceq w3o wrex sylibr wb opeq2d preq12d eqeq2d
      opeq2 adantl rspcedvd 3r19.43 c3 cuz cfv cgpg ciedg cdm cv caddc cmo cfzo
      cn eluz3nn lbfzo0 oveq1 0p1e1 eqtrdi oveq1d c2 cr clt wa uzuzle23 eluz2b1
      wbr cz zre anim1i sylbi 1mod 3syl eqcomd preq2d 3mix1d gpgprismgriedgdmel
      eqid mpbird a1i 3mix2d prssd cn0 1nn0 eluz2gt1 syl elfzo0 syl3anbrc prcom
      eqtrid 3mix3d unssd ) AUAUBUCCZDDEZDFEZGZWKFDEZGZGFFEZWLGZWPWNGZGAFUDHZUE
      UCUFZWJWMWOWTWJWMWTCWMDBUGZEZDXAFUHHZAUIHZEZGZIZWMXBFXAEZGZIZWMXHFXDEZGZI
      ZJBDAUJHZKZWJXGBXNKZXJBXNKZXMBXNKZJXOWJXPXQXRWJXGWMWKDFAUIHZEZGZIZBDXNWJA
      UKCZDXNCAULZAUMLZXADIZXGYBMWJYFXFYAWMYFXBWKXEXTXADDQZYFXDXSDYFXCFAUIYFXCD
      FUHHFXADFUHUNUOUPUQZNOPRWJWLXTWKWJFXSDWJXSFWJAURUBUCCZAUSCZFAUTVDZVAZXSFI
      AVBZYIAVECZYKVAYLAVCYNYJYKAVFVGVHAVIVJVKZNVLSVMXGXJXMBXNTLBWSXNAWMXNVOZWS
      VOZVNVPWJWOWTCWOXFIZWOXIIZWOXLIZJBXNKZWJYRBXNKZYSBXNKZYTBXNKZJUUAWJUUCUUB
      UUDWJYSWOWOIZBDXNYEYFYSUUEMWJYFXIWOWOYFXBWKXHWNYGXADFQZOPRUUEWJWOVOVQSVRY
      RYSYTBXNTLBWSXNAWOYPYQVNVPVSWJWQWRWTWJWQWTCWQXFIZWQXIIZWQXLIZJBXNKZWJUUGB
      XNKZUUHBXNKZUUIBXNKZJUUJWJUULUUKUUMWJUUHWQWLWPGZIZBFXNWJFVTCZYCYKFXNCUUPW
      JWAVQYDWJYIYKYMAWBWCFAWDWEXAFIZUUHUUOMWJUUQXIUUNWQUUQXBWLXHWPXAFDQXAFFQOP
      RUUOWJWPWLWFVQSVRUUGUUHUUIBXNTLBWSXNAWQYPYQVNVPWJWRWTCWRXFIZWRXIIZWRXLIZJ
      BXNKZWJUURBXNKZUUSBXNKZUUTBXNKZJUVAWJUVDUVBUVCWJUUTWRWNFXSEZGZIZBDXNYEYFU
      UTUVGMWJYFXLUVFWRYFXHWNXKUVEUUFYFXDXSFYHNOPRWJWRWNWPGUVFWPWNWFWJWPUVEWNWJ
      FXSFYONVLWGSWHUURUUSUUTBXNTLBWSXNAWRYPYQVNVPVSWI $.
  $}

  ${
    $d J x y $.  $d K x y $.  $d N x y $.  $d V x y $.  $d X x y $.
    gpgvtx0.j $e |- J = ( 1 ..^ ( |^ ` ( N / 2 ) ) ) $.
    gpgvtx0.g $e |- G = ( N gPetersenGr K ) $.
    gpgvtx0.v $e |- V = ( Vtx ` G ) $.
    $( The outside vertices in a generalized Petersen graph ` G ` .
       (Contributed by AV, 30-Aug-2025.) $)
    gpgvtx0 $p |- ( ( ( N e. ( ZZ>= ` 3 ) /\ K e. J ) /\ X e. V )
                    -> ( <. 0 , ( ( ( 2nd ` X ) + 1 ) mod N ) >. e. V
                      /\ <. 0 , ( 2nd ` X ) >. e. V
                      /\ <. 0 , ( ( ( 2nd ` X ) - 1 ) mod N ) >. e. V ) ) $=
      ( vx vy cfv wcel wa cc0 c1 co cmo cop wceq c3 cuz c2nd caddc cmin cv cfzo
      w3a wrex cpr eqid gpgvtxel cgpg cvtx fveq2i eqtri cn eluz3nn gpgvtx sylan
      cxp adantr eqtrid 0elpr01 elfzoelz peano2zd zmodfzo syl2anr opelxpd simpr
      a1i cz 1zzd zsubcld 3jca ad2ant2rl wb eleq2 3anbi123d adantl mpbird mpdan
      vex op2ndd oveq1 oveq1d opeq2d eleq1d opeq2 syl syl5ibrcom rexlimdvva imp
      sylbid ) DUAUBLMZCBMZNZFEMZOFUCLZPUDQZDRQZSZEMZOWSSZEMZOWSPUEQZDRQZSZEMZU
      HZWQWRFJUFZKUFZSTZKODUGQZUIJOPUJZUIXJJKAXNBCDEFXNUKZGHIULWQXMXJJKXOXNWQXK
      XOMZXLXNMZNZNZXJXMOXLPUDQZDRQZSZEMZOXLSZEMZOXLPUEQZDRQZSZEMZUHZXTEXOXNVAZ
      TZYKXTEDCUMQZUNLZYLEAUNLYOIAYNUNHUOUPWQYOYLTZXSWODUQMZWPYPDURZXNBCDGXPUSU
      TVBVCXTYMNYKYCYLMZYEYLMZYIYLMZUHZXTUUBYMWOXRUUBWPXQWOXRNZYSYTUUAUUCOYBXOX
      NOXOMUUCVDVKZXRYAVLMYQYBXNMWOXRXLXLODVEZVFYRYADVGVHVIUUCOXLXOXNUUDWOXRVJV
      IUUCOYHXOXNUUDXRYGVLMYQYHXNMWOXRXLPUUEXRVMVNYRYGDVGVHVIVOVPVBYMYKUUBVQXTY
      MYDYSYFYTYJUUAEYLYCVREYLYEVREYLYIVRVSVTWAWBXMWSXLTZXJYKVQXKXLFJWCKWCWDUUF
      XCYDXEYFXIYJUUFXBYCEUUFXAYBOUUFWTYADRWSXLPUDWEWFWGWHUUFXDYEEWSXLOWIWHUUFX
      HYIEUUFXGYHOUUFXFYGDRWSXLPUEWEWFWGWHVSWJWKWLWNWM $.

    $( The inside vertices in a generalized Petersen graph ` G ` .
       (Contributed by AV, 28-Aug-2025.) $)
    gpgvtx1 $p |- ( ( ( N e. ( ZZ>= ` 3 ) /\ K e. J ) /\ X e. V )
                    -> ( <. 1 , ( ( ( 2nd ` X ) + K ) mod N ) >. e. V
                      /\ <. 1 , ( 2nd ` X ) >. e. V
                      /\ <. 1 , ( ( ( 2nd ` X ) - K ) mod N ) >. e. V ) ) $=
      ( vx vy cfv wcel wa c1 co cmo cop wceq adantr cuz c2nd caddc cmin w3a cc0
      c3 cv cfzo wrex cpr eqid gpgvtxel cxp cgpg fveq2i eqtri cn eluz3nn gpgvtx
      cvtx sylan eqtrid 1elpr01 cz elfzoelz adantl c2 cdiv cceil eleq2s zaddcld
      a1i zmodfzo syl2anc opelxpd simprr zsubcld 3jca wb eleq2 3anbi123d mpbird
      mpdan vex op2ndd oveq1 oveq1d opeq2d eleq1d syl syl5ibrcom rexlimdvva imp
      opeq2 sylbid ) DUGUALMZCBMZNZFEMZOFUBLZCUCPZDQPZRZEMZOXARZEMZOXACUDPZDQPZ
      RZEMZUEZWSWTFJUHZKUHZRSZKUFDUIPZUJJUFOUKZUJXLJKAXPBCDEFXPULZGHIUMWSXOXLJK
      XQXPWSXMXQMZXNXPMZNZNZXLXOOXNCUCPZDQPZRZEMZOXNRZEMZOXNCUDPZDQPZRZEMZUEZYB
      EXQXPUNZSZYMYBEDCUOPZVALZYNEAVALYQIAYPVAHUPUQWSYQYNSZYAWQDURMZWRYRDUSZXPB
      CDGXRUTVBTVCYBYONYMYEYNMZYGYNMZYKYNMZUEZYBUUDYOYBUUAUUBUUCYBOYDXQXPOXQMYB
      VDVMZYBYCVEMYSYDXPMYBXNCYAXNVEMZWSXTUUFXSXNUFDVFVGVGZWSCVEMZYAWRUUHWQUUHC
      ODVHVIPVJLZUIPBCOUUIVFGVKVGTZVLWSYSYAWQYSWRYTTTZYCDVNVOVPYBOXNXQXPUUEWSXS
      XTVQVPYBOYJXQXPUUEYBYIVEMYSYJXPMYBXNCUUGUUJVRUUKYIDVNVOVPVSTYOYMUUDVTYBYO
      YFUUAYHUUBYLUUCEYNYEWAEYNYGWAEYNYKWAWBVGWCWDXOXAXNSZXLYMVTXMXNFJWEKWEWFUU
      LXEYFXGYHXKYLUULXDYEEUULXCYDOUULXBYCDQXAXNCUCWGWHWIWJUULXFYGEXAXNOWOWJUUL
      XJYKEUULXIYJOUULXHYIDQXAXNCUDWGWHWIWJWBWKWLWMWPWN $.
  $}

  ${
    opgpgvtx.i $e |- I = ( 0 ..^ N ) $.
    opgpgvtx.j $e |- J = ( 1 ..^ ( |^ ` ( N / 2 ) ) ) $.
    opgpgvtx.g $e |- G = ( N gPetersenGr K ) $.
    opgpgvtx.v $e |- V = ( Vtx ` G ) $.
    $( A vertex in a generalized Petersen graph ` G ` as ordered pair.
       (Contributed by AV, 1-Oct-2025.) $)
    opgpgvtx $p |- ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
              -> ( <. X , Y >. e. V <-> ( ( X = 0 \/ X = 1 ) /\ Y e. I ) ) ) $=
      ( cfv wcel wa cc0 c1 wceq cvtx wb c3 cuz cop cpr cxp wo cgpg fveq2i eqtri
      co cn eluz3nn gpgvtx sylan eqtrid eleq2d opelxp a1i c0ex 1ex elpr2 anbi1d
      3bitrd ) EUAUBMNZDCNZOZGHUCZFNVGPQUDZBUEZNZGVHNZHBNZOZGPRGQRUFZVLOVFFVIVG
      VFFEDUGUJZSMZVIFASMVPLAVOSKUHUIVDEUKNVEVPVIREULBCDEJIUMUNUOUPVJVMTVFGHVHB
      UQURVFVKVNVLVKVNTVFGPQUSUTVAURVBVC $.
  $}

  ${
    $d I e p $.  $d I x $.  $d J e x $.  $d K e x $.  $d N e x $.
    gpgusgralem.j $e |- J = ( 1 ..^ ( |^ ` ( N / 2 ) ) ) $.
    gpgusgralem.i $e |- I = ( 0 ..^ N ) $.
    $( Lemma for ~ gpgusgra .  (Contributed by AV, 27-Aug-2025.)  (Proof
       shortened by AV, 6-Sep-2025.) $)
    gpgusgralem $p |- ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
                         -> { e e. ~P ( { 0 , 1 } X. I ) | E. x e. I
                      ( e = { <. 0 , x >. , <. 0 , ( ( x + 1 ) mod N ) >. }
                     \/ e = { <. 0 , x >. , <. 1 , x >. }
                     \/ e = { <. 1 , x >. , <. 1 , ( ( x + K ) mod N ) >. } ) }
                        C_ { p e. ~P ( { 0 , 1 } X. I ) | ( # ` p ) = 2 } ) $=
      ( c3 cfv wcel wa cc0 c1 wceq chash c2 wne cvv cuz cv cop caddc co cmo cpr
      w3o wrex cxp cpw crab wo cfzo uzuzle23 adantr eleq2i biimpi syl2an necomd
      p1modne olcd cz wb 0z vex opthneg mp2an sylibr opex hashprg sylib fveqeq2
      syl5ibrcom 0ne1 a1i adantl mpbird ex cn cn0 clt wbr eluz3nn ad3antrrr w3a
      orcd elfzo0 bitri 3simpb sylbi cdiv cceil wi elfzo1 simpl1 nnre 3anim123i
      eluzelre cle rehalfcld eluzelz eluz2 simp2 0re 3re zre ltleii simpr letrd
      cr 3pos 3adant1 jca elnn0z 2nn nn0ledivnn syl2an2 3jca 3adant2 ceille syl
      lelttrdi 3exp com34 3imp1 impcom addmodne syl3anc 3jaod rexlimdva cbvrabv
      1z ss2rabdv sseqtrrdi ) FJUAKLZEDLZMZBUBZNAUBZUCZNYTOUDUEFUFUEZUCZUGZPZYS
      UUAOYTUCZUGZPZYSUUFOYTEUDUEFUFUEZUCZUGZPZUHZACUIZBNOUGCUJUKZULYSQKRPZBUUO
      ULGUBZQKRPZGUUOULYRUUNUUPBUUOYRYSUUOLZMZUUMUUPACUUTYTCLZMZUUEUUPUUHUULUVB
      UUPUUEUUDQKRPZUVBUUAUUCSZUVCUVBNNSZYTUUBSZUMZUVDUVBUVFUVEUVBUUBYTUUTFRUAK
      LZYTNFUNUEZLZUUBYTSUVAYRUVHUUSYPUVHYQFUOUPUPUVAUVJCUVIYTIUQZURYTFVAUSUTVB
      NVCLZYTTLZUVDUVGVDVEAVFZNYTNUUBVCTVGVHVIUUATLZUUCTLUVDUVCVDNYTVJZNUUBVJUU
      AUUCTTVKVHVLYSUUDRQVMVNUVBUUHUUPUVBUUHMZUUPUUGQKRPZUVQUUAUUFSZUVRUVQNOSZY
      TYTSZUMZUVSUVQUVTUWAUVTUVQVOVPWGUVLUVMUVSUWBVDVEUVNNYTOYTVCTVGVHVIUVOUUFT
      LZUVSUVRVDUVPOYTVJZUUAUUFTTVKVHVLUUHUUPUVRVDUVBYSUUGRQVMVQVRVSUVBUUPUULUU
      KQKRPZUVBUUFUUJSZUWEUVBOOSZYTUUISZUMZUWFUVBUWHUWGUVBUUIYTUVBFVTLZYTWALZYT
      FWBWCZMZEVTLZEFWBWCZMZUUIYTSYPUWJYQUUSUVAFWDWEUVAUWMUUTUVAUWKUWJUWLWFZUWM
      UVAUVJUWQUVKYTFWHWIUWKUWJUWLWJWKVQUUTUWPUVAYRUWPUUSYQYPUWPYQUWNFRWLUEZWMK
      ZVTLZEUWSWBWCZWFZYPUWPWNYQEOUWSUNUEZLUXBDUXCEHUQUWSEWOWIUXBYPUWPUXBYPMUWN
      UWOUWNUWTUXAYPWPUWNUWTUXAYPUWOUWNUWTYPUXAUWOUWNUWTYPUXAUWOWNUWNUWTYPWFZEU
      WSFUWNEXKLUWTUWSXKLYPFXKLZEWQUWSWQJFWSZWRUXDUWRXKLZFVCLZUWRFWTWCZWFZUWSFW
      TWCUWNYPUXJUWTUWNYPMZUXGUXHUXIYPUXGUWNYPFUXFXAVQYPUXHUWNJFXBVQYPFWALZUWNR
      VTLZUXIYPJVCLZUXHJFWTWCZWFZUXLJFXCUXPUXHNFWTWCZMUXLUXPUXHUXQUXNUXHUXOXDUX
      HUXOUXQUXNUXHUXOMZNJFNXKLUXRXEVPJXKLUXRXFVPUXHUXEUXOFXGUPNJWTWCUXRNJXEXFX
      LXHVPUXHUXOXIXJXMXNFXOVIWKUXMUXKXPVPFRXQXRXSXTUWRFYAYBYCYDYEYFXNVSWKYGUPU
      PYTEFYHYIUTVBOVCLUVMUWFUWIVDYMUVNOYTOUUIVCTVGVHVIUWCUUJTLUWFUWEVDUWDOUUIV
      JUUFUUJTTVKVHVLYSUUKRQVMVNYJYKYNUURUUPGBUUOUUQYSRQVMYLYO $.
  $}

  ${
    $d K e p $.  $d K e x $.  $d N p $.  $d N e x $.
    $( The generalized Petersen graph GPG(N,K) is a simple graph.  (Contributed
       by AV, 27-Aug-2025.) $)
    gpgusgra $p |- ( ( N e. ( ZZ>= ` 3 ) /\ K e. ( 1 ..^ ( |^ ` ( N / 2 ) ) ) )
                     -> ( N gPetersenGr K ) e. USGraph ) $=
      ( vp ve vx cfv wcel c1 c2 co cfzo cgpg cv wceq crab wf1 cc0 cop cpr eqid
      c3 cuz cdiv cceil wa cusgr ciedg cdm chash cvtx cpw caddc cmo w3o cxp cid
      wrex cres wss wf1o f1oi f1of1 mp1i gpgusgralem syl2anc cn eluz3nn gpgiedg
      f1ss sylan dmeqd dmresi eqtrdi gpgvtx rabeqdv f1eq123d mpbird cvv wb ovex
      pweqd isusgrs ) BUAUBFGZAHBIUCJUDFKJZGZUEZBALJZUFGZWGUGFZUHZCMUIFINZCWGUJ
      FZUKZOZWIPZWFWODMZQEMZRZQWQHULJBUMJRSNWPWRHWQRZSNWPWSHWQAULJBUMJRSNUNEQBK
      JZUQDQHSWTUOZUKZOZWKCXBOZUPXCURZPZWFXCXCXEPZXCXDUSXFXCXCXEUTXGWFXCVAXCXCX
      EVBVCEDWTWDABCWDTZWTTZVDXCXCXDXEVIVEWFWJXCWNXDWIXEWCBVFGZWEWIXENBVGZEDWTW
      DABXHXIVHVJZWFWJXEUHXCWFWIXEXLVKXCVLVMWFWKCWMXBWFWLXAWCXJWEWLXANXKWTWDABX
      HXIVNVJWAVOVPVQWGVRGWHWOVSWFBALVTCVRWIWGWLWLTWITWBVCVQ $.
  $}

  $( The generalized Petersen graphs G(N,1), which are the N-prisms, are simple
     graphs.  (Contributed by AV, 31-Oct-2025.) $)
  gpgprismgrusgra $p |- ( N e. ( ZZ>= ` 3 )
                          -> ( N gPetersenGr 1 ) e. USGraph ) $=
    ( c3 cuz cfv wcel c1 c2 cdiv co cceil cfzo cgpg cusgr cz clt wbr cr a1i syl
    ceilcld 1zzd cc0 wne w3a eluzelre 2re 2ne0 3jca redivcl 2ltceilhalf ltletrd
    1red zred 1lt2 fzolb syl3anbrc gpgusgra mpdan ) ABCDEZFFAGHIZJDZKIEZAFLIMEU
    SFNEVANEZFVAOPVBUSUAUSUTUSAQEZGQEZGUBUCZUDZUTQEUSVDVEVFBAUEVEUSUFRZVFUSUGRU
    HZAGUIZSTUSFGVAUSULVHUSVAUSVGVCVIVGUTVJTSUMFGOPUSUNRAUJUKFVAUOUPFAUQUR $.

  ${
    gpgorder.j $e |- J = ( 1 ..^ ( |^ ` ( N / 2 ) ) ) $.
    $( The order of the generalized Petersen graph GPG(N,K).  (Contributed by
       AV, 29-Sep-2025.) $)
    gpgorder $p |- ( ( N e. NN /\ K e. J )
                     -> ( # ` ( Vtx ` ( N gPetersenGr K ) ) ) = ( 2 x. N ) ) $=
      ( cn wcel wa cgpg co cvtx cfv chash cc0 c1 cpr cfzo cmul c2 cfn wceq eqid
      cxp gpgvtx fveq2d prfi fzofi pm3.2i mp1i prhash2ex a1i cn0 nnnn0 hashfzo0
      hashxp syl adantr oveq12d 3eqtrd ) CEFZBAFZGZCBHIJKZLKMNOZMCPIZUBZLKZVCLK
      ZVDLKZQIZRCQIVAVBVELVDABCDVDUAUCUDVCSFZVDSFZGVFVITVAVJVKMNUEMCUFUGVCVDUNU
      HVAVGRVHCQVGRTVAUIUJUSVHCTZUTUSCUKFVLCULCUMUOUPUQUR $.
  $}

  $( The order of a generalized Petersen graph G(5,K), which is either the
     Petersen graph G(5,2) or the 5-prism G(5,1), is 10.  (Contributed by AV,
     26-Aug-2025.) $)
  gpg5order $p |- ( K e. ( 1 ... 2 )
                      -> ( # ` ( Vtx ` ( 5 gPetersenGr K ) ) ) = ; 1 0 ) $=
    ( c1 c2 cfz co wcel c5 cgpg cvtx cfv chash cmul cc0 cn cdiv cceil cfzo wceq
    cdc 5nn caddc cz 2z fzval3 ax-mp c3 2p1e3 eqtr4i oveq2i eqtri eleq2i biimpi
    ceil5half3 eqid gpgorder sylancr 5cn 2cn 5t2e10 mulcomli eqtrdi ) ABCDEZFZG
    AHEIJKJZCGLEZBMSZVCGNFABGCOEPJZQEZFZVDVERTVCVIVBVHAVBBCBUAEZQEZVHCUBFVBVKRU
    CBCUDUEVJVGBQVJUFVGUGUMUHUIUJUKULVHAGVHUNUOUPGCVFUQURUSUTVA $.

  ${
    $d E x y $.  $d J x y z $.  $d K x y z $.  $d N x y z $.  $d X x y $.
    gpgedgvtx0.j $e |- J = ( 1 ..^ ( |^ ` ( N / 2 ) ) ) $.
    gpgedgvtx0.g $e |- G = ( N gPetersenGr K ) $.
    gpgedgvtx0.v $e |- V = ( Vtx ` G ) $.
    gpgedgvtx0.e $e |- E = ( Edg ` G ) $.
    $( The edges starting at an outside vertex in a generalized Petersen graph
       ` G ` .  (Contributed by AV, 29-Aug-2025.) $)
    gpgedgvtx0 $p |- ( ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
                      /\ ( X e. V /\ ( 1st ` X ) = 0 ) )
               -> ( { X , <. 0 , ( ( ( 2nd ` X ) + 1 ) mod N ) >. } e. E
                 /\ { X , <. 1 , ( 2nd ` X ) >. } e. E
                 /\ { X , <. 0 , ( ( ( 2nd ` X ) - 1 ) mod N ) >. } e. E ) ) $=
      ( wcel cc0 wceq c1 caddc co cmo cop cpr vx vy vz c3 cuz wa c1st c2nd cmin
      cfv w3a cv cfzo wrex wi eqid gpgvtxel fveq2 adantl op1st eqtrdi eqeq1d wb
      vex opeq1 eqeq2d w3o simpr weq opeq2 oveq1 oveq1d opeq2d 3orbi123d 3mix1i
      preq12d a1i rspcedvd 3mix2i wo elfzo0l eluz3nn ad2antrr fzo0end eqeqan12d
      cn syl adantll nncn npcan1 3syl crp nnrp modid0 eqtr2d cneg df-neg eqcomi
      cc m1modnnsub1 eqtrd prcom 3mix1d expcom elfzofz fz1fzo0m1 cz elfzoelz cr
      cfz zcn cle wbr clt elfzo1 nnre anim12i 3adant3 nnnn0 nn0ge0d 3adant2 jca
      anim1i sylbi modid 1red resubcld nnm1ge0 3ad2ant1 ltm1d simp3 lttrd jca32
      eqcomd 3ad2ant2 gpgedgel 3anbi123d adantr eleq1d sylbid mpbir3and adantrl
      jaoi impcom id c0ex op2ndd syl5ibrcom impancom ex rexlimdvva imp32 ) EUDU
      EUJLZDCLZUFZGFLZGUGUJZMNZGMGUHUJZOPQZERQZSZTZALZGOUUSSZTZALZGMUUSOUIQZERQ
      ZSZTZALZUKZUUOUUPGUAULZUBULZSZNZUBMEUMQZUNUAMOTZUNUURUVMUOZUAUBBUVRCDEFGU
      VRUPZHIJUQUUOUVQUVTUAUBUVSUVRUUOUVNUVSLZUVOUVRLZUFUFZUVQUVTUWDUVQUFZUURUV
      NMNZUVMUWEUUQUVNMUWEUUQUVPUGUJZUVNUVQUUQUWGNUWDGUVPUGURUSUVNUVOUAVDUBVDZU
      TVAVBUWDUWFUVQUVMUWDUWFUFUVQGMUVOSZNZUVMUWFUVQUWJVCUWDUWFUVPUWIGUVNMUVOVE
      VFUSUWDUWJUVMUOUWFUWDUVMUWJUWIMUVOOPQZERQZSZTZALZUWIOUVOSZTZALZUWIMUVOOUI
      QZERQZSZTZALZUKZUUOUWCUXDUWBUUOUWCUFZUXDUWNMUCULZSZMUXFOPQZERQZSZTZNZUWNU
      XGOUXFSZTZNZUWNUXMOUXFDPQZERQZSZTZNZVGZUCUVRUNZUWQUXKNZUWQUXNNZUWQUXSNZVG
      ZUCUVRUNZUXBUXKNZUXBUXNNZUXBUXSNZVGZUCUVRUNZUXEUYAUWNUWNNZUWNUWQNZUWNUWPO
      UVODPQZERQZSZTZNZVGZUCUVOUVRUUOUWCVHZUCUBVIZUYAUYTVCUXEVUBUXLUYMUXOUYNUXT
      UYSVUBUXKUWNUWNVUBUXGUWIUXJUWMUXFUVOMVJZVUBUXIUWLMVUBUXHUWKERUXFUVOOPVKVL
      VMVPZVFVUBUXNUWQUWNVUBUXGUWIUXMUWPVUCUXFUVOOVJZVPZVFVUBUXSUYRUWNVUBUXMUWP
      UXRUYQVUEVUBUXQUYPOVUBUXPUYOERUXFUVODPVKVLVMVPZVFVNUSUYTUXEUYMUYNUYSUWNUP
      VOVQVRUXEUYFUWQUWNNZUWQUWQNZUWQUYRNZVGZUCUVOUVRVUAVUBUYFVUKVCUXEVUBUYCVUH
      UYDVUIUYEVUJVUBUXKUWNUWQVUDVFVUBUXNUWQUWQVUFVFVUBUXSUYRUWQVUGVFVNUSVUKUXE
      VUIVUHVUJUWQUPVSVQVRUWCUUOUYLUWCUVOMNZUVOOEUMQLZVTUUOUYLUOZUVOEWAVULVUNVU
      MUUOVULUYLUUOVULUFZUYKMMSZMMOUIQZERQZSZTZMEOUIQZSZMVVAOPQZERQZSZTZNZVUTVV
      BOVVASZTZNZVUTVVHOVVADPQZERQZSZTZNZVGZUCVVAUVRVUOEWFLZVVAUVRLUUMVVQUUNVUL
      EWBZWCEWDWGVULUXFVVANZUYKVVPVCUUOVULVVSUFUYHVVGUYIVVJUYJVVOVULVVSUXBVUTUX
      KVVFVULUWIVUPUXAVUSUVOMMVJVULUWTVURMVULUWSVUQERUVOMOUIVKVLVMVPZVVSUXGVVBU
      XJVVEUXFVVAMVJZVVSUXIVVDMVVSUXHVVCERUXFVVAOPVKVLVMVPWEVULVVSUXBVUTUXNVVIV
      VTVVSUXGVVBUXMVVHVWAUXFVVAOVJZVPWEVULVVSUXBVUTUXSVVNVVTVVSUXMVVHUXRVVMVWB
      VVSUXQVVLOVVSUXPVVKERUXFVVADPVKVLVMVPWEVNWHVUOVVGVVJVVOVUOVUTVVEVVBTZVVFU
      UMVUTVWCNUUNVULUUMVUPVVEVUSVVBUUMMVVDMUUMVVDEERQZMUUMVVCEERUUMVVQEWSLVVCE
      NVVREWIEWJWKVLUUMVVQEWLLZVWDMNVVREWMZEWNWKWOVMUUMVURVVAMUUMVUROWPZERQZVVA
      UUMVUQVWGERVUQVWGNUUMVWGVUQOWQWRVQVLUUMVVQVWHVVANVVREWTWGXAVMVPWCVVEVVBXB
      VAXCVRXDUUOVUMUYLUUOVUMUFZUYKUXBMUWSSZMUWSOPQZERQZSZTZNZUXBVWJOUWSSZTZNZU
      XBVWPOUWSDPQZERQZSZTZNZVGZUCUWSUVRVUMUWSUVRLZUUOVUMUVOOEXJQLVXEUVOOEXEUVO
      EXFWGUSUXFUWSNZUYKVXDVCVWIVXFUYHVWOUYIVWRUYJVXCVXFUXKVWNUXBVXFUXGVWJUXJVW
      MUXFUWSMVJZVXFUXIVWLMVXFUXHVWKERUXFUWSOPVKVLVMVPVFVXFUXNVWQUXBVXFUXGVWJUX
      MVWPVXGUXFUWSOVJZVPVFVXFUXSVXBUXBVXFUXMVWPUXRVXAVXHVXFUXQVWTOVXFUXPVWSERU
      XFUWSDPVKVLVMVPVFVNUSVWIVWOVWRVXCVWIUXBVWMVWJTVWNVWIUWIVWMUXAVWJVWIUVOVWL
      MVWIVWLUVOVUMVWLUVONUUOVUMVWLUVOERQZUVOVUMVWKUVOERVUMUVOXGLUVOWSLVWKUVONU
      VOOEXHUVOXKUVOWJWKVLVUMUVOXILZVWEUFZMUVOXLXMZUVOEXNXMZUFZUFZVXIUVONVUMUVO
      WFLZVVQVXMUKZVXOEUVOXOZVXQVXKVXNVXPVVQVXKVXMVXPVXJVVQVWEUVOXPZVWFXQXRVXPV
      XMVXNVVQVXPVXLVXMVXPUVOUVOXSXTYCYAYBYDUVOEYEWGXAUSYNVMVWIUWTUWSMVWIUWSXIL
      ZVWEUFZMUWSXLXMZUWSEXNXMZUFUFZUWTUWSNVUMVYDUUOVUMVXQVYDVXRVXQVYAVYBVYCVXP
      VVQVYAVXMVXPVXTVVQVWEVXPUVOOVXSVXPYFYGZVWFXQXRVXPVVQVYBVXMUVOYHYIVXQUWSUV
      OEVXPVVQVXTVXMVYEYIVXPVVQVXJVXMVXSYIVVQVXPEXILVXMEXPYOVXPVVQUWSUVOXNXMVXM
      VXPUVOVXSYJYIVXPVVQVXMYKYLYMYDUSUWSEYEWGVMVPVWMVWJXBVAXCVRXDUUCWGUUDUUOUX
      DUYBUYGUYLUKVCUWCUUOUWOUYBUWRUYGUXCUYLUCABUVRCDEUWNUWAHIKYPUCABUVRCDEUWQU
      WAHIKYPUCABUVRCDEUXBUWAHIKYPYQYRUUAUUBUWJUVDUWOUVGUWRUVLUXCUWJUVCUWNAUWJG
      UWIUVBUWMUWJUUEZUWJUVAUWLMUWJUUTUWKERUWJUUSUVOOPMUVOGUUFUWHUUGZVLVLVMVPYS
      UWJUVFUWQAUWJGUWIUVEUWPVYFUWJUUSUVOOVYGVMVPYSUWJUVKUXBAUWJGUWIUVJUXAVYFUW
      JUVIUWTMUWJUVHUWSERUWJUUSUVOOUIVYGVLVLVMVPYSYQUUHYRYTUUIYTUUJUUKYTUUL $.

    $( The edges starting at an inside vertex in a generalized Petersen graph
       ` G ` .  (Contributed by AV, 2-Sep-2025.) $)
    gpgedgvtx1 $p |- ( ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
                      /\ ( X e. V /\ ( 1st ` X ) = 1 ) )
               -> ( { X , <. 1 , ( ( ( 2nd ` X ) + K ) mod N ) >. } e. E
                 /\ { X , <. 0 , ( 2nd ` X ) >. } e. E
                 /\ { X , <. 1 , ( ( ( 2nd ` X ) - K ) mod N ) >. } e. E ) ) $=
      ( wcel c1 wceq caddc co cmo cop cpr cc0 vx vy vz c3 cuz wa c1st c2nd cmin
      cfv w3a cv cfzo wrex wi eqid gpgvtxel fveq2 adantl op1st eqtrdi eqeq1d wb
      vex opeq1 eqeq2d opeq2 oveq1 oveq1d opeq2d preq12d 3orbi123d simpr 3mix3i
      w3o a1i rspcedvdw prcom 3mix2i wo cz cdiv cceil elfzoelz eleq2s fzospliti
      c2 anim1ci syl ex eluz3nn nnzd adantr zcnd elfzoel2 subsub3d 1zzd zsubcld
      cc cfz cle wbr elfzo0subge1 zred elfzo0suble gpgedgvtx1lem elfzo0le letrd
      ubmelfzo eqeltrrd eluzelcn addcld npcand cn0 cn clt elfzonn0 wss elfzouz2
      elfzd elfzolt2 imp syl3anc eqtr2d 3mix3d syl2anc cr crp anim12ci ad2antlr
      modid resubcld 3ad2ant1 3ad2ant2 sylbi gpgedgel 3anbi123d eleq1d sylbid
      zre fzoss2 sseld addmodid submodlt elfzo1 simp1bi nnnn0d elfzoextl sylan2
      syl6 ancoms fzosubel3 elfzoel1 nnrpd elfzole1 0red nnnn0 nn0ge0d ad3antlr
      mpdan syl12anc elfzo2 simp13 3adant3 subge0 mpbird nnrp 3ad2ant3 ltsubrpd
      eluz2 simp2r jca 3exp expd 3imp impcom jaod syld mpbir3and adantrl id 1ex
      lttrd op2ndd syl5ibrcom impancom rexlimdvva imp32 ) EUDUEUJLZDCLZUFZGFLZG
      UGUJZMNZGMGUHUJZDOPZEQPZRZSZALZGTUWORZSZALZGMUWODUIPZEQPZRZSZALZUKZUWKUWL
      GUAULZUBULZRZNZUBTEUMPZUNUATMSZUNUWNUXIUOZUAUBBUXNCDEFGUXNUPZHIJUQUWKUXMU
      XPUAUBUXOUXNUWKUXJUXOLZUXKUXNLZUFUFZUXMUXPUXTUXMUFZUWNUXJMNZUXIUYAUWMUXJM
      UYAUWMUXLUGUJZUXJUXMUWMUYCNUXTGUXLUGURUSUXJUXKUAVDUBVDZUTVAVBUXTUYBUXMUXI
      UXTUYBUFUXMGMUXKRZNZUXIUYBUXMUYFVCUXTUYBUXLUYEGUXJMUXKVEVFUSUXTUYFUXIUOUY
      BUXTUXIUYFUYEMUXKDOPZEQPZRZSZALZUYETUXKRZSZALZUYEMUXKDUIPZEQPZRZSZALZUKZU
      WKUXSUYTUXRUWKUXSUFZUYTUYJTUCULZRZTVUBMOPZEQPZRZSZNZUYJVUCMVUBRZSZNZUYJVU
      IMVUBDOPZEQPZRZSZNZVOZUCUXNUNZUYMVUGNZUYMVUJNZUYMVUONZVOZUCUXNUNZUYRVUGNZ
      UYRVUJNZUYRVUONZVOZUCUXNUNZVUAVUQUYJUYLTUXKMOPZEQPZRZSZNZUYJUYLUYESZNZUYJ
      UYJNZVOZUCUXKUXNVUBUXKNZVUHVVMVUKVVOVUPVVPVVRVUGVVLUYJVVRVUCUYLVUFVVKVUBU
      XKTVGZVVRVUEVVJTVVRVUDVVIEQVUBUXKMOVHVIVJVKZVFVVRVUJVVNUYJVVRVUCUYLVUIUYE
      VVSVUBUXKMVGZVKZVFVVRVUOUYJUYJVVRVUIUYEVUNUYIVWAVVRVUMUYHMVVRVULUYGEQVUBU
      XKDOVHVIVJVKZVFVLUWKUXSVMZVVQVUAVVPVVMVVOUYJUPVNVPVQVUAVVBUYMVVLNZUYMVVNN
      ZUYMUYJNZVOZUCUXKUXNVVRVUSVWEVUTVWFVVAVWGVVRVUGVVLUYMVVTVFVVRVUJVVNUYMVWB
      VFVVRVUOUYJUYMVWCVFVLVWDVWHVUAVWFVWEVWGUYEUYLVRVSVPVQUWKUXSVVHUWKUXSUXKTD
      UMPZLZUXKDEUMPLZVTZVVHUWKUXSVWLVUAUXSDWALZUFVWLUWKVWMUXSUWJVWMUWIVWMDMEWG
      WBPWCUJZUMPZCDMVWNWDHWEUSWHUXKTEDWFWIWJUWKVWJVVHVWKUWKVWJVVHUWKVWJUFZVVGU
      YRTEUXKOPZDUIPZRZTVWRMOPZEQPZRZSZNZUYRVWSMVWRRZSZNZUYRVXEMVWRDOPZEQPZRZSZ
      NZVOUCVWRUXNVUBVWRNZVVDVXDVVEVXGVVFVXLVXMVUGVXCUYRVXMVUCVWSVUFVXBVUBVWRTV
      GZVXMVUEVXATVXMVUDVWTEQVUBVWRMOVHVIVJVKVFVXMVUJVXFUYRVXMVUCVWSVUIVXEVXNVU
      BVWRMVGZVKVFVXMVUOVXKUYRVXMVUIVXEVUNVXJVXOVXMVUMVXIMVXMVULVXHEQVUBVWRDOVH
      VIVJVKVFVLVWPEDUXKUIPZUIPZVWRUXNVWPEDUXKUWKEWSLZVWJUWKEUWIEWALZUWJUWIEEWK
      ZWLWMZWNWMVWJDWSLUWKVWJDUXKTDWOZWNUSZVWJUXKWSLUWKVWJUXKUXKTDWDZWNUSZWPVWP
      VXPMEWTPLVXQUXNLVWPVXPMEVWPWQUWKVXSVWJVYAWMZVWPDUXKVWJVWMUWKVYBUSZVWJUXKW
      ALZUWKVYDUSWRZVWJMVXPXAXBUWKUXKDXCUSVWPVXPDEVWPVXPVYIXDVWPDVYGXDVWPEVYFXD
      VWJVXPDXAXBUWKUXKDXEUSUWKDEXAXBZVWJUWKDUXNLZVYJUXNCEDHUXQXFZDEXGWIWMXHXTV
      XPEXIWIXJVWPVXLVXDVXGVWPUYRVXJVXESVXKVWPUYEVXJUYQVXEVWPUXKVXIMVWPVXIVWQEQ
      PZUXKVWPVXHVWQEQVWPVWQDVWPEUXKUWKVXRVWJUWIVXRUWJUDEXKWMWMVYEXLVYCXMVIVWPU
      XKXNLZEXOLZUXKEXPXBZVYMUXKNVWJVYNUWKUXKDXQUSUWKVYOVWJUWIVYOUWJVXTWMZWMZUW
      KVWJVYPUWKVYKVWJVYPUOVYLVYKVWJUXSVYPVYKVWIUXNUXKVYKEDUEUJZLVWIUXNXRDTEXSD
      TEUUAWIUUBUXKTEYAUUJWIYBUXKEUUCYCYDVJVWPUYPVWRMVWPVYOVWJDEXPXBZUYPVWRNVYR
      UWKVWJVMUWKVYTVWJUWKVYKVYTVYLDTEYAWIWMUXKDEUUDYCVJVKVXJVXEVRVAYEVQWJUWKVW
      KVVHUWKVWKUFZVVGUYRTUYORZTUYOMOPZEQPZRZSZNZUYRWUBMUYORZSZNZUYRWUHMUYODOPZ
      EQPZRZSZNZVOUCUYOUXNVUBUYONZVVDWUGVVEWUJVVFWUOWUPVUGWUFUYRWUPVUCWUBVUFWUE
      VUBUYOTVGZWUPVUEWUDTWUPVUDWUCEQVUBUYOMOVHVIVJVKVFWUPVUJWUIUYRWUPVUCWUBVUI
      WUHWUQVUBUYOMVGZVKVFWUPVUOWUNUYRWUPVUIWUHVUNWUMWURWUPVUMWULMWUPVULWUKEQVU
      BUYODOVHVIVJVKVFVLWUAUXKDDEOPUMPLZVXSUYOUXNLVWKUWKWUSUWKVWKDXNLZWUSUWJWUT
      UWIWUTDVWOCDVWOLZDWVADXOLZVWNXOLZDVWNXPXBZVWNDUUEZUUFZUUGHWEUSDDEUXKUUHUU
      IUUKUWKVXSVWKUWKEVYQWLWMUXKDEUULYFWUAWUOWUGWUJWUAUYRWUMWUHSWUNWUAUYEWUMUY
      QWUHWUAUXKWULMWUAWULUXKEQPZUXKVWKWULWVGNUWKVWKWUKUXKEQVWKUXKDVWKUXKUXKDEW
      DZWNVWKDUXKDEUUMZWNXMVIUSWUAUXKYGLZEYHLZUFTUXKXAXBZVYPWVGUXKNUWKWVKVWKWVJ
      UWIWVKUWJUWIEVXTUUNWMZVWKUXKWVHXDZYIWUADUXKXAXBZWVLVWKWVOUWKUXKDEUUOUSWUA
      WVOUFZTDUXKWVPUUPVWKDYGLZUWKWVOVWKDWVIXDZYJVWKWVJUWKWVOWVNYJUWJTDXAXBZUWI
      VWKWVOWVSDVWOCWVAWVBWVSWVFWVBDDUUQUURWIHWEUUSWUAWVOVMXHUUTVWKVYPUWKUXKDEY
      AUSUXKEYKUVAYDVJWUAUYPUYOMWUAUYOYGLZWVKUFTUYOXAXBZUYOEXPXBZUFZUYPUYONUWKW
      VKVWKWVTWVMVWKUXKDWVNWVRYLYIVWKUWKWWCVWKUXKVYSLZVXSVYPUKUWKWWCUOZUXKDEUVB
      WWDVXSVYPWWEWWDVWMVYHWVOUKZVXSVYPWWEUOUODUXKUVJWWFVXSVYPWWEWWFVXSVYPUFZUW
      KWWCWWFWWGUWKUKZWWAWWBWWHWWAWVOVWMVYHWVOWWGUWKUVCWWHWVJWVQUFZWWAWVOVCWWFW
      WGWWIUWKVWMVYHWWIWVOVWMWVQVYHWVJDYTZUXKYTZYIUVDYMUXKDUVEWIUVFWWHUYOUXKEWW
      HUXKDWWFWWGWVJUWKVYHVWMWVJWVOWWKYNYMZWWFWWGWVQUWKVWMVYHWVQWVOWWJYMYMYLWWL
      WWGWWFEYGLZUWKVXSWWMVYPEYTWMYNWWHUXKDWWLUWKWWFDYHLZWWGUWJWWNUWIWWNDVWOCWV
      AWVBWVCWVDUKWWNWVEWVBWVCWWNWVDDUVGYMYOHWEUSUVHUVIWWFVXSVYPUWKUVKUWCUVLUVM
      UVNYOUVOYOUVPUYOEYKYFVJVKWUMWUHVRVAYEVQWJUVQUVRYBUWKUYTVURVVCVVHUKVCUXSUW
      KUYKVURUYNVVCUYSVVHUCABUXNCDEUYJUXQHIKYPUCABUXNCDEUYMUXQHIKYPUCABUXNCDEUY
      RUXQHIKYPYQWMUVSUVTUYFUWTUYKUXCUYNUXHUYSUYFUWSUYJAUYFGUYEUWRUYIUYFUWAZUYF
      UWQUYHMUYFUWPUYGEQUYFUWOUXKDOMUXKGUWBUYDUWDZVIVIVJVKYRUYFUXBUYMAUYFGUYEUX
      AUYLWWOUYFUWOUXKTWWPVJVKYRUYFUXGUYRAUYFGUYEUXFUYQWWOUYFUXEUYPMUYFUXDUYOEQ
      UYFUWOUXKDUIWWPVIVIVJVKYRYQUWEWMYSUWFYSWJUWGYSUWH $.

    $d V y $.  $d Y y $.
    $( The edges starting at an outside vertex ` X ` in a generalized Petersen
       graph ` G ` .  (Contributed by AV, 30-Aug-2025.) $)
    gpgvtxedg0 $p |- ( ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
                         /\ ( 1st ` X ) = 0 /\ { X , Y } e. E )
                       -> ( Y = <. 0 , ( ( ( 2nd ` X ) + 1 ) mod N ) >.
                         \/ Y = <. 1 , ( 2nd ` X ) >.
                         \/ Y = <. 0 , ( ( ( 2nd ` X ) - 1 ) mod N ) >. ) ) $=
      ( wcel wa cc0 wceq c1 co cmo wi vy c3 cuz cfv c1st cpr w3a c2nd caddc cop
      cmin w3o cusgr cdiv cceil cfzo cgpg gpgusgra eleq2i anbi2i eleq1i 3imtr4i
      c2 3ad2ant1 simp3 usgrpredgv syl2anc cv wrex wb eqid gpgedgel wo cvv opex
      adantr pm3.2i preq12bg sylancl simpr c0ex vex op2ndd eqcomd oveq1d opeq2d
      eqtrd 3mix1d a1i cr crp elfzoelz zred 1red readdcld cn0 cn clt wbr elfzo0
      nnrp 3ad2ant2 sylbi modsubmod syl3anc cc zcnd pncan1 zmodidfzoimp 3eqtrrd
      syl adantl ovex eqeq12d mpbird 3mix3d ex jaod sylbid 3mix2d op1std eqeq1d
      1ex wne ax-1ne0 eqneqall com12 mp1i impd 3jaod rexlimdva 3exp com34 3imp
      mpd ) EUBUCUDMZDCMZNZGUEUDZOPZGHUFZAMZUGZGFMHFMNZHOGUHUDZQUIRZESRZUJZPZHQ
      UUEUJZPZHOUUEQUKRZESRZUJZPZULZUUCBUMMZUUBUUDYRYTUUQUUBYPDQEVCUNRUOUDUPRZM
      ZNEDUQRZUMMYRUUQDEURYQUUSYPCUURDIUSUTBUUTUMJVAVBVDYRYTUUBVEABGHFLKVFVGYRY
      TUUBUUDUUPTYRYTUUDUUBUUPYRYTUUDUUBUUPTYRYTUUDUGZUUBUUAOUAVHZUJZOUVBQUIRZE
      SRZUJZUFPZUUAUVCQUVBUJZUFPZUUAUVHQUVBDUIRZESRZUJZUFPZULZUAOEUPRZVIZUUPYRY
      TUUBUVPVJUUDUAABUVOCDEUUAUVOVKIJLVLVDUVAUVNUUPUAUVOUVAUVBUVOMZNZUVGUUPUVI
      UVMUVRUVGGUVCPZHUVFPZNZGUVFPZHUVCPZNZVMZUUPUVRUUDUVCVNMZUVFVNMZNUVGUWEVJU
      VAUUDUVQYRYTUUDVEVPZUWFUWGOUVBVOZOUVEVOVQGHUVCUVFFFVNVNVRVSUVRUWAUUPUWDUW
      AUUPTUVRUWAUUIUUKUUOUWAHUVFUUHUVSUVTVTUWAUVEUUGOUVSUVEUUGPUVTUVSUVDUUFESU
      VSUVBUUEQUIUVSUUEUVBOUVBGWAUAWBZWCWDZWEWEVPWFWGWHWIUVRUWDUUPUVRUWDNZUUOUU
      IUUKUWLUUOUVCOUVEQUKRZESRZUJZPZUWLUVBUWNOUVRUVBUWNPZUWDUVQUWQUVAUVQUWNUVD
      QUKRZESRZUVBESRUVBUVQUVDWJMQWJMEWKMZUWNUWSPUVQUVBQUVQUVBUVBOEWLZWMUVQWNZW
      OUXBUVQUVBWPMZEWQMZUVBEWRWSZUGUWTUVBEWTUXDUXCUWTUXEEXAXBXCUVDQEXDXEUVQUWR
      UVBESUVQUVBXFMUWRUVBPUVQUVBUXAXGUVBXHXKWEUVBEXIXJXLVPWFUWDUUOUWPVJUVRUWDH
      UVCUUNUWOUWBUWCVTUWBUUNUWOPUWCUWBUUMUWNOUWBUULUWMESUWBUUEUVEQUKOUVEGWAUVD
      ESXMWCWEWEWFVPXNXLXOXPXQXRXSUVRUVIUVSHUVHPZNZGUVHPZUWCNZVMZUUPUVRUUDUWFUV
      HVNMZNUVIUXJVJUWHUWFUXKUWIQUVBVOZVQGHUVCUVHFFVNVNVRVSUVRUXGUUPUXIUVRUXGUU
      PUVRUXGNUUKUUIUUOUXGUUKUVRUXGHUVHUUJUVSUXFVTUXGUVBUUEQUVSUVBUUEPUXFUWKVPW
      FWGXLXTXQUVRUXHUWCUUPUVAUXHUWCUUPTZTZUVQYTYRUXNUUDUXHYTUXMUXHYTQOPZUXMUXH
      YSQOQUVBGYCUWJYAYBZQOYDZUXOUXMTUXHYEUXOUXQUXMUXMQOYFYGYHXSYGXBVPYIXRXSUVR
      UVMUXHHUVLPZNZGUVLPZUXFNZVMZUUPUVRUUDUXKUVLVNMZNUVMUYBVJUWHUXKUYCUXLQUVKV
      OVQGHUVHUVLFFVNVNVRVSUVAUYBUUPTZUVQYTYRUYDUUDYTUXSUUPUYAYTUXHUXRUUPUXHYTU
      XRUUPTZUXHYTUXOUYEUXPUXQUXOUYETUXHYEUXOUXQUYEUYEQOYFYGYHXSYGYIYTUXTUXFUUP
      UXTYTUXFUUPTZUXTYTUXOUYFUXTYSQOQUVKGYCUVJESXMYAYBUXQUXOUYFTUXTYEUXOUXQUYF
      UYFQOYFYGYHXSYGYIXRXBVPXSYJYKXSYLYMYNYO $.

    $( The edges starting at an inside vertex ` X ` in a generalized Petersen
       graph ` G ` .  (Contributed by AV, 2-Sep-2025.) $)
    gpgvtxedg1 $p |- ( ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
                         /\ ( 1st ` X ) = 1 /\ { X , Y } e. E )
                       -> ( Y = <. 1 , ( ( ( 2nd ` X ) + K ) mod N ) >.
                         \/ Y = <. 0 , ( 2nd ` X ) >.
                         \/ Y = <. 1 , ( ( ( 2nd ` X ) - K ) mod N ) >. ) ) $=
      ( wcel wa c1 wceq co cmo cc0 wi vy c3 cuz cfv c1st cpr w3a c2nd caddc cop
      cmin w3o cusgr cdiv cceil cfzo cgpg gpgusgra eleq2i anbi2i eleq1i 3imtr4i
      c2 3ad2ant1 simp3 usgrpredgv syl2anc cv wrex wb eqid gpgedgel wo cvv opex
      adantr pm3.2i preq12bg sylancl vex op1std eqeq1d eqcom bitrdi wne ax-1ne0
      c0ex eqneqall com12 mp1i sylbid impd ovex jaod 3ad2ant2 1ex op2ndd eqcomd
      simpr opeq2d eqtrd adantl 3mix2d ex oveq1d 3mix1d a1i elfzoelz zred sylbi
      cr crp readdcld cn0 cn clt wbr elfzo0 nnrp modsubmod syl3anc recnd pncand
      zcnd zmodidfzoimp 3eqtrrd imp eqeq12d mpbird 3mix3d 3jaod rexlimdva com34
      cc 3exp 3imp mpd ) EUBUCUDMZDCMZNZGUEUDZOPZGHUFZAMZUGZGFMHFMNZHOGUHUDZDUI
      QZERQZUJZPZHSUUGUJZPZHOUUGDUKQZERQZUJZPZULZUUEBUMMZUUDUUFYTUUBUUSUUDYRDOE
      VCUNQUOUDZUPQZMZNEDUQQZUMMYTUUSDEURYSUVBYRCUVADIUSZUTBUVCUMJVAVBVDYTUUBUU
      DVEABGHFLKVFVGYTUUBUUDUUFUURTYTUUBUUFUUDUURYTUUBUUFUUDUURTYTUUBUUFUGZUUDU
      UCSUAVHZUJZSUVFOUIQZERQZUJZUFPZUUCUVGOUVFUJZUFPZUUCUVLOUVFDUIQZERQZUJZUFP
      ZULZUASEUPQZVIZUURYTUUBUUDUVTVJUUFUAABUVSCDEUUCUVSVKIJLVLVDUVEUVRUURUAUVS
      UVEUVFUVSMZNZUVKUURUVMUVQUWBUVKGUVGPZHUVJPZNZGUVJPZHUVGPZNZVMZUURUWBUUFUV
      GVNMZUVJVNMZNUVKUWIVJUVEUUFUWAYTUUBUUFVEVPZUWJUWKSUVFVOZSUVIVOVQGHUVGUVJF
      FVNVNVRVSUVEUWIUURTZUWAUUBYTUWNUUFUUBUWEUURUWHUUBUWCUWDUURUWCUUBUWDUURTZU
      WCUUBOSPZUWOUWCUUBSOPZUWPUWCUUASOSUVFGWGUAVTZWAWBSOWCZWDZOSWEZUWPUWOTUWCW
      FUWPUXAUWOUWOOSWHWIWJWKWIWLUUBUWFUWGUURUWFUUBUWGUURTZUWFUUBUWPUXBUWFUUBUW
      QUWPUWFUUASOSUVIGWGUVHERWMWAWBUWSWDUXAUWPUXBTUWFWFUWPUXAUXBUXBOSWHWIWJWKW
      IWLWNWOVPWKUWBUVMUWCHUVLPZNZGUVLPZUWGNZVMZUURUWBUUFUWJUVLVNMZNUVMUXGVJUWL
      UWJUXHUWMOUVFVOZVQGHUVGUVLFFVNVNVRVSUWBUXDUURUXFUWBUWCUXCUURUVEUWCUXCUURT
      ZTZUWAUUBYTUXKUUFUWCUUBUXJUWCUUBUWPUXJUWTUXAUWPUXJTUWCWFUWPUXAUXJUXJOSWHW
      IWJWKWIWOVPWLUWBUXFUURUWBUXFNUUMUUKUUQUXFUUMUWBUXFHUVGUULUXEUWGWSUXFUVFUU
      GSUXEUVFUUGPUWGUXEUUGUVFOUVFGWPUWRWQWRZVPWTXAXBXCXDWNWKUWBUVQUXEHUVPPZNZG
      UVPPZUXCNZVMZUURUWBUUFUXHUVPVNMZNUVQUXQVJUWLUXHUXRUXIOUVOVOVQGHUVLUVPFFVN
      VNVRVSUWBUXNUURUXPUXNUURTUWBUXNUUKUUMUUQUXNHUVPUUJUXEUXMWSUXNUVOUUIOUXEUV
      OUUIPUXMUXEUVNUUHERUXEUVFUUGDUIUXLXEXEVPWTXAXFXGUWBUXPUURUWBUXPNZUUQUUKUU
      MUXSUUQUVLOUVODUKQZERQZUJZPZUXSUVFUYAOUWBUVFUYAPZUXPUVEUWAUYDYTUUBUWAUYDT
      ZUUFYSUYEYRYSUWAUYDYSUWANZUYAUVNDUKQZERQZUVFERQZUVFUYFUVNXKMDXKMZEXLMZUYA
      UYHPUYFUVFDUWAUVFXKMYSUWAUVFUVFSEXHZXIXBYSUYJUWAYSUVBUYJUVDUVBDDOUUTXHXIX
      JVPZXMUYMUWAUYKYSUWAUVFXNMZEXOMZUVFEXPXQZUGUYKUVFEXRUYOUYNUYKUYPEXSWOXJXB
      UVNDEXTYAUYFUYGUVFERUYFUVFDUWAUVFYNMYSUWAUVFUYLYDXBUYFDUYMYBYCXEUWAUYIUVF
      PYSUVFEYEXBYFXDXBVDYGVPWTUXPUUQUYCVJUWBUXPHUVLUUPUYBUXOUXCWSUXOUUPUYBPUXC
      UXOUUOUYAOUXOUUNUXTERUXOUUGUVODUKOUVOGWPUVNERWMWQXEXEWTVPYHXBYIYJXDWNWKYK
      YLWKYOYMYPYQ $.
  $}

  ${
    $d I x $.  $d J x $.  $d K x $.  $d N x $.  $d X x $.  $d Y x $.
    gpgedgiov.j $e |- J = ( 1 ..^ ( |^ ` ( N / 2 ) ) ) $.
    gpgedgiov.i $e |- I = ( 0 ..^ N ) $.
    gpgedgiov.g $e |- G = ( N gPetersenGr K ) $.
    gpgedgiov.e $e |- E = ( Edg ` G ) $.
    $( The edges of the generalized Petersen graph GPG(N,K) between an inside
       and an outside vertex.  (Contributed by AV, 11-Nov-2025.) $)
    gpgedgiov $p |- ( ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
                        /\ ( X e. I /\ Y e. I ) )
                      -> ( { <. 0 , X >. , <. 1 , Y >. } e. E <-> X = Y ) ) $=
      ( wa cc0 cop c1 wceq co cmo cvv vx c3 cuz cfv wcel cpr c2nd cmin w3o c1st
      caddc simpll c0ex a1i anim1i ancoms op1stg ad2antlr simpr cvtx gpgvtxedg0
      syl eqid syl3anc ex wi wb ovex pm3.2i opthg2 wne ax-1ne0 eqneqall mpi imp
      mp1i biimtrdi 1ex eqcomd 3jaod op2ndg oveq1 oveq1d opeq2d opeq2 3orbi123d
      eqeq2d imbi1d mpbird adantl syld cv wrex preq12d 3mix2d rspcedvd gpgedgel
      eqidd ad2antrr preq1d eleq1d impbid ) FUBUCUDUEEDUEMZGCUEZHCUEZMZMZNGOZPH
      OZUFZAUEZGHQZXGXKXINXHUGUDZPUKRZFSRZOZQZXIPXMOZQZXINXMPUHRZFSRZOZQZUIZXLX
      GXKYDXGXKMXCXHUJUDNQZXKYDXCXFXKULXFYEXCXKXFNTUEZXDMZYEXEXDYGXEYFXDYFXEUMU
      NUOUPZNGTCUQVBURXGXKUSABDEFBUTUDZXHXIIKYIVCLVAVDVEXFYDXLVFZXCXFYJXINGPUKR
      ZFSRZOZQZXIPGOZQZXINGPUHRZFSRZOZQZUIZXLVFZXFYNXLYPYTXFYNPNQZHYLQZMZXLYFYL
      TUEZMYNUUEVGXFYFUUFUMYKFSVHVIPHNYLTTVJVPUUCUUDXLUUCPNVKZUUDXLVFZVLUUHPNVM
      VNVOVQXFYPPPQZHGQZMZXLXFPTUEZXDMZYPUUKVGXEXDUUMXEUULXDUULXEVRUNUOUPPHPGTC
      VJVBUUKHGUUIUUJUSVSVQXFYTUUCHYRQZMZXLYFYRTUEZMYTUUOVGXFYFUUPUMYQFSVHVIPHN
      YRTTVJVPUUCUUNXLUUCUUGUUNXLVFZVLUUQPNVMVNVOVQVTXFXMGQZYJUUBVGXFYGUURYHNGT
      CWAVBUURYDUUAXLUURXQYNXSYPYCYTUURXPYMXIUURXOYLNUURXNYKFSXMGPUKWBWCWDWGUUR
      XRYOXIXMGPWEWGUURYBYSXIUURYAYRNUURXTYQFSXMGPUHWBWCWDWGWFWHVBWIWJWKXGXLXKX
      GXLMZXKNHOZXIUFZAUEZUUSUVBUVANUAWLZOZNUVCPUKRZFSRZOZUFZQZUVAUVDPUVCOZUFZQ
      ZUVAUVJPUVCEUKRZFSRZOZUFZQZUIZUACWMZUUSUVRUVAUUTNHPUKRZFSRZOZUFZQZUVAUVAQ
      ZUVAXIPHEUKRZFSRZOZUFZQZUIZUAHCXFXEXCXLXDXEUSURUVCHQZUVRUWKVGUUSUWLUVIUWD
      UVLUWEUVQUWJUWLUVHUWCUVAUWLUVDUUTUVGUWBUVCHNWEZUWLUVFUWANUWLUVEUVTFSUVCHP
      UKWBWCWDWNWGUWLUVKUVAUVAUWLUVDUUTUVJXIUWMUVCHPWEZWNWGUWLUVPUWIUVAUWLUVJXI
      UVOUWHUWNUWLUVNUWGPUWLUVMUWFFSUVCHEUKWBWCWDWNWGWFWJUUSUWEUWDUWJUUSUVAWRWO
      WPXCUVBUVSVGXFXLUAABCDEFUVAJIKLWQWSWIXLXKUVBVGXGXLXJUVAAXLXHUUTXIGHNWEWTX
      AWJWIVEXB $.

    $( The edges of the generalized Petersen graph GPG(N,K) between two outside
       vertices.  (Contributed by AV, 15-Nov-2025.) $)
    gpgedg2ov $p |- ( ( ( N e. ( ZZ>= ` 5 ) /\ K e. J )
                        /\ ( X e. I /\ Y e. I ) )
                  -> ( ( { <. 0 , ( ( Y - 1 ) mod N ) >. , <. 0 , X >. } e. E
                      /\ { <. 0 , X >. , <. 0 , ( ( Y + 1 ) mod N ) >. } e. E )
                       <-> X = Y ) ) $=
      ( wcel wa cc0 c1 co cmo wceq wi cuz cfv cmin cop cpr caddc c2nd w3o prcom
      c5 eleq1i c3 c1st uzuzle35 anim1i adantr cvv a1i ancoms op1stg syl adantl
      c0ex simpr cvtx eqid gpgvtxedg0 syl3anc ex biimtrid ovex opth ancomd 1zzd
      cz wb modaddid biimpa eqcomd adantld imp a1d wne 0ne1 eqneqall mpi eqcoms
      eqeq2 modm1nep1 syl2an com12 sylbid orci opthne mpbir 3jaod simpll simprl
      wo simprr modm1p1ne syld com23 op2ndg mpan oveq1d opeq2d eqeq2d 3orbi123d
      oveq1 opeq2 imbi1d imbi12d mpbird impd jctil opgpgvtx gpgedgvtx0 syl12anc
      w3a preq2d eqtrdi eleq1d anbi12d biimpcd 3adant2 preq1d syl5ibrcom impbid
      sylan mpd ) FUJUAUBMZEDMZNZGCMZHCMZNZNZOHPUCQZFRQZUDZOGUDZUEZAMZUUBOHPUFQ
      ZFRQZUDZUEZAMZNZGHSZYRUUDUUIUUKYRUUDUUAOUUBUGUBZPUFQZFRQZUDZSZUUAPUULUDZS
      ZUUAOUULPUCQZFRQZUDZSZUHZUUIUUKTUUDUUBUUAUEZAMZYRUVCUUCUVDAUUAUUBUIUKYRUV
      EUVCYRUVENFULUAUBMZYMNZUUBUMUBOSZUVEUVCYRUVGUVEYNUVGYQYLUVFYMFUNZUOZUPZUP
      YRUVHUVEYQUVHYNYQOUQMZYONZUVHYPYOUVMYPUVLYOUVLYPVCURUOUSOGUQCUTVAVBZUPYRU
      VEVDABDEFBVEUBZUUBUUAIKUVOVFZLVGVHVIVJYRUUIUVCUUKYRUUIUUGUUOSZUUGUUQSZUUG
      UVASZUHZUVCUUKTZYRUUIUVTYRUUINUVGUVHUUIUVTYRUVGUUIUVKUPYRUVHUUIUVNUPYRUUI
      VDABDEFUVOUUBUUGIKUVPLVGVHVIYRUVTUWATZUUGOGPUFQZFRQZUDZSZUUGPGUDZSZUUGOGP
      UCQZFRQZUDZSZUHZUUAUWESZUUAUWGSZUUAUWKSZUHZUUKTZTZYRUWFUWRUWHUWLYRUWFUWRY
      RUWFNUUKUWQYRUWFUUKUWFOOSZUUFUWDSZNYRUUKOUUFOUWDVCUUEFRVKZVLYRUXAUUKUWTYR
      UXAUUKYRUXANHGYRUXAHGSZYRUVFYPYONPVOMUXAUXCVPYNUVFYQYLUVFYMUVIUPZUPYRYOYP
      YNYQVDVMYRVNCPFHGJVQVHVRVSVIVTVJWAWBVIYRUWHUWRYRUWHNZUWNUUKUWOUWPYRUWHUWN
      UUKTZUWHOPSZUUFGSZNZYRUXFOUUFPGVCUXBVLUXIUXFTYRUXGUXHUXFUXGOPWCZUXHUXFTZW
      DUXKOPWEWFWAURVJWAUXEUWOUUAUUGSZUUKUWHUWOUXLVPZYRUXMUWGUUGUWGUUGUUAWHWGVB
      YRUXLUUKTZUWHUXLUWTYTUUFSZNYRUUKOYTOUUFVCYSFRVKZVLYRUXOUUKUWTYRYTUUFWCZUX
      OUUKTYNUVFYPUXQYQUXDYOYPVDZCFHJWIWJUXOUXQUUKUUKYTUUFWEWKVAVTVJZUPWLYRUWHU
      WPUUKTZYRUUGUWGWCZUWHUXTTUYAYRUYAUXJUUFGWCZWSUXJUYBWDWMOUUFPGVCUXBWNWOURU
      WHUYAUXTUXTUUGUWGWEWKVAWAWPVIYRUWLUWRYRUWLNZUWNUUKUWOUWPYRUWLUXFUWLUWTUUF
      UWJSZNYRUXFOUUFOUWJVCUXBVLYRUYDUXFUWTYRUWNUYDUUKUWNUWTYTUWDSZNYRUYDUUKTZO
      YTOUWDVCUXPVLYRUYEUYFUWTYRUYEUUFUWJWCZUYFYRYLYOYPUYEUYGTYLYMYQWQYNYOYPWRY
      NYOYPWTCFGHJXAVHUYGUYFTYRUYDUYGUUKUUKUUFUWJWEWKURXBVTVJXCVTVJWAUWOUUKTUYC
      UWOUUAUWGWCZUUKUYHUXJYTGWCZWSUXJUYIWDWMOYTPGVCUXPWNWOUUKUUAUWGWEWFURUYCUW
      PUXLUUKUWLUWPUXLVPZYRUYJUWKUUGUWKUUGUUAWHWGVBYRUXNUWLUXSUPWLWPVIWPYRUULGS
      ZUWBUWSVPYQUYKYNYOUYKYPUVLYOUYKVCOGUQCXDXEUPVBUYKUVTUWMUWAUWRUYKUVQUWFUVR
      UWHUVSUWLUYKUUOUWEUUGUYKUUNUWDOUYKUUMUWCFRUULGPUFXJXFXGZXHUYKUUQUWGUUGUUL
      GPXKZXHUYKUVAUWKUUGUYKUUTUWJOUYKUUSUWIFRUULGPUCXJXFXGZXHXIUYKUVCUWQUUKUYK
      UUPUWNUURUWOUVBUWPUYKUUOUWEUUAUYLXHUYKUUQUWGUUAUYMXHUYKUVAUWKUUAUYNXHXIXL
      XMVAXNXBXCXBXOYRUUJUUKUUAOHUDZUEZAMZUYOUUGUEZAMZNZYRUYOOUYOUGUBZPUFQZFRQZ
      UDZUEZAMZUYOPVUAUDUEAMZUYOOVUAPUCQZFRQZUDZUEZAMZXTZUYTYRUVGUYOUVOMZUYOUMU
      BOSZVUMUVKYRVUNUWTUXGWSZYPNZYQVUQYNYQYPVUPUXRUWTUXGOVFWMXPVBYNVUNVUQVPZYQ
      YNUVGVURUVJBCDEFUVOOHJIKUVPXQVAUPXNYQVUOYNYOUVLYPVUOUVLYOVCUROHUQCUTYJVBA
      BDEFUVOUYOIKUVPLXRXSYQVUMUYTTZYNYPVUSYOVUMYPUYTVUFVULYPUYTTZVUGVULVUFVUTY
      PVULVUFNZUYTYPVUAHSZVVAUYTVPUVLYPVVBVCOHUQCXDXEVVBVULUYQVUFUYSVVBVUKUYPAV
      VBVUKUYOUUAUEUYPVVBVUJUUAUYOVVBVUIYTOVVBVUHYSFRVUAHPUCXJXFXGYAUYOUUAUIYBY
      CVVBVUEUYRAVVBVUDUUGUYOVVBVUCUUFOVVBVUBUUEFRVUAHPUFXJXFXGYAYCYDVAYEUSYFWK
      VBVBYKUUKUUDUYQUUIUYSUUKUUCUYPAUUKUUBUYOUUAGHOXKZYAYCUUKUUHUYRAUUKUUBUYOU
      UGVVCYGYCYDYHYI $.

    $( The edges of the generalized Petersen graph GPG(N,K) between two inside
       vertices.  (Contributed by AV, 20-Nov-2025.) $)
    gpgedg2iv $p |- ( ( N e. ( ZZ>= ` 5 ) /\ ( X e. I /\ Y e. I )
                        /\ ( K e. J /\ ( ( 4 x. K ) mod N ) =/= 0 ) )
                  -> ( ( { <. 1 , ( ( Y - K ) mod N ) >. , <. 1 , X >. } e. E
                      /\ { <. 1 , X >. , <. 1 , ( ( Y + K ) mod N ) >. } e. E )
                       <-> X = Y ) ) $=
      ( wcel wa co cmo cc0 c1 wceq wi c5 cuz cfv c4 cmul wne w3a cmin cop caddc
      cpr c2nd w3o prcom eleq1i c3 c1st uzuzle35 anim12i 3adant2 adantr cvv 1ex
      simpl a1i anim1i ancoms op1stg syl 3ad2ant2 simpr cvtx gpgvtxedg1 syl3anc
      eqid ex biimtrid ovex opth cz wb 3ad2ant1 simp2 ancomd c2 cdiv cceil cfzo
      elfzoelz eleq2s 3ad2ant3 modaddid biimpa eqcomd adantld a1dd eqneqall mpi
      ax-1ne0 imp biimtrdi wo orci opthne mpbir mpan9 3jaod cn eluz3nn ad2antrl
      ad2antll adantl modmkpkne syl13anc expimpd com23 3impia expd eqeq2 eqcoms
      modmknepk syl3an sylbid op2ndg oveq1 oveq1d opeq2d eqeq2d opeq2 3orbi123d
      syl5com imbi1d imbi12d mpbird syld impd olci preq2d eleq1d anbi12d eqtrdi
      2a1i imdistanri opgpgvtx sylan gpgedgvtx1 syl12anc mpan biimpcd com12 mpd
      preq1d syl5ibrcom impbid ) FUAUBUCMZGCMZHCMZNZEDMZUDEUEOFPOZQUFZNZUGZRHEU
      HOZFPOZUIZRGUIZUKZAMZUVGRHEUJOZFPOZUIZUKZAMZNZGHSZUVCUVIUVNUVPUVCUVIUVFRU
      VGULUCZEUJOZFPOZUIZSZUVFQUVQUIZSZUVFRUVQEUHOZFPOZUIZSZUMZUVNUVPTUVIUVGUVF
      UKZAMZUVCUWHUVHUWIAUVFUVGUNUOUVCUWJUWHUVCUWJNFUPUBUCMZUUSNZUVGUQUCRSZUWJU
      WHUVCUWLUWJUUOUVBUWLUURUUOUWKUVBUUSFURZUUSUVAVDZUSZUTZVAUVCUWMUWJUURUUOUW
      MUVBUURRVBMZUUPNZUWMUUQUUPUWSUUQUWRUUPUWRUUQVCVEVFVGZRGVBCVHVIVJZVAUVCUWJ
      VKABDEFBVLUCZUVGUVFIKUXBVOZLVMVNVPVQUVCUVNUWHUVPUVCUVNUVLUVTSZUVLUWBSZUVL
      UWFSZUMZUWHUVPTZUVCUVNUXGUVCUVNNUWLUWMUVNUXGUVCUWLUVNUWQVAUVCUWMUVNUXAVAU
      VCUVNVKABDEFUXBUVGUVLIKUXCLVMVNVPUVCUXGUXHTZUVLRGEUJOZFPOZUIZSZUVLQGUIZSZ
      UVLRGEUHOZFPOZUIZSZUMZUVFUXLSZUVFUXNSZUVFUXRSZUMZUVPTZTZUVCUXMUYEUXOUXSUV
      CUXMUVPUYDUXMRRSZUVKUXKSZNUVCUVPRUVKRUXKVCUVJFPVRZVSUVCUYHUVPUYGUVCUYHUVP
      UVCUYHNHGUVCUYHHGSZUVCUWKUUQUUPNEVTMZUYHUYJWAUUOUURUWKUVBUWNWBUVCUUPUUQUU
      OUURUVBWCWDUVBUUOUYKUURUUSUYKUVAUYKERFWEWFOWGUCZWHODERUYLWIIWJZVAWKCEFHGJ
      WLVNWMWNVPWOVQWPUVCUXOUYEUVCUXONZUYAUVPUYBUYCUVCUXOUYAUVPTZUVCUXORQSZUVKG
      SZNZUYOUXOUYRWAUVCRUVKQGVCUYIVSVEUYPUYQUYOUYPRQUFZUYQUYOTZWSUYTRQWQWRWTXA
      WTUYNUYBUYPUVEGSZNZUVPUYBVUBWAUYNRUVEQGVCUVDFPVRZVSVEUYPVUAUVPUYPUYSVUAUV
      PTZWSVUDRQWQWRWTXAUVCUVLUXNUFZUXOUYCUVPTZVUEUVCVUEUYSUVKGUFZXBUYSVUGWSXCR
      UVKQGVCUYIXDXEVEVUFUVLUXNWQXFXGVPUVCUXSUYEUVCUXSNZUYAUVPUYBUYCUVCUXSUYOUX
      SUYGUVKUXQSZNUVCUYORUVKRUXQVCUYIVSUVCVUIUYOUYGUVCUYAVUIUVPUYAUYGUVEUXKSZN
      UVCVUIUVPTZRUVERUXKVCVUCVSUVCVUJVUKUYGUVCVUJVUIUVPUUOUURUVBVUJVUINZUVPTZU
      UOUURNZUUSUVAVUMVUNUUSNZVULUVAUVPVUOVUJVUIUVAUVPTZVUOVUJNVUIUUTQSZVUPVUOV
      UJVUIVUQWAZVUOFXHMZGVTMZHVTMZUYKVUJVURTVUNVUSUUSUUOVUSUURUUOUWKVUSUWNFXIV
      IVAVAVUNVUTUUSUUPVUTUUOUUQVUTGQFWHOZCGQFWIJWJXJVAVUNVVAUUSUUQVVAUUOUUPVVA
      HVVBCHQFWIJWJXKVAUUSUYKVUNUYMXLEFGHXMXNWTUVPUUTQWQXAXOXPXOXQXRWOVQXPWOVQW
      TUYBUVPTVUHUYBUVFUXNUFZUVPVVCUYSUVEGUFZXBUYSVVDWSXCRUVEQGVCVUCXDXEUVPUVFU
      XNWQWRVEVUHUYCUVFUVLSZUVPUXSUYCVVEWAZUVCVVFUXRUVLUXRUVLUVFXSXTXLUVCVVEUVP
      TUXSVVEUYGUVEUVKSZNUVCUVPRUVERUVKVCVUCVSUVCVVGUVPUYGUVCUVEUVKUFZVVGUVPUUO
      UWKUURUUQUVBUUSVVHUWNUUPUUQVKUWOCDEFHIJYAYBUVPUVEUVKWQYKWOVQVAYCXGVPXGUVC
      UVQGSZUXIUYFWAUURUUOVVIUVBUURUWSVVIUWTRGVBCYDVIVJVVIUXGUXTUXHUYEVVIUXDUXM
      UXEUXOUXFUXSVVIUVTUXLUVLVVIUVSUXKRVVIUVRUXJFPUVQGEUJYEYFYGZYHVVIUWBUXNUVL
      UVQGQYIZYHVVIUWFUXRUVLVVIUWEUXQRVVIUWDUXPFPUVQGEUHYEYFYGZYHYJVVIUWHUYDUVP
      VVIUWAUYAUWCUYBUWGUYCVVIUVTUXLUVFVVJYHVVIUWBUXNUVFVVKYHVVIUWFUXRUVFVVLYHY
      JYLYMVIYNYOXPYOYPUVCUVOUVPUVFRHUIZUKZAMZVVMUVLUKZAMZNZUVCVVMRVVMULUCZEUJO
      ZFPOZUIZUKZAMZVVMQVVSUIUKAMZVVMRVVSEUHOZFPOZUIZUKZAMZUGZVVRUVCUWLVVMUXBMZ
      VVMUQUCRSZVWKUWQUVCVWLUYPUYGXBZUUQNZUURUUOVWOUVBUUQUUPVWNVWNUUQUUPUYGUYPR
      VOYQUUBUUCVJUUOUVBVWLVWOWAZUURUUOUVBNUWLVWPUWPBCDEFUXBRHJIKUXCUUDVIUTYNUU
      RUUOVWMUVBUUPUWRUUQVWMUWRUUPVCVERHVBCVHUUEVJABDEFUXBVVMIKUXCLUUFUUGUURUUO
      VWKVVRTZUVBUUQVWQUUPVWKUUQVVRVWDVWJUUQVVRTZVWEVWJVWDVWRUUQVWJVWDNZVVRUUQV
      VSHSZVWSVVRWAUWRUUQVWTVCRHVBCYDUUHVWTVWJVVOVWDVVQVWTVWIVVNAVWTVWIVVMUVFUK
      VVNVWTVWHUVFVVMVWTVWGUVERVWTVWFUVDFPVVSHEUHYEYFYGYRVVMUVFUNUUAYSVWTVWCVVP
      AVWTVWBUVLVVMVWTVWAUVKRVWTVVTUVJFPVVSHEUJYEYFYGYRYSYTVIUUIVGUTUUJXLVJUUKU
      VPUVIVVOUVNVVQUVPUVHVVNAUVPUVGVVMUVFGHRYIZYRYSUVPUVMVVPAUVPUVGVVMUVLVXAUU
      LYSYTUUMUUN $.
  $}

  ${
    $d J x $.  $d K x $.  $d N x $.  $d V x $.  $d X x $.  $d W x $.
    gpg5nbgrvtx03starlem1.j $e |- J = ( 1 ..^ ( |^ ` ( N / 2 ) ) ) $.
    gpg5nbgrvtx03starlem1.g $e |- G = ( N gPetersenGr K ) $.
    gpg5nbgrvtx03starlem1.v $e |- V = ( Vtx ` G ) $.
    gpg5nbgrvtx03starlem1.e $e |- E = ( Edg ` G ) $.
    $( Lemma 1 for ~ gpg5nbgrvtx03star .  (Contributed by AV, 5-Sep-2025.) $)
    gpg5nbgrvtx03starlem1 $p |- ( ( N e. ( ZZ>= ` 3 ) /\ K e. J /\ X e. W )
                   -> { <. 0 , ( ( X + 1 ) mod N ) >. , <. 1 , X >. } e/ E ) $=
      ( vx wcel cc0 c1 wne wa cvv wo c3 cuz cfv w3a caddc co cmo cop wn wnel cv
      cpr wceq w3o cfzo wrex wral opex pm3.2i ax-1ne0 orci a1i wb 1ex simp3 jca
      adantr opthneg syl mpbird orcd olcd prneimg mpsyl eleq1 uzuzle23 3ad2ant1
      wi c2 p1modne sylan ex adantl sylbird impr neeq2 mpbid olc pm2.61ine c0ex
      a1d ovex opthne neirr biorfi bitr4i bitr4di prneimg2 mp1i 0ne1 mpbir 3jca
      orbi12d ralrimiva ralnex 3ioran df-ne 3anbi123i ralbii bitr3i sylibr eqid
      gpgedgel 3adant3 mtbird df-nel ) EUAUBUCNZDCNZHGNZUDZOHPUEUFZEUGUFZUHZPHU
      HZULZANZUIYEAUJXTYFYEOMUKZUHZOYGPUEUFEUGUFZUHZULZUMZYEYHPYGUHZULZUMZYEYMP
      YGDUEUFEUGUFZUHZULZUMZUNZMOEUOUFZUPZXTYEYKQZYEYNQZYEYRQZUDZMUUAUQZUUBUIZX
      TUUFMUUAXTYGUUANZRZUUCUUDUUEYCSNZYDSNZRZYHSNZYJSNZRZRUUJYCYHQZYCYJQRZYDYH
      QZYDYJQZRZTUUCUUMUUPUUKUULOYBURPHURUSZUUNUUOOYGURZOYIURUSUSUUJUVAUURUUJUU
      SUUTUUJUUSPOQZHYGQZTZUVFUUJUVDUVEUTVAVBUUJPSNZXSRZUUSUVFVCXTUVHUUIXTUVGXS
      UVGXTVDVBXQXRXSVEVFVGZPHOYGSGVHVIVJZUUJUUTUVDHYIQZTZUUJUVDUVKUVDUUJUTVBVK
      UUJUVHUUTUVLVCUVIPHOYISGVHVIVJVFVLYCYDYHYJSSSSVMVNUUJUUDUUQYDYMQZTZYCYMQZ
      UUSTZRZUUJUVNUVPUUJUVNYBYGQZUVETZUUJUVSVRHYGHYGUMZUUJUVSUVTUUJRZUVRUVEUWA
      YBHQZUVRUVTXTUUIUWBUVTXTRUUIHUUANZUWBUVTUWCUUIVCXTHYGUUAVOVGXTUWCUWBVRUVT
      XTUWCUWBXTEVSUBUCNZUWCUWBXQXRUWDXSEVPVQHEVTWAWBWCWDWEUVTUWBUVRVCUUJHYGYBW
      FVGWGVKWBUVEUVSUUJUVEUVRWHWKWIUUJUUQUVRUVMUVEUUQUVRVCUUJUUQOOQZUVRTUVROYB
      OYGWJYAEUGWLZWMUWEUVROWNWOWPVBUUJUVMPPQZUVETZUVEUUJUVHUVMUWHVCUVIPHPYGSGV
      HVIUWGUVEPWNWOWQXCVJUUJUUSUVOUVJVLVFUUMUUNYMSNZRZRUUDUVQVCUUJUUMUWJUVBUUN
      UWIUVCPYGURZUSUSYCYDYHYMSSSSWRWSVJUUMUWIYQSNZRZRUUJUVOYCYQQZRZUVMYDYQQRZT
      UUEUUMUWMUVBUWIUWLUWKPYPURUSUSUUJUWOUWPUWOUUJUVOUWNUVOOPQZUVRTUWQUVRWTVAO
      YBPYGWJUWFWMXAUWNUWQYBYPQZTUWQUWRWTVAOYBPYPWJUWFWMXAUSVBVKYCYDYMYQSSSSVMV
      NXBXDUUHYTUIZMUUAUQUUGYTMUUAXEUWSUUFMUUAUWSYLUIZYOUIZYSUIZUDUUFYLYOYSXFUU
      CUWTUUDUXAUUEUXBYEYKXGYEYNXGYEYRXGXHWPXIXJXKXQXRYFUUBVCXSMABUUACDEYEUUAXL
      IJLXMXNXOYEAXPXK $.

    $( Lemma 2 for ~ gpg5nbgrvtx03star .  (Contributed by AV, 6-Sep-2025.) $)
    gpg5nbgrvtx03starlem2 $p |- ( ( N e. ( ZZ>= ` 4 ) /\ K e. J /\ X e. ZZ )
                                 -> { <. 0 , ( ( X + 1 ) mod N ) >. ,
                                      <. 0 , ( ( X - 1 ) mod N ) >. } e/ E ) $=
      ( wcel cc0 c1 co cmo wne wa wo cvv vx c4 cuz cfv cz w3a caddc cop cmin wn
      cpr wnel cv wceq w3o cfzo wrex wi c2 m1modnep2mod 3adant2 cc zcn 3ad2ant3
      wral add1p1 syl oveq1d neeqtrrd cr crp zre 1red readdcld eluz4nn 3ad2ant1
      nnrpd modaddmod syl3anc ad2antrl adantr neeqtrd olcd ex orc a1d pm2.61ine
      oveq1 wb c0ex ovex opthne neirr biorfi bitr4i a1i orbi12d mpbird uzuzle24
      anim1i zp1modne npcan1 resubcld orcd opex pm3.2i mp1i mpbir2and 0ne1 orci
      prneimg2 mpbir olci prneimg mpsyl ralrimiva ralnex 3ioran df-ne 3anbi123i
      olc 3jca ralbii bitr3i sylibr uzuzle34 eqid gpgedgel sylan 3adant3 mtbird
      c3 df-nel ) EUBUCUDLZDCLZGUELZUFZMGNUGOZEPOZUHZMGNUIOZEPOZUHZUKZALZUJUUDA
      ULYQUUEUUDMUAUMZUHZMUUFNUGOZEPOZUHZUKZUNZUUDUUGNUUFUHZUKZUNZUUDUUMNUUFDUG
      OEPOZUHZUKZUNZUOZUAMEUPOZUQZYQUUDUUKQZUUDUUNQZUUDUURQZUFZUAUVAVEZUVBUJZYQ
      UVFUAUVAYQUUFUVALZRZUVCUVDUVEUVJUVCYTUUGQZUUCUUJQZSZYTUUJQZUUCUUGQZSZUVJU
      VMYSUUFQZUUBUUIQZSZUVJUVSURYSUUFYSUUFUNZUVJUVSUVTUVJRZUVRUVQUWAUUBYSNUGOZ
      EPOZUUIYQUUBUWCQUVTUVIYQUUBYRNUGOZEPOZUWCYQUUBGUSUGOZEPOZUWEYNYPUUBUWGQYO
      GEUTVAYQUWDUWFEPYQGVBLZUWDUWFUNYPYNUWHYOGVCVDZGVFVGVHVIYQYRVJLNVJLZEVKLZU
      WCUWEUNYQGNYPYNGVJLYOGVLVDZYQVMZVNUWMYNYOUWKYPYNEEVOVQVPZYRNEVRVSVIVTUVTU
      WCUUIUNUVJUVTUWBUUHEPYSUUFNUGWHVHWAWBWCWDUVQUVSUVJUVQUVRWEWFWGUVJUVKUVQUV
      LUVRUVKUVQWIUVJUVKMMQZUVQSUVQMYSMUUFWJYREPWKZWLUWOUVQMWMZWNWOWPUVLUVRWIUV
      JUVLUWOUVRSUVRMUUBMUUIWJUUAEPWKZWLUWOUVRUWQWNWOWPWQWRUVJUVPYSUUIQZUUBUUFQ
      ZSZUVJUXAURUUBUUFUUBUUFUNZUVJUXAUXBUVJRZUWSUWTUXCYSUUBNUGOZEPOZUUIYQYSUXE
      QUXBUVIYQYSUUANUGOZEPOZUXEYQYSGEPOZUXGYQEUSUCUDLZYPRZYSUXHQYNYPUXJYOYNUXI
      YPEWSWTVAGEXAVGYQUXFGEPYQUWHUXFGUNUWIGXBVGVHVIYQUUAVJLUWJUWKUXEUXGUNYQGNU
      WLUWMXCUWMUWNUUANEVRVSVIVTUXBUXEUUIUNUVJUXBUXDUUHEPUUBUUFNUGWHVHWAWBXDWDU
      WTUXAUVJUWTUWSYAWFWGUVJUVNUWSUVOUWTUVNUWSWIUVJUVNUWOUWSSUWSMYSMUUIWJUWPWL
      UWOUWSUWQWNWOWPUVOUWTWIUVJUVOUWOUWTSUWTMUUBMUUFWJUWRWLUWOUWTUWQWNWOWPWQWR
      YTTLZUUCTLZRZUUGTLZUUJTLZRZRUVCUVMUVPRWIUVJUXMUXPUXKUXLMYSXEMUUBXEXFZUXNU
      XOMUUFXEZMUUIXEXFXFYTUUCUUGUUJTTTTXKXGXHUVJUVDUVKUUCUUMQZSZYTUUMQZUVOSZRZ
      UYCUVJUXTUYBUXSUVKUXSMNQZUWTSUYDUWTXIXJMUUBNUUFWJUWRWLXLXMUYAUVOUYAUYDUVQ
      SUYDUVQXIXJMYSNUUFWJUWPWLXLZXJXFWPUXMUXNUUMTLZRZRUVDUYCWIUVJUXMUYGUXQUXNU
      YFUXRNUUFXEZXFXFYTUUCUUGUUMTTTTXKXGWRUXMUYFUUQTLZRZRUVJUYAYTUUQQZRZUXSUUC
      UUQQRZSUVEUXMUYJUXQUYFUYIUYHNUUPXEXFXFUVJUYLUYMUYLUVJUYAUYKUYEUYKUYDYSUUP
      QZSUYDUYNXIXJMYSNUUPWJUWPWLXLXFWPXDYTUUCUUMUUQTTTTXNXOYBXPUVHUUTUJZUAUVAV
      EUVGUUTUAUVAXQUYOUVFUAUVAUYOUULUJZUUOUJZUUSUJZUFUVFUULUUOUUSXRUVCUYPUVDUY
      QUVEUYRUUDUUKXSUUDUUNXSUUDUURXSXTWOYCYDYEYNYOUUEUVBWIZYPYNEYLUCUDLYOUYSEY
      FUAABUVACDEUUDUVAYGHIKYHYIYJYKUUDAYMYE $.

    $( Lemma 3 for ~ gpg5nbgrvtx03star .  (Contributed by AV, 5-Sep-2025.) $)
    gpg5nbgrvtx03starlem3 $p |- ( ( N e. ( ZZ>= ` 3 ) /\ K e. J /\ X e. W )
                                 -> { <. 1 , X >. ,
                                      <. 0 , ( ( X - 1 ) mod N ) >. } e/ E ) $=
      ( wcel c1 cc0 wne wa cvv wo pm3.2i vx c3 cuz cfv w3a cop cmin co cmo wnel
      cpr wn cv caddc wceq w3o cfzo wrex wral opex ax-1ne0 a1i wb 1ex simp3 jca
      orcd adantr opthneg syl mpbird orci prneimg mpsyl eleq1 uzuzle23 3ad2ant1
      wi c2 m1modne sylan ex adantl sylbird impr neeq2 mpbid olc pm2.61ine c0ex
      ovex opthne neirr biorfi bitr4i bitr4di orbi12d olcd prneimg2 mp1i neeq1i
      a1d prcom sylibr 0ne1 mpbir 3jca ralrimiva ralnex 3ioran 3anbi123i ralbii
      df-ne bitr3i eqid gpgedgel 3adant3 mtbird df-nel ) EUBUCUDMZDCMZHGMZUEZNH
      UFZOHNUGUHZEUIUHZUFZUKZAMZULYHAUJYCYIYHOUAUMZUFZOYJNUNUHEUIUHZUFZUKZUOZYH
      YKNYJUFZUKZUOZYHYPNYJDUNUHEUIUHZUFZUKZUOZUPZUAOEUQUHZURZYCYHYNPZYHYQPZYHU
      UAPZUEZUAUUDUSZUUEULZYCUUIUAUUDYCYJUUDMZQZUUFUUGUUHYDRMZYGRMZQZYKRMZYMRMZ
      QZQUUMYDYKPZYDYMPZQZYGYKPZYGYMPQZSUUFUUPUUSUUNUUONHUTZOYFUTZTZUUQUUROYJUT
      ZOYLUTTTUUMUVBUVDUUMUUTUVAUUMUUTNOPZHYJPZSZUUMUVIUVJUVIUUMVAVBVGUUMNRMZYB
      QZUUTUVKVCYCUVMUULYCUVLYBUVLYCVDVBXTYAYBVEVFVHZNHOYJRGVIVJVKZUUMUVAUVIHYL
      PZSZUVQUUMUVIUVPVAVLVBUUMUVMUVAUVQVCUVNNHOYLRGVIVJVKVFVGYDYGYKYMRRRRVMVNU
      UMYGYDUKZYQPZUUGUUMUVSUVCYDYPPZSZYGYPPZUUTSZQZUUMUWAUWCUUMUWAYFYJPZUVJSZU
      UMUWFVRHYJHYJUOZUUMUWFUWGUUMQZUWEUVJUWHYFHPZUWEUWGYCUULUWIUWGYCQUULHUUDMZ
      UWIUWGUWJUULVCYCHYJUUDVOVHYCUWJUWIVRUWGYCUWJUWIYCEVSUCUDMZUWJUWIXTYAUWKYB
      EVPVQHEVTWAWBWCWDWEUWGUWIUWEVCUUMHYJYFWFVHWGVGWBUVJUWFUUMUVJUWEWHXBWIUUMU
      VCUWEUVTUVJUVCUWEVCUUMUVCOOPZUWESUWEOYFOYJWJYEEUIWKZWLUWLUWEOWMWNWOVBUUMU
      VTNNPZUVJSZUVJUUMUVMUVTUWOVCUVNNHNYJRGVIVJUWNUVJNWMWNWPWQVKUUMUUTUWBUVOWR
      VFUUOUUNQZUUQYPRMZQZQUVSUWDVCUUMUWPUWRUUOUUNUVFUVETUUQUWQUVHNYJUTZTTYGYDY
      KYPRRRRWSWTVKYHUVRYQYDYGXCXAXDUUPUWQYTRMZQZQUUMUVTYDYTPQZUWBYGYTPZQZSUUHU
      UPUXAUVGUWQUWTUWSNYSUTTTUUMUXDUXBUXDUUMUWBUXCUWBONPZUWESUXEUWEXEVLOYFNYJW
      JUWMWLXFUXCUXEYFYSPZSUXEUXFXEVLOYFNYSWJUWMWLXFTVBWRYDYGYPYTRRRRVMVNXGXHUU
      KUUCULZUAUUDUSUUJUUCUAUUDXIUXGUUIUAUUDUXGYOULZYRULZUUBULZUEUUIYOYRUUBXJUU
      FUXHUUGUXIUUHUXJYHYNXMYHYQXMYHUUAXMXKWOXLXNXDXTYAYIUUEVCYBUAABUUDCDEYHUUD
      XOIJLXPXQXRYHAXSXD $.

    $( Lemma 1 for ~ gpg5nbgr3star .  (Contributed by AV, 7-Sep-2025.) $)
    gpg5nbgrvtx13starlem1 $p |- ( ( ( N = 5 /\ K e. J ) /\ X e. W )
                   -> { <. 1 , ( ( X + K ) mod N ) >. , <. 0 , X >. } e/ E ) $=
      ( c5 wcel wa c1 co cc0 wne cvv vx wceq caddc cmo cop cpr wn wnel w3o cfzo
      cv wrex w3a wral wo opex pm3.2i ax-1ne0 orci 1ex opthne mpbir a1i prneimg
      ovex orcd mpsyl 0ne1 wb c0ex anim1i adantr opthneg syl mpbiri eleq1 oveq2
      wi eleq2d biimpd ad2antrr imp cn ceilhalfelfzo1 sylibd plusmod5ne syl2anc
      olcd 5nn neeq1d mpbird ex adantl sylbird impr neeq2 mpbid pm2.61ine neirr
      olc a1d biorfi bitr4i bitr4di orbi12d prneimg2 mp1i 3jca ralrimiva ralnex
      jca 3ioran 3anbi123i ralbii bitr3i sylibr c3 cuz cfv 5eluz3 eqid gpgedgel
      df-ne sylan mtbird df-nel ) EMUBZDCNZOZHGNZOZPHDUCQZEUDQZUEZRHUEZUFZANZUG
      YPAUHYKYQYPRUAUKZUEZRYRPUCQEUDQZUEZUFZUBZYPYSPYRUEZUFZUBZYPUUDPYRDUCQEUDQ
      ZUEZUFZUBZUIZUAREUJQZULZYKYPUUBSZYPUUESZYPUUISZUMZUAUULUNZUUMUGZYKUUQUAUU
      LYKYRUULNZOZUUNUUOUUPYNTNZYOTNZOZYSTNZUUATNZOZOUVAYNYSSZYNUUASZOZYOYSSZYO
      UUASOZUOUUNUVDUVGUVBUVCPYMUPRHUPUQZUVEUVFRYRUPZRYTUPUQUQUVAUVJUVLUVJUVAUV
      HUVIUVHPRSZYMYRSZUOUVOUVPURUSPYMRYRUTYLEUDVEZVAVBUVIUVOYMYTSZUOUVOUVRURUS
      PYMRYTUTUVQVAVBUQVCVFYNYOYSUUATTTTVDVGUVAUUOUVHYOUUDSZUOZYNUUDSZUVKUOZOZU
      VAUVTUWBUVAUVSUVHUVAUVSRPSZHYRSZUOZUWDUWEVHUSUVARTNZYJOZUVSUWFVIYKUWHUUTY
      IUWGYJUWGYIVJVCVKVLZRHPYRTGVMVNVOZWHUVAUWBUVPUWEUOZUVAUWKVRHYRHYRUBZUVAUW
      KUWLUVAOZUVPUWEUWMYMHSZUVPUWLYKUUTUWNUWLYKOUUTHUULNZUWNUWLUWOUUTVIYKHYRUU
      LVPVLYKUWOUWNVRUWLYKUWOUWNYKUWOOZUWNYLMUDQZHSZUWPHRMUJQZNZDPMUJQZNZUWRYKU
      WOUWTYGUWOUWTVRYHYJYGUWOUWTYGUULUWSHEMRUJVQVSVTWAWBYIUXBYJUWOYGYHUXBYGYHD
      PEUJQZNZUXBYGEWCNZYHUXDVRYGUXEMWCNWIEMWCVPVOCDEIWDVNYGUXCUXADEMPUJVQVSWEW
      BWAHDWFWGYIUWNUWRVIZYJUWOYGUXFYHYGYMUWQHEMYLUDVQWJVLWAWKWLWMWNWOUWLUWNUVP
      VIUVAHYRYMWPVLWQVFWLUWEUWKUVAUWEUVPWTXAWRUVAUWAUVPUVKUWEUWAUVPVIUVAUWAPPS
      ZUVPUOUVPPYMPYRUTUVQVAUXGUVPPWSXBXCVCUVAUVKRRSZUWEUOZUWEUVAUWHUVKUXIVIUWI
      RHRYRTGVMVNUXHUWERWSXBXDXEWKXKUVDUVEUUDTNZOZOUUOUWCVIUVAUVDUXKUVMUVEUXJUV
      NPYRUPZUQUQYNYOYSUUDTTTTXFXGWKUVDUXJUUHTNZOZOUVAUWAYNUUHSOZUVSYOUUHSZOZUO
      UUPUVDUXNUVMUXJUXMUXLPUUGUPUQUQUVAUXQUXOUVAUVSUXPUWJUVAUXPUWDHUUGSZUOZUVA
      UWDUXRUWDUVAVHVCVFUVAUWHUXPUXSVIUWIRHPUUGTGVMVNWKXKWHYNYOUUDUUHTTTTVDVGXH
      XIUUSUUKUGZUAUULUNUURUUKUAUULXJUXTUUQUAUULUXTUUCUGZUUFUGZUUJUGZUMUUQUUCUU
      FUUJXLUUNUYAUUOUYBUUPUYCYPUUBYCYPUUEYCYPUUIYCXMXCXNXOXPYIYQUUMVIZYJYGEXQX
      RXSZNZYHUYDYGUYFMUYENXTEMUYEVPVOUAABUULCDEYPUULYAIJLYBYDVLYEYPAYFXP $.

    $( Lemma 2 for ~ gpg5nbgr3star .  (Contributed by AV, 8-Sep-2025.) $)
    gpg5nbgrvtx13starlem2 $p |- ( ( ( N = 5 /\ K e. J ) /\ X e. ZZ )
                                 -> { <. 1 , ( ( X + K ) mod N ) >. ,
                                      <. 1 , ( ( X - K ) mod N ) >. } e/ E ) $=
      ( c5 wcel wa c1 co cmo wne cvv wo vx wceq cz caddc cop cmin cpr wn cc0 cv
      wnel w3o cfzo wrex w3a wral opex pm3.2i ax-1ne0 orci 1ex opthne mpbir a1i
      ovex orcd prneimg mpsyl olci wb prneimg2 mp1i mpbir2and wi c2 cmul c3 cfv
      cdiv cceil ceil5half3 eqtrdi oveq2d eqtrid eleq2d biimpa minusmodnep2tmod
      fvoveq1 anim1ci syl neeq12d ad2antrr mpbird cc zcn adantl elfzoelz eleq2s
      oveq2 zcnd ad2antlr addassd 2timesd eqcomd eqtrd oveq1d neeqtrrd crp zred
      cr zre readdcld cn 5nn eleq1 mpbiri nnrpd modaddmod ad2antrl oveq1 adantr
      syl3anc neeqtrd olcd ex orc a1d pm2.61ine neirr biorfi bitr4i orbi12d cuz
      cle wbr 2z nnzi 2re df-ne sylibr 5re ltleii eluz2 mpbir3an ceilhalfelfzo1
      2lt5 simpr imp zplusmodne npcan syl2anr resubcld 5rp olc ralrimiva ralnex
      3jca 3ioran 3anbi123i ralbii bitr3i 5eluz3 gpgedgel sylan mtbird df-nel
      eqid ) ELUBZDCMZNZGUCMZNZOGDUDPZEQPZUEZOGDUFPZEQPZUEZUGZAMZUHUVSAUKUVLUVT
      UVSUIUAUJZUEZUIUWAOUDPEQPZUEZUGZUBZUVSUWBOUWAUEZUGZUBZUVSUWGOUWADUDPZEQPZ
      UEZUGZUBZULZUAUIEUMPZUNZUVLUVSUWERZUVSUWHRZUVSUWMRZUOZUAUWPUPZUWQUHZUVLUX
      AUAUWPUVLUWAUWPMZNZUWRUWSUWTUVOSMZUVRSMZNZUWBSMZUWDSMZNZNUXEUVOUWBRZUVOUW
      DRZNZUVRUWBRZUVRUWDRNZTUWRUXHUXKUXFUXGOUVNUQOUVQUQURZUXIUXJUIUWAUQZUIUWCU
      QURURUXEUXNUXPUXNUXEUXLUXMUXLOUIRZUVNUWARZTUXSUXTUSUTOUVNUIUWAVAUVMEQVEZV
      BVCZUXMUXSUVNUWCRZTUXSUYCUSUTOUVNUIUWCVAUYAVBVCURVDVFUVOUVRUWBUWDSSSSVGVH
      UXEUWSUXLUVRUWGRZTZUVOUWGRZUXOTZUYEUXEUXLUYDUYBUTVDUYGUXEUXOUYFUXOUXSUVQU
      WARZTUXSUYHUSUTOUVQUIUWAVAUVPEQVEZVBVCVIVDUXHUXIUWGSMZNZNUWSUYEUYGNVJUXEU
      XHUYKUXQUXIUYJUXROUWAUQZURURUVOUVRUWBUWGSSSSVKVLVMUXEUWTUYFUVRUWLRZTZUVOU
      WLRZUYDTZUXEUYNUXTUVQUWKRZTZUXEUYRVNUVNUWAUVNUWAUBZUXEUYRUYSUXENZUYQUXTUY
      TUVQUVNDUDPZEQPZUWKUVLUVQVUBRUYSUXDUVLUVQUVMDUDPZEQPZVUBUVLUVQGVODVPPZUDP
      ZEQPZVUDUVLUVQVUGRZUVPLQPZVUFLQPZRZUVLUVKDOVQUMPZMZNVUKUVJVUMUVKUVHUVIVUM
      UVHCVULDUVHCOEVOVSPVTVRZUMPZVULHUVHVUNVQOUMUVHVUNLVOVSPVTVRVQELVOVTVSWHWA
      WBWCWDWEWFWIGDWGWJUVHVUHVUKVJUVIUVKUVHUVQVUIVUGVUJELUVPQWSELVUFQWSWKWLWMU
      VLVUCVUFEQUVLVUCGDDUDPZUDPVUFUVLGDDUVKGWNMZUVJGWOZWPUVIDWNMZUVHUVKUVIDDUC
      MDVUOCDOVUNWQZHWRZWTZXAZVVCXBUVLVUPVUEGUDUVLVUEVUPUVLDVVCXCXDWCXEXFXGUVLU
      VMXJMDXJMZEXHMZVUBVUDUBUVLGDUVKGXJMUVJGXKWPZUVIVVDUVHUVKUVIDVVAXIXAZXLVVG
      UVHVVEUVIUVKUVHEUVHEXMMZLXMMXNELXMXOXPZXQWLUVMDEXRYBXGXSUYSVUBUWKUBUXEUYS
      VUAUWJEQUVNUWADUDXTXFYAYCYDYEUXTUYRUXEUXTUYQYFYGYHUXEUYFUXTUYMUYQUYFUXTVJ
      UXEUYFOORZUXTTUXTOUVNOUWAVAUYAVBVVJUXTOYIZYJYKVDUYMUYQVJUXEUYMVVJUYQTUYQO
      UVQOUWKVAUYIVBVVJUYQVVKYJYKVDYLWMUXEUYPUVNUWKRZUYHTZUXEVVMVNUVQUWAUVQUWAU
      BZUXEVVMVVNUXENZVVLUYHVVOUVNUVQDUDPZEQPZUWKUVLUVNVVQRVVNUXDUVLUVNUVPDUDPZ
      EQPZVVQUVLUVNGEQPZVVSUVLEVOYMVRZMZUVKDOEUMPMZUVNVVTRUVHVWBUVIUVKUVHVWBLVW
      AMZVWDVOUCMLUCMVOLYNYOYPLXNYQVOLYRUUAUUFUUBVOLUUCUUDELVWAXOXPWLUVJUVKUUGU
      VJVWCUVKUVHUVIVWCUVHVVHUVIVWCVNVVICDEHUUEWJUUHYAGDEUUIYBUVLVVRGEQUVKVUQVU
      SVVRGUBUVJVURUVIVUSUVHVVBWPGDUUJUUKXFXGUVLUVPXJMVVDVVEVVQVVSUBUVLGDVVFUVI
      VVDUVHUVKVVDDVUOCDVUOMDVUTXIHWRXAZUULVWEUVHVVEUVIUVKUVHVVELXHMUUMELXHXOXP
      WLUVPDEXRYBXGXSVVNVVQUWKUBUXEVVNVVPUWJEQUVQUWADUDXTXFYAYCVFYEUYHVVMUXEUYH
      VVLUUNYGYHUXEUYOVVLUYDUYHUYOVVLVJUXEUYOVVJVVLTVVLOUVNOUWKVAUYAVBVVJVVLVVK
      YJYKVDUYDUYHVJUXEUYDVVJUYHTUYHOUVQOUWAVAUYIVBVVJUYHVVKYJYKVDYLWMUXHUYJUWL
      SMZNZNUWTUYNUYPNVJUXEUXHVWGUXQUYJVWFUYLOUWKUQURURUVOUVRUWGUWLSSSSVKVLVMUU
      QUUOUXCUWOUHZUAUWPUPUXBUWOUAUWPUUPVWHUXAUAUWPVWHUWFUHZUWIUHZUWNUHZUOUXAUW
      FUWIUWNUURUWRVWIUWSVWJUWTVWKUVSUWEYSUVSUWHYSUVSUWMYSUUSYKUUTUVAYTUVJUVTUW
      QVJZUVKUVHEVQYMVRZMZUVIVWLUVHVWNLVWMMUVBELVWMXOXPUAABUWPCDEUVSUWPUVGHIKUV
      CUVDYAUVEUVSAUVFYT $.

    $( Lemma 3 for ~ gpg5nbgr3star .  (Contributed by AV, 8-Sep-2025.) $)
    gpg5nbgrvtx13starlem3 $p |- ( ( ( N = 5 /\ K e. J ) /\ X e. W )
                                 -> { <. 0 , X >. ,
                                      <. 1 , ( ( X - K ) mod N ) >. } e/ E ) $=
      ( c5 wcel wa cc0 c1 wne cvv wo vx wceq cop cmin co cmo cpr wn wnel cv w3o
      caddc cfzo wrex w3a wral opex pm3.2i ax-1ne0 orci 1ex ovex mpbir a1i olcd
      opthne mpsyl wi wb eleq1 adantr simpll oveq2d eleq2d biimpa cn 5nn mpbiri
      prneimg ceilhalfelfzo1 syl sylibd imp ad2antrr minusmod5ne syl2anc neeq1d
      oveq2 mpbird adantl sylbird impr neeq2 mpbid orcd olc a1d pm2.61ine neirr
      ex biorfi bitr4i c0ex anim1i opthneg bitr4di orbi12d orcomd 0ne1 prneimg2
      mp1i 3jca ralrimiva ralnex 3ioran df-ne 3anbi123i ralbii bitr3i sylibr c3
      jca cuz cfv 5eluz3 eqid gpgedgel sylan mtbird df-nel ) EMUBZDCNZOZHGNZOZP
      HUCZQHDUDUEZEUFUEZUCZUGZANZUHYTAUIYOUUAYTPUAUJZUCZPUUBQULUEEUFUEZUCZUGZUB
      ZYTUUCQUUBUCZUGZUBZYTUUHQUUBDULUEEUFUEZUCZUGZUBZUKZUAPEUMUEZUNZYOYTUUFRZY
      TUUIRZYTUUMRZUOZUAUUPUPZUUQUHZYOUVAUAUUPYOUUBUUPNZOZUURUUSUUTYPSNZYSSNZOZ
      UUCSNZUUESNZOZOUVEYPUUCRZYPUUEROZYSUUCRZYSUUERZOZTUURUVHUVKUVFUVGPHUQQYRU
      QURZUVIUVJPUUBUQZPUUDUQURURUVEUVPUVMUVPUVEUVNUVOUVNQPRZYRUUBRZTUVSUVTUSUT
      QYRPUUBVAYQEUFVBZVFVCUVOUVSYRUUDRZTUVSUWBUSUTQYRPUUDVAUWAVFVCURVDVEYPYSUU
      CUUESSSSVSVGUVEUUSUVLYSUUHRZTZYPUUHRZUVNTZOZUVEUWDUWFUVEUWCUVLUVEUWCUVLTU
      VTHUUBRZTZUVEUWIVHHUUBHUUBUBZUVEUWIUWJUVEOZUVTUWHUWKYRHRZUVTUWJYOUVDUWLUW
      JYOOUVDHUUPNZUWLUWJUWMUVDVIYOHUUBUUPVJVKYOUWMUWLVHUWJYOUWMUWLYOUWMOZUWLYQ
      MUFUEZHRZUWNHPMUMUEZNZDQMUMUEZNZUWPYOUWMUWRYOUUPUWQHYOEMPUMYKYLYNVLVMVNVO
      YMUWTYNUWMYKYLUWTYKYLDQEUMUEZNZUWTYKEVPNZYLUXBVHYKUXCMVPNVQEMVPVJVRCDEIVT
      WAYKUXAUWSDEMQUMWHVNWBWCWDHDWEWFYMUWLUWPVIZYNUWMYKUXDYLYKYRUWOHEMYQUFWHWG
      VKWDWIWTWJWKWLUWJUWLUVTVIUVEHUUBYRWMVKWNWOWTUWHUWIUVEUWHUVTWPWQWRUVEUWCUV
      TUVLUWHUWCUVTVIUVEUWCQQRZUVTTUVTQYRQUUBVAUWAVFUXEUVTQWSXAXBVDUVEUVLPPRZUW
      HTZUWHUVEPSNZYNOZUVLUXGVIYOUXIUVDYMUXHYNUXHYMXCVDXDVKZPHPUUBSGXEWAUXFUWHP
      WSXAXFXGWIXHUVEUWEUVNUVEUWEPQRZUWHTZUXKUWHXIUTUVEUXIUWEUXLVIUXJPHQUUBSGXE
      WAVRZWOYBUVHUVIUUHSNZOZOUUSUWGVIUVEUVHUXOUVQUVIUXNUVRQUUBUQZURURYPYSUUCUU
      HSSSSXJXKWIUVHUXNUULSNZOZOUVEUWEYPUULRZOZUWCYSUULROZTUUTUVHUXRUVQUXNUXQUX
      PQUUKUQURURUVEUXTUYAUVEUWEUXSUXMUVEUXSUXKHUUKRZTZUXKUYBXIUTUVEUXIUXSUYCVI
      UXJPHQUUKSGXEWAVRYBWOYPYSUUHUULSSSSVSVGXLXMUVCUUOUHZUAUUPUPUVBUUOUAUUPXNU
      YDUVAUAUUPUYDUUGUHZUUJUHZUUNUHZUOUVAUUGUUJUUNXOUURUYEUUSUYFUUTUYGYTUUFXPY
      TUUIXPYTUUMXPXQXBXRXSXTYMUUAUUQVIZYNYKEYAYCYDZNZYLUYHYKUYJMUYINYEEMUYIVJV
      RUAABUUPCDEYTUUPYFIJLYGYHVKYIYTAYJXT $.
  $}

  ${
    $d G v y $.  $d J v $.  $d K v $.  $d N v $.  $d V v y $.  $d X v y $.
    gpgnbgr.j $e |- J = ( 1 ..^ ( |^ ` ( N / 2 ) ) ) $.
    gpgnbgr.g $e |- G = ( N gPetersenGr K ) $.
    gpgnbgr.v $e |- V = ( Vtx ` G ) $.
    gpgnbgr.u $e |- U = ( G NeighbVtx X ) $.
    $( The (open) neighborhood of an outside vertex in a generalized Petersen
       graph ` G ` .  (Contributed by AV, 28-Aug-2025.) $)
    gpgnbgrvtx0 $p |- ( ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
                          /\ ( X e. V /\ ( 1st ` X ) = 0 ) )
                        -> U = { <. 0 , ( ( ( 2nd ` X ) + 1 ) mod N ) >. ,
                                 <. 1 , ( 2nd ` X ) >. ,
                                 <. 0 , ( ( ( 2nd ` X ) - 1 ) mod N ) >. } ) $=
      ( vy cfv wcel wa wceq co cpr c1 cop vv c3 cuz c1st cc0 cnbgr cv cedg crab
      c2nd caddc cmo cmin ctp a1i cusgr cgpg c2 cdiv cceil cfzo eleq2i gpgusgra
      sylan2b eqeltrid simpl nbusgrvtx syl2an simpr adantl gpgvtxedg0 syl2an3an
      eqid w3o gpgvtx0 simp1d adantrr gpgedgvtx0 jca eleq1 preq2 eleq1d anbi12d
      ex syl5ibrcom gpgvtx1 simp2d simp3d adantr wb mpbird 3jaod impbid weq vex
      elrab eltp 3bitr4g eqrdv 3eqtrd ) EUBUCMNZDCNZOZGFNZGUDMUEPZOZOZABGUFQZGL
      UGZRZBUHMZNZLFUIZUEGUJMZSUKQEULQTZSXNTZUEXNSUMQEULQTZUNZAXHPXGKUOXCBUPNXD
      XHXMPXFXCBEDUQQZUPIXBXADSEURUSQUTMVAQZNXSUPNCXTDHVBDEVCVDVEXDXEVFLXKBGFJX
      KVMZVGVHXGUAXMXRXGUAUGZFNZGYBRZXKNZOZYBXOPZYBXPPZYBXQPZVNZYBXMNYBXRNXGYFY
      JXGYFYJXGXCXEYFYEYJXCXFVFXFXEXCXDXEVIVJYCYEVIXKBCDEFGYBHIJYAVKVLWDXGYGYFY
      HYIXGYFYGXOFNZGXORZXKNZOXGYKYMXCXDYKXEXCXDOZYKUEXNTFNZXQFNZBCDEFGHIJVOZVP
      VQXGYMGXPRZXKNZGXQRZXKNZXKBCDEFGHIJYAVRZVPVSYGYCYKYEYMYBXOFVTYGYDYLXKYBXO
      GWAWBWCWEXGYFYHXPFNZYSOXGUUCYSXCXDUUCXEYNSXNDUKQEULQTFNUUCSXNDUMQEULQTFNB
      CDEFGHIJWFWGVQXGYMYSUUAUUBWGVSYHYCUUCYEYSYBXPFVTYHYDYRXKYBXPGWAWBWCWEXGYI
      YFXGYIOZYCYEUUDYCYPXGYPYIXCXDYPXEYNYKYOYPYQWHVQWIYIYCYPWJXGYBXQFVTVJWKUUD
      YEUUAXGUUAYIXGYMYSUUAUUBWHWIYIYEUUAWJXGYIYDYTXKYBXQGWAWBVJWKVSWDWLWMXLYEL
      YBFLUAWNXJYDXKXIYBGWAWBWPYBXOXPXQUAWOWQWRWSWT $.

    $( The (open) neighborhood of an inside vertex in a generalized Petersen
       graph ` G ` .  (Contributed by AV, 2-Sep-2025.) $)
    gpgnbgrvtx1 $p |- ( ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
                          /\ ( X e. V /\ ( 1st ` X ) = 1 ) )
                        -> U = { <. 1 , ( ( ( 2nd ` X ) + K ) mod N ) >. ,
                                 <. 0 , ( 2nd ` X ) >. ,
                                 <. 1 , ( ( ( 2nd ` X ) - K ) mod N ) >. } ) $=
      ( vy cfv wcel wa c1 wceq co cpr cop vv c3 c1st cnbgr cedg crab c2nd caddc
      cuz cv cmo cc0 cmin ctp a1i cusgr cgpg c2 cdiv cceil cfzo eleq2i gpgusgra
      sylan2b eqeltrid simpl nbusgrvtx syl2an simpr adantl gpgvtxedg1 syl2an3an
      eqid w3o gpgvtx1 simp1d adantrr gpgedgvtx1 jca eleq1 preq2 eleq1d anbi12d
      ex syl5ibrcom gpgvtx0 simp2d simp3d adantr mpbird 3jaod impbid elrab eltp
      wb vex 3bitr4g eqrdv 3eqtrd ) EUBUIMNZDCNZOZGFNZGUCMPQZOZOZABGUDRZGLUJZSZ
      BUEMZNZLFUFZPGUGMZDUHREUKRTZULXMTZPXMDUMREUKRTZUNZAXGQXFKUOXBBUPNXCXGXLQX
      EXBBEDUQRZUPIXAWTDPEURUSRUTMVARZNXRUPNCXSDHVBDEVCVDVEXCXDVFLXJBGFJXJVMZVG
      VHXFUAXLXQXFUAUJZFNZGYASZXJNZOZYAXNQZYAXOQZYAXPQZVNZYAXLNYAXQNXFYEYIXFYEY
      IXFXBXDYEYDYIXBXEVFXEXDXBXCXDVIVJYBYDVIXJBCDEFGYAHIJXTVKVLWDXFYFYEYGYHXFY
      EYFXNFNZGXNSZXJNZOXFYJYLXBXCYJXDXBXCOZYJPXMTFNZXPFNZBCDEFGHIJVOZVPVQXFYLG
      XOSZXJNZGXPSZXJNZXJBCDEFGHIJXTVRZVPVSYFYBYJYDYLYAXNFVTYFYCYKXJYAXNGWAWBWC
      WEXFYEYGXOFNZYROXFUUBYRXBXCUUBXDYMULXMPUHREUKRTFNUUBULXMPUMREUKRTFNBCDEFG
      HIJWFWGVQXFYLYRYTUUAWGVSYGYBUUBYDYRYAXOFVTYGYCYQXJYAXOGWAWBWCWEXFYHYEXFYH
      OZYBYDUUCYBYOXFYOYHXBXCYOXDYMYJYNYOYPWHVQWIYHYBYOWOXFYAXPFVTVJWJUUCYDYTXF
      YTYHXFYLYRYTUUAWHWIYHYDYTWOXFYHYCYSXJYAXPGWAWBVJWJVSWDWKWLXKYDLYAFXHYAQXI
      YCXJXHYAGWAWBWMYAXNXOXPUAWPWNWQWRWS $.

    $( In a generalized Petersen graph ` G ` , every outside vertex has exactly
       three (different) neighbors.  (Contributed by AV, 30-Aug-2025.) $)
    gpg3nbgrvtx0 $p |- ( ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
                       /\ ( X e. V /\ ( 1st ` X ) = 0 ) ) -> ( # ` U ) = 3 ) $=
      ( c3 wcel cc0 c1 co cmo wne a1i c2 cuz cfv c1st wceq chash c2nd caddc cop
      cmin ctp gpgnbgrvtx0 fveq2d w3a 0ne1 orcd c0ex ovex opthne sylibr ax-1ne0
      wa wo 1ex fvex cfzo cz anim2i eqid gpgvtxel2 elfzoelz 3syl zcnd 1cnd 2cnd
      simpl subadd23d 2m1e1 oveq2d eqtrd eqcomd oveq1d cr crp 1zzd zsubcld zred
      2re eluz3nn nnrpd ad2antrr modaddabs syl3anc cn cn0 clt wbr zmodcld modlt
      syl2anc jca 2nn0 cle eluz2 3re zre adantr 2lt3 simpr ltletrd sylbi elfzo0
      3adant1 syl3anbrc zmodidfzoimp syl 2nn eqeltrdi addmodne necomd olcd 3jca
      eqnetrd cvv wb opex hashtpg mp3an sylib ) ELUAUBMZDCMZVAZGFMZGUCUBNUDZVAZ
      VAZAUEUBNGUFUBZOUGPZEQPZUHZOYPUHZNYPOUIPZEQPZUHZUJZUEUBZLYOAUUDUEABCDEFGH
      IJKUKULYOYSYTRZYTUUCRZUUCYSRZUMZUUELUDZYOUUFUUGUUHYONORZYRYPRZVBUUFYOUUKU
      ULUUKYOUNSUONYROYPUPYQEQUQURUSYOONRZYPUUBRZVBUUGYOUUMUUNUUMYOUTSUOOYPNUUB
      VCGUFVDURUSYONNRZUUBYRRZVBUUHYOUUPUUOYOYRUUBYOYRUUBTEQPZUGPEQPZUUBYOYRUUA
      TUGPZEQPZUURYOYQUUSEQYOUUSYQYOUUSYPTOUIPZUGPYQYOYPOTYOYPYOYKYLVAYPNEVEPZM
      YPVFMYNYLYKYLYMVOVGBUVBCDEFGUVBVHHIJVIYPNEVJVKZVLYOVMYOVNVPYOUVAOYPUGUVAO
      UDYOVQSVRVSVTWAYOUURUUTYOUUAWBMZTWBMZEWCMZUURUUTUDYOUUAYOYPOUVCYOWDWEZWFZ
      UVEYOWGSYIUVFYJYNYIEEWHZWIZWJZUUATEWKWLVTVSYOEWMMZUUBWNMZUUBEWOWPZVAUUQWM
      MZUUQEWOWPZVAZUURUUBRYIUVLYJYNUVIWJZYOUVMUVNYOUUAEUVGUVRWQYOUVDUVFUVNUVHU
      VKUUAEWRWSWTYIUVQYJYNYIUVOUVPYIUUQTWMYITUVBMZUUQTUDYITWNMZUVLTEWOWPZUVSUV
      TYIXASUVIYILVFMZEVFMZLEXBWPZUMUWALEXCUWCUWDUWAUWBUWCUWDVAZTLEUVEUWEWGSLWB
      MUWEXDSUWCEWBMUWDEXEXFTLWOWPUWEXGSUWCUWDXHXIXLXJTEXKXMTEXNXOXPXQYIUVEUVFU
      VPUVEYIWGSUVJTEWRWSWTWJUUBUUQEXRWLYBXSXTNUUBNYRUPUUAEQUQURUSYAYSYCMYTYCMU
      UCYCMUUIUUJYDNYRYEOYPYENUUBYEYSYTUUCYCYCYCYFYGYHVS $.

    $( In a generalized Petersen graph ` G ` , every outside vertex has exactly
       three (different) neighbors.  (Contributed by AV, 30-Aug-2025.)

       The proof of ~ gpg3nbgrvtx0 can be shortened using ~ modmknepk , but
       then theorem ~ 2ltceilhalf is required which is based on an "example"
       ~ ex-ceil .  If these theorems were moved to main, the "example" should
       also be moved up to become a full-fledged theorem.  (Proof shortened by
       AV, 4-Sep-2025.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    gpg3nbgrvtx0ALT $p |- ( ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
                       /\ ( X e. V /\ ( 1st ` X ) = 0 ) ) -> ( # ` U ) = 3 ) $=
      ( c3 cfv wcel cc0 c1 co wne c2 cvv cuz c1st wceq chash c2nd caddc cmo cop
      wa cmin ctp gpgnbgrvtx0 fveq2d w3a 0ne1 a1i orcd c0ex ovex opthne ax-1ne0
      wo sylibr 1ex fvex cfzo cdiv cceil simpll gpgvtxel2 adantrr cz cle wbr 2z
      eluzelre rehalfcld ceilcld 2ltceilhalf eluz2 syl3anbrc ad2antrr modmknepk
      eqid fzo1lb syl3anc olcd 3jca wb opex hashtpg mp3an sylib eqtrd ) ELUAMNZ
      DCNZUIZGFNZGUBMOUCZUIZUIZAUDMOGUEMZPUFQZEUGQZUHZPXBUHZOXBPUJQZEUGQZUHZUKZ
      UDMZLXAAXJUDABCDEFGHIJKULUMXAXEXFRZXFXIRZXIXERZUNZXKLUCZXAXLXMXNXAOPRZXDX
      BRZVBXLXAXQXRXQXAUOUPUQOXDPXBURXCEUGUSUTVCXAPORZXBXHRZVBXMXAXSXTXSXAVAUPU
      QPXBOXHVDGUEVEUTVCXAOORZXHXDRZVBXNXAYBYAXAWOXBOEVFQZNZPPESVGQZVHMZVFQZNZY
      BWOWPWTVIWQWRYDWSBYCCDEFGYCWDZHIJVJVKWOYHWPWTWOYFSUAMNZYHWOSVLNZYFVLNSYFV
      MVNYJYKWOVOUPWOYEWOELEVPVQVREVSSYFVTWAYFWEVCWBYCYGPEXBYGWDYIWCWFWGOXHOXDU
      RXGEUGUSUTVCWHXETNXFTNXITNXOXPWIOXDWJPXBWJOXHWJXEXFXITTTWKWLWMWN $.

    $( In a generalized Petersen graph ` G ` , every inside vertex has exactly
       three (different) neighbors.  (Contributed by AV, 3-Sep-2025.)  (Proof
       shortened by AV, 22-Nov-2025.) $)
    gpg3nbgrvtx1 $p |- ( ( ( N e. ( ZZ>= ` 3 ) /\ K e. J )
                       /\ ( X e. V /\ ( 1st ` X ) = 1 ) ) -> ( # ` U ) = 3 ) $=
      ( c3 cfv wcel c1 co cmo cc0 wne cvv cuz wa c1st wceq chash c2nd caddc cop
      cmin ctp gpgnbgrvtx1 fveq2d w3a wo ax-1ne0 a1i orcd ovex opthne 0ne1 c0ex
      1ex sylibr fvex cfzo simpll eqid gpgvtxel2 adantrr modmknepk syl3anc olcd
      simplr 3jca wb opex hashtpg mp3an sylib eqtrd ) ELUAMNZDCNZUBZGFNZGUCMOUD
      ZUBZUBZAUEMOGUFMZDUGPZEQPZUHZRWHUHZOWHDUIPZEQPZUHZUJZUEMZLWGAWPUEABCDEFGH
      IJKUKULWGWKWLSZWLWOSZWOWKSZUMZWQLUDZWGWRWSWTWGORSZWJWHSZUNWRWGXCXDXCWGUOU
      PUQOWJRWHVBWIEQURUSVCWGROSZWHWNSZUNWSWGXEXFXEWGUTUPUQRWHOWNVAGUFVDUSVCWGO
      OSZWNWJSZUNWTWGXHXGWGWAWHREVEPZNZWBXHWAWBWFVFWCWDXJWEBXICDEFGXIVGZHIJVHVI
      WAWBWFVMXICDEWHHXKVJVKVLOWNOWJVBWMEQURUSVCVNWKTNWLTNWOTNXAXBVOOWJVPRWHVPO
      WNVPWKWLWOTTTVQVRVSVT $.

    $d J x y $.  $d K x y $.  $d N x y $.  $d U x y $.  $d V x $.  $d X x $.
    $( Every generalized Petersen graph is a _cubic_ graph, i.e., it is a
       3-regular graph, i.e., every vertex has degree 3 (see ~ gpgvtxdg3 ),
       i.e., every vertex has exactly three (different) neighbors.
       (Contributed by AV, 3-Sep-2025.) $)
    gpgcubic $p |- ( ( N e. ( ZZ>= ` 3 ) /\ K e. J /\ X e. V )
                     -> ( # ` U ) = 3 ) $=
      ( vx vy cfv wcel cop wceq cc0 c1 wi c3 cuz w3a cv cfzo co wrex chash eqid
      cpr gpgvtxel biimp3a wa wo elpri opeq1 eqeq2d adantr c1st c0ex vex op1std
      wb gpg3nbgrvtx0 exp43 3imp syl5 adantl sylbid ex gpg3nbgrvtx1 jaoi impcom
      1ex syl a1d expimpd rexlimdvv mpd ) EUAUBNOZDCOZGFOZUCZGLUDZMUDZPZQZMREUE
      UFZUGLRSUJZUGZAUHNUAQZVTWAWBWJLMBWHCDEFGWHUIHIJUKULWCWGWKLMWIWHWCWDWIOZWE
      WHOZWGWKTZWCWLUMWNWMWLWCWNWLWDRQZWDSQZUNWCWNTZWDRSUOWOWQWPWOWCWNWOWCUMWGG
      RWEPZQZWKWOWGWSVCWCWOWFWRGWDRWEUPUQURWCWSWKTWOWSGUSNZRQZWCWKRWEGUTMVAZVBV
      TWAWBXAWKTVTWAWBXAWKABCDEFGHIJKVDVEVFVGVHVIVJWPWCWNWPWCUMWGGSWEPZQZWKWPWG
      XDVCWCWPWFXCGWDSWEUPUQURWCXDWKTWPXDWTSQZWCWKSWEGVNXBVBVTWAWBXEWKTVTWAWBXE
      WKABCDEFGHIJKVKVEVFVGVHVIVJVLVOVMVPVQVRVS $.

    $d E x y $.
    gpgnbgr.e $e |- E = ( Edg ` G ) $.
    $( In a generalized Petersen graph G(N,K) of order greater than 8
       ( ` 3 < N ` ), every outside vertex has exactly three (different)
       neighbors, and none of these neighbors are connected by an edge (i.e.,
       the (closed) neighborhood of every outside vertex induces a subgraph
       which is isomorphic to a 3-star).  (Contributed by AV, 31-Aug-2025.) $)
    gpg5nbgrvtx03star $p |- ( ( ( N e. ( ZZ>= ` 4 ) /\ K e. J )
                                /\ ( X e. V /\ ( 1st ` X ) = 0 ) )
                -> ( ( # ` U ) = 3 /\ A. x e. U A. y e. U { x , y } e/ E ) ) $=
      ( wceq cpr syl wb neleq1 c4 cuz cfv wcel wa c1st cc0 chash c3 cv uzuzle34
      wnel wral gpg3nbgrvtx0 sylanl1 c2nd c1 caddc co cmo cop cmin ctp wn cusgr
      eqid wi c2 cdiv cceil cfzo eleq2i biimpi cgpg gpgusgra eqeltrid usgredgne
      syl2an adantr neneqd ex mt2i df-nel sylibr simplr simpl anim12i gpgvtxel2
      anim1i gpg5nbgrvtx03starlem1 syl3anc cz simpll 3syl gpg5nbgrvtx03starlem2
      elfzoelz opex preq2 raltp prcom ax-mp gpg5nbgrvtx03starlem3 preq1 ralbidv
      syl3anbrc gpgnbgrvtx0 raleqdv raleqbidvv mpbird jca ) HUAUBUCUDZGFUDZUEZJ
      IUDZJUFUCUGPZUEZUEZCUHUCUIPZAUJZBUJZQZDULZBCUMZACUMZXKHUIUBUCUDZXLXPXRHUK
      ZCEFGHIJKLMNUNUOXQYDYBBUGJUPUCZUQURUSHUTUSZVAZUQYGVAZUGYGUQVBUSHUTUSZVAZV
      CZUMZAYMUMZXQYIXTQZDULZBYMUMZYJXTQZDULZBYMUMZYLXTQZDULZBYMUMZYOXQYIYIQZDU
      LZYIYJQZDULZYIYLQZDULZYRXQUUEDUDZVDUUFXQUUKYIYIPZYIVFXQEVEUDZUUKUULVDZVGX
      MUUMXPXKYEGUQHVHVIUSVJUCVKUSZUDZUUMXLYFXLUUPFUUOGKVLVMYEUUPUEEHGVNUSVELGH
      VOVPVRVSZUUMUUKUUNUUMUUKUEYIYIDEYIYIOVQVTWARWBUUEDWCWDXQYEXLYGUGHVKUSZUDZ
      UUHXMYEXPXKYEXLYFVSVSZXKXLXPWEZXQYEXLUEZXNUEZUUSXMUVBXPXNXKYEXLYFWIXNXOWF
      WGZEUURFGHIJUURVFKLMWHZRZDEFGHIUURYGKLMOWJWKZXQXKXLYGWLUDZUUJXKXLXPWMUVAX
      QUVCUUSUVHUVDUVEYGUGHWPWNDEFGHIYGKLMOWOWKZYQUUFUUHUUJBYIYJYLUGYHWQZUQYGWQ
      ZUGYKWQZXTYIPZYPUUEPYQUUFSXTYIYIWRYPUUEDTRXTYJPZYPUUGPYQUUHSXTYJYIWRYPUUG
      DTRXTYLPZYPUUIPYQUUJSXTYLYIWRYPUUIDTRWSXEXQYJYIQZDULZYJYJQZDULZYJYLQZDULZ
      UUAXQUUHUVQUVGUVPUUGPUVQUUHSYJYIWTUVPUUGDTXAWDXQUVRDUDZVDUVSXQUWBYJYJPZYJ
      VFXQUUMUWBUWCVDZVGUUQUUMUWBUWDUUMUWBUEYJYJDEYJYJOVQVTWARWBUVRDWCWDXQYEXLU
      USUWAUUTUVAUVFDEFGHIUURYGKLMOXBWKZYTUVQUVSUWABYIYJYLUVJUVKUVLUVMYSUVPPYTU
      VQSXTYIYJWRYSUVPDTRUVNYSUVRPYTUVSSXTYJYJWRYSUVRDTRUVOYSUVTPYTUWASXTYLYJWR
      YSUVTDTRWSXEXQYLYIQZDULZYLYJQZDULZYLYLQZDULZUUDXQUUJUWGUVIUWFUUIPUWGUUJSY
      LYIWTUWFUUIDTXAWDXQUWAUWIUWEUWHUVTPUWIUWASYLYJWTUWHUVTDTXAWDXQUWJDUDZVDUW
      KXQUWLYLYLPZYLVFXQUUMUWLUWMVDZVGUUQUUMUWLUWNUUMUWLUEYLYLDEYLYLOVQVTWARWBU
      WJDWCWDUUCUWGUWIUWKBYIYJYLUVJUVKUVLUVMUUBUWFPUUCUWGSXTYIYLWRUUBUWFDTRUVNU
      UBUWHPUUCUWISXTYJYLWRUUBUWHDTRUVOUUBUWJPUUCUWKSXTYLYLWRUUBUWJDTRWSXEYNYRU
      UAUUDAYIYJYLUVJUVKUVLXSYIPZYBYQBYMUWOYAYPPYBYQSXSYIXTXCYAYPDTRXDXSYJPZYBY
      TBYMUWPYAYSPYBYTSXSYJXTXCYAYSDTRXDXSYLPZYBUUCBYMUWQYAUUBPYBUUCSXSYLXTXCYA
      UUBDTRXDWSXEXQYCYNACYMXKYEXLXPCYMPYFCEFGHIJKLMNXFUOZXQYBBCYMUWRXGXHXIXJ
      $.

    $d E a b x y $.  $d J a b $.  $d K a b $.  $d N a b $.  $d U a b $.
    $d V a b $.  $d X a b $.
    $( In a generalized Petersen graph G(N,K) of order 10 ( ` N = 5 ` ), these
       are the Petersen graph G(5,2) and the 5-prism G(5,1), every vertex has
       exactly three (different) neighbors, and none of these neighbors are
       connected by an edge (i.e., the (closed) neighborhood of every vertex
       induces a subgraph which is isomorphic to a 3-star).  This does not hold
       for every generalized Petersen graph: for example, in the 3-prism G(3,1)
       (see gpg31grim3prism TODO) and the D&uuml;rer graph G(6,2) there are
       vertices which have neighborhoods containing triangles.  In general, all
       generalized Petersen graphs G(N,K) with ` N = 3 x. K ` contain
       triangles, see ~ gpg3kgrtriex .  (Contributed by AV, 8-Sep-2025.) $)
    gpg5nbgr3star $p |- ( ( N = 5 /\ K e. J /\ X e. V )
                -> ( ( # ` U ) = 3 /\ A. x e. U A. y e. U { x , y } e/ E ) ) $=
      ( wceq wcel wb syl neleq1 va vb c5 w3a cv cop cc0 cfzo co wrex c1 cpr cfv
      chash c3 wnel wral wa 5eluz3 eleq1 mpbiri anim1i eqid gpgvtxel biimp3a wi
      cuz wo elpri opeq1 eqeq2d adantr c1st c0ex vex op1std c4 cle wbr 5nn nnzi
      cz 4z 4re 4lt5 ltleii eluz2 mpbir3an gpg5nbgrvtx03star sylanl1 exp43 3imp
      5re syl5 adantl sylbid ex 1ex gpg3nbgrvtx1 c2nd caddc cmo ctp wn cusgr c2
      cmin cdiv cceil eleq2i biimpi cgpg gpgusgra eqeltrid syl2an neneqd df-nel
      usgredgne sylibr cvv fvexd gpg5nbgrvtx13starlem1 sylan2 anim12i gpgvtxel2
      mt2i simpl elfzoelz 3syl gpg5nbgrvtx13starlem2 opex preq2 raltp syl3anbrc
      syldan prcom ax-mp gpg5nbgrvtx13starlem3 preq1 ralbidv gpgnbgrvtx1 mpbird
      raleqdv raleqbidv jca jaoi impcom a1d expimpd rexlimdvv mpd ) HUCPZGFQZJI
      QZUDZJUAUEZUBUEZUFZPZUBUGHUHUIZUJUAUGUKULZUJZCUNUMUOPZAUEZBUEZULZDUPZBCUQ
      ZACUQZURZUULUUMUUNUVBUULUUMURZHUOVGUMZQZUUMURZUUNUVBRUULUVMUUMUULUVMUCUVL
      QUSHUCUVLUTVAZVBZUAUBEUUTFGHIJUUTVCZKLMVDSVEUUOUUSUVJUAUBUVAUUTUUOUUPUVAQ
      ZUUQUUTQZUUSUVJVFZUUOUVRURUVTUVSUVRUUOUVTUVRUUPUGPZUUPUKPZVHUUOUVTVFZUUPU
      GUKVIUWAUWCUWBUWAUUOUVTUWAUUOURUUSJUGUUQUFZPZUVJUWAUUSUWERUUOUWAUURUWDJUU
      PUGUUQVJVKVLUUOUWEUVJVFUWAUWEJVMUMZUGPZUUOUVJUGUUQJVNUBVOZVPUULUUMUUNUWGU
      VJVFUULUUMUUNUWGUVJUULHVQVGUMZQZUUMUUNUWGURUVJUULUWJUCUWIQZUWKVQWBQUCWBQV
      QUCVRVSWCUCVTWAVQUCWDWMWEWFVQUCWGWHHUCUWIUTVAABCDEFGHIJKLMNOWIWJWKWLWNWOW
      PWQUWBUUOUVTUWBUUOURUUSJUKUUQUFZPZUVJUWBUUSUWMRUUOUWBUURUWLJUUPUKUUQVJVKV
      LUUOUWMUVJVFUWBUWMUWFUKPZUUOUVJUKUUQJWRUWHVPUULUUMUUNUWNUVJVFUULUUMUUNUWN
      UVJUVKUUNUWNURZURZUVCUVIUULUVMUUMUWOUVCUVOCEFGHIJKLMNWSWJUWPUVIUVGBUKJWTU
      MZGXAUIHXBUIZUFZUGUWQUFZUKUWQGXGUIHXBUIZUFZXCZUQZAUXCUQZUWPUWSUVEULZDUPZB
      UXCUQZUWTUVEULZDUPZBUXCUQZUXBUVEULZDUPZBUXCUQZUXEUWPUWSUWSULZDUPZUWSUWTUL
      ZDUPZUWSUXBULZDUPZUXHUWPUXODQZXDUXPUWPUYAUWSUWSPZUWSVCUWPEXEQZUYAUYBXDZVF
      UVKUYCUWOUULUVMGUKHXFXHUIXIUMUHUIZQZUYCUUMUVOUUMUYFFUYEGKXJXKUVMUYFUREHGX
      LUIXELGHXMXNXOVLZUYCUYAUYDUYCUYAURUWSUWSDEUWSUWSOXRXPWQSYFUXODXQXSUWOUVKU
      WQXTQZUXRUWOJWTYAZDEFGHIXTUWQKLMOYBYCZUVKUWOUWQWBQZUXTUWPUVNUUNURUWQUUTQU
      YKUVKUVNUWOUUNUVPUUNUWNYGYDEUUTFGHIJUVQKLMYEUWQUGHYHYIDEFGHIUWQKLMOYJYOZU
      XGUXPUXRUXTBUWSUWTUXBUKUWRYKZUGUWQYKZUKUXAYKZUVEUWSPZUXFUXOPUXGUXPRUVEUWS
      UWSYLUXFUXODTSUVEUWTPZUXFUXQPUXGUXRRUVEUWTUWSYLUXFUXQDTSUVEUXBPZUXFUXSPUX
      GUXTRUVEUXBUWSYLUXFUXSDTSYMYNUWPUWTUWSULZDUPZUWTUWTULZDUPZUWTUXBULZDUPZUX
      KUWPUXRUYTUYJUYSUXQPUYTUXRRUWTUWSYPUYSUXQDTYQXSUWPVUADQZXDVUBUWPVUEUWTUWT
      PZUWTVCUWPUYCVUEVUFXDZVFUYGUYCVUEVUGUYCVUEURUWTUWTDEUWTUWTOXRXPWQSYFVUADX
      QXSUWOUVKUYHVUDUYIDEFGHIXTUWQKLMOYRYCZUXJUYTVUBVUDBUWSUWTUXBUYMUYNUYOUYPU
      XIUYSPUXJUYTRUVEUWSUWTYLUXIUYSDTSUYQUXIVUAPUXJVUBRUVEUWTUWTYLUXIVUADTSUYR
      UXIVUCPUXJVUDRUVEUXBUWTYLUXIVUCDTSYMYNUWPUXBUWSULZDUPZUXBUWTULZDUPZUXBUXB
      ULZDUPZUXNUWPUXTVUJUYLVUIUXSPVUJUXTRUXBUWSYPVUIUXSDTYQXSUWPVUDVULVUHVUKVU
      CPVULVUDRUXBUWTYPVUKVUCDTYQXSUWPVUMDQZXDVUNUWPVUOUXBUXBPZUXBVCUWPUYCVUOVU
      PXDZVFUYGUYCVUOVUQUYCVUOURUXBUXBDEUXBUXBOXRXPWQSYFVUMDXQXSUXMVUJVULVUNBUW
      SUWTUXBUYMUYNUYOUYPUXLVUIPUXMVUJRUVEUWSUXBYLUXLVUIDTSUYQUXLVUKPUXMVULRUVE
      UWTUXBYLUXLVUKDTSUYRUXLVUMPUXMVUNRUVEUXBUXBYLUXLVUMDTSYMYNUXDUXHUXKUXNAUW
      SUWTUXBUYMUYNUYOUVDUWSPZUVGUXGBUXCVURUVFUXFPUVGUXGRUVDUWSUVEYSUVFUXFDTSYT
      UVDUWTPZUVGUXJBUXCVUSUVFUXIPUVGUXJRUVDUWTUVEYSUVFUXIDTSYTUVDUXBPZUVGUXMBU
      XCVUTUVFUXLPUVGUXMRUVDUXBUVEYSUVFUXLDTSYTYMYNUWPUVHUXDACUXCUULUVMUUMUWOCU
      XCPUVOCEFGHIJKLMNUUAWJZUWPUVGBCUXCVVAUUCUUDUUBUUEWKWLWNWOWPWQUUFSUUGUUHUU
      IUUJUUK $.
  $}

  ${
    gpgvtxdg3.j $e |- J = ( 1 ..^ ( |^ ` ( N / 2 ) ) ) $.
    gpgvtxdg3.g $e |- G = ( N gPetersenGr K ) $.
    gpgvtxdg3.v $e |- V = ( Vtx ` G ) $.
    $( Every vertex in a generalized Petersen graph has degree 3.  (Contributed
       by AV, 4-Sep-2025.) $)
    gpgvtxdg3 $p |- ( ( N e. ( ZZ>= ` 3 ) /\ K e. J /\ X e. V )
                      -> ( ( VtxDeg ` G ) ` X ) = 3 ) $=
      ( c3 cuz cfv wcel w3a cvtxdg cnbgr co chash cusgr wa wceq cgpg c1 c2 cdiv
      cceil cfzo eleq2i biimpi 3adant3 gpgusgra syl eqeltrid simp3 hashnbusgrvd
      anim2i eqcomd syl2anc eqid gpgcubic eqtrd ) DJKLMZCBMZFEMZNZFAOLLZAFPQZRL
      ZJVEASMZVDVFVHUAVEADCUBQZSHVEVBCUCDUDUEQUFLUGQZMZTZVJSMVBVCVMVDVCVLVBVCVL
      BVKCGUHUIUPUJCDUKULUMVBVCVDUNVIVDTVHVFFAEIUOUQURVGABCDEFGHIVGUSUTVA $.
  $}

  $( Lemma 1 for ~ gpg3kgrtriex .  (Contributed by AV, 1-Oct-2025.) $)
  gpg3kgrtriexlem1 $p |- ( K e. NN -> K < ( |^ ` ( ( 3 x. K ) / 2 ) ) ) $=
    ( cn wcel c3 cmul co cdiv cceil cfv nnre 3re a1i remulcld rehalfcld ceilcld
    c2 cr zred clt wbr 2re nnrp 2lt3 ltmul1dd wb 2pos ltmuldiv2 syl112anc mpbid
    cc0 ceilged ltletrd ) ABCZADAEFZPGFZUOHIZAJZUMUNUMDADQCUMKLZUQMZNZUMUPUMUOU
    TORUMPAEFUNSTZAUOSTZUMPDAPQCZUMUALZURAUBPDSTUMUCLUDUMAQCUNQCVCUJPSTZVAVBUEU
    QUSVDVEUMUFLAUNPUGUHUIUMUOUTUKUL $.

  ${
    gpg3kgrtriex.n $e |- N = ( 3 x. K ) $.
    $( Lemma 2 for ~ gpg3kgrtriex .  (Contributed by AV, 1-Oct-2025.) $)
    gpg3kgrtriexlem2 $p |- ( K e. NN
                         -> ( -u K mod N ) = ( ( ( K mod N ) + K ) mod N ) ) $=
      ( cn wcel cmo co caddc c2 cmul crp wceq c3 a1i eqeltrid syl3anc oveq1d cz
      cc0 nnmulcld cneg cr nnre 3rp nnrp rpmulcld modaddmod nncn 2timesd eqcomd
      c1 2cnd adddirp1d 2p1e3 oveq1i eqtr3di oveq2d modid0 syl 3eqtrd wb 2nn id
      nnzd nnz 3nn summodnegmod mpbid 3eqtrrd ) ADEZABFGAHGBFGZAAHGZBFGZIAJGZBF
      GZAUABFGZVJAUBEZVQBKEVKVMLAUCZVRVJBMAJGZKCVJMAMKEVJUDNAUEUFZOAABUGPVJVLVN
      BFVJVNVLVJAAUHZUIUJQVJVNAHGZBFGZSLZVOVPLZVJWCVSBFGVSVSFGZSVJWBVSBFVJIUKHG
      ZAJGWBVSVJIAVJULWAUMWGMAJUNUOUPQVJBVSVSFBVSLVJCNUQVJVSKEWFSLVTVSURUSUTVJV
      NREAREBDEWDWEVAVJVNVJIAIDEVJVBNVJVCZTVDAVEVJBVSDCVJMAMDEVJVFNWHTOVNABVGPV
      HVI $.

    $( Lemma 3 for ~ gpg3kgrtriex .  (Contributed by AV, 1-Oct-2025.) $)
    gpg3kgrtriexlem3 $p |- ( K e. NN -> N e. ( ZZ>= ` 3 ) ) $=
      ( cn wcel c3 cmul co cuz cfv cz cle wbr 3z a1i nnz zmulcld c1 3t1e3 cr wa
      nnge1 cc0 clt wb 1re nnre 3re pm3.2i lemul2 mp3an2i mpbid eqbrtrrid eluz2
      3pos syl3anbrc eqeltrid ) ADEZBFAGHZFIJZCURFKEZUSKEFUSLMUSUTEVAURNOZURFAV
      BAPQURFFRGHZUSLSURRALMZVCUSLMZAUBRTEURATEFTEZUCFUDMZUAZVDVEUEUFAUGVHURVFV
      GUHUOUIORAFUJUKULUMFUSUNUPUQ $.

    $( Lemma 4 for ~ gpg3kgrtriex .  (Contributed by AV, 1-Oct-2025.) $)
    gpg3kgrtriexlem4 $p |- ( K e. NN -> K e. ( 1 ..^ ( |^ ` ( N / 2 ) ) ) ) $=
      ( cn wcel c2 co cceil cfv clt wbr c1 cle c3 cr rehalfcld eqeltrid ceilcld
      cdiv zred cfzo id cmul oveq1i 3re a1i nnre remulcld 1red gpg3kgrtriexlem1
      cz nnge1 ltled fveq2i breqtrrdi letrd elnnz1 sylanbrc elfzo1 syl3anbrc )
      ADEZVABFSGZHIZDEZAVCJKALVCUAGEVAUBVAVCUKELVCMKVDVAVBVAVBNAUCGZFSGZOBVEFSC
      UDZVAVEVANANOEVAUEUFAUGZUHZPZQRVALAVCVAUIVHVAVCVAVBVABVABVEOCVIQPRTAULVAA
      VFHIZVCMVAAVKVHVAVKVAVFVJRTAUJZUMVBVFHVGUNZUOUPVCUQURVAAVKVCJVLVMUOVCAUSU
      T $.

    $( Lemma 5 for ~ gpg3kgrtriex .  (Contributed by AV, 1-Oct-2025.) $)
    gpg3kgrtriexlem5 $p |- ( K e. NN -> ( K mod N ) =/= ( -u K mod N ) ) $=
      ( cn wcel cmo co c2 cmul cdvds wbr wceq c3 c1 cfz a1i syl2anc cz cc0 wb
      cneg cmin wn 3nn cuz cfv 2eluzge1 eluzfz2 ax-mp oveq2i eleqtrri fzm1ndvds
      3m1e2 wne 3z 2z nnz nnne0 dvdsmulcr syl112anc mtbird breq1i sylnibr caddc
      id nnmulcld eqeltrid 2nn nnzd dvdsval3 2timesd oveq1d eqeq1d summodnegmod
      nncn syl3anc 3bitrd mtbid neqned ) ADEZABFGZAUABFGZVTBHAIGZJKZWAWBLZVTMAI
      GZWCJKZWDVTWGMHJKZVTMDEZHNMNUBGZOGZEZWHUCWIVTUDPZWLVTHNHOGZWKHNUEUFEHWNEU
      GNHUHUIWJHNOUMUJUKPMHULQVTMREZHREZAREZASUNWGWHTWOVTUOPWPVTUPPAUQZAURAMHUS
      UTVABWFWCJCVBVCVTWDWCBFGZSLZAAVDGZBFGZSLZWEVTBDEZWCREWDWTTVTBWFDCVTMAWMVT
      VEZVFVGZVTWCVTHAHDEVTVHPXEVFVIBWCVJQVTWSXBSVTWCXABFVTAAVOVKVLVMVTWQWQXDXC
      WETWRWRXFAABVNVPVQVRVS $.

    gpg3kgrtriex.g $e |- G = ( N gPetersenGr K ) $.
    ${
      $d E x $.  $d K x $.  $d N x $.
      gpg3kgrtriex.e $e |- E = { <. 1 , ( K mod N ) >. ,
                                 <. 1 , ( -u K mod N ) >. } $.
      $( Lemma 6 for ~ gpg3kgrtriex : ` E ` is an edge in the generalized
         Petersen graph G(N,K) with ` N = 3 x. K ` .  (Contributed by AV,
         1-Oct-2025.) $)
      gpg3kgrtriexlem6 $p |- ( K e. NN -> E e. ( Edg ` G ) ) $=
        ( cn wcel cc0 cop c1 caddc co cmo cpr wceq c3 cle wbr cedg cfv w3o cfzo
        vx cv wrex cz nnz 3nn a1i id nnmulcld eqeltrid zmodfzo syl2anc wb opeq2
        cmul oveq1 oveq1d opeq2d preq12d eqeq2d 3orbi123d cneg gpg3kgrtriexlem2
        adantl preq2d eqtrid 3mix3d rspcedvd cuz c2 cdiv cceil 3z zmulcld 3t1e3
        nnge1 cr clt wa 1red nnre 3re 3pos pm3.2i syl3anc mpbid eqbrtrrid eluz2
        lemul2 syl3anbrc remulcld rehalfcld ceilcld zred gpg3kgrtriexlem1 ltled
        oveq1i fveq2i breqtrrdi letrd elnnz1 sylanbrc elfzo1 gpgedgel mpbird
        eqid ) CHIZABUAUBZIZAJUEUFZKZJXNLMNZDONZKZPZQZAXOLXNKZPZQZAYALXNCMNZDON
        ZKZPZQZUCZUEJDUDNZUGZXKYIAJCDONZKZJYLLMNZDONZKZPZQZAYMLYLKZPZQZAYSLYLCM
        NZDONZKZPZQZUCZUEYLYJXKCUHIDHIYLYJICUIZXKDRCUSNZHEXKRCRHIXKUJUKXKULZUMU
        NCDUOUPXNYLQZYIUUGUQXKUUKXTYRYCUUAYHUUFUUKXSYQAUUKXOYMXRYPXNYLJURZUUKXQ
        YOJUUKXPYNDOXNYLLMUTVAVBVCVDUUKYBYTAUUKXOYMYAYSUULXNYLLURZVCVDUUKYGUUEA
        UUKYAYSYFUUDUUMUUKYEUUCLUUKYDUUBDOXNYLCMUTVAVBVCVDVEVHXKUUFYRUUAXKAYSLC
        VFDONZKZPUUEGXKUUOUUDYSXKUUNUUCLCDEVGVBVIVJVKVLXKDRVMUBZICLDVNVONZVPUBZ
        UDNZIZXMYKUQXKDUUIUUPEXKRUHIZUUIUHIRUUISTUUIUUPIUVAXKVQUKZXKRCUVBUUHVRX
        KRRLUSNZUUISVSXKLCSTZUVCUUISTZCVTZXKLWAICWAIRWAIZJRWBTZWCZUVDUVEUQXKWDZ
        CWEZUVIXKUVGUVHWFWGWHUKLCRWMWIWJWKRUUIWLWNUNXKXKUURHIZCUURWBTUUTUUJXKUU
        RUHILUURSTUVLXKUUQXKDXKDUUIWAEXKRCUVGXKWFUKUVKWOZUNWPWQZXKLCUURUVJUVKXK
        UURUVNWRUVFXKCUUIVNVONZVPUBZUURSXKCUVPUVKXKUVPXKUVOXKUUIUVMWPWQWRCWSZWT
        UUQUVOVPDUUIVNVOEXAXBZXCXDUURXEXFXKCUVPUURWBUVQUVRXCUURCXGWNUEXLBYJUUSC
        DAYJXJUUSXJFXLXJXHUPXI $.
    $}

    $d G a b c t $.  $d K a b c $.  $d N b c $.
    $( All generalized Petersen graphs G(N,K) with ` N = 3 x. K ` contain
       triangles.  (Contributed by AV, 1-Oct-2025.) $)
    gpg3kgrtriex $p |- ( K e. NN -> E. t t e. ( GrTriangles ` G ) ) $=
      ( vb vc wcel cfv wa co c1 cc0 cop a1i wb eqid wceq cmo cgrtri wex wne cpr
      va cn cv cedg cnbgr wrex cvtx cgpg cfzo 1elpr01 c3 cmul nnmulcld eqeltrid
      cxp id lbfzo0 sylibr opelxpd c2 cdiv cceil gpg3kgrtriexlem4 gpgvtx eleq2d
      3nn jca syl mpbird fveq2i eleqtrrdi oveq2 biidd rexeqbidv c2nd caddc cmin
      adantl ctp cuz c1st gpg3kgrtriexlem3 olcd opgpgvtx c0ex op1st gpgnbgrvtx1
      wo 1ex syl22anc neeq1 preq1 eleq1d anbi12d neeq2 preq2 tpid1 eleq2 mpbiri
      opex tpid3 cneg gpg3kgrtriexlem5 oveq1i nncn addlidd eqtrid oveq1d df-neg
      op2nd eqtr4di 3netr4d ovex opthne opeq2d preq12d gpg3kgrtriexlem6 eqeltrd
      eqtrd adantr 2rspcedvdw mpdan rspcedvd cusgr gpgusgra usgrgrtrirex 3syl )
      CUFIZAUGBUAJIAUBZGUGZHUGZUCZYNYOUDZBUHJZIZKZHBUEUGZUILZUJZGUUBUJZUEBUKJZU
      JZYLUUDYTHBMNOZUILZUJZGUUHUJZUEUUGUUEYLUUGDCULLZUKJZUUEYLUUGUULIZUUGNMUDZ
      NDUMLZUSZIZYLMNUUNUUOMUUNIYLUNPYLDUFIZNUUOIZYLDUOCUPLUFEYLUOCUOUFIYLVJPYL
      UTUQURZDVAVBZVCYLUURCMDVDVELVFJUMLZIZKZUUMUUQQYLUURUVCUUTCDEVGZVKUVDUULUU
      PUUGUUOUVBCDUVBRZUUORZVHVIVLVMBUUKUKFVNVOUUAUUGSZUUDUUJQYLUVHUUCUUIGUUBUU
      HUUAUUGBUIVPZUVHYTYTHUUBUUHUVIUVHYTVQVRVRWBYLUUHMUUGVSJZCVTLZDTLZOZNUVJOZ
      MUVJCWALZDTLZOZWCZSZUUJYLDUOWDJIZUVCUUGUUEIZUUGWEJMSZUVSCDEWFZUVEYLUWAMNS
      ZMMSZWLZUUSKZYLUWFUUSYLUWEUWDUWEYLMRPWGUVAVKYLUVTUVCKZUWAUWGQYLUVTUVCUWCU
      VEVKZBUUOUVBCDUUEMNUVGUVFFUUERZWHVLVMUWBYLMNWMWIWJPUUHBUVBCDUUEUUGUVFFUWJ
      UUHRWKWNYLUVSKZYTUVMYOUCZUVMYOUDZYRIZKUVMUVQUCZUVMUVQUDZYRIZKZGHUVMUVQUUH
      UUHYNUVMSZYPUWLYSUWNYNUVMYOWOUWSYQUWMYRYNUVMYOWPWQWRYOUVQSZUWLUWOUWNUWQYO
      UVQUVMWSUWTUWMUWPYRYOUVQUVMWTWQWRUWKUVMUUHIZUVMUVRIZUVMUVNUVQMUVLXDXAUVSU
      XAUXBQYLUUHUVRUVMXBWBXCUWKUVQUUHIZUVQUVRIZUVMUVNUVQMUVPXDXEUVSUXCUXDQYLUU
      HUVRUVQXBWBXCYLUWRUVSYLUWOUWQYLMMUCZUVLUVPUCZWLUWOYLUXFUXEYLCDTLZCXFZDTLZ
      UVLUVPCDEXGYLUVKCDTYLUVKNCVTLZCUVJNCVTMNWMWIXNZXHYLCCXIXJZXKXLYLUVOUXHDTY
      LUVONCWALZUXHUVOUXMSYLUVJNCWAUXKXHPCXMZXOXLXPWGMUVLMUVPWMUVKDTXQXRVBYLUWP
      MUXGOZMUXIOZUDZYRYLUVMUXOUVQUXPYLUVLUXGMYLUVKCDTYLUVKUXJCYLUVJNCVTUVJNSYL
      UXKPZXLUXLYCXLXSYLUVPUXIMYLUVOUXHDTYLUVOUXMUXHYLUVJNCWAUXRXLUXNXOXLXSXTUX
      QBCDEFUXQRYAYBVKYDYEYFYGYLUWHBYHIYMUUFQUWIUWHBUUKYHFCDYIURAYRBUUBUUEUEGHU
      WJYRRUUBRYJYKVM $.
  $}

  ${
    $d G x y $.  $d K x y $.  $d V x y $.
    gpg5gricstgr3.g $e |- G = ( 5 gPetersenGr K ) $.
    $( Each closed neighborhood in a generalized Petersen graph G(N,K) of order
       10 ( ` N = 5 ` ), which is either the Petersen graph G(5,2) or the
       5-prism G(5,1), is isomorphic to a 3-star.  (Contributed by AV,
       13-Sep-2025.) $)
    gpg5gricstgr3 $p |- ( ( K e. ( 1 ... 2 ) /\ V e. ( Vtx ` G ) )
                   -> ( G ISubGr ( G ClNeighbVtx V ) ) ~=gr ( StarGr ` 3 ) ) $=
      ( vx vy c1 c2 co wcel cvtx cfv wa cusgr c3 wceq cv c5 cfzo eqid cfz cnbgr
      chash cpr cedg wnel wral cclnbgr cisubgr cstgr cgric wbr cuz cceil 5eluz3
      caddc cz fzval3 ax-mp 2p1e3 oveq2i ceil5half3 eqcomi 3eqtri eleq2i biimpi
      cdiv 2z gpgusgra eqeltrid sylancr anim1i eqidd birani simpr gpg5nbgr3star
      cgpg syl3anc 3nn0 isubgr3stgr sylc ) BGHUAIZJZCAKLZJZMZANJZWEMACUBIZUCLOP
      EQFQUDAUELZUFFWHUGEWHUGMZAACUHIZUIIOUJLZUKULWCWGWEWCROUMLJZBGRHVGIUNLZSIZ
      JZWGUOWCWPWBWOBWBGHGUPIZSIZGOSIWOHUQJWBWRPVHGHURUSWQOGSUTVAOWNGSWNOVBVCVA
      VDVEZVFWMWPMARBVQINDBRVIVJVKVLWFRRPWPWEWJWFRVMWCWPWEWSVNWCWEVOEFWHWIAWOBR
      WDCWOTDWDTZWHTZWITZVPVREFWKWLWHWIAOWDWLKLZCWTXAWKTVSWLTXCTXBVTWA $.
  $}

  $( Lemma for theorems about Petersen graphs.  (Contributed by AV,
     10-Nov-2025.) $)
  pglem $p |- 2 e. ( 1 ..^ ( |^ ` ( 5 / 2 ) ) ) $=
    ( c2 c1 c3 cfzo co cdiv cceil cfv cpr 2ex prid2 fzo13pr eleqtrri ceil5half3
    c5 oveq2i ) ABCDEZBOAFEGHZDEABAIQBAJKLMRCBDNPM $.

  $( A Petersen graph is a simple graph.  (Contributed by AV, 10-Nov-2025.) $)
  pgjsgr $p |- ( 5 gPetersenGr 2 ) e. USGraph $=
    ( c5 c3 cuz cfv wcel c2 c1 cdiv cceil cfzo cgpg cusgr 5eluz3 pglem gpgusgra
    co mp2an ) ABCDEFGAFHPIDJPEAFKPLEMNFAOQ $.

  ${
    $d v w $.
    $( A local isomorphism between the two generalized Petersen graphs G(N,K)
       of order 10 ( ` N = 5 ` ), which are the Petersen graph G(5,2) and the
       5-prism G(5,1).  (Contributed by AV, 28-Dec-2025.) $)
    gpg5grlim $p |- ( _I |` ( { 0 , 1 } X. ( 0 ..^ 5 ) ) )
                  e. ( ( 5 gPetersenGr 1 ) GraphLocIso ( 5 gPetersenGr 2 ) ) $=
      ( vv vw c5 c1 cgpg co cusgr wcel c2 cvtx cfv cc0 cfzo wf1o cv cclnbgr wbr
      c3 cuz eqid cid cpr cxp cres cisubgr cstgr cgric wral cgrlim cceil 5eluz3
      w3a cdiv cz clt 3z eluz2b1 mpbir2an fzo1lb mpbir ceil5half3 eqcomi oveq2i
      1lt3 eleqtri gpgusgra mp2an pgjsgr f1oi cn wb 5nn pglem wa eqidd wceq a1i
      gpgvtx sylan2 f1oeq123d 3pm3.2i 2eluzge1 eluzfz1 ax-mp gpg5gricstgr3 mpan
      cfz rgen eluzfz2 3nn0 clnbgr3stgrgrlim mp3an ) CDEFZGHZCIEFZGHZWMJKZWOJKZ
      UALDUBLCMFZUCZUDZNZULWMWMAOZPFUEFRUFKZUGQZAWQUHWOWOBOZPFUEFXDUGQZBWRUHXAW
      MWOUIFHWNWPXBCRSKHDDCIUMFUJKZMFZHZWNUKDDRMFZXIDXKHRISKHZXLRUNHDRUOQUPVDRU
      QURRUSUTRXHDMXHRVAVBVCVEZDCVFVGVHXBWTWTXANZWTVICVJHZIXIHZXBXNVKVLVMXOXPVN
      ZWQWTWRWTXAXAXQXAVOXPXOXJWQWTVPXJXPXMVQWSXIDCXITZWSTZVRVSWSXIICXRXSVRVTVG
      UTWAXEAWQDDIWGFZHZXCWQHXEIDSKHZYAWBDIWCWDWMDXCWMTWEWFWHXGBWRIXTHZXFWRHXGY
      BYCWBDIWIWDWOIXFWOTWEWFWHABXAWMWORWQWRWJWQTWRTWKWL $.

    $( The two generalized Petersen graphs G(N,K) of order 10 ( ` N = 5 ` ),
       which are the Petersen graph G(5,2) and the 5-prism G(5,1), are locally
       isomorphic.  (Contributed by AV, 29-Sep-2025.)  (Proof shortened by AV,
       22-Nov-2025.) $)
    gpg5grlic $p |- ( 5 gPetersenGr 1 ) ~=lgr ( 5 gPetersenGr 2 ) $=
      ( vv vw c5 c1 cgpg co cusgr wcel c2 cvtx cfv wbr c3 cfzo mp2an wceq ax-mp
      cuz cvv eqid cen w3a cclnbgr cisubgr cstgr cgric wral cgrlic cceil 5eluz3
      cv cdiv cz 3z 1lt3 eluz2b1 mpbir2an fzo1lb mpbir ceil5half3 eqcomi oveq2i
      clt eleqtri gpgusgra pglem cc0 cdc cfz 2eluzge1 eluzfz1 gpg5order eluzfz2
      chash wa eqtr3 cfn wb wi fvex 10nn0 hashvnfin hashen syl2an mpbid 3pm3.2i
      cn0 gpg5gricstgr3 mpan rgen 3nn0 clnbgr3stgrgrlic mp3an ) CDEFZGHZCIEFZGH
      ZWNJKZWPJKZUALZUBWNWNAUKZUCFUDFMUEKZUFLZAWRUGWPWPBUKZUCFUDFXBUFLZBWSUGWNW
      PUHLWOWQWTCMRKHZDDCIULFUIKZNFZHWOUJDDMNFZXHDXIHMIRKHZXJMUMHDMVCLUNUOMUPUQ
      MURUSMXGDNXGMUTVAVBVDDCVEOXFIXHHWQUJVFICVEOWRVNKZDVGVHZPZWSVNKZXLPZWTDDIV
      IFZHZXMIDRKHZXQVJDIVKQZDVLQIXPHZXOXRXTVJDIVMQZIVLQXMXOVOXKXNPZWTXKXNXLVPX
      MWRVQHZWSVQHZYBWTVRXOWRSHXLWGHZXMYCVSWNJVTWAWRXLSWBOWSSHYEXOYDVSWPJVTWAWS
      XLSWBOWRWSWCWDWEOWFXCAWRXQXAWRHXCXSWNDXAWNTWHWIWJXEBWSXTXDWSHXEYAWPIXDWPT
      WHWIWJABWNWPMWRWSWKWRTWSTWLWM $.
  $}

  ${
    gpgprismgr4cycllem1.f $e |- F = <" { <. 0 , 0 >. , <. 0 , 1 >. }
                                       { <. 0 , 1 >. , <. 1 , 1 >. }
                                       { <. 1 , 1 >. , <. 1 , 0 >. }
                                       { <. 1 , 0 >. , <. 0 , 0 >. } "> $.
    $( Lemma 1 for ~ gpgprismgr4cycl0 : the cycle ` <. P , F >. ` consists of 4
       edges (i.e., has length 4).  (Contributed by AV, 1-Nov-2025.) $)
    gpgprismgr4cycllem1 $p |- ( # ` F ) = 4 $=
      ( chash cfv cc0 cop c1 cpr cs4 c4 fveq2i s4len eqtri ) ACDEEFZEGFZHZOGGFZ
      HZQGEFZHZSNHZIZCDJAUBCBKPRTUALM $.

    $( Lemma 2 for ~ gpgprismgr4cycl0 : the cycle ` <. P , F >. ` is proper,
       i.e., it has no overlapping edges.  (Contributed by AV, 2-Nov-2025.) $)
    gpgprismgr4cycllem2 $p |- Fun `' F $=
      ( cc0 cop c1 cpr cvv wcel wa wne pm3.2i wo olci c0ex opthne mpbir prneimg
      orci mp2 1ex w3a cs4 wceq cdm wf1o wi ccnv wfun prex opex ax-1ne0 3pm3.2i
      cun 0ne1 s4f1o imp pm2.27 ax-mp wf1 wfo df-f1o df-f1 simprbi adantr sylbi
      wf syl mp2b ) CCDZCEDZFZGHZVJEEDZFZGHZIZVMECDZFZGHZVQVIFZGHZIZIZVKVNJZVKV
      RJZVKVTJZUAZVNVRJZVNVTJZVRVTJZUAZIZIAVKVNVRVTUBUCZAUDZVKVNFVRVTFUMZAUEZUF
      ZAUGUHZWCWLVPWBVLVOVIVJUIVJVMUIKVSWAVMVQUIVQVIUIKKWGWKWDWEWFVIGHZVJGHZIZW
      TVMGHZIZIVIVJJZVIVMJZIZVJVJJVJVMJZIZLWDXAXCWSWTCCUJZCEUJZKZWTXBXJEEUJZKZK
      XFXHXDXEXDCCJZCEJZLXOXNUNMCCCENNOPXEXOXOLXOXOUNRCCEENNOPZKRVIVJVJVMGGGGQS
      XAXBVQGHZIZIXEVIVQJZIZXGVJVQJZIZLWEXAXRXKXBXQXLECUJZKZKXTYBXEXSXPXSXOXNLX
      OXNUNRCCECNNOPKRVIVJVMVQGGGGQSXAXQWSIZIXSVIVIJIZYAVJVIJZIZLWFXAYEXKXQWSYC
      XIKZKYHYFYAYGYAXOECJZLYJXOUKMCEECNTOPZYGXNYJLYJXNUKMCECCNTOPKMVIVJVQVIGGG
      GQSULWHWIWJXCXRIYBVMVMJVMVQJZIZLWHXCXRXMYDKYBYMXGYAXGXOEEJZLXOYNUNRCEEENT
      OPYKKRVJVMVMVQGGGGQSXCYEIYHYLVMVIJZIZLWIXCYEXMYIKYPYHYLYOYLYNYJLYJYNUKMEE
      ECTTOPYOYJYJLYJYJUKMEECCTTOPKZMVJVMVQVIGGGGQSXRYEIYPVQVQJVQVIJIZLWJXRYEYD
      YIKYPYRYQRVMVQVQVIGGGGQSULKKWCWLWQVKVNVRVTGAUOUPWQWPWRWMWQWPUFBWMWPUQURWP
      WNWOAUSZWNWOAUTZIWRWNWOAVAYSWRYTYSWNWOAVFWRWNWOAVBVCVDVEVGVH $.

    $d N x $.  $d X x $.
    $( Lemma 3 for ~ gpgprismgr4cycl0 .  (Contributed by AV, 5-Nov-2025.) $)
    gpgprismgr4cycllem3 $p |- ( ( N e. ( ZZ>= ` 3 ) /\ X e. ( 0 ..^ 4 ) )
       -> ( ( F ` X ) e. ~P ( { 0 , 1 } X. ( 0 ..^ N ) ) /\ E. x e. ( 0 ..^ N )
         ( ( F ` X ) = { <. 0 , x >. , <. 0 , ( ( x + 1 ) mod N ) >. }
        \/ ( F ` X ) = { <. 0 , x >. , <. 1 , x >. }
        \/ ( F ` X ) = { <. 1 , x >. , <. 1 , ( ( x + 1 ) mod N ) >. } ) ) ) $=
      ( cc0 co wcel c3 cfv c1 cpr cop wceq w3o c2 eqeq2d 3orbi123d cvv eqeq1d
      c4 cfzo cuz cxp cpw cv caddc cmo wrex wa wo wi cun fzo0to42pr eleq2i elun
      bitri elpri 0elpr01 a1i cn eluz3nn lbfzo0 sylibr opelxpd cn0 clt wbr 1nn0
      uzuzle23 eluz2gt1 syl elfzo0 syl3anbrc prelpwi syl2anc opeq2 oveq1 oveq1d
      opeq2d preq12d eluzelre 1mod 1e0p1 oveq1i eqtr3di preq2d 3mix1d rspcedvdw
      jca fveq2 cs4 fveq1i prex s4fv0 ax-mp eqtri eqtrdi eleq1d rexbidv anbi12d
      cr imbitrrid 1elpr01 eqid 3mix2i s4fv1 jaoi adantr prcom eqtrid 3mix3d wb
      s4fv2 adantl mpbird expcom s4fv3 sylbi impcom ) DFUAUBGZHZCIUCJHZDBJZFKLZ
      FCUBGZUDZUEZHZYDFAUFZMZFYJKUGGZCUHGZMZLZNZYDYKKYJMZLZNZYDYQKYMMZLZNZOZAYF
      UIZUJZYBDYEHZDPILZHZUKZYCUUEULZYBDYEUUGUMZHUUIYAUUKDUNUODYEUUGUPUQUUFUUJU
      UHUUFDFNZDKNZUKUUJDFKURUULUUJUUMYCUUEUULFFMZFKMZLZYHHZUUPYONZUUPYRNZUUPUU
      ANZOZAYFUIZUJYCUUQUVBYCUUNYGHZUUOYGHZUUQYCFFYEYFFYEHYCUSUTZYCCVAHZFYFHCVB
      ZCVCVDZVEZYCFKYEYFUVEYCKVFHZUVFKCVGVHZKYFHUVJYCVIUTUVGYCCPUCJHUVKCVJCVKVL
      ZKCVMVNZVEZUUNUUOYGVOVPYCUVAUUPUUNFFKUGGZCUHGZMZLZNZUUPUUNKFMZLZNZUUPUVTK
      UVPMZLZNZOAFYFYJFNZUURUVSUUSUWBUUTUWEUWFYOUVRUUPUWFYKUUNYNUVQYJFFVQZUWFYM
      UVPFUWFYLUVOCUHYJFKUGVRVSZVTWAZQUWFYRUWAUUPUWFYKUUNYQUVTUWGYJFKVQZWAZQUWF
      UUAUWDUUPUWFYQUVTYTUWCUWJUWFYMUVPKUWHVTWAZQRUVHYCUVSUWBUWEYCUUOUVQUUNYCKU
      VPFYCKCUHGZKUVPYCCXBHUVKUWMKNICWBUVLCWCVPKUVOCUHWDWEWFZVTWGWHWIWJUULYIUUQ
      UUDUVBUULYDUUPYHUULYDFBJZUUPDFBWKUWOFUUPUUOKKMZLZUWPUVTLZUVTUUNLZWLZJZUUP
      FBUWTEWMUUPSHUXAUUPNUUNUUOWNUUPUWQUWRUWSSWOWPWQWRZWSUULUUCUVAAYFUULYPUURY
      SUUSUUBUUTUULYDUUPYOUXBTUULYDUUPYRUXBTUULYDUUPUUAUXBTRWTXAXCYCUUEUUMUWQYH
      HZUWQYONZUWQYRNZUWQUUANZOZAYFUIZUJYCUXCUXHYCUVDUWPYGHZUXCUVNYCKKYEYFKYEHY
      CXDUTZUVMVEZUUOUWPYGVOVPYCUXGUWQUUOFKKUGGZCUHGZMZLZNZUWQUWQNZUWQUWPKUXMMZ
      LZNZOZAKYFYJKNZUXDUXPUXEUXQUXFUXTUYBYOUXOUWQUYBYKUUOYNUXNYJKFVQZUYBYMUXMF
      UYBYLUXLCUHYJKKUGVRVSZVTWAQUYBYRUWQUWQUYBYKUUOYQUWPUYCYJKKVQZWAQUYBUUAUXS
      UWQUYBYQUWPYTUXRUYEUYBYMUXMKUYDVTWAQRUVMUYAYCUXQUXPUXTUWQXEXFUTWIWJUUMYIU
      XCUUDUXHUUMYDUWQYHUUMYDKBJZUWQDKBWKUYFKUWTJZUWQKBUWTEWMUWQSHUYGUWQNUUOUWP
      WNUUPUWQUWRUWSSXGWPWQWRZWSUUMUUCUXGAYFUUMYPUXDYSUXEUUBUXFUUMYDUWQYOUYHTUU
      MYDUWQYRUYHTUUMYDUWQUUAUYHTRWTXAXCXHVLUUHDPNZDINZUKUUJDPIURUYIUUJUYJYCUYI
      UUEYCUYIUJZUUEUWRYHHZUWRYONZUWRYRNZUWRUUANZOZAYFUIZUJZUYKUYLUYQUYKUXIUVTY
      GHZUJZUYLYCUYTUYIYCUXIUYSUXKYCKFYEYFUXJUVHVEZWJXIUWPUVTYGVOVLYCUYQUYIYCUY
      PUWRUVRNZUWRUWANZUWRUWDNZOAFYFUWFUYMVUBUYNVUCUYOVUDUWFYOUVRUWRUWIQUWFYRUW
      AUWRUWKQUWFUUAUWDUWRUWLQRUVHYCVUDVUBVUCYCUWRUVTUWPLUWDUWPUVTXJYCUWPUWCUVT
      YCKUVPKUWNVTWGXKXLWIXIWJUYIUUEUYRXMYCUYIYIUYLUUDUYQUYIYDUWRYHUYIYDPBJZUWR
      DPBWKVUEPUWTJZUWRPBUWTEWMUWRSHVUFUWRNUWPUVTWNUUPUWQUWRUWSSXNWPWQWRZWSUYIU
      UCUYPAYFUYIYPUYMYSUYNUUBUYOUYIYDUWRYOVUGTUYIYDUWRYRVUGTUYIYDUWRUUAVUGTRWT
      XAXOXPXQYCUUEUYJUWSYHHZUWSYONZUWSYRNZUWSUUANZOZAYFUIZUJYCVUHVUMYCUYSUVCVU
      HVUAUVIUVTUUNYGVOVPYCVULUWSUVRNZUWSUWANZUWSUWDNZOZAFYFUWFVUIVUNVUJVUOVUKV
      UPUWFYOUVRUWSUWIQUWFYRUWAUWSUWKQUWFUUAUWDUWSUWLQRUVHVUQYCVUOVUNVUPUVTUUNX
      JXFUTWIWJUYJYIVUHUUDVUMUYJYDUWSYHUYJYDIBJZUWSDIBWKVURIUWTJZUWSIBUWTEWMUWS
      SHVUSUWSNUVTUUNWNUUPUWQUWRUWSSXRWPWQWRZWSUYJUUCVULAYFUYJYPVUIYSVUJUUBVUKU
      YJYDUWSYOVUTTUYJYDUWSYRVUTTUYJYDUWSUUAVUTTRWTXAXCXHVLXHXSXT $.
  $}

  ${
    gpgprismgr4cycl.p $e |- P = <" <. 0 , 0 >. <. 0 , 1 >. <. 1 , 1 >.
                                    <. 1 , 0 >. <. 0 , 0 >. "> $.
    $( Lemma 4 for ~ gpgprismgr4cycl0 : the cycle ` <. P , F >. ` consists of 5
       vertices (the first and the last vertex are identical, see
       ~ gpgprismgr4cycllem6 .  (Contributed by AV, 1-Nov-2025.) $)
    gpgprismgr4cycllem4 $p |- ( # ` P ) = 5 $=
      ( chash cfv cc0 cop c1 cs5 c5 fveq2i s5len eqtri ) ACDEEFZEGFZGGFZGEFZMHZ
      CDIAQCBJMNOPMKL $.

    $( Lemma 5 for ~ gpgprismgr4cycl0 .  (Contributed by AV, 1-Nov-2025.) $)
    gpgprismgr4cycllem5 $p |- P e. Word _V $=
      ( cc0 cop c1 cs5 cvv cword s5cli eqeltri ) ACCDZCEDZEEDZECDZKFGHBKLMNKIJ
      $.

    $( Lemma 6 for ~ gpgprismgr4cycl0 : the cycle ` <. P , F >. ` is closed,
       i.e., the first and the last vertex are identical.  (Contributed by AV,
       1-Nov-2025.) $)
    gpgprismgr4cycllem6 $p |- ( P ` 0 ) = ( P ` 4 ) $=
      ( cc0 cop c1 cs5 cfv cvv wcel wceq opex cs4 df-s5 s4cli s4len s4fv0 ax-mp
      c4 0nn0 fveq1i 4pos cats1fv cats1fvn eqtr4i 3eqtr4i ) CCCDZCEDZEEDZECDZUF
      FZGZRUJGZCAGRAGUKUFULUFHIZUKUFJCCKZUFUGUHUILZUJRCHUFUFUFUGUHUIUFMZUFUGUHU
      INZUFUGUHUIOZUFUGUHUIHPSUAUBQUMULUFJUNUOUJRHUFUPUQURUCQUDCAUJBTRAUJBTUE
      $.

    $( Lemma 7 for ~ gpgprismgr4cycl0 : the cycle ` <. P , F >. ` is proper,
       i.e., it has no overlapping vertices, except the first and the last one.
       (Contributed by AV, 1-Nov-2025.) $)
    gpgprismgr4cycllem7 $p |- ( ( X e. ( 0 ..^ ( # ` P ) )
                                  /\ Y e. ( 1 ..^ 4 ) )
                                 -> ( X =/= Y -> ( P ` X ) =/= ( P ` Y ) ) ) $=
      ( cc0 cfv wcel c1 c2 c3 c4 wne wceq wa mpbir cvv a1i adantl adantr ex cpr
      chash cfzo co cun csn ctp wi caddc c5 gpgprismgr4cycllem4 df-5 oveq2i cuz
      eqtri cn0 4nn0 elnn0uz mpbi fzosplitsn fzo0to42pr uneq1i 3eqtri fzo1to4tp
      ax-mp eleq2i wo elun orbi1i bitri elpri w3o cop 0ne1 olci c0ex opthne cs5
      fveq1i opex cs4 df-s5 s4cli s4len s4fv0 0nn0 4pos cats1fv s4fv1 1nn0 1lt4
      neeq12i fveq2 a1d orci s4fv2 2nn0 2lt4 s4fv3 3nn0 3jaoi eltpi syl11 simpr
      3netr4d 3lt4 simpl neeq12d eqid eqneqall biimtrdi 1ex syl necomi cats1fvn
      jaoi elsni syl2imc sylbi imp syl2anb ) BEAUBFZUCUDZGBEHUAZIJUAZUEZKUFZUEZ
      GZCHIJUGZGZBCLZBAFZCAFZLZUHZCHKUCUDZGYCYHBYCEKHUIUDZUCUDZEKUCUDZYGUEZYHYB
      YREUCYBUJYRADUKULUOUMKEUNFGZYSUUAMKUPGUUBUQKURUSEKUTVEYTYFYGVAVBVCVFYQYJC
      VDVFYIYKYPYIBYDGZBYEGZVGZBYGGZVGZYKYPUHZYIBYFGZUUFVGUUGBYFYGVHUUIUUEUUFBY
      DYEVHVIVJUUEUUHUUFUUCUUHUUDUUCBEMZBHMZVGUUHBEHVKUUJUUHUUKCHMZCIMZCJMZVLZU
      UJYPYKUULUUJYPUHUUMUUNUULUUJYPUULUUJNZYOYLUUPEAFZHAFZYMYNUUQUURLZUUPUUSEE
      VMZEHVMZLZUVBEELZEHLZVGUVDUVCVNVOEEEHVPVPVQOZUUQUUTUURUVAUUQEUUTUVAHHVMZH
      EVMZUUTVRZFZUUTEAUVHDVSUUTPGZUVIUUTMEEVTZUUTUVAUVFUVGWAZUVHKEPUUTUUTUUTUV
      AUVFUVGUUTWBZUUTUVAUVFUVGWCZUUTUVAUVFUVGWDZUUTUVAUVFUVGPWEWFWGWHVEUOZUURH
      UVHFZUVAHAUVHDVSUVAPGUVQUVAMEHVTUVLUVHKHPUUTUVAUVMUVNUVOUUTUVAUVFUVGPWIWJ
      WKWHVEUOZWLOQUUJYMUUQMZUULBEAWMZRUULYNUURMZUUJCHAWMZSXEWNTUUMUUJYPUUMUUJN
      ZYOYLUWCUUQIAFZYMYNUUQUWDLZUWCUWEUUTUVFLZUWFUVDUVDVGUVDUVDVNWOEEHHVPVPVQO
      ZUUQUUTUWDUVFUVPUWDIUVHFZUVFIAUVHDVSUVFPGUWHUVFMHHVTUVLUVHKIPUUTUVFUVMUVN
      UVOUUTUVAUVFUVGPWPWQWRWHVEUOZWLOQUUJUVSUUMUVTRUUMYNUWDMZUUJCIAWMZSXEWNTUU
      NUUJYPUUNUUJNZYOYLUWLUUQJAFZYMYNUUQUWMLZUWLUWNUUTUVGLZUWOUVDUVCVGUVDUVCVN
      WOEEHEVPVPVQOZUUQUUTUWMUVGUVPUWMJUVHFZUVGJAUVHDVSUVGPGUWQUVGMHEVTUVLUVHKJ
      PUUTUVGUVMUVNUVOUUTUVAUVFUVGPWSWTXFWHVEUOZWLOQUUJUVSUUNUVTRUUNYNUWMMZUUJC
      JAWMZSXEWNTXACHIJXBZXCUUOUUKYPYKUULUUKYPUHUUMUUNUULUUKYPUULUUKNZYLHHLZYOU
      XBBHCHUULUUKXDUULUUKXGXHHHMUXCYOUHHXIYOHHXJVEXKTUUMUUKYPUUMUUKNZYOYLUXDUU
      RUWDYMYNUURUWDLZUXDUXEUVAUVFLZUXFUVDUXCVGUVDUXCVNWOEHHHVPXLVQOUURUVAUWDUV
      FUVRUWIWLOZQUUKYMUURMZUUMBHAWMZRUUMUWJUUKUWKSXEWNTUUNUUKYPUUNUUKNZYOYLUXJ
      UURUWMYMYNUURUWMLZUXJUXKUVAUVGLZUXLUVDHELZVGUVDUXMVNWOEHHEVPXLVQOUURUVAUW
      MUVGUVRUWRWLOZQUUKUXHUUNUXIRUUNUWSUUKUWTSXEWNTXAUXAXCXPXMUUDBIMZBJMZVGUUH
      BIJVKUXOUUHUXPUUOUXOYPYKUULUXOYPUHUUMUUNUULUXOYPUULUXONZYOYLUXQUWDUURYMYN
      UWDUURLUXQUURUWDUXGXNQUXOYMUWDMZUULBIAWMZRUULUWAUXOUWBSXEWNTUUMUXOYPUUMUX
      ONZYLIILZYOUXTBICIUUMUXOXDUUMUXOXGXHIIMUYAYOUHIXIYOIIXJVEXKTUUNUXOYPUUNUX
      ONZYOYLUYBUWDUWMYMYNUWDUWMLZUYBUYCUVFUVGLZUYDUXCUXMVGUXMUXCEHVNXNVOHHHEXL
      XLVQOUWDUVFUWMUVGUWIUWRWLOZQUXOUXRUUNUXSRUUNUWSUXOUWTSXEWNTXAUXAXCUUOUXPY
      PYKUULUXPYPUHUUMUUNUULUXPYPUULUXPNZYOYLUYFUWMUURYMYNUWMUURLUYFUURUWMUXNXN
      QUXPYMUWMMZUULBJAWMZRUULUWAUXPUWBSXEWNTUUMUXPYPUUMUXPNZYOYLUYIUWMUWDYMYNU
      WMUWDLUYIUWDUWMUYEXNQUXPUYGUUMUYHRUUMUWJUXPUWKSXEWNTUUNUXPYPUUNUXPNZYLJJL
      ZYOUYJBJCJUUNUXPXDUUNUXPXGXHJJMUYKYOUHJXIYOJJXJVEXKTXAUXAXCXPXMXPYKUUOUUF
      BKMZYPUXABKXQUULUYLYPUHUUMUUNUULUYLYPUULUYLNZYOYLUYMKAFZUURYMYNUYNUURLZUY
      MUYOUVBUVEUYNUUTUURUVAUYNKUVHFZUUTKAUVHDVSUVJUYPUUTMUVKUVLUVHKPUUTUVMUVNU
      VOXOVEUOZUVRWLOQUYLYMUYNMZUULBKAWMZRUULUWAUYLUWBSXEWNTUUMUYLYPUUMUYLNZYOY
      LUYTUYNUWDYMYNUYNUWDLZUYTVUAUWFUWGUYNUUTUWDUVFUYQUWIWLOQUYLUYRUUMUYSRUUMU
      WJUYLUWKSXEWNTUUNUYLYPUUNUYLNZYOYLVUBUYNUWMYMYNUYNUWMLZVUBVUCUWOUWPUYNUUT
      UWMUVGUYQUWRWLOQUYLUYRUUNUYSRUUNUWSUYLUWTSXEWNTXAXRXPXSXTYA $.

    gpgprismgr4cycl.f $e |- F = <" { <. 0 , 0 >. , <. 0 , 1 >. }
                                   { <. 0 , 1 >. , <. 1 , 1 >. }
                                   { <. 1 , 1 >. , <. 1 , 0 >. }
                                   { <. 1 , 0 >. , <. 0 , 0 >. } "> $.
    gpgprismgr4cycl.g $e |- G = ( N gPetersenGr 1 ) $.
    $( Lemma 8 for ~ gpgprismgr4cycl0 .  (Contributed by AV, 2-Nov-2025.) $)
    gpgprismgr4cycllem8 $p |- ( N e. ( ZZ>= ` 3 )
                                -> F e. Word dom ( iEdg ` G ) ) $=
      ( cfv wcel ciedg cdm cc0 cop c1 cpr wss wa prex sylbir syl c3 cuz cs3 cs4
      cs1 cconcat co df-s4 eqtri cun cgpg gpgprismgriedgdmss unss eqcomi fveq2i
      prss dmeqi eleq2i birani adantr prcom eleq12i adantl bilani s3cld 3eltr4g
      simpr cats1cld ) DUAUBHIZCJHZKZLLMZLNMZOZVMNNMZOZVONLMZOZUCZBVQVLOZBVNVPV
      RVTUDVSVTUEUFUGFVNVPVRVTUHUIVIVNVPVRVKVIVNVLVQOZOZVOVMOZVROZUJDNUKUGZJHZK
      ZPZVNVKIZDULZWHWBWGPZWDWGPZQZWIWBWDWGUMZWKWIWLWKVNWGIZWAWGIZQZWIVNWAWGVLV
      MRVLVQRUPZWOWIWPWGVKVNWFVJWECJCWEGUNUOUQZURUSSUTSTVIWHVPVKIZWJWHWMWTWNWLW
      TWKWLWCWGIZVRWGIZQZWTWCVRWGVOVMRVOVQRUPZXAWTXBWCVPWGVKVOVMVAWSVBUSSVCSTVI
      WHVRVKIZWJWHWMXEWNWLXEWKWLXCXEXDXBXEXAWGVKVRWSURVDSVCSTVEVIWHVTVKIZWJWHWM
      XFWNWKXFWLWKWAWGVTVKWKWQWPWRWOWPVGSVQVLVAVJWFCWEJGUOUQVFUTSTVH $.

    $( Lemma 9 for ~ gpgprismgr4cycl0 .  (Contributed by AV, 3-Nov-2025.) $)
    gpgprismgr4cycllem9 $p |- ( N e. ( ZZ>= ` 3 )
                                -> P : ( 0 ... ( # ` F ) ) --> ( Vtx ` G ) ) $=
      ( cfv wcel cc0 cfz co cvtx cfzo cop c1 a1i opelxpd wceq c4 c3 chash cword
      cuz wf cs5 cpr cxp cn eluz3nn lbfzo0 sylibr cn0 clt 1nn0 eluzelz uzuzle23
      cz wbr c2 eluz2gt1 elfzo0z syl3anbrc wa 0elpr01 simpl simpr 1elpr01 s5cld
      syl syl2anc cgpg fveq2i cdiv 1elfzo1ceilhalf1 eqid gpgvtx eqtrid eleqtrrd
      cceil wrdeq eqeltrid caddc fzval3 gpgprismgr4cycllem1 gpgprismgr4cycllem4
      wrdf 4z ax-mp oveq2i c5 df-5 eqtri 3eqtr4i feq2d mpbird ) DUAUDHIZJBUBHZK
      LZCMHZAUEJAUBHZNLZWTAUEZWQAWTUCZIXCWQAJJOZJPOZPPOZPJOZXEUFZXDEWQXIJPUGZJD
      NLZUHZUCZXDWQJXKIZPXKIZXIXMIWQDUIIZXNDUJZDUKULWQPUMIZDURIPDUNUSZXOXRWQUOQ
      UADUPWQDUTUDHIXSDUQDVAVJPDVBVCXNXOVDZXEXFXGXHXEXLXTJJXJXKJXJIXTVEQZXNXOVF
      ZRZXTJPXJXKYAXNXOVGZRXTPPXJXKPXJIXTVHQZYDRXTPJXJXKYEYBRYCVIVKWQWTXLSXDXMS
      WQWTDPVLLZMHZXLCYFMGVMWQXPPPDUTVNLVTHNLZIYGXLSXQDVOXKYHPDYHVPXKVPVQVKVRWT
      XLWAVJVSWBWTAWGVJWQWSXBWTAWSXBSWQJTKLZJTPWCLZNLZWSXBTURIYIYKSWHJTWDWIWRTJ
      KBFWEWJXAYJJNXAWKYJAEWFWLWMWJWNQWOWP $.

    $d F e x $.  $d N e x $.  $d X e x $.
    $( Lemma 10 for ~ gpgprismgr4cycl0 .  (Contributed by AV, 5-Nov-2025.) $)
    gpgprismgr4cycllem10 $p |- ( ( N e. ( ZZ>= ` 3 )
                                  /\ X e. ( 0 ..^ ( # ` F ) ) )
                                -> ( ( iEdg ` G ) ` ( F ` X ) )
                                   = { ( P ` X ) , ( P ` ( X + 1 ) ) } ) $=
      ( c3 cfv wcel cc0 co c1 cpr wceq c2 c4 cvv ax-mp ve vx cuz chash wa ciedg
      cfzo caddc cid cv cop cmo w3o wrex cxp cpw crab cres cgpg fveq2i a1i cdiv
      cn cceil eluz3nn 1elfzo1ceilhalf1 adantr eqid gpgiedg gpgprismgr4cycllem3
      jca eqtrd fveq1d gpgprismgr4cycllem1 oveq2i eleq2i anbi2i eqeq1 3orbi123d
      syl rexbidv elrab 3imtr4i fvresi wo cun fzo0to42pr elun 3bitri elpri prex
      cs4 s4fv0 fveq1i cs5 opex df-s5 s4cli s4len 0nn0 4pos cats1fv eqtri s4fv1
      1nn0 1lt4 preq12i 3eqtr4i fveq2 fv0p1e1 preq12d 3eqtr4a s4fv2 oveq1 1p1e2
      2nn0 2lt4 eqtrdi fveq2d jaoi s4fv3 3nn0 2p1e3 cats1fvn 3p1e4 sylbi adantl
      3lt4 ) DIUCJKZELBUDJZUGMZKZUEZEBJZCUFJZJZYNEAJZENUHMZAJZOZYMYPYNUIUAUJZLU
      BUJZUKZLUUBNUHMDULMZUKOZPZUUAUUCNUUBUKZOZPZUUAUUGNUUDUKOZPZUMZUBLDUGMZUNZ
      UALNOZUUMUOUPZUQZURZJZYNYMYNYOUURYMYODNUSMZUFJZUURYOUVAPYMCUUTUFHUTVAYMDV
      CKZNNDQVBMVDJUGMZKZUEZUVAUURPYIUVEYLYIUVBUVDDVEDVFVKVGUBUAUUMUVCNDUVCVHUU
      MVHVIVTVLVMYMYNUUQKZUUSYNPYIELRUGMZKZUEYNUUPKYNUUEPZYNUUHPZYNUUJPZUMZUBUU
      MUNZUEYMUVFUBBDEGVJYLUVHYIYKUVGEYJRLUGBGVNVOVPZVQUUNUVMUAYNUUPUUAYNPZUULU
      VLUBUUMUVOUUFUVIUUIUVJUUKUVKUUAYNUUEVRUUAYNUUHVRUUAYNUUJVRVSWAWBWCUUQYNWD
      VTVLYLYNYTPZYIYLEUUOKZEQIOZKZWEZUVPYLUVHEUUOUVRWFZKUVTUVNUVGUWAEWGVPEUUOU
      VRWHWIUVQUVPUVSUVQELPZENPZWEUVPELNWJUWBUVPUWCUWBLBJZLAJZNAJZOZYNYTLLLUKZL
      NUKZOZUWINNUKZOZUWKNLUKZOZUWMUWHOZWLZJZUWJUWDUWGUWJSKUWQUWJPUWHUWIWKUWJUW
      LUWNUWOSWMTLBUWPGWNUWEUWHUWFUWIUWELUWHUWIUWKUWMUWHWOZJZUWHLAUWRFWNUWHSKZU
      WSUWHPLLWPZUWHUWIUWKUWMWLZUWRRLSUWHUWHUWHUWIUWKUWMUWHWQZUWHUWIUWKUWMWRZUW
      HUWIUWKUWMWSZUWHUWIUWKUWMSWMWTXAXBTXCUWFNUWRJZUWINAUWRFWNUWISKUXFUWIPLNWP
      UXBUWRRNSUWHUWIUXCUXDUXEUWHUWIUWKUWMSXDXEXFXBTXCZXGXHELBXIUWBYQUWEYSUWFEL
      AXIAEXJXKXLUWCNBJZUWFQAJZOZYNYTNUWPJZUWLUXHUXJUWLSKUXKUWLPUWIUWKWKUWJUWLU
      WNUWOSXDTNBUWPGWNUWFUWIUXIUWKUXGUXIQUWRJZUWKQAUWRFWNUWKSKUXLUWKPNNWPUXBUW
      RRQSUWHUWKUXCUXDUXEUWHUWIUWKUWMSXMXPXQXBTXCZXGXHENBXIUWCYQUWFYSUXIENAXIUW
      CYRQAUWCYRNNUHMQENNUHXNXOXRXSXKXLXTVTUVSEQPZEIPZWEUVPEQIWJUXNUVPUXOUXNQBJ
      ZUXIIAJZOZYNYTQUWPJZUWNUXPUXRUWNSKUXSUWNPUWKUWMWKUWJUWLUWNUWOSXMTQBUWPGWN
      UXIUWKUXQUWMUXMUXQIUWRJZUWMIAUWRFWNUWMSKUXTUWMPNLWPUXBUWRRISUWHUWMUXCUXDU
      XEUWHUWIUWKUWMSYAYBYHXBTXCZXGXHEQBXIUXNYQUXIYSUXQEQAXIUXNYRIAUXNYRQNUHMIE
      QNUHXNYCXRXSXKXLUXOIBJZUXQRAJZOZYNYTIUWPJZUWOUYBUYDUWOSKUYEUWOPUWMUWHWKUW
      JUWLUWNUWOSYATIBUWPGWNUXQUWMUYCUWHUYAUYCRUWRJZUWHRAUWRFWNUWTUYFUWHPUXAUXB
      UWRRSUWHUXCUXDUXEYDTXCXGXHEIBXIUXOYQUXQYSUYCEIAXIUXOYRRAUXOYRINUHMREINUHX
      NYEXRXSXKXLXTVTXTYFYGVL $.

    $d F y $.  $d G x $.  $d N y $.  $d P x y $.
    $( Lemma 11 for ~ gpgprismgr4cycl0 .  (Contributed by AV, 5-Nov-2025.) $)
    gpgprismgr4cycllem11 $p |- ( N e. ( ZZ>= ` 3 ) -> F ( Cycles ` G ) P ) $=
      ( vx vy cfv wcel wbr cc0 chash c4 c1 cmin co cfzo cusgr c3 cuz cpths wceq
      ccycls cvv cword gpgprismgr4cycllem5 a1i gpgprismgr4cycllem4 oveq1i 5m1e4
      c5 eqtri eqcomi cv wne gpgprismgr4cycllem7 ralrimivva gpgprismgr4cycllem1
      wi wa adantl cwlks ccnv wfun ctrls ciedg cdm cfz cvtx gpgprismgr4cycllem8
      wf caddc cpr wral gpgprismgr4cycllem9 gpgprismgr4cycllem10 ralrimiva cgpg
      cupgr w3a gpgprismgrusgra eleq1i usgrupgr sylbir eqid upgriswlk mpbir3and
      3syl gpgprismgr4cycllem2 sylanblrc pthd gpgprismgr4cycllem6 fveq2i iscycl
      wb istrl ) DUAUBJKZBACUCJLMAJZBNJZAJZUDBACUEJLWSAOHIBCAUFUGKWSAEUHUIANJZP
      QRZOXDUMPQROXCUMPQAEUJUKULUNUOWSHUPZIUPZUQXEAJZXFAJUQVAZHIMXCSRZPOSRZXEXI
      KXFXJKVBXHWSAXEXFEURVCUSBFUTZWSBACVDJLZBVEVFBACVGJLWSXLBCVHJZVIUGKZMXAVJR
      CVKJZAVMZXEBJXMJXGXEPVNRAJVOUDZHMXASRZVPZABCDEFGVLABCDEFGVQWSXQHXRABCDXEE
      FGVRVSWSDPVTRZTKZCWAKZXLXNXPXSWBWQDWCYACTKYBCXTTGWDCWEWFAHBCXMXOXOWGXMWGW
      HWJWIBFWKABCWRWLWMWTOAJXBAEWNOXAAXAOXKUOWOUNABCWPWL $.

    $( The generalized Petersen graphs G(N,1), which are the N-prisms, have a
       cycle of length 4 starting at the vertex ` <. 0 , 0 >. ` .  (Contributed
       by AV, 5-Nov-2025.) $)
    gpgprismgr4cycl0 $p |- ( N e. ( ZZ>= ` 3 )
                             -> ( F ( Cycles ` G ) P /\ ( # ` F ) = 4 ) ) $=
      ( c3 cuz cfv ccycls wbr chash c4 gpgprismgr4cycllem11 gpgprismgr4cycllem1
      wcel wceq jctir ) DHIJQBACKJLBMJNRABCDEFGOBFPS $.
  $}

  ${
    $d N f p $.
    $( The generalized Petersen graphs G(N,1), which are the N-prisms, have (at
       least) one cycle of length 4.  (Contributed by AV, 5-Nov-2025.) $)
    gpgprismgr4cyclex $p |- ( N e. ( ZZ>= ` 3 )
                            -> E. p E. f ( f ( Cycles ` ( N gPetersenGr 1 ) ) p
                                           /\ ( # ` f ) = 4 ) ) $=
      ( cc0 cop c1 cs5 cvv wcel cpr wa cfv wbr chash c4 wceq cv wex eqid wb cs4
      cword c3 cgpg co ccycls s5cli s4cli pm3.2i gpgprismgr4cycl0 breq12 ancoms
      cuz fveqeq2 adantl anbi12d spc2egv mpsyl ) DDEZDFEZFFEZFDEZUSGZHUBZIZUSUT
      JZUTVAJZVAVBJZVBUSJZUAZVDIZKBUCUMLIVJVCBFUDUEZUFLZMZVJNLOPZKZAQZCQZVMMZVQ
      NLOPZKZARCRVEVKUSUTVAVBUSUGVFVGVHVIUHUIVCVJVLBVCSVJSVLSUJWAVPCAVCVJVDVDVR
      VCPZVQVJPZKVSVNVTVOWCWBVSVNTVQVJVRVCVMUKULWCVTVOTWBVQVJONUNUOUPUQUR $.
  $}

  ${
    pgnioedg1.g $e |- G = ( 5 gPetersenGr 2 ) $.
    pgnioedg1.e $e |- E = ( Edg ` G ) $.
    $( An inside and an outside vertex not adjacent in a Petersen graph.
       (Contributed by AV, 21-Nov-2025.) $)
    pgnioedg1 $p |- ( y e. ( 0 ..^ 5 )
                      -> -. { <. 1 , ( ( y - 2 ) mod 5 ) >.
                               , <. 0 , ( ( y + 1 ) mod 5 ) >. }
                            e. E ) $=
      ( cc0 c5 co wcel c1 c2 cmo cop cfv wceq wa eqid wi c0ex opth cv cfzo cmin
      caddc cpr c2nd w3o wn c3 cuz cdiv cceil c1st 5eluz3 pglem pm3.2i 1ex ovex
      op1st simpr cvtx gpgvtxedg1 mp3an12i ex wne eqneqall mpi adantr sylbi a1i
      0ne1 op2nd eqeq2i cz nnzi uzid ax-mp modm2nep1 mpan necomd syl5 simplbiim
      5nn com12 3jaod syld pm2.01d ) AUAZFGUBHZIZJWHKUCHZGLHZMZFWHJUDHZGLHZMZUE
      BIZWJWQWPJWMUFNZKUDHGLHZMOZWPFWRMOZWPJWRKUCHGLHZMOZUGZWQUHZWJWQXDGUIUJNIZ
      KJGKUKHULNUBHZIZPWMUMNJOWJWQPWQXDXFXHUNUOUPJWLUQWKGLURZUSWJWQUTBCXGKGCVAN
      ZWMWPXGQDXJQEVBVCVDWJWTXEXAXCWTXERWJWTFJOZWOWSOZPXEFWOJWSSWNGLURZTXKXEXLX
      KFJVEXEVKXEFJVFVGZVHVIVJXAWJXEXAFFOWOWROZWJXERZFWOFWRSXMTXOWOWLOZXPWRWLWO
      JWLUQXIVLVMWJWOWLVEXQXEWJWLWOGGUJNIZWJWLWOVEGVNIXRGWCVOGVPVQWIGWHWIQVRVSV
      TXEWOWLVFWAVIWBWDXCXERWJXCXKWOXBOZPXEFWOJXBSXMTXKXEXSXNVHVIVJWEWFWG $.

    $( An inside and an outside vertex not adjacent in a Petersen graph.
       (Contributed by AV, 21-Nov-2025.) $)
    pgnioedg2 $p |- ( y e. ( 0 ..^ 5 )
                      -> -. { <. 1 , ( ( y + 2 ) mod 5 ) >.
                               , <. 0 , ( ( y + 1 ) mod 5 ) >. }
                            e. E ) $=
      ( cc0 c5 co wcel c1 c2 caddc cmo cop cfv wceq wa eqid wi c0ex cv cfzo cpr
      c2nd cmin w3o wn cuz cdiv cceil c1st 5eluz3 pglem pm3.2i ovex op1st simpr
      c3 1ex cvtx gpgvtxedg1 mp3an12i ex opth wne eqneqall mpi adantr sylbi a1i
      0ne1 op2nd eqeq2i cz nnzi uzid ax-mp modp2nep1 necomd mpan syl5 simplbiim
      5nn com12 3jaod syld pm2.01d ) AUAZFGUBHZIZJWHKLHZGMHZNZFWHJLHZGMHZNZUCBI
      ZWJWQWPJWMUDOZKLHGMHZNPZWPFWRNPZWPJWRKUEHGMHZNPZUFZWQUGZWJWQXDGURUHOIZKJG
      KUIHUJOUBHZIZQWMUKOJPWJWQQWQXDXFXHULUMUNJWLUSWKGMUOZUPWJWQUQBCXGKGCUTOZWM
      WPXGRDXJREVAVBVCWJWTXEXAXCWTXESWJWTFJPZWOWSPZQXEFWOJWSTWNGMUOZVDXKXEXLXKF
      JVEXEVKXEFJVFVGZVHVIVJXAWJXEXAFFPWOWRPZWJXESZFWOFWRTXMVDXOWOWLPZXPWRWLWOJ
      WLUSXIVLVMWJWOWLVEZXQXEGGUHOIZWJXRGVNIXSGWCVOGVPVQXSWJQWLWOWIGWHWIRVRVSVT
      XEWOWLVFWAVIWBWDXCXESWJXCXKWOXBPZQXEFWOJXBTXMVDXKXEXTXNVHVIVJWEWFWG $.

    $( An inside and an outside vertex not adjacent in a Petersen graph.
       (Contributed by AV, 21-Nov-2025.) $)
    pgnioedg3 $p |- ( y e. ( 0 ..^ 5 )
                      -> -. { <. 1 , ( ( y + 2 ) mod 5 ) >.
                               , <. 0 , ( ( y - 1 ) mod 5 ) >. }
                            e. E ) $=
      ( cc0 c5 co wcel c1 c2 cmo cop cfv wceq wa eqid wi c0ex opth cv cfzo cmin
      caddc cpr c2nd w3o wn c3 cuz cdiv cceil c1st 5eluz3 pglem pm3.2i 1ex ovex
      op1st simpr cvtx gpgvtxedg1 mp3an12i ex wne eqneqall mpi adantr sylbi a1i
      0ne1 op2nd eqeq2i 5nn nnzi uzid ax-mp modm1nep2 mpan syl5 simplbiim com12
      cz 3jaod syld pm2.01d ) AUAZFGUBHZIZJWGKUDHZGLHZMZFWGJUCHZGLHZMZUEBIZWIWP
      WOJWLUFNZKUDHGLHZMOZWOFWQMOZWOJWQKUCHGLHZMOZUGZWPUHZWIWPXCGUIUJNIZKJGKUKH
      ULNUBHZIZPWLUMNJOWIWPPWPXCXEXGUNUOUPJWKUQWJGLURZUSWIWPUTBCXFKGCVANZWLWOXF
      QDXIQEVBVCVDWIWSXDWTXBWSXDRWIWSFJOZWNWROZPXDFWNJWRSWMGLURZTXJXDXKXJFJVEXD
      VKXDFJVFVGZVHVIVJWTWIXDWTFFOWNWQOZWIXDRZFWNFWQSXLTXNWNWKOZXOWQWKWNJWKUQXH
      VLVMWIWNWKVEZXPXDGGUJNIZWIXQGWCIXRGVNVOGVPVQWHGWGWHQVRVSXDWNWKVFVTVIWAWBX
      BXDRWIXBXJWNXAOZPXDFWNJXASXLTXJXDXSXMVHVIVJWDWEWF $.

    $( An inside and an outside vertex not adjacent in a Petersen graph.
       (Contributed by AV, 21-Nov-2025.) $)
    pgnioedg4 $p |- ( y e. ( 0 ..^ 5 )
                      -> -. { <. 1 , ( ( y - 2 ) mod 5 ) >.
                               , <. 0 , ( ( y - 1 ) mod 5 ) >. }
                            e. E ) $=
      ( cc0 c5 co wcel c1 c2 cmin cmo cop cfv wceq wa eqid wi c0ex cv cfzo c2nd
      cpr caddc w3o wn cuz cdiv cceil c1st 5eluz3 pglem pm3.2i ovex op1st simpr
      c3 1ex cvtx gpgvtxedg1 mp3an12i ex opth wne eqneqall mpi adantr sylbi a1i
      0ne1 op2nd eqeq2i 5nn nnzi uzid ax-mp modm1nem2 mpan syl5 simplbiim com12
      cz 3jaod syld pm2.01d ) AUAZFGUBHZIZJWGKLHZGMHZNZFWGJLHZGMHZNZUDBIZWIWPWO
      JWLUCOZKUEHGMHZNPZWOFWQNPZWOJWQKLHGMHZNPZUFZWPUGZWIWPXCGURUHOIZKJGKUIHUJO
      UBHZIZQWLUKOJPWIWPQWPXCXEXGULUMUNJWKUSWJGMUOZUPWIWPUQBCXFKGCUTOZWLWOXFRDX
      IREVAVBVCWIWSXDWTXBWSXDSWIWSFJPZWNWRPZQXDFWNJWRTWMGMUOZVDXJXDXKXJFJVEXDVK
      XDFJVFVGZVHVIVJWTWIXDWTFFPWNWQPZWIXDSZFWNFWQTXLVDXNWNWKPZXOWQWKWNJWKUSXHV
      LVMWIWNWKVEZXPXDGGUHOIZWIXQGWCIXRGVNVOGVPVQWHGWGWHRVRVSXDWNWKVFVTVIWAWBXB
      XDSWIXBXJWNXAPZQXDFWNJXATXLVDXJXDXSXMVHVIVJWDWEWF $.

    $( An inside and an outside vertex not adjacent in a Petersen graph.
       (Contributed by AV, 21-Nov-2025.) $)
    pgnioedg5 $p |- ( y e. ( 0 ..^ 5 )
                      -> -. { <. 1 , ( ( y - 1 ) mod 5 ) >.
                               , <. 0 , ( ( y + 1 ) mod 5 ) >. }
                            e. E ) $=
      ( cc0 c5 co wcel c1 cmo cop cfv c2 wceq wa eqid wi c0ex opth cv cfzo cmin
      caddc cpr c2nd w3o wn c3 cuz cdiv cceil c1st 5eluz3 pglem pm3.2i 1ex ovex
      op1st simpr cvtx gpgvtxedg1 mp3an12i ex wne eqneqall mpi adantr sylbi a1i
      0ne1 op2nd eqeq2i modm1nep1 mpan necomd syl5 simplbiim com12 syld pm2.01d
      3jaod ) AUAZFGUBHZIZJWCJUCHZGKHZLZFWCJUDHZGKHZLZUEBIZWEWLWKJWHUFMZNUDHGKH
      ZLOZWKFWMLOZWKJWMNUCHGKHZLOZUGZWLUHZWEWLWSGUIUJMIZNJGNUKHULMUBHZIZPWHUMMJ
      OWEWLPWLWSXAXCUNUOUPJWGUQWFGKURZUSWEWLUTBCXBNGCVAMZWHWKXBQDXEQEVBVCVDWEWO
      WTWPWRWOWTRWEWOFJOZWJWNOZPWTFWJJWNSWIGKURZTXFWTXGXFFJVEWTVKWTFJVFVGZVHVIV
      JWPWEWTWPFFOWJWMOZWEWTRZFWJFWMSXHTXJWJWGOZXKWMWGWJJWGUQXDVLVMWEWJWGVEXLWT
      WEWGWJXAWEWGWJVEUNWDGWCWDQVNVOVPWTWJWGVFVQVIVRVSWRWTRWEWRXFWJWQOZPWTFWJJW
      QSXHTXFWTXMXIVHVIVJWBVTWA $.
  $}

  ${
    $d b y $.
    pgnbgreunbgr.g $e |- G = ( 5 gPetersenGr 2 ) $.
    pgnbgreunbgr.v $e |- V = ( Vtx ` G ) $.
    pgnbgreunbgr.e $e |- E = ( Edg ` G ) $.
    pgnbgreunbgr.n $e |- N = ( G NeighbVtx X ) $.
    $( Lemma 1 for ~ pgnbgreunbgr .  (Contributed by AV, 15-Nov-2025.) $)
    pgnbgreunbgrlem1 $p |- ( ( L = <. 0 , ( ( ( 2nd ` X ) + 1 ) mod 5 ) >.
                            \/ L = <. 1 , ( 2nd ` X ) >.
                            \/ L = <. 0 , ( ( ( 2nd ` X ) - 1 ) mod 5 ) >. )
                        -> ( ( K = <. 0 , ( ( ( 2nd ` X ) + 1 ) mod 5 ) >.
                            \/ K = <. 1 , ( 2nd ` X ) >.
                            \/ K = <. 0 , ( ( ( 2nd ` X ) - 1 ) mod 5 ) >. )
        -> ( ( X e. V /\ X = <. 0 , y >. )
             -> ( ( K =/= L /\ ( b e. ( 0 ..^ 5 ) /\ y e. ( 0 ..^ 5 ) ) )
                  -> ( ( { K , <. 0 , b >. } e. E /\ { <. 0 , b >. , L } e. E )
                       -> X = <. 0 , b >. ) ) ) ) ) $=
      ( wcel cc0 wceq wa co c5 wi cv cop c2nd cfv c1 caddc cmo cmin w3o wne cpr
      cfzo c0ex op2ndd oveq1 oveq1d opeq2d eqeq2d opeq2 3orbi123d anbi12d simpr
      vex simpl neeq12d eqid eqneqall ax-mp biimtrdi impd ex c3 cuz c2 cceil wb
      cdiv 5eluz3 pglem gpgedgiov mpanl12 eqcoms adantld preq1 eleq1d bi2anan9r
      preq2 imbi1d imbitrrid prcom eleq1i anbi12ci nnzi uzid gpgedg2ov equcomiv
      cz 5nn biimtrid 3jaoi adantrd adantl adantr a1i ancoms anbi1d eqeq2 3jaod
      3imtr4d imp syl eqeq1 imbi2d sylibrd expdcom ) HGNZHOAUAZUBZPZQEOHUCUDZUE
      UFRZSUGRZUBZPZEUEXTUBZPZEOXTUEUHRZSUGRZUBZPZUIZDYCPZDYEPZDYIPZUIZDEUJZIUA
      ZOSULRZNXQYRNQZQZDOYQUBZUKZBNZUUAEUKZBNZQZHUUAPZTZTZXSYKYOQZUUITXPXSUUJYT
      UUFXRUUAPZTZTZUUIXSXTXQPZUUJUUMTOXQHUMAVCUNUUNUUJEOXQUEUFRZSUGRZUBZPZEUEX
      QUBZPZEOXQUEUHRZSUGRZUBZPZUIZDUUQPZDUUSPZDUVCPZUIZQUUMUUNYKUVEYOUVIUUNYDU
      URYFUUTYJUVDUUNYCUUQEUUNYBUUPOUUNYAUUOSUGXTXQUEUFUOUPUQZURUUNYEUUSEXTXQUE
      USZURUUNYIUVCEUUNYHUVBOUUNYGUVASUGXTXQUEUHUOUPUQZURUTUUNYLUVFYMUVGYNUVHUU
      NYCUUQDUVJURUUNYEUUSDUVKURUUNYIUVCDUVLURUTVAUVEUVIUUMUVEUVFUUMUVGUVHUURUV
      FUUMTUUTUVDUURUVFUUMUURUVFQZYPYSUULUVMYPUUQUUQUJZYSUULTZUVMDUUQEUUQUURUVF
      VBUURUVFVDVEUUQUUQPUVNUVOTUUQVFUVOUUQUUQVGVHVIVJVKUUTUVFUUMUUTUVFQZYSUULY
      PYSUULUVPUUQUUAUKZBNZUUAUUSUKZBNZQZUUKTYSUVTUUKUVRYSUVTYQXQPZUUKSVLVMUDNV
      NUESVNVQRVOUDULRZNZYSUVTUWBVPVRVSBCYRUWCVNSYQXQUWCVFZYRVFZJLVTWAUUKXQYQXQ
      YQOUSWBZVIZWCUVPUUFUWAUUKUVFUUCUVRUUTUUEUVTUVFUUBUVQBDUUQUUAWDWEZUUTUUDUV
      SBEUUSUUAWGWEZWFWHWIWCVKUVDUVFUUMUVDUVFQZYSUULYPYSUULUWKUVRUUAUVCUKZBNZQZ
      UUKTUWNUVCUUAUKZBNZUUAUUQUKZBNZQZYSUUKUVRUWRUWMUWPUVQUWQBUUQUUAWJWKUWLUWO
      BUUAUVCWJWKWLYSUWSUWBUUKSSVMUDNZUWDYSUWSUWBVPSWQNUWTSWRWMSWNVHVSBCYRUWCVN
      SYQXQUWEUWFJLWOWAZUWBXQYQOIAWPUQVIWSUWKUUFUWNUUKUVFUUCUVRUVDUUEUWMUWIUVDU
      UDUWLBEUVCUUAWGZWEWFWHWIWCVKWTUURUVGUUMTUUTUVDUURUVGUUMUURUVGQZYSUULYPYSU
      ULUXCUUSUUAUKZBNZUWRQZUUKTYSUXEUUKUWRUXEUVTYSUUKUXDUVSBUUSUUAWJWKUWHWSZXA
      UXCUUFUXFUUKUVGUUCUXEUURUUEUWRUVGUUBUXDBDUUSUUAWDZWEUURUUDUWQBEUUQUUAWGWE
      ZWFWHWIWCVKUUTUVGUUMUUTUVGQZYPYSUULUXJYPUUSUUSUJZUVOUXJDUUSEUUSUUTUVGVBUU
      TUVGVDVEUUSUUSPUXKUVOTUUSVFUVOUUSUUSVGVHVIVJVKUVDUVGUUMUVDUVGQZYSUULYPYSU
      ULUXLUXEUWMQZUUKTYSUXEUUKUWMUXGXAUXLUUFUXMUUKUXLUUCUXEUUEUWMUXLUUBUXDBUVG
      UUBUXDPUVDUXHXBWEUXLUUDUWLBUVDUUDUWLPUVGUXBXCWEVAWHWIWCVKWTUURUVHUUMTUUTU
      VDUURUVHUUMUURUVHQZUVCUUQUJZYSQZUWSUUKTZYTUULUXPUXQTUXNYSUXQUXOYSUWSUWBUU
      KUXAUWGVIXBXDUXNYPUXOYSUVHUURYPUXOVPUVHUURQDUVCEUUQUVHUURVDUVHUURVBVEXEXF
      UXNUUFUWSUUKUVHUUCUWPUURUUEUWRUVHUUBUWOBDUVCUUAWDZWEUXIWFWHXIVKUUTUVHUUMY
      TUULUUTUVHQZUWPUVTQZUUKTZYSUYAYPYSUVTUUKUWPUWHWCXBUXSUUFUXTUUKUXSUUCUWPUU
      EUVTUXSUUBUWOBUVHUUBUWOPUUTUXRXBWEUUTUUEUVTVPUVHUWJXCVAWHWIVKUVDUVHDEPZUU
      MUVHUYBVPUVCEUVCEDXGWBUYBYPYSUULUVODEVGVJVIWTXHXJVIXKXSUUHUULYTXSUUGUUKUU
      FHXRUUAXLXMXMXNXBXO $.

    $( Lemma 1 for ~ pgnbgreunbgrlem2 .  (Contributed by AV, 16-Nov-2025.) $)
    pgnbgreunbgrlem2lem1 $p |- ( ( ( ( L = <. 1 , ( ( y + 2 ) mod 5 ) >.
                                    /\ K = <. 0 , y >. )
                                  /\ ( b e. ( 0 ..^ 5 ) /\ y e. ( 0 ..^ 5 ) ) )
                                    /\ { K , <. 0 , b >. } e. E )
                                  -> -. { <. 0 , b >. , L } e. E ) $=
      ( c1 co c5 cmo wceq cc0 c3 cv c2 caddc cop wa cfzo wcel cpr c2nd cfv cmin
      wn wi w3o cdiv cceil c1st 5eluz3 pglem pm3.2i c0ex op1st simpr gpgvtxedg0
      cuz vex eqid mp3an12i ex mp3an12 1ex ovex wne ax-1ne0 eqneqall mpi adantr
      opth sylbi op2nd eqeq2i eqcom bitri oveq1i opeq2i wb eqeq1 cz cn elfzoelz
      a1i zaddcld 1zzd 5nn difmod0 syl3anc zcnd 2cnd 1cnd pnpcand eqtrdi oveq1d
      2z 2m1e1 eqeq1d 3bitr2d cr crp cle wbr clt 1re 5rp 0le1 1lt5 modid eqeq1i
      mp4an biimtrdi ad2antll sylbid simplbiim 0ne1 w3a bicomd cneg subsubadd23
      zsubcld subidd 1p2e3 oveq12d df-neg eqtr4di eqtrd 3re negmod0 mp2an 3jaoi
      adantl eleq1d 0re 3pos ltleii 3lt5 3ne0 sylbir impd syl ax-1 pm2.61i syld
      com13 preq1 preq2 notbid imbi12d mpbird imp ) ENAUAZUBUCOZPQOZUDZRZDSUUSU
      DZRZUEZIUAZSPUFOZUGZUUSUVHUGZUEZUEZDSUVGUDZUHZBUGZUVMEUHZBUGZULZUVLUVOUVR
      UMZUVDUVMUHZBUGZUVMUVBUHZBUGZULZUMZUVKUWEUVFUVKUWAUVMSUVDUIUJZNUCOZPQOZUD
      ZRZUVMNUWFUDRZUVMSUWFNUKOZPQOZUDZRZUNZUWDUVKUWAUWPPTVEUJUGZUBNPUBUOOUPUJU
      FOZUGZUEZUVDUQUJSRUVKUWAUEUWAUWPUWQUWSURUSUTZSUUSVAAVFZVBUVKUWAVCBCUWRUBP
      GUVDUVMUWRVGZJKLVDVHVIUVKUWPUWDUWCUVKUWPUEZUWDUMZUWCUVBSUVMUIUJZNUCOPQOZU
      DRZUVBNUXFUDRZUVBSUXFNUKOPQOZUDRZUNZUXEUWTUVMUQUJSRUWCUXLUXASUVGVAIVFZVBB
      CUWRUBPGUVMUVBUXCJKLVDVJUXHUXEUXIUXKUXHNSRZUVAUXGRZUEUXENUVASUXGVKUUTPQVL
      ZVRUXNUXEUXOUXNNSVMZUXEVNUXENSVOVPZVQVSUXINNRUVAUXFRZUXENUVANUXFVKUXPVRUX
      SUVGUVARZUXEUXSUVAUVGRUXTUXFUVGUVASUVGVAUXMVTWAUVAUVGWBWCUXTUVKUWPUWDUWPU
      VKUXTUWDUWJUVKUXTUWDUMZUMZUWKUWOUWJSSRZUVGUUSNUCOZPQOZRZUYBUWJUVMSUYEUDZR
      UYCUYFUEUWIUYGUVMUWHUYESUWGUYDPQUWFUUSNUCSUUSVAUXBVTZWDWDWEWASUVGSUYEVAUX
      MVRWCUYFUVKUYAUYFUVKUEUXTUYEUVARZUWDUYFUXTUYIWFUVKUVGUYEUVAWGVQUVJUYIUWDU
      MUYFUVIUVJUYINPQOZSRZUWDUVJUYIUVAUYERZUUTUYDUKOZPQOZSRZUYKUYIUYLWFUVJUYEU
      VAWBWKUVJUUTWHUGZUYDWHUGPWIUGZUYOUYLWFUVJUUSUBUUSSPWJZUBWHUGUVJXCWKWLZUVJ
      UUSNUYRUVJWMZWLUYQUVJWNWKZUUTUYDPWOWPUVJUYNUYJSUVJUYMNPQUVJUYMUBNUKONUVJU
      USUBNUVJUUSUYRWQZUVJWRZUVJWSZWTXDXAXBXEXFUYKUXNUWDUYJNSNXGUGPXHUGZSNXIXJN
      PXKXJUYJNRXLXMXNXONPXPXRXQUXNUXQUWDVNUWDNSVOVPVSXSXTYAVIYBUWKSNRZUVGUWFRZ
      UEUYBSUVGNUWFVAUXMVRVUFUYBVUGVUFSNVMUYBYCUYBSNVOVPVQVSUWOUVMSUUSNUKOZPQOZ
      UDZRZUYBUWNVUJUVMUWMVUISUWLVUHPQUWFUUSNUKUYHWDWDWEWAVUKUYCUVGVUIRZUYBSUVG
      SVUIVAUXMVRVULUVKUYAVULUVKUEUXTVUIUVARZUWDVULUXTVUMWFUVKUVGVUIUVAWGVQUVJV
      UMUWDUMVULUVIUVJVUMVUHUUTUKOZPQOZSRZUWDUVJVUHWHUGZUYPUYQVUMVUPWFUVJUUSNUY
      RUYTYHUYSVUAVUQUYPUYQYDVUPVUMVUHUUTPWOYEWPUVJVUPTYFZPQOZSRZUWDUVJVUOVUSSU
      VJVUNVURPQUVJVUNUUSUUSUKOZNUBUCOZUKOZVURUVJUUSNUUSUBVUBVUDVUBVUCYGUVJVVCS
      TUKOVURUVJVVASVVBTUKUVJUUSVUBYIVVBTRUVJYJWKYKTYLYMYNXBXEVUTTPQOZSRZUWDTXG
      UGZVUEVVEVUTWFYOXMTPYPYQVVETSRZUWDVVDTSVVFVUESTXIXJTPXKXJVVDTRYOXMSTUUAYO
      UUBUUCUUDTPXPXRXQVVGTSVMUWDUUEUWDTSVOVPVSUUFXSYAXTYAVIYBVSYRUULUUGVSYBUXK
      UXNUVAUXJRZUEUXENUVASUXJVKUXPVRUXNUXEVVHUXRVQVSYRUUHUWDUXDUUIUUJVIUUKYSUV
      FUVSUWEWFUVKUVFUVOUWAUVRUWDUVEUVOUWAWFUVCUVEUVNUVTBDUVDUVMUUMYTYSUVCUVRUW
      DWFUVEUVCUVQUWCUVCUVPUWBBEUVBUVMUUNYTUUOVQUUPVQUUQUUR $.

    $( Lemma 2 for ~ pgnbgreunbgrlem2 .  (Contributed by AV, 16-Nov-2025.) $)
    pgnbgreunbgrlem2lem2 $p |- ( ( ( ( L = <. 1 , ( ( y - 2 ) mod 5 ) >.
                                    /\ K = <. 0 , y >. )
                                  /\ ( b e. ( 0 ..^ 5 ) /\ y e. ( 0 ..^ 5 ) ) )
                                    /\ { K , <. 0 , b >. } e. E )
                                  -> -. { <. 0 , b >. , L } e. E ) $=
      ( c1 co c5 cmo wceq cc0 c3 cv c2 cmin cop wa cfzo wcel cpr wn wi c2nd cfv
      caddc w3o cdiv cceil c1st 5eluz3 pglem pm3.2i c0ex op1st simpr gpgvtxedg0
      cuz vex eqid mp3an12i ex mp3an12 1ex ovex wne ax-1ne0 eqneqall mpi adantr
      opth sylbi op2nd eqeq2i eqcom bitri oveq1i opeq2i wb eqeq1 cneg a1i cz cn
      elfzoelz 2z zsubcld peano2zd difmod0 syl3anc zcnd 2cnd subsubadd23 subidd
      5nn 1cnd 2p1e3 oveq12d df-neg eqtr4di eqtrd oveq1d eqeq1d 3bitr2d crp 3re
      cr 5rp negmod0 mp2an cle wbr clt 0re 3pos ltleii 3lt5 modid eqeq1i bitr3i
      mp4an 3ne0 biimtrdi ad2antll sylbid simplbiim 0ne1 1zzd w3a bicomd adantl
      3jaoi eleq1d nnncan1d 2m1e1 eqtrdi 1re 0le1 1lt5 com13 impd syl ax-1 syld
      pm2.61i preq1 preq2 notbid imbi12d mpbird imp ) ENAUAZUBUCOZPQOZUDZRZDSUU
      SUDZRZUEZIUAZSPUFOZUGZUUSUVHUGZUEZUEZDSUVGUDZUHZBUGZUVMEUHZBUGZUIZUVLUVOU
      VRUJZUVDUVMUHZBUGZUVMUVBUHZBUGZUIZUJZUVKUWEUVFUVKUWAUVMSUVDUKULZNUMOZPQOZ
      UDZRZUVMNUWFUDRZUVMSUWFNUCOZPQOZUDZRZUNZUWDUVKUWAUWPPTVEULUGZUBNPUBUOOUPU
      LUFOZUGZUEZUVDUQULSRUVKUWAUEUWAUWPUWQUWSURUSUTZSUUSVAAVFZVBUVKUWAVCBCUWRU
      BPGUVDUVMUWRVGZJKLVDVHVIUVKUWPUWDUWCUVKUWPUEZUWDUJZUWCUVBSUVMUKULZNUMOPQO
      ZUDRZUVBNUXFUDRZUVBSUXFNUCOPQOZUDRZUNZUXEUWTUVMUQULSRUWCUXLUXASUVGVAIVFZV
      BBCUWRUBPGUVMUVBUXCJKLVDVJUXHUXEUXIUXKUXHNSRZUVAUXGRZUEUXENUVASUXGVKUUTPQ
      VLZVRUXNUXEUXOUXNNSVMZUXEVNUXENSVOVPZVQVSUXINNRUVAUXFRZUXENUVANUXFVKUXPVR
      UXSUVGUVARZUXEUXSUVAUVGRUXTUXFUVGUVASUVGVAUXMVTWAUVAUVGWBWCUXTUVKUWPUWDUW
      PUVKUXTUWDUWJUVKUXTUWDUJZUJZUWKUWOUWJSSRZUVGUUSNUMOZPQOZRZUYBUWJUVMSUYEUD
      ZRUYCUYFUEUWIUYGUVMUWHUYESUWGUYDPQUWFUUSNUMSUUSVAUXBVTZWDWDWEWASUVGSUYEVA
      UXMVRWCUYFUVKUYAUYFUVKUEUXTUYEUVARZUWDUYFUXTUYIWFUVKUVGUYEUVAWGVQUVJUYIUW
      DUJUYFUVIUVJUYITWHZPQOZSRZUWDUVJUYIUVAUYERZUUTUYDUCOZPQOZSRZUYLUYIUYMWFUV
      JUYEUVAWBWIUVJUUTWJUGZUYDWJUGPWKUGZUYPUYMWFUVJUUSUBUUSSPWLZUBWJUGUVJWMWIW
      NZUVJUUSUYSWOUYRUVJXBWIZUUTUYDPWPWQUVJUYOUYKSUVJUYNUYJPQUVJUYNUUSUUSUCOZU
      BNUMOZUCOZUYJUVJUUSUBUUSNUVJUUSUYSWRZUVJWSZVUEUVJXCZWTUVJVUDSTUCOUYJUVJVU
      BSVUCTUCUVJUUSVUEXAVUCTRUVJXDWIXETXFXGXHXIXJXKUYLTSRZUWDUYLTPQOZSRZVUHTXN
      UGZPXLUGZVUJUYLWFXMXOTPXPXQVUITSVUKVULSTXRXSTPXTXSVUITRXMXOSTYAXMYBYCYDTP
      YEYHYFYGVUHTSVMUWDYIUWDTSVOVPVSYJYKYLVIYMUWKSNRZUVGUWFRZUEUYBSUVGNUWFVAUX
      MVRVUMUYBVUNVUMSNVMUYBYNUYBSNVOVPVQVSUWOUVMSUUSNUCOZPQOZUDZRZUYBUWNVUQUVM
      UWMVUPSUWLVUOPQUWFUUSNUCUYHWDWDWEWAVURUYCUVGVUPRZUYBSUVGSVUPVAUXMVRVUSUVK
      UYAVUSUVKUEUXTVUPUVARZUWDVUSUXTVUTWFUVKUVGVUPUVAWGVQUVJVUTUWDUJVUSUVIUVJV
      UTVUOUUTUCOZPQOZSRZUWDUVJVUOWJUGZUYQUYRVUTVVCWFUVJUUSNUYSUVJYOWNUYTVUAVVD
      UYQUYRYPVVCVUTVUOUUTPWPYQWQUVJVVCNPQOZSRZUWDUVJVVBVVESUVJVVANPQUVJVVAUBNU
      CONUVJUUSNUBVUEVUGVUFUUAUUBUUCXIXJVVFUXNUWDVVENSNXNUGVULSNXRXSNPXTXSVVENR
      UUDXOUUEUUFNPYEYHYFUXNUXQUWDVNUWDNSVOVPVSYJYLYKYLVIYMVSYSUUGUUHVSYMUXKUXN
      UVAUXJRZUEUXENUVASUXJVKUXPVRUXNUXEVVGUXRVQVSYSUUIUWDUXDUUJUULVIUUKYRUVFUV
      SUWEWFUVKUVFUVOUWAUVRUWDUVEUVOUWAWFUVCUVEUVNUVTBDUVDUVMUUMYTYRUVCUVRUWDWF
      UVEUVCUVQUWCUVCUVPUWBBEUVBUVMUUNYTUUOVQUUPVQUUQUUR $.

    $( Lemma 3 for ~ pgnbgreunbgrlem2 .  (Contributed by AV, 17-Nov-2025.) $)
    pgnbgreunbgrlem2lem3 $p |- ( ( ( ( L = <. 1 , ( ( y + 2 ) mod 5 ) >.
                                    /\ K = <. 1 , ( ( y - 2 ) mod 5 ) >. )
                                  /\ ( b e. ( 0 ..^ 5 ) /\ y e. ( 0 ..^ 5 ) ) )
                                    /\ { K , <. 0 , b >. } e. E )
                                  -> -. { <. 0 , b >. , L } e. E ) $=
      ( c1 c2 co c5 wceq cc0 wcel cv caddc cmo cop cmin wa cfzo cpr wn c2nd cfv
      wi w3o wb prcom eleq1i a1i c3 cuz cdiv cceil c1st 5eluz3 pglem pm3.2i vex
      c0ex op1st eqid gpgvtxedg0 mp3an12 biimtrdi 1ex ovex wne ax-1ne0 eqneqall
      opth adantr sylbi op2nd eqeq2i eqeq2 eqcoms adantl cz cn elfzoelz zaddcld
      mpi 2z zsubcld 5nn w3a difmod0 bicomd syl3anc c4 zcnd 2cnd pnncand eqtrdi
      2p2e4 oveq1d eqeq1d cr crp cle wbr clt 4re 5rp 0re 4pos ltleii 4lt5 modid
      mp4an eqeq1i 4ne0 necon2bi sylbid ex com12 simplbiim 3jaoi com13 impd syl
      ax-1 pm2.61i syld preq1 eleq1d preq2 notbid imbi12d mpbird imp ) ENAUAZOU
      BPZQUCPZUDZRZDNYTOUEPZQUCPZUDZRZUFZIUAZSQUGPZTZYTUUKTZUFZUFZDSUUJUDZUHZBT
      ZUUPEUHZBTZUIZUUOUURUVAULZUUGUUPUHZBTZUUPUUCUHZBTZUIZULZUUNUVHUUIUUNUVDUU
      GSUUPUJUKZNUBPQUCPZUDZRZUUGNUVIUDZRZUUGSUVINUEPQUCPZUDZRZUMZUVGUUNUVDUUPU
      UGUHZBTZUVRUVDUVTUNUUNUVCUVSBUUGUUPUOUPUQQURUSUKTZONQOUTPVAUKUGPZTZUFZUUP
      VBUKSRZUVTUVRUWAUWCVCVDVEZSUUJVGIVFZVHZBCUWBOQGUUPUUGUWBVIZJKLVJVKVLUUNUV
      RUVGUVFUUNUVRUFZUVGULZUVFUUCUVKRZUUCUVMRZUUCUVPRZUMZUWKUWDUWEUVFUWOUWFUWH
      BCUWBOQGUUPUUCUWIJKLVJVKUWLUWKUWMUWNUWLNSRZUUBUVJRZUFUWKNUUBSUVJVMUUAQUCV
      NZVRUWPUWKUWQUWPNSVOZUWKVPUWKNSVQWJZVSVTUWMNNRZUUBUVIRZUWKNUUBNUVIVMUWRVR
      UXBUUBUUJRZUWKUVIUUJUUBSUUJVGUWGWAZWBUXCUUNUVRUVGUVRUUNUXCUVGUVLUUNUXCUVG
      ULZULZUVNUVQUVLUWPUUFUVJRZUFUXFNUUFSUVJVMUUEQUCVNZVRUWPUXFUXGUWPUWSUXFVPU
      XFNSVQWJZVSVTUVNUXAUUFUVIRZUXFNUUFNUVIVMUXHVRUXJUUFUUJRZUXFUVIUUJUUFUXDWB
      UUNUXKUXEUUMUXKUXEULUULUUMUXKUXEUUMUXKUFUXCUUBUUFRZUVGUXKUXCUXLUNZUUMUXMU
      UJUUFUUJUUFUUBWCWDWEUUMUXLUVGULUXKUUMUXLUUAUUEUEPZQUCPZSRZUVGUUMUUAWFTZUU
      EWFTZQWGTZUXLUXPUNUUMYTOYTSQWHZOWFTUUMWKUQZWIUUMYTOUXTUYAWLUXSUUMWMUQUXQU
      XRUXSWNUXPUXLUUAUUEQWOWPWQUUMUXPWRQUCPZSRZUVGUUMUXOUYBSUUMUXNWRQUCUUMUXNO
      OUBPWRUUMYTOOUUMYTUXTWSUUMWTZUYDXAXCXBXDXEUYCWRSRUVGUYBWRSWRXFTQXGTSWRXHX
      IWRQXJXIUYBWRRXKXLSWRXMXKXNXOXPWRQXQXRXSUVFWRSWRSVOUVFXTUQYAVTVLYBVSYBYCW
      EYDVTYEUVQUWPUUFUVORZUFUXFNUUFSUVOVMUXHVRUWPUXFUYEUXIVSVTYFYGYHVTYEUWNUWP
      UUBUVORZUFUWKNUUBSUVOVMUWRVRUWPUWKUYFUWTVSVTYFYIUVGUWJYJYKYCYLWEUUIUVBUVH
      UNUUNUUIUURUVDUVAUVGUUHUURUVDUNUUDUUHUUQUVCBDUUGUUPYMYNWEUUDUVAUVGUNUUHUU
      DUUTUVFUUDUUSUVEBEUUCUUPYOYNYPVSYQVSYRYS $.

    $( Lemma 2 for ~ pgnbgreunbgr .  Impossible cases.  (Contributed by AV,
       18-Nov-2025.) $)
    pgnbgreunbgrlem2 $p |- ( ( L = <. 1 , ( ( ( 2nd ` X ) + 2 ) mod 5 ) >.
                            \/ L = <. 0 , ( 2nd ` X ) >.
                            \/ L = <. 1 , ( ( ( 2nd ` X ) - 2 ) mod 5 ) >. )
                        -> ( ( K = <. 1 , ( ( ( 2nd ` X ) + 2 ) mod 5 ) >.
                            \/ K = <. 0 , ( 2nd ` X ) >.
                            \/ K = <. 1 , ( ( ( 2nd ` X ) - 2 ) mod 5 ) >. )
        -> ( ( X = <. 1 , y >. /\ X e. V )
             -> ( ( K =/= L /\ ( b e. ( 0 ..^ 5 ) /\ y e. ( 0 ..^ 5 ) ) )
                  -> ( ( { K , <. 0 , b >. } e. E /\ { <. 0 , b >. , L } e. E )
                       -> X = <. 0 , b >. ) ) ) ) ) $=
      ( c1 co wceq wa wi syl ex c2nd cfv c2 caddc cmo cop cc0 cmin w3o wcel wne
      c5 cv cfzo cpr eqtr3 eqneqall impd eqcoms a1d 1ex vex op2ndd oveq1 oveq1d
      opeq2d eqeq2d opeq2 anbi12d pgnbgreunbgrlem2lem1 pm2.21d expimpd biimtrdi
      wb adantld adantr pgnbgreunbgrlem2lem3 3jaod prcom eleq1i pm2.21 biimtrid
      expdcom wn impcomd ancoms pgnbgreunbgrlem2lem2 eqcomd 3jaoi ) ENHUAUBZUCU
      DOZULUEOZUFZPZDWMPZDUGWJUFZPZDNWJUCUHOZULUEOZUFZPZUIHNAUMZUFPZHGUJZQZDEUK
      ZIUMZUGULUNOZUJXBXHUJQZQDUGXGUFZUOZBUJZXJEUOZBUJZQHXJPZRZRZRZREWPPZEWTPZW
      NWOXRWQXAWNWOXRWNWOQZXQXEYAEDPXQEDWMUPXQDEDEPZXFXIXPXIXPRZDEUQZURZUSSUTTX
      EWNWQXQXCWNWQQZXQRXDXCYFENXBUCUDOZULUEOZUFZPZDUGXBUFZPZQZXQXCWJXBPZYFYMVN
      NXBHVAAVBVCZYNWNYJWQYLYNWMYIEYNWLYHNYNWKYGULUEWJXBUCUDVDVEVFZVGZYNWPYKDWJ
      XBUGVHZVGZVISYMXIXPXFYMXIXPYMXIQZXLXNXOYTXLQXNXOABCDEFGHIJKLMVJVKVLTVOVMV
      PWCXEWNXAXQXCWNXAQZXQRXDXCUUAYJDNXBUCUHOZULUEOZUFZPZQZXQXCYNUUAUUFVNYOYNW
      NYJXAUUEYQYNWTUUDDYNWSUUCNYNWRUUBULUEWJXBUCUHVDVEVFZVGZVISUUFXIXPXFUUFXIX
      PUUFXIQZXLXNXOUUIXLQXNXOABCDEFGHIJKLMVQVKVLTVOVMVPWCVRXSWOXRWQXAXEXSWOXQX
      EXSWOQZEYKPZDYIPZQZXQXEYNUUJUUMVNXCYNXDYOVPZYNXSUUKWOUULYNWPYKEYRVGZYNWMY
      IDYPVGZVISUUMXIXPXFUULUUKYCUULUUKQZXIXPUUQXIQZXNXLXOXNEXJUOZBUJZUURXLXORZ
      XMUUSBXJEVSVTZUURUUTUVAUURUUTQXJDUOZBUJZWDZUVAABCEDFGHIJKLMVJXLUVDUVEXOXK
      UVCBDXJVSVTUVDXOWAWBZSTWBWETWFVOVMWCXSWQXRXSWQQZXQXEUVGXFXIXPUVGYBXFYCRWQ
      XSYBDEWPUPWFYDSURUTTXEXSXAXQXEXSXAQZUUKUUEQZXQXEYNUVHUVIVNUUNYNXSUUKXAUUE
      UUOUUHVISUVIXIXPXFUUEUUKYCUUEUUKQZXIXPUVJXIQZXNXLXOXNUUTUVKUVAUVBUVKUUTUV
      AUVKUUTQUVEUVAABCEDFGHIJKLMWGUVFSTWBWETWFVOVMWCVRXTWOXRWQXAXEXTWOXQXEXTWO
      QZEUUDPZUULQZXQXEYNUVLUVNVNUUNYNXTUVMWOUULYNWTUUDEUUGVGZUUPVISUVNXIXPXFUU
      LUVMYCUULUVMQZXIXPUVPXIQZXNXLXOXNUUTUVQUVAUVBUVQUUTUVAUVQUUTQUVEUVAABCEDF
      GHIJKLMVQUVFSTWBWETWFVOVMWCXEXTWQXQXEXTWQQZUVMYLQZXQXEYNUVRUVSVNUUNYNXTUV
      MWQYLUVOYSVISUVSXIXPXFUVSXIXPUVSXIQZXLXNXOUVTXLQXNXOABCDEFGHIJKLMWGVKVLTV
      OVMWCXTXAXRXTXAQZXQXEUWAYBXQUWAEDEDWTUPWHYESUTTVRWI $.

    $d E x y $.  $d K x y $.  $d L x y $.  $d N x y $.  $d V x y $.
    $d X x y $.  $d b x $.
    $( Lemma 3 for ~ pgnbgreunbgr .  (Contributed by AV, 18-Nov-2025.) $)
    pgnbgreunbgrlem3 $p |- ( ( ( K e. N /\ L e. N /\ K =/= L )
                               /\ b e. ( 0 ..^ 5 ) )
                    -> ( ( { K , <. 0 , b >. } e. E
                        /\ { <. 0 , b >. , L } e. E ) -> X = <. 0 , b >. ) ) $=
      ( wcel cc0 c5 co wa wceq wi c1 vx vy wne w3a cv cfzo cop cpr cnbgr nbgrcl
      eleq2s 3ad2ant1 wrex c3 cuz cfv c2 cdiv cceil 5eluz3 pglem gpgvtxel mp2an
      wb eqid biimpi adantl wo vex elpr opeq1 eqeq2d adantr c2nd caddc cmo cmin
      ctp cvtx c1st pm3.2i eleq2i c0ex op1std anim12i gpgnbgrvtx0 sylancr eleq2
      anbi12d w3o eltpi pgnbgreunbgrlem1 syl mpan9 com12 mpdan expd com23 com24
      sylbid 3impia expdimp imp31 ex 1ex gpgnbgrvtx1 pgnbgreunbgrlem2 imbitrrid
      anim1ci imbi1d jaoi sylbi impd rexlimdvv mpd mpidan ) CEMZDEMZCDUCZUDZHUE
      ZNOUFPZMZGFMZCNYAUGZUHAMYEDUHAMQGYERSZXQXRYDXSYDCBGUIPEBCFGJUJLUKULXTYCQZ
      YDQZGUAUEZUBUEZUGZRZUBYBUMUANTUHZUMZYFYDYNYGYDYNOUNUOUPMZUQTOUQURPUSUPUFP
      ZMZYDYNVDUTVAUAUBBYBYPUQOFGYBVEYPVEZIJVBVCVFVGYHYLYFUAUBYMYBYHYIYMMZYJYBM
      ZYLYFSZYSYHYTUUASYSYHYTUUAYSYINRZYITRZVHYHYTQZUUASZYINTUAVIVJUUBUUEUUCUUB
      UUDUUAUUBUUDQYLGNYJUGZRZYFUUBYLUUGVDUUDUUBYKUUFGYINYJVKVLVMUUDUUGYFSZUUBY
      GYDYTUUHYGYTYDUUHXTYCYTYDUUHSZXQXRXSYCYTQZUUISXQXRQZXSUUJUUIUUKUUGYDXSUUJ
      QZYFUUKYDUUGUULYFSZUUKYDUUGUUMYDUUGQZUUKUUMUUNENGVNUPZTVOPOVPPUGZTUUOUGZN
      UUOTVQPOVPPUGZVRZRZUUKUUMSZUUNYOYQQZGBVSUPZMZGVTUPZNRZQUUTYOYQUTVAWAZYDUV
      DUUGUVFYDUVDFUVCGJWBVFNYJGWCUBVIZWDWEEBYPUQOUVCGYRIUVCVELWFWGUUNUUTQUUKCU
      USMZDUUSMZQZUUMUUTUUKUVKVDUUNUUTXQUVIXRUVJEUUSCWHEUUSDWHWIVGUUNUVKUUMSUUT
      UVKUUNUUMUVICUUPRCUUQRCUURRWJZUVJUUNUUMSZCUUPUUQUURWKUVJDUUPRDUUQRDUURRWJ
      UVLUVMSDUUPUUQUURWKUBABCDEFGHIJKLWLWMWNWOVMWTWPWOWQWRWSWQXAXBWRXCVGWTXDUU
      DUUAUUCGTYJUGZRZYFSZYGYDYTUVPYGYTYDUVPXTYCYTYDUVPSZXQXRXSUUJUVQSUUKXSUUJU
      VQUUKUVOYDUULYFUUKUVOYDUUMUVOYDQZUUKUUMUVRETUUOUQVOPOVPPUGZNUUOUGZTUUOUQV
      QPOVPPUGZVRZRZUVAUVRUVBYDUVETRZQUWCUVGUVOUWDYDTYJGXEUVHWDXIEBYPUQOFGYRIJL
      XFWGUVRUWCQUUKCUWBMZDUWBMZQZUUMUWCUUKUWGVDUVRUWCXQUWEXRUWFEUWBCWHEUWBDWHW
      IVGUVRUWGUUMSUWCUWGUVRUUMUWECUVSRCUVTRCUWARWJZUWFUVRUUMSZCUVSUVTUWAWKUWFD
      UVSRDUVTRDUWARWJUWHUWISDUVSUVTUWAWKUBABCDEFGHIJKLXGWMWNWOVMWTWPWOWQWSWQXA
      XBWRXCUUCYLUVOYFUUCYKUVNGYITYJVKVLXJXHXKXLWQWOXMXNXOXP $.

    $( Lemma 4 for ~ pgnbgreunbgr .  (Contributed by AV, 20-Nov-2025.) $)
    pgnbgreunbgrlem4 $p |- ( ( L = <. 1 , ( ( ( 2nd ` X ) + 2 ) mod 5 ) >.
                           \/ L = <. 0 , ( 2nd ` X ) >.
                           \/ L = <. 1 , ( ( ( 2nd ` X ) - 2 ) mod 5 ) >. )
                       -> ( ( K = <. 1 , ( ( ( 2nd ` X ) + 2 ) mod 5 ) >.
                           \/ K = <. 0 , ( 2nd ` X ) >.
                           \/ K = <. 1 , ( ( ( 2nd ` X ) - 2 ) mod 5 ) >. )
        -> ( ( X e. V /\ X = <. 1 , y >. )
             -> ( ( K =/= L /\ ( b e. ( 0 ..^ 5 ) /\ y e. ( 0 ..^ 5 ) ) )
                  -> ( ( { K , <. 1 , b >. } e. E /\ { <. 1 , b >. , L } e. E )
                       -> X = <. 1 , b >. ) ) ) ) ) $=
      ( wcel c1 wceq wa co c5 wi cv cop c2nd cfv c2 caddc cmo cc0 cmin w3o cfzo
      wne cpr 1ex vex op2ndd oveq1 oveq1d opeq2d eqeq2d opeq2 3orbi123d anbi12d
      simpr simpl neeq12d eqid eqneqall ax-mp biimtrdi impd ex weq prcom eleq1i
      wb c3 cuz cdiv cceil 5eluz3 pglem gpgedgiov mpanl12 ancoms bitrid adantld
      preq1 eleq1d preq2 bi2anan9r imbi1d imbitrrid anbi12ci cmul 5nn nnzi uzid
      c4 cz c8 4t2e8 oveq1i 8mod5e3 eqtri 3ne0 eqnetri pm3.2i gpgedg2iv mp3an13
      eqcoms adantrd adantl adantr simpll anim1i syl3anc anbi1d 3imtr4d ancom2s
      3jaoi a1i equcom bitrdi eqeq2 3jaod imp syl eqeq1 imbi2d sylibrd expdcom
      ) HGNZHOAUAZUBZPZQEOHUCUDZUEUFRZSUGRZUBZPZEUHYQUBZPZEOYQUEUIRZSUGRZUBZPZU
      JZDYTPZDUUBPZDUUFPZUJZDEULZIUAZUHSUKRZNZYNUUONZQZQZDOUUNUBZUMZBNZUUTEUMZB
      NZQZHUUTPZTZTZYPUUHUULQZUVHTYMYPUVIUUSUVEYOUUTPZTZTZUVHYPYQYNPZUVIUVLTOYN
      HUNAUOUPUVMUVIEOYNUEUFRZSUGRZUBZPZEUHYNUBZPZEOYNUEUIRZSUGRZUBZPZUJZDUVPPZ
      DUVRPZDUWBPZUJZQUVLUVMUUHUWDUULUWHUVMUUAUVQUUCUVSUUGUWCUVMYTUVPEUVMYSUVOO
      UVMYRUVNSUGYQYNUEUFUQURUSZUTUVMUUBUVREYQYNUHVAZUTUVMUUFUWBEUVMUUEUWAOUVMU
      UDUVTSUGYQYNUEUIUQURUSZUTVBUVMUUIUWEUUJUWFUUKUWGUVMYTUVPDUWIUTUVMUUBUVRDU
      WJUTUVMUUFUWBDUWKUTVBVCUWDUWHUVLUWDUWEUVLUWFUWGUVQUWEUVLTUVSUWCUVQUWEUVLU
      VQUWEQZUUMUURUVKUWLUUMUVPUVPULZUURUVKTZUWLDUVPEUVPUVQUWEVDUVQUWEVEVFUVPUV
      PPUWMUWNTUVPVGUWNUVPUVPVHVIVJVKVLUVSUWEUVLUVSUWEQZUURUVKUUMUURUVKUWOUVPUU
      TUMZBNZUUTUVRUMZBNZQZUVJTUURUWSUVJUWQUURUWSAIVMZUVJUWSUVRUUTUMZBNZUURUXAU
      WRUXBBUUTUVRVNVOZUUQUUPUXCUXAVPZSVQVRUDNZUEOSUEVSRVTUDUKRZNZUUQUUPQUXEWAW
      BBCUUOUXGUESYNUUNUXGVGZUUOVGZJLWCZWDWEZWFYNUUNOVAZVJWGUWOUVEUWTUVJUWEUVBU
      WQUVSUVDUWSUWEUVAUWPBDUVPUUTWHWIZUVSUVCUWRBEUVRUUTWJWIZWKWLWMWGVLUWCUWEUV
      LUWCUWEQZUURUVKUUMUURUVKUXPUWQUUTUWBUMZBNZQZUVJTUURUXSIAVMZUVJUXSUWBUUTUM
      ZBNZUUTUVPUMZBNZQZUURUXTUWQUYDUXRUYBUWPUYCBUVPUUTVNVOUXQUYABUUTUWBVNVOWNS
      SVRUDNZUURUXHWSUEWORZSUGRZUHULZQZUYEUXTVPZSWTNUYFSWPWQSWRVIZUXHUYIWBUYHVQ
      UHUYHXASUGRZVQUYGXASUGXBXCZXDXEXFXGXHBCUUOUXGUESUUNYNUXIUXJJLXIZXJWFUVJYN
      UUNUXMXKZVJUXPUVEUXSUVJUWEUVBUWQUWCUVDUXRUXNUWCUVCUXQBEUWBUUTWJZWIWKWLWMW
      GVLYAUVQUWFUVLTUVSUWCUVQUWFUVLUVQUWFQZUURUVKUUMUURUVKUYRUXCUYDQZUVJTUURUX
      CUVJUYDUURUXCUXAUVJUXLUXMVJZXLUYRUVEUYSUVJUWFUVBUXCUVQUVDUYDUWFUVAUXBBDUV
      RUUTWHZWIUVQUVCUYCBEUVPUUTWJWIZWKWLWMWGVLUVSUWFUVLUVSUWFQZUUMUURUVKVUCUUM
      UVRUVRULZUWNVUCDUVREUVRUVSUWFVDUVSUWFVEVFUVRUVRPVUDUWNTUVRVGUWNUVRUVRVHVI
      VJVKVLUWCUWFUVLUWCUWFQZUURUVKUUMUURUVKVUEUXCUXRQZUVJTUURUXCUVJUXRUYTXLVUE
      UVEVUFUVJVUEUVBUXCUVDUXRVUEUVAUXBBUWFUVAUXBPUWCVUAXMWIVUEUVCUXQBUWCUVCUXQ
      PUWFUYQXNWIVCWLWMWGVLYAUVQUWGUVLTUVSUWCUVQUWGUVLUVQUWGQZUWBUVPULZUURQZUYE
      UVJTZUUSUVKVUIVUJTVUGUURVUJVUHUURUYEUXTUVJUYFUYIUURUYKUYLUYHUYMUHUYNUYMVQ
      UHXDXFXGXGUYFUYIQZUURQUYFUURUYJUYKUYFUYIUURXOVUKUURVDVUKUYJUURUYFUXHUYIUX
      HUYFWBYBXPXNUYOXQWDUYPVJXMYBVUGUUMVUHUURUWGUVQUUMVUHVPUWGUVQQDUWBEUVPUWGU
      VQVEUWGUVQVDVFWEXRVUGUVEUYEUVJUWGUVBUYBUVQUVDUYDUWGUVAUYABDUWBUUTWHZWIVUB
      WKWLXSVLUVSUWGUVLUUSUVKUVSUWGQZUYBUWSQZUVJTZUURVUOUUMUURUWSUVJUYBUURUWSUX
      TUVJUXFUXHUURUWSUXTVPWAWBUWSUXCUXFUXHQZUURQZUXTUXDVUQUXCUXAUXTVUPUUQUUPUX
      EUXKXTAIYCYDWFWDUYPVJWGXMVUMUVEVUNUVJVUMUVBUYBUVDUWSVUMUVAUYABUWGUVAUYAPU
      VSVULXMWIUVSUVDUWSVPUWGUXOXNVCWLWMVLUWCUWGDEPZUVLUWGVURVPUWBEUWBEDYEXKVUR
      UUMUURUVKUWNDEVHVKVJYAYFYGVJYHYPUVGUVKUUSYPUVFUVJUVEHYOUUTYIYJYJYKXMYL $.

    $( Lemma 1 for ~ pgnbgreunbgrlem5 .  (Contributed by AV, 21-Nov-2025.) $)
    pgnbgreunbgrlem5lem1 $p |- ( ( ( ( L = <. 0 , ( ( y + 1 ) mod 5 ) >.
                                   /\ K = <. 1 , y >. )
                                  /\ ( b e. ( 0 ..^ 5 ) /\ y e. ( 0 ..^ 5 ) ) )
                                    /\ { K , <. 1 , b >. } e. E )
                                  -> -. { <. 1 , b >. , L } e. E ) $=
      ( c1 co c5 cop wceq wcel c2 cc0 cv caddc cmo wa cfzo cpr wn c2nd cfv cmin
      wi w3o cuz cdiv cceil c1st 5eluz3 pglem pm3.2i 1ex op1st simpr gpgvtxedg1
      c3 vex eqid mp3an12i ex op2nd oveq1i eqeq2i pgnioedg2 adantl opeq2 preq1d
      eleq1d notbid imbitrrid sylbi simplbiim com12 wne ax-1ne0 eqneqall adantr
      opth mpi a1i pgnioedg1 3jaod syld wb preq1 preq2 imbi12d mpbird imp ) EUA
      AUBZNUCOPUDOQZRZDNWSQZRZUEZIUBZUAPUFOZSZWSXFSZUEZUEZDNXEQZUGZBSZXKEUGZBSZ
      UHZXJXMXPULZXBXKUGZBSZXKWTUGZBSZUHZULZXIYCXDXIXSXKNXBUIUJZTUCOZPUDOZQRZXK
      UAYDQRZXKNYDTUKOZPUDOZQRZUMZYBXIXSYLPVEUNUJSZTNPTUOOUPUJUFOZSZUEXBUQUJNRX
      IXSUEXSYLYMYOURUSUTNWSVAAVFZVBXIXSVCBCYNTPGXBXKYNVGJKLVDVHVIXIYGYBYHYKYGX
      IYBYGNNRZXEYFRZXIYBULZNXENYFVAIVFZWGYRXEWSTUCOZPUDOZRZYSYFUUBXEYEUUAPUDYD
      WSTUCNWSVAYPVJZVKVKVLXIYBUUCNUUBQZWTUGZBSZUHZXHUUHXGABCJLVMVNUUCYAUUGUUCX
      TUUFBUUCXKUUEWTXEUUBNVOVPVQVRVSVTWAWBYHYBULXIYHNUARZXEYDRZUEYBNXEUAYDVAYT
      WGUUIYBUUJUUINUAWCYBWDYBNUAWEWHWFVTWIYKXIYBYKYQXEYJRZYSNXENYJVAYTWGUUKXEW
      STUKOZPUDOZRZYSYJUUMXEYIUULPUDYDWSTUKUUDVKVKVLXIYBUUNNUUMQZWTUGZBSZUHZXHU
      URXGABCJLWJVNUUNYAUUQUUNXTUUPBUUNXKUUOWTXEUUMNVOVPVQVRVSVTWAWBWKWLVNXDXQY
      CWMXIXDXMXSXPYBXCXMXSWMXAXCXLXRBDXBXKWNVQVNXAXPYBWMXCXAXOYAXAXNXTBEWTXKWO
      VQVRWFWPWFWQWR $.

    $( Lemma 2 for ~ pgnbgreunbgrlem5 .  (Contributed by AV, 20-Nov-2025.) $)
    pgnbgreunbgrlem5lem2 $p |- ( ( ( ( L = <. 0 , ( ( y - 1 ) mod 5 ) >.
                                   /\ K = <. 1 , y >. )
                                  /\ ( b e. ( 0 ..^ 5 ) /\ y e. ( 0 ..^ 5 ) ) )
                                    /\ { K , <. 1 , b >. } e. E )
                                  -> -. { <. 1 , b >. , L } e. E ) $=
      ( c1 co c5 cop wceq wcel c2 cc0 cv cmin cmo wa cfzo cpr wn c2nd cfv caddc
      wi w3o cuz cdiv cceil c1st 5eluz3 pglem pm3.2i 1ex op1st simpr gpgvtxedg1
      c3 vex eqid mp3an12i ex op2nd oveq1i eqeq2i pgnioedg3 adantl opeq2 preq1d
      eleq1d notbid imbitrrid sylbi simplbiim com12 wne ax-1ne0 eqneqall adantr
      opth mpi a1i pgnioedg4 3jaod syld wb preq1 preq2 imbi12d mpbird imp ) EUA
      AUBZNUCOPUDOQZRZDNWSQZRZUEZIUBZUAPUFOZSZWSXFSZUEZUEZDNXEQZUGZBSZXKEUGZBSZ
      UHZXJXMXPULZXBXKUGZBSZXKWTUGZBSZUHZULZXIYCXDXIXSXKNXBUIUJZTUKOZPUDOZQRZXK
      UAYDQRZXKNYDTUCOZPUDOZQRZUMZYBXIXSYLPVEUNUJSZTNPTUOOUPUJUFOZSZUEXBUQUJNRX
      IXSUEXSYLYMYOURUSUTNWSVAAVFZVBXIXSVCBCYNTPGXBXKYNVGJKLVDVHVIXIYGYBYHYKYGX
      IYBYGNNRZXEYFRZXIYBULZNXENYFVAIVFZWGYRXEWSTUKOZPUDOZRZYSYFUUBXEYEUUAPUDYD
      WSTUKNWSVAYPVJZVKVKVLXIYBUUCNUUBQZWTUGZBSZUHZXHUUHXGABCJLVMVNUUCYAUUGUUCX
      TUUFBUUCXKUUEWTXEUUBNVOVPVQVRVSVTWAWBYHYBULXIYHNUARZXEYDRZUEYBNXEUAYDVAYT
      WGUUIYBUUJUUINUAWCYBWDYBNUAWEWHWFVTWIYKXIYBYKYQXEYJRZYSNXENYJVAYTWGUUKXEW
      STUCOZPUDOZRZYSYJUUMXEYIUULPUDYDWSTUCUUDVKVKVLXIYBUUNNUUMQZWTUGZBSZUHZXHU
      URXGABCJLWJVNUUNYAUUQUUNXTUUPBUUNXKUUOWTXEUUMNVOVPVQVRVSVTWAWBWKWLVNXDXQY
      CWMXIXDXMXSXPYBXCXMXSWMXAXCXLXRBDXBXKWNVQVNXAXPYBWMXCXAXOYAXAXNXTBEWTXKWO
      VQVRWFWPWFWQWR $.

    $( Lemma 3 for ~ pgnbgreunbgrlem5 .  (Contributed by AV, 20-Nov-2025.) $)
    pgnbgreunbgrlem5lem3 $p |- ( ( ( ( L = <. 0 , ( ( y + 1 ) mod 5 ) >.
                                    /\ K = <. 0 , ( ( y - 1 ) mod 5 ) >. )
                                  /\ ( b e. ( 0 ..^ 5 ) /\ y e. ( 0 ..^ 5 ) ) )
                                    /\ { K , <. 1 , b >. } e. E )
                                  -> -. { <. 1 , b >. , L } e. E ) $=
      ( cc0 c1 co c5 cop wceq wcel cv caddc cmo cmin wa cfzo cpr wn wi c2nd cfv
      w3o c3 cuz cdiv cceil c1st 5eluz3 pglem pm3.2i c0ex ovex op1st simpr eqid
      c2 gpgvtxedg0 mp3an12i 1ex vex opth wne ax-1ne0 a1i necon2bi adantr sylbi
      ex op2nd eqeq2i pgnioedg5 adantl preq1d eleq1d notbid imbitrrid simplbiim
      opeq2 com12 3jaod syld wb preq1 preq2 imbi12d mpbird imp ) ENAUAZOUBPQUCP
      RZSZDNWROUDPZQUCPZRZSZUEZIUAZNQUFPZTZWRXGTZUEZUEZDOXFRZUGZBTZXLEUGZBTZUHZ
      XKXNXQUIZXCXLUGZBTZXLWSUGZBTZUHZUIZXJYDXEXJXTXLNXCUJUKZOUBPQUCPZRSZXLOYER
      SZXLNYEOUDPQUCPZRSZULZYCXJXTYKQUMUNUKTZVFOQVFUOPUPUKUFPZTZUEXCUQUKNSXJXTU
      EXTYKYLYNURUSUTNXBVAXAQUCVBZVCXJXTVDBCYMVFQGXCXLYMVEJKLVGVHVRXJYGYCYHYJYG
      YCUIXJYGONSZXFYFSZUEYCOXFNYFVIIVJZVKYPYCYQYBONONVLYBVMVNVOZVPVQVNYHXJYCYH
      OOSXFYESZXJYCUIZOXFOYEVIYRVKYTXFXBSZUUAYEXBXFNXBVAYOVSVTXJYCUUBOXBRZWSUGZ
      BTZUHZXIUUFXHABCJLWAWBUUBYBUUEUUBYAUUDBUUBXLUUCWSXFXBOWHWCWDWEWFVQWGWIYJY
      CUIXJYJYPXFYISZUEYCOXFNYIVIYRVKYPYCUUGYSVPVQVNWJWKWBXEXRYDWLXJXEXNXTXQYCX
      DXNXTWLWTXDXMXSBDXCXLWMWDWBWTXQYCWLXDWTXPYBWTXOYABEWSXLWNWDWEVPWOVPWPWQ
      $.

    $( Lemma 5 for ~ pgnbgreunbgr .  Impossible cases.  (Contributed by AV,
       21-Nov-2025.) $)
    pgnbgreunbgrlem5 $p |- ( ( L = <. 0 , ( ( ( 2nd ` X ) + 1 ) mod 5 ) >.
                            \/ L = <. 1 , ( 2nd ` X ) >.
                            \/ L = <. 0 , ( ( ( 2nd ` X ) - 1 ) mod 5 ) >. )
                        -> ( ( K = <. 0 , ( ( ( 2nd ` X ) + 1 ) mod 5 ) >.
                            \/ K = <. 1 , ( 2nd ` X ) >.
                            \/ K = <. 0 , ( ( ( 2nd ` X ) - 1 ) mod 5 ) >. )
        -> ( ( X = <. 0 , y >. /\ X e. V )
             -> ( ( K =/= L /\ ( b e. ( 0 ..^ 5 ) /\ y e. ( 0 ..^ 5 ) ) )
                  -> ( ( { K , <. 1 , b >. } e. E /\ { <. 1 , b >. , L } e. E )
                       -> X = <. 1 , b >. ) ) ) ) ) $=
      ( cc0 cop wceq wa c1 co ex cv wcel c2nd cfv caddc c5 cmo cmin w3o wne cpr
      cfzo wi c0ex vex op2ndd adantr oveq1 oveq1d opeq2d eqeq2d opeq2 3orbi123d
      anbi12d syl simpl simpr neeq12d ancoms eqid eqneqall pgnbgreunbgrlem5lem1
      wb ax-mp biimtrdi impd pm2.21d expimpd adantld pgnbgreunbgrlem5lem3 3jaod
      prcom eleq1i anbi12i impcomd biimtrid expcom pgnbgreunbgrlem5lem2 expdcom
      3jaoi imp ) HNAUAZOPZHGUBZQZENHUCUDZRUESZUFUGSZOZPZERWPOZPZENWPRUHSZUFUGS
      ZOZPZUIZDWSPZDXAPZDXEPZUIZDEUJZIUAZNUFULSZUBWLXNUBQZQDRXMOZUKZBUBZXPEUKZB
      UBZQZHXPPZUMZUMZWOXGXKQZENWLRUESZUFUGSZOZPZERWLOZPZENWLRUHSZUFUGSZOZPZUIZ
      DYHPZDYJPZDYNPZUIZQZYDWOWPWLPZYEUUAVMWMUUBWNNWLHUNAUOUPUQUUBXGYPXKYTUUBWT
      YIXBYKXFYOUUBWSYHEUUBWRYGNUUBWQYFUFUGWPWLRUEURUSUTZVAUUBXAYJEWPWLRVBZVAUU
      BXEYNEUUBXDYMNUUBXCYLUFUGWPWLRUHURUSUTZVAVCUUBXHYQXIYRXJYSUUBWSYHDUUCVAUU
      BXAYJDUUDVAUUBXEYNDUUEVAVCVDVEYPYTYDYIYTYDUMYKYOYIYQYDYRYSYIYQYDYIYQQZXLX
      OYCUUFXLYHYHUJZXOYCUMZYQYIXLUUGVMYQYIQDYHEYHYQYIVFYQYIVGVHVIYHYHPUUGUUHUM
      YHVJUUHYHYHVKVNVOVPTYIYRYDYIYRQZXOYCXLUUIXOYCUUIXOQZXRXTYBUUJXRQXTYBABCDE
      FGHIJKLMVLVQVRTVSTYIYSYDYIYSQZXOYCXLUUKXOYCUUKXOQZXRXTYBUULXRQXTYBABCDEFG
      HIJKLMVTVQVRTVSTWAYKYQYDYRYSYQYKYDYQYKQZXOYCXLUUMXOYCYAXPDUKZBUBZEXPUKZBU
      BZQZUUMXOQZYBXRUUOXTUUQXQUUNBDXPWBWCXSUUPBXPEWBWCWDZUUSUUQUUOYBUUSUUQUUOY
      BUMZUUSUUQQUUOYBABCEDFGHIJKLMVLVQTWEWFTVSWGYKYRYDYKYRQZXLXOYCUVBXLYJYJUJZ
      UUHUVBDYJEYJYKYRVGYKYRVFVHYJYJPUVCUUHUMYJVJUUHYJYJVKVNVOVPTYSYKYDYSYKQZXO
      YCXLUVDXOYCYAUURUVDXOQZYBUUTUVEUUQUUOYBUVEUUQUVAUVEUUQQUUOYBABCEDFGHIJKLM
      WHVQTWEWFTVSWGWAYOYQYDYRYSYQYOYDYQYOQZXOYCXLUVFXOYCYAUURUVFXOQZYBUUTUVGUU
      QUUOYBUVGUUQUVAUVGUUQQUUOYBABCEDFGHIJKLMVTVQTWEWFTVSWGYOYRYDYOYRQZXOYCXLU
      VHXOYCUVHXOQZXRXTYBUVIXRQXTYBABCDEFGHIJKLMWHVQVRTVSTYOYSYDYOYSQZXLXOYCUVJ
      XLYNYNUJZUUHUVJDYNEYNYOYSVGYOYSVFVHYNYNPUVKUUHUMYNVJUUHYNYNVKVNVOVPTWAWJW
      KVOWI $.

    $( Lemma 6 for ~ pgnbgreunbgr .  (Contributed by AV, 20-Nov-2025.) $)
    pgnbgreunbgrlem6 $p |- ( ( ( K e. N /\ L e. N /\ K =/= L )
                             /\ b e. ( 0 ..^ 5 ) )
                    -> ( ( { K , <. 1 , b >. } e. E
                        /\ { <. 1 , b >. , L } e. E ) -> X = <. 1 , b >. ) ) $=
      ( wcel cc0 c5 co c1 wa wceq wi vx vy wne w3a cv cfzo cop cpr cnbgr nbgrcl
      eleq2s 3ad2ant1 wrex c3 cuz cfv c2 cdiv cceil 5eluz3 pglem gpgvtxel mp2an
      wb eqid biimpi adantl vex elpr c2nd caddc cmo cmin ctp c1st pm3.2i op1std
      c0ex anim1ci gpgnbgrvtx0 sylancr eleq2 anbi12d w3o eltpi pgnbgreunbgrlem5
      syl mpan9 com12 adantr sylbid mpdan expd com24 3impia expdimp com23 imp31
      wo opeq1 eqeq2d imbi1d imbitrrid cvtx eleq2i 1ex anim12i pgnbgreunbgrlem4
      gpgnbgrvtx1 ex jaoi sylbi impd rexlimdvv mpd mpidan ) CEMZDEMZCDUCZUDZHUE
      ZNOUFPZMZGFMZCQYAUGZUHAMYEDUHAMRGYESTZXQXRYDXSYDCBGUIPEBCFGJUJLUKULXTYCRZ
      YDRZGUAUEZUBUEZUGZSZUBYBUMUANQUHZUMZYFYDYNYGYDYNOUNUOUPMZUQQOUQURPUSUPUFP
      ZMZYDYNVDUTVAUAUBBYBYPUQOFGYBVEYPVEZIJVBVCVFVGYHYLYFUAUBYMYBYHYIYMMZYJYBM
      ZYLYFTZYSYHYTUUATYSYHYTUUAYSYINSZYIQSZWSYHYTRZUUATZYINQUAVHVIUUBUUEUUCUUD
      UUAUUBGNYJUGZSZYFTZYGYDYTUUHYGYTYDUUHXTYCYTYDUUHTZXQXRXSYCYTRZUUITXQXRRZX
      SUUJUUIUUKUUGYDXSUUJRZYFUUKUUGYDUULYFTZUUGYDRZUUKUUMUUNENGVJUPZQVKPOVLPUG
      ZQUUOUGZNUUOQVMPOVLPUGZVNZSZUUKUUMTZUUNYOYQRZYDGVOUPZNSZRUUTYOYQUTVAVPZUU
      GUVDYDNYJGVRUBVHZVQVSEBYPUQOFGYRIJLVTWAUUNUUTRUUKCUUSMZDUUSMZRZUUMUUTUUKU
      VIVDUUNUUTXQUVGXRUVHEUUSCWBEUUSDWBWCVGUUNUVIUUMTUUTUVIUUNUUMUVGCUUPSCUUQS
      CUURSWDZUVHUUNUUMTZCUUPUUQUURWEUVHDUUPSDUUQSDUURSWDUVJUVKTDUUPUUQUURWEUBA
      BCDEFGHIJKLWFWGWHWIWJWKWLWIWMWNWMWOWPWQWRUUBYLUUGYFUUBYKUUFGYINYJWTXAXBXC
      UUCUUDUUAUUCUUDRYLGQYJUGZSZYFUUCYLUVMVDUUDUUCYKUVLGYIQYJWTXAWJUUDUVMYFTZU
      UCYGYDYTUVNYGYTYDUVNXTYCYTYDUVNTZXQXRXSUUJUVOTUUKXSUUJUVOUUKUVMYDUULYFUUK
      YDUVMUUMUUKYDUVMUUMYDUVMRZUUKUUMUVPEQUUOUQVKPOVLPUGZNUUOUGZQUUOUQVMPOVLPU
      GZVNZSZUVAUVPUVBGBXDUPZMZUVCQSZRUWAUVEYDUWCUVMUWDYDUWCFUWBGJXEVFQYJGXFUVF
      VQXGEBYPUQOUWBGYRIUWBVELXIWAUVPUWARUUKCUVTMZDUVTMZRZUUMUWAUUKUWGVDUVPUWAX
      QUWEXRUWFEUVTCWBEUVTDWBWCVGUVPUWGUUMTUWAUWGUVPUUMUWECUVQSCUVRSCUVSSWDZUWF
      UVPUUMTZCUVQUVRUVSWEUWFDUVQSDUVRSDUVSSWDUWHUWITDUVQUVRUVSWEUBABCDEFGHIJKL
      XHWGWHWIWJWKWLWIWMWQWNWMWOWPWQWRVGWKXJXKXLWMWIXMXNXOXP $.

    $d a b y $.  $d E a b $.  $d K a b $.  $d L a b $.  $d N a b $.
    $d V a b $.  $d X a b $.
    $( In a Petersen graph, two different neighbors of a vertex have exactly
       one common neighbor, which is the vertex itself.  (Contributed by AV,
       9-Nov-2025.) $)
    pgnbgreunbgr $p |- ( ( K e. N /\ L e. N /\ K =/= L )
                         -> E! x e. V { { K , x } , { x , L } } C_ E ) $=
      ( vy vb wcel cpr wi wa wceq cc0 va wne w3a wss wral wrex wreu preq2 preq1
      weq preq12d sseq1d eqeq1 imbi2d ralbidv anbi12d cumgr cnbgr eleq2i biimpi
      cv co 3ad2ant1 cusgr wb c5 c2 cgpg pgjsgr eqeltri nbusgreledg ax-mp sylib
      usgrumgr jctil umgrpredgv simpr anbi12i prcom eleq1i bitrdi sylbb 3adant3
      3syl prssi syl prex prss cop cfzo c1 cuz cfv cdiv cceil 5eluz3 pglem eqid
      c3 gpgvtxel mp2an adantl wo eqeq2d adantr pgnbgreunbgrlem3 adantlr eleq1d
      opeq1 imbi12d syl5ibrcom sylbid ex pgnbgreunbgrlem6 imbi1d imbitrrid jaoi
      eqeq2 expd elpri syl11 rexlimdvv mpd biimtrrid ralrimiva rspcedvdw sylibr
      impd jca reu8 ) DFOZEFOZDEUBZUCZDAVAZPZYOEPZPZBUDZDMVAZPZYTEPZPZBUDZAMUJZ
      QZMGUEZRZAGUFYSAGUGYNUUHDHPZHEPZPZBUDZUUDHYTSZQZMGUEZRAHGYOHSZYSUULUUGUUO
      UUPYRUUKBUUPYPUUIYQUUJYOHDUHYOHEUIUKULUUPUUFUUNMGUUPUUEUUMUUDYOHYTUMUNUOU
      PYNCUQOZUUIBOZRDGOZHGOZRUUTYNUURUUQYNDCHURVBZOZUURYKYLUVBYMYKUVBFUVADLUSZ
      UTVCCVDOZUVBUURVECVFVGVHVBVDIVIVJZBCHDKVKZVLVMUVDUUQUVECVNVLVOBCDHGJKVPUU
      SUUTVQWDYNUULUUOYNUURUUJBOZRZUULYKYLUVHYMYKYLRUVBEUVAOZRZUVHYKUVBYLUVIUVC
      FUVAELUSVRUVDUVJUVHVEUVEUVDUVBUURUVIUVGUVFUVDUVIEHPZBOUVGBCHEKVKUVKUUJBEH
      VSVTWAUPVLWBWCUUIUUJBWEWFYNUUNMGUUDUUABOZUUBBOZRZYNYTGOZRZUUMUUAUUBBDYTWG
      YTEWGWHUVPYTUAVAZNVAZWIZSZNTVFWJVBZUFUATWKPZUFZUVNUUMQZUVOUWCYNUVOUWCVFWS
      WLWMOVGWKVFVGWNVBWOWMWJVBZOUVOUWCVEWPWQUANCUWAUWEVGVFGYTUWAWRUWEWRIJWTXAU
      TXBUVPUVTUWDUANUWBUWAUVPUVQUWBOZUVRUWAOZUVTUWDQZUVQTSZUVQWKSZXCZUVPUWGUWH
      QUWFUWKUVPUWGUWHUWIUVPUWGRZUWHQUWJUWIUWLUWHUWIUWLRUVTYTTUVRWIZSZUWDUWIUVT
      UWNVEUWLUWIUVSUWMYTUVQTUVRXIXDXEUWLUWNUWDQUWIUWLUWDUWNDUWMPZBOZUWMEPZBOZR
      ZHUWMSZQZYNUWGUXAUVOBCDEFGHNIJKLXFXGUWNUVNUWSUUMUWTUWNUVLUWPUVMUWRUWNUUAU
      WOBYTUWMDUHXHUWNUUBUWQBYTUWMEUIXHUPYTUWMHXRXJXKXBXLXMUWLUWHUWJYTWKUVRWIZS
      ZUWDQUWLUWDUXCDUXBPZBOZUXBEPZBOZRZHUXBSZQZYNUWGUXJUVOBCDEFGHNIJKLXNXGUXCU
      VNUXHUUMUXIUXCUVLUXEUVMUXGUXCUUAUXDBYTUXBDUHXHUXCUUBUXFBYTUXBEUIXHUPYTUXB
      HXRXJXKUWJUVTUXCUWDUWJUVSUXBYTUVQWKUVRXIXDXOXPXQXSUVQTWKXTYAYHYBYCYDYEYIY
      FYSUUDAMGUUEYRUUCBUUEYPUUAYQUUBYOYTDUHYOYTEUIUKULYJYG $.
  $}

  ${
    pgn4cyclex.g $e |- G = ( 5 gPetersenGr 2 ) $.
    $d F a b c d $.  $d G a b c d x $.  $d P a b c d $.
    $( A cycle in a Petersen graph G(5,2) does not have length 4.  (Contributed
       by AV, 9-Nov-2025.) $)
    pgn4cyclex $p |- ( F ( Cycles ` G ) P -> ( # ` F ) =/= 4 ) $=
      ( va vb vc vd vx cfv c4 wne wa cv cpr wcel w3a wrex ax-mp eqid ccycls wbr
      chash wceq cedg cvtx cupgr cusgr c5 c2 cgpg pgjsgr eqeltri upgr4cycl4dv4e
      co usgrupgr mp3an1 wss cnbgr wb nbusgreledg bicomd biimpi ad3antrrr prcom
      wreu eleq1i sylibr ad3antlr simprl2 adantl pgnbgreunbgr syl2an23an simpll
      wn simplr simpr anim12i simprr2 df-3an 4cycl2vnunb pm2.21dd ex rexlimdvva
      rexlimivv syl neqne pm2.61d1 ) BACUAJUBZBUCJZKUDZWJKLZWIWKWLWIWKMENZFNZOC
      UEJZPZWNGNZOZWOPZMZWQHNZOWOPXAWMOWOPMZMZWMWNLZWMWQLZWMXALZQZWNWQLZWNXALZW
      QXALZQZMZMZHCUFJZRGXNRZFXNREXNRZWLCUGPZWIWKXPCUHPZXQCUIUJUKUOUHDULUMZCUPS
      AWOBCXNEFGHXNTZWOTZUNUQXOWLEFXNXNWMXNPZWNXNPZMZXMWLGHXNXNYDWQXNPZXAXNPZMZ
      MZXMWLYHXMMZWMINZOYJWQOOWOURIXNVFZWLXMWMCWNUSUOZPZWQYLPZYHXEYKWPYMWSXBXLW
      PYMXRWPYMUTXSXRYMWPWOCWNWMYAVAVBSVCVDWSYNWPXBXLWSWQWNOZWOPZYNWSYPWRYOWOWN
      WQVEVGVCXRYNYPUTXSWOCWNWQYAVASVHVIXMXEYHXDXEXFXKXCVJVKIWOCWMWQYLXNWNDXTYA
      YLTVLVMXMWTXBYHYCYFXIQZYKVOWTXBXLVNWTXBXLVPYIYCYFMZXIMYQYHYRXMXIYDYCYGYFY
      BYCVQYEYFVQVRXHXIXJXGXCVSVRYCYFXIVTVHIWMWNWQXAWOXNWAVMWBWCWDWEWFWCWJKWGWH
      $.
  $}

  $( In the Petersen graph G(5,2), there is no cycle of length 4.  (Contributed
     by AV, 22-Nov-2025.) $)
  pg4cyclnex $p |- -. E. p E. f ( f ( Cycles ` ( 5 gPetersenGr 2 ) ) p
                                   /\ ( # ` f ) = 4 ) $=
    ( cv c5 c2 cgpg co ccycls cfv wbr chash c4 wceq wa wex wn wne wo wal bitri
    eqid pgn4cyclex imori gen2 2nexaln ianor df-ne bicomi orbi2i 2albii mpbir )
    ACZBCZDEFGZHIJZULKIZLMZNZAOBOPZUOPZUPLQZRZASBSZVBBAUOVAUMULUNUNUAUBUCUDUSUR
    PZASBSVCURBAUEVDVBBAVDUTUQPZRVBUOUQUFVEVAUTVAVEUPLUGUHUITUJTUK $.

  ${
    $d f p $.
    $( The two generalized Petersen graphs G(5,K) of order 10, which are the
       Petersen graph G(5,2) and the 5-prism G(5,1), are not isomorphic.
       (Contributed by AV, 22-Nov-2025.) $)
    gpg5ngric $p |- -. ( 5 gPetersenGr 1 ) ~=gr ( 5 gPetersenGr 2 ) $=
      ( vf vp c5 c1 cgpg co cuspgr wcel c2 wa cv ccycls cfv wbr c4 wex wn cusgr
      5eluz3 pm3.2i chash wceq cgric cuz cdiv cceil cfzo 1elfzo1ceilhalf1 ax-mp
      c3 gpgusgra usgruspgr mp2b gpgprismgr4cyclex pg4cyclnex cycldlenngric mp2
      pglem ) CDEFZGHZCIEFZGHZJAKZBKZUSLMNVCUAMOUBZJAPBPZVCVDVALMNVEJAPBPQZJUSV
      AUCNQUTVBCUJUDMHZDDCIUEFUFMUGFZHZJUSRHUTVHVJSVHVJSCUHUITDCUKUSULUMVHIVIHZ
      JVARHVBVHVKSURTICUKVAULUMTVFVGVHVFSACBUNUIABUOTAUSVAOBUPUQ $.
  $}

  ${
    $d g h $.
    $( There are two different locally isomorphic graphs which are not
       isomorphic.  (Contributed by AV, 23-Nov-2025.) $)
    lgricngricex $p |- E. g E. h ( g ~=lgr h /\ -. g ~=gr h ) $=
      ( c5 c1 cgpg co c2 cgrlic wbr cgric wn cv wa wex gpg5grlic gpg5ngric ovex
      wceq breq12 notbid anbi12d spc2ev mp2an ) CDEFZCGEFZHIZUDUEJIZKZALZBLZHIZ
      UIUJJIZKZMZBNANOPUNUFUHMABUDUECDEQCGEQUIUDRUJUERMZUKUFUMUHUIUDUJUEHSUOULU
      GUIUDUJUEJSTUAUBUC $.
  $}

  $( Two consecutive (according to the numbering) inside vertices of the
     Petersen graph G(5,2) are not connected by an edge, but are connected by
     an edge in a 5-prism G(5,1).  (Contributed by AV, 29-Dec-2025.) $)
  gpg5edgnedg $p |- ( { <. 1 , 0 >. , <. 1 , 1 >. }
                      e. ( Edg ` ( 5 gPetersenGr 1 ) )
                   /\ { <. 1 , 0 >. , <. 1 , 1 >. }
                      e/ ( Edg ` ( 5 gPetersenGr 2 ) ) ) $=
    ( vx c1 cc0 cop cpr c5 co wcel c2 caddc cmo wa pm3.2i c3 wne cvv wo 1ex a1i
    wceq cgpg cedg cfv wnel cv w3o cfzo wrex wex c0ex eleq1 opeq2 oveq1d opeq2d
    oveq1 preq12d eqeq2d 3orbi123d anbi12d cn 5nn lbfzo0 mpbir 0p1e1 oveq1i clt
    cr wbr 5re 1lt5 1mod mp2an eqtr2i opeq2i preq2i 3mix3i ceqsexv2d df-rex cuz
    cceil wb 5eluz3 cz cle 2z rehalfcli ceilcl ax-mp 2ltceilhalf eluz2 mpbir3an
    cdiv fzo1lb eqid gpgedgel wn w3a wral opex ax-1ne0 orci opthne orcd prneimg
    pglem olci prneimg2 mp1i mpbir2and wi 1ne2 2cn addlidi cn0 2nn0 2lt5 elfzo0
    mpsyl zmodidfzoimp eqtrid adantr neeqtrd olcd ex orc pm2.61ine neirr biorfi
    a1d bitr4i orbi12d mpbird 0re 3pos ltneii 1p2e3 3nn0 3lt5 olc df-ne ralnex
    3jca ralrimiva 3ioran 3anbi123i ralbii bitr3i sylibr mtbird nelir ) BCDZBBD
    ZEZFBUAGZUBUCZHZUUMFIUAGZUBUCZUDUUPUUMCAUEZDZCUUSBJGZFKGZDZEZTZUUMUUTBUUSDZ
    EZTZUUMUVFBUVBDZEZTZUFZACFUGGZUHZUVNUUSUVMHZUVLLZAUIUVPCUVMHZUUMCCDZCCBJGZF
    KGZDZEZTZUUMUVRUUKEZTZUUMUUKBUVTDZEZTZUFZLACUJUUSCTZUVOUVQUVLUWIUUSCUVMUKUW
    JUVEUWCUVHUWEUVKUWHUWJUVDUWBUUMUWJUUTUVRUVCUWAUUSCCULZUWJUVBUVTCUWJUVAUVSFK
    UUSCBJUOUMZUNUPUQUWJUVGUWDUUMUWJUUTUVRUVFUUKUWKUUSCBULZUPUQUWJUVJUWGUUMUWJU
    VFUUKUVIUWFUWMUWJUVBUVTBUWLUNUPUQURUSUVQUWIUVQFUTHZVAFVBVCUWHUWCUWEUULUWFUU
    KBUVTBUVTBFKGZBUVSBFKVDVEFVGHBFVFVHUWOBTVIVJFVKVLVMVNVOVPMVQUVLAUVMVRVCFNVS
    UCHZBBFIWLGZVTUCZUGGZHZUUPUVNWAWBUWTUWRIVSUCHZUXAIWCHUWRWCHZIUWRWDVHZWEUWQV
    GHUXBFVIWFUWQWGWHUWPUXCWBFWIWHIUWRWJWKUWRWMVCAUUOUUNUVMUWSBFUUMUVMWNZUWSWNZ
    UUNWNUUOWNWOVLVCUUMUURUWPIUWSHZUUMUURHZWPWBXEUWPUXFLZUXGUVEUVHUUMUVFBUUSIJG
    ZFKGZDZEZTZUFZAUVMUHZUXHUUMUVDOZUUMUVGOZUUMUXLOZWQZAUVMWRZUXOWPZUXHUXSAUVMU
    XHUVOLZUXPUXQUXRUUKPHZUULPHZLZUUTPHZUVCPHZLZLUYBUUKUUTOZUUKUVCOZLZUULUUTOZU
    ULUVCOLZQUXPUYEUYHUYCUYDBCWSBBWSMZUYFUYGCUUSWSZCUVBWSMMUYBUYKUYMUYKUYBUYIUY
    JUYIBCOZCUUSOZQUYPUYQWTXABCCUUSRUJXBVCZUYJUYPCUVBOZQUYPUYSWTXABCCUVBRUJXBVC
    MSXCUUKUULUUTUVCPPPPXDXRUYBUXQUYIUULUVFOZQZUUKUVFOZUYLQZVUAUYBUYIUYTUYRXASV
    UCUYBUYLVUBUYLUYPBUUSOZQUYPVUDWTXABBCUUSRRXBVCXFSUYEUYFUVFPHZLZLUXQVUAVUCLW
    AUYBUYEVUFUYNUYFVUEUYOBUUSWSZMMUUKUULUUTUVFPPPPXGXHXIUYBUXRVUBUULUXKOZQZUUK
    UXKOZUYTQZUYBVUIUYQBUXJOZQZUYBVUMXJCUUSCUUSTZUYBVUMVUNUYBLZVULUYQVUOBIUXJBI
    OVUOXKSVUNIUXJTUYBVUNICIJGZFKGZUXJVUQIFKGZIVUPIFKIXLXMVEIUVMHZVURITVUSIXNHU
    WNIFVFVHXOVAXPIFXQWKIFXSWHVMVUNVUPUXIFKCUUSIJUOUMXTYAYBYCYDUYQVUMUYBUYQVULY
    EYIYFUYBVUBUYQVUHVULVUBUYQWAUYBVUBBBOZUYQQUYQBCBUUSRUJXBVUTUYQBYGZYHYJSVUHV
    ULWAUYBVUHVUTVULQVULBBBUXJRRXBVUTVULVVAYHYJSYKYLUYBVUKCUXJOZVUDQZUYBVVCXJBU
    USBUUSTZUYBVVCVVDUYBLZVVBVUDVVECNUXJCNOVVECNYMYNYOSVVDNUXJTUYBVVDNBIJGZFKGZ
    UXJVVGNFKGZNVVFNFKYPVENUVMHZVVHNTVVINXNHUWNNFVFVHYQVAYRNFXQWKNFXSWHVMVVDVVF
    UXIFKBUUSIJUOUMXTYAYBXCYDVUDVVCUYBVUDVVBYSYIYFUYBVUJVVBUYTVUDVUJVVBWAUYBVUJ
    VUTVVBQVVBBCBUXJRUJXBVUTVVBVVAYHYJSUYTVUDWAUYBUYTVUTVUDQVUDBBBUUSRRXBVUTVUD
    VVAYHYJSYKYLUYEVUEUXKPHZLZLUXRVUIVUKLWAUYBUYEVVKUYNVUEVVJVUGBUXJWSMMUUKUULU
    VFUXKPPPPXGXHXIUUBUUCUYAUXNWPZAUVMWRUXTUXNAUVMUUAVVLUXSAUVMVVLUVEWPZUVHWPZU
    XMWPZWQUXSUVEUVHUXMUUDUXPVVMUXQVVNUXRVVOUUMUVDYTUUMUVGYTUUMUXLYTUUEYJUUFUUG
    UUHAUURUUQUVMUWSIFUUMUXDUXEUUQWNUURWNWOUUIVLUUJM $.

  ${
    $d a b f g h $.
    $( In general, the image of an edge of a graph by a local isomprphism is
       not an edge of the other graph, proven by an example (see
       ~ gpg5edgnedg ).  This theorem proves that the analogon
       ` ( ( ( G e. USPGraph /\ H e. USPGraph ) /\ ( F e. ( G GraphLocIso H ) `
       ` /\ K e. I ) ) -> ( F " K ) e. E ) ` of ~ grimedgi for ordinarily
       isomorphic graphs does not hold in general.  (Contributed by AV,
       30-Dec-2025.) $)
    grlimedgnedg $p |- E. g e. USGraph E. h e. USGraph
                       E. f e. ( g GraphLocIso h )
                       E. a e. ( Vtx ` g ) E. b e. ( Vtx ` g )
                       ( { a , b } e. ( Edg ` g )
                         /\ { ( f ` a ) , ( f ` b ) } e/ ( Edg ` h ) ) $=
      ( cv cpr cedg cfv wcel wnel wa wrex cgrlim co cusgr wtru c5 c1 wceq oveq1
      cvtx cgpg c2 fveq2 eleq2d anbi1d rexeqbidv oveq2 neleq12d anbi2d 2rexbidv
      eqidd c3 cuz 5eluz3 gpgprismgrusgra mp1i pgjsgr a1i cid cc0 cfzo cxp cres
      cop fveq1 preq12d preq1 eleq1d preq1d anbi12d preq2d gpg5grlim 1elpr01 cn
      preq2 lbfzo0 mpbir opelxpii cdiv cceil 1elfzo1ceilhalf1 ax-mp eqid gpgvtx
      5nn mp2an eleqtrri cn0 cz clt 1nn0 nnzi 1lt5 elfzo0z mpbir3an gpg5edgnedg
      wbr wb fvresi preq12i neleq1 anbi2i 3rspcedvdw 2rspcedvdw mptru ) DFZEFZG
      ZBFZHIZJZXHAFZIZXIXNIZGZCFZHIZKZLZEXKUBIZMZDYBMZAXKXRNOZMZCPMBPMQYFXJRSUC
      OZHIZJZXTLZEYGUBIZMZDYKMZAYGXRNOZMYIXQRUDUCOZHIZKZLZEYKMDYKMZAYGYONOZMBCY
      GYOPPXKYGTZYDYMAYEYNXKYGXRNUAUUAYCYLDYBYKXKYGUBUEZUUAYAYJEYBYKUUBUUAXMYIX
      TUUAXLYHXJXKYGHUEUFUGUHUHUHXRYOTZYMYSAYNYTXRYOYGNUIUUCYJYRDEYKYKUUCXTYQYI
      UUCXQXQXSYPUUCXQUMXRYOHUEUJUKULUHRUNUOIJZYGPJQUPRUQURYOPJQUSUTQYRYIXHVAVB
      SGZVBRVCOZVDZVEZIZXIUUHIZGZYPKZLSVBVFZXIGZYHJZUUMUUHIZUUJGZYPKZLUUMSSVFZG
      ZYHJZUUPUUSUUHIZGZYPKZLZADEUUHUUMUUSYTYKYKXNUUHTZYQUULYIUVFXQUUKYPYPUVFXO
      UUIXPUUJXHXNUUHVGXIXNUUHVGVHUVFYPUMUJUKXHUUMTZYIUUOUULUURUVGXJUUNYHXHUUMX
      IVIVJUVGUUKUUQYPYPUVGUUIUUPUUJXHUUMUUHUEVKUVGYPUMUJVLXIUUSTZUUOUVAUURUVDU
      VHUUNUUTYHXIUUSUUMVQVJUVHUUQUVCYPYPUVHUUJUVBUUPXIUUSUUHUEVMUVHYPUMUJVLUUH
      YTJQVNUTUUMYKJQUUMUUGYKSVBUUEUUFVOVBUUFJRVPJZWGRVRVSVTZUVISSRUDWAOWBIVCOZ
      JZYKUUGTWGUUDUVLUPRWCWDUUFUVKSRUVKWEUUFWEWFWHZWIUTUUSYKJQUUSUUGYKSSUUEUUF
      VOSUUFJSWJJRWKJSRWLWSWMRWGWNWOSRWPWQVTZUVMWIUTUVEQUVEUVAUUTYPKZLWRUVDUVOU
      VAUVCUUTTUVDUVOWTUUPUUMUVBUUSUUMUUGJUUPUUMTUVJUUGUUMXAWDUUSUUGJUVBUUSTUVN
      UUGUUSXAWDXBUVCUUTYPXCWDXDVSUTXEXFXG $.
  $}

$(
  @{
    gpg31grim3prism.v @e |- V = ( { 0 , 1 , 2 } u. { 3 , 4 , 5 } ) @.
    gpg31grim3prism.e @e |- E = ( { { 0 , 1 } , { 1 , 2 } , { 2 , 0 } }
                             u. ( { { 3 , 4 } , { 4 , 5 } , { 5 , 3 } }
                               u. { { 0 , 3 } , { 1 , 4 } , { 2 , 5 } } ) ) @.
    @( The smallest generalized Petersen graph G(3,1) is (isomorphic to) the
       3-prism. (Contributed  by AV, 26-Aug-2025.) @)
    gpg31grim3prism  @p |- ( 3 gPetersenGr 1 ) ~=gr <. V , ( _I |` E ) >. @=
      ? @.
  @}
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Loop-free graphs - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d E x $.  $d V x $.
    1hegrlfgr.a $e |- ( ph -> A e. X ) $.
    1hegrlfgr.b $e |- ( ph -> B e. V ) $.
    1hegrlfgr.c $e |- ( ph -> C e. V ) $.
    1hegrlfgr.n $e |- ( ph -> B =/= C ) $.
    1hegrlfgr.x $e |- ( ph -> E e. ~P V ) $.
    1hegrlfgr.i $e |- ( ph -> ( iEdg ` G ) = { <. A , E >. } ) $.
    1hegrlfgr.e $e |- ( ph -> { B , C } C_ E ) $.
    $( A graph ` G ` with one hyperedge joining at least two vertices is a
       loop-free graph.  (Contributed by AV, 23-Feb-2021.) $)
    1hegrlfgr $p |- ( ph -> ( iEdg ` G ) : { A }
                                        --> { x e. ~P V | 2 <_ ( # ` x ) } ) $=
      ( csn c2 chash wcel cv cfv cle wbr cpw crab ciedg cop wf1o f1osng syl2anc
      wf f1of syl prid1g sseldd prid2g nehash2 wceq fveq2 breq2d elrab sylanbrc
      cpr snssd fssd feq1d mpbird ) ACQZRBUAZSUBZUCUDZBHUEZUFZGUGUBZULVIVNCFUHQ
      ZULAVIFQZVNVPAVIVQVPUIZVIVQVPULACITFVMTZVRJNCFIVMUJUKVIVQVPUMUNAFVNAVSRFS
      UBZUCUDZFVNTNADEFVMNADEVDZFDPADHTDWBTKDEHUOUNUPAWBFEPAEHTEWBTLDEHUQUNUPMU
      RVLWABFVMVJFUSVKVTRUCVJFSUTVAVBVCVEVFAVIVNVOVPOVGVH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Walks - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c UPWalks $.

  $( Extend class notation with walks (of a pseudograph). $)
  cupwlks $a class UPWalks $.

  ${
    $d f g k p $.
    $( Define the set of all walks (in a pseudograph), called "simple walks" in
       the following.

       According to Wikipedia ("Path (graph theory)",
       ~ https://en.wikipedia.org/wiki/Path_(graph_theory) , 3-Oct-2017):  "A
       walk of length k in a graph is an alternating sequence of vertices and
       edges, v0 , e0 , v1 , e1 , v2 , ... , v(k-1) , e(k-1) , v(k) which
       begins and ends with vertices.  If the graph is undirected, then the
       endpoints of e(i) are v(i) and v(i+1)."

       According to Bollobas:  " A walk W in a graph is an alternating sequence
       of vertices and edges x0 , e1 , x1 , e2 , ... , e(l) , x(l) where e(i) =
       x(i-1)x(i), 0<i<=l.", see Definition of [Bollobas] p. 4.

       Therefore, a walk can be represented by two mappings f from { 1 , ... ,
       n } and p from { 0 , ... , n }, where f enumerates the (indices of the)
       edges, and p enumerates the vertices.  So the walk is represented by the
       following sequence: p(0) e(f(1)) p(1) e(f(2)) ... p(n-1) e(f(n)) p(n).

       Although this definition is also applicable for arbitrary hypergraphs,
       it allows only walks consisting of not proper hyperedges (i.e. edges
       connecting at most two vertices).  Therefore, it should be used for
       pseudographs only.  (Contributed by Alexander van der Vekens and Mario
       Carneiro, 4-Oct-2017.)  (Revised by AV, 28-Dec-2020.) $)
    df-upwlks $a |- UPWalks = ( g e. _V |-> { <. f , p >. |
                                ( f e. Word dom ( iEdg ` g )
                                /\ p : ( 0 ... ( # ` f ) ) --> ( Vtx ` g )
                                /\ A. k e. ( 0 ..^ ( # ` f ) )
                                   ( ( iEdg ` g ) ` ( f ` k ) )
                                   = { ( p ` k ) , ( p ` ( k + 1 ) ) } ) } ) $.
  $}

  ${
    $d G f g k p $.  $d I f g p $.  $d V g p $.  $d W f g $.
    upwlksfval.v $e |- V = ( Vtx ` G ) $.
    upwlksfval.i $e |- I = ( iEdg ` G ) $.
    $( The set of simple walks (in an undirected graph).  (Contributed by
       Alexander van der Vekens, 19-Oct-2017.)  (Revised by AV,
       28-Dec-2020.) $)
    upwlksfval $p |- ( G e. W -> ( UPWalks ` G ) = { <. f , p >. |
            ( f e. Word dom I /\ p : ( 0 ... ( # ` f ) ) --> V
              /\ A. k e. ( 0 ..^ ( # ` f ) )
                 ( I ` ( f ` k ) ) = { ( p ` k ) , ( p ` ( k + 1 ) ) } ) } ) $=
      ( vg wcel cv ciedg cfv cc0 co cvtx wceq copab cvv cword chash wf c1 caddc
      cdm cfz cpr cfzo wral w3a cupwlks df-upwlks fveq2 eqtr4di dmeqd wrdeq syl
      eleq2d feq3d fveq1d eqeq1d ralbidv 3anbi123d opabbidv elex 3anass opabbii
      wa fvexi dmex wrdexg mp1i cab a1i mapex sylancr wss simpl ss2abi opabex3d
      ovex ssexd eqeltrid fvmptd3 ) CFKZJCALZJLZMNZUFZUAZKZOWGUBNZUGPZWHQNZGLZU
      CZBLZWGNZWINZWRWPNWRUDUEPWPNUHZRZBOWMUIPZUJZUKZAGSWGDUFZUAZKZWNEWPUCZWSDN
      ZXARZBXCUJZUKZAGSZTULTAJBGUMWHCRZXEXMAGXOWLXHWQXIXDXLXOWKXGWGXOWJXFRWKXGR
      XOWIDXOWICMNDWHCMUNIUOZUPWJXFUQURUSXOWOEWPWNXOWOCQNEWHCQUNHUOUTXOXBXKBXCX
      OWTXJXAXOWSWIDXPVAVBVCVDVECFVFWFXNXHXIXLVIZVIZAGSTXMXRAGXHXIXLVGVHWFXQAGX
      GTXFTKXGTKWFDDCMIVJVKXFTVLVMWFXHVIZXQGVNZXIGVNZTXSWNTKETKZYATKOWMUGWBYBXS
      ECQHVJVOWNETTGVPVQXTYAVRXSXQXIGXIXLVSVTVOWCWAWDWE $.

    $d F f k p $.  $d P f k p $.  $d V f $.
    $( Properties of a pair of functions to be a simple walk.  (Contributed by
       Alexander van der Vekens, 20-Oct-2017.)  (Revised by AV,
       28-Dec-2020.) $)
    isupwlk $p |- ( ( G e. W /\ F e. U /\ P e. Z ) -> ( F ( UPWalks ` G ) P
        <-> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V
              /\ A. k e. ( 0 ..^ ( # ` F ) )
                 ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } ) ) ) $=
      ( vf vp wcel w3a cfv cv cc0 co wceq cupwlks wbr cop cdm cword chash wf c1
      cfz caddc cpr cfzo copab df-br upwlksfval 3ad2ant1 eleq2d bitrid wb eleq1
      wral wa adantr simpr fveq2 oveq2d feq12d fveq1 fveq2d eqeqan12d raleqbidv
      preq12d 3anbi123d opelopabga 3adant1 bitrd ) EHNZDBNZAINZOZDAEUAPZUBZDAUC
      ZLQZFUDUEZNZRWDUFPZUISZGMQZUGZCQZWDPZFPZWKWIPZWKUHUJSZWIPZUKZTZCRWGULSZVA
      ZOZLMUMZNZDWENZRDUFPZUISZGAUGZWKDPZFPZWKAPZWOAPZUKZTZCRXEULSZVAZOZWBWCWAN
      VTXCDAWAUNVTWAXBWCVQVRWAXBTVSLCEFGHMJKUOUPUQURVRVSXCXPUSVQXAXPLMDABIWDDTZ
      WIATZVBZWFXDWJXGWTXOXQWFXDUSXRWDDWEUTVCXSWHXFGWIAXQXRVDXQWHXFTXRXQWGXERUI
      WDDUFVEZVFVCVGXSWRXMCWSXNXQWSXNTXRXQWGXERULXTVFVCXQXRWMXIWQXLXQWLXHFWKWDD
      VHVIXRWNXJWPXKWKWIAVHWOWIAVHVLVJVKVMVNVOVP $.

    $d F f k p $.  $d P f k p $.  $d V f $.
    $( Generalization of ~ isupwlk :  Conditions for two classes to represent a
       simple walk.  (Contributed by AV, 5-Nov-2021.) $)
    isupwlkg $p |- ( G e. W -> ( F ( UPWalks ` G ) P <-> ( F e. Word dom I
              /\ P : ( 0 ... ( # ` F ) ) --> V
              /\ A. k e. ( 0 ..^ ( # ` F ) )
                 ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } ) ) ) $=
      ( vf vp wcel cvv w3a cupwlks cfv cc0 cfz co cv wbr cdm cword chash wf cpr
      c1 caddc wceq cfzo wral wi upwlksfval brfvopab a1i wa elex cpm ovex fvexi
      cvtx fpm elexd anim12i 3adant3 ex 3anass imbitrrdi wb isupwlk pm5.21ndd )
      DGLZDMLZCMLZAMLZNZCADOPUAZCEUBUCZLZQCUDPZRSZFAUEZBTZCPEPWCAPWCUGUHSZAPUFU
      IBQVTUJSUKZNZVQVPULVLJTZVRLQWGUDPZRSFKTZUEWCWGPEPWCWIPWDWIPUFUIBQWHUJSUKN
      JKCAODJBDEFMKHIUMUNUOVLWFVMVNVOUPZUPZVPVLWFWKVLVMWFWJDGUQVSWBWJWEVSVNWBVO
      CVRUQWBAFWAURSWAFAQVTRUSFDVAHUTVBVCVDVEVDVFVMVNVOVGVHVPVQWFVIULVLAMBCDEFM
      MHIVJUOVK $.

    $( Basic properties of a simple walk.  (Contributed by Alexander van der
       Vekens, 31-Oct-2017.)  (Revised by AV, 29-Dec-2020.) $)
    upwlkbprop $p |- ( F ( UPWalks ` G ) P
                     -> ( G e. _V /\ F e. _V /\ P e. _V ) ) $=
      ( vf vp vk cvv wcel cupwlks cfv wbr w3a wa cv co c0 wi cdm cword chash wf
      cc0 cfz c1 caddc cpr wceq cfzo wral copab upwlksfval breqd brabv biimtrdi
      imdistani 3anass sylibr ex wn fvprc breq br0 pm2.21i syl pm2.61i ) CKLZBA
      CMNZOZVJBKLZAKLZPZUAZVJVLVOVJVLQVJVMVNQZQVOVJVLVQVJVLBAHRZDUBUCLUFVRUDNZU
      GSEIRZUEJRZVRNDNWAVTNWAUHUISVTNUJUKJUFVSULSUMPZHIUNZOVQVJVKWCBAHJCDEKIFGU
      OUPWBHIBAUQURUSVJVMVNUTVAVBVJVCVKTUKZVPCMVDWDVLBATOZVOBAVKTVEWEVOBAVFVGUR
      VHVI $.
  $}

  ${
    $d F k $.  $d G k $.  $d P k $.
    $( A simple walk is a walk.  (Contributed by AV, 30-Dec-2020.)  (Proof
       shortened by AV, 27-Feb-2021.) $)
    upwlkwlk $p |- ( F ( UPWalks ` G ) P -> F ( Walks ` G ) P ) $=
      ( vk cvv wcel w3a cupwlks cfv wbr cwlks ciedg cvtx eqid upwlkbprop cc0 co
      wceq wral idd cdm cword chash cfz wf cv c1 cpr cfzo csn wss wif ifpprsnss
      caddc wi wa a1i ralimdva 3anim123d isupwlk iswlk 3imtr4d mpcom ) CEFBEFAE
      FGZBACHIJZBACKIJZABCCLIZCMIZVHNZVGNZOVDBVGUAUBFZPBUCIZUDQVHAUEZDUFZBIVGIZ
      VNAIZVNUGUNQAIZUHZRZDPVLUIQZSZGVKVMVPVQRVOVPUJRVRVOUKULZDVTSZGVEVFVDVKVKV
      MVMWAWCVDVKTVDVMTVDVSWBDVTVSWBUOVDVNVTFUPVPVQVOUMUQURUSAEDBCVGVHEEVIVJUTA
      EDBCVGVHEEVIVJVAVBVC $.

    $( In a pseudograph, a walk is a simple walk.  (Contributed by AV,
       30-Dec-2020.)  (Proof shortened by AV, 2-Jan-2021.) $)
    upgrwlkupwlk $p |- ( ( G e. UPGraph /\ F ( Walks ` G ) P )
                         -> F ( UPWalks ` G ) P ) $=
      ( vk cfv wbr wcel cvv w3a wa cc0 co wceq wral wi eqid adantr exp31 impcom
      cpr cwlks cupgr cupwlks wlkv ciedg cdm cword chash cfz cvtx wf cv c1 cfzo
      caddc csn wss wif iswlk simpr1 simpr2 wn df-ifp dfsn2 preq2 eqtrid eqeq2d
      wo biimpa a1d cedg simpr simpl upgredginwlk syl2anr imp wne simprr simplr
      df-ne fvexd id sylbir adantl upgredgpr syl31anc eqcomd mpd com12 biimtrid
      3jca jaoi ralimdva ex com23 3impia sylbid impd wb isupwlk mpbird mpid ) B
      ACUAEFZCUBGZBACUCEFZXCXDCHGBHGAHGIZXEABCUDXCXDXFXEXCXDJZXFJXEBCUEEZUFUGGZ
      KBUHEZUILCUJEZAUKZDULZBEXHEZXMAEZXMUMUOLZAEZTZMZDKXJUNLZNZIZXFXGYBXFXCXDY
      BXFXCXIXLXOXQMZXNXOUPZMZXRXNUQZURZDXTNZIZXDYBOAHDBCXHXKHHXKPZXHPZUSXFXDYI
      YBXFXDYIYBXFXDJZYIJXIXLYAYLXIXLYHUTYLXIXLYHVAYIYLYAXIXLYHYLYAOXIXLJZYLYHY
      AYMYLYHYAOYMYLJZYGXSDXTYGYCYEJZYCVBZYFJZVHZYNXMXTGZJZXSYCYEYFVCYRYTXSYOYT
      XSOYQYOXSYTYCYEXSYCYDXRXNYCYDXOXOTXRXOVDXOXQXOVEVFVGVIVJYTYQXSYTXNCVKEZGZ
      YQXSOYNYSUUBYLXDXIYSUUBOYMXFXDVLXIXLVMUUABCXHXMYKUUAPZVNVOVPYTUUBYQXSYTUU
      BJZYQJZXRXNUUEXDUUBYFXOHGZXQHGZXOXQVQZIZXRXNMUUDXDYQYTXDUUBYNXDYSYMXFXDVR
      QQQYTUUBYQVSUUDYPYFVRYQUUIUUDYPUUIYFYPUUHUUIXOXQVTUUHUUFUUGUUHUUHXMAWAUUH
      XPAWAUUHWBWKWCQWDXOXQXNHUUACXKHYJUUCWEWFWGRWHWIWLWIWJWMWNWOWPSWKRWOWQWRSX
      FXEYBWSXGAHDBCXHXKHHYJYKWTWDXARXBS $.
  $}

  $( In a pseudograph, the definitions for a walk and a simple walk are
     equivalent.  (Contributed by AV, 30-Dec-2020.) $)
  upgrwlkupwlkb $p |- ( G e. UPGraph -> ( F ( Walks ` G ) P
                                         <-> F ( UPWalks ` G ) P ) ) $=
    ( cupgr wcel cwlks cfv wbr cupwlks upgrwlkupwlk ex upwlkwlk impbid1 ) CDEZB
    ACFGHZBACIGHZNOPABCJKABCLM $.

  ${
    $d G k $.  $d F k $.  $d P k $.
    upgrisupwlkALT.v $e |- V = ( Vtx ` G ) $.
    upgrisupwlkALT.i $e |- I = ( iEdg ` G ) $.
    $( Alternate proof of ~ upgriswlk using the definition of ` UPGraph ` and
       related theorems.  (Contributed by AV, 2-Jan-2021.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    upgrisupwlkALT $p |- ( ( G e. UPGraph /\ F e. U /\ P e. Z )
                      -> ( F ( Walks ` G ) P
        <-> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V
              /\ A. k e. ( 0 ..^ ( # ` F ) )
                 ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } ) ) ) $=
      ( cupgr wcel w3a cwlks cfv wbr cupwlks cdm cc0 co cword chash wf cv caddc
      cfz c1 cpr wceq cfzo wral wb upgrwlkupwlkb 3ad2ant1 isupwlk bitrd ) EKLZD
      BLZAHLZMDAENOPZDAEQOPZDFRUALSDUBOZUFTGAUCCUDZDOFOVCAOVCUGUETAOUHUICSVBUJT
      UKMUQURUTVAULUSADEUMUNABCDEFGKHIJUOUP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Edges of graphs expressed as sets of unordered pairs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d G p $.
    $( The set of edges of a pseudograph is a subset of the set of unordered
       pairs of vertices.  (Contributed by AV, 24-Nov-2021.) $)
    upgredgssspr $p |- ( G e. UPGraph
                         -> ( Edg ` G ) C_ ( Pairs ` ( Vtx ` G ) ) ) $=
      ( vp cupgr wcel cedg cfv cv chash c2 cle wbr cvtx cpw cdif crab upgredgss
      c0 csn cspr cvv wceq fvex sprvalpwle2 ax-mp sseqtrrdi ) ACDAEFBGHFIJKBALF
      ZMQRNOZUFSFZBAPUFTDUHUGUAALUBUFTBUCUDUE $.
  $}

  ${
    $d P e q v $.  $d V e q v $.  $d W e v $.
    uspgrsprf.p $e |- P = ~P ( Pairs ` V ) $.
    uspgrsprf.g $e |- G = { <. v , e >. | ( v = V /\ E. q e. USPGraph
                                  ( ( Vtx ` q ) = v /\ ( Edg ` q ) = e ) ) } $.
    $( The set ` G ` of "simple pseudographs" for a fixed set ` V ` of vertices
       is a subset of a Cartesian product.  For more details about the class
       ` G ` of all "simple pseudographs" see comments on ~ uspgrbisymrel .
       (Contributed by AV, 24-Nov-2021.) $)
    uspgropssxp $p |- ( V e. W -> G C_ ( W X. P ) ) $=
      ( wcel cv wceq cvtx cfv cedg wa cuspgr wrex cspr wss cxp wb eqcoms adantr
      copab eleq1 biimpac wi w3a cpw uspgrupgr upgredgssspr syl 3ad2ant1 simp2l
      cupgr simp3 eqtrd fveq2d sseqtrd fvex elpw sylibr eqcomd 3ad2ant2 3eltr4d
      simpr a1i 3exp rexlimiv impcom adantl opabssxpd eqsstrid ) EFJZDAKZELZGKZ
      MNZVPLZVRONZCKZLZPZGQRZPZACUEFBUAIVOWFACFBWFVOVPFJZVQVOWGUBZWEWHEVPEVPFUF
      UCUDUGWFWBBJZVOWEVQWIWDVQWIUHGQVRQJZWDVQWIWJWDVQUIZWAESNZUJZWBBWKWAWLTWAW
      MJWKWAVSSNZWLWJWDWAWNTZVQWJVRUPJWOVRUKVRULUMUNWKVSESWKVSVPEWJVTWCVQUOWJWD
      VQUQURUSUTWAWLVROVAVBVCWDWJWBWALVQWDWAWBVTWCVGVDVEBWMLWKHVHVFVIVJVKVLVMVN
      $.

    $d G g $.
    ${
      $d X g $.
      uspgrsprf.f $e |- F = ( g e. G |-> ( 2nd ` g ) ) $.
      $( The value of the function ` F ` which maps a "simple pseudograph" for
         a fixed set ` V ` of vertices to the set of edges (i.e. range of the
         edge function) of the graph.  Solely for ` G ` as defined here, the
         function ` F ` is a bijection between the "simple pseudographs" and
         the subsets of the set of pairs ` P ` over the fixed set ` V ` of
         vertices, see ~ uspgrbispr .  (Contributed by AV, 24-Nov-2021.) $)
      uspgrsprfv $p |- ( X e. G -> ( F ` X ) = ( 2nd ` X ) ) $=
        ( wcel cv c2nd cfv cvv fveq2 id fvexd fvmptd3 ) HFMZDHDNZOPHOPFEQLUCHOR
        UBSUBHOTUA $.

      $d P e g v $.
      $( The mapping ` F ` is a function from the "simple pseudographs" with a
         fixed set of vertices ` V ` into the subsets of the set of pairs over
         the set ` V ` .  (Contributed by AV, 24-Nov-2021.) $)
      uspgrsprf $p |- F : G --> P $=
        ( cv cfv wcel wceq wa cuspgr cspr wss adantr c2nd cvtx cedg wrex eleq2i
        cop wex copab elopab bitri cupgr uspgrupgr upgredgssspr syl simpr fveq2
        sseq12d adantl mpbid rexlimiva sseq2d vex op2ndd sseq1d mpbird cpw fvex
        wb elpw sylibr exlimivv sylbi fmpti ) DFBDLZUAMZEKVNFNZVNALZCLZUFOZVQGO
        ZHLZUBMZVQOZWAUCMZVROZPZHQUDZPZPZCUGAUGZVOBNZVPVNWHACUHZNWJFWLVNJUEWHAC
        VNUIUJWIWKACWIVOGRMZSZWKWIWNVRWMSZWHWOVSWHVRVQRMZSZWOWGWQVTWFWQHQWAQNZW
        FPWDWBRMZSZWQWRWTWFWRWAUKNWTWAULWAUMUNTWFWTWQVHWRWFWDVRWSWPWCWEUOWCWSWP
        OWEWBVQRUPTUQURUSUTURVTWQWOVHWGVTWPWMVRVQGRUPVATUSURVSWNWOVHWHVSVOVRWMV
        QVRVNAVBCVBVCVDTVEWKVOWMVFZNWNBXAVOIUEVOWMVNUAVGVIUJVJVKVLVM $.

      $d F a b $.  $d G a b g $.  $d P a b $.  $d V a b f e v w $.
      $d V f q w $.
      $( The mapping ` F ` is a one-to-one function from the "simple
         pseudographs" with a fixed set of vertices ` V ` into the subsets of
         the set of pairs over the set ` V ` .  (Contributed by AV,
         25-Nov-2021.) $)
      uspgrsprf1 $p |- F : G -1-1-> P $=
        ( va vw vf cv cfv wceq wi wa wex vb wf1 wf weq wral uspgrsprf wcel c2nd
        uspgrsprfv eqeqan12d cvtx cedg cuspgr copab eleq2i elopab opeq12 eqeq2d
        cop wrex wb eqeq1 adantr eqeq2 bi2anan9 rexbidv anbi12d cbvex2vw 3bitri
        bitri ex equcoms biimtrrdi ad2antrl com12 imp vex op2ndd eqeq12d eqeq12
        3imtr4d exlimivv syl2anb sylbid rgen2 dff13 mpbir2an ) FBEUBFBEUCLOZEPZ
        UAOZEPZQZLUAUDZRZUAFUELFUEABCDEFGHIJKUFWNLUAFFWHFUGZWJFUGZSWLWHUHPZWJUH
        PZQZWMWOWPWIWQWKWRABCDEFGWHHIJKUIABCDEFGWJHIJKUIUJWOWHMOZNOZUSZQZWTGQZH
        OZUKPZWTQZXEULPZXAQZSZHUMUTZSZSZNTMTZWJAOZCOZUSZQZXOGQZXFXOQZXHXPQZSZHU
        MUTZSZSZCTATZWSWMRZWPWOWHYDACUNZUGWHXQQZYDSZCTATXNFYHWHJUOYDACWHUPYJXMA
        CMNAMUDZCNUDZSZYIXCYDXLYMXQXBWHXOXPWTXAUQURYMXSXDYCXKYKXSXDVAYLXOWTGVBV
        CYMYBXJHUMYKXTXGYLYAXIXOWTXFVDXPXAXHVDVEVFVGVGVHVIWPWJYHUGYFFYHWJJUOYDA
        CWJUPVJXNYFYGXMYFYGRMNYFXMYGYEXMYGRACYEXMYGYEXMSZNCUDZXBXQQZWSWMYEXMYOY
        PRZXSXMYQRXRYCXMXSYQXDXSYQRXCXKXDXSYKYQWTGXOVDYQMAMAUDYOYPWTXAXOXPUQVKV
        LVMVNVOVNVPYNWQXAWRXPXCWQXAQYEXLWTXAWHMVQNVQVRVNYEWRXPQZXMXRYRYDXOXPWJA
        VQCVQVRVCVCVSYEXMWMYPVAZXRXMYSRYDXMXRYSXCXRYSRXLXCXRYSWHXBWJXQVTVKVCVOV
        CVPWAVKWBVOWBVPWCWDWELUAFBEWFWG $.

      $d V a f p $.  $d W a b $.  $d W p $.  $d W q $.  $d a q $.
      $( The mapping ` F ` is a function from the "simple pseudographs" with a
         fixed set of vertices ` V ` onto the subsets of the set of pairs over
         the set ` V ` .  (Contributed by AV, 25-Nov-2021.) $)
      uspgrsprfo $p |- ( V e. W -> F : G -onto-> P ) $=
        ( va vb wcel cv cfv wceq wa cvv vp vf wrex wral wfo uspgrsprf c2nd cspr
        wf a1i wss wi cpw eleq2i velpw bitri cop cvtx cedg cuspgr eqidd cid cdm
        cres chash c2 cle wbr csn cdif crab wf1 wf1o wex vex f1oi dmresi f1oeq2
        c0 ax-mp sylibr sprvalpwle2 sseq2d biimpac jca weq f1oeq3 sseq1 anbi12d
        spcedv resiexg f11o resiexd anim1ci isuspgrop syl mpbird fveqeq2 adantl
        wb sylan2 crn edgopval rnresi eqtrdi ancoms rspcedvd copab eqeq1 adantr
        opvtxfv eqeq2 rexbidv opelopabga bitrid fveq2 eqeq2d op2ndg elvd eqcomd
        bi2anan9 ex sylbi impcom uspgrsprfv rexbidva ralrimiva dffo3 sylanbrc )
        GHOZFBEUIZMPZNPZEQZRZNFUCZMBUDFBEUEYKYJABCDEFGIJKLUFUJYJYPMBYJYLBOZSZYP
        YLYMUGQZRZNFUCZYQYJUUAYQYLGUHQZUKZYJUUAULYQYLUUBUMZOUUCBUUDYLJUNMUUBUOU
        PUUCYJUUAUUCYJSZYTYLGYLUQZUGQZRZNUUFFUUEUUFFOZGGRZIPZURQZGRZUUKUSQZYLRZ
        SZIUTUCZSZUUEUUJUUQUUEGVAUUEUUPGVBYLVDZUQZURQGRZUUTUSQZYLRZSZIUUTUTUUEU
        UTUTOZUUSVCZUAPVEQVFVGVHUAGUMVSVIVJVKZUUSVLZUUEUVFUBPZUUSVMZUVIUVGUKZSZ
        UBVNUVHUUEUVLUVFYLUUSVMZYLUVGUKZSUBTYLYLTOZUUEMVOZUJUUEUVMUVNUUEYLYLUUS
        VMZUVMUVQUUEYLVPUJUVFYLRUVMUVQWTYLVQUVFYLYLUUSVRVTWAYJUUCUVNYJUUBUVGYLG
        HUAWBWCWDWEUBMWFUVJUVMUVKUVNUVIYLUVFUUSWGUVIYLUVGWHWIWJUBUVFUVGUUSUVOUU
        STOZUVPYLTWKVTWLWAUUEYJUVRSUVEUVHWTUUCUVRYJUUCYLTUVOUUCUVPUJZWMZWNUUSGH
        TUAWOWPWQUUKUUTRZUUPUVDWTUUEUWAUUMUVAUUOUVCUUKUUTGURWRUUKUUTYLUSWRWIWSY
        JUUCUVDYJUUCSZUVAUVCUUCYJUVRUVAUVTUUSGHTXKXAUWBUVBUUSXBZYLUUCYJUVRUVBUW
        CRUVTUUSGHTXCXAYLXDXEWEXFXGWEUUIUUFAPZGRZUULUWDRZUUNCPZRZSZIUTUCZSZACXH
        ZOZUUEUURFUWLUUFKUNUUEYJUVOSUWMUURWTUUCUVOYJUVSWNUWKUURACGYLHTUWECMWFZS
        ZUWEUUJUWJUUQUWEUWEUUJWTUWNUWDGGXIXJUWOUWIUUPIUTUWEUWFUUMUWNUWHUUOUWDGU
        ULXLUWGYLUUNXLYAXMWIXNWPXOWQYMUUFRZYTUUHWTUUEUWPYSUUGYLYMUUFUGXPXQWSUUE
        UUGYLYJUUGYLRZUUCYJUWQMGYLHTXRXSWSXTXGYBYCYDYRYOYTNFYRYMFOZSYNYSYLUWRYN
        YSRYRABCDEFGYMIJKLYEWSXQYFWQYGNMFBEYHYI $.

      $( The mapping ` F ` is a bijection between the "simple pseudographs"
         with a fixed set of vertices ` V ` and the subsets of the set of pairs
         over the set ` V ` .  See also the comments on ~ uspgrbisymrel .
         (Contributed by AV, 25-Nov-2021.) $)
      uspgrsprf1o $p |- ( V e. W -> F : G -1-1-onto-> P ) $=
        ( wcel wf1 wfo wf1o uspgrsprf1 a1i uspgrsprfo df-f1o sylanbrc ) GHMZFBE
        NZFBEOFBEPUCUBABCDEFGIJKLQRABCDEFGHIJKLSFBETUA $.
    $}

    $d P e g v $.  $d W q $.
    $( The class ` G ` of all "simple pseudographs" with a fixed set of
       vertices ` V ` is a set.  (Contributed by AV, 26-Nov-2021.) $)
    uspgrex $p |- ( V e. W -> G e. _V ) $=
      ( vg wcel cvv cspr cfv cpw fvex pwex eqeltri cv c2nd cmpt wf1o eqid f1ovv
      wb uspgrsprf1o syl mpbiri ) EFKZDLKZBLKZBEMNZOLHULEMPQRUIDBJDJSTNUAZUBUJU
      KUEABCJUMDEFGHIUMUCUFDBUMUDUGUH $.

    $d G f $.  $d P f g $.
    $( There is a bijection between the "simple pseudographs" with a fixed set
       of vertices ` V ` and the subsets of the set of pairs over the set
       ` V ` .  (Contributed by AV, 26-Nov-2021.) $)
    uspgrbispr $p |- ( V e. W -> E. f f : G -1-1-onto-> P ) $=
      ( vg wcel cv wf1o c2nd cfv cmpt cvv uspgrex mptexd uspgrsprf1o f1oeq1
      eqid spcedv ) FGLZEBDMZNEBKEKMOPZQZNDRUHUEKEUGRABCEFGHIJSTABCKUHEFGHIJUHU
      CUAEBUFUHUBUD $.

    $( The set ` G ` of the "simple pseudographs" with a fixed set of vertices
       ` V ` and the class ` P ` of subsets of the set of pairs over the fixed
       set ` V ` are equinumerous.  (Contributed by AV, 27-Nov-2021.) $)
    uspgrspren $p |- ( V e. W -> G ~~ P ) $=
      ( vf wcel cv wf1o wex cen wbr uspgrbispr bren sylibr ) EFKDBJLMJNDBOPABCJ
      DEFGHIQDBJRS $.
  $}

  ${
    $d V e q v $.  $d V r x y $.  $d W e q v $.  $d W x y $.
    uspgrbisymrel.g $e |- G = { <. v , e >. | ( v = V /\ E. q e. USPGraph
                                  ( ( Vtx ` q ) = v /\ ( Edg ` q ) = e ) ) } $.
    uspgrbisymrel.r $e |- R = { r e. ~P ( V X. V ) |
                                   A. x e. V A. y e. V ( x r y <-> y r x ) } $.
    $( The set ` G ` of the "simple pseudographs" with a fixed set of vertices
       ` V ` and the class ` R ` of the symmetric relations on the fixed set
       ` V ` are equinumerous.  For more details about the class ` G ` of all
       "simple pseudographs" see comments on ~ uspgrbisymrel .  (Contributed by
       AV, 27-Nov-2021.) $)
    uspgrymrelen $p |- ( V e. W -> G ~~ R ) $=
      ( wcel cspr cfv cpw cen wbr eqid uspgrspren sprsymrelen entr syl2anc ) GH
      MFGNOPZQRUDDQRFDQRCUDEFGHJUDSZKTABUDDGHIUELUAFUDDUBUC $.

    $d G f g $.  $d R f p $.  $d V g $.  $d V p r x y $.
    $( There is a bijection between the "simple pseudographs" for a fixed set
       ` V ` of vertices and the class ` R ` of the symmetric relations on the
       fixed set ` V ` .  The simple pseudographs, which are graphs without
       hyper- or multiedges, but which may contain loops, are expressed as
       ordered pairs of the vertices and the edges (as proper or improper
       unordered pairs of vertices, not as indexed edges!) in this theorem.
       That class ` G ` of such simple pseudographs is a set (if ` V ` is a
       set, see ~ uspgrex ) of equivalence classes of graphs abstracting from
       the index sets of their edge functions.

       Solely for this abstraction, there is a bijection between the "simple
       pseudographs" as members of ` G ` and the symmetric relations ` R ` on
       the fixed set ` V ` of vertices.  This theorem would not hold for
       ` G = { g e. USPGraph | ( Vtx `` g ) = V } ` and even not for
       ` G = { <. v , e >. | ( v = V /\ <. v , e >. e. USPGraph ) } ` , because
       these are much bigger classes.  (Proposed by Gerard Lang, 16-Nov-2021.)
       (Contributed by AV, 27-Nov-2021.) $)
    uspgrbisymrel $p |- ( V e. W -> E. f f : G -1-1-onto-> R ) $=
      ( wcel cen wbr cv wf1o wex uspgrymrelen bren sylib ) HINGDOPGDFQRFSABCDEG
      HIJKLMTGDFUAUB $.

    $d V c f p r x y $.  $d W c $.  $d e g v $.
    $( Alternate proof of ~ uspgrbisymrel not using the definition of
       equinumerosity.  (Contributed by AV, 26-Nov-2021.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    uspgrbisymrelALT $p |- ( V e. W -> E. f f : G -1-1-onto-> R ) $=
      ( vp vc vg wcel cv cvv wf1o cspr cfv cpw cpr wceq wrex cmpt c2nd ccom wex
      copab fvex pwex mptexg mp1i eqid uspgrex syl2anc sprsymrelf1o uspgrsprf1o
      syl coexg f1oco f1oeq1 spcegv sylc ) HIQZNHUAUBZUCZORARBRUDUEONRUFABUKZUG
      ZPGPRUHUBZUGZUIZSQZGDVNTZGDFRZTZFUJVGVKSQZVMSQZVOVISQVSVGVHHUAULUMNVIVJSU
      NUOVGGSQVTCVIEGHIKVIUPZLUQPGVLSUNVAVKVMSSVBURVGVIDVKTGVIVMTVPABVIDVKHIJNO
      WAMVKUPUSCVIEPVMGHIKWALVMUPUTGVIDVKVMVCURVRVPFVNSGDVQVNVDVEVF $.
  $}
