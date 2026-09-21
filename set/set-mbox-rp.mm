$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Richard Penner
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Set Theory and Ordinal Numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x y z $.  $d B x $.
    $( Two ways to say a union is an element of a class.  (Contributed by RP,
       27-Jan-2025.) $)
    uniel $p |- ( U. A e. B <->
                  E. x e. B A. z ( z e. x <-> E. y e. A z e. y ) ) $=
      ( wel wrex cab wcel cv wb wal wa cuni clabel dfuni2 eleq1i df-rex 3bitr4i
      wex ) CBFBDGZCHZEIAJEICAFUAKCLZMATDNZEIUCAEGUACAEOUDUBECBDPQUCAERS $.
  $}

  ${
    $d A x y z $.  $d B x y z $.
    $( Two ways to say the union of a class is an element of a subclass.
       (Contributed by RP, 29-Jan-2025.) $)
    unielss $p |- ( A C_ B -> ( U. B e. A <-> E. x e. A A. y e. B y C_ x ) ) $=
      ( vz wss cuni wcel wel wrex wb wal cv wral wi wa df-ral bitri nfv adantl
      uniel df-ss ralbii 19.21v albii alcom 3bitr2i ssel2 pm2.27 elequ2 imbi12d
      weq imbi1d rspcev syl2an r19.35 imbi1i sylib impancom nfa1 nfan sp impbid
      rexlimd rspe ex ax-gen nfre1 nfbi imbi2 imbi2d albid mpbiri albidv bitrid
      impbida rexbidva bitr4id ) CDFZDGCHEAIZEBIZBDJZKZELZACJBMZAMZFZBDNZACJABE
      DCUAVSWHWDACWHWEDHZWAVTOZOZBLZELZVSWFCHPZWDWHWJELZBDNZWMWGWOBDEWEWFUBUCWP
      WIWOOZBLWKELZBLWMWOBDQWRWQBWIWJEUDUEWKBEUFUGRWNWLWCEWNWLWCWNWLPZVTWBWNVTW
      LWBWNVTPWJWAOZBDJZWLWBOZWNWFDHVTVTOZVTOZXAVTCDWFUHVTVTUIWTXDBWFDBAULZWJXC
      WAVTXEWAVTVTBAEUJZUMXFUKUNUOXAWJBDNZWBOXBWJWABDUPXGWLWBWJBDQUQRURUSWSWAVT
      BDWNWLBWNBSWKBUTVAVTBSZWLWKWNWKBVBTVDVCWNWCPWLWIWAWBOZOZBLZXJBWIWAWBWABDV
      EVFVGWCWLXKKWNWCWKXJBVTWBBXHWABDVHVIWCWJXIWIVTWBWAVJVKVLTVMVPVNVOVQVR $.
  $}

  ${
    $d A x y $.
    $( Two ways to say the union of a class is an element of that class.
       (Contributed by RP, 27-Jan-2025.) $)
    unielid $p |- ( U. A e. A <-> E. x e. A A. y e. A y C_ x ) $=
      ( wss cuni wcel cv wral wrex wb ssid unielss ax-mp ) CCDCECFBGAGDBCHACIJC
      KABCCLM $.
  $}

  ${
    $d A x $.  $d B x y $.
    $( Two ways to say a class is a subclass of a union.  (Contributed by RP,
       27-Jan-2025.) $)
    ssunib $p |- ( A C_ U. B <-> A. x e. A E. y e. B x e. y ) $=
      ( cuni wss cv wcel wral wel wrex dfss3 eluni2 ralbii bitri ) CDEZFAGZPHZA
      CIABJBDKZACIACPLRSACBQDMNO $.
  $}

  ${
    $d A x $.  $d A y $.  $d B x $.  $d B y $.
    $( Equality theorem for supremum of sets of ordinals.  (Contributed by RP,
       23-Jan-2025.) $)
    rp-intrabeq $p |- ( A = B -> |^| { x e. On | A. y e. A y C_ x }
                  = |^| { x e. On | A. y e. B y C_ x } ) $=
      ( wceq cv wss wral con0 crab raleq rabbidv inteqd ) CDEZBFAFGZBCHZAIJOBDH
      ZAIJNPQAIOBCDKLM $.
  $}

  ${
    $d A x $.  $d A y $.  $d B x $.  $d B y $.
    $( Equality theorem for infimum of non-empty classes of ordinals.
       (Contributed by RP, 23-Jan-2025.) $)
    rp-unirabeq $p |- ( A = B -> U. { x e. On | A. y e. A x C_ y }
                  = U. { x e. On | A. y e. B x C_ y } ) $=
      ( wceq cv wss wral con0 crab raleq rabbidv unieqd ) CDEZAFBFGZBCHZAIJOBDH
      ZAIJNPQAIOBCDKLM $.
  $}

  ${
    $d A x y $.
    $( Two ways to say the maximum element of a class of ordinals is also the
       supremum of that class.  (Contributed by RP, 27-Jan-2025.) $)
    onmaxnelsup $p |- ( A C_ On -> ( -. A C_ U. A <->
                              E. x e. A A. y e. A y C_ x ) ) $=
      ( con0 wss cuni wel wral wrex rexnal ralnex rexbii ssunib notbii 3bitr4ri
      wn cv wcel wa wb sselda adantr ontri1 syl2anc ralbidva rexbidva bitr4id
      simpl ssel2 ) CDEZCCFEZPZABGZPZBCHZACIZBQZAQZEZBCHZACIUMBCIZPZACIVAACHZPU
      PULVAACJUOVBACUMBCKLUKVCABCCMNOUJUTUOACUJURCRZSZUSUNBCVEUQCRZSUQDRURDRZUS
      UNTVECDUQUJVDUHUAVEVGVFCDURUIUBUQURUCUDUEUFUG $.
  $}

  $( The supremum of a set of ordinals exists.  See ~ uniexg . $)

  $( If the supremum of a class of ordinals is not in that class, then the
     supremum is a limit ordinal or empty.  (Contributed by RP,
     27-Jan-2025.) $)
  onsupneqmaxlim0 $p |- ( A C_ On -> ( A C_ U. A -> U. A = U. U. A ) ) $=
    ( cuni wss con0 wceq uniss word ssorduni orduniss syl biantrud eqss bitr4di
    wa imbitrid ) AABZCPPBZCZADCZPQEZAPFSRRQPCZNTSUARSPGUAAHPIJKPQLMO $.

  $( The supremum of a set of ordinals is an ordinal.  See ~ ssonuni . $)

  $( The supremum of a set of ordinals is an ordinal.  (Contributed by RP,
     23-Jan-2025.) $)
  onsupcl2 $p |- ( A e. ~P On -> U. A e. On ) $=
    ( con0 cpw wcel cvv wss wa cuni elpwb ssonuni imp sylbi ) ABCDAEDZABFZGAHBD
    ZABIMNOAEJKL $.

  ${
    $d A x y $.
    $( The union of a set of ordinals is the intersection of every ordinal
       greater-than-or-equal to every member of the set.  Closed form of
       ~ uniordint .  (Contributed by RP, 28-Jan-2025.) $)
    onuniintrab $p |- ( ( A C_ On /\ A e. V ) ->
                        U. A = |^| { x e. On | A. y e. A y C_ x } ) $=
      ( con0 wcel wa cuni cv wral crab cint ssonuni impcom intmin unissb rabbii
      wss wceq inteqi eqtr3di syl ) CERZCDFZGCHZEFZUEBIAIZRBCJZAEKZLZSUDUCUFCDM
      NUFUEUGRZAEKZLUEUJAUEEOULUIUKUHAEBCUGPQTUAUB $.
  $}

  $( The infimum of a non-empty class of ordinals is an ordinal.  See
     ~ oninton . $)

  ${
    $d A x y $.
    $( The intersection of a non-empty class of ordinals is the union of every
       ordinal less-than-or-equal to every element of that class.  (Contributed
       by RP, 29-Jan-2025.) $)
    onintunirab $p |- ( ( A C_ On /\ A =/= (/) ) -> |^| A =
                     U. { x e. On | A. y e. A x C_ y } ) $=
      ( con0 wss c0 wne wa cv wral crab cuni cint wcel wceq csuc w3a wb syl2anc
      a1i simp3 ssint sylibr simp2 oninton 3ad2ant1 onsssuc rabssdv word ssrab2
      mpbid eloni ordunisssuc mpbird sseq1 ralbidv intss1 elrabd unissel eqcomd
      syl rgen ) CDECFGHZAIZBIZEZBCJZADKZLZCMZVCVIVJEZVJVHNVIVJOVCVKVHVJPZEZVCV
      GADVLVCVDDNZVGQZVDVJEZVDVLNZVOVGVPVCVNVGUABVDCUBUCVOVNVJDNZVPVQRVCVNVGUDV
      CVNVRVGCUEZUFVDVJUGSUKUHVCVHDEZVJUIZVKVMRVTVCVGADUJTVCVRWAVSVJULVAVHVJUMS
      UNVCVGVJVEEZBCJZAVJDVDVJOVFWBBCVDVJVEUOUPVSWCVCWBBCVECUQVBTURVHVJUSSUT $.
  $}

  ${
    $d A x y $.
    $( If the union of a class of ordinals is not the maximum element of that
       class, then the union is a limit ordinal or empty.  But this isn't a
       biconditional since ` A ` could be a non-empty set where a limit ordinal
       or the empty set happens to be the largest element.  (Contributed by RP,
       27-Jan-2025.) $)
    onsupnmax $p |- ( A C_ On -> ( -. U. A e. A -> U. A = U. U. A ) ) $=
      ( vy vx con0 wss cuni wcel wn wceq wi wa cv wral wel rexnal sselda adantr
      wrex wb a1i ralnex rexbii ssunib notbii 3bitr4ri simpll ralbidva rexbidva
      simpl ontri1 syl2anc bitr4id unielid biimprd sylbid con1d uniss syl6 word
      ssorduni orduniss syl biantrud eqss bitr4di sylibd ex unon unieq 3eqtr4rd
      id a1i13 wo ordeleqon sylib mpjaod ) ADEZAFZDGZVRAGZHZVRVRFZIZJZVRDIZVQVS
      WDVQVSKZWAVRWBEZWCWFWAAVREZWGWFWHVTWFWHHZBLZCLZEZBAMZCARZVTWFWICBNZHZBAMZ
      CARZWNWOBARZHZCARWSCAMZHWRWIWSCAOWQWTCAWOBAUAUBWHXACBAAUCUDUEWFWMWQCAWFWK
      AGZKZWLWPBAXCWJAGZKWJDGWKDGZWLWPSXCADWJVQVSXBUFPXCXEXDWFADWKVQVSUIPQWJWKU
      JUKUGUHULWFVTWNVTWNSWFCBAUMTUNUOUPAVRUQURVQWGWCSVSVQWGWGWBVREZKWCVQXFWGVQ
      VRUSZXFAUTZVRVAVBVCVRWBVDVEQVFVGVQWEWAWCWEDFZDWBVRXIDIWEVHTVRDVIWEVKVJVLV
      QXGVSWEVMXHVRVNVOVP $.

  $}

  ${
    $d A x y $.  $d V y $.
    $( The supremum of a set of ordinals is the union of that set.  Lemma 2.10
       of [Schloeder] p. 5.  (Contributed by RP, 19-Jan-2025.) $)
    onsupuni $p |- ( ( A C_ On /\ A e. V ) -> sup ( A , On , _E ) = U. A ) $=
      ( vy vx con0 wss wcel wa cuni cv cep wbr wn wral wrex wi csup adantr epel
      wb wceq ssonuni impcom elssuni simpl sselda ontri1 syl2anc notbii bitr4di
      rgen ralbidva mpbii epelg syl biimpd wel eluni2 rexbii imbitrdi ralrimiva
      bitr4i wwe wor epweon weso mp1i eqsup mp3and ) AEFZABGZHZAIZEGZVMCJZKLZMZ
      CANZVOVMKLZVODJKLZDAOZPZCENAEKQVMUAVKVJVNABUBUCZVLVOVMFZCANVRWDCAVOAUDUKV
      LWDVQCAVLVOAGZHZWDVMVOGZMZVQWFVOEGZVNWDWHTVLAEVOVJVKUEUFVLVNWEWCRVOVMUGUH
      VPWGCVMSUIUJULUMVLWBCEVLWIHZVSVOVMGZWAWJVSWKWJVNVSWKTVLVNWIWCRVOVMEUNUOUP
      WKCDUQZDAOWADVOAURVTWLDADVOSUSVBUTVAVLCDEAVMKEKVCEKVDVLVEEKVFVGVHVI $.
  $}

  $( The supremum of a set of ordinals is the union of that set.  (Contributed
     by RP, 22-Jan-2025.) $)
  onsupuni2 $p |- ( A e. ~P On -> sup ( A , On , _E ) = U. A ) $=
    ( con0 cpw wcel cvv wss wa cep csup cuni wceq elpwb onsupuni ancoms sylbi )
    ABCDAEDZABFZGABHIAJKZABLQPRAEMNO $.

  ${
    $d A x y $.  $d V x $.
    $( The supremum of a set of ordinals is the intersection of every ordinal
       greater-than-or-equal to every member of the set.  Definition 2.9 of
       [Schloeder] p. 5.  (Contributed by RP, 23-Jan-2025.) $)
    onsupintrab $p |- ( ( A C_ On /\ A e. V ) -> sup ( A , On , _E ) =
                  |^| { x e. On | A. y e. A y C_ x } ) $=
      ( con0 wss wcel wa csup cuni cv wral crab cint onsupuni onuniintrab eqtrd
      cep ) CEFCDGHCERICJBKAKFBCLAEMNCDOABCDPQ $.
  $}

  ${
    $d A x y $.
    $( The supremum of a set of ordinals is the intersection of every ordinal
       greater-than-or-equal to every member of the set.  (Contributed by RP,
       23-Jan-2025.) $)
    onsupintrab2 $p |- ( A e. ~P On -> sup ( A , On , _E ) =
                  |^| { x e. On | A. y e. A y C_ x } ) $=
      ( con0 cpw wcel cvv wss wa cep csup wral crab cint wceq elpwb onsupintrab
      cv ancoms sylbi ) CDEFCGFZCDHZICDJKBRARHBCLADMNOZCDPUBUAUCABCGQST $.
  $}

  ${
    $d A x y $.  $d V x $.
    $( The supremum of a set of ordinals is an ordinal.  (Contributed by RP,
       23-Jan-2025.) $)
    onsupcl3 $p |- ( ( A C_ On /\ A e. V ) ->
                  |^| { x e. On | A. y e. A y C_ x } e. On ) $=
      ( con0 wcel wa cuni cv wral crab cint onuniintrab ssonuni impcom eqeltrrd
      wss ) CEQZCDFZGCHZBIAIQBCJAEKLEABCDMSRTEFCDNOP $.
  $}

  ${
    $d A x y $.  $d V x $.
    $( The supremum of a set of ordinals exists.  (Contributed by RP,
       23-Jan-2025.) $)
    onsupex3 $p |- ( ( A C_ On /\ A e. V ) ->
                  |^| { x e. On | A. y e. A y C_ x } e. _V ) $=
      ( con0 wss wcel wa cv wral crab cint onsupcl3 elexd ) CEFCDGHBIAIFBCJAEKL
      EABCDMN $.
  $}

  ${
    $d A x y $.
    $( The union of a set of ordinals is the intersection of every ordinal
       greater-than-or-equal to every member of the set.  (Contributed by RP,
       23-Jan-2025.) $)
    onuniintrab2 $p |- ( A e. ~P On ->
                        U. A = |^| { x e. On | A. y e. A y C_ x } ) $=
      ( con0 cpw wcel cvv wss wa cuni cv wral crab cint wceq onuniintrab ancoms
      elpwb sylbi ) CDEFCGFZCDHZICJBKAKHBCLADMNOZCDRUATUBABCGPQS $.
  $}

  ${
    $d A x $.
    $( The infimum of a non-empty class of ordinals is the intersection of that
       class.  (Contributed by RP, 23-Jan-2025.) $)
    oninfint $p |- ( ( A C_ On /\ A =/= (/) ) -> inf ( A , On , _E ) =
                   |^| A ) $=
      ( vx con0 wss c0 wne cint cep wwe wor epweon weso mp1i oninton onint wcel
      wa cv wbr wb intss1 adantl simpl sselda ontri1 syl2an2r syl adantr mtbird
      wn mpbid epelg infmin ) ACDZAEFZQZBCAAGZHCHICHJUPKCHLMANZAOUPBRZAPZQZUSUQ
      HSZUSUQPZVAUQUSDZVCUJZUTVDUPUSAUAUBUPUQCPZUTUSCPVDVETURUPACUSUNUOUCUDUQUS
      UEUFUKUPVBVCTZUTUPVFVGURUSUQCULUGUHUIUM $.
  $}

  ${
    $d A x y $.
    $( The infimum of a non-empty class of ordinals is the union of every
       ordinal less-than-or-equal to every element of that class.  (Contributed
       by RP, 23-Jan-2025.) $)
    oninfunirab $p |- ( ( A C_ On /\ A =/= (/) ) -> inf ( A , On , _E ) =
                        U. { x e. On | A. y e. A x C_ y } ) $=
      ( con0 wss c0 wne wa cep cinf cint cv wral crab cuni oninfint onintunirab
      eqtrd ) CDECFGHCDIJCKALBLEBCMADNOCPABCQR $.
  $}

  ${
    $d A x y $.
    $( The infimum of a non-empty class of ordinals is an ordinal.
       (Contributed by RP, 23-Jan-2025.) $)
    oninfcl2 $p |- ( ( A C_ On /\ A =/= (/) ) ->
                        U. { x e. On | A. y e. A x C_ y } e. On ) $=
      ( con0 wss c0 wne wa cint cv wral crab cuni onintunirab oninton eqeltrrd
      ) CDECFGHCIAJBJEBCKADLMDABCNCOP $.
  $}

  ${
    $d A x y z $.
    $( The union of a class of ordinals is an element is an element of that
       class if and only if there is a maximum element of that class under the
       epsilon relation, which is to say that the domain of the restricted
       epsilon relation is not the whole class.  (Contributed by RP,
       25-Jan-2025.) $)
    onsupmaxb $p |- ( A C_ On -> ( dom ( _E i^i ( A X. A ) ) = A
                                   <-> -. U. A e. A ) ) $=
      ( vx vy vz con0 wss wel wrex wral wn wb wex cep wceq wcel cv elequ1 bitri
      wa wal cxp cin cdm cuni elirrv pm5.501 mp1i notbid rexbidv bibi12d bitr4d
      weq biimpd spimevw wi ssel adantr imp ssel2 ontri1 ralbidva ralnex bitrdi
      syl2anc unissb simpr elssuni ad2antlr eqssd sylan2br dfuni2 eqeq1i eqabcb
      cab bicom albii 3bitri sylib notnotb bibi1i nbbn alnex ex sylbird impbid2
      con4d wbr dminxp rexbii ralbii exnal bicomi exbii bitr3i xchnxbir 3bitr4g
      epel uniel ) AEFZBCGZCAHZBAIZDBGZJZDCGZCAHZKZDLZBAIZMAAUAUBUCANZAUDZAOZJW
      SXAXHBAWSBPZAOZSZXAXHXAXGDBDBULZXAXGXPXABBGZJZXAKZXGXRXAXSKXPBUEXRXAUFUGX
      PXDXRXFXAXPXCXQDBBQUHXPXEWTCADBCQUIUJUKUMUNXOXAXHXOXAJZCPZXMFZCAIZXHJZXOY
      CWTJZCAIXTXOYBYECAXOYAAOZSYAEOZXMEOZYBYEKXOYFYGWSYFYGUOXNAEYAUPUQURXOYHYF
      AEXMUSUQYAXMUTVDVAWTCAVBVCXOYCYDXOYCSZXCXFKZDTZYDYIXKXMNZYKYCXOXKXMFZYLCA
      XMVEXOYMSXKXMXOYMVFXNXMXKFWSYMXMAVGVHVIVJYLXFDVNZXMNXFXCKZDTYKXKYNXMDCAVK
      VLXFDXMVMYOYJDXFXCVOVPVQVRYKXGJZDTYDYJYPDYJXDJZXFKYPXCYQXFXCVSVTXDXFWARVP
      XGDWBRVRWCWDWFWEVAXJXMYAMWGZCAHZBAIXBBCAAMWHYSXABAYRWTCACXMWQWIWJRYKBAHZX
      IXLYTJYKJZBAIXIYKBAVBUUAXHBAUUAYJJZDLXHYJDWKUUBXGDXGUUBXCXFWAWLWMWNWJWNBC
      DAAWRWOWP $.
  $}

$( Unordered past here $)

  ${
    $d A x $.
    $( For any ordinal, there is always a larger ordinal.  (Contributed by RP,
       1-Feb-2025.) $)
    onexgt $p |- ( A e. On -> E. x e. On A e. x ) $=
      ( con0 wcel csuc cv wrex onsuc sucidg eleq2 rspcev syl2anc ) BCDBEZCDBMDZ
      BAFZDZACGBHBCIPNAMCOMBJKL $.
  $}

  ${
    $d A x a b c $.
    $( For any ordinal, there is always a larger product of omega.
       (Contributed by RP, 1-Feb-2025.) $)
    onexomgt $p |- ( A e. On -> E. x e. On A e. ( _om .o x ) ) $=
      ( vc va vb con0 wcel cv wceq com comu co coa wa wrex c0 omelon wi sylancr
      adantr cop weu peano1 ne0ii omeu mp3an13 euex csuc onsuc simpr simpl omcl
      wne wex oaordi mpd omsuc eleqtrrd eqeltrrd eleq2d rspcev syl2an2r adantld
      oveq2 ex a1i rexlimdvv exlimdv syl5 ) BFGZCHDHZEHZUAIZJVKKLZVLMLZBIZNZEJO
      DFOZCUBZBJAHZKLZGZAFOZJFGZVJJPUMVSQPJUCUDDECJBUEUFVSVRCUNVJWCVRCUGVJVRWCC
      VJVQWCDEFJVKFGZVLJGZNZVQWCRRVJWGVPWCVMWGVPWCWGVKUHZFGZVPBJWHKLZGZWCWEWIWF
      VKUITWGVPNVOBWJWGVPUJWGVOWJGVPWGVOVNJMLZWJWGWFVOWLGZWEWFUJWGWDVNFGZWFWMRQ
      WGWDWEWNQWEWFUKZJVKULSVLJVNUOSUPWGWDWEWJWLIQWOJVKUQSURTUSWBWKAWHFVTWHIWAW
      JBVTWHJKVDUTVAVBVEVCVFVGVHVIUP $.
  $}

  $( The product of a limit ordinal with any nonzero ordinal is a limit
     ordinal.  (Contributed by RP, 8-Jan-2025.) $)
  omlimcl2 $p |- ( ( ( A e. On /\ ( B e. C /\ Lim B ) ) /\ (/) e. A )
                   -> Lim ( B .o A ) ) $=
    ( con0 wcel wlim wa c0 cuni wceq comu co csuc word ad2antrr adantl ad3antlr
    ex syl simpr wne ne0i id w3a df-lim biimpri syl2an3an limelon simpll anim1i
    eloni 0ellim omlimcl syl21anc syld coa onuni anim12ci jca oalimcl wb oveq2d
    omcl omsuc eqtrd limeq mpbird wo orduniorsuc mpjaod ) ADEZBCEZBFZGZGZHAEZGZ
    AAIZJZBAKLZFZAVRMZJZVQVSAFZWAVQVSWDVQANZAHUAZVSVSWDVKWEVNVPAUKOZVPWFVOAHUBP
    VSUCWDWEWFVSUDAUEUFUGRVQWDWAVQWDGBDEZVKWDGHBEZWAVNWHVKVPWDBCUHZQVQVKWDVKVNV
    PUIUJVNWIVKVPWDVMWIVLBULPQBADUMUNRUOVQWCWAVQWCGZWABVRKLZBUPLZFZWKWLDEZVNGZW
    NVOWPVPWCVOWOVNVOWHVRDEZGZWOVKWQVNWHAUQWJURZBVRVCSVKVNTUSOWLBCUTSWKVTWMJWAW
    NVAWKVTBWBKLZWMWKAWBBKVQWCTVBWKWRWTWMJVOWRVPWCWSOBVRVDSVEVTWMVFSVGRVQWEVSWC
    VHWGAVISVJ $.

  ${
    $d A x a $.
    $( For any ordinal, there is always a larger limit ordinal.  (Contributed
       by RP, 1-Feb-2025.) $)
    onexlimgt $p |- ( A e. On -> E. x e. On ( Lim x /\ A e. x ) ) $=
      ( va con0 wcel com cun cv comu co wrex wlim wa omelon syl c0 wceq wi wn
      ex onun2 mpan2 onexomgt w3a simp2 omcl sylancr noel wb oveq2 ax-mp eqtrdi
      om0 eleq2d notbid adantl mpbiri pm2.21d com23 3impia limom jctir omlimcl2
      pm3.2i sylan wo on0eqel mpjaod wss simp1 jca simp3 ssun1 jctil ontr2 sylc
      limeq eleq2 anbi12d rspcev syl12anc rexlimdv3a mpd ) BDEZBFGZFCHZIJZEZCDK
      ZAHZLZBWJEZMZADKZWDWEDEZWIWDFDEZWONBFUAUBCWEUCOWDWHWNCDWDWFDEZWHUDZWGDEZW
      GLZBWGEZWNWRWPWQWSNWDWQWHUEZFWFUFUGZWRWFPQZWTPWFEZWDWQWHXDWTRWDWQMZXDWHWT
      XFXDWHWTRXFXDMZWHWTXGWHSZWEPEZSZWEUHXDXHXJUIXFXDWHXIXDWGPWEXDWGFPIJZPWFPF
      IUJWPXKPQNFUMUKULUNUOUPUQURTUSUTWRXEWTWRWQWPFLZMZMXEWTWRWQXMXBWPXLNVAVDVB
      WFFDVCVETWRWQXDXEVFXBWFVGOVHWRWDWSMBWEVIZWHMXAWRWDWSWDWQWHVJXCVKWRWHXNWDW
      QWHVLBFVMVNBWEWGVOVPWMWTXAMAWGDWJWGQWKWTWLXAWJWGVQWJWGBVRVSVTWAWBWC $.
  $}

  ${
    $d A x a b c d $.
    $( For any ordinal, there is always a larger power of omega.  (Contributed
       by RP, 1-Feb-2025.) $)
    onexoegt $p |- ( A e. On -> E. x e. On A e. ( _om ^o x ) ) $=
      ( vd va vb vc con0 wcel c0 wceq com cv coe co wrex wi c1o omelon a1i wa
      0elon 0lt1o oe0 ax-mp eleqtrri oveq2 eleq2d rspcev sylancr rexbidv mpbird
      eleq1 cotp comu coa cdif weu c2o 1onn ondif2 mpbir2an ondif1 biimpri oeeu
      wex euex w3a simpr csuc simp1 onsuc adantl oecl omcl syl2anc simp3 eldifi
      syl nnon 3ad2ant2 oaordi mpd omsuc eleqtrrd peano2 peano1 syl21anc omordi
      oen0 ontr1 imp syl12anc oesuc adantr eqeltrrd adantll syl2an2r syl5 3exp2
      ex imp4b rexlimdvv rexlimdva exlimdv on0eqel mpjaod ) BGHZBIJZBKALZMNZHZA
      GOZIBHZXHXLPXGXHXLIXJHZAGOZXHIGHIKIMNZHZXOUAXQXHIQXPUBKGHZXPQJRKUCUDUESXN
      XQAIGXIIJXJXPIXIIKMUFUGUHUIXHXKXNAGBIXJULUJUKSXGXMXLXGXMTZCLDLZELZFLZUMJZ
      KXTMNZYAUNNZYBUONZBJZTZFYDOEKQUPZOZDGOZCUQZXLXSKGURUPHZBGQUPHZYLYMXRQKHRU
      SKUTVAYNXSBVBVCDEFCKBVDUIYLYKCVEXSXLYKCVFXSYKXLCXSYJXLDGXSXTGHZTYHXLEFYIY
      DXSYOYAYIHZYBYDHZYHXLPZXSYOYPYQYRYHYGXSYOYPYQVGZTZXLYCYGVHYTYGXLYTXTVIZGH
      ZYGBKUUAMNZHZXLYSUUBXSYSYOUUBYOYPYQVJZXTVKVRVLYSYGUUDXSYSYGTYFBUUCYSYGVHY
      SYFUUCHYGYSYFYDKUNNZUUCYSUUFGHZYFYDYAVIZUNNZHZUUIUUFHZYFUUFHZYSYDGHZXRUUG
      YSXRYOUUMRUUEKXTVMUIZXRYSRSZYDKVNVOYSYFYEYDUONZUUIYSYQYFUUPHZYOYPYQVPYSUU
      MYEGHZYQUUQPUUNYSUUMYAGHZUURUUNYPYOUUSYQYPYAKHZUUSYAKQVQZYAVSVRVTZYDYAVNV
      OYBYDYEWAVOWBYSUUMUUSUUIUUPJUUNUVBYDYAWCVOWDYSUUHKHZUUKYSUUTUVCYPYOUUTYQU
      VAVTYAWEVRYSXRUUMIYDHZUVCUUKPUUOUUNYSXRYOIKHZUVDUUOUUEUVEYSWFSKXTWIWGUUHK
      YDWHWGWBUUGUUJUUKTUULYFUUIUUFWJWKWLYSXRYOUUCUUFJRUUEKXTWMUIWDWNWOWPXKUUDA
      UUAGXIUUAJXJUUCBXIUUAKMUFUGUHWQWTWRWSXAXBXCXDWRWBWTBXEXF $.
  $}

  $( The infimum of a non-empty class of ordinals exists.  See ~ intex . $)

  ${
    $d A x y $.
    $( The infimum of a non-empty class of ordinals exists.  (Contributed by
       RP, 23-Jan-2025.) $)
    oninfex2 $p |- ( ( A C_ On /\ A =/= (/) ) ->
                        U. { x e. On | A. y e. A x C_ y } e. _V ) $=
      ( con0 wss c0 wne wa cint cv wral crab cuni onintunirab wcel intex bilani
      cvv eqeltrrd ) CDEZCFGZHCIZAJBJEBCKADLMRABCNUAUBROTCPQS $.
  $}

  ${
    $d A x y $.  $d V x y $.
    $( Condition when the supremum of a set of ordinals is the maximum element
       of that set.  (Contributed by RP, 24-Jan-2025.) $)
    onsupeqmax $p |- ( ( A C_ On /\ A e. V ) -> ( E. x e. A A. y e. A y C_ x
                   <-> U. A e. A ) ) $=
      ( con0 wss wcel wa cuni cv wral wrex wb unielid a1i bicomd ) CEFCDGHZCICG
      ZBJAJFBCKACLZRSMQABCNOP $.
  $}

  ${
    $d A x y $.
    $( Condition when the supremum of a class of ordinals is not the maximum
       element of that class.  (Contributed by RP, 27-Jan-2025.) $)
    onsupeqnmax $p |- ( A C_ On -> ( A. x e. A E. y e. A x e. y
                   <-> ( U. A = U. U. A /\ -. U. A e. A ) ) ) $=
      ( con0 wss wrex wral cuni wcel wn wceq wa cv wb simpl sselda ssel2 adantr
      wel ontri1 syl2anc ralbidva rexbidva notbid bicomd dfrex2 unielid 3bitr4g
      ralbii ralnex bitri notbii onsupnmax pm4.71rd bitrd ) CDEZABSZBCFZACGZCHZ
      CIZJZUTUTHKZVBLUPUQJZBCGZACFZJZBMZAMZEZBCGZACFZJZUSVBUPVMVGUPVLVFUPVKVEAC
      UPVICIZLZVJVDBCVOVHCIZLVHDIVIDIZVJVDNVOCDVHUPVNOPVOVQVPCDVIQRVHVITUAUBUCU
      DUEUSVEJZACGVGURVRACUQBCUFUIVEACUJUKVAVLABCUGULUHUPVBVCCUMUNUO $.
  $}

  $( The infimum of a non-empty class of ordinals is the minimum element of
     that class.  See ~ onint. $)

  $( The supremum of a set of ordinals is an upper bound.  See ~ elssuni . $)

  ${
    $d A z $.  $d B z $.
    $( The supremum of a set of ordinals is the least upper bound.
       (Contributed by RP, 27-Jan-2025.) $)
    onsuplub $p |- ( ( ( A C_ On /\ A e. V ) /\ B e. On ) -> ( B e. U. A <->
                     E. z e. A B e. z ) ) $=
      ( cuni wcel cv wrex wb con0 wss wa eluni2 a1i ) CBEFCAGFABHIBJKBDFLCJFLAC
      BMN $.
  $}

  ${
    $d A z $.  $d B z $.
    $( An upper bound of a set of ordinals is not less than the supremum.
       (Contributed by RP, 27-Jan-2025.) $)
    onsupnub $p |- ( ( ( A C_ On /\ A e. V ) /\
                       ( B e. On /\ A. z e. A z C_ B ) ) -> U. A C_ B ) $=
      ( con0 wss wcel wa cv wral cuni simprr unissb sylibr ) BEFBDGHZCEGZAICFAB
      JZHHQBKCFOPQLABCMN $.
  $}

  $( Sufficient condition when the supremum of a set of ordinals is the maximum
     element of that set.  See ~ ordunifi .  (Contributed by RP,
     27-Jan-2025.) $)
  onfisupcl $p |- ( ( A C_ On /\ A e. V ) -> ( ( A e. Fin /\ A =/= (/) )
                   -> U. A e. A ) ) $=
    ( con0 wss wcel wa cfn c0 wne cuni w3a simpll simprl simprr ordunifi syl ex
    3jca ) ACDZABEZFZAGEZAHIZFZAJAEZUAUDFZSUBUCKUEUFSUBUCSTUDLUAUBUCMUAUBUCNRAO
    PQ $.

$( Julian J. Schl&ouml;der (2012). Ordinal Arithmetic. Tutorial notes on Set
   Theory, Bonn. ( ~ https://jjsch.github.io/output/oa.pdf )

  Definition 1.1  | ~ dftr5                | set.mm additionally allows
                                           | transitive classes
  Definition 1.2  | ~ dford3 , ~ elon2     | set.mm additionally allows
                  |                        | ordinal classes
  Lemma 1.3       | ~ ordelord , ~ ordelon | --
                  | ~ onelon , ~ onelord   |
  Definition 1.4  | ~ df-suc               | set.mm additionally
                  |                        | defines the successor
                  |                        | of arbitrary classes
  Remark 1.5      | ~ ord0 , ~ 0elon ,     | --
                  | ~ ordsuci , ~ onsuc    |
  Definition 1.6  | ~ epel , ~ epelg       | _E is relation, e. is syntax
  Lemma 1.7       | ~ sucidg , ~ onepsuc   | --
  Notation 1.8    | --                     | Greek wff, upper class, lower set
  Theorem 1.9     | ~ epsoon , ~ epirron , | linear order = strict order,
                  | ~ ordirr , ~ elirr ,   | thus "so"
                  | ~ oneptr , ~ oneltr ,  |
                  | ~ oneptri ,            |
                  | ~ oneltri , ~ ontr1 ,  |
                  | ~ ordtri3or ,          |
                  | ~ oneltri              |

  Lemma 1.10      | ~ ordne0gt0 , ~ ondif1i ,      | --
                  | ~ ord0eln0 , ~ ondif1          |
  Definition 1.11 | ~ dflim6 , ~ onsucelab ,       | --
                  | ~ limnsuc                      |
  Remark 1.12     | ~ ordzsl                       | --
  Lemma 1.13      | ~ elsuci , ~ trsucss           | --
  Lemma 1.14      | ~ ordsucss , ~ onsucss         | --
  Lemma 1.15      | ~ ordnbtwn , ~ onnbtwn ,       | --
  Lemma 1.16      | ~ ordnexbtwnsuc , ~ orddif0suc | --
  Lemma 1.17      | ~ onsucf1lem , ~ onsucf1olem , | fin1a2lem2 could be named
                  | ~ fin1a2lem2 , ~ onsucrn ,     | onsucf1 ?
                  | ~ onsucf1o                     |
  Lemma 1.18      | ~ dflim7                       | --
  Theorem 1.19    | ~ tfinds                       | --

  Definition 1.20 | ~ dfom3            | --
  Remark 1.21     | ~ omex             | --
  Theorem 1.22    | ~ ordom , ~ omelon | --
  Theorem 1.23    | ~ limom , ~ dfom5  | --

  Definition 2.1  | ~ df-1o , ~ df1o2               | --
  Lemma 2.2       | ~ 1onn                          | --
  Definition 2.3  | ~ oa0suclim , ~ oa0 , ~ oasuc , | --
                  | ~ oalim                         |
  Remark 2.4      | ~ oa1suc                        | --
  Definition 2.5  | ~ om0suclim , ~ om0 , ~ omsuc , | --
                  | ~ omlim                         |
  Definition 2.6  | ~ oe0suclim , ~ oe0 , ~ oesuc , | --
                  | ~ oe0m1 , ~ oelim               |
  Lemma 2.7       | ~ ssorduni , ~ ssonuni          | --
  Remark 2.8      | ~ oaomoecl , ~ oacl , ~ omcl ,  | --
                  | ~ oecl                          |
  Definition 2.9  | ~ onsupintrab                   | --
  Lemma 2.10      | ~ onsupuni                      | --
  Lemma 2.11      | ~ onsupsucismax                 | --
  Lemma 2.12      | ~ onsssupeqcond                 | --
  Lemma 2.13      | ~ limuni , ~ limexissup ,       | --
                  | ~ limiun , ~ limexissupab       |
  Lemma 2.14      | ~ oa0r                          | --
  Lemma 2.15      | ~ om1om1r , ~ om1 , ~ om1r      | --
  Lemma 2.16      | ~ oe1                           | --
  Lemma 2.17      | ~ oe1m                          | --
  Lemma 2.18      | ~ oe0rif                        | --
  Theorem 2.19    | ~ oasubex                       | --
  Theorem 2.20    | ~ nnamecl , ~ nnacl , ~ nnmcl , | --
                  | ~ nnecl

  Lemma 3.1    | ~ onsucwordi            | --
  Lemma 3.2    | ~ oaword1               | --
  Lemma 3.3    | ~ oaword2               | --
  Lemma 3.4    | ~ oalimcl               | --
  Lemma 3.5    | ~ oaltublim             | --
  Lemma 3.6    | ~ oaordi3               | --
  Theorem 3.7  | ~ oaord3                | --
  Lemma 3.8    | ~ 1oaomeqom             | --
  Remark 3.9   | ~ oaordnr , ~ oaordnrex | --
  Lemma 3.10   | ~ oa00                  | --
  Lemma 3.11   | ~ omge1 , ~ omword1     | Equivalent antecedents
  Lemma 3.12   | ~ omge2 , ~ omword2     | Equivalent antecedents
  Lemma 3.13   | ~ omlim2                | --
  Lemma 3.14   | ~ omord2lim             | --
  Lemma 3.15   | ~ omord2i , ~ omordi    | --
  Theorem 3.16 | ~ omord2com , ~ omord   | --
  Lemma 3.17   | ~ df-2o , ~ 2omomeqom   | --
  Remark 3.18  | ~ omnord1ex , ~ omnord1 | --
  Lemma 3.19   | ~ oege1 , ~ oewordi     | --
  Lemma 3.20   | ~ oege2 , ~ oeworde     | --
  Lemma 3.21   | ~ rp-oelim2             | --
  Lemma 3.22   | ~ oeord2lim             | --
  Lemma 3.23   | ~ oeord2i               | --
  Theorem 3.24 | ~ oeord2com             | --
  Lemma 3.25   | ~ nnoeomeqom            | --
  Remark 3.26  | ~ oenord1ex , ~ oenord1 | --

  Theorem 4.1  | ~ oaomoencom          | --
  Theorem 4.2  | ~ oaass               | --
  Theorem 4.3  | ~ odi                 | --
  Theorem 4.4  | ~ omass               | --
  Notation 4.5 | --                    | set.mm requires parenthesis
                                       | for all binary operators
                                       | per an early syntax choice
  Remark 4.6   | ~ oenass              | --
  Theorem 4.7  | ~ oeoa                | --

  Lemma 5.1   | ~ cantnftermord | --
  Lemma 5.2   | ~ cantnfub      | --
  Theorem 5.3 | ~ cantnf2       | --

  ~ dford3 is in the mathbox for Stefan O'Rear.

$)

  $( A set is called an ordinal iff it is transitive and every element is
     transitive.  See ~ elon2 . $)

  $( Every element of a ordinal is an ordinal.  Lemma 1.3 of [Schloeder] p. 1.
     Based on ~ onelon and ~ eloni .  (Contributed by RP, 15-Jan-2025.) $)
  onelord $p |- ( ( A e. On /\ B e. A ) -> Ord B ) $=
    ( con0 wcel wa word onelon eloni syl ) ACDBADEBCDBFABGBHI $.

  $( For ordinals, elementhood is equivalent to being less than.  See ~ epelg
     for a more general statement. $)

  $( Every ordinal is less than its successor.  See ~ sucidg for a more
     general statement. $)

  $( Every ordinal is less than its successor, relationship version.  Lemma 1.7
     of [Schloeder] p. 1.  (Contributed by RP, 15-Jan-2025.) $)
  onepsuc $p |- ( A e. On -> A _E suc A ) $=
    ( con0 wcel csuc cep wbr sucidg wb onsuc epelg syl mpbird ) ABCZAADZEFZANCZ
    ABGMNBCOPHAIANBJKL $.

  $( The ordinals are strictly and completely (linearly) ordered.  Theorem 1.9
     of [Schloeder] p. 1.  Based on ~ epweon and ~ weso .  (Contributed by RP,
     15-Jan-2025.) $)
  epsoon $p |- _E Or On $=
    ( con0 cep wwe wor epweon weso ax-mp ) ABCABDEABFG $.

  $( The strict order on the ordinals is irreflexive.  Theorem 1.9(i) of
     [Schloeder] p. 1.  (Contributed by RP, 15-Jan-2025.) $)
  epirron $p |- ( A e. On -> -. A _E A ) $=
    ( con0 cep wpo wcel wbr wn wwe wor epweon weso sopo mp2b poirr mpan ) BCDZA
    BEAACFGBCHBCIPJBCKBCLMBACNO $.

  $( The strict order on the ordinals is transitive.  Theorem 1.9(ii) of
     [Schloeder] p. 1.  (Contributed by RP, 15-Jan-2025.) $)
  oneptr $p |- ( ( A e. On /\ B e. On /\ C e. On )
                -> ( ( A _E B /\ B _E C )
                -> A _E C ) ) $=
    ( con0 cep wwe wor wcel w3a wbr wa wi epweon weso wpo sopo potr ex syl mp2b
    ) DEFDEGZADHBDHCDHIZABEJBCEJKACEJLZLZMDENUADEOZUDDEPUEUBUCDABCEQRST $.

  $( The elementhood relation on the ordinals is transitive.  Theorem 1.9(ii)
     of [Schloeder] p. 1.  See ~ ontr1 .  (Contributed by RP, 15-Jan-2025.) $)
  oneltr $p |- ( ( A e. On /\ B e. On /\ C e. On )
                -> ( ( A e. B /\ B e. C )
                -> A e. C ) ) $=
    ( con0 wcel wa wi ontr1 3ad2ant3 ) CDEADEABEBCEFACEGBDEABCHI $.

  $( The strict, complete (linear) order on the ordinals is complete.  Theorem
     1.9(iii) of [Schloeder] p. 1.  (Contributed by RP, 15-Jan-2025.) $)
  oneptri $p |- ( ( A e. On /\ B e. On )
                 -> ( A _E B \/ B _E A \/ A = B ) ) $=
    ( con0 wcel wa wceq cep wbr wo wn wb w3o wor epsoon sotrieq mpan wxo xorcom
    xoror df-xor xor3 3bitrri df-3or 3imtr4i syl ) ACDBCDEZABFZABGHZBAGHZIZJKZU
    HUIUGLZCGMUFUKNCABGOPUJUGQZUJUGIUKULUJUGSUMUGUJQUGUJKJUKUJUGRUGUJTUGUJUAUBU
    HUIUGUCUDUE $.

  $( Membership in the difference of ordinals.  (Contributed by RP,
     15-Jan-2025.) $)
  ordeldif $p |- ( ( Ord A /\ Ord B ) -> ( C e. ( A \ B )
                                        <-> ( C e. A /\ B C_ C ) ) ) $=
    ( cdif wcel wn wa word wss eldif wb simpr ordelord adantlr ordtri1 syl2an2r
    bicomd pm5.32da bitrid ) CABDECAEZCBEFZGAHZBHZGZTBCIZGCABJUDTUAUEUDTGUEUAUD
    UCTCHZUEUAKUBUCLUBTUFUCACMNBCOPQRS $.

  $( Membership in the difference of ordinal and successor ordinal.
     (Contributed by RP, 16-Jan-2025.) $)
  ordeldifsucon $p |- ( ( Ord A /\ B e. On ) -> ( C e. ( A \ suc B )
                                          <-> ( C e. A /\ B e. C ) ) ) $=
    ( csuc cdif wcel wn wa word con0 eldif wss simplr ordelord adantlr ordelsuc
    wb syl2anc eloni ordsuci 3syl ordtri1 bitr2d pm5.32da bitrid ) CABDZEFCAFZC
    UFFGZHAIZBJFZHZUGBCFZHCAUFKUKUGUHULUKUGHZULUFCLZUHUMUJCIZULUNQUIUJUGMZUIUGU
    OUJACNOZBCJPRUMUFIZUOUNUHQUMUJBIURUPBSBTUAUQUFCUBRUCUDUE $.

  $( Membership in the difference of ordinal and ordinal one.  (Contributed by
     RP, 16-Jan-2025.) $)
  ordeldif1o $p |- ( Ord A -> ( B e. ( A \ 1o )
                             <-> ( B e. A /\ B =/= (/) ) ) ) $=
    ( c1o cdif wcel c0 csuc wn wa word df-1o difeq2i eleq2i eldif bitri con0 wb
    wne 0elon sylancr wss ordelord ordelsuc ord0eln0 eloni ordsuci mp2b ordtri1
    syl 3bitr3rd pm5.32da bitrid ) BACDZEZBAEZBFGZEHZIZAJZUOBFRZIUNBAUPDZEURUMV
    ABCUPAKLMBAUPNOUSUOUQUTUSUOIZFBEZUPBUAZUTUQVBFPEZBJZVCVDQSABUBZFBPUCTVBVFVC
    UTQVGBUDUIVBUPJZVFVDUQQVEFJVHSFUEFUFUGVGUPBUHTUJUKUL $.

  $( Ordinal zero is less than every nonzero ordinal.  Theorem 1.10 of
     [Schloeder] p. 2.  Closely related to ~ ord0eln0 .  (Contributed by RP,
     16-Jan-2025.) $)
  ordne0gt0 $p |- ( ( Ord A /\ A =/= (/) ) -> (/) e. A ) $=
    ( word c0 wcel wne ord0eln0 biimpar ) ABCADACEAFG $.

  $( Ordinal zero is less than every nonzero ordinal, class difference version.
     Theorem 1.10 of [Schloeder] p. 2.  See ~ ondif1 .  (Contributed by RP,
     16-Jan-2025.) $)
  ondif1i $p |- ( A e. ( On \ 1o ) -> (/) e. A ) $=
    ( con0 c1o cdif wcel c0 ondif1 simprbi ) ABCDEABEFAEAGH $.

  ${
    $d A a b $.
    $( The successor of every ordinal is an element of the class of successor
       ordinals.  Definition 1.11 of [Schloeder] p. 2.  (Contributed by RP,
       16-Jan-2025.) $)
    onsucelab $p |- ( A e. On ->
                       suc A e. { a e. On | E. b e. On a = suc b } ) $=
      ( con0 wcel csuc cv wceq wrex crab onsuc eqid id wb eqeq2d adantl rspcedv
      suceq mpi eqeq1 rexbidv elrab sylanbrc ) ADEZAFZDEUECGZFZHZCDIZUEBGZUGHZC
      DIZBDJEAKUDUEUEHZUIUELUDUHUMCADUDMUFAHZUHUMNUDUNUGUEUEUFAROPQSULUIBUEDUJU
      EHUKUHCDUJUEUGTUAUBUC $.
  $}

  ${
    $d A b $.
    $( A limit ordinal is a nonzero ordinal which is not a successor ordinal.
       Definition 1.11 of [Schloeder] p. 2.  (Contributed by RP,
       16-Jan-2025.) $)
    dflim6 $p |- ( Lim A <->
                      ( Ord A /\ A =/= (/) /\ -. E. b e. On A = suc b ) ) $=
      ( word c0 wceq cv csuc con0 wrex wo wn wa wne wlim w3a ioran df-ne anbi1i
      bitr4i anbi2i dflim3 3anass 3bitr4i ) ACZADEZABFGEBHIZJKZLUDADMZUFKZLZLAN
      UDUHUIOUGUJUDUGUEKZUILUJUEUFPUHUKUIADQRSTBAUAUDUHUIUBUC $.
  $}

  ${
    $d A a b $.
    $( A limit ordinal is not an element of the class of successor ordinals.
       Definition 1.11 of [Schloeder] p. 2.  (Contributed by RP,
       16-Jan-2025.) $)
    limnsuc $p |- ( Lim A ->
                      -. A e. { a e. On | E. b e. On a = suc b } ) $=
      ( wlim word c0 wne cv csuc wceq con0 wrex wn crab wcel dflim6 simp3 eqeq1
      w3a rexbidv elrab simprbi nsyl sylbi ) ADAEZAFGZACHIZJZCKLZMZSZABHZUGJZCK
      LZBKNOZMACPUKUIUOUEUFUJQUOAKOUIUNUIBAKULAJUMUHCKULAUGRTUAUBUCUD $.
  $}

  $( If one ordinal is less than the successor of another, then the first is
     equal to or less than the second.  Use ~ elsuci or ~ trsucss . $)

  $( If one ordinal is less than another, then the successor of the first is
     less than or equal to the second.  Lemma 1.13 of [Schloeder] p. 2.  See
     ~ ordsucss .  (Contributed by RP, 16-Jan-2025.) $)
  onsucss $p |- ( A e. On -> ( B e. A -> suc B C_ A ) ) $=
    ( con0 wcel word csuc wss wi eloni ordsucss syl ) ACDAEBADBFAGHAIBAJK $.

  $( There is no ordinal between any ordinal and its successor.  See
     ~ ordnbtwn  and ~ onnbtwn . $)

  ${
    $d A c $.  $d B c $.
    $( For any distinct pair of ordinals, if there is no ordinal between the
       lesser and the greater, the greater is the successor of the lesser.
       Lemma 1.16 of [Schloeder] p. 2.  (Contributed by RP, 16-Jan-2025.) $)
    ordnexbtwnsuc $p |- ( ( A e. B /\ Ord B ) ->
                    ( A. c e. On -. ( A e. c /\ c e. B ) -> B = suc A ) ) $=
      ( word wcel cv wa wn con0 wral csuc wceq wi wrex ordelord ordnbtwn adantl
      wo syl wb pm2.21d expd com12 mpd sucidg ordelon onsuc eleq2 eleq1 anbi12d
      rspcedv mpand ralnex biimpi nsyli ordsuci ordtri3 syldan sylibrd ancoms
      jaod ) BDZABEZACFZEZVDBEZGZHCIJZBAKZLZMVBVCGZVHBVIEZVIBEZRZHZVJVKVNVGCINZ
      VHVKVLVPVMVKADZVLVPMZBAOZVCVQVRMVBVQVCVRVQVCVLVPVQVCVLGVPABPUAUBUCQUDVKAV
      IEZVMVPVCVTVBABUEQVKVGVTVMGZCVIIVKAIEVIIEBAUFAUGSVDVILZVGWATVKWBVEVTVFVMV
      DVIAUHVDVIBUIUJQUKULVAVHVPHVGCIUMUNUOVBVCVIDZVJVOTVKVQWCVSAUPSBVIUQURUSUT
      $.
  $}

  ${
    $d A c $.  $d B c $.
    $( For any distinct pair of ordinals, if the set difference between the
       greater and the successor of the lesser is empty, the greater is the
       successor of the lesser.  Lemma 1.16 of [Schloeder] p. 2.  (Contributed
       by RP, 17-Jan-2025.) $)
    orddif0suc $p |- ( ( A e. B /\ Ord B ) ->
                          ( ( B \ suc A ) = (/) -> B = suc A ) ) $=
      ( vc wcel word wa csuc cdif c0 wceq cv wn con0 wral wal wi ordelon ancoms
      wb simpr ordeldifsucon syl2anc biancomd ad2ant2l ex pm4.71rd df-an bitrdi
      bitr2d con1bid albidv eq0 df-ral 3bitr4g ordnexbtwnsuc sylbid ) ABDZBEZFZ
      BAGZHZIJZACKZDZVCBDZFZLZCMNZBUTJUSVCVADZLZCOVCMDZVGPZCOVBVHUSVJVLCUSVLVIU
      SVIVFVLLZUSVIVDVEUSURAMDZVIVEVDFSUQURTURUQVNBAQRBAVCUAUBUCUSVFVKVFFVMUSVF
      VKUSVFVKURVEVKUQVDBVCQUDUEUFVKVFUGUHUIUJUKCVAULVGCMUMUNABCUOUP $.
  $}

  ${
    $d A b c $.
    $( For ordinals, the successor operation is injective, so there is at most
       one ordinal that a given ordinal could be the successor of.  Lemma 1.17
       of [Schloeder] p. 2.  (Contributed by RP, 18-Jan-2025.) $)
    onsucf1lem $p |- ( A e. On -> E* b e. On A = suc b ) $=
      ( vc con0 wcel cv csuc wceq weq wi wral wrmo cuni onuni onsucuni2 adantlr
      wex wa simpr eqtr2d anim1i adantr ancomd suc11 syl mpbid ralrimiva imbi2d
      wb ex eqeq2 ralbidv spcedv nfv rmo2 sylibr ) ADEZABFZGZHZBCIZJZBDKZCQUTBD
      LUQVCUTURAMZHZJZBDKCDVDANZUQVFBDUQURDEZRZUTVEVIUTRZUSVDGZHZVEVJVKAUSUQUTV
      KAHVHAUROPVIUTSTVJVHVDDEZRVLVEUIVJVMVHVIVMVHRUTUQVMVHVGUAUBUCURVDUDUEUFUJ
      UGCFZVDHZVBVFBDVOVAVEUTVNVDURUKUHULUMUTBCDUTCUNUOUP $.
  $}

  ${
    $d A b $.
    $( The successor operation is bijective between the ordinals and the class
       of successor ordinals.  Lemma 1.17 of [Schloeder] p. 2.  (Contributed by
       RP, 18-Jan-2025.) $)
    onsucf1olem $p |- ( ( A e. On /\ A =/= (/) /\ -. Lim A )
                        -> E! b e. On A = suc b ) $=
      ( con0 wcel c0 wne wlim wn w3a cv csuc wceq wa wrmo wreu cuni 3ad2ant1 wi
      wex wo onuni word wb eloni unizlim oran anbi1i xchbinxr bitrdi syl pm2.21
      df-ne biimtrdi com23 3impib idd onuniorsuc mpjaod jca eleq1 suceq anbi12d
      eqeq2d spcedv onsucf1lem weu df-eu df-reu df-rmo anbi2i 3bitr4i sylanbrc
      wmo ) ACDZAEFZAGZHZIZBJZCDZAVSKZLZMZBSZWBBCNZWBBCOZVRWCAPZCDZAWGKZLZMBCWG
      VNVOWHVQAUAQZVRWHWJWKVRAWGLZWJWJVNVOVQWLWJRVNWLVOVQMZWJVNWLWMHZWMWJRVNAUB
      ZWLWNUCAUDWOWLAELZVPTZWNAUEWQWPHZVQMWMWPVPUFVOWRVQAEULUGUHUIUJWMWJUKUMUNU
      OVRWJUPVNVOWLWJTVQAUQQURUSVSWGLZVTWHWBWJVSWGCUTWSWAWIAVSWGVAVCVBVDVNVOWEV
      QABVEQWCBVFWDWCBVMZMWFWDWEMWCBVGWBBCVHWEWTWDWBBCVIVJVKVL $.
  $}

  ${
    $d a b x $.
    onsucrn.f $e |- F = ( x e. On |-> suc x ) $.
    $( The successor operation is surjective onto its range, the class of
       successor ordinals.  Lemma 1.17 of [Schloeder] p. 2.  (Contributed by
       RP, 18-Jan-2025.) $)
    onsucrn $p |- ran F = { a e. On | E. b e. On a = suc b } $=
      ( cv csuc wceq con0 wrex cab wcel crn crab simpr adantr eqeltrd rexlimiva
      wa onsuc pm4.71ri suceq eqeq2d cbvrexvw anbi2i bitri abbii df-rab 3eqtr4i
      weq rnmpt ) CFZAFZGZHZAIJZCKULILZULDFZGZHZDIJZSZCKBMVACINUPVBCUPUQUPSVBUP
      UQUOUQAIUMILZUOSULUNIVCUOOVCUNILUOUMTPQRUAUPVAUQUOUTADIADUJUNUSULUMURUBUC
      UDUEUFUGACIUNBEUKVACIUHUI $.
  $}

  ${
    $d F a b $.  $d x a b $.
    onsucf1o.f $e |- F = ( x e. On |-> suc x ) $.
    $( The successor operation is a bijective function between the ordinals and
       the class of successor ordinals.  Lemma 1.17 of [Schloeder] p. 2.
       (Contributed by RP, 18-Jan-2025.) $)
    onsucf1o $p |- F : On -1-1-onto->
                        { a e. On | E. b e. On a = suc b } $=
      ( con0 cv csuc wceq wrex crab wf1o wfn crn cfv weq wral wcel fin1a2lem1
      wi wf1 fin1a2lem2 ax-mp onsucrn eqeqan12d suc11 bitrd biimpd rgen2 dff1o6
      f1fn wa mpbir3an ) FCGZDGZHZIDFJCFKZBLBFMZBNUQIUNBOZUOBOZIZCDPZTZDFQCFQFF
      BUAURABEUBFFBUKUCABCDEUDVCCDFFUNFRZUOFRZULZVAVBVFVAUNHZUPIVBVDVEUSVGUTUPA
      UNBESAUOBESUEUNUOUFUGUHUICDFUQBUJUM $.
  $}

  ${
    $d A b $.
    $( A limit ordinal is a nonzero ordinal that contains all the successors of
       its elements.  Lemma 1.18 of [Schloeder] p. 2.  Closely related to
       ~ dflim4 .  (Contributed by RP, 17-Jan-2025.) $)
    dflim7 $p |- ( Lim A <-> ( Ord A /\ A. b e. A suc b e. A
                                     /\ A =/= (/) ) ) $=
      ( wlim word c0 wcel cv csuc wral w3a wne dflim4 ord0eln0 biancomd pm5.32i
      wa anbi1d 3anass 3bitr4i bitri ) ACADZEAFZBGHAFBAIZJZUAUCAEKZJZBALUAUBUCP
      ZPUAUCUEPZPUDUFUAUGUHUAUGUCUEUAUBUEUCAMQNOUAUBUCRUAUCUERST $.
  $}

  ${
    onov0suclim.0 $e |- ( A e. On -> ( A .(x) (/) ) = D ) $.
    onov0suclim.suc $e |- ( ( A e. On /\ C e. On ) ->
                               ( A .(x) suc C ) = E ) $.
    onov0suclim.lim $e |- ( ( ( A e. On /\ B e. On ) /\ Lim B )
                          -> ( A .(x) B ) = F ) $.
    $( Compactly express rules for binary operations on ordinals.  (Contributed
       by RP, 18-Jan-2025.) $)
    onov0suclim $p |- ( ( A e. On /\ B e. On ) -> (
                 ( B = (/) -> ( A .(x) B ) = D )
              /\ ( ( B = suc C /\ C e. On ) -> ( A .(x) B ) = E )
              /\ ( Lim B -> ( A .(x) B ) = F ) ) ) $=
      ( con0 wcel wa c0 wceq syl adantl ex wn pm2.21d wlim wo cuni csuc co word
      wi w3a eloni orduniorsuc unizlim biimpd orim1d mpd oveq2 sylan9eqr 0elsuc
      ad2antrr simpl eleqtrrd n0i impancom nlim0 limeq mtbiri 3jca con2i notbid
      biimprd nlimsucg impel a1d jaod c1o wne 1n0 necom df-1o uni0 suceq eqtr4i
      ax-mp neeq2i df-ne 3bitri unieq eqeq12d bitr4id mpbii simprl oveq2d eqtrd
      id adantrl onuni mpan9 adantll ) AKLZBKLZMZBNOZBUAZUBZBBUCZUDZOZUBZXAABEU
      EZDOZUGZBCUDZOZCKLZMZXHFOZUGZXBXHGOZUGZUHZWSXGWRWSBUFZXGBUIXTBXDOZXFUBXGB
      UJXTYAXCXFXTYAXCBUKULUMUNPQWTXCXSXFWTXAXSXBWTXAXSWTXAMZXJXPXRWRXJWSXAWRXA
      XIXAWRXHANEUEDBNAEUOHUPRURWTXNXAXOXNXAXOUGWTXNXAXOXNNBLXASZXNNXKBXMNXKLZX
      LXMCUFYDCUICUQPQXLXMUSUTBNVAPTQVBYBXBXQXAXBSZWTXAXBNUAVCBNVDVEZQTVFRWTXBX
      SWTXBMZXJXPXRYGXAXIXBYCWTXAXBYFVGQTWTXNXBXOWTXNMXBXOXNYEWTXLXKUAZSZYEXMXL
      YEYIXLXBYHBXKVDVHVICKVJVKQTVBYGXQXBJVLVFRVMWTXFXSWTXFMZXJXPXRYJXAXIXFYCWT
      XAXFXAVNNVOZXFSZVPXAYKNNUCZUDZOZSZYLYKNVNVONYNVOYPVNNVQVNYNNVNNUDZYNVRYMN
      OYNYQOVSYMNVTWBWAWCNYNWDWEXAXFYOXABNXEYNXAWMXAXDYMOXEYNOBNWFXDYMVTPWGVHWH
      WIVGQTWRXPWSXFWRXNXOWRXNMZXHAXKEUEZFYRBXKAEWRXLXMWJWKWRXMYSFOXLIWNWLRURYJ
      XBXQWSXFYEWRWSXEUAZSZXFYEWSXDKLUUABWOXDKVJPXFYEUUAXFXBYTBXEVDVHVIWPWQTVFR
      VMUN $.
  $}

  ${
    $d A c $.  $d B c $.
    $( Closed form expression of the value of ordinal addition for the cases
       when the second ordinal is zero, a successor ordinal, or a limit
       ordinal.  Definition 2.3 of [Schloeder] p. 4.  See ~ oa0 , ~ oasuc , and
       ~ oalim .  (Contributed by RP, 18-Jan-2025.) $)
    oa0suclim $p |- ( ( A e. On /\ B e. On ) -> (
                 ( B = (/) -> ( A +o B ) = A )
              /\ ( ( B = suc C /\ C e. On ) -> ( A +o B ) = suc ( A +o C ) )
              /\ ( Lim B -> ( A +o B ) = U_ c e. B ( A +o c ) ) ) ) $=
      ( coa co csuc cv ciun oasuc con0 wcel wlim wceq oalim anassrs onov0suclim
      oa0 ) ABCAEACEFGDBADHEFIZARACJAKLBKLBMABEFSNDABKOPQ $.
  $}

  ${
    $d A c $.  $d B c $.
    $( Closed form expression of the value of ordinal multiplication for the
       cases when the second ordinal is zero, a successor ordinal, or a limit
       ordinal.  Definition 2.5 of [Schloeder] p. 4.  See ~ om0 , ~ omsuc , and
       ~ omlim .  (Contributed by RP, 18-Jan-2025.) $)
    om0suclim $p |- ( ( A e. On /\ B e. On ) -> (
                 ( B = (/) -> ( A .o B ) = (/) )
              /\ ( ( B = suc C /\ C e. On )
                   -> ( A .o B ) = ( ( A .o C ) +o A ) )
              /\ ( Lim B -> ( A .o B ) = U_ c e. B ( A .o c ) ) ) ) $=
      ( c0 comu co coa ciun omsuc con0 wcel wlim wceq omlim anassrs onov0suclim
      cv om0 ) ABCEFACFGAHGDBADRFGIZASACJAKLBKLBMABFGTNDABKOPQ $.
  $}

  ${
    $d A c $.  $d B c $.
    $( Closed form expression of the value of ordinal exponentiation for the
       cases when the second ordinal is zero, a successor ordinal, or a limit
       ordinal.  Definition 2.6 of [Schloeder] p. 4.  See ~ oe0 , ~ oesuc ,
       ~ oe0m1 , and ~ oelim .  (Contributed by RP, 18-Jan-2025.) $)
    oe0suclim $p |- ( ( A e. On /\ B e. On ) -> (
                 ( B = (/) -> ( A ^o B ) = 1o )
              /\ ( ( B = suc C /\ C e. On )
                   -> ( A ^o B ) = ( ( A ^o C ) .o A ) )
              /\ ( Lim B -> ( A ^o B )
                   = if ( (/) e. A , U_ c e. B ( A ^o c ) , (/) ) ) ) ) $=
      ( c1o coe co comu c0 wcel cv ciun cif oe0 oesuc con0 wceq wa simpr eqtr4d
      wlim oelim iftrued wn wi simpl 0elon wss ontri1 ss0 biimtrrdi oveq1 oe0m1
      sylancl biimpd 0ellim impel adantl sylan9eqr ex syld imp iffalsed anassrs
      pm2.61dan onov0suclim ) ABCEFACFGAHGIAJZDBADKFGLZIMZANACOAPJZBPJZBUAZABFG
      ZVIQZVJVKVLRZRZVGVNVPVGRZVMVHVIDABPUBVQVGVHIVPVGSUCTVPVGUDZRZVMIVIVPVRVMI
      QZVPVRAIQZVTVPVJIPJZVRWAUEVJVOUFUGVJWBRVRAIUHWAAIUIAUJUKUNVPWAVTWAVPVMIBF
      GZIAIBFULVOWCIQZVJVKIBJZWDVLVKWEWDBUMUOBUPUQURUSUTVAVBVSVGVHIVPVRSVCTVEVD
      VF $.
  $}

  $( The union of any _set_ of ordinals is an ordinal.  See ~ ssonuni . $)

  $( The operations of addition, multiplication, and exponentiation are closed.
     Remark 2.8 of [Schloeder] p. 5.  See ~ oacl , ~ omcl , ~ oecl .
     (Contributed by RP, 18-Jan-2025.) $)
  oaomoecl $p |- ( ( A e. On /\ B e. On ) -> ( ( A +o B ) e. On
                      /\ ( A .o B ) e. On /\ ( A ^o B ) e. On ) ) $=
    ( con0 wcel wa coa co comu coe oacl omcl oecl 3jca ) ACDBCDEABFGCDABHGCDABI
    GCDABJABKABLM $.

  ${
    $d A b $.
    $( If the union of a set of ordinals is a successor ordinal, then that
       union is the maximum element of the set.  This is not a bijection
       because sets where the maximum element is zero or a limit ordinal exist.
       Lemma 2.11 of [Schloeder] p. 5.  (Contributed by RP, 27-Jan-2025.) $)
    onsupsucismax $p |- ( ( A C_ On /\ A e. V ) ->
                       ( E. b e. On U. A = suc b -> U. A e. A ) ) $=
      ( con0 wss cuni cv csuc wceq wrex wcel wi wn onsupnmax word wb orduninsuc
      ssorduni syl sylibd con4d adantr ) ADEZAFZCGHICDJZUDAKZLABKUCUFUEUCUFMUDU
      DFIZUEMZANUCUDOUGUHPARCUDQSTUAUB $.
  $}

  ${
    $d A a $.  $d B a b $.
    $( If for every element of a set of ordinals there is an element of a
       subset which is at least as large, then the union of the set and the
       subset is the same.  Lemma 2.12 of [Schloeder] p. 5.  (Contributed by
       RP, 27-Jan-2025.) $)
    onsssupeqcond $p |- ( ( A C_ On /\ A e. V ) ->
                       ( ( B C_ A /\ A. a e. A E. b e. B a C_ b ) ->
                       U. A = U. B ) ) $=
      ( cv wrex wral wa cuni wceq wi con0 wcel uniss2 adantl uniss adantr eqssd
      wss a1i ) BATZDFEFTEBGDAHZIZAJZBJZKLAMTACNIUDUEUFUCUEUFTUBDEABOPUBUFUETUC
      BAQRSUA $.
  $}

  $( An ordinal which is a limit ordinal is equal to its supremum.  Lemma 2.13
     of [Schloeder] p. 5.  (Contributed by RP, 27-Jan-2025.) $)
  limexissup $p |- ( ( Lim A /\ A e. V ) -> A = sup ( A , On , _E ) ) $=
    ( wlim wcel wa cuni con0 cep csup wceq limuni adantr wss limord ordsson syl
    word onsupuni sylan eqtr4d ) ACZABDZEAAFZAGHIZUAAUCJUBAKLUAAGMZUBUDUCJUAAQU
    EANAOPABRST $.

  ${
    $d A x $.
    $( A limit ordinal is the union of its elements, indexed union version.
       Lemma 2.13 of [Schloeder] p. 5.  See ~ limuni .  (Contributed by RP,
       27-Jan-2025.) $)
    limiun $p |- ( Lim A -> A = U_ x e. A x ) $=
      ( wlim cuni cv ciun limuni uniiun eqtrdi ) BCBBDABAEFBGABHI $.
  $}

  ${
    $d A x $.
    $( An ordinal which is a limit ordinal is equal to the supremum of the
       class of all its elements.  Lemma 2.13 of [Schloeder] p. 5.
       (Contributed by RP, 27-Jan-2025.) $)
    limexissupab $p |- ( ( Lim A /\ A e. V ) ->
                        A = sup ( { x | x e. A } , On , _E ) ) $=
      ( wlim wcel wa cuni con0 cep csup cab wceq limuni adantr wss word ordsson
      cv limord syl onsupuni sylan abid1 supeq1 mp1i 3eqtr2d ) BDZBCEZFZBBGZBHI
      JZARBEAKZHIJZUGBUJLUHBMNUGBHOZUHUKUJLUGBPUNBSBQTBCUAUBBULLUKUMLUIABUCHBUL
      IUDUEUF $.
  $}

  $( Ordinal one is both a left and right identity of ordinal multiplication.
     Lemma 2.15 of [Schloeder] p. 5.  See ~ om1 and ~ om1r for individual
     statements.  (Contributed by RP, 29-Jan-2025.) $)
  om1om1r $p |- ( A e. On -> ( ( 1o .o A ) = ( A .o 1o )
                                 /\ ( A .o 1o ) = A ) ) $=
    ( con0 wcel c1o comu co wceq om1r om1 eqtr4d jca ) ABCZDAEFZADEFZGNAGLMANAH
    AIZJOK $.

  $( Ordinal zero raised to any nonzero ordinal power is zero and zero to the
     zeroth power is one.  Lemma 2.18 of [Schloeder] p. 6.  (Contributed by RP,
     29-Jan-2025.) $)
  oe0rif $p |- ( A e. On ->
                       ( (/) ^o A ) = if ( (/) e. A , (/) , 1o ) ) $=
    ( con0 wcel c0 coe c1o cdif cif oe0m wceq nel02 iffalsed difeq2 dif0 eqtrdi
    co eqtr4d adantl wa iftrue wss word eloni ordgt0ge1 syl biimpa ssdif0 sylib
    wb on0eqel mpjaodan ) ABCZDAEPFAGZDACZDFHZAIULADJZUOUMJZUNUPUQULUPUOFUMUPUN
    DFADKLUPUMFDGFADFMFNOQRULUNSZUODUMUNUODJULUNDFTRURFAUAZUMDJULUNUSULAUBUNUSU
    IAUCAUDUEUFFAUGUHQAUJUKQ $.

  ${
    $d A c $.  $d B c $.
    $( While subtraction can't be a binary operation on ordinals, for any pair
       of ordinals there exists an ordinal that can be added to the lessor (or
       equal) one which will sum to the greater.  Theorem 2.19 of [Schloeder]
       p. 6.  (Contributed by RP, 29-Jan-2025.) $)
    oasubex $p |- ( ( A e. On /\ B e. On /\ B C_ A ) ->
                       E. c e. On ( c C_ A /\ ( B +o c ) = A ) ) $=
      ( con0 wcel wss w3a cv coa co wceq wrex simp2 simp1 simp3 oawordex biimpa
      wa simpr adantr syl21anc simpl1 simpl2 oaword2 syl2anc eqsstrd wb syl3anc
      oaword mpbird ex ancrd reximdva mpd ) ADEZBDEZBAFZGZBCHZIJZAKZCDLZUSAFZVA
      RZCDLURUPUOUQVBUOUPUQMUOUPUQNUOUPUQOUPUORUQVBCBAPQUAURVAVDCDURUSDEZRZVAVC
      VFVAVCVFVARZVCUTBAIJZFZVGUTAVHVFVASVFAVHFZVAVFUOUPVJUOUPUQVEUBZUOUPUQVEUC
      ZABUDUETUFVFVCVIUGZVAVFVEUOUPVMURVESVKVLUSABUIUHTUJUKULUMUN $.
  $}

  $( Natural numbers are closed under ordinal addition, multiplication, and
     exponentiation.  Theorem 2.20 of [Schloeder] p. 6.  See ~ nnacl ,
     ~ nnmcl , ~ nnecl .  (Contributed by RP, 29-Jan-2025.) $)
  nnamecl $p |- ( ( A e. _om /\ B e. _om ) -> ( ( A +o B ) e. _om
                      /\ ( A .o B ) e. _om /\ ( A ^o B ) e. _om ) ) $=
    ( com wcel wa coa co comu coe nnacl nnmcl nnecl 3jca ) ACDBCDEABFGCDABHGCDA
    BIGCDABJABKABLM $.

  $( The successor operation preserves the less-than-or-equal relationship
     between ordinals.  Lemma 3.1 of [Schloeder] p. 7.  (Contributed by RP,
     29-Jan-2025.) $)
  onsucwordi $p |- ( ( A e. On /\ B e. On )
                      -> ( A C_ B -> suc A C_ suc B ) ) $=
    ( con0 wcel wa wss csuc word wb eloni ordsucsssuc syl2an biimpd ) ACDZBCDZE
    ABFZAGBGFZNAHBHPQIOAJBJABKLM $.

  $( Any ordinal sum is greater-than-or-equal to either of its addends.  See
     ~ oaword1 and ~ oaword2 . $)

  $( The ordinal sum of any ordinal with a larger limit ordinal (on the right)
     is a limit ordinal.  See ~ oalimcl . $)

  ${
    $( The ordinal sum of any ordinal with a limit ordinal on the right is a
       limit ordinal.  (Contributed by RP, 6-Feb-2025.) $)
    oalim2cl $p |- ( ( A e. On /\ Lim B /\ B e. V ) ->
                     Lim ( A +o B ) ) $=
      ( con0 wcel wlim w3a coa co simp1 simp3 simp2 oalimcl syl12anc ) ADEZBFZB
      CEZGOQPABHIFOPQJOPQKOPQLABCMN $.
  $}

  $( Given ` C ` is a limit ordinal, the sum of any ordinal with an ordinal
     less than ` C ` is less than the sum of the first ordinal with ` C ` .
     Lemma 3.5 of [Schloeder] p. 7.  (Contributed by RP, 29-Jan-2025.) $)
  oaltublim $p |- ( ( A e. On /\ B e. C /\ ( Lim C /\ C e. V ) ) ->
                      ( A +o B ) e. ( A +o C ) ) $=
    ( con0 wcel wlim wa w3a coa co word cvv limord elex anim12i sylibr 3ad2ant3
    elon2 simp1 jca simp2 oaordi sylc ) AEFZBCFZCGZCDFZHZIZCEFZUEHUFABJKACJKFUJ
    UKUEUIUEUKUFUICLZCMFZHUKUGULUHUMCNCDOPCSQRUEUFUITUAUEUFUIUBBCAUCUD $.

  $( Ordinal addition of the same number on the left preserves the ordering of
     the numbers on the right.  Lemma 3.6 of [Schloeder] p. 8.  (Contributed by
     RP, 29-Jan-2025.) $)
  oaordi3 $p |- ( ( A e. On /\ B e. On /\ C e. On ) -> ( B e. C ->
                      ( A +o B ) e. ( A +o C ) ) ) $=
    ( con0 wcel w3a wa coa co wi simp3 simp1 jca oaordi syl ) ADEZBDEZCDEZFZRPG
    BCEABHIACHIEJSRPPQRKPQRLMBCANO $.

  $( When the same ordinal is added on the left, ordering of the sums is
     equivalent to the ordering of the ordinals on the right.  Theorem 3.7 of
     [Schloeder] p. 8.  (Contributed by RP, 29-Jan-2025.) $)
  oaord3 $p |- ( ( A e. On /\ B e. On /\ C e. On ) -> ( B e. C <->
                      ( A +o B ) e. ( A +o C ) ) ) $=
    ( con0 wcel coa co wb oaord 3comr ) BDECDEADEBCEABFGACFGEHBCAIJ $.

  $( Ordinal one plus omega is equal to omega.  See ~ oaabs for the sum of any
     natural number on the left and ordinal at least as large as omega on the
     right.  Lemma 3.8 of [Schloeder] p. 8.  See ~ oaabs2 where a power of
     omega is the upper bound of the left and a lower bound on the right.
     (Contributed by RP, 29-Jan-2025.) $)
  1oaomeqom $p |- ( 1o +o _om ) = _om $=
    ( com con0 wcel c1o coa co wceq omelon 1onn oaabslem mp2an ) ABCDACDAEFAGHI
    DJK $.

  ${
    $d A x y $.  $d B x y $.
    $( The right addend absorbs the sum with an ordinal iff that ordinal times
       omega is less than or equal to the right addend.  (Contributed by RP,
       19-Feb-2025.) $)
    oaabsb $p |- ( ( A e. On /\ B e. On ) ->
                   ( ( A .o _om ) C_ B <-> ( A +o B ) = B ) ) $=
      ( vx vy con0 wcel wa com comu co wss coa omelon adantr ad2antrr simpr c1o
      wceq oveq2 c0 cv wrex wb mpan2 oawordex sylan simpl oaass syl3anc 1on odi
      omcl mp3an23 1oaomeqom oveq2i a1i om1 oveq1d 3eqtr3rd eqtr3d id syl5ibcom
      eqeq12d rexlimdva sylbid ciun wlim limom mpanr12 wral csuc sseq1d weq om0
      0ss eqsstrdi w3a nnon syl2an 3jca expcom adantrd imp oaword biimpa adantl
      omlim syl 1onn nnacom mpan oa1suc eqtrd oveq2d 3sstr3d exp31 finds2 com12
      ralrimiv iunss sylibr eqsstrd ex impbid ) AEFZBEFZGZAHIJZBKZABLJZBRZXGXIX
      HCUAZLJZBRZCEUBZXKXEXHEFZXFXIXOUCXEHEFZXPMAHULUDZCXHBUEUFXGXNXKCEXGXLEFZG
      ZAXMLJZXMRXNXKXTAXHLJZXLLJZYAXMXTXEXPXSYCYARXGXEXSXEXFUGZNXEXPXFXSXROXGXS
      PAXHXLUHUIXEYCXMRXFXSXEYBXHXLLXEAQHLJZIJZAQIJZXHLJZXHYBXEQEFZXQYFYHRUJMAQ
      HUKUMYFXHRXEYEHAIUNUOUPXEYGAXHLAUQZURUSUROUTXNYAXJXMBXMBALSXNVAVCVBVDVEXG
      XKXIXGXKGZXHCHAXLIJZVFZBXEXHYMRZXFXKXEXQHVGYNMVHCAHEWGVIOYKYLBKZCHVJYMBKY
      KYOCHXLHFYKYOYOATIJZBKZADUAZIJZBKZAYRVKZIJZBKZYKCDXLTRYLYPBXLTAISVLCDVMYL
      YSBXLYRAISVLXLUUARYLUUBBXLUUAAISVLXEYQXFXKXEYPTBAVNBVOVPOYRHFZYKYTUUCUUDY
      KGZYTGAYSLJZXJUUBBUUEYTUUFXJKZUUEYSEFZXFXEVQZYTUUGUCUUDYKUUIUUDXGUUIXKXGU
      UDUUIXGUUDGUUHXFXEXGXEYREFZUUHUUDYDYRVRZAYRULVSXGXFUUDXEXFPNXGXEUUDYDNVTW
      AWBWCYSBAWDWHWEUUEUUFUUBRZYTUUDYKUULUUDXGUULXKUUDXEUULXFXEUUDUULXEUUDGZAQ
      YRLJZIJZYGYSLJZUUBUUFUUMXEYIUUJUUOUUPRXEUUDUGYIUUMUJUPUUDUUJXEUUKWFAQYRUK
      UIUUDUUOUUBRXEUUDUUNUUAAIUUDUUNYRQLJZUUAQHFUUDUUNUUQRWIQYRWJWKUUDUUJUUQUU
      ARUUKYRWLWHWMWNWFXEUUPUUFRUUDXEYGAYSLYJURNUSWAWBWBWCNUUEXKYTYKXKUUDXGXKPW
      FNWOWPWQWRWSCHYLBWTXAXBXCXD $.
  $}

  $( When omega is added on the right to ordinals zero and one, ordering of the
     sums is not equivalent to the ordering of the ordinals on the left.
     Remark 3.9 of [Schloeder] p. 8.  (Contributed by RP, 29-Jan-2025.) $)
  oaordnrex $p |- -. ( (/) e. 1o <-> ( (/) +o _om ) e. ( 1o +o _om ) ) $=
    ( c0 c1o wcel com coa co wb wn 0lt1o word ordom ordirr con0 wceq oa0r ax-mp
    omelon 1oaomeqom eleq12i sylnibr 2th xor3 mpbir ) ABCZADEFZBDEFZCZGHUDUGHZG
    UDUHIDJZUHKUIDDCUGDLUEDUFDDMCUEDNQDOPRSTPUAUDUGUBUC $.

  ${
    $d a b c $.
    $( When the same ordinal is added on the right, ordering of the sums is not
       equivalent to the ordering of the ordinals on the left.  Remark 3.9 of
       [Schloeder] p. 8.  (Contributed by RP, 29-Jan-2025.) $)
    oaordnr $p |- E. a e. On E. b e. On E. c e. On -. ( a e. b <->
                       ( a +o c ) e. ( b +o c ) ) $=
      ( c0 c1o wcel com coa co wb wn con0 wrex wceq oveq2 notbid rspcev rexbidv
      cv oveq1 wel oaordnrex 0elon 1on omelon eleq12d bibi2d mpan eleq2 bibi12d
      eleq2d sylancr eleq1 eleq1d ax-mp ) DEFZDGHIZEGHIZFZJZKZABUAZASZCSZHIZBSZ
      VDHIZFZJZKZCLMZBLMZALMZUBVADLFDVFFZDVDHIZVGFZJZKZCLMZBLMZVMUCVAELFUPVOEVD
      HIZFZJZKZCLMZVTUDGLFVAWEUEWDVACGLVDGNZWCUTWFWBUSUPWFVOUQWAURVDGDHOVDGEHOU
      FUGPQUHVSWEBELVFENZVRWDCLWGVQWCWGVNUPVPWBVFEDUIWGVGWAVOVFEVDHTUKUJPRQULVL
      VTADLVCDNZVKVSBLWHVJVRCLWHVIVQWHVBVNVHVPVCDVFUMWHVEVOVGVCDVDHTUNUJPRRQULU
      O $.
  $}

  $( Any ordinal sum is greater-than-or-equal to either of its addends.  See
     ~ oaword1 and ~ oaword2 . $)

  $( Any nonzero ordinal product is greater-than-or-equal to the term on the
     left.  Lemma 3.11 of [Schloeder] p. 8.  See ~ omword1 .  (Contributed by
     RP, 29-Jan-2025.) $)
  omge1 $p |- ( ( A e. On /\ B e. On /\ B =/= (/) ) ->
                       A C_ ( A .o B ) ) $=
    ( con0 wcel c0 wne w3a wa co 3simpa on0eln0 biimpar 3adant1 omword1 syl2anc
    comu wss ) ACDZBCDZBEFZGRSHEBDZAABPIQRSTJSTUARSUATBKLMABNO $.

  $( Any nonzero ordinal product is greater-than-or-equal to the term on the
     right.  Lemma 3.12 of [Schloeder] p. 9.  See ~ omword2 .  (Contributed by
     RP, 29-Jan-2025.) $)
  omge2 $p |- ( ( A e. On /\ B e. On /\ A =/= (/) ) ->
                       B C_ ( A .o B ) ) $=
    ( con0 wcel c0 wne w3a wa comu co wss ancom anbi1i df-3an wb on0eln0 adantl
    pm5.32i 3bitr4i omword2 sylbi ) ACDZBCDZAEFZGZUCUBHZEADZHZBABIJKUBUCHZUDHUF
    UDHUEUHUIUFUDUBUCLMUBUCUDNUFUGUDUBUGUDOUCAPQRSBATUA $.

  $( The nonzero product with an limit ordinal on the right is a limit ordinal.
     Lemma 3.13 of [Schloeder] p. 9.  (Contributed by RP, 29-Jan-2025.) $)
  omlim2 $p |- ( ( ( A e. On /\ A =/= (/) ) /\ ( Lim B /\ B e. V ) ) ->
                       Lim ( A .o B ) ) $=
    ( con0 wcel c0 wne wa wlim comu simpll simpr ancomd on0eln0 biimpar omlimcl
    co adantr syl21anc ) ADEZAFGZHZBIZBCEZHZHZTUDUCHFAEZABJQITUAUEKUFUCUDUBUELM
    UBUGUETUGUAANORABCPS $.

  $( Given a limit ordinal, the product of any nonzero ordinal with an ordinal
     less than that limit ordinal is less than the product of the nonzero
     ordinal with the limit ordinal .  Lemma 3.14 of [Schloeder] p. 9.
     (Contributed by RP, 29-Jan-2025.) $)
  omord2lim $p |- ( ( ( A e. On /\ A =/= (/) ) /\ ( Lim C /\ C e. V ) ) ->
                       ( B e. C -> ( A .o B ) e. ( A .o C ) ) ) $=
    ( con0 wcel c0 wne wa wlim comu word limord ad2antrl ordelon sylan cvv elex
    co anim12i ad2antlr elon2 sylibr simplll simpr on0eln0 biimpar ad2antrr w3a
    omord biimpa syl32anc ex ) AEFZAGHZIZCJZCDFZIZIZBCFZABKSACKSFZUTVAIZBEFZCEF
    ZUNVAGAFZVBUTCLZVAVDUQVGUPURCMZNCBOPVCVGCQFZIZVEUSVJUPVAUQVGURVIVHCDRTUACUB
    UCUNUOUSVAUDUTVAUEUPVFUSVAUNVFUOAUFUGUHVDVEUNUIVAVFIVBBCAUJUKULUM $.

  $( Ordinal multiplication of the same nonzero number on the left preserves
     the ordering of the numbers on the right.  Lemma 3.15 of [Schloeder] p. 9.
     (Contributed by RP, 29-Jan-2025.) $)
  omord2i $p |- ( ( ( A e. On /\ A =/= (/) ) /\ C e. On ) ->
                       ( B e. C -> ( A .o B ) e. ( A .o C ) ) ) $=
    ( con0 wcel c0 wne wa comu co anim1ci on0eln0 biimpar adantr omordi syl2anc
    wi simpl ) ADEZAFGZHZCDEZHUBSHFAEZBCEABIJACIJEQUASUBSTRKUAUCUBSUCTALMNBCAOP
    $.

  $( When the same nonzero ordinal is multiplied on the left, ordering of the
     products is equivalent to the ordering of the ordinals on the right.
     Theorem 3.16 of [Schloeder] p. 9.  (Contributed by RP, 29-Jan-2025.) $)
  omord2com $p |- ( ( A e. On /\ B e. On /\ C e. On ) ->
                       ( ( B e. C /\ (/) e. A )
                       <-> ( A .o B ) e. ( A .o C ) ) ) $=
    ( con0 wcel c0 wa comu co wb omord 3comr ) BDECDEADEBCEFAEGABHIACHIEJBCAKL
    $.

  $( Ordinal two times omega is omega.  Lemma 3.17 of [Schloeder] p. 10.
     (Contributed by RP, 30-Jan-2025.) $)
  2omomeqom $p |- ( 2o .o _om ) = _om $=
    ( com con0 wcel c2o c0 comu co wceq omelon csn cpr 0ex prid1 df2o2 eleqtrri
    2onn omabslem mp3an ) ABCDACEDCDAFGAHIPEEEJZKDESLMNODQR $.

  $( When omega is multiplied on the right to ordinals one and two, ordering of
     the products is not equivalent to the ordering of the ordinals on the
     left.  Remark 3.18 of [Schloeder] p. 10.  (Contributed by RP,
     29-Jan-2025.) $)
  omnord1ex $p |- -. ( 1o e. 2o <-> ( 1o .o _om ) e. ( 2o .o _om ) ) $=
    ( c1o c2o wcel com comu co wb wn c0 1oelpr df2o3 eleqtrri word ordom ordirr
    cpr con0 wceq omelon 1onn 0lt1o omabslem mp3an 2omomeqom eleq12i ax-mp xor3
    sylnibr 2th mpbir ) ABCZADEFZBDEFZCZGHUKUNHZGUKUOAIAPBJKLDMZUONUPDDCUNDOULD
    UMDDQCADCIACULDRSTUAAUBUCUDUEUHUFUIUKUNUGUJ $.

  ${
    $d a b c $.
    $( When the same nonzero ordinal is multiplied on the right, ordering of
       the products is not equivalent to the ordering of the ordinals on the
       left.  Remark 3.18 of [Schloeder] p. 10.  (Contributed by RP,
       4-Feb-2025.) $)
    omnord1 $p |- E. a e. On E. b e. On E. c e. ( On \ 1o ) -. ( a e. b <->
                       ( a .o c ) e. ( b .o c ) ) $=
      ( c1o c2o wcel com comu co wb wn con0 wrex wceq oveq2 notbid rspcev oveq1
      cv rexbidv wel omnord1ex 1on 2on c0 omelon peano1 ondif1 mpbir2an eleq12d
      cdif bibi2d mpan eleq2 eleq2d bibi12d sylancr eleq1 eleq1d ax-mp ) DEFZDG
      HIZEGHIZFZJZKZABUAZASZCSZHIZBSZVIHIZFZJZKZCLDUKZMZBLMZALMZUBVFDLFDVKFZDVI
      HIZVLFZJZKZCVPMZBLMZVSUCVFELFVAWAEVIHIZFZJZKZCVPMZWFUDGVPFZVFWKWLGLFUEGFU
      FUGGUHUIWJVFCGVPVIGNZWIVEWMWHVDVAWMWAVBWGVCVIGDHOVIGEHOUJULPQUMWEWKBELVKE
      NZWDWJCVPWNWCWIWNVTVAWBWHVKEDUNWNVLWGWAVKEVIHRUOUPPTQUQVRWFADLVHDNZVQWEBL
      WOVOWDCVPWOVNWCWOVGVTVMWBVHDVKURWOVJWAVLVHDVIHRUSUPPTTQUQUT $.
  $}

  $( Any nonzero ordinal power is greater-than-or-equal to the term on the
     left.  Lemma 3.19 of [Schloeder] p. 10.  See ~ oewordi .  (Contributed by
     RP, 29-Jan-2025.) $)
  oege1 $p |- ( ( A e. On /\ B e. On /\ B =/= (/) ) ->
                     A C_ ( A ^o B ) ) $=
    ( con0 wcel c0 wne w3a wceq coe co wss wi id 0ss eqsstrdi a1i c1o syl sylc
    wa simpl1 oe1 1on simp2 simp1 3jca anim1i word eloni simp3 ordge1n0 biimprd
    adantr oewordi eqsstrrd ex wo on0eqel mpjaod ) ACDZBCDZBEFZGZAEHZAABIJZKZEA
    DZVDVFLVCVDAEVEVDMVENOPVCVGVFVCVGTZAAQIJZVEVHUTVIAHUTVAVBVGUAAUBRVHQCDZVAUT
    GZVGTQBKZVIVEKVCVKVGVCVJVAUTVJVCUCPUTVAVBUDZUTVAVBUEZUFUGVCVLVGVCBUHZVBVLVC
    VAVOVMBUIRUTVAVBUJVOVLVBBUKULSUMQBAUNSUOUPVCUTVDVGUQVNAURRUS $.

  $( Any power of an ordinal at least as large as two is greater-than-or-equal
     to the term on the right.  Lemma 3.20 of [Schloeder] p. 10.  See
     ~ oeworde .  (Contributed by RP, 29-Jan-2025.) $)
  oege2 $p |- ( ( ( A e. On /\ 1o e. A ) /\ B e. On ) ->
                       B C_ ( A ^o B ) ) $=
    ( con0 wcel c1o wa c2o coe co wss cdif 2on cpr 1oelpr df2o3 eleqtrri ondif2
    c0 mpbir2an wi oeworde mpan adantl csuc onsucss imp adantr eqsstrid wceq wo
    df-2o simpll onsseleq sylancr oewordri adantlr oveq1 ssid eqsstrdi a1i jaod
    wb sylbid mpd sstrd ) ACDZEADZFZBCDZFZBGBHIZABHIZVIBVKJZVHGCGKDZVIVMVNGCDZE
    GDLEREMGNOPGQSGBUAUBUCVJGAJZVKVLJZVJGEUDZAUKVHVRAJZVIVFVGVSAEUEUFUGUHVJVPGA
    DZGAUIZUJZVQVJVOVFVPWBVBLVFVGVIULGAUMUNVJVTVQWAVFVIVTVQTVGGABUOUPWAVQTVJWAV
    KVLVLGABHUQVLURUSUTVAVCVDVE $.

  $( The power of an ordinal at least as large as two with a limit ordinal on
     thr right is a limit ordinal.  Lemma 3.21 of [Schloeder] p. 10.  See
     ~ oelimcl .  (Contributed by RP, 30-Jan-2025.) $)
  rp-oelim2 $p |- ( ( ( A e. On /\ 1o e. A ) /\ ( Lim B /\ B e. V ) ) ->
                       Lim ( A ^o B ) ) $=
    ( con0 wcel c1o wa c2o cdif wlim coe ondif2 biimpri pm3.22 oelimcl syl2an
    co ) ADEFAEGZADHIEZBCEZBJZGABKQJUATGSRALMUATNABCOP $.

  $( Given a limit ordinal, the power of any base at least as large as two
     raised to an ordinal less than that limit ordinal is less than the power
     of that base raised to the limit ordinal .  Lemma 3.22 of [Schloeder]
     p. 10.  See ~ oeordi .  (Contributed by RP, 30-Jan-2025.) $)
  oeord2lim $p |- ( ( ( A e. On /\ 1o e. A ) /\ ( Lim C /\ C e. V ) ) ->
                       ( B e. C -> ( A ^o B ) e. ( A ^o C ) ) ) $=
    ( wlim wcel wa con0 c2o cdif coe co wi limelon ancoms ondif2 biimpri oeordi
    c1o syl2anr ) CEZCDFZGCHFZAHIJFZBCFABKLACKLFMAHFSAFGZUBUAUCCDNOUDUEAPQBCART
    $.

  $( Ordinal exponentiation of the same base at least as large as two preserves
     the ordering of the exponents.  Lemma 3.23 of [Schloeder] p. 11.
     (Contributed by RP, 30-Jan-2025.) $)
  oeord2i $p |- ( ( ( A e. On /\ 1o e. A ) /\ C e. On ) ->
                       ( B e. C -> ( A ^o B ) e. ( A ^o C ) ) ) $=
    ( con0 wcel c1o wa c2o cdif coe co wi ondif2 biimpri anim1ci oeordi syl ) A
    DEFAEGZCDEZGSADHIEZGBCEABJKACJKELRTSTRAMNOBCAPQ $.

  $( When the same base at least as large as two is raised to ordinal powers, ,
     ordering of the power is equivalent to the ordering of the exponents.
     Theorem 3.24 of [Schloeder] p. 11.  (Contributed by RP, 30-Jan-2025.) $)
  oeord2com $p |- ( ( ( A e. On /\ 1o e. A ) /\ B e. On /\ C e. On ) ->
                       ( B e. C <-> ( A ^o B ) e. ( A ^o C ) ) ) $=
    ( con0 wcel c1o wa w3a c2o coe co wb ondif2 3anbi1i 3anrot sylbb1 oeord syl
    cdif ) ADEFAEGZBDEZCDEZHZUAUBADISEZHZBCEABJKACJKELUDUAUBHUCUEUDTUAUBAMNUDUA
    UBOPBCAQR $.

  ${
    $d A x y z $.
    $( Any natural number at least as large as two raised to the power of omega
       is omega.  Lemma 3.25 of [Schloeder] p. 11.  (Contributed by RP,
       30-Jan-2025.) $)
    nnoeomeqom $p |- ( ( A e. _om /\ 1o e. A ) -> ( A ^o _om ) = _om ) $=
      ( vx vy vz com wcel c1o wa coe co cv con0 wceq nnon syl a1i wss w3a wex
      c0 ciun wlim simpl omelon limom pm3.2i 0elon 0ss simpr ontr2 imp syl22anc
      oelim syl21anc wrex cab cuni ovex dfiun2 wel eluniab 19.42v 3anass df-rex
      exbii anbi2i 3bitr4ri excom 3bitri simpr3 simp2 nnecl syl2an onelss mpsyl
      eqsstrd simpr1 sseldd ex exlimdvv csuc peano2 adantl anim1i ondif2 sylibr
      cvv cdif oeworde sucid eqidd 3jca eleq2 eqeq1 3anbi13d spcedv eleq1 oveq2
      c2o vex eqeq2d 3anbi23d exbidv impbid bitrid eqrdv eqtrid eqtrd ) AEFZGAF
      ZHZAEIJZBEABKZIJZUAZEXKALFZELFZEUBZHZTAFZXLXOMXKXIXPXIXJUCZANZOZXSXKXQXRU
      DUEUFPXKTLFZXPTGQZXJXTYDXKUGPYCYEXKGUHPXIXJUIYDXPHYEXJHXTTGAUJUKULBAELUMU
      NXKXOCKZXNMZBEUOZCUPUQZEBCEXNAXMIURUSXKDYIEDKZYIFZDCUTZXMEFZYGRZCSZBSZXKY
      JEFZYKYLYHHZCSYNBSZCSYPYHCYJVAYRYSCYLYMYGHZHZBSYLYTBSZHYSYRYLYTBVBYNUUABY
      LYMYGVCVEYHUUBYLYGBEVDVFVGVEYNCBVHVIXKYPYQXKYNYQBCXKYNYQXKYNHZYFEYJUUCYFX
      NEXKYLYMYGVJXQUUCXNEFZXNEQUDXKXIYMUUDYNYAYLYMYGVKAXMVLVMEXNVNVOVPXKYLYMYG
      VQVRVSVTXKYQYPXKYQHZYOYLYJWAZEFZYFAUUFIJZMZRZCSBEUUFYQUUGXKYJWBZWCZUUEUUJ
      YJUUHFZUUGUUHUUHMZRCWGUUHUUHWGFUUEAUUFIURPUUEUUMUUGUUNUUEUUFUUHYJXKALWSWH
      FZUUFLFZUUFUUHQYQXKXPXJHUUOXIXPXJYBWDAWEWFYQUUGUUPUUKUUFNOAUUFWIVMYJUUFFU
      UEYJDWTWJPVRUULUUEUUHWKWLUUIYLUUMUUIUUNUUGYFUUHYJWMYFUUHUUHWNWOWPXMUUFMZY
      NUUJCUUQYMUUGYGUUIYLXMUUFEWQUUQXNUUHYFXMUUFAIWRXAXBXCWPVSXDXEXFXGXH $.
  $}

  $( Ordinal 3 is the unordered triple containing ordinals 0, 1, and 2.
     (Contributed by RP, 8-Jul-2021.) $)
  df3o2 $p |- 3o = { (/) , 1o , 2o } $=
    ( c3o c2o csuc c0 c1o ctp df-3o csn cun cpr df2o3 uneq1i df-suc df-tp eqtri
    3eqtr4i ) ABCZDEBFZGBBHZIDEJZSIQRBTSKLBMDEBNPO $.

  $( Ordinal 3, fully expanded.  (Contributed by RP, 8-Jul-2021.) $)
  df3o3 $p |- 3o = { (/) , { (/) } , { (/) , { (/) } } } $=
    ( c3o c2o c0 csn cpr ctp df-3o cun df2o2 sneqi uneq12i df-suc df-tp 3eqtr4i
    csuc eqtri ) ABOZCCDZCREZFZGBBDZHSSDZHQTBSUAUBIBSIJKBLCRSMNP $.

  $( When ordinals two and three are both raised to the power of omega,
     ordering of the powers is not equivalent to the ordering of the bases.
     Remark 3.26 of [Schloeder] p. 11.  (Contributed by RP, 30-Jan-2025.) $)
  oenord1ex $p |- -. ( 2o e. 3o <-> ( 2o ^o _om ) e. ( 3o ^o _om ) ) $=
    ( c2o c3o wcel com coe co wb wn c0 c1o 2oex tpid3 df3o2 eleqtrri word ordom
    ctp wceq nnoeomeqom mp2an ordirr 2onn cpr 1oelpr df2o3 3onn eleq12i sylnibr
    1oex tpid2 ax-mp 2th xor3 mpbir ) ABCZADEFZBDEFZCZGHUOURHZGUOUSAIJAQZBIJAKL
    MNDOZUSPVADDCURDUAUPDUQDADCJACUPDRUBJIJUCAUDUENASTBDCJBCUQDRUFJUTBIJAUIUJMN
    BSTUGUHUKULUOURUMUN $.

  ${
    $d a b c $.
    $( When two ordinals (both at least as large as two) are raised to the same
       power, ordering of the powers is not equivalent to the ordering of the
       bases.  Remark 3.26 of [Schloeder] p. 11.  (Contributed by RP,
       4-Feb-2025.) $)
    oenord1 $p |- E. a e. ( On \ 2o ) E. b e. ( On \ 2o )
                     E. c e. ( On \ 1o ) -. ( a e. b <->
                       ( a ^o c ) e. ( b ^o c ) ) $=
      ( c2o c3o wcel com coe co wb wn con0 c1o wrex mpbir2an wceq notbid rspcev
      cv c0 wel cdif oenord1ex 2on cpr 1oelpr df2o3 eleqtrri 3on ctp 1oex tpid2
      ondif2 df3o2 omelon peano1 ondif1 oveq2 eleq12d bibi2d eleq2 oveq1 eleq2d
      mpan bibi12d rexbidv sylancr eleq1 eleq1d 2rexbidv ax-mp ) DEFZDGHIZEGHIZ
      FZJZKZABUAZASZCSZHIZBSZVTHIZFZJZKZCLMUBZNBLDUBZNZAWHNZUCVQDWHFZDWBFZDVTHI
      ZWCFZJZKZCWGNZBWHNZWJWKDLFMDFUDMTMUEDUFUGUHDUMOVQEWHFZVLWMEVTHIZFZJZKZCWG
      NZWRWSELFMEFUIMTMDUJETMDUKULUNUHEUMOGWGFZVQXDXEGLFTGFUOUPGUQOXCVQCGWGVTGP
      ZXBVPXFXAVOVLXFWMVMWTVNVTGDHURVTGEHURUSUTQRVDWQXDBEWHWBEPZWPXCCWGXGWOXBXG
      WLVLWNXAWBEDVAXGWCWTWMWBEVTHVBVCVEQVFRVGWIWRADWHVSDPZWFWPBCWHWGXHWEWOXHVR
      WLWDWNVSDWBVHXHWAWMWCVSDVTHVBVIVEQVJRVGVK $.
  $}

  ${
    $d a b $.
    $( Ordinal addition, multiplication, and exponentiation do not generally
       commute.  Theorem 4.1 of [Schloeder] p. 11.  (Contributed by RP,
       30-Jan-2025.) $)
    oaomoencom $p |- ( E. a e. On E. b e. On -. ( a +o b ) = ( b +o a )
                   /\ E. a e. On E. b e. On -. ( a .o b ) = ( b .o a )
                   /\ E. a e. On E. b e. On -. ( a ^o b ) = ( b ^o a ) ) $=
      ( coa co wceq con0 wrex comu coe c1o com wcel omelon oveq2 eqeq12d notbid
      wn oveq1 rspcev c2o oancom neii 1on mpan rexbidv sylancr ax-mp wne pm3.2i
      cv wa c0 peano1 oaord1 biimpa elneq mp2b 2omomeqom csuc df-2o omsuc mp2an
      oveq2i om1 oveq1i 3eqtri neeq12i mpbir 2on 1onn mp1i omordi eqeltrrd 2onn
      imp cpr 1oelpr df2o3 eleqtrri nnoeomeqom oesuc oe1 3pm3.2i ) AUJZBUJZCDZW
      EWDCDZEZQZBFGZAFGZWDWEHDZWEWDHDZEZQZBFGZAFGZWDWEIDZWEWDIDZEZQZBFGZAFGZJKC
      DZKJCDZEZQZWKXDXEUAUBXGJFLZJWECDZWEJCDZEZQZBFGZWKUCKFLZXGXMMXLXGBKFWEKEZX
      KXFXOXIXDXJXEWEKJCNWEKJCROPSUDWJXMAJFWDJEZWIXLBFXPWHXKXPWFXIWGXJWDJWECRWD
      JWECNOPUESUFUGTKHDZKTHDZEZQZWQXQXRXQXRUHKKKCDZUHZXNXNUKZULKLZUKZKYALZYBYC
      YDXNXNMMUIUMUIZYCYDYFKKUNUOKYAUPUQXQKXRYAURXRKJUSZHDZKJHDZKCDZYATYHKHUTVC
      XNXHYIYKEMUCKJVAVBYJKKCXNYJKEZMKVDZUGVEVFVGVHUBXTTFLZTWEHDZWETHDZEZQZBFGZ
      WQVIXNXTYSMYRXTBKFXOYQXSXOYOXQYPXRWEKTHNWEKTHROPSUDWPYSATFWDTEZWOYRBFYTWN
      YQYTWLYOWMYPWDTWEHRWDTWEHNOPUESUFUGTKIDZKTIDZEZQZXCUUAUUBUUAUUBUHKKKHDZUH
      ZYEJKLZUKZKUUELUUFYEUUGYGVJUIUUHYJKUUEXNYLUUHMYMVKYEUUGYJUUELJKKVLVOVMKUU
      EUPUQUUAKUUBUUETKLJTLUUAKEVNJULJVPTVQVRVSTVTVBUUBKYHIDZKJIDZKHDZUUETYHKIU
      TVCXNXHUUIUUKEMUCKJWAVBUUJKKHXNUUJKEMKWBUGVEVFVGVHUBUUDYNTWEIDZWETIDZEZQZ
      BFGZXCVIXNUUDUUPMUUOUUDBKFXOUUNUUCXOUULUUAUUMUUBWEKTINWEKTIROPSUDXBUUPATF
      YTXAUUOBFYTWTUUNYTWRUULWSUUMWDTWEIRWDTWEINOPUESUFUGWC $.
  $}

  $( Ordinal two raised to two to the zeroth power is not the same as two
     squared then raised to the zeroth power.  (Contributed by RP,
     30-Jan-2025.) $)
  oenassex $p |- -. ( 2o ^o ( 2o ^o (/) ) ) = ( ( 2o ^o 2o ) ^o (/) ) $=
    ( c1o c2o wcel c0 coe co wn cpr 1oelpr df2o3 eleqtrri wne elneq df-ne necom
    wceq con0 2on oe0 ax-mp oveq2i oe1 eqtri wa pm3.2i oecl mp2b eqeq12i notbii
    3bitr4i sylib ) ABCZBBDEFZEFZBBEFZDEFZPZGZADAHBIJKULABLZURABMBALBAPZGUSURBA
    NABOUQUTUNBUPAUNBAEFZBUMABEBQCZUMAPRBSTUAVBVABPRBUBTUCVBVBUDUOQCUPAPVBVBRRU
    EBBUFUOSUGUHUIUJUKT $.

  ${
    $d a b c $.
    $( Ordinal exponentiation is not associative.  Remark 4.6 of [Schloeder]
       p. 14.  (Contributed by RP, 30-Jan-2025.) $)
    oenass $p |- E. a e. On E. b e. On E. c e. On
                    -. ( a ^o ( b ^o c ) ) = ( ( a ^o b ) ^o c ) $=
      ( c2o c0 coe co wceq wn cv con0 wrex wcel 2on oveq2 eqeq12d notbid rspcev
      oveq1 rexbidv oenassex 0elon oveq2d mpan oveq1d sylancr ax-mp ) DDEFGZFGZ
      DDFGZEFGZHZIZAJZBJZCJZFGZFGZUNUOFGZUPFGZHZIZCKLZBKLZAKLZUAUMDKMZDUQFGZDUO
      FGZUPFGZHZIZCKLZBKLZVENUMVFDDUPFGZFGZUJUPFGZHZIZCKLZVMNEKMUMVSUBVRUMCEKUP
      EHZVQULVTVOUIVPUKVTVNUHDFUPEDFOUCUPEUJFOPQRUDVLVSBDKUODHZVKVRCKWAVJVQWAVG
      VOVIVPWAUQVNDFUODUPFSUCWAVHUJUPFUODDFOUEPQTRUFVDVMADKUNDHZVCVLBKWBVBVKCKW
      BVAVJWBURVGUTVIUNDUQFSWBUSVHUPFUNDUOFSUEPQTTRUFUG $.
  $}

  $( For terms of the form of a power of omega times a nonzero natural number,
     ordering of the exponents implies ordering of the terms.  Lemma 5.1 of
     [Schloeder] p. 15.  (Contributed by RP, 30-Jan-2025.) $)
  cantnftermord $p |- ( ( ( A e. On /\ B e. On )
                     /\ ( C e. ( _om \ 1o ) /\ D e. ( _om \ 1o ) ) ) ->
                     ( A e. B ->
                      ( ( _om ^o A ) .o C ) e. ( ( _om ^o B ) .o D ) ) ) $=
    ( con0 wcel wa com c1o cdif coe co comu wss syl omelon a1i imp c0 oecl csuc
    c2o simplll onsuc simpllr ondif2 mpbir2an wi onsucss ad2antlr oeword biimpa
    1onn syl31anc sylancom omsson ssdif ax-mp sseli ondif1 sylib adantl anim12i
    adantr anass sylibr omword1 sstrd jctil peano1 oen0 sylancl simplrl eldifad
    w3a omordi syl1111anc wceq oesuc eleqtrrd sseldd ex ) AEFZBEFZGZCHIJZFZDWFF
    ZGZGZABFZHAKLZCMLZHBKLZDMLZFWJWKGZHAUAZKLZWOWMWPWRWNWOWPWQEFZWDHEUBJFZWQBNZ
    WRWNNZWPWCWSWCWDWIWKUCZAUDOWCWDWIWKUEWTWPWTHEFZIHFPUMHUFUGQWJWKXAWDWKXAUHWC
    WIBAUIUJRWSWDWTVOXAXBWQBHUKULUNWPWNEFZDEFZGSDFZGZWNWONWPXEXFXGGZGZXHWJXJWKW
    EXEWIXIWCWDXDXEXDWEPQHBTUOWHXIWGWHDEIJZFXIWFXKDHENWFXKNUPHEIUQURUSDUTVAVBVC
    VDXEXFXGVEVFWNDVGOVHWPWMWLHMLZWRWPXDWLEFZSWLFZCHFZWMXLFZXDWPPQWPXDWCGZXMWPW
    CXDXCPVIZHATOWPXQSHFXNXRVJHAVKVLWPCHIWEWGWHWKVMVNXDXMGXNGXOXPCHWLVPRVQWPXQW
    RXLVRXRHAVSOVTWAWB $.

  ${
    $d ph x y $.  $d A x y $.  $d F y $.  $d M x $.  $d X x $.
    cantnfub.0 $e |- ( ph -> X e. On ) $.
    cantnfub.n $e |- ( ph -> N e. _om ) $.
    cantnfub.a $e |- ( ph -> A : N -1-1-> X ) $.
    cantnfub.m $e |- ( ph -> M : N --> _om ) $.
    cantnfub.f $e |- F = ( x e. X |-> if ( x e. ran A ,
                                             ( M ` ( `' A ` x ) ) , (/) ) ) $.
    $( Given a finite number of terms of the form
       ` ( ( _om ^o ( A `` n ) ) .o ( M `` n ) ) ` with distinct exponents, we
       may order them from largest to smallest and find the sum is less than
       ` ( _om ^o X ) ` when ` ( A `` n ) ` is less than ` X ` and
       ` ( M `` n ) ` is less than ` _om ` .  Lemma 5.2 of [Schloeder] p. 15.
       (Contributed by RP, 31-Jan-2025.) $)
    cantnfub $p |- ( ph -> ( F e. dom ( _om CNF X ) /\
                              ( ( _om CNF X ) ` F ) e. ( _om ^o X ) ) ) $=
      ( vy com co wcel cfv c0 wa cfn ccnf cdm coe wf cfsupp wbr cv crn ccnv cif
      ad2antrr wf1 f1f1orn syl f1ocnvdm sylancom ffvelcdmd wn peano1 a1i ifclda
      wf1o fmptd csupp wfn f1fn con0 nnon onfin 3syl mpbird fnfi rnfi cdif wceq
      jca eldifi adantl weq eleq1w 2fveq3 ifbieq1d fvex 0ex ifex fvmpt iffalsed
      eldifn eqtrd suppss ssfid wfun cmap omelon elmapd funisfsupp syl3anc eqid
      wb ffund cantnfs mpbir2and cantnff ) ADNGUAOZUBZPZDXDQNGUCOZPAXFGNDUDZDRU
      EUFZABGBUGZCUHZPZXJCUIZQZEQZRUJZNDAXJGPZSZXLXORNXRXLSZFNXNEAFNEUDXQXLKUKX
      RXLFXKCVBZXNFPXSFGCULZXTAYAXQXLJUKFGCUMUNFXKXJCUOUPUQRNPZXRXLURSUSUTVALVC
      ZAXIDRVDOZTPZAXKYDACFVEZFTPZSCTPXKTPAYFYGAYAYFJFGCVFUNAYGFNPZIAYHFVGPYGYH
      WSIFVHFVIVJVKVPFCVLCVMVJAGNMDXKRYCAMUGZGXKVNPZSZYIDQZYIXKPZYIXMQZEQZRUJZR
      YKYIGPZYLYPVOYJYQAYIGXKVQVRBYIXPYPGDBMVSXLYMXOYORBMXKVTXJYIEXMWAWBLYMYORY
      NEWCWDWEWFUNYKYMYORYJYMURAYIGXKWHVRWGWIWJWKADWLDNGWMOZPZYBXIYEWSAGNDYCWTA
      YSXHYCANGDVGVGNVGPAWNUTZHWOVKYBAUSUTDYRNRWPWQVKANGXEDXEWRZYTHXAXBZAXEXGDX
      DANGXEUUAYTHXCUUBUQVP $.
  $}

  ${
    $d ph x $.  $d A x $.  $d M x $.
    cantnfub2.n $e |- ( ph -> N e. _om ) $.
    cantnfub2.a $e |- ( ph -> A : N -1-1-> On ) $.
    cantnfub2.m $e |- ( ph -> M : N --> _om ) $.
    cantnfub2.f $e |- F = ( x e. suc U. ran A |-> if ( x e. ran A ,
                                             ( M ` ( `' A ` x ) ) , (/) ) ) $.
    $( Given a finite number of terms of the form
       ` ( ( _om ^o ( A `` n ) ) .o ( M `` n ) ) ` with distinct exponents, we
       may order them from largest to smallest and find the sum is less than
       ` ( _om ^o suc U. ran A ) ` when ` ( M `` n ) ` is less than ` _om ` .
       Lemma 5.2 of [Schloeder] p. 15.  (Contributed by RP, 9-Feb-2025.) $)
    cantnfub2 $p |- ( ph -> ( suc U. ran A e. On /\
                       F e. dom ( _om CNF suc U. ran A ) /\
                       ( ( _om CNF suc U. ran A ) ` F )
                       e. ( _om ^o suc U. ran A ) ) ) $=
      ( crn con0 wcel com co cfn wss wf1 syl syl2anc cuni csuc ccnf cdm cfv coe
      wa w3a wfn f1fn nnfi fnfi rnfi f1f frnd ssonuni sylc onsuc onsucuni f1ssr
      wf cantnfub 3anass sylanbrc ) ACKZUAZUBZLMZDNVGUCOZUDMZDVIUENVGUFOMZUGVHV
      JVKUHAVFLMZVHAVEPMZVELQZVLACPMZVMACFUIZFPMZVOAFLCRZVPHFLCUJSAFNMVQGFUKSFC
      ULTCUMSAFLCAVRFLCVAHFLCUNSUOZVEPUPUQVFURSZABCDEFVGVTGAVRVEVGQZFVGCRHAVNWA
      VSVEUSSFLVGCUTTIJVBVHVJVKVCVD $.
  $}

  ${
    $d x y A $.  $d x B y $.  $d ch x y $.
    bropabg.xA $e |- ( x = A -> ( ph <-> ps ) ) $.
    bropabg.yB $e |- ( y = B -> ( ps <-> ch ) ) $.
    bropabg.R $e |- R = { <. x , y >. | ph } $.
    $( Equivalence for two classes related by an ordered-pair class
       abstraction.  A generalization of ~ brslts .  (Contributed by RP,
       26-Sep-2024.) $)
    bropabg $p |- ( A R B <-> ( ( A e. _V /\ B e. _V ) /\ ch ) ) $=
      ( wbr cvv wcel wa bropaex12 brabg biadanii ) FGHLFMNGMNOCADEFGHKPABCDEFGM
      MHIJKQR $.
  $}

  ${
    $d A a b c x y $.  $d B a b c x y $.  $d C a b c x y $.  $d F a b c x y $.
    $( A Cantor normal form which sums to less than a certain power has only
       zeros for larger components.  (Contributed by RP, 3-Feb-2025.) $)
    cantnfresb $p |- ( ( ( A e. ( On \ 2o ) /\ B e. On )
                      /\ ( C e. On /\ F e. dom ( A CNF B ) ) ) ->
                       ( ( ( A CNF B ) ` F ) e. ( A ^o C )
                   <-> A. x e. ( B \ C ) ( F ` x ) = (/) ) ) $=
      ( vy vc con0 wcel wa co cfv c0 wceq wral wi c1o wb adantr ad2antrr va c2o
      vb cdif ccnf cdm coe wss cif cmpt wel wrex copab wbr cep wiso eqid eldifi
      cv simpr cantnf wf cfsupp ondif2 simprbi dif20el fmpttd sniffsupp cantnfs
      ifcld mpbir2and isorel syl12anc adantrl cvv fvexd syl comu csn cxp simplr
      epelg coa fconst6g fczfsuppd fczsupp0 0ss eqsstri a1i 0ex fvconst2 ifeq2d
      csupp mpteq2ia eqcomi cantnfp1 simprd sylan om1 cantnf0 oveq12d oa0 eqtrd
      adantrr eleq2d 3bitrrd fveq1 eleq1d imbi2d ralbidv anbi12d rexbidv eqeq2d
      oecl weq eqeq1 ifbid 1oex ifex fvmpt biimpd simpl sylbid expimpd iffalsed
      adantl fveqeq2 wn simpllr syl2anc notbid word eloni adantld 3syld adantll
      ex cun raleqdv imp exp32 adantrd imp31 eqeq1d fveq2 iftrue sylan9eqr el1o
      bropabg eleq12d jctild wne neneqd noel pm2.21i syl6 ralsng anbi2d biimprd
      pm2.61ine csuc anim1i pm3.31 eldif onelon ontri1 con2bid onsssuc pm5.32da
      bitrid imim1d syl2an ordeldifsucon biimpa ordirr eleq1 syl5ibcom sylc a2d
      con2d ralimdv2 ralun undif3 snssd ssequn1 sylib orddif 3syl eqcomd eqtrid
      difeq12d syld expl expdimp impd rexlimdva biimtrid adantlrr ssdif0 biimpi
      mpbid ral0 mpbiri a1i13 wo ordtri2or syl2anr mpjaod simplrr simpld rspccv
      simplrl suppss cantnflt2 impbid ) BHUBUDIZCHIZJZDHIZEBCUEKZUFZIZJZJZEUXTL
      ZBDUGKZIZAUSZELZMNZACDUDZOZUYDDCIZUYGUYLPZCDUHZUYDUYMUYNUYDUYMJZUYGEFCFUS
      ZDNZQMUIZUJZGUSZUAUSZLZVUAUCUSZLZIZGAUKZUYHVUBLZUYHVUDLZNZPZACOZJZGCULZUA
      UCUMZUNZUYLUYPVUPUYEUYTUXTLZUOUNZUYEVUQIZUYGUYDVUPVURRZUYMUXRUYBVUTUXSUXR
      UYBJUYABCUGKZVUOUOUXTUPZUYBUYTUYAIZVUTUXRVVBUYBUXRUAUCGABCUYAVUOUYAUQZUXP
      BHIZUXQBHUBURZSZUXPUXQUTZVUOUQZVASUXRUYBUTUXRVVCUYBUXRVVCCBUYTVBUYTMVCUNU
      XRFCUYSBUXPUYSBIUXQUYQCIZUXPUYRQMBUXPVVEQBIZBVDVEZBVFZVJTVGUXRFQUYTCHBDMV
      VHUXPMBIZUXQVVMSZUYTUQZVHUXRBCUYAUYTVVDVVGVVHVIVKSUYAVVAEUYTVUOUOUXTVLVMV
      NSUYPVUQVOIVURVUSRUYPUYTUXTVPUYEVUQVOWBVQUXRUYCUYMVUSUYGRZUXRUXSUYMVVQPUY
      BUXRUXSUYMVVQUXRUXSUYMJZJZVUQUYFUYEVVSVUQUYFQVRKZCMVSVTZUXTLZWCKZUYFUXRUY
      MVUQVWCNZUXSUXRUYMJZVVCVWDVWEFBCUYAUYTVWADQVVDUXPVVEUXQUYMVVFTUXPUXQUYMWA
      UXRVWAUYAIZUYMUXRVWFCBVWAVBZVWAMVCUNUXPVWGUXQUXPVVNVWGVVMCMBWDVQSUXRCHBMV
      VHVVOWEUXRBCUYAVWAVVDVVGVVHVIVKSUXRUYMUTUXPVVKUXQUYMVVLTVWAMWMKZDUHVWEVWH
      MDCMWFDWGWHWIFCUYRQUYQVWALZUIZUJUYTFCVWJUYSVVJUYRVWIMQCMUYQWJWKWLWNWOWPWQ
      VNUXRUXSVWCUYFNUYMUXRUXSJZVWCUYFMWCKZUYFVWKVVTUYFVWBMWCVWKUYFHIZVVTUYFNUX
      RVVEUXSVWMVVGBDXNWRZUYFWSVQUXRVWBMNUXSUXRBCUYAVVDVVGVVHVVOWTSXAVWKVWMVWLU
      YFNVWNUYFXBVQXCXDXCXEUUAUUBUUCXFUXRUXSUYMVUPUYLPUYBVUPEVOIUYTVOIJZVUAELZV
      UAUYTLZIZVUGUYIUYHUYTLZNZPZACOZJZGCULZJVWKUYMJZUYLVUNVWPVUEIZVUGUYIVUINZP
      ZACOZJZGCULVXDUAUCEUYTVUOVUBENZVUMVXJGCVXKVUFVXFVULVXIVXKVUCVWPVUEVUAVUBE
      XGXHVXKVUKVXHACVXKVUJVXGVUGVXKVUHUYIVUIUYHVUBEXGUUDXIXJXKXLVUDUYTNZVXJVXC
      GCVXLVXFVWRVXIVXBVXLVUEVWQVWPVUAVUDUYTXGXEVXLVXHVXAACVXLVXGVWTVUGVXLVUIVW
      SUYIUYHVUDUYTXGXMXIXJXKXLVVIUUIVXEVXDUYLVWOVXEVXCUYLGCVXEVUACIZJVWRVXBUYL
      VXEVXMVWRVXBUYLPZVXEVXMVWRJZVUADNZDELZMNZJZVXPUYJADVSZOZJZVXNVXOVXSPZVXEV
      YCVUADVXPVXMVWRVXSVXPVXMJZVWRVXQQIZVXSVYDVWPVXQVWQQVXPVWPVXQNVXMVUADEUUES
      VXMVXPVWQVXPQMUIZQFVUAUYSVYFCUYTFGXOUYRVXPQMUYQVUADXPXQVVPVXPQMXRWJXSXTZV
      XPQMUUFUUGUUJVYDVYEVXRVXPVYDVYEVXRVYEVXRRVYDVXQUUHWIYAVXPVXMYBUUKYCYDVUAD
      UULZVXOVWPMIZVXSVYHVXMVWRVYIVYHVXMJZVWRVYIVYJVWQMVWPVYJVWQVYFMVXMVWQVYFNV
      YHVYGYFVYJVXPQMVYJVUADVYHVXMYBUUMYEXCXEYAYDVYIVXSVWPUUNUUOUUPUUTWIUYMVXSV
      YBPVWKUYMVYBVXSUYMVYAVXRVXPUYJVXRADCUYHDMEYGUUQUURUUSYFVXEVXPVYAVXNVXEVXP
      JZVYAJZVXBUYJACDUVAZUDZOZUYLVYKVXBVYOPZVYAVXEUXQUXSJZVXPVYPVWKVYQUYMUXRUX
      QUXSVVHUVBSVYQVXPJZVXAUYJACVYNVYRUYHCIZVXAPZVYSVUGJZVWTPZUYHVYNIZVWTPWUCU
      YJPVYTWUBPVYRVYSVUGVWTUVCWIVYRWUCWUAVWTVYRWUCWUAWUCVYSUYHVYMIZYHZJVYRWUAU
      YHCVYMUVDVYRVYSWUEVUGVYRVYSJZVUGDUYHIZUYHDUHZYHWUEWUFVUADUYHVYQVXPVYSWAXH
      WUFWUHWUGWUFUYHHIZUXSWUHWUGYHZRVYRUXQVYSWUIVYQUXQVXPUXQUXSYBSZCUYHUVEZWRZ
      UXQUXSVXPVYSYIZUYHDUVFYJUVGWUFWUHWUDWUFWUIUXSWUHWUDRWUMWUNUYHDUVHYJYKXFUV
      IUVJYAUVKVYRWUCVWTUYJVYRWUCVWTUYJPVYRWUCJZVWTUYJWUOVWSMUYIWUOVWSUYHDNZQMU
      IZMWUOVYSVWSWUQNWUCVYSVYRUYHCVYMURZYFFUYHUYSWUQCUYTFAXOUYRWUPQMUYQUYHDXPX
      QVVPWUPQMXRWJXSXTVQWUOWUPQMWUOUYHYLZVYSWUGJZWUPYHZWUOWUIWUSVYRUXQVYSWUIWU
      CWUKWURWULUVLUYHYMVQVYRWUCWUTVYRCYLZUXSWUCWUTRUXQWVBUXSVXPCYMZTUXQUXSVXPW
      ACDUYHUVMYJUVNWUSWUGWVAVYSWUSWUPWUGWUSAAUKZYHWUPWUJUYHUVOWUPWVDWUGUYHDUYH
      UVPYKUVQUVTYNUVRYEXCXMYAYQUVSYOUWAWRSVYLVYOUYLVYLVYOJUYJAVXTVYNYRZOZUYLVY
      AVYOWVFVYKUYJAVXTVYNUWBYPVYKWVFUYLRVYAVYOVYKUYJAWVEUYKVXEWVEUYKNZVXPUXSUY
      MWVGUXRVVRWVEVXTCYRZVYMVXTUDZUDUYKVXTCVYMUWCVVRWVHCWVIDVVRVXTCUHWVHCNVVRD
      CUXSUYMUTUWDVXTCUWEUWFVVRDWVIVVRUXSDYLZDWVINUXSUYMYBDYMZDUWGUWHUWIUWKUWJY
      PSYSTUXAYQUWLUWMYOUWNUWOUWPYNUWQUWRYCYQUYDUYOUYGUYLUYOUYLUYJAMOUYJAUXBUYO
      UYJAUYKMUYOUYKMNCDUWSUWTYSUXCUXDUYCWVJWVBUYMUYOUXEUXRUXSWVJUYBWVKSUXQWVBU
      XPWVCYFDCUXFUXGUXHUYDUYLUYGUYDUYLJZBCDUYAEVVDUXRVVEUYCUYLVVGTUXPUXQUYCUYL
      YIUXRUXSUYBUYLUXIUXRVVNUYCUYLVVOTUXRUXSUYBUYLUXLWVLCBFEDMUYDCBEVBZUYLUYDW
      VMEMVCUNZUXRUYCWVMWVNJZUXRUYBWVOUXSUXRUYBWVOUXRBCUYAEVVDVVGVVHVIYAYNYTUXJ
      SWVLUYQUYKIZUYQELMNZUYLWVPWVQPUYDUYJWVQAUYQUYKUYHUYQMEYGUXKYFYTUXMUXNYQUX
      O $.
  $}

  ${
    $d A a b c d f $.
    $( For every ordinal, ` A ` , there is a an ordinal exponent ` b ` such
       that ` A ` is less than ` ( _om ^o b ) ` and for every ordinal at least
       as large as ` b ` there is a unique Cantor normal form, ` f ` , with
       zeros for all the unnecessary higher terms, that sums to ` A ` .
       Theorem 5.3 of [Schloeder] p. 16.  (Contributed by RP, 3-Feb-2025.) $)
    cantnf2 $p |- ( A e. On -> E. b e. On A. c e. ( On \ b )
                      E! f e. dom ( _om CNF c )
                      ( ( A e. ( _om ^o b ) /\ f finSupp (/) )
                     /\ ( ( ( _om CNF b ) ` ( f |` b ) ) = A
                        /\ ( ( _om CNF c ) ` f ) = A ) ) ) $=
      ( va vd con0 wcel com cv co c0 wbr wa cfv wceq syl omelon a1i ad2antrr wn
      coe wrex cfsupp cres ccnf cdm wreu cdif wral onexoegt w3a wss eldif wb wi
      wel simp2 pm3.2 ontri1 syl6 pm5.32d bitr4id crn simplr breq2d wfun simprl
      wf1o eqid cantnff1o f1ofun funbrfvb sylancom bitr4d reubidva simpl2 jctir
      3jca peano1 simprr oewordi sylc simpl3 sseldd dff1o5 simpr sylbi eleqtrrd
      wf1 ccnv wfn dff1o2 funcnv3 sylib rspcdv2 wf cantnfs cmpt eqeltrd c2o c1o
      mpbid 1onn ondif2 mpbir2an syl22anc r19.21bi simpllr adantr simpld sselda
      ffvelcdmd fmpttd simprbda feqresmpt fsuppres eqbrtrrd mpbir2and cantnfres
      cantnfresb fveq2d feqmptd eqtrd pm4.71rd 3an4anass bitrdi sylbid ralrimiv
      3eqtr4d ex 3exp reximdvai mpd ) AGHZAICJZUBKZHZCGUCYRBJZLUDMZNYSYPUEZIYPU
      FKZOZAPZYSIDJZUFKZOZAPZNNZBUUFUGZUHZDGYPUIZUJZCGUCCAUKYOYRUUMCGYOYPGHZYRU
      UMYOUUNYRULZUUKDUULUUOUUEUULHZUUEGHZYPUUEUMZNZUUKUUOUUPUUQDCUQUAZNUUSUUEG
      YPUNUUOUUQUURUUTUUOUUQUUNUUQNZUURUUTUOUUOUUNUUQUVAUPYOUUNYRURUUNUUQUSQYPU
      UEUTVAVBVCUUOUUSUUKUUOUUSNZUUHBUUJUHZUUKUVBYSEJZUUFMZBUUJUHZUVCEAUUFVDZUV
      BUVDAPZNZUVEUUHBUUJUVIYSUUJHZNZUVEYSAUUFMZUUHUVKUVDAYSUUFUVBUVHUVJVEVFUVI
      UVJUUFVGZUUHUVLUOUVKUUJIUUEUBKZUUFVIZUVMUVKIUUEUUJUUJVJZIGHZUVKRSUVBUUQUV
      HUVJUUOUUQUURVHZTVKUUJUVNUUFVLQYSAUUFVMVNVOVPUVBAUVNUVGUVBYQUVNAUVBUUNUUQ
      UVQULZLIHZNUURYQUVNUMUVBUVSUVTUVBUUNUUQUVQYOUUNYRUUSVQZUVRUVQUVBRSZVSVTVR
      UUOUUQUURWAZYPUUEIWBWCYOUUNYRUUSWDZWEUVBUVOUVGUVNPZUVBIUUEUUJUVPUWBUVRVKZ
      UVOUUJUVNUUFWJZUWENUWEUUJUVNUUFWFUWGUWEWGWHQWIUVBUUFWKVGZUVFEUVGUJUVBUVOU
      WHUWFUVOUUFUUJWLZUWHUWEULUWHUUJUVNUUFWMUWIUWHUWEURWHQBEUUFWNWOWPUVBUUHUUI
      BUUJUVBUVJNZUUHYRYTUUDULZUUHNUUIUWJUUHUWKUWJUUHUWKUWJUUHNZYRYTUUDUVBYRUVJ
      UUHUWDTZUWLUUEIYSWQZYTNZYTUWLUVJUWOUVBUVJUUHVEZUWLIUUEUUJYSUVPUVQUWLRSZUV
      BUUQUVJUUHUVRTZWRXCUWNYTWGQZUWLUUCUUGAUWLFYPFJZYSOZWSZUUBOFUUEUXAWSZUUFOU
      UCUUGUWLIYPUUEUUBUGZUUJFUXAUXDVJZUWQUVBUUNUVJUUHUWATZUWRUVBUURUVJUUHUWCTZ
      UWLUXALPZFUUEYPUIZUWLUUGYQHZUXHFUXIUJZUWLUUGAYQUWJUUHWGZUWMWTUWLIGXAUIHZU
      UQUUNUVJUXJUXKUOUXMUWLUXMUVQXBIHRXDIXEXFSUWRUXFUWPFIUUEYPYSYAXGXCXHUVTUWL
      VTSZUVPUWLUXBUXDHYPIUXBWQUXBLUDMUWLFYPUXAIUWLFCUQZNZUUEIUWTYSUXPUWNYTUXPU
      VJUWOUVBUVJUUHUXOXIUXPIUUEUUJYSUVPUVQUXPRSUWJUUQUUHUXOUVBUUQUVJUVRXJTWRXC
      XKUWLYPUUEUWTUXGXLXMXNUWLUUAUXBLUDUWLFUUEIYPYSUWJUWNUUHUVBUVJUWNYTUVBIUUE
      UUJYSUVPUWBUVRWRXOXJZUXGXPZUWLYSIYPLUWSUXNXQXRUWLIYPUXDUXBUXEUWQUXFWRXSXT
      UWLUUAUXBUUBUXRYBUWLYSUXCUUFUWLFUUEIYSUXQYCYBYJUXLYDVSYKYEYRYTUUDUUHYFYGV
      PXCYKYHYIYLYMYN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Natural addition of Cantor normal forms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( If ` C ` is between ` A ` (inclusive) and ` ( A +o B ) ` (exclusive),
       there is an ordinal which equals ` C ` when summed to ` A ` .  This is a
       slightly different statement than ~ oawordex or ~ oawordeu .
       (Contributed by RP, 7-Jan-2025.) $)
    oawordex2 $p |- ( ( ( A e. On /\ B e. On )
                      /\ ( A C_ C /\ C e. ( A +o B ) ) ) ->
                      E. x e. B ( A +o x ) = C ) $=
      ( con0 wcel wa wss coa co cv wceq wrex simprl wb simpll oacl simpr simprr
      adantr onelon syl2an oawordex syl2anc mpbid eqeltrd simpllr oaord syl3anc
      mpbird reximssdv ) BEFZCEFZGZBDHZDBCIJZFZGZGZBAKZIJZDLZVBACEUSUOVBAEMZUNU
      OUQNUSULDEFZUOVCOULUMURPZUNUPEFUQVDURBCQUOUQRUPDUAUBABDUCUDUEUSUTEFZVBGZG
      ZUTCFZVAUPFZVHVADUPUSVFVBSZUSUQVGUNUOUQSTUFVHVFUMULVIVJOUSVFVBNULUMURVGUG
      USULVGVETUTCBUHUIUJVKUK $.
  $}

  ${
    $d A x $.  $d B x $.
    $( If an ordinal, ` B ` , is in a half-open interval between some ` A ` and
       the next limit ordinal, ` B ` is the sum of the ` A ` and some natural
       number.  This weakens the antecedent of ~ nnawordex .  (Contributed by
       RP, 7-Jan-2025.) $)
    nnawordexg $p |- ( ( A e. On /\ A C_ B /\ B e. ( A +o _om ) )
                       -> E. x e. _om ( A +o x ) = B ) $=
      ( con0 wcel wss com coa co w3a wa cv wceq wrex simp1 omelon a1i oawordex2
      3simpc syl21anc ) BDEZBCFZCBGHIEZJZUAGDEZUBUCKBALHICMAGNUAUBUCOUEUDPQUAUB
      UCSABGCRT $.
  $}

  $( Closure law for ordinal successor.  (Contributed by RP, 8-Jan-2025.) $)
  succlg $p |- ( ( A e. B /\
               ( B = (/) \/ ( B = ( _om .o C ) /\ C e. ( On \ 1o ) ) ) ) ->
               suc A e. B ) $=
    ( wcel c0 wceq com comu co con0 c1o cdif wa wo csuc eleq2 wlim cvv ad2antll
    wb noel pm2.21i biimtrdi com12 simpl eldifi limom pm3.2i a1i ondif1 simprbi
    omex omlimcl2 syl21anc limeq ad2antrl mpbird limsuc syl mpbid ex jaod imp )
    ABDZBEFZBGCHIZFZCJKLDZMZNAOBDZVDVEVJVIVEVDVJVEVDAEDZVJBEAPVKVJAUAUBUCUDVDVI
    VJVDVIMZVDVJVDVIUEVLBQZVDVJTVLVMVFQZVLCJDZGRDZGQZMZECDZVNVHVOVDVGCJKUFSVRVL
    VPVQULUGUHUIVHVSVDVGVHVOVSCUJUKSCGRUMUNVGVMVNTVDVHBVFUOUPUQBAURUSUTVAVBVC
    $.

  ${
    $d A x y $.
    $( A limit ordinal is either the proper class of ordinals or some nonzero
       product with omega.  (Contributed by RP, 8-Jan-2025.) $)
    dflim5 $p |- ( Lim A <-> ( A = On \/
                               E. x e. ( On \ 1o ) A = ( _om .o x ) ) ) $=
      ( vy wlim con0 wceq wa wo com co syl limeq coa c0 omelon wi adantr adantl
      wcel wn cv comu c1o cdif wrex word limord ordeleqon biimpi pm4.71ri andir
      orcomd bitri limon mpbiri pm4.71i orbi1i wne w3a simpl a1i id peano1 3jca
      ne0ii omeulem1 3syl biimprd simplr wb on0eln0 necon1bd imp jca oveq2d om0
      nnlim mp1i eqtrd oveq1d nna0r mtbird ex cuni csuc cvv ovex nlimsucg nnord
      orduniorsuc w3o 3ianor df-lim xchnxbir sylib pm2.24d nne a1i13 pm2.21 mpd
      3jaod ord omcl sylancr nnon onuni oasuc syl2anc jaod con2d anor imbitrrdi
      orim1d syl9 com13 3imp simp2 anim12i ondif1 sylibr simpr simpl3 oa0 mpdan
      3eqtr3d 3exp expdimp rexlimdv expimpd reximdv2 eldifi limom pm3.2i mpanl2
      eqeltrd omlimcl2 sylbi mpbird rexlimiva impbii orbi2i 3bitr2i ) BDZBEFZUU
      CGZBESZUUCGZHZUUDUUGHUUDBIAUAZUBJZFZAEUCUDZUEZHUUCUUDUUFHZUUCGUUHUUCUUNUU
      CBUFZUUNBUGUUOUUFUUDUUOUUFUUDHBUHUIULKUJUUDUUFUUCUKUMUUDUUEUUGUUDUUCUUDUU
      CEDUNBELUOUPUQUUGUUMUUDUUGUUMUUGUUJCUAZMJZBFZCIUEZAEUEZUUMUUGUUFIESZUUFIN
      URZUSUUTUUFUUCUTUUFUVAUUFUVBUVAUUFOVAUUFVBUVBUUFNIVCVEVAVDACIBVFVGUUGUUSU
      UKAEUULUUGUUIESZUUSUUIUULSZUUKGZUUGUVCGUURUVECIUUGUVCUUPISZUURUVEPUUGUVCU
      VFGZUURUVEUUGUVGUURUSZNUUISZUUPNFZGZUVEUUGUVGUURUVKUUCUVGUURUVKPPUUFUURUV
      GUUCUVKUURUUCUUQDZUVGUVKUURUVLUUCUUQBLVHUVGUVLUVITZUVJTZHZTUVKUVGUVOUVLUV
      GUVMUVLTZUVNUVGUVMUVPUVGUVMGZUVLUUPDZUVQUVFUVRTZUVCUVFUVMVIZUUPVQZKUVQUUI
      NFZUVFGZUUQUUPFUVLUVRVJUVQUWBUVFUVGUVMUWBUVCUVMUWBPUVFUVCUVIUUINUVCUVIUUI
      NURUUIVKVHVLQVMUVTVNUWCUUQNUUPMJZUUPUWCUUJNUUPMUWCUUJINUBJZNUWCUUINIUBUWB
      UVFUTVOUVAUWENFUWCOIVPVRVSVTUVFUWDUUPFUWBUUPWARVSUUQUUPLVGWBWCUVGUVNUVPUV
      GUVNGZUVLUUJUUPWDZMJZWEZDZUWHWFSUWJTUWFUUJUWGMWGUWHWFWHVRUWFUUQUWIFUVLUWJ
      VJUWFUUQUUJUWGWEZMJZUWIUWFUUPUWKUUJMUVGUVNUUPUWKFZUVFUVNUWMPUVCUVFUVJUWMU
      VFUUPUWGFZUWMHZUVJUWMHUVFUUPUFZUWOUUPWIZUUPWJKUVFUWNUVJUWMUVFUWPTZUUPNURZ
      TZUWNTZWKZUWNUVJPZUVFUVSUXBUWAUWPUWSUWNUSUXBUVRUWPUWSUWNWLUUPWMWNWOUVFUWR
      UXCUWTUXAUVFUWPUXCUWQWPUVFUWTUWNUVJUWTUVJUUPNWQUIWRUXAUXCPUVFUWNUVJWSVAXA
      WTXMWTXBRVMVOUWFUUJESZUWGESZUWLUWIFUWFUVAUVCUXDOUVGUVCUVNUVCUVFUTZQIUUIXC
      ZXDUVGUXEUVNUVFUXEUVCUVFUUPESUXEUUPXEUUPXFKRQUUJUWGXGXHVSUUQUWILKWBWCXIXJ
      UVIUVJXKXLXNXORXPUVHUVKGZUVDUUKUXHUVCUVIGZUVDUVHUVCUVKUVIUVHUVGUVCUUGUVGU
      URXQZUXFKUVIUVJUTXRUUIXSZXTUXHUUQUUJNMJZBUUJUVKUUQUXLFUVHUVKUUPNUUJMUVIUV
      JYAVORUUGUVGUURUVKYBUVHUXLUUJFZUVKUVHUVGUXDUXMUXJUVGUVAUVCUXDOUXFUXGXDUUJ
      YCVGQYEVNYDYFYGYHYIYJWTUUKUUGAUULUVEUUFUUCUVEBUUJEUVDUUKYAUVDUXDUUKUVDUVA
      UVCUXDOUUIEUCYKUXGXDQYOUVEUUCUUJDZUVDUXNUUKUVDUXIUXNUXKUVCUVAIDZGUVIUXNUV
      AUXOOYLYMUUIIEYPYNYQQUUKUUCUXNVJUVDBUUJLRYRVNYSYTUUAUUB $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d D x $.
    $( Closure law for ordinal addition.  Here we show that ordinal addition is
       closed within the empty set or any ordinal power of omega.  (Contributed
       by RP, 5-Jan-2025.) $)
    oacl2g $p |- ( ( ( A e. C /\ B e. C ) /\
                 ( C = (/) \/ ( C = ( _om ^o D ) /\ D e. On ) ) ) ->
                 ( A +o B ) e. C ) $=
      ( vx wcel wa c0 wceq com co con0 coa adantr simpl simpr syl wss eleqtrd
      wi wo eleq2 noel pm2.21i biimtrdi com12 cv ciun omelon jctil oecl eqeltrd
      coe adantl onelon expcom jcai oaordi sylc eliuni syl2an2r eqcomd eqsstrdi
      oveq1 ssid oaabs2 syl21anc iunssd wrex peano1 sylancl oveq1d eqtrd sseq2d
      oen0 oa0r ssidd rspcedvd ssiun eqssd ex jaod imp ) ACFZBCFZGZCHIZCJDUMKZI
      ZDLFZGZUAABMKZCFZWFWGWMWKWDWGWMTWEWGWDWMWGWDAHFZWMCHAUBWNWMAUCUDUEUFNWFWK
      WMWFWKGZWLECEUGZCMKZUHZCWFWDWKWLACMKZFZWLWRFWDWEOWOCLFZALFZGWEWTWOXAXBWKX
      AWFWKCWHLWIWJOZWKJLFZWJGZWHLFWKWJXDWIWJPUIUJZJDUKQULZUNWFXAXBTZWKWDXHWEXA
      WDXBCAUOUPNNUQWFWEWKWDWEPNBCAURUSEAWQWSCWLWPACMVDUTVAWKWRCIWFWKWRCWKECWQC
      WKWPCFZGZWQCCXJWPWHFXAWHCRZWQCIXJWPCWHWKXIPWKWIXIXCNSWKXAXIXGNWKXKXIWKWHC
      CWKCWHXCVBZCVEZVCNWPCDVFVGXMVCVHWKCWQRZECVICWRRWKXNCCREHCWKHWHCWKXEHJFHWH
      FXFVJJDVOVKXLSWKWPHIZGZWQCCXPWQHCMKZCXPWPHCMWKXOPVLWKXQCIZXOWKXAXRXGCVPQN
      VMVNWKCVQVRECWQCVSQVTUNSWAWBWC $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d N x $.
    $( If an ordinal is less than a power of omega, the product with a natural
       number is also less than that power of omega.  (Contributed by RP,
       19-Feb-2025.) $)
    onmcl $p |- ( ( A e. On /\ B e. On /\ N e. _om ) ->
            ( A e. ( _om ^o B ) -> ( A .o N ) e. ( _om ^o B ) ) ) $=
      ( vx vy con0 wcel com c0 wceq co wi wa simpl2 eqeltrd adantr oveq2 eleq1d
      comu imbi2d oveq1 simp3 nnon om0r 3syl sylan9eqr omelon jctil peano1 oen0
      w3a coe sylancl a1d c1o cdif simp1 anim1i ondif1 sylibr cv weq eldifi om0
      csuc syl jctl adantl coa ad2antrl simpll onmsuc syl2an2r wo simpr simplrr
      eqid olcd oacl2g syl21anc exp31 finds expdimp syl12anc on0eqel mpjaodan
      a2d ) AFGZBFGZCHGZUKZAIJZAHBULKZGZACSKZWMGZLZIAGZWKWLMZWPWNWSWOIWMWLWKWOI
      CSKZIAICSUAWKWJCFGWTIJWHWIWJUBZCUCCUDUEUFWSHFGZWIMZIHGZIWMGZWSWIXBWHWIWJW
      LNUGUHUIHBUJZUMOUNWKWRMZWJAFUOUPGZWIWQWKWJWRXAPXGWHWRMXHWKWHWRWHWIWJUQZUR
      AUSUTWHWIWJWRNWJXHWIMZWNWPXJWNMZADVAZSKZWMGZLXKAISKZWMGZLXKAEVAZSKZWMGZLX
      KAXQVEZSKZWMGZLXKWPLDECXLIJZXNXPXKYCXMXOWMXLIASQRTDEVBZXNXSXKYDXMXRWMXLXQ
      ASQRTXLXTJZXNYBXKYEXMYAWMXLXTASQRTXLCJZXNWPXKYFXMWOWMXLCASQRTXJXPWNXJXOIW
      MXHXOIJZWIXHWHYGAFUOVCZAVDVFPWIXEXHWIXCXDXEWIXBUGVGUIXFUMVHOPXQHGZXKXSYBY
      IXKXSYBYIXKMZXSMZYAXRAVIKZWMYJWHXSYIYAYLJXJWHYIWNXHWHWIYHPVJYIXKXSVKAXQVL
      VMYKXSWNWMIJZWMWMJZWIMZVNZYLWMGYJXSVOYIXJWNXSVPYJYPXSXJYPYIWNWIYPXHWIYOYM
      WIYNWMVQVGVRVHVJPXRAWMBVSVTOWAWGWBWCWDWKWHWLWRVNXIAWEVFWF $.
  $}

  ${
    $d A w x y z $.  $d B w x y z $.  $d C w x y z $.
    $( Ordinal multiplication by a larger ordinal is absorbed when the larger
       ordinal is either 2 or ` _om ` raised to some power of ` _om ` .
       (Contributed by RP, 12-Jan-2025.) $)
    omabs2 $p |- ( ( ( A e. B /\ (/) e. A ) /\
                     ( B = (/) \/ B = 2o \/
                       ( B = ( _om ^o ( _om ^o C ) ) /\ C e. On ) ) )
                 -> ( A .o B ) = B ) $=
      ( wcel c0 wa wceq c2o com coe co con0 comu c1o syl wss omelon adantr coa
      wi vw vx vy vz w3o eleq2 noel pm2.21i biimtrdi impd com12 cpr elpri oveq1
      wo 2on om1r ax-mp eqtrdi a1d jaoi df2o3 eleq2s imp oveq2 id eqeq12d simpr
      a1i simpllr oecl mpan adantl ad2antlr peano1 sylancl wb mpbird wrex simpl
      cv cdif sylancr eqeltrd onelon simplr ondif1 jctil cun 0elon ad2antrr 1on
      1onn omcl ad3antrrr w3a oaword biimpd mp3an2ani csuc df-1o eloni ordsucss
      word eqsstrid omwordi mpd syl2anc syl3anc sstrd oa0 eqtrd simplrl eleqtrd
      3syl ad6antlr ontr2 oeord syl2an2r ordom mpsyl oveq2d oveq1d ex eqsstrrid
      sylib 3jca oeoa mp3an2i omwordri ssidd eqtr3d mp2an mp3an13 sylcom oeword
      syl21anc mpjaodan syl5 rexlimdva anbi1d jctl oen0 omabs syl22anc cotp weu
      3imtr4d syl2anr sylanbrc ondif2 mpbir2an oeeu wex 0ss sylancom mpi omsson
      euex ssdif sseli eldifi nnon simp-4r oawordri om1 3sstr3d simp-7l ad4antr
      sylbi mp2and simp-5r unssd wne onelpss omsuc sseqtrrd oe1 oveq12d 3eqtr3d
      oe0 el1o pm3.2i expd wn ordirr 3syld on0eqel mpjaod oewordi onsuc 3sstr4d
      eqcomd simpr3 simprr simp1 anim12i sylan pm4.24 oacl simpr1 oaabs2 3eqtrd
      oaass sseqtrd uneq2d oneluni eqtr4i 2a1i oveq2i eqtri ssun1 eqsstri simp2
      jca2 sstrid syl6ci bitrd biimprd sseq1i imbitrrdi jcai biimpa oaabs mpbid
      jca ssequn1 3eqtr2d onun2 eqsstrrd eqssd ad5antr mp3and exlimdv ordtri2or
      3jaod ) ABDZEADZFZBEGZBHGZBIICJKZJKZGZCLDZFZUEABMKZBGZUYSUYTVUHVUAVUFUYTU
      YSVUHUYTUYQUYRVUHUYTUYQAEDZUYRVUHTZBEAUFVUIVUJAUGUHUIUJUKVUAUYSVUHVUAAHDZ
      UYRFZAHMKZHGZUYSVUHVULVUNTVUAVUKUYRVUNUYRVUNTZAENULZHAVUPDAEGZANGZUOVUOAE
      NUMVUQVUOVURVUQUYREEDZVUNAEEUFVUSVUNEUGUHUIVURVUNUYRVURVUMNHMKZHANHMUNHLD
      VUTHGUPHUQURUSUTVAOVBVCVDVIVUAUYQVUKUYRBHAUFUUAVUAVUGVUMBHBHAMVEVUAVFVGUU
      HUKUYSVUFVUHUYSVUFFZAIDZVUHIAPZVVAVVBFZVUHAVUCMKZVUCGZVVDVVBUYRVUBLDZEVUB
      DZVVFVVAVVBVHUYQUYRVUFVVBVJVUFVVGUYSVVBVUEVVGVUDILDZVUEVVGQICVKVLZVMZVNVU
      FVVHUYSVVBVUEVVHVUDVUEVVIVUEFEIDZVVHVUEVVIQUUBVOICUUCVPVMVNAVUBUUDUUEVUFV
      UHVVFVQZUYSVVBVUDVVMVUEVUDVUGVVEBVUCBVUCAMVEVUDVFVGRZVNVRVVAVVCFZUAWAUBWA
      ZUCWAZUDWAZUUFGZIVVPJKZVVQMKZVVRSKZAGZFZUDVVTVSZUCINWBZVSZUBLVSZUAUUGZVUH
      VVOILHWBDZALNWBZDZFZVWIVVAVWMVVCVVAVWLVWJVVAALDZUYRVWLVUFBLDUYQVWNUYSVUFB
      VUCLVUDVUEVTVUEVUCLDZVUDVUEVVIVVGVWOQVVJIVUBVKWCZVMZWDUYQUYRVTZBAWEUUIZUY
      QUYRVUFWFAWGUUJVWJVVINIDZQWMIUUKUULZWHRUBUCUDUAIAUUMOVWIVWHUAUUNVVOVUHVWH
      UAUUSVVOVWHVUHUAVVOVWGVUHUBLVVOVVPLDZFZVWEVUHUCVWFVXCVVQVWFDZFZVWDVUHUDVV
      TVWDVWCVXEVVRVVTDZFZVUHVVSVWCVHVXGVWCVUHVXGVWCFZVVPVUBDZIVVTWIZAPZAIVVPVV
      PSKZJKZPZVUHVXHVXIVVTVUCDZVXHVVTAPZAVUCDZVXOVXHVVTNMKZESKZVWBVVTAVXHVXSVX
      RVVRSKZVWBVXHEVVRPZVXSVXTPZVVRUUOELDZVXGVVRLDZVWCVXRLDZVYAVYBTWJVXEVXFVVT
      LDZVYDVXCVYFVXDVXFVXCVVIVXBVYFQVVOVXBVHIVVPVKZWCZWKVVTVVRWEUUPZVXCVYEVXDV
      XFVWCVXCVYFNLDZVYEVYHWLVVTNWNZVPWOZVYCVYDVYEWPVYAVYBEVVRVXRWQWRWSUUQVXHVX
      RVWAPZVXTVWBPZVXHNVVQPZVYMVXHVXDVVQVWKDZVYOVXCVXDVXFVWCVJZVWFVWKVVQILPVWF
      VWKPUURILNUUTURUVAVYPVVQLDZEVVQDZFZVYOVVQWGVYTNEWTZVVQXAVYRVYSWUAVVQPZVYR
      VVQXDVYSWUBTVVQXBEVVQXCOVDXEUVJXOVYJVXGVYRVWCVYFVYOVYMTWLVXDVYRVXCVXFVXDV
      VQIDZVYRVVQINUVBZVVQUVCOZVNZVXHVVIVXBVYFQVVOVXBVXDVXFVWCUVDZVYGWCZNVVQVVT
      XFWSXGVXHVYEVWALDZVYDVYMVYNTVYLVXHVYFVYRWUIWUHVXGVYRVWCWUFRZVVTVVQWNXHZVX
      GVYDVWCVYIRZVXRVWAVVRUVEXIXGXJVXHVXBVXSVVTGWUGVXBVXSVXRVVTVXBVYEVXSVXRGVX
      BVYFVYJVYEVVIVXBVYFQVYGVLZWLVYKVPVXRXKOVXBVYFVXRVVTGWUMVVTUVFOXLOVXGVWCVH
      ZUVGZVXHABVUCUYQUYRVUFVVCVXBVXDVXFVWCUVHVVOVUDVXBVXDVXFVWCUYSVUDVUEVVCXMU
      VIXNVXHVYFVWOVXPVXQFVXOTWUHVUFVWOUYSVVCVXBVXDVXFVWCVWQXPVVTAVUCXQXHUVKVXH
      VXBVVGVWJVXIVXOVQWUGVUFVVGUYSVVCVXBVXDVXFVWCVVKXPVWJVXHVXAVIVVPVUBIXRXIVR
      VXHIVVTAVVAVVCVXBVXDVXFVWCUVLZWUOUVMVXHVWBVVTVVTMKZAVXMVXHVWBVVTVVQWTZMKZ
      WUQVXHVWBVWAVVTSKZWUSVXHVVRVVTPZVWBWUTPZVXHWVAVVRVVTUVNZFZWVAVXHVXFWVDVXE
      VXFVWCWFVXGVYDVWCVYFVXFWVDTVYIWUHVYDVYFFVXFWVDVVRVVTUVOWRXSXGWVAWVCVTOVXH
      VYDVYFWUIWVAWVBTWULWUHWUKVYDVYFWUIWPWVAWVBVVRVVTVWAWQWRXIXGVXHVYFVYRWUSWU
      TGWUHWUJVVTVVQUVPXHUVQVXHWURVVTPZWUSWUQPZVXHWURIVVTIXDZVXHWUCWURIPXTVXHVX
      DWUCVYQWUDOZVVQIXCYAVXHIINJKZVVTVVIWVIIGQIUVRURZVXHNVVPPZWVIVVTPZVXHVVPEG
      ZWVKEVVPDZVXHWVMVVBIIDZWVKVXHWVMVVBVXHWVMFZAVVQIWVPVWBVVQESKZAVVQWVPVWAVV
      QVVRESWVPVWANVVQMKZVVQWVPVVTNVVQMWVPVVTIEJKZNWVPVVPEIJVXHWVMVHYBVVIWVSNGQ
      IUWAURZUSZYCWVPVYRWVRVVQGVXEVYRVXFVWCWVMVXDVYRVXCWUEVMWOZVVQUQOXLWVPVVRND
      VVREGWVPVVRVVTNVXEVXFVWCWVMVJWWAXNVVRUWBYFUVSVXGVWCWVMWFWVPVYRWVQVVQGWWBV
      VQXKOUVTVXHWUCWVMWVHRWDYDVVIVVIFZVXHVVCVVBWVOTVVIVVIQQUWCWUPWWCVVCVVBWVOI
      AIXQUWDYAWVOWVKTVXHWVOWVKWVGWVOUWEXTIUWFURUHVIUWGVXHVXBVVPXDZWVNWVKTWUGVV
      PXBZWWDWVNWVKWWDWVNFNWUAVVPXAWWDWVNWUAVVPPZEVVPXCZVDXEYDXOVXHVXBWVMWVNUOZ
      WUGVVPUWHZOUWIVXHVYJVXBVVIWPVVLWVKWVLTVXHVYJVXBVVIVYJVXHWLVIWUGVVIVXHQVIY
      GVONVVPIUWJVPXGYEXJVXHWURLDZVYFVYFWVEWVFTVXHVYRWWJWUJVVQUWKOWUHWUHWURVVTV
      VTXFXIXGXJVXHVWBAWUNUWMVVIVXHVXBVXBVXMWUQGQWUGWUGIVVPVVPYHYIUWLVVAVXIVXKV
      XNWPZVUHTVVCVXBVXDVXFVWCVVAWWKVUHVVAWWKFZVUHVVFWWLVVEVUCWWLVVEVXMVUCMKZVU
      CWWLVXNVVEWWMPZVVAVXIVXKVXNUWNWWLVWNVXMLDZVWOVXNWWNTVVAVWNWWKVWSRZWWLVUEV
      XIFZWWOVVAVUEWWKVXIUYSVUDVUEUWOZVXIVXKVXNUWPUWQZWWQVVIVXLLDZWWOQWWQVXBVXB
      FZWWTWWQVXBWXAVUEVVGVXIVXBVVJVUBVVPWEZUWRZVXBUWSYFZVVPVVPUWTZOIVXLVKWCOVU
      FVWOUYSWWKVWQVNZAVXMVUCYJXIXGWWLIVXLVUBSKZJKZWWMVUCVVIWWLWWTVVGWXHWWMGQWW
      LWWQWXAWWTWWSWXDWXEXOVUFVVGUYSWWKVVKVNZIVXLVUBYHYIWWLWXGVUBIJWWLWXGVVPVVP
      VUBSKZSKZWXJVUBWWLVXBVXBVVGWXGWXKGWWLWWQVXBWWSWXCOZWXLWXIVVPVVPVUBUXDXIWW
      LWXJVUBVVPSWWLVXIVVGVUBVUBPZWXJVUBGZVVAVXIVXKVXNUXAZWXIWWLVUBYKVVPVUBCUXB
      ZYQZYBWXQUXCYBYLUXEWWLVUCVXJVUCMKZVVEWWLWVMWXRVUCGWVNWWLWVMFZWXRWVIVUCMKZ
      VUCWXSVXJWVIVUCMWVMVXJWVIGWWLWVMVXJINWIZWVIWVMVVTNIWVMVVTWVSNVVPEIJVEWVTU
      SUXFWYAIWVIVWTWYAIGWMINQUXGURWVJUXHUSVMYCWXSVUENCPZFZWXTVUCGWXSVUEWYBVVAV
      UEWWKWVMWWRWKWXSVUEECDZWYBWXSVUEIWVSJKZVUCDZWYDWXSVUEWYELDZVWOFWYEAPZVXQF
      ZWYFWXSVUEWYGVWOWYGWXSVUEVVIWVSLDZWYGQVVIVYCWYJQWJIEVKYMZIWVSVKYMUXIVWPUX
      OWWLWYIWVMWWLWYHVXQWWKWYHVVAWWKWYEVXJAWYEIVXJWYEWVIIWVSNIJWVTUXJWVJUXKIVV
      TUXLUXMVXIVXKVXNUXNZUXPVMWWLABVUCUYSUYQVUFWWKVWRWKUYSVUDVUEWWKXMXNUYFRWYE
      AVUCXQUXQVUEWYDWYFVUEWYDWVSVUBDZWYFVYCVUEVWJWYDWYMVQWJVXAECIXRYNWYJVUEVVG
      VWJWYMWYFVQWYKVVJVWJVUEVXAVIWVSVUBIXRYIUXRUXSYOVUECXDZWYDWYBTCXBWYNWYDWUA
      CPWYBECXCNWUACXAUXTUYAOYOUYBWYCINVUBSKZJKZWXTVUCWYCVVIVYJVVGWPZWYPWXTGVUE
      WYQWYBVUEVVIVYJVVGVVIVUEQVIVYJVUEWLVIVVJYGRINVUBYHOWYCWYOVUBIJWYCVWTVVGIV
      UBPWYOVUBGVWTWYCWMVIVUEVVGWYBVVJRWYCIWVIVUBWVJVUEWYBWVIVUBPZVYJVUEVWJWYBW
      YRVQWLVXANCIYPYNUYCYENVUBUYDYQYBYLOXLWWLWVNFZWXRVVTVUCMKZIWXJJKZVUCWYSVXJ
      VVTVUCMWYSIVVTPVXJVVTGWYSIWVIVVTWVJWYSWVKWVLWYSNWUAVVPXAWWLWVNWWFWWLVXBWW
      DWVNWWFTWXLWWEWWGXOVDXEVYJWYSVXBVWJWVKWVLVQWLWWLVVGWVNVXIVXBWXIWWLVXIWVNW
      XORZWXBXSZVWJWYSVXAVINVVPIYPYIUYEYEIVVTUYGYFYCVVIWYSVXBVVGXUAWYTGQXUCWWLV
      VGWVNWXIRZIVVPVUBYHYIWYSWXJVUBIJWYSVXIVVGWXMWXNXUBXUDWYSVUBYKWXPYQYBUYHWW
      LWWQVXBWWHWWSWXCWWIXOYRWWLVXKWXRVVEPZWWKVXKVVAWYLVMWWLVXJLDZVWNVWOVXKXUET
      WWLWWQVVIVYFFXUFWWSWWQVYFVVIWWQVVIVXBVYFQWXCVYGWCQWHIVVTUYIXOWWPWXFVXJAVU
      CYJXIXGUYJUYKVUFVVMUYSWWKVVNVNVRYDUYLUYMYDYSYTYTYTUYNYSXGVVAAXDZWVGVVBVVC
      UOVVAVWNXUGVWSAXBOXTAIUYOVPYRYDUYPVD $.
    $( $j usage 'omabs2' avoids 'ax-reg'; $)
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d D x $.
    $( Closure law for ordinal multiplication.  (Contributed by RP,
       12-Jan-2025.) $)
    omcl2 $p |- ( ( ( A e. C /\ B e. C ) /\
                 ( C = (/) \/ ( C = ( _om ^o ( _om ^o D ) ) /\ D e. On ) ) ) ->
                 ( A .o B ) e. C ) $=
      ( vx wcel wa c0 wceq com co con0 comu wi omelon syl adantl simpr wss c1o
      wo eleq2 noel pm2.21i biimtrdi com12 adantr simpl oecl mpan jctil eqeltrd
      coe simpll onelon syl2an2 on0eqel oveq1 sylan9eqr peano1 sylancl eleqtrrd
      om0r oen0 ex w3a cv ciun simp1 ad2antrr syl2anc jcai simpl3 simpl2 omordi
      imp syl21anc eliuni syl2an2r oveq1d eqtrd 0ss a1i eqsstrd c2o w3o adantll
      id 3mix3d omabs2 ssidd sylan mpjaodan iunssd wrex cdif 1onn ondif2 oeordi
      mpbir2an mpd oe0 ax-mp eqcomi 3eltr4d sseq2d rspcedvd ssiun eqssd eleqtrd
      om1r 3expia com23 jaod ) ACFZBCFZGZCHIZCJJDUMKZUMKZIZDLFZGZUAABMKZCFZXQXR
      YEYCXOXRYENXPXRXOYEXRXOAHFZYECHAUBYFYEAUCUDUEUFUGXQYCYEXQYCGZAHIZHAFZUAZY
      EYGALFZYJYCCLFZXQXOYKYCCXTLYAYBUHZYBXTLFZYAYBJLFZXSLFZGZYNYBYPYOYOYBYPOJD
      UIZUJOUKZJXSUIPQULZXOXPYCUNCAUOZUPAUQPYGYHYEYIYGYHYEYGYHGYDHCYHYGYDHBMKZH
      AHBMURYGBLFZUUBHIYCYLXQXPUUCYTXQXPYCXOXPRUGCBUOUPBVCPUSYGHCFZYHYCUUDXQYCH
      XTCYBHXTFZYAYBYQHJFZUUEYSUTJXSVDVAQYMVBQUGULVEXQYCYIYENXQYIYCYEXOXPYIYCYE
      NXOXPYIVFZYCYEUUGYCGZYDECEVGZCMKZVHZCUUGXOYCYDACMKZFZYDUUKFXOXPYIVIZUUHYL
      YKGZYIXPUUMUUHYLYKYCYLUUGYTQUUHYLYKUUHYLGYLXOYKUUHYLRUUGXOYCYLUUNVJUUAVKV
      EVLXOXPYIYCVMXOXPYIYCVNUUOYIGXPUUMBCAVOVPVQEAUUJUULCYDUUIACMURVRVSYCUUKCI
      UUGYCUUKCYCECUUJCYCUUICFZGZUUIHIZUUJCSHUUIFZUUQUURGZUUJHCUUTUUJHCMKZHUUTU
      UIHCMUUQUURRVTYCUVAHIZUUPUURYCYLUVBYTCVCPVJWAHCSUUTCWBWCWDUUQUUSGZUUJCCUV
      CUUPUUSGZXRCWEIZYCWFUUJCIUUPUUSUVDYCUVDWHWGUVCYCXRUVEYCUUPUUSUNWIUUICDWJV
      KUVCCWKWDUUQUUILFZUURUUSUAYCYLUUPUVFYTCUUIUOWLUUIUQPWMWNYCCUUJSZECWOCUUKS
      YCUVGCCSETCYCJHUMKZXTTCYCHXSFZUVHXTFZYCYOYBGZUUFUVIYCYBYOYAYBROUKZUTJDVDV
      AYCYPJLWEWPFZUVIUVJNYCUVKYPUVLYRPUVMYOTJFOWQJWRWTHXSJWSVAXATUVHIYCUVHTYOU
      VHTIOJXBXCXDWCYMXEYCUUITIZGUUJCCUVNYCUUJTCMKZCUUITCMURYCYLUVOCIYTCXKPUSXF
      YCCWKXGECUUJCXHPXIQXJVEXLXMVPXNXAVEXNVP $.
  $}

  $( Closure law for ordinal multiplication.  (Contributed by RP,
     14-Jan-2025.) $)
  omcl3g $p |- ( ( ( A e. C /\ B e. C ) /\
                 ( C e. 3o \/ ( C = ( _om ^o ( _om ^o D ) ) /\ D e. On ) ) ) ->
                 ( A .o B ) e. C ) $=
    ( wcel wa com coe co wceq con0 wo comu c1o c2o df2o3 oveq12 eqeltrdi eleq2
    c0 c3o w3o ctp eltpi df-3o csn cun uneq1i df-suc df-tp 3eqtr4i eqtri eleq2s
    csuc cpr orc omcl2 sylan2 ex el1o 0elon om0 ax-mp 0lt1o eqeltri syl2anb a1i
    wi anbi12d 3imtr4d com12 elpri 0ex prid1 3eltr4i 1on om0r 1oelpr om1 syl2an
    ccase 3jaod syl5 olc jaod imp ) ACEZBCEZFZCUAEZCGGDHIHIJDKEFZLABMIZCEZWIWJW
    MWKWJCTJZCNJZCOJZUBZWIWMWQCTNOUCZUACTNOUDUAOUNZWRUEOOUFZUGTNUOZWTUGWSWROXAW
    TPUHOUITNOUJUKULUMWIWNWMWOWPWIWNWMWNWIWNCGGCHIHIJCKEFZLWMWNXBUPABCCUQURUSWO
    WIWMWOANEZBNEZFZWLNEZWIWMXEXFVHWOXCATJZBTJZXFXDAUTBUTXGXHFZWLTTMIZNATBTMQZX
    JTNTKEXJTJVATVBVCZVDVERVFVGWOWGXCWHXDCNASCNBSVICNWLSVJVKWPWIWMWPAOEZBOEZFZW
    LOEZWIWMXOXPVHWPXMXGANJZLZXHBNJZLZXPXNXRAXAOATNVLPUMXTBXAOBTNVLPUMXGXHXQXSX
    PXIWLXJOXKTXAXJOTNVMVNZXLPVORXQXHFWLNTMIZOANBTMQTXAYBOYANKEZYBTJVPNVBVCPVOR
    XGXSFWLTNMIZOATBNMQTXAYDOYAYCYDTJVPNVQVCPVORXQXSFWLNNMIZOANBNMQNXAYEOVRYCYE
    NJVPNVSVCPVORWAVTVGWPWGXMWHXNCOASCOBSVICOWLSVJVKWBWCWIWKWMWKWIWNWKLWMWKWNWD
    ABCDUQURUSWEWF $.

  $( An ordinal number is less than or equal to the successor of an ordinal
     class iff the ordinal number is either less than or equal to the ordinal
     class or the ordinal number is equal to the successor of the ordinal
     class.  See also ~ ordsssucim , ~ limsssuc .  (Contributed by RP,
     22-Feb-2025.) $)
  ordsssucb $p |- ( ( A e. On /\ Ord B ) -> ( A C_ suc B
              <-> ( A C_ B \/ A = suc B ) ) ) $=
    ( con0 wcel word wa csuc wpss wceq wo sspss ordsssuc eloni ordsuci ordelpss
    wss wb syl2an bitrd orbi1d bitr4id ) ACDZBEZFZABGZPAUEHZAUEIZJABPZUGJAUEKUD
    UHUFUGUDUHAUEDZUFABLUBAEUEEUIUFQUCAMBNAUEORSTUA $.

  ${
    $d A x y $.  $d B x y $.  $d C x y $.  $d F x y $.
    $( Lemma for ~ tfsconcatun .  (Contributed by RP, 23-Feb-2025.) $)
    tfsconcatlem $p |- ( ( A e. On /\ B e. On /\ C e. ( ( A +o B ) \ A ) ) ->
                       E! x E. y e. B ( C = ( A +o y ) /\ x = ( F ` y ) ) ) $=
      ( con0 wcel coa co cdif wceq wa wrex wmo wex wss word syl sylib wrmo wreu
      w3a cv cfv weu onss 3ad2ant2 wb oacl eloni adantr ordeldif syl2anc biimpa
      wal ancomd ex imdistani 3impa oawordex2 simp1 ssdifd sselda ordon sylancr
      mpbid anass sylanbrc oawordeu reuss syl3anc reurmo df-rmo ax-gen moexexvw
      moeq sylancl df-rex exbii bitr4i mobii sylibr wi fvex isseti a1i reximdva
      jctr mpd rexcom4a exmoeu bitr3i eqcom anbi1i rexbii eubii ) CGHZDGHZECDIJ
      ZCKZHZUCZCBUDZIJZELZAUDXDFUEZLZMZBDNZAUFZEXELZXHMZBDNZAUFXCXJAOZXKXCXDDHZ
      XFMZXHMZBPZAOZXOXCXQBOZXHAOZBUPXTXCXFBDUAZYAXCXFBDUBZYCXCDGQZXFBDNZXFBGUB
      ZYDWSWRYEXBDUGUHXCWRWSMZCEQZEWTHZMZMZYFWRWSXBYLYHXBYKYHXBYKYHXBMYJYIYHXBY
      JYIMZYHWTRZCRZXBYMUIYHWTGHZYNCDUJZWTUKSWRYOWSCUKZULWTCEUMUNUOUQURUSUTBCDE
      VASZXCWREGHZMYIMZYGXCWRYTYIMZUUAWRWSXBVBZXCEGCKZHZUUBWRWSXBUUEYHXAUUDEYHW
      TGCYHYPWTGQYQWTUGSVCVDUTXCGRYOUUEUUBUIVEXCWRYOUUCYRSGCEUMVFVGWRYTYIVHVIBC
      EVJSXFBDGVKVLXFBDVMSXFBDVNTYBBAXGVQVOXQXHBAVPVRXJXSAXJXPXIMZBPXSXIBDVSXRU
      UFBXPXFXHVHVTWAWBWCXCXFXHAPZMZBDNZXOXKWDZXCYFUUIYSXCXFUUHBDXFUUHWDXCXPMXF
      UUGAXGXDFWEWFWIWGWHWJUUIXJAPUUJXFXHABDWKXJAWLWMTWJXJXNAXIXMBDXFXLXHXEEWNW
      OWPWQT $.
  $}

  ${
    $d A a b d u v x y z $.  $d B a b d u v x y z $.  $d C a b d u v x y z $.
    $d D a b d u v x y z $.  $d F a b d u v x y z $.  $d X d u v x y z $.
    $d .+ d u v $.
    tfsconcat.op $e |- .+ = ( a e. _V , b e. _V |-> ( a u. { <. x , y >. |
               ( x e. ( ( dom a +o dom b ) \ dom a ) /\
               E. z e. dom b ( x = ( dom a +o z ) /\ y = ( b ` z ) ) ) } ) ) $.
    $( The concatenation of two transfinite series is a union of functions.
       (Contributed by RP, 23-Feb-2025.) $)
    tfsconcatun $p |- ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. On ) ) ->
                      ( A .+ B ) = ( A u.
                      { <. x , y >. | ( x e. ( ( C +o D ) \ C ) /\
                      E. z e. D ( x = ( C +o z ) /\ y = ( B ` z ) ) ) } ) ) $=
      ( wa con0 wcel cvv cv cdm coa wceq adantl wfn co cdif cfv wrex copab cmpo
      cun a1i simprl dmeq adantr fndm sylan9eqr oveq12d eleq2d oveq1d eqeq2d wb
      difeq12d anbi12d rexeqbidv opabbidv uneq12d fnex ad2ant2r ad2ant2l difexd
      fveq1 oacl weu simplrl simplrr simpr tfsconcatlem syl3anc euabex opabex3d
      cab syl unexd ovmpod ) DFUAZEGUAZLZFMNZGMNZLZLZIJDEOOIPZAPZWJQZJPZQZRUBZW
      LUCZNZWKWLCPZRUBZSZBPZWRWMUDZSZLZCWNUEZLZABUFZUHZDWKFGRUBZFUCZNZWKFWRRUBZ
      SZXAWREUDZSZLZCGUEZLZABUFZUHHOHIJOOXHUGSWIKUIWIWJDSZWMESZLZLZWJDXGXSWIXTY
      AUJYCXFXRABYCWQXKXEXQYCWPXJWKYCWOXIWLFYCWLFWNGRYBWIWLDQZFXTWLYDSYAWJDUKUL
      WEYDFSZWHWCYEWDFDUMULULUNZYBWIWNEQZGYAWNYGSXTWMEUKTWEYGGSZWHWDYHWCGEUMTUL
      UNZUOYFUTUPYCXDXPCWNGYIYCWTXMXCXOYCWSXLWKYCWLFWRRYFUQURYBXCXOUSZWIYAYJXTY
      AXBXNXAWRWMEVIURTTVAVBVAVCVDWCWFDONWDWGFMDVEVFZWDWGEONWCWFGMEVEVGWIDXSOOY
      KWIXQABXJOWHXJONWEWHXIFMFGVJVHTWIXKLZXQBVKZXQBVSONYLWFWGXKYMWEWFWGXKVLWEW
      FWGXKVMWIXKVNBCFGWKEVOVPXQBVQVTVRWAWB $.

    $( The concatenation of two transfinite series is a transfinite series.
       (Contributed by RP, 22-Feb-2025.) $)
    tfsconcatfn $p |- ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. On ) ) ->
                        ( A .+ B ) Fn ( C +o D ) ) $=
      ( wfn wa con0 wcel co coa cv wceq cun cdif cfv wrex copab simpll weu wral
      simplrl simplrr simpr tfsconcatlem syl3anc ralrimiva fnopabg sylib cin c0
      eqid disjdif a1i fnund tfsconcatun wss oaword1 undif eqcomd adantl mpbird
      fneq12d ) DFLZEGLZMZFNOZGNOZMZMZDEHPZFGQPZLDARZVRFUAZOZVSFCRZQPSBRWBEUBSM
      CGUCZMABUDZTZFVTTZLVPFVTDWDVJVKVOUEVPWCBUFZAVTUGWDVTLVPWGAVTVPWAMVMVNWAWG
      VLVMVNWAUHVLVMVNWAUIVPWAUJBCFGVSEUKULUMWCABVTWDWDURUNUOFVTUPUQSVPFVRUSUTV
      AVPVRWFVQWEABCDEFGHIJKVBVOVRWFSVLVOWFVRVOFVRVCWFVRSFGVDFVRVEUOVFVGVIVH $.

    $( An early value of the concatenation of two transfinite series.
       (Contributed by RP, 23-Feb-2025.) $)
    tfsconcatfv1 $p |- ( ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. On ) )
                   /\ X e. C ) -> ( ( A .+ B ) ` X ) = ( A ` X ) ) $=
      ( wfn wa con0 wcel co cfv cv wceq coa cdif wrex tfsconcatun fveq1d adantr
      copab cun simplll weu wral simplrl simplrr tfsconcatlem syl3anc ralrimiva
      simpr eqid fnopabg sylib cin c0 disjdif a1i fvun1d eqtrd ) DFMZEGMZNZFOPZ
      GOPZNZNZIFPZNZIDEHQZRZIDASZFGUAQZFUBZPZVRFCSZUAQTBSWBERTNCGUCZNABUGZUHZRZ
      IDRVMVQWFTVNVMIVPWEABCDEFGHJKLUDUEUFVOFVTDWDIVGVHVLVNUIVOWCBUJZAVTUKZWDVT
      MVMWHVNVMWGAVTVMWANVJVKWAWGVIVJVKWAULVIVJVKWAUMVMWAUQBCFGVREUNUOUPUFWCABV
      TWDWDURUSUTFVTVAVBTVOFVSVCVDVMVNUQVEVF $.

    $( A latter value of the concatenation of two transfinite series.
       (Contributed by RP, 23-Feb-2025.) $)
    tfsconcatfv2 $p |- ( ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. On ) )
                   /\ X e. D ) -> ( ( A .+ B ) ` ( C +o X ) ) = ( B ` X ) ) $=
      ( wa con0 wcel coa co cfv wceq adantr wfn cdif wrex copab cun tfsconcatun
      cv fveq1d simplll weu wral simplrl simplrr tfsconcatlem syl3anc ralrimiva
      simpr eqid fnopabg sylib cin disjdif a1i wss pm3.22 adantl oaordi syl imp
      c0 wi onelon sylan oaword1 syl2anc word oacl eloni jca ordeldif mpbir2and
      fvun2d cop oveq2 eqeq2d fveq2 anbi12d rspcev mpanr12 cvv ovex fvex pm3.2i
      wb eleq1 eqeq1 anbi1d rexbidv anbi2d opelopabg mp1i fnopfvb mpbird 3eqtrd
      ) DFUAZEGUAZMZFNOZGNOZMZMZIGOZMZFIPQZDEHQZRZXNDAUGZFGPQZFUBZOZXQFCUGZPQZS
      ZBUGZYAERZSZMZCGUCZMZABUDZUEZRZXNYJRZIERZXKXPYLSXLXKXNXOYKABCDEFGHJKLUFUH
      TXMFXSDYJXNXEXFXJXLUIXKYJXSUAZXLXKYHBUJZAXSUKYOXKYPAXSXKXTMXHXIXTYPXGXHXI
      XTULXGXHXIXTUMXKXTUQBCFGXQEUNUOUPYHABXSYJYJURUSUTTZFXSVAVJSXMFXRVBVCXMXNX
      SOZXNXROZFXNVDZXKXLYSXKXIXHMZXLYSVKXJUUAXGXHXIVEVFIGFVGVHVIXMXHINOZYTXGXH
      XIXLULXKXIXLUUBXJXIXGXHXIUQVFGIVLVMFIVNVOXMXRVPZFVPZMZYRYSYTMWNXKUUEXLXJU
      UEXGXJUUCUUDXJXRNOUUCFGVQXRVRVHXHUUDXIFVRTVSVFTXRFXNVTVHWAZWBXMYMYNSZXNYN
      WCYJOZXMUUHYRXNYBSZYNYESZMZCGUCZUUFXLUULXKXLXNXNSZYNYNSZUULXNURYNURUUKUUM
      UUNMCIGYAISZUUIUUMUUJUUNUUOYBXNXNYAIFPWDWEUUOYEYNYNYAIEWFWEWGWHWIVFXNWJOZ
      YNWJOZMUUHYRUULMZWNXMUUPUUQFIPWKIEWLWMYIYRUUIYFMZCGUCZMUURABXNYNWJWJXQXNS
      ZXTYRYHUUTXQXNXSWOUVAYGUUSCGUVAYCUUIYFXQXNYBWPWQWRWGYDYNSZUUTUULYRUVBUUSU
      UKCGUVBYFUUJUUIYDYNYEWPWSWRWSWTXAWAXMYOYRUUGUUHWNYQUUFXSXNYNYJXBVOXCXD $.

    $( The value of the concatenation of two transfinite series.  (Contributed
       by RP, 24-Feb-2025.) $)
    tfsconcatfv $p |- ( ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. On ) )
                   /\ X e. ( C +o D ) ) -> ( ( A .+ B ) ` X ) = if ( X e. C ,
                   ( A ` X ) , ( B ` ( iota_ d e. D ( C +o d ) = X ) ) ) ) $=
      ( wa con0 wcel coa co cfv wceq wfn cv crio cif tfsconcatfv1 adantlr simpr
      iftrued eqtr4d iffalsed simpll wreu wss wrex onss adantl ad3antlr simpllr
      wn wb simplrl oacl onelon sylan ontri1 syl2anc biimpar oawordex2 syl12anc
      simplr oawordeu syl2an2r reuss syl3anc riotacl tfsconcatfv2 wsbc riotasbc
      jca syl sbceq1g csbov2g csbvarg oveq2d eqtrd eqeq1d bitrd biimpa 3eqtr2rd
      csb fveq2d pm2.61dan ) DFUAEGUANZFOPZGOPZNZNZIFGQRZPZNZIFPZIDEHRZSZXAIDSZ
      FLUBZQRZITZLGUCZESZUDZTWTXANZXCXDXJWQXAXCXDTWSABCDEFGHIJKMUEUFXKXAXDXIWTX
      AUGUHUIWTXAUSZNZXJXIFXHQRZXBSZXCXMXAXDXIWTXLUGUJXMWQXHGPZXOXITWQWSXLUKXMX
      GLGULZXPXMGOUMZXGLGUNZXGLOULZXQWPXRWMWSXLWOXRWNGUOUPUQXMWPFIUMZWSXSWMWPWS
      XLURWTYAXLWTWNIOPZYAXLUTWMWNWOWSVAZWQWROPZWSYBWPYDWMFGVBUPWRIVCVDZFIVEVFV
      GZWQWSXLVJLFGIVHVIWTWNYBNXLYAXTWTWNYBYCYEVSYFLFIVKVLXGLGOVMVNZXGLGVOVTZAB
      CDEFGHXHJKMVPVFXMXNIXBXMXPXGLXHVQZXNITZYHXMXQYIYGXGLGVRVTXPYIYJXPYILXHXFW
      JZITYJLXHXFIGWAXPYKXNIXPYKFLXHXEWJZQRXNLXHFXEQGWBXPYLXHFQLXHGWCWDWEWFWGWH
      VFWKWIWL $.

    $( The range of the concatenation of two transfinite series.  (Contributed
       by RP, 24-Feb-2025.) $)
    tfsconcatrn $p |- ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. On ) ) ->
                        ran ( A .+ B ) = ( ran A u. ran B ) ) $=
      ( vd wa con0 wcel crn wceq wrex syl adantr wfn co cv coa cdif tfsconcatun
      cfv copab cun rnun a1i wex cab df-rex wss wi pm3.22 adantl oaordi simplrl
      rneqd imp simprr onelon sylan oaword1 syl2anc word wb oacl ad2antlr eloni
      ordeldif mpbir2and simpr jca biimpa ancomd oawordex2 eqcom rexbii w3a csn
      sylib weq simpll3 eqtr3d simp1rl simp1rr simp2 3jca oacan mpbid sylibr ex
      velsn adantrd expimpd jca2 reximdv2 vex fveq2 eqeq2d rexsn imbitrdi oveq2
      simpl3 anbi12d rspcev syl12anc impbid bitr3id abbidv rnopab fnrnfv uneq2d
      rexxfrd2 3eqtr4d 3eqtrd ) DFUAZEGUAZMZFNOZGNOZMZMZDEHUBZPDAUCZFGUDUBZFUEZ
      OZYHFCUCZUDUBZQZBUCZYLEUGZQZMZCGRZMZABUHZUIZPZDPZUUAPZUIZUUDEPZUIYFYGUUBA
      BCDEFGHIJKUFVAUUCUUFQYFDUUAUJUKYFUUEUUGUUDYFYTAULZBUMZYOLUCZEUGZQZLGRZBUM
      ZUUEUUGYFUUHUUMBUUHYSAYJRYFUUMYSAYJUNYFYSUULALFUUJUDUBZYJGYFUUJGOZMZUUOYJ
      OZUUOYIOZFUUOUOZYFUUPUUSYFYDYCMZUUPUUSUPYEUVAYBYCYDUQURUUJGFUSSVBUUQYCUUJ
      NOZUUTYBYCYDUUPUTZYFYDUUPUVBYBYCYDVCGUUJVDZVEFUUJVFVGUUQYIVHZFVHZUURUUSUU
      TMVIUUQYINOZUVEYEUVGYBUUPFGVJZVKYIVLZSUUQYCUVFUVCFVLZSYIFUUOVMVGVNYFYKMZU
      UOYHQZLGRZYHUUOQZLGRUVKYEFYHUOZYHYIOZMUVMYFYEYKYBYEVOTUVKUVPUVOYFYKUVPUVO
      MZYFUVEUVFMZYKUVQVIYEUVRYBYEUVEUVFYEUVGUVEUVHUVISYCUVFYDUVJTVPURYIFYHVMSV
      QVRLFGYHVSVGUVLUVNLGUUOYHVTWAWDYFUUPUVNWBZYSUULUVSYSYQCUUJWCZRUULUVSYRYQC
      GUVTUVSYLGOZYRMYLUVTOZYQUVSUWAYRUWBUVSUWAMZYNUWBYQUWCYNUWBUWCYNMZCLWEZUWB
      UWDYMUUOQZUWEUWDYHYMUUOUWCYNVOYFUUPUVNUWAYNWFWGUWDYCYLNOZUVBWBZUWFUWEVIUW
      CUWHYNUWCYCUWGUVBUVSYCUWAYCYDYBUUPUVNWHTUVSYDUWAUWGYCYDYBUUPUVNWIZGYLVDVE
      UVSUVBUWAUVSYDUUPUVBUWIYFUUPUVNWJZUVDVGTWKTFYLUUJWLSWMCUUJWPWNWOWQWRUWAYN
      YQVCWSWTYQUULCUUJLXAUWEYPUUKYOYLUUJEXBXCZXDXEUVSUULYSUVSUULMUUPUVNUULYSUV
      SUUPUULUWJTYFUUPUVNUULXGUVSUULVOYRUVNUULMCUUJGUWEYNUVNYQUULUWEYMUUOYHYLUU
      JFUDXFXCUWKXHXIXJWOXKXQXLXMUUEUUIQYFYTABXNUKYAUUGUUNQXTYELBGEXOVKXRXPXS
      $.

    $( The concatenation of two transfinite series is onto the union of the
       ranges.  (Contributed by RP, 24-Feb-2025.) $)
    tfsconcatfo $p |- ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. On ) ) ->
                      ( A .+ B ) : ( C +o D ) -onto-> ( ran A u. ran B ) ) $=
      ( wfn wa con0 wcel co coa crn cun wceq wfo tfsconcatfn tfsconcatrn df-fo
      sylanbrc ) DFLEGLMFNOGNOMMDEHPZFGQPZLUFRDRERSZTUGUHUFUAABCDEFGHIJKUBABCDE
      FGHIJKUCUGUHUFUDUE $.

    $( The concatentation with the empty series leaves the series unchanged.
       (Contributed by RP, 25-Feb-2025.) $)
    tfsconcatb0 $p |- ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. On ) ) ->
                        ( B = (/) <-> ( A .+ B ) = A ) ) $=
      ( wa con0 wcel c0 wceq wb syl wn adantl wfn cv coa co cdif cfv wrex copab
      cun wss cdm wrel fnrel reldm0 fndm eqeq1d bitrd ad2antlr wal rexeq mtbiri
      rex0 intnand alrimivv opab0 sylibr 0ss eqsstrdi ex c1o wi df-1o simpl wne
      csuc on0eln0 df-ne bitrdi biimpar onsucss eqsstrid cop simpr 0lt1o sseldd
      sylc a1i oaord1 mpbid ssidd word oacl eloni adantr jca ordeldif mpbir2and
      oa0 eqcomd eqidd oveq2 eqeq2d fveq2 anbi12d syl2anc cvv fvexd eleq1 eqeq1
      rspcev rexbidv opelopabga ordirr neleqtrrd opeldmd mtod jctird nelss syl6
      bi2anan9 syld impcon4bid ssequn2 tfsconcatun bitr4d ) DFUAZEGUAZLZFMNZGMN
      ZLZLZEOPZDAUBZFGUCUDZFUEZNZYNFCUBZUCUDZPZBUBZYREUFZPZLZCGUGZLZABUHZUIZDPZ
      DEHUDZDPYLYMUUGDUJZUUIYLYMGOPZUUKYGYMUULQYFYKYGYMEUKZOPZUULYGEULYMUUNQGEU
      MEUNRYGUUMGOGEUOUPUQURYLUULUUKYLUULUUKYLUULLZUUGODUUOUUFSZBUSAUSUUGOPUUOU
      UPABUUOUUEYQUUOUUEUUDCOUGZUUDCVBUULUUEUUQQYLUUDCGOUTTVAVCVDUUFABVEVFDVGVH
      VIYLUULSZVJGUJZUUKSZYKUURUUSVKZYHYJUVAYIYJUURUUSYJUURLZVJOVOZGVLUVBYJOGNZ
      UVCGUJYJUURVMYJUVDUURYJUVDGOVNUURGVPGOVQVRVSGOVTWFWAVITTYLUUSFOEUFZWBZUUG
      NZUVFDNZSZLUUTYLUUSUVGUVIYLUUSUVGYLUUSLZUVGFYPNZFYSPZUVEUUBPZLZCGUGZUVJUV
      KFYONZFFUJZUVJUVDUVPUVJVJGOYLUUSWCOVJNUVJWDWGWEZYKUVDUVPQYHUUSFGWHURWIUVJ
      FWJUVJYOWKZFWKZLZUVKUVPUVQLQYKUWAYHUUSYKUVSUVTYKYOMNUVSFGWLYOWMRYIUVTYJFW
      MZWNWOURYOFFWPRWQUVJUVDFFOUCUDZPZUVEUVEPZLZUVOUVRUVJUWDUWEUVJUWCFUVJYIUWC
      FPYKYIYHUUSYIYJVMZURZFWRRWSUVJUVEWTWOUVNUWFCOGYROPZUVLUWDUVMUWEUWIYSUWCFY
      ROFUCXAXBUWIUUBUVEUVEYROEXCXBXDXJXEUVJYIUVEXFNUVGUVKUVOLZQUWHUVJOEXGUUFUW
      JABFUVEMXFYNFPZUUAUVEPZLZYQUVKUUEUVOUWKYQUVKQUWLYNFYPXHWNUWMUUDUVNCGUWKYT
      UVLUWLUUCUVMYNFYSXIUUAUVEUUBXIXTXKXDXLXEWQVIYLUVHFDUKZNYLUWNFFYKFFNSZYHYI
      UWOYJYIUVTUWOUWBFXMRWNTYHUWNFPZYKYFUWPYGFDUOWNWNXNYLFUVEDMXFYKYIYHUWGTYLO
      EXGXOXPXQUVFUUGDXRXSYAYBUQUUGDYCVRYLUUJUUHDABCDEFGHIJKYDUPYE $.

    $( The concatentation with the empty series leaves the series unchanged.
       (Contributed by RP, 28-Feb-2025.) $)
    tfsconcat0i $p |- ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. On ) ) ->
                    ( A = (/) -> ( A .+ B ) = B ) ) $=
      ( wa con0 wcel c0 wceq coa co wb syl wfn cv cdif cfv wrex copab cun simpr
      cop cdm wrel fnrel reldm0 fndm eqeq1d bitrd ad2antrr anim12i anim1i oveq1
      sylbida id difeq12d dif0 eqtrdi eleq2d eqeq2d anbi1d rexbidv anbi12d oa0r
      weq onelon rexbidva wbr df-rex an12 eqcom anbi1i bitri exbii eleq1w fveq2
      wex equsexvw 3bitri baib adantl bitrdi fnbrfvb pm5.32da ex pm4.71rd df-br
      fnbr bitr3di sylan9bbr opabbidv opabid2 eqtrd uneq12d tfsconcatun sylibrd
      0un ) DFUAZEGUAZLZFMNZGMNZLZLZDOPZDAUBZFGQRZFUCZNZXMFCUBZQRZPZBUBZXQEUDZP
      ZLZCGUEZLZABUFZUGZEPZDEHRZEPXKXLYHXKXLLZYGOEUGEYJDOYFEXKXLUHYJYFXMXTUIENZ
      ABUFZEYJXFXILZFOPZLZYFYLPXKXLYNYOXEXLYNSXFXJXEXLDUJZOPZYNXEDUKXLYQSFDULDU
      MTXEYPFOFDUNUOUPUQXKYMYNXGXFXJXIXEXFUHXHXIUHURUSVAYOYEYKABYNYEXMOGQRZNZXM
      OXQQRZPZYBLZCGUEZLZYMYKYNXPYSYDUUCYNXOYRXMYNXOYROUCYRYNXNYRFOFOGQUTYNVBVC
      YRVDVEVFYNYCUUBCGYNXSUUAYBYNXRYTXMFOXQQUTVGVHVIVJXIUUDXMGNZACVLZYBLZCGUEZ
      LZXFYKXIYSUUEUUCUUHXIYRGXMGVKVFXIUUBUUGCGXIXQGNZLXQMNZUUBUUGSGXQVMUUKUUAU
      UFYBUUKYTXQXMXQVKVGVHTVNVJXFUUIUUEXMXTEVOZLZYKXFUUEUUHUULXFUUELZUUHXMEUDZ
      XTPZUULUUNUUHXTUUOPZUUPUUEUUHUUQSXFUUHUUEUUQUUHUUJUUGLZCWDCAVLZUUJYBLZLZC
      WDUUEUUQLZUUGCGVPUURUVACUURUUFUUTLUVAUUJUUFYBVQUUFUUSUUTXMXQVRVSVTWAUUTUV
      BCAUUSUUJUUEYBUUQCAGWBUUSYAUUOXTXQXMEWCVGVJWEWFWGWHXTUUOVRWIGXMXTEWJUPWKX
      FUULUUMYKXFUULUUEXFUULUUEGXMXTEWOWLWMXMXTEWNWPUPWQWQWRTXGYLEPZXJXLXFUVCXE
      XFEUKUVCGEULABEWSTWHUQWTXAEXDVEWLXKYIYGEABCDEFGHIJKXBUOXC $.

    $( The concatentation with the empty series leaves the finite series
       unchanged.  (Contributed by RP, 1-Mar-2025.) $)
    tfsconcat0b $p |- ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. _om ) ) ->
                        ( A = (/) <-> ( A .+ B ) = B ) ) $=
      ( wa wcel com c0 wceq wi syl wb adantr wfn con0 co anim2i tfsconcat0i cdm
      nnon dmeq coa nna0r adantl eqeq2d eqcom bitr3di wne on0eln0 df-ne bitr2di
      wn wss peano1 nnaordr mp3an1 biimpd ex a1i simpr oaword1 sstrd id eqeltrd
      ad2antlr sseldd a1d exp31 com23 word eloni ordom ordtri2or sylancl mpjaod
      wo imp elneq neneqd syl6 sylbid con4d tfsconcatfn fndmd fndm eqeq12d wrel
      fnrel reldm0 eqeq1d bitrd 3imtr4d syl5 impbid ) DFUAZEGUAZLZFUBMZGNMZLZLZ
      DOPZDEHUCZEPZXHXDXEGUBMZLZLZXIXKQXGXMXDXFXLXEGUGUDZUDZABCDEFGHIJKUERXKXJU
      FZEUFZPZXHXIXJEUHXHFGUIUCZGPZFOPZXSXIXGYAYBQXDXGYAOGUIUCZXTPZYBXGXTYCPYAY
      DXGYCGXTXFYCGPXEGUJZUKULXTYCUMUNXGYBYDXGYBUSZOFMZYDUSZXGYGFOUOZYFXEYGYISX
      FFUPTFOUQURXGYGYCXTMZYHXEXFYGYJQZXEFNMZXFYKQZNFUTZYLYMQXEYLXFYKYLXFLYGYJO
      NMYLXFYGYJSVAOFGVBVCVDVEVFXEXFYNYKXEXFYNYKXGYNLZYJYGYONXTYCYONFXTXGYNVGXG
      FXTUTZYNXGXMYPXOFGVHRTVIXFYCNMXEYNXFYCGNYEXFVJVKVLVMVNVOVPXEFVQNVQYLYNWCF
      VRVSFNVTWAWBWDYJYCXTYCXTWEWFWGWHWIWHUKXHXQXTXRGXHXTXJXHXNXJXTUAXPABCDEFGH
      IJKWJRWKXCXRGPXBXGGEWLVLWMXDXIYBSZXGXBYQXCXBXIDUFZOPZYBXBDWNXIYSSFDWODWPR
      XBYRFOFDWLWQWRTTWSWTXA $.

    $( The concatentation of two empty series results in an empty series.
       (Contributed by RP, 25-Feb-2025.) $)
    tfsconcat00 $p |- ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. On ) ) ->
                        ( ( A = (/) /\ B = (/) ) <-> ( A .+ B ) = (/) ) ) $=
      ( wfn wa crn c0 wceq wrel wb fnrel relrn0 con0 wcel co tfsconcatrn eqeq1d
      cun coa tfsconcatfn 3syl syl bi2anan9 un00 bitrdi adantr 3bitr4rd ) DFLZE
      GLZMZFUAUBGUAUBMZMZDEHUCZNZOPZDNZENZUFZOPZVAOPZDOPZEOPZMZUTVBVFOABCDEFGHI
      JKUDUEUTVAFGUGUCZLVAQVHVCRABCDEFGHIJKUHVLVASVATUIURVKVGRUSURVKVDOPZVEOPZM
      VGUPVIVMUQVJVNUPDQVIVMRFDSDTUJUQEQVJVNRGESETUJUKVDVEULUMUNUO $.

    $( If the domain of a transfinite sequence is an ordinal sum, the sequence
       can be decomposed into two sequences with domains corresponding to the
       addends.  Theorem 2 in Grzegorz Bancerek, "Epsilon Numbers and Cantor
       Normal Form", Formalized Mathematics, Vol. 17, No. 4, Pages
       249&ndash;256, 2009.  DOI: 10.2478/v10037-009-0032-8 (Contributed by RP,
       2-Mar-2025.) $)
    tfsconcatrev $p |- ( ( F Fn ( C +o D ) /\ ( C e. On /\ D e. On ) ) ->
                       E. u e. ( ran F ^m C ) E. v e. ( ran F ^m D )
                       ( ( u .+ v ) = F /\ dom u = C /\ dom v = D ) ) $=
      ( vd co con0 wcel wa cv wceq adantl coa wfn cres crn cmap cfv cdm w3a wss
      cmpt wrex wf dffn3 birani cvv wfun fndm adantr oacl eqeltrd fnfun funrnex
      elmapd mpbird oaword1 elmapssres syl2anc simpl oaordi ancoms imp fnfvelrn
      sylc wi syl2an2r fmpttd simprr cdif copab fnssresd fvex eqid fnmpti simpr
      cun a1i tfsconcatun syl21anc wbr oveq2 fveq2d fvmpt ad2antlr fveq2 eqtr4d
      weq eqeq2d biimpd expimpd rexlimdva simplr word eloni syl ordeldif biimpa
      wb ancomd jca oawordex2 eqcomd simpllr 3eqtr4rd ex reximdva impbid eldifi
      eqcom fnbrfvb bitrid syl2an bitrd pm5.32da opabbidv dfres2 eqtr4di uneq2d
      mpd eqtrd resundi undif sylib reseq2d fnresdm 3eqtr2d cin sseqtrrd eqeq1d
      dmres dmeq dfss2 eqtrid dmmpti oveq1 3anbi12d 3anbi13d rspc2ev syl113anc
      ) IFGUANZUBZFOPZGOPZQZQZIFUCZIUDZFUENZPZMGFMRZUANZIUFZUJZUUPGUENZPZUUOUVB
      HNZISZUUOUGZFSZUVBUGZGSZERZDRZHNZISZUVKUGZFSZUVLUGZGSZUHZDUVCUKEUUQUKUUNI
      UUPUUIUENPZFUUIUIZUURUUNUVTUUIUUPIULZUUJUWBUUMUUIIUMUNUUNUUPUUIIUOOUUNIUG
      ZOPIUPZUUPUOPUUNUWCUUIOUUJUWCUUISUUMUUIIUQURZUUMUUIOPZUUJFGUSZTZUTUUJUWDU
      UMUUIIVAUROIVBVMZUWHVCVDUUMUWAUUJFGVEZTZIUUPUUIFVFVGUUNUVDGUUPUVBULUUNMGU
      VAUUPUUNUUJUUSGPZUUTUUIPZUVAUUPPUUJUUMVHZUUNUWLUWMUUMUWLUWMVNZUUJUULUUKUW
      OUUSGFVIVJTVKUUIUUTIVLVOVPUUNUUPGUVBUOOUWIUUJUUKUULVQVCVDUUNUVEUUOIUUIFVR
      ZUCZWEZIFUWPWEZUCZIUUNUVEUUOARZUWPPZUXAFCRZUANZSZBRZUXCUVBUFZSZQZCGUKZQZA
      BVSZWEZUWRUUNUUOFUBUVBGUBZUUMUVEUXMSUUNUUIFIUWNUWKVTUXNUUNMGUVAUVBUUTIWAZ
      UVBWBZWCWFUUJUUMWDABCUUOUVBFGHJKLWGWHUUNUXLUWQUUOUUNUXLUXBUXAUXFIWIZQZABV
      SUWQUUNUXKUXRABUUNUXBUXJUXQUUNUXBQZUXJUXFUXAIUFZSZUXQUXSUXJUYAUXSUXIUYACG
      UXSUXCGPZQZUXEUXHUYAUYCUXEQZUXHUYAUYDUXGUXTUXFUYDUXGUXDIUFZUXTUYBUXGUYESZ
      UXSUXEMUXCUVAUYEGUVBMCWPUUTUXDIUUSUXCFUAWJWKUXPUXDIWAWLZWMUXEUXTUYESUYCUX
      AUXDIWNTWOWQWRWSWTUXSUYAUXJUXSUYAQZUXDUXASZCGUKZUXJUYHUUMFUXAUIZUXAUUIPZQ
      ZQZUYJUXSUYNUYAUXSUUMUYMUUJUUMUXBXAUXSUYLUYKUUNUXBUYLUYKQZUUMUXBUYOXGZUUJ
      UUMUUIXBZFXBZUYPUUMUWFUYQUWGUUIXCXDUUKUYRUULFXCURUUIFUXAXEVGTXFXHXIURCFGU
      XAXJXDUYHUYIUXICGUYHUYBQZUYIUXIUYSUYIQZUXEUXHUYTUXDUXAUYSUYIWDZXKUYTUYEUX
      TUXGUXFUYTUXDUXAIVUAWKUYBUYFUYHUYIUYGWMUXSUYAUYBUYIXLXMXIXNXOYHXNXPUUNUUJ
      UYLUYAUXQXGUXBUWNUXAUUIFXQUYAUXTUXFSUUJUYLQUXQUXFUXTXRUUIUXAUXFIXSXTYAYBY
      CYDABUWPIYEYFYGYIUWTUWRSUUNIFUWPYJWFUUNUWTIUUIUCZIUUNUWSUUIIUUMUWSUUISZUU
      JUUMUWAVUCUWJFUUIYKYLTYMUUJVUBISUUMUUIIYNURYIYOUUNUVGFUWCYPZFIFYSUUNFUWCU
      IVUDFSUUNFUUIUWCUWKUWEYQFUWCUUAYLUUBUVJUUNMGUVAUVBUXOUXPUUCWFUVSUVFUVHUVJ
      UHUUOUVLHNZISZUVHUVRUHEDUUOUVBUUQUVCUVKUUOSZUVNVUFUVPUVHUVRVUGUVMVUEIUVKU
      UOUVLHUUDYRVUGUVOUVGFUVKUUOYTYRUUEUVLUVBSZVUFUVFUVRUVJUVHVUHVUEUVEIUVLUVB
      UUOHWJYRVUHUVQUVIGUVLUVBYTYRUUFUUGUUH $.

    $( The range of the concatenation of transfinite sequences is a superset of
       the ranges of both sequences.  Theorem 3 in Grzegorz Bancerek, "Epsilon
       Numbers and Cantor Normal Form", Formalized Mathematics, Vol. 17, No. 4,
       Pages 249&ndash;256, 2009.  DOI: 10.2478/v10037-009-0032-8 (Contributed
       by RP, 2-Mar-2025.) $)
    tfsconcatrnss12 $p |- ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. On ) )
                          -> ( ran A C_ ran ( A .+ B )
                            /\ ran B C_ ran ( A .+ B ) ) ) $=
      ( wfn wa con0 wcel co crn cun wss sseqtrrid wceq tfsconcatrn ssun1 id jca
      ssun2 syl ) DFLEGLMFNOGNOMMDEHPQZDQZEQZRZUAZUIUHSZUJUHSZMABCDEFGHIJKUBULU
      MUNULUKUIUHUIUJUCULUDZTULUKUJUHUJUIUFUOTUEUG $.

    $( The concatenation of transfinite sequences yields elements from a class
       iff both sequences yield elements from that class.  (Contributed by RP,
       2-Mar-2025.) $)
    tfsconcatrnss $p |- ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. On ) )
           -> ( ran ( A .+ B ) C_ X <-> ( ran A C_ X /\ ran B C_ X ) ) ) $=
      ( wfn wa con0 wcel co crn wss cun tfsconcatrn sseq1d unss bitr4di ) DFMEG
      MNFOPGOPNNZDEHQRZISDRZERZTZISUGISUHISNUEUFUIIABCDEFGHJKLUAUBUGUHIUCUD $.

    $( The concatenation of transfinite sequences yields ordinals iff both
       sequences yield ordinals.  Theorem 4 in Grzegorz Bancerek, "Epsilon
       Numbers and Cantor Normal Form", Formalized Mathematics, Vol. 17, No. 4,
       Pages 249&ndash;256, 2009.  DOI: 10.2478/v10037-009-0032-8 (Contributed
       by RP, 2-Mar-2025.) $)
    tfsconcatrnsson $p |- ( ( ( A Fn C /\ B Fn D ) /\ ( C e. On /\ D e. On ) )
           -> ( ran ( A .+ B ) C_ On <-> ( ran A C_ On /\ ran B C_ On ) ) ) $=
      ( con0 tfsconcatrnss ) ABCDEFGHLIJKM $.
  $}

  ${
    $( A transfinite sequence is infinite iff its domain is greater than or
       equal to omega.  Theorem 5 in Grzegorz Bancerek, "Epsilon Numbers and
       Cantor Normal Form", Formalized Mathematics, Vol. 17, No. 4, Pages
       249&ndash;256, 2009.  DOI: 10.2478/v10037-009-0032-8 (Contributed by RP,
       1-Mar-2025.) $)
    tfsnfin $p |- ( ( A Fn B /\ B e. On ) -> ( -. A e. Fin <-> _om C_ B ) ) $=
      ( wfn con0 wcel wa cfn wn com wss cdm wfun wb fnfun fundmfibi fndm eleq1d
      syl bitrd onfin sylan9bb notbid omelon simpr ontri1 sylancr bitr4d ) ABCZ
      BDEZFZAGEZHBIEZHZIBJZUJUKULUHUKBGEZUIULUHUKAKZGEZUOUHALUKUQMBANAORUHUPBGB
      APQSBTUAUBUJIDEUIUNUMMUCUHUIUDIBUEUFUG $.
  $}

  ${
    $d A x $.  $d B x $.
    $( The limit of a sequence of ordinals is the union of its range.
       (Contributed by RP, 1-Mar-2025.) $)
    rp-tfslim $p |- ( A Fn B -> U_ x e. B ( A ` x ) = U. ran A ) $=
      ( wfn cfv ciun cmpt crn cuni fvex dfiun3 wceq dffn5 biimpi unieqd eqtr4id
      cv rneqd ) BCDZACAQZBEZFACUAGZHZIBHZIACUATBJKSUDUCSBUBSBUBLACBMNROP $.
  $}

  ${
    $d A c f g $.  $d B c f g $.  $d C c d f g $.  $d D c d f g $.
    $d E c d f g $.  $d F c f g $.  $d V c f g $.  $d W c f g $.
    $( Addition operator for functions from sets into ordinals results in a
       function from the intersection of sets into an ordinal.  (Contributed by
       RP, 5-Jan-2025.) $)
    ofoafg $p |- ( ( ( A e. V /\ B e. W /\ C = ( A i^i B ) ) /\
                     ( D e. On /\ E e. On /\ F = U_ d e. D ( d +o E ) ) )
                 -> ( oF +o |` ( ( D ^m A ) X. ( E ^m B ) ) )
                 : ( ( D ^m A ) X. ( E ^m B ) ) --> ( F ^m C ) ) $=
      ( vf wcel wceq con0 coa co wa wf wfn adantl ad2antrr vg vc cin w3a cv cof
      ciun cmap wral cxp cres wb simp1 elmapg syl2anr simp2 adantr crn wss ffnd
      simpl simpr eqid offn simp3 fneq2d mpbird cfv fresin inss1 eqsstrdi sylib
      sseqin2 feq2d mpbid ffvelcdmda ad3antlr onelon syl2anc inss2 imp syl21anc
      oaordi oveq1 eliuni reseq2d oveq12d eqtr4d fveq1d cvv fnssresd jca inex1g
      ofres syl eqeltrd anim1i fnfvof syl2an2r eqtrd 3eltr4d ralrimiva fnfvrnss
      sylan2 expcom jcai adantlr oacl iunon syldan 3adant3 elmapd bitrdi sylbid
      df-f expr ralrimiv ex ofmres fmpo ) AGKZBHKZCABUCZLZUDZDMKZEMKZFIDIUEZENO
      ZUGZLZUDZPZJUEZUAUEZNUFZOZFCUHOZKZUAEBUHOZUIZJDAUHOZUIUUBYTUJZYRYPUUCUKZQ
      YMUUAJUUBYMYNUUBKZADYNQZUUAYLYFYAUUEUUFULYEYFYGYKUMZYAYBYDUMZDAYNMGUNUOYM
      UUFUUAYMUUFPZYSUAYTUUIYOYTKZBEYOQZYSYMUUJUUKULZUUFYLYGYBUULYEYFYGYKUPZYAY
      BYDUPZEBYOMHUNUOUQYMUUFUUKYSYMUUFUUKPZPZYSYQCRZYQURFUSZPZUUPUUQUURUUPUUQY
      QYCRZUUPABNYCYNYOGHUUOYNARYMUUOADYNUUFUUKVAUTSZUUOYOBRYMUUOBEYOUUFUUKVBUT
      SZYEYAYLUUOUUHTZYEYBYLUUOUUNTZYCVCZVDYEUUQUUTULYLUUOYECYCYQYAYBYDVEZVFTVG
      UUQUUPUURUUPUUQUBUEZYQVHZFKZUBCUIUURUUPUVIUBCUUPUVGCKZPZUVGYNCUKZVHZUVGYO
      CUKZVHZNOZYJUVHFUVKUVMDKZUVPUVMENOZKZUVPYJKUUPCDUVGUVLUUPACUCZDUVLQZCDUVL
      QUUOUWAYMUUFUWAUUKADYNCVIUQSUUPUVTCDUVLYEUVTCLZYLUUOYECAUSZUWBYECYCAUVFAB
      VJVKZCAVMVLTVNVOVPZUVKYGUVMMKZUVOEKZUVSYLYGYEUUOUVJUUMVQUVKYFUVQUWFYLYFYE
      UUOUVJUUGVQUWEDUVMVRVSUUPCEUVGUVNUUPBCUCZEUVNQZCEUVNQUUOUWIYMUUKUWIUUFBEY
      OCVISSUUPUWHCEUVNYEUWHCLZYLUUOYECBUSZUWJYECYCBUVFABVTVKZCBVMVLTVNVOVPYGUW
      FPUWGUVSUVOEUVMWCWAWBIUVMYIUVRDUVPYHUVMENWDWEVSUVKUVHUVGUVLUVNYPOZVHZUVPU
      UPUVHUWNLUVJUUPUVGYQUWMUUPYQYNYCUKZYOYCUKZYPOZUWMUUPABYCNYNYOGHUVAUVBUVCU
      VDUVEWNYEUWMUWQLYLUUOYEUVLUWOUVNUWPYPYECYCYNUVFWFYECYCYOUVFWFWGTWHWIUQUUP
      UVLCRZUVNCRZPUVJCWJKZUVJPUWNUVPLUUPUWRUWSUUPACYNUVAYEUWCYLUUOUWDTWKUUPBCY
      OUVBYEUWKYLUUOUWLTWKWLUUPUWTUVJYEUWTYLUUOYECYCWJUVFYEYAYCWJKUUHABGWMWOWPT
      ZWQCNUVLUVNWJUVGWRWSWTYLYKYEUUOUVJYFYGYKVEZVQXAXBUBCFYQXCXDXEXFUUPYSCFYQQ
      UUSUUPFCYQMWJYMFMKZUUOYLUXCYEYLFYJMUXBYFYGYJMKZYKYFYGYIMKZIDUIUXDYFYGPZUX
      EIDUXFYHDKZPYHMKZYGUXEYFUXGUXHYGDYHVRXGUXFYGUXGYFYGVBUQYHEXHVSXBIDYIMXIXJ
      XKWPSUQUXAXLCFYQXOXMVGXPXNXQXRXNXQJUAUUBYTYQYRUUDUUBYTNJUAXSXTVL $.
  $}

  ${
    $d C x $.  $d D x $.  $d E x $.
    $( Addition operator for functions from sets into power of omega results in
       a function from the intersection of sets to that power of omega.
       (Contributed by RP, 5-Jan-2025.) $)
    ofoaf $p |- ( ( ( A e. V /\ B e. W /\ C = ( A i^i B ) ) /\
                     ( D e. On /\ E = ( _om ^o D ) ) )
                 -> ( oF +o |` ( ( E ^m A ) X. ( E ^m B ) ) )
                 : ( ( E ^m A ) X. ( E ^m B ) ) --> ( E ^m C ) ) $=
      ( vx con0 wcel com co wceq wa w3a coa cmap omelon wss c0 coe cin ciun cxp
      cv cof cres wf simpr simpl oecl sylancr eqeltrd wrex jctil peano1 sylancl
      oen0 eleqtrrd oveq1 sseq2d adantl oa0r syl ssid eqsstrrdi rspcedvd eleq2d
      wb ssiun biimpa adantr oaabs2 syl21anc eqsstrdi iunssd 3jca ofoafg sylan2
      eqssd ) DIJZEKDUALZMZNZAFJBGJCABUBMOEIJZWEEHEHUEZEPLZUCZMZOEAQLEBQLUDZECQ
      LPUFWJUGUHWDWEWEWIWDEWBIWAWCUIZWDKIJZWAWBIJRWAWCUJZKDUKULUMZWNWDEWHWDEWGS
      ZHEUNEWHSWDWOETEPLZSZHTEWDTWBEWDWLWANTKJTWBJWDWAWLWMRUOUPKDURUQWKUSWFTMZW
      OWQVIWDWRWGWPEWFTEPUTVAVBWDEWPWPWDWEWPEMWNEVCVDWPVEVFVGHEWGEVJVDWDHEWGEWD
      WFEJZNZWGEEWTWFWBJZWEWBESWGEMWDWSXAWDEWBWFWKVHVKWDWEWSWNVLWTWBEEWDWCWSWKV
      LEVEZVFWFEDVMVNXBVOVPVTVQABCEEEFGHVRVS $.
  $}

  ${
    $d A a f h z $.  $d B a h $.  $d C a f h z $.  $d V a h $.
    $( Addition operator for functions from a set into a power of omega is an
       onto binary operator.  (Contributed by RP, 5-Jan-2025.) $)
    ofoafo $p |- ( ( A e. V /\ ( B e. On /\ C = ( _om ^o B ) ) )
                 -> ( oF +o |` ( ( C ^m A ) X. ( C ^m A ) ) )
                 : ( ( C ^m A ) X. ( C ^m A ) ) -onto-> ( C ^m A ) ) $=
      ( vh vf vz wcel con0 com co wceq wa coa wf cv c0 syl adantl adantr va coe
      cmap cxp cof cres wrex wral wfo cin w3a inidm eqcomi a1i 3jca ofoaf sylan
      id simpr csn omelon simpl jca oen0 sylancl eleqtrrd fconst6g oecl sylancr
      peano1 eqeltrd elmapd mpbird ovres wfn elmapi ffnd elmapfn anim12i anim1i
      offn cfv fnfvof syl2an2r fvconst2g oveq2d onss ad2antrl ffvelcdmda sseldd
      wss oa0 3eqtrd eqfnfvd eqtr2d expr jcai oveq2 rspceeqv weq eqeq2d rexbidv
      oveq1 rspcev ralrimiva foov sylanbrc ) ADHZBIHZCJBUBKZLZMZMZCAUCKZXNUDZXN
      NUEZXOUFZOZEPZFPZGPZXQKZLZGXNUGZFXNUGZEXNUHXOXNXQUIXHXHXHAAAUJZLZUKXLXRXH
      XHXHYGXHURZYHYGXHYFAAULZUMUNUOAAABCDDUPUQXMYEEXNXMXSXNHZMZYJXSXSYAXQKZLZG
      XNUGZMYEYKYJYNXMYJUSYKAQUTUDZXNHZXSXSYOXQKZLZMYNYKYPYRXMYPYJXMYPACYOOZXLY
      SXHXLQCHYSXLQXJCXLJIHZXIMQJHZQXJHXLYTXIYTXLVAUNXIXKVBZVCVJJBVDVEXIXKUSZVF
      AQCVGRSXMCAYOIDXLCIHZXHXLCXJIUUCXLYTXIXJIHVAUUBJBVHVIVKSZXHXLVBZVLVMTXMYJ
      YPYRXMYJYPMZMZYQXSYOXPKZXSUUGYQUUILXMXSYOXNXNXPVNSUUHUAAUUIXSUUHAANAXSYOD
      DUUGXSAVOZXMUUGACXSYJACXSOZYPXSCAVPZTVQSZUUGYOAVOZXMUUGACYOYPYSYJYOCAVPSV
      QSXMXHUUGUUFTZUUOYIWAUUMUUHUAPZAHZMZUUPUUIWBZUUPXSWBZUUPYOWBZNKZUUTQNKZUU
      TUUHUUJUUNMZUUQXHUUQMUUSUVBLUUGUVDXMYJUUJYPUUNXSCAVRYOCAVRVSSUUHXHUUQUUOV
      TANXSYODUUPWCWDUURUVAQUUTNUURUUAUUQUVAQLVJUUHUUQUSAQUUPJWEVIWFUURUUTIHUVC
      UUTLUURCIUUTUURUUDCIWKUUHUUDUUQXMUUDUUGUUETTCWGRUUHACUUPXSYJUUKXMYPUULWHW
      IWJUUTWLRWMWNWOWPWQGYOXNYLYQXSYAYOXSXQWRWSRVCYDYNFXSXNFEWTZYCYMGXNUVEYBYL
      XSXTXSYAXQXCXAXBXDRXEFGEXNXNXNXQXFXG $.
  $}

  $( Closure law for component wise addition of ordinal-yielding functions.
     (Contributed by RP, 5-Jan-2025.) $)
  ofoacl $p |- ( ( ( A e. V /\ ( B e. On /\ C = ( _om ^o B ) ) ) /\
                 ( F e. ( C ^m A ) /\ G e. ( C ^m A ) ) ) ->
                 ( F oF +o G ) e. ( C ^m A ) ) $=
    ( wcel con0 com coe co wceq wa cmap coa cof cxp cres ovres adantl cin wf id
    w3a inidm a1i eqcomd 3jca ofoaf sylan fovcdmda eqeltrrd ) AFGZBHGCIBJKLMZMZ
    DCANKZGEUPGMZMDEOPZUPUPQZRZKZDEURKZUPUQVAVBLUODEUPUPURSTUODEUPUPUPUTUMUMUMA
    AAUAZLZUDUNUSUPUTUBUMUMUMVDUMUCZVEUMVCAVCALUMAUEUFUGUHAAABCFFUIUJUKUL $.

  ${
    $d A a $.  $d F a $.  $d V a $.
    $( Identity law for component wise addition of ordinal-yielding functions.
       (Contributed by RP, 5-Jan-2025.) $)
    ofoaid1 $p |- ( ( ( A e. V /\ B e. On ) /\ F e. ( B ^m A ) )
                 -> ( F oF +o ( A X. { (/) } ) ) = F ) $=
      ( va wcel con0 wa co wf c0 wfn coa wceq wss syl df-f com peano1 cfv impel
      cmap csn cxp cof simpll wi onss sstr expcom anim2d 3imtr4g elmapi adantll
      crn fnconstg mp1i w3a simp2 ffnd simp3 simp1 inidm offn jca adantr fnfvof
      cv simpr syl12anc fvconst2g sylancr oveq2d ffvelcdmda oa0 eqfnfvd syl3anc
      3eqtrd ) ADFZBGFZHCBAUBIFZHZVSAGCJZAKUCUDZALZCWDMUEIZCNVSVTWAUFVTWAWCVSVT
      ABCJZWCWAVTCALZCUOZBOZHWHWIGOZHWGWCVTWJWKWHVTBGOZWJWKUGBUHWJWLWKWIBGUIUJP
      UKABCQAGCQULCBAUMUAUNKRFZWEWBSAKRUPUQVSWCWEURZEAWFCWNAAMACWDDDWNAGCVSWCWE
      USZUTZVSWCWEVAZVSWCWEVBZWRAVCVDWPWNEVHZAFZHZWSWFTZWSCTZWSWDTZMIZXCKMIZXCX
      AWHWEHZVSWTXBXENWNXGWTWNWHWEWPWQVEVFWNVSWTWRVFWNWTVIZAMCWDDWSVGVJXAXDKXCM
      XAWMWTXDKNSXHAKWSRVKVLVMXAXCGFXFXCNWNAGWSCWOVNXCVOPVRVPVQ $.
  $}

  ${
    $d A a $.  $d F a $.  $d V a $.
    $( Identity law for component wise addition of ordinal-yielding functions.
       (Contributed by RP, 5-Jan-2025.) $)
    ofoaid2 $p |- ( ( ( A e. V /\ B e. On ) /\ F e. ( B ^m A ) )
                 -> ( ( A X. { (/) } ) oF +o F ) = F ) $=
      ( va wcel con0 wa co wf c0 wfn coa wceq wss syl df-f com peano1 cfv impel
      cmap csn cxp cof simpll wi onss sstr expcom anim2d 3imtr4g elmapi adantll
      crn fnconstg mp1i w3a simp3 simp2 ffnd simp1 inidm offn jca adantr fnfvof
      cv simpr syl12anc fvconst2g sylancr oveq1d ffvelcdmda oa0r 3eqtrd eqfnfvd
      syl3anc ) ADFZBGFZHCBAUBIFZHZVSAGCJZAKUCUDZALZWDCMUEIZCNVSVTWAUFVTWAWCVSV
      TABCJZWCWAVTCALZCUOZBOZHWHWIGOZHWGWCVTWJWKWHVTBGOZWJWKUGBUHWJWLWKWIBGUIUJ
      PUKABCQAGCQULCBAUMUAUNKRFZWEWBSAKRUPUQVSWCWEURZEAWFCWNAAMAWDCDDVSWCWEUSZW
      NAGCVSWCWEUTZVAZVSWCWEVBZWRAVCVDWQWNEVHZAFZHZWSWFTZWSWDTZWSCTZMIZKXDMIZXD
      XAWEWHHZVSWTXBXENWNXGWTWNWEWHWOWQVEVFWNVSWTWRVFWNWTVIZAMWDCDWSVGVJXAXCKXD
      MXAWMWTXCKNSXHAKWSRVKVLVMXAXDGFXFXDNWNAGWSCWPVNXDVOPVPVQVR $.
  $}

  ${
    $d A a $.  $d B a $.  $d F a $.  $d G a $.  $d H a $.  $d V a $.
    $( Component-wise addition of ordinal-yielding functions is associative.
       (Contributed by RP, 5-Jan-2025.) $)
    ofoaass $p |- ( ( ( A e. V /\ B e. On ) /\
                  ( F e. ( B ^m A ) /\ G e. ( B ^m A ) /\ H e. ( B ^m A ) ) )
                  -> ( ( F oF +o G ) oF +o H ) = ( F oF +o ( G oF +o H ) ) ) $=
      ( wcel con0 wa co coa wfn elmapfn adantl offn cfv wceq wf elmapi fnfvof
      va cmap w3a 3ad2ant1 3ad2ant2 simpll inidm 3ad2ant3 cv simpllr ffvelcdmda
      cof onelon syl2anc oaass syl3anc adantr anim1i syl21anc oveq1d jca oveq2d
      syl2an2r 3eqtr4d eqfnfvd ) AFGZBHGZIZCBAUBJZGZDVIGZEVIGZUCZIZUAACDKULZJZE
      VOJZCDEVOJZVOJZVNAAKAVPEFFVNAAKACDFFVMCALZVHVJVKVTVLCBAMUDNZVMDALZVHVKVJW
      BVLDBAMUENZVFVGVMUFZWDAUGZOZVMEALZVHVLVJWGVKEBAMUHNZWDWDWEOVNAAKACVRFFWAV
      NAAKADEFFWCWHWDWDWEOZWDWDWEOVNUAUIZAGZIZWJVPPZWJEPZKJZWJCPZWJVRPZKJZWJVQP
      ZWJVSPZWLWPWJDPZKJZWNKJZWPXAWNKJZKJZWOWRWLWPHGZXAHGZWNHGZXCXEQWLVGWPBGXFV
      FVGVMWKUJZVNABWJCVMABCRZVHVJVKXJVLCBASUDNUKBWPUMUNWLVGXABGXGXIVNABWJDVMAB
      DRZVHVKVJXKVLDBASUENUKBXAUMUNWLVGWNBGXHXIVNABWJEVMABERZVHVLVJXLVKEBASUHNU
      KBWNUMUNWPXAWNUOUPWLWMXBWNKWLVTWBVFWKIZWMXBQVNVTWKWAUQVNWBWKWCUQVNVFWKWDU
      RZAKCDFWJTUSUTWLWQXDWPKVNWBWGIWKXMWQXDQVNWBWGWCWHVAXNAKDEFWJTVCVBVDVNVPAL
      ZWGIWKXMWSWOQVNXOWGWFWHVAXNAKVPEFWJTVCVNVTVRALZIWKXMWTWRQVNVTXPWAWIVAXNAK
      CVRFWJTVCVDVE $.
  $}

  ${
    $d A a $.  $d F a $.  $d G a $.  $d V a $.
    $( Component-wise addition of natural numnber-yielding functions commutes.
       (Contributed by RP, 5-Jan-2025.) $)
    ofoacom $p |- ( ( A e. V /\ ( F e. ( _om ^m A ) /\ G e. ( _om ^m A ) ) ) ->
                    ( F oF +o G ) = ( G oF +o F ) ) $=
      ( va wcel com co wa coa wfn elmapfn ad2antrl ad2antll offn wceq wf elmapi
      cfv ffvelcdmda cmap cof simpl inidm cv nnacom syl2anc jca anim1i syl2an2r
      fnfvof 3eqtr4d eqfnfvd ) ADFZBGAUAHZFZCUOFZIZIZEABCJUBZHZCBUTHZUSAAJABCDD
      UPBAKZUNUQBGALMZUQCAKZUNUPCGALNZUNURUCZVGAUDZOUSAAJACBDDVFVDVGVGVHOUSEUEZ
      AFZIZVIBSZVICSZJHZVMVLJHZVIVASZVIVBSZVKVLGFVMGFVNVOPUSAGVIBUPAGBQUNUQBGAR
      MTUSAGVICUQAGCQUNUPCGARNTVLVMUFUGUSVCVEIVJUNVJIZVPVNPUSVCVEVDVFUHUSUNVJVG
      UIZAJBCDVIUKUJUSVEVCIVJVRVQVOPUSVEVCVFVDUHVSAJCBDVIUKUJULUM $.
  $}

  ${
    $d S f g $.  $d X f g x $.
    $( Addition operator for Cantor normal forms is a function into Cantor
       normal forms.  (Contributed by RP, 2-Jan-2025.) $)
    naddcnff $p |- ( ( X e. On /\ S = dom ( _om CNF X ) )
                     -> ( oF +o |` ( S X. S ) ) : ( S X. S ) --> S ) $=
      ( vf vg vx con0 wcel com co wceq wa cv coa wral wf c0 simpl adantr ffnd
      ex ccnf cdm cof cxp cres cfsupp wbr simpr eleq2d omelon a1i cantnfs bitrd
      eqid anim12i anassrs wfn crn wss simprl simprr inidm offn simplrl simplrr
      wb cfv simpll syl22anc ffvelcdmda nnacl syl2anc eqeltrd ralrimiv fnfvrnss
      fnfvof jcai df-f sylibr syl wfun csupp cfn ffun adantl cun simp-4l peano1
      fsuppunfi 0elon oa0 mp1i suppofssd ssfid ovexd isfsupp mpbir2and ad2antrr
      cvv sylancl mpbird sylbid ofmres fmpo sylib ) BFGZAHBUAIUBZJZKZCLZDLZMUCZ
      IZAGZDANZCANAAUDZAXLXPUEZOXIXOCAXIXJAGZBHXJOZXJPUFUGZKZXOXIXRXJXGGYAXIAXG
      XJXFXHUHZUIXIHBXGXJXGUNZHFGXIUJUKZXFXHQZULUMXIYAXOXIYAKZXNDAYFXKAGZBHXKOZ
      XKPUFUGZKZXNXIYGYJVFYAXIYGXKXGGYJXIAXGXKYBUIXIHBXGXKYCYDYEULUMRYFYJXNYFYJ
      KZXNBHXMOZXMPUFUGZKZYKYLYMYKXFXSYHKZKZYLXIYAYJYPXIXFYAYJKYOYEYAXSYJYHXSXT
      QYHYIQUOUOUPYPXMBUQZXMURHUSZKYLYPYQYRYPBBMBXJXKFFYPBHXJXFXSYHUTZSYPBHXKXF
      XSYHVAZSXFYOQZUUABVBVCYPYQYRYPYQKYQELZXMVGZHGZEBNZYRYPYQUHYPUUEYQYPUUDEBY
      PUUBBGZUUDYPUUFKZUUCUUBXJVGZUUBXKVGZMIZHUUGXJBUQXKBUQXFUUFUUCUUJJUUGBHXJX
      FXSYHUUFVDSUUGBHXKXFXSYHUUFVESXFYOUUFVHYPUUFUHBMXJXKFUUBVPVIUUGUUHHGUUIHG
      UUJHGYPBHUUBXJYSVJYPBHUUBXKYTVJUUHUUIVKVLVMTVNREBHXMVOVLTVQBHXMVRVSVTYKYL
      YMYKYLKZYMXMWAZXMPWBIZWCGZYLUULYKBHXMWDWEUUKXJPWBIXKPWBIWFUUMUUKXJXKPYKXT
      YLXIXSXTYJVERYFYHYIYLVEWIUUKBHXJXKFMPXFXHYAYJYLWGPHGUUKWHUKYKXSYLXIXSXTYJ
      VDRYFYHYIYLVDPFGZPPMIPJUUKWJPWKWLWMWNUUKXMWSGUUOYMUULUUNKVFUUKXJXKXLWOWJX
      MWSFPWPWTWQTVQXIXNYNVFYAYJXIXNXMXGGYNXIAXGXMYBUIXIHBXGXMYCYDYEULUMWRXATXB
      VNTXBVNCDAAXMAXQAAMCDXCXDXE $.
  $}

  $( Addition operator for Cantor normal forms is a function.  (Contributed by
     RP, 2-Jan-2025.) $)
  naddcnffn $p |- ( ( X e. On /\ S = dom ( _om CNF X ) )
                    -> ( oF +o |` ( S X. S ) ) Fn ( S X. S ) ) $=
    ( con0 wcel com ccnf co cdm wceq wa cxp coa cof cres naddcnff ffnd ) BCDAEB
    FGHIJAAKZALMQNABOP $.

  ${
    $d S f g z $.  $d S f x $.  $d X f z $.  $d X f x $.
    $( Addition of Cantor normal forms is a function onto Cantor normal forms.
       (Contributed by RP, 2-Jan-2025.) $)
    naddcnffo $p |- ( ( X e. On /\ S = dom ( _om CNF X ) )
                     -> ( oF +o |` ( S X. S ) ) : ( S X. S ) -onto-> S ) $=
      ( vf vg vz con0 wcel com co wceq wa wf cv wrex simpr c0 peano1 mp1i simpl
      coa ccnf cdm cxp cof cres wral wfo naddcnff csn cfsupp fconst6g fczfsuppd
      vx wbr a1i eleq2d eqid omelon bitrd mpbir2and adantr adantl ovresd biimpd
      cantnfs syl56 imp ffnd wfn fnconstg inidm offn simplll syl22anc fvconst2g
      cfv fnfvof syl2anc oveq2d ffvelcdmda nnon 3syl 3eqtrd eqfnfvd eqtr2d expr
      oa0 oveq2 rspceeqv syl weq oveq1 eqeq2d rexbidv rspcev ralrimiva sylanbrc
      jcai foov ) BFGZAHBUAIUBZJZKZAAUCZATUDZXDUEZLCMZDMZEMZXFIZJZEANZDANZCAUFX
      DAXFUGABUHXCXMCAXCXGAGZKZXNXGXGXIXFIZJZEANZXMXCXNOXOBPUIUCZAGZXGXGXSXFIZJ
      ZKXRXOXTYBXCXTXNXCXTBHXSLZXSPUJUNZPHGZYCXCQBPHUKRXCBFHPWTXBSZYEXCQUOULXCX
      TXSXAGYCYDKXCAXAXSWTXBOZUPXCHBXAXSXAUQZHFGXCURUOZYFVEUSUTVAXCXNXTYBXCXNXT
      KZKZYAXGXSXEIZXGYKXGXSXEAYJXNXCXNXTSZVBYJXTXCXNXTOVBVCYKUMBYLXGYKBBTBXGXS
      FFYKBHXGXCYJBHXGLZYJXNXCYNXGPUJUNZKZYNYMXCXNYPXCXNXGXAGYPXCAXAXGYGUPXCHBX
      AXGYHYIYFVEUSVDYNYOSVFVGZVHZYEXSBVIZYKQBPHVJZRXCWTYJYFVAZUUABVKVLYRYKUMMZ
      BGZKZUUBYLVPZUUBXGVPZUUBXSVPZTIZUUFPTIZUUFUUDXGBVIZYSWTUUCUUEUUHJYKUUJUUC
      YRVAYEYSUUDQYTRWTXBYJUUCVMYKUUCOZBTXGXSFUUBVQVNUUDUUGPUUFTUUDYEUUCUUGPJYE
      UUDQUOUUKBPUUBHVOVRVSUUDUUFHGUUFFGUUIUUFJYKBHUUBXGYQVTUUFWAUUFWGWBWCWDWEW
      FWREXSAXPYAXGXIXSXGXFWHWIWJXLXRDXGADCWKZXKXQEAUULXJXPXGXHXGXIXFWLWMWNWOVR
      WPDECAAAXFWSWQ $.
  $}

  $( Closure law for component-wise ordinal addition of Cantor normal forms.
     (Contributed by RP, 2-Jan-2025.) $)
  naddcnfcl $p |- ( ( ( X e. On /\ S = dom ( _om CNF X ) ) /\
                    ( F e. S /\ G e. S ) ) -> ( F oF +o G ) e. S ) $=
    ( con0 wcel com ccnf co cdm wceq coa cof cxp ovres adantl naddcnff fovcdmda
    wa cres eqeltrrd ) DEFAGDHIJKSZBAFCAFSZSBCLMZAANTZIZBCUDIZAUCUFUGKUBBCAAUDO
    PUBBCAAAUEADQRUA $.

  ${
    $d F x $.  $d G x $.  $d S x $.  $d X x $.
    $( Component-wise ordinal addition of Cantor normal forms commutes.
       (Contributed by RP, 2-Jan-2025.) $)
    naddcnfcom $p |- ( ( ( X e. On /\ S = dom ( _om CNF X ) ) /\
                   ( F e. S /\ G e. S ) ) -> ( F oF +o G ) = ( G oF +o F ) ) $=
      ( vx con0 wcel com co wceq wa coa wf c0 cfsupp wbr simpr eleq2d simpl cfv
      ccnf cdm cof eqid omelon a1i cantnfs bitrd biimtrdi impel ffnd inidm offn
      simpll cv ffvelcdmda nnacom syl2anc adantr simplll fnfvof 3eqtr4d eqfnfvd
      wfn syl22anc ) DFGZAHDUAIUBZJZKZBAGZCAGZKZKZEDBCLUCZIZCBVNIZVMDDLDBCFFVMD
      HBVIVJDHBMZVLVIVJVQBNOPZKZVQVIVJBVGGVSVIAVGBVFVHQZRVIHDVGBVGUDZHFGVIUEUFZ
      VFVHSZUGUHVQVRSUIVJVKSUJZUKZVMDHCVIVKDHCMZVLVIVKWFCNOPZKZWFVIVKCVGGWHVIAV
      GCVTRVIHDVGCWAWBWCUGUHWFWGSUIVJVKQUJZUKZVFVHVLUNZWKDULZUMVMDDLDCBFFWJWEWK
      WKWLUMVMEUOZDGZKZWMBTZWMCTZLIZWQWPLIZWMVOTZWMVPTZWOWPHGWQHGWRWSJVMDHWMBWD
      UPVMDHWMCWIUPWPWQUQURWOBDVDZCDVDZVFWNWTWRJVMXBWNWEUSZVMXCWNWJUSZVFVHVLWNU
      TZVMWNQZDLBCFWMVAVEWOXCXBVFWNXAWSJXEXDXFXGDLCBFWMVAVEVBVC $.
  $}

  ${
    $d F x $.  $d S x $.  $d X x $.
    $( Identity law for component-wise ordinal addition of Cantor normal forms.
       (Contributed by RP, 3-Jan-2025.) $)
    naddcnfid1 $p |- ( ( ( X e. On /\ S = dom ( _om CNF X ) ) /\ F e. S ) ->
                       ( F oF +o ( X X. { (/) } ) ) = F ) $=
      ( vx con0 wcel com co wceq wa c0 coa wf cfsupp wbr peano1 mp1i a1i adantr
      cfv ccnf cdm csn cxp fconst6g simpl fczfsuppd simpr eleq2d omelon cantnfs
      cof eqid bitrd mpbir2and wfn simprbda ffnd simplll offn cv simp-4l fnfvof
      inidm syl22anc fvconst2g sylancr oveq2d ffvelcdmda nna0 syl 3eqtrd mpidan
      eqfnfvd ) CEFZAGCUAHUBZIZJZBAFZCKUCUDZAFZBVTLULHZBIVRWACGVTMZVTKNOZKGFZWC
      VRPCKGUEZQVRCEGKVOVQUFZWEVRPRUGVRWAVTVPFWCWDJVRAVPVTVOVQUHZUIVRGCVPVTVPUM
      ZGEFVRUJRZWGUKUNUOVRVSJZWAJZDCWBBWLCCLCBVTEEWKBCUPZWAWKCGBVRVSCGBMZBKNOZV
      RVSBVPFWNWOJVRAVPBWHUIVRGCVPBWIWJWGUKUNUQZURSZWEVTCUPZWLPWECGVTWFURZQVOVQ
      VSWAUSZWTCVDUTWQWLDVAZCFZJZXAWBTZXABTZXAVTTZLHZXEKLHZXEXCWMWRVOXBXDXGIWLW
      MXBWQSWEWRXCPWSQVOVQVSWAXBVBWLXBUHZCLBVTEXAVCVEXCXFKXELXCWEXBXFKIPXICKXAG
      VFVGVHXCXEGFXHXEIWLCGXABWKWNWAWPSVIXEVJVKVLVNVM $.
  $}

  $( Identity law for component-wise ordinal addition of Cantor normal forms.
     (Contributed by RP, 3-Jan-2025.) $)
  naddcnfid2 $p |- ( ( ( X e. On /\ S = dom ( _om CNF X ) ) /\ F e. S ) ->
                     ( ( X X. { (/) } ) oF +o F ) = F ) $=
    ( con0 wcel com ccnf co cdm wceq wa c0 csn cxp coa cof wf cfsupp peano1 a1i
    wbr fconst6g mp1i simpl fczfsuppd simpr eleq2d eqid cantnfs bitrd mpbir2and
    omelon naddcnfcom ex mpand imp naddcnfid1 eqtrd ) CDEZAFCGHIZJZKZBAEZKCLMNZ
    BOPZHZBVDVEHZBVBVCVFVGJZVBVDAEZVCVHVBVICFVDQZVDLRUAZLFEZVJVBSCLFUBUCVBCDFLU
    SVAUDZVLVBSTUEVBVIVDUTEVJVKKVBAUTVDUSVAUFUGVBFCUTVDUTUHFDEVBULTVMUIUJUKVBVI
    VCKVHAVDBCUMUNUOUPABCUQUR $.

  ${
    $d F x $.  $d G x $.  $d H x $.  $d S x $.  $d X x $.
    $( Component-wise addition of Cantor normal forms is associative.
       (Contributed by RP, 3-Jan-2025.) $)
    naddcnfass $p |- ( ( ( X e. On /\ S = dom ( _om CNF X ) ) /\
                  ( F e. S /\ G e. S /\ H e. S ) ) ->
                  ( ( F oF +o G ) oF +o H ) = ( F oF +o ( G oF +o H ) ) ) $=
      ( con0 wcel com co wceq wa coa wfn simpl biimtrdi impel adantr cfv fnfvof
      offn vx ccnf cdm w3a cof wf c0 cfsupp wbr simpr eleq2d omelon a1i cantnfs
      eqid bitrd ffnd simp1 simp2 inidm simp3 ffvelcdmda nnaass anim1i syl21anc
      cv syl3anc oveq1d oveq2d 3eqtr4d eqfnfvd ) EFGZAHEUBIUCZJZKZBAGZCAGZDAGZU
      DZKZUAEBCLUEZIZDWAIZBCDWAIZWAIZVTEELEWBDFFVTEELEBCFFVOVPBEMZVSVOVPEHBUFZB
      UGUHUIZKZWFVOVPBVMGWIVOAVMBVLVNUJZUKVOHEVMBVMUOZHFGVOULUMZVLVNNZUNUPZWIEH
      BWGWHNZUQOVPVQVRURZPZVOVQCEMZVSVOVQEHCUFZCUGUHUIZKZWRVOVQCVMGXAVOAVMCWJUK
      VOHEVMCWKWLWMUNUPZXAEHCWSWTNZUQOVPVQVRUSZPZVOVLVSWMQZXFEUTZTZVOVRDEMZVSVO
      VREHDUFZDUGUHUIZKZXIVOVRDVMGXLVOAVMDWJUKVOHEVMDWKWLWMUNUPZXLEHDXJXKNZUQOV
      PVQVRVAZPZXFXFXGTVTEELEBWDFFWQVTEELECDFFXEXPXFXFXGTZXFXFXGTVTUAVFZEGZKZXR
      WBRZXRDRZLIZXRBRZXRWDRZLIZXRWCRZXRWERZXTYDXRCRZLIZYBLIZYDYIYBLIZLIZYCYFXT
      YDHGYIHGYBHGYKYMJVTEHXRBVOVPWGVSVOVPWIWGWNWOOWPPVBVTEHXRCVOVQWSVSVOVQXAWS
      XBXCOXDPVBVTEHXRDVOVRXJVSVOVRXLXJXMXNOXOPVBYDYIYBVCVGXTYAYJYBLXTWFWRVLXSK
      ZYAYJJVTWFXSWQQZVTWRXSXEQZVTVLXSXFVDZELBCFXRSVEVHXTYEYLYDLXTWRXIYNYEYLJYP
      VTXIXSXPQZYQELCDFXRSVEVIVJXTWBEMZXIYNYGYCJVTYSXSXHQYRYQELWBDFXRSVEXTWFWDE
      MZYNYHYFJYOVTYTXSXQQYQELBWDFXRSVEVJVK $.
  $}

  ${
    $d A x $.
    $( The successor to the union of any non-empty, finite subset of ordinals
       is the union of the successors of the elements.  (Contributed by RP,
       12-Feb-2025.) $)
    onsucunifi $p |- ( ( A C_ On /\ A e. Fin /\ A =/= (/) ) ->
                     suc U. A = U_ x e. A suc x ) $=
      ( con0 wss cfn wcel c0 wne w3a cuni csuc ciun ordunifi suceq ssiun2s word
      cv syl ssorduni ordsuci onsucuni sselda ordsucss syl2an2r iunssd 3ad2ant1
      imp eqssd ) BCDZBEFZBGHZIZBJZKZABAQZKZLZULUMBFUNUQDBMABUPUMUNUOUMNORUIUJU
      QUNDUKUIABUPUNUIUNPZUOBFUOUNFZUPUNDZUIUMPURBSUMTRUIBUNUOBUAUBURUSUTUOUNUC
      UGUDUEUFUH $.
  $}

  $( The successor to the union of any singleton of a set is the successor of
     the set.  (Contributed by RP, 11-Feb-2025.) $)
  sucunisn $p |- ( A e. V ->
                  suc U. { A } = suc A ) $=
    ( wcel csn cuni wceq csuc unisng suceq syl ) ABCADEZAFKGAGFABHKAIJ $.

  $( The successor to the union of any pair of ordinals is the union of the
     successors of the elements.  (Contributed by RP, 12-Feb-2025.) $)
  onsucunipr $p |- ( ( A e. On /\ B e. On ) ->
                  suc U. { A , B } = U. { suc A , suc B } ) $=
    ( con0 wcel wa cun csuc cpr cuni wceq ssequn1 suceq sylbi adantl onsucwordi
    wss imp sylib eqtr4d ssequn2 wi ancoms word wo eloni syl2an mpjaodan uniprg
    ordtri2or2 syl onsuc 3eqtr4d ) ACDZBCDZEZABFZGZAGZBGZFZABHIZGZURUSHIZUOABPZ
    UQUTJBAPZUOVDEZUQUSUTVDUQUSJZUOVDUPBJVGABKUPBLMNVFURUSPZUTUSJUOVDVHABOQURUS
    KRSUOVEEZUQURUTVEUQURJZUOVEUPAJVJBATUPALMNVIUSURPZUTURJUOVEVKUNUMVEVKUABAOU
    BQUSURTRSUMAUCBUCVDVEUDUNAUEBUEABUIUFUGUOVAUPJVBUQJABCCUHVAUPLUJUMURCDUSCDV
    CUTJUNAUKBUKURUSCCUHUFUL $.

  $( The successor to the union of any triple of ordinals is the union of the
     successors of the elements.  (Contributed by RP, 12-Feb-2025.) $)
  onsucunitp $p |- ( ( A e. On /\ B e. On /\ C e. On ) ->
                  suc U. { A , B , C } = U. { suc A , suc B , suc C } ) $=
    ( con0 wcel ctp cuni csuc wceq wa cun onsucunipr sylan uniprg adantr unisng
    cpr csn adantl syl onun2 uneq12d df-tp unieqi uniun eqtri a1i 3eqtr4d suceq
    onsuc syl2an eqtr3d eqcomd eqtrd eqtr4id 3impa ) ADEZBDEZCDEZABCFZGZHZAHZBH
    ZCHZFZGZIUQURJZUSJZABKZCQGZHZVJHZVEQGZVBVGVHVJDEZUSVLVNIABUAZVJCLMVIVAVKIVB
    VLIVIABQZGZCRZGZKZVJCKZVAVKVIVRVJVTCVHVRVJIZUSABDDNZOUSVTCIVHCDPSUBVAWAIVIV
    AVQVSKZGWAUTWEABCUCUDVQVSUEUFUGVHVOUSVKWBIVPVJCDDNMUHVAVKUITVIVGVCVDQZGZVER
    ZGZKZVNVGWFWHKZGWJVFWKVCVDVEUCUDWFWHUEUFVIVNVMVEKZWJVHVMDEZVEDEZVNWLIUSVHVO
    WMVPVJUJTCUJZVMVEDDNUKVIVMWGVEWIVHVMWGIUSVHVRHZVMWGVHWCWPVMIWDVRVJUITABLULO
    USVEWIIVHUSWIVEUSWNWIVEIWOVEDPTUMSUBUNUOUHUP $.

  ${
    $d A a b w x y z $.  $d B a b w x y z $.

    $( The class of all ordinal sums of elements from two ordinals is ordinal.
       Lemma for ~ oaun3 .  (Contributed by RP, 13-Feb-2025.) $)
    oaun3lem1 $p |- ( ( A e. On /\ B e. On ) ->
                     Ord { x | E. a e. A E. b e. B x = ( a +o b ) } ) $=
      ( vz vy vw con0 wcel wa cv coa co wceq wrex word c0 adantr weq cab wtr wi
      cep wwe wral wal nfv nfcv nfre1 nfralw nfrexw wel simp-4l simplrl anim1ci
      nfsab wss ontr1 sylc wne simpr ne0i adantl on0eln0 syl2an onelon ad2ant2r
      biimpar syl2anc sylan oa0 syl eqcomd oveq2 rspceeqv syl2an2r oveq1 eqeq2d
      oacl rexbidv rspcev jca wpss anim12i oaordi ordelpss biimpd pssssd sselda
      eloni oawordex2 eqcom bitrdi wo ordtri2or mpjaodan vex 2rexbidv cbvrex2vw
      eqeq1 elab ralrimiva raleqtrrdv exp31 expdimp rexlimd alrimiv ralab dftr5
      sylibr ex eqeltrd rexlimdvv abssdv epweon wess mpisyl df-ord sylanbrc ) B
      IJZCIJZKZALZDLZELZMNZOZECPZDBPZAUAZUBZYKUDUEZYKQYCFLZYKJZFGLZUFZGYKUFZYLY
      CYPYGOZECPZDBPZYQUCZGUGYRYCUUBGYCYTYQDBYCDUHYODFYPDYPUIYJDAFYIDBUJUQUKYCY
      EBJZYTYQUCYCUUCKZYSYQECUUDEUHYOEFYPEYPUIYJEAFYIEDBEBUIYHECUJULUQUKYCUUCYF
      CJZYSYQUCYCUUCUUEKZYSYQYCUUFKZYSKYOFYGYPUUGYOFYGUFYSUUGYOFYGUUGYNYGJZKZYN
      HLZYPMNZOZGCPZHBPZYOUUIFDUMZUUNYEYNURZUUIUUOKZYNBJZYNYNYPMNZOZGCPZUUNUUQY
      AUUOUUCKUURYAYBUUFUUHUUOUNUUIUUCUUOYCUUCUUEUUHUOZUPYNYEBUSUTUUIUVAUUOUUGR
      CJZUUHYNYNRMNZOUVAYCYBCRVAZUVCUUFYAYBVBZUUEUVEUUCCYFVCVDYBUVCUVECVEVIVFUU
      IUVDYNUUIYNIJZUVDYNOUUGYGIJZUUHUVGUUGYEIJZYFIJZUVHYAUUCUVIYBUUEBYEVGVHZYC
      YBUUEUVJUUFUVFUUCUUEVBZCYFVGVFYEYFVTVJZYGYNVGVKZYNVLVMVNGRCUUSUVDYNYPRYNM
      VOVPVQSUUMUVAHYNBHFTZUULUUTGCUVOUUKUUSYNUUJYNYPMVRVSWAWBVJUUIUUCUUPYEYPMN
      ZYNOZGCPZUUNUVBUUIUVIYBKZUUPUUPYNYECMNZJZKUVRUUGUVSUUHUUGUVIYBUVKYCYBUUFU
      VFSZWCSUUIUWAUUPUUGYGUVTYNUUGYGUVTUUGYGQZUVTQZKZYGUVTJZYGUVTWDZUUGUVHUVTI
      JZUWEUVMUUGUVIYBUWHUVKUWBYECVTVJUVHUWCUWHUWDYGWKUVTWKWEVJUUGYBUVIKUUEUWFU
      UGYBUVIUWBUVKWCUUFUUEYCUVLVDYFCYEWFUTUWEUWFUWGYGUVTWGWHUTWIWJUPGYECYNWLVQ
      UUMUVRHYEBHDTZUULUVQGCUWIUULYNUVPOUVQUWIUUKUVPYNUUJYEYPMVRVSYNUVPWMWNWAWB
      VQUUIYNQZYEQZUUOUUPWOUUIUVGUWJUVNYNWKVMUUGUWKUUHUUGUVIUWKUVKYEWKVMSYNYEWP
      VJWQYJUUNAYNFWRAFTZYJYNYGOZECPDBPUUNUWLYHUWMDEBCYDYNYGXAWSUWMUULYNUUJYFMN
      ZODEHGBCDHTYGUWNYNYEUUJYFMVRVSEGTUWNUUKYNYFYPUUJMVOVSWTWNXBXKXCSUUGYSVBXD
      XEXFXGXLXGXHYJUUAYQGAAGTYHYSDEBCYDYPYGXAWSXIXKGFYKXJXKYCYKIURIUDUEYMYCYJA
      IYCYHYDIJZDEBCYCUUFYHUWOUUGYHKYDYGIUUGYHVBUUGUVHYHUVMSXMXEXNXOXPYKIUDXQXR
      YKXSXT $.
  $}

  ${
    $d A a b x $.  $d B a b x $.
    $( The class of all ordinal sums of elements from two ordinals is bounded
       by the sum.  Lemma for ~ oaun3 .  (Contributed by RP, 13-Feb-2025.) $)
    oaun3lem2 $p |- ( ( A e. On /\ B e. On ) ->
                     { x | E. a e. A E. b e. B x = ( a +o b ) }
                     C_ ( A +o B ) ) $=
      ( con0 wcel wa cv coa wrex simpr wss onelon oacl syl2anc adantr jca sylc
      co wceq ad2ant2r ad2ant2l simpl 3jca wpss adantl word wb anim12i ordelpss
      w3a eloni syl mpbid pssssd oawordri pm3.22 oaordi ontr2 eqeltrd rexlimdvv
      exp31 abssdv ) BFGZCFGZHZAIZDIZEIZJTZUAZECKDBKABCJTZVGVLVHVMGZDEBCVGVIBGZ
      VJCGZHZVLVNVGVQHZVLHVHVKVMVRVLLVRVKVMGZVLVRVKFGZVMFGZHVKBVJJTZMZWBVMGZHVS
      VRVTWAVRVIFGZVJFGZVTVEVOWEVFVPBVINUBZVFVPWFVEVOCVJNUCZVIVJOPVGWAVQBCOQRVR
      WCWDVRWEVEWFULVIBMWCVRWEVEWFWGVGVEVQVEVFUDQZWHUEVRVIBVRVOVIBUFZVQVOVGVOVP
      UDUGVRVIUHZBUHZHZVOWJUIVRWEVEWMWGWIWEWKVEWLVIUMBUMUJPVIBUKUNUOUPVIBVJUQSV
      RVFVEHZVPWDVGWNVQVEVFURQVQVPVGVOVPLUGVJCBUSSRVKWBVMUTSQVAVCVBVD $.

    $( The class of all ordinal sums of elements from two ordinals is an
       ordinal.  Lemma for ~ oaun3 .  (Contributed by RP, 13-Feb-2025.) $)
    oaun3lem3 $p |- ( ( A e. On /\ B e. On ) ->
                     { x | E. a e. A E. b e. B x = ( a +o b ) } e. On ) $=
      ( con0 wcel wa cv coa co wceq wrex cab word cvv oaun3lem1 oaun3lem2 ssexd
      oacl elon2 sylanbrc ) BFGCFGHZAIDIEIJKLECMDBMANZOUDPGUDFGABCDEQUCUDBCJKFB
      CTABCDERSUDUAUB $.

    $( The class of all ordinal sums of elements from two ordinals is less than
       the successor to the sum.  Lemma for ~ oaun3 .  (Contributed by RP,
       12-Feb-2025.) $)
    oaun3lem4 $p |- ( ( A e. On /\ B e. On ) ->
                     { x | E. a e. A E. b e. B x = ( a +o b ) } e.
                     suc ( A +o B ) ) $=
      ( con0 wcel wa cv coa co wceq wrex cab wss csuc oaun3lem2 oaun3lem3 oacl
      wb onsssuc syl2anc mpbid ) BFGCFGHZAIDIEIJKLECMDBMANZBCJKZOZUEUFPGZABCDEQ
      UDUEFGUFFGUGUHTABCDERBCSUEUFUAUBUC $.
  $}

  ${
    $d A a x $.
    $( Two ways to express a class.  (Contributed by RP, 13-Feb-2025.) $)
    rp-abid $p |- A = { x | E. a e. A x = a } $=
      ( weq wrex cv clel5 eqabi ) ACDCBEABCBAFGH $.
  $}

  ${
    $d A b x y $.  $d B b x y $.  $d .(+) b x y $.
    oadif1lem.cl1 $e |- ( ( A e. On /\ B e. On ) -> ( A .(+) B ) e. On ) $.
    oadif1lem.cl2 $e |- ( ( A e. On /\ b e. On ) -> ( A .(+) b ) e. On ) $.
    oadif1lem.sub $e |- ( ( ( A e. On /\ B e. On ) /\
                          ( A C_ y /\ y e. ( A .(+) B ) ) ) ->
                          E. b e. B ( A .(+) b ) = y ) $.
    oadif1lem.ord $e |- ( ( A e. On /\ B e. On ) -> ( b e. B ->
                          ( A .(+) b ) e. ( A .(+) B ) ) ) $.
    oadif1lem.word $e |- ( ( A e. On /\ b e. On ) -> A C_ ( A .(+) b ) ) $.
    $( Express the set difference of a continuous sum and its left addend as a
       class of sums.  (Contributed by RP, 13-Feb-2025.) $)
    oadif1lem $p |- ( ( A e. On /\ B e. On ) -> ( ( A .(+) B ) \ A ) =
                      { x | E. b e. B x = ( A .(+) b ) } ) $=
      ( con0 wcel wa co cv wceq wrex wn syl2an2r cdif cab wb simpl onelon sylan
      wss ontri1 pm5.32da ancom bitr3di sylbida eqcom rexbii sylib ex simpr imp
      adantr eqeltrd mpbid eqneltrd jca rexlimdva2 impbid eldif vex weq rexbidv
      eqeq1 elab 3bitr4g eqrdv ) CLMZDLMZNZBCDEOZCUAZAPZCFPZEOZQZFDRZAUBZVPBPZV
      QMZWECMSZNZWEWAQZFDRZWEVRMWEWDMVPWHWJVPWHWJVPWHNWAWEQZFDRZWJVPWHCWEUGZWFN
      ZWLVPWFWMNWHWNVPWFWMWGVPVNWFWELMZWMWGUCVNVOUDZVPVQLMWFWOGVQWEUEUFCWEUHTUI
      WFWMUJUKIULWKWIFDWAWEUMUNUOUPVPWIWHFDVPVTDMZNZWINZWFWGWSWEWAVQWRWIUQZWRWA
      VQMZWIVPWQXAJURUSUTWSWEWACWTWRWACMSZWIWRCWAUGZXBVPVNWQVTLMZXCWPVPVOWQXDVN
      VOUQDVTUEUFZKTVPVNWQWALMZXCXBUCWPVPVNWQXDXFWPXEHTCWAUHTVAUSVBVCVDVEWEVQCV
      FWCWJAWEBVGABVHWBWIFDVSWEWAVJVIVKVLVM $.
  $}

  ${
    $d A b x y $.  $d B b x y $.
    $( Express the set difference of an ordinal sum and its left addend as a
       class of sums.  (Contributed by RP, 13-Feb-2025.) $)
    oadif1 $p |- ( ( A e. On /\ B e. On ) ->
                   ( ( A +o B ) \ A ) = { x | E. b e. B x = ( A +o b ) } ) $=
      ( vy con0 wcel wa coa co cv wceq wrex wn wss oacl onelon sylan syl2an2r
      wb cab simpl ontri1 pm5.32da ancom bitr3di oawordex2 sylbida eqcom rexbii
      sylib ex simpr wi oaordi ancoms imp adantr eqeltrd oaword1 mpbid eqneltrd
      cdif jca rexlimdva2 impbid eldif vex weq eqeq1 rexbidv elab 3bitr4g eqrdv
      ) BFGZCFGZHZEBCIJZBVCZAKZBDKZIJZLZDCMZAUAZVQEKZVRGZWFBGNZHZWFWBLZDCMZWFVS
      GWFWEGVQWIWKVQWIWKVQWIHWBWFLZDCMZWKVQWIBWFOZWGHZWMVQWGWNHWIWOVQWGWNWHVQVO
      WGWFFGZWNWHTVOVPUBZVQVRFGWGWPBCPVRWFQRBWFUCSUDWGWNUEUFDBCWFUGUHWLWJDCWBWF
      UIUJUKULVQWJWIDCVQWACGZHZWJHZWGWHWTWFWBVRWSWJUMZWSWBVRGZWJVQWRXBVPVOWRXBU
      NWACBUOUPUQURUSWTWFWBBXAWSWBBGNZWJWSBWBOZXCVQVOWRWAFGZXDWQVQVPWRXEVOVPUMC
      WAQRZBWAUTSVQVOWRWBFGZXDXCTWQVQVOWRXEXGWQXFBWAPSBWBUCSVAURVBVDVEVFWFVRBVG
      WDWKAWFEVHAEVIWCWJDCVTWFWBVJVKVLVMVN $.
  $}

  $( Corrected version of Theorems 3.5 and 3.11 of
     https://arxiv.org/abs/2501.04412v1 $)

  ${
    $d A a b x y $.  $d B a b x y $.
    $( Ordinal addition as a union of classes.  (Contributed by RP,
       13-Feb-2025.) $)
    oaun2 $p |- ( ( A e. On /\ B e. On ) -> ( A +o B ) = U. {
              { x | E. a e. A x = a } ,
              { y | E. b e. B y = ( A +o b ) }
              } ) $=
      ( con0 wcel wa coa co cdif cpr cuni cun wrex cab cv wceq cvv oacl rp-abid
      weq difexd uniprg syldan a1i oadif1 preq12d unieqd undif2 oaword1 ssequn1
      wss sylib eqtrid 3eqtr3rd ) CGHZDGHZIZCCDJKZCLZMZNZCVBOZAEUCECPAQZBRCFRJK
      SFDPBQZMZNVAURUSVBTHVDVESUTVACGCDUAUDCVBGTUEUFUTVCVHUTCVFVBVGCVFSUTACEUBU
      GBCDFUHUIUJUTVECVAOZVACVAUKUTCVAUNVIVASCDULCVAUMUOUPUQ $.
  $}

  ${
    $d A a b x y z $.  $d B a b x y z $.
    $( Ordinal addition as a union of classes.  (Contributed by RP,
       13-Feb-2025.) $)
    oaun3 $p |- ( ( A e. On /\ B e. On ) -> ( A +o B ) = U. {
              { x | E. a e. A x = a } ,
              { y | E. b e. B y = ( A +o b ) } ,
              { z | E. a e. A E. b e. B z = ( a +o b ) } } ) $=
      ( con0 wcel coa co cuni cv wceq wrex cab cun ctp cvv wss cdif cpr csn weq
      wa oacl difexd uniprg syldan undif2 oaword1 ssequn1 sylib eqtrd oaun3lem4
      eqtrid unisng syl uneq12d uniun df-tp rp-abid a1i oadif1 tpeq123d eqtr3id
      csuc eqidd unieqd oaun3lem2 ssequn2 3eqtr3rd ) DHIZEHIZUEZDDEJKZDUAZUBZLZ
      CMFMGMZJKNGEOFDOCPZUCZLZQZVPWAQZAFUDFDOAPZBMDVTJKNGEOBPZWARZLZVPVOVSVPWCW
      AVOVSDVQQZVPVMVNVQSIVSWJNVOVPDHDEUFUGDVQHSUHUIVOWJDVPQZVPDVPUJVODVPTWKVPN
      DEUKDVPULUMUPUNVOWAVPVGZIWCWANCDEFGUOWAWLUQURUSVOWDVRWBQZLWIVRWBUTVOWMWHV
      OWMDVQWARWHDVQWAVAVODWFVQWGWAWADWFNVOADFVBVCBDEGVDVOWAVHVEVFVIVFVOWAVPTWE
      VPNCDEFGVJWAVPVKUMVL $.
  $}

  ${
    $d A a x $.  $d A b x $.  $d B a x $.  $d B b x $.
    $( Alternate expression for natural addition.  (Contributed by RP,
       19-Dec-2024.) $)
    naddov4 $p |- ( ( A e. On /\ B e. On ) -> ( A +no B ) =
     |^| ( { x e. On | A. a e. A ( a +no B ) e. x }
           i^i { x e. On | A. b e. B ( A +no b ) e. x } ) ) $=
      ( con0 wcel wa cnadd co cv wral crab cint cin naddov2 inrab eqtr3i inteqi
      incom eqtrdi ) BFGCFGHBCIJBEKIJAKZGECLZDKCIJUBGDBLZHAFMZNUDAFMZUCAFMZOZNA
      EDBCPUEUHUGUFOUEUHUCUDAFQUGUFTRSUA $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d C x y $.
    $( The set of ordinals which have a natural sum less than some ordinal is
       transitive.  (Contributed by RP, 20-Dec-2024.) $)
    nadd2rabtr $p |- ( ( Ord A /\ B e. On /\ C e. On ) ->
                       Tr { x e. A | ( B +no x ) e. C } ) $=
      ( vy word con0 wcel w3a cv cnadd co crab wss wral wa simplr adantr sylibr
      syl2anc wtr wi simpll1 ordelss wel simpll3 simpllr ordelon onelon simpll2
      simpr wb naddel2 syl3anc mpbid jca ontr1 sylc ssrabdv ralrimiva weq oveq2
      ex eleq1d ralrab dftr3 ) BFZCGHZDGHZIZEJZCAJZKLZDHZABMZNZEVOOZVOUAVJCVKKL
      ZDHZVPUBZEBOVQVJVTEBVJVKBHZPZVSVPWBVSPZVNABVKWCVGWAVKBNVGVHVIWAVSUCZVJWAV
      SQBVKUDTWCAEUEZPZVIVMVRHZVSPVNWCVIWEVGVHVIWAVSUFRWFWGVSWFWEWGWCWEUKZWFVLG
      HZVKGHZVHWEWGULWFWJWEWIWFVGWAWJWCVGWEWDRVJWAVSWEUGBVKUHTZWHVKVLUITWKWCVHW
      EVGVHVIWAVSUJRVLVKCUMUNUOWBVSWEQUPVMVRDUQURUSVCUTVNVSVPEABAEVAVMVRDVLVKCK
      VBVDVESEVOVFS $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( The set of ordinals which have a natural sum less than some ordinal is
       an ordinal.  (Contributed by RP, 20-Dec-2024.) $)
    nadd2rabord $p |- ( ( Ord A /\ B e. On /\ C e. On ) ->
                       Ord { x e. A | ( B +no x ) e. C } ) $=
      ( word con0 wcel w3a cv cnadd crab wss wtr ssrab2 ordsson 3ad2ant1 sstrid
      co nadd2rabtr dford5 sylanbrc ) BEZCFGZDFGZHZCAIJRDGZABKZFLUGMUGEUEUGBFUF
      ABNUBUCBFLUDBOPQABCDSUGTUA $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( The class of ordinals which have a natural sum less than some ordinal is
       a set.  (Contributed by RP, 20-Dec-2024.) $)
    nadd2rabex $p |- ( ( Ord A /\ B e. On /\ C e. On ) ->
                       { x e. A | ( B +no x ) e. C } e. _V ) $=
      ( word con0 wcel w3a cv cnadd co crab simp3 wa wss c0 wceq 0elon ordelon
      wi 3ad2antl1 naddcom sylancr naddrid syl simpl2 naddssim mp3an2i eqsstrrd
      eqtrd 0ss mpi simpl3 ontr2 syl2anc mpand 3impia rabssdv ssexd ) BEZCFGZDF
      GZHZCAIZJKZDGZABLDFUTVAVBMVCVFABDVCVDBGZVFVDDGZVCVGNZVDVEOZVFVHVIVDPVDJKZ
      VEVIVKVDPJKZVDVIPFGZVDFGZVKVLQRUTVAVGVNVBBVDSUAZPVDUBUCVIVNVLVDQVOVDUDUEU
      JVIPCOZVKVEOZCUKVMVIVAVNVPVQTRUTVAVBVGUFVOPCVDUGUHULUIVIVNVBVJVFNVHTVOUTV
      AVBVGUMVDVEDUNUOUPUQURUS $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( The set of ordinals which have a natural sum less than some ordinal is
       an ordinal number.  (Contributed by RP, 20-Dec-2024.) $)
    nadd2rabon $p |- ( ( Ord A /\ B e. On /\ C e. On ) ->
                       { x e. A | ( B +no x ) e. C } e. On ) $=
      ( word con0 wcel w3a cv cnadd co crab cvv nadd2rabord nadd2rabex sylanbrc
      elon2 ) BECFGDFGHCAIJKDGABLZERMGRFGABCDNABCDORQP $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( The set of ordinals which have a natural sum less than some ordinal is
       transitive.  (Contributed by RP, 20-Dec-2024.) $)
    nadd1rabtr $p |- ( ( Ord A /\ B e. On /\ C e. On )
                       -> Tr { x e. A | ( x +no B ) e. C } ) $=
      ( word con0 wcel w3a cv cnadd co crab wtr nadd2rabtr wb wa simpl2 ordelon
      wceq 3ad2antl1 naddcom syl2anc eleq1d rabbidva treq syl mpbid ) BEZCFGZDF
      GZHZCAIZJKZDGZABLZMZULCJKZDGZABLZMZABCDNUKUOUSSUPUTOUKUNURABUKULBGZPZUMUQ
      DVBUIULFGZUMUQSUHUIUJVAQUHUIVAVCUJBULRTCULUAUBUCUDUOUSUEUFUG $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( The set of ordinals which have a natural sum less than some ordinal is
       an ordinal.  (Contributed by RP, 20-Dec-2024.) $)
    nadd1rabord $p |- ( ( Ord A /\ B e. On /\ C e. On ) ->
                       Ord { x e. A | ( x +no B ) e. C } ) $=
      ( word con0 wcel w3a cv cnadd crab wss wtr ssrab2 ordsson 3ad2ant1 sstrid
      co nadd1rabtr dford5 sylanbrc ) BEZCFGZDFGZHZAICJRDGZABKZFLUGMUGEUEUGBFUF
      ABNUBUCBFLUDBOPQABCDSUGTUA $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( The class of ordinals which have a natural sum less than some ordinal is
       a set.  (Contributed by RP, 20-Dec-2024.) $)
    nadd1rabex $p |- ( ( Ord A /\ B e. On /\ C e. On ) ->
                       { x e. A | ( x +no B ) e. C } e. _V ) $=
      ( word con0 wcel w3a cv cnadd co crab wa simpl2 ordelon 3ad2antl1 naddcom
      cvv wceq syl2anc eleq1d rabbidva nadd2rabex eqeltrrd ) BEZCFGZDFGZHZCAIZJ
      KZDGZABLUICJKZDGZABLRUHUKUMABUHUIBGZMZUJULDUOUFUIFGZUJULSUEUFUGUNNUEUFUNU
      PUGBUIOPCUIQTUAUBABCDUCUD $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( The set of ordinals which have a natural sum less than some ordinal is
       an ordinal number.  (Contributed by RP, 20-Dec-2024.) $)
    nadd1rabon $p |- ( ( Ord A /\ B e. On /\ C e. On ) ->
                       { x e. A | ( x +no B ) e. C } e. On ) $=
      ( word con0 wcel w3a cv cnadd co crab cvv nadd1rabord nadd1rabex sylanbrc
      elon2 ) BECFGDFGHAICJKDGABLZERMGRFGABCDNABCDORQP $.
  $}

  ${
    $d A a $.  $d a b x y $.
    $( Natural addition with 1 is same as successor.  (Contributed by RP,
       31-Dec-2024.) $)
    nadd1suc $p |- ( A e. On -> ( A +no 1o ) = suc A ) $=
      ( va vb vy vx cv c1o cnadd co csuc wceq oveq1 con0 wcel wral wa c0 eleq1d
      wb adantr weq suceq eqeq12d crab wel naddrid anbi1d ad2antrr df1o2 raleqi
      cint csn 0ex oveq2 ralsn bitri a1i cbvralvw nfv nfra1 nfan simpr r19.21bi
      ralbida bitrid anbi12d wss onelon ad4ant13 syl simpllr jca word ad3antrrr
      onsuc eloni simplr ordsucss sylc ontr2 ralrimdva pm4.71d adantlr rabbidva
      ex 3bitr4d inteqd 1on naddov2 mpan2 onsucmin 3eqtr4d tfis3 ) BFZGHIZWNJZK
      ZCFZGHIZWRJZKZAGHIZAJZKBCABCUAWOWSWPWTWNWRGHLWNWRUBUCWNAKWOXBWPXCWNAGHLWN
      AUBUCWNMNZXACWNOZWQXDXEPZWNDFZHIZEFZNZDGOZXGGHIZXINZDWNOZPZEMUDZUKZBEUEZE
      MUDZUKZWOWPXFXPXSXFXOXREMXFXIMNZPWNQHIZXINZWTXINZCWNOZPZXRYEPZXOXRXDYFYGS
      XEYAXDYCXRYEXDYBWNXIWNUFRUGUHXFXOYFSYAXFXKYCXNYEXKYCSXFXKXJDQULZOYCXJDGYH
      UIUJXJYCDQUMXGQKXHYBXIXGQWNHUNRUOUPUQXNWSXINZCWNOXFYEXMYIDCWNDCUAXLWSXIXG
      WRGHLRURXFYIYDCWNXDXECXDCUSXACWNUTVAXFCBUEZPWSWTXIXFXACWNXDXEVBVCRVDVEVFT
      XDYAXRYGSXEXDYAPZXRYEYKXRYDCWNYKYJPZXRYDYLXRPZWTMNZYAPWTWNVGZXRPYDYMYNYAY
      MWRMNZYNXDYJYPYAXRWNWRVHVIWRVOVJXDYAYJXRVKVLYMYOXRYMWNVMZYJYOXDYQYAYJXRWN
      VPVNYKYJXRVQWRWNVRVSYLXRVBVLWTWNXIVTVSWEWAWBWCWFWDWGXDWOXQKZXEXDGMNYRWHED
      DWNGWIWJTXDWPXTKXEEWNWKTWLWEWM $.
  $}

  $( Natural addition of ordinal numbers is associative when the third element
     is 1.  (Contributed by RP, 1-Jan-2025.) $)
  naddass1 $p |- ( ( A e. On /\ B e. On ) -> ( ( A +no B ) +no 1o ) =
                   ( A +no ( B +no 1o ) ) ) $=
    ( con0 wcel wa csuc cnadd co c1o naddsuc2 nadd1suc adantl oveq2d naddcl syl
    wceq 3eqtr4rd ) ACDZBCDZEZABFZGHABGHZFZABIGHZGHUBIGHZABJTUDUAAGSUDUAPRBKLMT
    UBCDUEUCPABNUBKOQ $.

  ${
    $d A a b $.  $d B b $.  $d a b c d $.
    $( Natural addition results in a value greater than or equal than that of
       ordinal addition.  (Contributed by RP, 1-Jan-2025.) $)
    naddgeoa $p |- ( ( A e. On /\ B e. On ) -> ( A +o B ) C_ ( A +no B ) ) $=
      ( vb vc vd cv coa co cnadd wss oveq1 sseq12d wceq con0 wcel wa wral simpr
      syl c0 va weq oveq2 wlim w3a wi ciun simplll simpllr simplr oalim syl2anc
      jca simpl simp3 wel onelss imp onelon simpll naddss2 syl3anc mpbid adantr
      wb sstrd ralimdva iunss sylibr syl2an eqsstrd exp31 csuc wrex word dflim3
      ex wn notbii iman bitr4i eloni pm5.5 3syl bitrid ssidd oveq2d oa0 naddrid
      wo eqtrd 3sstr4d a1d vex sucid eleqtrrid a1i reximdv2 r19.29r simprr oacl
      naddcl ordsucsssuc oasuc ad4ant23 naddsuc2 rexlimdva2 syl5 expd syl7 syld
      simprl jaod sylbid pm2.61d on2ind ) UAFZCFZGHZXQXRIHZJZDFZXRGHZYBXRIHZJZY
      BEFZGHZYBYFIHZJZXQYFGHZXQYFIHZJZAXRGHZAXRIHZJABGHZABIHZJABUACDEUADUBZXSYC
      XTYDXQYBXRGKXQYBXRIKLCEUBYCYGYDYHXRYFYBGUCXRYFYBIUCLYQYJYGYKYHXQYBYFGKXQY
      BYFIKLXQAMXSYMXTYNXQAXRGKXQAXRIKLXRBMYMYOYNYPXRBAGUCXRBAIUCLXQNOZXRNOZPZX
      RUDZYIEXRQDXQQZYEDXQQZYLEXRQZUEZYAUFZYTUUAUUEYAYTUUAPZUUEPZXSEXRYJUGZXTUU
      HYRYSUUAPXSUUIMYRYSUUAUUEUHUUHYSUUAYRYSUUAUUEUIYTUUAUUEUJUMEXQXRNUKULUUGY
      TUUDUUIXTJZUUEYTUUAUNUUBUUCUUDUOZYTUUDPYJXTJZEXRQZUUJYTUUDUUMYTYLUULEXRYT
      ECUPZPZYLUULUUOYLPYJYKXTUUOYLRUUOYKXTJZYLUUOYFXRJZUUPYTUUNUUQYTYSUUNUUQUF
      YRYSRZXRYFUQSURUUOYFNOZYSYRUUQUUPVEUUOYSUUNUUSYRYSUUNUJZYTUUNRXRYFUSZULZU
      UTYRYSUUNUTZYFXRXQVAVBVCVDVFVQVGUREXRYJXTVHVIVJVKVLYTUUAVRZXRTMZXRYFVMZMZ
      ENVNZWJZUUFUVDXRVOZUVIUFZYTUVIUVDUVJUVIVRPZVRUVKUUAUVLEXRVPVSUVJUVIVTWAYT
      YSUVJUVKUVIVEUURXRWBUVJUVIWCWDWEYTUVEUUFUVHYTUVEUUFYTUVEPZYAUUEUVMXQXQXSX
      TUVMXQWFUVMXSXQTGHZXQUVMXRTXQGYTUVERZWGUVMYRUVNXQMYRYSUVEUTZXQWHSWKUVMXTX
      QTIHZXQUVMXRTXQIUVOWGUVMYRUVQXQMUVPXQWISWKWLWMVQYTUVHUVGEXRVNZUUFYTUVGUVG
      ENXRUUSUVGPZUUNUVGPUFYTUVSUUNUVGUVSYFUVFXRYFEWNWOUUSUVGRZWPUVTUMWQWRUUEUU
      DYTUVRYAUUKYTUVRUUDYAUVRUUDPUVGYLPZEXRVNYTYAUVGYLEXRWSYTUWAYAEXRUUOUWAPZY
      JVMZYKVMZXSXTUWBYLUWCUWDJZUUOUVGYLWTUUOYLUWEVEZUWAUUOYRUUSPZYJVOZYKVOZPUW
      FUUOYRUUSUVCUVBUMZUWGUWHUWIUWGYJNOUWHXQYFXAYJWBSUWGYKNOUWIXQYFXBYKWBSUMYJ
      YKXCWDVDVCUWBXSXQUVFGHZUWCUWBXRUVFXQGUUOUVGYLXLZWGUWBUWGUWKUWCMUUOUWGUWAU
      WJVDXQYFXDSWKUWBXTXQUVFIHZUWDUWBXRUVFXQIUWLWGUWBYRUUSUWMUWDMYRYSUUNUWAUHY
      SUUNUUSYRUWAUVAXEXQYFXFULWKWLXGXHXIXJXKXMXNXOXP $.
  $}

  ${
    $d A x y $.  $d B x $.
    $( Natural addition with a natural number on the right results in a value
       equal to that of ordinal addition.  (Contributed by RP, 1-Jan-2025.) $)
    naddonnn $p |- ( ( A e. On /\ B e. _om ) -> ( A +o B ) = ( A +no B ) ) $=
      ( vx vy com wcel con0 co cnadd wceq cv wi c0 csuc oveq2 eqeq12d imbi2d wa
      coa adantr weq naddrid eqtr4d nnon suceq adantl oasuc naddsuc2 3eqtr4d ex
      oa0 expcom syl a2d finds impcom ) BEFAGFZABSHZABIHZJZUQACKZSHZAVAIHZJZLUQ
      AMSHZAMIHZJZLUQADKZSHZAVHIHZJZLUQAVHNZSHZAVLIHZJZLUQUTLCDBVAMJZVDVGUQVPVB
      VEVCVFVAMASOVAMAIOPQCDUAZVDVKUQVQVBVIVCVJVAVHASOVAVHAIOPQVAVLJZVDVOUQVRVB
      VMVCVNVAVLASOVAVLAIOPQVABJZVDUTUQVSVBURVCUSVABASOVABAIOPQUQVEAVFAUKAUBUCV
      HEFZUQVKVOVTVHGFZUQVKVOLZLVHUDUQWAWBUQWARZVKVOWCVKRVINZVJNZVMVNVKWDWEJWCV
      IVJUEUFWCVMWDJVKAVHUGTWCVNWEJVKAVHUHTUIUJULUMUNUOUP $.
  $}

  ${
    naddwordnex.a $e |- ( ph -> A = ( ( _om .o C ) +o M ) ) $.
    naddwordnex.b $e |- ( ph -> B = ( ( _om .o D ) +o N ) ) $.
    naddwordnex.c $e |- ( ph -> C e. D ) $.
    naddwordnex.d $e |- ( ph -> D e. On ) $.
    naddwordnex.m $e |- ( ph -> M e. _om ) $.
    naddwordnex.n $e |- ( ph -> N e. M ) $.
    $( When ` A ` is the sum of a limit ordinal (or zero) and a natural number
       and ` B ` is the sum of a larger limit ordinal and a smaller natural
       number, ` ( _om .o suc C ) ` lies between ` A ` and ` B ` .
       (Contributed by RP, 14-Feb-2025.) $)
    naddwordnexlem0 $p |- ( ph -> ( A e. ( _om .o suc C ) /\
                                    ( _om .o suc C ) C_ B ) ) $=
      ( com co wcel wss con0 syl2anc sylc csuc comu coa wa omelon onelon oaordi
      a1i omcl jca wceq omsuc 3eltr4d w3a onsuc 3jca onsucss omwordi ontr1 nnon
      syl oaword1 sstrd sseqtrrd ) ABNDUAZUBOZPVFCQANDUBOZFUCOZVGNUCOZBVFANRPZV
      GRPZUDFNPZVHVIPAVJVKVJAUEUHZAVJDRPZVKVMAERPZDEPZVNKJEDUFSZNDUISUJLFNVGUGT
      HAVJVNVFVIUKVMVQNDULSUMAVFNEUBOZGUCOZCAVFVRVSAVERPZVOVJUNVEEQZVFVRQAVTVOV
      JAVNVTVQDUOVAKVMUPAVOVPWAKJEDUQTVEENURTAVRRPZGRPZVRVSQAVJVOWBVMKNEUISAGNP
      ZWCAVJGFPZVLUDWDVMAWEVLMLUJGFNUSTGUTVAVRGVBSVCIVDUJ $.

    $( When ` A ` is the sum of a limit ordinal (or zero) and a natural number
       and ` B ` is the sum of a larger limit ordinal and a smaller natural
       number, ` B ` is equal to or larger than ` A ` .  (Contributed by RP,
       14-Feb-2025.) $)
    naddwordnexlem1 $p |- ( ph -> A C_ B ) $=
      ( com csuc wcel wss wa con0 syl comu co naddwordnexlem0 wi omelon syl2anc
      onelon onsuc omcl sylancr onelss adantrd imp simprr sstrd mpdan ) ABNDOZU
      AUBZPZURCQZRZBCQABCDEFGHIJKLMUCAVARBURCAVABURQZAUSVBUTAURSPZUSVBUDANSPUQS
      PZVCUEADSPZVDAESPDEPVEKJEDUGUFDUHTNUQUIUJURBUKTULUMAUSUTUNUOUP $.

    $( When ` A ` is the sum of a limit ordinal (or zero) and a natural number
       and ` B ` is the sum of a larger limit ordinal and a smaller natural
       number, ` B ` is larger than ` A ` .  (Contributed by RP,
       14-Feb-2025.) $)
    naddwordnexlem2 $p |- ( ph -> A e. B ) $=
      ( com csuc comu co wcel wss wa naddwordnexlem0 ssel impcom syl ) ABNDOPQZ
      RZUECSZTBCRZABCDEFGHIJKLMUAUGUFUHUECBUBUCUD $.

    ${
      $d ph x $.
      $( When ` A ` is the sum of a limit ordinal (or zero) and a natural
         number and ` B ` is the sum of a larger limit ordinal and a smaller
         natural number, every natural sum of ` A ` with a natural number is
         less that ` B ` .  (Contributed by RP, 14-Feb-2025.) $)
      naddwordnexlem3 $p |- ( ph -> A. x e. _om ( A +no x ) e. B ) $=
        ( co wcel com coa con0 wceq cv cnadd wa comu omelon onelon syl2anc omcl
        sylancr nnon syl oacl eqeltrd naddonnn sylan wss naddwordnexlem0 simprd
        csuc adantr jctil nnacl oaordi sylc oaass syl2an3an eqtrd omsuc 3eltr4d
        oveq1d sseldd eqeltrrd ex ralrimiv ) ACBUAZUBOZDPZBQAVOQPZVQAVRUCZCVORO
        ZVPDACSPVRVTVPTACQEUDOZGROZSIAWASPZGSPZWBSPAQSPZESPZWCUEAFSPEFPWFLKFEUF
        UGZQEUHUIZAGQPZWDMGUJUKZWAGULUGUMCVOUNUOVSQEUSUDOZDVTAWKDUPZVRACWKPWLAC
        DEFGHIJKLMNUQURUTVSWAGVOROZROZWAQROZVTWKVSWEWCUCZWMQPZWNWOPAWPVRAWCWEWH
        UEVAUTAWIVRWQMGVOVBUOWMQWAVCVDVSVTWBVOROZWNVSCWBVORACWBTVRIUTVJAWCWDVRV
        OSPWRWNTWHWJVOUJWAGVOVEVFVGVSWEWFWKWOTUEAWFVRWGUTQEVHUIVIVKVLVMVN $.
    $}

    ${
      $d A x $.  $d B x $.
      $( When ` A ` is the sum of a limit ordinal (or zero) and a natural
         number and ` B ` is the sum of a larger limit ordinal and a smaller
         natural number, some ordinal sum of ` A ` is equal to ` B ` .  This is
         a specialization of ~ oawordex .  (Contributed by RP, 14-Feb-2025.) $)
      oawordex3 $p |- ( ph -> E. x e. On ( A +o x ) = B ) $=
        ( coa co con0 wcel com syl2anc wss cv wceq wrex naddwordnexlem1 wb comu
        omelon a1i onelon omcl nnon syl oacl eqeltrd wa jca ontr1 sylc oawordex
        mpbid ) ACDUAZCBUBOPDUCBQUDZACDEFGHIJKLMNUEACQRDQRVBVCUFACSEUGPZGOPZQIA
        VDQRZGQRZVEQRASQRZEQRZVFVHAUHUIZAFQRZEFRVILKFEUJTSEUKTAGSRZVGMGULUMVDGU
        NTUOADSFUGPZHOPZQJAVMQRZHQRZVNQRAVHVKVOVJLSFUKTAHSRZVPAVHHGRZVLUPVQVJAV
        RVLNMUQHGSURUSHULUMVMHUNTUOBCDUTTVA $.
    $}

    ${
      $d A x $.  $d B x $.  $d C x y z $.  $d D x y z $.  $d S x z $.
      $d ph y z $.
      naddwordnexlem4.s $e |- S = { y e. On | D C_ ( C +o y ) } $.
      $( When ` A ` is the sum of a limit ordinal (or zero) and a natural
         number and ` B ` is the sum of a larger limit ordinal and a smaller
         natural number, there exists a product with omega such that the
         ordinal sum with ` A ` is less than or equal to ` B ` while the
         natural sum is larger than ` B ` .  (Contributed by RP,
         15-Feb-2025.) $)
      naddwordnexlem4 $p |- ( ph -> E. x e. ( On \ 1o ) ( ( C +o x ) = D /\
                                   ( A +o ( _om .o x ) ) C_ B /\
                              B e. ( A +no ( _om .o x ) ) ) ) $=
        ( wcel coa co vz cint con0 c1o cdif wceq com comu wss cnadd w3a cv wrex
        c0 wne ssrab3 crab oveq2 sseq2d onelon syl2anc oaword2 elrabd eleqtrrdi
        ne0d oninton sylancr wi wa wn oa0 syl sylan9eqr adantr eqeltrd ex con3d
        wral wb oacl sylan ontri1 syl2an2r on0eln0 df-ne bitrdi adantl ralrimiv
        3imtr4d 0ex elintrab sylibr inteqi ondif1 sylanbrc csuc cvv onzsl sylib
        wlim w3o onelpss mpbid simpld eqsstrd oasuc vex sucid mpbiri a1i eleq2i
        eleq2 weq onnminsb biimtrid con2bid sylibrd onsucss imp rexlimdva2 ciun
        3syld oalim ancrd expimpd rspcev nfcv omelon omcl jca sylc nnon syl3anc
        oveq1d oveq2d 3eqtrd 3jca naddonnn naddass eqtr2d iunss 3jaod mpd nfint
        onelss nfrab1 nfov onminsb oveq2i sseqtrrdi eqssd ontr1 oaword1 omword1
        oaass jctil oaabs syl21anc odi 3eqtr2d 3sstr4d naddcl naddgeoa oawordri
        nfss eqtr3d eqtrd naddcom sseqtrd oaordi sseldd eqeq1d sseq1d 3anbi123d
        eleq2d ) AHUBZUCUDUEZRZFUVPSTZGUFZDUGUVPUHTZSTZEUIZEDUWAUJTZRZUKZFBULZS
        TZGUFZDUGUWGUHTZSTZEUIZEDUWJUJTZRZUKZBUVQUMAUVPUCRZUNUVPRZUVRAHUCUIHUNU
        OUWPGFCULZSTZUIZCUCHQUPAHGAGUWTCUCUQZHAUWTGFGSTZUIZCGUCUWRGUFUWSUXBGUWR
        GFSURUSZNAGUCRZFUCRZUXCNAUXEFGRZUXFNMGFUTVAZGFVBVAZVCQVDVEHVFVGZAUNUXAU
        BZUVPAUWTUNUWRRZVHZCUCVRUNUXKRAUXMCUCAUWRUCRZUXMAUXNVIZUWSGRZVJZUWRUNUF
        ZVJZUWTUXLUXOUXRUXPAUXRUXPVHUXNAUXRUXPAUXRVIUWSFGUXRAUWSFUNSTZFUWRUNFSU
        RAUXFUXTFUFUXHFVKVLZVMAUXGUXRMVNVOVPVNVQAUXEUXNUWSUCRZUWTUXQVSNAUXFUXNU
        YBUXHFUWRVTWAGUWSWBWCUXNUXLUXSVSAUXNUXLUWRUNUOUXSUWRWDUWRUNWEWFWGWIVPWH
        UWTCUNUCWJWKWLHUXAQWMZVDZUVPWNWOAUVTUWCUWEAUVSGAUVPUNUFZUVPUAULZWPZUFZU
        AUCUMZUVPWQRUVPWTVIZXAZUVSGUIZAUWPUYKUXJUAUVPWRWSAUYEUYLUYIUYJAUYEUYLAU
        YEVIUVSFGUYEAUVSUXTFUVPUNFSURUYAVMAFGUIZUYEAUYMFGUOZAUXGUYMUYNVIZMAUXFU
        XEUXGUYOVSUXHNFGXBVAXCXDVNXEVPAUYHUYLUAUCAUYFUCRZVIZUYHVIUVSFUYFSTZWPZG
        UYHUYQUVSFUYGSTZUYSUVPUYGFSURAUXFUYPUYTUYSUFUXHFUYFXFWAVMUYQUYHUYSGUIZU
        YQUYHUYFUVPRZUYRGRZVUAUYHVUBVHUYQUYHVUBUYFUYGRUYFUAXGXHUVPUYGUYFXLXIXJU
        YQVUBGUYRUIZVJZVUCVUBUYFUXKRZUYQVUEUVPUXKUYFUYCXKUYPVUFVUEVHAUWTVUDCUYF
        CUAXMUWSUYRGUWRUYFFSURUSXNWGXOUYQVUDVUCAUXEUYPUYRUCRZVUDVUCVJVSNAUXFUYP
        VUGUXHFUYFVTWAGUYRWBWCXPXQZAVUCVUAVHZUYPAUXEVUINGUYRXRVLVNYBXSXEXTAUYJU
        YLAUYJVIUVSUAUVPUYRYAZGAUXFUYJUVSVUJUFUXHUAFUVPWQYCWAAVUJGUIZUYJAUYRGUI
        ZUAUVPVRVUKAVULUAUVPAVUBUYPVUBVIVUCVULAVUBUYPAVUBUYPAUWPVUBUYPUXJUVPUYF
        UTWAVPYDAUYPVUBVUCVUHYEAUXEVUCVULVHNGUYRUUEVLYBWHUAUVPUYRGUUAWLVNXEVPUU
        BUUCAGFUXKSTZUVSAUWTCUCUMZGVUMUIZAUXEUXCVUNNUXIUWTUXCCGUCUXDYFVAUWTVUOC
        CGVUMCGYGCFUXKSCFYGCSYGCUXAUWTCUCUUFUUDUUGUVEUWRUXKUFUWSVUMGUWRUXKFSURU
        SUUHVLUVPUXKFSUYCUUIUUJUUKZAUGGUHTZVUQJSTZUWBEAVUQUCRZJUCRZVUQVURUIAUGU
        CRZUXEVUSYHNUGGYIVGZAJUGRZVUTAVVAJIRZIUGRZVIVVCVVAAYHXJZAVVDVVEPOYJJIUG
        UULYKJYLVLVUQJUUMVAAUWBUGFUHTZISTZUWASTZVVGIUWASTZSTZVUQADVVHUWASKYNAVV
        GUCRZIUCRZUWAUCRZVVIVVKUFAVVAUXFVVLYHUXHUGFYIVGZAVVEVVMOIYLVLZAVVAUWPVV
        NYHUXJUGUVPYIVGZVVGIUWAUUOYMAVVKVVGUWASTZUGUVSUHTZVUQAVVJUWAVVGSAVVEVVN
        UGUWAUIZVVJUWAUFOVVQAVVAUWPVIUWQVVTAUWPVVAUXJYHUUPUYDUGUVPUUNVAIUWAUUQU
        URYOAVVAUXFUWPVVSVVRUFVVFUXHUXJUGFUVPUUSYMZAUVSGUGUHVUPYOZUUTYPLUVAAVUQ
        ISTZUWDEAVWCVVGUWAUJTZISTZUWDAVUSVWDUCRZVVMUKVUQVWDUIVWCVWEUIAVUSVWFVVM
        VVBAVVLVVNVWFVVOVVQVVGUWAUVBVAZVVPYQAVUQVVRVWDAVVSVUQVVRVWBVWAUVFAVVLVV
        NVVRVWDUIVVOVVQVVGUWAUVCVAXEVUQVWDIUVDYKAUWDVVGIUJTZUWAUJTZVWEADVWHUWAU
        JADVVHVWHKAVVLVVEVVHVWHUFVVOOVVGIYRVAUVGYNAVWIVVGIUWAUJTZUJTZVVGUWAIUJT
        ZUJTZVWEAVVLVVMVVNVWIVWKUFVVOVVPVVQVVGIUWAYSYMAVWJVWLVVGUJAVVMVVNVWJVWL
        UFVVPVVQIUWAUVHVAYOAVWEVWDIUJTZVWMAVWFVVEVWEVWNUFVWGOVWDIYRVAAVVLVVNVVM
        VWNVWMUFVVOVVQVVPVVGUWAIYSYMYTYPYTUVIAEVURVWCLAVVMVUSVIVVDVURVWCRAVVMVU
        SVVPVVBYJPJIVUQUVJYKVOUVKYQUWOUWFBUVPUVQUWGUVPUFZUWIUVTUWLUWCUWNUWEVWOU
        WHUVSGUWGUVPFSURUVLVWOUWKUWBEVWOUWJUWADSUWGUVPUGUHURZYOUVMVWOUWMUWDEVWO
        UWJUWADUJVWPYOUVOUVNYFVA $.
    $}
  $}

  $( If an ordinal is less than or equal to the successor of another, then the
     first is either less than or equal to the second or the first is equal to
     the successor of the second.  Theorem 1 in Grzegorz Bancerek, "Epsilon
     Numbers and Cantor Normal Form", Formalized Mathematics, Vol. 17, No. 4,
     Pages 249&ndash;256, 2009.  DOI: 10.2478/v10037-009-0032-8 See also
     ~ ordsssucb for a biimplication when ` A ` is a set.  (Contributed by RP,
     3-Jan-2025.) $)
  ordsssucim $p |- ( ( Ord A /\ Ord B ) ->
                     ( A C_ suc B -> ( A C_ B \/ A = suc B ) ) ) $=
    ( word wa csuc wss wcel wceq wo wb ordsuc ordsseleq sylan2b wtr simpr ordtr
    wi trsucss 3syl orim1d sylbid ) ACZBCZDZABEZFZAUEGZAUEHZIZABFZUHIUCUBUECUFU
    IJBKAUELMUDUGUJUHUDUCBNUGUJQUBUCOBPBARSTUA $.

  $( The intersection of a class and its successor is itself.  (Contributed by
     RP, 3-Jan-2025.) $)
  insucid $p |- ( A i^i suc A ) = A $=
    ( csuc wss cin wceq sssucid dfss2 mpbi ) AABZCAIDAEAFAIGH $.

  $( Multiplication eventually dominates addition.  (Contributed by RP,
     3-Jan-2025.) $)
  oaltom $p |- ( ( A e. On /\ B e. On ) -> ( ( 1o e. A /\ A e. B ) ->
                 ( B +o A ) e. ( B .o A ) ) ) $=
    ( con0 wcel wa c1o coa comu c2o wceq om2 ad2antlr wss a1i simpr adantr sylc
    co jca eqsstrd w3a simpl 3jca csuc df-2o word simprl eloni ordelsuc omwordi
    2on biimpd oaordi imp syl2an sseldd ex ) ACDZBCDZEZFADZABDZEZBAGRZBAHRZDUTV
    CEZBBGRZVEVDVFVGBIHRZVEUSVGVHJURVCBKLVFICDZURUSUAZIAMVHVEMUTVJVCUTVIURUSVIU
    TUKNURUSUBURUSOZUCPVFIFUDZAIVLJVFUENVFVAAUFZEZVAVLAMZVFVAVMUTVAVBUGZUTVMVCU
    RVMUSAUHPPSVPVNVAVOFAAUIULQTIABUJQTUTUSUSEZVBVDVGDZVCUTUSUSVKVKSVAVBOVQVBVR
    ABBUMUNUOUPUQ $.

  $( Two ways to square an ordinal.  (Contributed by RP, 3-Jan-2025.) $)
  oe2 $p |- ( A e. On -> ( A .o A ) = ( A ^o 2o ) ) $=
    ( con0 wcel c2o coe co c1o csuc comu df-2o oveq2i wceq 1on oesuc oe1 oveq1d
    mpan2 eqtrd eqtr2id ) ABCZADEFAGHZEFZAAIFZDUAAEJKTUBAGEFZAIFZUCTGBCUBUELMAG
    NQTUDAAIAOPRS $.

  $( Exponentiation eventually dominates multiplication.  (Contributed by RP,
     3-Jan-2025.) $)
  omltoe $p |- ( ( A e. On /\ B e. On ) -> ( ( 1o e. A /\ A e. B ) ->
                 ( B .o A ) e. ( B ^o A ) ) ) $=
    ( con0 wcel wa c1o comu co coe c2o simpr adantr syl c0 wss a1i simpl adantl
    wceq sylc oe2 w3a 2on 3jca wne ne0d wb on0eln0 mpbird csuc df-2o word eloni
    jca ordelsuc biimpd eqsstrd oewordi jca31 omordi sseldd ex ) ACDZBCDZEZFADZ
    ABDZEZBAGHZBAIHZDVEVHEZBBGHZVJVIVKVLBJIHZVJVKVDVLVMSVEVDVHVCVDKZLZBUAMVKJCD
    ZVCVDUBZNBDZEJAOVMVJOVKVQVRVEVQVHVEVPVCVDVPVEUCPVCVDQVNUDLVKVRBNUEZVKBAVHVG
    VEVFVGKRZUFVKVDVRVSUGVOBUHMUIZUNVKJFUJZAJWBSVKUKPVKVFAULZEZVFWBAOZVKVFWCVHV
    FVEVFVGQRZVEWCVHVCWCVDAUMLLUNWFWDVFWEFAAUOUPTUQJABURTUQVKVDVDEVREVGVIVLDVKV
    DVDVRVOVOWAUSVTABBUTTVAVB $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Surreal Contributions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    abeqabi.a $e |- A = { x | ps } $.
    $( Generalized condition for a class abstraction to be equal to some class.
       (Contributed by RP, 2-Sep-2024.) $)
    abeqabi $p |- ( { x | ph } = A <-> A. x ( ph <-> ps ) ) $=
      ( cab wceq wb wal eqeq2i abbib bitri ) ACFZDGMBCFZGABHCIDNMEJABCKL $.
  $}

  ${
    $d x Y $.  $d x Z $.
    $( Condition for a class abstraction to be a pair.  (Contributed by RP,
       25-Aug-2024.) $)
    abpr $p |- ( { x | ph } = { Y , Z } <->
                 A. x ( ph <-> ( x = Y \/ x = Z ) ) ) $=
      ( cv wceq wo cpr dfpr2 abeqabi ) ABEZCFKDFGBCDHBCDIJ $.
  $}

  ${
    $d x X $.  $d x Y $.  $d x Z $.
    $( Condition for a class abstraction to be a triple.  (Contributed by RP,
       25-Aug-2024.) $)
    abtp $p |- ( { x | ph } = { X , Y , Z } <->
                 A. x ( ph <-> ( x = X \/ x = Y \/ x = Z ) ) ) $=
      ( cv wceq w3o ctp dftp2 abeqabi ) ABFZCGLDGLEGHBCDEIBCDEJK $.
  $}

  ${
    $d o O $.  $d x o y $.  $d ph o $.  $d ps x y $.  $d ch o $.
    ralopabb.o $e |- O = { <. x , y >. | ph } $.
    ralopabb.p $e |- ( o = <. x , y >. -> ( ps <-> ch ) ) $.
    $( Restricted universal quantification over an ordered-pair class
       abstraction.  (Contributed by RP, 25-Sep-2024.) $)
    ralopabb $p |- ( A. o e. O ps <-> A. x A. y ( ph -> ch ) ) $=
      ( wral wi wal wn wex wrex 2nalexn wa cv cop wceq notbid rexopabb 3bitr2ri
      annim 2exbii bitri rexnal con4bii ) BFGJZACKZELDLZUKMUJMZENDNZBMZFGOZUIMU
      JDEPUOACMZQZENDNUMAUNUPDEFGHFRDRERSTBCIUAUBUQULDEACUDUEUFBFGUGUCUH $.
  $}

  ${
    fpwfvss.f $e |- F : C --> ~P B $.
    $( Functions into a powerset always have values which are subsets.  This is
       dependant on our convention when the argument is not part of the domain.
       (Contributed by RP, 13-Sep-2024.) $)
    fpwfvss $p |- ( F ` A ) C_ B $=
      ( wcel cfv wss cpw ffvelcdmi elpwid wn cdm wceq fdmi eleq2i ndmfv sylnbir
      c0 0ss eqsstrdi pm2.61i ) ACFZADGZBHUCUDBCBIZADEJKUCLUDSBUCADMZFUDSNUFCAC
      UEDEOPADQRBTUAUB $.
  $}

  $( A class that strictly dominates any set is not empty.  (Suggested by SN,
     14-Jan-2025.)  (Contributed by RP, 14-Jan-2025.) $)
  sdomne0 $p |- ( B ~< A -> A =/= (/) ) $=
    ( csdm wbr c0 wne wcel wi relsdom brrelex1i wceq breq1 biimpd 0sdomg sdomtr
    cvv a1i ex biimtrrdi syl pm2.61dne wb brrelex2i ibi syl6 pm2.43i ) BACDZAEF
    ZUGUGEACDZUHUGBPGZUGUIHZBACIJUJUKBEBEKZUKHUJULUGUIBEACLMQUJBEFEBCDZUKBPNUMU
    GUIEBAORSUATUIUHUIAPGUIUHUBEACIUCAPNTUDUEUF $.

  ${
    sdomne0d.a $e |- ( ph -> B ~< A ) $.
    sdomne0d.b $e |- ( ph -> B e. V ) $.
    $( A class that strictly dominates any set is not empty.  (Contributed by
       RP, 3-Sep-2024.) $)
    sdomne0d $p |- ( ph -> A =/= (/) ) $=
      ( csdm wbr c0 wne wcel wi wceq breq1 biimpd a1i 0sdomg sdomtr syl cvv ibi
      ex biimtrrdi pm2.61dne wb relsdom brrelex2i syl6 mpd ) ACBGHZBIJZEAUJIBGH
      ZUKACDKZUJULLZFUMUNCICIMZUNLUMUOUJULCIBGNOPUMCIJICGHZUNCDQUPUJULICBRUBUCU
      DSULUKULBTKULUKUEIBGUFUGBTQSUAUHUI $.
  $}

  ${
    $d ph x $.  $d A x $.  $d B x $.  $d R x $.  $d O x $.
    safesnsupfiss.small $e |- ( ph -> ( O = (/) \/ O = 1o ) ) $.
    safesnsupfiss.finite $e |- ( ph -> B e. Fin ) $.
    safesnsupfiss.subset $e |- ( ph -> B C_ A ) $.
    safesnsupfiss.ordered $e |- ( ph -> R Or A ) $.
    $( If ` B ` is a finite subset of ordered class ` A ` , we can safely
       create a small subset with the same largest element and upper bound, if
       any.  (Contributed by RP, 1-Sep-2024.) $)
    safesnsupfiss $p |- ( ph ->
                     if ( O ~< B , { sup ( B , A , R ) } , B ) C_ B ) $=
      ( vx wcel wa wo wceq simpr c0 adantr con0 c1o eleq1 csdm wbr csup csn cif
      cv elif elsni wor cfn wne wss 0elon mpbiri 1on jaoi syl sdomne0d syl13anc
      wn fisupcl eqeltrd ex syl5 expimpd wi a1i jaod biimtrid ssrdv ) AJECUAUBZ
      CBDUCZUDZCUEZCJUFZVNKVKVOVMKZLZVKUTZVOCKZLZMAVSVKVOVMCUGAVQVSVTAVKVPVSVPV
      OVLNZAVKLZVSVOVLUHWBWAVSWBWALVOVLCWBWAOWBVLCKZWAWBBDUIZCUJKZCPUKCBULZWCAW
      DVKIQAWEVKGQWBCERAVKOAERKZVKAEPNZESNZMWGFWHWGWIWHWGPRKUMEPRTUNWIWGSRKUOES
      RTUNUPUQQURAWFVKHQBCDVAUSQVBVCVDVEVTVSVFAVRVSOVGVHVIVJ $.
  $}

  ${
    $d ph x $.
    safesnsupfiub.small $e |- ( ph -> ( O = (/) \/ O = 1o ) ) $.
    safesnsupfiub.finite $e |- ( ph -> B e. Fin ) $.
    safesnsupfiub.subset $e |- ( ph -> B C_ A ) $.
    safesnsupfiub.ordered $e |- ( ph -> R Or A ) $.
    safesnsupfiub.ub $e |- ( ph -> A. x e. B A. y e. C x R y ) $.
    $( If ` B ` is a finite subset of ordered class ` A ` , we can safely
       create a small subset with the same largest element and upper bound, if
       any.  (Contributed by RP, 1-Sep-2024.) $)
    safesnsupfiub $p |- ( ph ->
                  A. x e. if ( O ~< B , { sup ( B , A , R ) } , B )
                  A. y e. C
                  x R y ) $=
      ( cv wbr wral csdm csup csn wcel cif safesnsupfiss sseld imim1d ralimdv2
      mpd ) ABNZCNGOCFPZBEPUHBHEQOEDGRSEUAZPMAUHUHBEUIAUGUITUGETUHAUIEUGADEGHIJ
      KLUBUCUDUEUF $.
  $}

  ${
    safesnsupfidom1o.small $e |- ( ph -> ( O = (/) \/ O = 1o ) ) $.
    safesnsupfidom1o.finite $e |- ( ph -> B e. Fin ) $.
    $( If ` B ` is a finite subset of ordered class ` A ` , we can safely
       create a small subset with the same largest element and upper bound, if
       any.  (Contributed by RP, 1-Sep-2024.) $)
    safesnsupfidom1o $p |- ( ph ->
                     if ( O ~< B , { sup ( B , A , R ) } , B ) ~<_ 1o ) $=
      ( wbr c1o cdom wa wceq adantl cvv wcel con0 1on ax-mp c0 wi csdm csup csn
      cif iftrue ensn1g domrefg endomtr sylancl wn snprc snex eqeng sylbi 0domg
      cen pm2.61i eqbrtrdi iffalse cfn wo wb 0elon eleq1 mpbiri fidomtri sylan2
      jaoi breq2 domtr mpan2 biimtrdi biimpd sylbird syl2anc eqbrtrd pm2.61dan
      imp ) AECUAHZVSCBDUBZUCZCUDZIJHAVSKWBWAIJVSWBWALAVSWACUEMVTNOZWAIJHZWCWAI
      UPHIIJHZWDVTNUFIPOZWEQIPUGRWAIIUHUIWCUJZWASUPHZSIJHZWDWGWASLZWHVTUKWANOWJ
      WHTVTULWASNUMRUNWFWIQIPUORZWASIUHUIUQURAVSUJZKWBCIJWLWBCLAVSWACUSMAWLCIJH
      ZACUTOZESLZEILZVAZWLWMTGFWNWQKWLCEJHZWMWQWNEPOZWRWLVBWOWSWPWOWSSPOVCESPVD
      VEWPWSWFQEIPVDVEVHCEPVFVGWQWRWMTZWNWOWTWPWOWRCSJHZWMESCJVIXAWIWMWKCSIVJVK
      VLWPWRWMEICJVIVMVHMVNVOVRVPVQ $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d O x y $.  $d R x y $.  $d ph x $.
    safesnsupfilb.small $e |- ( ph -> ( O = (/) \/ O = 1o ) ) $.
    safesnsupfilb.finite $e |- ( ph -> B e. Fin ) $.
    safesnsupfilb.subset $e |- ( ph -> B C_ A ) $.
    safesnsupfilb.ordered $e |- ( ph -> R Or A ) $.
    $( If ` B ` is a finite subset of ordered class ` A ` , we can safely
       create a small subset with the same largest element and upper bound, if
       any.  (Contributed by RP, 3-Sep-2024.) $)
    safesnsupfilb $p |- ( ph ->
                  A. x e. ( B \ if ( O ~< B , { sup ( B , A , R ) } , B ) )
                  A. y e. if ( O ~< B , { sup ( B , A , R ) } , B )
                  x R y ) $=
      ( wbr wral cdif wa wcel wceq wo c0 con0 csdm cv csup csn cif wne ad2antrr
      wi wor wss cfn simpr eqidd supgtoreq df-or orcom imbi1i 3bitr4i ralrimiva
      wn df-ne sylib iftrue difeq2d adantl raleqdv iftrued w3a adantr c1o 0elon
      wb eleq1 mpbiri 1on jaoi syl sdomne0d fisupcl syl2an2r breq2 ralsng bitrd
      3jca ralbidv raldifsnb bitr4di mpbird ral0 iffalse difid eqtrdi pm2.61dan
      ) AGEUALZBUBZCUBZFLZCWNEDFUCZUDZEUEZMZBEWTNZMZAWNOZXCWOWRUFZWOWRFLZUHZBEM
      ZXDXGBEXDWOEPZOZXFWOWRQZRZXGXJDEWOFWRADFUIZWNXIKUGAEDUJZWNXIJUGAEUKPZWNXI
      IUGXDXIULXJWRUMUNXKXFRXKUTZXFUHXLXGXKXFUOXFXKUPXEXPXFWOWRVAUQURVBUSXDXCXA
      BEWSNZMZXHXDXABXBXQWNXBXQQAWNWTWSEWNWSEVCVDVEVFXDXRXFBXQMXHXDXAXFBXQXDXAW
      QCWSMZXFXDWQCWTWSXDWNWSEAWNULZVGVFXDWREPZXSXFVLAXMWNXOESUFZXNVHYAKXDXOYBX
      NAXOWNIVIXDEGTXTXDGSQZGVJQZRZGTPZAYEWNHVIYCYFYDYCYFSTPVKGSTVMVNYDYFVJTPVO
      GVJTVMVNVPVQVRAXNWNJVIWDDEFVSVTWQXFCWREWPWRWOFWAWBVQWCWEXFBEWRWFWGWCWHAWN
      UTZOZXCXABSMXABWIYHXABXBSYHXBEENSYHWTEEYGWTEQAWNWSEWJVEVDEWKWLVFVNWM $.
  $}

  ${
    isoeq145.1 $e |- ( ph -> F = G ) $.
    isoeq145.4 $e |- ( ph -> A = C ) $.
    isoeq145.5 $e |- ( ph -> B = D ) $.
    $( Equality deduction for isometries.  (Contributed by RP, 14-Jan-2025.) $)
    isoeq145d $p |- ( ph -> ( F Isom R , S ( A , B )
                          <-> G Isom R , S ( C , D ) ) ) $=
      ( wiso wceq wb isoeq1 syl isoeq4 isoeq5 3bitrd ) ABCFGHMZBCFGIMZDCFGIMZDE
      FGIMZAHINUAUBOJBCFGIHPQABDNUBUCOKBCDFGIRQACENUCUDOLDCEFGISQT $.
  $}

  ${
    resisoeq45.4 $e |- ( ph -> A = C ) $.
    resisoeq45.5 $e |- ( ph -> B = D ) $.
    $( Equality deduction for equally restricted isometries.  (Contributed by
       RP, 14-Jan-2025.) $)
    resisoeq45d $p |- ( ph -> ( ( F |` A ) Isom R , S ( A , B )
                           <-> ( F |` C ) Isom R , S ( C , D ) ) ) $=
      ( cres reseq2d isoeq145d ) ABCDEFGHBKHDKABDHILIJM $.
  $}

  $( An equivalence between identically restricted order-reversing
     self-isometries.  (Contributed by RP, 30-Sep-2024.) $)
  negslem1 $p |- ( A = B ->
                   ( ( F |` A ) Isom R , `' R ( A , A ) <->
                     ( F |` B ) Isom R , `' R ( B , B ) ) ) $=
    ( wceq ccnv id resisoeq45d ) ABEZAABBCCFDIGZJH $.

  ${
    $d x A $.  $d x F $.
    $( Equivalence to saying the converse of an involution is the function
       itself.  (Contributed by RP, 13-Oct-2024.) $)
    nvocnvb $p |- ( ( F Fn A /\ `' F = F ) <->
                    ( F : A -1-1-onto-> A /\
                      A. x e. A ( F ` ( F ` x ) ) = x ) ) $=
      ( wfn ccnv wceq wa wf1o cv cfv wral nvof1o fveq1 ad2antlr f1ocnvfv1 sylan
      wcel eqtr3d ralrimiva jca wf f1of ffn adantr nvocnv impbii ) CBDZCEZCFZGZ
      BBCHZAIZCJZCJZULFZABKZGUJUKUPBCLZUJUOABUJULBQZGUMUHJZUNULUIUSUNFUGURUMUHC
      MNUJUKURUSULFUQBBULCOPRSTUKBBCUAZUPUJBBCUBUTUPGUGUIUTUGUPBBCUCUDABCUETPUF
      $.
  $}

  ${
    $d A a b x y $.  $d B a b x y $.  $d R a b $.  $d S a b $.
    $( The following is probably most useful when ` R Or S ` . $)
    nla0001.defslts $e |- .< = { <. a , b >. | ( a C_ S /\ b C_ S /\
                             A. x e. a A. y e. b x R y ) } $.
    $( Binary relation form of a relation, ` .< ` , which has been extended
       from relation ` R ` to subsets of class ` S ` .  Usually, we will assume
       ` R Or S ` .  Definition in [Alling], p. 2.  Generalization of
       ~ brslts .  (Originally by Scott Fenton, 8-Dec-2021.)  (Contributed by
       RP, 28-Nov-2023.) $)
    rp-brsslt $p |- ( A .< B <-> ( ( A e. _V /\ B e. _V ) /\ ( A C_ S /\ B C_
      S /\ A. x e. A A. y e. B x R y ) ) ) $=
      ( cv wss wbr wral w3a wceq sseq1 raleq 3anbi13d ralbidv 3anbi23d bropabg
      ) HKZFLZIKZFLZAKBKEMZBUENZAUCNZOCFLZUFUHACNZOUJDFLZUGBDNZACNZOHICDGUCCPUD
      UJUIUKUFUCCFQUHAUCCRSUEDPZUFULUKUNUJUEDFQUOUHUMACUGBUEDRTUAJUB $.

    ${
      nla0001.set $e |- ( ph -> A e. _V ) $.
      nla0002.sset $e |- ( ph -> A C_ S ) $.
      $( Extending a linear order to subsets, the empty set is less than any
         subset.  Note in [Alling], p. 3.  (Contributed by RP, 28-Nov-2023.) $)
      nla0002 $p |- ( ph -> (/) .< A ) $=
        ( c0 cvv wcel wss cv wbr wral a1i w3a 0ex 0ss ral0 rp-brsslt syl21anbrc
        3jca ) AMNOZDNOMFPZDFPZBQCQERCDSZBMSZUAMDGRUHAUBTKAUIUJULUIAFUCTLULAUKB
        UDTUGBCMDEFGHIJUEUF $.

      $( Extending a linear order to subsets, the empty set is greater than any
         subset.  Note in [Alling], p. 3.  (Contributed by RP, 28-Nov-2023.) $)
      nla0003 $p |- ( ph -> A .< (/) ) $=
        ( cvv wcel c0 wss cv wbr wral a1i w3a 0ex 0ss ral0 mpbi 3jca syl21anbrc
        ralcom rp-brsslt ) ADMNOMNZDFPZOFPZBQCQERZCOSBDSZUADOGRKUJAUBTAUKULUNLU
        LAFUCTUNAUMBDSZCOSUNUOCUDUMCBODUHUETUFBCDOEFGHIJUIUG $.
    $}

    $( Extending a linear order to subsets, the empty set is less than itself.
       Note in [Alling], p. 3.  (Contributed by RP, 28-Nov-2023.) $)
    nla0001 $p |- ( ph -> (/) .< (/) ) $=
      ( c0 cvv wcel 0ex a1i wss 0ss nla0002 ) ABCJDEFGHIJKLAMNJEOAEPNQ $.
  $}

  ${
    $d A x $.

    $( ` B ` is called a non-limit ordinal if it is not a limit ordinal.
       (Contributed by RP, 27-Sep-2023.)

       Alling, Norman L. "Fundamentals of Analysis Over Surreal Numbers
       Fields."  The Rocky Mountain Journal of Mathematics 19, no. 3 (1989):
       565-73. http://www.jstor.org/stable/44237243. $)
    faosnf0.11b $p |- ( ( Ord A /\ -. Lim A /\ A =/= (/) ) ->
                       E. x e. On A = suc x ) $=
      ( word wlim wn c0 wne w3a wa cv csuc wceq con0 wi 3ancomb df-3an wo df-ne
      wrex anbi2i imbi1i pm5.6 iman 3bitrri dflim3 xchnxbir 3bitri pm3.35 sylbi
      ) BCZBDZEZBFGZHZUJUMIZUOBAJKLAMSZNZIZUPUNUJUMULHUOULIURUJULUMOUJUMULPULUQ
      UOUJBFLZUPQZEIZUQUKUQUJUSEZIZUPNUJUTNVAEUOVCUPUMVBUJBFRTUAUJUSUPUBUJUTUCU
      DABUEUFTUGUOUPUHUI $.
  $}

  ${
    $d f x $.
    $( A surreal number, in the functional sign expansion representation, is a
       function which maps from an ordinal into a set of two possible signs.
       (Contributed by RP, 12-Jan-2025.) $)
    dfno2 $p |- No = { f e. ~P ( On X. { 1o , 2o } ) |
                       ( Fun f /\ dom f e. On ) } $=
      ( vx cv c1o c2o cpr wf con0 wrex cab cxp cpw wcel wfun cdm wa adantl wceq
      wss simpl csur crab fssxp onss adantr xpss1 syl sstrd sylibr ffun eqeltrd
      velpw fdm jca32 rexlimiva simprr wb feq2 funssxp simplbi syl2anr rspcedvd
      elpwi impbii abbii df-no df-rab 3eqtr4i ) BCZDEFZACZGZBHIZAJVKHVJKZLZMZVK
      NZVKOZHMZPZPZAJUAVTAVOUBVMWAAVMWAVLWABHVIHMZVLPZVPVQVSWCVKVNSZVPWCVKVIVJK
      ZVNVLVKWESWBVIVJVKUCQWCVIHSZWEVNSWBWFVLVIUDUEVIHVJUFUGUHAVNULUIVLVQWBVIVJ
      VKUJQWCVRVIHVLVRVIRWBVIVJVKUMQWBVLTUKUNUOWAVLVRVJVKGZBVRHVPVQVSUPVIVRRVLW
      GUQWAVIVRVJVKURQVTVQWDWGVPVQVSTVKVNVCVQWDPWGVRHSHVJVKUSUTVAVBVDVEABVFVTAV
      OVGVH $.
  $}

  $( Every ordinal maps to a surreal number.  (Contributed by RP,
     21-Sep-2023.) $)
  onnoxpg $p |- ( ( A e. On /\ B e. { 1o , 2o } )
              -> ( A X. { B } ) e. No ) $=
    ( con0 wcel c1o c2o cpr csn cxp csur fconst6g adantl w3a wfun cdm crn simp3
    wf wss ffund c0 wceq simp2 snnzg dmxp eqcomd 3syl simp1 eqeltrrd frnd elno2
    wne syl3anbrc mpd3an3 ) ACDZBEFGZDZAUPABHZIZRZUSJDZUQUTUOABUPKLUOUQUTMZUSNU
    SOZCDUSPUPSVAVBAUPUSUOUQUTQZTVBAVCCVBUQURUAULZAVCUBUOUQUTUCBUPUDVEVCAAURUEU
    FUGUOUQUTUHUIVBAUPUSVDUJUSUKUMUN $.

  $( Every ordinal maps to a surreal number of that birthday.  (Contributed by
     RP, 21-Sep-2023.) $)
  onnobdayg $p |- ( ( A e. On /\ B e. { 1o , 2o } )
                  -> ( bday ` ( A X. { B } ) ) = A ) $=
    ( con0 wcel c1o c2o cpr csn cxp cbday cfv cdm csur wceq onnoxpg bdayval syl
    wa c0 wne simpr snnzg dmxp 3syl eqtrd ) ACDZBEFGZDZRZABHZIZJKZUKLZAUIUKMDUL
    UMNABOUKPQUIUHUJSTUMANUFUHUABUGUBAUJUCUDUE $.

  $( Bounds formed from the birthday are surreal numbers.  (Contributed by RP,
     21-Sep-2023.) $)
  bdaybndex $p |- ( ( A e. No /\ B = ( bday ` A ) /\ C e. { 1o , 2o } )
                   -> ( B X. { C } ) e. No ) $=
    ( csur wcel cbday cfv wceq con0 c1o c2o cpr csn cxp wa simpr bdayval adantr
    cdm eqtrd nodmon eqeltrd onnoxpg stoic3 ) ADEZBAFGZHZBIECJKLEBCMNDEUEUGOZBA
    SZIUHBUFUIUEUGPUEUFUIHUGAQRTUEUIIEUGAUARUBBCUCUD $.

  $( Bounds formed from the birthday have the same birthday.  (Contributed by
     RP, 30-Sep-2023.) $)
  bdaybndbday $p |- ( ( A e. No /\ B = ( bday ` A ) /\ C e. { 1o , 2o } )
                   -> ( bday ` ( B X. { C } ) ) = ( bday ` A ) ) $=
    ( csur wcel cbday cfv wceq c1o c2o cpr w3a csn cxp cdm bdaybndex bdayval c0
    syl wne simp3 snnzg dmxp 3syl simp2 3eqtrd ) ADEZBAFGZHZCIJKZEZLZBCMZNZFGZU
    NOZBUHULUNDEUOUPHABCPUNQSULUKUMRTUPBHUGUIUKUACUJUBBUMUCUDUGUIUKUEUF $.

  $( Every ordinal maps to a surreal number.  (Contributed by RP,
     21-Sep-2023.) $)
  onnoxp $p |- ( A e. On -> ( A X. { 2o } ) e. No ) $=
    ( con0 wcel c2o c1o cpr csn cxp csur 2oex prid2 onnoxpg mpan2 ) ABCDEDFCADG
    HICEDJKADLM $.

  ${
    onnoxpi.on $e |- A e. On $.
    $( Every ordinal maps to a surreal number.  (Contributed by RP,
       21-Sep-2023.) $)
    onnoxpi $p |- ( A X. { 2o } ) e. No $=
      ( con0 wcel c2o csn cxp csur onnoxp ax-mp ) ACDAEFGHDBAIJ $.
  $}

  $( Ordinal zero maps to a surreal number.  (Contributed by RP,
     21-Sep-2023.) $)
  0fno $p |- (/) e. No $=
    ( c0 c2o csn cxp csur 0xp 0elon onnoxpi eqeltrri ) ABCZDAEJFAGHI $.

  $( Ordinal one maps to a surreal number.  (Contributed by RP,
     21-Sep-2023.) $)
  1fno $p |- ( 1o X. { 2o } ) e. No $=
    ( c1o 1on onnoxpi ) ABC $.

  $( Ordinal two maps to a surreal number.  (Contributed by RP,
     21-Sep-2023.) $)
  2fno $p |- ( 2o X. { 2o } ) e. No $=
    ( c2o 2on onnoxpi ) ABC $.

  $( Ordinal three maps to a surreal number.  (Contributed by RP,
     21-Sep-2023.) $)
  3fno $p |- ( 3o X. { 2o } ) e. No $=
    ( c3o 3on onnoxpi ) ABC $.

  $( Ordinal four maps to a surreal number.  (Contributed by RP,
     21-Sep-2023.) $)
  4fno $p |- ( 4o X. { 2o } ) e. No $=
    ( c4o 4on onnoxpi ) ABC $.

  ${
    fnimafnex.f $e |- F Fn B $.
    $( The functional image of a function value exists.  (Contributed by RP,
       31-Oct-2024.) $)
    fnimafnex $p |- ( F " ( G ` A ) ) e. _V $=
      ( wfun cfv cvv wcel cima wfn fnfun ax-mp fvex funimaexg mp2an ) CFZADGZHI
      CRJHICBKQEBCLMADNCRHOP $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Short Studies
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A successor is not a limit ordinal.  (Contributed by RP, 13-Dec-2024.) $)
  nlimsuc $p |- ( A e. On -> -. Lim suc A ) $=
    ( con0 wcel csuc word c0 cuni wceq wlim sucidg wn eloni ordirr eleq2 notbid
    w3a syl syl5ibrcom mt2d neqned onunisuc neeqtrrd neneqd intn3an3d sylnibr
    dflim2 ) ABCZADZEZFUHCZUHUHGZHZPUHIUGULUIUJUGUHUKUGUHAUKUGUHAUGUHAHZAUHCZAB
    JUGUNKUMAACZKZUGAEUPALAMQUMUNUOUHAANORSTAUAUBUCUDUHUFUE $.
  $( $j usage 'nlimsuc' avoids 'ax-un'; $)

  $( 1 is not a limit ordinal.  (Contributed by BTernaryTau, 1-Dec-2024.)
     (Proof shortened by RP, 13-Dec-2024.) $)
  nlim1NEW $p |- -. Lim 1o $=
    ( c0 con0 wcel wlim wn 0elon csuc nlimsuc wceq wb df-1o limeq ax-mp sylnibr
    c1o ) ABCZODZEFPAGZDZQAHORIQSJKORLMNM $.
  $( $j usage 'nlim1NEW' avoids 'ax-un'; $)

  $( 2 is not a limit ordinal.  (Contributed by BTernaryTau, 1-Dec-2024.)
     (Proof shortened by RP, 13-Dec-2024.) $)
  nlim2NEW $p |- -. Lim 2o $=
    ( c1o con0 wcel c2o wlim wn 1on csuc nlimsuc wceq df-2o limeq ax-mp sylnibr
    wb ) ABCZDEZFGPAHZEZQAIDRJQSOKDRLMNM $.
  $( $j usage 'nlim2NEW' avoids 'ax-un'; $)

  $( 3 is not a limit ordinal.  (Contributed by RP, 13-Dec-2024.) $)
  nlim3 $p |- -. Lim 3o $=
    ( c2o con0 wcel c3o wlim wn 2on csuc nlimsuc wceq df-3o limeq ax-mp sylnibr
    wb ) ABCZDEZFGPAHZEZQAIDRJQSOKDRLMNM $.
  $( $j usage 'nlim3' avoids 'ax-un'; $)

  $( 4 is not a limit ordinal.  (Contributed by RP, 13-Dec-2024.) $)
  nlim4 $p |- -. Lim 4o $=
    ( c3o con0 wcel c4o wlim wn 3on csuc nlimsuc wceq df-4o limeq ax-mp sylnibr
    wb ) ABCZDEZFGPAHZEZQAIDRJQSOKDRLMNM $.

  $( Given ` A e. On ` , let ` A +o 1o ` be defined to be the union of ` A `
     and ` { A } ` .  Compare with ~ oa1suc .  (Contributed by RP,
     27-Sep-2023.) $)
  oa1un $p |- ( A e. On -> ( A +o 1o ) = ( A u. { A } ) ) $=
    ( con0 wcel c1o coa co csuc csn cun oa1suc df-suc eqtrdi ) ABCADEFAGAAHIAJA
    KL $.

  $( ` A +o 1o ` is in ` On ` .  (Contributed by RP, 27-Sep-2023.) $)
  oa1cl $p |- ( A e. On -> ( A +o 1o ) e. On ) $=
    ( con0 wcel c1o coa co 1on oacl mpan2 ) ABCDBCADEFBCGADHI $.

  $( 0 is a finite ordinal.  See ~ peano1 .  (Contributed by RP,
     27-Sep-2023.) $)
  0finon $p |- (/) e. ( On i^i Fin ) $=
    ( c0 com con0 cfn cin peano1 onfin2 eleqtri ) ABCDEFGH $.

  $( 1 is a finite ordinal.  See ~ 1onn .  (Contributed by RP, 27-Sep-2023.) $)
  1finon $p |- 1o e. ( On i^i Fin ) $=
    ( c1o com con0 cfn cin 1onn onfin2 eleqtri ) ABCDEFGH $.

  $( 2 is a finite ordinal.  See ~ 1onn .  (Contributed by RP, 27-Sep-2023.) $)
  2finon $p |- 2o e. ( On i^i Fin ) $=
    ( c2o com con0 cfn cin 2onn onfin2 eleqtri ) ABCDEFGH $.

  $( 3 is a finite ordinal.  See ~ 1onn .  (Contributed by RP, 27-Sep-2023.) $)
  3finon $p |- 3o e. ( On i^i Fin ) $=
    ( c3o com con0 cfn cin 3onn onfin2 eleqtri ) ABCDEFGH $.

  $( 4 is a finite ordinal.  See ~ 1onn .  (Contributed by RP, 27-Sep-2023.) $)
  4finon $p |- 4o e. ( On i^i Fin ) $=
    ( c4o com con0 cfn cin 4onn onfin2 eleqtri ) ABCDEFGH $.

  $( The finite ordinals are closed under the add one operation.  (Contributed
     by RP, 27-Sep-2023.) $)
  finona1cl $p |- ( N e. ( On i^i Fin ) -> ( N +o 1o ) e. ( On i^i Fin ) ) $=
    ( com wcel c1o coa co con0 cfn cin 1onn nnacl mpan2 onfin2 eleq2i 3imtr3i )
    ABCZADEFZBCZAGHIZCQSCPDBCRJADKLBSAMNBSQMNO $.

  $( The finite ordinals are a set.  See also ~ onprc and ~ fiprc for proof
     that ` On ` and ` Fin ` are proper classes.  (Contributed by RP,
     27-Sep-2023.) $)
  finonex $p |- ( On i^i Fin ) e. _V $=
    ( com con0 cfn cin cvv onfin2 omex eqeltrri ) ABCDEFGH $.

  ${
    $d K j $.  $d M j $.  $d N j $.
    $( Union of two adjacent finite sets of sequential integers that share a
       common endpoint.  (Suggested by NM, 21-Jul-2005.)  (Contributed by RP,
       14-Dec-2024.) $)
    fzunt $p |- ( ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) /\ ( K <_ M /\ M <_ N ) )
                 -> ( ( K ... M ) u. ( M ... N ) ) = ( K ... N ) ) $=
      ( cz wcel w3a cle wbr wa cfz co wo cr wb zre simprl adantr simprr syl2anc
      elfz1 vj cun simpl2 simpll3 letrd expr anim2d simpll1 anim1d jaod orc jca
      cv ad2antrl letric ancoms sylan olcd orddi sylanbrc impbid sylan2 syl3anl
      ex pm5.32da simp1 simp2 3anass bitrdi simp3 orbi12d 3bitr4g 3bitr4d eqrdv
      elun andi ) ADEZBDEZCDEZFZABGHZBCGHZIZIZUAABJKZBCJKZUBZACJKZWDUAUMZDEZAWI
      GHZWIBGHZIZBWIGHZWICGHZIZLZIZWJWKWOIZIZWIWGEZWIWHEZVQAMEZVRBMEZVSCMEZWCWR
      WTNAOBOCOXCXDXEFZWCIZWJWQWSWJXGWIMEZWQWSNWIOXGXHIZWQWSXIWMWSWPXIWLWOWKXGX
      HWLWOXGXHWLIZIWIBCXGXHWLPXGXDXJXCXDXEWCUCZQXCXDXEWCXJUDXGXHWLRXGWBXJXFWAW
      BRQUEUFUGXIWNWKWOXGXHWNWKXGXHWNIZIABWIXCXDXEWCXLUHXGXDXLXKQXGXHWNPXGWAXLX
      FWAWBPQXGXHWNRUEUFUIUJXIWSWQXIWSIZWKWNLZWKWOLZIZWLWNLZWLWOLZIWQWKXPXIWOWK
      XNXOWKWNUKWKWOUKULUNXMXQXRXIXQWSXGXDXHXQXKXHXDXQWIBUOUPUQQXMWOWLXIWKWORUR
      ULWKWLWNWOUSUTVDVAVBVEVCVTXAWRNWCVTWIWEEZWIWFEZLWJWMIZWJWPIZLXAWRVTXSYAXT
      YBVTXSWJWKWLFZYAVTVQVRXSYCNVQVRVSVFZVQVRVSVGZWIABTSWJWKWLVHVIVTXTWJWNWOFZ
      YBVTVRVSXTYFNYEVQVRVSVJZWIBCTSWJWNWOVHVIVKWIWEWFVOWJWMWPVPVLQVTXBWTNWCVTX
      BWJWKWOFZWTVTVQVSXBYHNYDYGWIACTSWJWKWOVHVIQVMVN $.
  $}

  ${
    $d ph j $.  $d K j $.  $d M j $.  $d N j $.
    fzuntd.k $e |- ( ph -> K e. ZZ ) $.
    fzuntd.m $e |- ( ph -> M e. ZZ ) $.
    fzuntd.n $e |- ( ph -> N e. ZZ ) $.
    fzuntd.km $e |- ( ph -> K <_ M ) $.
    fzuntd.mn $e |- ( ph -> M <_ N ) $.
    $( Union of two adjacent finite sets of sequential integers that share a
       common endpoint.  (Contributed by RP, 14-Dec-2024.) $)
    fzuntd $p |- ( ph -> ( ( K ... M ) u. ( M ... N ) ) = ( K ... N ) ) $=
      ( cfz co cz wcel cle wbr wa wo zred cr adantr vj cun cv simprl letrd expr
      simprr anim2d anim1d jaod orc jca ad2antrl simpr letrid orddi sylanbrc ex
      olcd impbid pm5.32da w3a wb elfz1 syl2anc 3anass bitrdi orbi12d elun andi
      3bitr4g 3bitr4d eqrdv ) AUABCJKZCDJKZUBZBDJKZAUAUCZLMZBVRNOZVRCNOZPZCVRNO
      ZVRDNOZPZQZPZVSVTWDPZPZVRVPMZVRVQMZAVSWFWHAVSPZWFWHWLWBWHWEWLWAWDVTAVSWAW
      DAVSWAPZPZVRCDWNVRAVSWAUDRACSMZWMACFRZTADSMWMADGRTAVSWAUGACDNOWMITUEUFUHW
      LWCVTWDAVSWCVTAVSWCPZPZBCVRABSMWQABERTAWOWQWPTWRVRAVSWCUDRABCNOWQHTAVSWCU
      GUEUFUIUJWLWHWFWLWHPZVTWCQZVTWDQZPZWAWCQZWAWDQZPWFVTXBWLWDVTWTXAVTWCUKVTW
      DUKULUMWSXCXDWLXCWHWLVRCWLVRAVSUNRAWOVSWPTUOTWSWDWAWLVTWDUGUSULVTWAWCWDUP
      UQURUTVAAVRVNMZVRVOMZQVSWBPZVSWEPZQWJWGAXEXGXFXHAXEVSVTWAVBZXGABLMZCLMZXE
      XIVCEFVRBCVDVEVSVTWAVFVGAXFVSWCWDVBZXHAXKDLMZXFXLVCFGVRCDVDVEVSWCWDVFVGVH
      VRVNVOVIVSWBWEVJVKAWKVSVTWDVBZWIAXJXMWKXNVCEGVRBDVDVEVSVTWDVFVGVLVM $.
  $}

  ${
    $d ph j $.  $d K j $.  $d L j $.  $d M j $.  $d N j $.
    fzunt1d.k $e |- ( ph -> K e. ZZ ) $.
    fzunt1d.l $e |- ( ph -> L e. ZZ ) $.
    fzunt1d.m $e |- ( ph -> M e. ZZ ) $.
    fzunt1d.n $e |- ( ph -> N e. ZZ ) $.
    fzunt1d.km $e |- ( ph -> K <_ M ) $.
    fzunt1d.ml $e |- ( ph -> M <_ L ) $.
    fzunt1d.ln $e |- ( ph -> L <_ N ) $.
    $( Union of two overlapping finite sets of sequential integers.
       (Contributed by RP, 14-Dec-2024.) $)
    fzunt1d $p |- ( ph -> ( ( K ... L ) u. ( M ... N ) ) = ( K ... N ) ) $=
      ( cz wcel cle wbr wa wo ad2antrr zred vj cfz co cun cv cr wb simplr simpr
      zre letrd ex anim2d anim1d jaod orc jca ad2antrl adantr orcd olcd lecasei
      simprr orddi sylanbrc impbid sylan2 pm5.32da elfz1 syl2anc 3anass orbi12d
      w3a bitrdi elun andi 3bitr4g 3bitr4d eqrdv ) AUABCUBUCZDEUBUCZUDZBEUBUCZA
      UAUEZMNZBWDOPZWDCOPZQZDWDOPZWDEOPZQZRZQZWEWFWJQZQZWDWBNZWDWCNZAWEWLWNWEAW
      DUFNZWLWNUGWDUJAWRQZWLWNWSWHWNWKWSWGWJWFWSWGWJWSWGQZWDCEAWRWGUHWTCACMNZWR
      WGGSTWTEAEMNZWRWGISTWSWGUIZACEOPWRWGLSUKULUMWSWIWFWJWSWIWFWSWIQZBDWDXDBAB
      MNZWRWIFSTXDDADMNZWRWIHSTAWRWIUHABDOPWRWIJSWSWIUIUKULUNUOWSWNWLWSWNQZWFWI
      RZWFWJRZQZWGWIRZWGWJRZQWLWFXJWSWJWFXHXIWFWIUPWFWJUPUQURXGXKXLWSXKWNWSXKWD
      CAWRUIWSCAXAWRGUSTWTWGWIXCUTWSCWDOPZQZWIWGXNDCWDXNDAXFWRXMHSTXNCAXAWRXMGS
      TAWRXMUHADCOPWRXMKSWSXMUIUKVAVBUSXGWJWGWSWFWJVCVAUQWFWGWIWJVDVEULVFVGVHAW
      DVTNZWDWANZRWEWHQZWEWKQZRWPWMAXOXQXPXRAXOWEWFWGVMZXQAXEXAXOXSUGFGWDBCVIVJ
      WEWFWGVKVNAXPWEWIWJVMZXRAXFXBXPXTUGHIWDDEVIVJWEWIWJVKVNVLWDVTWAVOWEWHWKVP
      VQAWQWEWFWJVMZWOAXEXBWQYAUGFIWDBEVIVJWEWFWJVKVNVRVS $.
  $}

  ${
    $d ph j $.  $d K j $.  $d L j $.  $d M j $.  $d N j $.
    fzuntgd.k $e |- ( ph -> K e. ZZ ) $.
    fzuntgd.l $e |- ( ph -> L e. ZZ ) $.
    fzuntgd.m $e |- ( ph -> M e. ZZ ) $.
    fzuntgd.n $e |- ( ph -> N e. ZZ ) $.
    fzuntgd.km $e |- ( ph -> K <_ M ) $.
    fzuntgd.ml $e |- ( ph -> M <_ ( L + 1 ) ) $.
    fzuntgd.ln $e |- ( ph -> L <_ N ) $.
    $( Union of two adjacent or overlapping finite sets of sequential integers.
       (Contributed by RP, 14-Dec-2024.) $)
    fzuntgd $p |- ( ph -> ( ( K ... L ) u. ( M ... N ) ) = ( K ... N ) ) $=
      ( wcel cle wbr wa wo cr zred ad2antrr vj cfz co cun cv cz wi simplr simpr
      zre letrd ex anim2d anim1d jaod sylan2 orc jca ad2antrl c1 caddc animorrl
      peano2re syl clt adantr lelttric syl2anc wb zltp1le sylan orbi2d mpjaodan
      olcd mpbid simprr orddi sylanbrc impbid pm5.32da w3a elfz1 3anass orbi12d
      bitrdi elun andi 3bitr4g 3bitr4d eqrdv ) AUABCUBUCZDEUBUCZUDZBEUBUCZAUAUE
      ZUFMZBWONOZWOCNOZPZDWONOZWOENOZPZQZPZWPWQXAPZPZWOWMMZWOWNMZAWPXCXEAWPPZXC
      XEWPAWORMZXCXEUGWOUJAXJPZWSXEXBXKWRXAWQXKWRXAXKWRPWOCEAXJWRUHACRMZXJWRACG
      SZTAERMXJWRAEISTXKWRUIACENOXJWRLTUKULUMXKWTWQXAXKWTWQXKWTPBDWOABRMXJWTABF
      STADRMZXJWTADHSZTAXJWTUHABDNOXJWTJTXKWTUIUKULUNUOUPXIXEXCXIXEPZWQWTQZWQXA
      QZPZWRWTQZWRXAQZPXCWQXSXIXAWQXQXRWQWTUQWQXAUQURUSXPXTYAXIXTXEXIWRXTCUTVAU
      CZWONOZXIWRWTVBXIYCPZWTWRYDDYBWOAXNWPYCXOTAYBRMZWPYCAXLYEXMCVCVDTYDWOAWPY
      CUHSADYBNOWPYCKTXIYCUIUKVNXIWRCWOVEOZQZWRYCQXIXJXLYGXIWOAWPUISXICACUFMZWP
      GVFSWOCVGVHXIYFYCWRAYHWPYFYCVIGCWOVJVKVLVOVMVFXPXAWRXIWQXAVPVNURWQWRWTXAV
      QVRULVSVTAWOWKMZWOWLMZQWPWSPZWPXBPZQXGXDAYIYKYJYLAYIWPWQWRWAZYKABUFMZYHYI
      YMVIFGWOBCWBVHWPWQWRWCWEAYJWPWTXAWAZYLADUFMEUFMZYJYOVIHIWODEWBVHWPWTXAWCW
      EWDWOWKWLWFWPWSXBWGWHAXHWPWQXAWAZXFAYNYPXHYQVIFIWOBEWBVHWPWQXAWCWEWIWJ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Additional work on conditional logical operator
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Conjunction of conditional logical operators.  (Contributed by RP,
     18-Apr-2020.) $)
  ifpan123g $p |- ( ( if- ( ph , ch , ta ) /\ if- ( ps , th , et ) )
                      <-> ( ( ( -. ph \/ ch ) /\ ( ph \/ ta ) )
                            /\ ( ( -. ps \/ th ) /\ ( ps \/ et ) ) ) ) $=
    ( wif wn wo wa dfifp4 anbi12i ) ACEGAHCIAEIJBDFGBHDIBFIJACEKBDFKL $.

  $( Conjunction of conditional logical operators.  (Contributed by RP,
     20-Apr-2020.) $)
  ifpan23 $p |- ( ( if- ( ph , ps , ch ) /\ if- ( ph , th , ta ) )
                      <-> if- ( ph , ( ps /\ th ) , ( ch /\ ta ) ) ) $=
    ( wif wa wn wo ifpan123g an4 dfifp4 ordi anbi12i bitr2i 3bitri ) ABCFADEFGA
    HZBIZACIZGQDIZAEIZGGRTGZSUAGZGZABDGZCEGZFZAABDCEJRSTUAKUGQUEIZAUFIZGUDAUEUF
    LUHUBUIUCQBDMACEMNOP $.

  $( Define or in terms of conditional logic operator.  (Contributed by RP,
     20-Apr-2020.) $)
  ifpdfor2 $p |- ( ( ph \/ ps ) <-> if- ( ph , ph , ps ) ) $=
    ( wo wn wa wif pm2.1 biantrur dfifp4 bitr4i ) ABCZADACZKEAABFLKAGHAABIJ $.

  $( Corollary of commutation of or.  (Contributed by RP, 20-Apr-2020.) $)
  ifporcor $p |- ( if- ( ph , ph , ps ) <-> if- ( ps , ps , ph ) ) $=
    ( wo wif orcom ifpdfor2 3bitr3i ) ABCBACAABDBBADABEABFBAFG $.

  $( Define and with conditional logic operator.  (Contributed by RP,
     25-Apr-2020.) $)
  ifpdfan2 $p |- ( ( ph /\ ps ) <-> if- ( ph , ps , ph ) ) $=
    ( wa wi wn wo wif id notnoti biorfri dfifp6 bitr4i ) ABCZMAADZEZFABAGOMNAHI
    JABAKL $.

  $( Corollary of commutation of and.  (Contributed by RP, 25-Apr-2020.) $)
  ifpancor $p |- ( if- ( ph , ps , ph ) <-> if- ( ps , ph , ps ) ) $=
    ( wa wif ancom ifpdfan2 3bitr3i ) ABCBACABADBABDABEABFBAFG $.

  $( Define or in terms of conditional logic operator and true.  (Contributed
     by RP, 20-Apr-2020.) $)
  ifpdfor $p |- ( ( ph \/ ps ) <-> if- ( ph , T. , ps ) ) $=
    ( wo wn wtru wa wif tru olci biantrur dfifp4 bitr4i ) ABCZADZECZMFAEBGOMENH
    IJAEBKL $.

  $( Define and with conditional logic operator and false.  (Contributed by RP,
     20-Apr-2020.) $)
  ifpdfan $p |- ( ( ph /\ ps ) <-> if- ( ph , ps , F. ) ) $=
    ( wa wn wfal wo wif fal intnan biorfri df-ifp bitr4i ) ABCZMADZECZFABEGOMEN
    HIJABEKL $.

  $( Equivalence theorem for conditional logical operators.  (Contributed by
     RP, 14-Apr-2020.) $)
  ifpbi2 $p |- ( ( ph <-> ps )
                   -> ( if- ( ch , ph , th ) <-> if- ( ch , ps , th ) ) ) $=
    ( wb wi wn wa wif imbi2 anbi1d dfifp2 3bitr4g ) ABEZCAFZCGDFZHCBFZPHCADICBD
    INOQPABCJKCADLCBDLM $.

  $( Equivalence theorem for conditional logical operators.  (Contributed by
     RP, 14-Apr-2020.) $)
  ifpbi3 $p |- ( ( ph <-> ps )
                   -> ( if- ( ch , th , ph ) <-> if- ( ch , th , ps ) ) ) $=
    ( wb wi wn wa wif imbi2 anbi2d dfifp2 3bitr4g ) ABEZCDFZCGZAFZHOPBFZHCDAICD
    BINQROABPJKCDALCDBLM $.

  $( Restate implication as conditional logic operator.  (Contributed by RP,
     20-Apr-2020.) $)
  ifpim1 $p |- ( ( ph -> ps ) <-> if- ( -. ph , T. , ps ) ) $=
    ( wn wo wtru wa wi wif tru olci biantrur imor dfifp4 3bitr4i ) ACZBDZOCZEDZ
    PFABGOEBHRPEQIJKABLOEBMN $.

  $( Restate negated wff as conditional logic operator.  (Contributed by RP,
     20-Apr-2020.) $)
  ifpnot $p |- ( -. ph <-> if- ( ph , F. , T. ) ) $=
    ( wn wfal wo wtru wa wif tru olci biantru fal biorfri dfifp4 3bitr4i ) ABZC
    DZPAEDZFOACEGQPEAHIJCOKLACEMN $.

  $( Restate wff as conditional logic operator.  (Contributed by RP,
     20-Apr-2020.) $)
  ifpid2 $p |- ( ph <-> if- ( ph , T. , F. ) ) $=
    ( wfal wo wn wtru wa wif tru olci biantrur fal biorfri dfifp4 3bitr4i ) ABC
    ZADZECZOFAAEBGQOEPHIJBAKLAEBMN $.

  $( Restate implication as conditional logic operator.  (Contributed by RP,
     20-Apr-2020.) $)
  ifpim2 $p |- ( ( ph -> ps ) <-> if- ( ps , T. , -. ph ) ) $=
    ( wn wo wtru wa wi wif tru olci biantrur imor orcom bitri dfifp4 3bitr4i )
    BACZDZBCZEDZRFABGZBEQHTRESIJKUAQBDRABLQBMNBEQOP $.

  $( Equivalence theorem for conditional logical operators.  (Contributed by
     RP, 15-Apr-2020.) $)
  ifpbi23 $p |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) )
                    -> ( if- ( ta , ph , ch ) <-> if- ( ta , ps , th ) ) ) $=
    ( wb wa simpl simpr ifpbi23d ) ABFZCDFZGEACBDKLHKLIJ $.

  $( Restatement of ~ biid .  (Contributed by RP, 25-Apr-2020.) $)
  ifpbiidcor $p |- if- ( ph , ph , -. ph ) $=
    ( wb wn wif biid ifpdfbi mpbi ) AABAAACDAEAAFG $.

  $( Corollary of commutation of biconditional.  (Contributed by RP,
     25-Apr-2020.) $)
  ifpbicor $p |- ( if- ( ph , ps , -. ps ) <-> if- ( ps , ph , -. ph ) ) $=
    ( wb wn wif bicom ifpdfbi 3bitr3i ) ABCBACABBDEBAADEABFABGBAGH $.

  $( Corollary of commutation of biconditional.  (Contributed by RP,
     25-Apr-2020.) $)
  ifpxorcor $p |- ( if- ( ph , -. ps , ps ) <-> if- ( ps , -. ph , ph ) ) $=
    ( wn wif ifpbicor wb notnotb ifpbi3 ax-mp ifpn 3bitr4i ) ABCZLCZDZLAACZDALB
    DZBOADALEBMFPNFBGBMALHIBOAJK $.

  $( Equivalence theorem for conditional logical operators.  (Contributed by
     RP, 14-Apr-2020.) $)
  ifpbi1 $p |- ( ( ph <-> ps )
                   -> ( if- ( ph , ch , th ) <-> if- ( ps , ch , th ) ) ) $=
    ( wb wi wn wa wif imbi1 notbi biimpi imbi1d anbi12d dfifp2 3bitr4g ) ABEZAC
    FZAGZDFZHBCFZBGZDFZHACDIBCDIQRUATUCABCJQSUBDQSUBEABKLMNACDOBCDOP $.

  $( Negation of conditional logical operator.  (Contributed by RP,
     18-Apr-2020.) $)
  ifpnot23 $p |- ( -. if- ( ph , ps , ch )
                     <-> if- ( ph , -. ps , -. ch ) ) $=
    ( wa wn wo wif ianor pm4.55 anbi12i ioran dfifp4 3bitr4i df-ifp xchnxbir )
    ABDZAEZCDZFZABEZCEZGZABCGPEZREZDQTFZAUAFZDSEUBUCUEUDUFABHACIJPRKATUALMABCNO
    $.

  $( Factor conditional logic operator over negation in terms 2 and 3.
     (Contributed by RP, 21-Apr-2020.) $)
  ifpnotnotb $p |- ( if- ( ph , -. ps , -. ch )
                       <-> -. if- ( ph , ps , ch ) ) $=
    ( wif wn ifpnot23 bicomi ) ABCDEABECEDABCFG $.

  $( Corollary of commutation of nor.  (Contributed by RP, 25-Apr-2020.) $)
  ifpnorcor $p |- ( if- ( ph , -. ph , -. ps )
                      <-> if- ( ps , -. ps , -. ph ) ) $=
    ( wif wn ifporcor notbii ifpnot23 3bitr3i ) AABCZDBBACZDAADZBDZCBLKCIJABEFA
    ABGBBAGH $.

  $( Corollary of commutation of and.  (Contributed by RP, 25-Apr-2020.) $)
  ifpnancor $p |- ( if- ( ph , -. ps , -. ph )
                      <-> if- ( ps , -. ph , -. ps ) ) $=
    ( wif wn ifpancor notbii ifpnot23 3bitr3i ) ABACZDBABCZDABDZADZCBLKCIJABEFA
    BAGBABGH $.

  $( Negation of conditional logical operator.  (Contributed by RP,
     25-Apr-2020.) $)
  ifpnot23b $p |- ( -. if- ( ph , -. ps , ch )
                     <-> if- ( ph , ps , -. ch ) ) $=
    ( wn wif ifpnot23 wb notnotb ifpbi2 ax-mp bitr4i ) ABDZCEDALDZCDZEZABNEZALC
    FBMGPOGBHBMANIJK $.

  $( Restatement of ~ biid .  (Contributed by RP, 25-Apr-2020.) $)
  ifpbiidcor2 $p |- -. if- ( ph , -. ph , ph ) $=
    ( wn wif ifpbiidcor ifpnot23b mpbir ) AABZACBAAGCADAAAEF $.

  $( Negation of conditional logical operator.  (Contributed by RP,
     25-Apr-2020.) $)
  ifpnot23c $p |- ( -. if- ( ph , ps , -. ch )
                     <-> if- ( ph , -. ps , ch ) ) $=
    ( wn wif ifpnot23 wb notnotb ifpbi3 ax-mp bitr4i ) ABCDZEDABDZLDZEZAMCEZABL
    FCNGPOGCHCNAMIJK $.

  $( Negation of conditional logical operator.  (Contributed by RP,
     25-Apr-2020.) $)
  ifpnot23d $p |- ( -. if- ( ph , -. ps , -. ch )
                     <-> if- ( ph , ps , ch ) ) $=
    ( wn wif ifpnot23 wb notnotb ifpbi23 mp2an bitr4i ) ABDZCDZEDALDZMDZEZABCEZ
    ALMFBNGCOGQPGBHCHBNCOAIJK $.

  $( Define nand as conditional logic operator.  (Contributed by RP,
     20-Apr-2020.) $)
  ifpdfnan $p |- ( ( ph -/\ ps ) <-> if- ( ph , -. ps , T. ) ) $=
    ( wnan wa wn wfal wif df-nan ifpdfan notbii ifpnot23 wb notfal ifpbi3 ax-mp
    wtru bitri 3bitri ) ABCABDZEABFGZEZABEZPGZABHSTABIJUAAUBFEZGZUCABFKUDPLUEUC
    LMUDPAUBNOQR $.

  $( Define xor as conditional logic operator.  (Contributed by RP,
     20-Apr-2020.) $)
  ifpdfxor $p |- ( ( ph \/_ ps ) <-> if- ( ph , -. ps , ps ) ) $=
    ( wxo wo wa wn wtru wif wfal xor2 ifpdfor ifpnot23 ifpdfan xchnxbir anbi12i
    ifpan23 wb truan fal biantru bicomi ifpbi23 mp2an bitri 3bitri ) ABCABDZABE
    ZFZEAGBHZABFZIFZHZEZAUJBHZABJUFUIUHULABKABIHULUGABILABMNOUMAGUJEZBUKEZHZUNA
    GBUJUKPUOUJQUPBQUQUNQUJRBUPUKBSTUAUOUJUPBAUBUCUDUE $.

  $( Equivalence theorem for conditional logical operators.  (Contributed by
     RP, 15-Apr-2020.) $)
  ifpbi12 $p |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) )
                    -> ( if- ( ph , ch , ta ) <-> if- ( ps , th , ta ) ) ) $=
    ( wb wa wi wn wif imbi12 imp simpl notbid imbi1d anbi12d dfifp2 3bitr4g ) A
    BFZCDFZGZACHZAIZEHZGBDHZBIZEHZGACEJBDEJUAUBUEUDUGSTUBUEFABCDKLUAUCUFEUAABST
    MNOPACEQBDEQR $.

  $( Equivalence theorem for conditional logical operators.  (Contributed by
     RP, 15-Apr-2020.) $)
  ifpbi13 $p |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) )
                    -> ( if- ( ph , ta , ch ) <-> if- ( ps , ta , th ) ) ) $=
    ( wb wa wi wif simpl imbi1d notbi imbi12 sylbi imp anbi12d dfifp2 3bitr4g
    wn ) ABFZCDFZGZAEHZASZCHZGBEHZBSZDHZGAECIBEDIUBUCUFUEUHUBABETUAJKTUAUEUHFZT
    UDUGFUAUIHABLUDUGCDMNOPAECQBEDQR $.

  $( Equivalence theorem for conditional logical operators.  (Contributed by
     RP, 15-Apr-2020.) $)
  ifpbi123 $p |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) /\ ( ta <-> et ) )
                     -> ( if- ( ph , ch , ta ) <-> if- ( ps , th , et ) ) ) $=
    ( wb w3a simp1 simp2 simp3 ifpbi123d ) ABGZCDGZEFGZHACEBDFMNOIMNOJMNOKL $.

  $( Restate wff as conditional logic operator.  (Contributed by RP,
     20-Apr-2020.) $)
  ifpidg $p |- ( ( th <-> if- ( ph , ps , ch ) )
                   <-> ( ( ( ( ph /\ ps ) -> th )
                           /\ ( ( ph /\ th ) -> ps ) )
                         /\ ( ( ch -> ( ph \/ th ) )
                              /\ ( th -> ( ph \/ ch ) ) ) ) ) $=
    ( wb wn wo wa wi dfifp4 bibi2i dfbi2 imor ordi ancomst bitri bicomi anbi12i
    wif 3bitri impexp imbi2i 3bitrri df-or cases2 imbi1i pm5.6 anbi2i ancom an4
    jaob ) DABCSZEDAFZBGZACGZHZEZADHBIZDUOIZHZABHZDIZCADGIZHZHZVBURHVCUSHHZULUP
    DABCJKUQDUPIZUPDIZHVEDUPLVGUTVHVDVGDFZUPGVIUNGZVIUOGZHUTDUPMVIUNUONVJURVKUS
    URDAHBIDABIZIZVJADBODABUAVMDUNIVJVLUNDABMZUBDUNMPUCUSVKDUOMQRTVHVAUMCHZGZDI
    VBVODIZHVDUPVPDUPVLUMCIZHZVPUNVLUOVRVLUNVNQACUDRVPVSABCUEQPUFVADVOUKVQVCVBV
    QCUMHDIVCUMCDOCADUGPUHTRPVEVDUTHVFUTVDUIVBVCURUSUJPT $.

  $( Restate wff as conditional logic operator.  (Contributed by RP,
     20-Apr-2020.) $)
  ifpid3g $p |- ( ( ch <-> if- ( ph , ps , ch ) )
                    <-> ( ( ( ph /\ ps ) -> ch )
                          /\ ( ( ph /\ ch ) -> ps ) ) ) $=
    ( wif wb wa wi wo olc pm3.2i ifpidg mpbiran2 ) CABCDEABFCGACFBGFCACHGZMFMMC
    AIZNJABCCKL $.

  $( Restate wff as conditional logic operator.  (Contributed by RP,
     20-Apr-2020.) $)
  ifpid2g $p |- ( ( ps <-> if- ( ph , ps , ch ) )
                    <-> ( ( ps -> ( ph \/ ch ) )
                          /\ ( ch -> ( ph \/ ps ) ) ) ) $=
    ( wif wb wa wi wo ifpidg simpr pm3.2i biantrur ancom 3bitr2i ) BABCDEABFBGZ
    OFZCABHGZBACHGZFZFSRQFABCBIPSOOABJZTKLQRMN $.

  $( Restate wff as conditional logic operator.  (Contributed by RP,
     20-Apr-2020.) $)
  ifpid1g $p |- ( ( ph <-> if- ( ph , ps , ch ) )
                    <-> ( ( ch -> ph ) /\ ( ph -> ps ) ) ) $=
    ( wif wb wa wi wo ifpidg ancom pm4.25 imbi2i orc bitr2i pm4.24 imbi1i simpl
    biantru biantrur anbi12i 3bitri ) AABCDEABFAGZAAFZBGZFZCAAHZGZAACHGZFZFUIUE
    FCAGZABGZFABCAIUEUIJUIUJUEUKUJUGUIAUFCAKLUHUGACMRNUKUDUEAUCBAOPUBUDABQSNTUA
    $.

  $( Restate implication as conditional logic operator.  (Contributed by RP,
     25-Apr-2020.) $)
  ifpim23g $p |- ( ( ( ph -> ps ) <-> if- ( ch , ps , -. ph ) )
                     <-> ( ( ( ph /\ ps ) -> ch )
                           /\ ( ch -> ( ph \/ ps ) ) ) ) $=
    ( wi wn wif wb wa wo ifpidg imbi2i impexp ax-1 adantl biantrur 3bitr2i imdi
    dfor2 imor bitri orcom pm2.21 olcd anbi12i ancom ) ABDZCBAEZFGCBHUFDZCUFHBD
    ZHZUGCUFIDZUFCUGIZDZHZHCABIZDZABHCDZHUQUPHCBUGUFJUPUJUQUNUPCUFBDZDUIUJUOURC
    ABRKCUFBLUHUIBUFCBAMNOPUQUMUNUQABCDDZUMABCLUSUFACDZDUMABCQUTULUFUTUGCIULACS
    UGCUATKTTUKUMUGUFCABUBUCOTUDUPUQUEP $.

  $( Restate implication as conditional logic operator.  (Contributed by RP,
     25-Apr-2020.) $)
  ifpim3 $p |- ( ( ph -> ps ) <-> if- ( ph , ps , -. ph ) ) $=
    ( wi wn wif wb wa wo simpl orc ifpim23g mpbir2an ) ABCABADEFABGACAABHCABIAB
    JABAKL $.

  $( Restate negated implication as conditional logic operator.  (Contributed
     by RP, 25-Apr-2020.) $)
  ifpnim1 $p |- ( -. ( ph -> ps ) <-> if- ( ph , -. ps , ph ) ) $=
    ( wn wif wi ifpnot23c ifpim3 xchnxbir ) ABACDABCADABEABAFABGH $.

  $( Restate implication as conditional logic operator.  (Contributed by RP,
     25-Apr-2020.) $)
  ifpim4 $p |- ( ( ph -> ps ) <-> if- ( ps , ps , -. ph ) ) $=
    ( wi wn wif wb wa wo simpr olc ifpim23g mpbir2an ) ABCBBADEFABGBCBABHCABIBA
    JABBKL $.

  $( Restate negated implication as conditional logic operator.  (Contributed
     by RP, 25-Apr-2020.) $)
  ifpnim2 $p |- ( -. ( ph -> ps ) <-> if- ( ps , -. ps , ph ) ) $=
    ( wn wif wi ifpnot23c ifpim4 xchnxbir ) BBACDBBCADABEBBAFABGH $.

  $( Implication of conditional logical operators.  The right hand side is
     basically conjunctive normal form which is useful in proofs.  (Contributed
     by RP, 16-Apr-2020.) $)
  ifpim123g $p |- ( ( if- ( ph , ch , ta ) -> if- ( ps , th , et ) )
                      <-> ( ( ( ( ph -> -. ps ) \/ ( ch -> th ) )
                              /\ ( ( ps -> ph ) \/ ( ta -> th ) ) )
                            /\ ( ( ( ph -> ps ) \/ ( ch -> et ) )
                                /\ ( ( -. ps -> ph ) \/ ( ta -> et ) ) ) ) ) $=
    ( wi wn wo wa orass bicomi anbi12i bitri 3bitri orbi1i orcom bitr3i orbi2i
    imor wif dfifp4 imbi12i ordi ianor pm4.52 ioran orbi12i cases2 pm4.66 ordir
    bitr4i df-or ) ACEUAZBDFUAZGAHZCIZAEIZJZBHZDIZBFIZJZGUSHZVCIZAUTGZCDGZIZBAG
    ZEDGZIZJZABGZCFGZIZUTAGZEFGZIZJZJZUNUSUOVCACEUBBDFUBUCUSVCTVEVDVAIZVDVBIZJV
    TVDVAVBUDWAVLWBVSWAVDUTIZDIZVLVDUTDKWDVFCHZIZVIEHZIZJZDIWFDIZWHDIZJVLWCWIDW
    CUPWEIZAWGIZJZUTIZUTWLIZUTWMIZJZWIVDWNUTVDUQHZURHZIAWEJZUPWGJZIZWNUQURUEWSX
    AWTXBXAWSACUFLAEUGUHXCAWEGZUPWGGZJWNAWEWGUIXDWLXEWMAWETAEUJMNOZPWOUTWNIWRWN
    UTQUTWLWMUDNWPWFWQWHWPUTUPIZWEIWFUTUPWEKXGVFWEXGUPUTIVFUTUPQAUTTULPRWQUTAIZ
    WGIWHUTAWGKXHVIWGVIXHBATLPRMOPWFWHDUKWJVHWKVKWJVFWEDIZIVHVFWEDKXIVGVFVGXICD
    TLSNWKVIWGDIZIVKVIWGDKXJVJVIVJXJEDTLSNMORWBVDBIZFIZVSVDBFKXLVMWEIZVPWGIZJZF
    IXMFIZXNFIZJVSXKXOFXKWNBIZBWLIZBWMIZJZXOVDWNBXFPXRBWNIYAWNBQBWLWMUDNXSXMXTX
    NXSBUPIZWEIXMBUPWEKYBVMWEYBUPBIVMBUPQABTULPRXTBAIZWGIXNBAWGKYCVPWGBAUMPRMOP
    XMXNFUKXPVOXQVRXPVMWEFIZIVOVMWEFKYDVNVMVNYDCFTLSNXQVPWGFIZIVRVPWGFKYEVQVPVQ
    YEEFTLSNMORMNO $.

  $( Implication of conditional logical operators.  (Contributed by RP,
     18-Apr-2020.) $)
  ifpim1g $p |- ( ( if- ( ph , ch , th ) -> if- ( ps , ch , th ) )
                    <-> ( ( ( ps -> ph ) \/ ( th -> ch ) )
                          /\ ( ( ph -> ps ) \/ ( ch -> th ) ) ) ) $=
    ( wif wi wn wo wa ifpim123g id olci biantrur bicomi biantru anbi12i bitri )
    ACDEBCDEFABGZFZCCFZHZBAFDCFHZIZABFCDFHZRAFZDDFZHZIZIUBUDIABCCDDJUCUBUHUDUBU
    CUAUBTSCKLMNUDUHUGUDUFUEDKLONPQ $.

  $( Substitute the first element of conditional logical operator.
     (Contributed by RP, 20-Apr-2020.) $)
  ifp1bi $p |- ( ( if- ( ph , ch , th ) <-> if- ( ps , ch , th ) )
                   <-> ( ( ( ( ph -> ps ) \/ ( ch -> th ) )
                           /\ ( ( ph -> ps ) \/ ( th -> ch ) ) )
                         /\ ( ( ( ps -> ph ) \/ ( ch -> th ) )
                              /\ ( ( ps -> ph ) \/ ( th -> ch ) ) ) ) ) $=
    ( wif wb wi wa wo dfbi2 ifpim1g biancomi anbi12i an42 3bitri ) ACDEZBCDEZFP
    QGZQPGZHABGZCDGZIZBAGZDCGZIZHZTUDIZUCUAIZHZHUBUGHUHUEHHPQJRUFSUIRUBUEABCDKL
    BACDKMUBUEUGUHNO $.

  $( When the first variable is irrelevant, it can be replaced.  (Contributed
     by RP, 25-Apr-2020.) $)
  ifpbi1b $p |- ( if- ( ph , ch , ch ) <-> if- ( ps , ch , ch ) ) $=
    ( wif wi wn wo wa id olci pm3.2i ifpim123g mpbir2an impbii ) ACCDZBCCDZOPEA
    BFZEZCCEZGZBAEZSGZHABEZSGZQAEZSGZHTUBSRCIZJSUAUGJZKUDUFSUCUGJZSUEUGJKABCCCC
    LMPOEBAFZEZSGZUDHUBUJBEZSGZHULUDSUKUGJUIKUBUNUHSUMUGJKBACCCCLMN $.

  $( Factor conditional logic operator over implication in terms 2 and 3.
     (Contributed by RP, 21-Apr-2020.) $)
  ifpimimb $p |- ( if- ( ph , ( ps -> ch ) , ( th -> ta ) )
                     <-> ( if- ( ph , ps , th ) -> if- ( ph , ch , ta ) ) ) $=
    ( wi wn wa wo dfifp2 imor pm4.8 bicomi orbi1i id orci biantru 3bitri pm4.64
    wif pm4.81 biantrur anbi12i ifpim123g ) ABCFZDEFZTAUEFZAGZUFFZHAUHFZUEIZAAF
    ZDCFZIZHZULBEFZIZUHAFZUFIZHZHZABDTACETFZAUEUFJUGUOUIUTUGUHUEIUKUOAUEKUHUJUE
    UJUHALMNUNUKULUMAOZPQRUIAUFIUSUTAUFSAURUFURAAUAMNUQUSULUPVCPUBRUCVBVAAABCDE
    UDMR $.

  $( Factor conditional logic operator over disjunction in terms 2 and 3.
     (Contributed by RP, 21-Apr-2020.) $)
  ifpororb $p |- ( if- ( ph , ( ps \/ ch ) , ( th \/ ta ) )
                     <-> ( if- ( ph , ps , th ) \/ if- ( ph , ch , ta ) ) ) $=
    ( wo wif wi wn wa dfifp2 df-or imbi2i anbi12i ifpimimb imor ifpnot23d bitri
    orbi1i 3bitr3i 3bitri ) ABCFZDEFZGAUBHZAIZUCHZJABIZCHZHZUEDIZEHZHZJZABDGZAC
    EGZFZAUBUCKUDUIUFULUBUHABCLMUCUKUEDELMNAUHUKGAUGUJGZUOHZUMUPAUGCUJEOAUHUKKU
    RUQIZUOFUPUQUOPUSUNUOABDQSRTUA $.

  $( Factor conditional logic operator over conjunction in terms 2 and 3.
     (Contributed by RP, 21-Apr-2020.) $)
  ifpananb $p |- ( if- ( ph , ( ps /\ ch ) , ( th /\ ta ) )
                     <-> ( if- ( ph , ps , th ) /\ if- ( ph , ch , ta ) ) ) $=
    ( wa wif wn wo anor ifpbi23 mp2an ifpororb ifpnotnotb orbi12i bitri 3bitr4i
    wb notbii ) ABCFZDEFZGZABHZCHZIZHZDHZEHZIZHZGZABDGZACEGZFZTUFRUAUJRUBUKRBCJ
    DEJTUFUAUJAKLAUEUIGZHULHZUMHZIZHUKUNUOURUOAUCUGGZAUDUHGZIURAUCUDUGUHMUSUPUT
    UQABDNACENOPSAUEUINULUMJQP $.

  $( Factor conditional logic operator over nand in terms 2 and 3.
     (Contributed by RP, 21-Apr-2020.) $)
  ifpnannanb $p |- ( if- ( ph , ( ps -/\ ch ) , ( th -/\ ta ) )
                       <-> ( if- ( ph , ps , th ) -/\ if- ( ph , ch , ta ) ) )
    $=
    ( wnan wif wa wn wb df-nan ifpbi23 mp2an ifpananb notbii ifpnotnotb 3bitr4i
    bitri ) ABCFZDEFZGZABCHZIZDEHZIZGZABDGZACEGZFZSUCJTUEJUAUFJBCKDEKSUCTUEALMA
    UBUDGZIUGUHHZIUFUIUJUKABCDENOAUBUDPUGUHKQR $.

  $( Disjunction of conditional logical operators.  (Contributed by RP,
     18-Apr-2020.) $)
  ifpor123g $p |- ( ( if- ( ph , ch , ta ) \/ if- ( ps , th , et ) )
                      <-> ( ( ( ( ph -> -. ps ) \/ ( ch \/ th ) )
                              /\ ( ( ps -> ph ) \/ ( ta \/ th ) ) )
                            /\ ( ( ( ph -> ps ) \/ ( ch \/ et ) )
                                 /\ ( ( -. ps -> ph ) \/ ( ta \/ et ) ) ) ) )
    $=
    ( wif wo wn wi df-or ifpnot23 imbi1i bitri ifpim123g pm4.64 orbi2i anbi12i
    wa ) ACEGZBDFGZHZABIZJZCIZDJZHZBAJZEIZDJZHZSZABJZUEFJZHZUCAJZUIFJZHZSZSZUDC
    DHZHZUHEDHZHZSZUMCFHZHZUPEFHZHZSZSUBAUEUIGZUAJZUTUBTIZUAJVLTUAKVMVKUAACELMN
    ABUEDUIFONULVEUSVJUGVBUKVDUFVAUDCDPQUJVCUHEDPQRUOVGURVIUNVFUMCFPQUQVHUPEFPQ
    RRN $.

  $( Consequnce of implication.  (Contributed by RP, 17-Apr-2020.) $)
  ifpimim $p |- ( if- ( ph , ( ps -> ch ) , ( th -> ta ) )
                    -> ( if- ( ph , ps , th ) -> if- ( ph , ch , ta ) ) ) $=
    ( wn wi wo wa wif pm2.521 orim1i adantr id orci a1i jca simpr wb pm4.81
    bicomi ifpbi1 ax-mp dfifp4 bitri ifpim123g 3imtr4i ) AFZAGZFZBCGZHZUIDEGZHZ
    IZAUHGZUKHZAAGZDCGZHZIZURBEGZHZUNIZIAUKUMJZABDJACEJGUOVAVDUOUQUTULUQUNUJUPU
    KUHAKLMUTUOURUSANZOPQUOVCUNVCUOURVBVFOPULUNRQQVEUIUKUMJZUOAUISVEVGSUIAATUAA
    UIUKUMUBUCUIUKUMUDUEAABCDEUFUG $.

  $( Factor conditional logic operator over biconditional in terms 2 and 3.
     (Contributed by RP, 21-Apr-2020.) $)
  ifpbibib $p |- ( if- ( ph , ( ps <-> ch ) , ( th <-> ta ) )
                     <-> ( if- ( ph , ps , th ) <-> if- ( ph , ch , ta ) ) ) $=
    ( wb wi wn wa dfifp2 dfbi2 imbi2i jcab bitri anbi12i ifpimimb bitr3i bitr4i
    wif an4 3bitri ) ABCFZDEFZSAUBGZAHZUCGZIZABCGZGZUEDEGZGZIZACBGZGZUEEDGZGZIZ
    IZABDSZACESZFZAUBUCJUGUIUNIZUKUPIZIURUDVBUFVCUDAUHUMIZGVBUBVDABCKLAUHUMMNUF
    UEUJUOIZGVCUCVEUEDEKLUEUJUOMNOUIUNUKUPTNURUSUTGZUTUSGZIVAULVFUQVGULAUHUJSVF
    AUHUJJABCDEPQUQAUMUOSVGAUMUOJACBEDPQOUSUTKRUA $.

  $( Factor conditional logic operator over xor in terms 2 and 3.  (Contributed
     by RP, 21-Apr-2020.) $)
  ifpxorxorb $p |- ( if- ( ph , ( ps \/_ ch ) , ( th \/_ ta ) )
                     <-> ( if- ( ph , ps , th ) \/_ if- ( ph , ch , ta ) ) ) $=
    ( wxo wif wb df-xor ifpbi23 mp2an ifpbibib notbii ifpnotnotb 3bitr4i bitri
    wn ) ABCFZDEFZGZABCHZQZDEHZQZGZABDGZACEGZFZRUBHSUDHTUEHBCIDEIRUBSUDAJKAUAUC
    GZQUFUGHZQUEUHUIUJABCDELMAUAUCNUFUGIOP $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Sophisms
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( A special case where implication appears to conform to a mixed associative
     law.  (Contributed by RP, 29-Feb-2020.) $)
  rp-fakeimass $p |- ( ( ph \/ ch ) <->
                       ( ( ( ph -> ps ) -> ch )
                         <-> ( ph -> ( ps -> ch ) ) ) ) $=
    ( wo wi wb wn pm2.521g a1d ax-1 ja ax-2 impbid2 2thd jaoi jarl orrd simplim
    com3r orcd a1i bija impbii ) ACDZABEZCEZABCEZEZFZAUICAUFUHUECUHUEGUGAABCHIC
    UGACBJIZKUHUEACABCLSMCUFUHCUEJUJNOUFUHUDUFUDUHUFACABCPQIUHGZUDEUFGUKACAUGRT
    UAUBUC $.

  $( A special case where a mixture of and and or appears to conform to a mixed
     associative law.  (Contributed by RP, 26-Feb-2020.) $)
  rp-fakeanorass $p |- ( ( ch -> ph ) <->
                         ( ( ( ph /\ ps ) \/ ch )
                           <-> ( ph /\ ( ps \/ ch ) ) ) ) $=
    ( wi wo wa wb wn pm1.4 ord pm4.83 biimpi sylan2 anim1d orc anim1i jctir olc
    ex jca simpl imim12i adantr impbii dfbi2 ordir bicomi bibi1i 3bitr2i ) CADZ
    ACEZBCEZFZAULFZDZUNUMDZFZUMUNGABFCEZUNGUJUQUJUOUPUJUKAULUJUKAUKUJCHADZAUKCA
    ACIJUJUSFACAKLMSNAUKULACOPQUOUJUPCUMUNACUKULCARCBRTAULUAUBUCUDUMUNUEUMURUNU
    RUMABCUFUGUHUI $.

  $( A special case where a mixture of or and and appears to conform to a mixed
     associative law.  (Contributed by RP, 29-Feb-2020.) $)
  rp-fakeoranass $p |- ( ( ph -> ch ) <->
                         ( ( ( ph \/ ps ) /\ ch )
                           <-> ( ph \/ ( ps /\ ch ) ) ) ) $=
    ( wi wa wo wb rp-fakeanorass bicom orcom anbi1ci ancom orbi2i bitri bibi12i
    ) ACDCBEZAFZCBAFZEZGZABFZCEZABCEZFZGZCBAHTSQGUEQSISUBQUDRUACBAJKQAPFUDPAJPU
    CACBLMNONN $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( A special case where a mixture of intersection and union appears to
       conform to a mixed associative law.  (Contributed by RP,
       26-Feb-2020.) $)
    rp-fakeinunass $p |- ( C C_ A <->
                           ( ( A i^i B ) u. C ) = ( A i^i ( B u. C ) ) ) $=
      ( vx cv wcel wi wal wa wo wss cin cun wceq rp-fakeanorass albii elun elin
      wb bitri df-ss dfcleq orbi1i anbi2i bibi12i 3bitr4i ) DEZCFZUGAFZGZDHUIUG
      BFZIZUHJZUIUKUHJZIZSZDHZCAKABLZCMZABCMZLZNZUJUPDUIUKUHOPDCAUAVBUGUSFZUGVA
      FZSZDHUQDUSVAUBVEUPDVCUMVDUOVCUGURFZUHJUMUGURCQVFULUHUGABRUCTVDUIUGUTFZIU
      OUGAUTRVGUNUIUGBCQUDTUEPTUF $.
  $}

  $( A special case where a mixture of union and intersection appears to
     conform to a mixed associative law.  (Contributed by RP, 29-Feb-2020.) $)
  rp-fakeuninass $p |- ( A C_ C <->
                         ( ( A u. B ) i^i C ) = ( A u. ( B i^i C ) ) ) $=
    ( wss cin wceq rp-fakeinunass eqcom incom uncom ineq1i eqtri uneq2i eqeq12i
    cun 3bitri ) ACDCBEZAOZCBAOZEZFTRFABOZCEZABCEZOZFCBAGRTHTUBRUDTSCEUBCSISUAC
    BAJKLRAQOUDQAJQUCACBIMLNP $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Finite Sets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Membership in the class of finite sets can be expressed in many ways.

$)

  ${
    $d n A $.
    $( A set is said to be finite if it can be put in one-to-one correspondence
       with all the natural numbers between 1 and some ` n e. NN0 ` .
       (Contributed by RP, 3-Mar-2020.) $)
    rp-isfinite5 $p |- ( A e. Fin <-> E. n e. NN0 ( 1 ... n ) ~~ A ) $=
      ( cfn wcel c1 cv cfz co cen wbr cn0 wrex wa wex chash cfv wceq sylibr cvv
      oveq2 hashcl isfinite4 biimpi breq1d anbi12d spcedv df-rex hasheni eqcomd
      jca eleq1 hashfz1 ovex eqtr eqeng syl5 mpsyl syl2anr entr sylancom impbii
      rexlimiva ) ACDZEBFZGHZAIJZBKLZVCVDKDZVFMZBNVGVCVIAOPZKDZEVJGHZAIJZMBKVJA
      UAZVCVKVMVNVCVMAUBZUCUJVDVJQZVHVKVFVMVDVJKUKVPVEVLAIVDVJEGTUDUEUFVFBKUGRV
      FVCBKVIVMVCVHVFVLVEIJZVMVFVJVEOPZQZVRVDQZVQVHVFVRVJVEAUHUIVDULVLSDZVSVTMV
      JVDQZVQEVJGUMVJVRVDUNWBVLVEQWAVQVJVDEGTVLVESUOUPUQURVLVEAUSUTVORVBVA $.
  $}

  ${
    $d n A $.
    $( A set is said to be finite if it is either empty or it can be put in
       one-to-one correspondence with all the natural numbers between 1 and
       some ` n e. NN ` .  (Contributed by RP, 10-Mar-2020.) $)
    rp-isfinite6 $p |- ( A e. Fin <-> ( A = (/) \/
                                        E. n e. NN ( 1 ... n ) ~~ A ) ) $=
      ( cfn wcel c0 wceq wa wn wo c1 cfz cen wbr cn bitri cn0 wex w3a cc0 syl
      cv co wrex exmid biantrur andir simpl 0fi eleq1a ax-mp ancli rp-isfinite5
      impbii df-rex anbi2i en0 ensymb bitr3i notbii elnn0 anbi1i anbi12i 3anass
      andi orbi12i sylbb2 simp2 oveq2 fz10 eqtrdi simp3 eqbrtrrd simp1 pm2.21dd
      wi syl3an2 jaoi simprr jca csdm chash cfv clt nngt0 hash0 hashfz1 3brtr4d
      a1i nnnn0 wb fzfi hashsdom mp2an sylib anim1i sdomentr sdomnen en0r exbii
      19.42v 3bitr2ri ) ACDZAEFZXBGZXCHZXBGZIZXCJBUAZKUBZALMZBNUCZIXBXCXEIZXBGX
      GXLXBXCUDUEXCXEXBUFOXDXCXFXKXDXCXCXBUGXCXBECDZXCXBVOUHECAUIUJUKUMXFXEXHPD
      ZXJGZBQZGZXKXBXPXEXBXJBPUCXPABULXJBPUNOUOXKXHNDZXJGZBQXEXOGZBQXQXJBNUNXTX
      SBXTXSXTXRXJXTEALMZHZXRXJRZYBXHSFZXJRZIZXRXTYBXSGZYBYDXJGZGZIZYFXTYBXSYHI
      ZGYJXEYBXOYKXCYAXCAELMYAAUPAEUQURUSXOXRYDIZXJGYKXNYLXJXHUTVAXRYDXJUFOVBYB
      XSYHVDOYCYGYEYIYBXRXJVCYBYDXJVCVEVFYCXRYEYBXRXJVGYDYBXIEFZXJXRYDXIJSKUBEX
      HSJKVHVIVJYBYMXJRZYAXRYNXIEALYBYMXJVGYBYMXJVKVLYBYMXJVMVNVPVQTXEXNXJVRVSX
      SXEXOXSEXIVTMZXJGZXEXRYOXJXREWAWBZXIWAWBZWCMZYOXRSXHYQYRWCXHWDYQSFXRWEWHX
      RXNYRXHFXHWIZXHWFTWGXMXICDYSYOWJUHJXHWKEXIWLWMWNWOYPYBXEYPEAVTMYBEXIAWPEA
      WQTYAXCAWRUSWNTXRXNXJYTWOVSUMWSXEXOBWTXAOVEO $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  General Observations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( May move to main section after ~ elintab . $)

  ${
    $d x z ch $.  $d y z ps $.  $d x y z ph $.  $d x A $.
    intabssd.ex $e |- ( ph -> A e. V ) $.
    intabssd.sub $e |- ( ( ph /\ x = A ) -> ( ch -> ps ) ) $.
    intabssd.ss $e |- ( ph -> A C_ y ) $.
    $( When for each element ` y ` there is a subset ` A ` which may
       substituted for ` x ` such that ` y ` satisfying ` ch ` implies ` x `
       satisfies ` ps ` then the intersection of all ` x ` that satisfy ` ps `
       is a subclass the intersection of all ` y ` that satisfy ` ch ` .
       (Contributed by RP, 17-Oct-2020.) $)
    intabssd $p |- ( ph -> |^| { x | ps } C_ |^| { y | ch } ) $=
      ( vz cab cint wel wi wal cv wcel wceq elintab eleq2 sseld sylan9r imim12d
      wa biimpd spcimdv alrimdv vex 3imtr4g ssrdv ) AKBDLMZCELMZABKDNZOZDPZCKEN
      ZOZEPKQZULRUSUMRAUPUREAUOURDFGHADQZFSZUECBUNUQIVAUNUSFRZAUQVAUNVBUTFUSUAU
      FAFEQUSJUBUCUDUGUHBDUSKUIZTCEUSVCTUJUK $.
  $}

  $( May move to main section after ~ ax-nul . $)

  ${
    $d x y $.
    $( There is only one empty set.  (Contributed by RP, 1-Oct-2023.) $)
    eu0 $p |- ( A. x -. x e. (/) /\ E! x A. y -. y e. x ) $=
      ( cv c0 wcel wn wal wel weu noel ax-gen wex wmo ax-nul nulmo df-eu pm3.2i
      mpbir2an ) ACZDEFZAGBAHFBGZAIZTASJKUBUAALUAAMABNABOUAAPRQ $.
  $}

  $( May move to main section after ~ con0 . $)

  $( Over the ordinal numbers, one may define the relation ` A _E B ` iff
     ` A e. B ` and one finds that, under this ordering, ` On ` is a
     well-ordered class, see ~ epweon .  This is a weak form of ~ epelg which
     only requires that we know ` B ` to be a set.  (Contributed by RP,
     27-Sep-2023.) $)
  epelon2 $p |- ( ( A e. On /\ B e. On ) -> ( A _E B <-> A e. B ) ) $=
    ( con0 wcel cep wbr wb epelg adantl ) BCDABEFABDGACDABCHI $.

  $( May move to main section after ~ onsseleq . $)

  ${
    $d x y $.
    $( For all ` x , y e. On ` , one and only one of the following hold:
       ` x e. y ` , ` y = x ` , or ` y e. x ` .  This is a transparent strict
       trichotomy.  (Contributed by RP, 27-Sep-2023.) $)
    ontric3g $p |- A. x e. On A. y e. On (
                    ( x e. y <-> -. ( y = x \/ y e. x ) )
                 /\ ( y = x <-> -. ( x e. y \/ y e. x ) )
                 /\ ( y e. x <-> -. ( x e. y \/ y = x ) ) ) $=
      ( wel weq wo wn wb w3a con0 cv wcel wss orcom a1i onsseleq ontri1 3bitr2d
      wa con2bid ancoms anbi12d eqss ioran 3bitr4g equcom orbi2i 3jca rgen2 ) A
      BCZBADZBACZEZFGZUJUIUKEFZGZUKUIUJEZFGZHABIIAJZIKZBJZIKZRZUMUOUQVAUSUMVAUS
      RZULUIVCULUKUJEZUTURLZUIFZULVDGVCUJUKMNUTUROUTURPZQSTVBVEURUTLZRVFUKFZRUJ
      UNVBVEVFVHVIVAUSVEVFGVGTURUTPZUAUTURUBUIUKUCUDVBUPUKVBUPUIABDZEZVHVIUPVLG
      VBUJVKUIBAUEUFNURUTOVJQSUGUH $.
  $}

  $( May move to main section after ~ dflim3 . $)

  ${
    $d A x $.
    $( ` A ` is called a successor ordinal if it is not a limit ordinal and not
       the empty set.  (Contributed by RP, 11-Nov-2023.) $)
    dfsucon $p |- ( ( Ord A /\ -. Lim A /\ A =/= (/) ) <->
                       E. x e. On A = suc x ) $=
      ( word wlim wn c0 wne w3a cv csuc wceq con0 wa wi 3ancomb df-3an wo df-ne
      wrex anbi2i imbi1i pm5.6 iman 3bitrri dflim3 xchnxbir 3bitri pm3.35 sylbi
      wcel eloni ordsuc sylib nlimsuc nsuceq0 a1i 3jca ordeq limeq notbid neeq1
      3anbi123d syl5ibrcom rexlimiv impbii ) BCZBDZEZBFGZHZBAIZJZKZALSZVJVFVIMZ
      VOVNNZMZVNVJVFVIVHHVOVHMVQVFVHVIOVFVIVHPVHVPVOVFBFKZVNQZEMZVPVGVPVFVREZMZ
      VNNVFVSNVTEVOWBVNVIWAVFBFRTUAVFVRVNUBVFVSUCUDABUEUFTUGVOVNUHUIVMVJALVKLUJ
      ZVJVMVLCZVLDZEZVLFGZHWCWDWFWGWCVKCWDVKUKVKULUMVKUNWGWCVKUOUPUQVMVFWDVHWFV
      IWGBVLURVMVGWEBVLUSUTBVLFVAVBVCVDVE $.
  $}

  $( May move to main section after ~ en1 . $)

  ${
    $d A x $.
    $( A singleton is equinumerous to ordinal one iff its content is a set.
       (Contributed by RP, 8-Oct-2023.) $)
    snen1g $p |- ( { A } ~~ 1o <-> A e. _V ) $=
      ( vx csn wceq wex c1o cen wbr cvv wcel eqcom vex sneqr impbii bitri exbii
      cv sneq en1 isset 3bitr4i ) ACZBQZCZDZBEUCADZBEUBFGHAIJUEUFBUEUDUBDZUFUBU
      DKUGUFUCABLMUCARNOPBUBSBATUA $.
  $}

  $( A singleton is equinumerous to ordinal one if its content is an element of
     it.  (Contributed by RP, 8-Oct-2023.) $)
  snen1el $p |- ( { A } ~~ 1o <-> A e. { A } ) $=
    ( csn c1o cen wbr cvv wcel snen1g snidb bitri ) ABZCDEAFGAKGAHAIJ $.

  $( May move to main section after ~ 0domg . $)

  $( A singleton is dominated by ordinal one.  (Contributed by RP,
     29-Oct-2023.) $)
  sn1dom $p |- { A } ~<_ 1o $=
    ( cvv wcel csn c1o cdom wbr cen ensn1g 1on domrefg ax-mp endomtr sylancl wn
    con0 c0 wceq snprc wi snex eqeng sylbi 0domg pm2.61i ) ABCZADZEFGZUFUGEHGEE
    FGZUHABIEPCZUIJEPKLUGEEMNUFOZUGQHGZQEFGZUHUKUGQRZULASUGBCUNULTAUAUGQBUBLUCU
    JUMJEPUDLUGQEMNUE $.

  $( An unordered pair is dominated by ordinal two.  (Contributed by RP,
     29-Oct-2023.) $)
  pr2dom $p |- { A , B } ~<_ 2o $=
    ( cpr csn cun c2o cdom df-pr cdju wbr cvv wcel snex undjudom c1o cen sn1dom
    mp2an con0 domtr djudom1 1on djudom2 dju1p1e2 domentr eqbrtri ) ABCADZBDZEZ
    FGABHUIUGUHIZGJZUJFGJZUIFGJUGKLUHKLZUKAMBMZUGUHKKNRUJOOIZGJZUOFPJULUJOUHIZG
    JZUQUOGJZUPUGOGJUMURAQUNUGOUHKUARUHOGJOSLUSBQUBUHOOSUCRUJUQUOTRUDUJUOFUERUI
    UJFTRUF $.

  $( An unordered triple is dominated by ordinal three.  (Contributed by RP,
     29-Oct-2023.) $)
  tr3dom $p |- { A , B , C } ~<_ 3o $=
    ( ctp cpr csn cun c3o cdom cdju wbr cvv wcel mp2an c2o c1o cen con0 domtr
    2on df-tp prex snex undjudom pr2dom djudom1 sn1dom djudom2 co onadju ensymi
    coa 1on csuc wceq oa1suc ax-mp df-3o eqtr4i breqtri domentr eqbrtri ) ABCDA
    BEZCFZGZHIABCUAVEVCVDJZIKZVFHIKZVEHIKVCLMVDLMZVGABUBCUCZVCVDLLUDNVFOPJZIKZV
    KHQKVHVFOVDJZIKZVMVKIKZVLVCOIKVIVNABUEVJVCOVDLUFNVDPIKORMZVOCUGTVDPORUHNVFV
    MVKSNVKOPULUIZHQVQVKVPPRMVQVKQKTUMOPUJNUKVQOUNZHVPVQVRUOTOUPUQURUSUTVFVKHVA
    NVEVFHSNVB $.

  $( May move to main section after ~ ensdomtr . $)

  $( A class equinumerous to a successor is never empty.  (Contributed by RP,
     11-Nov-2023.)  (Proof shortened by SN, 16-Nov-2023.) $)
  ensucne0 $p |- ( A ~~ suc B -> A =/= (/) ) $=
    ( csuc cen wbr c0 wceq nsuceq0 en0r nemtbir breq1 mtbiri necon2ai ) ABCZDEZ
    AFAFGOFNDEZPNFBHNIJAFNDKLM $.

  $( A class equinumerous to a successor is never empty.  (Contributed by RP,
     11-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ensucne0OLD $p |- ( A ~~ suc B -> A =/= (/) ) $=
    ( csuc cvv wcel cen wbr c0 wne encv simprd wceq csdm wa en0 biimpri nsuceq0
    wn wi a1i 0sdomg mpbiri jctird ensdomtr sdomnen syl syl6 necon2ad mpcom ) B
    CZDEZAUJFGZAHIULADEUKAUJJKUKULAHUKAHLZAHFGZHUJMGZNZULRZUKUMUNUOUMUNSUKUNUMA
    OPTUKUOUJHIBQUJDUAUBUCUPAUJMGUQAHUJUDAUJUEUFUGUHUI $.

  $( May move to main section after ~ onfin2 . $)

  $( Let ` _om ` be defined to be the union of the set of all finite ordinals.
     (Contributed by RP, 27-Sep-2023.) $)
  dfom6 $p |- _om = U. ( On i^i Fin ) $=
    ( com cuni con0 cfn cin wlim wceq limom limuni ax-mp onfin2 unieqi eqtri )
    AABZCDEZBAFANGHAIJAOKLM $.

  $( May move to main section after ~ omelon . $)

  $( ` _om ` is the smallest infinite ordinal.  (Contributed by RP,
     27-Sep-2023.) $)
  infordmin $p |- A. x e. ( On \ Fin ) _om C_ x $=
    ( com cv wss con0 cfn cdif wcel wn wa eldif wi omelon ontri1 bicomd con1bid
    nnfi biimtrdi mpan con1d imp sylbi rgen ) BACZDZAEFGZUDUFHUDEHZUDFHZIZJUEUD
    EFKUGUIUEUGUEUHBEHZUGUEIZUHLMUJUGJZUKUDBHZUHULUMUEULUEUMIBUDNOPUDQRSTUAUBUC
    $.

  $( May move to main section after ~ oncard . $)

  ${
    $d A x y $.
    $( Two ways to express the property of being a cardinal number.
       (Contributed by RP, 8-Nov-2023.) $)
    iscard4 $p |- ( ( card ` A ) = A <-> A e. ran card ) $=
      ( vx vy ccrd cfv wceq crn wcel eqcom cv wbr wex wrel wb cvv con0 ax-mp id
      eqeltrdi syl cen crab cint cmpt mptrel df-card releqi mpbir relelrnb wfun
      wi funmpt2 funbrfv eqcomd eximi cardidm fveq2 3eqtr4a exlimiv wsbc biimpi
      cdm cardon onenon funfvbrb biimpd mpsyl breqtrd eqcoms csb sbcbr1g breq1d
      csbvarg bitrd mpbird spesbcd impbii oncard 3bitrri bitri ) ADEZAFZAWAFZAD
      GHZWAAIZWDBJZADKZBLZAWFDEZFZBLZWCDMZWDWHNWLBOCJWFUAKCPUBUCZUDZMBOWMUEDWNB
      CUFZUGUHBADUIQWHWKWGWJBWGWIADUJZWGWIAFUKBOWMDWOULZWFADUMQUNUOWKWBWHWJWBBW
      JWIDEWIWAAWFUPAWIDUQWJRURUSWBWGBAWBWGBAUTZAADKZWBAWAADWPWBADVBHZAWADKZWQW
      BAPHZWTWBAWAPWBWCWEVAAVCZSAVDTWPWTXAADVEVFVGWBRVHWBXBWRWSNXBAWAWCAWAPWCRX
      CSVIXBWRBAWFVJZADKWSBAWFADPVKXBXDAADBAPVMVLVNTVOVPTVQBAVRVSVT $.
  $}

  ${
    $d A x y $.
    $( Given any cardinal number ` A ` , there exists an argument ` x ` , which
       yields the least regular uncountable value of ` aleph ` which is greater
       to or equal to ` A ` .  This proof uses AC. (Contributed by RP,
       23-Nov-2023.) $)
    minregex $p |- ( A e. ( ran card \ _om ) -> E. x e. On x = |^| { y e. On |
                   ( (/) e. y /\ A C_ ( aleph ` y ) /\
                     ( cf ` ( aleph ` y ) ) = ( aleph ` y ) ) } ) $=
      ( com wcel con0 c0 cale cfv wss ccf wceq w3a wa wrex wsbc wb a1i syl csb
      ccrd crn cdif cv crab cint csuc wn eldif omelon cardon eleq1 mpbii ontri1
      wex sylancr pm5.32i iscard4 anbi1i bitr2i ancom 3bitri biimpi cardalephex
      biimpa wi eqimss reximdv onintrab2 sylib simpr onsuc word eloni cardaleph
      mpd 0elsuc adantr sssucid alephord3 syl2anc2 eqsstrd alephreg jca sbcel1v
      3jca sbcan sbc3an sbcel2gv sbcssg csbconstg csbfv2g csbvarg eqtrd sseq12d
      fveq2d bitrd sbceqg eqeq12d 3anbi123d bitrid anbi12d mpbird df-rex risset
      spesbcd 3bitr3i ) CUAUBZDUCEZBUDZFEZGXJEZCXJHIZJZXMKIZXMLZMZNZBUOZAUDZXQB
      FUEUFZLAFOZXIXRBCXTHIZJZAFUEUFZUGZXIXRBYFPZYFFEZGYFEZCYFHIZJZYJKIZYJLZMZN
      ZXIDCJZCUAIZCLZNZYEFEZYOXIYSXICXHEZCDEUHZNZYRYPNZYSCXHDUIUUDYRUUBNUUCYRYP
      UUBYRDFECFEZYPUUBQUJYRYQFEUUECUKYQCFULUMDCUNUPUQYRUUAUUBCURUSUTYRYPVAVBVC
      ZYSYDAFOZYTYSCYCLZAFOZUUGYPYRUUIACVDVEZYSUUHYDAFUUHYDVFZYSCYCVGZRVHVPYDAV
      IZVJYSYTNZYHYNUUNYTYHYSYTVKZYEVLZSUUNYIYKYMUUNYEVMZYIUUNYTUUQUUOYEVNSYEVQ
      SUUNCYEHIZYJYSCUURLYTACVOVRUUNYEYFJZUURYJJZYEVSUUNYTYHUUSUUTQUUOUUPYEYFVT
      WAUMWBYMUUNYEWCRWFWDWAXIYHYGYOQXIYTYHXIUUGYTXIUUIUUGXIYSUUIUUFUUJSXIUUHYD
      AFUUKXIUULRVHVPUUMVJUUPSYGXKBYFPZXQBYFPZNYHYOXKXQBYFWGYHUVAYHUVBYNUVAYHQY
      HBYFFWERUVBXLBYFPZXNBYFPZXPBYFPZMYHYNXLXNXPBYFWHYHUVCYIUVDYKUVEYMBGYFFWIY
      HUVDBYFCTZBYFXMTZJYKBYFCXMFWJYHUVFCUVGYJBYFCFWKYHUVGBYFXJTZHIYJBYFXJFHWLY
      HUVHYFHBYFFWMWPWNZWOWQYHUVEBYFXOTZUVGLYMBYFXOXMFWRYHUVJYLUVGYJYHUVJUVGKIY
      LBYFXMFKWLYHUVGYJKUVIWPWNUVIWSWQWTXAXBXASXCXFXQBFOYAFEXSYBXQBVIXQBFXDAYAF
      XEXGVJ $.

    $( Given any cardinal number ` A ` , there exists an argument ` x ` , which
       yields the least regular uncountable value of ` aleph ` which dominates
       ` A ` .  This proof uses AC. (Contributed by RP, 24-Nov-2023.) $)
    minregex2 $p |- ( A e. ( ran card \ _om ) -> E. x e. On x = |^| { y e. On |
                   ( (/) e. y /\ A ~<_ ( aleph ` y ) /\
                     ( cf ` ( aleph ` y ) ) = ( aleph ` y ) ) } ) $=
      ( ccrd crn com cdif wcel cv cale cfv wss ccf wceq w3a con0 crab cint wrex
      c0 wbr minregex wa eldifi iscard4 sylibr adantr alephcard a1i sseq12d cdm
      cdom wb numth3 alephon onenon mp1i carddom2 syl2an bitr3d rabbidva inteqd
      3anbi2d eqeq2d rexbidv mpbid ) CDEZFGZHZAIZTBIZHZCVKJKZLZVMMKVMNZOZBPQZRZ
      NZAPSVJVLCVMULUAZVOOZBPQZRZNZAPSABCUBVIVSWDAPVIVRWCVJVIVQWBVIVPWABPVIVKPH
      ZUCZVNVTVLVOWFCDKZVMDKZLZVNVTWFWGCWHVMVIWGCNZWEVICVGHWJCVGFUDCUEUFUGWHVMN
      WFVKUHUIUJVICDUKZHVMWKHZWIVTUMWECVHUNVMPHWLWEVKUOVMUPUQCVMURUSUTVCVAVBVDV
      EVF $.
  $}

  $( May move to main section after ~ iscard . $)

  ${
    $d A x $.
    $( Two ways to express the property of being a cardinal number.
       (Contributed by RP, 8-Nov-2023.) $)
    iscard5 $p |- ( ( card ` A ) = A
                    <-> ( A e. On /\ A. x e. A -. x ~~ A ) ) $=
      ( ccrd cfv wceq con0 wcel cv csdm wbr wral wa cen iscard sdomnen cdom wss
      wn onelss ssdomg imp wi brsdom biimpri a1i mpand impbid2 ralbidva pm5.32i
      syld bitri ) BCDBEBFGZAHZBIJZABKZLULUMBMJRZABKZLABNULUOUQULUNUPABULUMBGZL
      ZUNUPUMBOUSUMBPJZUPUNULURUTULURUMBQUTBUMSUMBFTUJUAUTUPLZUNUBUSUNVAUMBUCUD
      UEUFUGUHUIUK $.
  $}

  ${
    $d A x $.
    $( Let us define a cardinal number to be an element ` A e. On ` such that
       ` A ` is not equipotent with any ` x e. A ` .  (Contributed by RP,
       1-Oct-2023.) $)
    elrncard $p |- ( A e. ran card <-> ( A e. On /\ A. x e. A -. x ~~ A ) ) $=
      ( ccrd crn wcel cfv wceq con0 cv cen wbr wn wral iscard4 iscard5 bitr3i
      wa ) BCDEBCFBGBHEAIBJKLABMQBNABOP $.
  $}

  ${
    $d A x y $.
    $( ` ( har `` A ) ` is the least cardinal that is greater than ` A ` .
       (Contributed by RP, 4-Nov-2023.) $)
    harval3 $p |- ( A e. dom card -> ( har ` A )
                    = |^| { x e. ran card | A ~< x } ) $=
      ( vy ccrd wcel cfv cv csdm wbr con0 crab cint cab cvv vex a1i adantl wceq
      wa wi cdm char crn harval2 weq cen wn elrncard simplbi anim1i eleq1 breq2
      wral anbi12d imbitrrid ssidd intabssd cin oncardid ensymd sdomentr mpan2d
      inex1 wfun df-card funmpt2 onenon fvelrn sylancr jctild wb simpl cardonle
      wss sseqin2 sylib eqtrd sylibrd expimpd inss1 eqssd df-rab inteqi 3eqtr4g
      syl ) BDUAZEZBUBFBCGZHIZCJKZLZBAGZHIZADUCZKZLZCBUDWGWHJEZWISZCMZLZWLWNEZW
      MSZAMZLZWKWPWGWTXDWGWRXBCAWLNWLNEWGAOPCAUEZXBWRTWGXBWRXEWLJEZWMSXAXFWMXAX
      FWHWLUFIZUGCWLUMCWLUHUIUJXEWQXFWIWMWHWLJUKWHWLBHULUNUOQWGWLUPUQWGXBWRACWH
      WHDFZURZNXINEWGWHXHCOVCPWLXIRZWRXBTWGXJWQWIXBXJWQSZWIXHWNEZBXHHIZSZXBWQWI
      XNTXJWQWIXMXLWQWIWHXHUFIZXMWQXHWHWHUSUTWIXOSXMTWQBWHXHVAPVBWQDVDWHWFEXLAN
      XGCJKLDACVEVFWHVGWHDVHVIVJQXKWLXHRZXBXNVKXKWLXIXHXJWQVLXKXHWHVNZXIXHRWQXQ
      XJWHVMQXHWHVOVPVQXPXAXLWMXMWLXHWNUKWLXHBHULUNWEVRVSQXIWHVNWGWHXHVTPUQWAWJ
      WSWICJWBWCWOXCWMAWNWBWCWDVQ $.
  $}

  ${
    $d A x $.
    $( For any ordinal number ` A ` let ` ( har `` A ) ` denote the least
       cardinal that is greater than ` A ` .  (Contributed by RP,
       4-Nov-2023.) $)
    harval3on $p |- ( A e. On -> ( har ` A )
                    = |^| { x e. ran card | A ~< x } ) $=
      ( con0 wcel ccrd cdm char cfv csdm wbr crn crab cint wceq onenon harval3
      cv syl ) BCDBEFDBGHBAQIJAEKLMNBOABPR $.
  $}

  ${
    $d x y $.
    $( All natural numbers are cardinals.  (Contributed by RP, 1-Oct-2023.) $)
    omssrncard $p |- _om C_ ran card $=
      ( vx vy com ccrd crn cv wcel con0 cen wbr wn wral nnon wel wa wpss wi wss
      wne syl onelon simpl simpr biimpa syl21anc df-pss sylibr ex imdistani php
      onelpss ensymb sylnib ralrimiva elrncard sylanbrc ssriv ) ACDEZAFZCGZUSHG
      ZBFZUSIJZKZBUSLUSURGUSMZUTVDBUSUTBANZOZUSVBIJZVCVGUTVBUSPZOVHKUTVFVIUTVAV
      FVIQVEVAVFVIVAVFOZVBUSRVBUSSOZVIVJVBHGZVAVFVKUSVBUAVAVFUBVAVFUCVLVAOVFVKV
      BUSUKUDUEVBUSUFUGUHTUIUSVBUJTUSVBULUMUNBUSUOUPUQ $.
  $}

  $( 0 is a cardinal number.  (Contributed by RP, 1-Oct-2023.) $)
  0iscard $p |- (/) e. ran card $=
    ( com ccrd crn c0 omssrncard peano1 sselii ) ABCDEFG $.

  $( 1 is a cardinal number.  (Contributed by RP, 1-Oct-2023.) $)
  1iscard $p |- 1o e. ran card $=
    ( com ccrd crn c1o omssrncard 1onn sselii ) ABCDEFG $.

  $( ` _om ` is a cardinal number.  (Contributed by RP, 1-Oct-2023.) $)
  omiscard $p |- _om e. ran card $=
    ( vx com ccrd crn wcel con0 cv cen wbr wral omelon csdm nnsdom sdomnen rgen
    wn syl elrncard mpbir2an ) BCDEBFEAGZBHIPZABJKUAABTBETBLIUATMTBNQOABRS $.

  $( ` _om +o 1o ` is not a cardinal number.  (Contributed by RP,
     1-Oct-2023.) $)
  sucomisnotcard $p |- -. ( _om +o 1o ) e. ran card $=
    ( vx com c1o coa co ccrd crn wcel csuc con0 cv cen wn wral wa omelon sucidg
    wbr wrex ax-mp omensuc breq1 rspcev dfrex2 mpbi intnan wceq oa1suc elrncard
    mp2an eleq1i sylbb mto ) BCDEZFGZHZBIZJHZAKZUQLRZMAUQNZOZVAURUTAUQSZVAMBUQH
    ZBUQLRZVCBJHZVDPBJQTUAUTVEABUQUSBUQLUBUCUJUTAUQUDUEUFUPUQUOHVBUNUQUOVFUNUQU
    GPBUHTUKAUQUIULUM $.

  $( For any natural number, the add one operation is results in a cardinal
     number.  (Contributed by RP, 1-Oct-2023.) $)
  nna1iscard $p |- ( N e. _om -> ( N +o 1o ) e. ran card ) $=
    ( com wcel c1o coa co csuc wceq wa ccrd crn con0 nnon oa1suc syl peano2 jca
    simpl simpr eqeltrd omssrncard sseli 3syl ) ABCZADEFZAGZHZUFBCZIZUEBCUEJKZC
    UDUGUHUDALCUGAMANOAPQUIUEUFBUGUHRUGUHSTBUJUEUAUBUC $.

  $( The least cardinal greater than 2 is 3.  (Contributed by RP,
     5-Nov-2023.) $)
  har2o $p |- ( har ` 2o ) = 3o $=
    ( c2o char cfv csuc c3o com wcel wceq 2onn harsucnn ax-mp df-3o eqtr4i ) AB
    CZADZEAFGNOHIAJKLM $.

  $( May move to main section after ~ pr2ne . $)

  ${
    $d A x y $.
    $( A class is equinumerous to ordinal two iff it is a pair of distinct
       sets.  (Contributed by RP, 11-Oct-2023.) $)
    en2pr $p |- ( A ~~ 2o <-> E. x E. y ( A = { x , y } /\ x =/= y ) ) $=
      ( c2o cen wbr cv cpr wceq wex wa wne en2 pm4.71ri 19.41vv breq1 cvv pr2ne
      wb el2v bitrdi pm5.32i 2exbii 3bitr2i ) CDEFZCAGZBGZHZIZBJAJZUEKUIUEKZBJA
      JUIUFUGLZKZBJAJUEUJABCMNUIUEABOUKUMABUIUEULUIUEUHDEFZULCUHDEPUNULSABUFUGQ
      QRTUAUBUCUD $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( If an unordered pair is equinumerous to ordinal two, then both parts are
       sets.  (Contributed by RP, 8-Oct-2023.) $)
    pr2cv $p |- ( { A , B } ~~ 2o -> ( A e. _V /\ B e. _V ) ) $=
      ( vx vy cpr cv wceq wex c2o cen wbr cvv wcel wa en2 wi breq1 wne eqvisset
      vex wb pr2ne el2v biimpi w3a wo preq12nebg anim12i anim12ci jaoi biimtrdi
      mp3an12i com12 eqcoms sylbid exlimivv mpcom ) ABEZCFZDFZEZGZDHCHURIJKZALM
      ZBLMZNZCDUROVBVCVFPCDVBVCVAIJKZVFURVAIJQVGVFPVAURVGVAURGZVFUSLMZUTLMZVGUS
      UTRZVHVFPCTDTVGVKVGVKUACDUSUTLLUBUCUDVIVJVKUEVHUSAGZUTBGZNZUSBGZUTAGZNZUF
      VFUSUTABLLUGVNVFVQVLVDVMVECASDBSUHVOVEVPVDCBSDASUIUJUKULUMUNUOUPUQ $.
  $}

  $( If an unordered pair is equinumerous to ordinal two, then a part is a
     member.  (Contributed by RP, 21-Oct-2023.) $)
  pr2el1 $p |- ( { A , B } ~~ 2o -> A e. { A , B } ) $=
    ( cpr c2o cen wbr cvv wcel pr2cv simpld prid1g syl ) ABCZDEFZAGHZAMHNOBGHAB
    IJABGKL $.

  $( If an unordered pair is equinumerous to ordinal two, then a part is a set.
     (Contributed by RP, 21-Oct-2023.) $)
  pr2cv1 $p |- ( { A , B } ~~ 2o -> A e. _V ) $=
    ( cpr c2o cen wbr cvv wcel pr2cv simpld ) ABCDEFAGHBGHABIJ $.

  $( If an unordered pair is equinumerous to ordinal two, then a part is a
     member.  (Contributed by RP, 21-Oct-2023.) $)
  pr2el2 $p |- ( { A , B } ~~ 2o -> B e. { A , B } ) $=
    ( cpr c2o cen wbr cvv wcel pr2cv prid2g simpl2im ) ABCZDEFAGHBGHBLHABIABGJK
    $.

  $( If an unordered pair is equinumerous to ordinal two, then a part is a set.
     (Contributed by RP, 21-Oct-2023.) $)
  pr2cv2 $p |- ( { A , B } ~~ 2o -> B e. _V ) $=
    ( cpr c2o cen wbr cvv wcel pr2cv simprd ) ABCDEFAGHBGHABIJ $.

  $( An unordered pair is equinumerous to ordinal two iff both parts are sets
     not equal to each other.  (Contributed by RP, 8-Oct-2023.) $)
  pren2 $p |- ( { A , B } ~~ 2o
                  <-> ( A e. _V /\ B e. _V /\ A =/= B ) ) $=
    ( cvv wcel wa cpr c2o cen wbr wne w3a pr2ne pm5.32i pm4.71ri df-3an 3bitr4i
    pr2cv ) ACDZBCDZEZABFGHIZETABJZEUARSUBKTUAUBABCCLMUATABQNRSUBOP $.

  $( If an unordered pair is equinumerous to ordinal two, then a part is an
     element of the difference of the pair and the singleton of the other part.
     (Contributed by RP, 21-Oct-2023.) $)
  pr2eldif1 $p |- ( { A , B } ~~ 2o -> A e. ( { A , B } \ { B } ) ) $=
    ( cpr c2o cen wbr cvv wcel wne w3a csn pren2 prid1g 3ad2ant1 nelsn 3ad2ant3
    cdif wn eldifd sylbi ) ABCZDEFAGHZBGHZABIZJZAUABKZQHABLUEAUAUFUBUCAUAHUDABG
    MNUDUBAUFHRUCABOPST $.

  $( If an unordered pair is equinumerous to ordinal two, then a part is an
     element of the difference of the pair and the singleton of the other part.
     (Contributed by RP, 21-Oct-2023.) $)
  pr2eldif2 $p |- ( { A , B } ~~ 2o -> B e. ( { A , B } \ { A } ) ) $=
    ( cpr c2o cen wbr cvv wcel wne w3a csn pren2 prid2g 3ad2ant2 wn necom nelsn
    cdif sylbi 3ad2ant3 eldifd ) ABCZDEFAGHZBGHZABIZJZBUBAKZRHABLUFBUBUGUDUCBUB
    HUEABGMNUEUCBUGHOZUDUEBAIUHABPBAQSTUAS $.

  ${
    pren2d.a $e |- ( ph -> A e. V ) $.
    pren2d.b $e |- ( ph -> B e. W ) $.
    pren2d.aneb $e |- ( ph -> A =/= B ) $.
    $( A pair of two distinct sets is equinumerous to ordinal two.
       (Contributed by RP, 21-Oct-2023.) $)
    pren2d $p |- ( ph -> { A , B } ~~ 2o ) $=
      ( cvv wcel wne cpr c2o cen wbr elexd pren2 syl3anbrc ) ABIJCIJBCKBCLMNOAB
      DFPACEGPHBCQR $.
  $}

  $( May move to main section after ~ alephsuc . $)

  $( ` ( aleph `` 1o ) ` is the least uncountable ordinal.  (Contributed by RP,
     18-Nov-2023.) $)
  aleph1min $p |- ( aleph ` 1o ) = |^| { x e. On | _om ~< x } $=
    ( c1o cale cfv c0 csuc com cv csdm wbr con0 crab cint fveq2i char wcel wceq
    df-1o ax-mp eqtri 0elon alephsuc aleph0 ccrd cdm omelon onenon harval2 ) BC
    DEFZCDZGAHIJAKLMZBUICRNUJGODZUKUJECDZODZULEKPUJUNQUAEUBSUMGOUCNTGUDUEPZULUK
    QGKPUOUFGUGSAGUHSTT $.

  $( May move to main section after ~ alephiso . $)

  ${
    $d x y z $.
    $( ` aleph ` is a strictly order-preserving mapping of ` On ` onto the
       class of all infinite cardinal numbers.  (Contributed by RP,
       18-Nov-2023.) $)
    alephiso2 $p |- aleph Isom _E , ~< ( On , { x e. ran card | _om C_ x } ) $=
      ( vy vz con0 cv ccrd cfv wceq wa cab cep cale wiso csdm wf1o wb wral wcel
      wbr df-isom com wss crn crab alephiso iscard4 anbi1ci abbii df-rab eqtr4i
      f1oeq3 ax-mp wel alephon epelg alephord2 alephord 3bitr2d bibi2d ralbidva
      mp1i ralbiia anbi12i 3bitr4i mpbi ) DUAAEZUBZVFFGVFHZIZAJZKKLMZDVGAFUCZUD
      ZKNLMZAUEDVJLOZBEZCEZKSZVPLGZVQLGZKSZPZCDQZBDQZIDVMLOZVRVSVTNSZPZCDQZBDQZ
      IVKVNVOWEWDWIVJVMHVOWEPVJVFVLRZVGIZAJVMVIWKAVHWJVGVFUFUGUHVGAVLUIUJVJVMDL
      UKULWCWHBDVPDRZWBWGCDWLVQDRIZWAWFVRWMWAVSVTRZBCUMWFVTDRWAWNPWMVQUNVSVTDUO
      VAVPVQUPVPVQUQURUSUTVBVCBCDVJKKLTBCDVMKNLTVDVE $.
  $}

  ${
    $d x y $.
    $( ` aleph ` is a strictly order-preserving mapping of ` On ` onto the
       class of all infinite cardinal numbers.  (Contributed by RP,
       18-Nov-2023.) $)
    alephiso3 $p |- aleph Isom _E , ~< ( On , ( ran card \ _om ) ) $=
      ( vx vy con0 com wss ccrd crn crab cep csdm cale wiso cdif alephiso2 wceq
      cv wb wcel wn omelon cen wbr wral elrncard simplbi ontri1 sylancr rabbiia
      dfdif2 eqtr4i isoeq5 ax-mp mpbi ) CDAPZEZAFGZHZIJKLZCUPDMZIJKLZANUQUSOURU
      TQUQUNDRSZAUPHUSUOVAAUPUNUPRZDCRUNCRZUOVAQTVBVCBPUNUAUBSBUNUCBUNUDUEDUNUF
      UGUHAUPDUIUJCUQUSIJKUKULUM $.
  $}

  $( May move to main section after ~ infdjuabs . $)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Infinite Sets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x A $.  $d x B $.
    $( The powerclass is an element of a class closed under union and
       powerclass operations iff the element is a member of that class.
       (Contributed by RP, 21-Mar-2020.) $)
    pwelg $p |- ( A. x e. B ( U. x e. B /\ ~P x e. B )
                  -> ( A e. B <-> ~P A e. B ) ) $=
      ( cv cuni wcel cpw wa wral simpr ralimi wceq pweq eleq1d rspccv syl simpl
      wi unieq unipw eqtrdi impbid ) ADZEZCFZUCGZCFZHZACIZBCFZBGZCFZUIUGACIUJUL
      RUHUGACUEUGJKUGULABCUCBLUFUKCUCBMNOPUIUEACIULUJRUHUEACUEUGQKUEUJAUKCUCUKL
      ZUDBCUMUDUKEBUCUKSBTUANOPUB $.

    $( The powerclass of an infinite set is an infinite set, and vice-versa.
       Here ` B ` is a class which is closed under both the union and the
       powerclass operations and which may have infinite sets as members.
       (Contributed by RP, 21-Mar-2020.) $)
    pwinfig $p |- ( A. x e. B ( U. x e. B /\ ~P x e. B )
                  -> ( A e. ( B \ Fin ) <-> ~P A e. ( B \ Fin ) ) ) $=
      ( cv cuni wcel cpw wa wral cfn wn cdif pwelg wb pwfi notbii anbi12d eldif
      a1i 3bitr4g ) ADZECFUAGCFHACIZBCFZBJFZKZHBGZCFZUFJFZKZHBCJLZFUFUJFUBUCUGU
      EUIABCMUEUINUBUDUHBOPSQBCJRUFCJRT $.
  $}

  ${
    $d x y U $.  $d x A $.
    $( The powerclass of an infinite set is an infinite set, and vice-versa.
       Here ` U ` is a weak universe.  (Contributed by RP, 21-Mar-2020.) $)
    pwinfi2 $p |- ( U e. WUni
                  -> ( A e. ( U \ Fin ) <-> ~P A e. ( U \ Fin ) ) ) $=
      ( vx vy cwun wcel wtr c0 wne cv cuni cpw cpr wral w3a wa cfn cdif iswun
      wb ibi 3simpa ralimi 3ad2ant3 pwinfig 3syl ) BEFZBGZBHIZCJZKBFZUJLBFZUJDJ
      MBFDBNZOZCBNZOZUKULPZCBNZABQRZFALUSFTUGUPCDBESUAUOUHURUIUNUQCBUKULUMUBUCU
      DCABUEUF $.
  $}

  ${
    $d x T $.  $d x A $.
    $( The powerclass of an infinite set is an infinite set, and vice-versa.
       Here ` T ` is a transitive Tarski universe.  (Contributed by RP,
       21-Mar-2020.) $)
    pwinfi3 $p |- ( ( T e. Tarski /\ Tr T )
                  -> ( A e. ( T \ Fin ) <-> ~P A e. ( T \ Fin ) ) ) $=
      ( vx ctsk wcel wtr wa cv cuni cpw wral cfn cdif wb tskuni 3expia wi tskpw
      ex adantr jcad ralrimiv pwinfig syl ) BDEZBFZGZCHZIBEZUHJBEZGZCBKABLMZEAJ
      ULENUGUKCBUGUHBEZUIUJUEUFUMUIUHBOPUEUMUJQUFUEUMUJUHBRSTUAUBCABUCUD $.
  $}

  ${
    $d x A $.
    $( The powerclass of an infinite set is an infinite set, and vice-versa.
       (Contributed by RP, 21-Mar-2020.) $)
    pwinfi $p |- ( A e. ( _V \ Fin ) <-> ~P A e. ( _V \ Fin ) ) $=
      ( vx cv cuni cvv wcel cpw wa wral cfn cdif wb vuniex vpwex pm3.2i pwinfig
      rgenw ax-mp ) BCZDEFZSGEFZHZBEIAEJKZFAGUCFLUBBETUABMBNOQBAEPR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Finite intersection property
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  While there is not yet a definition, the finite intersection property of a
  class is introduced by ~ fiint where two textbook definitions are shown to
  be equivalent.

  This property is seen often with ordinal numbers ( ~ onin , ~ ordelinel ),
  chains of sets ordered by the proper subset relation ( ~ sorpssin ), various
  sets in the field of topology ( ~ inopn , ~ incld , ~ innei , ... ) and
  "universal" classes like weak universes ( ~ wunin , ~ tskin ) and the class
  of all sets ( ~ inex1g ).

$)

  ${
    $d u v x y A $.
    $( A definition of the finite intersection property of a class based on
       closure under pairwise intersection of its elements is independent of
       the dummy variables.  (Contributed by RP, 1-Jan-2020.) $)
    fipjust $p |- ( A. u e. A A. v e. A ( u i^i v ) e. A
                    <-> A. x e. A A. y e. A ( x i^i y ) e. A ) $=
      ( cv cin wcel weq ineq1 eleq1d ineq2 cbvral2vw ) DFZCFZGZEHAFZBFZGZEHQOGZ
      EHDCABEEDAIPTENQOJKCBITSEORQLKM $.
  $}

  ${
    $d z ps $.  $d z ch $.  $d z th $.  $d x y z $.  $d y V $.  $d z R $.
    cllem0.v $e |- V = { z | ph } $.
    cllem0.rex $e |- R e. U $.
    cllem0.r $e |- ( z = R -> ( ph <-> ps ) ) $.
    cllem0.x $e |- ( z = x -> ( ph <-> ch ) ) $.
    cllem0.y $e |- ( z = y -> ( ph <-> th ) ) $.
    cllem0.closed $e |- ( ( ch /\ th ) -> ps ) $.
    $( The class of all sets with property ` ph ( z ) ` is closed under the
       binary operation on sets defined in ` R ( x , y ) ` .  (Contributed by
       RP, 3-Jan-2020.) $)
    cllem0 $p |- A. x e. V A. y e. V R e. V $=
      ( wcel wral elab2 ralbii cv wi wal elexi df-ral 3bitri syl2anb ex alrimiv
      vex mpgbir ) HJQZFJRZEJRZEUAZJQZFUAZJQZBUBZFUCZUBZEUNBFJRZEJRUTEJRVAEUCUM
      VBEJULBFJABGHJHILUDMKSTTVBUTEJBFJUETUTEJUEUFUPUSFUPURBUPCDBURACGUOJEUJNKS
      ADGUQJFUJOKSPUGUHUIUK $.
  $}

  ${
    $d x y z $.  $d y A $.  $d z B $.
    superficl.a $e |- A = { z | B C_ z } $.
    $( The class of all supersets of a class has the finite intersection
       property.  (Contributed by RP, 1-Jan-2020.)  (Proof shortened by RP,
       3-Jan-2020.) $)
    superficl $p |- A. x e. A A. y e. A ( x i^i y ) e. A $=
      ( cv wss cin cvv vex inex1 sseq2 wa ssin biimpi cllem0 ) ECGZHEAGZBGZIZHZ
      ESHZETHZABCUAJDFSTAKLRUAEMRSEMRTEMUCUDNUBESTOPQ $.

    $( The class of all supersets of a class is closed under binary union.
       (Contributed by RP, 3-Jan-2020.) $)
    superuncl $p |- A. x e. A A. y e. A ( x u. y ) e. A $=
      ( cv wss cun cvv vex unex sseq2 ssun3 adantr cllem0 ) ECGZHEAGZBGZIZHZERH
      ZESHZABCTJDFRSAKBKLQTEMQREMQSEMUBUAUCERSNOP $.
  $}

  ${
    $d x y z $.  $d y A $.  $d z B $.
    $( N.B. This hypothesis is same as the power class of B. $)
    ssficl.a $e |- A = { z | z C_ B } $.
    $( The class of all subsets of a class has the finite intersection
       property.  (Contributed by RP, 1-Jan-2020.)  (Proof shortened by RP,
       3-Jan-2020.) $)
    ssficl $p |- A. x e. A A. y e. A ( x i^i y ) e. A $=
      ( cv wss cin cvv vex inex1 sseq1 ssinss1 adantr cllem0 ) CGZEHAGZBGZIZEHZ
      REHZSEHZABCTJDFRSAKLQTEMQREMQSEMUBUAUCRSENOP $.

    $( The class of all subsets of a class is closed under binary union.
       (Contributed by RP, 3-Jan-2020.) $)
    ssuncl $p |- A. x e. A A. y e. A ( x u. y ) e. A $=
      ( cv wss cun cvv vex unex sseq1 wa unss biimpi cllem0 ) CGZEHAGZBGZIZEHZS
      EHZTEHZABCUAJDFSTAKBKLRUAEMRSEMRTEMUCUDNUBSTEOPQ $.

    $( The class of all subsets of a class is closed under class difference.
       (Contributed by RP, 3-Jan-2020.) $)
    ssdifcl $p |- A. x e. A A. y e. A ( x \ y ) e. A $=
      ( cv wss cdif cvv vex difexi sseq1 ssdifss adantr cllem0 ) CGZEHAGZBGZIZE
      HZREHZSEHZABCTJDFRSAKLQTEMQREMQSEMUBUAUCRESNOP $.

    $( The class of all subsets of a class is closed under symmetric
       difference.  (Contributed by RP, 3-Jan-2020.) $)
    sssymdifcl $p |- A. x e. A A. y e. A ( ( x \ y ) u. ( y \ x ) ) e. A $=
      ( cv wss cdif cun cvv vex difexi unex sseq1 ssdifss wa unss biimpi syl2an
      cllem0 ) CGZEHAGZBGZIZUDUCIZJZEHZUCEHZUDEHZABCUGKDFUEUFUCUDALMUDUCBLMNUBU
      GEOUBUCEOUBUDEOUIUEEHZUFEHZUHUJUCEUDPUDEUCPUKULQUHUEUFERSTUA $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y ph $.
    fiinfi.a $e |- ( ph -> A. x e. A A. y e. A ( x i^i y ) e. A ) $.
    fiinfi.b $e |- ( ph -> A. x e. B A. y e. B ( x i^i y ) e. B ) $.
    fiinfi.c $e |- ( ph -> C = ( A i^i B ) ) $.
    $( If two classes have the finite intersection property, then so does their
       intersection.  (Contributed by RP, 1-Jan-2020.) $)
    fiinfi $p |- ( ph -> A. x e. C A. y e. C ( x i^i y ) e. C ) $=
      ( cv cin wcel wral elinel1 imim1i ralimi2 imim12i syl ralbidv mpbird elin
      wa elinel2 r19.26-2 sylanbrc 2ralbii sylibr eleq2d raleqdv ) ABJZCJZKZFLZ
      CFMZBFMUNBDEKZMZAUPUMCUOMZBUOMZAURULUOLZCUOMZBUOMZAULDLZULELZUBZCUOMBUOMZ
      VAAVBCUOMZBUOMZVCCUOMZBUOMZVEAVBCDMZBDMVGGVJVFBDUOUJUOLZUJDLVJVFUJDENVBVB
      CDUOUKUOLZUKDLVBUKDENOPQPRAVCCEMZBEMVIHVMVHBEUOVKUJELVMVHUJDEUCVCVCCEUOVL
      UKELVCUKDEUCOPQPRVBVCBCUOUOUDUEUSVDBCUOUOULDEUAUFUGAUQUTBUOAUMUSCUOAFUOUL
      IUHSSTAUNUQBUOAUMCFUOIUISTAUNBFUOIUIT $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  RP ADDTO: Subclasses and subsets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( AFTER 11928 rabssab $)

  ${
    $d y ph $.  $d y A $.  $d x y $.
    $( Condition when restricted class is equal to unrestricted class.
       (Contributed by RP, 13-Aug-2020.) $)
    rababg $p |- ( A. x ( ph -> x e. A ) <-> { x e. A | ph } = { x | ph } ) $=
      ( vy cv wcel wi wal wa cab crab wceq ancrb albii nfv nfsab1 nfrab1 eleq1w
      bitr3id wss nfcri nfim weq abid rabid imbi12d cbvalv1 eqss biantrur df-ss
      rabssab 3bitr2ri 3bitri ) ABEZCFZGZBHAUOAIZGZBHDEZABJZFZUSABCKZFZGZDHZVBU
      TLZUPURBAUOMNURVDBDURDOVAVCBABDPBDVBABCQUAUBBDUCZAVAUQVCAUNUTFVGVAABUDBDU
      TRSUQUNVBFVGVCABCUEBDVBRSUFUGVFVBUTTZUTVBTZIVIVEVBUTUHVHVIABCUKUIDUTVBUJU
      LUM $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  RP ADDTO: The intersection of a class
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( AFTER 14085 elintg $)

  ${
    $d x A $.
    $( Two ways of saying a set is an element of the intersection of a class
       with the intersection of a class.  (Contributed by RP, 13-Aug-2020.) $)
    elinintab $p |- ( A e. ( B i^i |^| { x | ph } )
                      <-> ( A e. B /\ A. x ( ph -> A e. x ) ) ) $=
      ( cab cint cin wcel wa cv wi wal elin elintabg pm5.32i bitri ) CDABEFZGHC
      DHZCQHZIRACBJHKBLZICDQMRSTABCDNOP $.
  $}

  $( AFTER 14110 elintrabg $)

  ${
    elmapintrab.ex $e |- C e. _V $.
    elmapintrab.sub $e |- C C_ B $.

    $d w ph $.  $d w x A $.  $d w x B $.  $d w C $.
    $( Two ways to say a set is an element of the intersection of a class of
       images.  (Contributed by RP, 16-Aug-2020.) $)
    elmapintrab $p |- ( A e. V
                        -> ( A e. |^| { w e. ~P B | E. x ( w = C /\ ph ) }
                             <-> ( ( E. x ph -> A e. B )
                                   /\ A. x ( ph -> A e. C ) ) ) ) $=
      ( wcel wa wex wi wal bitrdi wss 19.23v bi2.04 albii 3bitri wceq crab cint
      cv wral elintrabg df-ral velpw bicomi imbi12i 19.21v impexp bitri 3bitr2i
      cpw alcom sseq1 eleq2 sseli pm4.71ri imbi12d imbi2d ceqsalv wb pm5.5 jcab
      ax-mp 19.26 anbi1i ) DGJZDCUDZFUAZAKZBLZCEUOZUBUCJZVKVOJZVNDVKJZMZMZCNZAB
      LDEJZMZADFJZMZBNZKZVJVPVSCVOUEWAVNCDVOGUFVSCVOUGOWAVLAVKEPZVRMZMZMZBNZCNW
      KCNZBNZWGVTWLCVTWHVMVRMZBNZMWHWOMZBNWLVQWHVSWPCEUHWPVSVMVRBQUIUJWHWOBUKWQ
      WKBWQVMWIMWKWHVMVRRVLAWIULUMSUNSWKCBUPWNAWBMZWEKZBNWRBNZWFKWGWMWSBWMAFEPZ
      WBWDKZMZMZXAAXBMZMZWSWJXDCFHVLWIXCAVLWHXAVRXBVKFEUQVLVRWDXBVKFDURWDWBFEDI
      USUTOVAVBVCAXAXBRXFXEWSXAXFXEVDIXAXEVEVGAWBWDVFUMTSWRWEBVHWTWCWFAWBBQVITT
      O $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  RP ADDTO: Theorems requiring subset and intersection existence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( AFTER 15376 inex2 $)

  ${
    $d w ph $.  $d w x A $.  $d w x B $.
    $( Two ways of saying a set is an element of the intersection of a class
       with the intersection of a class.  (Contributed by RP, 14-Aug-2020.) $)
    elinintrab $p |- ( A e. V
                       -> ( A e. |^| { w e. ~P B
                                       | E. x ( w = ( B i^i x ) /\ ph ) }
                            <-> ( ( E. x ph -> A e. B )
                                  /\ A. x ( ph -> A e. x ) ) ) ) $=
      ( wcel cv cin wceq wa wex cpw crab cint wi wal vex inex2 bitri inss1 elin
      elmapintrab imbi2i jcab albii 19.26 19.23v anbi1i anbi2i anabs5 bitrdi )
      DFGDCHEBHZIZJAKBLCEMNOGABLDEGZPZADUNGZPZBQZKZUPADUMGZPZBQZKZABCDEUNFUMEBR
      SEUMUAUCUTUPVDKVDUSVDUPUSAUOPZVBKZBQZVDURVFBURAUOVAKZPVFUQVHADEUMUBUDAUOV
      AUETUFVGVEBQZVCKVDVEVBBUGVIUPVCAUOBUHUITTUJUPVCUKTUL $.
  $}

  ${
    $d u w ph $.  $d u w x A $.
    $( Upper bound on intersection of class and the intersection of a class.
       (Contributed by RP, 13-Aug-2020.) $)
    inintabss $p |- ( A i^i |^| { x | ph } )
                      C_ |^| { w e. ~P A |
                            E. x ( w = ( A i^i x ) /\ ph ) } $=
      ( vu cab cint cin cv wceq wa wex cpw crab wcel wel wi wal ax-1 anim1i cvv
      elinintab wb elinintrab elv 3imtr4i ssriv ) EDABFGHZCIDBIHJAKBLCDMNGZEIZD
      OZAEBPQBRZKABLZUKQZULKZUJUHOUJUIOZUKUNULUKUMSTABUJDUBUPUOUCEABCUJDUAUDUEU
      FUG $.
  $}

  ${
    inintabd.x $e |- ( ph -> E. x ps ) $.
    $d u ph $.  $d u w ps $.  $d u w x A $.
    $( Value of the intersection of class with the intersection of a nonempty
       class.  (Contributed by RP, 13-Aug-2020.) $)
    inintabd $p |- ( ph -> ( A i^i |^| { x | ps } )
                    = |^| { w e. ~P A | E. x ( w = ( A i^i x ) /\ ps ) } ) $=
      ( vu cab cint cin cv wceq wa wex cpw crab wcel wel wi wb wal pm5.5 bicomd
      syl anbi1d elinintab cvv elinintrab elv 3bitr4g eqrdv ) AGEBCHIJZDKECKJLB
      MCNDEOPIZAGKZEQZBGCRSCUAZMBCNZUOSZUPMZUNULQUNUMQZAUOURUPAURUOAUQURUOTFUQU
      OUBUDUCUEBCUNEUFUTUSTGBCDUNEUGUHUIUJUK $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  RP ADDTO: Relations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( AFTER 16786 cxp $)

  ${
    xpinintabd.x $e |- ( ph -> E. x ps ) $.
    $d w ps $.  $d w x A $.  $d w x B $.

    $( Value of the intersection of Cartesian product with the intersection of
       a nonempty class.  (Contributed by RP, 12-Aug-2020.) $)
    xpinintabd $p |- ( ph -> ( ( A X. B ) i^i |^| { x | ps } )
                    = |^| { w e. ~P ( A X. B ) |
                            E. x ( w = ( ( A X. B ) i^i x ) /\ ps ) } ) $=
      ( cxp inintabd ) ABCDEFHGI $.
  $}

  $( AFTER 17081 releq $)

  $( If the intersection of a class is a relation, then the class is nonempty.
     (Contributed by RP, 12-Aug-2020.) $)
  relintabex $p |- ( Rel |^| { x | ph } -> E. x ph ) $=
    ( cab cint wrel cvv wcel wex wn wceq intnex nrelv releq sylbi con4i intexab
    mtbiri sylibr ) ABCZDZEZTFGZABHUBUAUBITFJZUAISKUCUAFELTFMQNOABPR $.

  $( AFTER 18222 cnvcnv $)

  ${
    $d x A $.
    $( Two ways of saying a set is an element of the converse of the converse
       of the intersection of a class.  (Contributed by RP, 20-Aug-2020.) $)
    elcnvcnvintab $p |- ( A e. `' `' |^| { x | ph }
                          <-> ( A e. ( _V X. _V )
                                /\ A. x ( ph -> A e. x ) ) ) $=
      ( cab cint ccnv cvv cxp cin cv wi wal cnvcnv incom eqtri eleq2i elinintab
      wcel wa bitri ) CABDEZFFZRCGGHZUAIZRCUCRACBJRKBLSUBUDCUBUAUCIUDUAMUAUCNOP
      ABCUCQT $.
  $}

  ${
    $d w ph $.  $d w x $.
    $( Value of the intersection of a class when it is a relation.
       (Contributed by RP, 12-Aug-2020.) $)
    relintab $p |- ( Rel |^| { x | ph } -> |^| { x | ph }
                   = |^| { w e. ~P ( _V X. _V ) |
                           E. x ( w = `' `' x /\ ph ) } ) $=
      ( cab cint wrel ccnv cvv cxp cin cv wceq wex cpw crab cnvcnv incom dfrel2
      wa eqtri biimpi relintabex xpinintabd eqtr4i eqeq2i anbi1i rabbii 3eqtr3a
      exbii inteqi eqtrdi ) ABDEZFZULGGZHHIZULJZULCKZBKZGGZLZASZBMZCUONZOZEZUNU
      LUOJUPULPULUOQTUMUNULLULRUAUMUPUQUOURJZLZASZBMZCVCOZEVEUMABCHHABUBUCVJVDV
      IVBCVCVHVABVGUTAVFUSUQVFURUOJUSUOURQURPUDUEUFUIUGUJUKUH $.
  $}

  $( AFTER 18222 cnvcnv $)

  $( A non-relation is equal to the base class with all ordered pairs removed.
     (Contributed by RP, 25-Oct-2020.) $)
  nonrel $p |- ( A \ `' `' A ) = ( A \ ( _V X. _V ) ) $=
    ( ccnv cdif cvv cxp cin cnvcnv difeq2i difin eqtri ) AABBZCAADDEZFZCALCKMAA
    GHALIJ $.

  $( Only an ordered pair where not both entries are sets could be an element
     of the non-relation part of class.  (Contributed by RP, 25-Oct-2020.) $)
  elnonrel $p |- ( <. X , Y >. e. ( A \ `' `' A )
                   <-> ( (/) e. A /\ -. ( X e. _V /\ Y e. _V ) ) ) $=
    ( cop ccnv cdif wcel cvv cxp c0 wa nonrel eleq2i eldif opelxp notbii anbi2i
    wn opprc bitri eleq1d pm5.32ri ) BCDZAAEEFZGUCAHHIZFZGZJAGZBHGCHGKZRZKZUDUF
    UCALMUGUCAGZUCUEGZRZKZUKUCAUENUOULUJKUKUNUJULUMUIBCHHOPQUJULUHUJUCJABCSUAUB
    TTT $.

  $( AFTER 18224 cnvcnvss $)

  $( Subclass theorem for converse.  (Contributed by RP, 22-Oct-2020.) $)
  cnvssb $p |- ( Rel A -> ( A C_ B <-> `' A C_ `' B ) ) $=
    ( wrel wss ccnv cnvss wa dfrel2 biimpi eqcomd adantr cnvcnvss sstrdi adantl
    wceq id eqsstrd ex syl5 impbid2 ) ACZABDZAEZBEZDZABFUEUCEZUDEZDZUAUBUCUDFUA
    UHUBUAUHGAUFBUAAUFOUHUAUFAUAUFAOAHIJKUHUFBDUAUHUFUGBUHPBLMNQRST $.

  $( The non-relation part of a relation is empty.  (Contributed by RP,
     22-Oct-2020.) $)
  relnonrel $p |- ( Rel A <-> ( A \ `' `' A ) = (/) ) $=
    ( wrel ccnv wss wa cdif c0 wceq dfrel2 eqss bitri cnvcnvss biantrur 3bitr2i
    ssdif0 ) ABZACCZADZAQDZEZSAQFGHPQAHTAIQAJKRSALMAQON $.

  $( The converse of the non-relation part of a class is empty.  (Contributed
     by RP, 18-Oct-2020.) $)
  cnvnonrel $p |- `' ( A \ `' `' A ) = (/) $=
    ( ccnv cdif c0 cnvdif wrel wceq relcnv relnonrel mpbi eqtri ) AABZBZCBLMBCZ
    DAMELFNDGAHLIJK $.

  $( A non-relation cannot relate any two classes.  (Contributed by RP,
     23-Oct-2020.) $)
  brnonrel $p |- ( ( X e. U /\ Y e. V ) -> -. X ( A \ `' `' A ) Y ) $=
    ( wcel wa ccnv cdif wbr c0 br0 brcnvg ancoms cnvnonrel breqi bitr3di mtbiri
    wb ) DBFZECFZGZDEAAHHIZJZEDKJZEDLUBEDUCHZJZUDUEUATUGUDSEDCBUCMNEDUFKAOPQR
    $.

  $( The domain of the non-relation part of a class is empty.  (Contributed by
     RP, 22-Oct-2020.) $)
  dmnonrel $p |- dom ( A \ `' `' A ) = (/) $=
    ( ccnv cdif cdm crn c0 dfdm4 cnvnonrel rneqi rn0 3eqtri ) AABBCZDLBZEFEFLGM
    FAHIJK $.

  $( The range of the non-relation part of a class is empty.  (Contributed by
     RP, 22-Oct-2020.) $)
  rnnonrel $p |- ran ( A \ `' `' A ) = (/) $=
    ( ccnv cdif cdm c0 wceq crn dmnonrel dm0rn0 mpbi ) AABBCZDEFKGEFAHKIJ $.

  $( A restriction of the non-relation part of a class is empty.  (Contributed
     by RP, 22-Oct-2020.) $)
  resnonrel $p |- ( ( A \ `' `' A ) |` B ) = (/) $=
    ( ccnv cdif cres c0 wss wceq cvv ssres2 ax-mp cnvnonrel cnveqi cnvcnv2 cnv0
    ssv 3eqtr3i sseqtri ss0b mpbi ) AACCDZBEZFGUBFHUBUAIEZFBIGUBUCGBPBIUAJKUACZ
    CFCUCFUDFALMUANOQRUBST $.

  $( An image under the non-relation part of a class is empty.  (Contributed by
     RP, 22-Oct-2020.) $)
  imanonrel $p |- ( ( A \ `' `' A ) " B ) = (/) $=
    ( ccnv cdif cima cres crn c0 df-ima resnonrel rneqi rn0 3eqtri ) AACCDZBENB
    FZGHGHNBIOHABJKLM $.

  $( AFTER 18346 co02 $)

  $( Composition with the non-relation part of a class is empty.  (Contributed
     by RP, 22-Oct-2020.) $)
  cononrel1 $p |- ( ( A \ `' `' A ) o. B ) = (/) $=
    ( ccnv cdif ccom cnvco cnvnonrel coeq2i co02 3eqtri cnveqi wrel wceq dfrel2
    c0 relco mpbi cnv0 3eqtr3i ) AACCDZBEZCZCZOCUAOUBOUBBCZTCZEUDOEOTBFUEOUDAGH
    UDIJKUALUCUAMTBPUANQRS $.

  $( AFTER 18347 co01 $)

  $( Composition with the non-relation part of a class is empty.  (Contributed
     by RP, 22-Oct-2020.) $)
  cononrel2 $p |- ( A o. ( B \ `' `' B ) ) = (/) $=
    ( ccnv cdif ccom cnvco cnvnonrel coeq1i co01 3eqtri cnveqi wrel wceq dfrel2
    c0 relco mpbi cnv0 3eqtr3i ) ABBCCDZEZCZCZOCUAOUBOUBTCZACZEOUEEOATFUDOUEBGH
    UEIJKUALUCUAMATPUANQRS $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  RP ADDTO: Functions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  See also ~ idssxp by Thierry Arnoux.

$)

  $( AFTER 18872 fnresi $)

  $(
  %( A diagonal set as a subset of a Cartesian product.  (Contributed by
     Thierry Arnoux, 29-Dec-2019.) %)
  idssxp $p |- ( _I |` A ) C_ ( A X. A ) $=
    ( cid cres cdm crn cxp wfn wss fnresi fnrel relssdmrn dmresi rnresi xpeq12i
    wrel mp2b sseqtri ) BACZRDZREZFZAAFRAGRORUAHAIARJRKPSATAALAMNQ $.
  $)

  $( AFTER 19314 fvex $)

  ${
    elmapintab.1 $e |- ( A e. B
                         <-> ( A e. C /\ ( F ` A ) e. |^| { x | ph } ) ) $.
    elmapintab.2 $e |- ( A e. E <-> ( A e. C /\ ( F ` A ) e. x ) ) $.
    $d x A $.  $d x C $.  $d x F $.
    $( Two ways to say a set is an element of mapped intersection of a class.
       Here ` F ` maps elements of ` C ` to elements of ` |^| { x | ph } ` or
       ` x ` .  (Contributed by RP, 19-Aug-2020.) $)
    elmapintab $p |- ( A e. B <-> ( A e. C /\ A. x ( ph -> A e. E ) ) ) $=
      ( wcel cfv cab cint wa cv wi wal fvex elintab anbi2i baibr imbi2d pm5.32i
      albidv 3bitri ) CDJCEJZCGKZABLMJZNUFAUGBOJZPZBQZNUFACFJZPZBQZNHUHUKUFABUG
      CGRSTUFUKUNUFUJUMBUFUIULAULUFUIIUAUBUDUCUE $.
  $}

  $( AFTER 19354 fvrn0 $)

  $( The function value of any class under a non-relation is empty.
     (Contributed by RP, 23-Oct-2020.) $)
  fvnonrel $p |- ( ( A \ `' `' A ) ` X ) = (/) $=
    ( ccnv cdif cfv c0 csn wcel wceq crn cun fvrn0 wss rnnonrel eqsstri ssequn1
    0ss mpbi eleqtri fvex elsn ) BAACCDZEZFGZHUCFIUCUBJZUDKZUDUBBLUEUDMUFUDIUEF
    UDANUDQOUEUDPRSUCFBUBTUAR $.

  $( AFTER 19465 fvi $)

  $( Two ways to say a set is a member of an intersection.  (Contributed by RP,
     19-Aug-2020.) $)
  elinlem $p |- ( A e. ( B i^i C ) <-> ( A e. B /\ ( _I ` A ) e. C ) ) $=
    ( cin wcel wa cid cfv elin fvi eqcomd eleq1d pm5.32i bitri ) ABCDEABEZACEZF
    OAGHZCEZFABCIOPROAQCOQAABJKLMN $.

  $( Two ways to say a set is a member of the converse of the converse of a
     class.  (Contributed by RP, 20-Aug-2020.) $)
  elcnvcnvlem $p |- ( A e. `' `' B <-> ( A e. ( _V X. _V )
                                           /\ ( _I ` A ) e. B ) ) $=
    ( ccnv wcel cvv cxp cin cid cfv wa cnvcnv incom eqtri eleq2i elinlem bitri
    ) ABCCZDAEEFZBGZDARDAHIBDJQSAQBRGSBKBRLMNARBOP $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  RP ADDTO: Finite induction (for finite ordinals)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Original probably needs new subsection for Relation-related existence
  theorems.

$)

  $( AFTER 23510 cnvexg $)

  ${
    cnvcnvintabd.x $e |- ( ph -> E. x ps ) $.
    $d y ph $.  $d w y ps $.  $d w x y $.
    $( Value of the relationship content of the intersection of a class.
       (Contributed by RP, 20-Aug-2020.) $)
    cnvcnvintabd $p |- ( ph -> `' `' |^| { x | ps }
                         = |^| { w e. ~P ( _V X. _V )
                         | E. x ( w = `' `' x /\ ps ) } ) $=
      ( vy cab cint ccnv cv wa wex cvv wcel wi wal bitrid bicomd wb cnvexg wceq
      cxp cpw crab wel cin cnvcnv eleq2i elin rbaib imbi2d albidv pm5.32i pm5.5
      syl anbi1d elcnvcnvintab vex mp2b wrel wss relcnv df-rel mpbi elmapintrab
      elv 3bitr4g eqrdv ) AFBCGHIIZDJCJZIZIZUABKCLDMMUBZUCUDHZAFJZVMNZBFCUEZOZC
      PZKZBCLZVPOZBVOVLNZOZCPZKZVOVINVOVNNZVTVPWEKAWFVPVSWEVPVRWDCVPVQWCBVPWCVQ
      WCVOVJVMUFZNZVPVQVLWHVOVJUGUHWIVQVPVOVJVMUIUJQRUKULUMAVPWBWEAWBVPAWAWBVPS
      EWAVPUNUORUPQBCVOUQWGWFSFBCDVOVMVLMVJMNVKMNVLMNCURVJMTVKMTUSVLUTVLVMVAVKV
      BVLVCVDVEVFVGVH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  RP ADDTO: First and second members of an ordered pair
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( AFTER 23778 op2ndd $)

  ${
    elcnvlem.f $e |- F = ( x e. ( _V X. _V )
                           |-> <. ( 2nd ` x ) , ( 1st ` x ) >. ) $.
    $d u v A $.  $d u v B $.  $d u v F $.  $d u v x $.
    $( Two ways to say a set is a member of the converse of a class.
       (Contributed by RP, 19-Aug-2020.) $)
    elcnvlem $p |- ( A e. `' B <-> ( A e. ( _V X. _V ) /\ ( F ` A ) e. B ) ) $=
      ( vu vv ccnv wcel cv cop wceq wa wex cvv cxp cfv elcnv2 fveq2 vex opeq12d
      opelvv c2nd c1st op2ndd op1std fvmpt ax-mp eqtrdi eleq1d copsex2gb bitri
      opex ) BCHIBFJZGJZKZLZUOUNKZCIZMGNFNBOOPZIBDQZCIZMFGBCRVBUSFGBUQVAURCUQVA
      UPDQZURBUPDSUPUTIVCURLUNUOFTZGTZUBAUPAJZUCQZVFUDQZKURUTDVFUPLVGUOVHUNUNUO
      VFVDVEUEUNUOVFVDVEUFUAEUOUNUMUGUHUIUJUKUL $.
  $}

  ${
    $d x y $.  $d x A $.
    $( Two ways of saying a set is an element of the converse of the
       intersection of a class.  (Contributed by RP, 19-Aug-2020.) $)
    elcnvintab $p |- ( A e. `' |^| { x | ph }
                       <-> ( A e. ( _V X. _V )
                             /\ A. x ( ph -> A e. `' x ) ) ) $=
      ( vy cab cint ccnv cvv cxp cv c2nd cfv c1st cmpt eqid elcnvlem elmapintab
      cop ) ABCABEFZGHHIZBJZGDTDJZKLUBMLRNZDCSUCUCOZPDCUAUCUDPQ $.
  $}

  ${
    cnvintabd.x $e |- ( ph -> E. x ps ) $.
    $d y ph $.  $d w y ps $.  $d w x y $.
    $( Value of the converse of the intersection of a nonempty class.
       (Contributed by RP, 20-Aug-2020.) $)
    cnvintabd $p |- ( ph -> `' |^| { x | ps } = |^| { w e. ~P ( _V X. _V )
                      | E. x ( w = `' x /\ ps ) } ) $=
      ( vy cab cint ccnv cv wceq wa wex cvv cxp cpw crab wcel wi wb wal syl vex
      pm5.5 bicomd anbi1d elcnvintab cnvex wrel wss relcnv mpbi elmapintrab elv
      df-rel 3bitr4g eqrdv ) AFBCGHIZDJCJZIZKBLCMDNNOZPQHZAFJZVARZBVCUTRSCUAZLB
      CMZVDSZVELZVCURRVCVBRZAVDVGVEAVGVDAVFVGVDTEVFVDUDUBUEUFBCVCUGVIVHTFBCDVCV
      AUTNUSCUCUHUTUIUTVAUJUSUKUTUOULUMUNUPUQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  RP ADDTO: The reflexive and transitive properties of relations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( AFTER 17819 relres $)
  $( NEW $)

  ${
    $d x y z A $.  $d x y z B $.
    $( Two ways of saying the identity relation restricted to the union of the
       domain and range of a relation is a subset of a relation.
       Generalization of ~ reflexg .  (Contributed by RP, 26-Sep-2020.) $)
    undmrnresiss $p |- ( ( _I |` ( dom A u. ran A ) ) C_ B
                 <-> A. x A. y ( x A y -> ( x B x /\ y B y ) ) ) $=
      ( vz cid wss wa wbr wi wal weq wex df-br bicomi 2albii bitri albii 3bitri
      wcel cdm crn cun cres cv resundi sseq1i unss cop wrel wb relres ssrel vex
      ax-mp eldm bitr3i anbi12ci opelresi 19.42v 3bitr4i imbi12i 19.23v ancomst
      ideq alcom impexp 19.21v equcom imbi1i breq2 equsalvw imbi2i elrn 3bitr2i
      alrot3 anbi12i 19.26-2 pm4.76 ) FCUAZCUBZUCUDZDGFVTUDZFWAUDZUCZDGWCDGZWDD
      GZHZAUEZBUEZCIZWIWIDIZWJWJDIZHJZBKAKZWBWEDFVTWAUFUGWCWDDUHWHWKWLJZBKZAKZW
      KWMJZBKAKZHWPWSHZBKAKWOWFWRWGWTWFWIEUEZUIZWCTZXCDTZJZEKAKZAELZWKHZBMZWIXB
      DIZJZEKAKZWRWCUJWFXGUKFVTULAEWCDUMUOXFXLAEXDXJXEXKWIVTTZXCFTZHXHWKBMZHXDX
      JXNXPXOXHBWICAUNUPXOWIXBFIXHWIXBFNWIXBEUNZVEUQURVTWIXBFXQUSXHWKBUTVAXKXEW
      IXBDNOVBPXMXIXKJZBKZEKZAKWRXLXSAEXSXLXIXKBVCOPXTWQAXTXREKZBKWQXREBVFYAWPB
      YAWKXHXKJZJZEKWKYBEKZJWPXRYCEXRWKXHHXKJYCXHWKXKVDWKXHXKVGQRWKYBEVHYDWLWKY
      DEALZXKJZEKWLYBYFEXHYEXKAEVIVJRXKWLEAXBWIWIDVKVLQVMSRQRQSWGWJXBUIZWDTZYGD
      TZJZEKBKZBELZWKHZAMZWJXBDIZJZEKBKZWTWDUJWGYKUKFWAULBEWDDUMUOYJYPBEYHYNYIY
      OWJWATZYGFTZHYLWKAMZHYHYNYRYTYSYLAWJCBUNVNYSWJXBFIYLWJXBFNWJXBXQVEUQURWAW
      JXBFXQUSYLWKAUTVAYOYIWJXBDNOVBPYQYMYOJZAKZEKBKUUAEKZBKAKWTYPUUBBEUUBYPYMY
      OAVCOPUUAABEVPUUCWSABUUCWKYLYOJZJZEKWKUUDEKZJWSUUAUUEEUUAWKYLHYOJUUEYLWKY
      OVDWKYLYOVGQRWKUUDEVHUUFWMWKUUFEBLZYOJZEKWMUUDUUHEYLUUGYOBEVIVJRYOWMEBXBW
      JWJDVKVLQVMSPVOSVQWPWSABVRXAWNABWKWLWMVSPVOVO $.
  $}

  ${
    $d x y A $.
    $( Two ways of saying a relation is reflexive over its domain and range.
       (Contributed by RP, 4-Aug-2020.) $)
    reflexg $p |- ( ( _I |` ( dom A u. ran A ) ) C_ A
                 <-> A. x A. y ( x A y -> ( x A x /\ y A y ) ) ) $=
      ( undmrnresiss ) ABCCD $.
  $}

  $( AFTER 18030 relcnv $)

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.
    $( A condition weaker than reflexivity.  (Contributed by RP,
       3-Aug-2020.) $)
    cnvssco $p |- ( `' A C_ `' ( B o. C )
                 <-> A. x A. y E. z ( x A y -> ( x C z /\ z B y ) ) ) $=
      ( cv cop ccnv wcel ccom wi wal wss wbr wex vex brcnv df-br bitr3i wa wrel
      alcom wb relcnv ssrel ax-mp 19.37v brco imbi12i bitri 2albii 3bitr4i ) BG
      ZAGZHZDIZJZUPEFKZIZJZLZAMBMZVBBMAMUQUTNZUOUNDOZUOCGZFOVFUNEOUAZLCPZBMAMVB
      BAUCUQUBVDVCUDDUEBAUQUTUFUGVHVBABVHVEVGCPZLVBVEVGCUHVEURVIVAVEUNUOUQOURUN
      UODBQZAQZRUNUOUQSTVIUOUNUSOZVACUOUNEFVKVJUIVLUNUOUTOVAUNUOUSVJVKRUNUOUTST
      TUJUKULUM $.
  $}

  ${
    $d x y z A $.
    $( Reflexive relations are subsets of their self-composition.  (Contributed
       by RP, 4-Aug-2020.) $)
    refimssco $p |- ( ( _I |` ( dom A u. ran A ) ) C_ A
                      -> `' A C_ `' ( A o. A ) ) $=
      ( vx vy vz cv wbr wa wal wex cid cdm crn cun cres wss ccnv ccom weq breq2
      wi breq1 anbi12d biimprd spimevw ex adantr com12 a2i 19.37v sylibr 2alimi
      reflexg cnvssco 3imtr4i ) BEZCEZAFZUOUOAFZUPUPAFZGZTZCHBHUQUODEZAFZVBUPAF
      ZGZTDIZCHBHJAKALMNAOAPAAQPOVAVFBCVAUQVEDIZTZVFUQUTVGUTUQVGURVHUSURUQVGURU
      QGZVEDBDBRZVEVIVJVCURVDUQVBUOUOASVBUOUPAUAUBUCUDUEUFUGUHUQVEDUIUJUKBCAULB
      CDAAAUMUN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  RP ADDTO: Basic properties of closures
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( AFTER 11682 sseq2 $)

  ${
    cleq2lem.b $e |- ( A = B -> ( ph <-> ps ) ) $.
    $( Equality implies bijection.  (Contributed by RP, 24-Jul-2020.) $)
    cleq2lem $p |- ( A = B -> ( ( R C_ A /\ ph ) <-> ( R C_ B /\ ps ) ) ) $=
      ( wceq wss sseq2 anbi12d ) CDGECHEDHABCDEIFJ $.
  $}

  ${
    $d x y X $.  $d x ps $.  $d y ph $.
    cbvcllem.y $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change of bound variable in class of supersets of a with a property.
       (Contributed by RP, 24-Jul-2020.) $)
    cbvcllem $p |- { x | ( X C_ x /\ ph ) } = { y | ( X C_ y /\ ps ) } $=
      ( cv wss wa cleq2lem cbvabv ) ECGZHAIEDGZHBICDABLMEFJK $.
  $}

  $( AFTER 14120 intss1 $)

  ${
    clublem.y $e |- ( ph -> Y e. _V ) $.
    clublem.sub $e |- ( x = Y -> ( ps <-> ch ) ) $.
    clublem.sup $e |- ( ph -> X C_ Y ) $.
    clublem.maj $e |- ( ph -> ch ) $.
    $d x ch $.  $d x X $.  $d x Y $.
    $( If a superset ` Y ` of ` X ` possesses the property parameterized in
       ` x ` in ` ps ` , then ` Y ` is a superset of the closure of that
       property for the set ` X ` .  (Contributed by RP, 23-Jul-2020.) $)
    clublem $p |- ( ph -> |^| { x | ( X C_ x /\ ps ) } C_ Y ) $=
      ( cv wss wa cab wcel cint cvv wi wb syl cleq2lem elab3g mpbir2and intss1
      a1d ) AFEDKZLBMZDNZOZUHPFLAUIEFLZCIJAUJCMZFQOZRUIUKSAULUKGUEUGUKDFQBCUFFE
      HUAUBTUCFUHUDT $.
  $}

  $( AFTER 14126 intss $)

  ${
    $d x ph $.
    clss2lem.1 $e |- ( ph -> ( ch -> ps ) ) $.
    $( The closure of a property is a superset of the closure of a less
       restrictive property.  (Contributed by RP, 24-Jul-2020.) $)
    clss2lem $p |- ( ph -> |^| { x | ( X C_ x /\ ps ) }
                             C_ |^| { x | ( X C_ x /\ ch ) } ) $=
      ( cv wss wa cab cint wal adantld alrimiv pm5.3 albii ss2ab bitr4i sylib
      wi intss syl ) AEDGHZCIZDJZUCBIZDJZHZUGKUEKHAUDBTZDLZUHAUIDACBUCFMNUJUDUF
      TZDLUHUIUKDUCCBOPUDUFDQRSUEUGUAUB $.
  $}

  $( AFTER 16287 dfid4 $)

  ${
    $d x y $.
    $( Definition of identity relation as the trivial closure.  (Contributed by
       RP, 26-Jul-2020.) $)
    dfid7 $p |- _I = ( x e. _V |-> |^| { y | ( x C_ y /\ T. ) } ) $=
      ( cid cvv cv cmpt wss wtru wa cab cint dfid4 ancom truan bitri inteqi vex
      abbii intmin2 eqtri mpteq2i eqtr4i ) CADAEZFADUCBEGZHIZBJZKZFALADUGUCUGUD
      BJZKUCUFUHUEUDBUEHUDIUDUDHMUDNORPBUCAQSTUAUB $.
  $}

  $( AFTER 17818 ssres2 $)

  ${
    $d x y z V $.  $d x z ph $.  $d x y ps $.  $d y ch $.  $d y th $.
    $d z ta $.
    mptrcllem.ex1 $e |- ( x e. V -> |^| { y | ( x C_ y /\ ( ph
                          /\ ( _I |` ( dom y u. ran y ) ) C_ y ) ) } e. _V ) $.
    mptrcllem.ex2 $e |- ( x e. V -> |^| { z | (
                                    ( x u. ( _I |` ( dom x u. ran x ) ) ) C_ z
                                    /\ ps ) } e. _V ) $.
    mptrcllem.hyp1 $e |- ( x e. V -> ch ) $.
    mptrcllem.hyp2 $e |- ( x e. V -> th ) $.
    mptrcllem.hyp3 $e |- ( x e. V -> ta ) $.
    mptrcllem.sub1 $e |- (
        y = |^| { z | ( ( x u. ( _I |` ( dom x u. ran x ) ) ) C_ z /\ ps ) } ->
        ( ph <-> ch ) ) $.
    mptrcllem.sub2 $e |- (
        y = |^| { z | ( ( x u. ( _I |` ( dom x u. ran x ) ) ) C_ z /\ ps ) } ->
        ( ( _I |` ( dom y u. ran y ) ) C_ y <-> th ) ) $.
    mptrcllem.sub3 $e |- (
        z = |^| { y | ( x C_ y
                        /\ ( ph /\ ( _I |` ( dom y u. ran y ) ) C_ y ) ) } ->
        ( ps <-> ta ) ) $.
    $( Show two versions of a closure with reflexive properties are equal.
       (Contributed by RP, 19-Oct-2020.) $)
    mptrcllem $p |- ( x e. V |-> |^| { y | ( x C_ y
        /\ ( ph /\ ( _I |` ( dom y u. ran y ) ) C_ y ) ) } ) = ( x e. V |->
        |^| { z | ( ( x u. ( _I |` ( dom x u. ran x ) ) ) C_ z /\ ps ) } ) $=
      ( cv wss wa cid cdm crn cun cres cab cint wcel wceq anbi12d wi wal unssad
      id adantr a1i alrimiv ssintab sylibr jca clublem simpl dmss unss12 ssres2
      rnss 3syl simprr sstrd unss imbitrdi eqssd mpteq2ia ) FIFRZGRZSZAUAVOUBZV
      OUCZUDZUEZVOSZTZTZGUFUGZVNUAVNUBZVNUCZUDZUEZUDZHRZSZBTZHUFUGZVNIUHZWDWMWN
      WBCDTGVNWMKVOWMUIACWADOPUJWNWLVNWJSZUKZHULVNWMSWNWPHWPWNWKWOBWKVNWHWJWKUN
      UMUOUPUQWLHVNURUSWNCDLMUTVAWNBEHWIWDJQWNWCWIVOSZUKZGULWIWDSWNWRGWNWCVPWHV
      OSZTZWQWCWTUKWNWCVPWSVPWBVBWCWHVTVOVPWHVTSZWBVPWEVQSZWFVRSZTWGVSSXAVPXBXC
      VNVOVCVNVOVFUTWEVQWFVRVDWGVSUAVEVGUOVPAWAVHVIUTUPVNWHVOVJVKUQWCGWIURUSNVA
      VLVM $.
  $}

  $( AFTER 18046 cotr $)

  ${
    $d u v w ph $.  $d u v w x $.
    cotrintab.min $e |- ( ph -> ( x o. x ) C_ x ) $.
    $( The intersection of a class is a transitive relation if membership in
       the class implies the member is a transitive relation.  (Contributed by
       RP, 28-Oct-2020.) $)
    cotrintab $p |- ( |^| { x | ph } o. |^| { x | ph } ) C_ |^| { x | ph } $=
      ( vu vw vv ccom cv wbr wa wi wal cop wcel opex elintab df-br imbi2i albii
      3bitr4i cab cint wss pm3.43 biimpi 2sp sps sylcom alanimi anbi12i 3imtr4i
      cotr 3syl gen2 mpgbir ) ABUAUBZUPGUPUCDHZEHZUPIZURFHZUPIZJZUQUTUPIZKZFLEL
      DDEFUPULVDEFAUQURBHZIZKZBLZAURUTVEIZKZBLZJAUQUTVEIZKZBLZVBVCVGVJVMBVGVJJA
      VFVIJZVLAVFVIUDAVEVEGVEUCZVOVLKZFLELZDLZVQCVPVSDEFVEULUEVRVQDVQEFUFUGUMUH
      UIUSVHVAVKUQURMZUPNAVTVENZKZBLUSVHABVTUQUROPUQURUPQVGWBBVFWAAUQURVEQRSTUR
      UTMZUPNAWCVENZKZBLVAVKABWCURUTOPURUTUPQVJWEBVIWDAURUTVEQRSTUJUQUTMZUPNAWF
      VENZKZBLVCVNABWFUQUTOPUQUTUPQVMWHBVLWGAUQUTVEQRSTUKUNUO $.
  $}

  $( AFTER 23464 rnexg $)

  ${
    $d x A $.
    rclexi.1 $e |- A e. V $.
    $( The reflexive closure of a set exists.  (Contributed by RP,
       27-Oct-2020.) $)
    rclexi $p |- |^| { x | ( A C_ x
                             /\ ( _I |` ( dom x u. ran x ) ) C_ x ) }
                 e. _V $=
      ( cid cdm crn cun cres wss cvv wcel ssun1 uneq2i wceq ssequn1 mpbi 3eqtri
      wa ssun2 cv cab cint dmun dmresi rnun uneq12i unidm eqtri reseq2i eqsstri
      rnresi wex elexi dmexg rnexg unexd resiexd unex dmeq rneq uneq12d reseq2d
      ax-mp id sseq12d cleq2lem spcev intexab sylib mp2an ) BBEBFZBGZHZIZHZJZEV
      PFZVPGZHZIZVPJZBAUAZJEWCFZWCGZHZIZWCJZSZAUBUCKLZBVOMWAVOVPVTVNEVTVNVNHVNV
      RVNVSVNVRVLVOFZHVLVNHZVNBVOUDWKVNVLVNUENVLVNJWLVNOVLVMMVLVNPQRVSVMVOGZHVM
      VNHZVNBVOUFWMVNVMVNULNVMVNJWNVNOVMVLTVMVNPQRUGVNUHUIUJVOBTUKVQWBSZWIAUMWJ
      WIWOAVPBVOBCDUNBCLZVOKLDWPVNKWPVLVMKKBCUOBCUPUQURVDUSWHWBWCVPBWCVPOZWGWAW
      CVPWQWFVTEWQWDVRWEVSWCVPUTWCVPVAVBVCWQVEVFVGVHWIAVIVJVK $.
  $}

  $( Existence of relation implies existence of union with Cartesian product of
     domain and range.  (Contributed by RP, 1-Nov-2020.) $)
  rtrclexlem $p |- ( R e. V ->
               ( R u. ( ( dom R u. ran R ) X. ( dom R u. ran R ) ) ) e. _V ) $=
    ( wcel cdm crn cun cxp cvv dmexg rnexg unexd sqxpexg syl unexg mpdan ) ABCZ
    ADZAEZFZSGZHCZATFHCPSHCUAPQRHHABIABJKSHLMATBHNO $.

  ${
    $d x A $.
    $( The reflexive-transitive closure of a set exists.  (Contributed by RP,
       1-Nov-2020.) $)
    rtrclex $p |- ( A e. _V <-> |^| { x | ( A C_ x /\ ( ( x o. x ) C_ x
                               /\ ( _I |` ( dom x u. ran x ) ) C_ x ) ) }
                   e. _V ) $=
      ( cvv wcel wss ccom cid cdm crn cun cres wa cxp cossxp xpss12 mp2an sstri
      unssi eqsstri wceq wex cab cint ssun1 coundir coundi dmxpss rnxpss xpidtr
      cv ssun2 dmun dmxpid uneq2i ssequn1 mpbi 3eqtri rnun rnxpid uneq12i unidm
      eqtri reseq2i idssxp pm3.2i rtrclexlem wi id coeq12d sseq12d dmeq uneq12d
      rneq reseq2d anbi12d cleq2lem biimprd adantl spcimedv mp2ani exsimpl ssex
      vex exlimiv syl impbii intexab bitri ) BCDZBAUJZEZWJWJFZWJEZGWJHZWJIZJZKZ
      WJEZLZLZAUAZWTAUBUCCDWIXAWIBBBHZBIZJZXDMZJZEZXFXFFZXFEZGXFHZXFIZJZKZXFEZL
      ZXABXEUDXIXNXHXEXFXHBXFFZXEXFFZJXEBXEXFUEXPXQXEXPBBFZBXEFZJXEBBXEUFXRXSXE
      XRXBXCMZXEBBNXBXDEZXCXDEZXTXEEXBXCUDZXCXBUKZXBXDXCXDOPQXSXEHZXCMZXEBXENYE
      XDEYBYFXEEXDXDUGYDYEXDXCXDOPQRSXQXEBFZXEXEFZJXEXEBXEUFYGYHXEYGXBXEIZMZXEX
      EBNYAYIXDEYJXEEYCXDXDUHXBXDYIXDOPQXDUIRSRSXEBUKZQXMXEXFXMGXDKXEXLXDGXLXDX
      DJXDXJXDXKXDXJXBYEJXBXDJZXDBXEULYEXDXBXDUMUNYAYLXDTYCXBXDUOUPUQXKXCYIJXCX
      DJZXDBXEURYIXDXCXDUSUNYBYMXDTYDXCXDUOUPUQUTXDVAVBVCXDVDSYKQVEWIWTXGXOLZAX
      FCBCVFWJXFTZYNWTVGWIYOWTYNWSXOWJXFBYOWMXIWRXNYOWLXHWJXFYOWJXFWJXFYOVHZYPV
      IYPVJYOWQXMWJXFYOWPXLGYOWNXJWOXKWJXFVKWJXFVMVLVNYPVJVOVPVQVRVSVTXAWKAUAWI
      WKWSAWAWKWIABWJAWCWBWDWEWFWTAWGWH $.
  $}

  ${
    trclubgNEW.rex $e |- ( ph -> R e. _V ) $.
    $d x R $.
    $( If a relation exists then the transitive closure has an upper bound.
       (Contributed by RP, 24-Jul-2020.) $)
    trclubgNEW $p |- ( ph -> |^| { x | ( R C_ x /\ ( x o. x ) C_ x ) }
                              C_ ( R u. ( dom R X. ran R ) ) ) $=
      ( cv ccom wss cxp cun cvv wcel syl wceq a1i 3sstr3g ssequn1 sylib eqsstrd
      ccnv eqsstrid cdm dmexd rnexg xpexd unexd coeq12d sseq12d ssun1 cnvssrndm
      crn id coundi cnvss coss2 cocnvcnv2 cnvxp coeq2i coundir cocnvcnv1 coeq1i
      coss1 xptrrel ssun2 sstri mp1i clublem ) ABEZVGFZVGGCCUAZCUJZHZIZVLFZVLGZ
      BCVLACVKJJDAVIVJJJACJDUBACJKVJJKDCJUCLUDUEVGVLMZVHVMVGVLVOVGVLVGVLVOUKZVP
      UFVPUGCVLGACVKUHNCSZVJVIHZGZVNACUIVSVMVLCFZVLVKFZIZVLVLCVKULVSWBWAVLVSVTW
      AGWBWAMVSVLVQSZFZVLVRSZFZVTWAVSWCWEGZWDWFGVQVRUMZWCWEVLUNLVLCUOWEVKVLVJVI
      UPZUQOVTWAPQVSWACVKFZVKVKFZIZVLCVKVKURVSWLWKVLVSWJWKGWLWKMVSWCVKFZWEVKFZW
      JWKVSWGWMWNGWHWCWEVKVALCVKUSWEVKVKWIUTOWJWKPQWKVLGVSWKVKVLVIVJVBVKCVCVDNR
      TRTVEVF $.
  $}

  ${
    trclubNEW.rex $e |- ( ph -> R e. _V ) $.
    trclubNEW.rel $e |- ( ph -> Rel R ) $.
    $d x R $.
    $( If a relation exists then the transitive closure has an upper bound.
       (Contributed by RP, 24-Jul-2020.) $)
    trclubNEW $p |- ( ph -> |^| { x | ( R C_ x /\ ( x o. x ) C_ x ) }
                              C_ ( dom R X. ran R ) ) $=
      ( cv wss ccom cab cint cdm crn cxp cun trclubgNEW wceq wrel relssdmrn syl
      wa ssequn1 sylib sseqtrd ) ACBFZGUDUDHUDGTBIJCCKCLMZNZUEABCDOACUEGZUFUEPA
      CQUGECRSCUEUAUBUC $.
  $}

  $( AFTER 23468 rnex $)

  ${
    $d x A $.
    trclexi.1 $e |- A e. V $.
    $( The transitive closure of a set exists.  (Contributed by RP,
       27-Oct-2020.) $)
    trclexi $p |- |^| { x | ( A C_ x /\ ( x o. x ) C_ x ) } e. _V $=
      ( cdm crn cxp cun wss ccom cv wa cab cint coundi cossxp ax-mp sstri unssi
      eqsstri cvv wcel ssun1 coundir dmxpss xpss1 xpss2 xptrrel ssun2 wex elexi
      rnxpss dmex rnex xpex unex trcleq2lem spcev intexab sylib mp2an ) BBBEZBF
      ZGZHZIZVEVEJZVEIZBAKZIVIVIJVIILZAMNUAUBZBVDUCVGVDVEVGBVEJZVDVEJZHVDBVDVEU
      DVLVMVDVLBBJZBVDJZHVDBBVDOVNVOVDBBPVOVDEZVCGZVDBVDPVPVBIVQVDIVBVCUEVPVBVC
      UFQRSTVMVDBJZVDVDJZHVDVDBVDOVRVSVDVRVBVDFZGZVDVDBPVTVCIWAVDIVBVCULVTVCVBU
      GQRVBVCUHSTSTVDBUIRVFVHLZVJAUJVKVJWBAVEBVDBCDUKZVBVCBWCUMBWCUNUOUPVIVEBUQ
      URVJAUSUTVA $.
  $}

  ${
    $d x A $.
    rtrclexi.1 $e |- A e. V $.
    $( The reflexive-transitive closure of a set exists.  (Contributed by RP,
       27-Oct-2020.) $)
    rtrclexi $p |- |^| { x | ( A C_ x /\ ( ( x o. x ) C_ x
                               /\ ( _I |` ( dom x u. ran x ) ) C_ x ) ) }
                   e. _V $=
      ( cdm crn cun cxp wss ccom cid cres ssun1 cossxp xpss12 mp2an sstri unssi
      wa eqsstri cv cab cint cvv wcel coundir coundi ssun2 dmxpss rnxpss xpidtr
      dmun rnun ssres2 ax-mp idssxp id wex elexi dmex rnex unex coeq12d sseq12d
      xpex wceq dmeq rneq uneq12d reseq2d anbi12d cleq2lem spcev intexab sylib
      ) BBBEZBFZGZVRHZGZIZVTVTJZVTIZKVTEZVTFZGZLZVTIZSZBAUAZIWJWJJZWJIZKWJEZWJF
      ZGZLZWJIZSZSZAUBUCUDUEZBVSMWCWHWIWBVSVTWBBVTJZVSVTJZGVSBVSVTUFXAXBVSXABBJ
      ZBVSJZGVSBBVSUGXCXDVSXCVPVQHZVSBBNVPVRIZVQVRIZXEVSIVPVQMZVQVPUHZVPVRVQVRO
      PQXDVSEZVQHZVSBVSNXJVRIXGXKVSIVRVRUIZXIXJVRVQVROPQRTXBVSBJZVSVSJZGVSVSBVS
      UGXMXNVSXMVPVSFZHZVSVSBNXFXOVRIXPVSIXHVRVRUJZVPVRXOVROPQVRUKRTRTVSBUHZQWG
      VSVTWGKVRLZVSWFVRIWGXSIWDWEVRWDVPXJGVRBVSULVPXJVRXHXLRTWEVQXOGVRBVSUMVQXO
      VRXIXQRTRWFVRKUNUOVRUPQXRQWIUQPWAWISZWSAURWTWSXTAVTBVSBCDUSZVRVRVPVQBYAUT
      BYAVAVBZYBVEVBWRWIWJVTBWJVTVFZWLWCWQWHYCWKWBWJVTYCWJVTWJVTYCUQZYDVCYDVDYC
      WPWGWJVTYCWOWFKYCWMWDWNWEWJVTVGWJVTVHVIVJYDVDVKVLVMWSAVNVOP $.
  $}

  $( AFTER 23510 cnvexg $)

  ${
    clrellem.y $e |- ( ph -> Y e. _V ) $.
    clrellem.rel $e |- ( ph -> Rel X ) $.
    clrellem.sub $e |- ( x = `' `' Y -> ( ps <-> ch ) ) $.
    clrellem.sup $e |- ( ph -> X C_ Y ) $.
    clrellem.maj $e |- ( ph -> ch ) $.
    $d x y X $.  $d x Y $.  $d x ph $.  $d y ps $.  $d x ch $.
    $( When the property ` ps ` holds for a relation substituted for ` x ` ,
       then the closure on that property is a relation if the base set is a
       relation.  (Contributed by RP, 30-Jul-2020.) $)
    clrellem $p |- ( ph -> Rel |^| { x | ( X C_ x /\ ps ) } ) $=
      ( vy cv wss wa wrel ccnv cvv wcel 3syl wrex cint cnvexg wceq dfrel2 sylib
      wex cab cnvss eqsstrrd relcnv jca31 cleq2lem releq anbi12d spcedv biimpri
      a1i rexab2 relint ) AEDMZNBOZVAPZOZDUGZLMZPZLVBDUHZUAZVHUBPAVDEFQZQZNZCOZ
      VKPZODRVKAFRSVJRSVKRSGFRUCVJRUCTAVLCVNAEEQZQZVKAEPVPEUDHEUEUFAEFNVOVJNVPV
      KNJEFUIVOVJUITUJKVNAVJUKURULVAVKUDVBVMVCVNBCVAVKEIUMVAVKUNUOUPVIVEVBVGVCL
      DVFVAUNUSUQLVHUTT $.
  $}

  $( AFTER 23513 cnvex $)

  ${
    $d x A $.  $d x y z X $.  $d x y z ph $.  $d y z ps $.  $d x z ch $.
    $d x th $.
    clcnvlem.sub1 $e |- ( ( ph /\ x = ( `' y u. ( X \ `' `' X ) ) )
                             -> ( ch -> ps ) ) $.
    clcnvlem.sub2 $e |- ( ( ph /\ y = `' x ) -> ( ps -> ch ) ) $.
    clcnvlem.sub3 $e |- ( x = A -> ( ps <-> th ) ) $.
    clcnvlem.ssub $e |- ( ph -> X C_ A ) $.
    clcnvlem.ubex $e |- ( ph -> A e. _V ) $.
    clcnvlem.clex $e |- ( ph -> th ) $.
    $( When ` A ` , an upper bound of the closure, exists and certain
       substitutions hold the converse of the closure is equal to the closure
       of the converse.  (Contributed by RP, 18-Oct-2020.) $)
    clcnvlem $p |- ( ph -> `' |^| { x | ( X C_ x /\ ps ) }
                              = |^| { y | ( `' X C_ y /\ ch ) } ) $=
      ( vz wss wa ccnv wceq cvv cv cab cint wex cxp cpw crab cleq2lem cnvintabd
      jca spcedv wcel df-rab wrel exsimpl relcnv releq mpbiri exlimiv syl sylib
      df-rel velpw bicomi pm4.71ri abbii eqtri inteqi a1i vex cnvex cdif difexd
      cun ssexd unexg sylancr wi cin inundif sseq1i biimpi unssad relin2 dfrel2
      cnvun ax-mp mpbi cnvss eqsstrrid ssid unss12 sylancl cnveq sseq1d 3imtr3d
      sseq1 sseq2 imbitrrid adantl anim12d cnvnonrel 0ss eqsstri ssequn2 eqtr2i
      c0 eqtr4id jctild spcimedv adantlr wb eqeq1 anbi1d exbidv ad2antlr mpbird
      imp ex cnvcnvss intabssd weq eqtr syl5 impl expimpd exlimdv eqssd 3eqtrd
      ) AHEUAZPZBQZEUBUCROUAZYJRZSZYLQZEUDZOTTUEZUFZUGZUCZYQOUBZUCZHRZFUAZPZCQZ
      FUBUCZAYLEOAYLHGPZDQETGMAUUIDLNUJBDYJGHKUHUKUIUUAUUCSAYTUUBYTYMYSULZYQQZO
      UBUUBYQOYSUMUUKYQOYQUUKYQUUJYQYMYRPZUUJYQYMUNZUULYQYOEUDUUMYOYLEUOYOUUMEY
      OUUMYNUNYJUPYMYNUQURUSUTYMVBVAUUJUULOYRVCVDVAVEVDVFVGVHVIAUUCUUHAYQUUGOFU
      UERZRZTUUOTULAUUNUUEFVJVKZVKVIAYMUUOSZQZUUGYQUURUUGQYQUUOYNSZYLQZEUDZAUUG
      UVAUUQAUUGUVAAUUTUUGEUUNHUUDRZVLZVNZTAUUNTULUVCTULUVDTULUUPAHUVBTAHGTMLVO
      VMUUNUVCTTVPVQAYJUVDSZQZUUGYLUUSUVFUUFYKCBUVEUUFYKVRAUUFYKUVEHUVDPZHUVBVS
      ZUVCVNZHSZUUFUVGVRHUVBVTUVJUVIRZUUEPZUVIUVDPZUUFUVGUVLUVMVRUVJUVLUVHUUNPZ
      UVCUVCPUVMUVLUVHRZUUEPZUVNUVLUVOUVCRZUUEUVLUVOUVQVNZUUEPUVKUVRUUEUVHUVCWF
      WAWBWCUVPUVHUVORZUUNUVHUNZUVSUVHSUVBUNUVTUUDUPHUVBWDWGUVHWEWHUVOUUEWIWJUT
      UVCWKUVHUUNUVCUVCWLWMVIUVJUVKUUDUUEUVIHWNWOUVIHUVDWQWPWGYJUVDHWRWSWTIXAUV
      EUUSAUVEUUOUVDRZYNUWAUUOUVQVNZUUOUUNUVCWFUVQUUOPUWBUUOSUVQXGUUOHXBUUOXCXD
      UVQUUOXEWHXFYJUVDWNXHWTXIXJXRXKUUQYQUVAXLAUUGUUQYPUUTEUUQYOUUSYLYMUUOYNXM
      XNXOXPXQXSUUOUUEPAUUEXTVIYAAUUGYQFOYMTYMTULAOVJVIAFOYBZQZYPUUGEUWDYOYLUUG
      AUWCYOYLUUGVRZUWCYOQUUEYNSZAUWEUUEYMYNYCAUWFUWEAUWFQYKUUFBCUWFYKUUFVRAYKU
      UFUWFUUDYNPHYJWIUUEYNUUDWRWSWTJXAXSYDYEYFYGYMYMPAYMWKVIYAYHYI $.
  $}

  ${
    $d x y V $.  $d x y X $.
    $( The converse of the trivial closure is equal to the closure of the
       converse.  (Contributed by RP, 18-Oct-2020.) $)
    cnvtrucl0 $p |- ( X e. V -> `' |^| { x | ( X C_ x /\ T. ) }
                              = |^| { y | ( `' X C_ y /\ T. ) } ) $=
      ( wcel wtru cv ccnv cdif cun wceq wa idd biidd ssidd elex trud clcnvlem )
      DCEZFFFABDDSAGZBGZHDDHHIJKLFMSUATHKLFMTDKFNSDODCPSQR $.
  $}

  ${
    $d x y V $.  $d x y X $.
    $( The converse of the reflexive closure is equal to the closure of the
       converse.  (Contributed by RP, 18-Oct-2020.) $)
    cnvrcl0 $p |- ( X e. V -> `' |^| { x | ( X C_ x
                   /\ ( _I |` ( dom x u. ran x ) ) C_ x ) }
                              = |^| { y | ( `' X C_ y
                   /\ ( _I |` ( dom y u. ran y ) ) C_ y ) } ) $=
      ( wcel cid cdm crn cun cres wss ccnv wceq c0 df-rn eqsstri dfdm4 dmeq cvv
      ssun1 cv cdif wi cnvresid cnvnonrel cnv0 eqtr4i dmeqi 3eqtr4i 0ss ssequn2
      rnssi mpbi rnun 3eqtr4ri rneqi dmss ax-mp uneq12i equncomi reseq2i eqtr2i
      dmun eqsstrid sstrdi rneq uneq12d reseq2d id sseq12d imbitrrid adantl a1i
      cnvss dmexg rnexg unexd resiexd unexg mpdan wa resdmss unssi ssun2 rnresi
      eqimssi pm3.2i unss ssres2 sylbi ssun4 mp2b clcnvlem ) DCEZFAUAZGZWOHZIZJ
      ZWOKZFBUAZGZXAHZIZJZXAKZFDFDGZDHZIZJZIZGZXKHZIZJZXKKZABXKDWOXALZDDLLUBZIZ
      MZXFWTUCWNXFWTXTFXSGZXSHZIZJZXSKXFYDXQXSXFYDXELZXQYEXEYDXDUDXDYCFXDYBYAXB
      YBXCYAXQHZXRHZIZYFYBXBYGYFKYHYFMYGNHZYFXRLZGNLZGYGYIYJYKYJNYKDUEUFUGZUHXR
      ONOUINXQXQUJZULPYGYFUKUMXQXRUNXAQUOXQGZXRGZIZYNYAXCYOYNKYPYNMYONGZYNYJHYK
      HYOYQYJYKYLUPXRQNQUINXQKYQYNKYMNXQUQURPYOYNUKUMXQXRVCXAOUOUSUTVAVBXEXAVNV
      DXQXRTVEXTWSYDWOXSXTWRYCFXTWPYAWQYBWOXSRWOXSVFVGVHXTVIVJVKVLXAWOLZMZWTXFU
      CWNWTXFYSFYRGZYRHZIZJZYRKWTUUCWSLZYRUUDWSUUCWRUDWRUUBFWRUUAYTWPUUAWQYTWOQ
      WOOUSUTVAVBWSWOVNVDYSXEUUCXAYRYSXDUUBFYSXBYTXCUUAXAYRRXAYRVFVGVHYSVIVJVKV
      LWOXKMZWSXOWOXKUUEWRXNFUUEWPXLWQXMWOXKRWOXKVFVGVHUUEVIVJDXKKWNDXJTVMWNXJS
      EXKSEWNXISWNXGXHSSDCVODCVPVQVRDXJCSVSVTXPWNXLXIKZXMXIKZWAZXOXJKZXPUUFUUGX
      LXGXJGZIXIDXJVCXGUUJXIXGXHTFXIWBWCPXMXHXJHZIXIDXJUNXHUUKXIXHXGWDUUKXIXIWE
      WFWCPWGUUHXNXIKUUIXLXMXIWHXNXIFWIWJXOXJDWKWLVMWM $.
  $}

  ${
    $d x y V $.  $d x y X $.
    $( The converse of the transitive closure is equal to the closure of the
       converse.  (Contributed by RP, 18-Oct-2020.) $)
    cnvtrcl0 $p |- ( X e. V
                   -> `' |^| { x | ( X C_ x /\ ( x o. x ) C_ x ) }
                    = |^| { y | ( `' X C_ y /\ ( y o. y ) C_ y ) } ) $=
      ( cv ccom wss cdm cxp cun ccnv wceq coundi eqsstri coeq12d sseq12d cossxp
      unssi id sstri wcel crn cdif cnvco cnvss eqsstrrid coundir ssid cononrel2
      wi c0 cononrel1 sstrid ssun3 3syl imbitrrid adantl ssun1 trclexlem dmxpss
      0ss a1i xpss1 ax-mp rnxpss xpss2 xptrrel ssun2 clcnvlem ) DCUAZAEZVKFZVKG
      ZBEZVNFZVNGZDDHZDUBZIZJZVTFZVTGZABVTDVKVNKZDDKKUCZJZLZVPVMUJVJVPVMWFWEWEF
      ZWEGZVPWCWCFZWCGZWGWCGWHVPWIVOKWCVNVNUDVOVNUEUFWJWGWIWCWGWCWEFZWDWEFZJWIW
      CWDWEUGWKWLWIWKWIWCWDFZJWIWCWCWDMWIWMWIWIUHWMUKWIWCDUIWIVAZNRNWLUKWIDWEUL
      WNNRNWJSUMWGWCWDUNUOWFVLWGVKWEWFVKWEVKWEWFSZWOOWOPUPUQVNVKKZLZVMVPUJVJVMV
      PWQWPWPFZWPGVMWRVLKWPVKVKUDVLVKUEUFWQVOWRVNWPWQVNWPVNWPWQSZWSOWSPUPUQVKVT
      LZVLWAVKVTWTVKVTVKVTWTSZXAOXAPDVTGVJDVSURVBDCUSWBVJWAVSVTWADVTFZVSVTFZJVS
      DVSVTUGXBXCVSXBDDFZDVSFZJVSDDVSMXDXEVSDDQXEVSHZVRIZVSDVSQXFVQGXGVSGVQVRUT
      XFVQVRVCVDTRNXCVSDFZVSVSFZJVSVSDVSMXHXIVSXHVQVSUBZIZVSVSDQXJVRGXKVSGVQVRV
      EXJVRVQVFVDTVQVRVGRNRNVSDVHTVBVI $.
  $}

  $( AFTER 41062 trclubg $)

  ${
    $d x X $.
    $( The domain of the transitive closure is equal to the domain of its base
       relation.  (Contributed by RP, 1-Nov-2020.) $)
    dmtrcl $p |- ( X e. V ->
      dom |^| { x | ( X C_ x /\ ( x o. x ) C_ x ) } = dom X ) $=
      ( wcel cv wss ccom wa cab cint cdm crn cxp cun trclubg dmss syl dmun wceq
      dmxpss ssequn2 mpbi eqtri sseqtrdi ssmin mp1i eqssd ) CBDZCAEZFUIUIGUIFZH
      AIJZKZCKZUHULCUMCLZMZNZKZUMUHUKUPFULUQFCBAOUKUPPQUQUMUOKZNZUMCUORURUMFUSU
      MSUMUNTURUMUAUBUCUDCUKFUMULFUHUJACUECUKPUFUG $.
  $}

  ${
    $d x X $.
    $( The range of the transitive closure is equal to the range of its base
       relation.  (Contributed by RP, 1-Nov-2020.) $)
    rntrcl $p |- ( X e. V ->
      ran |^| { x | ( X C_ x /\ ( x o. x ) C_ x ) } = ran X ) $=
      ( wcel cv wss ccom wa cab cint crn cdm cxp cun trclubg rnss syl rnun wceq
      rnxpss ssequn2 mpbi eqtri sseqtrdi ssmin mp1i eqssd ) CBDZCAEZFUIUIGUIFZH
      AIJZKZCKZUHULCCLZUMMZNZKZUMUHUKUPFULUQFCBAOUKUPPQUQUMUOKZNZUMCUORURUMFUSU
      MSUNUMTURUMUAUBUCUDCUKFUMULFUHUJACUECUKPUFUG $.
  $}

  ${
    $d x y z $.
    $( Definition of reflexive-transitive closure as a standard closure.
       (Contributed by RP, 1-Nov-2020.) $)
    dfrtrcl5 $p |- t* = ( x e. _V |->
                           |^| { y | ( x C_ y
                                       /\ ( ( _I |` ( dom y u. ran y ) ) C_ y
                                       /\ ( y o. y ) C_ y ) ) } ) $=
      ( vz cvv cid cdm crn cun cres wss ccom cab cint cmpt wcel a1i wceq 3eqtri
      cv wa crtcl w3a df-rtrcl ancom anbi2i abbii inteqi mpteq2i rtrclexi dmexg
      vex rnexg unexd resiexg mp2b unex trclexi simpr cotrintab dmex rnex unexg
      resiexd mp2an dmtrcl ax-mp dmun dmresi uneq2i ssun1 ssequn1 rntrcl rnresi
      mpbi eqtri rnun ssun2 uneq12i unidm reseq2i ssmin sstri eqsstri simprl id
      coeq12d sseq12d dmeq uneq12d reseq2d mptrcllem df-3an bitri anbi1i bitr2i
      rneq unss eqtr4i ) UAADEASZFZWSGZHZIZCSZJZWSXDJZXDXDKZXDJZUBZCLZMZNZADWSB
      SZJZEXMFZXMGZHZIZXMJZXMXMKZXMJZTZTZBLZMZNZACUCYFADXNYAXSTZTZBLZMZNADWSXCH
      ZXDJZXHTZCLZMZNXLADYEYJYDYIYCYHBYBYGXNXSYAUDUEUFUGUHYAXHYOYOKZYOJZEYOFZYO
      GZHZIZYOJZYJYJKZYJJZABCDYJDOWSDOZBWSDAUKZUIPYODOUUECYKDWSXCUUFUUEXBDOXCDO
      ZUUFUUEWTXADDWSDUJWSDULUMXBDUNUOUPUQPYQUUEYMCYLXHURUSPUUBUUEUUAXCYOYTXBEY
      TXBXBHXBYRXBYSXBYRYKFZXBYKDOZYRUUHQWSXCUUFWTDOZXADOZUUGWSUUFUTWSUUFVAUUJU
      UKTXBDWTXADDVBVCVDUPZCDYKVEVFUUHWTXCFZHWTXBHZXBWSXCVGUUMXBWTXBVHVIWTXBJUU
      NXBQWTXAVJWTXBVKVNRVOYSYKGZXBUUIYSUUOQUULCDYKVLVFUUOXAXCGZHXAXBHZXBWSXCVP
      UUPXBXAXBVMVIXAXBJUUQXBQXAWTVQXAXBVKVNRVOVRXBVSVOVTXCYKYOXCWSVQXHCYKWAWBW
      CPUUDUUEYHBXNYAXSWDUSPXMYOQZXTYPXMYOUURXMYOXMYOUURWEZUUSWFUUSWGUURXRUUAXM
      YOUURXQYTEUURXOYRXPYSXMYOWHXMYOWPWIWJUUSWGXDYJQZXGUUCXDYJUUTXDYJXDYJUUTWE
      ZUVAWFUVAWGWKADYOXKYNXJYMXICXIXEXFTZXHTYMXEXFXHWLUVBYLXHUVBXFXETYLXEXFUDW
      SXCXDWQWMWNWOUFUGUHRWR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  RP REPLACE: Definitions and basic properties of transitive closures
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Equality implies bijection.  (Contributed by RP, 5-May-2020.)
     (Proof modification is discouraged.) $)
  trcleq2lemRP $p |- ( A = B -> ( ( R C_ A /\ ( A o. A ) C_ A ) <->
                                ( R C_ B /\ ( B o. B ) C_ B ) ) ) $=
    ( ccom wss wceq id coeq12d sseq12d cleq2lem ) AADZAEBBDZBEABCABFZKLABMABABM
    GZNHNIJ $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Additions for square root; absolute value
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  This is based on the observation that the real and imaginary parts of a
  complex number can be calculated from the number's absolute and real part and
  the sign of its imaginary part.

  <HTML>
  Formalization of the formula in ~ sqrtcval was motivated by a short
  <A HREF="https://www.youtube.com/watch?v=QAhWTQ4Ravw">Michael Penn video</A>.
  </HTML>

$)

  $( Not before: recld $)

  ${
    sqrtcvallem1.1 $e |- ( ph -> A e. CC ) $.

    $d A x $.
    $( Two ways of saying a complex number does not lie on the positive real
       axis.  Lemma for ~ sqrtcval .  (Contributed by RP, 17-May-2024.) $)
    sqrtcvallem1 $p |- ( ph -> ( ( ( Im ` A ) = 0 -> ( Re ` A ) <_ 0 ) <->
                                    -. A e. RR+ ) ) $=
      ( vx cc crp wcel wn wa cfv cc0 wceq cre wbr wb a1i cr crab clt wo cim cle
      cdif wi eldif cv cun imor biantrurd reim0b syl notbid eleq1 elrab 3bitr4d
      bicomd recld 0red lenltd fveq2 breq2d orbi12d bitrid elun ianor elrp rere
      bicomi pm5.32i bitri xchbinxr rabbii unrab dfdif2 3eqtr4i eleq2d 3bitr2d
      ) ABEFUCZGZBEGZBFGHZIZBUAJKLZBMJZKUBNZUDZWAVSWBOABEFUEPAWFBDUFZQGZHZDERZG
      ZBKWGMJZSNZHZDERZGZTZBWJWOUGZGZVSWFWCHZWETAWQWCWEUHAWTWKWEWPABQGZHZVTXBIZ
      WTWKAVTXBCUIAXBWTAXAWCAVTXAWCOCBUJUKULUPWKXCOAWIXBDBEWGBLZWHXAWGBQUMULUNP
      UOAKWDSNZHZVTXFIZWEWPAVTXFCUIAWDKABCUQAURUSWPXGOAWNXFDBEXDWMXEXDWLWDKSWGB
      MUTVAULUNPUOVBVCWSWQOABWJWOVDPAWRVRBWRVRLAWIWNTZDERWGFGZHZDERWRVRXHXJDEXH
      WHWMIZXIXKHXHWHWMVEVHXIWHKWGSNZIXKWGVFWHXLWMWHWMXLWHWLWGKSWGVGVAUPVIVJVKV
      LWIWNDEVMDEFVNVOPVPVQAVTWACUIUO $.
  $}

  $( Not before absnid: $)

  $( Alternate expression for the absolute value of a real number.  Lemma for
     ~ sqrtcval .  (Contributed by RP, 11-May-2024.) $)
  reabsifneg $p |- ( A e. RR -> ( abs ` A ) = if ( A < 0 , -u A , A ) ) $=
    ( cr wcel cc0 clt wbr cneg cif cabs cfv wa cle wceq wi ltle mpan2 imdistani
    0re absnid eqcomd syl wn 0red id lenltd bicomd absid sylbida ifeqda ) ABCZA
    DEFZAGZAHAIJZUJUKULAUMUJUKKZUMULUNUJADLFZKUMULMUJUKUOUJDBCUKUONRADOPQASUATU
    JUKUBZKUMAUJUPDALFZUMAMUJUQUPUJDAUJUCUJUDUEUFAUGUHTUIT $.

  $( Alternate expression for the absolute value of a real number.
     (Contributed by RP, 11-May-2024.) $)
  reabsifnpos $p |- ( A e. RR -> ( abs ` A ) = if ( A <_ 0 , -u A , A ) ) $=
    ( cr wcel cc0 cle wbr cneg cif cabs cfv wa absnid eqcomd wn wceq wi 0re clt
    ltnle ltle sylbird mpan imdistani absid syl ifeqda ) ABCZADEFZAGZAHAIJZUGUH
    UIAUJUGUHKUJUIALMUGUHNZKZUJAULUGDAEFZKUJAOUGUKUMDBCZUGUKUMPQUNUGKUKDARFUMDA
    SDATUAUBUCAUDUEMUFM $.

  $( Alternate expression for the absolute value of a real number.
     (Contributed by RP, 11-May-2024.) $)
  reabsifpos $p |- ( A e. RR -> ( abs ` A ) = if ( 0 < A , A , -u A ) ) $=
    ( cr wcel cc0 clt wbr cneg cif cabs cfv wa cle wceq 0re ltle mpan imdistani
    wi absid eqcomd syl wn id 0red lenltd pm5.32i absnid sylbir ifeqda ) ABCZDA
    EFZAAGZHAIJZUJUKAULUMUJUKKZUMAUNUJDALFZKUMAMUJUKUODBCUJUKUORNDAOPQASUATUJUK
    UBZKZUMULUQUJADLFZKUMULMUJURUPUJADUJUCUJUDUEUFAUGUHTUIT $.

  $( Alternate expression for the absolute value of a real number.
     (Contributed by RP, 11-May-2024.) $)
  reabsifnneg $p |- ( A e. RR -> ( abs ` A ) = if ( 0 <_ A , A , -u A ) ) $=
    ( cr wcel cc0 cle wbr cneg cif cabs cfv wa absid eqcomd wn wi 0re clt ltnle
    wceq ltle sylbird mpan2 imdistani absnid syl ifeqda ) ABCZDAEFZAAGZHAIJZUGU
    HAUIUJUGUHKUJAALMUGUHNZKZUJUIULUGADEFZKUJUISUGUKUMUGDBCZUKUMOPUGUNKUKADQFUM
    ADRADTUAUBUCAUDUEMUFM $.

  $( Alternate expression for the absolute value of a real number.
     (Contributed by RP, 22-May-2024.) $)
  reabssgn $p |- ( A e. RR -> ( abs ` A ) = ( ( sgn ` A ) x. A ) ) $=
    ( cr wcel csgn cfv cmul cc0 wceq clt wbr cneg cif cabs cxr rexr ovif adantr
    co c1 eqtr4d sgnval syl oveq1d ifeq2 ax-mp eqtri wa mul02lem2 simpr abs00bd
    wn recn mulm1d mullidd ifeq12d reabsifneg ifeqda eqtrid eqtr2d ) ABCZADEZAF
    RAGHZGAGIJZSKZSLZLZAFRZAMEZUTVAVFAFUTANCVAVFHAOAUAUBUCUTVGVBGAFRZVCVDAFRZSA
    FRZLZLZVHVGVBVIVEAFRZLZVMVBGVEAFPVNVLHVOVMHVCVDSAFPVBVNVLVIUDUEUFUTVBVIVLVH
    UTVBUGZVIGVHUTVIGHVBAUHQVPAUTVBUIUJTUTVLVHHVBUKUTVLVCAKZALVHUTVCVJVQVKAUTAA
    ULZUMUTAVRUNUOAUPTQUQURUS $.

  $( Not before releabs: $)

  $( Equivalent to saying that the square of the imaginary component of the
     square root of a complex number is a nonnegative real number.  Lemma for
     ~ sqrtcval .  See ~ imsqrtval .  (Contributed by RP, 11-May-2024.) $)
  sqrtcvallem2 $p |- ( A e. CC ->
                       0 <_ ( ( ( abs ` A ) - ( Re ` A ) ) / 2 ) ) $=
    ( cc wcel cabs cfv cre cmin co c2 recl resubcld crp 2rp a1i cc0 cle releabs
    abscl wbr subge0d mpbird divge0d ) ABCZADEZAFEZGHZIUCUDUEARZAJZKILCUCMNUCOU
    FPSUEUDPSAQUCUDUEUGUHTUAUB $.

  $( Not before resqrtcld: $)

  $( Equivalent to saying that the absolute value of the imaginary component of
     the square root of a complex number is a real number.  Lemma for
     ~ sqrtcval , ~ sqrtcval2 , ~ resqrtval , and ~ imsqrtval .  (Contributed
     by RP, 11-May-2024.) $)
  sqrtcvallem3 $p |- ( A e. CC ->
                     ( sqrt ` ( ( ( abs ` A ) - ( Re ` A ) ) / 2 ) ) e. RR ) $=
    ( cc wcel cabs cfv cre cmin co c2 cdiv recl resubcld rehalfcld sqrtcvallem2
    abscl resqrtcld ) ABCZADEZAFEZGHZIJHQTQRSAOAKLMANP $.

  $( Not before releabsd: $)

  $( Equivalent to saying that the square of the real component of the square
     root of a complex number is a nonnegative real number.  Lemma for
     ~ sqrtcval .  See ~ resqrtval .  (Contributed by RP, 11-May-2024.) $)
  sqrtcvallem4 $p |- ( A e. CC ->
                       0 <_ ( ( ( abs ` A ) + ( Re ` A ) ) / 2 ) ) $=
    ( cc wcel cabs cfv cre caddc co c2 abscl recl readdcld crp 2rp cc0 cneg cle
    cmin wbr recnd a1i negcl releabsd abscld recld subge0d mpbird reneg oveq12d
    absneg subnegd eqtrd breqtrd divge0d ) ABCZADEZAFEZGHZIUOUPUQAJZAKZLIMCUONU
    AUOOAPZDEZVAFEZRHZURQUOOVDQSVCVBQSUOVAAUBZUCUOVBVCUOVAVEUDUOVAVEUEUFUGUOVDU
    PUQPZRHURUOVBUPVCVFRAUJAUHUIUOUPUQUOUPUSTUOUQUTTUKULUMUN $.

  $( Equivalent to saying that the real component of the square root of a
     complex number is a real number.  Lemma for ~ resqrtval and ~ imsqrtval .
     (Contributed by RP, 11-May-2024.) $)
  sqrtcvallem5 $p |- ( A e. CC ->
                     ( sqrt ` ( ( ( abs ` A ) + ( Re ` A ) ) / 2 ) ) e. RR ) $=
    ( cc wcel cabs cfv caddc co cdiv abscl recl readdcld rehalfcld sqrtcvallem4
    cre c2 resqrtcld ) ABCZADEZANEZFGZOHGQTQRSAIAJKLAMP $.

  $( Explicit formula for the complex square root in terms of the
     square root of nonnegative reals.  The right-hand side is
     decomposed into real and imaginary parts in the format expected
     by ~ crrei and ~ crimi .
     <HTML>
     This formula can be found in section 3.7.27 of <I>Handbook
     of Mathematical Functions</I>, ed. M. Abramowitz and I. A.  Stegun
     (1965, Dover Press).
     </HTML>
     (Contributed by RP, 18-May-2024.) $)
  sqrtcval $p |- ( A e. CC -> ( sqrt ` A ) =
                   ( ( sqrt ` ( ( ( abs ` A ) + ( Re ` A ) ) / 2 ) ) + ( _i x.
                     ( if ( ( Im ` A ) < 0 , -u 1 , 1 ) x.
                     ( sqrt ` ( ( ( abs ` A ) - ( Re ` A ) ) / 2 ) ) ) ) ) ) $=
    ( cc wcel cfv caddc co c2 cdiv csqrt ci cc0 c1 cmul recnd a1i cexp wceq cle
    wb eqtrd cabs cre cim clt wbr cneg cmin sqrtcvallem5 ax-icn cr neg1rr ifcli
    cif 1re sqrtcvallem3 remulcld mulcld addcld id binom2 syl2anc recl readdcld
    abscl rehalfcld sqsqrtd sqmuld ovif neg1sqe1 sq1 ifeq12 mp2an ifid resubcld
    i2 3eqtri oveq12d mullidd 3eqtrd mulm1d negsubd pnncand 2timesd eqtr4d 2cnd
    oveq1d wne 2ne0 divsubdird divcan3d 3eqtr3d mul12d mulassd sqrtcvallem4 syl
    halfnneg2 mpbird crp 2rp sqrtdivd sqrtcvallem2 resqrtcld 2re 0le2 necon3bii
    sqrt00 mpbir divmuldivd resqcld imcl absvalsq2 mvrladdd subsq eqtr3d fveq2d
    absred reabsifneg sqrtmuld 3eqtr3rd remsqsqrt oveq2d renegcld ifcld divassd
    ovif12 neg1mulneg1e1 adantr wn ifeqda eqtrid divcan2d sqcld add32d sqrtge0d
    replim eqeq1d 3bitrd 3ad2ant1 eqtrdi mpbid crred breqtrrd wi cnsqrt00 half0
    3eqtr4d wa addcomd addeq0 wo olc eqcom sqeqor addid0 sqeq0 3bitr3d imbitrid
    reim ancld sylbid w3a simp2 negidd div0i sqrt0 simp3 0red eqnbrtrd iffalsed
    2cn ltnrd subnegd absge0 addlidd rered le0neg2d eqbrtrd 3expib sqrtcvallem1
    ixi syld eqsqrtd eqcomd ) ABCZAUADZAUBDZEFZGHFZIDZJAUCDZKUDUEZLUFZLUMZUWEUW
    FUGFZGHFZIDZMFZMFZEFZAIDUWDUWSAUWDUWIUWRUWDUWIAUHZNZUWDJUWQJBCUWDUIOZUWDUWQ
    UWDUWMUWPUWMUJCUWDUWKUWLLUJUKUNULOZAUOZUPZNZUQZURZUWDUSUWDUWSGPFZUWIGPFZGUW
    IUWRMFZMFZEFUWRGPFZEFZAUWDUWIBCUWRBCUXIUXNQUXAUXGUWIUWRUTVAUWDUXJUXMEFZUXLE
    FUWFJUWJMFZEFUXNAUWDUXOUWFUXLUXPEUWDUXOUWHUWOUFZEFUWHUWOUGFZUWFUWDUXJUWHUXM
    UXQEUWDUWHUWDUWHUWDUWGUWDUWEUWFAVDZAVBZVCZVEZNZVFUWDUXMJGPFZUWQGPFZMFUWLUWO
    MFUXQUWDJUWQUXBUXFVGUWDUYDUWLUYEUWOMUYDUWLQUWDVOOUWDUYEUWMGPFZUWPGPFZMFLUWO
    MFUWOUWDUWMUWPUWDUWMUXCNZUWDUWPUXDNZVGUWDUYFLUYGUWOMUYFLQUWDUYFUWKUWLGPFZLG
    PFZUMZUWKLLUMZLUWKUWLLGPVHUYJLQUYKLQUYLUYMQVIVJUWKUYJLUYKLVKVLUWKLVMVPOUWDU
    WOUWDUWOUWDUWNUWDUWEUWFUXSUXTVNZVENZVFVQUWDUWOUYOVRVSVQUWDUWOUYOVTVSVQUWDUW
    HUWOUYCUYOWAUWDUWGUWNUGFZGHFGUWFMFZGHFUXRUWFUWDUYPUYQGHUWDUYPUWFUWFEFUYQUWD
    UWEUWFUWFUWDUWEUXSNZUWDUWFUXTNZUYSWBUWDUWFUYSWCWDWFUWDUWGUWNGUWDUWGUYANZUWD
    UWNUYNNUWDWEZGKWGZUWDWHOZWIUWDUWFGUYSVUAVUCWJWKVSUWDGUWIMFZUWRMFJVUDUWQMFZM
    FUXLUXPUWDVUDJUWQUWDGUWIVUAUXAUQUXBUXFWLUWDGUWIUWRVUAUXAUXGWMUWDVUEUWJJMUWD
    VUEGUWIUWQMFZMFGUWMUWKUWJUFZUWJUMZGHFZMFZMFZUWJUWDGUWIUWQVUAUXAUXFWMUWDVUFV
    UJGMUWDVUFUWMUWIUWPMFZMFVUJUWDUWIUWMUWPUXAUYHUYIWLUWDVULVUIUWMMUWDVULUWGIDZ
    GIDZHFZUWNIDZVUNHFZMFVUMVUPMFZVUNVUNMFZHFVUIUWDUWIVUOUWPVUQMUWDUWGGUYAUWDKU
    WGRUEZKUWHRUEZAWNZUWDUWGUJCVUTVVASUYAUWGWPWOWQZGWRCUWDWSOZWTUWDUWNGUYNUWDKU
    WNRUEZKUWORUEZAXAUWDUWNUJCVVEVVFSUYNUWNWPWOWQZVVDWTVQUWDVUMVUNVUPVUNUWDVUMU
    WDUWGUYAVVCXBNUWDVUNUWDGGUJCZUWDXCOKGRUEZUWDXDOXBNZUWDVUPUWDUWNUYNVVGXBNVVJ
    VUNKWGZUWDVVKVUBWHVUNKGKVVHVVIVUNKQGKQSXCXDGXFVLXEXGOZVVLXHUWDVURVUHVUSGHUW
    DUWJGPFZIDZUWGUWNMFZIDVUHVURUWDVVMVVOIUWDUWEGPFZUWFGPFZUGFZVVMVVOUWDVVPVVQV
    VMUWDVVQUWDUWFUXTXINZUWDVVMUWDUWJAXJZXINZAXKZXLUWDUWEBCZUWFBCZVVRVVOQUYRUYS
    UWEUWFXMVAXNXOUWDUWJUADZVVNVUHUWDUWJVVTXPUWDUWJUJCVWEVUHQVVTUWJXQWOXNUWDUWG
    UWNUYAVVCUYNVVGXRXSVUSGQZUWDVVHVVIVWFXCXDGXTVLOVQVSYATYAUWDVUKGUWJGHFZMFUWJ
    UWDVUJVWGGMUWDUWMVUHMFZGHFVUJVWGUWDUWMVUHGUYHUWDVUHUWDUWKVUGUWJUJUWDUWJVVTY
    BVVTYCNVUAVUCYDUWDVWHUWJGHUWDVWHUWKUWLVUGMFZLUWJMFZUMUWJUWKUWLLVUGUWJMYEUWD
    UWKVWIVWJUWJUWDVWIUWJQUWKUWDUWLUWLMFZUWJMFZUWLUWLUWJMFZMFUWJVWIUWDUWLUWLUWJ
    UWDUWLUWLUJCUWDUKONZVWNUWDUWJVVTNZWMUWDVWLVWJUWJUWDVWKLUWJMVWKLQUWDYFOWFUWD
    UWJVWOVRZTUWDVWMVUGUWLMUWDUWJVWOVTYAXSYGUWDVWJUWJQUWKYHVWPYGYIYJWFXNYAUWDUW
    JGVWOVUAVUCYKTVSYAWKVQUWDUXJUXLUXMUWDUXJUWDUWIUWTXINUWDGUXKVUAUWDUWIUWRUXAU
    XGUQUQUWDUWRUXGYLYMAYOUUFTUWDKUWIUWSUBDZRUWDUWHUYBVVBYNUWDUWIUWQUWTUXEUUAZU
    UBUWDJUWSMFZUCDZKQZVWSUBDZKRUEZUUCVWSWRCYHUWDVXAUWFUWEUFZQZUWJKQZUUGZVXCUWD
    VXAVXEVXGUWDVXAUWIKQZUWHKQZVXEUWDVWTUWIKUWDVWQVWTUWIUWDUWSBCVWQVWTQUXHUWSUU
    RWOVWRXNYPUWDUWHBCVXHVXISUYCUWHUUDWOUWDVXIUWGKQZUWFUWEEFZKQZVXEUWDUWGBCVXIV
    XJSUYTUWGUUEWOUWDUWGVXKKUWDUWEUWFUYRUYSUUHYPUWDVWDVWCVXLVXESUYSUYRUWFUWEUUI
    VAYQYQUWDVXEVXFVXEUWFUWEQZVXEUUJZUWDVXFVXEVXMUUKUWDVVQVVPQZVVPVVQQZVXNVXFVX
    OVXPSUWDVVQVVPUULOUWDVWDVWCVXOVXNSUYSUYRUWFUWEUUMVAUWDVXPVVQVVMEFZVVQQZVVMK
    QZVXFUWDVVPVXQVVQVWBYPUWDVVQBCVVMBCVXRVXSSVVSVWAVVQVVMUUNVAUWDUWJBCVXSVXFSV
    WOUWJUUOWOYQUUPUUQUUSUUTUWDVXEVXFVXCUWDVXEVXFUVAZVXBUWEIDZUFZKRVXTVXBVYBUBD
    ZVYBVXTVWSVYBUBVXTVWSJJVYAMFZMFZVYBVXTUWSVYDJMVXTUWSKVYDEFVYDVXTUWIKUWRVYDE
    VXTUWIKIDKVXTUWHKIVXTUWHKGHFKVXTUWGKGHVXTUWGUWEVXDEFKVXTUWFVXDUWEEUWDVXEVXF
    UVBZYAVXTUWEUWDVXEVWCVXFUYRYRUVCTWFGUVJWHUVDYSXOUVEYSVXTUWQVYAJMVXTUWQLVYAM
    FZVYAVXTUWMLUWPVYAMVXTUWKUWLLVXTUWJKKUDUWDVXEVXFUVFVXTKVXTUVGUVKUVHUVIVXTUW
    OUWEIVXTUWOGUWEMFZGHFZUWEVXTUWNVYHGHVXTUWNUWEVXDUGFZVYHVXTUWFVXDUWEUGVYFYAU
    WDVXEVYJVYHQVXFUWDVYJUWEUWEEFVYHUWDUWEUWEUYRUYRUVLUWDUWEUYRWCWDYRTWFUWDVXEV
    YIUWEQVXFUWDUWEGUYRVUAVUCWJYRTXOVQUWDVXEVYGVYAQVXFUWDVYAUWDVYAUWDUWEUXSAUVM
    ZXBZNZVRYRTYAVQVXTVYDUWDVXEVYDBCVXFUWDJVYAUXBVYMUQYRUVNTYAUWDVXEVYEVYBQVXFU
    WDJJMFZVYAMFUWLVYAMFVYEVYBUWDVYNUWLVYAMVYNUWLQUWDUVTOWFUWDJJVYAUXBUXBVYMWMU
    WDVYAVYMVTWKYRTXOUWDVXEVYCVYBQVXFUWDVYBUWDVYAVYLYBUVOYRTUWDVXEVYBKRUEZVXFUW
    DKVYARUEVYOUWDUWEUXSVYKYNUWDVYAVYLUVPYTYRUVQUVRUWAUWDVWSUWDJUWSUXBUXHUQUVSY
    TUWBUWC $.

  $( Explicit formula for the complex square root in terms of the square root
     of nonnegative reals.  The right side is slightly more compact than
     ~ sqrtcval .  (Contributed by RP, 18-May-2024.) $)
  sqrtcval2 $p |- ( A e. CC -> ( sqrt ` A ) =
                ( ( sqrt ` ( ( ( abs ` A ) + ( Re ` A ) ) / 2 ) ) +
                  ( if ( ( Im ` A ) < 0 , -u _i , _i ) x.
                    ( sqrt ` ( ( ( abs ` A ) - ( Re ` A ) ) / 2 ) ) ) ) ) $=
    ( cc wcel csqrt cfv cabs caddc co c2 cdiv ci c1 cneg cif cmul ax-icn a1i cr
    wceq recnd cre cim cc0 clt wbr cmin sqrtcval neg1cn mulm1i mulcomli mulridi
    ovif2 ifeq12 mp2an eqtr2i oveq1d neg1rr 1re ifcli sqrtcvallem3 eqtrd oveq2d
    mulassd eqtr4d ) ABCZADEAFEZAUAEZGHIJHDEZKAUBEUCUDUEZLMZLNZVFVGUFHIJHDEZOHO
    HZGHVHVIKMZKNZVLOHZGHAUGVEVPVMVHGVEVPKVKOHZVLOHVMVEVOVQVLOVOVQSVEVQVIKVJOHZ
    KLOHZNZVOVIKVJLOULVRVNSVSKSVTVOSVJKVNUHPKPUIUJKPUKVIVRVNVSKUMUNUOQUPVEKVKVL
    KBCVEPQVEVKVKRCVEVIVJLRUQURUSQTVEVLAUTTVCVAVBVD $.

  $( Real part of the complex square root.  (Contributed by RP,
     18-May-2024.) $)
  resqrtval $p |- ( A e. CC -> ( Re ` ( sqrt ` A ) ) =
                ( sqrt ` ( ( ( abs ` A ) + ( Re ` A ) ) / 2 ) ) ) $=
    ( cc wcel csqrt cfv cre cabs caddc co c2 cdiv ci cim cc0 clt wbr c1 cneg cr
    cmul cif cmin sqrtcval fveq2d sqrtcvallem5 neg1rr 1re sqrtcvallem3 remulcld
    ifcli a1i crred eqtrd ) ABCZADEZFEAGEZAFEZHIJKIDEZLAMENOPZQRZQUAZUPUQUBIJKI
    DEZTIZTIHIZFEURUNUOVDFAUCUDUNURVCAUEUNVAVBVASCUNUSUTQSUFUGUJUKAUHUIULUM $.

  $( Imaginary part of the complex square root.  (Contributed by RP,
     18-May-2024.) $)
  imsqrtval $p |- ( A e. CC -> ( Im ` ( sqrt ` A ) ) =
                  ( if ( ( Im ` A ) < 0 , -u 1 , 1 ) x.
                    ( sqrt ` ( ( ( abs ` A ) - ( Re ` A ) ) / 2 ) ) ) ) $=
    ( cc wcel csqrt cfv cim cabs cre caddc co c2 cdiv ci cc0 clt wbr c1 cneg cr
    cmul cif cmin sqrtcval fveq2d sqrtcvallem5 neg1rr 1re sqrtcvallem3 remulcld
    ifcli a1i crimd eqtrd ) ABCZADEZFEAGEZAHEZIJKLJDEZMAFENOPZQRZQUAZUPUQUBJKLJ
    DEZTJZTJIJZFEVCUNUOVDFAUCUDUNURVCAUEUNVAVBVASCUNUSUTQSUFUGUJUKAUHUIULUM $.

  $( Example for ~ resqrtval .  (Contributed by RP, 21-May-2024.) $)
  resqrtvalex $p |- ( Re ` ( sqrt ` ( ; 1 5 + ( _i x. 8 ) ) ) ) = 4 $=
    ( c1 c5 cdc c8 cmul co caddc csqrt c2 c4 wceq 1nn0 5nn0 nn0cni c6 7nn0 eqid
    cfv c7 2nn0 ci cre cabs cdiv cexp cc wcel deccl ax-icn 8cn mulcli resqrtval
    addcli ax-mp c3 cr nn0rei 8re absreim mp2an c9 sqvali 1p1e2 7p5e12 addcomli
    mullidi decaddci mulridi oveq1i 5p2e7 eqtri 5t5e25 decmul2c decmul1c 8t8e64
    oveq12i 6nn0 4nn0 2cn 6p2e8 decaddi 5p4e9 decadd 7p1e8 7p4e11 7t7e49 eqtr2i
    9nn0 3eqtri fveq2i cc0 cle wbr nn0ge0i sqrtsqi crrei 2p1e3 decaddc mulcomli
    6t2e12 3nn0 2ne0 divmuli mpbir 4t4e16 ) ABCZUADEFZGFZHRUBRZXHUCRZXHUBRZGFZI
    UDFZHRZJIUEFZHRZJXHUFUGXIXNKXFXGXFABLMUHZNZUADUIUJUKUMXHULUNXMXOHXMUOICZIUD
    FZAOCZXOXLXSIUDASABUOIXJXKLPLMXJXFIUEFZDIUEFZGFZHRZASCZIUEFZHRZYFXFUPUGDUPU
    GXJYEKXFXQUQZURXFDUSUTYDYGHYDIICZBCZOJCZGFIDCZVACZYGYBYKYCYLGYBXFXFEFYKXFXR
    VBABYJBXFSXFXQLMXFQZMPABIIAXFEFSLMPXFXRVFVCTSBAICZSPNZBMNZVDVEVGABSBBIXFMLM
    YOMTBAEFZIGFBIGFSYSBIGBYRVHVIVJVKVLVMVNVKYCDDEFYLDUJVBVOVKVPYJBOJYMVAYKYLII
    TTUHMVQVRYKQYLQIIDYJOTTVQYJQOIDOVQNZVSVTVEWAWBWCYGYFYFEFYNYFYFASLPUHZNZVBAS
    YMVAYFAACZYFUUALPYFQZWHAALLUHASAAIDAYFEFUUCLPLLYFUUBVFUUCQVCWDWCASUUCVASJYF
    PLPUUDWHVRSAEFZJGFSJGFUUCUUESJGSYQVHVIWEVKWFVMVNWGWIWJWKYFWLWMYHYFKYFUUAWNY
    FYFUUAUQWOUNWIXFDYIURWPAAGFZAGFIAGFZUOUUFIAGVCVIWQVKTVDWRVIXTYAKIYAEFXSKAOU
    OIIAYATLVQYAQTLIAEFZAGFUUGUOUUHIAGIVSVHVIWQVKOIYPYTVSWTWSVMXSIYAXSUOIXATUHN
    VSYAAOLVQUHNXBXCXDXOJJEFYAJJVRNVBXEWGWIWJWKJWLWMXPJKJVRWNJJVRUQWOUNWI $.

  $( Example for ~ imsqrtval .  (Contributed by RP, 21-May-2024.) $)
  imsqrtvalex $p |- ( Im ` ( sqrt ` ( ; 1 5 + ( _i x. 8 ) ) ) ) = 1 $=
    ( c1 c5 cdc c8 cmul co caddc csqrt cfv cc0 c2 1nn0 5nn0 nn0cni c7 eqid 7nn0
    c4 2nn0 eqtri ci cim clt wbr cneg cif cabs cre cmin cdiv cc wcel wceq deccl
    ax-icn 8cn mulcli addcli imsqrtval ax-mp 8pos 0re 8re ltnsymi nn0rei breq1i
    wn crimi sylnibr iffalsei cexp cr absreim mp2an c6 c9 sqvali mullidi 7p5e12
    1p1e2 addcomli decaddci mulridi oveq1i 5p2e7 5t5e25 decmul2c 8t8e64 oveq12i
    6nn0 4nn0 6p2e8 decaddi 5p4e9 decadd 9nn0 7p1e8 7p4e11 7t7e49 eqtr2i 3eqtri
    decmul1c fveq2i cle nn0ge0i sqrtsqi crrei subaddrii 2div2e1 sqrt1 1t1e1 ) A
    BCZUADEFZGFZHIUBIZXNUBIZJUCUDZAUEZAUFZXNUGIZXNUHIZUIFZKUJFZHIZEFZAAEFAXNUKU
    LXOYEUMXLXMXLABLMUNZNZUADUOUPUQURXNUSUTXSAYDAEXQXRAJDUCUDZXQVGVAYHDJUCUDXQJ
    DVBVCVDXPDJUCXLDXLYFVEZVCVHVFVIUTVJYDAHIAYCAHYCKKUJFAYBKKUJYBAOCZXLUIFKXTYJ
    YAXLUIXTXLKVKFZDKVKFZGFZHIZYJKVKFZHIZYJXLVLULDVLULXTYNUMYIVCXLDVMVNYMYOHYMK
    KCZBCZVORCZGFKDCZVPCZYOYKYRYLYSGYKXLXLEFYRXLYGVQABYQBXLOXLYFLMXLPZMQABKKAXL
    EFOLMQXLYGVRVTSOBAKCOQNZBMNZVSWAWBABOBBKXLMLMUUBMSBAEFZKGFBKGFOUUEBKGBUUDWC
    WDWETWFWGXBTYLDDEFYSDUPVQWHTWIYQBVORYTVPYRYSKKSSUNMWJWKYRPYSPKKDYQVOSSWJYQP
    VOKDVOWJNKSNZWLWAWMWNWOYOYJYJEFUUAYJYJAOLQUNZNZVQAOYTVPYJAACZYJUUGLQYJPZWPA
    ALLUNAOAAKDAYJEFUUILQLLYJUUHVRUUIPVTWQWOAOUUIVPORYJQLQUUJWPWKOAEFZRGFORGFUU
    IUUKORGOUUCWCWDWRTWSWGXBWTXAXCJYJXDUDYPYJUMYJUUGXEYJYJUUGVEXFUTXAXLDYIVCXGW
    IYJXLKUUHYGUUFABOXLKLMSUUBWEWMXHTWDXITXCXJTWIXKXA $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Additional statements on relations and subclasses
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Version of ~ ax-4 for a nested implication.  (Contributed by RP,
     13-Apr-2020.) $)
  al3im $p |- ( A. x ( ph -> ( ps -> ( ch -> th ) ) )
                -> ( A. x ph -> ( A. x ps -> ( A. x ch -> A. x th ) ) ) ) $=
    ( wi wal alim al2im syl6 ) ABCDFFZFEGAEGKEGBEGCEGDEGFFAKEHBCDEIJ $.

  ${
    $d x A $.  $d x B $.  $d x a $.
    $( Two ways of expressing the intersection of images of a class.
       (Contributed by RP, 13-Apr-2020.) $)
    intima0 $p |- |^|_ a e. A ( a " B )
                  = |^| { x | E. a e. A x = ( a " B ) } $=
      ( cv cima vex imaex dfiin2 ) DABDEZCFJCDGHI $.
  $}

  ${
    $d a b A $.  $d b B $.  $d a b y $.
    $( Element of image of intersection.  (Contributed by RP, 13-Apr-2020.) $)
    elimaint $p |- ( y e. ( |^| A " B )
                     <-> E. b e. B A. a e. A <. b , y >. e. a ) $=
      ( cv cint cima wcel wbr wrex cop wral vex elima df-br elint2 bitri rexbii
      opex ) AFZBGZCHIEFZUAUBJZECKUCUALZDFIDBMZECKEUAUBCANOUDUFECUDUEUBIUFUCUAU
      BPDUEBUCUATQRSR $.
  $}

  ${
    $d x y z A $.  $d y z B $.
    $( Converse of indexed union.  (Contributed by RP, 20-Jun-2020.) $)
    cnviun $p |- `' U_ x e. A B = U_ x e. A `' B $=
      ( vy vz ciun ccnv relcnv wrel reliun cv wcel a1i mprgbir cop wrex opelcnv
      vex bicomi eliun rexbii bitri 3bitr4i eqrelriiv ) DEABCFZGZABCGZFZUEHUHIU
      GIZABABUGJUIAKBLCHMNEKZDKZOZCLZABPZUKUJOZUGLZABPUOUFLZUOUHLUMUPABUPUMUKUJ
      CDRZERZQSUAUQULUELUNUKUJUEURUSQAULBCTUBAUOBUGTUCUD $.
  $}

  ${
    $d y z A $.  $d y z B $.  $d x y z C $.
    $( The image of an indexed union is the indexed union of the images.
       (Contributed by RP, 29-Jun-2020.) $)
    imaiun1 $p |- ( U_ x e. A B " C ) = U_ x e. A ( B " C ) $=
      ( vy vz ciun cima cv wcel cop wa wex wrex rexcom4 vex elima3 rexbii eliun
      anbi2i r19.42v bitr4i exbii 3bitr4ri 3bitr4i eqriv ) EABCGZDHZABCDHZGZFIZ
      DJZUKEIZKZUGJZLZFMZUMUIJZABNZUMUHJUMUJJULUNCJZLZFMZABNVAABNZFMUSUQVAAFBOU
      RVBABFUMCDEPZQRUPVCFUPULUTABNZLVCUOVEULAUNBCSTULUTABUAUBUCUDFUMUGDVDQAUMB
      UISUEUF $.
  $}

  ${
    $d w y z A $.  $d w x y z B $.  $d w y z C $.
    $( Composition with an indexed union.  Proof analogous to that of ~ coiun .
       (Contributed by RP, 20-Jun-2020.) $)
    coiun1 $p |- ( U_ x e. C A o. B ) = U_ x e. C ( A o. B ) $=
      ( vy vz vw ciun ccom relco wrel cv wcel wbr wa wex wrex cop eliun df-br
      reliun a1i mprgbir rexbii 3bitr4i anbi2i r19.42v bitr4i exbii rexcom4 vex
      opelco bitri eqrelriiv ) EFADBHZCIZADBCIZHZUOCJURKUQKZADADUQUAUSALDMBCJUB
      UCELZGLZCNZVAFLZUONZOZGPZVBVAVCBNZOZGPZADQZUTVCRZUPMVKURMZVFVHADQZGPVJVEV
      MGVEVBVGADQZOVMVDVNVBVAVCRZUOMVOBMZADQVDVNAVODBSVAVCUOTVGVPADVAVCBTUDUEUF
      VBVGADUGUHUIVHAGDUJUHGUTVCUOCEUKZFUKZULVLVKUQMZADQVJAVKDUQSVSVIADGUTVCBCV
      QVRULUDUMUEUN $.
  $}

  ${
    $d x z A $.  $d x z B $.  $d a y z $.  $d b B $.  $d a b x y $.
    $( Element of intersection of images.  (Contributed by RP, 13-Apr-2020.) $)
    elintima $p |- ( y e. |^| { x | E. a e. A x = ( a " B ) }
                     <-> A. a e. A E. b e. B <. b , y >. e. a ) $=
      ( vz cv wrex wcel wel wral vex wi wal wex imbi1i 19.23v bitri albii simpr
      cima wceq cab cop elint2 elequ2 ralab2 wa df-rex eleq2d pm5.74i wbr elima
      cint df-br rexbii imbi2i 3bitr2i imaex isseti 19.42v alcom df-ral 3bitr4i
      mpbiran2 ) BHZAHZEHZDUBZUCZECIZAUDZUOJBGKZGVMLZFHZVGUEVIJZFDIZECLZGVGVMBM
      ZUFVOVLBAKZNZAOZVSVLVNWAGAGABUGUHWCVICJZVKUIZVRNZEOZAOZVSWBWGAWBWEEPZWANW
      EWANZEOWGVLWIWAVKECUJQWEWAERWJWFEWJWEVGVJJZNWFWEWAWKWEVHVJVGWDVKUAUKULWKV
      RWEWKVPVGVIUMZFDIVRFVGVIDVTUNWLVQFDVPVGVIUPUQSURSTUSTWFAOZEOWDVRNZEOWHVSW
      MWNEWMWEAPZVRNWNWEVRARWOWDVRWOWDVKAPAVJVIDEMUTVAWDVKAVBVFQSTWFAEVCVRECVDV
      ESSS $.
  $}

  ${
    $d a x y A $.  $d a x y B $.  $d b A $.  $d b B $.  $d a b y $.  $d x b $.
    $( The image under the intersection of relations is a subset of the
       intersection of the images.  (Contributed by RP, 13-Apr-2020.) $)
    intimass $p |- ( |^| A " B )
                   C_ |^| { x | E. a e. A x = ( a " B ) } $=
      ( vy vb cint cima cv wceq wrex cab cop wcel wral r19.12 elimaint elintima
      3imtr4i ssriv ) EBGCHZAIDIZCHJDBKALGZFIEIZMUBNZDBOFCKUEFCKDBOUDUANUDUCNUE
      FDCBPEBCDFQAEBCDFRST $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( The image under the intersection of relations is a subset of the
       intersection of the images.  (Contributed by RP, 13-Apr-2020.) $)
    intimass2 $p |- ( |^| A " B ) C_ |^|_ x e. A ( x " B ) $=
      ( vy cint cima cv wceq wrex cab ciin intimass intima0 sseqtrri ) BECFDGAG
      CFZHABIDJEABOKDBCALDBCAMN $.
  $}

  ${
    $d a x y A $.  $d a x y B $.  $d b A $.  $d b B $.  $d a b y $.  $d x b $.
    $( Requirement for the image under the intersection of relations to equal
       the intersection of the images of those relations.  (Contributed by RP,
       13-Apr-2020.) $)
    intimag $p |- ( A. y ( A. a e. A E. b e. B <. b , y >. e. a
                           -> E. b e. B A. a e. A <. b , y >. e. a )
                    -> ( |^| A " B )
                       = |^| { x | E. a e. A x = ( a " B ) } ) $=
      ( cv cop wcel wrex wral wi wal cint cima wceq cab wb r19.12 id elimaint
      impbid2 elintima 3bitr4g alimi dfcleq sylibr ) FGBGZHEGZIZFDJECKZUJECKFDJ
      ZLZBMUHCNDOZIZUHAGUIDOPECJAQNZIZRZBMUNUPPUMURBUMULUKUOUQUMULUKUJFEDCSUMTU
      BBCDEFUAABCDEFUCUDUEBUNUPUFUG $.
  $}

  ${
    $d y V $.  $d a b y A $.  $d a b y B $.  $d a x A $.  $d x y B $.
    $d x b $.
    $( Two ways to express the image of a singleton when the relation is an
       intersection.  (Contributed by RP, 13-Apr-2020.) $)
    intimasn $p |- ( B e. V -> ( |^| A " { B } )
                               = |^| { x | E. a e. A x = ( a " { B } ) } ) $=
      ( vy vb wcel wal cv cop csn wrex wral wi cint cima wceq cab ax-5 r19.12sn
      biimprd alimi intimag 3syl ) CDHZUFFIGJFJKEJZHZGCLZMEBNZUHEBNGUIMZOZFIBPU
      IQAJUGUIQREBMASPRUFFTUFULFUFUKUJUHGECBDUAUBUCAFBUIEGUDUE $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Two ways to express the image of a singleton when the relation is an
       intersection.  (Contributed by RP, 13-Apr-2020.) $)
    intimasn2 $p |- ( B e. V -> ( |^| A " { B } )
                                  = |^|_ x e. A ( x " { B } ) ) $=
      ( vy wcel cint csn cima cv wceq wrex cab ciin intimasn intima0 eqtr4di )
      CDFBGCHZIEJAJRIZKABLEMGABSNEBCDAOEBRAPQ $.
  $}

  ${
    ss2iundf.xph $e |- F/ x ph $.
    ss2iundf.yph $e |- F/ y ph $.
    ss2iundf.y $e |- F/_ y Y $.
    ss2iundf.a $e |- F/_ y A $.
    ss2iundf.b $e |- F/_ y B $.
    ss2iundf.xc $e |- F/_ x C $.
    ss2iundf.yc $e |- F/_ y C $.
    ss2iundf.d $e |- F/_ x D $.
    ss2iundf.g $e |- F/_ y G $.
    ss2iundf.el $e |- ( ( ph /\ x e. A ) -> Y e. C ) $.
    ss2iundf.sub $e |- ( ( ph /\ x e. A /\ y = Y ) -> D = G ) $.
    ss2iundf.ss $e |- ( ( ph /\ x e. A ) -> B C_ G ) $.
    $d x y z $.  $d z A $.  $d z B $.  $d z C $.  $d z D $.
    $( Subclass theorem for indexed union.  (Contributed by RP,
       17-Jul-2020.) $)
    ss2iundf $p |- ( ph -> U_ x e. A B C_ U_ y e. C D ) $=
      ( vz wss wrex wral ciun cv wcel wa wn wi wal df-ral wceq nfcri nfan simpr
      eleq1d biimprd wb w3a sseq2d 3expa notbid biimpd imim12d alrimi nfel nfss
      nfn nfim spcimgfi1 sylc mpid biimtrid con2d dfrex2 imbitrrdi mpd ralrimia
      ex ssel reximi r19.37 syl eliun ssrdv ralimi nfiun iunssf sylibr ) AEGUCZ
      CFUDZBDUEZBDEUFCFGUFZUCZAWMBDJABUGDUHZUIZEHUCZWMUAWRWSWLUJZCFUEZUJWMWRXAW
      SXACUGZFUHZWTUKZCULZWRWSUJZWTCFUMWRXEIFUHZXFSWRXBIUNZXDXGXFUKZUKZUKZCULXG
      XEXIUKWRXKCAWQCKCBDMUOUPWRXHXJWRXHUIZXGXCWTXFXLXCXGXLXBIFWRXHUQURUSXLWTXF
      XLWLWSAWQXHWLWSUTAWQXHVAGHETVBVCVDVEVFWAVGSXDXICIFXGXFCCIFLPVHWSCCEHNRVIV
      JVKLVLVMVNVOVPWLCFVQVRVSVTWNEWOUCZBDUEWPWMXMBDWMUBEWOWMUBUGZEUHZXNGUHZCFU
      DZXNWOUHWMXOXPUKZCFUDXOXQUKWLXRCFEGXNWBWCXOXPCFCUBENUOWDWECXNFGWFVRWGWHBD
      EWOCBFGOQWIWJWKWE $.
  $}

  ${
    ss2iundv.el $e |- ( ( ph /\ x e. A ) -> Y e. C ) $.
    ss2iundv.sub $e |- ( ( ph /\ x e. A /\ y = Y ) -> D = G ) $.
    ss2iundv.ss $e |- ( ( ph /\ x e. A ) -> B C_ G ) $.
    $d x y ph $.  $d y A $.  $d y B $.  $d x y C $.  $d x D $.  $d y G $.
    $d y Y $.
    $( Subclass theorem for indexed union.  (Contributed by RP,
       17-Jul-2020.) $)
    ss2iundv $p |- ( ph -> U_ x e. A B C_ U_ y e. C D ) $=
      ( nfv nfcv ss2iundf ) ABCDEFGHIABMACMCINCDNCENBFNCFNBGNCHNJKLO $.
  $}

  ${
    cbviuneq12df.xph $e |- F/ x ph $.
    cbviuneq12df.yph $e |- F/ y ph $.
    cbviuneq12df.x $e |- F/_ x X $.
    cbviuneq12df.y $e |- F/_ y Y $.
    cbviuneq12df.xa $e |- F/_ x A $.
    cbviuneq12df.ya $e |- F/_ y A $.
    cbviuneq12df.b $e |- F/_ y B $.
    cbviuneq12df.xc $e |- F/_ x C $.
    cbviuneq12df.yc $e |- F/_ y C $.
    cbviuneq12df.d $e |- F/_ x D $.
    cbviuneq12df.f $e |- F/_ x F $.
    cbviuneq12df.g $e |- F/_ y G $.
    cbviuneq12df.xel $e |- ( ( ph /\ y e. C ) -> X e. A ) $.
    cbviuneq12df.yel $e |- ( ( ph /\ x e. A ) -> Y e. C ) $.
    cbviuneq12df.xsub $e |- ( ( ph /\ y e. C /\ x = X ) -> B = F ) $.
    cbviuneq12df.ysub $e |- ( ( ph /\ x e. A /\ y = Y ) -> D = G ) $.
    cbviuneq12df.eq1 $e |- ( ( ph /\ x e. A ) -> B = G ) $.
    cbviuneq12df.eq2 $e |- ( ( ph /\ y e. C ) -> D = F ) $.

    $d x y $.
    $( Rule used to change the bound variables and classes in an indexed union,
       with the substitution specified implicitly by the hypothesis.
       (Contributed by RP, 17-Jul-2020.) $)
    cbviuneq12df $p |- ( ph -> U_ x e. A B = U_ y e. C D ) $=
      ( ciun cv wcel wa wceq wss eqimss syl ss2iundf eqssd ) ABDEUJCFGUJABCDEFG
      IKLMOQRSTUAUCUEUGABUKDULUMEIUNEIUOUHEIUPUQURACBFGDEHJMLNSUAQPRUBUDUFACUKF
      ULUMGHUNGHUOUIGHUPUQURUS $.
  $}

  ${
    cbviuneq12dv.xel $e |- ( ( ph /\ y e. C ) -> X e. A ) $.
    cbviuneq12dv.yel $e |- ( ( ph /\ x e. A ) -> Y e. C ) $.
    cbviuneq12dv.xsub $e |- ( ( ph /\ y e. C /\ x = X ) -> B = F ) $.
    cbviuneq12dv.ysub $e |- ( ( ph /\ x e. A /\ y = Y ) -> D = G ) $.
    cbviuneq12dv.eq1 $e |- ( ( ph /\ x e. A ) -> B = G ) $.
    cbviuneq12dv.eq2 $e |- ( ( ph /\ y e. C ) -> D = F ) $.

    $d x y ph $.  $d x y A $.  $d y B $.  $d x y C $.  $d x D $.  $d x F $.
    $d y G $.  $d x X $.  $d y Y $.
    $( Rule used to change the bound variables and classes in an indexed union,
       with the substitution specified implicitly by the hypothesis.
       (Contributed by RP, 17-Jul-2020.) $)
    cbviuneq12dv $p |- ( ph -> U_ x e. A B = U_ y e. C D ) $=
      ( nfv nfcv cbviuneq12df ) ABCDEFGHIJKABRACRBJSCKSBDSCDSCESBFSCFSBGSBHSCIS
      LMNOPQT $.
  $}

  ${
    conrel1d.a $e |- ( ph -> `' A = (/) ) $.
    $( Deduction about composition with a class with no relational content.
       (Contributed by RP, 24-Dec-2019.) $)
    conrel1d $p |- ( ph -> ( A o. B ) = (/) ) $=
      ( cdm crn cin incom wceq ccnv dfdm4 rneqd rn0 eqtrdi eqtrid ineq2 in0 syl
      c0 coemptyd ) ABCABEZCFZGUBUAGZSUAUBHAUASIZUCSIAUABJZFZSBKAUFSFSAUESDLMNO
      UDUCUBSGSUASUBPUBQNROT $.
    $( Deduction about composition with a class with no relational content.
       (Contributed by RP, 24-Dec-2019.) $)
    conrel2d $p |- ( ph -> ( B o. A ) = (/) ) $=
      ( cdm crn cin ccnv c0 wceq df-rn ineq2i a1i dmeqd ineq2d dm0 eqtri 3eqtrd
      in0 coemptyd ) ACBACEZBFZGZUABHZEZGZUAIEZGZIUCUFJAUBUEUABKLMAUEUGUAAUDIDN
      OUHIJAUHUAIGIUGIUAPLUASQMRT $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Transitive relations (not to be confused with transitive classes)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    trrelind.r $e |- ( ph -> ( R o. R ) C_ R ) $.
    trrelind.s $e |- ( ph -> ( S o. S ) C_ S ) $.
    trrelind.t $e |- ( ph -> T = ( R i^i S ) ) $.
    $( The intersection of transitive relations is a transitive relation.
       (Contributed by RP, 24-Dec-2019.) $)
    trrelind $p |- ( ph -> ( T o. T ) C_ T ) $=
      ( cin ccom wss inss1 a1i trrelssd inss2 ssind coeq12d 3sstr4d ) ABCHZRIZR
      DDIDASBCABRRERBJABCKLZTMACRRFRCJABCNLZUAMOADRDRGGPGQ $.
  $}

  ${
    xpintrreld.r $e |- ( ph -> ( R o. R ) C_ R ) $.
    xpintrreld.s $e |- ( ph -> S = ( R i^i ( A X. B ) ) ) $.
    $( The intersection of a transitive relation with a Cartesian product is a
       transitive relation.  (Contributed by RP, 24-Dec-2019.) $)
    xpintrreld $p |- ( ph -> ( S o. S ) C_ S ) $=
      ( cxp ccom wss xptrrel a1i trrelind ) ADBCHZEFNNINJABCKLGM $.
  $}

  ${
    restrreld.r $e |- ( ph -> ( R o. R ) C_ R ) $.
    restrreld.s $e |- ( ph -> S = ( R |` A ) ) $.
    $( The restriction of a transitive relation is a transitive relation.
       (Contributed by RP, 24-Dec-2019.) $)
    restrreld $p |- ( ph -> ( S o. S ) C_ S ) $=
      ( cvv cres cxp cin df-res eqtrdi xpintrreld ) ABGCDEADCBHCBGIJFCBKLM $.
  $}

  ${
    trrelsuperreldg.r $e |- ( ph -> Rel R ) $.
    trrelsuperreldg.s $e |- ( ph -> S = ( dom R X. ran R ) ) $.
    $( Concrete construction of a superclass of relation ` R ` which is a
       transitive relation.  (Contributed by RP, 25-Dec-2019.) $)
    trrelsuperreldg $p |- ( ph -> ( R C_ S /\ ( S o. S ) C_ S ) ) $=
      ( wss ccom cdm crn cxp relssdmrn syl sseqtrrd xptrrel a1i coeq12d 3sstr4d
      wrel jca ) ABCFCCGZCFABBHZBIZJZCABRBUCFDBKLEMAUCUCGZUCTCUDUCFAUAUBNOACUCC
      UCEEPEQS $.
  $}

  ${
    $d x y z $.  $d y A $.
    trficl.a $e |- A = { z | ( z o. z ) C_ z } $.
    $( The class of all transitive relations has the finite intersection
       property.  (Contributed by RP, 1-Jan-2020.)  (Proof shortened by RP,
       3-Jan-2020.) $)
    trficl $p |- A. x e. A A. y e. A ( x i^i y ) e. A $=
      ( cv ccom wss cin cvv vex inex1 wceq id coeq12d sseq12d weq trin2 cllem0
      ) CFZTGZTHAFZBFZIZUDGZUDHUBUBGZUBHUCUCGZUCHABCUDJDEUBUCAKLTUDMZUAUETUDUHT
      UDTUDUHNZUIOUIPCAQZUAUFTUBUJTUBTUBUJNZUKOUKPCBQZUAUGTUCULTUCTUCULNZUMOUMP
      UBUCRS $.
  $}

  $( The converse of a transitive relation is a transitive relation.
     (Contributed by RP, 25-Dec-2019.) $)
  cnvtrrel $p |- ( ( S o. S ) C_ S <-> ( `' S o. `' S ) C_ `' S ) $=
    ( ccom wss ccnv cnvss cnvco cnveqi cocnvcnv1 cocnvcnv2 3eqtri sseq1i biimpi
    eqtri cnvcnvss sstrdi syl impbii bitri ) AABZACZSDZADZCZUBUBBZUBCTUCSAEUCUA
    DZUBDZCZTUAUBEUGSUFAUGSUFCUESUFUEUDDUFUFBZSUAUDAAFZGUBUBFUHAUFBSAUFHAAIMJKL
    ANOPQUAUDUBUIKR $.

  ${
    trrelsuperrel2dg.s $e |- ( ph -> S = ( R u. ( dom R X. ran R ) ) ) $.
    $( Concrete construction of a superclass of relation ` R ` which is a
       transitive relation.  (Contributed by RP, 20-Jul-2020.) $)
    trrelsuperrel2dg $p |- ( ph -> ( R C_ S /\ ( S o. S ) C_ S ) ) $=
      ( wss ccom cdm crn cxp cun ssun1 sseqtrrid ccnv syl eqsstrrid sylib ax-mp
      wceq ssequn1 eqtri xptrrel ssun2 sstri a1i coeq12d coundir wrel cocnvcnv1
      relcnv relssdmrn dmcnvcnv rncnvcnv xpeq12i sseqtrdi coss1 cocnvcnv2 coss2
      coundi eqtrdi 3sstr4d jca ) ABCECCFZCEABBGZBHZIZJZBCBVEKDLAVEVEFZVFVBCVGV
      FEAVGVEVFVCVDUAVEBUBUCUDAVBVFVFFZVGACVFCVFDDUEVHVEVFFZVGVHBVFFZVIJZVIBVEV
      FUFBMZMZUGZVKVIRZVLUIZVNVJVIEVOVNVJVMVFFZVIBVFUHVNVMVEEZVQVIEVNVMVMGZVMHZ
      IVEVMUJVSVCVTVDBUKBULUMUNZVMVEVFUONOVJVISPQTVIVEBFZVGJZVGVEBVEURVNWCVGRZV
      PVNWBVGEWDVNWBVEVMFZVGVEBUPVNVRWEVGEWAVMVEVEUQNOWBVGSPQTTUSDUTVA $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Reflexive closures
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c r* $.

  $( Extend class notation with reflexive closure. $)
  crcl $a class r* $.

  ${
    $d x z $.
    $( Reflexive closure of a relation.  This is the smallest superset which
       has the reflexive property.  (Contributed by RP, 5-Jun-2020.) $)
    df-rcl $a |- r* = ( x e. _V |-> |^| { z | ( x C_ z /\ ( _I |`
                    ( dom z u. ran z ) ) C_ z ) } ) $.
  $}

  ${
    $d x z $.
    $( Reflexive closure of a relation as union with restricted identity
       relation.  (Contributed by RP, 6-Jun-2020.) $)
    dfrcl2 $p |- r* = ( x e. _V |-> ( ( _I |` ( dom x u. ran x ) ) u. x ) ) $=
      ( vz cvv cv wss cid cdm crn cun cres cint cmpt wcel wceq a1i uneq1i unidm
      wa unex eqtri crcl cab df-rcl crab rabab eqcomi inteqi dmex resiexg ax-mp
      vex rnex ssun2 dmun dmresi un23 3eqtri rnun rnresi uneq2i uneq12i reseq2i
      unass ssun1 eqsstri pm3.2i dmeq rneq uneq12d reseq2d id cleq2lem intminss
      sseq12d sylancl eqsstrd wal cin dmss rnss unss12 syl2anc dfss sylib incom
      eqtrdi resres eqtr4di resss adantr simpr sstrd simpl unssd ax-gen ssintab
      wi sylibr eqssd mpteq2ia ) UAACADZBDZEZFXBGZXBHZIZJZXBEZRZBUBZKZLACFXAGZX
      AHZIZJZXAIZLABUCACXKXPXACMZXKXPXQXKXIBCUDZKZXPXKXSNXQXJXRXRXJXIBUEUFUGOXQ
      XPCMZXAXPEZFXPGZXPHZIZJZXPEZRZXSXPEXTXQXOXAXNCMXOCMXLXMXAAUKZUHXAYHULSXNC
      UIUJYHSOYAYFXAXOUMYEXOXPYDXNFYDXNXNIXNYBXNYCXNYBXOGZXLIXNXLIZXNXOXAUNYIXN
      XLXNUOPYJXLXLIZXMIXNXLXMXLUPYKXLXMXLQPTUQYCXOHZXMIXNXMIZXNXOXAURYLXNXMXNU
      SPYMXLXMXMIZIXNXLXMXMVCYNXMXLXMQUTTUQVAXNQTVBXOXAVDVEVFXIYGBXPCXHYFXBXPXA
      XBXPNZXGYEXBXPYOXFYDFYOXDYBXEYCXBXPVGXBXPVHVIVJYOVKVNVLVMVOVPXQXIXPXBEWQZ
      BVQZXPXKEYQXQYPBXIXOXAXBXIXOXGXBXCXOXGEXHXCXOXGXNJZXGXCXOFXFXNVRZJYRXCXNY
      SFXCXNXNXFVRZYSXCXNXFEZXNYTNXCXLXDEXMXEEUUAXAXBVSXAXBVTXLXDXMXEWAWBXNXFWC
      WDXNXFWEWFVJFXFXNWGWHYRXGEXCXGXNWIOVPWJXCXHWKWLXCXHWMWNWOOXIBXPWPWRWSWTT
      $.
  $}

  $( Reflexive closure of a relation as union of powers of the relation.
     (Contributed by RP, 6-Jun-2020.) $)
  dfrcl3 $p |- r* = ( x e. _V |-> ( ( x ^r 0 ) u. ( x ^r 1 ) ) ) $=
    ( crcl cvv cid cv cdm crn cun cres cmpt cc0 crelexp co dfrcl2 wcel relexp0g
    c1 relexp1g uneq12d mpteq2ia eqtr4i ) BACDAEZFUBGHIZUBHZJACUBKLMZUBQLMZHZJA
    NACUGUDUBCOUEUCUFUBUBCPUBCRSTUA $.

  ${
    $d n r $.
    $( Reflexive closure of a relation as indexed union of powers of the
       relation.  (Contributed by RP, 8-Jun-2020.) $)
    dfrcl4 $p |- r* = ( r e. _V |-> U_ n e. { 0 , 1 } ( r ^r n ) ) $=
      ( crcl cvv cv cc0 crelexp co c1 cun cmpt cpr ciun dfrcl3 csn df-pr iuneq1
      wceq oveq2 iunxsn ax-mp iunxun c0ex 1ex uneq12i 3eqtri mpteq2i eqtr4i ) C
      BDBEZFGHZUIIGHZJZKBDAFILZUIAEZGHZMZKBNBDUPULUPAFOZIOZJZUOMZAUQUOMZAURUOMZ
      JULUMUSRUPUTRFIPAUMUSUOQUAAUQURUOUBVAUJVBUKAFUOUJUCUNFUIGSTAIUOUKUDUNIUIG
      STUEUFUGUH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Finite relationship composition
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  In order for theorems on the transitive closure of a relation to
  be grouped together before the concept of continuity, we really
  need an analogue of ` ^r ` that works on finite ordinals or finite
  sets instead of natural numbers.

$)

  $( A set operated on by the relation exponent to the second power is equal to
     the composition of the set with itself.  (Contributed by RP,
     1-Jun-2020.) $)
  relexp2 $p |- ( R e. V -> ( R ^r 2 ) = ( R o. R ) ) $=
    ( wcel c2 crelexp co c1 caddc ccom wceq df-2 oveq2i a1i cn 1nn relexpsucnnr
    mpan2 relexp1g coeq1d 3eqtrd ) ABCZADEFZAGGHFZEFZAGEFZAIZAAIUBUDJUADUCAEKLM
    UAGNCUDUFJOAGBPQUAUEAAABRST $.

  $( If the domain and range of powers of a relation are disjoint then the
     relation raised to the sum of those exponents is empty.  (Contributed by
     RP, 1-Jun-2020.) $)
  relexpnul $p |- ( ( ( R e. V /\ Rel R ) /\ ( N e. NN0 /\ M e. NN0 ) )
                    -> ( ( dom ( R ^r N ) i^i ran ( R ^r M ) ) = (/)
                         <-> ( R ^r ( N + M ) ) = (/) ) ) $=
    ( crelexp co cdm crn cin c0 wceq ccom wcel wa cn0 caddc coeq0 simplr simprl
    wrel simprr relexpaddd eqeq1d bitr3id ) ACEFZGABEFZHIJKUEUFLZJKADMZATZNZCOM
    ZBOMZNZNZACBPFEFZJKUEUFQUNUGUOJUNABCUHUIUMRUJUKULSUJUKULUAUBUCUD $.

  ${
    $d n r C N .^ $.
    mptiunov2.def $e |- C = ( r e. _V |-> U_ n e. N ( r .^ n ) ) $.

    ${
      $d n r R $.  $d n X $.
      $( Membership in the indexed union over operator values where the index
         varies the second input is equivalent to the existence of at least one
         index such that the element is a member of that operator value.
         Generalized from ~ dfrtrclrec2 .  (Contributed by RP, 1-Jun-2020.) $)
      eliunov2 $p |- ( ( R e. U /\ N e. V )
                       -> ( X e. ( C ` R )
                            <-> E. n e. N X e. ( R .^ n ) ) ) $=
        ( wcel wa cfv cv co wb wi cvv ciun wceq wrex cmpt eqid elex adantr wral
        oveq1 iuneq2d simpr ovex rgenw sylancl fvmptd3 eleq2 eliun a1i sylan9bb
        iunexg mpancom fveq1 eleq2d bibi1d imbi2d ax-mp mpbir ) BCKZFGKZLZHBAMZ
        KZHBDNZEOZKDFUAZPZQZVHHBIRDFINZVKEOZSZUBZMZKZVMPZQZVTDFVLSZTZVHWBVHIBVR
        WDRVSRVSUCVPBTDFVQVLVPBVKEUGUHVFBRKVGBCUDUEVHVGVLRKZDFUFWDRKVFVGUIWFDFB
        VKEUJUKDFVLGRURULUMWEWAHWDKZVHVMVTWDHUNWGVMPVHDHFVLUOUPUQUSAVSTZVOWCPJW
        HVNWBVHWHVJWAVMWHVIVTHBAVSUTVAVBVCVDVE $.
    $}
  $}

  ${
    $d n r C $.
    trclrec.def $e |- C = ( r e. _V |-> U_ n e. NN ( r ^r n ) ) $.

    ${
      $d n r R $.  $d n X $.
      $( Membership in the indexed union of relation exponentiation over the
         natural numbers is equivalent to the existence of at least one number
         such that the element is a member of that relationship power.
         (Contributed by RP, 2-Jun-2020.) $)
      eltrclrec $p |- ( R e. V -> ( X e. ( C ` R )
                                    <-> E. n e. NN X e. ( R ^r n ) ) ) $=
        ( wcel cn cvv cfv cv crelexp co wrex wb nnex eliunov2 mpan2 ) BDHIJHEBA
        KHEBCLMNHCIOPQABDCMIJEFGRS $.
    $}
  $}

  ${
    $d n r C $.
    rtrclrec.def $e |- C = ( r e. _V |-> U_ n e. NN0 ( r ^r n ) ) $.

    ${
      $d n r R $.  $d n X $.
      $( Membership in the indexed union of relation exponentiation over the
         natural numbers (including zero) is equivalent to the existence of at
         least one number such that the element is a member of that
         relationship power.  (Contributed by RP, 2-Jun-2020.) $)
      elrtrclrec $p |- ( R e. V -> ( X e. ( C ` R )
                                     <-> E. n e. NN0 X e. ( R ^r n ) ) ) $=
        ( wcel cn0 cvv cfv cv crelexp co wrex wb nn0ex eliunov2 mpan2 ) BDHIJHE
        BAKHEBCLMNHCIOPQABDCMIJEFGRS $.
    $}
  $}

  ${
    $d n r C N .^ $.
    briunov2.def $e |- C = ( r e. _V |-> U_ n e. N ( r .^ n ) ) $.

    ${
      $d n r R $.  $d n X $.  $d n Y $.
      $( Two classes related by the indexed union over operator values where
         the index varies the second input is equivalent to the existence of at
         least one index such that the two classes are related by that operator
         value.  (Contributed by RP, 1-Jun-2020.) $)
      briunov2 $p |- ( ( R e. U /\ N e. V )
                       -> ( X ( C ` R ) Y
                            <-> E. n e. N X ( R .^ n ) Y ) ) $=
        ( wcel wa cop cfv cv co wrex wbr df-br eliunov2 rexbii 3bitr4g ) BCLFGL
        MHINZBAOZLUDBDPEQZLZDFRHIUESHIUFSZDFRABCDEFGUDJKUAHIUETUHUGDFHIUFTUBUC
        $.
    $}
  $}

  ${
    $d n A $.  $d n B $.  $d n r C N $.  $d n r R $.
    brmptiunrelexpd.c $e |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) ) $.
    brmptiunrelexpd.r $e |- ( ph -> R e. _V ) $.
    brmptiunrelexpd.n $e |- ( ph -> N C_ NN0 ) $.
    $( If two elements are connected by an indexed union of relational powers,
       then they are connected via ` n ` instances the relation, for some
       ` n ` .  Generalization of ~ dfrtrclrec2 .  (Contributed by RP,
       21-Jul-2020.) $)
    brmptiunrelexpd $p |- ( ph -> ( A ( C ` R ) B
                                     <-> E. n e. N A ( R ^r n ) B ) ) $=
      ( cvv wcel cfv wbr cv crelexp co wrex cn0 wss nn0ex ssex briunov2 syl2anc
      wb syl ) AELMGLMZBCEDNOBCEFPQROFGSUFJAGTUAUHKGTUBUCUGDELFQGLBCHIUDUE $.
  $}

  ${
    $d n r N $.  $d n r R $.
    fvmptiunrelexplb0d.c $e |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) ) $.
    fvmptiunrelexplb0d.r $e |- ( ph -> R e. _V ) $.
    fvmptiunrelexplb0d.n $e |- ( ph -> N e. _V ) $.
    fvmptiunrelexplb0d.0 $e |- ( ph -> 0 e. N ) $.
    $( If the indexed union ranges over the zeroth power of the relation, then
       a restriction of the identity relation is a subset of the appliction of
       the function to the relation.  (Contributed by RP, 22-Jul-2020.) $)
    fvmptiunrelexplb0d $p |- ( ph -> ( _I |` ( dom R u. ran R ) )
                                     C_ ( C ` R ) ) $=
      ( cc0 crelexp co cv ciun cid wcel syl cvv wceq cdm crn cun cres cfv oveq2
      wss ssiun2s relexp0g oveq1 iuneq2d wral ovex rgenw iunexg sylancl fvmptd3
      eqcomd 3sstr3d ) ACKLMZDECDNZLMZOZPCUACUBUCUDZCBUEZAKEQUTVCUGJDEVBKUTVAKC
      LUFUHRACSQUTVDTHCSUIRAVEVCAFCDEFNZVALMZOVCSBSGVFCTDEVGVBVFCVALUJUKHAESQVB
      SQZDEULVCSQIVHDECVALUMUNDEVBSSUOUPUQURUS $.
  $}

  ${
    $d n r C N $.  $d n r R $.
    fvmptiunrelexplb0da.c $e |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) ) $.
    fvmptiunrelexplb0da.r $e |- ( ph -> R e. _V ) $.
    fvmptiunrelexplb0da.n $e |- ( ph -> N e. _V ) $.
    fvmptiunrelexplb0da.rel $e |- ( ph -> Rel R ) $.
    fvmptiunrelexplb0da.0 $e |- ( ph -> 0 e. N ) $.
    $( If the indexed union ranges over the zeroth power of the relation, then
       a restriction of the identity relation is a subset of the appliction of
       the function to the relation.  (Contributed by RP, 22-Jul-2020.) $)
    fvmptiunrelexplb0da $p |- ( ph -> ( _I |` U. U. R ) C_ ( C ` R ) ) $=
      ( cid cuni cres cdm crn cun cfv wrel wceq syl reseq2d fvmptiunrelexplb0d
      relfld eqsstrd ) ALCMMZNLCOCPQZNCBRAUFUGLACSUFUGTJCUDUAUBABCDEFGHIKUCUE
      $.
  $}

  ${
    $d n r N $.  $d n r R $.
    fvmptiunrelexplb1d.c $e |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) ) $.
    fvmptiunrelexplb1d.r $e |- ( ph -> R e. _V ) $.
    fvmptiunrelexplb1d.n $e |- ( ph -> N e. _V ) $.
    fvmptiunrelexplb1d.1 $e |- ( ph -> 1 e. N ) $.
    $( If the indexed union ranges over the first power of the relation, then
       the relation is a subset of the appliction of the function to the
       relation.  (Contributed by RP, 22-Jul-2020.) $)
    fvmptiunrelexplb1d $p |- ( ph -> R C_ ( C ` R ) ) $=
      ( c1 crelexp co cv ciun cfv wcel wss oveq2 cvv ssiun2s syl relexp1d oveq1
      wceq iuneq2d wral ovex rgenw iunexg sylancl fvmptd3 eqcomd 3sstr3d ) ACKL
      MZDECDNZLMZOZCCBPZAKEQUOURRJDEUQKUOUPKCLSUAUBACTHUCAUSURAFCDEFNZUPLMZOURT
      BTGUTCUEDEVAUQUTCUPLUDUFHAETQUQTQZDEUGURTQIVBDECUPLUHUIDEUQTTUJUKULUMUN
      $.
  $}

  ${
    brfvid.r $e |- ( ph -> R e. _V ) $.
    $( If two elements are connected by a value of the identity relation, then
       they are connected via the argument.  (Contributed by RP,
       21-Jul-2020.) $)
    brfvid $p |- ( ph -> ( A ( _I ` R ) B <-> A R B ) ) $=
      ( cid cfv cvv wcel wceq fvi syl breqd ) ADFGZDBCADHINDJEDHKLM $.
  $}

  ${
    brfvidRP.r $e |- ( ph -> R e. _V ) $.
    $d n A $.  $d n B $.  $d n r R $.
    $( If two elements are connected by a value of the identity relation, then
       they are connected via the argument.  This is an example which uses
       ~ brmptiunrelexpd .  (Contributed by RP, 21-Jul-2020.)
       (Proof modification is discouraged.) $)
    brfvidRP $p |- ( ph -> ( A ( _I ` R ) B <-> A R B ) ) $=
      ( vn vr cid cfv wbr cv crelexp co c1 csn wrex cn0 1nn0 mp1i breqd wcel wb
      dfid6 wss snssi brmptiunrelexpd wceq oveq2 rexsng cvv relexp1d 3bitrd ) A
      BCDHIJBCDFKZLMZJZFNOZPZBCDNLMZJZBCDJABCHDFUPGGFUCENQUAZUPQUDARNQUESUFUTUQ
      USUBARUOUSFNQUMNUGUNURBCUMNDLUHTUISAURDBCADUJEUKTUL $.
  $}

  ${
    fvilbd.r $e |- ( ph -> R e. _V ) $.
    $( A set is a subset of its image under the identity relation.
       (Contributed by RP, 22-Jul-2020.) $)
    fvilbd $p |- ( ph -> R C_ ( _I ` R ) ) $=
      ( cid cfv ssid cvv wcel wceq fvi syl sseqtrrid ) ABBBDEZBFABGHMBICBGJKL
      $.
  $}

  ${
    $d n r R $.
    fvilbdRP.r $e |- ( ph -> R e. _V ) $.
    $( A set is a subset of its image under the identity relation.
       (Contributed by RP, 22-Jul-2020.)
       (Proof modification is discouraged.) $)
    fvilbdRP $p |- ( ph -> R C_ ( _I ` R ) ) $=
      ( vn vr cid c1 csn dfid6 cvv wcel snex a1i 1ex snid fvmptiunrelexplb1d )
      AFBDGHZEEDICQJKAGLMGQKAGNOMP $.
  $}

  ${
    $d n A $.  $d n B $.  $d n r R $.
    brfvrcld.r $e |- ( ph -> R e. _V ) $.
    $( If two elements are connected by the reflexive closure of a relation,
       then they are connected via zero or one instances the relation.
       (Contributed by RP, 21-Jul-2020.) $)
    brfvrcld $p |- ( ph -> ( A ( r* ` R ) B
                             <-> ( A ( R ^r 0 ) B \/ A ( R ^r 1 ) B ) ) ) $=
      ( vn vr crcl wbr crelexp co cc0 c1 cn0 wcel 0nn0 1nn0 mp2an wceq oveq2 cv
      cfv cpr wrex wo dfrcl4 wss prssi a1i brmptiunrelexpd breqd rexprg bitrdi
      wb ) ABCDHUBIBCDFUAZJKZIZFLMUCZUDZBCDLJKZIZBCDMJKZIZUEZABCHDFURGFGUFEURNU
      GZALNOZMNOZVEPQLMNUHRUIUJVFVGUSVDUNPQUQVAVCFLMNNUOLSUPUTBCUOLDJTUKUOMSUPV
      BBCUOMDJTUKULRUM $.
  $}

  ${
    brfvrcld2.r $e |- ( ph -> R e. _V ) $.
    $( If two elements are connected by the reflexive closure of a relation,
       then they are equal or related by relation.  (Contributed by RP,
       21-Jul-2020.) $)
    brfvrcld2 $p |- ( ph -> ( A ( r* ` R ) B
                              <-> ( ( A e. ( dom R u. ran R )
                                      /\ B e. ( dom R u. ran R )
                                      /\ A = B )
                                    \/ A R B ) ) ) $=
      ( crcl wbr crelexp co wo cdm crn wcel wceq cid cvv breqd wa eleq2i biimpi
      cfv cc0 c1 cun w3a brfvrcld cres relexp0g relres releldmi relelrni dmresi
      syl rnresi anim12i syl2anc resieq biadanii df-3an bitr4i relexp1d orbi12d
      bitrdi bitrd ) ABCDFUAGBCDUBHIZGZBCDUCHIZGZJBDKDLUDZMZCVIMZBCNZUEZBCDGZJA
      BCDEUFAVFVMVHVNAVFBCOVIUGZGZVMAVEVOBCADPMVEVONEDPUHUMQVPVJVKRZVLRVMVPVQVL
      VPBVOKZMZCVOLZMZVQBCVOOVIUIZUJBCVOWBUKVSVJWAVKVSVJVRVIBVIULSTWAVKVTVICVIU
      NSTUOUPVIBCUQURVJVKVLUSUTVCAVGDBCADPEVAQVBVD $.
  $}

  ${
    $d n r R $.
    fvrcllb0d.r $e |- ( ph -> R e. _V ) $.
    $( A restriction of the identity relation is a subset of the reflexive
       closure of a set.  (Contributed by RP, 22-Jul-2020.) $)
    fvrcllb0d $p |- ( ph -> ( _I |` ( dom R u. ran R ) ) C_ ( r* ` R ) ) $=
      ( vn vr crcl cc0 cpr dfrcl4 cvv wcel prex a1i 0elpr01 fvmptiunrelexplb0d
      c1 ) AFBDGPHZEDEICQJKAGPLMGQKANMO $.
  $}

  ${
    $d n r R $.
    fvrcllb0da.rel $e |- ( ph -> Rel R ) $.
    fvrcllb0da.r $e |- ( ph -> R e. _V ) $.
    $( A restriction of the identity relation is a subset of the reflexive
       closure of a relation.  (Contributed by RP, 22-Jul-2020.) $)
    fvrcllb0da $p |- ( ph -> ( _I |` U. U. R ) C_ ( r* ` R ) ) $=
      ( vn vr crcl cc0 cpr dfrcl4 cvv wcel prex a1i 0elpr01 fvmptiunrelexplb0da
      c1 ) AGBEHQIZFEFJDRKLAHQMNCHRLAONP $.
  $}

  ${
    $d n r R $.
    fvrcllb1d.r $e |- ( ph -> R e. _V ) $.
    $( A set is a subset of its image under the reflexive closure.
       (Contributed by RP, 22-Jul-2020.) $)
    fvrcllb1d $p |- ( ph -> R C_ ( r* ` R ) ) $=
      ( vn vr crcl cc0 cpr dfrcl4 cvv wcel prex a1i 1elpr01 fvmptiunrelexplb1d
      c1 ) AFBDGPHZEDEICQJKAGPLMPQKANMO $.
  $}

  ${
    $d n r C $.
    brtrclrec.def $e |- C = ( r e. _V |-> U_ n e. NN ( r ^r n ) ) $.
    ${
      $d n r R $.  $d n X $.  $d n Y $.
      $( Two classes related by the indexed union of relation exponentiation
         over the natural numbers is equivalent to the existence of at least
         one number such that the two classes are related by that relationship
         power.  (Contributed by RP, 2-Jun-2020.) $)
      brtrclrec $p |- ( R e. V -> ( X ( C ` R ) Y
                                    <-> E. n e. NN X ( R ^r n ) Y ) ) $=
        ( wcel cn cvv cfv wbr cv crelexp co wrex wb nnex briunov2 mpan2 ) BDIJK
        IEFBALMEFBCNOPMCJQRSABDCOJKEFGHTUA $.
    $}
  $}

  ${
    $d n r C $.
    brrtrclrec.def $e |- C = ( r e. _V |-> U_ n e. NN0 ( r ^r n ) ) $.
    ${
      $d n r R $.  $d n X $.  $d n Y $.
      $( Two classes related by the indexed union of relation exponentiation
         over the natural numbers (including zero) is equivalent to the
         existence of at least one number such that the two classes are related
         by that relationship power.  (Contributed by RP, 2-Jun-2020.) $)
      brrtrclrec $p |- ( R e. V -> ( X ( C ` R ) Y
                                     <-> E. n e. NN0 X ( R ^r n ) Y ) ) $=
        ( wcel cn0 cvv cfv wbr cv crelexp co wrex wb nn0ex briunov2 mpan2 ) BDI
        JKIEFBALMEFBCNOPMCJQRSABDCOJKEFGHTUA $.
    $}
  $}

  ${
    $d n r C N .^ $.
    briunov2uz.def $e |- C = ( r e. _V |-> U_ n e. N ( r .^ n ) ) $.
    ${
      $d n r R $.  $d n X $.  $d n Y $.
      $( Two classes related by the indexed union over operator values where
         the index varies the second input is equivalent to the existence of at
         least one index such that the two classes are related by that operator
         value.  The index set ` N ` is restricted to an upper range of
         integers.  (Contributed by RP, 2-Jun-2020.) $)
      briunov2uz $p |- ( ( R e. U /\ N = ( ZZ>= ` M ) )
                         -> ( X ( C ` R ) Y
                              <-> E. n e. N X ( R .^ n ) Y ) ) $=
        ( wcel cuz cfv wceq cvv wbr cv co wrex wb wa simpr fvex eqeltrdi syldan
        briunov2 ) BCLZGFMNZOZGPLHIBANQHIBDRESQDGTUAUHUJUBGUIPUHUJUCFMUDUEABCDE
        GPHIJKUGUF $.
    $}
  $}

  ${
    $d n r C N .^ $.
    eliunov2uz.def $e |- C = ( r e. _V |-> U_ n e. N ( r .^ n ) ) $.

    ${
      $d n r R $.  $d n X $.
      $( Membership in the indexed union over operator values where the index
         varies the second input is equivalent to the existence of at least one
         index such that the element is a member of that operator value.  The
         index set ` N ` is restricted to an upper range of integers.
         (Contributed by RP, 2-Jun-2020.) $)
      eliunov2uz $p |- ( ( R e. U /\ N = ( ZZ>= ` M ) )
                         -> ( X e. ( C ` R )
                              <-> E. n e. N X e. ( R .^ n ) ) ) $=
        ( wcel cuz cfv wceq cvv cv co wrex wb wa simpr eqeltrdi eliunov2 syldan
        fvex ) BCKZGFLMZNZGOKHBAMKHBDPEQKDGRSUFUHTGUGOUFUHUAFLUEUBABCDEGOHIJUCU
        D $.
    $}
  $}

  ${
    $d n r C N .^ $.
    ov2ssiunov2.def $e |- C = ( r e. _V |-> U_ n e. N ( r .^ n ) ) $.

    ${
      $d x .^ $.  $d x C $.  $d n x M $.  $d x N $.  $d r R $.  $d n x R $.
      $d n x U $.  $d n x V $.
      $( Any particular operator value is the subset of the index union over a
         set of operator values.  Generalized from ~ rtrclreclem1 and
         rtrclreclem2 .  (Contributed by RP, 4-Jun-2020.) $)
      ov2ssiunov2 $p |- ( ( R e. U /\ N e. V /\ M e. N )
                          -> ( R .^ M ) C_ ( C ` R ) ) $=
        ( vx wcel w3a co cfv cv wrex simp3 wceq wa simpr oveq2d eleq2d eliunov2
        rspcedv wi biimprd 3adant3 syld ssrdv ) BCLZGHLZFGLZMZKBFENZBAOZUNKPZUO
        LZUQBDPZENZLZDGQZUQUPLZUNVAURDFGUKULUMRUNUSFSZTZUTUOUQVEUSFBEUNVDUAUBUC
        UEUKULVBVCUFUMUKULTVCVBABCDEGHUQIJUDUGUHUIUJ $.
    $}
  $}

  ${
    $d x y A $.  $d x y B $.
    $( The zeroth power of relationships is the same if and only if the union
       of their domain and ranges is the same.  (Contributed by RP,
       11-Jun-2020.) $)
    relexp0eq $p |- ( ( A e. U /\ B e. V ) ->
                      ( ( dom A u. ran A ) = ( dom B u. ran B )
                        <-> ( A ^r 0 ) = ( B ^r 0 ) ) ) $=
      ( vx vy wcel wa cdm crn cun wceq cid cres cc0 crelexp co wb wal bitri weq
      cv copab dfcleq alcom 19.3v wex ax6ev pm5.5 ax-mp 19.23v 3bitr4ri bibi12i
      wi pm5.32 ancom albii 3bitr3i eqopab2bw opabresid eqcomi eqeq12i relexp0g
      3bitr2i eqeqan12d bitr4id ) ACGZBDGZHAIAJKZBIBJKZLZMVINZMVJNZLZAOPQZBOPQZ
      LVKEUBZVIGZFEUAZHZVQVJGZVSHZRZFSZESZVTEFUCZWBEFUCZLVNVKVRWARZESZWEEVIVJUD
      WIFSWHFSZESWIWEWHFEUEWIFUFWJWDEWJVSWHUNZFSZWDVSFUGZWHUNZWHWLWJWMWNWHRFEUH
      WMWHUIUJVSWHFUKWHFUFULWKWCFWKVSVRHZVSWAHZRWCVSVRWAUOWOVTWPWBVSVRUPVSWAUPU
      MTUQTUQURTVTWBEFUSWFVLWGVMVLWFEFVIUTVAVMWGEFVJUTVAVBVDVGVHVOVLVPVMACVCBDV
      CVEVF $.
  $}

  ${
    $d x R $.  $d x V $.  $d x Z $.
    $( Simplification of zeroth power of indexed union of powers of relations.
       (Contributed by RP, 19-Jun-2020.) $)
    iunrelexp0 $p |- ( ( R e. V /\ Z C_ NN0 /\ ( { 0 , 1 } i^i Z ) =/= (/) )
                       -> ( U_ x e. Z ( R ^r x ) ^r 0 ) = ( R ^r 0 ) ) $=
      ( wcel cn0 wss cc0 c1 cin c0 crelexp ciun cun wceq eqtrdi eqtrd wral cvv
      wn cpr wne w3a cv csn df-pr ineq1i indir eqtr2i uneq1i inss2 ssequn1 mpbi
      co iuneq1 oveq1d ax-mp cdm crn dmiun iunxun equncomi 3eqtri rniun uneq12i
      uncom un4 eqtri wo wa wi df-ne incom ineq2i indi eqeq1i un00 anor 3bitr2i
      notbii notnotb disjsn bitr4i orbi12i sylbb simpl snssd dfss2 iuneq1d c0ex
      sylib oveq2 dmeqd iunxsn cid cres relexp0g ad2antll dmresi rnresi uneq12d
      rneqd unidm uneq1d relexpdmg expcom ralrimiv olc ad2antrl inss syl imim1d
      sseld ralimdv2 mpd iunss sylibr relexprng unssd ssequn2 1ex relexp1g jaoi
      ex uneq2d 3impib 3com13 adantr ssel adantl 3adant3 eqtrid wb nn0ex inex2g
      ssex unexd unexg mpancom ovex rgenw iunexg sylancl 3ad2ant2 simp1 syl2anc
      relexp0eq mpbid ) BCEZDFGZHIUAZDJZKUBZUCZADBAUDZLUNZMZHLUNZAHUEZDJZIUEZDJ
      ZNZDNZUUPMZHLUNZBHLUNZDUVDOZUURUVFOUVDUULDNZDUVCUULDUULUUSUVANZDJUVCUUKUV
      JDHIUFZUGUUSUVADUHUIUJUULDGUVIDOUUKDUKUULDULUMUIUVHUUQUVEHLADUVDUUPUOUPUQ
      UUNUVEURZUVEUSZNZBURZBUSZNZOZUVFUVGOZUUNUVNAUUTUUPURZMZAUUTUUPUSZMZNZAUVB
      UVTMZAUVBUWBMZNZNZADUVTMZADUWBMZNZNZUVQUVNUWIUWEUWANZNZUWCUWFNZUWJNZNZUWM
      UWONZUWKNZUWLUVLUWNUVMUWPUVLAUVDUVTMAUVCUVTMZUWINZUWNAUVDUUPUTAUVCDUVTVAU
      XAUWMUWIUWTUWMUWIUWTUWAUWEAUUTUVBUVTVAVBUJVBVCUVMAUVDUWBMAUVCUWBMZUWJNUWP
      AUVDUUPVDAUVCDUWBVAUXBUWOUWJAUUTUVBUWBVAUJVCVEUWQUWMUWINZUWPNUWSUWNUXCUWP
      UWIUWMVFUJUWMUWIUWOUWJVGVHUWRUWHUWKUWRUWAUWENZUWONUWHUWMUXDUWOUWEUWAVFUJU
      WAUWEUWCUWFVGVHUJVCUUNUWLUVQUWKNZUVQUUNUWHUVQUWKUUMUUJUUIUWHUVQOZUUMUUJUU
      IUXFUUMHDEZIDEZVIZUUJUUIVJZUXFVKZUUMUULKOZTZUXIUULKVLUXMDUUSJZKOZTZDUVAJZ
      KOZTZVIZTZTUXTUXIUXLUYAUXLUXNUXQNZKOUXOUXRVJUYAUULUYBKUULDUUKJDUVJJUYBUUK
      DVMUUKUVJDUVKVNDUUSUVAVOVCVPUXNUXQVQUXOUXRVRVSVTUXTWAUXPUXGUXSUXHUXPUXGTZ
      TUXGUXOUYCDHWBVTUXGWAWCUXSUXHTZTUXHUXRUYDDIWBVTUXHWAWCWDVSWEUXGUXKUXHUXGU
      XJUXFUXGUXJVJZUWHUVQUWGNZUVQUYEUWDUVQUWGUYEUWDUVQUVQNUVQUYEUWAUVQUWCUVQUY
      EUWAUVGURZUVQUYEUWAAUUSUVTMUYGUYEAUUTUUSUVTUYEUUSDGUUTUUSOUYEHDUXGUXJWFWG
      UUSDWHWKZWIAHUVTUYGWJUUOHOZUUPUVGUUOHBLWLZWMWNPUYEUYGWOUVQWPZURUVQUYEUVGU
      YKUUIUVGUYKOUXGUUJBCWQWRZWMUVQWSPQUYEUWCUVGUSZUVQUYEUWCAUUSUWBMUYMUYEAUUT
      UUSUWBUYHWIAHUWBUYMWJUYIUUPUVGUYJXBWNPUYEUYMUYKUSUVQUYEUVGUYKUYLXBUVQWTPQ
      XAUVQXCPXDUYEUWGUVQGUYFUVQOUYEUWEUWFUVQUYEUVTUVQGZAUVBRZUWEUVQGUYEUYNAFRZ
      UYOUUIUYPUXGUUJUUIUYNAFUUOFEZUUIUYNBUUOCXEXFXGZWRUYEUYNUYNAFUVBUYEUUOUVBE
      ZUYQUYNUYEUVBFUUOUYEUVAFGZUUJVIZUVBFGUUJVUAUXGUUIUUJUYTXHXIUVADFXJXKXMZXL
      XNXOAUVBUVTUVQXPXQUYEUWBUVQGZAUVBRZUWFUVQGUYEVUCAFRZVUDUUIVUEUXGUUJUUIVUC
      AFUYQUUIVUCBUUOCXRXFXGZWRUYEVUCVUCAFUVBUYEUYSUYQVUCVUBXLXNXOAUVBUWBUVQXPX
      QXSUWGUVQXTWKQYDUXHUXJUXFUXHUXJVJZUWHUWDUVQNZUVQVUGUWGUVQUWDVUGUWEUVOUWFU
      VPVUGUWEBILUNZURZUVOVUGUWEAUVAUVTMVUJVUGAUVBUVAUVTVUGUVADGUVBUVAOVUGIDUXH
      UXJWFWGUVADWHWKZWIAIUVTVUJYAUUOIOZUUPVUIUUOIBLWLZWMWNPVUGVUIBUUIVUIBOUXHU
      UJBCYBWRZWMQVUGUWFVUIUSZUVPVUGUWFAUVAUWBMVUOVUGAUVBUVAUWBVUKWIAIUWBVUOYAV
      ULUUPVUIVUMXBWNPVUGVUIBVUNXBQXAYEVUGUWDUVQGVUHUVQOVUGUWAUWCUVQVUGUYNAUUTR
      ZUWAUVQGVUGUYPVUPUUIUYPUXHUUJUYRWRVUGUYNUYNAFUUTVUGUUOUUTEZUYQUYNVUGUUTFU
      UOVUGUUSFGZUUJVIZUUTFGUUJVUSUXHUUIUUJVURXHXIUUSDFXJXKXMZXLXNXOAUUTUVTUVQX
      PXQVUGVUCAUUTRZUWCUVQGVUGVUEVVAUUIVUEUXHUUJVUFWRVUGVUCVUCAFUUTVUGVUQUYQVU
      CVUTXLXNXOAUUTUWBUVQXPXQXSUWDUVQULWKQYDYCXKYFYGXDUUNUWKUVQGZUXEUVQOUUIUUJ
      VVBUUMUUIUUJVJZUWIUWJUVQVVCUYNADRZUWIUVQGVVCUYPVVDUUIUYPUUJUYRYHVVCUYNUYN
      AFDVVCUUODEZUYQUYNUUJVVEUYQVKUUIDFUUOYIYJZXLXNXOADUVTUVQXPXQVVCVUCADRZUWJ
      UVQGVVCVUEVVGUUIVUEUUJVUFYHVVCVUCVUCAFDVVCVVEUYQVUCVVFXLXNXOADUWBUVQXPXQX
      SYKUWKUVQXTWKQYLUUNUVESEZUUIUVRUVSYMUUJUUIVVHUUMUUJDSEZVVHDFYNYPVVIUVDSEZ
      UUPSEZAUVDRVVHUVCSEVVIVVJVVIUUTUVBSSDUUSSYODUVASYOYQUVCDSSYRYSVVKAUVDBUUO
      LYTUUAAUVDUUPSSUUBUUCXKUUDUUIUUJUUMUUEUVEBSCUUGUUFUUHYL $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x N $.  $d x y U $.  $d x y V $.
    $( Any positive power of a Cartesian product of non-disjoint sets is
       itself.  (Contributed by RP, 13-Jun-2020.) $)
    relexpxpnnidm $p |- ( N e. NN
                        -> ( ( A e. U /\ B e. V /\ ( A i^i B ) =/= (/) )
                             -> ( ( A X. B ) ^r N ) = ( A X. B ) ) ) $=
      ( vx vy wcel w3a cv crelexp co wceq wi c1 oveq2 eqeq1d imbi2d cvv 3syl c0
      cin wne cxp caddc weq wa 3simpa xpexg relexp1g cn ccom simp2 relexpsucnnr
      simp1 syl2anc simp3 coeq1d simp23 xpcoidgend 3eqtrd 3exp a2d nnind ) ACHZ
      BEHZABUBUAUCZIZABUDZFJZKLZVIMZNVHVIOKLZVIMZNVHVIGJZKLZVIMZNVHVIVOOUELZKLZ
      VIMZNVHVIDKLZVIMZNFGDVJOMZVLVNVHWCVKVMVIVJOVIKPQRFGUFZVLVQVHWDVKVPVIVJVOV
      IKPQRVJVRMZVLVTVHWEVKVSVIVJVRVIKPQRVJDMZVLWBVHWFVKWAVIVJDVIKPQRVHVEVFUGZV
      ISHZVNVEVFVGUHZABCEUIZVISUJTVOUKHZVHVQVTWKVHVQVTWKVHVQIZVSVPVIULZVIVIULVI
      WLWHWKVSWMMWLVHWGWHWKVHVQUMWIWJTWKVHVQUOVIVOSUNUPWLVPVIVIWKVHVQUQURWLABWK
      VEVFVGVQUSUTVAVBVCVD $.
  $}

  ${
    $d x y A $.  $d x N $.  $d x y V $.
    $( Any power of any restriction of the identity relation is itself.
       (Contributed by RP, 12-Jun-2020.) $)
    relexpiidm $p |- ( ( A e. V /\ N e. NN0 )
                     -> ( ( _I |` A ) ^r N ) = ( _I |` A ) ) $=
      ( vx vy cn0 wcel cid cres crelexp co wceq cv wi cc0 eqeq1d imbi2d cun cvv
      oveq2 c1 caddc weq cdm crn resiexg relexp0g syl dmresi rnresi unidm eqtri
      uneq12i reseq2i eqtrdi w3a ccom relres a1i simp3 relexpsucrd simp1 coeq1d
      wrel coires1 residm eqtrd 3exp com13 a2d nn0ind impcom ) BFGACGZHAIZBJKZV
      NLZVMVNDMZJKZVNLZNVMVNOJKZVNLZNVMVNEMZJKZVNLZNVMVNWBUAUBKZJKZVNLZNVMVPNDE
      BVQOLZVSWAVMWHVRVTVNVQOVNJTPQDEUCZVSWDVMWIVRWCVNVQWBVNJTPQVQWELZVSWGVMWJV
      RWFVNVQWEVNJTPQVQBLZVSVPVMWKVRVOVNVQBVNJTPQVMVTHVNUDZVNUEZRZIZVNVMVNSGVTW
      OLACUFVNSUGUHWNAHWNAARAWLAWMAAUIAUJUMAUKULUNUOWBFGZVMWDWGWDVMWPWGWDVMWPWG
      WDVMWPUPZWFWCVNUQZVNWQVNWBVNVDWQHAURUSWDVMWPUTVAWQWRVNVNUQZVNWQWCVNVNWDVM
      WPVBVCWSVNAIVNVNAVEHAVFULUOVGVHVIVJVKVL $.
  $}

  ${
    $d x y ph $.  $d x y A $.  $d x y B $.  $d x N $.
    relexpss1d.a $e |- ( ph -> A C_ B ) $.
    relexpss1d.b $e |- ( ph -> B e. _V ) $.
    relexpss1d.n $e |- ( ph -> N e. NN0 ) $.
    $( The relational power of a subset is a subset.  (Contributed by RP,
       17-Jun-2020.) $)
    relexpss1d $p |- ( ph -> ( A ^r N ) C_ ( B ^r N ) ) $=
      ( wcel cc0 wceq crelexp co wss wi c1 oveq2 sseq12d imbi2d cvv 3syl vx cn0
      vy cn wo elnn0 sylib caddc weq ssexd relexp1d 3sstr4d ccom simp3 3ad2ant2
      cv w3a coss12d simp1 relexpsucnnr syl2anc 3exp a2d nnind cid cdm crn cres
      wa cun simpr dmss rnss jca unss12 ssres2 simpl oveq2d relexp0g eqtrd jaoi
      ex mpcom ) DUDHZDIJZUEZABDKLZCDKLZMZADUBHWFGDUFUGWDAWINZWEABUAUPZKLZCWKKL
      ZMZNABOKLZCOKLZMZNABUCUPZKLZCWRKLZMZNABWROUHLZKLZCXBKLZMZNWJUAUCDWKOJZWNW
      QAXFWLWOWMWPWKOBKPWKOCKPQRUAUCUIZWNXAAXGWLWSWMWTWKWRBKPWKWRCKPQRWKXBJZWNX
      EAXHWLXCWMXDWKXBBKPWKXBCKPQRWKDJZWNWIAXIWLWGWMWHWKDBKPWKDCKPQRABCWOWPEABS
      ABCSFEUJZUKACSFUKULWRUDHZAXAXEXKAXAXEXKAXAUQZWSBUMZWTCUMZXCXDXLWSWTBCXKAX
      AUNAXKBCMZXAEUOURXLBSHZXKXCXMJAXKXPXAXJUOXKAXAUSZBWRSUTVAXLCSHZXKXDXNJAXK
      XRXAFUOXQCWRSUTVAULVBVCVDWEAWIWEAVIZVEBVFZBVGZVJZVHZVECVFZCVGZVJZVHZWGWHX
      SAYBYFMZYCYGMWEAVKZAXOXTYDMZYAYEMZVIYHEXOYJYKBCVLBCVMVNXTYDYAYEVOTYBYFVEV
      PTXSWGBIKLZYCXSDIBKWEAVQZVRXSAXPYLYCJYIXJBSVSTVTXSWHCIKLZYGXSDICKYMVRXSAX
      RYNYGJYIFCSVSTVTULWBWAWC $.
  $}

  ${
    $d a i .^ $.  $d b .^ $.  $d c .^ $.  $d a i I $.  $d k I $.  $d a i j J $.
    $d b J $.  $d k J $.  $d c k K $.  $d d X $.  $d d Y $.  $d d Z $.
    $d a d i j $.  $d b d j $.  $d c d k $.
    comptiunov2.x $e |- X = ( a e. _V |-> U_ i e. I ( a .^ i ) ) $.
    comptiunov2.y $e |- Y = ( b e. _V |-> U_ j e. J ( b .^ j ) ) $.
    comptiunov2.z $e |- Z = ( c e. _V |-> U_ k e. K ( c .^ k ) ) $.
    comptiunov2.i $e |- I e. _V $.
    comptiunov2.j $e |- J e. _V $.
    comptiunov2.k $e |- K = ( I u. J ) $.
    comptiunov2.1 $e |- U_ k e. I ( d .^ k )
                        C_ U_ i e. I ( U_ j e. J ( d .^ j ) .^ i ) $.
    comptiunov2.2 $e |- U_ k e. J ( d .^ k )
                        C_ U_ i e. I ( U_ j e. J ( d .^ j ) .^ i ) $.
    comptiunov2.3 $e |- U_ i e. I ( U_ j e. J ( d .^ j ) .^ i )
                        C_ U_ k e. ( I u. J ) ( d .^ k ) $.
    $( The composition two indexed unions is sometimes a similar indexed union.
       (Contributed by RP, 10-Jun-2020.) $)
    comptiunov2i $p |- ( X o. Y ) = Z $=
      ( ccom wfun wceq cvv cv ciun funmpt2 funco mp2an cdm cfv wral crn wss ssv
      co wa ovex iunex dmmpti sseqtrri dmcosseq ax-mp eqtri unex eqeltri eqtr4i
      cun wcel vex eleqtrri fvco weq oveq1 iuneq2d fvmpt fveq2i 3eqtri raleqbii
      elv eqeq12i iunxun unssi eqsstri eqssi iuneq1 a1i mprgbir eqfunfv biimprd
      mp2ani ) HIUDZUEZJUEZWOJUFZHUEIUEZWPKUGAEKUHZAUHZDUSZUIZHOUJLUGBFLUHZBUHZ
      DUSZUIZIPUJZHIUKULMUGCGMUHZCUHZDUSZUIZJQUJWPWQUTZWOUMZJUMZUFZNUHZWOUNZXQJ
      UNZUFZNXNUOZWRXNUGXOXNIUMZUGIUPZHUMZUQXNYBUFYCUGYDYCURKUGXCHAEXBRWTXADVAV
      BOVCVDHIVEVFLUGXGIBFXFSXDXEDVAVBPVCZVGZMUGXLJCGXKGEFVKZUGTEFRSVHVIZXIXJDV
      AVBQVCVJYAAEBFXQXEDUSZUIZXADUSZUIZCGXQXJDUSZUIZUFZNUGXTYONXNUGYFXRYLXSYNX
      RXQIUNZHUNZYJHUNZYLWSXQYBVLXRYQUFXHXQUGYBNVMYEVNXQHIVOULYPYJHYPYJUFNLXQXG
      YJUGILNVPBFXFYIXDXQXEDVQVRPBFYISXQXEDVAVBZVSWCVTYJUGVLYRYLUFYSKYJXCYLUGHW
      TYJUFAEXBYKWTYJXADVQVROAEYKRYJXADVAVBVSVFWAXSYNUFNMXQXLYNUGJMNVPCGXKYMXIX
      QXJDVQVRQCGYMYHXQXJDVAVBVSWCWDWBYOXQUGVLYLCYGYMUIZYNYLYTUCYTCEYMUIZCFYMUI
      ZVKYLCEFYMWEUUAUUBYLUAUBWFWGWHGYGUFYNYTUFTCGYGYMWIVFVJWJWKXMWRXPYAUTNWOJW
      LWMWNUL $.
  $}

  ${
    $d a b c d i j k $.
    $( The reflexive closure is idempotent.  (Contributed by RP,
       13-Jun-2020.) $)
    corclrcl $p |- ( r* o. r* ) = r* $=
      ( vi vj vk vd crelexp cc0 c1 crcl cun cv ciun oveq2 wcel wceq ax-mp eqtri
      co cvv wss cn0 va vb vc cpr dfrcl4 prex unidm eqcomi csn cbviunv 1ex ovex
      iunxsn iunex relexp1g snsspr2 iunss1 eqsstri 0elpr01 ssiun2s unss12 mp2an
      eqimssi df-pr iuneq1 iunxun c0ex cin wne 0nn0 1nn0 prssi elini iunrelexp0
      c0 vex ne0ii mp3an uneq12i 3sstr4i comptiunov2i ) ABCEFGUDZWBWBHHHUAUBUCD
      AUAUEBUBUECUCUEFGUFZWCWBWBIZWBWBUGUHCWBDJZCJZEQZKZAGUIZBWBWEBJZEQZKZAJZEQ
      ZKZAWBWNKZWHWLWOCBWBWGWKWFWJWEELUJWOWLWOWLGEQZWLAGWNWQUKWMGWLELUMWLRMWQWL
      NBWBWKWCWEWJEULUNWLRUOOPZUHPWIWBSWOWPSFGUPAWIWBWNUQOURZWSWEFEQZWLIZWHWHIZ
      WPCWDWGKWTWHSZWLWHSXAXBSFWBMXCUSCWBWGFWTWFFWEELUTOWLWHBCWBWKWGWJWFWEELUJV
      CWTWHWLWHVAVBWPAFUIZWIIZWNKZXAWBXENWPXFNFGVDAWBXEWNVEOXFAXDWNKZWOIXAAXDWI
      WNVFXGWTWOWLXGWLFEQZWTAFWNXHVGWMFWLELUMWERMWBTSZWBWBVHZVOVIXHWTNDVPFTMGTM
      XIVJVKFGTVLVBFXJFWBWBUSUSVMVQBWERWBVNVRPWRVSPPCWBWBWGVFVTWA $.
  $}

  ${
    $d n r C N $.
    iunrelexpmin1.def $e |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) ) $.

    ${
      $d s N $.  $d n r R $.  $d s x y R $.  $d n r V $.  $d s x y V $.
      $d n s x $.  $d s x y $.
      $( The indexed union of relation exponentiation over the natural numbers
         is the minimum transitive relation that includes the relation.
         (Contributed by RP, 4-Jun-2020.) $)
      iunrelexpmin1 $p |- ( ( R e. V /\ N = NN )
                            -> A. s ( ( R C_ s /\ ( s o. s ) C_ s )
                                      -> ( C ` R ) C_ s ) ) $=
        ( wcel cn wceq wa cv wss wi crelexp co c1 sseq1d imbi2d vx vy ccom ciun
        cfv cvv simplr simpr oveq1d iuneq12d elex adantr nnex iunex a1i fvmptd2
        ovex relexp1g anbi1d wral caddc oveq2 weq simprl w3a simp2l relexpaddnn
        simp1 1nn syl3anc simp2rr simp3 simp2rl trrelssd eqsstrrd 3exp ralrimiv
        a2d nnind com12 iunss sylibr ex sylbird sseq1 imbitrrid mpcom alrimiv )
        BEIZDJKZLZBFMZNZWLWLUCWLNZLZBAUEZWLNZOZFWPCJBCMZPQZUDZKZWKWRWKGBCDGMZWS
        PQZUDXAUFAUFHWKXCBKZLZCDJXDWTWIWJXEUGXFXCBWSPWKXEUHUIUJWIBUFIWJBEUKULXA
        UFIWKCJWTUMBWSPUQUNUOUPWKWRXBWOXAWLNZOZWIXHWJWIWOBRPQZWLNZWNLZXGWIXJWMW
        NWIXIBWLBEURSUSWIXKXGWIXKLZWTWLNZCJUTXGXLXMCJWSJIXLXMXLBUAMZPQZWLNZOXLX
        JOXLBUBMZPQZWLNZOXLBXQRVAQZPQZWLNZOXLXMOUAUBWSXNRKZXPXJXLYCXOXIWLXNRBPV
        BSTUAUBVCZXPXSXLYDXOXRWLXNXQBPVBSTXNXTKZXPYBXLYEXOYAWLXNXTBPVBSTUACVCZX
        PXMXLYFXOWTWLXNWSBPVBSTWIXJWNVDXQJIZXLXSYBYGXLXSYBYGXLXSVEZYAXRXIUCZWLY
        HYGRJIZWIYIYAKYGXLXSVHYJYHVIUOYGWIXKXSVFBRXQEVGVJYHWLXRXIXJWNWIYGXSVKYG
        XLXSVLXJWNWIYGXSVMVNVOVPVRVSVTVQCJWTWLWAWBWCWDULXBWQXGWOWPXAWLWETWFWGWH
        $.
    $}
  $}

  ${
    $d x y I $.  $d x y J $.  $d x y K $.  $d x y R $.  $d x y V $.
    $( With exponents limited to the counting numbers, the composition of
       powers of a relation is the relation raised to the product of exponents.
       (Contributed by RP, 13-Jun-2020.) $)
    relexpmulnn $p |- ( ( ( R e. V /\ I = ( J x. K ) )
                      /\ ( J e. NN /\ K e. NN ) )
                      -> ( ( R ^r J ) ^r K ) = ( R ^r I ) ) $=
      ( vx wcel cmul co wceq cn crelexp wi c1 caddc oveq2 oveq2d eqeq12d imbi2d
      eqtrd vy wa w3a cv weq cvv ovexd relexp1d cr simp1 nnre ax-1rid 3syl ccom
      eqcomd ovex relexpsucnnr sylancr simp3 coeq1d simp21 nnmulcld relexpaddnn
      simp22 syl3anc nncnd 1cnd adddid mulridd eqtr2d 3exp a2d nnind 3expd impd
      impcom simplr ) AEGZBCDHIZJZUBZCKGZDKGZUBZUBZACLIZDLIZAVSLIZABLIWDWAWGWHJ
      ZWDVRVTWIWCWBVRVTWIMMWCWBVRVTWIWBVRVTUCZWFFUDZLIZACWKHIZLIZJZMWJWFNLIZACN
      HIZLIZJZMWJWFUAUDZLIZACWTHIZLIZJZMWJWFWTNOIZLIZACXEHIZLIZJZMWJWIMFUADWKNJ
      ZWOWSWJXJWLWPWNWRWKNWFLPXJWMWQALWKNCHPQRSFUAUEZWOXDWJXKWLXAWNXCWKWTWFLPXK
      WMXBALWKWTCHPQRSWKXEJZWOXIWJXLWLXFWNXHWKXEWFLPXLWMXGALWKXECHPQRSWKDJZWOWI
      WJXMWLWGWNWHWKDWFLPXMWMVSALWKDCHPQRSWJWPWFWRWJWFUFWJACLUGUHWJCWQALWJWQCWJ
      WBCUIGWQCJWBVRVTUJCUKCULUMUOQTWTKGZWJXDXIXNWJXDXIXNWJXDUCZXFXAWFUNZXHXOWF
      UFGXNXFXPJACLUPXNWJXDUJZWFWTUFUQURXOXPAXBCOIZLIZXHXOXPXCWFUNZXSXOXAXCWFXN
      WJXDUSUTXOXBKGWBVRXTXSJXOCWTXNWBVRVTXDVAZXQVBYAXNWBVRVTXDVDACXBEVCVETXOXR
      XGALXOXGXBWQOIXRXOCWTNXOCYAVFZXOWTXQVFXOVGVHXOWQCXBOXOCYBVIQVJQTTVKVLVMVN
      VPVOVPWEVSBALWEBVSVRVTWDVQUOQT $.
  $}

  $( With ordered exponents, the composition of powers of a relation is the
     relation raised to the product of exponents.  (Contributed by RP,
     13-Jun-2020.) $)
  relexpmulg $p |- ( ( ( R e. V /\ I = ( J x. K ) /\ ( I = 0 -> J <_ K ) )
                     /\ ( J e. NN0 /\ K e. NN0 ) )
                     -> ( ( R ^r J ) ^r K ) = ( R ^r I ) ) $=
    ( cn0 wcel wa cmul co wceq cc0 cle wi crelexp oveq2d 3eqtrd syl ex cvv jcnd
    wbr w3a cn wo elnn0 relexpmulnn 3adantl3 expcom simprr simpll simplr mul01d
    nncnd wn simpl nnnle0 adantl breq2d mtbird pm2.21d exp32 3impd jaoi cid cdm
    sylbi crn cun cres simpr1 eqtrd oveq1d dmexg rnexg unexd relexpiidm syl2anc
    relexp0g simpr2 nn0cnd mul02d eqtr2d jaod biimtrid impcom ) CFGZDFGZHAEGZBC
    DIJZKZBLKZCDMUBZNZUCZACOJZDOJZABOJZKZWHWGWOWSNZWGCUDGZCLKZUEWHWTCUFWHXAWTXB
    WHDUDGZDLKZUEXAWTNZDUFXCXEXDXAXCWTWOXAXCHZWSWIWKXFWSWNABCDEUGUHUIUIXDXAWTXD
    XAHZWIWKWNWSXGWIWKWNWSNXGWIWKHZHZWNWSXIWLWMXIBWJCLIJLXGWIWKUJXIDLCIXDXAXHUK
    PXICXICXDXAXHULUNUMQXIXGWMUOXGXHUPXGWMCLMUBZXAXJUOXDCUQURXGDLCMXDXAUPUSUTRU
    AVAVBVCSVDVGWHXBWTWHXBHZWOWSXKWOHZWQVEAVFZAVHZVIZVJZDOJZXPWRXLWPXPDOXLWPALO
    JZXPXLCLAOWHXBWOULZPXLWIXRXPKXKWIWKWNVKZAEVSRZVLVMXLXOTGZWHXQXPKXLWIYBXTWIX
    MXNTTAEVNAEVOVPRWHXBWOUKZXODTVQVRXLWRXRXPXLBLAOXLBWJLDIJLXKWIWKWNVTXLCLDIXS
    VMXLDXLDYCWAWBQPYAWCQSSWDWEWFWF $.

  ${
    $d D j x y $.  $d D k x y $.  $d D l $.  $d D m $.  $d N k x $.  $d j l $.
    $d j m $.  $d k l $.  $d k m $.  $d m y $.
    $( The union of relational powers to positive multiples of ` N ` is a
       subset to the transitive closure raised to the power of ` N ` .
       (Contributed by RP, 15-Jun-2020.) $)
    trclrelexplem $p |- ( N e. NN -> U_ k e. NN ( ( D ^r k ) ^r N )
                                     C_ ( U_ j e. NN ( D ^r j ) ^r N ) ) $=
      ( vl vm cn cv crelexp co ciun wss c1 wceq oveq2 iuneq2d sseq12d wcel ccom
      cvv vx vy caddc cbviunv eqtri ovex relexp1g mp1i iuneq2i nnex iunex ax-mp
      weq 3eqtr4i eqimssi oveq1d coeq12d ss2iun ssiun2s coss1 mprg eqsstri wral
      syl ralrimivw sstrid adantl relexpsucnnr mpan adantr coeq2i coiun 3sstr4d
      wa eqtrdi ex nnind ) CGACHZIJZUAHZIJZKZBGABHZIJZKZVTIJZLCGVSMIJZKZWEMIJZL
      CGVSUBHZIJZKZWEWJIJZLZCGVSWJMUCJZIJZKZWEWOIJZLZCGVSDIJZKZWEDIJZLUAUBDVTMN
      ZWBWHWFWIXCCGWAWGVTMVSIOPVTMWEIOQUAUBUMZWBWLWFWMXDCGWAWKVTWJVSIOPVTWJWEIO
      QVTWONZWBWQWFWRXECGWAWPVTWOVSIOPVTWOWEIOQVTDNZWBXAWFXBXFCGWAWTVTDVSIOPVTD
      WEIOQWHWICGVSKZWEWHWIXGEGAEHZIJZKWECEGVSXIVRXHAIOUDEBGXIWDXHWCAIOUDUECGWG
      VSVSTRZWGVSNVRGRAVRIUFZVSTUGUHUIWETRZWIWENBGWDUJAWCIUFUKZWETUGULUNUOWJGRZ
      WNWSXNWNVNCGWKVSSZKZFGWMAFHZIJZSZKZWQWRWNXPXTLXNWNXPFGWLXRSZKZXTXPFGXRWJI
      JZXRSZKZYBCFGXOYDCFUMZWKYCVSXRYFVSXRWJIVRXQAIOZUPZYGUQUDYDYALZYEYBLFGFGYD
      YAURXQGRYCWLLYICGWKXQYCYHUSYCWLXRUTVDVAVBWNYAXSLZFGVCYBXTLWNYJFGWLWMXRUTV
      EFGYAXSURVDVFVGXNWQXPNWNXNCGWPXOXJXNWPXONXKVSWJTVHVIPVJXNWRXTNWNXNWRWMWES
      ZXTXLXNWRYKNXMWEWJTVHVIYKWMFGXRKZSXTWEYLWMBFGWDXRWCXQAIOUDVKFWMXRGVLUEVOV
      JVMVPVQ $.
  $}

  ${
    $d n r C N $.
    iunrelexpmin2.def $e |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) ) $.
    ${
      $d s N $.  $d n r R $.  $d s x y R $.  $d n r V $.  $d s x y V $.
      $d n s x $.  $d s x y $.

      $( The indexed union of relation exponentiation over the natural numbers
         (including zero) is the minimum reflexive-transitive relation that
         includes the relation.  (Contributed by RP, 4-Jun-2020.) $)
      iunrelexpmin2 $p |- ( ( R e. V /\ N = NN0 )
                            -> A. s ( ( ( _I |` ( dom R u. ran R ) ) C_ s
                                        /\ R C_ s /\ ( s o. s ) C_ s )
                                      -> ( C ` R ) C_ s ) ) $=
        ( wcel cn0 wceq cv wss wi crelexp co c1 sseq1d oveq2 imbi2d cid cdm crn
        vx vy wa cun cres ccom w3a cfv ciun simplr simpr oveq1d iuneq12d adantr
        cvv elex nn0ex ovex iunex a1i fvmptd2 cc0 relexp0g relexp1g 3anbi12d cn
        wral wo elnn0 caddc weq simpr2 simp1 simp2l relexpaddnn syl3anc simp2r3
        1nn simp3 simp2r2 trrelssd eqsstrrd 3exp a2d nnind imbitrrid jaoi sylbi
        simpr1 com12 ralrimiv iunss sylibr ex sylbird sseq1 mpcom alrimiv ) BEI
        ZDJKZUFZUABUBBUCUGUHZFLZMZBXFMZXFXFUIXFMZUJZBAUKZXFMZNZFXKCJBCLZOPZULZK
        ZXDXMXDGBCDGLZXNOPZULXPURAURHXDXRBKZUFZCDJXSXOXBXCXTUMYAXRBXNOXDXTUNUOU
        PXBBURIXCBEUSUQXPURIXDCJXOUTBXNOVAVBVCVDXDXMXQXJXPXFMZNZXBYCXCXBXJBVEOP
        ZXFMZBQOPZXFMZXIUJZYBXBYEXGYGXHXIXBYDXEXFBEVFRXBYFBXFBEVGRVHXBYHYBXBYHU
        FZXOXFMZCJVJYBYIYJCJXNJIZYIYJYKXNVIIZXNVEKZVKYIYJNZXNVLYLYNYMYIBUDLZOPZ
        XFMZNYIYGNYIBUELZOPZXFMZNYIBYRQVMPZOPZXFMZNYNUDUEXNYOQKZYQYGYIUUDYPYFXF
        YOQBOSRTUDUEVNZYQYTYIUUEYPYSXFYOYRBOSRTYOUUAKZYQUUCYIUUFYPUUBXFYOUUABOS
        RTUDCVNZYQYJYIUUGYPXOXFYOXNBOSRTXBYEYGXIVOYRVIIZYIYTUUCUUHYIYTUUCUUHYIY
        TUJZUUBYSYFUIZXFUUIUUHQVIIZXBUUJUUBKUUHYIYTVPUUKUUIWAVCUUHXBYHYTVQBQYRE
        VRVSUUIXFYSYFYEYGXIXBUUHYTVTUUHYIYTWBYEYGXIXBUUHYTWCWDWEWFWGWHYIYJYMYEX
        BYEYGXIWLYMXOYDXFXNVEBOSRWIWJWKWMWNCJXOXFWOWPWQWRUQXQXLYBXJXKXPXFWSTWIW
        TXA $.
    $}
  $}

  $( With exponents limited to 0 and 1, the composition of powers of a relation
     is the relation raised to the minimum of exponents.  (Contributed by RP,
     12-Jun-2020.) $)
  relexp01min $p |- ( ( ( R e. V /\ I = if ( J < K , J , K ) )
                        /\ ( J e. { 0 , 1 } /\ K e. { 0 , 1 } ) )
                      -> ( ( R ^r J ) ^r K ) = ( R ^r I ) ) $=
    ( cc0 c1 wcel clt wbr wceq crelexp w3a simp1 oveq2d eqtrd simp2 oveq12d cvv
    co cpr wa cif wo wi elpri cid cdm crn cun dmresi rnresi uneq12i unidm eqtri
    cres reseq2i simp3l relexp0g syl dmexg rnexg unexd resiexd simp3r 0re ltnri
    3syl breq12d mtbiri iffalsed 3eqtrd 3eqtr4a 3exp relexp1d 0lt1 ltnsymi mp1i
    1re mtbird eqtr4d jaoi ovex relexp1g mpbiri iftrued 3eqtr4d jaod imp syl2an
    wn impcom ) CFGUAZHZDWMHZUBAEHZBCDIJZCDUCZKZUBZACLTZDLTZABLTZKZWNCFKZCGKZUD
    ZDFKZDGKZUDZWTXDUEZWOCFGUFDFGUFXGXJXKXGXHXKXIXEXHXKUEXFXEXHWTXDXEXHWTMZUGUG
    AUHZAUIZUJZUPZUHZXPUIZUJZUPZXPXBXCXSXOUGXSXOXOUJXOXQXOXRXOXOUKXOULUMXOUNUOU
    QXLXBXPFLTZXTXLXAXPDFLXLXAAFLTZXPXLCFALXEXHWTNZOXLWPYBXPKXEXHWPWSURZAEUSUTZ
    PXEXHWTQZRXLWPXPSHYAXTKYDWPXOSWPXMXNSSAEVAAEVBVCVDXPSUSVHPXLXCYBXPXLBFALXLB
    WRDFXEXHWPWSVEXLWQCDXLWQFFIJFVFVGXLCFDFIYCYFVIVJVKYFVLOYEPVMVNXFXHWTXDXFXHW
    TMZXBYBXCYGXAADFLYGXAAGLTZAYGCGALXFXHWTNZOYGAEXFXHWPWSURVOPXFXHWTQZRYGBFALY
    GBWRDFXFXHWPWSVEYGWQCDYGWQGFIJZFGIJZYKWKYGVPFGVFVSVQVRYGCGDFIYIYJVIVTVKYJVL
    OWAVNWBXEXIXKUEXFXEXIWTXDXEXIWTMZYBGLTZYBXBXCYBSHYNYBKYMAFLWCYBSWDVRYMXAYBD
    GLYMCFALXEXIWTNZOXEXIWTQZRYMBFALYMBWRCFXEXIWPWSVEYMWQCDYMWQYLVPYMCFDGIYOYPV
    IWEWFYOVLOWGVNXFXIWTXDXFXIWTMZXBYHXCYQXAADGLYQXAYHAYQCGALXFXIWTNZOYQAEXFXIW
    PWSURVOPXFXIWTQZRYQBGALYQBWRDGXFXIWPWSVEYQWQCDYQWQGGIJGVSVGYQCGDGIYRYSVIVJV
    KYSVLOWAVNWBWHWIWJWL $.

  $( Repeated raising a relation to the first power is idempotent.
     (Contributed by RP, 12-Jun-2020.) $)
  relexp1idm $p |- ( R e. V -> ( ( R ^r 1 ) ^r 1 ) = ( R ^r 1 ) ) $=
    ( wcel c1 clt wbr cif wceq wa cc0 cpr crelexp co ifid eqcomi 1elpr01 pm3.2i
    jctr relexp01min sylancl ) ABCZUADDDEFZDDGZHZIDJDKCZUEIADLMZDLMUFHUAUDUCDUB
    DNORUEUEPPQADDDBST $.

  $( Repeated raising a relation to the zeroth power is idempotent.
     (Contributed by RP, 12-Jun-2020.) $)
  relexp0idm $p |- ( R e. V -> ( ( R ^r 0 ) ^r 0 ) = ( R ^r 0 ) ) $=
    ( wcel cc0 clt wbr cif wceq wa c1 cpr crelexp ifid eqcomi jctr prid1 pm3.2i
    co c0ex relexp01min sylancl ) ABCZUBDDDEFZDDGZHZIDDJKCZUFIADLRZDLRUGHUBUEUD
    DUCDMNOUFUFDJSPZUHQADDDBTUA $.

  ${
    $d x y A $.  $d x N $.  $d x y V $.
    $( Absorption law for zeroth power of a relation.  (Contributed by RP,
       17-Jun-2020.) $)
    relexp0a $p |- ( ( A e. V /\ N e. NN0 )
                     -> ( ( A ^r N ) ^r 0 ) C_ ( A ^r 0 ) ) $=
      ( wcel crelexp co cc0 wss wceq wi oveq2 oveq1d sseq1d imbi2d cid cun cres
      c1 cvv ax-mp vx vy cn0 cn wo elnn0 cv weq relexp1g ssid eqsstrdi w3a ccom
      caddc simp2 simp1 wa relexpsucnnr syl2anc cdm crn ovex coexg relexp0g syl
      dmcoss rncoss unss12 mp2an ssres2 resundi ssun1 sseqtrrid adantr sseqtrri
      mpan ssun2 simpr unssd eqsstrid 3adant1 sstrd eqsstrd 3exp a2d relexp0idm
      sstrid nnind sylan9eq eqimss ex jaoi sylbi impcom ) BUCDZACDZABEFZGEFZAGE
      FZHZWOBUDDZBGIZUEWPWTJZBUFXAXCXBWPAUAUGZEFZGEFZWSHZJWPAREFZGEFZWSHZJWPAUB
      UGZEFZGEFZWSHZJWPAXKRUNFZEFZGEFZWSHZJXCUAUBBXDRIZXGXJWPXSXFXIWSXSXEXHGEXD
      RAEKLMNUAUBUHZXGXNWPXTXFXMWSXTXEXLGEXDXKAEKLMNXDXOIZXGXRWPYAXFXQWSYAXEXPG
      EXDXOAEKLMNXDBIZXGWTWPYBXFWRWSYBXEWQGEXDBAEKLMNWPXIWSWSWPXHAGEACUILWSUJUK
      XKUDDZWPXNXRYCWPXNXRYCWPXNULZXQXLAUMZGEFZWSYDWPYCXQYFIYCWPXNUOZYCWPXNUPWP
      YCUQXPYEGEAXKCURLUSYDYFOAUTZXLVAZPZQZWSYDWPYFYKHYGWPYFOYEUTZYEVAZPZQZYKWP
      YESDZYFYOIXLSDZWPYPAXKEVBZXLASCVCVPYESVDVEYNYJHZYOYKHYLYHHYMYIHYSXLAVFXLA
      VGYLYHYMYIVHVIYNYJOVJTUKVEWPXNYKWSHYCWPXNUQZYKOYHQZOYIQZPWSOYHYIVKYTUUAUU
      BWSWPUUAWSHXNWPOYHAVAZPZQZUUAWSYHUUDHUUAUUEHYHUUCVLYHUUDOVJTACVDVMVNYTUUB
      XMWSUUBOXLUTZYIPZQZXMYIUUGHUUBUUHHYIUUFVQYIUUGOVJTYQXMUUHIYRXLSVDTVOWPXNV
      RWGVSVTWAWBWCWDWEWHXBWPWTXBWPUQWRWSIWTXBWPWRWSGEFWSXBWQWSGEBGAEKLACWFWIWR
      WSWJVEWKWLWMWN $.
  $}

  $( The composition of powers of a Cartesian product of non-disjoint sets is
     the Cartesian product raised to the minimum exponent.  (Contributed by RP,
     13-Jun-2020.) $)
  relexpxpmin $p |- ( ( ( A e. U /\ B e. V /\ ( A i^i B ) =/= (/) )
                     /\ ( I = if ( J < K , J , K ) /\ J e. NN0 /\ K e. NN0 ) )
                     -> ( ( ( A X. B ) ^r J ) ^r K ) = ( ( A X. B ) ^r I ) ) $=
    ( clt wceq wcel w3a crelexp co wi cc0 wo wa simpl1 oveq2d cvv wbr cif c0 cn
    cn0 cin wne cxp elnn0 ifeqor andi biimpi mpan2 eqtr relexpxpnnidm 3ad2antl3
    orim12i 3ad2antl2 oveq1d eqtrd 3eqtr4d 3exp1 eqcomd oveq12d jaoi 3syl com13
    imp simp3 simp2 simp1 nngt0d eqbrtrd iftrued 3eqtrd cid cdm crn cres simpr1
    cun simpr2 xpexd dmexg rnexg jca unexg nnnn0d relexpiidm syl2anc simpl2 syl
    relexp0g simpl3 ex syld3an3 3exp biimtrid 3ad2ant2 wn nn0nlt0 breq2d mtbird
    jaod iffalsed relexp0idm syl3c sylbi 3imp31 impcom ) DEFHUAZEFUBZIZEUEJZFUE
    JZKACJZBGJZABUFUCUGZKZABUHZELMZFLMZXTDLMZIZXOXNXMXSYDNZXOFUDJZFOIZPXNXMYENZ
    NZFUIYFYIYGXNEUDJZEOIZPZYFYHEUIZYFYJYHYKXMYJYFYEXMXMXLEIZQZXMXLFIZQZPZDEIZD
    FIZPYJYFYENNZXMYNYPPZYRXKEFUJXMUUBQYRXMYNYPUKULUMYOYSYQYTDXLEUNDXLFUNUQYSUU
    AYTYSYJYFXSYDYSYJYFKXSQZXTFLMZXTYBYCYFYSXSUUDXTIZYJYFXSUUEABCFGUOVHUPUUCYAX
    TFLYJYSXSYAXTIZYFYJXSUUFABCEGUOZVHZURZUSUUCYCYAXTUUCDEXTLYSYJYFXSRSUUIUTVAV
    BYTYJYFXSYDYTYJYFKXSQZYAXTFDLYJYTXSUUFYFUUHURUUJDFYTYJYFXSRVCVDVBVEVFVGYFYK
    XMYEYFYKXMDOIZYEYFYKXMKZDXLEOYFYKXMVIUULXKEFUULEOFHYFYKXMVJZUULFYFYKXMVKVLV
    MVNUUMVOYFYKUUKKZXSYDUUNXSQZVPXTVQZXTVRZWAZVSZFLMZUUSYBYCUUOUURTJZXOUUTUUSI
    UUOXTTJZUUPTJZUUQTJZQUVAUUOABCGUUNXPXQXRVTUUNXPXQXRWBWCZUVBUVCUVDXTTWDXTTWE
    WFUUPUUQTTWGVFUUOFYFYKUUKXSRWHUURFTWIWJUUOYAUUSFLUUOYAXTOLMZUUSUUOEOXTLYFYK
    UUKXSWKSUUOUVBUVFUUSIUVEXTTWMWLZUTUSUUOYCUVFUUSUUODOXTLYFYKUUKXSWNSUVGUTVAW
    OWPWQXDWRYGXNXMYEYGXNXMKZYGYLUUKYEYGXNXMVKZXNYGYLXMXNYLYMULWSUVHDXLFOYGXNXM
    VIUVHXKEFUVHXKEOHUAZXNYGUVJWTXMEXAWSUVHFOEHUVIXBXCXEUVIVOYGYJUUKYENYKYGYJUU
    KXSYDYGYJUUKKZXSQZYAOLMUVFYBYCUVLYAXTOLUVKXSUUFYJYGXSUUFNUUKUUGWSVHUSUVLFOY
    ALYGYJUUKXSRSUVLDOXTLYGYJUUKXSWNSVAVBYGYKUUKXSYDYGYKUUKKZXSQZUVFOLMZUVFYBYC
    UVNUVBUVOUVFIUVNABCGUVMXPXQXRVTUVMXPXQXRWBWCXTTXFWLUVNYAUVFFOLUVNEOXTLYGYKU
    UKXSWKSYGYKUUKXSRVDUVNDOXTLYGYKUUKXSWNSVAVBXDXGWQVEXHXIXJ $.

  $( The composition of two powers of a relation is a subset of the relation
     raised to the sum of those exponents.  This is equality where ` R ` is a
     relation as shown by ~ relexpaddd or when the sum of the powers isn't 1 as
     shown by ~ relexpaddg .  (Contributed by RP, 3-Jun-2020.) $)
  relexpaddss $p |- ( ( N e. NN0 /\ M e. NN0 /\ R e. V )
                      -> ( ( R ^r N ) o. ( R ^r M ) )
                         C_ ( R ^r ( N + M ) ) ) $=
    ( wcel crelexp co ccom caddc wss cc0 wceq w3a syl cres ccnv oveq2d 3ad2ant3
    c1 eqtrd cn0 cn wo wi elnn0 biimpi relexpaddnn eqimss 3exp cuz cfv elnn1uz2
    c2 cid cdm crn wrel relco dfrel2 ax-mp cnvco cnvresid coeq2i coires1 3eqtri
    cun cnvss resss sstri eqsstrri cnvcnvss a1i simp1 relexp0g relexp1g coeq12d
    simp2 oveq12d addlidd 3sstr4d cnvexg relexpuzrel syl2anc eluz2nn relexpnndm
    1cnd df-rn ssun2 sstrdi relssres eqtrid simp3 eluzge2nn0 relexpcnvd 3eqtr4d
    cvv 3adant1 cnveqb sylancr mpbird coeq1d oveq1d eluzelcn jaod biimtrid jaoi
    wb cc eqsstri addridd 3adant2 ssun1 coeq2d cin resres inidm reseq2i 3eqtr4a
    00id 3imp ) CUAEZBUAEZADEZACFGZABFGZHZACBIGZFGZJZYBBUBEZBKLZUCYAYCYIUDZBUEY
    AYJYLYKYACUBEZCKLZUCZYJYLUDZYAYOCUEUFZYMYPYNYMYJYCYIYMYJYCMYFYHLZYIABCDUGYF
    YHUHZNUIYJBSLZBUMUJUKZEZUCYNYLBULYNYTYLUUBYNYTYCYIYNYTYCMZUNAUOZAUPZVFZOZAH
    ZAYFYHUUHAJUUCUUHAPZPZAUUHUUHPZPZUUJUUHUQZUULUUHLZUUGAURUUMUUNUUHUSUFUTUULU
    UIUUFOZPZUUJUUKUUOJZUULUUPJUUKUUOLUUQUUKUUIUUGPZHUUIUUGHUUOUUGAVAUURUUGUUIU
    UFVBZVCUUIUUFVDVEUUKUUOUHUTUUKUUOVGUTUUOUUIJUUPUUJJUUIUUFVHUUOUUIVGUTVIVJAV
    KVIVLUUCYDUUGYEAUUCYDAKFGZUUGUUCCKAFYNYTYCVMZQYCYNUUTUUGLZYTADVNZRTUUCYEASF
    GZAUUCBSAFYNYTYCVQZQYCYNUVDALZYTADVOZRZTVPUUCYHUVDAUUCYGSAFUUCYGKSIGSUUCCKB
    SIUVAUVEVRUUCSUUCWFVSTQUVHTVTUIYNUUBYCYIYNUUBYCMZYRYIUVIUUGYEHZYEYFYHUVIUVJ
    YELZUVJPZYEPZLZUVIUUIBFGZUUGHZUVOUVLUVMUVIUVPUVOUUFOZUVOUVOUUFVDUVIUVOUQZUV
    OUOZUUFJUVQUVOLUVIUUBUUIWPEZUVRYNUUBYCVQZYCYNUVTUUBADWARZUUIBWPWBWCUVIUVSUU
    IUOZUUFUVIYJUVTUVSUWCJUVIUUBYJUWABWDNUWBUUIBWPWEWCUWCUUEUUFAWGUUEUUDWHVJWIU
    VOUUFWJWCWKUVIUVLUVMUURHUVPUUGYEVAUVIUVMUVOUURUUGUVIABDYNUUBYCWLUVIUUBYBUWA
    BWMNWNZUURUUGLUVIUUSVLVPWKUWDWOUVIUVJUQYEUQZUVKUVNXGUUGYEURUUBYCUWEYNABDWBW
    QUVJYEWRWSWTUVIYDUUGYEUVIYDUUTUUGUVICKAFYNUUBYCVMZQYCYNUVBUUBUVCRTXAUVIYGBA
    FUVIYGKBIGBUVICKBIUWFXBUVIBUVIUUBBXHEUWAUMBXCNVSTQWOYSNUIXDXEXFNYAYOYKYLUDZ
    YQYMUWGYNYMCSLZCUUAEZUCZUWGYMUWJCULUFUWHUWGUWIUWHYKYCYIUWHYKYCMZAUUGHZAYFYH
    UWLAJUWKUWLAUUFOAAUUFVDAUUFVHXIVLUWKYDAYEUUGUWKYDUVDAUWKCSAFUWHYKYCVMZQYCUW
    HUVFYKUVGRZTUWKYEUUTUUGUWKBKAFUWHYKYCVQZQYCUWHUVBYKUVCRTVPUWKYHUVDAUWKYGSAF
    UWKYGSKIGSUWKCSBKIUWMUWOVRUWKSUWKWFXJTQUWNTVTUIUWIYKYCYIUWIYKYCMZYRYIUWPYDU
    UGHZYDYFYHUWPUWQYDUUFOZYDYDUUFVDUWPYDUQZYDUOZUUFJUWRYDLUWIYCUWSYKACDWBXKUWP
    UWTUUDUUFUWPYMYCUWTUUDJUWPUWIYMUWIYKYCVMZCWDNUWIYKYCWLACDWEWCUUDUUEXLWIYDUU
    FWJWCWKUWPYEUUGYDUWPYEUUTUUGUWPBKAFUWIYKYCVQZQYCUWIUVBYKUVCRTXMUWPYGCAFUWPY
    GCKIGCUWPBKCIUXBQUWPCUWPUWICXHEUXAUMCXCNXJTQWOYSNUIXFNYNYKYCYIYNYKYCMZYRYIU
    XCUUGUUGHZUUGYFYHUXDUUGUUFOUNUUFUUFXNZOUUGUUGUUFVDUNUUFUUFXOUXEUUFUNUUFXPXQ
    VEUXCYDUUGYEUUGUXCYDUUTUUGUXCCKAFYNYKYCVMZQYCYNUVBYKUVCRZTUXCYEUUTUUGUXCBKA
    FYNYKYCVQZQUXGTVPUXCYHUUTUUGUXCYGKAFUXCYGKKIGZKUXCCKBKIUXFUXHVRUXIKLUXCXSVL
    TQUXGTXRYSNUIXFNXDXEXT $.

  ${
    $d n r C N $.
    mptiunrelexp.def $e |- C = ( r e. _V |-> U_ n e. N ( r ^r n ) ) $.

    ${
      $d x y z C $.  $d i j n x y z M $.  $d i j x y z N $.
      $d i j n x y z R $.  $d r R $.  $d i j n x y z V $.
      $( The indexed union of relation exponentiation over upper integers is a
         transive relation.  Generalized from ~ rtrclreclem3 .  (Contributed by
         RP, 4-Jun-2020.) $)
      iunrelexpuztr $p |- ( ( R e. V /\ N = ( ZZ>= ` M ) /\ M e. NN0 )
                             -> ( ( C ` R ) o. ( C ` R ) ) C_ ( C ` R ) ) $=
        ( vx vy vi vz vj wcel cv crelexp wbr wrex wa cvv cuz cfv wceq cn0 co wi
        w3a wal wss caddc ovexd simprlr simpll2 eleqtrd simpll3 simprll eluznn0
        ccom wex syl2anc uzaddcl simplr 3eltr4d vex brcogw mp3an simprr simpll1
        simprl relexpaddss syl3anc oveq2d sseqtrrd ssbrd syl5 impr jca spcimedv
        exlimdvv reeanv r2ex bitr3i df-rex 3imtr4g alrimiv briunov2uz weq oveq2
        ex cotr breqd cbvrexvw bitrdi anbi12d imbi12d albidv bitrid biimprd mpd
        3adant3 ) BFNZEDUAUBZUCZDUDNZUGZIOZJOZBKOZPUEZQZKERZXGLOZBMOZPUEZQZMERZ
        SZXFXLBCOZPUEZQZCERZUFZLUHZJUHZIUHZBAUBZYFURYFUIZXEYDIXEYCJXEYBLXEXHENZ
        XMENZSZXJXOSZSZMUSKUSZXRENZXTSZCUSZXQYAXEYLYPKMXEYOYLCXMXHUJUEZTXEXMXHU
        JUKXEXRYQUCZSZYLYOYSYLSZYNXTYTYQXBXREYTXMXBNZXHUDNZYQXBNYTXMEXBYSYHYIYK
        ULXAXCXDYRYLUMZUNYTXDXHXBNZUUBXAXCXDYRYLUOYTXHEXBYSYHYIYKUPUUCUNXHDUQZU
        TXHDXMVAUTXEYRYLVBUUCVCYSYJYKXTYKXFXLXNXIURZQZYSYJSZXTXFTNZXLTNZXGTNZYK
        UUGUFIVDLVDJVDUUIUUJUUKUGYKUUGXFXLXNXITTXGTVEWIVFUUHUUFXSXFXLUUHUUFBYQP
        UEZXSUUHXMUDNZUUBXAUUFUULUIUUHXDUUAUUMXAXCXDYRYJUOZUUHXMEXBYSYHYIVGXAXC
        XDYRYJUMZUNXMDUQUTUUHXDUUDUUBUUNUUHXHEXBYSYHYIVIUUOUNUUEUTXAXCXDYRYJVHB
        XHXMFVJVKUUHXRYQBPXEYRYJVBVLVMVNVOVPVQWIVRVSXQYKMERKERYMXJXOKMEEVTYKKME
        EWAWBXTCEWCWDWEWEWEXAXCYEYGUFXDXAXCSZYGYEYGXFXGYFQZXGXLYFQZSZXFXLYFQZUF
        ZLUHZJUHZIUHUUPYEIJLYFWJUUPUVCYDIUUPUVBYCJUUPUVAYBLUUPUUSXQUUTYAUUPUUQX
        KUURXPUUPUUQXFXGXSQZCERXKABFCPDEXFXGGHWFUVDXJCKECKWGXSXIXFXGXRXHBPWHWKW
        LWMUUPUURXGXLXSQZCERXPABFCPDEXGXLGHWFUVEXOCMECMWGXSXNXGXLXRXMBPWHWKWLWM
        WNABFCPDEXFXLGHWFWOWPWPWPWQWRWTWS $.
    $}
  $}

  $( BEGIN WIP

  ${
  relexpempty.1 $e |- ( ph -> Rel R ) $.
  relexpempty.2 $e |- ( ph -> R e. V ) $.
  relexpempty.3 $e |- ( ph -> N e. NN0 ) $.
  relexpempty.4 $e |- ( ph -> ( dom ( R ^r N ) i^i ran ( R ^r N ) ) = (/) ) $.
  relexpempty $p |- ( ph -> ( M e. NN -> ( R ^r ( N + M ) ) = (/) ) ) $=
      ? $.
  $}

  END WIP $)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Transitive closure of a relation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d a k t $.  $d a n r s z $.  $d k n r $.  $d k s $.  $d n r t $.
    $( Transitive closure of a relation, expressed as indexed union of powers
       of relations.  (Contributed by RP, 5-Jun-2020.) $)
    dftrcl3 $p |- t+ = ( r e. _V |-> U_ n e. NN ( r ^r n ) ) $=
      ( vz va vk vt vs cvv cv wss ccom wa cmpt cn crelexp co ciun wcel c1 wceq
      ctcl cab cint df-trcl cfv relexp1g 1nn oveq1 iuneq2d oveq2 cbviunv eqtrdi
      nnex weq cbvmptv ov2ssiunov2 mp3an23 eqsstrrd cuz nnuz 1nn0 iunrelexpuztr
      cn0 wb wi wal fvex trcleq2lem a1i alrimiv elabgt sylancr mpbir2and intss1
      syl wral vex elab eqid iunrelexpmin1 mpan2 biimtrid ralrimiv ssint sylibr
      19.21bi eqssd ovex iunex fvmpt eqtrd mpteq2ia eqtri ) UABHBIZCIZJWOWOKWOJ
      LZCUBZUCZMBHANWNAIZOPZQZMBCUDBHWRXAWNHRZWRWNDHANDIZWSOPZQZMZUEZXAXBWRXGXB
      XGWQRZWRXGJXBXHWNXGJZXGXGKXGJZXBWNWNSOPZXGWNHUFXBNHRSNRXKXGJUMUGXFWNHEOSN
      HFDFHXEENFIZEIZOPZQZDFUNZXEANXLWSOPZQXOXPANXDXQXCXLWSOUHUIAENXQXNWSXMXLOU
      JUKULUOZUPUQURXBNSUSUETSVCRXJUTVAXFWNESNHFXRVBUQXBXGHRWOXGTWPXIXJLZVDVEZC
      VFXHXSVDWNXFVGXBXTCXTXBWOXGWNVHVIVJWPXSCXGHVKVLVMXGWQVNVOXBXGGIZJZGWQVPXG
      WRJXBYBGWQYAWQRWNYAJYAYAKYAJLZXBYBWPYCCYAGVQWOYAWNVHVRXBYCYBVEZGXBNNTYDGV
      FNVSXFWNENHGFXRVTWAWFWBWCGXGWQWDWEWGDWNXEXAHXFDBUNANXDWTXCWNWSOUHUIXFVSAN
      WTUMWNWSOWHWIWJWKWLWM $.
  $}

  ${
    $d n A $.  $d n B $.  $d n r R $.
    brfvtrcld.r $e |- ( ph -> R e. _V ) $.
    $( If two elements are connected by the transitive closure of a relation,
       then they are connected via ` n ` instances the relation, for some
       counting number ` n ` .  (Contributed by RP, 22-Jul-2020.) $)
    brfvtrcld $p |- ( ph -> ( A ( t+ ` R ) B
                                     <-> E. n e. NN A ( R ^r n ) B ) ) $=
      ( vr ctcl cn dftrcl3 cn0 wss nnssnn0 a1i brmptiunrelexpd ) ABCHDEIGEGJFIK
      LAMNO $.
  $}

  ${
    $d n r R $.
    fvtrcllb1d.r $e |- ( ph -> R e. _V ) $.
    $( A set is a subset of its image under the transitive closure.
       (Contributed by RP, 22-Jul-2020.) $)
    fvtrcllb1d $p |- ( ph -> R C_ ( t+ ` R ) ) $=
      ( vn vr ctcl cn dftrcl3 cvv wcel nnex a1i c1 1nn fvmptiunrelexplb1d ) AFB
      DGEDEHCGIJAKLMGJANLO $.
  $}

  ${
    $d n r R $.  $d n V $.
    $( The transitive closure of a relation commutes with the relation.
       (Contributed by RP, 18-Jul-2020.) $)
    trclfvcom $p |- ( R e. V
                        -> ( ( t+ ` R ) o. R ) = ( R o. ( t+ ` R ) ) ) $=
      ( vn vr wcel cvv ctcl cfv ccom wceq elex cn cv crelexp co wa caddc eqtrdi
      ciun c1 relexpsucnnr relexpsucnnl eqtr3d iuneq2dv oveq1 iuneq2d nnex ovex
      dftrcl3 iunex fvmpt coeq1d coiun1 coeq2d coiun 3eqtr4d syl ) ABEAFEZAGHZA
      IZAUSIZJABKURCLACMZNOZAIZSZCLAVCIZSZUTVAURCLVDVFURVBLEPAVBTQONOVDVFAVBFUA
      AVBFUBUCUDURUTCLVCSZAIVEURUSVHADACLDMZVBNOZSVHFGVIAJCLVJVCVIAVBNUEUFCDUIC
      LVCUGAVBNUHUJUKZULCVCALUMRURVAAVHIVGURUSVHAVKUNCAVCLUORUPUQ $.
  $}

  ${
    $d n r R $.  $d n s R $.
    $( The converse of the transitive closure is equal to the transitive
       closure of the converse relation.  (Contributed by RP, 19-Jul-2020.) $)
    cnvtrclfv $p |- ( R e. V -> `' ( t+ ` R ) = ( t+ ` `' R ) ) $=
      ( vn vr vs wcel cvv ctcl cfv ccnv wceq cn cv crelexp co syl oveq1 iuneq2d
      ciun dftrcl3 elex wral nnnn0 relexpcnv sylan expcom ralrimiv iuneq2 iunex
      cn0 nnex ovex fvmpt cnveqd cnviun eqtrdi cnvexg 3eqtr4d ) ABFAGFZAHIZJZAJ
      ZHIZKABUAUSCLACMZNOZJZSZCLVBVDNOZSZVAVCUSVFVHKZCLUBVGVIKUSVJCLVDLFZUSVJVK
      VDUJFUSVJVDUCAVDGUDUEUFUGCLVFVHUHPUSVACLVESZJVGUSUTVLDACLDMZVDNOZSVLGHVMA
      KCLVNVEVMAVDNQRCDTCLVEUKAVDNULUIUMUNCLVEUOUPUSVBGFVCVIKAGUQEVBCLEMZVDNOZS
      VIGHVOVBKCLVPVHVOVBVDNQRCETCLVHUKVBVDNULUIUMPURP $.
  $}

  ${
    $d a b c d i j k x y $.
    $( The transitive closure is idempotent.  (Contributed by RP,
       16-Jun-2020.) $)
    cotrcltrcl $p |- ( t+ o. t+ ) = t+ $=
      ( vi vj vk vc vd vx crelexp cn ctcl nnex cv co ciun c1 oveq2 cvv wceq wss
      sseq1d ccom va vb dftrcl3 cun unidm eqcomi csn 1ex iunxsn wcel ovex iunex
      vy relexp1g ax-mp cbviunv eqtri 1nn snssi iunss1 mp2b eqsstri iunss caddc
      weq eqimssi wa simpl relexpsucnnr sylancr coss1 adantl coeq2i trclfvcotrg
      cfv oveq1 iuneq2d fvmpt elv coeq12i 3sstr3i sstrdi eqsstrd mprgbir iuneq1
      ex nnind sseqtri comptiunov2i ) ABCGHHHIIIUAUBDEAUAUCBUBUCCDUCZJJHHUDZHHU
      EUFZCHEKZCKZGLZMZANUGZBHWMBKZGLZMZAKZGLZMZAHXBMZXCWPXCWTNGLZWPANXBXEUHXAN
      WTGOUIXEWTWPWTPUJZXEWTQBHWSJWMWRGUKULZWTPUNUOBCHWSWOWRWNWMGOUPZUQZUQUFNHU
      JWQHRXCXDRURNHUSAWQHXBUTVAVBZXJXDWPCWKWOMZXDWPRXBWPRZAHAHXBWPVCWTFKZGLZWP
      RXEWPRWTUMKZGLZWPRZWTXONVDLZGLZWPRZXLFUMXAXMNQXNXEWPXMNWTGOSFUMVEXNXPWPXM
      XOWTGOSXMXRQXNXSWPXMXRWTGOSFAVEXNXBWPXMXAWTGOSXEWPXIVFXOHUJZXQXTYAXQVGZXS
      XPWTTZWPYBXFYAXSYCQXGYAXQVHWTXOPVIVJYBYCWPWTTZWPXQYCYDRYAXPWPWTVKVLYDWPWP
      TZWPWTWPWPXHVMWMIVOZYFTYFYEWPWMVNYFWPYFWPYFWPQEDWMCHDKZWNGLZMWPPIDEVECHYH
      WOYGWMWNGVPVQWJCHWOJWMWNGUKULVRVSZYIVTYIWAVBWBWCWFWGWDHWKQWPXKQWLCHWKWOWE
      UOWHWI $.
  $}

  ${
    $d k x A $.  $d x y A $.  $d k x B $.  $d x y B $.  $d k x R $.
    $d x y R $.  $d r R $.  $d k x V $.  $d x y V $.  $d k r $.
    $( Lower bound for image under a transitive closure.  (Contributed by RP,
       1-Jul-2020.) $)
    trclimalb2 $p |- ( ( R e. V /\ ( R " ( A u. B ) ) C_ B )
                       -> ( ( t+ ` R ) " A ) C_ B ) $=
      ( vk vx wcel cima cn cv crelexp co wceq imaeq1d wi c1 oveq2 sseq1d imbi2d
      wss vr vy cun wa ctcl cfv ciun cvv elex adantr oveq1 iuneq2d dftrcl3 nnex
      ovex iunex fvmpt imaiun1 eqtrdi syl wral caddc relexp1g ssun1 imass2 mp1i
      weq simpr sstrd eqsstrd w3a simp2l simp1 ccom relexpsucnnl imaco 3ad2ant3
      syl2anc ssun2 simp2r 3exp a2d nnind com12 ralrimiv iunss sylibr ) CDGZCAB
      UCZHZBTZUDZCUEUFZAHZEICEJZKLZAHZUGZBWLCUHGZWNWRMWHWSWKCDUIUJWSWNEIWPUGZAH
      WRWSWMWTAUACEIUAJZWOKLZUGWTUHUEXACMEIXBWPXACWOKUKULEUAUMEIWPUNCWOKUOUPUQN
      EIWPAURUSUTWLWQBTZEIVAWRBTWLXCEIWOIGWLXCWLCFJZKLZAHZBTZOWLCPKLZAHZBTZOWLC
      UBJZKLZAHZBTZOWLCXKPVBLZKLZAHZBTZOWLXCOFUBWOXDPMZXGXJWLXSXFXIBXSXEXHAXDPC
      KQNRSFUBVGZXGXNWLXTXFXMBXTXEXLAXDXKCKQNRSXDXOMZXGXRWLYAXFXQBYAXEXPAXDXOCK
      QNRSFEVGZXGXCWLYBXFWQBYBXEWPAXDWOCKQNRSWLXICAHZBWHXIYCMWKWHXHCACDVCNUJWLY
      CWJBAWITYCWJTWLABVDAWICVEVFWHWKVHVIVJXKIGZWLXNXRYDWLXNXRYDWLXNVKZXQCXMHZB
      YEWHYDXQYFMYDWHWKXNVLYDWLXNVMWHYDUDZXQCXLVNZAHYFYGXPYHACXKDVONCXLAVPUSVRY
      EYFCBHZBXNYDYFYITWLXMBCVEVQYEYIWJBBWITYIWJTYEBAVSBWICVEVFYDWHWKXNVTVIVIVJ
      WAWBWCWDWEEIWQBWFWGVJ $.
  $}

  ${
    $d f g r s R $.  $d f U $.  $d f V $.  $d f W $.  $d f g r s X $.
    $d f Y $.
    $( Two ways to indicate two elements are related by the transitive closure
       of a relation.  (Contributed by RP, 1-Jul-2020.) $)
    brtrclfv2 $p |- ( ( X e. U /\ Y e. V /\ R e. W ) ->
                      ( X ( t+ ` R ) Y
                        <-> Y e. |^| { f | ( R " ( { X } u. f ) ) C_ f } )
                    ) $=
      ( vr vg vs wcel wss wa cima wb wceq wsbc cvv syl ax-mp w3a cfv wbr cv cab
      ctcl ccom cint csn cun cop df-br trclfv 3ad2ant3 elimasng 3adant3 3bitr4d
      a1i breqd wrex intimasn 3ad2ant1 wal wex cxp simpl3 snex vex xpex sylancl
      wi unexg trclfvlb unssad trclfvcotrg cin wne simpl1 inelcm syl2anc xpima2
      c0 snidg unssbd imass1 eqsstrrd imaundir simpr imassrn rnxpss sstri unssd
      crn eqsstrid trclimalb2 eqssd sbcan csb sbcssg csbconstg csbvargi sseq12i
      fvex bitri csbcog coeq12i anbi12i sbceq2g csbima12 imaeq1i imaeq2i 3eqtri
      eqtri eqeq2i sylbbr syl21anc spesbcd ex eqeq1 imaeq1 eqeq2d rexab2 bitrdi
      weq rexbidv elab imbitrrdi intss1 alrimiv ssintab sylibr adantr eqsstrrid
      syl6 imaco sylan9ss jca imaex imaundi sseq1i unss bitr4i sseq12d cleq2lem
      imaeq2 id bitrid eqeltrd exlimiv sylbi mpgbir eqtrd eleq2d bitrd ) FBKZGD
      KZAEKZUAZFGAUFUBZUCZGAHUDZLZUVAUVAUGZUVALZMZHUEZUHZFUIZNZKZGAUVHCUDZUJZNZ
      UVKLZCUEZUHZKUURFGUVGUCZFGUKUVGKZUUTUVJUVQUVROUURFGUVGULURUUQUUOUUTUVQOUU
      PUUQUUSUVGFGHAEUMUSUNUUOUUPUVJUVROUUQUVGFGBDUOUPUQUURUVIUVPGUURUVIIUDZJUD
      ZUVHNZPZJUVFUTZIUEZUHZUVPUUOUUPUVIUWEPUUQIUVFFBJVAVBUURUWEUVPUURUVNUWEUVK
      LZVKZCVCUWEUVPLUURUWGCUURUVNUVKUWDKZUWFUURUVNUVEUVKUVAUVHNZPZMZHVDZUWHUUR
      UVNUWLUURUVNMZUWKHAUVHUVKVEZUJZUFUBZUWMAUWPLZUWPUWPUGZUWPLZUVKUWPUVHNZPZU
      WKHUWPQZUWMUWORKZUWQUWMUUQUWNRKUXCUUOUUPUUQUVNVFUVHUVKFVGCVHZVIAUWNERVLVJ
      ZUXCAUWNUWPUWORVMZVNSUWSUWMUWOVOURUWMUVKUWTUWMUVKUWNUVHNZUWTUWMUVHUVHVPWB
      VQZUXGUVKPUWMFUVHKZUXIUXHUWMUUOUXIUUOUUPUUQUVNVRFBWCSZUXJFUVHUVHVSVTUVHUV
      KUVHWASUWMUWNUWPLUXGUWTLUWMAUWNUWPUWMUXCUWOUWPLUXEUXFSWDUWNUWPUVHWESWFUWM
      UXCUWOUVLNZUVKLUWTUVKLUXEUWMUXKUVMUWNUVLNZUJUVKAUWNUVLWGUWMUVMUXLUVKUURUV
      NWHUXLUVKLUWMUXLUWNWMUVKUWNUVLWIUVHUVKWJWKURWLWNUVHUVKUWORWOVTWPUXBUVEHUW
      PQZUWJHUWPQZMUWQUWSMZUXAMUVEUWJHUWPWQUXMUXOUXNUXAUXMUVBHUWPQZUVDHUWPQZMUX
      OUVBUVDHUWPWQUXPUWQUXQUWSUXPHUWPAWRZHUWPUVAWRZLZUWQUWPRKZUXPUXTOUWOUFXCZH
      UWPAUVARWSTUXRAUXSUWPUYAUXRAPUYBHUWPARWTTHUWPUYBXAZXBXDUXQHUWPUVCWRZUXSLZ
      UWSUYAUXQUYEOUYBHUWPUVCUVARWSTUYDUWRUXSUWPUYDUXSUXSUGZUWRUYAUYDUYFPUYBHUW
      PUVAUVARXETUXSUWPUXSUWPUYCUYCXFXMUYCXBXDXGXDUXNUVKHUWPUWIWRZPZUXAUYAUXNUY
      HOUYBHUWPUVKUWIRXHTUYGUWTUVKUYGUXSHUWPUVHWRZNUWPUYINUWTHUWPUVHUVAXIUXSUWP
      UYIUYCXJUYIUVHUWPUYAUYIUVHPUYBHUWPUVHRWTTXKXLXNXDXGXOXPXQXRUWCUWLIUVKUXDI
      CYDZUWCUVKUWAPZJUVFUTUWLUYJUWBUYKJUVFUVSUVKUWAXSYEUVEUYKUWJJHJHYDZUWAUWIU
      VKUVTUVAUVHXTZYAYBYCYFYGUVKUWDYHYNYIUVNCUWEYJYKUVPUWELZUURUYNUWCUVPUVSLZV
      KIUWCIUVPYJUWCUVSUVOKZUYOUWCUVEUVSUWIPZMZHVDUYPUVEUWBUYQJHUYLUWAUWIUVSUYM
      YAYBUYRUYPHUYRUVSUWIUVOUVEUYQWHUYRAUVHNZUWILZAUWINZUWILZMZUWIUVOKUVEVUCUY
      QUVEUYTVUBUVBUYTUVDAUVAUVHWEYLUVBUVDVUAUVAUWINZUWIAUVAUWIWEUVDVUDUVCUVHNU
      WIUVAUVAUVHYOUVCUVAUVHWEYMYPYQYLUVNVUCCUWIUVAUVHHVHYRUVNUYSUVKLAUVKNZUVKL
      ZMZUWJVUCUVNUYSVUEUJZUVKLVUGUVMVUHUVKAUVHUVKYSYTUYSVUEUVKUUAUUBVUFVUBUVKU
      WIUYSUWJVUEVUAUVKUWIUVKUWIAUUEUWJUUFUUCUUDUUGYFYKUUHUUIUUJUVSUVOYHSUUKURW
      PUULUUMUUN $.
  $}

  ${
    $d m n r R $.  $d m n V $.
    $( The transitive closure of a relation may be decomposed into a union of
       the relation and the composition of the relation with its transitive
       closure.  (Contributed by RP, 18-Jul-2020.) $)
    trclfvdecomr $p |- ( R e. V
                        -> ( t+ ` R ) = ( R u. ( ( t+ ` R ) o. R ) ) ) $=
      ( vn vr vm wcel ctcl cfv cn cv crelexp co ciun ccom cun wceq c1 cuz oveq2
      c2 cvv elex oveq1 iuneq2d dftrcl3 nnex ovex iunex fvmpt syl csn cmin nnuz
      2eluzge1 uzsplit ax-mp 2m1e1 oveq2i cz 1z fzsn eqtri uneq1i 3eqtri iuneq1
      cfz iunxun 1ex iunxsn relexp1g coeq1d coiun1 caddc adantl eluzp1p1 eleq2s
      uz2m1nn 1p1e2 fveq2i eleqtrdi 3ad2ant3 wa relexpsucnnr eqcomd wb eluzelcn
      sylan2 cc npcan1 3syl eqeq1d mpbid cbviuneq12dv eqtrid eqtrd uneq12d ) AB
      FZAGHZCIACJZKLZMZAWRANZOZWQAUAFZWRXAPABUBZDACIDJZWSKLZMXAUAGXFAPZCIXGWTXF
      AWSKUCUDCDUECIWTUFAWSKUGUHUIUJWQXAAQKLZCTRHZWTMZOZXCXACQUKZXJOZWTMZCXMWTM
      ZXKOXLIXNPXAXOPIQRHZQTQULLZVFLZXJOZXNUMTXQFXQXTPUNQTUOUPXSXMXJXSQQVFLZXMX
      RQQVFUQURQUSFYAXMPUTQVAUPVBVCVDCIXNWTVEUPCXMXJWTVGXPXIXKCQWTXIVHWSQAKSVIV
      CVDWQXIAXKXBABVJWQXBXKWQXBEIAEJZKLZMZANZXKWQWRYDAWQXDWRYDPXEDAEIXFYBKLZMY
      DUAGXHEIYFYCXFAYBKUCUDEDUEEIYCUFAYBKUGUHUIUJVKWQYEEIYCANZMXKEYCAIVLWQECIY
      GXJWTAWSQULLZKLZANZAYBQVMLZKLZYHYKWSXJFZYHIFZWQWSVQZVNYBIFZYKXJFWQYPYKQQV
      MLZRHZXJYKYRFYBXQIQYBVOUMVPYQTRVRVSVTVNYBYHPZWQYGYJPYMYSYCYIAYBYHAKSVKWAW
      SYKPWQWTYLPYPWSYKAKSWAWQYPWBYLYGAYBBWCWDWQYMWBAYHQVMLZKLZYJPZWTYJPZYMWQYN
      UUBYOAYHBWCWGYMUUBUUCWEWQYMUUAWTYJYMWSWHFYTWSPUUAWTPTWSWFWSWIYTWSAKSWJWKV
      NWLWMWNWOWDWPWNWO $.
  $}

  $( The transitive closure of a relation may be decomposed into a union of the
     relation and the composition of the relation with its transitive closure.
     (Contributed by RP, 18-Jul-2020.) $)
  trclfvdecoml $p |- ( R e. V
                        -> ( t+ ` R ) = ( R u. ( R o. ( t+ ` R ) ) ) ) $=
    ( wcel ctcl cfv ccom cun trclfvdecomr trclfvcom uneq2d eqtrd ) ABCZADEZAMAF
    ZGAAMFZGABHLNOAABIJK $.

  $( The domain of the transitive closure is equal to the domain of the
     relation.  (Contributed by RP, 18-Jul-2020.)
     (Proof modification is discouraged.) $)
  dmtrclfvRP $p |- ( R e. V -> dom ( t+ ` R ) = dom R ) $=
    ( wcel ctcl cfv cdm ccom cun trclfvdecomr dmun wss wceq dmcoss ssequn2 mpbi
    dmeqd eqtri eqtrdi ) ABCZADEZFATAGZHZFZAFZSTUBABIPUCUDUAFZHZUDAUAJUEUDKUFUD
    LTAMUEUDNOQR $.

  $( The range of the transitive closure is equal to the range of the relation.
     (Contributed by RP, 19-Jul-2020.)  (Proof modification is discouraged.) $)
  rntrclfvRP $p |- ( R e. V -> ran ( t+ ` R ) = ran R ) $=
    ( wcel ctcl cfv crn ccnv cdm df-rn cnvtrclfv dmeqd cvv wceq cnvexg dmtrclfv
    syl eqtr4di eqtrd eqtrid ) ABCZADEZFUAGZHZAFZUAITUCAGZDEZHZUDTUBUFABJKTUGUE
    HZUDTUELCUGUHMABNUELOPAIQRS $.

  $( The range of the transitive closure is equal to the range of the relation.
     (Contributed by RP, 18-Jul-2020.)  (Proof modification is discouraged.) $)
  rntrclfv $p |- ( R e. V -> ran ( t+ ` R ) = ran R ) $=
    ( wcel ctcl cfv crn ccom cun trclfvdecoml rnun wss wceq rncoss ssequn2 mpbi
    rneqd eqtri eqtrdi ) ABCZADEZFAATGZHZFZAFZSTUBABIPUCUDUAFZHZUDAUAJUEUDKUFUD
    LATMUEUDNOQR $.

  ${
    $d a k t $.  $d a n r s z $.  $d k n r $.  $d k s $.  $d n r t $.
    $( Reflexive-transitive closure of a relation, expressed as indexed union
       of powers of relations.  Generalized from ~ dfrtrcl2 .  (Contributed by
       RP, 5-Jun-2020.) $)
    dfrtrcl3 $p |- t* = ( r e. _V |-> U_ n e. NN0 ( r ^r n ) ) $=
      ( vz va vk vt vs cvv cv wss ccom w3a cmpt cn0 crelexp ciun wcel cc0 sseq2
      co crtcl cid cdm crn cun cres cab cint df-rtrcl relexp0g nn0ex 0nn0 oveq1
      cfv weq iuneq2d oveq2 cbviunv eqtrdi cbvmptv ov2ssiunov2 mp3an23 eqsstrrd
      c1 relexp1g 1nn0 cuz wceq nn0uz iunrelexpuztr wb wal fvex coeq12d sseq12d
      wi id 3anbi123d a1i alrimiv elabgt sylancr mpbir3and intss1 syl wral elab
      vex eqid iunrelexpmin2 mpan2 19.21bi biimtrid ralrimiv ssint sylibr eqssd
      ovex iunex fvmpt eqtrd mpteq2ia eqtri ) UABHUBBIZUCXDUDUEUFZCIZJZXDXFJZXF
      XFKZXFJZLZCUGZUHZMBHANXDAIZOTZPZMBCUIBHXMXPXDHQZXMXDDHANDIZXNOTZPZMZUNZXP
      XQXMYBXQYBXLQZXMYBJXQYCXEYBJZXDYBJZYBYBKZYBJZXQXEXDROTZYBXDHUJXQNHQZRNQZY
      HYBJUKULYAXDHEORNHFDFHXTENFIZEIZOTZPZDFUOZXTANYKXNOTZPYNYOANXSYPXRYKXNOUM
      UPAENYPYMXNYLYKOUQURUSUTZVAVBVCXQXDXDVDOTZYBXDHVEXQYIVDNQYRYBJUKVFYAXDHEO
      VDNHFYQVAVBVCXQNRVGUNVHYJYGVIULYAXDERNHFYQVJVBXQYBHQXFYBVHZXKYDYEYGLZVKVP
      ZCVLYCYTVKXDYAVMXQUUACUUAXQYSXGYDXHYEXJYGXFYBXESXFYBXDSYSXIYFXFYBYSXFYBXF
      YBYSVQZUUBVNUUBVOVRVSVTXKYTCYBHWAWBWCYBXLWDWEXQYBGIZJZGXLWFYBXMJXQUUDGXLU
      UCXLQXEUUCJZXDUUCJZUUCUUCKZUUCJZLZXQUUDXKUUICUUCGWHCGUOZXGUUEXHUUFXJUUHXF
      UUCXESXFUUCXDSUUJXIUUGXFUUCUUJXFUUCXFUUCUUJVQZUUKVNUUKVOVRWGXQUUIUUDVPZGX
      QNNVHUULGVLNWIYAXDENHGFYQWJWKWLWMWNGYBXLWOWPWQDXDXTXPHYADBUOANXSXOXRXDXNO
      UMUPYAWIANXOUKXDXNOWRWSWTXAXBXC $.
  $}

  ${
    $d n A $.  $d n B $.  $d n r R $.
    brfvrtrcld.r $e |- ( ph -> R e. _V ) $.
    $( If two elements are connected by the reflexive-transitive closure of a
       relation, then they are connected via ` n ` instances the relation, for
       some natural number ` n ` .  Similar of ~ dfrtrclrec2 .  (Contributed by
       RP, 22-Jul-2020.) $)
    brfvrtrcld $p |- ( ph -> ( A ( t* ` R ) B
                               <-> E. n e. NN0 A ( R ^r n ) B ) ) $=
      ( vr crtcl cn0 dfrtrcl3 ssidd brmptiunrelexpd ) ABCHDEIGEGJFAIKL $.
  $}

  ${
    $d n r R $.
    fvrtrcllb0d.r $e |- ( ph -> R e. _V ) $.
    $( A restriction of the identity relation is a subset of the
       reflexive-transitive closure of a set.  (Contributed by RP,
       22-Jul-2020.) $)
    fvrtrcllb0d $p |- ( ph -> ( _I |` ( dom R u. ran R ) ) C_ ( t* ` R ) ) $=
      ( vn vr crtcl cn0 dfrtrcl3 cvv wcel nn0ex a1i cc0 0nn0 fvmptiunrelexplb0d
      ) AFBDGEDEHCGIJAKLMGJANLO $.
  $}

  ${
    $d n r R $.
    fvrtrcllb0da.rel $e |- ( ph -> Rel R ) $.
    fvrtrcllb0da.r $e |- ( ph -> R e. _V ) $.
    $( A restriction of the identity relation is a subset of the
       reflexive-transitive closure of a relation.  (Contributed by RP,
       22-Jul-2020.) $)
    fvrtrcllb0da $p |- ( ph -> ( _I |` U. U. R ) C_ ( t* ` R ) ) $=
      ( vn crtcl cn0 dfrtrcl3 cvv wcel nn0ex a1i cc0 0nn0 fvmptiunrelexplb0da
      vr ) AFBEGPEPHDGIJAKLCMGJANLO $.
  $}

  ${
    $d n r R $.
    fvrtrcllb1d.r $e |- ( ph -> R e. _V ) $.
    $( A set is a subset of its image under the reflexive-transitive closure.
       (Contributed by RP, 22-Jul-2020.) $)
    fvrtrcllb1d $p |- ( ph -> R C_ ( t* ` R ) ) $=
      ( vn vr crtcl cn0 dfrtrcl3 cvv wcel nn0ex a1i c1 1nn0 fvmptiunrelexplb1d
      ) AFBDGEDEHCGIJAKLMGJANLO $.
  $}

  ${
    $d n r x $.
    $( Reflexive-transitive closure of a relation, expressed as the union of
       the zeroth power and the transitive closure.  (Contributed by RP,
       5-Jun-2020.) $)
    dfrtrcl4 $p |- t* = ( r e. _V |-> ( ( r ^r 0 ) u. ( t+ ` r ) ) ) $=
      ( vn vx crtcl cvv cn0 cv crelexp ciun cmpt cc0 ctcl cfv cun dfrtrcl3 wcel
      co cn wceq eqtri csn df-n0 equncomi iuneq1 ax-mp iunxun c0ex oveq2 iunxsn
      a1i weq oveq1 iuneq2d dftrcl3 nnex ovex iunex fvmpt eqcomd uneq12d eqtrid
      mpteq2ia ) DAEBFAGZBGZHQZIZJAEVCKHQZVCLMZNZJBAOAEVFVIVCEPZVFBKUAZVEIZBRVE
      IZNZVIVFBVKRNZVEIZVNFVOSVFVPSFRVKUBUCBFVOVEUDUEBVKRVEUFTVJVLVGVMVHVLVGSVJ
      BKVEVGUGVDKVCHUHUIUJVJVHVMCVCBRCGZVDHQZIVMELCAUKBRVRVEVQVCVDHULUMBCUNBRVE
      UOVCVDHUPUQURUSUTVAVBT $.
  $}

  ${
    $d a b c d i j k $.
    $( The composition of the reflexive and transitive closures is the
       reflexive-transitive closure.  (Contributed by RP, 17-Jun-2020.) $)
    corcltrcl $p |- ( r* o. t+ ) = t* $=
      ( vi vj vk vd crelexp cc0 c1 cn cn0 cun wss wceq wcel ax-mp cv ciun oveq2
      1nn co cvv va vb vc cpr crcl ctcl crtcl dfrcl4 dftrcl3 dfrtrcl3 prex nnex
      df-n0 uncom df-pr uneq1i unass ssequn1 mpbi uneq2i 3eqtrri 3eqtri cbviunv
      csn snssi ss2iun relexp1g elv ssiun2s eqsstrri ovex iunex 0nn0 1nn0 prssi
      mp2an sseli relexpss1d mprg eqsstri eqtr4i 1elpr01 c0ex prid1 ssid unss12
      a1i iuneq1 iunxun iunxsn cin c0 wne nnssnn0 inelcm iunrelexp0 mp3an eqtri
      vex 1ex uneq12i 3sstr4i comptiunov2i ) ABCEFGUDZHIUEUFUGUAUBUCDAUAUHBUBUI
      CUCUJFGUKULIHFVDZJXEHJZXDHJZUMHXEUNXGXEGVDZJZHJXEXHHJZJXFXDXIHFGUOZUPXEXH
      HUQXJHXEXHHKZXJHLGHMZXLRGHVENXHHURUSUTVAVBCXDDOZCOZESZPZAXDXNAOZESZPZAXDB
      HXNBOZESZPZXRESZPZCAXDXPXSXOXRXNEQVCXSYDKXTYEKAXDAXDXSYDVFXRXDMZXNYCXRXNY
      CKYFXNXNGESZYCYGXNLDXNTVGVHXMYGYCKRBHYBGYGYAGXNEQVINVJWGYCTMZYFBHYBULXNYA
      EVKVLZWGXDIXRFIMGIMXDIKVMVNFGIVOVPVQVRVSVTCHXPPZYCGESZYEYJYCYKCBHXPYBXOYA
      XNEQVCZYHYKYCLYIYCTVGNZWAGXDMZYKYEKWBAXDYDGYKXRGYCEQZVINVTXNFESZYJJZXQYJJ
      ZYECXGXPPYPXQKZYJYJKYQYRKFXDMYSFGWCWDCXDXPFYPXOFXNEQVINYJWEYPXQYJYJWFVPYE
      AXIYDPZAXEYDPZAXHYDPZJYQXDXILYEYTLXKAXDXIYDWHNAXEXHYDWIUUAYPUUBYJUUAYCFES
      ZYPAFYDUUCWCXRFYCEQWJXNTMHIKXDHWKWLWMZUUCYPLDWSWNYNXMUUDWBRGXDHWOVPBXNTHW
      PWQWRUUBYKYJAGYDYKWTYOWJYKYCYJYMYLWAWRXAVBCXDHXPWIXBXC $.
  $}

  $( Composition with the reflexive-transitive closure absorbs the transitive
     closure.  (Contributed by RP, 13-Jun-2020.) $)
  cortrcltrcl $p |- ( t* o. t+ ) = t* $=
    ( crtcl ctcl ccom corcltrcl eqcomi coeq1i coass cotrcltrcl coeq2i eqtri
    crcl ) ABCKBCZBCZAALBLADEFMKBBCZCZAKBBGOLANBKHIDJJJ $.

  $( Composition with the reflexive-transitive closure absorbs the reflexive
     closure.  (Contributed by RP, 13-Jun-2020.) $)
  corclrtrcl $p |- ( r* o. t* ) = t* $=
    ( crcl crtcl ccom ctcl corcltrcl eqcomi coeq2i coass corclrcl coeq1i eqtri
    ) ABCAADCZCZBBLALBEFGMAACZDCZBOMAADHFOLBNADIJEKKK $.

  ${
    $d a b c d i j k x y $.
    $( The composition of the reflexive and transitive closures is the
       reflexive-transitive closure.  (Contributed by RP, 21-Jun-2020.) $)
    cotrclrcl $p |- ( t+ o. r* ) = t* $=
      ( vi vj vk vd crelexp cn cc0 c1 cn0 cun wss wceq wcel ax-mp cv ciun oveq2
      co cvv ccom va vb vc vx vy cpr ctcl crcl crtcl dftrcl3 dfrtrcl3 nnex prex
      dfrcl4 csn df-n0 df-pr equncomi uneq2i unass ssequn2 mpbi uneq1i 3eqtr2ri
      1nn snssi eqtri cbviunv ss2iun 1elpr01 relexp1g eqtrdi ssiun2s ovex iunex
      elv a1i nnnn0 relexpss1d mprg eqsstri iunss iuneq1 iunxun c0ex iunxsn 1ex
      uneq12i 3eqtri oveq1i caddc sseq1d weq unex 0nn0 unssi simpl relexpsucnnr
      1nn0 sylancr coss1 coundi cdm crn cres cid relexp0g coeq2i coiun1 coires1
      wa iuneq2i resss wrex iunss2 wex peano2nn0 sbcel1v sylibr csb relexpaddss
      wsbc vex mp3an23 csbconstg csbov2g csbvarg oveq2d eqtrd 3sstr4g wb sbcssg
      sbcan sylanbrc spesbcd df-rex sseqtri sstrdi adantl eqsstrd nnind mprgbir
      ex eqsstrid comptiunov2i ) ABCEFGHUFZIUGUHUIUAUBUCDAUAUJBUBUNCUCUKULGHUMZ
      IFGUOZJZFUUFJZUPUUJFHUOZUUHJZJFUUKJZUUHJUUIUUFUULFUUFUUHUUKGHUQZURUSFUUKU
      UHUTUUMFUUHUUKFKZUUMFLHFMZUUOVEHFVFNUUKFVAVBVCVDVGZCFDOZCOZERZPAFUURAOZER
      ZPZAFBUUFUURBOZERZPZUVAERZPZCAFUUTUVBUUSUVAUUREQVHUVBUVGKUVCUVHKAFAFUVBUV
      GVIUVAFMZUURUVFUVAUURUVFKZUVIHUUFMUVJVJBUUFUVEHUURUVDHLUVEUURHERZUURUVDHU
      UREQZUVKUURLDUURSVKVPVLVMNVQUVFSMZUVIBUUFUVEUUGUURUVDEVNVOZVQUVAVRVSVTWAU
      UPCUUFUUTPZUVHKVEAFUVGHUVOUVAHLUVGUVFHERZUVOUVAHUVFEQUVPUVFUVOUVMUVPUVFLU
      VNUVFSVKNBCUUFUVEUUTUVDUUSUUREQVHVGVLVMNUVHCIUUTPZCUUJUUTPZUVHUVQKUVGUVQK
      AFAFUVGUVQWBUVIUVGUURGERZUVKJZUVAERZUVQUVFUVTUVAEUVFBUUHUUKJZUVEPZBUUHUVE
      PZBUUKUVEPZJUVTUUFUWBLUVFUWCLUUNBUUFUWBUVEWCNBUUHUUKUVEWDUWDUVSUWEUVKBGUV
      EUVSWEUVDGUUREQWFBHUVEUVKWGUVLWFWHWIWJUVTUDOZERZUVQKUVTHERZUVQKUVTUEOZERZ
      UVQKZUVTUWIHWKRZERZUVQKZUWAUVQKUDUEUVAUWFHLUWGUWHUVQUWFHUVTEQWLUDUEWMUWGU
      WJUVQUWFUWIUVTEQWLUWFUWLLUWGUWMUVQUWFUWLUVTEQWLUDAWMUWGUWAUVQUWFUVAUVTEQW
      LUWHUVTUVQUVTSMZUWHUVTLUVSUVKUURGEVNUURHEVNWNZUVTSVKNUVSUVKUVQGIMUVSUVQKW
      OCIUUTGUVSUUSGUUREQVMNHIMZUVKUVQKWSCIUUTHUVKUUSHUUREQVMNWPWAUWIFMZUWKUWNU
      WRUWKXKZUWMUWJUVTTZUVQUWSUWOUWRUWMUWTLUWPUWRUWKWQUVTUWISWRWTUWKUWTUVQKUWR
      UWKUWTUVQUVTTZUVQUWJUVQUVTXAUXAUVQUVSTZUVQUVKTZJUVQUVQUVSUVKXBUXBUXCUVQUX
      BCIUUTUURXCUURXDJZXEZPZUVQUXBUVQXFUXDXEZTCIUUTUXGTZPUXFUVSUXGUVQUVSUXGLDU
      URSXGVPXHCUUTUXGIXICIUXHUXEUXHUXELUUSIMZUUTUXDXJVQXLWIUXEUUTKZUXFUVQKCICI
      UXEUUTVIUXJUXIUUTUXDXMVQVTWAUXCAIUVBPZUVQUXCCIUUTUVKTZPZUXKCUUTUVKIXIUXLU
      VBKZAIXNZUXMUXKKCICAIIUXLUVBXOUXIUVAIMZUXNXKZAXPUXOUXIUXQAUUSHWKRZUXIUXPA
      UXRYBZUXNAUXRYBZUXQAUXRYBUXIUXRIMUXSUUSXQAUXRIXRXSUXIAUXRUXLXTZAUXRUVBXTZ
      KZUXTUXIUXLUURUXRERZUYAUYBUXIUWQUURSMUXLUYDKWSDYCUURHUUSSYAYDUXRSMZUYAUXL
      LUUSHWKVNZAUXRUXLSYENUYEUYBUYDLUYFUYEUYBUURAUXRUVAXTZERUYDAUXRUURUVAESYFU
      YEUYGUXRUUREAUXRSYGYHYINYJUYEUXTUYCYKUYFAUXRUXLUVBSYLNXSUXPUXNAUXRYMYNYOU
      XNAIYPXSVTWAACIUVBUUTUVAUUSUUREQVHYQWPWAYRYSYTUUCUUAUUDUUBIUUJLUVQUVRLUUQ
      CIUUJUUTWCNYQUUE $.
  $}

  $( Composition with the reflexive-transitive closure absorbs the reflexive
     closure.  (Contributed by RP, 13-Jun-2020.) $)
  cortrclrcl $p |- ( t* o. r* ) = t* $=
    ( crtcl crcl ccom ctcl cotrclrcl eqcomi coeq1i coass corclrcl coeq2i eqtri
    ) ABCDBCZBCZAALBLAEFGMDBBCZCZADBBHOLANBDIJEKKK $.

  $( Composition with the reflexive-transitive closure absorbs the transitive
     closure.  (Contributed by RP, 13-Jun-2020.) $)
  cotrclrtrcl $p |- ( t+ o. t* ) = t* $=
    ( ctcl crtcl ccom cotrclrcl eqcomi coeq2i coass cotrcltrcl coeq1i eqtri
    crcl ) ABCAAKCZCZBBLALBDEFMAACZKCZBOMAAKGEOLBNAKHIDJJJ $.

  $( The reflexive-transitive closure is idempotent.  (Contributed by RP,
     13-Jun-2020.) $)
  cortrclrtrcl $p |- ( t* o. t* ) = t* $=
    ( crtcl ccom ctcl crcl cotrclrcl eqcomi coeq1i coass corclrtrcl cotrclrtrcl
    coeq2i eqtri ) AABCDBZABZAAMAMAEFGNCDABZBZACDAHPCABAOACIKJLLL $.

  $(
    $d x y r R $.  $d x y r A $.  $d x y V $.
    %( When the image of a class is a subclass (the relation is hereditary in
       that class) then the transitive closure of the restriction is equal to
       the restriction of the transitive closure of that relation. %)
    trclubgres $p |- ( ( R e. V /\ ( R " A ) C_ A ) ->
                       |^| { r | ( ( R |` A ) C_ r /\ ( r o. r ) C_ r ) } =
                       ( |^| { r | ( R C_ r /\ ( r o. r ) C_ r ) } |` A ) ) $=
      ( vx vy wcel wss wa cres cv cab cint wrel wb wal cvv relres wi a1i resexg
      cima ccom cop wceq jctir adantr cxp cdm crn trclub xpss sstrdi df-rel syl
      sylibr opex elintab resss sstr2 anim1d imim1d alimdv impbid anbi1i bicomd
      ax-mp jcad 3bitrd vex opelres bitrd gen2 nfv 19.21-2 biimpi eqrel biimpar
      jca ) BCGZBAUBAHZIZBAJZDKZHWDWDUCWDHZIZDLMZNZBWDHWEIZDLMZAJZNZIZEKZFKZUDZ
      WGGZWPWKGZOZFPEPZIWGWKUEZWBWMWTWBWHWLWBWCQGZWCNZIZWHVTXDWAVTXBXCBACUABARU
      FUGXDWGQQUHZHWHXDWGWCUIZWCUJZUHXEWCQDUKXFXGULUMWGUNUPUOWJARUFWBWSSZFPEPZW
      BWTSZXHEFWBWQWPWJGZWNAGZIZWRWBWQWFWPWDGZSDPZWIXNSDPZXLIZXMWQXOOWBWFDWPWNW
      OUQZURT?????????????????????????US???UTVGTVAVBVC?VH?VDWBXMXQXMXQOWBXKXPXL
      WIDWPXRURVETVFVIWBWRXMWRXMOWBWNWOWJAFVJVKTVFVLVMXIXJWBWSEFWBEVNWBFVNVOVPV
      GVSWMXAWTEFWGWKVQVRUO $.
  $)

  $(
    $d r A $.  $d r B $.  $d r R $.
    %( Two ways of expressing the transitive closure of the converse of a
       binary relation.  %)
    brcnvtrclfv2 $p |- ( ( R e. U /\ A e. V /\ B e. W )
                     -> ( A `' ( t+ ` R ) B
                          <-> A. r ( ( R C_ `' r /\ ( r o. r ) C_ r )
                                     -> A r B ) ) ) $=
      ? $.
  $)

  $(
    %( Condition when the restriction of the transitive closure is equal to the
       transitive closure of the restriction. %)
    trclfvres $p |- ( ( ( R e. V /\ A e. W ) /\ ( B C_ A /\ ( R " A ) C_ B ) )
               -> ( ( t+ ` R ) |` A ) = ( t+ ` ( R |` A ) ) $= ? $.
  $)

  $(
    %( The image under the transitive closure of a relation may be decomposed
       into the image under the relation and the image under the transitive
       closure of that image. %)
    trclfvimadecom $p |- ( R e. V ->
                           ( ( t+ ` R ) " A )
                           = ( ( R " A ) u. ( ( t+ ` R ) " ( R " A ) ) ) ) $=
      ( wcel ctcl cfv ccom cun wceq cima imaeq1 imaundir imaco uneq2i eqtri syl
      eqtrdi ) BCDBEFZBRBGZHZIZRAJZBAJZRUCJZHZI?UAUBTAJZUERTAKUFUCSAJZHUEBSALUG
      UDUCRBAMNOQP $.
  $)

  $(
    %( Upper bound for the restriction of the transitive closure. %)
    trclfvresub $p |- ( ( ( R e. V /\ A e. W )
                        /\ ( B C_ A /\ ( R " A ) C_ B ) )
               -> ( ( t+ ` R ) |` A ) C_ ( A X. B ) ) $= ? $.
  $)

  $(
    %( An upper bound on the image of a transitive relation. %)
    trclimaub $p |- ( ( ( R e. U /\ A e. V /\ B e. W )
                      /\ ( R " ( A u. B ) ) C_ B )
                    -> ( ( t+ ` R ) " A ) C_ B ) $=
      (  ) ? $.
  $)

  $(
    %( A special case where union with a Cartesian product may be moved out of
       the transitive closure of a relation. %)
    trclunxp $p |- ( ( ( R e. U /\ A e. V /\ B e. W )
                     /\ ( R " ( A u. B ) ) C_ B )
                   -> ( t+ ` ( R u. ( A X. B ) ) )
                      = ( ( t+ ` R ) u. ( A X. B ) ) ) $=
      (  ) ? $.
  $)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Adapted from Frege
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Theorems inspired by _Begriffsschrift_ without restricting form and content
  to closely parallel those in [Frege1879].

$)

  ${
    frege77d.r $e |- ( ph -> R e. _V ) $.
    frege77d.a $e |- ( ph -> A e. _V ) $.
    frege77d.b $e |- ( ph -> B e. _V ) $.
    frege77d.ab $e |- ( ph -> A ( t+ ` R ) B ) $.
    frege77d.he $e |- ( ph -> ( R " U ) C_ U ) $.
    frege77d.ss $e |- ( ph -> ( R " { A } ) C_ U ) $.
    $( If the images of both ` { A } ` and ` U ` are subsets of ` U ` and ` B `
       follows ` A ` in the transitive closure of ` R ` , then ` B ` is an
       element of ` U ` .  Similar to Proposition 77 of [Frege1879] p. 62.
       Compare with ~ frege77 .  (Contributed by RP, 15-Jul-2020.) $)
    frege77d $p |- ( ph -> B e. U ) $=
      ( ctcl cfv csn cima cvv wcel cun wss syl2anc imaundi unssd trclimalb2 cop
      eqsstrid wbr df-br sylib wb elimasng mpbird sseldd ) ADLMZBNZOZECADPQDUNE
      ROZESUOESFAUPDUNOZDEOZREDUNEUAAUQUREKJUBUEUNEDPUCTACUOQZBCUDUMQZABCUMUFUT
      IBCUMUGUHABPQCPQUSUTUIGHUMBCPPUJTUKUL $.
  $}

  ${
    frege81d.r $e |- ( ph -> R e. _V ) $.
    frege81d.a $e |- ( ph -> A e. U ) $.
    frege81d.b $e |- ( ph -> B e. _V ) $.
    frege81d.ab $e |- ( ph -> A ( t+ ` R ) B ) $.
    frege81d.he $e |- ( ph -> ( R " U ) C_ U ) $.
    $( If the image of ` U ` is a subset ` U ` , ` A ` is an element of ` U `
       and ` B ` follows ` A ` in the transitive closure of ` R ` , then ` B `
       is an element of ` U ` .  Similar to Proposition 81 of [Frege1879]
       p. 63.  Compare with ~ frege81 .  (Contributed by RP, 15-Jul-2020.) $)
    frege81d $p |- ( ph -> B e. U ) $=
      ( elexd csn cima wss snssd imass2 syl sstrd frege77d ) ABCDEFABEGKHIJADBL
      ZMZDEMZEATENUAUBNABEGOTEDPQJRS $.
  $}

  ${
    frege83d.r $e |- ( ph -> R e. _V ) $.
    frege83d.a $e |- ( ph -> A e. U ) $.
    frege83d.b $e |- ( ph -> B e. _V ) $.
    frege83d.ab $e |- ( ph -> A ( t+ ` R ) B ) $.
    frege83d.he $e |- ( ph -> ( R " ( U u. V ) ) C_ ( U u. V ) ) $.
    $( If the image of the union of ` U ` and ` V ` is a subset of the union of
       ` U ` and ` V ` , ` A ` is an element of ` U ` and ` B ` follows ` A `
       in the transitive closure of ` R ` , then ` B ` is an element of the
       union of ` U ` and ` V ` .  Similar to Proposition 83 of [Frege1879]
       p. 65.  Compare with ~ frege83 .  (Contributed by RP, 15-Jul-2020.) $)
    frege83d $p |- ( ph -> B e. ( U u. V ) ) $=
      ( cun ssun1 sselid frege81d ) ABCDEFLZGAEPBEFMHNIJKO $.
  $}

  ${
    frege96d.r $e |- ( ph -> R e. _V ) $.
    frege96d.a $e |- ( ph -> A e. _V ) $.
    frege96d.b $e |- ( ph -> B e. _V ) $.
    frege96d.c $e |- ( ph -> C e. _V ) $.
    frege96d.ac $e |- ( ph -> A ( t+ ` R ) C ) $.
    frege96d.cb $e |- ( ph -> C R B ) $.
    $( If ` C ` follows ` A ` in the transitive closure of ` R ` and ` B `
       follows ` C ` in ` R ` , then ` B ` follows ` A ` in the transitive
       closure of ` R ` .  Similar to Proposition 96 of [Frege1879] p. 71.
       Compare with ~ frege96 .  (Contributed by RP, 15-Jul-2020.) $)
    frege96d $p |- ( ph -> A ( t+ ` R ) B ) $=
      ( ctcl cfv ccom wbr cvv wcel brcogw syl32anc wss coss1 trclfvcotrg sstrdi
      trclfvlb 3syl ssbrd mpd ) ABCEELMZNZOZBCUHOABPQCPQDPQBDUHODCEOUJGHIJKBCEU
      HPPDPRSAUIUHBCAUIUHUHNZUHAEPQEUHTUIUKTFEPUDEUHUHUAUEEUBUCUFUG $.
  $}

  ${
    frege87d.r $e |- ( ph -> R e. _V ) $.
    frege87d.a $e |- ( ph -> A e. _V ) $.
    frege87d.b $e |- ( ph -> B e. _V ) $.
    frege87d.c $e |- ( ph -> C e. _V ) $.
    frege87d.ac $e |- ( ph -> A ( t+ ` R ) C ) $.
    frege87d.cb $e |- ( ph -> C R B ) $.
    frege87d.ss $e |- ( ph -> ( R " { A } ) C_ U ) $.
    frege87d.he $e |- ( ph -> ( R " U ) C_ U ) $.
    $( If the images of both ` { A } ` and ` U ` are subsets of ` U ` and ` C `
       follows ` A ` in the transitive closure of ` R ` and ` B ` follows ` C `
       in ` R ` , then ` B ` is an element of ` U ` .  Similar to Proposition
       87 of [Frege1879] p. 66.  Compare with ~ frege87 .  (Contributed by RP,
       15-Jul-2020.) $)
    frege87d $p |- ( ph -> B e. U ) $=
      ( frege96d frege77d ) ABCEFGHIABCDEGHIJKLONMP $.
  $}

  ${
    frege91d.r $e |- ( ph -> R e. _V ) $.
    frege91d.ac $e |- ( ph -> A R B ) $.
    $( If ` B ` follows ` A ` in ` R ` then ` B ` follows ` A ` in the
       transitive closure of ` R ` .  Similar to Proposition 91 of [Frege1879]
       p. 68.  Comparw with ~ frege91 .  (Contributed by RP, 15-Jul-2020.) $)
    frege91d $p |- ( ph -> A ( t+ ` R ) B ) $=
      ( wbr ctcl cfv cvv wcel wss trclfvlb syl ssbrd mpd ) ABCDGBCDHIZGFADQBCAD
      JKDQLEDJMNOP $.
  $}

  ${
    frege97d.r $e |- ( ph -> R e. _V ) $.
    frege97d.a $e |- ( ph -> A = ( ( t+ ` R ) " U ) ) $.
    $( If ` A ` contains all elements after those in ` U ` in the transitive
       closure of ` R ` , then the image under ` R ` of ` A ` is a subclass of
       ` A ` .  Similar to Proposition 97 of [Frege1879] p. 71.  Compare with
       ~ frege97 .  (Contributed by RP, 15-Jul-2020.) $)
    frege97d $p |- ( ph -> ( R " A ) C_ A ) $=
      ( ctcl cfv ccom cima wss cvv wcel trclfvlb 3syl trclfvcotrg sstrdi imass1
      coss1 syl imaeq2d imaco eqtr4di 3sstr4d ) ACCGHZIZDJZUEDJZCBJZBAUFUEKUGUH
      KAUFUEUEIZUEACLMCUEKUFUJKECLNCUEUESOCPQUFUEDRTAUICUHJUGABUHCFUACUEDUBUCFU
      D $.
  $}

  ${
    frege98d.a $e |- ( ph -> A e. _V ) $.
    frege98d.b $e |- ( ph -> B e. _V ) $.
    frege98d.c $e |- ( ph -> C e. _V ) $.
    frege98d.ac $e |- ( ph -> A ( t+ ` R ) C ) $.
    frege98d.cb $e |- ( ph -> C ( t+ ` R ) B ) $.
    $( If ` C ` follows ` A ` and ` B ` follows ` C ` in the transitive closure
       of ` R ` , then ` B ` follows ` A ` in the transitive closure of ` R ` .
       Similar to Proposition 98 of [Frege1879] p. 71.  Compare with
       ~ frege98 .  (Contributed by RP, 15-Jul-2020.) $)
    frege98d $p |- ( ph -> A ( t+ ` R ) B ) $=
      ( ctcl cfv ccom wbr cvv wcel brcogw syl32anc wss trclfvcotrg a1i ssbrd
      mpd ) ABCEKLZUDMZNZBCUDNABOPCOPDOPBDUDNDCUDNUFFGHIJBCUDUDOODOQRAUEUDBCUEU
      DSAETUAUBUC $.
  $}

  ${
    frege102d.r $e |- ( ph -> R e. _V ) $.
    frege102d.a $e |- ( ph -> A e. _V ) $.
    frege102d.b $e |- ( ph -> B e. _V ) $.
    frege102d.c $e |- ( ph -> C e. _V ) $.
    frege102d.ac $e |- ( ph -> ( A ( t+ ` R ) C \/ A = C ) ) $.
    frege102d.cb $e |- ( ph -> C R B ) $.
    $( If either ` A ` and ` C ` are the same or ` C ` follows ` A ` in the
       transitive closure of ` R ` _and_ ` B ` is the successor to ` C ` , then
       ` B ` follows ` A ` in the transitive closure of ` R ` .  Similar to
       Proposition 102 of [Frege1879] p. 72.  Compare with ~ frege102 .
       (Contributed by RP, 15-Jul-2020.) $)
    frege102d $p |- ( ph -> A ( t+ ` R ) B ) $=
      ( ctcl cfv wbr wceq wa cvv wcel adantr simpr frege96d frege91d mpjaodan
      eqbrtrd ) ABDELMZNZBCUENBDOZAUFPBCDEAEQRZUFFSABQRUFGSACQRUFHSADQRUFISAUFT
      ADCENZUFKSUAAUGPZBCEAUHUGFSUJBDCEAUGTAUIUGKSUDUBJUC $.
  $}

  ${
    frege106d.cb $e |- ( ph -> A R B ) $.
    $( If ` B ` follows ` A ` in ` R ` , then either ` A ` and ` B ` are the
       same or ` B ` follows ` A ` in ` R ` .  Similar to Proposition 106 of
       [Frege1879] p. 73.  Compare with ~ frege106 .  (Contributed by RP,
       15-Jul-2020.) $)
    frege106d $p |- ( ph -> ( A R B \/ A = B ) ) $=
      ( wbr wceq orcd ) ABCDFBCGEH $.
  $}

  ${
    frege108d.r $e |- ( ph -> R e. _V ) $.
    frege108d.a $e |- ( ph -> A e. _V ) $.
    frege108d.b $e |- ( ph -> B e. _V ) $.
    frege108d.c $e |- ( ph -> C e. _V ) $.
    frege108d.ac $e |- ( ph -> ( A ( t+ ` R ) C \/ A = C ) ) $.
    frege108d.cb $e |- ( ph -> C R B ) $.
    $( If either ` A ` and ` C ` are the same or ` C ` follows ` A ` in the
       transitive closure of ` R ` _and_ ` B ` is the successor to ` C ` , then
       either ` A ` and ` B ` are the same or ` B ` follows ` A ` in the
       transitive closure of ` R ` .  Similar to Proposition 108 of [Frege1879]
       p. 74.  Compare with ~ frege108 .  (Contributed by RP, 15-Jul-2020.) $)
    frege108d $p |- ( ph -> ( A ( t+ ` R ) B \/ A = B ) ) $=
      ( ctcl cfv frege102d frege106d ) ABCELMABCDEFGHIJKNO $.
  $}

  ${
    frege109d.r $e |- ( ph -> R e. _V ) $.
    frege109d.a $e |- ( ph -> A = ( U u. ( ( t+ ` R ) " U ) ) ) $.
    $( If ` A ` contains all elements of ` U ` and all elements after those in
       ` U ` in the transitive closure of ` R ` , then the image under ` R ` of
       ` A ` is a subclass of ` A ` .  Similar to Proposition 109 of
       [Frege1879] p. 74.  Compare with ~ frege109 .  (Contributed by RP,
       15-Jul-2020.) $)
    frege109d $p |- ( ph -> ( R " A ) C_ A ) $=
      ( cima ctcl cfv ccom cun cvv wcel trclfvlb imass1 3syl trclfvcotrg sstrdi
      wss coss1 unssd ssun2 imaeq2d imaundi imaco eqcomi uneq2i eqtrdi 3sstr4d
      syl eqtri ) ACDGZCCHIZJZDGZKZDUMDGZKZCBGZBAUPUQURAULUOUQACLMZCUMSZULUQSEC
      LNZCUMDOPAUNUMSUOUQSAUNUMUMJZUMAUTVAUNVCSEVBCUMUMTPCQRUNUMDOUJUAUQDUBRAUS
      CURGZUPABURCFUCVDULCUQGZKUPCDUQUDVEUOULUOVECUMDUEUFUGUKUHFUI $.
  $}

  ${
    frege114d.ab $e |- ( ph -> ( A R B \/ A = B ) ) $.
    $( If either ` R ` relates ` A ` and ` B ` or ` A ` and ` B ` are the same,
       then either ` A ` and ` B ` are the same, ` R ` relates ` A ` and
       ` B ` , ` R ` relates ` B ` and ` A ` .  Similar to Proposition 114 of
       [Frege1879] p. 76.  Compare with ~ frege114 .  (Contributed by RP,
       15-Jul-2020.) $)
    frege114d $p |- ( ph -> ( A R B \/ A = B \/ B R A ) ) $=
      ( wbr wceq wo w3o df-3or biimpri orcs syl ) ABCDFZBCGZHZNOCBDFZIZEPQRRPQH
      NOQJKLM $.
  $}

  ${
    frege111d.r $e |- ( ph -> R e. _V ) $.
    frege111d.a $e |- ( ph -> A e. _V ) $.
    frege111d.b $e |- ( ph -> B e. _V ) $.
    frege111d.c $e |- ( ph -> C e. _V ) $.
    frege111d.ac $e |- ( ph -> ( A ( t+ ` R ) C \/ A = C ) ) $.
    frege111d.cb $e |- ( ph -> C R B ) $.
    $( If either ` A ` and ` C ` are the same or ` C ` follows ` A ` in the
       transitive closure of ` R ` _and_ ` B ` is the successor to ` C ` , then
       either ` A ` and ` B ` are the same or ` A ` follows ` B ` or ` B ` and
       ` A ` in the transitive closure of ` R ` .  Similar to Proposition 111
       of [Frege1879] p. 75.  Compare with ~ frege111 .  (Contributed by RP,
       15-Jul-2020.) $)
    frege111d $p |- ( ph -> ( A ( t+ ` R ) B \/ A = B \/ B ( t+ ` R ) A ) ) $=
      ( ctcl cfv frege108d frege114d ) ABCELMABCDEFGHIJKNO $.
  $}

  ${
    frege122d.a $e |- ( ph -> A = ( F ` X ) ) $.
    frege122d.b $e |- ( ph -> B = ( F ` X ) ) $.
    $( If ` F ` is a function, ` A ` is the successor of ` X ` , and ` B ` is
       the successor of ` X ` , then ` A ` and ` B ` are the same (or ` B `
       follows ` A ` in the transitive closure of ` F ` ).  Similar to
       Proposition 122 of [Frege1879] p. 79.  Compare with ~ frege122 .
       (Contributed by RP, 15-Jul-2020.) $)
    frege122d $p |- ( ph -> ( A ( t+ ` F ) B \/ A = B ) ) $=
      ( wceq ctcl cfv wbr eqtr4d olcd ) ABCHBCDIJKABEDJCFGLM $.
  $}

  ${
    frege124d.f $e |- ( ph -> F e. _V ) $.
    frege124d.x $e |- ( ph -> X e. dom F ) $.
    frege124d.a $e |- ( ph -> A = ( F ` X ) ) $.
    frege124d.xb $e |- ( ph -> X ( t+ ` F ) B ) $.
    frege124d.fun $e |- ( ph -> Fun F ) $.
    $d a B $.  $d a F $.  $d a X $.
    $( If ` F ` is a function, ` A ` is the successor of ` X ` , and ` B `
       follows ` X ` in the transitive closure of ` F ` , then ` A ` and ` B `
       are the same or ` B ` follows ` A ` in the transitive closure of ` F ` .
       Similar to Proposition 124 of [Frege1879] p. 80.  Compare with
       ~ frege124 .  (Contributed by RP, 16-Jul-2020.) $)
    frege124d $p |- ( ph -> ( A ( t+ ` F ) B \/ A = B ) ) $=
      ( va wbr wceq wn wa wcel syl2anc wsbc cvv syl ctcl cfv wfun ccom cdif wal
      cv wi weu wex eqcomd cdm funbrfvb mpbid funeu fvex eqeltrdi sbcan sbcbr2g
      wb csbvarg breq2d bitrd sbcng sbcbr1g breq1d notbid anbi12d bitrid spesbc
      csb biimtrrdi mpand eupicka syl6an alinexa wrel funrel reltrclfv brrelex2
      brcog bitr4id sylibd brdif simplbi2 sylsyld cun trclfvdecomr uncom eqtrdi
      wss eqimss ssundif sylib ssbrd syld funbrfv eqcom imbitrdi eqtr3 orrd ) A
      BCDUAUBZLZBCMZABEDUBZMXCNZCXEMZXDHAXFXECMZXGADUCZXFECDLZXHJAXFECXBXBDUDZU
      EZLZXJAECXBLZXFECXKLZNZXMIAXFEKUGZDLZXQCXBLZNZUHKUFZXPAXRKUIZXFXRXTOZKUJZ
      YAAXIEBDLZYBJAXEBMZYEABXEHUKAXIEDULZPZYFYEUTJGEBDUMQUNZKEBDUOQAYEXFYDYIAY
      EXFOZYCKBRZYDABSPZYKYJUTABXESHEDUPUQYKXRKBRZXTKBRZOYLYJXRXTKBURYLYMYEYNXF
      YLYMEKBXQVKZDLYEKBEXQDSUSYLYOBEDKBSVAZVBVCYLYNXSKBRZNXFXSKBSVDYLYQXCYLYQY
      OCXBLXCKBXQCXBSVEYLYOBCXBYPVFVCVGVCVHVITYCKBVJVLVMXRXTKVNVOAYAXRXSOKUJZNX
      PXRXSKVPAXOYRAYHCSPZXOYRUTGAXBVQZXNYSADSPZDVQZYTFAXIUUBJDVRTDSVSQIECXBVTQ
      KECXBDYGSWAQVGWBWCXMXNXPECXBXKWDWEWFAXLDECAXBXKDWGZWKZXLDWKAXBUUCMUUDAXBD
      XKWGZUUCAUUAXBUUEMFDSWHTDXKWIWJXBUUCWLTXBXKDWMWNWOWPECDWQWFXECWRWSBCXEWTV
      OXA $.
  $}

  ${
    frege126d.f $e |- ( ph -> F e. _V ) $.
    frege126d.x $e |- ( ph -> X e. dom F ) $.
    frege126d.a $e |- ( ph -> A = ( F ` X ) ) $.
    frege126d.xb $e |- ( ph -> X ( t+ ` F ) B ) $.
    frege126d.fun $e |- ( ph -> Fun F ) $.
    $( If ` F ` is a function, ` A ` is the successor of ` X ` , and ` B `
       follows ` X ` in the transitive closure of ` F ` , then (for distinct
       ` A ` and ` B ` ) either ` A ` follows ` B ` or ` B ` follows ` A ` in
       the transitive closure of ` F ` .  Similar to Proposition 126 of
       [Frege1879] p. 81.  Compare with ~ frege126 .  (Contributed by RP,
       16-Jul-2020.) $)
    frege126d $p |- ( ph -> ( A ( t+ ` F ) B \/ A = B \/ B ( t+ ` F ) A ) ) $=
      ( ctcl cfv frege124d frege114d ) ABCDKLABCDEFGHIJMN $.
  $}

  ${
    frege129d.f $e |- ( ph -> F e. _V ) $.
    frege129d.a $e |- ( ph -> A e. dom F ) $.
    frege129d.c $e |- ( ph -> C = ( F ` A ) ) $.
    frege129d.or $e |- ( ph -> ( A ( t+ ` F ) B
                                 \/ A = B \/ B ( t+ ` F ) A ) ) $.
    frege129d.fun $e |- ( ph -> Fun F ) $.
    $( If ` F ` is a function and (for distinct ` A ` and ` B ` ) either ` A `
       follows ` B ` or ` B ` follows ` A ` in the transitive closure of
       ` F ` , the successor of ` A ` is either ` B ` or it follows ` B ` or it
       comes before ` B ` in the transitive closure of ` F ` .  Similar to
       Proposition 129 of [Frege1879] p. 83.  Comparw with ~ frege129 .
       (Contributed by RP, 16-Jul-2020.) $)
    frege129d $p |- ( ph -> ( B ( t+ ` F ) C \/ B = C \/ C ( t+ ` F ) B ) ) $=
      ( cfv wbr wceq w3o wa cvv wcel adantr simpr ex ctcl frege126d eqcom sylib
      cdm wfun biid 3orbi123i 3orcomb 3orrot sylbb syl eqcomd wi biimpd syl2anc
      funbrfvb mpd frege91d eqbrtrrd 3mix1 syl6 funrel reltrclfv brrelex1 sylan
      wrel fvex eqeltrdi elexd frege96d 3jaod ) ABCEUAKZLZBCMZCBVMLZNCDVMLZCDMZ
      DCVMLZNZIAVNVTVOVPAVNVTAVNOZVSVRVQNZVTWAVSDCMZVQNWBWADCEBAEPQZVNFRABEUEZQ
      ZVNGRADBEKZMVNHRAVNSAEUFZVNJRUBVSVSWCVRVQVQVSUGDCUCVQUGUHUDWBVSVQVRNVTVSV
      RVQUIVSVQVRUJUKULTAVOVQVTAVOVQAVOOBCDVMAVOSABDVMLVOABDEFAWGDMZBDELZADWGHU
      MAWHWFWIWJUNJGWHWFOWIWJBDEUQUOUPURZUSRUTTVQVRVSVAZVBAVPVQVTAVPVQAVPOCDBEA
      WDVPFRAVMVGZVPCPQAWDEVGZWMFAWHWNJEVCULEPVDUPCBVMVEVFADPQVPADWGPHBEVHVIRAB
      PQVPABWEGVJRAVPSAWJVPWKRVKTWLVBVLUR $.
  $}

  ${
    frege131d.f $e |- ( ph -> F e. _V ) $.
    frege131d.a $e |- ( ph -> A = ( U u. ( ( `' ( t+ ` F ) " U )
                                         u. ( ( t+ ` F ) " U ) ) ) ) $.
    frege131d.fun $e |- ( ph -> Fun F ) $.
    $( If ` F ` is a function and ` A ` contains all elements of ` U ` and all
       elements before or after those elements of ` U ` in the transitive
       closure of ` F ` , then the image under ` F ` of ` A ` is a subclass of
       ` A ` .  Similar to Proposition 131 of [Frege1879] p. 85.  Compare with
       ~ frege131 .  (Contributed by RP, 17-Jul-2020.) $)
    frege131d $p |- ( ph -> ( F " A ) C_ A ) $=
      ( cima ccnv ccom cun cvv wss imass1 sstrdi cid syl eqtri eqtrdi eqcomi
      ctcl cfv wcel trclfvlb 3syl ssun2 sstri crn cres wceq trclfvdecomr cnveqd
      cnvun cnvco uneq2i coeq2d coundi wfun funcocnv2 coass coeq1d eqtrid eqtrd
      uneq12d imaeq1d resss ax-mp imai sseqtri imaco eqsstri unss12 mp2an ssun1
      imaundir unass eqsstrdi coss1 trclfvcotrg imaeq2d imaundi uneq12i 3sstr4d
      unssd ) ADCHZDDUAUBZIZJZCHZDWFJZCHZKZKZCWGCHZWFCHZKZKZDBHZBAWEWLWQAWEWOWQ
      ADLUCZDWFMZWEWOMEDLUDZDWFCNUEWOWPWQWOWNUFWPCUFUGZOAWIWKWQAWIPDUHZUIZCHZXD
      WGJZCHZKZWQAWIXDXFKZCHXHAWHXICAWHDDIZXJWGJZKZJZXIAWGXLDAWGDWFDJZKZIZXLAWF
      XOAWSWFXOUJEDLUKQULXPXJXNIZKXLDXNUMXQXKXJWFDUNUORSUPAXMDXJJZDXKJZKXIDXJXK
      UQAXRXDXSXFADURXRXDUJGDUSQZAXSXRWGJZXFYAXSDXJWGUTTAXRXDWGXTVAVBVDVBVCVEXD
      XFCVOSXHCWNKZWQXECMXGWNMXHYBMXEPCHZCXDPMZXEYCMPXCVFZXDPCNVGCVHVIXGXDWNHZW
      NXDWGCVJYFPWNHZWNYDYFYGMYEXDPWNNVGWNVHVIVKXECXGWNVLVMYBYBWOKWQYBWOVNCWNWO
      VPVIUGVQAWKWOWQAWJWFMWKWOMAWJWFWFJZWFAWSWTWJYHMEXADWFWFVRUEDVSOWJWFCNQXBO
      WDWDAWRDWQHZWMABWQDFVTYIWEDWPHZKWMDCWPWAYJWLWEYJDWNHZDWOHZKWLDWNWOWAYKWIY
      LWKWIYKDWGCVJTWKYLDWFCVJTWBRUORSFWC $.
  $}

  ${
    frege133d.f $e |- ( ph -> F e. _V ) $.
    frege133d.xa $e |- ( ph -> X ( t+ ` F ) A ) $.
    frege133d.xb $e |- ( ph -> X ( t+ ` F ) B ) $.
    frege133d.fun $e |- ( ph -> Fun F ) $.
    $( If ` F ` is a function and ` A ` and ` B ` both follow ` X ` in the
       transitive closure of ` F ` , then (for distinct ` A ` and ` B ` )
       either ` A ` follows ` B ` or ` B ` follows ` A ` in the transitive
       closure of ` F ` (or both if it loops).  Similar to Proposition 133 of
       [Frege1879] p. 86.  Compare with ~ frege133 .  (Contributed by RP,
       18-Jul-2020.) $)
    frege133d $p |- ( ph -> ( A ( t+ ` F ) B \/ A = B \/ B ( t+ ` F ) A ) ) $=
      ( cima wcel w3o wbr wceq cun wrel wb cvv syl wo ctcl cfv ccnv wfun funrel
      csn reltrclfv syl2anc eliniseg2 brrelex2 un12 a1i frege131d frege83d elun
      mpbird orbi2i 3orass 3bitr4i sylib biimpd elsni elrelimasn 3orim123d mpd
      wi ) ABDUAUBZUCCUFZJZKZBVHKZBVGVHJZKZLZBCVGMZBCNZCBVGMZLABVIVHVLOZOZKZVNA
      EBDVIVRFAEVIKZECVGMZHAVGPZWAWBQADRKDPZWCFADUDWDIDUESDRUGUHZVGCEUISUPAWCEB
      VGMBRKWEGEBVGUJUHGAVSVHDFVSVHVIVLOONAVIVHVLUKULIUMUNVJBVRKZTVJVKVMTZTVTVN
      WFWGVJBVHVLUOUQBVIVRUOVJVKVMURUSUTAVJVOVKVPVMVQAVJVOAWCVJVOQWEVGCBUISVAVK
      VPVFABCVBULAVMVQAWCVMVQQWECBVGVCSVAVDVE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Propositions from _Begriffsschrift_
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

   In 1879, Frege introduced notation for documenting formal reasoning about
   propositions (and classes) which covered elements of propositional logic,
   predicate calculus and reasoning about relations.  However, due to the
   pitfalls of naive set theory, adapting this work for inclusion in set.mm
   required dividing statements about propositions from those about classes and
   identifying when a restriction to sets is required.  For an overview
   comparing the details of Frege's two-dimensional notation and that used in
   set.mm, see ~ mmfrege.html .  See ~ ru for discussion of an example of a
   class that is not a set.

   Numbered propositions from [Frege1879]. ~ ax-frege1 , ~ ax-frege2 ,
   ~ ax-frege8 , ~ ax-frege28 , ~ ax-frege31 , ~ ax-frege41 , frege52 (see
   ~ ax-frege52a , ~ frege52b , and ~ ax-frege52c for translations), frege54
   (see ~ ax-frege54a , ~ frege54b and ~ ax-frege54c for translations) and
   frege58 (see ~ ax-frege58a , ~ ax-frege58b and ~ frege58c for translations)
   are considered "core" or axioms.  However, at least ~ ax-frege8 can be
   derived from ~ ax-frege1 and ~ ax-frege2 , see ~ axfrege8 .

   Frege introduced implication, negation and the universal quantifier as
   primitives and did not in the numbered propositions use other logical
   connectives other than equivalence introduced in ~ ax-frege52a ,
   ~ frege52b , and ~ ax-frege52c .  In ~ dffrege69 , Frege introduced
   ` R hereditary A `  to say that relation ` R ` , when restricted to operate
   on elements of class ` A ` , will only have elements of class ` A ` in its
   domain; see ~ df-he for a definition in terms of image and subset.
   In ~ dffrege76 , Frege introduced notation for the concept of two sets
   related by the transitive closure of a relation, for which we write
   ` X ( t+ `` R ) Y ` , which requires ` R ` to also be a set.
   In ~ dffrege99 , Frege introduced notation for the concept of two sets
   either identical or related by the transitive closure of a relation, for
   which we write ` X ( ( t+ `` R ) u. _I ) Y ` , which is a superclass of
   sets related by the reflexive-transitive relation ` X ( t* `` R ) Y ` .
   Finally, in ~ dffrege115 , Frege introduced notation for the concept of a
   relation having the property elements in its domain pair up with only one
   element each in its range, for which we write ` Fun ``' ``' R ` (to ignore
   any non-relational content of the class ` R ` ).  Frege did this without
   the expressing concept of a relation (or its transitive closure) as a
   class, and needed to invent conventions for discussing indeterminate
   propositions with two slots free and how to recognize which of the slots
   was domain and which was range.  See ~ mmfrege.html for details.

   English translations for specific propositions lifted in part
   from a translation by Stefan Bauer-Mengelberg as reprinted in
   _From Frege to Goedel: A Source Book in Mathematical Logic,
   1879-1931_. An attempt to align these propositions in the larger
   set.mm database has also been made.  See ~ frege77d for an example.

$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  _Begriffsschrift_ Chapter I
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Section 2 introduces the turnstile ` |- ` which turns an idea which
  may be true ` ph ` into an assertion that it does hold true ` |- ph ` .
  Section 5 introduces implication, ` ( ph -> ps ) ` .  Section 6 introduces
  the single rule of interference relied upon, _modus ponens_ ~ ax-mp .
  Section 7 introduces negation and with in synonyms for or ` ( -. ph -> ps ) `
  , and ` -. ( ph -> -. ps ) ` , and two for exclusive-or corresponding to
  ~ df-or , ~ df-an , ~ dfxor4 , ~ dfxor5 .

  Section 8 introduces the problematic notation for identity of conceptual
  content which must be separated into cases for biconditional
  ` ( ph <-> ps ) ` or class equality ` A = B ` in this adaptation.  Section
  10 introduces "truth functions" for one or two variables in equally
  troubling notation, as the arguments may be understood to be logical
  predicates or collections.  Here f( ` ph ` )  is interpreted to mean
  ` if- ( ph , ps , ch ) ` where the content of the "function" is specified
  by the latter two arguments or logical equivalent, while g( ` A  ` ) is read
  as ` A e. G ` and h( ` A , B ` ) as ` A H B ` .  This necessarily
  introduces a need for set theory as both ` A e. G ` and ` A H B ` cannot
  hold unless ` A ` is a set. (Also ` B ` .)

  Section 11 introduces notation for generality, but there is no standard
  notation for generality when the variable is a proposition because it was
  realized after Frege that the universe of all possible propositions includes
  paradoxical constructions leading to the failure of naive set theory.  So
  adopting f( ` ph ` ) as ` if- ( ph , ps , ch ) ` would result in the
  translation of ` A. ph ` f ( ` ph ` )  as ` ( ps /\ ch ) ` .  For
  collections, we must generalize over set variables or run into the same
  problems; this leads to ` A. A ` g( ` A ` ) being translated as
  ` A. a a e. G ` and so forth.

  Under this interpreation the text of section 11 gives us ~ sp (or ~ simpl
  and ~ simpr and ~ anifp in the propositional case) and statements similar
  to ~ cbvalivw , ~ ax-gen , ~ alrimiv , and ~ alrimdv .  These last four
  introduce a generality and have no useful definition in terms of
  propositional variables.

  Section 12 introduces some combinations of primitive symbols and their human
  language counterparts. Using class notation, these can also be expressed
  without dummy variables.  All are A, ` A. x x e. A ` , ` -. E. x -. x e. A `
  ~ alex , ` A = _V ` ~ eqv ; Some are not B, ` -. A. x x e. B ` ,
  ` E. x -. x e. B ` ~ exnal , ` B C. _V ` ~ pssv , ` B =/= _V ` ~ nev ; There
  are no C, ` A. x -. x e. C ` , ` -. E. x x e. C ` ~ alnex , ` C = (/) `
  ~ eq0 ; There exist D, ` -. A. x -. x e. D ` , ` E. x x e. D ` ~ df-ex ,
  ` (/) C. D ` ~ 0pss , ` D =/= (/) ` ~ n0 .

  Notation for relations between expressions also can be written in various
  ways.  All E are P, ` A. x ( x e. E -> x e. P ) ` ,
  ` -. E. x ( x e. E /\ -. x e. P ) ` ~ dfss6 , ` E = ( E i^i P ) ` ~ dfss2 ,
  ` E C_ P ` ~ df-ss ; No F are P, ` A. x ( x e. F -> -. x e. P ) ` ,
  ` -. E. x ( x e. F /\ x e. P ) ` ~ alinexa , ` ( F i^i P ) = (/) ` ~ disj1 ;
  Some G are not P, ` -. A. x ( x e. G -> x e. P ) ` ,
  ` E. x ( x e. G /\ -. x e. P ) ` ~ exanali , ` ( G i^i P ) C. G `
  ~ nssinpss ,  ` -. G C_ P ` ~ nss ;  Some H are P,
  ` -. A. x ( x e. H -> -. x e. P ) ` , ` E. x ( x e. H /\ x e. P ) `
  ~ exnalimn , ` (/) C. ( H i^i P ) ` ~ 0pssin , ` ( H i^i P ) =/= (/) `
  ~ ndisj .

$)

  $( Express exclusive-or in terms of implication and negation.  Statement in
     [Frege1879] p. 12.  (Contributed by RP, 14-Apr-2020.) $)
  dfxor4 $p |- ( ( ph \/_ ps )
                 <-> -. ( ( -. ph -> ps ) -> -. ( ph -> -. ps ) ) ) $=
    ( wxo wo wa wn wi xor2 df-or imnan bicomi anbi12i df-an 3bitri ) ABCABDZABE
    FZEAFBGZABFGZEQRFGFABHOQPRABIRPABJKLQRMN $.

  $( Express exclusive-or in terms of implication and negation.  Statement in
     [Frege1879] p. 12.  (Contributed by RP, 14-Apr-2020.) $)
  dfxor5 $p |- ( ( ph \/_ ps )
                 <-> -. ( ( ph -> -. ps ) -> -. ( -. ph -> ps ) ) ) $=
    ( wxo wn wi dfxor4 con2b xchbinx ) ABCADBEZABDEZDEJIDEABFIJGH $.

  $( Express triple-or in terms of implication and negation.  Statement in
     [Frege1879] p. 11.  (Contributed by RP, 25-Jul-2020.) $)
  df3or2 $p |- ( ( ph \/ ps \/ ch )
                 <-> ( -. ph -> ( -. ps -> ch ) ) ) $=
    ( w3o wo wn wi df-3or df-or wa ioran imbi1i impexp bitri ) ABCDABEZCEZAFZBF
    ZCGGZABCHPOFZCGZSOCIUAQRJZCGSTUBCABKLQRCMNNN $.

  $( Express triple-and in terms of implication and negation.  Statement in
     [Frege1879] p. 12.  (Contributed by RP, 25-Jul-2020.) $)
  df3an2 $p |- ( ( ph /\ ps /\ ch )
                 <-> -. ( ph -> ( ps -> -. ch ) ) ) $=
    ( w3a wa wn wi df-3an df-an impexp xchbinx bitri ) ABCDABEZCEZABCFZGGZFABCH
    NMOGPMCIABOJKL $.

  ${
    $d x A $.
    $( Express that not every set is in a class.  (Contributed by RP,
       16-Apr-2020.) $)
    nev $p |- ( A =/= _V <-> -. A. x x e. A ) $=
      ( cv wcel wal cvv eqv necon3abii ) ACBDAEBFABGH $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Express that an intersection is not empty.  (Contributed by RP,
       16-Apr-2020.) $)
    0pssin $p |- ( (/) C. ( A i^i B ) <-> E. x ( x e. A /\ x e. B ) ) $=
      ( c0 cin wpss wne cv wcel wa wex 0pss ndisj bitri ) DBCEZFODGAHZBIPCIJAKO
      LABCMN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  _Begriffsschrift_ Notation hints
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  The statement ` R hereditary A ` means relation ` R ` is hereditary (in the
  sense of Frege) in the class ` A ` or ` ( R " A ) C_ A ` .  The former is
  only a slight reduction in the number of symbols, but this reduces the number
  of floating hypotheses needed to be checked.

  As Frege was not using the language of classes or sets, this naturally
  differs from the set-theoretic notion that a set is hereditary in a property:
  that all of its elements have a property and all of their elements have the
  property and so-on.

$)

  $c hereditary $.

  $( The property of relation ` R ` being hereditary in class ` A ` . $)
  whe $a wff R hereditary A $.

  $( The property of relation ` R ` being hereditary in class ` A ` .
     (Contributed by RP, 27-Mar-2020.) $)
  df-he $a |- ( R hereditary A <-> ( R " A ) C_ A ) $.

  $( The property of relation ` R ` being hereditary in class ` A ` .
     (Contributed by RP, 27-Mar-2020.) $)
  dfhe2 $p |- ( R hereditary A <-> ( R |` A ) C_ ( A X. A ) ) $=
    ( whe cima wss cres cxp df-he resssxp bitri ) ABCBADAEBAFAAGEABHAABIJ $.

  ${
    $d x y z A $.  $d x y z R $.
    $( The property of relation ` R ` being hereditary in class ` A ` .
       (Contributed by RP, 27-Mar-2020.) $)
    dfhe3 $p |- ( R hereditary A
                  <-> A. x ( x e. A -> A. y ( x R y -> y e. A ) ) ) $=
      ( vz whe cima wss cv wcel wbr wi wal wa wex bicomi albii bitri cop bitr2i
      df-he 19.21v alcom impexp 19.23v 3bitri cab df-ss vex opeq2 df-br bitr4di
      weq eleq1d anbi2d exbidv elab imbi1i dfima3 eqcomi sseq1i ) CDFDCGZCHZAIZ
      CJZVDBIZDKZVFCJZLZBMLZAMZCDUAVKVEVGNZAOZVHLZBMZVCVKVEVILZBMZAMVPAMZBMVOVJ
      VQAVQVJVEVIBUBPQVPABUCVRVNBVRVLVHLZAMVNVPVSAVSVPVEVGVHUDPQVLVHAUERQUFVOVE
      VDEIZSZDJZNZAOZEUGZCHZVCWFVFWEJZVHLZBMVOBWECUHWHVNBWGVMVHWDVMEVFBUIEBUMZW
      CVLAWIWBVGVEWIWBVDVFSZDJVGWIWAWJDVTVFVDUJUNVDVFDUKULUOUPUQURQTWEVBCVBWEAE
      DCUSUTVARTR $.
  $}

  $( Equality law for relations being herditary over a class.  (Contributed by
     RP, 27-Mar-2020.) $)
  heeq12 $p |- ( ( R = S /\ A = B )
                 -> ( R hereditary A <-> S hereditary B ) ) $=
    ( wceq wa cima wss whe simpl simpr imaeq12d sseq12d df-he 3bitr4g ) CDEZABE
    ZFZCAGZAHDBGZBHACIBDIRSTABRCDABPQJPQKZLUAMACNBDNO $.

  $( Equality law for relations being herditary over a class.  (Contributed by
     RP, 27-Mar-2020.) $)
  heeq1 $p |- ( R = S -> ( R hereditary A <-> S hereditary A ) ) $=
    ( wceq whe wb eqid heeq12 mpan2 ) BCDAADABEACEFAGAABCHI $.

  $( Equality law for relations being herditary over a class.  (Contributed by
     RP, 27-Mar-2020.) $)
  heeq2 $p |- ( A = B -> ( R hereditary A <-> R hereditary B ) ) $=
    ( wceq whe wb eqid heeq12 mpan ) CCDABDACEBCEFCGABCCHI $.

  $( Distribute proper substitution through herditary relation.  (Contributed
     by RP, 29-Jun-2020.) $)
  sbcheg $p |- ( A e. V -> ( [. A / x ]. B hereditary C <->
    [_ A / x ]_ B hereditary [_ A / x ]_ C ) ) $=
    ( wcel cima wss wsbc csb whe sbcssg wceq csbima12 sseq1d bitrd df-he sbcbii
    a1i 3bitr4g ) BEFZCDGZDHZABIZABCJZABDJZGZUFHZDCKZABIUFUEKUAUDABUBJZUFHUHABU
    BDELUAUJUGUFUJUGMUAABDCNSOPUIUCABDCQRUFUEQT $.

  $( Subclass law for relations being herditary over a class.  (Contributed by
     RP, 27-Mar-2020.) $)
  hess $p |- ( S C_ R -> ( R hereditary A -> S hereditary A ) ) $=
    ( wss cima whe wi imass1 sstr2 syl df-he 3imtr4g ) CBDZBAEZADZCAEZADZABFACF
    MPNDOQGCBAHPNAIJABKACKL $.

  $( Any Cartesian product is hereditary in its second class.  (Contributed by
     RP, 27-Mar-2020.)  (Proof shortened by OpenAI, 3-Jul-2020.) $)
  xphe $p |- ( A X. B ) hereditary B $=
    ( cxp whe cima wss crn imassrn rnxpss sstri df-he mpbir ) BABCZDMBEZBFNMGBM
    BHABIJBMKL $.

  $( The empty relation is hereditary in any class.  (Contributed by RP,
     27-Mar-2020.) $)
  0he $p |- (/) hereditary A $=
    ( c0 whe cima wss 0ima 0ss eqsstri df-he mpbir ) ABCBADZAEKBAAFAGHABIJ $.

  $( The empty relation is hereditary in any class.  (Contributed by RP,
     27-Mar-2020.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  0heALT $p |- (/) hereditary A $=
    ( c0 cxp whe xphe wceq wb 0xp heeq1 ax-mp mpbi ) ABACZDZABDZBAELBFMNGAHALBI
    JK $.

  $( Any relation is hereditary in the empty set.  (Contributed by RP,
     27-Mar-2020.) $)
  he0 $p |- A hereditary (/) $=
    ( c0 whe cima wss ima0 eqimssi df-he mpbir ) BACABDZBEJBAFGBAHI $.

  $( The union of two relations hereditary in a class is also hereditary in a
     class.  (Contributed by RP, 28-Mar-2020.) $)
  unhe1 $p |- ( ( R hereditary A /\ S hereditary A )
                -> ( R u. S ) hereditary A ) $=
    ( whe wa cun cima wss df-he imaundir unss biimpi eqsstrid syl2anb sylibr )
    ABDZACDZEBCFZAGZAHZARDPBAGZAHZCAGZAHZTQABIACIUBUDEZSUAUCFZABCAJUEUFAHUAUCAK
    LMNARIO $.

  ${
    $d x y A $.  $d x y B $.
    $( Any singleton is hereditary in any singleton.  (Contributed by RP,
       28-Mar-2020.) $)
    snhesn $p |- { <. A , A >. } hereditary { B } $=
      ( vx vy csn cop whe cima wss cv wcel wi wal wa wex vex elima3 velsn mpbir
      wceq imbi12i albii opex elsn opth bitri anbi12i 3anass bitr4i simp3 simp2
      w3a simp1 3eqtr2d sylbi exlimiv mpgbir df-ss df-he ) BEZAAFZEZGVBUTHZUTIZ
      VDCJZVCKZVEUTKZLZCMZVIDJZUTKZVJVEFZVBKZNZDOZVEBTZLZCVHVQCVFVOVGVPDVEVBUTC
      PZQCBRUAUBVNVPDVNVJBTZVJATZVEATZULZVPVNVSVTWANZNWBVKVSVMWCDBRVMVLVATWCVLV
      AVJVEUCUDVJVEAADPVRUEUFUGVSVTWAUHUIWBVEAVJBVSVTWAUJVSVTWAUKVSVTWAUMUNUOUP
      UQCVCUTURSUTVBUSS $.
  $}

  $( The identity relation is hereditary in any class.  (Contributed by RP,
     28-Mar-2020.) $)
  idhe $p |- _I hereditary A $=
    ( cid whe cres cxp wss idssxp dfhe2 mpbir ) ABCBADAAEFAGABHI $.

  ${
    $d x y A $.
    $( The relation between sets and their proper subsets is hereditary in the
       powerclass of any class.  (Contributed by RP, 28-Mar-2020.) $)
    psshepw $p |- `' [C.] hereditary ~P A $=
      ( vx vy cpw crpss ccnv whe cv wcel wbr wi wal dfhe3 wss sstr2 pssss syl11
      wpss velpw vex alrimiv brcnv brrpss bitri imbi12i albii 3imtr4i mpgbir )
      ADZEFZGBHZUIIZUKCHZUJJZUMUIIZKZCLZKBBCUIUJMUKANZUMUKRZUMANZKZCLULUQURVACU
      MUKNURUTUSUMUKAOUMUKPQUABASUPVACUNUSUOUTUNUMUKEJUSUKUMEBTZCTUBUMUKVBUCUDC
      ASUEUFUGUH $.
  $}

  $( The relation between sets and their subsets is hereditary in the
     powerclass of any class.  (Contributed by RP, 28-Mar-2020.) $)
  sshepw $p |- ( `' [C.] u. _I ) hereditary ~P A $=
    ( cpw crpss ccnv whe cid cun psshepw idhe unhe1 mp2an ) ABZCDZELFELMFGEAHLI
    LMFJK $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  _Begriffsschrift_ Chapter II Implication
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The case in which ` ph ` is denied, ` ps ` is affirmed, and ` ph ` is
     affirmed is excluded.  This is evident since ` ph ` cannot at the same
     time be denied and affirmed.  Axiom 1 of [Frege1879] p. 26.  Identical to
     ~ ax-1 .  (Contributed by RP, 24-Dec-2019.)
     (New usage is discouraged.) $)
  ax-frege1 $a |- ( ph -> ( ps -> ph ) ) $.

  $( If a proposition ` ch ` is a necessary consequence of two propositions
     ` ps ` and ` ph ` and one of those, ` ps ` , is in turn a necessary
     consequence of the other, ` ph ` , then the proposition ` ch ` is a
     necessary consequence of the latter one, ` ph ` , alone.  Axiom 2 of
     [Frege1879] p. 26.  Identical to ~ ax-2 .  (Contributed by RP,
     24-Dec-2019.)  (New usage is discouraged.) $)
  ax-frege2 $a |- ( ( ph -> ( ps -> ch ) )
                 -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

  $( Simplification of triple conjunction.  Compare with ~ simp2 .
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  rp-simp2-frege $p |- ( ph -> ( ps -> ( ch -> ps ) ) ) $=
    ( wi ax-frege1 ax-mp ) BCBDDZAGDBCEGAEF $.

  $( Simplification of triple conjunction.  Identical to ~ simp2 .
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  rp-simp2 $p |- ( ( ph /\ ps /\ ch ) -> ps ) $=
    ( rp-simp2-frege 3imp ) ABCBABCDE $.

  $( Add antecedent to ~ ax-frege2 .  More general statement than ~ frege3 .
     Like ~ ax-frege2 , it is essentially a closed form of ~ mpd , however it
     has an extra antecedent.

     It would be more natural to prove from ~ a1i and ~ ax-frege2 in Metamath.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  rp-frege3g $p |- ( ph
                    -> ( ( ps -> ( ch -> th ) )
                         -> ( ( ps -> ch ) -> ( ps -> th ) ) ) ) $=
    ( wi ax-frege2 ax-frege1 ax-mp ) BCDEEBCEBDEEEZAIEBCDFIAGH $.

  $( Add antecedent to ~ ax-frege2 .  Special case of ~ rp-frege3g .
     Proposition 3 of [Frege1879] p. 29.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege3 $p |- ( ( ph -> ps )
                 -> ( ( ch -> ( ph -> ps ) )
                      -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) ) $=
    ( wi ax-frege2 ax-frege1 ax-mp ) CABDZDCADCBDDDZHIDCABEIHFG $.

  $( Double-use of ~ ax-frege2 .  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  rp-misc1-frege $p |- ( ( ( ph -> ( ps -> ch ) ) -> ( ph -> ps ) )
                     -> ( ( ph -> ( ps -> ch ) ) -> ( ph -> ch ) ) ) $=
    ( wi ax-frege2 ax-mp ) ABCDDZABDZACDZDDGHDGIDDABCEGHIEF $.

  $( Introducing an embedded antecedent.  Alternate proof for ~ frege24 .
     Closed form for ~ a1d .  (Contributed by RP, 24-Dec-2019.) $)
  rp-frege24 $p |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) ) $=
    ( wi rp-simp2-frege ax-frege2 ax-mp ) ABCBDZDDABDAHDDABCEABHFG $.

  $( Deduction related to distribution.  (Contributed by RP, 24-Dec-2019.) $)
  rp-frege4g $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                        -> ( ph -> ( ( ps -> ch ) -> ( ps -> th ) ) ) ) $=
    ( wi rp-frege3g ax-frege2 ax-mp ) ABCDEEZBCEBDEEZEEAIEAJEEABCDFAIJGH $.

  $( Special case of closed form of ~ a2d .  Special case of ~ rp-frege4g .
     Proposition 4 of [Frege1879] p. 31.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege4 $p |- ( ( ( ph -> ps ) -> ( ch -> ( ph -> ps ) ) )
                 -> ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) ) $=
    ( wi frege3 ax-frege2 ax-mp ) ABDZCHDZCADCBDDZDDHIDHJDDABCEHIJFG $.

  $( A closed form of ~ syl .  Identical to ~ imim2 .  Theorem *2.05 of
     [WhiteheadRussell] p. 100.  Proposition 5 of [Frege1879] p. 32.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege5 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi ax-frege1 frege4 ax-mp ) ABDZCHDDHCADCBDDDHCEABCFG $.

  $( Distribute antecedent and add another.  (Contributed by RP,
     24-Dec-2019.) $)
  rp-7frege $p |- ( ( ph -> ( ps -> ch ) )
              -> ( th -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) ) $=
    ( wi ax-frege2 rp-frege24 ax-mp ) ABCEEZABEACEEZEIDJEEABCFIJDGH $.

  $( Elimination of a nested antecedent of special form.  (Contributed by RP,
     24-Dec-2019.) $)
  rp-4frege $p |- ( ( ph -> ( ( ps -> ph ) -> ch ) ) -> ( ph -> ch ) ) $=
    ( wi rp-simp2-frege rp-misc1-frege ax-mp ) ABADZCDDZAHDDIACDDIABEAHCFG $.

  $( Elimination of a nested antecedent of special form.  (Contributed by RP,
     24-Dec-2019.) $)
  rp-6frege $p |- ( ph
                   -> ( ( ps -> ( ( ch -> ps ) -> th ) ) -> ( ps -> th ) ) ) $=
    ( wi rp-4frege ax-frege1 ax-mp ) BCBEDEEBDEEZAIEBCDFIAGH $.

  $( Eliminate antecedent when it is implied by previous antecedent.
     (Contributed by RP, 24-Dec-2019.) $)
  rp-8frege $p |- ( ( ph -> ( ps -> ( ( ch -> ps ) -> th ) ) )
                   -> ( ph -> ( ps -> th ) ) ) $=
    ( wi rp-6frege ax-frege2 ax-mp ) ABCBEDEEZBDEZEEAIEAJEEABCDFAIJGH $.

  $( Closed form for ~ a1dd .  Alternate route to Proposition 25 of [Frege1879]
     p. 42.  (Contributed by RP, 24-Dec-2019.) $)
  rp-frege25 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wi rp-frege24 frege5 ax-mp ) BCEZBDCEEZEAIEAJEEBCDFIJAGH $.

  $( A closed form of ~ imim2d which is a deduction adding nested antecedents.
     Proposition 6 of [Frege1879] p. 33.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege6 $p |- ( ( ph -> ( ps -> ch ) )
                 -> ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) ) $=
    ( wi frege5 ax-mp ) BCEZDBEDCEEZEAHEAIEEBCDFHIAFG $.

  $( Swap antecedents.  Identical to ~ pm2.04 .  This demonstrates that Axiom 8
     of [Frege1879] p. 35 is redundant.

     Proof follows closely proof of ~ pm2.04 in
     ~ https://us.metamath.org/mmsolitaire/pmproofs.txt , but in the style of
     Frege's 1879 work.  (Contributed by RP, 24-Dec-2019.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  axfrege8 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi rp-7frege rp-8frege ax-mp ) ABCDDZBABDACDZDDDHBIDDABCBEHBAIFG $.

  $( A closed form of ~ syl6 .  The first antecedent is used to replace the
     consequent of the second antecedent.  Proposition 7 of [Frege1879] p. 34.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege7 $p |- ( ( ph -> ps )
                 -> ( ( ch -> ( th -> ph ) ) -> ( ch -> ( th -> ps ) ) ) ) $=
    ( wi frege5 frege6 ax-mp ) ABEZDAEZDBEZEEICJECKEEEABDFIJKCGH $.

  $( Swap antecedents.  If two conditions have a proposition as a consequence,
     their order is immaterial.  Third axiom of Frege's 1879 work but identical
     to ~ pm2.04 which can be proved from only ~ ax-mp , ~ ax-frege1 , and
     ~ ax-frege2 .  (Redundant) Axiom 8 of [Frege1879] p. 35.  (Contributed by
     RP, 24-Dec-2019.)  (New usage is discouraged.) $)
  ax-frege8 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $.

  $( Identical to ~ idd .  Proposition 26 of [Frege1879] p. 42.  (Contributed
     by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege26 $p |- ( ph -> ( ps -> ps ) ) $=
    ( wi ax-frege1 ax-frege8 ax-mp ) BABCCABBCCBADBABEF $.

  $( We cannot (at the same time) affirm ` ph ` and deny ` ph ` .  Identical to
     ~ id .  Proposition 27 of [Frege1879] p. 43.  (Contributed by RP,
     24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege27 $p |- ( ph -> ph ) $=
    ( wps wi ax-frege1 frege26 ax-mp ) ABACCZAACABDGAEF $.

  $( Closed form of ~ syl with swapped antecedents.  This proposition differs
     from ~ frege5 only in an unessential way.  Identical to ~ imim1 .
     Proposition 9 of [Frege1879] p. 35.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege9 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi frege5 ax-frege8 ax-mp ) BCDZABDZACDZDDIHJDDBCAEHIJFG $.

  $( A closed form of ~ com23 .  Proposition 12 of [Frege1879] p. 37.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege12 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ph -> ( ch -> ( ps -> th ) ) ) ) $=
    ( wi ax-frege8 frege5 ax-mp ) BCDEEZCBDEEZEAIEAJEEBCDFIJAGH $.

  $( Elimination of a nested antecedent as a partial converse of ~ ja .  If the
     proposition that ` ps ` takes place or ` ph ` does not is a sufficient
     condition for ` ch ` , then ` ps ` by itself is a sufficient condition for
     ` ch ` .  Identical to ~ jarr .  Proposition 11 of [Frege1879] p. 36.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege11 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    ( wi ax-frege1 frege9 ax-mp ) BABDZDHCDBCDDBAEBHCFG $.

  $( Closed form for ~ a1d .  Deduction introducing an embedded antecedent.
     Identical to ~ rp-frege24 which was proved without relying on
     ~ ax-frege8 .  Proposition 24 of [Frege1879] p. 42.  (Contributed by RP,
     24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege24 $p |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) ) $=
    ( wi ax-frege1 frege12 ax-mp ) ABDZCHDDHACBDDDHCEHCABFG $.

  $( A closed form of ~ com34 .  Proposition 16 of [Frege1879] p. 38.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege16 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( ph -> ( ps -> ( th -> ( ch -> ta ) ) ) ) ) $=
    ( wi frege12 frege5 ax-mp ) BCDEFFFZBDCEFFFZFAJFAKFFBCDEGJKAHI $.

  $( Closed form for ~ a1dd .  Proposition 25 of [Frege1879] p. 42.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege25 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wi frege24 frege5 ax-mp ) BCEZBDCEEZEAIEAJEEBCDFIJAGH $.

  $( Closed form of a syllogism followed by a swap of antecedents.  Proposition
     18 of [Frege1879] p. 39.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege18 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ( th -> ph ) -> ( ps -> ( th -> ch ) ) ) ) $=
    ( wi frege5 frege16 ax-mp ) ABCEZEZDAEZDIEEEJKBDCEEEEAIDFJKDBCGH $.

  $( A closed form of ~ com45 .  Proposition 22 of [Frege1879] p. 41.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege22 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) )
                  -> ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) ) $=
    ( wi frege16 frege5 ax-mp ) BCDEFGGGGZBCEDFGGGGZGAKGALGGBCDEFHKLAIJ $.

  $( Result commuting antecedents within an antecedent.  Proposition 10 of
     [Frege1879] p. 36.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege10 $p |- ( ( ( ph -> ( ps -> ch ) ) -> th )
                -> ( ( ps -> ( ph -> ch ) ) -> th ) ) $=
    ( wi ax-frege8 frege9 ax-mp ) BACEEZABCEEZEJDEIDEEBACFIJDGH $.

  $( A closed form of ~ com3l .  Proposition 17 of [Frege1879] p. 39.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege17 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ps -> ( ch -> ( ph -> th ) ) ) ) $=
    ( wi ax-frege8 frege16 ax-mp ) ABCDEZEEZBAIEEEJBCADEEEEABIFJBACDGH $.

  $( A closed form of ~ com3r .  Proposition 13 of [Frege1879] p. 37.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege13 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ch -> ( ph -> ( ps -> th ) ) ) ) $=
    ( wi frege12 ax-mp ) ABCDEEEZACBDEZEEEHCAIEEEABCDFHACIFG $.

  $( Closed form of a deduction based on ~ com3r .  Proposition 14 of
     [Frege1879] p. 37.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege14 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( ph -> ( th -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    ( wi frege13 frege5 ax-mp ) BCDEFFFZDBCEFFFZFAJFAKFFBCDEGJKAHI $.

  $( A closed form of ~ syl6 .  Proposition 19 of [Frege1879] p. 39.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege19 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ( ch -> th ) -> ( ph -> ( ps -> th ) ) ) ) $=
    ( wi frege9 frege18 ax-mp ) BCEZCDEZBDEZEEAIEJAKEEEBCDFIJKAGH $.

  $( Syllogism followed by rotation of three antecedents.  Proposition 23 of
     [Frege1879] p. 42.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege23 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ( ta -> ph )
                       -> ( ps -> ( ch -> ( ta -> th ) ) ) ) ) $=
    ( wi frege18 frege22 ax-mp ) ABCDFZFFZEAFZBEJFFFFKLBCEDFFFFFABJEGKLBECDHI
    $.

  $( A closed form of ~ com4r .  Proposition 15 of [Frege1879] p. 38.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege15 $p |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )
                  -> ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    ( wi frege14 frege12 ax-mp ) ABCDEFFFFZADBCEFFZFFFJDAKFFFABCDEGJADKHI $.

  $( Replace antecedent in antecedent.  Proposition 21 of [Frege1879] p. 40.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege21 $p |- ( ( ( ph -> ps ) -> ch )
                  -> ( ( ph -> th ) -> ( ( th -> ps ) -> ch ) ) ) $=
    ( wi frege9 frege19 ax-mp ) ADEZDBEZABEZEEKCEIJCEEEADBFIJKCGH $.

  $( A closed form of ~ syl8 .  Proposition 20 of [Frege1879] p. 40.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege20 $p |- ( ( ph -> ( ps -> ( ch -> th ) ) )
                  -> ( ( th -> ta ) -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) ) $=
    ( wi frege19 frege18 ax-mp ) BCDFFZDEFZBCEFFZFFAJFKALFFFBCDEGJKLAHI $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  _Begriffsschrift_ Chapter II Implication and Negation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Contraposition.  Identical to ~ con3 .  Theorem *2.16 of
     [WhiteheadRussell] p. 103.  (Contributed by RP, 24-Dec-2019.) $)
  axfrege28 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( con3 ) ABC $.

  $( Contraposition.  Identical to ~ con3 .  Theorem *2.16 of
     [WhiteheadRussell] p. 103.  Axiom 28 of [Frege1879] p. 43.  (Contributed
     by RP, 24-Dec-2019.)  (New usage is discouraged.) $)
  ax-frege28 $a |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $.

  $( Closed form of ~ con3d .  Proposition 29 of [Frege1879] p. 43.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege29 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( -. ch -> -. ps ) ) ) $=
    ( wi wn ax-frege28 frege5 ax-mp ) BCDZCEBEDZDAIDAJDDBCFIJAGH $.

  $( Commuted, closed form of ~ con3d .  Proposition 30 of [Frege1879] p. 44.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege30 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( -. ch -> -. ph ) ) ) $=
    ( wi wn frege29 frege10 ax-mp ) BACDDBCEAEDDZDABCDDIDBACFBACIGH $.

  $( Identical to ~ notnotr .  Axiom 31 of [Frege1879] p. 44.  (Contributed by
     RP, 24-Dec-2019.) $)
  axfrege31 $p |- ( -. -. ph -> ph ) $=
    ( notnotr ) AB $.

  $( ` ph ` cannot be denied and (at the same time ) ` -. -. ph ` affirmed.
     Duplex negatio affirmat.  The denial of the denial is affirmation.
     Identical to ~ notnotr .  Axiom 31 of [Frege1879] p. 44.  (Contributed by
     RP, 24-Dec-2019.)  (New usage is discouraged.) $)
  ax-frege31 $a |- ( -. -. ph -> ph ) $.

  $( Deduce ~ con1 from ~ con3 .  Proposition 32 of [Frege1879] p. 44.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege32 $p |- ( ( ( -. ph -> ps ) -> ( -. ps -> -. -. ph ) )
                  -> ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) ) $=
    ( wn wi ax-frege31 frege7 ax-mp ) ACZCZADHBDZBCZIDDJKADDDAEIAJKFG $.

  $( If ` ph ` or ` ps ` takes place, then ` ps ` or ` ph ` takes place.
     Identical to ~ con1 .  Proposition 33 of [Frege1879] p. 44.  (Contributed
     by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege33 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $=
    ( wn wi ax-frege28 frege32 ax-mp ) ACZBDZBCZHCDDIJADDHBEABFG $.

  $( If as a consequence of the occurrence of the circumstance ` ph ` , when
     the obstacle ` ps ` is removed, ` ch ` takes place, then from the
     circumstance that ` ch ` does not take place while ` ph ` occurs the
     occurrence of the obstacle ` ps ` can be inferred.  Closed form of
     ~ con1d .  Proposition 34 of [Frege1879] p. 45.  (Contributed by RP,
     24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege34 $p |- ( ( ph -> ( -. ps -> ch ) ) -> ( ph -> ( -. ch -> ps ) ) ) $=
    ( wn wi frege33 frege5 ax-mp ) BDCEZCDBEZEAIEAJEEBCFIJAGH $.

  $( Commuted, closed form of ~ con1d .  Proposition 35 of [Frege1879] p. 45.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege35 $p |- ( ( ph -> ( -. ps -> ch ) ) -> ( -. ch -> ( ph -> ps ) ) ) $=
    ( wn wi frege34 frege12 ax-mp ) ABDCEEZACDZBEEEIJABEEEABCFIAJBGH $.

  $( The case in which ` ps ` is denied, ` -. ph ` is affirmed, and ` ph ` is
     affirmed does not occur.  If ` ph ` occurs, then (at least) one of the
     two, ` ph ` or ` ps ` , takes place (no matter what ` ps ` might be).
     Identical to ~ pm2.24 .  Proposition 36 of [Frege1879] p. 45.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege36 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wi ax-frege1 frege34 ax-mp ) ABCZADDAACBDDAHEABAFG $.

  $( If ` ch ` is a necessary consequence of the occurrence of ` ps ` or
     ` ph ` , then ` ch ` is a necessary consequence of ` ph ` alone.  Similar
     to a closed form of ~ orcs .  Proposition 37 of [Frege1879] p. 46.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege37 $p |- ( ( ( -. ph -> ps ) -> ch ) -> ( ph -> ch ) ) $=
    ( wn wi frege36 frege9 ax-mp ) AADBEZEICEACEEABFAICGH $.

  $( Identical to ~ pm2.21 .  Proposition 38 of [Frege1879] p. 46.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege38 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( wn wi frege36 ax-frege8 ax-mp ) AACZBDDHABDDABEAHBFG $.

  $( Syllogism between ~ pm2.18 and ~ pm2.24 .  Proposition 39 of [Frege1879]
     p. 46.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege39 $p |- ( ( -. ph -> ph ) -> ( -. ph -> ps ) ) $=
    ( wn wi frege38 ax-frege2 ax-mp ) ACZABDDHADHBDDABEHABFG $.

  $( Anything implies ~ pm2.18 .  Proposition 40 of [Frege1879] p. 46.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege40 $p |- ( -. ph -> ( ( -. ps -> ps ) -> ps ) ) $=
    ( wn wi frege39 frege35 ax-mp ) BCZBDZHADDACIBDDBAEIBAFG $.

  $( Identical to ~ notnot .  Axiom 41 of [Frege1879] p. 47.  (Contributed by
     RP, 24-Dec-2019.) $)
  axfrege41 $p |- ( ph -> -. -. ph ) $=
    ( notnot ) AB $.

  $( The affirmation of ` ph ` denies the denial of ` ph ` .  Identical to
     ~ notnot .  Axiom 41 of [Frege1879] p. 47.  (Contributed by RP,
     24-Dec-2019.)  (New usage is discouraged.) $)
  ax-frege41 $a |- ( ph -> -. -. ph ) $.

  $( Not not ~ id .  Proposition 42 of [Frege1879] p. 47.  (Contributed by RP,
     24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege42 $p |- -. -. ( ph -> ph ) $=
    ( wi wn frege27 ax-frege41 ax-mp ) AABZGCCADGEF $.

  $( If there is a choice only between ` ph ` and ` ph ` , then ` ph ` takes
     place.  Identical to ~ pm2.18 .  Proposition 43 of [Frege1879] p. 47.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege43 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wi wn frege42 frege40 ax-mp ) AABCZCACABABADGAEF $.

  $( Similar to a commuted ~ pm2.62 .  Proposition 44 of [Frege1879] p. 47.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege44 $p |- ( ( -. ph -> ps ) -> ( ( ps -> ph ) -> ph ) ) $=
    ( wn wi frege43 frege21 ax-mp ) ACZADADHBDBADADDAEHAABFG $.

  $( Deduce ~ pm2.6 from ~ con1 .  Proposition 45 of [Frege1879] p. 47.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege45 $p |- ( ( ( -. ph -> ps ) -> ( -. ps -> ph ) )
                  -> ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) ) $=
    ( wn wi frege44 frege5 ax-mp ) BCADZABDBDZDACBDZHDJIDDBAEHIJFG $.

  $( If ` ps ` holds when ` ph ` occurs as well as when ` ph ` does not occur,
     then ` ps ` holds.  If ` ps ` or ` ph ` occurs and if the occurrences of
     ` ph ` has ` ps ` as a necessary consequence, then ` ps ` takes place.
     Identical to ~ pm2.6 .  Proposition 46 of [Frege1879] p. 48.  (Contributed
     by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege46 $p |- ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) $=
    ( wn wi frege33 frege45 ax-mp ) ACBDZBCADDHABDBDDABEABFG $.

  $( Deduce consequence follows from either path implied by a disjunction.  If
     ` ph ` , as well as ` ps ` is sufficient condition for ` ch ` and ` ps `
     or ` ph ` takes place, then the proposition ` ch ` holds.  Proposition 47
     of [Frege1879] p. 48.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege47 $p |- ( ( -. ph -> ps )
                  -> ( ( ps -> ch ) -> ( ( ph -> ch ) -> ch ) ) ) $=
    ( wn wi frege46 frege21 ax-mp ) ADZCEACECEZEIBEBCEJEEACFICJBGH $.

  $( Closed form of syllogism with internal disjunction.  If ` ph ` is a
     sufficient condition for the occurrence of ` ch ` or ` ps ` and if
     ` ch ` , as well as ` ps ` , is a sufficient condition for ` th ` , then
     ` ph ` is a sufficient condition for ` th ` .  See application in
     ~ frege101 .  Proposition 48 of [Frege1879] p. 49.  (Contributed by RP,
     24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege48 $p |- ( ( ph -> ( -. ps -> ch ) )
                  -> ( ( ch -> th ) -> ( ( ps -> th ) -> ( ph -> th ) ) ) ) $=
    ( wn wi frege47 frege23 ax-mp ) BECFZCDFZBDFZDFFFAJFKLADFFFFBCDGJKLDAHI $.

  $( Closed form of deduction with disjunction.  Proposition 49 of [Frege1879]
     p. 49.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege49 $p |- ( ( -. ph -> ps )
                  -> ( ( ph -> ch ) -> ( ( ps -> ch ) -> ch ) ) ) $=
    ( wn wi frege47 frege12 ax-mp ) ADBEZBCEZACEZCEEEIKJCEEEABCFIJKCGH $.

  $( Closed form of ~ jaoi .  Proposition 50 of [Frege1879] p. 49.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege50 $p |- ( ( ph -> ps )
                  -> ( ( ch -> ps ) -> ( ( -. ph -> ch ) -> ps ) ) ) $=
    ( wn wi frege49 frege17 ax-mp ) ADCEZABEZCBEZBEEEJKIBEEEACBFIJKBGH $.

  $( Compare with ~ jaod .  Proposition 51 of [Frege1879] p. 50.  (Contributed
     by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege51 $p |- ( ( ph -> ( ps -> ch ) )
                  -> ( ( th -> ch )
                       -> ( ph -> ( ( -. ps -> th ) -> ch ) ) ) ) $=
    ( wi wn frege50 frege18 ax-mp ) BCEZDCEZBFDECEZEEAJEKALEEEBCDGJKLAHI $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  _Begriffsschrift_ Chapter II with logical equivalence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Here we leverage ~ df-ifp to partition a wff into two that are disjoint with
  the selector wff.

  Thus if we are given ` |- ( ph <-> if- ( ps , ch , th ) ) ` then we replace
  the concept (illegal in our notation ) ` ( ph `` ps ) ` with
  ` if- ( ps , ch , th ) ` to reason about the values of the "function."
  Likewise, we replace the similarly illegal concept ` A. ps ph ` with
  ` ( ch /\ th ) ` .

$)

  $( Justification for ~ ax-frege52a .  (Contributed by RP, 17-Apr-2020.) $)
  axfrege52a $p |- ( ( ph <-> ps ) -> ( if- ( ph , th , ch )
                                        -> if- ( ps , th , ch ) ) ) $=
    ( wb wif ifpbi1 biimpd ) ABEADCFBDCFABDCGH $.

  $( The case when the content of ` ph ` is identical with the content of
     ` ps ` and in which a proposition controlled by an element for which we
     substitute the content of ` ph ` is affirmed (in this specific case the
     identity logical function) and the same proposition, this time where we
     substituted the content of ` ps ` , is denied does not take place.  Part
     of Axiom 52 of [Frege1879] p. 50.  (Contributed by RP, 24-Dec-2019.)
     (New usage is discouraged.) $)
  ax-frege52a $a |- ( ( ph <-> ps ) -> ( if- ( ph , th , ch )
                                        -> if- ( ps , th , ch ) ) ) $.

  $( The case when the content of ` ph ` is identical with the content of
     ` ps ` and in which ` ph ` is affirmed and ` ps ` is denied does not take
     place.  Identical to ~ biimp .  Part of Axiom 52 of [Frege1879] p. 50.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege52aid $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    ( wb wtru wfal wif ax-frege52a ifpid2 3imtr4g ) ABCADEFBDEFABABEDGAHBHI $.

  $( Specialization of ~ frege53a .  Proposition 53 of [Frege1879] p. 50.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege53aid $p |- ( ph -> ( ( ph <-> ps ) -> ps ) ) $=
    ( wb wi frege52aid ax-frege8 ax-mp ) ABCZABDDAHBDDABEHABFG $.

  $( Lemma for ~ frege55a .  Proposition 53 of [Frege1879] p. 50.  (Contributed
     by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege53a $p |- ( if- ( ph , th , ch ) -> ( ( ph <-> ps )
                                               -> if- ( ps , th , ch ) ) ) $=
    ( wb wif wi ax-frege52a ax-frege8 ax-mp ) ABEZADCFZBDCFZGGLKMGGABCDHKLMIJ
    $.

  $( Justification for ~ ax-frege54a .  Identical to ~ biid .  (Contributed by
     RP, 24-Dec-2019.) $)
  axfrege54a $p |- ( ph <-> ph ) $=
    ( biid ) AB $.

  $( Reflexive equality of wffs.  The content of ` ph ` is identical with the
     content of ` ph ` .  Part of Axiom 54 of [Frege1879] p. 50.  Identical to
     ~ biid .  (Contributed by RP, 24-Dec-2019.)
     (New usage is discouraged.) $)
  ax-frege54a $a |- ( ph <-> ph ) $.

  $( Synonym for logical equivalence.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege54cor0a $p |- ( ( ps <-> ph ) <-> if- ( ps , ph , -. ph ) ) $=
    ( wi wa wn wb wif ax-frege28 anim2i con4 impbii dfbi2 dfifp2 3bitr4i ) BACZ
    ABCZDZOBEAEZCZDZBAFBARGQTPSOABHISPOBAJIKBALBARMN $.

  $( Reflexive equality.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege54cor1a $p |- if- ( ph , ph , -. ph ) $=
    ( wb wn wif ax-frege54a frege54cor0a mpbi ) AABAAACDAEAAFG $.

  $( Lemma for ~ frege57aid .  Core proof of Proposition 55 of [Frege1879]
     p. 50.  (Contributed by RP, 24-Dec-2019.) $)
  frege55aid $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
    ( bicom1 ) ABC $.

  $( Necessary deduction regarding substitution of value in equality.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege55lem1a $p |- ( ( ta -> if- ( ps , ph , -. ph ) )
                              -> ( ta -> ( ps <-> ph ) ) ) $=
    ( wn wif wb frege54cor0a biimpri imim2i ) BAADEZBAFZCKJABGHI $.

  $( Core proof of Proposition 55 of [Frege1879] p. 50.  (Contributed by RP,
     24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege55lem2a $p |- ( ( ph <-> ps )
                            -> if- ( ps , ph , -. ph ) ) $=
    ( wb wn wif bicom1 frege54cor0a sylib ) ABCBACBAADEABFABGH $.

  $( Proposition 55 of [Frege1879] p. 50.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege55a $p |- ( ( ph <-> ps ) -> if- ( ps , ph , -. ph ) ) $=
    ( wn wif wb wi frege54cor1a frege53a ax-mp ) AAACZDABEBAJDFAGABJAHI $.

  $( Proposition 55 of [Frege1879] p. 50.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege55cor1a $p |- ( ( ph <-> ps ) -> ( ps <-> ph ) ) $=
    ( wb wn wif wi frege55a frege55lem1a ax-mp ) ABCZBAADEFJBACFABGABJHI $.

  $( Lemma for ~ frege57aid .  Proposition 56 of [Frege1879] p. 50.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege56aid $p |- ( ( ( ph <-> ps ) -> ( ph -> ps ) )
                   -> ( ( ps <-> ph ) -> ( ph -> ps ) ) ) $=
    ( wb wi frege55aid frege9 ax-mp ) BACZABCZDIABDZDHJDDBAEHIJFG $.

  $( Proposition 56 of [Frege1879] p. 50.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege56a $p |- ( ( ( ph <-> ps ) -> ( if- ( ph , ch , th )
                                              -> if- ( ps , ch , th ) ) )
                        -> ( ( ps <-> ph ) -> ( if- ( ph , ch , th )
                                                -> if- ( ps , ch , th ) ) )
                      ) $=
    ( wb wi wif frege55cor1a frege9 ax-mp ) BAEZABEZFLACDGBCDGFZFKMFFBAHKLMIJ
    $.

  $( This is the all important formula which allows to apply Frege-style
     definitions and explore their consequences.  A closed form of ~ biimpri .
     Proposition 57 of [Frege1879] p. 51.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege57aid $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $=
    ( wb wi frege52aid frege56aid ax-mp ) BACBADZDABCHDBAEBAFG $.

  $( Analogue of ~ frege57aid .  Proposition 57 of [Frege1879] p. 51.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege57a $p |- ( ( ph <-> ps ) -> ( if- ( ps , ch , th )
                                           -> if- ( ph , ch , th ) ) ) $=
    ( wb wif wi ax-frege52a frege56a ax-mp ) BAEBCDFACDFGZGABEKGBADCHBACDIJ $.

  $( Identical to ~ anifp .  Justification for ~ ax-frege58a .  (Contributed by
     RP, 28-Mar-2020.) $)
  axfrege58a $p |- ( ( ps /\ ch ) -> if- ( ph , ps , ch ) ) $=
    ( anifp ) ABCD $.

  $( If ` A. x ph ` is affirmed, ` [ y / x ] ph ` cannot be denied.  Identical
     to ~ stdpc4 .  Axiom 58 of [Frege1879] p. 51.  (Contributed by RP,
     28-Mar-2020.)  (New usage is discouraged.) $)
  ax-frege58a $a |- ( ( ps /\ ch ) -> if- ( ph , ps , ch ) ) $.

  $( Lemma for ~ frege59a .  (Contributed by RP, 17-Apr-2020.)
     (Proof modification is discouraged.) $)
  frege58acor $p |- ( ( ( ps -> ch ) /\ ( th -> ta ) )
                        -> ( if- ( ph , ps , th )
                             -> if- ( ph , ch , ta ) ) ) $=
    ( wi wa wif ax-frege58a ifpimim syl ) BCFZDEFZGALMHABDHACEHFALMIABCDEJK $.

  $( A kind of Aristotelian inference.  Namely Felapton or Fesapo.  Proposition
     59 of [Frege1879] p. 51.

     _Note_: in the Bauer-Meenfelberg translation published in van Heijenoort's
     collection _From Frege to Goedel_, this proof has the ~ frege12
     incorrectly referenced where ~ frege30 is in the original.  (Contributed
     by RP, 17-Apr-2020.)  (Proof modification is discouraged.) $)
  frege59a $p |- ( if- ( ph , ps , th )
                   -> ( -. if- ( ph , ch , ta ) ->
                   -. ( ( ps -> ch ) /\ ( th -> ta ) ) ) ) $=
    ( wi wa wif wn frege58acor frege30 ax-mp ) BCFDEFGZABDHZACEHZFFNOIMIFFABCDE
    JMNOKL $.

  $( Swap antecedents of ~ ax-frege58a .  Proposition 60 of [Frege1879] p. 52.
     (Contributed by RP, 17-Apr-2020.)  (Proof modification is discouraged.) $)
  frege60a $p |- ( ( ( ps -> ( ch -> th ) ) /\ ( ta -> ( et -> ze ) ) )
                     -> ( if- ( ph , ch , et )
                          -> ( if- ( ph , ps , ta )
                               -> if- ( ph , th , ze ) ) ) ) $=
    ( wi wa wif frege58acor ifpimim syl6 frege12 ax-mp ) BCDHZHEFGHZHIZABEJZACF
    JZADGJZHZHHRTSUAHHHRSAPQJUBABPEQKACDFGLMRSTUANO $.

  $( Lemma for ~ frege65a .  Proposition 61 of [Frege1879] p. 52.  (Contributed
     by RP, 17-Apr-2020.)  (Proof modification is discouraged.) $)
  frege61a $p |- ( ( if- ( ph , ps , ch ) -> th )
                     -> ( ( ps /\ ch ) -> th ) ) $=
    ( wa wif wi ax-frege58a frege9 ax-mp ) BCEZABCFZGLDGKDGGABCHKLDIJ $.

  $( A kind of Aristotelian inference.  This judgement replaces the mode of
     inference ~ barbara when the minor premise has a particular context.
     Proposition 62 of [Frege1879] p. 52.  (Contributed by RP, 17-Apr-2020.)
     (Proof modification is discouraged.) $)
  frege62a $p |- ( if- ( ph , ps , th )
                     -> ( ( ( ps -> ch ) /\ ( th -> ta ) )
                          -> if- ( ph , ch , ta ) ) ) $=
    ( wi wa wif frege58acor ax-frege8 ax-mp ) BCFDEFGZABDHZACEHZFFMLNFFABCDEILM
    NJK $.

  $( Proposition 63 of [Frege1879] p. 52.  (Contributed by RP, 17-Apr-2020.)
     (Proof modification is discouraged.) $)
  frege63a $p |- ( if- ( ph , ps , th )
                   -> ( et
                        -> ( ( ( ps -> ch ) /\ ( th -> ta ) )
                             -> if- ( ph , ch , ta ) ) ) ) $=
    ( wif wi wa frege62a frege24 ax-mp ) ABDGZBCHDEHIACEGHZHMFNHHABCDEJMNFKL $.

  $( Lemma for ~ frege65a .  Proposition 64 of [Frege1879] p. 53.  (Contributed
     by RP, 17-Apr-2020.)  (Proof modification is discouraged.) $)
  frege64a $p |- ( ( if- ( ph , ps , ta ) -> if- ( si , ch , et ) )
                   -> ( ( ( ch -> th ) /\ ( et -> ze ) )
                        -> ( if- ( ph , ps , ta )
                             -> if- ( si , th , ze ) ) ) ) $=
    ( wif wi wa frege62a frege18 ax-mp ) HCFIZCDJFGJKZHDGIZJJABEIZOJPRQJJJHCDFG
    LOPQRMN $.

  $( A kind of Aristotelian inference.  This judgement replaces the mode of
     inference ~ barbara when the minor premise has a general context.
     Proposition 65 of [Frege1879] p. 53.  (Contributed by RP, 17-Apr-2020.)
     (Proof modification is discouraged.) $)
  frege65a $p |- ( ( ( ps -> ch ) /\ ( ta -> et ) )
                   -> ( ( ( ch -> th ) /\ ( et -> ze ) )
                        -> ( if- ( ph , ps , ta )
                             -> if- ( ph , th , ze ) ) ) ) $=
    ( wi wif wa ifpimim frege64a syl frege61a ax-mp ) ABCHZEFHZIZCDHFGHJABEIZAD
    GIHHZHPQJTHRSACFIHTABCEFKABCDEFGALMAPQTNO $.

  $( Swap antecedents of ~ frege65a .  Proposition 66 of [Frege1879] p. 54.
     (Contributed by RP, 17-Apr-2020.)  (Proof modification is discouraged.) $)
  frege66a $p |- ( ( ( ch -> th ) /\ ( et -> ze ) )
                   -> ( ( ( ps -> ch ) /\ ( ta -> et ) )
                        -> ( if- ( ph , ps , ta )
                             -> if- ( ph , th , ze ) ) ) ) $=
    ( wi wa wif frege65a ax-frege8 ax-mp ) BCHEFHIZCDHFGHIZABEJADGJHZHHONPHHABC
    DEFGKNOPLM $.

  $( Lemma for ~ frege68a .  Proposition 67 of [Frege1879] p. 54.  (Contributed
     by RP, 17-Apr-2020.)  (Proof modification is discouraged.) $)
  frege67a $p |- ( ( ( ( ps /\ ch ) <-> th ) -> ( th -> ( ps /\ ch ) ) )
                   -> ( ( ( ps /\ ch ) <-> th )
                        -> ( th -> if- ( ph , ps , ch ) ) ) ) $=
    ( wa wif wi wb ax-frege58a frege7 ax-mp ) BCEZABCFZGLDHZDLGGNDMGGGABCILMNDJ
    K $.

  $( Combination of applying a definition and applying it to a specific
     instance.  Proposition 68 of [Frege1879] p. 54.  (Contributed by RP,
     17-Apr-2020.)  (Proof modification is discouraged.) $)
  frege68a $p |- ( ( ( ps /\ ch ) <-> th )
                   -> ( th -> if- ( ph , ps , ch ) ) ) $=
    ( wa wb wi wif frege57aid frege67a ax-mp ) BCEZDFZDLGGMDABCHGGLDIABCDJK $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  _Begriffsschrift_ Chapter II with equivalence of sets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Justification for ~ ax-frege52c .  (Contributed by RP, 24-Dec-2019.) $)
  axfrege52c $p |- ( A = B -> ( [. A / x ]. ph -> [. B / x ]. ph ) ) $=
    ( wceq wsbc dfsbcq biimpd ) CDEABCFABDFABCDGH $.

  $( One side of ~ dfsbcq .  Part of Axiom 52 of [Frege1879] p. 50.
     (Contributed by RP, 24-Dec-2019.)  (New usage is discouraged.) $)
  ax-frege52c $a |- ( A = B -> ( [. A / x ]. ph -> [. B / x ]. ph ) ) $.

  $( The case when the content of ` x ` is identical with the content of ` y `
     and in which a proposition controlled by an element for which we
     substitute the content of ` x ` is affirmed and the same proposition, this
     time where we substitute the content of ` y ` , is denied does not take
     place.  In ` [ x / z ] ph ` , ` x ` can also occur in other than the
     argument ( ` z ` ) places.  Hence ` x ` may still be contained in
     ` [ y / z ] ph ` .  Part of Axiom 52 of [Frege1879] p. 50.  (Contributed
     by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege52b $p |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) ) $=
    ( weq cv wsbc wsb ax-frege52c sbsbc 3imtr4g ) BCEADBFZGADCFZGADBHADCHADLMIA
    DBJADCJK $.

  $( Lemma for frege102 (via ~ frege92 ).  Proposition 53 of [Frege1879] p. 50.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege53b $p |- ( [ y / x ] ph -> ( y = z -> [ z / x ] ph ) ) $=
    ( weq wsb wi frege52b ax-frege8 ax-mp ) CDEZABCFZABDFZGGLKMGGACDBHKLMIJ $.

  $( Reflexive equality of classes.  Identical to ~ eqid .  Justification for
     ~ ax-frege54c .  (Contributed by RP, 24-Dec-2019.) $)
  axfrege54c $p |- A = A $=
    ( eqid ) AB $.

  $( Reflexive equality of sets (as classes).  Part of Axiom 54 of [Frege1879]
     p. 50.  Identical to ~ eqid .  (Contributed by RP, 24-Dec-2019.)
     (New usage is discouraged.) $)
  ax-frege54c $a |- A = A $.

  $( Reflexive equality of sets.  The content of ` x ` is identical with the
     content of ` x ` .  Part of Axiom 54 of [Frege1879] p. 50.  Slightly
     specialized version of ~ eqid .  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege54b $p |- x = x $=
    ( cv ax-frege54c ) ABC $.

  $( Reflexive equality.  (Contributed by RP, 24-Dec-2019.) $)
  frege54cor1b $p |- [ x / y ] y = x $=
    ( equsb1 ) BAC $.

  ${
    $d y z $.
    $( Necessary deduction regarding substitution of value in equality.
       (Contributed by RP, 24-Dec-2019.) $)
    frege55lem1b $p |- ( ( ph -> [ x / y ] y = z )
                       -> ( ph -> x = z ) ) $=
      ( weq wsb equsb3 biimpi imim2i ) CDECBFZBDEZAJKCBDGHI $.
  $}

  $( Lemma for ~ frege55b .  Core proof of Proposition 55 of [Frege1879] p. 50.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege55lem2b $p |- ( x = y -> [ y / z ] z = x ) $=
    ( weq wsb wi frege54cor1b frege53b ax-mp ) CADZCAEABDJCBEFACGJCABHI $.

  ${
    $d x z $.  $d y z $.
    $( Lemma for ~ frege57b .  Proposition 55 of [Frege1879] p. 50.

       Note that ~ eqtr2 incorporates ~ eqcom which is stronger than this
       proposition which is identical to ~ equcomi .  Is it possible that Frege
       tricked himself into assuming what he was out to prove?  (Contributed by
       RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
    frege55b $p |- ( x = y -> y = x ) $=
      ( vz weq wsb frege55lem2b wi wa wex dfsb1 eqtr2 exlimiv adantl sylbi syl
      cv ) ABDCADZCBEZBADZABCFRCBDZQGZTQHZCIZHSQCBJUCSUAUBSCCPBPAPKLMNO $.
  $}

  $( Lemma for ~ frege57b .  Proposition 56 of [Frege1879] p. 50.  (Contributed
     by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege56b $p |- ( ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) )
                   -> ( y = x -> ( [ x / z ] ph -> [ y / z ] ph ) ) ) $=
    ( weq wi wsb frege55b frege9 ax-mp ) CBEZBCEZFLADBGADCGFZFKMFFCBHKLMIJ $.

  $( Analogue of ~ frege57aid .  Proposition 57 of [Frege1879] p. 51.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege57b $p |- ( x = y -> ( [ y / z ] ph -> [ x / z ] ph ) ) $=
    ( weq wsb wi frege52b frege56b ax-mp ) CBEADCFADBFGZGBCEKGACBDHACBDIJ $.

  $( If ` A. x ph ` is affirmed, ` [ y / x ] ph ` cannot be denied.  Identical
     to ~ stdpc4 .  Justification for ~ ax-frege58b .  (Contributed by RP,
     28-Mar-2020.) $)
  axfrege58b $p |- ( A. x ph -> [ y / x ] ph ) $=
    ( stdpc4 ) ABCD $.

  $( If ` A. x ph ` is affirmed, ` [ y / x ] ph ` cannot be denied.  Identical
     to ~ stdpc4 .  Axiom 58 of [Frege1879] p. 51.  (Contributed by RP,
     28-Mar-2020.)  (New usage is discouraged.) $)
  ax-frege58b $a |- ( A. x ph -> [ y / x ] ph ) $.

  $( If ` A. x ph ` is affirmed, ` ph ` cannot be denied.  Identical to ~ sp .
     See ~ ax-frege58b and ~ frege58c for versions which more closely track the
     original.  Axiom 58 of [Frege1879] p. 51.  (Contributed by RP,
     28-Mar-2020.)  (Proof modification is discouraged.) $)
  frege58bid $p |- ( A. x ph -> ph ) $=
    ( wal wsb ax-frege58b sbid biimpi syl ) ABCABBDZAABBEIAABFGH $.

  $( Lemma for ~ frege59b .  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege58bcor $p |- ( A. x ( ph -> ps ) -> ( [ y / x ] ph
                                             -> [ y / x ] ps ) ) $=
    ( wi wal wsb ax-frege58b sbim sylib ) ABEZCFKCDGACDGBCDGEKCDHABCDIJ $.

  $( A kind of Aristotelian inference.  Namely Felapton or Fesapo.  Proposition
     59 of [Frege1879] p. 51.

     _Note_: in the Bauer-Meenfelberg translation published in van Heijenoort's
     collection _From Frege to Goedel_, this proof has the ~ frege12
     incorrectly referenced where ~ frege30 is in the original.  (Contributed
     by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege59b $p |- ( [ y / x ] ph
                 -> ( -. [ y / x ] ps -> -. A. x ( ph -> ps ) ) ) $=
    ( wi wal wsb wn frege58bcor frege30 ax-mp ) ABECFZACDGZBCDGZEEMNHLHEEABCDIL
    MNJK $.

  $( Swap antecedents of ~ ax-frege58b .  Proposition 60 of [Frege1879] p. 52.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege60b $p |- ( A. x ( ph -> ( ps -> ch ) )
                   -> ( [ y / x ] ps
                        -> ( [ y / x ] ph -> [ y / x ] ch ) ) ) $=
    ( wi wal wsb ax-frege58b sbim imbi2i bitri sylib frege12 ax-mp ) ABCFZFZDGZ
    ADEHZBDEHZCDEHZFZFZFRTSUAFFFRQDEHZUCQDEIUDSPDEHZFUCAPDEJUEUBSBCDEJKLMRSTUAN
    O $.

  $( Lemma for ~ frege65b .  Proposition 61 of [Frege1879] p. 52.  (Contributed
     by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege61b $p |- ( ( [ x / y ] ph -> ps ) -> ( A. y ph -> ps ) ) $=
    ( wal wsb wi ax-frege58b frege9 ax-mp ) ADEZADCFZGLBGKBGGADCHKLBIJ $.

  $( A kind of Aristotelian inference.  This judgement replaces the mode of
     inference ~ barbara when the minor premise has a particular context.
     Proposition 62 of [Frege1879] p. 52.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege62b $p |- ( [ y / x ] ph
                   -> ( A. x ( ph -> ps ) -> [ y / x ] ps ) ) $=
    ( wi wal wsb frege58bcor ax-frege8 ax-mp ) ABECFZACDGZBCDGZEELKMEEABCDHKLMI
    J $.

  $( Lemma for ~ frege91 .  Proposition 63 of [Frege1879] p. 52.  (Contributed
     by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege63b $p |- ( [ y / x ] ph
                 -> ( ps
                      -> ( A. x ( ph -> ch ) -> [ y / x ] ch ) ) ) $=
    ( wsb wi wal frege62b frege24 ax-mp ) ADEFZACGDHCDEFGZGLBMGGACDEILMBJK $.

  $( Lemma for ~ frege65b .  Proposition 64 of [Frege1879] p. 53.  (Contributed
     by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege64b $p |- ( ( [ x / y ] ph -> [ z / y ] ps )
                 -> ( A. y ( ps -> ch )
                      -> ( [ x / y ] ph -> [ z / y ] ch ) ) ) $=
    ( wsb wi wal frege62b frege18 ax-mp ) BEFGZBCHEIZCEFGZHHAEDGZMHNPOHHHBCEFJM
    NOPKL $.

  $( A kind of Aristotelian inference.  This judgement replaces the mode of
     inference ~ barbara when the minor premise has a general context.
     Proposition 65 of [Frege1879] p. 53.

     In Frege care is taken to point out that the variables in the first
     clauses are independent of each other and of the final term so another
     valid translation could be :
     ` |- ( A. x ( [ x / a ] ph -> [ x / b ] ps ) -> ( A. y ( [ y / b ] ps `
     ` -> [ y / c ] ch ) -> ( [ z / a ] ph -> [ z / c ] ch ) ) ) ` .  But that
     is perhaps too pedantic a translation for this exploration.  (Contributed
     by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege65b $p |- ( A. x ( ph -> ps )
                 -> ( A. x ( ps -> ch )
                      -> ( [ y / x ] ph -> [ y / x ] ch ) ) ) $=
    ( wi wsb wal sbim frege64b sylbi frege61b ax-mp ) ABFZDEGZBCFDHADEGZCDEGFFZ
    FNDHQFOPBDEGFQABDEIABCEDEJKNQEDLM $.

  $( Swap antecedents of ~ frege65b .  Proposition 66 of [Frege1879] p. 54.
     (Contributed by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege66b $p |- ( A. x ( ph -> ps )
                 -> ( A. x ( ch -> ph )
                      -> ( [ y / x ] ch -> [ y / x ] ps ) ) ) $=
    ( wi wal wsb frege65b ax-frege8 ax-mp ) CAFDGZABFDGZCDEHBDEHFZFFMLNFFCABDEI
    LMNJK $.

  $( Lemma for ~ frege68b .  Proposition 67 of [Frege1879] p. 54.  (Contributed
     by RP, 24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege67b $p |- ( ( ( A. x ph <-> ps ) -> ( ps -> A. x ph ) )
                   -> ( ( A. x ph <-> ps ) -> ( ps -> [ y / x ] ph ) ) ) $=
    ( wal wsb wi wb ax-frege58b frege7 ax-mp ) ACEZACDFZGLBHZBLGGNBMGGGACDILMNB
    JK $.

  $( Combination of applying a definition and applying it to a specific
     instance.  Proposition 68 of [Frege1879] p. 54.  (Contributed by RP,
     24-Dec-2019.)  (Proof modification is discouraged.) $)
  frege68b $p |- ( ( A. x ph <-> ps ) -> ( ps -> [ y / x ] ph ) ) $=
    ( wal wb wi wsb frege57aid frege67b ax-mp ) ACEZBFZBLGGMBACDHGGLBIABCDJK $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  _Begriffsschrift_ Chapter II with equivalence of classes
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  _Begriffsschrift_ Chapter II with equivalence of classes (where they are
  sets).

$)

  $( Proposition 53 of [Frege1879] p. 50.  (Contributed by RP, 24-Dec-2019.)
     (Proof modification is discouraged.) $)
  frege53c $p |- ( [. A / x ]. ph -> ( A = B -> [. B / x ]. ph ) ) $=
    ( wceq wsbc wi ax-frege52c ax-frege8 ax-mp ) CDEZABCFZABDFZGGLKMGGABCDHKLMI
    J $.

  ${
    $d x A $.
    frege54c.1 $e |- A e. C $.
    $( Reflexive equality.  (Contributed by RP, 24-Dec-2019.)  (Revised by RP,
       25-Apr-2020.) $)
    frege54cor1c $p |- [. A / x ]. x = A $=
      ( cv wceq wsbc cab wcel csn elexi snid df-sn eleqtri df-sbc mpbir ) AEBFZ
      ABGBQAHZIBBJRBBCDKLABMNQABOP $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Necessary deduction regarding substitution of value in equality.
       (Contributed by RP, 24-Dec-2019.) $)
    frege55lem1c $p |- ( ( ph -> [. A / x ]. x = B )
                         -> ( ph -> A = B ) ) $=
      ( cv wceq wsbc cab wcel df-sbc eqeq1 elabg ibi sylbi imim2i ) BEZDFZBCGZC
      DFZARCQBHZIZSQBCJUASQSBCTPCDKLMNO $.
  $}

  ${
    $d x z $.
    $( Core proof of Proposition 55 of [Frege1879] p. 50.  (Contributed by RP,
       24-Dec-2019.)  (Proof modification is discouraged.) $)
    frege55lem2c $p |- ( x = A -> [. A / z ]. z = x ) $=
      ( weq cv wsbc wceq wi cvv vex frege54cor1c frege53c ax-mp ) BADZBAEZFOCGN
      BCFHBOIAJKNBOCLM $.
  $}

  ${
    $d x y $.  $d y A $.
    $( Proposition 55 of [Frege1879] p. 50.  (Contributed by RP, 24-Dec-2019.)
       (Proof modification is discouraged.) $)
    frege55c $p |- ( x = A -> A = x ) $=
      ( vy cv wceq weq wsbc wi cvv vex frege54cor1c frege53c ax-mp wex cab wcel
      wa df-sbc clelab bitri eqtr2 exlimiv sylbi syl ) ADZBEZCAFZCBGZBUEEZUGCUE
      GUFUHHCUEIAJKUGCUEBLMUHCDZBEUGQZCNZUIUHBUGCOPULUGCBRUGCBSTUKUICUJBUEUAUBU
      CUD $.
  $}

  ${
    $d x A $.  $d x B $.
    frege56c.b $e |- B e. C $.
    $( Lemma for ~ frege57c .  Proposition 56 of [Frege1879] p. 50.
       (Contributed by RP, 24-Dec-2019.)
       (Proof modification is discouraged.) $)
    frege56c $p |- ( ( A = B -> ( [. A / x ]. ph -> [. B / x ]. ph ) )
                     -> ( B = A -> ( [. A / x ]. ph -> [. B / x ]. ph ) ) ) $=
      ( wceq wi wsbc cv frege54cor1c frege53c ax-mp frege55lem1c frege9 ) DCGZC
      DGZHZQABCIABDIHZHPSHHPBJDGZBCIHZRTBDIUABDEFKTBDCLMPBCDNMPQSOM $.
  $}

  ${
    $d x A $.  $d x B $.
    frege57c.a $e |- A e. C $.
    $( Swap order of implication in ~ ax-frege52c .  Proposition 57 of
       [Frege1879] p. 51.  (Contributed by RP, 24-Dec-2019.)
       (Proof modification is discouraged.) $)
    frege57c $p |- ( A = B -> ( [. B / x ]. ph -> [. A / x ]. ph ) ) $=
      ( wceq wsbc wi ax-frege52c frege56c ax-mp ) DCGABDHABCHIZICDGMIABDCJABDCE
      FKL $.
  $}

  ${
    $d y ph $.  $d y x $.  $d y A $.
    frege58c.a $e |- A e. B $.
    $( Principle related to ~ sp .  Axiom 58 of [Frege1879] p. 51.
       (Contributed by RP, 24-Dec-2019.)
       (Proof modification is discouraged.) $)
    frege58c $p |- ( A. x ph -> [. A / x ]. ph ) $=
      ( vy wcel wal wsbc wi cv wceq wsb ax-frege58b sbsbc sylib dfsbcq imbitrid
      vtocleg ax-mp ) CDGABHZABCIZJZEUCFCDUAABFKZIZUDCLUBUAABFMUEABFNABFOPABUDC
      QRST $.
  $}

  ${
    frege59c.a $e |- A e. B $.
    $( A kind of Aristotelian inference.  Proposition 59 of [Frege1879] p. 51.

       _Note_: in the Bauer-Meenfelberg translation published in van
       Heijenoort's collection _From Frege to Goedel_, this proof has the
       ~ frege12 incorrectly referenced where ~ frege30 is in the original.
       (Contributed by RP, 24-Dec-2019.)
       (Proof modification is discouraged.) $)
    frege59c $p |- ( [. A / x ]. ph
                   -> ( -. [. A / x ]. ps -> -. A. x ( ph -> ps ) ) ) $=
      ( wi wal wsbc wn frege58c sbcim1 syl frege30 ax-mp ) ABGZCHZACDIZBCDIZGZG
      RSJQJGGQPCDITPCDEFKABCDLMQRSNO $.

    $( Swap antecedents of ~ frege58c .  Proposition 60 of [Frege1879] p. 52.
       (Contributed by RP, 24-Dec-2019.)
       (Proof modification is discouraged.) $)
    frege60c $p |- ( A. x ( ph -> ( ps -> ch ) )
                   -> ( [. A / x ]. ps
                        -> ( [. A / x ]. ph -> [. A / x ]. ch ) ) ) $=
      ( wi wal wsbc frege58c sbcim1 syl6 syl frege12 ax-mp ) ABCHZHZDIZADEJZBDE
      JZCDEJZHZHZHSUATUBHHHSRDEJZUDRDEFGKUETQDEJUCAQDELBCDELMNSTUAUBOP $.

    $( Lemma for ~ frege65c .  Proposition 61 of [Frege1879] p. 52.
       (Contributed by RP, 24-Dec-2019.)
       (Proof modification is discouraged.) $)
    frege61c $p |- ( ( [. A / x ]. ph -> ps ) -> ( A. x ph -> ps ) ) $=
      ( wal wsbc wi frege58c frege9 ax-mp ) ACGZACDHZINBIMBIIACDEFJMNBKL $.

    $( A kind of Aristotelian inference.  This judgement replaces the mode of
       inference ~ barbara when the minor premise has a particular context.
       Proposition 62 of [Frege1879] p. 52.  (Contributed by RP, 24-Dec-2019.)
       (Proof modification is discouraged.) $)
    frege62c $p |- ( [. A / x ]. ph
                   -> ( A. x ( ph -> ps ) -> [. A / x ]. ps ) ) $=
      ( wi wal wsbc frege58c sbcim1 syl ax-frege8 ax-mp ) ABGZCHZACDIZBCDIZGZGQ
      PRGGPOCDISOCDEFJABCDKLPQRMN $.

    $( Analogue of ~ frege63b .  Proposition 63 of [Frege1879] p. 52.
       (Contributed by RP, 24-Dec-2019.)
       (Proof modification is discouraged.) $)
    frege63c $p |- ( [. A / x ]. ph
                   -> ( ps
                        -> ( A. x ( ph -> ch ) -> [. A / x ]. ch ) ) ) $=
      ( wsbc wi wal frege62c frege24 ax-mp ) ADEHZACIDJCDEHIZINBOIIACDEFGKNOBLM
      $.

    $( Lemma for ~ frege65c .  Proposition 64 of [Frege1879] p. 53.
       (Contributed by RP, 24-Dec-2019.)
       (Proof modification is discouraged.) $)
    frege64c $p |- ( ( [. C / x ]. ph -> [. A / x ]. ps )
                   -> ( A. x ( ps -> ch )
                        -> ( [. C / x ]. ph -> [. A / x ]. ch ) ) ) $=
      ( wsbc wi wal frege62c frege18 ax-mp ) BDEIZBCJDKZCDEIZJJADGIZOJPRQJJJBCD
      EFHLOPQRMN $.

    $( A kind of Aristotelian inference.  This judgement replaces the mode of
       inference ~ barbara when the minor premise has a general context.
       Proposition 65 of [Frege1879] p. 53.  (Contributed by RP, 24-Dec-2019.)
       (Proof modification is discouraged.) $)
    frege65c $p |- ( A. x ( ph -> ps )
                   -> ( A. x ( ps -> ch )
                        -> ( [. A / x ]. ph -> [. A / x ]. ch ) ) ) $=
      ( wi wsbc wal sbcim1 frege64c syl frege61c ax-mp ) ABHZDEIZBCHDJADEIZCDEI
      HHZHPDJSHQRBDEIHSABDEKABCDEFEGLMPSDEFGNO $.

    $( Swap antecedents of ~ frege65c .  Proposition 66 of [Frege1879] p. 54.
       (Contributed by RP, 24-Dec-2019.)
       (Proof modification is discouraged.) $)
    frege66c $p |- ( A. x ( ph -> ps )
                 -> ( A. x ( ch -> ph )
                      -> ( [. A / x ]. ch -> [. A / x ]. ps ) ) ) $=
      ( wi wal wsbc frege65c ax-frege8 ax-mp ) CAHDIZABHDIZCDEJBDEJHZHHONPHHCAB
      DEFGKNOPLM $.

    $( Lemma for ~ frege68c .  Proposition 67 of [Frege1879] p. 54.
       (Contributed by RP, 24-Dec-2019.)
       (Proof modification is discouraged.) $)
    frege67c $p |- ( ( ( A. x ph <-> ps ) -> ( ps -> A. x ph ) )
                   -> ( ( A. x ph <-> ps ) -> ( ps -> [. A / x ]. ph ) ) ) $=
      ( wal wsbc wi wb frege58c frege7 ax-mp ) ACGZACDHZINBJZBNIIPBOIIIACDEFKNO
      PBLM $.

    $( Combination of applying a definition and applying it to a specific
       instance.  Proposition 68 of [Frege1879] p. 54.  (Contributed by RP,
       24-Dec-2019.)  (Proof modification is discouraged.) $)
    frege68c $p |- ( ( A. x ph <-> ps ) -> ( ps -> [. A / x ]. ph ) ) $=
      ( wal wb wi wsbc frege57aid frege67c ax-mp ) ACGZBHZBNIIOBACDJIINBKABCDEF
      LM $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  _Begriffsschrift_ Chapter III Properties hereditary in a sequence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

   ` ( R " A ) C_ A ` means membership in ` A ` is hereditary in the
   sequence dictated by relation ` R ` .  This differs from the
   set-theoretic notion that a set is hereditary in a property:
   that all of its elements have a property and all of their elements
   have the property and so-on.

   While the above notation is modern, it is cumbersome in the case
   when ` A ` is complex and to more closely follow Frege, we
   abbreviate it with new notation ` R hereditary A ` .  This greatly
   shortens the statements for ~ frege97 and ~ frege109 .

   ~ dffrege69 through ~ frege75 develop this, but translation to Metamath
   is pending some decisions.

   While Frege does not limit discussion to sets, we may have to
   depart from Frege by limiting ` R ` or ` A ` to sets when we quantify
   over all hereditary relations or all classes where membership
   is hereditary in a sequence dictated by ` R ` .

$)

  ${
    $d x y A $.  $d x y R $.
    $( If from the proposition that ` x ` has property ` A ` it can be inferred
       generally, whatever ` x ` may be, that every result of an application of
       the procedure ` R ` to ` x ` has property ` A ` , then we say " Property
       ` A ` is hereditary in the ` R ` -sequence.  Definition 69 of
       [Frege1879] p. 55.  (Contributed by RP, 28-Mar-2020.) $)
    dffrege69 $p |- ( A. x ( x e. A -> A. y ( x R y -> y e. A ) )
                  <-> R hereditary A ) $=
      ( whe cv wcel wbr wi wal dfhe3 bicomi ) CDEAFZCGMBFZDHNCGIBJIAJABCDKL $.
  $}

  ${
    frege70.x $e |- X e. V $.
    $d x y A $.  $d x y R $.  $d y X $.
    $( Lemma for ~ frege72 .  Proposition 70 of [Frege1879] p. 58.
       (Contributed by RP, 28-Mar-2020.)  (Revised by RP, 3-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege70 $p |- ( R hereditary A
                    -> ( X e. A -> A. y ( X R y -> y e. A ) ) ) $=
      ( vx cv wcel wbr wi wal whe dffrege69 wsbc frege68c sbcel1v sbcim1 ax-mp
      wb biimpri sbcal csb sbcbr1g wceq csbvarg breq1i bitri sbcg 3imtr3g alimi
      sylbi syl56 syl6 ) GHZBIZUOAHZCJZUQBIZKZALZKZGLBCMZTZVCEBIZEUQCJZUSKZALZK
      ZKGABCNVDVCVBGEOZVIVBVCGEDFPVEUPGEOZVJVAGEOZVHVKVEGEBQUAUPVAGERVLUTGEOZAL
      VHUTAGEUBVMVGAVMURGEOZUSGEOZVFUSURUSGERVNGEUOUCZUQCJZVFEDIZVNVQTFGEUOUQCD
      UDSVPEUQCVRVPEUEFGEDUFSUGUHVRVOUSTFUSGEDUISUJUKULUMUNS $.
  $}

  ${
    frege71.x $e |- X e. V $.
    $d z A $.  $d z R $.  $d z X $.
    $( Lemma for ~ frege72 .  Proposition 71 of [Frege1879] p. 59.
       (Contributed by RP, 28-Mar-2020.)  (Revised by RP, 3-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege71 $p |- ( ( A. z ( X R z -> z e. A ) -> ( X R Y -> Y e. A ) )
                  -> ( R hereditary A
                       -> ( X e. A -> ( X R Y -> Y e. A ) ) ) ) $=
      ( whe wcel cv wbr wi wal frege70 frege19 ax-mp ) BCHZEBIZEAJZCKSBILAMZLLT
      EFCKFBILZLQRUALLLABCDEGNQRTUAOP $.
  $}

  ${
    frege72.x $e |- X e. U $.
    frege72.y $e |- Y e. V $.
    $d z A $.  $d z R $.  $d z X $.
    $( If property ` A ` is hereditary in the ` R ` -sequence, if ` x ` has
       property ` A ` , and if ` y ` is a result of an application of the
       procedure ` R ` to ` x ` , then ` y ` has property ` A ` .  Proposition
       72 of [Frege1879] p. 59.  (Contributed by RP, 28-Mar-2020.)  (Revised by
       RP, 5-Jul-2020.)  (Proof modification is discouraged.) $)
    frege72 $p |- ( R hereditary A -> ( X e. A -> ( X R Y -> Y e. A ) ) ) $=
      ( vz cv wbr wcel wi wal whe wsbc frege58c sbcim1 wb ax-mp sbcbr2g csbvarg
      csb breq2d bitrd sbcel1v 3imtr3g syl frege71 ) EIJZBKZUJALZMZINZEFBKZFALZ
      MZMABOEALUQMMUNUMIFPZUQUMIFDHQURUKIFPZULIFPUOUPUKULIFRFDLZUSUOSHUTUSEIFUJ
      UCZBKUOIFEUJBDUAUTVAFEBIFDUBUDUETIFAUFUGUHIABCEFGUIT $.
  $}

  ${
    frege73.x $e |- X e. U $.
    frege73.y $e |- Y e. V $.
    $( Lemma for ~ frege87 .  Proposition 73 of [Frege1879] p. 59.
       (Contributed by RP, 28-Mar-2020.)  (Revised by RP, 5-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege73 $p |- ( ( R hereditary A -> X e. A )
                  -> ( R hereditary A -> ( X R Y -> Y e. A ) ) ) $=
      ( whe wcel wbr wi frege72 ax-frege2 ax-mp ) ABIZEAJZEFBKFAJLZLLPQLPRLLABC
      DEFGHMPQRNO $.
  $}

  ${
    frege74.x $e |- X e. U $.
    frege74.y $e |- Y e. V $.
    $( If ` X ` has a property ` A ` that is hereditary in the ` R ` -sequence,
       then every result of a application of the procedure ` R ` to ` X ` has
       the property ` A ` .  Proposition 74 of [Frege1879] p. 60.  (Contributed
       by RP, 28-Mar-2020.)  (Revised by RP, 5-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege74 $p |- ( X e. A -> ( R hereditary A -> ( X R Y -> Y e. A ) ) ) $=
      ( whe wcel wbr wi frege72 ax-frege8 ax-mp ) ABIZEAJZEFBKFAJLZLLQPRLLABCDE
      FGHMPQRNO $.
  $}

  ${
    $d x y A $.  $d x y R $.
    $( If from the proposition that ` x ` has property ` A ` , whatever ` x `
       may be, it can be inferred that every result of an application of the
       procedure ` R ` to ` x ` has property ` A ` , then property ` A ` is
       hereditary in the ` R ` -sequence.  Proposition 75 of [Frege1879] p. 60.
       (Contributed by RP, 28-Mar-2020.)
       (Proof modification is discouraged.) $)
    frege75 $p |- ( A. x ( x e. A -> A. y ( x R y -> y e. A ) )
                  -> R hereditary A ) $=
      ( cv wcel wbr wi wal whe wb dffrege69 frege52aid ax-mp ) AEZCFOBEZDGPCFHB
      IHAIZCDJZKQRHABCDLQRMN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  _Begriffsschrift_ Chapter III Following in a sequence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  ` p ( t+ `` R ) c ` means ` c ` follows ` p ` in the ` R ` -sequence.

  ~ dffrege76 through ~ frege98 develop this.

  This will be shown to be the transitive closure of the relation ` R ` .  But
  more work needs to be done on transitive closure of relations before this is
  ready for Metamath.

$)

  ${
    frege76.b $e |- B e. U $.
    frege76.e $e |- E e. V $.
    frege76.r $e |- R e. W $.
    ${
      $d a f B $.  $d f E $.  $d a f R $.  $d f U $.  $d f V $.  $d f W $.
      $( If from the two propositions that every result of an application of
         the procedure ` R ` to ` B ` has property ` f ` and that property
         ` f ` is hereditary in the ` R ` -sequence, it can be inferred,
         whatever ` f ` may be, that ` E ` has property ` f ` , then we say
         ` E ` follows ` B ` in the ` R ` -sequence.  Definition 76 of
         [Frege1879] p. 60.

         Each of ` B ` , ` E ` and ` R ` must be sets.  (Contributed by RP,
         2-Jul-2020.) $)
      dffrege76 $p |- ( A. f ( R hereditary f
                      -> ( A. a ( B R a -> a e. f ) -> E e. f ) )
                      <-> B ( t+ ` R ) E ) $=
        ( wbr cv cun cima wss wcel wi wal bitri ctcl cfv csn cab cint brtrclfv2
        whe wb mp3an elexi elintab wa imaundi equncomi sseq1i unss bitr4i df-he
        wel bicomi df-ss cop elimasn df-br imbi1i albii anbi12i impexp 3bitrri
        vex ) AEBUAUBLZEBAUCZDMZNOZVMPZDUDUEQZVOEVMQZRZDSVMBUGZAHMZBLZHDUSZRZHS
        ZVQRRZDSACQEFQBGQVKVPUHIJKBCDFGAEUFUIVODEEFJUJUKVRWEDVRVSWDULZVQRWEVOWF
        VQVOBVMOZVMPZBVLOZVMPZULZWFVOWGWINZVMPWKVNWLVMVNWIWGBVLVMUMUNUOWGWIVMUP
        UQWHVSWJWDVSWHVMBURUTWJVTWIQZWBRZHSWDHWIVMVAWNWCHWMWAWBWMAVTVBBQWABAVTA
        CIUJHVJVCAVTBVDUQVEVFTVGTVEVSWDVQVHTVFVI $.
    $}
  $}

  ${
    frege77.x $e |- X e. U $.
    frege77.y $e |- Y e. V $.
    frege77.r $e |- R e. W $.
    frege77.a $e |- A e. B $.
    ${
      $d a A $.  $d a f R $.  $d f U $.  $d f V $.  $d f W $.  $d a f X $.
      $d f Y $.
      $( If ` Y ` follows ` X ` in the ` R ` -sequence, if property ` A ` is
         hereditary in the ` R ` -sequence, and if every result of an
         application of the procedure ` R ` to ` X ` has the property ` A ` ,
         then ` Y ` has property ` A ` .  Proposition 77 of [Frege1879] p. 62.
         (Contributed by RP, 29-Jun-2020.)  (Revised by RP, 2-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege77 $p |- ( X ( t+ ` R ) Y -> ( R hereditary A
                        -> ( A. a ( X R a -> a e. A ) -> Y e. A ) ) ) $=
        ( vf wi wal wb wsbc ax-mp bitri cv whe wbr wcel ctcl dffrege76 frege68c
        wel cfv sbcimg csb sbcheg csbconstg csbvarg heeq12 mp2an sbcal sbcel2gv
        wceq sbcg imbi12i albii imbitrdi ) NUAZCUBZGIUAZCUCZINUHZOZIPZHVDUDZOZO
        ZNPGHCUEUIUCZQZVNACUBZVGVFAUDZOZIPZHAUDZOZOZOGCDNHEFIJKLUFVOVNVMNARZWBV
        MVNNABMUGWCVENARZVLNARZOZWBABUDZWCWFQMVEVLNABUJSWDVPWEWAWDNAVDUKZNACUKZ
        UBZVPWGWDWJQMNACVDBULSWICUSZWHAUSZWJVPQWGWKMNACBUMSWGWLMNABUNSWHAWICUOU
        PTWEVJNARZVKNARZOZWAWGWEWOQMVJVKNABUJSWMVSWNVTWMVINARZIPVSVIINAUQWPVRIW
        PVGNARZVHNARZOZVRWGWPWSQMVGVHNABUJSWQVGWRVQWGWQVGQMVGNABUTSWGWRVQQMNVFA
        BURSVATVBTWGWNVTQMNHABURSVATVATVCS $.
    $}
  $}

  ${
    frege78.x $e |- X e. U $.
    frege78.y $e |- Y e. V $.
    frege78.r $e |- R e. W $.
    frege78.a $e |- A e. B $.
    ${
      $d a A $.  $d a R $.  $d a X $.
      $( Commuted form of ~ frege77 .  Proposition 78 of [Frege1879] p. 63.
         (Contributed by RP, 1-Jul-2020.)  (Revised by RP, 2-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege78 $p |- ( R hereditary A -> ( A. a ( X R a -> a e. A )
                                      -> ( X ( t+ ` R ) Y -> Y e. A ) ) ) $=
        ( ctcl cfv wbr whe cv wcel wi wal frege77 frege17 ax-mp ) GHCNOPZACQZGI
        RZCPUGASTIUAZHASZTTTUFUHUEUITTTABCDEFGHIJKLMUBUEUFUHUIUCUD $.
    $}
  $}

  ${
    frege79.x $e |- X e. U $.
    frege79.y $e |- Y e. V $.
    frege79.r $e |- R e. W $.
    frege79.a $e |- A e. B $.
    ${
      $d a A $.  $d a R $.  $d a X $.
      $( Distributed form of ~ frege78 .  Proposition 79 of [Frege1879] p. 63.
         (Contributed by RP, 1-Jul-2020.)  (Revised by RP, 3-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege79 $p |- ( ( R hereditary A -> A. a ( X R a -> a e. A ) )
                  -> ( R hereditary A -> ( X ( t+ ` R ) Y -> Y e. A ) ) ) $=
        ( whe cv wbr wcel wi wal ctcl cfv frege78 ax-frege2 ax-mp ) ACNZGIOZCPU
        FAQRISZGHCTUAPHAQRZRRUEUGRUEUHRRABCDEFGHIJKLMUBUEUGUHUCUD $.
    $}
  $}

  ${
    frege80.x $e |- X e. U $.
    frege80.y $e |- Y e. V $.
    frege80.r $e |- R e. W $.
    frege80.a $e |- A e. B $.
    ${
      $d a A $.  $d a R $.  $d a X $.
      $( Add additional condition to both clauses of ~ frege79 .  Proposition
         80 of [Frege1879] p. 63.  (Contributed by RP, 1-Jul-2020.)  (Revised
         by RP, 5-Jul-2020.)  (Proof modification is discouraged.) $)
      frege80 $p |- ( ( X e. A -> ( R hereditary A
                          -> A. a ( X R a -> a e. A ) ) )
                     -> ( X e. A -> ( R hereditary A
                          -> ( X ( t+ ` R ) Y -> Y e. A ) ) ) ) $=
        ( whe cv wbr wcel wi wal ctcl cfv frege79 frege5 ax-mp ) ACNZGIOZCPUFAQ
        RISRZUEGHCTUAPHAQRRZRGAQZUGRUIUHRRABCDEFGHIJKLMUBUGUHUIUCUD $.
    $}
  $}

  ${
    frege81.x $e |- X e. U $.
    frege81.y $e |- Y e. V $.
    frege81.r $e |- R e. W $.
    frege81.a $e |- A e. B $.
    ${
      $d a A $.  $d a R $.  $d a X $.
      $( If ` X ` has a property ` A ` that is hereditary in the ` R `
         -sequence, and if ` Y ` follows ` X ` in the ` R ` -sequence, then
         ` Y ` has property ` A ` .  This is a form of induction attributed to
         Jakob Bernoulli.  Proposition 81 of [Frege1879] p. 63.  (Contributed
         by RP, 1-Jul-2020.)  (Revised by RP, 5-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege81 $p |- ( X e. A -> ( R hereditary A -> ( X ( t+ ` R ) Y
                        -> Y e. A ) ) ) $=
        ( va wcel whe cv wbr wi wal ctcl cfv cvv frege74 alrimdv frege80 ax-mp
        vex ) GANZACOZGMPZCQUJANRZMSRRUHUIGHCTUAQHANRRRUHUIUKMACDUBGUJIMUGUCUDA
        BCDEFGHMIJKLUEUF $.
    $}
  $}

  ${
    frege82.x $e |- X e. U $.
    frege82.y $e |- Y e. V $.
    frege82.r $e |- R e. W $.
    frege82.a $e |- A e. B $.
    $( Closed-form deduction based on ~ frege81 .  Proposition 82 of
       [Frege1879] p. 64.  (Contributed by RP, 1-Jul-2020.)  (Revised by RP,
       5-Jul-2020.)  (Proof modification is discouraged.) $)
    frege82 $p |- ( ( ph -> X e. A ) -> ( R hereditary A
                     -> ( ph -> ( X ( t+ ` R ) Y -> Y e. A ) ) ) ) $=
      ( wcel whe ctcl cfv wbr wi frege81 frege18 ax-mp ) HBNZBDOZHIDPQRIBNSZSSA
      UCSUDAUESSSBCDEFGHIJKLMTUCUDUEAUAUB $.
  $}

  ${
    frege83.x $e |- X e. S $.
    frege83.y $e |- Y e. T $.
    frege83.r $e |- R e. U $.
    frege83.b $e |- B e. V $.
    frege83.c $e |- C e. W $.
    $( Apply commuted form of ~ frege81 when the property ` R ` is hereditary
       in a disjunction of two properties, only one of which is known to be
       held by ` X ` .  Proposition 83 of [Frege1879] p. 65.  Here we introduce
       the union of classes where Frege has a disjunction of properties which
       are represented by membership in either of the classes.  (Contributed by
       RP, 1-Jul-2020.)  (Revised by RP, 5-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege83 $p |- ( R hereditary ( B u. C ) -> ( X e. B
                        -> ( X ( t+ ` R ) Y -> Y e. ( B u. C ) ) ) ) $=
      ( wcel cun wi whe elexi ctcl cfv wbr wn frege36 wo df-or bitri sylibr cvv
      elun unex frege82 ax-mp ) IAPZIABQZPZRUPCSUOIJCUAUBUCJUPPRRRUOUOUDIBPZRZU
      QUOURUEUQUOURUFUSIABUKUOURUGUHUIUOUPUJCDEFIJKLMABAGNTBHOTULUMUN $.
  $}

  ${
    frege84.x $e |- X e. U $.
    frege84.y $e |- Y e. V $.
    frege84.r $e |- R e. W $.
    frege84.a $e |- A e. B $.
    $( Commuted form of ~ frege81 .  Proposition 84 of [Frege1879] p. 65.
       (Contributed by RP, 1-Jul-2020.)  (Revised by RP, 5-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege84 $p |- ( R hereditary A -> ( X e. A -> ( X ( t+ ` R ) Y
                        -> Y e. A ) ) ) $=
      ( wcel whe ctcl cfv wbr wi frege81 ax-frege8 ax-mp ) GAMZACNZGHCOPQHAMRZR
      RUCUBUDRRABCDEFGHIJKLSUBUCUDTUA $.

    ${
      $d z A $.  $d z R $.  $d z X $.
      $( Commuted form of ~ frege77 .  Proposition 85 of [Frege1879] p. 66.
         (Contributed by RP, 1-Jul-2020.)  (Revised by RP, 5-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege85 $p |- ( X ( t+ ` R ) Y -> ( A. z ( X R z -> z e. A )
                        -> ( R hereditary A -> Y e. A ) ) ) $=
        ( ctcl cfv wbr whe cv wcel wi wal frege77 frege12 ax-mp ) HIDNOPZBDQZHA
        RZDPUGBSTAUAZIBSZTTTUEUHUFUITTTBCDEFGHIAJKLMUBUEUFUHUIUCUD $.
    $}
  $}

  ${
    frege86.x $e |- X e. U $.
    frege86.y $e |- Y e. V $.
    frege86.r $e |- R e. W $.
    frege86.a $e |- A e. B $.

    ${
      $d w A $.  $d w R $.  $d w X $.
      $( Conclusion about element one past ` Y ` in the ` R ` -sequence.
         Proposition 86 of [Frege1879] p. 66.  (Contributed by RP, 1-Jul-2020.)
         (Revised by RP, 7-Jul-2020.)  (Proof modification is discouraged.) $)
      frege86 $p |- ( ( ( R hereditary A -> Y e. A )
                      -> ( R hereditary A -> ( Y R Z -> Z e. A ) ) )
                    -> ( X ( t+ ` R ) Y -> ( A. w ( X R w -> w e. A )
                                    -> ( R hereditary A
                                         -> ( Y R Z -> Z e. A ) ) ) ) ) $=
        ( ctcl cfv wbr cv wcel wi wal whe frege85 frege19 ax-mp ) HIDOPQZHARZDQ
        UGBSTAUAZBDUBZIBSTZTTUJUIIJDQJBSTTZTUFUHUKTTTABCDEFGHIKLMNUCUFUHUJUKUDU
        E $.
    $}
  $}

  ${
    frege87.x $e |- X e. U $.
    frege87.y $e |- Y e. V $.
    frege87.z $e |- Z e. W $.
    frege87.r $e |- R e. S $.
    frege87.a $e |- A e. B $.
    ${
      $d w A $.  $d w R $.  $d w X $.
      $( If ` Z ` is a result of an application of the procedure ` R ` to an
         object ` Y ` that follows ` X ` in the ` R ` -sequence and if every
         result of an application of the procedure ` R ` to ` X ` has a
         property ` A ` that is hereditary in the ` R ` -sequence, then ` Z `
         has property ` A ` .  Proposition 87 of [Frege1879] p. 66.
         (Contributed by RP, 1-Jul-2020.)  (Revised by RP, 7-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege87 $p |- ( X ( t+ ` R ) Y -> ( A. w ( X R w -> w e. A )
                        -> ( R hereditary A -> ( Y R Z -> Z e. A ) ) ) ) $=
        ( whe wcel wi wbr ctcl cfv cv wal frege73 frege86 ax-mp ) BDQZJBRSUHJKD
        TKBRSSZSIJDUAUBTIAUCZDTUJBRSAUDUISSBDGHJKMNUEABCDFGEIJKLMOPUFUG $.
    $}

    ${
      $d w A $.  $d w R $.  $d w X $.
      $( Commuted form of ~ frege87 .  Proposition 88 of [Frege1879] p. 67.
         (Contributed by RP, 1-Jul-2020.)  (Revised by RP, 7-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege88 $p |- ( Y R Z -> ( X ( t+ ` R ) Y
                        -> ( A. w ( X R w -> w e. A ) -> ( R hereditary A
                             -> Z e. A ) ) ) ) $=
        ( ctcl wbr wcel wi cfv cv wal whe frege87 frege15 ax-mp ) IJDQUARZIAUBZ
        DRUIBSTAUCZBDUDZJKDRZKBSZTTTTULUHUJUKUMTTTTABCDEFGHIJKLMNOPUEUHUJUKULUM
        UFUG $.
    $}
  $}

  ${
    frege89.x $e |- X e. U $.
    frege89.y $e |- Y e. V $.
    frege89.r $e |- R e. W $.
    ${
      $d f w R $.  $d f U $.  $d f V $.  $d f W $.  $d f w X $.  $d f Y $.
      $( One direction of ~ dffrege76 .  Proposition 89 of [Frege1879] p. 68.
         (Contributed by RP, 1-Jul-2020.)  (Revised by RP, 2-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege89 $p |- ( A. f ( R hereditary f -> ( A. w ( X R w -> w e. f )
                      -> Y e. f ) ) -> X ( t+ ` R ) Y ) $=
        ( cv whe wbr wel wi wal wcel ctcl cfv wb dffrege76 frege52aid ax-mp ) D
        LZBMGALBNADOPAQHUERPPDQZGHBSTNZUAUFUGPGBCDHEFAIJKUBUFUGUCUD $.
    $}
  $}

  ${
    frege90.x $e |- X e. U $.
    frege90.y $e |- Y e. V $.
    frege90.r $e |- R e. W $.
    ${
      $d f w R $.  $d f U $.  $d f V $.  $d f W $.  $d f w X $.  $d f Y $.
      $( Add antecedent to ~ frege89 .  Proposition 90 of [Frege1879] p. 68.
         (Contributed by RP, 1-Jul-2020.)  (Revised by RP, 2-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege90 $p |- ( ( ph -> A. f ( R hereditary f
                        -> ( A. w ( X R w -> w e. f ) -> Y e. f ) ) )
                      -> ( ph -> X ( t+ ` R ) Y ) ) $=
        ( cv whe wbr wel wi wal wcel ctcl cfv frege89 frege5 ax-mp ) EMZCNHBMCO
        BEPQBRIUESQQERZHICTUAOZQAUFQAUGQQBCDEFGHIJKLUBUFUGAUCUD $.
    $}
  $}

  ${
    frege91.x $e |- X e. U $.
    frege91.y $e |- Y e. V $.
    frege91.r $e |- R e. W $.

    ${
      $d a f R $.  $d f U $.  $d f V $.  $d f W $.  $d a f X $.  $d f Y $.
      $( Every result of an application of a procedure ` R ` to an object ` X `
         follows that ` X ` in the ` R ` -sequence.  Proposition 91 of
         [Frege1879] p. 68.  (Contributed by RP, 2-Jul-2020.)  (Revised by RP,
         5-Jul-2020.)  (Proof modification is discouraged.) $)
      frege91 $p |- ( X R Y -> X ( t+ ` R ) Y ) $=
        ( vf va wbr cv whe wi wal wcel wsbc ax-mp imbi2i wel cfv wb csb sbcbr2g
        ctcl frege63c csbvarg breq2d bitrd sbcel1v 3imtr3i alrimiv frege90 ) EF
        ALZJMZANZEKMZALZKJUAZOKPZFUPQZOZOZJPOUOEFAUFUBLOUOVDJUSKFRZUQVAUTKFRZOZ
        OUOVDUSUQUTKFCHUGFCQZVEUOUCHVHVEEKFURUDZALUOKFEURACUEVHVIFEAKFCUHUIUJSV
        GVCUQVFVBVAKFUPUKTTULUMUOKABJCDEFGHIUNS $.
    $}

    ${
      $d w R $.  $d w Y $.
      $( Inference from ~ frege91 .  Proposition 92 of [Frege1879] p. 69.
         (Contributed by RP, 2-Jul-2020.)  (Revised by RP, 5-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege92 $p |- ( X = Z -> ( X R Y -> Z ( t+ ` R ) Y ) ) $=
        ( vw wcel wceq wbr wi wsbc syl wb csb sbcbr1g cv ctcl cfv cvv vex sbcth
        frege91 frege53c sbcim1 imim2i dfsbcq csbvarg bitrd ax-mp bitr3di eqcom
        breq1d biimpi eqeltrdi imbi12d mpbidi mp2b ) EBLZEGMZKUAZFANZVEFAUBUCZN
        ZOZKGPZOZVDEFANZGFVGNZOZOHVCVIKEPVKVIKEBAUDCDVEFKUEIJUGUFVIKEGUHQVDVFKG
        PZVHKGPZOZVNVKVJVQVDVFVHKGUIUJVDVOVLVPVMVDVFKEPZVOVLVFKEGUKVCVRVLRHVCVR
        KEVESZFANVLKEVEFABTVCVSEFAKEBULUQUMUNUOVDGBLZVPVMRVDGEBVDGEMEGUPURHUSVT
        VPKGVESZFVGNVMKGVEFVGBTVTWAGFVGKGBULUQUMQUTVAVB $.
    $}

    ${
      $d f z R $.  $d f U $.  $d f V $.  $d f W $.  $d f z X $.  $d f Y $.
      $( Necessary condition for two elements to be related by the transitive
         closure.  Proposition 93 of [Frege1879] p. 70.  (Contributed by RP,
         2-Jul-2020.)  (Revised by RP, 5-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege93 $p |- ( A. f ( A. z ( X R z -> z e. f )
                             -> ( R hereditary f -> Y e. f ) )
                      -> X ( t+ ` R ) Y ) $=
        ( cv wbr wel wi wal whe wcel wsbc sbcid ctcl cfv cvv vex frege60c axc4i
        imbi12i 3imtr3g frege90 ax-mp ) GALBMADNOAPZDLZBQZHULRZOOZDPZUMUKUNOZOZ
        DPOUPGHBUAUBMOUOURDUPUMDULSUKDULSZUNDULSZOUMUQUKUMUNDULUCDUDUEUMDTUSUKU
        TUNUKDTUNDTUGUHUFUPABCDEFGHIJKUIUJ $.
    $}
  $}

  ${
    frege94.x $e |- X e. U $.
    frege94.z $e |- Z e. V $.
    frege94.r $e |- R e. W $.
    ${
      $d f w R $.  $d f U $.  $d f V $.  $d f W $.  $d f w X $.  $d f Z $.
      $( Looking one past a pair related by transitive closure of a relation.
         Proposition 94 of [Frege1879] p. 70.  (Contributed by RP, 2-Jul-2020.)
         (Revised by RP, 5-Jul-2020.)  (Proof modification is discouraged.) $)
      frege94 $p |- ( ( Y R Z
                      -> ( X ( t+ ` R ) Y
                           -> A. f ( A. w ( X R w -> w e. f )
                                     -> ( R hereditary f -> Z e. f ) ) ) )
                    -> ( Y R Z -> ( X ( t+ ` R ) Y -> X ( t+ ` R ) Z ) ) ) $=
        ( cv wbr wel wi wal whe wcel ctcl cfv frege93 frege7 ax-mp ) GAMBNADOPA
        QDMZBRIUESPPDQZGIBTUAZNZPHIBNZGHUGNZUFPPUIUJUHPPPABCDEFGIJKLUBUFUHUIUJU
        CUD $.
    $}
  $}

  ${
    frege95.x $e |- X e. U $.
    frege95.y $e |- Y e. V $.
    frege95.z $e |- Z e. W $.
    frege95.r $e |- R e. A $.
    ${
      $d f A $.  $d f w R $.  $d f U $.  $d f W $.  $d f w X $.  $d f Y $.
      $d f Z $.
      $( Looking one past a pair related by transitive closure of a relation.
         Proposition 95 of [Frege1879] p. 70.  (Contributed by RP, 2-Jul-2020.)
         (Revised by RP, 7-Jul-2020.)  (Proof modification is discouraged.) $)
      frege95 $p |- ( Y R Z -> ( X ( t+ ` R ) Y -> X ( t+ ` R ) Z ) ) $=
        ( vw vf wbr ctcl cfv cv wi wal wel whe wcel cvv frege88 alrimdv frege94
        vex ax-mp ) GHBOZFGBPQZOZFMRBOMNUASMTNRZBUBHUMUCSSZNTSSUJULFHUKOSSUJULU
        NNMUMUDBACDEFGHIJKLNUHUEUFMBCNEAFGHIKLUGUI $.
    $}

    $( Every result of an application of the procedure ` R ` to an object that
       follows ` X ` in the ` R ` -sequence follows ` X ` in the ` R `
       -sequence.  Proposition 96 of [Frege1879] p. 71.  (Contributed by RP,
       2-Jul-2020.)  (Revised by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege96 $p |- ( X ( t+ ` R ) Y -> ( Y R Z -> X ( t+ ` R ) Z ) ) $=
      ( wbr ctcl cfv wi frege95 ax-frege8 ax-mp ) GHBMZFGBNOZMZFHUAMZPPUBTUCPPA
      BCDEFGHIJKLQTUBUCRS $.
  $}

  ${
    frege97.x $e |- X e. U $.
    frege97.r $e |- R e. W $.
    ${
      $d a b R $.  $d a b X $.
      $( The property of following ` X ` in the ` R ` -sequence is hereditary
         in the ` R ` -sequence.  Proposition 97 of [Frege1879] p. 71.

         Here we introduce the image of a singleton under a relation as class
         which stands for the property of following ` X ` in the ` R `
         -sequence.  (Contributed by RP, 2-Jul-2020.)  (Revised by RP,
         7-Jul-2020.)  (Proof modification is discouraged.) $)
      frege97 $p |- R hereditary ( ( t+ ` R ) " { X } ) $=
        ( vb va cv ctcl cfv wcel wbr wi cvv vex cop df-br elimasn bitr4i imbi2i
        csn cima wal whe frege75 frege96 elexi 3imtr3i alrimiv mpg ) GIZAJKZDUB
        UCZLZULHIZAMZUPUNLZNZHUDNUNAUEGGHUNAUFUOUSHDULUMMZUQDUPUMMZNUOUSCABOODU
        LUPEGPZHPZFUGUTDULQUMLUODULUMRUMDULDBEUHZVBSTVAURUQVADUPQUMLURDUPUMRUMD
        UPVDVCSTUAUIUJUK $.
    $}
  $}

  ${
    frege98.x $e |- X e. A $.
    frege98.y $e |- Y e. B $.
    frege98.z $e |- Z e. C $.
    frege98.r $e |- R e. D $.
    $( If ` Y ` follows ` X ` and ` Z ` follows ` Y ` in the ` R ` -sequence
       then ` Z ` follows ` X ` in the ` R ` -sequence because the transitive
       closure of a relation has the transitive property.  Proposition 98 of
       [Frege1879] p. 71.  (Contributed by RP, 2-Jul-2020.)  (Revised by RP,
       6-Jul-2020.)  (Proof modification is discouraged.) $)
    frege98 $p |- ( X ( t+ ` R ) Y
                      -> ( Y ( t+ ` R ) Z -> X ( t+ ` R ) Z ) ) $=
      ( ctcl wcel wbr wi cvv ax-mp cop elexi cfv csn whe frege97 imaexg frege84
      cima fvex elimasn df-br bitr4i imbi2i 3imtr3i ) GEMUAZFUBZUGZNZGHUNOZHUPN
      ZPZFGUNOZURFHUNOZPUPEUCUQUTPEADFILUDUPQEBCDGHJKLUNQNUPQNEMUHUNUOQUERUFRUQ
      FGSUNNVAUNFGFAITZGBJTUIFGUNUJUKUSVBURUSFHSUNNVBUNFHVCHCKTUIFHUNUJUKULUM
      $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  _Begriffsschrift_ Chapter III Member of sequence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

    ` p ( ( t+ `` R ) u. _I ) c ` means ` c ` is a member of the ` R `
    -sequence beginning with ` p ` and ` p ` is a member of the  ` R `
    -sequence ending with ` c ` .

    ~ dffrege99 through ~ frege114 develop this.

    This will be shown to be related to the transitive-reflexive
    closure of relation ` R ` .  But more work needs to be done on
    transitive closure of relations before this is ready for
    Metamath.

$)

  ${
    frege99.z $e |- Z e. U $.
    $( If ` Z ` is identical with ` X ` or follows ` X ` in the ` R `
       -sequence, then we say :  " ` Z ` belongs to the ` R ` -sequence
       beginning with ` X ` " or " ` X ` belongs to the ` R ` -sequence ending
       with ` Z ` ".  Definition 99 of [Frege1879] p. 71.  (Contributed by RP,
       2-Jul-2020.) $)
    dffrege99 $p |- ( ( -. X ( t+ ` R ) Z -> Z = X )
                     <-> X ( ( t+ ` R ) u. _I ) Z ) $=
      ( ctcl cfv cid cun wbr wo wn wi wceq brun df-or elexi ideq eqcom bitri
      imbi2i 3bitrri ) CDAFGZHIJCDUCJZCDHJZKUDLZUEMUFDCNZMCDUCHOUDUEPUEUGUFUECD
      NUGCDDBEQRCDSTUAUB $.

    $( One direction of ~ dffrege99 .  Proposition 100 of [Frege1879] p. 72.
       (Contributed by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege100 $p |- ( X ( ( t+ ` R ) u. _I ) Z
                     -> ( -. X ( t+ ` R ) Z -> Z = X ) ) $=
      ( ctcl cfv wbr wn wceq wi cid cun wb dffrege99 frege57aid ax-mp ) CDAFGZH
      IDCJKZCDRLMHZNTSKABCDEOSTPQ $.

    $( Lemma for ~ frege102 .  Proposition 101 of [Frege1879] p. 72.
       (Contributed by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege101 $p |- ( ( Z = X -> ( Z R V -> X ( t+ ` R ) V ) )
           -> ( ( X ( t+ ` R ) Z -> ( Z R V -> X ( t+ ` R ) V ) )
           -> ( X ( ( t+ ` R ) u. _I ) Z
           -> ( Z R V -> X ( t+ ` R ) V ) ) ) ) $=
      ( ctcl cfv cid cun wbr wn wceq wi frege100 frege48 ax-mp ) DEAGHZIJKZDERK
      ZLEDMZNNUAECAKDCRKNZNTUBNSUBNNNABDEFOSTUAUBPQ $.
  $}

  ${
    frege102.x $e |- X e. A $.
    frege102.z $e |- Z e. B $.
    frege102.v $e |- V e. C $.
    frege102.r $e |- R e. D $.
    $( If ` Z ` belongs to the ` R ` -sequence beginning with ` X ` , then
       every result of an application of the procedure ` R ` to ` Z ` follows
       ` X ` in the ` R ` -sequence.  Proposition 102 of [Frege1879] p. 72.
       (Contributed by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege102 $p |- ( X ( ( t+ ` R ) u. _I ) Z
                     -> ( Z R V -> X ( t+ ` R ) V ) ) $=
      ( wceq wbr ctcl cfv wi cid cun frege92 frege96 frege101 mp2 ) HGMHFENGFEO
      PZNQZQGHUDNUEQGHUDRSNUEQEBCDHFGJKLTDEABCGHFIJKLUAEBFGHJUBUC $.
  $}

  ${
    frege103.z $e |- Z e. V $.
    $( Proposition 103 of [Frege1879] p. 73.  (Contributed by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege103 $p |- ( ( Z = X -> X = Z )
                     -> ( X ( ( t+ ` R ) u. _I ) Z -> ( -. X ( t+ ` R ) Z
                          -> X = Z ) ) ) $=
      ( ctcl cfv cid cun wbr wn wceq wi frege100 frege19 ax-mp ) CDAFGZHIJZCDQJ
      KZDCLZMMTCDLZMRSUAMMMABCDENRSTUAOP $.

    ${
      $d z X $.  $d z Z $.
      $( Proposition 104 of [Frege1879] p. 73.

         _Note_: in the Bauer-Meenfelberg translation published in van
         Heijenoort's collection _From Frege to Goedel_, this proof has the
         minor clause and result swapped.  (Contributed by RP, 7-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege104 $p |- ( X ( ( t+ ` R ) u. _I ) Z
                     -> ( -. X ( t+ ` R ) Z -> X = Z ) ) $=
        ( vz wceq wi ctcl cfv cid cun wbr wn elexi eqeq1 eqeq2 imbi12d frege55c
        cv vtocl frege103 ax-mp ) DCGZCDGZHZCDAIJZKLMCDUGMNUEHHFTZCGZCUHGZHUFFD
        DBEOUHDGUIUDUJUEUHDCPUHDCQRFCSUAABCDEUBUC $.
    $}

    $( Proposition 105 of [Frege1879] p. 73.  (Contributed by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege105 $p |- ( ( -. X ( t+ ` R ) Z -> Z = X )
                     -> X ( ( t+ ` R ) u. _I ) Z ) $=
      ( ctcl cfv wbr wn wceq wi cid cun wb dffrege99 frege52aid ax-mp ) CDAFGZH
      IDCJKZCDRLMHZNSTKABCDEOSTPQ $.

    $( Whatever follows ` X ` in the ` R ` -sequence belongs to the ` R `
       -sequence beginning with ` X ` .  Proposition 106 of [Frege1879] p. 73.
       (Contributed by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege106 $p |- ( X ( t+ ` R ) Z -> X ( ( t+ ` R ) u. _I ) Z ) $=
      ( ctcl cfv wbr wn wceq wi cid cun frege105 frege37 ax-mp ) CDAFGZHZIDCJZK
      CDQLMHZKRTKABCDENRSTOP $.
  $}

  ${
    frege107.v $e |- V e. A $.
    $( Proposition 107 of [Frege1879] p. 74.  (Contributed by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege107 $p |- ( ( Z ( ( t+ ` R ) u. _I ) Y
                       -> ( Y R V -> Z ( t+ ` R ) V ) )
                     -> ( Z ( ( t+ ` R ) u. _I ) Y
                          -> ( Y R V -> Z ( ( t+ ` R ) u. _I ) V ) ) ) $=
      ( ctcl cfv wbr cid cun wi frege106 frege7 ax-mp ) ECBGHZIZECPJKZIZLEDRIZD
      CBIZQLLTUASLLLBAECFMQSTUANO $.
  $}

  ${
    frege108.z $e |- Z e. A $.
    frege108.y $e |- Y e. B $.
    frege108.v $e |- V e. C $.
    frege108.r $e |- R e. D $.
    $( If ` Y ` belongs to the ` R ` -sequence beginning with ` Z ` , then
       every result of an application of the procedure ` R ` to ` Y ` belongs
       to the ` R ` -sequence beginning with ` Z ` .  Proposition 108 of
       [Frege1879] p. 74.  (Contributed by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege108 $p |- ( Z ( ( t+ ` R ) u. _I ) Y
                     -> ( Y R V -> Z ( ( t+ ` R ) u. _I ) V ) ) $=
      ( ctcl cfv cid cun wbr wi frege102 frege107 ax-mp ) HGEMNZOPZQZGFEQZHFUBQ
      RRUDUEHFUCQRRABCDEFHGIJKLSCEFGHKTUA $.
  $}

  ${
    frege109.x $e |- X e. U $.
    frege109.r $e |- R e. V $.
    $d y z R $.  $d y z X $.
    $( The property of belonging to the ` R ` -sequence beginning with ` X ` is
       hereditary in the ` R ` -sequence.  Proposition 109 of [Frege1879]
       p. 74.  (Contributed by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege109 $p |- R hereditary ( ( ( t+ ` R ) u. _I ) " { X } ) $=
      ( vy vz cv ctcl cfv wcel wbr wi cvv vex cop df-br elimasn bitr4i cid cima
      cun csn wal whe frege75 frege108 elexi imbi2i 3imtr3i alrimiv mpg ) GIZAJ
      KUAUCZDUDUBZLZUNHIZAMZURUPLZNZHUENUPAUFGGHUPAUGUQVAHDUNUOMZUSDURUOMZNUQVA
      BOOCAURUNDEGPZHPZFUHVBDUNQUOLUQDUNUORUODUNDBEUIZVDSTVCUTUSVCDURQUOLUTDURU
      ORUODURVFVESTUJUKULUM $.
  $}

  ${
    frege110.x $e |- X e. A $.
    frege110.y $e |- Y e. B $.
    frege110.m $e |- M e. C $.
    frege110.r $e |- R e. D $.
    $d a R $.  $d a X $.  $d a Y $.
    $( Proposition 110 of [Frege1879] p. 75.  (Contributed by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege110 $p |- ( A. a ( Y R a -> X ( ( t+ ` R ) u. _I ) a )
                     -> ( Y ( t+ ` R ) M -> X ( ( t+ ` R ) u. _I ) M ) ) $=
      ( ctcl cid cima wbr wi wcel cvv cfv cun csn whe cv frege109 imaundir fvex
      wal imaexg ax-mp imai snex eqeltri frege78 cop elexi elimasn df-br bitr4i
      unex vex imbi2i albii 3imtr3g ) ENUAZOUBZGUCZPZEUDZHIUEZEQZGVKVGQZRZIUIZH
      FVFQZGFVGQZRZREADGJMUFVJVLVKVISZRZIUIVPFVISZRVOVRVITEBCDHFIKLMVIVFVHPZOVH
      PZUBTVFOVHUGWBWCVFTSWBTSENUHVFVHTUJUKWCVHTVHULGUMUNVAUNUOVTVNIVSVMVLVSGVK
      UPVGSVMVGGVKGAJUQZIVBURGVKVGUSUTVCVDWAVQVPWAGFUPVGSVQVGGFWDFCLUQURGFVGUSU
      TVCVEUK $.
  $}

  ${
    frege111.z $e |- Z e. A $.
    frege111.y $e |- Y e. B $.
    frege111.v $e |- V e. C $.
    frege111.r $e |- R e. D $.
    $( If ` Y ` belongs to the ` R ` -sequence beginning with ` Z ` , then
       every result of an application of the procedure ` R ` to ` Y ` belongs
       to the ` R ` -sequence beginning with ` Z ` or precedes ` Z ` in the
       ` R ` -sequence.  Proposition 111 of [Frege1879] p. 75.  (Contributed by
       RP, 7-Jul-2020.)  (Revised by RP, 8-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege111 $p |- ( Z ( ( t+ ` R ) u. _I ) Y -> ( Y R V -> ( -. V ( t+ ` R ) Z
                     -> Z ( ( t+ ` R ) u. _I ) V ) ) ) $=
      ( ctcl cfv cid cun wbr wi wn frege108 frege25 ax-mp ) HGEMNZOPZQZGFEQZHFU
      DQZRRUEUFFHUCQSZUGRRRABCDEFGHIJKLTUEUFUGUHUAUB $.
  $}

  ${
    frege112.z $e |- Z e. V $.
    $( Identity implies belonging to the ` R ` -sequence beginning with self.
       Proposition 112 of [Frege1879] p. 76.  (Contributed by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege112 $p |- ( Z = X -> X ( ( t+ ` R ) u. _I ) Z ) $=
      ( ctcl cfv wbr wn wceq wi cid cun frege105 frege11 ax-mp ) CDAFGZHIZDCJZK
      CDQLMHZKSTKABCDENRSTOP $.

    $( Proposition 113 of [Frege1879] p. 76.  (Contributed by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege113 $p |- ( ( Z ( ( t+ ` R ) u. _I ) X
                       -> ( -. Z ( t+ ` R ) X -> Z = X ) )
                     -> ( Z ( ( t+ ` R ) u. _I ) X -> ( -. Z ( t+ ` R ) X
                          -> X ( ( t+ ` R ) u. _I ) Z ) ) ) $=
      ( wceq ctcl cfv cid cun wbr wi wn frege112 frege7 ax-mp ) DCFZCDAGHZIJZKZ
      LDCSKZDCRKMZQLLUAUBTLLLABCDENQTUAUBOP $.
  $}

  ${
    frege114.x $e |- X e. U $.
    frege114.z $e |- Z e. V $.
    $( If ` X ` belongs to the ` R ` -sequence beginning with ` Z ` , then
       ` Z ` belongs to the ` R ` -sequence beginning with ` X ` or ` X `
       follows ` Z ` in the ` R ` -sequence.  Proposition 114 of [Frege1879]
       p. 76.  (Contributed by RP, 7-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege114 $p |- ( Z ( ( t+ ` R ) u. _I ) X -> ( -. Z ( t+ ` R ) X
                     -> X ( ( t+ ` R ) u. _I ) Z ) ) $=
      ( ctcl cfv cid cun wbr wn wceq wi frege104 frege113 ax-mp ) EDAHIZJKZLZED
      SLMZEDNOOUAUBDETLOOABEDFPACDEGQR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  _Begriffsschrift_ Chapter III Single-valued procedures
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  ` Fun ``' ``' R ` means the relationship content of procedure ` R ` is
  single-valued.  The double converse allows to simply apply this syntax in
  place of Frege's even though the original never explicitly limited discussion
  of propositional statements which vary on two variables to relations.

  ~ dffrege115 through ~ frege133 develop this and how functions relate
  to transitive and transitive-reflexive closures.

$)

  ${
    $d a b c R $.
    $( If from the circumstance that ` c ` is a result of an application of the
       procedure ` R ` to ` b ` , whatever ` b ` may be, it can be inferred
       that every result of an application of the procedure ` R ` to ` b ` is
       the same as ` c ` , then we say :  "The procedure ` R ` is
       single-valued".  Definition 115 of [Frege1879] p. 77.  (Contributed by
       RP, 7-Jul-2020.) $)
    dffrege115 $p |- ( A. c A. b ( b R c -> A. a ( b R a -> a = c ) )
                       <-> Fun `' `' R ) $=
      ( cv wbr weq wi wal cop ccnv wcel alcom wa vex brcnv df-br 3bitr3ri albii
      bitr3i wex wfun wmo 19.21v impexp anbi12ci imbi1i bitri opeq2 eleq1d dfmo
      mo4 3bitr2i wrel relcnv biantrur dffun5 bitr4i 3bitri ) CEZDEZAFZUTBEZAFZ
      BDGZHZBIHZCIDIVGDIZCIUTVCJZAKZKZLZVEHBIDUAZCIZVKUBZVGDCMVHVMCVHVLUTVAJZVK
      LZNZVEHZDIBIZVLBUCVMVHVSBIZDIVTVGWADVGVBVFHZBIWAVBVFBUDWBVSBWBVBVDNZVEHVS
      VBVDVEUEWCVRVEVBVQVDVLUTVAVKFVAUTVJFVQVBUTVAVJCOZDOZPUTVAVKQVAUTAWEWDPRUT
      VCVKFVCUTVJFVLVDUTVCVJWDBOZPUTVCVKQVCUTAWFWDPRUFUGTSTSVSDBMUHVLVQBDVEVIVP
      VKVCVAUTUIUJULVLBDUKUMSVNVKUNZVNNVOWGVNVJUOUPCBDVKUQURUS $.
  $}

  ${
    frege116.x $e |- X e. U $.
    ${
      $d a b c R $.  $d a b X $.
      $( One direction of ~ dffrege115 .  Proposition 116 of [Frege1879] p. 77.
         (Contributed by RP, 8-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege116 $p |- ( Fun `' `' R -> A. b ( b R X
                                             -> A. a ( b R a -> a = X ) ) ) $=
        ( vc cv wbr wi wal ccnv wb wceq wsbc sbcal sbcimg ax-mp bitri imbi12i
        weq wfun dffrege115 frege68c wcel sbcbr2g csbvarg breq2i sbceq2g eqeq2i
        csb sbcg albii imbitrdi ) EHZGHZAIZUODHZAIZDGUAZJZDKZJZEKZGKALLUBZMZVEU
        OCAIZUSURCNZJZDKZJZEKZJADEGUCVFVEVDGCOZVLVDVEGCBFUDVMVCGCOZEKVLVCEGCPVN
        VKEVNUQGCOZVBGCOZJZVKCBUEZVNVQMFUQVBGCBQRVOVGVPVJVOUOGCUPUKZAIZVGVRVOVT
        MFGCUOUPABUFRVSCUOAVRVSCNFGCBUGRZUHSVPVAGCOZDKVJVADGCPWBVIDWBUSGCOZUTGC
        OZJZVIVRWBWEMFUSUTGCBQRWCUSWDVHVRWCUSMFUSGCBULRWDURVSNZVHVRWDWFMFGCURUP
        BUIRVSCURWAUJSTSUMSTSUMSUNR $.
    $}

    ${
      $d a b R $.  $d a b X $.
      $( Lemma for ~ frege118 .  Proposition 117 of [Frege1879] p. 78.
         (Contributed by RP, 8-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege117 $p |- ( ( A. b ( b R X -> A. a ( b R a -> a = X ) )
                         -> ( Y R X -> A. a ( Y R a -> a = X ) ) )
                       -> ( Fun `' `' R
                            -> ( Y R X -> A. a ( Y R a -> a = X ) ) ) ) $=
        ( ccnv wfun cv wbr wceq wi wal frege116 frege9 ax-mp ) AHHIZFJZCAKSEJZA
        KTCLZMENMFNZMUBDCAKDTAKUAMENMZMRUCMMABCEFGORUBUCPQ $.
    $}

    frege118.y $e |- Y e. V $.
    ${
      $d a b R $.  $d a b X $.  $d a Y $.
      $( Simplified application of one direction of ~ dffrege115 .  Proposition
         118 of [Frege1879] p. 78.  (Contributed by RP, 8-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege118 $p |- ( Fun `' `' R -> ( Y R X -> A. a ( Y R a -> a = X ) ) ) $=
        ( vb cv wbr wceq wi wal ccnv wsbc wb sbcimg ax-mp bitri sbcbr1g csbvarg
        wfun frege58c wcel csb breq1i sbcal sbcg imbi12i albii sylib frege117 )
        IJZDAKZUNFJZAKZUPDLZMZFNZMZINZEDAKZEUPAKZURMZFNZMZMAOOUCVGMVBVAIEPZVGVA
        IECHUDVHUOIEPZUTIEPZMZVGECUEZVHVKQHUOUTIECRSVIVCVJVFVIIEUNUFZDAKZVCVLVI
        VNQHIEUNDACUASVMEDAVLVMELHIECUBSZUGTVJUSIEPZFNVFUSFIEUHVPVEFVPUQIEPZURI
        EPZMZVEVLVPVSQHUQURIECRSVQVDVRURVQVMUPAKZVDVLVQVTQHIEUNUPACUASVMEUPAVOU
        GTVLVRURQHURIECUISUJTUKTUJTULABDEFIGUMS $.
    $}

    ${
      $d a R $.  $d a X $.  $d a Y $.
      $( Lemma for ~ frege120 .  Proposition 119 of [Frege1879] p. 78.
         (Contributed by RP, 8-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege119 $p |- ( ( A. a ( Y R a -> a = X ) -> ( Y R A -> A = X ) )
                       -> ( Fun `' `' R
                            -> ( Y R X -> ( Y R A -> A = X ) ) ) ) $=
        ( ccnv wfun wbr cv wceq wi wal frege118 frege19 ax-mp ) BJJKZFEBLZFGMZB
        LUBENOGPZOOUCFABLAENOZOTUAUDOOOBCDEFGHIQTUAUCUDRS $.
    $}

    frege120.a $e |- A e. W $.
    ${
      $d a R $.  $d a X $.  $d a Y $.
      $( Simplified application of one direction of ~ dffrege115 .  Proposition
         120 of [Frege1879] p. 78.  (Contributed by RP, 8-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege120 $p |- ( Fun `' `' R -> ( Y R X -> ( Y R A -> A = X ) ) ) $=
        ( va cv wbr wceq wi ccnv wsbc wb ax-mp bitri wal wfun frege58c csb wcel
        sbcim1 sbcbr2g csbvarg breq2i sbceq1g eqeq1i 3imtr3g syl frege119 ) GKL
        ZBMZUOFNZOZKUAZGABMZAFNZOZOBPPUBGFBMVBOOUSURKAQZVBURKAEJUCVCUPKAQZUQKAQ
        ZUTVAUPUQKAUFVDGKAUOUDZBMZUTAEUEZVDVGRJKAGUOBEUGSVFAGBVHVFANJKAEUHSZUIT
        VEVFFNZVAVHVEVJRJKAUOFEUJSVFAFVIUKTULUMABCDFGKHIUNS $.
    $}

    $( Lemma for ~ frege122 .  Proposition 121 of [Frege1879] p. 79.
       (Contributed by RP, 8-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege121 $p |- ( ( A = X -> X ( ( t+ ` R ) u. _I ) A )
                   -> ( Fun `' `' R -> ( Y R X
                        -> ( Y R A -> X ( ( t+ ` R ) u. _I ) A ) ) ) ) $=
      ( ccnv wfun wbr wceq wi ctcl cfv cid cun frege120 frege20 ax-mp ) BKKLZGF
      BMZGABMZAFNZOOOUFFABPQRSMZOUCUDUEUGOOOOABCDEFGHIJTUCUDUEUFUGUAUB $.

    $( If ` X ` is a result of an application of the single-valued procedure
       ` R ` to ` Y ` , then every result of an application of the procedure
       ` R ` to ` Y ` belongs to the ` R ` -sequence beginning with ` X ` .
       Proposition 122 of [Frege1879] p. 79.  (Contributed by RP, 8-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege122 $p |- ( Fun `' `' R
                     -> ( Y R X -> ( Y R A -> X ( ( t+ ` R ) u. _I ) A ) ) ) $=
      ( wceq ctcl cfv cid cun wbr wi ccnv wfun frege112 frege121 ax-mp ) AFKFAB
      LMNOPZQBRRSGFBPGABPUCQQQBEFAJTABCDEFGHIJUAUB $.
  $}

  ${
    frege123.x $e |- X e. U $.
    frege123.y $e |- Y e. V $.
    ${
      $d a R $.  $d a X $.  $d a Y $.
      $( Lemma for ~ frege124 .  Proposition 123 of [Frege1879] p. 79.
         (Contributed by RP, 8-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege123 $p |- ( ( A. a ( Y R a -> X ( ( t+ ` R ) u. _I ) a )
                       -> ( Y ( t+ ` R ) M -> X ( ( t+ ` R ) u. _I ) M ) )
                     -> ( Fun `' `' R
                          -> ( Y R X
                               -> ( Y ( t+ ` R ) M
                                    -> X ( ( t+ ` R ) u. _I ) M ) ) ) ) $=
        ( ccnv wfun wbr cv ctcl cfv cid cun wi wal cvv frege122 alrimdv frege19
        vex ax-mp ) AJJKZFEALZFGMZALEUHANOZPQZLRZGSZRRULFCUILECUJLRZRUFUGUMRRRU
        FUGUKGUHABDTEFHIGUDUAUBUFUGULUMUCUE $.
    $}

    frege124.m $e |- M e. W $.
    frege124.r $e |- R e. S $.
    ${
      $d a R $.  $d a X $.  $d a Y $.
      $( If ` X ` is a result of an application of the single-valued procedure
         ` R ` to ` Y ` and if ` M ` follows ` Y ` in the ` R ` -sequence, then
         ` M ` belongs to the ` R ` -sequence beginning with ` X ` .
         Proposition 124 of [Frege1879] p. 80.  (Contributed by RP,
         8-Jul-2020.)  (Proof modification is discouraged.) $)
      frege124 $p |- ( Fun `' `' R
                     -> ( Y R X
                          -> ( Y ( t+ ` R ) M
                               -> X ( ( t+ ` R ) u. _I ) M ) ) ) $=
        ( va cv wbr ctcl cfv cid wi ccnv cun wal wfun frege110 frege123 ax-mp )
        HMNZAOGUGAPQZRUAZOSMUBHDUHOGDUIOSZSATTUCHGAOUJSSCEFBADGHMIJKLUDACDEGHMI
        JUEUF $.
    $}

    $( Lemma for ~ frege126 .  Proposition 125 of [Frege1879] p. 81.
       (Contributed by RP, 9-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege125 $p |- ( ( X ( ( t+ ` R ) u. _I ) M
                         -> ( -. X ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) X ) )
                       -> ( Fun `' `' R
                            -> ( Y R X
                                 -> ( Y ( t+ ` R ) M
                                      -> ( -. X ( t+ ` R ) M
                                           -> M ( ( t+ ` R ) u. _I ) X ) ) )
                          ) ) $=
      ( ccnv wfun wbr ctcl cfv cid cun wi wn frege124 frege20 ax-mp ) AMMNZHGAO
      ZHDAPQZOZGDUGRSZOZTTTUJGDUGOUADGUIOTZTUEUFUHUKTTTTABCDEFGHIJKLUBUEUFUHUJU
      KUCUD $.

    $( If ` M ` follows ` Y ` in the ` R ` -sequence and if the procedure ` R `
       is single-valued, then every result of an application of the procedure
       ` R ` to ` Y ` belongs to the ` R ` -sequence beginning with ` M ` or
       precedes ` M ` in the ` R ` -sequence.  Proposition 126 of [Frege1879]
       p. 81.  (Contributed by RP, 9-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege126 $p |- ( Fun `' `' R
                       -> ( Y R X
                            -> ( Y ( t+ ` R ) M
                                 -> ( -. X ( t+ ` R ) M
                                      -> M ( ( t+ ` R ) u. _I ) X ) ) ) ) $=
      ( ctcl cfv cid cun wbr wn wi ccnv wfun frege114 frege125 ax-mp ) GDAMNZOP
      ZQGDUEQRDGUFQSZSATTUAHGAQHDUEQUGSSSAFCDGKIUBABCDEFGHIJKLUCUD $.

    $( Communte antecedents of ~ frege126 .  Proposition 127 of [Frege1879]
       p. 82.  (Contributed by RP, 9-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege127 $p |- ( Fun `' `' R
                       -> ( Y ( t+ ` R ) M
                            -> ( Y R X
                                 -> ( -. X ( t+ ` R ) M
                                      -> M ( ( t+ ` R ) u. _I ) X ) ) ) ) $=
      ( ccnv wfun wbr ctcl cfv wn cid wi cun frege126 frege12 ax-mp ) AMMNZHGAO
      ZHDAPQZOZGDUGORDGUGSUAOTZTTTUEUHUFUITTTABCDEFGHIJKLUBUEUFUHUIUCUD $.

    $( Lemma for ~ frege129 .  Proposition 128 of [Frege1879] p. 83.
       (Contributed by RP, 9-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege128 $p |- ( ( M ( ( t+ ` R ) u. _I ) Y
                         -> ( Y R X
                              -> ( -. X ( t+ ` R ) M
                                   -> M ( ( t+ ` R ) u. _I ) X ) ) )
                       -> ( Fun `' `' R
                            -> ( ( -. Y ( t+ ` R ) M
                                   -> M ( ( t+ ` R ) u. _I ) Y )
                                 -> ( Y R X
                                      -> ( -. X ( t+ ` R ) M
                                           -> M ( ( t+ ` R ) u. _I ) X ) ) ) )
                     ) $=
      ( ccnv wfun ctcl cfv wbr wn cid wi cun frege127 frege51 ax-mp ) AMMNZHDAO
      PZQZHGAQGDUFQRDGUFSUAZQTTZTTDHUHQZUITUEUGRUJTUITTTABCDEFGHIJKLUBUEUGUIUJU
      CUD $.

    $( If the procedure ` R ` is single-valued and ` Y ` belongs to the ` R `
       -sequence beginning with ` M ` or precedes ` M ` in the ` R ` -sequence,
       then every result of an application of the procedure ` R ` to ` Y `
       belongs to the ` R ` -sequence beginning with ` M ` or precedes ` M ` in
       the ` R ` -sequence.  Proposition 129 of [Frege1879] p. 83.
       (Contributed by RP, 9-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege129 $p |- ( Fun `' `' R
                       -> ( ( -. Y ( t+ ` R ) M
                              -> M ( ( t+ ` R ) u. _I ) Y )
                            -> ( Y R X
                                 -> ( -. X ( t+ ` R ) M
                                      -> M ( ( t+ ` R ) u. _I ) X ) ) ) ) $=
      ( ctcl cfv cid cun wbr wn wi ccnv wfun frege111 frege128 ax-mp ) DHAMNZOP
      ZQZHGAQGDUEQRDGUFQSSZSATTUAHDUEQRUGSUHSSFECBAGHDKJILUBABCDEFGHIJKLUCUD $.
  $}

  ${
    frege130.m $e |- M e. U $.
    frege130.r $e |- R e. V $.
    ${
      $d a M $.  $d a b R $.
      $( Lemma for ~ frege131 .  Proposition 130 of [Frege1879] p. 84.
         (Contributed by RP, 9-Jul-2020.)
         (Proof modification is discouraged.) $)
      frege130 $p |- (
        ( A. b ( ( -. b ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) b )
                 -> A. a ( b R a
                           -> ( -. a ( t+ ` R ) M -> M ( ( t+ ` R ) u. _I ) a )
         ) )
         -> R hereditary ( ( `' ( t+ ` R ) " { M } )
                                     u. ( ( ( t+ ` R ) u. _I ) " { M } ) ) )
        -> ( Fun `' `' R
             -> R hereditary ( ( `' ( t+ ` R ) " { M } )
                                     u. ( ( ( t+ ` R ) u. _I ) " { M } ) ) )
       ) $=
        ( ccnv wfun cv ctcl wbr wn cun wi wal cima cvv vex cfv cid csn frege129
        whe alrimdv alrimiv frege9 ax-mp ) AIIJZFKZCALUAZMNCUKULUBOZMPZUKEKZAMU
        OCULMNCUOUMMPPZEQPZFQZPURULICUCZRUMUSROAUEZPUJUTPPUJUQFUJUNUPEADSCSBUOU
        KETFTGHUDUFUGUJURUTUHUI $.
    $}

    ${
      $d a b M $.  $d a b R $.
      $( If the procedure ` R ` is single-valued, then the property of
         belonging to the ` R ` -sequence beginning with ` M ` or preceeding
         ` M ` in the ` R ` -sequence is hereditary in the ` R ` -sequence.
         Proposition 131 of [Frege1879] p. 85.  (Contributed by RP,
         9-Jul-2020.)  (Proof modification is discouraged.) $)
      frege131 $p |- ( Fun `' `' R
                       -> R hereditary ( ( `' ( t+ ` R ) " { M } )
                                     u. ( ( ( t+ ` R ) u. _I ) " { M } ) ) ) $=
        ( vb va cv ccnv cima cun wcel wbr wi wal wn elimasn df-br imbi12i df-or
        ctcl cfv csn cid whe wfun frege75 wo cop elexi vex brcnv 3bitr2i notbii
        elun bitr4i 3bitri imbi2i albii imbi1i frege130 sylbi ax-mp ) GIZAUBUCZ
        JZCUDZKZVFUELZVHKZLZMZVEHIZANZVNVLMZOZHPZOZGPZVLAUFZOZAJJUGWAOZGHVLAUHW
        BVECVFNZQZCVEVJNZOZVOVNCVFNZQZCVNVJNZOZOZHPZOZGPZWAOWCVTWOWAVSWNGVMWGVR
        WMVMVEVIMZVEVKMZUIWPQZWQOWGVEVIVKUPWPWQUAWRWEWQWFWPWDWPCVEUJZVGMCVEVGNW
        DVGCVECBEUKZGULZRCVEVGSCVEVFWTXAUMUNUOWQWSVJMWFVJCVEWTXARCVEVJSUQTURVQW
        LHVPWKVOVPVNVIMZVNVKMZUIXBQZXCOWKVNVIVKUPXBXCUAXDWIXCWJXBWHXBCVNUJZVGMC
        VNVGNWHVGCVNWTHULZRCVNVGSCVNVFWTXFUMUNUOXCXEVJMWJVJCVNWTXFRCVNVJSUQTURU
        SUTTUTVAABCDHGEFVBVCVD $.
    $}

    $( Lemma for ~ frege133 .  Proposition 132 of [Frege1879] p. 86.
       (Contributed by RP, 9-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege132 $p |- (
       ( R hereditary ( ( `' ( t+ ` R ) " { M } )
                                     u. ( ( ( t+ ` R ) u. _I ) " { M } ) )
                          -> ( X ( t+ ` R ) M
                               -> ( X ( t+ ` R ) Y
                                    -> ( -. Y ( t+ ` R ) M
                                         -> M ( ( t+ ` R ) u. _I ) Y ) ) ) )
       -> ( Fun `' `' R
                          -> ( X ( t+ ` R ) M
                               -> ( X ( t+ ` R ) Y
                                    -> ( -. Y ( t+ ` R ) M
                                         -> M ( ( t+ ` R ) u. _I ) Y ) ) ) )
      ) $=
      ( ccnv wfun ctcl cfv csn cima cid cun whe wi wbr wn frege131 frege9 ax-mp
      ) AIIJZAKLZICMZNUEOPZUFNPAQZRUHECUESEFUESFCUESTCFUGSRRRZRUDUIRRABCDGHUAUD
      UHUIUBUC $.
  $}

  ${
    frege133.x $e |- X e. U $.
    frege133.y $e |- Y e. V $.
    frege133.m $e |- M e. W $.
    frege133.r $e |- R e. S $.
    $( If the procedure ` R ` is single-valued and if ` M ` and ` Y ` follow
       ` X ` in the ` R ` -sequence, then ` Y ` belongs to the ` R ` -sequence
       beginning with ` M ` or precedes ` M ` in the ` R ` -sequence.
       Proposition 133 of [Frege1879] p. 86.  (Contributed by RP, 9-Jul-2020.)
       (Proof modification is discouraged.) $)
    frege133 $p |- ( Fun `' `' R
                          -> ( X ( t+ ` R ) M
                               -> ( X ( t+ ` R ) Y
                                    -> ( -. Y ( t+ ` R ) M
                                         -> M ( ( t+ ` R ) u. _I ) Y ) ) ) ) $=
      ( ccnv cima cid cun wcel wbr wi cvv ctcl cfv csn whe wfun wn cnvex imaexg
      fvex ax-mp imaundir imai snex eqeltri frege83 elexi elimasn df-br 3bitr2i
      unex cop brcnv wo elun df-or notbii bitr4i imbi12i 3bitri imbi2i frege132
      sylbi ) AUAUBZMZDUCZNZVMOPZVONZPZAUDZGVPQZGHVMRZHVSQZSZSZSZAMMUEGDVMRZWBH
      DVMRZUFZDHVQRZSZSZSZSZVPVRACEBTTGHIJLVNTQVPTQVMAUAUIZUGVNVOTUHUJVRVMVONZO
      VONZPTVMOVOUKWPWQVMTQWPTQWOVMVOTUHUJWQVOTVOULDUMUNUTUNUOWFVTWMSWNWEWMVTWA
      WGWDWLWADGVAVNQDGVNRWGVNDGDFKUPZGCIUPZUQDGVNURDGVMWRWSVBUSWCWKWBWCHVPQZHV
      RQZVCWTUFZXASWKHVPVRVDWTXAVEXBWIXAWJWTWHWTDHVAZVNQDHVNRWHVNDHWRHEJUPZUQDH
      VNURDHVMWRXDVBUSVFXAXCVQQWJVQDHWRXDUQDHVQURVGVHVIVJVHVJAFDBGHKLVKVLUJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Exploring Topology via Seifert and Threlfall
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  See Seifert and Threlfall: A Textbook Of Topology (1980) which is an English
  translation of Lehrbuch der Topologie (1934).

$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Equinumerosity of sets of relations and maps
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Because ` ( ( 2o ^m B ) ^m A ) ~~ ( 2o ^m ( A X. B ) ) ~~ `
  ` ( ( 2o ^m A ) ^m B ) ` is an instance of the law of exponents:
  ` ( ( C ^m B ) ^m A ) ~~ ( C ^m ( A X. B ) ) ~~ ( ( C ^m A ) ^m B ) `
  we are led to see that ` ( ~P B ^m A ) ~~ ~P ( A X. B ) ~~ ( ~P A ^m B ) `
  is true for any two sets, ` A ` and ` B ` , and thus there exist one-to-one
  onto relations between each of these three sets of relations.

$)

  $( The set of all possible relations between two sets is equinumerous to the
     set of all mappings from one set to the powerset of the other.  See
     ~ rfovf1od for a demonstration of a natural one-to-one onto mapping.
     (Contributed by RP, 27-Apr-2021.) $)
  enrelmap $p |- ( ( A e. V /\ B e. W ) -> ~P ( A X. B ) ~~ ( ~P B ^m A ) ) $=
    ( wcel wa cxp cpw c2o cmap co cen wbr xpcomeng syl pw2eng entr syl2anc con0
    cvv pwen xpexg ancoms enrefg mapen syl2anr 2on simpr mapxpen mp3an2i ensymd
    simpl ) ACEZBDEZFZABGZHZIBAGZJKZLMZUSBHZAJKZLMUQVBLMUOUQURHZLMZVCUSLMZUTUOU
    PURLMVDABCDNUPURUAOUOURTEZVEUNUMVFBADCUBUCURTPOUQVCUSQRUOVBUSUOVBIBJKZAJKZL
    MZVHUSLMZVBUSLMUNVAVGLMAALMVIUMBDPACUDVAVGAAUEUFISEUOUNUMVJUGUMUNUHUMUNULIB
    ASDCUIUJVBVHUSQRUKUQUSVBQR $.

  $( The set of all possible relations between two sets is equinumerous to the
     set of all mappings from one set to the powerset of the other.
     (Contributed by RP, 27-Apr-2021.) $)
  enrelmapr $p |- ( ( A e. V /\ B e. W ) -> ~P ( A X. B ) ~~ ( ~P A ^m B ) ) $=
    ( wcel wa cxp cpw cen wbr cmap co xpcomeng pwen syl enrelmap ancoms syl2anc
    entr ) ACEZBDEZFZABGZHZBAGZHZIJZUFAHBKLZIJZUDUHIJUBUCUEIJUGABCDMUCUENOUATUI
    BADCPQUDUFUHSR $.

  $( The set of all mappings from one set to the powerset of the other is
     equinumerous to the set of all mappings from the second set to the
     powerset of the first.  (Contributed by RP, 27-Apr-2021.) $)
  enmappw $p |- ( ( A e. V /\ B e. W ) -> ( ~P B ^m A ) ~~ ( ~P A ^m B ) ) $=
    ( wcel wa cpw cmap co cxp cen wbr enrelmap ensymd enrelmapr entr syl2anc )
    ACEBDEFZBGAHIZABJGZKLTAGBHIZKLSUAKLRTSABCDMNABCDOSTUAPQ $.

  $( The set of all mappings from the powerset to the powerset is equinumerous
     to the set of all mappings from the set to the powerset of the powerset.
     (Contributed by RP, 27-Apr-2021.) $)
  enmappwid $p |- ( A e. V -> ( ~P A ^m ~P A ) ~~ ( ~P ~P A ^m A ) ) $=
    ( cpw cvv wcel cmap co cen wbr pwexg enmappw mpancom ) ACZDEABEMMFGMCAFGHIA
    BJMADBKL $.

  ${
    $( The operator which gives a 1-to-1 mapping between relations
       and functions to subsets. $)
    rfovd.rf $e |- O = ( a e. _V , b e. _V |->
                         ( r e. ~P ( a X. b ) |->
                           ( x e. a |-> { y e. b | x r y } ) ) ) $.
    rfovd.a $e |- ( ph -> A e. V ) $.
    rfovd.b $e |- ( ph -> B e. W ) $.
    ${
      $d A a b r $.  $d A a b x $.  $d B a b r $.  $d B a b x $.  $d B a b y $.
      $d ph a b $.

      $( Value of the operator, ` ( A O B ) ` , which maps between relations
         and functions for relations between base sets, ` A ` and ` B ` .
         (Contributed by RP, 25-Apr-2021.) $)
      rfovd $p |- ( ph -> ( A O B ) = ( r e. ~P ( A X. B ) |->
                           ( x e. A |-> { y e. B | x r y } ) ) ) $=
        ( cvv cv cxp cmpt wceq wcel cpw wbr crab cmpo a1i wa xpeq12 pweqd simpl
        rabeq adantl mpteq12dv elexd xpexd pwexg mptexg 3syl ovmpod ) AJKDEOOIJ
        PZKPZQZUAZBUSBPCPIPUBZCUTUCZRZRZIDEQZUAZBDVCCEUCZRZRZFOFJKOOVFUDSALUEUS
        DSZUTESZUFZVFVKSAVNIVBVEVHVJVNVAVGUSDUTEUGUHVNBUSVDDVIVLVMUIVMVDVISVLVC
        CUTEUJUKULULUKADGMUMAEHNUMAVGOTVHOTVKOTADEGHMNUNVGOUOIVHVJOUPUQUR $.
    $}

    ${
      rfovfvd.r $e |- ( ph -> R e. ~P ( A X. B ) ) $.
      rfovfvd.f $e |- F = ( A O B ) $.
      ${
        $d A a b r x $.  $d B a b r x $.  $d B a b r y $.  $d R r x $.
        $d R r y $.  $d ph a b r $.

        $( Value of the operator, ` ( A O B ) ` , which maps between relations
           and functions for relations between base sets, ` A ` and ` B ` , and
           relation ` R ` .  (Contributed by RP, 25-Apr-2021.) $)
        rfovfvd $p |- ( ph -> ( F ` R ) = ( x e. A |->
                                            { y e. B | x R y } ) ) $=
          ( cv cmpt wbr crab cxp cpw co rfovd eqtrid wceq breq rabbidv mpteq2dv
          cvv adantl mptexd fvmptd ) AKFBDBSZCSZKSZUAZCEUBZTZBDUPUQFUAZCEUBZTZD
          EUCUDZGULAGDEHUEKVEVATRABCDEHIJKLMNOPUFUGURFUHZVAVDUHAVFBDUTVCVFUSVBC
          EUPUQURFUIUJUKUMQABDVCIOUNUO $.
      $}

      ${
        rfovfvfvd.x $e |- ( ph -> X e. A ) $.
        rfovfvfvd.g $e |- G = ( F ` R ) $.
        ${
          $d A a b r x $.  $d B a b r x y $.  $d R r x y $.  $d X x y $.
          $d ph a b r x $.

          $( Value of the operator, ` ( A O B ) ` , which maps between
             relations and functions for relations between base sets, ` A ` and
             ` B ` , relation ` R ` , and left element ` X ` .  (Contributed by
             RP, 25-Apr-2021.) $)
          rfovfvfvd $p |- ( ph -> ( G ` X ) = { y e. B | X R y } ) $=
            ( cv wbr crab cvv cfv cmpt rfovfvd eqtrid wceq breq1 rabbidv adantl
            wcel rabexg syl fvmptd ) ABLBUCZCUCZFUDZCEUEZLUTFUDZCEUEZDHUFAHFGUG
            BDVBUHUBABCDEFGIJKMNOPQRSTUIUJUSLUKZVBVDUKAVEVAVCCEUSLUTFULUMUNUAAE
            KUOVDUFUORVCCEKUPUQUR $.
        $}
      $}
    $}

    ${
      rfovcnvf1od.f $e |- F = ( A O B ) $.
      ${
        $d A a b f r u x y $.  $d A b f r u v x y $.  $d B a b f r u x y $.
        $d B b f r u v x y $.  $d W a u x $.  $d W v x $.
        $d ph a b f r u x y $.

        $( Properties of the operator, ` ( A O B ) ` , which maps between
           relations and functions for relations between base sets, ` A ` and
           ` B ` .  (Contributed by RP, 27-Apr-2021.) $)
        rfovcnvf1od $p |- ( ph -> ( F : ~P ( A X. B ) -1-1-onto-> ( ~P B ^m A )
                             /\ `' F = ( f e. ( ~P B ^m A ) |->
                                         { <. x , y >. |
                                           ( x e. A
                                             /\ y e. ( f ` x ) ) } ) ) ) $=
          ( wcel wa cvv vu vv cxp cpw cmap co wf1o ccnv cfv copab cmpt wceq wbr
          cv crab eqid wss ssrab2 a1i sselpwd adantr fmpttd pwexd elmapd mpbird
          wf xpexd wtru wi biimpa ffvelcdmda ex elpwi sseld syl6 imdistand trud
          jca2 ssopab2dv opabssxp sstrdi wfn simplrr elmapfn syl wral ralrimivw
          ad2antrr rabexg nfcv fnmptf 3syl cin dfin5 simpllr simpl2im ffvelcdmd
          elmapi simpr elpwid sseqin2 sylib ibar rabbidv adantl 3eqtr3a cop weq
          breq2 cbvrabv breq1 df-br bitrdi eqtrid cbvmptv opeq1d eleq12d eleq1d
          vex fveq2d anbi12d opelopaba ad3antrrr fvmptd2 eqtr4d eqfnfvd simplrl
          simpl wrel xpss df-rel sylibr relopabv wb simplr eqtrdi syl5 pm4.71rd
          cdm crn anim1i elrab anbi2i fvmptd eleq2d pm5.32da opeldm dmss dmxpss
          anim12i opelrn rnxpss anbi2d bitrd 3bitr4d bitr2id eqrelrdv2 syl21anc
          rnss impbida f1ocnv2d rfovd f1oeq1 cnveq eqeq1d ) ADEUCZUDZEUDZDUEUFZ
          GUGZGUHZFUVIBUNZDRZCUNZUVLFUNZUIZRZSZBCUJZUKZULZSZUVGUVIKUVGBDUVLUVNK
          UNZUMZCEUOZUKZUKZUGZUWGUHZUVTULZSZAKFUVGUVIUWFUVSUWGUWGUPAUWFUVIRZUWC
          UVGRZAUWLDUVHUWFVFABDUWEUVHAUWEUVHRUVMAUWEEJPUWEEUQAUWDCEURUSUTVAVBAU
          VHDUWFTIAEJPVCZOVDVEVAAUVOUVIRZSZUVSUVFTAUVFTRUWOADEIJOPVGVAUWPUVSUVM
          UVNERZSZVHSZBCUJUVFUWPUVRUWSBCUWPUVRUWRVHUWPUVMUVQUWQUWPUVMUVPUVHRZUV
          QUWQVIUWPUVMUWTUWPDUVHUVLUVOAUWODUVHUVOVFZAUVHDUVOTIUWNOVDVJVKVLUWTUV
          PEUVNUVPEVMVNVOVPUVRVQVRVSVHBCDEVTWAUTAUWMUWOSZSZUWCUVSULZUVOUWFULZUX
          CUXDSZUADUVOUWFUXFUWOUVODWBAUWMUWOUXDWCUVOUVHDWDWEUXFEJRZUWETRZBDWFUW
          FDWBAUXGUXBUXDPWHUXGUXHBDUWDCEJWIWGBDUWETBDWJWKWLUXFUAUNZDRZSZUXIUVOU
          IZUXJMUNZUXLRZSZMEUOZUXIUWFUIUXKEUXLWMZUXNMEUOZUXLUXPMEUXLWNUXKUXLEUQ
          UXQUXLULUXKUXLEUXKDUVHUXIUVOUXKUWMUWOUXAAUXBUXDUXJWOUVOUVHDWRWPUXFUXJ
          WSZWQWTUXLEXAXBUXJUXRUXPULUXFUXJUXNUXOMEUXJUXNXCXDXEXFUXKLUXILUNZUXMX
          GZUWCRZMEUOZUXPDUWFTBLDUWEUYCBLXHZUWEUVLUXMUWCUMZMEUOUYCUWDUYECMEUVNU
          XMUVLUWCXIXJUYDUYEUYBMEUYDUYEUXTUXMUWCUMZUYBUVLUXTUXMUWCXKUXTUXMUWCXL
          XMXDXNXOUXKLUAXHZSZUYBUXOMEUYHUYBUXIUXMXGZUVSRUXOUYHUYAUYIUWCUVSUYHUX
          TUXIUXMUXKUYGWSXPUXCUXDUXJUYGWOXQUVRUXOBCUXIUXMUAXSZMXSBUAXHZCMXHZSZU
          VMUXJUVQUXNUYMUVLUXIDUYKUYLYHZXRUYMUVNUXMUVPUXLUYKUYLWSUYMUVLUXIUVOUY
          NXTXQYAYBXMXDUXSUXKUXGUXPTRAUXGUXBUXDUXJPYCUXOMEJWIWEYDYEYFUXCUXESZUW
          CYIZUVSYIZUXGUWMSZUXESZUXDUYOUWCTTUCZUQUYPUYOUWCUVFUYTUYOUWCUVFAUWMUW
          OUXEYGWTDEYJWAUWCYKYLUYQUYOUVRBCYMUSUXCUYRUXEAUXGUXBUWMPUWMUWOYHUUJUU
          AUYSUAUBUWCUVSUXIUBUNZXGZUVSRUXJVUAUXLRZSZUYSVUBUWCRZUVRVUDBCUXIVUAUY
          JUBXSZUYKCUBXHZSZUVMUXJUVQVUCVUHUVLUXIDUYKVUGYHZXRVUHUVNVUAUVPUXLUYKV
          UGWSVUHUVLUXIUVOVUIXTXQYAYBUYSUXJVUAUXIUXMUWCUMZMEUOZRZSZUXJVUAERZVUE
          SZSZVUDVUEVUMVUPYNUYSVULVUOUXJVUJVUEMVUAEMUBXHVUJUXIVUAUWCUMVUEUXMVUA
          UXIUWCXIUXIVUAUWCXLXMUUBUUCUSUYSUXJVUCVULUYSUXJSZUXLVUKVUAVUQLUXIUYFM
          EUOZVUKDUVOTVUQUVOUWFLDVURUKUYRUXEUXJYOBLDUWEVURUYDUWEUXTUVNUWCUMZCEU
          OVURUYDUWDVUSCEUVLUXTUVNUWCXKXDVUSUYFCMEUVNUXMUXTUWCXIXJYPXOYPUYGVURV
          UKULVUQUYGUYFVUJMEUXTUXIUXMUWCXKXDXEUYSUXJWSUXGVUKTRUWMUXEUXJVUJMEJWI
          YCUUDUUEUUFUYSUWCUVFUQZVUEVUPYNUYSUWCUVFUXGUWMUXEYOWTVUTVUEUXJVUESVUP
          VUTVUEUXJVUEUXIUWCYSZRVUTUXJUXIVUAUWCUYJVUFUUGVUTVVADUXIVUTVVAUVFYSDU
          WCUVFUUHDEUUIWAVNYQYRVUTVUEVUOUXJVUTVUEVUNVUEVUAUWCYTZRVUTVUNUXIVUAUW
          CUYJVUFUUKVUTVVBEVUAVUTVVBUVFYTEUWCUVFUUSDEUULWAVNYQYRUUMUUNWEUUOUUPU
          UQUURUUTUVAAGUWGULZUWBUWKYNAGDEHUFUWGQABCDEHIJKLMNOPUVBXNVVCUVJUWHUWA
          UWJUVGUVIGUWGUVCVVCUVKUWIUVTGUWGUVDUVEYAWEVE $.
      $}

      ${
        $d A a b f r x y $.  $d B a b f r x y $.  $d W a x $.
        $d ph a b f r x y $.

        $( Value of the converse of the operator, ` ( A O B ) ` , which maps
           between relations and functions for relations between base sets,
           ` A ` and ` B ` .  (Contributed by RP, 27-Apr-2021.) $)
        rfovcnvd $p |- ( ph -> `' F =
                   ( f e. ( ~P B ^m A ) |->
                   { <. x , y >. | ( x e. A /\ y e. ( f ` x ) ) } ) ) $=
          ( cpw cv wcel cxp cmap co wf1o ccnv cfv copab cmpt rfovcnvf1od simprd
          wa wceq ) ADEUARERDUBUCZGUDGUEFUMBSZDTCSUNFSUFTUKBCUGUHULABCDEFGHIJKL
          MNOPQUIUJ $.

        $( The value of the operator, ` ( A O B ) ` , which maps between
           relations and functions for relations between base sets, ` A ` and
           ` B ` , is a bijection.  (Contributed by RP, 27-Apr-2021.) $)
        rfovf1od $p |- ( ph -> F : ~P ( A X. B ) -1-1-onto-> ( ~P B ^m A ) ) $=
          ( vf cpw cv wcel cxp cmap co wf1o ccnv wa copab cmpt wceq rfovcnvf1od
          cfv simpld ) ADEUARERDUBUCZFUDFUEQUMBSZDTCSUNQSUKTUFBCUGUHUIABCDEQFGH
          IJKLMNOPUJUL $.
      $}

      ${
        $d A a b g r x y $.  $d B a b g r x y $.  $d G g x y $.  $d W a x $.
        $d ph a b g r x y $.
        rfovcnvfv.g $e |- ( ph -> G e. ( ~P B ^m A ) ) $.
        $( Value of the converse of the operator, ` ( A O B ) ` , which maps
           between relations and functions for relations between base sets,
           ` A ` and ` B ` , evaluated at function ` G ` .  (Contributed by RP,
           27-Apr-2021.) $)
        rfovcnvfvd $p |- ( ph -> ( `' F ` G )
                                 = { <. x , y >. |
                                     ( x e. A /\ y e. ( G ` x ) ) } ) $=
          ( vg wcel cv cfv wa copab cpw cmap co ccnv rfovcnvd wceq fveq1 eleq2d
          cvv anbi2d opabbidv adantl simprl elmapi ffvelcdmda sylan elpwid impr
          sseld opabex2 fvmptd ) ASGBUAZDTZCUAZVFSUAZUBZTZUCZBCUDZVGVHVFGUBZTZU
          CZBCUDZEUEZDUFUGZFUHUMABCDESFHIJKLMNOPQUIVIGUJZVMVQUJAVTVLVPBCVTVKVOV
          GVTVJVNVHVFVIGUKULUNUOUPRAVPBCDEIJOPAVGVOUQAVGVOVHETAVGUCZVNEVHWAVNEA
          GVSTZVGVNVRTRWBDVRVFGGVRDURUSUTVAVCVBVDVE $.
      $}
    $}
  $}

  ${
    $( The operator which gives a 1-to-1 a mapping to a subset and
       a reverse mapping from elements. $)
    fsovd.fs $e |- O = ( a e. _V , b e. _V |-> ( f e. ( ~P b ^m a ) |->
                         ( y e. b |-> { x e. a | y e. ( f ` x ) } ) ) ) $.
    fsovd.a $e |- ( ph -> A e. V ) $.
    fsovd.b $e |- ( ph -> B e. W ) $.
    ${
      $d A a b f $.  $d A a b x $.  $d A a b y $.  $d B a b f $.  $d B a b y $.
      $d ph a b $.
      $( Value of the operator, ` ( A O B ) ` , which maps between maps from
         one base set to subsets of the second to maps from the second base set
         to subsets of the first for base sets, ` A ` and ` B ` .  (Contributed
         by RP, 25-Apr-2021.) $)
      fsovd $p |- ( ph -> ( A O B ) = ( f e. ( ~P B ^m A ) |->
                                     ( y e. B |->
                                      { x e. A | y e. ( f ` x ) } ) ) ) $=
        ( cvv cv cpw cmap cmpt wceq co cfv wcel crab cmpo a1i pweq adantl simpl
        wa oveq12d simpr rabeq adantr mpteq12dv elexd ovex mptex ovmpod ) AJKDE
        OOFKPZQZJPZRUAZCUTCPBPFPUBUCZBVBUDZSZSZFEQZDRUAZCEVDBDUDZSZSZGOGJKOOVGU
        ETALUFVBDTZUTETZUJZVGVLTAVOFVCVFVIVKVOVAVHVBDRVNVAVHTVMUTEUGUHVMVNUIUKV
        OCUTVEEVJVMVNULVMVEVJTVNVDBVBDUMUNUOUOUHADHMUPAEINUPVLOUCAFVIVKVHDRUQUR
        UFUS $.
    $}

    ${
      fsovd.rf $e |- R = ( a e. _V , b e. _V |->
                            ( r e. ~P ( a X. b ) |->
                              ( u e. a |-> { v e. b | u r v } ) ) ) $.
      fsovd.cnv $e |- C = ( a e. _V , b e. _V |->
                            ( s e. ~P ( a X. b ) |-> `' s ) ) $.

      $d A a b f r u v $.  $d A a b f s u v $.  $d A a b f x y $.
      $d A c d f r t u v $.  $d A c t x y $.  $d A d x $.  $d B a b f r u v $.
      $d B a b d s u v $.  $d B c t y $.  $d W a u $.  $d ph a b f r u v $.

      $( The operator which gives a 1-to-1 a mapping to a subset and a reverse
         mapping from elements can be composed from the operator which gives a
         1-to-1 mapping between relations and functions to subsets and the
         converse operator.  (Contributed by RP, 15-May-2021.) $)
      fsovrfovd $p |- ( ph -> ( A O B ) = ( ( B R A ) o. ( ( A C B ) o.
                                           `' ( A R B ) ) ) ) $=
        ( vt vc vd co cpw cmap cv wcel cfv wa copab cmpt ccom crab ccnv cxp wbr
        cvv xpexd adantr wss wb elmapi ffvelcdmda elpwid sseld impancom pm4.71d
        ex pm5.32rd ancom anbi1i bitrdi opabbidv opabssxp eqsstrdi adantl eqidd
        sselpwd rfovd weq breq rabbidv mpteq2dv breq1 breq2 cbvrabv eqtrdi wceq
        cbvmptv cop df-br vex eleq1w anbi2d fveq2 eleq2d anbi12d opelopab bitri
        ibar bicomd rabbiia eqtri mpteq2i fmptco eqid rfovcnvd a1i xpeq12 pweqd
        cmpo mpteq1d elexd pwexg mptexg 3syl ovmpod cnveq coeq2d fsovd 3eqtr4rd
        cnvopab ) AGFIUFZJGUGZFUHUFZEUIZFUJZDUIZYIJUIZUKZUJZULZDEUMZUNZUOJYHCGC
        UIBUIZYLUKZUJZBFUPZUNZUNYFFGHUFZFGIUFZUQZUOZUOFGKUFAJUCYHGFURZUGZYPUDGU
        DUIZUEUIZUCUIZUSZUEFUPZUNZUUBYQYFAYLYHUJZULZYPUUGUTAUUGUTUJUUOAGFMLTSVA
        VBUUOYPUUGVCAUUOYPYKGUJZYJULZYNULZDEUMUUGUUOYOUUSDEUUOYOYJUUQULZYNULZUU
        SUUOYNYJUUTUUOYNYJUUTVDUUOYNULYJUUQUUOYJYNUUQUUOYJULZYMGYKUVBYMGUUOFYGY
        IYLYLYGFVEVFVGVHVIVJVKVLZUUTUURYNYJUUQVMVNVOVPYNDEGFVQVRVSWAAYQVTAYFOUU
        HEGYIYKOUIZUSZDFUPZUNZUNUCUUHUUNUNAEDGFIMLOPQUATSWBOUCUUHUVGUUNOUCWCZUV
        GEGYIYKUUKUSZDFUPZUNUUNUVHEGUVFUVJUVHUVEUVIDFYIYKUVDUUKWDWEWFEUDGUVJUUM
        EUDWCZUVJUUIYKUUKUSZDFUPUUMUVKUVIUVLDFYIUUIYKUUKWGWEUVLUULDUEFYKUUJUUIU
        UKWHWIWJWLWJWLWJUUKYPWKZUUNUDGUUJFUJZUUIUUJYLUKZUJZULZUEFUPZUNZUUBUVMUD
        GUUMUVRUVMUULUVQUEFUVMUULUUIUUJYPUSZUVQUUIUUJUUKYPWDUVTUUIUUJWMYPUJUVQU
        UIUUJYPWNYOYJUUIYMUJZULUVQDEUUIUUJUDWOUEWODUDWCYNUWAYJDUDYMWPWQEUEWCZYJ
        UVNUWAUVPEUEFWPUWBYMUVOUUIYIUUJYLWRWSWTXAXBVOWEWFUVSUDGUUIYSUJZBFUPZUNU
        UBUDGUVRUWDUVRUVPUEFUPUWDUVQUVPUEFUVNUVPUVQUVNUVPXCXDXEUVPUWCUEBFUEBWCU
        VOYSUUIUUJYRYLWRWSWIXFXGUDCGUWDUUAUDCWCUWCYTBFUDCYSWPWEWLXFWJXHAUUFYQYF
        AJNYHFGURZUGZYOEDUMZNUIZUQZYPUUEUUCUUPUWGUWEUTAUWEUTUJZUUOAFGLMSTVAZVBU
        UOUWGUWEVCAUUOUWGUVAEDUMUWEUUOYOUVAEDUVCVPYNEDFGVQVRVSWAAEDFGJUUDILMOPQ
        UASTUUDXIXJAPQFGUTUTNPUIZQUIZURZUGZUWIUNZNUWFUWIUNZHUTHPQUTUTUWPXNWKAUB
        XKUWLFWKUWMGWKULZUWPUWQWKAUWRNUWOUWFUWIUWRUWNUWEUWLFUWMGXLXMXOVSAFLSXPA
        GMTXPAUWJUWFUTUJUWQUTUJUWKUWEUTXQNUWFUWIUTXRXSXTUWHUWGWKUWIUWGUQYPUWHUW
        GYAYOEDYEWJXHYBABCFGJKLMPQRSTYCYD $.
    $}

    ${
      fsovfvd.g $e |- G = ( A O B ) $.
      ${
        fsovfvd.f $e |- ( ph -> F e. ( ~P B ^m A ) ) $.

        ${
          $d A a b f x $.  $d A a b f y $.  $d B a b f y $.  $d F f x $.
          $d F f y $.  $d ph a b f $.

          $( Value of the operator, ` ( A O B ) ` , which maps between maps
             from one base set to subsets of the second to maps from the second
             base set to subsets of the first for base sets, ` A ` and ` B ` ,
             when applied to function ` F ` .  (Contributed by RP,
             25-Apr-2021.) $)
          fsovfvd $p |- ( ph -> ( G ` F ) = ( y e. B |->
                                         { x e. A | y e. ( F ` x ) } ) ) $=
            ( cv cmpt cfv wcel crab cpw cmap cvv fsovd eqtrid wceq fveq1 eleq2d
            co rabbidv mpteq2dv adantl mptexd fvmptd ) AFGCECSZBSZFSZUAZUBZBDUC
            ZTZCEURUSGUAZUBZBDUCZTZEUDDUEULZHUFAHDEIULFVIVDTQABCDEFIJKLMNOPUGUH
            UTGUIZVDVHUIAVJCEVCVGVJVBVFBDVJVAVEURUSUTGUJUKUMUNUORACEVGKPUPUQ $.
        $}

        ${
          fsovfvfvd.h $e |- H = ( G ` F ) $.
          fsovfvfvd.y $e |- ( ph -> Y e. B ) $.

          ${
            $d A a b f x y $.  $d B a b f y $.  $d F f x y $.  $d Y x y $.
            $d ph a b f y $.

            $( Value of the operator, ` ( A O B ) ` , which maps between maps
               from one base set to subsets of the second to maps from the
               second base set to subsets of the first for base sets, ` A ` and
               ` B ` , when applied to function ` F ` and element ` Y ` .
               (Contributed by RP, 25-Apr-2021.) $)
            fsovfvfvd $p |- ( ph -> ( H ` Y ) = { x e. A |
                                                  Y e. ( F ` x ) } ) $=
              ( cfv wcel crab cvv cmpt fsovfvd eqtrid wceq eleq1 rabbidv adantl
              cv rabexg syl fvmptd ) ACMCUNZBUNGUCZUDZBDUEZMUSUDZBDUEZEIUFAIGHU
              CCEVAUGUAABCDEFGHJKLNOPQRSTUHUIURMUJZVAVCUJAVDUTVBBDURMUSUKULUMUB
              ADKUDVCUFUDQVBBDKUOUPUQ $.
          $}
        $}
      $}

      ${
        $d A a b f $.  $d A a b x $.  $d A a b y $.  $d B a b f $.
        $d B a b y $.  $d ph a b f $.  $d ph a b y $.

        $( The operator, ` ( A O B ) ` , which maps between maps from one base
           set to subsets of the second to maps from the second base set to
           subsets of the first for base sets, ` A ` and ` B ` , gives a
           function between two sets of functions.  (Contributed by RP,
           27-Apr-2021.) $)
        fsovfd $p |- ( ph -> G : ( ~P B ^m A ) --> ( ~P A ^m B ) ) $=
          ( cpw co cv wcel cmap cfv crab fsovd eqtrid wf wss ssrab2 a1i sselpwd
          cmpt adantr fmpttd cvv pwexd elmapd mpbird fmpt3d ) AFEQDUARZCECSZBSF
          SZUBTZBDUCZUKZDQZEUARZGAGDEHRFUSVDUKPABCDEFHIJKLMNOUDUEAVDVFTZVAUSTAV
          GEVEVDUFACEVCVEAVCVETUTETAVCDINVCDUGAVBBDUHUIUJULUMAVEEVDUNJADINUOOUP
          UQULUR $.
      $}

      ${
        fsovcnvlem.h $e |- H = ( B O A ) $.

        ${
          $d A a b c d f x y $.  $d A c d f g u v x y $.  $d B a b c d f y $.
          $d B c d f g u v y $.  $d ph a b c d f y $.  $d ph c d f u v y $.

          $( The ` O ` operator, which maps between maps from one base set to
             subsets of the second to maps from the second base set to subsets
             of the first for base sets, gives a family of functions that
             include their own inverse.  (Contributed by RP, 27-Apr-2021.) $)
          fsovcnvlem $p |- ( ph -> ( H o. G ) = ( _I |` ( ~P B ^m A ) ) ) $=
            ( wcel cmpt vu vv vg vd vc ccom cpw cmap co cv cfv crab cid cres wf
            wss ssrab2 a1i sselpwd adantr fmpttd cvv pwexd elmapd mpbird eqtrid
            fsovd cmpo weq oveq2 rabeq mpteq2dv mpteq12dv oveq1d mpteq1 cbvmpov
            pweq eqid fveq1 eleq2d rabbidv cbvmptv eleq1w fveq2 cbvrabv mpteq2i
            eqtri mpoeq123i 3eqtri wceq fmptco wa eqidd adantl simpr rabexg syl
            ad2antrr fvmptd wb elrab3 ad2antlr bitrd rabbidva adantlr ffvelcdmd
            elmapi elpwid sseqin2 sylib dfin5 eqtr3di eqtr4d mpteq2dva mptresid
            cin feqmptd eqcomi 3eqtrd ) AHGUFFEUGZDUHUIZUADUAUJZUBUJZCECUJZBUJZ
            FUJZUKZSZBDULZTZUKZSZUBEULZTZTFYAYFTZUMYAUNZAFUCYADUGZEUHUIZYJUADYB
            YCUCUJZUKZSZUBEULZTZYNGHAYJYRSZYFYASZAUUDEYQYJUOACEYIYQAYIYQSYDESAY
            IDJOYIDUPAYHBDUQURUSUTVAAYQEYJVBKADJOVCPVDVEUTAGDEIUIFYAYJTQABCDEFI
            JKLMNOPVGVFAHEDIUIUCYRUUCTRAUBUAEDUCIKJUDUEILMVBVBFMUJZUGZLUJZUHUIZ
            CUUFYHBUUHULZTZTZVHUDUEVBVBFUEUJZUGZUDUJZUHUIZCUUMYHBUUOULZTZTZVHUD
            UEVBVBUCUUPUAUUMUUAUBUUOULZTZTZVHNLMUDUEVBVBUULUUSFUUGUUOUHUIZCUUFU
            UQTZTLUDVIZFUUIUUKUVCUVDUUHUUOUUGUHVJUVECUUFUUJUUQYHBUUHUUOVKVLVMMU
            EVIZFUVCUVDUUPUURUVFUUGUUNUUOUHUUFUUMVQVNCUUFUUMUUQVOVMVPUDUEVBVBUU
            SVBVBUVBVBVRZUVGUUSUCUUPCUUMYDYEYSUKZSZBUUOULZTZTUVBFUCUUPUURUVKFUC
            VIZCUUMUUQUVJUVLYHUVIBUUOUVLYGUVHYDYEYFYSVSVTWAVLWBUCUUPUVKUVAUVKUA
            UUMYBUVHSZBUUOULZTUVACUAUUMUVJUVNCUAVIUVIUVMBUUOCUAUVHWCWAWBUAUUMUV
            NUUTUVMUUABUBUUOBUBVIUVHYTYBYEYCYSWDVTWEWFWGWFWGWHWIPOVGVFYSYJWJZUA
            DUUBYMUVOUUAYLUBEUVOYTYKYBYCYSYJVSVTWAVLWKAFYAYNYFAUUEWLZYNUADYBYFU
            KZTZYFUVPUADYMUVQUVPYBDSZWLZYMYCUVQSZUBEULZUVQAUVSYMUWBWJUUEAUVSWLZ
            YLUWAUBEUWCYCESZWLZYLYBYCYGSZBDULZSZUWAUWEYKUWGYBUWECYCYIUWGEYJVBUW
            EYJWMCUBVIZYIUWGWJUWEUWIYHUWFBDCUBYGWCWAWNUWCUWDWOAUWGVBSZUVSUWDADJ
            SUWJOUWFBDJWPWQWRWSVTUVSUWHUWAWTAUWDUWFUWABYBDBUAVIYGUVQYCYEYBYFWDV
            TXAXBXCXDXEUVTEUVQXPZUVQUWBUVTUVQEUPUWKUVQWJUVTUVQEUVTDXTYBYFUUEDXT
            YFUOAUVSYFXTDXGZXBUVPUVSWOXFXHUVQEXIXJUBEUVQXKXLXMXNUUEYFUVRWJAUUEU
            ADXTYFUWLXQWNXMXNYOYPWJAYPYOFYAXOXRURXS $.
        $}

        ${
          $d A a b f x y $.  $d B a b f x y $.  $d ph a b f y $.

          $( The value of the converse ` ( A O B ) ` is ` ( B O A ) ` , where
             ` O ` is the operator which maps between maps from one base set to
             subsets of the second to maps from the second base set to subsets
             of the first for base sets, gives a family of functions that
             include their own inverse.  (Contributed by RP, 27-Apr-2021.) $)
          fsovcnvd $p |- ( ph -> `' G = H ) $=
            ( cpw cmap co fsovfd fsovcnvlem 2fcoidinvd ) AESDTUADSETUAGHABCDEFG
            IJKLMNOPQUBABCEDFHIKJLMNPORUBABCDEFGHIJKLMNOPQRUCABCEDFHGIKJLMNPORQ
            UCUD $.
        $}
      $}

      ${
        $d A a b f x y $.  $d B a b f x y $.  $d F f x y $.  $d ph a b f y $.
        fsovcnvfvd.f $e |- ( ph -> F e. ( ~P A ^m B ) ) $.
        $( The value of the converse of ` ( A O B ) ` , where ` O ` is the
           operator which maps between maps from one base set to subsets of the
           second to maps from the second base set to subsets of the first for
           base sets, evaluated at function ` F ` .  (Contributed by RP,
           27-Apr-2021.) $)
        fsovcnvfvd $p |- ( ph -> ( `' G ` F ) = ( y e. A |->
                                                 { x e. B |
                                                   y e. ( F ` x ) } ) ) $=
          ( cfv cv ccnv co wcel crab cmpt eqid fsovcnvd fveq1d fsovfvd eqtrd )
          AGHUAZSGEDIUBZSCDCTBTGSUCBEUDUEAGUKULABCDEFHULIJKLMNOPQULUFZUGUHABCED
          FGULIKJLMNPOUMRUIUJ $.
      $}

      ${
        $d A a b f x y $.  $d B a b f x y $.  $d ph a b f y $.

        $( The value of ` ( A O B ) ` is a bijection, where ` O ` is the
           operator which maps between maps from one base set to subsets of the
           second to maps from the second base set to subsets of the first for
           base sets.  (Contributed by RP, 27-Apr-2021.) $)
        fsovf1od $p |- ( ph -> G : ( ~P B ^m A ) -1-1-onto-> ( ~P A ^m B ) ) $=
          ( cpw cmap co wfn ccnv wf1o fsovfd ffnd fsovcnvd fneq1d mpbird dff1o4
          eqid sylanbrc ) AGEQDRSZTGUAZDQERSZTZUKUMGUBAUKUMGABCDEFGHIJKLMNOPUCU
          DAUNEDHSZUMTAUMUKUOABCEDFUOHJIKLMONUOUIZUCUDAUMULUOABCDEFGUOHIJKLMNOP
          UPUEUFUGUKUMGUHUJ $.
      $}
    $}
  $}

  ${
    $( An operator which operates on self-maps, ` f ` , of a power
       set of a base set, ` b ` .  This operation was generalized
       from equation 1 of Basic Properties of Closure Spaces by
       Baerbel and Peter Stadler and can be used in generalizations
       of topologies analogous to ~ ntrval2 . $)
    dssmapfvd.o $e |- O = ( b e. _V |-> ( f e. ( ~P b ^m ~P b ) |->
                            ( s e. ~P b |-> ( b \ ( f ` ( b \ s ) ) ) ) ) ) $.
    dssmapfvd.d $e |- D = ( O ` B ) $.
    dssmapfvd.b $e |- ( ph -> B e. V ) $.

    ${
      $d B b f $.  $d B b s $.  $d ph b $.
      $( Value of the duality operator for self-mappings of subsets of a base
         set, ` B ` .  (Contributed by RP, 19-Apr-2021.) $)
      dssmapfvd $p |- ( ph -> D = ( f e. ( ~P B ^m ~P B ) |->
                            ( s e. ~P B |-> ( B \ ( f ` ( B \ s ) ) ) ) ) ) $=
        ( cfv cpw cmap co cv cdif cmpt cvv mpteq12dv wceq oveq12d difeq1 fveq2d
        pweq id difeq12d elexd wcel ovex mptexg mp1i fvmptd3 eqtrid ) ACBELDBMZ
        UONOZGUOBBGPZQZDPZLZQZRZRZJAHBDHPZMZVENOZGVEVDVDUQQZUSLZQZRZRVCSESIVDBU
        AZDVFVJUPVBVKVEUOVEUONVDBUEZVLUBVKGVEVIUOVAVLVKVDBVHUTVKUFVKVGURUSVDBUQ
        UCUDUGTTABFKUHUPSUIVCSUIAUOUONUJDUPVBSUKULUMUN $.
    $}

    ${
      dssmapfv2d.f $e |- ( ph -> F e. ( ~P B ^m ~P B ) ) $.
      dssmapfv2d.g $e |- G = ( D ` F ) $.

      ${
        $d B b f s $.  $d F f s $.  $d ph b f $.

        $( Value of the duality operator for self-mappings of subsets of a base
           set, ` B ` when applied to function ` F ` .  (Contributed by RP,
           19-Apr-2021.) $)
        dssmapfv2d $p |- ( ph -> G = ( s e. ~P B |->
                                       ( B \ ( F ` ( B \ s ) ) ) ) ) $=
          ( cfv cv cdif cvv wcel cpw cmpt cmap co dssmapfvd wceq fveq1 mpteq2dv
          difeq2d adantl pwexg mptexg 3syl fvmptd eqtrid ) AFECPIBUAZBBIQRZEPZR
          ZUBZOADEIUPBUQDQZPZRZUBZUTUPUPUCUDCSABCDGHIJKLMUEVAEUFZVDUTUFAVEIUPVC
          USVEVBURBUQVAEUGUIUHUJNABHTUPSTUTSTMBHUKIUPUSSULUMUNUO $.
      $}

      dssmapfv3d.s $e |- ( ph -> S e. ~P B ) $.
      dssmapfv3d.t $e |- T = ( G ` S ) $.

      ${
        $d B b f s $.  $d F f s $.  $d S s $.  $d ph b f s $.

        $( Value of the duality operator for self-mappings of subsets of a base
           set, ` B ` when applied to function ` F ` and subset ` S ` .
           (Contributed by RP, 19-Apr-2021.) $)
        dssmapfv3d $p |- ( ph -> T = ( B \ ( F ` ( B \ S ) ) ) ) $=
          ( cdif cfv cv cpw dssmapfv2d wceq difeq2 fveq2d difeq2d adantl difexd
          cvv fvmptd eqtrid ) AEDHUABBDTZGUAZTZSAKDBBKUBZTZGUAZTZUPBUCHUKABCFGH
          IJKLMNOPQUDUQDUEZUTUPUEAVAUSUOBVAURUNGUQDBUFUGUHUIRABUOJOUJULUM $.
      $}
    $}

    ${
      $d B b f g s z $.  $d B f g s t u z $.  $d ph b f g s z $.
      $d ph f g s t u z $.
      $( For any base set ` B ` the duality operator for self-mappings of
         subsets of that base set is its own inverse, an involution.
         (Contributed by RP, 20-Apr-2021.) $)
      dssmapnvod $p |- ( ph -> `' D = D ) $=
        ( vt cdif cfv cmpt wcel wceq wa difeq2d cvv vg vz vu cmap co cv ccnv wf
        cpw simpr weq difeq2 fveq2d cbvmptv eqtrdi cun ssun1 sspwi pwidg sselid
        syl fvex elpwun sylib ad2antrr fmpt3d adantr elmapd mpbird adantrl wral
        pwexd simplr adantl vex difexd fvmptd wss elpwi dfss4 biimpa ffvelcdmda
        adantlrl elpwid adantlrr 3eqtrrd ralrimiva wfn elmapfn ad2antrl impbida
        fnmptfvd mptcnv dssmapfvd cnveqd fveq1 mpteq2dv mpteq2i eqtri 3eqtr4d
        jca ) ADBUIZXBUDUEZGXBBBGUFZMZDUFZNZMZOZOZUGUAXCUBXBBBUBUFZMZUAUFZNZMZO
        ZOCUGCADUAXCXIXCXPAXFXCPZXMXIQZRZXMXCPZXFXPQZRZAXSRZXTYAAXRXTXQAXRRZXTX
        BXBXMUHZYDLXBBBLUFZMZXFNZMZXBXMYDXMXILXBYIOAXRUJGLXBXHYIGLUKZXGYHBYJXEY
        GXFXDYFBULUMSUNUOAYIXBPZXRYFXBPZABBYHUPZUIZPYKAXBYNBBYMBYHUQURABFPBXBPK
        BFUSVAZUTBBYHYGXFVBVCVDVEVFYDXBXBXMTTAXBTPZXRABFKVLZVGZYRVHVIVJYCYAYFXF
        NZBYGXMNZMZQZLXBVKYCUUBLXBYCYLRUUABBBYGMZXFNZMZMZBBYSMZMZYSAXRYLUUAUUFQ
        XQYDYLRZYTUUEBUUIUCYGBBUCUFZMZXFNZMZUUEXBXMTUUIXMXIUCXBUUMOAXRYLVMGUCXB
        XHUUMGUCUKZXGUULBUUNXEUUKXFXDUUJBULUMSUNUOUUJYGQZUUMUUEQUUIUUOUULUUDBUU
        OUUKUUCXFUUJYGBULZUMSVNAYGXBPZXRYLABBYFUPZUIZPUUQAXBUUSBBUURBYFUQURYOUT
        BBYFLVOVCVDZVEAUUETPXRYLABUUDFKVPVEVQSWCYLUUFUUHQYCYLUUEUUGBYLUUDYSBYLU
        UCYFXFYLYFBVRUUCYFQYFBVSYFBVTVDZUMSSVNAXQYLUUHYSQZXRAXQRZYLRZYSBVRUVBUV
        DYSBUVCXBXBYFXFAXQXBXBXFUHZAXBXBXFTTYQYQVHWAWBWDYSBVTVDWEWFWGYCXBXOUUAT
        LXFTUBXQXFXBWHAXRXFXBXBWIWJLUBUKZYTXNBUVFYGXLXMYFXKBULUMSAUUATPXSYLABYT
        FKVPVEAXOTPXSXKXBPABXNFKVPVEWLVIXAAYBRZXQXRAYAXQXTAYARZXQUVEUVHLXBUUAXB
        XFUVHXFXPLXBUUAOAYAUJUBLXBXOUUAUBLUKZXNYTBUVIXLYGXMXKYFBULUMSUNUOAUUAXB
        PZYAYLABBYTUPZUIZPUVJAXBUVLBBUVKBYTUQURYOUTBBYTYGXMVBVCVDVEVFUVHXBXBXFT
        TAYPYAYQVGZUVMVHVIVJUVGXRYFXMNZYIQZLXBVKUVGUVOLXBUVGYLRYIBBUUCXMNZMZMZB
        BUVNMZMZUVNAYAYLYIUVRQXTUVHYLRZYHUVQBUWAUCYGBUUKXMNZMZUVQXBXFTUWAXFXPUC
        XBUWCOAYAYLVMUBUCXBXOUWCUBUCUKZXNUWBBUWDXLUUKXMXKUUJBULUMSUNUOUUOUWCUVQ
        QUWAUUOUWBUVPBUUOUUKUUCXMUUPUMSVNAUUQYAYLUUTVEAUVQTPYAYLABUVPFKVPVEVQSW
        CYLUVRUVTQUVGYLUVQUVSBYLUVPUVNBYLUUCYFXMUVAUMSSVNAXTYLUVTUVNQZYAAXTRZYL
        RZUVNBVRUWEUWGUVNBUWFXBXBYFXMAXTYEAXBXBXMTTYQYQVHWAWBWDUVNBVTVDWEWFWGUV
        GXBXHYITLXMTGXTXMXBWHAYAXMXBXBWIWJLGUKZYHXGBUWHYGXEXFYFXDBULUMSAYITPYBY
        LABYHFKVPVEAXHTPYBXDXBPABXGFKVPVEWLVIXAWKWMACXJABCDEFGHIJKWNWOABCUAEFUB
        HEHTDHUFZUIZUWJUDUEZGUWJUWIUWIXDMZXFNZMZOZOZOHTUAUWKUBUWJUWIUWIXKMZXMNZ
        MZOZOZOIHTUWPUXADUAUWKUWOUWTDUAUKZUWOGUWJUWIUWLXMNZMZOUWTUXBGUWJUWNUXDU
        XBUWMUXCUWIUWLXFXMWPSWQGUBUWJUXDUWSGUBUKZUXCUWRUWIUXEUWLUWQXMXDXKUWIULU
        MSUNUOUNWRWSJKWNWT $.
    $}

    ${
      $d B b f s $.  $d ph b f s $.

      $( For any base set ` B ` the duality operator for self-mappings of
         subsets of that base set is one-to-one and onto.  (Contributed by RP,
         21-Apr-2021.) $)
      dssmapf1od $p |- ( ph -> D : ( ~P B ^m ~P B ) -1-1-onto->
                                   ( ~P B ^m ~P B ) ) $=
        ( cpw cmap co wfn wceq cv cdif cmpt cvv ccnv wf1o dssmapfvd wcel mptexd
        cfv wral pwexd ralrimivw nfcv fnmptf syl biimprd sylc dssmapnvod nvof1o
        fneq1 syl2anc ) ACBLZUSMNZOZCUACPUTUTCUBACDUTGUSBBGQRDQUFRZSZSZPZVDUTOZ
        VAABCDEFGHIJKUCAVCTUDZDUTUGVFAVGDUTAGUSVBTABFKUHUEUIDUTVCTDUTUJUKULVEVA
        VFUTCVDUQUMUNABCDEFGHIJKUOUTCUPUR $.
    $}

    ${
      $d B b f s $.  $d ph b f s $.

      $( For any base set ` B ` the duality operator for self-mappings of
         subsets of that base set when composed with itself is the restricted
         identity operator.  (Contributed by RP, 21-Apr-2021.) $)
      dssmap2d $p |- ( ph -> ( D o. D ) = ( _I |` ( ~P B ^m ~P B ) ) ) $=
        ( ccnv ccom cid cpw cmap co cres dssmapnvod coeq1d wf1o wceq dssmapf1od
        f1ococnv1 syl eqtr3d ) ACLZCMZCCMNBOZUIPQZRZAUGCCABCDEFGHIJKSTAUJUJCUAU
        HUKUBABCDEFGHIJKUCUJUJCUDUEUF $.
    $}
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Generic Pseudoclosure Spaces, Pseudointerior Spaces, and Pseudoneighborhoods
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  <HTML>
  <P>
  For any base set, ` B ` , an arbitrary mapping of subsets to subsets
  can be called a pseudoclosure (pseudointerior) function, ` K ` ,
  with its dual of a pseudointerior (pseudoclosure), ` I `, related
  by the involution in ~ dssmapfvd .  As ` K `
  gains properties of the closure (interior) function of a topology
  on ` B `, so does its dual gain corresponding properties of the
  interior (closure) function of that topology.
  </P>

  <P>
  As ` ( ~P B ^m ~P B ) ~~ ( ~P ~P B ^m B ) ` there is also a natural
  isomorphism which maps from ` I ` to ` N ` (and likewise for
  ` K ` and ` M ` , introduced below) which identically gains the
  properties of the neighborhood function of a topology (modified and
  restricted to operate on single points). A function dual to ` N ` ,
  which Stadler and Stadler refer to as a convergent function, is
  represented by ` M ` in this section.
  </P>

  <!-- TODO: evaluate replacing 'convergent function' with 'adherents
  function' and replace 'neighborhood function' with 'neighborhoods
  function' so that we might more clearly refer to the members of the
  value of the functions as 'an adherent' and 'a neighborhood'.
  Likewise the collection N(x) could be a 'neighborhood system' and
  by analogy M(x) would be an 'adherent system'.  BJ suggested
  'adherent' but I want to think about it.
  -->

  <P>
  Based on this and the early treatment of topology in Seifert and
  Threlfall, it seems reasonable to define a pseudotopology as defined
  in terms of its base set and one of these functions with theorems
  treating the equivalence of the other definitions and adding
  topological structure if enough properties hold true.
  </P>

  <TABLE>
  <TR>
    <TD WIDTH="15%"> </TD>
    <TH WIDTH="17%"> Neighborhoods </TH>
    <TH></TH>
    <TH WIDTH="17%"> Interior </TH>
    <TH></TH>
    <TH WIDTH="17%"> Closure </TH>
    <TH></TH>
    <TH WIDTH="17%"> Convergents </TH>
    <TH> Theorems </TH>
  </TR>
  <TR>
    <TH WIDTH="15%"> Functions </TH>
    <TD WIDTH="17%" STYLE="text-align: center;">
    ` N e. ( ~P ~P B ^m B ) ` </TD>
    <TD></TD>
    <TD WIDTH="17%" STYLE="text-align: center;">
    ` I e. ( ~P B ^m ~P B ) ` </TD>
    <TD></TD>
    <TD WIDTH="17%" STYLE="text-align: center;">
    ` K e. ( ~P B ^m ~P B ) ` </TD>
    <TD></TD>
    <TD WIDTH="17%" STYLE="text-align: center;">
    ` M e. ( ~P ~P B ^m B ) ` </TD>
    <TD> </TD>
  </TR>
  <TR>
    <TD ROWSPAN="2" STYLE="text-align: center;">
        <DIV STYLE="font-weight: bold"> Correspondences </DIV>
        (assuming ` ( X e. B /\ S e. ~P B ) ` )
    </TD>
    <TD STYLE="text-align: center;"> ` S e. ( N `` X ) ` </TD>
    <TD STYLE="text-align: center;"> ` <-> ` </TD>
    <TD STYLE="text-align: center;"> ` X e. ( I `` S )  ` </TD>
    <TD STYLE="text-align: center;"> ` <-> ` </TD>
    <TD STYLE="text-align: center;"> ` -. X e. ( K `` ( B \ S ) ) ` </TD>
    <TD STYLE="text-align: center;"> ` <-> ` </TD>
    <TD STYLE="text-align: center;"> ` -. ( B \ S ) e. ( M `` X )  ` </TD>
    <TD ROWSPAN="2"> ~ ntrclselnel1 , ~ ntrneiel , ~ neicvgel1 </TD>
  </TR>
  <TR>
    <TD STYLE="text-align: center;"> ` -. ( B \ S ) e. ( N `` X ) ` </TD>
    <TD STYLE="text-align: center;"> ` <-> ` </TD>
    <TD STYLE="text-align: center;"> ` -. X e. ( I `` ( B \ S ) )  ` </TD>
    <TD STYLE="text-align: center;"> ` <-> ` </TD>
    <TD STYLE="text-align: center;"> ` X e. ( K `` S ) ` </TD>
    <TD STYLE="text-align: center;"> ` <-> ` </TD>
    <TD STYLE="text-align: center;"> ` S e. ( M `` X )  ` </TD>
  </TR>
  <TR>
    <TH> Neighborhoods </TH>
    <TD STYLE="text-align: center;"> ` ( N `` X ) ` </TD>
    <TD STYLE="text-align: center;"> ` = ` </TD>
    <TD STYLE="text-align: center;"> ` { s e. ~P B | X e. ( I `` s ) } ` </TD>
    <TD STYLE="text-align: center;"> ` = ` </TD>
    <TD STYLE="text-align: center;">
    ` { s e. ~P B | -. X e. ( K `` ( B \ s ) ) } ` </TD>
    <TD STYLE="text-align: center;"> ` = ` </TD>
    <TD STYLE="text-align: center;">
    ` { s e. ~P B | -. ( B \ s ) e. ( M `` X ) } ` </TD>
    <TD> ~ ntrneifv3 , ~ clsneifv3 , ~ neicvgfv </TD>
  </TR>
  <TR>
    <TH> Interior </TH>
    <TD STYLE="text-align: center;"> ` { x e. B | S e. ( N `` x ) } ` </TD>
    <TD STYLE="text-align: center;"> ` = ` </TD>
    <TD STYLE="text-align: center;"> ` ( I `` S ) ` </TD>
    <TD STYLE="text-align: center;"> ` = ` </TD>
    <TD STYLE="text-align: center;"> ` ( B \ ( K `` ( B \ S ) ) ) ` </TD>
    <TD STYLE="text-align: center;"> ` = ` </TD>
    <TD STYLE="text-align: center;">
    ` { x e. B | -. ( B \ S ) e. ( M `` x ) } ` </TD>
    <TD> ~ ntrneifv4 , ~ ntrclsfv , ~ clsneifv4 </TD>
  </TR>
  <TR>
    <TH> Closure </TH>
    <TD STYLE="text-align: center;">
    ` { x e. B | -. ( B \ S ) e. ( N `` x ) } ` </TD>
    <TD STYLE="text-align: center;"> ` = ` </TD>
    <TD STYLE="text-align: center;"> ` ( B \ ( I `` ( B \ S ) ) ) ` </TD>
    <TD STYLE="text-align: center;"> ` = ` </TD>
    <TD STYLE="text-align: center;"> ` ( K `` S ) ` </TD>
    <TD STYLE="text-align: center;"> ` = ` </TD>
    <TD STYLE="text-align: center;"> ` { x e. B | S e. ( M `` x ) } ` </TD>
    <TD> ~ clsneifv4 , ~ ntrclsfv , ~ ntrneifv4 </TD>
  </TR>
  <TR>
    <TH> Convergents </TH>
    <TD STYLE="text-align: center;">
    ` { s e. ~P B | -. ( B \ s ) e. ( N `` X ) } ` </TD>
    <TD STYLE="text-align: center;"> ` = ` </TD>
    <TD STYLE="text-align: center;">
    ` { s e. ~P B | -. X e. ( I `` ( B \ s ) ) } ` </TD>
    <TD STYLE="text-align: center;"> ` = ` </TD>
    <TD STYLE="text-align: center;"> ` { s e. ~P B | X e. ( K `` s ) } ` </TD>
    <TD STYLE="text-align: center;"> ` = ` </TD>
    <TD STYLE="text-align: center;"> ` ( M `` X ) ` </TD>
    <TD> ~ neicvgfv , ~ clsneifv3 , ~ ntrneifv3 </TD>
  </TR>
  </TABLE>

  <P>
  We have the following table of equivalences to axioms largely
  established by Kuratowski.  In the formulas in this table, to reduce
  the width of the columns, if any of the variables ` x ` , ` s ` ,
  or ` t ` are used, then they are implicitly universally quantified
  and ` x ` (respectively ` s ` and ` t ` ) ranges
  over ` B ` (respectively ` ~P B ` and ` ~P B ` ).
  </P>

  <!--
  The following table adapted from:

  B&auml;rbel M. R. Stadler, Peter F. Stadler.
    "Basic Properties of Closure Spaces."
    ~ https://www.academia.edu/12565065/Basic_Properties_of_Closure_Spaces

  with variants also in:

  B&auml;rbel M. R. Stadler, Peter F. Stadler.
    "Higher Separation Axioms in Generalized Closure Spaces."
    Comment. Math. Warszawa, Ser. I, 43: 257-273, 2003.
    Preprint: ~ https://www.tbi.univie.ac.at/papers/Abstracts/01-pfs-017.pdf

    Stadler claims that K3 implies KB, but counterexamples
    exist.  A pseudo-closure function of ( x e. ~~P B |-> ( B \ x ) ),
    for nonempty base set, satisfies K0' and K3 but not KB.
    See clsk3nimkb for proof of this counterexample.

    Likewise, K0 is unnecessary to demonstrate KB implies KA.
    See ntrkbimka .
  -->
  <TABLE>
  <TR>
    <TD WIDTH="15%"> Assuming a prefix of: <BR>
     ` A. x e. B A. s e. ~P B A. t e. ~P B ` </TD>
    <TH WIDTH="17%"> Neighborhoods </TH>
    <TH WIDTH="17%"> Interior </TH>
    <TH WIDTH="17%"> Closure </TH>
    <TH WIDTH="17%"> Convergents </TH>
    <TH> Equivalence Theorems </TH>
  </TR>
  <TR>
    <TH> K0' <BR>
    Neighborhoods are nonempty.
    </TH>
    <TD STYLE="text-align: center;">
    ` ( N `` x ) =/= (/) ` </TD>
    <TD STYLE="text-align: center;">
    ` E. u e. ~P B x e. ( I `` u ) ` </TD>
    <TD STYLE="text-align: center;">
    ` E. u e. ~P B -. x e. ( K `` u ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( M `` x ) =/= ~P B ` </TD>
    <TD> ~ ntrclsneine0 , ~ ntrneineine0 , ~ ntrneineine1 </TD>
  </TR>
  <TR>
    <TH> KA' <!-- invented name for the dual of K0' --> <BR>
    No neighborhood is equal to the full powerset. </TH>
    <TD STYLE="text-align: center;">
    ` ( N `` x ) =/= ~P B ` </TD>
    <TD STYLE="text-align: center;">
    ` E. u e. ~P B -. x e. ( I `` u ) ` </TD>
    <TD STYLE="text-align: center;">
    ` E. u e. ~P B x e. ( K `` u ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( M `` x ) =/= (/) ` </TD>
    <TD> ~ ntrclsneine0 , ~ ntrneineine0 , ~ ntrneineine1 </TD>
  </TR>
  <TR>
    <TH> K0 <BR>
    Preservation of the Nullary Union of Closures
    </TH>
    <TD STYLE="text-align: center;">
    ` B e. ( N `` x ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( I `` B ) = B ` </TD>
    <TD STYLE="text-align: center;">
    ` ( K `` (/) ) = (/) ` </TD>
    <TD STYLE="text-align: center;">
    ` -. (/) e. ( M `` x )  ` </TD>
    <TD> ~ ntrclscls00 , ~ ntrneicls00 , ~ ntrneicls11 </TD>
  </TR>
  <TR>
    <TH> KA <BR>
    Preservation of the Nullary Union of Interiors
    </TH>
    <TD STYLE="text-align: center;">
    ` -. (/) e. ( N `` x )  ` </TD>
    <TD STYLE="text-align: center;">
    ` ( I `` (/) ) = (/) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( K `` B ) = B ` </TD>
    <TD STYLE="text-align: center;">
    ` B e. ( M `` x ) ` </TD>
    <TD> ~ ntrclscls00 , ~ ntrneicls00 , ~ ntrneicls11 </TD>
  </TR>
  <TR>
    <TH> K1 <BR>
    Isotonic <BR>
    Montonic
    </TH>
    <TD STYLE="text-align: center;">
    ` ( ( s e. ( N `` x ) /\ s C_ t ) -> t e. ( N `` x ) ) ` </TD>
    <TD STYLE="text-align: center; line-height: 1em;">
    ` ( s C_ t -> ( I `` s ) C_ ( I `` t ) ) ` <BR>
    <SPAN STYLE="color: #AAAAAA;"> &#8212; or &#8212; </SPAN> <BR>
    ` ( ( I `` s ) u. ( I `` t ) ) C_ ( I `` ( s u. t ) ) ` <BR>
    <SPAN STYLE="color: #AAAAAA;"> &#8212; or &#8212; </SPAN> <BR>
    ` ( I `` ( s i^i t ) ) C_ ( ( I `` s ) i^i ( I `` t ) ) ` </TD>
    <TD STYLE="text-align: center; line-height: 1em;">
    ` ( s C_ t -> ( K `` s ) C_ ( K `` t ) ) ` <BR>
    <SPAN STYLE="color: #AAAAAA;"> &#8212; or &#8212; </SPAN> <BR>
    ` ( ( K `` s ) u. ( K `` t ) ) C_ ( K `` ( s u. t ) ) ` <BR>
    <SPAN STYLE="color: #AAAAAA;"> &#8212; or &#8212; </SPAN> <BR>
    ` ( K `` ( s i^i t ) ) C_ ( ( K `` s ) i^i ( K `` t ) ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( ( s e. ( M `` x ) /\ s C_ t ) -> t e. ( M `` x ) ) ` </TD>
    <TD> ~ isotone1 , ~ isotone2 , ~ ntrclsiso , ~ ntrneiiso </TD>
  </TR>
  <TR>
    <TH> K2 <BR>
    Closure is Expansive
    </TH>
    <TD STYLE="text-align: center;">
    ` ( s e. ( N `` x ) -> x e. s ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( I `` s ) C_ s ` </TD>
    <TD STYLE="text-align: center;">
    ` s C_ ( K `` s ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( x e. s -> s e. ( M `` x ) ) ` </TD>
    <TD> ~ ntrclsk2 , ~ ntrneik2 , ~ ntrneix2 </TD>
  </TR>
  <TR>
    <TH> KB <BR>
    Non-disjoint Neighborhoods
    </TH>
    <TD STYLE="text-align: center;">
    ` ( ( s e. ( N `` x ) /\ t e. ( N `` x ) ) `
    ` -> ( s i^i t ) =/= (/) ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( ( s i^i t ) = (/) -> ( ( I `` s ) i^i ( I `` t ) ) = (/) ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( ( s u. t ) = B -> ( ( K `` s ) u. ( K `` t ) ) = B ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( ( s u. t ) = B -> ( s e. ( M `` x ) \/ t e. ( M `` x ) ) ) ` </TD>
    <TD> ~ ntrclskb , ~ ntrneikb , ~ ntrneixb </TD>
  </TR>
  <TR>
    <TH> K3 <BR>
    Closure is Sub-linear
    </TH>
    <TD STYLE="text-align: center;">
    ` ( ( s e. ( N `` x ) /\ t e. ( N `` x ) ) `
         ` -> ( s i^i t ) e. ( N `` x ) ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( ( I `` s ) i^i ( I `` t ) ) C_ ( I `` ( s i^i t ) ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( K `` ( s u. t ) ) C_ ( ( K `` s ) u. ( K `` t ) ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( ( s u. t ) e. ( M `` x ) `
         ` -> ( s e. ( M `` x ) \/ t e. ( M `` x ) ) ) ` </TD>
    <TD> ~ ntrclsk3 , ~ ntrneik3 , ~ ntrneix3 </TD>
  </TR>
  <TR>
    <TH> K13 <BR>
    Closure is finitely linear
    </TH>
    <TD STYLE="text-align: center;">
    ` ( ( s i^i t ) e. ( N `` x ) <-> `
         ` ( s e. ( N `` x ) /\ t e. ( N `` x ) ) ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( I `` ( s i^i t ) ) = ( ( I `` s ) i^i ( I `` t ) ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( K `` ( s u. t ) ) = ( ( K `` s ) u. ( K `` t ) )  ` </TD>
    <TD STYLE="text-align: center;">
    ` ( ( s u. t ) e. ( M `` x ) <-> `
         ` ( s e. ( M `` x ) \/ t e. ( M `` x ) ) ) ` </TD>
    <TD> ~ ntrclsk13 , ~ ntrneik13 , ~ ntrneix13 </TD>
  </TR>
  <TR>
    <TH> K4 <BR>
    Closure is idempotent
    </TH>
    <TD STYLE="text-align: center;">
    ` ( s e. ( N `` x ) <-> E. u e. ( N `` x ) A. y e. B `
         ` ( y e. u <-> s e. ( N `` y ) ) ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( I `` ( I `` s ) ) = ( I `` s ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( K `` ( K `` s ) ) = ( K `` s ) ` </TD>
    <TD STYLE="text-align: center;">
    ` ( s e. ( M `` x ) <-> E. u e. ( M `` x ) A. y e. B `
         ` ( y e. u <-> s e. ( M `` y ) ) ) ` </TD>
    <TD> ~ ntrclsk4 , ~ ntrneik4 </TD>
  </TR>
  <!-- TODO: K5, XF = Every neighborhood is a Filter
           K13 <-> K1 + K3 -->
  </TABLE>

  <P>
    Using these properties as axiomic constraints on the functions,
    certain collections of them give rise to named spaces.
  </P>

  <!--
  The following table adapted from:

  B&auml;rbel M. R. Stadler, Peter F. Stadler.
    "Basic Properties of Closure Spaces."
    ~ https://www.academia.edu/12565065/Basic_Properties_of_Closure_Spaces

  with variants also in:

  B&auml;rbel M. R. Stadler, Peter F. Stadler.
    "Generalized Topological Spaces in Evolutionary Theory and
    Combinatorial Chemistry."
    J. Chem. Inf. Comput. Sci. 2002, 42, 3, 577-585
    ~ https://doi.org/10.1021/ci0100898
  -->

  <TABLE>
  <TR>
    <TH>Space</TH>
    <TH>Foundational Axioms</TH>
    <TH>Derived Axioms</TH>
    <TH>Theorems</TH>
  </TR>
  <TR>
    <!--
        &Aacute;. Cs&aacute;z&aacute;r.
            "Generalized topology, Generalized continuity."
            Acta. Math. Hungar. 96: 351-357, 2002.
    -->
    <TD> Cs&aacute;z&aacute;r Generalized Neighborhood Space </TD>
    <TD> K2 </TD>
    <TD> KA', KA, KB </TD>
    <TD> ~ ntrk2imkb , ~ ntrkbimka , ~ neik0imk0p </TD>
  </TR>
  <TR>
    <!--
        Won Keun Min.
            "Results on Strong Generalized Neighborhood Spaces."
            J. Korea Soc. Math. Educ. Ser. B: Pure Appl. Math.
            15(3): 221-227, August 2008.
    -->
    <TD> <!-- Won Keun --> Min
    Strong Generalized Neighborhood Space </TD>
    <TD> K2, K3 </TD>
    <TD> KA', KA, KB </TD>
    <TD> ~ ntrk2imkb , ~ ntrkbimka , ~ neik0imk0p </TD>
  </TR>
  <TR>
    <!--
        S. Gni&lstrok;ka.
            "On extended topologies. I: Closure operators."
            Ann. Soc. Math. Pol. Ser. I, Commentat. Math. 34:81-94, 1994.

        S. Gni&lstrok;ka.
            "On extended topologies. II: Compactness, quasi-metrizability,
            symmetry." Ann. Soc. Math. Pol. Ser. I, Commentat. Math.
            35:99-108, 1997.
    -->
    <TD> Gni&lstrok;ka Extended Topology</TD>
    <TD> K0', K1 </TD>
    <TD> K0 </TD>
    <TD> ~ neik0pk1imk0 </TD>
  </TR>
  <TR>
    <!--
        M. M. Brissaud. "Les espaces pr&eacute;topologiques."
        C. R. Acad. Sc. Paris Ser. A 280:705-708, 1975.
    -->
    <TD> Brissaud Space </TD>
    <TD> K0, K2 </TD>
    <TD> K0', KA', KA, KB </TD>
    <TD> ~ neik0imk0p , ~ ntrk2imkb , ~ ntrkbimka </TD>
  </TR>
  <TR>
    <TD> Neighborhood Space </TD>
    <TD> K0', K1, K2 </TD>
    <TD> K0, KA', KA, KB </TD>
    <TD> ~ neik0pk1imk0 , ~ ntrk2imkb , ~ ntrkbimka , ~ neik0imk0p </TD>
  </TR>
  <TR>
    <!-- Appears to be a reference to

        B. A. Davey, H. A. Priestley.
        "Introduction to Lattices and Order."
        Cambridge University Press, 2002. p. 48.

        where the pseudo-closure is:
        ( s e. ~~P B |-> |^| { t e. C | s C_ t } )
        where C is presumably a subset of ~~P B
        such that every nonempty subset has its intersection in C .
    -->
    <TD> Davey and Priestley Intersection Structure </TD>
    <TD> K1, K4 </TD>
    <TD> </TD>
    <TD> </TD>
  </TR>
  <TR>
    <TD> Moore Closure Space </TD>
    <TD> K1, K2, K4 </TD>
    <TD> KA', KA, KB </TD>
    <TD> ~ ntrk2imkb , ~ ntrkbimka , ~ neik0imk0p </TD>
  </TR>
  <TR>
    <!--
        W. P. Soltan.
        "An Introduction in Axiomatic Theory of Convexity."
        Shtiintsa, Kishinev, 1984.  Russian.
    -->
    <TD> Convex Closure Space </TD>
    <TD> K0', K1, K2, K4 </TD>
    <TD> K0, KA', KA, KB </TD>
    <TD> ~ neik0pk1imk0 , ~ ntrk2imkb , ~ ntrkbimka , ~ neik0imk0p </TD>
  </TR>
  <TR>
    <!--
        M. B. Smyth. "Semi-metric, closure spaces and digital topology."
        Theor. Computer Sci. 151: 257-276, 1995.
    -->
    <TD> Smyth Neighborhood Space </TD>
    <TD> K0', K13 </TD>
    <TD> K0, K1, K3  </TD>
    <TD> ~ neik0pk1imk0 , ~ ntrk1k3eqk13 </TD>
  </TR>
  <TR>
    <TD> &Ccaron;ech Closure Space <BR>
    Pretopological Space </TD>
    <TD> K0', K2, K13 </TD>
    <TD> K0, K1, KA', KA, KB, K3 </TD>
    <TD> ~ neik0pk1imk0 , ~ ntrk2imkb , ~ ntrkbimka ,
         ~ neik0imk0p , ~ ntrk1k3eqk13 </TD>
  </TR>
  <TR>
    <TD> Topological Space </TD>
    <TD> K0', K2, K13, K4 </TD>
    <TD> K0, K1, KA', KA, KB, K3 </TD>
    <TD> ~ neik0pk1imk0 , ~ ntrk2imkb , ~ ntrkbimka ,
         ~ neik0imk0p , ~ ntrk1k3eqk13 </TD>
  </TR>
  <TR>
    <!--
        P. Alexandroff. "Diskrete R&auml;ume."
        Math. Sb. (N.S.) 2: 501-518, 1937.

        R. E. Strong.  "Finite Topological Spaces."
        Trans. Amer. Math. Soc. 123: 325-340, 1966.

        F. G. Arenas. "Alexandroff Spaces."
        Acta Math. Univ. Comenianae.  68: 17-25, 1999.
    -->
    <TD> Alexandroff Space </TD>
    <TD> K0', K2, K5 </TD>
    <TD> K0, K1, KA', KA, KB, K3, K13 </TD>
    <TD> ~ neik0pk1imk0 , ~ ntrk2imkb , ~ ntrkbimka ,
         ~ neik0imk0p , ~ ntrk1k3eqk13 ,
         TBD <!-- AND K5 -> K1 + K3 --> </TD>
  </TR>
  <TR>
    <TD> Alexandroff Topological Space </TD>
    <TD> K0', K2, K4, K5 </TD>
    <TD> K0, K1, KA', KA, KB, K3, K13 </TD>
    <TD> ~ neik0pk1imk0 , ~ ntrk2imkb , ~ ntrkbimka ,
         ~ neik0imk0p , ~ ntrk1k3eqk13 ,
         TBD </TD>
  </TR>
  </TABLE>

  </HTML>

$)

  $( rename sscon34b to rcomplss ?? $)

  $( Decompose disjunction into three cases.  (Contributed by RP,
     5-Jul-2021.) $)
  or3or $p |- ( ( ph \/ ps ) <-> ( ( ph /\ ps ) \/ ( ph /\ -. ps )
                             \/ ( -. ph /\ ps ) ) ) $=
    ( wa wxo wo wn w3o excxor orbi2i wb orc exmid pm3.2 wi biimp sylib con2i ex
    iman biorf df-xor bicomi imbitrdi orim12d bicom bibif bitrid con2bid bitrdi
    mpi 2thd simpl nsyl5 3bitr3d pm2.61i 3orass 3bitr4i ) ABCZABDZEZURABFZCZAFZ
    BCZEZEABEZURVBVDGUSVEURABHIAVFUTJAVFUTABKABVAEUTBLABURVAUSABMAVAABJZFZUSAVA
    VHVGVBVGABNVBFABOABSPQRUSVHABUAUBZUCUDUJUKVCBUSVFUTVCBVHUSVCVGBVGBAJVCVAABU
    EBAUFUGUHVIUIABTURAUSUTJABULURUSTUMUNUOURVBVDUPUQ $.

  $( Distribute over triple disjunction.  (Contributed by RP, 5-Jul-2021.) $)
  andi3or $p |- ( ( ph /\ ( ps \/ ch \/ th ) ) <-> ( ( ph /\ ps )
                                         \/ ( ph /\ ch ) \/ ( ph /\ th ) ) ) $=
    ( wo wa w3o andi orbi1i bitri df-3or anbi2i 3bitr4i ) ABCEZDEZFZABFZACFZEZA
    DFZEZABCDGZFQRTGPANFZTEUAANDHUCSTABCHIJUBOABCDKLQRTKM $.

  $( If a union of classes is equal to a singleton then at least one class is
     equal to the singleton while the other may be equal to the empty set.
     (Contributed by RP, 5-Jul-2021.) $)
  uneqsn $p |- ( ( A u. B ) = { C } <-> ( ( A = { C } /\ B = { C } )
                 \/ ( A = { C } /\ B = (/) ) \/ ( A = (/) /\ B = { C } ) ) ) $=
    ( cvv wcel wceq wa c0 w3o wb wss wo a1i bicomi snssg orbi12d anbi12d bitrid
    eqss wn cun csn unss elun bitr2id bitr2d or3or anbi2i andi3or bitri anbi12i
    an4 sssn anbi1d andir n0i biimtrrdi con2d pm4.71d eqimss2 iman mpbi biorfri
    wi bitr2di bitrd 3orbi123d 3bitrd snprc biimpi eqeq2d pm4.25 orbi1i bitr4id
    anbi2d un00 df-3or 3bitr4g pm2.61i ) CDEZABUAZCUBZFZAWBFZBWBFZGZWDBHFZGZAHF
    ZWEGZIZJVTWCWAWBKZWBWAKZGZAWBKZBWBKZGZWBAKZWBBKZLZGZWKWCWNJVTWAWBSMVTWLWQWM
    WTWLWQJVTWQWLABWBUCNMVTWTCWAEZWMXBCAEZCBEZLVTWTCABUDVTXCWRXDWSCADOZCBDOZPUE
    CWADOUFQXAWQWRWSGZGZWQWRWSTZGZGZWQWRTZWSGZGZIZVTWKXAWQXGXJXMIZGXOWTXPWQWRWS
    UGUHWQXGXJXMUIUJVTXHWFXKWHXNWJXHWFJVTXHWOWRGZWPWSGZGZWFWOWPWRWSULWFXSWDXQWE
    XRAWBSZBWBSZUKNUJMXKXQWPXIGZGVTWHWOWPWRXIULVTXQWDYBWGXQWDJVTWDXQXTNMVTYBWGW
    ELZXIGZWGVTWPYCXIWPYCJVTBCUMMUNYDWGXIGZWEXIGZLZVTWGWGWEXIUOVTWGYEYGVTWGXIVT
    WSWGVTWSXDWGTXFBCUPUQURUSYFYEWEWSVDYFTWBBUTWEWSVAVBVCVERVFQRXNWOXLGZXRGVTWJ
    WOWPXLWSULVTYHWIXRWEVTYHWIWDLZXLGZWIVTWOYIXLWOYIJVTACUMMUNYJWIXLGZWDXLGZLZV
    TWIWIWDXLUOVTWIYKYMVTWIXLVTWRWIVTWRXCWITXEACUPUQURUSYLYKWDWRVDYLTWBAUTWDWRV
    AVBVCVERVFXRWEJVTWEXRYANMQRVGRVHVTTZWCWAHFZWKYNWBHWAYNWBHFCVIVJZVKYNWIWGGZW
    FWHLZWJLZYOWKYNYQYQYQLZYQLZYSYQYTUUAYQVLZYQYTYQUUBVMUJYNYRYTWJYQYNWFYQWHYQY
    NWDWIWEWGYNWBHAYPVKZYNWBHBYPVKZQYNWDWIWGUUCUNPYNWEWGWIUUDVOPVNYQYOABVPNWFWH
    WJVQVRVFVS $.

  ${
    brfvimex.br $e |- ( ph -> A R B ) $.
    brfvimex.fv $e |- ( ph -> R = ( F ` C ) ) $.
    $( If a binary relation holds and the relation is the value of a function,
       then the argument to that function is a set.  (Contributed by RP,
       22-May-2021.) $)
    brfvimex $p |- ( ph -> C e. _V ) $=
      ( cfv wbr c0 wne cvv wcel breqdi brne0 fvprc necon1ai 3syl ) ABCDFIZJTKLD
      MNZAETBCHGOBCTPUATKDFQRS $.
  $}

  ${
    $d E x y $.  $d F y $.
    brovmptimex.mpt $e |- F = ( x e. E , y e. G |-> H ) $.
    brovmptimex.br $e |- ( ph -> A R B ) $.
    brovmptimex.ov $e |- ( ph -> R = ( C F D ) ) $.
    $( If a binary relation holds and the relation is the value of a binary
       operation built with maps-to, then the arguments to that operation are
       sets.  (Contributed by RP, 22-May-2021.) $)
    brovmptimex $p |- ( ph -> ( C e. _V /\ D e. _V ) ) $=
      ( co wbr c0 cvv wcel wne wa breqdi brne0 reldmmpo ovprc necon1ai 3syl ) A
      DEFGJPZQUIRUAFSTGSTUBZAHUIDEONUCDEUIUDUJUIRFGJBCIKLJMUEUFUGUH $.

    $( If a binary relation holds and the relation is the value of a binary
       operation built with maps-to, then the arguments to that operation are
       sets.  (Contributed by RP, 22-May-2021.) $)
    brovmptimex1 $p |- ( ph -> C e. _V ) $=
      ( cvv wcel brovmptimex simpld ) AFPQGPQABCDEFGHIJKLMNORS $.

    $( If a binary relation holds and the relation is the value of a binary
       operation built with maps-to, then the arguments to that operation are
       sets.  (Contributed by RP, 22-May-2021.) $)
    brovmptimex2 $p |- ( ph -> D e. _V ) $=
      ( cvv wcel brovmptimex simprd ) AFPQGPQABCDEFGHIJKLMNORS $.
  $}

  ${
    brcoffn.c $e |- ( ph -> C Fn Y ) $.
    brcoffn.d $e |- ( ph -> D : X --> Y ) $.
    brcoffn.r $e |- ( ph -> A ( C o. D ) B ) $.
    $( Conditions allowing the decomposition of a binary relation.
       (Contributed by RP, 7-Jun-2021.) $)
    brcoffn $p |- ( ph -> ( A D ( D ` A ) /\ ( D ` A ) C B ) ) $=
      ( wfn wcel cfv wbr wa syl2anc wceq 3ad2ant1 wb fnbrfvb w3a wf fnfco simpl
      ccom simpr syl fnbr 3jca mpdan simp3 fvco3 3adant1 mpbird eqid jctil ffnd
      eqtr3d ffvelcdmd anbi12d mpbid ) AADEUEZFKZBFLZUAZBBEMZENZVFCDNZOZAVCVEAD
      GKZFGEUBZVCHIGFDEUCPAVCOZAVCVDAVCUDZAVCUFZVLVCBCVBNZVDVNVLAVOVMJUGFBCVBUH
      PUIUJVEVFVFQZVFDMZCQZOVIVEVRVPVEBVBMZVQCVEVKVDVSVQQAVCVKVDIRZAVCVDUKZFGBD
      EULPVEVSCQZVOAVCVOVDJRVCVDWBVOSAFBCVBTUMUNURVFUOUPVEVPVGVRVHVEEFKVDVPVGSV
      EFGEVTUQWAFBVFETPVEVJVFGLVRVHSAVCVJVDHRVEFGBEVTWAUSGVFCDTPUTVAUG $.
  $}

  ${
    brcofffn.c $e |- ( ph -> C Fn Z ) $.
    brcofffn.d $e |- ( ph -> D : Y --> Z ) $.
    brcofffn.e $e |- ( ph -> E : X --> Y ) $.
    brcofffn.r $e |- ( ph -> A ( C o. ( D o. E ) ) B ) $.
    $( Conditions allowing the decomposition of a binary relation.
       (Contributed by RP, 8-Jun-2021.) $)
    brcofffn $p |- ( ph -> ( A E ( E ` A )
                          /\ ( E ` A ) D ( D ` ( E ` A ) )
                          /\ ( D ` ( E ` A ) ) C B ) ) $=
      ( cfv wbr ccom wa wfn brcoffn adantr w3a fnfco syl2anc coass breqi sylibr
      wf simprr ex jcai simpll simprl 3jca syl ) ABBFNZFOZUOCDEPZOZQZUOUOENZEOZ
      UTCDOZQZQZUPVAVBUAAUSVCABCUQFGHADIRZHIEUGZUQHRJKIHDEUBUCLABCDEFPPZOBCUQFP
      ZOMBCVHVGDEFUDUEUFSAUSVCAUSQUOCDEHIAVEUSJTAVFUSKTAUPURUHSUIUJVDUPVAVBUPUR
      VCUKUSVAVBULUSVAVBUHUMUN $.
  $}

  ${
    brco2f1o.c $e |- ( ph -> C : Y -1-1-onto-> Z ) $.
    brco2f1o.d $e |- ( ph -> D : X -1-1-onto-> Y ) $.
    brco2f1o.r $e |- ( ph -> A ( C o. D ) B ) $.
    $( Conditions allowing the decomposition of a binary relation.
       (Contributed by RP, 8-Jun-2021.) $)
    brco2f1o $p |- ( ph -> ( ( `' C ` B ) C B
                                   /\ A D ( `' C ` B ) ) ) $=
      ( ccnv wbr wa wf1o f1ocnv 3syl ccom wrel wb cfv f1ofn f1of relco relbrcnv
      wfn wf cnvco breqi bitr3i sylib brcoffn f1orel relbrcnvg anbi12d mpbid )
      ACCDLZUAZUQMZURBELZMZNURCDMZBUREMZNACBUTUQHGAFGEOZGFUTOUTGUFJFGEPGFUTUBQA
      GHDOZHGUQOHGUQUGIGHDPHGUQUCQABCDERZMZCBUTUQRZMZKVGCBVFLZMVICBVFDEUDUECBVJ
      VHDEUHUIUJUKULAUSVBVAVCAVEDSUSVBTIGHDUMCURDUNQAVDESVAVCTJFGEUMURBEUNQUOUP
      $.
  $}

  ${
    brco3f1o.c $e |- ( ph -> C : Y -1-1-onto-> Z ) $.
    brco3f1o.d $e |- ( ph -> D : X -1-1-onto-> Y ) $.
    brco3f1o.e $e |- ( ph -> E : W -1-1-onto-> X ) $.
    brco3f1o.r $e |- ( ph -> A ( C o. ( D o. E ) ) B ) $.
    $( Conditions allowing the decomposition of a binary relation.
       (Contributed by RP, 8-Jun-2021.) $)
    brco3f1o $p |- ( ph -> ( ( `' C ` B ) C B
               /\ ( `' D ` ( `' C ` B ) ) D ( `' C ` B )
               /\ A E ( `' D ` ( `' C ` B ) ) ) ) $=
      ( ccnv wbr wf1o f1ocnv 3syl ccom cfv w3a wfn f1ofn wf f1of relco relbrcnv
      cnvco coeq2i eqtri breqi coass 3bitr3ri brcofffn wrel wb f1orel relbrcnvg
      sylib 3anbi123d mpbid ) ACCDOZUAZVCPZVDVDEOZUAZVFPZVGBFOZPZUBVDCDPZVGVDEP
      ZBVGFPZUBACBVIVFVCJIHAGHFQZHGVIQVIHUCMGHFRHGVIUDSAHIEQZIHVFQIHVFUELHIERIH
      VFUFSAIJDQZJIVCQJIVCUEKIJDRJIVCUFSABCDEFTTZPZCBVIVFVCTZTZPZNCBDETZFTZOZPB
      CWCPWAVRCBWCWBFUGUHCBWDVTWDVIWBOZTVTWBFUIWEVSVIDEUIUJUKULBCWCVQDEFUMULUNU
      TUOAVEVKVHVLVJVMAVPDUPVEVKUQKIJDURCVDDUSSAVOEUPVHVLUQLHIEURVDVGEUSSAVNFUP
      VJVMUQMGHFURVGBFUSSVAVB $.
  $}

  ${
    ntrclsbex.d $e |- D = ( O ` B ) $.
    ntrclsbex.r $e |- ( ph -> I D K ) $.
    $( If (pseudo-)interior and (pseudo-)closure functions are related by the
       duality operator then the base set exists.  (Contributed by RP,
       21-May-2021.) $)
    ntrclsbex $p |- ( ph -> B e. _V ) $=
      ( cfv wceq a1i brfvimex ) ADEBCFHCBFIJAGKL $.

    $( The relative complement of the class ` S ` exists as a subset of the
       base set.  (Contributed by RP, 25-Jun-2021.) $)
    ntrclsrcomplex $p |- ( ph -> ( B \ S ) e. ~P B ) $=
      ( cdif cvv ntrclsbex difssd sselpwd ) ABDJBKABCEFGHILABDMN $.
  $}

  $( Kuratowski's K0 axiom implies K0'.  Neighborhood version.  Also a proof
     the dual KA axiom implies KA' when considering the convergents.
     (Contributed by RP, 28-Jun-2021.) $)
  neik0imk0p $p |- ( A. x e. B B e. ( N ` x )
                  -> A. x e. B ( N ` x ) =/= (/) ) $=
    ( cv cfv wcel c0 wne ne0i ralimi ) BADCEZFKGHABKBIJ $.

  ${
    $d B s t $.  $d I s t $.
    $( If an interior function is contracting, the interiors of disjoint sets
       are disjoint.  Kuratowski's K2 axiom implies KB. Interior version.
       (Contributed by RP, 9-Jun-2021.) $)
    ntrk2imkb $p |- ( A. s e. ~P B ( I ` s ) C_ s
                   -> A. s e. ~P B A. t e. ~P B ( ( s i^i t ) = (/)
                               -> ( ( I ` s ) i^i ( I ` t ) ) = (/) ) ) $=
      ( cv cfv wss cpw wral wa cin c0 wceq wi id weq fveq2 sseq12d cbvralvw syl
      biimpi raaanv sylanbrc ss2in adantr simpr sseqtrd ss0 ex 2ralimi ) DEZCFZ
      UKGZDBHZIZUMAEZCFZUPGZJZAUNIDUNIZUKUPKZLMZULUQKZLMZNZAUNIDUNIUOUOURAUNIZU
      TUOOUOVFUMURDAUNDAPZULUQUKUPUKUPCQVGORSUAUMURDAUNUBUCUSVEDAUNUNUSVBVDUSVB
      JZVCLGVDVHVCVALUSVCVAGVBULUKUQUPUDUEUSVBUFUGVCUHTUIUJT $.
  $}

  ${
    $d B s t $.  $d I s t $.
    $( If the interiors of disjoint sets are disjoint, then the interior of the
       empty set is the empty set.  (Contributed by RP, 14-Jun-2021.) $)
    ntrkbimka $p |- ( A. s e. ~P B A. t e. ~P B ( ( s i^i t ) = (/)
                      -> ( ( I ` s ) i^i ( I ` t ) ) = (/) )
                      -> ( I ` (/) ) = (/) ) $=
      ( cv cin c0 wceq cfv cpw wral inidm wcel 0elpw ineq1 eqeq1d fveq2 imbi12d
      wi ineq1d wb 0in pm5.5 ax-mp bitrdi ineq2d rspc2v mp2an eqtr3id ) DEZAEZF
      ZGHZUJCIZUKCIZFZGHZSZABJZKDUSKZGCIZVAVAFZGVALGUSMZVCUTVBGHZSBNZVEURVDVAUO
      FZGHZDAGGUSUSUJGHZURGUKFZGHZVGSZVGVHUMVJUQVGVHULVIGUJGUKOPVHUPVFGVHUNVAUO
      UJGCQTPRVJVKVGUAUKUBVJVGUCUDUEUKGHZVFVBGVLUOVAVAUKGCQUFPUGUHUI $.
  $}

  ${
    $d B s t $.  $d I s t $.
    $( If the interiors of disjoint sets are disjoint and the interior of the
       base set is the base set, then the interior of the empty set is the
       empty set.  Obsolete version of ~ ntrkbimka .  (Contributed by RP,
       12-Jun-2021.) $)
    ntrk0kbimka $p |- ( ( B e. V /\ I e. ( ~P B ^m ~P B ) )
                      -> ( ( ( I ` B ) = B
                      /\ A. s e. ~P B A. t e. ~P B ( ( s i^i t ) = (/)
                      -> ( ( I ` s ) i^i ( I ` t ) ) = (/) ) )
                      -> ( I ` (/) ) = (/) ) ) $=
      ( wcel wa cfv wceq cv cin c0 wi wral a1i ineq1 eqeq1d fveq2 imbi12d wss
      cpw cmap co pwidg ad2antrr 0elpw simprr ineq1d ineq2 ineq2d wb pm5.5 mp1i
      in0 bitrd rspc2va syl21anc ex elmapi adantl ffvelcdmd elpwid simpl eqtrdi
      wf incom biimpd cdif reldisj difid sseq2i sylbi syl6com com13 syl2im mpdd
      ss0 ) BDFZCBUAZVSUBUCFZGZBCHZBIZEJZAJZKZLIZWDCHZWECHZKZLIZMZAVSNEVSNZGZWB
      LCHZKZLIZWOLIZWAWNWQWAWNGZBVSFZLVSFZWMWQVRWTVTWNBDUDUEXAWSBUFZOWAWCWMUGWL
      WQBWEKZLIZWBWIKZLIZMZEABLVSVSWDBIZWGXDWKXFXHWFXCLWDBWEPQXHWJXELXHWHWBWIWD
      BCRUHQSWELIZXGBLKZLIZWQMZWQXIXDXKXFWQXIXCXJLWELBUIQXIXEWPLXIWIWOWBWELCRUJ
      QSXKXLWQUKXIBUNXKWQULUMUOUPUQURWAWOBTZWNWCWQWRMWAWOBWAVSVSLCVTVSVSCVEVRCV
      SVSUSUTXAWAXBOVAVBWCWMVCWQWCXMWRWCWQWOBKZLIZXMWRMWCWQXOWCWPXNLWCWPBWOKXNW
      BBWOPBWOVFVDQVGXMXOWOBBVHZTZWRXMXOXQWOBBVIVGXQWOLTWRXPLWOBVJVKWOVQVLVMVMV
      NVOVP $.
  $}

  ${
    $d b k t s x z $.
    $( If the base set is not empty, axiom K3 does not imply KB. A concrete
       example with a pseudo-closure function of
       ` k = ( x e. ~P b |-> ( b \ x ) ) ` is given.  (Contributed by RP,
       16-Jun-2021.) $)
    clsk3nimkb $p |- -. A. b A. k e. ( ~P b ^m ~P b ) ( A. s e. ~P b
                     A. t e. ~P b ( k ` ( s u. t ) )
                     C_ ( ( k ` s ) u. ( k ` t ) ) -> A. s e. ~P b
                     A. t e. ~P b ( ( s u. t ) = b ->
                     ( ( k ` s ) u. ( k ` t ) ) = b ) ) $=
      ( vx vz cv cun wss wral wceq wi wn wa wrex cvv c0 cdif c1o wcel cmap 1oex
      cfv cpw co wal csn wex wne 1n0 nelsn ax-mp eldif ne0i sylbir r19.2zb mpbi
      mp2an rexex rexanali exbii exnal sylbb 3syl cmpt wf difelpw adantr fmpttd
      cin pwexg elmapd mpbird simpllr difeq2 cbvmptv eqtrdi adantl simplr simpr
      simplll elpwid sselpwd vex difexi a1i weq uneq12d difindi eqtr4di sseq12d
      unssd fvmptd ralbidva eqeq1d imbi2d notbid anbi12d pwidg ssidd eldifsnneq
      uneq1 ssequn2 bitr4di ineq1 difeq2d sseq1 ineq2 inidm difid eqcom rspc2ev
      bitrdi syl112anc rexbii rexnal syl inss1 ssun1 sstri sscon jctil rspcedvd
      rgen2w mprg ) CGZAGZHZBGZUCZYFYIUCZYGYIUCZHZIZADGZUDZJZCYPJZYHYOKZYMYOKZL
      ZAYPJZCYPJZMZNZBYPYPUAUEZOZYRUUCLBUUFJZDUFMZDPQUGZRZUUGDUUKJZUUGDUUKOZUUG
      DUHZUUIUUKQUIZUULUUMLSPTZSUUJTMZUUOUBSQUIUUQUJSQUKULUUPUUQNSUUKTUUOSPUUJU
      MUUKSUNUOURUUGDUUKUPUQUUGDUUKUSUUNUUHMZDUHUUIUUGUURDYRUUCBUUFUTVAUUHDVBVC
      VDYOUUKTZUUEYOYHRZYOYFYGVJZRZIZAYPJZCYPJZYSUVBYOKZLZAYPJZCYPJZMZNBEYPYOEG
      ZRZVEZUUFUUSUVMUUFTYPYPUVMVFUUSEYPUVLYPUUSUVLYPTUVKYPTYOUVKUUKVGVHVIUUSYP
      YPUVMPPYOUUKVKZUVNVLVMUUSYIUVMKZNZYRUVEUUDUVJUVPYQUVDCYPUVPYFYPTZNZYNUVCA
      YPUVRYGYPTZNZYJUUTYMUVBUVTFYHYOFGZRZUUTYPYIPUVTYIUVMFYPUWBVEUUSUVOUVQUVSV
      NEFYPUVLUWBUVKUWAYOVOVPVQZUWAYHKUWBUUTKUVTUWAYHYOVOVRUVTYHYOUUKUUSUVOUVQU
      VSWAUVTYFYGYOUVTYFYOUVPUVQUVSVSZWBUVTYGYOUVRUVSVTZWBWLWCUUTPTUVTYOYHDWDZW
      EWFWMUVTYMYOYFRZYOYGRZHUVBUVTYKUWGYLUWHUVTFYFUWBUWGYPYIPUWCFCWGUWBUWGKUVT
      UWAYFYOVOVRUWDUWGPTUVTYOYFUWFWEWFWMUVTFYGUWBUWHYPYIPUWCFAWGUWBUWHKUVTUWAY
      GYOVOVRUWEUWHPTUVTYOYGUWFWEWFWMWHYOYFYGWIWJZWKWNWNUVPUUCUVIUVPUUBUVHCYPUV
      RUUAUVGAYPUVTYTUVFYSUVTYMUVBYOUWIWOWPWNWNWQWRUUSUVJUVEUUSYSUVFMZNZAYPOZCY
      POZUVJUUSYOYPTZUWNYOYOIZYOQKZMZUWMYOUUKWSZUWRUUSYOWTYOPQXAUWKUWOUWQNYGYOI
      ZYOYOYGVJZRZYOKZMZNCAYOYOYPYPCDWGZYSUWSUWJUXCUXDYSYOYGHZYOKUWSUXDYHUXEYOY
      FYOYGXBWOYGYOXCXDUXDUVFUXBUXDUVBUXAYOUXDUVAUWTYOYFYOYGXEXFWOWQWRADWGZUWSU
      WOUXCUWQYGYOYOXGUXFUXBUWPUXFUXBQYOKUWPUXFUXAQYOUXFUXAYOYORQUXFUWTYOYOUXFU
      WTYOYOVJYOYGYOYOXHYOXIVQXFYOXJVQWOQYOXKXMWQWRXLXNUWMUVHMZCYPOUVJUWLUXGCYP
      YSUVFAYPUTXOUVHCYPXPVCXQUVCCAYPYPUVAYHIUVCUVAYFYHYFYGXRYFYGXSXTUVAYHYOYAU
      LYDYBYCYE $.
  $}

  ${
    clsk1indlem.k $e |- K = ( r e. ~P 3o |->
                              if ( r = { (/) } , { (/) , 1o } , r ) ) $.
    $( The ansatz closure function
       ` ( r e. ~P 3o |-> if ( r = { (/) } , { (/) , 1o } , r ) ) ` has the K0
       property of preserving the nullary union.  (Contributed by RP,
       6-Jul-2021.) $)
    clsk1indlem0 $p |- ( K ` (/) ) = (/) $=
      ( c0 c3o cpw wcel cfv wceq 0elpw cv csn c1o cpr cif eqeq1 id ifbieq2d wne
      0nep0 a1i neneqd iffalsed eqtrd 0ex fvmpt ax-mp ) DEFZGDAHDIEJBDBKZDLZIZD
      MNZUIOZDUHAUIDIZUMDUJIZULDODUNUKUOUIDULUIDUJPUNQRUNUOULDUNDUJDUJSUNTUAUBU
      CUDCUEUFUG $.

    ${
      $d s r $.
      $( The ansatz closure function
         ` ( r e. ~P 3o |-> if ( r = { (/) } , { (/) , 1o } , r ) ) ` has the
         K2 property of expanding.  (Contributed by RP, 6-Jul-2021.) $)
      clsk1indlem2 $p |- A. s e. ~P 3o s C_ ( K ` s ) $=
        ( cv cfv wss c3o cpw wcel c0 csn wceq c1o cpr cif wa wn id sseq2 wo a1i
        snsspr1 eqsstrdi ancli con3i ssid jctir orri elimif sylibr weq ifbieq2d
        eqeq1 prex vex ifex fvmpt sseqtrrd rgen ) BEZVAAFZGBHIZVAVCJZVAVAKLZMZK
        NOZVAPZVBVDVFVAVGGZQZVFRZVAVAGZQZUAZVAVHGZVNVDVJVMVJRVKVLVFVJVFVIVFVAVE
        VGVFSKNUCUDUEUFVAUGUHUIUBVFVOVIVLVGVAVHVGVATVHVAVATUJUKCVACEZVEMZVGVPPV
        HVCACBULZVQVFVPVAVGVPVAVEUNVRSUMDVFVGVAKNUOBUPUQURUSUT $.
    $}

    ${
      $d r s t $.  $d x s t $.
      $( The ansatz closure function
         ` ( r e. ~P 3o |-> if ( r = { (/) } , { (/) , 1o } , r ) ) ` has the
         K3 property of being sub-linear.  (Contributed by RP, 6-Jul-2021.) $)
      clsk1indlem3 $p |- A. s e. ~P 3o A. t e. ~P 3o
                            ( K ` ( s u. t ) ) C_ ( ( K ` s ) u. ( K ` t ) ) $=
        ( vx cv cun wcel wa c0 wceq cif wo wi ex a1i adantrd adantl id cfv elif
        wss c3o cpw csn c1o cpr wn wel uneq12 unidm eqtrdi an3 orcd pm2.24 impd
        jaao mpdan uneqsn df-3or bitri pm2.21 jaod adantr adantld biimtrid elun
        w3o bilani andi simpl anim1i simpr orim12i sylbi sylan2 olcd or4 expcom
        sylib orc snsspr1 eqsstrdi sseld impcom jca olc jaoa jaoi orim12d com12
        anc2li or42 imbitrdi 4exmid mpjaod orbi12i sylbbr ssrdv pwuncl ifbieq2d
        syl6 eqeq1 prex vex unex ifex fvmpt syl weq uneq12d 3sstr4d rgen2 ) CGZ
        AGZHZBUAZXOBUAZXPBUAZHZUCCAUDUEZYBXOYBIZXPYBIZJZXQKUFZLZKUGUHZXQMZXOYFL
        ZYHXOMZXPYFLZYHXPMZHZXRYAYEFYIYNYEFGZYIIZYJYOYHIZJZYJUIZFCUJZJZNZYLYQJZ
        YLUIZFAUJZJZNZNZYOYNIZYPYGYQJZYGUIZYOXQIZJZNZYEUUHYGYOYHXQUBYEYJYLJZYSU
        UDJZNZUUNUUHOZYJUUDJZYLYSJZNZYEUUOUURUUPUUOUUROYEUUOYGUURUUOXQYFYFHYFXO
        YFXPYFUKYFULUMUUOUUJUUHYGUUMUUOUUJUUHUUOUUJJZUUBUUGUVBYRUUAYJYLYGYQUNUO
        UOPYGUUKUULUUHYGUULUUHOUPUQURUSQUUPUUROYEUUPUUJUUHUUMUUPYGYQUUHYGUUOYJX
        PKLZJZNZXOKLZYLJZNZUUPYQUUHOZYGUUOUVDUVGVIUVHXOXPKUTUUOUVDUVGVAVBUUPUVE
        UVIUVGYSUVEUVIOUUDYSUUOUVIUVDYSYJUVIYLYJUVIVCZRYSYJUVIUVCUVJRVDVEUUPYLU
        VIUVFUUDYLUVIOYSYLUVIVCSVFVDVGUQUUPUUMUUHUUPUUMJZYRUUCNZUUAUUFNZNUUHUVK
        UVMUVLUUMUUPYTUUENZUVMUULUVNUUKYOXOXPVHZVJUUPUVNJUUPYTJZUUPUUEJZNUVMUUP
        YTUUEVKUVPUUAUVQUUFUUPYSYTYSUUDVLVMUUPUUDUUEYSUUDVNVMVOVPVQVRYRUUCUUAUU
        FVSWAPVDQVDUVAUUROYEUVAUUNYRUUFNZUUAUUCNZNZUUHUUNUVAUVTUUNUUSUVRUUTUVSU
        UJUUSUVROZUUMYQUWAYGYQYJUVRUUDYJYQUVRYRUUFWBVTRSUULUWAUUKUULUVNUWAUVOYT
        YJUVRUUEUUDYTYJUVRYTYJJZYRUUFUWBYJYQYTYJVNYJYTYQYJXOYHYOYJXOYFYHYJTKUGW
        CZWDWEWFWGUOPUUDUUEUVRUUFYRWHVTWIVPSWJUUJUUTUVSOZUUMUUJYLUVSYSYQYLUVSOY
        GYLYQUVSUUCUUAWHVTSRUULUWDUUKUULUVNUWDUVOUUTUVNUVSUUTYTUUAUUEUUCYSYTUUA
        OYLYSYTUUAUUATPSYLUUEUUCOYSYLUUEYQYLXPYHYOYLXPYFYHYLTUWCWDWEWMVEWKWLVPS
        WJWKWLYRUUFUUAUUCWNWOQUUQUVANYEYJYLWPQWQVGUUIYOYKIZYOYMIZNUUHYOYKYMVHUW
        EUUBUWFUUGYJYOYHXOUBYLYOYHXPUBWRWSXCWTYEXQYBIXRYILXOXPUDXADXQDGZYFLZYHU
        WGMZYIYBBUWGXQLZUWHYGUWGXQYHUWGXQYFXDUWJTXBEYGYHXQKUGXEZXOXPCXFZAXFZXGX
        HXIXJYEXSYKXTYMYCXSYKLYDDXOUWIYKYBBDCXKZUWHYJUWGXOYHUWGXOYFXDUWNTXBEYJY
        HXOUWKUWLXHXIVEYDXTYMLYCDXPUWIYMYBBDAXKZUWHYLUWGXPYHUWGXPYFXDUWOTXBEYLY
        HXPUWKUWMXHXISXLXMXN $.
    $}

    ${
      $d r s $.
      $( The ansatz closure function
         ` ( r e. ~P 3o |-> if ( r = { (/) } , { (/) , 1o } , r ) ) ` has the
         K4 property of idempotence.  (Contributed by RP, 6-Jul-2021.) $)
      clsk1indlem4 $p |- A. s e. ~P 3o ( K ` ( K ` s ) ) = ( K ` s ) $=
        ( cv cfv wceq c3o cpw wcel c0 c1o cif c2o wtru cvv a1i id wa eqcom tpex
        csn cpr ctp wss snsstp1 0ex snss snsstp2 1oex prssd sselpwd mptru df3o2
        sylibr pweqi eleqtrri ifcld wn wo eqeq1 bitri bitrdi ifbieq2d 1n0 dfsn2
        eqif eqeq1i wb con0 preq2b 3bitri nemtbir intnan pm3.24 anbi2ci pm3.2ni
        1on mtbi iffalsei eqtrdi prex vex ifex fvmpt syl fveq2d 3eqtr4d rgen
        weq ) BEZAFZAFZWLGBHIZWKWNJZWKKUBZGZKLUCZWKMZAFZWSWMWLWOWSWNJWTWSGWOWQW
        RWKWNWRWNJWOWRKLNUDZIZWNWRXBJOWRXAPXAPJOKLNUAQOKLXAOWPXAUEZKXAJXCOKLNUF
        QKXAUGUHUOOLUBXAUEZLXAJXDOKLNUIQLXAUJUHUOUKULUMHXAUNUPUQQWORURCWSCEZWPG
        ZWRXEMZWSWNAXEWSGZXGWQWPWRGZSZWQUSZWPWKGZSZUTZWRWSMWSXHXFXNXEWSWRXHXFWS
        WPGZXNXEWSWPVAXOWPWSGXNWSWPTWQWPWRWKVGVBVCXHRVDXNWRWSXJXMXIWQXILKVEXIKK
        UCZWRGZKLGZLKGWPXPWRKVFVHXQXRVIOKLKPVJKPJOUGQLVJJOVRQVKUMKLTVLVMVNWQXKS
        XMWQVOWQXLXKWKWPTVPVSVQVTWADWQWRWKKLWBBWCWDZWEWFWOWLWSACWKXGWSWNACBWJZX
        FWQXEWKWRXEWKWPVAXTRVDDXSWEZWGYAWHWI $.
    $}

    ${
      $d K s t $.  $d r s t $.
      $( The ansatz closure function
         ` ( r e. ~P 3o |-> if ( r = { (/) } , { (/) , 1o } , r ) ) ` does not
         have the K1 property of isotony.  (Contributed by RP, 6-Jul-2021.) $)
      clsk1indlem1 $p |- E. s e. ~P 3o E. t e. ~P 3o ( s C_ t /\
                                                 -. ( K ` s ) C_ ( K ` t ) ) $=
        ( c0 wcel c2o cv wss cfv wn wa wrex c1o cvv wtru a1i wceq adantl elpwi2
        csn c3o cpw cpr ctp tpex snsstp1 df3o2 eleqtrri 0ex snss sylibr snsstp3
        pweqi 2oex prssd sselpwd mptru simpl sseq1 fveq2 sseq1d anbi12d rexbidv
        wb notbid simpr sseq2d cleq2lem 1oelpr cif iftrue prex adantr eleqtrrid
        fvmpt wo 1n0 neii csuc eqcom df-2o df-1o eqeq12i 3bitri nemtbir pm3.2ni
        suc11reg elpri mto eqeq1 id ifbieq2d prid2 wne 2on0 nelsn ax-mp nelneq2
        mp2an iffalsei eqtrdi neleqtrrd nelss syl2anc snsspr1 jctil rspcedvd )
        FUBZUCUDZGZFHUEZXKGZCIZAIZJZXOBKZXPBKZJZLZMZAXKNZCXKNXJFOHUFZUDZXKXJYDP
        FOHUGZFOHUHZUAUCYDUIUOZUJXMYEXKXMYEGQXMYDPYDPGQYFRQFHYDQXJYDJZFYDGYIQYG
        RFYDUKULUMQHUBYDJZHYDGYJQFOHUNRHYDUPULUMUQURUSYHUJXLXNMZYCXJXPJZXJBKZXS
        JZLZMZAXKNZCXJXKXLXNUTXOXJSZYCYQVFYKYRYBYPAXKYRXQYLYAYOXOXJXPVAYRXTYNYR
        XRYMXSXOXJBVBVCVGVDVETYKYPXJXMJZYMXMBKZJZLZMZAXMXKXLXNVHXPXMSZYPUUCVFYK
        YOUUBXPXMXJUUDYNUUAUUDXSYTYMXPXMBVBVIVGVJTYKUUBYSYKOYMGOYTGLUUBYKOFOUEZ
        YMVKXLYMUUESXNDXJDIZXJSZUUEUUFVLZUUEXKBUUGUUEUUFVMEFOVNVQVOVPYKYTXMOOXM
        GZLYKUUIOFSZOHSZVRUUJUUKOFVSVTUUKOFVSUUKHOSOWAZFWAZSUUJOHWBHUULOUUMWCWD
        WEOFWIWFWGWHOFHWJWKRXNYTXMSXLDXMUUHXMXKBUUFXMSZUUHXMXJSZUUEXMVLXMUUNUUG
        UUOUUFXMUUEUUFXMXJWLUUNWMWNUUOUUEXMHXMGHXJGLZUUOLFHUPWOHFWPUUPWQHFWRWSH
        XMXJWTXAXBXCEFHVNVQTXDOYMYTXEXFFHXGXHXIXIXA $.
    $}
  $}

  ${
    $( Question: Does K0, K2, K3, K4 imply K1 ? Stadler has twice said so.

         But for base sets of at least 3 elements, counter examples exist.
         ( s e. ~P { a, b, c } |-> if ( s = { a } , { a, b } , s ) ) is
         a pseudo-closure function which satisfies K0, K2, K3, and K4,
         but not K1.
    $)
    clsnim.k0 $e |- ( ph <-> ( k ` (/) ) = (/) ) $.
    clsnim.k1 $e |- ( ps <-> A. s e. ~P b A. t e. ~P b
                             ( s C_ t -> ( k ` s ) C_ ( k ` t ) ) ) $.
    clsnim.k2 $e |- ( ch <-> A. s e. ~P b s C_ ( k ` s ) ) $.
    clsnim.k3 $e |- ( th <-> A. s e. ~P b A. t e. ~P b
                      ( k ` ( s u. t ) ) C_ ( ( k ` s ) u. ( k ` t ) ) ) $.
    clsnim.k4 $e |- ( ta <-> A. s e. ~P b ( k ` ( k ` s ) ) = ( k ` s ) ) $.
    ${
      $d b k s t $.  $d r k s t $.
      $( For generalized closure functions, property K1 (isotony)
         is independent of the properties K0, K2, K3, K4.
         <HTML>
         This contradicts a claim which appears in preprints of Table
         2 in B&auml;rbel M. R. Stadler and Peter F. Stadler.  "Generalized
         Topological Spaces in Evolutionary Theory and Combinatorial
         Chemistry." <I>J. Chem. Inf. Comput. Sci.</I>, <B>42</B>:577-585,
         2002. Proceedings MCC 2001, Dubrovnik.
         The same table row implying K1 follows from the other four
         appears in the supplemental materials B&auml;rbel M. R. Stadler
         and Peter F. Stadler. "Basic Properties of Closure Spaces"
         2001 on page 12.
         </HTML>
         (Contributed by RP, 5-Jul-2021.) $)
      clsk1independent $p |- -. A. b A. k e. ( ~P b ^m ~P b ) (
                    ( ( ph /\ ch ) /\ ( th /\ ta ) ) -> ps ) $=
        ( vr c3o cfv wral wa wn cvv wcel c0 cv wceq wss cpw cun wi cmap co wrex
        wal con0 3on elexi csn c1o cpr cif cmpt wf eqid wo notnotr a1i c2o csuc
        sssucid 2oex elpw mpbir df2o3 df-3o eqcomi pweqi 2a1i jcad con1d anc2ri
        3eltr3i orrd sylibr fmpti clsk1indlem0 clsk1indlem2 pm3.2i clsk1indlem3
        ifel pwex elmap clsk1indlem4 clsk1indlem1 eqeq1d sseq2d ralbidv anbi12d
        fveq1 uneq12d sseq12d 2ralbidv id fveq12d eqeq12d rexnal2 pm4.61 notbid
        anbi2d bitrid 2rexbidv bitr3id rspcev pweq oveq12d wb raleqdv raleqbidv
        mp2an rexeqbidv ralv xchbinx sylib ) PUAUBZUCGUDZQZUCUEZHUDZYGYDQZUFZHP
        UGZRZSZYGFUDZUHZYDQZYHYMYDQZUHZUFZFYJRZHYJRZYHYDQZYHUEZHYJRZSZSZYGYMUFZ
        YHYPUFZUIZFYJRZHYJRZTZSZGYJYJUJUKZULZACSZDESZSZBUIZGIUDZUGZUUTUJUKZRZIU
        MZTZPUNUOUPZOYJOUDZUCUQUEZUCURUSZUVFUTZVAZUUMUBZUCUVJQZUCUEZYGYGUVJQZUF
        ZHYJRZSZYNUVJQZUVNYMUVJQZUHZUFZFYJRHYJRZUVNUVJQZUVNUEZHYJRZSZSZUUFUVNUV
        SUFZTZSZFYJULHYJULZSZUUNUVKYJYJUVJVBOYJYJUVIUVJUVJVCZUVFYJUBZUVGUVHYJUB
        ZSZUVGTZUWNSZVDUVIYJUBUWNUWPUWRUWNUWPTUWQUWNUWQUWPUWNUWQTZUVGUWOUWSUVGU
        IUWNUVGVEVFUWOUWNUWSVGVGVHZUGZUVHYJVGUXAUBVGUWTUFVGVIVGUWTVJVKVLVMUWTPP
        UWTVNVOVPWAVQVRVSVTWBUVGUVHUVFYJWIWCWDYJYJUVJPUVEWJZUXBWKVLUWGUWKUVQUWF
        UVMUVPUVJOUWMWEUVJHOUWMWFWGUWBUWEFUVJHOUWMWHUVJHOUWMWLWGWGFUVJHOUWMWMWG
        UULUWLGUVJUUMYDUVJUEZUUEUWGUUKUWKUXCYLUVQUUDUWFUXCYFUVMYKUVPUXCYEUVLUCU
        CYDUVJWRWNUXCYIUVOHYJUXCYHUVNYGYGYDUVJWRZWOWPWQUXCYTUWBUUCUWEUXCYRUWAHF
        YJYJUXCYOUVRYQUVTYNYDUVJWRUXCYHUVNYPUVSUXDYMYDUVJWRZWSWTXAUXCUUBUWDHYJU
        XCUUAUWCYHUVNUXCYHUVNYDUVJUXCXBUXDXCUXDXDWPWQWQUUKUUHTZFYJULHYJULUXCUWK
        UUHHFYJYJXEUXCUXFUWJHFYJYJUXFUUFUUGTZSUXCUWJUUFUUGXFUXCUXGUWIUUFUXCUUGU
        WHUXCYHUVNYPUVSUXDUXEWTXGXHXIXJXKWQXLXRYCUUNSUURTZGUVAULZIUAULZUVDUXIUU
        NIPUAUUSPUEZUXHUULGUVAUUMUXKUUTYJUUTYJUJUUSPXMZUXLXNUXHUUQBTZSUXKUULUUQ
        BXFUXKUUQUUEUXMUUKUXKUUOYLUUPUUDUXKAYFCYKAYFXOUXKJVFCYIHUUTRUXKYKLUXKYI
        HUUTYJUXLXPXIWQUXKDYTEUUCDYRFUUTRZHUUTRUXKYTMUXKUXNYSHUUTYJUXLUXKYRFUUT
        YJUXLXPXQXIEUUBHUUTRUXKUUCNUXKUUBHUUTYJUXLXPXIWQWQUXKBUUJBUUHFUUTRZHUUT
        RUXKUUJKUXKUXOUUIHUUTYJUXLUXKUUHFUUTYJUXLXPXQXIXGWQXIXSXLUXJUVBIUARUVCU
        URIGUAUVAXEUVBIXTYAYBXR $.
    $}
  $}

  ${
    $d B s t $.  $d N s t $.  $d ph s x $.  $d t x $.
    neik0pk1imk0.bex $e |- ( ph -> B e. V ) $.
    neik0pk1imk0.n $e |- ( ph -> N e. ( ~P ~P B ^m B ) ) $.
    neik0pk1imk0.k0p $e |- ( ph -> A. x e. B ( N ` x ) =/= (/) ) $.
    neik0pk1imk0.k1 $e |- ( ph -> A. x e. B A. s e. ~P B A. t e. ~P B
                                  ( ( s e. ( N ` x ) /\ s C_ t )
                                    -> t e. ( N ` x ) ) ) $.
    $( Kuratowski's K0' and K1 axioms imply K0.  Neighborhood version.
       (Contributed by RP, 3-Jun-2021.) $)
    neik0pk1imk0 $p |- ( ph -> A. x e. B B e. ( N ` x ) ) $=
      ( cv wcel wss wa cpw wi wral ralimdv mpd cfv wrex pwidg wceq sseq2 anbi2d
      eleq1 imbi12d rspcv 3syl r19.23v biimpi a1i c0 wne wex cmap co elmapi syl
      wf ffvelcdmda elpwid sseld ancrd eximdv n0 df-rex 3imtr4g elpwi ralrimivw
      imp syl6 adantr r19.29imd ex ralimdva ralim sylc ) AGLZBLZEUAZMZVTDNZOZGD
      PZUBZDWBMZQZBDRZWGBDRZWHBDRAWEWHQZGWFRZBDRZWJAWCVTCLZNZOZWOWBMZQZCWFRZGWF
      RZBDRWNKAXAWMBDAWTWLGWFADFMDWFMWTWLQHDFUCWSWLCDWFWODUDZWQWEWRWHXBWPWDWCWO
      DVTUEUFWODWBUGUHUIUJSSTAWMWIBDWMWIQAWMWIWEWHGWFUKULUMSTAWBUNUOZBDRWKJAXCW
      GBDAWADMOZXCWGXDXCOWCWDGWFXDXCWCGWFUBZXDWCGUPVTWFMZWCOZGUPXCXEXDWCXGGXDWC
      XFXDWBWFVTXDWBWFADWFPZWAEAEXHDUQURMDXHEVAIEXHDUSUTVBVCVDZVEVFGWBVGWCGWFVH
      VIVLXDWCWDQZGWFRXCXDXJGWFXDWCXFWDXIVTDVJVMVKVNVOVPVQTWGWHBDVRVS $.
  $}

  ${
    $( Based on:

       Casimir Kuratowski (Kazimierz Kuratowski).
       "Sur l'op&#233;ration A&#773; de l'Analysis Situs."
       Fundamenta Mathematicae, 3:182-199, 1922.

       P. C. Hammer. "Extended topology: Set-valued set functions."
       Nieuw Arch. Wisk. III, 10:55-77, 1962.
    $)

    $d A a b c d $.  $d F a b c d $.
    $( Two different ways to say subset relation persists across applications
       of a function.  (Contributed by RP, 31-May-2021.) $)
    isotone1 $p |- ( A. a e. ~P A A. b e. ~P A
                     ( a C_ b -> ( F ` a ) C_ ( F ` b ) )
                 <-> A. a e. ~P A A. b e. ~P A
                     ( ( F ` a ) u. ( F ` b ) ) C_ ( F ` ( a u. b ) ) ) $=
      ( vc vd cv wss cfv wi wral cun weq sseq1 fveq2 sseq1d imbi12d sseq2 wcel
      wa cpw sseq2d cbvral2vw ssun1 simprl pwuncl adantl simpl rspc2va syl21anc
      wceq mpi ssun2 simprr unssd ralrimivva ssequn1 uneq1d uneq1 fveq2d uneq2d
      sseq12d uneq2 ancoms unssad adantr sseqtrd ex biimtrid impbii bitri ) CGZ
      DGZHZVLBIZVMBIZHZJZDAUAZKCVSKEGZFGZHZVTBIZWABIZHZJZFVSKEVSKZVOVPLZVLVMLZB
      IZHZDVSKCVSKZVRWFVTVMHZWCVPHZJCDEFVSVSCEMZVNWMVQWNVLVTVMNWOVOWCVPVLVTBOZP
      QDFMZWMWBWNWEVMWAVTRWQVPWDWCVMWABOZUBQUCWGWLWGWKCDVSVSWGVLVSSZVMVSSZTZTZV
      OVPWJXBVLWIHZVOWJHZVLVMUDXBWSWIVSSZWGXCXDJZWGWSWTUEXAXEWGVLVMAUFUGZWGXAUH
      ZWFXFVLWAHZVOWDHZJEFVLWIVSVSECMZWBXIWEXJVTVLWANXKWCVOWDVTVLBOPQWAWIUKZXIX
      CXJXDWAWIVLRXLWDWJVOWAWIBOZUBQUIUJULXBVMWIHZVPWJHZVMVLUMXBWTXEWGXNXOJZWGW
      SWTUNXGXHWFXPVMWAHZVPWDHZJEFVMWIVSVSEDMZWBXQWEXRVTVMWANXSWCVPWDVTVMBOPQXL
      XQXNXRXOWAWIVMRXLWDWJVPXMUBQUIUJULUOUPWLWFEFVSVSWBVTWALZWAUKZWLVTVSSWAVSS
      TZTZWEVTWAUQYCYAWEYCYATWCXTBIZWDYCWCYDHYAYCWCWDYDYBWLWCWDLZYDHZWKYFWCVPLZ
      VTVMLZBIZHCDVTWAVSVSWOWHYGWJYIWOVOWCVPWPURWOWIYHBVLVTVMUSUTVBWQYGYEYIYDWQ
      VPWDWCWRVAWQYHXTBVMWAVTVCUTVBUIVDVEVFYAYDWDUKYCXTWABOUGVGVHVIUPVJVK $.

    $( Two different ways to say subset relation persists across applications
       of a function.  (Contributed by RP, 31-May-2021.) $)
    isotone2 $p |- ( A. a e. ~P A A. b e. ~P A
                     ( a C_ b -> ( F ` a ) C_ ( F ` b ) )
                 <-> A. a e. ~P A A. b e. ~P A
                     ( F ` ( a i^i b ) ) C_ ( ( F ` a ) i^i ( F ` b ) ) ) $=
      ( vc vd cv wss cfv wi wral cin weq fveq2 imbi12d sseq2 sseq2d wcel wceq
      wa cpw sseq1 sseq1d cbvral2vw inss1 inss2 elpwi sstrid vex inex2 ad2antll
      elpw sylibr simprl simpl syl21anc mpi simprr ssind ralrimivva dfss adantl
      rspc2va ineq1 fveq2d ineq1d sseq12d ineq2 ineq2d ancoms sstrdi eqsstrd ex
      adantr biimtrid impbii bitri ) CGZDGZHZVRBIZVSBIZHZJZDAUAZKCWEKEGZFGZHZWF
      BIZWGBIZHZJZFWEKEWEKZVRVSLZBIZWAWBLZHZDWEKCWEKZWDWLWFVSHZWIWBHZJCDEFWEWEC
      EMZVTWSWCWTVRWFVSUBXAWAWIWBVRWFBNZUCODFMZWSWHWTWKVSWGWFPXCWBWJWIVSWGBNZQO
      UDWMWRWMWQCDWEWEWMVRWERZVSWERZTZTZWOWAWBXHWNVRHZWOWAHZVRVSUEXHWNWERZXEWMX
      IXJJZXFXKWMXEXFWNAHXKXFWNVSAVRVSUFZVSAUGUHWNAVSVRDUIUJULUMUKZWMXEXFUNWMXG
      UOZWLXLWNWGHZWOWJHZJZEFWNVRWEWEWFWNSZWHXPWKXQWFWNWGUBXSWIWOWJWFWNBNUCOZFC
      MZXPXIXQXJWGVRWNPYAWJWAWOWGVRBNQOVCUPUQXHWNVSHZWOWBHZXMXHXKXFWMYBYCJZXNWM
      XEXFURXOWLYDXREFWNVSWEWEXTFDMZXPYBXQYCWGVSWNPYEWJWBWOWGVSBNQOVCUPUQUSUTWR
      WLEFWEWEWHWFWFWGLZSZWRWFWERWGWERTZTZWKWFWGVAYIYGWKYIYGTWIYFBIZWJYGWIYJSYI
      WFYFBNVBYIYJWJHYGYIYJWIWJLZWJYHWRYJYKHZWQYLWFVSLZBIZWIWBLZHCDWFWGWEWEXAWO
      YNWPYOXAWNYMBVRWFVSVDVEXAWAWIWBXBVFVGXCYNYJYOYKXCYMYFBVSWGWFVHVEXCWBWJWIX
      DVIVGVCVJWIWJUFVKVNVLVMVOUTVPVQ $.
  $}

  ${
    $d B s t $.  $d I s t $.
    $( An interior function is both monotone and sub-linear if and only if it
       is finitely linear.  (Contributed by RP, 18-Jun-2021.) $)
    ntrk1k3eqk13 $p |- ( ( A. s e. ~P B A. t e. ~P B ( s C_ t
                               -> ( I ` s ) C_ ( I ` t ) )
                        /\ A. s e. ~P B A. t e. ~P B
                          ( ( I ` s ) i^i ( I ` t ) ) C_ ( I ` ( s i^i t ) )
                     ) <-> A. s e. ~P B A. t e. ~P B ( I ` ( s i^i t ) )
                                             = ( ( I ` s ) i^i ( I ` t ) ) ) $=
      ( cv cin cfv wss wa cpw wral wceq r19.26-2 eqss 2ralbii isotone2 3bitr4ri
      wi anbi1i ) DEZAEZFCGZTCGZUACGZFZHZUEUBHZIZABJZKDUIKUFAUIKDUIKZUGAUIKDUIK
      ZIUBUELZAUIKDUIKTUAHUCUDHRAUIKDUIKZUKIUFUGDAUIUIMULUHDAUIUIUBUENOUMUJUKBC
      DAPSQ $.
  $}

  ${
    ntrcls.o $e |- O = ( i e. _V |-> ( k e. ( ~P i ^m ~P i ) |->
                        ( j e. ~P i |-> ( i \ ( k ` ( i \ j ) ) ) ) ) ) $.
    ntrcls.d $e |- D = ( O ` B ) $.
    ntrcls.r $e |- ( ph -> I D K ) $.

    ${
      $d B i j k $.  $d ph i j k $.
      $( If (pseudo-)interior and (pseudo-)closure functions are related by the
         duality operator we may characterize the relation as part of a 1-to-1
         onto function.  (Contributed by RP, 29-May-2021.) $)
      ntrclsf1o $p |- ( ph -> D : ( ~P B ^m ~P B ) -1-1-onto->
                                  ( ~P B ^m ~P B ) ) $=
        ( cvv ntrclsbex dssmapf1od ) ABCFIMEDJKABCGHIKLNO $.
    $}

    ${
      $d B i j k $.  $d ph i j k $.

      $( If (pseudo-)interior and (pseudo-)closure functions are related by the
         duality operator then they are related the opposite way.  (Contributed
         by RP, 21-May-2021.) $)
      ntrclsnvobr $p |- ( ph -> K D I ) $=
        ( ccnv cvv ntrclsbex dssmapnvod wbr cpw cmap co wf1o wrel f1orel mpbird
        wb ntrclsf1o relbrcnvg 3syl breqdi ) ACMZCHGABCFINEDJKABCGHIKLOPAHGUJQZ
        GHCQZLABRZUMSTZUNCUACUBUKULUEABCDEFGHIJKLUFUNUNCUCHGCUGUHUDUI $.
    $}

    ${
      $d B i j k $.  $d ph i j k $.

      $( If (pseudo-)interior and (pseudo-)closure functions are related by the
         duality operator then those functions are maps of subsets to subsets.
         (Contributed by RP, 21-May-2021.) $)
      ntrclsiex $p |- ( ph -> I e. ( ~P B ^m ~P B ) ) $=
        ( cdm cpw cmap co wrel wbr wcel syl wf1o ntrclsf1o releldm syl2anc wceq
        f1orel f1odm eleqtrd ) AGCMZBNZUJOPZACQZGHCRGUISAUKUKCUAZULABCDEFGHIJKL
        UBZUKUKCUFTLGHCUCUDAUMUIUKUEUNUKUKCUGTUH $.
    $}

    ${
      $d B i j k $.  $d ph i j k $.

      $( If (pseudo-)interior and (pseudo-)closure functions are related by the
         duality operator then those functions are maps of subsets to subsets.
         (Contributed by RP, 21-May-2021.) $)
      ntrclskex $p |- ( ph -> K e. ( ~P B ^m ~P B ) ) $=
        ( ntrclsnvobr ntrclsiex ) ABCDEFHGIJKABCDEFGHIJKLMN $.
    $}

    ${
      $d B i j k $.  $d ph i j k $.
      $( If (pseudo-)interior and (pseudo-)closure functions are related by the
         duality operator then there is a functional relation between them
         (Contributed by RP, 28-May-2021.) $)
      ntrclsfv1 $p |- ( ph -> ( D ` I ) = K ) $=
        ( cfv wceq wbr wfun wcel wa syl jca cdm wb cpw cmap wfn ntrclsf1o f1ofn
        co wf1o ntrclsiex fnfun adantr fndm eleq2d biimpar funbrfvb mpbird ) AG
        CMHNZGHCOZLACPZGCUAZQZRZURUSUBACBUCZVDUDUHZUEZGVEQZRZVCAVFVGAVEVECUIVFA
        BCDEFGHIJKLUFVEVECUGSABCDEFGHIJKLUJTVHUTVBVFUTVGVECUKULVFVBVGVFVAVEGVEC
        UMUNUOTSGHCUPSUQ $.

      $( If (pseudo-)interior and (pseudo-)closure functions are related by the
         duality operator then there is a functional relation between them
         (Contributed by RP, 28-May-2021.) $)
      ntrclsfv2 $p |- ( ph -> ( D ` K ) = I ) $=
        ( ntrclsnvobr ntrclsfv1 ) ABCDEFHGIJKABCDEFGHIJKLMN $.
    $}

    ${
      ntrcls.x $e |- ( ph -> X e. B ) $.
      ${
        ntrcls.s $e |- ( ph -> S e. ~P B ) $.
        ${
          $d B i j k $.  $d K j k $.  $d S j $.  $d ph i j k $.
          $( If (pseudo-)interior and (pseudo-)closure functions are related by
             the duality operator then there is an equivalence between
             membership in the interior of a set and non-membership in the
             closure of the complement of the set.  (Contributed by RP,
             28-May-2021.) $)
          ntrclselnel1 $p |- ( ph -> ( X e. ( I ` S )
                                       <-> -. X e. ( K ` ( B \ S ) ) ) ) $=
            ( cfv wcel cdif eqid wn ntrclsfv2 eqcomd fveq1d ntrclsbex ntrclskex
            cvv dssmapfv3d eqtrd eleq2d wa wb eldif a1i mpbirand bitrd ) AKDHQZ
            RKBBDSIQZSZRZKURRUAZAUQUSKAUQDICQZQZUSADHVBAVBHABCEFGHIJLMNUBUCUDAB
            CDVCGIVBJUGFELMABCHIJMNUEABCEFGHIJLMNUFVBTPVCTUHUIUJAUTKBRZVAOUTVDV
            AUKULAKBURUMUNUOUP $.
        $}

        ${
          $d B i j k $.  $d I j k $.  $d S j $.  $d ph i j k $.
          $( If (pseudo-)interior and (pseudo-)closure functions are related by
             the duality operator then there is an equivalence between
             membership in interior of the complement of a set and
             non-membership in the closure of the set.  (Contributed by RP,
             28-May-2021.) $)
          ntrclselnel2 $p |- ( ph -> ( X e. ( I ` ( B \ S ) )
                                       <-> -. X e. ( K ` S ) ) ) $=
            ( cfv wcel cdif ntrclsnvobr ntrclselnel1 con2bid ) AKDIQRKBDSHQRABC
            DEFGIHJKLMABCEFGHIJLMNTOPUAUB $.
        $}
      $}
    $}

    ${
      ntrclsfv.s $e |- ( ph -> S e. ~P B ) $.

      ${
        $d B i j k $.  $d K j k $.  $d S j $.  $d ph i j k $.
        $( The value of the interior (closure) expressed in terms of the
           closure (interior).  (Contributed by RP, 25-Jun-2021.) $)
        ntrclsfv $p |- ( ph -> ( I ` S ) = ( B \ ( K ` ( B \ S ) ) ) ) $=
          ( cfv cdif ntrclsfv2 fveq1d cvv eqid ntrclsbex ntrclskex dssmapfv3d
          eqtr3d ) ADICOZOZDHOBBDPIOPADUEHABCEFGHIJKLMQRABCDUFGIUEJSFEKLABCHIJL
          MUAABCEFGHIJKLMUBUETNUFTUCUD $.
      $}

      ${
        ntrclsfv.c $e |- ( ph -> C e. ~P B ) $.

        ${
          $d B i j k $.  $d K j k $.  $d S j $.  $d ph i j k $.
          $( If interior and closure functions are related then specific
             function values are complementary.  (Contributed by RP,
             27-Jun-2021.) $)
          ntrclsfveq1 $p |- ( ph -> ( ( I ` S ) = C <->
                              ( K ` ( B \ S ) ) = ( B \ C ) ) ) $=
            ( cdif cfv wceq wss elpwid dfss4 eqcomd eqeq2d ntrclsfv eqeq1d cmap
            sylib wb cpw co wf ntrclskex elmapi ntrclsrcomplex ffvelcdmd difssd
            wcel syl rcompleq syl2anc 3bitr4d ) ABBEQZJRZQZCSVEBBCQZQZSZEIRZCSV
            DVFSZACVGVEAVGCACBTVGCSACBPUACBUBUHUCUDAVIVECABDEFGHIJKLMNOUEUFAVDB
            TVFBTVJVHUIAVDBABUJZVKVCJAJVKVKUGUKURVKVKJULABDFGHIJKLMNUMJVKVKUNUS
            ABDEIJKMNUOUPUAABCUQVDVFBUTVAVB $.
        $}

        ${
          $d B i j k $.  $d I j k $.  $d S j $.  $d ph i j k $.
          $( If interior and closure functions are related then specific
             function values are complementary.  (Contributed by RP,
             27-Jun-2021.) $)
          ntrclsfveq2 $p |- ( ph -> ( ( I ` ( B \ S ) ) = C <->
                                              ( K ` S ) = ( B \ C ) ) ) $=
            ( cdif cfv wceq wss wb cpw cmap co wcel wf ntrclsiex ntrclsrcomplex
            elmapi syl ffvelcdmd elpwid rcompleq syl2anc ntrclsfv eqeq1d bitr4d
            ntrclsnvobr ) ABEQZIRZCSZBUTQZBCQZSZEJRZVCSAUTBTCBTVAVDUAAUTBABUBZV
            FUSIAIVFVFUCUDUEVFVFIUFABDFGHIJKLMNUGIVFVFUIUJABDEIJKMNUHUKULACBPUL
            UTCBUMUNAVEVBVCABDEFGHJIKLMABDFGHIJKLMNUROUOUPUQ $.
        $}
      $}

      ${
        ntrclsfv.t $e |- ( ph -> T e. ~P B ) $.

        ${
          $d B i j k $.  $d K j k $.  $d S j $.  $d T j $.  $d ph i j k $.
          $( If interior and closure functions are related then equality of a
             pair of function values is equivalent to equality of a pair of the
             other function's values.  (Contributed by RP, 27-Jun-2021.) $)
          ntrclsfveq $p |- ( ph -> ( ( I ` S ) = ( I ` T ) <->
                             ( K ` ( B \ S ) ) = ( K ` ( B \ T ) ) ) ) $=
            ( cfv wceq cdif eqeq2d ntrclsfv ntrclsrcomplex ntrclsfveq1 wss cmap
            cpw co wcel wf ntrclskex elmapi ffvelcdmd elpwid dfss4 sylib 3bitrd
            syl ) ADIQZEIQZRURBBESZJQZSZRBDSJQZBVBSZRVCVARAUSVBURABCEFGHIJKLMNP
            UATABVBCDFGHIJKLMNOABCVAIJKMNUBUCAVDVAVCAVABUDVDVARAVABABUFZVEUTJAJ
            VEVEUEUGUHVEVEJUIABCFGHIJKLMNUJJVEVEUKUQABCEIJKMNUBULUMVABUNUOTUP
            $.
        $}

        ${
          $d B i j k $.  $d K j k $.  $d S j $.  $d T j $.  $d ph i j k $.
          $( If interior and closure functions are related then a subset
             relation of a pair of function values is equivalent to subset
             relation of a pair of the other function's values.  (Contributed
             by RP, 27-Jun-2021.) $)
          ntrclsss $p |- ( ph -> ( ( I ` S ) C_ ( I ` T ) <->
                           ( K ` ( B \ T ) ) C_ ( K ` ( B \ S ) ) ) ) $=
            ( cfv wss cdif wcel ntrclsfv sseq12d cpw cmap co wa ntrclskex ancli
            wb wf elmapi adantl ntrclsrcomplex adantr ffvelcdmd elpwid sscon34b
            jca 3syl bitr4d ) ADIQZEIQZRBBDSZJQZSZBBESZJQZSZRZVGVDRZAVAVEVBVHAB
            CDFGHIJKLMNOUAABCEFGHIJKLMNPUAUBAAJBUCZVKUDUETZUFZVGBRZVDBRZUFVJVIU
            IAVLABCFGHIJKLMNUGUHVMVNVOVMVGBVMVKVKVFJVLVKVKJUJAJVKVKUKULZAVFVKTV
            LABCEIJKMNUMUNUOUPVMVDBVMVKVKVCJVPAVCVKTVLABCDIJKMNUMUNUOUPURVGVDBU
            QUSUT $.
        $}
      $}
    $}

    ${
      ntrclslem0.x $e |- ( ph -> X e. B ) $.

      ${
        $d B i j k s t $.  $d I j k s t $.  $d K t $.  $d X s t $.
        $d ph i j k s t $.
        $( If (pseudo-)interior and (pseudo-)closure functions are related by
           the duality operator then conditions equal to claiming that at least
           one (pseudo-)neighborbood of a particular point exists hold equally.
           (Contributed by RP, 21-May-2021.) $)
        ntrclsneine0lem $p |- ( ph -> ( E. s e. ~P B X e. ( I ` s )
                                    <-> E. s e. ~P B -. X e. ( K ` s ) ) ) $=
          ( vt cfv wcel adantr wceq cv cpw wrex weq fveq2 eleq2d ntrclsrcomplex
          wn cbvrexvw cdif difeq2 adantl elpwi dfss4 sylib ad2antlr rspcedeq2vd
          wa wss eqtr2d w3a wb 3ad2ant3 wbr simpr ntrclselnel2 3adant3 rexxfrd2
          bitrd bitrid ) JKUAZGQZRZKBUBZUCJPUAZGQZRZPVNUCAJVKHQRUHZKVNUCVMVQKPV
          NKPUDVLVPJVKVOGUEUFUIAVQVRPKBVKUJZVNVNAVSVNRVKVNRZABCVKGHIMNUGSAVOVNR
          ZURZKBVOUJZVNVOVSAWCVNRWAABCVOGHIMNUGSWBVKWCTZURVSBWCUJZVOWDVSWETWBVK
          WCBUKULWAWEVOTZAWDWAVOBUSWFVOBUMVOBUNUOUPUTUQAVTVOVSTZVAVQJVSGQZRZVRW
          GAVQWIVBVTWGVPWHJVOVSGUEUFVCAVTWIVRVBWGAVTURBCVKDEFGHIJLMAGHCVDVTNSAJ
          BRVTOSAVTVEVFVGVIVHVJ $.
      $}
    $}

    ${
      $d B i j k s $.  $d I j k s $.  $d ph i j k s x $.

      $( If (pseudo-)interior and (pseudo-)closure functions are related by the
         duality operator then conditions equal to claiming that for every
         point, at least one (pseudo-)neighborbood exists hold equally.
         (Contributed by RP, 21-May-2021.) $)
      ntrclsneine0 $p |- ( ph -> ( A. x e. B E. s e. ~P B x e. ( I ` s )
                            <-> A. x e. B E. s e. ~P B -. x e. ( K ` s ) ) ) $=
        ( cv cfv wcel cpw wrex wn wa wbr adantr simpr ntrclsneine0lem ralbidva
        ) ABOZKOZHPQKCRZSUGUHIPQTKUISBCAUGCQZUACDEFGHIJUGKLMAHIDUBUJNUCAUJUDUEU
        F $.
    $}

    ${
      $d B i j k $.  $d I j k $.  $d K j k $.  $d ph i j k $.
      $( If (pseudo-)interior and (pseudo-)closure functions are related by the
         duality operator then conditions equal to claiming that the closure of
         the empty set is the empty set hold equally.  (Contributed by RP,
         1-Jun-2021.) $)
      ntrclscls00 $p |- ( ph -> ( ( I ` B ) = B <-> ( K ` (/) ) = (/) ) ) $=
        ( cfv wceq c0 cdif cvv eqid wcel fveq2i ntrclsfv1 fveq1d cpw dssmapfv3d
        ntrclsbex ntrclsiex 0elpw a1i eqtr3d dif0 eqtrid difeq2d difid sylan9eq
        id eqtrdi pwidg syl ntrclsfv impbida ) ABGMZBNZOHMZONZAVBVCBBOPZGMZPZOA
        OGCMZMZVCVGAOVHHABCDEFGHIJKLUAUBABCOVIFGVHIQEDJKABCGHIKLUEZABCDEFGHIJKL
        UFVHROBUCZSABUGUHVIRUDUIVBVGBBPZOVBVFBBVBVFVABVEBGBUJZTVBUOUKULBUMZUPUN
        AVDVABVLHMZPZBABCBDEFGHIJKLABQSBVKSVJBQUQURUSVDVPVEBVDVOOBVDVOVCOVLOHVN
        TVDUOUKULVMUPUNUT $.
    $}

    ${
      $d B a b i j k s t $.  $d I a b j k s t $.  $d K a b $.
      $d ph a b i j k s t $.
      $( If (pseudo-)interior and (pseudo-)closure functions are related by the
         duality operator then conditions equal to claiming that either is
         isotonic hold equally.  (Contributed by RP, 3-Jun-2021.) $)
      ntrclsiso $p |- ( ph -> ( A. s e. ~P B A. t e. ~P B
                                ( s C_ t -> ( I ` s ) C_ ( I ` t ) )
                            <-> A. s e. ~P B A. t e. ~P B
                                ( s C_ t -> ( K ` s ) C_ ( K ` t ) ) ) ) $=
        ( wss cfv wral cdif cvv wceq vb va cv wi cpw sseq1 fveq2 sseq1d imbi12d
        weq sseq2 sseq2d cbvral2vw ralcom bitri wcel simpl ntrclsbex syl difssd
        wa sselpwd wrex elpwi simpr difeq2d eqeq2d eqcom bitrdi bilani rspcedvd
        dfss4 syl2an w3a simpl1 3ad2antl1 wb simp12 elpwid simp2 syl2anc bicomd
        sscon34b cmap co simp11 ntrclsiex elmapi ffvelcdmd simp3 simp13 sseq12d
        wf fveq2d ntrclsfv1 fveq1d eqid dssmapfv3d eqtr3d imbi2d 3bitr4d bitrid
        wbr ralxfrd2 ) KUCZBUCZOZXEHPZXFHPZOZUDZBCUEZQKXLQZUAUCZUBUCZOZXNHPZXOH
        PZOZUDZUAXLQZUBXLQZAXGXEIPZXFIPZOZUDZBXLQZKXLQXMXTUBXLQUAXLQYBXKXTXNXFO
        ZXQXIOZUDKBUAUBXLXLKUAUJZXGYHXJYIXEXNXFUFYJXHXQXIXEXNHUGUHUIBUBUJZYHXPY
        IXSXFXOXNUKYKXIXRXQXFXOHUGULUIUMXTUAUBXLXLUNUOAYAYGUBKCXERZXLXLAXEXLUPZ
        VAZYLCSYNACSUPZAYMUQACDHIJMNURZUSYNCXEUTVBAYOXOCOZXOYLTZKXLVCXOXLUPYPXO
        CVDYOYQVAZYRCCXORZRZXOTZKYTXLYSYTCSYOYQUQYSCXOUTVBYSXEYTTZVAZYRXOUUATUU
        BUUDYLUUAXOUUDXEYTCYSUUCVEVFVGXOUUAVHVIYQUUBYOXOCVLVJVKVMAYMYRVNZXTYFUA
        BCXFRZXLXLUUEXFXLUPZVAZUUFCSUUHAYOAYMYRUUGVOYPUSUUHCXFUTVBAYMXNXLUPZXNU
        UFTZBXLVCZYRAYOXNCOZUUKUUIYPXNCVDYOUULVAZUUJCCXNRZRZXNTZBUUNXLUUMUUNCSY
        OUULUQUUMCXNUTVBUUMXFUUNTZVAZUUJXNUUOTUUPUURUUFUUOXNUURXFUUNCUUMUUQVEVF
        VGXNUUOVHVIUULUUPYOXNCVLVJVKVMVPUUEUUGUUJVNZUUFYLOZUUFHPZYLHPZOZUDXGCUV
        BRZCUVARZOZUDXTYFUUSUUTXGUVCUVFUUSXGUUTUUSXECOXFCOXGUUTVQUUSXECAYMYRUUG
        UUJVRZVSUUSXFCUUEUUGUUJVTZVSXEXFCWCWAWBUUSUVACOUVBCOUVCUVFVQUUSUVACUUSX
        LXLUUFHUUSHXLXLWDWEUPZXLXLHWMUUSAUVIAYMYRUUGUUJWFZACDEFGHIJLMNWGUSZHXLX
        LWHUSZUUSUUFCSUUSAYOUVJYPUSZUUSCXFUTVBWIVSUUSUVBCUUSXLXLYLHUVLUUSYLCSUV
        MUUSCXEUTVBWIVSUVAUVBCWCWAUIUUSXPUUTXSUVCUUSXNUUFXOYLUUEUUGUUJWJZAYMYRU
        UGUUJWKZWLUUSXQUVAXRUVBUUSXNUUFHUVNWNUUSXOYLHUVOWNWLUIUUSYEUVFXGUUSYCUV
        DYDUVEUUSXEHDPZPZYCUVDUUSXEUVPIUUSAUVPITUVJACDEFGHIJLMNWOUSWPUUSCDXEUVQ
        GHUVPJSFELMUVMUVKUVPWQZUVGUVQWQWRWSUUSXFUVPPZYDUVEUUSXFUVPIUUSCDEFGHIJL
        MUUSAHIDXCUVJNUSWOWPUUSCDXFUVSGHUVPJSFELMUVMUVKUVRUVHUVSWQWRWSWLWTXAXDX
        DXB $.
    $}

    ${
      $d B i j k s t $.  $d I j k s t $.  $d K t $.  $d ph i j k s t $.
      $( An interior function is contracting if and only if the closure
         function is expansive.  (Contributed by RP, 9-Jun-2021.) $)
      ntrclsk2 $p |- ( ph -> ( A. s e. ~P B ( I ` s ) C_ s
                           <-> A. s e. ~P B s C_ ( K ` s ) ) ) $=
        ( vt cfv wss cdif wcel wceq wb cv cpw wral fveq2 sseq12d ntrclsrcomplex
        weq id cbvralvw adantr wa difeq2 eqeq2d adantl elpwi dfss4 sylib eqcomd
        rspcedvd 3ad2ant3 wf cmap co ntrclsiex elmapi 3ad2ant1 ffvelcdmd elpwid
        w3a syl difssd sscon34b syl2anc simp2 sseq1d bitrd ntrclsbex dssmapfv3d
        cvv eqid sseq2d ntrclsfv1 fveq1d 3bitr2d ralxfrd2 bitrid ) JUAZGOZWGPZJ
        BUBZUCNUAZGOZWKPZNWJUCAWGWGHOZPZJWJUCWIWMJNWJJNUGZWHWLWGWKWGWKGUDWPUHUE
        UIAWMWONJBWGQZWJWJAWQWJRZWGWJRZABCWGGHILMUFZUJAWKWJRZUKZWKWQSZWKBBWKQZQ
        ZSZJXDWJAXDWJRXAABCWKGHILMUFUJWGXDSZXCXFTXBXGWQXEWKWGXDBULUMUNXBXEWKXAX
        EWKSZAXAWKBPXHWKBUOWKBUPUQUNURUSAWSXCVIZWMWQGOZWQPZWOXCAWMXKTWSXCWLXJWK
        WQWKWQGUDXCUHUEUTXIXKWGBXJQZPZWGWGGCOZOZPZWOXIXKBWQQZXLPZXMXIXJBPWQBPXK
        XRTXIXJBXIWJWJWQGAWSWJWJGVAZXCAGWJWJVBVCRZXSABCDEFGHIKLMVDZGWJWJVEVJVFA
        WSWRXCWTVFVGVHXIBWGVKXJWQBVLVMXIWSXRXMTAWSXCVNZWSXQWGXLWSWGBPXQWGSWGBUO
        WGBUPUQVOVJVPXIXOXLWGXIBCWGXOFGXNIVSEDKLAWSBVSRXCABCGHILMVQVFAWSXTXCYAV
        FXNVTYBXOVTVRWAAWSXPWOTXCAXOWNWGAWGXNHABCDEFGHIKLMWBWCWAVFWDVPWEWF $.
    $}

    ${
      $d B a b s t $.  $d B i j k s t $.  $d I a b s t $.  $d I j k s t $.
      $d K a b $.  $d ph a b s t $.  $d ph i j k s t $.
      $( The interiors of disjoint sets are disjoint if and only if the
         closures of sets that span the base set also span the base set.
         (Contributed by RP, 10-Jun-2021.) $)
      ntrclskb $p |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( ( s i^i t ) = (/)
                                        -> ( ( I ` s ) i^i ( I ` t ) ) = (/) )
                            <-> A. s e. ~P B A. t e. ~P B ( ( s u. t ) = B
                                         -> ( ( K ` s ) u. ( K ` t ) ) = B )
                             ) ) $=
        ( cin c0 wceq cfv cdif wcel va vb cv wi cpw wral cun ineq1 eqeq1d fveq2
        weq ineq1d imbi12d ineq2d cbvral2vw ntrclsrcomplex adantr difeq2 eqeq2d
        ineq2 wa wb adantl wss elpwi dfss4 sylib eqcomd rspcedvd w3a simpl1 syl
        wrex 3ad2antl1 simp13 simp3 simp11 simp12 simp2 elpwid rcompleq sylancl
        unssd ssid difundi difid eqeq12i bitr2di cmap ntrclsiex 3ad2ant1 elmapi
        co wf cvv ntrclsbex difssd sselpwd ffvelcdmd ssinss1 0ss difindi bitrdi
        dif0 eqid dssmapfv3d uneq12d ntrclsfv1 fveq1 eqtr3d imbi2d bitrd 3bitrd
        syl3anc ralxfrd2 bitrid ) KUCZBUCZOZPQZXQHRZXRHRZOZPQZUDZBCUEZUFKYFUFUA
        UCZUBUCZOZPQZYGHRZYHHRZOZPQZUDZUBYFUFZUAYFUFAXQXRUGZCQZXQIRZXRIRZUGZCQZ
        UDZBYFUFZKYFUFYEYOYGXROZPQZYKYBOZPQZUDKBUAUBYFYFKUAUKZXTUUFYDUUHUUIXSUU
        EPXQYGXRUHUIUUIYCUUGPUUIYAYKYBXQYGHUJULUIUMBUBUKZUUFYJUUHYNUUJUUEYIPXRY
        HYGUTUIUUJUUGYMPUUJYBYLYKXRYHHUJUNUIUMUOAYPUUDUAKCXQSZYFYFAUUKYFTXQYFTZ
        ACDXQHIJMNUPUQAYGYFTZVAZYGUUKQZYGCCYGSZSZQZKUUPYFAUUPYFTUUMACDYGHIJMNUP
        UQXQUUPQZUUOUURVBUUNUUSUUKUUQYGXQUUPCURUSVCUUMUURAUUMUUQYGUUMYGCVDUUQYG
        QYGCVEYGCVFVGVHVCVIAUULUUOVJZYOUUCUBBCXRSZYFYFUUTXRYFTZVAAUVAYFTAUULUUO
        UVBVKACDXRHIJMNUPVLAUULYHYFTZYHUVAQZBYFVMUUOAUVCVAZUVDYHCCYHSZSZQZBUVFY
        FAUVFYFTUVCACDYHHIJMNUPUQXRUVFQZUVDUVHVBUVEUVIUVAUVGYHXRUVFCURUSVCUVCUV
        HAUVCUVGYHUVCYHCVDUVGYHQYHCVEYHCVFVGVHVCVIVNUUTUVBUVDVJZYOUUKYHOZPQZUUK
        HRZYLOZPQZUDZUUKUVAOZPQZUVMUVAHRZOZPQZUDZUUCUVJUUOYOUVPVBAUULUUOUVBUVDV
        OUUOYJUVLYNUVOUUOYIUVKPYGUUKYHUHUIUUOYMUVNPUUOYKUVMYLYGUUKHUJULUIUMVLUV
        JUVDUVPUWBVBUUTUVBUVDVPUVDUVLUVRUVOUWAUVDUVKUVQPYHUVAUUKUTUIUVDUVNUVTPU
        VDYLUVSUVMYHUVAHUJUNUIUMVLUVJAUULUVBUWBUUCVBAUULUUOUVBUVDVQAUULUUOUVBUV
        DVRUUTUVBUVDVSAUULUVBVJZUWBYRCUVMSZCUVSSZUGZCQZUDUUCUWCUVRYRUWAUWGUWCYR
        CYQSZCCSZQZUVRUWCYQCVDCCVDYRUWJVBUWCXQXRCUWCXQCAUULUVBVSZVTUWCXRCAUULUV
        BVPZVTWCCWDYQCCWAWBUWHUVQUWIPCXQXRWECWFWGWHUWCUWACUVTSZCPSZQZUWGUWCUVTC
        VDZPCVDUWAUWOVBUWCUVMCVDUWPUWCUVMCUWCYFYFUUKHUWCHYFYFWIWMTZYFYFHWNAUULU
        WQUVBACDEFGHIJLMNWJWKZHYFYFWLVLUWCUUKCWOAUULCWOTUVBACDHIJMNWPWKZUWCCXQW
        QWRWSVTUVMUVSCWTVLCXAUVTPCWAWBUWMUWFUWNCCUVMUVSXBCXDWGXCUMUWCUWGUUBYRUW
        CUWFUUACUWCXQHDRZRZXRUWTRZUGZUWFUUAUWCUXAUWDUXBUWEUWCCDXQUXAGHUWTJWOFEL
        MUWSUWRUWTXEZUWKUXAXEXFUWCCDXRUXBGHUWTJWOFELMUWSUWRUXDUWLUXBXEXFXGUWCUW
        TIQZUXCUUAQAUULUXEUVBACDEFGHIJLMNXHWKUXEUXAYSUXBYTXQUWTIXIXRUWTIXIXGVLX
        JUIXKXLXNXMXOXOXP $.
    $}

    ${
      $d B a b s t $.  $d B i j k s t $.  $d I a b s t $.  $d I i j k s t $.
      $d K a b $.  $d ph a b s t $.  $d ph i j k s t $.
      $( The intersection of interiors of a every pair is a subset of the
         interior of the intersection of the pair if an only if the closure of
         the union of every pair is a subset of the union of closures of the
         pair.  (Contributed by RP, 19-Jun-2021.) $)
      ntrclsk3 $p |- ( ph -> ( A. s e. ~P B A. t e. ~P B
                               ( ( I ` s ) i^i ( I ` t ) )
                               C_ ( I ` ( s i^i t ) )
                           <-> A. s e. ~P B A. t e. ~P B ( K ` ( s u. t ) )
                               C_ ( ( K ` s ) u. ( K ` t ) ) ) ) $=
        ( cfv cin wss cdif cvv wceq va vb cv cpw wral fveq2 ineq1d ineq1 fveq2d
        cun sseq12d ineq2d ineq2 cbvral2vw wcel ntrclsbex difssd sselpwd adantr
        weq wrex elpwi wa simpl simpr eqeq2d eqcom bitrdi dfss4 bilani rspcedvd
        difeq2d syl2an w3a simpl1 syl 3ad2antl1 simp13 difundi eqtr4di 3ad2ant3
        wb cmap co simp11 ntrclsiex jca wo wf elmapi ffvelcdmd elpwid inss 3syl
        orc sscon34b 4syl difindi sseq2i a1i simp12 rp-simp2 simpl2 simpl3 eqid
        simprl simprr unssd 3ad2antl2 dssmapfv3d fveq1d eqtr3d uneq12d syl32anc
        ntrclsfv1 3bitrd ralxfrd2 bitrid ) KUCZHOZBUCZHOZPZXSYAPZHOZQZBCUDZUEKY
        GUEUAUCZHOZUBUCZHOZPZYHYJPZHOZQZUBYGUEZUAYGUEAXSYAUJZIOZXSIOZYAIOZUJZQZ
        BYGUEZKYGUEYFYOYIYBPZYHYAPZHOZQKBUAUBYGYGKUAUTZYCUUDYEUUFUUGXTYIYBXSYHH
        UFUGUUGYDUUEHXSYHYAUHUIUKBUBUTZUUDYLUUFYNUUHYBYKYIYAYJHUFULUUHUUEYMHYAY
        JYHUMUIUKUNAYPUUCUAKCXSRZYGYGAUUIYGUOXSYGUOZAUUICSACDHIJMNUPZACXSUQURUS
        ACSUOZYHCQZYHUUITZKYGVAYHYGUOUUKYHCVBUULUUMVCZUUNCCYHRZRZYHTZKUUPYGUUOU
        UPCSUULUUMVDUUOCYHUQURUUOXSUUPTZVCZUUNYHUUQTUURUUTUUIUUQYHUUTXSUUPCUUOU
        USVEVLVFYHUUQVGVHUUMUURUULYHCVIVJVKVMAUUJUUNVNZYOUUBUBBCYARZYGYGUVAYAYG
        UOZVCAUVBYGUOAUUJUUNUVCVOAUVBCSUUKACYAUQURVPAUUJYJYGUOZYJUVBTZBYGVAZUUN
        AUULYJCQZUVFUVDUUKYJCVBUULUVGVCZUVECCYJRZRZYJTZBUVIYGUVHUVICSUULUVGVDUV
        HCYJUQURUVHYAUVITZVCZUVEYJUVJTUVKUVMUVBUVJYJUVMYAUVICUVHUVLVEVLVFYJUVJV
        GVHUVGUVKUULYJCVIVJVKVMVQUVAUVCUVEVNZYOUUIHOZYKPZUUIYJPZHOZQZUVOUVBHOZP
        ZCYQRZHOZQZUUBUVNUUNYOUVSWBAUUJUUNUVCUVEVRUUNYLUVPYNUVRUUNYIUVOYKYHUUIH
        UFUGUUNYMUVQHYHUUIYJUHUIUKVPUVEUVAUVSUWDWBUVCUVEUVPUWAUVRUWCUVEYKUVTUVO
        YJUVBHUFULUVEUVQUWBHUVEUVQUUIUVBPUWBYJUVBUUIUMCXSYAVSVTUIUKWAUVNUWDCUWC
        RZCUWARZQZUWECUVORZCUVTRZUJZQZUUBUVNAHYGYGWCWDUOZUULVCZUWACQZUWCCQZVCUW
        DUWGWBAUUJUUNUVCUVEWEZAUWLUULACDEFGHIJLMNWFZUUKWGUWMUWNUWOUWMUVOCQZUWRU
        VTCQZWHUWNUWMUVOCUWMYGYGUUIHUWLYGYGHWIUULHYGYGWJUSZUWMUUICSUWLUULVEZUWM
        CXSUQURWKWLUWRUWSWOUVOUVTCWMWNUWMUWCCUWMYGYGUWBHUWTUWMUWBCSUXAUWMCYQUQU
        RWKWLWGUWAUWCCWPWQUWGUWKWBUVNUWFUWJUWECUVOUVTWRWSWTUVNAUULUWLUUJUVCUWKU
        UBWBUWPUVNAUULUWPUUKVPUVNAUWLUWPUWQVPAUUJUUNUVCUVEXAUVAUVCUVEXBAUULUWLV
        NZUUJUVCVCZVCZUWEYRUWJUUAUXDYQHDOZOZUWEYRUXDCDYQUXFGHUXEJSFELMAUULUWLUX
        CXCZAUULUWLUXCXDZUXEXEZUULAUXCYQYGUOUWLUULUXCVCZYQCSUULUXCVDUXJXSYACUXJ
        XSCUULUUJUVCXFWLUXJYACUULUUJUVCXGWLXHURXIUXFXEXJUXDAUXFYRTAUULUWLUXCVOZ
        AYQUXEIACDEFGHIJLMNXOZXKVPXLUXDUWHYSUWIYTUXDXSUXEOZUWHYSUXDCDXSUXMGHUXE
        JSFELMUXGUXHUXIUXBUUJUVCXFUXMXEXJUXDAUXMYSTUXKAXSUXEIUXLXKVPXLUXDYAUXEO
        ZUWIYTUXDCDYAUXNGHUXEJSFELMUXGUXHUXIUXBUUJUVCXGUXNXEXJUXDAUXNYTTUXKAYAU
        XEIUXLXKVPXLXMUKXNXPXPXQXQXR $.
    $}

    ${
      $d B a b s t $.  $d B i j k s t $.  $d I a b s t $.  $d I i j k s t $.
      $d K a b $.  $d ph a b s t $.  $d ph i j k s t $.
      $( The interior of the intersection of any pair is equal to the
         intersection of the interiors if and only if the closure of the unions
         of any pair is equal to the union of closures.  (Contributed by RP,
         19-Jun-2021.) $)
      ntrclsk13 $p |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( I ` ( s i^i t ) ) =
                                                    ( ( I ` s ) i^i ( I ` t ) )
                            <-> A. s e. ~P B A. t e. ~P B ( K ` ( s u. t ) ) =
                                              ( ( K ` s ) u. ( K ` t ) ) ) ) $=
        ( cin cfv wceq cdif cvv wa va vb cv cpw wral cun weq ineq1 fveq2d fveq2
        ineq1d eqeq12d ineq2 ineq2d cbvral2vw wcel ntrclsbex difssd sselpwd wss
        adantr elpwi wb difeq2 eqeq2d eqcom bitrdi adantl dfss4 bilani rspcedvd
        wrex sylan2 w3a ralbidv 3ad2ant3 ad2antrr simpll syl2anc difundi simp1l
        eqtr4di jccir simp1r simp2 wf cmap co ntrclsiex elmapi syl anim1i simpl
        simpr ffvelcdmd elpwid ssinss1 rcompleq 3syl simplr simprl simprr unssd
        jca eqid dssmapfv3d uneq12d difindi ntrclsfv1 3bitr2d syl12anc ralxfrd2
        fveq1 bitrd 3adant3 bitrid ) KUCZBUCZOZHPZXQHPZXRHPZOZQZBCUDZUEKYEUEUAU
        CZUBUCZOZHPZYFHPZYGHPZOZQZUBYEUEZUAYEUEAXQXRUFZIPZXQIPZXRIPZUFZQZBYEUEZ
        KYEUEYDYMYFXROZHPZYJYBOZQKBUAUBYEYEKUAUGZXTUUCYCUUDUUEXSUUBHXQYFXRUHUIU
        UEYAYJYBXQYFHUJUKULBUBUGZUUCYIUUDYLUUFUUBYHHXRYGYFUMUIUUFYBYKYJXRYGHUJU
        NULUOAYNUUAUAKCXQRZYEYEAUUGYEUPXQYEUPZAUUGCSACDHIJMNUQZACXQURUSVAYFYEUP
        AYFCUTZYFUUGQZKYEVLYFCVBAUUJTZUUKCCYFRZRZYFQZKUUMYEUULUUMCSACSUPZUUJUUI
        VAUULCYFURUSXQUUMQZUUKUUOVCUULUUQUUKYFUUNQUUOUUQUUGUUNYFXQUUMCVDVEYFUUN
        VFVGVHUUJUUOAYFCVIVJVKVMAUUHUUKVNYNUUGYGOZHPZUUGHPZYKOZQZUBYEUEZUUAUUKA
        YNUVCVCUUHUUKYMUVBUBYEUUKYIUUSYLUVAUUKYHUURHYFUUGYGUHUIUUKYJUUTYKYFUUGH
        UJUKULVOVPAUUHUVCUUAVCUUKAUUHTZUVBYTUBBCXRRZYEYEAUVEYEUPUUHXRYEUPZAUVEC
        SUUIACXRURUSVQUVDYGYEUPZTAYGCUTZYGUVEQZBYEVLAUUHUVGVRUVGUVHUVDYGCVBVHAU
        VHTZUVICCYGRZRZYGQZBUVKYEAUVKYEUPUVHAUVKCSUUIACYGURUSVAXRUVKQZUVIUVMVCU
        VJUVNUVIYGUVLQUVMUVNUVEUVLYGXRUVKCVDVEYGUVLVFVGVHUVHUVMAYGCVIVJVKVSUVDU
        VFUVIVNZUVBCYORZHPZUUTUVEHPZOZQZYTUVIUVDUVBUVTVCUVFUVIUUSUVQUVAUVSUVIUU
        RUVPHUVIUURUUGUVEOUVPYGUVEUUGUMCXQXRVTWBUIUVIYKUVRUUTYGUVEHUJUNULVPUVOA
        UUPTZUUHUVFUVTYTVCUVOAUUPAUUHUVFUVIWAUUIWCAUUHUVFUVIWDUVDUVFUVIWEUWAUUH
        UVFTZTZUVTCUVQRZCUVSRZQZYOHDPZPZXQUWGPZXRUWGPZUFZQZYTUWCYEYEHWFZUUPTZUV
        QCUTZUVSCUTZTUVTUWFVCUWAUWNUWBAUWMUUPAHYEYEWGWHUPZUWMACDEFGHIJLMNWIZHYE
        YEWJWKWLVAUWNUWOUWPUWNUVQCUWNYEYEUVPHUWMUUPWMZUWNUVPCSUWMUUPWNZUWNCYOUR
        USWOWPUWNUUTCUTUWPUWNUUTCUWNYEYEUUGHUWSUWNUUGCSUWTUWNCXQURUSWOWPUUTUVRC
        WQWKXDUVQUVSCWRWSUWCUWHUWDUWKUWEUWCCDYOUWHGHUWGJSFELMAUUPUWBWTZAUWQUUPU
        WBUWRVQUWGXEZUWCYOCSUXAUWCXQXRCUWCXQCUWAUUHUVFXAWPUWCXRCUWAUUHUVFXBWPXC
        USUWHXEXFUWCUWKCUUTRZCUVRRZUFUWEUWCUWIUXCUWJUXDUWBUWAUUHUWIUXCQUUHUVFWM
        UWAUUHTCDXQUWIGHUWGJSFELMAUUPUUHWTAUWQUUPUUHUWRVQUXBUWAUUHWNUWIXEXFVMUW
        BUWAUVFUWJUXDQUUHUVFWNUWAUVFTCDXRUWJGHUWGJSFELMAUUPUVFWTAUWQUUPUVFUWRVQ
        UXBUWAUVFWNUWJXEXFVMXGCUUTUVRXHWBULUWCAUWGIQZUWLYTVCAUUPUWBVRACDEFGHIJL
        MNXIUXEUWHYPUWKYSYOUWGIXMUXEUWIYQUWJYRXQUWGIXMXRUWGIXMXGULWSXJXKXNXLXOX
        NXLXP $.
    $}

    ${
      $d B i j k s t $.  $d I j k s t $.  $d K j t $.  $d ph i j k s t $.
      $( Idempotence of the interior function is equivalent to idempotence of
         the closure function.  (Contributed by RP, 10-Jul-2021.) $)
      ntrclsk4 $p |- ( ph -> ( A. s e. ~P B ( I ` ( I ` s ) ) = ( I ` s )
                      <-> A. s e. ~P B ( K ` ( K ` s ) ) = ( K ` s ) ) ) $=
        ( vt cfv wceq cdif wcel adantr wb cv cpw wral weq 2fveq3 fveq2 cbvralvw
        eqeq12d ntrclsrcomplex wa difeq2 eqeq2d adantl elpwi dfss4 sylib eqcomd
        wss rspcedvd w3a 3ad2ant3 cmap co ntrclsiex elmapi syl ffvelcdmd elpwid
        wf rcompleq syl2anc ntrclsnvobr ffvelcdmda ntrclsfv simpr difeq2d eqtrd
        wbr fveq2d bitr4d 3adant3 bitrd ralxfrd2 bitrid ) JUAZGOZGOZWFPZJBUBZUC
        NUAZGOZGOZWKPZNWIUCAWEHOZHOZWNPZJWIUCWHWMJNWIJNUDWGWLWFWKWEWJGGUEWEWJGU
        FUHUGAWMWPNJBWEQZWIWIAWQWIRWEWIRZABCWEGHILMUIZSAWJWIRZUJZWJWQPZWJBBWJQZ
        QZPZJXCWIAXCWIRWTABCWJGHILMUISWEXCPZXBXETXAXFWQXDWJWEXCBUKULUMWTXEAWTXD
        WJWTWJBURXDWJPWJBUNWJBUOUPUQUMUSAWRXBUTWMWQGOZGOZXGPZWPXBAWMXITWRXBWLXH
        WKXGWJWQGGUEWJWQGUFUHVAAWRXIWPTXBAWRUJZXIBXHQZBXGQZPZWPAXIXMTZWRAXHBURX
        GBURZXNAXHBAWIWIXGGAGWIWIVBVCZRWIWIGVIABCDEFGHIKLMVDGWIWIVEVFZAWIWIWQGX
        QWSVGZVGVHAXGBXRVHZXHXGBVJVKSXJWOXKWNXLXJWOBBWNQZGOZQXKXJBCWNDEFHGIKLAH
        GCVRWRABCDEFGHIKLMVLZSZAWIWIWEHAHXPRWIWIHVIABCDEFHGIKLYBVDHWIWIVEVFVMVN
        XJYAXHBXJXTXGGXJXTBXLQZXGXJWNXLBXJBCWEDEFHGIKLYCAWRVOVNZVPAYDXGPZWRAXOY
        FXSXGBUOUPSVQVSVPVQYEUHVTWAWBWCWD $.
    $}
  $}

  ${
    ntrnei.o $e |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |->
                         ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) ) $.
    ntrnei.f $e |- F = ( ~P B O B ) $.
    ntrnei.r $e |- ( ph -> I F N ) $.

    ${
      $d O b $.  $d a b i j k $.  $d a b i j l $.  $d a b i j m $.
      $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
         by the operator, ` F ` , then the base set exists.  (Contributed by
         RP, 29-May-2021.) $)
      ntrneibex $p |- ( ph -> B e. _V ) $=
        ( va vb cvv cv cmap cmpt cpw co cfv wcel crab cmpo oveq2 rabeq mpteq2dv
        weq mpteq12dv pweq oveq1d mpteq1 cbvmpov eqtri wceq a1i brovmptimex2 )
        AOPHIBUAZBGQJQEPRZUAZORZSUBZKVAKRFRERUCUDZFVCUEZTZTZJCDQQEDRZUAZCRZSUBZ
        KVIVEFVKUEZTZTZUFOPQQVHUFLCDOPQQVOVHEVJVCSUBZKVIVFTZTCOUJZEVLVNVPVQVKVC
        VJSUGVRKVIVMVFVEFVKVCUHUIUKDPUJZEVPVQVDVGVSVJVBVCSVIVAULUMKVIVAVFUNUKUO
        UPNGUTBJUBUQAMURUS $.
    $}

    ${
      $d i j k $.  $d i j l $.  $d i j m $.
      $( The relative complement of the class ` S ` exists as a subset of the
         base set.  (Contributed by RP, 26-Jun-2021.) $)
      ntrneircomplex $p |- ( ph -> ( B \ S ) e. ~P B ) $=
        ( cdif cvv ntrneibex difssd sselpwd ) ABCPBQABDEFGHIJKLMNORABCST $.
    $}

    ${
      $d B i j k l m $.  $d ph i j k l $.
      $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
         by the operator, ` F ` , we may characterize the relation as part of a
         1-to-1 onto function.  (Contributed by RP, 29-May-2021.) $)
      ntrneif1o $p |- ( ph -> F : ( ~P B ^m ~P B ) -1-1-onto->
                                  ( ~P ~P B ^m B ) ) $=
        ( cpw cvv ntrneibex pwexd fsovf1od ) AFKBOBEGJPPCDLABPABCDEFGHIJKLMNQZR
        TMS $.
    $}

    ${
      $d B i j k l m $.  $d ph i j k l $.
      $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
         by the operator, ` F ` , then the interior function exists.
         (Contributed by RP, 29-May-2021.) $)
      ntrneiiex $p |- ( ph -> I e. ( ~P B ^m ~P B ) ) $=
        ( cdm cpw cmap co wrel syl wbr wcel wf1o ntrneif1o releldm syl2anc wceq
        f1orel f1odm eleqtrd ) AHGOZBPZULQRZAGSZHIGUAHUKUBAUMULPBQRZGUCZUNABCDE
        FGHIJKLMNUDZUMUOGUHTNHIGUEUFAUPUKUMUGUQUMUOGUITUJ $.
    $}

    ${
      $d B i j k l m $.  $d ph i j k l $.
      $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
         by the operator, ` F ` , then the neighborhood function exists.
         (Contributed by RP, 29-May-2021.) $)
      ntrneinex $p |- ( ph -> N e. ( ~P ~P B ^m B ) ) $=
        ( crn cpw cmap co wrel wbr wcel wf1o ntrneif1o syl relelrn syl2anc ccnv
        f1orel wfn wfun wceq w3a dff1o2 sylib simp3d eleqtrd ) AIGOZBPZPBQRZAGS
        ZHIGTIUQUAAURURQRZUSGUBZUTABCDEFGHIJKLMNUCZVAUSGUHUDNHIGUEUFAGVAUIZGUGU
        JZUQUSUKZAVBVDVEVFULVCVAUSGUMUNUOUP $.
    $}

    ${
      $d B i j k l m $.  $d ph i j k l $.
      $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
         by the operator, ` F ` , then converse of ` F ` is known.
         (Contributed by RP, 29-May-2021.) $)
      ntrneicnv $p |- ( ph -> `' F = ( B O ~P B ) ) $=
        ( cpw co cvv ntrneibex pwexd eqid fsovcnvd ) AFKBOZBEGBUBJPZJQQCDLABQAB
        CDEFGHIJKLMNRZSUDMUCTUA $.
    $}

    ${
      $d B i j k l m $.  $d ph i j k l $.
      $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
         by the operator, ` F ` , then the function value of ` F ` is the
         neighborhood function.  (Contributed by RP, 29-May-2021.) $)
      ntrneifv1 $p |- ( ph -> ( F ` I ) = N ) $=
        ( cpw cmap co wcel wa jca cfv wceq wbr wfn wfun wb wf1o ntrneif1o f1ofn
        cdm syl ntrneiiex fnfun adantr fndm eleq2d biimpar funbrfvb 3syl mpbird
        ) AHGUAIUBZHIGUCZNAGBOZVCPQZUDZHVDRZSZGUEZHGUJZRZSVAVBUFAVEVFAVDVCOBPQZ
        GUGVEABCDEFGHIJKLMNUHVDVKGUIUKABCDEFGHIJKLMNULTVGVHVJVEVHVFVDGUMUNVEVJV
        FVEVIVDHVDGUOUPUQTHIGURUSUT $.
    $}

    ${
      $d B i j k l m $.  $d ph i j k l $.
      $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
         by the operator, ` F ` , then the function value of converse of ` F `
         is the interior function.  (Contributed by RP, 29-May-2021.) $)
      ntrneifv2 $p |- ( ph -> ( `' F ` N ) = I ) $=
        ( wceq wbr wcel wa wb cpw ccnv cfv wfun cdm cmap co ntrneif1o ntrneinex
        wf1o wfo dff1o3 simprbi adantr crn df-rn f1ofo forn syl eqtr3id biimpar
        eleq2d jca syl2anc funbrfvb ntrneiiex brcnvg bitrd mpbird ) AIGUAZUBHOZ
        HIGPZNAVJIHVIPZVKAVIUCZIVIUDZQZRZVJVLSABTZVQUEUFZVQTBUEUFZGUIZIVSQZVPAB
        CDEFGHIJKLMNUGABCDEFGHIJKLMNUHZVTWARVMVOVTVMWAVTVRVSGUJZVMVRVSGUKULUMVT
        VOWAVTVNVSIVTVNGUNZVSGUOVTWCWDVSOVRVSGUPVRVSGUQURUSVAUTVBVCIHVIVDURAWAH
        VRQVLVKSWBABCDEFGHIJKLMNVEIHVSVRGVFVCVGVH $.
    $}

    ${
      ntrnei.x $e |- ( ph -> X e. B ) $.
      ${
        ntrnei.s $e |- ( ph -> S e. ~P B ) $.
        ${
          $d B i j k l m $.  $d I k l m $.  $d S m $.  $d X l m $.
          $d ph i j k l $.
          $( If (pseudo-)interior and (pseudo-)neighborhood functions are
             related by the operator, ` F ` , then there is an equivalence
             between membership in the interior of a set and non-membership in
             the closure of the complement of the set.  (Contributed by RP,
             29-May-2021.) $)
          ntrneiel $p |- ( ph -> ( X e. ( I ` S ) <-> S e. ( N ` X ) ) ) $=
            ( cfv wcel cv cpw crab wceq fveq2 eleq2d elrab3 syl ntrneibex pwexd
            wb cvv ntrneiiex eqid fsovfvfvd ntrneifv1 fveq1d eqtr3d bitr3d ) AC
            LGUAZISZTZGBUBZUCZTZLCISZTZCLJSZTACVCTVEVGUKRVBVGGCVCUTCUDVAVFLUTCI
            UEUFUGUHAVDVHCALIHSZSVDVHAGMVCBFIHVIKULULLDENABULABDEFGHIJKMNOPUIZU
            JVJOABDEFGHIJKMNOPUMVIUNQUOALVIJABDEFGHIJKMNOPUPUQURUFUS $.
        $}
      $}

      ${
        $d B i j k l m s $.  $d I k l m $.  $d N s $.  $d X l m s $.
        $d ph i j k l s $.
        $( The value of the neighbors (convergents) expressed in terms of the
           interior (closure) function.  (Contributed by RP, 26-Jun-2021.) $)
        ntrneifv3 $p |- ( ph -> ( N ` X ) = { s e. ~P B | X e. ( I ` s ) } ) $=
          ( cpw cfv wcel cin cv crab dfin5 wss wceq cmap co wf ntrneinex elmapi
          syl ffvelcdmd elpwid sseqin2 sylib wbr adantr simpr ntrneiel rabbidva
          wa bicomd 3eqtr3a ) ABRZKISZUAZLUBZVFTZLVEUCVFKVHHSTZLVEUCLVEVFUDAVFV
          EUEVGVFUFAVFVEABVERZKIAIVKBUGUHTBVKIUIABCDEFGHIJMNOPUJIVKBUKULQUMUNVF
          VEUOUPAVIVJLVEAVHVETZVBZVJVIVMBVHCDEFGHIJKMNOAHIGUQVLPURAKBTVLQURAVLU
          SUTVCVAVD $.
      $}

      ${
        $d B i j k l m $.  $d I k l m $.  $d N s $.  $d X l m s $.
        $d ph i j k l s $.
        $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
           by the operator, ` F ` , then conditions equal to claiming that for
           every point, at least one (pseudo-)neighborbood exists hold equally.
           (Contributed by RP, 29-May-2021.) $)
        ntrneineine0lem $p |- ( ph -> ( E. s e. ~P B X e. ( I ` s )
                                        <-> ( N ` X ) =/= (/) ) ) $=
          ( cfv wcel cpw cv wrex c0 wne wbr adantr simpr ntrneiel rexbidva cmap
          wa wex co ntrneinex elmapi syl ffvelcdmd elpwid sseld pm4.71rd exbidv
          wf bicomd df-rex n0 3bitr4g bitrd ) AKLUAZHRSZLBTZUBVHKIRZSZLVJUBZVKU
          CUDZAVIVLLVJAVHVJSZUKBVHCDEFGHIJKMNOAHIGUEVOPUFAKBSVOQUFAVOUGUHUIAVOV
          LUKZLULZVLLULZVMVNAVRVQAVLVPLAVLVOAVKVJVHAVKVJABVJTZKIAIVSBUJUMSBVSIV
          BABCDEFGHIJMNOPUNIVSBUOUPQUQURUSUTVAVCVLLVJVDLVKVEVFVG $.
      $}

      ${
        $d B i j k l m s $.  $d I k l m $.  $d N s $.  $d X l m s $.
        $d ph i j k l s $.
        $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
           by the operator, ` F ` , then conditions equal to claiming that for
           every point, at not all subsets are (pseudo-)neighborboods hold
           equally.  (Contributed by RP, 1-Jun-2021.) $)
        ntrneineine1lem $p |- ( ph -> ( E. s e. ~P B -. X e. ( I ` s )
                                        <-> ( N ` X ) =/= ~P B ) ) $=
          ( wcel wn wa cv cfv cpw wne wbr adantr simpr ntrneiel notbid rexbidva
          wrex wss wo wb co wf ntrneinex elmapi syl ffvelcdmd elpwid biortn wex
          cmap df-rex bitr4i wceq df-ne ianor eqss xchnxbir bitri 3bitr4g bitrd
          nss ) AKLUAZHUBRZSZLBUCZUKVPKIUBZRZSZLVSUKZVTVSUDZAVRWBLVSAVPVSRZTZVQ
          WAWFBVPCDEFGHIJKMNOAHIGUEWEPUFAKBRWEQUFAWEUGUHUIUJAVSVTULZSZVTVSULZSW
          HUMZWCWDAWIWHWJUNAVTVSABVSUCZKIAIWKBVDUORBWKIUPABCDEFGHIJMNOPUQIWKBUR
          USQUTVAWIWHVBUSWCWEWBTLVCWHWBLVSVELVSVTVOVFWDVTVSVGZSWJVTVSVHWIWGTWJW
          LWIWGVIVTVSVJVKVLVMVN $.
      $}
    $}

    ${
      $d B i j k l m x $.  $d I k l m x $.  $d S m x $.  $d ph i j k l x $.
      ntrneifv.s $e |- ( ph -> S e. ~P B ) $.
      $( The value of the interior (closure) expressed in terms of the
         neighbors (convergents) function.  (Contributed by RP,
         26-Jun-2021.) $)
      ntrneifv4 $p |- ( ph -> ( I ` S ) = { x e. B | S e. ( N ` x ) } ) $=
        ( cfv wcel crab cin cv dfin5 wss wceq cpw co ntrneiiex elmapi ffvelcdmd
        cmap wf syl elpwid sseqin2 sylib wa wbr simpr ntrneiel rabbidva 3eqtr3a
        adantr ) ACDJRZUAZBUBZVDSZBCTVDDVFKRSZBCTBCVDUCAVDCUDVEVDUEAVDCACUFZVID
        JAJVIVIUKUGSVIVIJULACEFGHIJKLMNOPUHJVIVIUIUMQUJUNVDCUOUPAVGVHBCAVFCSZUQ
        CDEFGHIJKLVFMNOAJKIURVJPVCAVJUSADVISVJQVCUTVAVB $.
    $}

    ${
      ntrneiel2.x $e |- ( ph -> X e. B ) $.
      ${
        ntrneiel2.s $e |- ( ph -> S e. ~P B ) $.
        ${
          $d B i j k l m y $.  $d B u y $.  $d I k l m y $.  $d N u y $.
          $d S m y $.  $d S u y $.  $d X l m y $.  $d X u y $.
          $d ph i j k l y $.  $d ph u y $.
          $( Membership in iterated interior of a set is equivalent to there
             existing a particular neighborhood of that member such that points
             are members of that neighborhood if and only if the set is a
             neighborhood of each of those points.  (Contributed by RP,
             11-Jul-2021.) $)
          ntrneiel2 $p |- ( ph -> ( X e. ( I ` ( I ` S ) )
                                    <-> E. u e. ( N ` X ) A. y e. B
                                        ( y e. u <-> S e. ( N ` y ) ) ) ) $=
            ( cfv wcel cv wa cab wel wb wral wrex cpw cmap ntrneiiex elmapi syl
            co wf ffvelcdmd ntrneiel crab ntrneifv4 df-rab eqtrdi eleq1d clabel
            wal wex df-rex bitr4i cvv ibar bibi2d ralbiia wss ssv cdif wn eldif
            a1i vex mpbiran ntrneinex elpwid sselda con3dimp pm3.14 orcs adantl
            sseld 2falsed ex biimtrid ralrimiv raldifeq bitrid bitr2di rexbidva
            ralv 3bitrd ) ANEKUAZKUAUBWSNLUAZUBBUCZDUBZEXALUAUBZUDZBUEZWTUBZBCU
            FZXCUGZBDUHZCWTUIZADWSFGHIJKLMNOPQRSADUJZXKEKAKXKXKUKUOUBXKXKKUPADF
            GHIJKLMOPQRULKXKXKUMUNTUQURAWSXEWTAWSXCBDUSXEABDEFGHIJKLMOPQRTUTXCB
            DVAVBVCXFXGXDUGZBVEZCWTUIZAXJXFCUCZWTUBZXMUDCVFXNXDBCWTVDXMCWTVGVHA
            XMXICWTAXPUDZXIXLBVIUHZXMXIXLBDUHXQXRXHXLBDXBXCXDXGXBXCVJVKVLXQXLBD
            VIDVIVMXQDVNVRXQXLBVIDVOZXAXSUBZXBVPZXQXLXTXAVIUBYABVSXAVIDVQVTXQYA
            XLXQYAUDXGXDXQXGXBXQXODXAXQXODAWTXKXOAWTXKADXKUJZNLALYBDUKUOUBDYBLU
            PADFGHIJKLMOPQRWALYBDUMUNSUQWBWCWBWHWDYAXDVPZXQYAXCVPYCXBXCWEWFWGWI
            WJWKWLWMWNXLBWQWOWPWNWR $.
        $}
      $}
    $}

    ${
      $d B i j k l m s $.  $d I k l m $.  $d N s $.  $d ph i j k l s x $.
      $d m x $.

      $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
         by the operator, ` F ` , then conditions equal to claiming that for
         every point, at least one (pseudo-)neighborbood exists hold equally.
         (Contributed by RP, 29-May-2021.) $)
      ntrneineine0 $p |- ( ph -> ( A. x e. B E. s e. ~P B x e. ( I ` s )
                            <-> A. x e. B ( N ` x ) =/= (/) ) ) $=
        ( cv cfv wcel cpw wrex c0 wne wbr adantr simpr ntrneineine0lem ralbidva
        wa ) ABQZLQIRSLCTUAUJJRUBUCBCAUJCSZUICDEFGHIJKUJLMNOAIJHUDUKPUEAUKUFUGU
        H $.
    $}

    ${
      $d B i j k l m s $.  $d I k l m $.  $d N s $.  $d ph i j k l s x $.
      $d m x $.
      $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
         by the operator, ` F ` , then conditions equal to claiming that for
         every point, at not all subsets are (pseudo-)neighborboods hold
         equally.  (Contributed by RP, 1-Jun-2021.) $)
      ntrneineine1 $p |- ( ph -> ( A. x e. B E. s e. ~P B -. x e. ( I ` s )
                            <-> A. x e. B ( N ` x ) =/= ~P B ) ) $=
        ( cv cfv wcel wn cpw wrex wne wbr adantr simpr ntrneineine1lem ralbidva
        wa ) ABQZLQIRSTLCUAZUBUJJRUKUCBCAUJCSZUICDEFGHIJKUJLMNOAIJHUDULPUEAULUF
        UGUH $.
    $}

    ${
      $d B i j k l m x $.  $d I k l m x $.  $d ph i j k l x $.
      $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
         by the operator, ` F ` , then conditions equal to claiming that the
         closure of the empty set is the empty set hold equally.  (Contributed
         by RP, 2-Jun-2021.) $)
      ntrneicls00 $p |- ( ph -> ( ( I ` B ) = B <->
                                  A. x e. B B e. ( N ` x ) ) ) $=
        ( cfv wcel wral wss wa wceq cv cpw co wf ntrneiiex elmapi syl ntrneibex
        cmap cvv pwidg ffvelcdmd elpwid wb eqss dfss3 anbi2i bitri a1i mpbirand
        wbr adantr simpr ntrneiel ralbidva bitrd ) ACIPZCUAZBUBZVHQZBCRZCVJJPQZ
        BCRAVIVHCSZVLAVHCACUCZVOCIAIVOVOUJUDQVOVOIUEACDEFGHIJKLMNOUFIVOVOUGUHAC
        UKQCVOQZACDEFGHIJKLMNOUICUKULUHZUMUNVIVNVLTZUOAVIVNCVHSZTVRVHCUPVSVLVNB
        CVHUQURUSUTVAAVKVMBCAVJCQZTCCDEFGHIJKVJLMNAIJHVBVTOVCAVTVDAVPVTVQVCVEVF
        VG $.
    $}

    ${
      $d B i j k l m x $.  $d I k l m x $.  $d ph i j k l x $.
      $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
         by the operator, ` F ` , then conditions equal to claiming that the
         interior of the empty set is the empty set hold equally.  (Contributed
         by RP, 2-Jun-2021.) $)
      ntrneicls11 $p |- ( ph -> ( ( I ` (/) ) = (/) <->
                                  A. x e. B -. (/) e. ( N ` x ) ) ) $=
        ( c0 cfv wceq wcel wss cv wn wral cdif cin wb cpw cmap ntrneiiex elmapi
        co wf syl 0elpw ffvelcdmd elpwid reldisj bicomd difid sseq2i ss0b bitri
        a1i disjr 3bitr3g wa wbr adantr simpr ntrneiel notbid ralbidva bitrd )
        APIQZPRZBUAZVNSZUBZBCUCZPVPJQSZUBZBCUCAVNCCUDZTZVNCUEPRZVOVSAWDWCAVNCTW
        DWCUFAVNCACUGZWEPIAIWEWEUHUKSWEWEIULACDEFGHIJKLMNOUIIWEWEUJUMPWESZACUNZ
        VCUOUPVNCCUQUMURWCVNPTVOWBPVNCUSUTVNVAVBBVNCVDVEAVRWABCAVPCSZVFZVQVTWIC
        PDEFGHIJKVPLMNAIJHVGWHOVHAWHVIWFWIWGVCVJVKVLVM $.
    $}

    ${
      $d B i j k l m s t x $.  $d I k l m x $.  $d ph i j k l s t x $.
      $( If (pseudo-)interior and (pseudo-)neighborhood functions are related
         by the operator, ` F ` , then conditions equal to claiming that the
         interior function is isotonic hold equally.  (Contributed by RP,
         3-Jun-2021.) $)
      ntrneiiso $p |- ( ph -> ( A. s e. ~P B A. t e. ~P B
                                ( s C_ t -> ( I ` s ) C_ ( I ` t ) )
                            <-> A. x e. B A. s e. ~P B A. t e. ~P B
                                ( ( s e. ( N ` x ) /\ s C_ t )
                                  -> t e. ( N ` x ) ) ) ) $=
        ( wi wral wcel cv wss cfv cpw wa wal df-ss imbi2i 19.21v bitr4i ax-1 wn
        cmap co wf simpll ntrneiiex elmapi 3syl simplr ffvelcdmd elpwid pm2.24d
        sselda com23 a1dd idd jad impbid2 albidv df-ral bitr4di ad3antrrr simpr
        ex simpllr ntrneiel imbi12d imbi2d impexp ancomst bitr3i ralbidva bitrd
        wbr bitrdi bitrid ralcom ) AMUAZCUAZUBZWIJUCZWJJUCZUBZRZCDUDZSZMWPSWIBU
        AZKUCZTZWKUEWJWSTZRZCWPSZBDSZMWPSXCMWPSBDSAWQXDMWPAWIWPTZUEZWQXBBDSZCWP
        SXDXFWOXGCWPWOWKWRWLTZWRWMTZRZRZBUFZXFWJWPTZUEZXGWOWKXJBUFZRXLWNXOWKBWL
        WMUGUHWKXJBUIUJXNXLXKBDSZXGXNXLWRDTZXKRZBUFXPXNXKXRBXNXKXRXKXQUKXNXQXKX
        KXNXQULZXJWKXNXHXSXIXNXHXSXIRXNXHUEXQXIXNWLDWRXNWLDXNWPWPWIJXNAJWPWPUMU
        NTWPWPJUOAXEXMUPADEFGHIJKLNOPQUQJWPWPURUSAXEXMUTVAVBVDVCVOVEVFXNXKVGVHV
        IVJXKBDVKVLXNXKXBBDXNXQUEZXKWKWTXARZRZXBXTXJYAWKXTXHWTXIXAXTDWIEFGHIJKL
        WRNOPAJKIWEXEXMXQQVMZXNXQVNZAXEXMXQVPVQXTDWJEFGHIJKLWRNOPYCYDXFXMXQUTVQ
        VRVSYBWKWTUEXARXBWKWTXAVTWKWTXAWAWBWFWCWDWGWCXBCBWPDWHWFWCXCMBWPDWHWF
        $.
    $}

    ${
      $d B i j k l m s x $.  $d I k l m x $.  $d ph i j k l s x $.
      $( An interior function is contracting if and only if all the
         neighborhoods of a point contain that point.  (Contributed by RP,
         11-Jun-2021.) $)
      ntrneik2 $p |- ( ph -> ( A. s e. ~P B ( I ` s ) C_ s
                 <-> A. x e. B A. s e. ~P B ( s e. ( N ` x ) -> x e. s ) ) ) $=
        ( wral wcel wi wa cv cfv wss cpw wel wal wb cmap co wf ntrneiiex elmapi
        syl ffvelcdmda elpwid sselda biimt pm5.74da bi2.04 bitrdi albidv df-ral
        df-ss 3bitr4g wbr ad2antrr simpr simplr ntrneiel imbi1d ralbidva ralcom
        bitrd ) ALUAZIUBZVNUCZLCUDZQVNBUAZJUBRZBLUEZSZBCQZLVQQWALVQQBCQAVPWBLVQ
        AVNVQRZTZVPVRVORZVTSZBCQZWBWDWFBUFVRCRZWFSZBUFVPWGWDWFWIBWDWFWEWHVTSZSW
        IWDWEVTWJWDWETWHVTWJUGWDVOCVRWDVOCAVQVQVNIAIVQVQUHUIRVQVQIUJACDEFGHIJKM
        NOPUKIVQVQULUMUNUOUPWHVTUQUMURWEWHVTUSUTVABVOVNVCWFBCVBVDWDWFWABCWDWHTZ
        WEVSVTWKCVNDEFGHIJKVRMNOAIJHVEWCWHPVFWDWHVGAWCWHVHVIVJVKVMVKWALBVQCVLUT
        $.
    $}

    ${
      $d B i j k l m s x $.  $d I k l m x $.  $d ph i j k l s x $.
      $( An interior (closure) function is expansive if and only if all subsets
         which contain a point are neighborhoods (convergents) of that point.
         (Contributed by RP, 11-Jun-2021.) $)
      ntrneix2 $p |- ( ph -> ( A. s e. ~P B s C_ ( I ` s )
                 <-> A. x e. B A. s e. ~P B ( x e. s -> s e. ( N ` x ) ) ) ) $=
        ( wral wcel wi wa cv cfv wss cpw wel wb simpr wal elpwi sselda pm5.74da
        biimt syl bi2.04 bitrdi albidv df-ss df-ral 3bitr4g wbr ad2antrr simplr
        ntrneiel imbi2d ralbidva bitrd ralcom ) ALUAZVHIUBZUCZLCUDZQBLUEZVHBUAZ
        JUBRZSZBCQZLVKQVOLVKQBCQAVJVPLVKAVHVKRZTZVJVLVMVIRZSZBCQZVPVRVQVJWAUFAV
        QUGVQVTBUHVMCRZVTSZBUHVJWAVQVTWCBVQVTVLWBVSSZSWCVQVLVSWDVQVLTWBVSWDUFVQ
        VHCVMVHCUIUJWBVSULUMUKVLWBVSUNUOUPBVHVIUQVTBCURUSUMVRVTVOBCVRWBTZVSVNVL
        WECVHDEFGHIJKVMMNOAIJHUTVQWBPVAVRWBUGAVQWBVBVCVDVEVFVEVOLBVKCVGUO $.
    $}

    ${
      $d B i j k l m s t x $.  $d I k l m x $.  $d ph i j k l s t x $.
      $( The interiors of disjoint sets are disjoint if and only if the
         neighborhoods of every point contain no disjoint sets.  (Contributed
         by RP, 11-Jun-2021.) $)
      ntrneikb $p |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( ( s i^i t ) = (/)
                                        -> ( ( I ` s ) i^i ( I ` t ) ) = (/) )
                 <-> A. x e. B A. s e. ~P B A. t e. ~P B ( ( s e. ( N ` x )
                                                          /\ t e. ( N ` x ) )
                                                      -> ( s i^i t ) =/= (/) )
                             ) ) $=
        ( wi wral wcel cv cin c0 wceq cfv cpw wa wne wal wn con34b albii 19.21v
        nne wss elin imbi1i wb imnot ax-mp bitr2i df-ss 3bitr2i imbi12i 3bitrri
        noel ss0b cmap co ntrneiiex elmapi syl ffvelcdmda adantr elpwid adantrd
        wf sseld imp pm5.74da bi2.04 bitrdi albidv df-ral bitr4di wbr ad3antrrr
        biimt simpr simpllr ntrneiel simplr anbi12d imbi1d bitrd bitrid ralrot3
        ralbidva ) AMUAZCUAZUBZUCUDZWSJUEZWTJUEZUBZUCUDZRZCDUFZSZMXHSWSBUAZKUEZ
        TZWTXKTZUGZXAUCUHZRZBDSZCXHSZMXHSXPCXHSMXHSBDSAXIXRMXHAWSXHTZUGZXGXQCXH
        XGXJXCTZXJXDTZUGZXORZBUIZXTWTXHTZUGZXQYEXOUJZYCUJZRZBUIYHYIBUIZRXGYDYJB
        YCXOUKULYHYIBUMYHXBYKXFXAUCUNYKXJXETZXJUCTZRZBUIXEUCUOXFYIYNBYNYCYMRZYI
        YLYCYMXJXCXDUPUQYMUJYOYIURXJVFYCYMUSUTVAULBXEUCVBXEVGVCVDVEYGYEYDBDSZXQ
        YGYEXJDTZYDRZBUIYPYGYDYRBYGYDYCYQXORZRYRYGYCXOYSYGYCUGYQXOYSURYGYCYQYGY
        AYQYBYGXCDXJYGXCDXTXCXHTYFAXHXHWSJAJXHXHVHVITXHXHJVQADEFGHIJKLNOPQVJJXH
        XHVKVLVMVNVOVRVPVSYQXOWHVLVTYCYQXOWAWBWCYDBDWDWEYGYDXPBDYGYQUGZYCXNXOYT
        YAXLYBXMYTDWSEFGHIJKLXJNOPAJKIWFXSYFYQQWGZYGYQWIZAXSYFYQWJWKYTDWTEFGHIJ
        KLXJNOPUUAUUBXTYFYQWLWKWMWNWRWOWPWRWRXPMCBXHXHDWQWB $.
    $}

    ${
      $d B i j k l m s t x $.  $d I k l m x $.  $d ph i j k l s t x $.
      $( The interiors (closures) of sets that span the base set also span the
         base set if and only if the neighborhoods (convergents) of every point
         contain at least one of every pair of sets that span the base set.
         (Contributed by RP, 11-Jun-2021.) $)
      ntrneixb $p |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( ( s u. t ) = B
                                        -> ( ( I ` s ) u. ( I ` t ) ) = B )
                 <-> A. x e. B A. s e. ~P B A. t e. ~P B ( ( s u. t ) = B
                                    -> ( s e. ( N ` x ) \/ t e. ( N ` x ) ) )
                             ) ) $=
        ( wral wcel wa cv cun wceq cfv wi cpw wo wss wb eqss a1i cmap ntrneiiex
        co wf elmapi syl ffvelcdmda elpwid adantr adantlr unssd biantrurd dfss3
        elun ralbii bitri 3bitr2d imbi2d r19.21v wbr ad3antrrr simpllr ntrneiel
        simpr simplr orbi12d ralbidva ralrot3 bitrdi ) AMUAZCUAZUBDUCZWAJUDZWBJ
        UDZUBZDUCZUEZCDUFZRZMWIRWCWABUAZKUDZSZWBWLSZUGZUEZBDRZCWIRZMWIRWPCWIRMW
        IRBDRAWJWRMWIAWAWISZTZWHWQCWIWTWBWISZTZWHWCWKWDSZWKWESZUGZBDRZUEZWCXEUE
        ZBDRZWQXBWGXFWCXBWGWFDUHZDWFUHZTZXKXFWGXLUIXBWFDUJUKXBXJXKXBWDWEDWTWDDU
        HXAWTWDDAWIWIWAJAJWIWIULUNSWIWIJUOADEFGHIJKLNOPQUMJWIWIUPUQZURUSUTAXAWE
        DUHWSAXATWEDAWIWIWBJXMURUSVAVBVCXKXFUIXBXKWKWFSZBDRXFBDWFVDXNXEBDWKWDWE
        VEVFVGUKVHVIXIXGUIXBWCXEBDVJUKXBXHWPBDXBWKDSZTZXEWOWCXPXCWMXDWNXPDWAEFG
        HIJKLWKNOPAJKIVKWSXAXOQVLZXBXOVOZAWSXAXOVMVNXPDWBEFGHIJKLWKNOPXQXRWTXAX
        OVPVNVQVIVRVHVRVRWPMCBWIWIDVSVT $.
    $}

    ${
      $d B i j k l m s t x $.  $d I k l m x $.  $d ph i j k l s t x $.
      $( The intersection of interiors of any pair is a subset of the interior
         of the intersection if and only if the intersection of any two
         neighborhoods of a point is also a neighborhood.  (Contributed by RP,
         19-Jun-2021.) $)
      ntrneik3 $p |- ( ph -> ( A. s e. ~P B A. t e. ~P B
                               ( ( I ` s ) i^i ( I ` t ) )
                               C_ ( I ` ( s i^i t ) )
                 <-> A. x e. B A. s e. ~P B A. t e. ~P B
                               ( ( s e. ( N ` x ) /\ t e. ( N ` x ) )
                              -> ( s i^i t ) e. ( N ` x ) ) ) ) $=
        ( wss wral wcel cv cfv cin cpw wa wi dfss3 wb cmap ntrneiiex elmapi syl
        co wf ffvelcdmda elpwid ssinss1 adantr ralss elin wbr ad3antrrr simpllr
        simpr ntrneiel simplr anbi12d bitrid ntrneibex sselpwd imbi12d ralbidva
        cvv bitrd ralcom bitrdi ) AMUAZJUBZCUAZJUBZUCZVQVSUCZJUBZRZCDUDZSZMWESV
        QBUAZKUBZTZVSWHTZUEZWBWHTZUFZCWESZBDSZMWESWNMWESBDSAWFWOMWEAVQWETZUEZWF
        WMBDSZCWESWOWQWDWRCWEWDWGWCTZBWASZWQVSWETZUEZWRBWAWCUGXBWTWGWATZWSUFZBD
        SZWRXBWADRZWTXEUHWQXFXAWQVRDRXFWQVRDAWEWEVQJAJWEWEUIUMTWEWEJUNADEFGHIJK
        LNOPQUJJWEWEUKULUOUPVRVTDUQULURWSBWADUSULXBXDWMBDXBWGDTZUEZXCWKWSWLXCWG
        VRTZWGVTTZUEXHWKWGVRVTUTXHXIWIXJWJXHDVQEFGHIJKLWGNOPAJKIVAWPXAXGQVBZXBX
        GVDZAWPXAXGVCZVEXHDVSEFGHIJKLWGNOPXKXLWQXAXGVFVEVGVHXHDWBEFGHIJKLWGNOPX
        KXLXHWBDVMADVMTWPXAXGADEFGHIJKLNOPQVIVBXHVQDRWBDRXHVQDXMUPVQVSDUQULVJVE
        VKVLVNVHVLWMCBWEDVOVPVLWNMBWEDVOVP $.
    $}

    ${
      $d B i j k l m s t x $.  $d I k l m x $.  $d ph i j k l s t x $.
      $( The closure of the union of any pair is a subset of the union of
         closures if and only if the union of any pair belonging to the
         convergents of a point implies at least one of the pair belongs to the
         the convergents of that point.  (Contributed by RP, 19-Jun-2021.) $)
      ntrneix3 $p |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( I ` ( s u. t ) )
                                                 C_ ( ( I ` s ) u. ( I ` t ) )
                 <-> A. x e. B A. s e. ~P B A. t e. ~P B
                                ( ( s u. t ) e. ( N ` x )
                               -> ( s e. ( N ` x ) \/ t e. ( N ` x ) ) ) ) ) $=
        ( wral wcel elpwid cv cun cfv wss cpw wo wi wa dfss3 wb co wf ntrneiiex
        cmap ad2antrr elmapi syl ntrneibex simplr simpr unssd sselpwd ffvelcdmd
        cvv wbr ad3antrrr simpllr ntrneiel elun orbi12d bitrid imbi12d ralbidva
        ralss bitrd ralcom bitrdi ) AMUAZCUAZUBZJUCZVRJUCZVSJUCZUBZUDZCDUEZRZMW
        FRVTBUAZKUCZSZVRWISZVSWISZUFZUGZCWFRZBDRZMWFRWOMWFRBDRAWGWPMWFAVRWFSZUH
        ZWGWNBDRZCWFRWPWRWEWSCWFWEWHWDSZBWARZWRVSWFSZUHZWSBWAWDUIXCXAWHWASZWTUG
        ZBDRZWSXCWADUDXAXFUJXCWADXCWFWFVTJXCJWFWFUNUKSZWFWFJULAXGWQXBADEFGHIJKL
        NOPQUMUOJWFWFUPUQXCVTDVDADVDSZWQXBADEFGHIJKLNOPQURZUOXCVRVSDXCVRDAWQXBU
        STXCVSDWRXBUTTVAVBVCTWTBWADVNUQXCXEWNBDXCWHDSZUHZXDWJWTWMXKDVTEFGHIJKLW
        HNOPAJKIVEWQXBXJQVFZXCXJUTZXKVTDVDAXHWQXBXJXIVFXKVRVSDXKVRDAWQXBXJVGZTX
        KVSDWRXBXJUSZTVAVBVHWTWHWBSZWHWCSZUFXKWMWHWBWCVIXKXPWKXQWLXKDVREFGHIJKL
        WHNOPXLXMXNVHXKDVSEFGHIJKLWHNOPXLXMXOVHVJVKVLVMVOVKVMWNCBWFDVPVQVMWOMBW
        FDVPVQ $.
    $}

    ${
      $d B i j k l m s t x $.  $d I k l m x $.  $d ph i j k l s t x $.
      $( The interior of the intersection of any pair equals intersection of
         interiors if and only if the intersection of any pair belonging to the
         neighborhood of a point is equivalent to both of the pair belonging to
         the neighborhood of that point.  (Contributed by RP, 19-Jun-2021.) $)
      ntrneik13 $p |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( I ` ( s i^i t ) ) =
                                                    ( ( I ` s ) i^i ( I ` t ) )
                  <-> A. x e. B A. s e. ~P B A. t e. ~P B
                                ( ( s i^i t ) e. ( N ` x )
                              <-> ( s e. ( N ` x ) /\ t e. ( N ` x ) ) ) ) ) $=
        ( wral wcel wa cv cin cfv wceq cpw wb wss wi dfss3 wf cmap co ntrneiiex
        elmapi syl ad2antrr cvv ntrneibex simplr ssinss1 3syl sselpwd ffvelcdmd
        elpwi elpwid ralss bitrid ffvelcdmda adantr anbi12d ralbiim 3bitr4g wbr
        eqss ad3antrrr simpr ntrneiel elin simpllr ralbidva bitrd ralcom bitrdi
        bibi12d ) AMUAZCUAZUBZJUCZWEJUCZWFJUCZUBZUDZCDUEZRZMWMRWGBUAZKUCZSZWEWP
        SZWFWPSZTZUFZCWMRZBDRZMWMRXBMWMRBDRAWNXCMWMAWEWMSZTZWNXABDRZCWMRXCXEWLX
        FCWMXEWFWMSZTZWLWOWHSZWOWKSZUFZBDRZXFXHWHWKUGZWKWHUGZTXIXJUHBDRZXJXIUHB
        DRZTWLXLXHXMXOXNXPXMXJBWHRZXHXOBWHWKUIXHWHDUGXQXOUFXHWHDXHWMWMWGJAWMWMJ
        UJZXDXGAJWMWMUKULSXRADEFGHIJKLNOPQUMJWMWMUNUOZUPXHWGDUQADUQSZXDXGADEFGH
        IJKLNOPQURZUPXHXDWEDUGZWGDUGZAXDXGUSWEDVDWEWFDUTZVAVBVCVEXJBWHDVFUOVGXN
        XIBWKRZXHXPBWKWHUIXHWKDUGZYEXPUFXEYFXGXEWIDUGYFXEWIDAWMWMWEJXSVHVEWIWJD
        UTUOVIXIBWKDVFUOVGVJWHWKVNXIXJBDVKVLXHXKXABDXHWODSZTZXIWQXJWTYHDWGEFGHI
        JKLWONOPAJKIVMXDXGYGQVOZXHYGVPZXEWGWMSXGYGXEWGDUQAXTXDYAVIXEYBYCXEWEDAX
        DVPVEYDUOVBUPVQXJWOWISZWOWJSZTYHWTWOWIWJVRYHYKWRYLWSYHDWEEFGHIJKLWONOPY
        IYJAXDXGYGVSVQYHDWFEFGHIJKLWONOPYIYJXEXGYGUSVQVJVGWDVTWAVTXACBWMDWBWCVT
        XBMBWMDWBWC $.
    $}

    ${
      $d B i j k l m s t x $.  $d I k l m x $.  $d ph i j k l s t x $.
      $( The closure of the union of any pair is equal to the union of closures
         if and only if the union of any pair belonging to the convergents of a
         point if equivalent to at least one of the pain belonging to the
         convergents of that point.  (Contributed by RP, 19-Jun-2021.) $)
      ntrneix13 $p |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( I ` ( s u. t ) )
                                                   = ( ( I ` s ) u. ( I ` t ) )
                  <-> A. x e. B A. s e. ~P B A. t e. ~P B
                                ( ( s u. t ) e. ( N ` x )
                              <-> ( s e. ( N ` x ) \/ t e. ( N ` x ) ) ) ) ) $=
        ( wral wcel elpwid cv cun cfv wceq cpw wo wb wa wss wi dfss3 cmap co wf
        ntrneiiex elmapi syl cvv ntrneibex simplr simpr unssd sselpwd ffvelcdmd
        ad2antrr ralss bitrid anbi12d eqss ralbiim 3bitr4g wbr simpllr ntrneiel
        ad3antrrr elun orbi12d bibi12d ralbidva bitrd ralcom bitrdi ) AMUAZCUAZ
        UBZJUCZWCJUCZWDJUCZUBZUDZCDUEZRZMWKRWEBUAZKUCZSZWCWNSZWDWNSZUFZUGZCWKRZ
        BDRZMWKRWTMWKRBDRAWLXAMWKAWCWKSZUHZWLWSBDRZCWKRXAXCWJXDCWKXCWDWKSZUHZWJ
        WMWFSZWMWISZUGZBDRZXDXFWFWIUIZWIWFUIZUHXGXHUJBDRZXHXGUJBDRZUHWJXJXFXKXM
        XLXNXKXHBWFRZXFXMBWFWIUKXFWFDUIXOXMUGXFWFDXFWKWKWEJXFJWKWKULUMSZWKWKJUN
        AXPXBXEADEFGHIJKLNOPQUOVEJWKWKUPUQZXFWEDURADURSZXBXEADEFGHIJKLNOPQUSZVE
        XFWCWDDXFWCDAXBXEUTZTXFWDDXCXEVAZTVBVCVDTXHBWFDVFUQVGXLXGBWIRZXFXNBWIWF
        UKXFWIDUIYBXNUGXFWGWHDXFWGDXFWKWKWCJXQXTVDTXFWHDXFWKWKWDJXQYAVDTVBXGBWI
        DVFUQVGVHWFWIVIXGXHBDVJVKXFXIWSBDXFWMDSZUHZXGWOXHWRYDDWEEFGHIJKLWMNOPAJ
        KIVLXBXEYCQVOZXFYCVAZYDWEDURAXRXBXEYCXSVOYDWCWDDYDWCDAXBXEYCVMZTYDWDDXC
        XEYCUTZTVBVCVNXHWMWGSZWMWHSZUFYDWRWMWGWHVPYDYIWPYJWQYDDWCEFGHIJKLWMNOPY
        EYFYGVNYDDWDEFGHIJKLWMNOPYEYFYHVNVQVGVRVSVTVSWSCBWKDWAWBVSWTMBWKDWAWB
        $.
    $}

    ${
      $d B i j k l m s x $.  $d I k l m x $.  $d ph i j k l s x $.
      $( Idempotence of the interior function is equivalent to saying a set is
         a neighborhood of a point if and only if the interior of the set is a
         neighborhood of a point.  (Contributed by RP, 11-Jul-2021.) $)
      ntrneik4w $p |- ( ph -> ( A. s e. ~P B ( I ` ( I ` s ) ) = ( I ` s )
              <-> A. x e. B A. s e. ~P B (
              s e. ( N ` x ) <-> ( I ` s ) e. ( N ` x ) ) ) ) $=
        ( wral wcel cvv adantr cv cfv wceq cpw wb wal dfcleq eqcom ralv 3bitr4i
        wa wss ssv a1i cdif wn vex eldif mpbiran co ntrneiiex elmapi ffvelcdmda
        cmap wf syl sseld con3dimp ffvelcdmd 2falsed biimtrid ralrimiv raldifeq
        elpwid ex wbr simpr simplr ntrneiel bibi12d bitr3d bitrid ralcom bitrdi
        ralbidva ) ALUAZIUBZIUBZWGUCZLCUDZQWFBUAZJUBZRZWGWLRZUEZBCQZLWJQWOLWJQB
        CQAWIWPLWJWIWKWGRZWKWHRZUEZBSQZAWFWJRZUKZWPWGWHUCWSBUFWIWTBWGWHUGWHWGUH
        WSBUIUJXBWSBCQWTWPXBWSBCSCSULXBCUMUNXBWSBSCUOZWKXCRZWKCRZUPZXBWSXDWKSRX
        FBUQWKSCURUSXBXFWSXBXFUKWQWRXBWQXEXBWGCWKXBWGCAWJWJWFIAIWJWJVDUTRWJWJIV
        EZACDEFGHIJKMNOPVAIWJWJVBVFZVCZVNVGVHXBWRXEXBWHCWKXBWHCXBWJWJWGIAXGXAXH
        TXIVIVNVGVHVJVOVKVLVMXBWSWOBCXBXEUKZWQWMWRWNXJCWFDEFGHIJKWKMNOXBIJHVPZX
        EAXKXAPTTZXBXEVQZAXAXEVRVSXJCWGDEFGHIJKWKMNOXLXMXBWGWJRXEXITVSVTWEWAWBW
        EWOLBWJCWCWD $.
    $}

    ${
      $d B i j k l m s x y $.  $d I k l m x y $.  $d ph i j k l s x $.
      $d B s x u y $.  $d N u y $.  $d ph u y $.
      $( Idempotence of the interior function is equivalent to stating a set,
         ` s ` , is a neighborhood of a point, ` x ` is equivalent to there
         existing a special neighborhood, ` u ` , of ` x ` such that a point is
         an element of the special neighborhood if and only if ` s ` is also a
         neighborhood of the point.  (Contributed by RP, 11-Jul-2021.) $)
      ntrneik4 $p |- ( ph -> ( A. s e. ~P B ( I ` ( I ` s ) ) = ( I ` s )
              <-> A. x e. B A. s e. ~P B
              ( s e. ( N ` x ) <-> E. u e. ( N ` x ) A. y e. B
                                    ( y e. u <-> s e. ( N ` y ) ) ) ) ) $=
        ( wral wcel cv cfv wceq cpw wel wrex ntrneik4w wbr ad2antrr simplr cmap
        wb wa ntrneiiex elmapi syl ffvelcdmda adantlr ntrneiel ntrneiel2 bitr3d
        co wf simpr bibi2d ralbidva bitrd ) ANUAZKUBZKUBZVIUCNEUDZSVHBUAZLUBZTZ
        VIVMTZULZNVKSZBESVNCDUEVHCUALUBTULCESDVMUFZULZNVKSZBESABEFGHIJKLMNOPQRU
        GAVQVTBEAVLETZUMZVPVSNVKWBVHVKTZUMZVOVRVNWDVLVJTVOVRWDEVIFGHIJKLMVLOPQA
        KLJUHWAWCRUIZAWAWCUJZAWCVIVKTWAAVKVKVHKAKVKVKUKVBTVKVKKVCAEFGHIJKLMOPQR
        UNKVKVKUOUPUQURUSWDCDEVHFGHIJKLMVLOPQWEWFWBWCVDUTVAVEVFVFVG $.
    $}
  $}

  ${
    clsneibex.d $e |- D = ( P ` B ) $.
    clsneibex.h $e |- H = ( F o. D ) $.
    clsneibex.r $e |- ( ph -> K H N ) $.
    $( If (pseudo-)closure and (pseudo-)neighborhood functions are related by
       the composite operator, ` H ` , then the base set exists.  (Contributed
       by RP, 4-Jun-2021.) $)
    clsneibex $p |- ( ph -> B e. _V ) $=
      ( cfv ccom wbr c0 wne cvv crn cin eqtrdi wcel wceq coeq2i eqtri a1i brne0
      breqdi wn cdm fvprc rneqd rn0 ineq2d in0 coemptyd necon1ai 3syl ) AGHEBDL
      ZMZNUSOPBQUAZAFUSGHFUSUBAFECMUSJCUREIUCUDUEKUGGHUSUFUTUSOUTUHZEURVAEUIZUR
      RZSVBOSOVAVCOVBVAVCOROVAUROBDUJUKULTUMVBUNTUOUPUQ $.

    $( The relative complement of the class ` S ` exists as a subset of the
       base set.  (Contributed by RP, 26-Jun-2021.) $)
    clsneircomplex $p |- ( ph -> ( B \ S ) e. ~P B ) $=
      ( cdif cvv clsneibex difssd sselpwd ) ABEMBNABCDFGHIJKLOABEPQ $.
  $}

  ${
    clsnei.o $e |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |->
                         ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) ) $.
    clsnei.p $e |- P = ( n e. _V |-> ( p e. ( ~P n ^m ~P n ) |->
                        ( o e. ~P n |-> ( n \ ( p ` ( n \ o ) ) ) ) ) ) $.
    clsnei.d $e |- D = ( P ` B ) $.
    clsnei.f $e |- F = ( ~P B O B ) $.
    clsnei.h $e |- H = ( F o. D ) $.
    clsnei.r $e |- ( ph -> K H N ) $.

    ${
      $d B i j k l m $.  $d B n o p $.  $d ph i j k l $.  $d ph n o p $.
      $( If a (pseudo-)closure function and a (pseudo-)neighborhood function
         are related by the ` H ` operator, then the operator is a one-to-one,
         onto mapping.  (Contributed by RP, 5-Jun-2021.) $)
      clsneif1o $p |- ( ph -> H : ( ~P B ^m ~P B )
                                   -1-1-onto-> ( ~P ~P B ^m B ) ) $=
        ( cpw cmap co cfv ccom wf1o cvv wcel clsneibex wa pwexg adantl fsovf1od
        simpr eqid dssmapf1od f1oco syl2anc mpdan wb coeq12i eqtri f1oeq1 ax-mp
        wceq sylibr ) ABUDZVJUEUFZVJUDBUEUFZVJBOUFZBDUGZUHZUIZVKVLLUIZABUJUKZVP
        ABCDKLMNTUBUCULAVRUMZVKVLVMUIVKVKVNUIVPVSHQVJBGVMOUJUJEFRVRVJUJUKABUJUN
        UOAVRUQZVMURUPVSBVNPDUJJISVNURVTUSVKVKVLVMVNUTVAVBLVOVHVQVPVCLKCUHVOUBK
        VMCVNUATVDVEVKVLLVOVFVGVI $.
    $}

    ${
      $d B i j k l m $.  $d B n o p $.  $d ph i j k l $.  $d ph n o p $.
      $( If a (pseudo-)closure function and a (pseudo-)neighborhood function
         are related by the ` H ` operator, then the converse of the operator
         is known.  (Contributed by RP, 5-Jun-2021.) $)
      clsneicnv $p |- ( ph -> `' H = ( D o. ( B O ~P B ) ) ) $=
        ( ccnv ccom cpw co cnveqi cnvco eqtri wcel wceq clsneibex wa dssmapnvod
        cvv simpr pwexg adantl eqid fsovcnvd coeq12d mpdan eqtrid ) ALUDZCUDZKU
        DZUEZCBBUFZOUGZUEZVEKCUEZUDVHLVLUBUHKCUIUJABUPUKZVHVKULABCDKLMNTUBUCUMA
        VMUNZVFCVGVJVNBCPDUPJISTAVMUQZUOVNHQVIBGKVJOUPUPEFRVMVIUPUKABUPURUSVOUA
        VJUTVAVBVCVD $.
    $}

    ${
      $d B i j k l m $.  $d B n o p $.  $d ph i j k l $.  $d ph n o p $.
      $( If closure and neighborhoods functions are related, the closure
         function exists.  (Contributed by RP, 27-Jun-2021.) $)
      clsneikex $p |- ( ph -> K e. ( ~P B ^m ~P B ) ) $=
        ( cfv wbr cvv wcel wa clsneibex cpw cmap co wf1o wfn pwexg adantl simpr
        fsovf1od f1ofn wf dssmapf1od f1of ccom adantr breqi sylib brcoffn mpdan
        syl simpld ntrclsiex ) ABCIJPMMCUDZDSTAMVLCUEZVLNKUEZABUFUGZVMVNUHABCDK
        LMNTUBUCUIAVOUHZMNKCBUJZVQUKULZVRVPVRVQUJBUKULZKUMKVRUNVPHQVQBGKOUFUFEF
        RVOVQUFUGABUFUOUPAVOUQZUAURVRVSKUSVIVPVRVRCUMVRVRCUTVPBCPDUFJISTVTVAVRV
        RCVBVIVPMNLUEZMNKCVCZUEAWAVOUCVDMNLWBUBVEVFVGVHVJVK $.
    $}

    ${
      $d B i j k l m $.  $d B n o p $.  $d ph i j k l $.  $d ph n o p $.
      $( If closure and neighborhoods functions are related, the neighborhoods
         function exists.  (Contributed by RP, 27-Jun-2021.) $)
      clsneinex $p |- ( ph -> N e. ( ~P ~P B ^m B ) ) $=
        ( cfv wbr cvv wcel wa clsneibex cpw cmap co wf1o wfn pwexg adantl simpr
        fsovf1od f1ofn wf dssmapf1od f1of ccom adantr breqi sylib brcoffn mpdan
        syl simprd ntrneinex ) ABEFGHKMCUDZNOQRUAAMVLCUEZVLNKUEZABUFUGZVMVNUHAB
        CDKLMNTUBUCUIAVOUHZMNKCBUJZVQUKULZVRVPVRVQUJBUKULZKUMKVRUNVPHQVQBGKOUFU
        FEFRVOVQUFUGABUFUOUPAVOUQZUAURVRVSKUSVIVPVRVRCUMVRVRCUTVPBCPDUFJISTVTVA
        VRVRCVBVIVPMNLUEZMNKCVCZUEAWAVOUCVDMNLWBUBVEVFVGVHVJVK $.
    $}

    ${
      clsneiel.x $e |- ( ph -> X e. B ) $.
      clsneiel.s $e |- ( ph -> S e. ~P B ) $.
      ${
        $d B i j k l m $.  $d B n o p $.  $d D i j k l m $.  $d D n o p $.
        $d F i j k l $.  $d F n o p $.  $d K i j k l m $.  $d K n o p $.
        $d N i j k l $.  $d N n o p $.  $d S m $.  $d S o $.  $d X l m $.
        $d ph i j k l $.  $d ph n o p $.
        $( If a (pseudo-)closure function and a (pseudo-)neighborhood function
           are related by the ` H ` operator, then membership in the closure of
           a subset is equivalent to the complement of the subset not being a
           neighborhood of the point.  (Contributed by RP, 7-Jun-2021.) $)
        clsneiel1 $p |- ( ph -> ( X e. ( K ` S )
                                  <-> -. ( B \ S ) e. ( N ` X ) ) ) $=
          ( cvv wcel wa cfv wbr cdif wn wb clsneibex ancli cpw cmap simpr pwexd
          co fsovfd ffnd wf1o wf dssmapf1od f1of syl breqi sylib adantr brcoffn
          ccom simprl ad2antrr ntrclselnel1 simprr simplr difssd sselpwd notbid
          ntrneiel bitrd syl2anc2 ) AABUHUIZUJZNNCUKZCULZWHOLULZUJZQENUKUIZBEUM
          ZQOUKUIZUNZUOAWFABCDLMNOUBUDUEUPUQWGNOLCBURZWPUSVBZWQWGWQWPURBUSVBLWG
          ISWPBHLPUHUHFGTWGBUHAWFUTZVAWRUCVCVDWGWQWQCVEWQWQCVFWGBCRDUHKJUAUBWRV
          GWQWQCVHVIANOLCVNZULZWFANOMULWTUENOMWSUDVJVKVLVMWGWKUJZWLQWMWHUKUIZUN
          WOXABCEJKRNWHDQUAUBWGWIWJVOAQBUIWFWKUFVPZAEWPUIWFWKUGVPVQXAXBWNXABWMF
          GHILWHOPQSTUCWGWIWJVRXCXAWMBUHAWFWKVSXABEVTWAWCWBWDWE $.
      $}

      ${
        $d B i j k l m $.  $d B n o p $.  $d D i j k l m $.  $d D n o p $.
        $d F i j k l $.  $d F n o p $.  $d K i j k l m $.  $d K n o p $.
        $d N i j k l $.  $d N n o p $.  $d S m $.  $d S o $.  $d X l m $.
        $d ph i j k l $.  $d ph n o p $.
        $( If a (pseudo-)closure function and a (pseudo-)neighborhood function
           are related by the ` H ` operator, then membership in the closure of
           the complement of a subset is equivalent to the subset not being a
           neighborhood of the point.  (Contributed by RP, 7-Jun-2021.) $)
        clsneiel2 $p |- ( ph -> ( X e. ( K ` ( B \ S ) )
                                  <-> -. S e. ( N ` X ) ) ) $=
          ( cdif cfv wcel clsneircomplex clsneiel1 wss wceq elpwid dfss4 eleq1d
          wn sylib notbid bitrd ) AQBEUHZNUIUJBVBUHZQOUIZUJZUREVDUJZURABCDVBFGH
          IJKLMNOPQRSTUAUBUCUDUEUFABCDELMNOUBUDUEUKULAVEVFAVCEVDAEBUMVCEUNAEBUG
          UOEBUPUSUQUTVA $.
      $}
    $}

    ${
      $d B i j k l m s $.  $d B n o p s $.  $d D i j k l m $.  $d D n o p $.
      $d F i j k l $.  $d F n o p $.  $d K i j k l m $.  $d K n o p $.
      $d N i j k l s $.  $d N n o p s $.  $d X l m s $.  $d ph i j k l s $.
      $d ph n o p s $.
      clsneifv.x $e |- ( ph -> X e. B ) $.
      $( Value of the neighborhoods (convergents) in terms of the closure
         (interior) function.  (Contributed by RP, 27-Jun-2021.) $)
      clsneifv3 $p |- ( ph -> ( N ` X )
                              = { s e. ~P B | -. X e. ( K ` ( B \ s ) ) } ) $=
        ( cpw cfv cin cv wcel crab cdif wn dfin5 wss wceq cmap clsneinex elmapi
        co wf syl ffvelcdmd elpwid sseqin2 sylib wa wbr simpr clsneiel2 con2bid
        adantr rabbidva 3eqtr3a ) ABUGZPNUHZUIZQUJZVQUKZQVPULVQPBVSUMMUHUKZUNZQ
        VPULQVPVQUOAVQVPUPVRVQUQAVQVPABVPUGZPNANWCBURVAUKBWCNVBABCDEFGHIJKLMNOR
        STUAUBUCUDUEUSNWCBUTVCUFVDVEVQVPVFVGAVTWBQVPAVSVPUKZVHZWAVTWEBCDVSEFGHI
        JKLMNOPRSTUAUBUCUDAMNLVIWDUEVMAPBUKWDUFVMAWDVJVKVLVNVO $.
    $}

    ${
      $d B i j k l m x $.  $d B n o p x $.  $d D i j k l m $.  $d D n o p $.
      $d F i j k l $.  $d F n o p $.  $d K i j k l m x $.  $d K n o p x $.
      $d N i j k l $.  $d N n o p $.  $d S m x $.  $d S o x $.
      $d ph i j k l x $.  $d ph n o p x $.
      clsneifv.s $e |- ( ph -> S e. ~P B ) $.
      $( Value of the closure (interior) function in terms of the neighborhoods
         (convergents) function.  (Contributed by RP, 27-Jun-2021.) $)
      clsneifv4 $p |- ( ph -> ( K ` S )
                              = { x e. B | -. ( B \ S ) e. ( N ` x ) } ) $=
        ( cfv cin cv wcel crab cdif wn dfin5 wss wceq cpw cmap clsneikex elmapi
        co wf ffvelcdmd elpwid sseqin2 sylib wa adantr simpr clsneiel1 rabbidva
        syl wbr 3eqtr3a ) ACFOUGZUHZBUIZVOUJZBCUKVOCFULVQPUGUJUMZBCUKBCVOUNAVOC
        UOVPVOUPAVOCACUQZVTFOAOVTVTURVAUJVTVTOVBACDEGHIJKLMNOPQRSTUAUBUCUDUEUSO
        VTVTUTVLUFVCVDVOCVEVFAVRVSBCAVQCUJZVGCDEFGHIJKLMNOPQVQRSTUAUBUCUDAOPNVM
        WAUEVHAWAVIAFVTUJWAUFVHVJVKVN $.
    $}
  $}

  ${
    neicvgbex.d $e |- D = ( P ` B ) $.
    neicvgbex.h $e |- H = ( F o. ( D o. G ) ) $.
    neicvgbex.r $e |- ( ph -> N H M ) $.
    $( If (pseudo-)neighborhood and (pseudo-)convergent functions are related
       by the composite operator, ` H ` , then the base set exists.
       (Contributed by RP, 4-Jun-2021.) $)
    neicvgbex $p |- ( ph -> B e. _V ) $=
      ( cfv ccom c0 cdm crn cin eqtrdi coemptyd wbr wne wcel wceq coeq1i coeq2i
      cvv eqtri a1i breqdi brne0 wn fvprc dmeqd dm0 ineq1d 0in rneqd rn0 ineq2d
      in0 necon1ai 3syl ) AIHEBDMZFNZNZUAVFOUBBUGUCZAGVFIHGVFUDAGECFNZNVFKVHVEE
      CVDFJUEUFUHUILUJIHVFUKVGVFOVGULZEVEVIEPZVEQZRVJOROVIVKOVJVIVKOQOVIVEOVIVD
      FVIVDPZFQZROVMROVIVLOVMVIVLOPOVIVDOBDUMUNUOSUPVMUQSTURUSSUTVJVASTVBVC $.

    $( The relative complement of the class ` S ` exists as a subset of the
       base set.  (Contributed by RP, 26-Jun-2021.) $)
    neicvgrcomplex $p |- ( ph -> ( B \ S ) e. ~P B ) $=
      ( cdif cvv neicvgbex difssd sselpwd ) ABENBOABCDFGHIJKLMPABEQR $.
  $}

  ${
    neicvg.o $e |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |->
                         ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) ) $.
    neicvg.p $e |- P = ( n e. _V |-> ( p e. ( ~P n ^m ~P n ) |->
                        ( o e. ~P n |-> ( n \ ( p ` ( n \ o ) ) ) ) ) ) $.
    neicvg.d $e |- D = ( P ` B ) $.
    neicvg.f $e |- F = ( ~P B O B ) $.
    neicvg.g $e |- G = ( B O ~P B ) $.
    neicvg.h $e |- H = ( F o. ( D o. G ) ) $.
    neicvg.r $e |- ( ph -> N H M ) $.

    ${
      $d B i j k l m $.  $d B n o p $.  $d ph i j k l $.  $d ph n o p $.
      $( If neighborhood and convergent functions are related by operator
         ` H ` , it is a one-to-one onto relation.  (Contributed by RP,
         11-Jun-2021.) $)
      neicvgf1o $p |- ( ph -> H : ( ~P ~P B ^m B )
                                   -1-1-onto-> ( ~P ~P B ^m B ) ) $=
        ( cpw cmap co ccom wf1o cvv neicvgbex pwexd fsovf1od dssmapf1od syl2anc
        f1oco wceq wb f1oeq1 ax-mp sylibr ) ABUFZUFBUGUHZVDKCLUIZUIZUJZVDVDMUJZ
        AVCVCUGUHZVDKUJVDVIVEUJZVGAHRVCBGKPUKUKEFSABUKABCDKLMNOUAUDUEULZUMZVKUB
        UNAVIVICUJVDVILUJVJABCQDUKJITUAVKUOAHRBVCGLPUKUKEFSVKVLUCUNVDVIVICLUQUP
        VDVIVDKVEUQUPMVFURVHVGUSUDVDVDMVFUTVAVB $.
    $}

    ${
      $d B i j k l m $.  $d B n o p $.  $d ph i j k l $.  $d ph n o p $.
      $( If neighborhood and convergent functions are related by operator
         ` H ` , it is its own converse function.  (Contributed by RP,
         11-Jun-2021.) $)
      neicvgnvo $p |- ( ph -> `' H = H ) $=
        ( ccnv ccom cnveqi cnvco coeq1i 3eqtri cpw cvv neicvgbex pwexd fsovcnvd
        dssmapnvod coeq12d eqtrid coass eqtr4i eqtrdi ) AMUFZKCUGZLUGZMAVCLUFZC
        UFZUGZKUFZUGZVEVCKCLUGZUGZUFVKUFZVIUGVJMVLUDUHKVKUIVMVHVICLUIUJUKAVHVDV
        ILAVFKVGCAHRBBULZGLKPUMUMEFSABCDKLMNOUAUDUEUNZABUMVOUOZUCUBUPABCQDUMJIT
        UAVOUQURAHRVNBGKLPUMUMEFSVPVOUBUCUPURUSVEVLMKCLUTUDVAVB $.
    $}

    ${
      $d B i j k l m $.  $d B n o p $.  $d ph i j k l $.  $d ph n o p $.
      $( If neighborhood and convergent functions are related by operator
         ` H ` , the relationship holds with the functions swapped.
         (Contributed by RP, 11-Jun-2021.) $)
      neicvgnvor $p |- ( ph -> M H N ) $=
        ( ccnv wbr neicvgnvo breqd mpbird wrel ccom relco releqi mpbir relbrcnv
        sylib ) AONMUFZUGZNOMUGAUSONMUGUEAURMONABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUH
        UIUJONMMUKKCLULZULZUKKUTUMMVAUDUNUOUPUQ $.
    $}

    ${
      $d B i j k l m $.  $d B n o p $.  $d ph i j k l $.  $d ph n o p $.
      $( If the neighborhoods and convergents functions are related, the
         convergents function exists.  (Contributed by RP, 27-Jun-2021.) $)
      neicvgmex $p |- ( ph -> M e. ( ~P ~P B ^m B ) ) $=
        ( cfv wbr cvv wcel w3a neicvgbex wa cpw cmap co wf1o pwexg adantl simpr
        wfn fsovf1od f1ofn syl dssmapf1od f1of fsovfd ccom breqi sylib brcofffn
        wf adantr mpdan simp3d ntrneinex ) ABEFGHKOLUFZCUFZNPRSUBAOVPLUGZVPVQCU
        GZVQNKUGZABUHUIZVRVSVTUJABCDKLMNOUAUDUEUKAWAULZONKCLBUMZUMBUNUOZWCWCUNU
        OZWEWBWEWDKUPKWEUTWBHRWCBGKPUHUHEFSWAWCUHUIABUHUQURZAWAUSZUBVAWEWDKVBVC
        WBWEWECUPWEWECVKWBBCQDUHJITUAWGVDWEWECVEVCWBHRBWCGLPUHUHEFSWGWFUCVFAONK
        CLVGVGZUGZWAAONMUGWIUEONMWHUDVHVIVLVJVMVNVO $.
    $}

    ${
      $d B i j k l m $.  $d B n o p $.  $d ph i j k l $.  $d ph n o p $.
      $( If the neighborhoods and convergents functions are related, the
         neighborhoods function exists.  (Contributed by RP, 27-Jun-2021.) $)
      neicvgnex $p |- ( ph -> N e. ( ~P ~P B ^m B ) ) $=
        ( neicvgnvor neicvgmex ) ABCDEFGHIJKLMONPQRSTUAUBUCUDABCDEFGHIJKLMNOPQR
        STUAUBUCUDUEUFUG $.
    $}

    ${
      neicvgel.x $e |- ( ph -> X e. B ) $.
      neicvgel.s $e |- ( ph -> S e. ~P B ) $.
      ${
        $d B i j k l m $.  $d B n o p $.  $d D i j k l m $.  $d D n o p $.
        $d F i j k l $.  $d F n o p $.  $d G i j k l m $.  $d G n o p $.
        $d M i j k l $.  $d M n o p $.  $d N i j k l m $.  $d N n o p $.
        $d S m $.  $d S o $.  $d X l m $.  $d ph i j k l $.  $d ph n o p $.
        $( A subset being an element of a neighborhood of a point is equivalent
           to the complement of that subset not being a element of the
           convergent of that point.  (Contributed by RP, 12-Jun-2021.) $)
        neicvgel1 $p |- ( ph -> ( S e. ( N ` X )
                                  <-> -. ( B \ S ) e. ( M ` X ) ) ) $=
          ( cfv wbr w3a wcel cdif wn wb cvv neicvgbex wa cpw cmap co wf1o simpr
          wfn pwexd fsovf1od f1ofn syl dssmapf1od f1of fsovfd ccom breqi adantr
          wf sylib brcofffn mpdan simpr2 ntrclselnel1 eqid simpr1 ccnv a1i wrel
          id pwexg f1orel relbrcnvg 4syl fsovcnvd breqd 3bitr2d ntrneiel simpr3
          mpbid difssd sselpwd notbid 3bitr3d ) APPMUJZMUKZXBXBCUJZCUKZXDOLUKZU
          LZERPUJUMZBEUNZROUJUMZUOZUPABUQUMZXGABCDLMNOPUCUFUGURZAXLUSZPOLCMBUTZ
          UTBVAVBZXOXOVAVBZXQXNXQXPLVCLXQVEXNITXOBHLQUQUQFGUAXNBUQAXLVDZVFZXRUD
          VGXQXPLVHVIXNXQXQCVCXQXQCVPXNBCSDUQKJUBUCXRVJXQXQCVKVIXNITBXOHMQUQUQF
          GUAXRXSUEVLAPOLCMVMVMZUKZXLAPONUKYAUGPONXTUFVNVQVOVRVSAXGUSZREXBUJUMR
          XIXDUJUMZUOXHXKYBBCEJKSXBXDDRUBUCAXCXEXFVTARBUMXGUHVOZAEXOUMXGUIVOZWA
          YBBEFGHIXOBQVBZXBPQRTUAYFWBZYBXCXBPYFUKZAXCXEXFWCYBXCPXBBXOQVBZUKZXBP
          YIWDZUKZYHXCYJUPYBPXBMYIUEVNWEYBXLXPXQYIVCYIWFYLYJUPAXLXGXMVOZXLITBXO
          HYIQUQUQFGUAXLWGZBUQWHZYIWBZVGXPXQYIWIXBPYIWJWKYBXLYLYHUPYMXLYKYFXBPX
          LITBXOHYIYFQUQUQFGUAYNYOYPYGWLWMVIWNWQYDYEWOYBYCXJYBBXIFGHILXDOQRTUAU
          DAXCXEXFWPYDAXIXOUMXGAXIBUQXMABEWRWSVOWOWTXAVS $.
      $}

      ${
        $d B i j k l m $.  $d B n o p $.  $d D i j k l m $.  $d D n o p $.
        $d F i j k l $.  $d F n o p $.  $d G i j k l m $.  $d G n o p $.
        $d M i j k l $.  $d M n o p $.  $d N i j k l m $.  $d N n o p $.
        $d S m $.  $d S o $.  $d X l m $.  $d ph i j k l $.  $d ph n o p $.
        $( The complement of a subset being an element of a neighborhood at a
           point is equivalent to that subset not being a element of the
           convergent at that point.  (Contributed by RP, 12-Jun-2021.) $)
        neicvgel2 $p |- ( ph -> ( ( B \ S ) e. ( N ` X )
                                  <-> -. S e. ( M ` X ) ) ) $=
          ( cdif cfv wcel neicvgrcomplex neicvgel1 wss wceq elpwid dfss4 eleq1d
          wn sylib notbid bitrd ) ABEUJZRPUKULBVDUJZROUKZULZUTEVFULZUTABCDVDFGH
          IJKLMNOPQRSTUAUBUCUDUEUFUGUHABCDELMNOPUCUFUGUMUNAVGVHAVEEVFAEBUOVEEUP
          AEBUIUQEBURVAUSVBVC $.
      $}
    $}

    ${
      $d B i j k l m s $.  $d B n o p s $.  $d D i j k l m $.  $d D n o p $.
      $d F i j k l $.  $d F n o p $.  $d G i j k l m $.  $d G n o p $.
      $d M i j k l $.  $d M n o p $.  $d N i j k l m s $.  $d N n o p s $.
      $d X l m s $.  $d ph i j k l s $.  $d ph n o p s $.
      neicvgfv.x $e |- ( ph -> X e. B ) $.
      $( The value of the neighborhoods (convergents) in terms of the
         convergents (neighborhoods) function.  (Contributed by RP,
         27-Jun-2021.) $)
      neicvgfv $p |- ( ph -> ( N ` X )
                             = { s e. ~P B | -. ( B \ s ) e. ( M ` X ) } ) $=
        ( cpw cfv cin cv wcel crab cdif wn dfin5 wss wceq cmap neicvgnex elmapi
        co wf ffvelcdmd elpwid sseqin2 sylib wa adantr simpr neicvgel1 rabbidva
        syl wbr 3eqtr3a ) ABUIZQOUJZUKZRULZVRUMZRVQUNVRBVTUOQNUJUMUPZRVQUNRVQVR
        UQAVRVQURVSVRUSAVRVQABVQUIZQOAOWCBUTVCUMBWCOVDABCDEFGHIJKLMNOPSTUAUBUCU
        DUEUFUGVAOWCBVBVNUHVEVFVRVQVGVHAWAWBRVQAVTVQUMZVIBCDVTEFGHIJKLMNOPQSTUA
        UBUCUDUEUFAONMVOWDUGVJAQBUMWDUHVJAWDVKVLVMVP $.
    $}
  $}

  ${
    ntrrn.x $e |- X = U. J $.
    ntrrn.i $e |- I = ( int ` J ) $.

    ${
      $d J s $.  $d X s $.
      $( The range of the interior function of a topology a subset of the open
         sets of the topology.  (Contributed by RP, 22-Apr-2021.) $)
      ntrrn $p |- ( J e. Top -> ran I C_ J ) $=
        ( vs ctop wcel crn cnt cfv rneqi cpw wfn cv wral wss cin cuni cvv vpwex
        cmpt inex2 uniex rgenw nfcv fnmptf mp1i ntrfval fneq1d mpbird ntropn ex
        elpwi syl5 ralrimiv fnfvrnss syl2anc eqsstrid ) BGHZAIBJKZIZBAVAELUTVAC
        MZNZFOZVAKBHZFVCPVBBQUTVDFVCBVEMZRZSZUBZVCNZVITHZFVCPVKUTVLFVCVHVGBFUAU
        CUDUEFVCVITFVCUFUGUHUTVCVAVJFBCDUIUJUKUTVFFVCVEVCHVECQZUTVFVECUNUTVMVFV
        EBCDULUMUOUPFVCBVAUQURUS $.

      $( The interior function of a topology is a map from the powerset of the
         base set to the open sets of the topology.  (Contributed by RP,
         22-Apr-2021.) $)
      ntrf $p |- ( J e. Top -> I : ~P X --> J ) $=
        ( vs ctop wcel cpw wfn crn wss wf cv cin cuni cmpt vpwex inex2 uniex
        eqid fnmpti cnt cfv ntrfval eqtrid fneq1d mpbiri ntrrn df-f sylanbrc )
        BGHZACIZJZAKBLUMBAMULUNFUMBFNIZOZPZQZUMJFUMUQURUPUOBFRSTURUAUBULUMAURUL
        ABUCUDUREFBCDUEUFUGUHABCDEUIUMBAUJUK $.
    $}

    $( The interior function is a map from the powerset of the base set to
       itself.  (Contributed by RP, 22-Apr-2021.) $)
    ntrf2 $p |- ( J e. Top -> I : ~P X --> ~P X ) $=
      ( ctop wcel cpw ntrf c0 cpr wss ctopon cfv wa toptopon topgele sylbi fssd
      simprd ) BFGZCHZBUBAABCDEIUAJCKBLZBUBLZUABCMNGUCUDOBCDPBCQRTS $.

    $( The interior function is a map from the powerset of the base set to
       itself.  (Contributed by RP, 22-Apr-2021.) $)
    ntrelmap $p |- ( J e. Top -> I e. ( ~P X ^m ~P X ) ) $=
      ( ctop wcel cpw cmap co wf ntrf2 cvv topopn pwexd elmapd mpbird ) BFGZACH
      ZSIJGSSAKABCDELRSSAMMRCBBCDNOZTPQ $.
  $}

  ${
    clselmap.x $e |- X = U. J $.
    clselmap.k $e |- K = ( cls ` J ) $.
    $( The closure function is a map from the powerset of the base set to
       itself.  This is less precise than ~ clsf .  (Contributed by RP,
       22-Apr-2021.) $)
    clsf2 $p |- ( J e. Top -> K : ~P X --> ~P X ) $=
      ( ctop wcel cpw wfn crn wss wa wf ccld cfv ccl clsf feq1i df-f sylbb1 mpi
      cldss2 sstr2 anim2i 3syl sylibr ) AFGZBCHZIZBJZUHKZLZUHUHBMUGUHANOZAPOZMZ
      UIUJUMKZLZULACDQUHUMBMUOUQUHUMBUNERUHUMBSTUPUKUIUPUMUHKUKACDUBUJUMUHUCUAU
      DUEUHUHBSUF $.

    $( The closure function is a map from the powerset of the base set to
       itself.  (Contributed by RP, 22-Apr-2021.) $)
    clselmap $p |- ( J e. Top -> K e. ( ~P X ^m ~P X ) ) $=
      ( ctop wcel cpw cmap co wf clsf2 cvv topopn pwexd elmapd mpbird ) AFGZBCH
      ZSIJGSSBKABCDELRSSBMMRCAACDNOZTPQ $.
  $}

  ${
    dssmapclsntr.x $e |- X = U. J $.
    dssmapclsntr.k $e |- K = ( cls ` J ) $.
    dssmapclsntr.i $e |- I = ( int ` J ) $.
    dssmapclsntr.o $e |- O = ( b e. _V |-> ( f e. ( ~P b ^m ~P b ) |->
                            ( s e. ~P b |-> ( b \ ( f ` ( b \ s ) ) ) ) ) ) $.
    dssmapclsntr.d $e |- D = ( O ` X ) $.

    ${
      $d D t $.  $d I t $.  $d J b f s t $.  $d K f s t $.  $d X b f s t $.

      $( The interior and closure operators on a topology are duals of each
         other.  See also ~ kur14lem2 .  (Contributed by RP, 21-Apr-2021.) $)
      dssmapntrcls $p |- ( J e. Top -> I = ( D ` K ) ) $=
        ( vt wcel cpw cfv wfn cdif ctop cv cin cuni cmpt wral vpwex inex2 uniex
        cvv rgenw nfcv fnmptf mp1i ntrfval eqtrid fneq1d mpbird cmap co wf1o wf
        cnt topopn dssmapf1od f1of syl clselmap ffvelcdmd elmapfn ccl wss elpwi
        wceq ntrval2 sylan2 fveq1i difeq2i 3eqtr4g adantr eqid simpr dssmapfv3d
        wa eqtr4d eqfnfvd ) DUAPZOGQZCEARZWGCWHSOWHDOUBZQZUCZUDZUEZWHSZWMUJPZOW
        HUFWOWGWPOWHWLWKDOUGUHUIUKOWHWMUJOWHULUMUNWGWHCWNWGCDVCRZWNLODGJUOUPUQU
        RWGWIWHWHUSUTZPWIWHSWGWRWREAWGWRWRAVAWRWRAVBWGGABFDHIMNDGJVDZVEWRWRAVFV
        GDEGJKVHZVIWIWHWHVJVGWGWJWHPZWDZWJCRZGGWJTZERZTZWJWIRZXBWJWQRZGXDDVKRZR
        ZTZXCXFXAWGWJGVLXHXKVNWJGVMWJDGJVOVPWJCWQLVQXEXJGXDEXIKVQVRVSXBGAWJXGBE
        WIFDHIMNWGGDPXAWSVTWGEWRPXAWTVTWIWAWGXAWBXGWAWCWEWF $.
    $}

    ${
      $d J b f s $.  $d K f s $.  $d X b f s $.
      $( The closure and interior operators on a topology are duals of each
         other.  See also ~ kur14lem2 .  (Contributed by RP, 22-Apr-2021.) $)
      dssmapclsntr $p |- ( J e. Top -> K = ( D ` I ) ) $=
        ( ctop wcel ccnv cfv wceq dssmapntrcls eqcomd cpw cmap co wi dssmapf1od
        wf1o topopn clselmap f1ocnvfv syl2anc mpd dssmapnvod fveq1d eqtr3d ) DO
        PZCAQZRZECARUPEARZCSZURESZUPCUSABCDEFGHIJKLMNTUAUPGUBZVBUCUDZVCAUGEVCPU
        TVAUEUPGABFDHIMNDGJUHZUFDEGJKUIVCVCECAUJUKULUPCUQAUPGABFDHIMNVDUMUNUO
        $.
    $}
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Generic Neighborhood Spaces
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Any neighborhood space is an open set topology and any open set topology is a
  neighborhood space.  Seifert and Threlfall define a generic neighborhood
  space which is a superset of what is now generally used and related concepts
  and the following will show that those definitions apply to elements of
  ` Top ` .

  Seifert and Threlfall do not allow neighborhood spaces on the empty set while
  ~ sn0top is an example of a topology with an empty base set.  This divergence
  is unlikely to pose serious problems.

$)

  ${
    gneispace.x $e |- X = U. J $.
    ${
      $d J n p $.  $d X n $.
      $( Each point ` p ` of the neighborhood space has at least one
         neighborhood; each neighborhood of ` p ` contains ` p ` .  Axiom A of
         Seifert and Threlfall.  (Contributed by RP, 5-Apr-2021.) $)
      gneispa $p |- ( J e. Top
                      -> A. p e. X ( ( ( nei ` J ) ` { p } ) =/= (/)
                                     /\ A. n e. ( ( nei ` J ) ` { p } )
                                           p e. n ) ) $=
        ( ctop wcel cv csn cnei cfv c0 wne wel wral wa wss snssi tpnei imbitrid
        imp ne0d elnei 3expia ralrimiv jca ralrimiva ) BFGZDHZIZBJKKZLMZDANZAUK
        OZPDCUHUICGZPZULUNUPUKCUHUOCUKGZUOUJCQUHUQUICRUJBCESTUAUBUPUMAUKUHUOAHZ
        UKGUMCUIBURUCUDUEUFUG $.
    $}

    ${
      $d J s $.  $d N s $.  $d P s $.  $d X s $.
      $( Given a neighborhood ` N ` of ` P ` , each subset of the neighborhood
         space containing this neighborhood is also a neighborhood of ` P ` .
         Axiom B of Seifert and Threlfall.  (Contributed by RP, 5-Apr-2021.) $)
      gneispb $p |- ( ( J e. Top /\ P e. X /\ N e. ( ( nei ` J ) ` { P } ) )
                      -> A. s e. ~P X ( N C_ s
                                        -> s e. ( ( nei ` J ) ` { P } ) ) ) $=
        ( ctop wcel csn cnei cfv w3a cv wss wi cpw wa 3simpb ad2antrr simpr
        simplr elpwid ssnei2 syl12anc exp31 ralrimiv ) BGHZADHZCAIZBJKKZHZLZCEM
        ZNZUMUJHZOEDPZULUMUPHZUNUOULUQQZUNQZUGUKQZUNUMDNUOULUTUQUNUGUHUKRSURUNT
        USUMDULUQUNUAUBUIBUMCDFUCUDUEUF $.
    $}
  $}

  ${
    gneispace.a $e |- A = { f | ( f : dom f -->
                                      ( ~P ( ~P dom f \ { (/) } ) \ { (/) } )
                                  /\ A. p e. dom f A. n e. ( f ` p ) ( p e. n
                            /\ A. s e. ~P dom f ( n C_ s -> s e. ( f ` p ) )
                               ) ) } $.

    ${
      $d F n p $.  $d F f s $.  $d f n p $.
      $( The predicate that ` F ` is a (generic) Seifert and Threlfall
         neighborhood space.  (Contributed by RP, 15-Apr-2021.) $)
      gneispace2 $p |- ( F e. V -> ( F e. A <-> ( F : dom F -->
                                      ( ~P ( ~P dom F \ { (/) } ) \ { (/) } )
                                  /\ A. p e. dom F A. n e. ( F ` p ) ( p e. n
                            /\ A. s e. ~P dom F ( n C_ s -> s e. ( F ` p ) )
                               ) ) ) ) $=
        ( cv cdm cpw cdif wf cfv wcel wi wral wa pweqd raleqbidv c0 csn wel wss
        wceq id dmeq difeq1d feq123d fveq1 eleq2d imbi2d anbi2d anbi12d elab2g
        ) BIZJZUQKZUAUBZLZKZUSLZUPMZGCUCZCIFIZUDZVEGIZUPNZOZPZFURQZRZCVHQZGUQQZ
        RDJZVOKZUSLZKZUSLZDMZVDVFVEVGDNZOZPZFVPQZRZCWAQZGVOQZRBDAEUPDUEZVCVTVNW
        GWHUQVOVBVSUPDWHUFUPDUGZWHVAVRUSWHUTVQWHURVPUSWHUQVOWISZUHSUHUIWHVMWFGU
        QVOWIWHVLWECVHWAVGUPDUJZWHVKWDVDWHVJWCFURVPWJWHVIWBVFWHVHWAVEWKUKULTUMT
        TUNHUO $.
    $}

    ${
      $d F n p $.  $d F f s $.  $d f n p $.
      $( The predicate that ` F ` is a (generic) Seifert and Threlfall
         neighborhood space.  (Contributed by RP, 15-Apr-2021.) $)
      gneispace3 $p |- ( F e. V -> ( F e. A <-> (
                       ( Fun F
                         /\ ran F C_ ( ~P ( ~P dom F \ { (/) } ) \ { (/) } ) )
                       /\ A. p e. dom F A. n e. ( F ` p ) (
                          p e. n
                          /\ A. s e. ~P dom F (
                             n C_ s -> s e. ( F ` p ) ) ) ) ) ) $=
        ( wcel cdm cpw c0 csn cdif wf cv wss wral wa anbi1i wel cfv wi wfun crn
        gneispace2 wfn df-f funfn bitr4i bitrdi ) DEIDAIDJZULKZLMZNKUNNZDOZGCUA
        CPFPZQUQGPDUBZIUCFUMRSCURRGULRZSDUDZDUEUOQZSZUSSABCDEFGHUFUPVBUSUPDULUG
        ZVASVBULUODUHUTVCVADUITUJTUK $.
    $}

    ${
      $d F n p $.  $d F f s $.  $d f n p $.  $d V p $.  $d F p x $.
      $( The predicate that ` F ` is a (generic) Seifert and Threlfall
         neighborhood space.  (Contributed by RP, 14-Apr-2021.) $)
      gneispace $p |- ( F e. V -> ( F e. A <-> ( Fun F /\ ran F C_ ~P ~P dom F
                       /\ A. p e. dom F ( ( F ` p ) =/= (/)
                          /\ A. n e. ( F ` p ) ( p e. n
                             /\ A. s e. ~P dom F ( n C_ s -> s e. ( F ` p ) )
                             )
                          ) ) ) ) $=
        ( vx wcel c0 wss wa cv wral syl cin wceq wn sylibr wfun crn cdm cpw csn
        cdif wel cfv wi gneispace3 simpll simplr difss sspwi sstri sstrdi simpr
        wne simpl fvelrn sylan ssel2 eldifsni syl2an2r ralrimiva r19.26 biimpri
        w3a 3jca simp1 nfv nfra1 nf3an wex 19.8ad ralimi 3ad2ant3 rsp wal df-ex
        wrex ralbii ralnex bitri 0el xchbinxr biimpi elinel1 nsyl disjdif2 syl6
        disjsn simp2 ex fvex elpw dfss2 sylbb syl6an jcad indif2 eqeq1i ralrimi
        eqtr wfn wb funfnd sseq1 ralrn mpbird pwssb jca elrnrexdm nesym reldisj
        nsyli imp biimpd sylc impbii bitrdi ) DEJDAJDUAZDUBZDUCZUDZKUEZUFZUDZYF
        UFZLZMZGCUGZCNFNZLYMGNZDUHZJUIFYEOZMZCYOOZGYDOZMZYBYCYEUDZLZYOKURZYRMZG
        YDOZVHZABCDEFGHUJYTUUFYTYBUUBUUEYBYJYSUKYTYCYIUUAYBYJYSULYIYHUUAYHYFUMY
        GYEYEYFUMUNUOUPYKUUCGYDOZYSUUEYKUUCGYDYKYJYNYDJZYOYCJZUUCYBYJUQYKYBUUHU
        UIYBYJUSYNDUTZVAYJUUIMYOYIJUUCYCYIYOVBYOYHKVCPVDVEUUEUUGYSMZUUCYRGYDVFZ
        VGVAVIUUFYKYSUUFYBYJYBUUBUUEVJZUUFYCYHLZYCYFQKRZYJUUFINZYGLZIYCOZUUNUUF
        UURYOYGLZGYDOZUUFUUSGYDYBUUBUUEGYBGVKUUBGVKUUDGYDVLVMUUFUUHYOYEQZYFUFZU
        VARZUVAYORZMZUUSUUFUUHUVCUVDUUFUUHYLGVNZCYOOZUVCUUFUVGGYDOZUUHUVGUIUUEY
        BUVHUUBUUDUVGGYDUUDYRUVGUUCYRUQYQUVFCYOYQYLGYLYPUSVOVPPVPVQUVGGYDVRPUVG
        UVAYFQKRZUVCUVGKUVAJZSUVIUVGKYOJZUVJUVGUVKSUVGYLSGVSZCYOWAZUVKUVGUVLSZC
        YOOUVMSUVFUVNCYOYLGVTWBUVLCYOWCWDCGYOWEWFWGKYOYEWHWIUVAKWLTUVAYFWJPWKUU
        FUUBUUHUUIUVDYBUUBUUEWMUUFYBUUHUUIUIUUMYBUUHUUIUUJWNPUUBUUIMYOUUAJZUVDY
        CUUAYOVBUVOYOYELUVDYOYEYNDWOWPYOYEWQWRPWSWTUVEUVBYORZUUSUVBUVAYOXDUUSYO
        YGQZYORUVPYOYGWQUVQUVBYOYOYEYFXAXBWDTWKXCUUFDYDXEUURUUTXFUUFDUUMXGUUQUU
        SIGYDDUUPYOYGXHXIPXJIYCYGXKTUUFYBUUGMZUUOUUFYBUUGUUMUUEYBUUGUUBUUDUUCGY
        DUUCYRUSVPVQXLUVRKYCJZSZUUOYBUUGUVTYBUVSKYORZGYDWAZUUGGDKXMUUGUWASZGYDO
        UWBSUUCUWCGYDYOKXNWBUWAGYDWCWRXPXQYCKWLTPUUNUUOYJYCYFYHXOXRXSXLUUFUUKYS
        UUEYBUUKUUBUUEUUKUULWGVQUUGYSUQPXLXTYA $.
    $}

    ${
      $d F n p $.  $d F f s $.  $d f n p $.  $d P p $.  $d P n $.  $d N n $.
      $d S s $.
      $( A generic neighborhood space is a function with a range that is a
         subset of the powerset of the powerset of its domain.  (Contributed by
         RP, 15-Apr-2021.) $)
      gneispacef $p |- ( F e. A -> F : dom F
                         --> ( ~P ( ~P dom F \ { (/) } ) \ { (/) } ) ) $=
        ( wcel cdm cpw c0 csn cdif wf wel cv wss cfv wral wa wi gneispace2 ibi
        simpld ) DAHZDIZUFJZKLZMJUHMDNZFCOCPEPZQUJFPDRZHUAEUGSTCUKSFUFSZUEUIULT
        ABCDAEFGUBUCUD $.

      $( A generic neighborhood space is a function with a range that is a
         subset of the powerset of the powerset of its domain.  (Contributed by
         RP, 15-Apr-2021.) $)
      gneispacef2 $p |- ( F e. A -> F : dom F --> ~P ~P dom F ) $=
        ( wcel wfun crn cdm cpw wss cv cfv c0 wral wa cvv syl wne wel wi w3a wf
        wb elex gneispace ibi wfn simp1 funfnd simp2 df-f sylanbrc ) DAHZDIZDJD
        KZLZLZMZFNDOZPUAFCUBCNENZMVCVBHUCEUSQRCVBQRFURQZUDZURUTDUEZUPVEUPDSHUPV
        EUFDAUGABCDSEFGUHTUIVEDURUJVAVFVEDUQVAVDUKULUQVAVDUMURUTDUNUOT $.

      $( A generic neighborhood space is a function.  (Contributed by RP,
         15-Apr-2021.) $)
      gneispacefun $p |- ( F e. A -> Fun F ) $=
        ( wcel cdm cpw c0 csn cdif gneispacef ffund ) DAHDIZPJKLZMJQMDABCDEFGNO
        $.

      $( A generic neighborhood space has a range that is a subset of the
         powerset of the powerset of its domain.  (Contributed by RP,
         15-Apr-2021.) $)
      gneispacern $p |- ( F e. A -> ran F C_
                          ( ~P ( ~P dom F \ { (/) } ) \ { (/) } ) ) $=
        ( wcel cdm cpw c0 csn cdif gneispacef frnd ) DAHDIZPJKLZMJQMDABCDEFGNO
        $.

      $( A generic neighborhood space has a range that is a subset of the
         powerset of the powerset of its domain.  (Contributed by RP,
         15-Apr-2021.) $)
      gneispacern2 $p |- ( F e. A -> ran F C_ ~P ~P dom F ) $=
        ( wcel wfun crn cdm cpw wss cv cfv c0 wne wral wa cvv wel w3a gneispace
        wi wb elex syl ibi simp2d ) DAHZDIZDJDKZLZLMZFNDOZPQFCUACNENZMUPUOHUDEU
        MRSCUORSFULRZUJUKUNUQUBZUJDTHUJURUEDAUFABCDTEFGUCUGUHUI $.

      $( A generic neighborhood space has a nonempty set of neighborhoods for
         every point in its domain.  (Contributed by RP, 15-Apr-2021.) $)
      gneispace0nelrn $p |- ( F e. A -> A. p e. dom F ( F ` p ) =/= (/) ) $=
        ( wcel cv cfv c0 wne wel wss wi cpw wral wa cvv syl cdm wfun crn w3a wb
        elex gneispace ibi simp3d simpl ralimi ) DAHZFIDJZKLZFCMCIEIZNUOUMHOEDU
        AZPZQRCUMQZRZFUPQZUNFUPQULDUBZDUCUQPNZUTULVAVBUTUDZULDSHULVCUEDAUFABCDS
        EFGUGTUHUIUSUNFUPUNURUJUKT $.

      $( A generic neighborhood space has a nonempty set of neighborhoods for
         every point in its domain.  (Contributed by RP, 15-Apr-2021.) $)
      gneispace0nelrn2 $p |- ( ( F e. A /\ P e. dom F ) ->
                               ( F ` P ) =/= (/) ) $=
        ( wcel cdm cfv c0 wne cv wral wi gneispace0nelrn wceq fveq2 neeq1d syl
        rspccv imp ) EAIZBEJZIZBEKZLMZUDGNZEKZLMZGUEOUFUHPACDEFGHQUKUHGBUEUIBRU
        JUGLUIBESTUBUAUC $.

      $( A generic neighborhood space has a nonempty set of neighborhoods for
         every point in its domain.  (Contributed by RP, 15-Apr-2021.) $)
      gneispace0nelrn3 $p |- ( F e. A -> -. (/) e. ran F ) $=
        ( wcel crn cdm cpw c0 csn cdif wss wn gneispacern neldifsnd ssel mtod
        syl ) DAHDIZDJKLMZNKZUCNZOZLUBHZPABCDEFGQUFUGLUEHUFLUDRUBUELSTUA $.

      $( Every neighborhood of a point in a generic neighborhood space contains
         that point.  (Contributed by RP, 15-Apr-2021.) $)
      gneispaceel $p |- ( F e. A -> A. p e. dom F A. n e. ( F ` p ) p e. n ) $=
        ( wcel cdm cpw c0 csn cdif wf wel cv wss cfv wral wa gneispace2 2ralimi
        wi ibi simpl simpl2im ) DAHZDIZUHJZKLZMJUJMDNZFCOZCPEPZQUMFPDRZHUCEUISZ
        TZCUNSFUHSZULCUNSFUHSUGUKUQTABCDAEFGUAUDUPULFCUHUNULUOUEUBUF $.

      $( Every neighborhood of a point in a generic neighborhood space contains
         that point.  (Contributed by RP, 15-Apr-2021.) $)
      gneispaceel2 $p |- ( ( F e. A /\ P e. dom F /\ N e. ( F ` P ) ) ->
                           P e. N ) $=
        ( wcel cdm cfv cv wral wi wel gneispaceel wceq fveq2 rspccv eleq1 eleq2
        raleqbidv syl syl6 3imp ) EAJZBEKZJZFBELZJZBFJZUGUIBDMZJZDUJNZUKULOUGHD
        PZDHMZELZNZHUHNUIUOOACDEGHIQUSUOHBUHUQBRUPUNDURUJUQBESUQBUMUAUCTUDUNULD
        FUJUMFBUBTUEUF $.

      $( All supersets of a neighborhood of a point (limited to the domain of
         the neighborhood space) are also neighborhoods of that point.
         (Contributed by RP, 15-Apr-2021.) $)
      gneispacess $p |- ( F e. A -> A. p e. dom F
                                      A. n e. ( F ` p )
                                        A. s e. ~P dom F
                                          ( n C_ s -> s e. ( F ` p ) ) ) $=
        ( wcel cdm cpw c0 csn cdif wf wel cv wss cfv wral wa gneispace2 2ralimi
        wi ibi simpr simpl2im ) DAHZDIZUHJZKLZMJUJMDNZFCOZCPEPZQUMFPDRZHUCEUISZ
        TZCUNSFUHSZUOCUNSFUHSUGUKUQTABCDAEFGUAUDUPUOFCUHUNULUOUEUBUF $.

      $d n s $.  $d N s $.  $d p s $.  $d P s $.

      $( All supersets of a neighborhood of a point (limited to the domain of
         the neighborhood space) are also neighborhoods of that point.
         (Contributed by RP, 15-Apr-2021.) $)
      gneispacess2 $p |- ( ( ( F e. A /\ P e. dom F )
                           /\ ( N e. ( F ` P ) /\ S e. ~P dom F /\ N C_ S ) )
                           -> S e. ( F ` P ) ) $=
        ( wcel cfv wss cv wi wral wceq ralbidv rspccv syl6 cdm cpw fveq2 eleq2d
        w3a gneispacess imbi2d raleqbidv sseq1 imbi1d sseq2 eleq1 imbi12d 3impd
        syl imp31 ) FAKZBFUAZKZGBFLZKZCURUBZKZGCMZUEZCUTKZUQUSENZHNZMZVHUTKZOZH
        VBPZEUTPZVEVFOUQVIVHINZFLZKZOZHVBPZEVOPZIURPUSVMOADEFHIJUFVSVMIBURVNBQZ
        VRVLEVOUTVNBFUCZVTVQVKHVBVTVPVJVIVTVOUTVHWAUDUGRUHSUOVMVAVCVDVFVMVAGVHM
        ZVJOZHVBPZVCVDVFOZOVLWDEGUTVGGQZVKWCHVBWFVIWBVJVGGVHUIUJRSWCWEHCVBVHCQW
        BVDVJVFVHCGUKVHCUTULUMSTUNTUP $.
    $}
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Exploring Higher Homotopy via Kerodon
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  See ~ https://kerodon.net/ for a work in progress by Jacob Lurie.

$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Simplicial Sets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  See ~ https://kerodon.net/tag/0004 for introduction to the topological
  simplex of dimension ` N ` .

$)

  $( Application of ~ ssin to range of a function.  (Contributed by RP,
     1-Apr-2021.) $)
  k0004lem1 $p |- ( D = ( B i^i C ) ->
                   ( ( F : A --> B /\ ( F " A ) C_ C )
                     <-> F : A --> D ) ) $=
    ( cin wceq wf cima wss wfn crn fnima sseq1d anbi2d ssin bitrdi pm5.32i df-f
    wa anbi1i anass bitri 3bitr4i feq3 bitr4id ) DBCFZGABEHZEAIZCJZTZAUGEHZADEH
    EAKZELZBJZUJTZTZUMUNUGJZTUKULUMUPURUMUPUOUNCJZTURUMUJUSUOUMUIUNCAEMNOUNBCPQ
    RUKUMUOTZUJTUQUHUTUJABESUAUMUOUJUBUCAUGESUDDUGAEUEUF $.

  $( A mapping with a particular restricted range is also a mapping to that
     range.  (Contributed by RP, 1-Apr-2021.) $)
  k0004lem2 $p |- ( ( A e. U /\ B e. V /\ C C_ B ) ->
                   ( ( F e. ( B ^m A ) /\ ( F " A ) C_ C )
                     <-> F e. ( C ^m A ) ) ) $=
    ( wcel wss w3a wf cima wa cmap co cin wceq wb simp3 sseqin2 elmapd 3syl cvv
    biimpi eqcomd k0004lem1 simp2 simp1 anbi1d ssexd 3bitr4d ) ADGZBFGZCBHZIZAB
    EJZEAKCHZLZACEJZEBAMNGZUPLECAMNGUNUMCBCOZPUQURQUKULUMRZUMUTCUMUTCPCBSUCUDAB
    CCEUEUAUNUSUOUPUNBAEFDUKULUMUFZUKULUMUGZTUHUNCAEUBDUNCBFVBVAUIVCTUJ $.

  $( When the value of a mapping on a singleton is known, the mapping is a
     completely known singleton.  (Contributed by RP, 2-Apr-2021.) $)
  k0004lem3 $p |- ( ( A e. U /\ B e. V /\ C e. B ) ->
                   ( ( F e. ( B ^m { A } ) /\ ( F ` A ) = C )
                     <-> F = { <. A , C >. } ) ) $=
    ( wcel w3a csn cmap co cfv wceq wa wss syl bitrid cvv wb snex cima cop sneq
    eqimss fvex snsssn impbii wfn elmapfn simpl1 fnsnfv syl2an2 sseq1d pm5.32da
    snidg simp2 simp3 snssd k0004lem2 mp3an2i wf elmap fsng 3adant2 3bitrd ) AD
    GZBFGZCBGZHZEBAIZJKGZAELZCMZNVKEVJUAZCIZOZNZEVOVJJKGZEACUBIMZVIVKVMVPVMVLIZ
    VOOZVIVKNZVPVMWAVMVTVOMWAVLCUCVTVOUDPVLCAEUEUFUGWBVTVNVOVKEVJUHVIAVJGZVTVNM
    EBVJUIWBVFWCVFVGVHVKUJADUOPVJAEUKULUMQUNVJRGVIVGVOBOVQVRSATZVFVGVHUPVICBVFV
    GVHUQURVJBVOREFUSUTVRVJVOEVAZVIVSVOVJECTWDVBVFVHWEVSSVGACDBEVCVDQVE $.

  ${
    $d n k $.  $d n t $.  $d N k $.  $d N t $.  $d N n $.  $d N v $.
    $( ` ( A `` n ) ` is the topological simplex of dimension ` n ` . $)
    k0004.a $e |- A = ( n e. NN0 |-> { t e. ( ( 0 [,] 1 )
                                              ^m ( 1 ... ( n + 1 ) ) )
                                     | sum_ k e. ( 1 ... ( n + 1 ) )
                                            ( t ` k )
                                       = 1 } ) $.
    $( The topological simplex of dimension ` N ` is the set of real vectors
       where the components are nonnegative and sum to 1.  (Contributed by RP,
       29-Mar-2021.) $)
    k0004val $p |- ( N e. NN0 -> ( A ` N ) = { t e. ( ( 0 [,] 1 )
                                                      ^m ( 1 ... ( N + 1 ) ) )
                                             | sum_ k e. ( 1 ... ( N + 1 ) )
                                                    ( t ` k )
                                               = 1 } ) $=
      ( c1 cv caddc co cfz cfv csu wceq cc0 cicc cmap crab cn0 oveq2d rabeqbidv
      oveq1 sumeq1d eqeq1d ovex rabex fvmpt ) DEGDHZGIJZKJZCHAHLZCMZGNZAOGPJZUJ
      QJZRGEGIJZKJZUKCMZGNZAUNUQQJZRSBUHENZUMUSAUOUTVAUJUQUNQVAUIUPGKUHEGIUBTZT
      VAULURGVAUJUQUKCVBUCUDUAFUSAUTUNUQQUEUFUG $.

    $( The topological simplex of dimension ` N ` is a subset of the real
       vectors of dimension ` ( N + 1 ) ` .  (Contributed by RP,
       29-Mar-2021.) $)
    k0004ss1 $p |- ( N e. NN0 -> ( A ` N ) C_ ( RR ^m ( 1 ... ( N + 1 ) ) )
                   ) $=
      ( cn0 wcel cfv cc0 c1 cicc co caddc cfz cmap cr cv cvv wss csu wceq simp2
      crab k0004val rabssdv eqsstrd reex unitssre mapss mp2an sstrdi ) EGHZEBIZ
      JKLMZKEKNMOMZPMZQUPPMZUMUNUPCRARZICUAKUBZAUQUDUQABCDEFUEUMUTAUQUQUMUSUQHU
      TUCUFUGQSHUOQTUQURTUHUIUOQUPSUJUKUL $.

    $( The topological simplex of dimension ` N ` is a subset of the base set
       of a real vector space of dimension ` ( N + 1 ) ` .  (Contributed by RP,
       29-Mar-2021.) $)
    k0004ss2 $p |- ( N e. NN0 -> ( A ` N )
                                 C_ ( Base ` ( RR^ ` ( 1 ... ( N + 1 ) ) ) )
                   ) $=
      ( vv cn0 wcel cfv cr c1 caddc co cfz cmap crrx cc0 cvv eqid cbs cv cfsupp
      k0004ss1 wbr crab ssidd wa wf elmapi adantl fzfid 0red fdmfifsupp ssrabdv
      wceq ovex rrxbase ax-mp sseqtrrdi sstrd ) EHIZEBJKLELMNZONZPNZVDQJZUAJZAB
      CDEFUDVBVEGUBZRUCUEZGVEUFZVGVBVIGVEVEVBVEUGVBVHVEIZUHZVDKVHKRVKVDKVHUIVBV
      HKVDUJUKVLLVCULVLUMUNUOVDSIVGVJUPLVCOUQVGGVFVDSVFTVGTURUSUTVA $.

    $( The topological simplex of dimension ` N ` is a subset of the base set
       of Euclidean space of dimension ` ( N + 1 ) ` .  (Contributed by RP,
       29-Mar-2021.) $)
    k0004ss3 $p |- ( N e. NN0 -> ( A ` N ) C_ ( Base ` ( EEhil ` ( N + 1 ) ) )
                   ) $=
      ( cn0 wcel cfv cr c1 caddc co cfz cmap cehl cbs k0004ss1 wceq peano2nn0
      eqid ehlbase syl sseqtrd ) EGHZEBIJKEKLMZNMOMZUFPIZQIZABCDEFRUEUFGHUGUISE
      TUHUFUHUAUBUCUD $.

    ${
      $d k t $.
      $( The topological simplex of dimension 0 is a singleton.  (Contributed
         by RP, 2-Apr-2021.) $)
      k0004val0 $p |- ( A ` 0 ) = { { <. 1 , 1 >. } } $=
        ( cc0 cfv c1 co cfz wceq cmap crab csn wcel ax-mp cz 1z eqtri cc cv csu
        caddc cicc cop cn0 0nn0 k0004val 0p1e1 oveq2i fzsn rabeqi sumeq1i wf wa
        elmapi wb fsn2g biimpi unitssre ax-resscn sstri sseli adantr 3syl fveq2
        cr sumsn sylancr eqtrid eqeq1d rabbiia rabeqsn cvv ovex k0004lem3 mp3an
        1elunit mpgbir ) FBGZHFHUCIZJIZCUAZAUAZGZCUBZHKZAFHUDIZWBLIZMZHHUENZNZF
        UFOVTWJKUGABCDFEUHPWJHWDGZHKZAWHHNZLIZMZWLWJWGAWPMWQWGAWIWPWBWOWHLWBHHJ
        IZWOWAHHJUIUJHQOZWRWOKRHUKPSZUJULWGWNAWPWDWPOZWFWMHXAWFWOWECUBZWMWBWOWE
        CWTUMXAWSWMTOZXBWMKRXAWOWHWDUNZWMWHOZWDHWMUENKZUOZXCWDWHWOUPXDXGWSXDXGU
        QRHWHWDQURPUSXEXCXFWHTWMWHVGTUTVAVBVCVDVEWEWMCHQWCHWDVFVHVIVJVKVLSWQWLK
        XAWNUOWDWKKUQZAWNAWPWKVMWSWHVNOHWHOXHRFHUDVOVRHWHHQWDVNVPVQVSSS $.
    $}
  $}

$( (End of Richard Penner's mathbox.) $)
