
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                Mathbox for Scott Fenton
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              ZFC Axioms in primitive form
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  $( ~ ax-ext without distinct variable conditions or defined symbols. $)
  axextprim $p |- -. A. x -. ( ( x e. y -> x e. z ) ->
               ( ( x e. z -> x e. y ) -> y = z ) ) $=
    ( wel wb weq wi wex wn wal axextnd wa dfbi2 imbi1i impexp bitri exbii
    df-ex mpbi ) ABDZACDZEZBCFZGZAHZTUAGZUATGZUCGGZIAJIZABCKUEUHAHUIUDUHAUDUFUG
    LZUCGUHUBUJUCTUAMNUFUGUCOPQUHARPS $.
    $( [13-Oct-2010] $)

  $( ~ ax-rep without distinct variable conditions or defined symbols. $)
  axrepprim $p |- -. A. x -. ( -. A. y -. A. z ( ph -> z = y ) ->
               A. z -. ( ( A. y z e. x -> -. A. x ( A. z x e. y ->
               -. A. y ph ) ) -> -. ( -. A. x ( A. z x e. y -> -. A. y ph )
               -> A. y z e. x ) ) ) $=
    ( weq wi wal wex wel wa wb wn axrepnd df-ex df-an exbii exnal bitri bibi2i
    dfbi1 albii imbi12i mpbi ) ADCEFDGZCHZDBICGZBCIDGZACGZJZBHZKZDGZFZBHZUDLCGL
    ZUFUGUHLFZBGLZFUQUFFLFLZDGZFZLBGLZABCDMUNUTBHVAUMUTBUEUOULUSUDCNUKURDUKUFUQ
    KURUJUQUFUJUPLZBHUQUIVBBUGUHOPUPBQRSUFUQTRUAUBPUTBNRUC $.
    $( [13-Oct-2010] $)

  $( ~ ax-un without distinct variable conditions or defined symbols. $)
  axunprim $p |- -. A. x -. A. y ( -. A. x ( y e. x -> -. x e. z )
               -> y e. x ) $=
    ( wel wa wex wi wal wn axunnd df-an exbii exnal bitri imbi1i albii df-ex
    mpbi ) BADZACDZEZAFZSGZBHZAFZSTIGZAHIZSGZBHZIAHIZABCJUEUIAFUJUDUIAUCUHBUBUG
    SUBUFIZAFUGUAUKASTKLUFAMNOPLUIAQNR $.
    $( [13-Oct-2010] $)

  $( ~ ax-pow without distinct variable conditions or defined symbols. $)
  axpowprim $p |- ( A. x -. A. y ( A. x ( -. A. z -. x e. y -> A. y x e. z )
               -> y e. x ) -> x = y ) $=
    ( weq wel wn wal wi wex axpownd df-ex imbi1i albii exbii bitri sylib con4i
    ) ABDZABEZFCGFZACEBGZHZAGZBAEZHZBGZFAGZRFSCIZUAHZAGZUDHZBGZAIZUGFZABCJUMUFA
    IUNULUFAUKUEBUJUCUDUIUBAUHTUASCKLMLMNUFAKOPQ $.
    $( [13-Oct-2010] $)

  $( ~ ax-reg without distinct variable conditions or defined symbols. $)
  axregprim $p |- ( x e. y ->
               -. A. x ( x e. y -> -. A. z ( z e. x -> -. z e. y ) ) ) $=
    ( wel wn wi wal wa wex axregnd df-an exbii exnal bitri sylib ) ABDZPCADCBDE
    FCGZHZAIZPQEFZAGEZABCJSTEZAIUARUBAPQKLTAMNO $.
    $( [13-Oct-2010] $)

  $( ~ ax-inf without distinct variable conditions or defined symbols. $)
  axinfprim $p |- -. A. x -. ( y e. z -> -. ( y e. x ->
               -. A. y ( y e. x -> -. A. z ( y e. z -> -. z e. x ) ) ) ) $=
    ( wel wa wex wi wal wn axinfnd df-an exbii exnal bitri imbi2i albii anbi2i
    df-ex mpbi ) BCDZBADZUATCADZEZCFZGZBHZEZGZAFZTUAUATUBIGZCHIZGZBHZIGIZGZIAHI
    ZABCJUIUOAFUPUHUOAUGUNTUGUAUMEUNUFUMUAUEULBUDUKUAUDUJIZCFUKUCUQCTUBKLUJCMNO
    PQUAUMKNOLUOARNS $.
    $( [13-Oct-2010] $)

  $( ~ ax-ac without distinct variable conditions or defined symbols. $)
  axacprim $p |- -. A. x -. A. y A. z ( A. x -. ( y e. z -> -. z e. w ) ->
                  -. A. w -. A. y -. ( ( -. A. w ( y e. z -> ( z e. w ->
                  ( y e. w -> -. w e. x ) ) ) -> y = w ) -> -. ( y = w ->
                  -. A. w ( y e. z -> ( z e. w -> ( y e. w -> -. w e. x )
                  ) ) ) ) ) $=
    ( wel wa wal wex weq wb wi wn axacnd df-an albii anass annim pm4.63 anbi2i
    bitr3i 3bitr2i exbii exnal bitri bibi1i dfbi1 df-ex imbi12i 2albii mpbi )
    BCEZCDEZFZAGZUMBDEZDAEZFZFZDHZBDIZJZBGZDHZKZCGBGZAHZUKULLKLZAGZUKULUOUPLKZK
    ZKZDGLZUTKUTVLKLKLZBGZLDGLZKZCGBGZLAGLZABCDMVFVQAHVRVEVQAVDVPBCUNVHVCVOUMVG
    AUKULNOVCVNDHVOVBVNDVAVMBVAVLUTJVMUSVLUTUSVKLZDHVLURVSDURUKULUQFZFUKVJLZFVS
    UKULUQPWAVTUKWAULVILZFVTULVIQWBUQULUOUPRSTSUKVJQUAUBVKDUCUDUEVLUTUFUDOUBVND
    UGUDUHUIUBVQAUGUDUJ $.
    $( [26-Oct-2010] $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Transitive classes
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  ${
    $d x y A $.
    $( The union of a class of transitive sets is transitive. $)
    truni $p |- ( A. x e. A Tr x -> Tr U. A ) $=
      ( vy cv wtr wral wel cuni wss wi wal wcel wa dftr3 biimpi a1i ax-17
      alral syl jctird r19.26 syl6ibr ssuni ralimi syl6 ralimia df-ral ralbii
      ralcom4 bitr2i sylibr wrex eluni2 imbi1i r19.23v bitr4i albii 3bitri ) AD
      ZEZABFZCAGZCDZBHZIZJZABFZCKZVDEZVAVECUSFZABFZVHUTVJABUSBLZUTVCUSIZVLMZCUS
      FZVJVLUTVMCUSFZVLCUSFZMVOVLUTVPVQUTVPJVLUTVPCUSNOPVLVLCKVQVLCQVLCUSRSTVMV
      LCUSUAUBVNVECUSVCUSBUCUDUEUFVKVFCKZABFVHVJVRABVECUSUGUHVFACBUIUJUKVIVECVD
      FVCVDLZVEJZCKVHCVDNVECVDUGVTVGCVTVBABULZVEJVGVSWAVEAVCBUMUNVBVEABUOUPUQUR
      UK $.
      $( [21-Feb-2011] $)
  $}

  ${
    $d x y A $.
    $( The successor of a transitive set is transitive. $)
    trsuc2 $p |- ( Tr A -> Tr suc A ) $=
      ( vx vy wtr cv wcel csn wo wa wi wal csuc wceq trel orc syl6 a1i jaod
      eleq2 biimpac orim2i syl5 elsn orbi2i syl6ibr anbi2i syl5ib andi
      19.21aivv cun wb df-suc treq ax-mp dftr2 elun imbi12i albii bitri sylibr
      ) ADZBEZCEZFZVCAFZVCAGZFZHZIZVBAFZVBVFFZHZJZCKZBKZALZDZVAVMBCVAVDVEIZVDVG
      IZHZVLVIVAVRVDVCAMZIZHZVLVTVAWCVJVBAMZHZVLVAVRVJHWEWCVAVRWEVJVAVRVJWEAVBV
      CNVJWDOZPVJWEJVAWFQRWBVJVRWAVDVJVCAVBSTUAUBVKWDVJBAUCUDUEVSWBVRVGWAVDCAUC
      UFUDUGVDVEVGUHUGUIVQAVFUJZDZVOVPWGMVQWHUKAULVPWGUMUNWHVDVCWGFZIZVBWGFZJZC
      KZBKVOBCWGUOWMVNBWLVMCWJVIWKVLWIVHVDVCAVFUPUFVBAVFUPUQURURUSUSUT $.
      $( [21-Feb-2011] $)
  $}

  ${
    $d A x y z $.
    $( The intersection of a class of transitive sets is transitive. $)
    trint $p |- ( A. x e. A Tr x -> Tr |^| A ) $=
      ( vy cv wtr wral wel wss wi wal cint dftr3 ralbii biimpi df-ral ralcom4
      bitri sylib ralim alimi syl wcel visset elint2 ssint imbi12i albii
      3bitri sylibr ) ADZEZABFZCAGZABFZCDZUJHZABFZIZCJZBKZEZULUMUPIZABFZCJZUSUL
      UPCUJFZABFZVDULVFUKVEABCUJLMNVFVBCJZABFVDVEVGABUPCUJOMVBACBPQRVCURCUMUPAB
      STUAVAUOUTHZCUTFUOUTUBZVHIZCJUSCUTLVHCUTOVJURCVIUNVHUQAUOBCUCUDAUOBUEUFUG
      UHUI $.
      $( [25-Feb-2011] $)
  $}

  ${
    $d x y z A $.
    $( If ` A ` is transitive and non-null, then ` |^| A ` is a subset of
       ` A ` $)
    trintss $p |- ( ( A =/= (/) /\ Tr A ) -> |^| A C_ A ) $=
      ( vy vx c0 wne wtr wa cint wel wral cv wcel wrex r19.2z ex trel ancomsd
      exp3a r19.23adv sylan9 visset elint2 syl5ib ssrdv ) ADEZAFZGZBAHZAUGBCIZC
      AJZBKZALZUKUHLUEUJUICAMZUFULUEUJUMUICANOUFUIULCAUFCKZALZUIULUFUIUOULAUKUN
      PQRSTCUKABUAUBUCUD $.
      $( [3-Mar-2011] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Untangled classes
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x A $.
    $( We call a class "untanged" if all its members are not members of
       themselves.  The term originates from Isbell (see citation in
       ~ dfon2 ).  Using this concept, we can avoid a lot of the uses of the
       Axiom of Regularity.  Here, we prove a series of properties of untanged
       classes.  First, we prove that an untangled class is not a member of
       itself. $)
    untelirr $p |- ( A. x e. A -. x e. x -> -. A e. A ) $=
      ( wel wn wral wcel cv wceq eleq1 eleq2 bitrd notbid rcla4cv pm2.01d ) AAC
      ZDZABEBBFZPQDABBAGZBHZOQSOBRFQRBRIRBBJKLMN $.
      $( [28-Feb-2011] $)
  $}

  ${
    $d x y A $.
    $( The union of a class is untangled iff all its members are untangled. $)
    untuni $p |- ( A. x e. U. A -. x e. x <-> A. y e. A A. x e. y -. x e. x )
        $=
      ( cv cuni wcel wel wn wi wal wral wrex r19.23v albii ralcom4 eluni2
      imbi1i 3bitr4ri df-ral ralbii 3bitr4i ) ADZCEZFZAAGHZIZAJZABGZUEIZAJZBCKZ
      UEAUCKUEABDZKZBCKUIBCKZAJUHBCLZUEIZAJUKUGUNUPAUHUEBCMNUIBACOUFUPAUDUOUEBU
      BCPQNRUEAUCSUMUJBCUEAULSTUA $.
      $( [28-Feb-2011] $)
  $}

  ${
    $d x A $.  $d x y $.
    untsucf.1 $e |- ( x e. A -> A. y x e. A ) $.
    $( If a class is untangled, then so is its successor. $)
    untsucf $p |- ( A. x e. A -. x e. x -> A. y e. suc A -. y e. y ) $=
      ( wel wn wral csuc ax-17 hbral cv wcel wceq wo weq elequ1 elequ2 bitrd
      notbid rcla4cv eleq1 eleq2 untelirr syl5cbir jaod visset elsuc syl5ib
      r19.21ai ) AAEZFZACGZBBEZFZBCHZUKBACDUKBIJULBKZCLZUPCMZNUNUPUOLULUQUNURUK
      UNAUPCABOZUJUMUSUJBAEUMABAPABBQRSTURUNCCLZFULURUMUTURUMCUPLUTUPCUPUAUPCCU
      BRSACUCUDUEUPCBUFUGUHUI $.
      $( [28-Feb-2011] $)
  $}

  $( The null set is untangled.  (The proof was shortened by Andrew Salmon,
     27-Aug-2011.) $)
  unt0 $p |- A. x e. (/) -. x e. x $=
    ( wel wn ral0 ) AABCAD $.
    $( [27-Aug-2011] $) $( [10-Mar-2011] $)

  ${
    $d x y A $.
    $( If there is an untangled element of a class, then the intersection of
       the class is untangled. $)
    untint $p |- ( E. x e. A A. y e. x -. y e. y ->
                    A. y e. |^| A -. y e. y ) $=
      ( wel wn cv wral cint wcel wss wi intss1 ssralv syl r19.23aiv ) BBDEZBAFZ
      GZPBCHZGZACQCISQJRTKQCLPBSQMNO $.
      $( [1-Mar-2011] $)
  $}

  ${
    $d x A $.
    $( If ` A ` is well-founded by ` _E ` , then it is untangled. $)
    efrunt $p |- ( _E Fr A -> A. x e. A -. x e. x ) $=
      ( cep wfr wel wn cv wcel wa wbr frirr epel notbii sylib r19.21aiva ) BCDZ
      AAEZFZABPAGZBHISSCJZFRABCKTQAALMNO $.
      $( [1-Mar-2011] $)
  $}

  ${
    $d x y A $.
    $( A transitive class is untangled iff its elements are. $)
    untangtr $p |- ( Tr A ->
                   ( A. x e. A -. x e. x <->
                     A. x e. A A. y e. x -. y e. y ) ) $=
      ( wtr wel wn wral cv cuni wss wi df-tr ssralv sylbi weq elequ1 elequ2
      bitrd notbid cbvralv untuni bitri syl6ib untelirr ralimi impbid1 ) CDZAAE
      ZFZACGZBBEZFZBAHZGZACGZUGUJUIACIZGZUOUGUPCJUJUQKCLUIAUPCMNUQULBUPGUOUIULA
      BUPABOZUHUKURUHBAEUKABAPABBQRSTBACUAUBUCUNUIACBUMUDUEUF $.
      $( [7-Mar-2011] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Extra propositional calculus theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Analouge of ~ an4 for triple conjunction.  (The proof was shortened by
       Andrew Salmon, 25-May-2011.) $)
    3an6 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) /\ ( ta /\ et ) ) <->
                  ( ( ph /\ ch /\ ta ) /\ ( ps /\ th /\ et ) ) ) $=
      ( w3a wa an6 bicomi ) ACEGBDFGHABHCDHEFHGACEBDFIJ $.
      $( [25-May-2011] $) $( [16-Mar-2011] $)

    $( Analouge of ~ or4 for triple conjunction. $)
    3or6 $p |- ( ( ( ph \/ ps ) \/ ( ch \/ th ) \/ ( ta \/ et ) ) <->
                  ( ( ph \/ ch \/ ta ) \/ ( ps \/ th \/ et ) ) ) $=
      ( wo w3o or4 orbi1i bitr2i df-3or orbi12i 3bitr4i ) ABGZCDGZGZEFGZGZACGZE
      GZBDGZFGZGZOPRHACEHZBDFHZGUDTUBGZRGSTEUBFIUGQRACBDIJKOPRLUEUAUFUCACELBDFL
      MN $.
      $( [20-Mar-2011] $)

  $}

  $( Partial elimination of a triple disjunction by denial of a disjunct. $)
  3orel1 $p |- ( -. ph -> ( ( ph \/ ps \/ ch ) -> ( ps \/ ch ) ) ) $=
    ( wn wo w3o orel1 3orass syl5ib ) ADABCEZEJABCFAJGABCHI $.
    $( [26-Mar-2011] $)

  $( Partial elimination of a triple disjunction by denial of a disjunct.  (The
     proof was shortened by Andrew Salmon, 25-May-2011.) $)
  3orel2 $p |- ( -. ps -> ( ( ph \/ ps \/ ch ) -> ( ph \/ ch ) ) ) $=
    ( wn w3o wo 3orel1 orcom syl6ib 3orrot syl5ib ) BDZBCAEZACFZABCELMCAFNBCAGC
    AHIABCJK $.
    $( [25-May-2011] $) $( [26-Mar-2011] $)

  $( Partial elimination of a triple disjunction by denial of a disjunct. $)
  3orel3 $p |- ( -. ch -> ( ( ph \/ ps \/ ch ) -> ( ph \/ ps ) ) ) $=
    ( wn wo w3o orel2 df-3or syl5ib ) CDABEZCEJABCFCJGABCHI $.
    $( [26-Mar-2011] $)


  $( Negated triple disjunction as triple conjunction. $)
  3ioran $p |- ( -. ( ph \/ ps \/ ch ) <-> ( -. ph /\ -. ps /\ -. ch ) ) $=
    ( wo wn wa w3o w3a ioran anbi1i df-3or notbii bitri df-3an 3bitr4i ) ABDZEZ
    CEZFZAEZBEZFZRFABCGZEZTUARHQUBRABIJUDPCDZESUCUEABCKLPCIMTUARNO $.
    $( [19-Apr-2011] $)

  ${
    3pm3.2ni.1 $e |- -. ph $.
    3pm3.2ni.2 $e |- -. ps $.
    3pm3.2ni.3 $e |- -. ch $.
    $( Triple negated disjuntion introduction. $)
    3pm3.2ni $p |- -. ( ph \/ ps \/ ch ) $=
      ( w3o wo pm3.2ni df-3or mtbir ) ABCGABHZCHLCABDEIFIABCJK $.
      $( [20-Apr-2011] $)
  $}

  ${
    3jaodd.1 $e |- ( ph -> ( ps -> ( ch -> et ) ) ) $.
    3jaodd.2 $e |- ( ph -> ( ps -> ( th -> et ) ) ) $.
    3jaodd.3 $e |- ( ph -> ( ps -> ( ta -> et ) ) ) $.
    $( Double deduction form of ~ 3jaoi . $)
    3jaodd $p |- ( ph -> ( ps -> ( ( ch \/ th \/ ta ) -> et ) ) ) $=
      ( w3o wi com3r 3jaoi com3l ) CDEJABFCABFKKDEABCFGLABDFHLABEFILMN $.
      $( [20-Apr-2011] $)
  $}

  $( Closed form of ~ 3ori , $)
  3orit $p |- ( ( ph \/ ps \/ ch ) <-> ( ( -. ph /\ -. ps ) -> ch ) ) $=
    ( w3o wo wn wi wa df-3or df-or ioran imbi1i 3bitri ) ABCDABEZCENFZCGAFBFHZC
    GABCINCJOPCABKLM $.
    $( [20-Apr-2011] $)


  ${
    3mixd.1 $e |- ( ph -> ps ) $.
    $( Deduction introducing triple disjunction. $)
    3mix1d $p |- ( ph -> ( ps \/ ch \/ th ) ) $=
      ( w3o 3mix1 syl ) ABBCDFEBCDGH $.
      $( [8-Jun-2011] $)


    $( Deduction introducing triple disjunction. $)
    3mix2d $p |- ( ph -> ( ch \/ ps \/ th ) ) $=
      ( w3o 3mix2 syl ) ABCBDFEBCDGH $.
      $( [8-Jun-2011] $)


    $( Deduction introducing triple disjunction. $)
    3mix3d $p |- ( ph -> ( ch \/ th \/ ps ) ) $=
      ( w3o 3mix3 syl ) ABCDBFEBCDGH $.
      $( [8-Jun-2011] $)
  $}

  $( A biconditional in the antecedent is the same as two implications. $)
  biimpexp $p |- ( ( ( ph <-> ps ) -> ch )
                   <-> ( ( ph -> ps ) -> ( ( ps -> ph ) -> ch ) ) ) $=
    ( wb wi wa dfbi2 imbi1i impexp bitri ) ABDZCEABEZBAEZFZCELMCEEKNCABGHLMCIJ
    $.
    $( [12-Dec-2010] $)


  $( Elimination of two disjuncts in a triple disjunction. $)
  3orel13 $p |- ( ( -. ph /\ -. ch ) -> ( ( ph \/ ps \/ ch ) -> ps ) ) $=
    ( wn w3o wo 3orel3 orel1 sylan9r ) CDABCEABFADBABCGABHI $.
    $( [9-Jun-2011] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Restricted quantification
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Restricted version of ~ 19.30 $)
  r19.30 $p |- ( A. x e. A ( ph \/ ps ) ->
                 ( A. x e. A ph \/ E. x e. A ps ) ) $=
    ( wn wi wral wo wrex ralim orcom df-or bitri ralbii dfrex2 orbi2i imor
    3bitr4i 3imtr4i ) BEZAFZCDGTCDGZACDGZFZABHZCDGUCBCDIZHZTACDJUEUACDUEBAHUAAB
    KBALMNUCUBEZHUHUCHUGUDUCUHKUFUHUCBCDOPUBUCQRS $.
    $( [25-Feb-2011] $)

  ${
    r19.21.1 $e |- ( ph -> A. x ph ) $.
    $( Restricted version of ~ 19.21 $)
    r19.21 $p |- ( A. x e. A ( ph -> ps ) <-> ( ph -> A. x e. A ps ) ) $=
      ( wi wral ra5 hbra1 hbim cv wcel ra4 imim2i com23 r19.21ai impbii ) ABFZC
      DGABCDGZFZABCDEHTRCDASCEBCDIJTACKDLZBSUABFABCDMNOPQ $.
      $( [30-Mar-2011] $)
  $}

  $( Restricted quantification over a union.  (Moved to ~ ralunb in main set.mm
     and may be deleted by mathbox owner, SF. --NM 4-Mar-2012.) $)
  ralunbOLD $p |- ( A. x e. ( A u. B ) ph <->
                 ( A. x e. A ph /\ A. x e. B ph ) ) $=
    ( cv cun wcel wi wal wa wral wo elun imbi1i jaob bitri albii 19.26 df-ral
    anbi12i 3bitr4i ) BEZCDFZGZAHZBIZUBCGZAHZBIZUBDGZAHZBIZJZABUCKABCKZABDKZJUF
    UHUKJZBIUMUEUPBUEUGUJLZAHUPUDUQAUBCDMNUGAUJOPQUHUKBRPABUCSUNUIUOULABCSABDST
    UA $.
    $( [12-Apr-2011] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Misc. Useful Theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Two classes are inequal iff their intersection is a proper subset of one
     of them. $)
  nepss $p |- ( A =/= B <-> ( ( A i^i B ) C. A \/ ( A i^i B ) C. B ) ) $=
    ( wne cin wss wa wo wpss wceq wn neeq1 biimprcd nne syl5ib orrd inss1 jctl
    inss2 orim12i syl ineq2 inidm syl5reqr necon3i adantl ineq1 syl6eq jaoi
    impbii df-pss orbi12i bitr4i ) ABCZABDZAEZUNACZFZUNBEZUNBCZFZGZUNAHZUNBHZGU
    MVAUMUPUSGVAUMUPUSUMUNAIZUSUPJVDUSUMUNABKLUNAMNOUPUQUSUTUPUOABPQUSURABRQSTU
    QUMUTUPUMUOABUNAABIZAADUNAABAUAAUBUCUDUEUSUMURABUNBVEUNBBDBABBUFBUBUGUDUEUH
    UIVBUQVCUTUNAUJUNBUJUKUL $.
    $( [23-Feb-2011] $)

  $( If a class is an element of a pair, then it is one of the two paired
     elements. $)
  elpri $p |- ( A e. { B , C } -> ( A = B \/ A = C ) ) $=
    ( cpr wcel wceq wo elprg ibi ) ABCDZEABFACFGABCJHI $.
    $( [1-Apr-2011] $)

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Closed form of ~ sneqr . $)
    sneqrg $p |- ( A e. X -> ( { A } = { B } -> A = B ) ) $=
      ( vx cv csn wceq wi sneq eqeq1d eqeq1 imbi12d visset sneqr vtoclg ) DEZFZ
      BFZGZPBGZHAFZRGZABGZHDACPAGZSUBTUCUDQUARPAIJPABKLPBDMNO $.
      $( [1-Apr-2011] $)

  $}

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( Distribute intersection over difference. $)
    indifdi $p |- ( ( A \ B ) i^i C ) = ( ( A i^i C ) \ ( B i^i C ) ) $=
      ( vx cdif cin cv wcel wn wa wo pm3.24 intnan anass mtbir biorfi an23
      andi 3bitr4i ianor anbi2i bitr4i elin eldif anbi1i bitri notbii anbi12i
      eqriv ) DABEZCFZACFZBCFZEZDGZAHZUOBHZIZJZUOCHZJZUPUTJZUQUTJZIZJZUOUKHZUOU
      NHZVAVBURUTIZKZJZVEVBURJZVKVBVHJZKVAVJVLVKVLUPUTVHJZJVMUPUTLMUPUTVHNOPUPU
      RUTQVBURVHRSVDVIVBUQUTTUAUBVFUOUJHZUTJVAUOUJCUCVNUSUTUOABUDUEUFVGUOULHZUO
      UMHZIZJVEUOULUMUDVOVBVQVDUOACUCVPVCUOBCUCUGUHUFSUI $.
      $( [14-Apr-2011] $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Properties of relationships
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x y $.  $d B x y $.  $d C x y $.
    $( Membership in a restriction. $)
    elres $p |- ( A e. ( B |` C ) <-> E. x e. C E. y ( A = <. x , y >. /\
                                                        <. x , y >. e. B ) ) $=
      ( cres wcel cv cop wceq wa wex wrex wrel relres elrel mpan eleq1 biimpd
      visset opelres biimpi ancomd syl6com ancld an12 syl6ib 2eximdv mpd
      rexcom4 df-rex exbii excom 3bitri sylibr biimpri expcom biimprd syl9
      imp3a 19.23adv r19.23aiv impbii ) CDEFZGZCAHZBHZIZJZVHDGZKZBLZAEMZVEVFEGZ
      VKKZBLALZVMVEVIBLALZVPVDNVEVQDEOABCVDPQVEVIVOABVEVIVIVNVJKZKVOVEVIVRVIVEV
      HVDGZVRVIVEVSCVHVDRZSVSVJVNVSVJVNKZVFVGDEBTUAZUBUCUDUEVIVNVJUFUGUHUIVMVKA
      EMZBLVOALZBLVPVKABEUJWCWDBVKAEUKULVOBAUMUNUOVLVEAEVNVKVEBVNVIVJVEVNVJVSVI
      VEVJVNVSVSWAWBUPUQVIVEVSVTURUSUTVAVBVC $.
      $( [17-Mar-2011] $)
  $}

  ${
    $d A x y $.  $d B x y $.  $d C x y $.
    elsnres.1 $e |- C e. _V $.
    $( Memebership in restriction to a singleton. $)
    elsnres $p |- ( A e. ( B |` { C } ) <-> E. y ( A = <. C , y >. /\
                                                    <. C , y >. e. B ) ) $=
      ( vx csn cres wcel cv cop wceq wa wex wrex elres rexcom4 opeq1 eqeq2d
      eleq1d anbi12d rexsn exbii 3bitri ) BCDGZHIBFJZAJZKZLZUHCIZMZANFUEOUKFUEO
      ZANBDUGKZLZUMCIZMZANFABCUEPUKFAUEQULUPAUKUPFDEUFDLZUIUNUJUOUQUHUMBUFDUGRZ
      SUQUHUMCURTUAUBUCUD $.
      $( [17-Mar-2011] $)
  $}

  ${
    $d A x y $.  $d B x y $.
    $( The epsilon relation and membership are the same.  General version of
       ~ epel . $)
    epelg $p |- ( ( A e. C /\ B e. D ) -> ( A _E B <-> A e. B ) ) $=
      ( vx vy cv cep wbr wel wb wcel wceq breq1 eleq1 bibi12d breq2 eleq2 epel
      vtocl2g ) EGZFGZHIZEFJZKAUBHIZAUBLZKABHIZABLZKEFABCDUAAMUCUEUDUFUAAUBHNUA
      AUBOPUBBMUEUGUFUHUBBAHQUBBARPEFST $.
      $( [27-Mar-2011] $)
  $}

  $( The difference of two binary relations. $)
  brdif $p |- ( A ( R \ S ) B <-> ( A R B /\ -. A S B ) ) $=
    ( cop cdif wcel wn wa wbr eldif df-br notbii anbi12i 3bitr4i ) ABEZCDFZGPCG
    ZPDGZHZIABQJABCJZABDJZHZIPCDKABQLUARUCTABCLUBSABDLMNO $.
    $( [11-Apr-2011] $)

  ${
    $d A z $.  $d X z $.
    ressn0.1 $e |- X e. _V $.
    ressn0.2 $e |- Y e. _V $.
    $( If ` X ` is not in ` A ` , then the restriction of a singleton of
       ` <. X , Y >. ` to ` A ` is null. $)
    ressn0 $p |- ( -. X e. A -> ( { <. X , Y >. } |` A ) = (/) ) $=
      ( vz wcel wn csn cin cvv cxp c0 cop cres wceq wo cv wal wa elin elsni
      eleq1d biimpa sylbi con3i 19.21aiv eq0 sylibr orcd xpeq0 df-res xpsn
      ineq1i inxp 3eqtr2i syl5eq ) BAGZHZBIZAJZCIZKJZLZMBCNIZAOZUSVAMPZVCMPZQVD
      MPUSVGVHUSFRZVAGZHZFSVGUSVKFVJURVJVIUTGZVIAGZTURVIUTAUAVLVMURVLVIBAVIBUBU
      CUDUEUFUGFVAUHUIUJVAVCUKUIVFVEAKLZJUTVBLZVNJVDVEAULVOVEVNBCDEUMUNUTVBAKUO
      UPUQ $.
      $( [15-Apr-2011] $)
  $}

  ${
    brtp.1 $e |- X e. _V $.
    brtp.2 $e |- Y e. _V $.
    brtp.3 $e |- B e. _V $.
    brtp.4 $e |- D e. _V $.
    brtp.5 $e |- F e. _V $.
    $( A condition for a binary relation over an unordered triple. $)
    brtp $p |- ( X { <. A , B >. , <. C , D >. , <. E , F >. } Y <->
                 ( ( X = A /\ Y = B ) \/
                   ( X = C /\ Y = D ) \/
                   ( X = E /\ Y = F ) ) ) $=
      ( cop ctp wbr wcel wceq w3o wa df-br opex eltp opth 3orbi123i 3bitri ) GH
      ABNZCDNZEFNZOZPGHNZUJQUKUGRZUKUHRZUKUIRZSGARHBRTZGCRHDRTZGERHFRTZSGHUJUAU
      KUGUHUIGHUBUCULUOUMUPUNUQGHABIJKUDGHCDIJLUDGHEFIJMUDUEUF $.
      $( [8-Jun-2011] $)
  $}

  ${
    $d R x y z $.  $d A x y z $.
    $( A quantifier free definition of a founded relationship. $)
    dffr5 $p |- ( R Fr A <->
                  ~P A C_ ( { (/) } u. ran ( _E \ ( _E o. `' R ) ) ) ) $=
      ( vx vz vy cv cpw wcel c0 csn cep ccnv ccom cdif crn cun wi wal wss wne
      wa wbr wn wral wrex wfr wo elun imbi2i df-or impexp visset elpw elsn
      necon3bbii anbi12i wex wel brdif epel brcnv ancom bitri exbii brco
      df-rex 3bitr4i notbii ralnex bitr4i elrn imbi12i bitr3i 3bitri albii
      dfss2 df-fr 3bitr4ri ) CFZAGZHZVSIJZKKBLZMZNZOZPZHZQZCRVSASZVSITZUAZDFZEF
      ZBUBZUCDVSUDZEVSUEZQZCRVTWGSABUFWIWRCWIWAVSWBHZVSWFHZUGZQWAWSUCZWTQZQZWRW
      HXAWAVSWBWFUHUIXAXCWAWSWTUJUIXDWAXBUAZWTQWRWAXBWTUKXEWLWTWQWAWJXBWKVSACUL
      ZUMWSVSICIUNUOUPWNVSWEUBZEUQECURZWPUAZEUQWTWQXGXIEXGWNVSKUBZWNVSWDUBZUCZU
      AXIWNVSKWDUSXJXHXLWPECUTXLWODVSUEZUCWPXKXMWNWMWCUBZWMVSKUBZUAZDUQDCURZWOU
      AZDUQXKXMXPXRDXPWOXQUAXRXNWOXOXQWNWMBEULZDULVADCUTUPWOXQVBVCVDDWNVSKWCXSX
      FVEWODVSVFVGVHWODVSVIVJUPVCVDEVSWEXFVKWPEVSVFVGVLVMVNVOCVTWGVPCEDABVQVR
      $.
      $( [11-Apr-2011] $)
  $}

  ${
    $d R x y z $.  $d A x y z $.
    $( Another quantifier free definition of a founded relationship.  (The
       proof was shortened by Andrew Salmon, 27-Aug-2011.) $)
    dffr6 $p |- ( R Fr A <->
                   ( ~P A \ { (/) } ) C_ ran ( _E \ ( _E o. `' R ) ) ) $=
      ( wfr cpw c0 csn cep ccnv ccom cdif crn cun wss dffr5 ssundif bitri ) ABC
      ADZEFZGGBHIJKZLMQRJSMABNQRSOP $.
      $( [27-Aug-2011] $) $( [28-Jun-2011] $)
  $}

  ${
    $d R x $.  $d A x $.  $d X x $.
    $( A founded relation is irreflexive.  Special case of Proposition 6.23 of
       [TakeutiZaring] p. 30. $)
    frirrc $p |- ( ( R Fr A /\ X e. A ) -> -. X R X ) $=
      ( vx wfr wcel wbr wn cv wa wi wceq eleq1 anbi2d breq1 breq2 bitrd notbid
      imbi12d frirr vtoclg anabsi7 ) ABEZCAFZCCBGZHZUCDIZAFZJZUGUGBGZHZKUCUDJZU
      FKDCAUGCLZUIULUKUFUMUHUDUCUGCAMNUMUJUEUMUJCUGBGUEUGCUGBOUGCCBPQRSDABTUAUB
      $.
      $( [22-Apr-2011] $)
  $}


  ${ $d A x y $.
     dftr6.1 $e |- A e. _V $.

     $( A potential definition of transitivity for sets. $)
     dftr6 $p |- ( Tr A <-> A e. ( _V \ ran ( ( _E o. _E ) \ _E ) ) ) $=
       ( vx vy wel cv wcel wa wi wal cep ccom cdif crn wn wtr cvv wbr wex elrn 
       brdif visset brco epel epelc anbi12i exbii bitri notbii 19.41v exanali 
       bitr3i 3bitri exnal con2bii dftr2 eldif mpbiran 3bitr4i ) CDEZDFZAGZHZCF
       ZAGZIDJZCJZAKKLZKMZNZGZOZAPAQVJMGZVKVGVKVDAVIRZCSVFOZCSVGOCAVIBTVNVOCVNV
       DAVHRZVDAKRZOZHVCDSZVEOZHZVOVDAVHKUAVPVSVRVTVPVDVAKRZVAAKRZHZDSVSDVDAKKC
       UBZBUCWDVCDWBUTWCVBCDUDVAADUBBUEUFUGUHVQVEVDAWEBUEUIUFWAVCVTHDSVOVCVTDUJ
       VCVEDUKULUMUGVFCUNUMUOCDAUPVMAQGVLAQVJUQBURUS $.
       $( [22-Mar-2012] $) $( [18-Mar-2012] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Properties of functions and mappings
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  $( A condition for subset trichotomy for functions. $)
  funpsstri $p |- ( ( Fun H /\ ( F C_ H /\ G C_ H ) /\
                      ( dom F C_ dom G \/ dom G C_ dom F ) ) ->
                    ( F C. G \/ F = G \/ G C. F ) ) $=
    ( wfun wss wa cdm wo w3a wpss wceq w3o cres wi funssres ex anim12d sseq12
    wb ancoms orbi12d ssres2 orim12i syl5bi syl6 3imp sspsstri sylib ) CDZACEZB
    CEZFZAGZBGZEZUNUMEZHZIABEZBAEZHZABJABKBAJLUIULUQUTUIULCUMMZAKZCUNMZBKZFZUQU
    TNUIUJVBUKVDUIUJVBCAOPUIUKVDCBOPQVEVAVCEZVCVAEZHUTUQVEVFURVGUSVAAVCBRVDVBVG
    USSVCBVAARTUAUOVFUPVGUMUNCUBUNUMCUBUCUDUEUFABUGUH $.
    $( [19-Apr-2011] $)

  ${
    $d F p x y z $.  $d G p x y z $.
    $( If a class ` F ` is a proper subset of a function ` G ` , then
       ` dom F C. dom G ` . $)
    fundmpss $p |- ( Fun G -> ( F C. G -> dom F C. dom G ) ) $=
      ( vx vy vz vp wfun wpss cdm wss wn wa wi pssss dmss syl a1i cv wbr wex
      cdif wcel wne c0 pssdifn0 df-pss n0 bicomi 3imtr4i adantl wrel funrel
      reldif cop wceq elrel eleq1 df-br syl6bbr biimpcd 2eximdv mpd ex adantr
      difss ssbri eximi brdif pm3.27bi ssbrd ad2antlr weq wal dffun2 ax4 a4s
      breq2 biimprd syl6 exp3a pm3.26bi syl5 imp adantlr com23 mpdd 19.23adv
      mtod jcad eximdv syld dfss2 notbii exanali visset eldm anbi12i exbii
      3bitr2i sylibr dfpss3 syl6ibr ) BGZABHZAIZBIZJZXFXEJZKZLXEXFHXCXDXGXIXDXG
      MXCXDABJZXGABNZABOPQXCXDXIXCXDLZCRZDRZBSZDTZXMERZASZETZKZLZCTZXIXLFRZBAUA
      ZUBZFTZYBXDYFXCXJABUCLYDUDUCZXDYFABUEABUFYGYFFYDUGUHUIUJXLYEYBFXLYEXMXNYD
      SZDTZCTZYBXCYEYJMZXDXCYDUKZYKXCBUKZYLBULBAUMPYLYEYJYLYELZYCXMXNUNZUOZDTCT
      YJCDYCYDUPYNYPYHCDYEYPYHMYLYPYEYHYPYEYOYDUBYHYCYOYDUQXMXNYDURUSUTUJVAVBVC
      PVDXLYIYACXLYIXPXTYIXPMXLYHXODYDBXMXNBAVEVFVGQXLYHXTDXLYHXTXLYHLZXSXMXNAS
      ZYHYRKZXLYHXOYSXMXNBAVHZVIUJYQXRYREYQXRXMXQBSZYRXDXRUUAMXCYHXDABXMXQXKVJV
      KYQUUAXRYRXCYHUUAXRYRMZMZXDXCYHUUCXCXOUUCYHXCXOUUAUUBXCXOUUALZDEVLZUUBXCU
      UDUUEMZEVMZDVMZCVMZUUFXCYMUUICDEBVNVIUUHUUFCUUGUUFDUUFEVOVPVPPUUEYRXRXNXQ
      XMAVQVRVSVTYHXOYSYTWAWBWCWDWEWFWGWHVCWGWIWJWKWGVBXIXMXFUBZXMXEUBZMCVMZKUU
      JUUKKZLZCTYBXHUULCXFXEWLWMUUJUUKCWNUUNYACUUJXPUUMXTDXMBCWOZWPUUKXSEXMAUUO
      WPWMWQWRWSWTVCWIXEXFXAXB $.
      $( [20-Apr-2011] $)
  $}

  $( A function value is a member of the range plus null. $)
  fvrn0 $p |- ( Fun A -> ( A ` X ) e. ( ran A u. { (/) } ) ) $=
    ( wfun cdm wcel cfv crn c0 csn cun wa fvelrn elun1 syl wn wceq ndmfv 0ex
    snid eleq1 mpbiri elun2 adantl pm2.61dan ) ACZBADEZBAFZAGZHIZJEZUEUFKUGUHEU
    JBALUGUHUIMNUFOZUJUEUKUGHPZUJBAQULUGUIEZUJULUMHUIEHRSUGHUITUAUGUIUHUBNNUCUD
    $.
    $( [8-Jun-2011] $)

  ${
    $d y A $.  $d y C $.  $d y B $.  $d y D $.  $d x y $.
    mpteq.1 $e |- A = C $.
    mpteq.2 $e |- B = D $.
    $( An equality inference for the maps to notation. $)
    mpteqi $p |- ( x e. A |-> B ) = ( x e. C |-> D ) $=
      ( vy cv wcel wceq wa copab cmpt eleq2i eqeq2i anbi12i opabbii df-mpt
      3eqtr4i ) AIZBJZHIZCKZLZAHMUADJZUCEKZLZAHMABCNADENUEUHAHUBUFUDUGBDUAFOCEU
      CGPQRAHBCSAHDEST $.
      $( [27-Oct-2010] $)
  $}

  ${
    $d F x $.  $d G x $.
    $( Equality of functions is determined by their values. $)
    eqfunfv $p |- ( ( Fun F /\ Fun G ) -> ( F = G <->
                    ( dom F = dom G /\
                      A. x e. dom F ( F ` x ) = ( G ` x ) ) ) ) $=
      ( cdm wfn wceq cv cfv wral wa wb wfun eqfnfv funfn syl2anb ) BBDZECCDZEBC
      FPQFAGZBHRCHFAPIJKBLCLAPQBCMBNCNO $.
      $( [10-Jul-2011] $) $( [19-Jun-2011] $)
  $}

  $( An identity for the mapping relationship under restriction. $)
  fresin $p |- ( F : A --> B -> ( F |` X ) : ( A i^i X ) --> B ) $=
    ( wfn crn wss wa cres cin wf wfun cdm wceq funres ineq1 dmres incom eqtri
    syl5eq anim12i df-fn 3imtr4i wi resss rnss ax-mp sstr2 df-f ) CAEZCFZBGZHCD
    IZADJZEZUMFZBGZHABCKUNBUMKUJUOULUQCLZCMZANZHUMLZUMMZUNNZHUJUOURVAUTVCDCOUTU
    SDJZUNVBUSADPVBDUSJVDCDQDUSRSTUACAUBUMUNUBUCUPUKGZULUQUDUMCGVECDUEUMCUFUGUP
    UKBUHUGUAABCUIUNBUMUIUC $.
    $( [10-Sep-2011] $) $( [4-Sep-2011] $)

  $( The value of a function at a restriction is either null or the same as the
     function itself. $)
  fvresval $p |- ( ( ( F |` B ) ` A ) = ( F ` A ) \/
                   ( ( F |` B ) ` A ) = (/) ) $=
    ( wcel wn wo cres cfv wceq c0 exmid fvres nfvres orim12i ax-mp ) ABDZPEZFAC
    BGHZACHIZRJIZFPKPSQTABCLABCMNO $.
    $( [10-Sep-2011] $) $( [4-Sep-2011] $)

  ${ $d A y $. $d x y z $.
     $( The range of a restricted operation class abstraction $)
     rnoprab2 $p |- ran { <. <. x , y >. , z >. | 
     	      	    	  ( ( x e. A /\ y e. B ) /\ ph ) } =
                    { z | E. x e. A E. y e. B ph } $=
       ( cv wcel wa copab2 crn wex cab wrex rnoprab r2ex abbii eqtr4i ) BGEHCGF
       HIAIZBCDJKSCLBLZDMACFNBENZDMSBCDOUATDABCEFPQR $.
       $( [22-Mar-2012] $) $( [21-Mar-2012] $)
  $}

  ${ $d A w z $. $d B w z $. $d C w z $. $d x y w z $. 
     mpt2fun.1 $e |- F = ( x e. A , y e. B |-> C ) $.

     $( The maps-to notation for an operation is always a function $)
     mpt2fun $p |- Fun F $=
       ( vz vw wfun cv wcel wa wceq copab2 wmo weq wi wal eqtr3 ad2ant2l gen2 
       eqeq1 anbi2d mo4 mpbir funoprab cmpt2 df-mpt2 eqtri funeqi ) FJAKCLBKDLM
       ZHKZENZMZABHOZJUOABHUOHPUOULIKZENZMZMHIQZRZISHSVAHIUNURUTULULUMUQETUAUBU
       OUSHIUTUNURULUMUQEUCUDUEUFUGFUPFABCDEUHUPGABHCDEUIUJUKUF $.
       $( [22-Mar-2012] $) $( [21-Mar-2012] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Epsilon induction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d ph y z w $.  $d x y z w $.
    setinds.1 $e |- ( A. y e. x [ y / x ] ph -> ph ) $.
    $( Principle of ` _E ` induction (set induction).  If a property passes
       from all elements of ` x ` to ` x ` itself, then it holds for all
       ` x ` . $)
    setinds $p |- ph $=
      ( vz vw cv cvv wcel visset cab wss wi wceq setind wral wsb df-clab
      ralbii wel ax-17 hbs1 hbral hbim weq raleqf sbequ12 imbi12d chvar sylbi
      dfss3 3imtr4i mpg eqcomi abeq2i mpbi ) BGZHIABJABHABKZHEGZURLZUSURIZMURHN
      EEUROCGURIZCUSPZABEQZUTVAVCABCQZCUSPZVDVBVECUSACBRSVECUQPZAMVFVDMBEVFVDBV
      EBCUSCETBUAABCUBUCABEUBUDBEUEVGVFAVDVECFUQUSFBTCUAFETCUAUFABEUGUHDUIUJCUS
      URUKAEBRULUMUNUOUP $.
      $( [10-Mar-2011] $)
  $}

  ${
    $d x y $.  $d ph y $.
    setinds2f.1 $e |- ( ps -> A. x ps ) $.
    setinds2f.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    setinds2f.3 $e |- ( A. y e. x ps -> ph ) $.
    $( ` _E ` induction schema, using implicit substitution. $)
    setinds2f $p |- ph $=
      ( wsb cv wral sbie ralbii sylbi setinds ) ACDACDHZDCIZJBDPJAOBDPABCDEFKLG
      MN $.
      $( [10-Mar-2011] $)
  $}

  ${
    $d x y $.  $d ph y $.  $d ps x $.
    setinds2.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    setinds2.2 $e |- ( A. y e. x ps -> ph ) $.
    $( ` _E ` induction schema, using implicit substitution. $)
    setinds2 $p |- ph $=
      ( ax-17 setinds2f ) ABCDBCGEFH $.
      $( [10-Mar-2011] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Ordinal numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  ${
    $d x y z A $.
    $( A class of transitive sets is partially ordered by ` _E ` . $)
    elpotr $p |- ( A. z e. A Tr z -> _E Po A ) $=
      ( vx vy wel wa wi wal wral cv wtr cep wpo alral alimi syl ralimi ralcom
      ralbii bitri sylib dftr2 wbr wn df-po epel anbi12i imbi12i elirrv mtbir
      biantrur bitr3i 2ralbii bitr4i 3imtr4i ) CDEZDAEZFZCAEZGZDHZCHZABIZUTABIZ
      DBIZCBIZAJZKZABIBLMZVCUTDBIZCBIZABIZVFVBVKABVBVJCHVKVAVJCUTDBNOVJCBNPQVLV
      JABIZCBIVFVJACBBRVMVECBUTADBBRSTUAVHVBABCDVGUBSVICJZVNLUCZUDZVNDJZLUCZVQV
      GLUCZFZVNVGLUCZGZFZABIZDBICBIVFCDABLUEVDWDCDBBUTWCABUTWBWCVTURWAUSVRUPVSU
      QCDUFDAUFUGCAUFUHVPWBVOCCECUICCUFUJUKULSUMUNUO $.
      $( [15-Oct-2010] $)
  $}

  ${
    $( Given ~ ax-reg , an ordinal is a transitive class totally ordered by
       epsilon. $)
    dford3 $p |- ( Ord A <-> ( Tr A /\ _E Or A ) ) $=
      ( word wtr cep wwe wa wor df-ord wfr df-we zfregfr mpbiran anbi2i bitri
      ) ABACZADEZFOADGZFAHPQOPADIQADJAKLMN $.
      $( [28-Jan-2011] $)
  $}

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( Lemma for ~ dfon2 . $)
    dfon2lem1 $p |- Tr U. { x | ( ph /\ Tr x /\ ps ) } $=
      ( vy cv wtr w3a cab cuni truni wcel wsb hbs1 ax-17 hb3an visset weq
      sbequ12 treq 3anbi123d elabf 3simp2bi mprg ) DEZFZACEZFZBGZCHZIFDUIDUIJUD
      UIKACDLZUEBCDLZUHUJUEUKGCUDUJUEUKCACDMUECNBCDMODPCDQAUJUGUEBUKACDRUFUDSBC
      DRTUAUBUC $.
      $( [28-Feb-2011] $)
  $}

  ${
    $d x y A $.  $d y ph $.  $d y ps $.
    $( Lemma for ~ dfon2 $)
    dfon2lem2 $p |- U. { x | ( x C_ A /\ ph /\ ps ) } C_ A $=
      ( cv wss w3a cab cpw cuni 3simp1 ss2abi df-pw sseqtr4i sspwuni mpbi ) CED
      FZABGZCHZDIZFSJDFSQCHTRQCQABKLCDMNSDOP $.
      $( [28-Feb-2011] $)
  $}

  ${
    $d A x y z w t $.

    $( Lemma for ~ dfon2 .  All sets satisfying the new definition are
       transitive and untangled. $)
    dfon2lem3 $p |- ( A e. B -> ( A. x ( ( x C. A /\ Tr x ) -> x e. A ) ->
                                        ( Tr A /\ A. z e. A -. z e. z ) ) ) $=
      ( vw vt vy wcel cv wpss wtr wa wi wal wel wn wral wss w3a cab cuni wceq
      untelirr wrex eluni2 visset weq sseq1 treq raleq 3anbi123d elab elequ1
      elequ2 bitrd notbid cbvralv biimpi 3ad2ant3 sylbi ra4 syl r19.23aiv mprg
      dfon2lem2 dfon2lem1 cvv psseq1 anbi12d eleq1 imbi12d cla4gv imp ssexg
      mpan sylan csuc csn snssg biimpd pm2.43i cun df-suc sseq1i unss bitr4i
      biimpri trsuc2 ax-mp untuni mprgbir ax-17 hbra1 hb3an hbab hbuni untsucf
      sucexg hbsuc raleqf elabg cbvabv eleq2i syl5bb biimprd com12 mp3an23
      sucssel elssuni syl5 syld mpd syl6 mpan2i dfpss2 syl5ibr mpani mt3i
      pm3.2i mpbii ex ) CDHZAIZCJZYCKZLZYCCHZMZANZCKZBBOZPZBCQZLZYBYILZEIZCRZYP
      KZFFOZPZFYPQZSZETZUAZCUBZYNYOUUEUUDUUDHZYLUUFPBUUDBUUDUCBIZUUDHBAOZAUUCUD
      YLAUUGUUCUEUUHYLAUUCYCUUCHZYLBYCQZUUHYLMUUIYCCRZYEYTFYCQZSZUUJUUBUUMEYCAU
      FEAUGYQUUKYRYEUUAUULYPYCCUHYPYCUIYTFYPYCUJUKULUULUUKUUJYEUULUUJYTYLFBYCFB
      UGZYSYKUUNYSBFOYKFBFUMFBBUNUOUPUQURUSUTZYLBYCVAVBVCUTVDYOUUDCRZUUEPZUUFYR
      UUAECVEZYOUUDCJZUUFUUPUUQLYOUUSUUDKZUUFYQUUAEVFZYOUUSUUTLZUUDCHZUUFUUDVGH
      ZYIUVBUVCMZYBUVDYIUVEYHUVEAUUDVGYCUUDUBZYFUVBYGUVCUVFYDUUSYEUUTYCUUDCVHYC
      UUDUIVIYCUUDCVJVKVLVMUUPYBUVDUURUUDCDVNVOVPUVCUUDVQZCRZUUFUVCUUDVRZCRZUVH
      UVCUVJUVCUVCUVJUUDCCVSVTWAUUPUVJUVHUURUVHUUPUVJLZUVHUUDUVIWBZCRUVKUVGUVLC
      UUDWCWDUUDUVICWEWFWGVOVBUVCUVHUVGUUCHZUUFUVHUVCUVMUVHUVGKZYTFUVGQZUVCUVMM
      UUTUVNUVAUUDWHWIYLBUUDQZUVOUVPUUJAUUCBAUUCWJUUOWKZBFUUDFBUUCUUBFEBYQYRUUA
      FYQFWLYRFWLYTFYPWMWNZWOWPWQWIUVCUVHUVNUVOSZUVMUVCUVGVGHZUVSUVMMUUDCWRUVTU
      VMUVSUVTUVGUUGCRZUUGKZYTFUUGQZSZBTZHUVSUVMUWDUVSBUVGVGUUGUVGUBUWAUVHUWBUV
      NUWCUVOUUGUVGCUHUUGUVGUIYTFGUUGUVGGIUUGHFWLFGUUDFGUUCUUBFEGUVRWOWPWSWTUKX
      AUUCUWEUVGUUBUWDEBYPUUGUBYQUWAYRUWBUUAUWCYPUUGCUHYPUUGUIYTFYPUUGUJUKXBXCX
      DXEVBXFXGXFUVCUVGUUDRUUFUVMUUDUUDCXHUVGUUCXIXJXKXLXMXNUUDCXOXPXQXRUUEUUTU
      VPLYNUUTUVPUVAUVQXSUUEUUTYJUVPYMUUDCUIYLBUUDCUJVIXTVBYA $.
      $( [25-Feb-2011] $)
  $}

  ${
    $d A x y z $.  $d B x y z $.
    dfon2lem4.1 $e |- A e. _V $.
    dfon2lem4.2 $e |- B e. _V $.
    $( Lemma for ~ dfon2 .  If two sets satisfy the new definition, then one is
       a subset of the other. $)
    dfon2lem4 $p |- ( ( A. x ( ( x C. A /\ Tr x ) -> x e. A ) /\
                         A. y ( ( y C. B /\ Tr y ) -> y e. B ) ) ->
                         ( A C_ B \/ B C_ A ) ) $=
      ( vz cv wpss wtr wa wcel wi wal cin wceq wo wss wn wel wral cvv
      dfon2lem3 ax-mp pm3.27d eleq1 eleq2 bitrd notbid rcla4cv syl adantr
      inss1 sseli syl5 pm2.01d elin notbii sylib trin pm3.26d syl2an inex1
      psseq1 treq anbi12d imbi12d cla4v mpan2d adantl anim12d mtod ianor sspss
      mpbi inss2 orel1 orc syl6 olc jaoa mp2ani df-ss sseqin2 orbi12i sylibr )
      AHZCIZWGJZKZWGCLZMZANZBHZDIZWNJZKZWNDLZMZBNZKZCDOZCPZXBDPZQZCDRZDCRZQXAXB
      CIZSZXBDIZSZQZXEXAXHXJKZSXLXAXMXBCLZXBDLZKZXAXBXBLZSZXPSXAXQXAXNXRXQWMXNX
      RMZWTWMGGTZSZGCUAZXSWMCJZYBCUBLWMYCYBKMEAGCUBUCUDZUEYAXRGXBCGHZXBPZXTXQYF
      XTXBYELXQYEXBYEUFYEXBXBUGUHUIUJUKULXBCXBCDUMZUNUOUPXQXPXBCDUQURUSXAXHXNXJ
      XOXAXHXBJZXNYCDJZYHWMWTCDUTWMYCYBYDVAWTYIYAGDUAZDUBLWTYIYJKMFBGDUBUCUDVAV
      BZWMXHYHKZXNMZWTWLYMAXBCDEVCZWGXBPZWJYLWKXNYOWHXHWIYHWGXBCVDWGXBVEVFWGXBC
      UFVGVHULVIXAXJYHXOYKWTXJYHKZXOMZWMWSYQBXBYNWNXBPZWQYPWRXOYRWOXJWPYHWNXBDV
      DWNXBVEVFWNXBDUFVGVHVJVIVKVLXHXJVMUSXLXHXCQZXJXDQZXEXBCRYSYGXBCVNVOXBDRYT
      CDVPXBDVNVOXIYSXEXKYTXIYSXCXEXHXCVQXCXDVRVSXKYTXDXEXJXDVQXDXCVTVSWAWBUKXF
      XCXGXDCDWCDCWDWEWF $.
      $( [25-Feb-2011] $)
  $}


  ${
    $d A x y z $.  $d B x y z $.
    dfon2lem5.1 $e |- A e. _V $.
    dfon2lem5.2 $e |- B e. _V $.
    $( Lemma for ~ dfon2 .  Two sets satisfying the new definition also satisfy
       trichotomy with respect to ` e. ` $)
    dfon2lem5 $p |- ( ( A. x ( ( x C. A /\ Tr x ) -> x e. A ) /\
                         A. y ( ( y C. B /\ Tr y ) -> y e. B ) ) ->
                       ( A e. B \/ A = B \/ B e. A ) ) $=
      ( vz cv wpss wtr wa wcel wi wal wceq wn wo w3o wss dfon2lem4 psseq1 treq
      anbi12d eleq1 imbi12d cla4v exp3a com23 imp wel wral cvv dfon2lem3 ax-mp
      pm3.26d sylan2 mpan9 orim12d orcom syl5ib dfpss2 eqcom notbii anbi2i
      bitri orbi12i andir bitr4i syl5ibr mpand 3orrot 3orass df-or 3bitri
      sylibr ) AHZCIZVPJZKZVPCLZMZANZBHZDIZWCJZKZWCDLZMZBNZKZCDOZPZDCLZCDLZQZMZ
      WNWKWMRZWJCDSZDCSZQZWLWOABCDEFTWJCDIZDCIZQZWOWTWLKZWJXBXAQWOXCWJXBWMXAWNW
      BDJZXBWMMZWIWBXEXFWBXBXEWMWBXBXEWMWAXBXEKZWMMADFVPDOZVSXGVTWMXHVQXBVRXEVP
      DCUAVPDUBUCVPDCUDUEUFUGUHUIWIXEGGUJPZGDUKZDULLWIXEXJKMFBGDULUMUNUOUPWBCJZ
      WIXAWNMWBXKXIGCUKZCULLWBXKXLKMEAGCULUMUNUOWIXAXKWNWIXAXKWNWHXAXKKZWNMBCEW
      CCOZWFXMWGWNXNWDXAWEXKWCCDUAWCCUBUCWCCDUDUEUFUGUHUQURXAXBUSUTXCWRWLKZWSWL
      KZQXDXAXOXBXPCDVAXBWSDCOZPZKXPDCVAXRWLWSXQWKDCVBVCVDVEVFWRWSWLVGVHVIVJWQW
      KWMWNRWKWOQWPWNWKWMVKWKWMWNVLWKWOVMVNVO $.
      $( [25-Feb-2011] $)
  $}

  ${
    $d S x y z w s t $.
    $( Lemma for ~ dfon2 .  A transitive class of sets satisfying the new
       definition satisfies the new definition. $)
    dfon2lem6 $p |- ( ( Tr S /\
                         A. x e. S A. z ( ( z C. x /\ Tr z ) -> z e. x ) ) ->
                       A. y ( ( y C. S /\ Tr y ) -> y e. S ) ) $=
      ( vs vw vt wtr cv wpss wa wel wi wal wral wcel weq wo cdif wss wn pssss
      ssralv syl impcom adantrr ad2ant2lr psseq2 anbi1d elequ2 imbi12d albidv
      rcla4cv imp eldifi rcla4v psseq1 treq anbi12d elequ1 cbvalv syl6ib
      ad2ant2l adantr w3o eleq1a elndif nsyli adantll orel1 trss ssel con3d
      eldifn syl5com syl9 adantl imp31 syl9r mpd 3orrot 3orass bitri syl5ib
      visset dfon2lem5 syl5 mp2and ex ssrdv a4v exp3a com23 syl6 com3l adantld
      imp32 dfpss2 syl5ibr mpand orrd anassrs r19.21aiva wrex c0 wne df-pss
      pssdifn0 sylbi r19.2z ad2antrl eleq1 syl5bir a1i trel syl7 ad2antrr jaod
      r19.23adv syld 19.21aiv ) DHZCIZAIZJZYCHZKZCALZMZCNZADOZKZBIZDJZYMHZKZYMD
      PZMBYLYPYQYLYPKZBEQZBELZRZEDYMSZOZYQYRUUAEUUBYLYPEIZUUBPZUUAYLYPUUEKZKZYS
      YTUUGYMUUDTZYSUAZYTUUGFYMUUDUUGFBLZFELZUUGUUJKZYCFIZJZYFKZCFLZMZCNZGIZUUD
      JZUUSHZKZGELZMZGNZUUKUUGUUJUURUUGYJAYMOZUUJUURMYKYPUVFYBUUEYKYNUVFYOYNYKU
      VFYNYMDTZYKUVFMYMDUBYJAYMDUCUDUEUFUGYJUURAUUMYMAFQZYIUUQCUVHYGUUOYHUUPUVH
      YEUUNYFYDUUMYCUHUIAFCUJUKULUMUDUNUUGUVEUUJYKUUEUVEYBYPUUEYKUVEUUEYKYCUUDJ
      ZYFKZCELZMZCNZUVEUUEUUDDPZYKUVMMUUDDYMUOZYJUVMAUUDDAEQZYIUVLCUVPYGUVJYHUV
      KUVPYEUVIYFYDUUDYCUHUIAECUJUKULUPUDZUVLUVDCGCGQZUVJUVBUVKUVCUVRUVIUUTYFUV
      AYCUUSUUDUQYCUUSURUSCGEUTUKVAVBUEVCVDUULUUKFEQZEFLZVEZUUKUURUVEKUULUVSUVT
      UUKRZRZUUKUWAUULUVSUAZUWCUUKMUUFUUJUWDYLUUEUUJUWDYPUUEUUJUWDUUEUVSUUMUUBP
      UUJUUDUUBUUMVFUUMYMDVGVHUNVIVIUWDUWCUWBUULUUKUVSUWBVJUULUVTUAZUWBUUKMUUFU
      UJUWEYLYPUUEUUJUWEYOUUEUUJUWEMMYNYOUUJUUMYMTZUUEUWEYMUUMVKUWFEBLZUAUWEUUE
      UWFUVTUWGUUMYMUUDVLVMUUDDYMVNVOVPVQVRVIUVTUUKVJUDVSVTUWAUVSUVTUUKVEUWCUUK
      UVSUVTWAUVSUVTUUKWBWCWDCGUUMUUDFWEEWEWFWGWHWIWJUUGYMUUDJZYTUUHUUIKYLYPUUE
      UWHYTMZYKYPUUEUWIMZMYBYKYOUWJYNUUEYKYOUWIUUEYKUVMYOUWIMUVQUVMUWHYOYTUVMUW
      HYOYTUVLUWHYOKZYTMCBCBQZUVJUWKUVKYTUWLUVIUWHYFYOYCYMUUDUQYCYMURUSCBEUTUKW
      KWLWMWNWOWPVQWQYMUUDWRWSWTXAXBXCYRUUCUUAEUUBXDZYQYNUUCUWMMZYLYOYNUUBXEXFZ
      UWNYNUVGYMDXFKUWOYMDXGYMDXHXIUWOUUCUWMUUAEUUBXJWIUDXKYRUUAYQEUUBYRUUAUUEY
      QYRYSUUEYQMZYTYSUWPMYRYSYQUVNUUEYMUUDDXLUVOXMXNYBYTUWPMYKYPYBYTUVNYQUUEYB
      YTUVNYQDYMUUDXOWLUVOXPXQXRWMXSXTVTWIYA $.
      $( [25-Feb-2011] $)
  $}


  ${
    $d A x y z w s t u $.  $d B x y z w t $.
    dfon2lem7.1 $e |- A e. _V $.
    $( Lemma for ~ dfon2 .  All elements of a new ordinal are new ordinals. $)
    dfon2lem7 $p |- ( A. x ( ( x C. A /\ Tr x ) -> x e. A ) ->
                       ( B e. A -> A. y ( ( y C. B /\ Tr y ) -> y e. B ) ) ) $=
      ( vw vt vu vz vs cv wpss wtr wa wcel wi wal wss wel wral w3a cab cuni
      wceq csuc csn wn weq elequ1 elequ2 bitrd notbid cbvralv biimpi ralimi
      untuni sylibr visset sseq1 treq raleq 3anbi123d elab cvv dfon2lem3 ax-mp
      pm3.27d untelirr syl 3ad2ant3 sylbi mprg psseq2 anbi1d imbi12d albidv
      3anbi3i abbii unieqi eleq2i notbii sylib dfon2lem2 ssexi snss mtbi
      intnan cun df-suc sseq1i unss bitr4i mtbir dfon2lem1 trsuc2 wo elsuc
      wrex eluni2 hba1 rcla4cv psseq1 anbi12d cbvalv syl6ib r19.23ai r19.23aiv
      rgen dfon2lem6 mp2an eleq2 mpbiri jaoi sucex elssuni sylbir mp3an23
      ralbii syl6bb cbvabv syl6ss a1i syl5ibr mpani syl5ib mtoi eleq1 cla4v
      mpan2i mtod dfpss2 biimpri mpan nsyl2 ra4 mpbii ) AKZCLZYQMZNZYQCOZPZAQZF
      KZCRZUUDMZBKZGKZLZUUGMZNZBGSZPZBQZGUUDTZUAZFUBZUCZCUDZDCOUUGDLZUUJNZUUGDO
      ZPZBQZPZUUCUURCLZUUSUUCUVFUURCOZUUCUVGUURUEZUUEUUFUUGHKZLZUUJNZBHSZPZBQZH
      UUDTZUAZFUBZUCZRZUVSUURUVRRZUURUFZUVRRZNZUWBUVTUURUVROZUWBIISZUGZIUURTZUW
      DUGZGGSZUGZGYQTZUWGAUUQUWKAUUQTUWFIYQTZAUUQTUWGUWKUWLAUUQUWKUWLUWJUWFGIYQ
      GIUHZUWIUWEUWMUWIIGSUWEGIGUIGIIUJUKULUMUNUOIAUUQUPUQYQUUQOZYQCRZYSUUNGYQT
      ZUAZUWKUUPUWQFYQAURZFAUHZUUEUWOUUFYSUUOUWPUUDYQCUSZUUDYQUTZUUNGUUDYQVAZVB
      VCZUWPUWOUWKYSUUNUWJGYQUUNHHSUGHUUHTZUWJUUNUUHMZUXDUUHVDOUUNUXEUXDNPGURBH
      UUHVDVEVFVGHUUHVHVIUOVJVKVLUWGUURUUROZUGUWHIUURVHUXFUWDUURUVRUURUUQUVQUUP
      UVPFUUOUVOUUEUUFUUNUVNGHUUDGHUHZUUMUVMBUXGUUKUVKUULUVLUXGUUIUVJUUJUUHUVIU
      UGVMVNGHBUJVOVPZUMVQVRVSVTWAWBVFUURUVRUURCEUUFUUOFCWCZWDZWEWFWGUVSUURUWAW
      HZUVRRUWCUVHUXKUVRUURWIZWJUURUWAUVRWKWLWMUUCUWACRZUVSUVGUUCUURCRZUXMUVSUX
      IUUCUVHCRZUVSUXNUXMNZUXOUVSPUUCUXOUVHJKZCRZUXQMZYQUVILZYSNZAHSZPZAQZHUXQT
      ZUAZJUBZUCZUVRUXOUVHMZUYDHUVHTZUVHUYHRZUURMZUYIUUEUUOFWNZUURWOVFUYDHUVHUV
      IUVHOUVIUUROZUVIUURUDZWPUYDUVIUURHURWQUYNUYDUYOUYNHASZAUUQWRZUYDAUVIUUQWS
      ZUYPUYDAUUQUYCAWTUWNUWQUYPUYDPZUXCUWPUWOUYSYSUWPUYPUVNUYDUUNUVNGUVIYQUXHX
      AZUVMUYCBABAUHZUVKUYAUVLUYBVUAUVJUXTUUJYSUUGYQUVIXBUUGYQUTXCBAHUIVOXDXEVJ
      VKXFVKUYOUYDYQUURLZYSNZYQUUROZPZAQZUYLIKZUVILZVUGMZNZIHSZPZIQZHUURTVUFUYM
      VUMHUURUYNUYQVUMUYRUYPVUMAUUQUWNUWQUYPVUMPZUXCUWPUWOVUNYSUWPUYPUVNVUMUYTU
      VMVULBIBIUHZUVKVUJUVLVUKVUOUVJVUHUUJVUIUUGVUGUVIXBUUGVUGUTXCBIHUIVOXDXEVJ
      VKXGVKXHHAIUURXIXJUYOUYCVUEAUYOUYAVUCUYBVUDUYOUXTVUBYSUVIUURYQVMVNUVIUURY
      QXKVOVPXLXMVKXHUXOUYIUYJUAZUVHUYGOUYKUYFVUPJUVHUURUXJXNUXQUVHUDUXRUXOUXSU
      YIUYEUYJUXQUVHCUSUXQUVHUTUYDHUXQUVHVAVBVCUVHUYGXOXPXQUYGUVQUYFUVPJFJFUHZU
      XRUUEUXSUUFUYEUVOUXQUUDCUSUXQUUDUTVUQUYEUYDHUUDTUVOUYDHUXQUUDVAUYDUVNHUUD
      UYCUVMABABUHZUYAUVKUYBUVLVURUXTUVJYSUUJYQUUGUVIXBYQUUGUTXCABHUIVOXDXRXSVB
      XTVSYAYBUXOUXKCRUXPUVHUXKCUXLWJUURUWACWKWLYCYDUURCUXJWEYEYFUUCUVFUYLUVGUY
      MUUBUVFUYLNZUVGPAUURUXJYQUURUDZYTVUSUUAUVGVUTYRUVFYSUYLYQUURCXBYQUURUTXCY
      QUURCYGVOYHYIYJUXNUUSUGZUVFUXIUVFUXNVVANUURCYKYLYMYNUUSUUGVUGLZUUJNZBISZP
      ZBQZICTZUVEUUSVVFIUURTVVGVVFIUURVUGUUROIASZAUUQWRVVFAVUGUUQWSVVHVVFAUUQUW
      NUWOYSVVFIYQTZUAZVVHVVFPZUUPVVJFYQUWRUWSUUEUWOUUFYSUUOVVIUWTUXAUWSUUOUWPV
      VIUXBUUNVVFGIYQUWMUUMVVEBUWMUUKVVCUULVVDUWMUUIVVBUUJUUHVUGUUGVMVNGIBUJVOV
      PUMXSVBVCVVIUWOVVKYSVVFIYQYOVJVKXGVKXHVVFIUURCVAYPVVFUVDIDCVUGDUDZVVEUVCB
      VVLVVCUVAVVDUVBVVLVVBUUTUUJVUGDUUGVMVNVUGDUUGXKVOVPXAVIVI $.
      $( [25-Feb-2011] $)
  $}


  ${
    $d A x y z w s t $.
    $( Lemma for ~ dfon2 .  The intersection of a non-empty class ` A ` of new
       ordinals is itself a new ordinal and is contained within ` A ` $)
    dfon2lem8 $p |- ( ( A =/= (/) /\
                         A. x e. A A. y ( ( y C. x /\ Tr y ) -> y e. x ) ) ->
                       ( A. z ( ( z C. |^| A /\ Tr z ) -> z e. |^| A ) /\
                         |^| A e. A ) ) $=
      ( vt vw c0 wne cv wpss wtr wa wel wi wal wral cint wcel wn cvv visset
      dfon2lem3 ax-mp pm3.26d ralimi trint syl adantl cuni dfon2lem7 19.21aiv
      df-ral 19.21v albii bitr4i impexp 2albii wrex eluni2 biimpi imim1i alimi
      alcom wex 19.23v df-rex imbi1i bitri 3imtr4i sylbir sylbi wss intssuni
      ssralv adantr mpd intex imp pm3.27d untelirr adantlr wceq weq psseq2
      anbi1d elequ2 imbi12d albidv rcla4cv psseq1 treq anbi12d eleq1 cla4gv
      exp3a dfpss2 syl5ibr exp4b com45 com23 intss1 syl5 mpdd mpid eqcom
      notbii syl7ib r19.21aiv ralim risset ralnex syl5ib wb elintg ad2antrr
      sylibrd mt3d ex ancld dfon2lem6 mp2and ) DGHZBIZAIZJZYCKZLZBAMZNZBOZADPZL
      ZDQZKZEIZFIZJYOKLEFMNEOZFYMPZCIZYMJYSKLYSYMRNCOZYMDRZLZYKYNYBYKYDKZADPYNY
      JUUCADYJUUCCCMSCYDPZYDTRYJUUCUUDLNAUAZBCYDTUBUCUDUEADUFUGUHYLYQFDUIZPZYRY
      KUUGYBYKFAMZYQNZFOZADPZUUGYJUUJADYJUUIFBEYDYPUUEUJUKUEUUKYDDRZUUINZFOZAOZ
      UUGUUKUULUUJNZAOUUOUUJADULUUNUUPAUULUUIFUMUNUOUUOUULUUHLZYQNZFOAOZUUGUURU
      UMAFUULUUHYQUPUQUUHADURZYQNZFOZYPUUFRZYQNZFOUUSUUGUVAUVDFUVCUUTYQUVCUUTAY
      PDUSUTVAVBUUSUURAOZFOUVBUURAFVCUVEUVAFUVEUUQAVDZYQNUVAUUQYQAVEUUTUVFYQUUH
      ADVFVGUOUNVHYQFUUFULVIVJVKUGUHYBUUGYRNZYKYBYMUUFVLUVGDVMYQFYMUUFVNUGVOVPY
      LYTUUBYNYRLYLYTUUAYLYTUUAYLYTLZUUAYMYMRZYBYTUVISZYKYBYTLZEEMSEYMPZUVJUVKY
      NUVLYBYTYNUVLLZYBYMTRZYTUVMNDVQZCEYMTUBVKVRZVSEYMVTUGWAUVHUUASZYMYORZEDPZ
      UVIUVHYOYMWBZSZEDPZUVSUVQUVHUWAUVRNZEDPUWBUVSNUVHUWCEDUVHYODRZYMYOWBZSZUV
      RUWAUVHUWDYNUWFUVRNZYBYTYNYKUVKYNUVLUVPUDWAYLUWDYNUWGNZNYTYLUWDYCYOJZYFLZ
      BEMZNZBOZUWHYKUWDUWMNYBYJUWMAYODAEWCZYIUWLBUWNYGUWJYHUWKUWNYEUWIYFYDYOYCW
      DWEAEBWFWGWHWIUHYBUWDUWMUWHNZNYKYBYMYOVLZUWOUWDYBUWMUWPUWHYBUWMUWPUWFYNUV
      RYBUWMUWPUWFYNUVRNZYBUWMLZYMYOJZUWQUWPUWFLUWRUWSYNUVRYBUWMUWSYNLZUVRNZYBU
      VNUWMUXANUVOUWLUXABYMTYCYMWBZUWJUWTUWKUVRUXBUWIUWSYFYNYCYMYOWJYCYMWKWLYCY
      MYOWMWGWNVKVRWOYMYOWPWQWRWSWTYODXAXBVOXCVOXDUVTUWEYOYMXEXFXGXHUWAUVREDXIU
      GUVQUVTEDURZSUWBUUAUXCEYMDXJXFUVTEDXKUOXLYBUVIUVSXMZYKYTYBUVNUXDUVOEYMDTX
      NVKXOXPXQXRXSFCEYMXTXBYA $.
      $( [26-Feb-2011] $)
  $}

  ${
    $d A x y z w s t u v $.
    $( Lemma for ~ dfon2 .  A class of new ordinals is well-founded by
       ` _E ` . $)
    dfon2lem9 $p |- ( A. x e. A A. y ( ( y C. x /\ Tr y ) -> y e. x )
                         -> _E Fr A ) $=
      ( vz vt vw vu cv wpss wtr wa wel wi wal wral wss c0 wne wn wrex cep wfr
      ssralv cint wcel wceq eleq2 notbid ralbidv rcla4ev dfon2lem8 pm3.27d
      pm3.26d cvv eleq1 dfon2lem3 imp untelirr syl syl5cbi a1dd trss eqss
      biimpri expcom syl6 com23 con3 pm2.61d intex sylanb syldan intss1 syl5
      r19.21aiv sylanc syl6com imp3a 19.21aiv wbr df-fr epel notbii ralbii
      rexbii imbi2i albii bitri sylibr ) BHZAHIWJJKBALMBNZACOZDHZCPZWMQRZKZEFLZ
      SZEWMOZFWMTZMZDNZCUAUBZWLXADWLWNWOWTWNWLWKAWMOZWOWTMWKAWMCUCWOXDWTWMUDZWM
      UEZEHZXEUEZSZEWMOZWTWOXDKZWSXJFXEWMFHZXEUFZWRXIEWMXMWQXHXLXEXGUGUHUIUJXKG
      HZXEIXNJKXNXEUEMGNZXFABGWMUKZULXKXIEWMXKXEXGPZXIEDLWOXDXOXQXIMZXKXOXFXPUM
      XEUNUEZXOXRWOXSXOKZXEXGUFZXRXTYAXIXQYAXEXEUEZSZXIXTYAYBXHXEXGXEUOUHXTAALS
      AXEOZYCXTXEJZYDXSXOYEYDKGAXEUNUPUQZULAXEURUSUTVAXTXQYASZXIXTXQXHYAMYGXIMX
      TXHXQYAXTXHXGXEPZXQYAMXTYEXHYHMXTYEYDYFUMXEXGVBUSXQYHYAYAXQYHKXEXGVCVDVEV
      FVGXHYAVHVFVGVIWMVJVKVLXGWMVMVNVOVPVEVQVRVSXCWPXGXLUAVTZSZEWMOZFWMTZMZDNX
      BDFECUAWAYMXADYLWTWPYKWSFWMYJWREWMYIWQEFWBWCWDWEWFWGWHWI $.
      $( [3-Mar-2011] $)
  $}

  ${
    $d x y z w t u v $.
    $( ` On ` consists of all sets that contain all its transitive proper
       subsets.  This definition comes from J. R. Isbell, "A Definition of
       Ordinal Numbers," American Mathematical Monthly, vol 67 (1960), pp.
       51-52. $)
    dfon2 $p |- On = { x | A. y ( ( y C. x /\ Tr y ) -> y e. x ) } $=
      ( vz vw vu vt vv con0 cv word cab wpss wtr wa wel wi wal df-on wss wne
      tz7.7 df-pss syl6bbr exbiri com23 imp3a 19.21aiv cep wwe df-ord wn wral
      cvv wcel visset dfon2lem3 ax-mp pm3.26d wfr weq w3o dfon2lem7 r19.21aiv
      dfon2lem9 psseq2 anbi1d elequ2 imbi12d albidv psseq1 treq anbi12d elequ1
      cbvalv syl6bb rcla4cv anim12d dfon2lem5 syl6 r19.21aivv jca syl wbr
      dfwe2 epel biid 3orbi123i 2ralbii anbi2i bitri sylibr sylanbrc impbii
      abbii eqtri ) HAIZJZAKBIZWPLZWRMZNBAOZPZBQZAKARWQXCAWQXCWQXBBWQWSWTXAWQWT
      WSXAWQWTXAWSWQWTNXAWRWPSWRWPTNWSWPWRUAWRWPUBUCUDUEUFUGWQWPMZWPUHUIZXCWPUJ
      XCXDCCOUKCWPULZWPUMUNXCXDXFNPAUOZBCWPUMUPUQURXCWPUHUSZCDOZCDUTZDCOZVAZDWP
      ULCWPULZNZXEXCEIZFIZLZXOMZNZEFOZPZEQZFWPULZXNXCYBFWPBEWPXPXGVBVCYCXHXMFEW
      PVDYCXLCDWPWPYCCAOZDAOZNGIZCIZLZYFMZNZGCOZPZGQZWRDIZLZWTNZBDOZPZBQZNXLYCY
      DYMYEYSYBYMFYGWPFCUTZYBXOYGLZXRNZECOZPZEQYMYTYAUUDEYTXSUUBXTUUCYTXQUUAXRX
      PYGXOVEVFFCEVGVHVIUUDYLEGEGUTZUUBYJUUCYKUUEUUAYHXRYIXOYFYGVJXOYFVKVLEGCVM
      VHVNVOVPYBYSFYNWPFDUTZYBXOYNLZXRNZEDOZPZEQYSUUFYAUUJEUUFXSUUHXTUUIUUFXQUU
      GXRXPYNXOVEVFFDEVGVHVIUUJYREBEBUTZUUHYPUUIYQUUKUUGYOXRWTXOWRYNVJXOWRVKVLE
      BDVMVHVNVOVPVQGBYGYNCUODUOVRVSVTWAWBXEXHYGYNUHWCZXJYNYGUHWCZVAZDWPULCWPUL
      ZNXNCDWPUHWDUUOXMXHUUNXLCDWPWPUULXIXJXJUUMXKCDWEXJWFDCWEWGWHWIWJWKWLWMWNW
      O $.
      $( [20-Feb-2011] $)
  $}

  ${
    $d x A $.
    $( Lemma for dford4 .  A new-style ordinal is transitive. $)
    dford4lem1 $p |- ( A = { x | ( x C. A /\ Tr x ) } -> Tr A ) $=
      ( cv wpss wtr wa cab wceq cpw wss pssss adantr ss2abi df-pw sseqtr4i
      sseq1 mpbiri dftr4 sylibr ) BACZBDZTEZFZAGZHZBBIZJZBEUEUGUDUFJUDTBJZAGUFU
      CUHAUAUHUBTBKLMABNOBUDUFPQBRS $.
      $( [6-Apr-2011] $)
  $}

  ${
    $d x A $.
    $( Lemma for dford4 .  A new-style ordinal is irreflexive in membership. $)
    dford4lem2 $p |- ( A = { x | ( x C. A /\ Tr x ) } -> -. A e. A ) $=
      ( cv wpss wtr wa cab wceq wcel wn eleq2 psseq1 treq anbi12d elabg ibi
      pssirr pm2.21i adantr syl syl6bi pm2.01d ) BACZBDZUCEZFZAGZHZBBIZUHUIBUGI
      ZUIJZBUGBKUJBBDZBEZFZUKUJUNUFUNABUGUCBHUDULUEUMUCBBLUCBMNOPULUKUMULUKBQRS
      TUAUB $.
      $( [6-Apr-2011] $)
  $}


  ${
    $d x y $.
    $( The domain of the epsilon relation is the universe. $)
    domep $p |- dom _E = _V $=
      ( vx vy cep cdm cv wbr wex cab cvv df-dm wceq df-v equid wcel el epel
      exbii mpbir 2th abbii eqtri eqtr4i ) CDAEZBEZCFZBGZAHZIABCJIUCUCKZAHUGALU
      HUFAUHUFAMUFUCUDNZBGABOUEUIBABPQRSTUAUB $.
      $( [27-Oct-2010] $)
  $}

  $( Ordinal two is not zero. $)
  2on0 $p |- 2o =/= (/) $=
    ( c2o c0 wne c1o csuc nsuceq0 df-2o neeq1i mpbir ) ABCDEZBCDFAJBGHI $.
    $( [10-Jul-2011] $) $( [17-Jun-2011] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Defined equality axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  $( A version of ~ ax-ext for use with defined equality. $)
  axextdfeq $p |- E. z ( ( z e. x -> z e. y )
                    -> ( ( z e. y -> z e. x ) -> ( x e. w -> y e. w ) ) ) $=
    ( wel wb wi wex weq axextnd ax-13 imim2i eximi ax-mp biimpexp exbii mpbi )
    CAEZCBEZFZADEBDEGZGZCHZRSGSRGUAGGZCHTABIZGZCHUCCABJUFUBCUEUATABDKLMNUBUDCRS
    UAOPQ $.
    $( [12-Dec-2010] $)

  $( A version of ~ ax-13 for use with defined equality. $)
  ax13dfeq $p |- E. z ( ( z e. x -> z e. y ) -> ( w e. x -> w e. y ) ) $=
    ( weq wex wel wi a9e ax-13 equcoms imim12d eximi ax-mp ) CDEZCFCAGZCBGZHDAG
    ZDBGZHHZCFCDIOTCORPQSRPHDCDCAJKCDBJLMN $.
    $( [12-Dec-2010] $)

  ${
    $d w x $.  $d w y $.  $d z w $.
    $( ~ ax-ext with distinctors instead of distinct variable restrictions. $)
    axextdist $p |- ( ( -. A. z z = x /\ -. A. z z = y )
                      -> ( A. z ( z e. x <-> z e. y ) -> x = y ) ) $=
      ( vw weq wal wn wa wel wb hbnae hban wi dveel2 adantr adantl hbbid
      elequ1 bibi12d a1i cbvald axext3 syl6bir ) CAECFGZCBECFGZHZCAIZCBIZJZCFDA
      IZDBIZJZDFABEUFULUIDCUDUECCACKCBCKLZUFUJUKCUMUDUJUJCFMUECADNOUEUKUKCFMUDC
      BDNPQDCEZULUIJMUFUNUJUGUKUHDCARDCBRSTUAABDUBUC $.
      $( [13-Dec-2010] $)

    $( ~ axext4 with distinctors instead of distinct variable restrictions. $)
    axext4dist $p |- ( ( -. A. z z = x /\ -. A. z z = y )
                      -> ( x = y <-> A. z ( z e. x <-> z e. y ) ) ) $=
      ( weq wal wn wa wel wb wi ax-12 imp hbnae hban elequ2 a1i alimd syld
      axextdist impbid ) CADCEFZCBDCEFZGZABDZCAHCBHIZCEZUCUDUDCEZUFUAUBUDUGJABC
      KLUCUDUECUAUBCCACMCBCMNUDUEJUCABCOPQRABCST $.
      $( [13-Dec-2010] $)
  $}

  ${
    $d x y $.
    19.12b.1 $e |- ( ph -> A. y ph ) $.
    19.12b.2 $e |- ( ps -> A. x ps ) $.
    $( ~ 19.12vv with not-free hypotheses, instead of distinct variable
       conditions. $)
    19.12b $p |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) ) $=
      ( wi wal wex 19.21 exbii hbal 19.36 albii bitr2i 3bitri ) ABGZDHZCIABDHZG
      ZCIACHZSGZQCIZDHZRTCABDEJKASCBCDFLMUDUABGZDHUBUCUEDABCFMNUABDADCELJOP $.
      $( [13-Dec-2010] $)
  $}

  $( There is always a set not in ` y ` . $)
  exnel $p |- E. x -. x e. y $=
    ( cv wcel wn wex elirr hbth wceq ax-13 con3d a4ime ax-mp ) BCZNDZEZACZNDZEZ
    AFNGZPSABPATHQNIROABBJKLM $.
    $( [13-Dec-2010] $)

  ${
    $d x z $.  $d y z $.
    $( Distinctors in terms of membership.  (NOTE: this only works with
       relations where we can prove ~ el and ~ elirrv .) $)
    distel $p |- ( -. A. y y = x <-> -. A. y -. x e. y ) $=
      ( vz weq wal wn wel wex el hbnae dveel1 hbnd wb wi elequ2 notbid a1i
      cbvald df-ex 3bitr4g mpbii sylib elirrv elequ1 mtbii alimi con3i impbii
      ) BADZBEZFZABGZFZBEZFZUKULBHZUOUKACGZCHZUPACIUKUQFZCEZFUOURUPUKUTUNUKUSUM
      CBBABJZUKUQBVABACKLCBDZUSUMMNUKVBUQULCBAOPQRPUQCSULBSZTUAVCUBUJUNUIUMBUIB
      BGULBUCBABUDUEUFUGUH $.
      $( [15-Dec-2010] $)
  $}

  $( ~ axextnd as a biconditional. $)
  axextndbi $p |- E. z ( x = y <-> ( z e. x <-> z e. y ) ) $=
    ( cv wceq wcel wb wex wi wa axextnd elequ2 pm3.2 ax-mp eximi dfbi2 exbii
    mpbir ) ADZBDZEZCDZSFUBTFGZGZCHUAUCIZUCUAIZJZCHZUFCHUHCABKUFUGCUEUFUGIABCLU
    EUFMNONUDUGCUAUCPQR $.
    $( [14-Dec-2010] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Hypothesis builders
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  $( A more general form of ~ hbnt . $)
  hbntg $p |- ( A. x ( ph -> A. x ps ) -> ( -. ps -> A. x -. ph ) ) $=
    ( wal wi wn con3 al2imi ax-6o con1i syl5 ) ABCDZEZCDLFZCDZAFZCDBFMNPCALGHOB
    BCIJK $.
    $( [13-Dec-2010] $)

  $( A more general and closed form of ~ hbim . $)
  hbimtg $p |- ( ( A. x ( ph -> A. x ch ) /\ ( ps -> A. x th ) ) ->
                ( ( ch -> ps ) -> A. x ( ph -> th ) ) ) $=
    ( wal wi wa wn hbntg pm2.21 alimi syl6 adantr ax-1 imim2i adantl jad ) ACEF
    GEFZBDEFZGZHCBADGZEFZSCIZUCGUASUDAIZEFUCACEJUEUBEADKLMNUABUCGSTUCBDUBEDAOLP
    QR $.
    $( [13-Dec-2010] $)

  $( A more general and closed form of ~ hbal . $)
  hbaltg $p |- ( A. x ( ph -> A. y ps ) -> ( A. x ph -> A. y A. x ps ) ) $=
    ( wal wi alim ax-7 imim2i ax-mp ) ABDEZFCEZACEZKCEZFZFLMBCEDEZFZFAKCGOQLNPM
    BCDHIIJ $.
    $( [13-Dec-2010] $)

  ${
    hbg.1 $e |- ( ph -> A. x ps ) $.
    $( A more general form of ~ hbn . $)
    hbng $p |- ( -. ps -> A. x -. ph ) $=
      ( wal wi wn hbntg mpg ) ABCEFBGAGCEFCABCHDI $.
      $( [13-Dec-2010] $)

    ${
      hbg.2 $e |- ( ch -> A. x th ) $.
      $( A more general form of ~ hbim . $)
      hbimg $p |- ( ( ps -> ch ) -> A. x ( ph -> th ) ) $=
        ( wal wi ax-gen hbimtg mp2an ) ABEHIZEHCDEHIBCIADIEHIMEFJGACBDEKL $.
        $( [13-Dec-2010] $)
    $}
  $}

  ${
    $d A x y $.  $d B x y $.
    $( Membership in a range. $)
    elrn2g $p |- ( A e. C -> ( A e. ran B <-> E. x <. x , A >. e. B ) ) $=
      ( vy cv cop wcel wex crn wceq opeq2 eleq1d exbidv dfrn3 elab2g ) AFZEFZGZ
      CHZAIQBGZCHZAIEBCJDRBKZTUBAUCSUACRBQLMNAECOP $.
      $( [2-Feb-2011] $)

    $( Membership in a range. $)
    elrng $p |- ( A e. C -> ( A e. ran B <-> E. x x B A ) ) $=
      ( wcel crn cv cop wex wbr elrn2g wb df-br exbii a1i bitr4d ) BDEZBCFEAGZB
      HCEZAIZRBCJZAIZABCDKUBTLQUASARBCMNOP $.
      $( [2-Feb-2011] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              The Predecessor Class
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  $c Pred $.
  $( The predecessors symbol. $)
  cpred $a class Pred ( R , A , X ) $.

  $( Define the predecessor class of a relationship.  This is the class of all
     elements ` y ` of ` A ` such that ` y R X ` . $)
  df-pred $a |- Pred ( R , A , X ) = ( A i^i ( `' R " { X } ) ) $.

  $( Equality theorem for the predecessor class. $)
  predeq1 $p |- ( R = S -> Pred ( R , A , X ) = Pred ( S , A , X ) ) $=
    ( wceq ccnv csn cima cin cpred cnveq imaeq1d ineq2d df-pred 3eqtr4g ) BCEZA
    BFZDGZHZIACFZRHZIABDJACDJPSUAAPQTRBCKLMABDNACDNO $.
    $( [2-Feb-2011] $)

  $( Equality theorem for the predecessor class. $)
  predeq2 $p |- ( A = B -> Pred ( R , A , X ) = Pred ( R , B , X ) ) $=
    ( wceq ccnv csn cima cin cpred ineq1 df-pred 3eqtr4g ) ABEACFDGHZIBNIACDJBC
    DJABNKACDLBCDLM $.
    $( [2-Feb-2011] $)

  $( Equality theorem for the predecessor class. $)
  predeq3 $p |- ( X = Y -> Pred ( R , A , X ) = Pred ( R , A , Y ) ) $=
    ( wceq ccnv csn cima cin cpred sneq imaeq2d ineq2d df-pred 3eqtr4g ) CDEZAB
    FZCGZHZIAQDGZHZIABCJABDJPSUAAPRTQCDKLMABCNABDNO $.
    $( [2-Feb-2011] $)

  $( If ` A ` is a subset of ` B ` , then their predecessor classes are also
     subsets. $)
  predpredss $p |- ( A C_ B -> Pred ( R , A , X ) C_ Pred ( R , B , X ) ) $=
    ( wss ccnv csn cima cin cpred ssrin df-pred 3sstr4g ) ABEACFDGHZIBNIACDJBCD
    JABNKACDLBCDLM $.
    $( [2-Feb-2011] $)

  $( The predecessor class of ` A ` is a subset of ` A ` $)
  predss $p |- Pred ( R , A , X ) C_ A $=
    ( cpred wss ccnv csn cima cin inss1 df-pred sseq1i mpbir ) ABCDZAEABFCGHZIZ
    AEAOJNPAABCKLM $.
    $( [2-Feb-2011] $)

  $( Another subset/predecessor class relationship. $)
  sspred $p |- ( ( B C_ A /\ Pred ( R , A , X ) C_ B ) ->
                 Pred ( R , A , X ) = Pred ( R , B , X ) ) $=
    ( cin wceq ccnv csn cima cpred wss wa ineq1 eqeq1d biimpa df-pred eqeq12i
    biimpri eqcoms syl sseqin2 sseq1i df-ss in23 eqeq1i 3bitri syl2anb ) ABEZBF
    ZUHCGDHIZEZAUJEZFZACDJZBCDJZFZBAKUNBKZUIUMLBUJEZULFZUPUIUMUSUIUKURULUHBUJMN
    OUPULURUPULURFUNULUOURACDPZBCDPQRSTBAUAUQULBKULBEZULFUMUNULBUTUBULBUCVAUKUL
    AUJBUDUEUFUG $.
    $( [6-Feb-2011] $)

  ${
    $d R y $.  $d X y $.
    dfpred2.1 $e |- X e. _V $.
    $( An alternate definition of predecessor class when ` X ` is a set. $)
    dfpred2 $p |- Pred ( R , A , X ) = ( A i^i { y | y R X } ) $=
      ( cpred ccnv csn cima cin cv wbr cab df-pred cvv wcel wceq iniseg ax-mp
      ineq2i eqtri ) BCDFBCGDHIZJBAKDCLAMZJBCDNUBUCBDOPUBUCQEACDORSTUA $.
      $( [8-Feb-2011] $)
  $}

  ${
    elpred.1 $e |- Y e. _V $.
    $( Membership in a predecessor class. $)
    elpred $p |- ( X e. D -> ( Y e. Pred ( R , A , X ) <->
                                ( Y e. A /\ Y R X ) ) ) $=
      ( wcel cpred ccnv csn cima wa wbr wb cin df-pred eleq2i elin bitri a1i
      eliniseg anbi2d bitrd ) DBGZEACDHZGZEAGZECIDJKZGZLZUGEDCMZLUFUJNUDUFEAUHO
      ZGUJUEULEACDPQEAUHRSTUDUIUKUGCDEBFUAUBUC $.
      $( [4-Feb-2011] $)
  $}

  $( Membership in a predecessor class. $)
  elpredg $p |- ( ( X e. B /\ Y e. A ) ->
                  ( Y e. Pred ( R , A , X ) <-> Y R X ) ) $=
    ( wcel wa cpred ccnv csn cima wbr wb cin df-pred eleq2i elin bitri baib
    adantl cop elimasng df-br a1i brcnvg 3bitr2d bitrd ) DBFZEAFZGZEACDHZFZECIZ
    DJKZFZEDCLZUIULUOMUHULUIUOULEAUNNZFUIUOGUKUQEACDOPEAUNQRSTUJUODEUAUMFZDEUML
    ZUPUMDEBAUBUSURMUJDEUMUCUDDEBACUEUFUG $.
    $( [17-Apr-2011] $)

  ${
    $d A y $.  $d F y $.  $d G y $.  $d X y $.  $d R y $.
    predreseq.1 $e |- X e. _V $.
    $( Equality of restriction to predecessor classes. $)
    predreseq $p |- ( ( F Fn A /\ G Fn A ) ->
                       ( ( F |` Pred ( R , A , X ) ) =
                         ( G |` Pred ( R , A , X ) ) <->
                         A. y e. A ( y R X -> ( F ` y ) = ( G ` y ) ) ) ) $=
      ( wfn wa cpred cres wceq cv cfv wral wbr wi wss wb predss fvreseq mpan2
      wcel wal df-ral cvv visset elpred ax-mp imbi1i albii impexp 3bitri
      bitr4i syl6bb ) DBHEBHIZDBCFJZKEUQKLZAMZDNUSENLZAUQOZUSFCPZUTQZABOZUPUQBR
      URVASBCFTABUQDEUAUBVAUSBUCZVCQZAUDZVDVAUSUQUCZUTQZAUDVEVBIZUTQZAUDVGUTAUQ
      UEVIVKAVHVJUTFUFUCVHVJSGBUFCFUSAUGUHUIUJUKVKVFAVEVBUTULUKUMVCABUEUNUO $.
      $( [8-Feb-2011] $)
  $}

  ${
    predasetex.1 $e |- A e. _V $.
    $( The predecessor class exists when ` A ` does. $)
    predasetex $p |- Pred ( R , A , X ) e. _V $=
      ( cpred ccnv csn cima cin cvv df-pred inex1 eqeltri ) ABCEABFCGHZIJABCKAN
      DLM $.
      $( [8-Feb-2011] $)
  $}

  ${
    $d R x z $.  $d R y z $.  $d A x z $.  $d A y z $.
    $( Change the bound variable in the statement stating that ` R ` is
       set-like. $)
    cbvsetlike $p |- ( A. x e. A Pred ( R , A , x ) e. _V <->
                        A. y e. A Pred ( R , A , y ) e. _V ) $=
      ( vz cv cpred cvv wcel wral weq predeq3 eleq1d cbvralv bitr4i ) CDAFZGZHI
      ZACJCDEFZGZHIZECJCDBFZGZHIZBCJRUAAECAEKQTHCDPSLMNUDUABECBEKUCTHCDUBSLMNO
      $.
      $( [2-Feb-2011] $)
  $}

  ${
    $d x y R $.  $d x A $.
    $( Alternate definition of founded relation. $)
    dffr4 $p |- ( R Fr A <->
                   A. x ( ( x C_ A /\ x =/= (/) )
                          -> E. y e. x Pred ( R , x , y ) = (/) ) ) $=
      ( wfr cv wss c0 wne wa ccnv csn cima cin wceq wrex wi wal cpred dffr3
      df-pred eqeq1i rexbii imbi2i albii bitr4i ) CDEAFZCGUGHIJZUGDKBFZLMNZHOZB
      UGPZQZARUHUGDUISZHOZBUGPZQZARABCDTUQUMAUPULUHUOUKBUGUNUJHUGDUIUAUBUCUDUEU
      F $.
      $( [2-Feb-2011] $)
  $}

  ${
    $( Membership in the predecessor class implies membership in the base
       class. $)
    predel $p |- ( Y e. Pred ( R , A , X ) -> Y e. A ) $=
      ( cpred wcel ccnv csn cima cin df-pred eleq2i elin pm3.26bi sylbi ) DABCE
      ZFDABGCHIZJZFZDAFZPRDABCKLSTDQFDAQMNO $.
      $( [11-Feb-2011] $)
  $}

  ${
    $d R z $.  $d A z $.  $d X z $.  $d Y z $.
    $( Property of the predecessor class for strict orderings. $)
    predso $p |- ( ( R Or A /\ X e. A ) ->
                    ( Y e. Pred ( R , A , X ) ->
                      Pred ( R , A , Y ) C_ Pred ( R , A , X ) ) ) $=
      ( vz wor wcel wa cpred wss predel w3a cv wi wal wbr wb elpredg adantll
      sotr 3exp2 com24 imp31 com13 ex com14 sylbid com23 3imp imdistand visset
      elpred 3ad2ant3 adantl 3ad2ant1 3imtr4d 19.21aiv dfss2 sylibr 3exp mpdi
      ) ABFZCAGZHZDABCIZGZDAGZABDIZVEJZABCDKVDVFVGVIVDVFVGLZEMZVHGZVKVEGZNZEOVI
      VJVNEVJVKAGZVKDBPZHZVOVKCBPZHZVLVMVJVOVPVRVDVFVGVOVPVRNNZVDVGVFVTVDVGVFVT
      NVDVGHZVFDCBPZVTVCVGVFWBQVBAABCDRSVPWBVOWAVRVPWBVOWAVRNNWAVOVPWBHZVRVBVCV
      GVOWCVRNZNVBVOVGVCWDVBVOVGVCWDAVKDCBTUAUBUCUDUEUFUGUEUHUIUJVGVDVLVQQVFAAB
      DVKEUKZULUMVDVFVMVSQZVGVCWFVBAABCVKWEULUNUOUPUQEVHVEURUSUTVA $.
      $( [11-Feb-2011] $)
  $}

  ${
    predbr.1 $e |- X e. _V $.
    predbr.2 $e |- Y e. _V $.
    $( If a set is in the predecessor class, then it is less than the base
       element. $)
    predbr $p |- ( Y e. Pred ( R , A , X ) -> Y R X ) $=
      ( cpred wcel wbr wa cvv wb elpred ax-mp biimpi pm3.27d ) DABCGHZDAHZDCBIZ
      QRSJZCKHQTLEAKBCDFMNOP $.
      $( [11-Feb-2011] $)
  $}

  ${
    $d A x y $.  $d R x y $.  $d X x y $.  $d Y y $.
    $( Closed form of ~ predbr . $)
    predbrg $p |- ( ( X e. A /\ Y e. B ) ->
                     ( Y e. Pred ( R , A , X ) -> Y R X ) ) $=
      ( vy vx cv cpred wcel wbr wi wceq predeq3 eleq2d breq2 imbi12d eleq1
      breq1 visset predbr vtocl2g ) FHZACGHZIZJZUCUDCKZLUCACDIZJZUCDCKZLEUHJZED
      CKZLGFDEABUDDMZUFUIUGUJUMUEUHUCACUDDNOUDDUCCPQUCEMUIUKUJULUCEUHRUCEDCSQAC
      UDUCGTFTUAUB $.
      $( [13-Apr-2011] $)
  $}

  ${
    $d R x $.  $d A x $.  $d X x $.
    $( If ` R ` is set-like in ` A ` then all predecessors classes of elements
       of ` A ` exist. $)
    setlikespec $p |- ( ( X e. A /\ A. x e. A Pred ( R , A , x ) e. _V )
                         -> Pred ( R , A , X ) e. _V ) $=
      ( cv cpred cvv wcel wceq predeq3 eleq1d rcla4va ) BCAEZFZGHBCDFZGHADBMDIN
      OGBCMDJKL $.
      $( [20-Feb-2011] $)
  $}

  $( Idempotent law for the predecessor class. $)
  predidm $p |- Pred ( R , Pred ( R , A , X ) , X ) = Pred ( R , A , X ) $=
    ( cpred ccnv csn cima cin df-pred ineq1i inidm ineq2i inass 3eqtr4ri
    3eqtr4i ) ABCDZBECFGZHAQHZQHZPBCDPPRQABCIZJPBCIAQQHZHRSPUAQAQKLAQQMTNO $.
    $( [29-Mar-2011] $)

  $( Intersection law for predecessor classes. $)
  predin $p |- Pred ( R , ( A i^i B ) , X ) =
               ( Pred ( R , A , X ) i^i Pred ( R , B , X ) ) $=
    ( cin ccnv csn cima cpred inindir df-pred ineq12i 3eqtr4i ) ABEZCFDGHZEAOEZ
    BOEZENCDIACDIZBCDIZEABOJNCDKRPSQACDKBCDKLM $.
    $( [29-Mar-2011] $)

  $( Union law for predecessor classes. $)
  predun $p |- Pred ( R , ( A u. B ) , X ) =
               ( Pred ( R , A , X ) u. Pred ( R , B , X ) ) $=
    ( cun ccnv csn cima cin cpred indir df-pred uneq12i 3eqtr4i ) ABEZCFDGHZIAP
    IZBPIZEOCDJACDJZBCDJZEABPKOCDLSQTRACDLBCDLMN $.
    $( [29-Mar-2011] $)

  $( Difference law for predecessor classes. $)
  preddif $p |- Pred ( R , ( A \ B ) , X ) =
                  ( Pred ( R , A , X ) \ Pred ( R , B , X ) ) $=
    ( cdif ccnv csn cima cin cpred indifdi df-pred difeq12i 3eqtr4i ) ABEZCFDGH
    ZIAPIZBPIZEOCDJACDJZBCDJZEABPKOCDLSQTRACDLBCDLMN $.
    $( [14-Apr-2011] $)

  ${
    $d X y $.  $d B y $.
    $( The predecessor under the epsilon relationship is equivalent to an
       intersection.  (The proof was shortened by Andrew Salmon,
       27-Aug-2011.) $)
    predep $p |- ( X e. B -> Pred ( _E , A , X ) = ( A i^i X ) ) $=
      ( vy wcel cep ccnv csn cima cin cpred cv wbr cab cvv wb visset wa brcnvg
      ancoms epelg bitrd mpan abbi1dv wrel wceq relcnv relimasn ax-mp syl5eq
      ineq2d df-pred ) CBEZAFGZCHIZJACJAFCKUMUOCAUMCDLZUNMZDNZCUOUMUQDCUPOEZUMU
      QUPCEZPDQUSUMRUQUPCFMZUTUMUSUQVAPCUPBOFSTUPCOBUAUBUCUDUNUEUOURUFFUGDCUNUH
      UIUJUKAFCULUJ $.
      $( [27-Aug-2011] $) $( [27-Mar-2011] $)
  $}

  $( For an ordinal, the predecessor under ` _E ` and ` On ` is an identity
     relationship. $)
  predon $p |- ( A e. On -> Pred ( _E , On , A ) = A ) $=
    ( con0 wcel cep cpred cin predep wss wceq onss sseqin2 sylib eqtrd ) ABCZBD
    AEBAFZABBAGNABHOAIAJABKLM $.
    $( [27-Mar-2011] $)

  $( The epsilon relationship is set-like. $)
  epsetlike $p |- A. x e. A Pred ( _E , A , x ) e. _V $=
    ( cep cv cpred cvv wcel cin predep incom syl6eq inex1g eqeltrd rgen ) BCADZ
    EZFGABOBGZPOBHZFQPBOHRBBOIBOJKOBBLMN $.
    $( [27-Mar-2011] $)

  ${
    $d A x $.  $d B x $.
    $( If ` R ` is set-like over ` A ` , then it is set-like over any subclass
       of ` A ` . $)
    setlikess $p |- ( ( A C_ B /\ A. x e. B Pred ( R , B , x ) e. _V ) ->
                       A. x e. A Pred ( R , A , x ) e. _V ) $=
      ( wss cv cpred cvv wcel wral ssralv wi predpredss ssexg ex syl ralimdv
      syld imp ) BCEZCDAFZGZHIZACJZBDUAGZHIZABJZTUDUCABJUGUCABCKTUCUFABTUEUBEZU
      CUFLBCDUAMUHUCUFUEUBHNOPQRS $.
      $( [28-Mar-2011] $)
  $}

  ${
    $d A x y z $.  $d B x y z $.  $d R x y z $.  $d X y $.
    $( A property of classes that are downward closed under predecessor. $)
    preddowncl $p |- ( ( B C_ A /\ A. x e. B Pred ( R , A , x ) C_ B ) ->
                        ( X e. B ->
                          Pred ( R , B , X ) = Pred ( R , A , X ) ) ) $=
      ( vy vz wss cv cpred wral wa wcel wceq wi eleq1 predeq3 eqeq12d imbi12d
      imbi2d predpredss ad2antrr wbr weq sseq1d rcla4cv imp sseld visset
      predbr a1i jcad wb elpred adantl mpbird ssrdv adantll eqssd ex vtoclg
      pm2.43b ) CBHZBDAIZJZCHZACKZLZECMZCDEJZBDEJZNZVHFIZCMZCDVMJZBDVMJZNZOZOVH
      VIVLOZOFECVMENZVRVSVHVTVNVIVQVLVMECPVTVOVJVPVKCDVMEQBDVMEQRSTVHVNVQVHVNLV
      OVPVCVOVPHVGVNCBDVMUAUBVGVNVPVOHVCVGVNLZGVPVOWAGIZVPMZWBVOMZOZWCWBCMZWBVM
      DUCZLZOZWAWCWFWGWAVPCWBVGVNVPCHZVFWJAVMCAFUDVEVPCBDVDVMQUEUFUGUHWCWGOWABD
      VMWBFUIGUIZUJUKULVNWEWIUMVGVNWDWHWCCCDVMWBWKUNTUOUPUQURUSUTVAVB $.
      $( [13-Apr-2011] $)
  $}

  $( Given a partial ordering, ` X ` is not a member of its predecessor
     class. $)
  predpoirr $p |- ( R Po A -> -. X e. Pred ( R , A , X ) ) $=
    ( wpo wcel cpred wn wbr wa wb elpredg anidms notbid poirr syl5bir exp3a
    pm2.43b predel con3i pm2.61d1 ) ABDZCAEZCABCFEZGZUAUBUDUBUAUBUDUBUDCCBHZGUA
    UBIUBUCUEUBUCUEJAABCCKLMACBNOPQUCUBABCCRST $.
    $( [17-Apr-2011] $)

  $( Given a founded relationship, ` X ` is not a member of its predecessor
     class. $)
  predfrirr $p |- ( R Fr A -> -. X e. Pred ( R , A , X ) ) $=
    ( wfr wcel cpred wn wbr wa wb elpredg anidms notbid frirrc syl5bir exp3a
    pm2.43b predel con3i pm2.61d1 ) ABDZCAEZCABCFEZGZUAUBUDUBUAUBUDUBUDCCBHZGUA
    UBIUBUCUEUBUCUEJAABCCKLMABCNOPQUCUBABCCRST $.
    $( [22-Apr-2011] $)


  $( The predecessor class over ` (/) ` is always ` (/) ` $)
  pred0 $p |- Pred ( R , (/) , X ) = (/) $=
    ( c0 cpred ccnv csn cima cin df-pred incom in0 3eqtri ) CABDCAEBFGZHMCHCCAB
    ICMJMKL $.
    $( [16-Apr-2011] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              (Trans)finite Recursion Theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d z D $.  $d y z C $.  $d z A $.  $d z B $.  $d x y z $.
    frsucopabn.1 $e |- ( z e. A -> A. x z e. A ) $.
    frsucopabn.2 $e |- ( z e. B -> A. x z e. B ) $.
    frsucopabn.3 $e |- ( z e. D -> A. x z e. D ) $.
    frsucopabn.4 $e |- F = ( rec ( { <. x , y >. | y = C } , A ) |` om ) $.
    frsucopabn.5 $e |- ( x = ( F ` B ) -> C = D ) $.
    $( The value of the finite recursive definition generator at a successor
       (special case where the characteristic function is an ordered-pair class
       abstraction and where the mapping class ` D ` is a proper class).  This
       is a technical lemma that can be used together with ~ frsucopab to help
       eliminate redundant sethood antecedents. $)
    frsucopabn $p |- ( -. D e. _V -> ( F ` suc B ) = (/) ) $=
      ( com wcel cvv wn csuc cfv c0 wceq cv copab crdg cres frsuc fveq1i
      syl5eq hbopab1 hbrdg ax-17 hbres hbfv eqeq2i sylbir fvopabnf sylan9eq
      cdm peano2b dmeqi wfn frfnom fndm ax-mp eqtri eleq2i bitr4i notbii ndmfv
      sylbi adantr pm2.61ian ) ENOZGPOQZERZHSZTUAZVMVNVPEBUBFUAZABUCZDUDZNUEZSZ
      VSSZTVMVOWASWCVPDEVSUFVOHWALUGUHABCWBFGACEWAACVTNACDVSVRABCUIIUJCUBNOAUKU
      LJUMKAUBZWBUAWDEHSZUAFGUAWEWBWDEHWALUGUNMUOUPUQVMQZVQVNWFVOHURZOZQVQVMWHV
      MVONOWHEUSWGNVOWGWAURZNHWALUTWANVAWINUADVSVBNWAVCVDVEVFVGVHVOHVIVJVKVL $.
      $( [19-Feb-2011] $)
  $}

  ${
    $d ph y z $.  $d x y z $.
    $( A closed form of ~ tfis . $)
    tfisg $p |- ( A. x e. On ( A. y e. x [ y / x ] ph -> ph ) ->
                 A. x e. On ph ) $=
      ( vz wsb cv wral wi con0 crab wceq wss wcel tfi ssrab2 wa wel ax-17 hbs1
      hbral hbim weq raleq sbequ12 imbi12d rcla4 impcom dfss3 elrabsf pm3.27bi
      ralimi sylbi syl5 pm3.27 jctild syl6ibr r19.21aiva sylancr eqcomd rabid2
      sylib ) ABCEZCBFZGZAHZBIGZIABIJZKABIGVFVGIVGILDFZVGLZVHVGMZHZDIGVGIKVFDVG
      NABIOVFVKDIVFVHIMZPZVIVLABDEZPVJVMVIVNVLVMVBCVHGZVNVIVLVFVOVNHZVEVPBVHIVO
      VNBVBBCVHCDQBRABCSTABDSUABDUBVDVOAVNVBCVCVHUCABDUDUEUFUGVICFZVGMZCVHGVOCV
      HVGUHVRVBCVHVRVQIMVBABDVQIVLBRZUIUJUKULUMVFVLUNUOABDVHIVSUIUPUQURUSABIUTV
      A $.
      $( [8-Jun-2011] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Well-founded induction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x z w t u v $.  $d A y $.  $d B x z w t u v $.  $d B y $.
    $d R x z w t u v $.  $d R y $.  $d y z w t u v $.
    $( All nonempty (possibly proper) subclasses of ` A ` , which has a
       well-founded relation ` R ` , have ` R `-minimal elements.  Proposition
       6.26 of [TakeutiZaring] p. 31. $)
    tz6.26 $p |- ( ( ( R We A /\
                        A. x e. A Pred ( R , A , x ) e. _V ) /\
                      ( B C_ A /\ B =/= (/) ) ) ->
                    E. y e. B Pred ( R , B , y ) = (/) ) $=
      ( vt vz vw wwe cv cpred cvv wcel wral wa wss c0 wne wceq wrex wi wess
      ssralv predpredss ssexg ex syl ralimdv syld cbvsetlike syl5ib anim12d
      wex weq predeq3 eqeq1d rcla4ev adantl predss wfr wefr eleq1d rcla4cva
      anim12i anassrs sseq1 neeq1 anbi12d predeq2 rexeqbi1dv imbi12d imbi2d
      wal dffr4 ax-4 sylbi vtoclg impcom mpani wor wbr w3a sotr 3exp2 com23
      com34 3imp exp3a 3exp imp43 wb elpredg adantll adantlr 3adant2 mpbird
      imdistand visset elpred ax-mp ancom bitri 3imtr4g ssrdv sseq0 weso
      anim1i biimpi syl2an reximdva ssrexv syl6 pm2.61dne 19.23adv n0 syl6com
      imp32 ) CEIZCEAJKLMACNZOZDCPZDQRZDEBJZKZQSZBDTZYAXTDEIZDEFJZKZLMZFDNZOZYB
      YFUAYAXRYGXSYKDCEUBYACEYHKZLMZFCNZYKXSYAYOYNFDNYKYNFDCUCYAYNYJFDYAYIYMPZY
      NYJUADCEYHUDYPYNYJYIYMLUEUFUGUHUIAFCEUJUKULYLGJZDMZGUMYFYBYLYRYFGYLYRYFYL
      YROZYFDEYQKZQYRYTQSZYFUAYLYRUUAYFYEUUABYQDBGUNYDYTQDEYCYQUOUPUQUFURYSYTQR
      ZYEBYTTZYFYSUUBYTEYCKZQSZBYTTZUUCYSYTDPZUUBUUFDEYQUSZYSDEUTZYTLMZOZUUGUUB
      OZUUFUAZYGYKYRUUKYGUUIYKYROUUJDEVAYJUUJFYQDFGUNYIYTLDEYHYQUOVBVCVDVEUUJUU
      IUUMUUIHJZDPZUUNQRZOZUUNEYCKZQSZBUUNTZUAZUAUUIUUMUAHYTLUUNYTSZUVAUUMUUIUV
      BUUQUULUUTUUFUVBUUOUUGUUPUUBUUNYTDVFUUNYTQVGVHUUSUUEBUUNYTUVBUURUUDQUUNYT
      EYCVIUPVJVKVLUUIUVAHVMUVAHBDEVNUVAHVOVPVQVRUGVSYGYRUUFUUCUAYKYGYROZUUEYEB
      YTDEVTZYROZYCDMZYCYQEWAZOZUUEYEUAZUVCYCYTMZUVEUVHOZYDUUDPZUVIUVKHYDUUDUVK
      UUNYCEWAZUUNDMZOZUVMUUNYTMZOZUUNYDMZUUNUUDMZUVKUVMUVNUVPUVKUVMUVNUVPUVKUV
      MUVNWBUVPUUNYQEWAZUVKUVMUVNUVTUVDYRUVFUVGUVMUVNUVTUAZUAZUVDUVFYRUVGUWBUAZ
      UVDUVFYRUWCUVDUVFYRWBZUVMUVGUWAUWDUVMUVGUWAUWDUVNUVMUVGOZUVTUVDUVFYRUVNUW
      EUVTUAZUAUVDUVFUVNYRUWFUVDUVNUVFYRUWFUAUVDUVNUVFYRUWFDUUNYCYQEWCWDWEWFWGW
      EWHWEWIWEWJWGUVKUVNUVPUVTWKZUVMUVEUVNUWGUVHYRUVNUWGUVDDDEYQUUNWLWMWNWOWPW
      IWQUVRUVNUVMOZUVOYCLMZUVRUWHWKBWRZDLEYCUUNHWRZWSWTUVNUVMXAXBUVSUVPUVMOZUV
      QUWIUVSUWLWKUWJYTLEYCUUNUWKWSWTUVPUVMXAXBXCXDUVLUUEYEYDUUDXEUFUGYGUVDYRDE
      XFXGUVJUVHYQLMUVJUVHWKGWRDLEYQYCUWJWSWTXHXIXJWNUIUUGUUCYFUAUUHYEBYTDXKWTX
      LXMUFXNGDXOUKXPXQ $.
      $( [29-Jan-2011] $)
  $}

  ${
    $d A x $.  $d A y $.  $d B x $.  $d B y $.  $d R x $.  $d R y $.
    tz6.26i.1 $e |- R We A $.
    tz6.26i.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    $( All nonempty (possibly proper) subclasses of ` A ` , which has a
       well-founded relation ` R ` , have ` R `-minimal elements.  Proposition
       6.26 of [TakeutiZaring] p. 31. $)
    tz6.26i $p |- ( ( B C_ A /\ B =/= (/) ) ->
                    E. y e. B Pred ( R , B , y ) = (/) ) $=
      ( wwe cv cpred cvv wcel wral wss c0 wne wa wceq wrex tz6.26 mpanl12 ) CEH
      CEAIJKLACMDCNDOPQDEBIJORBDSFGABCDETUA $.
      $( [14-Apr-2011] $)
  $}


  ${
    $d A x $.  $d A y $.  $d B x $.  $d B y $.  $d R x $.  $d R y $.
    $( The Principle of Well-Founded Induction.  Theorem 6.27 of
       [TakeutiZaring] p. 32.  This principle states that if ` B ` is a
       subclass of a well-ordered class ` A ` with the property that every
       element of ` B ` whose inital segment is included in ` A ` is itself
       equal to ` A ` . $)
    wfi $p |- ( ( ( R We A /\ A. x e. A Pred ( R , A , x ) e. _V ) /\
                    ( B C_ A /\
                      A. y e. A ( Pred ( R , A , y ) C_ B -> y e. B ) ) )
                  -> A = B ) $=
      ( wwe cv cpred cvv wcel wral wa wss wi cdif c0 wne wn difss wceq wrex
      tz6.26 eldif anbi1i anass ancom ccnv csn cima cin indif2 df-pred incom
      eqtri difeq1i 3eqtr4i eqeq1i ssdif0 bitr4i bitri anbi2i 3bitri rexbii2
      rexanali sylib ex mpani necon3bbii syl5ib con4d imp adantrl simprl eqssd
      ) CEFCEAGHIJACKLZDCMZCEBGZHZDMZVQDJZNBCKZLLCDVOWACDMZVPVOWAWBVOWBWAVOCDOZ
      PQZWARZWBRVOWCCMZWDWECDSVOWFWDLZWEVOWGLWCEVQHZPTZBWCUAZWEABCWCEUBWJVSVTRZ
      LZBCUAWEWIWLBWCCVQWCJZWILVQCJZWKLZWILWNWKWILZLWNWLLWMWOWIVQCDUCUDWNWKWIUE
      WPWLWNWPWIWKLWLWKWIUFWIVSWKWIVRDOZPTVSWHWQPEUGVQUHUIZWCUJZWRCUJZDOWHWQWRC
      DUKWHWCWRUJWSWCEVQULWCWRUMUNVRWTDVRCWRUJWTCEVQULCWRUMUNUOUPUQVRDURUSUDUTV
      AVBVCVSVTBCVDUTVEVFVGWBWCPCDURVHVIVJVKVLVOVPWAVMVN $.
      $( [29-Jan-2011] $)
  $}

  ${
    $d A x $.  $d A y $.  $d B x $.  $d B y $.  $d R x $.  $d R y $.
    wfi.1 $e |- R We A $.
    wfi.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    $( The Principle of Well-Founded Induction.  Theorem 6.27 of
       [TakeutiZaring] p. 32.  This principle states that if ` B ` is a
       subclass of a well-ordered class ` A ` with the property that every
       element of ` B ` whose inital segment is included in ` A ` is itself
       equal to ` A ` . $)
    wfii $p |- ( ( B C_ A /\
                    A. y e. A ( Pred ( R , A , y ) C_ B -> y e. B ) )
                  -> A = B ) $=
      ( wwe cv cpred cvv wcel wral wa wss wi wceq pm3.2i wfi mpan ) CEHZCEAIJKL
      ACMZNDCOCEBIZJDOUCDLPBCMNCDQUAUBFGRABCDEST $.
      $( [29-Jan-2011] $)
  $}


  ${
    $d A w x y $.  $d A z $.  $d ph w x $.  $d ph z $.  $d R w x y $.
    $d R z $.  $d w y z $.
    wfisg.1 $e |- ( y e. A ->
                       ( A. z e. Pred ( R , A , y ) [ z / y ] ph -> ph ) ) $.
    $( Well-Founded Induction Schema.  If a property passes from all elements
       less than ` y ` of a well founded class ` A ` to ` y ` itself (induction
       hypothesis), then the property holds for all elements of ` A ` . $)
    wfisg $p |- ( ( R We A /\ A. x e. A Pred ( R , A , x ) e. _V )
                     -> A. y e. A ph ) $=
      ( vw wwe cv cpred cvv wcel wral wa crab wceq wss wi ssrab2 wsbc ax-17
      hbs1 hbral hbim eleq1 predeq3 raleqdv sbequ12 imbi12d chvar dfss3
      elrabsf pm3.27bi ralimi sylbi syl5 anc2li syl6ibr rgen wfi mpanr12
      rabid2 sylib ) EFIEFBJKLMBENOZEACEPZQZACENVEVFEREFHJZKZVFRZVHVFMZSZHENVGA
      CETVLHEVHEMZVJVMACVHUAZOVKVMVJVNVMACDJZUAZDVINZVNVJCJZEMZVPDEFVRKZNZASZSV
      MVQVNSZSCHVMWCCVMCUBZVQVNCVPCDVIVOVIMCUBACDUCUDACHUCUEUEVRVHQZVSVMWBWCVRV
      HEUFWEWAVQAVNWEVPDVTVIEFVRVHUGUHACHUIUJUJGUKVJVOVFMZDVINVQDVIVFULWFVPDVIW
      FVOEMVPACHVOEWDUMUNUOUPUQURACHVHEWDUMUSUTBHEVFFVAVBACEVCVD $.
      $( [11-Feb-2011] $)
  $}


  ${
    $d A w y z $.  $d A x $.  $d ph w z $.  $d ph x $.  $d R w y z $.
    $d R x $.  $d x y $.
    wfis.1 $e |- R We A $.
    wfis.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    wfis.3 $e |- ( y e. A ->
                    ( A. z e. Pred ( R , A , y ) [ z / y ] ph -> ph ) ) $.
    $( Well-Founded Induction Schema.  If all elements less than a given set
       ` x ` of the well founded class ` A ` have a property (induction
       hypothesis), then all elements of ` A ` have that property. $)
    wfis $p |- ( y e. A -> ph ) $=
      ( wwe cv cpred cvv wcel wral wfisg mp2an rspec ) ACEEFJEFBKLMNBEOACEOGHAB
      CDEFIPQR $.
      $( [29-Jan-2011] $)
  $}

  ${
    $d A x y $.  $d A z $.  $d ph x $.  $d ph z $.  $d R x y $.  $d R z $.
    $d y z $.
    wfis2fg.1 $e |- ( ps -> A. y ps ) $.
    wfis2fg.2 $e |- ( y = z -> ( ph <-> ps ) ) $.
    wfis2fg.3 $e |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.
    $( Well-Founded Induction Schema, using implicit substitution. $)
    wfis2fg $p |- ( ( R We A /\ A. x e. A Pred ( R , A , x ) e. _V )
                     -> A. y e. A ph ) $=
      ( cv wcel cpred wral wsbc sbie ralbii syl5ib wfisg ) ACDEFGDKZFLBEFGTMZNA
      ADEKOZEUANJUBBEUAABDEHIPQRS $.
      $( [11-Feb-2011] $)
  $}

  ${
    $d A x y $.  $d A z $.  $d ph x $.  $d ph z $.  $d R x y $.  $d R z $.
    $d y z $.
    wfis2f.1 $e |- R We A $.
    wfis2f.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    wfis2f.3 $e |- ( ps -> A. y ps ) $.
    wfis2f.4 $e |- ( y = z -> ( ph <-> ps ) ) $.
    wfis2f.5 $e |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.
    $( Well Founded Induction schema, using implicit substitution. $)
    wfis2f $p |- ( y e. A -> ph ) $=
      ( wwe cv cpred cvv wcel wral wfis2fg mp2an rspec ) ADFFGMFGCNOPQCFRADFRHI
      ABCDEFGJKLSTUA $.
      $( [29-Jan-2011] $)
  $}

  ${
    $d A x y $.  $d A z $.  $d ph x $.  $d ph z $.  $d ps y $.  $d R x y $.
    $d R z $.  $d y z $.
    wfis2g.1 $e |- ( y = z -> ( ph <-> ps ) ) $.
    wfis2g.2 $e |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.
    $( Well-Founded Induction Schema, using implicit substitution. $)
    wfis2g $p |- ( ( R We A /\ A. x e. A Pred ( R , A , x ) e. _V )
                     -> A. y e. A ph ) $=
      ( ax-17 wfis2fg ) ABCDEFGBDJHIK $.
      $( [11-Feb-2011] $)
  $}

  ${
    $d A x y $.  $d A z $.  $d ph x $.  $d ph z $.  $d ps y $.  $d R x y $.
    $d R z $.  $d y z $.
    wfis2.1 $e |- R We A $.
    wfis2.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    wfis2.3 $e |- ( y = z -> ( ph <-> ps ) ) $.
    wfis2.4 $e |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.
    $( Well Founded Induction schema, using implicit substitution. $)
    wfis2 $p |- ( y e. A -> ph ) $=
      ( wwe cv cpred cvv wcel wral wfis2g mp2an rspec ) ADFFGLFGCMNOPCFQADFQHIA
      BCDEFGJKRST $.
      $( [29-Jan-2011] $)
  $}

  ${
    $d A x y $.  $d A z $.  $d B y $.  $d ch y $.  $d ph x $.  $d ph z $.
    $d ps y $.  $d R x y $.  $d R z $.  $d y z $.
    wfis3.1 $e |- R We A $.
    wfis3.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    wfis3.3 $e |- ( y = z -> ( ph <-> ps ) ) $.
    wfis3.4 $e |- ( y = B -> ( ph <-> ch ) ) $.
    wfis3.5 $e |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.


    $( Well Founded Induction schema, using implicit substitution. $)
    wfis3 $p |- ( B e. A -> ch ) $=
      ( wfis2 vtoclga ) ACEHGMABDEFGIJKLNOP $.
      $( [29-Jan-2011] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Transitive closure under a relationship
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Trcl $.
  $( Define the transitive closure class as a class. $)
  ctrcl $a class Trcl ( R , A , X ) $.

  ${
    $d R a b y $.  $d A a b y $.  $d X a b y $.
    $( Define the transitive closure of a class ` X ` under a relationship and
       a class.  This class can be thought of as the "smallest" class
       containing all elements of ` A ` that are linked to ` X ` by a chain of
       ` R ` relationships.  Definition based off of Lemma 4.2 of Don Monk's
       notes for Advanced Set Theory, which can be found at
       ~ http://euclid.colorado.edu/~~monkd/settheory . $)
    df-trcl $a |- Trcl ( R , A , X ) =
                        U. ran ( rec ( { <. a , b >. |
                                 b = U_ y e. a Pred ( R , A , y ) } ,
                                 Pred ( R , A , X ) ) |` om ) $.
  $}

  ${
    $d R a b y $.  $d S a b y $.  $d A a b y $.  $d B a b y $.  $d X a b y $.
    $d Y a b y $.

    $( Equality theorem for transitive closure. $)
    trcleq1 $p |- ( R = S -> Trcl ( R , A , X ) = Trcl ( S , A , X ) ) $=
      ( vb vy va wceq cv cpred ciun copab crdg com cres crn cuni ctrcl wel
      predeq1 adantr iuneq2dv eqeq2d opabbidv rdgeq1 syl rdgeq2 eqtrd reseq1
      rneqd unieqd df-trcl 3eqtr4g ) BCHZEIZFGIZABFIZJZKZHZGELZABDJZMZNOZPZQUOF
      UPACUQJZKZHZGELZACDJZMZNOZPZQABDRACDRUNVEVMUNVDVLUNVCVKHVDVLHUNVCVIVBMZVK
      UNVAVIHVCVNHUNUTVHGEUNUSVGUOUNFUPURVFUNURVFHFGSABCUQTUAUBUCUDVBVAVIUEUFUN
      VBVJHVNVKHABCDTVBVJVIUGUFUHVCVKNUIUFUJUKFABDGEULFACDGEULUM $.
      $( [2-Feb-2011] $)

    $( Equality theorem for the transitive closure. $)
    trcleq2 $p |- ( A = B -> Trcl ( R , A , X ) = Trcl ( R , B , X ) ) $=
      ( vb vy va wceq cv cpred ciun copab crdg com cres crn cuni ctrcl wel
      predeq2 adantr iuneq2dv eqeq2d opabbidv rdgeq1 syl rdgeq2 eqtrd reseq1
      rneqd unieqd df-trcl 3eqtr4g ) ABHZEIZFGIZACFIZJZKZHZGELZACDJZMZNOZPZQUOF
      UPBCUQJZKZHZGELZBCDJZMZNOZPZQACDRBCDRUNVEVMUNVDVLUNVCVKHVDVLHUNVCVIVBMZVK
      UNVAVIHVCVNHUNUTVHGEUNUSVGUOUNFUPURVFUNURVFHFGSABCUQTUAUBUCUDVBVAVIUEUFUN
      VBVJHVNVKHABCDTVBVJVIUGUFUHVCVKNUIUFUJUKFACDGEULFBCDGEULUM $.
      $( [2-Feb-2011] $)

    $( Equality theorem for the transitive closure. $)
    trcleq3 $p |- ( X = Y -> Trcl ( R , A , X ) = Trcl ( R , A , Y ) ) $=
      ( vb vy va wceq cv cpred ciun copab crdg com cres crn cuni ctrcl predeq3
      rdgeq2 reseq1 3syl rneqd unieqd df-trcl 3eqtr4g ) CDHZEIFGIABFIJKHGELZABC
      JZMZNOZPZQUHABDJZMZNOZPZQABCRABDRUGULUPUGUKUOUGUIUMHUJUNHUKUOHABCDSUIUMUH
      TUJUNNUAUBUCUDFABCGEUEFABDGEUEUF $.
      $( [2-Feb-2011] $)
  $}

  ${
    trcleq1d.1 $e |- ( ph -> R = S ) $.
    $( Equality deduction for the transitive closure. $)
    trcleq1d $p |- ( ph -> Trcl ( R , A , X ) = Trcl ( S , A , X ) ) $=
      ( wceq ctrcl trcleq1 syl ) ACDGBCEHBDEHGFBCDEIJ $.
      $( [2-Feb-2011] $)
  $}

  ${
    trcleq2d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for the transitive closure. $)
    trcleq2d $p |- ( ph -> Trcl ( R , A , X ) = Trcl ( R , B , X ) ) $=
      ( wceq ctrcl trcleq2 syl ) ABCGBDEHCDEHGFBCDEIJ $.
      $( [2-Feb-2011] $)
  $}

  ${
    trcleq3d.1 $e |- ( ph -> X = Y ) $.
    $( Equality deduction for the transitive closure. $)
    trcleq3d $p |- ( ph -> Trcl ( R , A , X ) = Trcl ( R , A , Y ) ) $=
      ( wceq ctrcl trcleq3 syl ) ADEGBCDHBCEHGFBCDEIJ $.
      $( [2-Feb-2011] $)
  $}

  ${
    $d R a b y i $.  $d A a b y i $.  $d X a b y i $.  $d Y a b y i $.
    $( Technzical lemma for the properties of the transitive closure.  A set is
       an element of the transitive closure iff it is in some value of the
       underlying function. $)
    eltrcl $p |- ( Y e. Trcl ( R , A , X ) <->
                    E. i e. om Y e. ( ( rec ( { <. a , b >. |
                                        b = U_ y e. a Pred ( R , A , y ) } ,
                                        Pred ( R , A , X ) ) |` om ) ` i ) ) $=
      ( ctrcl wcel cv cpred ciun wceq copab crdg com cres crn cuni cfv cdm
      wrex df-trcl eleq2i wfun wb wfn frfnom fnfun ax-mp elunirn fndm rexeq
      3bitri ) FBCEIZJFHKAGKBCAKLMNGHOZBCELZPQRZSTZJZFDKUSUAJZDUSUBZUCZVBDQUCZU
      PUTFABCEGHUDUEUSUFZVAVDUGUSQUHZVFURUQUIZQUSUJUKDFUSULUKVCQNZVDVEUGVGVIVHQ
      USUMUKVBDVCQUNUKUO $.
      $( [18-Feb-2011] $)
  $}

  ${
    $d A a b d e j $.  $d A a d e y $.  $d B j $.  $d i j $.  $d j y $.
    $d R a b d e j $.  $d R y $.  $d X a d e j $.
    $( Technical lemma for transitive closure properties.  All values of the
       transitive closure's underlying function are subsets of the base set. $)
    trcllem1 $p |- ( Pred ( R , A , X ) e. B ->
                      ( ( rec ( { <. a , b >. |
                                        b = U_ y e. a Pred ( R , A , y ) } ,
                                        Pred ( R , A , X ) ) |` om ) ` i )
                       C_ A ) $=
      ( vj ve vd cv com wcel cpred ciun wceq copab crdg cres cfv wss wi c0
      csuc wrex wo nn0suc fveq2 sseq1d predss fr0g mpbiri syl5bir wa cvv iunss
      a1i mprgbir ax-17 wel wal hbopab1 hbrdg hbres hbfv hbrex eliun albii
      3imtr4i predeq3 cbviunv eqeq2i opabbii rdgeq1 reseq1 syl ax-mp iuneq1
      frsucopab wn 0ss frsucopabn adantl pm2.61dan adantr wb mpbird a1d
      r19.23aiva jaoi nfvres pm2.61i ) ELZMNZBDFOZCNZWNHLZAGLZBDALZOZPZQZGHRZWP
      SZMTZUAZBUBZUCZWOWNUDQZWNILZUEZQZIMUFZUGXIIWNUHXJXIXNXJXHUDXFUAZBUBZWQXJX
      GXOBWNUDXFUIUJWQXPWPBUBBDFUKWQXOWPBWPCXDULUJUMUNXMXIIMXKMNZXMUOZXHWQXRXHX
      LXFUAZBUBZXQXTXMXQJXKXFUAZBDJLZOZPZUPNZXTXQYEUOZXTYDBUBZYGYCBUBZJYAJYAYCB
      UQYHYBYANBDYBUKURUSYFXSYDBGHKWPXKJWSYCPZYDUPXFKLZWPNGUTZKIVAGUTZYJYCNZJYA
      UFZYNGVBYJYDNZYOGVBYMGJYAGJXKXFGJXEMGJWPXDXCGHJVCYBWPNGUTVDYBMNGUTVEJIVAG
      UTVFYMGUTVGJYJYAYCVHZYOYNGYPVIVJZXDWRYIQZGHRZQZXFYSWPSZMTQZXCYRGHXBYIWRAJ
      WSXAYCBDWTYBVKVLVMVNYTXEUUAQUUBWPXDYSVOXEUUAMVPVQVRZJWSYAYCVSZVTUJUMXQYEW
      AZUOZXTUDBUBZBWBZUUFXSUDBUUEXSUDQXQGHKWPXKYIYDXFYKYLYQUUCUUDWCWDUJUMWEWFX
      MXHXTWGXQXMXGXSBWNXLXFUIUJWDWHWIWJWKVQWOWAZXHWQUUIXHUUGUUHUUIXGUDBWNMXEWL
      UJUMWIWM $.
      $( [18-Feb-2011] $)
  $}

  ${
    $d R a b y z $.  $d A a b y z $.  $d X a b y z $.
    $( Assuming it exists, the predecessor class is a subset of the transitive
       closure. $)
    trclpred $p |- ( Pred ( R , A , X ) e. B ->
                      Pred ( R , A , X ) C_ Trcl ( R , A , X ) ) $=
      ( vb vy va vz cpred wcel cv ciun wceq copab crdg com cres crn cuni ctrcl
      wss wbr wex c0 cfv fr0g wfun cdm wb wfn frfnom fnfun ax-mp peano1 fndm
      eleqtrri funbrfvbg mp3an12 mpbid 0ex breq1 cla4ev syl elrng mpbird
      elssuni df-trcl syl6ssr ) ACDIZBJZVIEKFGKACFKILMGENZVIOPQZRZSZACDTVJVIVMJ
      ZVIVNUAVJVOHKZVIVLUBZHUCZVJUDVIVLUBZVRVJUDVLUEVIMZVSVIBVKUFVLUGZUDVLUHZJV
      JVTVSUIVLPUJZWAVIVKUKZPVLULUMUDPWBUNWCWBPMWDPVLUOUMUPUDVIBVLUQURUSVQVSHUD
      UTVPUDVIVLVAVBVCHVIVLBVDVEVIVMVFVCFACDGEVGVH $.
      $( [18-Feb-2011] $)
  $}

  ${
    $d R a b i y z $.  $d A a b i y z $.  $d B i z $.  $d X a b i y z $.
    $( The transitive closure is a subset of the base class. $)
    trclss $p |- ( Pred ( R , A , X ) e. B ->
                    Trcl ( R , A , X ) C_ A ) $=
      ( vb vy va vi vz cpred wcel cv ciun wceq copab crdg com cres crn cuni
      ctrcl wbr wex wss wi wal cfv wfn wb frfnom visset fnbrfvb mpan biimprd
      sseq1 trcllem1 syl5cbi syl9r cdm breldm fndm ax-mp syl6eleq syl5 pm2.43d
      19.23adv 19.21aiv wral unissb df-ral elrn imbi1i albii 3bitri sylibr
      df-trcl syl5ss ) ACDJZBKZELFGLACFLJMNGEOZVRPQRZSZTZAACDUAVSHLZILZWAUBZHUC
      ZWEAUDZUEZIUFZWCAUDZVSWIIVSWFWHHVSWFWHVSWDQKZWFWHUEWFWLWFWDWAUGZWENZVSWHW
      LWNWFWAQUHZWLWNWFUIVRVTUJZQWDWEWAIUKZULUMUNWNWMAUDWHVSWMWEAUOFABCHDGEUPUQ
      URWFWDWAUSZQWDWEWAHUKUTWOWRQNWPQWAVAVBVCVDVEVFVGWKWHIWBVHWEWBKZWHUEZIUFWJ
      IWBAVIWHIWBVJWTWIIWSWGWHHWEWAWQVKVLVMVNVOFACDGEVPVQ $.
      $( [20-Feb-2011] $)
  $}

  ${
    $d R a b f g h t x y z $.  $d A a b f g h t x y z $.
    $d X a b f g h t x y z $.  $d Y a h $.
    $( The transitive closure is transitive in ` R ` and ` A ` $)
    trcltr $p |- ( ( X e. A /\ A. x e. A Pred ( R , A , x ) e. _V ) ->
                    ( Y e. Trcl ( R , A , X ) ->
                      Pred ( R , A , Y ) C_ Trcl ( R , A , X ) ) ) $=
      ( va vz vt vy vh vf vg vb wcel cv cpred cvv wral wa ciun wceq copab crdg
      com cres cfv cdm wrex crn cuni wss ctrcl wi csuc ssuni ax-17 ax17el weq
      pm3.27 iuneq1 predeq3 cbviunv syl6eq adantr eqeq12d cbvopabv rdgeq1
      ax-mp reseq1 frsucopab iunexg fvex setlikespec trcllem1 syl ssralv
      cbvsetlike syl5ib com12 adantl mpd sylancr sylan2 sseq2d ssiun2s syl5bir
      expcom imp32 wfn fnfvelrn frfnom peano2 ad2antrl sylanc exp32 fndm
      eleq2i r19.23adv df-trcl wfun wb fnfun elunirn bitri sseq2i 3imtr4g ) DBN
      ZBCAOPQNABRZSZEFOZGOZHIOZBCHOZPZTZUAZIGUBZBCDPZUCZUDUEZUFZNZFXTUGZUHZBCEP
      ZXTUIZUJZUKZEBCDULZNZYEYIUKXIYBYHFYCXIXJUDNZYBYHUMXJYCNXIYKYBYHYEXJUNZXTU
      FZUKZYMYFNZYHXIYKYBSSYEYMYFUOXIYKYBYNYKXIYBYNUMYKXISZYNYEJYABCJOZPZTZUKYB
      YPYMYSYEYKYSQNZYMYSUAXIKLMXRXJJKOZYRTZYSQXTMOZXRNKUPMFKUQUUCYSNKUPXSLOZUU
      BUAZKLUBZXRUCZUAZXTUUGUDUEUAXQUUFUAUUHXPUUEIGKLIKURZGLURZSXKUUDXOUUBUUIUU
      JUSUUIXOUUBUAUUJUUIXOHUUAXNTUUBHXLUUAXNUTHJUUAXNYRBCXMYQVAVBVCVDVEVFXRXQU
      UFVGVHXSUUGUDVIVHJUUAYAYRUTVJYAQNYRQNZJYARZYTXIJYAYRQQVKXJXTVLXIYABUKZUUL
      XIXRQNUUMABCDVMHBQCFDIGVNVOXHUUMUULUMXGUUMXHUULUUMUUKJBRUULXHUUKJYABVPAJB
      CVQVRVSVTWAWBWCWDJYAYREYEBCYQEVAWEWFWGWHYKYOXIYBXTUDWIZYLUDNYOYKUDYLXTWJX
      RXQWKZXJWLWBWMWNWOYCUDXJUUNYCUDUAUUOUDXTWPVHWQVRWRYJEYGNZYDYIYGEHBCDIGWSZ
      WQXTWTZUUPYDXAUUNUURUUOUDXTXBVHFEXTXCVHXDYIYGYEUUQXEXF $.
      $( [20-Feb-2011] $)
  $}

  ${
    $d R a b y $.  $d A a b y $.  $d X a b y $.
    $( The transitive closure of a relation exists (NOTE: this is the first
       theorem in the transitive closure series that requires infinity). $)
    trclex $p |- Trcl ( R , A , X ) e. _V $=
      ( vb vy va ctrcl cv cpred ciun wceq copab crdg com cres crn cuni cvv
      df-trcl wfn wcel frfnom omex fnex mp2an rnex uniex eqeltri ) ABCGDHEFHABE
      HIJKFDLZABCIZMNOZPZQREABCFDSULUKUKNTNRUAUKRUAUJUIUBUCNRUKUDUEUFUGUH $.
      $( [18-Feb-2011] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Founded Induction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A a b x $.  $d B a b c y $.  $d R a b c x $.  $d R y $.
    $( Every (possibly proper) subclass of a class ` A ` with a founded,
       set-like relation ` R ` has a minimal element.  Lemma 4.3 of Don Monk's
       notes for Advanced Set Theory, which can be found at
       ~ http://euclid.colorado.edu/~~monkd/settheory .  This is a very strong
       generalization of ~ tz6.26 and ~ tz7.5 . $)
    frmin $p |- ( ( ( R Fr A /\ A. x e. A Pred ( R , A , x ) e. _V ) /\
                     ( B C_ A /\ B =/= (/) ) ) ->
                   E. y e. B Pred ( R , B , y ) = (/) ) $=
      ( va vb vc wfr cv cpred cvv wcel wral wa wss c0 wne wceq wrex wi frss
      ssralv predpredss ssexg ex syl ralimdv syld cbvsetlike syl5ib anim12d
      wex weq predeq3 eqeq1d rcla4ev adantl ctrcl setlikespec trclpred ssn0
      trclss jctild adantr trclex sseq1 neeq1 anbi12d predeq2 rexeqbi1dv
      imbi12d imbi2d wal dffr4 ax-4 sylbi vtocl sspred trcltr imp sylanc
      biimprd reximdva ssrexv sylsyld sylan9r ancom31s pm2.61dne 19.23adv n0
      syl6com imp32 ) CEIZCEAJKLMACNZOZDCPZDQRZDEBJZKZQSZBDTZWQWPDEIZDEFJZKZLMZ
      FDNZOZWRXBUAWQWNXCWOXGDCEUBWQCEXDKZLMZFCNZXGWOWQXKXJFDNXGXJFDCUCWQXJXFFDW
      QXEXIPZXJXFUADCEXDUDXLXJXFXEXILUEUFUGUHUIAFCEUJUKULXHGJZDMZGUMXBWRXHXNXBG
      XHXNXBXHXNOXBDEXMKZQXNXOQSZXBUAXHXNXPXBXAXPBXMDBGUNWTXOQDEWSXMUOUPUQUFURX
      NXGXCXOQRZXBUAXNXGOZXCOXQDEXMUSZDPZXSQRZOZXBXRXQYBUAZXCXRXOLMZYCFDEXMUTZY
      DXQYAXTYDXOXSPZXQYAUADLEXMVAYFXQYAXOXSVBUFUGDLEXMVCZVDUGVEXCYBXSEWSKZQSZB
      XSTZXRXBXCHJZDPZYKQRZOZYKEWSKZQSZBYKTZUAZUAXCYBYJUAZUAHXSDEXMVFYKXSSZYRYS
      XCYTYNYBYQYJYTYLXTYMYAYKXSDVGYKXSQVHVIYPYIBYKXSYTYOYHQYKXSEWSVJUPVKVLVMXC
      YRHVNYRHBDEVOYRHVPVQVRXRXTYJXABXSTXBXRYDXTYEYGUGZXRYIXABXSXRWSXSMZOZXAYIU
      UCWTYHQXTWTXSPZWTYHSUUCDXSEWSVSXRXTUUBUUAVEXRUUBUUDFDEXMWSVTWAWBUPWCWDXAB
      XSDWEWFWGUIWHWIUFWJGDWKUKWLWM $.
      $( [4-Feb-2011] $)
  $}

  ${
    $d A x $.  $d A y $.  $d B y $.  $d R x $.  $d R y $.
    $( The principle of founded induction.  Theorem 4.4 of Don Monk's notes
       (see ~ frmin ).  This principle states that if ` B ` is a subclass of a
       founded class ` A ` with the property that every element of ` B ` whose
       initial segment is included in ` A ` is is itself equal to ` A ` .
       Compare ~ wfi and ~ tfi , which are special cases of this theorem that
       do not require the transitive closure to prove. $)
    frind $p |- ( ( ( R Fr A /\ A. x e. A Pred ( R , A , x ) e. _V ) /\
                     ( B C_ A /\
                       A. y e. A ( Pred ( R , A , y ) C_ B -> y e. B ) ) ) ->
                   A = B ) $=
      ( wfr cv cpred cvv wcel wral wa wss wi cdif c0 wne wn difss wceq wrex
      frmin eldif anbi1i anass ancom ccnv csn cima cin indif2 df-pred incom
      eqtri difeq1i 3eqtr4i eqeq1i ssdif0 bitr4i bitri anbi2i 3bitri rexbii2
      rexanali sylib ex mpani necon3bbii syl5ib con4d imp adantrl simprl eqssd
      ) CEFCEAGHIJACKLZDCMZCEBGZHZDMZVQDJZNBCKZLLCDVOWACDMZVPVOWAWBVOWBWAVOCDOZ
      PQZWARZWBRVOWCCMZWDWECDSVOWFWDLZWEVOWGLWCEVQHZPTZBWCUAZWEABCWCEUBWJVSVTRZ
      LZBCUAWEWIWLBWCCVQWCJZWILVQCJZWKLZWILWNWKWILZLWNWLLWMWOWIVQCDUCUDWNWKWIUE
      WPWLWNWPWIWKLWLWKWIUFWIVSWKWIVRDOZPTVSWHWQPEUGVQUHUIZWCUJZWRCUJZDOWHWQWRC
      DUKWHWCWRUJWSWCEVQULWCWRUMUNVRWTDVRCWRUJWTCEVQULCWRUMUNUOUPUQVRDURUSUDUTV
      AVBVCVSVTBCVDUTVEVFVGWBWCPCDURVHVIVJVKVLVOVPWAVMVN $.
      $( [6-Feb-2011] $)

    ${
      frind.1 $e |- R Fr A $.
      frind.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
      $( The principle of founded induction.  Theorem 4.4 of Don Monk's notes
         (see ~ frmin ).  This principle states that if ` B ` is a subclass of
         a founded class ` A ` with the property that every element of ` B `
         whose initial segment is included in ` A ` is is itself equal to
         ` A ` . $)
      frindi $p |- ( ( B C_ A /\
                         A. y e. A ( Pred ( R , A , y ) C_ B -> y e. B ) ) ->
                        A = B ) $=
        ( wfr cv cpred cvv wcel wral wa wss wi wceq pm3.2i frind mpan ) CEHZCEA
        IJKLACMZNDCOCEBIZJDOUCDLPBCMNCDQUAUBFGRABCDEST $.
        $( [6-Feb-2011] $)
    $}

  $}

  ${
    $d A w y z $.  $d A x $.  $d ph w z $.  $d R w y z $.  $d R x $.
    frinsg.1 $e |- ( y e. A ->
                       ( A. z e. Pred ( R , A , y ) [ z / y ] ph -> ph ) ) $.
    $( Founded Induction Schema.  If a property passes from all elements less
       than ` y ` of a founded class ` A ` to ` y ` itself (induction
       hypothesis), then the property holds for all elements of ` A ` . $)
    frinsg $p |- ( ( R Fr A /\ A. x e. A Pred ( R , A , x ) e. _V )
                     -> A. y e. A ph ) $=
      ( vw wfr cv cpred cvv wcel wral wa crab wceq wss wi ssrab2 wsb ax-17
      hbs1 hbral hbim weq eleq1 predeq3 raleqdv sbequ12 imbi12d chvar dfss3
      elrabsf pm3.27bi ralimi sylbi syl5 anc2li syl6ibr rgen frind mpanr12
      rabid2 sylib ) EFIEFBJKLMBENOZEACEPZQZACENVFVGEREFHJZKZVGRZVIVGMZSZHENVHA
      CETVMHEVIEMZVKVNACHUAZOVLVNVKVOVNACDUAZDVJNZVOVKCJZEMZVPDEFVRKZNZASZSVNVQ
      VOSZSCHVNWCCVNCUBZVQVOCVPCDVJDJZVJMCUBACDUCUDACHUCUEUECHUFZVSVNWBWCVRVIEU
      GWFWAVQAVOWFVPDVTVJEFVRVIUHUIACHUJUKUKGULVKWEVGMZDVJNVQDVJVGUMWGVPDVJWGWE
      EMVPACHWEEWDUNUOUPUQURUSACHVIEWDUNUTVABHEVGFVBVCACEVDVE $.
      $( [7-Feb-2011] $)
  $}

  ${
    $d A x $.  $d A w y z $.  $d ph w z $.  $d R x $.  $d R w y z $.
    frins.1 $e |- R Fr A $.
    frins.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    frins.3 $e |- ( y e. A ->
                      ( A. z e. Pred ( R , A , y ) [ z / y ] ph -> ph ) ) $.
    $( Founded Induction Schema.  If a property passes from all elements less
       than ` y ` of a founded class ` A ` to ` y ` itself (induction
       hypothesis), then the property holds for all elements of ` A ` . $)
    frins $p |- ( y e. A -> ph ) $=
      ( wfr cv cpred cvv wcel wral frinsg mp2an rspec ) ACEEFJEFBKLMNBEOACEOGHA
      BCDEFIPQR $.
      $( [6-Feb-2011] $)
  $}


  ${
    $d A w y z $.  $d A x $.  $d ph w z $.  $d R w y z $.  $d R x $.
    frins2fg.1 $e |- ( y e. A ->
                         ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.
    frins2fg.2 $e |- ( ps -> A. y ps ) $.
    frins2fg.3 $e |- ( y = z -> ( ph <-> ps ) ) $.
    $( Founded Induction schema, using implicit substitution. $)
    frins2fg $p |- ( ( R Fr A /\ A. x e. A Pred ( R , A , x ) e. _V )
                     -> A. y e. A ph ) $=
      ( cv wcel cpred wral wsbc sbie ralbii syl5ib frinsg ) ACDEFGDKZFLBEFGTMZN
      AADEKOZEUANHUBBEUAABDEIJPQRS $.
      $( [7-Feb-2011] $)
  $}


  ${
    $d A x $.  $d A y z $.  $d ph z $.  $d R x $.  $d R y z $.
    frins2f.1 $e |- R Fr A $.
    frins2f.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    frins2f.3 $e |- ( ps -> A. y ps ) $.
    frins2f.4 $e |- ( y = z -> ( ph <-> ps ) ) $.
    frins2f.5 $e |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.
    $( Founded Induction schema, using implicit substitution. $)
    frins2f $p |- ( y e. A -> ph ) $=
      ( wfr cv cpred cvv wcel wral frins2fg mp2an rspec ) ADFFGMFGCNOPQCFRADFRH
      IABCDEFGLJKSTUA $.
      $( [6-Feb-2011] $)
  $}

  ${
    $d A w y z $.  $d A x $.  $d ph w z $.  $d R w y z $.  $d R x $.
    $d ps y $.
    frins2g.1 $e |- ( y e. A ->
                         ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.
    frins2g.3 $e |- ( y = z -> ( ph <-> ps ) ) $.
    $( Founded Induction schema, using implicit substitution. $)
    frins2g $p |- ( ( R Fr A /\ A. x e. A Pred ( R , A , x ) e. _V )
                     -> A. y e. A ph ) $=
      ( ax-17 frins2fg ) ABCDEFGHBDJIK $.
      $( [8-Feb-2011] $)
  $}

  ${
    $d A x $.  $d A y z $.  $d ph z $.  $d ps y $.  $d R x $.  $d R y z $.
    frins2.1 $e |- R Fr A $.
    frins2.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    frins2.3 $e |- ( y = z -> ( ph <-> ps ) ) $.
    frins2.4 $e |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.
    $( Founded Induction schema, using implicit substitution. $)
    frins2 $p |- ( y e. A -> ph ) $=
      ( ax-17 frins2f ) ABCDEFGHIBDLJKM $.
      $( [6-Feb-2011] $)
  $}

  ${
    $d A x $.  $d A y z $.  $d B y $.  $d ph z $.  $d ps y $.  $d ch y $.
    $d R x $.  $d R y z $.
    frins3.1 $e |- R Fr A $.
    frins3.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    frins3.3 $e |- ( y = z -> ( ph <-> ps ) ) $.
    frins3.4 $e |- ( y = B -> ( ph <-> ch ) ) $.
    frins3.5 $e |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.


    $( Founded Induction schema, using implicit substitution. $)
    frins3 $p |- ( B e. A -> ch ) $=
      ( frins2 vtoclga ) ACEHGMABDEFGIJKLNOP $.
      $( [6-Feb-2011] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Ordering cross products
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x y $.  $d B x y $.  $d R x y $.  $d S x y $.  $d a x y $.
    $d b x y $.  $d c x y $.  $d d x y $.
    xporderlem.1 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\
                                                y e. ( A X. B ) ) /\
                              ( ( 1st ` x ) R ( 1st ` y ) \/
                                ( ( 1st ` x ) = ( 1st ` y ) /\
                                  ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
    $( Lemma for the lexicographical ordering theorems. $)
    xporderlem $p |- ( <. a , b >. T <. c , d >. <->
                        ( ( ( a e. A /\ c e. A ) /\ ( b e. B /\ d e. B ) ) /\
                          ( a R c \/ ( a = c /\ b S d ) ) ) ) $=
      ( cv cop wbr cxp wcel wa c1st cfv wceq c2nd wo copab weq df-br eleq2i
      bitri opex eleq1 visset opelxp syl6bb anbi1d fveq2 op1st syl6eq breq1d
      eqeq1d op2nd anbi12d orbi12d anbi2d breq2d eqeq2d opelopab an4 anbi1i
      3bitri ) HMZIMZNZJMZKMZNZGOZVLVONZAMZCDPZQZBMZVSQZRZVRSTZWASTZEOZWDWEUAZV
      RUBTZWAUBTZFOZRZUCZRZABUDZQZVJCQZVKDQZRZVMCQZVNDQZRZRZVJVMEOZHJUEZVKVNFOZ
      RZUCZRZWPWSRWQWTRRZXGRVPVQGQWOVLVOGUFGWNVQLUGUHWMWRWBRZVJWEEOZVJWEUAZVKWI
      FOZRZUCZRXHABVLVOVJVKUIVMVNUIVRVLUAZWCXJWLXOXPVTWRWBXPVTVLVSQWRVRVLVSUJVJ
      VKCDIUKZULUMUNXPWFXKWKXNXPWDVJWEEXPWDVLSTVJVRVLSUOVJVKHUKZUPUQZURXPWGXLWJ
      XMXPWDVJWEXSUSXPWHVKWIFXPWHVLUBTVKVRVLUBUOVJVKXRXQUTUQURVAVBVAWAVOUAZXJXB
      XOXGXTWBXAWRXTWBVOVSQXAWAVOVSUJVMVNCDKUKZULUMVCXTXKXCXNXFXTWEVMVJEXTWEVOS
      TVMWAVOSUOVMVNJUKZUPUQZVDXTXLXDXMXEXTWEVMVJYCVEXTWIVNVKFXTWIVOUBTVNWAVOUB
      UOVMVNYBYAUTUQVDVAVBVAVFXBXIXGWPWQWSWTVGVHVI $.
      $( [16-Mar-2011] $)
  $}

  ${
    $d A a b c d e f t u v x y z $.  $d B a b c d e f t u v x y z $.
    $d R a b c d e f x y $.  $d S a b c d e f x y $.  $d T a b c d e f t u v $.
    poxp.1 $e |- R Po A $.
    poxp.2 $e |- S Po B $.
    poxp.3 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\
                                          y e. ( A X. B ) ) /\
                                        ( ( 1st ` x ) R ( 1st ` y ) \/
                                          ( ( 1st ` x ) = ( 1st ` y ) /\
                                           ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.


    $( A lexicographical ordering of two posets. $)
    poxp $p |- T Po ( A X. B ) $=
      ( vt vu vv va vb vc vd ve vf cxp wpo cv wbr wn wa wi wral cop wceq wcel
      wex w3a 3an6 weq wo wb breq12 anidms notbid 3ad2ant1 3adant3 3adant1
      anbi12d 3adant2 imbi12d xporderlem notbii anbi12i imbi12i syl6bb poirr
      mpan intnand anim12i ioran sylibr potr imp orcd expr breq2 biimpa expcom
      adantrd adantl jaod ex breq1 equequ1 anbi1d orbi12d imbi2d expdimp
      anim2d orim2d syl5bir exp3a com12 imp3a jaao sylbi an4 biimpi jctild
      adantld syl5ib jca 3exp com3l 19.23aivv 3imp elxp syl3anb rgen3 df-po
      mpbir ) CDTZGUAKUBZXRGUCZUDZXRLUBZGUCZYAMUBZGUCZUEZXRYCGUCZUFZUEZMXQUGLXQ
      UGKXQUGYHKLMXQXQXQXRNUBZOUBZUHZUIZYICUJZYJDUJZUEZUEZOUKNUKZYAPUBZQUBZUHZU
      IZYRCUJZYSDUJZUEZUEZQUKPUKZYCRUBZSUBZUHZUIZUUGCUJZUUHDUJZUEZUEZSUKRUKZYHX
      RXQUJYAXQUJYCXQUJYQUUFUUOYHYPUUFUUOYHUFUFNOUUOYPUUFYHUUNYPUUFYHUFUFRSUUFU
      UNYPYHUUEUUNYPYHUFUFPQYPUUEUUNYHYPUUEUUNYHYPUUEUUNULYLUUAUUJULZYOUUDUUMUL
      ZUEYHYLYOUUAUUDUUJUUMUMUUPUUQYHUUPYHYMYMUEYNYNUEUEZYIYIEUCZNNUNZYJYJFUCZU
      EZUOZUEZUDZYMUUBUEYNUUCUEUEZYIYREUCZNPUNZYJYSFUCZUEZUOZUEZUUBUUKUEUUCUULU
      EUEZYRUUGEUCZPRUNZYSUUHFUCZUEZUOZUEZUEZYMUUKUEYNUULUEUEZYIUUGEUCZNRUNZYJU
      UHFUCZUEZUOZUEZUFZUEZUUQUUPYHYKYKGUCZUDZYKYTGUCZYTUUIGUCZUEZYKUUIGUCZUFZU
      EUWIUUPXTUWKYGUWPYLUUAXTUWKUPUUJYLXSUWJYLXSUWJUPXRYKXRYKGUQURUSUTUUPYEUWN
      YFUWOUUPYBUWLYDUWMYLUUAYBUWLUPUUJXRYKYAYTGUQVAUUAUUJYDUWMUPYLYAYTYCUUIGUQ
      VBVCYLUUJYFUWOUPUUAXRYKYCUUIGUQVDVEVCUWKUVEUWPUWHUWJUVDABCDEFGNONOJVFVGUW
      NUVTUWOUWGUWLUVLUWMUVSABCDEFGNOPQJVFABCDEFGPQRSJVFVHABCDEFGNORSJVFVIVHVJU
      UQUVEUWHYOUUDUVEUUMYOUVCUURYOUUSUDZUVBUDZUEUVCUDYMUWQYNUWRCEUAZYMUWQHCYIE
      VKVLYNUVAUUTDFUAZYNUVAUDIDYJFVKVLVMVNUUSUVBVOVPVMUTUUQUVFUVMUEZUVKUVRUEZU
      EUWGUVTUUQUXBUWGUXAUUQUXBUWFUWAUUQYMUUBUUKULZYNUUCUULULZUEZUXBUWFUFYMYNUU
      BUUCUUKUULUMUXEUVKUVRUWFUXCUVGUVRUWFUFZUXDUVJUXCUVGUXFUXCUVGUEUVNUWFUVQUX
      CUVGUVNUWFUXCUVGUVNUEZUEUWBUWEUXCUXGUWBUWSUXCUXGUWBUFHCYIYRUUGEVQVLVRVSVT
      UVGUVQUWFUFUXCUVGUVOUWFUVPUVOUVGUWFUVOUVGUEUWBUWEUVOUVGUWBYRUUGYIEWAWBVSW
      CWDWEWFWGUXDUVHUVIUXFUVHUXDUVIUXFUFUVHUXDUVIUXFUVHUXFUVRUVNUVOUWDUEZUOZUF
      UXDUVIUEZUVHUWFUXIUVRUVHUWBUVNUWEUXHYIYRUUGEWHUVHUWCUVOUWDNPRWIWJWKWLUXJU
      VQUXHUVNUXJUVPUWDUVOUXDUVIUVPUWDUWTUXDUVIUVPUEUWDUFIDYJYSUUHFVQVLWMWNWOWP
      WQWRWSWTWSXAYOUUMUWAUUDYOUUMUEUWAYMYNUUKUULXBXCVDXDXEUVFUVKUVMUVRXBXFXGWP
      VRXAXHXIXJXIXJXIXJXKNOXRCDXLPQYACDXLRSYCCDXLXMXNKLMXQGXOXP $.
      $( [16-Mar-2011] $)
  $}

  ${
    $d A a b c d t u x y $.  $d B a b c d t u x y $.  $d R x y $.  $d S x y $.
    $d T a b c d t u $.
    soxp.1 $e |- R Or A $.
    soxp.2 $e |- S Or B $.
    soxp.3 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) )
                                        /\
                                        ( ( 1st ` x ) R ( 1st ` y ) \/
                                          ( ( 1st ` x ) = ( 1st ` y ) /\
                                           ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
    $( A lexicographical ordering of two strictly ordered classes. $)
    soxp $p |- T Or ( A X. B ) $=
      ( vt vu va vb vc vd cxp wor wpo cv wbr weq w3o wral df-so sopo ax-mp
      poxp cop wceq wcel wa wex wi wo breq12 eqeq12 wb ancoms 3orbi123d
      xporderlem visset opth 3orbi123i syl6bb wn solin mpan 3orass df-or bitri
      sylib orim2d im2anan9 pm2.53 orc syl6 adantr orel1 anim2d imor biimpri
      com12 equcomi anim1i olcd ex syld a1d jaoi imp syl6com jaod imp3a ioran
      ianor anbi2i anbi12i syl5ib df-3or sylibr pm3.2 idd ancom syl2anb
      3orim123d mpd an4s syl5bir expcom 19.23aivv elxp rgen2a mpbir2an ) CDQZGR
      XOGSKTZLTZGUAZKLUBZXQXPGUAZUCZLXOUDKXOUDKLXOGUEABCDEFGCERZCESHCEUFUGDFRZD
      FSIDFUFUGJUHYAKLXOXPMTZNTZUIZUJZYDCUKZYEDUKZULZULZNUMMUMZXQOTZPTZUIZUJZYM
      CUKZYNDUKZULZULZPUMOUMZYAXPXOUKXQXOUKYLUUAYAYKUUAYAUNMNUUAYKYAYTYKYAUNOPY
      KYTYAYGYPYJYSYAYGYPULZYJYSULZYAUUBYAYHYQULZYIYRULZULZYDYMEUAZMOUBZYEYNFUA
      ZULZUOZULZUUHNPUBZULZYQYHULZYRYIULZULZYMYDEUAZOMUBZYNYEFUAZULZUOZULZUCZUU
      CUUBYAYFYOGUAZYFYOUJZYOYFGUAZUCUVDUUBXRUVEXSUVFXTUVGXPYFXQYOGUPXPYFXQYOUQ
      YPYGXTUVGURXQYOXPYFGUPUSUTUVEUULUVFUUNUVGUVCABCDEFGMNOPJVAYDYEYMYNMVBNVBP
      VBVCABCDEFGOPMNJVAVDVEYHYQYIYRUVDUUFUUKUUNUVBUCZUVDUUFUUKUUNUOZVFZUVBUNZU
      VHUUFUUGVFZUUHVFZUUIVFZUOZULZUVMUUMVFZUOZULZUVBUVJUUFUVPUVRUVBUUFUVPUUHUU
      RUOZUVMUUMUUTUOZUOZULZUVRUVBUNUUDUVLUVTUUEUVOUWBUUDUUGUUHUURUCZUVLUVTUNZY
      BUUDUWDHCYDYMEVGVHUWDUUGUVTUOUWEUUGUUHUURVIUUGUVTVJVKVLUUEUVNUWAUVMUUEUUI
      UUMUUTUCZUVNUWAUNZYCUUEUWFIDYEYNFVGVHUWFUUIUWAUOUWGUUIUUMUUTVIUUIUWAVJVKV
      LVMVNUWCUVMUVBUVQUVTUVMUVBUNUWBUVTUVMUURUVBUUHUURVOUURUVAVPZVQVRUVQUWCUVT
      UVMUUTUOZULUVBUVQUWBUWIUVTUVQUWAUUTUVMUUMUUTVSVMVTUVTUWIUVBUUHUWIUVBUNUUR
      UUHUWIUUTUVBUWIUUHUUTUUHUUTUNUWIUUHUUTWAWBWCUUHUUTUVBUUHUUTULUVAUURUUHUUS
      UUTMOWDWEWFWGWHUURUVBUWIUWHWIWJWKWLWMVQWNUVJUUKVFZUUNVFZULUVSUUKUUNWOUWJU
      VPUWKUVRUWJUVLUUJVFZULUVPUUGUUJWOUWLUVOUVLUUHUUIWPWQVKUUHUUMWPWRVKWSUVHUV
      IUVBUOUVKUUKUUNUVBWTUVIUVBVJVKXAUUFUUKUULUUNUUNUVBUVCUUFUUKXBUUFUUNXCUUOU
      UPUVBUVCUNUUDUUEUUQUVBXBYHYQXDYIYRXDXEXFXGXHXIWKXHXJXKWCXKWKMNXPCDXLOPXQC
      DXLXEXMXN $.
      $( [17-Mar-2011] $)

  $}

  ${
    $d A a b c d s v w x y z $.  $d B a b d s v w x y z $.
    $d R a b c v w x y $.  $d S b c d t u v w x y $.  $d T a b s w z $.
    $d a s t u $.
    frxp.1 $e |- R Fr A $.
    frxp.2 $e |- S Fr B $.
    frxp.3 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) )
                                        /\
                                        ( ( 1st ` x ) R ( 1st ` y ) \/
                                          ( ( 1st ` x ) = ( 1st ` y ) /\
                                           ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
    $( A lexicographical ordering of two well founded classes. $)
    frxp $p |- T Fr ( A X. B ) $=
      ( vs vw vz vc va vb vd vv vt vu cxp wfr cv wss c0 wne wa wbr wn wral
      wrex wi df-fr cdm wceq wo xpeq0 biimpri olcs sseq2 ss0 dm0 0ss eqsstri
      dmeq sseq1d mpbiri syl syl6bi dmxp dmss syl5bi pm2.61ine adantr wrel wb
      relxp relss mpi reldm0 necon3bid biimpa wcel cop csn cima cvv visset
      imaexg ax-mp sseq1 neeq1 anbi12d raleq rexeqbi1dv imbi12d wal mpbi a4i
      vtocl crn sstr imassrn orcs rn0 rneq rnxp rnss sylancr wex eldm elimasn
      df-br bitr4i ne0i sylbir 19.23aiv sylbi syl2an c1st cfv c2nd wel breq1
      notbid rcla4cv 1stdm syl5 exp3a impcom elrel ex weq eleq1 fveq2 op1st
      syl6eq eqeq1d op2nd breq1d opeq1 eleq1d imbi1d syl5ibr adantl syl5bir
      com3l 19.23aivv mpdd adantlr jcad r19.21aiv sylan olc ralimi syl6 opex
      anbi1d orbi12d anbi2d breq2d eqeq2d brab notbii ianor ioran pm4.62
      anbi2i bitri orbi2i 3bitri ralbii syl6ibr reximdv com23 mpd expimpd cres
      df-rex eqid eqeq1 breq2 ralbidv cla4ev mpan sylanb eximi excom sylib
      elsnres anbi1i 19.41v anass exbii 3bitr2i sylibr resss ssrexv r19.23adv
      dmex mp2and mpgbir ) CDUAZGUBKUCZUXCUDZUXDUEUFZUGZLUCZMUCZGUHZUIZLUXDUJZM
      UXDUKZULKKMLUXCGUMUXGUXDUNZCUDZUXNUEUFZUXMUXEUXOUXFUXEUXOULZDUEDUEUOZUXCU
      EUOZUXQCUEUOZUXRUXSUXSUXTUXRUPCDUQURZUSUXSUXEUXDUEUDZUXOUXCUEUXDUTZUYBUXD
      UEUOZUXOUXDVAZUYDUXOUEUNZCUDUYFUECVBCVCVDUYDUXNUYFCUXDUEVEVFVGVHVIVHDUEUF
      UXCUNZCUOZUXQCDVJUYHUXNUYGUDUXOUXEUYGCUXNUTUXDUXCVKVLVHVMVNUXEUXFUXPUXEUX
      DUEUXNUEUXEUXDVOZUYDUXNUEUOVPUXEUXCVOUYICDVQUXDUXCVRVSZUXDVTVHWAWBUXGNUCZ
      OUCZEUHZUIZNUXNUJZOUXNUKZUXMUXOUXPUGZUXGUYOUXMOUXNUXGUYLUXNWCZUYOUXMUXGUY
      RUYOUGZUXHUYLPUCZWDZGUHZUIZLUXDUJZPUXDUYLWEZWFZUKZUXMUXEUYSVUGULUXFUXEUYR
      UYOVUGUXEUYRUGQUCZUYTFUHZUIZQVUFUJZPVUFUKZUYOVUGULZVUFDUDZVUFUEUFZVULUXEU
      YRRUCZDUDZVUPUEUFZUGZVUJQVUPUJZPVUPUKZULZVUNVUOUGZVULULRVUFUXDWGWCVUFWGWC
      KWHZUXDVUEWGWIWJVUPVUFUOZVUSVVCVVAVULVVEVUQVUNVURVUOVUPVUFDWKVUPVUFUEWLWM
      VUTVUKPVUPVUFVUJQVUPVUFWNWOWPVVBRDFUBVVBRWQIRPQDFUMWRWSWTVUFUXDXAZUDVVFDU
      DZVUNUXEVUFVVFDXBUXDVUEXCUXEVVGULZCUEUXTUXSVVHUXTUXRUXSUYAXDUXSUXEUYBVVGU
      YCUYBUYDVVGUYEUYDVVGUEXAZDUDVVIUEDXEDVCVDUYDVVFVVIDUXDUEXFVFVGVHVIVHCUEUF
      UXCXAZDUOZVVHCDXGVVKVVFVVJUDVVGUXEVVJDVVFUTUXDUXCXHVLVHVMXIUYRUYLUYTUXDUH
      ZPXJVUOPUYLUXDOWHZXKVVLVUOPVVLUYTVUFWCZVUOVVNVUAUXDWCZVVLUXDUYLUYTVVMPWHZ
      XLZUYLUYTUXDXMXNVUFUYTXOXPXQXRXSUXEVULVUMULUYRUXEUYOVULVUGUXEUYOVULVUGULU
      XEUYOUGZVUKVUDPVUFVVRVUKUXHUXCWCZVUAUXCWCZUGZUIZUXHXTYAZUYLEUHZUIZVWCUYLU
      OZUXHYBYAZUYTFUHZUIZULZUGZUPZLUXDUJZVUDVVRVUKVWKLUXDUJZVWMUYIUYOVUKVWNULU
      XEUYIUYOUGZVUKVWNVWOVUKUGZVWKLUXDVWPLKYCZVWEVWJVWOVWQVWEULZVUKUYOUYIVWRUY
      OUYIVWQVWEUYOVWCUXNWCVWEUYIVWQUGUYNVWENVWCUXNUYKVWCUOUYMVWDUYKVWCUYLEYDYE
      YFUXHUXDYGYHYIYJVNUYIVUKVWQVWJULZUYOUYIVUKUGZVWQUXHSUCZTUCZWDZUOZTXJSXJZV
      WJUYIVWQVXEULVUKUYIVWQVXESTUXHUXDYKYLVNVXEVWTVWQVWJVXDVWTVWSULSTVXDVWSVXC
      UXDWCZSOYMZVXBUYTFUHZUIZULZULVWTVXDVWQVXFVWJVXJUXHVXCUXDYNVXDVWFVXGVWIVXI
      VXDVWCVXAUYLVXDVWCVXCXTYAVXAUXHVXCXTYOVXAVXBSWHZYPYQYRVXDVWHVXHVXDVWGVXBU
      YTFVXDVWGVXCYBYAVXBUXHVXCYBYOVXAVXBVXKTWHZYSYQYTYEWPWPVXGVWTVXFVXIVXGVXFV
      XIULUYLVXBWDZUXDWCZVXIULZVWTVXGVXFVXNVXIVXGVXCVXMUXDVXAUYLVXBUUAUUBUUCVUK
      VXOUYIVUKVXBVUFWCVXIVXNVUJVXIQVXBVUFQTYMVUIVXHVUHVXBUYTFYDYEYFUXDUYLVXBVV
      MVXLXLUUDUUEUUFUUGUUFUUHUUGUUIUUJUUKUULYLUYJUUMVWKVWLLUXDVWKVWBUUNUUOUUPV
      UCVWLLUXDVUCVWAVWDVWFVWHUGZUPZUGZUIVWBVXQUIZUPVWLVUBVXRAUCZUXCWCZBUCZUXCW
      CZUGZVXTXTYAZVYBXTYAZEUHZVYEVYFUOZVXTYBYAZVYBYBYAZFUHZUGZUPZUGVVSVYCUGZVW
      CVYFEUHZVWCVYFUOZVWGVYJFUHZUGZUPZUGVXRABUXHVUAGLWHUYLUYTUUQZALYMZVYDVYNVY
      MVYSWUAVYAVVSVYCVXTUXHUXCYNUURWUAVYGVYOVYLVYRWUAVYEVWCVYFEVXTUXHXTYOZYTWU
      AVYHVYPVYKVYQWUAVYEVWCVYFWUBYRWUAVYIVWGVYJFVXTUXHYBYOYTWMUUSWMVYBVUAUOZVY
      NVWAVYSVXQWUCVYCVVTVVSVYBVUAUXCYNUUTWUCVYOVWDVYRVXPWUCVYFUYLVWCEWUCVYFVUA
      XTYAUYLVYBVUAXTYOUYLUYTVVMYPYQZUVAWUCVYPVWFVYQVWHWUCVYFUYLVWCWUDUVBWUCVYJ
      UYTVWGFWUCVYJVUAYBYAUYTVYBVUAYBYOUYLUYTVVMVVPYSYQUVAWMUUSWMJUVCUVDVWAVXQU
      VEVXSVWKVWBVXSVWEVXPUIZUGVWKVWDVXPUVFWUEVWJVWEWUEVWFUIVWIUPVWJVWFVWHUVEVW
      FVWHUVGXNUVHUVIUVJUVKUVLUVMUVNYLUVOVNUVPUVQVNVUGUXLMUXDVUEUVRZUKZUXMVUGUX
      IVUAUOZVVOUXLUGZUGZPXJZMXJZWUGVUGWUJMXJZPXJZWULVUGVVNVUDUGZPXJWUNVUDPVUFU
      VSWUOWUMPVVOVUDWUMVVNVUAVUAUOZVVOVUDUGZWUMVUAUVTWUJWUPWUQUGMVUAVYTWUHWUHW
      UPWUIWUQUXIVUAVUAUWAWUHUXLVUDVVOWUHUXKVUCLUXDWUHUXJVUBUXIVUAUXHGUWBYEUWCU
      UTWMUWDUWEVVQUWFUWGXRWUJPMUWHUWIWUGUXIWUFWCZUXLUGZMXJWULUXLMWUFUVSWUSWUKM
      WUSWUHVVOUGZPXJZUXLUGWUTUXLUGZPXJWUKWURWVAUXLPUXIUXDUYLVVMUWJUWKWUTUXLPUW
      LWVBWUJPWUHVVOUXLUWMUWNUWOUWNUVIUWPWUFUXDUDWUGUXMULUXDVUEUWQUXLMWUFUXDUWR
      WJVHUUPYIUWSVUPCUDZVURUGZUYNNVUPUJZOVUPUKZULZUYQUYPULRUXNUXDVVDUWTVUPUXNU
      OZWVDUYQWVFUYPWVHWVCUXOVURUXPVUPUXNCWKVUPUXNUEWLWMWVEUYOOVUPUXNUYNNVUPUXN
      WNWOWPWVGRCEUBWVGRWQHRONCEUMWRWSWTYHUXAUXB $.
      $( [17-Mar-2011] $)
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.  $d S x y $.
    wexp.1 $e |- R We A $.
    wexp.2 $e |- S We B $.
    wexp.3 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) )
                                        /\
                                        ( ( 1st ` x ) R ( 1st ` y ) \/
                                          ( ( 1st ` x ) = ( 1st ` y ) /\
                                           ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
    $( A lexicographical ordering of two well ordered classes. $)
    wexp $p |- T We ( A X. B ) $=
      ( cxp wwe wfr wor df-we wefr ax-mp frxp weso soxp mpbir2an ) CDKZGLUBGMUB
      GNUBGOABCDEFGCELZCEMHCEPQDFLZDFMIDFPQJRABCDEFGUCCENHCESQUDDFNIDFSQJTUA $.
      $( [17-Mar-2011] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Ordering Ordinal Sequences
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A f x $.  $d G f x $.  $d X x $.
    orderseqlem.1 $e |- F = { f | E. x e. On f : x --> A } $.
    $( Lemma for ~ poseq and ~ soseq .  The function value of a sequene is
       either in ` A ` or null. $)
    orderseqlem $p |- ( G e. F -> ( G ` X ) e. ( A u. { (/) } ) ) $=
      ( wcel cv wf con0 wrex cfv c0 csn cun wceq feq1 rexbidv elab2g ibi wi
      wfun crn wss unss1 sseld fvrn0 syl5com ffun frn sylc a1i r19.23aiv syl )
      EDHZAIZBEJZAKLZFEMZBNOZPZHZUPUSUQBCIZJZAKLUSCEDDVDEQVEURAKUQBVDERSGTUAURV
      CAKURVCUBUQKHEUCZEUDZBUEZVCURVHUTVGVAPZHVCVFVHVIVBUTVGBVAUFUGEFUHUIUQBEUJ
      UQBEUKULUMUNUO $.
      $( [8-Jun-2011] $)
  $}


  ${
    $d A b f x $.  $d a b c f g t w x y z $.  $d F a b c f g t w x z $.
    $d R f g t w x z $.  $d S a b c $.
    poseq.1 $e |- R Po ( A u. { (/) } ) $.
    poseq.2 $e |- F = { f | E. x e. On f : x --> A } $.
    poseq.3 $e |- S = { <. f , g >. | ( ( f e. F /\ g e. F ) /\
                        E. x e. On ( A. y e. x ( f ` y ) = ( g ` y ) /\
                           ( f ` x ) R ( g ` x ) ) ) } $.
    $( A partial ordering of sequences of ordinals. $)
    poseq $p |- S Po F $=
      ( va vb vc vz vw vt wpo cv wbr wn wa wi wral wcel w3a cfv wceq con0 wrex
      c0 csn cun wf cab feq2 cbvrexv abbii eqtri orderseqlem poirr mpan syl
      intnand adantr nrexdv imnan mpbi visset weq eleq1 anbi1d fveq1 eqeq1d
      ralbidv breq1d anbi12d rexbidv anbi2d eqeq2d breq2d brab mtbir simplll
      simplrr an4 2rexbii reeanv bitri wel w3o word ordtri3or eloni syl2an
      3simp1l wss onelss imp adantll ssralv anim2d r19.26 syl6ibr eqtr ralimi
      syl6 adantrd 3impia fveq2 eqeq12d rcla4v breq2 biimpd com3l ad2ant2lr
      impcom 3adant1 raleq breq12d rcla4ev sylan32c a1d 3exp syl5bb imbi1d
      potr ad2antrr ad2antlr ad2antll 3jca sylancr anim12i anassrs sylan2
      exp32 syl5cbi 3simp1r adantlr anim1d sylbir breq1 biimprd ad2ant2rl
      3jaod mpd r19.23aivv jca31 an4s anbi12i 3imtr4i pm3.2i a1i rgen3 df-po
      mpbir ) HERLSZUUQETZUAZUUQMSZETZUUTNSZETZUBZUUQUVBETZUCZUBZNHUDMHUDLHUDUV
      GLMNHHHUVGUUQHUEZUUTHUEZUVBHUEZUFUUSUVFUURUVHUVHUBZBSZUUQUGZUVMUHZBASZUDZ
      UVOUUQUGZUVQDTZUBZAUIUJZUBZUVKUVTUAZUCUWAUAUVHUWBUVHUVHUVSAUIUVHUVSUAUVOU
      IUEUVHUVRUVPUVHUVQCUKULUMZUEZUVRUAZMCFHUUQUVOHUVOCFSZUNZAUIUJZFUOUUTCUWFU
      NZMUIUJZFUOJUWHUWJFUWGUWIAMUIUVOUUTCUWFUPUQURUSUTUWCDRZUWDUWEIUWCUVQDVAVB
      VCVDVEVFVEUVKUVTVGVHUWFHUEZGSZHUEZUBZUVLUWFUGZUVLUWMUGZUHZBUVOUDZUVOUWFUG
      ZUVOUWMUGZDTZUBZAUIUJZUBZUVHUWNUBZUVMUWQUHZBUVOUDZUVQUXADTZUBZAUIUJZUBUWA
      FGUUQUUQELVIZUXLFLVJZUWOUXFUXDUXKUXMUWLUVHUWNUWFUUQHVKVLZUXMUXCUXJAUIUXMU
      WSUXHUXBUXIUXMUWRUXGBUVOUXMUWPUVMUWQUVLUWFUUQVMVNZVOUXMUWTUVQUXADUVOUWFUU
      QVMVPVQVRVQGLVJZUXFUVKUXKUVTUXPUWNUVHUVHUWMUUQHVKVSUXPUXJUVSAUIUXPUXHUVPU
      XIUVRUXPUXGUVNBUVOUXPUWQUVMUVMUVLUWMUUQVMVTVOUXPUXAUVQUVQDUVOUWMUUQVMWAVQ
      VRVQKWBWCUVHUVIUBZUVMUVLUUTUGZUHZBOSZUDZUXTUUQUGZUXTUUTUGZDTZUBZOUIUJZUBZ
      UVIUVJUBZUXRUVLUVBUGZUHZBPSZUDZUYKUUTUGZUYKUVBUGZDTZUBZPUIUJZUBZUBUVHUVJU
      BZUVMUYIUHZBQSZUDZVUAUUQUGZVUAUVBUGZDTZUBZQUIUJZUBZUVDUVEUXQUYHUYFUYQVUHU
      XQUYHUBZUYFUYQUBZUBUVHUVJVUGUVHUVIUYHVUJWDUXQUVIUVJVUJWEVUJVUIVUGVUJUYAUY
      LUBZUYDUYOUBZUBZPUIUJOUIUJZVUIVUGUCZVUNUYEUYPUBZPUIUJOUIUJVUJVUMVUPOPUIUI
      UYAUYLUYDUYOWFWGUYEUYPOPUIUIWHWIVUMVUOOPUIUIUXTUIUEZUYKUIUEZUBZOPWJZOPVJZ
      POWJZWKZVUMVUOUCZUXTWLUYKWLVVCVUQVURUXTUYKWMUXTWNUYKWNWOVUSVUTVVDVVAVVBVU
      SVUTVUMVUOVUSVUTVUMUFZVUGVUIVUQUYTBUXTUDZUYBUXTUVBUGZDTZVUGVVEVUQVURVUTVU
      MWPVUSVUTVUMVVFVUSVUTUBZVUKVVFVULVVIUXTUYKWQZVUKVVFUCVURVUTVVJVUQVURVUTVV
      JUYKUXTWRWSWTVVJVUKUXSUYJUBZBUXTUDZVVFVVJVUKUYAUYJBUXTUDZUBZVVLVVJUYLVVMU
      YAUYJBUXTUYKXAXBUXSUYJBUXTXCZXDVVKUYTBUXTUVMUXRUYIXEZXFZXGVCXHXIVUTVUMVVH
      VUSVUMVUTVVHUYLUYDVUTVVHUCZUYAUYOUYLUYDVVRVUTUYLUYDVVHVUTUYLUYCVVGUHZUYDV
      VHUCUYJVVSBUXTUYKBOVJUXRUYCUYIVVGUVLUXTUUTXJUVLUXTUVBXJXKXLVVSUYDVVHUYCVV
      GUYBDXMXNXGXOWSXPXQXRVUFVVFVVHUBZQUXTUIQOVJZVUBVVFVUEVVHUYTBVUAUXTXSVWAVU
      CUYBVUDVVGDVUAUXTUUQXJVUAUXTUVBXJXTVQYAZYBYCYDVUQVVAVVDUCVURVVAVVLUYDUYCV
      VGDTZUBZUBZVUOUCVVDVUQVVAVWEVUMVUOVVAVVLVUKVWDVULVVAVVNVUKVVLVVAVVMUYLUYA
      UYJBUXTUYKXSVSVVOYEVVAVWCUYOUYDVVAUYCUYMVVGUYNDUXTUYKUUTXJUXTUYKUVBXJXTVS
      VQYFVUQVWEVUIVUGVUQVVTVUGVWEVUIUBVWBVVLVWDVUIVVTVVLVVFVWDVUIUBVVHVVQVUIVW
      DVVHUWKUYBUWCUEZUYCUWCUEZVVGUWCUEZUFVWDVVHUCVUIUWCUYBUYCVVGDYGIVUIVWFVWGV
      WHUVHVWFUVIUYHACFHUUQUXTJUTYHUVIVWGUVHUYHACFHUUTUXTJUTYIUVJVWHUXQUVIACFHU
      VBUXTJUTYJYKYLXQYMYNYOYPYQVEVUSVVBVUMVUOVUSVVBVUMUFZVUGVUIVURUYTBUYKUDZUY
      KUUQUGZUYNDTZVUGVWIVUQVURVVBVUMYRVUSVVBVUMVWJVUSVVBUBUYKUXTWQZVUMVWJUCVUQ
      VVBVWMVURVUQVVBVWMUXTUYKWRWSYSVWMVUKVWJVULVWMVUKUXSBUYKUDZUYLUBZVWJVWMUYA
      VWNUYLUXSBUYKUXTXAYTVWOVVKBUYKUDVWJUXSUYJBUYKXCVVKUYTBUYKVVPXFUUAXGXHVCXI
      VVBVUMVWLVUSVUMVVBVWLUYAUYOVVBVWLUCZUYLUYDUYAUYOVWPVVBUYAUYOVWLVVBUYAVWKU
      YMUHZUYOVWLUCUXSVWQBUYKUXTBPVJUVMVWKUXRUYMUVLUYKUUQXJUVLUYKUUTXJXKXLVWQVW
      LUYOVWKUYMUYNDUUBUUCXGXOWSUUDXQXRVUFVWJVWLUBQUYKUIQPVJZVUBVWJVUEVWLUYTBVU
      AUYKXSVWRVUCVWKVUDUYNDVUAUYKUUQXJVUAUYKUVBXJXTVQYAYBYCYDUUEUUFUUGUUAXQUUH
      UUIUVAUYGUVCUYRUXEUXFUXGBUXTUDZUYBUXTUWMUGZDTZUBZOUIUJZUBUYGFGUUQUUTEUXLM
      VIZUXMUWOUXFUXDVXCUXNUXMUWRBUXTUDZUXTUWFUGZVWTDTZUBZOUIUJVXCUXDUXMVXHVXBO
      UIUXMVXEVWSVXGVXAUXMUWRUXGBUXTUXOVOUXMVXFUYBVWTDUXTUWFUUQVMVPVQVRUXCVXHAO
      UIAOVJZUWSVXEUXBVXGUWRBUVOUXTXSVXIUWTVXFUXAVWTDUVOUXTUWFXJUVOUXTUWMXJXTVQ
      UQYEVQGMVJZUXFUXQVXCUYFVXJUWNUVIUVHUWMUUTHVKVSVXJVXBUYEOUIVXJVWSUYAVXAUYD
      VXJUXGUXSBUXTVXJUWQUXRUVMUVLUWMUUTVMVTVOVXJVWTUYCUYBDUXTUWMUUTVMWAVQVRVQK
      WBUXEUVIUWNUBZUXRUWQUHZBUYKUDZUYMUYKUWMUGZDTZUBZPUIUJZUBUYRFGUUTUVBEVXDNV
      IZFMVJZUWOVXKUXDVXQVXSUWLUVIUWNUWFUUTHVKVLVXSUWRBUYKUDZUYKUWFUGZVXNDTZUBZ
      PUIUJVXQUXDVXSVYCVXPPUIVXSVXTVXMVYBVXOVXSUWRVXLBUYKVXSUWPUXRUWQUVLUWFUUTV
      MVNVOVXSVYAUYMVXNDUYKUWFUUTVMVPVQVRUXCVYCAPUIAPVJZUWSVXTUXBVYBUWRBUVOUYKX
      SVYDUWTVYAUXAVXNDUVOUYKUWFXJUVOUYKUWMXJXTVQUQYEVQGNVJZVXKUYHVXQUYQVYEUWNU
      VJUVIUWMUVBHVKZVSVYEVXPUYPPUIVYEVXMUYLVXOUYOVYEVXLUYJBUYKVYEUWQUYIUXRUVLU
      WMUVBVMZVTVOVYEVXNUYNUYMDUYKUWMUVBVMWAVQVRVQKWBUUJUXEUXFUXGBVUAUDZVUCVUAU
      WMUGZDTZUBZQUIUJZUBVUHFGUUQUVBEUXLVXRUXMUWOUXFUXDVYLUXNUXMUWRBVUAUDZVUAUW
      FUGZVYIDTZUBZQUIUJVYLUXDUXMVYPVYKQUIUXMVYMVYHVYOVYJUXMUWRUXGBVUAUXOVOUXMV
      YNVUCVYIDVUAUWFUUQVMVPVQVRUXCVYPAQUIAQVJZUWSVYMUXBVYOUWRBUVOVUAXSVYQUWTVY
      NUXAVYIDUVOVUAUWFXJUVOVUAUWMXJXTVQUQYEVQVYEUXFUYSVYLVUGVYEUWNUVJUVHVYFVSV
      YEVYKVUFQUIVYEVYHVUBVYJVUEVYEUXGUYTBVUAVYEUWQUYIUVMVYGVTVOVYEVYIVUDVUCDVU
      AUWMUVBVMWAVQVRVQKWBUUKUULUUMUUNLMNHEUUOUUP $.
      $( [8-Jun-2011] $)
  $}

  ${
    $d a b p q y $.  $d A f p q x $.  $d A y $.  $d F a b f g x $.
    $d f g x y $.  $d R f g x $.  $d S a b $.
    soseq.1 $e |- R Or ( A u. { (/) } ) $.
    soseq.2 $e |- F = { f | E. x e. On f : x --> A } $.
    soseq.3 $e |- S = { <. f , g >. | ( ( f e. F /\ g e. F ) /\
                        E. x e. On ( A. y e. x ( f ` y ) = ( g ` y ) /\
                           ( f ` x ) R ( g ` x ) ) ) } $.
    soseq.4 $e |- -. (/) e. A $.
    $( A linear ordering of sequences of ordinals. $)
    soseq $p |- S Or F $=
      ( va vb vp vq wor wpo cv wbr weq w3o wral df-so c0 csn cun sopo ax-mp
      poseq wcel wa wo wn cfv wceq con0 wrex eleq1 anbi1d fveq1 eqeq1d ralbidv
      breq1d anbi12d rexbidv anbi2d eqeq2d breq2d brabg bianabs wb ancoms
      orbi12d notbid wi sotrieq mpan wf cab feq2 cbvrexv abbii eqtri
      orderseqlem syl2an imbi2d visset feq1 elab2 bitri anbi12i reeanv bitr4i
      wel wss onss ssralv syl ad2antlr fveq2 eqeq12d rcla4v a1i cdm eleq2
      biimparc word eloni ordirr sylan ndmfv eqtr2 biimprd ex com23 fdm sylan2
      adantlr ffvelrn syl5 exp4b imp32 syldd imp mtoi syld ad2antrr eqtr
      biimpd expcom adantll jcad ordtri3or adantr jctird 3orel13 syl6 wfn
      eqfnfv ffn adantl sylibrd r19.23aivv sylbi wsb ax-17 sbie ralbii imbi1i
      tfisg sylbir sylbird ralinexa andi eqcom anbi1i orbi2i rexbii r19.43
      notbii syl5ibr sylbid orrd 3orcomb df-3or bitr2i sylib rgen2 mpbir2an )
      HEQHERMSZNSZETZMNUAZUVLUVKETZUBZNHUCMHUCMNHEUDABCDEFGHCUEUFUGZDQZUVQDRIUV
      QDUHUIJKUJUVPMNHHUVKHUKZUVLHUKZULZUVMUVOUMZUVNUMZUVPUWAUWBUVNUWAUWBUNBSZU
      VKUOZUWDUVLUOZUPZBASZUCZUWHUVKUOZUWHUVLUOZDTZULZAUQURZUWFUWEUPZBUWHUCZUWK
      UWJDTZULZAUQURZUMZUNZUVNUWAUWBUWTUWAUVMUWNUVOUWSUWAUVMUWNFSZHUKZGSZHUKZUL
      ZUWDUXBUOZUWDUXDUOZUPZBUWHUCZUWHUXBUOZUWHUXDUOZDTZULZAUQURZULZUVSUXEULZUW
      EUXHUPZBUWHUCZUWJUXLDTZULZAUQURZULUWAUWNULFGUVKUVLHHEFMUAZUXFUXQUXOUYBUYC
      UXCUVSUXEUXBUVKHUSUTUYCUXNUYAAUQUYCUXJUXSUXMUXTUYCUXIUXRBUWHUYCUXGUWEUXHU
      WDUXBUVKVAVBVCUYCUXKUWJUXLDUWHUXBUVKVAVDVEVFVEGNUAZUXQUWAUYBUWNUYDUXEUVTU
      VSUXDUVLHUSVGUYDUYAUWMAUQUYDUXSUWIUXTUWLUYDUXRUWGBUWHUYDUXHUWFUWEUWDUXDUV
      LVAVHVCUYDUXLUWKUWJDUWHUXDUVLVAVIVEVFVEKVJVKUVTUVSUVOUWSVLUVTUVSULZUVOUWS
      UXPUVTUXEULZUWFUXHUPZBUWHUCZUWKUXLDTZULZAUQURZULUYEUWSULFGUVLUVKHHEFNUAZU
      XFUYFUXOUYKUYLUXCUVTUXEUXBUVLHUSUTUYLUXNUYJAUQUYLUXJUYHUXMUYIUYLUXIUYGBUW
      HUYLUXGUWFUXHUWDUXBUVLVAVBVCUYLUXKUWKUXLDUWHUXBUVLVAVDVEVFVEGMUAZUYFUYEUY
      KUWSUYMUXEUVSUVTUXDUVKHUSVGUYMUYJUWRAUQUYMUYHUWPUYIUWQUYMUYGUWOBUWHUYMUXH
      UWEUWFUWDUXDUVKVAVHVCUYMUXLUWJUWKDUWHUXDUVKVAVIVEVFVEKVJVKVMVNVOUWAUWIUWL
      UWQUMZUNZVPZAUQUCZUVNUXAUWAUYQUWIUWJUWKUPZVPZAUQUCZUVNUWAUYSUYPAUQUWAUYRU
      YOUWIUWJUVQUKZUWKUVQUKZUYRUYOVLZUVSUVTUVRVUAVUBULVUCIUVQUWJUWKDVQVRBCFHUV
      KUWHHUWHCUXBVSZAUQURZFVTUWDCUXBVSZBUQURZFVTJVUEVUGFVUDVUFABUQUWHUWDCUXBWA
      WBWCWDZWEBCFHUVLUWHVUHWEWFWGVCUWAUYRAUQUCZUVNUYTUWAOSZCUVKVSZPSZCUVLVSZUL
      ZPUQUROUQURZVUIUVNVPZUWAVUKOUQURZVUMPUQURZULVUOUVSVUQUVTVURUVSUWHCUVKVSZA
      UQURZVUQVUEVUTFUVKHMWHUYCVUDVUSAUQUWHCUXBUVKWIVFJWJVUSVUKAOUQUWHVUJCUVKWA
      WBWKUVTUWHCUVLVSZAUQURZVURVUEVVBFUVLHNWHUYLVUDVVAAUQUWHCUXBUVLWIVFJWJVVAV
      UMAPUQUWHVULCUVLWAWBWKWLVUKVUMOPUQUQWMWNVUNVUPOPUQUQVUJUQUKZVULUQUKZULZVU
      NVUPVVEVUNULZVUIOPUAZUYRAVUJUCZULZUVNVVFVUIVVGVVHVVFVUIOPWOZUNZPOWOZUNZUL
      ZVVJVVGVVLUBZULVVGVVFVUIVVNVVOVVFVUIVVKVVMVVFVUIUYRAVULUCZVVKVVDVUIVVPVPZ
      VVCVUNVVDVULUQWPVVQVULWQUYRAVULUQWRWSWTVVFVVPVVKVVFVVPULVVJUECUKZLVVFVVPV
      VJVVRVPVVFVVJVVPVVRVVFVVJVVPVUJUVKUOZVUJUVLUOZUPZVVRVVJVVPVWAVPVPVVFUYRVW
      AAVUJVULAOUAUWJVVSUWKVVTUWHVUJUVKXAUWHVUJUVLXAXBXCXDVVEVUKVUMVVJVWAVVRVPZ
      VPVVEVUKVUMVVJVWBVVEVUKULVVTCUKZVWBVUMVVJULVVCVUKVWCVWBVPZVVDVVCUVKXEZVUJ
      UPZVWDVUKVVCVWFULZVWAVWCVVRVWGVVSUEUPZVWAVWCVVRVPZVPVWGVUJVWEUKZUNZVWHOOW
      OZUNZVWFVWKVVCVWFVWKVWMVWFVWJVWLVWEVUJVUJXFVOXGVVCVUJXHZVWMVUJXIZVUJXJWSX
      KVUJUVKXLWSVWHVWAVWIVWHVWAULUEVVTUPZVWIVVSUEVVTXMVWPVVRVWCUEVVTCUSXNWSXOW
      SXPVUJCUVKXQXRXSVULCVUJUVLXTYAYBYCYDXPYEYFXOYGVVFVUIVVHVVMVVCVUIVVHVPZVVD
      VUNVVCVUJUQWPVWQVUJWQUYRAVUJUQWRWSYHZVVFVVHVVMVVFVVHULVVLVVRLVVFVVHVVLVVR
      VPVVFVVLVVHVVRVVFVVLVVHVULUVKUOZVULUVLUOZUPZVVRVVLVVHVXAVPVPVVFUYRVXAAVUL
      VUJAPUAUWJVWSUWKVWTUWHVULUVKXAUWHVULUVLXAXBXCXDVVEVUKVUMVVLVXAVVRVPZVPZVV
      EVUMVUKVXCVVEVUMVUKVVLVXBVVEVUMULVWSCUKZVXBVUKVVLULVVEUVLXEZVULUPZVXDVXBV
      PZVUMVVDVXFVXGVVCVVDVXFULVWTUEUPZVXGPPWOZUNZVXFVXHVVDVXJVXFULVULVXEUKZUNZ
      VXHVXFVXLVXJVXFVXKVXIVXEVULVULXFVOXGVULUVLXLWSVVDVULXHZVXJVULXIZVULXJWSXK
      VXHVXAVXDVVRVXAVXHVXDVVRVPZVXAVXHULVWSUEUPZVXOVWSVWTUEYIVXPVXDVVRVWSUECUS
      YJWSYKXPWSYLVULCUVLXQXRVUJCVULUVKXTYAYBXPYCYDXPYEYFXOYGYMVVEVVOVUNVWNVXMV
      VOVVCVVDVUJVULYNVWOVXNWFYOYPVVNVVOVVGVVJVVGVVLYQYEYRVWRYMVUNUVNVVIVLZVVEU
      VKVUJYSUVLVULYSVXQVUKVUMAVUJVULUVKUVLYTVUJCUVKUUAVULCUVLUUAWFUUBUUCXOUUDU
      UEUYTUYRABUUFZBUWHUCZUYRVPZAUQUCVUIVXTUYSAUQVXSUWIUYRVXRUWGBUWHUYRUWGABUW
      GAUUGABUAUWJUWEUWKUWFUWHUWDUVKXAUWHUWDUVLXAXBUUHUUIUUJUUIUYRABUUKUULYAUUM
      UYQUWIUYNULZAUQURZUNUXAUWIUYNAUQUUNVYBUWTVYBUWMUWRUMZAUQURUWTVYAVYCAUQVYA
      UWMUWIUWQULZUMVYCUWIUWLUWQUUOVYDUWRUWMUWIUWPUWQUWGUWOBUWHUWEUWFUUPUUIUUQU
      URWKUUSUWMUWRAUQUUTWKUVAWKUVBUVCUVDUVPUVMUVOUVNUBUWCUVMUVNUVOUVEUVMUVOUVN
      UVFUVGUVHUVIUVJ $.
      $( [8-Jun-2011] $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Well-founded recursion
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A w x y z $.  $d F w x y z $.  $d G w x y z $.  $d H w x y z $.
    $d R w x y z $.
    $( Functions defined by well founded recursion are identical up to
       relation, domain, and characteristic function. $)
    wfr3g $p |- ( ( ( R We A /\ A. x e. A Pred ( R , A , x ) e. _V ) /\
                        ( F Fn A /\
                          A. y e. A ( F ` y ) =
                                    ( H ` ( F |` Pred ( R , A , y ) ) ) ) /\
                     ( G Fn A /\
                       A. y e. A ( G ` y ) =
                                 ( H ` ( G |` Pred ( R , A , y ) ) ) ) )
                   -> F = G ) $=
      ( vz vw wwe cv cpred cvv wcel wral wa wfn cfv cres wceq w3a wi weq fveq2
      eqeq12d imbi2d predeq3 reseq2 syl fveq2d anbi12d rcla4va wss wb predss
      fvreseq mpan2 biimpar eqcomd eqtr3 ancoms ex expimpd com12 exp3a com23
      imp3a a2d ax-17 ra5 syl5 wfis2g r19.21 sylib r19.26 sylan2br an4s 3impib
      eqid jctil eqfnfv ad2ant2r 3adant1 mpbird ) CDJCDAKLMNACOPZECQZBKZERZECDW
      GLZSZGRZTZBCOZPZFCQZWGFRZFWISZGRZTZBCOZPZUAZEFTZCCTZHKZERZXEFRZTZHCOZPZXB
      XIXDWEWNXAXIWNXAPWEXIWFWOWMWTWEXIUBZWFWOPZWLWSPZBCOZXKWMWTPWEXLXNPZXIWEXO
      XHUBZHCOXOXIUBXPXOIKZERZXQFRZTZUBZAHICDHIUCZXHXTXOYBXFXRXGXSXEXQEUDXEXQFU
      DUEUFXECNZXOXTICDXELZOZUBXPYAIYDOYCXOYEXHYCXLXNYEXHUBZYCXNXLYFYCXNXLYFUBZ
      YCXNPXFEYDSZGRZTZXGFYDSZGRZTZPZYGXMYNBXECBHUCZWLYJWSYMYOWHXFWKYIWGXEEUDYO
      WJYHGYOWIYDTZWJYHTCDWGXEUGZWIYDEUHUIUJUEYOWPXGWRYLWGXEFUDYOWQYKGYOYPWQYKT
      YQWIYDFUHUIUJUEUKULYNXLYEXHXLYEPZYNXHYRYLYITZYNXHUBYRYKYHGYRYHYKXLYHYKTZY
      EXLYDCUMYTYEUNCDXEUOICYDEFUPUQURUSUJYSYJYMXHYSYJPXFYLTZYMXHUBYJYSUUAXFYLY
      IUTVAUUAYMXHXFXGYLUTVBUIVCUIVDVEUIVBVFVGVHXOXTIYDXOIVIVJVKVLXOXHHCXOHVIVM
      VNVDWLWSBCVOVPVQVDVRCVSVTWNXAXCXJUNZWEWFWOUUBWMWTHCCEFWAWBWCWD $.
      $( [11-Feb-2011] $)
  $}

  ${
    $d A f g w x y z $.  $d G f g w x y z $.  $d R f g w x y z $.
    wfrlem1.1 $e |- B = { f |
                           E. x ( f Fn x /\
                                  ( x C_ A /\
                                    A. y e. x Pred ( R , A , y ) C_ x ) /\
                                  A. y e. x ( f ` y ) =
                                            ( G ` ( f |` Pred ( R , A , y ) ) )
                                ) } $.
    $( Lemma for well-founded recursion.  The final item we are interested in
       is the union of acceptable functions ` B ` .  This lemma just changes
       bound variables for later use. $)
    wfrlem1 $p |- B = { g |
                         E. z ( g Fn z /\
                                  ( z C_ A /\
                                    A. w e. z Pred ( R , A , w ) C_ z ) /\
                                  A. w e. z ( g ` w ) =
                                            ( G ` ( g |` Pred ( R , A , w ) ) )
                                ) } $=
      ( cv wfn wss cpred wral wa cfv cres wceq w3a wex cab weq fneq1 fveq1
      reseq1 fveq2d eqeq12d ralbidv 3anbi13d exbidv fneq2 sseq1 sseq2
      raleqbi1dv predeq3 sseq1d cbvralv syl6bb anbi12d raleq fveq2 reseq2 syl
      3anbi123d cbvexv cbvabv eqtri ) FHLZALZMZVKENZEGBLZOZVKNZBVKPZQZVNVJRZVJV
      OSZJRZTZBVKPZUAZAUBZHUCILZCLZMZWGENZEGDLZOZWGNZDWGPZQZWJWFRZWFWKSZJRZTZDW
      GPZUAZCUBZIUCKWEXAHIHIUDZWEWFVKMZVRVNWFRZWFVOSZJRZTZBVKPZUAZAUBXAXBWDXIAX
      BVLXCWCXHVRVKVJWFUEXBWBXGBVKXBVSXDWAXFVNVJWFUFXBVTXEJVJWFVOUGUHUIUJUKULXI
      WTACACUDZXCWHVRWNXHWSVKWGWFUMXJVMWIVQWMVKWGEUNXJVQVOWGNZBWGPWMVPXKBVKWGVK
      WGVOUOUPXKWLBDWGBDUDZVOWKWGEGVNWJUQZURUSUTVAXJXHXGBWGPWSXGBVKWGVBXGWRBDWG
      XLXDWOXFWQVNWJWFVCXLXEWPJXLVOWKTXEWPTXMVOWKWFVDVEUHUIUSUTVFVGUTVHVI $.
      $( [21-Apr-2011] $)

    $( Lemma for well-founded recursion.  An acceptable function is a
       function. $)
    wfrlem2 $p |- ( g e. B -> Fun g ) $=
      ( vz vw cv wcel wfn wss cpred wral wa cfv cres wceq w3a wex wfun wfrlem1
      abeq2i fnfun 3ad2ant1 19.23aiv sylbi ) GLZDMUKJLZNZULCOCEKLZPZULOKULQRZUN
      UKSUKUOTHSUAKULQZUBZJUCZUKUDZUSGDABJKCDEFGHIUEUFURUTJUMUPUTUQULUKUGUHUIUJ
      $.
      $( [21-Apr-2011] $)

    $( Lemma for well-founded recursion.  An acceptable function's domain is a
       subset of ` A ` . $)
    wfrlem3 $p |- ( g e. B -> dom g C_ A ) $=
      ( vz vw cv wcel wfn wss cpred wral wa cfv cres wceq w3a wex cdm wfrlem1
      abeq2i fndm sseq1d biimpar adantrr 3adant3 19.23aiv sylbi ) GLZDMUNJLZNZU
      OCOZCEKLZPZUOOKUOQZRZURUNSUNUSTHSUAKUOQZUBZJUCZUNUDZCOZVDGDABJKCDEFGHIUEU
      FVCVFJUPVAVFVBUPUQVFUTUPVFUQUPVEUOCUOUNUGUHUIUJUKULUM $.
      $( [21-Apr-2011] $)

  $}

  ${
    $d A a b c f g h x y $.  $d B a $.  $d G a b c f g h x y $.
    $d R a b c f g h x y $.
    wfrlem4.1 $e |- R We A $.
    wfrlem4.2 $e |- B = { f |
                           E. x ( f Fn x /\
                                  ( x C_ A /\
                                    A. y e. x Pred ( R , A , y ) C_ x ) /\
                                  A. y e. x ( f ` y ) =
                                            ( G ` ( f |` Pred ( R , A , y ) ) )
                                ) } $.
    $( Lemma for well-founded recursion.  Properties of the restriction of an
       acceptable function to the domain of another one. $)
    wfrlem4 $p |- ( ( g e. B /\ h e. B ) ->
                     ( ( g |` ( dom g i^i dom h ) ) Fn ( dom g i^i dom h ) /\
                       A. a e. ( dom g i^i dom h )
                        ( ( g |` ( dom g i^i dom h ) ) ` a ) =
                        ( G `
                          ( ( g |` ( dom g i^i dom h ) ) |`
                              Pred ( R , ( dom g i^i dom h ) , a ) ) ) ) ) $=
      ( vb vc cv wcel wa cdm cin cres wfn cfv cpred wceq wral wfun wfrlem2
      funfn sylib fnresin1 syl adantr wss w3a wex wi wfrlem1 abeq2i fndm
      raleqdv biimpar ra4 3adant2 19.23aiv sylbi inss1 sseli syl5 imp adantlr
      fvres adantl preddowncl 3an6 2exbii eeanv bitri ssinss1 ad2antrr hbra1
      hban wel syl5com inss2 anim12d ssin biimpi syl6com r19.21ai ad2ant2l jca
      wb ineqan12d sseq1 sseq2 raleqbi1dv anbi12d imbi2d mpbiri 3adant3
      19.23aivv sylbir syl2anb pm3.27 sylc predss sseqin2 mpbi syl5eq reseq2
      resres fveq2d 3eqtr4d r19.21aiva ) GOZDPZHOZDPZQZXOXORZXQRZSZTZYBUAZJOZYC
      UBZYCYBEYEUCZTZIUBZUDZJYBUEXPYDXRXPXOXTUAZYDXPXOUFYKABCDEFGILUGXOUHUIXTYA
      XOUJUKULXSYJJYBXSYEYBPZQZYEXOUBZXOCEYEUCZTZIUBZYFYIXPYLYNYQUDZXRXPYLYRXPY
      EXTPZYRYLXPXOMOZUAZYTCUMZYOYTUMZJYTUEZQZYRJYTUEZUNZMUOZYSYRUPZUUHGDABMJCD
      EFGILUQURZUUGUUIMUUAUUFUUIUUEUUAUUFQYRJXTUEZUUIUUAUUKUUFUUAYRJXTYTYTXOUSZ
      UTVAYRJXTVBUKVCVDVEYBXTYEXTYAVFVGVHVIVJYLYFYNUDXSYEYBXOVKVLYMYHYPIYMXOYBY
      GSZTZYPYHYMUUMYOUDUUNYPUDYMYGYOUUMYBCUMZYOYBUMZJYBUEZQZYLYGYOUDYMJCYBEYEV
      MXSUURYLUUHXQNOZUAZUUSCUMZYOUUSUMZJUUSUEZQZYEXQUBXQYOTIUBUDJUUSUEZUNZNUOZ
      UURXPXRUUHUVGQZUUAUUTQZUUEUVDQZUUFUVEQZUNZNUOMUOZUURUVMUUGUVFQZNUOMUOUVHU
      VLUVNMNUUAUUTUUEUVDUUFUVEVNVOUUGUVFMNVPVQUVLUURMNUVIUVJUURUVKUVIUVJUURUVI
      UVJUURUPZUVJYTUUSSZCUMZYOUVPUMZJUVPUEZQZUPZUVJUVQUVSUUBUVQUUDUVDYTUUSCVRV
      SUUDUVCUVSUUBUVAUUDUVCQZUVRJUVPUUDUVCJUUCJYTVTUVBJUUSVTWAYEUVPPZUWBUUCUVB
      QZUVRUWCUUDUUCUVCUVBUUDJMWBUUCUWCUUCJYTVBUVPYTYEYTUUSVFVGWCUVCJNWBUVBUWCU
      VBJUUSVBUVPUUSYEYTUUSWDVGWCWEUWDUVRYOYTUUSWFWGWHWIWJWKUVIYBUVPUDZUVOUWAWL
      UUAUUTXTYTYAUUSUULUUSXQUSWMUWEUURUVTUVJUWEUUOUVQUUQUVSYBUVPCWNUUPUVRJYBUV
      PYBUVPYOWOWPWQWRUKWSVIWTXAXBUUJUVGHDABNJCDEFHILUQURXCULXSYLXDXEYGYBUMUUMY
      GUDYBEYEXFYGYBXGXHXIUUMYOXOXJUKXOYBYGXKXIXLXMXNWK $.
      $( [21-Apr-2011] $)
  $}

  ${
    $d A a f g h x y $.  $d B a $.  $d G a f g h x y $.  $d R a f g h x y $.
    $d g h u v x $.
    wfrlem5.1 $e |- R We A $.
    wfrlem5.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    wfrlem5.3 $e |- B = { f |
                           E. x ( f Fn x /\
                                  ( x C_ A /\
                                    A. y e. x Pred ( R , A , y ) C_ x ) /\
                                  A. y e. x ( f ` y ) =
                                            ( G ` ( f |` Pred ( R , A , y ) ) )
                                ) } $.
    $( Lemma for well-founded recursion.  The values of two acceptable
       functions agree within their domains. $)
    wfrlem5 $p |- ( ( g e. B /\ h e. B ) ->
                     ( ( x g u /\ x h v ) -> u = v ) ) $=
      ( va cv wcel wa cdm cin cres wbr weq wi wfun wfrlem2 funres wal wrel
      dffun2 pm3.27bi ax-4 a4s syl 3syl adantr wwe cpred cvv wral wfn cfv wceq
      wfr3g wss wfrlem3 ssinss1 wess mpi setlikess mpan2 jca wfrlem4 ancom
      incom reseq2 ax-mp fneq1i fneq2i bitri eleq2i fveq1i reseq1 predeq2
      eqtri fveq2i eqeq12i imbi12i ralbii2 anbi12i 3imtr4i syl3anc breqd
      biimprd sylan2d visset breldm anim12i elin sylibr anandir brres bitr4i
      biimpi mpdan syl5 ) IPZFQZJPZFQZRZAPZDPZXGXGSZXISZTZUAZUBZXLCPZXIXPUAZUBZ
      RZDCUCZXLXMXGUBZXLXSXIUBZRZXKXRXLXSXQUBZYCYAXHXRYGRYCUDZXJXHXGUEXQUEZYHAB
      EFGHIKNUFXPXGUGYIYHCUHZDUHZAUHZYHYIXQUIYLADCXQUJUKYKYHAYJYHDYHCULUMUMUNUO
      UPXKYGYAXKXQXTXLXSXPGUQZXPGXLURUSQAXPUTZRZXQXPVAOPZXQVBXQXPGYPURZUAKVBVCO
      XPUTRXTXPVAZYPXTVBZXTYQUAZKVBZVCZOXPUTZRZXQXTVCXKAOXPGXQXTKVDXHYOXJXHXNEV
      EXPEVEZYOABEFGHIKNVFXNXOEVGUUEYMYNUUEEGUQYMLXPEGVHVIUUEEGXLURUSQAEUTYNMAX
      PEGVJVKVLUOUPABEFGHIJKOLNVMXJXHRXIXOXNTZUAZUUFVAZYPUUGVBZUUGUUFGYPURZUAZK
      VBZVCZOUUFUTZRXKUUDABEFGHJIKOLNVMXHXJVNYRUUHUUCUUNYRUUGXPVAUUHXPXTUUGXPUU
      FVCZXTUUGVCZXNXOVOZXPUUFXIVPVQZVRXPUUFUUGUUQVSVTUUBUUMOXPUUFYPXPQYPUUFQUU
      BUUMXPUUFYPUUQWAYSUUIUUAUULYPXTUUGUURWBYTUUKKYTUUGYQUAZUUKUUPYTUUSVCUURXT
      UUGYQWCVQYQUUJVCZUUSUUKVCUUOUUTUUQXPUUFGYPWDVQYQUUJUUGVPVQWEWFWGWHWIWJWKW
      LWMWNWOYFXLXPQZYBYFXLXNQZXLXOQZRUVAYDUVBYEUVCXLXMXGAWPZWQXLXSXIUVDWQWRXLX
      NXOWSWTYFUVARZYBUVEYDUVARZYEUVARZRYBYDYEUVAXAXRUVFYAUVGXLXMXGXPDWPXBXLXSX
      IXPCWPXBWJXCXDXEXF $.
      $( [21-Apr-2011] $)
  $}

  ${
    $d A f g w x y z $.  $d B g $.  $d G f g w x y z $.  $d R f g w x y z $.
    $d X g w z $.
    wfrlem6.1 $e |- B = { f |
                           E. x ( f Fn x /\
                                  ( x C_ A /\
                                    A. y e. x Pred ( R , A , y ) C_ x ) /\
                                  A. y e. x ( f ` y ) =
                                            ( G ` ( f |` Pred ( R , A , y ) ) )
                                ) } $.
    wfrlem6.2 $e |- F = U. B $.
    $( Lemma for well-founded recursion.  The union of all acceptable functions
       is a relationship. $)
    wfrlem6 $p |- Rel F $=
      ( vg cuni wceq wrel cv reluni wcel wfun wfrlem2 funrel syl mprgbir releq
      mpbiri ax-mp ) GDLZMZGNZJUGUHUFNZUIKOZNZKDKDPUJDQUJRUKABCDEFKHISUJTUAUBGU
      FUCUDUE $.
      $( [21-Apr-2011] $)

    $( Lemma for well-founded recursion.  The domain of ` F ` is a subclass of
       ` A ` . $)
    wfrlem7 $p |- dom F C_ A $=
      ( vg cdm cv ciun cuni dmeqi dmuni eqtri wss iunss wfrlem3 mprgbir
      eqsstri ) GLZKDKMLZNZCUDDOZLUFGUGJPKDQRUFCSUECSKDKDUECTABCDEFKHIUAUBUC $.
      $( [21-Apr-2011] $)

    $( Lemma for well-founded recursion.  Compute the prececessor class for an
       ` R ` minimal element of ` ( A \ dom F ) ` . $)
    wfrlem8 $p |- ( Pred ( R , ( A \ dom F ) , X ) = (/) <->
                   Pred ( R , A , X ) = Pred ( R , dom F , X ) ) $=
      ( cdm cdif cpred c0 wceq wss wa preddif eqeq1i ssdif0 wfrlem7 predpredss
      ax-mp biantru 3bitr2i eqss bitr4i ) CGLZMEINZOPZCEINZUIEINZQZUMULQZRZULUM
      PUKULUMMZOPUNUPUJUQOCUIEISTULUMUAUOUNUICQUOABCDEFGHJKUBUICEIUCUDUEUFULUMU
      GUH $.
      $( [21-Apr-2011] $)

    $( Lemma for well-founded recursion.  If ` X e. dom F ` , then its
       predecessor class is a subset of ` dom F ` . $)
    wfrlem9 $p |- ( X e. dom F -> Pred ( R , A , X ) C_ dom F ) $=
      ( vg vz vw cv cdm wcel wrex cpred ciun wss wfn wral wa cfv cres wceq w3a
      wex wi wfrlem1 abeq2i predeq3 sseq1d rcla4cv adantl wb fndm eleq2d
      sseq2d imbi12d adantr mpbird adantrl 3adant3 19.23aiv sylbi reximia
      ssiun syl cuni dmeqi dmuni eqtri eleq2i eliun bitri sseq2i 3imtr4i ) ILOZ
      PZQZLDRZCEISZLDWATZUAZIGPZQZWDWGUAWCWDWAUAZLDRWFWBWILDVTDQVTMOZUBZWJCUAZC
      ENOZSZWJUAZNWJUCZUDZWMVTUEVTWNUFHUEUGNWJUCZUHZMUIZWBWIUJZWTLDABMNCDEFLHJU
      KULWSXAMWKWQXAWRWKWPXAWLWKWPUDXAIWJQZWDWJUAZUJZWPXDWKWOXCNIWJWMIUGWNWDWJC
      EWMIUMUNUOUPWKXAXDUQWPWKWBXBWIXCWKWAWJIWJVTURZUSWKWAWJWDXEUTVAVBVCVDVEVFV
      GVHLDWAWDVIVJWHIWEQWCWGWEIWGDVKZPWEGXFKVLLDVMVNZVOLIDWAVPVQWGWEWDXGVRVS
      $.
      $( [21-Apr-2011] $)

  $}

  ${
    $d A f w x y z $.  $d F w $.  $d G f x y $.  $d R f w x y $.
    wfrlem10.1 $e |- R We A $.
    wfrlem10.2 $e |- B = { f |
                           E. x ( f Fn x /\
                                  ( x C_ A /\
                                    A. y e. x Pred ( R , A , y ) C_ x ) /\
                                  A. y e. x ( f ` y ) =
                                            ( G ` ( f |` Pred ( R , A , y ) ) )
                                ) } $.
    wfrlem10.3 $e |- F = U. B $.
    $( Lemma for well-founded recursion.  When ` z ` is an ` R ` minimal
       element of ` ( A \ dom F ) ` , then its predecessor class is equal to
       ` dom F ` . $)
    wfrlem10 $p |- ( ( z e. ( A \ dom F ) /\
                     Pred ( R , ( A \ dom F ) , z ) = (/) ) ->
                   Pred ( R , A , z ) = dom F ) $=
      ( vw cv cdm cdif wcel cpred c0 wceq wa wfrlem8 biimpi adantl wss predss
      a1i wi wbr cvv wb visset elpred ax-mp pm3.27 weq wn eleq1 biimprd eldifn
      syl6com con2d imp wfrlem9 ssel con3d syl5com adantr mpd elpredg ancoms
      eldifi sylan mtbid w3o wor wwe weso solin mpan wfrlem7 sseli syl2an
      ecase23d sylanbrc ex ssrdv eqssd eqtrd ) CNZDHOZPZQZWLFWJRSTZUAZDFWJRZWKF
      WJRZWKWNWPWQTZWMWNWRABDEFGHIWJKLUBUCUDWOWQWKWQWKUEWOWKFWJUFUGWOMWKWQWMMNZ
      WKQZWSWQQZUHWNWMWTXAXAWTWSWJFUIZWMWTUAZWJUJQXAWTXBUAUKCULWKUJFWJWSMULUMUN
      WMWTUOXCXBMCUPZWJWSFUIZWMWTXDUQWMXDWTXDWMWSWLQZWTUQXDXFWMWSWJWLURUSWSDWKU
      TVAVBVCXCWJDFWSRZQZXEXCXGWKUEZXHUQZWTXIWMABDEFGHIWSKLVDUDWMXIXJUHWTXIWJWK
      QZUQXJWMXIXHXKXGWKWJVEVFWJDWKUTVGVHVIWJDQZWTXHXEUKZWMWTXLXMDWKFWSWJVJVKWJ
      DWKVLZVMVNXLWSDQZXBXDXEVOZWMWTXOXLXPDFVPZXOXLUAXPDFVQXQJDFVRUNDWSWJFVSVTV
      KXNWKDWSABDEFGHIKLWAWBWCWDWEWFVHWGWHWI $.
      $( [21-Apr-2011] $)

  $}


  ${
    $d A f g h u v x y z $.  $d B g h $.  $d F u v x z $.  $d G f g h x y z $.
    $d R f g h x y z $.
    wfrlem11.1 $e |- R We A $.
    wfrlem11.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    wfrlem11.3 $e |- B = { f |
                           E. x ( f Fn x /\
                                  ( x C_ A /\
                                    A. y e. x Pred ( R , A , y ) C_ x ) /\
                                  A. y e. x ( f ` y ) =
                                            ( G ` ( f |` Pred ( R , A , y ) ) )
                                ) } $.
    wfrlem11.4 $e |- F = U. B $.
    $( Lemma for well-founded recursion.  The union of all acceptable functions
       is a function. $)
    wfrlem11 $p |- Fun F $=
      ( vu vv vg vh wfun wrel cv wbr wa weq wi wal dffun2 wfrlem6 wcel wex cop
      cuni eleq2i eluni bitri df-br anbi1i exbii 3bitr4i anbi12i eeanv bitr4i
      wfrlem5 impcom an4s 19.23aivv sylbi ax-gen gen2 mpbir2an ) GQGRASZMSZGTZV
      INSZGTZUAZMNUBZUCZNUDZMUDAUDAMNGUEABCDEFGHKLUFVQAMVPNVNVIVJOSZTZVRDUGZUAZ
      VIVLPSZTZWBDUGZUAZUAZPUHOUHZVOVNWAOUHZWEPUHZUAWGVKWHVMWIVIVJUIZGUGZWJVRUG
      ZVTUAZOUHZVKWHWKWJDUJZUGWNGWOWJLUKOWJDULUMVIVJGUNWAWMOVSWLVTVIVJVRUNUOUPU
      QVIVLUIZGUGZWPWBUGZWDUAZPUHZVMWIWQWPWOUGWTGWOWPLUKPWPDULUMVIVLGUNWEWSPWCW
      RWDVIVLWBUNUOUPUQURWAWEOPUSUTWFVOOPVSWCVTWDVOVTWDUAVSWCUAVOABNMCDEFOPHIJK
      VAVBVCVDVEVFVGVH $.
      $( [21-Apr-2011] $)


    ${
      $d F f $.
      $( Lemma for well-founded recursion.  Here, we compute the value of ` F `
         (the union of all acceptable functions). $)
      wfrlem12 $p |- ( y e. dom F ->
                    ( F ` y ) = ( G ` ( F |` Pred ( R , A , y ) ) ) ) $=
        ( vz cv cdm wcel cop wex cfv cpred cres wceq visset eldm2 wfn wss wral
        wa w3a cab cuni unieqi eqtri eleq2i eluniab bitri abeq2i elssuni
        syl6ssr sylbir wi wel fnop ex ra4 fndm sseq2d eleq2d anbi12d biimprd
        exp3a impcom wfun wfrlem11 funssfv 3adant3l fun2ssres 3adant3r fveq2d
        eqeq12d mp3an1 expcom com23 syl6com com34 sylcom adantl com14 syl7
        exp4a pm2.43d syld com12 3impd 19.23adv mpdi imp 19.23aiv sylbi ) BNZGO
        PWTMNZQZGPZMRWTGSZGCEWTTZUAZHSZUBZMWTGBUCUDXCXHMXCXBFNZPZXIANZUEZXKCUFZ
        XEXKUFZBXKUGZUHZWTXISZXIXEUAZHSZUBZBXKUGZUIZARZUHZFRZXHXCXBYCFUJZUKZPYE
        GYGXBGDUKZYGLDYFKULUMUNYCFXBUOUPYDXHFXJYCXHXJYCXIGUFZXHYCXIDPZYIYCFDKUQ
        YJXIYHGXIDURLUSUTXJYBYIXHVAZAXJXLXPYAYKXLXJXPYAYKVAVAZXLXJBAVBZYLXLXJYM
        XKWTXAXIVCVDXLYMYAXPYKXLYMYAXPYKVAZVAXLYMYMYAYNXLYMXTYNYMYAUHXPYMXTXLYK
        XOYMXTXLYKVAVAZVAXMXOYMXNYOXNBXKVEYMXNXLXTYKYMXNXLXTYKVAZXNXLUHYMXEXIOZ
        UFZWTYQPZUHZYPXLXNYMYTVAXLXNYMYTXLYTXNYMUHXLYRXNYSYMXLYQXKXEXKXIVFZVGXL
        YQXKWTUUAVHVIVJVKVLYTYIXTXHYIYTXTXHVAZGVMZYIYTUUBABCDEFGHIJKLVNUUCYIYTU
        IZXHXTUUDXDXQXGXSUUCYIYSXDXQUBYRWTGXIVOVPUUDXFXRHUUCYIYRXFXRUBYSXEGXIVQ
        VRVSVTVJWAWBWCWDVKWEWFWGWHYAYMXTXTBXKVEVLWIWJWKWEWLWMWNWOWPWQWRWSWRWS
        $.
        $( [21-Apr-2011] $)
    $}
  $}

  ${
    $d A f x y z $.  $d F f x y z $.  $d G f x y $.  $d R f x y z $.
    $d C f x y $.
    wfrlem13.1 $e |- R We A $.
    wfrlem13.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    wfrlem13.3 $e |- B = { f |
                           E. x ( f Fn x /\
                                  ( x C_ A /\
                                    A. y e. x Pred ( R , A , y ) C_ x ) /\
                                  A. y e. x ( f ` y ) =
                                           ( G ` ( f |` Pred ( R , A , y ) ) )
                                ) } $.
    wfrlem13.4 $e |- F = U. B $.
    wfrlem13.5 $e |- C = ( F u.
                      { <. z , ( G ` ( F |` Pred ( R , A , z ) ) ) >. } ) $.
    $( Lemma for well-founded recursion.  From here through ~ wfrlem16 , we aim
       to prove that ` dom F = A ` .  We do this by supposing that there is an
       element ` z ` of ` A ` that is not in ` dom F ` .  We then define ` C `
       by extending ` dom F ` with the appropriate value at ` z ` .  We then
       show that ` z ` cannot be an ` R ` minimal element of
       ` ( A \ dom F ) ` , meaning that ` ( A \ dom F ) ` must be empty, so
       ` dom A = F ` .  Here, we show that ` C ` is a function extending the
       domain of ` F ` by one. $)
    wfrlem13 $p |- ( z e. ( A \ dom F ) -> C Fn ( dom F u. { z } ) ) $=
      ( cv cdm cdif wcel cpred cres cfv cop csn cun wfun wceq wa wfn cin c0
      funun wfrlem11 visset fvex funsn pm3.2i wn eldifn disjsn sylibr dmsnop
      ineq2i syl5eq sylancr dmun uneq2i eqtri jctir fneq1i df-fn bitri ) CPZDIQ
      ZRSZIVMIDGVMTUAZJUBZUCUDZUEZUFZVSQZVNVMUDZUEZUGZUHZFWCUIZVOVTWDIUFZVRUFZU
      HVNVRQZUJZUKUGVTVOIVRULWGWHABDEGHIJKLMNUMVMVQCUNVPJUOUPUQVOVNWBUJZUKWJVOV
      MVNSURWKUKUGVMDVNUSVNVMUTVAWIWBVNVMVQVBZVCVDVEWAVNWIUEWCIVRVFWIWBVNWLVGVH
      VIWFVSWCUIWEWCFVSOVJVSWCVKVLVA $.
      $( [21-Apr-2011] $)


    $( Lemma for well-founded recursion.  Compute the value of ` C ` . $)
    wfrlem14 $p |- ( z e. ( A \ dom F ) ->
                     ( y e. ( dom F u. { z } ) ->
                       ( C ` y ) = ( G ` ( C |` Pred ( R , A , y ) ) ) ) ) $=
      ( cv cdm cdif wcel csn cun wfn cfv cpred cres wceq wi wfrlem13 weq wo wa
      wfun wb wss cop ssun1 sseqtr4i w3a funssfv fun2ssres wfrlem9 syl3an3
      fveq2d eqeq12d mp3an2 fnfun sylan wfrlem12 syl5bir ex pm2.43d fveq2
      predeq3 reseq2 syl ssun2 visset snid sselii c0 reseq1 ax-mp resundir
      eqtri wn wfr wwe wefr predfrirr fvex ressn0 uneq2i un0 3eqtri fveq2i
      opeq2i opex elsnc mpbir elun2 eleqtrri fnopfvb mpbiri mpan2 syl5cbir
      jaod elun elsn orbi2i bitri syl5ib ) CPZDIQZRSFXMXLTZUAZUBZBPZXOSZXQFUCZF
      DGXQUDZUEZJUCZUFZUGABCDEFGHIJKLMNOUHXPXQXMSZBCUIZUJZYCXRXPYDYCYEXPYDYCXPY
      DYDYCUGXPYDUKYCXQIUCZIXTUEZJUCZUFZYDFULZYDYCYJUMZXPYKIFUNZYDYLIIXLIDGXLUD
      ZUEZJUCZUOZTZUAZFIYRUPOUQYKYMYDURZXSYGYBYIXQFIUSYTYAYHJYKYMXTXMUNYAYHUFYD
      XTFIUTABDEGHIJXQMNVAVBVCVDVEXOFVFVGABDEGHIJKLMNVHVIVJVKYEYCXLFUCZFYNUEZJU
      CZUFZXPYEXSUUAYBUUCXQXLFVLYEYAUUBJYEXTYNUFYAUUBUFDGXQXLVMXTYNFVNVOVCVDXPX
      LXOSZUUDXNXOXLXNXMVPXLCVQZVRVSXPUUEUKUUDXLUUCUOZFSUUGYSFUUGYRSZUUGYSSUUHU
      UGYQUFUUCYPXLUUBYOJUUBYOYRYNUEZUAZYOVTUAYOUUBYSYNUEZUUJFYSUFUUBUUKUFOFYSY
      NWAWBIYRYNWCWDUUIVTYOXLYNSWEZUUIVTUFDGWFZUULDGWGUUMKDGWHWBDGXLWIWBYNXLYPU
      UFYOJWJWKWBWLYOWMWNWOWPUUGYQXLUUCWQWRWSUUGYRIWTWBOXAXOXLUUCFUUBJWJXBXCXDX
      EXFXRYDXQXNSZUJYFXQXMXNXGUUNYEYDBXLXHXIXJXKVO $.
      $( [21-Apr-2011] $)

    $( Lemma for well-founded recursion.  When ` z ` is ` R ` minimal, ` C ` is
       an acceptable function. $)
    wfrlem15 $p |- ( ( z e. ( A \ dom F ) /\
                       Pred ( R , ( A \ dom F ) , z ) = (/) ) ->
                     C e. B ) $=
      ( cv cdm cdif wcel cpred c0 wceq wa wfn wss wral cfv cres w3a wex csn
      cun cvv fneq2 sseq1 sseq2 raleqbi1dv anbi12d raleq 3anbi123d cla4egv
      unexg wfrlem10 setlikespec eldifi sylancl adantr eqeltrrd snex wfrlem13
      unss biimpi wfrlem7 snssd sylancr weq wo wi wfrlem9 ssun3 syl a1i
      predeq3 sseq1d ssun1 mpbiri syl5cbir jaod elun elsn orbi2i bitri syl5ib
      r19.21aiv jca wfrlem14 3jca sylc wb fnex mpan2 sylan2 sylanc fneq1 fveq1
      reseq1 fveq2d eqeq12d ralbidv 3anbi13d exbidv elab2g mpbird ) CPZDIQZRZSZ
      XPGXNTUAUBZUCZFESZFAPZUDZYADUEZDGBPZTZYAUEZBYAUFZUCZYDFUGZFYEUHZJUGZUBZBY
      AUFZUIZAUJZXOXNUKZULZUMSZFYQUDZYQDUEZYEYQUEZBYQUFZUCZYLBYQUFZUIZYOXSYNUUE
      AYQUMYAYQUBZYBYSYHUUCYMUUDYAYQFUNUUFYCYTYGUUBYAYQDUOYFUUABYAYQYAYQYEUPUQU
      RYLBYAYQUSUTVAXOUMSZYPUMSZYRXSXOYPUMUMVBZXSDGXNTZXOUMABCDEGHIJKMNVCZXQUUJ
      UMSZXRXNDSDGYATUMSADUFUULXQADGXNVDXNDXOVEZLVFVGVHZXNVIZVFXSYSUUCUUDXQYSXR
      ABCDEFGHIJKLMNOVJVGZXSYTUUBXQYTXRXODUEZYPDUEZYTXQUUQUURUCYTXOYPDVKVLABDEG
      HIJMNVMXQXNDUUMVNVOVGXSUUABYQXSYDXOSZBCVPZVQZUUAYDYQSZXSUUSUUAUUTUUSUUAVR
      XSUUSYEXOUEUUAABDEGHIJYDMNVSYEXOYPVTWAWBUUTUUAUUJYQUEZXSUUTYEUUJYQDGYDXNW
      CWDXSUVCXOYQUEXOYPWEXSUUJXOYQUUKWDWFWGWHUVBUUSYDYPSZVQUVAYDXOYPWIUVDUUTUU
      SBXNWJWKWLWMWNWOXQUUDXRXQYLBYQABCDEFGHIJKLMNOWPWNVGWQWRXSFUMSZXTYOWSYSUUG
      UVEXSYSYRUVEUUGYQUMFWTUUGUUHYRUUOUUIXAXBUUPUUNXCHPZYAUDZYHYDUVFUGZUVFYEUH
      ZJUGZUBZBYAUFZUIZAUJYOHFEUMUVFFUBZUVMYNAUVNUVGYBUVLYMYHYAUVFFXDUVNUVKYLBY
      AUVNUVHYIUVJYKYDUVFFXEUVNUVIYJJUVFFYEXFXGXHXIXJXKMXLWAXM $.
      $( [21-Apr-2011] $)

    $( Lemma for well-founded recursion.  If ` z ` is ` R ` minimal in
       ` ( A \ dom F ) ` , then ` C ` is acceptable and thus a subset of
       ` F ` , but ` dom C ` is bigger than ` dom F ` .  Thus, ` z ` cannot be
       minimal, so ` ( A \ dom F ) ` must be empty, and (due to ~ wfrlem7 ),
       ` dom F = A ` . $)
    wfrlem16 $p |- dom F = A $=
      ( cdm wfrlem7 wss cdif c0 wceq cv cpred wrex wcel eldifn wa csn cun
      ssun2 visset snid sselii cres cfv cop dmeqi dmun dmsnop uneq2i 3eqtri
      eleqtrri cuni wfrlem15 elssuni syl syl6ssr dmss sseld mpi mtand nrex wn
      wne df-ne difss tz6.26i mpan sylbir mt3 ssdif0 mpbir eqssi ) IPZDABDEGHIJ
      MNQDWDRDWDSZTUAZWFWEGCUBZUCTUAZCWEUDZWHCWEWGWEUEZWHWGWDUEZWGDWDUFWJWHUGZW
      GFPZUEWKWGWDWGUHZUIZWMWNWOWGWNWDUJWGCUKULUMWMIWGIDGWGUCUNJUOZUPUHZUIZPWDW
      QPZUIWOFWROUQIWQURWSWNWDWGWPUSUTVAVBWLWMWDWGWLFIRWMWDRWLFEVCZIWLFEUEFWTRA
      BCDEFGHIJKLMNOVDFEVEVFNVGFIVHVFVIVJVKVLWFVMWETVNZWIWETVOWEDRXAWIDWDVPACDW
      EGKLVQVRVSVTDWDWAWBWC $.
      $( [21-Apr-2011] $)

  $}

  ${
    $d A f x y z $.  $d F f x y z $.  $d G f x y $.  $d R f x y z $.
    wfr1.1 $e |- R We A $.
    wfr1.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    wfr1.3 $e |- B = { f |
                           E. x ( f Fn x /\
                                  ( x C_ A /\
                                    A. y e. x Pred ( R , A , y ) C_ x ) /\
                                  A. y e. x ( f ` y ) =
                                            ( G ` ( f |` Pred ( R , A , y ) ) )
                                ) } $.
    wfr1.4 $e |- F = U. B $.
    $( The Principle of Well-Founded Recursion, part 1 of 3.  We start with an
       arbitrary function ` G ` and a class of "acceptable" functions ` B ` .
       Then, using a base class ` A ` and a well-ordering ` R ` of ` A ` , we
       define a function ` F ` .  This function is said to be defined by
       "well-founded recursion."  The purpose of these three theorems is to
       demonstrate the properties of ` F ` .  We begin by showing that ` F ` is
       a function over ` A ` . $)
    wfr1 $p |- F Fn A $=
      ( vz wfn wfun cdm wceq df-fn wfrlem11 cv cpred cres cfv cop csn cun eqid
      wfrlem16 mpbir2an ) GCNGOGPCQGCRABCDEFGHIJKLSABMCDGMTZGCEUJUAUBHUCUDUEUFZ
      EFGHIJKLUKUGUHUI $.
      $( [22-Apr-2011] $)
  $}

  ${
    $d A f w x y $.  $d F f w x y $.  $d G f x y $.  $d R f w x y $.  $d y z $.
    wfr2.1 $e |- R We A $.
    wfr2.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    wfr2.3 $e |- B = { f |
                           E. x ( f Fn x /\
                                  ( x C_ A /\
                                    A. y e. x Pred ( R , A , y ) C_ x ) /\
                                  A. y e. x ( f ` y ) =
                                            ( G ` ( f |` Pred ( R , A , y ) ) )
                                ) } $.
    wfr2.4 $e |- F = U. B $.
    $( The Principle of Well-Founded Recursion, part 2 of 3.  Next, we show
       that the value of ` F ` at any ` z e. A ` is ` G ` recursively applied
       to all "previous" values of ` F ` . $)
    wfr2 $p |- ( z e. A ->
                  ( F ` z ) = ( G ` ( F |` Pred ( R , A , z ) ) ) ) $=
      ( vw cv cfv cpred cres wceq weq fveq2 predeq3 reseq2 syl fveq2d eqeq12d
      wcel cdm cop csn cun eqid wfrlem16 eleq2i wfrlem12 sylbir vtoclga ) BOZHP
      ZHDFURQZRZIPZSZCOZHPZHDFVDQZRZIPZSBVDDBCTZUSVEVBVHURVDHUAVIVAVGIVIUTVFSVA
      VGSDFURVDUBUTVFHUCUDUEUFURDUGURHUHZUGVCVJDURABNDEHNOZHDFVKQRIPUIUJUKZFGHI
      JKLMVLULUMUNABDEFGHIJKLMUOUPUQ $.
      $( [18-Apr-2011] $)

  $}

  ${
    $d A f x y z $.  $d F f x y z $.  $d G f x y z $.  $d H x z $.
    $d R f x y z $.
    wfr3.1 $e |- R We A $.
    wfr3.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
    wfr3.3 $e |- B = { f |
                           E. x ( f Fn x /\
                                  ( x C_ A /\
                                    A. y e. x Pred ( R , A , y ) C_ x ) /\
                                  A. y e. x ( f ` y ) =
                                            ( G ` ( f |` Pred ( R , A , y ) ) )
                                ) } $.
    wfr3.4 $e |- F = U. B $.
    $( The principle of Well-Founded Recursion, part 3 of 3.  Finally, we show
       that ` F ` is unique.  We do this by showing that any function ` H `
       with the same properties we proved of ` F ` in ~ wfr1 and ~ wfr2 is
       identical to ` F ` . $)
    wfr3 $p |- ( ( H Fn A /\
                    A. z e. A ( H ` z ) =
                            ( G ` ( H |` Pred ( R , A , z ) ) ) ) ->
                  F = H ) $=
      ( wwe cv cpred cvv wcel wral wa wfn cfv cres wceq pm3.2i wfr1 wfr2 rgen
      wfr3g mp3an12 ) DFOZDFAPQRSADTZUAHDUBZCPZHUCHDFUOQZUDIUCUEZCDTZUAJDUBUOJU
      CJUPUDIUCUECDTUAHJUEULUMKLUFUNURABDEFGHIKLMNUGUQCDABCDEFGHIKLMNUHUIUFACDF
      HJIUJUK $.
      $( [18-Apr-2011] $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Transfinite recursion via Well-founded recursion
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  ${
    $d x y $.
    $( Lemma for deriving transfinite recursion from well-founded recursion. $)
    tfrALTlem $p |- { f | E. x e. On ( f Fn x /\
                A. y e. x ( f ` y ) = ( G ` ( f |` y ) ) ) } =
                    { f |
                           E. x ( f Fn x /\
                                  ( x C_ On /\
                                    A. y e. x Pred ( _E , On , y ) C_ x ) /\
                                  A. y e. x ( f ` y ) =
                                          ( G ` ( f |` Pred ( _E , On , y ) ) )
                                ) } $=
      ( cv wfn cfv cres wceq wral wa con0 wrex wss cep cpred w3a wex wcel
      df-rex wel wb onelon predon reseq2 syl fveq2d eqeq2d pm5.74da ralbidv2
      pm5.32i word wtr wwe df-ord ordsson sylbir ex epweon wess mpi impbid1
      ancom 3bitr4i visset elon ssel2 sseq1d ralbidva dftr3 syl6bbr anbi1i
      bitr3i anbi2i an12 3anass exbii bitri abbii ) CEZAEZFZBEZVTGZVTWCHZDGZIZB
      WAJZKZALMZWBWALNZLOWCPZWANZBWAJZKZWDVTWLHZDGZIZBWAJZQZARZCWJWALSZWIKZARXA
      WIALTXCWTAWBXBWHKZKWBWOWSKZKXCWTXDXEWBXDXBWSKXEXBWSWHXBWRWGBWAWAXBBAUAZWR
      WGXBXFKWCLSZWRWGUBWAWCUCXGWQWFWDXGWPWEDXGWLWCIZWPWEIWCUDZWLWCVTUEUFUGUHUF
      UIUJUKXBWOWSWAULZWKWAUMZKZXBWOXKWAOUNZKZXKWKKXJXLXKXMWKXKXMWKXKXMWKXNXJWK
      WAUOZWAUPUQURWKLOUNXMUSWALOUTVAVBUKXOWKXKVCVDWAAVEVFWKWNXKWKWNWCWANZBWAJX
      KWKWMXPBWAWKXFKZWLWCWAXQXGXHWALWCVGXIUFVHVIBWAVJVKUKVDVLVMVNXBWBWHVOWBWOW
      SVPVDVQVRVS $.
      $( [22-Apr-2011] $)
  $}

  ${
    $d B w $.  $d F f w x y $.  $d G f w x y $.  $d y z $.
    tfrALT.1 $e |- A = { f | E. x e. On ( f Fn x /\
                A. y e. x ( f ` y ) = ( G ` ( f |` y ) ) ) } $.

    $( Let ` F ` be the union of all acceptable functions. $)
    tfrALT.2 $e |- F = U. A $.
    $( ~ tfr1 via well-founded recursion. $)
    tfr1ALT $p |- F Fn On $=
      ( con0 cep epweon epsetlike cv wfn cfv cres wceq wral wa wrex cab wss
      cpred w3a wex tfrALTlem eqtri wfr1 ) ABICJDEFKAILCDMZAMZNZBMZUIOZUIULPFOQ
      BUJRSAITDUAUKUJIUBIJULUCZUJUBBUJRSUMUIUNPFOQBUJRUDAUEDUAGABDFUFUGHUH $.
      $( [5-May-2004] $) $( [17-Aug-1994] $)

    $( ~ tfr2 via well-founded recursion. $)
    tfr2ALT $p |- ( z e. On -> ( F ` z ) = ( G ` ( F |` z ) ) ) $=
      ( cv con0 wcel cfv cep cpred cres epweon epsetlike wfn wceq wral wa wrex
      cab wss w3a wex tfrALTlem eqtri wfr2 predon reseq2 syl fveq2d eqtrd ) CJZ
      KLZUPFMFKNUPOZPZGMFUPPZGMABCKDNEFGQAKRDEJZAJZSZBJZVAMZVAVDPGMTBVBUAUBAKUC
      EUDVCVBKUEKNVDOZVBUEBVBUAUBVEVAVFPGMTBVBUAUFAUGEUDHABEGUHUIIUJUQUSUTGUQUR
      UPTUSUTTUPUKURUPFULUMUNUO $.
      $( [22-Apr-2011] $)

    ${
      $d B x $.
      $( ~ tfr3 via well-founded recursion. $)
      tfr3ALT $p |- ( ( B Fn On /\
               A. x e. On ( B ` x ) = ( G ` ( B |` x ) ) ) -> B = F ) $=
        ( vw con0 wfn cv cfv cep cpred cres wceq wral wa epweon epsetlike wrex
        cab wss w3a wex tfrALTlem eqtri wfr3 eqcomd weq fveq2 predeq3 reseq2
        syl fveq2d eqeq12d cbvralv wcel predon eqeq2d ralbiia bitri sylan2br )
        DKLZJMZDNZDKOVGPZQZGNZRZJKSZDFRAMZDNZDVNQZGNZRZAKSZVFVMTFDABJKCOEFGDUAA
        KUBCEMZVNLZBMZVTNZVTWBQGNRBVNSTAKUCEUDWAVNKUEKOWBPZVNUEBVNSTWCVTWDQGNRB
        VNSUFAUGEUDHABEGUHUIIUJUKVMVODKOVNPZQZGNZRZAKSVSVLWHJAKJAULZVHVOVKWGVGV
        NDUMWIVJWFGWIVIWERVJWFRKOVGVNUNVIWEDUOUPUQURUSWHVRAKVNKUTZWGVQVOWJWFVPG
        WJWEVNRWFVPRVNVAWEVNDUOUPUQVBVCVDVE $.
        $( [22-Apr-2011] $)
    $}
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Founded Recursion
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A w y z $.  $d A x $.  $d F w y z $.  $d G w y z $.  $d H w y z $.
    $d R w y z $.  $d R x $.  $d x z $.


    $( Functions defined by founded recursion are identical up to relation,
       domain, and characteristic function.  General version of frr3 $)
    frr3g $p |- ( ( ( R Fr A /\ A. x e. A Pred ( R , A , x ) e. _V ) /\
                     ( F Fn A /\
                       A. y e. A ( F ` y ) =
                                 ( y H ( F |` Pred ( R , A , y ) ) ) ) /\
                     ( G Fn A /\
                       A. y e. A ( G ` y ) =
                                 ( y H ( G |` Pred ( R , A , y ) ) ) ) )
                   -> F = G ) $=
      ( vz vw wfr cv cpred cvv wcel wral wa wfn cfv cres co wceq w3a wi weq
      fveq2 id predeq3 reseq2 syl opreq12d eqeq12d anbi12d rcla4va wss wb
      predss fvreseq mpan2 biimpar opreq2d eqcomd eqtr3 ex expimpd com12 exp3a
      com23 imp3a r19.26 anbi2i syl5ibr a2d ax-17 ra5 syl5 imbi2d frins2g ra4
      com3r an4s 3impib r19.21aiv eqid jctil eqfnfv ad2ant2r 3adant1 mpbird )
      CDJCDAKLMNACOPZECQZBKZERZWKECDWKLZSZGTZUAZBCOZPZFCQZWKFRZWKFWMSZGTZUAZBCO
      ZPZUBZEFUAZCCUAZHKZERZXIFRZUAZHCOZPZXFXMXHXFXLHCWIWRXEXICNZXLUCZWRXEPWIXP
      WJWSWQXDWIXPUCWIXOWJWSPZWQXDPZPZXLWIXSXLUCZHCOXOXTUCXTXSIKZERZYAFRZUAZUCZ
      AHICDXOXSYDICDXILZOZUCXTYEIYFOXOXSYGXLXOXQWPXCPZBCOZPYGXLUCZXSXOXQYIYJXOY
      IXQYJXOYIXQYJUCZXOYIPXJXIEYFSZGTZUAZXKXIFYFSZGTZUAZPZYKYHYRBXICBHUDZWPYNX
      CYQYSWLXJWOYMWKXIEUEYSWKXIWNYLGYSUFZYSWMYFUAZWNYLUACDWKXIUGZWMYFEUHUIUJUK
      YSWTXKXBYPWKXIFUEYSWKXIXAYOGYTYSUUAXAYOUAUUBWMYFFUHUIUJUKULUMYRXQYGXLXQYG
      PZYRXLUUCYPYMUAZYRXLUCUUCYMYPUUCYLYOXIGXQYLYOUAZYGXQYFCUNUUEYGUOCDXIUPICY
      FEFUQURUSUTVAUUDYNYQXLUUDYNPZXJYPUAZYQXLUCUUFYPXJYPXJYMVBVAUUGYQXLXJXKYPV
      BVCUIVDUIVEVFUIVCVGVHYIXRXQWPXCBCVIVJVKVLXSYDIYFXSIVMVNVOHIUDZXLYDXSUUHXJ
      YBXKYCXIYAEUEXIYAFUEUKVPVQXTHCVRUIVSVTVEWAWBCWCWDWRXEXGXNUOZWIWJWSUUIWQXD
      HCCEFWEWFWGWH $.
      $( [10-Feb-2011] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Surreal Numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Set up the new syntax for surreal numbers $)
  $c No <s bday $.
  $( Declare the class of all surreal numbers (see ~ df-no ). $)
  csur $a class No $.
  $( Declare the less than relationship over surreal numbers (see
     ~ df-slt ). $)
  cslt $a class <s $.
  $( Declare the birthday function for surreal numbers (see ~ df-bday ). $)
  cbday $a class bday $.

  ${
    $d f a $.
    $( Define the class of surreal numbers.  The surreal numbers are a proper
       class of numbers developed by John H. Conway and introduced by Donald
       Knuth in 1975.  They form a proper class into which all ordered fields
       can be embedded.  The approach we take to defining them was first
       introduced by Hary Goshnor, and is based on the conception of a "sign
       expansion" of a surreal number.  We define the surreals as
       ordinal-indexed sequences of ` 1o ` and ` 2o ` , analagous to Goshnor's
       ` ( - ) ` and ` ( + ) ` .

       After introducing this definition, we will abstract away from it using
       axioms that Norman Alling developed in "Foundations of Analysis over
       Surreal Number Fields."  This is done in a effort to be agnostic towards
       the exact implementation of surreals. $)
    df-no $a |- No = { f | E. a e. On f : a --> { 1o , 2o } } $.
  $}

  ${
    $d f g x y $.
    $( Next, we introduce surreal less-than, a comparison relationship over the
       surreals by lexicographically ordering them. $)
    df-slt $a |- <s = { <. f , g >. | ( ( f e. No /\ g e. No ) /\
                         E. x e. On (
                            A. y e. x ( f ` y ) = ( g ` y ) /\
                              ( f ` x ) { <. 1o , (/) >. ,
                                          <. 1o , 2o >. ,
                                          <. (/) , 2o >. } ( g ` x ) ) ) } $.
  $}

  $( Finally, we introduce the birthday function.  This function maps each
     surreal to an ordinal.  In our implementation, this is the domain of the
     sign function.  The important properties of this function are established
     later. $)
  df-bday $a |- bday = ( x e. No |-> dom x ) $.


  ${
    $d A f x $.
    $( Membership in the surreals. $)
    elno $p |- ( A e. No <-> E. x e. On A : x --> { 1o , 2o } ) $=
      ( vf csur wcel cvv cv c1o c2o cpr wf con0 wrex elisset wi visset fex
      mpan2 a1i r19.23aiv wceq feq1 rexbidv df-no elab2g pm5.21nii ) BDEBFEZAGZ
      HIJZBKZALMZBDNUJUGALUJUGOUHLEUJUHFEUGAPUHUIFBQRSTUHUICGZKZALMUKCBDFULBUAU
      MUJALUHUIULBUBUCCAUDUEUF $.
      $( [11-Jun-2011] $)
  $}

  ${
    $d A f g x y $.  $d B f g x y $.
    $( The value of the surreal less than relationship. $)
    sltval $p |- ( ( A e. No /\ B e. No ) ->
            ( A <s B <-> E. x e. On ( A. y e. x ( A ` y ) = ( B ` y ) /\
                         ( A ` x ) { <. 1o , (/) >. , <. 1o , 2o >. ,
                                     <. (/) , 2o >. } ( B ` x ) ) ) ) $=
      ( vf vg csur wcel wa cslt wbr cv cfv wceq wral c1o c0 cop c2o ctp con0
      wrex eleq1 anbi1d fveq1 eqeq1d ralbidv breq1d anbi12d rexbidv anbi2d
      eqeq2d breq2d df-slt brabg bianabs ) CGHZDGHZIZCDJKBLZCMZUTDMZNZBALZOZVDC
      MZVDDMZPQRPSRQSRTZKZIZAUAUBZELZGHZFLZGHZIZUTVLMZUTVNMZNZBVDOZVDVLMZVDVNMZ
      VHKZIZAUAUBZIUQVOIZVAVRNZBVDOZVFWBVHKZIZAUAUBZIUSVKIEFCDGGJVLCNZVPWFWEWKW
      LVMUQVOVLCGUCUDWLWDWJAUAWLVTWHWCWIWLVSWGBVDWLVQVAVRUTVLCUEUFUGWLWAVFWBVHV
      DVLCUEUHUIUJUIVNDNZWFUSWKVKWMVOURUQVNDGUCUKWMWJVJAUAWMWHVEWIVIWMWGVCBVDWM
      VRVBVAUTVNDUEULUGWMWBVGVFVHVDVNDUEUMUIUJUIABEFUNUOUP $.
      $( [10-Jul-2011] $) $( [14-Jun-2011] $)
  $}

  ${
    $d A x $.
    $( The value of the birthday function within the surreals. $)
    bdayval $p |- ( A e. No -> ( bday ` A ) = dom A ) $=
      ( vx csur wcel cdm cvv cbday cfv wceq dmexg cv dmeq df-bday fvmptg mpdan
      ) ACDAEZFDAGHPIACJBABKZEPCFGQALBMNO $.
      $( [10-Jul-2011] $) $( [14-Jun-2011] $)
  $}

  ${
    $d A x $.  $d X x $.
    noxpsgn.1 $e |- X e. { 1o , 2o } $.
    $( The cross product of an ordinal and the singleton of a sign is a
       surreal. $)
    noxpsgn $p |- ( A e. On -> ( A X. { X } ) e. No ) $=
      ( vx con0 wcel cv c1o c2o cpr csn cxp wf wrex csur wss elisseti fconst
      snss mpbi fss mp2an feq2 rcla4ev mpan2 elno sylibr ) AEFZDGZHIJZABKZLZMZD
      ENZULOFUHAUJULMZUNAUKULMUKUJPZUOABBUJCQZRBUJFUPCBUJUQSTAUKUJULUAUBUMUODAE
      UIAUJULUCUDUEDULUFUG $.
      $( [10-Jul-2011] $) $( [21-Jun-2011] $)
  $}

  $( The cross product of an ordinal and ` { 1o } ` is a surreal. $)
  noxp1o $p |- ( A e. On -> ( A X. { 1o } ) e. No ) $=
    ( c1o c2o con0 1on elisseti prid1 noxpsgn ) ABBCBDEFGH $.
    $( [10-Jul-2011] $) $( [12-Jun-2011] $)

  $( The cross product of an ordinal and ` { 2o } ` is a surreal. $)
  noxp2o $p |- ( A e. On -> ( A X. { 2o } ) e. No ) $=
    ( c2o c1o con0 2on elisseti prid2 noxpsgn ) ABCBBDEFGH $.
    $( [10-Jul-2011] $) $( [12-Jun-2011] $)

  ${
    $d A x $.
    $( A surreal is a function. $)
    nofun $p |- ( A e. No -> Fun A ) $=
      ( vx csur wcel cv c1o c2o cpr wf con0 wrex wfun elno wi ffun a1i
      r19.23aiv sylbi ) ACDBEZFGHZAIZBJKALZBAMUAUBBJUAUBNSJDSTAOPQR $.
      $( [10-Jul-2011] $) $( [16-Jun-2011] $)

    $( The domain of a surreal is an ordinal. $)
    nodmon $p |- ( A e. No -> dom A e. On ) $=
      ( vx csur wcel cv c1o c2o cpr wf con0 wrex cdm elno fdm eleq1d biimprcd
      r19.23aiv sylbi ) ACDBEZFGHZAIZBJKALZJDZBAMUAUCBJUAUCSJDUAUBSJSTANOPQR $.
      $( [10-Jul-2011] $) $( [16-Jun-2011] $)

    $( The range of a surreal is a subset of the surreal signs. $)
    norn $p |- ( A e. No -> ran A C_ { 1o , 2o } ) $=
      ( vx csur wcel cv c1o c2o cpr wf con0 wrex crn wss elno wi frn a1i
      r19.23aiv sylbi ) ACDBEZFGHZAIZBJKALUAMZBANUBUCBJUBUCOTJDTUAAPQRS $.
      $( [10-Jul-2011] $) $( [16-Jun-2011] $)
  $}

  $( The domain of a surreal has the ordinal property. $)
  nodmord $p |- ( A e. No -> Ord dom A ) $=
    ( csur wcel cdm con0 word nodmon eloni syl ) ABCADZECJFAGJHI $.
    $( [10-Jul-2011] $) $( [16-Jun-2011] $)

  ${
    $d A a x y $.  $d B a x y $.
    $( Alternate expression for surreal less than.  Two surreals obey surreal
       less than iff they obey the sign ordering at the first place they
       differ. $)
    sltval2 $p |- ( ( A e. No /\ B e. No ) ->
                     ( A <s B <->
                       ( A ` |^| { a e. On | ( A ` a ) =/= ( B ` a ) } )
                       { <. 1o , (/) >. , <. 1o , 2o >. , <. (/) , 2o >. }
                       ( B ` |^| { a e. On | ( A ` a ) =/= ( B ` a ) } )
                     ) ) $=
      ( vy vx csur wcel wa cslt wbr cv cfv wceq wral c1o c0 cop c2o ctp con0
      wrex wne crab cint sltval cvv w3o fvex 0ex 2on elisseti brtp wn 1n0
      df-ne mpbi eqeq1 mtbiri fvprc nsyl2 adantr 2on0 adantl 3jaoi sylbi
      onintrab sylib onelon expcom syl5 weq fveq2 eqeq12d necon3bid onnminsb
      com12 syld con2bii syl6ibr r19.21aiv jca ex impac anass raleq breq12d
      anbi12d rcla4ev syl wi elrab biimpri adantlr wss onint ssrab2 ne0i
      sylancr hbrab1 hbint ax-17 hbfv hbne elrabf pm3.27bi rcla4cv ad2antlr
      mtod wb ontri1 simpll oninton sylanc mpbird intss1 eqssd syldan eqeq12
      csuc 1on 0elon suc11 mp2an mpbir df-2o df-1o eqeq12i nemtbir eqcom
      syl6bb mtbi 3imtr4i sylan2 fveq2d biimpd pm2.43d expimpd r19.23aiv
      impbid1 bitr4d ) AFGBFGHZABIJDKZALZUUBBLZMZDEKZNZUUFALZUUFBLZOPQORQPRQSZJ
      ZHZETUAZCKZALZUUNBLZUBZCTUCZUDZALZUUSBLZUUJJZEDABUEUUAUVBUUMUUAUVBUUMUUAU
      VBHZUUSTGZUUEDUUSNZUVBHZHZUUMUVCUVDUVEHZUVBHUVGUUAUVBUVHUUAUVBUVHUVCUVDUV
      EUVBUVDUUAUVBUUSUFGZUVDUVBUUTOMZUVAPMZHZUVJUVARMZHZUUTPMZUVMHZUGUVIOPORPR
      UUTUVAUUSAUHUUSBUHUIRTUJUKZUVQULUVLUVIUVNUVPUVJUVIUVKUVJUVOUVIUVJUVOOPMZO
      PUBZUVRUMUNOPUOUPZUUTOPUQURUUSAUSUTZVAUVJUVIUVMUWAVAUVMUVIUVOUVMUVKUVIUVM
      UVKRPMZRPUBUWBUMVBRPUOUPZUVARPUQURUUSBUSUTVCVDVEUUQCVFVGVCZUVCUUEDUUSUVCU
      UBUUSGZUUCUUDUBZUMZUUEUWEUVCUWGUWEUVCUUBTGZUWGUWEUVDUWHUVCUVDUWEUWHUUSUUB
      VHVIUWDVJUWHUWEUWGUUQUWFCUUBCDVKZUUOUUPUUCUUDUWIUUOUUCUUPUUDUUNUUBAVLUUNU
      UBBVLVMVNVOVPVQVPUWFUUEUUCUUDUOVRVSVTWAWBWCUVDUVEUVBWDVGUULUVFEUUSTUUFUUS
      MZUUGUVEUUKUVBUUEDUUFUUSWEUWJUUHUUTUUIUVAUUJUUFUUSAVLUUFUUSBVLWFWGWHWIWBU
      ULUVBETUUFTGZUUGUUKUVBUWKUUGHZUUKUVBUWLUUKUUKUVBWJUWLUUKHZUUKUVBUWMUUHUUT
      UUIUVAUUJUWMUUFUUSAUWLUUHUUIUBZUWJUUKUWLUWNUUFUURGZUWJUWKUWNUWOUUGUWOUWKU
      WNHUUQUWNCUUFTCEVKZUUOUUPUUHUUIUWPUUOUUHUUPUUIUUNUUFAVLUUNUUFBVLVMVNWKWLW
      MUWLUWOHZUUFUUSUWQUUFUUSWNZUUSUUFGZUMZUWQUWSUUTUVAMZUWQUUTUVAUBZUXAUMUWQU
      USUURGZUXBUURTWNZUURPUBZUXCUWQUURWOUUQCTWPZUWOUXEUWLUURUUFWQZVCWRUXCUVDUX
      BUUQUXBCEUUSTCEUURUUQCETWSWTZUWKCXACEUUTUVACEUUSAUUFAGCXAUXHXBCEUUSBUUFBG
      CXAUXHXBXCUUNUUSMZUUOUUPUUTUVAUXIUUOUUTUUPUVAUUNUUSAVLUUNUUSBVLVMVNXDXEWI
      UUTUVAUOVGUUGUWSUXAWJUWKUWOUUEUXADUUSUUFUUBUUSMUUCUUTUUDUVAUUBUUSAVLUUBUU
      SBVLVMXFXGXHUWKUVDUWRUWTXIUWQUUFUUSXJUWKUUGUWOXKUWOUVDUWLUXDUXEUVDUWOUURX
      LUXFUXGWRVCXMXNUWOUUSUUFWNUWLUUFUURXOVCXPXQUUHOMZUUIPMHZUXJUUIRMZHZUUHPMU
      XLHZUGUUHUUIMZUMZUUKUWNUXKUXPUXMUXNUXKUXOUVRUVTUUHOUUIPXRURUXMUXOROMZUXQO
      XSZPXSZUXRUXSUBZUVSUNOTGZPTGZUXTUVSXIXTYAUYAUYBHUXRUXSOPOPYBVNYCYDRUXROUX
      SYEYFYGYHUXMUXOORMUXQUUHOUUIRXRORYIYJURUXNUXOPRMZUWBUYCUWCRPYIYKUUHPUUIRX
      RURVDOPORPRUUHUUIUUFAUHUUFBUHUIUVQUVQULUUHUUIUOYLYMZYNUWMUUFUUSBUYDYNWFYO
      WBYPYQYRYSYT $.
      $( [10-Jul-2011] $) $( [17-Jun-2011] $)
  $}

  ${
    $( The function value of a surreal is either a sign or the empty set. $)
    nofv $p |- ( A e. No -> ( ( A ` X ) = (/) \/ ( A ` X ) = 1o \/
                               ( A ` X ) = 2o ) ) $=
      ( csur wcel cfv c0 wceq c1o c2o wo w3o cdm wn pm2.1 wi ndmfv a1i wfun
      crn cpr wss wa ssel fvelrn syl5com ex com23 imp con0 1on elisseti 2on
      elpr2 syl6ib nofun norn sylanc orim12d mpi 3orass sylibr ) ACDZBAEZFGZVCH
      GZVCIGZJZJZVDVEVFKVBBALDZMZVIJVHVINVBVJVDVIVGVJVDOVBBAPQARZASZHITZUAZVIVG
      OVBVKVNUBVIVCVMDZVGVKVNVIVOOVKVIVNVOVKVIVNVOOVNVCVLDVOVKVIUBVLVMVCUCBAUDU
      EUFUGUHVCHIHUIUJUKIUIULUKUMUNAUOAUPUQURUSVDVEVFUTVA $.
      $( [10-Jul-2011] $) $( [22-Jun-2011] $)
  $}

  ${
    $( ` (/) ` is not a surreal sign. $)
    nosgnn0 $p |- -. (/) e. { 1o , 2o } $=
      ( c0 c1o c2o cpr wcel wceq wo wne wn 1n0 necom df-ne bitri mpbi csuc
      nsuceq0 df-2o neeq2i bitr4i pm3.2ni 0ex elpr mtbir ) ABCDEABFZACFZGUDUEBA
      HZUDIZJUFABHUGBAKABLMNACHZUEIBOZAHZUHBPUJAUIHUHUIAKCUIAQRSNACLNTABCUAUBUC
      $.
      $( [10-Jul-2011] $) $( [16-Jun-2011] $)
  $}

  ${
    nosgnn0i.1 $e |- X e. { 1o , 2o } $.
    $( If ` X ` is a surreal sign, then it is not null. $)
    nosgnn0i $p |- (/) =/= X $=
      ( c0 wne wceq wn c1o c2o cpr wcel nosgnn0 eleq1 mpbiri mto df-ne mpbir )
      CADCAEZFQCGHIZJZKQSARJBCARLMNCAOP $.
      $( [10-Sep-2011] $) $( [3-Aug-2011] $)
  $}

  ${
    $d A x y $.  $d B x y $.
    $( The restriction of a surreal to an ordinal is still a surreal. $)
    noreson $p |- ( ( A e. No /\ B e. On ) -> ( A |` B ) e. No ) $=
      ( vx vy cv c1o c2o cpr wf con0 wrex wcel wa cres csur wi an23 cin feq2
      rcla4ev onin adantr fresin adantl sylanc sylbi ex r19.23aiva imp elno
      anbi1i 3imtr4i ) CEZFGHZAIZCJKZBJLZMDEZUNABNZIZDJKZAOLZUQMUSOLUPUQVAUOUQV
      APCJUMJLZUOMZUQVAVDUQMVCUQMZUOMZVAVCUOUQQUMBRZJLZVGUNUSIZVAVFUTVIDVGJURVG
      UNUSSTVEVHUOUMBUAUBUOVIVEUMUNABUCUDUEUFUGUHUIVBUPUQCAUJUKDUSUJUL $.
      $( [10-Sep-2011] $) $( [4-Sep-2011] $)
  $}

  ${
    $d A k $.  $d B k $.

    $( If ` A <s B ` , then the sign of ` A ` at the first place they differ is
       either undefined or ` 1o ` $)
    sltsgn1 $p |- ( ( A e. No /\ B e. No ) ->
                     ( A <s B ->
                  ( ( A ` |^| { k e. On | ( A ` k ) =/= ( B ` k ) } ) = (/) \/
                    ( A ` |^| { k e. On | ( A ` k ) =/= ( B ` k ) } ) = 1o )
                    ) ) $=
      ( csur wcel wa cslt wbr cv cfv wne con0 crab cint c1o c0 cop c2o ctp
      wceq wo sltval2 w3o fvex 0ex 2on elisseti brtp olc adantr orc 3jaoi
      sylbi syl6bi ) ADEBDEFABGHCIZAJUOBJKCLMNZAJZUPBJZOPQORQPRQSHZUQPTZUQOTZUA
      ZABCUBUSVAURPTZFZVAURRTZFZUTVEFZUCVBOPORPRUQURUPAUDUPBUDUERLUFUGZVHUHVDVB
      VFVGVAVBVCVAUTUIZUJVAVBVEVIUJUTVBVEUTVAUKUJULUMUN $.
      $( [10-Sep-2011] $) $( [4-Sep-2011] $)

    $( If ` A <s B ` , then the sign of ` B ` at the first place they differ is
       either undefined or ` 2o ` $)
    sltsgn2 $p |- ( ( A e. No /\ B e. No ) ->
                     ( A <s B ->
                  ( ( B ` |^| { k e. On | ( A ` k ) =/= ( B ` k ) } ) = (/) \/
                    ( B ` |^| { k e. On | ( A ` k ) =/= ( B ` k ) } ) = 2o )
                    ) ) $=
      ( csur wcel wa cslt wbr cv cfv wne con0 crab cint c1o c0 cop c2o ctp
      wceq wo sltval2 w3o fvex 0ex 2on elisseti brtp orc adantl olc 3jaoi
      sylbi syl6bi ) ADEBDEFABGHCIZAJUOBJKCLMNZAJZUPBJZOPQORQPRQSHZURPTZURRTZUA
      ZABCUBUSUQOTZUTFZVCVAFZUQPTZVAFZUCVBOPORPRUQURUPAUDUPBUDUERLUFUGZVHUHVDVB
      VEVGUTVBVCUTVAUIUJVAVBVCVAUTUKZUJVAVBVFVIUJULUMUN $.
      $( [10-Sep-2011] $) $( [4-Sep-2011] $)
  $}

  ${
    $d A a $.  $d B a $.
    $( If ` A <s B ` , then the intersection of all the ordinals that have
       differing signs in ` A ` and ` B ` exists. $)
    sltintdifex $p |- ( ( A e. No /\ B e. No ) ->
       ( A <s B -> |^| { a e. On | ( A ` a ) =/= ( B ` a ) } e. _V ) ) $=
       ( csur wcel wa cslt wbr cv cfv wne con0 crab cint c1o c0 cop c2o ctp
       cvv sltval2 wceq w3o fvex 0ex 2on elisseti brtp wn fvprc 1n0 df-ne mpbi
       eqeq1 eqcom syl6bb mtbiri syl con4i adantr 2on0 adantl 3jaoi sylbi
       syl6bi ) ADEBDEFABGHCIZAJVFBJKCLMNZAJZVGBJZOPQORQPRQSHZVGTEZABCUAVJVHOUB
       ZVIPUBZFZVLVIRUBZFZVHPUBZVOFZUCVKOPORPRVHVIVGAUDVGBUDUERLUFUGZVSUHVNVKVP
       VRVLVKVMVKVLVKUIZVQVLUIVGAUJVQVLOPUBZOPKWAUIUKOPULUMVQVLPOUBWAVHPOUNPOUO
       UPUQURUSZUTVLVKVOWBUTVOVKVQVKVOVTVMVOUIVGBUJVMVORPUBZRPKWCUIVARPULUMVMVO
       PRUBWCVIPRUNPRUOUPUQURUSVBVCVDVE $.
       $( [22-Mar-2012] $) $( [22-Feb-2012] $)
  $}

  ${ $d x A $.
     $( An alternative condition for membership in ` No ` . $)
     elno2 $p |- ( A e. No <-> 
     	      ( Fun A /\ dom A e. On /\ ran A C_ { 1o , 2o } ) ) $=
       ( vx csur wcel wfun cdm con0 crn c1o c2o cpr wss w3a nofun nodmon norn 
       3jca cv wf wrex feq2 rcla4ev 3simp2 wfn wa wceq df-fn pm3.26 eqidd 
       sylanbrc anim1i 3impa df-f sylibr sylanc elno impbii ) ACDZAEZAFZGDZAHIJ
       KZLZMZURUSVAVCANAOAPQVDBRZVBASZBGTZURVAUTVBASZVGVDVFVHBUTGVEUTVBAUAUBUSV
       AVCUCVDAUTUDZVCUEZVHUSVAVCVJUSVAUEZVIVCVIUSUTUTUFVKAUTUGUSVAUHVKUTUIUJUK
       ULUTVBAUMUNUOBAUPUNUQ $.
       $( [22-Mar-2012] $) $( [21-Mar-2012] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Surreal Numbers: Ordering
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  ${
    $d x y z $.
    $( Lemma for ~ axsltso .  The sign expansion relationship totally orders
       the surreal signs. $)
    axsltsolem1 $p |- { <. 1o , (/) >. , <. 1o , 2o >. , <. (/) , 2o >. }
                      Or ( { 1o , 2o } u. { (/) } ) $=
      ( vx vy vz c1o c2o c0 ctp cop wor cpr csn cun cv wbr wn wcel wceq wa w3o
      wne 1n0 df-ne mpbi eqtr2 mto con0 wb 1on 0elon csuc suc11 df-2o df-1o
      eqeq12i syl5bb mp2an nemtbir ancoms nsuceq0 eqeq1i 3pm3.2ni visset 0ex
      2on elisseti brtp mtbir a1i wi w3a pm2.21i ad2ant2rl expcom 3mix2 ex
      3jaod ad2ant2lr 3jaoi imp anbi12i 3imtr4i weq eqtr3 3mix2d 3mix1d 3mix1
      3mix3d 3mix3 eltp biid 3orbi123i itlso df-tp soeq2 ax-mp ) DEFGZDFHDEHFEH
      GZIZDEJFKLZWQIZABCWPWQAMZXAWQNZOXAWPPZXBXADQZXAFQZRZXDXAEQZRZXEXGRZSXFXHX
      IXFDFQZDFTXJOUADFUBUCZXADFUDUEXHEDQZXLDFUADUFPZFUFPZXLXJUGUHUIXMXNRDUJZFU
      JZQXJXLDFUKEXODXPULUMUNUOUPUQZXGXDXLXAEDUDURUEXIEFQZXRXOFDUSEXOFULUTUQZXG
      XEXRXAEFUDURUEVADFDEFEXAXAAVBZXTVCEUFVDVEZYAVFVGVHXABMZWQNZYBCMZWQNZRZXAY
      DWQNZVIXCYBWPPZYDWPPVJXDYBFQZRZXDYBEQZRZXEYKRZSZYBDQZYDFQZRZYOYDEQZRZYIYR
      RZSZRXDYPRZXDYRRZXEYRRZSZYFYGYNUUAUUEYJUUAUUEVIYLYMYJYQUUEYSYTYQYJUUEYOYI
      UUEYPXDYOYIRZUUEUUFXJXKYBDFUDUEVKZVLVMYSYJUUEYOYIUUEYRXDUUGVLVMYJYTUUEXDY
      RUUEYIYIUUCUUBUUDVNVLVOVPYLYQUUEYSYTYLYQUUEYKYOUUEXDYPYKYORZUUEUUHXLXQYBE
      DUDUEVKZVQVOYLYSUUEYKYOUUEXDYRUUIVQVOYLYTUUEYKYIUUEXDYRYKYIRZUUEUUJXRXSYB
      EFUDUEVKZVQVOVPYMYQUUEYSYTYMYQUUEYKYOUUEXEYPUUIVQVOYMYSUUEYKYOUUEXEYRUUIV
      QVOYMYTUUEYKYIUUEXEYRUUKVQVOVPVRVSYCYNYEUUADFDEFEXAYBXTBVBZVCYAYAVFZDFDEF
      EYBYDUULCVBZVCYAYAVFVTDFDEFEXAYDXTUUNVCYAYAVFWAVHXDXGXESZYOYKYISZRYNABWBZ
      YOXERZYOXGRZYIXGRZSZSZXCYHRYCUUQYBXAWQNZSUUOUUPUVBXDUUPUVBVIXGXEXDYOUVBYK
      YIXDYOUVBXDYORUUQYNUVAXAYBDWCWDVOXDYKUVBYLYNUUQUVAYLYJYMVNWEVOXDYIUVBYJYN
      UUQUVAYJYLYMWFWEVOVPXGYOUVBYKYIYOXGUVBUUSUVAYNUUQUUSUURUUTVNWGVMXGYKUVBXG
      YKRUUQYNUVAXAYBEWCWDVOYIXGUVBUUTUVAYNUUQUUTUURUUSWHWGVMVPXEYOUVBYKYIYOXEU
      VBUURUVAYNUUQUURUUSUUTWFWGVMXEYKUVBYMYNUUQUVAYMYJYLWHWEVOXEYIUVBXEYIRUUQY
      NUVAXAYBFWCWDVOVPVRVSXCUUOYHUUPXADEFXTWIYBDEFUULWIVTYCYNUUQUUQUVCUVAUUMUU
      QWJDFDEFEYBXAUULXTVCYAYAVFWKWAWLWPWSQWRWTUGDEFWMWPWSWQWNWOUC $.
      $( [8-Jun-2011] $)
  $}

  ${
    $d f g x y $.
    $( Surreal less than totally orders the surreals.  Alling's axiom (O). $)
    axsltso $p |- <s Or No $=
      ( vx vy vf vg c1o c2o cpr c0 cop ctp cslt csur axsltsolem1 df-no df-slt
      nosgnn0 soseq ) ABEFGEHIEFIHFIJKCDLMCANABCDOPQ $.
      $( [9-Jun-2011] $)
  $}

  $( Surreal less than is irreflexive. $)
  sltirr $p |- ( A e. No -> -. A <s A ) $=
    ( csur cslt wor wcel wbr wn axsltso sonr mpan ) BCDABEAACFGHBACIJ $.
    $( [10-Jul-2011] $) $( [16-Jun-2011] $)

  $( Surreal less than is transitive. $)
  slttr $p |- ( ( A e. No /\ B e. No /\ C e. No ) ->
                ( ( A <s B /\ B <s C ) -> A <s C ) ) $=
    ( csur cslt wor wcel w3a wbr wa wi axsltso sotr mpan ) DEFADGBDGCDGHABEIBCE
    IJACEIKLDABCEMN $.
    $( [10-Jul-2011] $) $( [16-Jun-2011] $)

  $( Surreal less than is asymmetric. $)
  sltasym $p |- ( ( A e. No /\ B e. No ) -> ( A <s B -> -. B <s A ) ) $=
    ( csur wcel wa cslt wbr wn sltirr ad2antrr wi slttr 3anidm13 expdimp mtod
    ex ) ACDZBCDZEZABFGZBAFGZHSTEUAAAFGZQUBHRTAIJSTUAUBQRTUAEUBKABALMNOP $.
    $( [10-Jul-2011] $) $( [16-Jun-2011] $)

  $( Surreal less than obeys trichotomy. $)
  slttri $p |- ( ( A e. No /\ B e. No ) -> ( A <s B \/ A = B \/ B <s A ) ) $=
    ( csur cslt wor wcel wa wbr wceq w3o axsltso solin mpan ) CDEACFBCFGABDHABI
    BADHJKCABDLM $.
    $( [10-Jul-2011] $) $( [16-Jun-2011] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Surreal Numbers: Birthday Function
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  ${
    $d f x y $.
    $( The birthday function maps the surreals onto the ordinals.  Alling's
       axiom (B). $)
    axbday $p |- bday : No -onto-> On $=
      ( vf vx vy csur con0 cbday wfo wfn crn wceq df-fo cv cdm cvv wcel wral
      dmexg rgen df-bday mptfn mpbi wrex cab rnmpt c1o csn cxp dmeq eqeq2d
      rcla4ev noxp1o c0 wne 1on elisseti snnz dmxp ax-mp eqcomi sylancl c2o
      cpr wf wi elno weq wa eleq1 biimpcd eqtr3 eqcom sylanb syl5 exp3a fdm
      r19.23aiv sylbi impbii abbi2i eqtr4i mpbir2an ) DEFGFDHZFIZEJDEFKALZMZNOZ
      ADPWBWFADWDDQRADWEFASZTUAWCBLZWEJZADUBZBUCEABDWEFWGUDWJBEWHEOZWJWHUEUFZUG
      ZDOWHWMMZJZWJWKWIWOAWMDWDWMJWEWNWHWDWMUHUIUJWHUKWNWHWLULUMWNWHJUEUEEUNUOU
      PWHWLUQURUSUTWIWKADWDDOCLZUEVAVBZWDVCZCEUBWIWKVDZCWDVEWRWSCEWPEOZWEWPJZWS
      WRWTXAWIWKWTCBVFZWKXAWIVGXBWTWKWPWHEVHVIWPWEJWIXBXAWPWHWEVJWEWPVKVLVMVNWP
      WQWDVOVMVPVQVPVRVSVTWA $.
      $( [11-Jun-2011] $)

  $}

  $( The birthday function is a function. $)
  bdayfun $p |- Fun bday $=
    ( csur con0 cbday wfo wfun axbday fofun ax-mp ) ABCDCEFABCGH $.
    $( [10-Jul-2011] $) $( [14-Jun-2011] $)

  $( The birthday function's range is ` On ` $)
  bdayrn $p |- ran bday = On $=
    ( csur con0 cbday wfo crn wceq axbday forn ax-mp ) ABCDCEBFGABCHI $.
    $( [10-Jul-2011] $) $( [14-Jun-2011] $)

  $( The birthday function's domain is ` No ` $)
  bdaydm $p |- dom bday = No $=
    ( csur con0 cbday wf cdm wceq wfo axbday fof ax-mp fdm ) ABCDZCEAFABCGLHABC
    IJABCKJ $.
    $( [10-Jul-2011] $) $( [14-Jun-2011] $)

  $( The birthday function is a function over ` No ` $)
  bdayfn $p |- bday Fn No $=
    ( cbday csur wfn wfun cdm wceq df-fn bdayfun bdaydm mpbir2an ) ABCADAEBFABG
    HIJ $.
    $( [10-Jul-2011] $) $( [30-Jun-2011] $)

  $( The value of the birthday function is always an ordinal. $)
  bdayelon $p |- ( bday ` A ) e. On $=
    ( cbday cdm wcel cfv con0 wfun bdayfun wa crn fvelrn bdayrn syl6eleq mpan
    wn c0 ndmfv 0elon syl6eqel pm2.61i ) ABCDZABEZFDZBGZUAUCHUDUAIUBBJFABKLMNUA
    OUBPFABQRST $.
    $( [10-Jul-2011] $) $( [14-Jun-2011] $)

  $( The surreal numbers are a proper class. $)
  noprc $p |- -. No e. _V $=
    ( csur cvv wcel con0 onprc cbday wfo axbday fornex mpi mto ) ABCZDBCZELADFG
    MHADBFIJK $.
    $( [10-Jul-2011] $) $( [16-Jun-2011] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Surreal Numbers: Density
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Lemma for ~ axdense .  A surreal is a function over its birthday. $)
    axdenselem1 $p |- ( A e. No -> A Fn ( bday ` A ) ) $=
      ( cbday cfv wfn wfun cdm wceq csur wcel df-fn nofun bdayval eqcomd
      sylanbrc ) AABCZDAEAFZOGAHIZAOJAKQOPALMN $.
      $( [10-Jul-2011] $) $( [16-Jun-2011] $)
  $}

  ${
    $d A x $.
    $( Lemma for axfe (future) and ~ axdense .  The value of a surreal at its
       birthday is ` (/) ` $)
    axdenselem2 $p |- ( A e. No -> ( A ` ( bday ` A ) ) = (/) ) $=
      ( vx csur wcel cbday cfv cdm c0 bdayval fveq2d wn wceq cv c1o c2o cpr wf
      con0 wrex elno fdm eleq1d biimprd word eloni ordirr syl syl6com
      r19.23aiv sylbi ndmfv eqtrd ) ACDZAEFZAFAGZAFZHUMUNUOAAIJUMUOUODKZUPHLUMB
      MZNOPZAQZBRSUQBATUTUQBRUTURRDZUORDZUQUTVBVAUTUOURRURUSAUAUBUCVBUOUDUQUOUE
      UOUFUGUHUIUJUOAUKUGUL $.
      $( [10-Jul-2011] $) $( [14-Jun-2011] $)
  $}

  ${
    $d A a $.  $d B a $.
    $( Lemma for ~ axdense .  If one surreal is older than another, then there
       is an ordinal at which they are not equal. $)
    axdenselem3 $p |- ( ( A e. No /\ B e. No ) ->
                           ( ( bday ` A ) e. ( bday ` B ) ->
                             E. a e. On ( A ` a ) =/= ( B ` a ) ) ) $=
      ( csur wcel wa cbday cfv cv wne con0 wrex wceq fveq2 neeq1d neeq2d bitrd
      rcla4ev bdayelon c0 wi cdm bdayval eleq2d wfn crn c1o c2o cpr wss
      fnfvelrn ssel nosgnn0 eleq1 mtbiri necon2ai syl6com syl ex com23 wfun
      nofun funfn sylib norn sylc sylbid adantl imp necomd wb axdenselem2
      ad2antrr mpbird sylancr ) ADEZBDEZFZAGHZBGHZEZCIZAHZWBBHZJZCKLZVSKEVSAHZV
      SBHZJZWFVRWAFZWEWICVSKWBVSMZWEWGWDJWIWKWCWGWDWBVSANOWKWDWHWGWBVSBNPQRASWJ
      WITWHJZWJWHTVRWAWHTJZVQWAWMUAVPVQWAVSBUBZEZWMVQVTWNVSBUCUDBWNUEZBUFZUGUHU
      IZUJZWOWMUAVQWPWOWSWMWPWOWSWMUAZWPWOFWHWQEZWTWNVSBUKWSXAWHWREZWMWQWRWHULX
      BWHTWHTMXBTWREUMWHTWRUNUOUPUQURUSUTVQBVAWPBVBBVCVDBVEVFVGVHVIVJVPWIWLVKVQ
      WAVPWGTWHAVLOVMVNVOUS $.
      $( [10-Jul-2011] $) $( [16-Jun-2011] $)
  $}

  ${
    $d A a x $.  $d B a x $.
    $( Lemma for ~ axdense .  Show that a particular abstraction is an
       ordinal. $)
    axdenselem4 $p |- ( ( ( A e. No /\ B e. No ) /\ A <s B ) ->
                        |^| { a e. On | ( A ` a ) =/= ( B ` a ) } e. On ) $=
      ( csur wcel wa cslt wbr cv cfv wne con0 crab c0 cint wrex wceq wn wi
      breq2 biimprcd con3d sltirr syl5com adantr cbday wral wfn wb eqfnfv
      axdenselem1 syl2an notbid wo axdenselem3 necom rexbii syl6ib ancoms jaod
      word bdayelon eloni ax-mp ordtri3 mp2an con2bii syl5ibr rexnal wss onssi
      ssrexv df-ne sylibr sylbir a1i ianor syl5ib sylbid syld imp rabn0 ssrab2
      oninton mpan syl ) ADEZBDEZFZABGHZFZCIZAJZWLBJZKZCLMZNKZWPOLEZWKWOCLPZWQW
      IWJWSWIWJABQZRZWSWGWJXASWHWJAAGHZRXAWGWJWTXBWTXBWJABAGTUAUBAUCUDUEWIXAAUF
      JZBUFJZQZWMWNQZCXCUGZFZRZWSWIWTXHAXCUHBXDUHWTXHUIWGWHCXCXDABUJAUKBUKULUMW
      IXERZXGRZUNWSXIWIXJWSXKWIXCXDEZXDXCEZUNZWSXJWIXLWSXMABCUOWHWGXMWSSWHWGFXM
      WNWMKZCLPWSBACUOXOWOCLWNWMUPUQURUSUTXEXNXCVAZXDVAZXEXNRUIXCLEXPAVBZXCVCVD
      XDLEXQBVBXDVCVDXCXDVEVFVGVHXKWSSWIXKXFRZCXCPZWSXFCXCVIXTXSCLPZWSXCLVJXTYA
      SXCXRVKXSCXCLVLVDWOXSCLWMWNVMUQVNVOVPUTXEXGVQVRVSVTWAWOCLWBVNWPLVJWQWRWOC
      LWCWPWDWEWF $.
      $( [10-Jul-2011] $) $( [16-Jun-2011] $)
  $}

  ${
    $d A a x $.  $d B a x $.
    $( Lemma for ~ axdense .  If the birthdays of two distinct surreals are
       equal, then the ordinal from ~ axdenselem4 is an element of that
       birthday. $)
    axdenselem5 $p |- ( ( ( A e. No /\ B e. No ) /\
                            ( ( bday ` A ) = ( bday ` B ) /\ A <s B ) ) ->
                          |^| { a e. On | (
                                     A ` a ) =/= ( B ` a ) } e.
                          ( bday ` A ) ) $=
      ( vx csur wcel wa cbday cfv wceq cslt wbr cv wne con0 crab cint cdm wn
      breq2 notbid sltirr syl5cbi con2d imp ad2ant2rl wral wb wfun eqfunfv
      nofun syl2an adantr wi wrex word wss ordtr2 axdenselem4 eloni syl
      nodmord ad2antrr onelon nodmon sylan ex anim1d weq fveq2 neeq1d neeq2d
      bitrd elrab intss1 sylbir simprl syl2anc exp32 r19.23adv df-ne rexbii
      rexnal bitri syl5ibr imnan biimpri impcom syl5 exp4b com23 imp32 sylbid
      mpd bdayval eqeqan12d anbi1d eleq2d 3imtr4d ) AEFZBEFZGZAHIZBHIZJZABKLZGZ
      CMZAIZXHBIZNZCOPZQZXCFZXBARZBRZJZXFGZXMXOFZXGXNXBXRXSXBXRGZABJZSZXSWTXFYB
      XAXQWTXFYBWTYAXFYAAAKLZSXFSWTYAYCXFABAKTUAAUBUCUDUEUFXTYBXQDMZAIZYDBIZJZD
      XOUGZGZSZXSXBYBYJUHXRXBYAYIAUIBUIYAYIUHWTXADABUJAUKBUKULUAUMXBXQXFYJXSUNZ
      XBXFXQYKXBXFXQYJXSXBXFGZYHSZXSXQYJGYLYEYFNZDXOUOZXSYMYLYNXSDXOYLYDXOFZYNX
      SXMUPZXOUPZXMYDUQZYPXSYLYPYNGZGZYQYRGYSYPGXSXMYDXOURUEYLYQYTYLXMOFYQABCUS
      XMUTVAUMXBYRXFYTWTYRXAAVBUMVCUUAYDOFZYNGZYSYLYTUUCYLYPUUBYNWTYPUUBUNXAXFW
      TYPUUBXOOFYPUUBWTXOYDVDAVEVFVGVCVHUEUUCYDXLFYSXKYNCYDOCDVIZXKYEXJNYNUUDXI
      YEXJXHYDAVJVKUUDXJYFYEXHYDBVJVLVMVNYDXLVOVPVAYLYPYNVQVRVSVTYOYGSZDXOUOYMY
      NUUEDXOYEYFWAWBYGDXOWCWDWEYJXQYMXQYMUNYJXQYHWFWGWHWIWJWKWLWMWNVGXBXEXQXFW
      TXAXCXOXDXPAWOZBWOWPWQWTXNXSUHXAWTXCXOXMUUFWRUMWSUE $.
      $( [10-Jul-2011] $) $( [16-Jun-2011] $)
  $}

  ${
    $d A a x $.  $d B a x $.
    $( The restriction of a surreal to the abstraction from ~ axdenselem4 is
       still a surreal. $)
    axdenselem6 $p |- ( ( ( A e. No /\ B e. No ) /\
                        ( ( bday ` A ) = ( bday ` B ) /\ A <s B ) ) ->
                        ( A |` |^| { a e. On | (
                                     A ` a ) =/= ( B ` a ) } ) e. No ) $=
      ( vx csur wcel wa cbday cfv wceq cslt wbr cv c1o c2o cpr wne con0 crab
      cint cres wf wrex feq2 rcla4ev axdenselem4 adantrl wfn crn wss df-f
      fnssres axdenselem1 ad2antrr axdenselem5 bdayelon onelssi syl sylanc
      sstr resss rnss ax-mp norn sylancr sylanbrc elno sylibr ) AEFZBEFZGZAHIZB
      HIJZABKLZGZGZDMZNOPZACMZAIVSBIQCRSTZUAZUBZDRUCZWAEFVTRFZVTVRWAUBZWCVPWBWE
      DVTRVQVTVRWAUDUEVKVNWDVMABCUFUGWEWAVTUHZWAUIZVRUJZVPVTVRWAUKAVLUHZVTVLUJZ
      WFVPVLVTAULVIWIVJVOAUMUNVPVTVLFWJABCUOVLVTAUPUQURUSWGAUIZUJZWKVRUJZWHVPWG
      WKVRUTWAAUJWLAVTVAWAAVBVCVIWMVJVOAVDUNVEVFUSDWAVGVH $.
      $( [10-Jul-2011] $) $( [16-Jun-2011] $)
  $}

  ${
    $d A a $.  $d B a $.  $d C a $.
    $( Lemma for ~ axdense . ` A ` and ` B ` are equal at all elements of the
       abstraction. $)
    axdenselem7 $p |- ( ( ( A e. No /\ B e. No ) /\
                        ( ( bday ` A ) = ( bday ` B ) /\ A <s B ) ) ->
                        ( C e. |^| { a e. On | ( A ` a ) =/= ( B ` a ) }
                          -> ( A ` C ) = ( B ` C ) ) ) $=
      ( csur wcel wa cbday cfv wceq cslt wbr cv wne con0 crab cint wn wi
      axdenselem4 adantrl onelon ex syl wss sylan ontri1 con2bid biimpd com23
      imp mpd intss1 nsyl fveq2 neeq1d neeq2d bitrd elrab notbii syl6ib imnan
      syl6ibr mpdd df-ne con2bii ) AEFBEFGZAHIBHIJZABKLZGGZCDMZAIZVKBIZNZDOPZQZ
      FZCAIZCBIZNZRZVRVSJZVJVQCOFZWAVJVPOFZVQWCSVGVIWDVHABDTUAZWDVQWCVPCUBZUCUD
      VJVQWCVTGZRZWCWASVJVQCVOFZRZWHVJVQWJVJVQGZVPCUEZWIWKWCWLRZWDVQWCVJWFWEUFV
      JVQWCWMSZVJWDVQWNSWEWDWCVQWMWDWCVQWMSWDWCGZVQWMWOWLVQVPCUGUHUIUCUJUDUKULC
      VOUMUNUCWIWGVNVTDCOVKCJZVNVRVMNVTWPVLVRVMVKCAUOUPWPVMVSVRVKCBUOUQURUSUTVA
      WCVTVBVCVDVTWBVRVSVEVFVC $.
      $( [10-Jul-2011] $) $( [17-Jun-2011] $)
  $}


  ${
    $d A a $.  $d B a $.
    $( Lemma for ~ axdense .  Give a condition for surreal less than when two
       surreals have the same birthday. $)
    axdenselem8 $p |- ( ( A e. No /\ B e. No /\
                            ( bday ` A ) = ( bday ` B ) ) ->
                          ( A <s B <->
                            ( ( A `
                                |^| { a e. On | ( A ` a ) =/= ( B ` a ) } ) =
                              1o /\
                              ( B `
                                |^| { a e. On | ( A ` a ) =/= ( B ` a ) } ) =
                              2o ) ) ) $=
      ( csur wcel cbday cfv wceq w3a cslt wbr cv wne con0 crab cint c1o c2o wa
      wi axdenselem5 exp32 3impia c0 cop ctp wb sltval2 3adant3 w3o wn 3orel13
      eleq2 biimpd cpr nosgnn0 crn wfn eleq1 fnfvelrn syl5cbi axdenselem1
      sylan norn sseld adantr syld mtoi ex adantl syl9r imp intnand 3ad2antl1
      intnanrd sylanc com23 fvex 0ex 2on elisseti brtp syl5ib sylbid mpdd
      3mix2 sylibr syl5bir impbid ) ADEZBDEZAFGZBFGZHZIZABJKZCLZAGWQBGMCNOPZAGZ
      QHZWRBGZRHZSZWOWPWRWLEZXCWJWKWNWPXDTWJWKSZWNWPXDABCUAUBUCWOWPWSXAQUDUEQRU
      EUDRUEUFKZXDXCTZWJWKWPXFUGWNABCUHUIZWOWTXAUDHZSZXCWSUDHZXBSZUJZXGXFWOXDXM
      XCWOXDXMXCTZXJUKXLUKXNWOXDSZXJXCXLULXOXIWTWOXDXIUKZWJWKWNXDXPTWNXDWRWMEZX
      EXPWNXDXQWLWMWRUMUNWKXQXPTWJWKXQXPWKXQSZXIUDQRUOZEZUPXRXIUDBUQZEZXTBWMURZ
      XQXIYBTWKXIXAYAEYBYCXQSXAUDYAUSWMWRBUTVABVBVCWKYBXTTXQWKYAXSUDBVDVEVFVGVH
      VIVJVKUCVLVMXOXKXBWJWKXDXKUKWNWJXDSZXKXTUPYDXKUDAUQZEZXTAWLURZXDXKYFTWJXK
      WSYEEYFYGXDSWSUDYEUSWLWRAUTVAAVBVCWJYFXTTXDWJYEXSUDAVDVEVFVGVHVNVOVPVIVQQ
      UDQRUDRWSXAWRAVRWRBVRVSRNVTWAZYHWBZWCWDWEWOWPXFXCXHXCXMXFXCXJXLWFYIWGWHWI
      $.
      $( [10-Jul-2011] $) $( [19-Jun-2011] $)
  $}

  ${
    $d A a x y $.  $d B a x y $.
    $( Given two distinct surreals with the same birthday, there is an older
       surreal lying between the two of them.  Alling's axiom (SD) $)
    axdense $p |- ( ( ( A e. No /\ B e. No ) /\
                      ( ( bday ` A ) = ( bday ` B ) /\ A <s B ) ) ->
                    E. x e. No ( ( bday ` x ) e. ( bday ` A ) /\
                                 A <s x /\ x <s B ) ) $=
      ( va vy cv cfv wne con0 crab cint cres csur wcel cbday cslt wbr w3a wrex
      wa wceq fveq2 eleq1d breq2 breq1 3anbi123d rcla4ev axdenselem6 cdm
      bdayval syl cin wss axdenselem5 bdayelon onelssi ad2antrr sseqtrd df-ss
      sylib dmres syl5eq eqtrd eqeltrd wral c1o c0 cop c2o ctp raleq breq12d
      anbi12d axdenselem4 adantrl w3o wi axdenselem8 biimpd 3expia imp32
      pm3.26d eqid jctir 3mix1d fvex 0ex 2on elisseti brtp sylibr fveq2d
      axdenselem2 eqtr3d breqtrrd fvres eqcomd rgen jctil sylanc wb sltval
      simpll mpbird adantl axdenselem7 imp r19.21aiva pm3.27d 3mix3d eqbrtrd
      sylan32c simplr syl3an2c ) BDFZBGXOCGHDIJKZLZMNZXQOGZBOGZNZBXQPQZXQCPQZAF
      ZOGZXTNZBYDPQZYDCPQZRZAMSBMNZCMNZTZXTCOGUAZBCPQZTZTZYIYAYBYCRAXQMYDXQUAZY
      FYAYGYBYHYCYQYEXSXTYDXQOUBUCYDXQBPUDYDXQCPUEUFUGBCDUHZYPXSXPXTYPXSXQUIZXP
      YPXRXSYSUAYRXQUJUKYPXPBUIZULZXPYSYPXPYTUMUUAXPUAYPXPXTYTYPXPXTNXPXTUMBCDU
      NZXTXPBUOUPUKYJXTYTUAYKYOBUJUQURXPYTUSUTBXPVAVBVCZUUBVDYPYBEFZBGZUUDXQGZU
      AZEYDVEZYDBGZYDXQGZVFVGVHVFVIVHVGVIVHVJZQZTZAISZXPINZUUGEXPVEZXPBGZXPXQGZ
      UUKQZTZUUNYPUUMUUTAXPIYDXPUAZUUHUUPUULUUSUUGEYDXPVKUVAUUIUUQUUJUURUUKYDXP
      BUBYDXPXQUBZVLVMUGYLYNUUOYMBCDVNVOZYPUUSUUPYPUUQVGUURUUKYPUUQVFUAZVGVGUAZ
      TZUVDVGVIUAZTZUUQVGUAUVGTZVPUUQVGUUKQYPUVFUVHUVIYPUVDUVEYPUVDXPCGZVIUAZYL
      YMYNUVDUVKTZYJYKYMYNUVLVQYJYKYMRYNUVLBCDVRVSVTWAZWBVGWCZWDWEVFVGVFVIVGVIU
      UQVGXPBWFWGWGVIIWHWIZUVOWJWKYPXSXQGZUURVGYPXSXPXQUUCWLYPXRUVPVGUAYRXQWMUK
      WNZWOUUGEXPUUDXPNZUUFUUEUUDXPBWPWQZWRWSWTYJXRYBUUNXAYPAEBXQXBYJYKYOXCYRWT
      XDYPYCUUFUUDCGZUAZEYDVEZUUJYDCGZUUKQZTZAISZUUOUWAEXPVEZUURUVJUUKQZUWFYPUV
      CYPUWAEXPYPUVRTUUEUUFUVTUVRUUGYPUVSXEYPUVRUUEUVTUABCUUDDXFXGWNXHYPUURVGUV
      JUUKUVQYPVGVFUAZUVJVGUATZUWIUVKTZUVEUVKTZVPVGUVJUUKQYPUWLUWJUWKYPUVKUVEYP
      UVDUVKUVMXIUVNWSXJVFVGVFVIVGVIVGUVJWGXPCWFWGUVOUVOWJWKXKUWEUWGUWHTAXPIUVA
      UWBUWGUWDUWHUWAEYDXPVKUVAUUJUURUWCUVJUUKUVBYDXPCUBVLVMUGXLXRYKYCUWFXAYPAE
      XQCXBYRYJYKYOXMWTXDXN $.
      $( [10-Jul-2011] $) $( [16-Jun-2011] $)
  $}

  ${
    $d A w x y z $.  $d X w x y z $.  $d Y w y z $.
    $( Lemma for ~ nocvxmin .  Given two birthday-minimal elements of a convex
       class of surreals, they are not comparable. $)
    nocvxminlem $p |- ( ( A C_ No /\ A. x e. A A. y e. A
                           A. z e. No ( ( x <s z /\ z <s y ) -> z e. A ) ) ->
                         ( ( ( X e. A /\ Y e. A ) /\
                             ( ( bday ` X ) = |^| ( bday " A ) /\
                               ( bday ` Y ) = |^| ( bday " A ) ) ) ->
                           -. X <s Y ) ) $=
      ( vw csur wss cv cslt wbr wa wcel wi wral cbday cfv cima cint wceq wn
      w3a wrex breq1 anbi1d imbi1d ralbidv breq2 anbi2d rcla42v weq anbi12d
      eleq1 imbi12d rcla4v cdm bdaydm sseq2i wfun bdayfun funfvima2 mpan
      sylbir imp intss1 syl con0 wb ontri1 c0 wne oninton crn imassrn bdayrn
      sseqtri ne0i sylancr bdayelon sylancl mpbid ex eleq2 notbid biimprcd
      syl6 com3l adantrd syl8 com35 com4l impcom imp42 con2d 3anass notbii
      imnan bitr4i sylibr nrexdv axdense anassrs ssel anim12d eqtr3 anim12i
      anasss adantlr sylan mtand ) DHIZAJZCJZKLZXNBJZKLZMZXNDNZOZCHPZBDPADPZMZE
      DNZFDNZMZEQRZQDSZTZUAZFQRZYIUAZMZMZEFKLZUBYCYNMZYOGJZQRZYGNZEYQKLZYQFKLZU
      CZGHUDZYPUUBGHYPYQHNZMZYSYTUUAMZUBOZUUBUBZUUEUUFYSYCYFYMUUDUUFYSUBZOZYBXL
      YFYMUUDUUJOOZOYFYBXLUUKYFYBEXNKLZXNFKLZMZXSOZCHPZXLUUKOYAUUPUULXQMZXSOZCH
      PABEFDDXMEUAZXTUURCHUUSXRUUQXSUUSXOUULXQXMEXNKUEUFUGUHXPFUAZUURUUOCHUUTUU
      QUUNXSUUTXQUUMUULXPFXNKUIUJUGUHUKUUDUUPXLYMUUJUUDUUPUUFYMXLUUIUUDUUPUUFYQ
      DNZYMXLUUIOZOUUOUUFUVAOCYQHCGULZUUNUUFXSUVAUVCUULYTUUMUUAXNYQEKUIXNYQFKUE
      UMXNYQDUNUOUPUVAYJUVBYLXLUVAYJUUIXLUVAYRYINZUBZYJUUIOXLUVAUVEXLUVAMZYIYRI
      ZUVEUVFYRYHNZUVGXLUVAUVHXLDQUQZIZUVAUVHOZUVIHDURUSQUTUVJUVKVADYQQVBVCVDVE
      ZYRYHVFVGYIVHNZYRVHNUVGUVEVIUVFYIYRVJYHVHIYHVKVLZUVMUVFYHVMYHQVNVHQDVOVPV
      QUVFUVHUVNUVLYHYRVRVGVSYQVTWAWBWCYJUUIUVEYJYSUVDYGYIYRWDWEWFWGWHWIWJWKWLW
      GWHWMWNWOUUHYSUUFMZUBUUGUUBUVOYSYTUUAWPWQYSUUFWRWSWTXAEHNZFHNZMZYGYKUAZMZ
      YOUUCYPUVRUVSYOUUCGEFXBXCXLYNUVTYBXLYFYMUVTXLYFMUVRYMUVSXLYFUVRXLYDUVPYEU
      VQDHEXDDHFXDXEVEYGYKYIXFXGXHXIXJXKWC $.
      $( [10-Jul-2011] $) $( [30-Jun-2011] $)

  $}

  ${
    $d A t w x y z $.
    $( Given a non-empty convex class of surreals, there is a unique
       birthday-minimal element of that class. $)
    nocvxmin $p |- ( ( A =/= (/) /\ A C_ No /\
                        A. x e. A A. y e. A
                           A. z e. No ( ( x <s z /\ z <s y ) -> z e. A ) ) ->
                      E! w e. A ( bday ` w ) = |^| ( bday " A ) ) $=
      ( vt cv cbday cfv cima cint wceq wreu wrex wa weq wi wral c0 wne csur
      wss cslt wbr wcel w3a fveq2 eqeq1d reu4 con0 onint crn imassrn bdayrn
      sseqtri wex cdm bdaydm sseq2i wfun bdayfun funfvima2 mpan sylbir fvex
      eleq1 cla4ev syl6 19.23adv n0 3imtr4g impcom sylancr wb wfn bdayfn
      fvelimab adantl mpbid 3adant3 wn ssel anim12d imp ad2ant2r nocvxminlem
      ancom anbi12i syl5ib wor axsltso sotrieq2 biimpar sylan32c exp32
      r19.21aivv 3adant1 sylanbrc ) DGZHIZHEJZKZLZDEMXCDENZXCFGZHIZXBLZOZDFPZQZ
      FERDERZESTZEUAUBZAGZCGZUCUDXOBGUCUDOXOEUEQCUARBERAERZUFXCXGDFEXIWTXFXBWSX
      EHUGUHUIXLXMXDXPXLXMOZXBXAUEZXDXAUJUBXASTZXRXQXAUKXAHULUJHEUMUNUOXMXLXSXM
      XNEUEZAUPWSXAUEZDUPZXLXSXMXTYBAXMXTXNHIZXAUEZYBXMEHUQZUBZXTYDQZYEUAEURUSH
      UTYFYGVAEXNHVBVCVDYAYDDYCXNHVEWSYCXAVFVGVHVIAEVJDXAVJVKVLVMXMXRXDVNZXLHUA
      VOXMYHVPDUAEXBHVQVCVRVSVTXMXPXKXLXMXPOZXJDFEEYIWSEUEZXEEUEZOZXHXIWSUAUEZX
      EUAUEZOZWSXEUCUDWAZXEWSUCUDWAZXIYIYLXHOZOXMYLYOXPXHXMYLYOXMYJYMYKYNEUAWSW
      BEUAXEWBWCWDWEYIYRYPABCEWSXEWFWDYIYRYQYIYKYJOZXGXCOZOYQYRABCEXEWSWFYLYSXH
      YTYJYKWGXCXGWGWHWIWDYOXIYPYQOZUAUCWJYOXIUUAVNWKUAWSXEUCWLVCWMWNWOWPWQWR
      $.
      $( [10-Jul-2011] $) $( [30-Jun-2011] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Surreal Numbers: Full-Eta Property
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  $( Lemma for axfe (future) .  The successor of the union of the image of the
     birthday function under a set is an ordinal. $)
  axfelem0 $p |- ( A e. B -> suc U. ( bday " A ) e. On ) $=
    ( wcel cbday cima cuni word cvv wa csuc con0 wfun bdayfun funimaexg mpan
    uniexg syl wss crn imassrn bdayrn sseqtri ssorduni ax-mp jctil elon2
    sucelon bitr3i sylib ) ABCZDAEZFZGZULHCZIZULJKCZUJUNUMUJUKHCZUNDLUJUQMDABNO
    UKHPQUKKRUMUKDSKDATUAUBUKUCUDUEUOULKCUPULUFULUGUHUI $.
    $( [10-Sep-2011] $) $( [20-Aug-2011] $)

  ${
    $d F a b n $.  $d X a b $.
    axfelem1.1 $e |- X e. { 1o , 2o } $.
    axfelem1.2 $e |- C = |^| { a e. On |
                                A. n e. F E. b e. a ( n ` b ) =/= X } $.
    $( Lemma for axfe (future) .  Show a particular abstraction is an
       ordinal. $)
    axfelem1 $p |- ( ( F C_ No /\ F e. A ) -> C e. On ) $=
      ( csur wss wcel wa cv cfv wne wrex wral con0 crab cint cbday cima cuni
      csuc wceq rexeq ralbidv rcla4ev axfelem0 fveq2 neeq1d cdm wfun wi
      bdayfun funfvima mpan ssel2 bdaydm syl6eleqr pm3.27 sylc elssuni syl
      word wb bdayelon crn imassrn bdayrn sseqtri ssorduni ax-mp ordsssuc
      mp2an sylib c0 nosgnn0i axdenselem2 mpbiri sylanc r19.21aiva syl2an
      ancoms onintrab2 syl5eqel ) DJKZDALZMZGNZCNZOZEPZGFNZQZCDRZFSTUAZSBWJWQFS
      QZWRSLWIWHWSUBDUCZUDZUEZSLWNGXBQZCDRZWSWIWHWQXDFXBSWOXBUFWPXCCDWNGWOXBUGU
      HUIDAUJWHXCCDWLUBOZXBLZXEWLOZEPZXCWHWLDLZMZWNXHGXEXBWKXEUFWMXGEWKXEWLUKUL
      UIXJXEXAKZXFXJXEWTLZXKWLUBUMZLZXIXLXJUBUNXNXIXLUOUPDWLUBUQURXJWLJXMDJWLUS
      ZUTVAWHXIVBVCXEWTVDVEXESLXAVFZXKXFVGWLVHWTSKXPWTUBVISUBDVJVKVLWTVMVNXEXAV
      OVPVQXJXHVREPEHVSXJXGVREXJWLJLXGVRUFXOWLVTVEULWAWBWCWDWEWQFWFVQIWG $.
      $( [10-Sep-2011] $) $( [17-Aug-2011] $)

    $( Lemma for axfe (future) .  Calculate the birthday of
       ` ( C X. { X } ) ` . $)
    axfelem2 $p |- ( ( F C_ No /\ F e. A ) ->
                       ( bday ` ( C X. { X } ) ) = C ) $=
      ( csur wss wcel wa csn cxp cbday cfv cdm con0 wceq axfelem1 noxpsgn
      bdayval 3syl c0 wne c1o c2o cpr elisseti snnz dmxp ax-mp syl6eq ) DJKDALM
      ZBENZOZPQZUQRZBUOBSLUQJLURUSTABCDEFGHIUABEHUBUQUCUDUPUEUFUSBTEEUGUHUIHUJU
      KBUPULUMUN $.
      $( [10-Sep-2011] $) $( [17-Aug-2011] $)

  $}

  ${
    $d A x y $.  $d X x y $.
    axfelem3.1 $e |- X e. { 1o , 2o } $.
    $( Lemma for axfe (future) .  The infimum of the class of all ordinals such
       that ` A ` is not ` X ` is an ordinal. $)
    axfelem3 $p |- ( A e. No ->
                        |^| { x e. On | ( A ` x ) =/= X } e. On ) $=
      ( csur wcel cv cfv wne con0 wrex crab cint cbday wceq fveq2 neeq1d
      rcla4ev bdayelon c0 nosgnn0i axdenselem2 mpbiri sylancr onintrab2 sylib
      ) BEFZAGZBHZCIZAJKZUJAJLMJFBNHZJFULBHZCIZUKUGUJUNAULJUHULOUIUMCUHULBPQRBS
      UGUNTCICDUAUGUMTCBUBQUCUDUJAUEUF $.
      $( [10-Sep-2011] $) $( [17-Aug-2011] $)

    $( Lemma for axfe (future) .  There is always a minimal value of a surreal
       that is not a given sign. $)
    axfelem4 $p |- ( A e. No ->
                      ( A ` |^| { x e. On | ( A ` x ) =/= X } ) =/= X ) $=
      ( vy csur wcel cv cfv wne con0 crab cint wa wss c0 onint ssrab2 cbday
      nosgnn0i axdenselem2 neeq1d mpbiri wb bdayelon wceq fveq2 elrab3 ax-mp
      sylibr ne0i syl sylancr hbrab1 hbint ax-17 hbfv hbne elrabf sylib
      pm3.27d ) BFGZAHZBIZCJZAKLZMZKGZVGBIZCJZVBVGVFGZVHVJNVFKOVFPJZVKVBVFQVEAK
      RVBBSIZVFGZVLVBVMBIZCJZVNVBVPPCJCDTVBVOPCBUAUBUCVMKGVNVPUDBUEVEVPAVMKVCVM
      UFVDVOCVCVMBUGUBUHUIUJVFVMUKULUMVEVJAEVGKAEVFVEAEKUNUOZEHZKGAUPAEVICAEVGB
      VRBGAUPVQUQVRCGAUPURVCVGUFVDVICVCVGBUGUBUSUTVA $.
      $( [10-Sep-2011] $) $( [3-Aug-2011] $)
  $}

  ${
    $d A a b x $.  $d F a b $.  $d X a b x $.  $d X n $.  $d a b n $.
    $d A n $.  $d F n $.
    axfelem5.1 $e |- X e. { 1o , 2o } $.
    axfelem5.2 $e |- C = |^| { a e. On |
                                A. n e. F E. b e. a ( n ` b ) =/= X } $.
    $( Lemma for axfe (future) .  Given an element ` A ` of ` F ` , then the
       first position where it differs from ` X ` is strictly less than
       ` C ` $)
    axfelem5 $p |- ( ( F C_ No /\ A e. F ) ->
                     |^| { x e. On | ( A ` x ) =/= X } e. C ) $=
      ( csur wss wcel wa cv cfv wne con0 crab cint wrex wral wi elintrabg
      biimpar cbday wceq fveq2 neeq1d rcla4ev bdayelon ssel2 c0 nosgnn0i
      axdenselem2 mpbiri syl sylancr onintrab2 sylib fveq1 rexbidv rcla4v
      ad2antlr wel ontr2 imp ad2antrr simplr onelon anim1i anasss weq elrab
      intss1 sylbir adantll simprl syl2anc exp32 r19.23adv syld r19.21aiva
      sylanc syl6eleqr ) EKLZBEMZNZAOZBPZFQZARSZTZHOZDOZPZFQZHGOZUAZDEUBZGRSTZC
      WMRMZWTWMWRMZUCZGRUBZWMXAMZWHXBXFXEWTGWMRRUDUEWHWKARUAZXBBUFPZRMXHBPZFQZX
      GWHWKXJAXHRWIXHUGWJXIFWIXHBUHUIUJBUKWHBKMZXJEKBULXKXJUMFQFIUNXKXIUMFBUOUI
      UPUQURWKAUSUTZWHXDGRWHWRRMZNZWTWNBPZFQZHWRUAZXCWGWTXQUCWFXMWSXQDBEWOBUGZW
      QXPHWRXRWPXOFWNWOBVAUIVBVCVDXNXPXCHWRXNHGVEZXPXCXBXMWMWNLZXSXCXNXSXPNZNXB
      XMNXTXSNXCWMWNWRVFVGWHXBXMYAXLVHWHXMYAVIXMYAXTWHXMYANWNRMZXPNZXTXMXSXPYCX
      MXSNYBXPWRWNVJVKVLYCWNWLMXTWKXPAWNRAHVMWJXOFWIWNBUHUIVNWNWLVOVPUQVQXNXSXP
      VRVSVTWAWBWCWDJWE $.
      $( [10-Sep-2011] $) $( [3-Aug-2011] $)
  $}

  ${
    $d A a b x $.  $d F a b $.  $d X a b x $.  $d a b n $.  $d A n $.
    $d F n $.  $d X n $.
    axfelem6.1 $e |- X e. { 1o , 2o } $.
    axfelem6.2 $e |- C = |^| { a e. On |
                                A. n e. F E. b e. a ( n ` b ) =/= X } $.
    $( Lemma for axfe (future) .  Calculate the value of ` ( C X. { X } ) ` at
       the minimal ordinal whose value is different from ` X ` . $)
    axfelem6 $p |- ( ( F C_ No /\ A e. F ) ->
                      ( ( C X. { X } ) ` |^| { x e. On | ( A ` x ) =/= X } ) =
                      X ) $=
      ( csur wss wcel wa cv cfv wne con0 crab cint csn cxp wceq axfelem5 c1o
      c2o cpr elisseti fvconst2 syl ) EKLBEMNAOBPFQARSTZCMUKCFUAUBPFUCABCDEFGHI
      JUDCFUKFUEUFUGIUHUIUJ $.
      $( [10-Sep-2011] $) $( [3-Aug-2011] $)
  $}

  ${
    $d F a b n $.  $d S a b $.  $d X a b n $.
    axfelem7.1 $e |- S e. { 1o , 2o } $.
    axfelem7.2 $e |- C = |^| { a e. On |
                                A. n e. F E. b e. a ( n ` b ) =/= S } $.
    $( Lemma for axfe (future) .  Bound the birthday of ` ( C X. { X } ) `
       above. $)
    axfelem7 $p |- ( ( ( F C_ No /\ F e. A ) /\
                          ( X e. On /\ A. n e. F ( bday ` n ) e. X ) ) ->
                        ( bday ` ( C X. { S } ) ) C_ X ) $=
      ( csur wss wcel wa con0 cv cbday cfv wral csn cxp wne wrex crab cint wi
      ssel2 c0 nosgnn0i axdenselem2 neeq1d mpbiri syl wceq fveq2 rcla4ev
      expcom ralimdvaa anim2d rexeq ralbidv elrab intss1 sylbir syl6 imp
      syl5ss adantlr wb axfelem2 sseq1d adantr mpbird ) EKLZEAMZNZFOMZDPZQRZFMZ
      DESZNZNBCTUAQRZFLZBFLZVNWBWEVOVNWBNHPZVRRZCUBZHGPZUCZDESZGOUDZUEZFBVNWBWM
      FLZVNWBVQWHHFUCZDESZNZWNVNWAWPVQVNVTWODEVNVREMNZVSVRRZCUBZVTWOUFWRVRKMZWT
      EKVRUGXAWTUHCUBCIUIXAWSUHCVRUJUKULUMVTWTWOWHWTHVSFWFVSUNWGWSCWFVSVRUOUKUP
      UQUMURUSWQFWLMWNWKWPGFOWIFUNWJWODEWHHWIFUTVAVBFWLVCVDVEVFJVGVHVPWDWEVIWBV
      PWCBFABDECGHIJVJVKVLVM $.
      $( [10-Sep-2011] $) $( [17-Aug-2011] $)
  $}

  ${
    $d L a b c d k n $.  $d A d x $.  $d a n x z $.  $d b x $.  $d b z $.
    $d c x $.  $d k x $.  $d L x $.  $d L z $.  $d R n $.  $d R y $.  $d R z $.
    $d X a $.  $d X b $.  $d X n $.  $d X z $.

    $( Lemma for axfe (future) .  The full statement of the axiom when ` R ` is
       empty. $)
    axfelem8 $p |- ( R = (/) ->
                      ( ( ( ( L C_ No /\ R C_ No ) /\ ( L e. A /\ R e. B ) ) /\
                          ( X e. On /\ A. n e. ( L u. R ) ( bday ` n ) e. X )
        /\
                          A. x e. L A. y e. R x <s y ) ->
                        E. z e. No ( ( bday ` z ) C_ X /\
                                     A. x e. L x <s z /\
                                     A. y e. R z <s y ) ) ) $=
      ( vb va vd vc vk c0 wceq csur wss wa wcel con0 cv cbday cfv cun wral
      cslt wbr w3a wrex wi c2o wne crab cint csn cxp c1o 2on elisseti prid2
      eqid axfelem1 noxp2o syl adantr axfelem7 cop ctp ssel2 adantlr axfelem3
      wn wb ontri1 onss sseld imp sylanc biimpd con2d ex pm2.43d intss1 nsyl
      weq fveq2 neeq1d elrab3 biimprd df-ne syl5ibr mt3d onelss axfelem5 sylc
      fvconst2 eqtr4d r19.21aiva w3o wo 3orel3 axfelem4 bnj1540 nofv orcom
      sylib jctir andir olcd 3orass sylibr fvex 0ex brtp axfelem6 breqtrrd
      raleq breq12d anbi12d rcla4ev sylan32c sltval biimpar sylan31c sseq1d
      breq2 ralbidv ad2ant2r 3adant3 uneq2 un0 syl6eq raleqdv anbi2d 3anbi2d
      3anbi3d df-3an ral0 mpbiran2 syl6bb rexbidv imbi12d mpbiri ) FOPZHQRZFQRZ
      SHDTZFETZSSZIUATZGUBZUCUDITZGHFUEZUFZSZAUBZBUBZUGUHBFUFAHUFZUIZCUBZUCUDZI
      RZUUQUVAUGUHZAHUFZUVAUURUGUHZBFUFZUIZCQUJZUKUUJUUKUUMGHUFZSZUUSUIZUVCUVES
      ZCQUJZUKUUJUVKUVNUUSUUJUVKUVNUUFUUHUVKUVNUKUUGUUIUUFUUHSZUVKUVNJUBUULUDUL
      UMJKUBUJGHUFKUAUNUOZULUPUQZQTZUVQUCUDZIRZUUQUVQUGUHZAHUFZUVNUVOUVKSUVOUVR
      UVKUVOUVPUATZUVRDUVPGHULKJURULULUAUSUTZVAZUVPVBZVCZUVPVDVEZVFDUVPULGHIKJU
      WEUWFVGUVOUWBUVKUVOUWAAHUUQQTZUVRLUBZUUQUDZUWJUVQUDZPZLMUBZUFZUWNUUQUDZUW
      NUVQUDZUROVHURULVHOULVHVIZUHZSZMUAUJZUWAUVOUUQHTZSZUUFUXBUWIUUHHQUUQVJVKZ
      UVOUVRUXBUWHVFNUBZUUQUDZULUMZNUAUNZUOZUATZUWMLUXIUFZUXIUUQUDZUXIUVQUDZUWR
      UHZUXAUXCUXCUWIUXJUXDNUUQULUWEVLVEZUXCUWMLUXIUXCUWJUXITZSZUWKULUWLUXQUWKU
      LPZUWJUXHTZUXQUXIUWJRZUXSUXCUXPUXTVMZUXCUXPUYAUXCUXPUXPUYAUKUXQUXTUXPUXQU
      XTUXPVMZUXJUWJUATZUXTUYBVNUXQUXIUWJVOUXCUXJUXPUXOVFUXCUXPUYCUXCUXIUAUWJUX
      CUXJUXIUARUXOUXIVPVEVQVRZVSVTWAWBWCVRUWJUXHWDWEUXQUWKULUMZUXSUXRVMUXQUYCU
      YEUXSUKUYDUYCUXSUYEUXGUYENUWJUANLWFUXFUWKULUXEUWJUUQWGWHWIWJVEUWKULWKWLWM
      UXQUWJUVPTZUWLULPUXCUXPUYFUXCUXIUVPUWJUWCUXIUVPTZUXIUVPRUXCUVPUXIWNUVOUWC
      UXBUWGVFUUFUXBUYGUUHNUUQUVPGHULKJUWEUWFWOVKWPVQVRUVPULUWJUWDWQVEWRWSUXCUX
      LULUXMUWRUXCUXLURPZULOPSZUYHULULPZSZUXLOPZUYJSZWTZUXLULUWRUHUXCUYIUYKUYMX
      AZXAUYNUXCUYOUYIUXCUYHUYLXAZUYJSUYOUXCUYPUYJUXCUYLUYHXAZUYPUXLULPZVMUYLUY
      HUYRWTZUYQUXCUYLUYHUYRXBUXCUXLULUXCUWIUXLULUMUXDNUUQULUWEXCVEXDUXCUWIUYSU
      XDUUQUXIXEVEWPUYLUYHXFXGULVBXHUYHUYLUYJXIXGXJUYIUYKUYMXKXLUROURULOULUXLUL
      UXIUUQXMUWDXNUWDUWDXOXLUUFUXBUXMULPUUHNUUQUVPGHULKJUWEUWFXPVKXQUWTUXKUXNS
      MUXIUAUWNUXIPZUWOUXKUWSUXNUWMLUWNUXIXRUYTUWPUXLUWQUXMUWRUWNUXIUUQWGUWNUXI
      UVQWGXSXTYAYBUWIUVRSUWAUXAMLUUQUVQYCYDYEWSVFUVMUVTUWBSCUVQQUVAUVQPZUVCUVT
      UVEUWBVUAUVBUVSIUVAUVQUCWGYFVUAUVDUWAAHUVAUVQUUQUGYGYHXTYAYBWBYIVRYJUUEUU
      TUVLUVIUVNUUEUUPUVKUUJUUSUUEUUOUVJUUKUUEUUMGUUNHUUEUUNHOUEHFOHYKHYLYMYNYO
      YPUUEUVHUVMCQUUEUVHUVCUVEUVFBOUFZUIZUVMUUEUVGVUBUVCUVEUVFBFOXRYQVUCUVMVUB
      UVCUVEVUBYRUVFBYSYTUUAUUBUUCUUD $.
      $( [10-Sep-2011] $) $( [3-Aug-2011] $)
  $}

  ${
    $d a b c d k n y z $.  $d B d y $.  $d L n z $.  $d L x $.
    $d R a b c d n y z $.  $d X a b n z $.
    $( Lemma for axfe (future) .  The full statement of the axiom when ` L ` is
       empty. $)
    axfelem9 $p |- ( L = (/) ->
                      ( ( ( ( L C_ No /\ R C_ No ) /\ ( L e. A /\ R e. B ) ) /\
                          ( X e. On /\ A. n e. ( L u. R ) ( bday ` n ) e. X )
        /\
                          A. x e. L A. y e. R x <s y ) ->
                        E. z e. No ( ( bday ` z ) C_ X /\
                                     A. x e. L x <s z /\
                                     A. y e. R z <s y ) ) ) $=
      ( vb va vd vc vk c0 wceq csur wss wa wcel con0 cv cbday cfv cun wral
      cslt wbr w3a wrex wi c1o wne crab cint csn cxp c2o 1on elisseti prid1
      eqid axfelem1 noxp1o syl adantr axfelem7 cop ctp ssel2 adantlr axfelem3
      onelss axfelem5 sylc sseld imp fvconst2 wn wb ontri1 onss sylanc biimpd
      con2d ex pm2.43d intss1 nsyl weq fveq2 neeq1d elrab3 biimprd df-ne
      syl5ibr mt3d eqtr4d r19.21aiva axfelem6 w3o wo 3orel2 axfelem4 bnj1540
      nofv jctil bnj1426 orcd df-3or sylibr fvex 0ex 2on brtp eqbrtrd raleq
      breq12d anbi12d rcla4ev sylan32c sltval biimpar sylan31c sseq1d breq1
      ralbidv ad2ant2l 3adant3 uneq1 uncom un0 eqtri syl6eq raleqdv anbi2d
      3anbi2d 3anass ral0 biantrur anbi2i bitr4i syl6bb rexbidv imbi12d mpbiri
      ) HOPZHQRZFQRZSHDTZFETZSSZIUATZGUBZUCUDITZGHFUEZUFZSZAUBZBUBZUGUHBFUFAHUF
      ZUIZCUBZUCUDZIRZUUSUVCUGUHZAHUFZUVCUUTUGUHZBFUFZUIZCQUJZUKUULUUMUUOGFUFZS
      ZUVAUIZUVEUVISZCQUJZUKUULUVMUVPUVAUULUVMUVPUUIUUKUVMUVPUKUUHUUJUUIUUKSZUV
      MUVPJUBUUNUDULUMJKUBUJGFUFKUAUNUOZULUPUQZQTZUVSUCUDZIRZUVSUUTUGUHZBFUFZUV
      PUVQUVMSUVQUVTUVMUVQUVRUATZUVTEUVRGFULKJULURULUAUSUTZVAZUVRVBZVCZUVRVDVEZ
      VFEUVRULGFIKJUWGUWHVGUVQUWDUVMUVQUWCBFUVTUUTQTZLUBZUVSUDZUWLUUTUDZPZLMUBZ
      UFZUWPUVSUDZUWPUUTUDZULOVHULURVHOURVHVIZUHZSZMUAUJZUWCUVQUUTFTZSZUVQUVTUX
      DUWJVFUUIUXDUWKUUKFQUUTVJVKZNUBZUUTUDZULUMZNUAUNZUOZUATZUWOLUXKUFZUXKUVSU
      DZUXKUUTUDZUWTUHZUXCUXEUXEUWKUXLUXFNUUTULUWGVLVEZUXEUWOLUXKUXEUWLUXKTZSZU
      WMULUWNUXSUWLUVRTZUWMULPUXEUXRUXTUXEUXKUVRUWLUWEUXKUVRTZUXKUVRRUXEUVRUXKV
      MUVQUWEUXDUWIVFUUIUXDUYAUUKNUUTUVRGFULKJUWGUWHVNVKVOVPVQUVRULUWLUWFVRVEUX
      SUWNULPZUWLUXJTZUXSUXKUWLRZUYCUXEUXRUYDVSZUXEUXRUYEUXEUXRUXRUYEUKUXSUYDUX
      RUXSUYDUXRVSZUXLUWLUATZUYDUYFVTUXSUXKUWLWAUXEUXLUXRUXQVFUXEUXRUYGUXEUXKUA
      UWLUXEUXLUXKUARUXQUXKWBVEVPVQZWCWDWEWFWGVQUWLUXJWHWIUXSUWNULUMZUYCUYBVSUX
      SUYGUYIUYCUKUYHUYGUYCUYIUXIUYINUWLUANLWJUXHUWNULUXGUWLUUTWKWLWMWNVEUWNULW
      OWPWQWRWSUXEUXNULUXOUWTUUIUXDUXNULPUUKNUUTUVRGFULKJUWGUWHWTVKUXEULULPZUXO
      OPZSZUYJUXOURPZSZULOPUYMSZXAZULUXOUWTUHUXEUYLUYNXBZUYOXBUYPUXEUYQUYOUXEUY
      JUYKUYMUXEUYKUYMXBZUYJUXOULPZVSUYKUYSUYMXAZUYRUXEUYKUYSUYMXCUXEUXOULUXEUW
      KUXOULUMUXFNUUTULUWGXDVEXEUXEUWKUYTUXFUUTUXKXFVEVOULVBXGXHXIUYLUYNUYOXJXK
      ULOULUROURULUXOUWFUXKUUTXLXMURUAXNUTZVUAXOXKXPUXBUXMUXPSMUXKUAUWPUXKPZUWQ
      UXMUXAUXPUWOLUWPUXKXQVUBUWRUXNUWSUXOUWTUWPUXKUVSWKUWPUXKUUTWKXRXSXTYAUVTU
      WKSUWCUXCMLUVSUUTYBYCYDWSVFUVOUWBUWDSCUVSQUVCUVSPZUVEUWBUVIUWDVUCUVDUWAIU
      VCUVSUCWKYEVUCUVHUWCBFUVCUVSUUTUGYFYGXSXTYAWFYHVQYIUUGUVBUVNUVKUVPUUGUURU
      VMUULUVAUUGUUQUVLUUMUUGUUOGUUPFUUGUUPOFUEZFHOFYJVUDFOUEFOFYKFYLYMYNYOYPYQ
      UUGUVJUVOCQUUGUVJUVEUVFAOUFZUVIUIZUVOUUGUVGVUEUVEUVIUVFAHOXQYQVUFUVEVUEUV
      ISZSUVOUVEVUEUVIYRUVIVUGUVEVUEUVIUVFAYSYTUUAUUBUUCUUDUUEUUF $.
      $( [10-Sep-2011] $) $( [3-Aug-2011] $)
  $}

  ${
    $d L a p q $.  $d L x $.  $d p x y $.  $d q x y $.  $d R a p q $.
    $d R x y $.
    axfelem10.1 $e |- C =
                         |^| { a e. On |
                               A. p e. L A. q e. R
                                  ( p |` a ) =/= ( q |` a ) } $.
    $( Lemma for axfe (future) .  Now that we have proven the cases where one
       of ` L ` or ` R ` is empty, we turn to the case where they are both
       non-empty.  We start by proving that this new ` C ` is an ordinal. $)
    axfelem10 $p |- ( ( ( ( L C_ No /\ R C_ No ) /\ ( L e. A /\ R e. B ) ) /\
                         A. x e. L A. y e. R x <s y ) ->
                       C e. On ) $=
      ( csur wss wa wcel cv cslt wbr wral cres wne con0 crab cint wrex cbday
      cun cima cuni csuc wceq reseq2 neeq1d neeq2d bitrd 2ralbidv rcla4ev cvv
      unexg axfelem0 syl ad2antlr wi ssel2 weq wn breq2 notbid sltirr syl5cbi
      necon2ad ad2ant2r wrel cdm relssres wfun nofun funrel 3syl cfv bdayval
      bdaydm syl6eleqr bdayfun funfvima mpan com12 adantl mpd ssun1 imass2
      ax-mp sseli elssuni sssucid sstr2 mpi eqsstr3d sylanc ssun2 ad2ant2l
      eqeq12d necon3bid sylibrd ex com23 breq1 rcla42v impcom syl5 expdimp
      pm2.43d r19.21aivv adantlr onintrab2 sylib syl5eqel ) GLMZFLMZNZGCOFDONZN
      APZBPZQRZBFSAGSZNZIPZJPZTZHPZYHTZUAZHFSIGSZJUBUCUDZUBEYFYMJUBUEZYNUBOUFGF
      UGZUHZUIZUJZUBOZYGYSTZYJYSTZUAZHFSIGSZYOYFYMUUDJYSUBYHYSUKZYLUUCIHGFUUEYL
      UUAYKUAUUCUUEYIUUAYKYHYSYGULUMUUEYKUUBUUAYHYSYJULUNUOUPUQYAYTXTYEYAYPUROY
      TGFCDUSYPURUTVAVBXTYEUUDYAXTYENZUUCIHGFUUFYGGOZYJFOZNZUUCXTYEUUIUUIUUCVCZ
      XTYGYJQRZUUJYEUUINXTUUIUUKUUCXTUUIUUKUUCVCXTUUINZUUKYGYJUAZUUCXRUUGUUKUUM
      VCZXSUUHXRUUGNZYGLOZUUNGLYGVDZUUPUUKYGYJIHVEZYGYGQRZVFUUKVFUUPUURUUSUUKYG
      YJYGQVGVHYGVIVJVKVAVLUULUUAUUBYGYJUULUUAYGUUBYJXRUUGUUAYGUKZXSUUHYGVMZYGV
      NZYSMUUTUUOYGYSVOUUOUUPYGVPUVAUUQYGVQYGVRVSUUOUVBYGUFVTZYSUUOUUPUVCUVBUKU
      UQYGWAVAUUOUVCYRMZUVCYSMZUUOUVCYQOZUVDUUOUVCUFGUHZOZUVFUUOYGUFVNZOZUVHUUO
      YGLUVIUUQWBWCUUGUVJUVHVCXRUVJUUGUVHUFVPZUVJUUGUVHVCWDGYGUFWEWFWGWHWIUVGYQ
      UVCGYPMUVGYQMGFWJGYPUFWKWLWMVAUVCYQWNVAUVDYRYSMZUVEYRWOZUVCYRYSWPWQVAWRWS
      VLXSUUHUUBYJUKZXRUUGYJVMZYJVNZYSMUVNXSUUHNZYJYSVOUVQYJLOZYJVPUVOFLYJVDZYJ
      VQYJVRVSUVQUVPYJUFVTZYSUVQUVRUVTUVPUKUVSYJWAVAUVQUVTYRMZUVTYSMZUVQUVTYQOZ
      UWAUVQUVTUFFUHZOZUWCUVQYJUVIOZUWEUVQYJLUVIUVSWBWCUUHUWFUWEVCXSUWFUUHUWEUV
      KUWFUUHUWEVCWDFYJUFWEWFWGWHWIUWDYQUVTFYPMUWDYQMFGWTFYPUFWKWLWMVAUVTYQWNVA
      UWAUVLUWBUVMUVTYRYSWPWQVAWRWSXAXBXCXDXEXFUUIYEUUKYDUUKYGYCQRABYGYJGFYBYGY
      CQXGYCYJYGQVGXHXIXJXKXLXMXNWSYMJXOXPKXQ $.
      $( [10-Sep-2011] $) $( [17-Aug-2011] $)

  $}

  ${
    $d C d $.  $d L a p q $.  $d L x $.  $d p q x y $.  $d R a p q $.
    $d R x y $.
    axfelem11.1 $e |- C =
                         |^| { a e. On |
                               A. p e. L A. q e. R
                                  ( p |` a ) =/= ( q |` a ) } $.
    $( Lemma for axfe (future) . ` C ` is either a limit or successor
       ordinal. $)
    axfelem11 $p |- ( ( L =/= (/) /\ R =/= (/) ) ->
                      ( ( ( ( L C_ No /\ R C_ No ) /\ ( L e. A /\ R e. B ) ) /\
                         A. x e. L A. y e. R x <s y )
                      -> ( E. d e. On C = suc d \/ Lim C ) ) ) $=
      ( c0 wne wa con0 wcel cv csuc wceq wrex wlim wo csur wss cslt wbr wral
      w3o wn wi cres crab wex eqid jctr anim1i ancomd 2eximi df-rex r19.42v
      exbii 3bitr2i sylibr n0 anbi12i eeanv bitr4i rexnal df-ne con2bii rexbii
      bitr2i bitr3i 3imtr4i reseq2 eqeq12d res0 eqeq12i syl6bb necon3bid
      2ralbidv elrab pm3.27bi nsyl cint eqeq1i wb ssrab2 onint0 ax-mp bitri
      notbii 3orel1 syl word eloni ordzsl sylib syl5 axfelem10 ) GMNZFMNZOZEPQZ
      EKRSTKPUAZEUBZUCZGUDUEFUDUEOGCQFDQOOARBRUFUGBFUHAGUHOXDEMTZXFXGUIZXHXEXDX
      IUJZXJXHUKXDMIRZJRZULZHRZXMULZNZHFUHIGUHZJPUMZQZUJXKXDMMNZHFUHZIGUHZXTXLG
      QZXOFQZOZHUNIUNZMMTZHFUAZIGUAZXDYCUJZYGYEYDYHOZOZHUNZIUNZYJYFYMIHYFYLYEYD
      YLYEYDYHMUOUPUQURUSYJYDYIOZIUNYLHFUAZIUNYOYIIGUTYQYPIYDYHHFVAVBYQYNIYLHFU
      TVBVCVDXDYDIUNZYEHUNZOYGXBYRXCYSIGVEHFVEVFYDYEIHVGVHYKYBUJZIGUAYJYBIGVIYT
      YIIGYIYAUJZHFUAYTYHUUAHFYAYHMMVJVKVLYAHFVIVMVLVNVOXTMPQYCXRYCJMPXMMTZXQYA
      IHGFUUBXNXPMMUUBXNXPTXLMULZXOMULZTYHUUBXNUUCXPUUDXMMXLVPXMMXOVPVQUUCMUUDM
      XLVRXOVRVSVTWAWBWCWDWEXIXTXIXSWFZMTZXTEUUEMLWGXSPUEUUFXTWHXRJPWIXSWJWKWLW
      MVDXIXFXGWNWOXEEWPXJEWQKEWRWSWTABCDEFGHIJLXAWT $.
      $( [10-Sep-2011] $) $( [24-Aug-2011] $)
  $}

  ${
    $d A a x y $.  $d B a x y $.  $d X a x y $.
    $( Lemma for axfe (future) .  If the restrictions of two surreals to a
       given ordinal obey surreal less than, then so do the two surreals
       themselves. $)
    axfelem12 $p |- ( ( A e. No /\ B e. No /\ X e. On ) ->
                      ( ( A |` X ) <s ( B |` X ) -> A <s B ) ) $=
      ( vy vx va csur wcel con0 w3a cres cslt wbr wa cv cfv wceq wral c1o c0
      cop c2o ctp wrex wne crab cint wi cvv sltintdifex onintrab syl6ib
      noreson 3adant2 3adant1 sylanc imp fvres eqeq12d biimpd wss onelss
      3simpl3 cdm wo wb sltval2 w3o fvex 0ex 2on elisseti brtp wn 1n0 df-ne
      mpbi eqeq1 mtbiri ndmfv nsyl2 adantr orcd prid2 nosgnn0i eqcom syl6bb
      adantl olcd 3jaoi sylbi syl6bi cin dmres eleq2i elin bitri pm3.26bi jaoi
      syl sylc sseld weq fveq2 necon3bid elrab pm3.26bi2 con3d onelon sylan
      ontri1 intss1 syl5bi con2d ex com23 mpd con2bii sylibr r19.21aiva
      fvresval ori eqcomd eqeq2 mpbid a1i ad2antrl cpr crn wfun nofun fvelrn
      norn syld nosgnn0 eleq1 nsyli adantrl jcad anim12i ad2antll adantrr syl6
      3orim123d 3imtr4g sylbid raleq breq12d anbi12d rcla4ev sylan32c sltval
      3adant3 mpbird ) AGHZBGHZCIHZJZACKZBCKZLMZABLMZUURUVANZUVBDOZAPZUVDBPZQZD
      EOZRZUVHAPZUVHBPZSTUASUBUATUBUAUCZMZNZEIUDZFOZUUSPZUVPUUTPZUEZFIUFZUGZIHZ
      UVGDUWARZUWAAPZUWABPZUVLMZUVOUVCUURUVAUWBUUSGHZUUTGHZUVAUWBUHUURUWGUWHNUV
      AUWAUIHUWBUUSUUTFUJUVSFUKULUUOUUQUWGUUPACUMUNZUUPUUQUWHUUOBCUMUOZUPUQZUVC
      UVGDUWAUVDCHZUVDUUSPZUVDUUTPZQZUVGUVCUVDUWAHZNZUWLUWOUVGUWLUWMUVEUWNUVFUV
      DCAURUVDCBURUSUTUVCUWPUWLUVCUWACUVDUUQUWACHZUWACVAUVCCUWAVBUUOUUPUUQUVAVC
      UVCUWAUUSVDZHZUWAUUTVDZHZVEZUWRUURUVAUXCUURUVAUWAUUSPZUWAUUTPZUVLMZUXCUWG
      UWHUVAUXFVFUURUUSUUTFVGUWIUWJUPZUXFUXDSQZUXETQZNZUXHUXEUBQZNZUXDTQZUXKNZV
      HZUXCSTSUBTUBUXDUXEUWAUUSVIUWAUUTVIVJUBIVKVLZUXPVMZUXJUXCUXLUXNUXJUWTUXBU
      XHUWTUXIUXHUXMUWTUXHUXMSTQZSTUEUXRVNVOSTVPVQUXDSTVRVSZUWAUUSVTWAZWBWCUXLU
      WTUXBUXHUWTUXKUXTWBWCUXNUXBUWTUXKUXBUXMUXKUXIUXBUXKUXITUBQZTUBUEUYAVNUBSU
      BUXPWDWETUBVPVQUXKUXIUBTQUYAUXEUBTVRUBTWFWGVSZUWAUUTVTWAZWHWIWJWKWLUQUWTU
      WRUXBUWTUWRUWAAVDZHZUWTUWACUYDWMZHUWRUYENUWSUYFUWAACWNWOUWACUYDWPWQZWRZUX
      BUWRUWABVDZHZUXBUWACUYIWMZHUWRUYJNUXAUYKUWABCWNWOUWACUYIWPWQZWRZWSWTXAXBU
      QUWQUWMUWNUEZVNZUWOUVDIHZUVDUVTHZVNZUYOUWQUYPUYNUYQUYQUYPUYNUVSUYNFUVDIFD
      XCZUVQUVRUWMUWNUYSUVQUWMUVRUWNUVPUVDUUSXDUVPUVDUUTXDUSXEXFXGXHUWBUWPUYPUV
      CUWAUVDXIUWKXJZUWQUYPUYRUYTUVCUWPUYPUYRUHUVCUYPUWPUYRUVCUYPUWPUYRUHZUWBUY
      PVUAUVCUWBUYPNZUYQUWPVUBUWAUVDVAUWPVNUYQUWAUVDXKUVDUVTXLXMXNUWKXJXOXPUQXQ
      XAUYNUWOUWMUWNVPXRXSXAXTUURUVAUWFUURUVAUXFUWFUXGUURUXOUWDSQZUWETQZNZVUCUW
      EUBQZNZUWDTQZVUFNZVHUXFUWFUURUXJVUEUXLVUGUXNVUIUURUXJVUCVUDUXJVUCUHUURUXH
      VUCUXIUXHUWDUXDQVUCUXHUXDUWDUXHUXMUXDUWDQZUXSVUJUXMUWACAYAYBWAYCUXDSUWDYD
      YEZWBYFUURUXJVUDUURUXJNZUYJVNZVUDUWRUXBVNZVUMVULUWRUYJUXBUXBUWRUYJUYLXGXH
      VULUWTUWRUXHUWTUURUXIUXTYGUYHWTUURUXIVUNUXHUURUXIVUNUURUWHUXIVUNUHUWJUWHU
      XBUXESUBYHZHZUXIUWHUXBUXEUUTYIZHZVUPUWHUUTYJZUXBVURUHUUTYKVUSUXBVURUWAUUT
      YLXOWTUWHVUQVUOUXEUUTYMXBYNUXIVUPTVUOHZYOUXETVUOYPVSYQWTUQYRXAUWABVTWTXOY
      SUXLVUGUHUURUXHVUCUXKVUFVUKUXKUWEUXEQVUFUXKUXEUWEUXKUXIUXEUWEQZUYBVVAUXIU
      WACBYAYBWAYCUXEUBUWEYDYEZYTYFUURUXNVUHVUFUURUXNUYEVNZVUHUURUXNVVCUWRUWTVN
      ZVVCUURUXNNZUWRUYEUWTUWTUWRUYEUYGXGXHVVEUXBUWRUXKUXBUURUXMUYCUUAUYMWTUURU
      XMVVDUXKUURUXMVVDUURUWGUXMVVDUHUWIUWGUWTUXDVUOHZUXMUWGUWTUXDUUSYIZHZVVFUW
      GUUSYJZUWTVVHUHUUSYKVVIUWTVVHUWAUUSYLXOWTUWGVVGVUOUXDUUSYMXBYNUXMVVFVUTYO
      UXDTVUOYPVSYQWTUQUUBXAXOUWAAVTUUCUXNVUFUHUURUXKVUFUXMVVBWHYFYSUUDUXQSTSUB
      TUBUWDUWEUWAAVIUWABVIVJUXPUXPVMUUEUUFUQUVNUWCUWFNEUWAIUVHUWAQZUVIUWCUVMUW
      FUVGDUVHUWAUUGVVJUVJUWDUVKUWEUVLUVHUWAAXDUVHUWABXDUUHUUIUUJUUKUURUVBUVOVF
      ZUVAUUOUUPVVKUUQEDABUULUUMWBUUNXO $.
      $( [9-Mar-2012] $) $( [4-Sep-2011] $)
  $}

  ${ $d A x $. $d B x y $. $d Q y $. $d R x y $.
     $( Lemma for axfe (future) . Preliminary work for ~ axfelem14 . $)
     axfelem13 $p |- ( ( ( ( A C_ No /\ B C_ No ) /\
     	       	       	   A. x e. A A. y e. B x <s y ) /\
                         ( X e. On /\
                           ( ( P e. A /\ Q e. B ) /\
			     ( R e. A /\ S e. B ) ) ) ) ->
                       ( ( ( P |` X ) = ( Q |` X ) /\
		       	   ( R |` X ) = ( S |` X ) ) ->
                         ( -. ( P |` X ) <s ( R |` X ) /\
                           -. ( Q |` X ) <s ( S |` X ) ) ) ) $=
       ( csur wss wa cv cslt wbr wral con0 wcel cres wceq wn sltasym ssel2 
       ad2ant2r ad2ant2rl ad2ant2l jca wi breq1 breq2 rcla42v ancoms ad2ant2lr 
       impcom adantll sylc adantrl adantr wb biimpd axfelem12 adantrr simprl 
       syl3anc sylan9r mtod adantl biimprd ex ) CJKZDJKZLZAMZBMZNOZBDPACPZLZIQR
       ZECRZFDRZLZGCRZHDRZLZLZLLZEISZFISZTZGISZHISZTZLZWGWJNOZUAZWHWKNOZUAZLWFW
       MLZWOWQWRWNFGNOZWFWSUAZWMVQWEWTVRGJRZFJRZLGFNOZWTVQWELZGFUBXDXAXBVLWDXAV
       PWAVJWBXAVKWCCJGUCUDZUEVLWAXBVPWDVKVTXBVJVSDJFUCUFZUDUGVPWEXCVLWEVPXCVTW
       BVPXCUHZVSWCWBVTXGVOXCGVNNOABGFCDVMGVNNUIVNFGNUJUKULUMUNUOUPUQURZWMWNWHW
       JNOZWFWSWMWNXIWIWNXIUSWLWGWHWJNUIURUTXBXAVRXIWSUHWFFGIVAVLWEXBVPVRVLWAXB
       WDXFVBUEVLWEXAVPVRVLWDXAWAXEUQUEVQVRWEVCVDZVEVFWRWPWSXHWMWPXIWFWSWMXIWPW
       LXIWPUSWIWJWKWHNUJVGVHXJVEVFUGVI $.
       $( [22-Mar-2012] $) $( [16-Mar-2012] $)
  $}

  ${ $d A x $. $d B x y $. $d P x y $. $d Q y $. $d R x y $. $d S y $.
     $( Lemma for axfe (future) . A uniqueness result for restrictions of
     	surreals. $)
     axfelem14 $p |- ( ( ( ( A C_ No /\ B C_ No ) /\
     	       	       	   A. x e. A A. y e. B x <s y ) /\
                         ( X e. On /\
                           ( ( P e. A /\ Q e. B ) /\
			     ( R e. A /\ S e. B ) ) ) ) ->
                       ( ( ( P |` X ) = ( Q |` X ) /\
		       	   ( R |` X ) = ( S |` X ) ) ->
                         ( ( P |` X ) = ( R |` X ) /\
                           ( Q |` X ) = ( S |` X ) ) ) ) $=
       ( csur wss wa cv cslt wbr wral con0 wcel cres wceq wn axfelem13 imp wi 
       ancom anbi2i sylan2b ancomsd jca an4 sylib wb wor sotrieq2 axsltso 
       noreson expcom anim12d adantrr sylancr adantrl anbi12d ssel im2anan9 
       syl5ib sylan2 an1s adantlr adantr mpbird ex ) CJKZDJKZLZAMBMNOBDPACPZLZI
       QRZECRZFDRZLZGCRZHDRZLZLZLZLZEISZFISZTZGISZHISZTZLZWGWJTZWHWKTZLZWFWMLZW
       PWGWJNOUAZWJWGNOUAZLZWHWKNOUAZWKWHNOUAZLZLZWQWRXALZWSXBLZLXDWQXEXFWFWMXE
       ABCDEFGHIUBUCWFWMXFWFWLWIXFVPVQWCVTLZLWLWILXFUDWEABCDGHEFIUBWDXGVQVTWCUE
       UFUGUHUCUIWRXAWSXBUJUKWFWPXDULZWMVNWEXHVOVQVNWDXHVQEJRZGJRZLZFJRZHJRZLZL
       ZXHVNWDLVQXOLZWNWTWOXCJNUMZWGJRZWJJRZLZWNWTULXPJWGWJNUNUOVQXKXTXNVQXKXTV
       QXIXRXJXSXIVQXREIUPUQXJVQXSGIUPUQURUCUSUTXQWHJRZWKJRZLZWOXCULXPJWHWKNUNU
       OVQXNYCXKVQXNYCVQXLYAXMYBXLVQYAFIUPUQXMVQYBHIUPUQURUCVAUTVBVNWDXOVNVRWAL
       ZVSWBLZLXOWDVLYDXKVMYEXNVLVRXIWAXJCJEVCCJGVCURVMVSXLWBXMDJFVCDJHVCURVDVR
       VSWAWBUJVEUCVFVGVHVIVJVK $.
       $( [22-Mar-2012] $) $( [16-Mar-2012] $)
  $}

  ${ $d A a g h $.  $d p a q x y $.  $d B a g h $.  $d C a f g h $.  
     $d D a $.  $d x g y h $.  $d L a f g h $.  $d L p q x $.  
     $d R a f g h $.  $d R p q x y $. $d A f $. $d B f $. $d f x y $.

     $d A a b c d j k $. $d B b c d j k $. $d C b c d j k $.
     $d f b c d j k $. $d g b c d j k $. $d h b c d j k $.
     $d x y b c d j k $. $d L b c d j k $. $d R b c d j k $.
    axfelem15.1 $e |- C =
                         |^| { a e. On |
                               A. p e. L A. q e. R
                                  ( p |` a ) =/= ( q |` a ) } $.
    axfelem15.2 $e |- D = U. { f | 
    		      E. g e. L E. h e. R E. a e. U. C
		      ( ( g |` a ) =  f /\ ( h |` a ) = f )
		      } $.

    $( Lemma for axfe (future) .  At this point, we introduce a new
       surreal number ` D ` . The next several lemmas prove that
       either ` D ` or a surreal closely related so it has the
       required properties for the final theorem. We begin by proving
       that ` D ` is a surreal. $)
    axfelem15 $p |- ( ( L =/= (/) /\ R =/= (/) ) ->
                      ( ( ( ( L C_ No /\ R C_ No ) /\ ( L e. A /\ R e. B ) ) /\
                         A. x e. L A. y e. R x <s y ) -> D e. No ) ) $=
      ( vk vj vb vd vc c0 wne wa csur wss wcel cv cslt wbr wral cres wceq cuni 
      wrex cab wfun cdm con0 crn c1o c2o cpr w3a wo wi ssel ad2antrr ad2antrl 
      axfelem10 onuni syl adantl onelon ex eleq1 noreson syl5cbi adantrd 
      sylan9 r19.23adv syld r19.23advv visset weq eqeq2 anbi12d rexbidv 
      2rexbidv elab syl5ib nofun syl6 word ordtri2or2 eloni syl2an axfelem14 
      pm3.26 anim1i simpll simprl jca anim12i adantr simprrl ad2antlr simprrr 
      cin wb sseqin2 reseq2 eqeq12d resres eqeq12i syl5bb sylbi reseq1 imp 
      sylc pm3.26d sseq1 ssres2 syl5cbir mpd pm3.27 orim12d com23 exp4a mpdi 
      syl2and imp3a simplr jca32 syl5 anassrs expr eqeq1 eqcom syl6bb sseq2 
      orbi12d imbi12d biimpcd r19.23adva r19.21aiv ralbidv eqeq1d anbi1d 
      cbvrexv anbi2d rexbii 2rexbii 3bitri abbii raleqi 3imtr4g jcad fununi 
      ciun cvv dmuni eleq1i elon2 bitri wal nodmon eleq1a 19.21aiv abss sylibr 
      ssorduni dmex dfiun2 ordeq ax-mp iunexg ssexg rexcom r19.42v pm3.26bi 
      reximi ss2abi cmpt2 cxp xpexg copab2 dmoprabss mpan df-mpt2 dmeqi 
      syl5eqel eqid mpt2fun funrnex mpi rneqi rnoprab2 3eqtri syl5eqelr 
      sylancr simplrl sylanc sylanbrc norn rnuni sseq1i iunss 3jca elno2 ) KUBU
      CGUBUCUDZKUEUFZGUEUFZUDZKCUGZGDUGZUDZUDZAUHBUHUIUJBGUKAKUKZUDZFUEUGZUXKUX
      TUDZIUHZNUHZULZHUHZUMZJUHZUYDULZUYFUMZUDZNEUNZUOZJGUOZIKUOZHUPZUNZUQZUYQU
      RZUSUGZUYQUTZVAVBVCZUFZVDZUYAUYBUYRUYTVUCUYBQUHZUQZVUERUHZUFZVUGVUEUFZVEZ
      RUYPUKZUDZQUYPUKUYRUYBVULQUYPUYBVUEUYPUGZVUFVUKUYBVUMVUEUEUGZVUFUYBUYEVUE
      UMZUYIVUEUMZUDZNUYLUOZJGUOIKUOZVUNVUMUYBVURVUNIJKGUYBUYCKUGZVURVUNVFZUYHG
      UGZUYBVUTUYCUEUGZVVAUXRVUTVVCVFZUXKUXSUXLVVDUXMUXQKUEUYCVGVHVIUYBVVCVVAUY
      BVVCUDVUQVUNNUYLUYBUYDUYLUGZUYDUSUGZVVCVUQVUNVFZUYBUYLUSUGZVVEVVFVFUXTVVH
      UXKUXTEUSUGVVHABCDEGKLMNOVJEVKVLVMZVVHVVEVVFUYLUYDVNVOVLZVVCVVFVVGVVCVVFU
      DZVUOVUNVUPVUOUYEUEUGVUNVVKUYEVUEUEVPUYCUYDVQVRVSVOVTWAVOWBVSWCUYOVUSHVUE
      QWDZHQWEZUYMVURIJKGVVMUYKVUQNUYLVVMUYGVUOUYJVUPUYFVUEUYEWFUYFVUEUYIWFWGWH
      WIWJZWKZVUEWLWMUYBVUSVUJRSUHZTUHZULZUYFUMZUAUHZVVQULZUYFUMZUDZTUYLUOZUAGU
      OSKUOZHUPZUKZVUMVUKUYBVURVWGIJKGUYBVUTVVBUDZVURVWGVFUYBVWHUDVUQVWGNUYLUYB
      VWHVVEVUQVWGVFZUYBVWHVVEUDZUDUYEUYIUMZUYEVUGUFZVUGUYEUFZVEZRVWFUKZVFZVWIU
      YBVWJVWKVWOUYBVWJVWKUDZUDZVWNRVWFVWRVVRVUGUMZVWAVUGUMZUDZTUYLUOZUAGUOSKUO
      ZVWNVUGVWFUGVWRVXBVWNSUAKGVWRVVPKUGVVTGUGUDZVXBVWNVFVWRVXDUDVXAVWNTUYLVWR
      VXDVVQUYLUGZVXAVWNVFZVWRVXDVXEUDZUDVVRVWAUMZUYEVVRUFZVVRUYEUFZVEZVFZVXFVW
      RVXGVXHVXKUYBVWQVXGVXHUDZVXKUYBVWQVXMUDZVXKUYBVVEVXEUDZVWHVXDUDZVWKVXHUDZ
      UDZUDVXKVXNUYBVXOVXRVXKUYBVVFVVQUSUGZVXRVXKVFZVVEVXEUYBVVFVXSUDZUYDVVQUFZ
      VVQUYDUFZVEZVXTUYDWNVVQWNVYDVVFVXSUYDVVQWOUYDWPVVQWPWQUYBVYDVYAVXTUYBVYDV
      YAVXRVXKUYBVYAVXRUDZVYDVXKUYBVYEVYDVXKVFUYBVYEUDZVYBVXIVYCVXJVYFVYBVXIVYF
      VYBUDZUYEVVPUYDULZUMZVXIVYGVYIUYIVVTUYDULZUMZUXNUXSUDZVVFVXPUDZUDZVWKVYHV
      YJUMZUDVYIVYKUDVYGABKGUYCUYHVVPVVTUYDWRVYFVYNVYBUYBVYLVYEVYMUXTVYLUXKUXRU
      XNUXSUXNUXQWSWTVMZVYEVVFVXPVVFVXSVXRXAVYAVXPVXQXBXCXDXEVYGVWKVYOVYEVWKUYB
      VYBVYAVXPVWKVXHXFZXGVYFVYBVYOVYFVXHVYBVYOVFVYEVXHUYBVYAVXPVWKVXHXHZVMVYBV
      VRUYDULZVWAUYDULZUMZVYOVXHVYBVVQUYDXIZUYDUMZWUAVYOXJUYDVVQXKWUCVVPWUBULZV
      VTWUBULZUMVYOWUAWUCWUDVYHWUEVYJWUBUYDVVPXLWUBUYDVVTXLXMVYSWUDVYTWUEVVPVVQ
      UYDXNVVTVVQUYDXNXOXPXQVVRVWAUYDXRVRVLXSXCXTYAVYBVYIVXIVFVYFVYIVXIVYHVVRUF
      VYBUYEVYHVVRYBUYDVVQVVPYCYDVMYEVOVYFVYCVXJVYFVYCUDZUYCVVQULZVVRUMZVXJWUFW
      UHUYHVVQULZVWAUMZVYLVXSVXPUDZUDZWUGWUIUMZVXHUDWUHWUJUDWUFABKGUYCUYHVVPVVT
      VVQWRVYFWULVYCUYBVYLVYEWUKVYPVYAVXSVXRVXPVVFVXSYFVXPVXQWSXDXDXEWUFWUMVXHV
      YFVYCWUMVYFVWKVYCWUMVFVYEVWKUYBVYQVMVYCUYEVVQULZUYIVVQULZUMZWUMVWKVYCUYDV
      VQXIZVVQUMZWUPWUMXJVVQUYDXKWURUYCWUQULZUYHWUQULZUMWUMWUPWURWUSWUGWUTWUIWU
      QVVQUYCXLWUQVVQUYHXLXMWUNWUSWUOWUTUYCUYDVVQXNUYHUYDVVQXNXOXPXQUYEUYIVVQXR
      VRVLXSVYEVXHUYBVYCVYRXGXCXTYAVYCWUHVXJVFVYFWUHWUGUYEUFVXJVYCWUGVVRUYEYBVV
      QUYDUYCYCVRVMYEVOYGVOYHYIYHYJVVJUYBVVHVXEVXSVFVVIVVHVXEVXSUYLVVQVNVOVLYKY
      LVXNVXOVXPVXQVWQVVEVXMVXEVWHVVEVWKYMVXDVXEVXHYMXDVWQVWHVXMVXDVWHVVEVWKXAV
      XDVXEVXHXAXDVWQVWKVXMVXHVWJVWKYFVXGVXHYFXDYNYOXSYPYQVXLVWSVWTVWNVWSVXLVWT
      VWNVFVWSVXHVWTVXKVWNVWSVXHVUGVWAUMVWTVVRVUGVWAYRVUGVWAYSYTVWSVXIVWLVXJVWM
      VVRVUGUYEUUAVVRVUGUYEYBUUBUUCUUDYLVLYPUUEVOWCVWEVXCHVUGRWDHRWEZVWDVXBSUAK
      GWVAVWCVXATUYLWVAVVSVWSVWBVWTUYFVUGVVRWFUYFVUGVWAWFWGWHWIWJWKUUFYQVWPVUOV
      UPVWGVUOVWPVUPVWGVFVUOVWKVUPVWOVWGVUOVWKVUEUYIUMVUPUYEVUEUYIYRVUEUYIYSYTV
      UOVWNVUJRVWFVUOVWLVUHVWMVUIUYEVUEVUGYBUYEVUEVUGUUAUUBUUGUUCUUDYLVLYPUUEVO
      WCVVNVUJRUYPVWFUYOVWEHUYOVYHUYFUMZUYJUDZNUYLUOZJGUOZSKUOWVBVYJUYFUMZUDZNU
      YLUOZUAGUOZSKUOVWEUYNWVEISKISWEZUYKWVCJNGUYLWVJUYGWVBUYJWVJUYEVYHUYFUYCVV
      PUYDXRUUHUUIWIUUJWVEWVISKWVDWVHJUAGJUAWEZWVCWVGNUYLWVKUYJWVFWVBWVKUYIVYJU
      YFUYHVVTUYDXRUUHUUKWHUUJUULWVHVWDSUAKGWVGVWCNTUYLNTWEZWVBVVSWVFVWBWVLVYHV
      VRUYFUYDVVQVVPXLUUHWVLVYJVWAUYFUYDVVQVVTXLUUHWGUUJUUMUUNUUOUUPUUQUURUUFUY
      PQRUUSVLUYTQUYPVUEURZUUTZWNZWVNUVAUGZUYBUYTWVNUSUGWVOWVPUDUYSWVNUSQUYPUVB
      UVCWVNUVDUVEUYBVUGWVMUMZQUYPUOZRUPZUSUFZWVOUYBWVRVUGUSUGZVFZRUVFWVTUYBWWB
      RUYBWVQWWAQUYPUYBVUMWVMUSUGZWVQWWAVFUYBVUMVUNWWCVVOVUEUVGWMZWVMUSVUGUVHWM
      WAUVIWVRRUSUVJUVKWVTWVSUNZWNZWVOWVSUVLWVNWWEUMWVOWWFXJQRUYPWVMVUEVVLUVMUV
      NWVNWWEUVOUVPUVKVLUYPUVAUGZWWCQUYPUKWVPUYBQUYPWVMUVAUSUVQUXOVVHWWGUYBUYPU
      YGNUYLUOZIKUOZHUPZUFWWJUVAUGWWGUXOVVHUDZUYPWWJUVAUVRUYOWWIHUYNWWHIKUYNUYK
      JGUOZNUYLUOWWHUYKJNGUYLUVSWWLUYGNUYLWWLUYGUYJJGUOUYGUYJJGUVTUWAUWBXQUWBUW
      CWWKINKUYLUYEUWDZUTZUVAWWJWWKWWMURZUVAUGZWWNUVAUGZWWKKUYLUWEZUVAUGZWWPKUY
      LCUSUWFWWSVUTVVEUDUYFUYEUMZUDINHUWGZURZUVAWWOWXBWWRUFWWSWXBUVAUGWWTINHKUY
      LUWHWXBWWRUVAUVRUWIWWMWXAINHKUYLUYEUWJZUWKUWLVLWWPWWMUQWWQINKUYLUYEWWMWWM
      UWMUWNUVAWWMUWOUWPVLWWNWXAUTWWTNUYLUOIKUOZHUPWWJWWMWXAWXCUWQWWTINHKUYLUWR
      WXDWWIHWWTUYGINKUYLUYFUYEYSUUMUUOUWSUWTUXAUXTUXOUXKUXNUXOUXPUXSUXBVMVVIUX
      CUYBWWCQUYPWWDUUFUXCUXDUYBVUEUTZVUBUFZQUYPUKZVUCUYBWXFQUYPUYBVUMVUNWXFVVO
      VUEUXEWMUUFVUCQUYPWXEUUTZVUBUFWXGVUAWXHVUBQUYPUXFUXGQUYPWXEVUBUXHUVEUVKUX
      IUYAUYQUEUGVUDFUYQUEPUVCUYQUXJUVEUVKVO $.
      $( [22-Mar-2012] $)
  $}

$( (End of Scott Fenton's mathbox.) $)

