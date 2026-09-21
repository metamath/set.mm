$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Scott Fenton
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Set up a new wff var $)
  $v al $.  $( Greek alpha $)

  $( Let variable ` al ` be a wff. $)
  walpha $f wff al $.

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  ZFC Axioms in primitive form
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( ~ ax-ext without distinct variable conditions or defined symbols.
     (Contributed by Scott Fenton, 13-Oct-2010.) $)
  axextprim $p |- -. A. x -. ( ( x e. y -> x e. z ) ->
               ( ( x e. z -> x e. y ) -> y = z ) ) $=
    ( wel wb weq wi wex wn wal axextnd wa dfbi2 imbi1i impexp bitri exbii df-ex
    mpbi ) ABDZACDZEZBCFZGZAHZTUAGZUATGZUCGGZIAJIZABCKUEUHAHUIUDUHAUDUFUGLZUCGU
    HUBUJUCTUAMNUFUGUCOPQUHARPS $.

  $( ~ ax-rep without distinct variable conditions or defined symbols.
     (Contributed by Scott Fenton, 13-Oct-2010.) $)
  axrepprim $p |- -. A. x -. ( -. A. y -. A. z ( ph -> z = y ) ->
               A. z -. ( ( A. y z e. x -> -. A. x ( A. z x e. y ->
               -. A. y ph ) ) -> -. ( -. A. x ( A. z x e. y -> -. A. y ph )
               -> A. y z e. x ) ) ) $=
    ( weq wi wal wex wel wa wb wn axrepnd df-ex df-an exbii exnal bitri bibi2i
    dfbi1 albii imbi12i mpbi ) ADCEFDGZCHZDBICGZBCIDGZACGZJZBHZKZDGZFZBHZUDLCGL
    ZUFUGUHLFZBGLZFUQUFFLFLZDGZFZLBGLZABCDMUNUTBHVAUMUTBUEUOULUSUDCNUKURDUKUFUQ
    KURUJUQUFUJUPLZBHUQUIVBBUGUHOPUPBQRSUFUQTRUAUBPUTBNRUC $.

  $( ~ ax-un without distinct variable conditions or defined symbols.
     (Contributed by Scott Fenton, 13-Oct-2010.) $)
  axunprim $p |- -. A. x -. A. y ( -. A. x ( y e. x -> -. x e. z )
               -> y e. x ) $=
    ( wel wa wex wi wal axunnd df-an exbii exnal bitri imbi1i albii df-ex mpbi
    wn ) BADZACDZEZAFZSGZBHZAFZSTRGZAHRZSGZBHZRAHRZABCIUEUIAFUJUDUIAUCUHBUBUGSU
    BUFRZAFUGUAUKASTJKUFALMNOKUIAPMQ $.

  $( ~ ax-pow without distinct variable conditions or defined symbols.
     (Contributed by Scott Fenton, 13-Oct-2010.) $)
  axpowprim $p |- ( A. x -. A. y ( A. x ( -. A. z -. x e. y -> A. y x e. z )
               -> y e. x ) -> x = y ) $=
    ( weq wel wn wal wi wex axpownd df-ex imbi1i albii exbii bitri sylib con4i
    ) ABDZABEZFCGFZACEBGZHZAGZBAEZHZBGZFAGZRFSCIZUAHZAGZUDHZBGZAIZUGFZABCJUMUFA
    IUNULUFAUKUEBUJUCUDUIUBAUHTUASCKLMLMNUFAKOPQ $.

  $( ~ ax-reg without distinct variable conditions or defined symbols.
     (Contributed by Scott Fenton, 13-Oct-2010.) $)
  axregprim $p |- ( x e. y ->
               -. A. x ( x e. y -> -. A. z ( z e. x -> -. z e. y ) ) ) $=
    ( wel wn wi wal wa wex axregnd df-an exbii exnal bitri sylib ) ABDZPCADCBDE
    FCGZHZAIZPQEFZAGEZABCJSTEZAIUARUBAPQKLTAMNO $.

  $( ~ ax-inf without distinct variable conditions or defined symbols.
     (New usage is discouraged.)  (Contributed by Scott Fenton,
     13-Oct-2010.) $)
  axinfprim $p |- -. A. x -. ( y e. z -> -. ( y e. x ->
               -. A. y ( y e. x -> -. A. z ( y e. z -> -. z e. x ) ) ) ) $=
    ( wel wa wex wi wn axinfnd df-an exbii exnal bitri imbi2i albii anbi2i mpbi
    wal df-ex ) BCDZBADZUATCADZEZCFZGZBRZEZGZAFZTUAUATUBHGZCRHZGZBRZHGHZGZHARHZ
    ABCIUIUOAFUPUHUOAUGUNTUGUAUMEUNUFUMUAUEULBUDUKUAUDUJHZCFUKUCUQCTUBJKUJCLMNO
    PUAUMJMNKUOASMQ $.

  $( ~ ax-ac without distinct variable conditions or defined symbols.
     (New usage is discouraged.)  (Contributed by Scott Fenton,
     26-Oct-2010.) $)
  axacprim $p |- -. A. x -. A. y A. z ( A. x -. ( y e. z -> -. z e. w ) ->
                  -. A. w -. A. y -. ( ( -. A. w ( y e. z -> ( z e. w ->
                  ( y e. w -> -. w e. x ) ) ) -> y = w ) -> -. ( y = w ->
                  -. A. w ( y e. z -> ( z e. w -> ( y e. w -> -. w e. x )
                  ) ) ) ) ) $=
    ( wel wa wal wex wb wi wn axacnd df-an albii annim anbi2i exbii bitri df-ex
    weq anass pm4.63 bitr3i 3bitr2i exnal bibi1i dfbi1 imbi12i 2albii mpbi ) BC
    EZCDEZFZAGZUMBDEZDAEZFZFZDHZBDTZIZBGZDHZJZCGBGZAHZUKULKJKZAGZUKULUOUPKJZJZJ
    ZDGKZUTJUTVLJKJKZBGZKDGKZJZCGBGZKAGKZABCDLVFVQAHVRVEVQAVDVPBCUNVHVCVOUMVGAU
    KULMNVCVNDHVOVBVNDVAVMBVAVLUTIVMUSVLUTUSVKKZDHVLURVSDURUKULUQFZFUKVJKZFVSUK
    ULUQUAWAVTUKWAULVIKZFVTULVIOWBUQULUOUPUBPUCPUKVJOUDQVKDUERUFVLUTUGRNQVNDSRU
    HUIQVQASRUJ $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Untangled classes
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x A $.
    $( We call a class "untanged" if all its members are not members of
       themselves.  The term originates from Isbell (see citation in ~ dfon2 ).
       Using this concept, we can avoid a lot of the uses of the Axiom of
       Regularity.  Here, we prove a series of properties of untanged classes.
       First, we prove that an untangled class is not a member of itself.
       (Contributed by Scott Fenton, 28-Feb-2011.) $)
    untelirr $p |- ( A. x e. A -. x e. x -> -. A e. A ) $=
      ( wel wn wral wcel cv wceq eleq1 eleq2 bitrd notbid rspccv pm2.01d ) AACZ
      DZABEBBFZPQDABBAGZBHZOQSOBRFQRBRIRBBJKLMN $.
  $}

  ${
    $d x y A $.
    $( The union of a class is untangled iff all its members are untangled.
       (Contributed by Scott Fenton, 28-Feb-2011.) $)
    untuni $p |- ( A. x e. U. A -. x e. x
        <-> A. y e. A A. x e. y -. x e. x ) $=
      ( cv cuni wcel wel wn wal wral wrex r19.23v albii ralcom4 eluni2 3bitr4ri
      wi imbi1i df-ral ralbii 3bitr4i ) ADZCEZFZAAGHZQZAIZABGZUEQZAIZBCJZUEAUCJ
      UEABDZJZBCJUIBCJZAIUHBCKZUEQZAIUKUGUNUPAUHUEBCLMUIBACNUFUPAUDUOUEBUBCORMP
      UEAUCSUMUJBCUEAULSTUA $.
  $}

  ${
    $d x A $.  $d x y $.
    untsucf.1 $e |- F/_ y A $.
    $( If a class is untangled, then so is its successor.  (Contributed by
       Scott Fenton, 28-Feb-2011.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)
    untsucf $p |- ( A. x e. A -. x e. x -> A. y e. suc A -. y e. y ) $=
      ( wel wn wral csuc nfv nfralw cv wcel wceq vex elsuc elequ1 elequ2 notbid
      wo bitrd rspccv untelirr eleq1 eleq2 syl5ibrcom jaod biimtrid ralrimi ) A
      AEZFZACGZBBEZFZBCHZUJBACDUJBIJBKZUNLUOCLZUOCMZSUKUMUOCBNOUKUPUMUQUJUMAUOC
      AKUOMZUIULURUIBAEULABAPABBQTRUAUKUMUQCCLZFACUBUQULUSUQULCUOLUSUOCUOUCUOCC
      UDTRUEUFUGUH $.
  $}

  $( The empty set is untangled.  (Contributed by Scott Fenton, 10-Mar-2011.)
     (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
  unt0 $p |- A. x e. (/) -. x e. x $=
    ( wel wn ral0 ) AABCAD $.

  ${
    $d x y A $.
    $( If there is an untangled element of a class, then the intersection of
       the class is untangled.  (Contributed by Scott Fenton, 1-Mar-2011.) $)
    untint $p |- ( E. x e. A A. y e. x -. y e. y ->
                    A. y e. |^| A -. y e. y ) $=
      ( wel wn cv wral cint wcel wss wi intss1 ssralv syl rexlimiv ) BBDEZBAFZG
      ZPBCHZGZACQCISQJRTKQCLPBSQMNO $.
  $}

  ${
    $d x A $.
    $( If ` A ` is well-founded by ` _E ` , then it is untangled.  (Contributed
       by Scott Fenton, 1-Mar-2011.) $)
    efrunt $p |- ( _E Fr A -> A. x e. A -. x e. x ) $=
      ( cep wfr cv wcel wn wa wbr frirr epel sylnib ralrimiva ) BCDZAEZOFZGABNO
      BFHOOCIPBOCJAOKLM $.
  $}

  ${
    $d x y A $.
    $( A transitive class is untangled iff its elements are.  (Contributed by
       Scott Fenton, 7-Mar-2011.) $)
    untangtr $p |- ( Tr A ->
                   ( A. x e. A -. x e. x <->
                     A. x e. A A. y e. x -. y e. y ) ) $=
      ( wtr wel wn wral cv cuni wss df-tr ssralv sylbi weq elequ1 elequ2 notbid
      wi bitrd cbvralvw untuni bitri imbitrdi untelirr ralimi impbid1 ) CDZAAEZ
      FZACGZBBEZFZBAHZGZACGZUGUJUIACIZGZUOUGUPCJUJUQRCKUIAUPCLMUQULBUPGUOUIULAB
      UPABNZUHUKURUHBAEUKABAOABBPSQTBACUAUBUCUNUIACBUMUDUEUF $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Extra propositional calculus theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    3jaodd.1 $e |- ( ph -> ( ps -> ( ch -> et ) ) ) $.
    3jaodd.2 $e |- ( ph -> ( ps -> ( th -> et ) ) ) $.
    3jaodd.3 $e |- ( ph -> ( ps -> ( ta -> et ) ) ) $.
    $( Double deduction form of ~ 3jaoi .  (Contributed by Scott Fenton,
       20-Apr-2011.) $)
    3jaodd $p |- ( ph -> ( ps -> ( ( ch \/ th \/ ta ) -> et ) ) ) $=
      ( w3o wi com3r 3jaoi com3l ) CDEJABFCABFKKDEABCFGLABDFHLABEFILMN $.
  $}

  $( Closed form of ~ 3ori .  (Contributed by Scott Fenton, 20-Apr-2011.) $)
  3orit $p |- ( ( ph \/ ps \/ ch ) <-> ( ( -. ph /\ -. ps ) -> ch ) ) $=
    ( w3o wo wn wi wa df-3or df-or ioran imbi1i 3bitri ) ABCDABEZCENFZCGAFBFHZC
    GABCINCJOPCABKLM $.

  $( A biconditional in the antecedent is the same as two implications.
     (Contributed by Scott Fenton, 12-Dec-2010.) $)
  biimpexp $p |- ( ( ( ph <-> ps ) -> ch )
                   <-> ( ( ph -> ps ) -> ( ( ps -> ph ) -> ch ) ) ) $=
    ( wb wi wa dfbi2 imbi1i impexp bitri ) ABDZCEABEZBAEZFZCELMCEEKNCABGHLMCIJ
    $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Misc. Useful Theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Two classes are unequal iff their intersection is a proper subset of one
     of them.  (Contributed by Scott Fenton, 23-Feb-2011.) $)
  nepss $p |- ( A =/= B <-> ( ( A i^i B ) C. A \/ ( A i^i B ) C. B ) ) $=
    ( wne cin wss wa wo wpss wceq nne neeq1 biimprcd biimtrid orrd jctl necon3i
    wn inidm adantl df-pss inss1 inss2 orim12i ineq2 eqtr3di eqtrdi jaoi impbii
    syl ineq1 orbi12i bitr4i ) ABCZABDZAEZUNACZFZUNBEZUNBCZFZGZUNAHZUNBHZGUMVAU
    MUPUSGVAUMUPUSUPQUNAIZUMUSUNAJVDUSUMUNABKLMNUPUQUSUTUPUOABUAOUSURABUBOUCUIU
    QUMUTUPUMUOABUNAABIZAADUNAABAUDARUEPSUSUMURABUNBVEUNBBDBABBUJBRUFPSUGUHVBUQ
    VCUTUNATUNBTUKUL $.

  ${
    3ccased.1 $e |- ( ph -> ( ( ch /\ et ) -> ps ) ) $.
    3ccased.2 $e |- ( ph -> ( ( ch /\ ze ) -> ps ) ) $.
    3ccased.3 $e |- ( ph -> ( ( ch /\ si ) -> ps ) ) $.
    3ccased.4 $e |- ( ph -> ( ( th /\ et ) -> ps ) ) $.
    3ccased.5 $e |- ( ph -> ( ( th /\ ze ) -> ps ) ) $.
    3ccased.6 $e |- ( ph -> ( ( th /\ si ) -> ps ) ) $.
    3ccased.7 $e |- ( ph -> ( ( ta /\ et ) -> ps ) ) $.
    3ccased.8 $e |- ( ph -> ( ( ta /\ ze ) -> ps ) ) $.
    3ccased.9 $e |- ( ph -> ( ( ta /\ si ) -> ps ) ) $.
    $( Triple disjunction form of ~ ccased .  (Contributed by Scott Fenton,
       27-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    3ccased $p |- ( ph -> ( ( ( ch \/ th \/ ta ) /\ ( et \/ ze \/ si ) ) ->
                     ps ) ) $=
      ( wa com12 3jaodan w3o wi 3jaoian ) CDEUAFGHUAZRABCUDABUBZDECFUEGHACFRBIS
      ACGRBJSACHRBKSTDFUEGHADFRBLSADGRBMSADHRBNSTEFUEGHAEFRBOSAEGRBPSAEHRBQSTUC
      S $.
  $}

  ${
    $d R x y z $.  $d A x y z $.
    $( Expansion of the definition of a strict order.  (Contributed by Scott
       Fenton, 6-Jun-2016.) $)
    dfso3 $p |- ( R Or A <->
       A. x e. A A. y e. A A. z e. A
       ( -. x R x /\
         ( ( x R y /\ y R z ) -> x R z ) /\
         ( x R y \/ x = y \/ y R x ) ) ) $=
      ( cv wbr wn wa wi weq w3o wral w3a wor wcel c0 wne wb ralbii r19.27zv syl
      ne0i ralbiia df-3an 2ralbii df-po anbi1i df-so r19.26-2 3bitr4i 3bitr4ri
      wpo ) AFZUNEGHZUNBFZEGZUPCFZEGIUNUREGJZIZUQABKUPUNEGLZIZCDMZBDMZADMUTCDMZ
      VAIZBDMZADMZUOUSVANZCDMZBDMADMDEOZVDVGADVCVFBDUPDPDQRVCVFSDUPUCUTVACDUAUB
      UDTVJVCABDDVIVBCDUOUSVAUETUFDEUMZVABDMADMZIVEBDMADMZVMIVKVHVLVNVMABCDEUGU
      HABDEUIVEVAABDDUJUKUL $.
  $}

  $( A binary relation involving unordered triples.  (Contributed by Scott
     Fenton, 7-Jun-2016.) $)
  brtpid1 $p |- A { <. A , B >. , C , D } B $=
    ( cop ctp wbr wcel opex tpid1 df-br mpbir ) ABABEZCDFZGMNHMCDABIJABNKL $.

  $( A binary relation involving unordered triples.  (Contributed by Scott
     Fenton, 7-Jun-2016.) $)
  brtpid2 $p |- A { C , <. A , B >. , D } B $=
    ( cop ctp wbr wcel opex tpid2 df-br mpbir ) ABCABEZDFZGMNHCMDABIJABNKL $.

  $( A binary relation involving unordered triples.  (Contributed by Scott
     Fenton, 7-Jun-2016.) $)
  brtpid3 $p |- A { C , D , <. A , B >. } B $=
    ( cop ctp wbr wcel opex tpid3 df-br mpbir ) ABCDABEZFZGMNHCDMABIJABNKL $.

  ${
    $d x V $.  $d A y $.  $d ps y $.  $d x y $.
    iota5f.1 $e |- F/ x ph $.
    iota5f.2 $e |- F/_ x A $.
    iota5f.3 $e |- ( ( ph /\ A e. V ) -> ( ps <-> x = A ) ) $.
    $( A method for computing iota.  (Contributed by Scott Fenton,
       13-Dec-2017.) $)
    iota5f $p |- ( ( ph /\ A e. V ) -> ( iota x ps ) = A ) $=
      ( vy wcel wa cv wceq wb wal cio nfel1 nfan wi eqeq2 alrimi bibi2d imbi12d
      weq nfeq2 albid iotaval vtoclg adantl mpd ) ADEJZKZBCLZDMZNZCOZBCPZDMZULU
      OCAUKCFCDEGQRHUAUKUPURSZABCIUDZNZCOZUQILZMZSUSIDEVCDMZVBUPVDURVEVAUOCCVCD
      GUEVEUTUNBVCDUMTUBUFVCDUQTUCBCIUGUHUIUJ $.
  $}

  $( Closed form of ~ ja .  Proved using the completeness script.
     (Proof modification is discouraged.)  (Contributed by Scott Fenton,
     13-Dec-2021.) $)
  jath $p |- ( ( -. ph -> ch ) -> ( ( ps -> ch ) ->
  ( ( ph -> ps ) -> ch ) ) ) $=
    ( wn wi jcn pm2.21 imim2 ax-mp ax-1 pm2.61 ) ADZLCEZBCEZABEZCEZEZEZEZRLCDZR
    EZEZSLTMDZEZEZUBLCFUDUAEZUEUBEUCREUFMQGUCRTHIUDUALHIIUAREZUBSECREZUGCQEZUHC
    PEZUICOJPQEZUJUIEPNJZPQCHIIQREZUIUHEQMJZQRCHIICRKIZUARLHIIAREZSREABDZREZEZU
    PAUQQEZEZUSAUQPEZEZVAAUQODZEZEZVCABFVEVBEZVFVCEVDPEVGOCGVDPUQHIVEVBAHIIVBUT
    EZVCVAEUKVHULPQUQHIVBUTAHIIUTUREZVAUSEUMVIUNQRUQHIUTURAHIIURREZUSUPEBREZVJB
    UAEZVKBTQEZEZVLBTNDZEZEZVNBCFVPVMEZVQVNEVOQEVRNPGVOQTHIVPVMBHIIVMUAEZVNVLEU
    MVSUNQRTHIVMUABHIIUGVLVKEUOUARBHIIBRKIURRAHIIARKII $.

  ${
    $d a b $.  $d a ph $.  $d a ps $.  $d a x $.  $d a y $.  $d b ph $.
    $d b ps $.  $d b x $.  $d b y $.  $d ph y $.  $d ps x $.  $d x y $.
    $( Cartesian product of two class abstractions.  (Contributed by Scott
       Fenton, 19-Aug-2024.) $)
    xpab $p |- ( { x | ph } X. { y | ps } ) = { <. x , y >. | ( ph /\ ps ) } $=
      ( va vb cab cxp wa copab wcel wsbc wbr wsb df-clab sban sbsbc sbv 3bitr3i
      cv relxp relopabv anbi12i anbi1i sbbii anbi2i bitri bitr4i brabsb 3bitr4i
      brxp eqid eqbrriv ) EFACGZBDGZHZABIZCDJZUNUOUAUQCDUBETZUNKZFTZUOKZIZUQDVA
      LZCUSLZUSVAUPMUSVAURMVCACENZBDFNZIZVEUTVFVBVGAECOBFDOUCVDCENAVGIZCENZVEVH
      VDVICEUQDFNADFNZVGIVDVIABDFPUQDFQVKAVGADFRUDSUEVDCEQVJVFVGCENZIVHAVGCEPVL
      VGVFVGCERUFUGSUHUSVAUNUOUKUQCDUSVAURURULUIUJUM $.
  $}

  ${
    $d A x $.
    $( The union of a finite ordinal is a finite ordinal.  (Contributed by
       Scott Fenton, 17-Oct-2024.) $)
    nnuni $p |- ( A e. _om -> U. A e. _om ) $=
      ( vx com wcel c0 wceq cv csuc wrex cuni nn0suc unieq uni0 eqtrdi eqeltrdi
      wo peano1 word nnord syl ordunisuc id eqeltrd eleq1d syl5ibrcom rexlimiv
      jaoi ) ACDAEFZABGZHZFZBCIZPAJZCDZBAKUHUNULUHUMECUHUMEJEAELMNQOUKUNBCUICDZ
      UNUKUJJZCDUOUPUICUOUIRUPUIFUISUIUATUOUBUCUKUMUPCAUJLUDUEUFUGT $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Properties of real and complex numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    sqdivzi.1 $e |- A e. CC $.
    sqdivzi.2 $e |- B e. CC $.
    $( Distribution of square over division.  (Contributed by Scott Fenton,
       7-Jun-2013.) $)
    sqdivzi $p |- ( B =/= 0 ->
            ( ( A / B ) ^ 2 ) = ( ( A ^ 2 ) / ( B ^ 2 ) ) ) $=
      ( cc0 wne cdiv co c2 cexp c1 cif oveq2 oveq1d oveq1 oveq2d eqeq12d ax-1cn
      wceq cc ifcli elimne0 sqdivi dedth ) BEFZABGHZIJHZAIJHZBIJHZGHZSAUEBKLZGH
      ZIJHZUHUKIJHZGHZSBKBUKSZUGUMUJUOUPUFULIJBUKAGMNUPUIUNUHGBUKIJOPQAUKCUEBKT
      DRUABUBUCUD $.
  $}

  ${
    $d N x $.  $d M x $.
    $( The supremum of a finite sequence of integers.  (Contributed by Scott
       Fenton, 8-Aug-2013.) $)
    supfz $p |- ( N e. ( ZZ>= ` M ) -> sup ( ( M ... N ) , ZZ , < ) = N ) $=
      ( vx cuz cfv wcel cz cfz co clt wor cr wss zssre ltso mp2 a1i eluzelz wbr
      soss eluzfz2 cv wa cle wn elfzle2 adantl wb elfzelz zred eluzelre syl2anr
      lenlt mpbid supmax ) BADEFZCGABHIZBJGJKZUPGLMLJKURNOGLJTPQABRABUAUPCUBZUQ
      FZUCUSBUDSZBUSJSUEZUTVAUPUSABUFUGUTUSLFBLFVAVBUHUPUTUSUSABUIUJABUKUSBUMUL
      UNUO $.

    $( The infimum of a finite sequence of integers.  (Contributed by Scott
       Fenton, 8-Aug-2013.)  (Revised by AV, 10-Oct-2021.) $)
    inffz $p |- ( N e. ( ZZ>= ` M ) -> inf ( ( M ... N ) , ZZ , < ) = M ) $=
      ( vx cuz cfv wcel cz cfz co clt wor wss zssre ltso soss mp2 a1i wbr zred
      cr eluzel2 eluzfz1 cv wa cle wn elfzle1 adantl elfzelz lenlt syl2an mpbid
      wb infmin ) BADEFZCGABHIZAJGJKZUOGTLTJKUQMNGTJOPQABUAZABUBUOCUCZUPFZUDAUS
      UERZUSAJRUFZUTVAUOUSABUGUHUOATFUSTFVAVBUMUTUOAURSUTUSUSABUISAUSUJUKULUN
      $.
  $}

  $( The sequence ` ( 0 ... ( N - 1 ) ) ` is empty iff ` N ` is zero.
     (Contributed by Scott Fenton, 16-May-2014.) $)
  fz0n $p |- ( N e. NN0 -> ( ( 0 ... ( N - 1 ) ) = (/) <-> N = 0 ) ) $=
    ( cn0 wcel c1 cmin co cc0 clt wbr cfz c0 wceq cz wb nn0z sylancr cle bitr3d
    0z cr peano2zm syl fzn cn wo elnn0 wn nnge1 1re wa subge0 0re resubcl lenlt
    nnre sylancl mpbid nnne0 neneqd 2falsed cneg oveq1 eqtr4di neg1lt0 eqbrtrdi
    df-neg id 2thd jaoi sylbi ) ABCZADEFZGHIZGVLJFKLZAGLZVKGMCVLMCZVMVNNSVKAMCV
    PAOAUAUBGVLUCPVKAUDCZVOUEVMVONZAUFVQVRVOVQVMVOVQDAQIZVMUGZAUHVQATCZDTCZVSVT
    NAUOUIWAWBUJZGVLQIZVSVTADUKWCGTCVLTCWDVTNULADUMGVLUNPRUPUQVQAGAURUSUTVOVMVO
    VOVLDVAZGHVOVLGDEFWEAGDEVBDVFVCVDVEVOVGVHVIVJR $.

  ${
    $d F f $.  $d A f $.  $d B f $.
    $( Value of a sequence shifted by ` A ` .  (Contributed by Scott Fenton,
       16-Dec-2017.) $)
    shftvalg $p |- ( ( F e. V /\ A e. CC /\ B e. CC ) ->
      ( ( F shift A ) ` B ) = ( F ` ( B - A ) ) ) $=
      ( vf wcel cc cshi co cmin wceq wa cv wi oveq1 fveq1d fveq1 eqeq12d imbi2d
      cfv vex shftval vtoclg 3impib ) CDFAGFZBGFZBCAHIZTZBAJIZCTZKZUEUFLZBEMZAH
      IZTZUIUMTZKZNULUKNECDUMCKZUQUKULURUOUHUPUJURBUNUGUMCAHOPUIUMCQRSABUMEUAUB
      UCUD $.
  $}

  ${
    $d A k $.  $d A m $.  $d B k $.  $d B m $.  $d F k $.  $d k m $.
    $d k ph $.  $d M k $.  $d m ph $.  $d Z k $.
    divcnvlin.1 $e |- Z = ( ZZ>= ` M ) $.
    divcnvlin.2 $e |- ( ph -> M e. ZZ ) $.
    divcnvlin.3 $e |- ( ph -> A e. CC ) $.
    divcnvlin.4 $e |- ( ph -> B e. ZZ ) $.
    divcnvlin.5 $e |- ( ph -> F e. V ) $.
    divcnvlin.6 $e |- ( ( ph /\ k e. Z ) ->
        ( F ` k ) = ( ( k + A ) / ( k + B ) ) ) $.
    $( Limit of the ratio of two linear functions.  (Contributed by Scott
       Fenton, 17-Dec-2017.) $)
    divcnvlin $p |- ( ph -> F ~~> 1 ) $=
      ( vm c1 co caddc cn wcel cli wbr cz cv cmin cdiv cmpt cc0 wa cc nncn zcnd
      adantl subcld adantr wne nnne0 divdird dividd oveq1d eqtrd mpteq2dva nnuz
      cvv 1zzd divcnv syl 1cnd nnex mptex a1i divcld fmpttd ffvelcdmda cfv wceq
      weq oveq2 oveq2d eqid ovex fvmpt eqtr4d climaddc2 eqbrtrd cuz cres resmpt
      wss nnssz ax-mp reseq2i eqtr3i 1p0e1 breq12i wb climres mp2an bitri sylib
      zex eluzelz eleq2s ppncand zaddcld oveq1 oveq12d 3eqtr4d climshft2 mpbird
      1z id ) AEPUAUBOUCOUDZBCUEQZRQZXMUFQZUGZPUAUBZAOSXPUGZPUHRQZUAUBZXRAXSOSP
      XNXMUFQZRQZUGZXTUAAOSXPYCAXMSTZUIZXPXMXMUFQZYBRQYCYFXMXNXMYEXMUJTAXMUKUMZ
      AXNUJTZYEABCKACLULUNZUOZYHYEXMUHUPAXMUQUMZURYFYGPYBRYFXMYHYLUSUTVAVBAUHPD
      OSYBUGZYDPVDSVCAVEAYIYMUHUAUBYJXNOVFVGAVHYDVDTAOSYCVIVJVKASUJDUDZYMAOSYBU
      JYFXNXMYKYHYLVLVMVNYNSTZYNYDVOZPYNYMVOZRQZVPAYOYPPXNYNUFQZRQZYROYNYCYTSYD
      ODVQYBYSPRXMYNXNUFVRZVSYDVTPYSRWAWBYOYQYSPROYNYBYSSYMUUAYMVTXNYNUFWAWBVSW
      CUMWDWEYAXQPWFVOZWGZPUAUBZXRXSUUCXTPUAXQSWGZXSUUCSUCWIUUEXSVPWJOUCSXPWHWK
      SUUBXQVCWLWMWNWOPUCTXQVDTZUUDXRWPXKOUCXPXAVJZPXQPVDWQWRWSWTAPDEXQCFGVDHIJ
      LMUUFAUUGVKAYNHTZUIZYNCRQZXNRQZUUJUFQZYNBRQZUUJUFQUUJXQVOZYNEVOUUIUUKUUMU
      UJUFUUIYNCBUUHYNUJTAUUHYNYNUCTZYNFWFVOHFYNXBIXCZULUMUUICACUCTUUHLUOZULABU
      JTUUHKUOXDUTUUIUUJUCTUUNUULVPUUIYNCUUHUUOAUUPUMUUQXEOUUJXPUULUCXQXMUUJVPZ
      XOUUKXMUUJUFXMUUJXNRXFUURXLXGXQVTUUKUUJUFWAWBVGNXHXIXJ $.
  $}

  ${
    $d A k $.  $d B k $.  $d F k $.  $d F m $.  $d k m $.  $d k ph $.
    $d M k $.  $d Z k $.  $d Z m $.
    climlec3.1 $e |- Z = ( ZZ>= ` M ) $.
    climlec3.2 $e |- ( ph -> M e. ZZ ) $.
    climlec3.3 $e |- ( ph -> B e. RR ) $.
    climlec3.4 $e |- ( ph -> F ~~> A ) $.
    climlec3.5 $e |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR ) $.
    climlec3.6 $e |- ( ( ph /\ k e. Z ) -> ( F ` k ) <_ B ) $.
    $( Comparison of a constant to the limit of a sequence.  (Contributed by
       Scott Fenton, 5-Jan-2018.) $)
    climlec3 $p |- ( ph -> A <_ B ) $=
      ( vm cle wbr cneg cfv cc0 wcel cv cmpt renegcld cmin co cli cvv cuz fvexi
      0cnd mptex a1i wa recnd eqid weq fveq2 negeqd simpr fvmptd3 df-neg eqtrdi
      climsubc2 breqtrrdi adantr lenegd mpbid breqtrrd climlec2 climrecl mpbird
      cr eqeltrd ) ABCOPCQZBQZOPAVNVODNGNUAZERZQZUBZFGHIACJUCAVSSBUDUEVOUFABSDE
      VSFUGGHIKAUJVSUGTANGVRGFUHHUIUKULADUAZGTZUMZVTERZLUNWBVTVSRZWCQZSWCUDUEWB
      NVTVRWEGVSVLVSUONDUPVQWCVPVTEUQURAWAUSWBWCLUCZUTZWCVAVBVCBVAVDWBWDWEVLWGW
      FVMWBVNWEWDOWBWCCOPVNWEOPMWBWCCLACVLTWAJVEVFVGWGVHVIABCABDEFGHIKLVJJVFVK
      $.
  $}

  $( ` _i ` raised to itself is real.  (Contributed by Scott Fenton,
     13-Apr-2020.) $)
  iexpire $p |- ( _i ^c _i ) e. RR $=
    ( ci ccxp co c1 cneg cpi c2 cdiv cmul ce cfv cr clog cc wcel cc0 wne ax-icn
    wceq halfpire ine0 cxpef mp3an logi oveq2i recni mulassi ixi oveq1i 3eqtr2i
    fveq2i eqtri neg1rr remulcli reefcl ax-mp eqeltri ) AABCZDEZFGHCZICZJKZLURA
    AMKZICZJKZVBANOZAPQVFURVESRUARAAUBUCVDVAJVDAAUTICZICAAICZUTICVAVCVGAIUDUEAA
    UTRRUTTUFUGVHUSUTIUHUIUJUKULVALOVBLOUSUTUMTUNVAUOUPUQ $.

  $( The binomial coefficient over negative one is zero.  (Contributed by Scott
     Fenton, 29-May-2020.) $)
  bcneg1 $p |- ( N e. NN0 -> ( N _C -u 1 ) = 0 ) $=
    ( cn0 wcel c1 cneg cbc co cc0 cfz cfa cfv cmin cmul cdiv cif wceq neg1z cle
    cz wbr bcval mpan2 wa clt wn neg1lt0 neg1rr 0re ltnlei mpbi intnanr wb nn0z
    0z elfz mp3an12 syl mtbiri iffalsed eqtrd ) ABCZADEZFGZVBHAIGCZAJKAVBLGJKVB
    JKMGNGZHOZHVAVBSCZVCVFPQVBAUAUBVAVDVEHVAVDHVBRTZVBARTZUCZVHVIVBHUDTVHUEUFVB
    HUGUHUIUJUKVAASCZVDVJULZAUMVGHSCVKVLQUNVBHAUOUPUQURUSUT $.

  $( The proportion of one binomial coefficient to another with ` N ` decreased
     by 1.  (Contributed by Scott Fenton, 23-Jun-2020.) $)
  bcm1nt $p |- ( ( N e. NN /\ K e. ( 0 ... ( N - 1 ) ) ) ->
    ( N _C K ) = ( ( ( N - 1 ) _C K ) x. ( N / ( N - K ) ) ) ) $=
    ( cn wcel cc0 c1 cmin co cfz wa caddc cbc cdiv cmul wceq bcp1n adantl simpl
    nncnd oveq1d 1cnd npcand oveq12d oveq2d 3eqtr3d ) BCDZAEBFGHZIHDZJZUGFKHZAL
    HZUGALHZUJUJAGHZMHZNHZBALHULBBAGHZMHZNHUHUKUOOUFAUGPQUIUJBALUIBFUIBUFUHRSUI
    UAUBZTUIUNUQULNUIUJBUMUPMURUIUJBAGURTUCUDUE $.

  ${
    $d N n m j k $.
    $( A product identity for binomial coefficients.  (Contributed by Scott
       Fenton, 23-Jun-2020.) $)
    bcprod $p |- ( N e. NN ->
     prod_ k e. ( 1 ... ( N - 1 ) ) ( ( N - 1 ) _C k ) =
     prod_ k e. ( 1 ... ( N - 1 ) ) ( k ^ ( ( 2 x. k ) - N ) ) ) $=
      ( c1 cmin co cfz cbc cprod cmul cexp wceq oveq2d oveq1d adantr prodeq12dv
      c2 wcel cn cdiv nncnd vm vn vj cv cc0 caddc oveq1 1m1e0 eqtrdi fz10 oveq2
      c0 eqeq12d weq prod0 eqtr4i wa cfa cfv nncn 1cnd pncand cuz elnnuz biimpi
      simpr cn0 nnnn0 elfzelz bccl syl2an nn0cnd fprodm1 bcnn syl fzfid fprodcl
      cz mulridd fz1ssfz0 bcm1nt sylan2 prodeq2dv nnm1nn0 clt wbr elfznn adantl
      sseli cc nnred nn0red cr cle elfzle2 ltm1d lelttrd wb simpl nnsub syl2anc
      nnre mpbid nnne0d divcld fprodmul fproddiv chash cfn fzfi sylancr hashfz1
      fprodconst eqtr2d fprodfac nnz 1zzd nn0zd fprodrev nncand prodeq1d 3eqtrd
      id oveq12d eqtr4d 2nn a1i nnmulcld nnzd peano2nn zsubcld expclzd subsub4d
      expm1d eqtr3d 3eqtr4d 2timesd mvrladdd faccl expcld div32d eqtrd ex nnind
      ) CUAUDZCDEZFEZUUFAUDZGEZAHZUUGUUHPUUHIEZUUEDEZJEZAHZKULUEUUHGEZAHZULUUHU
      UKCDEZJEZAHZKCUBUDZCDEZFEZUVAUUHGEZAHZUVBUUHUUKUUTDEZJEZAHZKZCUUTCUFEZCDE
      ZFEZUVJUUHGEZAHZUVKUUHUUKUVIDEZJEZAHZKZCBCDEZFEZUVRUUHGEZAHZUVSUUHUUKBDEZ
      JEZAHZKUAUBBUUECKZUUJUUPUUNUUSUWEUUGULUUIUUOAUWEUUGCUEFEULUWEUUFUECFUWEUU
      FCCDEUEUUECCDUGUHUIZLUJUIZUWEUUIUUOKUUHUUGQZUWEUUFUEUUHGUWFMNOUWEUUGULUUM
      UURAUWGUWEUUMUURKUWHUWEUULUUQUUHJUUECUUKDUKLNOUMUAUBUNZUUJUVDUUNUVGUWIUUG
      UVBUUIUVCAUWIUUFUVACFUUEUUTCDUGZLZUWIUUIUVCKUWHUWIUUFUVAUUHGUWJMNOUWIUUGU
      VBUUMUVFAUWKUWIUUMUVFKUWHUWIUULUVEUUHJUUEUUTUUKDUKLNOUMUUEUVIKZUUJUVMUUNU
      VPUWLUUGUVKUUIUVLAUWLUUFUVJCFUUEUVICDUGZLZUWLUUIUVLKUWHUWLUUFUVJUUHGUWMMN
      OUWLUUGUVKUUMUVOAUWNUWLUUMUVOKUWHUWLUULUVNUUHJUUEUVIUUKDUKLNOUMUUEBKZUUJU
      WAUUNUWDUWOUUGUVSUUIUVTAUWOUUFUVRCFUUEBCDUGZLZUWOUUIUVTKUWHUWOUUFUVRUUHGU
      WPMNOUWOUUGUVSUUMUWCAUWQUWOUUMUWCKUWHUWOUULUWBUUHJUUEBUUKDUKLNOUMUUPCUUSU
      UOAUOUURAUOUPUUTRQZUVHUVQUWRUVHUQZUVDUUTUVAJEZUVAURUSZSEZIEZUVGUXBIEZUVMU
      VPUWSUVDUVGUXBIUWRUVHVFMUWRUVMUXCKUVHUWRUVMCUUTFEZUUTUUHGEZAHUVBUXFAHZUUT
      UUTGEZIEZUXCUWRUVKUXEUVLUXFAUWRUVJUUTCFUWRUUTCUUTUTZUWRVAZVBZLZUWRUVLUXFK
      UUHUVKQUWRUVJUUTUUHGUXLMNOUWRUXFUXHACUUTUWRUUTCVCUSQUUTVDVEZUWRUUHUXEQZUQ
      ZUXFUWRUUTVGQZUUHVRQZUXFVGQZUXOUUTVHZUUHCUUTVIUUHUUTVJZVKVLUUHUUTUUTGUKVM
      UWRUXIUXGCIEUXGUXCUWRUXHCUXGIUWRUXQUXHCKUXTUUTVNVOLUWRUXGUWRUVBUXFAUWRCUV
      AVPZUWRUUHUVBQZUQZUXFUWRUXQUXRUXSUYCUXTUUHCUVAVIZUYAVKVLVQVSUWRUXGUVBUVCU
      UTUUTUUHDEZSEZIEZAHUVDUVBUYGAHZIEUXCUWRUVBUXFUYHAUYCUWRUUHUEUVAFEZQUXFUYH
      KUVBUYJUUHUVAVTWIUUHUUTWAWBWCUWRUVBUVCUYGAUYBUYDUVCUWRUVAVGQZUXRUVCVGQUYC
      UUTWDZUYEUUHUVAVJVKVLUYDUUTUYFUWRUUTWJQZUYCUXJNZUYDUYFUYDUUHUUTWEWFZUYFRQ
      ZUYDUUHUVAUUTUYDUUHUYCUUHRQZUWRUUHUVAWGWHZWKUYDUVAUWRUYKUYCUYLNWLUWRUUTWM
      QUYCUUTXBNZUYCUUHUVAWNWFUWRUUHCUVAWOWHUYDUUTUYSWPWQUYDUYQUWRUYOUYPWRUYRUW
      RUYCWSUUHUUTWTXAXCZTZUYDUYFUYTXDZXEXFUWRUYIUXBUVDIUWRUYIUVBUUTAHZUVBUYFAH
      ZSEUXBUWRUVBUUTUYFAUYBUYNVUAVUBXGUWRUWTVUCUXAVUDSUWRVUCUUTUVBXHUSZJEZUWTU
      WRUVBXIQUYMVUCVUFKCUVAXJUXJUVBUUTAXMXKUWRVUEUVAUUTJUWRUYKVUEUVAKUYLUVAXLV
      OLXNUWRUXAUVBUCUDZUCHZUUTUVADEZUVAFEZUYFAHVUDUWRUYKUXAVUHKUYLUVAUCXOVOUWR
      VUGUYFUCAUUTCUVAUUTXPZUWRXQUWRUVAUYLXRUWRVUGUVBQZUQVUGVULVUGRQUWRVUGUVAWG
      WHTVUGUYFKYCXSUWRVUJUVBUYFAUWRVUICUVAFUWRUUTCUXJUXKXTMYAYBYDYELYBYBYBNUWR
      UVPUXDKUVHUWRUVPUXEUVOAHUVBUVOAHZUUTPUUTIEZUVIDEZJEZIEZUXDUWRUVKUXEUVOAUX
      MYAUWRUVOVUPACUUTUXNUXPUUHUVNUXPUUHUXOUYQUWRUUHUUTWGWHZTUXPUUHVURXDUXPUUK
      UVIUXPUUKUXPPUUHPRQZUXPYFYGVURYHYIUXPUVIUWRUVIRQUXOUUTYJNYIYKYLAUBUNZUUHU
      UTUVNVUOJVUTYCVUTUUKVUNUVIDUUHUUTPIUKMYDVMUWRVUQUVGUXASEZUWTIEUXDUWRVUMVV
      AVUPUWTIUWRUVBUVFUUHSEZAHUVGUVBUUHAHZSEVUMVVAUWRUVBUVFUUHAUYBUYDUUHUVEUYD
      UUHUYRTZUYDUUHUYRXDZUYDUUKUUTUYDUUKUYDPUUHVUSUYDYFYGUYRYHZYIUWRUUTVRQUYCV
      UKNYKZYLZVVDVVEXGUWRUVBUVOVVBAUYDUUHUVECDEZJEUVOVVBUYDVVIUVNUUHJUYDUUKUUT
      CUYDUUKVVFTUYNUYDVAYMLUYDUUHUVEVVDVVEVVGYNYOWCUWRUXAVVCUVGSUWRUYKUXAVVCKU
      YLUVAAXOVOLYPUWRVUOUVAUUTJUWRVUNUUTDEZCDEVUOUVAUWRVUNUUTCUWRVUNUWRPUUTVUS
      UWRYFYGUWRYCYHTUXJUXKYMUWRVVJUUTCDUWRVUNUUTUUTUXJUXJUWRUUTUXJYQYRMYOLYDUW
      RUVGUXAUWTUWRUVBUVFAUYBVVHVQUWRUXAUWRUYKUXARQUYLUVAYSVOZTUWRUUTUVAUXJUYLY
      TUWRUXAVVKXDUUAUUBYBNYPUUCUUD $.
  $}

  ${
    $d N n m k $.  $d C n m k $.
    $( A column-sum rule for binomial coefficients.  (Contributed by Scott
       Fenton, 24-Jun-2020.) $)
    bccolsum $p |- ( ( N e. NN0 /\ C e. NN0 ) ->
    sum_ k e. ( 0 ... N ) ( k _C C ) = ( ( N + 1 ) _C ( C + 1 ) ) ) $=
      ( cn0 wcel cc0 cfz co cbc csu c1 caddc wceq wi oveq2 sumeq1d oveq1 oveq1d
      eqeq12d imbi2d vm vn cv 0p1e1 eqtrdi weq cz 0nn0 nn0z bccl sylancr nn0cnd
      cc 0z fsum1 cn wo elnn0 cfa cfv cmin cmul cdiv cif cle wbr 1red ltaddrp2d
      wn nnrp peano2nn nnred ltnled mpbid elfzle2 nsyl iffalsed 1nn0 nnzd bcval
      clt bc0k 3eqtr4rd bcnn ax-mp eqtr4i oveq2d 3eqtr4a sylbi eqtrd wa elnn0uz
      jaoi cuz birani elfznn0 adantl simplr nn0zd syl2anc fsump1 adantr id 1cnd
      nn0cn pncand eqcomd oveqan12rd peano2nn0 bcpasc syl2an 3eqtrd a2d nn0ind
      exp31 imp ) CDEADEZFCGHZBUCZAIHZBJZCKLHZAKLHZIHZMZXQFUAUCZGHZXTBJZYFKLHZY
      CIHZMZNXQFFGHZXTBJZKYCIHZMZNXQFUBUCZGHZXTBJZYPKLHZYCIHZMZNXQFYSGHZXTBJZYS
      KLHZYCIHZMZNXQYENUAUBCYFFMZYKYOXQUUGYHYMYJYNUUGYGYLXTBYFFFGOPUUGYIKYCIUUG
      YIFKLHZKYFFKLQUDUERSTUAUBUFZYKUUAXQUUIYHYRYJYTUUIYGYQXTBYFYPFGOPUUIYIYSYC
      IYFYPKLQRSTYFYSMZYKUUFXQUUJYHUUCYJUUEUUJYGUUBXTBYFYSFGOPUUJYIUUDYCIYFYSKL
      QRSTYFCMZYKYEXQUUKYHYAYJYDUUKYGXRXTBYFCFGOPUUKYIYBYCIYFCKLQRSTXQYMFAIHZYN
      XQFUGEUULUMEYMUULMUNXQUULXQFDEZAUGEZUULDEUHAUIAFUJUKULXTUULBFXSFAIQUOUKXQ
      AUPEZAFMZUQUULYNMZAURUUOUUQUUPUUOYCFKGHEZKUSUTKYCVAHUSUTYCUSUTVBHVCHZFVDZ
      FYNUULUUOUURUUSFUUOYCKVEVFZUURUUOKYCWAVFUVAVIUUOKAUUOVGZAVJVHUUOKYCUVBUUO
      YCAVKZVLVMVNYCFKVOVPVQUUOKDEZYCUGEZYNUUTMVRUUOYCUVCVSYCKVTUKAWBWCUUPFFIHZ
      KKIHZUULYNUVFKUVGUUMUVFKMUHFWDWEUVDUVGKMVRKWDWEWFAFFIOUUPYCKKIUUPYCUUHKAF
      KLQUDUEWGWHWMWIWJYPDEZXQUUAUUFUVHXQUUAUUFUVHXQWKZUUAWKUUCYRYSAIHZLHZYTYSY
      CKVAHZIHZLHZUUEUVIUUCUVKMUUAUVIXTUVJBFYPUVHYPFWNUTEXQYPWLWOUVIXSUUBEZWKZX
      TUVPXSDEZUUNXTDEUVOUVQUVIXSYSWPWQUVPAUVHXQUVOWRWSAXSUJWTULXSYSAIQXAXBUUAU
      VIYRYTUVJUVMLUUAXCUVIUVMUVJUVIUVLAYSIUVIAKXQAUMEUVHAXEWQUVIXDXFWGXGXHUVIU
      VNUUEMZUUAUVHYSDEUVEUVRXQYPXIXQYCAXIWSYCYSXJXKXBXLXOXMXNXP $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Infinite products
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $(
  @{
    @d A w x @. @d B w x @. @d C w x @. @d ph x @. @d R w x @.
    @d w z @. @d X w y @. @d x y @. @d x z @. @d X z @. @d Y w x @.
    ntrivcvgvaulem1.1 @e |- ( ( ph /\ x e. A ) ->
      E. y e. B A. z e. C Y R x ) @.
    @( Lemma for ~ ntrivcvgcau .  Specialization of a particular form
       while avoiding a distinctness requirement between ` x ` and ` X ` .
       (Contributed by Scott Fenton, 30-Dec-2017.) @)
    ntrivcvgcaulem1 @p |- ( ( ph /\ X e. A ) ->
      E. y e. B A. z e. C Y R X ) @=
      ( vw cv wbr wral wrex wcel breq2 ralbidv rexbidv ralrimiva weq sylib wceq
      cbvralv rspcv mpan9 ) AJLMZHNZDGOZCFPZLEOZIEQJIHNZDGOZCFPZAJBMZHNZDGOZCFP
      ZBEOULAUSBEKUAUSUKBLEBLUBZURUJCFUTUQUIDGUPUHJHRSTUEUCUKUOLIEUHIUDZUJUNCFV
      AUIUMDGUHIJHRSTUFUG @.
  @}

  @{
    ntrivcvgcaulem2.1 @e |- Z = ( ZZ>= `  M ) @.
    ntrivcvgcaulem2.2 @e |- ( ph -> K e. Z ) @.
    ntrivcvgcaulem2.3 @e |- ( ( ph /\ k e. Z ) -> A e. CC ) @.
    ntrivcvgcaulem2.4 @e |- ( ( ph /\ m e. ( ZZ>= ` K ) ) ->
       ( abs ` ( prod_ k e. ( K ... m ) A - 1 ) ) < ( 1 / 2 ) ) @.

    @{
      @d K k @. @d k m @. @d k ph @.
    @( Lemma for ~ ntrivcvgcau .  A product whose absolute difference
       from one is less than one half has an absolute value less than two.
       (Contributed by Scott Fenton, 30-Dec-2017.) @)
    ntrivcvgcaulem2 @p |- ( ( ph /\ m e. ( ZZ>= ` K ) ) ->
     ( abs ` prod_ k e. ( K ... m ) A ) < 2 ) @=
      ( cfv wcel co c1 caddc cabs c2 a1i cr cv cuz wa cfz cprod cmin clt elfzuz
      fzfid cc uztrn2 syl2an syldan adantlr fprodcl ax-1cn npcand fveq2d abscld
      eqeltrd subcld abs1 1re eqeltri readdcld 2re abstrid rereccli wbr halflt1
      cdiv 2ne0 lttrd ltadd1dd oveq2i df-2 3brtr4g lelttrd eqbrtrrd ) ADUAZEUBL
      ZMZUCZEVTUDNZBCUEZOUFNZOPNZQLZWEQLRUGWCWGWEQWCWEOWCWDBCWCEVTUIACUAZWDMZBU
      JMZWBAWJWIGMZWKAEGMWIWAMWLWJIWIEVTUHFWIEGHUKULJUMUNUOZOUJMWCUPSZUQZURWCWH
      WFQLZOQLZPNZRWCWGWCWGWEUJWOWMUTUSWCWPWQWCWFWCWEOWMWNVAZUSZWQTMWCWQOTVBVCV
      DSVERTMWCVFSWCWFOWSWNVGWCWPOPNOOPNWRRUGWCWPOOWTOTMWCVCSZXAWCWPORVKNZOWTXB
      TMWCRVFVLVHSXAKXBOUGVIWCVJSVMVNWQOWPPVBVOVPVQVRVS @.
    @}

    @{
      @d A m @. @d K k @. @d k m @. @d K m @. @d k ph @. @d m ph @.
    @( Lemma for ~ ntrivcvgcau .  A product whose absolute difference from
       one is less than one half has no zero values.  (Contributed
       by Scott Fenton, 30-Dec-2017.) @)
    ntrivcvgcaulem3 @p |- ( ( ph /\ k e. ( ZZ>= ` K ) ) -> A =/= 0 ) @=
      ( cfv wcel cc0 wceq co c1 cmin cabs clt cv cuz wne csb wi wa cfz cprod c2
      wral cdiv wbr fzfid elfzuz uztrn2 syl2an syldan fprodcl adantr ax-1cn a1i
      cc subcld abscld cr 2re 2ne0 rereccli ltnsymd halflt1 cneg absnegi df-neg
      fveq2i abs1 3eqtr3i breqtrri oveq1 fveq2d breqtrrid nsyl adantlr fprodm1s
      cmul simpr oveq2 sylan9eqr eqtrd mtand neqned ralrimiva nfv nfcsb1v nfcv
      mul01d nfne weq csbeq1a neeq1d cbvral rsp sylbir syl imp ) ACUAZEUBLZMZBN
      UCZACDUAZBUDZNUCZDXFUJZXGXHUEZAXKDXFAXIXFMZUFZXJNXOXJNOZEXIUGPZBCUHZNOZXO
      QUIUKPZXRQRPZSLZTULXSXOYBXTXOYAXOXRQAXRVBMXNAXQBCAEXIUMAXEXQMZXEGMZBVBMZA
      EGMZXGYDYCIXEEXIUNFXEEGHUOZUPJUQZURUSQVBMXOUTVAVCVDXTVEMXOUIVFVGVHVAKVIXS
      XTNQRPZSLZYBTXTQYJTVJQVKZSLQSLYJQQUTVLYKYISQVMVNVOVPVQXSYAYISXRNQRVRVSVTW
      AXOXPUFXREXIQRPZUGPZBCUHZXJWDPZNXOXRYOOXPXOBCEXIAXNWEAYCYEXNYHWBWCUSXPXOY
      OYNNWDPNXJNYNWDWFXOYNXOYMBCXOEYLUMAXEYMMZYEXNAYPYDYEAYFXGYDYPIXEEYLUNYGUP
      JUQWBURWOWGWHWIWJWKXLXHCXFUJXMXHXKCDXFXHDWLCXJNCXIBWMCNWNWPCDWQBXJNCXIBWR
      WSWTXHCXFXAXBXCXD @.
    @}

    ntrivcvgcaulem4.5 @e |- ( ( ph /\ x e. RR+ ) ->
      E. n e. Z A. q e. ( ZZ>= ` n )
       ( abs ` ( prod_ k e. ( n ... q ) A - 1 ) ) < x ) @.

    ntrivcvgcaulem4 @p |- ( ( ph /\ x e. RR+ ) ->
      E. j e. ( ZZ>= ` K ) A. p e. ( ZZ>= ` j )
      ( abs ` ( prod_ k e. ( ( j + 1 ) ... p ) A - 1 ) ) < ( x / 2 ) ) @= ? @.

    @{
    @d j p @. @d j ph @. @d j x @. @d K p @. @d p ph @. @d p x @. @d A m @.
    @d j k @. @d j m @. @d K k @. @d k m @. @d K m @. @d k p @. @d k ph @.
    @d k x @. @d m ph @.

    @( Lemma for ~ ntrivcvgcau .  Translate final hypothesis into
       a Cauchy-like criterion.  (Contributed by Scott Fenton, 30-Dec-2017.) @)
    ntrivcvgcaulem5 @p |- ( ( ph /\ x e. RR+ ) ->
     E. j e. Z A. p e. ( ZZ>= ` j )
       ( abs ` ( prod_ k e. ( K ... p ) A - prod_ k e. ( K ... j ) A ) )
                 < x ) @=
      ( wcel wa co cv crp c1 caddc cfz cprod cmin cabs cfv c2 cdiv clt wbr wral
      cuz wrex ntrivcvgcaulem4 wss eleqtrdi uzss sseqtrrdi adantr sseld adantrd
      syl wi w3a cmul fzfid simplll simpll elfzuz uztrn2 syl2an syl2anc fprodcl
      cr cc abscld 3adant3 simpl peano2uzs ax-1cn subcld simplr rphalfcld rpred
      2re a1i cc0 cle absge0d simprl eleq1 anbi2d prodeq1d oveq1d fveq2d breq1d
      weq oveq2 imbi12d chvarv ntrivcvgcaulem2 simp3 ltmul12ad wceq c0 eluzelre
      cin ad2antrl fzdisj cun simprr elfzuzb sylanbrc fzsplit fprodsplit muls1d
      ltp1d eqtr4d absmuld eqtr2d simp1r rpcn 2cn 2ne0 divcan2d 3brtr3d anassrs
      wne 3expia ralimdva expimpd jcad reximdv2 mpd ) ABUAZUBRZSZDUAZUCUDTZLUAZ
      UETZCEUFZUCUGTZUHUIZYRUJUKTZULUMZLUUAUOUIZUNZDHUOUIZUPHUUCUETZCEUFZHUUAUE
      TZCEUFZUGTZUHUIZYRULUMZLUUJUNZDJUPABCDEFGHIJKLMNOPQUQYTUUKUUTDUULJYTUUAUU
      LRZUUKSUUAJRZUUTYTUVAUVBUUKYTUULJUUAAUULJURYSAUULIUOUIZJAHUVCRUULUVCURAHJ
      UVCNMUSIHUTVEMVAVBVCVDYTUVAUUKUUTYTUVASUUIUUSLUUJYTUVAUUCUUJRZUUIUUSVFYTU
      VAUVDSZUUIUUSYTUVEUUIVGZUUPUHUIZUUGVHTZUJUUHVHTZUURYRULUVFUVGUJUUGUUHYTUV
      EUVGVQRUUIYTUVESZUUPUVJUUOCEUVJHUUAVIUVJEUAZUUORZSAUVKJRZCVRRZAYSUVEUVLVJ
      UVJHJRZUVKUULRZUVMUVLUVJAUVOAYSUVEVKZNVEZUVKHUUAVLIUVKHJMVMZVNOVOVPZVSVTU
      JVQRUVFWHWIYTUVEUUGVQRUUIUVJUUFUVJUUEUCUVJUUDCEUVJUUBUUCVIUVJUVKUUDRZSAUV
      MUVNAYSUVEUWAVJUVJUUBJRZUVKUUBUOUIRUVMUWAUVJUVBUWBYTUVOUVAUVBUVEAUVOYSNVB
      UVAUVDWAIUUAHJMVMVNIUUAJMWBVEUVKUUBUUCVLIUVKUUBJMVMVNOVOVPZUCVRRUVJWCWIWD
      ZVSVTYTUVEUUHVQRUUIUVJUUHUVJYRAYSUVEWEWFWGVTYTUVEWJUVGWKUMUUIUVJUUPUVTWLV
      TYTUVEUVGUJULUMZUUIUVJAUVAUWEUVQYTUVAUVDWMZACEDHIJMNOAFUAZUULRZSZHUWGUETZ
      CEUFZUCUGTZUHUIZUCUJUKTZULUMZVFAUVASZUUPUCUGTZUHUIZUWNULUMZVFFDFDWTZUWIUW
      PUWOUWSUWTUWHUVAAUWGUUAUULWNWOUWTUWMUWRUWNULUWTUWLUWQUHUWTUWKUUPUCUGUWTUW
      JUUOCEUWGUUAHUEXAWPWQWRWSXBPXCXDVOVTYTUVEWJUUGWKUMUUIUVJUUFUWDWLVTYTUVEUU
      IXEXFYTUVEUVHUURXGUUIUVJUURUUPUUFVHTZUHUIUVHUVJUUQUXAUHUVJUUQUUPUUEVHTZUU
      PUGTUXAUVJUUNUXBUUPUGUVJUUOUUDCUUMEUVJUUAUUBULUMUUOUUDXJXHXGUVJUUAUVAUUAV
      QRYTUVDHUUAXIXKXTHUUAUUBUUCXLVEUVJUUAUUMRZUUMUUOUUDXMXGUVJUVAUVDUXCUWFYTU
      VAUVDXNUUAHUUCXOXPUUAHUUCXQVEUVJHUUCVIUVJUVKUUMRZSAUVMUVNAYSUVEUXDVJUVJUV
      OUVPUVMUXDUVRUVKHUUCVLUVSVNOVOXRWQUVJUUPUUEUVTUWCXSYAWRUVJUUPUUFUVTUWDYBY
      CVTUVFYSUVIYRXGAYSUVEUUIYDYSYRUJYRYEUJVRRYSYFWIUJWJYKYSYGWIYHVEYIYLYJYMYN
      YOYPYQ @.
    @}
  @}
  $)

  ${
    $d F j $.  $d F k $.  $d F n $.  $d j k $.  $d j n $.  $d j ph $.
    $d k ph $.  $d M j $.  $d M k $.  $d M n $.  $d n ph $.  $d Z k $.
    iprodefisumlem.1 $e |- Z = ( ZZ>= ` M ) $.
    iprodefisumlem.2 $e |- ( ph -> M e. ZZ ) $.
    iprodefisumlem.3 $e |- ( ph -> F : Z --> CC ) $.
    $( Lemma for ~ iprodefisum .  (Contributed by Scott Fenton,
       11-Feb-2018.) $)
    iprodefisumlem $p |- ( ph -> seq M ( x. , ( exp o. F ) ) =
       ( exp o. seq M ( + , F ) ) ) $=
      ( vk vj cmul ce caddc cc wcel cfv wceq fvco3 syl wi co vn ccom cseq cv wa
      sylan ffvelcdmda efcl eqeltrd prodf ffnd wfn eff ax-mp serf fnfco sylancr
      wf ffn cuz c1 fveq2 2fveq3 eqeq12d imbi2d weq uzid eleqtrrdi syl2anc seq1
      cz fveq2d 3eqtr4d a1i oveq1 3ad2ant3 adantl peano2uz adantr oveq2d expcom
      w3a eqcomi eleq2s imp ffvelcdmd efadd eqtr4d 3adant3 eqtrd seqp1 3exp a2d
      uzind4 impcom eqfnfvd ) AHDJKBUBZCUCZKLBCUCZUBZADMWRAHWQCDEFAHUDZDNZUEZXA
      WQOZXABOZKOZMADMBURZXBXDXFPGDMXAKBQUFXCXEMNXFMNADMXABGUGZXEUHRUIUJUKAKMUL
      ZDMWSURZWTDULMMKURXIUMMMKUSUNAHBCDEFXHUOZMDKWSUPUQXCXAWROZXAWSOKOZXAWTOZX
      BAXLXMPZAXOSZXACUTOZDAIUDZWROZXRWSOKOZPZSACWROZCWSOZKOZPZSZAUAUDZWROZYGWS
      OZKOZPZSAYGVALTZWROZYLWSOZKOZPZSXPIUACXAXRCPZYAYEAYQXSYBXTYDXRCWRVBXRCKWS
      VCVDVEIUAVFZYAYKAYRXSYHXTYJXRYGWRVBXRYGKWSVCVDVEXRYLPZYAYPAYSXSYMXTYOXRYL
      WRVBXRYLKWSVCVDVEIHVFZYAXOAYTXSXLXTXMXRXAWRVBXRXAKWSVCVDVEYFCVKNZACWQOZCB
      OZKOZYBYDAXGCDNUUBUUDPGACXQDAUUACXQNFCVGREVHDMCKBQVIAUUAYBUUBPFJWQCVJRAYC
      UUCKAUUAYCUUCPFLBCVJRVLVMVNYGXQNZAYKYPUUEAYKYPUUEAYKWBZYHYLWQOZJTZYIYLBOZ
      LTZKOZYMYOUUFUUHYJUUGJTZUUKYKUUEUUHUULPAYHYJUUGJVOVPUUEAUULUUKPYKUUEAUEZU
      ULYJUUIKOZJTZUUKUUMUUGUUNYJJUUMXGYLDNZUUGUUNPAXGUUEGVQZUUEUUPAUUEYLXQDCYG
      VREVHVSZDMYLKBQVIVTUUMYIMNZUUIMNUUKUUOPUUEAUUSAUUSSYGDXQAYGDNUUSADMYGWSXK
      UGWADXQEWCWDWEUUMDMYLBUUQUURWFYIUUIWGVIWHWIWJUUEAYMUUHPZYKUUEUUTAJWQCYGWK
      VSWIUUEAYOUUKPYKUUMYNUUJKUUEYNUUJPALBCYGWKVSVLWIVMWLWMWNEWDWOAXJXBXNXMPXK
      DMXAKWSQUFWHWP $.
  $}

  ${
    $d F k $.  $d k ph $.  $d M k $.  $d Z k $.  $d F j $.  $d j k $.
    $d Z j $.  $d j ph $.  $d M j $.
    iprodefisum.1 $e |- Z = ( ZZ>= ` M ) $.
    iprodefisum.2 $e |- ( ph -> M e. ZZ ) $.
    iprodefisum.3 $e |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B ) $.
    iprodefisum.4 $e |- ( ( ph /\ k e. Z ) -> B e. CC ) $.
    iprodefisum.5 $e |- ( ph -> seq M ( + , F ) e. dom ~~> ) $.
    $( Applying the exponential function to an infinite sum yields an infinite
       product.  (Contributed by Scott Fenton, 11-Feb-2018.) $)
    iprodefisum $p |- ( ph -> prod_ k e. Z ( exp ` B ) =
       ( exp ` sum_ k e. Z B ) ) $=
      ( vj ce cfv cc wcel syl caddc cseq cli cmpt ccom csu cc0 wne isumcl efne0
      cv cmul ccncf co efcn a1i wa wceq fveq2 eqid fvex adantl eqeltrd serf cuz
      fvmpt eqcomi eleq2s seqfeq cdm wbr climdm eqbrtrd climcl climcncf cbvmptv
      sylib fmptd iprodefisumlem isum fveq2d 3brtr4d wf fvco3 sylan 3eqtrd efcl
      iprodn0 ) ABMNZCMLFLUHZDNZUAZUBZEFBCUCZMNZFGHAWKOPWLUDUEABCDEFGHIJKUFWKUG
      QAMRWIESZUBRDESZTNZMNUIWJESWLTAOOWOMWMEFGHMOOUJUKPAULUMACWIEFGHACUHZFPZUN
      ZWPWINZWPDNZOWQWSWTUOZALWPWHWTFWIWGWPDUPZWIUQWPDURVCZUSZWRWTBOIJUTZUTVAAW
      MWNWOTARCWIDEHWPEVBNZPXAAXAWPFXFXCFXFGVDVEUSVFAWNTVGPWNWOTVHZKWNVIVNZVJAX
      GWOOPXHWOWNVKQVLAWIEFGHACFWTOWIXELCFWHWTXBVMVOZVPAWKWOMABCDEFGHIJVQVRVSWR
      WPWJNZWSMNZWTMNWFAFOWIVTWQXJXKUOXIFOWPMWIWAWBWRWSWTMXDVRWRWTBMIVRWCWRBOPW
      FOPJBWDQWE $.
  $}

  ${
    $d A j $.  $d A k $.  $d A z $.  $d j k $.  $d j ph $.  $d k ph $.
    $d k z $.
    iprodgam.1 $e |- ( ph -> A e. ( CC \ ( ZZ \ NN ) ) ) $.
    $( An infinite product version of Euler's gamma function.  (Contributed by
       Scott Fenton, 12-Feb-2018.) $)
    iprodgam $p |- ( ph -> ( _G ` A ) =
    ( prod_ k e. NN ( ( ( 1 + ( 1 / k ) ) ^c A ) / ( 1 + ( A / k ) ) ) /
      A ) ) $=
      ( vj cfv ce cn c1 cdiv co caddc cc wcel wceq clog cmul cmin oveq12d eqtrd
      vz clgam cgam cv ccxp cprod cz cdif eflgam oveq1 fvoveq1d sumeq2sdv fveq2
      syl csu df-lgam ovex fvmpt fveq2d cmpt nnuz 1zzd weq id oveq2d oveq2 eqid
      adantl wa eldifad adantr peano2nn nncnd nncn cc0 wne nnne0 divcld divne0d
      nnne0d logcld mulcld 1cnd addcld simpr dmgmdivn0 cseq cli wbr cdm lgamcvg
      subcld seqex breldm isumcl dmgmn0 efsub syl2anc iprodefisum dividd oveq1d
      divdird crp 1rp nnrpd rpreccld rpaddcld rpcnd rpne0d cxpefd eflog addcomd
      a1i eqtr4d prodeq2dv eqtr3d ) ABUBFZGFZBUCFZHIICUDZJKZLKZBUEKZIBXTJKZLKZJ
      KZCUFZBJKZABMUGHUHZUHZNZXRXSODBUIUNAXRHBXTILKZXTJKZPFZQKZYDILKZPFZRKZCUOZ
      BPFZRKZGFZYHAXQUUAGAYKXQUUAODUABHUAUDZYNQKZUUCXTJKZILKPFZRKZCUOZUUCPFZRKU
      UAYJUBUUCBOZUUHYSUUIYTRUUJHUUGYRCUUJUUDYOUUFYQRUUCBYNQUJUUJUUEYDIPLUUCBXT
      JUJUKSULUUCBPUMSUACUPYSYTRUQURUNUSAUUBYSGFZYTGFZJKZYHAYSMNYTMNUUBUUMOAYRC
      EHBEUDZILKZUUNJKZPFZQKZBUUNJKZILKPFZRKZUTZIHVAAVBZXTHNZXTUVBFYROAEXTUVAYR
      HUVBECVCZUURYOUUTYQRUVEUUQYNBQUVEUUPYMPUVEUUOYLUUNXTJUUNXTILUJUVEVDSUSVEU
      VEUUSYDIPLUUNXTBJVFUKSUVBVGZYOYQRUQURVHZAUVDVIZYOYQUVHBYNABMNZUVDABMYIDVJ
      ZVKZUVHYMUVHYLXTUVHYLUVDYLHNAXTVLVHZVMZUVDXTMNAXTVNVHZUVDXTVOVPAXTVQVHZVR
      UVHYLXTUVMUVNUVHYLUVLVTUVOVSWAWBZUVHYPUVHYDIUVHBXTUVKUVNUVOVRZUVHWCZWDZUV
      HBXTAYKUVDDVKAUVDWEZWFZWAZWLZALUVBIWGZXQYTLKZWHWIUWDWHWJNABEUVBUVFDWKUWDU
      WEWHLUVBIWMXQYTLUQWNUNZWOABUVJABDWPZWAYSYTWQWRAUUKYGUULBJAHYRGFZCUFUUKYGA
      YRCUVBIHVAUVCUVGUWCUWFWSAHUWHYFCUVHUWHYOGFZYQGFZJKZYFUVHYOMNYQMNUWHUWKOUV
      PUWBYOYQWQWRUVHUWIYCUWJYEJUVHUWIBYBPFZQKZGFYCUVHYOUWMGUVHYNUWLBQUVHYMYBPU
      VHYMXTXTJKZYALKYBUVHXTIXTUVNUVRUVNUVOXBUVHUWNIYALUVHXTUVNUVOWTXATUSVEUSUV
      HYBBUVHYBUVHIYAIXCNUVHXDXMUVHXTUVHXTUVTXEXFXGZXHUVHYBUWOXIUVKXJXNUVHUWJYP
      YEUVHYPMNYPVOVPUWJYPOUVSUWAYPXKWRUVHYDIUVQUVRXLTSTXOXPAUVIBVOVPUULBOUVJUW
      GBXKWRSTTXP $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Factorial limits
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d a b $.  $d a k $.  $d a n $.  $d b n $.  $d b x $.  $d k n $.  $d M a $.
    $d M b $.  $d M k $.  $d M n $.  $d M x $.
    $( Lemma for ~ faclim .  Closed form for a particular sequence.
       (Contributed by Scott Fenton, 15-Dec-2017.) $)
    faclimlem1 $p |- ( M e. NN0 ->
     seq 1 ( x. , ( n e. NN |-> ( ( ( 1 + ( M / n ) ) x. ( 1 + ( 1 / n ) ) ) /
     ( 1 + ( ( M + 1 ) / n ) ) ) ) ) =
     ( x e. NN |-> ( ( M + 1 ) x. ( ( x + 1 ) / ( x + ( M + 1 ) ) ) ) ) ) $=
      ( vb wcel cv cmul cn c1 cdiv co caddc cfv wceq oveq1 oveq12d oveq2d oveq2
      3eqtrd rpcnd va vk cn0 cmpt cseq wral wa wi fveq2 cz 1z seq1 ax-mp eqtrdi
      eqeq12d imbi2d weq 1nn eqid ovex fvmpt nn0cn div1d 1div1e1 oveq2i nn0p1nn
      nncnd 1cnd addcomd oveq1d cc ax-1cn addcli nnaddcld nnne0d divassd eqtrid
      a1i cuz seqp1 nnuz eleq2s adantr adantl peano2nn syl nnrpd simpl rpaddcld
      rpdivcld crp cr nn0re nndivred recnd cc0 cle wbr divge0d ge0p1rpd eqeltrd
      nn0ge0 1rp rpreccld rpmulcld mulassd rpne0d divcan5d mul12d mulridd simpr
      adddid nn0cnd divcan2d addassd eqtrd eqtr3d divcan1d 3eqtr3rd exp31 nnind
      a2d impcom eqtr4d ralrimiva wfn wb seqfn fneq2i mpbir fnmpti eqfnfv mp2an
      sylibr ) CUCEZDFZGBHICBFZJKZLKZIIYQJKZLKZGKZICILKZYQJKZLKZJKZUDZIUEZMZYPA
      HUUCAFZILKZUUJUUCLKZJKZGKZUDZMZNZDHUFZUUHUUONZYOUUQDHYOYPHEZUGUUIUUCYPILK
      ZYPUUCLKZJKZGKZUUPUUTYOUUIUVDNZYOUAFZUUHMZUUCUVFILKZUVFUUCLKZJKZGKZNZUHYO
      IUUGMZUUCIILKZIUUCLKZJKZGKZNZUHYOUBFZUUHMZUUCUVSILKZUVSUUCLKZJKZGKZNZUHYO
      UWAUUHMZUUCUWAILKZUWAUUCLKZJKZGKZNZUHYOUVEUHUAUBYPUVFINZUVLUVRYOUWLUVGUVM
      UVKUVQUWLUVGIUUHMZUVMUVFIUUHUIIUJEZUWMUVMNUKGUUGIULUMUNUWLUVJUVPUUCGUWLUV
      HUVNUVIUVOJUVFIILOUVFIUUCLOPQUOUPUAUBUQZUVLUWEYOUWOUVGUVTUVKUWDUVFUVSUUHU
      IUWOUVJUWCUUCGUWOUVHUWAUVIUWBJUVFUVSILOUVFUVSUUCLOPQUOUPUVFUWANZUVLUWKYOU
      WPUVGUWFUVKUWJUVFUWAUUHUIUWPUVJUWIUUCGUWPUVHUWGUVIUWHJUVFUWAILOUVFUWAUUCL
      OPQUOUPUADUQZUVLUVEYOUWQUVGUUIUVKUVDUVFYPUUHUIUWQUVJUVCUUCGUWQUVHUVAUVIUV
      BJUVFYPILOUVFYPUUCLOPQUOUPYOUVMICIJKZLKZIIIJKZLKZGKZIUUCIJKZLKZJKZUVQIHEZ
      UVMUXENURBIUUFUXEHUUGYQINZUUBUXBUUEUXDJUXGYSUWSUUAUXAGUXGYRUWRILYQICJRQUX
      GYTUWTILYQIIJRQPUXGUUDUXCILYQIUUCJRQPUUGUSZUXBUXDJUTVAUMYOUXEICLKZUVNGKZU
      VOJKUUCUVNGKZUVOJKUVQYOUXBUXJUXDUVOJYOUWSUXIUXAUVNGYOUWRCILYOCCVBZVCQUXAU
      VNNYOUWTIILVDVEVRPYOUXCUUCILYOUUCYOUUCCVFZVGZVCQPYOUXJUXKUVOJYOUXIUUCUVNG
      YOICYOVHUXLVIVJVJYOUUCUVNUVOUXNUVNVKEYOIIVLVLVMVRYOUVOYOIUUCUXFYOURVRUXMV
      NZVGYOUVOUXOVOVPSVQUVSHEZYOUWEUWKUXPYOUWEUWKUXPYOUGZUWEUGUWFUVTUWAUUGMZGK
      ZUWDUXRGKZUWJUXQUWFUXSNZUWEUXPUYAYOUYAUVSIVSMZHGUUGIUVSVTWAWBWCWCUWEUXSUX
      TNUXQUVTUWDUXRGOWDUXQUXTUWJNUWEUXQUXTUWDICUWAJKZLKZIIUWAJKZLKZGKZIUUCUWAJ
      KZLKZJKZGKZUUCUWCUYJGKZGKUWJUXPUXTUYKNYOUXPUXRUYJUWDGUXPUWAHEZUXRUYJNUVSW
      EZBUWAUUFUYJHUUGYQUWANZUUBUYGUUEUYIJUYOYSUYDUUAUYFGUYOYRUYCILYQUWACJRQUYO
      YTUYEILYQUWAIJRQPUYOUUDUYHILYQUWAUUCJRQPUXHUYGUYIJUTVAWFQWCUXQUUCUWCUYJUX
      QUUCYOUUCHEUXPUXMWDZVGZUXQUWCUXQUWAUWBUXQUWAUXPUYMYOUYNWCZWGZUXQUVSUUCUXQ
      UVSUXPYOWHZWGUXQUUCUYPWGZWIZWJZTZUXQUYJUXQUYGUYIUXQUYDUYFUXQUYDUYCILKWKUX
      QIUYCUXQVHZUXQUYCUXQCUWAYOCWLEUXPCWMWDZUYRWNZWOZVIUXQUYCVUGUXQCUWAVUFUYSY
      OWPCWQWRUXPCXBWDWSWTXAZUXQIUYEIWKEUXQXCVRZUXQUWAUYSXDZWIZXEZUXQIUYHVUJUXQ
      UUCUWAVUAUYSWJZWIZWJTXFUXQUYLUWIUUCGUXQUWAUWCUYGGKZGKZUWAUYIGKZJKVUPUYIJK
      UWIUYLUXQVUPUYIUWAUXQVUPUXQUWCUYGVUCVUMXETUXQUYIVUOTZUXQUWAUYRVGZUXQUYIVU
      OXGZUXQUWAUYRVOZXHUXQVUQUWGVURUWHJUXQVUQUWCUWAUYGGKZGKUWCUWBUYFGKZGKZUWGU
      XQUWAUWCUYGVUTVUDUXQUYGVUMTZXIUXQVVCVVDUWCGUXQUWAUYDGKZUYFGKVVCVVDUXQUWAU
      YDUYFVUTUXQUYDVUITUXQUYFVULTZXFUXQVVGUWBUYFGUXQVVGUWAIGKZUWAUYCGKZLKUWACL
      KZUWBUXQUWAIUYCVUTVUEVUHXLUXQVVIUWAVVJCLUXQUWAVUTXJZUXQCUWAUXQCUXPYOXKXMZ
      VUTVVBXNPUXQVVKUVSUXILKUWBUXQUVSICUXQUVSUYTVGVUEVVMXOUXQUXIUUCUVSLUXQICVU
      EVVMVIQXPSVJXQQUXQUWCUWBGKZUYFGKZVVEUWGUXQUWCUWBUYFVUDUXQUWBVUBTZVVHXFUXQ
      VVOUWAUYFGKVVIUWAUYEGKZLKUWGUXQVVNUWAUYFGUXQUWAUWBVUTVVPUXQUWBVUBXGXRVJUX
      QUWAIUYEVUTVUEUXQUYEVUKTXLUXQVVIUWAVVQILVVLUXQIUWAVUEVUTVVBXNPSXQSUXQVURV
      VIUWAUYHGKZLKUWHUXQUWAIUYHVUTVUEUXQUYHVUNTXLUXQVVIUWAVVRUUCLVVLUXQUUCUWAU
      YQVUTVVBXNPXPPUXQUWCUYGUYIVUDVVFVUSVVAVPXSQSWCSXTYBYAYCUUTUUPUVDNYOAYPUUN
      UVDHUUOADUQZUUMUVCUUCGVVSUUKUVAUULUVBJUUJYPILOUUJYPUUCLOPQUUOUSZUUCUVCGUT
      VAWDYDYEUUHHYFZUUOHYFUUSUURYGVWAUUHUYBYFZUWNVWBUKGUUGIYHUMHUYBUUHWAYIYJAH
      UUNUUOUUCUUMGUTVVTYKDHUUHUUOYLYMYN $.
  $}

  ${
    $d k m $.  $d M k $.  $d M m $.  $d M n $.
    $( Lemma for ~ faclim .  Show a limit for the inductive step.  (Contributed
       by Scott Fenton, 15-Dec-2017.) $)
    faclimlem2 $p |- ( M e. NN0 ->
     seq 1 ( x. ,
     ( n e. NN |-> ( ( ( 1 + ( M / n ) ) x. ( 1 + ( 1 / n ) ) ) /
     ( 1 + ( ( M + 1 ) / n ) ) ) ) ) ~~> ( M + 1 ) ) $=
      ( vm vk wcel cmul cn c1 cv cdiv co caddc cmpt cli cvv nnuz nnex mptex a1i
      adantl cn0 cseq faclimlem1 1zzd 1cnd nn0p1nn nnzd cfv wceq weq oveq1 eqid
      oveq12d ovex fvmpt divcnvlin nncnd cc wa peano2nn nnred nnaddcld nndivred
      simpr adantr recnd fmpttd oveq2d eqtr4d climmulc2 mulridd breqtrd eqbrtrd
      ffvelcdmda ) BUAEZFAGHBAIZJKLKHHVPJKLKFKHBHLKZVPJKLKJKMHUBCGVQCIZHLKZVRVQ
      LKZJKZFKZMZVQNCABUCVOWCVQHFKVQNVOHVQDCGWAMZWCHOGPVOUDZVOHVQDWDHOGPWEVOUEV
      OVQBUFZUGWDOEVOCGWAQRSDIZGEZWGWDUHZWGHLKZWGVQLKZJKZUIVOCWGWAWLGWDCDUJZVSW
      JVTWKJVRWGHLUKVRWGVQLUKUMZWDULWJWKJUNUOZTUPVOVQWFUQZWCOEVOCGWBQRSVOGURWGW
      DVOCGWAURVOVRGEZUSZWAWRVSVTWRVSWQVSGEVOVRUTTVAWRVRVQVOWQVDVOVQGEWQWFVEVBV
      CVFVGVNWHWGWCUHZVQWIFKZUIVOWHWSVQWLFKZWTCWGWBXAGWCWMWAWLVQFWNVHWCULVQWLFU
      NUOWHWIWLVQFWOVHVITVJVOVQWPVKVLVM $.
  $}

  $( Lemma for ~ faclim .  Algebraic manipulation for the final induction.
     (Contributed by Scott Fenton, 15-Dec-2017.) $)
  faclimlem3 $p |- ( ( M e. NN0 /\ B e. NN ) ->
  ( ( ( 1 + ( 1 / B ) ) ^ ( M + 1 ) ) / ( 1 + ( ( M + 1 ) / B ) ) ) =
  ( ( ( ( 1 + ( 1 / B ) ) ^ M ) / ( 1 + ( M / B ) ) ) x.
    ( ( ( 1 + ( M / B ) ) x. ( 1 + ( 1 / B ) ) ) / ( 1 + ( ( M + 1 ) / B ) ) )
    ) ) $=
    ( cn0 wcel cn c1 cdiv co caddc cexp cmul crp 1rp a1i adantl rpaddcld rpne0d
    rpcnd oveq1d rpdivcld wa nnrp rpreccld simpl expp1d cz nn0z rpexpcl syl2anr
    1cnd nn0nndivcl addcomd nn0ge0div ge0p1rpd eqeltrd divcan1d mulassd 3eqtr2d
    recnd rpmulcld nn0p1nn nnrpd adantr divassd eqtrd ) BCDZAEDZUAZFFAGHZIHZBFI
    HZJHZFVKAGHZIHZGHVJBJHZFBAGHZIHZGHZVQVJKHZKHZVNGHVRVSVNGHKHVHVLVTVNGVHVLVOV
    JKHVRVQKHZVJKHVTVHVJBVHVJVHFVIFLDZVHMNZVGVILDVFVGAAUBZUCZOPZRZVFVGUDUEVHWAV
    OVJKVHVOVQVHVOVGVJLDBUFDVOLDVFVGFVIWBVGMNWEPBUGVJBUHUIZRVHVQVHVQVPFIHLVHFVP
    VHUJVHVPBAUKZUSULVHVPWIBAUMUNUOZRZVHVQWJQUPSVHVRVQVJVHVRVHVOVQWHWJTRZWKWGUQ
    URSVHVRVSVNWLVHVSVHVQVJWJWFUTRVHVNVHFVMWCVHVKAVFVKLDVGVFVKBVAVBVCVGALDVFWDO
    TPZRVHVNWMQVDVE $.

  ${
    $d A a b m n x $.
    faclim.1 $e |- F =
         ( n e. NN |-> ( ( ( 1 + ( 1 / n ) ) ^ A ) / ( 1 + ( A / n ) ) ) ) $.
    $( An infinite product expression relating to factorials.  Originally due
       to Euler.  (Contributed by Scott Fenton, 22-Nov-2017.) $)
    faclim $p |- ( A e. NN0 -> seq 1 ( x. , F ) ~~> ( ! ` A ) ) $=
      ( wcel cmul c1 cseq cn cdiv co caddc cexp cfa cfv cli wceq cc0 oveq12d cc
      va vm vb vx cn0 cmpt seqeq3 ax-mp wbr oveq2 oveq1 oveq2d mpteq2dv seqeq3d
      cv fveq2 fac0 eqtrdi breq12d weq csn cxp 1red nnrecre readdcld recnd nncn
      exp0d nnne0 div0d 1p0e1 1div1e1 fconstmpt eqtr4i wtru nnuz 1zzd climprod1
      mpteq2ia mptru eqbrtri wa cvv simpr seqex faclimlem2 adantr elnnuz bilani
      a1i cuz cfz wf crp nnrp rpreccld adantl rpaddcld nn0z rpexpcld nn0nndivcl
      cz 1cnd addcomd nn0ge0div ge0p1rpd eqeltrd rpdivcld rpcnd fmpttd ffvelcdm
      1rp elfznn syl2an adantlr mulcl seqcl rpmulcld nn0p1nn rpdivcl faclimlem3
      nnrpd oveq1d eqid fvmpt 3eqtr4d sylan2 prodfmul climmul facp1 breqtrrd ex
      ovex nn0ind eqbrtrid ) AUEEFCGHZFBIGGBUOZJKZLKZAMKZGAYQJKZLKZJKZUFZGHZANO
      ZPCUUDQYPUUEQDFCUUDGUGUHFBIYSUAUOZMKZGUUGYQJKZLKZJKZUFZGHZUUGNOZPUIFBIYSR
      MKZGRYQJKZLKZJKZUFZGHZGPUIFBIYSUBUOZMKZGUVAYQJKZLKZJKZUFZGHZUVANOZPUIZFBI
      YSUVAGLKZMKZGUVJYQJKZLKZJKZUFZGHZUVJNOZPUIZUUEUUFPUIUAUBAUUGRQZUUMUUTUUNG
      PUVSUULUUSFGUVSBIUUKUURUVSUUHUUOUUJUUQJUUGRYSMUJUVSUUIUUPGLUUGRYQJUKULSUM
      UNUVSUUNRNOGUUGRNUPUQURUSUAUBUTZUUMUVGUUNUVHPUVTUULUVFFGUVTBIUUKUVEUVTUUH
      UVBUUJUVDJUUGUVAYSMUJUVTUUIUVCGLUUGUVAYQJUKULSUMUNUUGUVANUPUSUUGUVJQZUUMU
      VPUUNUVQPUWAUULUVOFGUWABIUUKUVNUWAUUHUVKUUJUVMJUUGUVJYSMUJUWAUUIUVLGLUUGU
      VJYQJUKULSUMUNUUGUVJNUPUSUUGAQZUUMUUEUUNUUFPUWBUULUUDFGUWBBIUUKUUCUWBUUHY
      TUUJUUBJUUGAYSMUJUWBUUIUUAGLUUGAYQJUKULSUMUNUUGANUPUSUUTFIGVAVBZGHZGPUUSU
      WCQUUTUWDQUUSBIGUFUWCBIUURGYQIEZUURGGJKGUWEUUOGUUQGJUWEYSUWEYSUWEGYRUWEVC
      YQVDVEVFVHUWEUUQGRLKGUWEUUPRGLUWEYQYQVGYQVIVJULVKURSVLURVSBIGVMVNFUUSUWCG
      UGUHUWDGPUIVOGIVPVOVQVRVTWAUVAUEEZUVIUVRUWFUVIWBZUVPUVHUVJFKZUVQPUWGUVHUV
      JUAUVGFBIUVDYSFKZUVMJKZUFZGHZUVPGWCIVPUWGVQUWFUVIWDUVPWCEUWGFUVOGWEWJUWFU
      WLUVJPUIUVIBUVAWFWGUWFUUGIEZUUGUVGOZTEUVIUWFUWMWBZUCUDFTUVFGUUGUWMUUGGWKO
      EUWFUUGWHWIZUWFUCUOZGUUGWLKEZUWQUVFOZTEZUWMUWFITUVFWMUWQIEZUWTUWRUWFBIUVE
      TUWFUWEWBZUVEUXBUVBUVDUXBYSUVAUXBGYRGWNEUXBXLWJZUWEYRWNEUWFUWEYQYQWOZWPWQ
      WRZUWFUVAXBEUWEUVAWSWGWTUXBUVDUVCGLKWNUXBGUVCUXBXCUXBUVCUVAYQXAZVFXDUXBUV
      CUXFUVAYQXEXFXGZXHXIXJUWQUUGXMZITUWQUVFXKXNXOZUWQTEUDUOZTEWBUWQUXJFKTEUWO
      UWQUXJXPWQZXQXOUWFUWMUUGUWLOZTEUVIUWOUCUDFTUWKGUUGUWPUWFUWRUWQUWKOZTEZUWM
      UWFITUWKWMUXAUXNUWRUWFBIUWJTUXBUWJUXBUWIUVMUXBUVDYSUXGUXEXRUXBGUVLUXCUWFU
      VJWNEYQWNEUVLWNEUWEUWFUVJUVAXSYBUXDUVJYQXTXNWRXHXIXJUXHITUWQUWKXKXNXOZUXK
      XQXOUWFUWMUUGUVPOUWNUXLFKQUVIUWOUCUVFUWKUVOGUUGUWPUXIUXOUWFUWRUWQUVOOZUWS
      UXMFKZQZUWMUWRUWFUXAUXRUXHUWFUXAWBGGUWQJKZLKZUVJMKZGUVJUWQJKZLKZJKZUXTUVA
      MKZGUVAUWQJKZLKZJKZUYGUXTFKZUYCJKZFKZUXPUXQUWQUVAYAUXAUXPUYDQUWFBUWQUVNUY
      DIUVOBUCUTZUVKUYAUVMUYCJUYLYSUXTUVJMUYLYRUXSGLYQUWQGJUJULZYCUYLUVLUYBGLYQ
      UWQUVJJUJULZSUVOYDUYAUYCJYMYEWQUXAUXQUYKQUWFUXAUWSUYHUXMUYJFBUWQUVEUYHIUV
      FUYLUVBUYEUVDUYGJUYLYSUXTUVAMUYMYCUYLUVCUYFGLYQUWQUVAJUJULZSUVFYDUYEUYGJY
      MYEBUWQUWJUYJIUWKUYLUWIUYIUVMUYCJUYLUVDUYGYSUXTFUYOUYMSUYNSUWKYDUYIUYCJYM
      YESWQYFYGXOYHXOYIUWFUVQUWHQUVIUVAYJWGYKYLYNYO $.
  $}

  ${
    $d A k x $.
    $( An infinite product expression for factorial.  (Contributed by Scott
       Fenton, 15-Dec-2017.) $)
    iprodfac $p |- ( A e. NN0 -> ( ! ` A ) =
      prod_ k e. NN ( ( ( 1 + ( 1 / k ) ) ^ A ) / ( 1 + ( A / k ) ) ) ) $=
      ( vx cn0 wcel cn c1 cv cdiv co caddc cexp cprod cfa cfv cmpt oveq2 oveq2d
      nnuz crp 1zzd facne0 eqid faclim wceq oveq1d oveq12d ovex fvmpt adantl wa
      weq 1rp a1i simpr nnrpd rpreccld rpaddcld nn0z adantr rpexpcld nn0nndivcl
      cz recnd addcomd nn0ge0div ge0p1rpd eqeltrd rpdivcld rpcnd iprodn0 eqcomd
      1cnd ) ADEZFGGBHZIJZKJZALJZGAVOIJZKJZIJZBMANOZVNWABCFGGCHZIJZKJZALJZGAWCI
      JZKJZIJZPZGWBFSVNUAAUBACWJWJUCZUDVOFEZVOWJOWAUEVNCVOWIWAFWJCBULZWFVRWHVTI
      WMWEVQALWMWDVPGKWCVOGIQRUFWMWGVSGKWCVOAIQRUGWKVRVTIUHUIUJVNWLUKZWAWNVRVTW
      NVQAWNGVPGTEWNUMUNWNVOWNVOVNWLUOUPUQURVNAVCEWLAUSUTVAWNVTVSGKJTWNGVSWNVMW
      NVSAVOVBZVDVEWNVSWOAVOVFVGVHVIVJVKVL $.
  $}

  ${
    $d a m $.  $d a n $.  $d k m $.  $d k n $.  $d M a $.  $d m n $.  $d M n $.
    faclim2.1 $e |- F =
     ( n e. NN |->
     ( ( ( ! ` n ) x. ( ( n + 1 ) ^ M ) ) / ( ! ` ( n + M ) ) ) ) $.
    $( Another factorial limit due to Euler.  (Contributed by Scott Fenton,
       17-Dec-2017.) $)
    faclim2 $p |- ( M e. NN0 -> F ~~> 1 ) $=
      ( wcel cn cfa cfv c1 caddc co cexp cmul cdiv cli wceq oveq2 oveq12d nncnd
      cc0 va vm vk cn0 cmpt wbr oveq2d fveq2d mpteq2dv breq1d weq wtru cvv nnuz
      cv 1zzd nnex mptex a1i 1cnd fveq2 oveq1 oveq1d fvoveq1 eqid ovex peano2nn
      fvmpt exp0d nnnn0 faccl mulridd eqtrd addridd nnne0d dividd 3eqtrd adantl
      syl nncn climconst mptru wa simpr nn0p1nn nnzd divcnvlin adantr cc nnnn0d
      nnexpcl sylan ancoms nnmulcld nnred nnnn0addcl nndivred fmpttd ffvelcdmda
      recnd adantlr nnaddcld simpl expp1d mulassd eqtr4d nn0addcld facp1 nn0cnd
      addassd 3eqtr3d divmuldivd 3eqtr4d climmul 1t1e1 breqtrdi nn0ind eqbrtrid
      ex ) CUDEBAFAUOZGHZXTIJKZCLKZMKZXTCJKZGHZNKZUEZIODAFYAYBUAUOZLKZMKZXTYIJK
      ZGHZNKZUEZIOUFAFYAYBTLKZMKZXTTJKZGHZNKZUEZIOUFZAFYAYBUBUOZLKZMKZXTUUCJKZG
      HZNKZUEZIOUFZAFYAYBUUCIJKZLKZMKZXTUUKJKZGHZNKZUEZIOUFZYHIOUFUAUBCYITPZYOU
      UAIOUUSAFYNYTUUSYKYQYMYSNUUSYJYPYAMYITYBLQUGUUSYLYRGYITXTJQUHRUIUJUAUBUKZ
      YOUUIIOUUTAFYNUUHUUTYKUUEYMUUGNUUTYJUUDYAMYIUUCYBLQUGUUTYLUUFGYIUUCXTJQUH
      RUIUJYIUUKPZYOUUQIOUVAAFYNUUPUVAYKUUMYMUUONUVAYJUULYAMYIUUKYBLQUGUVAYLUUN
      GYIUUKXTJQUHRUIUJYICPZYOYHIOUVBAFYNYGUVBYKYDYMYFNUVBYJYCYAMYICYBLQUGUVBYL
      YEGYICXTJQUHRUIUJUUBULIUBUUAIUMFUNULUPUUAUMEULAFYTUQURUSULUTUUCFEZUUCUUAH
      ZIPULUVCUVDUUCGHZUUKTLKZMKZUUCTJKZGHZNKZUVEUVENKIAUUCYTUVJFUUAAUBUKZYQUVG
      YSUVINUVKYAUVEYPUVFMXTUUCGVAUVKYBUUKTLXTUUCIJVBVCRXTUUCTGJVDRUUAVEUVGUVIN
      VFVHUVCUVGUVEUVIUVENUVCUVGUVEIMKUVEUVCUVFIUVEMUVCUUKUVCUUKUUCVGSVIUGUVCUV
      EUVCUVEUVCUUCUDEZUVEFEUUCVJUUCVKVSZSZVLVMUVCUVHUUCGUVCUUCUUCVTVNUHRUVCUVE
      UVNUVCUVEUVMVOVPVQVRWAWBUVLUUJUURUVLUUJWCZUUQIIMKIOUVOIIUCUUIAFYBUUNNKZUE
      ZUUQIUMFUNUVOUPUVLUUJWDUUQUMEUVOAFUUPUQURUSUVLUVQIOUFUUJUVLIUUKUCUVQIUMFU
      NUVLUPUVLUTUVLUUKUUCWEZWFUVQUMEUVLAFUVPUQURUSUCUOZFEZUVSUVQHZUVSIJKZUVSUU
      KJKZNKZPUVLAUVSUVPUWDFUVQAUCUKZYBUWBUUNUWCNXTUVSIJVBZXTUVSUUKJVBRUVQVEUWB
      UWCNVFVHZVRWGWHUVLUVTUVSUUIHZWIEUUJUVLFWIUVSUUIUVLAFUUHWIUVLXTFEZWCZUUHUW
      JUUEUUGUWJUUEUWJYAUUDUWJXTUDEYAFEUWJXTUVLUWIWDZWJXTVKVSUWIUVLUUDFEZUWIYBF
      EZUVLUWLXTVGZYBUUCWKWLWMWNWOUWJUUFUDEUUGFEUWJUUFUWIUVLUUFFEXTUUCWPWMWJUUF
      VKVSWQWTWRWSXAUVLUVTUWAWIEUUJUVLFWIUVSUVQUVLAFUVPWIUWJUVPUWJYBUUNUWJYBUWI
      UWMUVLUWNVRWOUWJXTUUKUWKUVLUUKFEZUWIUVRWHXBWQWTWRWSXAUVLUVTUVSUUQHZUWHUWA
      MKZPUUJUVLUVTWCZUVSGHZUWBUUKLKZMKZUWCGHZNKZUWSUWBUUCLKZMKZUVSUUCJKZGHZNKZ
      UWDMKZUWPUWQUWRUXCUXEUWBMKZUXGUWCMKZNKUXIUWRUXAUXJUXBUXKNUWRUXAUWSUXDUWBM
      KZMKUXJUWRUWTUXLUWSMUWRUWBUUCUWRUWBUVTUWBFEZUVLUVSVGZVRSZUVLUVTXCZXDUGUWR
      UWSUXDUWBUWRUWSUWRUVSUDEUWSFEUWRUVSUVLUVTWDZWJZUVSVKVSZSUWRUXDUVTUVLUXDFE
      ZUVTUXMUVLUXTUXNUWBUUCWKWLWMZSUXOXEXFUWRUXFIJKZGHZUXGUYBMKZUXBUXKUWRUXFUD
      EZUYCUYDPUWRUVSUUCUXRUXPXGZUXFXHVSUWRUYBUWCGUWRUVSUUCIUWRUVSUXQSUWRUUCUXP
      XIUWRUTXJZUHUWRUYBUWCUXGMUYGUGXKRUWRUXEUXGUWBUWCUWRUXEUWRUWSUXDUXSUYAWNSU
      WRUXGUWRUYEUXGFEUYFUXFVKVSZSUXOUWRUWCUWRUVSUUKUXQUVLUWOUVTUVRWHXBZSUWRUXG
      UYHVOUWRUWCUYIVOXLXFUVTUWPUXCPUVLAUVSUUPUXCFUUQUWEUUMUXAUUOUXBNUWEYAUWSUU
      LUWTMXTUVSGVAZUWEYBUWBUUKLUWFVCRXTUVSUUKGJVDRUUQVEUXAUXBNVFVHVRUVTUWQUXIP
      UVLUVTUWHUXHUWAUWDMAUVSUUHUXHFUUIUWEUUEUXEUUGUXGNUWEYAUWSUUDUXDMUYJUWEYBU
      WBUUCLUWFVCRXTUVSUUCGJVDRUUIVEUXEUXGNVFVHUWGRVRXMXAXNXOXPXSXQXR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Greatest common divisor and divisibility
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Swap the second and third arguments of a gcd.  (Contributed by Scott
     Fenton, 8-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
  gcd32 $p |- ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) ->
    ( ( A gcd B ) gcd C ) = ( ( A gcd C ) gcd B ) ) $=
    ( cz wcel w3a cgcd co wceq gcdcom 3adant1 oveq2d gcdass 3com23 3eqtr4d ) AD
    EZBDEZCDEZFZABCGHZGHACBGHZGHZABGHCGHACGHBGHZSTUAAGQRTUAIPBCJKLCBAMPRQUCUBIB
    CAMNO $.

  $( Absorption law for gcd.  (Contributed by Scott Fenton, 8-Apr-2014.)
     (Revised by Mario Carneiro, 19-Apr-2014.) $)
  gcdabsorb $p |- ( ( A e. ZZ /\ B e. ZZ ) -> ( ( A gcd B ) gcd B ) = ( A gcd B
      ) ) $=
    ( cz wcel wa cgcd cabs cfv wceq gcdass 3anidm23 gcdid oveq2d adantl gcdabs2
    co 3eqtrd ) ACDZBCDZEABFPZBFPZABBFPZFPZABGHZFPZTRSUAUCIBBAJKSUCUEIRSUBUDAFB
    LMNBAOQ $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Properties of relationships
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x y $.
    dftr6.1 $e |- A e. _V $.
    $( A potential definition of transitivity for sets.  (Contributed by Scott
       Fenton, 18-Mar-2012.) $)
    dftr6 $p |- ( Tr A <-> A e. ( _V \ ran ( ( _E o. _E ) \ _E ) ) ) $=
      ( vx vy wel cv wcel wa wi wal cep cdif wn cvv wbr wex epeli anbi12i exbii
      3bitri ccom crn wtr elrn brdif vex brco epel notbii 19.41v exanali bitr3i
      bitri exnal con2bii dftr2 eldif mpbiran 3bitr4i ) CDEZDFZAGZHZCFZAGZIDJZC
      JZAKKUAZKLZUBZGZMZAUCANVJLGZVKVGVKVDAVIOZCPVFMZCPVGMCAVIBUDVNVOCVNVDAVHOZ
      VDAKOZMZHVCDPZVEMZHZVOVDAVHKUEVPVSVRVTVPVDVAKOZVAAKOZHZDPVSDVDAKKCUFBUGWD
      VCDWBUTWCVBDVDUHVAABQRSUMVQVEVDABQUIRWAVCVTHDPVOVCVTDUJVCVEDUKULTSVFCUNTU
      OCDAUPVMANGVLBANVJUQURUS $.
  $}

  ${
    $d A x $.  $d B x $.  $d R x $.
    coep.1 $e |- A e. _V $.
    coep.2 $e |- B e. _V $.
    $( Composition with the membership relation.  (Contributed by Scott Fenton,
       18-Feb-2013.) $)
    coep $p |- ( A ( _E o. R ) B <-> E. x e. B A R x ) $=
      ( cv wbr cep wex wcel ccom wrex epeli anbi1ci exbii brco df-rex 3bitr4i
      wa ) BAGZDHZUACIHZTZAJUACKZUBTZAJBCIDLHUBACMUDUFAUCUEUBUACFNOPABCIDEFQUBA
      CRS $.

    $( Composition with the converse membership relation.  (Contributed by
       Scott Fenton, 18-Feb-2013.) $)
    coepr $p |- ( A ( R o. `' _E ) B <-> E. x e. A x R B ) $=
      ( cv cep ccnv wbr wa wex wcel ccom wrex vex brcnv epeli bitri anbi1i brco
      exbii df-rex 3bitr4i ) BAGZHIZJZUECDJZKZALUEBMZUHKZALBCDUFNJUHABOUIUKAUGU
      JUHUGUEBHJUJBUEHEAPQUEBERSTUBABCDUFEFUAUHABUCUD $.
  $}

  ${
    $d R x y z $.  $d A x y z $.
    $( A quantifier-free definition of a well-founded relation.  (Contributed
       by Scott Fenton, 11-Apr-2011.)  (Proof shortened by Scott Fenton,
       26-Aug-2026.) $)
    dffr5 $p |- ( R Fr A <->
                  ( ~P A \ { (/) } ) C_ ran ( _E \ ( _E o. `' R ) ) ) $=
      ( vx vz vy cv cep ccnv ccom cdif crn wcel cpw wral wbr wn wrex wex wa vex
      c0 csn wss wfr wel brdif epel brcnv rexbii dfrex2 3bitrri con1bii anbi12i
      coep bitri exbii elrn df-rex 3bitr4i ralbii dfss3 dffr6 3bitr4ri ) CFZGGB
      HZIZJZKZLZCAMUAUBJZNDFZEFZBOZPDVDNZEVDQZCVJNVJVHUCABUDVIVOCVJVLVDVGOZEREC
      UEZVNSZERVIVOVPVREVPVLVDGOZVLVDVFOZPZSVRVLVDGVFUFVSVQWAVNCVLUGVNVTVTVLVKV
      EOZDVDQVMDVDQVNPDVLVDVEETZCTZUNWBVMDVDVLVKBWCDTUHUIVMDVDUJUKULUMUOUPEVDVG
      WDUQVNEVDURUSUTCVJVHVACEDABVBVC $.
  $}

  ${
    $d A x y $.  $d R x y $.
    $( Quantifier-free definition of a strict order.  (Contributed by Scott
       Fenton, 22-Feb-2013.) $)
    dfso2 $p |- ( R Or A <->
              ( R Po A /\ ( A X. A ) C_ ( R u. ( _I u. `' R ) ) ) ) $=
      ( vx vy wor wpo cv wbr wral wa cid cun wcel wi wal wo brun bitr2i 3bitr4i
      vex weq w3o cxp ccnv wss df-so cop opelxp ideq brcnv orbi12i orbi2i df-br
      3orass imbi12i 2albii wrel wb relxp ssrel ax-mp r2al anbi2i bitr4i ) ABEA
      BFZCGZDGZBHZCDUAZVGVFBHZUBZDAICAIZJVEAAUCZBKBUDZLZLZUEZJCDABUFVQVLVEVFVGU
      GZVMMZVRVPMZNZDOCOZVFAMVGAMJZVKNZDOCOVQVLWAWDCDVSWCVTVKVFVGAAUHVKVFVGVPHZ
      VTVHVIVJPZPVHVFVGVOHZPVKWEWFWGVHWGVFVGKHZVFVGVNHZPWFVFVGKVNQWHVIWIVJVFVGD
      TZUIVFVGBCTWJUJUKRULVHVIVJUNVFVGBVOQSVFVGVPUMRUOUPVMUQVQWBURAAUSCDVMVPUTV
      AVKCDAAVBSVCVD $.
  $}

  ${
    $d b ch $.  $d e et $.  $d a b c d e f g h p q P $.  $d a ps $.  $d g si $.
    $d a b c d e f g h p q x A $.  $d p q x ph $.  $d a b c d e f g h x rh $.
    $d a b c d e f g h p q x B $.  $d a b c d e f g h p q x C $.  $d d ta $.
    $d a b c d e f g h p q x D $.  $d a b c d e f g h p q x E $.  $d c th $.
    $d a b c d e f g h p q x F $.  $d a b c d e f g h p q x G $.  $d f ze $.
    $d a b c d e f g h p q x H $.  $d a b c d e f g h p q x S $.
    $d a b c d e f g h x Q $.  $d a b c d e f g h x X $.
    br8.1 $e |- ( a = A -> ( ph <-> ps ) ) $.
    br8.2 $e |- ( b = B -> ( ps <-> ch ) ) $.
    br8.3 $e |- ( c = C -> ( ch <-> th ) ) $.
    br8.4 $e |- ( d = D -> ( th <-> ta ) ) $.
    br8.5 $e |- ( e = E -> ( ta <-> et ) ) $.
    br8.6 $e |- ( f = F -> ( et <-> ze ) ) $.
    br8.7 $e |- ( g = G -> ( ze <-> si ) ) $.
    br8.8 $e |- ( h = H -> ( si <-> rh ) ) $.
    br8.9 $e |- ( x = X -> P = Q ) $.
    br8.10 $e |- R = { <. p , q >. |
       E. x e. S E. a e. P E. b e. P E. c e. P E. d e. P E. e e. P
       E. f e. P E. g e. P E. h e. P ( p = <. <. a , b >. , <. c , d >. >. /\
       q = <. <. e , f >. , <. g , h >. >. /\ ph ) } $.
    $( Substitution for an eight-place predicate.  (Contributed by Scott
       Fenton, 26-Sep-2013.)  (Revised by Mario Carneiro, 3-May-2015.) $)
    br8 $p |- ( ( ( X e. S /\ A e. Q /\ B e. Q ) /\
                   ( C e. Q /\ D e. Q /\ E e. Q ) /\
                   ( F e. Q /\ G e. Q /\ H e. Q ) ) ->
      ( <. <. A , B >. , <. C , D >. >. R <. <. E , F >. , <. G , H >. >. <->
        rh ) ) $=
      ( cop wbr wceq wrex wcel opex eqeq1 3anbi1d rexbidv 2rexbidv 3anbi2d brab
      cv w3a wa wi wb opth vex sylan9bb eqcoms biimp3a a1i rexlimdva rexlimdvva
      sylbi simpl11 simpl12 simpl13 simpl21 simpl22 simpl23 simpl31 eqidd simpr
      simpl32 simpl33 opeq2d eqeq2d 3anbi23d rspc2ev syl113anc 3anbi13d rspc3ev
      opeq1 opeq1d syl31anc rexeqdv rexeqbidv rspcev syl2anc ex impbid bitrid
      opeq2 ) KLVDZMNVDZVDZUCUDVDZUEUFVDZVDZQVEYAUJVPZUKVPZVDZULVPZUMVPZVDZVDZV
      FZYDSVPZTVPZVDZUAVPZUBVPZVDZVDZVFZAVQZUBOVGZUAOVGZTOVGZSOVGZUMOVGZULOVGZU
      KOVGZUJOVGZJRVGZUGRVHZKPVHZLPVHZVQZMPVHZNPVHZUCPVHZVQZUDPVHZUEPVHZUFPVHZV
      QZVQZIUIVPZYKVFZUHVPZYSVFZAVQZUBOVGZUAOVGTOVGZSOVGUMOVGZULOVGUKOVGZUJOVGJ
      RVGYLUVGAVQZUBOVGZUAOVGTOVGZSOVGUMOVGZULOVGUKOVGZUJOVGJRVGUUJUIUHYAYDQXSX
      TVIYBYCVIUVDYAVFZUVLUVQJUJROUVRUVKUVPUKULOOUVRUVJUVOUMSOOUVRUVIUVNTUAOOUV
      RUVHUVMUBOUVRUVEYLUVGAUVDYAYKVJVKVLVMVMVMVMUVFYDVFZUVQUUHJUJROUVSUVPUUFUK
      ULOOUVSUVOUUDUMSOOUVSUVNUUBTUAOOUVSUVMUUAUBOUVSUVGYTYLAUVFYDYSVJVNVLVMVMV
      MVMVCVOUVCUUJIUVCUUHIJUJROUVCJVPZRVHYEOVHVRVRZUUFIUKULOOUWAYFOVHYHOVHVRVR
      ZUUDIUMSOOUWBYIOVHYMOVHVRVRZUUBITUAOOUWCYNOVHYPOVHVRVRZUUAIUBOUUAIVSUWDYQ
      OVHVRYLYTAIYLAEYTIAEVTZYKYAYKYAVFYGXSVFZYJXTVFZVRUWEYGYJXSXTYEYFVIYHYIVIW
      AUWFACUWGEUWFYEKVFZYFLVFZVRACVTYEYFKLUJWBUKWBWAUWHABUWICUNUOWCWIUWGYHMVFZ
      YINVFZVRCEVTYHYIMNULWBUMWBWAUWJCDUWKEUPUQWCWIWCWIWDEIVTZYSYDYSYDVFYOYBVFZ
      YRYCVFZVRUWLYOYRYBYCYMYNVIYPYQVIWAUWMEGUWNIUWMYMUCVFZYNUDVFZVREGVTYMYNUCU
      DSWBTWBWAUWOEFUWPGURUSWCWIUWNYPUEVFZYQUFVFZVRGIVTYPYQUEUFUAWBUBWBWAUWQGHU
      WRIUTVAWCWIWCWIWDWCWEWFWGWHWHWHWHUVCIUUJUVCIVRZUUKUUAUBPVGZUAPVGZTPVGZSPV
      GZUMPVGZULPVGZUKPVGZUJPVGZUUJUUKUULUUMUURUVBIWJUWSUULUUMUUOYAXSMYIVDZVDZV
      FZYTDVQZUBPVGZUAPVGZTPVGZSPVGUMPVGZUXGUUKUULUUMUURUVBIWKUUKUULUUMUURUVBIW
      LUUOUUPUUQUUNUVBIWMUWSUUPUUQUUSYAYAVFZYDYBYRVDZVFZGVQZUBPVGUAPVGZUXOUUOUU
      PUUQUUNUVBIWNUUOUUPUUQUUNUVBIWOUUSUUTUVAUUNUURIWPUWSUUTUVAUXPYDYDVFZIUXTU
      USUUTUVAUUNUURIWSUUSUUTUVAUUNUURIWTUWSYAWQUWSYDWQUVCIWRUXSUXPUYAIVQUXPYDY
      BUEYQVDZVDZVFZHVQUAUBUEUFPPUWQUXRUYDGHUXPUWQUXQUYCYDUWQYRUYBYBYPUEYQXHXAX
      BUTXCUWRUYDUYAHIUXPUWRUYCYDYDUWRUYBYCYBYQUFUEXRXAXBVAXCXDXEUXMUXTUXPYTEVQ
      ZUBPVGUAPVGUXPYDUCYNVDZYRVDZVFZFVQZUBPVGUAPVGUMSTNUCUDPPPUWKUXKUYEUAUBPPU
      WKUXJUXPDEYTUWKUXIYAYAUWKUXHXTXSYINMXRXAXBUQXFVMUWOUYEUYIUAUBPPUWOYTUYHEF
      UXPUWOYSUYGYDUWOYOUYFYRYMUCYNXHXIXBURXCVMUWPUYIUXSUAUBPPUWPUYHUXRFGUXPUWP
      UYGUXQYDUWPUYFYBYRYNUDUCXRXIXBUSXCVMXGXJUXDUXOYAKYFVDZYJVDZVFZYTBVQZUBPVG
      ZUAPVGTPVGZSPVGUMPVGYAXSYJVDZVFZYTCVQZUBPVGZUAPVGTPVGZSPVGUMPVGUJUKULKLMP
      PPUWHUXBUYOUMSPPUWHUWTUYNTUAPPUWHUUAUYMUBPUWHYLUYLABYTUWHYKUYKYAUWHYGUYJY
      JYEKYFXHXIXBUNXFVLVMVMUWIUYOUYTUMSPPUWIUYNUYSTUAPPUWIUYMUYRUBPUWIUYLUYQBC
      YTUWIUYKUYPYAUWIUYJXSYJYFLKXRXIXBUOXFVLVMVMUWJUYTUXNUMSPPUWJUYSUXLTUAPPUW
      JUYRUXKUBPUWJUYQUXJCDYTUWJUYPUXIYAUWJYJUXHXSYHMYIXHXAXBUPXFVLVMVMXGXJUUIU
      XGJUGRUVTUGVFZUUHUXFUJOPVBVUAUUGUXEUKOPVBVUAUUFUXDULOPVBVUAUUEUXCUMOPVBVU
      AUUDUXBSOPVBVUAUUCUXATOPVBVUAUUBUWTUAOPVBVUAUUAUBOPVBXKXLXLXLXLXLXLXLXMXN
      XOXPXQ $.
  $}

  ${
    $d b ch $.  $d e et $.  $d a b c d e f p q P $.  $d p q x ph $.  $d a ps $.
    $d a b c d e f p q x A $.  $d a b c d e f p q x B $.  $d a b c d e f x Q $.
    $d a b c d e f p q x C $.  $d a b c d e f p q x D $.  $d a b c d e f x X $.
    $d a b c d e f p q x E $.  $d d ta $.  $d c th $.  $d a b c d e f x ze $.
    $d a b c d e f p q x F $.  $d a b c d e f p q x S $.
    br6.1 $e |- ( a = A -> ( ph <-> ps ) ) $.
    br6.2 $e |- ( b = B -> ( ps <-> ch ) ) $.
    br6.3 $e |- ( c = C -> ( ch <-> th ) ) $.
    br6.4 $e |- ( d = D -> ( th <-> ta ) ) $.
    br6.5 $e |- ( e = E -> ( ta <-> et ) ) $.
    br6.6 $e |- ( f = F -> ( et <-> ze ) ) $.
    br6.7 $e |- ( x = X -> P = Q ) $.
    br6.8 $e |- R = { <. p , q >. |
       E. x e. S E. a e. P E. b e. P E. c e. P E. d e. P E. e e. P
       E. f e. P ( p = <. a , <. b , c >. >. /\
       q = <. d , <. e , f >. >. /\ ph ) } $.
    $( Substitution for a six-place predicate.  (Contributed by Scott Fenton,
       4-Oct-2013.)  (Revised by Mario Carneiro, 3-May-2015.) $)
    br6 $p |- ( ( X e. S /\
                   ( A e. Q /\ B e. Q /\ C e. Q ) /\
                   ( D e. Q /\ E e. Q /\ F e. Q ) ) ->
      ( <. A , <. B , C >. >. R <. D , <. E , F >. >. <-> ze ) ) $=
      ( cop wbr cv wceq w3a wrex wcel opex eqeq1 eqcom 3anbi1d rexbidv 2rexbidv
      bitrdi 3anbi2d brab wa wi wb vex opth sylan9bb sylbi rexlimdva rexlimdvva
      biimp3a a1i simpl1 simpl2 opeq1 eqeq1d 3anbi23d opeq2d eqid pm3.2i df-3an
      opeq2 mpbiran rspc3ev 3ad2antl3 3anbi13d syl2anc rexeqdv rexeqbidv rspcev
      ex impbid bitrid ) IJKUPZUPZLSTUPZUPZOUQUDURZUEURZUFURZUPZUPZXEUSZUGURZQU
      RZRURZUPZUPZXGUSZAUTZRMVAZQMVAZUGMVAZUFMVAZUEMVAZUDMVAZHPVAZUAPVBZINVBJNV
      BKNVBUTZLNVBSNVBTNVBUTZUTZGUCURZXLUSZUBURZXRUSZAUTZRMVAZQMVAUGMVAZUFMVAUE
      MVAZUDMVAHPVAXMYOAUTZRMVAZQMVAUGMVAZUFMVAUEMVAZUDMVAHPVAYGUCUBXEXGOIXDVCL
      XFVCYLXEUSZYSUUCHUDPMUUDYRUUBUEUFMMUUDYQUUAUGQMMUUDYPYTRMUUDYMXMYOAUUDYMX
      EXLUSXMYLXEXLVDXEXLVEVIVFVGVHVHVHYNXGUSZUUCYEHUDPMUUEUUBYCUEUFMMUUEUUAYAU
      GQMMUUEYTXTRMUUEYOXSXMAUUEYOXGXRUSXSYNXGXRVDXGXRVEVIVJVGVHVHVHUOVKYKYGGYK
      YEGHUDPMYKHURZPVBXHMVBVLVLZYCGUEUFMMUUGXIMVBXJMVBVLVLZYAGUGQMMUUHXNMVBXOM
      VBVLVLZXTGRMXTGVMUUIXPMVBVLXMXSAGXMADXSGXMXHIUSZXKXDUSZVLADVNXHXKIXDUDVOX
      IXJVCVPUUJABUUKDUHUUKXIJUSZXJKUSZVLBDVNXIXJJKUEVOUFVOVPUULBCUUMDUIUJVQVRV
      QVRXSXNLUSZXQXFUSZVLDGVNXNXQLXFUGVOXOXPVCVPUUNDEUUOGUKUUOXOSUSZXPTUSZVLEG
      VNXOXPSTQVORVOVPUUPEFUUQGULUMVQVRVQVRVQWAWBVSVTVTVTYKGYGYKGVLZYHXTRNVAZQN
      VAZUGNVAZUFNVAZUENVAZUDNVAZYGYHYIYJGWCUURYIXEXEUSZXSDUTZRNVAZQNVAUGNVAZUV
      DYHYIYJGWDYJYHGUVHYIUVFGUVELXQUPZXGUSZEUTUVELSXPUPZUPZXGUSZFUTZUGQRLSTNNN
      UUNXSUVJDEUVEUUNXRUVIXGXNLXQWEWFUKWGUUPUVJUVMEFUVEUUPUVIUVLXGUUPXQUVKLXOS
      XPWEWHWFULWGUUQUVNUVEXGXGUSZGUTZGUUQUVMUVOFGUVEUUQUVLXGXGUUQUVKXFLXPTSWLW
      HWFUMWGUVPUVEUVOVLGUVEUVOXEWIXGWIWJUVEUVOGWKWMVIWNWOUVAUVHIXKUPZXEUSZXSBU
      TZRNVAZQNVAUGNVAIJXJUPZUPZXEUSZXSCUTZRNVAZQNVAUGNVAUDUEUFIJKNNNUUJUUSUVTU
      GQNNUUJXTUVSRNUUJXMUVRABXSUUJXLUVQXEXHIXKWEWFUHWPVGVHUULUVTUWEUGQNNUULUVS
      UWDRNUULUVRUWCBCXSUULUVQUWBXEUULXKUWAIXIJXJWEWHWFUIWPVGVHUUMUWEUVGUGQNNUU
      MUWDUVFRNUUMUWCUVECDXSUUMUWBXEXEUUMUWAXDIXJKJWLWHWFUJWPVGVHWNWQYFUVDHUAPU
      UFUAUSZYEUVCUDMNUNUWFYDUVBUEMNUNUWFYCUVAUFMNUNUWFYBUUTUGMNUNUWFYAUUSQMNUN
      UWFXTRMNUNWRWSWSWSWSWSWTWQXAXBXC $.
  $}

  ${
    $d a b c d p q x A $.  $d a b c d p q x B $.  $d b ch $.  $d a b c d x Q $.
    $d a b c d p q x C $.  $d a b c d p q x D $.  $d a ps $.  $d a b c d x X $.
    $d a b c d p q P $.  $d a b c d p q x S $.  $d a b c d x ta $.  $d c th $.
    $d p q x ph $.
    br4.1 $e |- ( a = A -> ( ph <-> ps ) ) $.
    br4.2 $e |- ( b = B -> ( ps <-> ch ) ) $.
    br4.3 $e |- ( c = C -> ( ch <-> th ) ) $.
    br4.4 $e |- ( d = D -> ( th <-> ta ) ) $.
    br4.5 $e |- ( x = X -> P = Q ) $.
    br4.6 $e |- R = { <. p , q >. |
       E. x e. S E. a e. P E. b e. P E. c e. P E. d e. P
       ( p = <. a , b >. /\ q = <. c , d >. /\ ph ) } $.
    $( Substitution for a four-place predicate.  (Contributed by Scott Fenton,
       9-Oct-2013.)  (Revised by Mario Carneiro, 14-Oct-2013.) $)
    br4 $p |- ( ( X e. S /\
                   ( A e. Q /\ B e. Q ) /\
                   ( C e. Q /\ D e. Q ) ) ->
      ( <. A , B >. R <. C , D >. <-> ta ) ) $=
      ( cop wbr cv wceq w3a wrex wcel wa eqeq1 3anbi1d rexbidv 2rexbidv 3anbi2d
      opex brab wi wb vex opth sylan9bb eqcoms biimp3a a1i rexlimdva rexlimdvva
      sylbi simpl1 simpl2l simpl2r simpl3l simpl3r eqidd simpr 3anbi23d rspc2ev
      opeq1 eqeq2d opeq2 syl113anc 3anbi13d syl3anc rexeqdv rexeqbidv rspcev ex
      syl2anc impbid bitrid ) GHUHZIJUHZMUIWPRUJZSUJZUHZUKZWQTUJZUAUJZUHZUKZAUL
      ZUAKUMZTKUMZSKUMZRKUMZFNUMZONUNZGLUNZHLUNZUOZILUNZJLUNZUOZULZEQUJZWTUKZPU
      JZXDUKZAULZUAKUMZTKUMSKUMZRKUMFNUMXAYCAULZUAKUMZTKUMSKUMZRKUMFNUMXKQPWPWQ
      MGHVAIJVAXTWPUKZYFYIFRNKYJYEYHSTKKYJYDYGUAKYJYAXAYCAXTWPWTUPUQURUSUSYBWQU
      KZYIXIFRNKYKYHXGSTKKYKYGXFUAKYKYCXEXAAYBWQXDUPUTURUSUSUGVBXSXKEXSXIEFRNKX
      SFUJZNUNWRKUNUOUOZXGESTKKYMWSKUNXBKUNUOUOZXFEUAKXFEVCYNXCKUNUOXAXEAEXAACX
      EEACVDZWTWPWTWPUKWRGUKZWSHUKZUOYOWRWSGHRVESVEVFYPABYQCUBUCVGVMVHCEVDZXDWQ
      XDWQUKXBIUKZXCJUKZUOYRXBXCIJTVEUAVEVFYSCDYTEUDUEVGVMVHVGVIVJVKVLVLXSEXKXS
      EUOZXLXFUALUMZTLUMZSLUMZRLUMZXKXLXOXREVNUUAXMXNWPWPUKZXECULZUALUMTLUMZUUE
      XMXNXLXREVOXMXNXLXREVPUUAXPXQUUFWQWQUKZEUUHXPXQXLXOEVQXPXQXLXOEVRUUAWPVSU
      UAWQVSXSEVTUUGUUFUUIEULUUFWQIXCUHZUKZDULTUAIJLLYSXEUUKCDUUFYSXDUUJWQXBIXC
      WCWDUDWAYTUUKUUIDEUUFYTUUJWQWQXCJIWEWDUEWAWBWFUUCUUHWPGWSUHZUKZXEBULZUALU
      MTLUMRSGHLLYPXFUUNTUALLYPXAUUMABXEYPWTUULWPWRGWSWCWDUBWGUSYQUUNUUGTUALLYQ
      UUMUUFBCXEYQUULWPWPWSHGWEWDUCWGUSWBWHXJUUEFONYLOUKZXIUUDRKLUFUUOXHUUCSKLU
      FUUOXGUUBTKLUFUUOXFUAKLUFWIWJWJWJWKWMWLWNWO $.
  $}

  ${
    $d A x y z $.  $d B x y z $.
    $( Another distributive law of converse over class composition.
       (Contributed by Scott Fenton, 3-May-2014.) $)
    cnvco1 $p |- `' ( `' A o. B ) = ( `' B o. A ) $=
      ( vx vy vz ccnv ccom relcnv relco cv wbr wa wex cop wcel vex brcnv bicomi
      anbi12ci opelco exbii opelcnv bitri 3bitr4i eqrelriiv ) CDAFZBGZFZBFZAGZU
      GHUIAIDJZEJZBKZULCJZUFKZLZEMZUNULAKZULUKUIKZLZEMUNUKNZUHOZVAUJOUPUTEUMUSU
      OURUSUMULUKBEPZDPZQRULUNAVCCPZQSUAVBUKUNNUGOUQUNUKUGVEVDUBEUKUNUFBVDVETUC
      EUNUKUIAVEVDTUDUE $.

    $( Another distributive law of converse over class composition.
       (Contributed by Scott Fenton, 3-May-2014.) $)
    cnvco2 $p |- `' ( A o. `' B ) = ( B o. `' A ) $=
      ( vx vy vz ccnv ccom relcnv relco cv wbr wa wex cop wcel vex brcnv bicomi
      anbi12ci opelco exbii opelcnv bitri 3bitr4i eqrelriiv ) CDABFZGZFZBAFZGZU
      GHBUIIDJZEJZUFKZULCJZAKZLZEMZUNULUIKZULUKBKZLZEMUNUKNZUHOZVAUJOUPUTEUMUSU
      OURUKULBDPZEPZQURUOUNULACPZVDQRSUAVBUKUNNUGOUQUNUKUGVEVCUBEUKUNAUFVCVETUC
      EUNUKBUIVEVCTUDUE $.
  $}

  ${
    $d A x y z p $.  $d B x y z p $.
    $( Quantifier-free definition of membership in a domain.  (Contributed by
       Scott Fenton, 21-Jan-2017.) $)
    eldm3 $p |- ( A e. dom B <-> ( B |` { A } ) =/= (/) ) $=
      ( vx vy vp vz cdm wcel cvv csn cres c0 wne wceq cv eleq1 cop wex wa exbii
      elex wn snprc reseq2 res0 eqtrdi sylbi necon1ai reseq2d neeq1d dfclel vex
      sneq eldm2 n0 wrex elres pm5.32i opeq1 eqeq2d anbi1d bitr3id exbidv rexsn
      weq bitri excom 3bitri 3bitr4i vtoclbg pm5.21nii ) ABGZHZAIHZBAJZKZLMZAVL
      UAVNVPLVNUBVOLNZVPLNAUCVRVPBLKLVOLBUDBUEUFUGUHCOZVLHZBVSJZKZLMZVMVQCAIVSA
      VLPVSANZWBVPLWDWAVOBVSAUMUIUJVSDOZQZBHZDREOZWFNZWHBHZSZERZDRZVTWCWGWLDEWF
      BUKTDVSBCULZUNWCWHWBHZERWKDRZERWMEWBUOWOWPEWOWHFOZWEQZNZWRBHZSZDRZFWAUPWP
      FDWHBWAUQXBWPFVSWNFCVEZXAWKDXAWSWJSXCWKWSWJWTWHWRBPURXCWSWIWJXCWRWFWHWQVS
      WEUSUTVAVBVCVDVFTWKEDVGVHVIVJVK $.
  $}

  $( Quantifier-free definition of membership in a range.  (Contributed by
     Scott Fenton, 21-Jan-2017.) $)
  elrn3 $p |- ( A e. ran B <-> ( B i^i ( _V X. { A } ) ) =/= (/) ) $=
    ( crn wcel ccnv cdm csn cres wne cvv cxp cin df-rn eleq2i eldm3 wceq ineq2i
    c0 cnvxp cnvin df-res 3eqtr4ri eqeq1i wrel wb cnveq0 ax-mp bitr4i necon3bii
    relinxp 3bitri ) ABCZDABEZFZDUMAGZHZRIBJUOKZLZRIULUNABMNAUMOUPRURRUPRPUREZR
    PZURRPZUPUSRUMUQEZLUMUOJKZLUSUPVBVCUMJUOSQBUQTUMUOUAUBUCURUDVAUTUEJUOBUJURU
    FUGUHUIUK $.

  ${
    $d R x y z $.  $d A x y z $.

    $( The converse of a partial ordering is still a partial ordering.
       (Contributed by Scott Fenton, 13-Jun-2018.) $)
    pocnv $p |- ( R Po A -> `' R Po A ) $=
      ( vx vy vz wpo ccnv cv wcel wa wbr poirr vex brcnv sylnibr wi 3anrev potr
      w3a sylan2b anbi12ci 3imtr4g ispod ) ABFZCDEABGZUDCHZAIZJUFUFBKUFUFUEKAUF
      BLUFUFBCMZUHNOUDUGDHZAIZEHZAIZSZJUKUIBKZUIUFBKZJZUKUFBKZUFUIUEKZUIUKUEKZJ
      UFUKUEKUMUDULUJUGSUPUQPUGUJULQAUKUIUFBRTURUOUSUNUFUIBUHDMZNUIUKBUTEMZNUAU
      FUKBUHVANUBUC $.

    $( The converse of a strict ordering is still a strict ordering.
       (Contributed by Scott Fenton, 13-Jun-2018.) $)
    socnv $p |- ( R Or A -> `' R Or A ) $=
      ( wor ccnv cnvso biimpi ) ABCABDCABEF $.
  $}

  ${
    $d A y z $.  $d B y z $.  $d F y z $.  $d X y z $.
    elintfv.1 $e |- X e. _V $.
    $( Membership in an intersection of function values.  (Contributed by Scott
       Fenton, 9-Dec-2021.) $)
    elintfv $p |- ( ( F Fn A /\ B C_ A ) ->
       ( X e. |^| ( F " B ) <-> A. y e. B X e. ( F ` y ) ) ) $=
      ( vz cima cint wcel cv wi wal wfn wss wa cfv wral elint wceq wrex r19.23v
      imbi1d bitr4di albidv ralcom4 eqcom imbi1i albii fvex eleq2 ceqsalv bitri
      fvelimab ralbii bitr3i bitrdi bitrid ) EDCHZIJGKZUSJZEUTJZLZGMZDBNCBOPZEA
      KZDQZJZACRZGEUSFSVEVDVGUTTZVBLZACRZGMZVIVEVCVLGVEVCVJACUAZVBLVLVEVAVNVBAB
      CUTDUNUCVJVBACUBUDUEVMVKGMZACRVIVKAGCUFVOVHACVOUTVGTZVBLZGMVHVKVQGVJVPVBV
      GUTUGUHUIVBVHGVGVFDUJUTVGEUKULUMUOUPUQUR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Properties of functions and mappings
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A condition for subset trichotomy for functions.  (Contributed by Scott
     Fenton, 19-Apr-2011.) $)
  funpsstri $p |- ( ( Fun H /\ ( F C_ H /\ G C_ H ) /\
                      ( dom F C_ dom G \/ dom G C_ dom F ) ) ->
                    ( F C. G \/ F = G \/ G C. F ) ) $=
    ( wfun wss wa cdm wo w3a wpss wceq w3o cres funssres anim12d ssres2 orim12i
    wi ex sseq12 wb ancoms orbi12d imbitrid syl6 3imp sspsstri sylib ) CDZACEZB
    CEZFZAGZBGZEZUNUMEZHZIABEZBAEZHZABJABKBAJLUIULUQUTUIULCUMMZAKZCUNMZBKZFZUQU
    TRUIUJVBUKVDUIUJVBCANSUIUKVDCBNSOUQVAVCEZVCVAEZHVEUTUOVFUPVGUMUNCPUNUMCPQVE
    VFURVGUSVAAVCBTVDVBVGUSUAVCBVAATUBUCUDUEUFABUGUH $.

  ${
    $d F p x y z $.  $d G p x y z $.
    $( If a class ` F ` is a proper subset of a function ` G ` , then
       ` dom F C. dom G ` .  (Contributed by Scott Fenton, 20-Apr-2011.) $)
    fundmpss $p |- ( Fun G -> ( F C. G -> dom F C. dom G ) ) $=
      ( vx vy vz vp wpss wss wn wa wi syl cv wbr wex wcel adantl ex wal exlimdv
      wfun cdm pssss dmss a1i cdif c0 wne pssdif n0 wrel funrel reldif cop wceq
      sylib elrel eleq1 df-br bitr4di biimpcd 2eximdv difss ssbri eximi simprbi
      mpd adantr brdif ssbrd ad2antlr weq dffun2 2sp breq2 biimprd syl6 simplbi
      sps expd impel adantlr com23 mpdd mtod jcad eximdv nss vex notbii anbi12i
      syld eldm exbii bitri sylibr dfpss3 imbitrrdi ) BUAZABGZAUBZBUBZHZXBXAHIZ
      JXAXBGWSWTXCXDWTXCKWSWTABHXCABUCZABUDLUEWSWTXDWSWTJZCMZDMZBNZDOZXGEMZANZE
      OZIZJZCOZXDXFFMZBAUFZPZFOZXPWTXTWSWTXRUGUHXTABUIFXRUJUPQXFXSXPFXFXSXGXHXR
      NZDOZCOZXPWSXSYCKZWTWSXRUKZYDWSBUKZYEBULBAUMLYEXSYCYEXSJZXQXGXHUNZUOZDOCO
      YCCDXQXRUQYGYIYACDXSYIYAKYEYIXSYAYIXSYHXRPYAXQYHXRURXGXHXRUSUTVAQVBVGRLVH
      XFYBXOCXFYBXJXNYBXJKXFYAXIDXRBXGXHBAVCVDVEUEXFYAXNDXFYAXNXFYAJZXMXGXHANZY
      AYKIZXFYAXIYLXGXHBAVIZVFQYJXLYKEYJXLXGXKBNZYKWTXLYNKWSYAWTABXGXKXEVJVKYJY
      NXLYKWSYAYNXLYKKZKZWTWSXIYPYAWSXIYNYOWSXIYNJZDEVLZYOWSYQYRKZESDSZCSZYSWSY
      FUUACDEBVMVFYTYSCYSDEVNVSLYRYKXLXHXKXGAVOVPVQVTYAXIYLYMVRWAWBWCWDTWERTWFW
      GWLTVGXDXGXBPZXGXAPZIZJZCOXPCXBXAWHUUEXOCUUBXJUUDXNDXGBCWIZWMUUCXMEXGAUUF
      WMWJWKWNWOWPRWFXAXBWQWR $.
  $}

  $( Given two functions with equal domains, equality only requires one
     direction of the subset relationship.  (Contributed by Scott Fenton,
     24-Apr-2012.)  (Proof shortened by Mario Carneiro, 3-May-2015.) $)
  funsseq $p |- ( ( Fun F /\ Fun G /\ dom F = dom G ) ->
                  ( F = G <-> F C_ G ) ) $=
    ( wfun cdm wceq w3a eqimss wa cres simpl3 reseq2d funssres 3ad2antl2 simpl2
    wss wrel funrel resdm 3syl 3eqtr3d ex impbid2 ) ACZBCZADZBDZEZFZABEZABOZABG
    UHUJUIUHUJHZBUEIZBUFIZABUKUEUFBUCUDUGUJJKUDUCUJULAEUGBALMUKUDBPUMBEUCUDUGUJ
    NBQBRSTUAUB $.

  ${
    $d A x y z $.  $d B x y z $.  $d C x y z $.  $d F x y z $.
    fununiq.1 $e |- A e. _V $.
    fununiq.2 $e |- B e. _V $.
    fununiq.3 $e |- C e. _V $.
    $( The uniqueness condition of functions.  (Contributed by Scott Fenton,
       18-Feb-2013.) $)
    fununiq $p |- ( Fun F -> ( ( A F B /\ A F C ) -> B = C ) ) $=
      ( vx vy vz cv wbr wa wi wal wceq cvv wcel wb breq12 wfun wrel weq 3adant3
      dffun2 w3a 3adant2 anbi12d eqeq12 3adant1 imbi12d spc3gv mp3an simplbiim
      ) DUADUBHKZIKZDLZUOJKZDLZMZIJUCZNZJOIOHOZABDLZACDLZMZBCPZNZHIJDUEAQRBQRCQ
      RVCVHNEFGVBVHHIJABCQQQUOAPZUPBPZURCPZUFZUTVFVAVGVLUQVDUSVEVIVJUQVDSVKUOAU
      PBDTUDVIVKUSVESVJUOAURCDTUGUHVJVKVAVGSVIUPBURCUIUJUKULUMUN $.
  $}

  ${
    funbreq.1 $e |- A e. _V $.
    funbreq.2 $e |- B e. _V $.
    funbreq.3 $e |- C e. _V $.
    $( An equality condition for functions.  (Contributed by Scott Fenton,
       18-Feb-2013.) $)
    funbreq $p |- ( ( Fun F /\ A F B ) -> ( A F C <-> B = C ) ) $=
      ( wfun wbr wa wceq fununiq expdimp wi breq2 biimpcd adantl impbid ) DHZAB
      DIZJACDIZBCKZSTUAUBABCDEFGLMTUBUANSUBTUABCADOPQR $.
  $}

  ${
    br1steq.1 $e |- A e. _V $.
    br1steq.2 $e |- B e. _V $.
    $( Uniqueness condition for the binary relation ` 1st ` .  (Contributed by
       Scott Fenton, 11-Apr-2014.)  (Proof shortened by Mario Carneiro,
       3-May-2015.) $)
    br1steq $p |- ( <. A , B >. 1st C <-> C = A ) $=
      ( cvv wcel cop c1st wbr wceq wb br1steqg mp2an ) AFGBFGABHCIJCAKLDEABCFFM
      N $.

    $( Uniqueness condition for the binary relation ` 2nd ` .  (Contributed by
       Scott Fenton, 11-Apr-2014.)  (Proof shortened by Mario Carneiro,
       3-May-2015.) $)
    br2ndeq $p |- ( <. A , B >. 2nd C <-> C = B ) $=
      ( cvv wcel cop c2nd wbr wceq wb br2ndeqg mp2an ) AFGBFGABHCIJCBKLDEABCFFM
      N $.
  $}

  ${
    $d A p x y z $.
    $( Definition of domain in terms of ` 1st ` and image.  (Contributed by
       Scott Fenton, 11-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.)
       (Proof shortened by Peter Mazsa, 2-Oct-2022.) $)
    dfdm5 $p |- dom A = ( ( 1st |` ( _V X. _V ) ) " A ) $=
      ( vx vy vp vz c1st cvv cv cop wcel wex wbr wa wceq excom vex bitri anbi1i
      exbii 3bitr4i cdm cxp cres cima breq1 eleq1 anbi12d br1steq equcom bitrdi
      opex ceqsexv opeq1 eleq1d 3bitr3ri ancom anass brresi elvv 19.41vv elima2
      eldm2 eqriv ) BAUAZFGGUBZUCZAUDZBHZCHZIZAJZCKZDHZAJZVMVHVFLZMZDKZVHVDJVHV
      GJVMEHZVIIZNZVMVHFLZVNMZMZEKZDKZCKWDCKZDKVLVQWDCDOVKWECWCDKZEKVRVHNZVSAJZ
      MZEKWEVKWGWJEWBWJDVSVRVIUKVTWBVSVHFLZWIMWJVTWAWKVNWIVMVSVHFUEVMVSAUFUGWKW
      HWIWKVHVRNWHVRVIVHEPCPUHBEUIQRUJULSWCEDOWIVKEVHBPZWHVSVJAVRVHVIUMUNULUOSV
      PWFDVPVOVNMZWFVNVOUPVTEKCKZWAMZVNMWNWBMWMWFWNWAVNUQVOWOVNVOVMVEJZWAMWOVEV
      MVHFWLURWPWNWAWPVTCKEKWNECVMUSVTECOQRQRVTWBCEUTTQSTCVHAWLVBDVHVFAWLVATVC
      $.

    $( Definition of range in terms of ` 2nd ` and image.  (Contributed by
       Scott Fenton, 17-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.)
       (Proof shortened by Peter Mazsa, 2-Oct-2022.) $)
    dfrn5 $p |- ran A = ( ( 2nd |` ( _V X. _V ) ) " A ) $=
      ( vx vy vp vz c2nd cvv cv cop wcel wex wbr wa wceq excom vex bitri anbi1i
      exbii 3bitr4i crn cxp cres cima breq1 eleq1 anbi12d br2ndeq equcom bitrdi
      opex ceqsexv opeq2 eleq1d 3bitr3ri ancom anass brresi elvv 19.41vv elima2
      elrn2 eqriv ) BAUAZFGGUBZUCZAUDZCHZBHZIZAJZCKZDHZAJZVMVIVFLZMZDKZVIVDJVIV
      GJVMVHEHZIZNZVMVIFLZVNMZMZEKZDKZCKWDCKZDKVLVQWDCDOVKWECWCDKZEKVRVINZVSAJZ
      MZEKWEVKWGWJEWBWJDVSVHVRUKVTWBVSVIFLZWIMWJVTWAWKVNWIVMVSVIFUEVMVSAUFUGWKW
      HWIWKVIVRNWHVHVRVICPEPUHBEUIQRUJULSWCEDOWIVKEVIBPZWHVSVJAVRVIVHUMUNULUOSV
      PWFDVPVOVNMZWFVNVOUPVTEKCKZWAMZVNMWNWBMWMWFWNWAVNUQVOWOVNVOVMVEJZWAMWOVEV
      MVIFWLURWPWNWACEVMUSRQRVTWBCEUTTQSTCVIAWLVBDVIVFAWLVATVC $.
  $}

  ${
    $d A z $.  $d B z $.  $d C z $.  $d D z $.
    $( Alternate way of saying that an ordered pair is in a composition.
       (Contributed by Scott Fenton, 6-May-2018.) $)
    opelco3 $p |- ( <. A , B >. e. ( C o. D ) <->
       B e. ( C " ( D " { A } ) ) ) $=
      ( vz cop ccom wcel wbr csn cima df-br cvv wa relco wn c0 ima0 wex wb wceq
      brrelex12i snprc noel imaeq2 imaeq2d eqtri eqtrdi eleq2d sylbi con4i elex
      imaeq2i mtbiri jca wrex df-rex elimasng elvd bitr4di adantr anbi1d exbidv
      cv bitr2id brcog elimag adantl 3bitr4d pm5.21nii bitr3i ) ABFCDGZHABVLIZB
      CDAJZKZKZHZABVLLVMAMHZBMHZNZVQABVLCDOUBVQVRVSVRVQVRPVNQUAZVQPAUCWAVQBQHBU
      DWAVPQBWAVPCDQKZKZQWAVOWBCVNQDUEUFWCCQKQWBQCDRUMCRUGUHUIUNUJUKBVPULUOVTAE
      VDZDIZWDBCIZNZESZWFEVOUPZVMVQWIWDVOHZWFNZESVTWHWFEVOUQVTWKWGEVTWJWEWFVRWJ
      WETVSVRWJAWDFDHZWEVRWJWLTEDAWDMMURUSAWDDLUTVAVBVCVEEABCDMMVFVSVQWITVREBCV
      OMVGVHVIVJVK $.
  $}

  ${
    $d A x $.  $d B p x y z $.  $d R p x y z $.
    $( Quantifier-free expression saying that a class is a member of an image.
       (Contributed by Scott Fenton, 8-May-2018.) $)
    elima4 $p |- ( A e. ( R " B ) <-> ( R i^i ( B X. { A } ) ) =/= (/) ) $=
      ( vx vp vy vz wcel cvv csn cxp cin c0 wne wceq cv wex wa 3bitri exbii xp0
      cima elex xpeq2 eqtrdi ineq2d in0 necon3i snnzb sylibr sneq xpeq2d neeq1d
      eleq1 cop elin ancom anbi1i anass 2exbii 19.41vv bitr3i exrot3 weq anbi2d
      elxp opex ceqsexv an12 velsn vex opeq2 eleq1d n0 elima3 vtoclbg pm5.21nii
      3bitr4ri ) ACBUBZHZAIHZCBAJZKZLZMNZAVSUCWEWBMNWAWBMWDMWBMOZWDCMLMWFWCMCWF
      WCBMKMWBMBUDBUAUEUFCUGUEUHAUIUJDPZVSHZCBWGJZKZLZMNZVTWEDAIWGAVSUNWGAOZWKW
      DMWMWJWCCWMWIWBBWGAUKULUFUMEPZWKHZEQZFPZBHZWQWGUOZCHZRZFQZWLWHWPWNWQGPZUO
      ZOZWRXCWIHZRZRZGQFQZWNCHZRZEQZXEXGXJRZRZEQZGQZFQZXBWOXKEWOXJWNWJHZRXRXJRX
      KWNCWJUPXJXRUQXRXIXJFGWNBWIVFURSTXLXNGQFQZEQXQXSXKEXSXHXJRZGQFQXKXTXNFGXE
      XGXJUSUTXHXJFGVAVBTXNEFGVCVBXPXAFXPXGXDCHZRZGQGDVDZWRYARZRZGQXAXOYBGXMYBE
      XDWQXCVGXEXJYAXGWNXDCUNVEVHTYBYEGYBWRXFYARRXFYDRYEWRXFYAUSWRXFYAVIXFYCYDG
      WGVJURSTYDXAGWGDVKZYCYAWTWRYCXDWSCXCWGWQVLVMVEVHSTSEWKVNFWGCBYFVOVRVPVQ
      $.
  $}

  $( The value of the converse of ` 1st ` restricted to a singleton.
     (Contributed by Scott Fenton, 2-Jul-2020.) $)
  fv1stcnv $p |- ( ( X e. A /\ Y e. V ) ->
       ( `' ( 1st |` ( A X. { Y } ) ) ` X ) = <. X , Y >. ) $=
    ( wcel wa c1st csn cxp cres ccnv cfv cop wceq wbr wb cvv bitrd mpbird wf1o
    snidg anim2i eqid jctir opex brcnvg mpan2 brres adantr opelxp anbi1i anbi2d
    br1steqg bitrid wfn 1stconst f1ocnv f1ofn 3syl simpl fnbrfvb syl2an2 ) CAEZ
    DBEZFZCGADHZIZJZKZLCDMZNZCVJVIOZVEVLVCDVFEZFZCCNZFZVEVNVOVDVMVCDBUAUBCUCUDV
    EVLVJVGEZVJCGOZFZVPVCVLVSPVDVCVLVJCVHOZVSVCVJQEVLVTPCDUECVJAQVHUFUGVGVJCGAU
    HRUIVSVNVRFVEVPVQVNVRCDAVFUJUKVEVRVOVNCDCABUMULUNRSVDVIAUOZVCVCVKVLPVDVGAVH
    TAVGVITWAADBUPVGAVHUQAVGVIURUSVCVDUTACVJVIVAVBS $.

  $( The value of the converse of ` 2nd ` restricted to a singleton.
     (Contributed by Scott Fenton, 2-Jul-2020.) $)
  fv2ndcnv $p |- ( ( X e. V /\ Y e. A ) ->
       ( `' ( 2nd |` ( { X } X. A ) ) ` Y ) = <. X , Y >. ) $=
    ( wcel wa c2nd csn cxp cres ccnv cfv cop wceq wbr wb wf1o cvv adantl bitrd
    snidg anim1i eqid jctir wfn 2ndconst adantr f1ocnv f1ofn 3syl sylancom opex
    fnbrfvb brcnvg mpan2 brres opelxp anbi1i br2ndeqg anbi2d bitrid mpbird ) CB
    EZDAEZFZDGCHZAIZJZKZLCDMZNZCVFEZVDFZDDNZFZVEVMVNVCVLVDCBUAUBDUCUDVEVKDVJVIO
    ZVOVCVDVIAUEZVKVPPVEVGAVHQZAVGVIQVQVCVRVDCABUFUGVGAVHUHAVGVIUIUJADVJVIUMUKV
    EVPVJDVHOZVOVDVPVSPZVCVDVJREVTCDULDVJARVHUNUOSVEVSVJVGEZVJDGOZFZVOVDVSWCPVC
    VGVJDGAUPSWCVMWBFVEVOWAVMWBCDVFAUQURVEWBVNVMCDDBAUSUTVATTTVB $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Ordinal numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z A $.
    $( A class of transitive sets is partially ordered by ` _E ` .
       (Contributed by Scott Fenton, 15-Oct-2010.) $)
    elpotr $p |- ( A. z e. A Tr z -> _E Po A ) $=
      ( vx vy wel wa wi wal wral wtr cep wpo alral alimi syl ralcom ralbii epel
      cv wbr ralimi bitri sylib dftr2 df-po anbi12i imbi12i elirrv mtbir bitr3i
      wn biantrur 2ralbii bitr4i 3imtr4i ) CDEZDAEZFZCAEZGZDHZCHZABIZUTABIZDBIZ
      CBIZASZJZABIBKLZVCUTDBIZCBIZABIZVFVBVKABVBVJCHVKVAVJCUTDBMNVJCBMOUAVLVJAB
      IZCBIVFVJACBBPVMVECBUTADBBPQUBUCVHVBABCDVGUDQVICSZVNKTZUKZVNDSZKTZVQVGKTZ
      FZVNVGKTZGZFZABIZDBICBIVFCDABKUEVDWDCDBBUTWCABUTWBWCVTURWAUSVRUPVSUQDVNRA
      VQRUFAVNRUGVPWBVOCCECUHCVNRUIULUJQUMUNUO $.
  $}

  $( Given ~ ax-reg , an ordinal is a transitive class totally ordered by the
     membership relation.  (Contributed by Scott Fenton, 28-Jan-2011.) $)
  dford5reg $p |- ( Ord A <-> ( Tr A /\ _E Or A ) ) $=
    ( word wtr cep wwe wa wor df-ord wfr zfregfr df-we mpbiran anbi2i bitri ) A
    BACZADEZFOADGZFAHPQOPADIQAJADKLMN $.

  ${
    $d x y $.  $d y ph $.  $d y ps $.
    $( Lemma for ~ dfon2 .  (Contributed by Scott Fenton, 28-Feb-2011.) $)
    dfon2lem1 $p |- Tr U. { x | ( ph /\ Tr x /\ ps ) } $=
      ( vy cv wtr w3a cab cuni truni wcel wsbc nfsbc1v nfv vex weq sbceq1a treq
      nf3an 3anbi123d elabf simp2bi mprg ) DEZFZACEZFZBGZCHZIFDUIDUIJUDUIKACUDL
      ZUEBCUDLZUHUJUEUKGCUDUJUEUKCACUDMUECNBCUDMSDOCDPAUJUGUEBUKACUDQUFUDRBCUDQ
      TUAUBUC $.
  $}

  ${
    $d x A $.
    $( Lemma for ~ dfon2 .  (Contributed by Scott Fenton, 28-Feb-2011.) $)
    dfon2lem2 $p |- U. { x | ( x C_ A /\ ph /\ ps ) } C_ A $=
      ( cv wss w3a cab cpw cuni simp1 ss2abi df-pw sseqtrri sspwuni mpbi ) CEDF
      ZABGZCHZDIZFSJDFSQCHTRQCQABKLCDMNSDOP $.
  $}

  ${
    $d A x z w t $.

    $( Lemma for ~ dfon2 .  All sets satisfying the new definition are
       transitive and untangled.  (Contributed by Scott Fenton,
       25-Feb-2011.) $)
    dfon2lem3 $p |- ( A e. V -> ( A. x ( ( x C. A /\ Tr x ) -> x e. A ) ->
                                        ( Tr A /\ A. z e. A -. z e. z ) ) ) $=
      ( vw vt wcel cv wtr wa wi wel wn wral wss w3a wceq sseq1 treq cvv wal cab
      wpss cuni untelirr wrex eluni2 raleq 3anbi123d elequ1 elequ2 bitrd notbid
      vex elab cbvralvw biimpi 3ad2ant3 sylbi rsp syl rexlimiv dfon2lem2 dfpss2
      mprg dfon2lem1 ssexg mpan psseq1 anbi12d eleq1 imbi12d spcgv imp csuc csn
      sylan snssi cun unss df-suc sseq1i sylbb2 sylancr suctr ax-mp mprgbir nfv
      untuni nfra1 nf3an nfab nfuni untsucf raleqf cbvabv elab2g biimprd sucexg
      nfcv nfsuc syl11 mp3an23 com12 elssuni sucssel syl5 syld mpan2i biimtrrid
      mpd syl6 mpani mt3i pm3.2i mpbii ex ) CDGZAHZCUCZXSIZJZXSCGZKZAUAZCIZBBLZ
      MZBCNZJZXRYEJZEHZCOZYLIZFFLZMZFYLNZPZEUBZUDZCQZYJYKUUAYTYTGZYHUUBMBYTBYTU
      EBHZYTGBALZAYSUFYHAUUCYSUGUUDYHAYSXSYSGZYHBXSNZUUDYHKUUEXSCOZYAYPFXSNZPZU
      UFYRUUIEXSAUNYLXSQYMUUGYNYAYQUUHYLXSCRYLXSSYPFYLXSUHUIUOUUHUUGUUFYAUUHUUF
      YPYHFBXSFHUUCQZYOYGUUJYOBFLYGFBFUJFBBUKULUMUPUQURUSZYHBXSUTVAVBUSVEYKYTCO
      ZUUAMZUUBYNYQECVCZUULUUMJYTCUCZYKUUBYTCVDYKUUOYTIZUUBYMYQEVFZYKUUOUUPJZYT
      CGZUUBXRYTTGZYEUURUUSKZUULXRUUTUUNYTCDVGVHUUTYEUVAYDUVAAYTTXSYTQZYBUURYCU
      USUVBXTUUOYAUUPXSYTCVIXSYTSVJXSYTCVKVLVMVNVQUUSYTVOZCOZUUBUUSUULYTVPZCOZU
      VDUUNYTCVRUULUVFJYTUVEVSZCOUVDYTUVECVTUVCUVGCYTWAWBWCWDUUSUVDUVCYSGZUUBUV
      DUUSUVHUVDUVCIZYPFUVCNZUUSUVHKUUPUVIUUQYTWEWFYHBYTNZUVJUVKUUFAYSBAYSWIUUK
      WGZBFYTFYSYRFEYMYNYQFYMFWHYNFWHYPFYLWJWKWLWMZWNWFUVCTGZUVDUVIUVJPZUVHUUSU
      VNUVHUVOUUCCOZUUCIZYPFUUCNZPZUVOBUVCYSTUUCUVCQUVPUVDUVQUVIUVRUVJUUCUVCCRU
      UCUVCSYPFUUCUVCFUUCWTFYTUVMXAWOUIYRUVSEBYLUUCQYMUVPYNUVQYQUVRYLUUCCRYLUUC
      SYPFYLUUCUHUIWPWQWRYTCWSXBXCXDUVHUVCYTOUUSUUBUVCYSXEYTYTCXFXGXHXKXLXIXJXM
      XNUUAUUPUVKJYJUUPUVKUUQUVLXOUUAUUPYFUVKYIYTCSYHBYTCUHVJXPVAXQ $.
  $}

  ${
    $d A x y z $.  $d B x y z $.
    dfon2lem4.1 $e |- A e. _V $.
    dfon2lem4.2 $e |- B e. _V $.
    $( Lemma for ~ dfon2 .  If two sets satisfy the new definition, then one is
       a subset of the other.  (Contributed by Scott Fenton, 25-Feb-2011.) $)
    dfon2lem4 $p |- ( ( A. x ( ( x C. A /\ Tr x ) -> x e. A ) /\
                         A. y ( ( y C. B /\ Tr y ) -> y e. B ) ) ->
                         ( A C_ B \/ B C_ A ) ) $=
      ( vz cv wpss wtr wa wcel wi wal wceq wo wss wn cvv eleq1 inss1 sseli wral
      cin wel dfon2lem3 ax-mp simprd eleq2 bitrd notbid rspccv syl syl5 pm2.01d
      adantr elin sylnib simpld trin syl2an inex1 psseq1 anbi12d imbi12d mpan2d
      treq spcv adantl anim12d mtod ianor sylib sspss mpbi inss2 orel1 orc syl6
      olc jaoa mp2ani dfss2 sseqin2 orbi12i sylibr ) AHZCIZWGJZKZWGCLZMZANZBHZD
      IZWNJZKZWNDLZMZBNZKZCDUDZCOZXBDOZPZCDQZDCQZPXAXBCIZRZXBDIZRZPZXEXAXHXJKZR
      XLXAXMXBCLZXBDLZKZXAXBXBLZXPXAXQXQXNXAXQRZXBCXBCDUAZUBWMXNXRMZWTWMGGUEZRZ
      GCUCZXTWMCJZYCCSLWMYDYCKMEAGCSUFUGZUHYBXRGXBCGHZXBOZYAXQYGYAXBYFLXQYFXBYF
      TYFXBXBUIUJUKULUMUPUNUOXBCDUQURXAXHXNXJXOXAXHXBJZXNWMYDDJZYHWTWMYDYCYEUSW
      TYIYBGDUCZDSLWTYIYJKMFBGDSUFUGUSCDUTVAZWMXHYHKZXNMZWTWLYMAXBCDEVBZWGXBOZW
      JYLWKXNYOWHXHWIYHWGXBCVCWGXBVGVDWGXBCTVEVHUPVFXAXJYHXOYKWTXJYHKZXOMZWMWSY
      QBXBYNWNXBOZWQYPWRXOYRWOXJWPYHWNXBDVCWNXBVGVDWNXBDTVEVHVIVFVJVKXHXJVLVMXL
      XHXCPZXJXDPZXEXBCQYSXSXBCVNVOXBDQYTCDVPXBDVNVOXIYSXEXKYTXIYSXCXEXHXCVQXCX
      DVRVSXKYTXDXEXJXDVQXDXCVTVSWAWBUMXFXCXGXDCDWCDCWDWEWF $.
  $}

  ${
    $d A x y z $.  $d B x y z $.
    dfon2lem5.1 $e |- A e. _V $.
    dfon2lem5.2 $e |- B e. _V $.
    $( Lemma for ~ dfon2 .  Two sets satisfying the new definition also satisfy
       trichotomy with respect to ` e. ` .  (Contributed by Scott Fenton,
       25-Feb-2011.) $)
    dfon2lem5 $p |- ( ( A. x ( ( x C. A /\ Tr x ) -> x e. A ) /\
                         A. y ( ( y C. B /\ Tr y ) -> y e. B ) ) ->
                       ( A e. B \/ A = B \/ B e. A ) ) $=
      ( vz cv wpss wtr wa wcel wi wal wceq wn wo w3o bitri cvv dfon2lem4 dfpss2
      wss eqcom notbii anbi2i orbi12i andir bitr4i orcom dfon2lem3 ax-mp simpld
      wel wral psseq1 treq anbi12d eleq1 imbi12d spcv expcomd imp mpan9 orim12d
      sylan2 biimtrid biimtrrid mpand 3orrot 3orass df-or sylibr ) AHZCIZVNJZKZ
      VNCLZMZANZBHZDIZWAJZKZWADLZMZBNZKZCDOZPZDCLZCDLZQZMZWLWIWKRZWHCDUCZDCUCZQ
      ZWJWMABCDEFUAWRWJKZCDIZDCIZQZWHWMXBWPWJKZWQWJKZQWSWTXCXAXDCDUBXAWQDCOZPZK
      XDDCUBXFWJWQXEWIDCUDUEUFSUGWPWQWJUHUIXBXAWTQWHWMWTXAUJWHXAWKWTWLWGVTDJZXA
      WKMZWGXGGGUNPZGDUOZDTLWGXGXJKMFBGDTUKULUMVTXGXHVTXAXGWKVSXAXGKZWKMADFVNDO
      ZVQXKVRWKXLVOXAVPXGVNDCUPVNDUQURVNDCUSUTVAVBVCVFVTCJZWGWTWLMVTXMXIGCUOZCT
      LVTXMXNKMEAGCTUKULUMWGWTXMWLWFWTXMKZWLMBCEWACOZWDXOWEWLXPWBWTWCXMWACDUPWA
      CUQURWACDUSUTVAVBVDVEVGVHVIWOWIWKWLRZWNWLWIWKVJXQWIWMQWNWIWKWLVKWIWMVLSSV
      M $.
  $}

  ${
    $d S x y z w s t $.
    $( Lemma for ~ dfon2 .  A transitive class of sets satisfying the new
       definition satisfies the new definition.  (Contributed by Scott Fenton,
       25-Feb-2011.) $)
    dfon2lem6 $p |- ( ( Tr S /\
                         A. x e. S A. z ( ( z C. x /\ Tr z ) -> z e. x ) ) ->
                       A. y ( ( y C. S /\ Tr y ) -> y e. S ) ) $=
      ( vs vw vt wtr cv wpss wa wel wi wal wral wcel weq wn syl imbi12d wo cdif
      wss pssss ssralv impcom adantrr ad2ant2lr psseq2 anbi1d elequ2 albidv imp
      rspccv eldifi psseq1 treq anbi12d elequ1 cbvalvw imbitrdi ad2ant2l adantr
      rspcv w3o dfon2lem5 3orrot 3orass bitri eleq1a elndif nsyli adantll orel1
      vex trss eldifn ssel con3d syl5com adantl imp31 syl9r mpd biimtrid mp2and
      syl9 syl5 ssrdv dfpss2 spvv expd com23 syl6 com3l adantld imp32 biimtrrid
      ex mpand orrd anassrs ralrimiva wrex c0 wne pssdif r19.2z ad2antrl eleq1w
      imbitrrid a1i trel syl7 ad2antrr jaod rexlimdv syld alrimiv ) DHZCIZAIZJZ
      YAHZKZCALZMZCNZADOZKZBIZDJZYKHZKZYKDPZMBYJYNYOYJYNKZBEQZBELZUAZEDYKUBZOZY
      OYPYSEYTYJYNEIZYTPZYSYJYNUUCKZKZYQYRUUEYKUUBUCZYQRZYRUUEFYKUUBUUEFBLZFELZ
      UUEUUHKZYAFIZJZYDKZCFLZMZCNZGIZUUBJZUUQHZKZGELZMZGNZUUIUUEUUHUUPUUEYHAYKO
      ZUUHUUPMYIYNUVDXTUUCYIYLUVDYMYLYIUVDYLYKDUCYIUVDMYKDUDYHAYKDUESUFUGUHYHUU
      PAUUKYKAFQZYGUUOCUVEYEUUMYFUUNUVEYCUULYDYBUUKYAUIUJAFCUKTULUNSUMUUEUVCUUH
      YIUUCUVCXTYNUUCYIUVCUUCYIYAUUBJZYDKZCELZMZCNZUVCUUCUUBDPZYIUVJMUUBDYKUOZY
      HUVJAUUBDAEQZYGUVICUVMYEUVGYFUVHUVMYCUVFYDYBUUBYAUIUJAECUKTULVDSZUVIUVBCG
      CGQZUVGUUTUVHUVAUVOUVFUURYDUUSYAUUQUUBUPYAUUQUQURCGEUSTUTVAUFVBVCUUPUVCKU
      UIFEQZEFLZVEZUUJUUICGUUKUUBFVOEVOVFUVRUVPUVQUUIUAZUAZUUJUUIUVRUVPUVQUUIVE
      UVTUUIUVPUVQVGUVPUVQUUIVHVIUUJUVPRZUVTUUIMUUDUUHUWAYJUUCUUHUWAYNUUCUUHUWA
      UUCUVPUUKYTPUUHUUBYTUUKVJUUKYKDVKVLUMVMVMUWAUVTUVSUUJUUIUVPUVSVNUUJUVQRZU
      VSUUIMUUDUUHUWBYJYNUUCUUHUWBYMUUCUUHUWBMMYLYMUUHUUKYKUCZUUCUWBYKUUKVPUUCE
      BLZRUWCUWBUUBDYKVQUWCUVQUWDUUKYKUUBVRVSVTWGWAWBVMUVQUUIVNSWCWDWEWHWFWSWIU
      UFUUGKYKUUBJZUUEYRYKUUBWJYJYNUUCUWEYRMZYIYNUUCUWFMZMXTYIYMUWGYLUUCYIYMUWF
      UUCYIUVJYMUWFMUVNUVJUWEYMYRUVJUWEYMYRUVIUWEYMKZYRMCBCBQZUVGUWHUVHYRUWIUVF
      UWEYDYMYAYKUUBUPYAYKUQURCBEUSTWKWLWMWNWOWPWAWQWRWTXAXBXCYPUUAYSEYTXDZYOYL
      UUAUWJMZYJYMYLYTXEXFZUWKYKDXGUWLUUAUWJYSEYTXHWSSXIYPYSYOEYTYPYSUUCYOYPYQU
      UCYOMZYRYQUWMMYPUUCYOYQUVKUVLBEDXJXKXLXTYRUWMMYIYNUUCUVKXTYRYOUVLXTYRUVKY
      ODYKUUBXMWLXNXOXPWMXQXRWDWSXS $.
  $}

  ${
    $d A x y z w s t u $.  $d B x y z w t $.
    dfon2lem7.1 $e |- A e. _V $.
    $( Lemma for ~ dfon2 .  All elements of a new ordinal are new ordinals.
       (Contributed by Scott Fenton, 25-Feb-2011.) $)
    dfon2lem7 $p |- ( A. x ( ( x C. A /\ Tr x ) -> x e. A ) ->
                       ( B e. A -> A. y ( ( y C. B /\ Tr y ) -> y e. B ) ) ) $=
      ( vw vt vz vu wpss wtr wa wcel wi wal wss wel wral sylbi imbi12d w3a cuni
      vs cv cab wceq csuc csn wn weq elequ1 elequ2 bitrd notbid cbvralvw biimpi
      ralimi untuni sylibr vex sseq1 treq raleq 3anbi123d elab dfon2lem3 simprd
      cvv ax-mp untelirr syl 3ad2ant3 psseq2 anbi1d albidv 3anbi3i abbii unieqi
      mprg eleq2i sylnib dfon2lem2 ssexi snss mtbi intnan cun df-suc unss mtbir
      sseq1i bitr4i dfon2lem1 suctr wo elsuc wrex eluni2 rspccv anbi12d cbvalvw
      nfa1 psseq1 imbitrdi rexlimi rgen dfon2lem6 mp2an eleq2 mpbiri jaoi sucex
      rexlimiv elssuni sylbir ralbii bitrdi cbvabv sseqtrdi a1i biimtrrid mpani
      mp3an23 biimtrid mtoi eleq1 spcv mpan2i mtod biimpri mpan nsyl2 rsp mpbii
      dfpss2 3syl ) AUDZCJZYQKZLZYQCMZNZAOZFUDZCPZUUDKZBUDZGUDZJZUUGKZLZBGQZNZB
      OZGUUDRZUAZFUEZUBZCUFZUUGHUDZJZUUJLZBHQZNZBOZHCRZDCMUUGDJZUUJLZUUGDMZNZBO
      ZNUUCUURCJZUUSUUCUVLUURCMZUUCUVMUURUGZUUEUUFUUGIUDZJZUUJLZBIQZNZBOZIUUDRZ
      UAZFUEZUBZPZUWEUURUWDPZUURUHZUWDPZLZUWHUWFUURUWDMZUWHHHQZUIZHUURRZUWJUIGG
      QZUIZGYQRZUWMAUUQUWPAUUQRUWLHYQRZAUUQRUWMUWPUWQAUUQUWPUWQUWOUWLGHYQGHUJZU
      WNUWKUWRUWNHGQUWKGHGUKGHHULUMUNUOUPUQHAUUQURUSYQUUQMZYQCPZYSUUNGYQRZUAZUW
      PUUPUXBFYQAUTZFAUJZUUEUWTUUFYSUUOUXAUUDYQCVAZUUDYQVBZUUNGUUDYQVCZVDVEZUXA
      UWTUWPYSUUNUWOGYQUUNIIQUIIUUHRZUWOUUNUUHKZUXIUUHVHMUUNUXJUXILNGUTBIUUHVHV
      FVIVGIUUHVJVKUQVLSVSUWMUURUURMUWJHUURVJUURUWDUURUUQUWCUUPUWBFUUOUWAUUEUUF
      UUNUVTGIUUDGIUJZUUMUVSBUXKUUKUVQUULUVRUXKUUIUVPUUJUUHUVOUUGVMVNGIBULTVOZU
      OVPVQVRVTWAVIUURUWDUURCEUUFUUOFCWBZWCZWDWEWFUWEUURUWGWGZUWDPUWIUVNUXOUWDU
      URWHZWKUURUWGUWDWIWLWJUVMUWGCPZUUCUWEUURCUXNWDUUCUURCPZUXQUWEUXMUXRUXQLZU
      VNCPZUUCUWEUXTUXOCPUXSUVNUXOCUXPWKUURUWGCWIWLUXTUWENUUCUXTUVNUCUDZCPZUYAK
      ZYQUVOJZYSLZAIQZNZAOZIUYARZUAZUCUEZUBZUWDUXTUVNKZUYHIUVNRZUVNUYLPZUURKZUY
      MUUEUUOFWMZUURWNVIUYHIUVNUVOUVNMUVOUURMZUVOUURUFZWOUYHUVOUURIUTWPUYRUYHUY
      SUYRIAQZAUUQWQZUYHAUVOUUQWRZUYTUYHAUUQUYGAXBUWSUXBUYTUYHNZUXHUXAUWTVUCYSU
      XAUYTUVTUYHUUNUVTGUVOYQUXLWSZUVSUYGBABAUJZUVQUYEUVRUYFVUEUVPUYDUUJYSUUGYQ
      UVOXCUUGYQVBWTBAIUKTXAXDVLSXESUYSUYHYQUURJZYSLZYQUURMZNZAOZUYPUUTUVOJZUUT
      KZLZHIQZNZHOZIUURRVUJUYQVUPIUURUYRVUAVUPVUBUYTVUPAUUQUWSUXBUYTVUPNZUXHUXA
      UWTVUQYSUXAUYTUVTVUPVUDUVSVUOBHBHUJZUVQVUMUVRVUNVURUVPVUKUUJVULUUGUUTUVOX
      CUUGUUTVBWTBHIUKTXAXDVLSXMSXFIAHUURXGXHUYSUYGVUIAUYSUYEVUGUYFVUHUYSUYDVUF
      YSUVOUURYQVMVNUVOUURYQXITVOXJXKSXFUXTUYMUYNUAZUVNUYKMUYOUYJVUSUCUVNUURUXN
      XLUYAUVNUFUYBUXTUYCUYMUYIUYNUYAUVNCVAUYAUVNVBUYHIUYAUVNVCVDVEUVNUYKXNXOYC
      UYKUWCUYJUWBUCFUCFUJZUYBUUEUYCUUFUYIUWAUYAUUDCVAUYAUUDVBVUTUYIUYHIUUDRUWA
      UYHIUYAUUDVCUYHUVTIUUDUYGUVSABABUJZUYEUVQUYFUVRVVAUYDUVPYSUUJYQUUGUVOXCYQ
      UUGVBWTABIUKTXAXPXQVDXRVRXSXTYAYBYDYEUUCUVLUYPUVMUYQUUBUVLUYPLZUVMNAUURUX
      NYQUURUFZYTVVBUUAUVMVVCYRUVLYSUYPYQUURCXCYQUURVBWTYQUURCYFTYGYHYIUXRUUSUI
      ZUVLUXMUVLUXRVVDLUURCYOYJYKYLUUSUVEHUURRUVFUVEHUURUUTUURMHAQZAUUQWQUVEAUU
      TUUQWRVVEUVEAUUQUWSUWTYSUVEHYQRZUAZVVEUVENZUUPVVGFYQUXCUXDUUEUWTUUFYSUUOV
      VFUXEUXFUXDUUOUXAVVFUXGUUNUVEGHYQUWRUUMUVDBUWRUUKUVBUULUVCUWRUUIUVAUUJUUH
      UUTUUGVMVNGHBULTVOUOXQVDVEVVFUWTVVHYSUVEHYQYMVLSXMSXFUVEHUURCVCYNUVEUVKHD
      CUUTDUFZUVDUVJBVVIUVBUVHUVCUVIVVIUVAUVGUUJUUTDUUGVMVNUUTDUUGXITVOWSYP $.
  $}

  ${
    $d A x y z w t $.
    $( Lemma for ~ dfon2 .  The intersection of a nonempty class ` A ` of new
       ordinals is itself a new ordinal and is contained within ` A `
       (Contributed by Scott Fenton, 26-Feb-2011.) $)
    dfon2lem8 $p |- ( ( A =/= (/) /\
                         A. x e. A A. y ( ( y C. x /\ Tr y ) -> y e. x ) ) ->
                       ( A. z ( ( z C. |^| A /\ Tr z ) -> z e. |^| A ) /\
                         |^| A e. A ) ) $=
      ( vt vw cv wpss wtr wa wel wi wal wral wcel wn cvv syl sylbi wceq c0 cint
      wne vex dfon2lem3 ax-mp simpld ralimi trint adantl cuni dfon2lem7 alrimiv
      df-ral 19.21v albii bitr4i impexp 2albii eluni2 biimpi imim1i alimi alcom
      wrex wex 19.23v df-rex imbi1i bitri 3imtr4i sylbir intssuni ssralv adantr
      wss mpd dfon2lem6 imp simprd untelirr adantlr risset notbii ralnex psseq2
      intex eqcom anbi1d elequ2 imbi12d albidv rspccv intss1 dfpss2 psseq1 treq
      anbi12d eleq1 spcgv expd biimtrrid exp4b com45 com23 syl5 syl7bi ralrimiv
      mpdd mpid ralim biimtrid wb elintg ad2antrr sylibrd mt3d ex ancld mp2and
      ) DUAUCZBGZAGZHZYBIZJZBAKZLZBMZADNZJZDUBZIZEGZFGZHYNIJEFKLEMZFYLNZCGZYLHY
      RIJYRYLOLCMZYLDOZJZYJYMYAYJYCIZADNYMYIUUBADYIUUBCCKPCYCNZYCQOYIUUBUUCJLAU
      DZBCYCQUEUFUGUHADUIRUJYKYPFDUKZNZYQYJUUFYAYJFAKZYPLZFMZADNZUUFYIUUIADYIUU
      HFBEYCYOUUDULUMUHUUJYCDOZUUHLZFMZAMZUUFUUJUUKUUILZAMUUNUUIADUNUUMUUOAUUKU
      UHFUOUPUQUUNUUKUUGJZYPLZFMAMZUUFUUQUULAFUUKUUGYPURUSUUGADVEZYPLZFMZYOUUEO
      ZYPLZFMUURUUFUUTUVCFUVBUUSYPUVBUUSAYODUTVAVBVCUURUUQAMZFMUVAUUQAFVDUVDUUT
      FUVDUUPAVFZYPLUUTUUPYPAVGUUSUVEYPUUGADVHVIUQUPVJYPFUUEUNVKVLSRUJYAUUFYQLZ
      YJYAYLUUEVPUVFDVMYPFYLUUEVNRVOVQYMYQJYSYKUUAFCEYLVRYKYSYTYKYSYTYKYSJZYTYL
      YLOZYAYSUVHPZYJYAYSJZEEKPEYLNZUVIUVJYMUVKYAYSYMUVKJZYAYLQOZYSUVLLDWGZCEYL
      QUESVSZVTEYLWARWBUVGYTPZYLYNOZEDNZUVHUVPYNYLTZPZEDNZUVGUVRUVPUVSEDVEZPUWA
      YTUWBEYLDWCWDUVSEDWEUQUVGUVTUVQLZEDNUWAUVRLUVGUWCEDUVTYLYNTZPZUVGYNDOZUVQ
      UVSUWDYNYLWHWDUVGUWFYMUWEUVQLZYAYSYMYJUVJYMUVKUVOUGWBYKUWFYMUWGLZLYSYKUWF
      YBYNHZYEJZBEKZLZBMZUWHYJUWFUWMLYAYIUWMAYNDYCYNTZYHUWLBUWNYFUWJYGUWKUWNYDU
      WIYEYCYNYBWFWIAEBWJWKWLWMUJYAUWFUWMUWHLZLYJUWFYLYNVPZYAUWOYNDWNYAUWMUWPUW
      HYAUWMUWPUWEYMUVQYAUWMUWPUWEYMUVQLZUWPUWEJYLYNHZYAUWMJZUWQYLYNWOUWSUWRYMU
      VQYAUWMUWRYMJZUVQLZYAUVMUWMUXALUVNUWLUXABYLQYBYLTZUWJUWTUWKUVQUXBUWIUWRYE
      YMYBYLYNWPYBYLWQWRYBYLYNWSWKWTSVSXAXBXCXDXEXFVOXIVOXJXGXHUVTUVQEDXKRXLYAU
      VHUVRXMZYJYSYAUVMUXCUVNEYLDQXNSXOXPXQXRXSXFXT $.
  $}

  ${
    $d A x y z w t u $.
    $( Lemma for ~ dfon2 .  A class of new ordinals is well-founded by ` _E ` .
       (Contributed by Scott Fenton, 3-Mar-2011.) $)
    dfon2lem9 $p |- ( A. x e. A A. y ( ( y C. x /\ Tr y ) -> y e. x )
                         -> _E Fr A ) $=
      ( vz vt vw vu cv wpss wtr wa wel wi wal wral wss wn wrex cep wcel wne wfr
      c0 ssralv cint dfon2lem8 simprd intss1 simpld cvv wceq dfon2lem3 untelirr
      intex imp syl eleq1 notbid syl5ibcom a1dd trss eqss simplbi2com syl6 con3
      com23 pm2.61d sylanb syldan ralrimiv eleq2 ralbidv rspcev syl2anc syl6com
      syl5 expcom impd alrimiv wbr df-fr epel notbii ralbii rexbii imbi2i albii
      bitri sylibr ) BHZAHIWJJKBALMBNZACOZDHZCPZWMUCUAZKZEFLZQZEWMOZFWMRZMZDNZC
      SUBZWLXADWLWNWOWTWNWLWKAWMOZWOWTMWKAWMCUDWOXDWTWOXDKZWMUEZWMTZEHZXFTZQZEW
      MOZWTXEGHZXFIXLJKXLXFTMGNZXGABGWMUFZUGXEXJEWMEDLXFXHPZXEXJXHWMUHWOXDXMXOX
      JMZXEXMXGXNUIWOXFUJTZXMXPWMUNXQXMKZXFXHUKZXPXRXSXJXOXRXFXFTZQZXSXJXRAALQA
      XFOZYAXRXFJZYBXQXMYCYBKGAXFUJULUOZUGAXFUMUPXSXTXIXFXHXFUQURUSUTXRXOXSQZXJ
      XRXOXIXSMYEXJMXRXIXOXSXRXIXHXFPZXOXSMXRYCXIYFMXRYCYBYDUIXFXHVAUPXSXOYFXFX
      HVBVCVDVFXIXSVEVDVFVGVHVIVPVJWSXKFXFWMFHZXFUKZWRXJEWMYHWQXIYGXFXHVKURVLVM
      VNVQVOVRVSXCWPXHYGSVTZQZEWMOZFWMRZMZDNXBDFECSWAYMXADYLWTWPYKWSFWMYJWREWMY
      IWQFXHWBWCWDWEWFWGWHWI $.
  $}

  ${
    $d x y z w t u v $.
    $( ` On ` consists of all sets that contain all its transitive proper
       subsets.  This definition comes from J. R. Isbell, "A Definition of
       Ordinal Numbers", American Mathematical Monthly, vol 67 (1960), pp.
       51-52.  (Contributed by Scott Fenton, 20-Feb-2011.) $)
    dfon2 $p |- On = { x | A. y ( ( y C. x /\ Tr y ) -> y e. x ) } $=
      ( vz vw vu vt vv cv cab wpss wtr wa wel wi wal cep wral vex weq imbi12d
      con0 word df-on wss wne tz7.7 df-pss bitr4di exbiri com23 impd alrimiv wn
      wwe cvv wcel dfon2lem3 simpld wfr w3o dfon2lem7 ralrimiv dfon2lem9 psseq2
      ax-mp anbi1d elequ2 albidv psseq1 anbi12d elequ1 cbvalvw bitrdi dfon2lem5
      treq anim12d syl6 ralrimivv jca syl wbr dfwe2 epel biid 3orbi123i 2ralbii
      rspccv anbi2i bitri sylibr df-ord sylanbrc impbii abbii eqtri ) UAAHZUBZA
      IBHZWPJZWRKZLBAMZNZBOZAIAUCWQXCAWQXCWQXBBWQWSWTXAWQWTWSXAWQWTXAWSWQWTLXAW
      RWPUDWRWPUELWSWPWRUFWRWPUGUHUIUJUKULXCWPKZWPPUNZWQXCXDCCMUMCWPQZWPUOUPXCX
      DXFLNARZBCWPUOUQVEURXCWPPUSZCDMZCDSZDCMZUTZDWPQCWPQZLZXEXCEHZFHZJZXOKZLZE
      FMZNZEOZFWPQZXNXCYBFWPBEWPXPXGVAVBYCXHXMFEWPVCYCXLCDWPWPYCCAMZDAMZLGHZCHZ
      JZYFKZLZGCMZNZGOZWRDHZJZWTLZBDMZNZBOZLXLYCYDYMYEYSYBYMFYGWPFCSZYBXOYGJZXR
      LZECMZNZEOYMYTYAUUDEYTXSUUBXTUUCYTXQUUAXRXPYGXOVDVFFCEVGTVHUUDYLEGEGSZUUB
      YJUUCYKUUEUUAYHXRYIXOYFYGVIXOYFVOVJEGCVKTVLVMWGYBYSFYNWPFDSZYBXOYNJZXRLZE
      DMZNZEOYSUUFYAUUJEUUFXSUUHXTUUIUUFXQUUGXRXPYNXOVDVFFDEVGTVHUUJYREBEBSZUUH
      YPUUIYQUUKUUGYOXRWTXOWRYNVIXOWRVOVJEBDVKTVLVMWGVPGBYGYNCRDRVNVQVRVSVTXEXH
      YGYNPWAZXJYNYGPWAZUTZDWPQCWPQZLXNCDWPPWBUUOXMXHUUNXLCDWPWPUULXIXJXJUUMXKD
      YGWCXJWDCYNWCWEWFWHWIWJWPWKWLWMWNWO $.
  $}

  ${
    $d F g $.  $d I g $.
    $( The value of the recursive definition generator at ` (/) ` when the base
       value is a proper class.  (Contributed by Scott Fenton, 26-Mar-2014.)
       (Revised by Mario Carneiro, 19-Apr-2014.) $)
    rdgprc0 $p |- ( -. I e. _V -> ( rec ( F , I ) ` (/) ) = (/) ) $=
      ( vg cvv wcel wn c0 crdg cfv cv wceq cdm wlim crn cuni cif cmpt cres eqid
      unieqd con0 0elon rdgval ax-mp res0 fveq2i eqtri eqeq1 wb dmeq limeq rneq
      syl fveq12d fveq2d ifbieq12d ifbieq2d eleq1d elrab2 iftruei eleq1i biimpi
      id dmmpt simplbiim ndmfv nsyl5 eqtrid ) BDEZFGABHZIZGCDCJZGKZBVLLZMZVLNZO
      ZVNOZVLIZAIZPZPZQZIZGVKVJGRZWCIZWDGUAEVKWFKUBBGCAUCUDWEGWCVJUEUFUGGWCLZEZ
      VIWDGKWHGDEGGKZBGLZMZGNZOZWJOZGIZAIZPZPZDEZVIWBDEWSCGDWGVMWBWRDVMVMWIWAWQ
      BVLGGUHVMVOWKVQVTWMWPVMVNWJKVOWKUIVLGUJZVNWJUKUMVMVPWLVLGULTVMVSWOAVMVRWN
      VLGVMVCVMVNWJWTTUNUOUPUQURCDWBWCWCSVDUSWSVIWRBDWIBWQGSUTVAVBVEGWCVFVGVH
      $.
  $}

  ${
    $d F x y z $.  $d I x y z $.
    $( The value of the recursive definition generator when ` I ` is a proper
       class.  (Contributed by Scott Fenton, 26-Mar-2014.)  (Revised by Mario
       Carneiro, 19-Apr-2014.) $)
    rdgprc $p |- ( -. I e. _V -> rec ( F , I ) = rec ( F , (/) ) ) $=
      ( vx vz vy cvv wcel cv crdg cfv c0 wceq con0 wral wi fveq2 eqeq12d imbi2d
      weq wb csuc rdgprc0 0ex rdg0 eqtr4di rdgsuc imbitrrid imim2d wlim r19.21v
      wn cres word wss limord ordsson wfn rdgfnon fvreseq mpanl12 3syl cima crn
      cuni rneq df-ima 3eqtr4g unieqd vex wa rdglim mpan sylbird biimtrid com12
      tfinds ralrimiv eqfnfv mp2an sylibr ) BFGUKZCHZABIZJZWBAKIZJZLZCMNZWCWELZ
      WAWGCMWBMGWAWGWADHZWCJZWJWEJZLZOZWAKWCJZKWEJZLZOWAEHZWCJZWRWEJZLZOZWAWRUA
      ZWCJZXCWEJZLZOWAWGODEWBWJKLZWMWQWAXGWKWOWLWPWJKWCPWJKWEPQRDESZWMXAWAXHWKW
      SWLWTWJWRWCPWJWRWEPQRWJXCLZWMXFWAXIWKXDWLXEWJXCWCPWJXCWEPQRDCSZWMWGWAXJWK
      WDWLWFWJWBWCPWJWBWEPQRWAWOKWPABUBKAUCUDUEWRMGZXAXFWAXAXFXKWSAJZWTAJZLWSWT
      APXKXDXLXEXMBWRAUFKWRAUFQUGUHXBEWJNWAXAEWJNZOWJUIZWNWAXAEWJUJXOXNWMWAXOXN
      WCWJULZWEWJULZLZWMXOWJUMWJMUNZXRXNTZWJUOWJUPWCMUQZWEMUQZXSXTBAURZKAURZEMW
      JWCWEUSUTVAXRWMXOWCWJVBZVDZWEWJVBZVDZLZXRYEYGXRXPVCXQVCYEYGXPXQVEWCWJVFWE
      WJVFVGVHWJFGZXOWMYITDVIYJXOVJWKYFWLYHBWJFAVKKWJFAVKQVLUGVMUHVNVPVOVQYAYBW
      IWHTYCYDCMWCWEVRVSVT $.
  $}

  ${
    $d F f $.  $d f g $.  $d F g $.  $d f i $.  $d F i $.  $d f x $.  $d F x $.
    $d f y $.  $d F y $.  $d g i $.  $d g x $.  $d g y $.  $d I f $.  $d I i $.
    $d i x $.  $d I x $.  $d i y $.  $d I y $.  $d x y $.  $d f z $.  $d F z $.
    $d i z $.  $d y z $.
    $( Alternate definition of the recursive function generator when ` I ` is a
       set.  (Contributed by Scott Fenton, 26-Mar-2014.)  (Revised by Mario
       Carneiro, 19-Apr-2014.) $)
    dfrdg2 $p |- ( I e. V -> rec ( F , I ) =
       U. { f | E. x e. On ( f Fn x /\
            A. y e. x ( f ` y ) =
              if ( y = (/) , I ,
                   if ( Lim y , U. ( f " y ) ,
                        ( F ` ( f ` U. y ) ) ) ) ) } ) $=
      ( vg vz cv cfv c0 wceq cuni cif wa con0 cvv wcel fveq2d ifbieq2d crdg wfn
      wlim cima wral wrex cab rdgeq2 ifeq1 eqeq2d ralbidv anbi2d rexbidv abbidv
      vi unieqd eqeq12d cdm crn cmpt crecs cres df-rdg dfrecs3 wb w3a vex resex
      eqeq1 wrel relres reldm0 ax-mp bitrdi dmeq limeq syl rneq eqtr4di fveq12d
      df-ima id ifbieq12d eqid imaexg uniex fvex fvmpt cin dmres wss onelss imp
      ifex 3adant2 fndm 3ad2ant2 sseqtrrd dfss2 sylib eqtrid unieq onelon eloni
      word csuc ordzsl iftrue eqtr4d sucid fvres ordunisuc 3eqtr4a nsuceq0 neii
      w3o iffalsei wn nlimsucg iffalse eqtri 3eqtr4g reseq2 syl5ibrcom rexlimiv
      mp2b wne df-lim simp2bi neneqd iffalsed 3jaoi sylbi sylan9eqr mpdan 3expa
      3eqtr4d ralbidva pm5.32da rexbiia abbii unieqi 3eqtri vtoclg ) DUOIZUAZCI
      ZAIZUBZBIZUUGJZUUJKLZUUEUUJUCZUUGUUJUDZMZUUJMZUUGJZDJZNZNZLZBUUHUEZOZAPUF
      ZCUGZMZLDEUAZUUIUUKUULEUUSNZLZBUUHUEZOZAPUFZCUGZMZLUOEFUUEELZUUFUVGUVFUVN
      UUEEDUHUVOUVEUVMUVOUVDUVLCUVOUVCUVKAPUVOUVBUVJUUIUVOUVAUVIBUUHUVOUUTUVHUU
      KUULUUEEUUSUIUJUKULUMUNUPUQUUFGQGIZKLZUUEUVPURZUCZUVPUSZMZUVRMZUVPJZDJZNZ
      NZUTZVAUUIUUKUUGUUJVBZUWGJZLZBUUHUEZOZAPUFZCUGZMUVFGDUUEVCABCUWGVDUWNUVEU
      WMUVDCUWLUVCAPUUHPRZUUIUWKUVBUWOUUIOUWJUVABUUHUWOUUIUUJUUHRZUWJUVAVEUWOUU
      IUWPVFZUWIUUTUUKUWQUWIUWHURZKLZUUEUWRUCZUUOUWRMZUWHJZDJZNZNZUUTUWHQRUWIUX
      ELUUGUUJCVGZVHGUWHUWFUXEQUWGUVPUWHLZUVQUWSUWEUXDUUEUXGUVQUWHKLZUWSUVPUWHK
      VIUWHVJUXHUWSVEUUGUUJVKUWHVLVMVNUXGUVSUWTUWAUWDUUOUXCUXGUVRUWRLUVSUWTVEUV
      PUWHVOZUVRUWRVPVQUXGUVTUUNUXGUVTUWHUSUUNUVPUWHVRUUGUUJWAVSUPUXGUWCUXBDUXG
      UWBUXAUVPUWHUXGWBUXGUVRUWRUXIUPVTSWCTUWGWDUWSUUEUXDUOVGUWTUUOUXCUUNUUGQRU
      UNQRUXFUUGUUJQWEVMWFUXBDWGWNWNWHVMUWQUWRUUJLZUXEUUTLUWQUWRUUJUUGURZWIZUUJ
      UUGUUJWJUWQUUJUXKWKUXLUUJLUWQUUJUUHUXKUWOUWPUUJUUHWKZUUIUWOUWPUXMUUHUUJWL
      WMWOUUIUWOUXKUUHLUWPUUHUUGWPWQWRUUJUXKWSWTXAUXJUWQUXEUULUUEUUMUUOUUPUWHJZ
      DJZNZNZUUTUXJUWSUULUXDUXPUUEUWRUUJKVIUXJUWTUUMUXCUXOUUOUWRUUJVPUXJUXBUXND
      UXJUXAUUPUWHUWRUUJXBSSTTUWQUUJXEZUXQUUTLZUWOUWPUXRUUIUWOUWPOUUJPRUXRUUHUU
      JXCUUJXDVQWOUXRUULUUJHIZXFZLZHPUFZUUMXPUXSHUUJXGUULUXSUYCUUMUULUXQUUEUUTU
      ULUUEUXPXHUULUUEUUSXHXIUYBUXSHPUXTPRZUXSUYBUYAKLZUUEUYAUCZUUOUYAMZUUGUYAV
      BZJZDJZNZNZUYEUUEUYFUUOUYGUUGJZDJZNZNZLUYDUYJUYNUYLUYPUYDUYIUYMDUYDUXTUYH
      JZUXTUUGJZUYIUYMUXTUYARUYQUYRLUXTHVGZXJUXTUYAUUGXKVMUYDUYGUXTUYHUYDUXTXEU
      YGUXTLUXTXDUXTXLVQZSUYDUYGUXTUUGUYTSXMSUYLUYKUYJUYEUUEUYKUYAKUXTXNXOZXQUX
      TQRZUYFXRZUYKUYJLUYSUXTQXSZUYFUUOUYJXTYFYAUYPUYOUYNUYEUUEUYOVUAXQVUBVUCUY
      OUYNLUYSVUDUYFUUOUYNXTYFYAYBUYBUXQUYLUUTUYPUYBUULUYEUXPUYKUUEUUJUYAKVIZUY
      BUUMUYFUXOUYJUUOUUJUYAVPZUYBUXNUYIDUYBUUPUYGUWHUYHUUJUYAUUGYCUUJUYAXBZVTS
      TTUYBUULUYEUUSUYOUUEVUEUYBUUMUYFUURUYNUUOVUFUYBUUQUYMDUYBUUPUYGUUGVUGSSTT
      UQYDYEUUMUXQUUSUUTUUMUXPUUOUXQUUSUUMUUOUXOXHUUMUULUUEUXPUUMUUJKUUMUXRUUJK
      YGUUJUUPLUUJYHYIYJZYKUUMUUOUURXHYQUUMUULUUEUUSVUHYKXIYLYMVQYNYOXAUJYPYRYS
      YTUUAUUBUUCUUD $.
  $}

  ${
    $d F f $.  $d f x $.  $d F x $.  $d f y $.  $d F y $.  $d I f $.  $d I x $.
    $d I y $.  $d x y $.
    $( Generalization of ~ dfrdg2 to remove sethood requirement.  (Contributed
       by Scott Fenton, 27-Mar-2014.)  (Revised by Mario Carneiro,
       19-Apr-2014.) $)
    dfrdg3 $p |- rec ( F , I ) =
       U. { f | E. x e. On ( f Fn x /\
            A. y e. x ( f ` y ) =
              if ( y = (/) , if ( I e. _V , I , (/) ) ,
                   if ( Lim y , U. ( f " y ) ,
                        ( F ` ( f ` U. y ) ) ) ) ) } $=
      ( cvv wcel crdg cv cfv c0 wceq cif cuni wral wa con0 wrex cab dfrdg2 wlim
      wfn cima iftrue ifeq1d eqeq2d ralbidv anbi2d rexbidv abbidv unieqd eqtr4d
      wn 0ex ax-mp rdgprc iffalse 3eqtr4a pm2.61i ) EFGZDEHZCIZAIZUBZBIZVBJZVEK
      LZUTEKMZVEUAVBVEUCNVENVBJDJMZMZLZBVCOZPZAQRZCSZNZLUTVAVDVFVGEVIMZLZBVCOZP
      ZAQRZCSZNVPABCDEFTUTVOWBUTVNWACUTVMVTAQUTVLVSVDUTVKVRBVCUTVJVQVFUTVGVHEVI
      UTEKUDUEUFUGUHUIUJUKULUTUMZDKHZVDVFVGKVIMZLZBVCOZPZAQRZCSZNZVAVPKFGWDWKLU
      NABCDKFTUODEUPWCVOWJWCVNWICWCVMWHAQWCVLWGVDWCVKWFBVCWCVJWEVFWCVGVHKVIUTEK
      UQUEUFUGUHUIUJUKURUS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Defined equality axioms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A version of ~ ax-ext for use with defined equality.  (Contributed by
     Scott Fenton, 12-Dec-2010.) $)
  axextdfeq $p |- E. z ( ( z e. x -> z e. y )
                    -> ( ( z e. y -> z e. x ) -> ( x e. w -> y e. w ) ) ) $=
    ( wel wb wi wex weq axextnd ax8 imim2i eximii biimpexp exbii mpbi ) CAEZCBE
    ZFZADEBDEGZGZCHQRGRQGTGGZCHSABIZGUACCABJUCTSABDKLMUAUBCQRTNOP $.

  $( A version of ~ ax-8 for use with defined equality.  (Contributed by Scott
     Fenton, 12-Dec-2010.) $)
  ax8dfeq $p |- E. z ( ( z e. x -> z e. y ) -> ( w e. x -> w e. y ) ) $=
    ( weq wel wi ax6e ax8 equcoms imim12d eximii ) CDEZCAFZCBFZGDAFZDBFZGGCCDHM
    PNOQPNGDCDCAIJCDBIKL $.

  ${
    $d w x $.  $d w y $.  $d z w $.
    $( ~ ax-ext with distinctors instead of distinct variable conditions.
       (Contributed by Scott Fenton, 13-Dec-2010.) $)
    axextdist $p |- ( ( -. A. z z = x /\ -. A. z z = y )
                      -> ( A. z ( z e. x <-> z e. y ) -> x = y ) ) $=
      ( vw weq wal wn wa wel wb nfnae nfan wnfc nfcvf adantr nfcrd adantl nfbid
      cv elequ1 wi bibi12d a1i cbvald axextg biimtrrdi ) CAECFGZCBECFGZHZCAIZCB
      IZJZCFDAIZDBIZJZDFABEUIUOULDCUGUHCCACKCBCKLUIUMUNCUICDASZUGCUPMUHCANOPUIC
      DBSZUHCUQMUGCBNQPRDCEZUOULJUAUIURUMUJUNUKDCATDCBTUBUCUDABDUEUF $.

    $( ~ axextb with distinctors instead of distinct variable conditions.
       (Contributed by Scott Fenton, 13-Dec-2010.) $)
    axextbdist $p |- ( ( -. A. z z = x /\ -. A. z z = y )
                      -> ( x = y <-> A. z ( z e. x <-> z e. y ) ) ) $=
      ( weq wal wn wa wel wb wi axc9 imp nfnae nfan elequ2 alimd syld axextdist
      a1i impbid ) CADCEFZCBDCEFZGZABDZCAHCBHIZCEZUCUDUDCEZUFUAUBUDUGJABCKLUCUD
      UECUAUBCCACMCBCMNUDUEJUCABCOSPQABCRT $.
  $}

  ${
    $d x y $.
    19.12b.1 $e |- F/ y ph $.
    19.12b.2 $e |- F/ x ps $.
    $( Version of ~ 19.12vv with not-free hypotheses, instead of distinct
       variable conditions.  (Contributed by Scott Fenton, 13-Dec-2010.)
       (Revised by Mario Carneiro, 11-Dec-2016.) $)
    19.12b $p |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) ) $=
      ( wi wal wex 19.21 exbii nfal 19.36 albii bitr2i 3bitri ) ABGZDHZCIABDHZG
      ZCIACHZSGZQCIZDHZRTCABDEJKASCBCDFLMUDUABGZDHUBUCUEDABCFMNUABDADCELJOP $.
  $}

  $( There is always a set not in ` y ` .  (Contributed by Scott Fenton,
     13-Dec-2010.) $)
  exnel $p |- E. x -. x e. y $=
    ( wel wn wex elirrv nfth weq ax8 con3d spime ax-mp ) BBCZDZABCZDZAEBFZNPABN
    AQGABHOMABBIJKL $.

  ${
    $d x z $.  $d y z $.
    $( Distinctors in terms of membership.  (NOTE: this only works with
       relations where we can prove ~ el and ~ elirrv .)  (Contributed by Scott
       Fenton, 15-Dec-2010.) $)
    distel $p |- ( -. A. y y = x <-> -. A. y -. x e. y ) $=
      ( vz weq wal wn wel wex el df-ex nfnae dveel1 nf5d nfnd elequ2 notbid a1i
      wb wi cbvald bitrid mpbii elirrv elequ1 mtbii alimi con3i impbii ) BADZBE
      ZFZABGZFZBEZFZUKACGZCHZUOACIUQUPFZCEZFUKUOUPCJUKUSUNUKURUMCBBABKZUKUPBUKU
      PBUTBACLMNCBDZURUMRSUKVAUPULCBAOPQTPUAUBUJUNUIUMBUIBBGULBUCBABUDUEUFUGUH
      $.
  $}

  $( ~ axextnd as a biconditional.  (Contributed by Scott Fenton,
     14-Dec-2010.) $)
  axextndbi $p |- E. z ( x = y <-> ( z e. x <-> z e. y ) ) $=
    ( weq wel wb wex wi wa axextnd elequ2 jctl eximii dfbi2 exbii mpbir ) ABDZC
    AECBEFZFZCGQRHZRQHZIZCGUAUBCCABJUATABCKLMSUBCQRNOP $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Hypothesis builders
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A more general form of ~ hbnt .  (Contributed by Scott Fenton,
     13-Dec-2010.) $)
  hbntg $p |- ( A. x ( ph -> A. x ps ) -> ( -. ps -> A. x -. ph ) ) $=
    ( wn wal wi axc7 con1i con3 al2imi syl5 ) BDBCEZDZCEZALFZCEADZCENBBCGHOMPCA
    LIJK $.

  $( A more general and closed form of ~ hbim .  (Contributed by Scott Fenton,
     13-Dec-2010.) $)
  hbimtg $p |- ( ( A. x ( ph -> A. x ch ) /\ ( ps -> A. x th ) ) ->
                ( ( ch -> ps ) -> A. x ( ph -> th ) ) ) $=
    ( wal wi wa wn hbntg pm2.21 alimi syl6 adantr ala1 imim2i adantl jad ) ACEF
    GEFZBDEFZGZHCBADGZEFZSCIZUCGUASUDAIZEFUCACEJUEUBEADKLMNUABUCGSTUCBDAEOPQR
    $.

  $( A more general and closed form of ~ hbal .  (Contributed by Scott Fenton,
     13-Dec-2010.) $)
  hbaltg $p |- ( A. x ( ph -> A. y ps ) -> ( A. x ph -> A. y A. x ps ) ) $=
    ( wal wi alim ax-11 syl6 ) ABDEZFCEACEJCEBCEDEAJCGBCDHI $.

  ${
    hbg.1 $e |- ( ph -> A. x ps ) $.
    $( A more general form of ~ hbn .  (Contributed by Scott Fenton,
       13-Dec-2010.) $)
    hbng $p |- ( -. ps -> A. x -. ph ) $=
      ( wal wi wn hbntg mpg ) ABCEFBGAGCEFCABCHDI $.

    ${
      hbg.2 $e |- ( ch -> A. x th ) $.
      $( A more general form of ~ hbim .  (Contributed by Scott Fenton,
         13-Dec-2010.) $)
      hbimg $p |- ( ( ps -> ch ) -> A. x ( ph -> th ) ) $=
        ( wal wi ax-gen hbimtg mp2an ) ABEHIZEHCDEHIBCIADIEHIMEFJGACBDEKL $.
    $}
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Well-founded zero, successor, and limits
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c wsuc WLim $.

  $( Declare the syntax for well-founded successor. $)
  cwsuc $a class wsuc ( R , A , X ) $.

  $( Declare the syntax for well-founded limit class. $)
  cwlim $a class WLim ( R , A ) $.

  $( Define the concept of a successor in a well-founded set.  (Contributed by
     Scott Fenton, 13-Jun-2018.)  (Revised by AV, 10-Oct-2021.) $)
  df-wsuc $a |- wsuc ( R , A , X ) = inf ( Pred ( `' R , A , X ) , A , R ) $.

  ${
    $d R x $.  $d A x $.
    $( Define the class of limit points of a well-founded set.  (Contributed by
       Scott Fenton, 15-Jun-2018.)  (Revised by AV, 10-Oct-2021.) $)
    df-wlim $a |- WLim ( R , A ) =
       { x e. A | ( x =/= inf ( A , A , R ) /\
           x = sup ( Pred ( R , A , x ) , A , R ) ) } $.
  $}

  $( Equality theorem for well-founded successor.  (Contributed by Scott
     Fenton, 13-Jun-2018.)  (Proof shortened by AV, 10-Oct-2021.) $)
  wsuceq123 $p |- ( ( R = S /\ A = B /\ X = Y ) ->
     wsuc ( R , A , X ) = wsuc ( S , B , Y ) ) $=
    ( wceq w3a ccnv cpred cwsuc simp1 cnveqd predeq123 syld3an1 simp2 infeq123d
    cinf df-wsuc 3eqtr4g ) CDGZABGZEFGZHZACIZEJZACRBDIZFJZBDRACEKBDFKUDUFACUHBD
    UEUGGUBUAUCUFUHGUDCDUAUBUCLZMABUEUGEFNOUAUBUCPUIQACESBDFST $.

  $( Equality theorem for well-founded successor.  (Contributed by Scott
     Fenton, 13-Jun-2018.) $)
  wsuceq1 $p |- ( R = S -> wsuc ( R , A , X ) = wsuc ( S , A , X ) ) $=
    ( wceq cwsuc eqid wsuceq123 mp3an23 ) BCEAAEDDEABDFACDFEAGDGAABCDDHI $.

  $( Equality theorem for well-founded successor.  (Contributed by Scott
     Fenton, 13-Jun-2018.) $)
  wsuceq2 $p |- ( A = B -> wsuc ( R , A , X ) = wsuc ( R , B , X ) ) $=
    ( wceq cwsuc eqid wsuceq123 mp3an13 ) CCEABEDDEACDFBCDFECGDGABCCDDHI $.

  $( Equality theorem for well-founded successor.  (Contributed by Scott
     Fenton, 13-Jun-2018.) $)
  wsuceq3 $p |- ( X = Y -> wsuc ( R , A , X ) = wsuc ( R , A , Y ) ) $=
    ( wceq cwsuc eqid wsuceq123 mp3an12 ) BBEAAECDEABCFABDFEBGAGAABBCDHI $.

  ${
    nfwsuc.1 $e |- F/_ x R $.
    nfwsuc.2 $e |- F/_ x A $.
    nfwsuc.3 $e |- F/_ x X $.
    $( Bound-variable hypothesis builder for well-founded successor.
       (Contributed by Scott Fenton, 13-Jun-2018.)  (Proof shortened by AV,
       10-Oct-2021.) $)
    nfwsuc $p |- F/_ x wsuc ( R , A , X ) $=
      ( cwsuc ccnv cpred cinf df-wsuc nfcnv nfpred nfinf nfcxfr ) ABCDHBCIZDJZB
      CKBCDLARBCABQDACEMFGNFEOP $.
  $}

  ${
    $d R x $.  $d S x $.  $d A x $.  $d B x $.
    $( Equality theorem for the limit class.  (Contributed by Scott Fenton,
       15-Jun-2018.)  (Proof shortened by AV, 10-Oct-2021.) $)
    wlimeq12 $p |- ( ( R = S /\ A = B ) ->
        WLim ( R , A ) = WLim ( S , B ) ) $=
      ( vx wceq wa cv cinf wne cpred csup crab cwlim simpr infeq123d neeq2d weq
      simpl df-wlim predeq123 mp3an3 supeq123d eqeq2d anbi12d rabeqbidv 3eqtr4g
      equid ) CDFZABFZGZEHZAACIZJZULACULKZACLZFZGZEAMULBBDIZJZULBDULKZBDLZFZGZE
      BMACNBDNUKURVDEABUIUJOZUKUNUTUQVCUKUMUSULUKAACBBDVEVEUIUJSZPQUKUPVBULUKUO
      ACVABDUIUJEERUOVAFEUHABCDULULUAUBVEVFUCUDUEUFEACTEBDTUG $.
  $}

  $( Equality theorem for the limit class.  (Contributed by Scott Fenton,
     15-Jun-2018.) $)
  wlimeq1 $p |- ( R = S -> WLim ( R , A ) = WLim ( S , A ) ) $=
    ( wceq cwlim eqid wlimeq12 mpan2 ) BCDAADABEACEDAFAABCGH $.

  $( Equality theorem for the limit class.  (Contributed by Scott Fenton,
     15-Jun-2018.) $)
  wlimeq2 $p |- ( A = B -> WLim ( R , A ) = WLim ( R , B ) ) $=
    ( wceq cwlim eqid wlimeq12 mpan ) CCDABDACEBCEDCFABCCGH $.

  ${
    $d R y $.  $d A y $.  $d x y $.
    nfwlim.1 $e |- F/_ x R $.
    nfwlim.2 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for the limit class.  (Contributed by
       Scott Fenton, 15-Jun-2018.)  (Proof shortened by AV, 10-Oct-2021.) $)
    nfwlim $p |- F/_ x WLim ( R , A ) $=
      ( vy cwlim cv cinf cpred csup wceq wa crab df-wlim nfcv nfinf nfne nfpred
      wne nfsup nfeq2 nfan nfrabw nfcxfr ) ABCGFHZBBCIZTZUFBCUFJZBCKZLZMZFBNFBC
      OULAFBUHUKAAUFUGAUFPZABBCEEDQRAUFUJAUIBCABCUFDEUMSEDUAUBUCEUDUE $.
  $}

  ${
    $d R x $.  $d A x $.  $d X x $.
    $( Membership in the limit class.  (Contributed by Scott Fenton,
       15-Jun-2018.)  (Revised by AV, 10-Oct-2021.) $)
    elwlim $p |- ( X e. WLim ( R , A ) <-> ( X e. A /\
        X =/= inf ( A , A , R ) /\
        X = sup ( Pred ( R , A , X ) , A , R ) ) ) $=
      ( vx cwlim wcel cinf wne cpred csup wceq wa neeq1 predeq3 supeq1d eqeq12d
      w3a cv id anbi12d df-wlim elrab2 3anass bitr4i ) CABEZFCAFZCAABGZHZCABCIZ
      ABJZKZLZLUFUHUKQDRZUGHZUMABUMIZABJZKZLULDCAUEUMCKZUNUHUQUKUMCUGMURUMCUPUJ
      URSURAUOUIBABUMCNOPTDABUAUBUFUHUKUCUD $.
  $}

  ${
    $d R x y z $.  $d A x y z $.
    $( The zero of a well-founded set is a member of that set.  (Contributed by
       Scott Fenton, 13-Jun-2018.)  (Revised by AV, 10-Oct-2021.) $)
    wzel $p |- ( ( R We A /\ R Se A /\ A =/= (/) ) ->
       inf ( A , A , R ) e. A ) $=
      ( vx vy vz wwe wse c0 wne w3a wor cv wrex wbr wn wral wi wa wcel wal weso
      3ad2ant1 cpred wceq wss simp1 simp2 ssidd simp3 tz6.26 syl22anc wb elpred
      cvv vex elv notbii imnan bitr4i pm2.27 ad2antll rspcev ex ad2antrl jctird
      breq1 biimtrid com23 alimdv eq0 r19.26 df-ral bitr3i 3imtr4g reximdva mpd
      expr infcl ) ABFZABGZAHIZJZCDEAABVSVTABKWAABUAUBWBABCLZUCZHUDZCAMZDLZWCBN
      ZOZDAPWCWGBNZELZWGBNZEAMZQZDAPRZCAMWBVSVTAAUEWAWFVSVTWAUFVSVTWAUGWBAUHVSV
      TWAUICAABUJUKWBWEWOCAWBWCASZRZWGWDSZOZDTWGASZWIWNRZQZDTZWEWOWQWSXBDWQWTWS
      XAWBWPWTWSXAQWSWTWIQZWBWPWTRRZXAWSWTWHRZOXDWRXFWRXFULCAUNBWCWGDUOUMUPUQWT
      WHURUSXEXDWIWNWTXDWIQWBWPWTWIUTVAWPWNWBWTWPWJWMWLWJEWCAWKWCWGBVFVBVCVDVEV
      GVQVHVIDWDVJWOXADAPXCWIWNDAVKXADAVLVMVNVOVPVR $.
  $}

  ${
    $d A x y z w $.  $d ph x y $.  $d R x y z w $.  $d X x y z w $.
    wsuclem.1 $e |- ( ph -> R We A ) $.
    wsuclem.2 $e |- ( ph -> R Se A ) $.
    wsuclem.3 $e |- ( ph -> X e. V ) $.
    wsuclem.4 $e |- ( ph -> E. w e. A X R w ) $.
    $( Lemma for the supremum properties of well-founded successor.
       (Contributed by Scott Fenton, 15-Jun-2018.)  (Revised by AV,
       10-Oct-2021.) $)
    wsuclem $p |- ( ph -> E. x e. A
         ( A. y e. Pred ( `' R , A , X ) -. y R x /\
           A. y e. A ( x R y -> E. z e. Pred ( `' R , A , X ) z R y ) ) ) $=
      ( cv c0 wrex wbr wa wcel cvv ccnv cpred wceq wn wi wwe wse wss wne predss
      wral a1i crab dfpred3g syl elexd wb brcnvg ancoms rexbidva bitrid biimpar
      rabn0 syl2anc eqnetrd tz6.26 syl22anc breq1 rexrab w3a noel simp2r eleq2d
      rexeqdv mtbiri simp3 elpredg mtbid 3expa ralrimiva simp1rl simp1rr adantr
      vex expr 3ad2ant1 elpred mpbir2and rspcev 3expia anim12d ancomsd reximdva
      biimtrid sylbid mpd ) AFGUAZIUBZGBNZUBZOUCZBWRPZCNZWSGQZUDZCWRUKZWSXCGQZD
      NZXCGQZDWRPZUEZCFUKZRZBFPZAFGUFFGUGWRFUHZWROUIXBJKXOAFWQIUJULAWRENZIWQQZE
      FUMZOAIHSZWRXRUCLEFWQHIUNUOAITSZIXPGQZEFPZXROUIZAIHLUPMXTYCYBYCXQEFPXTYBX
      QEFVCXTXQYAEFXPFSXTXQYAUQXPIFTGURUSUTVAVBVDVEBFWRGVFVGAXBXABXCIWQQZCFUMZP
      ZXNAXABWRYEAXSWRYEUCLCFWQHIUNUOVNYFWSIWQQZXARZBFPAXNYDYGXABCFXCWSIWQVHVIA
      YHXMBFAWSFSZRZXAYGXMYJXAXFYGXLAYIXAXFAYIXARZRXECWRAYKXCWRSZXEAYKYLVJZXCWT
      SZXDYMYNXCOSXCVKYMWTOXCAYIXAYLVLVMVOYMWSTSZYLYNXDUQYOYMBWDZULAYKYLVPWRTGW
      SXCVQVDVRVSVTWEAYIYGXLAYIYGRZRZXKCFYRXCFSZXGXJYRYSXGVJZWSWRSZXGXJYTUUAYIY
      GYIYGAYSXGWAYIYGAYSXGWBYTXSUUAYQUQYRYSXSXGAXSYQLWCWFFHWQIWSYPWGUOWHYRYSXG
      VPXIXGDWSWRXHWSXCGVHWIVDWJVTWEWKWLWMWNWOWP $.
  $}

  ${
    wsucex.1 $e |- ( ph -> R Or A ) $.
    $( Existence theorem for well-founded successor.  (Contributed by Scott
       Fenton, 16-Jun-2018.)  (Proof shortened by AV, 10-Oct-2021.) $)
    wsucex $p |- ( ph -> wsuc ( R , A , X ) e. _V ) $=
      ( cwsuc ccnv cpred cinf cvv df-wsuc infexd eqeltrid ) ABCDFBCGDHZBCIJBCDK
      ABNCELM $.
  $}

  ${
    $d R a b c y $.  $d A a b c y $.  $d X a b c y $.  $d ph a b $.
    wsuccl.1 $e |- ( ph -> R We A ) $.
    wsuccl.2 $e |- ( ph -> R Se A ) $.
    wsuccl.3 $e |- ( ph -> X e. V ) $.
    wsuccl.4 $e |- ( ph -> E. y e. A X R y ) $.
    $( If ` X ` is a set with an ` R ` successor in ` A ` , then its
       well-founded successor is a member of ` A ` .  (Contributed by Scott
       Fenton, 15-Jun-2018.)  (Proof shortened by AV, 10-Oct-2021.) $)
    wsuccl $p |- ( ph -> wsuc ( R , A , X ) e. A ) $=
      ( va vb vc cwsuc ccnv cpred cinf df-wsuc wwe wor weso syl infcl eqeltrid
      wsuclem ) ACDFNCDOFPZCDQCCDFRAKLMCUFDACDSCDTGCDUAUBAKLMBCDEFGHIJUEUCUD $.
  $}

  ${
    $d R a b c y $.  $d A a b c y $.  $d X a b c y $.  $d ph a b c $.
    $d Y y $.
    wsuclb.1 $e |- ( ph -> R We A ) $.
    wsuclb.2 $e |- ( ph -> R Se A ) $.
    wsuclb.3 $e |- ( ph -> X e. V ) $.
    wsuclb.4 $e |- ( ph -> Y e. A ) $.
    wsuclb.5 $e |- ( ph -> X R Y ) $.
    $( A well-founded successor is a lower bound on points after ` X ` .
       (Contributed by Scott Fenton, 16-Jun-2018.)  (Proof shortened by AV,
       10-Oct-2021.) $)
    wsuclb $p |- ( ph -> -. Y R wsuc ( R , A , X ) ) $=
      ( va vb vc vy wbr wcel wb syl2anc mpbird ccnv cpred cinf cwsuc wn elpredg
      brcnvg wwe wor weso syl cv wrex breq2 rspcev wsuclem inflb df-wsuc breq2i
      mpd sylnibr ) AFBCUAZEUBZBCUCZCPZFBCEUDZCPAFVCQZVEUEAVGFEVBPZAVHEFCPZKAFB
      QZEDQZVHVIRJIFEBDCUGSTAVKVJVGVHRIJBDVBEFUFSTALMNBVCFCABCUHBCUIGBCUJUKALMN
      OBCDEGHIAVJVIEOULZCPZOBUMJKVMVIOFBVLFECUNUOSUPUQUTVFVDFCBCEURUSVA $.
  $}

  ${
    $d R x $.  $d A x $.
    $( The class of limit points is a subclass of the base class.  (Contributed
       by Scott Fenton, 16-Jun-2018.) $)
    wlimss $p |- WLim ( R , A ) C_ A $=
      ( vx cv cinf wne cpred csup wceq wa cwlim df-wlim ssrab3 ) CDZAABEFNABNGA
      BHIJCAABKCABLM $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Quantifier-free definitions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c (x) Bigcup SSet Trans Limits Fix Funs Singleton Singletons Image Cart $.
  $c Img Domain Range pprod Apply Cup Cap Succ Funpart FullFun Restrict $.
  $c UB LB $.
  $( Declare the syntax for tail Cartesian product. $)
  ctxp $a class ( A (x) B ) $.
  $( Declare the syntax for the parallel product. $)
  cpprod $a class pprod ( R , S ) $.
  $( Declare the subset relationship class. $)
  csset $a class SSet $.
  $( Declare the transitive set class. $)
  ctrans $a class Trans $.
  $( Declare the set union relationship. $)
  cbigcup $a class Bigcup $.
  $( Declare the syntax for the fixpoints of a class. $)
  cfix $a class Fix A $.
  $( Declare the class of limit ordinals. $)
  climits $a class Limits $.
  $( Declare the syntax for the class of all function. $)
  cfuns $a class Funs $.
  $( Declare the syntax for the singleton function. $)
  csingle $a class Singleton $.
  $( Declare the syntax for the class of all singletons. $)
  csingles $a class Singletons $.
  $( Declare the syntax for the image functor. $)
  cimage $a class Image A $.
  $( Declare the syntax for the cartesian function. $)
  ccart $a class Cart $.
  $( Declare the syntax for the image function. $)
  cimg $a class Img $.
  $( Declare the syntax for the domain function. $)
  cdomain $a class Domain $.
  $( Declare the syntax for the range function. $)
  crange $a class Range $.
  $( Declare the syntax for the application function. $)
  capply $a class Apply $.
  $( Declare the syntax for the cup function. $)
  ccup $a class Cup $.
  $( Declare the syntax for the cap function. $)
  ccap $a class Cap $.
  $( Declare the syntax for the successor function. $)
  csuccf $a class Succ $.
  $( Declare the syntax for the functional part functor. $)
  cfunpart $a class Funpart F $.
  $( Declare the syntax for the full function functor. $)
  cfullfn $a class FullFun F $.
  $( Declare the syntax for the restriction function. $)
  crestrict $a class Restrict $.
  $( Declare the syntax for the upper bound relationship functor. $)
  cub $a class UB R $.
  $( Declare the syntax for the lower bound relationship functor. $)
  clb $a class LB R $.

  $( Define the tail cross of two classes.  Membership in this class is defined
     by ~ txpss3v and ~ brtxp .  (Contributed by Scott Fenton, 31-Mar-2012.) $)
  df-txp $a |- ( A (x) B ) = ( ( `' ( 1st |` ( _V X. _V ) ) o. A ) i^i
                               ( `' ( 2nd |` ( _V X. _V ) ) o. B ) ) $.

  $( Define the parallel product of two classes.  Membership in this class is
     defined by ~ pprodss4v and ~ brpprod .  (Contributed by Scott Fenton,
     11-Apr-2014.) $)
  df-pprod $a |- pprod ( A , B ) =
     ( ( A o. ( 1st |` ( _V X. _V ) ) ) (x)
       ( B o. ( 2nd |` ( _V X. _V ) ) ) ) $.

  $( Define the subset class.  For the value, see ~ brsset .  (Contributed by
     Scott Fenton, 31-Mar-2012.) $)
  df-sset $a |- SSet = ( ( _V X. _V ) \ ran ( _E (x) ( _V \ _E ) ) ) $.

  $( Define the class of all transitive sets.  (Contributed by Scott Fenton,
     31-Mar-2012.) $)
  df-trans $a |- Trans = ( _V \ ran ( ( _E o. _E ) \ _E ) ) $.

  $( Define the Bigcup function, which, per ~ fvbigcup , carries a set to its
     union.  (Contributed by Scott Fenton, 11-Apr-2012.) $)
  df-bigcup $a |- Bigcup = ( ( _V X. _V ) \
     ran ( ( _V (x) _E ) /_\ ( ( _E o. _E ) (x) _V ) ) ) $.

  $( Define the class of all fixpoints of a relationship.  (Contributed by
     Scott Fenton, 11-Apr-2012.) $)
  df-fix $a |- Fix A = dom ( A i^i _I ) $.

  $( Define the class of all limit ordinals.  (Contributed by Scott Fenton,
     11-Apr-2012.) $)
  df-limits $a |- Limits = ( ( On i^i Fix Bigcup ) \ { (/) } ) $.

  $( Define the class of all functions.  See ~ elfuns for membership.
     (Contributed by Scott Fenton, 18-Feb-2013.) $)
  df-funs $a |- Funs =
    ( ~P ( _V X. _V ) \
      Fix ( _E o. ( ( 1st (x) ( ( _V \ _I ) o. 2nd ) ) o. `' _E ) ) ) $.

  $( Define the singleton function.  See ~ brsingle for its value.
     (Contributed by Scott Fenton, 4-Apr-2014.) $)
  df-singleton $a |- Singleton =
     ( ( _V X. _V ) \ ran ( ( _V (x) _E ) /_\ ( _I (x) _V ) ) ) $.

  $( Define the class of all singletons.  See ~ elsingles for membership.
     (Contributed by Scott Fenton, 19-Feb-2013.) $)
  df-singles $a |- Singletons = ran Singleton $.

  $( Define the image functor.  This function takes a set ` A ` to a function
     ` x |-> ( A " x ) ` , providing that the latter exists.  See ~ imageval
     for the derivation.  (Contributed by Scott Fenton, 27-Mar-2014.) $)
  df-image $a |- Image A = ( ( _V X. _V ) \
           ran ( ( _V (x) _E ) /_\ ( ( _E o. `' A ) (x) _V ) ) ) $.

  $( Define the cartesian product function.  See ~ brcart for its value.
     (Contributed by Scott Fenton, 11-Apr-2014.) $)
  df-cart $a |- Cart = ( ( ( _V X. _V ) X. _V ) \
    ran ( ( _V (x) _E ) /_\ ( pprod ( _E , _E ) (x) _V ) ) ) $.

  $( Define the image function.  See ~ brimg for its value.  (Contributed by
     Scott Fenton, 12-Apr-2014.) $)
  df-img $a |- Img = ( Image ( ( 2nd o. 1st ) |` ( 1st |` ( _V X. _V ) ) )
                       o. Cart ) $.

  $( Define the domain function.  See ~ brdomain for its value.  (Contributed
     by Scott Fenton, 11-Apr-2014.) $)
  df-domain $a |- Domain = Image ( 1st |` ( _V X. _V ) ) $.

  $( Define the range function.  See ~ brrange for its value.  (Contributed by
     Scott Fenton, 11-Apr-2014.) $)
  df-range $a |- Range = Image ( 2nd |` ( _V X. _V ) ) $.

  $( Define the little cup function.  See ~ brcup for its value.  (Contributed
     by Scott Fenton, 14-Apr-2014.) $)
  df-cup $a |- Cup = ( ( ( _V X. _V ) X. _V ) \
  ran ( ( _V (x) _E ) /_\
        ( ( ( `' 1st o. _E ) u. ( `' 2nd o. _E ) ) (x) _V ) ) ) $.

  $( Define the little cap function.  See ~ brcap for its value.  (Contributed
     by Scott Fenton, 17-Apr-2014.) $)
  df-cap $a |- Cap = ( ( ( _V X. _V ) X. _V ) \
  ran ( ( _V (x) _E ) /_\
        ( ( ( `' 1st o. _E ) i^i ( `' 2nd o. _E ) ) (x) _V ) ) ) $.

  $( Define the restriction function.  See ~ brrestrict for its value.
     (Contributed by Scott Fenton, 17-Apr-2014.) $)
  df-restrict $a |- Restrict = ( Cap o.
    ( 1st (x) ( Cart o. ( 2nd (x) ( Range o. 1st ) ) ) ) ) $.

  $( Define the successor function.  See its alternate version ~ dfsuccf2 .
     See ~ brsuccf for its value.  Cf. the equivalent ~ df-sucmap family.
     (Contributed by Scott Fenton, 14-Apr-2014.) $)
  df-succf $a |- Succ = ( Cup o. ( _I (x) Singleton ) ) $.

  $( Define the application function.  See ~ brapply for its value.
     (Contributed by Scott Fenton, 12-Apr-2014.) $)
  df-apply $a |- Apply = ( ( Bigcup o. Bigcup ) o.
  ( ( ( _V X. _V ) \
      ran ( ( _V (x) _E ) /_\ ( ( _E |` Singletons ) (x) _V ) ) ) o.
  ( ( Singleton o. Img ) o. pprod ( _I , Singleton ) ) ) ) $.

  $( Define the functional part of a class ` F ` .  This is the maximal part of
     ` F ` that is a function.  See ~ funpartfun and ~ funpartfv for the
     meaning of this statement.  (Contributed by Scott Fenton, 16-Apr-2014.) $)
  df-funpart $a |- Funpart F =
             ( F |` dom ( ( Image F o. Singleton ) i^i ( _V X. Singletons ) ) )
      $.

  $( Define the full function over ` F ` .  This is a function with domain
     ` _V ` that always agrees with ` F ` for its value.  (Contributed by Scott
     Fenton, 17-Apr-2014.) $)
  df-fullfun $a |- FullFun F = ( Funpart F u. ( ( _V \ dom Funpart F ) X. { (/)
      } ) ) $.

  $( Define the upper bound relationship functor.  See ~ brub for value.
     (Contributed by Scott Fenton, 3-May-2018.) $)
  df-ub $a |- UB R = ( ( _V X. _V ) \ ( ( _V \ R ) o. `' _E ) ) $.

  $( Define the lower bound relationship functor.  See ~ brlb for value.
     (Contributed by Scott Fenton, 3-May-2018.) $)
  df-lb $a |- LB R = UB `' R $.

  ${
    $d A x y z $.  $d B x y z $.
    $( A tail Cartesian product is a subset of the class of ordered triples.
       (Contributed by Scott Fenton, 31-Mar-2012.) $)
    txpss3v $p |- ( A (x) B ) C_ ( _V X. ( _V X. _V ) ) $=
      ( vx vy vz ctxp c1st cvv cxp cres ccnv ccom c2nd cin df-txp inss1 cv wcel
      wbr vex relco wa wex cop brcnv brresi simplbi sylbi adantl exlimiv opelco
      opelxp mpbiran 3imtr4i relssi sstri eqsstri ) ABFGHHIZJZKZALZMURJKBLZNZHU
      RIZABOVCVAVDVAVBPCDVAVDUTAUACQZEQZASZVFDQZUTSZUBZEUCVHURRZVEVHUDZVARVLVDR
      ZVJVKEVIVKVGVIVHVFUSSZVKVFVHUSETZDTZUEVNVKVHVFGSURVHVFGVOUFUGUHUIUJEVEVHU
      TACTZVPUKVMVEHRVKVQVEVHHURULUMUNUOUPUQ $.
  $}

  $( A tail Cartesian product is a relationship.  (Contributed by Scott Fenton,
     31-Mar-2012.) $)
  txprel $p |- Rel ( A (x) B ) $=
    ( ctxp wrel cvv cxp wss txpss3v xpss sstri df-rel mpbir ) ABCZDMEEFZGMENFNA
    BHENIJMKL $.

  ${
    $d A y z $.  $d B y z $.  $d X y z $.  $d Y y z $.  $d Z y z $.
    brtxp.1 $e |- X e. _V $.
    brtxp.2 $e |- Y e. _V $.
    brtxp.3 $e |- Z e. _V $.
    $( Characterize a ternary relation over a tail Cartesian product.  Together
       with ~ txpss3v , this completely defines membership in a tail cross.
       (Contributed by Scott Fenton, 31-Mar-2012.)  (Proof shortened by Peter
       Mazsa, 2-Oct-2022.) $)
    brtxp $p |- ( X ( A (x) B ) <. Y , Z >. <-> ( X A Y /\ X B Z ) ) $=
      ( vy vz wbr c1st cvv cres ccnv ccom c2nd wa wex 3bitri cop cxp cin df-txp
      ctxp breqi brin cv wceq opex brco vex brcnv opelvv brresi mpbiran br1steq
      wcel anbi1ci exbii breq2 ceqsexv br2ndeq anbi12i ) CDEUAZABUEZKCVELMMUBZN
      ZOZAPZQVGNZOZBPZUCZKCVEVJKZCVEVMKZRCDAKZCEBKZRCVEVFVNABUDUFCVEVJVMUGVOVQV
      PVRVOCIUHZAKZVSVEVIKZRZISVSDUIZVTRZISVQICVEVIAFDEUJZUKWBWDIWAWCVTWAVEVSVH
      KZVEVSLKZWCVSVEVHIULZWEUMWFVEVGURZWGDEGHUNZVGVEVSLWHUOUPDEVSGHUQTUSUTVTVQ
      IDGVSDCAVAVBTVPCJUHZBKZWKVEVLKZRZJSWKEUIZWLRZJSVRJCVEVLBFWEUKWNWPJWMWOWLW
      MVEWKVKKZVEWKQKZWOWKVEVKJULZWEUMWQWIWRWJVGVEWKQWSUOUPDEWKGHVCTUSUTWLVRJEH
      WKECBVAVBTVDT $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.  $d S x y $.
    brtxp2.1 $e |- A e. _V $.
    $( The binary relation over a tail cross when the second argument is not an
       ordered pair.  (Contributed by Scott Fenton, 14-Apr-2014.)  (Revised by
       Mario Carneiro, 3-May-2015.) $)
    brtxp2 $p |- ( A ( R (x) S ) B <->
            E. x E. y ( B = <. x , y >. /\ A R x /\ A S y ) ) $=
      ( ctxp wbr cv cop wceq wa wex w3a cvv wcel bitr4i 2exbii vex txpss3v brel
      cxp simprd elvv sylib pm4.71ri 19.41vv breq2 pm5.32i anbi2i 3anass 3bitri
      brtxp ) CDEFHZIZDAJZBJZKZLZUPMZBNANZUTCUSUOIZMZBNANUTCUQEIZCURFIZOZBNANUP
      UTBNANZUPMVBUPVHUPDPPUCZQZVHUPCPQVJCDPVIUOEFUAUBUDABDUEUFUGUTUPABUHRVAVDA
      BUTUPVCDUSCUOUIUJSVDVGABVDUTVEVFMZMVGVCVKUTEFCUQURGATBTUNUKUTVEVFULRSUM
      $.
  $}

  $( Expanded definition of parallel product.  (Contributed by Scott Fenton,
     3-May-2014.) $)
  dfpprod2 $p |- pprod ( A , B ) =
     ( ( `' ( 1st |` ( _V X. _V ) ) o. ( A o. ( 1st |` ( _V X. _V ) ) ) ) i^i
       ( `' ( 2nd |` ( _V X. _V ) ) o. ( B o. ( 2nd |` ( _V X. _V ) ) ) ) ) $=
    ( cpprod c1st cvv cxp cres ccom c2nd ctxp ccnv cin df-pprod df-txp eqtri )
    ABCADEEFZGZHZBIPGZHZJQKRHSKTHLABMRTNO $.

  $( A converse law for parallel product.  (Contributed by Scott Fenton,
     3-May-2014.) $)
  pprodcnveq $p |- pprod ( R , S ) = `' pprod ( `' R , `' S ) $=
    ( cpprod c1st cvv cxp cres ccnv ccom c2nd cin dfpprod2 cnveqi cnvco1 coeq1i
    cnvin coass 3eqtri ineq12i eqtr4i ) ABCDEEFZGZHZAUBIIZJUAGZHZBUEIIZKZAHZBHZ
    CZHZABLULUCUIUBIZIZUFUJUEIZIZKZHUNHZUPHZKUHUKUQUIUJLMUNUPPURUDUSUGURUMHZUBI
    UCAIZUBIUDUBUMNUTVAUBAUBNOUCAUBQRUSUOHZUEIUFBIZUEIUGUEUONVBVCUEBUENOUFBUEQR
    SRT $.

  ${
    $d A x y z w $.  $d B x y z w $.
    $( The parallel product is a subclass of
       ` ( ( _V X. _V ) X. ( _V X. _V ) ) ` .  (Contributed by Scott Fenton,
       11-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.)  (Proof
       shortened by Peter Mazsa, 2-Oct-2022.) $)
    pprodss4v $p |- pprod ( A , B ) C_ ( ( _V X. _V ) X. ( _V X. _V ) ) $=
      ( vx vy vz vw c1st cvv cxp cres ccom cv cop wcel wex wbr vex adantr sylbi
      wa cpprod c2nd ctxp df-pprod txprel txpss3v sseli opelxp2 wceq elvv opeq2
      syl wi eleq1d df-br brtxp brresi simplbi exlimiv sylbir biimtrdi exlimivv
      brco mpcom opelxpd relssi eqsstri ) ABUAAGHHIZJZKZBUBVHJKZUCZVHVHIZABUDCD
      VLVMVJVKUECLZDLZMZVLNZVNVOVHVHVOVHNZVQVNVHNZVQVPHVHIZNVRVLVTVPVJVKUFUGVNV
      OHVHUHULZVRVOELZFLZMZUIZFOEOVQVSUMZEFVOUJWEWFEFWEVQVNWDMZVLNZVSWEVPWGVLVO
      WDVNUKUNWHVNWDVLPZVSVNWDVLUOWIVNWBVJPZVNWCVKPZTVSVJVKVNWBWCCQZEQZFQUPWJVS
      WKWJVNVOVIPZVOWBAPZTZDOVSDVNWBAVIWLWMVCWPVSDWNVSWOWNVSVNVOGPVHVNVOGDQUQUR
      RUSSRSUTVAVBSVDWAVEVFVG $.
  $}

  ${
    $d A x $.  $d B y $.  $d W y $.  $d X x $.  $d X y $.  $d Y x $.  $d Y y $.
    $d Z x $.
    brpprod.1 $e |- X e. _V $.
    brpprod.2 $e |- Y e. _V $.
    brpprod.3 $e |- Z e. _V $.
    brpprod.4 $e |- W e. _V $.
    $( Characterize a quaternary relation over a tail Cartesian product.
       Together with ~ pprodss4v , this completely defines membership in a
       parallel product.  (Contributed by Scott Fenton, 11-Apr-2014.)  (Revised
       by Mario Carneiro, 19-Apr-2014.) $)
    brpprod $p |- ( <. X , Y >. pprod ( A , B ) <. Z , W >. <->
            ( X A Z /\ Y B W ) ) $=
      ( vx vy cop wbr c1st cvv c2nd wa wex 3bitri cpprod cxp cres ccom df-pprod
      ctxp breqi opex brtxp cv wceq brco wcel opelvv vex brresi mpbiran br1steq
      bitri anbi1i exbii breq1 ceqsexv br2ndeq anbi12i ) DEMZFCMZABUAZNVFVGAOPP
      UBZUCZUDZBQVIUCZUDZUFZNVFFVKNZVFCVMNZRDFANZECBNZRVFVGVHVNABUEUGVKVMVFFCDE
      UHZIJUIVOVQVPVRVOVFKUJZVJNZVTFANZRZKSVTDUKZWBRZKSVQKVFFAVJVSIULWCWEKWAWDW
      BWAVFVTONZWDWAVFVIUMZWFDEGHUNZVIVFVTOKUOUPUQDEVTGHURUSUTVAWBVQKDGVTDFAVBV
      CTVPVFLUJZVLNZWICBNZRZLSWIEUKZWKRZLSVRLVFCBVLVSJULWLWNLWJWMWKWJVFWIQNZWMW
      JWGWOWHVIVFWIQLUOUPUQDEWIGHVDUSUTVAWKVRLEHWIECBVBVCTVET $.
  $}

  ${
    $d w z $.  $d R w $.  $d R z $.  $d S w $.  $d S z $.  $d X w $.  $d X z $.
    $d Y w $.  $d Y z $.  $d Z w $.  $d Z z $.
    brpprod3.1 $e |- X e. _V $.
    brpprod3.2 $e |- Y e. _V $.
    brpprod3.3 $e |- Z e. _V $.
    $( Condition for parallel product when the last argument is not an ordered
       pair.  (Contributed by Scott Fenton, 11-Apr-2014.)  (Revised by Mario
       Carneiro, 19-Apr-2014.) $)
    brpprod3a $p |- ( <. X , Y >. pprod ( R , S ) Z <->
       E. z E. w ( Z = <. z , w >. /\ X R z /\ Y S w ) ) $=
      ( cop wbr cv wa wex cvv wcel bitr4i 2exbii vex cpprod wceq pprodss4v brel
      w3a cxp simprd sylib pm4.71ri 19.41vv breq2 pm5.32i brpprod anbi2i 3anass
      elvv 3bitri ) EFKZGCDUAZLZGAMZBMZKZUBZUTNZBOAOZVDURVCUSLZNZBOAOVDEVACLZFV
      BDLZUEZBOAOUTVDBOAOZUTNVFUTVLUTGPPUFZQZVLUTURVMQVNURGVMVMUSCDUCUDUGABGUPU
      HUIVDUTABUJRVEVHABVDUTVGGVCURUSUKULSVHVKABVHVDVIVJNZNVKVGVOVDCDVBEFVAHIAT
      BTUMUNVDVIVJUORSUQ $.

    $( Condition for parallel product when the first argument is not an ordered
       pair.  (Contributed by Scott Fenton, 3-May-2014.) $)
    brpprod3b $p |- ( X pprod ( R , S ) <. Y , Z >. <->
       E. z E. w ( X = <. z , w >. /\ z R Y /\ w S Z ) ) $=
      ( cop cpprod wbr ccnv cv w3a wex brcnv bitri vex wceq opex brpprod3a biid
      pprodcnveq breqi 3anbi123i 2exbii ) EFGKZCDLZMEUICNZDNZLZNZMZEAOZBOZKUAZU
      PFCMZUQGDMZPZBQAQZEUIUJUNCDUEUFUOURFUPUKMZGUQULMZPZBQAQZVBUOUIEUMMVFEUIUM
      HFGUBRABUKULFGEIJHUCSVEVAABURURVCUSVDUTURUDFUPCIATRGUQDJBTRUGUHSS $.
  $}

  $( The subset class is a binary relation.  (Contributed by Scott Fenton,
     31-Mar-2012.) $)
  relsset $p |- Rel SSet $=
    ( csset wrel cvv cxp wss cep cdif ctxp df-sset difss eqsstri df-rel mpbir
    crn ) ABACCDZEAOFCFGHNZGOIOPJKALM $.

  ${
    $d A x y $.  $d B x y $.
    brsset.1 $e |- B e. _V $.
    $( For sets, the ` SSet ` binary relation is equivalent to the subset
       relationship.  (Contributed by Scott Fenton, 31-Mar-2012.) $)
    brsset $p |- ( A SSet B <-> A C_ B ) $=
      ( vx vy csset wbr cvv wcel wss relsset cv cep wn wex wa vex mpbiran bitri
      cdif brrelex1i ssex breq1 sseq1 cop ctxp crn wal opex elrn brtxp epel brv
      wi brdif epeli xchbinx anbi12i exbii exanali 3bitrri con1bii df-br eleq2i
      cxp df-sset opelvv eldif df-ss 3bitr4i vtoclbg pm5.21nii ) ABFGZAHIABJZAB
      FKUAABCUBDLZBFGZVOBJZVMVNDAHVOABFUCVOABUDVOBUEZMHMTZUFZUGZIZNZELZVOIZWDBI
      ZUNEUHZVPVQWGWBWBWDVRVTGZEOWEWFNZPZEOWGNEVRVTVOBUIUJWHWJEWHWDVOMGZWDBVSGZ
      PWJMVSWDVOBEQDQZCUKWKWEWLWIDWDULWLWDBMGZWFWLWDBHGWNNWDBUMWDBHMUORWDBCUPUQ
      URSUSWEWFEUTVAVBVPVRFIZWCVOBFVCWOVRHHVEZWATZIZWCFWQVRVFVDWRVRWPIWCVOBWMCV
      GVRWPWAVHRSSEVOBVIVJVKVL $.
  $}

  ${
    $d y z $.
    $( ` _I ` is equal to the intersection of ` SSet ` and its converse.
       (Contributed by Scott Fenton, 31-Mar-2012.) $)
    idsset $p |- _I = ( SSet i^i `' SSet ) $=
      ( vy vz cid csset ccnv cin reli wrel relsset relin1 ax-mp weq cv wss eqss
      wa wbr vex brsset bitri ideq brin brcnv anbi12i 3bitr4i eqbrriv ) ABCDDEZ
      FZGDHUHHIDUGJKABLAMZBMZNZUJUINZPZUIUJCQUIUJUHQZUIUJOUIUJBRZUAUNUIUJDQZUIU
      JUGQZPUMUIUJDUGUBUPUKUQULUIUJUOSUQUJUIDQULUIUJDARZUOUCUJUIURSTUDTUEUF $.
  $}

  ${
    eltrans.1 $e |- A e. _V $.
    $( Membership in the class of all transitive sets.  (Contributed by Scott
       Fenton, 31-Mar-2012.) $)
    eltrans $p |- ( A e. Trans <-> Tr A ) $=
      ( ctrans wcel cvv cep ccom cdif crn wtr df-trans eleq2i dftr6 bitr4i ) AC
      DAEFFGFHIHZDAJCOAKLABMN $.
  $}

  ${
    $d x y $.

    $( A quantifier-free definition of ` On ` .  (Contributed by Scott Fenton,
       5-Apr-2012.) $)
    dfon3 $p |- On =
     ( _V \ ran ( ( SSet i^i ( Trans X. _V ) ) \ ( _I u. _E ) ) ) $=
      ( vy vx cv wa wcel cvv csset ctrans cid cep cdif wceq wbr wex vex anbi12i
      wn bitri wo anbi1i con0 wpss wtr wi wal cab cxp cin cun crn dfon2 wb elrn
      eqabcb wss brin brsset brxp mpbiran2 eltrans ioran brun ideq epel orbi12i
      brdif dfpss2 an32 anass 3bitr4i exbii exanali con2bii eldif bitr4i mpgbir
      xchnxbir mpbiran eqtri ) UAACZBCZUBZVTUCZDZVTWAEZUDAUEZBUFZFGHFUGZUHZIJUI
      ZKZUJZKZBAUKWGWMLWFWAWMEZULBWFBWMUNWFWAWLEZQZWNWOWFWOVTWAWKMZANZWFQZAWAWK
      BOZUMWRWDWEQZDZANWSWQXBAVTWAWIMZVTWAWJMZQZDVTWAUOZWCDZVTWALZQZXADZDZWQXBX
      CXGXEXJXCVTWAGMZVTWAWHMZDXGVTWAGWHUPXLXFXMWCVTWAWTUQXMVTHEZWCXMXNWAFEZWTV
      TWAHFURUSVTAOUTRPRXHWESZXJXDXHWEVAXDVTWAIMZVTWAJMZSXPVTWAIJVBXQXHXRWEVTWA
      WTVCBVTVDVERVQPVTWAWIWJVFXBXGXIDZXADXKWDXSXAWDXFXIDZWCDXSWBXTWCVTWAVGTXFX
      IWCVHRTXGXIXAVIRVJVKWDWEAVLRRVMWNXOWPWTWAFWLVNVRVOVPVS $.
  $}

  $( Another quantifier-free definition of ` On ` .  (Contributed by Scott
     Fenton, 4-May-2014.) $)
  dfon4 $p |- On = ( _V \ ( ( SSet \ ( _I u. _E ) ) " Trans ) ) $=
    ( con0 cvv csset ctrans cxp cin cid cep cun cdif crn cima dfon3 cres df-ima
    df-res indif1 eqtri rneqi difeq2i eqtr4i ) ABCDBEZFGHIZJZKZJBCUCJZDLZJMUGUE
    BUGUFDNZKUEUFDOUHUDUHUFUBFUDUFDPCUBUCQRSRTUA $.

  ${
    $d A x $.  $d B x $.  $d R x $.
    brtxpsd.1 $e |- A e. _V $.
    brtxpsd.2 $e |- B e. _V $.
    $( Expansion of a common form used in quantifier-free definitions.
       (Contributed by Scott Fenton, 17-Apr-2014.)  (Revised by Mario Carneiro,
       19-Apr-2014.) $)
    brtxpsd $p |- ( -. A ran ( ( _V (x) _E ) /_\ ( R (x) _V ) ) B <->
       A. x ( x e. B <-> x R A ) ) $=
      ( cv wcel wbr wb wal cvv cep ctxp csymdif wn wex brv brtxp bitri crn opex
      cop df-br brsymdif vex mpbiran epeli mpbiran2 bibi12i xchbinx exbii exnal
      elrn 3bitrri con1bii ) AGZCHZUQBDIZJZAKZBCLMNZDLNZOZUAZIZVFBCUCZVEHZUTPZA
      QZVAPBCVEUDVHUQVGVDIZAQVJAVGVDBCUBUNVKVIAVKUQVGVBIZUQVGVCIZJUTUQVGVBVCUEV
      LURVMUSVLUQCMIZURVLUQBLIVNUQBRLMUQBCAUFZEFSUGUQCFUHTVMUSUQCLIUQCRDLUQBCVO
      EFSUIUJUKULTUTAUMUOUP $.
  $}

  ${
    $d A x $.  $d B x $.  $d S x $.
    brtxpsd2.1 $e |- A e. _V $.
    brtxpsd2.2 $e |- B e. _V $.
    brtxpsd2.3 $e |- R = ( C \ ran ( ( _V (x) _E ) /_\ ( S (x) _V ) ) ) $.
    brtxpsd2.4 $e |- A C B $.
    $( Another common abbreviation for quantifier-free definitions.
       (Contributed by Scott Fenton, 21-Apr-2014.) $)
    brtxpsd2 $p |- ( A R B <-> A. x ( x e. B <-> x S A ) ) $=
      ( wbr cvv cep ctxp csymdif crn wn cv wcel bitri wb wal cdif breqi mpbiran
      wa brdif brtxpsd ) BCEKZBCLMNFLNOPZKQZARZCSULBFKUAAUBUIBCDKZUKJUIBCDUJUCZ
      KUMUKUFBCEUNIUDBCDUJUGTUEABCFGHUHT $.

    ${
      $d X x $.
      brtxpsd3.5 $e |- ( x e. X <-> x S A ) $.
      $( A third common abbreviation for quantifier-free definitions.
         (Contributed by Scott Fenton, 3-May-2014.) $)
      brtxpsd3 $p |- ( A R B <-> B = X ) $=
        ( cv wcel wb wal wbr wceq bibi2i albii dfcleq brtxpsd2 3bitr4ri ) AMZCN
        ZUDGNZOZAPUEUDBFQZOZAPCGRBCEQUGUIAUFUHUELSTACGUAABCDEFHIJKUBUC $.
    $}
  $}

  $( The ` Bigcup ` relationship is a relationship.  (Contributed by Scott
     Fenton, 11-Apr-2012.) $)
  relbigcup $p |- Rel Bigcup $=
    ( cbigcup wrel cvv cxp cep ctxp ccom csymdif crn cdif relxp ax-mp df-bigcup
    reldif releqi mpbir ) ABCCDZCEFEEGCFHIZJZBZQBTCCKQRNLASMOP $.

  ${
    $d A x y z $.  $d B x y z $.
    brbigcup.1 $e |- B e. _V $.
    $( Binary relation over ` Bigcup ` .  (Contributed by Scott Fenton,
       11-Apr-2012.) $)
    brbigcup $p |- ( A Bigcup B <-> U. A = B ) $=
      ( vx vy vz cbigcup wbr wcel cuni wceq relbigcup brrelex1i eleq1 mpbiri cv
      cvv cep vex wrex uniexb sylibr breq1 unieq eqeq1d cxp ccom df-bigcup brxp
      mpbir2an epel rexbii coep 3bitr4ri brtxpsd3 eqcom bitri vtoclbg pm5.21nii
      eluni2 ) ABGHZAQIZAJZBKZABGLMVDVCQIZVBVDVEBQIZCVCBQNOAUAUBDPZBGHZVGJZBKZV
      AVDDAQVGABGUCVGAKVIVCBVGAUDUEVHBVIKVJEVGBQQUFZGRRUGZVIDSZCUHVGBVKHVGQIVFV
      MCVGBQQUIUJEPZFPZRHZFVGTVNVOIZFVGTVNVGVLHVNVIIVPVQFVGFVNUKULFVNVGRESVMUMF
      VNVGUTUNUOBVIUPUQURUS $.
  $}

  ${
    $d x y z t $.
    $( ` Bigcup ` using maps-to notation.  (Contributed by Scott Fenton,
       16-Apr-2012.) $)
    dfbigcup2 $p |- Bigcup = ( x e. _V |-> U. x ) $=
      ( vy vz vt cbigcup cvv cuni cmpt relbigcup mptrel wceq wbr eqcom brbigcup
      cv vex wcel wa weq eleq1w unieq eqeq2d anbi12d biantrur eqeq1 df-mpt brab
      bitr4di 3bitr4i eqbrriv ) BCEAFAOZGZHZIAFULJBOZGZCOZKUPUOKZUNUPELUNUPUMLU
      OUPMUNUPCPZNUKFQZDOZULKZRZUTUOKZUQADUNUPUMBPZURABSZVBUNFQZVCRVCVEUSVFVAVC
      ABFTVEULUOUTUKUNUAUBUCVFVCVDUDUHUTUPUOUEADFULUFUGUIUJ $.
  $}

  ${
    $d x y $.
    $( ` Bigcup ` maps the universe onto itself.  (Contributed by Scott Fenton,
       16-Apr-2012.) $)
    fobigcup $p |- Bigcup : _V -onto-> _V $=
      ( vx vy cvv cbigcup wfo wfn crn wceq cuni wcel wral uniexg rgen dfbigcup2
      cv mptfng mpbi wrex cab rnmpt vex csn vsnex unisnv eqcomi unieq mp2an 2th
      rspceeqv eqabi eqtr4i df-fo mpbir2an ) CCDEDCFZDGZCHAOZIZCJZACKUNURACUPCL
      MACUQDANZPQUOBOZUQHACRZBSCABCUQDUSTVABCUTCJVABUAUTUBZCJUTVBIZHVABUCVCUTBU
      DUEAVBCUQVCUTUPVBUFUIUGUHUJUKCCDULUM $.
  $}

  $( ` Bigcup ` is a function over the universal class.  (Contributed by Scott
     Fenton, 11-Apr-2012.) $)
  fnbigcup $p |- Bigcup Fn _V $=
    ( cvv cbigcup wfo wfn fobigcup fofn ax-mp ) AABCBADEAABFG $.

  ${
    fvbigcup.1 $e |- A e. _V $.
    $( For sets, ` Bigcup ` yields union.  (Contributed by Scott Fenton,
       11-Apr-2012.) $)
    fvbigcup $p |- ( Bigcup ` A ) = U. A $=
      ( cbigcup cfv cuni wceq wbr eqid uniex brbigcup mpbir cvv wfn wb fnbigcup
      wcel fnbrfvb mp2an ) ACDAEZFZASCGZUASSFSHASABIJKCLMALPTUANOBLASCQRK $.
  $}

  ${
    $d A x $.  $d R x $.
    elfix.1 $e |- A e. _V $.
    $( Membership in the fixpoints of a class.  (Contributed by Scott Fenton,
       11-Apr-2012.) $)
    elfix $p |- ( A e. Fix R <-> A R A ) $=
      ( vx cfix wcel cid cin cdm cv wceq wbr wex df-fix eleq2i eldm brin 3bitri
      wa bitri ancom vex ideq eqcom anbi1i exbii breq2 ceqsexv ) ABEZFABGHZIZFZ
      DJZAKZAUMBLZSZDMZAABLZUIUKABNOULAUMUJLZDMUQDAUJCPUSUPDUSUOAUMGLZSUTUOSUPA
      UMBGQUOUTUAUTUNUOUTAUMKUNAUMDUBUCAUMUDTUERUFTUOURDACUMAABUGUHR $.
  $}

  ${
    $d A x $.  $d R x $.
    elfix2.1 $e |- Rel R $.
    $( Alternative membership in the fixpoint of a class.  (Contributed by
       Scott Fenton, 11-Apr-2012.) $)
    elfix2 $p |- ( A e. Fix R <-> A R A ) $=
      ( vx cfix wcel cvv wbr elex brrelex1i cv eleq1 wb breq12 anidms vex elfix
      wceq vtoclbg pm5.21nii ) ABEZFZAGFAABHZAUAIAABCJDKZUAFUDUDBHZUBUCDAGUDAUA
      LUDARUEUCMUDAUDABNOUDBDPQST $.
  $}

  ${
    $d A x y $.
    $( The fixpoints of a class in terms of its range.  (Contributed by Scott
       Fenton, 16-Apr-2012.) $)
    dffix2 $p |- Fix A = ran ( A i^i _I ) $=
      ( vx vy cfix cid cin crn cv wcel wbr vex elfix wex weq wa elrn brin ancom
      ideq 3bitri anbi1i exbii breq1 equsexvw bitr4i eqriv ) BADZAEFZGZBHZUGIUJ
      UJAJZUJUIIZUJABKZLULCHZUJUHJZCMCBNZUNUJAJZOZCMUKCUJUHUMPUOURCUOUQUNUJEJZO
      USUQOURUNUJAEQUQUSRUSUPUQUNUJUMSUATUBUQUKCBUNUJUJAUCUDTUEUF $.
  $}

  $( The fixpoints of a class are a subset of its domain.  (Contributed by
     Scott Fenton, 16-Apr-2012.) $)
  fixssdm $p |- Fix A C_ dom A $=
    ( cfix cid cin cdm df-fix wss inss1 dmss ax-mp eqsstri ) ABACDZEZAEZAFLAGMN
    GACHLAIJK $.

  $( The fixpoints of a class are a subset of its range.  (Contributed by Scott
     Fenton, 16-Apr-2012.) $)
  fixssrn $p |- Fix A C_ ran A $=
    ( cfix cid cin crn dffix2 inss1 rnssi eqsstri ) ABACDZEAEAFJAACGHI $.

  ${
    $d A x $.
    $( The fixpoints of a class are the same as those of its converse.
       (Contributed by Scott Fenton, 16-Apr-2012.) $)
    fixcnv $p |- Fix A = Fix `' A $=
      ( vx cfix ccnv cv wbr wcel vex brcnv elfix 3bitr4ri eqriv ) BACZADZCZBEZP
      NFPPAFPOGPMGPPABHZQIPNQJPAQJKL $.
  $}

  $( The fixpoint operator distributes over union.  (Contributed by Scott
     Fenton, 16-Apr-2012.) $)
  fixun $p |- Fix ( A u. B ) = ( Fix A u. Fix B ) $=
    ( cun cid cin cdm cfix indir dmeqi dmun eqtri df-fix uneq12i 3eqtr4i ) ABCZ
    DEZFZADEZFZBDEZFZCZOGAGZBGZCQRTCZFUBPUEABDHIRTJKOLUCSUDUAALBLMN $.

  ${
    ellimits.1 $e |- A e. _V $.
    $( Membership in the class of all limit ordinals.  (Contributed by Scott
       Fenton, 11-Apr-2012.) $)
    ellimits $p |- ( A e. Limits <-> Lim A ) $=
      ( climits wcel con0 cbigcup cfix cin c0 csn cdif wn wlim df-limits eleq2i
      wa eldif wceq 3bitri anbi12i word wne cuni 3anan32 df-lim elin elon elfix
      w3a wbr brbigcup eqcom bitri elsn necon3bbii 3bitr4ri ) ACDAEFGZHZIJZKZDA
      URDZAUSDZLZPZAMZCUTANOAURUSQAUAZAIUBZAAUCZRZUIVFVIPZVGPVEVDVFVGVIUDAUEVAV
      JVCVGVAAEDZAUQDZPVJAEUQUFVKVFVLVIABUGVLAAFUJVHARVIAFBUHAABUKVHAULSTUMVBAI
      AIBUNUOTUPS $.
  $}

  $( The class of all limit ordinals is a subclass of the class of all
     ordinals.  (Contributed by Scott Fenton, 11-Apr-2012.) $)
  limitssson $p |- Limits C_ On $=
    ( climits con0 cbigcup cfix cin c0 cdif df-limits difss inss1 sstri eqsstri
    csn ) ABCDZEZFMZGZBHQOBOPIBNJKL $.

  ${
    $d x y $.
    $( A quantifier-free definition of ` _om ` that does not depend on
       ~ ax-inf .  (Note: label was changed from ~ dfom5 to ~ dfom5b to prevent
       naming conflict.  NM, 12-Feb-2013.)  (Contributed by Scott Fenton,
       11-Apr-2012.) $)
    dfom5b $p |- _om = ( On i^i |^| Limits ) $=
      ( vx vy com con0 climits cint cin cv wcel wlim wi wal wa vex elint imbi1i
      ellimits albii bitr2i anbi2i elom elin 3bitr4i eqriv ) ACDEFZGZAHZDIZBHZJ
      ZUGUIIZKZBLZMUHUGUEIZMUGCIUGUFIUMUNUHUNUIEIZUKKZBLUMBUGEANOUPULBUOUJUKUIB
      NQPRSTBUGUAUGDUEUBUCUD $.
  $}

  ${
    $d A x y z $.  $d B x y z $.
    $( A condition for subset and composition with identity.  (Contributed by
       Scott Fenton, 13-Apr-2018.) $)
    sscoid $p |- ( A C_ ( _I o. B ) <-> ( Rel A /\ A C_ B ) ) $=
      ( vx vy vz cid wss wrel cv wcel wi wal wa wex wbr vex eleq1 df-br bitr4di
      wb ccom relco relss mpi cop wceq elrel weq brco ideq exbii breq2 equsexvw
      anbi1ci 3bitri a1i 3bitr4d exlimivv syl pm5.74da albidv 3bitr4g biadanii
      df-ss ) AFBUAZGZAHZABGZVFVEHVGFBUBAVEUCUDVGCIZAJZVIVEJZKZCLVJVIBJZKZCLVFV
      HVGVLVNCVGVJVKVMVGVJMVIDIZEIZUEZUFZENDNVKVMTZDEVIAUGVRVSDEVRVOVPVEOZVOVPB
      OZVKVMVTWATVRVTVOVIBOZVIVPFOZMZCNCEUHZWBMZCNWACVOVPFBDPEPZUIWDWFCWCWEWBVI
      VPWGUJUNUKWBWACEVIVPVOBULUMUOUPVRVKVQVEJVTVIVQVEQVOVPVERSVRVMVQBJWAVIVQBQ
      VOVPBRSUQURUSUTVACAVEVDCABVDVBVC $.
  $}

  ${
    $d F x y z $.
    $( Another potential definition of functionality.  Based on statements in
~ http://people.math.gatech.edu/~~belinfan/research/autoreas/otter/sum/fs/ .
       (Contributed by Scott Fenton, 30-Aug-2017.) $)
    dffun10 $p |- ( Fun F <-> F C_ ( _I o. ( _V \ ( ( _V \ _I ) o. F ) ) ) ) $=
      ( vx vy vz cv cop wcel wa weq wi wal cvv cid cdif ccom wss wn wbr wex vex
      wrel wfun impexp albii 19.21v opelco df-br brv brdif mpbiran equcom bitri
      ideq xchbinx anbi12i exbii exanali 3bitri opex eldif bitr4i imbi2i 2albii
      con2bii ssrel bitr4id pm5.32i dffun4 sscoid 3bitr4i ) AUAZBEZCEZFZAGZVLDE
      ZFAGZHCDIZJZDKZCKBKZHVKALLMNZAOZNZPZHAUBAMWDOPVKWAWEVKWAVOVNWDGZJZCKBKWEV
      TWGBCVTVOVQVRJZJZDKVOWHDKZJWGVSWIDVOVQVRUCUDVOWHDUEWJWFVOWJVNWCGZQZWFWKWJ
      WKVLVPARZVPVMWBRZHZDSVQVRQZHZDSWJQDVLVMWBABTCTZUFWOWQDWMVQWNWPVLVPAUGWNVP
      VMMRZVRWNVPVMLRWSQVPVMUHVPVMLMUIUJWSDCIVRVPVMWRUMDCUKULUNUOUPVQVRDUQURVDW
      FVNLGWLVLVMUSVNLWCUTUJVAVBURVCBCAWDVEVFVGBCDAVHAWDVIVJ $.
  $}

  ${
    $d F a x y z p q $.
    elfuns.1 $e |- F e. _V $.
    $( Membership in the class of all functions.  (Contributed by Scott Fenton,
       18-Feb-2013.) $)
    elfuns $p |- ( F e. Funs <-> Fun F ) $=
      ( vx vy vz vp vq va cv wcel wa weq cvv wbr wex wn bitrdi vex bitri 3bitri
      wrel cop wi wal c1st cdif c2nd ccom ctxp wfun cfuns wceq elrel ex anim12d
      cid adantrd pm4.71rd 19.41vvvv ee4anv anbi1i bitr2i 2exbidv excom13 excom
      exrot4 df-3an 2exbii opex eleq1 anbi1d breq2 anbi12d anbi2d breq1 br1steq
      w3a brtxp equcom brco br2ndeq exbii brv brdif mpbiran ideq notbii anbi12i
      equsexvw an12 ceqsex2v bitr3i opeq1 eleq1d exanali con2bid pm5.32i dffun4
      exnal cxp cpw cep ccnv cfix df-funs eleq2i eldif elpw df-rel bitr4i elfix
      wss wrex coep coepr rexbii r2ex 3bitr4ri ) AUAZCIZDIZUBZAJZXTEIZUBZAJZKZD
      ELZUCEUDZDUDZCUDZKXSFIZAJZGIZAJZKZYNYLUEMUPUFZUGUHZUIZNZKZGOFOZPZKZAUJAUK
      JZXSYKUUCXSUUBYKXSUUBYLYBULZYNHIZYDUBZULZKZUUAKZEOHOZDOZCOZGOFOZYKPZXSUUA
      UUNFGXSUUAUUFDOCOZUUIEOHOZKZUUAKZUUNXSUUAUUSXSYPUUSYTXSYMUUQYOUURXSYMUUQC
      DYLAUMUNXSYOUURHEYNAUMUNUOUQURUUNUUJEOHODOCOZUUAKUUTUUJUUADHECUSUVAUUSUUA
      UUFUUICDHEUTVAVBQVCUUOUUMFOGOZCOYJPZCOUUPUUMFGCVDUVBUVCCUVBUULGOFOZDOYIPZ
      DOUVCUULGFDVDUVDUVEDUVDUUKGOFOZEOHOUVFHOZEOZUVEUUKFGHEVFUVFHEVEUVHYGYHPZK
      ZEOUVEUVGUVJEUVGHCLZYCUUHAJZKZUVIKZKZHOUVJUVFUVOHUVFUUFUUIUUAVQZGOFOUVOUV
      PUUKFGUUFUUIUUAVGVHUUAYCYOKZYNYBYSNZKZUVOFGYBUUHXTYAVIUUGYDVIZUUFYPUVQYTU
      VRUUFYMYCYOYLYBAVJVKYLYBYNYSVLVMUUIUVSUVMUVKUVIKZKUVOUUIUVQUVMUVRUWAUUIYO
      UVLYCYNUUHAVJVNUUIUVRUUHYBYSNZUWAYNUUHYBYSVOUWBUUHXTUENZUUHYAYRNZKUWAUEYR
      UUHXTYAUVTCRDRZVRUWCUVKUWDUVIUWCCHLUVKUUGYDXTHRZERZVPCHVSSUWDUUHXTUGNZXTY
      AYQNZKZCOCELZUWIKZCOUVICUUHYAYQUGUVTUWEVTUWJUWLCUWHUWKUWIUUGYDXTUWFUWGWAV
      AWBUWIUVICEUWKUWIYDYAYQNZUVIXTYDYAYQVOUWMYDYAUPNZPZUVIUWMYDYAMNUWOYDYAWCY
      DYAMUPWDWEUWNYHUWNEDLYHYDYAUWEWFEDVSSWGSQWITWHSQVMUVMUVKUVIWJQWKWLWBUVNUV
      JHCUVKUVMYGUVIUVKUVLYFYCUVKUUHYEAUUGXTYDWMWNVNVKWISWBYGYHEWOSTWBYIDWSTWBY
      JCWSTQWPWQCDEAWRUUEAMMWTZXAZXBYSXBXCUHZUHZXDZUFZJAUWQJZAUWTJZPZKUUDUKUXAA
      XEXFAUWQUWTXGUXBXSUXDUUCUXBAUWPXLXSAUWPBXHAXIXJUXCUUBUXCAAUWSNZYTGAXMZFAX
      MZUUBAUWSBXKUXEAYLUWRNZFAXMUXGFAAUWRBBXNUXHUXFFAGAYLYSBFRXOXPSYTFGAAXQTWG
      WHTXR $.
  $}

  ${
    $d F f $.
    $( Closed form of ~ elfuns .  (Contributed by Scott Fenton, 2-May-2014.) $)
    elfunsg $p |- ( F e. V -> ( F e. Funs <-> Fun F ) ) $=
      ( vf cv cfuns wcel wfun eleq1 funeq vex elfuns vtoclbg ) CDZEFMGAEFAGCABM
      AEHMAIMCJKL $.
  $}

  ${
    $d A x $.  $d B x $.
    brsingle.1 $e |- A e. _V $.
    brsingle.2 $e |- B e. _V $.
    $( The binary relation form of the singleton function.  (Contributed by
       Scott Fenton, 4-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    brsingle $p |- ( A Singleton B <-> B = { A } ) $=
      ( vx cvv cxp csingle cid csn df-singleton wbr wcel brxp mpbir2an cv velsn
      wceq ideq bitr4i brtxpsd3 ) EABFFGZHIAJZCDKABUBLAFMBFMCDABFFNOEPZUCMUDARU
      DAILEAQUDACSTUA $.
  $}

  ${
    $d A x y $.
    $( Membership in the class of all singletons.  (Contributed by Scott
       Fenton, 19-Feb-2013.) $)
    elsingles $p |- ( A e. Singletons <-> E. x A = { x } ) $=
      ( vy csingles wcel cvv csn wceq wex elex vsnex eleq1 mpbiri exlimiv eqeq1
      cv exbidv csingle crn vex wbr df-singles eleq2i elrn exbii 3bitri vtoclbg
      brsingle pm5.21nii ) BDEZBFEZBAPZGZHZAIZBDJUNUKAUNUKUMFEAKBUMFLMNCPZDEZUP
      UMHZAIZUJUOCBFUPBDLUPBHURUNAUPBUMOQUQUPRSZEULUPRUAZAIUSDUTUPUBUCAUPRCTZUD
      VAURAULUPATVBUHUEUFUGUI $.
  $}

  ${
    $d x y z $.
    $( The singleton relationship is a function over the universe.
       (Contributed by Scott Fenton, 4-Apr-2014.)  (Revised by Mario Carneiro,
       19-Apr-2014.) $)
    fnsingle $p |- Singleton Fn _V $=
      ( vx vy vz csingle cvv wfn wfun cdm wceq wrel cv wbr wa weq wal mpbir vex
      ctxp brsingle mpbir2an wi cxp cep cid csymdif crn cdif difss df-singleton
      wss df-rel releqi csn eqtr3 syl2anb ax-gen gen2 dffun2 wcel eqv wex vsnex
      eqid breq2 spcev ax-mp eldm mpgbir df-fn ) DEFDGZDHZEIZVJDJZAKZBKZDLZVNCK
      ZDLZMBCNZUAZCOZBOAOVMEEUBZEUCRUDERUEUFZUGZJZWEWDWBUJWBWCUHWDUKPDWDUIULPWA
      ABVTCVPVOVNUMZIVQWFIVSVRVNVOAQZBQSVNVQWGCQSVOVQWFUNUOUPUQABCDURTVLVNVKUSZ
      AAVKUTWHVPBVAZVNWFDLZWIWJWFWFIWFVCVNWFWGAVBZSPVPWJBWFWKVOWFVNDVDVEVFBVNDW
      GVGPVHDEVIT $.
  $}

  ${
    $d A x $.
    $( The value of the singleton function.  (Contributed by Scott Fenton,
       4-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.)  (Revised by
       Scott Fenton, 13-Apr-2018.) $)
    fvsingle $p |- ( Singleton ` A ) = { A } $=
      ( vx cvv wcel csingle cfv csn wceq cv fveq2 sneq eqeq12d wbr vex brsingle
      eqid vsnex mpbir wfn c0 wb fnsingle fnbrfvb mp2an vtoclg wn biimpi eqtr4d
      fvprc snprc pm2.61i ) ACDZAEFZAGZHZBIZEFZUPGZHZUOBACUPAHUQUMURUNUPAEJUPAK
      LUSUPUREMZUTURURHURPUPURBNZBQORECSUPCDUSUTUAUBVACUPUREUCUDRUEULUFZUMTUNAE
      UIVBUNTHAUJUGUHUK $.
  $}

  ${
    $d x y $.
    $( Alternate definition of the class of all singletons.  (Contributed by
       Scott Fenton, 20-Nov-2013.)  (Revised by Mario Carneiro,
       19-Apr-2014.) $)
    dfsingles2 $p |- Singletons = { x | E. y x = { y } } $=
      ( cv csn wceq wex csingles elsingles eqabi ) ACZBCDEBFAGBJHI $.
  $}

  ${
    $d A x $.
    snelsingles.1 $e |- A e. _V $.
    $( A singleton is a member of the class of all singletons.  (Contributed by
       Scott Fenton, 19-Feb-2013.) $)
    snelsingles $p |- { A } e. Singletons $=
      ( vx csn csingles wcel cv wceq wex cvv isset eqcom exbii mpbi sneq eximii
      bitri elsingles mpbir ) ADZEFTCGZDHZCIAUAHZUBCAJFZUCCIZBUDUAAHZCIUECAKUFU
      CCUAALMQNAUAOPCTRS $.
  $}

  ${
    $d x y z w $.  $d ph y z w $.
    $( A definition of iota using minimal quantifiers.  (Contributed by Scott
       Fenton, 19-Feb-2013.) $)
    dfiota3 $p |- ( iota x ph ) = U. U. ( { { x | ph } } i^i Singletons ) $=
      ( vy vz vw cab cv csn wceq cuni csingles cin wex wcel ceqsexv bitri exbii
      wa weq eqtri cio df-iota wb eqabcb wel exdistr vex sneq vsnex eqeq1 eleq2
      eqeq2d anbi12d eqcom velsn equcom bitrdi an13 bitr3i excom eluniab mpgbir
      anbi12ci 3bitr4i df-sn dfsingles2 ineq12i inab 19.42v bicomi abbii unieqi
      eqtr4i ) ABUAABFZCGZHZIZCFZJVNHZKLZJZJABCUBVRWAVRDGZVNIZWBEGZHZIZRZEMZDFZ
      JZWAVRWJIVQVOWJNZUCCVQCWJUDCDUEZWGRZEMDMZWLWHRDMVQWKWLWGDEUFVQWMDMZEMZWNV
      QECSZVNWEIZRZEMWPWRVQEVOCUGWQWEVPVNWDVOUHULOWSWOEWSWFWCWLRZRZDMWOWTWSDWEE
      UIWFWTWEVNIZVOWENZRWSWFWCXBWLXCWBWEVNUJWBWEVOUKUMXBWRXCWQWEVNUNXCCESWQCWD
      UOCEUPPVCUQOXAWMDWFWCWLURQUSQUSWMEDUTPWHDVOVAVDVBVTWIVTWCDFZWFEMZDFZLZWIV
      SXDKXFDVNVEDEVFVGXGWCXERZDFWIWCXEDVHXHWHDWHXHWCWFEVIVJVKTTVLVMVLT $.
  $}

  ${
    $d F x $.  $d A x $.
    $( Another quantifier-free definition of function value.  (Contributed by
       Scott Fenton, 19-Feb-2013.) $)
    dffv5 $p |- ( F ` A ) = U. U. ( { ( F " { A } ) } i^i Singletons ) $=
      ( vx cfv cv csn cima wcel cio cab csingles cuni dffv3 dfiota3 abid2 sneqi
      cin ineq1i unieqi 3eqtri ) ABDCEBAFGZHZCIUBCJZFZKQZLZLUAFZKQZLZLCABMUBCNU
      FUIUEUHUDUGKUCUACUAOPRSST $.
  $}

  $( Express union of singleton in terms of ` if ` .  (Contributed by Scott
     Fenton, 27-Mar-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
  unisnif $p |- U. { A } = if ( A e. _V , A , (/) ) $=
    ( cvv wcel c0 cif csn cuni wceq iftrue unisng eqtr4d wn snprc biimpi unieqd
    iffalse uni0 eqtrdi pm2.61i eqcomi ) ABCZADEZAFZGZUAUBUDHUAUBAUDUAADIABJKUA
    LZUBDUDUAADPUEUDDGDUEUCDUEUCDHAMNOQRKST $.

  ${
    $d A x y $.  $d B x y $.  $d R x y $.
    brimage.1 $e |- A e. _V $.
    brimage.2 $e |- B e. _V $.
    $( Binary relation form of the Image functor.  (Contributed by Scott
       Fenton, 4-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    brimage $p |- ( A Image R B <-> B = ( R " A ) ) $=
      ( vx vy cvv cxp cimage cep ccnv ccom cima df-image wbr wcel cv wrex vex
      brxp mpbir2an brcnv rexbii coep elima 3bitr4ri brtxpsd3 ) FABHHIZCJKCLZMZ
      CANZDECOABUIPAHQBHQDEABHHUAUBFRZGRZUJPZGASUNUMCPZGASUMAUKPUMULQUOUPGAUMUN
      CFTZGTUCUDGUMAUJUQDUEGUMCAUQUFUGUH $.
  $}

  ${
    $d R x y $.  $d A x y $.  $d B x y $.
    $( Closed form of ~ brimage .  (Contributed by Scott Fenton, 4-Apr-2014.)
       (Revised by Mario Carneiro, 19-Apr-2014.) $)
    brimageg $p |- ( ( A e. V /\ B e. W ) ->
               ( A Image R B <-> B = ( R " A ) ) ) $=
      ( vx vy cv cimage wbr cima wb breq1 imaeq2 eqeq2d bibi12d breq2 eqeq1 vex
      wceq brimage vtocl2g ) FHZGHZCIZJZUDCUCKZTZLAUDUEJZUDCAKZTZLABUEJZBUJTZLF
      GABDEUCATZUFUIUHUKUCAUDUEMUNUGUJUDUCACNOPUDBTUIULUKUMUDBAUEQUDBUJRPUCUDCF
      SGSUAUB $.
  $}

  ${
    $d A x y z $.
    $( ` Image A ` is a function.  (Contributed by Scott Fenton, 27-Mar-2014.)
       (Revised by Mario Carneiro, 19-Apr-2014.) $)
    funimage $p |- Fun Image A $=
      ( vx vy vz cimage wfun wrel cv wbr wa weq wal cvv cep ctxp mpbir wceq vex
      wi brimage cxp ccnv ccom csymdif crn cdif wss df-rel df-image releqi cima
      difss eqtr3 syl2anb gen2 ax-gen dffun2 mpbir2an ) AEZFUSGZBHZCHZUSIZVADHZ
      USIZJCDKZSZDLCLZBLUTMMUAZMNONAUBUCMOUDUEZUFZGZVLVKVIUGVIVJULVKUHPUSVKAUIU
      JPVHBVGCDVCVBAVAUKZQVDVMQVFVEVAVBABRZCRTVAVDAVNDRTVBVDVMUMUNUOUPBCDUSUQUR
      $.
  $}

  ${
    $d R x y $.
    $( ` Image R ` is a function over the set-like portion of ` R ` .
       (Contributed by Scott Fenton, 4-Apr-2014.)  (Revised by Mario Carneiro,
       19-Apr-2014.) $)
    fnimage $p |- Image R Fn { x | ( R " x ) e. _V } $=
      ( cimage cima cvv wcel cab wfn wfun cdm wceq funimage wbr wex vex brimage
      vy cv eqvisset sylbi exlimiv eqid brimageg mpbiri breq2 spcegv mpd impbii
      wb mpan eldm weq imaeq2 eleq1d elab 3bitr4i eqriv df-fn mpbir2an ) BCZBAR
      ZDZEFZAGZHUTIUTJZVDKBLQVEVDQRZVAUTMZANZBVFDZEFZVFVEFVFVDFVHVJVGVJAVGVAVIK
      VJVFVABQOZAOPAVISTUAVJVFVIUTMZVHVJVLVIVIKZVIUBVFEFVJVLVMUIVKVFVIBEEUCUJUD
      VGVLAVIEVAVIVFUTUEUFUGUHAVFUTVKUKVCVJAVFVKAQULVBVIEVAVFBUMUNUOUPUQUTVDURU
      S $.
  $}

  ${
    $d R x y z $.
    $( The image functor in maps-to notation.  (Contributed by Scott Fenton,
       4-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    imageval $p |- Image R = ( x e. _V |-> ( R " x ) ) $=
      ( vy vz cimage cvv cv cima cmpt wfun wrel wbr wcel cdm breldm eleqtrdi wb
      vex wceq bitrid funimage funrel ax-mp mptrel cab fnimage fndmi crab dmmpt
      eqid rabab eqtri imaeq2 eleq1d elab brimage cfv fvmptg mpan eqeq1d funmpt
      eqcom wfn df-fn mpbir2an biimpri fnbrfvb sylancr bitr3d pm5.21nii eqbrriv
      sylbi ) CDBEZAFBAGZHZIZVMJVMKBUAVMUBUCAFVOUDCGZDGZVMLZVQVOFMZAUEZMZVQVRVP
      LZVSVQVMNWAVQVRVMCRZDRZOWAVMABUFUGPWCVQVPNZWAVQVRVPWDWEOWFVTAFUHWAAFVOVPV
      PUJZUIVTAUKULZPWBBVQHZFMZVSWCQVTWJAVQWDVNVQSVOWIFVNVQBUMZUNUOZVSVRWISZWJW
      CVQVRBWDWEUPWMWIVRSZWJWCVRWIVBWJVQVPUQZVRSZWNWCWJWOWIVRVQFMWJWOWISWDAVQVO
      WIFFVPWKWGURUSUTWJVPWAVCZWBWPWCQWQVPJWFWASAFVOVAWHVPWAVDVEWBWJWLVFWAVQVRV
      PVGVHVITTVLVJVK $.
  $}

  ${
    $d R x $.  $d A x $.
    $( Value of the image functor.  (Contributed by Scott Fenton, 4-Apr-2014.)
       (Revised by Mario Carneiro, 19-Apr-2014.) $)
    fvimage $p |- ( ( A e. V /\ ( R " A ) e. W ) ->
             ( Image R ` A ) = ( R " A ) ) $=
      ( vx wcel cvv cima cimage cfv wceq elex cv imaeq2 imageval fvmptg sylan )
      ACFAGFBAHZDFABIZJRKACLEABEMZHRGDSTABNEBOPQ $.
  $}

  ${
    $d A x y z $.  $d B x y z $.  $d C x y z $.
    brcart.1 $e |- A e. _V $.
    brcart.2 $e |- B e. _V $.
    brcart.3 $e |- C e. _V $.
    $( Binary relation form of the cartesian product operator.  (Contributed by
       Scott Fenton, 11-Apr-2014.)  (Revised by Mario Carneiro,
       19-Apr-2014.) $)
    brcart $p |- ( <. A , B >. Cart C <-> C = ( A X. B ) ) $=
      ( vx vy vz cop cvv cxp ccart cep wbr wcel cv wex wa epeli cpprod mpbir2an
      opex df-cart opelvv brxp w3a 3anass anbi12i anbi2i bitri 2exbii brpprod3b
      wceq vex elxp 3bitr4ri brtxpsd3 ) GABJZCKKLZKLZMNNUAZABLZABUCFUDUSCVAOUSU
      TPCKPABDEUEFUSCUTKUFUBGQZHQZIQZJUNZVEANOZVFBNOZUGZIRHRVGVEAPZVFBPZSZSZIRH
      RVDUSVBOVDVCPVJVNHIVJVGVHVISZSVNVGVHVIUHVOVMVGVHVKVIVLVEADTVFBETUIUJUKULH
      INNVDABGUODEUMHIVDABUPUQUR $.
  $}

  ${
    brdomain.1 $e |- A e. _V $.
    brdomain.2 $e |- B e. _V $.
    $( Binary relation form of the domain function.  (Contributed by Scott
       Fenton, 11-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    brdomain $p |- ( A Domain B <-> B = dom A ) $=
      ( c1st cvv cxp cres cimage wbr cima cdomain brimage df-domain breqi dfdm5
      wceq cdm eqeq2i 3bitr4i ) ABEFFGHZIZJBUAAKZQABLJBARZQABUACDMABLUBNOUDUCBA
      PST $.

    $( Binary relation form of the range function.  (Contributed by Scott
       Fenton, 11-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    brrange $p |- ( A Range B <-> B = ran A ) $=
      ( c2nd cvv cxp cres cimage wbr cima wceq crn brimage df-range breqi dfrn5
      crange eqeq2i 3bitr4i ) ABEFFGHZIZJBUAAKZLABRJBAMZLABUACDNABRUBOPUDUCBAQS
      T $.
  $}

  ${
    $d A a b $.  $d B a b $.
    $( Closed form of ~ brdomain .  (Contributed by Scott Fenton,
       2-May-2014.) $)
    brdomaing $p |- ( ( A e. V /\ B e. W ) ->
               ( A Domain B <-> B = dom A ) ) $=
      ( va vb cv cdomain wbr cdm wceq breq1 dmeq eqeq2d bibi12d breq2 eqeq1 vex
      wb brdomain vtocl2g ) EGZFGZHIZUCUBJZKZSAUCHIZUCAJZKZSABHIZBUHKZSEFABCDUB
      AKZUDUGUFUIUBAUCHLULUEUHUCUBAMNOUCBKUGUJUIUKUCBAHPUCBUHQOUBUCERFRTUA $.

    $( Closed form of ~ brrange .  (Contributed by Scott Fenton,
       3-May-2014.) $)
    brrangeg $p |- ( ( A e. V /\ B e. W ) ->
               ( A Range B <-> B = ran A ) ) $=
      ( va vb cv crange wbr crn wceq wb breq1 rneq eqeq2d bibi12d breq2 brrange
      eqeq1 vex vtocl2g ) EGZFGZHIZUCUBJZKZLAUCHIZUCAJZKZLABHIZBUHKZLEFABCDUBAK
      ZUDUGUFUIUBAUCHMULUEUHUCUBANOPUCBKUGUJUIUKUCBAHQUCBUHSPUBUCETFTRUA $.
  $}

  ${
    $d A a $.  $d a b $.  $d A b $.  $d a p $.  $d A p $.  $d a q $.  $d A q $.
    $d a x $.  $d A x $.  $d B a $.  $d B b $.  $d b p $.  $d B p $.  $d b q $.
    $d B q $.  $d b x $.  $d B x $.  $d C a $.  $d p q $.  $d p x $.  $d q x $.
    brimg.1 $e |- A e. _V $.
    brimg.2 $e |- B e. _V $.
    brimg.3 $e |- C e. _V $.
    $( Binary relation form of the ` Img ` function.  (Contributed by Scott
       Fenton, 12-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.)  (Proof
       shortened by Peter Mazsa, 2-Oct-2022.) $)
    brimg $p |- ( <. A , B >. Img C <-> C = ( A " B ) ) $=
      ( va vb vp vq cop wbr c2nd c1st wceq wa wex 3bitri wcel bitri vx cimg cvv
      ccom cres cimage ccart cima df-img breqi cv opex brco brcart anbi1i exbii
      cxp vex xpex breq1 ceqsexv brimage 19.42v anass an21 anbi2i 2exbii anbi2d
      excom wrex df-br risset brresi bitr3i elvv w3a ancom opeq1 breq1d anbi12d
      br1steq equcom br2ndeq anbi12i bitrdi pm5.32i df-3an 3bitr4i eqeq2d opeq2
      19.41vv ceqsex2v 3bitr3ri 3bitr4ri rexbii df-rex elima2 elxp bitr4i eqriv
      exrot3 eqeq2i ) ABKZCUBLXCCMNUDZNUCUCUQZUEZUEZUFZUGUDZLZABUQZCXHLZCABUHZO
      ZXCCUBXIUIUJXJXCGUKZUGLZXOCXHLZPZGQXOXKOZXQPZGQXLGXCCXHUGABULFUMXRXTGXPXS
      XQABXODEGURUNUOUPXQXLGXKABDEUSZXOXKCXHUTVARXLCXGXKUHZOXNXKCXGYAFVBYBXMCUA
      YBXMHUKZBSZYCUAUKZALZPZHQIUKZXOYCKZOZXOASZYDPZPZYHYEXGLZPZGQIQZHQZYEXMSYE
      YBSZYGYPHYDYKYIYEXGLZPZPZGQZYDYTGQZPYPYGYDYTGVCYPYJYDYKYNPZPZPZGQIQUUFIQZ
      GQUUBYOUUFIGYOYJYLYNPZPUUFYJYLYNVDUUHUUEYJYKYDYNVEVFTVGUUFIGVIUUGUUAGUUEU
      UAIYIXOYCULYJUUDYTYDYJYNYSYKYHYIYEXGUTVHVHVAUPRYFUUCYDYFYCYEKZASZYSGAVJZU
      UCYCYEAVKUUJXOUUIOZGAVJUUKGUUIAVLUULYSGAXOXESZXOYCNLZPZYIYEXDLZPZYIXFSZUU
      PPUULYSUUOUURUUPUUOXOYCXFLUURXEXOYCNHURZVMXOYCXFVKVNUOUUMUUNUUPPZPXOYHJUK
      ZKZOZJQIQZUUTPZUUQUULUUMUVDUUTIJXOVOUOUUMUUNUUPVDUVCUUTPZJQIQYHYCOZUVAYEO
      ZUVCVPZJQIQUVEUULUVFUVIIJUVCUVGUVHPZPUVJUVCPUVFUVIUVCUVJVQUVCUUTUVJUVCUUT
      UVBYCNLZUVBYCKZYEXDLZPUVJUVCUUNUVKUUPUVMXOUVBYCNUTUVCYIUVLYEXDXOUVBYCVRVS
      VTUVKUVGUVMUVHUVKYCYHOUVGYHUVAYCIURZJURZWAHIWBTUVMUVCXOYEMLZPZGQZYEUVAOZU
      VHUVMUVLXONLZUVPPZGQUVRGUVLYEMNUVBYCULUAURZUMUWAUVQGUVTUVCUVPUVBYCXOYHUVA
      ULZUUSWAUOUPTUVRUVBYEMLZUVSUVPUWDGUVBUWCXOUVBYEMUTVAYHUVAYEUVNUVOWCTUAJWB
      RWDWEWFUVGUVHUVCWGWHVGUVCUUTIJWKUVCXOYCUVAKZOUULIJYCYEUUSUWBUVGUVBUWEXOYH
      YCUVAVRWIUVHUWEUUIXOUVAYEYCWJWIWLWMWNXFYIYEXDUWBVMWHWOTYSGAWPRVFWNUPHYEAB
      UWBWQYRYHXKSZYNPZIQYOHQGQZIQZYQIYEXGXKUWBWQUWGUWHIUWGYMHQGQZYNPUWHUWFUWJY
      NGHYHABWRUOYMYNGHWKWSUPUWIYOIQHQGQYQYOIGHXAYOGHIXATRWNWTXBTR $.
  $}

  ${
    $d A a $.  $d a b $.  $d A b $.  $d a x $.  $d A x $.  $d A y $.  $d B a $.
    $d B b $.  $d b x $.  $d B x $.  $d B y $.  $d C x $.  $d C y $.  $d x y $.
    $d x z $.  $d y z $.  $d a z $.  $d A z $.  $d b z $.  $d B z $.
    brapply.1 $e |- A e. _V $.
    brapply.2 $e |- B e. _V $.
    brapply.3 $e |- C e. _V $.
    $( Binary relation form of the ` Apply ` function.  (Contributed by Scott
       Fenton, 12-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.)  (Proof
       shortened by Peter Mazsa, 2-Oct-2022.) $)
    brapply $p |- ( <. A , B >. Apply C <-> C = ( A ` B ) ) $=
      ( vx vy vz va vb csingles wceq wa wex wbr eqeq2d cbigcup cvv csingle cima
      csn cin cuni cop capply cfv snex inex1 unieq unieqd ceqsexv ccom cxp ctxp
      cv cep cres csymdif crn cdif cimg cid cpprod df-apply breqi opex brco vex
      w3a brpprod3a 3anrot ideq eqcom bitri brsingle biid 3anbi123i opeq1 opeq2
      2exbii ceqsex2v 3bitri anbi1i exbii breq1 brimg imaex sneq eqid wcel brxp
      anbi12i mpbir2an epel brresi elin 3bitr4ri brtxpsd3 ineq1 brbigcup vuniex
      anbi1ci dffv5 eqeq2i 3bitr4i ) GUPZABUBZUAZUBZLUCZMZCXGUDZUDZMZNZGOZCXKUD
      ZUDZMZABUEZCUFPZCBAUGZMXOXTGXKXJLXIUHZUIXLXNXSCXLXMXRXGXKUJUKQULYBYACRRUM
      ZSSUNZSUQUOUQLURZSUOUSUTVAZTVBUMZVCTVDZUMZUMZUMZPYAXGYLPZXGCYEPZNZGOXQYAC
      UFYMVEVFGYACYEYLABVGZFVHYPXPGYNXLYOXOYNYAHUPZYKPZYRXGYHPZNZHOYRXJMZXGYRLU
      CZMZNZHOXLHYAXGYHYKYQGVIZVHUUAUUEHYSUUBYTUUDYSYAIUPZYJPZUUGYRYIPZNZIOUUGA
      XHUEZMZUUINZIOZUUBIYAYRYIYJYQHVIZVHUUJUUMIUUHUULUUIUUHUUGJUPZKUPZUEZMZAUU
      PVCPZBUUQTPZVJZKOJOUUPAMZUUQXHMZUUSVJZKOJOUULJKVCTABUUGDEIVIVKUVBUVEJKUVB
      UUTUVAUUSVJUVEUUSUUTUVAVLUUTUVCUVAUVDUUSUUSUUTAUUPMUVCAUUPJVIVMAUUPVNVOBU
      UQEKVIVPUUSVQVRVOWAUUSUUGAUUQUEZMUULJKAXHDBUHZUVCUURUVFUUGUUPAUUQVSQUVDUV
      FUUKUUGUUQXHAVTQWBWCWDWEUUNUUKYRYIPZUUKXGVBPZXGYRTPZNZGOZUUBUUIUVHIUUKAXH
      VGZUUGUUKYRYIWFULGUUKYRTVBUVMUUOVHUVLXGXIMZYRXGUBZMZNZGOUUBUVKUVQGUVIUVNU
      VJUVPAXHXGDUVGUUFWGXGYRUUFUUOVPWMWEUVPUUBGXIAXHDWHUVNUVOXJYRXGXIWIQULVOWC
      WCIYRXGYFYHYGUUCUUOUUFYHWJYRXGYFPYRSWKXGSWKUUOUUFYRXGSSWLWNUUGLWKZUUGYRUQ
      PZNUUGYRWKZUVRNUUGYRYGPUUGUUCWKUVSUVTUVRHUUGWOXCLUUGYRUQUUOWPUUGYRLWQWRWS
      WMWEUUDXLHXJYDUUBUUCXKXGYRXJLWTQULWCYOXGYRRPZYRCRPZNZHOYRXMMZCYRUDZMZNZHO
      XOHXGCRRUUFFVHUWCUWGHUWAUWDUWBUWFUWAXMYRMUWDXGYRUUOXAXMYRVNVOUWBUWECMUWFY
      RCFXAUWECVNVOWMWEUWFXOHXMGXBUWDUWEXNCYRXMUJQULWCWMWEWCYCXSCBAXDXEXF $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d C x y $.
    brcup.1 $e |- A e. _V $.
    brcup.2 $e |- B e. _V $.
    brcup.3 $e |- C e. _V $.
    $( Binary relation form of the ` Cup ` function.  (Contributed by Scott
       Fenton, 14-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    brcup $p |- ( <. A , B >. Cup C <-> C = ( A u. B ) ) $=
      ( vx vy cvv cxp c1st ccnv cep ccom c2nd cun wbr wcel wa wex cop ccup opex
      df-cup opelvv brxp mpbir2an cv wceq wel epel brcnv br1steq bitri anbi12ci
      vex exbii brco clel3 3bitr4i br2ndeq orbi12i brun elun 3bitr4ri brtxpsd3
      wo ) GABUAZCIIJZIJZUBKLZMNZOLZMNZPZABPZABUCZFUDVHCVJQVHVIRCIRABDEUEFVHCVI
      IUFUGGUHZVHVLQZVRVHVNQZVGVRARZVRBRZVGVRVHVOQVRVPRVSWAVTWBVRHUHZMQZWCVHVKQ
      ZSZHTWCAUIZGHUJZSZHTVSWAWFWIHWDWHWEWGHVRUKZWEVHWCKQWGWCVHKHUPZVQULABWCDEU
      MUNUOUQHVRVHVKMGUPZVQURHVRADUSUTWDWCVHVMQZSZHTWCBUIZWHSZHTVTWBWNWPHWDWHWM
      WOWJWMVHWCOQWOWCVHOWKVQULABWCDEVAUNUOUQHVRVHVMMWLVQURHVRBEUSUTVBVRVHVLVNV
      CVRABVDVEVF $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d C x $.
    brcap.1 $e |- A e. _V $.
    brcap.2 $e |- B e. _V $.
    brcap.3 $e |- C e. _V $.
    $( Binary relation form of the ` Cap ` function.  (Contributed by Scott
       Fenton, 17-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    brcap $p |- ( <. A , B >. Cap C <-> C = ( A i^i B ) ) $=
      ( vx vy cvv cxp c1st ccnv cep ccom c2nd cin wbr wcel wa wex cop ccap opex
      df-cap opelvv brxp mpbir2an cv wceq wel epel brcnv br1steq bitri anbi12ci
      vex exbii brco clel3 3bitr4i br2ndeq anbi12i brin elin 3bitr4ri brtxpsd3
      ) GABUAZCIIJZIJZUBKLZMNZOLZMNZPZABPZABUCZFUDVGCVIQVGVHRCIRABDEUEFVGCVHIUF
      UGGUHZVGVKQZVQVGVMQZSVQARZVQBRZSVQVGVNQVQVORVRVTVSWAVQHUHZMQZWBVGVJQZSZHT
      WBAUIZGHUJZSZHTVRVTWEWHHWCWGWDWFHVQUKZWDVGWBKQWFWBVGKHUPZVPULABWBDEUMUNUO
      UQHVQVGVJMGUPZVPURHVQADUSUTWCWBVGVLQZSZHTWBBUIZWGSZHTVSWAWMWOHWCWGWLWNWIW
      LVGWBOQWNWBVGOWJVPULABWBDEVAUNUOUQHVQVGVLMWKVPURHVQBEUSUTVBVQVGVKVMVCVQAB
      VDVEVF $.
  $}

  ${
    $d A a b x $.  $d B a b x $.
    brsuccf.1 $e |- A e. _V $.
    brsuccf.2 $e |- B e. _V $.
    $( Lemma for unfolding different forms of the ` Succ ` function.
       (Contributed by Scott Fenton, 14-Apr-2014.)  (Revised by Mario Carneiro,
       19-Apr-2014.) $)
    lemsuccf $p |- ( E. x ( A ( _I (x) Singleton ) x /\ x Cup B ) <->
                     B = suc A ) $=
      ( va vb cv cop wceq ccup wbr wa wex cid csingle bitri w3a anbi1i vex ctxp
      csn cun csuc opex breq1 snex brcup brtxp2 3anass an32 ideq eqcom brsingle
      ceqsexv anbi12i ancom df-3an 3bitr4i 3bitri 2exbii 19.41vv opeq1 ceqsex2v
      eqeq2d anbi1d opeq2 3bitr3i exbii df-suc eqeq2i ) AHZBBUBZIZJZVLCKLZMZANZ
      CBVMUCZJZBVLOPUALZVPMZANCBUDZJVRVNCKLZVTVPWDAVNBVMUEVLVNCKUFUOBVMCDBUGZEU
      HQWBVQAWBVLFHZGHZIZJZBWFOLZBWGPLZRZGNFNZVPMZVQWAWMVPFGBVLOPDUISWLVPMZGNFN
      WFBJZWGVMJZWIVPMZRZGNFNWNVQWOWSFGWOWIWJWKMZMZVPMWRWTMZWSWLXAVPWIWJWKUJSWI
      WTVPUKWTWRMWPWQMZWRMXBWSWTXCWRWJWPWKWQWJBWFJWPBWFFTULBWFUMQBWGDGTUNUPSWRW
      TUQWPWQWRURUSUTVAWLVPFGVBWRVLBWGIZJZVPMVQFGBVMDWEWPWIXEVPWPWHXDVLWFBWGVCV
      EVFWQXEVOVPWQXDVNVLWGVMBVGVEVFVDVHQVIWCVSCBVJVKUS $.

    $( Binary relation form of the ` Succ ` function.  (Contributed by Scott
       Fenton, 14-Apr-2014.) $)
    brsuccf $p |- ( A Succ B <-> B = suc A ) $=
      ( vx csuccf wbr ccup cid csingle ctxp ccom cv wa csuc wceq df-succf breqi
      wex brco lemsuccf 3bitri ) ABFGABHIJKZLZGAEMZUCGUEBHGNESBAOPABFUDQREABHUC
      CDTEABCDUAUB $.
  $}

  ${
    $d m n x $.
    $( Alternate definition of Scott Fenton's version of ` Succ ` , cf.
       ~ df-sucmap .  (Contributed by Peter Mazsa, 6-Jan-2026.) $)
    dfsuccf2 $p |- Succ = { <. m , n >. | suc m = n } $=
      ( vx csuccf ccup cid csingle ctxp ccom cv wbr wa copab csuc wceq df-succf
      wex df-co vex lemsuccf eqcom bitri opabbii 3eqtri ) DEFGHZIAJZCJZUEKUGBJZ
      EKLCQZABMUFNZUHOZABMPABCEUERUIUKABUIUHUJOUKCUFUHASBSTUHUJUAUBUCUD $.
  $}

  ${
    $d A x y z $.  $d F x y z $.
    $( Lemma for ~ funpartfun .  Show membership in the restriction.
       (Contributed by Scott Fenton, 4-Dec-2017.) $)
    funpartlem $p |- (
    A e. dom ( ( Image F o. Singleton ) i^i ( _V X. Singletons ) ) <->
    E. x ( F " { A } ) = { x } ) $=
      ( vy vz csingle cvv csingles wcel csn cima cv wex c0 imaeq2d wbr wa exbii
      wceq 3bitri cimage ccom cxp cin cdm elex vsnid eleq2 mpbiri n0i wn biimpi
      snprc ima0 eqtrdi nsyl2 syl exlimiv eleq1 sneq eqeq1d exbidv eldm mpbiran
      brxp elsingles bitri anbi2i brin 19.42v 3bitr4i excom exancom vsnex breq2
      vex ceqsexv brco brsingle anbi1i breq1 brimage eqcom vtoclbg pm5.21nii )
      BCUAZFUBZGHUCZUDZUEZIZBGIZCBJZKZALZJZSZAMZBWJUFWQWLAWQWOWNIZWLWQWSWOWPIAU
      GWNWPWOUHUIWSWNNSWLWNWOUJWLUKZWNCNKNWTWMNCWTWMNSBUMULOCUNUOUPUQURDLZWJIZC
      XAJZKZWPSZAMZWKWRDBGXABWJUSXABSZXEWQAXGXDWNWPXGXCWMCXABUTOVAVBXBXAELZWIPZ
      EMZXAXHWGPZXHWPSZQZEMZAMZXFEXAWIDVPZVCXJXMAMZEMXOXIXQEXKXAXHWHPZQXKXLAMZQ
      XIXQXRXSXKXRXHHIZXSXRXAGIXTXPXAXHGHVEVDAXHVFVGVHXAXHWGWHVIXKXLAVJVKRXMEAV
      LVGXNXEAXNXLXKQEMXAWPWGPZXEXKXLEVMXKYAEWPAVNZXHWPXAWGVOVQYAXAXHFPZXHWPWFP
      ZQZEMXHXCSZYDQZEMZXEEXAWPWFFXPYBVRYEYGEYCYFYDXAXHXPEVPVSVTRYHXCWPWFPZWPXD
      SXEYDYIEXCDVNZXHXCWPWFWAVQXCWPCYJYBWBWPXDWCTTTRTWDWE $.
  $}

  ${
    $d F x y z w $.
    $( The functional part of ` F ` is a function.  (Contributed by Scott
       Fenton, 16-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.)  (Proof
       shortened by Peter Mazsa, 2-Oct-2022.) $)
    funpartfun $p |- Fun Funpart F $=
      ( vx vy vz vw wfun cv wbr wa wceq wal wcel vex brresi csn bitri cop df-br
      wi anbi12i cfunpart cimage csingle ccom cvv csingles cxp cres wrel relres
      cin cdm simprbi cima funpartlem anbi1i elimasn bitr4i eleq2 anbi12d velsn
      wex equtr2 syl2anb biimtrdi biimtrid impl sylanb sylan2 ax-gen df-funpart
      exlimiv gen2 funeqi dffun2 mpbir2an ) AUAZFZAAUBUCUDUEUFUGUKULZUHZUIZBGZC
      GZVTHZWBDGZVTHZIWCWEJZSZDKCKZBKZAVSUJWIBWHCDWFWDWBWEAHZWGWFWBVSLZWKVSWBWE
      ADMZNUMWDAWBOUNZEGZOZJZEVBZWBWCAHZIZWKWGWDWLWSIWTVSWBWCACMZNWLWRWSEWBAUOU
      PPWRWSWKWGWQWSWKIZWGSEXBWCWNLZWEWNLZIZWQWGXBWBWCQALZWBWEQALZIXEWSXFWKXGWB
      WCARWBWEARTXCXFXDXGAWBWCBMZXAUQAWBWEXHWMUQTURWQXEWCWPLZWEWPLZIWGWQXCXIXDX
      JWNWPWCUSWNWPWEUSUTXIWCWOJWEWOJWGXJCWOVADWOVACDEVCVDVEVFVLVGVHVIVMVJVRVTF
      WAWJIVQVTAVKVNBCDVTVOPVP $.
  $}

  $( The functional part of ` F ` is a subset of ` F ` .  (Contributed by Scott
     Fenton, 17-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
  funpartss $p |- Funpart F C_ F $=
    ( cfunpart cimage csingle ccom cvv csingles cxp cin cres df-funpart eqsstri
    cdm resss ) ABAACDEFGHIMZJAAKAONL $.

  ${
    $d A x $.  $d F x $.
    $( The function value of the functional part is identical to the original
       functional value.  (Contributed by Scott Fenton, 17-Apr-2014.)  (Revised
       by Mario Carneiro, 19-Apr-2014.) $)
    funpartfv $p |- ( Funpart F ` A ) = ( F ` A ) $=
      ( vx cfunpart cfv cimage csingle ccom cvv csingles cxp cin cdm wcel wn c0
      wceq weu csn pm2.61i cres df-funpart fveq1i fvres nfvres wi cv funpartlem
      wbr cima wex eusn bitr4i cop wb elimasng elvd df-br bitr4di eubidv bitrid
      notbid tz6.12-2 biimtrdi fvprc a1d eqtr4d eqtri ) ABDZEABBFGHIJKLMZUAZEZA
      BEZAVIVKBUBUCAVJNZVLVMQAVJBUDVNOZVLPVMAVJBUEAINZVOVMPQZUFVPVOACUGZBUIZCRZ
      OVQVPVNVTVNVRBASUJZNZCRZVPVTVNWAVRSQCUKWCCABUHCWAULUMVPWBVSCVPWBAVRUNBNZV
      SVPWBWDUOCBAVRIIUPUQAVRBURUSUTVAVBCABVCVDVPOVQVOABVEVFTVGTVH $.
  $}

  $( The full functional part of ` F ` is a function over ` _V ` .
     (Contributed by Scott Fenton, 17-Apr-2014.)  (Revised by Mario Carneiro,
     19-Apr-2014.) $)
  fullfunfnv $p |- FullFun F Fn _V $=
    ( cfullfn cvv wfn cfunpart cdm cdif c0 csn cxp cun cin wceq wfun funpartfun
    wa funfn mpbi wf 0ex fconst ffn ax-mp pm3.2i disjdif fnun df-fullfun fneq1i
    mp2an unvdif eqcomi fneq2i bitri mpbir ) ABZCDZAEZCUQFZGZHIZJZKZURUSKZDZUQU
    RDZVAUSDZPURUSLHMVDVEVFUQNVEAOUQQRUSUTVASVFUSHTUAUSUTVAUBUCUDURCUEURUSUQVAU
    FUIUPVBCDVDCUOVBAUGUHCVCVBVCCURUJUKULUMUN $.

  ${
    $d F x $.  $d A x $.
    $( The function value of the full function of ` F ` agrees with ` F ` .
       (Contributed by Scott Fenton, 17-Apr-2014.)  (Revised by Mario Carneiro,
       19-Apr-2014.) $)
    fullfunfv $p |- ( FullFun F ` A ) = ( F ` A ) $=
      ( vx cvv wcel cfullfn cfv wceq cv fveq2 c0 wfn wa 0ex mp3an12 mpan eqtr4d
      wn pm2.61i fvprc eqeq12d cfunpart cdm cdif csn cxp cun df-fullfun disjdif
      fveq1i cin wfun funpartfun funfn mpbi wf fconst ffn ax-mp fvun1 vex eldif
      mpbiran fvun2 fvconst2 eqtrd sylbir ndmfv funpartfv 3eqtri vtoclg ) ADEZA
      BFZGZABGZHZCIZVMGZVQBGZHVPCADVQAHVRVNVSVOVQAVMJVQABJUAVRVQBUBZDVTUCZUDZKU
      EZUFZUGZGZVQVTGZVSVQVMWEBUHUJVQWAEZWFWGHZWAWBUKKHZWHWIWADUIZVTWALZWDWBLZW
      JWHMWIVTULWLBUMVTUNUOZWBWCWDUPWMWBKNUQWBWCWDURUSZWAWBVTWDVQUTOPWHRZWFKWGW
      PVQWBEZWFKHWQVQDEWPCVAVQDWAVBVCWQWFVQWDGZKWJWQWFWRHZWKWLWMWJWQMWSWNWOWAWB
      VTWDVQVDOPWBKVQNVEVFVGVQVTVHQSVQBVIVJVKVLRVNKVOAVMTABTQS $.
  $}

  ${
    brfullfun.1 $e |- A e. _V $.
    brfullfun.2 $e |- B e. _V $.
    $( A binary relation form condition for the full function.  (Contributed by
       Scott Fenton, 17-Apr-2014.)  (Revised by Mario Carneiro,
       19-Apr-2014.) $)
    brfullfun $p |- ( A FullFun F B <-> B = ( F ` A ) ) $=
      ( cfullfn cfv wceq wbr eqcom cvv wfn wcel wb fullfunfnv fnbrfvb fullfunfv
      mp2an eqeq2i 3bitr3i ) ACFZGZBHZBUBHABUAIZBACGZHUBBJUAKLAKMUCUDNCODKABUAP
      RUBUEBACQST $.
  $}

  ${
    $d A a b x $.  $d B a b x $.  $d C x $.
    brrestrict.1 $e |- A e. _V $.
    brrestrict.2 $e |- B e. _V $.
    brrestrict.3 $e |- C e. _V $.
    $( Binary relation form of the ` Restrict ` function.  (Contributed by
       Scott Fenton, 17-Apr-2014.)  (Revised by Mario Carneiro,
       19-Apr-2014.) $)
    brrestrict $p |- ( <. A , B >. Restrict C <-> C = ( A |` B ) ) $=
      ( vx va vb cop ccap c1st ccart crange wbr wceq wa wex w3a bitri c2nd ccom
      ctxp crn cxp cin crestrict cres cv opex brtxp2 3anrot br1steq vex br2ndeq
      brco anbi1i exbii breq1 ceqsexv brrange 3bitri biid 3anbi123i 2exbii rnex
      opeq1 eqeq2d opeq2 ceqsex2v brcart brcap df-restrict breqi dfres3 3bitr4i
      xpex eqeq2i ) ABJZCKLMUANLUBZUCZUBZUCZUBZOZCABAUDZUEZUFZPZVSCUGOCABUHZPWE
      GUIZAWGJZPZWKCKOZQZGRZWLCKOZWIWEVSWKWCOZWNQZGRWPGVSCKWCABUJZFUPWSWOGWRWMW
      NWRWKHUIZIUIZJZPZVSXALOZVSXBWBOZSZIRHRXAAPZXBWGPZXDSZIRHRWMHIVSWKLWBWTUKX
      GXJHIXGXEXFXDSXJXDXEXFULXEXHXFXIXDXDABXADEUMXFVSWKWAOZWKXBMOZQZGRZBWFJZXB
      MOZXIGVSXBMWAWTIUNZUPXNWKXOPZXLQZGRXPXMXSGXKXRXLXKXDVSXAUAOZVSXBVTOZSZIRH
      RXABPZXBWFPZXDSZIRHRXRHIVSWKUAVTWTUKYBYEHIYBXTYAXDSYEXDXTYAULXTYCYAYDXDXD
      ABXADEUOYAVSWKLOZWKXBNOZQZGRZAXBNOZYDGVSXBNLWTXQUPYIWKAPZYGQZGRYJYHYLGYFY
      KYGABWKDEUMUQURYGYJGADWKAXBNUSUTTAXBDXQVAVBXDVCZVDTVEXDWKBXBJZPXRHIBWFEAD
      VFZYCXCYNWKXABXBVGVHYDYNXOWKXBWFBVIVHVJVBUQURXLXPGXOBWFUJWKXOXBMUSUTTBWFX
      BEYOXQVKVBYMVDTVEXDWKAXBJZPWMHIAWGDBWFEYOVQZXHXCYPWKXAAXBVGVHXIYPWLWKXBWG
      AVIVHVJVBUQURTWNWQGWLAWGUJWKWLCKUSUTAWGCDYQFVLVBVSCUGWDVMVNWJWHCABVOVRVP
      $.
  $}

  ${
    $d F f x y $.
    $( A quantifier-free definition of ` recs ` .  (Contributed by Scott
       Fenton, 17-Jul-2020.) $)
    dfrecs2 $p |- recs ( F ) = U. ( ( Funs i^i ( `' Domain " On ) ) \
         dom ( ( `' _E o. Domain ) \
         Fix ( `' Apply o. ( FullFun F o. Restrict ) ) ) ) $=
      ( vf vx vy cv wceq wa con0 wrex cfuns cdomain wcel wn wex wbr bitri exbii
      anbi1i ceqsexv 3bitri crecs wfn cfv cres wral cab cuni ccnv cima cin ccom
      cep capply cfullfn crestrict cfix cdif cdm dfrecs3 wfun elin elfuns brcnv
      vex brdomain rexbii elima risset 3bitr4i eldm brdif brco dmex breq1 epeli
      anbi12i df-br opex elfix ancom brapply fvex breq2 brrestrict resex notbii
      brfullfun df-rex rexnal 3bitr2ri con1bii anass eleq1 raleq anbi12d anbi2d
      cop df-fn eqcom anbi2i an12 3bitr3ri 3bitr2i eldif eqabi unieqi eqtr4i )
      AUABEZCEZUBZDEZXHUCZXHXKUDZAUCFZDXIUEZGZCHIZBUFZUGJKUHZHUIZUJZULUHZKUKZUM
      UHZAUNZUOUKZUKZUPZUQZURZUQZUGCDBAUSYKXRXQBYKXHYALZXHYJLZMZGZXIHLZXPGZCNZX
      HYKLXQYOXHUTZXHURZHLZXNDYTUEZGZGZXIYTFZYSYPXOGZGZGZCNYRYOYSUUAGZUUBGUUDYL
      UUIYNUUBYLXHJLZXHXTLZGUUIXHJXTVAUUJYSUUKUUAXHBVDZVBXIXHXSOZCHIUUECHIUUKUU
      AUUMUUECHUUMXHXIKOZUUEXIXHKCVDZUULVCXHXIUULUUOVEZPVFCXHXSHUULVGCYTHVHVIVP
      PUUBYMYMXKYTLZXNMZGZDNZUURDYTIUUBMYMXHXKYIOZDNUUTDXHYIUULVJUVAUUSDUVAXHXK
      YCOZXHXKYHOZMZGUUSXHXKYCYHVKUVBUUQUVDUURUVBUUNXIXKYBOZGZCNZYTXKYBOZUUQCXH
      XKYBKUULDVDZVLUVGUUEUVEGZCNUVHUVFUVJCUUNUUEUVEUUPRQUVEUVHCYTXHUULVMZXIYTX
      KYBVNSPUVHXKYTULOUUQYTXKULUVKUVIVCXKYTUVKVOPTUVCXNUVCXHXKWQZYHLUVLUVLYGOZ
      XNXHXKYHVQUVLYGXHXKVRZVSUVMUVLXIYFOZXIUVLYDOZGZCNZUVLXLYFOZXNCUVLUVLYDYFU
      VNUVNVLUVRXIXLFZUVOGZCNUVSUVQUWACUVQUVPUVOGUWAUVOUVPVTUVPUVTUVOUVPUVLXIUM
      OUVTXIUVLUMUUOUVNVCXHXKXIUULUVIUUOWAPRPQUVOUVSCXLXKXHWBZXIXLUVLYFWCSPUVSU
      VLXIUOOZXIXLYEOZGZCNZXMXLYEOZXNCUVLXLYEUOUVNUWBVLUWFXIXMFZUWDGZCNUWGUWEUW
      ICUWCUWHUWDXHXKXIUULUVIUUOWDRQUWDUWGCXMXHXKUULWEZXIXMXLYEVNSPXMXLAUWJUWBW
      GTTTWFVPPQPUURDYTWHXNDYTWIWJWKVPYSUUAUUBWLPUUGUUDCYTUVKUUEUUFUUCYSUUEYPUU
      AXOUUBXIYTHWMXNDXIYTWNWOWPSUUHYQCXJUUFGUUEYSGZUUFGYQUUHXJUWKUUFXJYSYTXIFZ
      GYSUUEGUWKXHXIWRUWLUUEYSYTXIWSWTYSUUEVTTRXJYPXOXAUUEYSUUFWLXBQXCXHYAYJXDX
      PCHWHVIXEXFXG $.
  $}

  ${
    $d A a b f x y z $.  $d F a b f x y z $.
    $( A quantifier-free definition of the recursive definition generator.
       (Contributed by Scott Fenton, 17-Apr-2014.)  (Revised by Mario Carneiro,
       19-Apr-2014.)  (Proof shortened by Peter Mazsa, 2-Oct-2022.) $)
    dfrdg4 $p |- rec ( F , A ) = U.
       ( ( Funs i^i ( `' Domain " On ) ) \
         dom ( ( `' _E o. Domain ) \
         Fix ( `' Apply o.
               ( ( ( _V X. { (/) } ) X. { U. { A } } ) u.
                 ( ( ( Bigcup o. Img ) |` ( _V X. Limits ) ) u.
                   ( ( FullFun F o. ( Apply o. pprod ( _I , Bigcup ) ) ) |`
                     ( _V X. ran Succ ) ) ) ) ) ) ) $=
      ( vx vy vz va vb c0 wceq cvv wcel cuni wa con0 capply wex 3bitri bitri wn
      wbr vf crdg cv wfn cfv cif wlim cima wral wrex cab cfuns cdomain ccnv cin
      cep ccom csn cxp cbigcup cimg climits cres cfullfn cid cpprod csuccf cfix
      crn cun cdif cdm dfrdg3 wfun an12 df-fn ancom eqcom anbi1i anass vex dmex
      exbii eleq1 raleq anbi12d anbi2d ceqsexv df-rex eldif elin elfuns anbi12i
      brcnv wi brco breq1 wb w3a cop wo brun opelxp mpbiran velsn opex brbigcup
      brresi unieq eqeq2d brapply fvex orbi12i limeq mtbiri intnanrd wne mpbiri
      neneqd syl iftrue biimprd adantld biimpd anc2li orc syl6 impbid rexlimivw
      orel2 orel1 fveq2d ifbieq2d 3syld olcd con2i adantl bitrid exbidv bitr4di
      elima brdomain anbi1ci wal brdif epeli onelon 3adant1 csuc ellimits brimg
      brxp imaex eqeq1d elrn brpprod3a 3anrot ideq equcom biid 3anbi123i 2exbii
      brsuccf vuniex opeq1 opeq2 ceqsex2v brfullfun fveq2 w3o onzsl nlim0 neeq2
      nsuceq0 nexdv ioran sylanbrc unisnif eqtr4di syld neeq1 nlimsucg elv neii
      necomd iffalsei iffalse mp2b eqtri eqeq1 3eqtr4a rexex olc syl6an exlimiv
      iffalsed eqtrd 3jaoi sylbi a1i biancomd df-br elfix eqvinc 3bitr4g notbid
      3expia pm5.32d annim bitrdi exnal bitr2di con1bid df-ral pm5.32i 3bitr4ri
      eldm eqabi unieqi eqtr4i ) BAUBUAUCZCUCZUDZDUCZUYAUEZUYDHIZAJKAHUFZUYDUGZ
      UYAUYDUHZLZUYDLZUYAUEZBUEZUFZUFZIZDUYBUIZMZCNUJZUAUKZLULUMUNZNUHZUOZUPUNZ
      UMUQZOUNZJHURZUSZAURLZURZUSZUTVAUQZJVBUSZVCZBVDZOVEUTVFZUQZUQZJVGVIZUSZVC
      ZVJZVJZUQZVHZVKZVLZVKZLCDUABAVMVVHUYTUYSUAVVHUYBNKZUYRMZCPZUYAVNZUYAVLZNK
      ZUYPDVVMUIZMZMZUYSUYAVVHKZVVKUYBVVMIZVVLVVIUYQMZMZMZCPVVQVVJVWBCVVJUYCVVT
      MVVSVVLMZVVTMVWBVVIUYCUYQVOUYCVWCVVTUYCVVLVVMUYBIZMVWDVVLMVWCUYAUYBVPVVLV
      WDVQVWDVVSVVLVVMUYBVRVSQVSVVSVVLVVTVTQWCVWAVVQCVVMUYAUAWAZWBZVVSVVTVVPVVL
      VVSVVIVVNUYQVVOUYBVVMNWDZUYPDUYBVVMWEWFWGWHRUYRCNWIVVRUYAVUCKZUYAVVGKZSZM
      VVLVVNMZVWJMZVVQUYAVUCVVGWJVWHVWKVWJVWHUYAULKZUYAVUBKZMVWKUYAULVUBWKVWMVV
      LVWNVVNUYAVWEWLVWNUYBUYAVUATZCNUJVVIVWOMZCPZVVNCUYAVUANVWEUUAVWOCNWIVWQVV
      SVVIMZCPVVNVWPVWRCVWOVVSVVIVWOUYAUYBUMTZVVSUYBUYAUMCWAZVWEWNUYAUYBVWEVWTU
      UBZRUUCWCVVIVVNCVVMVWFVWGWHRQWMRVSVWLVWKVVOMVVQVWKVWJVVOVWKVWJUYDVVMKZUYP
      WOZDUUDZVVOVWKVXDVWIVWKVXDSZUYAUYDVVFTZDPZVWIVWKVXGVXCSZDPVXEVWKVXFVXHDVX
      FVXBUYAUYDVVETZSZMZVWKVXHVXFUYAUYDVUETZVXJMVXKUYAUYDVUEVVEUUEVXLVXBVXJVXL
      VWSUYBUYDVUDTZMZCPZVVMUYDVUDTZVXBCUYAUYDVUDUMVWEDWAZWPVXOVVSVXMMZCPVXPVXN
      VXRCVWSVVSVXMVXAVSWCVXMVXPCVVMVWFUYBVVMUYDVUDWQWHRVXPUYDVVMUPTVXBVVMUYDUP
      VWFVXQWNUYDVVMVWFUUFRQVSRVWKVXKVXBUYPSZMVXHVWKVXBVXJVXSVVLVVNVXBVXJVXSWRV
      VLVVNVXBWSZVXIUYPVXTUYAUYDWTZUYBVVCTZUYBVYAVUFTZMZCPZUYBUYEIZUYBUYOIZMZCP
      VXIUYPVXTVYDVYHCVXTVYDVYFVYGVXTVYBVYGVYCVYFVXTUYDNKZVYBVYGWRVVNVXBVYIVVLV
      VMUYDUUGUUHVYBUYFUYBVUIIZMZUYHUYBUYJIZMZUYDEUCZUUIZIZEPZUYBUYMIZMZXAZXAZV
      YIVYGVYBVYAUYBVUKTZVYAUYBVVBTZXAWUAVYAUYBVUKVVBXBWUBVYKWUCVYTWUBVYAVUHKZU
      YBVUJKZMVYKVYAUYBVUHVUJUULWUDUYFWUEVYJWUDUYDVUGKZUYFWUDUYAJKZWUFVWEUYAUYD
      JVUGXCXDDHXERCVUIXEWMRWUCVYAUYBVUNTZVYAUYBVVATZXAVYTVYAUYBVUNVVAXBWUHVYMW
      UIVYSWUHVYAVUMKZVYAUYBVULTZMVYMVUMVYAUYBVULVWTXHWUJUYHWUKVYLWUJUYDVBKZUYH
      WUJWUGWULVWEUYAUYDJVBXCXDUYDVXQUUJRWUKVYAVYNVATZVYNUYBUTTZMZEPVYNUYIIZVYN
      LZUYBIZMZEPZVYLEVYAUYBUTVAUYAUYDXFZVWTWPWUOWUSEWUMWUPWUNWURUYAUYDVYNVWEVX
      QEWAZUUKVYNUYBVWTXGWMWCWUTUYJUYBIZVYLWURWVCEUYIUYAUYDVWEUUMWUPWUQUYJUYBVY
      NUYIXIUUNWHUYJUYBVRRQWMRWUIVYAVUTKZVYAUYBVURTZMVYSVUTVYAUYBVURVWTXHWVDVYQ
      WVEVYRWVDUYDVUSKZVYNUYDVGTZEPVYQWVDWUGWVFVWEUYAUYDJVUSXCXDEUYDVGVXQUUOWVG
      VYPEVYNUYDWVBVXQUVCWCQWVEVYAFUCZVUQTZWVHUYBVUOTZMZFPWVHUYLIZUYBWVHBUEZIZM
      ZFPVYRFVYAUYBVUOVUQWVAVWTWPWVKWVOFWVIWVLWVJWVNWVIVYAVYNVUPTZVYNWVHOTZMZEP
      VYNUYAUYKWTZIZWVQMZEPZWVLEVYAWVHOVUPWVAFWAZWPWVRWWAEWVPWVTWVQWVPVYNWVHGUC
      ZWTZIZUYAWVHVETZUYDWWDUTTZWSZGPFPWVHUYAIZWWDUYKIZWWFWSZGPFPWVTFGVEUTUYAUY
      DVYNVWEVXQWVBUUPWWIWWLFGWWIWWGWWHWWFWSWWLWWFWWGWWHUUQWWGWWJWWHWWKWWFWWFWW
      GUYAWVHIWWJUYAWVHWWCUURUAFUUSRWWHUYKWWDIWWKUYDWWDGWAXGUYKWWDVRRWWFUUTUVAR
      UVBWWFVYNUYAWWDWTZIWVTFGUYAUYKVWEDUVDZWWJWWEWWMVYNWVHUYAWWDUVEXJWWKWWMWVS
      VYNWWDUYKUYAUVFXJUVGQVSWCWWBWVSWVHOTZWVLWVQWWOEWVSUYAUYKXFVYNWVSWVHOWQWHU
      YAUYKWVHVWEWWNWWCXKRQWVHUYBBWWCVWTUVHWMWCWVNVYRFUYLUYKUYAXLWVLWVMUYMUYBWV
      HUYLBUVIXJWHQWMRXMRXMRVYIUYFVYPENUJZUYDJKZUYHMZUVJWUAVYGWRZEUYDUVKUYFWWSW
      WPWWRUYFWUAVYGUYFWUAVYKVYGUYFVYTSZWUAVYKWOUYFVYMSZVYSSZWWTUYFUYHVYLUYFUYH
      HUGUVLUYDHXNXOZXPUYFVYQVYRUYFVYPEUYFUYDVYOUYFVYOUYDUYFVYOUYDXQVYOHXQZVYNU
      VNZUYDHVYOUVMXRUWEXSUVOXPVYMVYSUVPUVQVYTVYKYJXTUYFVYJVYGUYFUYFVYGVYJUYFUY
      OVUIUYBUYFUYOUYGVUIUYFUYGUYNYAAUVRUVSXJZYBYCUVTUYFVYGVYKWUAUYFVYGVYJUYFVY
      GVYJWXFYDYEVYKVYTYFYGYHWWPWUAVYGWWPWUAVYTVYSVYGWWPVYKSZWUAVYTWOZVYPWXGENV
      YPUYFVYJVYPUYDHVYPUYDHXQWXDWXEUYDVYOHUWAXRXSXPYIVYKVYTYKZXTWWPWXAVYTVYSWO
      WWPUYHVYLVYPUYHSZENVYPUYHVYOUGZWXKSZEVYNJUWBZUWCUYDVYOXNZXOZYIXPVYMVYSYKX
      TWWPVYRVYGVYQWWPVYGVYRWWPUYOUYMUYBVYPUYOUYMIENVYPVYOHIZUYGWXKUYJVYOLZUYAU
      EZBUEZUFZUFZWXSUYOUYMWYAWXTWXSWXPUYGWXTVYOHWXEUWDUWFVYNJKWXLWXTWXSIWVBWXM
      WXKUYJWXSUWGUWHUWIVYPUYFWXPUYNWXTUYGUYDVYOHUWJVYPUYHWXKUYMWXSUYJWXNVYPUYL
      WXRBVYPUYKWXQUYAUYDVYOXIYLYLZYMYMWYBUWKYIXJZYBYCYNWWPVYQVYGVYRWUAVYPENUWL
      WWPVYGVYRWYCYDVYSVYTVYKVYSVYMUWMYOUWNYHWWRWUAVYGUYHWUAVYGWOWWQUYHWUAVYTVY
      MVYGUYHWXGWXHUYHUYFVYJUYFUYHWXCYPZXPWXIXTUYHWXBVYTVYMWOUYHVYQVYRVYQUYHVYP
      WXJEWXOUWOYPXPVYSVYMYJXTUYHVYLVYGUYHUYHVYGVYLUYHUYOUYJUYBUYHUYOUYNUYJUYHU
      YFUYGUYNWYDUWPUYHUYJUYMYAUWQXJZYBYCYNYQUYHVYGWUAWOWWQUYHVYGVYMWUAUYHVYGVY
      LUYHVYGVYLWYEYDYEVYMVYTVYKVYMVYSYFYOYGYQYHUWRUWSYRXTVYCVYFWRVXTVYCVYAUYBO
      TVYFUYBVYAOVWTWVAWNUYAUYDUYBVWEVXQVWTXKRUWTWFUXAYSVXIVYAVVEKVYAVYAVVDTVYE
      UYAUYDVVEUXBVYAVVDWVAUXCCVYAVYAVUFVVCWVAWVAWPQCUYEUYOUYDUYAXLUXDUXEUXFUXG
      UXHVXBUYPUXIUXJYRYSVXCDUXKUXLDUYAVVFVWEUXQYTUXMUYPDVVMUXNYTUXOVVLVVNVVOVT
      RQUXPUXRUXSUXT $.
  $}

  ${
    $d A x y $.
    $( Quantifier-free definition of class intersection.  (Contributed by Scott
       Fenton, 13-Apr-2018.) $)
    dfint3 $p |- |^| A = ( _V \ ( `' ( _V \ _E ) " A ) ) $=
      ( vx vy cint wel wral cab cvv cep cdif ccnv cima dfint2 cv wbr wn mpbiran
      wcel vex bitr2i wrex ralnex brcnv brdif con1bii epel ralbii eldif xchbinx
      brv elima 3bitr4ri eqabi eqtr4i ) ADBCEZCAFZBGHHIJZKZALZJZBCAMUPBUTCNZBNZ
      UROZPZCAFVCCAUAZPUPVBUTRZVCCAUBUOVDCAVDVBVAIOZUOVGVCVCVBVAUQOZVGPZVAVBUQC
      SBSZUCVHVBVAHOVIVBVAUJVBVAHIUDQTUECVBUFTUGVFVBUSRZVEVFVBHRVKPVJVBHUSUHQCV
      BURAVJUKUIULUMUN $.
  $}

  ${
    $d x y z $.
    $( The Image functor applied to the converse of the subset relationship
       yields a subset of the subset relationship.  (Contributed by Scott
       Fenton, 14-Apr-2018.) $)
    imagesset $p |- Image `' SSet C_ SSet $=
      ( vx vy vz csset ccnv cimage wss cv cop wcel wi wal wrex sseq2 wbr brsset
      vex bitri df-br bitr3i cima wceq wel ssid rspcev mpan2 elima brcnv rexbii
      sylibr ssriv mpbiri brimage 3imtr3i gen2 wfun wrel wb funimage ssrel mp2b
      funrel mpbir ) DEZFZDGZAHZBHZIZVEJZVIDJZKZBLALZVLABVHVDVGUAZUBZVGVHGZVJVK
      VOVPVGVNGBVGVNBAUCZVHCHZGZCVGMZVHVNJZVQVHVHGZVTVHUDVSWBCVHVGVRVHVHNUEUFWA
      VRVHVDOZCVGMVTCVHVDVGBQZUGWCVSCVGWCVHVRDOVSVRVHDCQZWDUHVHVRWEPRUIRUJUKVHV
      NVGNULVOVGVHVEOVJVGVHVDAQWDUMVGVHVESTVPVGVHDOVKVGVHWDPVGVHDSTUNUOVEUPVEUQ
      VFVMURVDUSVEVBABVEDUTVAVC $.
  $}

  ${
    $d A x $.  $d R x $.  $d S x $.
    brub.1 $e |- S e. _V $.
    brub.2 $e |- A e. _V $.
    $( Binary relation form of the upper bound functor.  (Contributed by Scott
       Fenton, 3-May-2018.) $)
    brub $p |- ( S UB R A <-> A. x e. S x R A ) $=
      ( cvv cxp cdif cep ccnv ccom wbr cv wrex wn cub wcel brdif mpbiran rexbii
      wral brxp mpbir2an coepr xchbinx df-ub breqi rexnal bitri con2bii 3bitr4i
      brv ) DBGGHZGCIZJKLZIZMZANZBUOMZADOZPDBCQZMUSBCMZADUBZURDBUPMZVAURDBUNMZV
      EPVFDGRBGREFDBGGUCUDDBUNUPSTADBUOEFUEUFDBVBUQCUGUHVAVDVAVCPZADOVDPUTVGADU
      TUSBGMVGUSBUMUSBGCSTUAVCADUIUJUKUL $.

    $( Binary relation form of the lower bound functor.  (Contributed by Scott
       Fenton, 3-May-2018.) $)
    brlb $p |- ( S LB R A <-> A. x e. S A R x ) $=
      ( clb wbr ccnv cub cv wral df-lb breqi brub vex brcnv ralbii 3bitri ) DBC
      GZHDBCIZJZHAKZBUAHZADLBUCCHZADLDBTUBCMNABUADEFOUDUEADUCBCAPFQRS $.
  $}

  ${
    $d R x y z $.  $d A x y z $.
    $( Alternate quantifier-free definition of a well-founded relation.
       (Contributed by Scott Fenton, 26-Aug-2026.) $)
    dffr7 $p |- ( R Fr A
    <-> ( ~P A \ { (/) } ) C_ Fix ( _E o. ( _V \ ( R o. `' _E ) ) ) ) $=
      ( vx vz vy cv cep cvv ccnv ccom cdif cfix wcel cpw c0 wral wbr wrex vex
      wn csn wss wfr elfix coepr notbii brv brdif mpbiran ralnex 3bitr4i rexbii
      coep 3bitri ralbii dfss3 dffr6 3bitr4ri ) CFZGHBGIJZKZJZLZMZCANOUAKZPDFEF
      ZBQZTDUSPZEUSRZCVEPVEVCUBABUCVDVICVEVDUSUSVBQUSVFVAQZEUSRVIUSVBCSZUDEUSUS
      VAVKVKUMVJVHEUSUSVFUTQZTZVGDUSRZTVJVHVLVNDUSVFBVKESUEUFVJUSVFHQVMUSVFUGUS
      VFHUTUHUIVGDUSUJUKULUNUOCVEVCUPCEDABUQUR $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Alternate ordered pairs
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c << >> XX. $.
  $( Declare the syntax for an alternate ordered pair. $)
  caltop $a class << A , B >> $.
  $( Declare the syntax for an alternate Cartesian product. $)
  caltxp $a class ( A XX. B ) $.

  $( An alternative definition of ordered pairs.  This definition removes a
     hypothesis from its defining theorem (see ~ altopth ), making it more
     convenient in some circumstances.  (Contributed by Scott Fenton,
     22-Mar-2012.) $)
  df-altop $a |- << A , B >> = { { A } , { A , { B } } } $.

  ${
    $d A x y z $.  $d B x y z $.
    $( Define Cartesian products of alternative ordered pairs.  (Contributed by
       Scott Fenton, 23-Mar-2012.) $)
    df-altxp $a |- ( A XX. B ) = { z | E. x e. A E. y e. B z = << x , y >> } $.
  $}

  $( Alternative ordered pairs always exist.  (Contributed by Scott Fenton,
     22-Mar-2012.) $)
  altopex $p |- << A , B >> e. _V $=
    ( caltop csn cpr cvv df-altop prex eqeltri ) ABCADZABDEZEFABGJKHI $.

  $( Two alternate ordered pairs are equal iff the singletons of their
     respective elements are equal.  Note that this holds regardless of sethood
     of any of the elements.  (Contributed by Scott Fenton, 16-Apr-2012.) $)
  altopthsn $p |- ( << A , B >> = << C , D >> <->
                    ( { A } = { C } /\ { B } = { D } ) ) $=
    ( caltop wceq csn cpr wa df-altop eqeq12i snex prex wss snsspr1 sseq2 df-pr
    cun preq2d preqr2 preq12b simpl mpbii adantl mpbiri adantr eqssd jaoi sylbi
    wo uneq1 3eqtr4g preq1 eqtrd eqeq1d biimpd syl syl6com jcai sylan9eq impbii
    preq2 bitri ) ABEZCDEZFAGZABGZHZHZCGZCDGZHZHZFZVFVJFZVGVKFZIZVDVIVEVMABJCDJ
    KVNVQVNVOVPVNVOVHVLFZIZVFVLFZVHVJFZIZUJVOVFVHVJVLALAVGMCLCVKMZUAVSVOWBVOVRU
    BWBVFVJWAVFVJNZVTWAVFVHNWDAVGOVHVJVFPUCUDVTVJVFNZWAVTWEVJVLNCVKOVFVLVJPUEUF
    UGUHUIVOVNVJCVGHZHZVMFZVPVOVNWHVOVIWGVMVOVIVFWFHWGVOVHWFVFVOVFVGGZRVJWIRVHW
    FVFVJWIUKAVGQCVGQULSVFVJWFUMUNZUOUPWHWFVLFVPWFVLVJCVGMWCTVGVKCBLDLTUQURUSVO
    VPVIWGVMWJVPWFVLVJVGVKCVBSUTVAVC $.

  $( Equality for alternate ordered pairs.  (Contributed by Scott Fenton,
     22-Mar-2012.) $)
  altopeq12 $p |- ( ( A = B /\ C = D ) -> << A , C >> = << B , D >> ) $=
    ( wceq wa csn caltop sneq anim12i altopthsn sylibr ) ABEZCDEZFAGBGEZCGDGEZF
    ACHBDHEMONPABICDIJACBDKL $.

  $( Equality for alternate ordered pairs.  (Contributed by Scott Fenton,
     22-Mar-2012.) $)
  altopeq1 $p |- ( A = B -> << A , C >> = << B , C >> ) $=
    ( wceq caltop eqid altopeq12 mpan2 ) ABDCCDACEBCEDCFABCCGH $.

  $( Equality for alternate ordered pairs.  (Contributed by Scott Fenton,
     22-Mar-2012.) $)
  altopeq2 $p |- ( A = B -> << C , A >> = << C , B >> ) $=
    ( wceq caltop eqid altopeq12 mpan ) CCDABDCAECBEDCFCCABGH $.

  $( Equality of the first members of equal alternate ordered pairs, which
     holds regardless of the second members' sethood.  (Contributed by Scott
     Fenton, 22-Mar-2012.) $)
  altopth1 $p |- ( A e. V -> ( << A , B >> = << C , D >> -> A = C ) ) $=
    ( caltop wceq csn wa wcel altopthsn sneqrg adantrd biimtrid ) ABFCDFGAHCHGZ
    BHDHGZIAEJZACGZABCDKQORPACELMN $.

  $( Equality of the second members of equal alternate ordered pairs, which
     holds regardless of the first members' sethood.  (Contributed by Scott
     Fenton, 22-Mar-2012.) $)
  altopth2 $p |- ( B e. V -> ( << A , B >> = << C , D >> -> B = D ) ) $=
    ( caltop wceq csn wa wcel altopthsn sneqrg adantld biimtrid ) ABFCDFGAHCHGZ
    BHDHGZIBEJZBDGZABCDKQPROBDELMN $.

  $( Alternate ordered pair theorem.  (Contributed by Scott Fenton,
     22-Mar-2012.) $)
  altopthg $p |- ( ( A e. V /\ B e. W ) ->
                   ( << A , B >> = << C , D >> <-> ( A = C /\ B = D ) ) ) $=
    ( caltop wceq csn wa wcel altopthsn sneqbg bi2anan9 bitrid ) ABGCDGHAICIHZB
    IDIHZJAEKZBFKZJACHZBDHZJABCDLRPTSQUAACEMBDFMNO $.

  $( Alternate ordered pair theorem.  (Contributed by Scott Fenton,
     14-Apr-2012.) $)
  altopthbg $p |- ( ( A e. V /\ D e. W ) ->
                   ( << A , B >> = << C , D >> <-> ( A = C /\ B = D ) ) ) $=
    ( caltop wceq csn wa wcel altopthsn sneqbg eqcom 3bitr4g bi2anan9 bitrid )
    ABGCDGHAICIHZBIZDIZHZJAEKZDFKZJACHZBDHZJABCDLUBRUDUCUAUEACEMUCTSHDBHUAUEDBF
    MSTNBDNOPQ $.

  ${
    altopth.1 $e |- A e. _V $.
    altopth.2 $e |- B e. _V $.
    $( The alternate ordered pair theorem.  If two alternate ordered pairs are
       equal, their first elements are equal and their second elements are
       equal.  Note that ` C ` and ` D ` are not required to be a set due to a
       peculiarity of our specific ordered pair definition, as opposed to the
       regular ordered pairs used here, which (as in ~ opth ), requires ` D `
       to be a set.  (Contributed by Scott Fenton, 23-Mar-2012.) $)
    altopth $p |- ( << A , B >> = << C , D >> <-> ( A = C /\ B = D ) ) $=
      ( cvv wcel caltop wceq wa wb altopthg mp2an ) AGHBGHABICDIJACJBDJKLEFABCD
      GGMN $.
  $}

  ${
    altopthb.1 $e |- A e. _V $.
    altopthb.2 $e |- D e. _V $.
    $( Alternate ordered pair theorem with different sethood requirements.  See
       ~ altopth for more comments.  (Contributed by Scott Fenton,
       14-Apr-2012.) $)
    altopthb $p |- ( << A , B >> = << C , D >> <-> ( A = C /\ B = D ) ) $=
      ( cvv wcel caltop wceq wa wb altopthbg mp2an ) AGHDGHABICDIJACJBDJKLEFABC
      DGGMN $.
  $}

  ${
    altopthc.1 $e |- B e. _V $.
    altopthc.2 $e |- C e. _V $.
    $( Alternate ordered pair theorem with different sethood requirements.  See
       ~ altopth for more comments.  (Contributed by Scott Fenton,
       14-Apr-2012.) $)
    altopthc $p |- ( << A , B >> = << C , D >> <-> ( A = C /\ B = D ) ) $=
      ( caltop wceq wa eqcom altopthb anbi12i 3bitri ) ABGZCDGZHONHCAHZDBHZIACH
      ZBDHZINOJCDABFEKPRQSCAJDBJLM $.
  $}

  ${
    altopthd.1 $e |- C e. _V $.
    altopthd.2 $e |- D e. _V $.
    $( Alternate ordered pair theorem with different sethood requirements.  See
       ~ altopth for more comments.  (Contributed by Scott Fenton,
       14-Apr-2012.) $)
    altopthd $p |- ( << A , B >> = << C , D >> <-> ( A = C /\ B = D ) ) $=
      ( caltop wceq wa eqcom altopth anbi12i 3bitri ) ABGZCDGZHONHCAHZDBHZIACHZ
      BDHZINOJCDABEFKPRQSCAJDBJLM $.
  $}

  ${
    $d A x y z $.  $d B x y z $.  $d C x y z $.
    $( Equality for alternate Cartesian products.  (Contributed by Scott
       Fenton, 24-Mar-2012.) $)
    altxpeq1 $p |- ( A = B -> ( A XX. C ) = ( B XX. C ) ) $=
      ( vz vx vy wceq cv caltop wrex cab caltxp rexeq abbidv df-altxp 3eqtr4g )
      ABGZDHEHFHIGFCJZEAJZDKREBJZDKACLBCLQSTDREABMNEFDACOEFDBCOP $.

    $( Equality for alternate Cartesian products.  (Contributed by Scott
       Fenton, 24-Mar-2012.) $)
    altxpeq2 $p |- ( A = B -> ( C XX. A ) = ( C XX. B ) ) $=
      ( vz vx vy wceq cv caltop wrex cab caltxp rexbidv abbidv df-altxp 3eqtr4g
      rexeq ) ABGZDHEHFHIGZFAJZECJZDKSFBJZECJZDKCALCBLRUAUCDRTUBECSFABQMNEFDCAO
      EFDCBOP $.
  $}

  ${
    $d A x y z $.  $d B x y z $.  $d X x y z $.
    $( Membership in alternate Cartesian products.  (Contributed by Scott
       Fenton, 23-Mar-2012.) $)
    elaltxp $p |- ( X e. ( A XX. B ) <->
                     E. x e. A E. y e. B X = << x , y >> ) $=
      ( vz caltxp wcel cvv cv caltop wceq wrex elex wi altopex eleq1 mpbiri a1i
      wa rexlimivv eqeq1 2rexbidv df-altxp elab2g pm5.21nii ) ECDGZHEIHZEAJZBJZ
      KZLZBDMACMZEUGNULUHABCDULUHOUICHUJDHTULUHUKIHUIUJPEUKIQRSUAFJZUKLZBDMACMU
      MFEUGIUNELUOULABCDUNEUKUBUCABFCDUDUEUF $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d X x y $.  $d Y x y $.
    $( Alternate ordered pair membership in a Cartesian product.  Note that,
       unlike ~ opelxp , there is no sethood requirement here.  (Contributed by
       Scott Fenton, 22-Mar-2012.) $)
    altopelaltxp $p |- ( << X , Y >> e. ( A XX. B ) <->
                          ( X e. A /\ Y e. B ) ) $=
      ( vx vy caltop caltxp wcel cv wceq wrex wa elaltxp reeanv eqcom vex bitri
      altopth risset 2rexbii anbi12i 3bitr4i ) CDGZABHIUDEJZFJZGZKZFBLEALZCAIZD
      BIZMZEFABUDNUECKZUFDKZMZFBLEALUMEALZUNFBLZMUIULUMUNEFABOUHUOEFABUHUGUDKUO
      UDUGPUEUFCDEQFQSRUAUJUPUKUQECATFDBTUBUCR $.
  $}

  ${
    $d A x y z $.  $d B x y z $.
    $( An inclusion rule for alternate Cartesian products.  (Contributed by
       Scott Fenton, 24-Mar-2012.) $)
    altxpsspw $p |- ( A XX. B ) C_ ~P ~P ( A u. ~P B ) $=
      ( vz vx vy caltxp cpw cun cv wcel wrex wa csn cpr wss snssi syl elpw prex
      vsnex caltop wceq elaltxp wi df-altop ssun3 adantr elun1 elun2 sylbir vex
      anim12i sylib prsspw bitri sylanbrc eqeltrid eleq1a rexlimivv sylbi ssriv
      prss ) CABFZABGZHZGZGZCIZVCJVHDIZEIZUAZUBZEBKDAKVHVGJZDEABVHUCVLVMDEABVIA
      JZVJBJZLZVKVGJVLVMUDVPVKVIMZVIVJMZNZNZVGVIVJUEVPVQVEOZVSVEOZVTVGJZVNWAVOV
      NVQAOWAVIAPVQAVDUFQUGVPVIVEJZVRVEJZLWBVNWDVOWEVIAVDUHVOVRBOZWEVJBPWFVRVDJ
      WEVRBETZRVRVDAUIUJQULVIVRVEDUKWGVBUMWCVTVFOWAWBLVTVFVQVSSRVQVSVEDTVIVRSUN
      UOUPUQVKVGVHURQUSUTVA $.
  $}

  $( The alternate Cartesian product of two sets is a set.  (Contributed by
     Scott Fenton, 24-Mar-2012.) $)
  altxpexg $p |- ( ( A e. V /\ B e. W ) -> ( A XX. B ) e. _V ) $=
    ( wcel wa caltxp cpw cun wss cvv altxpsspw pwexg unexg sylan2 ssexg sylancr
    3syl ) ACEZBDEZFZABGZABHZIZHZHZJUFKEZUBKEABLUAUDKEZUEKEUGTSUCKEUHBDMAUCCKNO
    UDKMUEKMRUBUFKPQ $.

  $( Compute the rank of an alternate ordered pair.  (Contributed by Scott
     Fenton, 18-Dec-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
  rankaltopb $p |- ( ( A e. U. ( R1 " On ) /\ B e. U. ( R1 " On ) ) -> ( rank
    ` << A , B >> ) = suc suc ( ( rank ` A ) u. suc ( rank ` B ) ) ) $=
    ( cr1 con0 cima wcel wa crnk cfv csn cun csuc wceq snwf cpr rankprb syl2anc
    fveq2i suceq eqtrd cuni caltop df-altop adantr prwf eqtrid wss snsspr1 mpbi
    ssequn1 rankunb 3eqtr3a syl sylan2 ranksnb uneq2d 3syl adantl ) ACDEUAZFZBU
    SFZGABUBZHIZAHIZBJZHIZKZLZLZVDBHILZKZLZLZVAUTVEUSFZVCVIMBNUTVNGZVCAJZHIAVEO
    ZHIZKZLZVIVOVCVPVQOZHIZVTVBWAHABUCRVOVPUSFZVQUSFZWBVTMUTWCVNANUDZAVEUEZVPVQ
    PQUFVOVSVHMVTVIMVOVPVQKZHIZVRVSVHWGVQHVPVQUGWGVQMAVEUHVPVQUJUIRVOWCWDWHVSMW
    EWFVPVQUKQAVEPULVSVHSUMTUNVAVIVMMZUTVAVGVKMVHVLMWIVAVFVJVDBUOUPVGVKSVHVLSUQ
    URT $.

  ${
    nfaltop.1 $e |- F/_ x A $.
    nfaltop.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for alternate ordered pairs.
       (Contributed by Scott Fenton, 25-Sep-2015.) $)
    nfaltop $p |- F/_ x << A , B >> $=
      ( caltop csn cpr df-altop nfsn nfpr nfcxfr ) ABCFBGZBCGZHZHBCIAMOABDJABND
      ACEJKKL $.
  $}

  ${
    $d x A $.
    $( Distribution of class substitution over alternate ordered pairs.
       (Contributed by Scott Fenton, 25-Sep-2015.) $)
    sbcaltop $p |- ( A e. _V -> [_ A / x ]_ << C , D >> =
                                << [_ A / x ]_ C , [_ A / x ]_ D >> ) $=
      ( caltop csb cvv wnfc wcel nfcsb1v nfaltop wceq csbeq1a altopeq1 altopeq2
      a1i cv syl eqtrd csbiegf ) ABCDEZABCFZABDFZEZGAUDHBGIAUBUCABCJABDJKPAQBLZ
      UAUBDEZUDUECUBLUAUFLABCMCUBDNRUEDUCLUFUDLABDMDUCUBORST $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Geometry in the Euclidean space
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Congruence properties
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c OuterFiveSeg $.

  $( Declare the syntax for the outer five segment configuration. $)
  cofs $a class OuterFiveSeg $.

  ${
    $d a b c d x y z w p q n $.
    $( The outer five segment configuration is an abbreviation for the
       conditions of the Five Segment Axiom ( ~ ax5seg ).  See ~ brofs and
       ~ 5segofs for how it is used.  Definition 2.10 of [Schwabhauser] p. 28.
       (Contributed by Scott Fenton, 21-Sep-2013.) $)
    df-ofs $a |- OuterFiveSeg =
        { <. p , q >. |
           E. n e. NN E. a e. ( EE ` n ) E. b e. ( EE ` n ) E. c e. ( EE ` n )
           E. d e. ( EE ` n ) E. x e. ( EE ` n ) E. y e. ( EE ` n )
           E. z e. ( EE ` n ) E. w e. ( EE ` n ) (
           p = <. <. a , b >. , <. c , d >. >. /\
           q = <. <. x , y >. , <. z , w >. >. /\
           ( ( b Btwn <. a , c >. /\ y Btwn <. x , z >. ) /\
             ( <. a , b >. Cgr <. x , y >. /\
               <. b , c >. Cgr <. y , z >. ) /\
             ( <. a , d >. Cgr <. x , w >. /\
               <. b , d >. Cgr <. y , w >. ) ) ) } $.
  $}

  ${
    cgrrflx2d.1 $e |- ( ph -> N e. NN ) $.
    cgrrflx2d.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
    cgrrflx2d.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
    $( Deduction form of ~ axcgrrflx .  (Contributed by Scott Fenton,
       13-Oct-2013.) $)
    cgrrflx2d $p |- ( ph -> <. A , B >. Cgr <. B , A >. ) $=
      ( cn wcel cee cfv cop ccgr wbr axcgrrflx syl3anc ) ADHIBDJKZICQIBCLCBLMNE
      FGBCDOP $.
  $}

  ${
    cgrtr4d.1 $e |- ( ph -> N e. NN ) $.
    cgrtr4d.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
    cgrtr4d.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
    cgrtr4d.4 $e |- ( ph -> C e. ( EE ` N ) ) $.
    cgrtr4d.5 $e |- ( ph -> D e. ( EE ` N ) ) $.
    cgrtr4d.6 $e |- ( ph -> E e. ( EE ` N ) ) $.
    cgrtr4d.7 $e |- ( ph -> F e. ( EE ` N ) ) $.
    cgrtr4d.8 $e |- ( ph -> <. A , B >. Cgr <. C , D >. ) $.
    cgrtr4d.9 $e |- ( ph -> <. A , B >. Cgr <. E , F >. ) $.
    $( Deduction form of ~ axcgrtr .  (Contributed by Scott Fenton,
       13-Oct-2013.) $)
    cgrtr4d $p |- ( ph -> <. C , D >. Cgr <. E , F >. ) $=
      ( cop ccgr wcel wbr cn cee cfv wa wi axcgrtr syl133anc mp2and ) ABCRZDERZ
      SUAZUJFGRZSUAZUKUMSUAZPQAHUBTBHUCUDZTCUPTDUPTEUPTFUPTGUPTULUNUEUOUFIJKLMN
      OBCDEFGHUGUHUI $.
  $}

  ${
    cgrtr4and.1 $e |- ( ph -> N e. NN ) $.
    cgrtr4and.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
    cgrtr4and.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
    cgrtr4and.4 $e |- ( ph -> C e. ( EE ` N ) ) $.
    cgrtr4and.5 $e |- ( ph -> D e. ( EE ` N ) ) $.
    cgrtr4and.6 $e |- ( ph -> E e. ( EE ` N ) ) $.
    cgrtr4and.7 $e |- ( ph -> F e. ( EE ` N ) ) $.
    cgrtr4and.8 $e |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. C , D >. ) $.
    cgrtr4and.9 $e |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. E , F >. ) $.
    $( Deduction form of ~ axcgrtr .  (Contributed by Scott Fenton,
       13-Oct-2013.) $)
    cgrtr4and $p |- ( ( ph /\ ps ) -> <. C , D >. Cgr <. E , F >. ) $=
      ( wcel adantr wa cn cee cfv cgrtr4d ) ABUACDEFGHIAIUBSBJTACIUCUDZSBKTADUF
      SBLTAEUFSBMTAFUFSBNTAGUFSBOTAHUFSBPTQRUE $.
  $}

  $( Reflexivity law for congruence.  Theorem 2.1 of [Schwabhauser] p. 27.
     (Contributed by Scott Fenton, 12-Jun-2013.) $)
  cgrrflx $p |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ->
    <. A , B >. Cgr <. A , B >. ) $=
    ( wcel cee cfv w3a simp1 simp3 simp2 cop ccgr wbr axcgrrflx 3com23 cgrtr4d
    cn ) CQDZACEFZDZBSDZGBAABABCRTUAHRTUAIZRTUAJZUCUBUCUBRUATBAKABKLMBACNOZUDP
    $.

  ${
    cgrrflxd.1 $e |- ( ph -> N e. NN ) $.
    cgrrflxd.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
    cgrrflxd.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
    $( Deduction form of ~ cgrrflx .  (Contributed by Scott Fenton,
       13-Oct-2013.) $)
    cgrrflxd $p |- ( ph -> <. A , B >. Cgr <. A , B >. ) $=
      ( cn wcel cee cfv cop ccgr wbr cgrrflx syl3anc ) ADHIBDJKZICQIBCLZRMNEFGB
      CDOP $.
  $}

  $( Congruence commutes on the two sides.  Implication version.  Theorem 2.2
     of [Schwabhauser] p. 27.  (Contributed by Scott Fenton, 12-Jun-2013.) $)
  cgrcomim $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
    ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
    ( <. A , B >. Cgr <. C , D >. ->
      <. C , D >. Cgr <. A , B >. ) ) $=
    ( cn wcel cee cfv w3a cop ccgr wbr simp1 simp2l simp2r simp3l simp3r simpr
    wa simpl1 simpl2l simpl2r cgrrflxd cgrtr4and ex ) EFGZAEHIZGZBUHGZTZCUHGZDU
    HGZTZJZABKZCDKZLMZUQUPLMUOURABCDABEUGUKUNNUGUIUJUNOZUGUIUJUNPZUGUKULUMQUGUK
    ULUMRUSUTUOURSUOURTABEUGUKUNURUAUIUJUGUNURUBUIUJUGUNURUCUDUEUF $.

  $( Congruence commutes between the two sides.  (Contributed by Scott Fenton,
     12-Jun-2013.) $)
  cgrcom $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
    ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
    ( <. A , B >. Cgr <. C , D >. <->
      <. C , D >. Cgr <. A , B >. ) ) $=
    ( cn wcel cee cfv wa w3a cop ccgr wbr cgrcomim wi 3com23 impbid ) EFGZAEHIZ
    GBTGJZCTGDTGJZKABLZCDLZMNZUDUCMNZABCDEOSUBUAUFUEPCDABEOQR $.

  ${
    cgrcomand.1 $e |- ( ph -> N e. NN ) $.
    cgrcomand.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
    cgrcomand.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
    cgrcomand.4 $e |- ( ph -> C e. ( EE ` N ) ) $.
    cgrcomand.5 $e |- ( ph -> D e. ( EE ` N ) ) $.
    cgrcomand.6 $e |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. C , D >. ) $.
    $( Deduction form of ~ cgrcom .  (Contributed by Scott Fenton,
       13-Oct-2013.) $)
    cgrcomand $p |- ( ( ph /\ ps ) -> <. C , D >. Cgr <. A , B >. ) $=
      ( wa cop ccgr wbr wb cn wcel cee cfv cgrcom syl122anc adantr mpbid ) ABNC
      DOZEFOZPQZUHUGPQZMAUIUJRZBAGSTCGUAUBZTDULTEULTFULTUKHIJKLCDEFGUCUDUEUF $.
  $}

  $( Transitivity law for congruence.  Theorem 2.3 of [Schwabhauser] p. 27.
     (Contributed by Scott Fenton, 24-Sep-2013.) $)
  cgrtr $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
       ( ( <. A , B >. Cgr <. C , D >. /\
           <. C , D >. Cgr <. E , F >. ) ->
         <. A , B >. Cgr <. E , F >. ) ) $=
    ( cn wcel cee cfv w3a cop ccgr wbr wa simp1 simp23 simp31 simp21 cgrcomand
    simp22 simp32 simp33 simprl simprr cgrtr4and ex ) GHIZAGJKZIZBUJIZCUJIZLZDU
    JIZEUJIZFUJIZLZLZABMZCDMZNOZVAEFMZNOZPZUTVCNOUSVECDABEFGUIUNURQZUIUKULUMURR
    ZUIUNUOUPUQSZUIUKULUMURTZUIUKULUMURUBZUIUNUOUPUQUCUIUNUOUPUQUDUSVEABCDGVFVI
    VJVGVHUSVBVDUEUAUSVBVDUFUGUH $.

  ${
    cgrtrand.1 $e |- ( ph -> N e. NN ) $.
    cgrtrand.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
    cgrtrand.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
    cgrtrand.4 $e |- ( ph -> C e. ( EE ` N ) ) $.
    cgrtrand.5 $e |- ( ph -> D e. ( EE ` N ) ) $.
    cgrtrand.6 $e |- ( ph -> E e. ( EE ` N ) ) $.
    cgrtrand.7 $e |- ( ph -> F e. ( EE ` N ) ) $.
    cgrtrand.8 $e |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. C , D >. ) $.
    cgrtrand.9 $e |- ( ( ph /\ ps ) -> <. C , D >. Cgr <. E , F >. ) $.
    $( Deduction form of ~ cgrtr .  (Contributed by Scott Fenton,
       13-Oct-2013.) $)
    cgrtrand $p |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. E , F >. ) $=
      ( cop wcel wa ccgr wbr wi cn cee cfv cgrtr syl133anc adantr mp2and ) ABUA
      CDSZEFSZUBUCZUMGHSZUBUCZULUOUBUCZQRAUNUPUAUQUDZBAIUETCIUFUGZTDUSTEUSTFUST
      GUSTHUSTURJKLMNOPCDEFGHIUHUIUJUK $.
  $}

  $( Transitivity law for congruence.  (Contributed by Scott Fenton,
     7-Oct-2013.) $)
  cgrtr3 $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
       ( ( <. A , B >. Cgr <. E , F >. /\
           <. C , D >. Cgr <. E , F >. ) ->
         <. A , B >. Cgr <. C , D >. ) ) $=
    ( cn wcel cee cfv w3a cop ccgr wbr wa simp1 simp21 simp22 simp32 cgrcomand
    simp33 simp23 simp31 simprl simprr cgrtrand ex ) GHIZAGJKZIZBUJIZCUJIZLZDUJ
    IZEUJIZFUJIZLZLZABMZEFMZNOZCDMZVANOZPZUTVCNOUSVEABEFCDGUIUNURQZUIUKULUMURRU
    IUKULUMURSUIUNUOUPUQTZUIUNUOUPUQUBZUIUKULUMURUCZUIUNUOUPUQUDZUSVBVDUEUSVECD
    EFGVFVIVJVGVHUSVBVDUFUAUGUH $.

  ${
    cgrtr3and.1 $e |- ( ph -> N e. NN ) $.
    cgrtr3and.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
    cgrtr3and.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
    cgrtr3and.4 $e |- ( ph -> C e. ( EE ` N ) ) $.
    cgrtr3and.5 $e |- ( ph -> D e. ( EE ` N ) ) $.
    cgrtr3and.6 $e |- ( ph -> E e. ( EE ` N ) ) $.
    cgrtr3and.7 $e |- ( ph -> F e. ( EE ` N ) ) $.
    cgrtr3and.8 $e |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. E , F >. ) $.
    cgrtr3and.9 $e |- ( ( ph /\ ps ) -> <. C , D >. Cgr <. E , F >. ) $.
    $( Deduction form of ~ cgrtr3 .  (Contributed by Scott Fenton,
       13-Oct-2013.) $)
    cgrtr3and $p |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. C , D >. ) $=
      ( cop wcel wa ccgr wbr wi cn cee cfv cgrtr3 syl133anc adantr mp2and ) ABU
      ACDSZGHSZUBUCZEFSZUMUBUCZULUOUBUCZQRAUNUPUAUQUDZBAIUETCIUFUGZTDUSTEUSTFUS
      TGUSTHUSTURJKLMNOPCDEFGHIUHUIUJUK $.
  $}

  $( Congruence commutes on the left.  Biconditional version of Theorem 2.4 of
     [Schwabhauser] p. 27.  (Contributed by Scott Fenton, 12-Jun-2013.) $)
  cgrcoml $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
    ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
    ( <. A , B >. Cgr <. C , D >. <->
      <. B , A >. Cgr <. C , D >. ) ) $=
    ( cn wcel cee cfv wa w3a cop wbr simp1 cgrrflx2d wi axcgrtr syl133anc mpand
    ccgr simp2l simp2r simp3l simp3r impbid ) EFGZAEHIZGZBUGGZJZCUGGZDUGGZJZKZA
    BLZCDLZTMZBALZUPTMZUNUOURTMZUQUSUNABEUFUJUMNZUFUHUIUMUAZUFUHUIUMUBZOUNUFUHU
    IUIUHUKULUTUQJUSPVAVBVCVCVBUFUJUKULUCZUFUJUKULUDZABBACDEQRSUNURUOTMZUSUQUNB
    AEVAVCVBOUNUFUIUHUHUIUKULVFUSJUQPVAVCVBVBVCVDVEBAABCDEQRSUE $.

  $( Congruence commutes on the right.  Biconditional version of Theorem 2.5 of
     [Schwabhauser] p. 27.  (Contributed by Scott Fenton, 12-Jun-2013.) $)
  cgrcomr $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
    ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
    ( <. A , B >. Cgr <. C , D >. <->
      <. A , B >. Cgr <. D , C >. ) ) $=
    ( cn wcel cee cfv wa w3a cop ccgr wbr wb cgrcoml 3com23 cgrcom simp1 simp2l
    simp2r simp3r simp3l syl122anc 3bitr4d ) EFGZAEHIZGZBUGGZJZCUGGZDUGGZJZKZCD
    LZABLZMNZDCLZUPMNZUPUOMNUPURMNZUFUMUJUQUSOCDABEPQABCDERUNUFUHUIULUKUTUSOUFU
    JUMSUFUHUIUMTUFUHUIUMUAUFUJUKULUBUFUJUKULUCABDCERUDUE $.

  $( Congruence commutes on both sides.  (Contributed by Scott Fenton,
     12-Jun-2013.) $)
  cgrcomlr $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
    ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
    ( <. A , B >. Cgr <. C , D >. <->
      <. B , A >. Cgr <. D , C >. ) ) $=
    ( cn wcel cee cfv wa w3a cop ccgr wbr cgrcoml ancom cgrcomr syl3an2b bitrd
    wb ) EFGZAEHIZGZBUBGZJZCUBGDUBGJZKABLCDLZMNBALZUGMNZUHDCLMNZABCDEOUEUAUDUCJ
    UFUIUJTUCUDPBACDEQRS $.

  ${
    cgrcomlrand.1 $e |- ( ph -> N e. NN ) $.
    cgrcomlrand.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
    cgrcomlrand.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
    cgrcomlrand.4 $e |- ( ph -> C e. ( EE ` N ) ) $.
    cgrcomlrand.5 $e |- ( ph -> D e. ( EE ` N ) ) $.
    cgrcomlrand.6 $e |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. C , D >. ) $.
    $( Deduction form of ~ cgrcoml .  (Contributed by Scott Fenton,
       14-Oct-2013.) $)
    cgrcomland $p |- ( ( ph /\ ps ) -> <. B , A >. Cgr <. C , D >. ) $=
      ( wa cop ccgr wbr wb cn wcel cee cfv cgrcoml syl122anc adantr mpbid ) ABN
      CDOEFOZPQZDCOUGPQZMAUHUIRZBAGSTCGUAUBZTDUKTEUKTFUKTUJHIJKLCDEFGUCUDUEUF
      $.

    $( Deduction form of ~ cgrcoml .  (Contributed by Scott Fenton,
       14-Oct-2013.) $)
    cgrcomrand $p |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. D , C >. ) $=
      ( wa cop ccgr wbr wb cn wcel cee cfv cgrcomr syl122anc adantr mpbid ) ABN
      CDOZEFOPQZUGFEOPQZMAUHUIRZBAGSTCGUAUBZTDUKTEUKTFUKTUJHIJKLCDEFGUCUDUEUF
      $.

    $( Deduction form of ~ cgrcomlr .  (Contributed by Scott Fenton,
       14-Oct-2013.) $)
    cgrcomlrand $p |- ( ( ph /\ ps ) -> <. B , A >. Cgr <. D , C >. ) $=
      ( cgrcomrand cgrcomland ) ABCDFEGHIJLKABCDEFGHIJKLMNO $.
  $}

  ${
    $d A x $.  $d B x $.  $d N x $.
    $( Degenerate segments are congruent.  Theorem 2.8 of [Schwabhauser] p. 28.
       (Contributed by Scott Fenton, 12-Jun-2013.) $)
    cgrtriv $p |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ->
    <. A , A >. Cgr <. B , B >. ) $=
      ( vx cn wcel cee cfv w3a cv cop cbtwn wbr ccgr simp1 simp2 simp3 axsegcon
      wa wrex syl122anc wceq simpl1 simpl2 simpr simpl3 axcgrid syl13anc breq1d
      wi opeq2 biimprd syli adantld rexlimdva mpd ) CEFZACGHZFZBURFZIZAADJZKZLM
      ZVCBBKZNMZSZDURTZAAKZVENMZVAUQUSUSUTUTVHUQUSUTOUQUSUTPZVKUQUSUTQZVLDAABBC
      RUAVAVGVJDURVAVBURFZSZVFVJVDVFVNAVBUBZVJVNUQUSVMUTVFVOUJUQUSUTVMUCUQUSUTV
      MUDVAVMUEUQUSUTVMUFAVBBCUGUHVOVJVFVOVIVCVENAVBAUKUIULUMUNUOUP $.
  $}

  $( Identity law for congruence.  (Contributed by Scott Fenton,
     12-Jun-2013.) $)
  cgrid2 $p |- ( ( N e. NN /\
    ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
    ( <. A , A >. Cgr <. B , C >. -> B = C ) ) $=
    ( cn wcel cee cfv w3a wa cop ccgr wceq wb simpl simpr1 simpr2 simpr3 cgrcom
    wbr syl122anc wi 3anrot axcgrid sylan2b sylbid ) DEFZADGHZFZBUHFZCUHFZIZJZA
    AKZBCKZLTZUOUNLTZBCMZUMUGUIUIUJUKUPUQNUGULOUGUIUJUKPZUSUGUIUJUKQUGUIUJUKRAA
    BCDSUAULUGUJUKUIIUQURUBUIUJUKUCBCADUDUEUF $.

  $( Two congruent segments are either both degenerate or both nondegenerate.
     (Contributed by Scott Fenton, 12-Jun-2013.) $)
  cgrdegen $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
    ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
      ( <. A , B >. Cgr <. C , D >. -> ( A = B <-> C = D ) ) ) $=
    ( cn wcel cee cfv wa cop ccgr wbr wceq opeq1 biimpac syl13anc syl5 expdimp
    wi wb breq1d simp1 simp2r simp3l simp3r cgrid2 breq2d simp2l axcgrid impbid
    w3a ex ) EFGZAEHIZGZBUOGZJZCUOGZDUOGZJZULZABKZCDKZLMZABNZCDNZUAVBVEJVFVGVBV
    EVFVGVEVFJBBKZVDLMZVBVGVFVEVIVFVCVHVDLABBOUBPVBUNUQUSUTVIVGTUNURVAUCZUNUPUQ
    VAUDZUNURUSUTUEUNURUSUTUFZBCDEUGQRSVBVEVGVFVEVGJVCDDKZLMZVBVFVGVEVNVGVDVMVC
    LCDDOUHPVBUNUPUQUTVNVFTVJUNUPUQVAUIVKVLABDEUJQRSUKUM $.

  ${
    $d N a b c d e f g h p q n $.  $d A a b c d e f g h p q n $.
    $d B a b c d e f g h p q n $.  $d C a b c d e f g h p q n $.
    $d D a b c d e f g h p q n $.  $d E a b c d e f g h p q n $.
    $d F a b c d e f g h p q n $.  $d G a b c d e f g h p q n $.
    $d H a b c d e f g h p q n $.
    $( Binary relation form of the outer five segment predicate.  (Contributed
       by Scott Fenton, 21-Sep-2013.) $)
    brofs $p |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
        ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\
        ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) ->
    ( <. <. A , B >. , <. C , D >. >. OuterFiveSeg
      <. <. E , F >. , <. G , H >. >. <-> ( ( B Btwn <. A , C >. /\
                     F Btwn <. E , G >. ) /\
        ( <. A , B >. Cgr <. E , F >. /\
          <. B , C >. Cgr <. F , G >. ) /\
        ( <. A , D >. Cgr <. E , H >. /\
          <. B , D >. Cgr <. F , H >. ) ) ) ) $=
      ( cv cop cbtwn wbr wa ccgr w3a wceq opeq1 breq2d opeq2 vb va vc vf ve cee
      vg vd vh vn vq vp cfv cofs anbi1d breq1d 3anbi123d breq1 anbi12d 3anbi12d
      cn anbi2d 3anbi3d fveq2 df-ofs br8 ) UAJZUBJZUCJZKZLMZUDJZUEJZUGJZKZLMZNZ
      VHVGKZVMVLKZOMZVGVIKZVLVNKZOMZNZVHUHJZKZVMUIJZKZOMZVGWEKZVLWGKZOMZNZPVGAV
      IKZLMZVPNZAVGKZVSOMZWCNZAWEKZWHOMZWLNZPBWNLMZVPNZABKZVSOMZBVIKZWBOMZNZXAB
      WEKZWKOMZNZPBACKZLMZVPNZXFBCKZWBOMZNZXLPXOXRADKZWHOMZBDKZWKOMZNZPXNVLEVNK
      ZLMZNZXEEVLKZOMZXQNZXSEWGKZOMZYBNZPXNFYDLMZNZXEEFKZOMZXPFVNKZOMZNZYKYAFWG
      KZOMZNZPXNFEGKZLMZNZYPXPFGKZOMZNZUUBPUUEUUHXSEHKZOMZYAFHKZOMZNZPUJABCDUJJ
      ZUFUMIUFUMUNVAUEUDUGUIEFGHIUKULUBUAUCUHVHAQZVQWPWDWSWMXBUUOVKWOVPUUOVJWNV
      GLVHAVIRSUOUUOVTWRWCUUOVRWQVSOVHAVGRUPUOUUOWIXAWLUUOWFWTWHOVHAWERUPUOUQVG
      BQZWPXDWSXIXBXLUUPWOXCVPVGBWNLURUOUUPWRXFWCXHUUPWQXEVSOVGBATUPUUPWAXGWBOV
      GBVIRUPUSUUPWLXKXAUUPWJXJWKOVGBWERUPVBUQVICQZXDXOXIXRXLUUQXCXNVPUUQWNXMBL
      VICATSUOUUQXHXQXFUUQXGXPWBOVICBTUPVBUTWEDQZXLYCXOXRUURXAXTXKYBUURWTXSWHOW
      EDATUPUURXJYAWKOWEDBTUPUSVCVMEQZXOYFXRYIYCYLUUSVPYEXNUUSVOYDVLLVMEVNRSVBU
      USXFYHXQUUSVSYGXEOVMEVLRSUOUUSXTYKYBUUSWHYJXSOVMEWGRSUOUQVLFQZYFYNYIYSYLU
      UBUUTYEYMXNVLFYDLURVBUUTYHYPXQYRUUTYGYOXEOVLFETSUUTWBYQXPOVLFVNRSUSUUTYBU
      UAYKUUTWKYTYAOVLFWGRSVBUQVNGQZYNUUEYSUUHUUBUVAYMUUDXNUVAYDUUCFLVNGETSVBUV
      AYRUUGYPUVAYQUUFXPOVNGFTSVBUTWGHQZUUBUUMUUEUUHUVBYKUUJUUAUULUVBYJUUIXSOWG
      HETSUVBYTUUKYAOWGHFTSUSVCUUNIUFVDUEUDUGUIUJUKULUBUAUCUHVEVF $.
  $}

  $( Rephrase ~ ax5seg using the outer five segment predicate.  Theorem 2.10 of
     [Schwabhauser] p. 28.  (Contributed by Scott Fenton, 21-Sep-2013.) $)
  5segofs $p |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
        ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\
        ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) ->
    ( ( <. <. A , B >. , <. C , D >. >. OuterFiveSeg
        <. <. E , F >. , <. G , H >. >. /\ A =/= B ) ->
        <. C , D >. Cgr <. G , H >. ) ) $=
    ( cn wcel cee cfv w3a cop wbr wa cbtwn ccgr 3jca brofs anbi1d simpr simpl1l
    cofs wne simpl1r simpl2 simpl3 biimtrdi ax5seg syld ) IJKAILMZKBUMKNCUMKDUM
    KEUMKNFUMKGUMKHUMKNNZABOZCDOZOEFOZGHOZOUEPZABUFZQZUTBACORPZFEGORPZNZUOUQSPB
    COFGOSPQZADOEHOSPBDOFHOSPQZNZUPURSPUNVAVBVCQZVEVFNZUTQZVGUNUSVIUTABCDEFGHIU
    AUBVJVDVEVFVJUTVBVCVIUTUCVBVCVEVFUTUDVBVCVEVFUTUGTVHVEVFUTUHVHVEVFUTUITUJAB
    CDEFGHIUKUL $.

  $( The outer five segment predicate commutes.  (Contributed by Scott Fenton,
     26-Sep-2013.) $)
  ofscom $p |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
        ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\
        ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) ->
    ( <. <. A , B >. , <. C , D >. >. OuterFiveSeg
      <. <. E , F >. , <. G , H >. >. <->
      <. <. E , F >. , <. G , H >. >. OuterFiveSeg
      <. <. A , B >. , <. C , D >. >. ) ) $=
    ( wcel w3a cop cbtwn wbr wa ccgr cofs wb cgrcom syl122anc cee cfv ancom a1i
    cn simp11 simp12 simp13 simp23 simp31 simp21 simp32 simp22 simp33 3anbi123d
    anbi12d brofs syl333anc 3bitr4d ) IUEJZAIUAUBZJZBVAJZKZCVAJZDVAJZEVAJZKZFVA
    JZGVAJZHVAJZKZKZBACLMNZFEGLMNZOZABLZEFLZPNZBCLZFGLZPNZOZADLZEHLZPNZBDLZFHLZ
    PNZOZKVOVNOZVRVQPNZWAVTPNZOZWEWDPNZWHWGPNZOZKZVQCDLLZVRGHLLZQNWTWSQNZVMVPWK
    WCWNWJWQVPWKRVMVNVOUCUDVMVSWLWBWMVMUTVBVCVGVIVSWLRUTVBVCVHVLUFZUTVBVCVHVLUG
    ZUTVBVCVHVLUHZVDVEVFVGVLUIZVDVHVIVJVKUJZABEFISTVMUTVCVEVIVJWBWMRXBXDVDVEVFV
    GVLUKZXFVDVHVIVJVKULZBCFGISTUPVMWFWOWIWPVMUTVBVFVGVKWFWORXBXCVDVEVFVGVLUMZX
    EVDVHVIVJVKUNZADEHISTVMUTVCVFVIVKWIWPRXBXDXIXFXJBDFHISTUPUOABCDEFGHIUQVMUTV
    GVIVJVKVBVCVEVFXAWRRXBXEXFXHXJXCXDXGXIEFGHABCDIUQURUS $.

  $( Link congruence over a pair of line segments.  Theorem 2.11 of
     [Schwabhauser] p. 29.  (Contributed by Scott Fenton, 12-Jun-2013.) $)
  cgrextend $p |- ( ( N e. NN /\
    ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
    ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
    ( ( ( B Btwn <. A , C >. /\ E Btwn <. D , F >. ) /\
        ( <. A , B >. Cgr <. D , E >. /\
          <. B , C >. Cgr <. E , F >. ) ) ->
      <. A , C >. Cgr <. D , F >. ) ) $=
    ( wcel w3a cop cbtwn wbr wa ccgr wi wceq wb opeq1 adantr 3jca cn cee breq1d
    cfv simp1 simp22 simp31 simp32 cgrid2 syl13anc adantl sylbid breqan12d syld
    exbiri impd adantld wne cofs simpl1 simpl21 simpl22 simpl23 simpl31 simpl32
    simpl33 simprrl simprrr cgrtriv syl3anc simpld cgrcomlr syl122anc mpbid jca
    ex brofs syl333anc mpbir3and simprl 5segofs sylc exp32 com12 pm2.61ine ) GU
    AHZAGUBUDZHZBWGHZCWGHZIZDWGHZEWGHZFWGHZIZIZBACJZKLEDFJZKLMZABJZDEJZNLZBCJZE
    FJZNLZMZMZWQWRNLZOZOABABPZWPXIXJWPMZXFXHWSXKXBXEXHXKXBDEPZXEXHOZXKXBBBJZXAN
    LZXLXJXBXOQWPXJWTXNXANABBRUCSWPXOXLOZXJWPWFWIWLWMXPWFWKWOUEWFWHWIWJWOUFWFWK
    WLWMWNUGWFWKWLWMWNUHBDEGUIUJUKULXJXLXMOWPXJXLXHXEXJXLWQXCWRXDNABCRDEFRUMUOS
    UNUPUQVPWPABURZXIWPXQXGXHWPXQXGMZMZCAJZFDJZNLZXHXSWFWHWIIZWJWHWLIZWMWNWLIZI
    WTXTJXAYAJUSLZXQMYBXSYCYDYEXSWFWHWIWFWKWOXRUTZWHWIWJWFWOXRVAZWHWIWJWFWOXRVB
    ZTXSWJWHWLWHWIWJWFWOXRVCZYHWLWMWNWFWKXRVDZTXSWMWNWLWLWMWNWFWKXRVEZWLWMWNWFW
    KXRVFZYKTTXSYFXQXSYFWSXFAAJDDJNLZBAJEDJNLZMZWPXQWSXFVGWPXQWSXFVHZXSYNYOXSWF
    WHWLYNYGYHYKADGVIVJXSXBYOXSXBXEYQVKXSWFWHWIWLWMXBYOQYGYHYIYKYLABDEGVLVMVNVO
    XSWFWHWIWJWHWLWMWNWLYFWSXFYPIQYGYHYIYJYHYKYLYMYKABCADEFDGVQVRVSWPXQXGVTVOAB
    CADEFDGWAWBXSWFWJWHWNWLYBXHQYGYJYHYMYKCAFDGVLVMVNWCWDWE $.

  ${
    cgrextendand.1 $e |- ( ph -> N e. NN ) $.
    cgrextendand.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
    cgrextendand.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
    cgrextendand.4 $e |- ( ph -> C e. ( EE ` N ) ) $.
    cgrextendand.5 $e |- ( ph -> D e. ( EE ` N ) ) $.
    cgrextendand.6 $e |- ( ph -> E e. ( EE ` N ) ) $.
    cgrextendand.7 $e |- ( ph -> F e. ( EE ` N ) ) $.
    cgrextendand.8 $e |- ( ( ph /\ ps ) -> B Btwn <. A , C >. ) $.
    cgrextendand.9 $e |- ( ( ph /\ ps ) -> E Btwn <. D , F >. ) $.
    cgrextendand.10 $e |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. D , E >. ) $.
    cgrextendand.11 $e |- ( ( ph /\ ps ) -> <. B , C >. Cgr <. E , F >. ) $.
    $( Deduction form of ~ cgrextend .  (Contributed by Scott Fenton,
       14-Oct-2013.) $)
    cgrextendand $p |- ( ( ph /\ ps ) -> <. A , C >. Cgr <. D , F >. ) $=
      ( wa cop cbtwn wbr ccgr jca wi cn wcel cee cfv cgrextend syl133anc adantr
      mp2and ) ABUAZDCEUBZUCUDZGFHUBZUCUDZUAZCDUBFGUBUEUDZDEUBGHUBUEUDZUAZUQUSU
      EUDZUPURUTQRUFUPVBVCSTUFAVAVDUAVEUGZBAIUHUICIUJUKZUIDVGUIEVGUIFVGUIGVGUIH
      VGUIVFJKLMNOPCDEFGHIULUMUNUO $.
  $}

  $( Two points that satisfy the conclusion of ~ axsegcon are identical.
     Uniqueness portion of Theorem 2.12 of [Schwabhauser] p. 29.  (Contributed
     by Scott Fenton, 12-Jun-2013.) $)
  segconeq $p |- ( ( N e. NN /\
   ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
   ( Q e. ( EE ` N ) /\ X e. ( EE ` N ) /\ Y e. ( EE ` N ) ) ) ->
   ( ( Q =/= A /\
     ( A Btwn <. Q , X >. /\ <. A , X >. Cgr <. B , C >. ) /\
     ( A Btwn <. Q , Y >. /\ <. A , Y >. Cgr <. B , C >. ) )
   -> X = Y ) ) $=
    ( wcel w3a cop cbtwn wbr ccgr wa jca cgrrflxd 3jca wb cgrcom wi cee cfv wne
    cn cofs wceq simpr2l simpl1 simpl31 simpl21 simpl32 simpl33 simpr3l simpl22
    simpl23 simpr3r syl122anc mpbid simpr2r cgrtr4d jca32 cgrextend sylc simp31
    simp1 simp21 simp32 simp33 brofs syl333anc sylibrd a1i jcad 5segofs axcgrid
    ex syl13anc 3syld ) EUDHZAEUAUBZHZBVTHZCVTHZIZDVTHZFVTHZGVTHZIZIZDAUCZADFJZ
    KLZAFJZBCJZMLZNZADGJZKLZAGJZWNMLZNZIZDAJZFGJZJXCFFJZJUELZWJNZXDXEMLZFGUFZWI
    XBXFWJWIXBWLWLNZXCXCMLZWMWMMLZNZWQWKMLZWSWMMLZNZIZXFWIXBXQWIXBNZXJXMXPXRWLW
    LWLWOWJXAWIUGZXSOXRXKXLXRDAEVSWDWHXBUHZWEWFWGVSWDXBUIZWAWBWCVSWHXBUJZPZXRAF
    EXTYBWEWFWGVSWDXBUKZPOXRXNXOXRVSWEWAWGIZWEWAWFIZIWRWLNZXKXONNXNXRVSYEYFXTXR
    WEWAWGYAYBWEWFWGVSWDXBULZQXRWEWAWFYAYBYDQQXRYGXKXOXRWRWLWRWTWJWPWIUMXSOYCXR
    BCAGAFEXTWAWBWCVSWHXBUNZWAWBWCVSWHXBUOZYBYHYBYDXRWTWNWSMLZWRWTWJWPWIUPXRVSW
    AWGWBWCWTYKRXTYBYHYIYJAGBCESUQURXRWOWNWMMLZWLWOWJXAWIUSXRVSWAWFWBWCWOYLRXTY
    BYDYIYJAFBCESUQURUTZVADAGDAFEVBVCYMOQVPWIVSWEWAWFWGWEWAWFWFXFXQRVSWDWHVEZVS
    WDWEWFWGVDZVSWAWBWCWHVFZVSWDWEWFWGVGZVSWDWEWFWGVHZYOYPYQYQDAFGDAFFEVIVJVKXB
    WJTWIWJWPXAVEVLVMWIVSWEWAWFWGWEWAWFWFXGXHTYNYOYPYQYRYOYPYQYQDAFGDAFFEVNVJWI
    VSWFWGWFXHXITYNYQYRYQFGFEVOVQVR $.

  ${
    $d N r s $.  $d A r s $.  $d B r s $.  $d C r s $.  $d D r s $.
    $( Existential uniqueness version of ~ segconeq .  (Contributed by Scott
       Fenton, 19-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    segconeu $p |- ( ( N e. NN /\
       ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) /\
         C =/= D ) ) ->
       E! r e. ( EE ` N ) ( D Btwn <. C , r >. /\
       <. D , r >. Cgr <. A , B >. ) ) $=
      ( vs cn wcel cee wa w3a cv cop cbtwn wbr ccgr wi wral opeq2 cfv wrex wreu
      wne simpl simpr2 simpr1 axsegcon syl3anc simpl23 simprl simprr 3jca simp1
      weq simp22r simp21l simp21r simp22l simp3l simp3r segconeq syl133anc syld
      ex 3expa ralrimivva breq2d breq1d anbi12d reu4 sylanbrc ) EHIZAEJUAZIZBVN
      IZKZCVNIZDVNIZKZCDUDZLZKZDCFMZNZOPZDWDNZABNZQPZKZFVNUBZWJDCGMZNZOPZDWLNZW
      HQPZKZKZFGUOZRZGVNSFVNSWJFVNUCWCVMVTVQWKVMWBUEVMVQVTWAUFVMVQVTWAUGFCDABEU
      HUIWCWTFGVNVNVMWBWDVNIZWLVNIZKZWTVMWBXCLZWRWAWJWQLZWSXDWRXEXDWRKWAWJWQVQV
      TWAVMXCWRUJXDWJWQUKXDWJWQULUMVEXDVMVSVOVPVRXAXBXEWSRVMWBXCUNVRVSVQWAVMXCU
      PVOVPVTWAVMXCUQVOVPVTWAVMXCURVRVSVQWAVMXCUSVMWBXAXBUTVMWBXAXBVADABCEWDWLV
      BVCVDVFVGWJWQFGVNWSWFWNWIWPWSWEWMDOWDWLCTVHWSWGWOWHQWDWLDTVIVJVKVL $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Betweenness properties
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x $.  $d B x $.  $d N x $.
    $( Betweenness always holds for the second endpoint.  Theorem 3.1 of
       [Schwabhauser] p. 30.  (Contributed by Scott Fenton, 12-Jun-2013.) $)
    btwntriv2 $p |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ->
      B Btwn <. A , B >. ) $=
      ( vx cn wcel cee cfv w3a cv cop cbtwn wbr ccgr wa wrex simp1 simp2 simp3
      wi axsegcon syl122anc simpl1 simpl3 simpr axcgrid syl13anc breq2d biimprd
      wceq opeq2 syl6 impd ancomsd rexlimdva mpd ) CEFZACGHZFZBURFZIZBADJZKZLMZ
      BVBKBBKNMZOZDURPZBABKZLMZVAUQUSUTUTUTVGUQUSUTQUQUSUTRUQUSUTSZVJVJDABBBCUA
      UBVAVFVIDURVAVBURFZOZVEVDVIVLVEVDVIVLVEBVBUJZVDVITVLUQUTVKUTVEVMTUQUSUTVK
      UCUQUSUTVKUDZVAVKUEVNBVBBCUFUGVMVIVDVMVHVCBLBVBAUKUHUIULUMUNUOUP $.
  $}

  ${
    $d N x $.  $d A x $.  $d B x $.  $d C x $.
    $( Betweenness commutes.  Implication version.  Theorem 3.2 of
       [Schwabhauser] p. 30.  (Contributed by Scott Fenton, 12-Jun-2013.) $)
    btwncomim $p |- ( ( N e. NN /\
      ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
      ( A Btwn <. B , C >. -> A Btwn <. C , B >. ) ) $=
      ( vx cn wcel cee cfv w3a wa cop cbtwn wbr cv btwntriv2 3adant3r2 wi simpl
      wrex simpr2 simpr1 simpr3 axpasch syl132anc mpan2d simpr simplr1 axbtwnid
      wceq simpll syl3anc breq1 biimpd syl6 impd rexlimdva syld ) DFGZADHIZGZBU
      TGZCUTGZJZKZABCLMNZEOZAALMNZVGCBLZMNZKZEUTTZAVIMNZVEVFCACLMNZVLUSVAVCVNVB
      ACDPQVEUSVBVAVCVAVCVFVNKVLRUSVDSUSVAVBVCUAUSVAVBVCUBZUSVAVBVCUCZVOVPEBACA
      CDUDUEUFVEVKVMEUTVEVGUTGZKZVHVJVMVRVHVGAUJZVJVMRVRUSVQVAVHVSRUSVDVQUKVEVQ
      UGVAVBVCUSVQUHVGADUIULVSVJVMVGAVIMUMUNUOUPUQUR $.
  $}

  $( Betweenness commutes.  (Contributed by Scott Fenton, 12-Jun-2013.) $)
  btwncom $p |- ( ( N e. NN /\
      ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
      ( A Btwn <. B , C >. <-> A Btwn <. C , B >. ) ) $=
    ( cn wcel cee cfv w3a wa cop cbtwn wbr btwncomim wi 3ancomb sylan2b impbid
    ) DEFZADGHZFZBTFZCTFZIZJABCKLMZACBKLMZABCDNUDSUAUCUBIUFUEOUAUBUCPACBDNQR $.

  ${
    btwncomand.1 $e |- ( ph -> N e. NN ) $.
    btwncomand.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
    btwncomand.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
    btwncomand.4 $e |- ( ph -> C e. ( EE ` N ) ) $.
    btwncomand.5 $e |- ( ( ph /\ ps ) -> A Btwn <. B , C >. ) $.
    $( Deduction form of ~ btwncom .  (Contributed by Scott Fenton,
       14-Oct-2013.) $)
    btwncomand $p |- ( ( ph /\ ps ) -> A Btwn <. C , B >. ) $=
      ( wa cop cbtwn wbr wb cn wcel cee cfv btwncom syl13anc adantr mpbid ) ABL
      CDEMNOZCEDMNOZKAUEUFPZBAFQRCFSTZRDUHREUHRUGGHIJCDEFUAUBUCUD $.
  $}

  $( Betweenness always holds for the first endpoint.  Theorem 3.3 of
     [Schwabhauser] p. 30.  (Contributed by Scott Fenton, 12-Jun-2013.) $)
  btwntriv1 $p |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ->
      A Btwn <. A , B >. ) $=
    ( cn wcel cee cfv w3a cop cbtwn wbr btwntriv2 3com23 wb simp1 simp2 btwncom
    simp3 syl13anc mpbird ) CDEZACFGZEZBUBEZHZAABIJKZABAIJKZUAUDUCUGBACLMUEUAUC
    UCUDUFUGNUAUCUDOUAUCUDPZUHUAUCUDRAABCQST $.

  ${
    $d N x $.  $d A x $.  $d B x $.  $d C x $.
    $( If you can swap the first two arguments of a betweenness statement, then
       those arguments are identical.  Theorem 3.4 of [Schwabhauser] p. 30.
       (Contributed by Scott Fenton, 12-Jun-2013.) $)
    btwnswapid $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
       ( ( A Btwn <. B , C >. /\ B Btwn <. A , C >. ) ->
         A = B ) ) $=
      ( vx cn wcel cee cfv w3a wa cop cbtwn wbr cv wrex wceq axbtwnid syl3anc
      wi simpl simpr2 simpr1 simpr3 axpasch simpr simplr1 simplr2 anim12d eqtr2
      syl132anc simpll syl6 rexlimdva syld ) DFGZADHIZGZBUQGZCUQGZJZKZABCLMNBAC
      LMNKZEOZAALMNZVDBBLMNZKZEUQPZABQZVBUPUSURUTURUSVCVHTUPVAUAUPURUSUTUBZUPUR
      USUTUCZUPURUSUTUDVKVJEBACABDUEUKVBVGVIEUQVBVDUQGZKZVGVDAQZVDBQZKVIVMVEVNV
      FVOVMUPVLURVEVNTUPVAVLULZVBVLUFZURUSUTUPVLUGVDADRSVMUPVLUSVFVOTVPVQURUSUT
      UPVLUHVDBDRSUIVDABUJUMUNUO $.
  $}

  $( If you can swap arguments one and three of a betweenness statement, then
     those arguments are identical.  (Contributed by Scott Fenton,
     7-Oct-2013.) $)
  btwnswapid2 $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
       ( ( A Btwn <. B , C >. /\ C Btwn <. B , A >. ) ->
         A = C ) ) $=
    ( cn wcel cee cfv w3a wa cop cbtwn wbr btwncom wb 3anrev sylan2b anbi12d wi
    wceq 3ancomb btwnswapid sylbid ) DEFZADGHZFZBUEFZCUEFZIZJZABCKLMZCBAKLMZJAC
    BKLMZCABKLMZJZACTZUJUKUMULUNABCDNUIUDUHUGUFIULUNOUFUGUHPCBADNQRUIUDUFUHUGIU
    OUPSUFUGUHUAACBDUBQUC $.

  ${
    $d N x $.  $d A x $.  $d B x $.  $d C x $.  $d D x $.
    $( Inner transitivity law for betweenness.  Left-hand side of Theorem 3.5
       of [Schwabhauser] p. 30.  (Contributed by Scott Fenton, 12-Jun-2013.) $)
    btwnintr $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
       ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
       ( ( B Btwn <. A , D >. /\ C Btwn <. B , D >. ) ->
         B Btwn <. A , C >. ) ) $=
      ( vx cn wcel cee cfv wa w3a cop cbtwn wbr cv wrex wi simp1 simp2l axpasch
      simp2r simp3r simp3l syl132anc wceq simpl1 simpr simpl2r axbtwnid syl3anc
      biimpa wb simpl3l simpl2l btwncom syl13anc imbitrid syland rexlimdva syld
      breq1 ) EGHZAEIJZHZBVDHZKZCVDHZDVDHZKZLZBADMNOCBDMNOKZFPZBBMNOZVMCAMZNOZK
      ZFVDQZBACMNOZVKVCVEVFVIVFVHVLVRRVCVGVJSVCVEVFVJTVCVEVFVJUBZVCVGVHVIUCVTVC
      VGVHVIUDFABDBCEUAUEVKVQVSFVDVKVMVDHZKZVNVMBUFZVPVSWBVCWAVFVNWCRVCVGVJWAUG
      ZVKWAUHVEVFVCVJWAUIZVMBEUJUKWCVPKBVONOZWBVSWCVPWFVMBVONVBULWBVCVFVHVEWFVS
      UMWDWEVHVIVCVGWAUNVEVFVCVJWAUOBCAEUPUQURUSUTVA $.

    $( Exchange the first endpoint in betweenness.  Left-hand side of Theorem
       3.6 of [Schwabhauser] p. 30.  (Contributed by Scott Fenton,
       12-Jun-2013.) $)
    btwnexch3 $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
       ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
       ( ( B Btwn <. A , C >. /\ C Btwn <. A , D >. ) ->
         C Btwn <. B , D >. ) ) $=
      ( vx cn wcel cee cfv wa w3a cop cbtwn wbr cv wb btwncom syl13anc wi simp1
      wrex simp3l simp2l simp3r simp2r anbi12d axpasch syl132anc sylbid ancomsd
      wceq simpl1 simpr simpl3l axbtwnid syl3anc breq1 syl6 impd rexlimdva syld
      biimpd ) EGHZAEIJZHZBVEHZKZCVEHZDVEHZKZLZBACMNOZCADMNOZKFPZCCMNOZVOBDMZNO
      ZKZFVEUBZCVQNOZVLVNVMVTVLVNVMKCDAMNOZBCAMNOZKZVTVLVNWBVMWCVLVDVIVFVJVNWBQ
      VDVHVKUAZVDVHVIVJUCZVDVFVGVKUDZVDVHVIVJUEZCADERSVLVDVGVFVIVMWCQWEVDVFVGVK
      UFZWGWFBACERSUGVLVDVJVIVFVIVGWDVTTWEWHWFWGWFWIFDCACBEUHUIUJUKVLVSWAFVEVLV
      OVEHZKZVPVRWAWKVPVOCULZVRWATWKVDWJVIVPWLTVDVHVKWJUMVLWJUNVIVJVDVHWJUOVOCE
      UPUQWLVRWAVOCVQNURVCUSUTVAVB $.

    ${
      btwnexch3and.1 $e |- ( ph -> N e. NN ) $.
      btwnexch3and.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
      btwnexch3and.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
      btwnexch3and.4 $e |- ( ph -> C e. ( EE ` N ) ) $.
      btwnexch3and.5 $e |- ( ph -> D e. ( EE ` N ) ) $.
      btwnexch3and.6 $e |- ( ( ph /\ ps ) -> B Btwn <. A , C >. ) $.
      btwnexch3and.7 $e |- ( ( ph /\ ps ) -> C Btwn <. A , D >. ) $.
      $( Deduction form of ~ btwnexch3 .  (Contributed by Scott Fenton,
         13-Oct-2013.) $)
      btwnexch3and $p |- ( ( ph /\ ps ) -> C Btwn <. B , D >. ) $=
        ( wa cop cbtwn wbr wi wcel cn cee cfv btwnexch3 syl122anc adantr mp2and
        ) ABODCEPQRZECFPQRZEDFPQRZMNAUHUIOUJSZBAGUATCGUBUCZTDULTEULTFULTUKHIJKL
        CDEFGUDUEUFUG $.
    $}

    $( Outer transitivity law for betweenness.  Left-hand side of Theorem 3.1
       of [Schwabhauser] p. 30.  (Contributed by Scott Fenton, 12-Jun-2013.) $)
    btwnouttr2 $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
       ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
       ( ( B =/= C /\
           B Btwn <. A , C >. /\ C Btwn <. B , D >. ) ->
         C Btwn <. A , D >. ) ) $=
      ( vx cn wcel cee wa w3a cop cbtwn wbr ccgr syl122anc adantr wi jca mpd cv
      cfv wne simp1 simp2l simp3l simp3r axsegcon simprrl simprl1 simpl2 simprl
      wrex wceq adantl simpl1 simpl2l simpl2r simpl3l btwnexch3 simprrr simprl3
      simpr simpl3r cgrrflxd segconeq syl133anc mp3and opeq2d breqtrd rexlimdva
      expr an32s ex ) EGHZAEIUBZHZBVPHZJZCVPHZDVPHZJZKZBCUCZBACLMNZCBDLMNZKZCAD
      LZMNZWCWGJZCAFUAZLZMNZCWKLCDLZONZJZFVPUMZWIWCWQWGWCVOVQVTVTWAWQVOVSWBUDVO
      VQVRWBUEVOVSVTWAUFZWRVOVSVTWAUGFACCDEUHPQWJWPWIFVPWCWKVPHZWGWPWIRWCWSJZWG
      WPWIWTWGWPJZJZCWLWHMWTWGWMWOUIXBWKDAXBWDCBWKLMNZWOJZWFWNWNONZJZWKDUNZWDWE
      WFWPWTUJXBXCWOXBWEWMJZXCXAXHWTXAWEWMWDWEWFWPUKWGWMWOULSUOWTXHXCRZXAWTVOVQ
      VRVTWSXIVOVSWBWSUPZVQVRVOWBWSUQVQVRVOWBWSURZVTWAVOVSWSUSZWCWSVCZABCWKEUTP
      QTWTWGWMWOVASXBWFXEWDWEWFWPWTVBWTXEXAWTCDEXJXLVTWAVOVSWSVDZVEQSWTWDXDXFKX
      GRZXAWTVOVTVTWAVRWSWAXOXJXLXLXNXKXMXNCCDBEWKDVFVGQVHVIVJVLVMVKTVN $.
  $}

  $( Exchange the outer point of two betweenness statements.  Right-hand side
     of Theorem 3.5 of [Schwabhauser] p. 30.  (Contributed by Scott Fenton,
     14-Jun-2013.) $)
  btwnexch2 $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
   ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
   ( ( B Btwn <. A , D >. /\ C Btwn <. B , D >. ) ->
     C Btwn <. A , D >. ) ) $=
    ( cn wcel cee cfv wa w3a cop cbtwn wbr wi wceq breq1 biimpd adantrd adantr
    a1i wne simprl simprr btwnintr simprrr btwnouttr2 mp3and exp32 pm2.61dne
    mpd ) EFGAEHIZGBULGJCULGDULGJKZBADLZMNZCBDLMNZJZCUNMNZOZBCBCPZUSOUMUTUOURUP
    UTUOURBCUNMQRSUAUMBCUBZUQURUMVAUQJZJZVABACLMNZUPURUMVAUQUCVCUQVDUMVAUQUDUMU
    QVDOVBABCDEUETUKUMVAUOUPUFUMVAVDUPKUROVBABCDEUGTUHUIUJ $.

  $( Outer transitivity law for betweenness.  Right-hand side of Theorem 3.7 of
     [Schwabhauser] p. 30.  (Contributed by Scott Fenton, 14-Jun-2013.) $)
  btwnouttr $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
   ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
   ( ( B =/= C /\
       B Btwn <. A , C >. /\ C Btwn <. B , D >. ) ->
     B Btwn <. A , D >. ) ) $=
    ( cn wcel cee cfv wa w3a wne cop cbtwn wbr simp1 simp2r wb btwncom syl13anc
    simp3r simp2l necom a1i simp3l 3anbi123d 3ancomb bitrdi biimpa wi syl122anc
    btwnouttr2 adantr mpd btwncomand ex ) EFGZAEHIZGZBURGZJZCURGZDURGZJZKZBCLZB
    ACMNOZCBDMNOZKZBADMNOVEVIBDAEUQVAVDPZUQUSUTVDQZUQVAVBVCUAZUQUSUTVDUBZVEVIJC
    BLZCDBMNOZBCAMNOZKZBDAMNOZVEVIVQVEVIVNVPVOKVQVEVFVNVGVPVHVOVFVNRVEBCUCUDVEU
    QUTUSVBVGVPRVJVKVMUQVAVBVCUEZBACESTVEUQVBUTVCVHVORVJVSVKVLCBDESTUFVNVPVOUGU
    HUIVEVQVRUJZVIVEUQVCVBUTUSVTVJVLVSVKVMDCBAEULUKUMUNUOUP $.

  $( Outer transitivity law for betweenness.  Right-hand side of Theorem 3.6 of
     [Schwabhauser] p. 30.  (Contributed by Scott Fenton, 24-Sep-2013.) $)
  btwnexch $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
  ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
  ( ( B Btwn <. A , C >. /\ C Btwn <. A , D >. ) -> B Btwn <. A , D >. ) ) $=
    ( cn wcel cee cfv wa w3a cop cbtwn wbr simp1 simp2r simp2l btwncom syl13anc
    wb simp3l simp3r anbi12d ancom bitrdi wi btwnexch2 syl122anc sylbid sylibd
    ) EFGZAEHIZGZBULGZJZCULGZDULGZJZKZBACLMNZCADLZMNZJZBDALZMNZBVAMNZUSVCCVDMNZ
    BCALMNZJZVEUSVCVHVGJVIUSUTVHVBVGUSUKUNUMUPUTVHTUKUOUROZUKUMUNURPZUKUMUNURQZ
    UKUOUPUQUAZBACERSUSUKUPUMUQVBVGTVJVMVLUKUOUPUQUBZCADERSUCVHVGUDUEUSUKUQUPUN
    UMVIVEUFVJVNVMVKVLDCBAEUGUHUIUSUKUNUQUMVEVFTVJVKVNVLBDAERSUJ $.

  ${
    btwnexchand.1 $e |- ( ph -> N e. NN ) $.
    btwnexchand.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
    btwnexchand.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
    btwnexchand.4 $e |- ( ph -> C e. ( EE ` N ) ) $.
    btwnexchand.5 $e |- ( ph -> D e. ( EE ` N ) ) $.
    btwnexchand.6 $e |- ( ( ph /\ ps ) -> B Btwn <. A , C >. ) $.
    btwnexchand.7 $e |- ( ( ph /\ ps ) -> C Btwn <. A , D >. ) $.
    $( Deduction form of ~ btwnexch .  (Contributed by Scott Fenton,
       13-Oct-2013.) $)
    btwnexchand $p |- ( ( ph /\ ps ) -> B Btwn <. A , D >. ) $=
      ( wa cop cbtwn wbr wi wcel cn cee cfv btwnexch syl122anc adantr mp2and )
      ABODCEPQRZECFPZQRZDUIQRZMNAUHUJOUKSZBAGUATCGUBUCZTDUMTEUMTFUMTULHIJKLCDEF
      GUDUEUFUG $.
  $}

  ${
    $d A c u v $.  $d B c u v $.  $d N c u v $.
    $( There is always a ` c ` distinct from ` B ` such that ` B ` lies between
       ` A ` and ` c ` .  Theorem 3.14 of [Schwabhauser] p. 32.  (Contributed
       by Scott Fenton, 24-Sep-2013.) $)
    btwndiff $p |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ->
       E. c e. ( EE ` N ) ( B Btwn <. A , c >. /\ B =/= c ) ) $=
      ( vu vv cn wcel cee cfv w3a cv wne wrex cop wbr wa syl122anc wi mpd cbtwn
      axlowdim1 3ad2ant1 ccgr simp11 simp12 simp13 simp2l axsegcon wceq simpl11
      simp2r weq wb simpl13 simpr simpl2l simpl2r cgrdegen biimp com12 3ad2ant3
      necon3d adantr syld anim2d reximdva 3exp rexlimdvv ) CGHZACIJZHZBVKHZKZEL
      ZFLZMZFVKNEVKNZBADLZOUAPZBVSMZQZDVKNZVJVLVRVMEFCUBUCVNVQWCEFVKVKVNVOVKHZV
      PVKHZQZVQWCVNWFVQKZVTBVSOVOVPOUDPZQZDVKNZWCWGVJVLVMWDWEWJVJVLVMWFVQUEVJVL
      VMWFVQUFVJVLVMWFVQUGVNWDWEVQUHVNWDWEVQULDABVOVPCUIRWGWIWBDVKWGVSVKHZQZWHW
      AVTWLWHBVSUJZEFUMZUNZWAWLVJVMWKWDWEWHWOSVJVLVMWFVQWKUKVJVLVMWFVQWKUOWGWKU
      PWDWEVNVQWKUQWDWEVNVQWKURBVSVOVPCUSRWGWOWASZWKVQVNWPWFWOVQWAWOBVSVOVPWMWN
      UTVCVAVBVDVEVFVGTVHVIT $.
  $}

  ${
    $d A q r $.  $d B q r $.  $d C q r $.  $d D q r $.  $d E q r $.
    $d N q r $.  $d P q r $.
    $( A line segment between two sides of a triange intersects a segment
       crossing from the remaining side to the opposite vertex.  Theorem 3.17
       of [Schwabhauser] p. 33.  (Contributed by Scott Fenton, 24-Sep-2013.) $)
    trisegint $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ P e. ( EE ` N ) ) ) ->
       ( ( B Btwn <. A , C >. /\ E Btwn <. D , C >. /\ P Btwn <. A , D >. ) ->
       E. q e. ( EE ` N ) ( q Btwn <. P , C >. /\ q Btwn <. B , E >. ) ) ) $=
      ( vr wcel w3a cop cbtwn wbr wa wrex 3jca jca sylc 3ad2ant1 cee cfv simpl1
      cn simpl23 simpl21 simpl31 simpl32 simpl33 simpr2 btwncom syl13anc simpr3
      cv mpbid axpasch simp1l1 simp2 simpl22 simp3l simp1r1 simpll1 syl simpll2
      wb simplr simpl3r anim1i btwnexch2 ex anim1d reximdva mpd rexlimdv3a ) GU
      DJZAGUAUBZJZBVPJZCVPJZKZDVPJZFVPJZEVPJZKZKZBACLMNZFDCLMNZEADLMNZKZHUNZECL
      ZMNZWJBFLMNZOZHVPPZWEWIOZIUNZFALMNZWQWKMNZOZIVPPZWOWPVOVSVQWAKZWBWCOZKFCD
      LMNZWHOXAWPVOXBXCVOVTWDWIUCZWPVSVQWAVQVRVSVOWDWIUEZVQVRVSVOWDWIUFZWAWBWCV
      OVTWIUGZQWPWBWCWAWBWCVOVTWIUHZWAWBWCVOVTWIUIZRQWPXDWHWPWGXDWEWFWGWHUJWPVO
      WBWAVSWGXDVEXEXIXHXFFDCGUKULUOWEWFWGWHUMRICADFEGUPSWPWTWOIVPWPWQVPJZWTKZW
      JWQCLMNZWMOZHVPPZWOXLVOWBVSVQKZXKVROZKWRBCALMNZOXOXLVOXPXQVOVTWDWIXKWTUQZ
      XLWBVSVQWPXKWBWTXITWPXKVSWTXFTZWPXKVQWTXGTZQXLXKVRWPXKWTURWPXKVRWTVQVRVSV
      OWDWIUSTZRQXLWRXRWPXKWRWSUTXLWFXRWFWGWHWEXKWTVAXLVOVRVQVSWFXRVEXSYBYAXTBA
      CGUKULUORHFCAWQBGUPSXLXNWNHVPXLWJVPJZOZXMWLWMYDXMWLYDXMOZVOWCXKOZYCVSOZKW
      SXMOWLYEVOYFYGYEWPVOWPXKWTYCXMVBZXEVCYEWCXKYEWPWCYHXJVCWPXKWTYCXMVDRYEYCV
      SXLYCXMVFYEWPVSYHXFVCRQYDWSXMWRWSWPXKYCVGVHEWQWJCGVISVJVKVLVMVNVMVJ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Segment Transportation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c TransportTo $.

  $( Declare the syntax for the segment transport function. $)
  ctransport $a class TransportTo $.

  ${
    $d n p q r x $.
    $( Define the segment transport function.  See ~ fvtransport for an
       explanation of the function.  (Contributed by Scott Fenton,
       18-Oct-2013.) $)
    df-transport $a |- TransportTo =
       { <. <. p , q >. , x >. |
         E. n e. NN ( ( p e. ( ( EE ` n ) X. ( EE ` n ) ) /\
                        q e. ( ( EE ` n ) X. ( EE ` n ) ) /\
                        ( 1st ` q ) =/= ( 2nd ` q ) ) /\
                      x = ( iota_ r e. ( EE ` n )
                        ( ( 2nd ` q ) Btwn <. ( 1st ` q ) , r >. /\
                        <. ( 2nd ` q ) , r >. Cgr p ) ) ) } $.
  $}

  ${
    $d m n p q r x y $.
    $( The ` TransportTo ` relationship is a function.  (Contributed by Scott
       Fenton, 18-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    funtransport $p |- Fun TransportTo $=
      ( vp vn vq vx vr vm vy ctransport wfun cv cee cfv cxp wcel c1st w3a wa cn
      wceq wrex c2nd wne cop cbtwn wbr ccgr crio coprab wmo weq wi reeanv simp1
      wal anim12i anim1i an4s xp1st axdimuniq riotaeqdv eqeq2d anbi2d biimtrrdi
      fveq2 eqtr3 syl ex syl2ani impd syl5 rexlimivv gen2 eqeq1 rexbidv sqxpeqd
      sylbir eleq2d 3anbi12d cbvrexvw bitrdi mpbir funoprab df-transport funeqi
      anbi12d mo4 ) HIAJZBJZKLZWIMZNZCJZWJNZWLOLZWLUALZUBZPZDJZWOWNEJZUCUDUEWOW
      SUCWGUFUEQZEWIUGZSZQZBRTZACDUHZIXDACDXDDUIXDWGFJZKLZXGMZNZWLXHNZWPPZGJZWT
      EXGUGZSZQZFRTZQZDGUJZUKZGUNDUNXSDGXQXCXOQZFRTBRTXRXCXOBFRRULXTXRBFRRXTWKX
      IQZXBXNQZQZWHRNZXFRNZQZXRWQXKXBXNYCWQXKQYAYBWQWKXKXIWKWMWPUMXIXJWPUMUOUPU
      QYFYAYBXRWKYFWGOLZWINZYGXGNZYBXRUKZXIWGWIWIURWGXGXGURYFYHYIQYJYDYHYEYIYJY
      DYHQYEYIQQBFUJZYJYGXFWHUSYKYBXBXLXASZQXRYKYLXNXBYKXAXMXLYKWTEWIXGWHXFKVDZ
      UTVAZVBWRXLXAVEVCVFUQVGVHVIVJVKVPVLXDXPDGXRXDWQYLQZBRTXPXRXCYOBRXRXBYLWQW
      RXLXAVMVBVNYOXOBFRYKWQXKYLXNYKWKXIWMXJWPYKWJXHWGYKWIXGYMVOZVQYKWJXHWLYPVQ
      VRYNWEVSVTWFWAWBHXEDBECAWCWDWA $.
  $}

  ${
    $d N n p q r x $.  $d A n p q r x $.  $d B n p q r x $.  $d C n p q r x $.
    $d D n p q r x $.
    $( Calculate the value of the ` TransportTo ` function.  This function
       takes four points, ` A ` through ` D ` , where ` C ` and ` D ` are
       distinct.  It then returns the point that extends ` C D ` by the length
       of ` A B ` .  (Contributed by Scott Fenton, 18-Oct-2013.)  (Revised by
       Mario Carneiro, 19-Apr-2014.) $)
    fvtransport $p |- ( ( N e. NN /\
       ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) /\
         C =/= D ) ) ->
       ( <. A , B >. TransportTo <. C , D >. ) =
       ( iota_ r e. ( EE ` N ) ( D Btwn <. C , r >. /\
         <. D , r >. Cgr <. A , B >. ) ) ) $=
      ( vn cn wcel cfv wa w3a cop ctransport cv cbtwn wbr ccgr wceq cvv cee wne
      vp vq vx co crio df-ov cxp c1st c2nd wrex opelxpi 3ad2ant1 3ad2ant2 simp3
      op1stg op2ndg 3netr4d 3jca opeq1d breq12d breq1d anbi12d riotabidv eqcomd
      fveq2 sqxpeqd eleq2d 3anbi12d riotaeqdv eqeq2d rspcev sylan2 coprab df-br
      jca df-transport eleq2i opex riotaex eleq1 3anbi1d anbi2d rexbidv neeq12d
      wb breq2 3anbi23d eqeq1 eloprabg mp3an wfun wi funtransport funbrfv ax-mp
      3bitri sylbir syl eqtrid ) EHIZAEUAJZIBXCIKZCXCIDXCIKZCDUBZLZKZABMZCDMZNU
      FXIXJMZNJZDCFOZMZPQZDXMMZXIRQZKZFXCUGZXIXJNUHXHXIGOZUAJZYAUIZIZXJYBIZXJUJ
      JZXJUKJZUBZLZXSYFYEXMMZPQZYFXMMZXIRQZKZFYAUGZSZKZGHULZXLXSSZXGXBXIXCXCUIZ
      IZXJYSIZYGLZXSYMFXCUGZSZKZYQXGUUBUUDXGYTUUAYGXDXEYTXFABXCXCUMUNXEXDUUAXFC
      DXCXCUMUOXGCDYEYFXDXEXFUPXEXDYECSXFCDXCXCUQUOZXEXDYFDSXFCDXCXCURUOZUSUTXG
      UUCXSXGYMXRFXCXGYJXOYLXQXGYFDYIXNPUUGXGYECXMUUFVAVBXGYKXPXIRXGYFDXMUUGVAV
      CVDVEVFVQYPUUEGEHXTESZYHUUBYOUUDUUHYCYTYDUUAYGUUHYBYSXIUUHYAXCXTEUAVGZVHZ
      VIUUHYBYSXJUUJVIVJUUHYNUUCXSUUHYMFYAXCUUIVKVLVDVMVNYQXKXSNQZYRUUKXKXSMZNI
      UULUCOZYBIZUDOZYBIZUUOUJJZUUOUKJZUBZLZUEOZUURUUQXMMZPQZUURXMMZUUMRQZKZFYA
      UGZSZKZGHULZUCUDUEVOZIZYQXKXSNVPNUVKUULUEGFUDUCVRVSXITIXJTIXSTIUVLYQWGABV
      TCDVTXRFXCWAUVJYCUUPUUSLZUVAUVCUVDXIRQZKZFYAUGZSZKZGHULYHUVAYNSZKZGHULYQU
      CUDUEXIXJXSTTTUUMXISZUVIUVRGHUWAUUTUVMUVHUVQUWAUUNYCUUPUUSUUMXIYBWBWCUWAU
      VGUVPUVAUWAUVFUVOFYAUWAUVEUVNUVCUUMXIUVDRWHWDVEVLVDWEUUOXJSZUVRUVTGHUWBUV
      MYHUVQUVSUWBUUPYDUUSYGYCUUOXJYBWBUWBUUQYEUURYFUUOXJUJVGZUUOXJUKVGZWFWIUWB
      UVPYNUVAUWBUVOYMFYAUWBUVCYJUVNYLUWBUURYFUVBYIPUWDUWBUUQYEXMUWCVAVBUWBUVDY
      KXIRUWBUURYFXMUWDVAVCVDVEVLVDWEUVAXSSZUVTYPGHUWEUVSYOYHUVAXSYNWJWDWEWKWLW
      RNWMUUKYRWNWOXKXSNWPWQWSWTXA $.
  $}

  ${
    $d N r $.  $d A r $.  $d B r $.  $d C r $.  $d D r $.
    $( Closure law for segment transport.  (Contributed by Scott Fenton,
       19-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    transportcl $p |- ( ( N e. NN /\
       ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) /\
         C =/= D ) ) ->
       ( <. A , B >. TransportTo <. C , D >. ) e. ( EE ` N ) ) $=
      ( vr cn wcel cee cfv wa wne w3a cop ctransport co cv cbtwn wbr ccgr crio
      fvtransport wreu segconeu riotacl syl eqeltrd ) EGHAEIJZHBUHHKCUHHDUHHKCD
      LMKZABNZCDNOPDCFQZNRSDUKNUJTSKZFUHUAZUHABCDEFUBUIULFUHUCUMUHHABCDEFUDULFU
      HUEUFUG $.

    $( Calculate the defining properties of the transport function.
       (Contributed by Scott Fenton, 19-Oct-2013.)  (Revised by Mario Carneiro,
       19-Apr-2014.) $)
    transportprops $p |- ( ( N e. NN /\
       ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) /\
         C =/= D ) ) ->
         ( D Btwn <. C , ( <. A , B >. TransportTo <. C , D >. ) >. /\
           <. D , ( <. A , B >. TransportTo <. C , D >. ) >. Cgr
           <. A , B >. ) ) $=
      ( vr cn wcel cee cfv wa wne w3a cop ctransport cbtwn wbr ccgr wceq opeq2
      co cv crio fvtransport eqcomd wreu wb transportcl segconeu breq2d anbi12d
      breq1d riota2 syl2anc mpbird ) EGHAEIJZHBUPHKCUPHDUPHKCDLMKZDCABNZCDNOUAZ
      NZPQZDUSNZURRQZKZDCFUBZNZPQZDVENZURRQZKZFUPUCZUSSZUQUSVKABCDEFUDUEUQUSUPH
      VJFUPUFVDVLUGABCDEUHABCDEFUIVJVDFUPUSVEUSSZVGVAVIVCVMVFUTDPVEUSCTUJVMVHVB
      URRVEUSDTULUKUMUNUO $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Properties relating betweenness and congruence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c InnerFiveSeg Cgr3 Colinear FiveSeg $.

  $( Declare the syntax for the inner five segment predicate. $)
  cifs $a class InnerFiveSeg $.

  $( Declare the syntax for the three place congruence predicate. $)
  ccgr3 $a class Cgr3 $.

  $( Declare the syntax for the colinearity predicate. $)
  ccolin $a class Colinear $.

  $( Declare the syntax for the five segment predicate. $)
  cfs $a class FiveSeg $.

  ${
    $d a b c n $.
    $( The colinearity predicate states that the three points in its arguments
       sit on one line.  Definition 4.10 of [Schwabhauser] p. 36.  (Contributed
       by Scott Fenton, 25-Oct-2013.) $)
    df-colinear $a |- Colinear = `' { <. <. b , c >. , a >. |
       E. n e. NN ( ( a e. ( EE ` n ) /\ b e. ( EE ` n ) /\ c e. ( EE ` n ) )
         /\
         ( a Btwn <. b , c >. \/ b Btwn <. c , a >. \/
           c Btwn <. a , b >. ) ) } $.
  $}

  ${
    $d a b c d x y z w p q n $.
    $( The inner five segment configuration is an abbreviation for another
       congruence condition.  See ~ brifs and ~ ifscgr for how it is used.
       Definition 4.1 of [Schwabhauser] p. 34.  (Contributed by Scott Fenton,
       26-Sep-2013.) $)
    df-ifs $a |- InnerFiveSeg =
        { <. p , q >. |
           E. n e. NN E. a e. ( EE ` n ) E. b e. ( EE ` n ) E. c e. ( EE ` n )
           E. d e. ( EE ` n ) E. x e. ( EE ` n ) E. y e. ( EE ` n )
           E. z e. ( EE ` n ) E. w e. ( EE ` n ) (
           p = <. <. a , b >. , <. c , d >. >. /\
           q = <. <. x , y >. , <. z , w >. >. /\
           ( ( b Btwn <. a , c >. /\ y Btwn <. x , z >. ) /\
             ( <. a , c >. Cgr <. x , z >. /\
               <. b , c >. Cgr <. y , z >. ) /\
             ( <. a , d >. Cgr <. x , w >. /\
               <. c , d >. Cgr <. z , w >. ) ) ) } $.
  $}

  ${
    $d a b c d e f n p q $.
    $( The three place congruence predicate.  This is an abbreviation for
       saying that all three pair in a triple are congruent with each other.
       Three place form of Definition 4.4 of [Schwabhauser] p. 35.
       (Contributed by Scott Fenton, 4-Oct-2013.) $)
    df-cgr3 $a |- Cgr3 = { <. p , q >. |
       E. n e. NN E. a e. ( EE ` n ) E. b e. ( EE ` n ) E. c e. ( EE ` n )
       E. d e. ( EE ` n ) E. e e. ( EE ` n ) E. f e. ( EE ` n )
       ( p = <. a , <. b , c >. >. /\
       q = <. d , <. e , f >. >. /\
       ( <. a , b >. Cgr <. d , e >. /\ <. a , c >. Cgr <. d , f >. /\
         <. b , c >. Cgr <. e , f >. ) ) } $.
  $}

  ${
    $d a b c d x y z w p q n $.
    $( The general five segment configuration is a generalization of the outer
       and inner five segment configurations.  See ~ brfs and ~ fscgr for its
       use.  Definition 4.15 of [Schwabhauser] p. 37.  (Contributed by Scott
       Fenton, 5-Oct-2013.) $)
    df-fs $a |- FiveSeg =
        { <. p , q >. |
           E. n e. NN E. a e. ( EE ` n ) E. b e. ( EE ` n ) E. c e. ( EE ` n )
           E. d e. ( EE ` n ) E. x e. ( EE ` n ) E. y e. ( EE ` n )
           E. z e. ( EE ` n ) E. w e. ( EE ` n ) (
           p = <. <. a , b >. , <. c , d >. >. /\
           q = <. <. x , y >. , <. z , w >. >. /\
           ( a Colinear <. b , c >. /\
             <. a , <. b , c >. >. Cgr3 <. x , <. y , z >. >. /\
             ( <. a , d >. Cgr <. x , w >. /\
               <. b , d >. Cgr <. y , w >. ) ) ) } $.
  $}

  ${
    $d N a b c d e f g h p q n $.  $d A a b c d e f g h p q n $.
    $d B a b c d e f g h p q n $.  $d C a b c d e f g h p q n $.
    $d D a b c d e f g h p q n $.  $d E a b c d e f g h p q n $.
    $d F a b c d e f g h p q n $.  $d G a b c d e f g h p q n $.
    $d H a b c d e f g h p q n $.
    $( Binary relation form of the inner five segment predicate.  (Contributed
       by Scott Fenton, 26-Sep-2013.) $)
    brifs $p |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
        ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\
        ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) ->
    ( <. <. A , B >. , <. C , D >. >. InnerFiveSeg
      <. <. E , F >. , <. G , H >. >. <-> ( ( B Btwn <. A , C >. /\
                     F Btwn <. E , G >. ) /\
        ( <. A , C >. Cgr <. E , G >. /\
          <. B , C >. Cgr <. F , G >. ) /\
        ( <. A , D >. Cgr <. E , H >. /\
          <. C , D >. Cgr <. G , H >. ) ) ) ) $=
      ( cv cop cbtwn wbr wa ccgr w3a wceq opeq1 breq2d breq1d vb va vc vf ve vg
      vd vh vn vq vp cee cifs cn anbi1d 3anbi123d breq1 anbi2d 3anbi12d anbi12d
      cfv opeq2 3anbi3d fveq2 df-ifs br8 ) UAJZUBJZUCJZKZLMZUDJZUEJZUFJZKZLMZNZ
      VJVOOMZVGVIKZVLVNKZOMZNZVHUGJZKZVMUHJZKZOMZVIWCKZVNWEKZOMZNZPVGAVIKZLMZVP
      NZWLVOOMZWANZAWCKZWFOMZWJNZPBWLLMZVPNZWOBVIKZVTOMZNZWSPBACKZLMZVPNZXEVOOM
      ZBCKZVTOMZNZWRCWCKZWIOMZNZPXGXKADKZWFOMZCDKZWIOMZNZPXFVLEVNKZLMZNZXEXTOMZ
      XJNZXOEWEKZOMZXRNZPXFFXTLMZNZYCXIFVNKZOMZNZYGPXFFEGKZLMZNZXEYMOMZXIFGKZOM
      ZNZYFXQGWEKZOMZNZPYOYSXOEHKZOMZXQGHKZOMZNZPUIABCDUIJZULVAIULVAUMUNUEUDUFU
      HEFGHIUJUKUBUAUCUGVHAQZVQWNWBWPWKWSUUIVKWMVPUUIVJWLVGLVHAVIRZSUOUUIVRWOWA
      UUIVJWLVOOUUJTUOUUIWGWRWJUUIWDWQWFOVHAWCRTUOUPVGBQZWNXAWPXDWSUUKWMWTVPVGB
      WLLUQUOUUKWAXCWOUUKVSXBVTOVGBVIRTURUSVICQZXAXGXDXKWSXNUULWTXFVPUULWLXEBLV
      ICAVBZSUOUULWOXHXCXJUULWLXEVOOUUMTUULXBXIVTOVICBVBTUTUULWJXMWRUULWHXLWIOV
      ICWCRTURUPWCDQZXNXSXGXKUUNWRXPXMXRUUNWQXOWFOWCDAVBTUUNXLXQWIOWCDCVBTUTVCV
      MEQZXGYBXKYDXSYGUUOVPYAXFUUOVOXTVLLVMEVNRZSURUUOXHYCXJUUOVOXTXEOUUPSUOUUO
      XPYFXRUUOWFYEXOOVMEWERSUOUPVLFQZYBYIYDYLYGUUQYAYHXFVLFXTLUQURUUQXJYKYCUUQ
      VTYJXIOVLFVNRSURUSVNGQZYIYOYLYSYGUUBUURYHYNXFUURXTYMFLVNGEVBZSURUURYCYPYK
      YRUURXTYMXEOUUSSUURYJYQXIOVNGFVBSUTUURXRUUAYFUURWIYTXQOVNGWERSURUPWEHQZUU
      BUUGYOYSUUTYFUUDUUAUUFUUTYEUUCXOOWEHEVBSUUTYTUUEXQOWEHGVBSUTVCUUHIULVDUEU
      DUFUHUIUJUKUBUAUCUGVEVF $.
  $}

  ${
    $d A e f $.  $d B e f $.  $d C e f $.  $d D e f $.  $d E e f $.
    $d F e f $.  $d G e f $.  $d H e f $.  $d N e f $.
    $( Inner five segment congruence.  Take two triangles, ` A D C ` and
       ` E H G ` , with ` B ` between ` A ` and ` C ` and ` F ` between ` E `
       and ` G ` .  If the other components of the triangles are congruent,
       then so are ` B D ` and ` F H ` .  Theorem 4.2 of [Schwabhauser] p. 34.
       (Contributed by Scott Fenton, 27-Sep-2013.) $)
    ifscgr $p |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
        ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\
        ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) ->
    ( <. <. A , B >. , <. C , D >. >. InnerFiveSeg
      <. <. E , F >. , <. G , H >. >. -> <. B , D >. Cgr <. F , H >. ) ) $=
      ( wcel w3a cop wbr cbtwn wa ccgr wi jca wb adantr ve vf cn cee cifs brifs
      cfv wceq simp1l simp11 simp13 simp21 axbtwnid syl3anc simp2r simp3r opeq2
      syl5 breq1d opeq1 anbi12d mpan9 simp31 simp32 cgrid2 syl13anc breq2d syl6
      biimprd impd expd mpdd anbi1d 3anbi12d imbi1d imbitrrid wne wrex btwndiff
      cv simpl11 simpl23 simpl32 simpl21 simpr axsegcon syl122anc anass simplrl
      simp12 cofs adantl simplll simpr2l simpllr ad2antrr simplrr mpbid simprr3
      cgrcom 3jca simpl12 simprl simpl22 simprr simpl33 brofs syl333anc sylibrd
      ex 5segofs syland simpr1l simpr1r jca32 simpl13 btwnexch3 simpl31 anim12d
      imp btwncom ad2antrl cgrcomlr simpr2r cgrcomlrand simpr3r necomd a1i jcad
      bitrd syld adantrd biimtrrid anassrs rexlimdva mpd com3r pm2.61ine sylbid
      ) IUCJZAIUDUGZJZBUUAJZKZCUUAJZDUUAJZEUUAJZKZFUUAJZGUUAJZHUUAJZKZKZABLCDLZ
      LEFLGHLZLUEMBACLZNMZFEGLZNMZOZUUPUURPMZBCLZFGLZPMZOZADLEHLPMZUUNUUOPMZOZK
      ZBDLZFHLZPMZABCDEFGHIUFUUMUVIUVLQZQACUUMUVMACUHZBCCLZNMZUUSOZUVOUURPMZUVD
      OZUVHKZUVLQUUMUVTBCUHZUVLUVTUVPUUMUWAUVPUUSUVSUVHUIUUMYTUUCUUEUVPUWAQYTUU
      BUUCUUHUULUJZYTUUBUUCUUHUULUKZUUDUUEUUFUUGUULULZBCIUMUNURUUMUVTUWAUVLUVTU
      WAOBBLZUVCPMZUVJUUOPMZOZUUMUVLUVTUVDUVGOZUWAUWHUVTUVDUVGUVQUVRUVDUVHUOUVQ
      UVSUVFUVGUPRUWAUWHUWIUWAUWFUVDUWGUVGUWAUWEUVBUVCPBCBUQUSUWAUVJUUNUUOPBCDU
      TUSVAVIVBUUMUWFUWGUVLUUMUWFFGUHZUWGUVLQUUMYTUUCUUIUUJUWFUWJQUWBUWCUUDUUHU
      UIUUJUUKVCUUDUUHUUIUUJUUKVDZBFGIVEVFUWJUVLUWGUWJUVKUUOUVJPFGHUTVGVIVHVJUR
      VKVLUVNUVIUVTUVLUVNUUTUVQUVEUVSUVHUVNUUQUVPUUSUVNUUPUVOBNACCUTZVGVMUVNUVA
      UVRUVDUVNUUPUVOUURPUWLUSVMVNVOVPUUMUVIACVQZUVLUUMUVIUWMUVLUUMCAUAVTZLNMZC
      UWNVQZOZUAUUAVRZUVIUWMOZUVLQZUUMYTUUBUUEUWRUWBYTUUBUUCUUHUULWJUWDACIUAVSU
      NUUMUWQUWTUAUUAUUMUWNUUAJZOZUWQUWSUVLUXBGEUBVTZLNMZGUXCLZCUWNLZPMZOZUBUUA
      VRZUWQUWSOZUVLQZUXBYTUUGUUJUUEUXAUXIYTUUBUUCUUHUULUXAWAUUEUUFUUGUUDUULUXA
      WBUUIUUJUUKUUDUUHUXAWCUUEUUFUUGUUDUULUXAWDUUMUXAWEUBEGCUWNIWFWGUXBUXHUXKU
      BUUAUUMUXAUXCUUAJZUXHUXKQUUMUXAUXLOZOZUXHUXJUVLUXHUXJOUXHUWQOZUWSOZUXNUVL
      UXHUWQUWSWHUXPUXOUVIOZUWMOZUXNUVLUXOUVIUWMWHUXNUXRUWNDLZUXCHLZPMZUVLUXNUX
      QUUPUXSLUURUXTLWKMZUWMUYAUXNUXQUWOUXDOZUVAUXFUXEPMZOZUVHKZUYBUXNUXQUYFUXN
      UXQOZUYCUYEUVHUYGUWOUXDUXQUWOUXNUXHUWOUWPUVIWIZWLUXQUXDUXNUXDUXGUWQUVIWMZ
      WLRUYGUVAUYDUXQUVAUXNUVAUVDUUTUVHUXOWNWLUYGUXGUYDUXQUXGUXNUXDUXGUWQUVIWOZ
      WLUYGYTUUJUXLUUEUXAUXGUYDSZUUMYTUXMUXQUWBWPUUMUUJUXMUXQUWKWPUUMUXAUXLUXQW
      QUUMUUEUXMUXQUWDWPUUMUXAUXLUXQWIGUXCCUWNIWTZWGWRRUUTUVEUVHUXOUXNWSXAXJUXN
      YTUUBUUEUXAUUFUUGUUJUXLUUKUYBUYFSYTUUBUUCUUHUULUXMWAZYTUUBUUCUUHUULUXMXBZ
      UUEUUFUUGUUDUULUXMWDZUUMUXAUXLXCZUUEUUFUUGUUDUULUXMXDZUUEUUFUUGUUDUULUXMW
      BZUUIUUJUUKUUDUUHUXMWCZUUMUXAUXLXEZUUIUUJUUKUUDUUHUXMXFZACUWNDEGUXCHIXGXH
      XIUXNYTUUBUUEUXAUUFUUGUUJUXLUUKUYBUWMOUYAQUYMUYNUYOUYPUYQUYRUYSUYTVUAACUW
      NDEGUXCHIXKXHXLUXNUXQUYAUVLQUWMUXNUXQUYAUVLUXNUXQUYAOZUWNCLZUVJLUXCGLZUVK
      LWKMZUWNCVQZOZUVLUXNVUBVUEVUFUXNVUBCUWNBLNMZGUXCFLNMZOZVUCVUDPMZCBLGFLPMZ
      OZUYAUVGOZKZVUEUXNVUBVUOUXNVUBOZVUJVUMVUNVUPCBUWNLNMZGFUXCLNMZOZVUJUXNVUB
      VUSVUBUUQUWOOZUUSUXDOZOUXNVUSVUBVUTUUSUXDVUBUUQUWOUXQUUQUYAUUQUUSUVEUVHUX
      OXMTUXQUWOUYAUYHTRUXQUUSUYAUUQUUSUVEUVHUXOXNTUXQUXDUYAUYITXOUXNVUTVUQVVAV
      URUXNYTUUBUUCUUEUXAVUTVUQQUYMUYNYTUUBUUCUUHUULUXMXPZUYOUYPABCUWNIXQWGUXNY
      TUUGUUIUUJUXLVVAVURQUYMUYRUUIUUJUUKUUDUUHUXMXRZUYSUYTEFGUXCIXQWGXSURXTUXN
      VUSVUJSVUBUXNVUQVUHVURVUIUXNYTUUEUUCUXAVUQVUHSUYMUYOVVBUYPCBUWNIYAVFUXNYT
      UUJUUIUXLVURVUISUYMUYSVVCUYTGFUXCIYAVFVATWRVUPVUKVULVUPUXGVUKUXQUXGUXNUYA
      UYJYBUXNUXGVUKSVUBUXNUXGUYDVUKUXNYTUUJUXLUUEUXAUYKUYMUYSUYTUYOUYPUYLWGUXN
      YTUUEUXAUUJUXLUYDVUKSUYMUYOUYPUYSUYTCUWNGUXCIYCWGYJTWRUXNVUBBCFGIUYMVVBUY
      OVVCUYSUXQUVDUXNUYAUVAUVDUUTUVHUXOYDYBYERVUPUYAUVGUXNUXQUYAXEUXQUVGUXNUYA
      UVFUVGUUTUVEUXOYFYBRXAXJUXNYTUXAUUEUUCUUFUXLUUJUUIUUKVUEVUOSUYMUYPUYOVVBU
      YQUYTUYSVVCVUAUWNCBDUXCGFHIXGXHXIVUBVUFQUXNVUBCUWNUXQUWPUYAUXHUWOUWPUVIWQ
      TYGYHYIUXNYTUXAUUEUUCUUFUXLUUJUUIUUKVUGUVLQUYMUYPUYOVVBUYQUYTUYSVVCVUAUWN
      CBDUXCGFHIXKXHYKVKYLVLYMYMVKYNYOYPVKYOYPVKYQYRYS $.
  $}

  $( Removing identical parts from the end of a line segment preserves
     congruence.  Theorem 4.3 of [Schwabhauser] p. 35.  (Contributed by Scott
     Fenton, 4-Oct-2013.) $)
  cgrsub $p |- ( ( N e. NN /\
         ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
         ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
         ( ( ( B Btwn <. A , C >. /\ E Btwn <. D , F >. ) /\
             ( <. A , C >. Cgr <. D , F >. /\ <. B , C >. Cgr <. E , F >. ) )
           -> <. A , B >. Cgr <. D , E >. ) ) $=
    ( cn wcel cee w3a cop cbtwn wbr wa ccgr wb cgrcomlr syl122anc mpbid simpl21
    cfv simprl simprr simpl1 simpl31 cgrtriv syl3anc simprrl simpl23 simpl33 wi
    jca simpl22 simpl32 cifs brifs ifscgr sylbird syl333anc mp3and ex ) GHIZAGJ
    UBZIZBVDIZCVDIZKZDVDIZEVDIZFVDIZKZKZBACLZMNEDFLZMNOZVNVOPNZBCLEFLPNZOZOZABL
    ZDELZPNZVMVTOZBALEDLPNZWCWDVPVSAALDDLPNZCALZFDLZPNZOZWEVMVPVSUCVMVPVSUDWDWF
    WIWDVCVEVIWFVCVHVLVTUEZVEVFVGVCVLVTUAZVIVJVKVCVHVTUFZADGUGUHWDVQWIVMVPVQVRU
    IWDVCVEVGVIVKVQWIQWKWLVEVFVGVCVLVTUJZWMVIVJVKVCVHVTUKZACDFGRSTUMWDVCVEVFVGV
    EVIVJVKVIVPVSWJKZWEULWKWLVEVFVGVCVLVTUNZWNWLWMVIVJVKVCVHVTUOZWOWMVCVEVFKVGV
    EVIKVJVKVIKKWPWAWGLWBWHLUPNWEABCADEFDGUQABCADEFDGURUSUTVAWDVCVFVEVJVIWEWCQW
    KWQWLWRWMBAEDGRSTVB $.

  ${
    $d A a b c d e f n p q $.  $d B a b c d e f n p q $.
    $d C a b c d e f n p q $.  $d D a b c d e f n p q $.
    $d E a b c d e f n p q $.  $d F a b c d e f n p q $.
    $d N a b c d e f n p q $.
    $( Binary relation form of the three-place congruence predicate.
       (Contributed by Scott Fenton, 4-Oct-2013.) $)
    brcgr3 $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
       ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. <->
         ( <. A , B >. Cgr <. D , E >. /\ <. A , C >. Cgr <. D , F >. /\
           <. B , C >. Cgr <. E , F >. ) ) ) $=
      ( va vb vd cv cop ccgr wbr w3a wceq opeq1 breq1d opeq2 breq2d ve vc vf vn
      vq vp cee cfv ccgr3 cn 3anbi12d 3anbi13d 3anbi23d fveq2 df-cgr3 br6 ) HKZ
      IKZLZJKZUAKZLZMNZUQUBKZLZUTUCKZLZMNZURVDLZVAVFLZMNZOAURLZVBMNZAVDLZVGMNZV
      KOABLZVBMNZVOBVDLZVJMNZOVQACLZVGMNZBCLZVJMNZOVPDVALZMNZVTDVFLZMNZWCOVPDEL
      ZMNZWGWBEVFLZMNZOWIVTDFLZMNZWBEFLZMNZOUDABCDUDKZUGUHGUGUHUIUJUAUCEFGUEUFH
      IUBJUQAPZVCVMVHVOVKWQUSVLVBMUQAURQRWQVEVNVGMUQAVDQRUKURBPZVMVQVKVSVOWRVLV
      PVBMURBASRWRVIVRVJMURBVDQRULVDCPZVOWAVSWCVQWSVNVTVGMVDCASRWSVRWBVJMVDCBSR
      UMUTDPZVQWEWAWGWCWTVBWDVPMUTDVAQTWTVGWFVTMUTDVFQTUKVAEPZWEWIWCWKWGXAWDWHV
      PMVAEDSTXAVJWJWBMVAEVFQTULVFFPZWGWMWKWOWIXBWFWLVTMVFFDSTXBWJWNWBMVFFESTUM
      WPGUGUNUAUCUDUEUFHIUBJUOUP $.
  $}

  $( Permutation law for three-place congruence.  (Contributed by Scott Fenton,
     5-Oct-2013.) $)
  cgr3permute3 $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
       ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. <->
         <. B , <. C , A >. >. Cgr3 <. E , <. F , D >. >. ) ) $=
    ( wcel w3a cop ccgr wbr ccgr3 wa wb 3simpa cgrcomlr syl3an 3simpb 3anrot cn
    cee cfv id 3anbi12d bitr4di brcgr3 biid syl3anb 3bitr4d ) GUAHZAGUBUCZHZBUL
    HZCULHZIZDULHZEULHZFULHZIZIZABJDEJKLZACJDFJKLZBCJZEFJZKLZIZVFBAJEDJKLZCAJZF
    DJZKLZIZAVDJDVEJMLBVIJEVJJMLZVAVGVHVKVFIVLVAVBVHVCVKVFUKUKUPUMUNNUTUQURNVBV
    HOUKUDZUMUNUOPUQURUSPABDEGQRUKUKUPUMUONUTUQUSNVCVKOVNUMUNUOSUQURUSSACDFGQRU
    EVFVHVKTUFABCDEFGUGUKUKUPUNUOUMIUTURUSUQIVMVLOUKUHUMUNUOTUQURUSTBCAEFDGUGUI
    UJ $.

  $( Permutation law for three-place congruence.  (Contributed by Scott Fenton,
     5-Oct-2013.) $)
  cgr3permute1 $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
       ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. <->
         <. A , <. C , B >. >. Cgr3 <. D , <. F , E >. >. ) ) $=
    ( cn wcel cee w3a cop ccgr wbr ccgr3 wa wb 3simpc brcgr3 3ancomb cfv syl3an
    id cgrcomlr 3anbi3d 3ancoma bitrdi biid syl3anb 3bitr4d ) GHIZAGJUAZIZBULIZ
    CULIZKZDULIZEULIZFULIZKZKZABLDELMNZACLDFLMNZBCLZEFLZMNZKZVCVBCBLZFELZMNZKZA
    VDLDVELONAVHLDVILONZVAVGVBVCVJKVKVAVFVJVBVCUKUKUPUNUOPUTURUSPVFVJQUKUCUMUNU
    ORUQURUSRBCEFGUDUBUEVBVCVJUFUGABCDEFGSUKUKUPUMUOUNKUTUQUSURKVLVKQUKUHUMUNUO
    TUQURUSTACBDFEGSUIUJ $.

  $( Permutation law for three-place congruence.  (Contributed by Scott Fenton,
     5-Oct-2013.) $)
  cgr3permute2 $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
       ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. <->
         <. B , <. A , C >. >. Cgr3 <. E , <. D , F >. >. ) ) $=
    ( cn wcel cee cfv w3a cop ccgr3 wbr cgr3permute3 biid 3anrot cgr3permute1
    wb syl3anb bitrd ) GHIZAGJKZIZBUDIZCUDIZLZDUDIZEUDIZFUDIZLZLABCMMDEFMMNOBCA
    MMEFDMMNOZBACMMEDFMMNOZABCDEFGPUCUCUHUFUGUELULUJUKUILUMUNTUCQUEUFUGRUIUJUKR
    BCAEFDGSUAUB $.

  $( Permutation law for three-place congruence.  (Contributed by Scott Fenton,
     5-Oct-2013.) $)
  cgr3permute4 $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
       ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. <->
         <. C , <. A , B >. >. Cgr3 <. F , <. D , E >. >. ) ) $=
    ( cn wcel cee cfv w3a cop ccgr3 wbr cgr3permute3 wb biid 3anrot syl3anb
    bitrd ) GHIZAGJKZIZBUCIZCUCIZLZDUCIZEUCIZFUCIZLZLABCMMDEFMMNOBCAMMEFDMMNOZC
    ABMMFDEMMNOZABCDEFGPUBUBUGUEUFUDLUKUIUJUHLULUMQUBRUDUEUFSUHUIUJSBCAEFDGPTUA
    $.

  $( Permutation law for three-place congruence.  (Contributed by Scott Fenton,
     5-Oct-2013.) $)
  cgr3permute5 $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
       ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. <->
         <. C , <. B , A >. >. Cgr3 <. F , <. E , D >. >. ) ) $=
    ( cn wcel cee cfv w3a cop ccgr3 wbr cgr3permute3 biid 3anrot cgr3permute2
    wb syl3anb bitrd ) GHIZAGJKZIZBUDIZCUDIZLZDUDIZEUDIZFUDIZLZLABCMMDEFMMNOBCA
    MMEFDMMNOZCBAMMFEDMMNOZABCDEFGPUCUCUHUFUGUELULUJUKUILUMUNTUCQUEUFUGRUIUJUKR
    BCAEFDGSUAUB $.

  $( Transitivity law for three-place congruence.  (Contributed by Scott
     Fenton, 5-Oct-2013.) $)
  cgr3tr4 $p |- ( ( N e. NN /\
    ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
      ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) /\
      ( G e. ( EE ` N ) /\ H e. ( EE ` N ) /\ I e. ( EE ` N ) ) ) ) ->
    ( ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. /\
        <. A , <. B , C >. >. Cgr3 <. G , <. H , I >. >. ) ->
      <. D , <. E , F >. >. Cgr3 <. G , <. H , I >. >. ) ) $=
    ( wcel w3a wa cop ccgr wbr ccgr3 wi axcgrtr syl133anc cn cee cfv 3an6 simpl
    simpr11 simpr12 simpr21 simpr22 simpr31 simpr32 simpr13 3anim123d biimtrrid
    simpr23 simpr33 wb brcgr3 3adant3r3 3adant3r2 anbi12d 3adant3r1 3imtr4d ) J
    UAKZAJUBUCZKZBVEKZCVEKZLZDVEKZEVEKZFVEKZLZGVEKZHVEKZIVEKZLZLZMZABNZDENZOPZA
    CNZDFNZOPZBCNZEFNZOPZLZVTGHNZOPZWCGINZOPZWFHINZOPZLZMZWAWJOPZWDWLOPZWGWNOPZ
    LZAWFNZDWGNZQPZXBGWNNZQPZMXCXEQPZWQWBWKMZWEWMMZWHWOMZLVSXAWBWKWEWMWHWOUDVSX
    HWRXIWSXJWTVSVDVFVGVJVKVNVOXHWRRVDVRUEZVFVGVHVMVQVDUFZVFVGVHVMVQVDUGZVJVKVL
    VIVQVDUHZVJVKVLVIVQVDUIZVNVOVPVIVMVDUJZVNVOVPVIVMVDUKZABDEGHJSTVSVDVFVHVJVL
    VNVPXIWSRXKXLVFVGVHVMVQVDULZXNVJVKVLVIVQVDUOZXPVNVOVPVIVMVDUPZACDFGIJSTVSVD
    VGVHVKVLVOVPXJWTRXKXMXRXOXSXQXTBCEFHIJSTUMUNVSXDWIXFWPVDVIVMXDWIUQVQABCDEFJ
    URUSVDVIVQXFWPUQVMABCGHIJURUTVAVDVMVQXGXAUQVIDEFGHIJURVBVC $.

  $( Commutativity law for three-place congruence.  (Contributed by Scott
     Fenton, 5-Oct-2013.) $)
  cgr3com $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
       ( <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. <->
         <. D , <. E , F >. >. Cgr3 <. A , <. B , C >. >. ) ) $=
    ( wcel w3a cop ccgr wbr ccgr3 wa wb 3simpa cgrcom syl3an 3simpb 3simpc cee
    cn cfv id 3anbi123d brcgr3 3com23 3bitr4d ) GUBHZAGUAUCZHZBUJHZCUJHZIZDUJHZ
    EUJHZFUJHZIZIZABJZDEJZKLZACJZDFJZKLZBCJZEFJZKLZIVAUTKLZVDVCKLZVGVFKLZIZAVFJ
    ZDVGJZMLVNVMMLZUSVBVIVEVJVHVKUIUIUNUKULNURUOUPNVBVIOUIUDZUKULUMPUOUPUQPABDE
    GQRUIUIUNUKUMNURUOUQNVEVJOVPUKULUMSUOUPUQSACDFGQRUIUIUNULUMNURUPUQNVHVKOVPU
    KULUMTUOUPUQTBCEFGQRUEABCDEFGUFUIURUNVOVLODEFABCGUFUGUH $.

  $( Identity law for three-place congruence.  (Contributed by Scott Fenton,
     6-Oct-2013.) $)
  cgr3rflx $p |- ( ( N e. NN /\
    ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
    <. A , <. B , C >. >. Cgr3 <. A , <. B , C >. >. ) $=
    ( cn wcel cee cfv w3a wa cop wbr ccgr cgrrflx 3adant3r3 3adant3r2 3adant3r1
    ccgr3 wb brcgr3 3anidm23 mpbir3and ) DEFZADGHZFZBUDFZCUDFZIZJABCKZKZUJRLZAB
    KZULMLZACKZUNMLZUIUIMLZUCUEUFUMUGABDNOUCUEUGUOUFACDNPUCUFUGUPUEBCDNQUCUHUKU
    MUOUPISABCABCDTUAUB $.

  ${
    $d A e f g $.  $d B e f g $.  $d C e f g $.  $d D e f g $.  $d F e f g $.
    $d N e f g $.
    $( A line segment can be divided at the same place as a congruent line
       segment is divided.  Theorem 4.5 of [Schwabhauser] p. 35.  (Contributed
       by Scott Fenton, 4-Oct-2013.) $)
    cgrxfr $p |- ( ( N e. NN /\
            ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
            ( D e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
            ( ( B Btwn <. A , C >. /\ <. A , C >. Cgr <. D , F >. ) ->
              E. e e. ( EE ` N ) ( e Btwn <. D , F >. /\
               <. A , <. B , C >. >. Cgr3 <. D , <. e , F >. >. ) ) ) $=
      ( vg vf wcel w3a wa cop cbtwn wbr ccgr wrex simpl1 wi ad2antrl cn cee cfv
      ccgr3 wne simpl3r simpl3l btwndiff syl3anc simpr simpl21 simpl22 axsegcon
      cv syl122anc adantr anass simprl simprr simpl23 df-3an anbi2i bitr4i wceq
      simplrr necomd simpr1 simpr2 simpr3 btwnexchand btwnexch3and cgrextendand
      simprrl simplll simprrr jca simplrl btwncomand simpllr cgrcomand segconeq
      3jca ex syl133anc syld opeq2 breq2d breq1d anbi12d biimpa simpl btwnexch3
      imp syl2ani adantl wb brcgr3 mpbir3and expr syl5 expcomd mpd sylanb an32s
      impr rexlimdva reximdva ) GUAJZAGUBUCZJZBXIJZCXIJZKZDXIJZFXIJZLZKZBACMZNO
      ZXRDFMZPOZLZEUNZXTNOZABCMZMDYCFMZMUDOZLZEXIQZXQYBLZDFHUNZMNOZDYKUEZLZHXIQ
      ZYIYJXHXOXNYOXHXMXPYBRXNXOXHXMYBUFXNXOXHXMYBUGFDGHUHUIYJYNYIHXIXQYKXIJZYB
      YNYISXQYPLZYBYNYIYQYBYNLZLZDYKYCMNOZDYCMZABMZPOZLZEXIQZYIYQUUEYRYQXHYPXNX
      JXKUUEXHXMXPYPRXQYPUJXNXOXHXMYPUGXJXKXLXHXPYPUKXJXKXLXHXPYPULEYKDABGUMUOU
      PYSUUDYHEXIYQYCXIJZYRUUDYHSZYQUUFLXQYPUUFLZLZYRUUGXQYPUUFUQUUIYRUUDYHUUIY
      RUUDLZLZYCYKIUNZMZNOZYCUULMZYEPOZLZIXIQZYHUUIUURUUJUUIXHYPUUFXKXLUURXHXMX
      PUUHRXQYPUUFURXQYPUUFUSXJXKXLXHXPUUHULXJXKXLXHXPUUHUTIYKYCBCGUMUOUPUUKUUQ
      YHIXIUUIUULXIJZUUJUUQYHSZUUIUUSLZXQYPUUFUUSKZLZUUJUUTUVAXQUUHUUSLZLUVCXQU
      UHUUSUQUVBUVDXQYPUUFUUSVAVBVCUVCUUJUUQYHUVCUUJUUQLZLZUULFVDZYHUVCUVEUVGUV
      CUVEYKDUEZDUUMNOZDUULMXRPOZLZDYKFMZNOZXTXRPOZLZKZUVGUVCUVEUVPUVFUVHUVKUVO
      UVFDYKUUJYMUVCUUQYBYLYMUUDVETVFUVFUVIUVJUVCUVEYKDYCUULGXHXMXPUVBRZXQYPUUF
      UUSVGZXNXOXHXMUVBUGZXQYPUUFUUSVHZXQYPUUFUUSVIZUUJYTUVCUUQYRYTUUCURZTZUVCU
      UJUUNUUPVMZVJUVCUVEDYCUULABCGUVQUVSUVTUWAXJXKXLXHXPUVBUKZXJXKXLXHXPUVBULZ
      XJXKXLXHXPUVBUTZUVCUVEYKDYCUULGUVQUVRUVSUVTUWAUWCUWDVKUUJXSUVCUUQXSYAYNUU
      DVNTUUJUUCUVCUUQYRYTUUCUSTUVCUUJUUNUUPVOVLVPUVFUVMUVNUVCUVEDFYKGUVQUVSXNX
      OXHXMUVBUFZUVRUUJYLUVCUUQYBYLYMUUDVQTVRUVCUVEACDFGUVQUWEUWGUVSUWHUUJYAUVC
      UUQXSYAYNUUDVSZTVTVPWBWCUVCXHXNXJXLYPUUSXOUVPUVGSUVQUVSUWEUWGUVRUWAUWHDAC
      YKGUULFWAWDWEWMUVCUUJUUQUVGYHSUVCUUJLZUVGUUQYHUVGUUQLYCUVLNOZYFYEPOZLZUWJ
      YHUVGUUQUWMUVGUUNUWKUUPUWLUVGUUMUVLYCNUULFYKWFWGUVGUUOYFYEPUULFYCWFWHWIWJ
      UVCUUJUWMYHUVCUUJUWMLZLZYDYGUVCUWNYDUUJUVCYTUWKYDUWMUWBUWKUWLWKUVCXHYPXNU
      UFXOYTUWKLYDSUVQUVRUVSUVTUWHYKDYCFGWLUOWNWMUWOYGUUBUUAPOZYAYEYFPOZUVCUWND
      YCABGUVQUVSUVTUWEUWFUWNUUCUVCYRYTUUCUWMVEWOVTUUJYAUVCUWMUWITUVCUWNYCFBCGU
      VQUVTUWHUWFUWGUVCUUJUWKUWLVOVTUVCYGUWPYAUWQKWPZUWNUVCXHXJXKXLXNUUFXOUWRUV
      QUWEUWFUWGUVSUVTUWHABCDYCFGWQWDUPWRVPWSWTXAXEXBWSXCXDXFXBWSXCXDXGXBWSXDXF
      XBWC $.
  $}

  ${
    $d N e $.  $d A e $.  $d B e $.  $d C e $.  $d D e $.  $d E e $.  $d F e $.
    $( A condition for extending betweenness to a new set of points based on
       congruence with another set of points.  Theorem 4.6 of [Schwabhauser]
       p. 36.  (Contributed by Scott Fenton, 4-Oct-2013.) $)
    btwnxfr $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
       ( ( B Btwn <. A , C >. /\
           <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. ) ->
         E Btwn <. D , F >. ) ) $=
      ( ve wcel w3a cop cbtwn wbr ccgr3 wa ccgr wi imp jca simpr cn cee cv wrex
      cfv brcgr3 simp2 biimtrdi simp1 simp21 simp22 simp23 simp31 simp33 cgrxfr
      sylan2d wceq simprrl simpl1 simpl31 simpl33 cgrrflxd adantr simpl2 simpl3
      syl132anc 3jca cgr3tr4 syl13anc cgr3com syl113anc syl133anc simpr1 simpr3
      wb simpl32 cgrcomlrand ex sylbid syld syl2ani cifs brifs ifscgr syl333anc
      sylbird cgrid2 eqbrtrrd expr an32s rexlimdva mpd ) GUAIZAGUBUEZIZBWNIZCWN
      IZJZDWNIZEWNIZFWNIZJZJZBACKZLMZABCKZKZDEFKZKZNMZOZEDFKZLMZXCXKOZHUCZXLLMZ
      XGDXOFKZKZNMZOZHWNUDZXMXCXKYAXCXJXDXLPMZXEYAXCXJABKDEKZPMZYBXFXHPMZJYBABC
      DEFGUFYDYBYEUGUHXCWMWOWPWQWSXAXEYBOYAQWMWRXBUIWMWOWPWQXBUJWMWOWPWQXBUKWMW
      OWPWQXBULWMWRWSWTXAUMWMWRWSWTXAUNABCDHFGUOVFUPRXNXTXMHWNXCXOWNIZXKXTXMQXC
      YFOZXKXTXMYGXKXTOZOZXOEXLLYGYHXOEUQZYGYHXOXOKXOEKPMZYJYGYHXPXPOZXLXLPMZXQ
      XQPMZOZDXOKZYCPMZFXOKZFEKZPMZOZJZYKYGYHUUBYIYLYOUUAYIXPXPYGXKXPXSURZUUCSY
      GYOYHYGYMYNYGDFGWMWRXBYFUSZWSWTXAWMWRYFUTZWSWTXAWMWRYFVAZVBYGXOFGUUDXCYFT
      ZUUFVBSVCYGYHUUAXKYGXJXSUUAXTXEXJTXPXSTYGXJXSOZXIXRNMZUUAYGWMWRXBWSYFXAJU
      UHUUIQUUDWMWRXBYFVDWMWRXBYFVEZYGWSYFXAUUEUUGUUFVGABCDEFDXOFGVHVIYGUUIXRXI
      NMZUUAYGWMXBWSYFXAUUIUUKVOUUDUUJUUEUUGUUFDEFDXOFGVJVKYGUUKYQYMXQXHPMZJZUU
      AYGWMWSYFXAWSWTXAUUKUUMVOUUDUUEUUGUUFUUEWSWTXAWMWRYFVPZUUFDXOFDEFGUFVLYGU
      UMUUAYGUUMOYQYTYGYQYMUULVMYGUUMXOFEFGUUDUUGUUFUUNUUFYGYQYMUULVNVQSVRVSVSV
      TWARVGVRYGWMWSYFXAYFWSYFXAWTUUBYKQUUDUUEUUGUUFUUGUUEUUGUUFUUNWMWSYFJXAYFW
      SJYFXAWTJJUUBYPYRKYPYSKWBMYKDXOFXODXOFEGWCDXOFXODXOFEGWDWFWEVTYGWMYFYFWTY
      KYJQUUDUUGUUGUUNXOXOEGWGVIVTRUUCWHWIWJWKWLVR $.
  $}

  ${
    $d p q r n $.
    $( Colinearity is a relationship.  (Contributed by Scott Fenton,
       7-Nov-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    colinrel $p |- Rel Colinear $=
      ( vp vn vq vr ccolin wrel cv cee cfv wcel w3a cop cbtwn wbr w3o wa coprab
      cn wrex ccnv relcnv df-colinear releqi mpbir ) EFAGZBGHIZJCGZUFJDGZUFJKUE
      UGUHLMNUGUHUELMNUHUEUGLMNOPBRSCDAQZTZFUIUAEUJBACDUBUCUD $.
  $}

  ${
    $d n p $.  $d n q $.  $d n r $.  $d P n $.  $d P p $.  $d p q $.  $d P q $.
    $d p r $.  $d P r $.  $d Q n $.  $d Q p $.  $d Q q $.  $d q r $.  $d Q r $.
    $d R n $.  $d R p $.  $d R q $.  $d R r $.

    $( Alternate colinearity binary relation.  (Contributed by Scott Fenton,
       7-Nov-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    brcolinear2 $p |- ( ( Q e. V /\ R e. W ) ->
        ( P Colinear <. Q , R >. <-> E. n e. NN
          ( ( P e. ( EE ` n ) /\ Q e. ( EE ` n ) /\ R e. ( EE ` n ) ) /\
            ( P Btwn <. Q , R >. \/ Q Btwn <. R , P >. \/
              R Btwn <. P , Q >. ) ) ) ) $=
      ( vp vq vr wcel wa cvv cop ccolin wbr cv w3a cbtwn cn breq2d cee cfv wrex
      w3o wi colinrel brrelex1i a1i elex 3ad2ant1 adantr rexlimivw coprab df-br
      wb ccnv df-colinear eleq2i bitri opex opelcnvg mpan2 3ad2ant3 bitrid wceq
      eleq1 3anbi2d opeq1 breq1 opeq2 3orbi123d anbi12d rexbidv 3anbi3d 3anbi1d
      eloprabg bitrd 3expia pm5.21ndd ) BEJZCFJZKZALJZABCMZNOZADPUAUBZJZBWFJZCW
      FJZQZAWDROZBCAMZROZCABMZROZUDZKZDSUCZWEWCUEWBAWDNUFUGUHWRWCUEWBWQWCDSWJWC
      WPWGWHWCWIAWFUIUJUKULUHVTWAWCWEWRUOVTWAWCQZWEWDAMGPZWFJZHPZWFJZIPZWFJZQZW
      TXBXDMZROZXBXDWTMZROZXDWTXBMZROZUDZKZDSUCZHIGUMZJZWRWEAWDMZXPUPZJZWSXQWEX
      RNJXTAWDNUNNXSXRDGHIUQURUSWCVTXTXQUOZWAWCWDLJYABCUTAWDLLXPVAVBVCVDXOXAWHX
      EQZWTBXDMZROZBXIROZXDWTBMZROZUDZKZDSUCXAWHWIQZWTWDROZBCWTMZROZCYFROZUDZKZ
      DSUCWRHIGBCAEFLXBBVEZXNYIDSYQXFYBXMYHYQXCWHXAXEXBBWFVFVGYQXHYDXJYEXLYGYQX
      GYCWTRXBBXDVHTXBBXIRVIYQXKYFXDRXBBWTVJTVKVLVMXDCVEZYIYPDSYRYBYJYHYOYRXEWI
      XAWHXDCWFVFVNYRYDYKYEYMYGYNYRYCWDWTRXDCBVJTYRXIYLBRXDCWTVHTXDCYFRVIVKVLVM
      WTAVEZYPWQDSYSYJWJYOWPYSXAWGWHWIWTAWFVFVOYSYKWKYMWMYNWOWTAWDRVIYSYLWLBRWT
      ACVJTYSYFWNCRWTABVHTVKVLVMVPVQVRVS $.
  $}

  ${
    $d A n $.  $d B n $.  $d C n $.  $d N n $.
    $( The binary relation form of the colinearity predicate.  (Contributed by
       Scott Fenton, 5-Oct-2013.) $)
    brcolinear $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
       ( A Colinear <. B , C >. <->
         ( A Btwn <. B , C >. \/ B Btwn <. C , A >. \/
           C Btwn <. A , B >. ) ) ) $=
      ( vn cn wcel cee cfv w3a wa cop ccolin wbr cv cbtwn w3o wrex wb eleq2d
      brcolinear2 3adant1 adantl simpr rexlimivw fveq2 3anbi123d anbi1d impbid2
      wceq rspcev expr bitrd ) DFGZADHIZGZBUOGZCUOGZJZKZABCLZMNZAEOZHIZGZBVDGZC
      VDGZJZAVAPNBCALPNCABLPNQZKZEFRZVIUSVBVKSZUNUQURVLUPABCEUOUOUAUBUCUTVKVIVJ
      VIEFVHVIUDUEUNUSVIVKVJUSVIKEDFVCDUJZVHUSVIVMVEUPVFUQVGURVMVDUOAVCDHUFZTVM
      VDUOBVNTVMVDUOCVNTUGUHUKULUIUM $.
  $}

  ${
    $d a b $.  $d a c $.  $d a n $.  $d a x $.  $d b c $.  $d b n $.  $d b x $.
    $d c n $.  $d c x $.  $d n x $.
    $( The colinear predicate exists.  (Contributed by Scott Fenton,
       25-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    colinearex $p |- Colinear e. _V $=
      ( va vn vb vc vx ccolin cv cee cfv wcel cop cbtwn wbr wa cn wrex cxp xpex
      wex opelxpi w3a w3o coprab ccnv cvv df-colinear ciun nnex fvex iunex wceq
      cab 3adant1 simp1 syl2anc adantr reximi eliun sylibr eleq1 biimpar sylan2
      df-oprab exlimiv exlimivv abssi eqsstri ssexi cnvex eqeltri ) FAGZBGZHIZJ
      ZCGZVMJZDGZVMJZUAZVKVOVQKZLMVOVQVKKLMVQVKVOKLMUBZNZBOPZCDAUCZUDUEBACDUFWD
      WDBOVMVMQZVMQZUGZBOWFUHWEVMVMVMVLHUIZWHRWHRUJWDEGZVTVKKZUKZWCNZASZDSCSZEU
      LWGWCCDAEVCWNEWGWMWIWGJZCDWLWOAWCWKWJWGJZWOWCWJWFJZBOPWPWBWQBOVSWQWAVSVTW
      EJZVNWQVPVRWRVNVOVQVMVMTUMVNVPVRUNVTVKWEVMTUOUPUQBWJOWFURUSWKWOWPWIWJWGUT
      VAVBVDVEVFVGVHVIVJ $.
  $}

  ${
    $d A a $.  $d a b $.  $d A b $.  $d a c $.  $d A c $.  $d a n $.  $d A n $.
    $d B a $.  $d B b $.  $d b c $.  $d B c $.  $d b n $.  $d B n $.  $d C a $.
    $d C b $.  $d C c $.  $d c n $.  $d C n $.  $d N n $.  $d V n $.  $d W n $.
    $( If ` A ` is colinear with ` B ` and ` C ` , then ` A ` is in the same
       space as ` B ` .  (Contributed by Scott Fenton, 25-Oct-2013.)  (Revised
       by Mario Carneiro, 19-Apr-2014.) $)
    colineardim1 $p |- (
       ( N e. NN /\ ( A e. V /\ B e. ( EE ` N ) /\ C e. W ) ) ->
       ( A Colinear <. B , C >. ->
       A e. ( EE ` N ) ) ) $=
      ( va vn vb vc cop wbr cv wcel w3a cbtwn w3o wa cn breq2d ccolin wrex ccnv
      cee cfv coprab df-colinear breqi wb simpr1 opex brcnvg sylancl df-br wceq
      eleq1 3anbi2d opeq1 breq1 opeq2 3orbi123d anbi12d rexbidv 3anbi3d 3anbi1d
      eloprabg 3comr adantl simpl simp2 anim2i axdimuniq adantrrl simprrl fveq2
      cvv 3simpa eleq2d syl5ibrcom syl2an exp32 syl7 rexlimdv sylbid biimtrid
      mpd ) ABCKZUALAWGGMZHMZUDUEZNZIMZWJNZJMZWJNZOZWHWLWNKZPLZWLWNWHKZPLZWNWHW
      LKZPLZQZRZHSUBZIJGUFZUCZLZDSNZAENZBDUDUEZNZCFNZOZRZAXKNZAWGUAXGHGIJUGUHXO
      XHWGAXFLZXPXOXJWGVPNXHXQUIXIXJXLXMUJBCUKAWGEVPXFULUMXQWGAKXFNZXOXPWGAXFUN
      XOXRAWJNZBWJNZCWJNZOZAWGPLZBCAKZPLZCABKZPLZQZRZHSUBZXPXNXRYJUIZXIXLXMXJYK
      XEWKXTWOOZWHBWNKZPLZBWSPLZWNWHBKZPLZQZRZHSUBWKXTYAOZWHWGPLZBCWHKZPLZCYPPL
      ZQZRZHSUBYJIJGBCAXKFEWLBUOZXDYSHSUUGWPYLXCYRUUGWMXTWKWOWLBWJUPUQUUGWRYNWT
      YOXBYQUUGWQYMWHPWLBWNURTWLBWSPUSUUGXAYPWNPWLBWHUTTVAVBVCWNCUOZYSUUFHSUUHY
      LYTYRUUEUUHWOYAWKXTWNCWJUPVDUUHYNUUAYOUUCYQUUDUUHYMWGWHPWNCBUTTUUHWSUUBBP
      WNCWHURTWNCYPPUSVAVBVCWHAUOZUUFYIHSUUIYTYBUUEYHUUIWKXSXTYAWHAWJUPVEUUIUUA
      YCUUCYEUUDYGWHAWGPUSUUIUUBYDBPWHACUTTUUIYPYFCPWHABURTVAVBVCVFVGVHXOYIXPHS
      YIYBXOWISNZXPYBYHVIXOUUJYBXPXOXIXLRZUUJXSXTRZRZXPUUJYBRXNXLXIXJXLXMVJVKYB
      UULUUJXSXTYAVQVKUUKUUMRZDWIUOZXPUUKUUJXTUUOXSBWIDVLVMUUNXPUUOXSUUKUUJXSXT
      VNUUOXKWJADWIUDVOVRVSWFVTWAWBWCWDWEWDWE $.
  $}

  $( Permutation law for colinearity.  Part of theorem 4.11 of [Schwabhauser]
     p. 36.  (Contributed by Scott Fenton, 5-Oct-2013.) $)
  colinearperm1 $p |- ( ( N e. NN /\
      ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
      ( A Colinear <. B , C >. <-> A Colinear <. C , B >. ) ) $=
    ( cn wcel cee cfv w3a wa cop cbtwn wbr w3o ccolin btwncom wb 3anrot sylan2b
    brcolinear sylan2br 3orbi123d 3orcomb bitrdi 3ancomb 3bitr4d ) DEFZADGHZFZB
    UHFZCUHFZIZJZABCKZLMZBCAKLMZCABKLMZNZACBKZLMZCBAKLMZBACKLMZNZAUNOMAUSOMZUMU
    RUTVBVANVCUMUOUTUPVBUQVAABCDPULUGUJUKUIIUPVBQUIUJUKRBCADPSULUGUKUIUJIUQVAQU
    KUIUJRCABDPUAUBUTVBVAUCUDABCDTULUGUIUKUJIVDVCQUIUJUKUEACBDTSUF $.

  $( Permutation law for colinearity.  Part of theorem 4.11 of [Schwabhauser]
     p. 36.  (Contributed by Scott Fenton, 5-Oct-2013.) $)
  colinearperm3 $p |- ( ( N e. NN /\
      ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
      ( A Colinear <. B , C >. <-> B Colinear <. C , A >. ) ) $=
    ( cn wcel cee cfv w3a cop cbtwn wbr w3o ccolin 3orrot a1i brcolinear 3anrot
    wa wb sylan2b 3bitr4d ) DEFZADGHZFZBUDFZCUDFZIZSZABCJZKLZBCAJZKLZCABJKLZMZU
    MUNUKMZAUJNLBULNLZUOUPTUIUKUMUNOPABCDQUHUCUFUGUEIUQUPTUEUFUGRBCADQUAUB $.

  $( Permutation law for colinearity.  Part of theorem 4.11 of [Schwabhauser]
     p. 36.  (Contributed by Scott Fenton, 5-Oct-2013.) $)
  colinearperm2 $p |- ( ( N e. NN /\
      ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
      ( A Colinear <. B , C >. <-> B Colinear <. A , C >. ) ) $=
    ( cn wcel cee cfv w3a wa cop ccolin wbr colinearperm3 colinearperm1 sylan2b
    wb 3anrot bitrd ) DEFZADGHZFZBUAFZCUAFZIZJABCKLMBCAKLMZBACKLMZABCDNUETUCUDU
    BIUFUGQUBUCUDRBCADOPS $.

  $( Permutation law for colinearity.  Part of theorem 4.11 of [Schwabhauser]
     p. 36.  (Contributed by Scott Fenton, 5-Oct-2013.) $)
  colinearperm4 $p |- ( ( N e. NN /\
      ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
      ( A Colinear <. B , C >. <-> C Colinear <. A , B >. ) ) $=
    ( cn wcel cee cfv w3a wa cop ccolin wbr colinearperm3 3anrot sylan2b bitrd
    wb ) DEFZADGHZFZBTFZCTFZIZJABCKLMBCAKLMZCABKLMZABCDNUDSUBUCUAIUEUFRUAUBUCOB
    CADNPQ $.

  $( Permutation law for colinearity.  Part of theorem 4.11 of [Schwabhauser]
     p. 36.  (Contributed by Scott Fenton, 5-Oct-2013.) $)
  colinearperm5 $p |- ( ( N e. NN /\
      ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
      ( A Colinear <. B , C >. <-> C Colinear <. B , A >. ) ) $=
    ( cn wcel cee cfv w3a wa cop ccolin colinearperm4 wb colinearperm1 sylan2br
    wbr 3anrot bitrd ) DEFZADGHZFZBUAFZCUAFZIZJABCKLQCABKLQZCBAKLQZABCDMUETUDUB
    UCIUFUGNUDUBUCRCABDOPS $.

  $( Trivial case of colinearity.  Theorem 4.12 of [Schwabhauser] p. 37.
     (Contributed by Scott Fenton, 5-Oct-2013.) $)
  colineartriv1 $p |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ->
    A Colinear <. A , B >. ) $=
    ( cn wcel cee cfv w3a cop ccolin wbr cbtwn w3o btwntriv1 3mix1d simp1 simp2
    wb simp3 brcolinear syl13anc mpbird ) CDEZACFGZEZBUDEZHZAABIZJKZAUHLKZABAIL
    KZBAAILKZMZUGUJUKULABCNOUGUCUEUEUFUIUMRUCUEUFPUCUEUFQZUNUCUEUFSAABCTUAUB $.

  $( Trivial case of colinearity.  (Contributed by Scott Fenton, 18-Oct-2013.)
     (Revised by Mario Carneiro, 19-Apr-2014.) $)
  colineartriv2 $p |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ->
    A Colinear <. B , B >. ) $=
    ( cn wcel cee cfv w3a cop ccolin wbr cbtwn btwntriv1 3mix2d 3com23 wb simp1
    w3o simp2 simp3 brcolinear syl13anc mpbird ) CDEZACFGZEZBUEEZHZABBIZJKZAUIL
    KZBBAILKZBABILKZRZUDUGUFUNUDUGUFHULUKUMBACMNOUHUDUFUGUGUJUNPUDUFUGQUDUFUGSU
    DUFUGTZUOABBCUAUBUC $.

  $( Betweenness implies colinearity.  (Contributed by Scott Fenton,
     7-Oct-2013.) $)
  btwncolinear1 $p |- ( ( N e. NN /\
    ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
    ( C Btwn <. A , B >. -> A Colinear <. B , C >. ) ) $=
    ( cop cbtwn wbr ccolin cn wcel cee cfv w3a w3o 3mix3 brcolinear imbitrrid
    wa ) CABEFGZABCEZHGDIJADKLZJBUAJCUAJMRATFGZBCAEFGZSNSUBUCOABCDPQ $.

  $( Betweenness implies colinearity.  (Contributed by Scott Fenton,
     15-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
  btwncolinear2 $p |- ( ( N e. NN /\
    ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
    ( C Btwn <. A , B >. -> A Colinear <. C , B >. ) ) $=
    ( cn cee cfv w3a wa cop cbtwn wbr ccolin btwncolinear1 colinearperm1 sylibd
    wcel ) DEQADFGZQBRQCRQHICABJKLABCJMLACBJMLABCDNABCDOP $.

  $( Betweenness implies colinearity.  (Contributed by Scott Fenton,
     15-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
  btwncolinear3 $p |- ( ( N e. NN /\
    ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
    ( C Btwn <. A , B >. -> B Colinear <. A , C >. ) ) $=
    ( cn cee cfv w3a wa cop cbtwn wbr ccolin btwncolinear1 colinearperm2 sylibd
    wcel ) DEQADFGZQBRQCRQHICABJKLABCJMLBACJMLABCDNABCDOP $.

  $( Betweenness implies colinearity.  (Contributed by Scott Fenton,
     15-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
  btwncolinear4 $p |- ( ( N e. NN /\
    ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
    ( C Btwn <. A , B >. -> B Colinear <. C , A >. ) ) $=
    ( cn cee cfv w3a wa cop cbtwn wbr ccolin btwncolinear1 colinearperm3 sylibd
    wcel ) DEQADFGZQBRQCRQHICABJKLABCJMLBCAJMLABCDNABCDOP $.

  $( Betweenness implies colinearity.  (Contributed by Scott Fenton,
     15-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
  btwncolinear5 $p |- ( ( N e. NN /\
    ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
    ( C Btwn <. A , B >. -> C Colinear <. A , B >. ) ) $=
    ( cn cee cfv w3a wa cop cbtwn wbr ccolin btwncolinear1 colinearperm4 sylibd
    wcel ) DEQADFGZQBRQCRQHICABJZKLABCJMLCSMLABCDNABCDOP $.

  $( Betweenness implies colinearity.  (Contributed by Scott Fenton,
     15-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
  btwncolinear6 $p |- ( ( N e. NN /\
    ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
    ( C Btwn <. A , B >. -> C Colinear <. B , A >. ) ) $=
    ( cn cee cfv w3a wa cop cbtwn wbr ccolin btwncolinear1 colinearperm5 sylibd
    wcel ) DEQADFGZQBRQCRQHICABJKLABCJMLCBAJMLABCDNABCDOP $.

  $( Transfer law for colinearity.  Theorem 4.13 of [Schwabhauser] p. 37.
     (Contributed by Scott Fenton, 5-Oct-2013.) $)
  colinearxfr $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
       ( ( B Colinear <. A , C >. /\
           <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. ) ->
         E Colinear <. D , F >. ) ) $=
    ( wcel w3a cop ccolin wbr ccgr3 wi wa cbtwn btwnxfr expcomd imp 3anrot biid
    cn cee cfv w3o cgr3permute4 syl3anbr sylbid cgr3permute3 3orim123d wb simp1
    syl3anb simp22 simp21 simp23 brcolinear adantr simp32 simp31 simp33 3imtr4d
    syl13anc ex com23 impd ) GUBHZAGUCUDZHZBVHHZCVHHZIZDVHHZEVHHZFVHHZIZIZBACJZ
    KLZABCJJDEFJJMLZEDFJZKLZVQVTVSWBVQVTVSWBNVQVTOZBVRPLZACBJPLZCBAJPLZUEZEWAPL
    ZDFEJPLZFEDJPLZUEZVSWBWCWDWHWEWIWFWJVQVTWDWHNVQWDVTWHABCDEFGQRSVQVTWEWINZVQ
    VTCABJJFDEJJMLZWLABCDEFGUFVQWEWMWIVGVGVLVKVIVJIVPVOVMVNIWEWMOWINVGUAZVKVIVJ
    TVOVMVNTCABFDEGQUGRUHSVQVTWFWJNZVQVTBCAJJEFDJJMLZWOABCDEFGUIVQWFWPWJVGVGVLV
    JVKVIIVPVNVOVMIWFWPOWJNWNVIVJVKTVMVNVOTBCAEFDGQUMRUHSUJVQVSWGUKZVTVQVGVJVIV
    KWQVGVLVPULZVGVIVJVKVPUNVGVIVJVKVPUOVGVIVJVKVPUPBACGUQVCURVQWBWKUKZVTVQVGVN
    VMVOWSWRVGVLVMVNVOUSVGVLVMVNVOUTVGVLVMVNVOVAEDFGUQVCURVBVDVEVF $.

  ${
    $d N f $.  $d A f $.  $d B f $.  $d C f $.  $d D f $.  $d E f $.
    $( Extend a line with a missing point.  Theorem 4.14 of [Schwabhauser]
       p. 37.  (Contributed by Scott Fenton, 6-Oct-2013.) $)
    lineext $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) ->
       ( ( A Colinear <. B , C >. /\ <. A , B >. Cgr <. D , E >. ) ->
         E. f e. ( EE ` N )
            <. A , <. B , C >. >. Cgr3 <. D , <. E , f >. >. ) ) $=
      ( wcel w3a wa cop wbr ccgr cbtwn wrex wb wi 3jca adantr anbi2d cn cee cfv
      ccolin w3o ccgr3 brcolinear 3adant3 anbi1d simp1 simp3r simp3l jca simp21
      cv simp23 axsegcon syl simprlr simprrr an4 simpl1 simpl21 simpl22 simpl3l
      simpl3r cgrcomlr syl122anc simpl23 simpr cgrextend syl133anc biimtrid imp
      sylbid expr cgrcom simpl2 brcgr3 syl113anc 3imtr4d an32s reximdva 3ancoma
      mpd exp32 btwncom sylan2b simp22 syl112anc simpll simplr ex adantl sylcom
      bitrid expdimp sylbird cgrxfr syl131anc cgr3permute1 biimprd adantld syld
      simp3 expd 3jaod impd ) GUAHZAGUBUCZHZBXJHZCXJHZIZDXJHZFXJHZJZIZABCKZUDLZ
      ABKZDFKZMLZJAXSNLZBCAKNLZCYANLZUEZYCJAXSKDFEUOZKZKUFLZEXJOZXRXTYGYCXIXNXT
      YGPXQABCGUGUHUIXRYGYCYKXRYDYCYKQZYEYFXRYDYCYKXRYDYCJZJZDYINLZDYHKZACKZMLZ
      JZEXJOZYKYNXIXPXOJZXKXMJZIZYTXRUUCYMXRXIUUAUUBXIXNXQUJZXRXPXOXIXNXOXPUKXI
      XNXOXPULUMXRXKXMXIXKXLXMXQUNZXIXKXLXMXQUPZUMRSEFDACGUQURYNYSYJEXJXRYHXJHZ
      YMYSYJQXRUUGJZYMJYOYQYPMLZJZYCUUIXSYIMLZIZYSYJUUHYMUUJUULUUHYMUUJJZJYCUUI
      UUKUUHYDYCUUJUSUUHYMYOUUIUTUUHUUMUUKUUMYDYOJZYCUUIJZJZUUHUUKYDYCYOUUIVAUU
      HUUPUUNBAKFDKMLZUUIJZJZUUKUUHUUOUURUUNUUHYCUUQUUIUUHXIXKXLXOXPYCUUQPXIXNX
      QUUGVBZXKXLXMXIXQUUGVCZXKXLXMXIXQUUGVDZXOXPXIXNUUGVEZXOXPXIXNUUGVFZABDFGV
      GVHUITUUHXIXLXKXMXPXOUUGUUSUUKQUUTUVBUVAXKXLXMXIXQUUGVIZUVDUVCXRUUGVJZBAC
      FDYHGVKVLVOVMVNRVPUUHYSUUJPYMUUHYRUUIYOUUHXIXOUUGXKXMYRUUIPUUTUVCUVFUVAUV
      EDYHACGVQVHTSUUHYJUULPZYMUUHXIXNXOXPUUGUVGUUTXIXNXQUUGVRZUVCUVDUVFABCDFYH
      GVSVTZSWAWBWCWEWFXRYEBYQNLZYLXIXNUVJYEPZXQXNXIXLXKXMIUVKXKXLXMWDBACGWGWHU
      HXRUVJYCYKXRUVJYCJZJZFYPNLZYIXSMLZJZEXJOZYKXRUVQUVLXRXIXQXLXMUVQUUDXIXNXQ
      XEZXIXKXLXMXQWIZUUFEDFBCGUQWJSUVMUVPYJEXJXRUUGUVLUVPYJQUUHUVLUVPYJUUHUVJU
      VNJZYCUUKJZJZUULUVLUVPJZYJUUHUWBUUIUULUUHXIXNXOXPUUGUWBUUIQUUTUVHUVCUVDUV
      FABCDFYHGVKVTUWAUUIUULQUVTUWAUUIUULUWAUUIJYCUUIUUKYCUUKUUIWKUWAUUIVJYCUUK
      UUIWLRWMWNWOUWCUVTYCUVOJZJUUHUWBUVJYCUVNUVOVAUUHUWDUWAUVTUUHUVOUUKYCUUHXI
      XPUUGXLXMUVOUUKPUUTUVDUVFUVBUVEFYHBCGVQVHTTWPUVIWAWQWBWCWEWFWRXRYFYCYKXRY
      FYCJZYHYBNLZACBKKDYHFKKUFLZJZEXJOZYKXRXIXKXMXLXQUWEUWIQUUDUUEUUFUVSUVRACB
      DEFGWSWTXRUWHYJEXJUUHUWGYJUWFUUHYJUWGUUHXIXNXOXPUUGYJUWGPUUTUVHUVCUVDUVFA
      BCDFYHGXAVTXBXCWCXDXFXGXHVO $.
  $}

  $( Change some conditions for outer five segment predicate.  (Contributed by
     Scott Fenton, 6-Oct-2013.) $)
  brofs2 $p |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
        ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\
        ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) ->
    ( <. <. A , B >. , <. C , D >. >. OuterFiveSeg
      <. <. E , F >. , <. G , H >. >. <->
      ( B Btwn <. A , C >. /\
        <. A , <. B , C >. >. Cgr3 <. E , <. F , G >. >. /\
        ( <. A , D >. Cgr <. E , H >. /\
          <. B , D >. Cgr <. F , H >. ) ) ) ) $=
    ( wcel w3a cop wbr cbtwn wa ccgr simpr1 syl133anc imp 3jca cn cee cfv ccgr3
    cofs brofs simpr1l simpr2l simpr2 jca ex simp11 simp12 simp13 simp21 simp23
    wi simp31 simp32 cgrextend syld simpr2r brcgr3 sylibrd simpr3 3simpa 3simpb
    wb btwnxfr syl5 biimtrdi 3ad2antr2 impbida bitrd ) IUAJZAIUBUCZJZBVPJZKZCVP
    JZDVPJZEVPJZKZFVPJZGVPJZHVPJZKZKZABLZCDLLEFLZGHLLUEMBACLZNMZFEGLZNMZOZWIWJP
    MZBCLZFGLZPMZOZADLEHLPMBDLFHLPMOZKZWLAWQLEWRLUDMZXAKZABCDEFGHIUFWHXBXDWHXBO
    ZWLXCXAWLWNWTXAWHUGWHXBXCWHXBWPWKWMPMZWSKZXCWHXBXGXEWPXFWSWPWSWOXAWHUHWHXBX
    FWHXBWOWTOZXFWHXBXHXEWOWTWHWOWTXAQWHWOWTXAUIUJUKWHVOVQVRVTWBWDWEXHXFUQVOVQV
    RWCWGULZVOVQVRWCWGUMZVOVQVRWCWGUNZVSVTWAWBWGUOZVSVTWAWBWGUPZVSWCWDWEWFURZVS
    WCWDWEWFUSZABCEFGIUTRVASWPWSWOXAWHVBTUKWHVOVQVRVTWBWDWEXCXGVHXIXJXKXLXMXNXO
    ABCEFGIVCRZVDSWHWOWTXAVETWHXDOZWOWTXAXQWLWNWHWLXCXAQWHXDWNXDWLXCOZWHWNWLXCX
    AVFWHVOVQVRVTWBWDWEXRWNUQXIXJXKXLXMXNXOABCEFGIVIRVJSUJWHWLXCWTXAWHXCWTWHXCX
    GWTXPWPXFWSVGVKSVLWHWLXCXAVETVMVN $.

  $( Change some conditions for inner five segment predicate.  (Contributed by
     Scott Fenton, 6-Oct-2013.) $)
  brifs2 $p |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
        ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\
        ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) ->
    ( <. <. A , B >. , <. C , D >. >. InnerFiveSeg
      <. <. E , F >. , <. G , H >. >. <->
      ( B Btwn <. A , C >. /\
        <. A , <. B , C >. >. Cgr3 <. E , <. F , G >. >. /\
        ( <. A , D >. Cgr <. E , H >. /\
          <. C , D >. Cgr <. G , H >. ) ) ) ) $=
    ( wcel w3a cop wbr cbtwn wa ccgr 3simpa syl133anc imp 3jca cn cee cfv ccgr3
    cifs brifs simpr1l wi simp11 simp12 simp13 simp21 simp23 simp31 simp32 syl5
    cgrsub simpr2l simpr2r ex brcgr3 sylibrd simpr3 simpr1 btwnxfr jca biimtrdi
    wb 3simpc 3ad2antr2 impbida bitrd ) IUAJZAIUBUCZJZBVNJZKZCVNJZDVNJZEVNJZKZF
    VNJZGVNJZHVNJZKZKZABLZCDLZLEFLZGHLZLUEMBACLZNMZFEGLZNMZOZWKWMPMZBCLZFGLZPMZ
    OZADLEHLPMWHWJPMOZKZWLAWQLEWRLUDMZXAKZABCDEFGHIUFWFXBXDWFXBOZWLXCXAWLWNWTXA
    WFUGWFXBXCWFXBWGWIPMZWPWSKZXCWFXBXGXEXFWPWSWFXBXFXBWOWTOZWFXFWOWTXAQWFVMVOV
    PVRVTWBWCXHXFUHVMVOVPWAWEUIZVMVOVPWAWEUJZVMVOVPWAWEUKZVQVRVSVTWEULZVQVRVSVT
    WEUMZVQWAWBWCWDUNZVQWAWBWCWDUOZABCEFGIUQRUPSWPWSWOXAWFURWPWSWOXAWFUSTUTWFVM
    VOVPVRVTWBWCXCXGVHXIXJXKXLXMXNXOABCEFGIVARZVBSWFWOWTXAVCTWFXDOZWOWTXAXQWLWN
    WFWLXCXAVDWFXDWNXDWLXCOZWFWNWLXCXAQWFVMVOVPVRVTWBWCXRWNUHXIXJXKXLXMXNXOABCE
    FGIVERUPSVFWFWLXCWTXAWFXCWTWFXCXGWTXPXFWPWSVIVGSVJWFWLXCXAVCTVKVL $.

  ${
    $d N a b c d e f g h p q n $.  $d A a b c d e f g h p q n $.
    $d B a b c d e f g h p q n $.  $d C a b c d e f g h p q n $.
    $d D a b c d e f g h p q n $.  $d E a b c d e f g h p q n $.
    $d F a b c d e f g h p q n $.  $d G a b c d e f g h p q n $.
    $d H a b c d e f g h p q n $.
    $( Binary relation form of the general five segment predicate.
       (Contributed by Scott Fenton, 5-Oct-2013.) $)
    brfs $p |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
        ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\
        ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) ->
    ( <. <. A , B >. , <. C , D >. >. FiveSeg <. <. E , F >. , <. G , H >. >.
      <->
      ( A Colinear <. B , C >. /\
        <. A , <. B , C >. >. Cgr3 <. E , <. F , G >. >. /\
        ( <. A , D >. Cgr <. E , H >. /\ <. B , D >. Cgr <. F , H >. ) ) ) ) $=
      ( cv cop ccolin wbr ccgr3 ccgr wa w3a wceq opeq1 breq2d va vb vc ve vf vg
      vd vh vn vq vp cee cfv cfs cn breq1 breq1d anbi1d 3anbi123d opeq2d anbi2d
      opeq2 3anbi12d anbi12d 3anbi3d 3anbi23d 3anbi2d fveq2 df-fs br8 ) UAJZUBJ
      ZUCJZKZLMZVKVNKZUDJZUEJZUFJZKZKZNMZVKUGJZKZVQUHJZKZOMZVLWCKZVRWEKZOMZPZQA
      VNLMZAVNKZWANMZAWCKZWFOMZWJPZQABVMKZLMZAWRKZWANMZWPBWCKZWIOMZPZQABCKZLMZA
      XEKZWANMZXDQXFXHADKZWFOMZBDKZWIOMZPZQXFXGEVTKZNMZXIEWEKZOMZXLPZQXFXGEFVSK
      ZKZNMZXQXKFWEKZOMZPZQXFXGEFGKZKZNMZYDQXFYGXIEHKZOMZXKFHKZOMZPZQUIABCDUIJZ
      ULUMIULUMUNUOUDUEUFUHEFGHIUJUKUAUBUCUGVKARZVOWLWBWNWKWQVKAVNLUPYNVPWMWANV
      KAVNSUQYNWGWPWJYNWDWOWFOVKAWCSUQURUSVLBRZWLWSWNXAWQXDYOVNWRALVLBVMSZTYOWM
      WTWANYOVNWRAYPUTUQYOWJXCWPYOWHXBWIOVLBWCSUQVAUSVMCRZWSXFXAXHXDYQWRXEALVMC
      BVBZTYQWTXGWANYQWRXEAYRUTUQVCWCDRZXDXMXFXHYSWPXJXCXLYSWOXIWFOWCDAVBUQYSXB
      XKWIOWCDBVBUQVDVEVQERZXHXOXMXRXFYTWAXNXGNVQEVTSTYTXJXQXLYTWFXPXIOVQEWESTU
      RVFVRFRZXOYAXRYDXFUUAXNXTXGNUUAVTXSEVRFVSSUTTUUAXLYCXQUUAWIYBXKOVRFWESTVA
      VFVSGRZYAYGXFYDUUBXTYFXGNUUBXSYEEVSGFVBUTTVGWEHRZYDYLXFYGUUCXQYIYCYKUUCXP
      YHXIOWEHEVBTUUCYBYJXKOWEHFVBTVDVEYMIULVHUDUEUFUHUIUJUKUAUBUCUGVIVJ $.
  $}

  $( Congruence law for the general five segment configuration.  Theorem 4.16
     of [Schwabhauser] p. 37.  (Contributed by Scott Fenton, 5-Oct-2013.) $)
  fscgr $p |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
      ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\
      ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) ->
   ( ( <. <. A , B >. , <. C , D >. >. FiveSeg <. <. E , F >. , <. G , H >. >.
       /\ A =/= B ) -> <. C , D >. Cgr <. G , H >. ) ) $=
    ( wcel w3a cop wbr wa ccgr3 wi cbtwn wb syl333anc sylbid cn cee cfv cfs wne
    ccolin ccgr brfs anbi1d w3o simp11 simp12 simp13 simp21 brcolinear syl13anc
    cofs simp23 simp31 simp32 cgr3permute2 syl133anc a1i 3anbi23d simp22 simp33
    ancom brofs2 bitr4d necom anbi12d 5segofs expd btwncom 3anbi1d cgr3permute1
    3expd cifs 3anbi2d brifs2 ifscgr a1dd 3jaod 3impd impd ) IUAJZAIUBUCZJZBWGJ
    ZKZCWGJZDWGJZEWGJZKZFWGJZGWGJZHWGJZKZKZABLZCDLZLZEFLGHLZLZUDMZABUEZNABCLZUF
    MZAXGLEFGLLOMZADLEHLUGMZBDLZFHLZUGMZNZKZXFNXAXCUGMZWSXEXOXFABCDEFGHIUHUIWSX
    OXFXPWSXHXIXNXFXPPZWSXHAXGQMZBCALQMZCWTQMZUJZXIXNXQPPZWSWFWHWIWKXHYARWFWHWI
    WNWRUKZWFWHWIWNWRULZWFWHWIWNWRUMZWJWKWLWMWRUNZABCIUOUPWSXRYBXSXTWSXRXIXNXQW
    SXRXIXNKZXFXPWSYGXFNBALXALFELXCLUQMZBAUEZNZXPWSYGYHXFYIWSYGXRBACLZLFEGLZLOM
    ZXMXJNZKZYHWSXIYMXNYNXRWSWFWHWIWKWMWOWPXIYMRYCYDYEYFWJWKWLWMWRURZWJWNWOWPWQ
    USZWJWNWOWPWQUTZABCEFGIVAVBXNYNRWSXJXMVGVCVDWSWFWIWHWKWLWOWMWPWQYHYORYCYEYD
    YFWJWKWLWMWRVEZYQYPYRWJWNWOWPWQVFZBACDFEGHIVHSVIXFYIRWSABVJVCVKWSWFWIWHWKWL
    WOWMWPWQYJXPPYCYEYDYFYSYQYPYRYTBACDFEGHIVLSTVMVQWSXSXIXNXQWSXSXIXNKZXFXPWSU
    UAXFNXBXDUQMZXFNXPWSUUAUUBXFWSUUABYKQMZXIXNKUUBWSXSUUCXIXNWSWFWIWKWHXSUUCRY
    CYEYFYDBCAIVNUPVOABCDEFGHIVHVIUIABCDEFGHIVLTVMVQWSXTXIXNXQWSXTXIXNKZXPXFWSU
    UDYKXKLYLXLLVRMZXPWSUUDXTACBLLEGFLLOMZXNKZUUEWSXIUUFXTXNWSWFWHWIWKWMWOWPXIU
    UFRYCYDYEYFYPYQYRABCEFGIVPVBVSWSWFWHWKWIWLWMWPWOWQUUEUUGRYCYDYFYEYSYPYRYQYT
    ACBDEGFHIVTSVIWSWFWHWKWIWLWMWPWOWQUUEXPPYCYDYFYEYSYPYRYQYTACBDEGFHIWASTWBVQ
    WCTWDWET $.

  $( Congruence rule for lines.  Theorem 4.17 of [Schwabhauser] p. 37.
     (Contributed by Scott Fenton, 6-Oct-2013.) $)
  linecgr $p |- ( ( N e. NN /\
    ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
    ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) ) ) ->
    ( ( ( A =/= B /\ A Colinear <. B , C >. ) /\
        ( <. A , P >. Cgr <. A , Q >. /\ <. B , P >. Cgr <. B , Q >. ) ) ->
      <. C , P >. Cgr <. C , Q >. ) ) $=
    ( cn wcel cee cfv w3a wa wne cop ccolin wbr ccgr ccgr3 simprlr cgr3rflx jca
    3adant3 adantr simprr 3jca simprll ex wi simp21 simp22 simp23 simp3l simp3r
    simp1 cfs brfs anbi1d fscgr sylbird syl333anc syld ) FGHZAFIJZHZBVCHZCVCHZK
    ZDVCHZEVCHZLZKZABMZABCNZOPZLZADNAENQPBDNBENQPLZLZVNAVMNZVRRPZVPKZVLLZCDNZCE
    NZQPZVKVQWAVKVQLZVTVLWEVNVSVPVKVLVNVPSVKVSVQVBVGVSVJABCFTUBUCVKVOVPUDUEVKVL
    VNVPUFUAUGVKVBVDVEVFVHVDVEVFVIWAWDUHVBVGVJUNVBVDVEVFVJUIZVBVDVEVFVJUJZVBVDV
    EVFVJUKZVBVGVHVIULWFWGWHVBVGVHVIUMVBVDVEKVFVHVDKVEVFVIKKZWAABNZWBNWJWCNUOPZ
    VLLWDWIWKVTVLABCDABCEFUPUQABCDABCEFURUSUTVA $.

  ${
    linecgrand.1 $e |- ( ph -> N e. NN ) $.
    linecgrand.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
    linecgrand.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
    linecgrand.4 $e |- ( ph -> C e. ( EE ` N ) ) $.
    linecgrand.5 $e |- ( ph -> P e. ( EE ` N ) ) $.
    linecgrand.6 $e |- ( ph -> Q e. ( EE ` N ) ) $.
    linecgrand.7 $e |- ( ( ph /\ ps ) -> A =/= B ) $.
    linecgrand.8 $e |- ( ( ph /\ ps ) -> A Colinear <. B , C >. ) $.
    linecgrand.9 $e |- ( ( ph /\ ps ) -> <. A , P >. Cgr <. A , Q >. ) $.
    linecgrand.10 $e |- ( ( ph /\ ps ) -> <. B , P >. Cgr <. B , Q >. ) $.
    $( Deduction form of ~ linecgr .  (Contributed by Scott Fenton,
       14-Oct-2013.) $)
    linecgrand $p |- ( ( ph /\ ps ) -> <. C , P >. Cgr <. C , Q >. ) $=
      ( cop wcel wa wne ccolin wbr ccgr jca wi cee cfv linecgr syl132anc adantr
      cn mp2and ) ABUAZCDUBZCDESUCUDZUAZCFSCGSUEUDZDFSDGSUEUDZUAZEFSEGSUEUDZUOU
      PUQOPUFUOUSUTQRUFAURVAUAVBUGZBAHUMTCHUHUIZTDVDTEVDTFVDTGVDTVCIJKLMNCDEFGH
      UJUKULUN $.
  $}

  $( Identity law for points on lines.  Theorem 4.18 of [Schwabhauser] p. 38.
     (Contributed by Scott Fenton, 7-Oct-2013.) $)
  lineid $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
    ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
    ( ( ( A =/= B /\ A Colinear <. B , C >. ) /\
        ( <. A , C >. Cgr <. A , D >. /\ <. B , C >. Cgr <. B , D >. ) ) ->
      C = D ) ) $=
    ( cn wcel cee cfv wa w3a wne cop ccolin wbr ccgr wceq wi simp2l simp2r 3jca
    simp3l linecgr syld3an2 simp1 simp3r cgrid2 syl13anc syld ) EFGZAEHIZGZBUKG
    ZJZCUKGZDUKGZJZKZABLABCMZNOJACMADMPOUSBDMPOJJZCCMCDMPOZCDQZUJULUMUOKUNUQUTV
    ARURULUMUOUJULUMUQSUJULUMUQTUJUNUOUPUBZUAABCCDEUCUDURUJUOUOUPVAVBRUJUNUQUEV
    CVCUJUNUOUPUFCCDEUGUHUI $.

  $( Law for finding a point inside a segment.  Theorem 4.19 of [Schwabhauser]
     p. 38.  (Contributed by Scott Fenton, 7-Oct-2013.) $)
  idinside $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
   ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
   ( ( C Btwn <. A , B >. /\ <. A , C >. Cgr <. A , D >. /\
       <. B , C >. Cgr <. B , D >. ) -> C = D ) ) $=
    ( cn wcel wa w3a cop cbtwn wbr ccgr wceq wi simp1 syl13anc opeq1 imbi1d idd
    cee simp3l simp3r cgrid2 axbtwnid syl3anc breq12d biimpcd ax-1 syl8 sylsyld
    cfv simp2l 3impd breq2d 3anbi1d imbitrid wne ccolin simpr2l simpr2r simpr3l
    opeq2 simpr1 btwncolinear1 3anim123d anim2i 3simpc adantl jca lineid impcom
    syl5 expd syld ex pm2.61ine ) EFGZAEUAULZGZBVSGZHZCVSGZDVSGZHZIZCABJZKLZACJ
    ZADJZMLZBCJZBDJMLZIZCDNZOZOABWFCAAJZKLZWKWMIZWOOABNZWPWFWRWKWMWOWFCCJZCDJZM
    LZWOOZWRCANZWKWMWOOZOWFVRWCWCWDXDVRWBWEPZVRWBWCWDUBZXHVRWBWCWDUCCCDEUDQWFVR
    WCVTWRXEOXGXHVRVTWAWEUMCAEUEUFXDXEWKWOXFXEXDWKWOOXEXCWKWOXEXAWIXBWJMCACRCAD
    RUGSUHWOWMUIUJUKUNWTWSWNWOWTWRWHWKWMWTWQWGCKABAVCUOUPSUQABURZWFWPXIWFHZWNAW
    LUSLZWKWMIZWOXJWHXKWKWKWMWMXJVRVTWAWCWHXKOXIVRWBWEVDVTWAVRWEXIUTVTWAVRWEXIV
    AWCWDVRWBXIVBABCEVEQXJWKTXJWMTVFWFXIXLWOOWFXIXLWOXIXLHZXIXKHZWKWMHZHWFWOXMX
    NXOXLXKXIXKWKWMPVGXLXOXIXKWKWMVHVIVJABCDEVKVMVNVLVOVPVQ $.

  $( If ` A ` , ` B ` , and ` C ` fall in order on a line, and ` A B ` and
     ` A C ` are congruent, then ` C = B ` .  (Contributed by Scott Fenton,
     7-Oct-2013.) $)
  endofsegid $p |- ( ( N e. NN /\
    ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
    ( ( B Btwn <. A , C >. /\ <. A , C >. Cgr <. A , B >. ) ->
      C = B ) ) $=
    ( cn wcel cee cfv w3a wa cop cbtwn ccgr wceq wb simpl syl3an3br 3anidm23 wi
    wbr ccgr3 simpr1 simpr3 simpr2 cgrcom syl122anc idd axcgrrflx 3adant3r1 a1d
    biimpd 3jcad 3ancomb brcgr3 sylibrd btwnxfr sylan2d jcad 3anrot btwnswapid2
    a1i sylan2br syld ) DEFZADGHZFZBVEFZCVEFZIZJZBACKZLTZVKABKZMTZJZCVMLTZVLJZC
    BNZVJVOVPVLVJVNABCKZKACBKZKUATZVLVPVJVNVMVKMTZVNVSVTMTZIZWAVJVNWBVNWCVJVNWB
    VJVDVFVHVFVGVNWBOVDVIPVDVFVGVHUBZVDVFVGVHUCWEVDVFVGVHUDACABDUEUFUKVJVNUGVJW
    CVNVDVGVHWCVFBCDUHUIUJULVDVIWAWDOZVIVDVIVFVHVGIZWFVFVHVGUMZABCACBDUNQRUOVDV
    IVLWAJVPSZVIVDVIWGWIWHABCACBDUPQRUQVOVLSVJVLVNPVAURVIVDVHVFVGIVQVRSVHVFVGUS
    CABDUTVBVC $.

  ${
    endofsegidand.1 $e |- ( ph -> N e. NN ) $.
    endofsegidand.2 $e |- ( ph -> A e. ( EE ` N ) ) $.
    endofsegidand.3 $e |- ( ph -> B e. ( EE ` N ) ) $.
    endofsegidand.4 $e |- ( ph -> C e. ( EE ` N ) ) $.
    endofsegidand.5 $e |- ( ( ph /\ ps ) -> C Btwn <. A , B >. ) $.
    endofsegidand.6 $e |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. A , C >. ) $.
    $( Deduction form of ~ endofsegid .  (Contributed by Scott Fenton,
       15-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    endofsegidand $p |- ( ( ph /\ ps ) -> B = C ) $=
      ( wa cop cbtwn wbr ccgr wceq wi wcel cn endofsegid syl13anc adantr mp2and
      cee cfv ) ABMECDNZOPZUHCENQPZDERZKLAUIUJMUKSZBAFUATCFUFUGZTEUMTDUMTULGHJI
      CEDFUBUCUDUE $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Connectivity of betweenness
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Lemma for ~ btwnconn1 .  The next several lemmas introduce various
     properties of hypothetical points that end up eliminating alternatives to
     connectivity.  We begin by showing a congruence property of those
     hypothetical points.  (Contributed by Scott Fenton, 8-Oct-2013.) $)
  btwnconn1lem1 $p |- (
     ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\
         ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ X e. ( EE ` N ) ) ) /\
         ( ( ( A =/= B /\ B =/= C ) /\
             ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\
           ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\
             ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\
           ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\
             ( d Btwn <. A , X >. /\ <. d , X >. Cgr <. D , B >. ) ) ) ) ->
     <. B , c >. Cgr <. X , C >. ) $=
    ( wcel w3a cv wne wa cop cbtwn wbr ccgr adantl btwnexch3and cee cfv simp1rr
    cn simp11 simp13 simp22 simp23 simp33 simp31 simp21 simp2ll simp2rl simp3rl
    simp12 btwncomand simp3rr cgrcomand simp2lr simp2rr cgrcomland cgrextendand
    cgrcomlrand cgrtr3and ) EUDJZAEUAUBZJZBVFJZKZCVFJZDVFJZHLZVFJZKZILZVFJZGLZV
    FJZFVFJZKZKZABMBCMNZBACOPQZBADOPQZNNZDAVLOPQZDVLOCDOZRQZNZCAVOOPQZCVOOWGRQZ
    NZNZVLAVQOPQVLVQOCBORQNZVOAFOPQZVOFODBORQZNNZKZBDVLFVOCEVEVGVHVNVTUEZVEVGVH
    VNVTUFZVIVJVKVMVTUGZVIVJVKVMVTUHZVIVNVPVRVSUIZVIVNVPVRVSUJZVIVJVKVMVTUKZWAW
    RABDVLEWSVEVGVHVNVTUOZWTXAXBWRWDWAWCWDWBWMWQUCSWRWFWAWFWHWLWEWQULSTWAWRVOCF
    EWSXDXEXCWAWRACVOFEWSXFXEXDXCWRWJWAWJWKWIWEWQUMSWRWOWAWOWPWNWEWMUNSTUPWAWRD
    BVOFEWSXAWTXDXCWAWRVOFDBEWSXDXCXAWTWRWPWAWOWPWNWEWMUQSURVCWAWRDVLVOCCDEWSXA
    XBXDXEXEXAWRWHWAWFWHWLWEWQUSSWAWRCVOCDEWSXEXDXEXAWRWKWAWJWKWIWEWQUTSVAVDVB
    $.

  $( Lemma for ~ btwnconn1 .  Now, we show that two of the hypotheticals we
     introduced in the first lemma are identical.  (Contributed by Scott
     Fenton, 8-Oct-2013.) $)
  btwnconn1lem2 $p |- (
     ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\
         ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ X e. ( EE ` N ) ) ) /\
         ( ( ( A =/= B /\ B =/= C ) /\
             ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\
           ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\
             ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\
           ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\
             ( d Btwn <. A , X >. /\ <. d , X >. Cgr <. D , B >. ) ) ) ) ->
     X = b ) $=
    ( wcel w3a cv wa cop cbtwn wbr ccgr adantl jca adantr cn cee cfv wne simp11
    simp1ll simp12 simp13 simp21 simp33 simp1rl simp2rl simp3rl simp31 btwnexch
    wi syl122anc mpd btwnexchand cgrrflx2d simp23 simp32 simp1rr simp2ll simp22
    simp3ll btwnexch3and btwncomand btwnconn1lem1 simp3lr cgrextendand segconeq
    wceq syl133anc mp3and ) EUAJZAEUBUCZJZBVQJZKZCVQJZDVQJZHLZVQJZKZILZVQJZGLZV
    QJZFVQJZKZKZABUDZBCUDZMZBACNOPZBADNOPZMZMZDAWCNZOPZDWCNCDNZQPZMZCAWFNOPZCWF
    NXBQPZMZMZWCAWHNZOPZWCWHNCBNQPZMZWFAFNZOPZWFFNDBNQPZMZMZKZMZWMBXMOPZBFNFBNZ
    QPZMZBXIOPZBWHNYAQPZMZFWHVMZXRWMWLWMWNWRXHXQUFRXSXTYBWLXRABCFEVPVRVSWEWKUEZ
    VPVRVSWEWKUGZVPVRVSWEWKUHZVTWAWBWDWKUIZVTWEWGWIWJUJZXRWPWLWPWQWOXHXQUKRZXSX
    EXNMZCXMOPZXRYNWLXRXEXNXEXFXDWSXQULXNXOXLWSXHUMSRWLYNYOUPZXRWLVPVRWAWGWJYPY
    HYIYKVTWEWGWIWJUNYLACWFFEUOUQTURZUSWLYBXRWLBFEYHYJYLUTTSXSYDYEWLXRABWCWHEYH
    YIYJVTWAWBWDWKVAZVTWEWGWIWJVBZXSWQXAMZBWTOPZXRYTWLXRWQXAWPWQWOXHXQVCXAXCXGW
    SXQVDSRWLYTUUAUPZXRWLVPVRVSWBWDUUBYHYIYJVTWAWBWDWKVEYRABDWCEUOUQTURZXRXJWLX
    JXKXPWSXHVFRZUSWLXRBWCWHFCBEYHYJYRYSYLYKYJWLXRABWCWHEYHYIYJYRYSUUCUUDVGWLXR
    CBFEYHYKYJYLWLXRABCFEYHYIYJYKYLYMYQVGVHABCDEFGHIVIXRXKWLXJXKXPWSXHVJRVKSWLW
    MYCYFKYGUPZXRWLVPVSWJVSVRWJWIUUEYHYJYLYJYIYLYSBFBAEFWHVLVNTVO $.

  $( Lemma for ~ btwnconn1 .  Establish the next congruence in the series.
     (Contributed by Scott Fenton, 8-Oct-2013.) $)
  btwnconn1lem3 $p |- (
     ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\
         ( d e. ( EE ` N ) /\ b e. ( EE ` N ) ) ) /\
         ( ( ( A =/= B /\ B =/= C ) /\
             ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\
           ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\
             ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\
           ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\
             ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) ) ->
     <. B , d >. Cgr <. b , D >. ) $=
    ( wcel w3a cv wa cop cbtwn wbr ccgr adantl syl122anc adantr wb cn simp11 wi
    cee cfv simp13 simp21 simp3l simp3r simp23 simp22 simp1rl simp2rl btwnexch3
    wne jca simp12 mpd simp2ll simp3ll btwncomand simp3lr cgrcomlr cgrcom bitrd
    mpbid simp2rr simp2lr cgrcomland cgrtr3and cgrextendand ) EUAIZAEUDUEZIZBVM
    IZJZCVMIZDVMIZGKZVMIZJZHKZVMIZFKZVMIZLZJZABUOBCUOLZBACMNOZBADMNOZLLZDAVSMNO
    ZDVSMCDMZPOZLZCAWBMNOZCWBMWMPOZLZLZVSAWDMZNOZVSWDMCBMPOZLWBWTNOWBWDMDBMPOLZ
    LZJZBCWBWDVSDEVLVNVOWAWFUBZVLVNVOWAWFUFZVPVQVRVTWFUGZVPWAWCWEUHZVPWAWCWEUIZ
    VPVQVRVTWFUJZVPVQVRVTWFUKZWGXELZWIWPLZCBWBMNOZXEXNWGXEWIWPWIWJWHWSXDULWPWQW
    OWKXDUMUPQWGXNXOUCZXEWGVLVNVOVQWCXPXFVLVNVOWAWFUQZXGXHXIABCWBEUNRSURWGXEVSD
    WDEXFXKXLXJXMWLXALZVSDWDMNOZXEXRWGXEWLXAWLWNWRWKXDUSXAXBXCWKWSUTUPQWGXRXSUC
    ZXEWGVLVNVRVTWEXTXFXQXLXKXJADVSWDEUNRSURVAXMXBBCMZWDVSMZPOZXEXBWGXAXBXCWKWS
    VBQWGXBYCTXEWGXBYBYAPOZYCWGVLVTWEVQVOXBYDTXFXKXJXHXGVSWDCBEVCRWGVLWEVTVOVQY
    DYCTXFXJXKXGXHWDVSBCEVDRVESVFWGXECWBVSDCDEXFXHXIXKXLXHXLXEWQWGWPWQWOWKXDVGQ
    WGXEDVSCDEXFXLXKXHXLXEWNWGWLWNWRWKXDVHQVIVJVK $.

  $( Lemma for ~ btwnconn1 .  Assuming ` C =/= c ` , we now attempt to force
     ` D = d ` from here out via a series of congruences.  (Contributed by
     Scott Fenton, 8-Oct-2013.) $)
  btwnconn1lem4 $p |- (
     ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\
         ( d e. ( EE ` N ) /\ b e. ( EE ` N ) ) ) /\
         ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\
             ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\
           ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\
             ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\
           ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\
             ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) ) ->
     <. d , c >. Cgr <. D , C >. ) $=
    ( wcel w3a cv wa wne cop cbtwn wbr ccgr adantl adantr wb cn cee cfv simp1rl
    ccgr3 simp2rl jca wi simp11 simp12 simp13 simp21 simp3l btwnexch3 syl122anc
    mpd simp3lr simp23 simp3r cgrcomlr cgrcom bitrd 3simpa anim1i btwnconn1lem3
    mpbid syl3anr1 simp22 simp2rr simp2lr cgrcomland cgrtr3and brcgr3 syl133anc
    mpbir3and simpl 3jca 3anim3i 3anim1i btwnconn1lem1 syl2an cgrrflx2d simp1l2
    simpr cofs brofs2 anbi1d 5segofs sylbird syl333anc mp2and ) EUAIZAEUBUCZIZB
    WMIZJZCWMIZDWMIZGKZWMIZJZHKZWMIZFKZWMIZLZJZABMZBCMZCWSMZJZBACNOPZBADNOPZLZL
    ZDAWSNOPZDWSNCDNZQPZLZCAXBNOPZCXBNZXQQPZLZLZWSAXDNZOPZWSXDNCBNQPZLXBYEOPXBX
    DNDBNQPLZLZJZLZCBXBNZOPZBYANXDWSDNZNUEPZBWSNXDCNQPZCWSNWSCNQPZLZJZXIXBWSNZD
    CNZQPZYKYMYOYRYKXLXTLZYMYJUUCXGYJXLXTXLXMXKYDYIUDXTYBXSXOYIUFUGRXGUUCYMUHZY
    JXGWLWNWOWQXCUUDWLWNWOXAXFUIZWLWNWOXAXFUJWLWNWOXAXFUKZWPWQWRWTXFULZWPXAXCXE
    UMZABCXBEUNUOSUPYKYOBCNZXDWSNZQPZYLXDDNQPZYAYNQPZYKYGUUKYJYGXGYFYGYHXOYDUQR
    XGYGUUKTYJXGYGUUJUUIQPZUUKXGWLWTXEWQWOYGUUNTUUEWPWQWRWTXFURZWPXAXCXEUSZUUGU
    UFWSXDCBEUTUOXGWLXEWTWOWQUUNUUKTUUEUUPUUOUUFUUGXDWSBCEVAUOVBSVFXOXHXILZXNLZ
    XGYDYIUULXKUUQXNXHXIXJVCVDZABCDEFGHVEVGXGYJCXBWSDCDEUUEUUGUUHUUOWPWQWRWTXFV
    HZUUGUUTYJYBXGXTYBXSXOYIVIRXGYJDWSCDEUUEUUTUUOUUGUUTYJXRXGXPXRYCXOYIVJRVKVL
    XGYOUUKUULUUMJTZYJXGWLWOWQXCXEWTWRUVAUUEUUFUUGUUHUUPUUOUUTBCXBXDWSDEVMVNSVO
    YKYPYQXGWPXAXCXEXEJZJUURYDYIJYPYJXFUVBWPXAXFXCXEXEXCXEVPXCXEWDZUVCVQVRXOUUR
    YDYIUUSVSABCDEXDFGHVTWAXGYQYJXGCWSEUUEUUGUUOWBSUGVQYJXIXGXHXIXJXNYDYIWCRXGY
    SXILZUUBUHZYJXGWLWOWQXCWTXEWTWRWQUVEUUEUUFUUGUUHUUOUUPUUOUUTUUGWLWOWQJXCWTX
    EJWTWRWQJJZUVDUUIYTNUUJUUANWEPZXILUUBUVFUVGYSXIBCXBWSXDWSDCEWFWGBCXBWSXDWSD
    CEWHWIWJSWK $.

  $( Lemma for ~ btwnconn1 .  Now, we introduce ` E ` , the intersection of
     ` C c ` and ` D d ` .  We begin by showing that it is the midpoint of
     ` C ` and ` c ` .  (Contributed by Scott Fenton, 8-Oct-2013.) $)
  btwnconn1lem5 $p |- (
     ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\
         ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) /\
         ( ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\
               ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\
             ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\
               ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\
             ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\
               ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) /\
           ( E Btwn <. C , c >. /\ E Btwn <. D , d >. ) ) ) ->
         <. E , C >. Cgr <. E , c >. ) $=
    ( wcel w3a cv wne cop cbtwn wbr wa ccgr adantr wb cn cee cfv simprrr simp11
    ccgr3 simp22 simp33 simp31 cgr3rflx syl13anc simp2lr ad2antrl simp23 simp21
    cgrcomr cgrcom bitrd mpbid simp2rr cgrcomlrand 3simpa 3anim3i btwnconn1lem4
    syl122anc simpl syl2an cgrtr3and jca wi cifs brifs2 ifscgr syl333anc mp3and
    sylbird ) FUAJZAFUBUCZJZBVRJZKZCVRJZDVRJZHLZVRJZKZILZVRJZGLZVRJZEVRJZKZKZAB
    MBCMCWDMKBACNOPBADNOPQQZDAWDNOPZDWDNZCDNZRPZQZCAWGNOPZCWGNWQRPZQZQWDAWINZOP
    WDWINCBNRPQWGXCOPWGWINDBNRPQQZKZECWDNOPZEDWGNOPZQZQZQZXGDEWGNNZXKUFPZDCNZWP
    RPZWGCNZWGWDNZRPZQZECNEWDNRPZWMXEXFXGUDWMXLXIWMVQWCWKWHXLVQVSVTWFWLUEZWAWBW
    CWEWLUGZWAWFWHWJWKUHZWAWFWHWJWKUIZDEWGFUJUKSXJXNXQXJWRXNXEWRWMXHWOWRXBWNXDU
    LUMWMWRXNTXIWMWRWPXMRPZXNWMVQWCWEWBWCWRYDTXTYAWAWBWCWEWLUNZWAWBWCWEWLUOZYAD
    WDCDFUPVEWMVQWCWEWCWBYDXNTXTYAYEYAYFDWDDCFUQVEURSUSWMXIWGCWGWDDCFXTYCYFYCYE
    YAYFWMXICWGCDFXTYFYCYFYAXEXAWMXHWTXAWSWNXDUTUMVAWMWAWFWHWJQZKXEXPXMRPXIWLYG
    WAWFWHWJWKVBVCXEXHVFABCDFGHIVDVGVHVIWMXGXLXRKZXSVJZXIWMVQWCWKWHWBWCWKWHWEYI
    XTYAYBYCYFYAYBYCYEVQWCWKKWHWBWCKWKWHWEKKYHDENZXONYJXPNVKPXSDEWGCDEWGWDFVLDE
    WGCDEWGWDFVMVPVNSVO $.

  $( Lemma for ~ btwnconn1 .  Next, we show that ` E ` is the midpoint of ` D `
     and ` d ` .  (Contributed by Scott Fenton, 8-Oct-2013.) $)
  btwnconn1lem6 $p |- (
     ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\
         ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) /\
         ( ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\
               ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\
             ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\
               ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\
             ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\
               ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) /\
           ( E Btwn <. C , c >. /\ E Btwn <. D , d >. ) ) ) ->
         <. E , D >. Cgr <. E , d >. ) $=
    ( wcel w3a cv wne cop cbtwn wbr wa ccgr jca cgrrflxd cee cfv simprrl simp11
    cn simp21 simp23 simp33 adantr simp31 simp2rr ad2antrl cgrcomand cgrcomrand
    simp22 simp2lr 3simpa 3anim3i btwnconn1lem4 syl2an cgrtr3and cgrcomlrand wi
    simpl cifs brifs ifscgr sylbird syl333anc mp3and ) FUEJZAFUAUBZJZBVLJZKZCVL
    JZDVLJZHLZVLJZKZILZVLJZGLZVLJZEVLJZKZKZABMBCMCVRMKBACNOPBADNOPQQZDAVRNOPZDV
    RNCDNZRPZQZCAWANOPZCWANZWJRPZQZQVRAWCNZOPVRWCNCBNRPQWAWQOPWAWCNDBNRPQQZKZEC
    VRNZOPZEDWANOPZQZQZQZXAXAQZWTWTRPZEVRNZXHRPZQZWJWNRPZVRDNZVRWANZRPZQZEDNEWA
    NRPZXEXAXAWGWSXAXBUCZXQSWGXJXDWGXGXIWGCVRFVKVMVNVTWFUDZVOVPVQVSWFUFZVOVPVQV
    SWFUGZTWGEVRFXRVOVTWBWDWEUHZXTTSUIXEXKXNWGXDCWACDFXRXSVOVTWBWDWEUJZXSVOVPVQ
    VSWFUOZWSWOWGXCWMWOWLWHWRUKULUMWGXDDVRWAVRFXRYCXTYBXTWGXDDVRWAVRDCFXRYCXTYB
    XTYCXSWGXDDVRCDFXRYCXTXSYCWSWKWGXCWIWKWPWHWRUPULUNWGVOVTWBWDQZKWSWAVRNDCNRP
    XDWFYDVOVTWBWDWEUQURWSXCVDABCDFGHIUSUTVAVBSWGXFXJXOKZXPVCZXDWGVKVPWEVSVQVPW
    EVSWBYFXRXSYAXTYCXSYAXTYBVKVPWEKVSVQVPKWEVSWBKKYECENZXLNYGXMNVEPXPCEVRDCEVR
    WAFVFCEVRDCEVRWAFVGVHVIUIVJ $.

  $( Lemma for ~ btwnconn1 .  Under our assumptions, ` C ` and ` d ` are
     distinct.  (Contributed by Scott Fenton, 8-Oct-2013.) $)
  btwnconn1lem7 $p |- (
     ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\
         ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) /\
         ( ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\
               ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\
             ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\
               ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\
             ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\
               ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) /\
           ( E Btwn <. C , c >. /\ E Btwn <. D , d >. ) ) ) ->
        C =/= d ) $=
    ( wcel w3a cv wne cop cbtwn wbr wa ccgr wi syl5 cee simp1l3 simp2rr simp2lr
    cfv adantr 3jca simp11 simp21 simp22 simp23 simp31 simpr1 wceq opeq2 breq1d
    cn 3anbi2d biimparc simp2 simp1 simp2l simp2r cgrid2 syl13anc opeq1 breq12d
    imp simp3l axcgrid expdimp 3ad2antr3 mpd ex necon3d syl122anc ) FUQJZAFUAUE
    ZJZBVRJZKZCVRJZDVRJZHLZVRJZKZILZVRJZGLZVRJZEVRJZKZKZABMZBCMZCWDMZKBACNOPBAD
    NOPQZQZDAWDNOPZDWDNZCDNZRPZQZCAWGNOPZCWGNZXARPZQZQZWDAWINZOPWDWINCBNRPQWGXI
    OPWGWINDBNRPQQZKZECWDNZOPEDWGNOPQZQZCWGMZXNWPXFXBKZWMXOXNWPXFXBXKWPXMWNWOWP
    WQXHXJUBUFXKXFXMXDXFXCWRXJUCUFXKXBXMWSXBXGWRXJUDUFUGWMVQWBWCWEWHXPXOSVQVSVT
    WFWLUHWAWBWCWEWLUIWAWBWCWEWLUJWAWBWCWEWLUKWAWFWHWJWKULVQWBWCQZWEWHQZKZXPXOX
    SXPQZWPXOXSWPXFXBUMXTCWGCWDXSXPCWGUNZCWDUNZXPYAQWPCCNZXARPZXBKZXSYBYAYEXPYA
    YDXFWPXBYAYCXEXARCWGCUOUPURUSXSYEYBXSYEQCDUNZYBXSYEYFYEYDXSYFWPYDXBUTXSVQWB
    WBWCYDYFSVQXQXRVAZVQWBWCXRVBZYHVQWBWCXRVCCCDFVDVETVHXSWPXBYFYBSYDXSXBYFYBXB
    YFQXLYCRPZXSYBYFYIXBYFXLWTYCXARCDWDVFCDCUOVGUSXSVQWBWEWBYIYBSYGYHVQXQWEWHVI
    YHCWDCFVJVETVKVLVMVNTVKVOVMVNVPTVH $.

  $( Lemma for ~ btwnconn1 .  Now, we introduce the last three points used in
     the construction: ` P ` , ` Q ` , and ` R ` will turn out to be equal
     further down, and will provide us with the key to the final statement.  We
     begin by establishing congruence of ` R P ` and ` E d ` .  (Contributed by
     Scott Fenton, 8-Oct-2013.) $)
  btwnconn1lem8 $p |- (
     ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\
           ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) /\
         ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ R e. ( EE ` N ) ) ) /\
         ( ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\
               ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\
             ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\
               ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\
             ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\
               ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) /\
           ( ( E Btwn <. C , c >. /\ E Btwn <. D , d >. ) /\
             ( ( C Btwn <. c , P >. /\ <. C , P >. Cgr <. C , d >. ) /\
               ( C Btwn <. d , R >. /\ <. C , R >. Cgr <. C , E >. ) /\
               ( R Btwn <. P , Q >. /\ <. R , Q >. Cgr <. R , P >. ) ) ) ) ) ->
       <. R , P >. Cgr <. E , d >. ) $=
    ( wcel w3a wa wne cop cbtwn wbr ccgr cn cee cfv cv simpr2l ad2antll simpr1r
    ccgr3 wb simp11 simp2l1 simp31 cgrcomlr syl122anc cgrcom bitrd adantr mpbid
    simp2r1 simp33 simp2r3 simp2l3 simpr1l btwncomand adantl wi btwnintr mp2and
    simprll simpr2r cgrextendand brcgr3 syl133anc mpbir3and cgrrflx2d jca simp1
    3jca simp2l simp2r simprl btwnconn1lem7 syl2an necomd brofs2 anbi1d 5segofs
    simpl cofs sylbird syl333anc ) IUAMZAIUBUCZMZBWMMZNZCWMMZDWMMZKUDZWMMZNZLUD
    ZWMMZJUDZWMMZHWMMZNZOZEWMMZFWMMZGWMMZNZNZABPBCPCWSPNBACQRSBADQRSOODAWSQRSDW
    SQCDQZTSOCAXBQRSCXBQZXNTSOOWSAXDQZRSWSXDQCBQTSOXBXPRSXBXDQDBQTSOONZHCWSQRSZ
    HDXBQRSZOZCWSEQRSZCEQXOTSZOZCXBGQZRSZCGQZCHQZTSZOZGEFQRSGFQGEQZTSOZNZOZOZOZ
    YEXBYFQEYGQUHSZXBEQEXBQTSZYBOZNZXBCPZYJHXBQZTSZYOYEYPYRYMYEXMXQYEYHYCYKXTUE
    UFZYOYPXBCQZECQZTSZYDEHQZTSZYHYOYBUUFYMYBXMXQYAYBYIYKXTUGUFZXMYBUUFUIYNXMYB
    UUEUUDTSZUUFXMWLWQXIWQXCYBUUJUIWLWNWOXHXLUJZWQWRWTXGWPXLUKZWPXHXIXJXKULZUUL
    XCXEXFXAWPXLUSZCECXBIUMUNXMWLXIWQXCWQUUJUUFUIUUKUUMUULUUNUULECXBCIUOUNUPUQU
    RZXMYNXBCGECHIUUKUUNUULWPXHXIXJXKUTZUUMUULXCXEXFXAWPXLVAZUUCYOCEWSQRSZXRCUU
    GRSZXMYNCWSEIUUKUULWQWRWTXGWPXLVBZUUMYMYAXMXQYAYBYIYKXTVCUFVDYNXRXMXQXRXSYL
    VIVEXMUURXROUUSVFZYNXMWLXIWQXFWTUVAUUKUUMUULUUQUUTECHWSIVGUNUQVHUUOYMYHXMXQ
    YEYHYCYKXTVJUFZVKUVBXMYPUUFUUHYHNUIZYNXMWLXCWQXKXIWQXFUVCUUKUUNUULUUPUUMUUL
    UUQXBCGECHIVLVMUQVNYOYQYBXMYQYNXMXBEIUUKUUNUUMVOUQUUIVPVRYOCXBXMWPXAXGNXQXT
    OCXBPYNXMWPXAXGWPXHXLVQWPXAXGXLVSWPXAXGXLVTVRYNXQXTXQYMWHXQXTYLWAVPABCDHIJK
    LWBWCWDXMYSYTOZUUBVFZYNXMWLXCWQXKXIXIWQXFXCUVEUUKUUNUULUUPUUMUUMUULUUQUUNWL
    XCWQNXKXIXINWQXFXCNNZUVDUUDYJQUUEUUAQWISZYTOUUBUVFUVGYSYTXBCGEECHXBIWEWFXBC
    GEECHXBIWGWJWKUQVH $.

  $( Lemma for ~ btwnconn1 .  Now, a quick use of transitivity to establish
     congruence on ` R Q ` and ` E D ` .  (Contributed by Scott Fenton,
     8-Oct-2013.) $)
  btwnconn1lem9 $p |- (
     ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\
           ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) /\
         ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ R e. ( EE ` N ) ) ) /\
         ( ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\
               ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\
             ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\
               ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\
             ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\
               ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) /\
           ( ( E Btwn <. C , c >. /\ E Btwn <. D , d >. ) /\
             ( ( C Btwn <. c , P >. /\ <. C , P >. Cgr <. C , d >. ) /\
               ( C Btwn <. d , R >. /\ <. C , R >. Cgr <. C , E >. ) /\
               ( R Btwn <. P , Q >. /\ <. R , Q >. Cgr <. R , P >. ) ) ) ) ) ->
       <. R , Q >. Cgr <. E , D >. ) $=
    ( wcel w3a cv wa cop cbtwn wbr ccgr cn cee cfv simp11 simp33 simp32 simp2r3
    simp2l2 simp2r1 simp31 simpr3r ad2antll btwnconn1lem8 cgrtrand simp1 simp2l
    wne simp2r 3jca simpl simprl jca btwnconn1lem6 syl2an cgrtr3and ) IUAMZAIUB
    UCZMZBVGMZNZCVGMZDVGMZKOZVGMZNZLOZVGMZJOZVGMZHVGMZNZPZEVGMZFVGMZGVGMZNZNZAB
    UQBCUQCVMUQNBACQRSBADQRSPPDAVMQRSDVMQCDQZTSPCAVPQRSCVPQZWHTSPPVMAVRQZRSVMVR
    QCBQTSPVPWJRSVPVRQDBQTSPPNZHCVMQRSHDVPQRSPZCVMEQRSCEQWITSPZCVPGQRSCGQCHQTSP
    ZGEFQRSZGFQGEQTSZPNZPZPZGFHDHVPIVFVHVIWBWFUDZVJWBWCWDWEUEZVJWBWCWDWEUFZVQVS
    VTVOVJWFUGZVKVLVNWAVJWFUHXCVQVSVTVOVJWFUIZWGWSGFGEHVPIWTXAXBXAVJWBWCWDWEUJX
    CXDWRWPWGWKWOWPWMWNWLUKULABCDEFGHIJKLUMUNWGVJVOWANWKWLPHDQHVPQTSWSWGVJVOWAV
    JWBWFUOVJVOWAWFUPVJVOWAWFURUSWSWKWLWKWRUTWKWLWQVAVBABCDHIJKLVCVDVE $.

  $( Lemma for ~ btwnconn1 .  Now we establish a congruence that will give us
     ` D = d ` when we compute ` P = Q ` later on.  (Contributed by Scott
     Fenton, 8-Oct-2013.) $)
  btwnconn1lem10 $p |- (
     ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\
           ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) /\
         ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ R e. ( EE ` N ) ) ) /\
         ( ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\
               ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\
             ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\
               ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\
             ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\
               ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) /\
           ( ( E Btwn <. C , c >. /\ E Btwn <. D , d >. ) /\
             ( ( C Btwn <. c , P >. /\ <. C , P >. Cgr <. C , d >. ) /\
               ( C Btwn <. d , R >. /\ <. C , R >. Cgr <. C , E >. ) /\
               ( R Btwn <. P , Q >. /\ <. R , Q >. Cgr <. R , P >. ) ) ) ) ) ->
       <. d , D >. Cgr <. P , Q >. ) $=
    ( wcel w3a cv wa cop cbtwn wbr ccgr cn cee cfv simp11 simp2r1 simp31 simp33
    wne simp2r3 simp2l2 simp32 simprlr adantl btwncomand ad2antll btwnconn1lem8
    simpr3l wb cgrcomlr syl122anc cgrcom bitrd mpbid btwnconn1lem9 cgrextendand
    adantr cgrcomand ) IUAMZAIUBUCZMZBVIMZNZCVIMZDVIMZKOZVIMZNZLOZVIMZJOZVIMZHV
    IMZNZPZEVIMZFVIMZGVIMZNZNZABUHBCUHCVOUHNBACQRSBADQRSPPDAVOQRSDVOQCDQZTSPCAV
    RQRSCVRQZWJTSPPVOAVTQZRSVOVTQCBQTSPVRWLRSVRVTQDBQTSPPNZHCVOQRSZHDVRQRSZPZCV
    OEQRSCEQWKTSPZCVRGQRSCGQCHQTSPZGEFQRSZGFQGEQZTSZPNZPZPZVRHDEGFIVHVJVKWDWHUD
    ZVSWAWBVQVLWHUEZVSWAWBVQVLWHUIZVMVNVPWCVLWHUJZVLWDWEWFWGUFZVLWDWEWFWGUGZVLW
    DWEWFWGUKZWIXDHDVRIXEXGXHXFXDWOWIWMWNWOXBULUMUNXCWSWIWMWSXAWQWRWPUQUOWIXDPW
    THVRQTSZVRHQZEGQZTSZABCDEFGHIJKLUPWIXLXOURXDWIXLXNXMTSZXOWIVHWGWEWBVSXLXPUR
    XEXJXIXGXFGEHVRIUSUTWIVHWEWGVSWBXPXOURXEXIXJXFXGEGVRHIVAUTVBVFVCWIXDGFHDIXE
    XJXKXGXHABCDEFGHIJKLVDVGVE $.

  $( Lemma for ~ btwnconn1 .  Now, we establish that ` D ` and ` Q ` are
     equidistant from ` C ` .  (Contributed by Scott Fenton, 8-Oct-2013.) $)
  btwnconn1lem11 $p |- (
     ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\
           ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) /\
         ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ R e. ( EE ` N ) ) ) /\
         ( ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\
               ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\
             ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\
               ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\
             ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\
               ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) /\
           ( ( E Btwn <. C , c >. /\ E Btwn <. D , d >. ) /\
             ( ( C Btwn <. c , P >. /\ <. C , P >. Cgr <. C , d >. ) /\
               ( C Btwn <. d , R >. /\ <. C , R >. Cgr <. C , E >. ) /\
               ( R Btwn <. P , Q >. /\ <. R , Q >. Cgr <. R , P >. ) ) ) ) ) ->
       <. D , C >. Cgr <. Q , C >. ) $=
    ( wcel w3a wa cop cbtwn wbr ccgr wb cee cfv wne btwnconn1lem8 btwnconn1lem9
    cn cv wceq btwnconn1lem10 adantr wi simpr3r adantl simpr2r jca opeq2 breq2d
    anbi2d 3anbi12d anbi12d biimpar simpr1 simp11 simp33 simp31 simp2r1 axcgrid
    3jca opeq1 syl5 breq12d breq1d biimpac simpll simp32 simprlr simpr3 simp2l2
    syl13anc imp opeq2d simp2l1 cgrcomlr syl122anc cgrcom bitrd mpbid ex anbi1d
    3anbi23d imbi12d syl5ibcom com23 mpdd expd exp4d imp31 mpd ccgr3 btwncomand
    simp2r3 cgrcomand brcgr3 syl133anc mpbir3and simpr1r ad2antll simpr 5segofs
    cofs brofs2 sylbird syl333anc ad2antrr mp2and pm2.61dane ) IUFMZAIUAUBZMZBX
    RMZNZCXRMZDXRMZKUGZXRMZNZLUGZXRMZJUGZXRMZHXRMZNZOZEXRMZFXRMZGXRMZNZNZABUCBC
    UCCYDUCNBACPQRBADPQROODAYDPQRDYDPCDPZSROCAYGPQRCYGPZYSSROOYDAYIPZQRYDYIPCBP
    SROYGUUAQRYGYIPDBPSROONZHCYDPQRZHDYGPQRZOZCYDEPQRZCEPZYTSRZOZCYGGPQRZCGPZCH
    PZSRZOZGEFPZQRZGFPZGEPZSRZOZNZOZOZOZDCPZFCPZSRZYGHUVDYGHUHZOUURHYGPZSRZUUQH
    DPZSRZYGDPZUUOSRZNZUVGUVDUVOUVHUVDUVJUVLUVNABCDEFGHIJKLUDZABCDEFGHIJKLUEZAB
    CDEFGHIJKLUIZVHUJYRUVCUVHUVOUVGUKZUVCUUSUUMOZYRUVHUVSUKUVCUUSUUMUVBUUSUUBUU
    PUUSUUIUUNUUEULUMUVBUUMUUBUUJUUMUUIUUTUUEUNZUMUOYRUVHUVTUVSYRUVHUVTUVOUVGUV
    HUVTUVOOZOUUSUUKYTSRZOZUURYGYGPZSRZUUQUVMSRZUVNNZOZYRUVGUVHUWIUWBUVHUWDUVTU
    WHUVOUVHUWCUUMUUSUVHYTUULUUKSYGHCUPUQURUVHUWFUVJUWGUVLUVNUVHUWEUVIUURSYGHYG
    VIUQUVHUVMUVKUUQSYGHDVIUQUSUTVAYRUWIGEUHZUVGUWIUWFYRUWJUWDUWFUWGUVNVBYRXQYP
    YNYHUWFUWJUKXQXSXTYMYQVCZYAYMYNYOYPVDZYAYMYNYOYPVEZYHYJYKYFYAYQVFZGEYGIVGVS
    VJYRUWIUWJUVGUWIUWJOUUOEEPZSRZUUHOZUWOUWESRZUUOUVMSRZUVNNZOZYRUVGUWJUWIUXAU
    WJUWDUWQUWHUWTUWJUUSUWPUWCUUHUWJUUQUUOUURUWOSGEFVIZGEEVIZVKUWJUUKUUGYTSGECU
    PVLUTUWJUWFUWRUWGUWSUVNUWJUURUWOUWESUXCVLUWJUUQUUOUVMSUXBVLUSUTVMYRUXAEFUHZ
    UVGUXAUWPYRUXDUWPUUHUWTVNYRXQYNYOYNUWPUXDUKUWKUWMYAYMYNYOYPVOZUWMEFEIVGVSVJ
    YRUXDUXAUVGYRUWOUWOSRZUUHOZUWRUWOUVMSRZUVMUWOSRZNZOZUVEECPZSRZUKUXDUXAUVGUK
    YRUXKUXMYRUXKOZUUHUXMYRUXFUUHUXJVPUXNUUHUUGYSSRZUXMUXNYTYSUUGSUXNYGDCYRUXKY
    GDUHZUXKUXIYRUXPUXGUWRUXHUXIVQYRXQYHYCYNUXIUXPUKUWKUWNYBYCYEYLYAYQVRZUWMYGD
    EIVGVSVJVTWAUQYRUXOUXMTUXKYRUXOUXLUVESRZUXMYRXQYBYNYBYCUXOUXRTUWKYBYCYEYLYA
    YQWBZUWMUXSUXQCECDIWCWDYRXQYNYBYCYBUXRUXMTUWKUWMUXSUXQUXSECDCIWEWDWFUJWFWGW
    HUXDUXKUXAUXMUVGUXDUXGUWQUXJUWTUXDUXFUWPUUHUXDUWOUUOUWOSEFEUPZVLWIUXDUXHUWS
    UXIUVNUWRUXDUWOUUOUVMSUXTVLUXDUWOUUOUVMSUXTUQWJUTUXDUXLUVFUVESEFCVIUQWKWLWM
    WNVJWOWNVJWPWMVJWQWRUVDYGHUCZOHUVMQRZYGUVKPEUUQPWSRZYGCPZUXLSRZHCPZGCPZSRZO
    ZNZUYAUVGUVDUYJUYAUVDUYBUYCUYIYRUVCHDYGIUWKYHYJYKYFYAYQXAZUXQUWNUVCUUDYRUUB
    UUCUUDUVAVPUMWTUVDUYCYGHPZEGPZSRZUVNUVKUUQSRZUVDUVJUYNUVPYRUVJUYNTUVCYRUVJU
    YMUYLSRZUYNYRXQYPYNYKYHUVJUYPTUWKUWLUWMUYKUWNGEHYGIWCWDYRXQYNYPYHYKUYPUYNTU
    WKUWMUWLUWNUYKEGYGHIWEWDWFUJWGUVRYRUVCGFHDIUWKUWLUXEUYKUXQUVQXBYRUYCUYNUVNU
    YONTZUVCYRXQYHYKYCYNYPYOUYQUWKUWNUYKUXQUWMUWLUXEYGHDEGFIXCXDUJXEUVDUYEUYHUV
    DUUHUYEUVBUUHYRUUBUUFUUHUUNUUTUUEXFXGYRUUHUYETUVCYRUUHUXLUYDSRZUYEYRXQYBYNY
    BYHUUHUYRTUWKUXSUWMUXSUWNCECYGIWCWDYRXQYNYBYHYBUYRUYETUWKUWMUXSUWNUXSECYGCI
    WEWDWFUJWGUVDUUMUYHUVBUUMYRUUBUWAXGYRUUMUYHTUVCYRUUMUYGUYFSRZUYHYRXQYBYPYBY
    KUUMUYSTUWKUXSUWLUXSUYKCGCHIWCWDYRXQYPYBYKYBUYSUYHTUWKUWLUXSUYKUXSGCHCIWEWD
    WFUJWGUOVHUJUVDUYAXHYRUYJUYAOZUVGUKZUVCUYAYRXQYHYKYCYBYNYPYOYBVUAUWKUWNUYKU
    XQUXSUWMUWLUXEUXSXQYHYKNYCYBYNNYPYOYBNNZUYTUYLUVEPUYMUVFPXJRZUYAOUVGVUBVUCU
    YJUYAYGHDCEGFCIXKWIYGHDCEGFCIXIXLXMXNXOXP $.

  $( Lemma for ~ btwnconn1 .  Using a long string of invocations of ~ linecgr ,
     we show that ` D = d ` .  (Contributed by Scott Fenton, 9-Oct-2013.) $)
  btwnconn1lem12 $p |- (
     ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\
           ( d e. ( EE ` N ) /\ b e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) /\
         ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ R e. ( EE ` N ) ) ) /\
         ( ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\
               ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\
             ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\
               ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\
             ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\
               ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) /\
           ( ( E Btwn <. C , c >. /\ E Btwn <. D , d >. ) /\
             ( ( C Btwn <. c , P >. /\ <. C , P >. Cgr <. C , d >. ) /\
               ( C Btwn <. d , R >. /\ <. C , R >. Cgr <. C , E >. ) /\
               ( R Btwn <. P , Q >. /\ <. R , Q >. Cgr <. R , P >. ) ) ) ) ) ->
       D = d ) $=
    ( wcel w3a wa cop cbtwn wbr ccgr wi cee cfv wne wceq simp11 simp2l1 simp2l3
    cn cv simp31 simp32 simp1l3 ad2antrl ccolin ad2antll btwncolinear5 syl13anc
    simpr1l simp2l2 simp2r1 simpr1r simp2rr cgrtrand btwnconn1lem11 cgrcomlrand
    adantr mpd weq simp12 simp13 simp2r2 simp1rr btwnexchand btwnexch3and opeq1
    simp2ll simp3ll breq2d biimpac axbtwnid syl3anc syl5 expd simp1 simp2l 3jca
    simp2r simprl jca btwnconn1lem7 syl2an simp2rl simp3rl btwncolinear2 simp33
    simpr2r btwnconn1lem5 breq1d anbi1d simp2r3 breq12d biimpar necon3d simpr2l
    simpl opeq2 cgrid2 syland mp2and btwncolinear4 simpr3r cgrcomand linecgrand
    biimprd syl6ci com12 adantrl btwncolinear1 btwncolinear6 an12s ex pm2.61ine
    simp1rl btwnconn1lem10 biimpa axcgrid eqcomd ) IUHMZAIUAUBZMZBYIMZNZCYIMZDY
    IMZKUIZYIMZNZLUIZYIMZJUIZYIMZHYIMZNZOZEYIMZFYIMZGYIMZNZNZABUCZBCUCZCYOUCZNZ
    BACPQRZBADPQRZOZOZDAYOPQRZDYOPCDPZSRZOZCAYRPQRZCYRPZUUSSRZOZOZYOAYTPZQRZYOY
    TPCBPSRZOZYRUVGQRZYRYTPZDBPSRZOZOZNZHCYOPZQRHDYRPQROZCYOEPZQRZCEPUVCSRZOZCY
    RGPQRZCGPZCHPZSRZOZGEFPZQRZGFPGEPSRZOZNZOZOZOZYRDUWOEFUDZYRDPZUWHSRZYRDUDZU
    WOEEPUWHSRZUWPUUIUWNCYOEEFIYHYJYKUUDUUHUEZYMYNYPUUCYLUUHUFZYMYNYPUUCYLUUHUG
    ZYLUUDUUEUUFUUGUJZUXDYLUUDUUEUUFUUGUKZUVPUULUUIUWMUUJUUKUULUUPUVFUVOULUMZUW
    OUVTCUVSUNRZUWMUVTUUIUVPUVTUWAUWGUWKUVRURUOUUIUVTUXGTZUWNUUIYHYPUUEYMUXHUXA
    UXCUXDUXBYOECIUPUQVFVGUUIUWNCECDCFIUXAUXBUXDUXBYMYNYPUUCYLUUHUSZUXBUXEUUIUW
    NCECYRCDIUXAUXBUXDUXBYSUUAUUBYQYLUUHUTZUXBUXIUWMUWAUUIUVPUVTUWAUWGUWKUVRVAU
    OUVPUVDUUIUWMUVBUVDUVAUUQUVOVBUMVCUUIUWNDCFCIUXAUXIUXBUXEUXBABCDEFGHIJKLVDV
    EVCZUWOUVSYOFPZSRZTBYTUWOBYTUDZUXMUWOUXNKJVHZYTEPZYTFPZSRZUXMUWOYOBYTPZQRZU
    XNUXOTZUUIUWNABYOYTIUXAYHYJYKUUDUUHVIZYHYJYKUUDUUHVJZUXCYSUUAUUBYQYLUUHVKZU
    UIUWNABDYOIUXAUYBUYCUXIUXCUVPUUOUUIUWMUUNUUOUUMUVFUVOVLUMUVPUURUUIUWMUURUUT
    UVEUUQUVOVPUMVMUVPUVHUUIUWMUVHUVIUVNUUQUVFVQUMVNZUUIUXTUYATUWNUUIUXTUXNUXOU
    XTUXNOYOYTYTPZQRZUUIUXOUXNUXTUYGUXNUXSUYFYOQBYTYTVOVRVSUUIYHYPUUAUYGUXOTUXA
    UXCUYDYOYTIVTWAWBWCVFVGUUIUWNCYRYTEFIUXAUXBUXJUYDUXDUXEUUIYLYQUUCNZUVPUVROZ
    CYRUCUWNUUIYLYQUUCYLUUDUUHWDYLYQUUCUUHWEYLYQUUCUUHWGWFZUWNUVPUVRUVPUWMXEUVP
    UVRUWLWHWIZABCDHIJKLWJWKZUWOYRCYTPQRZCUVLUNRZUUIUWNACYRYTIUXAUYBUXBUXJUYDUV
    PUVBUUIUWMUVBUVDUVAUUQUVOWLUMZUVPUVKUUIUWMUVKUVMUVJUUQUVFWMUMVNUUIUYMUYNTZU
    WNUUIYHYMUUAYSUYPUXAUXBUYDUXJCYTYRIWNUQVFVGUXKUUIUWNGCYREFIUXAYLUUDUUEUUFUU
    GWOZUXBUXJUXDUXEUWOUULGCUCUXFUWOGCCYOUWOUWFHCPZHYOPZSRZGCUDZCYOUDZTZUWMUWFU
    UIUVPUWCUWFUWBUWKUVRWPUOUUIUYHUYIUYTUWNUYJUYKABCDHIJKLWQWKUUIUWFUYTOZVUCTUW
    NUUIVUDVUAVUBVUDVUAOCCPZUWESRZUYTOZUUIVUBVUAVUDVUGVUAUWFVUFUYTVUAUWDVUEUWES
    GCCXFWRWSVSUUIVUFCHUDZUYTVUBUUIYHYMYMUUBVUFVUHTUXAUXBUXBYSUUAUUBYQYLUUHWTCC
    HIXGUQVUHUYTOVUEUVQSRZUUIVUBVUHVUIUYTVUHVUEUYRUVQUYSSCHCVOCHYOVOXAXBUUIYHYM
    YMYPVUIVUBTUXAUXBUXBUXCCCYOIXGUQWBXHWBWCVFXIXCVGUWOUWCGUVCUNRZUWMUWCUUIUVPU
    WCUWFUWBUWKUVRXDUOUUIUWCVUJTZUWNUUIYHYSUUGYMVUKUXAUXJUYQUXBYRGCIXJUQVFVGUUI
    UWNGFGEIUXAUYQUXEUYQUXDUWMUWJUUIUVPUWIUWJUWBUWGUVRXKUOXLUXKXMZXMZUXOUXMUXRU
    XOUVSUXPUXLUXQSYOYTEVOYOYTFVOXAXNXOXPBYTUCZUWOUXMUUIVUNUWNUXMUUIVUNUWNOZBYT
    YOEFIUXAUYCUYDUXCUXDUXEUUIVUNUWNWHUUIVUOOUXTBYTYOPUNRZUUIUWNUXTVUNUYEXQUUIU
    XTVUPTZVUOUUIYHYKUUAYPVUQUXAUYCUYDUXCBYTYOIXRUQVFVGUUIUWNBEPBFPSRVUNUUIUWNC
    YRBEFIUXAUXBUXJUYCUXDUXEUYLUWOCBYRPQRZCYRBPUNRZUUIUWNABCYRIUXAUYBUYCUXBUXJU
    VPUUNUUIUWMUUNUUOUUMUVFUVOYCUMUYOVNUUIVURVUSTZUWNUUIYHYKYSYMVUTUXAUYCUXJUXB
    BYRCIXSUQVFVGUXKVULXMXQUUIUWNUXRVUNVUMXQXMXTYAYBXMUUIUWTUWPTZUWNUUIYHUUEUUE
    UUFVVAUXAUXDUXDUXEEEFIXGUQVFVGABCDEFGHIJKLYDUUIUWPUWROZUWSTUWNVVBUWQFFPZSRZ
    UUIUWSUWPUWRVVDUWPUWHVVCUWQSEFFVOVRYEUUIYHYSYNUUFVVDUWSTUXAUXJUXIUXEYRDFIYF
    UQWBVFXIYG $.

  ${
    $d A e p q r $.  $d B e p q r $.  $d C e p q r $.  $d D e p q r $.
    $d N e p q r $.  $d b e p q r $.  $d c e p q r $.  $d d e p q r $.
    $( Lemma for ~ btwnconn1 .  Begin back-filling and eliminating hypotheses.
       (Contributed by Scott Fenton, 9-Oct-2013.) $)
    btwnconn1lem13 $p |- (
     ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\
           ( d e. ( EE ` N ) /\ b e. ( EE ` N ) ) ) ) /\
         ( ( ( A =/= B /\ B =/= C ) /\
               ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\
             ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\
               ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\
             ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\
               ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) ) ->
       ( C = c \/ D = d ) ) $=
      ( vp vr wcel w3a cv wa cop cbtwn wbr ccgr adantr ad3antrrr ve cee cfv wne
      vq cn wceq wn df-ne wrex simp2rl simp2ll wb simpl1 simprl1 simpl2 simprrl
      jca btwncom syl13anc simprl2 simprl3 anbi12d imbitrid wi axpasch syld imp
      syl132anc axsegcon syl122anc simpr reeanv sylanbrc ad2antrr simprl simprr
      simpll1 simp-4l simplrl simprrr simpllr 3jca simplrr jca32 btwnconn1lem12
      simp1ll simp1lr simpl1r simpll2 simpl3l simpl3r rexlimddv exp32 rexlimdvv
      syl2an an4s mpd expr biimtrrid orrd ) EUFKZAEUBUCZKZBXCKZLZCXCKZDXCKZGMZX
      CKZLZHMZXCKZFMZXCKZNZNZNZABUDZBCUDZNZBACOPQBADOPQNZNZDAXIOPQZDXIOCDOZRQZN
      ZCAXLOPQZCXLOZYERQZNZNZXIAXNOZPQXIXNOCBORQNZXLYMPQXLXNODBORQNZNZLZNZCXIUG
      ZDXLUGZYSUHCXIUDZYRYTCXIUIXRYQUUAYTXRYQUUANZNUAMZCXIOPQUUCDXLOPQNZYTUAXCX
      RUUBUUDUAXCUJZXRUUBCXLAOPQZDXIAOPQZNZUUEUUBYHYDNXRUUHUUBYHYDYQYHUUAYHYJYG
      YCYPUKSYQYDUUAYDYFYKYCYPULSURXRYHUUFYDUUGXRXBXGXDXMYHUUFUMXBXDXEXQUNZXGXH
      XJXPXFUOZXBXDXEXQUPZXFXKXMXOUQZCAXLEUSUTXRXBXHXDXJYDUUGUMUUIXGXHXJXPXFVAZ
      UUKXGXHXJXPXFVBZDAXIEUSUTVCVDXRXBXMXJXDXGXHUUHUUEVEUUIUULUUNUUKUUJUUMUAXL
      XIACDEVFVIVGVHXRUUCXCKZUUBUUDYTXRUUONZUUBUUDNZNZCXIIMZOPQCUUSOYIRQNZCXLJM
      ZOPQCUVAOCUUCORQNZNZJXCUJIXCUJZYTUUPUVDUUQUUPUUTIXCUJZUVBJXCUJZUVDUUPXBXJ
      XGXGXMUVEXBXDXEXQUUOVRZXRXJUUOUUNSXRXGUUOUUJSZUVHXRXMUUOUULSZIXICCXLEVJVK
      UUPXBXMXGXGUUOUVFUVGUVIUVHUVHXRUUOVLJXLCCUUCEVJVKUUTUVBIJXCXCVMVNSUURUVCY
      TIJXCXCUURUUSXCKZUVAXCKZNZUVCYTUUPUVLUUQUVCYTUUPUVLNZUUQUVCNZNUVAUUSUEMZO
      PQUVAUVOOUVAUUSORQNZYTUEXCUVMUVPUEXCUJZUVNUVMXBUVJUVKUVKUVJUVQXRXBUUOUVLU
      UIVOUUPUVJUVKVPZUUPUVJUVKVQZUVSUVRUEUUSUVAUVAUUSEVJVKSUVMUVOXCKZUVNUVPYTU
      VMUVTNZXFXKXMXOUUOLZNZUVJUVTUVKLZLXSXTUUALZYBNZYLYPLZUUDUUTUVBUVPLZNNYTUV
      NUVPNZUWAXFUWCUWDXFXQUUOUVLUVTVSUWAXKUWBUUPXKUVLUVTXFXKXPUUOVTVOUWAXMXOUU
      OXRXMUUOUVLUVTUULTXRXOUUOUVLUVTXFXKXMXOWATXRUUOUVLUVTWBWCURUWAUVJUVTUVKUU
      PUVJUVKUVTVTUVMUVTVLUUPUVJUVKUVTWDWCWCUWIUWGUUDUWHUWIUWFYLYPUWIUWEYBUWIXS
      XTUUAUVNXSUVPYQXSUUAUUDUVCXSXTYBYLYPWGTSUVNXTUVPYQXTUUAUUDUVCXSXTYBYLYPWH
      TSUVNUUAUVPYQUUAUUDUVCWBSWCUUBYBUUDUVCUVPYAYBYLYPUUAWITURUUQYLUVCUVPYCYLY
      PUUAUUDWJVOUWIYNYOUUBYNUUDUVCUVPYNYOYCYLUUAWKTUUBYOUUDUVCUVPYNYOYCYLUUAWL
      TURWCUUBUUDUVCUVPWBUWIUUTUVBUVPUUQUUTUVBUVPVTUUQUUTUVBUVPWDUVNUVPVLWCWEAB
      CDUUSUVOUVAUUCEFGHWFWPWQWMWQWNWOWRWQWMWSWTXA $.
  $}

  ${
    $d A b c d x $.  $d B b c d x $.  $d C b c d x $.  $d D b c d x $.
    $d N b c d x $.
    $( Lemma for ~ btwnconn1 .  Final statement of the theorem when
       ` B =/= C ` .  (Contributed by Scott Fenton, 9-Oct-2013.) $)
    btwnconn1lem14 $p |- ( (
     ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
       ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) /\
       ( ( A =/= B /\ B =/= C ) /\
         ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) ) ->
         ( C Btwn <. A , D >. \/ D Btwn <. A , C >. ) ) $=
      ( vc vd vb vx wcel wa w3a cop cbtwn wbr cv ccgr wrex axsegcon 3jca cn cee
      cfv wne simp1 simp2l simp3r simp3 syl121anc simp3l reeanv sylanbrc adantr
      wo wceq simpl1 simpl2l simprl simpl3l simpl2r syl122anc simprr jca sylibr
      simpl3r weq simplrr simpll simplr simpr btwnconn1lem2 syl2an opeq2 breq2d
      breq1d anbi12d anbi2d biimpac jca32 btwnconn1lem13 syl5 expdimp mpd exp32
      an4s rexlimdvv orcom simprrl adantl syl5ibrcom simprll orim12d biimtrid
      ex ) EUAJZAEUBUCZJZBWPJZKZCWPJZDWPJZKZLZABUDBCUDKBACMZNOBADMZNOKKZKZDAFPZ
      MZNOZDXHMCDMZQOZKZCAGPZMZNOZCXNMXKQOZKZKZGWPRFWPRZCXENOZDXDNOZUNZXCXTXFXC
      XMFWPRZXRGWPRZXTXCWOWQXAXBYDWOWSXBUEZWOWQWRXBUFZWOWSWTXAUGWOWSXBUHZFADCDE
      SUIXCWOWQWTXBYEYFYGWOWSWTXAUJYHGACCDESUIXMXRFGWPWPUKULUMXGXSYCFGWPWPXGXHW
      PJZXNWPJZKZXSYCXCYKXFXSYCXCYKKZXFXSKZKZCXHUOZDXNUOZUNZYCYNXHAHPZMZNOXHYRM
      CBMQOKZXNAIPZMZNOZXNUUAMZDBMZQOZKZKZIWPRHWPRZYQYNYTHWPRZUUGIWPRZKZUUIYLUU
      LYMYLUUJUUKYLWOWQYIWTWRUUJWOWSXBYKUPZWQWRWOXBYKUQZXCYIYJURZWTXAWOWSYKUSZW
      QWRWOXBYKUTZHAXHCBESVAYLWOWQYJXAWRUUKUUMUUNXCYIYJVBWTXAWOWSYKVEZUUQIAXNDB
      ESVAVCUMYTUUGHIWPWPUKVDYNUUHYQHIWPWPYNYRWPJZUUAWPJZKZUUHYQYLUVAYMUUHYQYLU
      VAKZYMUUHKZKIHVFZYQUVBWOWQWRLZWTXAYILZYJUUSUUTLZLXFXSUUHLUVDUVCUVBUVEUVFU
      VGYLUVEUVAYLWOWQWRUUMUUNUUQTUMZYLUVFUVAYLWTXAYIUUPUURUUOTUMZUVBYJUUSUUTXC
      YIYJUVAVGZYLUUSUUTURZYLUUSUUTVBTTUVCXFXSUUHXFXSUUHVHXFXSUUHVIYMUUHVJTABCD
      EUUAHFGVKVLUVBUVCUVDYQUVCUVDKYMYTXNYSNOZXNYRMZUUEQOZKZKZKZUVBYQUVDUVCUVQU
      VDUUHUVPYMUVDUUGUVOYTUVDUUCUVLUUFUVNUVDUUBYSXNNUUAYRAVMVNUVDUUDUVMUUEQUUA
      YRXNVMVOVPVQVQVRUVBUVQYQUVBUVEUVFYJUUSKZKKXFXSUVPLYQUVQUVBUVEUVFUVRUVHUVI
      UVBYJUUSUVJUVKVCVSUVQXFXSUVPXFXSUVPVHXFXSUVPVIYMUVPVJTABCDEHFGVTVLWNWAWBW
      CWEWDWFWCYQYPYOUNYNYCYOYPWGYNYPYAYOYBYNYAYPXPYMXPYLXFXMXPXQWHWIYPXEXOCNDX
      NAVMVNWJYNYBYOXJYMXJYLXFXJXLXRWKWIYOXDXIDNCXHAVMVNWJWLWMWCWEWDWFWC $.
  $}

  $( Connectitivy law for betweenness.  Theorem 5.1 of [Schwabhauser] p. 39-41.
     (Contributed by Scott Fenton, 9-Oct-2013.) $)
  btwnconn1 $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
     ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
     ( ( A =/= B /\ B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ->
       ( C Btwn <. A , D >. \/ D Btwn <. A , C >. ) ) ) $=
    ( cn wcel cee cfv wa w3a wne cop cbtwn wbr wo wi wceq breq1 ex orc 3ad2ant3
    3anbi3d biimtrdi adantld simpr1 simpl 3simpc jca31 btwnconn1lem14 pm2.61ine
    adantl sylan2 an12s ) EFGAEHIZGBUOGJCUOGDUOGJKZABLZBACMZNOZBADMZNOZKZCUTNOZ
    DURNOZPZUPVBJZVEQBCBCRZVBVEUPVGVBUQUSVCKVEVGVAVCUQUSBCUTNSUCVCUQVEUSVCVDUAU
    BUDUEBCLZVFVEUPVHVBVEVHVBJZUPUQVHJUSVAJZJVEVIUQVHVJVHUQUSVAUFVHVBUGVBVJVHUQ
    USVAUHULUIABCDEUJUMUNTUKT $.

  $( Another connectivity law for betweenness.  Theorem 5.2 of [Schwabhauser]
     p. 41.  (Contributed by Scott Fenton, 9-Oct-2013.) $)
  btwnconn2 $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
    ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
    ( ( A =/= B /\ B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ->
      ( C Btwn <. B , D >. \/ D Btwn <. B , C >. ) ) ) $=
    ( cn wcel cee cfv wa w3a wne cop cbtwn wbr wo btwnconn1 wi btwnexch3 ex mpd
    simpr2 anim1i ad2antrr simpr3 simp3r simp3l jca syld3an3 mpand orim12d mpdd
    adantr ) EFGZAEHIZGBUOGJZCUOGZDUOGZJZKZABLZBACMZNOZBADMZNOZKZCVDNOZDVBNOZPZ
    CBDMNOZDBCMNOZPZABCDEQUTVFVIVLRUTVFJZVGVJVHVKVMVGVJVMVGJVCVGJZVJVMVCVGUTVAV
    CVEUBUCUTVNVJRVFVGABCDESUDUATVMVEVHVKUTVAVCVEUEUTVEVHJVKRZVFUNUPUSURUQJVOUT
    URUQUNUPUQURUFUNUPUQURUGUHABDCESUIUMUJUKTUL $.

  ${
    $d N p $.  $d A p $.  $d B p $.  $d C p $.  $d D p $.
    $( Inner connectivity law for betweenness.  Theorem 5.3 of [Schwabhauser]
       p. 41.  (Contributed by Scott Fenton, 9-Oct-2013.) $)
    btwnconn3 $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
    ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
    ( ( B Btwn <. A , D >. /\ C Btwn <. A , D >. ) ->
      ( B Btwn <. A , C >. \/ C Btwn <. A , B >. ) ) ) $=
      ( vp cn wcel cee cfv wa w3a cv cop cbtwn wbr wne btwncomand btwnexch3and
      wi wo simp1 simp3r simp2l btwndiff syl3anc simprlr necomd simpl2l simpl2r
      wrex simpr simpl3r simprrl simprll simpl3l simprrr ex btwnconn2 syl122anc
      simpl1 3jca syld expd rexlimdva mpd ) EGHZAEIJZHZBVHHZKZCVHHZDVHHZKZLZADF
      MZNOPZAVPQZKZFVHUKZBADNZOPZCWAOPZKZBACNOPCABNOPUAZTZVOVGVMVIVTVGVKVNUBVGV
      KVLVMUCVGVIVJVNUDDAEFUEUFVOVSWFFVHVOVPVHHZKZVSWDWEWHVSWDKZVPAQZAVPBNOPZAV
      PCNOPZLZWEWHWIWMWHWIKZWJWKWLWNAVPWHVQVRWDUGUHWHWIABVPEVGVKVNWGVAZVIVJVGVN
      WGUIZVIVJVGVNWGUJZVOWGULZWHWIDBAVPEWOVLVMVGVKWGUMZWQWPWRWHWIBADEWOWQWPWSW
      HVSWBWCUNRWHVQVRWDUOZSRWHWIACVPEWOWPVLVMVGVKWGUPZWRWHWIDCAVPEWOWSXAWPWRWH
      WICADEWOXAWPWSWHVSWBWCUQRWTSRVBURWHVGWGVIVJVLWMWETWOWRWPWQXAVPABCEUSUTVCV
      DVEVF $.
  $}

  $( If two points fall in the same place in the middle of a segment, then they
     are identical.  (Contributed by Scott Fenton, 16-Oct-2013.)  (Revised by
     Mario Carneiro, 19-Apr-2014.) $)
  midofsegid $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
   ( D e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) ->
   ( ( D Btwn <. A , B >. /\ E Btwn <. A , B >. /\
       <. A , D >. Cgr <. A , E >. ) -> D = E ) ) $=
    ( cn wcel cee cfv wa w3a cop cbtwn wbr ccgr wceq simprl3 endofsegidand expr
    simprr simp2l simp3r simp3l cgrcomand eqcomd 3simpa adantl simp2r btwnconn3
    simp1 wo wi syl122anc adantr mpd mpjaod ex ) EFGZAEHIZGZBUSGZJZCUSGZDUSGZJZ
    KZCABLZMNZDVGMNZACLZADLZONZKZCDPZVFVMJZCVKMNZVNDVJMNZVFVMVPVNVFVMVPJZJDCVFV
    RADCEURVBVEUJZURUTVAVEUAZURVBVCVDUBZURVBVCVDUCZVFVMVPTVFVRACADEVSVTWBVTWAVH
    VIVLVPVFQUDRUESVFVMVQVNVFVMVQJACDEVSVTWBWAVFVMVQTVHVIVLVQVFQRSVOVHVIJZVPVQU
    KZVMWCVFVHVIVLUFUGVFWCWDULZVMVFURUTVCVDVAWEVSVTWBWAURUTVAVEUHACDBEUIUMUNUOU
    PUQ $.

  ${
    $d Q a x $.  $d N a x $.  $d A a x $.  $d B a x $.  $d C a x $.
    $( Generalization of ~ axsegcon .  This time, we generate an endpoint for a
       segment on the ray ` Q A ` congruent to ` B C ` and starting at ` Q ` ,
       as opposed to ~ axsegcon , where the segment starts at ` A `
       (Contributed by Scott Fenton, 14-Oct-2013.)  Remove unneeded inequality.
       (Revised by Scott Fenton, 15-Oct-2013.) $)
    segcon2 $p |- ( ( N e. NN /\
       ( Q e. ( EE ` N ) /\ A e. ( EE ` N ) ) /\
       ( B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
         E. x e. ( EE ` N ) ( ( A Btwn <. Q , x >. \/ x Btwn <. Q , A >. ) /\
           <. Q , x >. Cgr <. B , C >. ) ) $=
      ( va wcel wa w3a cv cop cbtwn wbr wrex wne axsegcon adantr wi mpd cee cfv
      cn ccgr wceq breq1 orbi1d anbi1d rexbidv simp1 simp2 ancomd syl3anc simpr
      wo simpl1 simpl2l simpl3 syl121anc anass df-3an simpr1 wb simpr2r simpl2r
      simprl syl122anc necon3bid mpbird necomd simpr2l btwncomand simpr3 simprr
      cgrdegen btwnconn2 mp3and sylan2br anim1d sylanb an32s reximdva rexlimdva
      expr simp2l simp3 orc anim1i reximi syl pm2.61ne ) FUCHZEFUAUBZHZBWMHZIZC
      WMHDWMHIZJZBEAKZLZMNZWSEBLMNZUOZWTCDLUDNZIZAWMOZEWTMNZXBUOZXDIZAWMOZBEBEU
      EZXEXIAWMXKXCXHXDXKXAXGXBBEWTMUFUGUHUIWRBEPZIZEBGKZLMNZEXNLBELUDNZIZGWMOZ
      XFWRXRXLWRWLWOWNIZXSXRWLWPWQUJZWRWNWOWLWPWQUKULZYAGBEBEFQUMRXMXQXFGWMWRXN
      WMHZXLXQXFSWRYBIZXLXQXFYCXLXQIZIZEXNWSLMNZXDIZAWMOZXFYCYHYDYCWLYBWNWQYHWL
      WPWQYBUPWRYBUNWNWOWLWQYBUQWLWPWQYBURAXNECDFQUSRYEYGXEAWMYCWSWMHZYDYGXESZY
      CYIIWRYBYIIZIZYDYJWRYBYIUTYLYDIYFXCXDYLYDYFXCYDYFIYLXLXQYFJZXCXLXQYFVAYLY
      MIZXNEPZEXNBLMNZYFXCYNEXNYNEXNPXLYLXLXQYFVBYNEXNBEYNXPEXNUEXKVCZXOXPXLYFY
      LVDYLXPYQSZYMYLWLWNYBWOWNYRWLWPWQYKUPZWNWOWLWQYKUQZWRYBYIVFZWNWOWLWQYKVEZ
      YTEXNBEFVOVGRTVHVIVJYLYMEBXNFYSYTUUBUUAXOXPXLYFYLVKVLYLXLXQYFVMYLYOYPYFJX
      CSZYMYLWLYBWNWOYIUUCYSUUAYTUUBWRYBYIVNXNEBWSFVPVGRVQVRWDVSVTWAWBTWDWAWCTW
      RXGXDIZAWMOZXJWRWLWNWNWQUUEXTWLWNWOWQWEZUUFWLWPWQWFAEECDFQUSUUDXIAWMXGXHX
      DXGXBWGWHWIWJWK $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Segment less than or equal to
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c Seg<_ $.

  $( Declare the constant for the segment less than or equal to
     relationship. $)
  csegle $a class Seg<_ $.

  ${
    $d p q n a b c d y $.
    $( Define the segment length comparison relationship.  This relationship
       expresses that the segment ` A B ` is no longer than ` C D ` .  In this
       section, we establish various properties of this relationship showing
       that it is a transitive, reflexive relationship on pairs of points that
       is substitutive under congruence.  Definition 5.4 of [Schwabhauser]
       p. 41.  (Contributed by Scott Fenton, 11-Oct-2013.) $)
    df-segle $a |- Seg<_ = { <. p , q >. |
       E. n e. NN E. a e. ( EE ` n ) E. b e. ( EE ` n ) E. c e. ( EE ` n )
       E. d e. ( EE ` n ) ( p = <. a , b >. /\ q = <. c , d >. /\
         E. y e. ( EE ` n ) ( y Btwn <. c , d >. /\
                              <. a , b >. Cgr <. c , y >. ) ) } $.
  $}

  ${
    $d A a b c d n p q y $.  $d N a b c d n y $.  $d D a b c d n p q y $.
    $d C a b c d n p q y $.  $d B a b c d n p q y $.
    $( Binary relation form of the segment comparison relationship.
       (Contributed by Scott Fenton, 11-Oct-2013.) $)
    brsegle $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
        ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
        ( <. A , B >. Seg<_ <. C , D >. <->
          E. y e. ( EE ` N ) ( y Btwn <. C , D >. /\
                  <. A , B >. Cgr <. C , y >. ) ) ) $=
      ( va vb vc vd vn cop wbr cv wceq wa wrex w3a cn wcel vp csegle cbtwn ccgr
      cee cfv opex eqeq1 eqcom bitrdi 3anbi1d rexbidv 2rexbidv 3anbi2d df-segle
      vq brab vex opth biid 3anbi123i 2rexbii rexbii wi simpl2l ad2antrl eleenn
      syl simprlr simprll adantl axdimuniq syl22anc fveq2d rexeqdv exbiri eleq1
      anassrs bi2anan9 anbi2d opeq12 breq1d breq2d opeq1 adantr sylan9bb imbi1d
      wb anbi12d 3imtr4d com12 expd 3impd rexlimdvv rexlimdvva rexlimdva simpl1
      biimtrid simpl2r simpl3l simpl3r eqidd simpr eqeq1d 3anbi23d opeq2 anbi1d
      rspc2ev syl113anc 3anbi13d syl3anc fveq2 3anbi3d rexeqbidv rspcev syl2anc
      expr ex impbid bitrid ) BCLZDELZUBMGNZHNZLZYAOZINZJNZLZYBOZANZYIUCMZYEYGY
      KLZUDMZPZAKNZUEUFZQZRZJYQQZIYQQZHYQQZGYQQZKSQZFSTZBFUEUFZTZCUUFTZPZDUUFTZ
      EUUFTZPZRZYKYBUCMZYADYKLZUDMZPZAUUFQZUANZYEOZUPNZYIOZYRRZJYQQZIYQQHYQQZGY
      QQKSQYFUVBYRRZJYQQZIYQQHYQQZGYQQKSQUUDUAUPYAYBUBBCUGDEUGUUSYAOZUVEUVHKGSY
      QUVIUVDUVGHIYQYQUVIUVCUVFJYQUVIUUTYFUVBYRUVIUUTYAYEOYFUUSYAYEUHYAYEUIUJUK
      ULUMUMUVAYBOZUVHUUBKGSYQUVJUVGYTHIYQYQUVJUVFYSJYQUVJUVBYJYFYRUVJUVBYBYIOY
      JUVAYBYIUHYBYIUIUJUNULUMUMAKUPUAGHIJUOUQUUMUUDUURUUDYCBOZYDCOZPZYGDOZYHEO
      ZPZYRRZJYQQIYQQZHYQQGYQQZKSQUUMUURUUCUVSKSUUAUVRGHYQYQYSUVQIJYQYQYFUVMYJU
      VPYRYRYCYDBCGURHURUSYGYHDEIURJURUSYRUTVAVBVBVCUUMUVSUURKSUUMYPSTZPZUVRUUR
      GHYQYQUWAYCYQTZYDYQTZPZPUVQUURIJYQYQUWAUWDYGYQTZYHYQTZPZUVQUURVDUWAUWDUWG
      PZPZUVMUVPYRUURUWIUVMUVPYRUURVDZUVMUVPPZUWIUWJUWKUWABYQTZCYQTZPZDYQTZEYQT
      ZPZPZPZUUQAYQQZUURVDZUWIUWJUVKUVLUVPUWSUXAVDUVKUVLUVPPPZUWSUURUWTUXBUWSPZ
      UUQAUUFYQUXCFYPUEUXCUUEUUGUVTUWLFYPOUXCUUGUUEUWAUUGUXBUWRUUGUUHUUEUULUVTV
      EVFZBFVGVHUXDUXBUUMUVTUWRVIUWSUWLUXBUWAUWLUWMUWQVJVKBYPFVLVMVNVOVPVRUWKUW
      HUWRUWAUVMUWDUWNUVPUWGUWQUVKUWBUWLUVLUWCUWMYCBYQVQYDCYQVQVSUVNUWEUWOUVOUW
      FUWPYGDYQVQYHEYQVQVSVSVTUWKYRUWTUURUWKYOUUQAYQUVMYOYLYAYMUDMZPZUVPUUQUVMY
      NUXEYLUVMYEYAYMUDYCYDBCWAWBVTUVPYLUUNUXEUUPUVPYIYBYKUCYGYHDEWAWCUVNUXEUUP
      WHUVOUVNYMUUOYAUDYGDYKWDWCZWEWIWFULWGWJWKWLWMXQWNWOWPWRUUMUURUUDUUMUURPZU
      UEYFYJYOAUUFQZRZJUUFQZIUUFQZHUUFQZGUUFQZUUDUUEUUIUULUURWQUXHUUGUUHYAYAOZY
      JUXFAUUFQZRZJUUFQIUUFQZUXNUUGUUHUUEUULUURVEUUGUUHUUEUULUURWSUXHUUJUUKUXOY
      BYBOZUURUXRUUJUUKUUEUUIUURWTUUJUUKUUEUUIUURXAUXHYAXBUXHYBXBUUMUURXCUXQUXO
      UXSUURRUXODYHLZYBOZYKUXTUCMZUUPPZAUUFQZRIJDEUUFUUFUVNYJUYAUXPUYDUXOUVNYIU
      XTYBYGDYHWDZXDUVNUXFUYCAUUFUVNYLUYBUXEUUPUVNYIUXTYKUCUYEWCUXGWIULXEUVOUYA
      UXSUYDUURUXOUVOUXTYBYBYHEDXFZXDUVOUYCUUQAUUFUVOUYBUUNUUPUVOUXTYBYKUCUYFWC
      XGULXEXHXIUXLUXRBYDLZYAOZYJYLUYGYMUDMZPZAUUFQZRZJUUFQIUUFQGHBCUUFUUFUVKUX
      JUYLIJUUFUUFUVKYFUYHUXIUYKYJUVKYEUYGYAYCBYDWDZXDUVKYOUYJAUUFUVKYNUYIYLUVK
      YEUYGYMUDUYMWBVTULXJUMUVLUYLUXQIJUUFUUFUVLUYHUXOUYKUXPYJUVLUYGYAYAYDCBXFZ
      XDUVLUYJUXFAUUFUVLUYIUXEYLUVLUYGYAYMUDUYNWBVTULXJUMXHXKUUCUXNKFSYPFOZUUBU
      XMGYQUUFYPFUEXLZUYOUUAUXLHYQUUFUYPUYOYTUXKIYQUUFUYPUYOYSUXJJYQUUFUYPUYOYR
      UXIYFYJUYOYOAYQUUFUYPVOXMXNXNXNXNXOXPXRXSXT $.
  $}

  ${
    $d N x y $.  $d A x y $.  $d B x y $.  $d C x y $.  $d D x y $.
    $( Alternate characterization of segment comparison.  Theorem 5.5 of
       [Schwabhauser] p. 41-42.  (Contributed by Scott Fenton, 11-Oct-2013.) $)
    brsegle2 $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
        ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
        ( <. A , B >. Seg<_ <. C , D >. <->
          E. x e. ( EE ` N ) ( B Btwn <. A , x >. /\
                  <. A , x >. Cgr <. C , D >. ) ) ) $=
      ( vy wcel wa w3a cop wbr ccgr wrex wi adantr mpd mp2and wb 3ad2ant1 cn cv
      cee csegle cbtwn brsegle ccgr3 ccolin simprl simpl1 simpl3l simpl3r simpr
      btwncolinear2 syl13anc simpl2l simpl2r simprr cgrcomand lineext syl131anc
      simpl2 simpll1 simplr brcgr3 syl133anc simp2l simp3 mpbird btwnxfr simp32
      cfv an32 cgrcom syl122anc mpbid jca 3expia sylbid sylanb an32s rexlimdva2
      reximdva btwncolinear1 simpl3 3jca syl113anc simp2r simp33 cgrcomlr bitrd
      impbid ) FUAHZBFUCVLZHZCWNHZIZDWNHZEWNHZIZJZBCKZDEKZUDLGUBZXCUELZXBDXDKZM
      LZIZGWNNZCBAUBZKZUELZXKXCMLZIZAWNNZGBCDEFUFXAXIXOXAXHXOGWNXAXDWNHZIZXHIZD
      XDEKZKZBCXJKZKZUGLZAWNNZXOXRDXSUHLZXFXBMLZYDXRXEYEXQXEXGUIXQXEYEOZXHXQWMW
      RWSXPYGWMWQWTXPUJZWRWSWMWQXPUKZWRWSWMWQXPULZXAXPUMZDEXDFUNUOPQXQXHBCDXDFY
      HWOWPWMWTXPUPWOWPWMWTXPUQYIYKXQXEXGURUSXQYEYFIYDOZXHXQWMWRXPWSWQYLYHYIYKY
      JWMWQWTXPVBDXDEBACFUTVAPRXRYCXNAWNXQXJWNHZXHYCXNOZXQYMIXAYMIZXPIZXHYNXAXP
      YMVMYPXHIYCYFXCXKMLZXSYAMLZJZXNYPYCYSSZXHYPWMWRXPWSWOWPYMYTWMWQWTYMXPVCZY
      OWRXPWRWSWMWQYMUKPZYOXPUMZYOWSXPWRWSWMWQYMULPZYOWOXPWOWPWMWTYMUPZPZYOWPXP
      WOWPWMWTYMUQZPZXAYMXPVDZDXDEBCXJFVEVFZPYPXHYSXNYPXHYSJZXLXMUUKXEYCXLYPXEX
      GYSVGUUKYCYSYPXHYSVHYPXHYTYSUUJTVIYPXHXEYCIXLOZYSYPWMWRXPWSWOWPYMUULUUAUU
      BUUCUUDUUFUUHUUIDXDEBCXJFVJVFTRUUKYQXMYPXHYFYQYRVKYPXHYQXMSZYSYPWMWRWSWOY
      MUUMUUAUUBUUDUUFUUIDEBXJFVNVOTVPVQVRVSVTWAWCQWBXAXNXIAWNYOXNIZBXJCKZKDEXD
      KZKUGLZGWNNZXIUUNBUUOUHLZXMUURUUNXLUUSYOXLXMUIUUNWMWOYMWPXLUUSOWMWQWTYMXN
      VCYOWOXNUUEPXAYMXNVDYOWPXNUUGPBXJCFWDUOQYOXLXMURYOUUSXMIUUROZXNYOWMWOYMWP
      WTUUTWMWQWTYMUJUUEXAYMUMZUUGWMWQWTYMWEBXJCDGEFUTVAPRUUNUUQXHGWNYOXPXNUUQX
      HOYPXNIUUQXMXGUUOUUPMLZJZXHYPUUQUVCSZXNYPWMWOYMWPJZWRWSXPUVDUUAYOUVEXPYOW
      OYMWPUUEUVAUUGWFPUUBUUDUUCBXJCDEXDFVEWGPYPXNUVCXHYPXNUVCJZXEXGUVFXLYBXTUG
      LZXEYPXLXMUVCVGUVFUVGXGXMYAXSMLZJZUVFXGXMUVHYPXNXMXGUVBVKZYPXLXMUVCWHUVFU
      VBUVHYPXNXMXGUVBWIYPXNUVBUVHSZUVCYPWMYMWPWSXPUVKUUAUUIUUHUUDUUCXJCEXDFWJV
      OTVPWFYPXNUVGUVISZUVCYPWMWOWPYMWRXPWSUVLUUAUUFUUHUUIUUBUUCUUDBCXJDXDEFVEV
      FTVIYPXNXLUVGIXEOZUVCYPWMWOWPYMWRXPWSUVMUUAUUFUUHUUIUUBUUCUUDBCXJDXDEFVJV
      FTRUVJVQVRVSWAWCQWBWLWK $.
  $}

  ${
    $d N y z $.  $d A y z $.  $d B y z $.  $d C y z $.  $d D y z $.
    $d E y z $.  $d F y z $.  $d G y z $.  $d H y z $.
    $( Substitution law for segment comparison under congruence.  Theorem 5.6
       of [Schwabhauser] p. 42.  (Contributed by Scott Fenton, 11-Oct-2013.) $)
    seglecgr12im $p |- (
       ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\
         ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) ->
       ( ( <. A , B >. Cgr <. E , F >. /\ <. C , D >. Cgr <. G , H >. /\
           <. A , B >. Seg<_ <. C , D >. ) ->
           <. E , F >. Seg<_ <. G , H >. ) ) $=
      ( vy vz wcel w3a cop ccgr wbr wi wa wrex adantr cn cee csegle cbtwn ccgr3
      cv simprrl simprlr simpl11 simpl21 simpr simpl22 simpl32 cgrxfr syl132anc
      cfv simpl33 mp2and anass wb simprl simprr brcgr3 syl133anc df-3an simpl23
      simpl31 simpl12 simpl13 simpr1l simpr2r cgrtr4and simpr31 cgrtrand sylbid
      sylan2br expr anim2d sylanb an32s reximdva rexlimdva simp11 simp12 simp13
      simp21 simp22 brsegle syl122anc simp23 simp31 simp32 simp33 3imtr4d exp32
      mpd 3impd ) IUALZAIUBUPZLZBWSLZMZCWSLZDWSLZEWSLZMZFWSLZGWSLZHWSLZMZMZABNZ
      EFNZOPZCDNZGHNZOPZXLXOUCPZXMXPUCPZXKXNXQXRXSQXKXNXQRZRZJUFZXOUDPZXLCYBNZO
      PZRZJWSSZKUFZXPUDPZXMGYHNZOPZRZKWSSZXRXSYAYFYMJWSXKYBWSLZXTYFYMQXKYNRZXTY
      FYMYOXTYFRZRZYICYBDNZNGYHHNZNUEPZRZKWSSZYMYQYCXQUUBYOXTYCYEUGYOXNXQYFUHYO
      YCXQRUUBQZYPYOWRXCYNXDXHXIUUCWRWTXAXFXJYNUIXCXDXEXBXJYNUJXKYNUKXCXDXEXBXJ
      YNULXGXHXIXBXFYNUMXGXHXIXBXFYNUQCYBDGKHIUNUOTURYQUUAYLKWSYOYHWSLZYPUUAYLQ
      ZYOUUDRXKYNUUDRZRZYPUUEXKYNUUDUSUUGYPRZYTYKYIUUHYTYDYJOPZXQYRYSOPZMZYKUUG
      YTUUKUTZYPUUGWRXCYNXDXHUUDXIUULWRWTXAXFXJUUFUIZXCXDXEXBXJUUFUJZXKYNUUDVAZ
      XCXDXEXBXJUUFULXGXHXIXBXFUUFUMZXKYNUUDVBZXGXHXIXBXFUUFUQCYBDGYHHIVCVDTUUG
      YPUUKYKYPUUKRUUGXTYFUUKMZYKXTYFUUKVEUUGUUREFCYBGYHIUUMXCXDXEXBXJUUFVFZXGX
      HXIXBXFUUFVGZUUNUUOUUPUUQUUGUURABEFCYBIUUMWRWTXAXFXJUUFVHWRWTXAXFXJUUFVIU
      USUUTUUNUUOXNXQYFUUKUUGVJYCYEXTUUKUUGVKVLUUIXQUUJXTYFUUGVMVNVPVQVOVRVSVTW
      AWPVQVTWBXKXRYGUTZXTXKWRWTXAXCXDUVAWRWTXAXFXJWCZWRWTXAXFXJWDWRWTXAXFXJWEX
      BXCXDXEXJWFXBXCXDXEXJWGJABCDIWHWITXKXSYMUTZXTXKWRXEXGXHXIUVCUVBXBXCXDXEXJ
      WJXBXFXGXHXIWKXBXFXGXHXIWLXBXFXGXHXIWMKEFGHIWHWITWNWOWQ $.
  $}

  $( Substitution law for segment comparison under congruence.  Biconditional
     version.  (Contributed by Scott Fenton, 15-Oct-2013.)  (Revised by Mario
     Carneiro, 19-Apr-2014.) $)
  seglecgr12 $p |- (
       ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
         ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\
         ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) ->
       ( ( <. A , B >. Cgr <. E , F >. /\ <. C , D >. Cgr <. G , H >. ) ->
           ( <. A , B >. Seg<_ <. C , D >. <->
             <. E , F >. Seg<_ <. G , H >. ) ) ) $=
    ( wcel w3a cop ccgr wbr wa csegle df-3an seglecgr12im biimtrrid expd cn cee
    cfv wi wb simp11 simp12 simp13 simp23 simp31 cgrcom syl122anc simp21 simp22
    simp32 simp33 anbi12d syl333anc sylbid impbidd ) IUAJZAIUBUCZJZBVBJZKZCVBJZ
    DVBJZEVBJZKZFVBJZGVBJZHVBJZKZKZABLZEFLZMNZCDLZGHLZMNZOZVOVRPNZVPVSPNZVNWAWB
    WCWAWBOVQVTWBKVNWCVQVTWBQABCDEFGHIRSTVNWAVPVOMNZVSVRMNZOZWCWBUDVNVQWDVTWEVN
    VAVCVDVHVJVQWDUEVAVCVDVIVMUFZVAVCVDVIVMUGZVAVCVDVIVMUHZVEVFVGVHVMUIZVEVIVJV
    KVLUJZABEFIUKULVNVAVFVGVKVLVTWEUEWGVEVFVGVHVMUMZVEVFVGVHVMUNZVEVIVJVKVLUOZV
    EVIVJVKVLUPZCDGHIUKULUQVNWFWCWBWFWCOWDWEWCKZVNWBWDWEWCQVNVAVHVJVKVLVCVDVFVG
    WPWBUDWGWJWKWNWOWHWIWLWMEFGHABCDIRURSTUSUT $.

  ${
    $d A y $.  $d B y $.  $d N y $.
    $( Segment comparison is reflexive.  Theorem 5.7 of [Schwabhauser] p. 42.
       (Contributed by Scott Fenton, 11-Oct-2013.) $)
    seglerflx $p |- ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ->
        <. A , B >. Seg<_ <. A , B >. ) $=
      ( vy cn wcel cee cfv w3a cop csegle cv cbtwn ccgr wa wrex simp3 btwntriv2
      wbr cgrrflx wceq breq1 opeq2 breq2d anbi12d rspcev syl12anc simp1 brsegle
      wb simp2 syl122anc mpbird ) CEFZACGHZFZBUOFZIZABJZUSKSZDLZUSMSZUSAVAJZNSZ
      OZDUOPZURUQBUSMSZUSUSNSZVFUNUPUQQZABCRABCTVEVGVHODBUOVABUAZVBVGVDVHVABUSM
      UBVJVCUSUSNVABAUCUDUEUFUGURUNUPUQUPUQUTVFUJUNUPUQUHUNUPUQUKZVIVKVIDABABCU
      IULUM $.
  $}

  ${
    $d N y $.  $d A y $.  $d B y $.  $d C y $.
    $( Any segment is at least as long as a degenerate segment.  Theorem 5.11
       of [Schwabhauser] p. 42.  (Contributed by Scott Fenton, 11-Oct-2013.) $)
    seglemin $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
       <. A , A >. Seg<_ <. B , C >. ) $=
      ( vy cn wcel cee cfv w3a wa cop csegle wbr cv cbtwn ccgr simpr2 btwntriv1
      wrex 3adant3r1 cgrtriv 3adant3r3 wceq breq1 opeq2 breq2d anbi12d syl12anc
      rspcev wb simpl simpr1 simpr3 brsegle syl122anc mpbird ) DFGZADHIZGZBUSGZ
      CUSGZJZKZAALZBCLZMNZEOZVFPNZVEBVHLZQNZKZEUSTZVDVABVFPNZVEBBLZQNZVMURUTVAV
      BRZURVAVBVNUTBCDSUAURUTVAVPVBABDUBUCVLVNVPKEBUSVHBUDZVIVNVKVPVHBVFPUEVRVJ
      VOVEQVHBBUFUGUHUJUIVDURUTUTVAVBVGVMUKURVCULURUTVAVBUMZVSVQURUTVAVBUNEAABC
      DUOUPUQ $.
  $}

  ${
    $d N y z w $.  $d A y z w $.  $d B y z w $.  $d C y z w $.  $d D y z w $.
    $d E y z w $.  $d F y z w $.
    $( Segment less than is transitive.  Theorem 5.8 of [Schwabhauser] p. 42.
       (Contributed by Scott Fenton, 11-Oct-2013.) $)
    segletr $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\
       ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ->
       ( ( <. A , B >. Seg<_ <. C , D >. /\ <. C , D >. Seg<_ <. E , F >. ) ->
         <. A , B >. Seg<_ <. E , F >. ) ) $=
      ( vy vz vw wcel w3a cv cop cbtwn wbr ccgr wa wrex wb cee cfv csegle ccgr3
      cn simprll simprrr wi simpl1 simpl23 simprl simpl31 simpl32 simprr cgrxfr
      jca syl132anc adantr mpd df-3an anbi2i bitr4i simpr1 simpr3 simpr2 brcgr3
      anass simpl33 simpr3l simpr2l btwnexchand simpl21 simpl22 simpr1r simp3r1
      syl133anc anbi2d adantl cgrtrand sylan2br sylbid an32s reximdva rexlimdvv
      expr sylanb exp31 simp1 simp21 simp22 simp23 simp31 brsegle simp32 simp33
      syl122anc anbi12d reeanv bitr4di 3imtr4d ) GUEKZAGUAUBZKZBXBKZCXBKZLZDXBK
      ZEXBKZFXBKZLZLZHMZCDNZOPZABNZCXLNZQPZRZIMZEFNZOPZXMEXSNZQPZRZRZIXBSHXBSZJ
      MZXTOPZXOEYGNZQPZRZJXBSZXOXMUCPZXMXTUCPZRZXOXTUCPZXKYEYLHIXBXBXKXLXBKZXSX
      BKZRZYEYLXKYSRZYERZYGYBOPZCXLDNZNEYGXSNZNUDPZRZJXBSZYLUUAXNYCRZUUGUUAXNYC
      YTXNXQYDUFYTXRYAYCUGUPYTUUHUUGUHZYEYTXAXEYQXGXHYRUUIXAXFXJYSUIXCXDXEXAXJY
      SUJXKYQYRUKXGXHXIXAXFYSULXGXHXIXAXFYSUMXKYQYRUNCXLDEJXSGUOUQURUSUUAUUFYKJ
      XBYTYGXBKZYEUUFYKUHZYTUUJRZXKYQYRUUJLZRZYEUUKUULXKYSUUJRZRUUNXKYSUUJVGUUM
      UUOXKYQYRUUJUTVAVBUUNYERUUFUUBXPYIQPZYCUUCUUDQPZLZRZYKUUNUUFUUSTYEUUNUUEU
      URUUBUUNXAXEYQXGXHUUJYRUUEUURTXAXFXJUUMUIZXCXDXEXAXJUUMUJZXKYQYRUUJVCZXGX
      HXIXAXFUUMULXGXHXIXAXFUUMUMZXKYQYRUUJVDZXKYQYRUUJVEZCXLDEYGXSGVFVPVQURUUN
      YEUUSYKYEUUSRUUNXRYDUUSLZYKXRYDUUSUTUUNUVFRYHYJUUNUVFEYGXSFGUUTUVCUVDUVEX
      GXHXIXAXFUUMVHUUBUURXRYDUUNVIYAYCXRUUSUUNVJVKUUNUVFABCXLEYGGUUTXCXDXEXAXJ
      UUMVLXCXDXEXAXJUUMVMUVAUVBUVCUVDXNXQYDUUSUUNVNUVFUUPUUNUUPYCUUQUUBXRYDVOV
      RVSUPVTWEWAWFWBWCUSWGWDXKYOXRHXBSZYDIXBSZRYFXKYMUVGYNUVHXKXAXCXDXEXGYMUVG
      TXAXFXJWHZXAXCXDXEXJWIZXAXCXDXEXJWJZXAXCXDXEXJWKZXAXFXGXHXIWLZHABCDGWMWPX
      KXAXEXGXHXIYNUVHTUVIUVLUVMXAXFXGXHXIWNZXAXFXGXHXIWOZICDEFGWMWPWQXRYDHIXBX
      BWRWSXKXAXCXDXHXIYPYLTUVIUVJUVKUVNUVOJABEFGWMWPWT $.
  $}

  ${
    $d N y t $.  $d A y t $.  $d B y t $.  $d C y t $.  $d D y t $.
    $( Antisymmetry law for segment comparison.  Theorem 5.9 of [Schwabhauser]
       p. 42.  (Contributed by Scott Fenton, 14-Oct-2013.) $)
    segleantisym $p |- ( ( N e. NN /\
        ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
        ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
        ( ( <. A , B >. Seg<_ <. C , D >. /\ <. C , D >. Seg<_ <. A , B >. ) ->
          <. A , B >. Cgr <. C , D >. ) ) $=
      ( vy vt wcel wa cop csegle wbr cv cbtwn ccgr wrex anbi12d simprll simprrl
      simprlr cn cee cfv w3a brsegle brsegle2 3com23 reeanv bitr4di weq simpl3l
      simpl1 simprr simprl simpl3r btwnexchand simpl2l simpl2r simprrr cgrtrand
      wb endofsegidand opeq2 breq2d breq1d anbi2d wceq btwncomand wi btwnswapid
      syl13anc adantr mp2and syl5ibrcom biimtrdi mpcom exp31 rexlimdvv sylbid
      mpd ) EUAHZAEUBUCZHZBWBHZIZCWBHZDWBHZIZUDZABJZCDJZKLZWKWJKLZIZFMZWKNLZWJC
      WOJZOLZIZDCGMZJZNLZXAWJOLZIZIZGWBPFWBPZWJWKOLZWIWNWSFWBPZXDGWBPZIXFWIWLXH
      WMXIFABCDEUEWAWHWEWMXIVAGCDABEUFUGQWSXDFGWBWBUHUIWIXEXGFGWBWBWIWOWBHZWTWB
      HZIZXEXGGFUJZWIXLIZXEIZXGXNXECWTWOEWAWEWHXLULZWFWGWAWEXLUKZWIXJXKUMZWIXJX
      KUNZXNXECWODWTEXPXQXSWFWGWAWEXLUOZXRXNWPWRXDRXNWSXBXCSUPXNXECWTABCWOEXPXQ
      XRWCWDWAWHXLUQWCWDWAWHXLURXQXSXNWSXBXCUSXNWPWRXDTUTVBXMXOXNWSDWQNLZWQWJOL
      ZIZIZIZXGXMXEYDXNXMXDYCWSXMXBYAXCYBXMXAWQDNWTWOCVCZVDXMXAWQWJOYFVEQVFVFYE
      DWOVGZXGYEDWOCJNLZWODCJNLZYGXNYDDCWOEXPXTXQXSXNWSYAYBSVHXNYDWOCDEXPXSXQXT
      XNWPWRYCRVHXNYHYIIYGVIZYDXNWAWGXJWFYJXPXTXSXQDWOCEVJVKVLVMYEXGYGWRXNWPWRY
      CTYGWKWQWJODWOCVCVDVNVTVOVPVQVRVS $.
  $}

  ${
    $d N x $.  $d A x $.  $d B x $.  $d C x $.  $d D x $.
    $( Linearity law for segment comparison.  Theorem 5.10 of [Schwabhauser]
       p. 42.  (Contributed by Scott Fenton, 14-Oct-2013.) $)
    seglelin $p |- ( ( N e. NN /\
     ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
     ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ->
     ( <. A , B >. Seg<_ <. C , D >. \/ <. C , D >. Seg<_ <. A , B >. ) ) $=
      ( vx cn wcel cee cfv wa w3a cop cbtwn wbr wo ccgr wrex csegle wb cv andir
      segcon2 simpl1 simpl2l simpr simpl3 cgrcom syl121anc anbi2d orbi2d bitrid
      rexbidva brsegle2 brsegle 3com23 orbi12d r19.43 bitr4di bitr4d mpbid ) EG
      HZAEIJZHZBVCHZKZCVCHDVCHKZLZBAFUAZMZNOZVIABMZNOZPVJCDMZQOZKZFVCRZVLVNSOZV
      NVLSOZPZFBCDAEUCVHVQVKVOKZVMVNVJQOZKZPZFVCRZVTVHVPWDFVCVPWAVMVOKZPVHVIVCH
      ZKZWDVKVMVOUBWHWFWCWAWHVOWBVMWHVBVDWGVGVOWBTVBVFVGWGUDVDVEVBVGWGUEVHWGUFV
      BVFVGWGUGAVICDEUHUIUJUKULUMVHVTWAFVCRZWCFVCRZPWEVHVRWIVSWJFABCDEUNVBVGVFV
      SWJTFCDABEUOUPUQWAWCFVCURUSUTVA $.
  $}

  ${
    $d N x $.  $d A x $.  $d B x $.  $d C x $.
    $( If ` B ` falls between ` A ` and ` C ` , then ` A B ` is no longer than
       ` A C ` .  (Contributed by Scott Fenton, 16-Oct-2013.)  (Revised by
       Mario Carneiro, 19-Apr-2014.) $)
    btwnsegle $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
       ( B Btwn <. A , C >. -> <. A , B >. Seg<_ <. A , C >. ) ) $=
      ( vx cn wcel cee cfv w3a wa cop cbtwn wbr csegle ccgr wrex simplr2 adantr
      cv simpr simpl simpr1 simpr2 cgrrflxd breq1 opeq2 breq2d anbi12d syl12anc
      wceq rspcev wb simpr3 brsegle syl122anc mpbird ex ) DFGZADHIZGZBUTGZCUTGZ
      JZKZBACLZMNZABLZVFONZVEVGKZVIETZVFMNZVHAVKLZPNZKZEUTQZVJVBVGVHVHPNZVPVAVB
      VCUSVGRVEVGUAVEVQVGVEABDUSVDUBZUSVAVBVCUCZUSVAVBVCUDZUESVOVGVQKEBUTVKBUKZ
      VLVGVNVQVKBVFMUFWAVMVHVHPVKBAUGUHUIULUJVEVIVPUMZVGVEUSVAVBVAVCWBVRVSVTVSU
      SVAVBVCUNEABACDUOUPSUQUR $.
  $}

  $( Given three colinear points ` A ` , ` B ` , and ` C ` , ` B ` falls in the
     middle iff the two segments to ` B ` are no longer than ` A C ` .  Theorem
     5.12 of [Schwabhauser] p. 42.  (Contributed by Scott Fenton, 15-Oct-2013.)
     (Revised by Mario Carneiro, 19-Apr-2014.) $)
  colinbtwnle $p |- ( ( N e. NN /\
      ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
      ( A Colinear <. B , C >. ->
        ( B Btwn <. A , C >. <->
          ( <. A , B >. Seg<_ <. A , C >. /\
            <. B , C >. Seg<_ <. A , C >. ) ) ) ) $=
    ( wcel w3a wa cop wbr cbtwn csegle btwnsegle sylan2b ccgr mp2and adantr imp
    wb wi ex cn cee ccolin 3anrev 3ancoma btwncom simpl simpr2 simpr3 cgrrflx2d
    cfv simpr1 seglecgr12 syl333anc 3imtr4d jcad w3o brcolinear wceq btwncomand
    simprl biimpa adantrl 3anrot sylan2br sylbid adantrr segleantisym syl122anc
    endofsegidand btwntriv1 3adant3r2 breq1 syl5ibrcom mpd expr adantld biimprd
    a1dd simprr 3ancomb btwntriv2 adantrd 3jaod impbid ) DUAEZADUBUKZEZBWGEZCWG
    EZFZGZABCHZUCIZBACHZJIZABHZWOKIZWMWOKIZGZRWLWNGWPWTWLWPWTSWNWLWPWRWSABCDLWL
    BCAHZJIZCBHZXAKIZWPWSWKWFWJWIWHFXBXDSWHWIWJUDCBADLMWKWFWIWHWJFWPXBRWHWIWJUE
    BACDUFMZWLWMXCNIZWOXANIZWSXDRZWLBCDWFWKUGZWFWHWIWJUHZWFWHWIWJUIZUJWLACDXIWF
    WHWIWJULZXKUJWLWFWIWJWHWJWJWIWJWHXFXGGXHSXIXJXKXLXKXKXJXKXLBCACCBCADUMUNOZU
    OUPPWLWNWTWPSZWLWNAWMJIZXBCWQJIZUQXNABCDURWLXOXNXBXPWLXOXNWLXOGWSWPWRWLXOWS
    WPWLXOWSGZGZBAUSZWPWLXQCBADXIXKXJXLWLXQABCDXIXLXJXKWLXOWSVAUTXRXDXAXCKIZXCX
    ANIZWLWSXDXOWLWSXDXMVBVCWLXOXTWSWLXOXTWLXOAXCJIZXTABCDUFWKWFWJWHWIFYBXTSWJW
    HWIVDCABDLVEVFQVGWLXDXTGYASZXQWLWFWJWIWJWHYCXIXKXJXKXLCBCADVHVIPOVJWLXSWPSX
    QWLWPXSAWOJIZWFWHWJYDWIACDVKVLBAWOJVMVNPVOVPVQTWLXBWPWTWLWPXBXEVRVSWLXPXNWL
    XPGWRWPWSWLXPWRWPWLXPWRGZGZBCUSZWPWLYEABCDXIXLXJXKWLXPWRVAYFWRWOWQKIZWQWONI
    ZWLXPWRVTWLXPYHWRWLXPYHWKWFWHWJWIFXPYHSWHWIWJWAACBDLMQVGWLWRYHGYISZYEWLWFWH
    WIWHWJYJXIXLXJXLXKABACDVHVIPOVJWLYGWPSYEWLWPYGCWOJIZWFWHWJYKWIACDWBVLBCWOJV
    MVNPVOVPWCTWDVFQWET $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Outside-of relationship
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c OutsideOf $.

  $( Declare the syntax for the outside of constant. $)
  coutsideof $a class OutsideOf $.

  $( The outside of relationship.  This relationship expresses that ` P ` ,
     ` A ` , and ` B ` fall on a line, but ` P ` is not on the segment
     ` A B ` .  This definition is taken from theorem 6.4 of [Schwabhauser]
     p. 43, since it requires no dummy variables.  (Contributed by Scott
     Fenton, 17-Oct-2013.) $)
  df-outsideof $a |- OutsideOf = ( Colinear \ Btwn ) $.

  $( Binary relation form of ` OutsideOf ` .  Theorem 6.4 of [Schwabhauser]
     p. 43.  (Contributed by Scott Fenton, 17-Oct-2013.)  (Revised by Mario
     Carneiro, 19-Apr-2014.) $)
  broutsideof $p |- ( P OutsideOf <. A , B >. <->
    ( P Colinear <. A , B >. /\ -. P Btwn <. A , B >. ) ) $=
    ( cop coutsideof wbr ccolin cbtwn cdif wn wa df-outsideof breqi brdif bitri
    ) CABDZEFCPGHIZFCPGFCPHFJKCPEQLMCPGHNO $.

  $( Alternate form of ` OutsideOf ` .  Definition 6.1 of [Schwabhauser] p. 43.
     (Contributed by Scott Fenton, 17-Oct-2013.)  (Revised by Mario Carneiro,
     19-Apr-2014.) $)
  broutsideof2 $p |- ( ( N e. NN /\
    ( P e. ( EE ` N ) /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ) ->
    ( P OutsideOf <. A , B >. <->
      ( A =/= P /\ B =/= P /\
        ( A Btwn <. P , B >. \/ B Btwn <. P , A >. ) ) ) ) $=
    ( cop wbr cbtwn wa wcel w3a wne wceq 3adant3r1 breq1 syl5ibcom necon3bd imp
    adantrl wi a1i coutsideof ccolin wn cee cfv broutsideof btwntriv1 btwntriv2
    cn wo w3o brcolinear pm2.24 wb 3anrot btwncom sylan2b orc biimtrdi a1dd olc
    3jaod sylbid imp32 3jca simp3 3ancomb btwncolinear2 btwncolinear1 jaod syl5
    simpr2 neneqd simprl1 simprr simpl simpr1 simpr3 btwnswapid syl13anc adantr
    a1d mp2and expr mtod 3exp2 btwncomand sylan2br com12 com4l 3imp2 jca bitrid
    impbida ) CABEZUAFCWOUBFZCWOGFZUCZHZDUIIZCDUDUEZIZAXAIZBXAIZJZHZACKZBCKZACB
    EGFZBCAEGFZUJZJZABCUFXFWSXLXFWSHXGXHXKXFWRXGWPXFWRXGXFWQACXFAWOGFZACLZWQWTX
    CXDXMXBABDUGMACWOGNOPQRXFWRXHWPXFWRXHXFWQBCXFBWOGFZBCLZWQWTXCXDXOXBABDUHMBC
    WOGNOPQRXFWPWRXKXFWPWQABCEGFZXJUKWRXKSZCABDULXFWQXRXQXJWQXRSXFWQXKUMTXFXQXK
    WRXFXQXIXKXEWTXCXDXBJXQXIUNXBXCXDUOABCDUPUQXIXJURUSUTXJXRSXFXJXKWRXJXIVAWBT
    VBVCVDVEXFXLHWPWRXFXLWPXLXKXFWPXGXHXKVFXFXIWPXJXEWTXBXDXCJXIWPSXBXCXDVGCBAD
    VHUQCABDVIVJVKQXFXGXHXKWRXKXFXGXHWRXFXKXGXHWRSSZXFXIXSXJXFXIXGXHWRXFXIXGXHJ
    ZHZWQXNYAACXFXIXGXHVLVMXFXTWQXNXFXTWQHZHXIWQXNXIXGXHWQXFVNXFXTWQVOXFXIWQHXN
    SZYBXFWTXCXBXDYCWTXEVPZWTXBXCXDVLZWTXBXCXDVQZWTXBXCXDVRZACBDVSVTWAWCWDWEWFX
    FXJXGXHWRXFXJXGXHJZHZWQXPYIBCXFXJXGXHVRVMXFYHWQXPXFYHWQHZHXJCBAEGFZXPXJXGXH
    WQXFVNXFYJCABDYDYFYEYGXFYHWQVOWGXFXJYKHXPSZYJXEWTXDXBXCJYLXDXBXCUOBCADVSWHW
    AWCWDWEWFVJWIWJWKWLWNWM $.

  $( Outsideness implies inequality.  (Contributed by Scott Fenton,
     18-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
  outsidene1 $p |- ( ( N e. NN /\
   ( P e. ( EE ` N ) /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ) ->
   ( P OutsideOf <. A , B >. -> A =/= P ) ) $=
    ( cn wcel cee cfv w3a wa cop coutsideof wbr wne cbtwn wo broutsideof2 simp1
    biimtrdi ) DEFCDGHZFATFBTFIJCABKLMACNZBCNZACBKOMBCAKOMPZIUAABCDQUAUBUCRS $.

  $( Outsideness implies inequality.  (Contributed by Scott Fenton,
     18-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
  outsidene2 $p |- ( ( N e. NN /\
   ( P e. ( EE ` N ) /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ) ->
   ( P OutsideOf <. A , B >. -> B =/= P ) ) $=
    ( cn wcel cee cfv w3a wa cop coutsideof wbr wne cbtwn wo broutsideof2 simp2
    biimtrdi ) DEFCDGHZFATFBTFIJCABKLMACNZBCNZACBKOMBCAKOMPZIUBABCDQUAUBUCRS $.

  $( A principle linking outsideness to betweenness.  Theorem 6.2 of
     [Schwabhauser] p. 43.  (Contributed by Scott Fenton, 18-Oct-2013.)
     (Revised by Mario Carneiro, 19-Apr-2014.) $)
  btwnoutside $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
    ( C e. ( EE ` N ) /\ P e. ( EE ` N ) ) ) ->
    ( ( ( A =/= P /\ B =/= P /\ C =/= P ) /\ P Btwn <. A , C >. ) ->
      ( P Btwn <. B , C >. <-> P OutsideOf <. A , B >. ) ) ) $=
    ( wcel wa w3a wne cop cbtwn wbr wb df-3an simpr2 btwncomand simpr3 sylan2br
    adantr expr cee cfv coutsideof simpr11 simpr12 simpr13 simp3r simp2l simp3l
    cn wo simp1 simp2r wi btwnconn2 3com23 mp3and simp3 btwnouttr2 btwnexch3and
    3jca syl122anc jaod syl5 impbid broutsideof2 syl13anc bitr4d ex ) EUJFZAEUA
    UBZFZBVKFZGZCVKFZDVKFZGZHZADIZBDIZCDIZHZDACJKLZGZDBCJKLZDABJUCLZMVRWDGZWEVS
    VTADBJKLZBDAJKLZUKZHZWFWGWEWKVRWDWEWKWDWEGVRWBWCWEHZWKWBWCWENVRWLGZVSVTWJVS
    VTWAWCWEVRUDVSVTWAWCWEVRUEWMWADCAJKLZDCBJKLZWJVSVTWAWCWEVRUFVRWLDACEVJVNVQU
    LZVJVNVOVPUGZVJVLVMVQUHZVJVNVOVPUIZVRWBWCWEOPVRWLDBCEWPWQVJVLVMVQUMZWSVRWBW
    CWEQPVRWAWNWOHWJUNZWLVJVQVNXACDABEUOUPSUQVARTWKWJWGWEVSVTWJURWGWHWEWIVRWDWH
    WEWDWHGVRWBWCWHHZWEWBWCWHNVRXBGVSABDJKLZWCWEVSVTWAWCWHVRUDVRXBADBEWPWRWQWTV
    RWBWCWHQPVRWBWCWHOVRVSXCWCHWEUNZXBVRVJVMVLVPVOXDWPWTWRWQWSBADCEUSVBSUQRTVRW
    DWIWEWDWIGVRWBWCWIHZWEWBWCWINVRXEABDCEWPWRWTWQWSVRXEBDAEWPWTWQWRVRWBWCWIQPV
    RWBWCWIOUTRTVCVDVEVRWFWKMZWDVRVJVPVLVMXFWPWQWRWTABDEVFVGSVHVI $.

  ${
    $d N c $.  $d A c $.  $d B c $.  $d P c $.
    $( Characterization of outsideness in terms of relationship to a fourth
       point.  Theorem 6.3 of [Schwabhauser] p. 43.  (Contributed by Scott
       Fenton, 18-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    broutsideof3 $p |- ( ( N e. NN /\
       ( P e. ( EE ` N ) /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ) ->
       ( P OutsideOf <. A , B >. <->
         ( A =/= P /\ B =/= P /\
           E. c e. ( EE ` N ) ( c =/= P /\ P Btwn <. A , c >. /\
                                P Btwn <. B , c >. ) ) ) ) $=
      ( wcel w3a wa cop wbr wne cbtwn simpr3 adantr wi df-3an btwncomand simpr2
      wrex expr cn cee cfv coutsideof wo cv broutsideof2 simpl btwndiff syl3anc
      simpr1 3anass necomd simp1 simp23 simp22 simp21 simpr1r btwnexch3and 3jca
      simp3 syl2anbr an32s reximdva jaod simprr1 simpll simplr1 simplr2 simprr2
      simpr simplr3 simprr3 btwnconn2 syl122anc mp3and rexlimdva impbid 3bitr4g
      mpd pm5.32da bitrd ) DUAFZCDUBUCZFZAWDFZBWDFZGZHZCABIUDJACKZBCKZACBILJZBC
      AILJZUEZGZWJWKEUFZCKZCAWPILJZCBWPILJZGZEWDSZGZABCDUGWIWJWKHZWNHXCXAHWOXBW
      IXCWNXAWIXCHZWNXAXDWLXAWMWIXCWLXAWIXCWLHZHZWSCWPKZHZEWDSZXAWIXIXEWIWCWGWE
      XIWCWHUHZWCWEWFWGMWCWEWFWGUKZBCDEUIUJNXFXHWTEWDWIWPWDFZXEXHWTOWIXLHZXEXHW
      TXMWCWHXLGZXEWSXGGZWTXEXHHWCWHXLPZXEWSXGULXNXOHZWQWRWSXQCWPXNXEWSXGMUMXNX
      OBACWPDWCWHXLUNZWCWEWFWGXLUOZWCWEWFWGXLUPZWCWEWFWGXLUQZWCWHXLVAZXNXOACBDX
      RXTYAXSXCWLWSXGXNURQXNXEWSXGRZUSYCUTVBTVCVDVTTWIXCWMXAWIXCWMHZHZWRXGHZEWD
      SZXAWIYGYDWIWCWFWEYGXJWCWEWFWGRXKACDEUIUJNYEYFWTEWDWIXLYDYFWTOXMYDYFWTXMX
      NYDWRXGGZWTYDYFHXPYDWRXGULXNYHHZWQWRWSYICWPXNYDWRXGMUMXNYDWRXGRZXNYHABCWP
      DXRXTXSYAYBXNYHBCADXRXSYAXTXCWMWRXGXNURQYJUSUTVBTVCVDVTTVEXDWTWNEWDWIXLXC
      WTWNOXMXCWTWNXMXCWTHZHWQCWPAILJZCWPBILJZWNWQWRWSXCXMVFXMYKCAWPDWCWHXLVGZW
      EWFWGWCXLVHZWEWFWGWCXLVIZWIXLVKZWQWRWSXCXMVJQXMYKCBWPDYNYOWEWFWGWCXLVLZYQ
      WQWRWSXCXMVMQXMWQYLYMGWNOZYKXMWCXLWEWFWGYSYNYQYOYPYRWPCABDVNVONVPTVCVQVRW
      AWJWKWNPWJWKXAPVSWB $.
  $}

  $( Reflexivity of outsideness.  Theorem 6.5 of [Schwabhauser] p. 44.
     (Contributed by Scott Fenton, 18-Oct-2013.)  (Revised by Mario Carneiro,
     19-Apr-2014.) $)
  outsideofrflx $p |- ( ( N e. NN /\ P e. ( EE ` N ) /\ A e. ( EE ` N ) ) ->
    ( A =/= P -> P OutsideOf <. A , A >. ) ) $=
    ( cn wcel cee cfv w3a wne cop ccolin wbr cbtwn wn coutsideof axbtwnid eqcom
    wa wceq imbitrdi necon3ad colineartriv2 jctild broutsideof imbitrrdi ) CDEB
    CFGZEAUFEHZABIZBAAJZKLZBUIMLZNZRBUIOLUGUHULUJUGUKABUGUKBASABSBACPBAQTUABACU
    BUCAABUDUE $.

  $( Commutativity law for outsideness.  Theorem 6.6 of [Schwabhauser] p. 44.
     (Contributed by Scott Fenton, 18-Oct-2013.)  (Revised by Mario Carneiro,
     19-Apr-2014.) $)
  outsideofcom $p |- ( ( N e. NN /\
    ( P e. ( EE ` N ) /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ) ->
    ( P OutsideOf <. A , B >. <-> P OutsideOf <. B , A >. ) ) $=
    ( cn cee cfv w3a wa wne cop cbtwn wbr wo coutsideof wb 3ancoma broutsideof2
    wcel orcom 3anbi3i bitri a1i 3ancomb sylan2b 3bitr4d ) DESZCDFGZSZAUHSZBUHS
    ZHZIZACJZBCJZACBKLMZBCAKLMZNZHZUOUNUQUPNZHZCABKOMCBAKOMZUSVAPUMUSUOUNURHVAU
    NUOURQURUTUOUNUPUQTUAUBUCABCDRULUGUIUKUJHVBVAPUIUJUKUDBACDRUEUF $.

  $( Transitivity law for outsideness.  Theorem 6.7 of [Schwabhauser] p. 44.
     (Contributed by Scott Fenton, 18-Oct-2013.)  (Revised by Mario Carneiro,
     19-Apr-2014.) $)
  outsideoftr $p |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) )
          /\
    ( C e. ( EE ` N ) /\ P e. ( EE ` N ) ) ) ->
    ( ( P OutsideOf <. A , B >. /\ P OutsideOf <. B , C >. ) ->
      P OutsideOf <. A , C >. ) ) $=
    ( wcel wa w3a wne cop cbtwn wbr wo coutsideof wi simprr df-3an expr jaod wb
    cn cee simpll simplr 3jca simplr1 simplr3 simp1 simp3r simp2l simp2r simp3l
    cfv simpr2 simpr3 btwnexchand orcd sylan2br simprlr btwnconn3 adantr mp2and
    syl122anc simpll2 adantl necomd btwnconn1 mp3and olcd imp32 exp31 syl5 impd
    broutsideof2 syl13anc anbi12d anbi12i an4 bitr4i bitrdi 3imtr4d ) EUAFZAEUB
    UMZFZBWCFZGZCWCFZDWCFZGZHZADIZBDIZGZWLCDIZGZGZADBJZKLZBDAJZKLZMZBDCJZKLZCWQ
    KLZMZGZGZWKWNAXBKLZCWSKLZMZHZDABJNLZDBCJNLZGZDACJNLZWJWPXFXKWPWKWLWNHZWJXFX
    KOWPWKWLWNWKWLWOUCWKWLWOUDWMWLWNPUEWJXPXFXKWJXPGZXFGWKWNXJWKWLWNWJXFUFWKWLW
    NWJXFUGXQXAXEXJXQWRXEXJOZWTWJXPWRXRWJXPWRGZGXCXJXDWJXSXCXJXSXCGWJXPWRXCHZXJ
    XPWRXCQWJXTGXHXIWJXTDABCEWBWFWIUHZWBWFWGWHUIZWBWDWEWIUJZWBWDWEWIUKZWBWFWGWH
    ULZWJXPWRXCUNWJXPWRXCUOUPUQURRWJXSXDXJWJXSXDGZGWRXDXJWJXPWRXDUSWJXSXDPWJWRX
    DGXJOZYFWJWBWHWDWGWEYGYAYBYCYEYDDACBEUTVCVAVBRSRWJXPWTXRWJXPWTGZGXCXJXDWJYH
    XCXJWJYHXCGZGZDBIZWTXCXJYJBDYIWLWJWKWLWNWTXCVDVEVFWJXPWTXCUSWJYHXCPWJYKWTXC
    HXJOZYIWJWBWHWEWDWGYLYAYBYDYCYEDBACEVGVCVAVHRWJYHXDXJYHXDGWJXPWTXDHZXJXPWTX
    DQWJYMGXIXHWJYMDCBAEYAYBYEYDYCWJXPWTXDUOWJXPWTXDUNUPVIURRSRSVJUEVKVLVMWJXNW
    KWLXAHZWLWNXEHZGZXGWJXLYNXMYOWJWBWHWDWEXLYNTYAYBYCYDABDEVNVOWJWBWHWEWGXMYOT
    YAYBYDYEBCDEVNVOVPYPWMXAGZWOXEGZGXGYNYQYOYRWKWLXAQWLWNXEQVQWMWOXAXEVRVSVTWJ
    WBWHWDWGXOXKTYAYBYCYEACDEVNVOWA $.

  $( Uniqueness law for ` OutsideOf ` .  Analogue of ~ segconeq .  (Contributed
     by Scott Fenton, 24-Oct-2013.)  (Revised by Mario Carneiro,
     19-Apr-2014.) $)
  outsideofeq $p |- ( ( N e. NN /\
    ( A e. ( EE ` N ) /\ R e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\
    ( C e. ( EE ` N ) /\ X e. ( EE ` N ) /\ Y e. ( EE ` N ) ) ) ->
    ( ( ( A OutsideOf <. X , R >. /\ <. A , X >. Cgr <. B , C >. ) /\
        ( A OutsideOf <. Y , R >. /\ <. A , Y >. Cgr <. B , C >. ) ) ->
      X = Y ) ) $=
    ( wcel w3a cop wbr wa wne cbtwn simprlr simprrr simprll exp32 endofsegidand
    adantl cn cee cfv coutsideof ccgr wo wceq simp21 simp32 simp22 broutsideof2
    wb syl13anc anbi1d simp33 anbi12d simpll3 simprl3 jca simpll2 simp23 simp31
    simp1 cgrtr3and wi midofsegid syl122anc adantr mp3and btwnexchand cgrcomand
    jca32 eqcomd simprr simplrr simprrl necomd btwnconn1 mpjaod ccased imp32 ex
    expr syldan sylbid ) EUAHZAEUBUCZHZDWGHZBWGHZIZCWGHZFWGHZGWGHZIZIZAFDJUDKZA
    FJZBCJZUEKZLZAGDJUDKZAGJZWSUEKZLZLFAMZDAMZFADJZNKZDWRNKZUFZIZWTLZGAMZXGGXHN
    KZDXCNKZUFZIZXDLZLZFGUGZWPXAXMXEXSWPWQXLWTWPWFWHWMWIWQXLULWFWKWOVCZWFWHWIWJ
    WOUHZWFWKWLWMWNUIZWFWHWIWJWOUJZFDAEUKUMUNWPXBXRXDWPWFWHWNWIXBXRULYBYCWFWKWL
    WMWNUOZYEGDAEUKUMUNUPWPXTYAWPXTXKXQLZXGWRXCUEKZLZLYAWPXTLYGXGYHXTYGWPXTXKXQ
    XFXGXKWTXSUQXNXGXQXDXMURUSTXTXGWPXFXGXKWTXSUTTWPXTAFAGBCEYBYCYDYCYFWFWHWIWJ
    WOVAWFWKWLWMWNVBWPXLWTXSOWPXMXRXDPVDVLWPYGYIYAWPXIXOXJXPYIYAVEWPXIXOLZYIYAW
    PYJYILZLXIXOYHYAWPXIXOYIQWPXIXOYIOWPYJXGYHPWPXIXOYHIYAVEZYKWPWFWHWIWMWNYLYB
    YCYEYDYFADFGEVFVGVHVIRWPXJXOLZYIYAWPYMYILZAFGEYBYCYDYFWPYNAGDFEYBYCYFYEYDWP
    XJXOYIOWPXJXOYIQVJWPYMXGYHPSRWPXIXPLZYIYAWPYOYILZLGFWPYPAGFEYBYCYFYDWPYPAFD
    GEYBYCYDYEYFWPXIXPYIQWPXIXPYIOVJWPYPAFAGEYBYCYDYCYFWPYOXGYHPVKSVMRWPXJXPLZY
    IYAWPYQYILZLZFXCNKZYAGWRNKZWPYRYTYAWPYRYTLZLGFWPUUBAGFEYBYCYFYDWPYRYTVNWPUU
    BAFAGEYBYCYDYCYFUUBYHWPYQXGYHYTVOTVKSVMWCWPYRUUAYAWPYRUUALZAFGEYBYCYDYFWPYR
    UUAVNUUCYHWPYQXGYHUUAVOTSWCYSADMZXJXPYTUUAUFZYSDAWPYQXGYHVPVQWPXJXPYIQWPXJX
    PYIOWPUUDXJXPIUUEVEZYRWPWFWHWIWMWNUUFYBYCYEYDYFADFGEVRVGVHVIVSRVTWAWDWBWE
    $.

  ${
    $d A x $.  $d A y $.  $d B x $.  $d B y $.  $d C x $.  $d C y $.  $d N x $.
    $d N y $.  $d R x $.  $d R y $.  $d x y $.
    $( Given a nondegenerate ray, there is a unique point congruent to the
       segment ` B C ` lying on the ray ` A R ` .  Theorem 6.11 of
       [Schwabhauser] p. 44.  (Contributed by Scott Fenton, 23-Oct-2013.)
       (Revised by Mario Carneiro, 19-Apr-2014.) $)
    outsideofeu $p |- ( ( N e. NN /\
      ( A e. ( EE ` N ) /\ R e. ( EE ` N ) ) /\
      ( B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) ->
      ( ( R =/= A /\ B =/= C ) ->
        E! x e. ( EE ` N ) ( A OutsideOf <. x , R >. /\
         <. A , x >. Cgr <. B , C >. ) ) ) $=
      ( vy wcel wa w3a wne cv cop coutsideof wbr ccgr wrex adantr wb 3jca cn wi
      cee cfv wreu weq wral cbtwn wo segcon2 simpl2l simpr simpl2r broutsideof2
      simpl1 syl13anc simpllr adantl wceq simprlr simp2l anim1i simpl3 cgrdegen
      simp3 syl3anc mpd necon3bid mpbird necomd simplll simprr expr bitrd orcom
      impbid2 bitrdi pm5.32rd an32s rexbidva simpl3l simpl3r simprl outsideofeq
      imp syl2an an4s exp32 ralrimivv opeq1 breq2d breq1d anbi12d reu4 sylanbrc
      opeq2 ex ) FUAHZBFUCUDZHZEWSHZIZCWSHZDWSHZIZJZEBKZCDKZIZBALZEMZNOZBXJMZCD
      MZPOZIZAWSUEZXFXIIZXPAWSQZXPBGLZEMZNOZBXTMZXNPOZIZIZAGUFZUBZGWSUGAWSUGXQX
      RXSEXMUHOZXJBEMUHOZUIZXOIZAWSQZXFYMXIAECDBFUJRXRXPYLAWSXFXJWSHZXIXPYLSXFY
      NIZXIIXOXLYKYOXIXOXLYKSYOXIXOIZIZXLYJYIUIZYKYQXLXJBKZXGYRJZYRYOXLYTSZYPYO
      WRWTYNXAUUAWRXBXEYNUOZWTXAWRXEYNUKXFYNULWTXAWRXEYNUMXJEBFUNUPRYQYTYRYSXGY
      RVEYOYPYRYTYOYPYRIZIZYSXGYRUUDBXJUUDBXJKXHUUCXHYOXGXHXOYRUQURUUDBXJCDUUDX
      OBXJUSCDUSSZYOXIXOYRUTYOXOUUEUBZUUCYOWRWTYNIXEUUFUUBXFWTYNWRWTXAXEVAVBWRX
      BXEYNVCBXJCDFVDVFRVGVHVIVJUUCXGYOXGXHXOYRVKURYOYPYRVLTVMVPVNYJYIVOVQVMVRV
      SVTVIXRYHAGWSWSXRYNXTWSHZIZYFYGXFUUHXIYFYGXFUUHIZWRWTXAXCJZXDYNUUGJZJZYFY
      GXIYFIUUIWRUUJUUKWRXBXEUUHUOUUIWTXAXCWTXAWRXEUUHUKWTXAWRXEUUHUMXCXDWRXBUU
      HWATUUIXDYNUUGXCXDWRXBUUHWBXFYNUUGWCXFYNUUGVLTTXIYFULUULYFYGBCDEFXJXTWDWE
      WFWGWHWIXPYEAGWSYGXLYBXOYDYGXKYABNXJXTEWJWKYGXMYCXNPXJXTBWPWLWMWNWOWQ $.
  $}

  ${
    $d A y $.  $d B y $.  $d P y $.  $d N y $.
    $( Relate ` OutsideOf ` to ` Seg<_ ` .  Theorem 6.13 of [Schwabhauser]
       p. 45.  (Contributed by Scott Fenton, 24-Oct-2013.)  (Revised by Mario
       Carneiro, 19-Apr-2014.) $)
    outsidele $p |- ( ( N e. NN /\
    ( P e. ( EE ` N ) /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ) ->
    ( P OutsideOf <. A , B >. ->
      ( <. P , A >. Seg<_ <. P , B >. <-> A Btwn <. P , B >. ) ) ) $=
      ( vy wcel w3a wa cop coutsideof cbtwn wb ccgr simpr3 adantr wceq ad2antrr
      wbr wi mpd cn cee cfv csegle cv wrex simpl simpr1 simpr2 syl122anc simprl
      brsegle2 outsideofcom mpbid simpll simplr1 simplr3 cgrrflxd jca ccolin wn
      simprrl simpr simplr2 btwncolinear1 syl13anc wne outsidene1 neneqd df-3an
      simpr2l btwncomand btwnswapid2 mp2and sylan2br expr mtod sylanbrc simprrr
      broutsideof outsideofeq syl133anc opeq2 breq2d syl5ibrcom an4s rexlimdvaa
      sylbid btwnsegle impbid ex ) DUAFZCDUBUCZFZAWMFZBWMFZGZHZCABIJRZCAICBIZUD
      RZAWTKRZLWRWSHZXAXBXCXAACEUEZIZKRZXEWTMRZHZEWMUFZXBWRXAXILZWSWRWLWNWOWNWP
      XJWLWQUGWLWNWOWPUHZWLWNWOWPUIXKWLWNWOWPNECACBDULUJOXCXHXBEWMWRXDWMFZWSXHX
      BWRXLHZWSXHHZHZBXDPZXBXOCBAIJRZWTWTMRZHZCXDAIZJRZXGHZXPXOXQXRXOWSXQXMWSXH
      UKZWRWSXQLXLXNABCDUMQUNXMXRXNXMCBDWLWQXLUOZWNWOWPWLXLUPZWNWOWPWLXLUQZUROU
      SXOYAXGXOCXTUTRZCXTKRZVAYAXOXFYGXMWSXFXGVBZXMXFYGSZXNXMWLWNXLWOYJYDYEWRXL
      VCZWNWOWPWLXLVDZCXDADVEVFOTXOYHACPZXOACXOWSACVGZYCWRWSYNSXLXNABCDVHQTVIXM
      XNYHYMXNYHHXMWSXHYHGZYMWSXHYHVJXMYOHAXDCIKRZYHYMXMYOACXDDYDYLYEYKXFXGWSYH
      XMVKVLXMWSXHYHNXMYPYHHYMSZYOXMWLWOXLWNYQYDYLYKYEAXDCDVMVFOVNVOVPVQXDACVTV
      RXMWSXFXGVSUSXMXSYBHXPSZXNXMWLWNWOWNWPWPXLYRYDYEYLYEYFYFYKCCBADBXDWAWBOVN
      XOXBXPXFYIXPWTXEAKBXDCWCWDWETWFWGWHWRXBXASWSCABDWIOWJWK $.
  $}

  $( Outside of implies colinearity.  (Contributed by Scott Fenton,
     26-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
  outsideofcol $p |- ( P OutsideOf <. Q , R >. -> P Colinear <. Q , R >. ) $=
    ( cop coutsideof wbr ccolin cbtwn wn broutsideof simplbi ) ABCDZEFALGFALHFI
    BCAJK $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Lines and Rays
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c Line LinesEE Ray $.

  $( Declare the constant for the line function. $)
  cline2 $a class Line $.

  $( Declare the constant for the ray function. $)
  cray $a class Ray $.

  $( Declare the constant for the set of all lines. $)
  clines2 $a class LinesEE $.

  ${
    $d a b l n $.
    $( Define the ` Line ` function.  This function generates the line passing
       through the distinct points ` a ` and ` b ` .  Adapted from definition
       6.14 of [Schwabhauser] p. 45.  (Contributed by Scott Fenton,
       25-Oct-2013.) $)
    df-line2 $a |- Line = { <. <. a , b >. , l >. |
       E. n e. NN ( ( a e. ( EE ` n ) /\ b e. ( EE ` n ) /\ a =/= b ) /\
         l = [ <. a , b >. ] `' Colinear ) } $.
  $}

  ${
    $d p a r n x $.
    $( Define the ` Ray ` function.  This function generates the set of all
       points that lie on the ray starting at ` p ` and passing through ` a ` .
       Definition 6.8 of [Schwabhauser] p. 44.  (Contributed by Scott Fenton,
       21-Oct-2013.) $)
    df-ray $a |- Ray = { <. <. p , a >. , r >. |
       E. n e. NN ( ( p e. ( EE ` n ) /\ a e. ( EE ` n ) /\ p =/= a ) /\
         r = { x e. ( EE ` n ) | p OutsideOf <. a , x >. } ) } $.
  $}

  $( Define the set of all lines.  Definition 6.14, part 2 of [Schwabhauser]
     p. 45.  See ~ ellines for membership.  (Contributed by Scott Fenton,
     28-Oct-2013.) $)
  df-lines2 $a |- LinesEE = ran Line $.

  ${
    $d a m $.  $d a n $.  $d a p $.  $d a r $.  $d a s $.  $d a x $.  $d m n $.
    $d m p $.  $d m r $.  $d m s $.  $d m x $.  $d n p $.  $d n r $.  $d n s $.
    $d n x $.  $d p r $.  $d p s $.  $d p x $.  $d r s $.  $d r x $.  $d s x $.

    $( Show that the ` Ray ` relationship is a function.  (Contributed by Scott
       Fenton, 21-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    funray $p |- Fun Ray $=
      ( vp vn va vr vx vm vs cray wfun cv cee cfv wcel w3a crab wceq wa cn wrex
      wi wne cop coutsideof wbr coprab wmo weq wal reeanv simp1 axdimuniq fveq2
      rabeq syl eqeq2d anbi1d eqtr3 biimtrdi an4s ex com3l syl2an imp rexlimivv
      com12 sylbir eqeq1 anbi2d rexbidv eleq2d 3anbi12d anbi12d cbvrexvw bitrdi
      gen2 mo4 mpbir funoprab df-ray funeqi ) HIAJZBJZKLZMZCJZWCMZWAWEUAZNZDJZW
      AWEEJUBUCUDZEWCOZPZQZBRSZACDUEZIWNACDWNDUFWNWAFJZKLZMZWEWQMZWGNZGJZWJEWQO
      ZPZQZFRSZQZDGUGZTZGUHDUHXHDGXFWMXDQZFRSBRSXGWMXDBFRRUIXIXGBFRRXIWBRMZWPRM
      ZQZXGWHWTWLXCXLXGTZWHWTQWLXCQZXMWHWDWRXNXMTWTWDWFWGUJWRWSWGUJXLWDWRQZXNXG
      XLXOXNXGTZXJWDXKWRXPXJWDQXKWRQQBFUGZXPWAWPWBUKXQXNWIXBPZXCQXGXQWLXRXCXQWK
      XBWIXQWCWQPWKXBPWBWPKULZWJEWCWQUMUNZUOUPWIXAXBUQURUNUSUTVAVBVCUSVEVDVFVOW
      NXEDGXGWNWHXAWKPZQZBRSXEXGWMYBBRXGWLYAWHWIXAWKVGVHVIYBXDBFRXQWHWTYAXCXQWD
      WRWFWSWGXQWCWQWAXSVJXQWCWQWEXSVJVKXQWKXBXAXTUOVLVMVNVPVQVRHWOEBDACVSVTVQ
      $.
  $}

  ${
    $d A a $.  $d a n $.  $d A n $.  $d a p $.  $d A p $.  $d a r $.  $d A r $.
    $d a x $.  $d A x $.  $d N a $.  $d N n $.  $d n p $.  $d N p $.  $d n r $.
    $d N r $.  $d n x $.  $d N x $.  $d P a $.  $d P n $.  $d P p $.  $d p r $.
    $d P r $.  $d p x $.  $d P x $.  $d r x $.
    $( Calculate the value of the ` Ray ` function.  (Contributed by Scott
       Fenton, 21-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    fvray $p |- ( ( N e. NN /\
           ( P e. ( EE ` N ) /\ A e. ( EE ` N ) /\ P =/= A ) ) ->
           ( P Ray A ) =
             { x e. ( EE ` N ) | P OutsideOf <. A , x >. } ) $=
      ( vp vn va vr cn wcel cee w3a wa cray cop cv coutsideof wbr crab wceq cfv
      wne df-ov wrex coprab eqid fveq2 eleq2d 3anbi12d rabeq syl eqeq2d anbi12d
      co rspcev mpanr2 wb simpr1 simpr2 fvex rabex eleq1 neeq1 3anbi13d rabbidv
      cvv breq1 rexbidv neeq2 3anbi23d opeq1 breq2d eqeq1 anbi2d mp3an3 syl2anc
      eloprabg mpbird df-br df-ray eleq2i bitri wi funray funbrfv sylbir eqtrid
      wfun ax-mp ) DIJZCDKUAZJZBWKJZCBUBZLZMZCBNUNCBOZNUAZCBAPZOZQRZAWKSZCBNUCW
      PWQXBOZEPZFPZKUAZJZGPZXFJZXDXHUBZLZHPZXDXHWSOZQRZAXFSZTZMZFIUDZEGHUEZJZWR
      XBTZWPXTCXFJZBXFJZWNLZXBXAAXFSZTZMZFIUDZWJWOXBXBTZYHXBUFYGWOYIMFDIXEDTZYD
      WOYFYIYJYBWLYCWMWNYJXFWKCXEDKUGZUHYJXFWKBYKUHUIYJYEXBXBYJXFWKTYEXBTYKXAAX
      FWKUJUKULUMUOUPWPWLWMXTYHUQZWJWLWMWNURWJWLWMWNUSWLWMXBVFJYLXAAWKDKUTVAXRY
      BXICXHUBZLZXLCXMQRZAXFSZTZMZFIUDYDXLYETZMZFIUDYHEGHCBXBWKWKVFXDCTZXQYRFIU
      UAXKYNXPYQUUAXGYBXJYMXIXDCXFVBXDCXHVCVDUUAXOYPXLUUAXNYOAXFXDCXMQVGVEULUMV
      HXHBTZYRYTFIUUBYNYDYQYSUUBXIYCYMWNYBXHBXFVBXHBCVIVJUUBYPYEXLUUBYOXAAXFUUB
      XMWTCQXHBWSVKVLVEULUMVHXLXBTZYTYGFIUUCYSYFYDXLXBYEVMVNVHVQVOVPVRXTWQXBNRZ
      YAUUDXCNJXTWQXBNVSNXSXCAFHEGVTWAWBNWHUUDYAWCWDWQXBNWEWIWFUKWG $.
  $}

  ${
    $d a b $.  $d a k $.  $d a l $.  $d a m $.  $d a n $.  $d b k $.  $d b l $.
    $d b m $.  $d b n $.  $d k l $.  $d k m $.  $d k n $.  $d l m $.  $d l n $.
    $d m n $.
    $( Show that the ` Line ` relationship is a function.  (Contributed by
       Scott Fenton, 25-Oct-2013.)  (Revised by Mario Carneiro,
       19-Apr-2014.) $)
    funline $p |- Fun Line $=
      ( va vn vb vl vm vk cline2 wfun cv cee cfv wcel w3a wceq wa cn weq wi wal
      wrex wne cop ccolin cec coprab wmo reeanv eqtr3 ad2ant2l rexlimivv sylbir
      ccnv a1i gen2 eqeq1 anbi2d rexbidv eleq2d 3anbi12d anbi1d cbvrexvw bitrdi
      fveq2 mo4 mpbir funoprab df-line2 funeqi ) GHAIZBIZJKZLZCIZVKLZVIVMUAZMZD
      IZVIVMUBUCULUDZNZOZBPTZACDUEZHWAACDWADUFWAVIEIZJKZLZVMWDLZVOMZFIZVRNZOZEP
      TZOZDFQZRZFSDSWNDFWLVTWJOZEPTBPTWMVTWJBEPPUGWOWMBEPPWOWMRVJPLWCPLOVSWIWMV
      PWGVQWHVRUHUIUMUJUKUNWAWKDFWMWAVPWIOZBPTWKWMVTWPBPWMVSWIVPVQWHVRUOUPUQWPW
      JBEPBEQZVPWGWIWQVLWEVNWFVOWQVKWDVIVJWCJVCZURWQVKWDVMWRURUSUTVAVBVDVEVFGWB
      BACDVGVHVE $.
  $}

  ${
    $d A l $.  $d A n $.  $d A x $.  $d A y $.  $d l n $.  $d l x $.  $d l y $.
    $d n x $.  $d n y $.  $d x y $.
    $( When ` Line ` is applied with the same argument, the result is the empty
       set.  (Contributed by Scott Fenton, 29-Oct-2013.)  (Revised by Mario
       Carneiro, 19-Apr-2014.) $)
    linedegen $p |- ( A Line A ) = (/) $=
      ( vx vn vy vl cline2 cop cfv wcel wn wceq cv wne w3a cec wa wrex wex cvv
      cn co c0 df-ov cdm cee ccolin ccnv copab neirr simp3 mto intnanr a1i nrex
      nex eleq1 neeq1 3anbi13d opeq1 eceq1d eqeq2d anbi12d rexbidv exbidv neeq2
      wb 3anbi23d opeq2 opelopabg anidms mtbiri cxp elopaelxp opelxp1 syl con3i
      pm2.61i coprab df-line2 dmeqi dmoprab eqtri eleq2i mtbir ndmfv ax-mp ) AA
      FUAAAGZFHZUBAAFUCWGFUDZIZJWHUBKWJWGBLZCLZUEHZIZDLZWMIZWKWOMZNZELZWKWOGZUF
      UGZOZKZPZCTQZERZBDUHZIZASIZXHJXIXHAWMIZXJAAMZNZWSWGXAOZKZPZCTQZERZXPEXOCT
      XOJWLTIXLXNXLXKAUIXJXJXKUJUKULUMUNUOXIXHXQVFXFXJWPAWOMZNZWSAWOGZXAOZKZPZC
      TQZERXQBDAASSWKAKZXEYDEYEXDYCCTYEWRXSXCYBYEWNXJWQXRWPWKAWMUPWKAWOUQURYEXB
      YAWSYEWTXTXAWKAWOUSUTVAVBVCVDWOAKZYDXPEYFYCXOCTYFXSXLYBXNYFWPXJXRXKXJWOAW
      MUPWOAAVEVGYFYAXMWSYFXTWGXAWOAAVHUTVAVBVCVDVIVJVKXHXIXHWGSSVLIXIXFBDWGVMA
      ASSVNVOVPVQWIXGWGWIXEBDEVRZUDXGFYGCBDEVSVTXEBDEWAWBWCWDWGFWEWFWB $.
  $}

  ${
    $d A a $.  $d a b $.  $d A b $.  $d a l $.  $d A l $.  $d a n $.  $d A n $.
    $d A x $.  $d B a $.  $d B b $.  $d b l $.  $d B l $.  $d b n $.  $d B n $.
    $d B x $.  $d l n $.  $d N n $.
    $( Calculate the value of the ` Line ` function.  (Contributed by Scott
       Fenton, 25-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    fvline $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ A =/= B ) ) ->
       ( A Line B ) = { x | x Colinear <. A , B >. } ) $=
      ( va vn vb vl cn wcel cee w3a wa cline2 cop ccolin cv wceq wrex cvv fveq2
      cfv wne ccnv cec wbr cab coprab eqid eleq2d 3anbi12d anbi1d rspcev mpanr2
      co simpr1 simpr2 colinearex cnvex ecexg ax-mp eleq1 neeq1 3anbi13d eceq1d
      wb opeq1 eqeq2d anbi12d neeq2 3anbi23d opeq2 eqeq1 anbi2d eloprabg mp3an3
      rexbidv syl2anc mpbird df-ov df-br df-line2 bitri wfun wi funline funbrfv
      eleq2i sylbir eqtrid syl opex dfec2 vex brcnv abbii eqtri eqtrdi ) DIJZBD
      KUBZJZCWTJZBCUCZLZMZBCNUOZBCOZPUDZUEZAQZXGPUFZAUGZXEXGXIOZEQZFQZKUBZJZGQZ
      XPJZXNXRUCZLZHQZXNXROZXHUEZRZMZFISZEGHUHZJZXFXIRXEYIBXPJZCXPJZXCLZXIXIRZM
      ZFISZWSXDYMYOXIUIYNXDYMMFDIXODRZYLXDYMYPYJXAYKXBXCYPXPWTBXODKUAZUJYPXPWTC
      YQUJUKULUMUNXEXAXBYIYOVFZWSXAXBXCUPWSXAXBXCUQXAXBXITJZYRXHTJYSPURUSXGTXHU
      TVAYGYJXSBXRUCZLZYBBXROZXHUEZRZMZFISYLYBXIRZMZFISYOEGHBCXIWTWTTXNBRZYFUUE
      FIUUHYAUUAYEUUDUUHXQYJXTYTXSXNBXPVBXNBXRVCVDUUHYDUUCYBUUHYCUUBXHXNBXRVGVE
      VHVIVQXRCRZUUEUUGFIUUIUUAYLUUDUUFUUIXSYKYTXCYJXRCXPVBXRCBVJVKUUIUUCXIYBUU
      IUUBXGXHXRCBVLVEVHVIVQUUFUUGYNFIUUFUUFYMYLYBXIXIVMVNVQVOVPVRVSYIXFXGNUBZX
      IBCNVTYIXGXINUFZUUJXIRZUUKXMNJYIXGXINWANYHXMFEGHWBWHWCNWDUUKUULWEWFXGXINW
      GVAWIWJWKXIXGXJXHUFZAUGZXLXGTJXIUUNRBCWLZAXGXHTWMVAUUMXKAXGXJPUUOAWNWOWPW
      QWR $.
  $}

  ${
    $d N x $.  $d A x $.  $d B x $.
    $( A line is a subset of the space its two points lie in.  (Contributed by
       Scott Fenton, 25-Oct-2013.)  (Revised by Mario Carneiro,
       19-Apr-2014.) $)
    liness $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ A =/= B ) ) ->
       ( A Line B ) C_ ( EE ` N ) ) $=
      ( vx cn wcel cee cfv wne w3a wa cline2 co cop ccolin wbr cab fvline cvv
      cv wi vex a1i simp1 simp2 3jca colineardim1 sylan2 abssdv eqsstrd ) CEFZA
      CGHZFZBULFZABIZJZKZABLMDTZABNOPZDQULDABCRUQUSDULUPUKURSFZUMUNJUSURULFUAUP
      UTUMUNUTUPDUBUCUMUNUOUDUMUNUOUEUFURABCSULUGUHUIUJ $.

    $( Alternate definition of a line.  (Contributed by Scott Fenton,
       25-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    fvline2 $p |- ( ( N e. NN /\
       ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ A =/= B ) ) ->
       ( A Line B ) = { x e. ( EE ` N ) | x Colinear <. A , B >. } ) $=
      ( cn wcel cee cfv wne w3a wa cline2 co cv cop ccolin wbr cab cin crab wss
      fvline wceq liness eqsstrrd dfss2 sylib eqtr4d dfrab2 eqtr4di ) DEFBDGHZF
      CUKFBCIJKZBCLMZANBCOPQZARZUKSZUNAUKTULUMUOUPABCDUBZULUOUKUAUPUOUCULUOUMUK
      UQBCDUDUEUOUKUFUGUHUNAUKUIUJ $.
  $}

  ${
    $d N x $.  $d P x $.  $d Q x $.  $d R x $.
    $( A line is composed of a point and the two rays emerging from it.
       Theorem 6.15 of [Schwabhauser] p. 45.  (Contributed by Scott Fenton,
       26-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    lineunray $p |- ( ( N e. NN /\
       ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ R e. ( EE ` N ) ) /\
       ( P =/= Q /\ P =/= R ) ) ->
       ( P Btwn <. Q , R >. ->
       ( P Line Q ) = ( ( ( P Ray Q ) u. { P } ) u. ( P Ray R ) ) ) ) $=
      ( vx wcel w3a wne wa cop cbtwn wbr cun wceq crab wo wb syl13anc adantr wi
      cn cee cfv cline2 co cray csn cv ccolin coutsideof simpl1 simpl21 simpl22
      w3o simpr brcolinear olc orcd simpl3l necomd simprl simprr 3jca btwnconn2
      a1i simpl23 syl122anc mpd olcd expr btwncom biimtrdi sylbid colineartriv1
      3jaod syl6 syl3anc breq1 syl5ibrcom btwncolinear3 btwncolinear5 btwnouttr
      orc simpl3r btwncolinear4 btwncomand btwnexch3and btwncolinear2 impbid wn
      jaod pm5.63 df-ne anbi1i bitr3i orbi2i bitrdi broutsideof2 3simpc simprrl
      andi bitri simprrr impbid2 bitrd orbi12d orbi2d orcom or32 an32s rabbidva
      bitr4d simp1 simp21 simp22 simp3l fvline2 fvray syl eqcomd uneq12d simp23
      rabsn simp3r unrab uneq1i eqtri eqtrdi 3eqtr4d ex ) DUAFZADUBUCZFZBYLFZCY
      LFZGZABHZACHZIZGZABCJKLZABUDUEZABUFUEZAUGZMZACUFUEZMZNYTUUAIZEUHZABJZUILZ
      EYLOZABUUIJZUJLZUUIANZPZACUUIJUJLZPZEYLOZUUBUUGUUHUUKUUREYLYTUUIYLFZUUAUU
      KUURQYTUUTIZUUAIZUUKUUOUUNUUQPZPZUURUVBUUKUUOUUIAHZBAUUIJZKLZUUIUUJKLZPZI
      ZUVECUVFKLZUUIACJKLZPZIZPZPZUVDUVBUUKUUOUVIUVMPZPZUVPUVBUUKUVRUVBUUKUVQUV
      RUVBUUKUVHAUUMKLZBUUIAJKLZUNZUVQUVAUUKUWAQZUUAUVAYKUUTYMYNUWBYKYPYSUUTUKZ
      YTUUTUOZYMYNYOYKYSUUTULZYMYNYOYKYSUUTUMZUUIABDUPRSUVBUVHUVQUVSUVTUVHUVQTU
      VBUVHUVIUVMUVHUVGUQURVEUVAUUAUVSUVQUVAUUAUVSIZIZUVMUVIUWHBAHZUUAUVSGZUVMU
      WHUWIUUAUVSUVAUWIUWGUVAABYQYRYKYPUUTUSUTSUVAUUAUVSVAUVAUUAUVSVBVCUVAUWJUV
      MTZUWGUVAYKYNYMYOUUTUWKUWCUWFUWEYMYNYOYKYSUUTVFZUWDBACUUIDVDVGSVHVIVJUVAU
      VTUVQTUUAUVAUVTUVGUVQUVAYKYNUUTYMUVTUVGQUWCUWFUWDUWEBUUIADVKRUVGUVIUVMUVG
      UVHWCURVLSVOVMUVQUUOUQVPUVBUUOUUKUVQUVAUUOUUKTUUAUVAUUKUUOAUUJUILZUVAYKYM
      YNUWMUWCUWEUWFABDVNVQUUIAUUJUIVRVSSUVBUVIUUKUVMUVAUVIUUKTUUAUVAUVGUUKUVHU
      VAYKYMUUTYNUVGUUKTUWCUWEUWDUWFAUUIBDVTRUVAYKYMYNUUTUVHUUKTUWCUWEUWFUWDABU
      UIDWARWKSUVBUVKUUKUVLUVAUUAUVKUUKUVAUUAUVKIZIZUVSUUKUWOYRUUAUVKGZUVSUWOYR
      UUAUVKUVAYRUWNYQYRYKYPUUTWDSUVAUUAUVKVAUVAUUAUVKVBVCUVAUWPUVSTZUWNUVAYKYN
      YMYOUUTUWQUWCUWFUWEUWLUWDBACUUIDWBVGSVHUVAUVSUUKTZUWNUVAYKYNUUTYMUWRUWCUW
      FUWDUWEBUUIADWERSVHVJUVAUUAUVLUUKUVAUUAUVLIZIAUUIBJKLZUUKUVAUWSCUUIABDUWC
      UWLUWDUWEUWFUVAUWSUUIACDUWCUWDUWEUWLUVAUUAUVLVBWFUVAUWSABCDUWCUWEUWFUWLUV
      AUUAUVLVAWFWGUVAUWTUUKTZUWSUVAYKUUTYNYMUXAUWCUWDUWFUWEUUIBADWHRSVHVJWKWKW
      KWIUVRUUOUUOWJZUVQIZPUVPUUOUVQWLUXCUVOUUOUXCUVEUVQIUVOUVEUXBUVQUUIAWMWNUV
      EUVIUVMXAWOWPXBWQUVBUVCUVOUUOUVAUVCUVOQUUAUVAUUNUVJUUQUVNUVAUUNUWIUVEUVIG
      ZUVJUVAYKYMYNUUTUUNUXDQUWCUWEUWFUWDBUUIADWRRUVAUXDUVJUWIUVEUVIWSYTUUTUVJU
      XDYTUUTUVJIZIZUWIUVEUVIUXFABYQYRYKYPUXEUSUTYTUUTUVEUVIWTYTUUTUVEUVIXCVCVJ
      XDXEUVAUUQCAHZUVEUVMGZUVNUVAYKYMYOUUTUUQUXHQUWCUWEUWLUWDCUUIADWRRUVAUXHUV
      NUXGUVEUVMWSYTUUTUVNUXHYTUUTUVNIZIZUXGUVEUVMUXJACYQYRYKYPUXIWDUTYTUUTUVEU
      VMWTYTUUTUVEUVMXCVCVJXDXEXFSXGXLUVDUVCUUOPUURUUOUVCXHUUNUUQUUOXIXBWQXJXKY
      TUUBUULNZUUAYTYKYMYNYQUXKYKYPYSXMZYKYMYNYOYSXNZYKYMYNYOYSXOZYKYPYQYRXPZEA
      BDXQRSUUHUUGUUNEYLOZUUOEYLOZMZUUQEYLOZMZUUSYTUUGUXTNUUAYTUUEUXRUUFUXSYTUU
      CUXPUUDUXQYTYKYMYNYQUUCUXPNUXLUXMUXNUXOEBADXRRYTUXQUUDYTYMUXQUUDNUXMEYLAY
      CXSXTYAYTYKYMYOYRUUFUXSNUXLUXMYKYMYNYOYSYBYKYPYQYRYDECADXRRYASUXTUUPEYLOZ
      UXSMUUSUXRUYAUXSUUNUUOEYLYEYFUUPUUQEYLYEYGYHYIYJ $.
  $}

  ${
    $d N x $.  $d P x $.  $d Q x $.  $d S x $.
    $( If ` S ` lies on ` P Q ` , then ` P Q = P S ` .  Theorem 6.16 of
       [Schwabhauser] p. 45.  (Contributed by Scott Fenton, 27-Oct-2013.)
       (Revised by Mario Carneiro, 19-Apr-2014.) $)
    lineelsb2 $p |- ( ( N e. NN /\
      ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ P =/= Q ) /\
      ( S e. ( EE ` N ) /\ P =/= S ) ) ->
        ( S e. ( P Line Q ) -> ( P Line Q ) = ( P Line S ) ) ) $=
      ( vx w3a wa cop wbr cbtwn syl13anc adantr syl122anc mpd simprl btwncomand
      wi expr simprr mp3and cn wcel cee cfv wne ccolin cv crab cline2 co wb w3o
      wceq simpl1 simpl3l simpl21 simpl22 brcolinear biimpa simpr btwnconn3 imp
      btwncolinear3 btwncolinear5 btwnexch3and btwncolinear4 btwnexchand sylbid
      wo 3jaod simpl3r necomd btwnouttr2 btwnconn1 impbid btwncolinear2 simpl23
      jaod btwnconn2 btwnouttr mp2and 3jaodan adantrl an32s rabbidva ex fvline2
      syldan 3adant3 eleq2d breq1 bitrdi simp21 simp3l simp3r eqeq12d 3imtr4d
      elrab simp1 ) DUAUBZADUCUDZUBZBXAUBZABUEZFZCXAUBZACUEZGZFZXFCABHZUFIZGZEU
      GZXJUFIZEXAUHZXMACHZUFIZEXAUHZUMZCABUIUJZUBZXTACUIUJZUMXIXLXSXIXLGXNXQEXA
      XIXMXAUBZXLXNXQUKZXIYCGZXKYDXFYEXKCXJJIZABCHJIZBCAHJIZULZYDYEXKYIYEWTXFXB
      XCXKYIUKWTXEXHYCUNZXFXGWTXEYCUOZXBXCXDWTXHYCUPZXBXCXDWTXHYCUQZCABDURKUSYE
      YFYDYGYHYEYFGZXNXQYNXNXMXJJIZABXMHJIZBXMAHZJIZULZXQYEXNYSUKZYFYEWTYCXBXCY
      TYJXIYCUTZYLYMXMABDURKZLYNYOXQYPYRYEYFYOXQYEYFYOGZGCAXMHZJIZXMXPJIZVIZXQY
      EUUCUUGYEWTXBXFYCXCUUCUUGQYJYLYKUUAYMACXMBDVAMVBYEUUGXQQZUUCYEUUEXQUUFYEW
      TXBYCXFUUEXQQZYJYLUUAYKAXMCDVCKZYEWTXBXFYCUUFXQQZYJYLYKUUAACXMDVDKZVRZLNR
      YEYFYPXQYEYFYPGZGACXMHJIZXQYEUUNBCAXMDYJYMYKYLUUAYEUUNCABDYJYKYLYMYEYFYPO
      PYEYFYPSVEYEUUOXQQZUUNYEWTXFYCXBUUPYJYKUUAYLCXMADVFKZLNRYEYFYRXQYEYFYRGZG
      UUEXQYEUURACBXMDYJYLYKYMUUAYEYFYROYEUURBXMADYJYMUUAYLYEYFYRSPVGYEUUIUURUU
      JLNRVJVHYNXQUUFUUOCYQJIZULZXNYEXQUUTUKZYFYEWTYCXBXFUVAYJUUAYLYKXMACDURKZL
      YNUUFXNUUOUUSYEYFUUFXNYEYFUUFGZGYOXNYEUVCAXMCBDYJYLUUAYKYMYEYFUUFSYEYFUUF
      OVGYEYOXNQZUVCYEWTXBXCYCUVDYJYLYMUUAABXMDVDKZLNRYEYFUUOXNYEYFUUOGZGZYPXNU
      VGCAUEZCBAHJIZUUOYPYEUVHUVFYEACXFXGWTXEYCVKZVLZLYEUVFCABDYJYKYLYMYEYFUUOO
      PYEYFUUOSYEUVHUVIUUOFYPQZUVFYEWTXCXFXBYCUVLYJYMYKYLUUABCAXMDVMMLTYEYPXNQZ
      UVFYEWTXCYCXBUVMYJYMUUAYLBXMADVFKZLNRYEYFUUSXNYEYFUUSGZGZBUUDJIZYOVIZXNUV
      PXGYFUUEUVRYEXGUVOUVJLYEYFUUSOYEUVOCXMADYJYKUUAYLYEYFUUSSPYEXGYFUUEFUVRQZ
      UVOYEWTXBXFXCYCUVSYJYLYKYMUUAACBXMDVNMLTYEUVRXNQZUVOYEUVQXNYOYEWTXBYCXCUV
      QXNQZYJYLUUAYMAXMBDVCKZUVEVRZLNRVJVHVOYEYGGZXNXQUWDXNYSXQYEYTYGUUBLUWDYOX
      QYPYRYEYGYOXQYEYGYOGZGAXMCHJIZXQYEUWEBXMACDYJYMUUAYLYKYEUWEXMABDYJUUAYLYM
      YEYGYOSPYEYGYOOVEYEUWFXQQZUWEYEWTYCXFXBUWGYJUUAYKYLXMCADVPKLNRYEYGYPXQYEY
      GYPGZGZUUGXQUWIBAUEZYGYPUUGYEUWJUWHYEABXBXCXDWTXHYCVQZVLZLYEYGYPOYEYGYPSY
      EUWJYGYPFUUGQZUWHYEWTXCXBXFYCUWMYJYMYLYKUUABACXMDVSMLTYEUUHUWHUUMLNRYEYGY
      RXQYEYGYRGZGZUUOXQUWOXDACBHJIZUVQUUOYEXDUWNUWKLYEUWNABCDYJYLYMYKYEYGYROPY
      EUWNBXMADYJYMUUAYLYEYGYRSPYEXDUWPUVQFUUOQZUWNYEWTXFXBXCYCUWQYJYKYLYMUUACA
      BXMDVTMLTYEUUPUWNUUQLNRVJVHUWDXQUUTXNYEUVAYGUVBLUWDUUFXNUUOUUSYEYGUUFXNYE
      YGUUFGZGAXMBHJIZXNYEUWRCXMABDYJYKUUAYLYMYEUWRXMACDYJUUAYLYKYEYGUUFSPYEUWR
      ABCDYJYLYMYKYEYGUUFOPVEYEUWSXNQZUWRYEWTYCXCXBUWTYJUUAYMYLXMBADVPKLNRYEYGU
      UOXNYEYGUUOGZGZUVRXNUXBUVHUWPUUOUVRYEUVHUXAUVKLYEUXAABCDYJYLYMYKYEYGUUOOP
      YEYGUUOSYEUVHUWPUUOFUVRQZUXAYEWTXFXBXCYCUXCYJYKYLYMUUACABXMDVSMLTYEUVTUXA
      UWCLNRYEYGUUSXNYEYGUUSGZGZYPXNUXEXGYGUUEYPYEXGUXDUVJLYEYGUUSOYEUXDCXMADYJ
      YKUUAYLYEYGUUSSPYEXGYGUUEFYPQZUXDYEWTXCXBXFYCUXFYJYMYLYKUUABACXMDVTMLTYEU
      VMUXDUVNLNRVJVHVOYEYHGZXNXQUXGXNYSXQYEYTYHUUBLUXGYOXQYPYRYEYHYOXQYEYHYOGZ
      GUUFXQYEUXHAXMBCDYJYLUUAYMYKYEYHYOSYEUXHBCADYJYMYKYLYEYHYOOPVGYEUUKUXHUUL
      LNRYEYHYPXQYEYHYPGZGZUUOXQUXJUWJYHYPUUOYEUWJUXIUWLLYEYHYPOYEYHYPSYEUWJYHY
      PFUUOQZUXIYEWTXFXCXBYCUXKYJYKYMYLUUACBAXMDVMMLTYEUUPUXIUUQLNRYEYHYRXQYEYH
      YRGZGZUUGXQUXMXDBXPJIZUVQUUGYEXDUXLUWKLYEUXLBCADYJYMYKYLYEYHYROPYEUXLBXMA
      DYJYMUUAYLYEYHYRSPYEXDUXNUVQFUUGQZUXLYEWTXBXCXFYCUXOYJYLYMYKUUAABCXMDVNML
      TYEUUHUXLUUMLNRVJVHUXGXQUUTXNYEUVAYHUVBLUXGUUFXNUUOUUSYEYHUUFXNYEYHUUFGZG
      ZUVRXNUXQUXNUUFUVRYEUXPBCADYJYMYKYLYEYHUUFOPYEYHUUFSYEUXNUUFGUVRQZUXPYEWT
      XBXCYCXFUXRYJYLYMUUAYKABXMCDVAMLWAYEUVTUXPUWCLNRYEYHUUOXNYEYHUUOGZGYPXNYE
      UXSCBAXMDYJYKYMYLUUAYEYHUUOOYEYHUUOSVEYEUVMUXSUVNLNRYEYHUUSXNYEYHUUSGZGUV
      QXNYEUXTABCXMDYJYLYMYKUUAYEUXTBCADYJYMYKYLYEYHUUSOPYEUXTCXMADYJYKUUAYLYEY
      HUUSSPVGYEUWAUXTUWBLNRVJVHVOWBWHWCWDWEWFXIYACXOUBXLXIXTXOCWTXEXTXOUMXHEAB
      DWGWIZWJXNXKECXAXMCXJUFWKWRWLXIXTXOYBXRUYAXIWTXBXFXGYBXRUMWTXEXHWSWTXBXCX
      DXHWMWTXEXFXGWNWTXEXFXGWOEACDWGKWPWQ $.
  $}

  ${
    $d N x $.  $d P x $.  $d Q x $.
    $( Reflexivity law for line membership.  Part of theorem 6.17 of
       [Schwabhauser] p. 45.  (Contributed by Scott Fenton, 28-Oct-2013.)
       (Revised by Mario Carneiro, 19-Apr-2014.) $)
    linerflx1 $p |- ( ( N e. NN /\
        ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ P =/= Q ) ) ->
        P e. ( P Line Q ) ) $=
      ( vx cn wcel cee cfv wne w3a wa cv cop ccolin wbr cline2 co colineartriv1
      crab simpr1 3adant3r3 breq1 elrab sylanbrc fvline2 eleqtrrd ) CEFZACGHZFZ
      BUHFZABIZJKZADLZABMZNOZDUHSZABPQULUIAUNNOZAUPFUGUIUJUKTUGUIUJUQUKABCRUAUO
      UQDAUHUMAUNNUBUCUDDABCUEUF $.

    $( Commutativity law for lines.  Part of theorem 6.17 of [Schwabhauser]
       p. 45.  (Contributed by Scott Fenton, 28-Oct-2013.)  (Revised by Mario
       Carneiro, 19-Apr-2014.) $)
    linecom $p |- ( ( N e. NN /\
        ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ P =/= Q ) ) ->
        ( P Line Q ) = ( Q Line P ) ) $=
      ( vx cn wcel cee cfv wne w3a wa cv cop ccolin wbr crab cline2 co fvline2
      wb simp1 simp3 simp21 simp22 colinearperm1 syl13anc rabbidva wceq 3anbi3i
      3expa necom 3ancoma bitri sylan2b 3eqtr4d ) CEFZACGHZFZBUQFZABIZJZKZDLZAB
      MNOZDUQPVCBAMNOZDUQPZABQRBAQRZVBVDVEDUQUPVAVCUQFZVDVETZUPVAVHJUPVHURUSVIU
      PVAVHUAUPVAVHUBUPURUSUTVHUCUPURUSUTVHUDVCABCUEUFUJUGDABCSVAUPUSURBAIZJZVG
      VFUHVAURUSVJJVKUTVJURUSABUKUIURUSVJULUMDBACSUNUO $.
  $}

  $( Reflexivity law for line membership.  Part of theorem 6.17 of
     [Schwabhauser] p. 45.  (Contributed by Scott Fenton, 28-Oct-2013.)
     (Revised by Mario Carneiro, 19-Apr-2014.) $)
  linerflx2 $p |- ( ( N e. NN /\
        ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ P =/= Q ) ) ->
        Q e. ( P Line Q ) ) $=
    ( cn wcel cee cfv wne w3a wa cline2 necom 3anbi3i 3ancoma linerflx1 sylan2b
    co bitri linecom eleqtrrd ) CDEZACFGZEZBUBEZABHZIZJBBAKQZABKQUFUAUDUCBAHZIZ
    BUGEUFUCUDUHIUIUEUHUCUDABLMUCUDUHNRBACOPABCST $.

  ${
    $d A n $.  $d A p $.  $d A q $.  $d A x $.  $d n p $.  $d n q $.  $d n x $.
    $d p q $.  $d p x $.  $d q x $.
    $( Membership in the set of all lines.  (Contributed by Scott Fenton,
       28-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    ellines $p |- ( A e. LinesEE <->
             E. n e. NN E. p e. ( EE ` n ) E. q e. ( EE ` n )
                ( p =/= q /\ A = ( p Line q ) ) ) $=
      ( vx clines2 wcel cvv cv cline2 wceq wa wrex cn ccolin bitr3i bitri anass
      wex cab wne co cee cfv elex wi ovex mpbiri adantl rexlimivw a1i rexlimivv
      eleq1 eqeq1 anbi2d rexbidv 2rexbidv w3a cop ccnv cec crn coprab df-lines2
      df-line2 rneqi rnoprab 3eqtri eleq2i df-rex 2exbii exrot3 r19.42v simplrl
      abid r2ex simplrr simpll simpr 3jca jca simpr2 simpl simpr1 simpr3 impbii
      jca32 anbi1i wbr fvline opex dfec2 ax-mp brcnv abbii eqtri eqtr4di eqeq2d
      vex pm5.32i 3bitrri 3exbii 3bitr4ri vtoclbg pm5.21nii ) AFGZAHGZDIZCIZUAZ
      AXHXIJUBZKZLZCBIZUCUDZMZDXOMBNMZAFUEXPXGBDNXOXPXGUFXNNGZXHXOGZLZXMXGCXOXL
      XGXJXLXGXKHGXHXIJUGAXKHUMUHUIUJUKULEIZFGZXJYAXKKZLZCXOMZDXOMBNMZXFXQEAHYA
      AFUMYAAKZYEXPBDNXOYGYDXMCXOYGYCXLXJYAAXKUNUOUPUQYBYAXSXIXOGZXJURZYAXHXIUS
      ZOUTZVAZKZLZBNMZCSDSZETZGZYFFYQYAFJVBYODCEVCZVBYQVDJYSBDCEVEVFYODCEVGVHVI
      YRYPYFYPEVOYPXRYNLZBSZCSDSZYFYOUUADCYNBNVJVKYHXTYDLZLZCSZDSBSZUUDBSCSDSYF
      UUBUUDBDCVLYFXTYELZDSBSUUFYEBDNXOVPUUGUUEBDUUGUUCCXOMUUEXTYDCXOVMUUCCXOVJ
      PVKQYTUUDDCBUUDXRYILZYCLZUUHYMLYTUUDYHXTLZYDLZUUIYHXTYDRUUKUUJXJLZYCLUUIU
      UJXJYCRUULUUHYCUULUUHUULXRYIYHXRXSXJVNUULXSYHXJYHXRXSXJVQYHXTXJVRUUJXJVSV
      TWAUUHUUJXJUUHYHXRXSXRXSYHXJWBXRYIWCXRXSYHXJWDWGXRXSYHXJWEWAWFWHPPUUHYCYM
      UUHXKYLYAUUHXKYAYJOWIZETZYLEXHXIXNWJYLYJYAYKWIZETZUUNYJHGYLUUPKXHXIWKZEYJ
      YKHWLWMUUOUUMEYJYAOUUQEWSWNWOWPWQWRWTXRYIYMRXAXBXCQQQXDXE $.
  $}

  ${
    $d A a $.  $d a b $.  $d A b $.  $d a n $.  $d A n $.  $d b n $.  $d P a $.
    $d P b $.  $d P n $.  $d Q a $.  $d Q b $.  $d Q n $.
    $( If ` A ` is a line containing two distinct points ` P ` and ` Q ` , then
       ` A ` is the line through ` P ` and ` Q ` .  Theorem 6.18 of
       [Schwabhauser] p. 45.  (Contributed by Scott Fenton, 28-Oct-2013.)
       (Revised by Mario Carneiro, 19-Apr-2014.) $)
    linethru $p |- ( ( A e. LinesEE /\ ( P e. A /\ Q e. A ) /\ P =/= Q ) ->
       A = ( P Line Q ) ) $=
      ( va vb vn wcel wa cline2 co wceq cv wrex cn wi syl13anc necomd lineelsb2
      wne syl132anc clines2 cee cfv ellines w3a simpll1 simpll2 simpll3 simprll
      wss simplr liness sseldd simprlr simplll adantl simprrl mpd linecom eqtrd
      neeq2 anbi2d anbi1d eqeq2d imbi12d mpbiri syl2anc simp1l1 simp1l2 simp1l3
      oveq2 simp2l simp1r simp2rr simplld eleqtrd simp2rl simp2lr 3eqtrd expcom
      simp1 simp3 3expa pm2.61ine expr mp2and ex eleq2 anbi12d eqeq1 syl5ibrcom
      expimpd rexlimdva rexlimivv sylbi 3impib ) AUAGZBAGZCAGZHZBCSZABCIJZKZWQD
      LZELZSZAXDXEIJZKZHZEFLZUBUCZMZDXKMFNMWTXAHZXCOZAFEDUDXLXNFDNXKXJNGZXDXKGZ
      HXIXNEXKXOXPXEXKGZXIXNOXOXPXQUEZXFXHXNXRXFHZXNXHBXGGZCXGGZHZXAHZXGXBKZOXS
      YCYDXSYCHZBXKGZCXKGZYDYEXGXKBYEXOXPXQXFXGXKUJXOXPXQXFYCUFXOXPXQXFYCUGXOXP
      XQXFYCUHXRXFYCUKXDXEXJULPZXSXTYAXAUIUMYEXGXKCYHXSXTYAXAUNZUMXSYCYFYGHZYDX
      SYCYJHZHZYDOZCXDCXDKZYMXSYBBXDSZHZYJHZHZXGBXDIJZKZOYRXGXDBIJZYSYRXTXGUUAK
      ZYQXTXSXTYAYOYJUOUPYRXOXPXQXFYFXDBSZXTUUBOXOXPXQXFYQUFZXOXPXQXFYQUGZXOXPX
      QXFYQUHXRXFYQUKXSYPYFYGUQZYRBXDXSYBYOYJUNQZXDXEBXJRTURYRXOXPYFUUCUUAYSKUU
      DUUEUUFUUGXDBXJUSPUTYNYLYRYDYTYNYKYQXSYNYCYPYJYNXAYOYBCXDBVAVBVCVBYNXBYSX
      GCXDBIVKVDVEVFYLCXDSZYDXSYKUUHYDXSYKUUHUEZXGCXDIJZCBIJZXBUUIXGXDCIJZUUJUU
      IYAXGUULKZUUIXSYCYAXSYKUUHWAXSYCYJUUHVLZYIVGUUIXOXPXQXFYGXDCSZYAUUMOXOXPX
      QXFYKUUHVHZXOXPXQXFYKUUHVIZXOXPXQXFYKUUHVJXRXFYKUUHVMYFYGYCXSUUHVNZUUICXD
      XSYKUUHWBZQZXDXECXJRTURUUIXOXPYGUUOUULUUJKUUPUUQUURUUTXDCXJUSPUTZUUIBUUJG
      ZUUJUUKKZUUIBXGUUJUUIXTYAXAUUNVOUVAVPUUIXOYGXPUUHYFCBSZUVBUVCOUUPUURUUQUU
      SYFYGYCXSUUHVQZUUIBCYBXAYJXSUUHVRQZCXDBXJRTURUUIXOYGYFUVDUUKXBKUUPUURUVEU
      VFCBXJUSPVSWCVTWDWEWFWGXHXMYCXCYDXHWTYBXAXHWRXTWSYAAXGBWHAXGCWHWIVCAXGXBW
      JVEWKWLWCWMWNWOWP $.
  $}

  ${
    $d N n $.  $d n p $.  $d N p $.  $d n q $.  $d N q $.  $d P n $.  $d P p $.
    $d p q $.  $d P q $.  $d P x $.  $d Q n $.  $d Q p $.  $d Q q $.  $d Q x $.
    $( There is a line through any two distinct points.  Hilbert's axiom I.1
       for geometry.  (Contributed by Scott Fenton, 29-Oct-2013.)  (Revised by
       Mario Carneiro, 19-Apr-2014.) $)
    hilbert1.1 $p |- ( ( N e. NN /\
       ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ P =/= Q ) ) ->
       E. x e. LinesEE ( P e. x /\ Q e. x ) ) $=
      ( vp vq vn cn wcel cee cfv wne wa cline2 co clines2 cv wrex wceq anbi12d
      simp1 simp2 simp3 eqidd neeq1 oveq1 neeq2 oveq2 rspc2ev syl112anc rexeqdv
      w3a eqeq2d fveq2 rexeqbidv rspcev sylan2 sylibr linerflx1 linerflx2 eleq2
      ellines syl12anc ) DHIZBDJKZIZCVEIZBCLZULZMZBCNOZPIZBVKIZCVKIZBAQZIZCVOIZ
      MZAPRVJEQZFQZLZVKVSVTNOZSZMZFGQZJKZRZEWFRZGHRZVLVIVDWDFVERZEVERZWIVIVFVGV
      HVKVKSZWKVFVGVHUAVFVGVHUBVFVGVHUCVIVKUDWDVHWLMBVTLZVKBVTNOZSZMEFBCVEVEVSB
      SZWAWMWCWOVSBVTUEWPWBWNVKVSBVTNUFUMTVTCSZWMVHWOWLVTCBUGWQWNVKVKVTCBNUHUMT
      UIUJWHWKGDHWEDSZWGWJEWFVEWEDJUNZWRWDFWFVEWSUKUOUPUQVKGFEVBURBCDUSBCDUTVRV
      MVNMAVKPVOVKSVPVMVQVNVOVKBVAVOVKCVATUPVC $.
  $}

  ${
    $d P x $.  $d P y $.  $d Q x $.  $d Q y $.  $d x y $.
    $( There is at most one line through any two distinct points.  Hilbert's
       axiom I.2 for geometry.  (Contributed by Scott Fenton, 29-Oct-2013.)
       (Revised by NM, 17-Jun-2017.) $)
    hilbert1.2 $p |- ( P =/= Q -> E* x e. LinesEE ( P e. x /\ Q e. x ) ) $=
      ( vy wne cv wcel wa weq wi clines2 wral wceq simprl simprr simpl linethru
      syl3anc ex eleq2w wrmo an4 cline2 co anim12d syl6 biimtrid expd ralrimivv
      eqtr3 anbi12d rmo4 sylibr ) BCEZBAFZGZCUOGZHZBDFZGZCUSGZHZHZADIZJZDKLAKLU
      RAKUAUNVEADKKUNUOKGZUSKGZHZVCVDVHVCHVFURHZVGVBHZHZUNVDVFVGURVBUBUNVKUOBCU
      CUDZMZUSVLMZHVDUNVIVMVJVNUNVIVMUNVIHVFURUNVMUNVFURNUNVFUROUNVIPUOBCQRSUNV
      JVNUNVJHVGVBUNVNUNVGVBNUNVGVBOUNVJPUSBCQRSUEUOUSVLUJUFUGUHUIURVBADKVDUPUT
      UQVAADBTADCTUKULUM $.
  $}

  ${
    $d P x $.  $d Q x $.
    $( There is a unique line going through any two distinct points.  Theorem
       6.19 of [Schwabhauser] p. 46.  (Contributed by Scott Fenton,
       29-Oct-2013.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
    linethrueu $p |- ( ( N e. NN /\
       ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ P =/= Q ) ) ->
       E! x e. LinesEE ( P e. x /\ Q e. x ) ) $=
      ( cn wcel cee cfv wne w3a wa clines2 wrex wrmo wreu hilbert1.1 hilbert1.2
      cv simpr3 syl reu5 sylanbrc ) DEFZBDGHZFZCUDFZBCIZJKZBARZFCUIFKZALMUJALNZ
      UJALOABCDPUHUGUKUCUEUFUGSABCQTUJALUAUB $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( Two distinct lines intersect in at most one point.  Theorem 6.21 of
       [Schwabhauser] p. 46.  (Contributed by Scott Fenton, 29-Oct-2013.)
       (Revised by Mario Carneiro, 19-Apr-2014.) $)
    lineintmo $p |- ( ( A e. LinesEE /\ B e. LinesEE /\ A =/= B ) ->
       E* x ( x e. A /\ x e. B ) ) $=
      ( vy clines2 wcel wne w3a cv wa weq wi wal wmo an4 wceq linethru 3expa ex
      eleq1w cline2 co eqtr3 syl2an anandirs necon1d an4s com23 3impia alrimivv
      sylan2b anbi12d mo4 sylibr ) BEFZCEFZBCGZHZAIZBFZUSCFZJZDIZBFZVCCFZJZJZAD
      KZLZDMAMVBANURVIADUOUPUQVIUOUPJZVGUQVHVJVGUQVHLZVGVJUTVDJZVAVEJZJVKUTVAVD
      VEOUOVLUPVMVKUOVLJZUPVMJZJZUSVCBCVPUSVCGZBCPZVNVOVQVRVNVQJBUSVCUAUBZPZCVS
      PZVRVOVQJUOVLVQVTBUSVCQRUPVMVQWACUSVCQRBCVSUCUDUESUFUGUKSUHUIUJVBVFADVHUT
      VDVAVEADBTADCTULUMUN $.
  $}

  $(
  @{
    @d a n @.  @d a p @.  @d a q @.  @d n p @.  @d n q @.  @d P a @.  @d P n @.
    @d P p @.  @d p q @.  @d P q @.  @d p x @.  @d P x @.  @d Q a @.  @d Q n @.
    @d Q p @.  @d Q q @.  @d q x @.  @d Q x @.  @d R a @.  @d R n @.  @d R p @.
    @d R q @.  @d R x @.
    @( Three points are colinear iff there is a line through all three of
       them.  Theorem 6.23 of [Schwabhauser] p. 46.  (Contributed by Scott
       Fenton, 7-Nov-2013). @)
    colinline @p |- ( ( Q e. V /\ R e. W ) -> ( P Colinear <. Q , R >. <->
          E. a e. LinesEE ( P e. a /\ Q e. a /\ R e. a ) ) ) @=
      ( vp vq vn vx wcel wa cop ccolin wbr cv w3a clines2 wrex wne cline2 co
      wceq cee cfv cn wi ellines df-3an cab fvline eqeq2d cvv eleq2 3anbi123d
      breq1 eqid elab4g 3anbi123i bitrdi pm5.32i 3an6 biimtrid adantld expd
      sylbid sylan2br expr impd anassrs rexlimdva rexlimivv sylbi rexlimiv
      impbid1 ) BDKCEKLABCMNOZAFPZKZBVQKZCVQKZQZFRS?WAVPFRVQRKGPZHPZTZVQWBWCUAU
      BZUCZLZHIPZUDUEZSZGWISIUFSWAVPUGZVQIHGUHWJWKIGUFWIWHUFKZWBWIKZLWGWKHWIWLW
      MWCWIKZWGWKUGWLWMWNLZLWDWFWKWLWOWDWFWKUGZWOWDLWLWMWNWDQZWPWMWNWDUIWLWQLZW
      FVQJPZWBWCMZNOZJUJZUCZWKWRWEXBVQJWBWCWHUKULWRXCWAVPXCWALXCAUMKZAWTNOZLZBU
      MKZBWTNOZLZCUMKZCWTNOZLZQZLWRVPXCWAXMXCWAAXBKZBXBKZCXBKZQXMXCVRXNVSXOVTXP
      VQXBAUNVQXBBUNVQXBCUNUOXNXFXOXIXPXLXAXEJAXBWSAWTNUPXBUQZURXAXHJBXBWSBWTNU
      PXQURXAXKJCXBWSCWTNUPXQURUSUTVAWRXMVPXCXMXDXGXJQXEXHXKQLWRVPXDXEXGXHXJXKV
      B?VCVDVCVEVFVGVHVIVJVKVLVMVNVO @.
      @( [19-Apr-2014] @) @( [7-Nov-2013] @)
  @}
  $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Forward difference
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the constant for the forward difference operator. $)
  $c _/_\ $.

  $( Declare the syntax for the forward difference operator. $)
  cfwddif $a class _/_\ $.

  ${
    $d f x y $.
    $( Define the forward difference operator.  This is a discrete analogue of
       the derivative operator.  Definition 2.42 of [GramKnuthPat], p. 47.
       (Contributed by Scott Fenton, 18-May-2020.) $)
    df-fwddif $a |- _/_\ = ( f e. ( CC ^pm CC ) |->
       ( x e. { y e. dom f | ( y + 1 ) e. dom f } |->
       ( ( f ` ( x + 1 ) ) - ( f ` x ) ) ) ) $.
  $}

  $( Declare the constant for the nth forward difference operator. $)
  $c _/_\^n $.

  $( Declare the syntax for the nth forward difference operator. $)
  cfwddifn $a class _/_\^n $.

  ${
    $d n f x y k $.
    $( Define the nth forward difference operator.  This works out to be the
       forward difference operator iterated ` n ` times.  (Contributed by Scott
       Fenton, 28-May-2020.) $)
    df-fwddifn $a |- _/_\^n = ( n e. NN0 , f e. ( CC ^pm CC ) |->
        ( x e. { y e. CC | A. k e. ( 0 ... n ) ( y + k ) e. dom f } |->
          sum_ k e. ( 0 ... n )
          ( ( n _C k ) x. ( ( -u 1 ^ ( n - k ) ) x. ( f ` ( x + k ) ) ) ) ) )
          $.
  $}

  ${
    $d F x y f $.  $d X x y f $.  $d A x y f $.  $d ph x y f $.
    fwddifval.1 $e |- ( ph -> A C_ CC ) $.
    fwddifval.2 $e |- ( ph -> F : A --> CC ) $.
    fwddifval.3 $e |- ( ph -> X e. A ) $.
    fwddifval.4 $e |- ( ph -> ( X + 1 ) e. A ) $.
    $( Calculate the value of the forward difference operator at a point.
       (Contributed by Scott Fenton, 18-May-2020.) $)
    fwddifval $p |- ( ph ->
     ( ( _/_\ ` F ) ` X ) = ( ( F ` ( X + 1 ) ) - ( F ` X ) ) ) $=
      ( vx vy vf c1 caddc co cfv cmin wcel cvv cc wceq cv crab cfwddif cdm cmpt
      cpm df-fwddif dmeq eleq2d rabeqbidv fveq1 oveq12d mpteq12dv wf wss elpm2r
      wa cnex mpanl12 syl2anc fdmd a1i ssexd eqeltrd rabexg mptexg 3syl fvmptd3
      mpteq1d eqtrd fvoveq1 fveq2 adantl oveq1 eleq1d elrab sylanbrc fvmptd
      ovexd ) AIDIUAZLMNZCOZVTCOZPNZDLMNZCOZDCOZPNZJUAZLMNZBQZJBUBZCUCOZRAWMIWJ
      CUDZQZJWNUBZWDUEZIWLWDUEAKCIWJKUAZUDZQZJWSUBZWAWROZVTWROZPNZUEWQSSUFNZUCR
      IJKUGWRCTZIXAXDWPWDXFWTWOJWSWNWRCUHZXFWSWNWJXGUIUJXFXBWBXCWCPWAWRCUKVTWRC
      UKULUMABSCUNZBSUOZCXEQZFESRQZXKXHXIUQXJURURSSBCRRUPUSUTAWNRQWPRQWQRQAWNBR
      ABSCFVAZABSRXKAURVBEVCVDWOJWNRVEIWPWDRVFVGVHAIWPWLWDAWOWKJWNBXLAWNBWJXLUI
      UJVIVJVTDTZWDWHTAXMWBWFWCWGPVTDLCMVKVTDCVLULVMADBQWEBQZDWLQGHWKXNJDBWIDTW
      JWEBWIDLMVNVOVPVQAWFWGPVSVR $.
  $}

  ${
    $d N n f k x y $.  $d A n f k x y $.  $d X n f k x y $.  $d F n f k x y $.
    $d ph n f k x y $.
    fwddifnval.1 $e |- ( ph -> N e. NN0 ) $.
    fwddifnval.2 $e |- ( ph -> A C_ CC ) $.
    fwddifnval.3 $e |- ( ph -> F : A --> CC ) $.
    fwddifnval.4 $e |- ( ph -> X e. CC ) $.
    fwddifnval.5 $e |- ( ( ph /\ k e. ( 0 ... N ) ) -> ( X + k ) e. A ) $.
    $( The value of the forward difference operator at a point.  (Contributed
       by Scott Fenton, 28-May-2020.) $)
    fwddifnval $p |- ( ph -> ( ( N _/_\^n F ) ` X ) =
       sum_ k e. ( 0 ... N )
       ( ( N _C k ) x. ( ( -u 1 ^ ( N - k ) ) x. ( F ` ( X + k ) ) ) ) ) $=
      ( vx vy co cv cmul wcel cc cvv wceq vn vf cc0 cfz c1 cneg cmin cexp caddc
      cbc cfv csu cdm wral crab cfwddifn cn0 cpm cmpt cmpo df-fwddifn a1i oveq2
      wa adantr wb eleq2d adantl raleqbidv rabbidv oveq1 oveq2d fveq1 oveqan12d
      dmeq oveq12d sumeq12dv mpteq12dv wss cnex elpm2r mpanl12 syl2anc mptrabex
      wf ovmpod fvoveq1 sumeq2sdv fdmd eleqtrrd ralrimiva eleq1d elrab sylanbrc
      ralbidv sumex fvmptd ) ALFUCEUDNZECOZUJNZUEUFZEWSUGNZUHNZLOZWSUINZDUKZPNZ
      PNZCULZWRWTXCFWSUINZDUKZPNZPNZCULZMOZWSUINZDUMZQZCWRUNZMRUOZEDUPNSAUAUBED
      UQRRURNZLXPUBOZUMZQZCUCUAOZUDNZUNZMRUOZYFYEWSUJNZXAYEWSUGNZUHNZXEYBUKZPNZ
      PNZCULZUSZLXTXIUSZUPSUPUAUBUQYAYPUTTALMUBCUAVAVBYEETZYBDTZVDZYPYQTAYTLYHY
      OXTXIYTYGXSMRYTYDXRCYFWRYRYFWRTYSYEEUCUDVCVEZYSYDXRVFYRYSYCXQXPYBDVOVGVHV
      IVJYTYFWRYNXHCUUAYTYNXHTWSYFQYTYIWTYMXGPYRYIWTTYSYEEWSUJVKVEYRYSYKXCYLXFP
      YRYJXBXAUHYEEWSUGVKVLXEYBDVMVNVPVEVQVRVHGABRDWEZBRVSZDYAQZIHRSQZUUEUUBUUC
      VDUUDVTVTRRBDSSWAWBWCYQSQAXSLMRXIVTWDVBWFXDFTZXIXNTAUUFWRXHXMCUUFXGXLWTPU
      UFXFXKXCPXDFWSDUIWGVLVLWHVHAFRQXJXQQZCWRUNZFXTQJAUUGCWRAWSWRQZVDXJBXQKAXQ
      BTUUIABRDIWIVEWJWKXSUUHMFRXOFTZXRUUGCWRUUJXPXJXQXOFWSUIVKWLWOWMWNXNSQAWRX
      MCWPVBWQ $.
  $}

  ${
    $d A k $.  $d F k $.  $d X k $.  $d ph k $.
    fwddifn0.1 $e |- ( ph -> A C_ CC ) $.
    fwddifn0.2 $e |- ( ph -> F : A --> CC ) $.
    fwddifn0.3 $e |- ( ph -> X e. A ) $.
    $( The value of the n-iterated forward difference operator at zero is just
       the function value.  (Contributed by Scott Fenton, 28-May-2020.) $)
    fwddifn0 $p |- ( ph -> ( ( 0 _/_\^n F ) ` X ) = ( F ` X ) ) $=
      ( vk cc0 co cfv cbc c1 cmin cexp cmul wcel cc wceq eqtrd cfwddifn cv cneg
      cfz caddc csu cn0 0nn0 a1i sseldd csn cz 0z fzsn ax-mp eleq2i velsn bitri
      wa oveq2 adantl addridd eqeltrd adantr fwddifnval fveq2d oveq2d ffvelcdmd
      sylan2b mullidd bcnn eqtrdi 0m0e0 neg1cn exp0 oveq12d fsum1 sylancr ) ADI
      CUAJKIIUDJZIHUBZLJZMUCZIVTNJZOJZDVTUEJZCKZPJZPJZHUFZDCKZABHCIDIUGQZAUHUIE
      FABRDEGUJZVTVSQZAVTISZWEBQWMVTIUKZQWNVSWOVTIULQZVSWOSUMIUNUOUPHIUQURAWNUS
      WEDIUEJZBWNWEWQSAVTIDUEUTZVAAWQBQWNAWQDBADWLVBZGVCVDVCVIVEAWIMMWQCKZPJZPJ
      ZWJAWPXBRQWIXBSUMAXBWJRAXBMWJPJZWJAXAWJMPAXAXCWJAWTWJMPAWQDCWSVFVGAWJABRD
      CFGVHZVJZTVGXETZXDVCWHXBHIWNWAMWGXAPWNWAIILJZMVTIILUTWKXGMSUHIVKUOVLWNWDM
      WFWTPWNWDWBIOJZMWNWCIWBOWNWCIINJIVTIINUTVMVLVGWBRQXHMSVNWBVOUOVLWNWEWQCWR
      VFVPVPVQVRXFTT $.
  $}

  ${
    $d A k j $.  $d F k j $.  $d X k j $.  $d N k j $.  $d ph k j $.
    fwddifnp1.1 $e |- ( ph -> N e. NN0 ) $.
    fwddifnp1.2 $e |- ( ph -> A C_ CC ) $.
    fwddifnp1.3 $e |- ( ph -> F : A --> CC ) $.
    fwddifnp1.4 $e |- ( ph -> X e. CC ) $.
    fwddifnp1.5 $e |- ( ( ph /\ k e. ( 0 ... ( N + 1 ) ) ) ->
     ( X + k ) e. A ) $.
    $( The value of the n-iterated forward difference at a successor.
       (Contributed by Scott Fenton, 28-May-2020.) $)
    fwddifnp1 $p |- ( ph -> ( ( ( N + 1 ) _/_\^n F ) ` X ) =
      ( ( ( N _/_\^n F ) ` ( X + 1 ) ) - ( ( N _/_\^n F ) ` X ) ) ) $=
      ( cc0 c1 caddc co cmin cmul wcel cz oveq2d cfz cbc cneg cexp cfv cfwddifn
      vj csu cn0 wceq elfzelz bcpasc syl2an oveq1d bccl nn0cnd peano2zm addcomd
      cv wa syl peano2nn0 nn0zd zsubcl m1expcl zcnd cc adantr ffvelcdmd adddird
      wf mulcld eqtrd adantl subsub3d eqcomd addsubd neg1cn a1i neg1ne0 expp1zd
      1cnd wne mulcomd mulm1d 3eqtrd mulneg1d mulneg2d oveq12d negsubd sumeq2dv
      eqtr3d fzfid fsumsub cuz nn0uz eleqtrdi oveq1 fveq2d fsum1p df-neg oveq2i
      oveq2 bcneg1 eqtr3id 0z 1z mp2an zsubcld eluzfz1 ralrimiva eleq1d syl2anc
      wral rspcva mul02d wo olc wb elfzp12 biimpar sylan2 syldan fsumcl addlidd
      ppncand 1zzd 0zd addassd fzp1elp1 rspccv imp eqeltrd fsumshft weq cbvsumv
      wi eqtr3di cfa fwddifnval 3eqtr2d fsump1 cdiv cif fzp1nel iffalsei eqtrdi
      bcval eluzfz2 sylc fzelp1 addridd peano2cn anbi2d imbi12d chvarvv 3eqtr4d
      rspcv ) ALEMNOZUAOZUUSCUSZUBOZMUCZUUSUVAPOZUDOZFUVANOZDUEZQOZQOZCUHZLEUAO
      ZEUVAUBOZUVCEUVAPOZUDOZFMNOZUVANOZDUEZQOZQOZCUHZUVKUVLUVNUVGQOZQOZCUHZPOZ
      FUUSDUFOUEUVOEDUFOZUEZFUWEUEZPOAUVJUUTEUVAMPOZUBOZUVCEUWHPOZUDOZUVGQOZQOZ
      UWBPOZCUHUUTUWMCUHZUUTUWBCUHZPOUWDAUUTUVIUWNCAUVAUUTRZUTZUVLUWINOZUVHQOZU
      VIUWNUWRUWSUVBUVHQAEUIRZUVASRZUWSUVBUJUWQGUVALUUSUKZUVAEULUMUNUWRUWTUWIUV
      HQOZUVLUVHQOZNOZUWMUWBUCZNOUWNUWRUWTUWIUVLNOZUVHQOUXFUWRUWSUXHUVHQUWRUVLU
      WIUWRUVLAUXAUXBUVLUIRUWQGUXCUVAEUOUMUPZUWRUWIAUXAUWHSRZUWIUIRUWQGUWQUXBUX
      JUXCUVAUQVAZUWHEUOUMUPZURUNUWRUWIUVLUVHUXLUXIUWRUVEUVGUWRUVEUWRUVDSRZUVES
      RAUUSSRZUXBUXMUWQAUUSAUXAUUSUIRGEVBVAZVCZUXCUUSUVAVDUMUVDVEVAVFUWRBVGUVFD
      ABVGDVKZUWQIVHKVIZVLVJVMUWRUXDUWMUXEUXGNUWRUVHUWLUWIQUWRUVEUWKUVGQUWRUVDU
      WJUVCUDUWRUWJUVDUWREUVAMUWREAUXAUWQGVHUPZUWRUVAUWQUXBAUXCVNVFZUWRWBZVOVPT
      UNTUWRUXEUVLUWAUCZQOUXGUWRUVHUYBUVLQUWRUVHUVNUCZUVGQOUYBUWRUVEUYCUVGQUWRU
      VEUVNUVCQOZUVCUVNQOUYCUWRUVEUVCUVMMNOZUDOUYDUWRUVDUYEUVCUDUWREMUVAUXSUYAU
      XTVQTUWRUVCUVMUVCVGRUWRVRVSZUVCLWCUWRVTVSAESRZUXBUVMSRZUWQAEGVCZUXCEUVAVD
      UMZWAVMUWRUVNUVCUWRUVNUWRUYHUVNSRUYJUVMVEVAVFZUYFWDUWRUVNUYKWEWFUNUWRUVNU
      VGUYKUXRWGVMTUWRUVLUWAUXIUWRUVNUVGUYKUXRVLZWHVMWIUWRUWMUWBUWRUWIUWLUXLUWR
      UWKUVGUWRUWKUWRUWJSRZUWKSRAUYGUXJUYMUWQUYIUXKEUWHVDUMUWJVEVAVFUXRVLVLZUWR
      UVLUWAUXIUYLVLZWJWFWLWKAUUTUWMUWBCALUUSWMUYNUYOWNAUWOUVTUWPUWCPAUWOLMNOZU
      USUAOZUWMCUHZUYQUWIUWKUVOUWHNOZDUEZQOZQOZCUHZUVTAUWOELMPOZUBOZUVCEVUDPOZU
      DOZFLNOZDUEZQOZQOZUYRNOLUYRNOUYRAUWMVUKCLUUSAUUSUILWOUEZUXOWPWQZUYNUVALUJ
      ZUWIVUEUWLVUJQVUNUWHVUDEUBUVALMPWRZTVUNUWKVUGUVGVUIQVUNUWJVUFUVCUDVUNUWHV
      UDEPVUOTTVUNUVFVUHDUVALFNXCZWSWIWIWTAVUKLUYRNAVUKLVUJQOLAVUELVUJQAVUEEUVC
      UBOZLUVCVUDEUBMXAXBAUXAVUQLUJGEXDVAXEUNAVUJAVUGVUIAVUGAVUFSRVUGSRAEVUDUYI
      VUDSRZALSRMSRVURXFXGLMVDXHVSXIVUFVEVAVFABVGVUHDIALUUTRZUVFBRZCUUTXNZVUHBR
      ZAUUSVULRZVUSVUMLUUSXJVAAVUTCUUTKXKZVUTVVBCLUUTVUNUVFVUHBVUPXLXOXMVIVLXPV
      MUNAUYRAUYQUWMCAUYPUUSWMAUVAUYQRZUWQUWMVGRVVEAVUNVVEXQZUWQVVEVUNXRAUWQVVF
      AVVCUWQVVFXSVUMUVALUUSXTVAYAYBUYNYCYDYEWFAUYQVUBUWMCAVVEUTZVUAUWLUWIQVVGU
      YTUVGUWKQVVGUYSUVFDVVGFMUVAAFVGRZVVEJVHVVGWBVVEUVAVGRZAVVEUVAUVAUYPUUSUKV
      FVNYFWSTTWKAUVKEUGUSZUBOZUVCEVVJPOZUDOZUVOVVJNOZDUEZQOZQOZUGUHVUCUVTAVVQV
      UBUGCMLEAYGAYHUYIAVVJUVKRZUTZVVKVVPAUXAVVJSRZVVKVGRVVRGVVJLEUKZUXAVVTUTVV
      KVVJEUOUPUMVVSVVMVVOVVSVVMVVSVVLSRZVVMSRAUYGVVTVWBVVRUYIVWAEVVJVDUMVVLVEV
      AVFVVSBVGVVNDAUXQVVRIVHVVSVVNFVVJMNOZNOZBVVSVVNFMVVJNOZNOVWDVVSFMVVJAVVHV
      VRJVHVVSWBZVVRVVJVGRAVVRVVJVWAVFVNZYIVVSVWEVWCFNVVSMVVJVWFVWGURTVMVVRAVWC
      UUTRZVWDBRZVVJLEYJAVWHVWIAVVAVWHVWIYQVVDVUTVWICVWCUUTUVAVWCUJUVFVWDBUVAVW
      CFNXCXLYKVAYLZYBYMVIVLVLVVJUWHUJZVVKUWIVVPVUAQVVJUWHEUBXCVWKVVMUWKVVOUYTQ
      VWKVVLUWJUVCUDVVJUWHEPXCTVWKVVNUYSDVVJUWHUVONXCWSWIWIYNUVKVVQUVSUGCUGCYOZ
      VVKUVLVVPUVRQVVJUVAEUBXCVWLVVMUVNVVOUVQQVWLVVLUVMUVCUDVVJUVAEPXCTVWLVVNUV
      PDVVJUVAUVONXCWSWIWIYPYRUUAAUWPUWCEUUSUBOZUVCEUUSPOZUDOZFUUSNOZDUEZQOZQOZ
      NOUWCLNOUWCAUWBVWSCLEAEUIVULGWPWQUYOUVAUUSUJZUVLVWMUWAVWRQUVAUUSEUBXCVWTU
      VNVWOUVGVWQQVWTUVMVWNUVCUDUVAUUSEPXCTVWTUVFVWPDUVAUUSFNXCZWSWIWIUUBAVWSLU
      WCNAVWSLVWRQOLAVWMLVWRQAVWMUUSUVKRZEYSUEVWNYSUEUUSYSUEQOUUCOZLUUDZLAUXAUX
      NVWMVXDUJGUXPUUSEUUHXMVXBVXCLLEUUEUUFUUGUNAVWRAVWOVWQAVWNSRZVWOVGRAEUUSUY
      IUXPXIVXEVWOVWNVEVFVAABVGVWPDIAUUSUUTRZVVAVWPBRZAVVCVXFVUMLUUSUUIVAVVDVUT
      VXGCUUSUUTVWTUVFVWPBVXAXLUURUUJVIVLXPVMTAUWCAUVKUWBCALEWMUVAUVKRZAUWQUWBV
      GRUVALEUUKZUYOYBYDUULWFWIWFABCDUUSFUXOHIJKYTAUWFUVTUWGUWCPABCDEUVOGHIAVVH
      UVOVGRJFUUMVAAVXHUTZUVPFUVAMNOZNOZBVXJUVPFMUVANOZNOVXLVXJFMUVAAVVHVXHJVHV
      XJWBZVXHVVIAVXHUVAUVALEUKVFVNZYIVXJVXMVXKFNVXJMUVAVXNVXOURTVMVXHAVXKUUTRZ
      VXLBRZUVALEYJAVWHUTZVWIYQAVXPUTZVXQYQUGCVWLVXRVXSVWIVXQVWLVWHVXPAVWLVWCVX
      KUUTVVJUVAMNWRZXLUUNVWLVWDVXLBVWLVWCVXKFNVXTTXLUUOVWJUUPYBYMYTABCDEFGHIJV
      XHAUWQVUTVXIKYBYTWIUUQ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Rank theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( The rank of the empty set is ` (/) ` .  (Contributed by Scott Fenton,
     17-Jul-2015.) $)
  rank0 $p |- ( rank ` (/) ) = (/) $=
    ( c0 wceq crnk cfv eqid 0ex rankeq0 mpbi ) AABACDABAEAFGH $.

  ${
    $d A x $.  $d x y $.
    $( The only set with rank ` 1o ` is the singleton of the empty set.
       (Contributed by Scott Fenton, 17-Jul-2015.) $)
    rankeq1o $p |- ( ( rank ` A ) = 1o <-> A = { (/) } ) $=
      ( vx vy crnk cfv c1o wceq c0 cvv wcel wne mpbiri wi csuc con0 ax-mp pweqi
      cr1 cpw sylbi csn 1n0 neeq1 neneqd fvprc nsyl2 cv fveqeq2 imbi12d rankeq0
      eqeq1 vex necon3bii sylibr crab cint rankval eqeq1i cpr wa wss elirr 1oex
      ssrab2 id eleqtrid inteq int0 eqtrdi eqeq1d mtbiri necon2ai onint sylancr
      mto eleq1 mpbid suceq fveq2d df-1o fveq2i 0elon r1suc r10 pw0 3eqtrri 1on
      3eqtri pwpw0 eqtr4i eqtr4di eleq2d elrab sylib wo df-ne orel1 df1o2 eqeq2
      elpr wn eqcomd syl6com adantl syl mpd vtoclg mpcom fveq2 cdm wf1 eleqtrri
      r111 f1dm rankonid mpbi impbii eqeq2i bitri ) ADEZFGZAFGZAHUAZGYAYBAIJZYA
      YBYAXTHGYDYAXTHYAXTHKFHKZUBXTFHUCLUDADUEUFBUGZDEZFGZYFFGZMYAYBMBAIYFAGYHY
      AYIYBYFAFDUHYFAFUKUIYHYFHKZYIYHYGHKZYJYHYKYEUBYGFHUCLYFHYGHYFBULZUJUMUNYH
      YFCUGZNZREZJZCOUOZUPZFGZYJYIMZYGYRFCYFYLUQURYSFOJZYFHYCUSZJZUTZYTYSFYQJZU
      UDYSYRYQJZUUEYSYQOVAYQHKUUFYPCOVDYSYQHYQHGZYSIFGZUUHFFJFVBUUHFIFVCUUHVEVF
      VOUUGYRIFUUGYRHUPIYQHVGVHVIVJVKVLYQVMVNYRFYQVPVQYPUUCCFOYMFGZYOUUBYFUUIYO
      FNZREZUUBUUIYNUUJRYMFVRVSUUBFREZSZUUKUUMHSZSYCSUUBUULUUNUULHNZREZHREZSZUU
      NFUUORVTWAHOJUUPUURGWBHWCPUUQHWDQWHQUUNYCWEQWIWFUUAUUKUUMGWGFWCPWJWKWLWMW
      NUUCYTUUAUUCYFHGZYFYCGZWOZYTYFHYCYLWTYJUVAUUTYIYJUUSXAUVAUUTMYFHWPUUSUUTW
      QTUUTFYFUUTFYFGFYCGWRYFYCFWSLXBXCTXDXETXFXGXHYBXTFDEZFAFDXIFRXJZJUVBFGFOU
      VCWGOIRXKUVCOGXMOIRXNPXLFXOXPVIXQFYCAWRXRXS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Hereditarily Finite Sets
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.
    $( The class of all hereditarily finite sets is transitive.  (Contributed
       by Scott Fenton, 16-Jul-2015.) $)
    hftr $p |- Tr Hf $=
      ( vx vy chf wtr wel cv wcel wa wi wal dftr2 hfelhf ax-gen mpgbir ) CDABEB
      FZCGHAFZCGIZBJAABCKQBPOLMN $.
  $}

  ${
    $d A x $.  $d B x $.
    $( Extensionality for HF sets depends only on comparison of HF elements.
       (Contributed by Scott Fenton, 16-Jul-2015.) $)
    hfext $p |- ( ( A e. Hf /\ B e. Hf ) ->
       ( A = B <-> A. x e. Hf ( x e. A <-> x e. B ) ) ) $=
      ( chf wcel wa wceq cv wb wral cvv cdif wal dfcleq unvdif raleqi wn hfelhf
      cun stoic1b ralv bitr2i ralunb 3bitri vex mpbiran adantlr adantll 2falsed
      eldif sylan2b ralrimiva biantrud bitr4id ) BDEZCDEZFZBCGZAHZBEZUSCEZIZADJ
      ZVBAKDLZJZFZVCURVBAMZVBADVDSZJZVFABCNVIVBAKJVGVBAVHKDOPVBAUAUBVBADVDUCUDU
      QVEVCUQVBAVDUSVDEZUQUSDEZQZVBVJUSKEVLAUEUSKDUJUFUQVLFUTVAUOVLUTQUPUTUOVKU
      SBRTUGUPVLVAQUOVAUPVKUSCRTUHUIUKULUMUN $.
  $}

  $( ` _om ` is not hereditarily finite.  (Contributed by Scott Fenton,
     16-Jul-2015.) $)
  hfninf $p |- -. _om e. Hf $=
    ( com chf wcel wn wi elirr crnk cfv elhf2g con0 wceq ordom elong mpbiri cr1
    word cdm cvv wf1 ax-mp r111 f1dm eleq2i rankonid bitr3i sylib eleq1d mtbiri
    bitrd pm2.01 ) ABCZUKDZEULUKUKAACZAFUKUKAGHZACUMABIUKUNAAUKAJCZUNAKZUKUOAPL
    ABMNUOAOQZCUPUQJAJROSUQJKUAJROUBTUCAUDUEUFUGUIUHUKUJT $.

  $(
  @{ @d t y @. @d t z @. @d x y @.
     @( The hereditarily finite sets are a subset of the finite sets. @)
     hfssfin @p |- Hf C_ Fin @=
       ( vx vy vt vz cr1 com cfn wss cv wcel cfv wceq con0 cvv fveq2 sseq1d weq
       c0 eqsstri syl chf cima cuni df-hf wral wrex wfun wf1 r111 f1fun fvelima
       ax-mp mpan wi csuc r10 0ss cpw r1suc sylibrd finds sseq1 biimpd rexlimiv
       nnon com12 rgen unissb mpbir ) UAEFUBZUCZGUDVKGHAIZGHZAVJUEVMAVJVLVJJZBI
       ZEKZVLLZBFUFZVMEUGZVNVRMNEUHVSUIMNEUJULBVLFEUKUMVQVMBFVOFJVPGHZVQVMUNCIZ
       EKZGHREKZGHDIZEKZGHZWDUOZEKZGHZVTCDVOWARLWBWCGWAREOPCDQWBWEGWAWDEOPWAWGL
       WBWHGWAWGEOPCBQWBVPGWAVOEOPWCRGUPGUQSWDFJZWFWEURZGHWI?WJWHWKGWJWDMJWHWKL
       WDVEWDUSTPUTVAVQVTVMVQVTVMVPVLGVBVCVFTVDTVGAVJGVHVIS @.
       @( [20-Jul-2015] @)

     @( Any finite set of HF sets is itself an HF set. @)
     hffinhf @p |- ( ( A C_ Hf /\ A e. Fin ) -> A e. Hf ) @= ? @.

  @}

  @{ @d A z @. @d x z @. @d y z @. @d A a @. @d a b @. @d A b @. @d a c @.
     @d A c @. @d a w @. @d A w @. @d a x @. @d a y @. @d a z @. @d b c @.
     @d b x @. @d b y @. @d b z @. @d c x @. @d c y @. @d c z @. @d w x @.
     @d w y @. @d w z @.

     @( Induction rule for hereditarily finite sets.  If the empty class
        is in a class ` A ` , and ` A ` is closed under adjunction of HF sets,
        then all HF sets are elements of ` A ` . @)
     hfind @p |- ( ( (/) e. A /\ A. x e. A A. y e. A ( ( x e. Hf /\ y e. Hf )
           -> ( x u. { y } ) e. A ) ) -> Hf C_ A ) @=
       ( vz vw va vb vc c0 wcel cv chf wa wi wral crnk cfv com wceq wal csn cun
       wrex risset eqeq1 imbi1d albidv fveq2 eqeq2d eleq1 imbi2d imbi12d cbvalv
       weq bitrdi nn0suc eqcom vex rankeq0 bicomi bitr3i biimprd
       biimtrdi adantrd
       com23 a1dd a1i jaod mpd bi2.04 albii 19.21v bitri ralbii r19.21v 3imtr4g
       a2d alrimdv omsinds sp syl com12 rexlimdv biimtrid elhf2 anbi12i 2ralbii
       imbi1i anbi2i 3imtr4i ssrdv ) ICJZAKZLJZBKZLJZMZWMWOUAUBCJZNZBCOACOZMZDL
       CWLWMPQRJZWOPQRJZMZWRNZBCOACOZMZDKZPQZRJZXHCJZNXAXHLJZXKNXJEKZXISZERUCXG
       XKEXIRUDXGXNXKERXMRJZXGXNXKNXOXNXGXKXOXNXGXKNZNZDTZXQFKZXISZXPNZDTZGKZHK
       ZPQZSZXGYDCJZNZNZHTZXRFGXMFGUNZYBYCXISZXPNZDTYJYKYAYMDYKXTYLXPXSYCXIUEUF
       UGYMYIDHDHUNZYLYFXPYHYNXIYEYCXHYDPUHUIYNXKYGXGXHYDCUJUKULUMUOFEUNZYAXQDY
       OXTXNXPXSXMXIUEUFUGXSRJZYJGXSOZYADYPXGYFYGNZHTZGXSOZNZXGXTXKNZNYQYAYPXGY
       TUUBYP?XGYTUUBNNZ?XSUPYPXSISZUUC?UUDUUCNYPUUDXGUUBYTUUDWLUUBXFUUDXTWLXKU
       UDXTXHISZWLXKNUUDXTIXISZUUEXSIXIUEUUFXIISZUUEXIIUQUUEUUGXHDURZUSUTVAUOUU
       EXKWLXHICUJVBVCVEVDVFVG?VHVIVQYQXGYSNZGXSOUUAYJUUIGXSYJXGYRNZHTUUIYIUUJH
       YFXGYGVJVKXGYRHVLVMVNXGYSGXSVOVMXTXGXKVJVPVRVSXQDVTWAVEWBWCWDWTXFWLWSXEA
       BCCWQXDWRWNXBWPXCWMAURWEWOBURWEWFWHWGWIXLXJXKXHUUHWEWHWJWK @.
       @( [17-Jul-2015] @)
  @}
  $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Natural ordinal operations
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare a new constant $)
  $c .no $.

  $( Declare the syntax for natural multiplication. $)
  cnmul $a class .no $.

  ${
    $d x y z p m a b c d $.
    $( Define natural ordinal multiplication.  This is the corresponding
       operation to ~ df-nadd .  (Contributed by Scott Fenton, 2-Jun-2026.) $)
    df-nmul $a |- .no =
     frecs ( { <. x , y >. | ( x e. ( On X. On ) /\ y e. ( On X. On )
     /\ ( ( ( 1st ` x ) _E ( 1st ` y ) \/ ( 1st ` x ) = ( 1st ` y ) ) /\
          ( ( 2nd ` x ) _E ( 2nd ` y ) \/ ( 2nd ` x ) = ( 2nd ` y ) ) /\
          x =/= y ) ) } , ( On X. On ) ,
          ( p e. _V , m e. _V |->
          [_ ( 1st ` p ) / a ]_ [_ ( 2nd ` p ) / b ]_
          |^| { z e. On | A. c e. a A. d e. b
          ( ( c m b ) +no ( a m d ) ) e. ( z +no ( c m d ) ) } ) ) $.
  $}

  ${
    $d x y z p m a b c d $.
    $( Natural multiplication is a function over pairs of ordinals.
       (Contributed by Scott Fenton, 2-Jun-2026.) $)
    nmulfn $p |- .no Fn ( On X. On ) $=
      ( vx vy vp vm va vb vc vd vz cnmul cvv cv c1st cfv c2nd co cnadd wcel csb
      wral con0 crab cint cmpo df-nmul on2recsfn ) ABJCDKKECLZMNFUGONGLZFLZDLZP
      ELZHLZUJPQPILUHULUJPQPRHUITGUKTIUAUBUCSSUDABIDCEFGHUEUF $.
  $}

  ${
    $d A a b c d p q r s t u v w x $.  $d B a b c d p q r s t u v w x $.
    $( Show closure and value of natural multiplication.  (Contributed by Scott
       Fenton, 2-Jun-2026.) $)
    nmulprop $p |- ( ( A e. On /\ B e. On ) -> ( ( A .no B ) e. On /\
     ( A .no B ) = |^| { x e. On | A. a e. A A. b e. B
     ( ( a .no B ) +no ( A .no b ) ) e. ( x +no ( a .no b ) ) } ) ) $=
      ( vp vq vr vs vc vd cnmul co con0 wcel cnadd wral wceq wa eleq1d vv vw vt
      vu crab cint weq oveq2d ralbidv raleqbi1dv rabbidv inteqd eqeq12d anbi12d
      cv oveq1 oveq2 oveq1d w3a simpl 2ralimi ralimi 3anim123i cop csuc cxp csn
      cdif cres cvv c1st cfv c2nd csb cmpo df-nmul opex vex sucex mp2an elelsuc
      adantr wel adantl sucid a1i opelxpd wn word wi eloni ordirr elequ1 notbid
      biimprcd con2d 3syl elsn opth bitr2i sylnib eldifd fvresd 3eqtr4g intnand
      imp df-ov oveq12d wss sssucid eleq12d wrex ciun 2ralbidv cab cuni simplr2
      dfiun2 rspcdva simplr3 simpr naddcld syl5ibrcom rexlimdva abssdv ssonunii
      eleq1 abrexex syl eqeltrid rspccva sylan syl2anc sseq2d rspcedvdw eqeltrd
      ssiun syl2an csbie oveq on2recsov wfun wfn nmulfn fnfun ax-mp xpex difexi
      resfunexg ad2ant2r intnanrd ad2ant2l xpss12 opelxpi sselid 2ralbidva ovex
      eleq2d iunex simplr onsuc simplr1 simprl simprr rspc2dv naddword1 iuneq2d
      ssidd wb simpr2 simpr3 onsssuc mpbid sseldd onintrab2 sylib op1std op2ndd
      ralrimivva csbeq1d csbeq12dv csbeq2dv eqtri eqtrid ovmpog mp3an12i 3eqtrd
      eqid jca ex syl5 on2ind ) FUOZGUOZLMZNOZUWODUOZUWNLMZUWMEUOZLMZPMZAUOZUWQ
      UWSLMZPMZOZEUWNQZDUWMQZANUEZUFZRZSZHUOZUWNLMZNOZUXMUWRUXLUWSLMZPMZUXDOZEU
      WNQZDUXLQZANUEZUFZRZSZUXLIUOZLMZNOZUYEUWQUYDLMZUXOPMZUXDOZEUYDQZDUXLQZANU
      EZUFZRZSZUWMUYDLMZNOZUYPUYGUWTPMZUXDOZEUYDQZDUWMQZANUEZUFZRZSZBUWNLMZNOZV
      UFUWRBUWSLMZPMZUXDOZEUWNQZDBQZANUEZUFZRZSBCLMZNOZVUPUWQCLMZVUHPMZUXDOZECQ
      ZDBQZANUEZUFZRZSBCFGHIFHUGZUWPUXNUXJUYBVVFUWOUXMNUWMUXLUWNLUPZTVVFUWOUXMU
      XIUYAVVGVVFUXHUXTVVFUXGUXSANUXFUXRDUWMUXLVVFUXEUXQEUWNVVFUXAUXPUXDVVFUWTU
      XOUWRPUWMUXLUWSLUPZUHTUIUJUKULUMUNGIUGZUXNUYFUYBUYNVVIUXMUYENUWNUYDUXLLUQ
      ZTVVIUXMUYEUYAUYMVVJVVIUXTUYLVVIUXSUYKANVVIUXRUYJDUXLUXQUYIEUWNUYDVVIUXPU
      YHUXDVVIUWRUYGUXOPUWNUYDUWQLUQURTUJUIUKULUMUNVVFUYQUYFVUDUYNVVFUYPUYENUWM
      UXLUYDLUPZTVVFUYPUYEVUCUYMVVKVVFVUBUYLVVFVUAUYKANUYTUYJDUWMUXLVVFUYSUYIEU
      YDVVFUYRUYHUXDVVFUWTUXOUYGPVVHUHTUIUJUKULUMUNUWMBRZUWPVUGUXJVUOVVLUWOVUFN
      UWMBUWNLUPZTVVLUWOVUFUXIVUNVVMVVLUXHVUMVVLUXGVULANUXFVUKDUWMBVVLUXEVUJEUW
      NVVLUXAVUIUXDVVLUWTVUHUWRPUWMBUWSLUPUHTUIUJUKULUMUNUWNCRZVUGVUQVUOVVEVVNV
      UFVUPNUWNCBLUQZTVVNVUFVUPVUNVVDVVOVVNVUMVVCVVNVULVVBANVVNVUKVVADBVUJVUTEU
      WNCVVNVUIVUSUXDVVNUWRVURVUHPUWNCUWQLUQURTUJUIUKULUMUNUYOIUWNQHUWMQZUYCHUW
      MQZVUEIUWNQZUSUYFIUWNQHUWMQZUXNHUWMQZUYQIUWNQZUSZUWMNOZUWNNOZSZUXKVVPVVSV
      VQVVTVVRVWAUYOUYFHIUWMUWNUYFUYNUTVAUYCUXNHUWMUXNUYBUTVBVUEUYQIUWNUYQVUDUT
      VBVCVWEVWBUXKVWEVWBSZUWPUXJVWFUWOUXINVWFUWOUWMUWNVDZLUWMVEZUWNVEZVFZVWGVG
      ZVHZVIZUAUBVJVJJUAUOZVKVLZKVWNVMVLZUWQKUOZUBUOZMZJUOZUWSVWRMZPMZUXBUWQUWS
      VWRMZPMZOZEVWQQZDVWTQZANUEZUFZVNZVNZVOZMZUWQUWNVWMMZUWMUWSVWMMZPMZUXBUWQU
      WSVWMMZPMZOZEUWNQDUWMQZANUEZUFZUXIVWEUWOVXMRVWBUCUDUWMUWNLVXLUCUDAUBUAJKD
      EVPUUAWBVWGVJOVWMVJOZVWFVYBNOVXMVYBRUWMUWNVQLUUBZVWLVJOVYCLNNVFZUUCVYDUUD
      VYELUUEUUFVWJVWKVWHVWIUWMFVRZVSUWNGVRZVSUUGUUHLVWLVJUUIVTVWFVYBUXINVWEVYB
      UXIRVWBVWEVYAUXHVWEVXTUXGANVWEVXSUXEDEUWMUWNVWEDFWCZEGWCZSZSZVXPUXAVXRUXD
      VYKVXNUWRVXOUWTPVYKUWQUWNVDZVWMVLVYLLVLVXNUWRVYKVYLVWLLVYKVYLVWJVWKVYKUWQ
      UWNVWHVWIVYJUWQVWHOZVWEVYHVYMVYIUWQUWMWAWBWDUWNVWIOVYKUWNVYGWEWFWGVYKDFUG
      ZGGUGZSZVYLVWKOZVYKVYNVYOVWCVYHVYNWHZVWDVYIVWCVYHVYRVWCUWMWIFFWCZWHZVYHVY
      RWJUWMWKUWMWLVYTVYNVYHVYNVYHWHVYTVYNVYHVYSDFFWMWNWOWPWQXFUUJUUKVYQVYLVWGR
      VYPVYLVWGUWQUWNVQWRUWQUWNUWMUWNDVRZVYGWSWTXAXBXCUWQUWNVWMXGUWQUWNLXGXDVYK
      UWMUWSVDZVWMVLWUBLVLVXOUWTVYKWUBVWLLVYKWUBVWJVWKVYKUWMUWSVWHVWIUWMVWHOVYK
      UWMVYFWEWFVYJUWSVWIOZVWEVYIWUCVYHUWSUWNWAWDWDWGVYKFFUGZEGUGZSZWUBVWKOZVYK
      WUEWUDVWDVYIWUEWHZVWCVYHVWDVYIWUHVWDUWNWIGGWCZWHZVYIWUHWJUWNWKUWNWLWUJWUE
      VYIWUEVYIWHWUJWUEVYIWUIEGGWMWNWOWPWQXFUULZXEWUGWUBVWGRWUFWUBVWGUWMUWSVQWR
      UWMUWSUWMUWNVYFEVRZWSWTXAXBXCUWMUWSVWMXGUWMUWSLXGXDXHVYKVXQUXCUXBPVYKUWQU
      WSVDZVWMVLWUMLVLVXQUXCVYKWUMVWLLVYKWUMVWJVWKVYJWUMVWJOVWEVYJUWMUWNVFZVWJW
      UMUWMVWHXIUWNVWIXIWUNVWJXIUWMXJUWNXJUWMVWHUWNVWIUUMVTUWQUWSUWMUWNUUNUUOWD
      VYKVYNWUESZWUMVWKOZVYKWUEVYNWUKXEWUPWUMVWGRWUOWUMVWGUWQUWSVQWRUWQUWSUWMUW
      NWUAWULWSWTXAXBXCUWQUWSVWMXGUWQUWSLXGXDUHXKUUPUKULWBZVWFUXGANXLUXINOVWFUX
      GUXAJUWMKUWNVWTUWNLMZUWMVWQLMZPMZXMZXMZVEZUXCPMZOZEUWNQDUWMQAWVCNUXBWVCRZ
      UXEWVEDEUWMUWNWVFUXDWVDUXAUXBWVCUXCPUPUURXNVWFWVBNOZWVCNOZVWFWVBUXBWVARZJ
      UWMXLZAXOZXPZNJAUWMWVAKUWNWUTVYGWURWUSPUUQZUUSXRZVWFWVKNXIZWVLNOZVWFWVJAN
      VWFWVIUXBNOZJUWMVWFJFWCZSZWVQWVIWVANOZWVSWVAUXBWUTRZKUWNXLZAXOZXPZNKAUWNW
      UTWVMXRZWVSWWCNXIZWWDNOZWVSWWBANWVSWWAWVQKUWNWVSKGWCZSZWVQWWAWUTNOZWWIWUR
      WUSWWIUXNWURNOZHUWMVWTHJUGUXMWURNUXLVWTUWNLUPTZWVSVVTWWHVVSVVTVWAVWEWVRXQ
      WBVWFWVRWWHUUTXSWWIUYQWUSNOZIUWNVWQIKUGUYPWUSNUYDVWQUWMLUQTZWVSVWAWWHVVSV
      VTVWAVWEWVRXTWBWVSWWHYAXSYBUXBWUTNYGZYCYDYEWWCKAUWNWUTVYGYHYFZYIYJUXBWVAN
      YGZYCYDYEWVKJAUWMWVAVYFYHYFZYIYJWVBUVAZYIVWFWVEDEUWMUWNVWFVYJSZWVCWVDUXAW
      WTWVHUXCNOZWVCWVDXIWWTWVGWVHWWTWVBWVLNWVNWWTWVOWVPWWTWVJANWWTWVIWVQJUWMWW
      TWVRSZWVQWVIWVTWXBWVAWWDNWWEWXBWWFWWGWXBWWBANWXBWWAWVQKUWNWXBWWHSZWVQWWAW
      WJWXCWURWUSWXBWWKWWHWWTVVTWVRWWKVVSVVTVWAVWEVYJXQUXNWWKHVWTUWMWWLYKYLWBWX
      BVWAWWHWWMWWTVWAWVRVVSVVTVWAVWEVYJXTWBUYQWWMIVWQUWNWWNYKYLYBWWOYCYDYEWWPY
      IYJWWQYCYDYEWWRYIYJZWWSYIWWTUYFWXAUYGNOHIUWQUWSUWMUWNHDUGZUYEUYGNUXLUWQUY
      DLUPTIEUGZUYGUXCNUYDUWSUWQLUQTVVSVVTVWAVWEVYJUVBVWFVYHVYIUVCZVWFVYHVYIUVD
      ZUVEWVCUXCUVFYMWWTUXAWVBXIZUXAWVCOZWWTUXAWVAXIZJUWMXLWXIWWTWXKUXAKUWNUWRW
      USPMZXMZXIZJUWQUWMJDUGZWVAWXMUXAWXOKUWNWUTWXLWXOWURUWRWUSPVWTUWQUWNLUPURU
      VGYNWXGWWTUXAWXLXIZKUWNXLWXNWWTWXPUXAUXAXIKUWSUWNKEUGZWXLUXAUXAWXQWUSUWTU
      WRPVWQUWSUWMLUQUHYNWXHWWTUXAUVHYOKUWNWXLUXAYQYIYOJUWMWVAUXAYQYIWWTUXANOWV
      GWXIWXJUVIWWTUWRUWTVWFVVTVYHUWRNOZVYJVWEVVSVVTVWAUVJVYHVYIUTUXNWXRHUWQUWM
      WXEUXMUWRNUXLUWQUWNLUPTYKYRVWFVWAVYIUWTNOZVYJVWEVVSVVTVWAUVKVYHVYIYAUYQWX
      SIUWSUWNWXFUYPUWTNUYDUWSUWMLUQTYKYRYBWXDUXAWVBUVLYMUVMUVNUVSYOUXGAUVOUVPZ
      YPUAUBVWGVWMVJVJVXKVYBVXLJUWMKUWNVXIVNZVNZNVWNVWGRZJVWOVXJUWMWYAUWMUWNVWN
      VYFVYGUVQWYCKVWPUWNVXIUWMUWNVWNVYFVYGUVRUVTUWAVWRVWMRZWYBUWQUWNVWRMZUWMUW
      SVWRMZPMZVXDOZEUWNQZDUWMQZANUEZUFZVYBWYBKUWNVWSWYFPMZVXDOZEVWQQZDUWMQZANU
      EZUFZVNZWYLJUWMWYAWYSVYFJFUGZKUWNVXIWYRWYTVXHWYQWYTVXGWYPANVXFWYODVWTUWMW
      YTVXEWYNEVWQWYTVXBWYMVXDWYTVXAWYFVWSPVWTUWMUWSVWRUPUHTUIUJUKULUWBYSKUWNWY
      RWYLVYGKGUGZWYQWYKXUAWYPWYJANXUAWYOWYIDUWMWYNWYHEVWQUWNXUAWYMWYGVXDXUAVWS
      WYEWYFPVWQUWNUWQVWRUQURTUJUIUKULYSUWCWYDWYKVYAWYDWYJVXTANWYDWYHVXSDEUWMUW
      NWYDWYGVXPVXDVXRWYDWYEVXNWYFVXOPUWQUWNVWRVWMYTUWMUWSVWRVWMYTXHWYDVXCVXQUX
      BPUWQUWSVWRVWMYTUHXKXNUKULUWDVXLUWHUWEUWFWUQUWGZWXTYPXUBUWIUWJUWKUWL $.
  $}

  ${
    $d A x a b $.  $d B x a b $.
    $( Closure law for natural multiplication.  (Contributed by Scott Fenton,
       10-Jun-2026.) $)
    nmulcl $p |- ( ( A e. On /\ B e. On ) -> ( A .no B ) e. On ) $=
      ( va vb vx con0 wcel wa cnmul co cv cnadd wral crab cint nmulprop simpld
      wceq ) AFGBFGHABIJZFGSCKZBIJADKZIJLJEKTUAIJLJGDBMCAMEFNOREABCDPQ $.

    $( Show the value of natural multiplication.  (Contributed by Scott Fenton,
       10-Jun-2026.) $)
    nmulval $p |- ( ( A e. On /\ B e. On ) -> ( A .no B ) =
     |^| { x e. On | A. a e. A A. b e. B ( ( a .no B ) +no ( A .no b ) ) e.
     ( x +no ( a .no b ) ) } ) $=
      ( con0 wcel wa cnmul co cv cnadd wral crab cint wceq nmulprop simprd ) BF
      GCFGHBCIJZFGSDKZCIJBEKZIJLJAKTUAIJLJGECMDBMAFNOPABCDEQR $.
  $}

  ${
    nmulcld.1 $e |- ( ph -> A e. On ) $.
    nmulcld.2 $e |- ( ph -> B e. On ) $.
    $( Closure law for natural multiplication.  Deduction form.  (Contributed
       by Scott Fenton, 12-Jun-2026.) $)
    nmulcld $p |- ( ph -> ( A .no B ) e. On ) $=
      ( con0 wcel cnmul co nmulcl syl2anc ) ABFGCFGBCHIFGDEBCJK $.
  $}

  ${
    $d A a b c d x y z $.  $d B a b c d x y z $.
    $( Natural multiplication is commutative.  (Contributed by Scott Fenton,
       10-Jun-2026.) $)
    nmulcom $p |- ( ( A e. On /\ B e. On ) -> ( A .no B ) = ( B .no A ) ) $=
      ( va vc vd vz vy vx cv cnmul co wceq oveq1 eqeq12d con0 wcel wral syl2anc
      oveq2 cnadd vb weq wa w3a crab cint simplr2 simprl rspcdva simplr3 simprr
      wel oveq12d simpllr simplll onelon nmulcl naddcom simplr1 rspc2dv eleq12d
      eqtrd oveq2d 2ralbidva ralcom bitrdi rabbidv inteqd nmulval adantr ancoms
      3eqtr4d ex on2ind ) CIZUAIZJKZVPVOJKZLZDIZVPJKZVPVTJKZLZVTEIZJKZWDVTJKZLZ
      VOWDJKZWDVOJKZLZAVPJKZVPAJKZLABJKZBAJKZLABCUADECDUBZVQWAVRWBVOVTVPJMVOVTV
      PJSNUAEUBWAWEWBWFVPWDVTJSVPWDVTJMNWOWHWEWIWFVOVTWDJMVOVTWDJSNVOALVQWKVRWL
      VOAVPJMVOAVPJSNVPBLWKWMWLWNVPBAJSVPBAJMNVOOPZVPOPZUCZWGEVPQDVOQZWCDVOQZWJ
      EVPQZUDZVSWRXBUCZFIZVPJKZVOGIZJKZTKZHIZXDXFJKZTKZPZGVPQFVOQZHOUEZUFZXFVOJ
      KZVPXDJKZTKZXIXFXDJKZTKZPZFVOQGVPQZHOUEZUFZVQVRXCXNYCXCXMYBHOXCXMYAGVPQFV
      OQYBXCXLYAFGVOVPXCFCULZGUAULZUCZUCZXHXRXKXTYHXHXQXPTKZXRYHXEXQXGXPTYHWCXE
      XQLDVOXDDFUBZWAXEWBXQVTXDVPJMVTXDVPJSNWSWTXAWRYGUGXCYEYFUHZUIYHWJXGXPLEVP
      XFEGUBZWHXGWIXPWDXFVOJSWDXFVOJMNWSWTXAWRYGUJXCYEYFUKZUIUMYHXQOPZXPOPZYIXR
      LYHWQXDOPZYNWPWQXBYGUNZYHWPYEYPWPWQXBYGUOZYKVOXDUPRVPXDUQRYHXFOPZWPYOYHWQ
      YFYSYQYMVPXFUPRYRXFVOUQRXQXPURRVBYHXJXSXITYHWGXJXSLXDWDJKZWDXDJKZLDEXDXFV
      OVPYJWEYTWFUUAVTXDWDJMVTXDWDJSNYLYTXJUUAXSWDXFXDJSWDXFXDJMNWSWTXAWRYGUSYK
      YMUTVCVAVDYAFGVOVPVEVFVGVHWRVQXOLXBHVOVPFGVIVJWRVRYDLZXBWQWPUUBHVPVOGFVIV
      KVJVLVMVN $.
  $}

  ${
    $d A a b x $.
    $( Natural multiplication by zero.  (Contributed by Scott Fenton,
       10-Jun-2026.) $)
    nmulr0 $p |- ( A e. On -> ( A .no (/) ) = (/) ) $=
      ( va vb vx con0 wcel c0 cnmul co cv cnadd wral crab cint wceq 0elon mpan2
      nmulval ral0 ax-mp rgenw oveq1 eleq2d 2ralbidv elrab3 mpbir int0el eqtrdi
      wb ) AEFZAGHIZBJZGHIACJZHIKIZDJZULUMHIZKIZFZCGLBALZDEMZNZGUJGEFZUKVAOPDAG
      BCRQGUTFZVAGOVCUNGUPKIZFZCGLZBALZVFBAVECSUAVBVCVGUIPUSVGDGEUOGOZURVEBCAGV
      HUQVDUNUOGUPKUBUCUDUETUFUTUGTUH $.
  $}

  $( Natural multiplication by zero.  (Contributed by Scott Fenton,
     10-Jun-2026.) $)
  nmull0 $p |- ( A e. On -> ( (/) .no A ) = (/) ) $=
    ( con0 wcel c0 cnmul co wceq 0elon nmulcom mpan2 nmulr0 eqtr3d ) ABCZADEFZD
    AEFZDMDBCNOGHADIJAKL $.


  ${
    $d A a b x y $.
    $( Identity law for natural multiplication.  (Contributed by Scott Fenton,
       21-Jul-2026.) $)
    nmulrid $p |- ( A e. On -> ( A .no 1o ) = A ) $=
      ( va vb vy vx cv c1o cnmul co wceq oveq1 con0 wcel wa cnadd adantr oveq2d
      wral c0 syl weq id eqeq12d crab cint wss 1on nmulval mpan2 wel csn raleqi
      df1o2 0ex oveq2 eleq12d ralsn bitri simprr nmulr0 ad2antrr oveq12d sselda
      onss adantrr naddrid eqtrd ad2antlr bitrid ralimdva imp ralbi an32s dfss3
      wb expr bitr4di rabbidva inteqd intmin 3eqtrd ex tfis3 ) BFZGHIZWDJZCFZGH
      IZWGJZAGHIZAJBCABCUAZWEWHWDWGWDWGGHKWKUBUCWDAJZWEWJWDAWDAGHKWLUBUCWDLMZWI
      CWDRZWFWMWNNZWEWHWDDFZHIZOIZEFZWGWPHIZOIZMZDGRZCWDRZELUDZUEZWDWSUFZELUDZU
      EZWDWMWEXFJZWNWMGLMXJUGEWDGCDUHUIPWOXEXHWOXDXGELWOWSLMZNXDCEUJZCWDRZXGWMX
      KWNXDXMVOZWMXKNZWNNXCXLVOZCWDRZXNXOWNXQXOWIXPCWDXOCBUJZWIXPXCWHWDSHIZOIZW
      SWGSHIZOIZMZXOXRWINZNZXLXCXBDSUKZRYCXBDGYFUMULXBYCDSUNWPSJZWRXTXAYBYGWQXS
      WHOWPSWDHUOQYGWTYAWSOWPSWGHUOQUPUQURYEXTWGYBWSYEXTWGSOIZWGYEWHWGXSSOXOXRW
      IUSWMXSSJXKYDWDUTVAVBYEWGLMZYHWGJXOXRYIWIXOWDLWGWMWDLUFXKWDVDPVCVEZWGVFTV
      GYEYBWSSOIZWSYEYASWSOYEYIYASJYJWGUTTQXKYKWSJWMYDWSVFVHVGUPVIVPVJVKXCXLCWD
      VLTVMCWDWSVNVQVRVSWMXIWDJWNEWDLVTPWAWBWC $.
  $}

  $( Identity law for natural multiplication.  (Contributed by Scott Fenton,
     21-Jul-2026.) $)
  nmullid $p |- ( A e. On -> ( 1o .no A ) = A ) $=
    ( con0 wcel c1o cnmul co wceq 1on nmulcom mpan nmulrid eqtrd ) ABCZDAEFZADE
    FZADBCMNOGHDAIJAKL $.

  ${
    onelond.1 $e |- ( ph -> A e. On ) $.
    onelond.2 $e |- ( ph -> B e. A ) $.
    $( An element of an ordinal number is an ordinal number.  Theorem 2.2(iii)
       of [BellMachover] p. 469.  Lemma 1.3 of [Schloeder] p. 1.  Deduction
       form.  (Contributed by Scott Fenton, 31-Jul-2026.) $)
    onelond $p |- ( ph -> B e. On ) $=
      ( con0 wcel onelon syl2anc ) ABFGCBGCFGDEBCHI $.
  $}

  ${
    ontr2d.1 $e |- ( ph -> A e. On ) $.
    ontr2d.2 $e |- ( ph -> C e. On ) $.
    ontr2d.3 $e |- ( ph -> A C_ B ) $.
    ontr2d.4 $e |- ( ph -> B e. C ) $.
    $( Transitive law for ordinal numbers.  Exercise 3 of [TakeutiZaring]
       p. 40.  Deduction form.  (Contributed by Scott Fenton, 31-Jul-2026.) $)
    ontr2d $p |- ( ph -> A e. C ) $=
      ( wss wcel con0 wa wi ontr2 syl2anc mp2and ) ABCIZCDJZBDJZGHABKJDKJQRLSME
      FBCDNOP $.
  $}

  ${
    onelssd.1 $e |- ( ph -> A e. On ) $.
    onelssd.2 $e |- ( ph -> B e. A ) $.
    $( An element of an ordinal number is a subset of the number.  Deduction
       form.  (Contributed by Scott Fenton, 31-Jul-2026.) $)
    onelssd $p |- ( ph -> B C_ A ) $=
      ( con0 wcel wss onelss sylc ) ABFGCBGCBHDEBCIJ $.
  $}

  ${
    nmul.1 $e |- ( ph -> A e. On ) $.
    $( Natural multiplication by zero.  Deduction form.  (Contributed by Scott
       Fenton, 30-Jul-2026.) $)
    nmulr0d $p |- ( ph -> ( A .no (/) ) = (/) ) $=
      ( con0 wcel c0 cnmul co wceq nmulr0 syl ) ABDEBFGHFICBJK $.

    $( Natural multiplication by zero.  Deduction form.  (Contributed by Scott
       Fenton, 30-Jul-2026.) $)
    nmull0d $p |- ( ph -> ( (/) .no A ) = (/) ) $=
      ( con0 wcel c0 cnmul co wceq nmull0 syl ) ABDEFBGHFICBJK $.

    $( Identity law for natural multiplication.  Deduction form.  (Contributed
       by Scott Fenton, 30-Jul-2026.) $)
    nmulridd $p |- ( ph -> ( A .no 1o ) = A ) $=
      ( con0 wcel c1o cnmul co wceq nmulrid syl ) ABDEBFGHBICBJK $.

    $( Identity law for natural multiplication.  Deduction form.  (Contributed
       by Scott Fenton, 30-Jul-2026.) $)
    nmullidd $p |- ( ph -> ( 1o .no A ) = A ) $=
      ( con0 wcel c1o cnmul co wceq nmullid syl ) ABDEFBGHBICBJK $.

    nmul.2 $e |- ( ph -> B e. On ) $.
    $( Natural multiplication commutes.  Deduction form.  (Contributed by Scott
       Fenton, 30-Jul-2026.) $)
    nmulcomd $p |- ( ph -> ( A .no B ) = ( B .no A ) ) $=
      ( con0 wcel cnmul co wceq nmulcom syl2anc ) ABFGCFGBCHICBHIJDEBCKL $.
  $}

  ${
    nadd.1 $e |- ( ph -> A e. On ) $.
    $( Identity law for natural addition.  Deduction form.  (Contributed by
       Scott Fenton, 30-Jul-2026.) $)
    naddridd $p |- ( ph -> ( A +no (/) ) = A ) $=
      ( con0 wcel c0 cnadd co wceq naddrid syl ) ABDEBFGHBICBJK $.

    $( Identity law for natural addition.  Deduction form.  (Contributed by
       Scott Fenton, 30-Jul-2026.) $)
    naddlidd $p |- ( ph -> ( (/) +no A ) = A ) $=
      ( con0 wcel c0 cnadd co wceq naddlid syl ) ABDEFBGHBICBJK $.

    nadd.2 $e |- ( ph -> B e. On ) $.
    $( Natural addition commutes.  Deduction form.  (Contributed by Scott
       Fenton, 30-Jul-2026.) $)
    naddcomd $p |- ( ph -> ( A +no B ) = ( B +no A ) ) $=
      ( con0 wcel cnadd co wceq naddcom syl2anc ) ABFGCFGBCHICBHIJDEBCKL $.

    nadd.3 $e |- ( ph -> C e. On ) $.
    $( Natural addition associates.  Deduction form.  (Contributed by Scott
       Fenton, 30-Jul-2026.) $)
    naddassd $p |- ( ph -> ( ( A +no B ) +no C ) = ( A +no ( B +no C ) ) ) $=
      ( con0 wcel cnadd co wceq naddass syl3anc ) ABHICHIDHIBCJKDJKBCDJKJKLEFGB
      CDMN $.

    $( Commutative/associative law that swaps the last two terms in a triple
       sum.  Deduction form.  (Contributed by Scott Fenton, 30-Jul-2026.) $)
    nadd32d $p |- ( ph -> ( ( A +no B ) +no C ) = ( ( A +no C ) +no B ) ) $=
      ( con0 wcel cnadd co wceq nadd32 syl3anc ) ABHICHIDHIBCJKDJKBDJKCJKLEFGBC
      DMN $.
  $}

  ${
    $d A x c d $.  $d B x c d $.  $d C x c d $.  $d D x c d $.
    $( Ordering relationship for natural ordinal operations.  (Contributed by
       Scott Fenton, 15-Jul-2026.) $)
    nmuladdel $p |- ( ( ( A e. On /\ B e. On ) /\ ( C e. A /\ D e. B ) ) ->
    ( ( C .no B ) +no ( A .no D ) ) e. ( ( A .no B ) +no ( C .no D ) ) ) $=
      ( vc vd vx con0 wcel wa cv cnmul co cnadd wral oveq1 oveq2d eleq12d oveq2
      wceq eleq2d 2ralbidv crab cint nmulval wss c0 ssrab2 nmulcl eqeltrrd wrex
      rabn0 onintrab2 bitri sylibr onint sylancr eqeltrd elrabrd oveq1d rspc2va
      wne ancoms sylan ) AHIBHIJZEKZBLMZAFKZLMZNMZABLMZVFVHLMZNMZIZFBOEAOZCAIDB
      IJZCBLMZADLMZNMZVKCDLMZNMZIZVEVJGKZVLNMZIZFBOEAOZVOGVKHWCVKTZWEVNEFABWGWD
      VMVJWCVKVLNPUAUBVEVKWFGHUCZUDZWHGABEFUEZVEWHHUFWHUGVBZWIWHIWFGHUHVEWIHIZW
      KVEVKWIHWJABUIUJWKWFGHUKWLWFGHULWFGUMUNUOWHUPUQURUSVPVOWBVNWBVQVINMZVKCVH
      LMZNMZIEFCDABVFCTZVJWMVMWOWPVGVQVINVFCBLPUTWPVLWNVKNVFCVHLPQRVHDTZWMVSWOW
      AWQVIVRVQNVHDALSQWQWNVTVKNVHDCLSQRVAVCVD $.
  $}

  ${
    $( Ordering relationship for natural ordinal operations.  (Contributed by
       Scott Fenton, 15-Jul-2026.) $)
    nmuladdss $p |- ( ( ( A e. On /\ B e. On ) /\ ( C e. On /\ D e. On ) /\
    ( C C_ A /\ D C_ B ) ) ->
    ( ( C .no B ) +no ( A .no D ) ) C_ ( ( A .no B ) +no ( C .no D ) ) ) $=
      ( con0 wcel wa wss cnmul co cnadd wceq onsseleq ancoms an4s nmulcl oveq2d
      wo wb wi bi2anan9 wtr adantr onelon syl2an naddcld ontr nmuladdel adantlr
      syl trss sylc expr simplll simpllr nmulcld simplrl naddcom eqimsscd oveq2
      syl2anc sseq12d syl5ibrcom jaod ssid 2a1i oveq1 oveq1d imbi2d impd sylbid
      ex 3impia ) AEFZBEFZGZCEFZDEFZGZCAHZDBHZGZCBIJZADIJZKJZABIJZCDIJZKJZHZVPV
      SGZWBCAFZCALZRZDBFZDBLZRZGZWIVNVQVOVRWBWQSVNVQGVTWMVOVRGWAWPVQVNVTWMSCAMN
      VRVOWAWPSDBMNUAOWJWMWPWIWJWKWPWITZWLWJWKWRWJWKGZWNWIWOWJWKWNWIVPWKWNGZWIV
      SVPWTGZWHUBZWEWHFWIXAWHEFXBXAWFWGVPWFEFZWTABPUCVNWKVOWNWGEFZVNWKGVQVRXDVO
      WNGACUDBDUDCDPUEOUFWHUGUJABCDUHWHWEUKULUIUMWSWIWOWCWFKJZWFWCKJZHWSXFXEWSX
      CWCEFXFXELWSABVNVOVSWKUNVNVOVSWKUOZUPWSCBVPVQVRWKUQXGUPWFWCURVAUSWOWEXEWH
      XFWOWDWFWCKDBAIUTQWOWGWCWFKDBCIUTQVBVCVDVLWJWRWLWPWFWDKJZXHHZTXIWJWPXHVEV
      FWLWIXIWPWLWEXHWHXHWLWCWFWDKCABIVGVHWLWGWDWFKCADIVGQVBVIVCVDVJVKVM $.
  $}


  $( Natural multiplication preserves less-than or equal.  (Contributed by
     Scott Fenton, 15-Jul-2026.) $)
  nmulss1 $p |- ( ( ( A e. On /\ B e. On /\ C e. On ) /\ A C_ B ) ->
    ( C .no A ) C_ ( C .no B ) ) $=
    ( con0 wcel w3a wss wa c0 cnmul cnadd simpl3 simpl2 a1i wceq nmull0 nmulcld
    co syl eqtr2d 0elon simpl1 simpr nmuladdss syl222anc oveq1d naddlid naddrid
    0ss oveq2d 3sstr4d ) ADEZBDEZCDEZFZABGZHZIBJRZCAJRZKRZCBJRZIAJRZKRZUSVAUQUN
    UMIDEZULICGZUPUTVCGULUMUNUPLZULUMUNUPMZVDUQUANULUMUNUPUBZVEUQCUINUOUPUCCBIA
    UDUEUQUTIUSKRZUSUQURIUSKUQUMURIOVGBPSUFUQUSDEVIUSOUQCAVFVHQUSUGSTUQVCVAIKRZ
    VAUQVBIVAKUQULVBIOVHAPSUJUQVADEVJVAOUQCBVFVGQVAUHSTUK $.

  $( Natural multiplication by a non-zero number preserves less-than.
     (Contributed by Scott Fenton, 15-Jul-2026.) $)
  nmulel1 $p |- ( ( ( B e. On /\ C e. On ) /\
  ( A e. B /\ C =/= (/) ) ) -> ( C .no A ) e. ( C .no B ) ) $=
    ( con0 wcel wa c0 wne cnmul co cnadd simplr simpll wceq wn df-ne nmull0 syl
    nmulcld eqtrd on0eqel orcanai sylan2b ad2ant2l simprl oveq1d onelon naddlid
    nmuladdel syl22anc ad2ant2r oveq2d naddrid 3eltr3d ) BDEZCDEZFZABEZCGHZFZFZ
    GBIJZCAIJZKJZCBIJZGAIJZKJZVCVEVAUPUOGCEZURVDVGEUOUPUTLZUOUPUTMZUPUSVHUOURUS
    UPCGNZOVHCGPUPVKVHCUAUBUCUDUQURUSUECBGAUIUJVAVDGVCKJZVCVAVBGVCKVAUOVBGNVJBQ
    RUFVAVCDEVLVCNVACAVIUOURADEZUPUSBAUGUKZSVCUHRTVAVGVEGKJZVEVAVFGVEKVAVMVFGNV
    NAQRULVAVEDEVOVENVACBVIVJSVEUMRTUN $.

  ${
    $d A b c x $.  $d B b c x $.  $d C b c x $.
    $( Characterize less-than a natural product.  (Contributed by Scott Fenton,
       15-Jul-2026.) $)
    ltnmul $p |- ( ( A e. On /\ B e. On /\ C e. On ) ->
    ( A e. ( B .no C ) <-> E. b e. B E. c e. C
    ( A +no ( b .no c ) ) C_ ( ( b .no C ) +no ( B .no c ) ) ) ) $=
      ( vx con0 wcel cnmul co cv cnadd wrex wral wn wi wb wa nmulcld naddcld
      w3a wss crab cint oveq1 eleq2d 2ralbidv onnminsb 3ad2ant1 nmulval 3adant1
      simpl1 simp2 simpl onelon syl2an simp3 simpr simpl3 simpl2 ontri1 syl2anc
      2rexbidva rexnal2 bitrdi 3imtr4d nmuladdel 3adantl1 ontr2 naddel1 syl3anc
      wceq mpan2d sylibrd rexlimdvva impbid ) AGHZBGHZCGHZUAZABCIJZHZADKZEKZIJZ
      LJZWCCIJZBWDIJZLJZUBZECMDBMZVTAWIFKZWELJZHZECNDBNZFGUCUDZHZWIWFHZECNDBNZO
      ZWBWKVQVRWQWTPVSWOWSFAWLAVLZWNWRDEBCXAWMWFWIWLAWELUEUFUGUHUIVRVSWBWQQVQVR
      VSRWAWPAFBCDEUJUFUKVTWKWROZECMDBMWTVTWJXBDEBCVTWCBHZWDCHZRZRZWFGHZWIGHWJX
      BQXFAWEVQVRVSXEULZXFWCWDVTVRXCWCGHXEVQVRVSUMXCXDUNBWCUOUPZVTVSXDWDGHXEVQV
      RVSUQXCXDURCWDUOUPZSZTZXFWGWHXFWCCXIVQVRVSXEUSZSXFBWDVQVRVSXEUTZXJSTWFWIV
      AVBVCWRDEBCVDVEVFVTWJWBDEBCXFWJWFWAWELJZHZWBXFWJWIXOHZXPVRVSXEXQVQBCWCWDV
      GVHXFXGXOGHWJXQRXPPXLXFWAWEXFBCXNXMSZXKTWFWIXOVIVBVMXFVQWAGHWEGHWBXPQXHXR
      XKAWAWEVJVKVNVOVP $.
  $}

  ${
    $d A a b $.  $d B a b $.  $d C a b $.
    $( A condition for bounding a natural product above.  Converse of
       ~ ltnmul .  (Contributed by Scott Fenton, 16-Jul-2026.) $)
    nmulle $p |- ( ( A e. On /\ B e. On /\ C e. On ) ->
    ( ( A .no B ) C_ C <-> A. a e. A A. b e. B
    ( ( a .no B ) +no ( A .no b ) ) e. ( C +no ( a .no b ) ) ) ) $=
      ( con0 wcel cnmul co wss wn cv cnadd wral wb ontri1 wrex onelon nmulcld
      wa w3a nmulcl stoic3 ltnmul 3coml simpl3 simp1 simpl syl2an simp2 naddcld
      simpr simpl2 simpl1 syl2anc 2rexbidva rexnal2 bitrdi bitr2d con1bid bitrd
      ) AFGZBFGZCFGZUAZABHIZCJZCVFGZKZDLZBHIZAELZHIZMIZCVJVLHIZMIZGZEBNDANZVBVC
      VFFGVDVGVIOABUBVFCPUCVEVRVHVEVHVPVNJZEBQDAQZVRKZVDVBVCVHVTOCABDEUDUEVEVTV
      QKZEBQDAQWAVEVSWBDEABVEVJAGZVLBGZTZTZVPFGVNFGVSWBOWFCVOVBVCVDWEUFWFVJVLVE
      VBWCVJFGWEVBVCVDUGWCWDUHAVJRUIZVEVCWDVLFGWEVBVCVDUJWCWDULBVLRUIZSUKWFVKVM
      WFVJBWGVBVCVDWEUMSWFAVLVBVCVDWEUNWHSUKVPVNPUOUPVQDEABUQURUSUTVA $.
  $}

  ${
    $d A b c x $.  $d B b c x $.  $d C b c x $.
    $( Condition for bounding a natural sum below.  (Contributed by Scott
       Fenton, 21-Jul-2026.) $)
    ltnadd $p |- ( ( A e. On /\ B e. On /\ C e. On ) ->
    ( A e. ( B +no C ) <-> ( E. b e. B A C_ ( b +no C ) \/
    E. c e. C A C_ ( B +no c ) ) ) ) $=
      ( vx con0 wcel cnadd co cv wss wrex wo wral wa wn wb simpl1 syl2anc eleq2
      w3a crab cint wi ralbidv anbi12d onnminsb 3ad2ant1 naddov2 3adant1 eleq2d
      wceq onss 3ad2ant2 sselda simpl3 naddcld ontri1 rexbidva 3ad2ant3 orbi12d
      simpl2 orcom rexnal orbi12i 3bitr4i bitrdi 3imtr4d simprr adantrr naddel1
      ianor simprl syl3anc mpbid naddcl adantr mp2and rexlimdvaa naddel2 impbid
      ontr2 jaod ) AGHZBGHZCGHZUBZABCIJZHZADKZCIJZLZDBMZABEKZIJZLZECMZNZWHAWPFK
      ZHZECOZWLWTHZDBOZPZFGUCUDZHZWPAHZECOZWLAHZDBOZPZQZWJWSWEWFXGXMUEWGXEXLFAW
      TAUMZXBXIXDXKXNXAXHECWTAWPUAUFXNXCXJDBWTAWLUAUFUGUHUIWHWIXFAWFWGWIXFUMWEF
      EDBCUJUKULWHWSXJQZDBMZXHQZECMZNZXMWHWNXPWRXRWHWMXODBWHWKBHZPZWEWLGHWMXORW
      EWFWGXTSYAWKCWHBGWKWFWEBGLWGBUNUOUPZWEWFWGXTUQURAWLUSTUTWHWQXQECWHWOCHZPZ
      WEWPGHWQXQRWEWFWGYCSYDBWOWEWFWGYCVCWHCGWOWGWECGLWFCUNVAUPZURAWPUSTUTVBXKQ
      ZXIQZNYGYFNXSXMYFYGVDXPYFXRYGXJDBVEXHECVEVFXIXKVMVGVHVIWHWNWJWRWHWMWJDBWH
      XTWMPZPZWMWLWIHZWJWHXTWMVJYIXTYJWHXTWMVNYIWKGHZWFWGXTYJRWHXTYKWMYBVKWEWFW
      GYHVCWEWFWGYHUQWKBCVLVOVPYIWEWIGHZWMYJPWJUEWEWFWGYHSWHYLYHWFWGYLWEBCVQUKZ
      VRAWLWIWCTVSVTWHWQWJECWHYCWQPZPZWQWPWIHZWJWHYCWQVJYOYCYPWHYCWQVNYOWOGHZWG
      WFYCYPRWHYCYQWQYEVKWEWFWGYNUQWEWFWGYNVCWOCBWAVOVPYOWEYLWQYPPWJUEWEWFWGYNS
      WHYLYNYMVRAWPWIWCTVSVTWDWB $.
  $}

  ${
    $d A a b $.  $d B a b $.  $d C a b $.
    $( Condition for bounding natural addition above.  (Contributed by Scott
       Fenton, 21-Jul-2026.) $)
    naddle $p |- ( ( A e. On /\ B e. On /\ C e. On ) ->
    ( ( A +no B ) C_ C <-> ( A. a e. A ( a +no B ) e. C /\
    A. b e. B ( A +no b ) e. C ) ) ) $=
      ( con0 wcel cnadd co wn cv wss wrex wo wral wa wb ontri1 syl2anc simpl3
      w3a ltnadd 3coml notbid naddcl 3adant3 simp3 onss 3ad2ant1 sselda naddcld
      simpl2 rexbidva simpl1 orbi12d rexnal orbi12i ianor bitr4i bitrdi con2bid
      3ad2ant2 3bitr4d ) AFGZBFGZCFGZUAZCABHIZGZJZCDKZBHIZLZDAMZCAEKZHIZLZEBMZN
      ZJVHCLZVLCGZDAOZVPCGZEBOZPZVGVIVSVFVDVEVIVSQCABDEUBUCUDVGVHFGZVFVTVJQVDVE
      WFVFABUEUFVDVEVFUGVHCRSVGVSWEVGVSWAJZDAMZWCJZEBMZNZWEJZVGVNWHVRWJVGVMWGDA
      VGVKAGZPZVFVLFGVMWGQVDVEVFWMTWNVKBVGAFVKVDVEAFLVFAUHUIUJVDVEVFWMULUKCVLRS
      UMVGVQWIEBVGVOBGZPZVFVPFGVQWIQVDVEVFWOTWPAVOVDVEVFWOUNVGBFVOVEVDBFLVFBUHV
      BUJUKCVPRSUMUOWKWBJZWDJZNWLWHWQWJWRWADAUPWCEBUPUQWBWDURUSUTVAVC $.
  $}

  ${
    $d ph z w $.  $d A d f z w $.  $d B d f z w $.  $d C d f z w $.
    $d Y z w $.
    nadddilem1.1 $e |- ( ph -> A e. On ) $.
    nadddilem1.2 $e |- ( ph -> B e. On ) $.
    nadddilem1.3 $e |- ( ph -> C e. On ) $.
    nadddilem1.4 $e |- ( ph -> A. d e. A
    ( d .no ( B +no C ) ) = ( ( d .no B ) +no ( d .no C ) ) ) $.
    nadddilem1.5 $e |- ( ph -> A. f e. C
    ( A .no ( B +no f ) ) = ( ( A .no B ) +no ( A .no f ) ) ) $.
    nadddilem1.6 $e |- ( ph -> A. d e. A A. f e. C
    ( d .no ( B +no f ) ) = ( ( d .no B ) +no ( d .no f ) ) ) $.
    $( Lemma for ~ nadddi .  Prove a subcase of the reverse implication.
       (Contributed by Scott Fenton, 31-Jul-2026.) $)
    nadddilem1 $p |- ( ( ph /\ Y e. ( A .no C ) ) ->
    ( ( A .no B ) +no Y ) e. ( A .no ( B +no C ) ) ) $=
      ( cnmul co wcel cnadd con0 nmulcld naddcld vz vw wa cv wss wrex wb adantr
      simpr onelond ltnmul syl3anc ad2antrr simprll simprlr simprr naddss2 wceq
      naddassd mpbid oveq2d eqeq12d wral rspcdva oveq1d nadd32d 3eqtrrd naddel2
      weq oveq2 nmuladdel syl22anc oveq1 oveq12d naddcomd eqtrd rspc2dv 3eltr4d
      eqtr4d naddel1 mpbird eqeltrd ontr2d expr rexlimdvva sylbid syldbl2 ) AFB
      DNOZPZBCNOZFQOZBCDQOZNOZPZAWIUCZWIFUAUDZUBUDZNOZQOZWPDNOZBWQNOZQOZUEZUBDU
      FUABUFZWNWOFRPZBRPZDRPZWIXDUGWOWHFWOBDAXFWIHUHZAXGWIJUHZSAWIUIUJZXHXIFBDU
      AUBUKULWOXCWNUAUBBDWOWPBPZWQDPZUCZXCWNWOXMXCUCZUCZWNWKWRQOZWMWRQOZPZXOXPW
      JWSQOZXQXOWJFWRXOBCAXFWIXNHUMZACRPZWIXNIUMZSZWOXEXNXJUHZXOWPWQXOBWPXTWOXK
      XLXCUNZUJZXODWQAXGWIXNJUMZWOXKXLXCUOZUJZSZUSXOXSWJXBQOZXQXOWJWSYCXOFWRYDY
      JTZTXOWMWRXOBWLXTXOCDYBYGTZSZYJTZXOXCXSYKUEZWOXMXCUPXOWSRPXBRPWJRPXCYPUGY
      LXOWTXAXOWPDYFYGSZXOBWQXTYISZTYCWSXBWJUQULUTXOYKBCWQQOZNOZWTQOZXQXOUUAWJX
      AQOZWTQOWJWTQOXAQOYKXOYTUUBWTQXOBCEUDZQOZNOZWJBUUCNOZQOZURZYTUUBUREDWQEUB
      VIZUUEYTUUGUUBUUIUUDYSBNUUCWQCQVJZVAUUIUUFXAWJQUUCWQBNVJVAVBAUUHEDVCWIXNL
      UMYHVDVEXOWJXAWTYCYRYQVFXOWJWTXAYCYQYRUSVGXOUUAXQPZUUAWPCNOZQOZXQUULQOZPZ
      XOWPWLNOZYTQOZWMWPYSNOZQOZUUMUUNXOXFWLRPXKYSWLPZUUQUUSPXTYMYEXOXLUUTYHXOW
      QRPXGYAXLUUTUGYIYGYBWQDCVHULUTBWLWPYSVKVLXOUUMYTUUPQOZUUQXOUUMYTWTUULQOZQ
      OUVAXOYTWTUULXOBYSXTXOCWQYBYITSZYQXOWPCYFYBSZUSXOUUPUVBYTQXOUUPUULWTQOZUV
      BXOGUDZWLNOZUVFCNOZUVFDNOZQOZURZUUPUVEURGBWPGUAVIZUVGUUPUVJUVEUVFWPWLNVMU
      VLUVHUULUVIWTQUVFWPCNVMZUVFWPDNVMVNVBAUVKGBVCWIXNKUMYEVDXOUULWTUVDYQVOVPV
      AVSXOYTUUPUVCXOWPWLYFYMSVOVPXOUUNWMWRUULQOZQOUUSXOWMWRUULYNYJUVDUSXOUVNUU
      RWMQXOUVNUULWRQOZUURXOWRUULYJUVDVOXOUVFUUDNOZUVHUVFUUCNOZQOZURZUURUVOURWP
      UUDNOZUULWPUUCNOZQOZURGEWPWQBDUVLUVPUVTUVRUWBUVFWPUUDNVMUVLUVHUULUVQUWAQU
      VMUVFWPUUCNVMVNVBUUIUVTUURUWBUVOUUIUUDYSWPNUUJVAUUIUWAWRUULQUUCWQWPNVJVAV
      BAUVSEDVCGBVCWIXNMUMYEYHVQVSVAVPVRXOUUARPXQRPUULRPUUKUUOUGXOYTWTUVCYQTYOU
      VDUUAXQUULVTULWAWBWCWBXOWKRPWMRPWRRPWNXRUGXOWJFYCYDTYNYJWKWMWRVTULWAWDWEW
      FWG $.
  $}

  ${
    $d ph p q x y $.  $d A d e f p q x y $.  $d B d e f p q x y $.
    $d C d e f p q x y $.
    nadddilem2.1 $e |- ( ph -> A e. On ) $.
    nadddilem2.2 $e |- ( ph -> B e. On ) $.
    nadddilem2.3 $e |- ( ph -> C e. On ) $.
    nadddilem2.4 $e |- ( ph -> A. d e. A
    ( d .no ( B +no C ) ) = ( ( d .no B ) +no ( d .no C ) ) ) $.
    nadddilem2.5 $e |- ( ph -> A. e e. B
    ( A .no ( e +no C ) ) = ( ( A .no e ) +no ( A .no C ) ) ) $.
    nadddilem2.6 $e |- ( ph -> A. f e. C
    ( A .no ( B +no f ) ) = ( ( A .no B ) +no ( A .no f ) ) ) $.
    nadddilem2.7 $e |- ( ph -> A. d e. A A. e e. B
    ( d .no ( e +no C ) ) = ( ( d .no e ) +no ( d .no C ) ) ) $.
    nadddilem2.8 $e |- ( ph -> A. d e. A A. f e. C
    ( d .no ( B +no f ) ) = ( ( d .no B ) +no ( d .no f ) ) ) $.
    $( Lemma for ~ nadddi .  Prove the reverse implication.  (Contributed by
       Scott Fenton, 31-Jul-2026.) $)
    nadddilem2 $p |- ( ph ->
    ( ( A .no B ) +no ( A .no C ) ) C_ ( A .no ( B +no C ) ) ) $=
      ( cnmul co cnadd wcel wral vx vy vq vp wss cv wa wceq weq oveq12d eqeq12d
      oveq1 cbvralvw naddcomd oveq2d adantr con0 simpr onelond nmulcld ralbidva
      bitrid mpbid oveq2 cbvral2vw adantrl adantrr 2ralbidva nadddilem1 3eltr4d
      oveq1d ralrimiva wb naddcld naddle syl3anc mpbir2and ) ABCPQZBDPQZRQBCDRQ
      ZPQZUEZUAUFZVSRQZWASZUAVRTZVRUBUFZRQWASZUBVSTZAWEUAVRAWCVRSZUGZVSWCRQBDCR
      QZPQZWDWAABDCUCWCUDHJIAGUFZVTPQZWNCPQZWNDPQZRQZUHZGBTZUDUFZWLPQZXADPQZXAC
      PQZRQZUHZUDBTZKWTXAVTPQZXDXCRQZUHZUDBTAXGWSXJGUDBGUDUIZWOXHWRXIWNXAVTPULX
      KWPXDWQXCRWNXACPULWNXADPULZUJUKUMAXJXFUDBAXABSZUGZXHXBXIXEAXHXBUHXMAVTWLX
      APACDIJUNZUOUPXNXDXCXNXACXNBXAABUQSZXMHUPAXMURUSZACUQSZXMIUPUTXNXADXQADUQ
      SZXMJUPUTUNUKVAVBVCABEUFZDRQZPQZBXTPQZVSRQZUHZECTZBDUCUFZRQZPQZVSBYGPQZRQ
      ZUHZUCCTZLYFBYGDRQZPQZYJVSRQZUHZUCCTAYMYEYQEUCCEUCUIZYBYOYDYPYRYAYNBPXTYG
      DRULZUOYRYCYJVSRXTYGBPVDVKUKUMAYQYLUCCAYGCSZUGZYOYIYPYKUUAYNYHBPUUAYGDUUA
      CYGAXRYTIUPAYTURUSZAXSYTJUPZUNZUOUUAYJVSUUABYGAXPYTHUPZUUBUTUUABDUUEUUCUT
      UNUKVAVBVCAWNYAPQZWNXTPQZWQRQZUHZECTGBTZXAYHPQZXCXAYGPQZRQZUHZUCCTUDBTZNU
      UJXAYNPQZUULXCRQZUHZUCCTUDBTAUUOUUIUURXAYAPQZXAXTPQZXCRQZUHGEUDUCBCXKUUFU
      USUUHUVAWNXAYAPULXKUUGUUTWQXCRWNXAXTPULXLUJUKYRUUSUUPUVAUUQYRYAYNXAPYSUOY
      RUUTUULXCRXTYGXAPVDVKUKVEAUURUUNUDUCBCAXMYTUGZUGZUUPUUKUUQUUMUVCYNYHXAPAY
      TYNYHUHXMUUDVFUOUVCUULXCUVCXAYGAXMXAUQSYTXQVGZAYTYGUQSXMUUBVFUTUVCXADUVDA
      XSUVBJUPUTUNUKVHVBVCVIWKWCVSWKVRWCAVRUQSZWJABCHIUTZUPAWJURUSAVSUQSZWJABDH
      JUTZUPUNAWAWMUHWJAVTWLBPXOUOUPVJVLAWHUBVSABCDFWGGHIJKMOVIVLAUVEUVGWAUQSWB
      WFWIUGVMUVFUVHABVTHACDIJVNUTVRVSWAUAUBVOVPVQ $.
  $}

  ${
    $d A d e $.  $d B d e $.  $d C d e $.  $d X d e $.  $d Y d e $.
    $d Z d e $.
    nadddilem3.1 $e |- ( ph -> A e. On ) $.
    nadddilem3.2 $e |- ( ph -> B e. On ) $.
    nadddilem3.3 $e |- ( ph -> C e. On ) $.
    nadddilem3.4 $e |- ( ph -> X e. A ) $.
    nadddilem3.5 $e |- ( ph -> Y e. ( B +no C ) ) $.
    nadddilem3.6 $e |- ( ph -> Z e. B ) $.
    nadddilem3.7 $e |- ( ph -> Y C_ ( Z +no C ) ) $.
    nadddilem3.8 $e |- ( ph -> A. d e. A
    ( d .no ( B +no C ) ) = ( ( d .no B ) +no ( d .no C ) ) ) $.
    nadddilem3.9 $e |- ( ph -> A. e e. B
    ( A .no ( e +no C ) ) = ( ( A .no e ) +no ( A .no C ) ) ) $.
    nadddilem3.10 $e |- ( ph -> A. d e. A A. e e. B
    ( d .no ( e +no C ) ) = ( ( d .no e ) +no ( d .no C ) ) ) $.
    $( Lemma for ~ nadddi .  Prove a subcase of the forward implication.
       (Contributed by Scott Fenton, 3-Aug-2026.) $)
    nadddilem3 $p |- ( ph -> ( ( X .no ( B +no C ) ) +no ( A .no Y ) )
    e. ( ( ( A .no B ) +no ( A .no C ) ) +no ( X .no Y ) ) ) $=
      ( co cnadd cnmul wcel con0 onelond naddcld onelssd nmuladdss syl222anc wb
      nmulcld naddss2 syl3anc mpbid nmuladdel syl22anc naddcomd eleqtrrd oveq1d
      naddel2 naddassd 3eqtr3d eleqtrd wceq oveq1 oveq12d eqeq12d rspcdva eqtrd
      wss cv oveq2d oveq2 rspc2dv 3eltr4d naddel1 nadd32d 3eltr3d sseldd eqtr4d
      mpbird ) AFCDUATZUBTZBGUBTZUATZBCUBTZBDUBTZUATZFGUBTZUATZUCZWEBHUBTZUATZW
      JWLUATZUCZAWMWFBHDUATZUBTZUATZWIUATZWNAWMWFWQWIUATZUATZWSAWFFWPUBTZWDUATZ
      UATZXAWMAXCWTVJZXDXAVJZABUDUCZWPUDUCFUDUCGUDUCFBVJGWPVJXEJAHDACHKOUEZLUFZ
      ABFJMUEZAWBGACDKLUFZNUEZABFJMUGPBWPFGUHUIAXCUDUCWTUDUCWFUDUCXEXFUJAXBWDAF
      WPXJXIUKZABGJXLUKZUFAWQWIABWPJXIUKZAFGXJXLUKZUFABCJKUKZXCWTWFULUMUNAWCWLU
      ATZWDUATZWFXBUATZWDUATZWMXDAXRXTUCZXSYAUCZAFDUBTZFCUBTZWLUATZUATZFHUBTZYD
      WFUATUATZXRXTAYGYDYHWFUATZUATZYIAYFYJUCZYGYKUCZAYFWFYHUATZYJAXGCUDUCFBUCH
      CUCYFYNUCJKMOBCFHUOUPAYHWFAFHXJXHUKZXQUQURAYFUDUCYJUDUCYDUDUCYLYMUJAYEWLA
      FCXJKUKZABHJXHUKZUFAYHWFYOXQUFAFDXJLUKZYFYJYDUTUMUNAYDYHUATZWFUATYHYDUATZ
      WFUATZYKYIAYSYTWFUAAYDYHYRYOUQUSAYDYHWFYRYOXQVAAYHYDWFYOYRXQVAZVBVCAXRYDY
      EUATZWLUATYGAWCUUCWLUAAWCYEYDUATZUUCAIVKZWBUBTZUUECUBTZUUEDUBTZUATZVDWCUU
      DVDIBFUUEFVDZUUFWCUUIUUDUUEFWBUBVEUUJUUGYEUUHYDUAUUEFCUBVEUUEFDUBVEZVFVGQ
      MVHAYEYDYPYRUQVIUSAYDYEWLYRYPYQVAVIAXTXBWFUATZYIAWFXBXQXMUQAUULUUAYIAXBYT
      WFUAAUUEEVKZDUATZUBTZUUEUUMUBTZUUHUATZVDXBYTVDFUUNUBTZFUUMUBTZYDUATZVDIEF
      HBCUUJUUOUURUUQUUTUUEFUUNUBVEUUJUUPUUSUUHYDUAUUEFUUMUBVEUUKVFVGUUMHVDZUUR
      XBUUTYTUVAUUNWPFUBUUMHDUAVEZVLUVAUUSYHYDUAUUMHFUBVMUSVGSMOVNUSUUBVIVIVOAX
      RUDUCXTUDUCWDUDUCYBYCUJAWCWLAFWBXJXKUKZYQUFAWFXBXQXMUFXNXRXTWDVPUMUNAWCWL
      WDUVCYQXNVQAWFXBWDXQXMXNVAVRVSAWFWQWIXQXOXPVAURAWSWHWLUATZWIUATWNAWRUVDWI
      UAAWRWFWGWLUATZUATUVDAWQUVEWFUAAWQWLWGUATZUVEABUUNUBTZBUUMUBTZWGUATZVDWQU
      VFVDECHUVAUVGWQUVIUVFUVAUUNWPBUBUVBVLUVAUVHWLWGUAUUMHBUBVMUSVGROVHAWLWGYQ
      ABDJLUKZUQVIVLAWFWGWLXQUVJYQVAVTUSAWHWLWIAWFWGXQUVJUFZYQXPVQVIVCAWEUDUCWJ
      UDUCWLUDUCWKWOUJAWCWDUVCXNUFAWHWIUVKXPUFYQWEWJWLVPUMWA $.
  $}

  ${
    $d ph p q x y z w $.  $d A d e f p q x y z w $.  $d B d e f p q x y z w $.
    $d C d e f p q x y z w $.
    nadddilem4.1 $e |- ( ph -> A e. On ) $.
    nadddilem4.2 $e |- ( ph -> B e. On ) $.
    nadddilem4.3 $e |- ( ph -> C e. On ) $.
    nadddilem4.4 $e |- ( ph -> A. d e. A
    ( d .no ( B +no C ) ) = ( ( d .no B ) +no ( d .no C ) ) ) $.
    nadddilem4.5 $e |- ( ph -> A. e e. B
    ( A .no ( e +no C ) ) = ( ( A .no e ) +no ( A .no C ) ) ) $.
    nadddilem4.6 $e |- ( ph -> A. f e. C
    ( A .no ( B +no f ) ) = ( ( A .no B ) +no ( A .no f ) ) ) $.
    nadddilem4.7 $e |- ( ph -> A. d e. A A. e e. B
    ( d .no ( e +no C ) ) = ( ( d .no e ) +no ( d .no C ) ) ) $.
    nadddilem4.8 $e |- ( ph -> A. d e. A A. f e. C
    ( d .no ( B +no f ) ) = ( ( d .no B ) +no ( d .no f ) ) ) $.
    $( Lemma for ~ nadddi .  Prove the forward implication.  (Contributed by
       Scott Fenton, 3-Aug-2026.) $)
    nadddilem4 $p |- ( ph ->
    ( A .no ( B +no C ) ) C_ ( ( A .no B ) +no ( A .no C ) ) ) $=
      ( cnadd co cnmul wcel wral vx vy vz vw vq vp cv wa simprr wrex wo con0 wb
      wss naddcld adantr onelond ltnadd syl3anc ad2antrr simplrl simplrr simprl
      wceq nadddilem3 rexlimdvaa naddcomd eleqtrd sseqtrd oveq1 oveq12d eqeq12d
      weq cbvralvw oveq2d simpr nmulcld ralbidva bitrid mpbid cbvral2vw adantrl
      adantrr 2ralbidva oveq1d 3eltr4d jaod sylbid mpd ralrimivva nmulle mpbird
      oveq2 ) ABCDPQZRQBCRQZBDRQZPQZUNZUAUGZWNRQZBUBUGZRQZPQZWQWSXARQZPQZSZUBWN
      TUABTZAXFUAUBBWNAWSBSZXAWNSZUHZUHZXIXFAXHXIUIZXKXIXAUCUGZDPQUNZUCCUJZXACU
      DUGZPQZUNZUDDUJZUKZXFXKXAULSCULSZDULSZXIXTUMXKWNXAAWNULSZXJACDIJUOZUPXLUQ
      AYAXJIUPAYBXJJUPXACDUCUDURUSXKXOXFXSXKXNXFUCCXKXMCSZXNUHZUHBCDEWSXAXMGABU
      LSZXJYFHUTAYAXJYFIUTAYBXJYFJUTAXHXIYFVAAXHXIYFVBXKYEXNVCXKYEXNUIAGUGZWNRQ
      ZYHCRQZYHDRQZPQZVDZGBTZXJYFKUTABEUGZDPQZRQBYORQWPPQVDECTXJYFLUTAYHYPRQYHY
      ORQYKPQVDECTGBTXJYFNUTVEVFXKXRXFUDDXKXPDSZXRUHZUHZWSDCPQZRQZXBPQWPWOPQZXD
      PQXCXEYSBDCUEWSXAXPUFAYGXJYRHUTAYBXJYRJUTZAYAXJYRIUTZAXHXIYRVAYSXAWNYTAXH
      XIYRVBYSCDUUDUUCVGZVHXKYQXRVCZYSXAXQXPCPQXKYQXRUIYSCXPUUDYSDXPUUCUUFUQVGV
      IAUFUGZYTRQZUUGDRQZUUGCRQZPQZVDZUFBTZXJYRAYNUUMKYNUUGWNRQZUUJUUIPQZVDZUFB
      TAUUMYMUUPGUFBGUFVMZYIUUNYLUUOYHUUGWNRVJUUQYJUUJYKUUIPYHUUGCRVJZYHUUGDRVJ
      VKVLVNAUUPUULUFBAUUGBSZUHZUUNUUHUUOUUKUUTWNYTUUGRAWNYTVDUUSACDIJVGUPVOUUT
      UUJUUIUUTUUGCUUTBUUGAYGUUSHUPAUUSVPUQZAYAUUSIUPVQZUUTUUGDUVAAYBUUSJUPVQVG
      VLVRVSVTUTABUEUGZCPQZRQZBUVCRQZWOPQZVDZUEDTZXJYRABCFUGZPQZRQZWOBUVJRQZPQZ
      VDZFDTZUVIMUVPBCUVCPQZRQZWOUVFPQZVDZUEDTAUVIUVOUVTFUEDFUEVMZUVLUVRUVNUVSU
      WAUVKUVQBRUVJUVCCPWMZVOUWAUVMUVFWOPUVJUVCBRWMVOVLVNAUVTUVHUEDAUVCDSZUHZUV
      RUVEUVSUVGUWDUVQUVDBRUWDCUVCAYAUWCIUPUWDDUVCAYBUWCJUPAUWCVPUQZVGZVOUWDWOU
      VFAWOULSZUWCABCHIVQZUPUWDBUVCAYGUWCHUPUWEVQVGVLVRVSVTUTAUUGUVDRQZUUGUVCRQ
      ZUUJPQZVDZUEDTUFBTZXJYRAYHUVKRQZYJYHUVJRQZPQZVDZFDTGBTZUWMOUWRUUGUVQRQZUU
      JUWJPQZVDZUEDTUFBTAUWMUWQUXAUUGUVKRQZUUJUUGUVJRQZPQZVDGFUFUEBDUUQUWNUXBUW
      PUXDYHUUGUVKRVJUUQYJUUJUWOUXCPUURYHUUGUVJRVJVKVLUWAUXBUWSUXDUWTUWAUVKUVQU
      UGRUWBVOUWAUXCUWJUUJPUVJUVCUUGRWMVOVLWAAUXAUWLUFUEBDAUUSUWCUHUHZUWSUWIUWT
      UWKUXEUVQUVDUUGRAUWCUVQUVDVDUUSUWFWBVOUXEUUJUWJAUUSUUJULSUWCUVBWCUXEUUGUV
      CAUUSUUGULSUWCUVAWCAUWCUVCULSUUSUWEWBVQVGVLWDVSVTUTVEYSWTUUAXBPYSWNYTWSRU
      UEVOWEYSWQUUBXDPYSWOWPAUWGXJYRUWHUTAWPULSXJYRABDHJVQZUTVGWEWFVFWGWHWIWJAY
      GYCWQULSWRXGUMHYDAWOWPUWHUXFUOBWNWQUAUBWKUSWL $.
  $}

  ${
    $d A a b c d e f $.  $d B a b c d e f $.  $d C a b c d e f $.
    $( Natural multiplication distributes over natural addition.  (Contributed
       by Scott Fenton, 27-Jul-2026.) $)
    nadddi $p |- ( ( A e. On /\ B e. On /\ C e. On ) ->
    ( A .no ( B +no C ) ) = ( ( A .no B ) +no ( A .no C ) ) ) $=
      ( va vb vd ve vf cv cnadd co cnmul wceq oveq1 eqeq12d oveq2d oveq2 oveq1d
      w3a wral vc weq oveq12d con0 wcel wa simpl1 simpl2 simpl3 simpr21 simpr23
      simpr3 simpr12 simpr13 nadddilem4 nadddilem2 eqssd ex on3ind ) DIZEIZUAIZ
      JKZLKZUTVALKZUTVBLKZJKZMZFIZVCLKZVIVALKZVIVBLKZJKZMZVIGIZVBJKZLKZVIVOLKZV
      LJKZMZVIVOHIZJKZLKZVRVIWALKZJKZMZUTWBLKZUTVOLKZUTWALKZJKZMZUTVAWAJKZLKZVE
      WIJKZMZVIWLLKZVKWDJKZMZUTVPLKZWHVFJKZMZAVCLKZAVALKZAVBLKZJKZMABVBJKZLKZAB
      LKZXDJKZMABCJKZLKZXHACLKZJKZMGHABCDEUAFDFUBZVDVJVGVMUTVIVCLNXNVEVKVFVLJUT
      VIVALNUTVIVBLNUCOEGUBZVJVQVMVSXOVCVPVILVAVOVBJNPXOVKVRVLJVAVOVILQZROUAHUB
      ZVQWCVSWEXQVPWBVILVBWAVOJQZPXQVLWDVRJVBWAVILQPOXNWGWCWJWEUTVIWBLNXNWHVRWI
      WDJUTVIVOLNUTVIWALNUCOXOWMWGWNWJXOWLWBUTLVAVOWAJNZPXOVEWHWIJVAVOUTLQROXOW
      PWCWQWEXOWLWBVILXSPXOVKVRWDJXPROXQWSWGWTWJXQVPWBUTLXRPXQVFWIWHJVBWAUTLQPO
      UTAMZVDXBVGXEUTAVCLNXTVEXCVFXDJUTAVALNUTAVBLNUCOVABMZXBXGXEXIYAVCXFALVABV
      BJNPYAXCXHXDJVABALQROVBCMZXGXKXIXMYBXFXJALVBCBJQPYBXDXLXHJVBCALQPOUTUDUEZ
      VAUDUEZVBUDUEZSZWFHVBTGVATFUTTZVTGVATFUTTZWRHVBTFUTTZSZVNFUTTZWKHVBTGVATZ
      XAGVATZSZWOHVBTZSZVHYFYPUFZVDVGYQUTVAVBGHFYCYDYEYPUGZYCYDYEYPUHZYCYDYEYPU
      IZYKYLYMYJYOYFUJZYKYLYMYJYOYFUKZYFYJYNYOULZYGYHYIYNYOYFUMZYGYHYIYNYOYFUNZ
      UOYQUTVAVBGHFYRYSYTUUAUUBUUCUUDUUEUPUQURUS $.
  $}

  ${
    nadddid.1 $e |- ( ph -> A e. On ) $.
    nadddid.2 $e |- ( ph -> B e. On ) $.
    nadddid.3 $e |- ( ph -> C e. On ) $.
    $( Natural multiplication distributes over natural addition.  Deduction
       form.  (Contributed by Scott Fenton, 3-Aug-2026.) $)
    nadddid $p |- ( ph ->
    ( A .no ( B +no C ) ) = ( ( A .no B ) +no ( A .no C ) ) ) $=
      ( con0 wcel cnadd co cnmul wceq nadddi syl3anc ) ABHICHIDHIBCDJKLKBCLKBDL
      KJKMEFGBCDNO $.

    $( Natural multiplication distributes over natural addition.  Deduction
       form.  (Contributed by Scott Fenton, 3-Aug-2026.) $)
    nadddird $p |- ( ph ->
    ( ( A +no B ) .no C ) = ( ( A .no C ) +no ( B .no C ) ) ) $=
      ( cnadd co cnmul nadddid naddcld nmulcomd oveq12d 3eqtr4d ) ADBCHIZJIDBJI
      ZDCJIZHIPDJIBDJIZCDJIZHIADBCGEFKAPDABCEFLGMASQTRHABDEGMACDFGMNO $.
  $}

$( (End of Scott Fenton's mathbox.) $)
