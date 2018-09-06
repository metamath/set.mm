$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Probability
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Probability Theory
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)
  $c Prob $. $( The class of probability measures $)

  $( Extend class notation to include the class of probability measures. $)
  cprb $a class Prob $.

  $( Define the class of probability measures as the set of measures with total
     measure 1.  (Contributed by Thierry Arnoux, 14-Sep-2016.) $)
  df-prob $a |- Prob = { p e. U. ran measures | ( p ` U. dom p ) = 1 } $.

  ${
    $d p P $.
    $( The property of being a probability measure (Contributed by Thierry
       Arnoux, 8-Dec-2016.) $)
    elprob $p |- ( P e. Prob <->
      ( P e. U. ran measures /\ ( P ` U. dom P ) = 1 ) ) $=
      ( vp cv cdm cuni cfv c1 wceq cmeas crn cprb id dmeq unieqd fveq12d eqeq1d
      df-prob elrab2 ) BCZDZEZSFZGHADZEZAFZGHBAIJEKSAHZUBUEGUFUAUDSAUFLUFTUCSAM
      NOPBQR $.
  $}

  $( A probability measure is a measure on its domain.  (Contributed by Thierry
     Arnoux, 23-Dec-2016.) $)
  domprobmeas $p |- ( P e. Prob -> P e. ( measures ` dom P ) ) $=
    ( cprb wcel cmeas crn cuni cdm cfv c1 wceq elprob simplbi measbasedom sylib
    ) ABCZADEFCZAAGZDHCOPQFAHIJAKLAMN $.

  $( The domain of a probability measure is a sigma-algebra.  (Contributed by
     Thierry Arnoux, 23-Dec-2016.) $)
  domprobsiga $p |- ( P e. Prob -> dom P e. U. ran sigAlgebra ) $=
    ( cprb wcel cdm cmeas cfv csiga crn cuni domprobmeas measbase syl ) ABCAADZ
    EFCMGHICAJMAKL $.

  $( The probability of the universe set is 1 (Second axiom of Kolmogorov)
     (Contributed by Thierry Arnoux, 8-Dec-2016.) $)
  probtot $p |- ( P e. Prob -> ( P ` U. dom P ) = 1 ) $=
    ( cprb wcel cmeas crn cuni cdm cfv c1 wceq elprob simprbi ) ABCADEFCAGFAHIJ
    AKL $.

  ${
    $d x y P $.
    $( A probability is bounded in [ 0 , 1 ] (First axiom of Kolmogorov)
       (Contributed by Thierry Arnoux, 25-Dec-2016.) $)
    prob01 $p |- ( ( P e. Prob /\ A e. dom P ) -> ( P ` A ) e. ( 0 [,] 1 ) ) $=
      ( cprb wcel cdm wa cfv cxr cc0 cle wbr c1 w3a cicc cpnf cmeas cuni adantr
      co wb domprobmeas measvxrge0 sylan elxrge0 sylib simpr csiga crn measbase
      unielsiga wss elssuni adantl measssd probtot breq2d mpbid df-3an sylanbrc
      3syl 0xr 1re rexri elicc1 mp2an sylibr ) BCDZABEZDZFZABGZHDZIVKJKZVKLJKZM
      ZVKILNSDZVJVLVMFZVNVOVJVKIONSDZVQVGBVHPGDZVIVRBUAZAVHBUBUCVKUDUEVJVKVHQZB
      GZJKZVNVJAWAVHBVGVSVIVTRZVGVIUFVJVSVHUGUHQDWAVHDWDVHBUIVHUJUTVIAWAUKVGAVH
      ULUMUNVGWCVNTVIVGWBLVKJBUOUPRUQVLVMVNURUSIHDLHDVPVOTVALVBVCILVKVDVEVF $.
  $}

  $( The probability of the empty event set is 0.  (Contributed by Thierry
     Arnoux, 25-Dec-2016.) $)
  probnul $p |- ( P e. Prob -> ( P ` (/) ) = 0 ) $=
    ( cprb wcel cdm cmeas cfv c0 cc0 wceq domprobmeas measvnul syl ) ABCAADZEFC
    GAFHIAJMAKL $.

  ${
    $d x P $.
    unveldomd.1 $e |- ( ph -> P e. Prob ) $.
    $( The universe is an element of the domain of the probability, the
       universe (entire probability space) being ` U. dom P ` in our
       construction.  (Contributed by Thierry Arnoux, 22-Jan-2017.) $)
    unveldomd $p |- ( ph -> U. dom P e. dom P ) $=
      ( cprb wcel cdm csiga crn cuni cfv domprobsiga sgon baselsiga 4syl ) ABDE
      BFZGHIEOOIZGJEPOECBKOLPOMN $.
  $}

  ${
    $d x P $.
    $( The universe is an element of the domain of the probability, the
       universe (entire probability space) being ` U. dom P ` in our
       construction.  (Contributed by Thierry Arnoux, 22-Jan-2017.) $)
    unveldom $p |- ( P e. Prob -> U. dom P e. dom P ) $=
      ( cprb wcel id unveldomd ) ABCZAFDE $.
  $}

  ${
    $d x P $.
    $( The empty set is an element of the domain of the probability.
       (Contributed by Thierry Arnoux, 22-Jan-2017.) $)
    nuleldmp $p |- ( P e. Prob -> (/) e. dom P ) $=
      ( cprb wcel cdm csiga crn cuni c0 domprobsiga 0elsiga syl ) ABCADZEFGCHLC
      AILJK $.
  $}

  ${
    $d x z A $.  $d x z P $.
    $( The probability of the union of a countable disjoint set of events is
       the sum of their probabilities.  (Third axiom of Kolmogorov) Here, the
       ` sum_ ` construct cannot be used as it can handle infinite indexing set
       only if they are subsets of ` ZZ ` , which is not the case here.
       (Contributed by Thierry Arnoux, 25-Dec-2016.) $)
    probcun $p |- ( ( P e. Prob /\ A e. ~P dom P /\ ( A ~<_ om
      /\ Disj_ x e. A x ) ) -> ( P ` U. A ) = sum* x e. A ( P ` x ) ) $=
      ( cprb wcel cdm cmeas cfv cpw com cdom cv wdisj wa cuni cesum domprobmeas
      wbr wceq measvun syl3an1 ) CDECCFZGHEBUBIEBJKRABALZMNBOCHBUCCHAPSCQABUBCT
      UA $.
  $}

  ${
    $d x A $.  $d x B $.  $d x P $.
    $( The probability of the union two incompatible events is the sum of their
       probabilities.  (Contributed by Thierry Arnoux, 25-Dec-2016.) $)
    probun $p |- ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) ->
      ( ( A i^i B ) = (/) ->
                          ( P ` ( A u. B ) ) = ( ( P ` A ) + ( P ` B ) ) ) ) $=
      ( vx wcel c0 wceq cfv caddc co wa syl6eq sylan9eqr fveq2d 3ad2ant2 adantr
      cc0 syl2anc sseldi cr cprb cdm w3a cin wi simpll1 simplr simpr cdif disj3
      cun biimpi difeq1 difid eqtr2 syldan uneq12d unidm probnul oveq12d eqtr4d
      00id syl12anc ex wne cxad 3anass anbi1i df-3an bitr4i cpr cuni cv cpw com
      cesum cdom wbr wdisj simpl1 wss prssi prex elpw sylibr prct simp2l simp2r
      wb simp3 id disjprg syl3anc biimpar probcun syl112anc uniprg fveq2 adantl
      c1 cicc cpnf unitssxrge0 simp1 prob01 esumpr eqeq12d mpbid sylanb simpll2
      unitssre simpll3 rexadd eqtrd pm2.61dane ) CUAEZACUBZEZBXQEZUCZABUDFGZABU
      KZCHZACHZBCHZIJZGZUEABXTABGZKZYAYGYIYAKXPYHYAYGXPXRXSYHYAUFXTYHYAUGYIYAUH
      XPYHYAKZKZYCQYFYJXPYCFCHZQYJYBFCYJYBFFUKFYJAFBFYAYHAABUIZFYAAYMGABUJULYHY
      MBBUIFABBUMBUNLMZYHYAAFGBFGYNABFUOUPZUQFURLNCUSZMYKYFQQIJQYKYDQYEQIYJXPYD
      YLQYJAFCYNNYPMYJXPYEYLQYJBFCYONYPMUTVBLVAVCVDXTABVEZKZYAYGYRYAKZYCYDYEVFJ
      ZYFYRXPXRXSKZYQUCZYAYCYTGZYRXPUUAKZYQKUUBXTUUDYQXPXRXSVGVHXPUUAYQVIVJUUBY
      AKZABVKZVLZCHZUUFDVMZCHZDVPZGZUUCUUEXPUUFXQVNEZUUFVOVQVRZDUUFUUIVSZUULXPU
      UAYQYAVTUUEUUFXQWAZUUMUUBUUPYAUUAXPUUPYQABXQWBOPUUFXQABWCWDWEUUBUUNYAUUAX
      PUUNYQABXQXQWFOPUUBUUOYAUUBXRXSYQUUOYAWIXPXRXSYQWGZXPXRXSYQWHZXPUUAYQWJZD
      ABUUIABXQUUIAGZWKUUIBGZWKWLWMWNDUUFCWOWPUUBUULUUCWIYAUUBUUHYCUUKYTUUAXPUU
      HYCGYQUUAUUGYBCABXQXQWQNOUUBABUUJYDDYEXQXQUUTUUJYDGUUBUUIACWRWSUVAUUJYEGU
      UBUUIBCWRWSUUQUURUUBQWTXAJZQXBXAJZYDXCUUBXPXRYDUVBEZXPUUAYQXDZUUQACXEZRSU
      UBUVBUVCYEXCUUBXPXSYEUVBEZUVEUURBCXEZRSUUSXFXGPXHXIYSYDTEYETEYTYFGYSUVBTY
      DXKYSXPXRUVDXPXRXSYQYAUFZXPXRXSYQYAXJUVFRSYSUVBTYEXKYSXPXSUVGUVIXPXRXSYQY
      AXLUVHRSYDYEXMRXNVDXO $.
  $}

  $( The probability of the difference of two event sets (Contributed by
     Thierry Arnoux, 12-Dec-2016.) $)
  probdif $p |- ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) ->
    ( P ` ( A \ B ) ) = ( ( P ` A ) - ( P ` ( A i^i B ) ) ) ) $=
    ( cprb wcel w3a cfv cin cmin co cdif wceq syl3an1 c0 wss cc unitsscn prob01
    syl2anc sseldi cdm caddc cun inundif fveq2i simp1 cuni domprobsiga inelsiga
    csiga crn difelsiga indif2 inss2 ssinss1 ax-mp ssdif0 mpbi eqtri probun mpi
    syl3anc syl5eqr oveq1d cc0 c1 cicc pncan2d eqtr2d ) CDEZACUAZEZBVKEZFZACGZA
    BHZCGZIJVQABKZCGZUBJZVQIJVSVNVOVTVQIVNVOVPVRUCZCGZVTWAACABUDUEVNVJVPVKEZVRV
    KEZWBVTLZVJVLVMUFZVJVKUJUKUGEZVLVMWCCUHZABVKUIMZVJWGVLVMWDWHABVKULMZVJWCWDF
    VPVRHZNLWEWKVPAHZBKZNVPABUMWLBOZWMNLVPBOWNABUNVPABUOUPWLBUQURUSVPVRCUTVAVBV
    CVDVNVQVSVNVEVFVGJZPVQQVNVJWCVQWOEWFWIVPCRSTVNWOPVSQVNVJWDVSWOEWFWJVRCRSTVH
    VI $.

  $( A probability law is increasing with regard to event set inclusion.
     (Contributed by Thierry Arnoux, 10-Feb-2017.) $)
  probinc $p |- ( ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) /\ A C_ B ) ->
    ( P ` A ) <_ ( P ` B ) ) $=
    ( cprb wcel cdm w3a wss wa cmeas cfv simpl1 domprobmeas simpl2 simpl3 simpr
    syl measssd ) CDEZACFZEZBTEZGZABHZIZABTCUESCTJKESUAUBUDLCMQSUAUBUDNSUAUBUDO
    UCUDPR $.

  $( The probability of the complement of a set.  That is, the probability that
     the event ` A ` does not occur.  (Contributed by Thierry Arnoux,
     15-Dec-2016.) $)
  probdsb $p |- ( ( P e. Prob /\ A e. dom P ) ->
    ( P ` ( U. dom P \ A ) ) = ( 1 - ( P ` A ) ) ) $=
    ( cprb wcel cdm wa cuni cdif cfv cmin co wceq simpl unveldomd simpr probdif
    cin c1 syl3anc probtot wss elssuni dfss1 sylib fveq2d oveqan12d eqtrd ) BCD
    ZABEZDZFZUIGZAHBIZULBIZULAQZBIZJKZRABIZJKUKUHULUIDUJUMUQLUHUJMZUKBUSNUHUJOU
    LABPSUHUJUNRUPURJBTUJUOABUJAULUAUOALAUIUBAULUCUDUEUFUG $.

  ${
    probmeasd.1 $e |- ( ph -> P e. Prob ) $.
    $( A probability measure is a measure.  (Contributed by Thierry Arnoux,
       2-Feb-2017.) $)
    probmeasd $p |- ( ph -> P e. U. ran measures ) $=
      ( cdm cmeas cfv wcel crn cuni cprb domprobmeas syl measbasedom sylibr ) A
      BBDEFGZBEHIGABJGOCBKLBMN $.

    ${
      probvalrnd.1 $e |- ( ph -> A e. dom P ) $.
      $( The value of a probability is a real number.  (Contributed by Thierry
         Arnoux, 2-Feb-2017.) $)
      probvalrnd $p |- ( ph -> ( P ` A ) e. RR ) $=
        ( cc0 c1 cicc co cr cfv unitssre cprb wcel cdm prob01 syl2anc sseldi )
        AFGHIZJBCKZLACMNBCONTSNDEBCPQR $.
    $}

    $( The probability of the universe set is finite.  (Contributed by Thierry
       Arnoux, 2-Feb-2017.) $)
    probtotrnd $p |- ( ph -> ( P ` U. dom P ) e. RR ) $=
      ( cdm cuni unveldomd probvalrnd ) ABDEBCABCFG $.
  $}

  ${
    $d b c A $.  $d b c B $.  $d b c P $.  $d c b ph $.
    totprobd.1 $e |- ( ph -> P e. Prob ) $.
    totprobd.2 $e |- ( ph -> A e. dom P ) $.
    totprobd.3 $e |- ( ph -> B e. ~P dom P ) $.
    totprobd.4 $e |- ( ph -> U. B = U. dom P ) $.
    totprobd.5 $e |- ( ph -> B ~<_ om ) $.
    totprobd.6 $e |- ( ph -> Disj_ b e. B b ) $.
    $( Law of total probability, deduction form.  (Contributed by Thierry
       Arnoux, 25-Dec-2016.) $)
    totprobd $p |- ( ph -> ( P ` A ) = sum* b e. B ( P ` ( b i^i A ) ) ) $=
      ( vc cuni cin cfv wceq wcel syl syl2anc adantr cesum wss elssuni sseqtr4d
      cdm dfss1 sylib fveq2d cmpt cmeas cpw com cdom wbr wdisj cprb domprobmeas
      cv measinb measvun syl112anc c1 cicc co eqidd wa simpr ineq1d domprobsiga
      cc0 crn sigaclcu syl3anc inelsiga prob01 fvmptd elelpwi esumeq2dv 3eqtr3d
      csiga eqtr3d ) ACMZBNZDOZBDOCEURZBNZDOZEUAZAWCBDABWBUBWCBPABDUEZMZWBABWIQ
      ZBWJUBGBWIUCRIUDBWBUFUGUHAWBLWILURZBNZDOZUIZOZCWEWOOZEUAZWDWHAWOWIUJOZQZC
      WIUKQZCULUMUNZECWEUOWPWRPADWSQZWKWTADUPQZXCFDUQRGLBWIDUSSHJKECWIWOUTVAALW
      BWNWDWIWOVJVBVCVDZAWOVEAWLWBPZVFZWMWCDXGWLWBBAXFVGVHUHAWIVTVKMQZXAXBWBWIQ
      ZAXDXHFDVIRZHJCWIVLVMZAXDWCWIQZWDXEQFAXHXIWKXLXJXKGWBBWIVNVMWCDVOSVPACWQW
      GEAWECQZVFZLWEWNWGWIWOXEXNWOVEXNWLWEPZVFZWMWFDXPWLWEBXNXOVGVHUHXNXMXAWEWI
      QZAXMVGAXAXMHTWECWIVQSZXNXDWFWIQZWGXEQAXDXMFTXNXHXQWKXSAXHXMXJTXRAWKXMGTW
      EBWIVNVMWFDVOSVPVRVSWA $.
  $}

  ${
    $d b c A $.  $d b c B $.  $d b c P $.
    $( Law of total probability (Contributed by Thierry Arnoux,
       25-Dec-2016.) $)
    totprob $p |- ( ( P e. Prob /\ A e. dom P /\
      ( U. B = U. dom P /\ B e. ~P dom P /\ ( B ~<_ om /\ Disj_ b e. B b ) ) )
      -> ( P ` A ) = sum* b e. B ( P ` ( b i^i A ) ) ) $=
      ( vc cprb wcel cdm cuni wceq cpw com cdom wbr cv wdisj w3a cfv cin cesum
      wa simp1 simp2 simp32 simp31 simp33l cbvdisjv sylib totprobd ineq1 fveq2d
      simp33r id cbvesumv syl6eqr ) CFGZACHZGZBIUQIJZBUQKGZBLMNZDBDOZPZUAZQZQZA
      CRBEOZASZCRZETBVBASZCRZDTVFABCEUPURVEUBUPURVEUCUPURUSUTVDUDUPURUSUTVDUEVA
      VCUSUTUPURUFVFVCEBVGPVAVCUSUTUPURULDEBVBVGVBVGJZUMUGUHUIBVKVIDEVLVJVHCVBV
      GAUJUKUNUO $.
  $}

  ${
    $d x M $.  $d x y S $.
    $( Build a probability measure from a finite measure (Contributed by
       Thierry Arnoux, 17-Dec-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    probfinmeasbOLD $p |- ( ( M e. ( measures ` S ) /\ ( M ` U. S ) e. RR+ )
                   -> ( x e. S |-> ( ( M ` x ) /e ( M ` U. S ) ) ) e. Prob ) $=
      ( vy cmeas cfv wcel cuni crp wa cv cxdiv co crn wceq cvv wral fveq2i cpw
      c1 cmpt cdm cprb measdivcstOLD ovex rgenw dmmptg ax-mp measbasedom sylibr
      syl6eleqr unieqi csiga measbase cdif com cdom wbr wi wss isrnsigau simprd
      w3a simp1d syl id rpxdivcld anim12i fveq2 oveq1d eqid fvmptg cc0 wne rpre
      cr rpne0 xdivid syl2anc adantl eqtrd syl5eq elprob sylanbrc ) CBEFZGZBHZC
      FZIGZJZABAKZCFZWHLMZUAZENHGZWNUBZHZWNFZTOWNUCGWJWNWPEFZGWOWJWNWEWSAWHBCUD
      WPBEWMPGZABQWPBOWTABWLWHLUEUFABWMPUGUHZRUKWNUIUJWJWRWGWNFZTWQWGWNWPBXAULR
      WJXBWHWHLMZTWJWGBGZXCIGZJXBXCOWFXDWIXEWFBUMNHGZXDBCUNXFXDWGDKZUOBGDBQZXGU
      PUQURXGHBGUSDBSQZXFBWGSUTXDXHXIVCDBVAVBVDVEWIWHWHWIVFZXJVGVHAWGWMXCBIWNWK
      WGOWLWHWHLWKWGCVIVJWNVKVLVEWIXCTOZWFWIWHVPGWHVMVNXKWHVOWHVQWHVRVSVTWAWBWN
      WCWD $.
  $}

  ${
    $( Build a probability measure from a finite measure (Contributed by
       Thierry Arnoux, 31-Jan-2017.) $)
    probfinmeasb $p |- ( ( M e. ( measures ` S ) /\ ( M ` U. S ) e. RR+ ) ->
      ( M oFC /e ( M ` U. S ) ) e. Prob ) $=
      ( cmeas cfv wcel cuni crp wa cxdiv cofc co crn cdm c1 wceq wfn adantr syl
      cprb fveq2d measdivcst csiga measfn measbase simpr ofcfn fndm measbasedom
      eleqtrrd sylibr unieqd unielsiga eqidd ofcval mpdan cr cc0 wne rpre rpne0
      xdivid syl2anc adantl 3eqtrd elprob sylanbrc ) BACDZEZAFZBDZGEZHZBVJIJKZC
      LFEZVMMZFZVMDZNOVMSEVLVMVOCDZEVNVLVMVGVRVJABUAVLVOACVLVMAPVOAOVLAVJIBUBLF
      ZGVHBAPVKABUCQZVHAVSEZVKABUDQZVHVKUEZUFAVMUGRZTUIVMUHUJVLVQVIVMDZVJVJIKZN
      VLVPVIVMVLVOAWDUKTVLVIAEZWEWFOVLWAWGWBAULRVLAVJVJIBVSGVIVTWBWCVLWGHVJUMUN
      UOVKWFNOZVHVKVJUPEVJUQURWHVJUSVJUTVJVAVBVCVDVMVEVF $.
  $}

  ${
    $d x y A $.  $d x y M $.  $d x y S $.
    $( Build a probability from a measure and a set with finite measure
       (Contributed by Thierry Arnoux, 25-Dec-2016.) $)
    probmeasb $p |- ( ( M e. ( measures ` S ) /\ A e. S /\ ( M ` A ) e. RR+ )
      -> ( x e. S |-> ( ( M ` ( x i^i A ) ) / ( M ` A ) ) ) e. Prob ) $=
      ( vy cmeas cfv wcel cin co cuni c1 wceq cc0 cpnf fveq2d adantr syl cr cxr
      crp w3a cv cdiv cmpt crn cdm cprb cxdiv simp1 simp2 measinb syl2anc simp3
      measdivcstOLD cicc eqidd simpr csiga measbase inelsiga syl3anc measvxrge0
      ineq1d fvmptd oveq1d wne cle wbr iccssxr sseldi rpred 0xr iccgelb mp3an12
      wa pnfxr wss inss2 measssd xrrege0 syl22anc rpne0d rexdiv eqtrd mpteq2dva
      wral rerpdivcld ralrimiva dmmptg eqcomd 3eltr3d measbasedom sylibr unieqd
      a1i rpcnd incom elssuni df-ss sylib syl5eq diveq1bd sgon baselsiga elprob
      4syl 1re sylanbrc ) DCFGZHZBCHZBDGZUAHZUBZACAUCZBIZDGZXMUDJZUEZFUFKHZXTUG
      ZKZXTGZLMXTUHHXOXTYBFGZHYAXOACXPECEUCZBIZDGZUEZGZXMUIJZUEZXJXTYEXOYIXJHZX
      NYLXJHXOXKXLYMXKXLXNUJZXKXLXNUKZEBCDULUMXKXLXNUNZAXMCYIUOUMXOACYKXSXOXPCH
      ZVPZYKXRXMUIJZXSYRYJXRXMUIYREXPYHXRCYINOUPJZYRYIUQYRYFXPMZVPZYGXQDUUBYFXP
      BYRUUAURVDPXOYQURZYRXKXQCHZXRYTHZXOXKYQYNQZYRCUSUFKHZYQXLUUDYRXKUUGUUFCDU
      TZRUUCXOXLYQYOQZXPBCVAVBZXQCDVCUMZVEVFYRXRSHZXMSHZXMNVGZYSXSMYRXRTHUUMNXR
      VHVIZXRXMVHVIUULYRYTTXRNOVJUUKVKYRXMXOXNYQYPQZVLZYRUUEUUOUUKNTHOTHUUEUUOV
      MVQNOXRVNVORYRXQBCDUUFUUJUUIXQBVRYRXPBVSWPVTXRXMWAWBZUUQYRXMUUPWCXRXMWDVB
      WEWFXOYEXJXOYBCFXOXSSHZACWGYBCMXOUUSACYRXRXMUURUUPWHWIACXSSWJRZPWKWLXTWMW
      NXOYDCKZXTGLXOYCUVAXTXOYBCUUTWOPXOAUVAXSLCXTSXOXTUQXOXPUVAMZVPZXRXMUVCXMX
      OXNUVBYPQWQXOUUNUVBXOXMYPWCQUVCXQBDUVCXQUVABIZBUVCXPUVABXOUVBURVDXOUVDBMZ
      UVBXOXLUVEYOXLUVDBUVAIZBUVABWRXLBUVAVRUVFBMBCWSBUVAWTXAXBRQWEPXCXOXKUUGCU
      VAUSGHUVACHYNUUHCXDUVACXEXGLSHXOXHWPVEWEXTXFXI $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Conditional Probabilities
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Conditional Probabililty builder $)
  $c cprob $.

  $( Extends class notation with the conditional probability builder. $)
  ccprob $a class cprob $.

  ${
    $d a b p $.
    $( Define the conditional probability.  (Contributed by Thierry Arnoux,
       14-Sep-2016.)  (Revised by Thierry Arnoux, 21-Jan-2017.) $)
    df-cndprob $a |- cprob = ( p e. Prob |->
      ( a e. dom p , b e. dom p |-> ( ( p ` ( a i^i b ) ) / ( p ` b ) ) ) ) $.
  $}

  ${
    $d a b p P $.  $d a b A $.  $d a b B $.
    $( The value of the conditional probability , i.e. the probability for the
       event ` A ` , given ` B ` , under the probability law ` P ` .
       (Contributed by Thierry Arnoux, 21-Jan-2017.) $)
    cndprobval $p |- ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) ->
    ( ( cprob ` P ) ` <. A , B >. ) = ( ( P ` ( A i^i B ) ) / ( P ` B ) ) ) $=
      ( va vb vp cprb wcel cdm ccprob cfv co cin cdiv cvv cmpt2 wceq a1i fveq1
      cv w3a cop df-ov cmpt df-cndprob dmeq oveq12d mpt2eq123dv adantl id dmexg
      mpt2exga syl2anc fvmptd 3ad2ant1 simprl simprr ineq12d fveq2d simp2 simp3
      wa ovex ovmpt2d syl5eqr ) CGHZACIZHZBVGHZUAZABUBCJKZKABVKLABMZCKZBCKZNLZA
      BVKUCVJDEABVGVGDTZETZMZCKZVQCKZNLZVOVKOVFVHVKDEVGVGWAPZQVIVFFCDEFTZIZWDVR
      WCKZVQWCKZNLZPZWBGJOJFGWHUDQVFFDEUERWCCQZWHWBQVFWIDEWDWDWGVGVGWAWCCUFZWJW
      IWEVSWFVTNVRWCCSVQWCCSUGUHUIVFUJVFVGOHZWKWBOHCGUKZWLDEVGVGWAOOULUMUNUOVJV
      PAQZVQBQZVBVBZVSVMVTVNNWOVRVLCWOVPAVQBVJWMWNUPVJWMWNUQZURUSWOVQBCWPUSUGVF
      VHVIUTVFVHVIVAVOOHVJVMVNNVCRVDVE $.
  $}

  $( An identity linking conditional probability and intersection.
     (Contributed by Thierry Arnoux, 13-Dec-2016.)  (Revised by Thierry Arnoux,
     21-Jan-2017.) $)
  cndprobin $p |- ( ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) /\
    ( P ` B ) =/= 0 ) ->
    ( ( ( cprob ` P ) ` <. A , B >. ) x. ( P ` B ) ) = ( P ` ( A i^i B ) ) ) $=
    ( cprb wcel cdm w3a cfv cc0 wne wa ccprob cmul co adantr cc unitsscn prob01
    cop sseldi cin cdiv wceq cndprobval oveq1d cicc simp1 csiga crn domprobsiga
    c1 cuni inelsiga syl3an1 syl2anc 3adant2 simpr divcan1d eqtrd ) CDEZACFZEZB
    VAEZGZBCHZIJZKZABSCLHHZVEMNZABUAZCHZVEUBNZVEMNZVKVDVIVMUCVFVDVHVLVEMABCUDUE
    OVGVKVEVDVKPEVFVDIUKUFNZPVKQVDUTVJVAEZVKVNEUTVBVCUGUTVAUHUIULEVBVCVOCUJABVA
    UMUNVJCRUOTOVDVEPEVFVDVNPVEQUTVCVEVNEVBBCRUPTOVDVFUQURUS $.

  $( The conditional probability has values in ` [ 0 , 1 ] ` .  (Contributed by
     Thierry Arnoux, 13-Dec-2016.)  (Revised by Thierry Arnoux,
     21-Jan-2017.) $)
  cndprob01 $p |- ( ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) /\
    ( P ` B ) =/= 0 ) -> ( ( cprob ` P ) ` <. A , B >. ) e. ( 0 [,] 1 ) ) $=
    ( cprb wcel cdm w3a cfv cc0 wne wa cop ccprob cin co syl3anc prob01 syl2anc
    cdiv syl cicc wceq cndprobval adantr cle wbr cmeas simpl1 domprobmeas csiga
    c1 crn cuni domprobsiga simpl2 simpl3 inelsiga wss inss2 measssd unitdivcld
    a1i wb simpr mpbid eqeltrd ) CDEZACFZEZBVHEZGZBCHZIJZKZABLCMHHZABNZCHZVLSOZ
    IUKUAOZVKVOVRUBVMABCUCUDVNVQVLUEUFZVRVSEZVNVPBVHCVNVGCVHUGHEVGVIVJVMUHZCUIT
    VNVHUJULUMEZVIVJVPVHEZVNVGWCWBCUNTVGVIVJVMUOVGVIVJVMUPZABVHUQPZWEVPBURVNABU
    SVBUTVNVQVSEZVLVSEZVMVTWAVCVNVGWDWGWBWFVPCQRVNVGVJWHWBWEBCQRVKVMVDVQVLVAPVE
    VF $.

  $( The conditional probability given a certain event is one.  (Contributed by
     Thierry Arnoux, 20-Dec-2016.)  (Revised by Thierry Arnoux,
     21-Jan-2017.) $)
  cndprobtot $p |- ( ( P e. Prob /\ A e. dom P /\ ( P ` A ) =/= 0 ) ->
    ( ( cprob ` P ) ` <. U. dom P , A >. ) = 1 ) $=
    ( cprb wcel cdm cfv cc0 wne w3a cuni cop ccprob cin cdiv co c1 wceq 3adant3
    wa simpl unveldomd simpr cndprobval syl3anc wss 3ad2ant2 dfss1 sylib fveq2d
    elssuni oveq1d cicc cc prob01 elunitcn syl simp3 dividd 3eqtrd ) BCDZABEZDZ
    ABFZGHZIZVAJZAKBLFFZVFAMZBFZVCNOZVCVCNOPUTVBVGVJQZVDUTVBSZUTVFVADVBVKUTVBTZ
    VLBVMUAUTVBUBVFABUCUDRVEVIVCVCNVEVHABVEAVFUEZVHAQVBUTVNVDAVAUJUFAVFUGUHUIUK
    VEVCVEVCGPULODZVCUMDUTVBVOVDABUNRVCUOUPUTVBVDUQURUS $.

  $( The conditional probability given empty event is zero.  (Contributed by
     Thierry Arnoux, 20-Dec-2016.)  (Revised by Thierry Arnoux,
     21-Jan-2017.) $)
  cndprobnul $p |- ( ( P e. Prob /\ A e. dom P /\ ( P ` A ) =/= 0 ) ->
    ( ( cprob ` P ) ` <. (/) , A >. ) = 0 ) $=
    ( cprb wcel cdm cfv cc0 wne w3a c0 cop ccprob cin cdiv co wceq nuleldmp syl
    simp1 simp2 cndprobval syl3anc incom in0 eqtri fveq2i oveq1i probnul oveq1d
    a1i c1 cicc cc prob01 3adant3 elunitcn simp3 div0d 3eqtrd eqtrd ) BCDZABEZD
    ZABFZGHZIZJAKBLFFZJAMZBFZVDNOZGVFVAJVBDZVCVGVJPVAVCVESZVFVAVKVLBQRVAVCVETJA
    BUAUBVFVJJBFZVDNOZGVDNOGVJVNPVFVIVMVDNVHJBVHAJMJJAUCAUDUEUFUGUJVFVMGVDNVFVA
    VMGPVLBUHRUIVFVDVFVDGUKULODZVDUMDVAVCVOVEABUNUOVDUPRVAVCVEUQURUSUT $.

  ${
    $d a B $.  $d a P $.
    $( The conditional probability defines a probability law.  (Contributed by
       Thierry Arnoux, 23-Dec-2016.)  (Revised by Thierry Arnoux,
       21-Jan-2017.) $)
    cndprobprob $p |- ( ( P e. Prob /\ B e. dom P /\ ( P ` B ) =/= 0 ) ->
      ( a e. dom P |-> ( ( cprob ` P ) ` <. a , B >. ) ) e. Prob ) $=
      ( cprb wcel cdm cfv cc0 wne w3a cv cop ccprob cmpt cin cdiv co 3adant3 wa
      syl cmeas domprobmeas 3ad2ant1 simp2 c1 cicc cr prob01 elunitrn elunitge0
      crp cle wbr simp3 ne0gt0d elrpd probmeasb syl3anc wceq 3anan32 cndprobval
      wb sylbir mpteq2dva eleq1d mpbird ) BDEZABFZEZABGZHIZJZCVHCKZALBMGGZNZDEZ
      CVHVMAOBGVJPQZNZDEZVLBVHUAGEZVIVJUKEVSVGVIVTVKBUBUCVGVIVKUDVLVJVLVJHUEUFQ
      EZVJUGEVGVIWAVKABUHRZVJUITZVLVJWCVLWAHVJULUMWBVJUJTVGVIVKUNUOUPCAVHBUQURV
      GVIVPVSVBVKVGVISZVOVRDWDCVHVNVQWDVMVHEZSVGWEVIJVNVQUSVGWEVIUTVMABVAVCVDVE
      RVF $.
  $}

  $( Bayes Theorem (Contributed by Thierry Arnoux, 20-Dec-2016.)  (Revised by
     Thierry Arnoux, 21-Jan-2017.) $)
  bayesth $p |- ( ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) /\
    ( P ` A ) =/= 0 /\ ( P ` B ) =/= 0 ) -> ( ( cprob ` P ) ` <. A , B >. ) =
    ( ( ( ( cprob ` P ) ` <. B , A >. ) x. ( P ` A ) ) / ( P ` B ) ) ) $=
    ( cprb wcel w3a cfv cc0 wne cop cmul co cdiv cc unitsscn 3adant2 sseldi cin
    wceq cndprobin cdm ccprob cicc cndprob01 simp11 simp13 prob01 syl2anc simp3
    c1 divcan4d incom fveq2i simp12 simp2 syl31anc 3eqtr4a oveq1d eqtr3d ) CDEZ
    ACUAZEZBVAEZFZACGZHIZBCGZHIZFZABJCUBGZGZVGKLZVGMLVKBAJVJGVEKLZVGMLVIVKVGVIH
    UJUCLZNVKOVDVHVKVNEVFABCUDPQVIVNNVGOVIUTVCVGVNEUTVBVCVFVHUEZUTVBVCVFVHUFZBC
    UGUHQVDVFVHUIUKVIVLVMVGMVIABRZCGZBARZCGZVLVMVQVSCABULUMVDVHVLVRSVFABCTPVIUT
    VCVBVFVMVTSVOVPUTVBVCVFVHUNVDVFVHUOBACTUPUQURUS $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Real Valued Random Variables
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c rRndVar $. $( The class of real-valued random variables $)

  $( Extend class notation with the class of real valued random variables. $)
  crrv $a class rRndVar $.

  $( In its generic definition, a random variable is a measurable function from
     a probability space to a Borel set.  Here, we specifically target
     real-valued random variables, i.e. measurable function from a probability
     space to the Borel sigma algebra on the set of real numbers.  (Contributed
     by Thierry Arnoux, 20-Sep-2016.)  (Revised by Thierry Arnoux,
     25-Jan-2017.) $)
  df-rrv $a |- rRndVar = ( p e. Prob |-> ( dom p MblFnM BrSiga ) ) $.

  ${
    $d p y P $.  $d y X $.
    isrrvv.1 $e |- ( ph -> P e. Prob ) $.
    $( A real-valued random variable is a measurable function from its sample
       space to the Borel Sigma Algebra.  (Contributed by Thierry Arnoux,
       25-Jan-2017.) $)
    rrvmbfm $p |- ( ph -> ( X e. ( rRndVar ` P ) <->
                                            X e. ( dom P MblFnM BrSiga ) ) ) $=
      ( vp crrv cfv cdm cbrsiga cmbfm co cprb wcel wceq dmeq oveq1d df-rrv ovex
      cv fvmpt syl eleq2d ) ABFGZBHZIJKZCABLMUCUENDEBESZHZIJKUELFUFBNUGUDIJUFBO
      PEQUDIJRTUAUB $.

    $( Elementhood to the set of real-valued random variables with respect to
       the probability ` P ` .  (Contributed by Thierry Arnoux,
       25-Jan-2017.) $)
    isrrvv $p |- ( ph -> ( X e. ( rRndVar ` P ) <-> ( X : U. dom P --> RR /\
      A. y e. BrSiga ( `' X " y ) e. dom P ) ) ) $=
      ( crrv cfv wcel cdm cbrsiga cmbfm co cuni cmap ccnv wa cr csiga syl cvv
      cv cima wral wf rrvmbfm cprb domprobsiga brsigarn elrnsiga mp1i unibrsiga
      crn ismbfm oveq1i eleq2i reex uniexg elmapg sylancr syl5bb anbi1d 3bitrd
      wb ) ADCFGHDCIZJKLHDJMZVDMZNLZHZDOBUAUBVDHBJUCZPVFQDUDZVIPACDEUEABVDJDACU
      FHVDRULMZHZECUGSZJQRGHJVKHAUHJQUIUJUMAVHVJVIVHDQVFNLZHZAVJVGVNDVEQVFNUKUN
      UOAQTHVFTHZVOVJVCUPAVLVPVMVDVKUQSQVFDTTURUSUTVAVB $.

    rrvvf.1 $e |- ( ph -> X e. ( rRndVar ` P ) ) $.
    $( A real-valued random variable is a function.  (Contributed by Thierry
       Arnoux, 25-Jan-2017.) $)
    rrvvf $p |- ( ph -> X : U. dom P --> RR ) $=
      ( vy cdm cuni cr wf ccnv cv cima wcel cbrsiga wral crrv cfv wa isrrvv
      mpbid simpld ) ABGZHICJZCKFLMUCNFOPZACBQRNUDUESEAFBCDTUAUB $.

    $( A real-valued random variable is a function over the universe.
       (Contributed by Thierry Arnoux, 25-Jan-2017.) $)
    rrvfn $p |- ( ph -> X Fn U. dom P ) $=
      ( cdm cuni cr wf wfn rrvvf ffn syl ) ABFGZHCICNJABCDEKNHCLM $.

    $( The domain of a random variable is the universe.  (Contributed by
       Thierry Arnoux, 25-Jan-2017.) $)
    rrvdm $p |- ( ph -> dom X = U. dom P ) $=
      ( cdm cuni cr wf wceq rrvvf fdm syl ) ABFGZHCICFNJABCDEKNHCLM $.

    $( The range of a random variable as a subset of ` RR ` .  (Contributed by
       Thierry Arnoux, 6-Feb-2017.) $)
    rrvrnss $p |- ( ph -> ran X C_ RR ) $=
      ( cdm cuni cr wf crn wss rrvvf frn syl ) ABFGZHCICJHKABCDELOHCMN $.

    $( A real-valued random variable is a function.  (Contributed by Thierry
       Arnoux, 25-Jan-2017.) $)
    rrvf2 $p |- ( ph -> X : dom X --> RR ) $=
      ( cdm cr wf cuni rrvvf rrvdm feq2d mpbird ) ACFZGCHBFIZGCHABCDEJANOGCABCD
      EKLM $.

    $( The domain of a random variable.  This is useful to shorten proofs.
       (Contributed by Thierry Arnoux, 25-Jan-2017.) $)
    rrvdmss $p |- ( ph -> U. dom P C_ dom X ) $=
      ( cdm cuni wceq wss rrvdm eqimss2 syl ) ACFZBFGZHNMIABCDEJNMKL $.

    $( For a real-value random variable ` X ` , any open interval in ` RR ` is
       the image of a measurable set.  (Contributed by Thierry Arnoux,
       25-Jan-2017.) $)
    rrvfinvima $p |- ( ph -> A. y e. BrSiga ( `' X " y ) e. dom P ) $=
      ( cdm cuni cr wf ccnv cv cima wcel cbrsiga wral crrv cfv wa isrrvv simprd
      mpbid ) ACGZHIDJZDKBLMUCNBOPZADCQRNUDUESFABCDETUBUA $.
  $}

  ${
    $d x y P $.  $d y ph $.  $d y P $.
    0rrv.1 $e |- ( ph -> P e. Prob ) $.
    $( The constant function equal to zero is a random variable.  (Contributed
       by Thierry Arnoux, 16-Jan-2017.)  (Revised by Thierry Arnoux,
       30-Jan-2017.) $)
    0rrv $p |- ( ph -> ( x e. U. dom P |-> 0 ) e. ( rRndVar ` P ) ) $=
      ( vy cdm cuni cc0 wcel cr ccnv cima cbrsiga wral cin wceq cxp 3eqtri cvv
      c0 cmpt crrv cfv wf cv 0re rgenw eqid fmpt mpbi a1i csn wa cres fconstmpt
      crn cnveqi cnvxp eqtr3i imaeq1i df-ima df-rn df-res inxp inv1 dmeqi xpeq2
      xpeq2i xp0 syl6eq dmeqd adantl cprb csiga domprobsiga 0elsiga 3syl adantr
      dm0 eqeltrd syl5eqel dmxp unveldomd pm2.61dane ralrimivw isrrvv mpbir2and
      wne ) ABCFZGZHUAZCUBUCIWJJWKUDZWKKZEUEZLZWIIZEMNWLAHJIZBWJNWLWQBWJUFUGBWJ
      JHWKWKUHUIUJUKAWPEMAWPHULZWNOZTAWSTPZUMZWOWJWSQZFZWIWOWRWJQZWNUNZKZFZWSWJ
      QZKZFXCWOXDWNLXEUPXGWMXDWNWJWRQZKWMXDXJWKBWJHUOUQWJWRURUSUTXDWNVAXEVBRXFX
      IXEXHXEXDWNSQOWSWJSOZQXHXDWNVCWRWJWNSVDXKWJWSWJVEVHRUQVFXIXBWSWJURVFRZXAX
      CTWIWTXCTPAWTXCTFTWTXBTWTXBWJTQTWSTWJVGWJVIVJVKVSVJVLATWIIZWTACVMIWIVNUPG
      IXMDCVOWIVPVQVRVTWAAWSTWHZUMZWOXCWIXLXOXCWJWIXNXCWJPAWJWSWBVLAWJWIIXNACDW
      CVRVTWAWDWEAECWKDWFWG $.
  $}

  ${
    $d a b x y P $.  $d a b x y X $.  $d a b x y Y $.  $d a b x y ph $.
    rrvadd.1 $e |- ( ph -> P e. Prob ) $.
    rrvadd.2 $e |- ( ph -> X e. ( rRndVar ` P ) ) $.
    rrvadd.3 $e |- ( ph -> Y e. ( rRndVar ` P ) ) $.
    $( The sum of two random variables is a random variable (Contributed by
       Thierry Arnoux, 4-Jun-2017.) $)
    rrvadd $p |- ( ph -> ( X oF + Y ) e. ( rRndVar ` P ) ) $=
      ( vx vy va vb caddc co cfv wcel cbrsiga cr cv rrvmbfm wceq cof crrv cmbfm
      cdm cmpt2 cuni cop cmpt ccom nfmpt1 rrvvf unveldomd eqidd ofoprabco csiga
      csx cprb crn domprobsiga syl brsigarn elrnsiga sxsiga syl2anc mpbid fveq2
      mp1i opeq12d cbvmptv mbfmco2 cioo ctg ctx ccn eqid a1i csigagen df-brsiga
      raddcn sxbrsiga cnmbfm mbfmco eqeltrd mpbird ) ACDLUAMZBUBNZOWEBUDZPUCMZO
      AWEHIQQHRIRLMUEZJWGUFZJRZCNZWKDNZUGZUHZUIWHAHIWJQQLCDWOWIWGJJWJWNUJABCEFU
      KABDEGUKABEULAWOUMAWIUMUNAWGPPUPMZPWOWIABUQOWGUOURUFZOEBUSUTZAPWQOZWSWPWQ
      OPQUONOWSAVAPQVBVGZWTPPVCVDWTAKWGPPCDWOWRWTWTACWFOCWHOFABCESVEADWFODWHOGA
      BDESVEJKWJWNKRZCNZXADNZUGWKXATWLXBWMXCWKXACVFWKXADVFVHVIVJAWPPWIVKURVLNZX
      DVMMZXDWIXEXDVNMOAHIXDXDVOZVSVPWPXEVQNTAXDXFVTVPPXDVQNTAVRVPWAWBWCABWEESW
      D $.
  $}

  ${
    $d v x y z C $.  $d x y z P $.  $d x y z X $.  $d v x y z ph $.
    rrvmulc.1 $e |- ( ph -> P e. Prob ) $.
    rrvmulc.2 $e |- ( ph -> X e. ( rRndVar ` P ) ) $.
    rrvmulc.3 $e |- ( ph -> C e. RR ) $.
    $( A random variable multiplied by a constant is a random variable.
       (Contributed by Thierry Arnoux, 17-Jan-2017.)  (Revised by Thierry
       Arnoux, 22-May-2017.) $)
    rrvmulc $p |- ( ph -> ( X oFC x. C ) e. ( rRndVar ` P ) ) $=
      ( vx cmul co cfv wcel cbrsiga cr cuni cvv csiga crn syl rrvmbfm cofc crrv
      cdm cmbfm cv cmpt ccom cprb domprobsiga uniexg ofcfval4 brsigarn elrnsiga
      rrvvf mp1i mpbid cioo ctg eqid rmulccn csigagen wceq df-brsiga a1i cnmbfm
      mbfmco eqeltrd mpbird ) ADBIUAJZCUBKZLVICUCZMUDJZLAVIHNHUEBIJUFZDUGVLAHVK
      OZNBIDPNACDEFUNAVKQROZLZVNPLACUHLVPECUISZVKVOUJSGUKAVKMMDVMVQMNQKLMVOLAUL
      MNUMUOZVRADVJLDVLLFACDETUPAMMVMUQRURKZVSAHBVSVSUSGUTMVSVAKVBAVCVDZVTVEVFV
      GACVIETVH $.
  $}

  ${
    $d k n P $.  $d k N $.  $d k n X $.  $d k n ph $.
    rrvsum.1 $e |- ( ph -> P e. Prob ) $.
    rrvsum.2 $e |- ( ph -> X : NN --> ( rRndVar ` P ) ) $.
    rrvsum.3 $e |- ( ( ph /\ N e. NN ) -> S = ( seq 1 ( oF + , X ) ` N ) ) $.
    $( An indexed sum of random variables is a random variable.  (Contributed
       by Thierry Arnoux, 22-May-2017.) $)
    rrvsum $p |- ( ( ph /\ N e. NN ) -> S e. ( rRndVar ` P ) ) $=
      ( vk vn cn wcel wa c1 cfv wi wceq fveq2 eleq1d imbi2d caddc cof cseq crrv
      cv co cz 1z seq1 ax-mp 1nn ffvelrnda mpan2 syl5eqel cuz seqp1 nnuz eleq2s
      ad2antlr cprb ad2antrr simpr peano2nn sylan2 adantr rrvadd eqeltrd expcom
      ex a2d nnind impcom ) ADKLZMCDUAUBZENUCZOZBUDOZHVMAVPVQLZAIUEZVOOZVQLZPAN
      VOOZVQLZPAJUEZVOOZVQLZPAWDNUAUFZVOOZVQLZPAVRPIJDVSNQZWAWCAWJVTWBVQVSNVORS
      TVSWDQZWAWFAWKVTWEVQVSWDVORSTVSWGQZWAWIAWLVTWHVQVSWGVORSTVSDQZWAVRAWMVTVP
      VQVSDVORSTAWBNEOZVQNUGLWBWNQUHVNENUIUJANKLWNVQLUKAKVQNEGULUMUNWDKLZAWFWIA
      WOWFWIPAWOMZWFWIWPWFMZWHWEWGEOZVNUFZVQWOWHWSQZAWFWTWDNUOOKVNENWDUPUQURUSW
      QBWEWRABUTLWOWFFVAWPWFVBWPWRVQLZWFWOAWGKLXAWDVCAKVQWGEGULVDVEVFVGVIVHVJVK
      VLVG $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Preimage set mapping operator
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c oRVC $. $( A small o with RV/C subscript $)

  $( Extend class notation to include the preimage set mapping operator. $)
  corvc $a class oRVC R $.

  ${
    $d a x y R $.
    $( Define the preimage set mapping operator.  In probability theory, the
       notation ` P ( X = A ) ` denotes the probability that a random variable
       ` X ` takes the value ` A ` .  We introduce here an operator which
       enables to write this in Metamath as ` ( P `` ( X oRVC _I A ) ) ` , and
       keep a similar notation.  Because with this notation ` ( X oRVC _I A ) `
       is a set, we can also apply it to conditional probabilities, like in
       ` ( P `` ( X oRVC _I A ) | ( Y oRVC _I B ) ) ) ` .

       The oRVC operator transforms a relation ` R ` into an operation taking a
       random variable ` X ` and a constant ` C ` , and returning the preimage
       through ` X ` of the equivalence class of ` C ` .

       The most commonly used relations are: - equality: ` { X = A } ` as
       ` ( X oRVC _I A ) ` cf. ~ ideq - elementhood: ` { X e. A } ` as
       ` ( X oRVC _E A ) ` cf. ~ epel - less-than: ` { X <_ A } ` as
       ` ( X oRVC <_ A ) `

       Even though it is primarily designed to be used within probability
       theory and with random variables, this operator is defined on generic
       functions, and could be used in other fields, e.g. for continuous
       functions.  (Contributed by Thierry Arnoux, 15-Jan-2017.) $)
    df-orvc $a |- oRVC R =
             ( x e. { x | Fun x } , a e. _V |-> ( `' x " { y | y R a } ) ) $.
  $}

  ${
    $d a x y A $.  $d a x y R $.  $d a x y X $.  $d a x ph $.
    orvcval.1 $e |- ( ph -> Fun X ) $.
    orvcval.2 $e |- ( ph -> X e. V ) $.
    orvcval.3 $e |- ( ph -> A e. W ) $.
    $( Value of the preimage mapping operator applied on a given random
       variable and constant (Contributed by Thierry Arnoux, 19-Jan-2017.) $)
    orvcval $p |- ( ph -> ( X oRVC R A ) = ( `' X " { y | y R A } ) ) $=
      ( vx va cv wfun cab cvv ccnv wbr wceq wcel cima corvc cmpt2 df-orvc simpl
      a1i wa cnveqd simpr breq2d abbidv imaeq12d adantl wb funeq elabg syl elex
      mpbird cnvexg imaexg 3syl ovmpt2d ) AKLGCKMZNZKOZPVDQZBMZLMZDRZBOZUAZGQZV
      HCDRZBOZUAZDUBZPVQKLVFPVLUCSAKBDLUDUFVDGSZVICSZUGZVLVPSAVTVGVMVKVOVTVDGVR
      VSUEUHVTVJVNBVTVICVHDVRVSUIUJUKULUMAGVFTZGNZHAGETZWAWBUNIVEWBKGEVDGUOUPUQ
      USACFTCPTJCFURUQAWCVMPTVPPTIGEUTVMVOPVAVBVC $.

    $d y z A $.  $d y z R $.  $d z X $.
    $( Another way to express the value of the preimage mapping operator
       (Contributed by Thierry Arnoux, 19-Jan-2017.) $)
    orvcval2 $p |- ( ph -> ( X oRVC R A ) = { z e. dom X | ( X ` z ) R A } ) $=
      ( vy corvc co ccnv cv wbr wcel crab wceq a1i cab cima cfv cdm orvcval wfn
      wfun funfn sylib fncnvima2 syl wb fvex breq1 elab rabbiia 3eqtrd ) AGCDLM
      GNKOZCDPZKUAZUBZBOZGUCZUTQZBGUDZRZVCCDPZBVERZAKCDEFGHIJUEAGVEUFZVAVFSAGUG
      VIHGUHUIBVEUTGUJUKVFVHSAVDVGBVEVDVGULVBVEQUSVGKVCVBGUMURVCCDUNUOTUPTUQ $.

    $( Elementhood of a preimage (Contributed by Thierry Arnoux,
       21-Jan-2017.) $)
    elorvc $p |- ( ( ph /\ z e. dom X ) ->
                              ( z e. ( X oRVC R A ) <-> ( X ` z ) R A ) ) $=
      ( cv corvc co wcel cdm cfv wbr crab wa orvcval2 eleq2d rabid syl6bb baibd
      ) ABKZGCDLMZNZUEGOZNZUEGPCDQZAUGUEUJBUHRZNUIUJSAUFUKUEABCDEFGHIJTUAUJBUHU
      BUCUD $.
  $}


  ${
    orvccel.1 $e |- ( ph -> S e. U. ran sigAlgebra ) $.
    orvccel.2 $e |- ( ph -> J e. Top ) $.
    orvccel.3 $e |- ( ph -> X e. ( S MblFnM ( sigaGen ` J ) ) ) $.
    orvccel.4 $e |- ( ph -> A e. V ) $.
    $d y A $.  $d y R $.  $d y X $.  $d y J $.
    $( The value of the preimage mapping operator can be restricted to
       preimages in the base set of the topology.  Cf. ~ orvcval (Contributed
       by Thierry Arnoux, 21-Jan-2017.) $)
    orvcval4 $p |- ( ph ->
                        ( X oRVC R A ) = ( `' X " { y e. U. J | y R A } ) ) $=
      ( cima cuni co wceq ctop wf wcel cvv ccnv wbr cab cin corvc crab wfun crn
      cv wss csigagen cfv sgsiga isanmbfm mbfmfun mbfmf eqidd elex unisg feq23d
      3syl mpbid frn syl fimacnvinrn2 syl2anc cmbfm orvcval a1i imaeq2d 3eqtr4d
      dfrab2 ) AHUAZBUICDUBZBUCZMZVMVOFNZUDZMZHCDUEOVMVNBVQUFZMAHUGHUHVQUJZVPVS
      PAHAEFUKULZHIAFQJUMZKUNUOZAENZVQHRZWAAWEWBNZHRWFAEWBHIWCKUPAWEWGWEVQHAWEU
      QAFQSFTSWGVQPJFQURFTUSVAUTVBWEVQHVCVDVOVQHVEVFABCDEWBVGOGHWDKLVHAVTVRVMVT
      VRPAVNBVQVLVIVJVK $.

    ${
      orvcoel.5 $e |- ( ph -> { y e. U. J | y R A } e. J ) $.
      $( If the relation produces open sets, preimage maps by a measurable
         function are measurable sets.  (Contributed by Thierry Arnoux,
         21-Jan-2017.) $)
      orvcoel $p |- ( ph -> ( X oRVC R A ) e. S ) $=
        ( corvc co ccnv cv wbr cuni ctop crab cima orvcval4 csigagen cfv sgsiga
        wcel wss sssigagen syl sseldd mbfmcnvima eqeltrd ) AHCDNOHPBQCDRBFSUAZU
        BEABCDEFGHIJKLUCAUNEFUDUEZHIAFTJUFKAFUOUNAFTUGFUOUHJFTUIUJMUKULUM $.
    $}

    ${
      orvccel.5 $e |- ( ph -> { y e. U. J | y R A } e. ( Clsd ` J ) ) $.
      $( If the relation produces closed sets, preimage maps by a measurable
         function are measurable sets.  (Contributed by Thierry Arnoux,
         21-Jan-2017.) $)
      orvccel $p |- ( ph -> ( X oRVC R A ) e. S ) $=
        ( corvc co ccnv cv wbr cfv ctop cuni crab cima orvcval4 csigagen sgsiga
        ccld wcel wss cldssbrsiga syl sseldd mbfmcnvima eqeltrd ) AHCDNOHPBQCDR
        BFUAUBZUCEABCDEFGHIJKLUDAUOEFUESZHIAFTJUFKAFUGSZUPUOAFTUHUQUPUIJFUJUKMU
        LUMUN $.
    $}
  $}

  ${
    orrvccel.1 $e |- ( ph -> P e. Prob ) $.
    orrvccel.2 $e |- ( ph -> X e. ( rRndVar ` P ) ) $.

    $d z A $.  $d z R $.  $d z X $.
    orrvccel.4 $e |- ( ph -> A e. V ) $.
    $( Elementhood of a preimage for a real-valued random variable.
       (Contributed by Thierry Arnoux, 21-Jan-2017.) $)
    elorrvc $p |- ( ( ph /\ z e. U. dom P ) ->
                                 ( z e. ( X oRVC R A ) <-> ( X ` z ) R A ) ) $=
      ( cv cdm cuni wcel wa corvc co cfv wbr syl rrvdm eleq2d biimprd imdistani
      wb crrv wfn wfun rrvfn fnfun elorvc ) ABKZDLMZNZOAULGLZNZOULGCEPQNULGRCES
      UEAUNUPAUPUNAUOUMULADGHIUAUBUCUDABCEDUFRFGAGUMUGGUHADGHIUIUMGUJTIJUKT $.

    $d y A $.  $d y R $.  $d y X $.
    $( The value of the preimage mapping operator can be restricted to
       preimages of subsets of RR. (Contributed by Thierry Arnoux,
       21-Jan-2017.) $)
    orrvcval4 $p |- ( ph ->
                          ( X oRVC R A ) = ( `' X " { y e. RR | y R A } ) ) $=
      ( co crn cfv cuni crab cima cr wcel cbrsiga cmbfm corvc ccnv wbr cioo ctg
      cdm cprb csiga domprobsiga syl ctop retop a1i csigagen crrv rrvmbfm mpbid
      cv df-brsiga oveq2i syl6eleq orvcval4 wceq uniretop rabeq imaeq2i syl6eqr
      ax-mp ) AGCEUAKGUBZBURCEUCZBUDLUEMZNZOZPVIVJBQOZPABCEDUFZVKFGADUGRVOUHLNR
      HDUIUJVKUKRAULUMAGVOSTKZVOVKUNMZTKAGDUOMRGVPRIADGHUPUQSVQVOTUSUTVAJVBVNVM
      VIQVLVCVNVMVCVDVJBQVLVEVHVFVG $.

    ${
      orrvcoel.5 $e |- ( ph ->
                              { y e. RR | y R A } e. ( topGen ` ran (,) ) ) $.
      $( If the relation produces open sets, preimage maps of a random variable
         are measurable sets.  (Contributed by Thierry Arnoux, 21-Jan-2017.) $)
      orrvcoel $p |- ( ph -> ( X oRVC R A ) e. dom P ) $=
        ( crn cfv wcel cuni cbrsiga cmbfm co crab cr cdm cioo csiga domprobsiga
        ctg cprb syl ctop retop a1i csigagen crrv rrvmbfm mpbid oveq2i syl6eleq
        df-brsiga cv wbr wceq uniretop rabeq ax-mp syl5eqelr orvcoel ) ABCEDUAZ
        UBLUEMZFGADUFNVFUCLONHDUDUGVGUHNAUIUJAGVFPQRZVFVGUKMZQRAGDULMNGVHNIADGH
        UMUNPVIVFQUQUOUPJABURCEUSZBVGOZSZVJBTSZVGTVKUTVMVLUTVAVJBTVKVBVCKVDVE
        $.
    $}

    ${
      orrvccel.5 $e |- ( ph ->
                   { y e. RR | y R A } e. ( Clsd ` ( topGen ` ran (,) ) ) ) $.
      $( If the relation produces closed sets, preimage maps are measurable
         sets.  (Contributed by Thierry Arnoux, 21-Jan-2017.) $)
      orrvccel $p |- ( ph -> ( X oRVC R A ) e. dom P ) $=
        ( crn cfv wcel cuni cbrsiga cmbfm co crab cr cdm cioo csiga domprobsiga
        ctg cprb syl ctop retop a1i csigagen crrv rrvmbfm mpbid oveq2i syl6eleq
        df-brsiga cv wbr ccld wceq uniretop rabeq ax-mp syl5eqelr orvccel ) ABC
        EDUAZUBLUEMZFGADUFNVGUCLONHDUDUGVHUHNAUIUJAGVGPQRZVGVHUKMZQRAGDULMNGVIN
        IADGHUMUNPVJVGQUQUOUPJABURCEUSZBVHOZSZVKBTSZVHUTMTVLVAVNVMVAVBVKBTVLVCV
        DKVEVF $.
    $}
  $}

  ${
    $d x A $.  $d x X $.  $d x ph $.
    orvcgteel.1 $e |- ( ph -> P e. Prob ) $.
    orvcgteel.2 $e |- ( ph -> X e. ( rRndVar ` P ) ) $.
    orvcgteel.3 $e |- ( ph -> A e. RR ) $.
    $( Preimage maps produced by the "greater than or equal" relation are
       measurable sets.  (Contributed by Thierry Arnoux, 5-Feb-2017.) $)
    orvcgteel $p |- ( ph -> ( X oRVC `' <_ A ) e. dom P ) $=
      ( vx cle cr wbr crab cpnf cfv wa cxr wcel adantr ad2antrl jca ccnv cv crn
      cico co cioo ctg ccld clt simpr brcnvg syl2anc pm5.32da rexr simprr ltpnf
      simprl simprrl simprrr xrre3 syl22anc impbida bitrd rabbidva2 rexrd pnfxr
      wb wceq icoval sylancl eqtr4d icopnfcld syl eqeltrd orrvccel ) AHBCIUAZJD
      EFGAHUBZBVPKZHJLZBMUDUEZUFUCUGNUHNZAVSBVQIKZVQMUIKZOZHPLZVTAVRWDHJPAVQJQZ
      VROWFWBOZVQPQZWDOZAWFVRWBAWFOWFBJQZVRWBVGAWFUJAWJWFGRVQBJJIUKULUMAWGWIAWG
      OZWHWDWFWHAWBVQUNSWKWBWCAWFWBUOWFWCAWBVQUPSTTAWIOZWFWBWLWHWJWBWCWFAWHWDUQ
      AWJWIGRAWHWBWCURZAWHWBWCUSVQBUTVAWMTVBVCVDABPQMPQVTWEVHABGVEVFHBMVIVJVKAW
      JVTWAQGBVLVMVNVO $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Distribution Functions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    dstrvprob.1 $e |- ( ph -> P e. Prob ) $.
    dstrvprob.2 $e |- ( ph -> X e. ( rRndVar ` P ) ) $.

    ${
      $d a x A $.  $d a P $.  $d a x X $.  $d a x ph $.
      orvcelel.1 $e |- ( ph -> A e. BrSiga ) $.
      $( Preimage maps produced by the "elementhood" relation (Contributed by
         Thierry Arnoux, 6-Feb-2017.) $)
      orvcelval $p |- ( ph -> ( X oRVC _E A ) = ( `' X " A ) ) $=
        ( vx cep corvc co ccnv cv cr crab cima cbrsiga wcel syl wceq wbr cin wb
        orrvcval4 epelg rabbidv a1i wss cuni elssuni unibrsiga syl6sseq sseqin2
        dfin5 sylib 3eqtr2d imaeq2d eqtrd ) ADBIJKDLZHMZBIUAZHNOZPUSBPAHBCIQDEF
        GUDAVBBUSAVBUTBRZHNOZNBUBZBAVAVCHNABQRZVAVCUCGUTBQUESUFVEVDTAHNBUNUGABN
        UHZVEBTAVFVGGVFBQUINBQUJUKULSBNUMUOUPUQUR $.

      $( Preimage maps produced by the "elementhood" relation are measurable
         sets.  (Contributed by Thierry Arnoux, 5-Feb-2017.) $)
      orvcelel $p |- ( ph -> ( X oRVC _E A ) e. dom P ) $=
        ( va cep corvc co ccnv cima cdm orvcelval wcel cbrsiga wral rrvfinvima
        cv wceq wa simpr imaeq2d eleq1d rspcdv mpd eqeltrd ) ADBIJKDLZBMZCNZABC
        DEFGOAUIHTZMZUKPZHQRUJUKPZAHCDEFSAUNUOHBQGAULBUAZUBZUMUJUKUQULBUIAUPUCU
        DUEUFUGUH $.
    $}

    ${
      $d a P $.  $d a X $.
      dstrvprob.3 $e |- ( ph ->
                           D = ( a e. BrSiga |-> ( P ` ( X oRVC _E a ) ) ) ) $.
      ${
        $d a A $.
        dstrvval.1 $e |- ( ph -> A e. BrSiga ) $.
        $( The value of the distribution of a random variable.  (Contributed by
           Thierry Arnoux, 9-Feb-2017.) $)
        dstrvval $p |- ( ph -> ( D ` A ) = ( P ` ( `' X " A ) ) ) $=
          ( cfv cbrsiga cv cep corvc co cmpt ccnv wceq fveq2d cima fveq1d oveq2
          wcel eqid fvex fvmpt syl orvcelval 3eqtrd ) ABCKBFLEFMZNOZPZDKZQZKZEB
          ULPZDKZERBUAZDKABCUOIUBABLUDUPURSJFBUNURLUOUKBSUMUQDUKBEULUCTUOUEUQDU
          FUGUHAUQUSDABDEGHJUITUJ $.
      $}

      $d a x D $.  $d a x ph $.
      $( The distribution of a random variable is a probability law (TODO:
         could be shortened using ~ dstrvval ) (Contributed by Thierry Arnoux,
         10-Feb-2017.) $)
      dstrvprob $p |- ( ph -> D e. Prob ) $=
        ( wcel cfv c1 wceq cbrsiga cc0 c0 wa syl cr fveq2d eqtrd cmeas crn cuni
        vx cdm cprb cpnf cicc co wf cv com cdom wbr wdisj cesum wi cpw wral cep
        corvc adantr crrv simpr orvcelel prob01 syl2anc cxr cle rexrd elunitge0
        elunitrn elxrge0 sylanbrc fmpt3d oveq2d csiga brsigarn elrnsiga 0elsiga
        ccnv cima mp2b probvalrnd fvmptd orvcelval fveq2i probnul syl5eq 3eqtrd
        a1i ima0 ciun wfun ad2antrr ffun unipreima domprobmeas nfv nfdisj1 nfan
        rrvvf simplll simpllr elelpwi rrvfinvima r19.21bi ralrimi simprl simprr
        disjpreima measvuni syl112anc cmpt mp1i simplr sigaclcu syl3anc fvmpt2d
        ex dstrvval esumeq2d 3eqtr4d ralrimiva wb ismeas syl3anbrc dmeqd dmmptg
        w3a eleqtrrd measbasedom sylibr unieqd unibrsiga syl6eq fimacnv probtot
        baselsiga 1re elprob ) ABUAUBUCIZBUEZUCZBJZKLBUFIABUUCUAJZIUUBABMUAJZUU
        FAMNUGUHUIZBUJZOBJZNLZUDUKZULUMUNZEUULEUKZUOZPZUULUCZBJZUULUUNBJZEUPZLZ
        UQZUDMURZUSZBUUGIZAEMDUUNUTVAZUIZCJZUUHBHAUUNMIZPZUVHNKUHUIZIZUVHUUHIZU
        VJCUFIZUVGCUEZIUVLAUVNUVIFVBZUVJUUNCDUVPADCVCJIZUVIGVBAUVIVDVEUVGCVFVGZ
        UVLUVHVHINUVHVIUNUVMUVLUVHUVHVLVJUVHVKUVHVMVNQZVOAUUJDOUVFUIZCJZDWAZOWB
        ZCJZNAEOUVHUWAMBRHAUUNOLZPZUVGUVTCUWFUUNODUVFAUWEVDVPSOMIZAMRVQJIZMVQUB
        UCIZUWGVRMRVSZMVTWCWKZAUVTCFAOCDFGUWKVEWDWEAUVTUWCCAOCDFGUWKWFSAUWDOCJZ
        NUWCOCUWBWLWGAUVNUWLNLFCWHQWIWJAUVBUDUVCAUULUVCIZPZUUPUVAUWNUUPPZUWBUUQ
        WBZCJZUULUWBUUNWBZCJZEUPZUURUUTUWOUWQEUULUWRWMZCJZUWTUWODWNZUWQUXBLUWOU
        VOUCZRDUJZUXCAUXEUWMUUPACDFGXBZWOUXDRDWPQZUXCUWPUXACEUULDWQSQUWOCUVOUAJ
        IZUWRUVOIZEUULUSUUMEUULUWRUOZUXBUWTLUWOUVNUXHAUVNUWMUUPFWOZCWRQUWOUXIEU
        ULUWNUUPEUWNEWSUUMUUOEUUMEWSEUULUUNWTXAXAZUWOUUNUULIZUXIUWOUXMPZAUVIUXI
        AUWMUUPUXMXCZUXNUXMUWMUVIUWOUXMVDAUWMUUPUXMXDUUNUULMXEVGZAUXIEMAECDFGXF
        XGVGXTXHUWNUUMUUOXIZUWOUXCUUOUXJUXGUWNUUMUUOXJEUULUUNDXKVGEUULUWRUVOCXL
        XMTUWOUUQBCDEUXKAUVQUWMUUPGWOZABEMUVHXNZLUWMUUPHWOUWOUWIUWMUUMUUQMIUWHU
        WIUWOVRUWJXOAUWMUUPXPUXQUULMXQXRYAUWOUULUUSUWSEUXLUWOUUSUWSLZEUULUXLUWO
        UXMUXTUXNUUSUVHUWSUXNAUVIUUSUVHLUXOUXPAEMUVHBUVKHUVRXSVGUXNUVGUWRCUXNUU
        NCDUWOUVNUXMUXKVBUWOUVQUXMUXRVBUXPWFSTXTXHYBYCXTYDUWHUWIUVEUUIUUKUVDYJY
        EVRUWJUDEMBYFWCYGAUUCMUAAUUCUXSUEZMABUXSHYHAUVMEMUSUYAMLAUVMEMUVSYDEMUV
        HUUHYIQTZSYKBYLYMAUUERBJKAUUDRBAUUDMUCRAUUCMUYBYNYOYPSAERUVHKMBRHAUUNRL
        ZPZUVHUWBRWBZCJZKUYDUVGUYECUYDUVGDRUVFUIZUYEUYDUUNRDUVFAUYCVDVPAUYGUYEL
        UYCARCDFGUWHRMIAVRRMYSXOZWFVBTSAUYFKLUYCAUYFUXDCJZKAUYEUXDCAUXEUYEUXDLU
        XFUXDRDYQQSAUVNUYIKLFCYRQTVBTUYHKRIAYTWKWETBUUAVN $.
    $}
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Cumulative Distribution Functions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    dstfrv.1 $e |- ( ph -> P e. Prob ) $.
    dstfrv.2 $e |- ( ph -> X e. ( rRndVar ` P ) ) $.

    ${
      $d x A $.  $d x X $.  $d x ph $.
      orvclteel.1 $e |- ( ph -> A e. RR ) $.
      $( Preimage maps produced by the "lower than or equal" relation are
         measurable sets.  (Contributed by Thierry Arnoux, 4-Feb-2017.) $)
      orvclteel $p |- ( ph -> ( X oRVC <_ A ) e. dom P ) $=
        ( vx cle cr cv wbr crab cmnf cfv wa cxr wcel ad2antrl jca cioc cioo crn
        co ctg ccld clt rexr simprr simprl adantr simprrl simprrr xrre syl22anc
        mnflt impbida rabbidva2 mnfxr rexrd iocval sylancr eqtr4d iocmnfcld syl
        wceq eqeltrd orrvccel ) AHBCIJDEFGAHKZBILZHJMZNBUAUDZUBUCUEOUFOZAVKNVIU
        GLZVJPZHQMZVLAVJVOHJQAVIJRZVJPZVIQRZVOPZAVRPZVSVOVQVSAVJVIUHSWAVNVJVQVN
        AVJVIUPSAVQVJUITTAVTPZVQVJWBVSBJRZVNVJVQAVSVOUJAWCVTGUKAVSVNVJULAVSVNVJ
        UMZVIBUNUOWDTUQURANQRBQRVLVPVFUSABGUTHNBVAVBVCAWCVLVMRGBVDVEVGVH $.

      $d x B $.
      dstfrvel.1 $e |- ( ph -> B e. U. dom P ) $.
      dstfrvel.2 $e |- ( ph -> ( X ` B ) <_ A ) $.
      $( Elementhood of preimage maps produced by the "lower than or equal"
         relation.  (Contributed by Thierry Arnoux, 13-Feb-2017.) $)
      dstfrvel $p |- ( ph -> B e. ( X oRVC <_ A ) ) $=
        ( vx ccnv cv cle wbr cr crab wcel cdm eleqtrrd cima corvc co cuni rrvvf
        cfv ffvelrnd breq1 elrab sylanbrc wfun wb wf syl rrvdm fvimacnv syl2anc
        ffun mpbid orrvcval4 ) ACELKMZBNOZKPQZUAZEBNUBUCACEUFZVCRZCVDRZAVEPRVEB
        NOZVFADSUDZPCEADEFGUEZIUGJVBVHKVEPVAVEBNUHUIUJAEUKZCESZRVFVGULAVIPEUMVK
        VJVIPEURUNACVIVLIADEFGUOTCVCEUPUQUSAKBDNPEFGHUTT $.
    $}

    ${
      $d n x P $.  $d n x X $.  $d n x ph $.
      $( The limit of all preimage maps by the "lower than or equal" relation
         is the universe.  (Contributed by Thierry Arnoux, 12-Feb-2017.) $)
      dstfrvunirn $p |- ( ph ->
                         U. ran ( n e. NN |-> ( X oRVC <_ n ) ) = U. dom P ) $=
        ( cn cle co wcel wa cfv c1 wbr cr a1i syl2anc breq2 adantr simpr vx cdm
        cuni cv corvc ciun cmpt crn wrex clt cif cfl caddc rrvvf ffvelrnda ifcl
        1le1 wn lenltd biimpar ifbothda flge1nn peano2nnd cprb crrv nnred ltled
        1re leidd fllep1 syl letrd dstfrvel oveq2 eleq2d rspcev ex wi orvclteel
        wceq elunii expcom rexlimdva impbid eliun syl6bbr eqrdv dfiun3 syl6req
        ovex ) ABUBZUCZCGDCUDZHUEZIZUFZCGWOUGUHUCAUAWLWPAUAUDZWLJZWQWOJZCGUIZWQ
        WPJAWRWTAWRWTAWRKZWQDLZMUJNZMXBUKZULLZMUMIZGJWQDXFWNIZJZWTXAXEXAXDOJZMX
        DHNZXEGJXAMOJZXBOJZXIXKXAVHPZAWLOWQDABDEFUNUOZXCMXBOUPQZXCMMHNZMXBHNZXJ
        XAMXBMXDMHRXBXDMHRXPXAXCKZUQPXAXQXCURZXAMXBXMXNUSUTVAXDVBQVCZXAXFWQBDAB
        VDJZWRESADBVELJZWRFSXAXFXTVFZAWRTXAXBXDXFXNXOYCXCXBMHNXBXBHNZXBXDHNXAMX
        BMXDXBHRXBXDXBHRXRXBMXAXLXCXNSXKXRVHPXAXCTVGXAYDXSXAXBXNVISVAXAXIXDXFHN
        XOXDVJVKVLVMWSXHCXFGWMXFVTWOXGWQWMXFDWNVNVOVPQVQAWSWRCGAWMGJZKZWOWKJZWS
        WRVRYFWMBDAYAYEESAYBYEFSYFWMAYETVFVSWSYGWRWQWOWKWAWBVKWCWDCWQGWOWEWFWGC
        GWODWMWNWJWHWI $.
    $}

    ${
      $d x A $.  $d x B $.  $d x X $.  $d x ph $.
      orvclteinc.1 $e |- ( ph -> A e. RR ) $.
      orvclteinc.2 $e |- ( ph -> B e. RR ) $.
      orvclteinc.3 $e |- ( ph -> A <_ B ) $.
      $( Preimage maps produced by the "lower than or equal" relation are
         increasing.  (Contributed by Thierry Arnoux, 11-Feb-2017.) $)
      orvclteinc $p |- ( ph -> ( X oRVC <_ A ) C_ ( X oRVC <_ B ) ) $=
        ( vx cle wbr cr crab cima co wss wcel 3ad2ant1 ccnv cv corvc wfun rrvf2
        cdm wf ffun syl w3a simp2 simp3 letrd 3expia ss2rabdv syl2anc orrvcval4
        sspreima 3sstr4d ) AEUAZKUBZBLMZKNOZPZUTVACLMZKNOZPZEBLUCZQECVHQAEUDZVC
        VFRVDVGRAEUFZNEUGVIADEFGUEVJNEUHUIAVBVEKNAVANSZVBVEAVKVBUJVABCAVKVBUKAV
        KBNSVBHTAVKCNSVBITAVKVBULAVKBCLMVBJTUMUNUOVCVFEURUPAKBDLNEFGHUQAKCDLNEF
        GIUQUS $.
    $}

    dstfrv.3 $e |- ( ph -> F = ( x e. RR |-> ( P ` ( X oRVC <_ x ) ) ) ) $.
    ${
      $d x A $.  $d x B $.  $d x P $.  $d x X $.  $d x ph $.
      dstfrvinc.1 $e |- ( ph -> A e. RR ) $.
      dstfrvinc.2 $e |- ( ph -> B e. RR ) $.
      dstfrvinc.3 $e |- ( ph -> A <_ B ) $.
      $( A cumulative distribution function is non-decreasing.  (Contributed by
         Thierry Arnoux, 11-Feb-2017.) $)
      dstfrvinc $p |- ( ph -> ( F ` A ) <_ ( F ` B ) ) $=
        ( cle co cfv wcel orvclteel cr wceq corvc cdm cprb cmeas syl orvclteinc
        domprobmeas measssd cv wa simpr oveq2d fveq2d probvalrnd fvmptd 3brtr4d
        ) AGCNUAZOZEPZGDUQOZEPZCFPDFPNAURUTEUBZEAEUCQEVBUDPQHEUGUEACEGHIKRZADEG
        HILRZACDEGHIKLMUFUHABCGBUIZUQOZEPZUSSFSJAVECTZUJZVFUREVIVECGUQAVHUKULUM
        KAUREHVCUNUOABDVGVASFSJAVEDTZUJZVFUTEVKVEDGUQAVJUKULUMLAUTEHVDUNUOUP $.
    $}

    $d a i n x P $.  $d a i n x X $.  $d i F $.  $d a i n x ph $.
    $( The limit of the cumulative distribution function is one.  (Contributed
       by Thierry Arnoux, 12-Feb-2017.)  (Revised by Thierry Arnoux,
       11-Jul-2017.) $)
    dstfrvclim1 $p |- ( ph -> F ~~> 1 ) $=
      ( vi va c1 wbr cn cfv cmpt co cc0 cpnf wcel wceq vn cli cv cle corvc ccom
      crn cuni cxrs cicc cress ctopn clm cdm eqid cprb cmeas domprobmeas syl wa
      adantr simpr nnred orvclteel fmptd caddc peano2nnd lep1d orvclteinc eqidd
      crrv oveq2d fvmptd 3sstr4d meascnbl wf wfn measfn dffn5 biimpi 3syl sylan
      prob01 fmpt3d fco syl2anc dstfrvunirn unveldomd eqeltrd cxr clt wss pnfxr
      cico 0xr 0le0 cr ltpnf ax-mp iccssico mp4an lmlimxrge0 mpbid fveq2 fmptco
      1re fveq2d probvalrnd mpteq2dva eqtr4d probtot eqtrd 3brtr3d cz cvv wb 1z
      reex mptex syl6eqel nnuz climmpt sylancr mpbird ) ADKUBLZIMIUCZDNZOZKUBLZ
      ACIMEYFUDUEZPZOZUFZYLUGUHZCNZYHKUBAYMYOUIQRUJPUKPULNZUMNLYMYOUBLACUNZUAYL
      YPCYPUOZACUPSZCYQUQNSZFCURUSZAIMYKYQYLAYFMSZUTZYFCEAYSUUBFVAZAECVKNSZUUBG
      VAUUCYFAUUBVBVCZVDZYLUOVEZAUAUCZMSZUTZEUUIYJPZEUUIKVFPZYJPZUUIYLNUUMYLNUU
      KUUIUUMCEAYSUUJFVAZAUUEUUJGVAZUUKUUIAUUJVBZVCZUUKUUMUUKUUIUUQVGZVCZUUKUUI
      UURVHVIUUKIUUIYKUULMYLYQUUKYLVJZUUKYFUUITZUTYFUUIEYJUUKUVBVBVLUUQUUKUUICE
      UUOUUPUURVDVMUUKIUUMYKUUNMYLYQUVAUUKYFUUMTZUTYFUUMEYJUUKUVCVBVLUUSUUKUUMC
      EUUOUUPUUTVDVMVNVOAYOYMYPQKUJPZYRAYQUVDCVPMYQYLVPMUVDYMVPAJYQJUCZCNZUVDCA
      YTCYQVQZCJYQUVFOTZUUAYQCVRUVGUVHJYQCVSVTWAZAYSUVEYQSUVFUVDSFUVECWCWBWDUUH
      MYQUVDCYLWEWFAYSYNYQSYOUVDSFAYNYQUHZYQACIEFGWGZACFWHWIYNCWCWFQWJSRWJSQQUD
      LKRWKLZUVDQRWNPWLWOWMWPKWQSUVLXFKWRWSQRQKWTXAXBXCAYMIMYKCNZOYHAIJMYQYKUVF
      UVMYLCUUGAYLVJUVIUVEYKCXDXEAIMYGUVMUUCBYFEBUCZYJPZCNZUVMWQDWQADBWQUVPOZTU
      UBHVAUUCUVNYFTZUTZUVOYKCUVSUVNYFEYJUUCUVRVBVLXGUUFUUCYKCUUDUUGXHVMXIXJAYO
      UVJCNZKAYNUVJCUVKXGAYSUVTKTFCXKUSXLXMAKXNSDXOSYEYIXPXQADUVQXOHBWQUVPXRXSX
      TKIDYHKXOMYAYHUOYBYCYD $.

    $( The limit at minus infinity of the cumulative distribution function is
       zero. $)
    $( dstfrvclim0 #p |- ( ph -> ( x e. RR |-> ( F ` -u x ) ) ~~> 0 ) $=
      $. $)
  $}

$(

@(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Expected Value
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
@)

  @c Exp @. @( Symbol for the expected value, 'exp' @)

  cexpt @a class Exp @.

  @( Define the expected value of a random variable as the integral of the
     variable, over the entire probability space. An expected value is defined
     with respect to a given probability measure ` p ` .
     (Contributed by Thierry Arnoux, 15-Jan-2017.) @)
  df-expt @a |- Exp = ( p e. Prob |->
    ( x e. ( rRndVar ` p ) |-> S.m U. dom p x _d p ) ) @.

  @{
    @d p x P @. @d p x ph @. @d x X @.
    exptval.1 @e |- ( ph -> P e. Prob ) @.
    exptval.2 @e |- ( ph -> E = ( Exp ` P ) ) @.
    @{
      exptval.3 @e |- ( ph -> X e. ( rRndVar ` P ) ) @.
      @( Expected value with respect to probability measure ` P ` .
         (Contributed by Thierry Arnoux, 15-Jan-2017.) @)
      exptval   @p |- ( ph -> ( E ` X ) =  S.m U. dom P X _d P ) @=
        ( vx vp cdm cuni cv citgm crrv cfv cexpt cmpt cvv wceq eqidd cr df-expt
        cprb a1i wa simpr fveq2d dmeqd unieqd itgmeq123dTMP mpteq12dv wcel fvex
        mptexg mp1i fvmptd eqtrd probmeasd rrvf2 rrvdmss probtotrnd itgmclrdTMP
        unveldomd ) AHDBJZKZHLZBMZVEDBMBNOZCUAACBPOHVHVGQZFAIBHILZNOZVJJZKZVFVJ
        MZQZVIUCPRPIUCVOQSAHIUBUDAVJBSZUEZHVKVNVHVGVQVJBNAVPUFZUGVQVMVEBVFVFVJV
        QVLVDVQVJBVRUHUIVQVFTVRUJUKEVHRULVIRULABNUMHVHVGRUNUOUPUQAVFDSZUEZVEVEB
        VFDBVTVETAVSUFVTBTUJGAVEDBABEURABDEGUSABDEGUTABEVCABEVAVBUP @.

      @( Expected values are real numbers.
         (Contributed by Thierry Arnoux, 20-Jan-2017.) @)
      exptvrn   @p |- ( ph -> ( E ` X ) e. RR ) @=
        ( cfv cdm citgm cr exptval probmeasd rrvf2 rrvdmss unveldomd probvalrnd
        cuni itgmclrdTMP eqeltrd ) ADCHBIRZDBJKABCDEFGLAUADBABEMABDEGNABDEGOABE
        PZAUABEUBQST @.
    @}

    @{
      exptind.1 @e |- ( ph -> A e. dom P ) @.
      @( The expected value of the indicator function of the set ` A `
         is the probability of ` A ` .
         (Contributed by Thierry Arnoux, 20-Jan-2017.) @)
      exptind   @p |- ( ph -> ( E ` ( U. dom P _Ind A ) ) = ( P ` A ) ) @=
        ( cfv citgm cun wcel wceq syl co cc0 c0 a1i cres cuni cdif crrv syl2anc
        cdm cind cprb indrrv fveq1d eleq1d mpbird exptval wss undif itgmeq1dTMP
        elssuni sylib cxad cin disjdif itgmunTMP c1 csn cxp itgmresTMP unveldom
        cmul indval2 eqtrd reseq1d resundir ssid xpssres ax-mp eqeq1i xpdisjres
        incom mpbi uneq12i un0 3eqtri syl6eq itgmeq2dTMP 3eqtr3rd cr probvalrnd
        inidm 1re itgmcst recnd mulid2 3eqtrd uncom eqtri csiga crn domprobsiga
        cc difelsiga syl3anc 0re mul02 oveq12d cxr rexrd xaddid1 3eqtr2d ) ABEJ
        ZDJCUEZUAZXHCKBXJBUBZLZXHCKZBCJZACDXHFGAXHCUCJZMBXJUFJZJZXOMZACUGMZBXIM
        ZXRFHBCUHUDAXHXQXOABEXPIUIZUJUKULAXLXJXHCABXJUMZXLXJNAXTYBHBXIUPOZBXJUN
        UQUOAXMBXHCKZXKXHCKZURPXNQURPZXNABXKXHCBXKUSZRNZABXJUTZSVAAYDXNYEQURAYD
        BBVBVCZVDZCKZVBXNVGPZXNABXHBTZCKZBBUSZXHCKZYLYDYOYQNABBXHCVESABYNYKCAYN
        YKXKQVCZVDZLZBTZYKAXHYTBAXHXQYTYAAXJXIMZYBXQYTNAXSUUBFCVFOZYCBXJXIVHUDV
        IZVJUUAYKBTZYSBTZLYKRLYKYKYSBVKUUEYKUUFRBBUMZUUEYKNBVLZBYJBVMVNXKBUSZRN
        ZUUFRNYHUUJYIYGUUIRBXKVQVOVRXKYRBVPVNVSYKVTWAWBWCAYPBXHCYPBNABWGSUOWDAB
        BVBCHUUGAUUHSVBWEMAWHSABCFHWFZWIAXNWRMYMXNNAXNUUKWJXNWKOWLAYEXKYSCKZQXK
        CJZVGPZQAXKXHXKTZCKZXKXKUSZXHCKZUULYEUUPUURNAXKXKXHCVESAXKUUOYSCAUUOYTX
        KTZYSAXHYTXKUUDVJUUSYKXKTZYSXKTZLRYSLZYSYKYSXKVKUUTRUVAYSYHUUTRNYIBYJXK
        VPVNXKXKUMZUVAYSNXKVLZXKYRXKVMVNVSUVBYSRLYSRYSWMYSVTWNWAWBWCAUUQXKXHCUU
        QXKNAXKWGSUOWDAXKXKQCAXIWOWPUAMZUUBXTXKXIMAXSUVEFCWQOUUCHXJBXIWSWTZUVCA
        UVDSQWEMAXASAXKCFUVFWFZWIAUUMWRMUUNQNAUUMUVGWJUUMXBOWLXCAXNXDMYFXNNAXNU
        UKXEXNXFOWLXG @.
    @}

    expt.3 @e |- ( ph -> X e. ( rRndVar ` P ) ) @.
    @{
      exptmulc.1 @e |- ( ph -> C e. RR ) @.
      @( The expected value of a random variable multiplied by a constant.
         (Contributed by Thierry Arnoux, 16-Jan-2017.) @)
      exptmulc   @p |- ( ph -> ( E ` ( X oFC x. C ) ) = ( ( E ` X ) x. C ) ) @=
        ( cdm cuni cmul cofc co citgm cfv probmeasd rrvf2 rrvdmss exptval
        unveldomd probtotrnd itgmmulc2TMP rrvmulc oveq1d 3eqtr4d ) ACJKZEBLMNZC
        OUGECOZBLNUHDPEDPZBLNAUGBECACFQACEFHRACEFHSACFUAACFUBIUCACDUHFGABCEFHIU
        DTAUJUIBLACDEFGHTUEUF @.
    @}

    @{
      exptadd.1 @e |- ( ph -> Y e. ( rRndVar ` P ) ) @.
      @( The sum of expected values is the expected value of the sum.
         (Contributed by Thierry Arnoux, 15-Jan-2017.) @)
      exptadd   @p |- ( ph ->
                          ( E ` ( X oF + Y ) ) = ( ( E ` X ) + ( E ` Y ) ) ) @=
        ( cdm cuni caddc cof co citgm cfv probmeasd rrvf2 rrvdmss exptval
        unveldomd probtotrnd itgmaddTMP rrvadd oveq12d 3eqtr4d ) ABJKZDELMNZBOU
        GDBOZUGEBOZLNUHCPDCPZECPZLNAUGDEBABFQABDFHRABEFIRABDFHSABEFISABFUAABFUB
        UCABCUHFGABDEFHIUDTAUKUIULUJLABCDFGHTABCEFGITUEUF @.

      exptle.1 @e |- ( ph -> X oR <_ Y ) @.
      @( If two random variables compare, so do their expected values.
         (Contributed by Thierry Arnoux, 15-Jan-2017.) @)
      exptle   @p |- ( ph -> ( E ` X ) <_ ( E ` Y ) ) @=
        ( cdm cuni citgm cfv cle cofr wbr itgmleTMP syl exptval 3brtr4d ) ABKLZ
        DBMZUBEBMZDCNECNOADEOPQUCUDOQJUBDEBRSABCDFGHTABCEFGITUA @.
    @}

    @{
      @d b x A @. @d b I @. @d b p x P @. @d b x X @. @d b p x ph @.
      markovneq.1 @e |- ( ph -> A e. RR+ ) @.
      markovneq.2 @e |- ( ( ph /\ b e. U. dom P ) -> 0 <_ ( X ` b ) ) @.
      markovneq.3 @e |- ( ph -> ( E ` X ) e. RR ) @.
      @{
        @( Lemma for Markov's Inequality
           (Contributed by Thierry Arnoux, 21-Jan-2017.)
           (Revised by Thierry Arnoux, 4-Feb-2017.) @)
        markovneqlem   @p |- ( ph ->
                 ( ( U. dom P _Ind ( X oRVC `' <_ A ) ) oFC x. A ) oR <_ X ) @=
          ( cle cmul wcel cc0 cvv cr ccnv corvc co cfv cofc cofr wbr cv cif cdm
          cuni wral wa crp elorrvc ifbid wn wo exmid a1i pm4.24 wb rpred brcnvg
          fvex sylancr adantr anbi2d syl5bb biantrud orbi12d mpbid breq1 elimif
          sylibr ralrimiva crrv cind cprb orvcgteel indrrv fveq1d eleq1d mpbird
          eqbrtrd syl2anc rrvfn csiga domprobsiga elex uniexb sylib ofcfn inidm
          crn 3syl c1 cmpt wss wceq elssuni syl indval eqtrd 1re ifclda fvmpt2d
          0re ofcval ovif rpcnd mulid2d mul02d ifeq12d syl5eq eqidd ofrfval ) A
          FBOUAZUBUCZEUDZBPUEUCZFOUFUGGUHZXSQZBRUIZYBFUDZOUGZGCUJZUKZULAYFGYHAY
          BYHQZUMZYDYEBXRUGZBRUIZYEOYJYCYKBRAGBCXRUNFHJKUOUPYJYKBYEOUGZUMZYKUQZ
          RYEOUGZUMZURZYLYEOUGZYJYKYOURZYRYTYJYKUSUTYJYKYNYOYQYKYKYKUMYJYNYKVAY
          JYKYMYKAYKYMVBZYIAYESQBTQUUAYBFVEABKVCZYEBSTOVDVFVGVHVIYJYPYOLVJVKVLY
          KYSYMYPBRYLBYEOVMYLRYEOVMVNVOWEVPAGYHYHYDYEOYHYAFSSAYHBPXTSTACXTHAXTC
          VQUDZQXSYHVRUDZUDZUUCQZACVSQZXSYGQZUUFHABCFHJUUBVTZXSCWAWFAXTUUEUUCAX
          SEUUDNWBZWCWDWGZAYGSQZYHSQZAUUGYGWHWOUKZQUULHCWIYGUUNWJWPYGWKWLZUUBWM
          ACFHJWGUUOUUOYHWNYJYBYAUDYCWQRUIZBPUCZYDAYHUUPBPXTSTYBUUKUUOUUBAGYHUU
          PXTTAXTUUEGYHUUPWRZUUJAUUMXSYHWSZUUEUURWTUUOAUUHUUSUUIXSYGXAXBGXSYHSX
          CWFXDAUUPTQYIAYCWQRTWQTQAYCUMXEUTRTQAYCUQUMXHUTXFVGXGXIAUUQYDWTYIAUUQ
          YCWQBPUCZRBPUCZUIYDYCWQRBPXJAYCUUTBUVARABABKXKZXLABUVBXMXNXOVGXDYJYEX
          PXQWD @.
      @}

      @( Markov's Inequality
         (Contributed by Thierry Arnoux, 21-Jan-2017.)
         (Revised by Thierry Arnoux, 4-Feb-2017.) @)
      markovneq   @p |- ( ph ->
                         ( P ` ( X oRVC `' <_ A ) ) <_ ( ( E `  X ) / A ) ) @=
        ( vx cle co cfv cmul wbr cr wcel ccnv corvc cdiv cpnf cico cv crab cioo
        rpred crn ctg ccld wb wal wceq wa elicopnf brcnvg expcom pm5.32d bitr4d
        syl rabid syl6bbr alrimiv nfcv nfrab1 cleqf icopnfcld eqeltrrd orrvccel
        sylibr probvalrnd remulcld cuni cind cofc cprb orvcgteel indrrv syl2anc
        crrv exptmulc eqidd exptind oveq1d rrvmulc markovneqlem exptle eqbrtrrd
        cdm eqtrd lediv1dd recnd rpne0d divcan4d breq1d mpbid ) AEBNUAZUBOZCPZB
        QOZBUCOZEDPZBUCOZNRXAXENRAXBXDBAXABAWTCGAMBCWSSEGIABJUIZABUDUEOZMUFZBWS
        RZMSUGZUHUJUKPULPZAXHXGTZXHXJTZUMZMUNXGXJUOAXNMAXLXHSTZXIUPZXMAXLXOBXHN
        RZUPZXPABSTZXLXRUMXFBXHUQVBAXSXPXRUMXFXSXOXIXQXOXSXIXQUMXHBSSNURUSUTVBV
        AXIMSVCVDVEMXGXJMXGVFXIMSVGVHVLAXSXGXKTXFBVIVBVJVKZVMZXFVNLJAWTCWKZVOVP
        PZPZBQVQOZDPZXBXDNAYFYDDPZBQOXBABCDYDGHACVRTWTYBTYDCWBPTGABCEGIXFVSWTCV
        TWAZXFWCAYGXABQAWTCDYCGHXTAYCWDZWEWFWLACDYEEGHABCYDGYHXFWGIABCDYCEFGHIJ
        KLYIWHWIWJWMAXCXAXENAXABAXAYAWNABXFWNABJWOWPWQWR @.
    @}

  @}

  @{
    exptsum.1 @e |- ( ph -> P e. Prob ) @.
    exptsum.2 @e |- ( ph -> E = ( Exp ` P ) ) @.
    exptsum.3 @e |- ( ph -> X : NN --> ( rRndVar ` P ) ) @.
    exptsum.4 @e |- ( ( ph /\ N e. NN ) -> S = ( seq 1 ( oF + , X ) ` N ) ) @.
    @( The expected value of an indexed sum of random variables is the sum
       of the expected values. (Contributed by Thierry Arnoux, XX-May-2017.) @)
    exptsum @p |- ( ( ph /\ N e. NN ) ->
                       ( E ` S ) = sum_ i e. ( 1 ... N ) ( E ` ( X ` i ) ) ) @=
      ? @.
  @}

@(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Variance and Covariance
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
@)

  @c Var @. @( Symbol for the variance, 'var' @)
  @c Cov @. @( Symbol for the covariance, 'cov' @)

  cvar @a class Var @.
  ccov @a class Cov @.

  @( Define the variance of a random variable.
     (Contributed by Thierry Arnoux, 15-Jan-2017.) @)
  df-var @a |- Var = ( p e. Prob |-> ( x e. ( rRndVar ` p ) |-> ( ( Exp ` p ) `
  ( ( x oFC - ( ( Exp ` p ) ` x ) ) oFC ^ 2 ) ) ) ) @.

  @( Define the covariance of two random variables.
     (Contributed by Thierry Arnoux, 18-May-2017.) @)
  df-cov @a |- Cov = ( p e. Prob |->
    ( x e. ( rRndVar ` p ) , y e. ( rRndVar ` p ) |-> ( ( Exp ` p ) `
    ( ( x oFC - ( ( Exp ` p ) ` x ) ) oFC x. ( y oFC - ( ( Exp ` p ) ` y ) ) )
    ) ) ) @.

  @{
    @d p x E @. @d p x P @. @d p x ph @. @d x X @.
    varval.1 @e |- ( ph -> P e. Prob ) @.
    varval.2 @e |- ( ph -> E = ( Exp ` P ) ) @.
    varval.3 @e |- ( ph -> V = ( Var ` P ) ) @.
    varval.4 @e |- ( ph -> X e. ( rRndVar ` P ) ) @.
    @( Value of the variance of the random variable ` X ` .
       (Contributed by Thierry Arnoux, 15-Jan-2017.) @)
    varval   @p |- ( ph -> ( V ` X ) =
      ( E ` ( ( X oFC - ( E ` X ) ) oFC ^ 2 ) ) ) @=
      ( vx vp cfv co c2 crrv cvv cvar cmpt wceq fveq2d cmin cofc cexp
      cv cexpt cprb df-var a1i wa adantr eqtr4d fveq1d oveq2d oveq1d
      simpr fveq12d mpteq12dv wcel fvex mptexg fvmptd eqtrd oveq12d
      syl ) AJEJUDZVECLZUAUBZMZNUCUBZMZCLZEECLZVGMZNVIMZCLZBOLZDPADBQ
      LJVPVKRZHAKBJKUDZOLZVEVEVRUELZLZVGMZNVIMZVTLZRZVQUFQPQKUFWERSAJ
      KUGUHAVRBSZUIZJVSWDVPVKWGVRBOAWFUOZTWGWCVJVTCWGVTBUELZCWGVRBUEW
      HTACWISWFGUJUKZWGWBVHNVIWGWAVFVEVGWGVEVTCWJULUMUNUPUQFAVPPURZVQ
      PURWKABOUSUHJVPVKPUTVDVAVBAVEESZUIZVJVNCWMVHVMNVIWMVEEVFVLVGAWL
      UOZWMVEECWNTVCUNTIVOPURAVNCUSUHVA @.

    @( Variances are real numbers.
       (Contributed by Thierry Arnoux, 18-May-2017.) @)
    varvrn   @p |- ( ph -> ( V ` X ) e. RR ) @=
      ? @.

    @( Variances are non-negative.
       (Contributed by Thierry Arnoux, 18-May-2017.) @)
    varge0   @p |- ( ph -> 0 <_ ( V ` X ) ) @=
      ? @.

    @{
      @d b x A @. @d b I @. @d b p x P @. @d b x X @. @d b p x ph @.
      chebneq.1 @e |- ( ph -> A e. RR+ ) @.
      chebneq.2 @e |- ( ( ph /\ b e. U. dom P ) -> 0 <_ ( X ` b ) ) @.
      chebneq.3 @e |- ( ph -> ( E ` X ) e. RR ) @.
      @( Chebyshev's Inequality @)
      chebneq   @p |- ( ph ->
        ( P ` ( ( abs ` ( X oFC - ( E ` X ) ) ) oRVC `' <_ A ) )
                                              <_ ( ( V ` X ) / ( A ^ 2 ) ) ) @=
        ? @.
     @}
  @}

  @{
    @d p x E @. @d p x P @. @d p x ph @. @d x X @.
    covval.1 @e |- ( ph -> P e. Prob ) @.
    covval.2 @e |- ( ph -> E = ( Exp ` P ) ) @.
    covval.3 @e |- ( ph -> C = ( Cov ` P ) ) @.
    @{
      covval.4 @e |- ( ph -> X e. ( rRndVar ` P ) ) @.
      covval.5 @e |- ( ph -> Y e. ( rRndVar ` P ) ) @.
      @( Value of the variance of the random variable ` X ` .
         (Contributed by Thierry Arnoux, 15-Jan-2017.) @)
      covval   @p |- ( ph -> ( X C Y ) =
        ( E ` ( ( X oFC - ( E ` X ) ) oFC x. ( Y oFC - ( E ` Y ) ) ) ) ) @=
        ? @.

      @( Covariance is symmetric. @)
      covsym @p |- ( ph -> ( X C Y ) = ( Y C X ) ) @=
        ? @.
    @}

    @{
      covid.4 @e |- ( ph -> V = ( Var ` P ) ) @.
      covid.5 @e |- ( ph -> X e. ( rRndVar ` P ) ) @.
      @( The covariance of a random variable with itself is its variance. @)
      covid @p |- ( ph -> ( X C X ) = ( V ` X ) ) @=
        ? @.

    @}

    @{
      varsum.3 @e |- ( ph -> V = ( Var ` P ) ) @.
      varsum.5 @e |- ( ph -> X : NN --> ( rRndVar ` P ) ) @.
      varsum.6 @e |- ( ( ph /\ N e NN ) -> S = ( seq 1 ( oF + , X ) ` N ) ) @.
      @( Sum of the variance of a sequence of random variables ` X ` .
         (Contributed by Thierry Arnoux, XX-May-2017.) @)
      varsum @p |- ( ( ph /\ N e. NN ) -> ( V ` S ) =  sum_ i e. ( 1 ... N )
        sum_ j e. ( 1 ... N ) ( ( X ` i ) C ( X ` j ) ) ) @=
        ? @.

      @( Sum of the variance of a sequence of random variables ` X ` ,
         expressed using the sum of the variances.
         (Contributed by Thierry Arnoux, XX-May-2017.) @)
      varsum2 @p |- ( ( ph /\ N e. NN ) -> ( V ` S ) = (
        sum_ i e. ( 1 ... N ) ( V ` ( X ` i ) ) + ( 2 x. sum_ i e. ( 1 ... N )
        sum_ j e. ( 1 ..^ i ) ( ( X ` i ) C ( X ` j ) ) ) ) ) @=
        ? @.
    @}
  @}

$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Probabilities - example
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y H $.  $d x y T $.  $d y P $.  $d y X $.  $d x y ph $.
    $( Coin-flip is a usual example in the probability theory.
       Here we use two sets ` H ` for heads, and ` T ` for tails.
       We assume a uniform probability for heads and tails.
       A random variable ` X ` is defined, yielding to a result of 1 for heads
       and 0 for tails. $)

    coinflip.h $e |- H e. _V $.
    coinflip.t $e |- T e. _V $.
    coinflip.th $e |- H =/= T $.
    coinflip.2 $e |- P = ( ( # |` ~P { H , T } ) oFC / 2 ) $.
    coinflip.3 $e |- X = { <. H , 1 >. , <. T , 0 >. } $.
    $( Division in the extended real numbers can be used for the coin-flip
       example.  (Contributed by Thierry Arnoux, 15-Jan-2017.) $)
    coinfliplem $p |- P = ( ( # |` ~P { H , T } ) oFC /e 2 ) $=
      ( vx chash c2 cdiv co cxdiv wcel wceq cr cfn a1i vy cpr cpw cres cofc cvv
      cv wa cfv simpr fvres syl cn0 wss prfi elpwid ssfi sylancr hashcl eqeltrd
      nn0red cc0 wne 2re 2ne0 rexdiv syl3anc hashresfn pwfi mpbi ofcfeqd2 ax-mp
      wfn eqtr4i ) AKCBUBZUCZUDZLMUENZVQLOUENZHCUFPZVSVRQEVTJUAVPRLMOVQSRVTJUGZ
      VPPZUHZWAVQUIZWAKUIZRWCWBWDWEQVTWBUJZWAVPKUKULWCWEWCWASPZWEUMPWCVOSPZWAVO
      UNWGCBUOZWCWAVOWFUPVOWAUQURWAUSULVAUTVTUAUGZRPZUHZWKLRPZLVBVCZWJLONWJLMNQ
      VTWKUJWMWLVDTWNWLVETWJLVFVGVQVPVMVTVPVHTVPSPZVTWHWOWIVOVIVJTWMVTVDTVKVLVN
      $.

    $( The ` P ` we defined for coin-flip is a probability law.  (Contributed
       by Thierry Arnoux, 15-Jan-2017.) $)
    coinflipprob $p |- P e. Prob $=
      ( chash cfv co cprb c2 wcel wceq eqeltri ax-mp cvv mp2an cres coinfliplem
      cpr cpw cuni cxdiv cofc unipw prex pwid fveq2i wne wb hashprg mpbi 3eqtri
      fvres oveq2i eqtr4i cmeas crp pwcntmeas 2rp probfinmeasb ) AJCBUCZUDZUAZV
      FUEZVGKZUFUGZLZMAVGNVJLVKABCDEFGHIUBVINVGVJVIVHJKZVEJKZNVHVFOVIVLPVHVEVFV
      EUHZVECBUIZUJQVHVFJUQRVHVEJVNUKCBULZVMNPZGCSOBSOVPVQUMEFCBSUNTUOUPZURUSVG
      VFUTKOZVIVAOVKMOVESOVSVOVESVBRVINVAVRVCQVFVGVDTQ $.

    $( The space of our coin-flip probability (Contributed by Thierry Arnoux,
       15-Jan-2017.) $)
    coinflipspace $p |- dom P = ~P { H , T } $=
      ( cdm chash cpr cpw c2 cdiv cvv wcel wfn cr a1i cres cofc dmeqi hashresfn
      co wceq prex pwexg mp1i 2re ofcfn fndm mp2b eqtri ) AJKCBLZMZUAZNOUBUEZJZ
      UPAURHUCCPQZURUPRUSUPUFEUTUPNOUQPSUQUPRUTUPUDTUOPQUPPQUTCBUGUOPUHUINSQUTU
      JTUKUPURULUMUN $.

    $( The universe of our coin-flip probability is ` { H , T } ` .
       (Contributed by Thierry Arnoux, 15-Jan-2017.) $)
    coinflipuniv $p |- U. dom P = { H , T } $=
      ( cdm cuni cpr cpw coinflipspace unieqi unipw eqtri ) AJZKCBLZMZKSRTABCDE
      FGHINOSPQ $.

    $( The ` X ` we defined for coin-flip is a random variable.  (Contributed
       by Thierry Arnoux, 12-Jan-2017.) $)
    coinfliprv $p |- X e. ( rRndVar ` P ) $=
      ( vy wcel cdm cr wf cbrsiga c1 cc0 cpr wss cvv crrv cfv cuni ccnv cv cima
      wral cop wne 1ex c0ex fpr ax-mp feq1i mpbir coinflipuniv feq2i wa 1re 0re
      pm3.2i prss mpbi fss mp2an crn imassrn dfdm4 eqtr3i sseqtri coinflipspace
      fdmi cpw eleq2i prex cnvexg imaexg mp2b elpw bitr2i biimpi mp1i rgen cprb
      eqeltri wb coinflipprob a1i isrrvv mpbir2an ) DAUAUBKZALZUCZMDNZDUDZJUEZU
      FZWLKZJOUGZWMPQRZDNZWTMSZWNXACBRZWTDNZXDXCWTCPUHZBQUHZRZNZCBUIXHGCBPQEFUJ
      UKULUMXCWTDXGIUNUOZWMXCWTDABCDEFGHIUPUQUOPMKZQMKZURXBXJXKUSUTVAPQMUJUKVBV
      CWMWTMDVDVEWRJOWQXCSZWRWPOKWQWOVFZXCWOWPVGDLXMXCDVHXCWTDXIVLVIVJXLWRWRWQX
      CVMZKXLWLXNWQABCDEFGHIVKVNWQXCDTKWOTKWQTKDXGTIXEXFVOWEDTVPWOWPTVQVRVSVTWA
      WBWCCTKZWKWNWSURWFEXOJADAWDKXOABCDEFGHIWGWHWIUMWJ $.

    $( The probability of heads is one-half.  (Contributed by Thierry Arnoux,
       15-Jan-2017.) $)
    coinflippv $p |- ( P ` { H } ) = ( 1 / 2 ) $=
      ( vx cfv chash c2 cdiv c1 wcel wceq cvv cn0 a1i csn cpr cpw cres cofc wss
      co fveq1i snsspr1 prex elpw2 biimpri cv fveq2 hashsng ax-mp syl6eq oveq1d
      cmpt pwex 2nn0 wa cfn prfi elpwi ssfi sylancr adantl hashcl syl cun hashf
      cpnf wf ssv feqresmpt ofcfval2 ovex fvmpt mp2b eqtri ) CUAZAKWBLCBUBZUCZU
      DZMNUEUGZKZOMNUGZWBAWFHUHWBWCUFZWBWDPZWGWHQCBUIWJWIWBWCCBUJZUKULJWBJUMZLK
      ZMNUGZWHWDWFWLWBQZWMOMNWOWMWBLKZOWLWBLUNCRPZWPOQECRUOUPUQURWQWFJWDWNUSQEW
      QJWDWMMNWERSWDRPWQWCWKUTTMSPWQVATWQWLWDPZVBWLVCPZWMSPWRWSWQWRWCVCPWLWCUFW
      SCBVDWLWCVEWCWLVFVGVHWLVIVJWQJRSVMUAVKZWDLRWTLVNWQVLTWDRUFWQWDVOTVPVQUPOM
      NVRVSVTWA $.

    $( The probability of tails is one-half.  (Contributed by Thierry Arnoux,
       5-Feb-2017.) $)
    coinflippvt $p |- ( P ` { T } ) = ( 1 / 2 ) $=
      ( csn cfv c1 c2 co cmin cdif wcel wceq ax-mp eqtri cdiv cuni coinflipprob
      cdm cprb cpr cpw prid1 snelpwi coinflipspace probdsb coinflipuniv difeq1i
      eleqtrri mp2an wne difprsn1 fveq2i coinflippv oveq2i 3eqtr3i 1mhlfehlf )
      BJZAKZLLMUANZONZVEAUDZUBZCJZPZAKZLVIAKZONZVDVFAUEQVIVGQVKVMRABCDEFGHIUCVI
      CBUFZUGZVGCVNQVIVOQCBEUHCVNUISABCDEFGHIUJUNVIAUKUOVJVCAVJVNVIPZVCVHVNVIAB
      CDEFGHIULUMCBUPVPVCRGCBUQSTURVLVELOABCDEFGHIUSUTVAVBT $.

$(
    @( The expectation of our gain is one-half.
       (Contributed by Thierry Arnoux, 12-Jan-2017.) @)
    coinflipexp @p |- ( ( Exp ` P ) ` X ) = ( 1 / 2 ) @=
      ( cfv c2 cxdiv co c1 cvv wcel wceq a1i ax-mp cc0 cexpt cpr chash cpw cres
      cofc citgm cdiv cuni cprb coinflipprob eqidd crrv coinfliprv coinflipuniv
      vy exptval coinfliplem itgmeq123dTMP eqtri itgmdiv3TMP cv prex itgmcntTMP
      cdm cesum oveq1i cxad fveq2 adantl cpnf cicc cop fveq1i wne 1ex fvpr1 cxr
      cle wbr cr ressxr 1re sselii 0le1 elxrge0 mpbir2an eqeltri c0ex fvpr2 0xr
      0le0 esumpr oveq12i xaddid1 3eqtri 2re 2ne0 rexdiv mp3an ) DAUAJZJZCBUBZD
      UCXCUDUEZKLUFMZUGZXCDXDUGZKLMZNKUHMZXBAVEUIZDAUGZXFCOPZXBXKQEXLAXADAUJPXL
      ABCDEFGHIUKRXLXAULDAUMJPXLABCDEFGHIUNRUQSXLXKXFQEXLXJXCXEDDAXJXCQXLABCDEF
      GHIUORXLDULAXEQXLABCDEFGHIURRUSSUTXCKDXDVAXHXCUPVBZDJZUPVFZKLMNKLMZXIXGXO
      KLXCOPXGXOQCBVCUPXCDXCOVDSVGXONKLXOCDJZBDJZVHMZNTVHMZNXLXOXSQEXLCBXNXQUPX
      ROOXMCQXNXQQXLXMCDVIVJXMBQXNXRQXLXMBDVIVJXLXLERBOPXLFRXQTVKVLMZPXLXQNYAXQ
      CCNVMBTVMUBZJZNCDYBIVNCBVOZYCNQGCBNTEVPVQSUTZNYAPNVRPZTNVSVTWAVRNWBWCWDZW
      ENWFWGWHRXRYAPXLXRTYAXRBYBJZTBDYBIVNYDYHTQGCBNTFWIWJSUTZTYAPTVRPTTVSVTWKW
      LTWFWGWHRYDXLGRWMSXQNXRTVHYEYIWNYFXTNQYGNWOSWPVGNWAPKWAPKTVOXPXIQWCWQWRNK
      WSWTWPWP @.
$)
  $}

$(
@(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
                      Uncorrelated random sequences
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
@)

  @c UnCorr @. @( Symbol for uncorrelated random samples @)
  cuncor @a class UnCorr @.

  @( Define a random sample as an indexed set of ` n ` random variables of
     the same probability measure ` p ` , which are not correlated when taken
     pairwise. @)
  df-uncor @a |- UnCorr = ( p e. Prob |-> { x e. ( ( rRndVar ` p ) ^m NN ) |
    A. i e. NN A. j e. NN  ( ( Exp ` p ) ` ( ( x ` i ) oF * ( x ` j ) ) ) =
    ( ( ( Exp ` p ) ` ( x ` i ) ) * ( ( Exp ` p ) ` ( x ` j ) ) ) } ) @.

  @{
    uncorval.1 @e |- ( ph -> P e. Prob ) @.
    uncorval.2 @e |- ( ph -> E = ( Exp ` P ) ) @.
    uncorval.3 @e |- ( ph -> X e. ( UnCorr ` P ) ) @.

    @( Elements of a sequence of random variables are random variables. @)
    uncorrnd @p |- ( ph -> X : NN --> ( rRndVar ` P ) ) @=
      ? @.

    @( Property of a sequence of pairwise uncorrelated random variables. @)
    uncorval @p |- ( ( ph /\ i e. NN /\ j e. NN ) ->
      ( E ` ( ( X ` i ) oF * ( X ` j ) ) ) =
      ( ( E ` ( X ` i ) ) * ( E ` ( X ` j ) ) ) ) @=
      ? @.

  @}
@(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
                               Convergence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
@)

  @c ~ms~> @. @( Symbol for convergence in mean square @)
  @c ~p~> @. @( Symbol for convergence in probability @)
  cmsli @a class ~ms~> @.
  cprl @a class ~p~> @.

  @( Define convergence in probability @)
  df-prl @a |- ~p~> = ( p e. Prob |-> { <. x , y >. | A. e e. RR+ ( n e. NN |->
    ( p ` ( ( abs o. ( ( x ` n ) oFC - y ) ) oRVC `' <_ e  ) ) ) ~~> 0 } ) @.

  @( Define convergence in mean square @)
  df-msli @a |- ~ms~> = ( p e. Prob |-> { <. x , y >. | ( n e. NN |->
    ( ( Exp ` p ) ` ( ( ( x ` n ) oFC - y ) oFC ^ 2 ) ) ) ~~> 0 } ) @.

  @{
    plival.1 @e |- ( ph -> P e. Prob ) @.
    @( Convergence in mean square is a relation. @)
    plirel @p |- ( ph -> Rel ( ~p~> ` P ) ) @=
      ? @.
    @( Convergence in mean square is a relation. @)
    mslirel @p |- ( ph -> Rel ( ~ms~> ` P ) ) @=
      ? @.

    plival.2 @e |- ( ph -> X : NN --> ( rRndVar ` P ) ) @.
    plival.3 @e |- ( ph -> Y e. RR ) @.
    @( Express the predicate: ` X ` converges in probability to ` Y ` . @)
    plival @p |- ( ph -> ( X ( ~ms~> ` P ) Y <-> A. e e. RR+ ( n e. NN |->
      ( P ` ( ( abs o. ( ( X ` n ) oFC - Y ) ) oRVC `' <_ e  ) ) ) ~~> 0 ) ) @=
      ? @.

    mslival.1 @e |- ( ph -> E = ( Exp ` P ) ) @.
    @( Express the predicate: ` X ` converges in mean square to ` Y ` . @)
    mslival @p |- ( ph -> ( X ( ~ms~> ` P ) Y <-> ( n e. NN |->
      ( E ` ( ( ( X ` n ) oFC - Y ) oFC ^ 2 ) ) ) ~~> 0 ) ) @=
      ? @.
  @}

@(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
                         Weak Law of Large Numbers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
@)
  @{
    @( Hypothesis for the Weak Law of Large Numbers. ` X ` is a random sample.
       ~ wllnms.5 expresses the fact that the random variables ` X ` are
       uncorrelated. ~ wllnms.9 defines ` S ` as the partial sum of ` X ` over
       ` ( 1 ... n ) ` . @)
    wllnms.1 @e |- ( ph -> P e. Prob ) @.
    wllnms.2 @e |- ( ph -> E = ( Exp ` P ) ) @.
    wllnms.3 @e |- ( ph -> V = ( Var ` P ) ) @.
    wllnms.4 @e |- ( ph -> X e. ( UnCorr ` P ) ) @.
    wllnms.5 @e |- ( ph -> C e. RR+ ) @.
    wllnms.6 @e |- ( ( ph /\ N e. NN ) -> M = ( E ` ( X ` N ) ) ) @.
    wllnms.7 @e |- ( ( ph /\ N e. NN ) -> ( V ` ( X ` N ) ) <_ C ) @.
    wllnms.8 @e |- ( ( ph /\ n e NN ) -> S = ( seq 1 ( oF + , X ) ` n ) ) @.

    @( Weak Law of Large Numbers - convergence in mean square @)
    wllnms @p |- ( ph -> ( n e. NN |-> ( S oFC / n ) ) ( ~ms~> ` P ) M ) @=
      ? @.

    @( Weak Law of Large Numbers - convergence in probability @)
    wllnp @p |- ( ph -> ( n e. NN |-> ( S oFC / n ) ) ( ~p~> ` P ) M ) @=
      ? @.
  @}
$)


