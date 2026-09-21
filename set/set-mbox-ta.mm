$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Thierry Arnoux
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Declare additional constants to be used as STS context-specific.
     These constants are used only in the STS MathML typesetting file,
     set-mathml.mmts, to describe alternate ways for expressions to be
     displayed. $)

  $( Constant used for displaying numbers only. MathML <mn> $)
  $c class-n $.

  $( Constant used for displaying formulas "on their own rows", where no
     brackets are necessary, like for example under/over a fraction bar, or
     below a square root radical. $)
  $c class-o $.

  $( Warn the parser about which particular formula prefixes are ambiguous.
     The set.mm grammar itself is not ambiguous, but some strings of symbols
     might be prefixes for entirely different expressions. For example,
     ` ( x e. A ` is a prefix for both the maps-to ` ( x e. A |-> B ) = C `
     and the expression ( x e. A /\ x e. B ) ` .
     Mario mentioned the name "garden path sentences" for those.

     LALR parsers would normally detect them as shift-reduce or
     reduce-reduce conflicts, but the current implementation of metamath-knife
     cannot, and therefore requires those hints. $)
  $( $j garden_path ( A   =>   ( ph ;
        type_conversions;
        garden_path ( x e. A   =>   ( ph ;
        garden_path { <.   =>   { A ;
        garden_path { <. <.   =>   { A ;
  $)


$[ set-mbox-ta-basics.mm $]


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Real and complex functions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Signum (sgn or sign) function - misc. additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Signum is idempotent.  (Contributed by Thierry Arnoux, 2-Oct-2018.) $)
  sgnsgn $p |- ( A e. RR* -> ( sgn ` ( sgn ` A ) ) = ( sgn ` A ) ) $=
    ( cxr wcel csgn cfv wceq cc0 c1 cneg id fveq2 eqeq12d sgn0 a1i clt wbr sgn1
    wa neg1rr rexri neg1lt0 sgnn mp2an sgn3da ) ABCZADEZDEZUFFGDEZGFZHDEZHFZHIZ
    DEZULFZAUEJUFGFZUGUHUFGUFGDKUOJLUFHFZUGUJUFHUFHDKUPJLUFULFZUGUMUFULUFULDKUQ
    JLUIUEAGFRMNUKUEGAOPRQNUNUEAGOPRULBCULGOPUNULSTUAULUBUCNUD $.

  $( If two real numbers are of same signs, so are their signs.  (Contributed
     by Thierry Arnoux, 12-Oct-2018.) $)
  sgnmulsgp $p |- ( ( A e. RR /\ B e. RR )
    -> ( 0 < ( A x. B ) <-> 0 < ( ( sgn ` A ) x. ( sgn ` B ) ) ) ) $=
    ( cr wcel wa cmul co csgn cfv c1 wceq cc0 clt 0lt1 simplr simpr wn ax-mp wb
    wbr breq2 mpbiri adantl cneg breqtrd cn0 1nn0 nn0nlt0 lt0neg1 mtbi pm2.21dd
    1re a1i gt0ne0d pm2.21ddne cxr ctp w3o remulcl rexrd adantr sgncl mpjao3dan
    eltpi 3syl impbida sgnpbi syl sgnmul breq2d 3bitr3d ) ACDBCDEZABFGZHIZJKZLV
    NMTZLVMMTZLAHIBHIFGZMTVLVOVPVOVPVLVOVPLJMTNVNJLMUAUBUCVLVPEZVNJUDZKZVOVNLKZ
    VOVSWAEZLVTMTZVOWCLVNVTMVLVPWAOVSWAPUEWDQWCJLMTZWDJUFDWEQUGJUHRJCDWEWDSULJU
    IRUJUMUKVSWBEZVOVNLVSWBPWFVNVLVPWBOUNUOVSVOPVSVMUPDZVNVTLJUQDWAWBVOURVLWGVP
    VLVMABUSUTZVAVMVBVNVTLJVDVEVCVFVLWGVOVQSWHVMVGVHVLVNVRLMABVIVJVK $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Integer powers - misc. additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d k A $.  $d k n B $.
    $( A lower bound for an exponentiation.  (Contributed by Thierry Arnoux,
       19-Aug-2017.) $)
    nexple $p |- ( ( A e. NN0 /\ B e. RR /\ 2 <_ B ) -> A <_ ( B ^ A ) ) $=
      ( wcel c2 cle wbr cexp co cc0 wceq wa simpr wi c1 id oveq2 breq12d imbi2d
      a1i letrd vk vn cn0 cr w3a cn simpl2 simpl3 cv caddc simpl 1nn0 1red 1le2
      2re expge1d simp1 nnred readdcld 3ad2ant2 remulcld nnnn0d reexpcld nnge1d
      cmul leadd2dd times2d breqtrrd nn0ge0d simp2r lemul2ad 0red 0le2 lemul1ad
      recnd simp3 expp1d 3exp a2d nnind 3impib syl3anc 0le1 exp0d eqtrd 3brtr4d
      oveq2d wo elnn0 biimpi 3ad2ant1 mpjaodan ) AUCCZBUDCZDBEFZUEZAUFCZABAGHZE
      FZAIJZWPWQKWQWNWOWSWPWQLWMWNWOWQUGWMWNWOWQUHWQWNWOWSWNWOKZUAUIZBXBGHZEFZM
      XANBNGHZEFZMXAUBUIZBXGGHZEFZMXAXGNUJHZBXJGHZEFZMXAWSMUAUBAXBNJZXDXFXAXMXB
      NXCXEEXMOXBNBGPQRXBXGJZXDXIXAXNXBXGXCXHEXNOXBXGBGPQRXBXJJZXDXLXAXOXBXJXCX
      KEXOOXBXJBGPQRXBAJZXDWSXAXPXBAXCWREXPOXBABGPQRXABNWNWOUKZNUCCXAULSXANDBXA
      UMDUDCZXAUOSZXQNDEFXAUNSWNWOLZTUPXGUFCZXAXIXLYAXAXIXLYAXAXIUEZXJXHBVEHZXK
      EYBXJXGBVEHZYCYBXGNYBXGYAXAXIUQZURZYBUMZUSZYBXGBYFXAYAWNXIXQUTZVAZYBXHBYB
      BXGYIYBXGYEVBZVCZYIVAYBXJXGDVEHZYDYHYBXGDYFXRYBUOSZVAYJYBXJXGXGUJHYMEYBNX
      GXGYGYFYFYBXGYEVDVFYBXGYBXGYFVOVGVHYBDBXGYNYIYFYBXGYKVIYAWNWOXIVJVKTYBXGX
      HBYFYLYIXAYAIBEFXIXAIDBXAVLXSXQIDEFXAVMSXTTUTYAXAXIVPVNTYBBXGYBBYIVOYKVQV
      HVRVSVTWAWBWPWTKZINAWREINEFYOWCSWPWTLZYOWRBIGHNYOAIBGYPWGYOBYOBWMWNWOWTUG
      VOWDWEWFWMWNWQWTWHZWOWMYQAWIWJWKWL $.
  $}

  ${
    $d K m $.  $d K n $.  $d X m $.  $d X n $.  $d m ph $.  $d n ph $.
    2exple2exp.1 $e |- ( ph -> X e. NN ) $.
    2exple2exp.2 $e |- ( ph -> K e. NN0 ) $.
    2exple2exp.3 $e |- ( ph -> ( 2 ^ K ) || X ) $.
    2exple2exp.4 $e |- ( ph -> X <_ ( 2 ^ ( K + 1 ) ) ) $.
    $( If a nonnegative integer ` X ` is a multiple of a power of two, but less
       than the next power of two, it is itself a power of two.  (Contributed
       by Thierry Arnoux, 19-Oct-2025.) $)
    2exple2exp $p |- ( ph -> E. n e. NN0 X = ( 2 ^ n ) ) $=
      ( vm c2 co cexp clt wbr wceq cn0 wa wcel cmul cn c1 caddc cv oveq2 eqeq2d
      wrex adantr cc0 wn simplr nnnn0d 2nn a1i nnexpcld nncnd ad3antrrr mulcomd
      cc simpr simpllr expp1d breqtrd eqbrtrd nnred cr 2re nnrpd ltmul2d mpbird
      2cnd nnne0d neneqd nn0lt2 orcanai syl21anc oveq1d mullidd cdvds nndivides
      3eqtr3d biimpa r19.29a rspcedvdw peano2nn0 syl wo reexpcld leloe mpjaodan
      cle ) ADJCUAUBKZLKZMNZDJBUCZLKZOZBPUFDWLOZAWMQZWPDJCLKZOZBCPWNCOWOWSDWNCJ
      LUDUEACPRZWMFUGWRIUCZWSSKZDOZWTITWRXBTRZQZXDQZXCUAWSSKDWSXGXBUAWSSXGXBPRZ
      XBJMNZXBUHOZUIXBUAOZXGXBWRXEXDUJZUKXGXIWSXBSKZWSJSKZMNXGXMXCXNMXGWSXBAWSU
      RRWMXEXDAWSAJCJTRAULUMFUNZUOUPZXGXBXLUOUQXGXCDXNMXFXDUSZXGDWLXNMAWMXEXDUT
      XGJCXGVJAXAWMXEXDFUPVAVBVCVCXGXBJWSXGXBXLVDJVERZXGVFUMXGWSAWSTRZWMXEXDXOU
      PVGVHVIXGXBUHXGXBXLVKVLXHXIQXJXKXBVMVNVOVPXQXGWSXPVQVTAXDITUFZWMAXSDTRZWS
      DVRNZXTXOEGXSYAQYBXTIWSDVSWAVOUGWBWCAWQQWPWQBWKPWNWKOWOWLDWNWKJLUDUEAWKPR
      ZWQAXAYCFCWDWEZUGAWQUSWCADVERZWLVERZDWLWJNZWMWQWFZADEVDAJWKXRAVFUMYDWGHYE
      YFQYGYHDWLWHWAVOWI $.
  $}

  ${
    $d A p $.  $d N p $.  $d p ph $.
    expevenpos.mmp.1 $e |- ( ph -> A e. RR ) $.
    expevenpos.mmp.2 $e |- ( ph -> N e. NN0 ) $.
    expevenpos.mmp.3 $e |- ( ph -> 2 || N ) $.
    $( Even powers are positive.  (Contributed by Thierry Arnoux,
       9-Nov-2025.) $)
    expevenpos $p |- ( ph -> 0 <_ ( A ^ N ) ) $=
      ( vp c2 cv cmul co wceq cc0 cexp cle wbr cn0 wcel wa cr simplr simpr 2nn0
      ad2antrr resqcld sqge0d expge0d oveq2d recnd expmuld eqtr3d breqtrrd wrex
      a1i cdvds evennn02n biimpa syl2anc r19.29a ) AHGIZJKZCLZMBCNKZOPGQAUTQRZS
      ZVBSZMBHNKZUTNKZVCOVFVGUTVFBABTRVDVBDUDZUEAVDVBUAZVFBVIUFUGVFBVANKVCVHVFV
      ACBNVEVBUBUHVFBHUTVFBVIUIVJHQRVFUCUNUJUKULACQRZHCUOPZVBGQUMZEFVKVLVMGCUPU
      QURUS $.
  $}

  ${
    oexpled.1 $e |- ( ph -> A e. RR ) $.
    oexpled.2 $e |- ( ph -> B e. RR ) $.
    oexpled.3 $e |- ( ph -> N e. NN ) $.
    oexpled.4 $e |- ( ph -> -. 2 || N ) $.
    oexpled.5 $e |- ( ph -> A <_ B ) $.
    $( Odd power monomials are monotonic.  (Contributed by Thierry Arnoux,
       9-Nov-2025.) $)
    oexpled $p |- ( ph -> ( A ^ N ) <_ ( B ^ N ) ) $=
      ( cexp co cle wbr cc0 wa cr wcel adantr ad2antrr reexpcld 0red cn0 nnnn0d
      simpr leexp1ad adantlr c1 cmin cmul wceq caddc nncnd 1cnd npcand recnd cn
      oveq2d nnm1nn0 expp1d eqtr3d cz c2 cdvds wn nnzd oddm1even biimpa syl2anc
      syl expevenpos lemul2ad mul01d breqtrd eqbrtrd expge0d letrd lecasei cneg
      simplr renegcld le0neg1d leneg syl21anc oexpneg syl3anc 3brtr3d biimpar
      cc ) ABDJKZCDJKZLMZNCAUAFANCLMZOZWKNBWMUAABPQZWLERANBLMZWKWLAWOOBCDAWNWOE
      RACPQZWOFRADUBQZWOADGUCZRAWOUDABCLMZWOIRUEUFWMBNLMZOZWINWJXABDAWNWLWTESZA
      WQWLWTWRSZTXAUAZXACDAWPWLWTFSZXCTXAWIBDUGUHKZJKZBUIKZNLAWIXHUJWLWTABXFUGU
      KKZJKWIXHAXIDBJADUGADGULAUMUNUQABXFABEUOZADUPQZXFUBQGDURVIZUSUTSXAXHXGNUI
      KNLXABNXGXBXDAXGPQWLWTABXFEXLTSZANXGLMWLWTABXFEXLADVAQZVBDVCMVDZVBXFVCMZA
      DGVEHXNXOXPDVFVGVHVJSWMWTUDVKXAXGXAXGXMUOVLVMVNXACDXEXCAWLWTVSVOVPVQACNLM
      ZOZWIPQZWJPQZWJVRZWIVRZLMZWKXRBDAWNXQERZAWQXQWRRZTXRCDAWPXQFRZYETXRCVRZDJ
      KZBVRZDJKZYAYBLXRYGYIDAYGPQXQACFVTRAYIPQXQABEVTRYEAXQNYGLMACFWAVGXRWNWPWS
      YGYILMZYDYFAWSXQIRWNWPOWSYKBCWBVGWCUEAYHYAUJZXQACWHQXKXOYLACFUOGHCDWDWERA
      YJYBUJZXQABWHQXKXOYMXJGHBDWDWERWFXSXTOWKYCWIWJWBWGWCVQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Indicator Functions (continued)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d k A $.  $d k B $.  $d k O $.  $d k ph $.
    indsumin.1 $e |- ( ph -> O e. V ) $.
    indsumin.2 $e |- ( ph -> A e. Fin ) $.
    indsumin.3 $e |- ( ph -> A C_ O ) $.
    indsumin.4 $e |- ( ph -> B C_ O ) $.
    indsumin.5 $e |- ( ( ph /\ k e. A ) -> C e. CC ) $.
    $( Finite sum of a product with the indicator function / Cartesian product
       with the indicator function.  (Contributed by Thierry Arnoux,
       11-Dec-2021.) $)
    indsumin $p |- ( ph -> sum_ k e. A ( ( ( ( _Ind ` O ) ` B ) ` k ) x. C )
                        = sum_ k e. ( A i^i B ) C ) $=
      ( cmul co csu cc0 wceq wcel adantr sselda cind cfv cin cdif caddc inindif
      cv c0 a1i cun inundif eqcomi wa c1 cpr cc cr pr01ssre ax-resscn sstri wss
      wf indf syl2anc ffvelcdmd sselid mulcld fsumsplit inss2 ind1 oveq1d inss1
      syl3anc syldan mullidd eqtrd sumeq2dv ssdifd ind0 difssd mul02d cfn diffi
      syl cuz sumz olcs oveq12d infi fsumcl addridd 3eqtrd ) ABEUGZCFUAUBUBZUBZ
      DMNZEOBCUCZWPEOZBCUDZWPEOZUENWQDEOZPUENXAAWQWSWPBEWQWSUCUHQABCUFUIBWQWSUJ
      ZQAXBBBCUKULUIIAWMBRZUMZWODXDPUNUOZUPWOXEUQUPURUSUTXDFXEWMWNAFXEWNVBZXCAF
      GRZCFVAZXFHKCFGVCVDSABFWMJTVEVFLVGVHAWRXAWTPUEAWQWPDEAWMWQRZUMZWPUNDMNDXJ
      WOUNDMXJXGXHWMCRWOUNQAXGXIHSAXHXIKSAWQCWMWQCVAABCVIUITCFGWMVJVMVKXJDAXIXC
      DUPRZAWQBWMWQBVAABCVLUITLVNZVOVPVQAWTWSPEOZPAWSWPPEAWMWSRZUMZWPPDMNPXOWOP
      DMXOXGXHWMFCUDZRWOPQAXGXNHSAXHXNKSAWSXPWMABFCJVRTCFGWMVSVMVKXODAXNXCXKAWS
      BWMABCVTTLVNWAVPVQAWSWBRZXMPQZABWBRZXQIBCWCWDWSPWEUBVAXQXRWSEPWFWGWDVPWHA
      XAAWQDEAXSWQWBRIBCWIWDXLWJWKWL $.
  $}

  ${
    $d A k l $.  $d B k l $.  $d F k l $.  $d O k l $.  $d k l ph $.
    prodindf.1 $e |- ( ph -> O e. V ) $.
    prodindf.2 $e |- ( ph -> A e. Fin ) $.
    prodindf.3 $e |- ( ph -> B C_ O ) $.
    prodindf.4 $e |- ( ph -> F : A --> O ) $.
    $( The product of indicators is one if and only if all values are in the
       set.  (Contributed by Thierry Arnoux, 11-Dec-2021.) $)
    prodindf $p |- ( ph -> prod_ k e. A ( ( ( _Ind ` O ) ` B ) ` ( F ` k ) )
      = if ( ran F C_ B , 1 , 0 ) ) $=
      ( vl cfv c1 wceq wral cc0 cif wcel adantr cv cind cprod crn wss 2fveq3 wa
      cpr wf indf syl2anc ffvelcdmda ffvelcdmd fprodex01 wb eqeq1d cbvralvw a1i
      ifbid cmpt eqid rnmptss nfmpt1 nfrn nfcv nfss nfan simplr feqmptd fveq12d
      nfv eqidd ralrimivw r19.21bi wfn ffnd fneq1d mpbid simpr fnfvelrn eqeltrd
      adantlr sseldd ralrimi impbid2 ind1a syl3anc ralbidva rneqd sseq1d 3eqtrd
      ex 3bitr4d ) ABDUAZEMZCFUBMMZMZDUCLUAZEMWPMZNOZLBPZNQRWQNOZDBPZNQREUDZCUE
      ZNQRABWQWSDLWNWRWPEUFIAWNBSZUGZFQNUHZWOWPAFXHWPUIZXFAFGSZCFUEZXIHJCFGUJUK
      TABFWNEKULZUMUNAXAXCNQXAXCUOAWTXBLDBWRWNOWSWQNWRWNWPEUFUPUQURUSAXCXENQAWO
      CSZDBPZDBWOUTZUDZCUEZXCXEAXNXQDBWOCXOXOVAVBAXQXNAXQUGZXMDBAXQDADVKDXPCDXO
      DBWOVCVDDCVEVFVGXRXFXMXRXFUGXPCWOAXQXFVHAXFWOXPSXQXGWOWNXOMZXPAWOXSOZDBAX
      TDBAWNWNEXOADBFEKVIZAWNVLVJVMVNXGXOBVOZXFXSXPSAYBXFAEBVOYBABFEKVPABEXOYAV
      QVRTAXFVSBWNXOVTUKWAWBWCWLWDWLWEAXBXMDBXGXJXKWOFSXBXMUOAXJXFHTAXKXFJTXLCF
      GWOWFWGWHAXDXPCAEXOYAWIWJWMUSWK $.
  $}

  ${
    $d O x $.  $d V x $.  $d X x $.
    $( The indicator function of a singleton.  (Contributed by Thierry Arnoux,
       15-Feb-2026.) $)
    indsn $p |- ( ( O e. V /\ X e. O ) -> ( ( _Ind ` O ) ` { X } )
                                     = ( x e. O |-> if ( x = X , 1 , 0 ) ) ) $=
      ( wcel wa csn cind cfv cv cc0 cif cmpt wceq wss simpr snssd indval syldan
      c1 wb velsn a1i ifbid mpteq2dv eqtrd ) BCEZDBEZFZDGZBHIIZABAJZUJEZTKLZMZA
      BULDNZTKLZMUGUHUJBOUKUONUIDBUGUHPQAUJBCRSUIABUNUQUIUMUPTKUMUPUAUIADUBUCUD
      UEUF $.
  $}

  ${
    $d a x O $.  $d a V $.
    $( The bijection between a power set and the set of indicator functions.
       (Contributed by Thierry Arnoux, 14-Aug-2017.) $)
    indf1o $p |- ( O e. V ->
                        ( _Ind ` O ) : ~P O -1-1-onto-> ( { 0 , 1 } ^m O ) ) $=
      ( va vx wcel cpw cc0 c1 cpr cmap co cind cfv wf1o wel cif cmpt cr id 0red
      1red wne 0ne1 a1i eqid pw2f1o indv f1oeq1d mpbird ) ABEZAFZGHIAJKZALMZNUK
      ULCUKDADCOHGPQQZNUJCDAGHUNBRUJSUJTUJUAGHUBUJUCUDUNUEUFUJUKULUMUNDABCUGUHU
      I $.
  $}

  ${
    $d x F $.  $d x O $.  $d x V $.
    $( A function with range ` { 0 , 1 } ` as an indicator of the preimage of
       ` { 1 } ` .  (Contributed by Thierry Arnoux, 23-Aug-2017.) $)
    indpreima $p |- ( ( O e. V /\ F : O --> { 0 , 1 } ) ->
                                   F = ( ( _Ind ` O ) ` ( `' F " { 1 } ) ) ) $=
      ( vx wcel cc0 c1 cpr wf wa ccnv csn cima cfv adantl wceq simpr ffvelcdmda
      eleqtrdi wb cind wfn ffn wss cdm cnvimass sseqtrid indf syldan ffnd prcom
      fdm simpll adantr ind1a syl3anc fniniseg syl baibd bitr2d elpreq eqfnfvd
      cv ) BCEZBFGHZAIZJZDBAAKGLZMZBUANNZVFABUBZVDBVEAUCOZVGBVEVJVDVFVIBUDZBVEV
      JIVGAUEZVIBAVHUFVFVNBPVDBVEAULOUGZVIBCUHUIZUJVGDVCZBEZJZGFVQANZVQVJNZVSVT
      VEGFHZVGBVEVQAVDVFQRFGUKZSVSWAVEWBVGBVEVQVJVPRWCSVSWAGPZVQVIEZVTGPZVSVDVM
      VRWDWETVDVFVRUMVGVMVRVOUNVGVRQVIBCVQUOUPVGWEVRWFVGVKWEVRWFJTVLBGVQAUQURUS
      UTVAVB $.
  $}

  ${
    $d a f g O $.  $d a g V $.
    $( The bijection between finite subsets and the indicator functions with
       finite support.  (Contributed by Thierry Arnoux, 22-Aug-2017.) $)
    indf1ofs $p |- ( O e. V -> ( ( _Ind ` O ) |` Fin ) : ( ~P O i^i Fin )
         -1-1-onto-> { f e. ( { 0 , 1 } ^m O ) | ( `' f " { 1 } ) e. Fin } ) $=
      ( vg va wcel cfn cfv cima cres wf1o cv ccnv c1 cc0 wss wceq wa syldan wb
      cpw cin cind csn cpr cmap crab wf1 indf1o f1of1 syl f1ores sylancl resres
      co inss1 wfn f1ofn fnresdm 3syl reseq1d eqtr3id eqidd simpll simpr sselid
      wrex wf elpwid indf adantr feq1d mpbid prex elmapg biimpar syl2anc cnveqd
      cvv mpan imaeq1d indpi1 inss2 eqeltrd eqeltrrd rexlimdva2 cnvimass biimpa
      jca cdm fdmd adantrr sseqtrid simprr elfpw sylanbrc eqcomd fveqeq2 rspcev
      indpreima impbid fvelimab cnveq eleq1d elrab a1i 3bitr4d eqrdv f1oeq123d
      ex ) BCFZBUAZGUBZBUCHZXMIZXNXMJZKZXMALZMZNUDZIZGFZAONUEZBUFUOZUGZXNGJZKXK
      XLYDXNUHZXMXLPZXQXKXLYDXNKZYGBCUIZXLYDXNUJUKXLGUPZXLYDXMXNULUMXKXMXMXOYEX
      PYFXKXPXNXLJZGJYFXNXLGUNXKYLXNGXKYIXNXLUQZYLXNQYJXLYDXNURZXLXNUSUTVAVBXKX
      MVCXKDXOYEXKELZXNHZDLZQZEXMVGZYQYDFZYQMZXTIZGFZRZYQXOFZYQYEFZXKYSUUDXKYRU
      UDEXMXKYOXMFZRZYRRZYTUUCUUIXKBYCYQVHZYTXKUUGYRVDUUIBYCYPVHZUUJUUHUUKYRXKU
      UGYOBPZUUKUUHYOBUUHXMXLYOYKXKUUGVEZVFVIZYOBCVJSVKUUIBYCYPYQUUHYRVEZVLVMXK
      YTUUJYCVSFXKYTUUJTONVNYCBYQVSCVOVTZVPVQUUIYPMZXTIZUUBGUUIUUQUUAXTUUIYPYQU
      UOVRWAUUHUURGFYRUUHUURYOGXKUUGUULUURYOQUUNYOBCWBSUUHXMGYOXLGWCUUMVFWDVKWE
      WIWFXKUUDYSXKUUDRZUUBXMFZUUBXNHZYQQZYSUUSUUBBPUUCUUTUUSYQWJZUUBBYQXTWGXKY
      TUVCBQUUCXKYTRBYCYQXKYTUUJUUPWHZWKWLWMXKYTUUCWNUUBBWOWPXKYTUVBUUCXKYTUUJU
      VBUVDXKUUJRYQUVAYQBCWTWQSWLYRUVBEUUBXMYOUUBYQXNWRWSVQXJXAXKYMYHUUEYSTXKYI
      YMYJYNUKYKEXLXMYQXNXBUMUUFUUDTXKYBUUCAYQYDXRYQQZYAUUBGUVEXSUUAXTXRYQXCWAX
      DXEXFXGXHXIVM $.
  $}

  $( The support of the indicator function.  (Contributed by Thierry Arnoux,
     13-Oct-2025.) $)
  indsupp $p |- ( ( O e. V /\ A C_ O ) -> ( ( ( _Ind ` O ) ` A ) supp 0 ) = A )
    $=
    ( wcel wss wa cind cfv cc0 csupp co ccnv c1 cpr csn cdif cima cvv wceq a1i
    wf simpl c0ex fsuppeq imp syl21anc prcom difeq1i wne ax-1ne0 difprsn2 ax-mp
    indf eqtri imaeq2d indpi1 3eqtrd ) BCDZABEZFZABGHHZIJKZVALZIMNZIOZPZQZVCMOZ
    QAUTURIRDZBVDVAUAZVBVGSZURUSUBVIUTUCTABCUMURVIFVJVKVDVABCRIUDUEUFUTVFVHVCVF
    VHSUTVFMINZVEPZVHVDVLVEIMUGUHMIUIVMVHSUJMIUKULUNTUOABCUPUQ $.

  ${
    indfsd.1 $e |- ( ph -> O e. V ) $.
    indfsd.2 $e |- ( ph -> A C_ O ) $.
    indfsd.3 $e |- ( ph -> A e. Fin ) $.
    $( The indicator function of a finite set has finite support.  (Contributed
       by Thierry Arnoux, 18-Jan-2026.) $)
    indfsd $p |- ( ph -> ( ( _Ind ` O ) ` A ) finSupp 0 ) $=
      ( cind cfv cvv cc0 fvexd wcel c0ex a1i c1 cpr wss wf syl2anc ffund co cfn
      indf csupp wceq indsupp eqeltrd isfsuppd ) ABCHIZIZJJKABUJLKJMANOACKPQZUK
      ACDMZBCRZCULUKSEFBCDUDTUAAUKKUEUBZBUCAUMUNUOBUFEFBCDUGTGUHUI $.
  $}

  ${
    indfsid.1 $e |- ( ph -> O e. V ) $.
    indfsid.2 $e |- ( ph -> F : O --> { 0 , 1 } ) $.
    $( Conditions for a function to be an indicator function.  (Contributed by
       Thierry Arnoux, 18-Jan-2026.) $)
    indfsid $p |- ( ph -> F = ( ( _Ind ` O ) ` ( F supp 0 ) ) ) $=
      ( ccnv c1 csn cima cind cfv cc0 csupp co wcel cpr wf wceq cvv syl2anc a1i
      indpreima cdif c0ex fsuppeq imp syl21anc 0ne1 difprsn1 mp1i imaeq2d eqtrd
      wa wne fveq2d eqtr4d ) ABBGZHIZJZCKLZLZBMNOZVALACDPZCMHQZBRZBVBSEFBCDUCUA
      AVCUTVAAVCURVEMIUDZJZUTAVDMTPZVFVCVHSZEVIAUEUBFVDVIUNVFVJVEBCDTMUFUGUHAVG
      USURMHUOVGUSSAUIMHUJUKULUMUPUQ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Decimal expansion
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Define a decimal expansion constructor.  The decimal expansions built with
  this constructor are not meant to be used alone outside of this chapter.
  Rather, they are meant to be used exclusively as part of a decimal number
  with a decimal fraction, for example ` ( 3 . _ 1 _ 4 _ 1 _ 5 9 ) ` .

  That decimal point operator is defined in the next section.  The bulk of
  these constructions have originally been proposed by David A. Wheeler on
  12-May-2015, and discussed with Mario Carneiro in this thread:
  ~ https://groups.google.com/g/metamath/c/2AW7T3d2YiQ .

$)

  $c _ $. $( Decimal fraction indicator for digits after decimal point $)

  $( Constant used for decimal fraction constructor.  See ~ df-dp2 . $)
  cdp2 $a class _ A B $.

  $( Define the "decimal fraction constructor", which is used to build up
     "decimal fractions" in base 10.  This is intentionally similar to
     ~ df-dec .  (Contributed by David A. Wheeler, 15-May-2015.)  (Revised by
     AV, 9-Sep-2021.) $)
  df-dp2 $a |- _ A B = ( A + ( B / ; 1 0 ) ) $.

  $( Equality theorem for the decimal expansion constructor.  (Contributed by
     David A. Wheeler, 15-May-2015.) $)
  dp2eq1 $p |- ( A = B -> _ A C = _ B C ) $=
    ( wceq c1 cc0 cdc cdiv co caddc cdp2 oveq1 df-dp2 3eqtr4g ) ABDACEFGHIZJIBO
    JIACKBCKABOJLACMBCMN $.

  $( Equality theorem for the decimal expansion constructor.  (Contributed by
     David A. Wheeler, 15-May-2015.) $)
  dp2eq2 $p |- ( A = B -> _ C A = _ C B ) $=
    ( wceq c1 cc0 cdc cdiv co caddc cdp2 oveq1 oveq2d df-dp2 3eqtr4g ) ABDZCAEF
    GZHIZJICBQHIZJICAKCBKPRSCJABQHLMCANCBNO $.

  ${
    dp2eq1i.1 $e |- A = B $.
    $( Equality theorem for the decimal expansion constructor.  (Contributed by
       David A. Wheeler, 15-May-2015.) $)
    dp2eq1i $p |- _ A C = _ B C $=
      ( wceq cdp2 dp2eq1 ax-mp ) ABEACFBCFEDABCGH $.

    $( Equality theorem for the decimal expansion constructor.  (Contributed by
       David A. Wheeler, 15-May-2015.) $)
    dp2eq2i $p |- _ C A = _ C B $=
      ( wceq cdp2 dp2eq2 ax-mp ) ABECAFCBFEDABCGH $.

    dp2eq12i.2 $e |- C = D $.
    $( Equality theorem for the decimal expansion constructor.  (Contributed by
       David A. Wheeler, 15-May-2015.) $)
    dp2eq12i $p |- _ A C = _ B D $=
      ( cdp2 dp2eq1i dp2eq2i eqtri ) ACGBCGBDGABCEHCDBFIJ $.
  $}

  ${
    dp20u.1 $e |- A e. NN0 $.
    $( Add a zero in the tenths (lower) place.  (Contributed by Thierry Arnoux,
       16-Dec-2021.) $)
    dp20u $p |- _ A 0 = A $=
      ( cc0 cdp2 c1 cdc cdiv co caddc df-dp2 cc wcel wne 10nn0 nn0rei recni 0re
      wceq 10pos gtneii div0 mp2an oveq2i nn0cni addridi 3eqtri ) ACDACECFZGHZI
      HACIHAACJUHCAIUGKLUGCMUHCRUGUGNOPCUGQSTUGUAUBUCAABUDUEUF $.
  $}

  ${
    dp20h.1 $e |- A e. RR+ $.
    $( Add a zero in the unit places.  (Contributed by Thierry Arnoux,
       16-Dec-2021.) $)
    dp20h $p |- _ 0 A = ( A / ; 1 0 ) $=
      ( cc0 cdp2 c1 cdc cdiv co caddc df-dp2 crp wcel cc ax-mp 10nn0 nn0cni 0re
      rpcn 10pos gtneii divcli addlidi eqtri ) CADCAECFZGHZIHUECAJUEAUDAKLAMLBA
      RNUDOPCUDQSTUAUBUC $.
  $}

  $( Closure for the decimal fraction constructor if both values are reals.
     (Contributed by David A. Wheeler, 15-May-2015.) $)
  dp2cl $p |- ( ( A e. RR /\ B e. RR ) -> _ A B e. RR ) $=
    ( cr wcel wa cdp2 c1 cc0 cdc cdiv co caddc df-dp2 wne 10re gt0ne0ii redivcl
    10pos mp3an23 readdcl sylan2 eqeltrid ) ACDZBCDZEABFABGHIZJKZLKZCABMUDUCUFC
    DZUGCDUDUECDUEHNUHOUEORPBUEQSAUFTUAUB $.

  ${
    dp2clq.a $e |- A e. NN0 $.
    dp2clq.b $e |- B e. QQ $.
    $( Closure for a decimal fraction.  (Contributed by Thierry Arnoux,
       16-Dec-2021.) $)
    dp2clq $p |- _ A B e. QQ $=
      ( cdp2 c1 cc0 cdc cdiv co caddc cq df-dp2 cn0 nn0ssq sselii wne 10nn0 0re
      wcel 10pos gtneii qdivcl mp3an qaddcl mp2an eqeltri ) ABEABFGHZIJZKJZLABM
      ALTUILTZUJLTNLAOCPBLTUHLTUHGQUKDNLUHORPGUHSUAUBBUHUCUDAUIUEUFUG $.
  $}

  ${
    rpdp2cl.a $e |- A e. NN0 $.
    rpdp2cl.b $e |- B e. RR+ $.
    $( Closure for a decimal fraction in the positive real numbers.
       (Contributed by Thierry Arnoux, 16-Dec-2021.) $)
    rpdp2cl $p |- _ A B e. RR+ $=
      ( cdp2 c1 cc0 cdc cdiv co caddc crp wcel cr clt wbr ax-mp mp2an wa pm3.2i
      df-dp2 nn0rei rpssre cn 10nn nnrp rpdivcl sselii readdcl nn0ge0i addgegt0
      cle rpgt0 elrp mpbir2an eqeltri ) ABEABFGHZIJZKJZLABUAUSLMUSNMZGUSOPZANMZ
      URNMZUTACUBZLNURUCBLMUQLMZURLMZDUQUDMVEUEUQUFQBUQUGRZUHZAURUIRVBVCSGAULPZ
      GUROPZSVAVBVCVDVHTVIVJACUJVFVJVGURUMQTAURUKRUSUNUOUP $.
  $}

  ${
    rpdp2cl2.a $e |- A e. NN $.
    $( Closure for a decimal fraction with no decimal expansion in the positive
       real numbers.  (Contributed by Thierry Arnoux, 25-Dec-2021.) $)
    rpdp2cl2 $p |- _ A 0 e. RR+ $=
      ( cc0 cdp2 crp nnnn0i dp20u cn wcel nnrp ax-mp eqeltri ) ACDAEAABFGAHIAEI
      BAJKL $.
  $}

  ${
    dp2lt10.a $e |- A e. NN0 $.
    dp2lt10.b $e |- B e. RR+ $.
    dp2lt10.1 $e |- A < ; 1 0 $.
    dp2lt10.2 $e |- B < ; 1 0 $.
    $( Decimal fraction builds real numbers less than 10.  (Contributed by
       Thierry Arnoux, 16-Dec-2021.) $)
    dp2lt10 $p |- _ A B < ; 1 0 $=
      ( c1 cc0 co caddc clt c9 wbr 9p1e10 cz wcel wb mp2an cr wa cdc df-dp2 cle
      cdp2 cdiv breqtrri nn0zi 9nn0 zleltp1 mpbir crp rpssre sselii 10re elrpii
      divlt1lt wi nn0rei 0re gtneii redivcli pm3.2i 9re leltadd breqtri eqbrtri
      10pos 1re ) ABUDABGHUAZUEIZJIZVIKABUBVKLGJIZVIKALUCMZVJGKMZVKVLKMZVMAVLKM
      ZAVIVLKENUFAOPLOPVMVPQACUGLUHUGALUIRUJVNBVIKMZFBSPVIUKPVNVQQUKSBULDUMZVIU
      NVGUOBVIUPRUJASPZVJSPZTLSPZGSPZTVMVNTVOUQVSVTACURBVIVRUNHVIUSVGUTVAVBWAWB
      VCVHVBAVJLGVDRRNVEVF $.
  $}

  ${
    dp2lt.a $e |- A e. NN0 $.
    dp2lt.b $e |- B e. RR+ $.
    ${
      dp2lt.c $e |- C e. RR+ $.
      dp2lt.l $e |- B < C $.
      $( Comparing two decimal fractions (equal unit places).  (Contributed by
         Thierry Arnoux, 16-Dec-2021.) $)
      dp2lt $p |- _ A B < _ A C $=
        ( cc0 cdiv co caddc cdp2 clt cr wcel wbr crp rpssre 10re mp3an c1 10pos
        cdc w3a wne sselii 0re gtneii redivcl nn0rei 3pm3.2i pm3.2i ltdiv1 mpbi
        wa wb axltadd imp mp2an df-dp2 3brtr4i ) ABUAHUCZIJZKJZACVBIJZKJZABLACL
        MVCNOZVENOZANOZUDZVCVEMPZVDVFMPZVGVHVIBNOZVBNOZVBHUEZVGQNBREUFZSHVBUGUB
        UHZBVBUITCNOZVNVOVHQNCRFUFZSVQCVBUITADUJUKBCMPZVKGVMVRVNHVBMPZUOVTVKUPV
        PVSVNWASUBULBCVBUMTUNVJVKVLVCVEAUQURUSABUTACUTVA $.
    $}

    ${
      dp2ltsuc.1 $e |- B < ; 1 0 $.
      dp2ltsuc.2 $e |- ( A + 1 ) = C $.
      $( Comparing a decimal fraction with the next integer.  (Contributed by
         Thierry Arnoux, 25-Dec-2021.) $)
      dp2ltsuc $p |- _ A B < C $=
        ( c1 cc0 cdc cdiv co caddc cdp2 clt wbr crp wcel 10re mpbi cr rpre 10nn
        ax-mp 10pos ltdiv1ii recni nnne0i dividi breqtri redivcli nn0rei df-dp2
        1re ltadd2i eqcomi 3brtr4i ) ABHIJZKLZMLZAHMLZABNCOUSHOPUTVAOPUSURURKLZ
        HOBUROPUSVBOPFBURURBQRBUAREBUBUDZSSUEUFTURURSUGURUCUHZUIUJUSHABURVCSVDU
        KUNADULUOTABUMVACGUPUQ $.
    $}

    ${
      dp2ltc.c $e |- C e. NN0 $.
      dp2ltc.d $e |- D e. RR+ $.
      dp2ltc.s $e |- B < ; 1 0 $.
      dp2ltc.l $e |- A < C $.
      $( Comparing two decimal expansions (unequal higher places).
         (Contributed by Thierry Arnoux, 16-Dec-2021.) $)
      dp2ltc $p |- _ A B < _ C D $=
        ( c1 co caddc clt wbr cr wcel crp 10re mp2an cc0 cdc cdiv cle wb rpssre
        cdp2 sselii 10pos elrp mpbir2an divlt1lt mpbir gt0ne0ii redivcli nn0rei
        1re ltadd2 mp3an mpbi cz nn0zi zltp1le readdcli ltletri wa pm3.2i ax-mp
        rpdivcl ltaddrp lttri df-dp2 3brtr4i ) ABKUAUBZUCLZMLZCDVNUCLZMLZABUGCD
        UGNVPCNOZCVRNOZVPVRNOVPAKMLZNOZWACUDOZVSVOKNOZWBWDBVNNOZIBPQVNRQZWDWEUE
        RPBUFFUHZWFVNPQUAVNNOSUIVNUJUKZBVNULTUMVOPQKPQAPQWDWBUEBVNWGSVNSUIUNZUO
        ZUQAEUPZVOKAURUSUTACNOZWCJAVAQCVAQWLWCUEAEVBCGVBACVCTUTVPWACAVOWKWJVDZA
        KWKUQVDCGUPZVETCPQVQRQZVTWNDRQZWFVFWOWPWFHWHVGDVNVIVHCVQVJTVPCVRWMWNCVQ
        WNDVNRPDUFHUHSWIUOVDVKTABVLCDVLVM $.
    $}
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Decimal point
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Define the decimal point operator and the decimal fraction constructor.  This
  can model traditional decimal point notation, and serve as a convenient way
  to write some fractional numbers.  See ~ df-dp and ~ df-dp2 for more
  information; ~ dpval2 and ~ dpfrac1 provide a more convenient way to obtain a
  value.  This is intentionally similar to ~ df-dec .

$)

  $c . $. $( Decimal point. $)

  $( Decimal point operator.  See ~ df-dp . $)
  cdp $a class . $.

  ${
    $d x y $.

    $( Define the ` . ` (decimal point) operator.  For example,
       ` ( 1 . 5 ) = ( 3 / 2 ) ` , and
       ` -u ( ; 3 2 . _ 7 _ 1 8 ) = -u ( ; ; ; ; 3 2 7 1 8 / ; ; ; 1 0 0 0 ) `
       Unary minus, if applied, should normally be applied in front of the
       parentheses.

       Metamath intentionally does not have a built-in construct for numbers,
       so it can show that numbers are something you can build based on set
       theory.  However, that means that Metamath has no built-in way to parse
       and handle decimal numbers as traditionally written, e.g., "2.54".  Here
       we create a system for modeling traditional decimal point notation; it
       is not syntactically identical, but it is sufficiently similar so it is
       a reasonable model of decimal point notation.  It should also serve as a
       convenient way to write some fractional numbers.

       The RHS is ` RR ` , not ` QQ ` ; this should simplify some proofs.  The
       LHS is ` NN0 ` , since that is what is used in practice.  The definition
       intentionally does not allow negative numbers on the LHS; if it did,
       nonzero fractions would produce the wrong results.  (It would be
       possible to define the decimal point to do this, but using it would be
       more complicated, and the expression ` -u ( A . B ) ` is just as
       convenient.)  (Contributed by David A. Wheeler, 15-May-2015.) $)
    df-dp $a |- . = ( x e. NN0 , y e. RR |-> _ x y ) $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Define the value of the decimal point operator.  See ~ df-dp .
       (Contributed by David A. Wheeler, 15-May-2015.) $)
    dpval $p |- ( ( A e. NN0 /\ B e. RR ) -> ( A . B ) = _ A B ) $=
      ( vx vy cn0 cr cv cdp2 cdp c1 cc0 cdc cdiv caddc wceq df-dp2 oveq1 eqtrid
      co oveq2d eqtr4di df-dp ovexi ovmpo ) CDABEFCGZDGZHZABHZIAUFJKLZMSZNSZUEA
      OUGUEUJNSUKUEUFPUEAUJNQRUFBOZUKABUIMSZNSUHULUJUMANUFBUIMQTABPZUACDUBUHAUM
      NUNUCUD $.
  $}

  $( Prove that the closure of the decimal point is ` RR ` as we have defined
     it.  See ~ df-dp .  (Contributed by David A. Wheeler, 15-May-2015.) $)
  dpcl $p |- ( ( A e. NN0 /\ B e. RR ) -> ( A . B ) e. RR ) $=
    ( cn0 wcel cr wa cdp co cdp2 dpval nn0re dp2cl sylan eqeltrd ) ACDZBEDZFABG
    HABIZEABJOAEDPQEDAKABLMN $.

  $( Prove a simple equivalence involving the decimal point.  See ~ df-dp and
     ~ dpcl .  (Contributed by David A. Wheeler, 15-May-2015.)  (Revised by AV,
     9-Sep-2021.) $)
  dpfrac1 $p |- ( ( A e. NN0 /\ B e. RR ) -> ( A . B ) = ( ; A B / ; 1 0 ) ) $=
    ( cn0 wcel cr wa cdp2 c1 cc0 cdc cdiv co caddc df-dp2 dpval wceq nn0cn 10re
    cdp cc recn cmul dfdec10 oveq1i recni a1i id mulcld wne 10pos pm3.2i divdir
    gt0ne0ii mp3an3 sylan divcan3 mp3an23 oveq1d adantr eqtrid syl2an 3eqtr4a
    eqtrd ) ACDZBEDZFABGABHIJZKLZMLZABSLABJZVFKLZABNABOVDATDZBTDZVJVHPVEAQBUAVK
    VLFZVJVFAUBLZBMLZVFKLZVHVIVOVFKABUCUDVMVPVNVFKLZVGMLZVHVKVNTDZVLVPVRPZVKVFA
    VFTDZVKVFRUEZUFVKUGUHVSVLWAVFIUIZFVTWAWCWBVFRUJUMZUKVNBVFULUNUOVKVRVHPVLVKV
    QAVGMVKWAWCVQAPWBWDAVFUPUQURUSVCUTVAVB $.

  $( TODO: Work out conversions and demos. E.G.,

     dpval.1 $e |- A e. NN0 $.
     dpval.2 $e |- B e. QQ $.
     dpval $p |- ( A . B ) = _ A B $.

     dpcl $p |- ( A . B ) e. QQ $.

     dpfracp1.1 $e |- ( ; A B . C ) = ( D / E ) $.
     dpfracp1 $p |- ( A . _ B C ) = ( D / ; E 0 ) $.
  $)

  ${
    dpval2.a $e |- A e. NN0 $.
    dpval2.b $e |- B e. RR $.
    $( Value of the decimal point construct.  (Contributed by Thierry Arnoux,
       16-Dec-2021.) $)
    dpval2 $p |- ( A . B ) = ( A + ( B / ; 1 0 ) ) $=
      ( cdp co cdp2 c1 cc0 cdc cdiv caddc wcel cr wceq dpval mp2an df-dp2 eqtri
      cn0 ) ABEFZABGZABHIJKFLFATMBNMUAUBOCDABPQABRS $.

    $( Value of the decimal point construct.  (Contributed by Thierry Arnoux,
       16-Dec-2021.) $)
    dpval3 $p |- ( A . B ) = _ A B $=
      ( cdp co c1 cc0 cdc cdiv caddc cdp2 dpval2 df-dp2 eqtr4i ) ABEFABGHIJFKFA
      BLABCDMABNO $.

    $( Multiply by 10 a decimal expansion.  (Contributed by Thierry Arnoux,
       25-Dec-2021.) $)
    dpmul10 $p |- ( ( A . B ) x. ; 1 0 ) = ; A B $=
      ( c1 cc0 cdc cmul co cdiv caddc cdp recni 10nn nncni nnne0i divcan2i wcel
      oveq2i cr dpval2 dpcl mp2an mulcomi nn0cni divcli 3eqtr3i dfdec10 3eqtr4i
      cn0 adddii ) EFGZAHIZULBULJIZHIZKIZUMBKIABLIZULHIZABGUOBUMKBULBDMZULNOZUL
      NPZQSULUQHIULAUNKIZHIURUPUQVBULHABCDUASULUQUTUQAUJRBTRUQTRCDABUBUCMUDULAU
      NUTACUEBULUSUTVAUFUKUGABUHUI $.

    $( Divide a decimal number by 10.  (Contributed by Thierry Arnoux,
       25-Dec-2021.) $)
    decdiv10 $p |- ( ; A B / ; 1 0 ) = ( A . B ) $=
      ( cdp co c1 cc0 cdc cmul cdiv dpmul10 oveq1i cn0 wcel cr dpcl mp2an recni
      10nn nncni nnne0i divcan4i eqtr3i ) ABEFZGHIZJFZUFKFABIZUFKFUEUGUHUFKABCD
      LMUEUFUEANOBPOUEPOCDABQRSUFTUAUFTUBUCUD $.
  $}

  ${
    dp3mul10.a $e |- A e. NN0 $.
    dp3mul10.b $e |- B e. NN0 $.
    dp3mul10.c $e |- C e. RR $.
    $( Multiply by 100 a decimal expansion.  (Contributed by Thierry Arnoux,
       25-Dec-2021.) $)
    dpmul100 $p |- ( ( A . _ B C ) x. ; ; 1 0 0 ) = ; ; A B C $=
      ( cdp2 cdp co cc0 cdc cmul caddc wcel nn0cni 10nn0 oveq1i eqtri dpmul10
      cr c1 cdiv cc nn0rei dp2cl mp2an dpval2 10nn nnne0i divcli addcli eqeltri
      recni mulassi dfdec100 mul32i dec0u dpval3 eqtr3i oveq12i dfdec10 adddiri
      mulcli eqtr2i 3eqtr2ri oveq2i 3eqtr3ri ) ABCGZHIZUAJKZLIZVJLIZVIVJVJLIZLI
      ABKCKZVIVJJKZLIVIVJVJVIAVHVJUBIZMIUCAVHDBTNCTNVHTNBEUDFBCUEUFZUGAVPADOZVH
      VJVHVQUMZVJPOZVJUHUIUJUKULVTVTUNVNVOALIZBCKZMIVJALIZVJLIZVHVJLIZMIZVLABCD
      EFUOWDWAWEWBMWDVMALIWAVJAVJVTVRVTUPVMVOALVJPUQZQRBCHIZVJLIWEWBWHVHVJLBCEF
      URQBCEFSUSUTVLWCVHMIZVJLIWFVKWIVJLVKAVHKWIAVHDVQSAVHVARQWCVHVJVJAVTVRVCVS
      VTVBVDVEVMVOVILWGVFVG $.

    $( Multiply by 10 a decimal expansion with 3 digits.  (Contributed by
       Thierry Arnoux, 25-Dec-2021.) $)
    dp3mul10 $p |- ( ( A . _ B C ) x. ; 1 0 ) = ( ; A B . C ) $=
      ( cdp2 cdp co c1 cc0 cdc cmul caddc cr wcel nn0rei dfdec10 10nn recni
      dp2cl mp2an dpmul10 cdiv nncni nn0cni mulcli nnne0i divcli addassi oveq1i
      df-dp2 oveq2i 3eqtr4ri deccl dpval2 eqtr4i 3eqtri ) ABCGZHIJKLZMIAUSLUTAM
      IZUSNIZABLZCHIZAUSDBOPCOPUSOPBEQZFBCUAUBUCAUSRVBVCCUTUDIZNIZVDVABNIZVFNIV
      ABVFNIZNIVGVBVABVFUTAUTSUEZADUFUGBVETCUTCFTVJUTSUHUIUJVCVHVFNABRUKUSVIVAN
      BCULUMUNVCCABDEUOFUPUQUR $.
  $}

  ${
    dpmul1000.a $e |- A e. NN0 $.
    dpmul1000.b $e |- B e. NN0 $.
    dpmul1000.c $e |- C e. NN0 $.
    dpmul1000.d $e |- D e. RR $.
    $( Multiply by 1000 a decimal expansion.  (Contributed by Thierry Arnoux,
       25-Dec-2021.) $)
    dpmul1000 $p |- ( ( A . _ B _ C D ) x. ; ; ; 1 0 0 0 ) = ; ; ; A B C D $=
      ( cdc cc0 cmul co wcel cr mp2an 10nn0 nn0cni oveq1i caddc eqtr3i cdp2 cdp
      c1 cn0 nn0rei dp2cl dpcl recni 0nn0 deccl mulassi dpmul100 dec0u mulcomli
      oveq2i 3eqtr3i dfdec10 mulcli adddiri dfdec100 dpmul10 wceq dpval oveq12i
      mul32i eqtr2i 3eqtri ) ABIZCDUAZIZUCJIZKLZABVIUAZUBLZVKJIZJIZKLZVHCIDIZVN
      VOKLZVKKLVNVOVKKLZKLVLVQVNVOVKVNAUDMVMNMZVNNMEBNMVINMZWABFUECNMDNMZWBCGUE
      HCDUFOZBVIUFOAVMUGOUHVOVKJPUIUJZQZVKPQZUKVSVJVKKABVIEFWDULRVTVPVNKVKVOVPW
      GWFVOWEUMUNUOUPVLVKVHKLZVISLZVKKLWHVKKLZVIVKKLZSLZVRVJWIVKKVHVIUQRWHVIVKV
      KVHWGVHABEFUJZQZURVIWDUHWGUSVRVOVHKLZCDIZSLWLVHCDWMGHUTWOWJWPWKSVKVKKLZVH
      KLWOWJWQVOVHKVKPUMRVKVKVHWGWGWNVETCDUBLZVKKLWPWKCDGHVAWRVIVKKCUDMWCWRVIVB
      GHCDVCORTVDVFVGT $.
  $}

  ${
    dpval3rp.a $e |- A e. NN0 $.
    dpval3rp.b $e |- B e. RR+ $.
    $( Value of the decimal point construct.  (Contributed by Thierry Arnoux,
       16-Dec-2021.) $)
    dpval3rp $p |- ( A . B ) = _ A B $=
      ( crp wcel cr rpre ax-mp dpval3 ) ABCBEFBGFDBHIJ $.
  $}

  ${
    dp0u.1 $e |- A e. NN0 $.
    $( Add a zero in the tenths place.  (Contributed by Thierry Arnoux,
       16-Dec-2021.) $)
    dp0u $p |- ( A . 0 ) = A $=
      ( cc0 cdp co cdp2 0re dpval3 dp20u eqtri ) ACDEACFAACBGHABIJ $.
  $}

  ${
    dp0h.1 $e |- A e. RR+ $.
    $( Remove a zero in the units places.  (Contributed by Thierry Arnoux,
       16-Dec-2021.) $)
    dp0h $p |- ( 0 . A ) = ( A / ; 1 0 ) $=
      ( cc0 cdp co cdp2 c1 cdc cdiv 0nn0 dpval3rp dp20h eqtri ) CADECAFAGCHIECA
      JBKABLM $.
  $}

  ${
    rpdpcl.a $e |- A e. NN0 $.
    rpdpcl.b $e |- B e. RR+ $.
    $( Closure of the decimal point in the positive real numbers.  (Contributed
       by Thierry Arnoux, 16-Dec-2021.) $)
    rpdpcl $p |- ( A . B ) e. RR+ $=
      ( cdp co cdp2 crp dpval3rp rpdp2cl eqeltri ) ABEFABGHABCDIABCDJK $.
  $}

  ${
    dplt.a $e |- A e. NN0 $.
    dplt.b $e |- B e. RR+ $.
    dplt.d $e |- C e. RR+ $.
    dplt.1 $e |- B < C $.
    $( Comparing two decimal expansions (equal higher places).  (Contributed by
       Thierry Arnoux, 16-Dec-2021.) $)
    dplt $p |- ( A . B ) < ( A . C ) $=
      ( cdp2 cdp co clt dp2lt dpval3rp 3brtr4i ) ABHACHABIJACIJKABCDEFGLABDEMAC
      DFMN $.
  $}

  ${
    dplti.a $e |- A e. NN0 $.
    dplti.b $e |- B e. RR+ $.
    dplti.c $e |- C e. NN0 $.
    dplti.1 $e |- B < ; 1 0 $.
    dplti.2 $e |- ( A + 1 ) = C $.
    $( Comparing a decimal expansions with the next higher integer.
       (Contributed by Thierry Arnoux, 16-Dec-2021.) $)
    dplti $p |- ( A . B ) < C $=
      ( co c1 caddc clt cc0 crp wcel cr wbr 10re 10pos mpbir cdp cdc cdiv ax-mp
      rpre dpval2 wb pm3.2i elrp divlt1lt mp2an 0re gtneii redivcli 1re nn0ssre
      wa cn0 sselii ltadd2i mpbi eqbrtri breqtri ) ABUAIZAJKIZCLVDABJMUBZUCIZKI
      ZVELABDBNOBPOZEBUEUDZUFVGJLQZVHVELQVKBVFLQZGVIVFNOZVKVLUGVJVMVFPOZMVFLQZU
      QVNVORSUHVFUITBVFUJUKTVGJABVFVJRMVFULSUMUNUOURPAUPDUSUTVAVBHVC $.
  $}

  ${
    dpgti.a $e |- A e. NN0 $.
    dpgti.b $e |- B e. RR+ $.
    $( Comparing a decimal expansions with the next lower integer.
       (Contributed by Thierry Arnoux, 16-Dec-2021.) $)
    dpgti $p |- A < ( A . B ) $=
      ( c1 cc0 cdc cdiv co caddc cdp clt cr wcel crp wbr nn0rei wa 10re mp2an
      10pos pm3.2i elrp mpbir rpdivcl ltaddrp rpre ax-mp dpval2 breqtrri ) AABE
      FGZHIZJIZABKILAMNULONZAUMLPACQBONZUKONZUNDUPUKMNZFUKLPZRUQURSUAUBUKUCUDBU
      KUETAULUFTABCUOBMNDBUGUHUIUJ $.
  $}

  ${
    dpltc.a $e |- A e. NN0 $.
    dpltc.b $e |- B e. RR+ $.
    dpltc.c $e |- C e. NN0 $.
    dpltc.d $e |- D e. RR+ $.
    dpltc.1 $e |- A < C $.
    dpltc.2 $e |- B < ; 1 0 $.
    $( Comparing two decimal integers (unequal higher places).  (Contributed by
       Thierry Arnoux, 16-Dec-2021.) $)
    dpltc $p |- ( A . B ) < ( C . D ) $=
      ( cdp2 cdp co clt dp2ltc dpval3rp 3brtr4i ) ABKCDKABLMCDLMNABCDEFGHJIOABE
      FPCDGHPQ $.
  $}

  ${
    dpexpp1.a $e |- A e. NN0 $.
    dpexpp1.b $e |- B e. RR+ $.
    dpexpp1.1 $e |- ( P + 1 ) = Q $.
    dpexpp1.p $e |- P e. ZZ $.
    dpexpp1.q $e |- Q e. ZZ $.
    $( Add one zero to the mantisse, and a one to the exponent in a scientific
       notation.  (Contributed by Thierry Arnoux, 16-Dec-2021.) $)
    dpexpp1 $p |- ( ( A . B ) x. ( ; 1 0 ^ P ) )
      = ( ( 0 . _ A B ) x. ( ; 1 0 ^ Q ) ) $=
      ( cdp2 cc0 cexp co cmul wceq crp wcel ax-mp cc oveq1i c1 cdc cdiv cdp wne
      0re 10pos gtneii cr rpdp2cl rpre recni cz clt wa 10re pm3.2i elrp rpexpcl
      mpbir mp2an rpcn mulcli 10nn0 nn0cni divcan1zi div23 mp3an eqtr3i mulassi
      wbr divcli caddc expp1z oveq2i 3eqtri dpval3rp 0nn0 dp20h eqtri 3eqtr4i )
      ABJZUAKUBZCLMZNMZWBWCUCMZWCDLMZNMZABUDMZWDNMKWBUDMZWGNMWEWFWDNMZWCNMZWFWD
      WCNMZNMWHWEWCUCMZWCNMZWEWLWCKUEZWOWEOKWCUFUGUHZWEWCWBWDWBWBPQWBUIQABEFUJZ
      WBUKRULZWDPQZWDSQZWCPQZCUMQZWTXBWCUIQZKWCUNVKZUOXDXEUPUGUQWCURUTHWCCUSVAW
      DVBRZVCWCVDVEZVFRWNWKWCNWBSQXAWCSQZWPUOWNWKOWSXFXHWPXGWQUQWBWDWCVGVHTVIWF
      WDWCWBWCWSXGWQVLXFXGVJWMWGWFNWCCUAVMMZLMZWMWGXHWPXCXJWMOXGWQHWCCVNVHXIDWC
      LGVOVIVOVPWIWBWDNABEFVQTWJWFWGNWJKWBJWFKWBVRWRVQWBWRVSVTTWA $.
  $}

  ${
    0dp2dp.a $e |- A e. NN0 $.
    0dp2dp.b $e |- B e. RR+ $.
    $( Multiply by 10 a decimal expansion which starts with a zero.
       (Contributed by Thierry Arnoux, 16-Dec-2021.) $)
    0dp2dp $p |- ( ( 0 . _ A B ) x. ; 1 0 ) = ( A . B ) $=
      ( cc0 cdp2 cdp co c1 cdc cmul cexp 0p1e1 0z 1z cc wcel wceq ax-mp oveq2i
      dpexpp1 10nn0 nn0cni exp0 exp1 3eqtr3ri crp rpdpcl rpcn mulrid eqtri ) EA
      BFGHZIEJZKHZABGHZIKHZUOUOUMELHZKHULUMILHZKHUPUNABEICDMNOUAUQIUOKUMPQZUQIR
      UMUBUCZUMUDSTURUMULKUSURUMRUTUMUESTUFUOPQZUPUORUOUGQVAABCDUHUOUISUOUJSUK
      $.
  $}

  ${
    dpadd2.a $e |- A e. NN0 $.
    dpadd2.b $e |- B e. RR+ $.
    dpadd2.c $e |- C e. NN0 $.
    dpadd2.d $e |- D e. RR+ $.
    dpadd2.e $e |- E e. NN0 $.
    dpadd2.f $e |- F e. RR+ $.
    dpadd2.g $e |- G e. NN0 $.
    dpadd2.h $e |- H e. NN0 $.
    dpadd2.i $e |- ( G + H ) = I $.
    dpadd2.1 $e |- ( ( A . B ) + ( C . D ) ) = ( E . F ) $.
    $( Addition with one decimal, no carry.  (Contributed by Thierry Arnoux,
       29-Dec-2021.) $)
    dpadd2 $p |- ( ( G . _ A B ) + ( H . _ C D ) ) = ( I . _ E F ) $=
      ( co cdp2 cdp caddc c1 cc0 cdc cdiv cr wcel nn0rei rpre ax-mp dp2cl mp2an
      crp dpval2 oveq12i nn0cni recni 10nn nncni nnne0i divcli divdiri cn0 wceq
      add4i dpval 3eqtr3i oveq1i eqtr3i nn0addcli eqeltrri eqtr4i 3eqtri ) GABU
      AZUBTZHCDUAZUBTZUCTGVPUDUEUFZUGTZUCTZHVRVTUGTZUCTZUCTGHUCTZWAWCUCTZUCTZIE
      FUAZUBTZVQWBVSWDUCGVPPAUHUIBUHUIZVPUHUIAJUJBUOUIWJKBUKULZABUMUNZUPHVRQCUH
      UIDUHUIZVRUHUICLUJDUOUIWMMDUKULZCDUMUNZUPUQGWAHWCGPURVPVTVPWLUSZVTUTVAZVT
      UTVBZVCHQURVRVTVRWOUSZWQWRVCVGWGIWHVTUGTZUCTWIWEIWFWTUCRVPVRUCTZVTUGTWFWT
      VPVRVTWPWSWQWRVDXAWHVTUGABUBTZCDUBTZUCTEFUBTZXAWHSXBVPXCVRUCAVEUIWJXBVPVF
      JWKABVHUNCVEUIWMXCVRVFLWNCDVHUNUQEVEUIFUHUIZXDWHVFNFUOUIXEOFUKULZEFVHUNVI
      VJVKUQIWHWEIVERGHPQVLVMEUHUIXEWHUHUIENUJXFEFUMUNUPVNVO $.
  $}

  ${
    dpmul.a $e |- A e. NN0 $.
    dpmul.b $e |- B e. NN0 $.
    dpmul.c $e |- C e. NN0 $.
    dpmul.d $e |- D e. NN0 $.
    dpmul.e $e |- E e. NN0 $.
    ${
      dpadd.f $e |- F e. NN0 $.
      dpadd.1 $e |- ( ; A B + ; C D ) = ; E F $.
      $( Addition with one decimal.  (Contributed by Thierry Arnoux,
         27-Dec-2021.) $)
      dpadd $p |- ( ( A . B ) + ( C . D ) ) = ( E . F ) $=
        ( cdc cdiv co caddc cdp nn0rei decdiv10 c1 cc0 deccl nn0cni 10nn nnne0i
        nncni divdiri oveq1i eqtr3i oveq12i 3eqtr3i ) ABNZUAUBNZOPZCDNZUNOPZQPZ
        EFNZUNOPZABRPZCDRPZQPEFRPUMUPQPZUNOPURUTUMUPUNUMABGHUCUDUPCDIJUCUDUNUEU
        GUNUEUFUHVCUSUNOMUIUJUOVAUQVBQABGBHSTCDIDJSTUKEFKFLSTUL $.
    $}

    dpmul.g $e |- G e. NN0 $.
    ${
      dpadd3.f $e |- F e. NN0 $.
      dpadd3.h $e |- H e. NN0 $.
      dpadd3.i $e |- I e. NN0 $.
      dpadd3.1 $e |- ( ; ; A B C + ; ; D E F ) = ; ; G H I $.
      $( Addition with two decimals.  (Contributed by Thierry Arnoux,
         27-Dec-2021.) $)
      dpadd3 $p |- ( ( A . _ B C ) + ( D . _ E F ) ) = ( G . _ H I ) $=
        ( wcel cdp2 cdp co caddc cc c1 cc0 cdc wne wa w3a cmul cn0 nn0rei dp2cl
        wceq mp2an dpcl recni addcli 10nn decnncl2 nncni nnne0i 3pm3.2i adddiri
        cr pm3.2i dpmul100 oveq12i 3eqtr4i eqtri mulcan2 biimpa ) ABCUAZUBUCZDE
        FUAZUBUCZUDUCZUETZGHIUAZUBUCZUETZUFUGUHZUGUHZUETZWEUGUIZUJZUKZVSWEULUCZ
        WBWEULUCZUPZVSWBUPZVTWCWHVPVRVPAUMTVOVGTZVPVGTJBVGTCVGTWNBKUNCLUNZBCUOU
        QAVOURUQUSZVRDUMTVQVGTZVRVGTMEVGTFVGTWQENUNFPUNZEFUOUQDVQURUQUSZUTWBGUM
        TWAVGTZWBVGTOHVGTIVGTWTHQUNIRUNZHIUOUQGWAURUQUSWFWGWEWDVAVBZVCZWEXBVDVH
        VEWJVPWEULUCZVRWEULUCZUDUCZWKVPVRWEWPWSXCVFABUHCUHZDEUHFUHZUDUCGHUHIUHX
        FWKSXDXGXEXHUDABCJKWOVIDEFMNWRVIVJGHIOQXAVIVKVLWIWLWMVSWBWEVMVNUQ $.
    $}

    dpmul.j $e |- J e. NN0 $.
    dpmul.k $e |- K e. NN0 $.
    ${
      dpmul.1 $e |- ( A x. C ) = F $.
      dpmul.2 $e |- ( A x. D ) = M $.
      dpmul.3 $e |- ( B x. C ) = L $.
      dpmul.4 $e |- ( B x. D ) = ; E K $.
      dpmul.5 $e |- ( ( L + M ) + E ) = ; G J $.
      dpmul.6 $e |- ( F + G ) = I $.
      $( Multiplication with one decimal point.  (Contributed by Thierry
         Arnoux, 26-Dec-2021.) $)
      dpmul $p |- ( ( A . B ) x. ( C . D ) ) = ( I . _ J K ) $=
        ( cdp co cmul cc0 cdc cdp2 wceq caddc deccl eqid cn0 nn0mulcli eqeltrri
        c1 nn0addcli decmul1 oveq1i dfdec10 10nn0 nn0cni mulcli 3eqtr3ri oveq2i
        addassi adddii eqtr3i 3eqtr2ri 3eqtr2i 3eqtri decmul1c decmul2c wcel cr
        nn0rei mp2an recni mul4i dec0u dpmul10 oveq12i 3eqtr3i dpmul100 3eqtr4i
        dpcl cc wne wa wb dp2cl 10nn decnncl2 nncni nnne0i pm3.2i mulcan2 mp3an
        mpbi ) ABUGUHZCDUGUHZUIUHZUTUJUKZUJUKZUIUHZHIJULZUGUHZXHUIUHZUMZXFXKUMZ
        ABUKZCDUKZUIUHZHIUKZJUKXIXLCDXRJXOLEUNUHZXPABMNUOOPXPUPTLEADUIUHZLUQUBA
        DMPURUSZQVAZXOCUIUHZXSUNUHFKUKZXSUNUHXGFUIUHZKUNUHZXSUNUHZXRYCYDXSUNABF
        KCXOOMNXOUPZUAUCVBVCYDYFXSUNFKVDVCYGYEKXSUNUHZUNUHYEXGGUIUHZIUNUHZUNUHZ
        XRYEKXSXGFXGVEVFZFACUIUHFUQUAACMOURUSZVFZVGZKBCUIUHKUQUCBCNOURUSVFZXSYB
        VFVJYKYIYEUNKLUNUHEUNUHGIUKYIYKUEKLEYQLYAVFEQVFVJGIVDVHVIXRXGHUIUHZIUNU
        HYEYJUNUHZIUNUHYLHIVDYSYRIUNXGFGUNUHZUIUHYSYRXGFGYMYOGRVFZVKYTHXGUIUFVI
        VLVCYEYJIYPXGGYMUUAVGISVFVJVMVNVOABXSJDEXOPMNYHTQXTLEUNUBVCUDVPVQXFXGXG
        UIUHZUIUHXDXGUIUHZXEXGUIUHZUIUHXIXQXDXEXGXGXDAUQVRBVSVRXDVSVRMBNVTZABWJ
        WAWBZXECUQVRDVSVRXEVSVRODPVTZCDWJWAWBZYMYMWCUUBXHXFUIXGVEWDVIUUCXOUUDXP
        UIABMUUEWECDOUUGWEWFWGHIJYTHUQUFFGYNRVAUSZSJTVTZWHWIXFWKVRXKWKVRXHWKVRZ
        XHUJWLZWMXMXNWNXDXEUUFUUHVGXKHUQVRXJVSVRZXKVSVRUUIIVSVRJVSVRUUMISVTUUJI
        JWOWAHXJWJWAWBUUKUULXHXGWPWQZWRXHUUNWSWTXFXKXHXAXBXC $.
    $}

    dpmul4.f $e |- F e. NN0 $.
    dpmul4.h $e |- H e. NN0 $.
    dpmul4.i $e |- I e. NN0 $.
    dpmul4.l $e |- L e. NN0 $.
    dpmul4.m $e |- M e. NN0 $.
    dpmul4.n $e |- N e. NN0 $.
    dpmul4.o $e |- O e. NN0 $.
    dpmul4.p $e |- P e. NN0 $.
    dpmul4.q $e |- Q e. NN0 $.
    dpmul4.r $e |- R e. NN0 $.
    dpmul4.s $e |- S e. NN0 $.
    dpmul4.t $e |- T e. NN0 $.
    dpmul4.u $e |- U e. NN0 $.
    dpmul4.w $e |- W e. NN0 $.
    dpmul4.x $e |- X e. NN0 $.
    dpmul4.y $e |- Y e. NN0 $.
    dpmul4.z $e |- Z e. NN0 $.
    dpmul4.a $e |- U < ; 1 0 $.
    dpmul4.b $e |- P < ; 1 0 $.
    dpmul4.c $e |- Q < ; 1 0 $.
    dpmul4.1 $e |- ( ; ; L M N + O ) = ; ; ; R S T U $.
    dpmul4.2 $e |- ( ( A . B ) x. ( E . F ) ) = ( I . _ J K ) $.
    dpmul4.3 $e |- ( ( C . D ) x. ( G . H ) ) = ( O . _ P Q ) $.
    dpmul4.4 $e |- ( ; ; ; I J K 1 + ; ; R S T ) = ; ; ; W X Y Z $.
    dpmul4.5 $e |- ( ( ( A . B ) + ( C . D ) ) x. ( ( E . F ) + ( G . H ) ) )
      = ( ( ( I . _ J K ) + ( L . _ M N ) ) + ( O . _ P Q ) ) $.
    $( An upper bound to multiplication of decimal numbers with 4 digits.
       (Contributed by Thierry Arnoux, 25-Dec-2021.) $)
    dpmul4 $p |-
             ( ( A . _ B _ C D ) x. ( E . _ F _ G H ) ) < ( W . _ X _ Y Z ) $=
      ( cdp2 cdp co cdc cmul c1 cc0 cdiv clt wbr caddc cmin c2 deccl cn0 nn0rei
      wcel cr dpcl mp2an recni 10nn mul4i mulcli oveq1i dp3mul10 eqtri 3eqtr2ri
      mulassi dpmul10 oveq12i 3eqtr3ri adddiri eqtr2i addcli 3eqtri 10nn0 dec0u
      oveq2i cc eqeltrri dp2cl 0nn0 nn0cni dpmul100 sq10 eqtr4i dfdec100 ax-1cn
      mulcomi addcomi eqtr3i eqid addassi 3eqtr4i subcli remulcli readdcli mpbi
      mp3an dpmul1000 divcan4i cexp 2nn0 nncni sqvali decsuc mvlladdi karatsuba
      addlidi 1nn0 subdiri 3eqtrri wceq subsub 3eqtr4ri crp 1re resubcli adddii
      sqcli 3decltc ltadd2i dfdec10 mullidi 3brtr4i eqbrtri posdifi mpbir2an wa
      ltsubrp wb decnncl2 nngt0i pm3.2i ltdiv1 gt0ne0ii div23i 3brtr3i divassi
      elrp ) ABCDVSZVSZVTWAZKLWBZMWBZNWBZWCWAZWDWEWBZWEWBZWEWBZWFWAZUBUCWBZUDWB
      ZUEWBZUWIWFWAZUWBKLMNVSZVSZVTWAZWCWAZUBUCUDUEVSZVSZVTWAZWGUWFUWMWGWHZUWJU
      WNWGWHZABWBZCWBZDWBZUWEWCWAZUWIWFWAZUWMUWIWCWAZUWIWFWAZUWFUWMWGUXGUXIWGWH
      ZUXHUXJWGWHZUXGUXIGHWBZIWBZWDWIWAZUWIWCWAZUWHRSWBZTWBZWCWAZUWHUAWCWAZEFWB
      ZWIWAZWIWAZWJWAZWJWAZUXIWGUXGUWMUXOWJWAZUWGWCWAZUXRWIWAZUWGWKUUAWAZWCWAZU
      AEWBZFWBZWIWAZUYEUXDCDWBZUWCMNWBZOPWBZQWBZUXRUYLWKUYHUXFUWEUYMABUFUGWLZCD
      UHUIWLKLUJUNWLZMNUKUOWLUXQTRSUQURWLUSWLZUUBUYPQVTWAZUWGWCWAZABVTWAZUWGWCW
      AZKLVTWAZUWGWCWAZWCWAZUYQUXDUWCWCWAVUGVUCVUEWCWAZUWGUWGWCWAZWCWAVUHUWGWCW
      AZUWGWCWAVUBVUCUWGVUEUWGVUCAWMWOZBWPWOZVUCWPWOUFBUGWNZABWQWRWSZUWGWTUUCZV
      UEKWMWOZLWPWOZVUEWPWOUJLUNWNZKLWQWRWSZVUOXAVUHUWGUWGVUCVUEVUNVUSXBZVUOVUO
      XGVUJVUAUWGWCVUJOPQVSVTWAZUWGWCWAVUAVUHVVAUWGWCVOXCOPQUPULQUMWNZXDXEXCXFU
      YPQOPUPULWLZVVBXHVUDUXDVUFUWCWCABUFVUMXHZKLUJVURXHZXIXJUYKFVTWAZUWGWCWAZC
      DVTWAZUWGWCWAZMNVTWAZUWGWCWAZWCWAZUYLUYNUYOWCWAVVLVVHVVJWCWAZVUIWCWAVVMUW
      GWCWAZUWGWCWAVVGVVHUWGVVJUWGVVHCWMWODWPWOZVVHWPWOUHDUIWNZCDWQWRWSZVUOVVJM
      WMWONWPWOZVVJWPWOUKNUOWNZMNWQWRWSZVUOXAVVMUWGUWGVVHVVJVVQVVTXBZVUOVUOXGVV
      NVVFUWGWCVVNUAEFVSVTWAZUWGWCWAVVFVVMVWBUWGWCVPXCUAEFUTVAFVBWNZXDXEXCXFUYK
      FUAEUTVAWLZVWCXHVVIUYNVVKUYOWCCDUHVVPXHZMNUKVVSXHZXIXJUXDUYNWIWAZUWCUYOWI
      WAZWCWAZVVARSTVSZVTWAZWIWAZVWBWIWAZVUIWCWAZVWMUWHWCWAZUYQUXRWIWAZUYLWIWAZ
      VWIVUCVVHWIWAZUWGWCWAZVUEVVJWIWAZUWGWCWAZWCWAVWRVWTWCWAZVUIWCWAVWNVWGVWSV
      WHVXAWCVWSVUDVVIWIWAVWGVUCVVHUWGVUNVVQVUOXKVUDUXDVVIUYNWIVVDVWEXIXLVXAVUF
      VVKWIWAVWHVUEVVJUWGVUSVVTVUOXKVUFUWCVVKUYOWIVVEVWFXIXLXIVWRUWGVWTUWGVUCVV
      HVUNVVQXMVUOVUEVVJVUSVVTXMVUOXAVXBVWMVUIWCVRXCXNVUIUWHVWMWCUWGXOXPXQVWOVW
      LUWHWCWAZVWBUWHWCWAZWIWAVVAUWHWCWAZVWKUWHWCWAZWIWAZVXDWIWAVWQVWLVWBUWHVVA
      VWKVUHVVAXRVOVUTXSZVWKRWMWOVWJWPWOZVWKWPWOUQSWPWOTWPWOVXISURWNTUSWNZSTXTW
      RRVWJWQWRWSZXMVVMVWBXRVPVWAXSUWHUWGWEXOYAWLZYBZXKVXCVXGVXDWIVVAVWKUWHVXHV
      XKVXMXKXCVXGVWPVXDUYLWIVXEUYQVXFUXRWIOPQUPULVVBYCRSTUQURVXJYCXIUAEFUTVAVW
      CYCXIXNXNUXDUYIWCWAZUYNWIWAUWHUXDWCWAZUYNWIWAUXFVXNVXOUYNWIVXNUXDUWHWCWAV
      XOUYIUWHUXDWCYDXQUWHUXDVXMUXDUYRYBYHYEXCUXDCDUYRUHVVPYFYEUWCUYIWCWAZUYOWI
      WAUWHUWCWCWAZUYOWIWAUWEVXPVXQUYOWIVXPUWCUWHWCWAVXQUYIUWHUWCWCYDXQUWHUWCVX
      MUWCUYSYBYHYEXCUWCMNUYSUKVVSYFYEUYQUYIWCWAZUYGUXRWIVXRUYQUWGWCWAZUWGWCWAZ
      UYGVXRUYQVUIWCWAVXTUYIVUIUYQWCUWGVUOUUDXQUYQUWGUWGUYQUYPQVVCUMWLZYBZVUOVU
      OXGYEVXSUYFUWGWCUXOVXSUWMUXNWDUXNUXMIGHVCVDWLVEWLZYBZYGXMZUYQUWGVYBVUOXBZ
      UXOVXSWIWAZUYQWDWBZUXNWIWAZUWMUXNWDVXSWIWAZWIWAUXNVYHWIWAVYGVYIVYJVYHUXNW
      IVYJVXSWDWIWAUYQWEWBZWDWIWAVYHWDVXSYGVYFYIVXSVYKWDWIUWGUYQWCWAVXSVYKUWGUY
      QVUOVYBYHUYQVYAXPYJXCUYQWEWDVYKVYAYAWDYGUUHVYKYKUUEXNXQUXNWDVXSVYDYGVYFYL
      VYHUXNVYHUYQWDVYAUUIWLYBVYDYIYMVQXEUUFXCXEZXCUYMYKUUGUXIUXPWJWAZUXSWIWAZU
      YBWIWAVYMUYCWIWAZUYMUYEVYMUXSUYBUXIUXPUWMUWIUWMUWLUEUWKUDUBUCVGVHWLVIWLVJ
      WLZYBZUWIUWHWEVXLYAWLZYBZXBZUXOUWIVYEVYSXBZYNUWHUXRVXMUXRUYTYBZXBZUYLUYBX
      RUAEFUTVAVWCYFZUYLUYKFVWDVBWLYBXSZYLUYJVYNUYLUYBWIUYHUWHWCWAUYGUWHWCWAZUX
      RUWHWCWAZWIWAUYJVYNUYGUXRUWHVXRUYGXRVYLUYQUYIVYBUWGVUOUUSXBXSWUBVXMXKUYIU
      WHUYHWCYDXQVYMWUFUXSWUGWIWUFUYFUWGUWHWCWAZWCWAUYFUWIWCWAVYMUYFUWGUWHUWMUX
      OVYQVYEYNVUOVXMXGWUHUWIUYFWCUWHVXLXPZXQUWMUXOUWIVYQVYEVYSUUJUUKUWHUXRVXMW
      UBYHXIYMWUDXIUXIXRWOUXPXRWOUYCXRWOUYEVYOUULVYTWUAUXSUYBWUCWUEXMUXIUXPUYCU
      UMYRUUNYEUXIWPWOZUYDUUOWOZUYEUXIWGWHUWMUWIUWMVYPWNZUWIVYRWNZYOZWUKUYDWPWO
      WEUYDWGWHZUXPUYCUXOUWIUXNWDUXNVYCWNZUUPYPWUMYOZUXSUYBUWHUXRUWHVXLWNZUXRUY
      TWNYOUXTUYAUWHUAWURUAUTWNZYOZUYAEFVAVBWLWNZYPYPZUUQUYCUXPWGWHWUOUYCUWHUXN
      JWBZWCWAZUYAWIWAZUXPWGUXSUXTWIWAZUYAWIWAUYCWVEUXSUXTUYAWUCUXTWUTWSUYAWVAW
      SZYLWVFWVDUYAWIUWHUXRUAWIWAZWCWAWVFWVDUWHUXRUAVXMWUBUAWUSWSUURWVHWVCUWHWC
      VNXQYJXCYJUXNUWIWCWAZJEWBZFWBZWIWAZWVIUWIWIWAZWVEUXPWGWVKUWIWGWHWVLWVMWGW
      HJUWGEWEFWEVFXOVAYAVBYAVKVLVMUUTWVKUWIWVIWVKWVJFJEVFVAWLVBWLWNWUMUXNUWIWU
      PWUMYOUVAYQWVIUWHJWCWAZWIWAZUYAWIWAWVIWVNUYAWIWAZWIWAWVEWVLWVIWVNUYAUXNUW
      IVYDVYSXBUWHJVXMJVFYBZXBWVGYLWVDWVOUYAWIWVDUWHUWGUXNWCWAZJWIWAZWCWAUWHWVR
      WCWAZWVNWIWAWVOWVCWVSUWHWCUXNJUVBXQUWHWVRJVXMUWGUXNVUOVYDXBWVQUURWVTWVIWV
      NWIWVIUWIUXNWCWAUWHUWGWCWAZUXNWCWAWVTUXNUWIVYDVYSYHWWAUWIUXNWCWUHWWAUWIUW
      GUWHVUOVXMYHWUIYJXCUWHUWGUXNVXMVUOVYDXGXFXCXNXCWVKWVPWVIWIJEFVFVAVWCYFXQY
      MUXPWVIWDUWIWCWAZWIWAWVMUXNWDUWIVYDYGVYSXKWWBUWIWVIWIUWIVYSUVCXQXEUVDUVEU
      YCUXPWVBWUQUVFYQUYDUVSUVGUXIUYDUVIWRUVEUXGWPWOWUJUWIWPWOZWEUWIWGWHZUVHZUX
      KUXLUVJUXFUWEUXFUXEDUXDCUYRUHWLUIWLZWNUWEUWDNUWCMUYSUKWLUOWLZWNZYOWUNWWCW
      WDWUMUWIUWHUWGWTUVKUVKUVLZUVMZUXGUXIUWIUVNYRYQUXHUXFUWIWFWAZUWEWCWAUWFUXF
      UWEUWIUXFWWFYBUWEWWGYBZVYSUWIWUMWWIUVOZUVPWWKUWBUWEWCUWBUWIWCWAZUWIWFWAWW
      KUWBWWNUXFUWIWFABCDUFUGUHVVPYSXCUWBUWIUWBVUKUWAWPWOZUWBWPWOUFVULUVTWPWOZW
      WOVUMCWPWOVVOWWPCUHWNVVPCDXTWRBUVTXTWRAUWAWQWRZWSZVYSWWMYTYJXCXEUWMUWIVYQ
      VYSWWMYTUVQUWFWPWOUWMWPWOWWEUXBUXCUVJUWBUWEWWQWWHYOWULWWJUWFUWMUWIUVNYRYQ
      UWJUWBUWEUWIWFWAZWCWAUWRUWBUWEUWIWWRWWLVYSWWMUVRWWSUWQUWBWCUWQUWIWCWAZUWI
      WFWAWWSUWQWWTUWEUWIWFKLMNUJUNUKVVSYSXCUWQUWIUWQVUPUWPWPWOZUWQWPWOUJVUQUWO
      WPWOZWXAVURMWPWOVVRWXBMUKWNVVSMNXTWRLUWOXTWRKUWPWQWRWSVYSWWMYTYJXQXEUXAUW
      IWCWAZUWIWFWAUWNUXAWXCUWMUWIWFUBUCUDUEVGVHVIUEVJWNZYSXCUXAUWIUXAUBWMWOUWT
      WPWOZUXAWPWOVGUCWPWOUWSWPWOZWXEUCVHWNUDWPWOUEWPWOWXFUDVIWNWXDUDUEXTWRUCUW
      SXTWRUBUWTWQWRWSVYSWWMYTYJUVQ $.
  $}

  $( Example theorem demonstrating decimal expansions.  (Contributed by Thierry
     Arnoux, 27-Dec-2021.) $)
  threehalves $p |- ( 3 / 2 ) = ( 1 . 5 ) $=
    ( c3 c2 co cc wcel c1 c5 cdp cc0 cmul wceq 3re 2ne0 recni 1nn0 mp2an 2cnne0
    cr caddc 5nn0 cdiv wne w3a 2re redivcli cn0 5re dpcl 3pm3.2i 3nn0 0nn0 eqid
    cdc df-2 oveq1i 2p1e3 eqtr3i 5p5e10 decaddc dpadd dp0u eqtri times2i simpli
    wa divcan1i 3eqtr4ri mulcan2 biimpa ) ABUACZDEZFGHCZDEZBDEZBIUBZVEZUCZVJBJC
    ZVLBJCZKZVJVLKZVKVMVPVJABLUDMUENVLFUFEGREVLREOUGFGUHPNZQUIVLVLSCZAVSVRWCAIH
    CAFGFGAIOTOTUJUKFGFGAIFGUMZWDOTOTWDULZWEBFSCFFSCZFSCABWFFSUNUOUPUQUKURUSUTA
    UJVAVBVLWBVCABALNVNVOQVDMVFVGVQVTWAVJVLBVHVIP $.

  $( Example theorem demonstrating decimal expansions.  (Contributed by Thierry
     Arnoux, 27-Dec-2021.) $)
  1mhdrd $p |- ( ( 0 . _ 9 9 ) + ( 0 . _ 0 1 ) ) = 1 $=
    ( cc0 c9 cdp2 cdp co c1 caddc 0nn0 9nn0 1nn0 cdc eqcomi deceq1i 9cn addridi
    dec0h oveq1i 9p1e10 eqtri decaddc dpadd3 dp20u oveq2i dp0u 3eqtri ) ABBCDEA
    AFCDEGEFAACZDEFADEFABBAAFFAAHIIHHJJHHBBAFFAKZAABKZBKAAKZFKIIHJUHBBBUHBIPLMU
    IAFAUIAHPLMBAGEZFGEBFGEUGUJBFGBNOQRSHRTUAUFAFDAHUBUCFJUDUE $.


$[ set-mbox-ta-xdiv.mm $]


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Words over a set - misc additions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Condition for the restriction of a word to be a word itself.  (Contributed
     by Thierry Arnoux, 5-Oct-2018.) $)
  wrdres $p |- ( ( W e. Word S /\ N e. ( 0 ... ( # ` W ) ) )
    -> ( W |` ( 0 ..^ N ) ) e. Word S ) $=
    ( cword wcel cc0 chash cfv cfz co cfzo cres wss wrdf cuz elfzuz3 fzoss2 syl
    wa wf fssres syl2an iswrdi ) CADZEZBFCGHZIJEZSFBKJZACUHLZTZUIUDEUEFUFKJZACT
    UHUKMZUJUGACNUGUFBOHEULBFUFPBFUFQRUKAUHCUAUBABUIUCR $.

  ${
    $d v N $.  $d v S $.  $d v W $.
    $( Existence of a split of a word at a given index.  (Contributed by
       Thierry Arnoux, 11-Oct-2018.)  (Proof shortened by AV, 3-Nov-2022.) $)
    wrdsplex $p |- ( ( W e. Word S /\ N e. ( 0 ... ( # ` W ) ) )
      -> E. v e. Word S W = ( ( W |` ( 0 ..^ N ) ) ++ v ) ) $=
      ( cword wcel chash cfv cop csubstr co cc0 cfz cfzo cres cconcat wceq wrex
      cv cpfx swrdcl wa cuz simpr elfzuz2 eluzfz2 ccatpfx mpd3an3 pfxres oveq1d
      3syl pfxid adantr 3eqtr3rd oveq2 rspceeqv syl2an2r ) DBEZFZDCDGHZIJKZURFC
      LUTMKZFZDDLCNKOZVAPKZQDVDASZPKZQAURRBDCUTUAUSVCUBZDCTKZVAPKZDUTTKZVEDUSVC
      UTVBFZVJVKQVHVCUTLUCHFVLUSVCUDCLUTUELUTUFUKBDCUTUGUHVHVIVDVAPBDCUIUJUSVKD
      QVCBDULUMUNAVAURVGVEDVFVAVDPUOUPUQ $.
  $}

  ${
    wrdfsupp.1 $e |- ( ph -> Z e. V ) $.
    wrdfsupp.2 $e |- ( ph -> W e. Word S ) $.
    $( A word has finite support.  (Contributed by Thierry Arnoux,
       27-May-2025.) $)
    wrdfsupp $p |- ( ph -> W finSupp Z ) $=
      ( cc0 chash cfv cfzo co eqidd wrdfd cfn wcel fzofi a1i fdmfifsupp ) AHDIJ
      ZKLZBDCEABTDATMGNUAOPAHTQRFS $.
  $}

  ${
    wrdpmcl.1 $e |- J = ( 0 ..^ ( # ` W ) ) $.
    wrdpmcl.2 $e |- ( ph -> E : J -1-1-onto-> J ) $.
    wrdpmcl.3 $e |- ( ph -> W e. Word S ) $.
    $( Closure of a word with permuted symbols.  (Contributed by Thierry
       Arnoux, 27-May-2025.) $)
    wrdpmcl $p |- ( ph -> ( W o. E ) e. Word S ) $=
      ( cc0 chash cfv cfzo co ccom wf cword wcel eqidd wf1o syl wceq wb f1oeq23
      wrdfd mp2an sylib f1of fcod iswrdi ) AIEJKZLMZBECNZOULBPQAUKUKBECABUJEAUJ
      RHUDAUKUKCSZUKUKCOADDCSZUMGDUKUAZUOUNUMUBFFDUKDUKCUCUEUFUKUKCUGTUHBUJULUI
      T $.
  $}

  $( The prefix of length 1 of a length 2 word.  (Contributed by Thierry
     Arnoux, 19-Sep-2023.) $)
  pfx1s2 $p |- ( ( A e. V /\ B e. V ) -> ( <" A B "> prefix 1 ) = <" A "> )
      $=
    ( wcel wa cs2 c1 cpfx co cc0 cfv cs1 cword c0 wne wceq s2cl c2 chash cle
    wbr leidi s2len breqtrri wrdlenge2n0 mpan2 pfx1 syl2anc2 s2fv0 adantr s1eqd
    2re eqtrd ) ACDZBCDZEZABFZGHIZJUQKZLZALUPUQCMDZUQNOZURUTPABCQVARUQSKZTUAVBR
    RVCTRULUBABUCUDCUQUEUFCUQUGUHUPUSAUNUSAPUOABCUIUJUKUM $.

  $( The range of a prefix of a word is a subset of the range of that word.
     Stronger version of ~ pfxrn .  (Contributed by Thierry Arnoux,
     12-Dec-2023.) $)
  pfxrn2 $p |- ( ( W e. Word S /\ L e. ( 0 ... ( # ` W ) ) )
               -> ran ( W prefix L ) C_ ran W ) $=
    ( cword wcel cc0 chash cfv cfz co wa cpfx crn cfzo pfxres rneqd resss rnssi
    cres eqsstrdi ) CADEBFCGHIJEKZCBLJZMCFBNJZSZMCMUAUBUDACBOPUDCCUCQRT $.

  $( Express the range of a prefix of a word.  Stronger version of ~ pfxrn2 .
     (Contributed by Thierry Arnoux, 13-Dec-2023.) $)
  pfxrn3 $p |- ( ( W e. Word S /\ L e. ( 0 ... ( # ` W ) ) )
               -> ran ( W prefix L ) = ( W " ( 0 ..^ L ) ) ) $=
    ( cword wcel cc0 chash cfv cfz co wa cpfx crn cfzo cres pfxres rneqd df-ima
    cima eqtr4di ) CADEBFCGHIJEKZCBLJZMCFBNJZOZMCUCSUAUBUDACBPQCUCRT $.

  ${
    pfxf1.1 $e |- ( ph -> W e. Word S ) $.
    pfxf1.2 $e |- ( ph -> W : dom W -1-1-> S ) $.
    pfxf1.3 $e |- ( ph -> L e. ( 0 ... ( # ` W ) ) ) $.
    $( Condition for a prefix to be injective.  (Contributed by Thierry Arnoux,
       13-Dec-2023.) $)
    pfxf1 $p |- ( ph -> ( W prefix L ) : dom ( W prefix L ) -1-1-> S ) $=
      ( cpfx co cdm wf1 cc0 cfzo wss wf cfv wcel wceq syl syl2anc chash cfz cuz
      cres elfzuz3 fzoss2 3syl cword wrddm sseqtrrd wrdf fssresd f1resf1 pfxres
      syl3anc wfn pfxfn fndmd eqidd f1eq123d mpbird ) ADCHIZJZBVBKLCMIZBDVDUDZK
      ZADJZBDKVDVGNVDBVEOVFFAVDLDUAPZMIZVGACLVHUBIQZVHCUCPQVDVINGCLVHUECLVHUFUG
      ZADBUHQZVGVIREBDUISUJAVIBVDDAVLVIBDOEBDUKSVKULVGBVDBDUMUOAVCVDBBVBVEAVLVJ
      VBVEREGBDCUNTAVDVBAVLVJVBVDUPEGDCBUQTURABUSUTVA $.
  $}


  ${
    s2f1.i $e |- ( ph -> I e. D ) $.
    s2f1.j $e |- ( ph -> J e. D ) $.
    s2f1.1 $e |- ( ph -> I =/= J ) $.
    $( Conditions for a length 2 string to be a one-to-one function.
       (Contributed by Thierry Arnoux, 19-Sep-2023.) $)
    s2f1 $p |- ( ph -> <" I J "> : dom <" I J "> -1-1-> D ) $=
      ( wf1 cc0 c1 cpr wf1o cop cn0 wcel wne a1i wa wceq syl cs2 0nn0 1nn0 0ne1
      cdm wss f1oprg 3impia syl222anc s2prop syl2anc f1oeq1d mpbird f1of1 prssd
      f1ss wb f1dm f1eq2 ) ACDUAZUEZBUTHZIJKZBUTHZAVCCDKZUTHZVEBUFVDAVCVEUTLZVF
      AVGVCVEICMJDMKZLZAINOZCBOZJNOZDBOZIJPZCDPZVIVJAUBQEVLAUCQFVNAUDQGVJVKRVLV
      MRVNVORVIICJDNBNBUGUHUIAVCVEUTVHAVKVMUTVHSEFCDBUJUKULUMVCVEUTUNTACDBEFUOV
      CVEBUTUPUKZAVAVCSZVBVDUQAVDVQVPVCBUTURTVAVCBUTUSTUM $.
  $}

  ${
    $d I i j $.  $d J i j $.  $d K i j $.  $d i j ph $.
    s3f1.i $e |- ( ph -> I e. D ) $.
    s3f1.j $e |- ( ph -> J e. D ) $.
    s3f1.k $e |- ( ph -> K e. D ) $.
    s3f1.1 $e |- ( ph -> I =/= J ) $.
    s3f1.2 $e |- ( ph -> J =/= K ) $.
    s3f1.3 $e |- ( ph -> K =/= I ) $.
    $( Conditions for a length 3 string to be a one-to-one function.
       (Contributed by Thierry Arnoux, 19-Sep-2023.) $)
    s3f1 $p |- ( ph -> <" I J K "> : dom <" I J K "> -1-1-> D ) $=
      ( cfv wceq cc0 wcel wa c1 c2 simpr adantlr vi vj cs3 cdm wf cv wral chash
      wi wf1 cfzo cword s3cld wrdf syl ffdmd simplr eqtr4d simpllr fveq2d s3fv0
      co ad4antr eqtrd adantr s3fv1 3eqtr3d wne ad5antr pm2.21ddne 3eqtr3rd w3o
      s3fv2 ctp wrddm c3 s3len oveq2i fzo0to3tp eqtri eqtrdi eleq2d biimpa eltp
      vex sylib ad2antrr mpjao3dan ex anasss ralrimivva dff13 sylanbrc ) ACDEUC
      ZUDZBWNUEUAUFZWNLZUBUFZWNLZMZWPWRMZUIZUBWOUGUAWOUGWOBWNUJANWNUHLZUKVBZBWN
      AWNBULOZXDBWNUEACDEBFGHUMZBWNUNUOUPAXBUAUBWOWOAWPWOOZWRWOOZXBAXGPZXHPZWTX
      AXJWTPZWPNMZXAWPQMZWPRMZXKXLPZWRNMZXAWRQMZWRRMZXOXPPWPNWRXKXLXPUQXOXPSURX
      OXQPZXACDXSWQWSCDXJWTXLXQUSXOWQCMZXQXOWQNWNLZCXOWPNWNXKXLSUTAYACMZXGXHWTX
      LACBOYBFCDEBVAUOZVCVDZVEXKXQWSDMZXLXKXQPZWSQWNLZDYFWRQWNXKXQSUTAYGDMZXGXH
      WTXQADBOYHGCDEBVFUOZVCVDZTVGACDVHZXGXHWTXLXQIVIVJXOXRPZXAECYLWQWSCEXJWTXL
      XRUSXOXTXRYDVEXKXRWSEMZXLXKXRPZWSRWNLZEYNWRRWNXKXRSUTAYOEMZXGXHWTXRAEBOYP
      HCDEBVMUOZVCVDZTVKAECVHZXGXHWTXLXRKVIVJXJXPXQXRVLZWTXLAXHYTXGAXHPWRNQRVNZ
      OZYTAXHUUBAWOUUAWRAWOXDUUAAXEWOXDMXFBWNVOUOXDNVPUKVBUUAXCVPNUKCDEVQVRVSVT
      WAZWBWCWRNQRUBWEWDWFTZWGWHXKXMPZXPXAXQXRUUEXPPZXACDUUFWQWSDCXJWTXMXPUSUUE
      WQDMZXPUUEWQYGDUUEWPQWNXKXMSUTAYHXGXHWTXMYIVCVDZVEXKXPWSCMZXMXKXPPZWSYACU
      UJWRNWNXKXPSUTAYBXGXHWTXPYCVCVDZTVKAYKXGXHWTXMXPIVIVJUUEXQPWPQWRXKXMXQUQU
      UEXQSURUUEXRPZXADEUULWQWSDEXJWTXMXRUSUUEUUGXRUUHVEXKXRYMXMYRTVGADEVHZXGXH
      WTXMXRJVIVJXJYTWTXMUUDWGWHXKXNPZXPXAXQXRUUNXPPZXAECUUOWQWSECXJWTXNXPUSUUN
      WQEMZXPUUNWQYOEUUNWPRWNXKXNSUTAYPXGXHWTXNYQVCVDZVEXKXPUUIXNUUKTVGAYSXGXHW
      TXNXPKVIVJUUNXQPZXADEUURWQWSEDXJWTXNXQUSUUNUUPXQUUQVEXKXQYEXNYJTVKAUUMXGX
      HWTXNXQJVIVJUUNXRPWPRWRXKXNXRUQUUNXRSURXJYTWTXNUUDWGWHXIXLXMXNVLZXHWTXIWP
      UUAOZUUSAXGUUTAWOUUAWPUUCWBWCWPNQRUAWEWDWFWGWHWIWJWKUAUBWOBWNWLWM $.
  $}

  ${
    $( Closure of the words of length 3 in a preimage using the hash function.
       (Contributed by Thierry Arnoux, 27-Sep-2023.) $)
    s3clhash $p |- <" I J K "> e. ( `' # " { 3 } ) $=
      ( cs3 chash ccnv c3 csn cima wcel cvv cfv wceq cword s3cli elexi cn0 cpnf
      s3len cun wf wfn wa wb hashf ffn fniniseg mp2b mpbir2an ) ABCDZEFGHIJZUJK
      JZUJELGMZUJKNABCOPABCSKQRHTZEUAEKUBUKULUMUCUDUEKUNEUFKGUJEUGUHUI $.
  $}


  ${
    pfxlsw2ccat.n $e |- N = ( # ` W ) $.
    $( Reconstruct a word from its prefix and its last two symbols.
       (Contributed by Thierry Arnoux, 26-Sep-2023.) $)
    pfxlsw2ccat $p |- ( ( W e. Word V /\ 2 <_ N )
          -> W = ( ( W prefix ( N - 2 ) )
                            ++ <" ( W ` ( N - 2 ) ) ( W ` ( N - 1 ) ) "> ) ) $=
      ( wcel c2 cle wbr cfv c1 cmin cpfx cs1 cconcat wceq syl2anc syl cn0 cc0
      co cword wa chash cs2 clsw c0 simpl simpr breqtrdi wrdlenge2n0 pfxlswccat
      wne lsw oveq1i fveq2i eqtr4di s1eqd oveq2d eqtr3d pfxcl cn lencl eqeltrid
      nn0ge2m1nn eqeltrrid nn0red lem1d syl3anc cfz ige2m1fz pfxlen nn0ge2m1nn0
      pfxn0 oveq1d 0zd nn0zd 1zzd zsubcld a1i nn0sub biimpa syl21anc nn0ge0d cc
      2nn0 nn0cnd sub1m1 breqtrrd nnred elfzd eqeltrd pfxpfx pfxtrcfvl fvoveq1d
      eqtrd eqtr4d oveq12d ccatw2s1ccatws2 3eqtrd ) CBUAZEZFAGHZUBZCCCUCIZJKTZL
      TZAJKTZCIZMZNTZCAFKTZLTZXKCIZMZNTZXINTZXLXMXHUDNTZXCXFCUEIZMZNTZCXJXCXACU
      FULZXTCOXAXBUGZXCXAFXDGHZYAYBXCFAXDGXAXBUHZDUIZBCUJPBCUKPXCXSXIXFNXCXRXHX
      CXAXRXHOYBXAXRXECIXHCWTUMXGXECAXDJKDUNZUOUPQUQURUSXCXFXOXINXCXFXFUCIZJKTZ
      LTZXFUEIZMZNTZXFXOXCXFWTEZXFUFULZYLXFOXCXAYMYBBCXEUTQXCXAXEVAEXEXDGHYNYBX
      CXEXGVAYFXCAREZXBXGVAEXCAXDRDXCXAXDREZYBBCVBQZVCZYDAVDPVEZXCXDXCXDYQVFVGX
      EBCVMVHBXFUKPXCYIXLYKXNNXCYICYHLTZXLXCXAXESXDVITEZYHSXEVITZEYIYTOYBXCYPYC
      UUAYQYEXDVJPZXCYHXEJKTZUUBXCYGXEJKXCXAUUAYGXEOYBUUCBCXEVKPZVNXCUUDSXEXCVO
      XCXEXCXEXGRYFXCYOXBXGREYRYDAVLPVEVPZXCXEJUUFXCVQVRXCSXGJKTZUUDGXCSXKUUGGX
      CXKXCFREZYOXBXKREZUUHXCWEVSYRYDUUHYOUBXBUUIFAVTWAWBWCXCAWDEUUGXKOXCAYRWFA
      WGQZWHXGXEJKYFUNUIXCXEXCXEYSWIVGWJWKYHXEBCWLVHXCYHXKCLXCYHUUGXKXCYGXGJKXC
      YGXEXGUUEYFUPVNUUJWOURWOXCYJXMXCYJXDFKTCIZXMXCXAYCYJUUKOYBYEBCWMPXCAXDFCK
      AXDOXCDVSWNWPUQWQUSVNXCXLWTEZXPXQOXCXAUULYBBCXKUTQBXLXMXHWRQWS $.
  $}

  ${
    $d J x y $.  $d N x y $.  $d T x y $.  $d ph x y $.
    ccatws1f1o.1 $e |- N = ( # ` T ) $.
    ccatws1f1o.2 $e |- J = ( 0 ..^ ( N + 1 ) ) $.
    ccatws1f1o.3 $e |- ( ph -> T : ( 0 ..^ N ) -1-1-onto-> ( 0 ..^ N ) ) $.
    $( Conditions for the concatenation of a word and a singleton word to be
       bijective.  (Contributed by Thierry Arnoux, 27-May-2025.) $)
    ccatws1f1o $p |- ( ph -> ( T ++ <" N "> ) : J -1-1-onto-> J ) $=
      ( vx co cc0 cfv cfzo wcel wceq wa cn0 adantr a1i biimpa ad2antrr cs1 wf1o
      vy cconcat chash caddc cv cmin cif cmpt wral wreu c1 wf cword f1of iswrdi
      wss syl 3syl eqeltrid fzossfzop1 sseqtrrdi eqcomi oveq2d eleq2d ffvelcdmd
      lencl sseldd wn cc fzo0ssnn0 eqsstrdi sselda nn0cnd cuz wo nn0uz eleqtrdi
      adantlr fzosplitsni syl2anc notbid orcnd eqtrdi subeq0bd fveq2d eleqtrrdi
      s1fv eqtrd fzonn0p1 eqeltrd ifclda ralrimiva wi f1ocnv ffvelcdmda iftrued
      ccnv oveq2i simpr f1ocnvfv2 eqtr2d ad5ant14 fzonel eleq2i sylnib eqneltrd
      ad3antrrr iffalsed eqsstri simpllr sselid 3eqtrd pm2.65da olcnd f1ocnvfv1
      ad5antr eleq1 fveq2 fvoveq1 ifbieq12d eqeq2d eqreu syl3anc eqtr3d ad4antr
      ex 3eqtr4rd eqeltrrd mpjaodan oveq12i eqtr4i mpteq1i f1ompt sylanbrc ovex
      s1len cvv sylancl fex s1cli ccatfval f1oeq1d mpbird ) ACCBDUAZUDIZUBCCHJB
      UEKZUUFUEKZUFIZLIZHUGZJUUHLIZMZUULBKZUULUUHUHIZUUFKZUIZUJZUBZAUURCMZHCUKU
      CUGZUURNZHCULZUCCUKUUTAUVAHCAUULCMZOZUUNUUOUUQCAUUNUUOCMUVEAUUNOZJDLIZCUU
      OAUVHCURZUUNAUVHJDUMUFIZLIZCADPMZUVHUVKURADUUHPEAUVHUVHBUNZBUVHUOMUUHPMAU
      VHUVHBUBZUVMGUVHUVHBUPUSZUVHDBUQUVHBVHUTVAZDVBUSFVCZQUVGUVHUVHUULBAUVMUUN
      UVOQAUUNUULUVHMZAUUMUVHUULAUUHDJLUUHDNADUUHEVDZRVEVFZSVGVIVTUVFUUNVJZOZUU
      QDCUWBUUQJUUFKZDUWBUUPJUUFUWBUULUUHUVFUULVKMUWAUVFUULACPUULACUVKPCUVKNAFR
      ZUVJVLZVMVNVOQUWBUULDUUHUWBUVRUULDNZUWBDJVPKZMZUULUVKMZUVRUWFVQZAUWHUVEUW
      AADPUWGUVPVRVSZTUVFUWIUWAAUVEUWIACUVKUULUWDVFSZQUWHUWIUWJJDUULWASZWBAUWAU
      VRVJZUVEAUWAUWNAUUNUVRUVTWCSVTWDEWEWFWGAUWCDNZUVEUWAAUVLUWOUVPDPWIUSZTWJA
      DCMZUVEUWAADUVKCAUVLDUVKMUVPDWKUSFWHZTWLWMWNAUVDUCCAUVBCMZOZUVBUVHMZUVDUV
      BDNZUWTUXAOZUVBBWSZKZCMUVBUXEUUMMZUXEBKZUXEUUHUHIUUFKZUIZNZUVCUULUXENZWOZ
      HCUKUVDUXCUVHCUXEAUVIUWSUXAUVQTUWTUVHUVHUVBUXDAUVHUVHUXDUNZUWSAUVNUVHUVHU
      XDUBUXMGUVHUVHBWPUVHUVHUXDUPUTQWQZVIUXCUXIUXGUVBUXCUXFUXGUXHUXCUXEUVHUUMU
      XNDUUHJLEWTZVSWRUXCUVNUXAUXGUVBNAUVNUWSUXAGTZUWTUXAXAZUVHUVHUVBBXBWBXCUXC
      UXLHCUXCUVEOZUVCUXKUXRUVCOZUXEUUOUXDKZUULUXSUVBUUOUXDUXSUVBUURUUOUXRUVCXA
      ZUXSUUNUUOUUQUXSUULUVHUUMUXSUVRUWFAUVEUWJUWSUXAUVCUVFUWHUWIUWJAUWHUVEUWKQ
      UWLUWMWBXDUXSUWFUXAUXCUXAUVEUVCUWFUXQXIUXSUWFOZUVBDUVHUYBUVBUURUUQDUXSUVC
      UWFUYAQUYBUUNUUOUUQUYBUULDUUMUXSUWFXAZUYBDUVHMZDUUMMZUYDVJZUYBJDXEZRZUVHU
      UMDUXOXFZXGXHXJUYBUUQUWCDUYBUUPJUUFUYBUULUUHUYBUULUYBCPUULCUVKPFUWEXKUXCU
      VEUVCUWFXLXMVOUYBUULDUUHUYCEWEWFWGAUWOUWSUXAUVEUVCUWFUWPXRWJXNUYHXHXOXPZU
      XOVSWRWJWGUXSUVNUVRUXTUULNUXCUVNUVEUVCUXPTUYJUVHUVHUULBXQWBXCYHWNUVCUXJHC
      UXEUXKUURUXIUVBUXKUUNUXFUUOUUQUXGUXHUULUXEUUMXSUULUXEBXTUULUXEUUHUUFUHYAY
      BYCYDYEUWTUXBOZUWQUVBUYEDBKZDUUHUHIZUUFKZUIZNZUVCUWFWOZHCUKUVDAUWQUWSUXBU
      WRTUYKUYNDUYOUVBUYKUYNUWCDUYKUYMJUUFUYKDUUHADVKMUWSUXBADUVPVOTDUUHNUYKERW
      FWGAUWOUWSUXBUWPTWJUYKUYEUYLUYNUYKUYDUYEUYFUYKUYGRUYIXGXJUWTUXBXAYIUYKUYQ
      HCUYKUVEOZUVCUWFUYRUVCOZUVRUWFUYSUWHUWIUWJUWTUWHUXBUVEUVCAUWHUWSUWKQZXIAU
      VEUWIUWSUXBUVCUWLXDUWMWBUYSUVRUYDUYSUVROZUURDUVHUYSUURDNUVRUYSUVBUURDUYRU
      VCXAUWTUXBUVEUVCXLYFQVUAUURUUOUVHVUAUUNUUOUUQUYSUVRUUNUYSUVHUUMUULUVHUUMN
      UYSUXORVFSWRUYSUVHUVHUULBAUVMUWSUXBUVEUVCUVOYGWQWLYJUYFVUAUYGRXOWDYHWNUVC
      UYPHCDUWFUURUYOUVBUWFUUNUYEUUOUUQUYLUYNUULDUUMXSUULDBXTUULDUUHUUFUHYAYBYC
      YDYEUWTUWHUVBUVKMZUXAUXBVQZUYTAUWSVUBACUVKUVBUWDVFSUWHVUBVUCJDUVBWASWBYKW
      NHUCCCUURUUSHUUKCUURUUKUVKCUUJUVJJLUUHDUUIUMUFUVSDYRYLWTFYMYNYOYPACCUUGUU
      SABYSMZUUFYSUOZMUUGUUSNAUVMUVHYSMVUDUVOJDLYQUVHUVHYSBUUAYTDUUBHBUUFYSVUEU
      UCYTUUDUUE $.
  $}

  ${
    ccatws1f1olast.1 $e |- N = ( # ` W ) $.
    ccatws1f1olast.3 $e |- ( ph -> W e. Word S ) $.
    ccatws1f1olast.4 $e |- ( ph -> X e. S ) $.
    ccatws1f1olast.5 $e |- ( ph -> T : ( 0 ..^ N ) -1-1-onto-> ( 0 ..^ N ) ) $.
    $( Two ways to reorder symbols in a word ` W ` according to permutation
       ` T ` , and add a last symbol ` X ` .  (Contributed by Thierry Arnoux,
       27-May-2025.) $)
    ccatws1f1olast $p |- ( ph -> ( ( W ++ <" X "> ) o. ( T ++ <" N "> ) )
                                = ( ( W o. T ) ++ <" X "> ) ) $=
      ( cs1 cconcat co ccom cc0 wcel wceq syl syl2anc cfz c1 caddc cword wf wss
      cfzo cn0 chash cfv lencl eqeltrid fzossfzop1 sswrd iswrdi sseldd fzonn0p1
      wf1o f1of s1cld oveq1i ccatws1len eqtr4id ccatws1cl wrdfd ccatco cres crn
      syl3anc frnd cores cpfx oveq2d fzossfz sseqtrid eleqtrrd pfxccat1 3eqtr3d
      a1i pfxres coeq1d eqtr3d s1co ccats1val2 s1eqd eqtrd oveq12d ) AEFKZLMZCD
      KZLMNZWHCNZWHWINZLMZECNZWGLMACODUAUBMZUFMZUCZPWIWQPWPBWHUDZWJWMQAODUFMZUC
      ZWQCAWSWPUEZWTWQUEADUGPZXAADEUHUIZUGGAEBUCZPZXCUGPHBEUJRUKZDULRWSWPUMRAWS
      WSCUDZCWTPAWSWSCUQXGJWSWSCURRZWSDCUNRUOADWPAXBDWPPZXFDUPRZUSABWOWHAWOXCUA
      UBMZWHUHUIZDXCUAUBGUTZAXEXLXKQHBEFVARZVBAXEFBPZWHXDPZHIBEFVCSZVDZWPBCWIWH
      VEVHAWKWNWLWGLAWHWSVFZCNZWKWNACVGWSUEXTWKQAWSWSCXHVIWHCWSVJRAXSECAWHDVKMZ
      WHXCVKMZXSEADXCWHVKDXCQZAGVRZVLAXPDOXLTMZPYAXSQXQADOXKTMZYEAWPYFDAOWOTMWP
      YFOWOVMAWOXKOTWOXKQAXMVRVLVNXJUOAXLXKOTXNVLVOBWHDVSSAXEWGXDPYBEQHAFBIUSBE
      WGVPSVQVTWAAWLDWHUIZKZWGAXIWRWLYHQXJXRWPBDWHWBSAYGFAXEXOYCYGFQHIYDFDBEWCV
      HWDWEWFWE $.
  $}

  ${
    $d A i x $.  $d A m n x $.  $d B i j x y $.  $d B k x y $.  $d B m n x $.
    $d ch x $.  $d i ph $.  $d j ph $.  $d k n x $.  $d k ph $.  $d m n ta x $.
    $d n ph $.  $d n ps $.  $d ph y $.  $d th x $.
    wrdt2ind.1 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
    wrdt2ind.2 $e |- ( x = y -> ( ph <-> ch ) ) $.
    wrdt2ind.3 $e |- ( x = ( y ++ <" i j "> ) -> ( ph <-> th ) ) $.
    wrdt2ind.4 $e |- ( x = A -> ( ph <-> ta ) ) $.
    wrdt2ind.5 $e |- ps $.
    wrdt2ind.6 $e |- ( ( y e. Word B /\ i e. B /\ j e. B ) -> ( ch -> th ) ) $.
    $( Perform an induction over the structure of a word of even length.
       (Contributed by Thierry Arnoux, 26-Sep-2023.) $)
    wrdt2ind $p |- ( ( A e. Word B /\ 2 || ( # ` A ) ) -> ta ) $=
      ( c2 co wceq vm vn vk cword wcel chash cfv cdvds wbr wa cmul cn0 wral cc0
      cv wi c1 caddc oveq2 eqeq1d imbi1d ralbidv c0 2t0e0 eqeq1i hasheq0 bitrid
      eqcom bitri mpbiri biimtrdi rgen fveq2 imbi12d cbvralvw cmin cpfx cconcat
      eqeq2d cs2 wsbc cfz simprl 0zd lencl syl nn0zd cz 2z a1i zsubcld cr nn0re
      cle 0le2 nn0ge0 mulge0d adantr 2cnd simpl nn0cnd 1cnd adddid simprr 2t1e2
      2re oveq2d 3eqtr3d oveq1d mulcld pncand eqtrd breqtrrd zred clt ltsubposd
      nn0red 2pos mpbii ltled syl2anc adantlr sbcie mpd 0red eqbrtrd nn0p1elfzo
      biimpa syl3anc wrdsymbcl leidd sbceq1d id eqidd s2eqd imbi2d wb eqbrtrrid
      eqcomd adantl elfzd pfxlen eqtr2d vex dfsbcq bitr3id simplr pfxcl rspcdva
      ad2antrl addlidd eqeltrrd leadd1dd eqbrtrrd nn0sub syl21anc recnd subsubd
      cfzo 2nn0 2m1e1 eqtr3d lem1d nn0ge2m1nn0 npcand w3a ovex 3imtr4g vtocl3ga
      oveq1 1red simpll readdcld 0p1e1 nn0ge0d le2addd breqtrd eqid pfxlsw2ccat
      lemul2ad sbceq1a mpbird expr ralrimiva ex biimtrid nn0ind rspcdv adantllr
      imp wrex evennn02n sylan r19.29a ) HIUDZUEZRHUFUGZUHUIZUJRUAUOZUKSZUWQTZE
      UAULUWPUWSULUEZUXAEUWRUWPUXBUJZUXAEUXCUWTFUOZUFUGZTZAUPZFUWOUMZUXAEUPZUXB
      UXHUWPRUBUOZUKSZUXETZAUPZFUWOUMRUNUKSZUXETZAUPZFUWOUMRUCUOZUKSZUXETZAUPZF
      UWOUMZRUXQUQURSZUKSZUXETZAUPZFUWOUMZUXHUBUCUWSUXJUNTZUXMUXPFUWOUYGUXLUXOA
      UYGUXKUXNUXEUXJUNRUKUSUTVAVBUXJUXQTZUXMUXTFUWOUYHUXLUXSAUYHUXKUXRUXEUXJUX
      QRUKUSUTVAVBUXJUYBTZUXMUYEFUWOUYIUXLUYDAUYIUXKUYCUXEUXJUYBRUKUSUTVAVBUXJU
      WSTZUXMUXGFUWOUYJUXLUXFAUYJUXKUWTUXEUXJUWSRUKUSUTVAVBUXPFUWOUXDUWOUEZUXOU
      XDVCTZAUXOUXEUNTZUYKUYLUXOUNUXETUYMUXNUNUXEVDVEUNUXEVHVIUXDUWOVFVGUYLABPL
      VJVKVLUYAUXRGUOZUFUGZTZCUPZGUWOUMZUXQULUEZUYFUXTUYQFGUWOUXDUYNTZUXSUYPACU
      YTUXEUYOUXRUXDUYNUFVMVSMVNVOUYSUYRUYFUYSUYRUJZUYEFUWOVUAUYKUYDAVUAUYKUYDU
      JZUJZAAFUXDUXERVPSZVQSZVUDUXDUGZUXEUQVPSZUXDUGZVTZVRSZWAZVUCAFVUEWAZVUKVU
      CUXRVUEUFUGZTZVULUYSVUBVUNUYRUYSVUBUJZVUMVUDUXRVUOUYKVUDUNUXEWBSUEVUMVUDT
      UYSUYKUYDWCZVUOVUDUNUXEVUOWDVUOUXEVUOUYKUXEULUEZVUPIUXDWEWFZWGZVUOUXERVUS
      RWHUEVUOWIWJWKZVUOUNUXRVUDWNUYSUNUXRWNUIVUBUYSRUXQRWLUEZUYSXFWJUXQWMUNRWN
      UIZUYSWOWJUXQWPWQWRZVUOVUDUXRRURSZRVPSUXRVUOUXEVVDRVPVUOUYCUXRRUQUKSZURSU
      XEVVDVUORUXQUQVUOWSZVUOUXQUYSVUBWTXAZVUOXBZXCUYSUYKUYDXDVUOVVERUXRURVVERT
      VUOXEWJXGXHZXIVUOUXRRVUORUXQVVFVVGXJVVFXKXLZXMVUOVUDUXEVUOVUDVUTXNZVUOUXE
      VURXQZVUOUNRXOUIVUDUXEXOUIXRVUORUXEVVAVUOXFWJZVVLXPXSXTUUAIUXDVUDUUBYAVVJ
      UUCYBVUCUYQVUNVULUPGUWOVUEUYNVUETZUYPVUNCVULVVNUYOVUMUXRUYNVUEUFVMVSCAFUY
      NWAZVVNVULACFUYNGUUDMYCZAFUYNVUEUUEZUUFVNUYSUYRVUBUUGUYKVUEUWOUEZVUAUYDIU
      XDVUDUUHUUJZUUIYDVUCVVRVUFIUEZVUHIUEZVULVUKUPZVVSUYSVUBVVTUYRVUOUYKVUDUNU
      XEUUSSZUEZVVTVUPVUOVUDULUEZVUQVUDUQURSZUXEWNUIVWDVUORULUEZVUQRUXEWNUIZVWE
      VWGVUOUUTWJVURVUORVVDUXEWNVUOUNRURSRVVDWNVUORVVFUUKVUOUNUXRRVUOYEVUOVUDUX
      RWLVVJVVKUULVVMVVCUUMUUNVVIXMZVWGVUQUJVWHVWERUXEUUOYHUUPVURVUOVWFVUGUXEWN
      VUOUXERUQVPSZVPSVWFVUGVUOUXERUQVUOUXEVVLUUQZVVFVVHUURVUOVWJUQUXEVPVWJUQTV
      UOUVAWJXGUVBVUOUXEVVLUVCYFVUDUXEYGYIVUDIUXDYJYAYBUYSVUBVWAUYRVUOUYKVUGVWC
      UEZVWAVUPVUOVUGULUEZVUQVUGUQURSZUXEWNUIVWLVUOVUQVWHVWMVURVWIUXEUVDYAVURVU
      OVWNUXEUXEWNVUOUXEUQVWKVVHUVEVUOUXEVVLYKYFVUGUXEYGYIVUGIUXDYJYAYBVVOAFUYN
      JUOZKUOZVTZVRSZWAZUPVULAFVUEVWQVRSZWAZUPVULAFVUEVUFVWPVTZVRSZWAZUPVWBGJKV
      UEVUFVUHUWOIIVVNVVOVULVWSVXAVVQVVNAFVWRVWTUYNVUEVWQVRUVJYLVNVWOVUFTZVXAVX
      DVULVXEAFVWTVXCVXEVWQVXBVUEVRVXEVWOVWPVUFVWPVXEYMVXEVWPYNYOXGYLYPVWPVUHTZ
      VXDVUKVULVXFAFVXCVUJVXFVXBVUIVUEVRVXFVUFVWPVUFVUHVXFVUFYNVXFYMYOXGYLYPUYN
      UWOUEVWOIUEVWPIUEUVFCDVVOVWSQVVPADFVWRUYNVWQVRUVGNYCUVHUVIYIYDVUCUXDVUJTZ
      AVUKYQVUCUYKVWHVXGVUAUYKUYDWCVUCRUYCUXEWNVUCRVVEUYCWNXEVUCUQUYBRVUCUVKZVU
      CUXQUQVUCUXQUYSUYRVUBUVLZXQZVXHUVMVVAVUCXFWJVVBVUCWOWJVUCUQUNUQURSUYBWNUV
      NVUCUNUQUXQUQVUCYEVXHVXJVXHVUCUXQVXIUVOVUCUQVXHYKUVPYRUVTYRVUAUYKUYDXDUVQ
      UYKVWHUJZVUJUXDVXKUXDVUJUXEIUXDUXEUVRUVSYSYSYAAFVUJUWAWFUWBUWCUWDUWEUWFUW
      GYTUXCUXGUXIFHUWOUWPUXBWTUXDHTZUXGUXIYQUXCVXLUXFUXAAEVXLUXEUWQUWTUXDHUFVM
      VSOVNYTUWHYDUWJUWIUWPUWQULUEZUWRUXAUAULUWKZIHWEVXMUWRVXNUAUWQUWLYHUWMUWN
      $.
  $}

  ${
    $d M x $.  $d N x $.  $d V x $.  $d W x $.
    $( The range of a subword is a subset of the range of that word.  Stronger
       version of ~ swrdrn .  (Contributed by Thierry Arnoux, 12-Dec-2023.) $)
    swrdrn2 $p |- ( ( W e. Word V /\ M e. ( 0 ... N ) /\ N e. ( 0 ... ( # ` W )
       ) ) -> ran ( W substr <. M , N >. ) C_ ran W ) $=
      ( vx cword wcel cc0 cfz co cfv crn cfzo wss cuz adantr cz elfzelzd sseldd
      syl chash w3a cop csubstr cmin cv caddc cmpt swrdval2 rneqd wral wfun cdm
      wa eqidd simpl1 wrdfd ffund elfzuz3 3ad2ant3 fzoss2 elfzuz 3ad2ant2 simpr
      fzoss1 simpl3 simpl2 fzoaddel2 syl3anc wceq wrddm 3ad2ant1 fvelrn syl2anc
      eleqtrrd ralrimiva eqid rnmptss eqsstrd ) DCFGZAHBIJGZBHDUAKZIJGZUBZDABUC
      UDJZLEHBAUEJMJZEUFZAUGJZDKZUHZLZDLZWDWEWJECDABUIUJWDWIWLGZEWFUKWKWLNWDWME
      WFWDWGWFGZUNZDULWHDUMZGWMWOHWBMJZCDWOCWBDWOWBUOVTWAWCWNUPUQURWOWHWQWPWOHB
      MJZWQWHWOWBBOKGZWRWQNWDWSWNWCVTWSWABHWBUSUTPBHWBVATWOABMJZWRWHWOAHOKGZWTW
      RNWDXAWNWAVTXAWCAHBVBVCPAHBVETWOWNBQGAQGWHWTGWDWNVDWOBHWBVTWAWCWNVFRWOAHB
      VTWAWCWNVGRWGBAVHVISSWDWPWQVJZWNVTWAXBWCCDVKVLPVOWHDVMVNVPEWFWIWLWJWJVQVR
      TVS $.
  $}

  ${
    $d M i j $.  $d N i j $.  $d W i j $.  $d i j ph $.
    swrdrndisj.w $e |- ( ph -> W e. Word D ) $.
    swrdrndisj.m $e |- ( ph -> M e. ( 0 ... N ) ) $.
    swrdrndisj.n $e |- ( ph -> N e. ( 0 ... ( # ` W ) ) ) $.
    swrdrndisj.f1 $e |- ( ph -> W : dom W -1-1-> D ) $.
    swrdrndisj.1 $e |- ( ph -> O e. ( N ... P ) ) $.
    swrdrndisj.2 $e |- ( ph -> P e. ( N ... ( # ` W ) ) ) $.
    $( Condition for the range of two subwords of an injective word to be
       disjoint.  (Contributed by Thierry Arnoux, 13-Dec-2023.) $)
    swrdrndisj $p |- ( ph -> ( ran ( W substr <. M , N >. )
                                  i^i ran ( W substr <. O , P >. ) ) = (/) ) $=
      ( co c0 wcel cc0 cfz wss 3syl cop csubstr crn cin cfzo cima cword swrdrn3
      chash cfv wceq syl3anc cuz elfzuz fzss1 sseldd ineq12d cdm wf1 ccnv df-f1
      wfun simprbi imain fzoss1 elfzuz3 fzoss2 sstrd sslin syl fzodisj sseqtrdi
      wf ss0 imaeq2d ima0 eqtrdi 3eqtr2d ) AGDEUAUBNUCZGFCUAUBNUCZUDGDEUENZUFZG
      FCUENZUFZUDZGWAWCUDZUFZOAVSWBVTWDAGBUGPZDQERNPEQGUIUJZRNZPZVSWBUKHIJDEBGU
      HULAWHFQCRNZPCWJPVTWDUKHAECRNZWLFAWKEQUMUJPZWMWLSJEQWIUNZEQCUOTLUPAEWIRNZ
      WJCAWKWNWPWJSJWOEQWIUOTMUPFCBGUHULUQAGURZBGUSZGUTVBZWGWEUKKWRWQBGVMWSWQBG
      VAVCWAWCGVDTAWGGOUFOAWFOGAWFOSWFOUKAWFWAEWIUENZUDZOAWCWTSWFXASAWCECUENZWT
      AFWMPFEUMUJPWCXBSLFECUNFECVETACWPPWICUMUJPXBWTSMCEWIVFCEWIVGTVHWCWTWAVIVJ
      DEWIVKVLWFVNVJVOGVPVQVR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Splicing words (substring replacement)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    splfv3.s $e |- ( ph -> S e. Word A ) $.
    splfv3.f $e |- ( ph -> F e. ( 0 ... T ) ) $.
    splfv3.t $e |- ( ph -> T e. ( 0 ... ( # ` S ) ) ) $.
    splfv3.r $e |- ( ph -> R e. Word A ) $.
    splfv3.x $e |- ( ph -> X e. ( 0 ..^ ( ( # ` S ) - T ) ) ) $.
    splfv3.k $e |- ( ph -> K = ( F + ( # ` R ) ) ) $.
    $( Symbols to the right of a splice are unaffected.  (Contributed by
       Thierry Arnoux, 14-Dec-2023.) $)
    splfv3 $p |- ( ph -> ( ( S splice <. F , T , R >. ) ` ( X + K ) )
                         = ( S ` ( X + T ) ) ) $=
      ( caddc co cfv wcel cc0 wceq cotp csplice cconcat chash cop csubstr cword
      cpfx cfz splval syl13anc cuz wss elfzuz3 fzss2 3syl sseldd pfxlen syl2anc
      oveq1d pfxcl syl ccatlen 3eqtr4rd oveq2d fveq12d cfzo ccatcl swrdcl lencl
      cn0 nn0fz0 sylib swrdlen syl3anc eleqtrrd ccatval3 swrdfv syl31anc 3eqtrd
      cmin ) AHGOPZDFECUAUBPZQHDFUHPZCUCPZUDQZOPZWEDEDUDQZUEUFPZUCPZQZHWIQZHEOP
      DQZAWBWGWCWJADBUGZRZFSEUIPZRESWHUIPZRZCWNRZWCWJTIJKLCDEFWNWPWQWNUJUKAGWFH
      OAWDUDQZCUDQZOPZFXAOPWFGAWTFXAOAWOFWQRWTFTIAWPWQFAWRWHEULQRWPWQUMKESWHUNE
      SWHUOUPJUQBDFURUSUTAWDWNRZWSWFXBTAWOXCIBDFVAVBZLBBWDCVCUSNVDVEVFAWEWNRZWI
      WNRZHSWIUDQZVGPZRWKWLTAXCWSXEXDLBWDCVHUSAWOXFIBDEWHVIVBAHSWHEWAPZVGPZXHMA
      XGXISVGAWOWRWHWQRZXGXITIKAWOXKIWOWHVKRXKBDVJWHVLVMVBZBDEWHVNVOVEVPBWEWIHV
      QVOAWOWRXKHXJRWLWMTIKXLMBDEWHHVRVSVT $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Cyclic shift of words
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Cyclically shifting a single letter word keeps it unchanged.  (Contributed
     by Thierry Arnoux, 21-Nov-2023.) $)
  1cshid $p |- ( ( W e. Word V /\ N e. ZZ /\ ( # ` W ) = 1 )
              -> ( W cyclShift N ) = W ) $=
    ( cword wcel cz chash cfv c1 wceq w3a ccsh co cmo cc0 cshwmodn simp3 oveq2d
    3adant3 zmod10 3ad2ant2 eqtrd cshw0 3ad2ant1 3eqtrd ) CBDEZAFEZCGHZIJZKZCAL
    MZCAUHNMZLMZCOLMZCUFUGUKUMJUIABCPSUJULOCLUJULAINMZOUJUHIANUFUGUIQRUGUFUOOJU
    IATUAUBRUFUGUNCJUIBCUCUDUE $.

  ${
    $d A i $.  $d B i $.  $d V i $.
    $( Cyclically shifting a length 2 word swaps its symbols.  (Contributed by
       Thierry Arnoux, 19-Sep-2023.) $)
    cshw1s2 $p |- ( ( A e. V /\ B e. V )
                 -> ( <" A B "> cyclShift 1 ) = <" B A "> ) $=
      ( vi wcel c1 cfv cmo co cop csubstr cpfx cconcat c2 oveq2i cc0 wceq caddc
      cfzo csn wa cs2 chash cs1 ccsh s2len cr crp cle wbr clt 1re 2rp 0le1 1lt2
      modid mp4an eqtri opeq12i cmin cmpt cword s2cl cfz ctp tpid2g ax-mp fz0tp
      eleqtrri tpid3g swrdval2 mp3an23 syl 2m1e1 fzo01 a1i simpr eleqtrdi elsni
      cv oveq1d 0p1e1 eqtrdi fveq2d s2fv1 ad2antlr mpteq12dva cxp fconstmpt cn0
      eqtrd 0nn0 xpsng sylancr s1val adantl eqtr4d eqtr3id 3eqtrd eqtrid pfx1s2
      oveq12d cz 1z cshword sylancl df-s2 3eqtr4d ) ACEZBCEZUAZABUBZFXLUCGZHIZX
      MJZKIZXLXNLIZMIZBUDZAUDZMIZXLFUEIZBAUBZXKXPXSXQXTMXKXPXLFNJZKIZXSXOYDXLKX
      NFXMNXNFNHIZFXMNFHABUFZOFUGEZNUHEZPFUIUJFNUKUJYFFQULUMUNUOFNUPUQURZYGUSOX
      KYEDPNFUTIZSIZDVTZFRIZXLGZVAZDPTZBVAZXSXKXLCVBEZYEYPQZABCVCZYSFPNVDIZENPX
      MVDIZEYTFPFNVEZUUBYHFUUDEULFUGPNVFVGVHVINUUBUUCNUUDUUBYINUUDEUMNUHPFVJVGV
      HVIXMNPVDYGOVIDCXLFNVKVLVMXKDYLYOYQBYLYQQXKYLPFSIYQYKFPSVNOVOURZVPXKYMYLE
      ZUAZYOFXLGZBUUGYNFXLUUGYNPFRIFUUGYMPFRUUGYMYQEYMPQUUGYMYLYQXKUUFVQUUEVRYM
      PVSVMWAWBWCWDXJUUHBQXIUUFABCWEWFWKWGXKYRYQBTWHZXSDYQBWIXKUUIPBJTZXSXKPWJE
      XJUUIUUJQWLXIXJVQPBWJCWMWNXJXSUUJQXIBCWOWPWQWRWSWTXKXQXLFLIXTXNFXLLYJOABC
      XAWTXBXKYSFXCEYBXRQUUAXDFCXLXEXFYCYAQXKBAXGVPXH $.
  $}

  ${
    $d N c i j $.  $d V c i j $.  $d W c i j $.
    $( Cyclically shifting a word preserves its range.  (Contributed by Thierry
       Arnoux, 19-Sep-2023.) $)
    cshwrnid $p |- ( ( W e. Word V /\ N e. ZZ )
                  -> ran ( W cyclShift N ) = ran W ) $=
      ( vc vj vi wcel cz wa cv co cfv wceq cc0 wrex cab cmin cmo adantl oveq1d
      cword ccsh chash cfzo crn w3a elfzoelz 3ad2ant3 simp2 zsubcld cn0 clt wbr
      cn elfzo0 simp2bi zmodfzo syl2anc 3expa caddc simplr zaddcld simpr eqeq2d
      cr zred readdcld nnrpd modsubmod syl3anc zcnd pncand zmodidfzoimp 3eqtrrd
      crp rspcedvd simp3 fveq2d simp1l simp1r cshwidxmodr eqtrd rexxfrd2 abbidv
      wfn cshwfn fnrnfv syl wrdfn adantr 3eqtr4d ) CBUAGZAHGZIZDJZEJZCAUBKZLZMZ
      ENCUCLZUDKZOZDPZWOFJZCLZMZFXAOZDPZWQUEZCUEZWNXBXGDWNWSXFEFXDAQKZWTRKZXAXA
      WLWMXDXAGZXLXAGZWLWMXMUFZXKHGWTUNGZXNXOXDAXMWLXDHGWMXDNWTUGUHWLWMXMUIUJXM
      WLXPWMXMXDUKGXPXDWTULUMXDWTUOUPUHXKWTUQURUSWNWPXAGZIZWPXLMZWPWPAUTKZWTRKZ
      AQKZWTRKZMFYAXAXRXTHGXPYAXAGXRWPAXQWPHGWNWPNWTUGSZWLWMXQVAZVBXQXPWNXQWPUK
      GXPWPWTULUMWPWTUOUPSZXTWTUQURXRXDYAMZIZXLYCWPYHXKYBWTRYHXDYAAQXRYGVCTTVDX
      RYCXTAQKZWTRKZWPWTRKZWPXRXTVEGAVEGWTVOGYCYJMXRWPAXRWPYDVFXRAYEVFZVGYLXRWT
      YFVHXTAWTVIVJXRYIWPWTRXRWPAXRWPYDVKXRAYEVKVLTXQYKWPMWNWPWTVMSVNVPWNXMXSUF
      ZWRXEWOYMWRXLWQLZXEYMWPXLWQWNXMXSVQVRYMWLWMXMYNXEMWLWMXMXSVSWLWMXMXSVTWNX
      MXSUIXDABCWAVJWBVDWCWDWNWQXAWEXIXCMABCWFEDXAWQWGWHWNCXAWEZXJXHMWLYOWMBCWI
      WJFDXACWGWHWK $.
  $}

  $( Condition for the cyclic shift to be a bijection.  (Contributed by Thierry
     Arnoux, 4-Oct-2023.) $)
  cshf1o $p |- ( ( W e. Word D /\ W : dom W -1-1-> D /\ N e. ZZ ) -> ( W
      cyclShift N ) : dom W -1-1-onto-> ran W ) $=
    ( cword wcel cdm wf1 cz w3a ccsh co wceq wf1o cshwrnid 3adant2 f1eq2 biimpa
    crn cc0 syl2anc chash cfv cfzo wrddm 3ad2ant1 simp2 simp3 eqid cshf1 mp3an3
    biimpar f1f1orn syl f1oeq3 ) CADEZCFZACGZBHEZIZCBJKZRZCRZLZUPVAUTMZUPVBUTMZ
    UOURVCUQBACNOUSUPAUTGZVDUSUPSCUAUBUCKZLZVGAUTGZVFUOUQVHURACUDUEZUSVGACGZURV
    IUSVHUQVKVJUOUQURUFVHUQVKUPVGACPQTUOUQURUGVKURUTUTLVIUTUHABCUTUIUJTVHVFVIUP
    VGAUTPUKTUPAUTULUMVCVDVEVAVBUPUTUNQT $.

$[ set-mbox-ta-algtop.mm $]


$[ set-mbox-ta-ucm.mm $]


$[ set-mbox-ta-rrhom.mm $]


$[ set-mbox-ta-man.mm $]


$[ set-mbox-ta-esum.mm $]


$[ set-mbox-ta-ofc.mm $]


$[ set-mbox-ta-meas.mm $]


$[ set-mbox-ta-itgm.mm $]


$[ set-mbox-ta-eulerpart.mm $]


$[ set-mbox-ta-fibonacci.mm $]


$[ set-mbox-ta-proba.mm $]


$[ set-mbox-ta-ballot.mm $]


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Signum (sgn or sign) function - misc. additions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$[ set-mbox-ta-signs.mm $]


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Number Theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x $.  $d B x $.
    iblidicc.a $e |- ( ph -> A e. RR ) $.
    iblidicc.b $e |- ( ph -> B e. RR ) $.
    $( The identity function is integrable on any closed interval.
       (Contributed by Thierry Arnoux, 13-Dec-2021.) $)
    iblidicc $p |- ( ph -> ( x e. ( A [,] B ) |-> x ) e. L^1 ) $=
      ( cr wcel cicc co cv cmpt ccncf cibl wss iccssre syl2anc ax-resscn sstrdi
      cc ssid cncfmptid sylancl cniccibl syl3anc ) ACGHZDGHZBCDIJZBKLZUHTMJHZUI
      NHEFAUHTOTTOUJAUHGTAUFUGUHGOEFCDPQRSTUABUHTUBUCCDUIUDUE $.
  $}

  $( Continuity of the real positive square root function.  (Contributed by
     Thierry Arnoux, 20-Dec-2021.) $)
  rpsqrtcn $p |- ( sqrt |` RR+ ) e. ( RR+ -cn-> RR+ ) $=
    ( vx csqrt crp cres ccncf co wcel wf cv cdm cc cr wceq sqrtf ax-mp wb mpbir
    wss cc0 cpnf cfv wa wral rpssre ax-resscn sstri fdm sseqtrri sseli rpsqrtcl
    rgen wfun ffun ffvresb cico cioo ioossico eqsstrri resabs1 resqrtcn rescncf
    jca ioorp mp2 eqeltrri cncfcdm mp2an ) BCDZCCEFGZCCVHHZVJAIZBJZGZVKBUACGZUB
    ZACUCZVOACVKCGVMVNCVLVKCKVLCLKUDUEUFZKKBHZVLKMNKKBUGOUHUIVKUJVBUKBULZVJVPPV
    RVSNKKBUMOACCBUNOQCKRVHCLEFZGVIVJPVQBSTUOFZDZCDZVHVTCWARZWCVHMCSTUPFWAVCSTU
    QURZBCWAUSOWDWBWALEFGWCVTGWEUTWALCWBVAVDVECLCVHVFVGQ $.

$(
  @{
    divsqrtid.a @e |- ( ph -> A e. RR ) @.
    divsqrtid.1 @e |- ( ph -> 0 <_ A ) @.
    @( A real number divided by its square root.  (Contributed by Thierry
       Arnoux, 29-Dec-2021.) @)
    divsqrtid @p |- ( ph -> ( A / ( sqrt ` A ) ) = ( sqrt ` A ) ) @=
      ? @.
  @}
$)

  $( A real number divided by its square root.  (Contributed by Thierry Arnoux,
     1-Jan-2022.) $)
  divsqrtid $p |- ( A e. RR+ -> ( A / ( sqrt ` A ) ) = ( sqrt ` A ) ) $=
    ( crp wcel csqrt cfv cmul co cdiv cc0 cle wceq rpre rpge0 remsqsqrt syl2anc
    cr wbr oveq1d recnd sqrtcld rpsqrtcl rpne0d divcan4d eqtr3d ) ABCZADEZUFFGZ
    UFHGAUFHGUFUEUGAUFHUEAPCIAJQUGAKALZAMANORUEUFUFUEAUEAUHSTZUIUEUFAUAUBUCUD
    $.

  ${
    $d A x y z $.  $d D x $.  $d ph x $.
    cxpcncf1.a $e |- ( ph -> A e. CC ) $.
    cxpcncf1.d $e |- ( ph -> D C_ ( CC \ ( -oo (,] 0 ) ) ) $.
    $( The power function on complex numbers, for fixed exponent A, is
       continuous.  Similar to ~ cxpcn .  (Contributed by Thierry Arnoux,
       20-Dec-2021.) $)
    cxpcncf1 $p |- ( ph -> ( x e. D |-> ( x ^c A ) ) e. ( D -cn-> CC ) ) $=
      ( vy vz cc co cv ccxp cmpt ccncf wss wceq wcel cfv eqid a1i cmnf cc0 cioc
      cdif cres resmpt syl ccnfld ctopn crest ctopon cnfldtopon difss resttopon
      ccn mp2an cnmptid cnmptc cmpo ctx cxpcn oveq12 cnmpt12 toponrestid cncfcn
      ssid eqcomi eleqtrd rescncf imp syl2anc eqeltrrd ) ABIUAUBUCJZUDZBKZCLJZM
      ZDUEZBDVPMZDINJZADVNOZVRVSPFBVNDVPUFUGAWAVQVNINJZQZVRVTQZFAVQUHUIRZVNUJJZ
      WEUOJZWBABGHVOCGKZHKZLJZVPWFWFWEWEVNVNIWFVNUKRQZAWEIUKRQZVNIOZWKWEWESZULZ
      IVMUMZVNWEIUNUPTZABWFVNWQUQABCWFWEVNIWQWLAWOTZEURWQWRGHVNIWJUSWFWEUTJWEUO
      JQAGHVNWEWFVNSWNWFSZVATWHVOWICLVBVCWGWBPAWBWGWMIIOWBWGPWPIVFVNIWEWFWEWNWS
      WEIWOVDVEUPVGTVHWAWCWDVNIDVQVIVJVKVL $.
  $}

  ${
    $d A x $.  $d ph x $.
    efmul2picn.1 $e |- ( ph -> ( x e. A |-> B ) e. ( A -cn-> CC ) ) $.
    $( Multiplying by ` ( _i x. ( 2 x. _pi ) ) ` and taking the exponential
       preserves continuity.  (Contributed by Thierry Arnoux, 13-Dec-2021.) $)
    efmul2picn $p |- ( ph -> ( x e. A |->
      ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. B ) ) ) e. ( A -cn-> CC ) ) $=
      ( ci c2 cpi cmul co ce cc ccncf wcel efcn a1i wss cmpt ax-icn mulcli picn
      2cn cncfrss syl ssidd cncfmptc syl3anc mulcncf cncfmpt1f ) ABFGHIJZIJZDIJ
      KCKLLMJNAOPABUKDCAUKLNZCLQZLLQBCUKRCLMJZNULAFUJSGHUBUATTPABCDRZUNNUMECLUO
      UCUDALUEBUKCLUFUGEUHUI $.
  $}

  ${
    $d t x y A $.  $d t x y B $.  $d x E $.  $d t x y F $.  $d t x y ph $.
    ftc2re.e $e |- E = ( C (,) D ) $.
    ftc2re.a $e |- ( ph -> A e. E ) $.
    ftc2re.b $e |- ( ph -> B e. E ) $.
    $( Lemma for ~ ftc2re .  (Contributed by Thierry Arnoux, 20-Dec-2021.) $)
    fct2relem $p |- ( ph -> ( A [,] B ) C_ E ) $=
      ( co cxr wcel clt wbr wa eleqtrdi syl simpld simprd eliooord cicc eliooxr
      cioo wss iccssioo syl22anc sseqtrrdi ) ABCUAJZDEUCJZFADKLZEKLZDBMNZCEMNZU
      HUIUDAUJUKABUILZUJUKOABFUIHGPZBDEUBQZRAUJUKUPSAULBEMNZAUNULUQOUOBDETQRADC
      MNZUMACUILURUMOACFUIIGPCDETQSDEBCUEUFGUG $.

    ftc2re.le $e |- ( ph -> A <_ B ) $.
    ftc2re.f $e |- ( ph -> F : E --> CC ) $.
    ftc2re.1 $e |- ( ph -> ( RR _D F ) e. ( E -cn-> CC ) ) $.
    $( The Fundamental Theorem of Calculus, part two, for functions continuous
       on ` D ` .  (Contributed by Thierry Arnoux, 1-Dec-2021.) $)
    ftc2re $p |- ( ph ->
      S. ( A (,) B ) ( ( RR _D F ) ` t ) _d t = ( ( F ` B ) - ( F ` A ) ) ) $=
      ( co cr cfv cc wceq wcel vy vx cioo cv cicc cres cdv citg ioossre eqsstri
      cmin wss a1i sseldd ccncf crn ctg cnt wf ax-resscn iccssre syl2anc ccnfld
      ctopn tgioo4 dvres syl22anc iccntr reseq2d eqtrd ioossicc fct2relem sstrd
      eqid rescncf sylc eqeltrd cibl cmbf cdm cvol cabs cle wbr wral wrex cnmbf
      ioombl cin dmres fveq2i cncff syl fdmd ineq2d dfss2 fveq2d volioo syl3anc
      sylib resubcld eqeltrid wi cniccbdd wa eqtrid eqsstrd ssralv adantr fvres
      sselda simpr ad2antrr eleqtrd eqtr4d breq1d biimpd ralimdva syld reximdva
      mpd bddibl dvcn syl31anc ftc2 fveq1d sylan9eq ralrimiva itgeq2 cxr ubicc2
      rexrd fvresd lbicc2 oveq12d 3eqtr3d ) ABCDUCOZBUDZPHCDUEOZUFZUGOZQZUHZDYT
      QZCYTQZUKOBYQYRPHUGOZQZUHZDHQZCHQZUKOABCDYTAGPCGPULZAGEFUCOPIEFUIUJUMZJUN
      ZAGPDUULKUNZLAUUAUUFYQUFZYQRUOOZAUUAUUFYSUCUPUQQZURQQZUFZUUOAPRULZGRHUSZU
      UKYSPULZUUAUUSSUUTAUTUMZMUULACPTZDPTZUVBUUMUUNCDVAVBGYSPUUQHVCVDQZUVFVNVE
      VFVGAUURYQUUFAUVDUVEUURYQSUUMUUNCDVHVBVIVJZAYQGULZUUFGRUOOZTZUUOUUPTZAYQY
      SGYQYSULACDVKUMZACDEFGIJKVLZVMZNGRYQUUFVOVPZVQAUUAUUOVRUVGAUUOVSTZUUOVTZW
      AQZPTUAUDZUUOQZWBQZUBUDZWCWDZUAUVQWEZUBPWFZUUOVRTAYQWAVTTZUVKUVPUWFACDWHU
      MUVOYQUUOWGVBAUVRYQUUFVTZWIZWAQZPUVQUWHWAUUFYQWJZWKAUWIYQWAQZPAUWHYQWAAUW
      HYQGWIZYQAUWGGYQAGRUUFAUVJGRUUFUSNGRUUFWLWMWNZWOAUVHUWLYQSUVNYQGWPWTVJZWQ
      AUWKDCUKOZPAUVDUVECDWCWDZUWKUWOSUUMUUNLCDWRWSADCUUNUUMXAVQVQXBAUVSUUFYSUF
      ZQZWBQZUWBWCWDZUAYSWEZUBPWFZUWEAUVDUVEUWQYSRUOOZTZUXBUUMUUNAUVJUXDNAYSGUL
      ZUVJUXDXCUVMGRYSUUFVOWMYAUBUACDUWQXDWSAUXAUWDUBPAUWBPTZXEZUXAUWTUAUVQWEZU
      WDAUXAUXHXCZUXFAUVQYSULZUXIAUVQYQYSAUVQUWHYQUWJUWNXFZUVLXGZUWTUAUVQYSXHWM
      XIUXGUWTUWCUAUVQUXGUVSUVQTZXEZUWTUWCUXNUWSUWAUWBWCUXNUWRUVTWBUXNUWRUVSUUF
      QZUVTUXNUVSYSTUWRUXOSUXGUVQYSUVSAUXJUXFUXLXIXKUVSYSUUFXJWMUXNUVSYQTUVTUXO
      SUXNUVSUVQYQUXGUXMXLAUVQYQSUXFUXMUXKXMXNUVSYQUUFXJWMXOWQXPXQXRXSXTYAUBUAU
      UOYBWSVQAHUVITZYTUXCTZAUUTUVAUUKUWGGSUXPUVCMUULUWMGPHYCYDAUXEUXPUXQXCUVMG
      RYSHVOWMYAYEAUUBUUGSZBYQWEUUCUUHSAUXRBYQAYRYQTUUBYRUUOQUUGAYRUUAUUOUVGYFY
      RYQUUFXJYGYHBYQUUBUUGYIWMAUUDUUIUUEUUJUKADYSHACYJTZDYJTZUWPDYSTACUUMYLZAD
      UUNYLZLCDYKWSYMACYSHAUXSUXTUWPCYSTUYAUYBLCDYNWSYMYOYP $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d E x y $.  $d F x y $.  $d ph x y $.
    fdvposlt.d $e |- E = ( C (,) D ) $.
    fdvposlt.a $e |- ( ph -> A e. E ) $.
    fdvposlt.b $e |- ( ph -> B e. E ) $.
    fdvposlt.f $e |- ( ph -> F : E --> RR ) $.
    fdvposlt.c $e |- ( ph -> ( RR _D F ) e. ( E -cn-> RR ) ) $.
    ${
      fdvposlt.lt $e |- ( ph -> A < B ) $.
      fdvposlt.1 $e |- ( ( ph /\ x e. ( A (,) B ) ) -> 0 < ( ( RR _D F ) ` x )
        ) $.
      $( Functions with a positive derivative, i.e. monotonously growing
         functions, preserve strict ordering.  (Contributed by Thierry Arnoux,
         20-Dec-2021.) $)
      fdvposlt $p |- ( ph -> ( F ` A ) < ( F ` B ) ) $=
        ( clt co cr wcel cc cfv wbr cc0 cmin cioo cdv citg cvol ioossre eqsstri
        cv sselid posdifd mpbid cle wceq ltled volioo syl3anc breqtrrd cicc wss
        ioossicc a1i ioombl wa wf ccncf cncff adantr fct2relem sselda ffvelcdmd
        cdm syl cmpt cibl ax-resscn ssid cncfss cres feqresmpt rescncf eqeltrrd
        mp2an sylc cniccibl iblss crp syldan sylanbrc itggt0 fss sylancl ftc2re
        elrp breqtrd mpbird ) ACHUAZDHUAZPUBUCWTWSUDQZPUBAUCBCDUEQZBUKZRHUFQZUA
        ZUGXAPABXBXEAUCDCUDQZXBUHUAZPACDPUBUCXFPUBNACDAGRCGEFUEQRIEFUIUJZJULZAG
        RDXHKULZUMUNACRSZDRSZCDUOUBXGXFUPXIXJACDXIXJNUQZCDURUSUTABXBCDVAQZXERXB
        XNVBACDVCVDZXBUHVNSACDVEVDAXCXNSZVFGRXCXDAGRXDVGZXPAXDGRVHQZSZXQMGRXDVI
        VOZVJAXNGXCACDEFGIJKVKZVLZVMAXKXLBXNXEVPZXNTVHQZSYCVQSXIXJAXNRVHQZYDYCR
        TVBZTTVBZYEYDVBVRTVSZXNRTVTWEAXDXNWAZYCYEABGRXNXDXTYAWBAXNGVBXSYIYESYAM
        GRXNXDWCWFWDULCDYCWGUSWHAXCXBSZVFZXERSUCXEPUBXEWISYKGRXCXDAXQYJXTVJAYJX
        PXCGSAXBXNXCXOVLYBWJVMOXEWPWKWLABCDEFGHIJKXMAGRHVGYFGTHVGLVRGRTHWMWNAXR
        GTVHQZXDYFYGXRYLVBVRYHGRTVTWEMULWOWQAWSWTAGRCHLJVMAGRDHLKVMUMWR $.
    $}

    ${
      fdvneggt.lt $e |- ( ph -> A < B ) $.
      fdvneggt.1 $e |- ( ( ph /\ x e. ( A (,) B ) ) -> ( ( RR _D F ) ` x ) < 0
        ) $.
      $( Functions with a negative derivative, i.e. monotonously decreasing
         functions, inverse strict ordering.  (Contributed by Thierry Arnoux,
         20-Dec-2021.) $)
      fdvneggt $p |- ( ph -> ( F ` B ) < ( F ` A ) ) $=
        ( vy cfv cr wcel cc clt wbr cneg cv cmpt ffvelcdmda renegcld fmpttd cdv
        wa co ccncf cvv cpr reelprrecn ax-resscn sselid fvexd feqmptd oveq2d wf
        a1i cncff syl eqtr3d dvmptneg wss wb ssid cncfss mp2an negfcncf cncfcdm
        eqid sylancr mpbird eqeltrd cioo cc0 adantr cicc fct2relem sstrd sselda
        ioossicc ffvelcdmd lt0neg1d mpbid wceq fveq1d simpr fveq2d negeqd eqtrd
        fvmptd breqtrrd fdvposlt eqidd 3brtr3d ltnegd ) ADHQZCHQZUAUBXBUCZXAUCZ
        UAUBACPGPUDZHQZUCZUEZQDXHQXCXDUAABCDEFGXHIJKAPGXGRAXEGSUJZXFAGRXEHLUFZU
        GUHARXHUIUKZPGXERHUIUKZQZUCZUEZGRULUKZAPXFXMRUMGRRTUNSAUOVBXIRTXFUPXJUQ
        XIXEXLURAXLRPGXFUEZUIUKPGXMUEAHXQRUIAPGRHLUSUTAPGRXLAXLXPSGRXLVAZMGRXLV
        CVDZUSVEVFZAXOXPSZGRXOVAZAPGXNRXIXMAGRXEXLXSUFUGUHARTVGZXOGTULUKZSZYAYB
        VHUPAXLYDSYEAXPYDXLYCTTVGXPYDVGUPTVIGRTVJVKMUQPGXLXOXOVNZVLVDGTRXOVMVOV
        PVQNABUDZCDVRUKZSZUJZVSYGXLQZUCZYGXKQZUAYJYKVSUAUBVSYLUAUBOYJYKYJGRYGXL
        AXRYIXSVTAYHGYGAYHCDWAUKZGYHYNVGACDWEVBACDEFGIJKWBWCWDZWFZWGWHYJYMYGXOQ
        YLYJYGXKXOAXKXOWIYIXTVTWJYJPYGXNYLGXORXOXOWIYJYFVBYJXEYGWIZUJZXMYKYRXEY
        GXLYJYQWKWLWMYOYJYKYPUGWOWNWPWQAPCXGXCGXHRAXHWRZAXECWIZUJZXFXBUUAXECHAY
        TWKWLWMJAXBAGRCHLJWFZUGWOAPDXGXDGXHRYSAXEDWIZUJZXFXAUUDXEDHAUUCWKWLWMKA
        XAAGRDHLKWFZUGWOWSAXAXBUUEUUBWTVP $.
    $}

    ${
      fdvposle.le $e |- ( ph -> A <_ B ) $.
      fdvposle.1 $e |- ( ( ph /\ x e. ( A (,) B ) ) -> 0 <_ ( ( RR _D F ) ` x )
          ) $.
      $( Functions with a nonnegative derivative, i.e. monotonously growing
         functions, preserve ordering.  (Contributed by Thierry Arnoux,
         20-Dec-2021.) $)
      fdvposle $p |- ( ph -> ( F ` A ) <_ ( F ` B ) ) $=
        ( co cr wss wcel cc cc0 cfv cmin cle wbr cioo cv cdv citg cicc ioossicc
        a1i cvol cdm ioombl wa wf ccncf cncff adantr fct2relem sselda ffvelcdmd
        syl cmpt cibl ioossre sselid ax-resscn ssid cncfss mp2an cres feqresmpt
        eqsstri rescncf sylc eqeltrrd cniccibl syl3anc iblss syldan fss sylancl
        itgge0 ftc2re breqtrd subge0d mpbid ) AUADHUBZCHUBZUCPZUDUEWKWJUDUEAUAB
        CDUFPZBUGZQHUHPZUBZUIWLUDABWMWPABWMCDUJPZWPQWMWQRACDUKULZWMUMUNSACDUOUL
        AWNWQSZUPGQWNWOAGQWOUQZWSAWOGQURPZSZWTMGQWOUSVDZUTAWQGWNACDEFGIJKVAZVBZ
        VCACQSDQSBWQWPVEZWQTURPZSXFVFSAGQCGEFUFPQIEFVGVOZJVHAGQDXHKVHAWQQURPZXG
        XFQTRZTTRZXIXGRVITVJZWQQTVKVLAWOWQVMZXFXIABGQWQWOXCXDVNAWQGRXBXMXISXDMG
        QWQWOVPVQVRVHCDXFVSVTWAAWNWMSZUPGQWNWOAWTXNXCUTAXNWSWNGSAWMWQWNWRVBXEWB
        VCOWEABCDEFGHIJKNAGQHUQXJGTHUQLVIGQTHWCWDAXAGTURPZWOXJXKXAXORVIXLGQTVKV
        LMVHWFWGAWJWKAGQDHLKVCAGQCHLJVCWHWI $.
    $}

    ${
      fdvnegge.le $e |- ( ph -> A <_ B ) $.
      fdvnegge.1 $e |- ( ( ph /\ x e. ( A (,) B ) ) -> ( ( RR _D F ) ` x ) <_ 0
          ) $.
      $( Functions with a nonpositive derivative, i.e., decreasing functions,
         preserve ordering.  (Contributed by Thierry Arnoux, 20-Dec-2021.) $)
      fdvnegge $p |- ( ph -> ( F ` B ) <_ ( F ` A ) ) $=
        ( vy cfv cr wcel cc cle wbr cneg cv cmpt ffvelcdmda renegcld fmpttd cdv
        wa co ccncf cvv cpr reelprrecn ax-resscn sselid fvexd feqmptd oveq2d wf
        a1i cncff syl eqtr3d dvmptneg wss wb ssid cncfss mp2an negfcncf cncfcdm
        eqid sylancr mpbird eqeltrd cioo cc0 adantr cicc fct2relem sstrd sselda
        ioossicc ffvelcdmd le0neg1d mpbid wceq fveq1d simpr fveq2d negeqd eqtrd
        fvmptd breqtrrd fdvposle eqidd 3brtr3d lenegd ) ADHQZCHQZUAUBXBUCZXAUCZ
        UAUBACPGPUDZHQZUCZUEZQDXHQXCXDUAABCDEFGXHIJKAPGXGRAXEGSUJZXFAGRXEHLUFZU
        GUHARXHUIUKZPGXERHUIUKZQZUCZUEZGRULUKZAPXFXMRUMGRRTUNSAUOVBXIRTXFUPXJUQ
        XIXEXLURAXLRPGXFUEZUIUKPGXMUEAHXQRUIAPGRHLUSUTAPGRXLAXLXPSGRXLVAZMGRXLV
        CVDZUSVEVFZAXOXPSZGRXOVAZAPGXNRXIXMAGRXEXLXSUFUGUHARTVGZXOGTULUKZSZYAYB
        VHUPAXLYDSYEAXPYDXLYCTTVGXPYDVGUPTVIGRTVJVKMUQPGXLXOXOVNZVLVDGTRXOVMVOV
        PVQNABUDZCDVRUKZSZUJZVSYGXLQZUCZYGXKQZUAYJYKVSUAUBVSYLUAUBOYJYKYJGRYGXL
        AXRYIXSVTAYHGYGAYHCDWAUKZGYHYNVGACDWEVBACDEFGIJKWBWCWDZWFZWGWHYJYMYGXOQ
        YLYJYGXKXOAXKXOWIYIXTVTWJYJPYGXNYLGXORXOXOWIYJYFVBYJXEYGWIZUJZXMYKYRXEY
        GXLYJYQWKWLWMYOYJYKYPUGWOWNWPWQAPCXGXCGXHRAXHWRZAXECWIZUJZXFXBUUAXECHAY
        TWKWLWMJAXBAGRCHLJWFZUGWOAPDXGXDGXHRYSAXEDWIZUJZXFXAUUDXEDHAUUCWKWLWMKA
        XAAGRDHLKWFZUGWOWSAXAXBUUEUUBWTVP $.
    $}
  $}

  ${
    $d A k $.  $d B k $.  $d C k $.  $d k ph $.
    prodfzo03.1 $e |- ( k = 0 -> D = A ) $.
    prodfzo03.2 $e |- ( k = 1 -> D = B ) $.
    prodfzo03.3 $e |- ( k = 2 -> D = C ) $.
    prodfzo03.a $e |- ( ( ph /\ k e. ( 0 ..^ 3 ) ) -> D e. CC ) $.
    $( A product of three factors, indexed starting with zero.  (Contributed by
       Thierry Arnoux, 14-Dec-2021.) $)
    prodfzo03 $p |- ( ph -> prod_ k e. ( 0 ..^ 3 ) D = ( A x. ( B x. C ) ) ) $=
      ( cc0 c3 co c1 cmul c2 wceq a1i wcel cc cfzo cprod csn c0 fzodisjsn caddc
      cin cun 2p1e3 oveq2i cuz cfv fzosplitsn ax-mp eqtr3i cfn fzofi fprodsplit
      2eluzge0 wne 0ne1 disjsn2 mp1i cpr fzo0to2pr df-pr eqtri cv wss cz cle 2z
      wbr 3z 2re 3re 2lt3 ltleii eluz2 mpbir3an fzoss2 sseli sylan2 oveq1d snfi
      eqtrd velsn wa adantl simpr adantr eqeltrrd wrex ctp c0ex tpid1 fzo0to3tp
      eleqtrri eqeq1d rspcev mp2an r19.29a eqeltrd sylan2b fprodcl 1eltp012 2ex
      eqid tpid3 mulassd cn0 0nn0 prodsn syl2anc 1nn0 2nn0 oveq12d 3eqtrd ) AKL
      UAMZEFUBZKUCZEFUBZNUCZEFUBZOMZPUCZEFUBZOMZYBYDYGOMZOMBCDOMZOMAXTKPUAMZEFU
      BZYGOMYHAYKYFEXSFYKYFUGUDQAKPUERXSYKYFUHZQAKPNUFMZUAMZXSYMYNLKUAUIUJPKUKU
      LSYOYMQUSKPUMUNUORXSUPSAKLUQRJURAYLYEYGOAYAYCEYKFKNUTYAYCUGUDQAVAKNVBVCYK
      YAYCUHZQAYKKNVDYPVEKNVFVGRYKUPSAKPUQRFVHZYKSAYQXSSZETSZYKXSYQLPUKULSZYKXS
      VIYTPVJSLVJSPLVKVMVLVNPLVOVPVQVRPLVSVTPKLWAUNWBJWCURWDWFAYBYDYGAYAEFYAUPS
      AKWERYQYASAYQKQZYSFKWGAUUAWHEBTUUAEBQZAGWIABTSZUUAAUUBUUCFXSAYRWHZUUBWHEB
      TUUDUUBWJUUDYSUUBJWKWLUUBFXSWMZAKXSSBBQZUUEKKNPWNZXSKNPWOWPWQWRBXHUUBUUFF
      KXSUUAEBBGWSWTXARXBZWKXCXDXEAYCEFYCUPSANWERYQYCSAYQNQZYSFNWGAUUIWHECTUUIE
      CQZAHWIACTSZUUIAUUJUUKFXSUUDUUJWHECTUUDUUJWJUUDYSUUJJWKWLUUJFXSWMZANXSSCC
      QZUULNUUGXSXFWQWRCXHUUJUUMFNXSUUIECCHWSWTXARXBZWKXCXDXEAYFEFYFUPSAPWERYQY
      FSAYQPQZYSFPWGAUUOWHEDTUUOEDQZAIWIADTSZUUOAUUPUUQFXSUUDUUPWHEDTUUDUUPWJUU
      DYSUUPJWKWLUUPFXSWMZAPXSSDDQZUURPUUGXSKNPXGXIWQWRDXHUUPUUSFPXSUUOEDDIWSWT
      XARXBZWKXCXDXEXJAYBBYIYJOAKXKSZUUCYBBQUVAAXLRUUHEBFKXKGXMXNAYDCYGDOANXKSZ
      UUKYDCQUVBAXORUUNECFNXKHXMXNAPXKSZUUQYGDQUVCAXPRUUTEDFPXKIXMXNXQXQXR $.
  $}

  ${
    $d A x y z $.  $d B z $.  $d C f y z $.  $d F f y z $.  $d I k x y z $.
    $d f k x y z $.  $d ph f k y z $.
    actfunsn.1 $e |- ( ( ph /\ k e. C ) -> A C_ ( C ^m B ) ) $.
    actfunsn.2 $e |- ( ph -> C e. _V ) $.
    actfunsn.3 $e |- ( ph -> I e. V ) $.
    actfunsn.4 $e |- ( ph -> -. I e. B ) $.
    actfunsn.5 $e |- F = ( x e. A |-> ( x u. { <. I , k >. } ) ) $.
    $( The action ` F ` of extending function from ` B ` to ` C ` with new
       values at point ` I ` is a bijection.  (Contributed by Thierry Arnoux,
       9-Dec-2021.) $)
    actfunsnf1o $p |- ( ( ph /\ k e. C ) -> F : A -1-1-onto-> ran F ) $=
      ( vz cv wcel wa wceq adantr crn cop csn cun cres cmpt uneq1 cbvmptv eqtri
      vy cvv vex snex unex a1i resex wrex elrnmpti sylibr adantll simpr reseq1d
      rspe wfn cin c0 cmap co sselda elmapfn syl fnsng sylan wn disjsn fnunres1
      syl3anc eqtr2d jca anasss ad3antrrr simplr sseldd ad4antr simp-4r syl2anc
      wss eqeltrd bilani r19.29a uneq1d eqtrd eqtr4d impbida f1od ) AFPZEQZRZOU
      JCGUAZOPZHWPUBZUCZUDZUJPZDUEZGUKUKGBCBPZXBUDZUFOCXCUFNBOCXGXCXFWTXBUGUHUI
      ZXCUKQWRWTCQZRZWTXBOULXAUMUNZUOXEUKQWRXDWSQZRZXDDUJULUPUOWRXIXDXCSZRZXLWT
      XESZRZWRXIXNXQXJXNRZXLXPXIXNXLWRXOXNOCUQZXLXNOCVCOCXCXDGXHXKURZUSUTXRXEXC
      DUEZWTXRXDXCDXJXNVAVBXJYAWTSZXNXJWTDVDZXBHUCZVDZDYDVEVFSZYBXJWTEDVGVHZQZY
      CWRCYGWTJVIWTEDVJZVKWRYEXIAHIQZWQYELHWPIEVLZVMTWRYFXIAYFWQAHDQVNYFMDHVOUS
      ZTTDYDWTXBVPZVQTVRVSVTWRXLXPXOXMXPRZXIXNYNWTXECXMXPVAZXMXECQZXPXMXNYPOCXM
      XIRZXNRZXEYACYRXDXCDYQXNVAZVBZYRYAWTCYRYCYEYFYBYRYHYCYRCYGWTWRCYGWGXLXIXN
      JWAXMXIXNWBZWCYIVKYRYJWQYEAYJWQXLXIXNLWDAWQXLXIXNWEYKWFAYFWQXLXIXNYLWDYMV
      QZUUAWHWHXLXSWRXTWIZWJTWHYNXCXEXBUDZXDYNWTXEXBYOWKXMUUDXDSZXPXMXNUUEOCYRU
      UDXCXDYRXEWTXBYRXEYAWTYTUUBWLWKYSWMUUCWJTVRVSVTWNWO $.

    $( The action ` F ` of extending function from ` B ` to ` C ` with new
       values at point ` I ` yields different functions.  (Contributed by
       Thierry Arnoux, 9-Dec-2021.) $)
    actfunsnrndisj $p |- ( ph -> Disj_ k e. C ran F ) $=
      ( vf vz cv wceq wcel wa cfv crn wdisj cop csn cun simpr fveq1d wfn cin c0
      wral cmap wss ad2antrr sseldd elmapfn syl ad3antrrr simpllr fnsng syl2anc
      co disjsn sylibr snidg fvun2 syl112anc fvsng eqtrd adantr wrex cmpt uneq1
      wn cbvmptv eqtri vex snex unex elrnmpti bilani r19.29a ralrimiva invdisj
      ) AHOQZUAZFQZRZOGUBZULZFEULFEWJUCAWKFEAWHESZTZWIOWJWMWFWJSZTZWFPQZHWHUDZU
      EZUFZRZWIPCWOWPCSZTZWTTZWGHWSUAZWHXCHWFWSXBWTUGUHXBXDWHRWTXBXDHWRUAZWHXBW
      PDUIZWRHUEZUIZDXGUJUKRZHXGSZXDXERXBWPEDUMVCZSXFXBCXKWPWMCXKUNWNXAJUOWOXAU
      GUPWPEDUQURXBHISZWLXHAXLWLWNXALUSZAWLWNXAUTZHWHIEVAVBAXIWLWNXAAHDSVOXIMDH
      VDVEUSXBXLXJXMHIVFURDXGWPWRHVGVHXBXLWLXEWHRXMXNHWHIEVIVBVJVKVJWNWTPCVLWMP
      CWSWFGGBCBQZWRUFZVMPCWSVMNBPCXPWSXOWPWRVNVPVQWPWRPVRWQVSVTWAWBWCWDWDFOEWJ
      WGWEUR $.
  $}

  ${
    $d N x y z $.
    $( The basis for the circle method in the form of trigonometric sums.
       Proposition of [Nathanson] p. 123.  (Contributed by Thierry Arnoux,
       2-Dec-2021.) $)
    itgexpif $p |- ( N e. ZZ -> S. ( 0 (,) 1 ) ( exp ` ( ( _i x. ( 2 x. _pi ) )
      x. ( N x. x ) ) ) _d x = if ( N = 0 , 1 , 0 ) ) $=
      ( vy wcel cc0 wceq c1 co cmul ce cfv wa fveq2d cc cr cdiv cmpt a1i mulcld
      adantr vz cz cif cioo ci c2 cpi cv citg wral oveq1 oveq2d ax-resscn sstri
      ioossre sseli mul02d ax-icn 2cn picn mulcli mul01i ef0 sylan9eq ralrimiva
      eqtrdi itgeq2 syl cdm ioombl 0re 1re ioovolcl mp2an ax-1cn itgconst mp3an
      cvol cmin cle wbr 0le1 volioo subid1i oveq2i mulridi 3eqtri adantl eqcomd
      eqtri wn cdv cmnf cpnf ioomax eqcomi 0red 1red wss sselda 2cnd simpl zcnd
      simpr efcld syldan ine0 pipos gtneii mulne0i neqned mulne0d divcld fmpttd
      wne ccncf reelprrecn cnelprrecn dvmptid dvmptcmul mulridd mpteq2dva eqtrd
      2ne0 cpr dvef eff feqmptd 3eqtr3a dvmptdivc fveq2 oveq1d dvmptco divcan1d
      wf efcn cres mp1i eqeltrrd fvmptd resmpt eqid mulc1cncf rescncf cncfmpt1f
      wi mpd eqeltrd ftc2re fveq1d cbvmptv fvmpt2d mulassd sylan2 ef2kpi sselid
      oveq2 eqidd mul01d oveq12d subidd 3eqtr3d ifeqda ) BUBDZBEFZGEUCAEGUDHZUE
      UFUGIHZIHZBAUHZIHZIHZJKZUIZUVDUVEGEUVMUVDUVELUVMGUVEUVMGFUVDUVEUVMAUVFGUI
      ZGUVEUVLGFZAUVFUJUVMUVNFUVEUVOAUVFUVEUVIUVFDZUVLUVHEUVIIHZIHZJKZGUVEUVKUV
      RJUVEUVJUVQUVHIBEUVIIUKULMUVPUVSEJKZGUVPUVREJUVPUVRUVHEIHEUVPUVQEUVHIUVPU
      VIUVFNUVIUVFONEGUOZUMUNUPUQULUVHUEUVGURUFUGUSUTVAZVAZVBVFMVCVFVDVEAUVFUVL
      GVGVHUVNGUVFVRKZIHZGGIHGUVFVRVIDUWDODZGNDZUVNUWEFEGVJEODZGODZUWFVKVLEGVMV
      NVOAUVFGVPVQUWDGGIUWDGEVSHZGUWHUWIEGVTWAZUWDUWJFVKVLWBEGWCVQGVOWDWJWEGVOW
      FWGVFWHWIUVDUVEWKZLZUVMEUWMAUVFUVIOCOUVHBIHZCUHZIHZJKZUWNPHZQZWLHZKZUIZGU
      WSKZEUWSKZVSHZUVMEUWMAEGWMWNOUWSWMWNUDHOWOWPUWMWQZUWMWRZUWKUWMWBRUWMCOUWR
      NUWMUWOODZLZUWQUWNUWMUXHUWONDZUWQNDUWMONUWOONWSZUWMUMRZWTZUWMUXJLZUWPUXNU
      WNUWOUWMUWNNDZUXJUWMUVHBUWMUEUVGUENDUWMURRUWMUFUGUWMXAUGNDUWMUTRSSZUWMBUV
      DUWLXBZXCZSZTUWMUXJXDSXEXFZUWMUXOUXHUXSTZUWMUWNEXOZUXHUWMUVHBUXPUXRUVHEXO
      UWMUEUVGURUWBXGUFUGUSUTYDEUGVKXHXIXJXJRUWMBEUVDUWLXDXKXLZTZXMXNUWMUWTCOUW
      QQZONXPHZUWMUWTCOUWRUWNIHZQUYEUWMCUAUWPUWNUAUHZJKZUWNPHZUYJONUWRUWRNNONOO
      NYEZDUWMXQRZNUYKDUWMXRRZUXIUWNUWOUYAUXMSUYAUWMUYHNDZLZUYIUWNUYOUYHUWMUYNX
      DXEZUWMUXOUYNUXSTUWMUYBUYNUYCTXMZUYQUWMOCOUWPQZWLHCOUWNGIHZQCOUWNQUWMCUWO
      GUWNOOOUYLUXMUWIUXIVLRUWMCOUYLXSUXSXTUWMCOUYSUWNUXIUWNUYAYAYBYCUWMUAUYIUY
      IUWNNNNUYMUYPUYPUWMNJWLHJNUANUYIQZWLHUYTYFUWMJUYTNWLUWMUANNJNNJYOUWMYGRYH
      ZULVUAYIUXSUYCYJUYHUWPFUYIUWQUWNPUYHUWPJYKYLZVUBYMUWMCOUYGUWQUXIUWQUWNUXT
      UYAUYDYNYBYCZUWMCUWPJOJNNXPHZDUWMYPRUWMCNUWPQZOYQZUYRUYFUXKVUFUYRFUWMUMCN
      OUWPUUAYRUWMVUEVUDDZVUFUYFDZUWMUXOVUGUXSCUWNVUEVUEUUBUUCVHUXKVUGVUHUUFUWM
      UMNNOVUEUUDYRUUGYSUUEUUHUUIUWMUXAUVLFZAUVFUJUXBUVMFUWMVUIAUVFUVPUWMUVIODZ
      VUIUVFOUVIUWAUPUWMVUJLZUXAUVIUYEKZUVLVUKUVIUWTUYEUWMUWTUYEFVUJVUCTUUJVUKV
      ULUWNUVIIHZJKZUVLUWMAOVUNUYENUYEAOVUNQFUWMCAOUWQVUNUWOUVIFUWPVUMJUWOUVIUW
      NIUUQMUUKRVUKVUMVUKUWNUVIUWMUXOVUJUXSTUWMONUVIUXLWTZSXEUULVUKVUMUVKJVUKUV
      HBUVIUVHNDVUKUWCRUWMBNDVUJUXRTVUOUUMMYCYCUUNVEAUVFUXAUVLVGVHUWMUXEGUWNPHZ
      VUPVSHEUWMUXCVUPUXDVUPVSUWMUXCUYSJKZUWNPHZVUPUWMCGUWRVUROUWSNUWMUWSUURZUW
      MUWOGFZLZUWQVUQUWNPVVAUWPUYSJVVAUWOGUWNIUWMVUTXDULMYLUXGUWMVUQUWNUWMUYSUW
      MUWNGUXSUWGUWMVORSXEUXSUYCXMZYTUWMVUQGUWNPUWMVUQUWNJKZGUWMUYSUWNJUWMUWNUX
      SYAMUWMUVDVVCGFUXQBUUOVHYCYLZYCUWMUXDUWNEIHZJKZUWNPHZVUPUWMCEUWRVVGOUWSNV
      USUWMUWOEFZLZUWQVVFUWNPVVIUWPVVEJVVIUWOEUWNIUWMVVHXDULMYLUXFUWMVVFUWNUWMV
      VEUWMUWNEUXSUWMONEUMUXFUUPSXEUXSUYCXMYTUWMVVFGUWNPUWMVVFUVTGUWMVVEEJUWMUW
      NUXSUUSMVCVFYLYCUUTUWMVUPUWMVURVUPNVVDVVBYSUVAYCUVBWIUVCWI $.
  $}

  ${
    $d A k $.  $d B i $.  $d M i j k $.  $d N i j k $.  $d i j k ph $.
    fzsum2sub.m $e |- ( ph -> M e. NN0 ) $.
    fzsum2sub.n $e |- ( ph -> N e. NN0 ) $.
    fzsum2sub.1 $e |- ( i = ( k - j ) -> A = B ) $.
    fzsum2sub.2 $e |- ( ( ph /\ i e. ( ZZ>= ` -u j ) /\ j e. ( 1 ... N ) )
      -> A e. CC ) $.
    fzsum2sub.3 $e |- ( ( ( ph /\ j e. ( 1 ... N ) )
      /\ k e. ( ( ( M + j ) + 1 ) ... ( M + N ) ) ) -> B = 0 ) $.
    fzsum2sub.4 $e |- ( ( ( ph /\ j e. ( 1 ... N ) ) /\ k e. ( 0 ..^ j ) )
      -> B = 0 ) $.
    $( Lemma for ~ breprexp - Re-index a double sum, using difference of the
       initial indices.  (Contributed by Thierry Arnoux, 7-Dec-2021.) $)
    fsum2dsub $p |- ( ph -> sum_ i e. ( 0 ... M ) sum_ j e. ( 1 ... N ) A
      = sum_ k e. ( 0 ... ( M + N ) ) sum_ j e. ( 1 ... N ) B ) $=
      ( co cc0 csu caddc wcel adantr c1 cfz cv wa simpr elfzelzd 0zd nn0zd cneg
      cz cuz cfv cc simpll wss cn0 cn fz1ssnn nnssnn0 sstri nn0uz eleqtrdi neg0
      sselid uzneg eqeltrrid 3syl fzssuz sstrdi sselda syl3anc fsumshft clt wbr
      fzss1 cin c0 wceq nnnn0d nn0addcld nn0red ltp1d fzdisj syl cun zaddcld cr
      cle nnred nn0addge2 syl2anc elfzle2 leadd2dd elfzd fzsplit fzfid fz2ssnn0
      adantl sseldd cmin eleq1d simplr an32s ralrimiva nnsscn nn0cnd negsubdi2d
      wral eluzmn eqeltrrd rspcdva fsumsplit zcnd addlidd oveq1d eqcomd sumeq1d
      syl21anc sumeq2dv cfn fzfi sumz olcs ax-mp eqtrdi oveq12d elfzuz3 eluzadd
      zsscn addcomd fveq2d fsumcl 3eqtrrd cfzo zred letrd 3eqtr4d eqtrd fsumcom
      fzval3 3eltr3d fzss2 eleqtrd addridd ineq2d fzodisj peano2zd lep1d uneq2d
      nn0ge0d fzosplit simpl adantrl fz0ssnn0 simprl anass1rs anasss ancom2s
      fzofi ) AUAHUBOZPGUBOZBDQZEQUUTPGHROZUBOZCFQZEQUVAUUTBEQDQUVDUUTCEQFQAUUT
      UVBUVEEAEUCZUUTSZUDZUVBPUVFROZGUVFROZUBOZCFQZUVEUVHBCDFUVFPGUVHUVFUAHAUVG
      UEZUFZUVHUGZAGUJSZUVGAGIUHZTZUVHDUCZUVASZUDAUVSUVFUIZUKULZSZUVGBUMSZAUVGU
      VTUNUVHUVAUWBUVSUVHUVAUWAGUBOZUWBUVHUVFPUKULZSZPUWBSUVAUWEUOUVHUVFUPUWFUV
      HUUTUPUVFUUTUQUPHURZUSUTZUVMVDVAVBUWGPPUIUWBVCPUVFVEVFPUWAGVOVGUWAGVHVIVJ
      UVHUVGUVTUVMTLVKZKVLUVHUVLUVFUVCUBOZCFQZUVEUVHUWLUVFUVJUBOZCFQZUVJUAROZUV
      CUBOZCFQZROUVLPROUVLUVHUWMUWPCUWKFUVHUVJUWOVMVNUWMUWPVPVQVRUVHUVJUVHUVJUV
      HGUVFAGUPSZUVGITZUVHUVFUVHUUTUQUVFUWHUVMVDZVSZVTZWAWBUVFUVJUWOUVCWCWDUVHU
      VJUWKSUWKUWMUWPWEVRUVHUVJUVFUVCUVNAUVCUJSZUVGAGHUVQAHJUHWFTZUVHUVJUXBUHUV
      HUVFWGSUWRUVFUVJWHVNUVHUVFUWTWIZUWSUVFGWJWKUVHUVFHGUXEAHWGSZUVGAHJWAZTZUV
      HGUWSWAUVGUVFHWHVNAUVFUAHWLWRZWMWNUVJUVFUVCWOWDUVHUVFUVCWPZUVHFUCZUWKSZUD
      ZAUVGUXKUPSZCUMSZAUVGUXLUNUVHUVGUXLUVMTZUXMUWKUPUXKUXMUVFUPSUWKUPUOUXMUUT
      UPUVFUWIUXPVDUVFUVCWQWDUVHUXLUEWSZUVHUXNUDZUWDUXODUWBUXKUVFWTOZUVSUXSVRBC
      UMKXAUVHUWDDUWBXHUXNUVHUWDDUWBAUWCUVGUWDAUWCUDZUVGUDAUWCUVGUWDAUWCUVGUNAU
      WCUVGXBUXTUVGUELVKXCXDTUXRUVFUXKWTOZUIZUXSUWBUXRUVFUXKUXRUUTUMUVFUUTUQUMU
      WHXEUTAUVGUXNXBZVDUXRUXKUVHUXNUEZXFXGUXRUVFUYAUKULSZUYBUWBSUXRUVFUJSUXNUY
      EUXRUVFUAHUYCUFUYDUVFUXKXIWKUYAUVFVEWDXJXKZXRZXLUVHUWNUVLUWQPRUVHUWMUVKCF
      UVHUVKUWMUVHUVIUVFUVJUBUVHUVFUVHUVFUVNXMZXNXOZXPXQUVHUWQUWPPFQZPUVHUWPCPF
      MXSUWPXTSZUYJPVRZUWOUVCYAUWPUWFUOUYKUYLUWPFPYBYCYDYEYFUVHUVLUVHUVKCFUVHUV
      IUVJWPUVHUXKUVKSZUDZAUVGUXNUXOAUVGUYMUNZUVHUVGUYMUVMTZUYNAUVGUXLUXNUYOUYP
      UYNUWMUWKUXKUYNUVCUVJUKULZSZUWMUWKUOUVHUYRUYMUVHHGROZUVFGROZUKULZUVCUYQUV
      HHUVFUKULSZUVPUYSVUASUVGVUBAUVFUAHYGWRUVRGUVFHYHWKUVHHGAHUMSUVGAHJXFTUVHU
      JUMGYIUVRVDZYJUVHUYTUVJUKUVHUVFGUYHVUCYJYKUUATUVJUVFUVCUUBWDUYNUXKUVKUWMU
      VHUYMUEUVHUVKUWMVRUYMUYITUUCWSUXQXRUYFXRYLUUDYMUVHUVEPUVFYNOZCFQZUWLROPUW
      LROUWLUVHVUDUWKCUVDFUVHVUDUWKVPVUDUVFUVCUAROZYNOZVPVQUVHUWKVUGVUDUVHUXCUW
      KVUGVRUXDUVFUVCYTWDZUUEPUVFVUFUUFYEUVHPVUFYNOZVUDVUGWEZUVDVUDUWKWEUVHUVFP
      VUFUBOSVUIVUJVRUVHUVFPVUFUVOUVHUVCUXDUUGZUVNUVHUVFUXAUUJUVHUVFHVUFUXEUXHU
      VHVUFVUKYOZUXIUVHHUVCVUFUXHUVHUVCUXDYOZVULAHUVCWHVNZUVGAUXFUWRVUNUXGIHGWJ
      WKTUVHUVCVUMUUHYPYPWNPVUFUVFUUKWDUVHUXCUVDVUIVRUXDPUVCYTWDUVHUWKVUGVUDVUH
      UUIYQAUVDXTSUVGAPUVCWPZTAUXKUVDSZUVGUXOAVUPUVGUDZUDZAUVGUXNUXOAVUQUULAUVG
      UVGVUPUVMUUMVURUVDUPUXKUVCUUNAVUPUVGUUOVDUYFXRZUUPXLUVHVUEPUWLRUVHVUEVUDP
      FQZPUVHVUDCPFNXSVUDXTSZVUTPVRZPUVFUUSVUDUWFUOVVAVVBVUDFPYBYCYDYEXOUVHUWLU
      VHUWKCFUXJUYGYLXNYMYRYRXSAUVAUUTBDEAPGWPAUAHWPZAUVGUVTUWDAUVGUVTUWDUWJUUQ
      UURYSAUVDUUTCFEVUOVVCVUSYSYQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Representations of a number as sums of integers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c repr $.

  $( Representations of a number as a sum of nonnegative integers. $)
  crepr $a class repr $.

  ${
    $d a b c m s $.
    $( The representations of a nonnegative ` m ` as the sum of ` s `
       nonnegative integers from a set ` b ` .  Cf.  Definition of [Nathanson]
       p. 123.  (Contributed by Thierry Arnoux, 1-Dec-2021.) $)
    df-repr $a |- repr = ( s e. NN0 |-> ( b e. ~P NN , m e. ZZ
      |-> { c e. ( b ^m ( 0 ..^ s ) ) |
        sum_ a e. ( 0 ..^ s ) ( c ` a ) = m } ) ) $.
  $}

  ${
    $d A b c m $.  $d M b c m $.  $d S a b c m s $.  $d ph b c m s $.
    reprval.a $e |- ( ph -> A C_ NN ) $.
    reprval.m $e |- ( ph -> M e. ZZ ) $.
    reprval.s $e |- ( ph -> S e. NN0 ) $.
    $( Value of the representations of ` M ` as the sum of ` S ` nonnegative
       integers in a given set ` A ` .  (Contributed by Thierry Arnoux,
       1-Dec-2021.) $)
    reprval $p |- ( ph -> ( A ( repr ` S ) M ) = { c e. ( A ^m ( 0 ..^ S ) ) |
      sum_ a e. ( 0 ..^ S ) ( c ` a ) = M } ) $=
      ( vb vm vs cn cz cc0 co cv wceq cmap cvv cpw cfzo cfv csu crab crepr cmpo
      cn0 df-repr oveq2 oveq2d sumeq1d eqeq1d rabeqbidv mpoeq3dv wcel nnex pwex
      zex mpoex a1i fvmptd3 simprl oveq1d simprr eqeq2d ssexd elpwd ovex ovmpod
      wa rabex ) AJKBDMUAZNOCUBPZEQFQUCZEUDZKQZRZFJQZVNSPZUEZVPDRZFBVNSPZUEZCUF
      UCTALCJKVMNOLQZUBPZVOEUDZVQRZFVSWFSPZUEZUGJKVMNWAUGZUHUFTKLEJFUIWECRZJKVM
      NWJWAWLWHVRFWIVTWLWFVNVSSWECOUBUJZUKWLWGVPVQWLWFVNVOEWMULUMUNUOIWKTUPAJKV
      MNWAMUQURUSUTVAVBAVSBRZVQDRZVKVKZVRWBFVTWCWPVSBVNSAWNWOVCVDWPVQDVPAWNWOVE
      VFUNABMTABMTMTUPAUQVAGVGGVHHWDTUPAWBFWCBVNSVIVLVAVJ $.

    $( There is exactly one representation with no elements (an empty sum),
       only for ` M = 0 ` .  (Contributed by Thierry Arnoux, 2-Dec-2021.) $)
    repr0 $p |- ( ph -> ( A ( repr ` 0 ) M ) = if ( M = 0 , { (/) } , (/) ) )
      $=
      ( va vc cc0 cfv co wceq cmap c0 wcel a1i wa cvv eqcomd crepr cfzo cv crab
      csu csn cif cn0 0nn0 reprval fzo0 sumeq1i sum0 eqtri eqeq1i 0ex snid nnex
      wb ssexd mapdm0 syl eleqtrrid oveq2i eleqtrrdi adantr simpr eqtrid eleq2d
      cn biimpa elsni ad4ant13 rabeqsnd wn wral simplr neqned eqnetrd ralrimiva
      necomd neneqd rabeq0 sylibr ifeqda eqtr4d ) ABDJUAKLJJUBLZHUCIUCZKZHUEZDM
      ZIBWGNLZUDZDJMZOUFZOUGABJDHIEFJUHPAUIQUJAWNWOOWMAWNRZWMWOWPWKJDMZIWLOWKWQ
      USWHOMZWJJDWJOWIHUEJWGOWIHJUKZULWIHUMUNZUOQAOWLPWNAOBONLZWLAOWOXAOUPUQABS
      PXAWOMABVJSVJSPAURQEUTBSVAVBZVCWGOBNWSVDZVEVFWPDJAWNVGTAWHWLPZWRWNWKAXDRW
      HWOPZWRAXDXEAWLWOWHAWLXAWOXCXBVHVIVKWHOVLVBVMVNTAWNVOZRZWMOXGWKVOZIWLVPWM
      OMXGXHIWLXGXDRZWJDXIWJJDWJJMXIWTQXIDJXIDJAXFXDVQVRWAVSWBVTWKIWLWCWDTWEWF
      $.

    ${
      $d C a c $.
      reprf.c $e |- ( ph -> C e. ( A ( repr ` S ) M ) ) $.
      $( Members of the representation of ` M ` as the sum of ` S ` nonnegative
         integers from set ` A ` as functions.  (Contributed by Thierry Arnoux,
         5-Dec-2021.) $)
      reprf $p |- ( ph -> C : ( 0 ..^ S ) --> A ) $=
        ( va vc cc0 cfzo co cv cfv csu wceq cmap wcel crab crepr reprval elrabi
        wf eleqtrd elmapi 3syl ) ACLDMNZJOKOPJQERZKBUISNZUAZTCUKTUIBCUEACBEDUBP
        NULIABDEJKFGHUCUFUJKCUKUDCBUIUGUH $.

      $( Sums of values of the members of the representation of ` M ` equal
         ` M ` .  (Contributed by Thierry Arnoux, 5-Dec-2021.) $)
      reprsum $p |- ( ph -> sum_ a e. ( 0 ..^ S ) ( C ` a ) = M ) $=
        ( vc cc0 cfzo co cmap wcel cv cfv csu wceq crab crepr reprval sumeq2sdv
        wa eleqtrd fveq1 eqeq1d elrab sylib simprd ) ACBLDMNZONZPZULFQZCRZFSZET
        ZACULUOKQZRZFSZETZKUMUAZPUNURUEACBEDUBRNVCJABDEFKGHIUCUFVBURKCUMUSCTZVA
        UQEVDULUTUPFUOUSCUGUDUHUIUJUK $.

      $d X a $.  $d ph a $.
      reprle.x $e |- ( ph -> X e. ( 0 ..^ S ) ) $.
      $( Upper bound to the terms in the representations of ` M ` as the sum of
         ` S ` nonnegative integers from set ` A ` .  (Contributed by Thierry
         Arnoux, 27-Dec-2021.) $)
      reprle $p |- ( ph -> ( C ` X ) <_ M ) $=
        ( va cc0 cfzo co cv cfv fveq2 wcel cn cfn fzofi reprsum wa adantr reprf
        a1i wss ffvelcdmda sseldd nnrpd fsumub ) AMDNOZLPZCQZEFCQLFUNFCRUMUASAM
        DUBUGABCDELGHIJUCAUNUMSZUDZUOUQBTUOABTUHUPGUEAUMBUNCABCDEGHIJUFUIUJUKKU
        L $.
    $}

    ${
      $d A a d e $.  $d F e $.  $d M a d e $.  $d S a b d c e $.
      $d a d e ph $.
      reprsuc.f $e |- F = ( c e. ( A ( repr ` S ) ( M - b ) )
        |-> ( c u. { <. S , b >. } ) ) $.
      $( Express the representations recursively.  (Contributed by Thierry
         Arnoux, 5-Dec-2021.) $)
      reprsuc $p |- ( ph -> ( A ( repr ` ( S + 1 ) ) M ) = U_ b e. A ran F ) $=
        ( va co cfv wceq wcel wa ad2antrr adantr cc ve vd c1 caddc crepr cc0 cv
        cfzo csu cmap crab crn ciun cn0 1nn0 a1i nn0addcld reprval wrex cop csn
        cun wf simplr elmapi syl fzonn0p1 ffvelcdmd simpr oveq2d wb opeq2 sneqd
        cmin uneq2d eqeq2d adantl rexeqbidv cres wss fzossfzop1 fssresd cn nnex
        cvv ssexd cfn fzofi elexi elmapg sylancl mpbird nnsscn sstrd ffvelcdmda
        sseldd fsumcl pncand nfcv wn fzonel sselda fveq2 fsumsplitsn fzosplitsn
        nfv cuz nn0uz eleq2s sumeq1d fvresd oveq1d 3eqtr4d eqtr3d jca sumeq2sdv
        sumeq2dv fveq1 eqeq1d elrab sylibr nnssz sstrdi zsubcld eleqtrrd uneq1d
        cdif wfn ffnd fnsnsplit syl2anc eleqtrdi fzodif2 reseq2d eqtrd rspcedvd
        cz fveq1d syl112anc 3eqtrd anasss reprf fsnd fzodisjsn fun2d feq2d ovex
        cin eqeltrd ad4antr feq1d elun1 ad3antrrr fvun1 ralrimiva sumeq2d snidg
        c0 reprsum fvun2 fvsng oveq12d sselid eqeltrrd npcand r19.29ffa impbida
        zsscn vex snex unex elrnmpti rexbii bitr4di cbvrabv eliun 3bitr4g eqrdv
        reqabi ) ABECUCUDMZUENMUFUVTUHMZLUGZGUGZNZLUIZEOZGBUWAUJMZUKZFBDULZUMZA
        BUVTELGHIACUCJUCUNPAUOUPUQURAUAUWHUWJAUAUGZUWGPZUWAUWBUWKNZLUIZEOZQZUWK
        UWIPZFBUSZUWKUWHPUWKUWJPAUWPUWKUWCCFUGZUTZVAZVBZOZGBEUWSVNMZCUENZMZUSZF
        BUSZUWRAUWPUXHAUWLUWOUXHAUWLQZUWOQZUXGUWKUWCCCUWKNZUTZVAZVBZOZGBEUXKVNM
        ZUXEMZUSFUXKBUXJUWABCUWKUXJUWLUWABUWKVCZAUWLUWOVDUWKBUWAVEZVFZUXJCUNPZC
        UWAPZAUYAUWLUWOJRZCVGZVFZVHZUXJUWSUXKOZQZUXCUXOGUXFUXQUYHUXDUXPBUXEUYHU
        WSUXKEVNUXJUYGVIVJVJUYGUXCUXOVKUXJUYGUXBUXNUWKUYGUXAUXMUWCUYGUWTUXLUWSU
        XKCVLVMVOVPVQVRUXJUXOUWKUWKUFCUHMZVSZUXMVBZOGUYJUXQUXJUYJUYIUWBUBUGZNZL
        UIZUXPOZUBBUYIUJMZUKZUXQUXJUYJUYPPZUYIUWBUYJNZLUIZUXPOZQUYJUYQPUXJUYRVU
        AUXJUYRUYIBUYJVCZUXIVUBUWOUXIUWABUYIUWKUWLUXRAUXSVQZUXIUYAUYIUWAVTAUYAU
        WLJSZCWAVFZWBZSAUYRVUBVKZUWLUWOABWEPZUYIWEPVUGABWCWEWCWEPAWDUPHWFZUYIWG
        UFCWHZWIBUYIUYJWEWEWJWKRWLUXJUYTUXKUDMZUXKVNMUYTUXPUXJUYTUXKUXIUYTTPUWO
        UXIUYIUYSLUYIWGPZUXIVUJUPZUXIUWBUYIPZQZBTUYSABTVTZUWLVUNABWCTHWCTVTAWMU
        PWNZRZUXIUYIBUWBUYJVUFWOWPWQSUXIUXKTPUWOUXIBTUXKAVUPUWLVUQSUXIUWABCUWKV
        UCUXIUYAUYBVUDUYDVFVHWPZSWRUXJVUKEUXKVNUXJUWNVUKEUXIUWNVUKOUWOUXIUYICVA
        ZVBZUWMLUIZUYIUWMLUIZUXKUDMZUWNVUKUXIUYICUWMUXKLUNUXILXFLUXKWSZVUMVUDCU
        YIPWTZUXIUFCXAZUPVUOBTUWMVURVUOUWABUWBUWKUXIUXRVUNVUCSUXIUYIUWAUWBVUEXB
        VHWPUWBCUWKXCZVUSXDUXIUWAVVAUWMLUXIUYAUWAVVAOZVUDVVICUFXGNZUNUFCXEXHXIZ
        VFXJUXIUYTVVCUXKUDUXIUYIUYSUWMLVUOUWBUYIUWKUXIVUNVIXKXQXLXMSUXIUWOVIXNX
        LXNXOUYOVUAUBUYJUYPUYLUYJOZUYNUYTUXPVVLUYIUYMUYSLUWBUYLUYJXRXPXSXTYAUXJ
        BCUXPLUBABWCVTZUWLUWOHRUXJEUXKAEYQPZUWLUWOIRUXJBYQUXKABYQVTUWLUWOABWCYQ
        HYBYCZRUYFWPYDUYCURYEUXJUWCUYJOZQZUXNUYKUWKVVQUWCUYJUXMUXJVVPVIYFVPUXJU
        WKUWKUWAVUTYGZVSZUXMVBZUYKUXJUWKUWAYHUYBUWKVVTOUXJUWABUWKUXTYIUYEUWAUWK
        CYJYKUXJVVSUYJUXMUXJVVRUYIUWKUXJCVVJPVVRUYIOUXJCUNVVJUYCXHYLUFCYMVFYNYF
        YOYPYPUUAAUXCUWPFGBUXFAUWSBPZQZUWCUXFPZQZUXCQZUWLUWOVWEUWKUXBUWGVWDUXCV
        IZVWDUXBUWGPZUXCVWDVWGUWABUXBVCZVWDVWHVVABUXBVCVWDUYIVUTBUWCUXAVWDBUWCC
        UXDVWBVVMVWCAVVMVWAHSSZVWBUXDYQPZVWCVWBEUWSAVVNVWAISZABYQUWSVVOXBYDSZVW
        BUYAVWCAUYAVWAJSSZVWBVWCVIZUUBZVWDCUWSUNBVWMAVWAVWCVDZUUCZUYIVUTUUHUURO
        ZVWDUFCUUDZUPUUEVWDUWAVVABUXBVWDUYAVVIVWMVVKVFZUUFWLZAVWGVWHVKZVWAVWCAV
        UHUWAWEPVXBVUIUFUVTUHUUGBUWAUXBWEWEWJWKRWLSUUIVWEUWNVVBVVDEVWEUWAVVAUWM
        LVWDVVIUXCVWTSXJVWEUYICUWMUXKLUNVWELXFVVEVULVWEVUJUPVWDUYAUXCVWMSZVVFVW
        EVVGUPVWEVUNQZBTUWMAVUPVWAVWCUXCVUNVUQUUJVXDUWABUWBUWKVWEUXRVUNVWEUXRVW
        HVWDVWHUXCVXASVWEUWABUWKUXBVWFUUKWLZSVXDUWBVVAUWAVXDVUNUWBVVAPVWEVUNVIZ
        UWBUYIVUTUULVFVWDVVIUXCVUNVWTRYEVHWPVVHVWEBTUXKAVUPVWAVWCUXCVUQUUMVWEUW
        ABCUWKVXEVWEUYAUYBVXCUYDVFVHWPZXDVWEVVDUXDUWSUDMEVWEVVCUXDUXKUWSUDVWEVV
        CUYIUWDLUIUXDVWEUYIUWMUWDLVWEUWMUWDOLUYIVXDUWMUWBUXBNZUWDVXDUWBUWKUXBVW
        DUXCVUNVDYRVXDUWCUYIYHZUXAVUTYHZVWRVUNVXHUWDOVWDVXIUXCVUNVWDUYIBUWCVWOY
        IZRVWDVXJUXCVUNVWDVUTBUXAVWQYIZRVWRVXDVWSUPVXFUYIVUTUWCUXAUWBUUNYSYOUUO
        UUPVWEBUWCCUXDLVWDVVMUXCVWISVWDVWJUXCVWLSVXCVWDVWCUXCVWNSUUSYOVWEUXKCUX
        BNZCUXANZUWSVWECUWKUXBVWFYRVWEVXIVXJVWRCVUTPZVXMVXNOVWDVXIUXCVXKSVWDVXJ
        UXCVXLSVWRVWEVWSUPVWEUYAVXOVXCCUNUUQVFUYIVUTUWCUXACUUTYSVWEUYAVWAVXNUWS
        OVXCVWDVWAUXCVWPSCUWSUNBUVAYKYTZUVBVWEEUWSVWEYQTEUVHVWBVVNVWCUXCVWKRUVC
        VWEUXKUWSTVXPVXGUVDUVEYOYTXOUVFUVGUWQUXGFBGUXFUXBUWKDKUWCUXAGUVIUWTUVJU
        VKUVLUVMUVNUWOUAUWHUWGUWFUWOGUAUWGUWCUWKOZUWEUWNEVXQUWAUWDUWMLUWBUWCUWK
        XRXPXSUVOUVSFUWKBUWIUVPUVQUVRYO $.
    $}

    ${
      reprfi.1 $e |- ( ph -> A e. Fin ) $.
      $( Bounded representations are finite sets.  (Contributed by Thierry
         Arnoux, 7-Dec-2021.) $)
      reprfi $p |- ( ph -> ( A ( repr ` S ) M ) e. Fin ) $=
        ( va vc crepr cfv co cc0 cfzo cv csu wceq cfn wcel cmap reprval sylancl
        crab fzofi mapfi rabfi syl eqeltrd ) ABDCKLMNCOMZIPJPLIQDRZJBUJUAMZUDZS
        ABCDIJEFGUBAULSTZUMSTABSTUJSTUNHNCUEBUJUFUCUKJULUGUHUI $.
    $}

    ${
      $d B c $.
      reprss.1 $e |- ( ph -> B C_ A ) $.
      $( Representations with terms in a subset.  (Contributed by Thierry
         Arnoux, 11-Dec-2021.) $)
      reprss $p |- ( ph -> ( B ( repr ` S ) M ) C_ ( A ( repr ` S ) M ) ) $=
        ( va vc co cv cfv cmap crab wcel cvv wss cn cc0 cfzo csu wceq crepr a1i
        nnex ssexd mapss syl2anc sselda adantrr rabss3d sstrd reprval 3sstr4d )
        AUADUBLZJMKMZNJUCEUDZKCUQOLZPUSKBUQOLZPCEDUENZLBEVBLAUSKUTVAAURUTQURVAQ
        USAUTVAURABRQCBSUTVASABTRTRQAUGUFFUHICBUQRUIUJUKULUMACDEJKACBTIFUNGHUOA
        BDEJKFGHUOUP $.
    $}

    ${
      $d B c $.
      $( Representations with term in an intersection.  (Contributed by Thierry
         Arnoux, 11-Dec-2021.) $)
      reprinrn $p |- ( ph -> ( c e. ( ( A i^i B ) ( repr ` S ) M )
        <-> ( c e. ( A ( repr ` S ) M ) /\ ran c C_ B ) ) ) $=
        ( va cv cc0 co wcel wa wf cvv cn anbi1d bitrdi cin cfzo cfv csu crn wss
        cmap wceq crepr fin wfn df-f adantl biantrurd bicomd bitrid pm5.32da wb
        ffn nnex a1i ssexd inex1g ovex elmapg sylancl 3bitr4d crab inss1 sstrid
        syl reprval eleq2d rabid an32 ) AFKZBCUAZLDUBMZUGMZNZVRJKVPUCJUDEUHZOZV
        PBVRUGMZNZVPUECUFZOZWAOZVPVQEDUIUCZMZNZVPBEWHMZNZWEOZAVTWFWAAVRVQVPPZVR
        BVPPZWEOZVTWFWNWOVRCVPPZOAWPVRBCVPUJAWOWQWEWQVPVRUKZWEOZAWOOZWEVRCVPULW
        TWEWSWTWRWEWOWRAVRBVPUSUMUNUOUPUQUPAVQQNZVRQNZVTWNURABQNZXAABRQRQNAUTVA
        GVBZBCQVCVKLDUBVDZVQVRVPQQVEVFAWDWOWEAXCXBWDWOURXDXEBVRVPQQVEVFSVGSAWJV
        PWAFVSVHZNWBAWIXFVPAVQDEJFAVQBRBCVIGVJHIVLVMWAFVSVNTAWMWDWAOZWEOWGAWLXG
        WEAWLVPWAFWCVHZNXGAWKXHVPABDEJFGHIVLVMWAFWCVNTSWDWAWEVOTVG $.
    $}

    ${
      $d A a $.  $d S a $.  $d ph a $.
      reprlt.1 $e |- ( ph -> M < S ) $.
      $( There are no representations of ` M ` with more than ` M ` terms.
         Remark of [Nathanson] p. 123.  (Contributed by Thierry Arnoux,
         7-Dec-2021.) $)
      reprlt $p |- ( ph -> ( A ( repr ` S ) M ) = (/) ) $=
        ( va vc cfv co wceq wcel cr adantr a1i cn cvv c1 crepr cc0 cfzo cv cmap
        csu crab c0 reprval wn wral wa zred nn0red cfn fzofi wss sstrd ad2antrr
        nnssre nnex ssexd elexi simpr elmapg biimpa syl21anc ffvelcdmd fsumrecl
        wf sseldd clt wbr cle chash cmul cc ax-1cn fsumconst mp2an hashcl ax-mp
        cn0 nn0cni mulridi eqtri hashfzo0 syl eqtrid 1red nnge1 fsumle eqbrtrrd
        ltletrd ltned necomd neneqd ralrimiva rabeq0 sylibr eqtrd ) ABDCUAKLUBC
        UCLZIUDZJUDZKZIUFZDMZJBXBUELZUGZUHABCDIJEFGUIAXGUJZJXHUKXIUHMAXJJXHAXDX
        HNZULZXFDXLDXFXLDXFADONXKADFUMPZXLDCXFXMACONXKACGUNPXLXBXEIXBUONZXLUBCU
        PZQZXLXCXBNZULZBOXEABOUQXKXQABROEROUQAUTQURUSXRXBBXCXDXLXBBXDVJZXQXLBSN
        ZXBSNZXKXSAXTXKABRSRSNAVAQEVBPYAXLXBUOXOVCQAXKVDXTYAULXKXSBXBXDSSVEVFVG
        PXLXQVDVHZVKZVIADCVLVMXKHPXLXBTIUFZCXFVNAYDCMXKAYDXBVOKZCYDYETVPLZYEXNT
        VQNYDYFMXOVRXBTIVSVTYEYEXNYEWCNXOXBWAWBWDWEWFACWCNYECMGCWGWHWIPXLXBTXEI
        XPXRWJYCXRXERNTXEVNVMXRBRXEABRUQXKXQEUSYBVKXEWKWHWLWMWNWOWPWQWRXGJXHWSW
        TXA $.
    $}

    ${
      $d A a $.  $d B a c $.  $d M a $.  $d S a $.  $d ph a $.
      hashreprin.b $e |- ( ph -> B e. Fin ) $.
      hashreprin.1 $e |- ( ph -> B C_ NN ) $.
      $( Express a sum of representations over an intersection using a product
         of the indicator function.  (Contributed by Thierry Arnoux,
         11-Dec-2021.) $)
      hashreprin $p |- ( ph -> ( # ` ( ( A i^i B ) ( repr ` S ) M ) )
         = sum_ c e. ( B ( repr ` S ) M )
             prod_ a e. ( 0 ..^ S ) ( ( ( _Ind ` NN ) ` A ) ` ( c ` a ) ) ) $=
        ( cfv co c1 cc0 cn wcel wss adantr cin crepr chash cmul cfzo cind cprod
        csu cv cfn cc wceq reprfi inss2 a1i reprss ssfid 1cnd fsumconst syl2anc
        cif wral cuz wo ralrimivw olcd sumss2 syl21anc wa crn wb reprinrn incom
        wi oveq1i eleq2i bibi1i imbi2i mpbi baibd ifbid cvv nnex r19.21bi fzofi
        cz cn0 simpr reprf prodindf eqtr4d sumeq2dv eqtrd hashcl nn0cnd mulridd
        fssd syl 3eqtr3rd ) ABCUAZEDUBMZNZOGUHZXBUCMZOUDNZCEXANZPDUENZFUIGUIZMB
        QUFMMMFUGZGUHZXDAXBUJRZOUKRZXCXEULAXFXBACDELIJKUMZACWTDELIJWTCSABCUNUOU
        PZUQZAURZXBOGUSUTAXCXFXHXBRZOPVAZGUHZXJAXBXFSXLGXBVBXFPVCMSZXFUJRZVDXCX
        SULXNAXLGXBXPVEAYAXTXMVFXBXFOGPVGVHAXFXRXIGAXHXFRZVIZXRXHVJBSZOPVAXIYCX
        QYDOPAXQYBYDAXHCBUAZEXANZRZYBYDVIZVKZVNAXQYHVKZVNACBDEGLIJVLYIYJAYGXQYH
        YFXBXHYEWTEXACBVMVOVPVQVRVSVTWAYCXGBFXHQWBAQWBRZGXFAYKGXFYKAWCUOVEWDXGU
        JRYCPDWEUOABQSYBHTYCXGCQXHYCCXHDEACQSYBLTZAEWFRYBITADWGRYBJTAYBWHWIYLWQ
        WJWKWLWMAXDAXDAXKXDWGRXOXBWNWRWOWPWS $.
    $}
  $}

  ${
    $d A a c $.  $d M c $.  $d N a $.  $d S a c $.  $d a c ph $.
    reprgt.n $e |- ( ph -> N e. NN0 ) $.
    reprgt.a $e |- ( ph -> A C_ ( 1 ... N ) ) $.
    reprgt.m $e |- ( ph -> M e. ZZ ) $.
    reprgt.s $e |- ( ph -> S e. NN0 ) $.
    reprgt.1 $e |- ( ph -> ( S x. N ) < M ) $.
    $( There are no representations of more than ` ( S x. N ) ` with only ` S `
       terms bounded by ` N ` .  Remark of [Nathanson] p. 123.  (Contributed by
       Thierry Arnoux, 7-Dec-2021.) $)
    reprgt $p |- ( ph -> ( A ( repr ` S ) M ) = (/) ) $=
      ( va vc cfv co wceq c1 wcel cr cvv adantr crepr cc0 cfzo cv csu cmap crab
      c0 cfz cn fz1ssnn sstrdi reprval wn wa cfn fzofi a1i wss nnssre ralrimivw
      wral r19.21bi wf ovex ssexd elexi elmapg biimpa syl21anc ffvelcdmd sseldd
      simpr fsumrecl cmul nn0red remulcld cle ad2antrr wbr elfzle2 fsumle chash
      zred syl cc recnd fsumconst sylancr cn0 hashfzo0 oveq1d eqtrd breqtrd clt
      lelttrd ltned neneqd ralrimiva rabeq0 sylibr ) ABDCUAMNUBCUCNZKUDZLUDZMZK
      UEZDOZLBXBUFNZUGZUHABCDKLABPEUINZUJGEUKULZHIUMAXGUNZLXHVBXIUHOAXLLXHAXDXH
      QZUOZXFDXNXFDXNXBXEKXBUPQZXNUBCUQZURZXNXCXBQZUOZBRXEXNBRUSZKXBAXTKXBVBZLX
      HAYALXHAXTKXBABUJRXKUTULVAVAVCVCXSXBBXCXDXNXBBXDVDZXRXNBSQZXBSQZXMYBAYCXM
      ABXJSXJSQAPEUIVEURGVFTYDXNXBUPXPVGURAXMVMYCYDUOXMYBBXBXDSSVHVIVJTXNXRVMVK
      ZVLZVNZXNXFCEVONZDYGXNCEACRQXMACIVPTAERQZXMAEFVPZTVQADRQXMADHWDTXNXFXBEKU
      EZYHVRXNXBXEEKXQYFAYIXMXRYJVSXSXEXJQXEEVRVTXSBXJXEABXJUSXMXRGVSYEVLXEPEWA
      WEWBAYKYHOXMAYKXBWCMZEVONZYHAXOEWFQYKYMOXPAEYJWGXBEKWHWIAYLCEVOACWJQYLCOI
      CWKWEWLWMTWNAYHDWOVTXMJTWPWQWRWSXGLXHWTXAWM $.
  $}

  ${
    $d A a b c $.  $d N a b c $.  $d S a b c $.  $d a b c ph $.
    reprinfz1.n $e |- ( ph -> N e. NN0 ) $.
    reprinfz1.s $e |- ( ph -> S e. NN0 ) $.
    reprinfz1.a $e |- ( ph -> A C_ NN ) $.
    $( For the representation of ` N ` , it is sufficient to consider
       nonnegative integers up to ` N ` .  Remark of [Nathanson] p. 123
       (Contributed by Thierry Arnoux, 13-Dec-2021.) $)
    reprinfz1 $p |- ( ph ->
      ( A ( repr ` S ) N ) = ( ( A i^i ( 1 ... N ) ) ( repr ` S ) N ) ) $=
      ( va vc vb cfv co cc0 wcel wa cvv cn wn ad3antrrr sylibr crepr c1 cfz cin
      cfzo cv csu wceq cmap crab wf wb nnex a1i ssexd ovex elmapg biimpa adantr
      sylancl wfn wral elmapfn ad2antlr wrex simplr wne cr nn0red simpllr mpbid
      wss ffvelcdmd sseldd nnred cfn fzofi ad4antr ffvelcdmda clt wbr cle simpr
      fsumrecl cz nn0zd fznn syl biantrurd bitr4d notbid ltnled mpbird cc recnd
      csn fveq2 sumsn syl2anc cn0 nnnn0d nn0ge0 snssi fsumless eqbrtrrd ltletrd
      ltned necomd r19.29an neneqd adantlr pm2.65da dfral2 eleq1d jca ffnfv fin
      cbvralvw inex2 elmap anasss rabss3d reprval inss1 sstrd 3sstr4d reprss
      eqssd ) ABDCUAKZLZBUBDUCLZUDZDYILZAMCUELZHUFZIUFZKZHUGZDUHZIBYNUILZUJYSIY
      LYNUILZUJYJYMAYSIYTUUAAYPYTNZYSYPUUANZAUUBOZYSOZYNYLYPUKZUUCUUEYNBYPUKZYN
      YKYPUKZOUUFUUEUUGUUHUUDUUGYSAUUBUUGABPNYNPNUUBUUGULZABQPQPNAUMUNGUOMCUEUP
      ZBYNYPPPUQUTZURUSUUEYPYNVAZYQYKNZHYNVBZOUUHUUEUULUUNUUBUULAYSYPBYNVCVDUUE
      JUFZYPKZYKNZJYNVBZUUNUUEUUQRZJYNVEZRUURUUEUUTYSUUDYSUUTVFUUDUUTYSRYSUUDUU
      TOYRDUUDUUSYRDVGJYNUUDUUOYNNZOZUUSOZDYRUVCDYRADVHNUUBUVAUUSADEVISZUVCDUUP
      YRUVDUVCUUPUVCBQUUPABQVLZUUBUVAUUSGSUVCYNBUUOYPUVCUUBUUGAUUBUVAUUSVJAUUIU
      UBUVAUUSUUKSVKZUUDUVAUUSVFZVMVNZVOZUVCYNYQHYNVPNUVCMCVQUNZUVCYOYNNZOZYQUV
      LBQYQAUVEUUBUVAUUSUVKGVRUVCYNBYOYPUVFVSVNZVOZWDUVCDUUPVTWAUUPDWBWAZRZUVCU
      USUVPUVBUUSWCUVCUUQUVOUVCUUQUUPQNZUVOOZUVOUVCDWENZUUQUVRULAUVSUUBUVAUUSAD
      EWFZSUUPDWGWHUVCUVQUVOUVHWIWJWKVKUVCDUUPUVDUVIWLWMUVCUUOWPZYQHUGZUUPYRWBU
      VCUVAUUPWNNUWBUUPUHUVGUVCUUPUVIWOYQUUPHUUOYNYOUUOYPWQZWRWSUVCYNYQUWAHUVJU
      VNUVLYQWTNMYQWBWAUVLYQUVMXAYQXBWHUVAUWAYNVLUUDUUSUUOYNXCVDXDXEXFXGXHXIXJX
      KXLUUQJYNXMTUUMUUQHJYNYOUUOUHYQUUPYKUWCXNXRTXOHYNYKYPXPTXOYNBYKYPXQTYLYNY
      PYKBUBDUCUPXSUUJXTTYAYBABCDHIGUVTFYCAYLCDHIAYLBQYLBVLABYKYDUNZGYEUVTFYCYF
      ABYLCDGUVTFUWDYGYH $.

    $( Corollary of ~ reprinfz1 .  (Contributed by Thierry Arnoux,
       15-Dec-2021.) $)
    reprfi2 $p |- ( ph -> ( A ( repr ` S ) N ) e. Fin ) $=
      ( crepr cfv co c1 cfz cin cfn reprinfz1 cn wss inss2 fz1ssnn a1i eqeltrd
      sstri nn0zd wcel fzfi ssfid reprfi ) ABDCHIZJBKDLJZMZDUHJNABCDEFGOAUJCDUJ
      PQAUJUIPBUIRZDSUBTADEUCFAUIUJUINUDAKDUETUJUIQAUKTUFUGUA $.
  $}

  ${
    reprfz1.n $e |- ( ph -> N e. NN0 ) $.
    reprfz1.s $e |- ( ph -> S e. NN0 ) $.
    $( Corollary of ~ reprinfz1 .  (Contributed by Thierry Arnoux,
       14-Dec-2021.) $)
    reprfz1 $p |- ( ph ->
      ( NN ( repr ` S ) N ) = ( ( 1 ... N ) ( repr ` S ) N ) ) $=
      ( cn crepr cfv co c1 cfz cin ssidd reprinfz1 wceq fz1ssnn dfss mpbi incom
      wss eqtri oveq1i eqtr4di ) AFCBGHZIFJCKIZLZCUDIUECUDIAFBCDEAFMNUEUFCUDUEU
      EFLZUFUEFTUEUGOCPUEFQRUEFSUAUBUC $.
  $}

  ${
    $d A a c $.  $d M a c $.  $d S a c $.  $d a c ph $.
    hashrepr.a $e |- ( ph -> A C_ NN ) $.
    hashrepr.m $e |- ( ph -> M e. NN0 ) $.
    hashrepr.s $e |- ( ph -> S e. NN0 ) $.
    $( Develop the number of representations of an integer ` M ` as a sum of
       nonnegative integers in set ` A ` .  (Contributed by Thierry Arnoux,
       14-Dec-2021.) $)
    hashrepr $p |- ( ph -> ( # ` ( A ( repr ` S ) M ) )
       = sum_ c e. ( NN ( repr ` S ) M )
           prod_ a e. ( 0 ..^ S ) ( ( ( _Ind ` NN ) ` A ) ` ( c ` a ) ) ) $=
      ( c1 cfz co cin crepr cfv chash cc0 cv cn csu cfzo cind cprod nn0zd fzfid
      wss fz1ssnn a1i hashreprin reprinfz1 fveq2d reprfz1 sumeq1d 3eqtr4d ) ABJ
      DKLZMDCNOZLZPOUODUPLZQCUALERFROBSUBOOOEUCZFTBDUPLZPOSDUPLZUSFTABUOCDEFGAD
      HUDIAJDUEUOSUFADUGUHUIAUTUQPABCDHIGUJUKAVAURUSFACDHIULUMUN $.
  $}

  ${
    $d A a b c d $.  $d B c d $.  $d M a b c d $.  $d P a b c d $.
    $d S a b c d $.  $d T a b c d $.  $d X c $.  $d a b c d ph $.
    reprpmtf1o.s $e |- ( ph -> S e. NN ) $.
    reprpmtf1o.m $e |- ( ph -> M e. ZZ ) $.
    reprpmtf1o.a $e |- ( ph -> A C_ NN ) $.
    reprpmtf1o.x $e |- ( ph -> X e. ( 0 ..^ S ) ) $.
    reprpmtf1o.o $e |- O = { c e. ( A ( repr ` S ) M ) | -. ( c ` 0 ) e. B } $.
    reprpmtf1o.p $e |- P = { c e. ( A ( repr ` S ) M ) | -. ( c ` X ) e. B } $.
    reprpmtf1o.t $e |- T = if ( X = 0 , ( _I |` ( 0 ..^ S ) )
                                , ( ( pmTrsp ` ( 0 ..^ S ) ) ` { X , 0 } ) ) $.
    reprpmtf1o.f $e |- F = ( c e. P |-> ( c o. T ) ) $.
    $( Transposing ` 0 ` and ` X ` maps representations with a condition on the
       first index to transpositions with the same condition on the index
       ` X ` .  (Contributed by Thierry Arnoux, 27-Dec-2021.) $)
    reprpmtf1o $p |- ( ph -> F : P -1-1-onto-> O ) $=
      ( wcel va vd vb cc0 cfzo co cmap cv ccom cmpt cima cres wf1o wf1 wss eqid
      cvv ovexd nnex a1i ssexd lbfzo0 sylibr pmtridf1o fmptco1f1o f1of1 syl cfv
      cn csu wceq crab ssrab2 crepr ssrab3 nnnn0d reprval sseqtrd sselda sselid
      wa wn ex ssrdv f1ores syl2anc resmpt eqtr4di eqidd wrex vex elimampt wral
      simpr f1of ad2antrr fmpt adantr rspa eqeltrd fveq1d wfun cdm f1ofun f1odm
      wf eleqtrrd fvco adantlr eqtrd sumeq2dv fveq2 cfn fzofi cz cn0 ffvelcdmda
      reprf sseldd nncnd fsumf1o reprsum 3eqtr2d fveq1 sumeq2sdv elrab sylanbrc
      eqeq1d pmtridfv2 fveq2d eleqtrdi rabid sylib simprd eqneltrd jca r19.29an
      3syl eleq1d notbid ccnv f1ocnv fco wb elmapg mpbird f1ocnvfv imp syl21anc
      eleqtrrdi anasss coeq1d eqeq2d cid f1ococnv1 coeq2d fcoi1 eqtr2d rspcedvd
      adantrr coass impbida bitrd bitr4di eqrdv f1oeq123d mpbid ) ADKBUDEUEUFZU
      GUFZKUHZFUIZUJZDUKZUVLDULZUMZDIGUMAUVIUVIUVLUNZDUVIUOZUVOAUVIUVIUVLUMZUVP
      AUVIUVIUVHBFKUVHUVLUQUQUQUVIUPZUVSUVLUPZAUDEUEURZUWAABVIUQVIUQTAUSUTNVAZA
      UVHFUQJUDUWAOAEVITUDUVHTZLEVBVCZRVDZVEZUVIUVIUVLVFVGAKDUVIAUVJDTZUVJUVITZ
      AUWGWAZUVHUAUHZUVJVHZUAVJZHVKZKUVIVLZUVIUVJUWMKUVIVMADUWNUVJADBHEVNVHUFZU
      WNDUWOUOAJUVJVHZCTZWBZKUWODQVOUTZABEHUAKNMAELVPZVQZVRVSVTZWCWDZUVIUVIDUVL
      WEWFADDUVMIUVNGAUVNKDUVKUJZGAUVQUVNUXDVKUXCKUVIDUVKWGVGSWHADWIAUVMUDUVJVH
      ZCTZWBZKUWOVLZIAUBUVMUXHAUBUHZUVMTZUXIUWOTZUDUXIVHZCTZWBZWAZUXIUXHTAUXJUX
      IUVKVKZKDWJZUXOAKUVIUVKUXIDUVLUQUVTUXIUQTAUBWKUTUXCWLAUXQUXOAUXPUXOKDUWIU
      XPWAZUXKUXNUXRUXIUWNUWOUXRUXIUVITUVHUWJUXIVHZUAVJZHVKZUXIUWNTUXRUXIUVKUVI
      UWIUXPWNZUXRUVKUVITZKUVIWMZUWHUYCUXRUVIUVIUVLXFZUYDAUYEUWGUXPAUVRUYEUWFUV
      IUVIUVLWOVGWPKUVIUVIUVKUVLUVTWQVCUWIUWHUXPUXBWRUYCKUVIWSWFWTUXRUXTUVHUWJF
      VHZUVJVHZUAVJZUVHUCUHZUVJVHZUCVJZHUXRUVHUXSUYGUAUXRUWJUVHTZWAZUXSUWJUVKVH
      ZUYGUYMUWJUXIUVKUXRUXPUYLUYBWRXAUWIUYLUYNUYGVKZUXPUWIUYLWAZFXBZUWJFXCZTUY
      OAUYQUWGUYLAUVHUVHFUMZUYQUWEUVHUVHFXDVGZWPUYPUWJUVHUYRUWIUYLWNAUYRUVHVKZU
      WGUYLAUYSVUAUWEUVHUVHFXEVGZWPXGUWJUVJFXHWFXIXJXKUWIUYKUYHVKUXPUWIUVHUYJUV
      HUYGUCUAFUYFUYIUYFUVJXLUVHXMTZUWIUDEXNZUTAUYSUWGUWEWRUYPUYFWIUWIUYIUVHTZW
      AZUYJVUFBVIUYJABVIUOZUWGVUENWPUWIUVHBUYIUVJUWIBUVJEHAVUGUWGNWRZAHXOTZUWGM
      WRZAEXPTZUWGUWTWRZADUWOUVJUWSVSZXRXQXSXTYAWRUWIUYKHVKUXPUWIBUVJEHUCVUHVUJ
      VULVUMYBWRYCUWMUYAKUXIUVIUVJUXIVKZUWLUXTHVUNUVHUWKUXSUAUWJUVJUXIYDYEYHYFY
      GAUWOUWNVKZUWGUXPUXAWPXGUXRUXLUDUVKVHZCUXRUDUXIUVKUYBXAUXRVUPUDFVHZUVJVHZ
      CUXRUYQUDUYRTZVUPVURVKAUYQUWGUXPUYTWPAVUSUWGUXPAUDUVHUYRUWDVUBXGWPUDUVJFX
      HWFUXRVURUWPCUXRVUQJUVJAVUQJVKZUWGUXPAUVHFUQJUDUWAOUWDRYIZWPYJUWIUWRUXPUW
      IUVJUWOTZUWRUWIUVJUWRKUWOVLZTVVBUWRWAUWIUVJDVVCAUWGWNQYKUWRKUWOYLYMYNWRYO
      YOYOYPYQAUXOWAZUXPUXIUXIFUUAZUIZFUIZVKKVVFDAUXKUXNVVFDTAUXKWAZUXNWAZVVFVV
      CDVVIVVFUWOTJVVFVHZCTZWBZVVFVVCTVVIVVFUWNUWOVVIVVFUVITZUVHUWJVVFVHZUAVJZH
      VKZVVFUWNTVVHVVMUXNVVHVVMUVHBVVFXFZVVHUVHBUXIXFZUVHUVHVVEXFZVVQVVHBUXIEHA
      VUGUXKNWRZAVUIUXKMWRZAVUKUXKUWTWRZAUXKWNZXRZAVVSUXKAUYSUVHUVHVVEUMZVVSUWE
      UVHUVHFUUBZUVHUVHVVEWOYRWRUVHUVHBUXIVVEUUCWFAVVMVVQUUDZUXKABUQTUVHUQTVWGU
      WBUWABUVHVVFUQUQUUEWFWRUUFWRVVHVVPUXNVVHVVOUVHUWJVVEVHZUXIVHZUAVJUVHUYIUX
      IVHZUCVJHVVHUVHVVNVWIUAVVHUYLWAZVVEXBZUWJVVEXCZTZVVNVWIVKAVWLUXKUYLAUYSVW
      EVWLUWEVWFUVHUVHVVEXDYRZWPAUYLVWNUXKAUYLWAUWJUVHVWMAUYLWNAVWMUVHVKZUYLAUY
      SVWEVWPUWEVWFUVHUVHVVEXEYRZWRXGXIUWJUXIVVEXHWFXKVVHUVHVWJUVHVWIUCUAVVEVWH
      UYIVWHUXIXLVUCVVHVUDUTAVWEUXKAUYSVWEUWEVWFVGWRVWKVWHWIVVHVUEWAZVWJVWRBVIV
      WJVVHVUGVUEVVTWRVVHUVHBUYIUXIVWDXQXSXTYAVVHBUXIEHUCVVTVWAVWBVWCYBYCWRUWMV
      VPKVVFUVIUVJVVFVKZUWLVVOHVWSUVHUWKVVNUAUWJUVJVVFYDYEYHYFYGAVUOUXKUXNUXAWP
      XGVVIVVJJVVEVHZUXIVHZCVVIVWLJVWMTZVVJVXAVKAVWLUXKUXNVWOWPAVXBUXKUXNAJUVHV
      WMOVWQXGWPJUXIVVEXHWFVVIVXAUXLCVVIVWTUDUXIAVWTUDVKZUXKUXNAUYSUWCVUTVXCUWE
      UWDVVAUYSUWCWAVUTVXCUVHUVHUDJFUUGUUHUUIWPYJVVHUXNWNYOYOUWRVVLKVVFUWOVWSUW
      QVVKVWSUWPVVJCJUVJVVFYDYSYTYFYGQUUJUUKVVDVWSWAZUVKVVGUXIVXDUVJVVFFVVDVWSW
      NUULUUMVVDUXIUXIVVEFUIZUIZVVGVVDVXFUXIUUNUVHULZUIZUXIVVDVXEVXGUXIAVXEVXGV
      KZUXOAUYSVXIUWEUVHUVHFUUOVGWRUUPVVDVVRVXHUXIVKAUXKVVRUXNVWDUUTUVHBUXIUUQV
      GUURUXIVVEFUVAWHUUSUVBUVCUXGUXNKUXIUWOVUNUXFUXMVUNUXEUXLCUDUVJUXIYDYSYTYF
      UVDUVEPWHUVFUVG $.
  $}

  ${
    $d A c d x $.  $d B c d x $.  $d M c d x $.  $d S a c d x $.  $d ph d x $.
    reprdifc.c $e |- C = { c e. ( A ( repr ` S ) M ) | -. ( c ` x ) e. B } $.
    reprdifc.a $e |- ( ph -> A C_ NN ) $.
    reprdifc.b $e |- ( ph -> B C_ NN ) $.
    reprdifc.m $e |- ( ph -> M e. NN0 ) $.
    reprdifc.s $e |- ( ph -> S e. NN0 ) $.
    $( Express the representations as a sum of integers in a difference of sets
       using conditions on each of the indices.  (Contributed by Thierry
       Arnoux, 27-Dec-2021.) $)
    reprdifc $p |- ( ph -> ( ( A ( repr ` S ) M ) \ ( B ( repr ` S ) M ) )
      = U_ x e. ( 0 ..^ S ) C ) $=
      ( va vd co cv wcel wa cvv cc0 cfzo cfv csu wceq cmap cdif crab crepr ciun
      wn nfv nfrab1 nfcv wrex nn0zd reprval eleq2d rabid bitrdi anbi1d wb eldif
      anbi1i an32 bitri a1i bitr4d wral wf cn ssexd ovexd elmapg syl2anc adantr
      nnex wfn ffnfv wss cz cn0 simpr reprf ffnd biantrurd bitr4id bitrd notbid
      rexnal bitr4di pm5.32da bitr3d fveq1 eleq1d elrab rexbii r19.42v difeq12d
      eliun 3bitr4g eqrd difrab2 eqtrdi iuneq2d 3eqtr4d ) AUAFUBPZNQOQZUCNUDGUE
      ZOCXGUFPZDXGUFPZUGZUHZBXGBQZHQZUCZDRZUKZHCGFUIUCZPZUHZUJZXTDGXSPZUGZBXGEU
      JAOXMYBAOULXIOXLUMOYBUNAXHXLRZXISZXHYARZBXGUOZXHXMRXHYBRAYFXHXTRZXNXHUCZD
      RZUKZBXGUOZSZYHAYIXHXKRZUKZSZYFYNAYQXHXJRZXISZYPSZYFAYIYSYPAYIXHXIOXJUHZR
      YSAXTUUAXHACFGNOJAGLUPZMUQZURXIOXJUSUTVAYFYTVBAYFYRYPSZXISYTYEUUDXIXHXJXK
      VCVDYRYPXIVEVFVGVHAYIYPYMAYISZYPYKBXGVIZUKYMUUEYOUUFUUEYOXGDXHVJZUUFAYOUU
      GVBZYIADTRXGTRUUHADVKTVKTRAVQVGKVLAUAFUBVMDXGXHTTVNVOVPUUEUUGXHXGVRZUUFSU
      UFBXGDXHVSUUEUUIUUFUUEXGCXHUUECXHFGACVKVTYIJVPAGWARYIUUBVPAFWBRYIMVPAYIWC
      WDWEWFWGWHWIYKBXGWJWKWLWMYHYIYLSZBXGUOYNYGUUJBXGXRYLHXHXTXOXHUEZXQYKUUKXP
      YJDXNXOXHWNWOWIWPWQYIYLBXGWRVFWKXIOXLUSBXHXGYAWTXAXBAYDUUAXIOXKUHZUGXMAXT
      UUAYCUULUUCADFGNOKUUBMUQWSXIOXJXKXCXDABXGEYAEYAUEAIVGXEXF $.
  $}

  ${
    $d N n $.  $d i n $.
    $( Value of the second Chebyshev function, or summatory of the von Mangoldt
       function.  (Contributed by Thierry Arnoux, 28-Dec-2021.) $)
    chpvalz $p |- ( N e. ZZ -> ( psi ` N ) = sum_ n e. ( 1 ... N ) ( Lam ` n )
      ) $=
      ( cz wcel cchp cfv c1 cfl cfz co cvma csu wceq zre chpval syl flid oveq2d
      cv cr sumeq1d eqtrd ) BCDZBEFZGBHFZIJZASKFZALZGBIJZUGALUCBTDUDUHMBNBAOPUC
      UFUIUGAUCUEBGIBQRUAUB $.

    $( Value of the Chebyshev function for integers.  (Contributed by Thierry
       Arnoux, 28-Dec-2021.) $)
    chtvalz $p |- ( N e. ZZ ->
           ( theta ` N ) = sum_ n e. ( ( 1 ... N ) i^i Prime ) ( log ` n ) ) $=
      ( vi cz wcel cfv cc0 co cprime cin c1 cfz wceq syl c2 cdif c0 wss a1i wbr
      ccht cicc cv clog csu cr zre chtval cn nnz cfl ppisval flid oveq2d ineq1d
      eqtrd cuz 2nn nnuz eleqtri fzss1 ax-mp ssdif0 mpbi ineq1i 0in eqtri caddc
      wn csn eleq2i fzpred sylbi eqcomd 1p1e2 oveq1i difeq12d difun2 fzpreddisj
      cun disjdif2 eqtrid eqtr3d incom 1nprm disjsn mpbir eqtr3i eqtrdi syl2anc
      difininv adantl clt znnnlt1 biimpa wa cpnf cico cdvds cmin isprm3 simplbi
      wral ssriv nnzi uzssico sstri cxr nnrei rexri 0le0 adantr 1red simpr 1lt2
      cle 0xr lttrd iccssico pnfxr icodisj mp3an ssdisj sylancl eqtr3id sylancr
      syl22anc 1zzd simpl fzn syl21anc eqtr4d syldan exmidd mpjaodan sumeq1d )
      BDEZBUAFZGBUBHZIJZAUCZUDFZAUEZKBLHZIJZUUBAUEYQBUFEZYRUUCMBUGZBAUHNYQYTUUE
      UUBAYQBUIEZYTUUEMZUUHVIZUUHUUIYQUUHYTOBLHZIJZUUEUUHYQYTUULMBUJYQYTOBUKFZL
      HZIJZUULYQUUFYTUUOMUUGBULNYQUUNUUKIYQUUMBOLBUMUNUOUPNUUHUUKUUDPZIJZQMZUUD
      UUKPZIJZQMUULUUEMUURUUHUUQQIJZQUUPQIUUKUUDRZUUPQMOKUQFZEUVBOUIUVCURUSUTOK
      BVAVBUUKUUDVCVDVEIVFZVGSUUHUUTKVJZIJZQUUHUUSUVEIUUHUVEKKVHHZBLHZVTZUVHPZU
      USUVEUUHUVIUUDUVHUUKUUHUUDUVIUUHBUVCEZUUDUVIMUIUVCBUSVKZKBVLVMVNUVHUUKMUU
      HUVGOBLVOVPSVQUUHUVJUVEUVHPZUVEUVEUVHVRUUHUVEUVHJQMZUVMUVEMUUHUVKUVNUVLKB
      VSVMUVEUVHWANWBWCUOIUVEJZUVFQIUVEWDUVOQMKIEVIWEIKWFWGWHWIUUKIUUDWKWJUPWLY
      QUUJBKWMTZUUIYQUUJUVPBWNWOYQUVPWPZYTQUUEUVQYTIYSJZQYSIWDUVQIOWQWRHZRUVSYS
      JZQMUVRQMIOUQFZUVSAIUWAUUAIEUUAUWAECUCUUAWSTVICOUUAKWTHLHXCCUUAXAXBXDODEU
      WAUVSROURXEOXFVBXGUVQUVTYSUVSJZQYSUVSWDUVQYSGOWRHZRZUWCUVSJQMZUWBQMUVQGXH
      EZOXHEZGGXPTZBOWMTUWDUWFUVQXQSUWGUVQOOURXIZXJZSUWHUVQXKSUVQBKOYQUUFUVPUUG
      XLUVQXMOUFEUVQUWISYQUVPXNZKOWMTUVQXOSXRGOGBXSYGUWFUWGWQXHEUWEXQUWJXTGOWQY
      AYBYSUWCUVSYCYDYEIUVSYSYCYFWBUVQUUEUVAQUVQUUDQIUVQKDEZYQUVPUUDQMZUVQYHYQU
      VPYIUWKUWLYQWPUVPUWMKBYJWOYKUOUVDWIYLYMYQUUHYNYOYPUP $.
  $}

  ${
    $d N c m s t $.  $d S a c m s t $.  $d Z c m s t $.  $d b c s t $.
    $d ph c s t $.
    breprexp.n $e |- ( ph -> N e. NN0 ) $.
    breprexp.s $e |- ( ph -> S e. NN0 ) $.
    ${
      $d L a b d e x y $.  $d M a b c d e v $.  $d N a b c d e v $.
      $d S a b c d e v x y $.  $d ph a b c d e v x y $.
      breprexplema.m $e |- ( ph -> M e. NN0 ) $.
      breprexplema.1 $e |- ( ph -> M <_ ( ( S + 1 ) x. N ) ) $.
      breprexplema.l $e |- ( ( ( ph /\ x e. ( 0 ..^ ( S + 1 ) ) ) /\ y e. NN )
        -> ( ( L ` x ) ` y ) e. CC ) $.
      $( Lemma for ~ breprexp (induction step for weighted sums over
         representations).  (Contributed by Thierry Arnoux, 7-Dec-2021.) $)
      breprexplema $p |- ( ph -> sum_ d e. ( ( 1 ... N ) ( repr ` ( S + 1 ) ) M
        ) prod_ a e. ( 0 ..^ ( S + 1 ) ) ( ( L ` a ) ` ( d ` a ) )
       = sum_ b e. ( 1 ... N ) sum_ d e. ( ( 1 ... N ) ( repr ` S ) ( M - b ) )
          ( prod_ a e. ( 0 ..^ S ) ( ( L ` a ) ` ( d ` a ) )
            x. ( ( L ` S ) ` b ) ) ) $=
        ( vv cfv a1i wcel wceq vc ve c1 cfz co caddc crepr cc0 cfzo cv csu cmin
        cprod cop csn cun cmpt crn ciun cmul fz1ssnn nn0zd eqid reprsuc sumeq1d
        cn wss fzfid wa cfn cz adantr fzssz simpr sselid zsubcld cn0 reprfi syl
        mptfi rnfi cmap crab reprval ssrab2 eqsstrdi elexd wn actfunsnrndisj cc
        fzonel fzofi wral ralrimiva ad3antrrr wi nfv nfcv nfmpt1 nfrn nfel nfan
        wf cin c0 simplr reprf fsnd fzodisjsn fun2 syl21anc eleqtrdi fzosplitsn
        nn0uz ad4antr feq12d mpbird wrex snex unex elrnmpti bilani fveq2 fveq1d
        cuz vex eleq1d rspc2v syl2anc mpd ad2antrr wfn syl112anc fveq2d eqeltrd
        prodeq2dv 3eqtrd sumeq2dv simpl cvv r19.29af ffvelcdmd fprodcl prodeq1d
        anasss fsumiun ffnd fnsng fvun1 fzossfzop1 ffvelcdmda snidg fvun2 fvsng
        sselda fveq12d fzonn0p1 fprodsplitsn oveq12d actfunsnf1o uneq1d fsumf1o
        eqtrd fvmptd oveq1d cbvsumv 3eqtr4d ) AUCGUDUEZFDUCUFUEZUGQUEZUHUVIUIUE
        ZHUJZJUJZQZUVLEQZQZHUMZJUKIUVHPUVHFIUJZULUEZDUGQUEZPUJZDUVRUNZUOZUPZUQZ
        URZUSZUVQJUKUVHUWFUVQJUKZIUKUVHUVTUHDUIUEZUVPHUMZUVRDEQZQZUTUEZJUKZIUKA
        UVJUWGUVQJAUVHDUWEFIPUVHVFVGZAGVAZRAFMVBZLUWEVCZVDVEAIUVHUWFUVQJAUCGVHZ
        AUVRUVHSZVIZUWEVJSZUWFVJSUXAUVTVJSUXBUXAUVHDUVSUWOUXAUWPRZUXAFUVRAFVKSU
        WTUWQVLUXAUVHVKUVRUCGVMAUWTVNZVOVPZADVQSZUWTLVLZAUVHVJSUWTUWSVLVRZPUVTU
        WDVTVSUWEWAVSAPUVTUWIUVHIUWEDVQUXAUVTUWIUVLUAUJQHUKUVSTZUAUVHUWIWBUEZWC
        UXJUXAUVHDUVSHUAUXCUXEUXGWDUXIUAUXJWEWFZAUVHVJUWSWGZLDUWISWHZAUHDWKZRZU
        WRWIAUWTUVMUWFSZUVQWJSUXAUXPVIZUVKUVPHUVKVJSUXQUHUVIWLRUXQUVLUVKSZVIZCU
        JZBUJZEQZQZWJSZCVFWMZBUVKWMZUVPWJSZAUYFUWTUXPUXRAUYEBUVKAUYAUVKSVIUYDCV
        FOWNWNZWOUXSUXRUVNVFSUYFUYGWPUXQUXRVNZUXSUVHVFUVNUWPUXSUVKUVHUVLUVMUXQU
        VKUVHUVMXCZUXRUXQUVMUWDTZUYJPUVTUXAUXPPUXAPWQPUVMUWFPUVMWRPUWEPUVTUWDWS
        WTXAXBUXQUWAUVTSZVIZUYKVIZUYJUWIDUOZUPZUVHUWDXCZUYNUWIUVHUWAXCUYOUVHUWC
        XCUWIUYOXDXETZUYQUYNUVHUWADUVSUWOUYNUWPRUXAUVSVKSZUXPUYLUYKUXEWOUXAUXFU
        XPUYLUYKUXGWOZUXQUYLUYKXFXGUYNDUVRVQUVHUYTUXAUWTUXPUYLUYKUXDWOXHUYRUYNU
        HDXIZRUWIUYOUVHUWAUWCXJXKUYNUVKUYPUVHUVMUWDUYMUYKVNAUVKUYPTZUWTUXPUYLUY
        KADUHYEQZSVUBADVQVUCLXNXLUHDXMVSZXOXPXQUXPUYKPUVTXRUXAPUVTUWDUVMUWEUWRU
        WAUWCPYFUWBXSZXTYAYBUUAVLUYIUUBVOUYDUYGUXTUVOQZWJSZBCUVLUVNUVKVFUYAUVLT
        ZUYCVUFWJVUHUXTUYBUVOUYAUVLEYCYDYGZUXTUVNTVUFUVPWJUXTUVNUVOYCYGYHYIYJUU
        CZUUEUUFAUVHUWHUWNIUXAUVTUVKUVLUBUJZUWCUPZQZUVOQZHUMZUBUKUVTUWIUVLVUKQZ
        UVOQZHUMZUWLUTUEZUBUKZUWHUWNUXAUVTVUOVUSUBUXAVUKUVTSZVIZVUOUYPVUNHUMUWI
        VUNHUMZDVULQZUWKQZUTUEVUSVVBUVKUYPVUNHAVUBUWTVVAVUDYKUUDVVBUWIDVUNVVEHV
        QVVBHWQHVVEWRUWIVJSVVBUHDWLRUXAUXFVVAUXGVLZUXMVVBUXNRVVBUVLUWISZVIZVUNV
        UQWJVVHVUMVUPUVOVVHVUKUWIYLZUWCUYOYLZUYRVVGVUMVUPTVVBVVIVVGVVBUWIUVHVUK
        VVBUVHVUKDUVSUWOVVBUWPRUXAUYSVVAUXEVLVVFUXAVVAVNZXGZUUGZVLVVBVVJVVGVVBU
        XFUWTVVJVVFUXAUWTVVAUXDVLZDUVRVQUVHUUHYIZVLUYRVVHVUARVVBVVGVNUWIUYOVUKU
        WCUVLUUIYMYNZVVHUYFVUQWJSZVVBUYFVVGAUYFUWTVVAUYHYKZVLVVHUXRVUPVFSUYFVVQ
        WPVVBUWIUVKUVLAUWIUVKVGZUWTVVAAUXFVVSLDUUJVSYKUUOVVHUVHVFVUPUWPVVBUWIUV
        HUVLVUKVVLUUKVOUYDVVQVUGBCUVLVUPUVKVFVUIUXTVUPTVUFVUQWJUXTVUPUVOYCYGYHY
        IYJYOUVLDTVUMVVDUVOUWKUVLDEYCUVLDVULYCUUPVVBVVEUWLWJVVBVVDUVRUWKVVBVVDD
        UWCQZUVRVVBVVIVVJUYRDUYOSZVVDVVTTVVMVVOUYRVVBVUARVVBUXFVWAVVFDVQUULVSUW
        IUYOVUKUWCDUUMYMVVBUXFUWTVVTUVRTVVFVVNDUVRVQUVHUUNYIUVCYNZVVBUYFUWLWJSZ
        VVRVVBDUVKSZUVRVFSUYFVWCWPAVWDUWTVVAAUXFVWDLDUUQVSYKVVBUVHVFUVRUWPVVNVO
        UYDVWCUXTUWKQZWJSBCDUVRUVKVFUYADTZUYCVWEWJVWFUXTUYBUWKUYADEYCYDYGUXTUVR
        TVWEUWLWJUXTUVRUWKYCYGYHYIYJYOUURVVBVVCVURVVEUWLUTVVBUWIVUNVUQHVVPYPVWB
        UUSYQYRUXAUWFUVQUVTVUOJUBUWEVULUVMVULTZUVKUVPVUNHVWGUXRVIZUVNVUMUVOVWHU
        VLUVMVULVWGUXRYSYDYNYPUXHAPUVTUWIUVHIUWEDVQUXKUXLLUXOUWRUUTVVBPVUKUWDVU
        LUVTUWEYTUWEUWETVVBUWRRVVBUWAVUKTZVIUWAVUKUWCVVBVWIVNUVAVVKVULYTSVVBVUK
        UWCUBYFVUEXTRUVDVUJUVBUWNVUTTUXAUVTUWMVUSJUBUVMVUKTZUWJVURUWLUTVWJUWIUV
        PVUQHVWJVVGVIZUVNVUPUVOVWKUVLUVMVUKVWJVVGYSYDYNYPUVEUVFRUVGYRYQ $.
    $}

    breprexp.z $e |- ( ph -> Z e. CC ) $.
    ${
      $d L c m s t $.
      breprexp.h $e |- ( ph -> L : ( 0 ..^ S ) --> ( CC ^m NN ) ) $.
      ${
        breprexplemb.x $e |- ( ph -> X e. ( 0 ..^ S ) ) $.
        breprexplemb.y $e |- ( ph -> Y e. NN ) $.
        $( Lemma for ~ breprexp (closure).  (Contributed by Thierry Arnoux,
           7-Dec-2021.) $)
        breprexplemb $p |- ( ph -> ( ( L ` X ) ` Y ) e. CC ) $=
          ( cn cc cfv cmap co wcel ffvelcdmd wf cc0 cfzo cnex nnex elmap sylib
          ) ANOFECPZAUHONQRZSNOUHUAAUBBUCRUIECKLTONUHUDUEUFUGMT $.
      $}

      ${
        $d T a b d m n x y $.  $d Z a b d m n $.  $d L a b d m n x y $.
        $d ph a b d m n x y $.  $d N a b d m n x y $.
        breprexplemc.t $e |- ( ph -> T e. NN0 ) $.
        breprexplemc.s $e |- ( ph -> ( T + 1 ) <_ S ) $.
        breprexplemc.1 $e |- ( ph -> prod_ a e. ( 0 ..^ T ) sum_ b e. ( 1 ... N
          ) ( ( ( L ` a ) ` b ) x. ( Z ^ b ) ) = sum_ m e. ( 0 ... ( T x. N ) )
          sum_ d e. ( ( 1 ... N ) ( repr ` T ) m ) ( prod_ a e. ( 0 ..^ T ) ( (
          L ` a ) ` ( d ` a ) ) x. ( Z ^ m ) ) ) $.
        $( Lemma for ~ breprexp (induction step).  (Contributed by Thierry
           Arnoux, 6-Dec-2021.) $)
        breprexplemc $p |- ( ph -> prod_ a e. ( 0 ..^ ( T + 1 ) ) sum_ b e. ( 1
          ... N ) ( ( ( L ` a ) ` b ) x. ( Z ^ b ) ) = sum_ m e. ( 0 ... ( ( T
          + 1 ) x. N ) ) sum_ d e. ( ( 1 ... N ) ( repr ` ( T + 1 ) ) m ) (
          prod_ a e. ( 0 ..^ ( T + 1 ) ) ( ( L ` a ) ` ( d ` a ) ) x. ( Z ^ m )
          ) ) $=
          ( co cmul wcel vn vx vy cc0 c1 caddc cfzo cfz cv cfv cexp csu csn cun
          cprod crepr cuz wceq cn0 nn0uz eleqtrdi fzosplitsn syl prodeq1d fzofi
          nfv cfn a1i wn wa fzfid ad2antrr cc cn wf adantr wss cz cle wbr nn0zd
          nn0red biimpar fzoss2 sselda breprexplemb expcld mulcld fsumcl oveq1d
          nfcv sstri sumeq2dv wb zltp1le mpbird simpr elfzelzd reprfi ad3antrrr
          clt simplr reprf sselid fprodcl fz0ssnn0 cmin zsubcld adantlr ad4antr
          ffvelcdmd fsummulc1 adantl syl21anc mulassd 3eqtrd nn0addcld 3eqtr2rd
          eqtrd 1nn0 oveq1 oveq2d sumeq1d oveq2 oveq12d 3ad2ant1 3adant2 biimpa
          w3a zcnd c0 zred eqtrdi npcand eqeltrd mul02d recnd nn0sscn ad4ant13
          cr fzonel cmap 1red readdcld lep1d syl12anc fz1ssnn nnssnn0 ralrimivw
          letrd eluz1 r19.21bi simpl fveq2d nn0ge0d syl2anc 0zd elfzo mpbir2and
          fveq1d syl3anc fprodsplitsn fsum2mul ad5ant15 elfzle2 peano2zd sseldd
          eluz breprexplema cbvsumv eqtr4di nn0mulcld uzssz simp2 simp3 subnegd
          cneg znegcld znn0sub eqeltrrd ssidd remulcld fz2ssnn0 zmulcld zaddcld
          eluzle elfzle1 ltaddsub syl31anc reprgt sum0 fzossfz elfzolt2 sublt0d
          fzssz 0red ltletrd reprlt fzo0ssnn0 fsum2dsub adddirp1d eqcomd eqtr4d
          sumeq12dv mulcomd expaddd 3eqtr4d eqtr3d 3eqtr4rd 3eqtr2d ) AUDCUEUFR
          ZUGRZUEFUHRZIUIZHUIZEUJZUJZGUXNUKRZSRZIULZHUOUDCUGRZCUMUNZUXTHUOUYAUX
          THUOZUXMUXNCEUJZUJZUXRSRZIULZSRZUDUXKFSRZUHRZUXMDUIZUXKUPUJRZUXLUXOJU
          IZUJZUXPUJZHUOZGUYKUKRZSRJULZDULZAUXLUYBUXTHACUDUQUJZTUXLUYBURACUSUYT
          OUTVAUDCVBVCVDAUYACUXTUYGHUSAHVFHUYGWKUYAVGTZAUDCVEZVHOCUYATVIAUDCUUA
          VHAUXOUYATZVJZUXMUXSIVUDUEFVKVUDUXNUXMTZVJZUXQUXRVUFBEFUXOUXNGAFUSTZV
          UCVUEKVLABUSTZVUCVUELVLAGVMTZVUCVUEMVLZVUDUDBUGRZVMVNUUBREVOZVUEAVULV
          UCNVPVPVUDUXOVUKTZVUEAUYAVUKUXOABCUQUJTZUYAVUKVQZACVRTZBVRTZCBVSVTZVU
          NACOWAZABLWAZACUXKBACOWBZACUEVVAAUUCUUDABLWBACVVAUUEPUUJVUPVUNVUQVURV
          JCBUUKWCUUFCUDBWDVCZWEZVPVUDUXMVNUXNUXMVNVQZVUDFUUGZVHWEWFVUFGUXNVUJV
          UDUXMUSUXNAUXMUSVQZHUYAAVVFHUYAVVFAUXMVNUSVVEUUHWLZVHZUUIUULWEWGWHWIU
          XOCURZUXMUXSUYFIVVIVUEVJZUXQUYEUXRSVVJUXNUXPUYDVVJUXOCEVVIVUEUUMUUNUU
          TWJWMAUXMUYFIAUEFVKZAVUEVJZUYEUXRVVLBEFCUXNGAVUGVUEKVPZAVUHVUELVPZAVU
          IVUEMVPZAVULVUENVPZACVUKTZVUEAVVQUDCVSVTZCBXAVTZACOUUOZAVVSUXKBVSVTZP
          AVUPVUQVVSVWAWNVUSVUTCBWOUUPWPAVUPUDVRTVUQVVQVVRVVSVJWNVUSAUUQVUTCUDB
          UURUVAUUSVPZAUXMVNUXNVVDAVVEVHWEZWFZVVLGUXNVVOAUXMUSUXNVVHWEZWGZWHZWI
          UVBAUYHUDCFSRZUHRZUXMUYKCUPUJZRZUYAUYOHUOZUYQSRZJULZDULZUYGSRVWIUXMVW
          NUYFSRZIULZDULZUYSAUYCVWOUYGSQWJAVWIUXMVWNUYFDIAUDVWHVKVVKAUYKVWITZVJ
          ZVWKVWMJVWTUXMCUYKVVDVWTVVEVHVWTUYKUDVWHAVWSWQZWRZACUSTZVWSOVPZAUXMVG
          TZVWSVVKVPWSZVWTUYMVWKTZVJZVWLUYQVXHUYAUYOHVUAVXHVUBVHVXHVUCVJZBEFUXO
          UYNGVWTVUGVXGVUCAVUGVWSKVPVLAVUHVWSVXGVUCLWTAVUIVWSVXGVUCMWTAVULVWSVX
          GVUCNWTVXHUYAVUKUXOAVUOVWSVXGVVBVLWEVXIUXMVNUYNVVEVXIUYAUXMUXOUYMVXIU
          XMUYMCUYKVVDVXIVVEVHVWTUYKVRTZVXGVUCVXBVLVWTVXCVXGVUCVXDVLVWTVXGVUCXB
          XCVXHVUCWQXKXDWFXEZVXHGUYKAVUIVWSVXGMVLZVWTUYKUSTZVXGVWTVWIUSUYKVWHXF
          VXAXDZVPZWGZWHZWIVWGUVCAUYSUYJUXMUXMUAUIZUXNXGRZVWJRZVWLJULZUYEGVXRUK
          RZSRZSRZIULZUAULZVWIUXMVWKVWLJULZUYEGUYKUXNUFRZUKRZSRZSRZIULZDULZVWRA
          UYSUYJUXMUXMUYKUXNXGRZVWJRZVWLJULZUYEUYQSRZSRZIULZDULVYFAUYJUYRVYSDAU
          YKUYJTZVJZVYSUXMVYOVWLVYQSRZJULZIULZUYLUYPJULZUYQSRZUYRWUAUXMVYRWUCIW
          UAVUEVJZVYOVWLVYQJWUGUXMCVYNVVDWUGVVEVHWUGUYKUXNWUAVXJVUEWUAUYKUDUYIA
          VYTWQZWRZVPWUGUXNUEFWUAVUEWQWRXHZWUAVXCVUEAVXCVYTOVPZVPZWUAVXEVUEAVXE
          VYTVVKVPZVPWSZWUGUYEUYQAVUEUYEVMTZVYTVWDXIZWUAUYQVMTZVUEWUAGUYKAVUIVY
          TMVPZWUAUYJUSUYKUYIXFZWUHXDZWGZVPZWHWUGUYMVYOTZVJZUYAUYOHVUAWVDVUBVHW
          VDVUCVJZBEFUXOUYNGWUGVUGWVCVUCWUAVUGVUEAVUGVYTKVPZVPVLAVUHVYTVUEWVCVU
          CLXJWUAVUIVUEWVCVUCWURWTAVULVYTVUEWVCVUCNXJAVUCVUMVYTVUEWVCVVCUVDWVEU
          XMVNUYNVVEWVEUYAUXMUXOUYMWVEUXMUYMCVYNVVDWVEVVEVHWUGVYNVRTWVCVUCWUJVL
          WUGVXCWVCVUCWULVLWUGWVCVUCXBXCWVDVUCWQXKXDWFXEZXLWMWUAWUFUXMVYOVWLUYE
          SRZJULZIULZUYQSRUXMWVIUYQSRZIULWUDWUAWUEWVJUYQSWUAUBUCCEUYKFHIJWVFWUK
          WUTVYTUYKUYIVSVTAUYKUDUYIUVEXMWUAUBUIZUXLTZVJZUCUIZVNTZVJZBEFWVLWVOGW
          UAVUGWVMWVPWVFVLAVUHVYTWVMWVPLWTWUAVUIWVMWVPWURVLAVULVYTWVMWVPNWTWVQU
          XLVUKWVLAUXLVUKVQZVYTWVMWVPABUXKUQUJTZWVRAUXKVRTZVUQVWAWVSACVUSUVFVUT
          PWVTVUQVJWVSVWAUXKBUVHWCXNUXKUDBWDVCZWTWUAWVMWVPXBUVGWVNWVPWQWFUVIWJW
          UAUXMWVIUYQIWUMWVAWUGVYOWVHJWUNWVDVWLUYEWVGWUGWUOWVCWUPVPZWHZWIXLWUAU
          XMWVKWUCIWUGWVKVYOWVHUYQSRZJULWUCWUGVYOWVHUYQJWUNWVBWWCXLWUGVYOWWDWUB
          JWVDVWLUYEUYQWVGWWBWUGWUQWVCWVBVPXOWMXSWMXPWUAUYLUYPUYQJWUAUXMUXKUYKV
          VDWUAVVEVHWUIWUACUEWUKUEUSTZWUAXTVHXQZWUMWSWVAWUAUYMUYLTZVJZUXLUYOHUX
          LVGTWWHUDUXKVEVHWWHUXOUXLTZVJZBEFUXOUYNGWUAVUGWWGWWIWVFVLAVUHVYTWWGWW
          ILWTWUAVUIWWGWWIWURVLAVULVYTWWGWWINWTWWHUXLVUKUXOAWVRVYTWWGWWAVLWEWWJ
          UXMVNUYNVVEWWJUXLUXMUXOUYMWWJUXMUYMUXKUYKVVDWWJVVEVHWUAVXJWWGWWIWUIVL
          WUAUXKUSTWWGWWIWWFVLWUAWWGWWIXBXCWWHWWIWQXKXDWFXEXLXRWMUYJVYEVYSUADVX
          RUYKURZUXMVYDVYRIWWKVYDVYRURVUEWWKVYAVYPVYCVYQSWWKVXTVYOVWLJWWKVXSVYN
          UXMVWJVXRUYKUXNXGYAYBYCWWKVYBUYQUYESVXRUYKGUKYDYBYEVPWMUVJUVKAVYMUDVW
          HFUFRZUHRZUXMVYAUYEGVXSUXNUFRZUKRZSRZSRZIULZUAULVYFAVYKWWQDIUAVWHFACF
          OKUVLZKUYKVXSURZVYGVYAVYJWWPSWWTVWKVXTVWLJUYKVXSUXMVWJYDYCWWTVYIWWOUY
          ESWWTVYHWWNGUKUYKVXSUXNUFYAYBYBYEAUYKUXNUVQZUQUJZTZVUEYIZVYGVYJWXDVWK
          VWLJWXDUXMCUYKVVDWXDVVEVHWXDWXBVRUYKWXAUVMAWXCVUEUVNZXDZAWXCVXCVUEOYF
          ZAWXCVXEVUEVVKYFWSWXDVXGVJZUYAUYOHVUAWXHVUBVHWXHVUCVJZBEFUXOUYNGWXDVU
          GVXGVUCAVUEVUGWXCVVMYGZVLWXDVUHVXGVUCAVUEVUHWXCVVNYGZVLWXDVUIVXGVUCAV
          UEVUIWXCVVOYGZVLWXDVULVXGVUCAVUEVULWXCVVPYGZVLWXHUYAVUKUXOWXDVUOVXGAW
          XCVUOVUEVVBYFVPWEWXIUXMVNUYNVVEWXIUYAUXMUXOUYMWXHUYAUXMUYMVOVUCWXHUXM
          UYMCUYKVVDWXHVVEVHWXDVXJVXGWXFVPWXDVXCVXGWXGVPWXDVXGWQXCVPWXHVUCWQXKX
          DWFXEWIWXDUYEVYIWXDBEFCUXNGWXJWXKWXLWXMAVUEVVQWXCVWBYGAVUEUXNVNTWXCVW
          CYGWFWXDGVYHWXLWXDUYKWXAXGRZVYHUSWXDUYKUXNWXDUYKWXFYJWXDUXNWXDUXNUEFA
          WXCVUEUVOWRZYJUVPWXDWXAVRTZVXJWXAUYKVSVTZWXNUSTZWXDUXNWXOUVRWXFWXDWXC
          WXQWXEWXAUYKUWFVCWXPVXJVJWXQWXRWXAUYKUVSYHXNUVTWGWHWHVVLVXRVWHUXNUFRZ
          UEUFRZWWLUHRZTZVJZWWQUDWWPSRZUDWYCVYAUDWWPSWYCVYAYKVWLJULZUDWYCVXTYKV
          WLJWYCUXMCVXSFVVLVUGWYBVVMVPZWYCUXMUWAWYCVXRUXNWYCVXRWXTWWLVVLWYBWQZW
          RZWYCUXNUEFAVUEWYBXBWRZXHAVXCVUEWYBOVLWYCVWHYTTZUXNYTTZVXRYTTZWXSVXRX
          AVTZVWHVXSXAVTZWYCCFACYTTZVUEWYBVVAVLWYCFWYFWBUWBWYCUXNWYIYLWYCVXRVVL
          WYAUSVXRVVLWXTUSTWYAUSVQVVLWXSUEVVLVWHUXNAVWHUSTVUEWWSVPVWEXQWWEVVLXT
          VHXQWXTWWLUWCVCWEZWBWYCWXSVRTZVXRVRTZWXTVXRVSVTZWYMWYCVWHUXNWYCCFAVUP
          VUEWYBVUSVLWYCFWYFWAUWDWYIUWEWYHWYCWYBWYSWYGVXRWXTWWLUWGVCWYQWYRVJWYM
          WYSWXSVXRWOWCXNWYJWYKWYLYIWYMWYNVWHUXNVXRUWHYHUWIUWJYCVWLJUWKZYMWJWYC
          WWPWYCUYEWWOVVLWUOWYBVWDVPWYCGWWNVVLVUIWYBVVOVPWYCWWNVXRUSWYCVXRUXNWY
          CVXRWYHYJWYCUXNWYIYJYNWYPYOWGWHYPXSVVLVXRUDUXNUGRZTZVJZWWQWYDUDXUCVYA
          UDWWPSXUCVYAWYEUDXUCVXTYKVWLJXUCUXMCVXSVVDXUCVVEVHXUCVXRUXNXUCXUAVRVX
          RXUAUDUXNUHRVRUDUXNUWLUDUXNUWOWLVVLXUBWQZXDZXUCUXNUEFAVUEXUBXBWRZXHZA
          VXCVUEXUBOVLXUCVXSUDCXUCVXSXUGYLXUCUWPAWYOVUEXUBVVAVLXUCVXSUDXAVTVXRU
          XNXAVTZXUBXUHVVLVXRUDUXNUWMXMXUCVXRUXNXUCVXRXUEYLZXUCUXNXUFYLZUWNWPAV
          VRVUEXUBVVTVLUWQUWRYCWYTYMWJXUCWWPXUCUYEWWOVVLWUOXUBVWDVPXUCGWWNVVLVU
          IXUBVVOVPXUCWWNVXRUSXUCVXRUXNXUCVXRXUIYQXUCUXNXUJYQYNXUCXUAUSVXRUXNUW
          SXUDXDYOWGWHYPXSUWTAUYJWWMVYEWWRUAAUYIWWLUDUHACFAUSVMCYROXDAUSVMFYRKX
          DUXAYBAVXRUYJTZVJZUXMVYDWWQIXULVUEVJZVYCWWPVYASXUMVYBWWOUYESXUMVXRWWN
          GUKXUMWWNVXRXUMVXRUXNXUMUYJVMVXRUYJUSVMWUSYRWLAXUKVUEXBXDXUMUXMVMUXNU
          XMUSVMVVGYRWLXULVUEWQXDYNUXBYBYBYBWMUXDUXCAVWIVYLVWQDVWTUXMVYKVWPIVWT
          VUEVJZVWKVWMUYFSRZJULVWKVWLVYJSRZJULVWPVYKXUNVWKXUOXUPJXUNVXGVJZXUOVW
          LUYQUYFSRZSRXUPXUQVWLUYQUYFVWTVXGVWLVMTVUEVXKXIZVWTVXGWUQVUEVXPXIZXUN
          UYFVMTZVXGAVUEXVAVWSVWGXIZVPXOXUQXURVYJVWLSXUQUYQUYESRZUXRSRZXURVYJXU
          QUYQUYEUXRXUTAVUEWUOVWSVXGVWDYSZAVUEUXRVMTVWSVXGVWFYSZXOXUQVYQUXRSRUY
          EUYQUXRSRZSRXVDVYJXUQUYEUYQUXRXVEXUTXVFXOXUQXVCVYQUXRSXUQUYQUYEXUTXVE
          UXEWJXUQVYIXVGUYESXUQGUYKUXNVWTVXGVUIVUEVXLXIAVUEUXNUSTZVWSVXGVWEYSVW
          TVXGVXMVUEVXOXIUXFYBUXGUXHYBXSWMXUNVWKVWMUYFJVWTVWKVGTVUEVXFVPZXVBVWT
          VXGVWMVMTVUEVXQXIXLXUNVWKVWLVYJJXVIXUNUYEVYIAVUEWUOVWSVWDXIXUNGVYHAVU
          EVUIVWSVVOXIXUNUYKUXNVWTVXMVUEVXNVPAVUEXVHVWSVWEXIXQWGWHXUSXLUXIWMWMX
          RUXJXP $.
      $}

      $d L a b c i j k n $.  $d N a b c i j k n $.  $d S b $.
      $d Z a b c i j k n $.  $d ph a b c m $.  $d a b c i j k m n s $.
      $( Express the ` S ` th power of the finite series in terms of the number
         of representations of integers ` m ` as sums of ` S ` terms.  This is
         a general formulation which allows logarithmic weighting of the sums
         (see ~ https://mathoverflow.net/questions/253246) and a mix of
         different smoothing functions taken into account in ` L ` .  See
         ~ breprexpnat for the simple case presented in the proposition of
         [Nathanson] p. 123.  (Contributed by Thierry Arnoux, 6-Dec-2021.) $)
      breprexp $p |- ( ph -> prod_ a e. ( 0 ..^ S ) sum_ b e. ( 1 ... N )
         ( ( ( L ` a ) ` b ) x. ( Z ^ b ) )
      = sum_ m e. ( 0 ... ( S x. N ) ) sum_ c e. ( ( 1 ... N ) ( repr ` S ) m )
         ( prod_ a e. ( 0 ..^ S ) ( ( L ` a ) ` ( c ` a ) ) x. ( Z ^ m ) ) ) $=
        ( wcel cc0 co c1 cmul csu wceq vt vs vj vi vn vk cn0 cfzo cfz cfv cprod
        cv cexp crepr wa cle wbr cr wss nn0ssre a1i sselda leid syl caddc breq1
        oveq2 prodeq1d oveq1 oveq2d fveq2 oveqd oveq1d adantr sumeq12dv eqeq12d
        wi imbi12d csn c0 cc 0nn0 cfn cif fz1ssnn 0zd repr0 eqid iftruei eqtrdi
        cn snfi eqeltrdi fzo0 prodeq1i prod0 exp0 oveq12d ax-1cn mulridi fsumcl
        eqtri simpl sumsn sylancr sumeq1d cvv 0ex mulcld fveq1 fveq2d ralrimivw
        prodeq2d 3eqtr2d eqtrd 3eqtrd nn0cnd mul02d 3eqtr4rd a1d simpll cbvsumv
        fz0sn simplr eqeq2i fveq1d sumeq2dv cbvprodv prodeq2i fveq12d prodeq2dv
        oveq1i sumeq2i eqeq12i bitri imbi2i simpr ad3antrrr sselid mpd sylib wf
        cmap simpllr readdcld ltp1d ltled letrd sylibr breprexplemc syl21anc ex
        1red nn0indd mpdan ) ABUGNZOBUHPZQEUIPZHULZGULZDUJZUJZFUUSUMPZRPZHSZGUK
        ZOBERPZUIPZUURCULZBUNUJZPZUUQUUTIULZUJZUVAUJZGUKZFUVIUMPZRPZISZCSZTZKAU
        UPUOZBBUPUQZUVTUWABURNUWBAUGURBUGURUSAUTVAVBBVCVDAUAULZBUPUQZOUWCUHPZUV
        EGUKZOUWCERPZUIPZUURUVIUWCUNUJZPZUWEUVNGUKZUVPRPZISZCSZTZVQOBUPUQZOOUHP
        ZUVEGUKZOOERPZUIPZUURUVIOUNUJZPZUWQUVNGUKZUVPRPZISZCSZTZVQUBULZBUPUQZOU
        XHUHPZUVEGUKZOUXHERPZUIPZUURUVIUXHUNUJZPZUXJUVNGUKZUVPRPZISZCSZTZVQZUXH
        QVEPZBUPUQZOUYBUHPZUVEGUKZOUYBERPZUIPZUURUVIUYBUNUJZPZUYDUVNGUKZUVPRPZI
        SZCSZTZVQUWBUVTVQUAUBBUWCOTZUWDUWPUWOUXGUWCOBUPVFUYOUWFUWRUWNUXFUYOUWEU
        WQUVEGUWCOOUHVGZVHUYOUWHUWTUWMUXECUYOUWGUWSOUIUWCOERVIVJUYOUWMUXETUVIUW
        HNZUYOUWJUXBUWLUXDIUYOUWIUXAUURUVIUWCOUNVKVLUYOUWLUXDTUVLUWJNZUYOUWKUXC
        UVPRUYOUWEUWQUVNGUYPVHVMVNVOVNVOVPVRUWCUXHTZUWDUXIUWOUXTUWCUXHBUPVFUYSU
        WFUXKUWNUXSUYSUWEUXJUVEGUWCUXHOUHVGZVHUYSUWHUXMUWMUXRCUYSUWGUXLOUIUWCUX
        HERVIVJUYSUWMUXRTUYQUYSUWJUXOUWLUXQIUYSUWIUXNUURUVIUWCUXHUNVKVLUYSUWLUX
        QTUYRUYSUWKUXPUVPRUYSUWEUXJUVNGUYTVHVMVNVOVNVOVPVRUWCUYBTZUWDUYCUWOUYNU
        WCUYBBUPVFVUAUWFUYEUWNUYMVUAUWEUYDUVEGUWCUYBOUHVGZVHVUAUWHUYGUWMUYLCVUA
        UWGUYFOUIUWCUYBERVIVJVUAUWMUYLTUYQVUAUWJUYIUWLUYKIVUAUWIUYHUURUVIUWCUYB
        UNVKVLVUAUWLUYKTUYRVUAUWKUYJUVPRVUAUWEUYDUVNGVUBVHVMVNVOVNVOVPVRUWCBTZU
        WDUWBUWOUVTUWCBBUPVFVUCUWFUVFUWNUVSVUCUWEUUQUVEGUWCBOUHVGZVHVUCUWHUVHUW
        MUVRCVUCUWGUVGOUIUWCBERVIVJVUCUWMUVRTUYQVUCUWJUVKUWLUVQIVUCUWIUVJUURUVI
        UWCBUNVKVLVUCUWLUVQTUYRVUCUWKUVOUVPRVUCUWEUUQUVNGVUDVHVMVNVOVNVOVPVRAUX
        GUWPAOVSZUXECSZQUXFUWRAVUFUUROUXAPZUXCFOUMPZRPZISZVTVSZVUIISZQAOUGNVUJW
        ANVUFVUJTWBAVUGVUIIAVUGVUKWCAVUGOOTZVUKVTWDVUKAUUREOUURWKUSAEWEVAAWFJWG
        VUMVUKVTOWHWIWJZVTWLWMAVUIWANUVLVUGNAVUIQWAAVUIQQRPZQAUXCQVUHQRUXCQTAUX
        CVTUVNGUKQUWQVTUVNGOWNZWOUVNGWPXBVAAFWANZVUHQTLFWQVDZWRZQWSWTWJZWSWMVNX
        AUXEVUJCOUGUVIOTZUXBVUGUXDVUIIUVIOUURUXAVGVVAUVLUXBNZUOZUVPVUHUXCRVVCUV
        IOFUMVVAVVBXCVJVJVOXDXEAVUGVUKVUIIVUNXFAVULUWQUUTVTUJZUVAUJZGUKZVUHRPZQ
        AVTXGNVVGWANVULVVGTXHAVVFVUHAVVFQWAVVFQTAVVFVTVVEGUKQUWQVTVVEGVUPWOVVEG
        WPXBVAZWSWMAVUHQWAVURWSWMXIVUIVVGIVTXGUVLVTTZUXCVVFVUHRVVIUWQUVNVVEGVVI
        UVNVVETGUWQVVIUVMVVDUVAUUTUVLVTXJXKXLXMVMXDXEAVVGVUOVUIQAVVFQVUHQRVVHVU
        RWRVUSVUTXNXOXPAUWTVUEUXECAUWTOOUIPVUEAUWSOOUIAEAEJXQXRVJYCWJXFUWRQTAUW
        RVTUVEGUKQUWQVTUVEGVUPWOUVEGWPXBVAXSXTAUXHUGNZUOZUYAUOZUYCUYNVVLUYCUOZV
        VKUXIUXJUURUCULZUDULZDUJZUJZFVVNUMPZRPZUCSZUDUKZUXMUURUEULZUXNPZUXJVVOU
        FULZUJZVVPUJZUDUKZFVWBUMPZRPZUFSZUESZTZVQZUYCUYNVVKUYAUYCYAVVMUYAVWMVVK
        UYAUYCYDUXTVWLUXIUXTUXKUXMVWCUXPVWHRPZISZUESZTVWLUXSVWPUXKUXMUXRVWOCUEU
        VIVWBTZUXOVWCUXQVWNIUVIVWBUURUXNVGVWQUXQVWNTUVLUXONVWQUVPVWHUXPRUVIVWBF
        UMVGVJVNVOYBYEUXKVWAVWPVWKUXKUXJUURUUSVVPUJZUVCRPZHSZUDUKVWAUXJUVEVWTGU
        DUUTVVOTZUURUVDVWSHVXAUUSUURNZUOZUVBVWRUVCRVXCUUSUVAVVPVXCUUTVVODVXAVXB
        XCXKYFVMYGYHUXJVWTVVTUDVWTVVTTVVOUXJNZUURVWSVVSHUCUUSVVNTVWRVVQUVCVVRRU
        USVVNVVPVKUUSVVNFUMVGWRYBVAYIXBUXMVWOVWJUEVWOVWJTVWBUXMNVWOVWCUXJVVOUVL
        UJZVVPUJZUDUKZVWHRPZISVWJVWCVWNVXHIVWNVXHTUVLVWCNUXPVXGVWHRUXJUVNVXFGUD
        VXAUVMVXEUVAVVPUUTVVODVKUUTVVOUVLVKYJYHYLVAYMVWCVXHVWIIUFUVLVWDTZVXGVWG
        VWHRVXIUXJVXFVWFUDVXIVXDUOZVXEVWEVVPVXJVVOUVLVWDVXIVXDXCYFXKYKVMYBXBVAY
        MYNYOYPZUUAVVLUYCYQVVKVWMUOZUYCUOZBUXHCDEFGHIAEUGNVVJVWMUYCJYRAUUPVVJVW
        MUYCKYRZAVUQVVJVWMUYCLYRAUUQWAWKUUCPDUUBVVJVWMUYCMYRAVVJVWMUYCUUDZVXLUY
        CYQZVXMUXIUXTVXMUXHUYBBVXMUGURUXHUTVXOYSZVXMUXHQVXQVXMUUMUUEZVXMUGURBUT
        VXNYSVXMUXHUYBVXQVXRVXMUXHVXQUUFUUGVXPUUHVXMVWMUYAVVKVWMUYCYDVXKUUIYTUU
        JUUKUULUUNYTUUO $.
    $}

    ${
      $d A a b c m $.  $d N a b c m $.  $d S a b c m $.  $d Z a b c m $.
      $d ph a b c m $.
      breprexpnat.a $e |- ( ph -> A C_ NN ) $.
      breprexpnat.p $e |- P = sum_ b e. ( A i^i ( 1 ... N ) ) ( Z ^ b ) $.
      breprexpnat.r $e |- R = ( # ` ( ( A i^i ( 1 ... N ) ) ( repr ` S ) m ) )
        $.
      $( Express the ` S ` th power of the finite series in terms of the number
         of representations of integers ` m ` as sums of ` S ` terms of
         elements of ` A ` , bounded by ` N ` .  Proposition of [Nathanson]
         p. 123.  (Contributed by Thierry Arnoux, 11-Dec-2021.) $)
      breprexpnat $p |- ( ph
         -> ( P ^ S ) = sum_ m e. ( 0 ... ( S x. N ) ) ( R x. ( Z ^ m ) ) ) $=
        ( va co cmul cn wcel vc c1 cfz cin cv cexp csu cc0 crepr cfv chash cfzo
        cind csn cxp cprod wf cc cmap wss fvex fconst cpr cvv nnex indf sylancr
        0cn ax-1cn prssi mp2an sylancl cnex elmap sylibr snss sylib breprexp wa
        fss wceq fvconst2 ad2antlr fveq1d oveq1d sumeq2dv a1i cfn fzfi ad2antrr
        fz1ssnn adantr nnssnn0 sstri simpr sselid expcld indsumin incom sumeq1d
        cn0 3eqtrd prodeq2dv fzofi inss2 fsumcl fprodconst syl2anc hashfzo0 syl
        ssfi oveq2d cz fzssz reprfi fz0ssnn0 ad3antrrr reprf ffvelcdmda fprodcl
        ffvelcdmd fsummulc1 hashreprin adantl 3eqtr4rd 3eqtr3d sumeq2i 3eqtr4g
        oveq1i ) ABUBGUCQZUDZHIUEZUFQZIUGZEUFQZUHEGRQZUCQZYKFUEZEUIUJZQUKUJZHYR
        UFQZRQZFUGZCEUFQYQDUUARQZFUGAUHEULQZYJYLPUEZUUEBSUMUJZUJZUNZUOZUJZUJZYM
        RQZIUGZPUPZYQYJYRYSQZUUEUUFUAUEZUJZUUKUJZPUPZUUARQZUAUGZFUGYOUUCAEFUUJG
        HPIUAJKLAUUEUUIUUJUQUUIURSUSQZUTZUUEUVCUUJUQUUEUUHBUUGVAZVBAUUHUVCTZUVD
        ASURUUHUQZUVFASUHUBVCZUUHUQZUVHURUTZUVGASVDTZBSUTZUVIVEMBSVDVFVGZUHURTU
        BURTUVJVHVIUHUBURVJVKZSUVHURUUHVTVLURSUUHVMVEVNVOUUHUVCUVEVPVQUUEUUIUVC
        UUJVTVGVRAUUOUUEYNPUPZYNUUEUKUJZUFQZYOAUUEUUNYNPAUUFUUETZVSZUUNYJYLUUHU
        JZYMRQZIUGYJBUDZYMIUGYNUVSYJUUMUWAIUVSYLYJTZVSZUULUVTYMRUWDYLUUKUUHUVRU
        UKUUHWAAUWCUUEUUHUUFUVEWBZWCWDWEWFUVSYJBYMISVDUVKUVSVEWGYJWHTZUVSUBGWIZ
        WGYJSUTZUVSGWKZWGAUVLUVRMWLUWDHYLAHURTZUVRUWCLWJUWDYJXAYLYJSXAUWIWMWNZU
        VSUWCWOWPWQWRUVSUWBYKYMIUWBYKWAUVSYJBWSWGWTXBXCAUUEWHTZYNURTUVOUVQWAUWL
        AUHEXDZWGAYKYMIYKWHTZAUWFYKYJUTUWNUWGBYJXEZYJYKXKVKWGAYLYKTZVSZHYLAUWJU
        WPLWLUWQYKXAYLYKYJXAUWOUWKWNAUWPWOWPWQXFUUEYNPXGXHAUVPEYNUFAEXATZUVPEWA
        KEXIXJXLXBAYQUVBUUBFAYRYQTZVSZUUPUUEUURUUHUJZPUPZUAUGZUUARQUUPUXBUUARQZ
        UAUGUUBUVBUWTUUPUXBUUAUAUWTYJEYRUWHUWTUWIWGZUWTYQXMYRUHYPXNAUWSWOZWPZAU
        WRUWSKWLZUWFUWTUWGWGZXOUWTHYRAUWJUWSLWLUWTYQXAYRYPXPUXFWPWQUWTUUQUUPTZV
        SZUUEUXAPUWLUXKUWMWGUXKUVRVSZUVHURUXAUVNUXLSUVHUURUUHAUVIUWSUXJUVRUVMXQ
        UXLYJSUURUWIUXKUUEYJUUFUUQUXKYJUUQEYRUWHUXKUWIWGUWTYRXMTUXJUXGWLUWTUWRU
        XJUXHWLUWTUXJWOXRXSWPYAWPXTYBUWTYTUXCUUARUWTBYJEYRPUAAUVLUWSMWLUXGUXHUX
        IUXEYCWEUWTUUPUVAUXDUAUXKUUTUXBUUARUWTUUTUXBWAUXJUWTUUEUUSUXAPUVRUUSUXA
        WAUWTUVRUURUUKUUHUWEWDYDXCWLWEWFYEWFYFCYNEUFNYIYQUUDUUBFUUDUUBWAUWSDYTU
        UAROYIWGYGYH $.
    $}
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Vinogradov Trigonometric Sums and the Circle Method
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c vts $.

  $( The Vinogradov trigonometric sums. $)
  cvts $a class vts $.

  ${
    $d a l n x $.
    $( Define the Vinogradov trigonometric sums.  (Contributed by Thierry
       Arnoux, 1-Dec-2021.) $)
    df-vts $a |- vts = ( l e. ( CC ^m NN ) , n e. NN0 |->
      ( x e. CC |-> sum_ a e. ( 1 ... n ) ( ( l ` a ) x.
        ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( a x. x ) ) ) ) ) ) $.
  $}

  ${
    vtsval.n $e |- ( ph -> N e. NN0 ) $.
    vtsval.x $e |- ( ph -> X e. CC ) $.
    ${
      $d L a l n x $.  $d N a l n x $.  $d X a x $.  $d ph x $.
      vtsval.l $e |- ( ph -> L : NN --> CC ) $.
      $( Value of the Vinogradov trigonometric sums.  (Contributed by Thierry
         Arnoux, 1-Dec-2021.) $)
      vtsval $p |- ( ph -> ( ( L vts N ) ` X ) = sum_ a e. ( 1 ... N )
       ( ( L ` a ) x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( a x. X ) ) ) ) ) $=
        ( vx vl vn c1 cfz co cv cfv cmul csu cc wceq ci c2 cpi ce cvts cvv cmap
        cn wcel cn0 cmpt cnex nnex elmap sylibr fveq1 oveq1d sumeq2sdv mpteq2dv
        oveq2 sumeq1d df-vts mptex ovmpo syl2anc oveq2d fveq2d adantl sumex a1i
        wf fvmptd ) AIDLCMNZEOZBPZUAUBUCQNQNZVNIOZQNZQNZUDPZQNZERZVMVOVPVNDQNZQ
        NZUDPZQNZERZSBCUENZUFABSUHUGNZUIZCUJUIWHISWBUKZTAUHSBVKWJHSUHBULUMUNUOF
        JKBCWIUJISLKOZMNZVNJOZPZVTQNZERZUKWKUEISWMWAERZUKWNBTZISWQWRWSWMWPWAEWS
        WOVOVTQVNWNBUPUQURUSWLCTZISWRWBWTWMVMWAEWLCLMUTVAUSIKEJVBISWBULVCVDVEVQ
        DTZWBWGTAXAVMWAWFEXAVTWEVOQXAVSWDUDXAVRWCVPQVQDVNQUTVFVGVFURVHGWGUFUIAV
        MWFEVIVJVL $.

      $d ph a $.
      $( Closure of the Vinogradov trigonometric sums.  (Contributed by Thierry
         Arnoux, 14-Dec-2021.) $)
      vtscl $p |- ( ph -> ( ( L vts N ) ` X ) e. CC ) $=
        ( va co cfv c1 ci c2 cpi cmul cc wcel cn adantr mulcld cfz cv ce vtsval
        cvts csu fzfid wa wf wss fz1ssnn a1i sselda ffvelcdmd ax-icn 2cn mulcli
        picn nncnd efcld fsumcl eqeltrd ) ADBCUEIJKCUAIZHUBZBJZLMNOIZOIZVDDOIZO
        IZUCJZOIZHUFPABCDHEFGUDAVCVKHAKCUGAVDVCQZUHZVEVJVMRPVDBARPBUIVLGSAVCRVD
        VCRUJACUKULUMZUNVMVIVMVGVHVGPQVMLVFUOMNUPURUQUQULVMVDDVMVDVNUSADPQVLFST
        TUTTVAVB $.
    $}

    ${
      $d L a b c m $.  $d N a b c m $.  $d S a b c m $.  $d X a b c m $.
      $d a b c m ph $.
      vtsprod.s $e |- ( ph -> S e. NN0 ) $.
      vtsprod.l $e |- ( ph -> L : ( 0 ..^ S ) --> ( CC ^m NN ) ) $.
      $( Express the Vinogradov trigonometric sums to the power of ` S `
         (Contributed by Thierry Arnoux, 12-Dec-2021.) $)
      vtsprod $p |- ( ph -> prod_ a e. ( 0 ..^ S ) ( ( ( L ` a ) vts N ) ` X )
      = sum_ m e. ( 0 ... ( S x. N ) ) sum_ c e. ( ( 1 ... N ) ( repr ` S ) m )
            ( prod_ a e. ( 0 ..^ S ) ( ( L ` a ) ` ( c ` a ) )
            x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( m x. X ) ) ) ) ) $=
        ( vb co cfv cmul ce csu cc wcel cc0 cfzo c1 cfz cv ci c2 cpi cexp cprod
        crepr cvts ax-icn a1i 2cnd picn mulcld efcld breprexp wa adantr cn cmap
        cn0 wf ffvelcdmda elmapi syl vtsval cz fzssz simpr sselid zcnd ad2antrr
        mul12d fveq2d wceq efexp syl2anc eqtr3d oveq2d sumeq2dv eqtrd prodeq2dv
        3eqtr4d ) AUABUBNZUCEUDNZMUEZGUEZDOZOZUFUGUHPNZPNZFPNZQOZWIUINZPNZMRZGU
        JUABEPNZUDNZWHCUEZBUKONZWGWJHUEZOWKOGUJZWPXBUINZPNZHRZCRWGFWKEULNOZGUJX
        AXCXEWNXBFPNPNZQOZPNZHRZCRABCDEWPGMHIKAWOAWNFAUFWMUFSTAUMUNAUGUHAUOUHST
        AUPUNUQUQZJUQZURLUSAWGXIWSGAWJWGTZUTZXIWHWLWNWIFPNPNZQOZPNZMRWSXQWKEFMA
        EVDTXPIVAAFSTZXPJVAZXQWKSVBVCNZTVBSWKVEAWGYCWJDLVFWKSVBVGVHVIXQWHXTWRMX
        QWIWHTZUTZXSWQWLPYEWIWOPNZQOZXSWQYEYFXRQYEWIWNFYEWIYEWHVJWIUCEVKXQYDVLV
        MZVNAWNSTZXPYDXNVOXQYAYDYBVAVPVQYEWOSTZWIVJTYGWQVRAYJXPYDXOVOYHWOWIVSVT
        WAWBWCWDWEAXAXMXHCAXBXATZUTZXCXLXGHYLXDXCTZUTZXKXFXEPYNXBWOPNZQOZXKXFYN
        YOXJQYNXBWNFYNXBYLXBVJTZYMYLXAVJXBUAWTVKAYKVLVMVAZVNAYIYKYMXNVOAYAYKYMJ
        VOVPVQYNYJYQYPXFVRAYJYKYMXOVOYRWOXBVSVTWAWBWCWCWF $.
    $}
  $}

  ${
    $d L a c m x $.  $d N a c m x $.  $d S a c m x $.  $d a c m ph x $.
    circlemeth.n $e |- ( ph -> N e. NN0 ) $.
    circlemeth.s $e |- ( ph -> S e. NN ) $.
    circlemeth.l $e |- ( ph -> L : ( 0 ..^ S ) --> ( CC ^m NN ) ) $.
    $( The Hardy, Littlewood and Ramanujan Circle Method, in a generic form,
       with different weighting / smoothing functions.  (Contributed by Thierry
       Arnoux, 13-Dec-2021.) $)
    circlemeth $p |- ( ph -> sum_ c e. ( NN ( repr ` S ) N )
             prod_ a e. ( 0 ..^ S ) ( ( L ` a ) ` ( c ` a ) )
       = S. ( 0 (,) 1 ) ( prod_ a e. ( 0 ..^ S ) ( ( ( L ` a ) vts N ) ` x )
         x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u N x. x ) ) ) ) _d x ) $=
      ( vm cc0 c1 co cmul csu wcel adantr cc a1i cioo cfzo cv cfv cvts cprod ci
      c2 cpi cneg ce citg cfz crepr cmin cn wa cn0 wss ioossre ax-resscn sselda
      cr sstri nnnn0d cmap vtsprod oveq1d fzfid ax-icn 2cn mulcli nn0cnd negcld
      wf picn ralrimivw r19.21bi mulcld efcld fz1ssnn cz simpr elfzelzd adantlr
      reprfi fzofi ad3antrrr zcnd ad2antrr reprf ffvelcdmda sselid breprexplemb
      adantl3r fprodcl fsumcl fsummulc1 mulassd wceq caddc efadd syl2anc adddid
      cfn adddird eqtr3d oveq2d fveq2d eqtrd sumeq2dv 3eqtrd itgeq2dv cmpt cibl
      negsubd cvol ioombl sumex adantllr subcld an32s anasss fvex cicc ioossicc
      cvv cdm ccncf 0red unitsscn syl3anc itgfsum simprd cif oveq2 nn0zd eqtr4d
      1red sumeq1d ssidd cncfmptc cncfmptid efmul2picn cniccibl iblmulc2 simpld
      mulcncf iblss mulridd mul01d ifeq3da velsn subeq0ad bitr4id ifbid zsubcld
      csn itgexpif syl 1cnd 0cnd ifcld 3eqtr4rd wral cuz wo 0zd zmulcld nn0ge0d
      cle wbr nnmulge elfzd snssd syldan ralrimiva olcd sumss2 syl21anc 3eqtr2d
      sumsn itgmulc2 reprfz1 3eqtr4d 3eqtrrd ) ABLMUANZLCUBNZBUCZFUCZDUDZEUENUD
      FUFZUGUHUIONZONZEUJZUWIONZONZUKUDZONZULBUWGLCEONZUMNZMEUMNZKUCZCUNUDZNZUW
      HUWJGUCZUDZUWKUDZFUFZUWNUXCEUONZUWIONZONZUKUDZONZGPZKPZULZUXABUWGUXOULZKP
      ZUPEUXDNZUXIGPZABUWGUWSUXPAUWIUWGQZUQZUWSUXAUXEUXIUWNUXCUWIONZONZUKUDZONZ
      GPZKPZUWRONUXAUYHUWRONZKPUXPUYCUWLUYIUWROUYCCKDEUWIFGAEURQZUYBHRAUWGSUWIU
      WGSUSAUWGVCSLMUTVAVDTVBZACURQZUYBACIVEZRZAUWHSUPVFNDVOZUYBJRVGVHUYCUXAUYH
      UWRKUYCLUWTVIUYCUWQUYCUWNUWPUWNSQZUYCUGUWMVJUHUIVKVPVLVLZTUYCUWOUWIAUWOSQ
      ZBUWGAUYSBUWGAEAEHVMZVNVQVRZUYLVSZVSZVTZUYCUXCUXAQZUQZUXEUYGGVUFUXBCUXCUX
      BUPUSZVUFEWAZTAVUEUXCWBQZUYBAVUEUQZUXCLUWTAVUEWCWDZWEZUYCUYMVUEUYORVUFMEV
      IWFZVUFUXFUXEQZUQZUXIUYFVUOUWHUXHFUWHXEQZVUOLCWGZTAVUEVUNUWJUWHQZUXHSQZUY
      BVUJVUNUQZVURUQZCDEUWJUXGUXCAUYKVUEVUNVURHWHAUYMVUEVUNVURUYNWHVUJUXCSQVUN
      VURVUJUXCVUKWIZWJAUYPVUEVUNVURJWHVUTVURWCVVAUXBUPUXGVUHVUTUWHUXBUWJUXFVUT
      UXBUXFCUXCVUGVUTVUHTVUJVUIVUNVUKRZAUYMVUEVUNUYNWJVUJVUNWCWKWLWMWNZWOWPZVU
      FUYFSQVUNVUFUYEVUFUWNUYDUYQVUFUYRTZVUFUXCUWIVUFUXCVULWIZUYCUWISQVUEUYLRZV
      SZVSZVTRZVSZWQWRUYCUXAUYJUXOKVUFUYJUXEUYGUWRONZGPUXOVUFUXEUYGUWRGVUMUYCUW
      RSQZVUEVUDRZVVLWRVUFUXEVVMUXNGVUOVVMUXIUYFUWRONZONZUXNVUOUXIUYFUWRVVEVVKV
      UFVVNVUNVVORWSVUFVVQUXNWTVUNVUFVVPUXMUXIOVUFUYEUWQXANZUKUDZVVPUXMVUFUYESQ
      UWQSQZVVSVVPWTVVJUYCVVTVUEVUCRUYEUWQXBXCVUFVVRUXLUKVUFUWNUYDUWPXANZONVVRU
      XLVUFUWNUYDUWPVVFVVIUYCUWPSQVUEVUBRXDVUFVWAUXKUWNOVUFUXCUWOXANZUWIONVWAUX
      KVUFUXCUWOUWIVVGUYCUYSVUEVUARVVHXFVUFVWBUXJUWIOVUFUXCEVVGAESQZUYBVUEUYTWJ
      ZXPVHXGXHXGXIXGXHRXJXKXJXKXLXMABUWGUXPXNXOQUXQUXSWTABUWGUXAUXOKYGUWGXQYHQ
      ZALMXRZTZALUWTVIZUXOYGQAUYBVUEUQUQUXEUXNGXSTVUJBUWGUXOXNXOQZUXRUXEBUWGUXN
      ULZGPZWTZVUJBUWGUXEUXNGSAVWEVUEVWGRVUJUXBCUXCVUGVUJVUHTVUKAUYMVUEUYNRVUJM
      EVIWFZVUJUYBVUNUXNSQVUJUYBUQZVUNUQZUXIUXMVWOUWHUXHFVUPVWOVUQTVUJVUNVURVUS
      UYBVVDXTWPVWOUXLVWNUXLSQZVUNAUYBVUEVWPVUFUWNUXKVVFVUFUXJUWIVUFUXCEVVGVWDY
      AVVHVSVSYBRVTZVSYCVUTBUWGUXMUXIYGVUTUWHUXHFVUPVUTVUQTVVDWPZUXMYGQZVUTUYBU
      QUXLUKYDZTVUJBUWGUXMXNXOQVUNVUJBUWGLMYENZUXMYGUWGVXAUSVUJLMYFTVWEVUJVWFTV
      WSVUJUWIVXAQUQVWTTVUJLVCQMVCQBVXAUXMXNZVXASYINZQVXBXOQVUJYJVUJYSVUJBVXAUX
      KVUJBUXJUWIVXAVUJUXJSQVXASUSZSSUSZBVXAUXJXNVXCQVUJUXCEVVBAVWCVUEUYTRZYAVX
      DVUJYKTZVUJSUUAZBUXJVXASUUBYLVUJVXDVXEBVXAUWIXNVXCQVXGVXHBVXASUUCXCUUHUUD
      LMVXBUUEYLUUIRZUUFYMZUUGYMYNAUXAUXEUXIBUWGUXMULZONZGPZKPZUXBEUXDNZUXIGPZU
      XSUYAAVXNUXAUXCEUURZQZUXEUXIGPZLYOZKPZVXQVXSKPZVXPAUXAVXMVXTKVUJUXJLWTZVX
      SLYOVXSVYCMLYOZONZVXTVXMVUJVYCVXSLVYEMLVXSMONVXSLONVYDMVXSOYPVYDLVXSOYPVU
      JVXSVUJUXEUXIGVWMVWRWQZUUJVUJVXSVYFUUKUULVUJVXRVYCVXSLVUJVXRUXCEWTZVYCKEU
      UMVUJUXCEVVBVXFUUNUUOUUPVUJVXMUXEUXIVYDONZGPVYEVUJUXEVXLVYHGVUTVXKVYDUXIO
      VUTUXJWBQVXKVYDWTVUTUXCEVVCAEWBQZVUEVUNAEHYQZWJUUQBUXJUUSUUTXHXKVUJUXEUXI
      VYDGVWMVUJVYCMLSVUJUVAVUJUVBUVCVWRWRYRUVDXKAVXQUXAUSVXSSQZKVXQUVEUXALUVFU
      DUSZUXAXEQZUVGVYBVYAWTAEUXAAELUWTAUVHACEACUYNYQVYJUVIVYJAEHUVJACUPQUYKEUW
      TUVKUVLIHCEUVMXCUVNUVOZAVYKKVXQAVXRVUEVYKAVXQUXAUXCVYNVBVYFUVPUVQAVYMVYLV
      WHUVRVXQUXAVXSKLUVSUVTAUYKVXPSQVYBVXPWTHAVXOUXIGAUXBCEVUGAVUHTVYJUYNAMEVI
      WFAUXFVXOQZUQZUWHUXHFVUPVYPVUQTVYPVURUQZCDEUWJUXGEAUYKVYOVURHWJAUYMVYOVUR
      UYNWJAVWCVYOVURUYTWJAUYPVYOVURJWJVYPVURWCVYQUXBUPUXGVUHVYPUWHUXBUWJUXFVYP
      UXBUXFCEVUGVYPVUHTAVYIVYOVYJRAUYMVYOUYNRAVYOWCWKWLWMWNWPWQVXSVXPKEURVYGUX
      EVXOUXIGUXCEUXBUXDYPYTUWBXCUWAAUXAUXRVXMKVUJUXRVWKVXMVUJVWIVWLVXJYNVUJUXE
      VXLVWJGVUTBUWGUXMUXISVWRVUJUYBVUNUXMSQVWQYBVXIUWCXKYRXKAUXTVXOUXIGACEHUYN
      UWDYTUWEUWF $.
  $}

  ${
    $d A a c x $.  $d F a $.  $d N a c x $.  $d S a c x $.
    circlemethnat.r $e |- R = ( # ` ( A ( repr ` S ) N ) ) $.
    circlemethnat.f $e |- F = ( ( ( ( _Ind ` NN ) ` A ) vts N ) ` x ) $.
    circlemethnat.n $e |- N e. NN0 $.
    circlemethnat.a $e |- A C_ NN $.
    circlemethnat.s $e |- S e. NN $.
    $( The Hardy, Littlewood and Ramanujan Circle Method, Chapter 5.1 of
       [Nathanson] p. 123.  This expresses ` R ` , the number of different ways
       a nonnegative integer ` N ` can be represented as the sum of at most
       ` S ` integers in the set ` A ` as an integral of Vinogradov
       trigonometric sums.  (Contributed by Thierry Arnoux, 13-Dec-2021.) $)
    circlemethnat $p |- R = S. ( 0 (,) 1 ) ( ( F ^ S )
        x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u N x. x ) ) ) ) _d x $=
      ( va co cmul cfv wtru cn wcel cc a1i vc cc0 c1 cioo cexp ci c2 cneg cv ce
      cpi citg wceq crepr cfzo cind csn cxp cprod csu cvts chash wa cmap wf cpr
      wss cvv nnex indf mp2an cr pr01ssre ax-resscn sstri fss elmap mpbir elexi
      cnex fvconst2 adantl fveq1d prodeq2dv sumeq2dv cn0 nnnn0d hashrepr eqtr4d
      eqtr4id fconst6 circlemeth fzofi ioossre sselda vtscl eqeltrid fprodconst
      cfn syl2anc oveq1d adantr hashfzo0 oveq2d 3eqtr3d itgeq2dv 3eqtrd mptru
      syl ) CAUBUCUDMZEDUEMZUFUGUKNMNMFUHAUIZNMNMUJOZNMZULZUMPCQFDUNOZMZUBDUOMZ
      LUIZUAUIZOZXSXRBQUPOOZUQURZOZOZLUSZUAUTZAXJXRXLYDFVAMZOZLUSZXMNMZULXOPCBF
      XPMVBOZYGGPYGXQXRYAYBOZLUSZUAUTYLPXQYFYNUAPXTXQRVCZXRYEYMLYOXSXRRZVCYAYDY
      BYPYDYBUMZYOXRYBXSYBSQVDMZYBYRRQSYBVEZQUBUCVFZYBVEZYTSVGYSQVHRBQVGZUUAVIJ
      BQVHVJVKYTVLSVMVNVOQYTSYBVPVKZSQYBVTVIVQVRZVSWAZWBWCWDWEPBDFLUAUUBPJTFWFR
      ZPITZPDDQRPKTZWGZWHWIWJPADYCFLUAUUGUUHXRYRYCVEPXRYBYRUUDWKTWLPAXJYKXNPXLX
      JRZVCZYJXKXMNUUKXRELUSZEXRVBOZUEMZYJXKUUKXRWSRZESRUULUUNUMUUOUUKUBDWMTUUK
      EXLYBFVAMZOZSHUUKYBFXLUUFUUKITPXJSXLXJSVGPXJVLSUBUCWNVNVOTWOYSUUKUUCTWPWQ
      XRELWRWTUUKXREYILUUKYPVCZEUUQYIHUURXLYHUUPUURYDYBFVAYPYQUUKUUEWBXAWCWJWDU
      UKUUMDEUEUUKDWFRZUUMDUMPUUSUUJUUIXBDXCXIXDXEXAXFXGXH $.
  $}

  ${
    $d N a n x $.  $d a n ph x $.
    circlevma.n $e |- ( ph -> N e. NN0 ) $.
    $( The Circle Method, where the Vinogradov sums are weighted using the von
       Mangoldt function, as it appears as proposition 1.1 of [Helfgott] p. 5.
       (Contributed by Thierry Arnoux, 13-Dec-2021.) $)
    circlevma $p |- ( ph -> sum_ n e. ( NN ( repr ` 3 ) N )
      ( ( Lam ` ( n ` 0 ) ) x. ( ( Lam ` ( n ` 1 ) ) x. ( Lam ` ( n ` 2 ) ) ) )
      = S. ( 0 (,) 1 ) ( ( ( ( Lam vts N ) ` x ) ^ 3 )
        x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u N x. x ) ) ) ) _d x ) $=
      ( va cn c3 cfv co cc0 cvma c1 c2 cmul wcel a1i cc cr wceq cfzo cv csn cxp
      crepr cprod csu cioo cvts ci cpi cneg ce citg cexp 3nn cmap wss ax-resscn
      wf vmaf fss mp2an cvv wb cnex nnex elmapg mpbir fconst6 circlemeth wa ctp
      tpid1 fzo0to3tp eleqtrri eleq1 mpbiri elexi fvconst2 syl fveq12d 1eltp012
      c0ex fveq2 2ex tpid3 fveq1d adantl ssidd cz nn0zd adantr cn0 nnnn0i simpr
      reprf ffvelcdmda ffvelcdmd eqeltrd prodfzo03 sumeq2dv chash prodeq2dv cfn
      oveq1d fzofi ioossre sstri sselda vtscl fprodconst syl2anc hashfzo0 ax-mp
      oveq2d 3eqtrd itgeq2dv 3eqtr3d ) AGDHUEIJZKHUAJZFUBZCUBZIZYBYALUCUDZIZIZF
      UFZCUGBKMUHJZYABUBZYFDUIJZIZFUFZUJNUKOJOJDULYJOJOJUMIZOJZUNXTKYCIZLIZMYCI
      ZLIZNYCIZLIZOJOJZCUGBYIYJLDUIJZIZHUOJZYNOJZUNABHYEDFCEHGPAUPQYARGUQJZYEUT
      AYALUUGLUUGPZGRLUTZGSLUTSRURUUIVAUSGSRLVBVCZRVDPGVDPUUHUUIVEVFVGRGLVDVDVH
      VCVIZVJQVKAXTYHUUBCAYCXTPZVLZYQYSUUAYGFYBKTZYDYPYFLUUNYBYAPZYFLTZUUNUUOKY
      APKKMNVMZYAKMNWDVNVOVPYBKYAVQVRYALYBLUUGUUKVSVTZWAYBKYCWEWBYBMTZYDYRYFLUU
      SUUOUUPUUSUUOMYAPMUUQYAWCVOVPYBMYAVQVRUURWAYBMYCWEWBYBNTZYDYTYFLUUTUUOUUP
      UUTUUONYAPNUUQYAKMNWFWGVOVPYBNYAVQVRUURWAYBNYCWEWBUUMUUOVLZYGYDLIZRUUOYGU
      VBTUUMUUOYDYFLUURWHWIUVAGRYDLUUIUVAUUJQUUMYAGYBYCUUMGYCHDUUMGWJADWKPUULAD
      EWLWMHWNPZUUMHUPWOZQAUULWPWQWRWSWTXAXBABYIYOUUFAYJYIPZVLZYMUUEYNOUVFYMYAU
      UDFUFZUUDYAXCIZUOJZUUEUVFYAYLUUDFUVFUUOVLZYJYKUUCUVJYFLDUIUUOUUPUVFUURWIX
      FWHXDUVFYAXEPZUUDRPUVGUVITUVKUVFKHXGQUVFLDYJADWNPUVEEWMAYIRYJYIRURAYISRKM
      XHUSXIQXJUUIUVFUUJQXKYAUUDFXLXMUVFUVHHUUDUOUVHHTZUVFUVCUVLUVDHXNXOQXPXQXF
      XRXS $.
  $}

  ${
    $d H a n x y $.  $d K a n x y $.  $d N a n x $.  $d ph a n x y $.
    circlemethhgt.h $e |- ( ph -> H : NN --> RR ) $.
    circlemethhgt.k $e |- ( ph -> K : NN --> RR ) $.
    circlemethhgt.n $e |- ( ph -> N e. NN0 ) $.
    $( The circle method, where the Vinogradov sums are weighted using the Von
       Mangoldt function and smoothed using functions ` H ` and ` K ` .
       Statement 7.49 of [Helfgott] p. 69.  At this point there is no further
       constraint on the smoothing functions.  (Contributed by Thierry Arnoux,
       22-Dec-2021.) $)
    circlemethhgt $p |- ( ph -> sum_ n e. ( NN ( repr ` 3 ) N )
       ( ( ( Lam ` ( n ` 0 ) ) x. ( H ` ( n ` 0 ) ) )
    x. ( ( ( Lam ` ( n ` 1 ) ) x. ( K ` ( n ` 1 ) ) )
      x. ( ( Lam ` ( n ` 2 ) ) x. ( K ` ( n ` 2 ) ) ) ) )
      = S. ( 0 (,) 1 ) ( ( ( ( ( Lam oF x. H ) vts N ) ` x )
        x. ( ( ( ( Lam oF x. K ) vts N ) ` x ) ^ 2 ) )
        x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u N x. x ) ) ) ) _d x ) $=
      ( cn c3 cfv co cc0 cmul c1 c2 wcel wceq cvv va vy crepr cfzo cvma cof cs3
      cv cprod csu cioo cvts ci cpi cneg ce citg cexp 3nn a1i cmap chash eqcomi
      cc s3len wf cr wa simprl simprr remulcld recnd vmaf nnex inidm cnex elmap
      off sylibr s3cld wrdfd circlemeth fveq12d adantr ffvelcdmda elmapi syl cz
      fveq2 ssidd nn0zd 3nn0 simpr reprf ffvelcdmd prodfzo03 s3fv0 fveq1d simpl
      cn0 ovex mp1i ctp c0ex tpid1 fzo0to3tp eleqtrri wfn ffn ax-mp eqidd ofval
      syl2anc eqtrd s3fv1 1eltp012 s3fv2 2ex tpid3 oveq12d sumeq2dv csn cun nfv
      ffnd nfcv cfn fzofi wn wo eqid orci cfz ad2antrr wss sselda oveq1d adantl
      vtscl 3eqtr3d 0elfz elfznelfzob mp2b mpbir ioossre ax-resscn sstri eqtrdi
      fzo0ss1 fprodsplitsn uncom fzo0sn0fzo1 eqtr4i prodeq1d cpr fzo13pr eleq2i
      wb vex elpr bitri jaodan sylan2b adantlr prodeq2dv fprodconst cuz eleqtri
      cmin nnuz hashfzo 3m1e2 eqtri oveq2d 3eqtrd sqcld mulcomd eqtr4d itgeq2dv
      ) AJFKUCLMZNKUDMZUAUHZCUHZLZUWBUEDOUFZMZUEEUWEMZUWGUGZLZLZUAUIZCUJBNPUKMZ
      UWABUHZUWIFULMZLZUAUIZUMQUNOMOMFUOUWMOMOMUPLZOMZUQUVTNUWCLZUELZUWSDLZOMZP
      UWCLZUELZUXCELZOMZQUWCLZUELZUXGELZOMZOMZOMZCUJBUWLUWMUWFFULMZLZUWMUWGFULM
      ZLZQURMZOMZUWQOMZUQABKUWHFUACIKJRZAUSUTAVDJVAMZKUWHKUWHVBLZSAUYBKUWFUWGUW
      GVEVCUTAUWFUWGUWGUYAAJVDUWFVFZUWFUYARABUBJJJOVGVGVDUEDTTAUWMVGRZUBUHZVGRZ
      VHVHZUWMUYEOMUYGUWMUYEAUYDUYFVIAUYDUYFVJVKVLZJVGUEVFZAVMUTZGJTRAVNUTZUYKJ
      VOZVRZVDJUWFVPVNVQVSAJVDUWGVFZUWGUYARABUBJJJOVGVGVDUEETTUYHUYJHUYKUYKUYLV
      RZVDJUWGVPVNVQVSZUYPVTWAZWBAUVTUWKUXLCAUWCUVTRZVHZUWKUWSNUWHLZLZUXCPUWHLZ
      LZUXGQUWHLZLZOMZOMUXLUYSVUAVUCVUEUWJUAUWBNSZUWDUWSUWIUYTUWBNUWHWIZUWBNUWC
      WIWCUWBPSZUWDUXCUWIVUBUWBPUWHWIZUWBPUWCWIWCUWBQSZUWDUXGUWIVUDUWBQUWHWIZUW
      BQUWCWIWCUYSUWBUWARVHZJVDUWDUWIVUMUWIUYARZJVDUWIVFZUYSUWAUYAUWBUWHAUWAUYA
      UWHVFZUYRUYQWDWEUWIVDJWFZWGUYSUWAJUWBUWCUYSJUWCKFUYSJWJAFWHRUYRAFIWKWDKWT
      RZUYSWLUTAUYRWMWNZWEWOWPUYSVUAUXBVUFUXKOUYSVUAUWSUWFLZUXBUYSUWSUYTUWFUWFT
      RZUYTUWFSZUYSUEDUWEXAZUWFUWGUWGTWQZXBWRUYSAUWSJRZVUTUXBSAUYRWSZUYSUWAJNUW
      CVUSNUWARUYSNNPQXCZUWANPQXDXEXFXGUTWOAJJUWTUXAOJUEDTTUWSUEJXHZAUYIVVHVMJV
      GUEXIXJUTZAJVGDGYEUYKUYKUYLAVVEVHZUWTXKVVJUXAXKXLXMXNUYSVUCUXFVUEUXJOUYSV
      UCUXCUWGLZUXFUYSUXCVUBUWGUWGTRZVUBUWGSZUYSUEEUWEXAZUWFUWGUWGTXOZXBWRUYSAU
      XCJRZVVKUXFSVVFUYSUWAJPUWCVUSPUWARUYSPVVGUWAXPXFXGUTWOAJJUXDUXEOJUEETTUXC
      VVIAJVGEHYEZUYKUYKUYLAVVPVHZUXDXKVVRUXEXKXLXMXNUYSVUEUXGUWGLZUXJUYSUXGVUD
      UWGVVLVUDUWGSZUYSVVNUWFUWGUWGTXQZXBWRUYSAUXGJRZVVSUXJSVVFUYSUWAJQUWCVUSQU
      WARUYSQVVGUWANPQXRXSXFXGUTWOAJJUXHUXIOJUEETTUXGVVIVVQUYKUYKUYLAVWBVHZUXHX
      KVWCUXIXKXLXMXNXTXTXNYAABUWLUWRUXSAUWMUWLRZVHZUWPUXRUWQOVWEPKUDMZNYBZYCZU
      WOUAUIVWFUWOUAUIZUXNOMZUWPUXRVWEVWFNUWOUXNUATVWEUAYDUAUXNYFVWFYGRZVWEPKYH
      UTZNTRVWEXDUTNVWFRYIZVWEVWMNNSZNKSZYJZVWNVWONYKYLVURNNKYMMRVWMVWPUURWLKUU
      AKNUUBUUCUUDUTVWEUWBVWFRZVHZUWIFUWMAFWTRZVWDVWQIYNVWEUWMVDRVWQAUWLVDUWMUW
      LVDYOAUWLVGVDNPUUEUUFUUGUTYPZWDVWRVUNVUOVWRUWAUYAUWBUWHAVUPVWDVWQUYQYNVWE
      VWFUWAUWBVWFUWAYOVWEKUUIUTYPWOVUQWGYSVUGUWMUWNUXMVUGUWIUWFFULVUGUWIUYTUWF
      VUHVVAVVBVVCVVDXJUUHYQWRVWEUWFFUWMAVWSVWDIWDZVWTAUYCVWDUYMWDYSZUUJVWEVWHU
      WAUWOUAVWHUWASVWEVWHVWGVWFYCZUWAVWFVWGUUKUXTUWAVXCSUSKUULXJUUMUTUUNVWEVWJ
      UXQUXNOMUXRVWEVWIUXQUXNOVWEVWIVWFUXPUAUIZUXPVWFVBLZURMZUXQVWEVWFUWOUXPUAV
      WRUWMUWNUXOVWRUWIUWGFULAVWQUWIUWGSZVWDVWQAVUIVUKYJZVXGVWQUWBPQUUOZRVXHVWF
      VXIUWBUUPUUQUWBPQUAUUSUUTUVAAVUIVXGVUKAVUIVHZUWIVUBUWGVUIUWIVUBSAVUJYRVVL
      VVMVXJVVNVVOXBXNAVUKVHZUWIVUDUWGVUKUWIVUDSAVULYRVVLVVTVXKVVNVWAXBXNUVBUVC
      UVDYQWRUVEVWEVWKUXPVDRVXDVXFSVWLVWEUWGFUWMVXAVWTAUYNVWDUYOWDYSZVWFUXPUAUV
      FXMVWEVXEQUXPURVXEQSVWEVXEKPUVIMZQKPUVGLZRVXEVXMSKJVXNUSUVJUVHPKUVKXJUVLU
      VMUTUVNUVOYQVWEUXNUXQVXBVWEUXPVXLUVPUVQUVRYTYQUVSYT $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The Ternary Goldbach Conjecture: Final Statement
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d h k m n x z $.
    $( Statement 7.49 of [Helfgott] p. 70.  For a sufficiently big odd ` N ` ,
       this postulates the existence of smoothing functions ` h ` (eta star)
       and ` k ` (eta plus) such that the lower bound for the circle integral
       is big enough.  (Contributed by Thierry Arnoux, 15-Dec-2021.) $)
    ax-hgt749 $a |- A. n e. { z e. ZZ | -. 2 || z } ( ( ; 1 0 ^ ; 2 7 ) <_ n
      -> E. h e. ( ( 0 [,) +oo ) ^m NN ) E. k e. ( ( 0 [,) +oo ) ^m NN ) (
         A. m e. NN ( k ` m ) <_ ( 1 . _ 0 _ 7 _ 9 _ 9 _ 5 5 )
      /\ A. m e. NN ( h ` m ) <_ ( 1 . _ 4 _ 1 4 )
      /\ ( ( 0 . _ 0 _ 0 _ 0 _ 4 _ 2 _ 2 _ 4 8 ) x. ( n ^ 2 ) )
       <_ S. ( 0 (,) 1 ) ( ( ( ( ( Lam oF x. h ) vts n ) ` x )
        x. ( ( ( ( Lam oF x. k ) vts n ) ` x ) ^ 2 ) )
        x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u n x. x ) ) ) ) _d x ) ) $.
  $}

  $( Theorem 12. of [RosserSchoenfeld] p. 71.  Theorem ~ chpo1ubb states that
     the ` psi ` function is bounded by a linear term; this axiom postulates an
     upper bound for that linear term.  This is stated as an axiom until a
     formal proof can be provided.  (Contributed by Thierry Arnoux,
     28-Dec-2021.) $)
  ax-ros335 $a |- A. x e. RR+ ( psi ` x )
                                        < ( ( 1 . _ 0 _ 3 _ 8 _ 8 3 ) x. x ) $.

  $( Theorem 13. of [RosserSchoenfeld] p. 71.  Theorem ~ chpchtlim states that
     the ` psi ` and ` theta ` function are asymtotic to each other; this axiom
     postulates an upper bound for their difference.  This is stated as an
     axiom until a formal proof can be provided.  (Contributed by Thierry
     Arnoux, 28-Dec-2021.) $)
  ax-ros336 $a |- A. x e. RR+ ( ( psi ` x ) - ( theta ` x ) )
                                 < ( ( 1 . _ 4 _ 2 _ 6 2 ) x. ( sqrt ` x ) ) $.

  ${
    $d N i j $.  $d N x $.  $d ph i x $.
    hgt750lemc.n $e |- ( ph -> N e. NN ) $.
    $( An upper bound to the summatory function of the von Mangoldt function.
       (Contributed by Thierry Arnoux, 29-Dec-2021.) $)
    hgt750lemc $p |- ( ph -> sum_ j e. ( 1 ... N ) ( Lam ` j )
      < ( ( 1 . _ 0 _ 3 _ 8 _ 8 3 ) x. N ) ) $=
      ( vx cchp cfv c1 cfz co cv cvma c3 c8 cdp2 cmul clt wceq wbr crp csu wcel
      cc0 cdp nnzd chpvalz syl fveq2 oveq2 breq12d wral ax-ros335 nnrpd rspcdva
      cz a1i eqbrtrrd ) ACFGZHCIJBKLGBUAZHUCMNNMOOOOUDJZCPJZQACUOUBURUSRACDUEBC
      UFUGAEKZFGZUTVBPJZQSZURVAQSETCVBCRVCURVDVAQVBCFUHVBCUTPUIUJVEETUKAEULUPAC
      DUMUNUQ $.

    hgt750lemd.0 $e |- ( ph -> ( ; 1 0 ^ ; 2 7 ) <_ N ) $.
    $( An upper bound to the summatory function of the von Mangoldt function on
       non-primes.  (Contributed by Thierry Arnoux, 29-Dec-2021.) $)
    hgt750lemd $p |- ( ph
      -> sum_ i e. ( ( ( 1 ... N ) \ Prime ) u. { 2 } ) ( Lam ` i )
       < ( ( 1 . _ 4 _ 2 _ 6 3 ) x. ( sqrt ` N ) ) ) $=
      ( c1 co cprime cfv c2 c4 c6 cmul cc0 clt wcel cr a1i 0nn0 wbr vx cfz cdif
      cv cvma csu clog caddc cdp2 cdp csqrt csn cun c3 cfn fzfid diffi wa cn wf
      syl vmaf wss fz1ssnn ssdifssd sselda ffvelcdmd fsumrecl crp relogcld 1nn0
      2rp cn0 4re 2re 6re pm3.2i dp2cl ax-mp mp2an nnred nnrpd rpge0d resqrtcld
      dpcl remulcld 0re 1re cchp ccht cmin cin wceq nnzd chpvalz vmaprm oveq12d
      cz recnd fsumcl eqcomi fveq2 cdc c7 cexp 10nn0 7nn0 nn0expcli nn0rei cdiv
      w3a 3pm3.2i 1lt10 ltexp2a cc wne 10pos 4z mp3an oveq2i 4nn0 1rp oveq1i c5
      nn0zi dpexpp1 rpdp2cl 6nn0 2nn0 deccl cle eqtr3i expgt0 ltleii lttrd 2prm
      3rp addridi eqid dpadd2 chtvalz inss2 sumeq2dv eqtr4d infi inss1 sstri c0
      inindif inundif fsumsplit eqtr2d oveq2d breq12d ax-ros336 rspcdva eqbrtrd
      mvrladdd wral log2le1 0z 3z 3pos numexp0 recni gtneii expm1 4m1e3 divrec2
      nn0cni 3eqtr3ri 3brtr4i dp0h breqtrri 4p1e5 5p1e6 6p1e7 3eqtrri breqtrrdi
      5nn0 rpdpcl nn0ge0i expmul 7t2e14 fveq2i sqrtsq 4lt10 1lt2 decltc wb mpbi
      sqrtlt eqbrtrri sqrtled mpbid ltletrd ltmul2dd lt2addd nfv nfcv wn elndif
      eqtrdi 2cnd 2ne0 logcld fsumsplitsn 1p0e1 4cn 2cn 3nn0 2p1e3 decadd dpadd
      6cn adddird eqtr3id 3brtr4d ) AFCUBGZHUCZBUDZUEIZBUFZJUGIZUHGFKJLJUIZUIZU
      IZUJGZCUKIZMGZNNNNFUIZUIZUIZUJGZUYIMGZUHGZUXTJULUMUYBBUFFKJLUNUIZUIZUIUJG
      ZUYIMGZOAUYCUYDUYJUYOAUXTUYBBAUXSUOPZUXTUOPAFCUPZUXSHUQVAZAUYAUXTPURZUSQU
      YAUEUSQUEUTZVUDVBRAUXTUSUYAAUXSUSHUXSUSVCACVDZRZVEVFVGZVHAJJVIPAVLRVJZAUY
      HUYIUYHQPZAFVMPUYGQPZVUJVKKQPZUYFQPZURVUKVULVUMVNJQPZUYEQPZURVUMVUNVUOVOL
      QPZVUNURVUOVUPVUNVPVOVQLJVRVSVQJUYEVRVSVQKUYFVRVSFUYGWEVTRZACACDWAZACACDW
      BZWCZWDZWFAUYNUYIUYNQPZANVMPUYMQPZVVBSNQPZUYLQPZURVVCVVDVVEWGVVDUYKQPZURV
      VEVVDVVFWGVVDFQPZURVVFVVDVVGWGWHVQNFVRVSVQNUYKVRVSVQNUYLVRVSNUYMWEVTRZVVA
      WFZAUYCCWIIZCWJIZWKGZUYJOAVVLUXSUYBBUFZUXSHWLZUYBBUFZWKGUYCAVVJVVMVVKVVOW
      KACWRPZVVJVVMWMACDWNZBCWOVAAVVKVVNUYAUGIZBUFZVVOAVVPVVKVVSWMVVQBCUUAVAAVV
      NUYBVVRBAUYAVVNPURZUYAHPUYBVVRWMAVVNHUYAVVNHVCAUXSHUUBRVFUYAWPVAUUCUUDWQA
      VVMVVOUYCAVVNUYBBAVUAVVNUOPVUBUXSHUUEVAVVTUYBVVTUSQUYAUEVUEVVTVBRAVVNUSUY
      AVVNUSVCAVVNUXSUSUXSHUUFVUFUUGRVFVGWSWTAUXTUYBBVUCVUDUYBVUHWSZWTAVVNUXTUY
      BUXSBVVNUXTWLUUHWMAUXSHUUIRUXSVVNUXTUMZWMAVWBUXSUXSHUUJXARVUBAUYAUXSPURZU
      YBVWCUSQUYAUEVUEVWCVBRAUXSUSUYAVUGVFVGWSUUKUURUULAUAUDZWIIZVWDWJIZWKGZUYH
      VWDUKIZMGZOTZVVLUYJOTUAVICVWDCWMZVWGVVLVWIUYJOVWKVWEVVJVWFVVKWKVWDCWIXBVW
      DCWJXBWQVWKVWHUYIUYHMVWDCUKXBUUMUUNVWJUAVIUUSAUAUUORVUSUUPUUQAUYDFUYOVUIV
      VGAWHRZVVIUYDFOTAUUTRAFUYNFNXCZXDXEGZMGZUYOVWLAUYNVWNVVHVWNQPZAVWNVWMXDXF
      XGXHXIZRZWFVVIAFNFUJGZVWMKXEGZMGZVWOOFVXAOTAFFVWMXJGZVWTMGZVXAOVWMNXEGZVW
      MUNXEGZFVXCOVWMQPZNWRPZUNWRPZXKFVWMOTZNUNOTZURVXDVXEOTVXFVXGVXHVWMXFXIZUV
      AUVBXLVXIVXJXMUVCVQVWMNUNXNVTVXDFVWMXFUVDXAVWMKFWKGZXEGZVWTVWMXJGZVXEVXCV
      WMXOPZVWMNXPZKWRPVXMVXNWMVWMVXKUVEZNVWMWGXQUVFZXRVWMKUVGXSVXLUNVWMXEUVHXT
      VWTXOPVXOVXPVXNVXCWMVWTVWMKXFYAXHUVJVXQVXRVWTVWMUVIXSUVKUVLVWSVXBVWTMFYBU
      VMYCUVNRVXANUYKUJGVWMYDXEGMGNUYLUJGVWMLXEGMGVWONFKYDSYBUVOXRYDUVTYEZYFNUY
      KYDLSNFSYBYGZUVPVXSLYHYEZYFNUYLLXDSNUYKSVXTYGZUVQVYAXDXGYEZYFUVRUVSAVWNUY
      IUYNVWRVVAUYNVIPANUYMSNUYLSVYBYGUWARAVWNVWMJXDXCZXEGZUKIZUYIVWRAVYEVYEQPZ
      AVYEVWMVYDXFJXDYIXGYJZXHZXIZRZNVYEYKTZAVYEVYIUWBZRZWDVVAVWNVYFOTAVWMFKXCZ
      XEGZUKIZVWNVYFOVWNJXEGZUKIZVYQVWNVYRVYPUKVWMXDJMGZXEGZVYRVYPVXOXDVMPJVMPW
      UAVYRWMVXQXGYIVWMXDJUWCXSVYTVYOVWMXEUWDXTYLUWEVWPNVWNYKTVYSVWNWMVWQNVWNWG
      VWQVXFXDWRPNVWMOTZNVWNOTVXKVYCXQVWMXDYMXSYNVWNUWFVTYLVYPVYEOTZVYQVYFOTZVX
      FVYOWRPZVYDWRPZXKVXIVYOVYDOTZURWUCVXFWUEWUFVXKVYOFKVKYAYJZYEZVYDVYHYEXLVX
      IWUGXMFJKXDVKYIYAXGUWGUWHUWIVQVWMVYOVYDXNVTVYPQPZNVYPYKTZURVYGVYLURWUCWUD
      UWJWUJWUKVYPVWMVYOXFWUHXHXIZNVYPWGWULVXFWUEWUBNVYPOTVXKWUIXQVWMVYOYMXSYNV
      QVYGVYLVYJVYMVQVYPVYEUWLVTUWKUWMRAVYECYKTVYFUYIYKTEAVYECVYKVYNVURVUTUWNUW
      OUWPUWQYOYOUWRAUXTJUYBUYDBHABUWSBUYDUWTVUCJHPZAYPRZAWUMJUXTPUXAWUNJHUXSUX
      BVAVWAUYAJWMUYBJUEIZUYDUYAJUEXBWUMWUOUYDWMYPJWPVSUXCAJAUXDJNXPAUXERUXFUXG
      AUYTUYHUYNUHGZUYIMGUYPWUPUYSUYIMKUYFNUYLKUYRFNFYAJUYEYILJYHVLYGZYGSVYBYAJ
      UYQYILUNYHYQYGZYGVKSUXHJUYENUYKJUYQKNKYIWUQSVXTYIWURYASKUXIYRLJNFLUNJNJYH
      VLSYBYHYQYISJUXJYRLJNFLUNYHYISVKYHUXKLJNFLUNLJXCZNFXCZYHYISVKWUSYSWUTYSLU
      XOYRUXLUXMUXNYTYTYTYCAUYHUYNUYIAUYHVUQWSAUYNVVHWSAUYIVVAWSUXPUXQUXR $.
  $}

  ${
    $d N h k n x $.  $d h k m n x z $.  $d n ph $.
    hgt749d.o $e |- O = { z e. ZZ | -. 2 || z } $.
    hgt749d.n $e |- ( ph -> N e. O ) $.
    hgt749d.1 $e |- ( ph -> ( ; 1 0 ^ ; 2 7 ) <_ N ) $.
    $( A deduction version of ~ ax-hgt749 .  (Contributed by Thierry Arnoux,
       15-Dec-2021.) $)
    hgt749d $p |- ( ph
      -> E. h e. ( ( 0 [,) +oo ) ^m NN ) E. k e. ( ( 0 [,) +oo ) ^m NN ) (
         A. m e. NN ( k ` m ) <_ ( 1 . _ 0 _ 7 _ 9 _ 9 _ 5 5 )
      /\ A. m e. NN ( h ` m ) <_ ( 1 . _ 4 _ 1 4 )
      /\ ( ( 0 . _ 0 _ 0 _ 0 _ 4 _ 2 _ 2 _ 4 8 ) x. ( N ^ 2 ) )
       <_ S. ( 0 (,) 1 ) ( ( ( ( ( Lam oF x. h ) vts N ) ` x )
        x. ( ( ( ( Lam oF x. k ) vts N ) ` x ) ^ 2 ) )
        x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u N x. x ) ) ) ) _d x ) ) $=
      ( cc0 c2 cexp co cle wbr cfv cdp2 cmul vn c1 cdc c7 cv c9 c5 cdp cn c4 c8
      wral cioo cvma cof cvts ci cpi cneg ce citg w3a cpnf cico cmap wrex cdvds
      wi wn crab wceq breq2 oveq1 oveq2d wcel oveq2 fveq1d oveq1d oveq12d negeq
      fveq2d adantr itgeq2dv breq12d 3anbi3d rexbidv imbi12d ax-hgt749 eleqtrdi
      cz a1i rspcdva mpd ) AUBLUCMUDUCNOZGPQZFUEZEUEZRUBLUDUFUFUGUGSSSSSUHOPQFU
      IULZWPDUEZRUBUJUBUJSSUHOPQFUIULZLLLLUJMMUJUKSSSSSSSUHOZGMNOZTOZBLUBUMOZBU
      EZUNWSTUOZOZGUPOZRZXEUNWQXFOZGUPOZRZMNOZTOZUQMURTOTOZGUSZXETOZTOZUTRZTOZV
      AZPQZVBZELVCVDOUIVEOZVFZDYDVFZKAWNUAUEZPQZWRWTXAYGMNOZTOZBXDXEXGYGUPOZRZX
      EXJYGUPOZRZMNOZTOZXOYGUSZXETOZTOZUTRZTOZVAZPQZVBZEYDVFZDYDVFZVHZWOYFVHUAM
      CUEVGQVICWJVJZGYGGVKZYHWOUUFYFYGGWNPVLUUIUUEYEDYDUUIUUDYCEYDUUIUUCYBWRWTU
      UIYJXCUUBYAPUUIYIXBXATYGGMNVMVNUUIBXDUUAXTUUIUUAXTVKXEXDVOUUIYPXNYTXSTUUI
      YLXIYOXMTUUIXEYKXHYGGXGUPVPVQUUIYNXLMNUUIXEYMXKYGGXJUPVPVQVRVSUUIYSXRUTUU
      IYRXQXOTUUIYQXPXETYGGVTVRVNWAVSWBWCWDWEWFWFWGUUGUAUUHULABCDEFUAWHWKAGHUUH
      JIWIWLWM $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d ph x y $.
    logdivsqrle.a $e |- ( ph -> A e. RR+ ) $.
    logdivsqrle.b $e |- ( ph -> B e. RR+ ) $.
    logdivsqrle.1 $e |- ( ph -> ( exp ` 2 ) <_ A ) $.
    logdivsqrle.2 $e |- ( ph -> A <_ B ) $.
    $( Conditions for ` ( ( log ` x ) / ( sqrt ` x ) ) ` to be decreasing.
       (Contributed by Thierry Arnoux, 20-Dec-2021.) $)
    logdivsqrle $p |- ( ph
      -> ( ( log ` B ) / ( sqrt ` B ) ) <_ ( ( log ` A ) / ( sqrt ` A ) ) ) $=
      ( vx crp cfv co cle cc0 cr wcel c1 c2 cmul cc a1i vy clog csqrt cdiv cmpt
      cv cpnf ioorp eqcomi wa simpr relogcld rpsqrtcld rpred wne rpsqrtcl rpne0
      cioo syl adantl redivcld fmpttd cneg ccxp cmin caddc ccncf logcld sqrtcld
      cdv rpcn divrecd 2cnd adantr 2ne0 reccld cxpnegd wceq oveq2d eqtrd eqtr4d
      cxpsqrt mpteq2dva cpr reelprrecn rpreccld cres csn cdif crn wf wf1o ax-mp
      logf1o f1of wn ssriv 0nrp ssdifsn mpbir2an feqresmpt dvrelog eqtr3di 1cnd
      wss halfcld negcld cxpcld subcld mulcld dvcxp1 dvmptmul ax-resscn syl3anc
      eqid cncfmptc sylancl cxpcncf1 mulcncf recxpcld remulcld readdcld oveq12d
      sselid 1re fveq1d cvv eqidd fveq2d fvmptd wbr ce 2re clt breqtrrd breqtrd
      wb mpbird eqbrtrd ovex ccnfld ctopn ctx ccn addcn difss cncfmptid divcncf
      ssid cmnf cioc ax-1 jca ellogdm sylibr cncfss relogcn eqeltrrdi cncfmpt2f
      wi mp2an rereccld rpge0 halfre renegcli resubcli relogcl cncfcdm syl21anc
      rpre biimpar eqeltrd cxpadd syl211anc mullidd negsubd cxpneg cxp1d eqtr2d
      mulcomd 3eqtr4rd mul32d oveq1d cicc ioossicc fct2relem sstrd sselda ovexd
      adddird 0red rpcxpcl rpge0d mullidi reefcld eliooord simpld ltled reeflog
      2cn letrd efle sylancr eqbrtrid lemuldivd mpbid divrec2d mulneg1d subnegd
      2rp addlidd 3eqtrd leaddsub lemul1ad mul02d fdvnegge 3brtr3d ) ACHIHUFZUB
      JZUXRUCJZUDKZUEZJBUYBJCUBJZCUCJZUDKZBUBJZBUCJZUDKZLAUABCMUGIUYBMUGURKIUHU
      IZDEAHIUYANAUXRIOZUJZUXSUXTUYKUXRAUYJUKZULUYKUXTUYKUXRUYLUMUNUYJUXTMUOZAU
      YJUXTIOUYMUXRUPUXTUQUSUTZVAVBANUYBVJKZHIPUXRUDKZUXRPQUDKZVCZVDKZRKZUYRUXR
      UYRPVEKZVDKZRKZUXSRKZVFKZUEZINVGKZAUYONHIUXSUYSRKZUEZVJKVUFAUYBVUINVJAHIU
      YAVUHUYKUYAUXSPUXTUDKZRKVUHUYKUXSUXTUYKUXRUYJUXRSOZAUXRVKZUTZUYJUXRMUOZAU
      XRUQZUTZVHZUYKUXRVUMVIUYNVLUYKUYSVUJUXSRUYKUYSPUXRUYQVDKZUDKVUJUYKUXRUYQV
      UMVUPUYKQAQSOZUYJAVMZVNQMUOZUYKVOTVPVQUYKVURUXTPUDUYKVUKVURUXTVRVUMUXRWBU
      SVSVTVSWAWCVSAHUXSUYPUYSVUCNISINNSWDOAWETVUQUYKUXRUYLWFZANUBIWGZVJKNHIUXS
      UEZVJKHIUYPUEAVVCVVDNVJAHSMWHZWIZUBWJZIUBVVFVVGUBWKZAVVFVVGUBWLVVHWNVVFVV
      GUBWOWMTIVVFXEZAVVIISXEZMIOWPHISVULWQZWRISMWSWTTZXAZVSHXBXCUYKUXRUYRVUMAU
      YRSOZUYJAUYQAPAXDZXFZXGZVNZXHZUYKUYRVUBVVRUYKUXRVUAVUMUYKUYRPVVRAPSOZUYJV
      VOVNZXIXHZXJAVVNNHIUYSUEVJKHIVUCUEVRVVQHUYRXKUSXLVTZANSXEZVUFISVGKZOZINVU
      FWKZVUFVUGOZVWDAXMTAHUYTVUDVFUUAUUBJZIVWIXOZVFVWIVWIUUCKVWIUUDKOAVWIVWJUU
      ETAHUYPUYSIAHPUXRIAVVTVVJSSXEZHIPUEVWEOVVOVVJAVVKTZVWKASUUIZTZHPISXPXNAVV
      IVVFSXEHIUXRUEIVVFVGKOVVLSVVEUUFHIVVFUUGXQUUHAHUYRIVVQISUUJMUUKKWIZXEAHIV
      WOUYJVUKUXRNOZUYJUUTZUJUXRVWOOUYJVUKVWQVULUYJVWPUULUUMUXRVWOVWOXOUUNUUOWQ
      TZXRXSAHVUCUXSIAHUYRVUBIAVVNVVJVWKHIUYRUEVWEOVVQVWLVWNHUYRISXPXNAHVUAIAUY
      RPVVQVVOXIVWRXRXSAVUGVWEVVDVWDVWKVUGVWEXEXMVWMINSUUPUVAAVVDVVCVUGVVMUUQUU
      RYDXSUUSAHIVUENUYJVUENOAUYJUYTVUDUYJUYPUYSUYJUXRUXRUVJZVUOUVBUYJUXRUYRVWS
      UXRUVCZUYRNOZUYJUYQUVDUVEZTZXTYAUYJVUCUXSUYJUYRVUBVXCUYJUXRVUAVWSVWTVUANO
      ZUYJUYRPVXBYEUVFZTXTYAUXRUVGYAYBUTVBVWDVWFUJVWHVWGISNVUFUVHUVKUVIUVLGAUAU
      FZBCURKZOZUJZVXFUYOJZVXFVUFJZMLAVXJVXKVRVXHAVXFUYOVUFVWCYFVNVXIVXKVXFHIPU
      YRUXSRKZVFKZVUBRKZUEZJZMLAVXKVXPVRVXHAVXFVUFVXOAHIVUEVXNUYKVUEPVUBRKZVXLV
      UBRKZVFKVXNUYKUYTVXQVUDVXRVFUYKUXRUYRPVCZVFKZVDKZUYSUXRVXSVDKZRKZVXQUYTUY
      KVUKVUNVVNVXSSOVYAVYCVRVUMVUPVVRUYKPVWAXGUXRUYRVXSUVMUVNUYKVXQVUBVYAUYKVU
      BVWBUVOUYKVXTVUAUXRVDUYKUYRPVVRVWAUVPVSWAUYKUYTUYSUYPRKVYCUYKUYPUYSUYKISU
      YPVVKVVBYDVVSUVTUYKUYPVYBUYSRUYKVYBPUXRPVDKZUDKZUYPUYKVUKVUNVVTVYBVYEVRVU
      MVUPVWAUXRPUVQXNUYKVYDUXRPUDUYKUXRVUMUVRVSUVSVSVTUWAUYKUYRVUBUXSVVRVWBVUQ
      UWBYCUYKPVXLVUBVWAUYKUYRUXSVVRVUQXJVWBUWJWAWCYFVNVXIVXPPUYRVXFUBJZRKZVFKZ
      VXFVUAVDKZRKZMLVXIHVXFVXNVYJIVXOYGVXIVXOYHVXIUXRVXFVRZUJZVXMVYHVUBVYIRVYL
      VXLVYGPVFVYLUXSVYFUYRRVYLUXRVXFUBVXIVYKUKZYIVSVSVYLUXRVXFVUAVDVYMUWCYCAVX
      GIVXFAVXGBCUWDKZIVXGVYNXEABCUWETABCMUGIUYIDEUWFUWGUWHZVXIVYHVYIRUWIYJVXIV
      YJMVYIRKMLVXIVYHMVYIVXIPVYGPNOZVXIYETZVXIUYRVYFVXAVXIVXBTVXIVXFVYOULZYAZY
      BVXIUWKZVXIVYIVXIVXFIOZVXDVYIIOVYOVXEVXFVUAUWLXQZUNVXIVYIWUBUWMVXIVYHMLYK
      ZPMVYGVEKZLYKZVXIPUYQVYFRKZWUDLVXIPVYFQUDKZWUFLVXIPQRKZVYFLYKPWUGLYKVXIWU
      HQVYFLQUWTUWNVXIQVYFLYKZQYLJZVYFYLJZLYKZVXIWUJVXFWUKLVXIWUJBVXFVXIQQNOZVX
      IYMTUWOABNOVXHABDUNVNZVXIVXFVYOUNZAWUJBLYKVXHFVNVXIBVXFWUNWUOVXHBVXFYNYKZ
      AVXHWUPVXFCYNYKVXFBCUWPUWQUTUWRUXAVXIWUAWUKVXFVRVYOVXFUWSUSYOVXIWUMVYFNOW
      UIWULYQYMVYRQVYFUXBUXCYRUXDVXIPVYFQVYQVYRQIOVXIUXJTUXEUXFVXIVYFQVXINSVYFX
      MVYRYDZAVUSVXHVUTVNVVAVXIVOTUXGYPVXIWUDMWUFVCZVEKMWUFVFKWUFVXIVYGWURMVEVX
      IUYQVYFAUYQSOVXHVVPVNZWUQUXHVSVXIMWUFVXINSMXMVYTYDVXIUYQVYFWUSWUQXJZUXIVX
      IWUFWUTUXKUXLYOVXIVYPVYGNOMNOWUCWUEYQVYQVYSVYTPVYGMUXMXNYRUXNVXIVYIVXIISV
      YIVVKWUBYDUXOYPYSYSYSUXPAHCUYAUYEIUYBYGAUYBYHZAUXRCVRZUJZUXSUYCUXTUYDUDWV
      CUXRCUBAWVBUKZYIWVCUXRCUCWVDYIYCEUYEYGOAUYCUYDUDYTTYJAHBUYAUYHIUYBYGWVAAU
      XRBVRZUJZUXSUYFUXTUYGUDWVFUXRBUBAWVEUKZYIWVFUXRBUCWVGYIYCDUYHYGOAUYFUYGUD
      YTTYJUXQ $.
  $}

  $( Lemma for ~ tgoldbachgtd .  (Contributed by Thierry Arnoux,
     17-Dec-2021.) $)
  hgt750lem $p |- ( ( N e. NN0 /\ ( ; 1 0 ^ ; 2 7 ) <_ N )
    -> ( ( 7 . _ 3 _ 4 8 ) x. ( ( log ` N ) / ( sqrt ` N ) ) )
      < ( 0 . _ 0 _ 0 _ 0 _ 4 _ 2 _ 2 _ 4 8 ) ) $=
    ( wcel c1 cc0 c2 c7 cexp co cle wbr wa c3 c4 c8 cmul cr ax-mp mp2an clt wb
    cn0 cdc cdp2 cdp clog cfv csqrt cdiv 7nn0 4re 8re pm3.2i dp2cl dpcl a1i 0re
    10re 2nn0 deccl reexpcl 1nn 0nn0 1nn0 c9 1re ltleii declei ltletri remulcld
    9re mp3an elrp mpbir2an relogcl gtneii redivcli cq qssre 4nn0 sselii dp2clq
    crp 8nn0 3nn0 rpdp2cl mpbi simpri 2nn nn0rei 2re eqbrtrri caddc ceu egt2lt3
    1p1e2 loge epr 3rp logltb cc wne wceq 3cn fveq2i 9pos 10pos logleb readdcli
    eqbrtri remulcli nn0zi relogexp mpbir 4lt10 8lt10 dp2lt10 lttri w3a 3pm3.2i
    1lt10 ltexp2a ltmul1i recni oveq2i eqtr3i expgt0 decltc 6nn nngt0i 6nn0 2rp
    cz c6 breqtri simpli 4pos ltmul2i 4cn ltdiv1i dpexpp1 3re nn0re adantr 0lt1
    1lt9 expge1 simpr ltletrd elrpd relogcld rpge0d resqrtcld sqrtgt0d redivcld
    gtned sqrtpclii sqrtgt0ii nn0ssq 8pos rpdpcl ce 2cn mullidi lemul1i lt2addi
    2pos 3ne0 logmul2 3t3e9 9lt10 ltlei decltdi lemul2i eqeltrri relogef rpefcl
    letri 3brtr4i logdivsqrle lemul2ad 3lt10 7p1e8 dplti numexp0 loggt0b expmul
    0z divgt0i 7t2e14 sqrtsq 1lt2 sqrtlt ltdiv2 declt 2exp4 mulridi 7lt10 2lt10
    declti 10nn decnncl2 nnrei cn 8nn dpgti mulcli nnne0i divdiv1 div23i oveq1i
    nnrp mulne0i divassi cmin expp1 sq10 mulcomi 3eqtrri 2p1e3 eqtri expsub 7cn
    4p3e7 addcomli subaddrii 3eqtr2i numexp1 nnzi 3p1e4 3eqtri 3eqtr3i breqtrri
    0dp2dp ltmuldiv2 ltdivmul2 lelttrd ) AUABZCDUBZEFUBZGHZAIJZKZFLMNUCZUCZUDHZ
    AUEUFZAUGUFZUHHZOHVUEUYTUEUFZUYTUGUFZUHHZOHZDDDDMEEVUCUCZUCZUCZUCZUCZUCZUDH
    ZVUBVUEVUHVUEPBZVUBFUABZVUDPBZVUTUILPBZVUCPBZKVVBVVCVVDUUAMPBZNPBZKVVDVVEVV
    FUJUKULMNUMQULLVUCUMQFVUDUNRZUOZVUBVUFVUGVUBAVUBAUYQAPBVUAAUUBUUCZVUBDUYTAD
    PBVUBUPUOZUYTPBZVUBUYRPBZUYSUABZVVKUQEFURUIUSZUYRUYSUTRZUOVVIDUYTSJZVUBDCSJ
    CUYTIJZVVPUUDVVLVVMCUYRIJVVQUQVVNCDCVAVBVCCVDVEVJUUEVFZVGUYRUYSUUFVKDCUYTUP
    VEVVOVHRZUOUYQVUAUUGZUUHUUIZUUJVUBAVVIVUBAVWAUUKUULVUBDVUGVVJVUBAVWAUUMUUOU
    UNZVIVUBVUEVUKVVHVUKPBZVUBVUIVUJUYTWBBZVUIPBZVWDVVKVVPVVOVVSUYTVLVMZUYTVNQZ
    UYTVVOVVSUUPZDVUJUPUYTVVOVVSUUQZVOVPZUOZVIVUSPBZVUBDUABVURPBVWLVBVQPVURVRDV
    UQVBDVUPVBDVUOVBMVUNVSEVUMUREVUCURMNVSUAVQNUURWCVTZWAWAWAWAWAWAWAVTDVURUNRZ
    UOVUBVUHVUKVUEVWBVWKVVHDVUEIJVUBDVUEUPVVGVUTDVUESJZVUEWBBVUTVWOKFVUDUILVUCW
    DMNVSNWBBZVVFDNSJUKUUSNVLVMZWEZWEZUUTVUEVLWFWGVFUOVUBUYTAVWDVUBVWFUOVWAEUVA
    UFZUYTIJZVUBVXAVWTUEUFZVUIIJZEUYSUYRUEUFZOHZVXBVUIIEUYSEOHZIJVXFVXEIJZEVXEI
    JCEOHZEVXFIEUVBUVCCUYSIJZVXHVXFIJZEFCWHUIVCVVRVGDESJVXIVXJTUVFCUYSEVEUYSVVN
    WIZWJUVDQWFWKEVXDIJZVXGEVXDSJVXLCCWLHZEVXDSWOVXMLUEUFZVXNWLHZSJZVXOVXDIJVXM
    VXDSJCVXNSJZVXQVXPWMUEUFZCVXNSWPWMLSJZVXRVXNSJZEWMSJZVXSWNWGWMWBBZLWBBZVXSV
    XTTWQWRWMLWSRWFWKZVYDCCVXNVXNVEVEVYCVXNPBWRLVNQZVYEUVERLLOHZUEUFZVXOVXDILWT
    BLDXAVYCVYGVXOXBXCUVGWRLLUVHVKVYGVDUEUFZVXDIVYFVDUEUVIXDVDUYRIJZVYHVXDIJZVD
    UYRVJUQUVJVFVDWBBZUYRWBBZVYIVYJTVYKVDPBDVDSJVJXEVDVLVMVYLVVLDUYRSJZUQXFUYRV
    LZVMZVDUYRXGRWFXIWKVXMVXOVXDCCVEVEXHVXNVXNVYEVYEXHVYLVXDPBVYOUYRVNQZVHRWKEV
    XDWJVYPUVKQDUYSSJZVXLVXGTEFDWHUIVBDVDUPVJXEVFUVLZEVXDUYSWJVYPVXKUVMQWFEVXFV
    XEWJUYSEVXKWJXJVUIVXEPVYLUYSYLBZVUIVXEXBVYOUYSVVNXKZUYRUYSXLRZVWGUVNUVQREPB
    ZVXBEXBWJEUVOQWUAUVRVWTWBBZVWDVXAVXCTWUBWUCWJEUVPQVWFVWTUYTXGRXMUOVVTUVSUVT
    VULVUSSJZVUBVULUYRVUKOHZSJZWUEVUSSJZWUDVUEUYRSJZWUFVUENSJNUYRSJWUHFVUDNUIVW
    SWCLVUCWDVWRUWAMNVSVWQXNXOXPXPUWBUWCXOVUENUYRVVGVQPNVRVWMVTUQXQRDVUKSJZWUHW
    UFTDVUISJZDVUJSJZWUIWUJCUYTSJZUYRDGHZCUYTSUYRCDVCVBUSZUWDVVLDYLBZVYSXRCUYRS
    JZVYQKWUMUYTSJVVLWUOVYSUQUWGVYTXSWUPVYQXTVYRULUYRDUYSYARWKVWDWUJWULTVWFUYTU
    WEQXMZVWIVUIVUJVWGVWHUWHRVUEUYRVUKVVGUQVWJYBQWFWUGVUKVUSUYRUHHZSJZVUKUYSMOH
    ZUYRFGHZUHHZSJZWVBWURSJZWUSVUKVUIWVAUHHZSJZWVEWVBSJZWVCWVAVUJSJZWVFUYRCMUBZ
    GHZUGUFZWVAVUJSWVAEGHZUGUFZWVKWVAWVLWVJUGUYRFEOHZGHZWVLWVJUYRWTBZVVAEUABZWV
    OWVLXBUYRUQYCZUIURUYRFEUWFVKWVNWVIUYRGUWIYDYEXDWVAPBZDWVAIJWVMWVAXBVVLVVAWV
    SUQUIUYRFUTRZDWVAUPWVTVVLFYLBZVYMDWVASJZUQFUIXKZXFUYRFYFVKZVFWVAUWJRYEWVJUY
    TSJZWVKVUJSJZVVLWVIYLBZVYSXRWUPWVIUYSSJZKWWEVVLWWGVYSUQWVICMVCVSUSZXKZVYTXS
    WUPWWHXTCEMFVCURVSUIXNUWKYGULUYRWVIUYSYARWVJPBZDWVJIJZKVVKDUYTIJZKWWEWWFTWW
    KWWLVVLWVIUABWWKUQWWIUYRWVIUTRZDWVJUPWWNVVLWWGVYMDWVJSJUQWWJXFUYRWVIYFVKVFU
    LVVKWWMVVODUYTUPVVOVVSVFULWVJUYTUWLRWFWKWVSWWBKZVUJPBZWUKKVWEWUJKWVHWVFTWVS
    WWBWVTWWDULZWWPWUKVWHVWIULVWEWUJVWGWUQULWVAVUJVUIUWMVKWFVUIWUTSJZWVGVUIVXEW
    UTSWUAVXDMSJZVXEWUTSJZVXDMEUEUFZOHZSJWXBMSJWWSVXDCYMUBZUEUFZWXBSUYRWXCSJZVX
    DWXDSJZCDYMVCVBYHYMYHYIUWNVYLWXCWBBZWXEWXFTVYOWXGWXCPBDWXCSJWXCCYMVCYJUSWIC
    YMDVAYJVBXFUWSWXCVLVMUYRWXCWSRWFEMGHZUEUFZWXDWXBWXHWXCUEUWOXDEWBBZMYLBWXIWX
    BXBYKMVSXKZEMXLRYEYNWXBMCOHZMSWXACSJZWXBWXLSJZWXAVXRCSVYAWXAVXRSJZVYAVXSWNY
    OWXJVYBVYAWXOTYKWQEWMWSRWFWPYNDMSJZWXMWXNTYPWXACMWXJWXAPBYKEVNQZVEUJYQQWFMY
    RUWPYNVXDWXBMVYPMWXAUJWXQXJUJXQRVYQWWSWWTTVYRVXDMUYSVYPUJVXKYQQWFXIWWBWWRWV
    GTWWDVUIWUTWVAVWGUYSMVXKUJXJZWVTYSQWFVUKWVEWVBVWJVUIWVAVWGWVTDWVAUPWWDVOZVP
    WUTWVAWXRWVTWXSVPZXQRWVBUYRDUBZMOHZWVAUHHZSJZWYCWURSJZWVDWUTWYBSJZWYDUYSWYA
    SJZWYFEUYRFDURWUNUIVBUWQUWRYGWXPWYGWYFTYPUYSWYAMVXKWYAUYRUWTUXAZUXBZUJYBQWF
    WWBWYFWYDTWWDWUTWYBWVAWXRWYAMWYIUJXJZWVTYSQWFWYEWYBWURWVAOHZSJZWYLMWYKWYAUH
    HZSJZMMVUNUDHZWYMSMVUNVSEVUMUREVUCURMNVSNUXCBVWPUXDNUXKQWEWEWEZUXEVUSWVAOHZ
    UYRUHHZWYAUHHZWYQUYRWYAOHZUHHZWYMWYOWYQWTBWVPUYRDXAZKZWYAWTBZWYADXAZKWYSXUA
    XBVUSWVAVUSVWNYCZWVAWVTYCZUXFWVPXUBWVRDUYRUPXFVOZULZXUDXUEWYAWYIYCZWYAWYHUX
    GZULWYQUYRWYAUXHVKWYRWYKWYAUHVUSWVAUYRXUFXUGWVRXUHUXIUXJXUAVUSWVAWYTUHHZOHV
    USUYRMGHZOHZWYOVUSWVAWYTXUFXUGUYRWYAWVRXUJUXFUYRWYAWVRXUJXUHXUKUXLUXMXULXUM
    VUSOXULWVAUYRLGHZUHHZUYRFLUXNHZGHZXUMWYTXUOWVAUHWYTUYRECWLHZGHZXUOXUTUYREGH
    ZUYROHZWYAUYROHWYTWVPWVQXUTXVBXBWVRURUYREUXORXVAWYAUYROUXPUXJWYAUYRXUJWVRUX
    QUXRXUSLUYRGUXSYDUXTYDXUCWWALYLBZKXURXUPXBXUIWWAXVCWWCLWDXKZULUYRFLUYARXUQM
    UYRGFLMUYBXCYRMLFYRXCUYCUYDUYEYDUYFYDDVUOUDHZUYRCGHZOHZXVEUYROHXUNWYOXVFUYR
    XVEOUYRWUNUYGYDXVGDVUPUDHXVAOHDVUQUDHXUOOHXUNDVUOCEVBMVUNVSWYPWEZWOCVAUYHEW
    HUYHZYTDVUPELVBDVUOVBXVHWEZUXSXVIXVDYTDVUQLMVBDVUPVBXVJWEUYIXVDWXKYTUYJMVUN
    VSWYPUYMUYKUYJUYKUYLVVEWYKPBWYAPBZDWYASJZKWYLWYNTUJWURWVAVUSUYRVWNUQXUHVPZW
    VTXJXVKXVLWYIWYAWYHYIULMWYKWYAUYNVKXMWYBPBWURPBWWOWYEWYLTWYJXVMWWQWYBWURWVA
    UYOVKXMWVBWYCWURWXTWYBWVAWYJWVTWXSVPXVMXQRVUKWVBWURVWJWUTWVAWXRWVSWWBWWQYOW
    XSVPXVMXQRVWCVWLVVLVYMKZWUGWUSTVWJVWNVYLXVNVYOVYNWFVUKVUSUYRUYNVKXMVULWUEVU
    SVUEVUKVVGVWJXJUYRVUKUQVWJXJVWNXQRUOUYP $.

  $( Decimal multiplication galore!  (Contributed by Thierry Arnoux,
     26-Dec-2021.) $)
  hgt750lem2 $p |- ( 3 x. ( ( ( ( 1 . _ 0 _ 7 _ 9 _ 9 _ 5 5 ) ^ 2 )
    x. ( 1 . _ 4 _ 1 4 ) ) x. ( ( 1 . _ 4 _ 2 _ 6 3 )
    x. ( 1 . _ 0 _ 3 _ 8 _ 8 3 ) ) ) ) < ( 7 . _ 3 _ 4 8 ) $=
    ( c3 c1 cc0 c7 c9 c5 cdp co c2 c4 c6 c8 wcel 1nn0 4nn0 0nn0 eqid caddc 2nn0
    cdc cdp2 cmul clt wbr cr wa cle cn0 0re 7re 9re 5re pm3.2i dp2cl ax-mp dpcl
    mp2an crp cn nnrp rpdp2cl rpdpcl rpre remulcli 7nn0 9nn0 5nn0 5lt10 dp2lt10
    6re 7p1e8 dp2ltsuc 8nn0 dp2lt dplt rpge0 mpbi recni 6nn0 deccl 10pos nn0cni
    8re dec0h addridi 6cn addlidi decadd 4cn 1t1e1 oveq12i oveq2i eqtri 3eqtr4i
    dp0u 10nn0 dec10p ax-1cn addcomi 6p1e7 oveq1i 8cn 8p1e9 3eqtri dpmul4 lttri
    decaddc 3nn0 3lt10 9cn 2cn eqtr3i mulridi 4p1e5 dpmul 7cn addcomli decaddci
    2p1e3 decaddi 6p3e9 deceq1i 5p1e6 mulcomli 5cn 1p1e2 dpadd decsuc 4p2e6 4re
    dpadd3 2re 3re 3rp mul01i 3p1e4 6p4e10 0cn 3cn 2p2e4 resqcli 4nn 1re sqge0i
    rpgt0 ltleii mulge0i 5nn 8nn rpdp2cl2 9lt10 dp20u breqtrri wb lt2sqi sqvali
    cexp 4lt10 8t8e64 7p4e11 9t9e81 3eqtr4ri ltmul1ii 1lt10 8lt10 9p1e10 9p2e11
    eqbrtri addcli 6t4e24 7t4e28 7t2e14 8t7e56 8t2e16 6p6e12 6p2e8 4p4e8 9p5e14
    mulcomi 3eqtr3i 3eqtr2i 4p3e7 8p6e14 7nn ltmul12a 6lt10 2t3e6 9t2e18 7t3e21
    9t7e63 9p6e15 eqeltrri cc 4t4e16 9t4e36 5p5e10 8t5e40 5t3e15 mullidi 8p5e13
    9t6e54 7t6e42 7t7e49 3p2e5 5p4e9 ltmul2i dp2eq2i eqtr2i 3t2e6 4t3e12 mul02i
    9nn 3pos eqtr4i eqeltri 9p4e13 3t3e9 wceq eqeq1i 7p2e9 00id ) ABCDEEFFUAZUA
    ZUAZUAZUAZGHZIUUQHZBJBJUAZUAZGHZUBHZBJIKAUAZUAZUAZGHZBCALLAUAZUAZUAZUAZGHZU
    BHZUBHZUBHZAIJJEUAZUAZGHZUBHZUCUDZVUHDAJLUAZUAZGHZUCUDVUDVULUCUDVUCVUGUCUDZ
    VUIVUCBKFBUAZUAZGHZBJUYQUAZGHZUBHZUCUDZVUSVUGUCUDVUMUYLUEMZVUPUEMZUFZCUYLUG
    UDZUYLVUPUCUDZUFZUFVUBUEMZVURUEMZUFZCVUBUGUDZVUBVURUCUDZUFZUFVUTVVCVVFVVAVV
    BUYHUYKUYGBUHMZUYFUEMZUYGUEMNCUEMZUYEUEMZUFVVNVVOVVPUIDUEMZUYDUEMZUFVVPVVQV
    VRUJEUEMZUYCUEMZUFVVRVVSVVTUKVVSUYBUEMZUFVVTVVSVWAUKFUEMZVWBUFVWAVWBVWBULUL
    UMFFUNUOUMEUYBUNUOUMEUYCUNUOUMDUYDUNUOUMCUYEUNUOBUYFUPUQZUUAZUYKURMZUYKUEMB
    UYJNJUYIOBJNJUSMJURMUUBJUTUOVAVAVBZUYKVCUOZVDZVVMVUOUEMZVVBNKUEMZVUNUEMZUFV
    WIVWJVWKVJVWBBUEMZUFVWKVWBVWLULUUCUMFBUNUOUMKVUNUNUOBVUOUPUQZUMVVDVVECUYHUG
    UDCUYKUGUDVVDUYGVWCUUDCUYKUIVWGVWECUYKUCUDVWFUYKUUEUOZUUFUYHUYKVWDVWGUUGUQU
    YLBBKDUAZUAZGHZUYKUBHZUCUDZVWRVUPUCUDVVEUYHVWQUCUDZVWSUYHBCLCUAZUAZGHZIUUQH
    ZUCUDZVXDVWQUCUDVWTUYGVXCUCUDZVXEBUYFVXBNCUYEPDUYDVEEUYCVFEUYBVFFFVGFUSMFUR
    MUUHFUTUOZVAZVAZVAZVAZVAZCVXAPLUUIUUJZVAZCUYEVXAPVXKVXMUYELVXAUCDUYDLVEVXJE
    UYCVFVXIUUKEUYBVFVXHUUKFFVGVXGVHVHVIVIVIVKVLLVMUULUUMVNVOCUYGUGUDZCVXCUGUDZ
    VXFVXEUUNUYGURMVXOBUYFNVXLVBUYGVPUOVXCURMVXPBVXBNVXNVBVXCVPUOUYGVXCVWCVVMVX
    BUEMZVXCUEMNVVOVXAUEMZUFVXQVVOVXRUILUEMZVVOUFVXRVXSVVOWCUIUMLCUNUOUMCVXAUNU
    OBVXBUPUQZUUOUQVQVXDVXCVXCUBHVWQUCVXCVXCVXTVRUUPBCLCCCBKKJBCLCBCCBKTZCCKJTZ
    BBKDNPVMPNVMPPPPNBKNVSVTZPPKJVSOVTZPPNVSVSONNVSVEUURWAWAVYACTZCKJVYAKTZJVYE
    CTZVYBVYACVYCPVTPVSOVYGQVYBQZVYACCKVYAKVYEKVYCPPVSVYEQKVSWDVYAVYAVYCWBWEKWF
    WGZWHJWIWGZWHBBUBHBBCGHZVYKUBHBCCUAZGHZWJVYKBVYKBUBBNWOZVYNWKVYMVYKBVYLCBGC
    PUULZWLVYNWMZWNLLUBHVYBLCGHZVYQUBHVYBVYLGHZUUSVYQLVYQLUBLVMWOZVYSWKVYRVYBCG
    HVYBVYLCVYBGVYOWLVYBVYDWOWMZWNBCTZCTZBVYAKBBTZKTDWUBBTZVYFWUACWPPVTNVYCVSWU
    DQVYFQWUACBKWUCKWUBVYAWPPNVSWUBQVYAQZBWQZVYIWHBKRHZKBRHZDBKWRWFWSWTWMZWHBDT
    ZVYBRHLBTZVYMVYAVYLGHZRHZVYRRHVYKVYQRHZWUNUBHZBDKJLBWUJVYBNVEVSOWUJQVYHWUGB
    RHDBRHLWUGDBRWUIXAVKWMNUUTXGWUMWUJVYRVYBRWUMBVYARHWUJVYMBWULVYARVYPWULVYACG
    HVYAVYLCVYAGVYOWLVYAVYCWOWMWKCBBKBDBVYAPNNVSBNWDZWUEBWRWGZWUIWHWMVYTWKWUOEE
    UBHWUKWUNEWUNEUBWUNBLRHZLBRHZEVYKBVYQLRVYNVYSWKBLWRXBWSZXCXDZWVAWKUVAWMUVBX
    EUVHUYHVXDVWQVWDVXCVXTUUAVVMVWPUEMZVWQUEMNVWLVWOUEMZUFWVBVWLWVCUUCVWJVVQUFW
    VCVWJVVQVJUJUMKDUNUOUMBVWOUNUOBVWPUPUQZXFUQUYHVWQUYKVWDWVDVWGVWNUVCVQBBKDAL
    BBCBBJBJBFJWUAEIEBKFBNNVSVENNVGOOONWPVFSVFXHVMNNPNNVSVGNUVDXIUVEWUAETZICEWU
    CCTZBWVEITZEWUAEWPVFVTZSPVFWVGQZEVFWDZWUAECBWUCCWVECRHBWPVFPNWVEWVEWVHWBWEW
    UPBCCBBBWUACRHBNPPNCWQWUPBWRWEZWUQWHPUVFXGNEIRHIERHWUCEIXJXKWSUVGXLZXGBBBJC
    BCBFJBJNNNOPPVGOWJJBUBHZBJUBHZJJBWIWRUVSZJWIXMZXLZWJWVMJWVNCJTZWVPWVOJOWDZU
    VTBJRHZCRHZFCFTWWAWVTJBRHFWVTBJWRWIUVIWEJBWIWRWSXNUWAFVGWDWMWVKXOKDBJIKAEAL
    DIJTZVSVENOSXHXHVMKWFXMZUVJDXPXMUVKDWWBRHZIRHABTZIRHAATWWDWWEIRWWBDRHWWDWWE
    WWBDWWBIJSOVTWBXPWSIJBAWWBDSOVEWWBQZXSNDJWUCXPWIUUTXQZXRXLXAABAWWEIXHNSWWEQ
    IBAXKWRXSXQZXTWMYAXOBFTZJTZBCBTZBTZCVYAFTBWWJBTZWVFWWIJBFNVGVTZOVTNWWKBCBPN
    VTZNVTPWWMQWUCWWLCBWWKBWUPYBYBWWIJWWKBVYAFWWJWWLWWNOWWONWWJQZWWLQWWIBRHWWIW
    WKRHVYABWWKWWIRWUPWLBFKWWIBNVGNWWIQZYCXTXLXNWHWVKWHDLGHZILGHZUBHIBTZLJUAGHZ
    BBGHKDGHZRHZBJGHZWXDRHZUBHBFJUAGHWUAEIUAGHRHZEALUAGHZRHZDLILKBJTZDWWTLJVYAF
    KTZVEVMSVMVSVEVMOUVLLDWXJXBXPUVMYDUVNUUSVYAWXJRHZKRHDITZKRHDLTWXKWXLKRBKFKD
    IVYAWXJNVSVGVSWUEWXJQBFRHZBRHWUHDWXMKBRFBKYEWRYCXQZXAWTWMSUVOXGXADILWXLKVES
    VSWXLQZKILWFXKUVPXQXTWMBJBIWXIDNOVEWXIQZYFNWWGXRZXOWXCWWRWXEWWSUBBBKDDLNNVS
    VEVEVMBBKDDLWUCKDTZNNVSVEWUCQWXRQWUIDBLXPWRVKXQZWHYGBJBJILNONOSVMBJBJILWXIW
    XINONOWXPWXPYFUVQWHYGWKWXHBITZJKUAGHZWXGRHWXAWXFWYAWXGRBFJWUAEIWXTJKNVGOWPV
    FBINSVTZSOVSWWIJWVEIWXTJTZKWWJWVGWWNOWVHSWWPWVIBFWUAEWXTJWWIWVENVGWPVFWWQWV
    EQBBIBWUARHNNYFWUABWUCWUAWPWBZWRWUFXQYHOEFWXIXJYEUVRXQXGYIWHYKXAWXTJKEALWWT
    LJWYBOVSVFXHIBSNVTZVMVMOWYCKEATZLWWTLTJWYCKTZWYFLTZWXTJWYBOVTVSEAVFXHVTVMWY
    GQWYHQWWTDLWYCWYFRHWYEVEVKWXTJEAWWTDWYCWYFWYBOVFXHWYCQWYFQBIBIWXTENSVFWXTQZ
    YFNWVLXRUWBWHYHOLKWXIXBWFUWCXQXGYKWMWNXEUYLVWRVUPVWHVWQUYKWVDVWGVDVWMXFUQUM
    UMVVIVVLVVGVVHUYPVUAVVMUYOUEMZUYPUEMZNJUEMZUYNUEMZUFWYJWYLWYMYJIUEMZUYMUEMZ
    UFWYMWYNWYOYLVWJAUEMZUFWYOVWJWYPVJYMUMKAUNUOUMIUYMUNUOUMJUYNUNUOBUYOUPUQZVV
    MUYTUEMZVUAUEMZNVVOUYSUEMZUFWYRVVOWYTUIWYPUYRUEMZUFWYTWYPXUAYMVXSUYQUEMZUFX
    UAVXSXUBWCVXSWYPUFXUBVXSWYPWCYMUMLAUNUOZUMLUYQUNUOUMAUYRUNUOUMCUYSUNUOBUYTU
    PUQZVDZVVMVUQUEMZVVHNWYLXUBUFXUFWYLXUBYJXUCUMJUYQUNUOBVUQUPUQZUMVVJVVKCUYPU
    GUDZCVUAUGUDZVVJUYPURMXUHBUYONJUYNOIUYMSKAVSYNVAZVAZVAZVBUYPVPUOZVUAURMXUIB
    UYTNCUYSPAUYRXHLUYQVMLAVMYNVAZVAZVAZVAZVBVUAVPUOZUYPVUAWYQXUDUUGUQVUBBJIDUA
    ZUAZGHZBCAEUAZUAZGHZUBHZUCUDZXVEVURUCUDVVKWYKXVAUEMZUFZXUHUYPXVAUCUDZUFZUFW
    YSXVDUEMZUFZXUIVUAXVDUCUDZUFZUFXVFXVHXVJWYKXVGWYQVVMXUTUEMZXVGNWYLXUSUEMZUF
    XVOWYLXVPYJWYNVVQUFXVPWYNVVQYLUJUMIDUNUOUMJXUSUNUOBXUTUPUQZUMXUHXVIXUMBUYOX
    UTNXULJXUSOIDSDUSMDURMUWDDUTUOZVAZVAJUYNXUSOXUKXVSIUYMDSXUJXVRKADVSYNXIWTVL
    VNVNVOUMUMXVLXVNWYSXVKXUDVVMXVCUEMZXVKNVVOXVBUEMZUFXVTVVOXWAUIWYPVVSUFXWAWY
    PVVSYMUKUMAEUNUOUMCXVBUNUOBXVCUPUQZUMXUIXVMXURBUYTXVCNXUQCXVBPAEXHEUSMEURMU
    XLEUTUOZVAZVACUYSXVBPXUPXWDAUYREXHXUOXWCLUYQEVMXUNLAVMYNUVEXIVIXCVLVNVNVOUM
    UMUYPXVAVUAXVDUWEUQBJIDFACLIKBCAEBJCLBKWUABJLANOSVENXHOPPVFNVMNVSWPVGXHPVMS
    VSNOVMXHUWFVHXIWUKKBCCLTZITZKWUKKTZWUALBVMNVTZVSNPXWGQZWUAQZWUKBRHLITXWFLBI
    WUKVMNYFWUKQZYHLXWEILVMWDZYBWMKWFWEWHBJBCCBCBJCJCNONPPPOPWJBWRYOWVPJCUBHCCC
    TZJWIYOCPWDZWMZJCRHZCRHXWPJWVRXWPJCRJWIWEZXAXWQWVSXDWVKXOIDAEKKJWUAFAWWTBLT
    ZSVEXHVFVSOVGXHUWGEIXWRXJXKUWHYDUWIEDKATZXJXPUWJYDZWWTXWRRHZKRHAETZKRHJFTXX
    AXXBKRIBBLAEWWTXWRSNNVMWWTQZXWRQXSWURWUSEWUTXCWMZWHXAAEFJXXBKXHVFVSXXBQZYPV
    GUWKXRWMYQXOWXICTZBXWEIWXILTAXXFBTZXWFWXICBJNOVTZPVTNLXWEUHXWLVMUWLZSXXGQXW
    FQWXICLXXFXWEXXHPXXIXXFQZXWECLLXWEUWMXWLXBUWLYRLCRHXWECRHLLXWECRXWLXALXBWEX
    LXQXTWWHWHJBGHZJEGHZUBHICTZCEUAGHZWXDIDGHRHZVYKAEGHRHZUBHBJCUAGHLBKUAGHRHZW
    UAFAUAGHZRHZJBJECVYAJXXMCEJAKTZONOVFPOPVFUWNEJXXTXJWIUWOYDWVQEBCETZXJWREBUB
    HEXYAEXJXMWVJWMYDJXXTRHZCRHJCTZCRHXYCXYBXYCCRXXTJXYCXXTAKXHVSVTWBWIAKCJXXTJ
    XHVSOXXTQYPPYQXRXQXAXYCXYCJCOPVTWBWEWMBKCIVYAJNVSOWUEYFPYQXRXOXXOXXKXXPXXLU
    BBJIDJBNOSVEONBJIDJBWXIIDTZNOSVEWXPXYDQBIRHZBRHABRHJXYEABRWWHXAYPWMNWWGXGYG
    BCAEJENPXHVFOVFBCAEJEWUAXXBNPXHVFXWJXXEABJYSWRYPXQEXJWGWHYGWKXXSEFKUAGHZXXR
    RHXXNXXQXYFXXRRBJCLBKEFKNOPVMNVFVSVGVSWXICWUKKEFTZKXXFXWGXXHPXWHVSXXJXWIBJL
    BEFWXIWUKNOVMNWXPXWKXXDXNWHVYIWHYKXAEFKWUAFAXXMCEVFVGVSWPVGICSPVTZXHPVFXYGK
    WUAFTZAXXMCTEXYGKTZXYIATZEFVFVGVTVSWUAFWPVGVTXHXYJQXYKQEFWUAFXXMCXYGXYIVFVG
    WPVGXYGQXYIQZEWUARHZBRHBETZBRHXXMXYMXYNBRWUAEXYNWYDXJEWQXQXABECIXYNBNVFNXYN
    QYFPUVFXRWMPUWPXGYAWHYKWMWNXEVUBXVEVURXUEXVAXVDXVQXWBVDXUGXFUQUMUMUYLVUPVUB
    VURUWEUQBKFBAAICLJBJLAIIJXXMJIJITZIJJENVSVGNNVMSOOXHSXYHOSJIOSVTZXHXHSPVMOS
    OOVFUURXIXIXXMJTZIJIXXMLTZJXYQITZXYOXXMJXYHOVTZSOSXYSQZXYOQZXXMJLXYQJXYHOOX
    YQQZUVQXTYTWHBKBJIBBIIJKJNVSNOSNSOWJWVQWWCUVJKJRHZIRHWUAIRHWXTYUDWUAIRYQXAI
    WQWMYFXOFBLACXYCIXYOAALWWIVGNVMXHPSXHXHLFXYCXBYEUWQYDUWRLXBUWSBAUBHACATAYSU
    WSAXHWDWMLWWIRHZCRHIATZCRHYUFYUEYUFCRWWILYUFWWIWWNWBXBBFAIWWILNVGVMWWQYFXHL
    FBATZXBYEUWTXQXRXQXAYUFYUFIASXHVTWBWEWMJCIXYCIOPSXYCQIXKWGZXTXOIITZJTZBXXML
    WWBJTEYUJBTZXYRYUIJIISSVTZOVTNXYHVMYUKQXYRQYUIJICWWBJYUJXXMYULOSPYUJQZXXMQZ
    IIJYUIISSSYUIQZYTXTXWQWHXXDWHYUIKKUAGHZXYOAAUAGHZRHVYBEEUAGHZIIJUAGHXXMJIUA
    GHRHZYUQRHBKGHFBGHRHZWXDLAGHRHZUBHZYUIKKXYOAAVYBEEYULVSVSXYPXHVYDXHVFVFYUIK
    TZKXYOATZAVYBETEYVCKTZYVDATZYUIKYULVSVTVSXYOAXYPXHVTXHYVEQYVFQYUIKXYOAVYBEY
    VCYVDYULVSXYPXHYVCQYVDQIIJIKJYUIXYOSSOSYUOYUBJIKWIXKYIXQZYTWHYAWHYAWHYKYUSY
    UPYUQRIIJXXMJIYUIKKSSOXYHOYULSVSVSYUIJXYQIYVCKYUJXYSYULOXYTSYUMYUAIIXXMJYUI
    KYUIXYQSSXYHOYUOYUCXXMIYUIXXMXYHWBXKICIXXMISPSYUNYUHXTXQYVGWHYIWHYKXAYVBWXB
    EDGHZUBHYURYUTWXBYVAYVHUBBKFBKDNVSVGNVSVEBKFBKDVYAFBTZNVSVGNWUEYVIQWXNWTWHY
    GBJLAEDNOVMXHVFVEBJLAEDWXILATZNOVMXHWXPYVJQXXDUWBWHYGWKKDEDJFJTZWUAVYBEEXWS
    XYOVSVEVFVEOWPVFVFEKYVKXJWFUXAYDDKXYOXPWFUXBYDXWTUXCXWSXYORHZJRHXYIJRHWVEYV
    LXYIJRKAJIWUAFXWSXYOVSXHOSXWSQYUBYQUXDWHXAWUAFEXYIJWPVGOXYLUXEXTWMFJBCKJYVK
    WUAVGONPYVKQXWJYCXWQWHXOWMUVBXEVUCVUSVUGUYLVUBVWHXUEVDZVUPVURVWMXUGVDVUGURM
    VUGUEMIVUFSJVUEOJEOXWCVAVAVBVUGVCUOZXFUQCAUCUDVUMVUIUUNUXMVUCVUGAYVMYVNYMUX
    FUOVQVUHACVYLUAZGHZVUGUBHVULUCAYVPVUGUBYVPACGHZAYVOCAGYVOVYLCVYLCCVYOUXGVYO
    WMWLAXHWOZUXHXAACCCCCBJDCIJJEDICWXIDCCDAJLXHPPPSOSPOVFVEXXHVEPPPPNOVEPVEXHO
    VMWAWAWAWXIDTZCTZYVTYVSCWXIDXXHVEVTZPVTWBWEACIJCKBDICCWXTXHPSOPNSPUXIJAWXTW
    IYSUXJYDIXKUXKJCXWMWIYRXWOYDCWXTRHZCRHWXTCRHWXTYWBWXTCRCCBIBICWXTPPNSXWNWYI
    WUQYUHWHXAWXTWXTWYBWBWEWMWTXOCCGHZXXLUBHZCCVYLGHZYWDCXXLUBHCYWCCXXLUBCPWOZX
    AXXLXXLJUHMVVSXXLUEMOUKJEUPUQVRUXKWMYWEYWCCVYLCCGVYOWLYWFWMZUXNWXLCTZBWXIDD
    ATZJTLYWHBTZYVSWXLCDIVESVTZPVTNXXHVEYWJQYVSQZWXLCBJYWIJYWHWXIYWKPNOYWHQZWXP
    DIAWXLVESXSWXOYHVYJWHWXSWHYVQYWCRHZIJGHXXLRHZUBHZWWTECUAGHZDICUAZGHZWXIDCUA
    ZGHZRHZYWERHZYWPYVQDAGHZUBHYWQYWNYVQYWOYXDUBYWNYVQCRHYVQYWCCYVQRYWFWLYVQYVQ
    AUWMYVRYSUXOWEWMIJJEDASOOVFVEXHIJJEDAWWBJETZSOOVFWWFYXEQIJRHZBRHWUHDYXFKBRY
    VGXAWTWMXHEJYUGXJWIUXPXQXGYGWKACDACWWTCWWTECCEXHPVEXHPPVFPDAWWTXPYSUWIYDUXQ
    DCCXPYRDXPYOYDACXWMYSYRACUBHCXWMAYSYOXWNWMYDECRHZCRHZXYAUXRCERHZCRHZXYAUXRY
    XHYXGEXYAYXGECREXJWEZXAYXKWVJXDYXHYXJXYAYXGYXICRECXJYRWSXAUXSVQIBBWWTCSNPXX
    CWVKXTXOWMYXCYXBCRHYXBYWQYWECYXBRYWGWLYXBYWSYXAYWSDUHMYWRUEMZYWSUEMVEWYNVVO
    UFYXLWYNVVOYLUIUMICUNUODYWRUPUQVRYXAWXIUHMYWTUEMZYXAUEMXXHVVQVVOUFYXMVVQVVO
    UJUIUMDCUNUOWXIYWTUPUQVRUVIWEDICWXIDCWWTECVESPXXHVEWYEPVFPWXLCYVSCWWTETCYWH
    YVTYWKPYWAPYWMYVTQDIWXIDWWTEWXLYVSVESXXHVEWXOYWLWXIDWWTWXIXXHWBXPWXQXQDIEXP
    XKUXTXQWHUYAWHYKXDUXNXEUVHVUDVUHVULAVUCYMYVMVDAVUGYMYVNVDVULURMVULUEMDVUKVE
    AVUJXHJLOLUSMLURMUUILUTUOVAVAVBVULVCUOXFUQ $.

  ${
    $d A m n $.  $d H m $.  $d K m $.  $d P m n $.  $d Q m n $.  $d m n ph $.
    hgt750lemf.a $e |- ( ph -> A e. Fin ) $.
    hgt750lemf.p $e |- ( ph -> P e. RR ) $.
    hgt750lemf.q $e |- ( ph -> Q e. RR ) $.
    hgt750lemf.h $e |- ( ph -> H : NN --> ( 0 [,) +oo ) ) $.
    hgt750lemf.k $e |- ( ph -> K : NN --> ( 0 [,) +oo ) ) $.
    hgt750lemf.0 $e |- ( ( ph /\ n e. A ) -> ( n ` 0 ) e. NN ) $.
    hgt750lemf.1 $e |- ( ( ph /\ n e. A ) -> ( n ` 1 ) e. NN ) $.
    hgt750lemf.2 $e |- ( ( ph /\ n e. A ) -> ( n ` 2 ) e. NN ) $.
    hgt750lemf.3 $e |- ( ( ph /\ m e. NN ) -> ( K ` m ) <_ P ) $.
    hgt750lemf.4 $e |- ( ( ph /\ m e. NN ) -> ( H ` m ) <_ Q ) $.
    $( Lemma for the statement 7.50 of [Helfgott] p. 69.  (Contributed by
       Thierry Arnoux, 1-Jan-2022.) $)
    hgt750lemf $p |- ( ph -> sum_ n e. A
       ( ( ( Lam ` ( n ` 0 ) ) x. ( H ` ( n ` 0 ) ) )
    x. ( ( ( Lam ` ( n ` 1 ) ) x. ( K ` ( n ` 1 ) ) )
      x. ( ( Lam ` ( n ` 2 ) ) x. ( K ` ( n ` 2 ) ) ) ) )
    <_ ( ( ( P ^ 2 ) x. Q ) x. sum_ n e. A ( ( Lam ` ( n ` 0 ) )
           x. ( ( Lam ` ( n ` 1 ) ) x. ( Lam ` ( n ` 2 ) ) ) ) ) ) $=
      ( cmul co cc0 cv cfv cvma c1 c2 csu cexp cle wcel wa cn cr vmaf ffvelcdmd
      a1i cpnf cico rge0ssre adantr sselid remulcld resqcld recnd mul4d mulcomd
      wf mulcld oveq2d 3eqtr3d wbr vmage0 syl mulge0d cxr pnfxr icogelb syl3anc
      0xr wceq breq1d wral ralrimiva rspcdva lemul12ad sqvald breqtrrd lemul1ad
      fveq2 eqtrd eqbrtrrd fsumle fsummulc2 ) ABUAFUBZUCZUDUCZWOGUCZSTZUEWNUCZU
      DUCZWSHUCZSTZUFWNUCZUDUCZXCHUCZSTZSTZSTZFUGBCUFUHTZDSTZWPWTXDSTZSTZSTZFUG
      XJBXLFUGSTUIABXHXMFIAWNBUJZUKZWRXGXOWPWQXOULUMWOUDULUMUDVGXOUNUPZNUOZXOUA
      UQURTZUMWQUSXOULXRWOGAULXRGVGXNLUTNUOZVAZVBXOXBXFXOWTXAXOULUMWSUDXPOUOZXO
      XRUMXAUSXOULXRWSHAULXRHVGXNMUTZOUOZVAZVBXOXDXEXOULUMXCUDXPPUOZXOXRUMXEUSX
      OULXRXCHYBPUOZVAZVBVBVBXOXJXLAXJUMUJXNAXIDACJVCZKVBZUTZXOWPXKXQXOWTXDYAYE
      VBZVBZVBXOWQXAXESTZSTZXLSTZXHXMUIXOXLYNSTWRXKYMSTZSTYOXHXOWPXKWQYMXOWPXQV
      DZXOXKYKVDZXOWQXTVDZXOYMXOXAXEYDYGVBZVDZVEXOXLYNXOWPXKYQYRVHXOWQYMYSUUAVH
      VFXOYPXGWRSXOWTXDXAXEXOWTYAVDXOXDYEVDXOXAYDVDXOXEYGVDVEVIVJXOYNXJXLXOWQYM
      XTYTVBYJYLXOWPXKXQYKXOWOULUJUAWPUIVKNWOVLVMXOWTXDYAYEXOWSULUJUAWTUIVKOWSV
      LVMXOXCULUJUAXDUIVKPXCVLVMVNVNXOYNDCCSTZSTZXJUIXOWQDYMUUBXTADUMUJXNKUTYTA
      UUBUMUJXNACCJJVBUTXOUAVOUJZUQVOUJZWQXRUJUAWQUIVKUUDXOVSUPZUUEXOVPUPZXSUAU
      QWQVQVRXOXAXEYDYGXOUUDUUEXAXRUJUAXAUIVKUUFUUGYCUAUQXAVQVRZXOUUDUUEXEXRUJU
      AXEUIVKUUFUUGYFUAUQXEVQVRZVNXOEUBZGUCZDUIVKZWQDUIVKEULWOUUJWOVTUUKWQDUIUU
      JWOGWIWAAUULEULWBXNAUULEULRWCUTNWDXOXACXECYDACUMUJXNJUTZYGUUMUUHUUIXOUUJH
      UCZCUIVKZXACUIVKEULWSUUJWSVTUUNXACUIUUJWSHWIWAAUUOEULWBXNAUUOEULQWCUTZOWD
      XOUUOXECUIVKEULXCUUJXCVTUUNXECUIUUJXCHWIWAUUPPWDWEWEAXJUUCVTXNAXJDXISTUUC
      AXIDAXIYHVDADKVDVFAXIUUBDSACACJVDWFVIWJUTWGWHWKWLABXLXJFIAXJYIVDXOXLYLVDW
      MWG $.
  $}

  ${
    $d F b $.  $d L a b $.  $d N a b c $.  $d R c $.  $d T a b c $.
    $d ph a b c $.
    hgt750lemg.f $e |- F = ( c e. R |-> ( c o. T ) ) $.
    hgt750lemg.t $e |- ( ph -> T : ( 0 ..^ 3 ) -1-1-onto-> ( 0 ..^ 3 ) ) $.
    hgt750lemg.n $e |- ( ph -> N : ( 0 ..^ 3 ) --> NN ) $.
    hgt750lemg.l $e |- ( ph -> L : NN --> RR ) $.
    hgt750lemg.1 $e |- ( ph -> N e. R ) $.
    $( Lemma for the statement 7.50 of [Helfgott] p. 69.  Applying a
       permutation ` T ` to the three factors of a product does not change the
       result.  (Contributed by Thierry Arnoux, 1-Jan-2022.) $)
    hgt750lemg $p |- ( ph -> ( ( L ` ( ( F ` N ) ` 0 ) )
      x. ( ( L ` ( ( F ` N ) ` 1 ) ) x. ( L ` ( ( F ` N ) ` 2 ) ) ) )
     = ( ( L ` ( N ` 0 ) ) x. ( ( L ` ( N ` 1 ) ) x. ( L ` ( N ` 2 ) ) ) ) ) $=
      ( cc0 cfv c1 c2 wcel cn ffvelcdmd cvv vb va cmul co ctp cprod 2fveq3 tpfi
      cv cfn a1i c3 cfzo wf1o wceq wb fzo0to3tp f1oeq23 mp2an sylib wa eqidd cr
      wf adantr simpr eleqtrrdi recnd fprodf1o ccom cmpt coeq1d f1of ovexd fexd
      syl coexg syl2anc fvmptd fveq1d wfun cdm f1ofun f1odm eleq2d biimpar fvco
      eqtr2d prodeq2dv c0ex 1ex tpid1 eleqtrrid eqtrd eleqtrri eqeltrd 1eltp012
      fveq2d wne 0ne1 2ex tpid3 0ne2 1ne2 prodtp 3eqtr3d mulassd ) AMFDNZNZENZO
      XHNZENZUCUDPXHNZENZUCUDZMFNZENZOFNZENZUCUDPFNZENZUCUDZXJXLXNUCUDUCUDXQXSY
      AUCUDUCUDAMOPUEZUAUIZXHNZENZUAUFZYCUBUIZFNZENZUBUFZXOYBAYKYCYDCNZFNZENZUA
      UFYGAYCYJYCYNUBUACYLYHYLEFUGYCUJQAMOPUHUKAMULUMUDZYOCUNZYCYCCUNZIYOYCUOZY
      RYPYQUPUQUQYOYCYOYCCURUSUTZAYDYCQZVAZYLVBAYHYCQZVAZYJUUCRVCYIEARVCEVDUUBK
      VEUUCYORYHFAYORFVDUUBJVEUUCYHYCYOAUUBVFUQVGSSVHVIAYCYNYFUAUUAYMYEEUUAYEYD
      FCVJZNZYMUUAYDXHUUDAXHUUDUOYTAGFGUIZCVJZUUDBDTDGBUUGVKUOAHUKAUUFFUOZVAUUF
      FCAUUHVFVLLAFBQCTQUUDTQLAYOYOTCAYPYOYOCVDIYOYOCVMVPZAMULUMVNVOFCBTVQVRVSZ
      VEVTUUACWAZYDCWBZQZUUEYMUOAUUKYTAYPUUKIYOYOCWCVPZVEAUUMYTAUULYCYDAYQUULYC
      UOYSYCYCCWDVPZWEWFYDFCWGVRWHWRWIWHAMOPYFUAXJXLXNTTTYDMEXHUGYDOEXHUGMTQAWJ
      UKZOTQAWKUKZAXJARVCXIEKAXIMCNZFNZRAXIMUUDNZUUSAMXHUUDUUJVTAUUKMUULQUUTUUS
      UOUUNAMYCUULMOPWJWLZUUOWMMFCWGVRWNAYORUURFJAYOYOMCUUIMYOQAMYCYOUVAUQWOUKZ
      SSWPSVHZAXLARVCXKEKAXKOCNZFNZRAXKOUUDNZUVEAOXHUUDUUJVTAUUKOUULQUVFUVEUOUU
      NAOYCUULWQUUOWMOFCWGVRWNAYORUVDFJAYOYOOCUUIOYOQAOYCYOWQUQWOUKZSSWPSVHZMOW
      SAWTUKZYDPEXHUGPTQAXAUKZAXNARVCXMEKAXMPCNZFNZRAXMPUUDNZUVLAPXHUUDUUJVTAUU
      KPUULQUVMUVLUOUUNAPYCUULMOPXAXBZUUOWMPFCWGVRWNAYORUVKFJAYOYOPCUUIPYOQAPYC
      YOUVNUQWOUKZSSWPSVHZMPWSAXCUKZOPWSAXDUKZXEAMOPYJUBXQXSYATTTYHMEFUGYHOEFUG
      UUPUUQAXQARVCXPEKAYORMFJUVBSSVHZAXSARVCXREKAYOROFJUVGSSVHZUVIYHPEFUGUVJAY
      AARVCXTEKAYORPFJUVOSSVHZUVQUVRXEXFAXJXLXNUVCUVHUVPXGAXQXSYAUVSUVTUWAXGXF
      $.
  $}

  ${
    $d O z $.
    hgt750leme.o $e |- O = { z e. ZZ | -. 2 || z } $.
    $( Two ways to write the set of odd primes.  (Contributed by Thierry
       Arnoux, 27-Dec-2021.) $)
    oddprm2 $p |- ( Prime \ { 2 } ) = ( O i^i Prime ) $=
      ( cprime c2 csn cdif cin cv wcel cdvds wn wa ancom cz wb prmz reqabi baib
      wbr syl pm5.32i bitr2i nnoddn2prmb elin 3bitr4i eqriv ) ADEFGZBDHZAIZDJZE
      UJKTLZMZUJBJZUKMZUJUHJUJUIJUOUKUNMUMUNUKNUKUNULUKUJOJZUNULPUJQUNUPULULABO
      CRSUAUBUCUJUDUJBDUEUFUG $.

    hgt750leme.n $e |- ( ph -> N e. NN ) $.
    ${
      $d A c d i j n u $.  $d N c i j n u $.  $d ph c i j n u $.
      hgt750lemb.2 $e |- ( ph -> 2 <_ N ) $.
      hgt750lemb.a $e |-
        A = { c e. ( NN ( repr ` 3 ) N ) | -. ( c ` 0 ) e. ( O i^i Prime ) } $.
      $( An upper bound on the contribution of the non-prime terms in the
         Statement 7.50 of [Helfgott] p. 69.  (Contributed by Thierry Arnoux,
         28-Dec-2021.) $)
      hgt750lemb $p |- ( ph -> sum_ n e. A ( ( Lam ` ( n ` 0 ) )
             x. ( ( Lam ` ( n ` 1 ) ) x. ( Lam ` ( n ` 2 ) ) ) )
      <_ ( ( log ` N ) x. (
               sum_ i e. ( ( ( 1 ... N ) \ Prime ) u. { 2 } ) ( Lam ` i )
            x. sum_ j e. ( 1 ... N ) ( Lam ` j ) ) ) ) $=
        ( cc0 cfv c1 c2 cn wcel a1i vd vu cv cvma cmul csu clog cfz cprime cdif
        co csn cun c3 crepr cfn wss nnnn0d cn0 3nn0 ssidd reprfi2 cin wn ssrab3
        ssfi sylancl wa cr wf vmaf cfzo adantr simpr sselid reprf c0ex eleqtrri
        cz fzo0to3tp ffvelcdmd 2ex remulcld fsumrecl nnrpd relogcld cle wbr w3a
        elfz1b biimpri syl3anc sselda crp syl vmage0 letrd lemul2ad nncnd recnd
        reprle fsummulc2 sumeq2dv cop cmpt adantl wral wceq sylib fveq1 opeq12d
        cc fvex op1std fveq2d op2ndd oveq12d cvv opex ad2antrr ad4ant13 adantlr
        ffnd 3eqtr4d caddc cmin sumeq1d ad4antr reprsum fveq2 3jca wne 3eqtr3rd
        sumtp addcld addrsub mpbid ad3antrrr vex syldan nnzd ctp tpid1 1eltp012
        tpid3 fzfi diffi ax-mp snfi mp2an difss snssd unssd fz1ssnn sstrd fzfid
        unfi 2nn relogcl vmalelog logleb biimpa syl21anc fsumle mulcomd mulassd
        nnne0d logcld eqtrd eqtr2d breqtrd nnred logge0d crn c1st c2nd cxp xpfi
        nnge1d syl2anc xp1st sseldd xp2nd mulge0d reqabi simprbi oddprm2 eleq2i
        sylnibr eldif sylibr wb uncom undif3 eqtri ssequn1 eqtrid eleq2d mpbird
        jca difeq1d opelxpd ralrimiva cbvmptv rnmptss fsumless wf1o rgenw fnmpt
        wfn wi eqidd fvmpt2d fvmptd3 3eqtr3d opth2 simpld simprd oveq2d 3pm3.2i
        mp1i 1ex 0ne1 0ne2 1ne2 ad5antr w3o eleqtrdi eltp eqfnfvd ex ralrimivva
        mpjao3dan anasss dff1o6 fsumf1o adantrl anassrs adantrr 3eqtrrd 3brtr3d
        fsummulc1 fsumxp ) ACNFUCZOZUDOZPVUDOZUDOZQVUDOZUDOZUEUKZUEUKZFUFZGUGOZ
        CVUFVUHUEUKZFUFZUEUKZVUNPGUHUKZUIUJZQULZUMZDUCZUDOZDUFZVUREUCZUDOZEUFZU
        EUKZUEUKACVULFARGUNUOOUKZUPSCVVIUQCUPSARUNGAGKURUNUSSZAUTTARVAVBNIUCZOZ
        HUIVCZSZVDZIVVICMVEZVVICVFVGZAVUDCSZVHZVUFVUKVVSRVIVUEUDRVIUDVJZVVSVKTZ
        VVSNUNVLUKZRNVUDVVSRVUDUNGVVSRVAZAGVSSZVVRAGKUUAZVMZVVJVVSUTTZVVSCVVIVU
        DVVPAVVRVNZVOZVPZNVWBSZVVSNNPQUUBZVWBNPQVQUUCVTVRZTWAZWAZVVSVUHVUJVVSRV
        IVUGUDVWAVVSVWBRPVUDVWJPVWBSZVVSPVWLVWBUUDVTVRZTWAZWAZVVSRVIVUIUDVWAVVS
        VWBRQVUDVWJQVWBSZVVSQVWLVWBNPQWBUUEVTVRZTZWAZWAZWCZWCZWDAVUNVUPAGAGKWEW
        FZACVUOFVVQVVSVUFVUHVWOVWSWCZWDZWCAVUNVVHVXGAVVDVVGAVVAVVCDVVAUPSZAVUSU
        PSZVUTUPSVXJVURUPSZVXKPGUUFZVURUIUUGUUHQUUIVUSVUTUUQUUJTZAVVBVVASZVHZRV
        IVVBUDVVTVXPVKTAVVARVVBAVVAVURRAVUSVUTVURVUSVURUQAVURUIUUKTAQVURAQRSZGR
        SZQGWGWHZQVURSZVXQAUURTKLVXTVXQVXRVXSWIGQWJWKWLUULZUUMVURRUQAGUUNZTZUUO
        ZWMWAZWDAVURVVFEAPGUUPZAVVEVURSZVHZRVIVVEUDVVTVYHVKTAVURRVVEVYCWMWAZWDZ
        WCZWCAVUMCVUFVUHVUNUEUKZUEUKZFUFZVUQWGACVULVYMFVVQVXFVVSVUFVYLVWOVVSVUH
        VUNVWSVVSGWNSZVUNVISVVSGAVXRVVRKVMWEZGUUSWOZWCZWCVVSVUKVYLVUFVXEVYRVWOV
        VSVUERSNVUFWGWHVWNVUEWPWOVVSVUJVUNVUHVXDVYQVWSVVSVUGRSNVUHWGWHVWRVUGWPW
        OVVSVUJVUIUGOZVUNVXDVVSVUIVVSVUIVXCWEZWFVYQVVSVUIRSVUJVYSWGWHVXCVUIUUTW
        OVVSVUIWNSZVYOVUIGWGWHZVYSVUNWGWHZVYTVYPVVSRVUDUNGQVWCVWFVWGVWIVXBXAWUA
        VYOVHWUBWUCVUIGUVAUVBUVCWQWRWRUVDAVUQCVUNVUOUEUKZFUFVYNACVUOVUNFVVQAGAG
        KWSZAGKUVGUVHZVVSVUOVXHWTZXBACWUDVYMFVVSWUDVUOVUNUEUKVYMVVSVUNVUOAVUNXL
        SVVRWUFVMZWUGUVEVVSVUFVUHVUNVVSVUFVWOWTVVSVUHVWSWTWUHUVFUVIXCUVJUVKAVUP
        VVHVUNVXIVYKVXGAGAGKUVLAGKUVSUVMAUACNUAUCZOZPWUIOZXDZXEZUVNZUBUCZUVOOZU
        DOZWUOUVPOZUDOZUEUKZUBUFVVAVURUVQZWUTUBUFZVUPVVHWGAWVAWUTWUNUBAVXJVXLWV
        AUPSVXNVYFVVAVURUVRUVTAWUOWVASZVHZWUQWUSWVDRVIWUPUDVVTWVDVKTZWVDVVARWUP
        AVVARUQWVCVYDVMWVCWUPVVASAWUOVVAVURUWAXFUWBZWAZWVDRVIWURUDWVEWVDVURRWUR
        VYBWVCWURVURSAWUOVVAVURUWCXFVOZWAZWCWVDWUQWUSWVGWVIWVDWUPRSNWUQWGWHWVFW
        UPWPWOWVDWURRSNWUSWGWHWVHWURWPWOUWDAVVLPVVKOZXDZWVASZICXGWUNWVAUQAWVLIC
        AVVKCSZVHZVVLWVJVVAVURWVNVVLVVASZVVLVURUIVUTUJZUJZSZWVNVVLVURSZVVLWVPSZ
        VDZVHWVRWVNWVSWWAWVNVVLRSZVXRVVLGWGWHZWVSWVNVWBRNVVKWVNRVVKUNGWVNRVAZAV
        WDWVMVWEVMZVVJWVNUTTZWVNCVVIVVKVVPAWVMVNZVOZVPZVWKWVNVWMTZWAZAVXRWVMKVM
        ZWVNRVVKUNGNWWDWWEWWFWWHWWJXAWVSWWBVXRWWCWIGVVLWJWKWLWVNWVMWWAWWGWVMVVN
        WVTWVMVVKVVISZVVOVVOICVVIMUWEUWFWVPVVMVVLBHJUWGUWHUWIWOUWTVVLVURWVPUWJU
        WKAWVOWVRUWLWVMAVVAWVQVVLAVVAVUTVURUMZWVPUJZWVQVVAVUTVUSUMWWOVUSVUTUWMV
        UTVURUIUWNUWOAWWNVURWVPAVUTVURUQWWNVURXHVYAVUTVURUWPXIUXAUWQUWRVMUWSWVN
        WVJRSZVXRWVJGWGWHZWVJVURSZWVNVWBRPVVKWWIVWPWVNVWQTZWAZWWLWVNRVVKUNGPWWD
        WWEWWFWWHWWSXAWWRWWPVXRWWQWIGWVJWJWKWLUXBUXCICWVKWVAWUMUAICWULWVKWUIVVK
        XHWUJVVLWUKWVJNWUIVVKXJPWUIVVKXJXKUXDZUXEWOZUXFAWUNWUTCVUOUBFWUMVUEVUGX
        DZWUOWXCXHZWUQVUFWUSVUHUEWXDWUPVUEUDVUEVUGWUONVUDXMZPVUDXMZXNXOWXDWURVU
        GUDVUEVUGWUOWXEWXFXPXOXQVVQAWUMCUXJZWUNWUNXHZVVKWUMOZVUDWUMOZXHZVVKVUDX
        HZUXKZFCXGICXGZCWUNWUMUXGZWVKXRSZICXGWXGAWXPICVVLWVJXSZUXHICWVKWUMXRWXA
        UXIUYAAWUNUXLAWXMIFCCAWVMVVRWXMWVNVVRVHZWXKWXLWXRWXKVHZDVWBVVKVUDWXSVWB
        RVVKWVNVWBRVVKVJVVRWXKWWIXTYCWXSVWBRVUDAVVRVWBRVUDVJWVMWXKVWJYAYCWXSVVB
        VWBSZVHZVVBNXHZVVBVVKOZVVBVUDOZXHVVBPXHZVVBQXHZWYAWYBVHZVVLVUEWYCWYDWXS
        VVLVUEXHZWXTWYBWXSWYHWVJVUGXHZWXSWVKWXCXHWYHWYIVHWXSWXIWXJWVKWXCWXRWXKV
        NWXRWXIWVKXHZWXKWVNWYJVVRAICWVKWUMXRWUMICWVKXEXHAWXATWXPWVNWXQTUXMVMVMW
        XRWXJWXCXHZWXKAVVRWYKWVMVVSIVUDWVKWXCCWUMXRWXAWXLVVLVUEWVJVUGNVVKVUDXJP
        VVKVUDXJXKVWHWXCXRSVVSVUEVUGXSTUXNZYBVMUXOVVLWVJVUEVUGWXEWXFUXPXIZUXQZX
        TWYGVVBNVVKWYAWYBVNZXOWYGVVBNVUDWYOXOYDWYAWYEVHZWVJVUGWYCWYDWXSWYIWXTWY
        EWXSWYHWYIWYMUXRZXTWYPVVBPVVKWYAWYEVNZXOWYPVVBPVUDWYRXOYDWYAWYFVHZQVVKO
        ZVUIWYCWYDWYSGVVLWVJYEUKZYFUKZGVUEVUGYEUKZYFUKZWYTVUIWYSXUAXUCGYFWYSVVL
        VUEWVJVUGYEWXSWYHWXTWYFWYNXTWXSWYIWXTWYFWYQXTXQUXSWYSXUAWYTYEUKZGXHWYTX
        UBXHWYSVWBVVEVVKOZEUFVWLXUFEUFGXUEWYSVWBVWLXUFEVWBVWLXHWYSVTTZYGWYSRVVK
        UNGEWYSRVAZWVNVWDVVRWXKWXTWYFWWEYHZVVJWYSUTTZWVNWWMVVRWXKWXTWYFWWHYHYIW
        YSNPQXUFEVVLWVJWYTXRXRXRVVENVVKYJVVEPVVKYJVVEQVVKYJWYSVVLXLSZWVJXLSZWYT
        XLSZWVNXUKVVRWXKWXTWYFWVNVVLWWKWSYHZWVNXULVVRWXKWXTWYFWVNWVJWWTWSYHZWVN
        XUMVVRWXKWXTWYFWVNWYTWVNVWBRQVVKWWIVWTWVNVXATWAWSYHZYKNXRSZPXRSZQXRSZWI
        WYSXUQXURXUSVQUYBWBUXTTZNPYLWYSUYCTZNQYLWYSUYDTZPQYLWYSUYETZYNYMWYSXUAW
        YTGWYSVVLWVJXUNXUOYOXUPAGXLSWVMVVRWXKWXTWYFWUEUYFZYPYQWYSXUCVUIYEUKZGXH
        VUIXUDXHWYSVWBVVEVUDOZEUFVWLXVFEUFGXVEWYSVWBVWLXVFEXUGYGWYSRVUDUNGEXUHX
        UIXUJWXSVUDVVISZWXTWYFAVVRXVGWVMWXKVWIYAXTYIWYSNPQXVFEVUEVUGVUIXRXRXRVV
        ENVUDYJVVEPVUDYJVVEQVUDYJWYSVUEXLSZVUGXLSZVUIXLSZWXRXVHWXKWXTWYFAVVRXVH
        WVMVVSVUEVWNWSYBYRZWXRXVIWXKWXTWYFAVVRXVIWVMVVSVUGVWRWSYBYRZWXRXVJWXKWX
        TWYFAVVRXVJWVMVVSVUIVXCWSYBYRZYKXUTXVAXVBXVCYNYMWYSXUCVUIGWYSVUEVUGXVKX
        VLYOXVMXVDYPYQYDWYSVVBQVVKWYAWYFVNZXOWYSVVBQVUDXVNXOYDWYAVVBVWLSWYBWYEW
        YFUYGWYAVVBVWBVWLWXSWXTVNVTUYHVVBNPQDYSZUYIXIUYMUYJUYKUYNUYLWXOWXGWXHWX
        NWIIFCWUNWUMUYOWKWLWYLAWUOWUNSZVHZWUTXVQWUQWUSAXVPWVCWUQVISAWUNWVAWUOWX
        BWMZWVGYTAXVPWVCWUSVISXVRWVIYTWCWTUYPAVVHVVAVVCVVGUEUKZDUFVVAVURVVCVVFU
        EUKZEUFZDUFWVBAVVAVVCVVGDVXNAVVGVYJWTVXPVVCVYEWTZVUBAVVAXVSXWADVXPVURVV
        FVVCEVXLVXPVXMTXWBVXPVYGVHVVFAVXOVYGVVFVISZAVYGXWCVXOVYIUYQZUYRWTXBXCAU
        BVVAVURXVTWUTDEWUOVVBVVEXDXHZWUQVVCWUSVVFUEXWEWUPVVBUDVVBVVEWUOXVOEYSZX
        NXOXWEWURVVEUDVVBVVEWUOXVOXWFXPXOXQVXNVYFAVXOVYGVHVHZXVTXWGVVCVVFAVXOVV
        CVISVYGVYEUYSXWDWCWTVUCUYTVUAWRWQ $.

      $d F e n $.  $d N a c d e n $.  $d O a c d e n $.  $d ph a d e n $.
      hgt750lema.f $e |- F = ( d e. { c e. ( NN ( repr ` 3 ) N ) | -. ( c ` a )
        e. ( O i^i Prime ) } |-> ( d o. if ( a = 0 , ( _I |` ( 0 ..^ 3 ) ) , (
        ( pmTrsp ` ( 0 ..^ 3 ) ) ` { a , 0 } ) ) ) ) $.
      $( An upper bound on the contribution of the non-prime terms in the
         Statement 7.50 of [Helfgott] p. 69.  (Contributed by Thierry Arnoux,
         1-Jan-2022.) $)
      hgt750lema $p |- ( ph -> sum_ n e. ( ( NN ( repr ` 3 ) N )
         \ ( ( O i^i Prime ) ( repr ` 3 ) N ) )
      ( ( Lam ` ( n ` 0 ) ) x. ( ( Lam ` ( n ` 1 ) ) x. ( Lam ` ( n ` 2 ) ) ) )
      <_ ( 3 x. sum_ n e. A ( ( Lam ` ( n ` 0 ) )
             x. ( ( Lam ` ( n ` 1 ) ) x. ( Lam ` ( n ` 2 ) ) ) ) ) ) $=
        ( cc0 cfv wcel cn cvma ve c3 cfzo co cv cprime wn crepr crab ciun c1 c2
        cin cmul csu cdif cle cfn fzofi a1i nnnn0d cn0 ssidd reprfi2 wss ssrab2
        3nn0 ssfid adantr wa cr wf vmaf cz nn0zd ad2antrr simpr sselid ctp c0ex
        reprf tpid1 fzo0to3tp eleqtrri ffvelcdmd 1eltp012 tpid3 remulcld vmage0
        2ex wbr syl mulge0d fsumiunle eqid inss2 prmssnn sstri reprdifc sumeq1d
        chash wceq sselda fsumrecl recnd fsumconst syl2anc fveq1 fveq2d oveq12d
        cid cres cpr cpmtr cif 3nn ralrimivw r19.21bi eleq1d cbvrabv reprpmtf1o
        cc notbid eqidd adantlr fsumf1o fveq1d cbvsumv cvv pmtridf1o hgt750lemg
        fveq2 ovexd sumeq2dv 3eqtrrd hashfzo0 ax-mp eqcomd 3eqtr4rd 3brtr4d ) A
        HPUBUCUDZHUEZIUEZQZGUFUMZRZUGZISFUBUHQZUDZUIZUJZPDUEZQZTQZUKUULQZTQZULU
        ULQZTQZUNUDZUNUDZDUOUUAUUJUUTDUOZHUOZUUIUUEFUUHUDUPZUUTDUOUBCUUTDUOZUNU
        DZUQAHUUAUUJUUTDUUAURRZAPUBUSUTZAUUJURRUUBUUARZAUUIUUJASUBFAFLVAZUBVBRZ
        AVGUTZASVCZVDZUUJUUIVEAUUGIUUIVFZUTVHVIZAUVHVJZUULUUJRZVJZUUNUUSUVRSVKU
        UMTSVKTVLZUVRVMUTZUVRUUASPUULUVRSUULUBFUVRSVCAFVNRZUVHUVQAFUVIVOZVPUVJU
        VRVGUTUVRUUJUUIUULUVNUVPUVQVQZVRWAZPUUARZUVRPPUKULVSZUUAPUKULVTWBWCWDZU
        TZWEZWEZUVRUUPUURUVRSVKUUOTUVTUVRUUASUKUULUWDUKUUARZUVRUKUWFUUAWFWCWDZU
        TWEZWEZUVRSVKUUQTUVTUVRUUASULUULUWDULUUARZUVRULUWFUUAPUKULWJWGWCWDZUTWE
        ZWEZWHZWHUVRUUNUUSUWJUWSUVRUUMSRPUUNUQWKUWIUUMWIWLUVRUUPUURUWNUWRUVRUUO
        SRPUUPUQWKUWMUUOWIWLUVRUUQSRPUURUQWKUWQUUQWIWLWMWMWNAUVCUUKUUTDAHSUUEUU
        JUBFIUUJWOUVLUUESVEAUUEUFSGUFWPWQWRUTUVIUVKWSWTAUUAPUUCQZUUERZUGZIUUIUI
        ZUUTDUOZHUOZUUAXAQZUXDUNUDZUVBUVEAUVFUXDYBRUXEUXGXBUVGAUXDAUXCUUTDAUUIU
        XCUVMUXCUUIVEAUXBIUUIVFUTZVHAUULUXCRZVJZUUNUUSUXJSVKUUMTUVSUXJVMUTZUXJU
        UASPUULUXJSUULUBFUXJSVCAUWAUXIUWBVIUVJUXJVGUTAUXCUUIUULUXHXCWAZUWEUXJUW
        GUTWEWEUXJUUPUURUXJSVKUUOTUXKUXJUUASUKUULUXLUWKUXJUWLUTWEWEUXJSVKUUQTUX
        KUXJUUASULUULUXLUWOUXJUWPUTWEWEWHWHZXDXEUUAUXDHXFXGAUUAUVAUXDHUVPUXDUUJ
        PUAUEZEQZQZTQZUKUXOQZTQZULUXOQZTQZUNUDZUNUDZUAUOZUUJPUULEQZQZTQZUKUYEQZ
        TQZULUYEQZTQZUNUDZUNUDZDUOZUVAUVPUXCUUTUUJUYCDUAEUXOUULUXOXBZUUNUXQUUSU
        YBUNUYOUUMUXPTPUULUXOXHXIUYOUUPUXSUURUYAUNUYOUUOUXRTUKUULUXOXHXIUYOUUQU
        XTTULUULUXOXHXIXJXJUVOUVPSUUEUUJUBUUBPXBXKUUAXLUUBPXMUUAXNQQXOZEFUXCUUB
        JAUBSRZHUUAAUYQHUUAUYQAXPUTXQXRAUWAUVHUWBVIUVPSVCAUVHVQZUXBPJUEZQZUUERZ
        UGIJUUIUUCUYSXBZUXAVUAVUBUWTUYTUUEPUUCUYSXHXSYCXTUUGUUBUYSQZUUERZUGIJUU
        IVUBUUFVUDVUBUUDVUCUUEUUBUUCUYSXHXSYCXTUYPWOZOYAUVPUXNUUJRVJUXOYDUVPUXI
        VJUUTAUXIUUTVKRUVHUXMYEXEYFUYDUYNXBUVPUUJUYCUYMUADUXNUULXBZUXQUYGUYBUYL
        UNVUFUXPUYFTVUFPUXOUYEUXNUULEYLZYGXIVUFUXSUYIUYAUYKUNVUFUXRUYHTVUFUKUXO
        UYEVUGYGXIVUFUXTUYJTVUFULUXOUYEVUGYGXIXJXJYHUTUVPUUJUYMUUTDUVRUUJUYPETU
        ULJOUVRUUAUYPYIUUBPUVRPUBUCYMUVPUVHUVQUYRVIUWHVUEYJUWDUVTUWCYKYNYOYNAUB
        UXFUVDUXDUNAUXFUBUXFUBXBZAUVJVUHVGUBYPYQUTYRACUXCUUTDCUXCXBANUTWTXJYSYT
        $.
    $}

    $d H m $.  $d K m $.  $d N a c d e i j m n $.  $d O a c d e i j m n z $.
    $d a c e i j m n ph $.
    hgt750leme.0 $e |- ( ph -> ( ; 1 0 ^ ; 2 7 ) <_ N ) $.
    hgt750leme.h $e |- ( ph -> H : NN --> ( 0 [,) +oo ) ) $.
    hgt750leme.k $e |- ( ph -> K : NN --> ( 0 [,) +oo ) ) $.
    hgt750leme.1 $e |- ( ( ph /\ m e. NN ) ->
              ( K ` m ) <_ ( 1 . _ 0 _ 7 _ 9 _ 9 _ 5 5 ) ) $.
    hgt750leme.2 $e |- ( ( ph /\ m e. NN ) ->
              ( H ` m ) <_ ( 1 . _ 4 _ 1 4 ) ) $.
    $( An upper bound on the contribution of the non-prime terms in the
       Statement 7.50 of [Helfgott] p. 69.  (Contributed by Thierry Arnoux,
       29-Dec-2021.) $)
    hgt750leme $p |- ( ph ->
       sum_ n e. ( ( NN ( repr ` 3 ) N ) \ ( ( O i^i Prime ) ( repr ` 3 ) N ) )
       ( ( ( Lam ` ( n ` 0 ) ) x. ( H ` ( n ` 0 ) ) )
    x. ( ( ( Lam ` ( n ` 1 ) ) x. ( K ` ( n ` 1 ) ) )
      x. ( ( Lam ` ( n ` 2 ) ) x. ( K ` ( n ` 2 ) ) ) ) )
    <_ ( ( ( 7 . _ 3 _ 4 8 ) x. ( ( log ` N ) / ( sqrt ` N ) ) )
         x. ( N ^ 2 ) ) ) $=
      ( cn co cmul wcel cr vd vc ve va vi vj c3 cfv cprime cdif cc0 cv cvma csu
      c1 c2 c7 c9 c5 cdp2 cdp cexp c4 wn crab cdiv cfn cn0 3nn0 a1i ssidd diffi
      c8 syl wa wf cz adantr reprf fzo0to3tp eleqtrri ffvelcdmd rge0ssre sselid
      vmaf remulcld fsumrecl 3re 1nn0 0nn0 7nn0 9nn0 ax-mp rpdp2cl rpdpcl rpred
      crp nnrp resqcld wss wceq sselda 4re 8re dp2cl dpcl mp2an cle 0re 9re 5re
      pm3.2i 1re wbr cdc 2re 10nn0 2nn0 nn0rei ltleii declei clt letrd rpexpcld
      2nn rpmulcld lemul2d mpbid recnd mulcld c6 vmage0 fsumge0 remulcli oveq2d
      cchp mulcomd eqtrd mulassd eqtr4d crepr cin clog nnnn0d reprfi2 cfzo nnzd
      csqrt simpr eldifad ctp c0ex tpid1 cpnf cico 1eltp012 2ex tpid3 5nn0 4nn0
      5nn fveq1 eleq1d notbid cbvrabv ssrab3 ssfi sylancl nnrpd relogcld rpge0d
      4nn nnred resqrtcld rpsqrtcld rpne0d redivcld 7re hgt750lemf cid cres cpr
      cpmtr cif ccom cmpt deccl nn0expcli numexp1 eqeltri 1nn 2lt9 breqtrri w3a
      1z nn0zi 3pm3.2i 1lt10 1lt9 leexp2 biimpa eqid hgt750lema 2z sqcld cc 3cn
      mul12d breqtrd cfz csn cun fzfi snfi fz1ssnn ssdifssd snssd unssd chpvalz
      unfi chpf eqeltrrd hgt750lemb hgt750lemd fzfid hgt750lemc ltmul12ad ltled
      3rp 1lt2 ltletrd rplogcld resqcli hgt750lem2 rpdivcld lemul1d mpbii mul4d
      6re div32d divcld sqvald oveq1d divassd divsqrtid 3eqtrd 3eqtrrd 3brtr4d
      ) APGUGUUAUHZQZHUIUUBZGVUIQZUJZUKDULZUHZUMUHZVUOEUHZRQZUOVUNUHZUMUHZVUSFU
      HZRQZUPVUNUHZUMUHZVVCFUHZRQZRQZRQZDUNZUGUOUKUQURURUSUSUTZUTZUTZUTZUTZVAQZ
      UPVBQZUOVCUOVCUTZUTZVAQZRQZUKUAULZUHZVUKSZVDZUAVUJVEZVUPVUTVVDRQZRQZDUNZR
      QZRQZUQUGVCVMUTZUTZVAQZGUUCUHZGUUHUHZVFQZRQZGUPVBQZRQZAVUMVVHDAVUJVGSZVUM
      VGSAPUGGAGJUUDUGVHSZAVIVJAPVKUUEZVUJVULVLVNZAVUNVUMSZVOZVURVVGVXEVUPVUQVX
      EPTVUOUMPTUMVPZVXEWEVJZVXEUKUGUUFQZPUKVUNVXEPVUNUGGVXEPVKAGVQSZVXDAGJUUGZ
      VRVXAVXEVIVJVXEVUNVUJVULAVXDUUIUUJVSZUKVXHSZVXEUKUKUOUPUUKZVXHUKUOUPUULUU
      MVTWAZVJWBZWBZVXEUKUUNUUOQZTVUQWCVXEPVXQVUOEAPVXQEVPVXDLVRVXOWBWDWFVXEVVB
      VVFVXEVUTVVAVXEPTVUSUMVXGVXEVXHPUOVUNVXKUOVXHSZVXEUOVXMVXHUUPVTWAZVJWBZWB
      ZVXEVXQTVVAWCVXEPVXQVUSFAPVXQFVPVXDMVRZVXTWBWDWFVXEVVDVVEVXEPTVVCUMVXGVXE
      VXHPUPVUNVXKUPVXHSZVXEUPVXMVXHUKUOUPUUQUURVTWAZVJWBZWBZVXEVXQTVVEWCVXEPVX
      QVVCFVYBVYEWBWDWFWFWFWGZAUGVWIUGTSZAWHVJZAVVTVWHAVVPVVSAVVOAVVOVVOWQSAUOV
      VNWIUKVVMWJUQVVLWKURVVKWLURVVJWLUSUSUUSUSPSUSWQSUVAUSWRWMWNWNWNWNWNWOVJZW
      PWSAVVSVVSWQSAUOVVRWIVCVVQUUTUOVCWIVCPSVCWQSUVLVCWRWMWNWNWOVJZWPWFZAVWEVW
      GDAVWTVWEVUJWTZVWEVGSVXBUKUBULZUHZVUKSZVDZUBVUJVWEVWDVYQUAUBVUJVWAVYNXAZV
      WCVYPVYRVWBVYOVUKUKVWAVYNUVBUVCUVDUVEZUVFZVUJVWEUVGUVHAVUNVWESZVOZVUPVWFW
      UBPTVUOUMVXFWUBWEVJZWUBVXHPUKVUNWUBPVUNUGGWUBPVKAVXIWUAVXJVRVXAWUBVIVJAVW
      EVUJVUNVYMAVYTVJXBVSZVXLWUBVXNVJWBWBWUBVUTVVDWUBPTVUSUMWUCWUBVXHPUOVUNWUD
      VXRWUBVXSVJWBWBWUBPTVVCUMWUCWUBVXHPUPVUNWUDVYCWUBVYDVJWBWBWFWFWGZWFZWFZAV
      WQVWRAVWMVWPVWMTSZAUQVHSVWLTSZWUHWKVYHVWKTSZVOWUIVYHWUJWHVCTSZVMTSZVOWUJW
      UKWULXCXDXLVCVMXEWMXLUGVWKXEWMUQVWLXFXGZVJZAVWNVWOAGAGJUVIZUVJZAGAGJUVMZA
      GWUOUVKUVNZAVWOAGWUOUVOZUVPZUVQZWFAGWUQWSZWFZAVVIVVTUGVWHRQZRQZVWJXHAVVIV
      VTVUMVWGDUNZRQZWVEVYGAVVTWVFAVVPVVSAVVOVVOTSZAUOVHSZVVNTSZWVHWIUKTSZVVMTS
      ZVOWVJWVKWVLXIUQTSZVVLTSZVOWVLWVMWVNUVRURTSZVVKTSZVOWVNWVOWVPXJWVOVVJTSZV
      OWVPWVOWVQXJUSTSZWVRVOWVQWVRWVRXKXKXLUSUSXEWMXLURVVJXEWMXLURVVKXEWMXLUQVV
      LXEWMXLUKVVMXEWMUOVVNXFXGZVJZWSVVSTSZAWVIVVRTSZWWAWIWUKVVQTSZVOWWBWUKWWCX
      CUOTSZWUKVOWWCWWDWUKXMXCXLUOVCXEWMXLVCVVQXEWMUOVVRXFXGZVJZWFZAVUMVWGDVXCV
      XEVUPVWFVXPVXEVUTVVDVYAVYFWFWFWGZWFAVVTWVDWWGAUGVWHVYIWUEWFZWFAVUMVVOVVSC
      DEFVXCWVTWWFLMVXOVXTVYENOUVSAWVFWVDXHXNWVGWVEXHXNABVWEDUCUDULZVYNUHVUKSVD
      UBVUJVEUCULWWJUKXAUVTVXHUWAWWJUKUWBVXHUWCUHUHUWDUWEUWFZGHUDUBUCIJAUPUOUKX
      OZUPUQXOZVBQZGUPTSZAXPVJZWWNTSAWWNWWLWWMXQUPUQXRWKUWGZUWHXSVJZWUQAUPWWLUO
      VBQZWWNWWPWWSTSAWWSWWLTWWLXQUWIZWWLXQXSZUWJVJWWRUPWWSXHXNAUPWWLWWSXHUOUKU
      PUWKWJXRUPURXPXJUWLXTYAWWTUWMVJWWSWWNXHXNZAWWLTSZUOVQSZWWMVQSZUWNZUOWWLYB
      XNZVOZUOWWMXHXNZWXBWXFWXGWXCWXDWXEWXAUWOWWMWWQUWPUWQUWRXLUPUQUOYEWKWIUOUR
      XMXJUWSXTYAWXHWXIWXBWWLUOWWMUWTUXAXGVJYCKYCZVYSWWKUXBUXCAWVFWVDVVTWWHWWIA
      VVPVVSAVVOUPVYJUPVQSAUXDVJZYDVYKYFZYGYHYCAVVTUGVWHAVVPVVSAVVOAVVOWVTYIUXE
      AVVSWWFYIYJUGUXFSAUXGVJAVWHWUEYIUXHUXIAVWJUGVVTVWNUOGUXJQZUIUJZUPUXKZUXLZ
      UEULZUMUHZUEUNZWXMUFULZUMUHZUFUNZRQZRQZRQZRQZVWSWUGAUGWYEVYIAVVTWYDVYLAVW
      NWYCWUPAWXSWYBAWXPWXRUEWXPVGSZAWXNVGSZWXOVGSWYGWXMVGSWYHUOGUXMWXMUIVLWMUP
      UXNWXNWXOUXTXGVJZAWXQWXPSVOZPTWXQUMVXFWYJWEVJAWXPPWXQAWXNWXOPAWXMPUIWXMPW
      TAGUXOVJZUXPAUPPUPPSAYEVJUXQUXRXBZWBZWGZAGYPUHZWYBTAVXIWYOWYBXAVXJUFGUXSV
      NATTGYPTTYPVPAUYAVJWUQWBUYBZWFZWFZWFZWFZWVCAVWIWYEXHXNZVWJWYFXHXNAVWHWYDX
      HXNXUAABVWEUEUFDGHUBIJWXJVYSUYCAVWHWYDVVTWUEWYRWXLYGYHAVWIWYEUGWUFWYSUGWQ
      SAUYIVJZYGYHAWYFUGVVTVWNUOVCUPYKUGUTZUTZUTZVAQZVWORQZUOUKUGVMVMUGUTZUTZUT
      ZUTZVAQZGRQZRQZRQZRQZRQZVWSWYTAUGXUPVYIAVVTXUOVYLAVWNXUNWUPAXUGXUMAXUFVWO
      XUFTSZAWVIXUETSZXURWIWUKXUDTSZVOXUSWUKXUTXCWWOXUCTSZVOXUTWWOXVAXPYKTSZVYH
      VOXVAXVBVYHUYSWHXLYKUGXEWMXLUPXUCXEWMXLVCXUDXEWMUOXUEXFXGZVJZWURWFZAXULGX
      ULTSZAWVIXUKTSZXVFWIWVKXUJTSZVOXVGWVKXVHXIVYHXUITSZVOXVHVYHXVIWHWULXUHTSZ
      VOXVIWULXVJXDWULVYHVOXVJWULVYHXDWHXLVMUGXEWMXLVMXUHXEWMXLUGXUIXEWMXLUKXUJ
      XEWMUOXUKXFXGZVJZWUQWFZWFZWFZWFZWFWVCAWYEXUPXHXNZWYFXUQXHXNAWYDXUOXHXNZXV
      QAWYCXUNXHXNXVRAWYCXUNWYQXVNAWXSXUGWYBXUMWYNXVEWYPXVMAWXPWXRUEWYIWYMWYJWX
      QPSUKWXRXHXNWYLWXQYLVNYMAUEGJKUYDAWXMWYAUFAUOGUYEAWXTWXMSVOZPTWXTUMVXFXVS
      WEVJAWXMPWXTWYKXBZWBXVSWXTPSUKWYAXHXNXVTWXTYLVNYMAUFGJUYFUYGUYHAWYCXUNVWN
      WYQXVNAGWUQAUOUPGWWDAXMVJWWPWUQUOUPYBXNAUYJVJWXJUYKUYLZYGYHAWYDXUOVVTWYRX
      VOWXLYGYHAWYEXUPUGWYSXVPXUBYGYHAUGVVTXUFXULRQZRQZRQZVWPVWRRQZRQZVWMXWERQZ
      XUQVWSXHAXWDVWMXHXNXWFXWGXHXNXWDVWMUGXWCWHVVTXWBVVPVVSVVOWVSUYMWWEYNXUFXU
      LXVCXVKYNYNYNZWUMUYNXTAXWDVWMXWEXWDTSAXWHVJWUNAVWPVWRAVWNVWOXWAWUSUYOAGUP
      WUOWXKYDYFUYPUYQAXUQXWDVWOGRQZVWNRQZRQZXWFAXUQUGXWCXWJRQZRQXWKAXUPXWLUGRA
      XUPVVTXWBXWJRQZRQXWLAXUOXWMVVTRAXUOXWBXWIRQZVWNRQZXWMAXUOVWNXWNRQXWOAXUNX
      WNVWNRAXUFVWOXULGAXUFXVDYIZAVWOWURYIZAXULXVLYIZAGWUQYIZUYRYOAVWNXWNAVWNWU
      PYIZAXWBXWIAXUFXULXWPXWRYJZAVWOGXWQXWSYJZYJYQYRAXWBXWIVWNXXAXXBXWTYSYRYOA
      VVTXWBXWJAVVTVYLYIZXXAAXWIVWNXXBXWTYJZYSYTYOAUGXWCXWJAUGVYIYIAVVTXWBXXCXX
      AYJXXDYSYTAXWJXWEXWDRAXWEVWNVWRVWOVFQZRQXXEVWNRQXWJAVWNVWOVWRXWTXWQAVWRWV
      BYIZWUTUYTAVWNXXEXWTAVWRVWOXXFXWQWUTVUAYQAXXEXWIVWNRAXXEGVWORQZXWIAXXEGGR
      QZVWOVFQGGVWOVFQZRQXXGAVWRXXHVWOVFAGXWSVUBVUCAGGVWOXWSXWSXWQWUTVUDAXXIVWO
      GRAGWQSXXIVWOXAWUOGVUEVNYOVUFAGVWOXWSXWQYQYRVUCVUGYOYRAVWMVWPVWRAVWMWUNYI
      AVWPWVAYIXXFYSVUHYCYCYC $.
  $}

  ${
    $d H m n x $.  $d K m n x $.  $d N m n x z $.  $d O m n z $.
    $d ph m n x $.
    tgoldbachgtda.o $e |- O = { z e. ZZ | -. 2 || z } $.
    tgoldbachgtda.n $e |- ( ph -> N e. O ) $.
    tgoldbachgtda.0 $e |- ( ph -> ( ; 1 0 ^ ; 2 7 ) <_ N ) $.
    $( Lemma for ~ tgoldbachgtd .  (Contributed by Thierry Arnoux,
       15-Dec-2021.) $)
    tgoldbachgnn $p |- ( ph -> N e. NN ) $=
      ( cz wcel c1 cle wbr cn c2 cv cdvds cdc c7 cr a1i wn crab eleqtrdi elrabi
      syl cc0 cexp 1red cn0 10nn0 nn0rei 2nn0 7nn0 deccl reexpcl mp2an zred 1re
      co 1lt10 ltleii expge1 mp3an letrd elnnz1 sylanbrc ) ACHIZJCKLCMIACNBOPLU
      AZBHUBZIVGACDVIFEUCVHBCHUDUEZAJJUFQZNRQZUGUSZCAUHVMSIZAVKSIZVLUIIZVNVKUJU
      KZNRULUMUNZVKVLUOUPTACVJUQJVMKLZAVOVPJVKKLVSVQVRJVKURVQUTVAVKVLVBVCTGVDCV
      EVF $.

    tgoldbachgtda.h $e |- ( ph -> H : NN --> ( 0 [,) +oo ) ) $.
    tgoldbachgtda.k $e |- ( ph -> K : NN --> ( 0 [,) +oo ) ) $.
    tgoldbachgtda.1 $e |- ( ( ph /\ m e. NN ) ->
              ( K ` m ) <_ ( 1 . _ 0 _ 7 _ 9 _ 9 _ 5 5 ) ) $.
    tgoldbachgtda.2 $e |- ( ( ph /\ m e. NN ) ->
              ( H ` m ) <_ ( 1 . _ 4 _ 1 4 ) ) $.
    tgoldbachgtda.3 $e |- ( ph ->
        ( ( 0 . _ 0 _ 0 _ 0 _ 4 _ 2 _ 2 _ 4 8 ) x. ( N ^ 2 ) )
      <_ S. ( 0 (,) 1 ) ( ( ( ( ( Lam oF x. H ) vts N ) ` x )
          x. ( ( ( ( Lam oF x. K ) vts N ) ` x ) ^ 2 ) )
          x. ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( -u N x. x ) ) ) ) _d x ) $.
    $( Lemma for ~ tgoldbachgtd .  (Contributed by Thierry Arnoux,
       15-Dec-2021.) $)
    tgoldbachgtde $p |- ( ph ->
      0 < sum_ n e. ( ( O i^i Prime ) ( repr ` 3 ) N )
       ( ( ( Lam ` ( n ` 0 ) ) x. ( H ` ( n ` 0 ) ) )
    x. ( ( ( Lam ` ( n ` 1 ) ) x. ( K ` ( n ` 1 ) ) )
      x. ( ( Lam ` ( n ` 2 ) ) x. ( K ` ( n ` 2 ) ) ) ) ) ) $=
      ( cc0 cn co c3 crepr cfv cv cvma cmul c1 csu cprime cin cdif cmin clt wbr
      c2 c4 c8 cdp2 cdp cexp cfn wcel tgoldbachgnn nnnn0d cn0 a1i ssidd reprfi2
      3nn0 diffi syl cr difssd sselda wa wf vmaf cfzo cz nn0zd adantr simpr ctp
      reprf c0ex tpid1 fzo0to3tp eleqtrri ffvelcdmd cpnf cico rge0ssre remulcld
      wss fss sylancl 1eltp012 2ex tpid3 syldan fsumrecl 0nn0 qssre 4nn0 nn0ssq
      cq 2nn0 8nn0 sselii dp2clq dpcl mp2an nnred resqcld clog csqrt cdiv nnrpd
      c7 7nn0 relogcld nn0ge0d sqrtgt0d gt0ne0d redivcld hgt750leme 2z rpexpcld
      resqrtcld cdc cle hgt750lem syl2anc ltmul1dd lelttrd cioo cvts recnd wceq
      cof ci cpi cneg citg circlemethhgt breqtrrd ltletrd posdifd mpbid prmssnn
      ce inss2 sstri reprss ssfid cc fsumcl c0 cun undif sylib eqcomd fsumsplit
      disjdif mvrraddd breqtrd ) ARSHUAUBUCZTZREUDZUCZUEUCZUVJFUCZUFTZUGUVIUCZU
      EUCZUVNGUCZUFTZUOUVIUCZUEUCZUVRGUCZUFTZUFTZUFTZEUHZUVHIUIUJZHUVGTZUKZUWCE
      UHZULTZUWFUWCEUHZUMAUWHUWDUMUNRUWIUMUNAUWHRRRRUPUOUOUPUQURZURZURZURZURZUR
      ZURZUSTZHUOUTTZUFTZUWDAUWGUWCEAUVHVAVBUWGVAVBASUAHAHACHIJKLVCZVDZUAVEVBZA
      VIVFZASVGZVHZUVHUWFVJVKAUVIUWGVBUVIUVHVBZUWCVLVBAUWGUVHUVIAUVHUWFVMVNAUXG
      VOZUVMUWBUXHUVKUVLUXHSVLUVJUESVLUEVPUXHVQVFZUXHRUAVRTZSRUVIUXHSUVIUAHUXHS
      VGAHVSVBUXGAHUXBVTZWAUXCUXHVIVFAUXGWBWDZRUXJVBUXHRRUGUOWCZUXJRUGUOWEWFWGW
      HVFWIZWIUXHSVLUVJFASVLFVPZUXGASRWJWKTZFVPUXPVLWNZUXOMWLSUXPVLFWOWPZWAUXNW
      IWMUXHUVQUWAUXHUVOUVPUXHSVLUVNUEUXIUXHUXJSUGUVIUXLUGUXJVBUXHUGUXMUXJWQWGW
      HVFWIZWIUXHSVLUVNGASVLGVPZUXGASUXPGVPUXQUXTNWLSUXPVLGWOWPZWAZUXSWIWMUXHUV
      SUVTUXHSVLUVRUEUXIUXHUXJSUOUVIUXLUOUXJVBUXHUOUXMUXJRUGUOWRWSWGWHVFWIZWIUX
      HSVLUVRGUYBUYCWIWMWMWMZWTXAZAUWRUWSUWRVLVBZARVEVBUWQVLVBUYFXBXFVLUWQXCRUW
      PXBRUWOXBRUWNXBUPUWMXDUOUWLXGUOUWKXGUPUQXDVEXFUQXEXHXIXJZXJXJXJXJXJXJXIRU
      WQXKXLVFZAHAHUXAXMZXNZWMZAUVHUWCEUXFUYDXAZAUWHXSUAUWKURZUSTZHXOUCZHXPUCZX
      QTZUFTZUWSUFTUWTUYEAUYRUWSAUYNUYQUYNVLVBZAXSVEVBUYMVLVBUYSXTXFVLUYMXCUAUW
      KVIUYGXJXIXSUYMXKXLVFAUYOUYPAHAHUXAXRZYAAHUYIAHUXBYBYIAUYPAHUYTYCYDYEWMZU
      YJWMUYKACDEFGHIJUXALMNOPYFAUYRUWRUWSVUAUYHAHUOUYTUOVSVBAYGVFYHAHVEVBUGRYJ
      UOXSYJUTTHYKUNUYRUWRUMUNUXBLHYLYMYNYOAUWTBRUGYPTBUDZUEFUFYTZTHYQTUCVUBUEG
      VUCTHYQTUCUOUTTUFTUUAUOUUBUFTUFTHUUCVUBUFTUFTUUKUCUFTUUDUWDYKQABEFGHUXRUY
      AUXBUUEUUFUUGAUWHUWDUYEUYLUUHUUIAUWDUWJUWHAUWFUWCEAUVHUWFUXFASUWEUAHUXEUX
      KUXDUWESWNAUWEUISIUIUULUUJUUMVFUUNZUUOAUVIUWFVBUXGUWCUUPVBAUWFUVHUVIVUDVN
      UXHUWCUYDYRZWTUUQAUWHUYEYRAUWFUWGUWCUVHEUWFUWGUJUURYSAUWFUVHUVDVFAUWFUWGU
      USZUVHAUWFUVHWNVUFUVHYSVUDUWFUVHUUTUVAUVBUXFVUEUVCUVEUVF $.

    $( Lemma for ~ tgoldbachgtd .  (Contributed by Thierry Arnoux,
       15-Dec-2021.) $)
    tgoldbachgtda $p |- ( ph
      -> 0 < ( # ` ( ( O i^i Prime ) ( repr ` 3 ) N ) ) ) $=
      ( vn cfv co cc0 cprime cin c3 crepr chash cn wcel clt wbr c0 tgoldbachgnn
      cfn wne nnnn0d cn0 3nn0 a1i inss2 prmssnn sstri reprfi2 wceq cv cvma cmul
      wss c1 c2 tgoldbachgtde gt0ne0d neneqd wa simpr sumeq1d sum0 eqtrdi mtand
      csu neqned hashnncl biimpar syl2anc nngt0 syl ) AHUAUBZGUCUDRSZUERZUFUGZT
      WGUHUIAWFULUGZWFUJUMZWHAWEUCGAGACGHIJKUKUNUCUOUGAUPUQWEUFVFAWEUAUFHUAURUS
      UTUQVAAWFUJAWFUJVBZWFTQVCZRZVDRWMERVESVGWLRZVDRWNFRVESVHWLRZVDRWOFRVESVES
      VESZQVRZTVBAWQTAWQABCDQEFGHIJKLMNOPVIVJVKAWKVLZWQUJWPQVRTWRWFUJWPQAWKVMVN
      WPQVOVPVQVSWIWHWJWFVTWAWBWGWCWD $.
  $}

  ${
    $d N h k m n x y z $.  $d O h k m n z $.  $d h k m n x y ph $.
    tgoldbachgtd.o $e |- O = { z e. ZZ | -. 2 || z } $.
    tgoldbachgtd.n $e |- ( ph -> N e. O ) $.
    tgoldbachgtd.1 $e |- ( ph -> ( ; 1 0 ^ ; 2 7 ) <_ N ) $.
    $( Odd integers greater than ` ( ; 1 0 ^ ; 2 7 ) ` have at least a
       representation as a sum of three odd primes.  Final statement in section
       7.4 of [Helfgott] p. 70.  (Contributed by Thierry Arnoux,
       15-Dec-2021.) $)
    tgoldbachgtd $p |- ( ph -> 0 < ( # ` ( ( O i^i Prime ) ( repr ` 3 ) N ) ) )
      $=
      ( vm vn cv cfv c1 cc0 cdp2 co cle wbr cn c2 cmul vk vh vx vy c7 c9 c5 cdp
      wral c4 c8 cexp cioo cvma cof cvts ci cpi cneg ce w3a cprime cin c3 crepr
      citg chash clt cpnf cico cmap wcel ad3antrrr cdc elmapi ad3antlr ad2antlr
      wa simpr1 wceq fveq2 breq1d cbvralvw sylib r19.21bi simpr2 simpr3 oveq12d
      wf oveq1d oveq2d fveq2d cbvitgv breqtrdi tgoldbachgtda hgt749d r19.29vva
      oveq2 ) AHJZUAJZKZLMUEUFUFUGUGNNNNNUHOZPQZHRUIZWSUBJZKZLUJLUJNNUHOZPQZHRU
      IZMMMMUJSSUJUKNNNNNNNUHOCSULOTOZUCMLUMOZUCJZUNXETUOZOCUPOZKZXLUNWTXMOCUPO
      ZKZSULOZTOZUQSURTOTOZCUSZXLTOZTOZUTKZTOZVFZPQZVAZMDVBVCCVDVEKOVGKVHQUBUAM
      VIVJOZRVKOZYJAXEYJVLZVRZWTYJVLZVRZYHVRZUDBIXEWTCDEACDVLYKYMYHFVMALMVNSUEV
      NULOCPQYKYMYHGVMYKRYIXEWIAYMYHXEYIRVOVPYMRYIWTWIYLYHWTYIRVOVQYOIJZWTKZXBP
      QZIRYOXDYRIRUIYNXDXIYGVSXCYRHIRWSYPVTZXAYQXBPWSYPWTWAWBWCWDWEYOYPXEKZXGPQ
      ZIRYOXIUUAIRUIYNXDXIYGWFXHUUAHIRYSXFYTXGPWSYPXEWAWBWCWDWEYOXJYFUDXKUDJZXN
      KZUUBXPKZSULOZTOZXTYAUUBTOZTOZUTKZTOZVFPYNXDXIYGWGUCUDXKYEUUJXLUUBVTZXSUU
      FYDUUITUUKXOUUCXRUUETXLUUBXNWAUUKXQUUDSULXLUUBXPWAWJWHUUKYCUUHUTUUKYBUUGX
      TTXLUUBYATWRWKWLWHWMWNWOAUCBUBUAHCDEFGWPWQ $.
  $}

  ${
    $d G m $.  $d O c i m p q r z $.  $d c i m n p q r z $.
    tgoldbachgt.o $e |- O = { z e. ZZ | -. 2 || z } $.
    tgoldbachgt.g $e |- G = { z e. O | E. p e. Prime E. q e. Prime
                           E. r e. Prime ( ( p e. O /\ q e. O /\ r e. O )
                                           /\ z = ( ( p + q ) + r ) ) } $.
    $( Odd integers greater than ` ( ; 1 0 ^ ; 2 7 ) ` have at least a
       representation as a sum of three odd primes.  Final statement in section
       7.4 of [Helfgott] p. 70 , expressed using the set ` G ` of odd numbers
       which can be written as a sum of three odd primes.  (Contributed by
       Thierry Arnoux, 22-Dec-2021.) $)
    tgoldbachgt $p |- E. m e. NN ( m <_ ( ; 1 0 ^ ; 2 7 )
                          /\ A. n e. O ( m < n -> n e. G ) ) $=
      ( vc c1 cc0 c2 wcel wa caddc wceq cprime a1i vi cdc c7 cexp co cn cle wbr
      cv clt wral wrex cn0 10nn 2nn0 7nn0 deccl nnexpcl mp2an nnrei leidi simpl
      wi w3a wtru cin c3 crepr cfv cfzo wss inss2 prmssnn sstri cz cdvds eleq2i
      crab elrabi sylbi ad2antrr 3nn0 simpr reprf c0ex tpid1 fzo0to3tp eleqtrri
      wn ctp ffvelcdmd elin2d 1eltp012 2ex tpid3 elin1d csu sumeq1d reprsum cvv
      3jca fveq2 cc sselid nncnd 1ex wne 0ne1 0ne2 1ne2 sumtp 3eqtr3d jca eleq1
      3anbi1d oveq1 oveq1d eqeq2d anbi12d 3anbi2d oveq2 3anbi3d syl31anc adantr
      rspc3ev wex c0 chash nnred cr zred ltled tgoldbachgtd ovex hashneq0 sylib
      wb sylibr rexbidv breq1 ax-mp neneqd neq0 tru jctil 19.42v exancom df-rex
      r19.29a eqeq1 anbi2d elrab3 bitrid biimpar syl2anc ex rgen pm3.2i ralbidv
      imbi1d rspcev ) LMUBZNUCUBZUDUEZUFOZUVDUVDUGUHZUVDCUIZUJUHZUVGDOZVCZCEUKZ
      PZBUIZUVDUGUHZUVMUVGUJUHZUVIVCZCEUKZPZBUFULUVBUFOUVCUMOUVEUNNUCUOUPUQUVBU
      VCURUSZUVFUVKUVDUVDUVSUTVAUVJCEUVGEOZUVHUVIUVTUVHPZUVTHUIZEOZGUIZEOZFUIZE
      OZVDZUVGUWBUWDQUEZUWFQUEZRZPZFSULZGSULZHSULZUVIUVTUVHVBZUWAVEUWOKESVFZUVG
      VGVHVIZUEZUWAKUIZUWSOZPZUWOVEUXBMUWTVIZSOLUWTVIZSONUWTVIZSOUXCEOZUXDEOZUX
      EEOZVDZUVGUXCUXDQUEZUXEQUEZRZPZUWOUXBESUXCUXBMVGVJUEZUWQMUWTUXBUWQUWTVGUV
      GUWQUFVKUXBUWQSUFESVLVMVNZTZUVTUVGVOOZUVHUXAUVTUVGNAUIZVPUHWIZAVOVRZOUXQE
      UXTUVGIVQUXSAUVGVOVSVTZWAZVGUMOUXBWBTZUWAUXAWCZWDZMUXNOUXBMMLNWJZUXNMLNWE
      WFWGWHTWKZWLUXBESUXDUXBUXNUWQLUWTUYELUXNOUXBLUYFUXNWMWGWHTWKZWLUXBESUXEUX
      BUXNUWQNUWTUYENUXNOUXBNUYFUXNMLNWNWOWGWHTWKZWLUXBUXIUXLUXBUXFUXGUXHUXBESU
      XCUYGWPUXBESUXDUYHWPUXBESUXEUYIWPXAUXBUXNUAUIZUWTVIZUAWQUYFUYKUAWQUVGUXKU
      XBUXNUYFUYKUAUXNUYFRUXBWGTWRUXBUWQUWTVGUVGUAUXPUYBUYCUYDWSUXBMLNUYKUAUXCU
      XDUXEWTWTWTUYJMUWTXBUYJLUWTXBUYJNUWTXBUXBUXCXCOUXDXCOUXEXCOUXBUXCUXBUWQUF
      UXCUXOUYGXDXEUXBUXDUXBUWQUFUXDUXOUYHXDXEUXBUXEUXBUWQUFUXEUXOUYIXDXEXAUXBM
      WTOZLWTOZNWTOZUYLUXBWETUYMUXBXFTUYNUXBWNTXAMLXGUXBXHTMNXGUXBXITLNXGUXBXJT
      XKXLXMUWLUXMUXFUWEUWGVDZUVGUXCUWDQUEZUWFQUEZRZPUXFUXGUWGVDZUVGUXJUWFQUEZR
      ZPHGFUXCUXDUXESSSUWBUXCRZUWHUYOUWKUYRVUBUWCUXFUWEUWGUWBUXCEXNXOVUBUWJUYQU
      VGVUBUWIUYPUWFQUWBUXCUWDQXPXQXRXSUWDUXDRZUYOUYSUYRVUAVUCUWEUXGUXFUWGUWDUX
      DEXNXTVUCUYQUYTUVGVUCUYPUXJUWFQUWDUXDUXCQYAXQXRXSUWFUXERZUYSUXIVUAUXLVUDU
      WGUXHUXFUXGUWFUXEEXNYBVUDUYTUXKUVGUWFUXEUXJQYAXRXSYEYCYDUWAUXAVEPKYFZVEKU
      WSULUWAVEUXAPKYFZVUEUWAVEUXAKYFZPVUFUWAVUGVEUWAUWSYGRWIVUGUWAUWSYGUWAMUWS
      YHVIUJUHZUWSYGXGZUWAAUVGEIUWPUWAUVDUVGUWAUVDUVEUWAUVSTYIUVTUVGYJOUVHUVTUV
      GUYAYKYDUVTUVHWCYLYMUWSWTOVUHVUIYQUWQUVGUWRYNUWSWTYOUUAYPUUBKUWSUUCYPUUDU
      UEVEUXAKUUFYRVEUXAKUUGYPVEKUWSUUHYRUUIUVTUVIUWOUVIUVGUWHUXRUWJRZPZFSULZGS
      ULZHSULZAEVRZOUVTUWODVUOUVGJVQVUNUWOAUVGEUXRUVGRZVUMUWNHSVUPVULUWMGSVUPVU
      KUWLFSVUPVUJUWKUWHUXRUVGUWJUUJUUKYSYSYSUULUUMUUNUUOUUPUUQUURUVRUVLBUVDUFU
      VMUVDRZUVNUVFUVQUVKUVMUVDUVDUGYTVUQUVPUVJCEVUQUVOUVHUVIUVMUVDUVGUJYTUUTUU
      SXSUVAUS $.
  $}


$[ set-mbox-ta-geom.mm $]


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  LeftPad Project
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  See ~ https://github.com/tirix/lets-prove-leftpad .

$)

  $( Define the ` leftpad ` constant. $)
  $c leftpad $.

  $( Extend class notation with the ` leftpad ` function. $)
  clpad $a class leftpad $.

  ${
    $d c l w $.
    $( Define the ` leftpad ` function.  (Contributed by Thierry Arnoux,
       7-Aug-2023.) $)
    df-lpad $a |- leftpad = ( c e. _V , w e. _V |-> ( l e. NN0 |->
        ( ( ( 0 ..^ ( l - ( # ` w ) ) ) X. { c } ) ++ w ) ) ) $.
  $}

  ${
    $d C c l w $.  $d L l $.  $d W c l w $.  $d c l ph w $.
    lpadval.1 $e |- ( ph -> L e. NN0 ) $.
    lpadval.2 $e |- ( ph -> W e. Word S ) $.
    lpadval.3 $e |- ( ph -> C e. S ) $.
    $( Value of the ` leftpad ` function.  (Contributed by Thierry Arnoux,
       7-Aug-2023.) $)
    lpadval $p |- ( ph -> ( ( C leftpad W ) ` L ) = ( ( ( 0 ..^ ( L - ( # ` W )
       ) ) X. { C } ) ++ W ) ) $=
      ( vl vc vw cc0 cv cmin co cfzo cconcat cn0 cvv wceq cfv csn cxp cmpt cmpo
      chash clpad df-lpad a1i simprr fveq2d oveq2d simprl sneqd xpeq12d oveq12d
      mpteq2dv elexd cword nn0ex mptexd ovmpod simpr oveq1d xpeq1d ovexd fvmptd
      wa wcel ) AIDLIMZEUFUAZNOZPOZBUBZUCZEQOZLDVKNOZPOZVNUCZEQORBEUGOSAJKBESSI
      RLVJKMZUFUAZNOZPOZJMZUBZUCZVTQOZUDZIRVPUDUGSUGJKSSWHUETAKJIUHUIAWDBTZVTET
      ZVHVHZIRWGVPWKWFVOVTEQWKWCVMWEVNWKWBVLLPWKWAVKVJNWKVTEUFAWIWJUJZUKULULWKW
      DBAWIWJUMUNUOWLUPUQABCHURAECUSGURAIRVPSRSVIAUTUIVAVBAVJDTZVHZVOVSEQWNVMVR
      VNWNVLVQLPWNVJDVKNAWMVCVDULVEVDFAVSEQVFVG $.
  $}

  ${
    lpadlem1.1 $e |- ( ph -> C e. S ) $.
    $( Lemma for the ` leftpad ` theorems.  (Contributed by Thierry Arnoux,
       7-Aug-2023.) $)
    lpadlem1 $p |- ( ph -> ( ( 0 ..^ ( L - ( # ` W ) ) ) X. { C } ) e. Word S )
       $=
      ( wcel cc0 chash cfv cmin co cfzo csn cxp wf cword fconst6g iswrdi 3syl )
      ABCGHDEIJKLZMLZCUBBNOZPUCCQGFUBBCRCUAUCST $.
  $}

  ${
    lpadlen.1 $e |- ( ph -> L e. NN0 ) $.
    lpadlen.2 $e |- ( ph -> W e. Word S ) $.
    lpadlen.3 $e |- ( ph -> C e. S ) $.
    ${
      lpadlen1.1 $e |- ( ph -> L <_ ( # ` W ) ) $.
      $( Lemma for ~ lpadlen1 .  (Contributed by Thierry Arnoux,
         7-Aug-2023.) $)
      lpadlem3 $p |- ( ph -> ( ( 0 ..^ ( L - ( # ` W ) ) ) X. { C } ) = (/) )
        $=
        ( cc0 chash cfv cmin co cfzo cxp c0 cz wcel nn0zd csn cle wbr cword cn0
        wceq lencl syl wa fzo0n biimpa syl21anc xpeq1d 0xp eqtrdi ) AJDEKLZMNON
        ZBUAZPQURPQAUQQURAUPRSZDRSZDUPUBUCZUQQUFZAUPAECUDSUPUESGCEUGUHTADFTIUSU
        TUIVAVBUPDUJUKULUMURUNUO $.

      $( Length of a left-padded word, in the case the length of the given word
         ` W ` is at least the desired length.  (Contributed by Thierry Arnoux,
         7-Aug-2023.) $)
      lpadlen1 $p |- ( ph -> ( # ` ( ( C leftpad W ) ` L ) ) = ( # ` W ) ) $=
        ( clpad co cfv chash cc0 cmin cfzo csn cxp cconcat c0 oveq1d cword wcel
        lpadval lpadlem3 wceq ccatlid syl 3eqtrd fveq2d ) ADBEJKLZEMAUKNDEMLOKP
        KBQRZESKTESKZEABCDEFGHUDAULTESABCDEFGHIUEUAAECUBUCUMEUFGCEUGUHUIUJ $.
    $}

    ${
      lpadlen2.1 $e |- ( ph -> ( # ` W ) <_ L ) $.
      $( Lemma for the ` leftpad ` theorems.  (Contributed by Thierry Arnoux,
         7-Aug-2023.) $)
      lpadlem2 $p |- ( ph -> ( # ` ( ( 0 ..^ ( L - ( # ` W ) ) ) X. { C } ) )
          = ( L - ( # ` W ) ) ) $=
        ( cc0 chash cfv co cmul c1 wceq cfn wcel cn0 syl cmin cfzo csn cxp snfi
        fzofi hashxp mp2an a1i cle cword lencl nn0sub2 syl3anc hashfzo0 hashsng
        wbr oveq12d nn0cnd mulridd 3eqtrd ) AJDEKLZUAMZUBMZBUCZUDKLZVDKLZVEKLZN
        MZVCONMVCVFVIPZAVDQRVEQRVJJVCUFBUEVDVEUGUHUIAVGVCVHONAVCSRZVGVCPAVBSRZD
        SRVBDUJUQVKAECUKRVLGCEULTFIVBDUMUNZVCUOTABCRVHOPHBCUPTURAVCAVCVMUSUTVA
        $.

      $( Length of a left-padded word, in the case the given word ` W ` is
         shorter than the desired length.  (Contributed by Thierry Arnoux,
         7-Aug-2023.) $)
      lpadlen2 $p |- ( ph -> ( # ` ( ( C leftpad W ) ` L ) ) = L ) $=
        ( clpad co cfv chash cc0 cmin cfzo csn caddc wcel nn0cnd cconcat fveq2d
        cxp lpadval cword wceq lpadlem1 ccatlen syl2anc lpadlem2 oveq1d cn0 syl
        lencl npcand 3eqtrd eqtrd ) ADBEJKLZMLNDEMLZOKZPKBQUCZEUAKZMLZDAURVBMAB
        CDEFGHUDUBAVCVAMLZUSRKZUTUSRKDAVACUEZSEVFSZVCVEUFABCDEHUGGCCVAEUHUIAVDU
        TUSRABCDEFGHIUJUKADUSADFTAUSAVGUSULSGCEUNUMTUOUPUQ $.
    $}

    $( Length of a left-padded word, in the general case, expressed with an
       ` if ` statement.  (Contributed by Thierry Arnoux, 7-Aug-2023.) $)
    lpadmax $p |- ( ph -> ( # ` ( ( C leftpad W ) ` L ) )
       = if ( L <_ ( # ` W ) , ( # ` W ) , L ) ) $=
      ( chash cfv cle wbr clpad wceq eqeq2 wa cn0 wcel adantr nn0red co cif syl
      cword simpr lpadlen1 wn lencl clt ltnled biimpar ltled lpadlen2 ifbothda
      cr ) DEIJZKLZDBEMUAJIJZUPNURDNURUQUPDUBZNAUPDUPUSURODUSUROAUQPBCDEADQRZUQ
      FSAECUDRZUQGSABCRZUQHSAUQUEUFAUQUGZPZBCDEAUTVCFSZAVAVCGSAVBVCHSVDUPDAUPUO
      RVCAUPAVAUPQRGCEUHUCTZSVDDVETAUPDUILVCAUPDVFADFTUJUKULUMUN $.

    ${
      lpadleft.1 $e |- ( ph -> N e. ( 0 ..^ ( L - ( # ` W ) ) ) ) $.
      $( The contents of prefix of a left-padded word is always the letter
         ` C ` .  (Contributed by Thierry Arnoux, 7-Aug-2023.) $)
      lpadleft $p |- ( ph -> ( ( ( C leftpad W ) ` L ) ` N ) = C ) $=
        ( clpad co cfv cc0 chash cfzo wcel wceq cn0 wbr csn cxp cconcat lpadval
        cmin fveq1d cword lpadlem1 cle lencl syl cn clt w3a elfzo0 sylib simp2d
        nnnn0d wa biimpar syl21anc lpadlem2 eleqtrrd ccatval1 syl3anc fvconst2g
        nn0sub oveq2d syl2anc 3eqtrd ) AEDBFKLMZMENDFOMZUELZPLZBUAUBZFUCLZMZEVO
        MZBAEVKVPABCDFGHIUDUFAVOCUGZQFVSQZENVOOMZPLZQVQVRRABCDFIUHHAEVNWBJAWAVM
        NPABCDFGHIAVLSQZDSQZVMSQZVLDUITZAVTWCHCFUJUKGAVMAESQZVMULQZEVMUMTZAEVNQ
        ZWGWHWIUNJEVMUOUPUQURWCWDUSWFWEVLDVGUTVAVBVHVCCCVOFEVDVEABCQWJVRBRIJVNB
        ECVFVIVJ $.
    $}

    ${
      lpadright.1 $e |- ( ph -> M = if ( L <_ ( # ` W ) , 0 , ( L - ( # ` W ) )
        ) ) $.
      lpadright.2 $e |- ( ph -> N e. ( 0 ..^ ( # ` W ) ) ) $.
      $( The suffix of a left-padded word the original word ` W ` .
         (Contributed by Thierry Arnoux, 7-Aug-2023.) $)
      lpadright $p |- ( ph
          -> ( ( ( C leftpad W ) ` L ) ` ( N + M ) ) = ( W ` N ) ) $=
        ( caddc co cfv cc0 chash wceq wcel adantr cmin cfzo csn cconcat lpadval
        clpad cxp fveq1d cle wbr cif eqeq2 wa c0 cn0 cword simpr lpadlem3 hash0
        fveq2d eqtrdi wn cr lencl syl nn0red clt ltnled ltled lpadlem2 ifbothda
        biimpar eqtr4d oveq2d lpadlem1 ccatval3 syl3anc 3eqtr2d ) AFEMNZDBGUFNO
        ZOVSPDGQOZUANZUBNBUCUGZGUDNZOFWCQOZMNZWDOZFGOZAVSVTWDABCDGHIJUEUHAWFVSW
        DAWEEFMAWEDWAUIUJZPWBUKZEWIWEPRWEWBRWEWJRAPWBPWJWEULWBWJWEULAWIUMZWEUNQ
        OPWKWCUNQWKBCDGADUOSZWIHTAGCUPZSZWIITABCSZWIJTAWIUQURUTUSVAAWIVBZUMZBCD
        GAWLWPHTAWNWPITAWOWPJTWQWADAWAVCSWPAWAAWNWAUOSICGVDVEVFZTADVCSWPADHVFZT
        AWADVGUJWPAWADWRWSVHVLVIVJVKKVMVNUTAWCWMSWNFPWAUBNSWGWHRABCDGJVOILCWCGF
        VPVQVR $.
    $}
  $}

$( (End of Thierry Arnoux's mathbox.) $)
