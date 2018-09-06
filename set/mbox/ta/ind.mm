$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Indicator Functions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c _Ind $.

  $( Extend class notation with the indicator function generator. $)
  cind $a class _Ind $.

  ${
    $d a o x $.
    $( Define the indicator function generator.  (Contributed by Thierry
       Arnoux, 20-Jan-2017.) $)
    df-ind $a |- _Ind = ( o e. _V |-> ( a e. ~P o |->
                                    ( x e. o |-> if ( x e. a , 1 , 0 ) ) ) ) $.
  $}

  ${
    $d a o x O $.  $d a o V $.
    $( Value of the indicator function generator with domain ` O ` .
       (Contributed by Thierry Arnoux, 23-Aug-2017.) $)
    indv $p |- ( O e. V ->
     ( _Ind ` O ) = ( a e. ~P O |-> ( x e. O |-> if ( x e. a , 1 , 0 ) ) ) ) $=
      ( vo wcel cpw cc0 cif cmpt cvv cind wceq df-ind a1i pweq mpteq1 mpteq12dv
      cv c1 adantl elex pwexg mptexg 3syl fvmptd ) BCFZEBDESZGZAUHASDSFTHIZJZJZ
      DBGZABUJJZJZKLKLEKULJMUGAEDNOUHBMZULUOMUGUPDUIUKUMUNUHBPAUHBUJQRUABCUBZUG
      BKFUMKFUOKFUQBKUCDUMUNKUDUEUF $.

    $d a o x A $.
    $( Value of the indicator function generator for a set ` A ` and a domain
       ` O ` .  (Contributed by Thierry Arnoux, 2-Feb-2017.) $)
    indval $p |- ( ( O e. V /\ A C_ O ) ->
               ( ( _Ind ` O ) ` A ) = ( x e. O |-> if ( x e. A , 1 , 0 ) ) ) $=
      ( va wcel wss wa cv c1 cc0 cif cmpt cpw cind cfv cvv wceq indv adantr syl
      eleq2 ifbid mpteq2dv adantl simpr ssexg ancoms elpwg mpbird mptexg fvmptd
      wb ) CDFZBCGZHZEBACAIZEIZFZJKLZMZACUQBFZJKLZMZCNZCOPZQUNVFEVEVAMRUOACDEST
      URBRZVAVDRUPVGACUTVCVGUSVBJKURBUQUBUCUDUEUPBVEFZUOUNUOUFUPBQFZVHUOUMUOUNV
      IBCDUGUHBCQUIUAUJUNVDQFUOACVCDUKTUL $.
  $}

  ${
    $d x y A $.  $d x O $.
    $( Alternate value of the indicator function generator.  (Contributed by
       Thierry Arnoux, 2-Feb-2017.) $)
    indval2 $p |- ( ( O e. V /\ A C_ O ) -> ( ( _Ind ` O ) ` A ) =
                              ( ( A X. { 1 } ) u. ( ( O \ A ) X. { 0 } ) ) ) $=
      ( vx wcel wss cfv csn c1 cc0 cxp ciun wceq syl6eq sneqd xpeq2d iunxpconst
      cun iuneq2i eqtri wa cind cif cdif cmpt dfmpt3 indval undif biimpi adantl
      cv iuneq1d 3eqtr4a iunxun iftrue wn eldifn iffalse syl uneq12i ) BCEZABFZ
      UAZABUBGGZDADUKZHZVEAEZIJUCZHZKZLZDBAUDZVJLZRZAIHZKZVLJHZKZRVCVDDAVLRZVJL
      ZVNVCDBVHUEDBVJLVDVTDBVHUFDABCUGVCDVSBVJVBVSBMZVAVBWAABUHUIUJULUMDAVLVJUN
      NVKVPVMVRVKDAVFVOKZLVPDAVJWBVGVIVOVFVGVHIVGIJUOOPSDAVOQTVMDVLVFVQKZLVRDVL
      VJWCVEVLEZVIVQVFWDVGUPZVIVQMVEBAUQWEVHJVGIJUROUSPSDVLVQQTUTN $.
  $}

  ${
    $d x A $.  $d x O $.  $d x V $.
    $( An indicator function as a function with domain and codomain.
       (Contributed by Thierry Arnoux, 13-Aug-2017.) $)
    indf $p |- ( ( O e. V /\ A C_ O ) ->
                                    ( ( _Ind ` O ) ` A ) : O --> { 0 , 1 } ) $=
      ( vx wcel wss wa cv c1 cc0 cif cpr cind cfv indval cr 1re 0re ifpr mp2an
      prcom eleqtri a1i fmpt3d ) BCEABFGZDBDHZAEZIJKZJILZABMNNDABCOUHUIEUEUFBEG
      UHIJLZUIIPEJPEUHUJEQRUGIJPPSTIJUAUBUCUD $.

    $d x X $.
    $( Value of the indicator function.  (Contributed by Thierry Arnoux,
       13-Aug-2017.) $)
    indfval $p |- ( ( O e. V /\ A C_ O /\ X e. O ) ->
      ( ( ( _Ind ` O ) ` A ) ` X ) = if ( X e. A , 1 , 0 ) ) $=
      ( vx wcel wss w3a cv c1 cc0 cif cind cfv cr cmpt wceq indval 3adant3 wa
      simpr eleq1d ifbid simp3 1re 0re keepel a1i fvmptd ) BCFZABGZDBFZHZEDEIZA
      FZJKLZDAFZJKLZBABMNNZOUJUKUSEBUPPQULEABCRSUMUNDQZTZUOUQJKVAUNDAUMUTUAUBUC
      UJUKULUDUROFUMUQJKOUEUFUGUHUI $.
  $}

  $( The range of the indicator function is a subset of ` RR ` .  (Contributed
     by Thierry Arnoux, 14-Aug-2017.) $)
  pr01ssre $p |- { 0 , 1 } C_ RR $=
    ( cc0 cr wcel c1 cpr wss 0re 1re prssi mp2an ) ABCDBCADEBFGHADBIJ $.

  $( Value of the indicator function where it is ` 1 ` .  (Contributed by
     Thierry Arnoux, 14-Aug-2017.) $)
  ind1 $p |- ( ( O e. V /\ A C_ O /\ X e. A ) ->
                                          ( ( ( _Ind ` O ) ` A ) ` X ) = 1 ) $=
    ( wcel wss w3a cind cfv c1 cc0 cif wceq simp2 simp3 sseldd indfval syld3an3
    iftrue 3ad2ant3 eqtrd ) BCEZABFZDAEZGZDABHIIIZUDJKLZJUBUCUDDBEUFUGMUEABDUBU
    CUDNUBUCUDOPABCDQRUDUBUGJMUCUDJKSTUA $.

  $( Value of the indicator function where it is ` 0 ` .  (Contributed by
     Thierry Arnoux, 14-Aug-2017.) $)
  ind0 $p |- ( ( O e. V /\ A C_ O /\ X e. ( O \ A ) ) ->
                                          ( ( ( _Ind ` O ) ` A ) ` X ) = 0 ) $=
    ( wcel wss cdif w3a cind cfv c1 cc0 wceq eldifi indfval syl3an3 wn 3ad2ant3
    cif eldifn iffalse syl eqtrd ) BCEZABFZDBAGEZHZDABIJJJZDAEZKLSZLUFUDUEDBEUH
    UJMDBANABCDOPUGUIQZUJLMUFUDUKUEDBATRUIKLUAUBUC $.

  $( Value of the indicator function where it is ` 1 ` .  (Contributed by
     Thierry Arnoux, 22-Aug-2017.) $)
  ind1a $p |- ( ( O e. V /\ A C_ O /\ X e. O ) ->
                           ( ( ( ( _Ind ` O ) ` A ) ` X ) = 1 <-> X e. A ) ) $=
    ( wcel wss w3a cind cfv c1 wceq cc0 cif indfval eqeq1d wa wn eqid biantru
    wo wne ax-1ne0 df-ne mpbi biorfi bianfi orbi2i 3bitri eqcom 3bitr2ri syl6bb
    eqif ) BCEABFDBEGZDABHIIIZJKDAEZJLMZJKZUOUMUNUPJABCDNOUOUOJJKZPZUOQZJLKZPZT
    ZJUPKUQUOUSUSVATVCURUOJRSVAUSJLUAVAQUBJLUCUDZUEVAVBUSVAUTVDUFUGUHUOJJLULJUP
    UIUJUK $.

  ${
    $d x A $.  $d x O $.  $d x V $.
    $( Preimage of the singleton ` { 1 } ` by the indicator function.  See
       ~ i1f1lem .  (Contributed by Thierry Arnoux, 21-Aug-2017.) $)
    indpi1 $p |- ( ( O e. V /\ A C_ O ) ->
                                   ( `' ( ( _Ind ` O ) ` A ) " { 1 } ) = A ) $=
      ( vx wcel wss wa cind cfv ccnv c1 csn cima cv wb ind1a 3expia pm5.32d cc0
      wceq cpr wf wfn indf ffn fniniseg 3syl ssel pm4.71rd adantl 3bitr4d eqrdv
      ) BCEZABFZGZDABHIIZJKLMZAUODNZBEZURUPIKTZGZUSURAEZGZURUQEZVBUOUSUTVBUMUNU
      SUTVBOABCURPQRUOBSKUAZUPUBUPBUCVDVAOABCUDBVEUPUEBKURUPUFUGUNVBVCOUMUNVBUS
      ABURUHUIUJUKUL $.
  $}

  ${
    $d x A $.  $d x O $.  $d x ph $.
    indsum.1 $e |- ( ph -> O e. Fin ) $.
    indsum.2 $e |- ( ph -> A C_ O ) $.
    indsum.3 $e |- ( ( ph /\ x e. O ) -> B e. CC ) $.
    $( TODO: shorten using ~ sumss2 ! $)
    $( Finite sum of a product with the indicator function / cross-product with
       the indicator function.  (Contributed by Thierry Arnoux,
       14-Aug-2017.) $)
    indsum $p |- ( ph -> sum_ x e. O ( ( ( ( _Ind ` O ) ` A ) ` x ) x. B )
                        = sum_ x e. A B ) $=
      ( cfv cmul co csu wcel wa cc0 c1 cfn syldan wceq adantr cv cind cc sselda
      cpr cr pr01ssre wss indf syl2anc ffvelrnda sseldi recnd mulcld cdif simpr
      wf ind0 syl3anc oveq1d difssd mul02d eqtrd fsumss mulid2d sumeq2dv eqtr3d
      ind1 ) ACBUAZCEUBIIZIZDJKZBLEVLBLCDBLACEVLBGAVICMZVIEMZVLUCMACEVIGUDZAVNN
      ZVKDVPVKVPOPUEZUFVKUGAEVQVIVJAEQMZCEUHZEVQVJUQFGCEQUIUJUKULUMHUNRAVIECUOZ
      MZNZVLODJKZOWBVKODJWBVRVSWAVKOSAVRWAFTAVSWAGTAWAUPCEQVIURUSUTAWAVNWCOSAVT
      EVIAECVAUDVPDHVBRVCFVDACVLDBAVMNZVLPDJKZDWDVKPDJWDVRVSVMVKPSAVRVMFTAVSVMG
      TAVMUPCEQVIVHUSUTAVMVNWEDSVOVPDHVERVCVFVG $.
  $}

  ${
    $d a x O $.  $d a V $.
    $( The bijection between a power set and the set of indicator functions.
       (Contributed by Thierry Arnoux, 14-Aug-2017.) $)
    indf1o $p |- ( O e. V ->
                        ( _Ind ` O ) : ~P O -1-1-onto-> ( { 0 , 1 } ^m O ) ) $=
      ( va vx wcel cpw cc0 c1 cpr cmap co cind cfv wf1o wel cif cmpt cr id a1i
      0re 1re wne ax-1ne0 necomi eqid pw2f1o wceq wb indv f1oeq1 syl mpbird ) A
      BEZAFZGHIAJKZALMZNZUOUPCUODADCOHGPQQZNZUNCDAGHUSBRUNSGREUNUATHREUNUBTGHUC
      UNHGUDUETUSUFUGUNUQUSUHURUTUIDABCUJUOUPUQUSUKULUM $.
  $}

  ${
    $d x F $.  $d x O $.  $d x V $.
    $( A function with range ` { 0 , 1 } ` as an indicator of the preimage of
       ` { 1 } ` (Contributed by Thierry Arnoux, 23-Aug-2017.) $)
    indpreima $p |- ( ( O e. V /\ F : O --> { 0 , 1 } ) ->
                                   F = ( ( _Ind ` O ) ` ( `' F " { 1 } ) ) ) $=
      ( vx wcel cc0 c1 cpr wf wa cfv wfn ffn adantl wceq syl ffvelrnda syl6eleq
      simpr wb ccnv csn cima cind wss cdm cnvimass fdm syl5sseq syldan cv prcom
      indf simpll adantr ind1a syl3anc fniniseg baibd bitr2d elpreq eqfnfvd ) B
      CEZBFGHZAIZJZDBAAUAGUBZUCZBUDKKZVEABLZVCBVDAMNZVFBVDVIIZVIBLVCVEVHBUEZVLV
      FAUFZVHBAVGUGVEVNBOVCBVDAUHNUIZVHBCUMUJZBVDVIMPVFDUKZBEZJZGFVQAKZVQVIKZVS
      VTVDGFHZVFBVDVQAVCVESQFGULZRVSWAVDWBVFBVDVQVIVPQWCRVSWAGOZVQVHEZVTGOZVSVC
      VMVRWDWETVCVEVRUNVFVMVRVOUOVFVRSVHBCVQUPUQVFWEVRWFVFVJWEVRWFJTVKBGVQAURPU
      SUTVAVB $.
  $}

  ${
    $d a f g O $.  $d a g V $.
    $( The bijection between finite subsets and the indicator functions with
       finite support.  (Contributed by Thierry Arnoux, 22-Aug-2017.) $)
    indf1ofs $p |- ( O e. V -> ( ( _Ind ` O ) |` Fin ) : ( ~P O i^i Fin )
         -1-1-onto-> { f e. ( { 0 , 1 } ^m O ) | ( `' f " { 1 } ) e. Fin } ) $=
      ( vg va wcel cfn cfv cima cres wf1o cv ccnv c1 wss syl wceq wa syldan wb
      cpw cin cind csn cc0 cpr cmap crab wf1 indf1o f1of1 f1ores sylancl resres
      co inss1 wfn f1ofn fnresdm 3syl reseq1d syl5eqr eqidd simpll simpr sseldi
      wrex wf elpwid indf adantr feq1d mpbid prex elmapg biimpar syl2anc cnveqd
      cvv mpan imaeq1d indpi1 inss2 eqeltrd eqeltrrd jca rexlimdva cdm cnvimass
      biimpa fdm adantrr syl5sseq simprr elfpw sylanbrc indpreima eqcomd eqeq1d
      ex fveq2 rspcev impbid fvelimab cnveq eleq1d elrab a1i 3bitr4d f1oeq123d
      eqrdv ) BCFZBUAZGUBZBUCHZXNIZXOXNJZKZXNALZMZNUDZIZGFZAUENUFZBUGUOZUHZXOGJ
      ZKXLXMYEXOUIZXNXMOZXRXLXMYEXOKZYHBCUJZXMYEXOUKPXMGUPZXMYEXNXOULUMXLXNXNXP
      YFXQYGXLXQXOXMJZGJYGXOXMGUNXLYMXOGXLYJXOXMUQZYMXOQYKXMYEXOURZXMXOUSUTVAVB
      XLXNVCXLDXPYFXLELZXOHZDLZQZEXNVGZYRYEFZYRMZYAIZGFZRZYRXPFZYRYFFZXLYTUUEXL
      YSUUEEXNXLYPXNFZRZYSUUEUUIYSRZUUAUUDUUJXLBYDYRVHZUUAXLUUHYSVDUUJBYDYQVHZU
      UKUUIUULYSXLUUHYPBOZUULUUIYPBUUIXNXMYPYLXLUUHVEZVFVIZYPBCVJSVKUUJBYDYQYRU
      UIYSVEZVLVMXLUUAUUKYDVSFXLUUAUUKTUENVNYDBYRVSCVOVTZVPVQUUJYQMZYAIZUUCGUUJ
      UURUUBYAUUJYQYRUUPVRWAUUIUUSGFYSUUIUUSYPGXLUUHUUMUUSYPQUUOYPBCWBSUUIXNGYP
      XMGWCUUNVFWDVKWEWFWTWGXLUUEYTXLUUERZUUCXNFZUUCXOHZYRQZYTUUTUUCBOUUDUVAUUT
      YRWHZUUCBYRYAWIXLUUAUVDBQZUUDXLUUARUUKUVEXLUUAUUKUUQWJZBYDYRWKPWLWMXLUUAU
      UDWNUUCBWOWPXLUUAUVCUUDXLUUAUUKUVCUVFXLUUKRYRUVBYRBCWQWRSWLYSUVCEUUCXNYPU
      UCQYQUVBYRYPUUCXOXAWSXBVQWTXCXLYNYIUUFYTTXLYJYNYKYOPYLEXMXNYRXOXDUMUUGUUE
      TXLYCUUDAYRYEXSYRQZYBUUCGUVGXTUUBYAXSYRXEWAXFXGXHXIXKXJVM $.
  $}

