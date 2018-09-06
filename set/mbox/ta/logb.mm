$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    Real and complex functions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
    Logarithm laws generalized to an arbitrary base - logb
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Define "log using an arbitrary base" function and then prove some
  of its properties.  This builds on previous work by Stefan O'Rear.
  Note that ` logb ` is generalized to an arbitrary base and arbitrary
  parameter in ` CC ` , but it doesn't accept infinities as arguments,
  unlike ` log ` .

  Metamath doesn't care what letters are used to represent classes.
  Usually classes begin with the letter "A", but here we use "B" and "X"
  to more clearly distinguish between "base" and "other parameter of log".

  There are different ways this could be defined in Metamath.  The
  approach used here is intentionally similar to existing 2-parameter Metamath
  functions.  The way defined here supports two notations,
  ` ( logb `` <. B , X >. ) ` and ` ( B logb X ) `  where ` B ` is the base
  and ` X ` is the other parameter.
  An alternative would be to support the notational form
  ` ( ( logb `` B ) `` X ) ` ;  that looks a little more like traditional
  notation, but is different than other 2-parameter functions.
  It's not obvious to me which is better,
  so here we try out one way as an experiment.  Feedback and help welcome.
$)

  $c logb $. $( Logarithm generalized to an arbitrary base. $)

  $( Extend class notation to include the logarithm generalized to an arbitrary
     base. $)
  clogb $a class logb $.

  ${
    $d n x y z $.
    $( Define the ` logb ` operator.  This is the logarithm generalized to an
       arbitrary base.  It can be used as ` ( logb `` <. B , X >. ) ` for "log
       base B of X".  In the most common traditional notation, base B is a
       subscript of "log".  You could also use ` ( B logb X ) ` , which looks
       like a less-common notation that some use where the base is a preceding
       superscript.  Note:  This definition doesn't prevent bases of 1 or 0;
       proofs may need to forbid them.  (Contributed by David A. Wheeler,
       21-Jan-2017.) $)
    df-logb $a |- logb = ( x e. ( CC \ { 0 , 1 } ) , y e. ( CC \ { 0 } ) |->
                         ( ( log ` y ) / ( log ` x ) ) ) $.
  $}

  ${
    $d x y B $.  $d x y X $.
    $( Define the value of the ` logb ` function, the logarithm generalized to
       an arbitrary base, when used as infix.  Most Metamath statements select
       variables in order of their use, but to make the order clearer we use
       "B" for base and "X" for the other operand here.  Proof is similar to
       ~ modval .  (Contributed by David A. Wheeler, 21-Jan-2017.)  (Revised by
       David A. Wheeler, 16-Jul-2017.) $)
    logbval $p |- ( ( B e. ( CC \ { 0 , 1 } ) /\ X e. ( CC \ { 0 } ) )
           -> ( B logb X ) = ( ( log ` X ) / ( log ` B ) ) )
      $=
      ( vx vy cc cc0 c1 cpr cdif csn cv clog cfv cdiv clogb fveq2 oveq2d oveq1d
      co wceq df-logb ovex ovmpt2 ) CDABEFGHIEFJIDKZLMZCKZLMZNSBLMZALMZNSOUEUIN
      SUFATUGUIUENUFALPQUDBTUEUHUINUDBLPRCDUAUHUINUBUC $.
  $}

  $( Define the value of the ` logb ` function, the logarithm generalized to an
     arbitrary base, when used in the 2-argument form ` logb <. B , X >. `
     (Contributed by David A. Wheeler, 21-Jan-2017.)  (Revised by David A.
     Wheeler, 16-Jul-2017.) $)
  logb2aval $p |- ( ( B e. ( CC \ { 0 , 1 } ) /\ X e. ( CC \ { 0 } ) )
         -> ( logb ` <. B , X >. ) = ( ( log ` X ) / ( log ` B ) ) ) $=
    ( cc cc0 c1 cpr cdif wcel csn wa cop clogb cfv co clog cdiv logbval syl5eqr
    df-ov ) ACDEFGHBCDIGHJABKLMABLNBOMAOMPNABLSABQR $.

  $( General logarithm is a real number, given positive real numbers.  Based on
     ~ reglogcl .  (Contributed by David A. Wheeler, 21-Jan-2017.)
  relogbcl $p |- ( ( B e. RR+ /\ X e. RR+ /\ B =/= 1 ) ->
                   ( B logb X ) e. RR ) $= ? $.
  $)

  $( Membership in a set with two elements removed.  Similar to ~ eldifsn and
     ~ eldiftp .  (Contributed by Mario Carneiro, 18-Jul-2017.) $)
  eldifpr $p |- ( A e. ( B \ { C , D } ) <->
                ( A e. B /\ A =/= C /\ A =/= D ) ) $=
    ( wcel cpr wn wa wne cdif w3a wo elprg notbid neanior syl6bbr pm5.32i eldif
    wceq 3anass 3bitr4i ) ABEZACDFZEZGZHUBACIZADIZHZHABUCJEUBUFUGKUBUEUHUBUEACS
    ADSLZGUHUBUDUIACDBMNACADOPQABUCRUBUFUGTUA $.

  $( Membership in a set with three elements removed.  Similar to ~ eldifsn and
     ~ eldifpr .  (Contributed by David A. Wheeler, 22-Jul-2017.) $)
  eldiftp $p |- ( A e. ( B \ { C , D , E } ) <->
                ( A e. B /\ ( A =/= C /\ A =/= D /\ A =/= E ) ) ) $=
    ( ctp cdif wcel wn wa wne w3a eldif wceq w3o eltpg ne3anior syl6bbr pm5.32i
    notbid bitri ) ABCDEFZGHABHZAUBHZIZJUCACKADKAEKLZJABUBMUCUEUFUCUEACNADNAENO
    ZIUFUCUDUGACDEBPTACADAEQRSUA $.

  $( if ` ( log `` A ) = 0 ` then ` A = 1 ` (Contributed by David A. Wheeler,
     22-Jul-2017.) $)
  logeq0im1 $p |- ( ( A e. CC /\ A =/= 0 /\ ( log ` A ) = 0 ) -> A = 1 ) $=
    ( cc wcel cc0 wne clog cfv wceq w3a ce c1 eflog 3adant3 ef0 syl6eq 3ad2ant3
    fveq2 eqtr3d ) ABCZADEZAFGZDHZIUAJGZAKSTUCAHUBALMUBSUCKHTUBUCDJGKUADJQNOPR
    $.

  $( log isn't 0 if argument isn't 0 or 1.  Unlike ~ logne0 , this handles
     complex numbers.  (Contributed by David A. Wheeler, 17-Jul-2017.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  logccne0OLD $p |- ( ( A e. CC /\ A =/= 0 /\ A =/= 1 ) ->
                  ( log ` A ) =/= 0 ) $=
    ( cc wcel cc0 wne c1 w3a clog ce wceq wn eflog 3adant3 simp3 eqnetrd neneqd
    cfv fveq2 ef0 syl6eq necon3bi syl ) ABCZADEZAFEZGZAHQZIQZFJZKUGDEUFUHFUFUHA
    FUCUDUHAJUEALMUCUDUENOPUIUGDUGDJUHDIQFUGDIRSTUAUB $.

  $( log isn't 0 if argument isn't 0 or 1.  Unlike ~ logne0 , this handles
     complex numbers.  (Contributed by David A. Wheeler, 17-Jul-2017.) $)
  logccne0 $p |- ( ( A e. CC /\ A =/= 0 /\ A =/= 1 ) ->
                  ( log ` A ) =/= 0 ) $=
    ( cc wcel cc0 wne c1 w3a clog wceq simp3 neneqd wi logeq0im1 3expia 3adant3
    cfv mtod neneqad ) ABCZADEZAFEZGZAHPZDUBUCDIZAFIZUBAFSTUAJKSTUDUELUASTUDUEA
    MNOQR $.

  $( General logarithm closure.  (Contributed by David A. Wheeler,
     17-Jul-2017.) $)
  logbcl $p |- ( ( B e. ( CC \ { 0 , 1 } ) /\ X e. ( CC \ { 0 } ) )
                 -> ( B logb X ) e. CC ) $=
    ( cc cc0 c1 cpr cdif wcel csn wa clogb co clog cfv cdiv logbval wne eldifsn
    sylbi adantr logcl adantl eldifi eldifpr simp2bi logcld w3a logccne0 divcld
    eqeltrd ) ACDEFZGHZBCDIGHZJZABKLBMNZAMNZOLCABPUNUOUPUMUOCHZULUMBCHBDQJUQBCD
    RBUASUBULUPCHUMULAACUKUCULACHZADQZAEQZACDEUDZUEUFTULUPDQZUMULURUSUTUGVBVAAU
    HSTUIUJ $.

  $( General logarithm when base and arg match (Contributed by David A.
     Wheeler, 22-Jul-2017.) $)
  logbid1 $p |- ( ( A e. CC /\ A =/= 0 /\ A =/= 1 ) -> ( A logb A ) = 1 ) $=
    ( cc wcel cc0 wne w3a clogb clog cfv cdiv cpr cdif csn wceq eldifpr biimpri
    c1 co wa 3adant3 eldifsn logbval syl2anc logcl logccne0 dividd eqtrd ) ABCZ
    ADEZAQEZFZAAGRZAHIZUMJRZQUKABDQKLCZABDMLCZULUNNUOUKABDQOPUHUIUPUJUPUHUISABD
    UAPTAAUBUCUKUMUHUIUMBCUJAUDTAUEUFUG $.

  $( Useful lemma for working with integer logarithm bases (with is a common
     case, e.g. base 2, base 3 or base 10) (Contributed by Thierry Arnoux,
     26-Sep-2017.) $)
  rnlogblem $p |- ( B e. ( ZZ>= ` 2 ) -> ( B e. RR+ /\ B =/= 0 /\ B =/= 1 ) )
    $=
    ( c2 cuz cfv wcel crp cc0 wne c1 cn wss cz cle wbr 2z 1re 2re nelne2 mpan2
    wn 1lt2 ltleii 1z eluz1i mpbir2an uzss ax-mp nnuz sseqtr4i sseli nnrpd 2pos
    clt 0re ltnlei mpbi eluzle mto 1nuz2 3jca ) ABCDZEZAFEAGHZAIHZVBAVAJAVAICDZ
    JBVEEZVAVEKVFBLEIBMNOIBPQUAUBIBUCUDUEIBUFUGUHUIUJUKVBGVAEZTVCVGBGMNZGBUMNVH
    TULGBUNQUOUPBGUQURAGVARSVBIVAETVDUSAIVARSUT $.

  $( Value of the general logarithm with integer base.  (Contributed by Thierry
     Arnoux, 27-Sep-2017.) $)
  rnlogbval $p |- ( ( B e. ( ZZ>= ` 2 ) /\ X e. RR+ )
        -> ( B logb X ) = ( ( log ` X ) / ( log ` B ) ) ) $=
    ( c2 cuz cfv wcel crp wa cc cc0 c1 cpr cdif csn clogb co clog cdiv wceq wne
    rnlogblem adantr simp1d rpcnd simp2d simp3d eldifpr syl3anbrc simpr eldifsn
    w3a rpcnne0d sylibr logbval syl2anc ) ACDEFZBGFZHZAIJKLMFZBIJNMFZABOPBQEAQE
    RPSURAIFAJTZAKTZUSURAURAGFZVAVBUPVCVAVBUKUQAUAUBZUCUDURVCVAVBVDUEURVCVAVBVD
    UFAIJKUGUHURBIFBJTHUTURBUPUQUIULBIJUJUMABUNUO $.

  $( Closure of the general logarithm with integer base on positive reals.  See
     ~ logbcl .  (Contributed by Thierry Arnoux, 27-Sep-2017.) $)
  rnlogbcl $p |- ( ( B e. ( ZZ>= ` 2 ) /\ X e. RR+ ) -> ( B logb X ) e. RR ) $=
    ( c2 cuz cfv wcel crp wa clogb co clog cdiv cr rnlogbval simpr relogcld cc0
    wne c1 w3a rnlogblem adantr simp1d simp3d logne0 syl2anc redivcld eqeltrd )
    ACDEFZBGFZHZABIJBKEZAKEZLJMABNUKULUMUKBUIUJOPUKAUKAGFZAQRZASRZUIUNUOUPTUJAU
    AUBZUCZPUKUNUPUMQRURUKUNUOUPUQUDAUEUFUGUH $.

  $( Closure of the general logarithm with integer base on positive reals.
     (Contributed by Thierry Arnoux, 27-Sep-2017.) $)
  relogbcl $p |- ( ( B e. RR+ /\ X e. RR+ /\ B =/= 1 )
              -> ( B logb X ) e. RR ) $=
    ( crp wcel c1 wne w3a clogb co clog cfv cdiv cr cc cc0 cdif rpcnne0d sylibr
    wa relogcl cpr csn wceq simp1 simp3 df-3an sylanbrc eldifpr eldifsn logbval
    simp2 syl2anc 3ad2ant2 3ad2ant1 logne0 3adant2 redivcld eqeltrd ) ACDZBCDZA
    EFZGZABHIZBJKZAJKZLIZMVBANOEUAPDZBNOUBPDZVCVFUCVBANDZAOFZVAGZVGVBVIVJSVAVKV
    BAUSUTVAUDQUSUTVAUEVIVJVAUFUGANOEUHRVBBNDBOFSVHVBBUSUTVAUKQBNOUIRABUJULVBVD
    VEUTUSVDMDVABTUMUSUTVEMDVAATUNUSVAVEOFUTAUOUPUQUR $.

  $( The natural logarithm of ` 1 ` in base ` B ` .  See ~ log1 (Contributed by
     Thierry Arnoux, 27-Sep-2017.) $)
  logb1 $p |- ( ( B e. CC /\ B =/= 0 /\ B =/= 1 ) -> ( B logb 1 ) = 0 ) $=
    ( cc wcel cc0 wne c1 w3a clogb co clog cfv cdiv cpr cdif eldifpr csn ax-1cn
    wceq ax-1ne0 eldifsn mpbir2an logbval mpan2 sylbir log1 oveq1i simp1 logcld
    simp2 logccne0 div0d syl5eq eqtrd ) ABCZADEZAFEZGZAFHIZFJKZAJKZLIZDUQABDFMN
    CZURVARZABDFOVBFBDPNCZVCVDFBCFDEQSFBDTUAAFUBUCUDUQVADUTLIDUSDUTLUEUFUQUTUQA
    UNUOUPUGUNUOUPUIUHAUJUKULUM $.

  $( Identity law for general logarithm with integer base.  (Contributed by
     Thierry Arnoux, 27-Sep-2017.) $)
  nnlogbexp $p |- ( ( B e. ( ZZ>= ` 2 ) /\ M e. ZZ ) ->
    ( B logb ( B ^ M ) ) = M ) $=
    ( cfv wcel wa cexp co clogb wceq cc0 c1 cc wne adantr oveq2d clog cdiv cdif
    simpr syl2anc c2 cuz cz crp w3a rnlogblem simp1d rpcnd simp2d logb1 syl3anc
    simp3d exp0d eqtrd 3eqtr4d cmul cpr csn eldifpr syl3anbrc rpexpcld rpcnne0d
    eldifsn sylibr logbval ccxp cr logcxpd cxpexpzd fveq2d eqtr3d oveq1d logcld
    zred recnd logne0 divcan4d 3eqtr2d pm2.61dane ) AUAUBCDZBUCDZEZAABFGZHGZBIB
    JWBBJIZEZAKHGZJWDBWFALDZAJMZAKMZWGJIWBWHWEWBAWBAUDDZWIWJVTWKWIWJUEWAAUFNZUG
    ZUHZNZWBWIWEWBWKWIWJWLUIZNWBWJWEWBWKWIWJWLULZNAUJUKWFWCKAHWFWCAJFGKWFBJAFWB
    WESZOWFAWOUMUNOWRUOWBBJMZEZWDWCPCZAPCZQGZBXBUPGZXBQGBWTALJKUQRDZWCLJURRDZWD
    XCIWTWHWIWJXEWBWHWSWNNZWBWIWSWPNZWBWJWSWQNZALJKUSUTWTWCLDWCJMEXFWTWCWTABWBW
    KWSWMNZWBWAWSVTWASZNZVAVBWCLJVCVDAWCVETWTXDXAXBQWTABVFGZPCXDXAWTABXJWBBVGDW
    SWBBXKVNNZVHWTXMWCPWTABXGXHXLVIVJVKVLWTBXBWTBXNVOWTAXGXHVMWTWKWJXBJMXJXIAVP
    TVQVRVS $.

  $( Logarithm of a reciprocal changes sign.  See ~ logrec (Contributed by
     Thierry Arnoux, 27-Sep-2017.) $)
  logbrec $p |- ( ( B e. ( ZZ>= ` 2 ) /\ A e. RR+ ) ->
    ( B logb ( 1 / A ) ) = -u ( B logb A ) ) $=
    ( c2 cfv wcel crp c1 cdiv co clog cneg wceq rnlogbval logcld cc0 wne adantr
    clogb relogcld cpi cuz simpr rpreccld syldan negeqd rpne0d rnlogblem simp1d
    wa rpcnd recnd simp3d logne0 syl2anc divnegd reccld recne0d cc reim0d pipos
    cim 0re gtneii necomd eqnetrd logrec syl3anc eqcomd negcon1ad oveq1d 3eqtrd
    a1i eqtr4d ) BCUADEZAFEZUIZBGAHIZRIZVQJDZBJDZHIZBARIZKZVNVOVQFEVRWALVPAVNVO
    UBZUCBVQMUDVPWCAJDZVTHIZKWEKZVTHIWAVPWBWFBAMUEVPWEVTVPAVPAWDUJZVPAWDUFZNVPV
    TVPBVNBFEZVOVNWJBOPZBGPZBUGZUHQZSUKVPWJWLVTOPWNVNWLVOVNWJWKWLWMULQBUMUNUOVP
    WGVSVTHVPVSWEVPVQVPAWHWIUPVPAWHWIUQNVPWEVSKZVPAUREAOPWEVADZTPWEWOLWHWIVPWPO
    TVPWEVPAWDSUSVPTOTOPVPOTVBUTVCVLVDVEAVFVGVHVIVJVKVM $.

  $( The general logarithm function is monotone.  See ~ logltb (Contributed by
     Thierry Arnoux, 27-Sep-2017.) $)
  logblt $p |- ( ( B e. ( ZZ>= ` 2 ) /\ X e. RR+ /\ Y e. RR+ ) ->
    ( X < Y <-> ( B logb X ) < ( B logb Y ) ) ) $=
    ( c2 cuz cfv wcel crp w3a clog clt cdiv co clogb relogcld cz wceq rnlogbval
    wbr c1 simp2 simp3 simp1 eluzelz syl zred caddc 1z fveq2i syl6eleqr eluzp1l
    sylancr rplogcld ltdiv1d wb logltb 3adant1 3adant3 3adant2 breq12d 3bitr4d
    1p1e2 ) ADEFZGZBHGZCHGZIZBJFZCJFZKSZVHAJFZLMZVIVKLMZKSBCKSZABNMZACNMZKSVGVH
    VIVKVGBVDVEVFUAOVGCVDVEVFUBOVGAVGAVGVDAPGVDVEVFUCZDAUDUEUFVGTPGATTUGMZEFZGT
    AKSUHVGAVCVSVQVRDEVBUIUJTAUKULUMUNVEVFVNVJUOVDBCUPUQVGVOVLVPVMKVDVEVOVLQVFA
    BRURVDVFVPVMQVEACRUSUTVA $.

  $( ` log 2 ` is less than ` 1 ` .  This is just a weaker form of ~ log2ub
     when no tight upper bound is required.  (Contributed by Thierry Arnoux,
     27-Sep-2017.) $)
  log2le1 $p |- ( log ` 2 ) < 1 $=
    ( c2 clog c5 cdc c3 c6 cdiv co clt wbr c1 2nn0 5nn0 3nn0 6nn0 decltc nn0rei
    deccl cc0 wcel cfv log2ub 3lt10 5lt10 2lt3 6nn decnncl 0nn0 declti ltdiv1ii
    10pos recni 0re gtneii dividi breqtri crp cr 2rp relogcl ax-mp redivcli 1re
    mpbi lttri mp2an ) ABUAZACDZEDZEFDZCDZGHZIJVLKIJVGKIJUBVLVKVKGHZKIVIVKIJVLV
    MIJVHVJECACLMRZEFNORZNMUCAECFLNMOUDUEPPVIVKVKVIVHEVNNRQZVKVJCVOMRQZVQVJCSEF
    NUFUGMUHUKUIZUJVDVKVKVQULSVKUMVRUNZUOUPVGVLKAUQTVGURTUSAUTVAVIVKVPVQVSVBVCV
    EVF $.

