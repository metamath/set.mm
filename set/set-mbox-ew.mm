$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Emmett Weisz
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellaneous Theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Some of these theorems are used in the series of lemmas and theorems proving
  the defining properties of ` setrecs ` .

$)

  ${
    $d ph y z $.  $d x y z $.  $d y z A $.
    nfintd.1 $e |- ( ph -> F/_ x A ) $.
    $( Bound-variable hypothesis builder for intersection.  (Contributed by
       Emmett Weisz, 16-Jan-2020.) $)
    nfintd $p |- ( ph -> F/_ x |^| A ) $=
      ( vz vy cint cv wcel wel wi wal cab df-int nfv nfcrd wnf a1i nfimd nfald
      nfabdw nfcxfrd ) ABCGEHCIZFEJZKZELZFMFECNAUFBFAFOAUEBEAEOAUCUDBABECDPUDBQ
      AUDBORSTUAUB $.
  $}

  ${
    $d x y z $.  $d z ph $.  $d z A $.  $d z B $.
    nfiund.1 $e |- F/ x ph $.
    nfiund.2 $e |- ( ph -> F/_ y A ) $.
    nfiund.3 $e |- ( ph -> F/_ y B ) $.
    $( Bound-variable hypothesis builder for indexed union.  (Contributed by
       Emmett Weisz, 6-Dec-2019.)  Add disjoint variable condition to avoid
       ~ ax-13 .  See ~ nfiundg for a less restrictive version requiring more
       axioms.  (Revised by GG, 20-Jan-2024.) $)
    nfiund $p |- ( ph -> F/_ y U_ x e. A B ) $=
      ( vz ciun cv wcel wrex cab df-iun nfv nfcrd nfrexdw nfabdw nfcxfrd ) ACBD
      EJIKELZBDMZINBIDEOAUBCIAIPAUACBDFGACIEHQRST $.
    $( $j usage 'nfiund' avoids 'ax-13'; $)
  $}

  ${
    $d z ph $.  $d z A $.  $d z B $.  $d z x $.  $d z y $.
    nfiundg.1 $e |- F/ x ph $.
    nfiundg.2 $e |- ( ph -> F/_ y A ) $.
    nfiundg.3 $e |- ( ph -> F/_ y B ) $.
    $( Bound-variable hypothesis builder for indexed union.  Usage of this
       theorem is discouraged because it depends on ~ ax-13 , see ~ nfiund for
       a weaker version that does not require it.  (Contributed by Emmett
       Weisz, 6-Dec-2019.)  (New usage is discouraged.) $)
    nfiundg $p |- ( ph -> F/_ y U_ x e. A B ) $=
      ( vz ciun cv wcel wrex cab df-iun nfv nfcrd nfrexd nfabd nfcxfrd ) ACBDEJ
      IKELZBDMZINBIDEOAUBCIAIPAUACBDFGACIEHQRST $.
  $}

  $( ${
    $d ph y $.  $d x y $.  $d y A $.  $d y B $.
    nfssd.1 $e |- ( ph -> F/_ x A ) $.
    nfssd.2 $e |- ( ph -> F/_ x B ) $.
    $ ( If ` x ` is not free in ` A ` and ` B ` , it is not free in
       ` A C_ B ` .  (Contributed by Emmett Weisz, 26-Jan-2020.) $ )
    nfssd $p |- ( ph -> F/ x A C_ B ) $=
      cA cB wss cA cB cin cA wceq wph vx cA cB dfss2 wph vx cA cB cin cA wph vx
      cA cB cin vy cv cA wcel vy cv cB wcel wa vy cab vy cA cB df-in wph vy cv
      cA wcel vy cv cB wcel wa vx vy wph vy nfv wph vy cv cA wcel vy cv cB wcel
      vx wph vx vy cv cA vx vy cv wnfc wph vx vy cv nfcv a1i nfssd.1 nfeld wph
      vx vy cv cB vx vy cv wnfc wph vx vy cv nfcv a1i nfssd.2 nfeld nfand nfabd
      nfcxfrd nfssd.1 nfeqd nfxfrd $.
  $} $)

  ${
    $d x y A $.  $d y B $.
    $( The indexed union of a collection of ordinal numbers ` B ( x ) ` is
       ordinal.  This proof is based on the proof of ~ ssorduni , but does not
       use it directly, since ~ ssorduni does not work when ` B ` is a proper
       class.  (Contributed by Emmett Weisz, 3-Nov-2019.) $)
    iunord $p |- ( A. x e. A Ord B -> Ord U_ x e. A B ) $=
      ( vy word wral ciun wtr con0 wss ordtr ralimi triun wcel wrex eliun nfra1
      syl cv nfv wi ordelon syl6 rexlimd biimtrid ssrdv ordon trssord 3exp mpii
      rsp ex sylc ) CEZABFZABCGZHZUPIJZUPEZUOCHZABFUQUNUTABCKLABCMRUODUPIDSZUPN
      VACNZABOUOVAINZAVABCPUOVBVCABUNABQVCATUOASBNUNVBVCUAUNABUKUNVBVCCVAUBULUC
      UDUEUFUQURIEZUSUGUQURVDUSUPIUHUIUJUM $.
  $}

  ${
    $d x A $.
    iunordi.B $e |- Ord B $.
    $( The indexed union of a collection of ordinal numbers ` B ( x ) ` is
       ordinal.  (Contributed by Emmett Weisz, 3-Nov-2019.) $)
    iunordi $p |- Ord U_ x e. A B $=
      ( word ciun iunord cv wcel a1i mprg ) CEZABCFEABABCGLAHBIDJK $.
  $}

  ${
    spd.1 $e |- ( ch -> F/ x ps ) $.
    spd.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Specialization deduction, using implicit substitution.  Based on the
       proof of ~ spimed .  (Contributed by Emmett Weisz, 17-Jan-2020.) $)
    spd $p |- ( ch -> ( A. x ph -> ps ) ) $=
      ( wal wex weq wi ax6e biimpd eximii 19.35i 19.9d syl5 ) ADHBDICBABDDEJZAB
      KDDELRABGMNOBCDFPQ $.
  $}

  ${
    $d ph x y $.  $d ch x $.  $d ps y $.
    tfis2d.1 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    tfis2d.2 $e |- ( ph -> ( x e. On -> ( A. y e. x ch -> ps ) ) ) $.
    $( Transfinite Induction Schema, using implicit substitution.  (Contributed
       by Emmett Weisz, 3-May-2020.) $)
    tfis2d $p |- ( ph -> ( x e. On -> ps ) ) $=
      ( cv con0 wcel wi weq wb com12 pm5.74d wral r19.21v a2d biimtrid tfis2 )
      DHZIJZABABKZACKZDEDELZABCAUEBCMFNOUDEUAPACEUAPZKUBUCACEUAQUBAUFBAUBUFBKGN
      RSTN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Examples and properties of set recursion
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d w y z F $.  $d w y z G $.
    $( Equality theorem for set recursion.  (Contributed by Emmett Weisz,
       17-Feb-2021.) $)
    setrecseq $p |- ( F = G -> setrecs ( F ) = setrecs ( G ) ) $=
      ( vw vy vz wceq cv wss cfv wi wal cab csetrecs fveq1 sseq1d imbi2d albidv
      cuni imbi1d df-setrecs abbidv unieqd 3eqtr4g ) ABFZCGZDGZHZUEEGZHZUEAIZUH
      HZJZJZCKZUFUHHZJZEKZDLZRUGUIUEBIZUHHZJZJZCKZUOJZEKZDLZRAMBMUDURVFUDUQVEDU
      DUPVDEUDUNVCUOUDUMVBCUDULVAUGUDUKUTUIUDUJUSUHUEABNOPPQSQUAUBDECATDECBTUC
      $.
  $}

  ${
    $d x y z w $.  $d F y z w $.
    nfsetrecs.1 $e |- F/_ x F $.
    $( Bound-variable hypothesis builder for ` setrecs ` .  (Contributed by
       Emmett Weisz, 21-Oct-2021.) $)
    nfsetrecs $p |- F/_ x setrecs ( F ) $=
      ( vw vy vz csetrecs cv wss cfv wal cab cuni df-setrecs nfv nfcv nffv nfim
      wi nfal nfss nfab nfuni nfcxfr ) ABGDHZEHZIZUEFHZIZUEBJZUHIZSZSZDKZUFUHIZ
      SZFKZELZMEFDBNAURUQAEUPAFUNUOAUMADUGULAUGAOUIUKAUIAOAUJUHAUEBCAUEPQAUHPUA
      RRTUOAORTUBUCUD $.
  $}

  ${
    $d a A $.  $d a C $.
    setrec2mpt.1 $e |- B = setrecs ( ( a e. A |-> S ) ) $.
    setrec2mpt.2 $e |- ( a e. A -> S e. V ) $.
    setrec2mpt.3 $e |- ( ph -> A. a ( a C_ C -> S C_ C ) ) $.
    $( Version of ~ setrec2 where ` F ` is defined using maps-to notation.
       Deduction form is omitted in the second hypothesis for simplicity.  In
       practice, nothing important is lost since we are only interested in one
       choice of ` A ` , ` S ` , and ` V ` at a time.  However, we are
       interested in what happens when ` C ` varies, so deduction form is used
       in the third hypothesis.  (Contributed by Emmett Weisz, 4-Jun-2024.) $)
    setrec2mpt $p |- ( ph -> B C_ C ) $=
      ( cmpt nfmpt1 cv wss wi cfv wcel wa wceq eqid fvmpt2 mpdan wn c0 fvmptndm
      eqimss syl 0ss eqsstrdi pm2.61i sstr2 ax-mp imim2i sylg setrec2 ) ACDGBEK
      ZGGBELHAGMZDNZEDNZOURUQUPPZDNZOGJUSVAURUTENZUSVAOUQBQZVBVCEFQZVBIVCVDRUTE
      SVBGBEFUPUPTZUAUTEUFUGUBVCUCUTUDEGBEUPUQVEUEEUHUIUJUTEDUKULUMUNUO $.

  $}

  ${
    $d F a b $.  $d a ps $.  $d b ch $.  $d b A $.
    setis.1 $e |- B = setrecs ( F ) $.
    setis.2 $e |- ( b = A -> ( ps <-> ch ) ) $.
    setis.3 $e |- ( ph -> A. a ( A. b e. a ps -> A. b e. ( F ` a ) ps ) ) $.
    $( Version of ~ setrec2 expressed as an induction schema.  This theorem is
       a generalization of ~ tfis3 .  (Contributed by Emmett Weisz,
       27-Feb-2022.) $)
    setis $p |- ( ph -> ( A e. B -> ch ) ) $=
      ( wcel cab cv wral cfv wi wal wss ssabral albii sylibr sseld elabg mpbidi
      imbi12i setrec2v ) DELDBHMZLCAAEUHDAEUHFGIABHGNZOZBHUIFPZOZQZGRUIUHSZUKUH
      SZQZGRKUPUMGUNUJUOULBHUITBHUKTUFUAUBUGUCBCHDEJUDUE $.
  $}

  ${
    $d A a x $.  $d B a x $.  $d F a x $.
    elsetrecs.1 $e |- B = setrecs ( F ) $.
    $( Lemma for ~ elsetrecs .  Any element of ` setrecs ( F ) ` is generated
       by some subset of ` setrecs ( F ) ` .  This is much weaker than
       ~ setrec2v .  To see why this lemma also requires ~ setrec1 , consider
       what would happen if we replaced ` B ` with ` { A } ` .  The antecedent
       would still hold, but the consequent would fail in general.  Consider
       dispensing with the deduction form.  (Contributed by Emmett Weisz,
       11-Jul-2021.)  (New usage is discouraged.) $)
    elsetrecslem $p |- ( A e. B -> E. x ( x C_ B /\ A e. ( F ` x ) ) ) $=
      ( va wcel cv wss cfv wa wn wal wex csn cdif ssdifsn simprbi con2i wi wceq
      sseq1 fveq2 eleq2d anbi12d notbid imnan idd cvv vex a1i id setrec1 jctild
      spvv a2i sylbir adantrd 3imtr4g syl alrimiv setrec2v nsyl df-ex sylibr )
      BCGZAHZCIZBVGDJZGZKZLZAMZLVKANVFCCBOPZIZVMVOVFVOCCIVFLCCBQRSVMCVNDFEVMFHZ
      VNIZVPDJZVNIZTZFVMVPCIZBVRGZKZLZVTVLWDAFVGVPUAZVKWCWEVHWAVJWBVGVPCUBWEVIV
      RBVGVPDUCUDUEUFUOWDWABVPGLZKVRCIZWBLZKZVQVSWDWAWIWFWDWAWHTWAWITWAWBUGWAWH
      WIWAWHWHWGWAWHUHWAVPCDEVPUIGWAFUJUKWAULUMUNUPUQURVPCBQVRCBQUSUTVAVBVCVKAV
      DVE $.

    $( A set ` A ` is an element of ` setrecs ( F ) ` iff ` A ` is generated by
       some subset of ` setrecs ( F ) ` .  The proof requires both ~ setrec1
       and ~ setrec2 , but this theorem is not strong enough to uniquely
       determine ` setrecs ( F ) ` .  If ` F ` respects the subset relation,
       the theorem still holds if both occurrences of ` e. ` are replaced by
       ` C_ ` for a stronger version of the theorem.  (Contributed by Emmett
       Weisz, 12-Jul-2021.) $)
    elsetrecs $p |- ( A e. B <-> E. x ( x C_ B /\ A e. ( F ` x ) ) ) $=
      ( wcel wss cfv wex elsetrecslem cvv vex a1i setrec1 sselda exlimiv impbii
      cv wa id ) BCFZARZCGZBUBDHZFSZAIABCDEJUEUAAUCUDCBUCUBCDEUBKFUCALMUCTNOPQ
      $.
  $}

  ${
    $d ph x $.  $d F x $.  $d G x $.
    setrecsss.1 $e |- ( ph -> Fun G ) $.
    setrecsss.2 $e |- ( ph -> F C_ G ) $.
    $( The ` setrecs ` operator respects the subset relation between two
       functions ` F ` and ` G ` .  (Contributed by Emmett Weisz,
       13-Mar-2022.) $)
    setrecsss $p |- ( ph -> setrecs ( F ) C_ setrecs ( G ) ) $=
      ( vx csetrecs eqid cv wss cfv wi wa csn cima cuni syl wfun wceq funfv cvv
      imass1 unissd funss sylc 3sstr4d wcel vex a1i simpr setrec1 sstrd alrimiv
      adantr ex setrec2v ) ABGZCGZBFUQHAFIZURJZUSBKZURJZLFAUTVBAUTMZVAUSCKZURAV
      AVDJUTABUSNZOZPZCVEOZPZVAVDAVFVHABCJZVFVHJEBCVEUBQUCABRZVAVGSAVJCRZVKEDBC
      UDUEUSBTQAVLVDVISDUSCTQUFUNVCUSURCURHUSUAUGVCFUHUIAUTUJUKULUOUMUP $.
  $}

  ${
    $d B x $.  $d F x $.  $d ph x $.
    setrecsres.1 $e |- B = setrecs ( F ) $.
    setrecsres.2 $e |- ( ph -> Fun F ) $.
    $( A recursively generated class is unaffected when its input function is
       restricted to subsets of the class.  (Contributed by Emmett Weisz,
       14-Mar-2022.) $)
    setrecsres $p |- ( ph -> B = setrecs ( ( F |` ~P B ) ) ) $=
      ( vx cpw cres csetrecs cv wss cfv wi wa wceq id resss a1i setrecsss wcel
      sseqtrrdi sylan9ssr velpw sylbir syl eqid cvv vex setrec1 adantl eqsstrrd
      fvres ex alrimiv setrec2v eqssd ) ABCBGZHZIZABUSCFDAFJZUSKZUTCLZUSKZMFAVA
      VCAVANZVBUTURLZUSVDUTBKZVEVBOZVAAUTUSBVAPZAUSCIBAURCEURCKACUQQRSDUAZUBVFU
      TUQTVGFBUCUTUQCULUDUEVAVEUSKAVAUTUSURUSUFUTUGTVAFUHRVHUIUJUKUMUNUOVIUP $.
  $}

  ${
    $d a F $.  $d a x $.
    vsetrec.1 $e |- F = ( x e. _V |-> ~P x ) $.
    $( Construct ` _V ` using set recursion.  The proof indirectly uses
       ~ trcl , which relies on ` rec ` , but theoretically ` C ` in ~ trcl
       could be constructed using ` setrecs ` instead.  The proof of this
       theorem uses the dummy variable ` a ` rather than ` x ` to avoid a
       distinct variable requirement between ` F ` and ` x ` .  (Contributed by
       Emmett Weisz, 23-Jun-2021.) $)
    vsetrec $p |- setrecs ( F ) = _V $=
      ( va cv csetrecs wss wcel wi cvv wceq setind cpw vex pwid cfv vpwex fvmpt
      pweq ax-mp eqid a1i id setrec1 eqsstrrid sseld mpi mpg ) DEZBFZGZUIUJHZIU
      JJKDDUJLUKUIUIMZHULUIDNZOUKUMUJUIUKUMUIBPZUJUIJHZUOUMKUNAUIAEZMUMJBUQUISC
      DQRTUKUIUJBUJUAUPUKUNUBUKUCUDUEUFUGUH $.
  $}

  ${
    $d ph x $.  $d F x $.
    0setrec.1 $e |- ( ph -> ( F ` (/) ) = (/) ) $.
    $( If a function sends the empty set to itself, the function will not
       recursively generate any sets, regardless of its other values.
       (Contributed by Emmett Weisz, 23-Jun-2021.) $)
    0setrec $p |- ( ph -> setrecs ( F ) = (/) ) $=
      ( vx csetrecs c0 wss wceq eqid cv cfv wi ss0 fveq2 sylan9eqr eqimss syl56
      ex alrimiv setrec2v syl ) ABEZFGUBFHAUBFBDUBIADJZFGZUCBKZFGZLDUDUCFHZAUEF
      HZUFUCMAUGUHUGAUEFBKFUCFBNCORUEFPQSTUBMUA $.
  $}

  ${
    $d a x $.
    onsetreclem1.1 $e |- F = ( x e. _V |-> { U. x , suc U. x } ) $.
    $( Lemma for ~ onsetrec .  (Contributed by Emmett Weisz, 22-Jun-2021.)
       (New usage is discouraged.) $)
    onsetreclem1 $p |- ( F ` a ) = { U. a , suc U. a } $=
      ( cv cfv cuni csuc cpr wceq cvv unieq suceq syl preq12d prex fvmpt elv )
      CEZBFSGZTHZIZJCASAEZGZUDHZIUBKBUCSJZUDTUEUAUCSLZUFUDTJUEUAJUGUDTMNODTUAPQ
      R $.
  $}

  ${
    $d a x $.
    onsetreclem2.1 $e |- F = ( x e. _V |-> { U. x , suc U. x } ) $.
    $( Lemma for ~ onsetrec .  (Contributed by Emmett Weisz, 22-Jun-2021.)
       (New usage is discouraged.) $)
    onsetreclem2 $p |- ( a C_ On -> ( F ` a ) C_ On ) $=
      ( cv con0 wss cfv cuni csuc cpr onsetreclem1 wcel ssonunii onsuc syl2anc2
      vex prssi eqsstrid ) CEZFGZTBHTIZUBJZKZFABCDLUAUBFMUCFMUDFGTCQNUBOUBUCFRP
      S $.
  $}

  ${
    $d a x $.
    onsetreclem3.1 $e |- F = ( x e. _V |-> { U. x , suc U. x } ) $.
    $( Lemma for ~ onsetrec .  (Contributed by Emmett Weisz, 22-Jun-2021.)
       (New usage is discouraged.) $)
    onsetreclem3 $p |- ( a e. On -> a e. ( F ` a ) ) $=
      ( cv con0 wcel cuni csuc cpr cfv wceq word eloni orduniorsuc syl vex elpr
      wo sylibr onsetreclem1 eleqtrrdi ) CEZFGZUCUCHZUEIZJZUCBKUDUCUELUCUFLSZUC
      UGGUDUCMUHUCNUCOPUCUEUFCQRTABCDUAUB $.
  $}

  ${
    $d a F $.  $d a x $.
    onsetrec.1 $e |- F = ( x e. _V |-> { U. x , suc U. x } ) $.
    $( Construct ` On ` using set recursion.  When ` x e. On ` , the function
       ` F ` constructs the least ordinal greater than any of the elements of
       ` x ` , which is ` U. x ` for a limit ordinal and ` suc U. x ` for a
       successor ordinal.

       For example, ` ( F `` { 1o , 2o } ) `
       ` = { U. { 1o , 2o } , suc U. { 1o , 2o } } = { 2o , 3o } ` which
       contains ` 3o ` , and
       ` ( F `` _om ) = { U. _om , suc U. _om } = { _om , _om +o 1o } ` , which
       contains ` _om ` .  If we start with the empty set and keep applying
       ` F ` transfinitely many times, all ordinal numbers will be generated.

       Any function ` F ` fulfilling lemmas ~ onsetreclem2 and ~ onsetreclem3
       will recursively generate ` On ` ; for example,
       ` F = ( x e. _V |-> suc suc U. x } ) ` also works.  Whether this
       function or the function in the theorem is used, taking this theorem as
       a definition of ` On ` is unsatisfying because it relies on the
       different properties of limit and successor ordinals.  A different
       approach could be to let ` F = ( x e. _V |-> { y e. ~P x | Tr y } ) ` ,
       based on ~ dfon2 .

       The proof of this theorem uses the dummy variable ` a ` rather than
       ` x ` to avoid a distinct variable condition between ` F ` and ` x ` .
       (Contributed by Emmett Weisz, 22-Jun-2021.) $)
    onsetrec $p |- setrecs ( F ) = On $=
      ( va csetrecs con0 wss cv wcel wi wral wceq wtru eqid onsetreclem2 ax-gen
      cfv wal a1i setrec2v mptru cvv vex setrec1 onsetreclem3 ssel syl2im com12
      id rgen tfi mp2an ) BEZFGZDHZUMGZUOUMIZJZDFKUMFLUNMUMFBDUMNZUOFGUOBQZFGJZ
      DRMVADABDCOPSTUAURDFUPUOFIZUQUPUTUMGVBUOUTIUQUPUOUMBUSUOUBIUPDUCSUPUIUDAB
      DCUEUTUMUOUFUGUHUJDUMUKUL $.
  $}
$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Construction of Games and Surreal Numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
Model organization after organization of reals - see TOC
$)

  $( Class of partizan game forms. $)
  $c Pg $.

  $( Extend class notation to include the class of partisan game forms. $)
  cpg $a class Pg $.

  $( Define the class of partisan games.  More precisely, this is the class of
     partisan game forms, many of which represent equal partisan games.  In
     Metamath, equality between partisan games is represented by a different
     equivalence relation than class equality.  (Contributed by Emmett Weisz,
     22-Aug-2021.) $)
  df-pg $a |- Pg = setrecs ( ( x e. _V |-> ( ~P x X. ~P x ) ) ) $.

  ${
    $d A x $.  $d x y $.

    $( Lemma for ~ elpg .  (Contributed by Emmett Weisz, 28-Aug-2021.) $)
    elpglem1 $p |- ( E. x ( x C_ Pg
                            /\ ( ( 1st ` A ) e. ~P x /\ ( 2nd ` A ) e. ~P x ) )
                      -> ( ( 1st ` A ) C_ Pg /\ ( 2nd ` A ) C_ Pg ) ) $=
      ( cv cpg wss c1st cfv cpw wcel c2nd wa elpwi adantl simpl sstrd anim12dan
      exlimiv ) ACZDEZBFGZRHZIZBJGZUAIZKKTDEZUCDEZKASUBUEUDUFSUBKTRDUBTRESTRLMS
      UBNOSUDKUCRDUDUCRESUCRLMSUDNOPQ $.

    $( Lemma for ~ elpg .  (Contributed by Emmett Weisz, 28-Aug-2021.) $)
    elpglem2 $p |- ( ( ( 1st ` A ) C_ Pg /\ ( 2nd ` A ) C_ Pg )
                     -> E. x ( x C_ Pg
                      /\ ( ( 1st ` A ) e. ~P x /\ ( 2nd ` A ) e. ~P x ) ) ) $=
      ( c1st cfv cpg wss c2nd wa cv cpw wcel wceq wi fvex unex isseti sseqtrrid
      cun elpw2 sylibr sseq1 unss bitr4di biimprd ssun1 id vex ssun2 jca jctird
      eximii 19.37iv ) BCDZEFBGDZEFHZAIZEFZUMUPJZKZUNURKZHZHZAUPUMUNRZLZUOVBMAA
      VCUMUNBCNBGNOPVDUOUQVAVDUQUOVDUQVCEFUOUPVCEUAUMUNEUBUCUDVDUSUTVDUMUPFUSVD
      VCUMUPUMUNUEVDUFZQUMUPAUGZSTVDUNUPFUTVDVCUNUPUNUMUHVEQUNUPVFSTUIUJUKUL $.

    $( Lemma for ~ elpg .  (Contributed by Emmett Weisz, 28-Aug-2021.) $)
    elpglem3 $p |- ( E. x ( x C_ Pg
                             /\ A e. ( ( y e. _V |-> ( ~P y X. ~P y ) ) ` x ) )
               <-> ( A e. ( _V X. _V ) /\ E. x ( x C_ Pg
                    /\ ( ( 1st ` A ) e. ~P x /\ ( 2nd ` A ) e. ~P x ) ) ) ) $=
      ( cv cpg wss cvv cpw cxp cmpt cfv wcel wex c1st c2nd wceq vex weq bitri
      wa pweq sqxpeqd eqid pwex xpex fvmpt ax-mp eleq2i elxp7 anbi2i an12 exbii
      19.42v ) ADZEFZCUNBGBDZHZUQIZJZKZLZTZAMCGGILZUOCNKUNHZLCOKVDLTZTZTZAMVCVF
      AMTVBVGAVBUOVCVETZTVGVAVHUOVACVDVDIZLVHUTVICUNGLUTVIPAQZBUNURVIGUSBARUQVD
      UPUNUAUBUSUCVDVDUNVJUDZVKUEUFUGUHCVDVDUISUJUOVCVEUKSULVCVFAUMS $.

    $( Membership in the class of partisan games.  In John Horton Conway's On
       Numbers and Games, this is stated as "If ` L ` and ` R ` are any two
       sets of games, then there is a game ` { L | R } ` .  All games are
       constructed in this way."  The first sentence corresponds to the
       backward direction of our theorem, and the second to the forward
       direction.  (Contributed by Emmett Weisz, 27-Aug-2021.) $)
    elpg $p |- ( A e. Pg <->
      ( A e. ( _V X. _V ) /\ ( 1st ` A ) C_ Pg /\ ( 2nd ` A ) C_ Pg ) ) $=
      ( vx vy cvv cxp wcel cv cpg wss c1st cfv cpw wa wex w3a elpglem1 elpglem2
      c2nd impbii anbi2i cmpt df-pg elsetrecs elpglem3 bitri 3anass 3bitr4i ) A
      DDEFZBGZHIZAJKZUILZFARKZULFMMBNZMZUHUKHIZUMHIZMZMAHFZUHUPUQOUNURUHUNURBAP
      BAQSTUSUJAUICDCGLZUTEUAZKFMBNUOBAHVACUBUCBCAUDUEUHUPUQUFUG $.
  $}

  ${
    $( Lemma for ~ pgind .  (Contributed by Emmett Weisz, 27-May-2024.)
       (New usage is discouraged.) $)
    pgindlem $p |- ( x e. ( ~P z X. ~P z )
                   -> ( ( 1st ` x ) u. ( 2nd ` x ) ) C_ z ) $=
      ( cv cpw cxp wcel c1st cfv c2nd xp1st elpwid xp2nd unssd ) ACZBCZDZPEFZNG
      HZNIHZOQRONPPJKQSONPPLKM $.
  $}

  ${
    $d A y $.  $d a x y z $.  $d ch x z $.  $d ph z $.  $d ps y $.  $d th y $.
    pgindnf.1 $e |- F/ x ph $.
    pgindnf.2 $e |- F/ y ph $.
    pgindnf.3 $e |- ( x = y -> ( ps <-> ch ) ) $.
    pgindnf.4 $e |- ( y = A -> ( ch <-> th ) ) $.
    pgindnf.5 $e |- ( ph -> A. x ( A. y e. ( ( 1st ` x ) u. ( 2nd ` x ) ) ch
                                 -> ps ) ) $.
    $( Version of ~ pgind with extraneous not-free requirements.  (Contributed
       by Emmett Weisz, 27-May-2024.)  (New usage is discouraged.) $)
    pgindnf $p |- ( ph -> ( A e. Pg -> th ) ) $=
      ( va vz cvv cv wral cfv wcel wceq cpg cpw cxp cmpt df-pg wi nfv nfan c1st
      wa c2nd cun pgindlem imim1d ralimdv2 19.21bi sylan9r impancom ralrimi vex
      sseld pweq sqxpeqd eqid vpwex xpex fvmpt ax-mp a1i cbvralv2 sylib alrimiv
      eqcomi ex setis ) ACDGUAMOMPZUBZVQUCZUDZNFMUEKACFNPZQZCFVTVSRZQZUFNAWAWCA
      WAUJZBEVTUBZWEUCZQWCWDBEWFAWAEHWAEUGUHAEPZWFSZWABWHWACFWGUIRWGUKRULZQZABW
      HCCFVTWIWHFPZWISWKVTSCWHWIVTWKENUMVAUNUOAWJBUFELUPUQURUSBCEFWFWBJWFWBTWGW
      KTWBWFVTOSWBWFTNUTMVTVRWFOVSVPVTTVQWEVPVTVBVCVSVDWEWENVEZWLVFVGVHVMVIVJVK
      VNVLVO $.
  $}

  ${
    $d A y $.  $d ch x $.  $d ps y $.  $d th y $.  $d x y $.
    pgind.1 $e |- ( x = y -> ( ps <-> ch ) ) $.
    pgind.2 $e |- ( y = A -> ( ch <-> th ) ) $.
    pgind.3 $e |- ( ph -> A. x ( A. y e. ( ( 1st ` x ) u. ( 2nd ` x ) ) ch
                               -> ps ) ) $.
    $( Induction on partizan games.  (Contributed by Emmett Weisz,
       27-May-2024.) $)
    pgind $p |- ( ph -> ( A e. Pg -> th ) ) $=
      ( wex cpg wcel wi 19.8a nfe1 nfex cv cfv exlimi c1st c2nd wral nfa1 nfra1
      cun wal nfv nfim nfal pgindnf 3syl ) AAFKZUMEKZGLMDNAFOUMEOUNBCDEFGUMEPUM
      FEAFPQHIUMCFERZUASUOUBSUFZUCZBNZEUGZEUREUDAUSFURFEUQBFCFUPUEBFUHUIUJJTTUK
      UL $.
  $}

$( (End of Emmett Weisz's mathbox.) $)
