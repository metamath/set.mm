$[ set.mm $]

  $c >w $.
  $c <w $.
  $c =h $.
  $c eh $.
  $c Ch $.
  $c Type $.

  $( Define term to wff conversion. $)
  wtw $a wff >w A $.

  $( Define wff to term conversion. $)
  cwt $a class <w ph $.

  $( Define the equality term. $)
  ceqh $a class =h A $.

  $( Define the indefinite descriptor. $)
  ceh $a class eh A $.

  $( Define the set of types. $)
  ctyp $a class Type $.

  $( Define the set of term choice functions. $)
  cche $a class Ch $.

  $( Define term to wff conversion. $)
  df-tw $a |- ( >w A <-> (/) e. A ) $.

  ${
    $d x ph $.  $d f x y A $.
    $( Define term to wff conversion. $)
    df-wt $a |- <w ph = { x e. 1o | ph } $.

    $( Define the equality term. $)
    df-eqh $a |- =h A = ( x e. A |-> ( y e. A |-> <w x = y ) ) $.
  
    $( Define the indefinite descriptor. (Note that the actual indefinite
       descriptor, given a choice function ` E ` , is ` ( E o. eh A ) ` .) $)
    df-eh $a |- eh A = ( f e. ( A ^m 2o ) |->
      if ( f = ( A X. 1o ) , A , ( `' f " { 1o } ) ) ) $.
  $}

  $( Define the set of all types, the model of HOL. $)
  df-typ $a |- Type = ( ( R1 ` ( om +o om ) ) \ 1o ) $.

  $( Define the set of choice functions on ` Type ` .  The if statement is
     designed so that  $)
  df-che $a |- Ch = [_ { f e. ( Type ^m U. Type ) | A. x e. Type
    ( f ` x ) e. x } / y ]_ if ( y = (/) , ( Type ^m U. Type ) , y ) $.

  $( Equality theorem for term-to-wff conversion. $)
  tweq $p |- ( A = B -> ( >w A <-> >w B ) ) $=
    ( wceq c0 wcel wtw eleq2 df-tw 3bitr4g ) ABCDAEDBEAFBFABDGAHBHI $.
    $( [20-Dec-2014] $)

  $( The truth term corresponds to the set ` 1o ` . $)
  wttru $p |- >w 1o $=
    ( c1o wtw c0 wcel 0lt1o df-tw mpbir ) ABCADEAFG $.
    $( [20-Dec-2014] $)

  $( The truth term corresponds to the set ` 1o ` . $)
  wtfal $p |- -. >w (/) $=
    ( c0 wtw wcel noel df-tw mtbir ) ABAACADAEF $.
    $( [20-Dec-2014] $)

  ${
    $d x ph $.  $d x ps $.
    $( Equality theorem for term-to-wff conversion. $)
    wteq $p |- ( ( ph <-> ps ) -> <w ph = <w ps ) $=
      ( vx wb c1o crab cwt id rabbidv df-wt 3eqtr4g ) ABDZACEFBCEFAGBGLABCELHIACJ
      BCJK $.
      $( [20-Dec-2014] $)

    $( The term-to-wff and wff-to-term operations are inverses. $)
    twwt $p |- ( >w <w ph <-> ph ) $=
      ( vx cwt wtw c1o crab c0 wcel wceq wb df-wt tweq ax-mp df-tw cv biidd elrab
      0lt1o mpbiran 3bitri ) ACZDZABEFZDZGUCHZAUAUCIUBUDJABKUAUCLMUCNUEGEHAAABGEB
      OGIAPQRST $.
      $( [20-Dec-2014] $)

    $( The truth term corresponds to the set ` 1o ` . $)
    twtru $p |- ( ph <-> <w ph = 1o ) $=
      ( vx cwt c1o wceq crab wral id ralrimivw rabid2 sylibr df-wt syl6reqr wttru
      wtw tweq mpbiri twwt sylib impbii ) AACZDEZADABDFZUAAABDGDUCEAABDAHIABDJKAB
      LMUBUAOZAUBUDDONUADPQARST $.
      $( [20-Dec-2014] $)

    $( The falsity term corresponds to the set ` (/) ` . $)
    twfal $p |- ( -. ph <-> <w ph = (/) ) $=
      ( vx wn cwt c0 wceq crab df-wt wral id ralrimivw rabeq0 sylibr syl5eq wtfal
      c1o wtw twwt tweq syl5bbr mtbiri impbii ) ACZADZEFZUCUDABPGZEABHUCUCBPIUFEF
      UCUCBPUCJKABPLMNUEAEQZOAUDQUEUGARUDESTUAUB $.
      $( [20-Dec-2014] $)
  $}

  $( The term-to-wff and wff-to-term operations are inverses. $)
  wttw $p |- ( A e. 2o -> <w >w A = A ) $=
    ( wtw cwt wceq c0 c1o cpr c2o wcel wo elprg ibi wn wtfal mtbiri twfal sylib
    tweq id eqtr4d wttru mpbiri twtru jaoi syl df2o2 df1o2 preq2i eqtr4i eleq2s
    csn ) ABZCZADZAEFGZHAUOIZAEDZAFDZJZUNUPUSAEFUOKLUQUNURUQUMEAUQULMUMEDUQULEB
    NAEROULPQUQSTURUMFAURULUMFDURULFBUAAFRUBULUCQURSTUDUEHEEUKZGUOUFFUTEUGUHUIU
    J $.
    $( [20-Dec-2014] $)

  $( The truth term is a member of the boolean type. $)
  holwtru $p |- ( ph -> 1o e. 2o ) $=
    ( c1o c2o wcel c0 csn cpr p0ex prid2 df1o2 df2o2 eleq12i mpbir a1i ) BCDZAO
    EFZEPGZDEPHIBPCQJKLMN $.
    $( [20-Dec-2014] $)

  $( The conversion of a wff is of boolean type. $)
  twcl $p |- <w ph e. 2o $=
    ( cwt c2o wcel c1o wceq twtru biimpi holwtru eqeltrd wn twfal csn cpr prid1
    c0 0ex df2o2 eleqtrri syl6eqel pm2.61i ) AABZCDAUBECAUBEFAGHAIJAKZUBPCUCUBP
    FALHPPPMZNCPUDQORSTUA $.
    $( [20-Dec-2014] $)

  $( The conversion of a wff is of boolean type. $)
  twcld $p |- ( ph -> <w ps e. 2o ) $=
    ( cwt c2o wcel twcl a1i ) BCDEABFG $.
    $( [20-Dec-2014] $)

  $( The conversion of a wff exists. $)
  twex $p |- <w ph e. _V $=
    ( cwt c2o twcl elexi ) ABCADE $.
    $( [20-Dec-2014] $)

  $( The definition of the truth term. $)
  holdftru $p |- 1o = <w ( p e. 2o |-> p ) = ( p e. 2o |-> p ) $=
    ( c2o cv cmpt wceq cwt c1o eqid twtru mpbi eqcomi ) ABACDZLEZFZGMNGELHMIJK
    $.
    $( [20-Dec-2014] $)

  ${
    $d x y A $.  $d x y B $.  $d y C $.
    eqhval.1 $e |- ( ph -> A e. Type ) $.
    eqhval.2 $e |- ( ph -> B e. A ) $.
    eqhval.3 $e |- ( ph -> C e. A ) $.
    $( Value of the equality term. $)
    eqhval $p |- ( ph -> ( ( =h A ` B ) ` C ) = <w B = C ) $=
      ( vy vx cfv cv wceq cwt cmpt wcel cvv ctyp syl wb wteq ceqh mptexg df-eqh
      eqeq1 mpteq2dv fvmptg syl2anc fveq1d eqeq2 eqid twex fvmpt eqtrd ) ADCBUA
      ZJZJDHBCHKZLZMZNZJZCDLZMZADUOUSACBOUSPOZUOUSLFABQOVCEHBURQUBRICHBIKZUPLZM
      ZNUSBPUNVDCLZHBVFURVGVEUQSVFURLVDCUPUDVEUQTRUEIHBUCUFUGUHADBOUTVBLGHDURVB
      BUSUPDLUQVASURVBLUPDCUIUQVATRUSUJVAUKULRUM $.
      $( [20-Dec-2014] $)

    ${
      eqh1.1 $e |- ( ph -> >w ( ( =h A ` B ) ` C ) ) $.
      $( Value of the equality term. $)
      eqh1b $p |- ( ph -> >w <w B = C ) $=
        ( ceqh cfv wtw wceq cwt wb eqhval tweq syl mpbid ) ADCBIJJZKZCDLMZKZHAS
        UALTUBNABCDEFGOSUAPQR $.
        $( [20-Dec-2014] $)

      $( Value of the equality term. $)
      eqh1 $p |- ( ph -> B = C ) $=
        ( wceq cwt wtw eqh1b twwt sylib ) ACDIZJKOABCDEFGHLOMN $.
        $( [20-Dec-2014] $)
    $}

    ${
      eqh2b.4 $e |- ( ph -> >w <w B = C ) $.
      $( Value of the equality term. $)
      eqh2b $p |- ( ph -> >w ( ( =h A ` B ) ` C ) ) $=
        ( ceqh cfv wtw wceq cwt wb eqhval tweq syl mpbird ) ADCBIJJZKZCDLMZKZHA
        SUALTUBNABCDEFGOSUAPQR $.
        $( [20-Dec-2014] $)
    $}

    ${
      eqh2.4 $e |- ( ph -> B = C ) $.
      $( Value of the equality term. $)
      eqh2 $p |- ( ph -> >w ( ( =h A ` B ) ` C ) ) $=
        ( wceq cwt wtw twwt sylibr eqh2b ) ABCDEFGACDIZOJKHOLMN $.
        $( [20-Dec-2014] $)
    $}
  $}

  ${
    wteqeq12d.1 $e |- ( ph -> B = D ) $.
    wteqeq12d.2 $e |- ( ph -> C = E ) $.
    $( Equality theorem for the equality term. $)
    wteqeq12d $p |- ( ph -> <w B = C = <w D = E ) $=
      ( wceq wb cwt eqeq12d wteq syl ) ABCHZDEHZINJOJHABDCEFGKNOLM $.
      $( [20-Dec-2014] $)
  $}

  $( The set of types is a set. $)
  typex $p |- Type e. _V $=
    ( ctyp com coa cr1 cfv c1o cdif cvv df-typ wcel fvex difexg ax-mp eqeltri
    co ) ABBCOZDEZFGZHIQHJRHJPDKQFHLMN $.
    $( [20-Dec-2014] $)

  $( Elementhood in the set of types. $)
  eltyp $p |- ( A e. Type <-> ( A e. ( R1 ` ( om +o om ) ) /\ A =/= (/) ) ) $=
    ( ctyp wcel com coa co cr1 cfv c0 csn wne wa c1o df-typ df1o2 difeq2i eqtri
    cdif eleq2i eldifsn bitri ) ABCADDEFGHZIJZRZCAUBCAIKLBUDABUBMRUDNMUCUBOPQSA
    UBITUA $.
    $( [20-Dec-2014] $)

  $( ` 2 x. om ` is a limit ordinal. $)
  lim2om $p |- Lim ( om +o om ) $=
    ( com con0 wcel wlim wa coa co omelon limom pm3.2i oalimcl mp2an ) ABCZMADZ
    EAAFGDHMNHIJAABKL $.
    $( [20-Dec-2014] $)

  $( A type is well-founded. $)
  typwf $p |- ( A e. Type -> A e. U. ( R1 " On ) ) $=
    ( ctyp wcel com coa co cr1 cfv con0 cima cuni wne eltyp simplbi r1elwf syl
    c0 ) ABCZADDEFZGHCZAGIJKCRTAQLAMNASOP $.
    $( [20-Dec-2014] $)

  $( A type has rank below ` ( om +o om ) ` . $)
  typrank $p |- ( A e. Type -> ( rank ` A ) e. ( om +o om ) ) $=
    ( ctyp wcel com coa co cr1 cfv crnk c0 wne eltyp simplbi con0 cima wb typwf
    cuni cvv wlim ovex lim2om limelon mp2an rankr1ag sylancl mpbid ) ABCZADDEFZ
    GHCZAIHUICZUHUJAJKALMUHAGNORCUINCZUJUKPAQUISCUITULDDEUAUBUISUCUDAUIUEUFUG
    $.
    $( [20-Dec-2014] $)

  $( The set of types is closed under pairing. $)
  typpr $p |- ( ( A e. Type /\ B e. Type ) -> { A , B } e. Type ) $=
    ( ctyp wcel wa cpr com coa co cr1 cfv c0 crnk con0 typwf syl2an typrank cvv
    lim2om wb wne cun csuc cima cuni wceq rankprb word wlim ovex limelon onordi
    mp2an ordunel mp3an1 limsuc ax-mp sylib eqeltrd a1i rankr1ag syl2anc mpbird
    prwf prnzg adantr eltyp sylanbrc ) ACDZBCDZEZABFZGGHIZJKDZVLLUAZVLCDVKVNVLM
    KZVMDZVKVPAMKZBMKZUBZUCZVMVIAJNUDUEZDZBWBDZVPWAUFVJAOZBOZABUGPVKVTVMDZWAVMD
    ZVIVRVMDZVSVMDZWGVJAQBQVMUHWIWJWGVMVMRDVMUIZVMNDZGGHUJSVMRUKUMZULVMVRVSUNUO
    PWKWGWHTSVMVTUPUQURUSVKVLWBDZWLVNVQTVIWCWDWNVJWEWFABVDPWLVKWMUTVLVMVAVBVCVI
    VOVJABCVEVFVLVGVH $.
    $( [20-Dec-2014] $)

  $( The set of types is closed under singleton. $)
  typsn $p |- ( A e. Type -> { A } e. Type ) $=
    ( ctyp wcel csn cpr dfsn2 typpr anidms syl5eqel ) ABCZADAAEZBAFJKBCAAGHI $.
    $( [20-Dec-2014] $)

  $( The set of types is closed under ordered pair. $)
  typop $p |- ( ( A e. Type /\ B e. Type ) -> <. A , B >. e. Type ) $=
    ( ctyp wcel wa cop csn cpr df-op typsn adantr typpr syl2anc syl5eqel ) ACDZ
    BCDZEZABFAGZABHZHZCABIQRCDZSCDTCDOUAPAJKABLRSLMN $.
    $( [20-Dec-2014] $)

  $( The set of types is closed under powerset. $)
  typpw $p |- ( A e. Type -> ~P A e. Type ) $=
    ( ctyp wcel cpw com coa co cr1 cfv c0 wne crnk csuc con0 cima syl wb lim2om
    ax-mp cvv cuni wceq typwf rankpwi typrank wlim limsuc sylib eqeltrd limelon
    pwwf ovex mp2an rankr1ag sylancl mpbird 0elpw ne0i a1i eltyp sylanbrc ) ABC
    ZADZEEFGZHICZVCJKZVCBCVBVEVCLIZVDCZVBVGALIZMZVDVBAHNOUAZCZVGVJUBAUCZAUDPVBV
    IVDCZVJVDCZAUEVDUFZVNVOQRVDVIUGSUHUIVBVCVKCZVDNCZVEVHQVBVLVQVMAUKPVDTCVPVRE
    EFULRVDTUJUMVCVDUNUOUPVFVBJVCCVFAUQVCJURSUSVCUTVA $.
    $( [20-Dec-2014] $)

  $( The set of types is hereditary for nonempty elements. $)
  typel $p |- ( ( A e. Type /\ B e. A /\ B =/= (/) ) -> B e. Type ) $=
    ( ctyp wcel c0 wne w3a com coa co cr1 cfv eltyp simplbi wtr wa wi r1tr trel
    ax-mp ancoms sylan 3adant3 simp3 sylanbrc ) ACDZBADZBEFZGBHHIJZKLZDZUHBCDUF
    UGUKUHUFAUJDZUGUKUFULAEFAMNUGULUKUJOUGULPUKQUIRUJBASTUAUBUCUFUGUHUDBMUE $.
    $( [20-Dec-2014] $)

  $( The set of types is closed under nonempty subset. $)
  typss $p |- ( ( A e. Type /\ B C_ A /\ B =/= (/) ) -> B e. Type ) $=
    ( ctyp wss c0 wne w3a cpw typpw 3ad2ant1 elpw2g biimpar 3adant3 simp3 typel
    wcel syl3anc ) ACPZBADZBEFZGAHZCPZBUAPZTBCPRSUBTAIJRSUCTRUCSBACKLMRSTNUABOQ
    $.
    $( [20-Dec-2014] $)

  ${
    $d x y A $.
    $( The set of types is closed under nonempty union. $)
    typuni $p |- ( ( A e. Type /\ U. A =/= (/) ) -> U. A e. Type ) $=
      ( vx vy ctyp wcel cuni wa com coa cr1 cfv crnk cv con0 wceq syl rankon word
      wss wi c0 wne co ciun cima typwf rankuni2b wral rankelb imp mpsyl ralrimiva
      onelss iunss sylibr typrank cab eleq1 mpbiri rexlimivw abssi ssorduni ax-mp
      wrex wb fvex dfiun2 ordeq mpbir cvv wlim lim2om limelon mp2an onordi ordtr2
      ovex syl2anc eqeltrd uniwf rankr1ag sylancl mpbird anim1i eltyp ) ADEZAFZUA
      UBZGWGHHIUCZJKEZWHGWGDEWFWJWHWFWJWGLKZWIEZWFWKBABMZLKZUDZWIWFAJNUEFZEZWKWOO
      AUFZBAUGPWFWOALKZSZWSWIEZWOWIEZWFWNWSSZBAUHWTWFXCBAWSNEWFWMAEZGWNWSEZXCAQWF
      XDXEWFWQXDXETWRWMAUIPUJWSWNUMUKULBAWNWSUNUOAUPWORZWIRWTXAGXBTXFCMZWNOZBAVDZ
      CUQZFZRZXJNSXLXICNXHXGNEZBAXHXMWNNEWMQXGWNNURUSUTVAXJVBVCWOXKOXFXLVEBCAWNWM
      LVFVGWOXKVHVCVIWIWIVJEWIVKWINEZHHIVQVLWIVJVMVNZVOWOWSWIVPVNVRVSWFWGWPEZXNWJ
      WLVEWFWQXPWRAVTPXOWGWIWAWBWCWDWGWEUO $.
      $( [20-Dec-2014] $)
  $}

  $( The set of types is closed under binary union. $)
  typun $p |- ( ( A e. Type /\ B e. Type ) -> ( A u. B ) e. Type ) $=
    ( ctyp wcel wa cpr cuni cun uniprg c0 wne typpr wss ssun1 com coa cr1 eltyp
    co cfv simprbi ssn0 sylancr adantr eqnetrd typuni syl2anc eqeltrrd ) ACDZBC
    DZEZABFZGZABHZCABCCIZUKULCDUMJKUMCDABLUKUMUNJUOUIUNJKZUJUIAUNMAJKZUPABNUIAO
    OPSQTDUQARUAAUNUBUCUDUEULUFUGUH $.
    $( [20-Dec-2014] $)

  $( The set of types is closed under cartesian product. $)
  typxp $p |- ( ( A e. Type /\ B e. Type ) -> ( A X. B ) e. Type ) $=
    ( ctyp wcel wa cun cpw cxp wss c0 wne typun typpw 3syl xpsspw a1i com eltyp
    coa simprbi co cr1 cfv anim12i xpnz sylib typss syl3anc ) ACDZBCDZEZABFZGZG
    ZCDZABHZUNIZUPJKZUPCDUKULCDUMCDUOABLULMUMMNUQUKABOPUKAJKZBJKZEURUIUSUJUTUIA
    QQSUAUBUCZDUSARTUJBVADUTBRTUDABUEUFUNUPUGUH $.
    $( [20-Dec-2014] $)

  $( The set of types is closed under mapping operation. $)
  typmap $p |- ( ( A e. Type /\ B e. Type ) -> ( A ^m B ) e. Type ) $=
    ( ctyp wcel wa cxp cpw cmap co wss wne typxp syl cid cfv fvi com wceq fvex
    c0 ancoms typpw mapsspw adantl oveqan12d coa cr1 eltyp simprbi eqnetrd map0
    adantr simplbi necon3i eqnetrrd typss syl3anc ) ACDZBCDZEZBAFZGZCDZABHIZVBJ
    ZVDTKVDCDUTVACDZVCUSURVFBALUAVAUBMUSVEURABCUCUDUTANOZBNOZHIZVDTURUSVGAVHBHA
    CPZBCPUEUTVGTKZVITKURVKUSURVGATVJURAQQUFIUGODATKAUHUIUJULVITVGTVITRVGTRVHTK
    VGVHANSBNSUKUMUNMUOVBVDUPUQ $.
    $( [20-Dec-2014] $)

  ${
    holht.1 $e |- ( ph -> A e. Type ) $.
    holht.2 $e |- ( ph -> B e. Type ) $.
    $( The set of types is closed under mapping operation. $)
    holht $p |- ( ph -> ( B ^m A ) e. Type ) $=
      ( ctyp wcel cmap co typmap syl2anc ) ACFGBFGCBHIFGEDCBJK $.
      $( [20-Dec-2014] $)
  $}

  $( The boolean type is a type. $)
  holhb $p |- ( ph -> 2o e. Type ) $=
    ( c2o com coa co cr1 cfv wcel wne ctyp crnk con0 wceq 2on lim2om sselii cvv
    c0 mp2an c1o rankonid mpbi wlim wss limomss ax-mp 2onn eqeltri cima cuni wb
    onwf ovex limelon rankr1ag mpbir a1i holwtru ne0i syl eltyp sylanbrc ) ABCC
    DEZFGHZBRIZBJHVDAVDBKGZVCHZVFBVCBLHVFBMNBUAUBCVCBVCUCZCVCUDOVCUEUFUGPUHBFLU
    IUJZHVCLHZVDVGUKLVIBULNPVCQHVHVJCCDUMOVCQUNSBVCUOSUPUQATBHVEAURBTUSUTBVAVB
    $.
    $( [20-Dec-2014] $)

  ${
    holwc.1 $e |- ( ph -> A e. Type ) $.
    holwc.2 $e |- ( ph -> B e. Type ) $.
    holwc.3 $e |- ( ph -> F e. ( B ^m A ) ) $.
    $( A HOL function is a function. $)
    holf $p |- ( ph -> F : A --> B ) $=
      ( cmap co wcel wf ctyp wb elmapg syl2anc mpbid ) ADCBHIJZBCDKZGACLJBLJQRM
      FECBDLLNOP $.
      $( [20-Dec-2014] $)

    holwc.4 $e |- ( ph -> X e. A ) $.
    $( The type of a function application. $)
    holwc $p |- ( ph -> ( F ` X ) e. B ) $=
      ( wf wcel cfv holf ffvelrn syl2anc ) ABCDJEBKEDLCKABCDFGHMIBCEDNO $.
      $( [20-Dec-2014] $)
  $}

  ${
    $d x A $.  $d x B $.  $d x ph $.  $d x ps $.
    holwl.1 $e |- ( ph -> A e. Type ) $.
    holwl.2 $e |- ( ph -> B e. Type ) $.
    ${
      holwl.3 $e |- ( ( ph /\ x e. A ) -> X e. B ) $.
      $( The type of a mapping operator. $)
      holwl $p |- ( ph -> ( x e. A |-> X ) e. ( B ^m A ) ) $=
        ( cmpt cmap co wcel wf eqid fmptd ctyp wb elmapg syl2anc mpbird ) ABCEI
        ZDCJKLZCDUAMZABCEDUAHUANOADPLCPLUBUCQGFDCUAPPRST $.
        $( [20-Dec-2014] $)
    $}

    holwl2.3 $e |- ( ( ph /\ ( ps /\ x e. A ) ) -> X e. B ) $.
    $( The type of a mapping operator. $)
    holwl2 $p |- ( ( ph /\ ps ) -> ( x e. A |-> X ) e. ( B ^m A ) ) $=
      ( wa ctyp wcel adantr cv anassrs holwl ) ABJCDEFADKLBGMAEKLBHMABCNDLFELIO
      P $.
      $( [20-Dec-2014] $)
  $}

  ${
    $d x ph $.  $d x ps $.
    holleq.1 $e |- ( ( ( ph /\ x e. A ) /\ ps ) -> B = C ) $.
    $( Equality theorem for mapping operator. $)
    holleq $p |- ( ( ph /\ ps ) -> ( x e. A |-> B ) = ( x e. A |-> C ) ) $=
      ( wa cv wcel wceq an32s mpteq2dva ) ABHCDEFACIDJBEFKGLM $.
      $( [20-Dec-2014] $)
  $}

  ${
    $d x ph $.  $d x ps $.  $d x ch $.
    holleq2.1 $e |- ( ( ( ph /\ ( ps /\ x e. A ) ) /\ ch ) -> B = C ) $.
    $( Equality theorem for mapping operator. $)
    holleq2 $p |- ( ( ( ph /\ ps ) /\ ch ) ->
      ( x e. A |-> B ) = ( x e. A |-> C ) ) $=
      ( wa cv wcel wceq anass sylanb holleq ) ABIZCDEFGPDJEKZIABQIICFGLABQMHNO
      $.
      $( [20-Dec-2014] $)
  $}

  ${
    $d x y A $.  $d x y ph $.
    holweq.1 $e |- ( ph -> A e. Type ) $.
    $( The type of the equality function. $)
    holweq $p |- ( ph -> =h A e. ( ( 2o ^m A ) ^m A ) ) $=
      ( vx vy ceqh cv wceq cwt cmpt c2o cmap co df-eqh holhb holht twcld holwl2
      wcel wa holwl syl5eqel ) ABFDBEBDGZEGZHZIZJZJKBLMZBLMDEBNADBUHUGCABKCAOZP
      AUCBSZEBKUFCUIAUJUDBSTTUEQRUAUB $.
      $( [20-Dec-2014] $)
  $}

  ${
    holeqmp.1 $e |- ( ph -> A = B ) $.
    holeqmp.2 $e |- ( ph -> >w A ) $.
    $( Equality-form modus ponens. $)
    holeqmp $p |- ( ph -> >w B ) $=
      ( wtw wceq wb tweq syl mpbid ) ABFZCFZEABCGLMHDBCIJK $.
      $( [20-Dec-2014] $)
  $}

  ${
    holded.1 $e |- ( ph -> A e. 2o ) $.
    holded.2 $e |- ( ph -> B e. 2o ) $.
    ${
      holded.3 $e |- ( ( ph /\ >w B ) -> >w A ) $.
      holded.4 $e |- ( ( ph /\ >w A ) -> >w B ) $.
      $( Equality-form modus ponens. $)
      holded $p |- ( ( ph /\ T. ) -> A = B ) $=
        ( wceq wtru wtw cwt wb impbida wteq syl c2o wcel wttw 3eqtr3d adantr )
        ABCHIABJZKZCJZKZBCAUAUCLUBUDHAUAUCGFMUAUCNOABPQUBBHDBROACPQUDCHECROST
        $.
        $( [20-Dec-2014] $)
    $}

    holded2.3 $e |- ( ( ph /\ ( ps /\ >w B ) ) -> >w A ) $.
    holded2.4 $e |- ( ( ph /\ ( ps /\ >w A ) ) -> >w B ) $.
    $( Equality-form modus ponens. $)
    holded2 $p |- ( ( ph /\ ps ) -> A = B ) $=
      ( wa wtru wceq tru c2o wcel adantr wtw anassrs holded mpan2 ) ABIZJCDKLTC
      DACMNBEOADMNBFOABDPZCPZGQABUBUAHQRS $.
      $( [20-Dec-2014] $)
  $}

  ${
    $d x A $.
    holbeta.1 $e |- ( ph -> B e. V ) $.
    holbeta.2 $e |- ( ph -> x e. A ) $.
    $( Beta conversion (function application). $)
    holbeta $p |- ( ( ph /\ ps ) -> ( ( x e. A |-> B ) ` x ) = B ) $=
      ( cv cmpt cfv wceq wcel eqid fvmpt2 syl2anc adantr ) ACIZCDEJZKELZBARDMEF
      MTHGCDEFSSNOPQ $.
      $( [20-Dec-2014] $)
  $}

  ${
    $d x A $.  $d x C $.  $d x D $.
    holbeta2.1 $e |- ( ph -> C e. A ) $.
    holbeta2.2 $e |- ( ph -> D e. V ) $.
    holbeta2.3 $e |- ( x = C -> B = D ) $.
    $( Beta conversion (function application). $)
    holbeta2 $p |- ( ( ph /\ ps ) -> ( ( x e. A |-> B ) ` C ) = D ) $=
      ( cmpt cfv wceq wcel eqid fvmptg syl2anc adantr ) AFCDELZMGNZBAFDOGHOUAIJ
      CFEGDHTKTPQRS $.
      $( [20-Dec-2014] $)
  $}
