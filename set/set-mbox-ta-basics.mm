$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Propositional Calculus - misc additions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Set up a new wff var $)
  $v nu $.  $( Greek nu $)

  $( Let variable ` nu ` be a wff. $)
  wnu $f wff nu $.

  ${
    ad11antr.1 $e |- ( ph -> ps ) $.
    $( Deduction adding 11 conjuncts to antecedent.  (Contributed by Thierry
       Arnoux, 27-Sep-2025.)  (New usage is discouraged.) $)
    ad11antr $p |- ( ( ( ( ( ( ( ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et )
       /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) /\ nu ) -> ps ) $=
      ( wa adantr ad10antr ) ACOBDEFGHIJKLMABCNPQ $.
  $}

  ${
    $( Simplification of a conjunction.  (Contributed by Thierry Arnoux,
       5-Oct-2025.)  (New usage is discouraged.) $)
    simp-12l $p |- ( ( ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
       /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) /\ nu ) -> ph )
       $=
      ( wa simpl ad11antr ) ABNACDEFGHIJKLMABOP $.
  $}

  ${
    $( Simplification of a conjunction.  (Contributed by Thierry Arnoux,
       5-Oct-2025.)  (New usage is discouraged.) $)
    simp-12r $p |- ( ( ( ( ( ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta )
       /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) /\ ka ) /\ nu ) -> ps )
       $=
      ( wa simpr ad11antr ) ABNBCDEFGHIJKLMABOP $.
  $}

  ${
    an52ds.1 $e |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) -> et ) $.
    $( Inference exchanging the last antecedent with the second.  (Contributed
       by Thierry Arnoux, 3-Jun-2025.) $)
    an52ds $p |- ( ( ( ( ( ph /\ ta ) /\ ch ) /\ th ) /\ ps ) -> et ) $=
      ( wa an32 anbi1i an42ds sylanbr ) AEHZBDCFMBHZDHABHZEHZDHCFPNDABEIJOCDEFG
      KLK $.
  $}

  ${
    an62ds.1 $e |- ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) -> ze
       ) $.
    $( Inference exchanging the last antecedent with the second one.
       (Contributed by Thierry Arnoux, 3-Jun-2025.) $)
    an62ds $p |- ( ( ( ( ( ( ph /\ et ) /\ ch ) /\ th ) /\ ta ) /\ ps ) -> ze )
       $=
      ( wa an32 anbi1i an52ds sylanbr ) AFIZBDECGNBIZDIZEIABIZFIZDIZEICGSPERODA
      BFJKKQCDEFGHLML $.
  $}

  ${
    an72ds.1 $e |- ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\
       ze ) -> si ) $.
    $( Inference exchanging the last antecedent with the second one.
       (Contributed by Thierry Arnoux, 3-Jun-2025.) $)
    an72ds $p |- ( ( ( ( ( ( ( ph /\ ze ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ps
       ) -> si ) $=
      ( wa an32 anbi1i an62ds sylanbr ) AGJZBDEFCHOBJZDJZEJZFJABJZGJZDJZEJZFJCH
      UBRFUAQETPDABGKLLLSCDEFGHIMNM $.
  $}

  ${
    an82ds.1 $e |- ( ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et )
       /\ ze ) /\ si ) -> rh ) $.
    $( Inference exchanging the last antecedent with the second one.
       (Contributed by Thierry Arnoux, 3-Jun-2025.) $)
    an82ds $p |- ( ( ( ( ( ( ( ( ph /\ si ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\
       ze ) /\ ps ) -> rh ) $=
      ( wa an32 anbi1i an72ds sylanbr ) AHKZBDEFGCIPBKZDKZEKZFKZGKABKZHKZDKZEKZ
      FKZGKCIUETGUDSFUCREUBQDABHLMMMMUACDEFGHIJNON $.
  $}

  ${
    syl22anbrc.1 $e |- ( ph -> ps ) $.
    syl22anbrc.2 $e |- ( ph -> ch ) $.
    syl22anbrc.3 $e |- ( ph -> th ) $.
    syl22anbrc.4 $e |- ( ph -> ta ) $.
    syl22anbrc.5 $e |- ( et <-> ( ( ps /\ ch ) /\ ( th /\ ta ) ) ) $.
    $( Syllogism inference.  (Contributed by Thierry Arnoux, 19-Oct-2025.) $)
    syl22anbrc $p |- ( ph -> et ) $=
      ( wa jca syl21anbrc ) ABCDELFGHADEIJMKN $.
  $}

  $( Distributive law for disjunction.  (Contributed by Thierry Arnoux,
     3-Jul-2017.) $)
  or3di $p |- ( ( ph \/ ( ps /\ ch /\ ta ) ) <->
                          ( ( ph \/ ps ) /\ ( ph \/ ch ) /\ ( ph \/ ta ) ) ) $=
    ( w3a wo wa df-3an orbi2i ordi anbi1i 3bitri bitr4i ) ABCDEZFZABFZACFZGZADF
    ZGZPQSEOABCGZDGZFAUAFZSGTNUBABCDHIAUADJUCRSABCJKLPQSHM $.

  $( Distributive law for disjunction.  (Contributed by Thierry Arnoux,
     3-Jul-2017.) $)
  or3dir $p |- ( ( ( ph /\ ps /\ ch ) \/ ta ) <->
              ( ( ph \/ ta ) /\ ( ps \/ ta ) /\ ( ch \/ ta ) ) ) $=
    ( w3a wo or3di orcom 3anbi123i 3bitr3i ) DABCEZFDAFZDBFZDCFZEKDFADFZBDFZCDF
    ZEDABCGDKHLOMPNQDAHDBHDCHIJ $.

  ${
    3o1cs.1 $e |- ( ( ph \/ ps \/ ch ) -> th ) $.
    $( Deduction eliminating disjunct.  (Contributed by Thierry Arnoux,
       19-Dec-2016.) $)
    3o1cs $p |- ( ph -> th ) $=
      ( wo w3o df-3or sylbir orcs ) ABDABFZCDKCFABCGDABCHEIJJ $.

    $( Deduction eliminating disjunct.  (Contributed by Thierry Arnoux,
       19-Dec-2016.) $)
    3o2cs $p |- ( ps -> th ) $=
      ( wo w3o df-3or sylbir orcs olcs ) ABDABFZCDLCFABCGDABCHEIJK $.

    $( Deduction eliminating disjunct.  (Contributed by Thierry Arnoux,
       19-Dec-2016.) $)
    3o3cs $p |- ( ch -> th ) $=
      ( wo w3o df-3or sylbir olcs ) ABFZCDKCFABCGDABCHEIJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Predicate Calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Predicate Calculus - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x y $.  $d B x y $.
    sbc2iedf.1 $e |- F/ x ph $.
    sbc2iedf.2 $e |- F/ y ph $.
    sbc2iedf.3 $e |- F/ x ch $.
    sbc2iedf.4 $e |- F/ y ch $.
    sbc2iedf.5 $e |- ( ph -> A e. V ) $.
    sbc2iedf.6 $e |- ( ph -> B e. W ) $.
    sbc2iedf.7 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ps <-> ch ) ) $.
    $( Conversion of implicit substitution to explicit class substitution.
       (Contributed by Thierry Arnoux, 4-Jul-2023.) $)
    sbc2iedf $p |- ( ph -> ( [. A / x ]. [. B / y ]. ps <-> ch ) ) $=
      ( cv wceq wnf a1i wsbc wa wcel adantr wb anassrs nfv nfan sbciedf ) ABEGU
      ACDFHNADQFRZUBZBCEGIAGIUCUJOUDAUJEQGRBCUEPUFAUJEKUJEUGUHCESUKMTUIJCDSALTU
      I $.

    $d V x $.  $d W x y $.
    rspc2daf.8 $e |- ( ph -> A. x e. V A. y e. W ps ) $.
    $( Double restricted specialization, using implicit substitution.
       (Contributed by Thierry Arnoux, 4-Jul-2023.) $)
    rspc2daf $p |- ( ph -> ch ) $=
      ( wsbc wral nfsbc1v nfcv nfralw cv wceq wa nfv nfan sbceq1a adantl ralbid
      wb rspcdf mpd sbc2iedf sbccom bitr3di mpbird ) ACBDFRZEGRZAUREISZUSABEISZ
      DHSUTQAVAUTDFHJURDEIDIUABDFTUBNADUCFUDZUEBUREIAVBEKVBEUFUGVBBURUKABDFUHUI
      UJULUMAURUSEGIKUREGTOEUCGUDURUSUKAUREGUHUIULUMABEGRDFRCUSABCDEFGHIJKLMNOP
      UNBDEFGUOUPUQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Restricted quantification - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y $.
    ralcom4f.1 $e |- F/_ y A $.
    $( Commutation of restricted and unrestricted universal quantifiers.
       (Contributed by NM, 26-Mar-2004.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.)  (Revised by Thierry Arnoux, 8-Mar-2017.) $)
    ralcom4f $p |- ( A. x e. A A. y ph <-> A. y A. x e. A ph ) $=
      ( cvv wral wal nfcv ralcomf ralv ralbii 3bitr3i ) ACFGZBDGABDGZCFGACHZBDG
      OCHABCDFEBFIJNPBDACKLOCKM $.

    $( Commutation of restricted and unrestricted existential quantifiers.
       (Contributed by NM, 12-Apr-2004.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.)  (Revised by Thierry Arnoux, 8-Mar-2017.) $)
    rexcom4f $p |- ( E. x e. A E. y ph <-> E. y E. x e. A ph ) $=
      ( cvv wrex wex nfcv rexcomf rexv rexbii 3bitr3i ) ACFGZBDGABDGZCFGACHZBDG
      OCHABCDFEBFIJNPBDACKLOCKM $.
  $}

  ${
    19.9d2rf.0 $e |- F/ y ph $.
    19.9d2rf.1 $e |- ( ph -> F/ x ps ) $.
    19.9d2rf.2 $e |- ( ph -> F/ y ps ) $.
    19.9d2rf.3 $e |- ( ph -> E. x e. A E. y e. B ps ) $.
    $( A deduction version of one direction of ~ 19.9 with two variables.
       (Contributed by Thierry Arnoux, 20-Mar-2017.) $)
    19.9d2rf $p |- ( ph -> ps ) $=
      ( wex wrex rexex eximi 3syl nfexd 19.9d mpd ) ABDKZBASCKZSABDFLZCELUACKTJ
      UACEMUASCBDFMNOSACABCDGHPQRBADIQR $.
  $}

  ${
    $d y ph $.
    19.9d2r.1 $e |- ( ph -> F/ x ps ) $.
    19.9d2r.2 $e |- ( ph -> F/ y ps ) $.
    19.9d2r.3 $e |- ( ph -> E. x e. A E. y e. B ps ) $.
    $( A deduction version of one direction of ~ 19.9 with two variables.
       (Contributed by Thierry Arnoux, 30-Jan-2017.) $)
    19.9d2r $p |- ( ph -> ps ) $=
      ( nfv 19.9d2rf ) ABCDEFADJGHIK $.
  $}

  ${
    $d A y $.  $d ph x y $.  $d ch x y $.
    r19.29ffa.3 $e |- ( ( ( ( ph /\ x e. A ) /\ y e. B ) /\ ps ) -> ch ) $.
    $( A commonly used pattern based on ~ r19.29 , version with two restricted
       quantifiers.  (Contributed by Thierry Arnoux, 26-Nov-2017.) $)
    r19.29ffa $p |- ( ( ph /\ E. x e. A E. y e. B ps ) -> ch ) $=
      ( wrex wa wi wral cv wcel ex ralrimiva adantr simpr r19.29d2r rexlimivw
      pm3.35 ancoms syl ) ABEGIDFIZJZBCKZBJZEGIZDFICUEUFBDEFGAUFEGLZDFLUDAUIDFA
      DMFNJZUFEGUJEMGNJBCHOPPQAUDRSUHCDFUGCEGBUFCBCUAUBTTUC $.
  $}

  ${
    $d A x $.  $d B x $.  $d ph x $.
    reu6d.1 $e |- ( ph -> B e. A ) $.
    reu6d.2 $e |- ( ( ph /\ x e. A ) -> ( ps <-> x = B ) ) $.
    $( A condition which implies existential uniqueness.  (Contributed by
       Thierry Arnoux, 13-Oct-2025.) $)
    reu6dv $p |- ( ph -> E! x e. A ps ) $=
      ( wcel cv wceq wb wral wreu ralrimiva reu6i syl2anc ) AEDHBCIEJKZCDLBCDMF
      AQCDGNBCDEOP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Equality
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( A transposition of equality.  (Contributed by Thierry Arnoux,
     20-Aug-2023.) $)
  eqtrb $p |- ( ( A = B /\ A = C ) <-> ( A = B /\ B = C ) ) $=
    ( wceq wa simpl eqtr2 jca eqtr impbii ) ABDZACDZEZKBCDZEZMKNKLFABCGHOKLKNFA
    BCIHJ $.

  ${
    $d A x $.  $d B x $.  $d C x $.  $d ph x $.
    eqelbid.1 $e |- ( ph -> B e. A ) $.
    eqelbid.2 $e |- ( ph -> C e. A ) $.
    $( A variable elimination law for equality within a given set ` A ` .  See
       ~ equvel .  (Contributed by Thierry Arnoux, 20-Feb-2025.) $)
    eqelbid $p |- ( ph -> ( A. x e. A ( x = B <-> x = C ) <-> B = C ) ) $=
      ( cv wceq wb wral wa eqeq1 bibi12d eqid tbt bicom bitri bitr4di wcel
      simpr adantr rspcdva simplr eqeq2d ralrimiva impbida ) ABHZDIZUHEIZJZBCKZ
      DEIZAULLUKUMBCDUIUKDDIZUMJZUMUIUIUNUJUMUHDDMUHDEMNUMUMUNJUOUNUMDOPUMUNQRS
      AULUAADCTULFUBUCAUMLZUKBCUPUHCTZLDEUHAUMUQUDUEUFUG $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Double restricted existential uniqueness quantification
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d a b p $.  $d a b ph $.  $d b x $.
    opsbc2ie.a $e |- ( p = <. a , b >. -> ( ph <-> ch ) ) $.
    $( Conversion of implicit substitution to explicit class substitution for
       ordered pairs.  (Contributed by Thierry Arnoux, 4-Jul-2023.) $)
    opsbc2ie $p |- ( p = <. x , y >. -> ( ph <-> [. y / b ]. [. x / a ]. ch ) )
       $=
      ( cv cop wceq wsbc wb wi cvv wcel sbcth sbcim1 csb bitrd csbopg csbconstg
      syl sbceq2g csbvarg opeq12d eqtrd eqeq2d sbcbig sbcg bibi1d 3imtr3d elv )
      EIZCIZDIZJZKZABFUOLZGUPLZMZNDUPOPZUNUOGIZJZKZGUPLZAUSMZGUPLZURVAVBVEVGNZG
      UPLVFVHNVIGUPOVICUOOPZUNFIZVCJZKZFUOLZABMZFUOLZVEVGVJVMVONZFUOLVNVPNVQFUO
      OHQVMVOFUORUCVJVNUNFUOVLSZKVEFUOUNVLOUDVJVRVDUNVJVRFUOVKSZFUOVCSZJVDFUOVK
      VCOUAVJVSUOVTVCFUOOUEFUOVCOUBUFUGUHTVJVPAFUOLZUSMVGABFUOOUIVJWAAUSAFUOOUJ
      UKTULUMQVEVGGUPRUCVBVFUNGUPVDSZKURGUPUNVDOUDVBWBUQUNVBWBGUPUOSZGUPVCSZJUQ
      GUPUOVCOUAVBWCUOWDUPGUPUOOUBGUPOUEUFUGUHTVBVHAGUPLZUTMVAAUSGUPOUIVBWEAUTA
      GUPOUJUKTULUM $.

    $d A a b p x y $.  $d B a b p x y $.  $d a b ch p x y $.  $d ph x y $.
    $( Correspondence between uniqueness of ordered pairs and double restricted
       existential uniqueness quantification.  Alternate proof of one direction
       only, use ~ opreu2reurex instead.  (Contributed by Thierry Arnoux,
       4-Jul-2023.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    opreu2reuALT $p |- ( ( E! a e. A E. b e. B ch /\ E! b e. B E. a e. A ch )
       -> E! p e. ( A X. B ) ph ) $=
      ( vx vy wrex wreu wa cv wceq wi wral wcel nfv nfan cxp 2reu4 cop wsbc w3a
      simpllr simplr opelxpi syl2anc nfre1 nfra1 nfcv nfsbc1v nfsbc nfrexw rspa
      nfral ad5ant23 simpr imp syl21anc simprd simpld biimpa adantllr r19.29af2
      sbceq1a simplll c1st cfv c2nd 1st2nd2 ad2antlr xp1st xp2nd wb eqcom eqopi
      syl bicomd ancoms ex syl2anbr impcom ad4ant24 simpl eqeq1d anbi12d adantl
      imbi12d rspc2daf com12 anabsi7 opeq12d eqtrd ralrimiva opsbc2ie r19.29ffa
      3jca eqreu sylbi ) BGDKZFCLBFCKGDLMXBFCKZBFNZINZOZGNZJNZOZMZPZGDQZFCQZJDK
      ICKMAECDUAZLZBFGIJCDUBXCXMXOIJCDXCXECRZMZXHDRZMZXMMZXEXHUCZXNRZBFXEUDZGXH
      UDZAENZYAOZPZEXNQZUEXOXTYBYDYHXTXPXRYBXCXPXRXMUFXQXRXMUGXEXHCDUHUIXTXBYDF
      CXSXMFXQXRFXCXPFXBFCUJXPFSTXRFSTXLFCUKTZYCFGXHFXHULBFXEUMUNXTXDCRZMZXBMBY
      DGDYKXBGXTYJGXSXMGXQXRGXCXPGXBGFCGCULZBGDUJZUOXPGSTXRGSTXLGFCYLXKGDUKUQTZ
      YJGSTYMTYCGXHUMYKXGDRZBYDXBYKYOMZBMZXIYCYDYQXFXIYQXLYOBXJXMYJXLXSYOBXLFCU
      PURYKYOBUGYPBUSZXLYOMBXJXKGDUPUTVAZVBYQXFBYCYQXFXIYSVCYRXFBYCBFXEVGVDUIXI
      YCYDYCGXHVGVDUIVEYKXBUSVFXCXPXRXMVHVFXTYGEXNXTYEXNRZMZAYFUUAAMZYEYEVIVJZY
      EVKVJZUCZYAYTYEUUEOXTAYECDVLVMUUBUUCXEUUDXHUUBUUCXEOZUUDXHOZUUAAUUFUUGMZU
      UBAUUHUUBXKAUUHPZFGUUCUUDCDUUAAFXTYTFYIYTFSTAFSTUUAAGXTYTGYNYTGSTAGSTUUIF
      SUUIGSYTUUCCRXTAYECDVNVMYTUUDDRXTAYECDVOVMUUBXDUUCOZXGUUDOZMZMBAXJUUHYTUU
      LBAVPZXTAUULYTUUMUUJUUCXDOZUUDXGOZYTUUMPUUKUUCXDVQUUDXGVQUUNUUOMZYTUUMYTU
      UPUUMYTUUPMZABUUQYEXDXGUCOABVPYEXDXGCDVRHVSVTWAWBWCWDWEUULXJUUHVPUUBUULXF
      UUFXIUUGUULXDUUCXEUUJUUKWFWGUULXGUUDXHUUJUUKUSWGWHWIWJXSXMYTAUFWKWLWMZVCU
      UBUUFUUGUURVBWNWOWBWPWSAYDEXNYAABIJEFGHWQWTVSWRXA $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Double restricted existential uniqueness quantification syntax
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Syntax for double restricted existential uniqueness quantification. $)
  w2reu $a wff E! x e. A , y e. B ph $.

  $( Define the double restricted existential uniqueness quantifier.
     (Contributed by Thierry Arnoux, 4-Jul-2023.) $)
  df-2reu $a |- ( E! x e. A , y e. B ph
    <-> ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) ) $.

  $( Double restricted existential uniqueness commutes.  (Contributed by
     Thierry Arnoux, 4-Jul-2023.) $)
  2reucom $p |- ( E! x e. A , y e. B ph <-> E! y e. B , x e. A ph ) $=
    ( wrex wreu wa w2reu ancom df-2reu 3bitr4i ) ACEFBDGZABDFCEGZHNMHABCDEIACBE
    DIMNJABCDEKACBEDKL $.

  $( Double restricted existential uniqueness implies double restricted
     existence.  (Contributed by Thierry Arnoux, 4-Jul-2023.) $)
  2reu2rex1 $p |- ( E! x e. A , y e. B ph -> E. x e. A E. y e. B ph ) $=
    ( w2reu wrex wreu df-2reu simplbi reurex syl ) ABCDEFZACEGZBDHZNBDGMOABDGCE
    HABCDEIJNBDKL $.

  $( Double restricted existential uniqueness implies restricted existential
     uniqueness with restricted existence.  (Contributed by AV, 5-Jul-2023.) $)
  2reureurex $p |- ( E! x e. A , y e. B ph -> E! x e. A E. y e. B ph ) $=
    ( w2reu wrex wreu df-2reu simplbi ) ABCDEFACEGBDHABDGCEHABCDEIJ $.

  ${
    $d A y $.  $d B x $.  $d x y $.
    $( Double restricted existential uniqueness implies two nested restricted
       existential uniqueness.  (Contributed by AV, 5-Jul-2023.) $)
    2reu2reu2 $p |- ( E! x e. A , y e. B ph -> E! x e. A E! y e. B ph ) $=
      ( w2reu wrex wreu wa df-2reu 2rexreu sylbi ) ABCDEFACEGBDHABDGCEHIACEHBDH
      ABCDEJABCDEKL $.
  $}

  ${
    $d A p x y $.  $d B p x y $.  $d ch x y $.  $d p ph x y $.
    opreu2reu1.a $e |- ( p = <. x , y >. -> ( ch <-> ph ) ) $.
    $( Equivalent definition of the double restricted existential uniqueness
       quantifier, using uniqueness of ordered pairs.  (Contributed by Thierry
       Arnoux, 4-Jul-2023.) $)
    opreu2reu1 $p |- ( E! x e. A , y e. B ph <-> E! p e. ( A X. B ) ch ) $=
      ( w2reu wrex wreu wa cxp df-2reu opreu2reurex bitr4i ) ACDEFIADFJCEKACEJD
      FKLBGEFMKACDEFNBAEFGCDHOP $.
  $}

  ${
    $d P a b $.
    $( There exists a unique decomposition of a prime as a sum of squares of
       two different positive integers iff the prime is of the form
       ` 4 k + 1 ` .  Double restricted existential uniqueness variant of
       ~ 2sqreunnltb .  (Contributed by AV, 5-Jul-2023.) $)
    sq2reunnltb $p |- ( P e. Prime -> ( ( P mod 4 ) = 1
                                        <-> E! a e. NN , b e. NN
                              ( a < b /\ ( ( a ^ 2 ) + ( b ^ 2 ) ) = P ) ) ) $=
      ( cprime wcel c4 cmo co c1 wceq cv clt wbr c2 cexp caddc wa cn wrex wreu
      w2reu biid 2sqreunnltb df-2reu bitr4di ) ADEAFGHIJBKZCKZLMUFNOHUGNOHPHAJQ
      ZCRSBRTUHBRSCRTQUHBCRRUAUHABCUHUBUCUHBCRRUDUE $.
  $}

  ${
    $d C a b $.
    $( For each complex number ` C ` , there does not uniquely exist two
       complex numbers ` a ` and ` b ` , with ` b ` squared and added to ` a `
       resulting in the given complex number ` C ` .  Double restricted
       existential uniqueness variant of ~ addsqn2reurex2 .  (Contributed by
       AV, 5-Jul-2023.) $)
    addsqnot2reu $p |- ( C e. CC -> -. E! a e. CC , b e. CC
                                       ( a + ( b ^ 2 ) ) = C ) $=
      ( cc wcel cv c2 cexp co caddc wceq wrex wreu w2reu addsqn2reurex2 df-2reu
      wa sylnibr ) ADEBFCFGHIJIAKZCDLBDMSBDLCDMQSBCDDNABCOSBCDDPR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Substitution (without distinct variables) - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    sbceqbidf.1 $e |- F/ x ph $.
    sbceqbidf.2 $e |- ( ph -> A = B ) $.
    sbceqbidf.3 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equality theorem for class substitution.  (Contributed by Thierry
       Arnoux, 4-Sep-2018.) $)
    sbceqbidf $p |- ( ph -> ( [. A / x ]. ps <-> [. B / x ]. ch ) ) $=
      ( cab wcel wsbc abbid eleq12d df-sbc 3bitr4g ) AEBDJZKFCDJZKBDELCDFLAEFQR
      HABCDGIMNBDEOCDFOP $.
  $}

  ${
    $d a w $.  $d a E $.  $d a W $.  $d a ph $.
    sbcies.a $e |- A = ( E ` W ) $.
    sbcies.1 $e |- ( a = A -> ( ph <-> ps ) ) $.
    $( A special version of class substitution commonly used for structures.
       (Contributed by Thierry Arnoux, 14-Mar-2019.) $)
    sbcies $p |- ( w = W -> ( [. ( E ` w ) / a ]. ps <-> ph ) ) $=
      ( cv wceq cfv cvv fvexd wa wb simpr fveq2 eqtr4id adantr eqtr4d bicomd
      syl sbcied ) CJZFKZBAGUEELZMUFUEENUFGJZUGKZOZABUJUHDKABPUJUHUGDUFUIQUFDUG
      KUIUFDFELUGHUEFERSTUAIUCUBUD $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Existential "at most one" - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d i j x $.
    mo5f.1 $e |- F/ i ph $.
    mo5f.2 $e |- F/ j ph $.
    $( Alternate definition of "at most one."  (Contributed by Thierry Arnoux,
       1-Mar-2017.) $)
    mo5f $p |- ( E* x ph <->
                   A. i A. j ( ( [ i / x ] ph /\ [ j / x ] ph ) -> i = j ) ) $=
      ( wmo wsb wa weq wi wal mo3 nfsbv nfan nfv nfim nfal sb8f sbim sban nfs1v
      sbf bicomi anbi2i bitr4i equsb3 imbi12i bitri sbalv albii 3bitri ) ABGAAB
      DHZIZBDJZKZDLZBLUQBCHZCLABCHZUMIZCDJZKZDLZCLABDFMUQBCUPCDUNUOCAUMCEABDCEN
      OUOCPQRSURVCCUPVBBCDUPBCHUNBCHZUOBCHZKVBUNUOBCTVDUTVEVAVDUSUMBCHZIUTAUMBC
      UAUMVFUSVFUMUMBCABDUBUCUDUEUFBCDUGUHUIUJUKUL $.
  $}

  ${
    $d x y $.
    nmo.1 $e |- F/ y ph $.
    $( Negation of "at most one".  (Contributed by Thierry Arnoux,
       26-Feb-2017.) $)
    nmo $p |- ( -. E* x ph <-> A. y E. x ( ph /\ x =/= y ) ) $=
      ( wmo wn weq wi wal wex cv wne wa mof notbii alnex pm4.61 biid necon3bbii
      exnal anbi2i bitri exbii bitr3i albii 3bitr2i ) ABEZFABCGZHZBIZCJZFUJFZCI
      ABKZCKZLZMZBJZCIUGUKABCDNOUJCPULUQCULUIFZBJUQUIBTURUPBURAUHFZMUPAUHQUSUOA
      UHUMUNUHRSUAUBUCUDUEUF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Existential uniqueness - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y ph $.  $d x ps $.  $d x A $.  $d x B $.  $d x y C $.
    reuxfrdf.0 $e |- F/_ y B $.
    reuxfrdf.1 $e |- ( ( ph /\ y e. C ) -> A e. B ) $.
    reuxfrdf.2 $e |- ( ( ph /\ x e. B ) -> E* y e. C x = A ) $.
    $( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  Cf. ~ reuxfrd
       (Contributed by Thierry Arnoux, 7-Apr-2017.)  (Revised by Thierry
       Arnoux, 8-Oct-2017.)  (Revised by Thierry Arnoux, 30-Mar-2018.) $)
    reuxfrdf $p |- ( ph
        -> ( E! x e. B E. y e. C ( x = A /\ ps ) <-> E! y e. C ps ) ) $=
      ( wa wrex wi ancom wmo wal wex weu bitri eubii cv wceq wreu wrmo wral syl
      wcel rmoan rmobii sylib ralrimiva df-rmo ralbii df-ral nfcri moanim albii
      bitr4i 2euswapv df-reu r19.41 rexbii 3bitr4i df-rex bitr3i an12 exbii nfv
      3imtr4g sylbi moanimv r19.42v moeq moani mobii mpbi mprg impbid1 wb biidd
      a1i ceqsrexv reubidva bitrd ) ACUAZEUBZBKZDGLZCFUCZWGCFLZDGUCZBDGUCAWIWKA
      WGDGUDZCFUEZWIWKMZAWLCFAWEFUGZKZBWFKZDGUDZWLWPWFDGUDWRJWFBDGUHUFWQWGDGBWF
      NUIUJUKWMDUAGUGZWGKZDOZCFUEZWNWLXACFWGDGULUMXBWOWTKZDOZCPZWNXBWOXAMZCPXEX
      ACFUNXDXFCWOWTDDCFHUOZUPUQURXEXCDQZCRZXCCQZDRZWIWKXCCDUSWIWOWHKZCRZXIWHCF
      UTZXLXHCXLWSWOWGKZKZDQZXHXLXODGLZXQWGWOKZDGLWHWOKXRXLWGWODGXGVAXOXSDGWOWG
      NVBWOWHNVCXODGVDVEZXPXCDWSWOWGVFVGSTSWKWSWJKZDRZXKWJDGUTZYAXJDYAWTCFLZXJW
      GWSKZCFLWJWSKYDYAWGWSCFWSCVHVAWTYECFWSWGNVBWSWJNVCWTCFVDZVETSVIVJVJUFXOCO
      ZWKWIMZDGYGDGUEZXPCOZDPZYHYIWSYGMZDPYKYGDGUNYJYLDWSXOCVKUQURYKXPCQZDRZXQC
      RZWKWIXPDCUSWKYBYNYCYAYMDYAXJYMYAYDXJWSWGCFVLYFVEXCXPCWOWSWGVFVGSTSWIXMYO
      XNXLXQCXTTSVIVJYGWSWOBKZWFKZCOYGWFYPCCEVMVNYQXOCYQWFYPKXOYPWFNWFWOBVFSVOV
      PWAVQVRAWJBDGAWSKEFUGWJBVSIBBCEFWFBVTWBUFWCWD $.
  $}

  ${
    $d b x y $.  $d y A $.  $d b B $.  $d x b F $.  $d x b ph $.
    rexunirn.1 $e |- F = ( x e. A |-> B ) $.
    rexunirn.2 $e |- ( x e. A -> B e. V ) $.
    $( Restricted existential quantification over the union of the range of a
       function.  Cf. ~ rexrn and ~ eluni2 .  (Contributed by Thierry Arnoux,
       19-Sep-2017.) $)
    rexunirn $p |- ( E. x e. A E. y e. B ph -> E. y e. U. ran F ph ) $=
      ( vb wrex cv wcel wa wex crn cuni df-rex bitr4i exbii 19.42v anbi2i mpdan
      elrnmpt1 wceq eleq2 anbi1d rspcev sylan r19.41v sylib eximi eluni2 anbi1i
      bitri sylibr exlimiv sylbi ) ACEKZBDKZBLDMZCLZEMZANZNZCOZBOZACFPZQZKZUTVA
      USNZBOVGUSBDRVFVKBVFVAVDCOZNVKVAVDCUAUSVLVAACERUBSTSVFVJBVFVBJLZMZJVHKZAN
      ZCOZVJVEVPCVEVNANZJVHKZVPVAEVHMZVDVSVAEGMVTIBDEFGHUDUCVRVDJEVHVMEUEVNVCAV
      MEVBUFUGUHUIVNAJVHUJUKULVJVBVIMZANZCOVQACVIRWBVPCWAVOAJVBVHUMUNTUOUPUQUR
      $.
  $}

$(
  @{
    @( Restricted existential quantification for ordered pair abstract builders
       moving one condition outside of the abstract builder. @)
    reuopan @p |- ( E! p e. { <. x , y >. | ( ( x e. A /\ y e. B ) /\ ph ) } ps
      <-> E! p e. { <. x , y >. | ( x e. A /\ y e. B ) } ( ph /\ ps ) ) @=
      ? @.

    @( Restricted existential quantification for ordered pair abstract builders
       @)
    reuopab @p |- ( E! p e. { <. x , y >. | ( x e. A /\ y e. B ) } ph
      <-> ( E! x e. A E! y e. B ( p = <. x , y >. /\ ph )
         /\ A. x e. A E* y e. B ( p = <. x , y >. /\ ph ) ) ) @=
      ? @.
  @}
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Restricted "at most one" - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x A $.  $d x y B $.  $d x y C $.  $d x y ph $.  $d y ps $.  $d x ch $.
    rmoxfrd.1 $e |- ( ( ph /\ y e. C ) -> A e. B ) $.
    rmoxfrd.2 $e |- ( ( ph /\ x e. B ) -> E! y e. C x = A ) $.
    rmoxfrd.3 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
    $( Transfer "at most one" restricted quantification from a variable ` x `
       to another variable ` y ` contained in expression ` A ` .  (Contributed
       by Thierry Arnoux, 7-Apr-2017.)  (Revised by Thierry Arnoux,
       8-Oct-2017.) $)
    rmoxfrd $p |- ( ph -> ( E* x e. B ps <-> E* y e. C ch ) ) $=
      ( cv wcel wa wmo wrmo wex weu wrex wreu wi wceq reurex syl rexxfrd df-rex
      3bitr3g reuxfr1d df-reu imbi12d moeu 3bitr4g df-rmo ) ADLZGMZBNZDOZELHMCN
      ZEOZBDGPCEHPAUPDQZUPDRZUAUREQZURERZUAUQUSAUTVBVAVCABDGSCEHSUTVBABCDEFGHIA
      UONUNFUBZEHTVDEHSJVDEHUCUDKUEBDGUFCEHUFUGABDGTCEHTVAVCABCDEFGHIJKUHBDGUIC
      EHUIUGUJUPDUKUREUKULBDGUMCEHUMUL $.
  $}

  $( "At most one" restricted existential quantifier for a union implies the
     same quantifier on both sets.  (Contributed by Thierry Arnoux,
     27-Nov-2023.) $)
  rmoun $p |- ( E* x e. ( A u. B ) ph -> ( E* x e. A ph /\ E* x e. B ph ) )
      $=
    ( cv wcel wa wo wmo cun wrmo mooran2 df-rmo elun anbi1i andir bitri anbi12i
    mobii 3imtr4i ) BEZCFZAGZUADFZAGZHZBIZUCBIZUEBIZGABCDJZKZABCKZABDKZGUCUEBLU
    KUAUJFZAGZBIUGABUJMUOUFBUOUBUDHZAGUFUNUPAUACDNOUBUDAPQSQULUHUMUIABCMABDMRT
    $.

  ${
    $d ph x $.
    rmounid.1 $e |- ( ( ph /\ x e. B ) -> -. ps ) $.
    $( A case where an "at most one" restricted existential quantifier for a
       union is equivalent to such a quantifier for one of the sets.
       (Contributed by Thierry Arnoux, 27-Nov-2023.) $)
    rmounid $p |- ( ph -> ( E* x e. ( A u. B ) ps <-> E* x e. A ps ) ) $=
      ( cv cun wcel wa wmo wrmo wo wn wb ex con2d bitr4di biancomd df-rmo biorf
      imp orcom syl elun pm5.32da bicomd mobidv 3bitr4g ) ACGZDEHZIZBJZCKUJDIZB
      JZCKBCUKLBCDLAUMUOCAUMUNBABUNJZUMAUPULBABUNULABJZUNUNUJEIZMZULUQURNZUNUSO
      ABUTAURBAURBNFPQUBUTUNURUNMUSURUNUAUNURUCRUDUJDEUERUFSUGSUHBCUKTBCDTUI $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Restricted iota (description binder)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d ph x $.
    riotaeqbidva.1 $e |- ( ph -> A = B ) $.
    riotaeqbidva.2 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( Equivalent wff's yield equal restricted definition binders (deduction
       form).  ( ~ raleqbidva analog.)  (Contributed by Thierry Arnoux,
       29-Jan-2025.) $)
    riotaeqbidva $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. B ch ) ) $=
      ( crio riotabidva riotaeqdv eqtrd ) ABDEICDEICDFIABCDEHJACDEFGKL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  General Set Theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Class abstractions (a.k.a. class builders)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x y z $.  $d B x y z $.  $d ph x y $.  $d ps z $.
    dmrab.1 $e |- ( z = <. x , y >. -> ( ph <-> ps ) ) $.
    $( Domain of a restricted class abstraction over a cartesian product.
       (Contributed by Thierry Arnoux, 3-Jul-2023.) $)
    dmrab $p |- dom { z e. ( A X. B ) | ph } = { x e. A | E. y e. B ps } $=
      ( cv cop cxp crab wcel wex cab wrex wa anbi1i ancom 3bitri opelxp r19.41v
      cdm elrab anass anbi2i exbii df-rex 3bitr2i biancomi abbii df-rab 3eqtr4i
      dfdm3 ) CIZDIZJZAEFGKZLZMZDNZCOUOFMZBDGPZQZCOUSUCVCCFLVAVDCVAVBVCVAUPGMZB
      VBQZQZDNVFDGPVCVBQUTVGDUTVEVBQZBQZVEVBBQZQVGUTUQURMZBQVBVEQZBQVIABEUQURHU
      DVKVLBUOUPFGUARVLVHBVBVESRTVEVBBUEVJVFVEVBBSUFTUGVFDGUHBVBDGUBUIUJUKCDUSU
      NVCCFULUM $.
  $}

  $( Difference of two restricted class abstractions.  Compare with ~ difrab .
     (Contributed by Thierry Arnoux, 3-Jan-2022.) $)
  difrab2 $p |- ( { x e. A | ph } \ { x e. B | ph } )
    = { x e. ( A \ B ) | ph } $=
    ( crab cdif nfrab1 nfdif cv wcel wa wn wo eldif anbi1i pm3.24 biorfri anass
    andi rabid ancom 3bitr2i anbi2i 3bitr4i bitr4i ianor xchnxbir anbi12i bitri
    3bitr4ri eqri ) BABCEZABDEZFZABCDFZEZBULUMABCGABDGHABUOGBIZUOJZAKZUQCJZAKZU
    QDJZLZALZMZKZUQUPJUQUNJZUSUTVCKZAKZVFURVHAUQCDNOUTAVEKZKUTVCAKZKVFVIVJVKUTV
    JAVCKZAVDKZMVLVKAVCVDSVMVLAPQAVCUAUBUCUTAVERUTVCARUDUEABUOTVGUQULJZUQUMJZLZ
    KVFUQULUMNVNVAVPVEABCTVBAKVEVOVBAUFABDTUGUHUIUJUK $.

  ${
    rabexgfGS.1 $e |- F/_ x A $.
    $( Separation Scheme in terms of a restricted class abstraction.  To be
       removed in profit of Glauco's equivalent version.  (Contributed by
       Thierry Arnoux, 11-May-2017.) $)
    rabexgfGS $p |- ( A e. V -> { x e. A | ph } e. _V ) $=
      ( wcel crab wss cvv cv wi nfrab1 dfssf rabidim1 mpgbir elex ssexg sylancr
      ) CDFABCGZCHZCIFSIFTBJZSFUACFKBBSCABCLEMABCNOCDPSCIQR $.
  $}

  ${
    $d x A $.  $d x B $.
    rabsnel.1 $e |- B e. _V $.
    $( Truth implied by equality of a restricted class abstraction and a
       singleton.  (Contributed by Thierry Arnoux, 15-Sep-2018.) $)
    rabsnel $p |- ( { x e. A | ph } = { B } -> B e. A ) $=
      ( crab csn wceq wcel snid eleq2 mpbiri elrabi syl ) ABCFZDGZHZDOIZDCIQRDP
      IDEJOPDKLABDCMN $.
  $}

  ${
    $d X x $.  $d Y x $.
    $( Conditions for a restricted class abstraction to be a subset of an
       unordered pair.  (Contributed by Thierry Arnoux, 6-Jul-2025.) $)
    rabsspr $p |- ( { x e. V | ph } C_ { X , Y }
                 <-> A. x e. V ( ph -> ( x = X \/ x = Y ) ) ) $=
      ( crab cpr wss cv wcel wa cab wceq wo wi wal wral df-rab dfpr2 sseq12i
      ss2ab impexp albii df-ral bitr4i 3bitri ) ABCFZDEGZHBIZCJZAKZBLZUIDMUIEMN
      ZBLZHUKUMOZBPZAUMOZBCQZUGULUHUNABCRBDESTUKUMBUAUPUJUQOZBPURUOUSBUJAUMUBUC
      UQBCUDUEUF $.
  $}

  ${
    $d X x $.  $d Y x $.  $d Z x $.
    $( Conditions for a restricted class abstraction to be a subset of an
       unordered triple.  (Contributed by Thierry Arnoux, 6-Jul-2025.) $)
    rabsstp $p |- ( { x e. V | ph } C_ { X , Y , Z }
                 <-> A. x e. V ( ph -> ( x = X \/ x = Y \/ x = Z ) ) ) $=
      ( crab ctp wss cv wcel wa cab wceq w3o wi wal wral df-rab dftp2 sseq12i
      ss2ab impexp albii df-ral bitr4i 3bitri ) ABCGZDEFHZIBJZCKZALZBMZUJDNUJEN
      UJFNOZBMZIULUNPZBQZAUNPZBCRZUHUMUIUOABCSBDEFTUAULUNBUBUQUKURPZBQUSUPUTBUK
      AUNUCUDURBCUEUFUG $.
  $}

  $( Union of three restricted class abstractions.  (Contributed by Thierry
     Arnoux, 6-Jul-2025.) $)
  3unrab $p |- ( ( { x e. A | ph } u. { x e. A | ps } ) u. { x e. A | ch } )
               = { x e. A | ( ph \/ ps \/ ch ) } $=
    ( wo crab cun w3o unrab uneq1i df-3or rabbii 3eqtr4i ) ABFZDEGZCDEGZHOCFZDE
    GADEGBDEGHZQHABCIZDEGOCDEJSPQABDEJKTRDEABCLMN $.

  ${
    $d A g x y z $.  $d B g x y z $.  $d F g x y z $.  $d V g y z $.
    $( From a surjective function, *choose* a subset of the domain, such that
       the restricted function is bijective.  (Contributed by Thierry Arnoux,
       27-Jan-2020.) $)
    foresf1o $p |- ( ( A e. V /\ F : A -onto-> B )
      -> E. x e. ~P A ( F |` x ) : x -1-1-onto-> B ) $=
      ( vg vy vz wcel wa cv wf cfv wrex wceq fveq2d nfv nfan syl2anc eqtrd ccnv
      wfo csn cima wral cres wf1o cpw cvv wex focdmex imp foelrn wfn fofn eqcom
      wi fniniseg biimpar anassrs sylan2br sylanl1 ex reximdva adantr ralrimiva
      mpd adantll eleq1 sylc crn wss frn ad2antrl vex rnex elpw sylibr ad2antlr
      ac6sg fof fssresd dffn3 sylib fvres nfra1 simpr ad5antlr simplrr ad2antrr
      ffn adantl simplr rspa simplbda eqtr3d fvelrnb biimpa r19.29af ffvelcdmda
      sylan syl ad3antlr ralrimi 2fvidf1od reseq2 id f1oeq123d rspcev exlimddv
      eqidd ) BEIZBCDUBZJZCBFKZLZGKZXOMZDUAXQUCUDZIZGCUEZJZAKZCDYCUFZUGZABUHZNZ
      FXNCUIIZHKZXSIZHBNZGCUEYBFUJXLXMYHBCEDUKULXNYKGCXMXQCIZYKXLXMYLJXQYIDMZOZ
      HBNZYKHBCXQDUMXMYOYKUQYLXMYNYJHBXMYIBIZJYNYJXMDBUNZYPYNYJBCDUOZYNYQYPJYMX
      QOZYJYMXQUPYQYPYSYJYQYJYPYSJBXQYIDURUSUTVAVBVCVDVEVGVHVFYJXTGHCBFUIYIXRXS
      VIVTVJXNYBJZXOVKZYFIZUUACDUUAUFZUGZYGYTUUABVLZUUBXPUUEXNYACBXOVMVNZUUABXO
      FVOVPVQVRYTUUACUUCXOHGYTBCUUADXMBCDLXLYBBCDWAVSUUFWBYTXOCUNZCUUAXOLXPUUGX
      NYACBXOWKVNZCXOWCWDZYTYIUUCMZXOMZYIOHUUAYTYIUUAIZJZUUKYMXOMZYIUUMUUJYMXOU
      ULUUJYMOYTYIUUADWEWLPUUMXRYIOZUUNYIOGCYTUULGXNYBGXNGQXPYAGXPGQXTGCWFRRZUU
      LGQRUUMYLJZUUOJZUUNXRYIUURYMXQXOUURXRDMZYMXQUURXRYIDUUQUUOWGZPUURYQXTUUSX
      QOZXMYQXLYBUULYLUUOYRWHUURYAYLXTUUMYAYLUUOXNXPYAUULWIWJUUMYLUUOWMXTGCWNZS
      YQXTXRBIUVABXQXRDURWOZSWPPUUTTYTUUGUULUUOGCNZUUHUUGUULUVDGCYIXOWQWRXAWSTV
      FYTXRUUCMZXQOZGCUUPYTYLUVFYTYLJZUVEUUSXQUVGXRUUAIUVEUUSOYTCUUAXQXOUUIWTXR
      UUADWEXBUVGYQXTUVAXMYQXLYBYLYRXCUVGYAYLXTXNXPYAYLWIYTYLWGUVBSUVCSTVCXDXEY
      EUUDAUUAYFYCUUAOZYCUUACCYDUUCYCUUADXFUVHXGUVHCXKXHXISXJ $.
  $}

  ${
    $d A a x y $.  $d B a x y $.  $d F a x y $.  $d V a x y $.  $d a x y ph $.
    $d a y ps $.  $d a x ch $.
    rabfodom.1 $e |- ( ( ph /\ x e. A /\ y = ( F ` x ) ) -> ( ch <-> ps ) ) $.
    rabfodom.2 $e |- ( ph -> A e. V ) $.
    rabfodom.3 $e |- ( ph -> F : A -onto-> B ) $.
    $( Domination relation for restricted abstract class builders, based on a
       surjective function.  (Contributed by Thierry Arnoux, 27-Jan-2020.) $)
    rabfodom $p |- ( ph -> { y e. B | ch } ~<_ { x e. A | ps } ) $=
      ( va cv cres wf1o crab wbr wcel cvv cdom cpw cen cfv cmpt rabex eqid wceq
      wa vex wfo wf fof syl feqmptd ad2antrr reseq1d wss elpwi ad2antlr resmptd
      eqtrd f1oeq1 biimpa sylancom w3a wb simp1ll 3ad2ant1 simp2 sseldd syl3anc
      f1oresrab f1oeng sylancr ensymd rabexg rabss2 ssdomg sylc endomtr syl2anc
      simp3 wrex foresf1o r19.29a ) AMNZGHWGOZPZCEGQZBDFQZUARZMFUBZAWGWMSZUIZWI
      UIZWJBDWGQZUCRWQWKUARZWLWPWQWJWPWQTSWQWJDWGDNZHUDZUEZWQOZPWQWJUCRBDWGMUJU
      FWPBCDEWGGWTXAXAUGWOWIWHXAUHZWGGXAPZWPWHDFWTUEZWGOXAWPHXEWGAHXEUHWNWIADFG
      HAFGHUKZFGHULLFGHUMUNUOUPUQWPDFWGWTWNWGFURZAWIWGFUSUTZVAVBXCWIXDWGGWHXAVC
      VDVEWPWSWGSZENWTUHZVFZAWSFSXJCBVGAWNWIXIXJVHXKWGFWSWPXIXGXJXHVIWPXIXJVJVK
      WPXIXJWCJVLVMWQWJTXBVNVOVPWPWKTSZWQWKURZWRAXLWNWIAFISZXLKBDFIVQUNUPWPXGXM
      XHBDWGFVRUNWQWKTVSVTWJWQWKWAWBAXNXFWIMWMWDKLMFGHIWEWBWF $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d ph y $.
    rabrexfi.1 $e |- ( ph -> B e. Fin ) $.
    rabrexfi.2 $e |- ( ( ph /\ y e. B ) -> { x e. A | ps } e. Fin ) $.
    $( Conditions for a class abstraction with a restricted existential
       quantification to be finite.  (Contributed by Thierry Arnoux,
       6-Jul-2025.) $)
    rabrexfi $p |- ( ph -> { x e. A | E. y e. B ps } e. Fin ) $=
      ( wrex crab ciun cfn iunrab wcel wral ralrimiva iunfi syl2anc eqeltrrid )
      ABDFICEJDFBCEJZKZLBDCFEMAFLNTLNZDFOUALNGAUBDFHPDFTQRS $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Image Sets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x y $.
    abrexdomjm.1 $e |- ( y e. A -> E* x ph ) $.
    $( An indexed set is dominated by the indexing set.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    abrexdomjm $p |- ( A e. V -> { x | E. y e. A ph } ~<_ A ) $=
      ( wcel wrex cab cv wa copab crn cdom wex df-rex abbii wbr cvv wmo cdm wfn
      rnopab eqtr4i wss dmopabss ssexg mpan funopab wi moanimv mpbir mpgbir a1i
      wfun funfn sylib fnrndomg sylc ssdomg mpi domtr syl2anc eqbrtrid ) DEGZAC
      DHZBIZCJDGZAKZCBLZMZDNVGVICOZBIVKVFVLBACDPQVICBUCUDVEVKVJUAZNRZVMDNRZVKDN
      RVEVMSGZVJVMUBZVNVMDUEZVEVPACBDUFZVMDEUGUHVEVJUOZVQVTVEVTVIBTZCVICBUIWAVH
      ABTUJFVHABUKULUMUNVJUPUQVMSVJURUSVEVRVOVSVMDEUTVAVKVMDVBVCVD $.
  $}

  ${
    $d A x y $.  $d B x $.
    $( An indexed set is dominated by the indexing set.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    abrexdom2jm $p |- ( A e. V -> { x | E. y e. A x = B } ~<_ A ) $=
      ( cv wceq wmo wcel moeq a1i abrexdomjm ) AFDGZABCEMAHBFCIADJKL $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.
    abrexexd.0 $e |- F/_ x A $.
    abrexexd.1 $e |- ( ph -> A e. _V ) $.
    $( Existence of a class abstraction of existentially restricted sets.
       (Contributed by Thierry Arnoux, 10-May-2017.) $)
    abrexexd $p |- ( ph -> { y | E. x e. A y = B } e. _V ) $=
      ( cv wceq wrex cab cmpt crn cvv wcel wa copab wex rnopab df-mpt rneqi cdm
      df-rex abbii 3eqtr4i wfun funmpt crab eqid dmmpt rabexgfGS eqeltrid funex
      sylancr rnexg 3syl eqeltrrid ) ACHEIZBDJZCKZBDELZMZNBHDOURPZBCQZMVCBRZCKV
      BUTVCBCSVAVDBCDETUAUSVECURBDUCUDUEADNOZVANOZVBNOGVFVAUFVAUBZNOVGBDEUGVFVH
      ENOZBDUHNBDEVAVAUIUJVIBDNFUKULNVAUMUNVANUOUPUQ $.
  $}

  ${
    $d x y A $.  $d y B $.  $d y C $.
    elabreximd.1 $e |- F/ x ph $.
    elabreximd.2 $e |- F/ x ch $.
    elabreximd.3 $e |- ( A = B -> ( ch <-> ps ) ) $.
    elabreximd.4 $e |- ( ph -> A e. V ) $.
    elabreximd.5 $e |- ( ( ph /\ x e. C ) -> ps ) $.
    $( Class substitution in an image set.  (Contributed by Thierry Arnoux,
       30-Dec-2016.) $)
    elabreximd $p |- ( ( ph /\ A e. { y | E. x e. C y = B } ) -> ch ) $=
      ( cv wceq wrex cab wcel wa wb eqeq1 rexbidv elabg syl biimpa simpr adantr
      biimpar syl2anc exp31 rexlimd imp syldan ) AFEOZGPZDHQZERSZFGPZDHQZCAURUT
      AFISURUTUAMUQUTEFIUOFPUPUSDHUOFGUBUCUDUEUFAUTCAUSCDHJKADOHSZUSCAVATZUSTUS
      BCVBUSUGVBBUSNUHUSCBLUIUJUKULUMUN $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.  $d x ch $.  $d x ph $.
    elabreximdv.1 $e |- ( A = B -> ( ch <-> ps ) ) $.
    elabreximdv.2 $e |- ( ph -> A e. V ) $.
    elabreximdv.3 $e |- ( ( ph /\ x e. C ) -> ps ) $.
    $( Class substitution in an image set.  (Contributed by Thierry Arnoux,
       30-Dec-2016.) $)
    elabreximdv $p |- ( ( ph /\ A e. { y | E. x e. C y = B } ) -> ch ) $=
      ( nfv elabreximd ) ABCDEFGHIADMCDMJKLN $.
  $}

  ${
    abrexss.1 $e |- F/_ x C $.
    $d x y z $.  $d y z A $.  $d z C $.  $d y z B $.
    $( A necessary condition for an image set to be a subset.  (Contributed by
       Thierry Arnoux, 6-Feb-2017.) $)
    abrexss $p |- ( A. x e. A B e. C -> { y | E. x e. A y = B } C_ C ) $=
      ( vz wcel wral cv wceq wrex cab cvv nfra1 nfcri eleq1 vex a1i rspa ssrdv
      elabreximd ex ) DEHZACIZGBJDKACLBMZEUEGJZUFHUGEHZUEUDUHABUGDCNUDACOAGEFPU
      GDEQUGNHUEGRSUDACTUBUCUA $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Set relations and operations - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Negated membership for a union.  (Contributed by Thierry Arnoux,
     13-Dec-2023.) $)
  nelun $p |- ( A = ( B u. C ) -> ( -. X e. A <-> ( -. X e. B /\ -. X e. C )
      ) ) $=
    ( cun wceq wcel wn wo wa eleq2 elun bitrdi notbid ioran ) ABCEZFZDAGZHDBGZD
    CGZIZHSHTHJQRUAQRDPGUAAPDKDBCLMNSTOM $.

  $( If a singleton is a subset of another, their members are equal.
     (Contributed by NM, 28-May-2006.)  (Revised by Thierry Arnoux,
     11-Apr-2024.) $)
  snsssng $p |- ( ( A e. V /\ { A } C_ { B } ) -> A = B ) $=
    ( csn wss wcel c0 wceq wo sssn snnzg neneqd pm2.21d sneqrg jaod imp sylan2b
    ) ADZBDZEACFZRGHZRSHZIZABHZRBJTUCUDTUAUDUBTUAUDTRGACKLMABCNOPQ $.

  ${
    $d A x $.  $d B x $.
    $( If a class with one element is not a singleton, there is at least
       another element in this class.  (Contributed by AV, 6-Mar-2025.)
       (Revised by Thierry Arnoux, 28-May-2025.) $)
    n0nsnel $p |- ( ( C e. B /\ B =/= { A } ) -> E. x e. B x =/= A ) $=
      ( wcel csn wne cv wrex wceq wn wral c0 ne0i eqsn syl biimprd con3d df-ne
      wb nne bicomi ralbii ralnex bitri con2bii 3imtr4g imp ) DCEZCBFZGZAHZBGZA
      CIZUICUJJZKULBJZACLZKUKUNUIUQUOUIUOUQUICMGUOUQTCDNACBOPQRCUJSUQUNUQUMKZAC
      LUNKUPURACURUPULBUAUBUCUMACUDUEUFUGUH $.
  $}

  $( Intersection with an intersection.  (Contributed by Thierry Arnoux,
     27-Dec-2016.) $)
  inin $p |- ( A i^i ( A i^i B ) ) = ( A i^i B ) $=
    ( cin in13 inidm ineq2i incom 3eqtri ) AABCZCBAACZCBACIAABDJABAEFBAGH $.

  $( Condition for the intersections of two sets with a given set to be equal.
     (Contributed by Thierry Arnoux, 28-Dec-2021.) $)
  difininv $p |- ( ( ( ( A \ C ) i^i B ) = (/) /\ ( ( C \ A ) i^i B ) = (/) )
    -> ( A i^i B ) = ( C i^i B ) ) $=
    ( cdif cin c0 wceq wa indif1 eqeq1i ssdif0 sylbb2 adantr inss2 ssind adantl
    wss a1i eqssd ) ACDBEZFGZCADBEZFGZHZABEZCBEZUDUECBUAUECQZUCUAUECDZFGUGTUHFA
    BCIJUECKLMUEBQUDABNROUDUFABUCUFAQZUAUCUFADZFGUIUBUJFCBAIJUFAKLPUFBQUDCBNROS
    $.

  $( Rewriting an equation with class difference, without using quantifiers.
     (Contributed by Thierry Arnoux, 24-Sep-2017.) $)
  difeq $p |- ( ( A \ B ) = C <->
                         ( ( C i^i B ) = (/) /\ ( C u. B ) = ( A u. B ) ) ) $=
    ( cdif wceq cin c0 wa ineq1 disjdifr eqtr3di uneq1 undif1 disj3 eqcom bitri
    cun jca birani difun2 wb difeq1 3eqtr3g eqeq1d adantl mpbid impbii ) ABDZCE
    ZCBFZGEZCBQZABQZEZHZUIUKUNUIUHBFUJGUHCBIBAJKUIUHBQULUMUHCBLABMKRUOCBDZCEZUI
    UKUQUNUKCUPEUQCBNCUPOPSUNUQUIUAUKUNUPUHCUNULBDUMBDUPUHULUMBUBCBTABTUCUDUEUF
    UG $.

  $( If both set differences of two sets are empty, those sets are equal.
     (Contributed by Thierry Arnoux, 16-Nov-2023.) $)
  eqdif $p |- ( ( ( A \ B ) = (/) /\ ( B \ A ) = (/) ) -> A = B ) $=
    ( wceq wss wa cdif c0 eqss ssdif0 anbi12i sylbbr ) ABCABDZBADZEABFGCZBAFGCZ
    EABHLNMOABIBAIJK $.

  $( Two ways to express equality relative to a class ` A ` .  (Contributed by
     Thierry Arnoux, 23-Jun-2024.) $)
  indifbi $p |- ( ( A i^i B ) = ( A i^i C ) <-> ( A \ B ) = ( A \ C ) ) $=
    ( cin wceq cdif wss wb inss1 rcompleq mp2an difin eqeq12i bitri ) ABDZACDZE
    ZAOFZAPFZEZABFZACFZEOAGPAGQTHABIACIOPAJKRUASUBABLACLMN $.

  $( Case where ~ diffi is a biconditional.  (Contributed by Thierry Arnoux,
     27-Jun-2024.) $)
  diffib $p |- ( B e. Fin -> ( A e. Fin <-> ( A \ B ) e. Fin ) ) $=
    ( cfn wcel cdif diffi adantl wn difinf ancoms ex con4d imp impbida ) BCDZAC
    DZABECDZPQOABFGOQPOPQOPHZQHZROSABIJKLMN $.

  $( Difference law for Cartesian products.  (Contributed by Thierry Arnoux,
     24-Jul-2023.) $)
  difxp1ss $p |- ( ( A \ C ) X. B ) C_ ( A X. B ) $=
    ( cdif cxp difxp1 difss eqsstri ) ACDBEABEZCBEZDIACBFIJGH $.

  $( Difference law for Cartesian products.  (Contributed by Thierry Arnoux,
     24-Jul-2023.) $)
  difxp2ss $p |- ( A X. ( B \ C ) ) C_ ( A X. B ) $=
    ( cdif cxp difxp2 difss eqsstri ) ABCDEABEZACEZDIABCFIJGH $.

  $( A remarkable equation with sets.  (Contributed by Thierry Arnoux,
     18-May-2020.) $)
  indifundif $p |- ( ( ( A i^i B ) \ C ) u. ( A \ B ) ) = ( A \ ( B i^i C ) )
    $=
    ( cin cdif cun difindi difundir inundif difeq1i uncom uneq2i unass undifabs
    3eqtr3i uneq1i 3eqtr2i 3eqtrri ) ABCDEABEZACEZFZSABDZCEZFZUCSFABCGUASSCEZUC
    FZFSUEFZUCFUDTUFSUBSFZCEUCUEFTUFUBSCHUHACABIJUCUEKOLSUEUCMUGSUCSCNPQSUCKR
    $.

  ${
    elpwincl.1 $e |- ( ph -> A e. ~P C ) $.
    $( Closure of intersection with regard to elementhood to a power set.
       (Contributed by Thierry Arnoux, 18-May-2020.) $)
    elpwincl1 $p |- ( ph -> ( A i^i B ) e. ~P C ) $=
      ( cin cpw wcel wss elpwi ssinss1 3syl cvv wb inex1g elpwg mpbird ) ABCFZD
      GZHZRDIZABSHZBDIUAEBDJBCDKLAUBRMHTUANEBCSORDMPLQ $.

    $( Closure of class difference with regard to elementhood to a power set.
       (Contributed by Thierry Arnoux, 18-May-2020.) $)
    elpwdifcl $p |- ( ph -> ( A \ B ) e. ~P C ) $=
      ( cdif cpw wcel wss elpwid ssdifssd cvv wb difexg elpwg 3syl mpbird ) ABC
      FZDGZHZRDIZABDCABDEJKABSHRLHTUAMEBCSNRDLOPQ $.
  $}

  ${
    $d A k $.  $d C k $.  $d k ph $.
    elpwiuncl.1 $e |- ( ph -> A e. V ) $.
    elpwiuncl.2 $e |- ( ( ph /\ k e. A ) -> B e. ~P C ) $.
    $( Closure of indexed union with regard to elementhood to a power set.
       (Contributed by Thierry Arnoux, 27-May-2020.) $)
    elpwiuncl $p |- ( ph -> U_ k e. A B e. ~P C ) $=
      ( ciun cpw wcel wss wral cv wa elpwid ralrimiva iunss sylibr cvv wb elpwg
      jca iunexg 3syl mpbird ) AEBCIZDJZKZUGDLZACDLZEBMUJAUKEBAENBKOCDHPQEBCDRS
      ABFKZCUHKZEBMZOUGTKUIUJUAAULUNGAUMEBHQUCEBCFUHUDUGDTUBUEUF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Unordered pairs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    elpreq.1 $e |- ( ph -> X e. { A , B } ) $.
    elpreq.2 $e |- ( ph -> Y e. { A , B } ) $.
    elpreq.3 $e |- ( ph -> ( X = A <-> Y = A ) ) $.
    $( Equality wihin a pair.  (Contributed by Thierry Arnoux, 23-Aug-2017.) $)
    elpreq $p |- ( ph -> X = Y ) $=
      ( wceq wa simpr biimpa eqtr4d wn cpr wcel wo elpri syl orcanai simpl 3syl
      notbid wi pm2.53 sylc pm2.61dan ) ADBIZDEIAUHJDBEAUHKAUHEBIZHLMAUHNZJZDCE
      AUHDCIZADBCOZPUHULQFDBCRSTUKAUINZECIZAUJUAAUJUNAUHUIHUCLAEUMPUIUOQUNUOUDG
      EBCRUIUOUEUBUFMUG $.
  $}

  ${
    prssad.1 $e |- ( ph -> A e. V ) $.
    prssad.2 $e |- ( ph -> { A , B } C_ C ) $.
    $( If a pair is a subset of a class, the first element of the pair is an
       element of that class.  (Contributed by Thierry Arnoux, 2-Nov-2025.) $)
    prssad $p |- ( ph -> A e. C ) $=
      ( cvv wcel wa cpr wss adantr simpr prssg biimpar syl21anc simpld wn csn
      wceq prprc2 adantl eqsstrrd snssg syl2an2r pm2.61dan ) ACHIZBDIZAUHJZUICD
      IZUJBEIZUHBCKZDLZUIUKJZAULUHFMAUHNAUNUHGMULUHJUOUNBCDEHOPQRAULUHSZBTZDLZU
      IFAUPJUQUMDUPUMUQUAABCUBUCAUNUPGMUDULUIURBDEUEPUFUG $.
  $}

  ${
    prssbd.1 $e |- ( ph -> B e. V ) $.
    prssbd.2 $e |- ( ph -> { A , B } C_ C ) $.
    $( If a pair is a subset of a class, the second element of the pair is an
       element of that class.  (Contributed by Thierry Arnoux, 2-Nov-2025.) $)
    prssbd $p |- ( ph -> B e. C ) $=
      ( cvv wcel wa cpr wss simpr adantr prssg biimpar syl21anc simprd wn csn
      wceq prprc1 adantl eqsstrrd snssg syl2an2r pm2.61dan ) ABHIZCDIZAUHJZBDIZ
      UIUJUHCEIZBCKZDLZUKUIJZAUHMAULUHFNAUNUHGNUHULJUOUNBCDHEOPQRAULUHSZCTZDLZU
      IFAUPJUQUMDUPUMUQUAABCUBUCAUNUPGNUDULUIURCDEUEPUFUG $.
  $}

  $( A set ` A ` not in a pair is neither element of the pair.  (Contributed by
     Thierry Arnoux, 20-Nov-2023.) $)
  nelpr $p |- ( A e. V -> ( -. A e. { B , C } <-> ( A =/= B /\ A =/= C ) ) )
      $=
    ( wcel cpr wn wceq wo wne wa elprg notbid neanior bitr4di ) ADEZABCFEZGABHA
    CHIZGABJACJKPQRABCDLMABACNO $.

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( Rewrite an empty intersection with a pair.  (Contributed by Thierry
       Arnoux, 20-Nov-2023.) $)
    inpr0 $p |- ( ( A i^i { B , C } ) = (/) <-> ( -. B e. A /\ -. C e. A ) ) $=
      ( vx cv wne wa wral cpr cin c0 wceq wcel wn r19.26 wi wal wb 3bitr4i nelb
      cvv nelpr elv imbi2i albii disj1 df-ral anbi12i ) DEZBFZUICFZGZDAHZUJDAHZ
      UKDAHZGABCIZJKLZBAMNZCAMNZGUJUKDAOUIAMZUIUPMNZPZDQUTULPZDQUQUMVBVCDVAULUT
      VAULRDUIBCUAUBUCUDUEDAUPUFULDAUGSURUNUSUODBATDCATUHS $.
  $}

  $( The first element of a pair is not an element of a difference with this
     pair.  (Contributed by Thierry Arnoux, 20-Nov-2023.) $)
  neldifpr1 $p |- -. A e. ( C \ { A , B } ) $=
    ( cpr cdif wcel wne neirr eldifpr simp2bi mto ) ACABDEFZAAGZAHLACFMABGACABI
    JK $.

  $( The second element of a pair is not an element of a difference with this
     pair.  (Contributed by Thierry Arnoux, 20-Nov-2023.) $)
  neldifpr2 $p |- -. B e. ( C \ { A , B } ) $=
    ( cpr cdif wcel wne neirr eldifpr simp3bi mto ) BCABDEFZBBGZBHLBCFBAGMBCABI
    JK $.

  ${
    $d P x $.  $d X x $.
    $( The other element of a pair is an element of the pair.  (Contributed by
       Thierry Arnoux, 26-Aug-2017.) $)
    unidifsnel $p |- ( ( X e. P /\ P ~~ 2o ) -> U. ( P \ { X } ) e. P ) $=
      ( wcel c2o cen wbr csn wceq cuni c1o ccrd cfv cfn 2onn adantl csuc eqtrdi
      vx wa sylib cdif cv wex com nnfi ax-mp enfi mpbiri diffi syl ensymd simpl
      cardidd dif1card syl2anc cardennn mpan2 df-2o eqtr3d suc11reg breqtrd en1
      simpr unieqd unisnv difssd eqsstrrd vsnid ssel2 sylancl eqeltrd exlimddv
      wss ) BACZADEFZSZABGZUAZRUBZGZHZVRIZACRVPVRJEFWARUCVPVRVRKLZJEVPWCVRVPVRM
      VPAMCZVRMCVOWDVNVOWDDMCZDUDCZWENDUEUFADUGUHOZAVQUIUJUMUKVPWCPZJPZHWCJHVPA
      KLZWHWIVPWDVNWJWHHWGVNVOULABUNUOVOWJWIHVNVOWJDWIVOWFWJDHNADUPUQURQOUSWCJU
      TTVARVRVBTVPWASZWBVSAWKWBVTIVSWKVRVTVPWAVCZVDRVEQWKVTAVMVSVTCVSACWKVTVRAW
      LWKAVQVFVGRVHVTAVSVIVJVKVL $.

    $( The other element of a pair is not the known element.  (Contributed by
       Thierry Arnoux, 26-Aug-2017.) $)
    unidifsnne $p |- ( ( X e. P /\ P ~~ 2o ) -> U. ( P \ { X } ) =/= X ) $=
      ( wcel c2o cen wbr csn wceq cuni c1o ccrd cfv cfn 2onn adantl csuc eqtrdi
      vx wa c0 cdif wne wex com nnfi ax-mp enfi mpbiri diffi syl cardidd ensymd
      simpl dif1card syl2anc cardennn mpan2 df-2o eqtr3d suc11reg sylib breqtrd
      cv en1 cvv simplll elexd cin simplr sneqbg biimpar ad4ant14 eqtr4d ineq2d
      wn disjdif inidm 3eqtr3g eqcomd snprc sylibr pm2.65da neqned simpr unieqd
      unisnv neeqtrrd necomd exlimddv ) BACZADEFZSZABGZUAZRVCZGZHZWNIZBUBRWLWNJ
      EFWQRUCWLWNWNKLZJEWLWSWNWLWNMWLAMCZWNMCWKWTWJWKWTDMCZDUDCZXANDUEUFADUGUHO
      ZAWMUIUJUKULWLWSPZJPZHWSJHWLAKLZXDXEWLWTWJXFXDHXCWJWKUMABUNUOWKXFXEHWJWKX
      FDXEWKXBXFDHNADUPUQURQOUSWSJUTVAVBRWNVDVAWLWQSZBWRXGBWOWRXGBWOXGBWOHZBVEC
      ZXGXHSZBAWJWKWQXHVFVGXJWMTHXIVOXJTWMXJWMWNVHWMWMVHTWMXJWNWMWMXJWNWPWMWLWQ
      XHVIWJXHWMWPHZWKWQWJXKXHBWOAVJVKVLVMVNWMAVPWMVQVRVSBVTWAWBWCXGWRWPIWOXGWN
      WPWLWQWDWERWFQWGWHWI $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Unordered triples
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( An unordered triple of elements of a class is a subset of the class.
     (Contributed by Thierry Arnoux, 2-Nov-2025.) $)
  tpssg $p |- ( ( A e. V /\ B e. W /\ C e. X )
              -> ( ( A e. D /\ B e. D /\ C e. D ) <-> { A , B , C } C_ D ) ) $=
    ( wcel w3a ctp wss wb wa df-3an cpr csn prssg snssg bi2anan9 cun unss df-tp
    sseq1i bitr4i bitrdi bitrid 3impa ) AEHZBFHZCGHZADHZBDHZCDHZIZABCJZDKZLUNUK
    ULMZUMMZUHUIMZUJMZUPUKULUMNUTURABOZDKZCPZDKZMZUPUSUQVBUJUMVDABDEFQCDGRSVEVA
    VCTZDKUPVAVCDUAUOVFDABCUBUCUDUEUFUG $.

  ${
    tpssd.1 $e |- ( ph -> A e. D ) $.
    tpssd.2 $e |- ( ph -> B e. D ) $.
    tpssd.3 $e |- ( ph -> C e. D ) $.
    $( Deduction version of tpssi :  An unordered triple of elements of a class
       is a subset of that class.  (Contributed by Thierry Arnoux,
       2-Nov-2025.) $)
    tpssd $p |- ( ph -> { A , B , C } C_ D ) $=
      ( wcel ctp wss tpssi syl3anc ) ABEICEIDEIBCDJEKFGHBCDELM $.
  $}

  ${
    tpssad.1 $e |- ( ph -> A e. V ) $.
    tpssad.2 $e |- ( ph -> { A , B , C } C_ D ) $.
    $( If an ordered triple is a subset of a class, the first element of the
       triple is an element of that class.  (Contributed by Thierry Arnoux,
       2-Nov-2025.) $)
    tpssad $p |- ( ph -> A e. D ) $=
      ( cvv wcel wn wa adantr cpr ctp wne wceq simpr intnanrd tpprceq3 eqsstrrd
      tpcomb syl eqtrid wss prssad w3a simprl simprr biimpar syl31anc pm2.61dda
      tpssg simp1d ) ACIJZDIJZBEJZAUOKZLZBDEFABFJZURGMUSBDNZBCDOZEUSVBBDCOZVABC
      DUBUSUOCDPZLKVCVAQUSUOVDAURRSBDCTUCUDAVBEUEZURHMUAUFAUPKZLZBCEFAUTVFGMVGB
      CNZVBEVGUPDCPZLKVBVHQVGUPVIAVFRSBCDTUCAVEVFHMUAUFAUOUPLZLZUQCEJZDEJZVKUTU
      OUPVEUQVLVMUGZAUTVJGMAUOUPUHAUOUPUIAVEVJHMUTUOUPUGVNVEBCDEFIIUMUJUKUNUL
      $.
  $}

  ${
    tpssbd.1 $e |- ( ph -> B e. V ) $.
    tpssbd.2 $e |- ( ph -> { A , B , C } C_ D ) $.
    $( If an ordered triple is a subset of a class, the second element of the
       triple is an element of that class.  (Contributed by Thierry Arnoux,
       2-Nov-2025.) $)
    tpssbd $p |- ( ph -> B e. D ) $=
      ( ctp tprot eqsstrrid tpssad ) ACDBEFGACDBIBCDIEBCDJHKL $.
  $}

  ${
    tpsscd.1 $e |- ( ph -> C e. V ) $.
    tpsscd.2 $e |- ( ph -> { A , B , C } C_ D ) $.
    $( If an ordered triple is a subset of a class, the third element of the
       triple is an element of that class.  (Contributed by Thierry Arnoux,
       2-Nov-2025.) $)
    tpsscd $p |- ( ph -> C e. D ) $=
      ( ctp tprot eqtri eqsstrrid tpssad ) ADBCEFGADBCIZBCDIZEOCDBINBCDJCDBJKHL
      M $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Conditional operator - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d a x $.  $d x C $.  $d x X $.  $d x Y $.  $d x V $.  $d x W $.
    $d x ps $.  $d x th $.
    ifeqeqx.1 $e |- ( x = X -> A = C ) $.
    ifeqeqx.2 $e |- ( x = Y -> B = a ) $.
    ifeqeqx.3 $e |- ( x = X -> ( ch <-> th ) ) $.
    ifeqeqx.4 $e |- ( x = Y -> ( ch <-> ps ) ) $.
    ifeqeqx.5 $e |- ( ph -> a = C ) $.
    ifeqeqx.6 $e |- ( ( ph /\ ps ) -> th ) $.
    ifeqeqx.y $e |- ( ph -> Y e. V ) $.
    ifeqeqx.x $e |- ( ph -> X e. W ) $.
    $( An equality theorem tailored for ~ ballotlemsf1o .  (Contributed by
       Thierry Arnoux, 14-Apr-2017.) $)
    ifeqeqx $p |- ( ( ph /\ x = if ( ps , X , Y ) )
                                                  -> a = if ( ch , A , B ) ) $=
      ( cv wceq cif wa eqeq2 csb simplr wsbc simpll simpr sbceq1a biimpd dfsbcq
      sylc wi csbeq1 eqeq2d imbi12d wcel nfcvd csbiegf syl eqtr4d adantr eqcomd
      a1d wn pm3.24 wb sbcieg anbi1d mtbiri pm2.21d anass1rs ex csbeq1a biimprd
      imp ifbothda notbid nsyld anim2d mtoi expdimp ) CMUBZFUCZWFGUCZWFCFGUDZUC
      AEUBBKLUDZUCZUEZFGFWIWFUFGWIWFUFWLCUEZWKWFEWJFUGZUCZWGAWKCUHZWMACEWJUIZWO
      AWKCUJWMWKCWQWPWLCUKWKCWQCEWJULZUMUOBCEKUIZWFEKFUGZUCZUPCELUIZWFELFUGZUCZ
      UPWQWOUPAKLKWJUCZWSWQXAWOCEKWJUNZXEWTWNWFEKWJFUQURUSLWJUCZXBWQXDWOCELWJUN
      ZXGXCWNWFELWJFUQURUSABUEZXAWSXIWTWFAWTWFUCBAWTHWFAKJUTZWTHUCUAEKFHJXJEHVA
      NVBVCRVDVEVFVGABVHZUEZXBXDAXBXKXDAXBXKUEZXDAXMXDAXMBXKUEZBVIZAXBBXKALIUTZ
      XBBVJTCBELIQVKVCVLVMVNVSVOVPVTUOWKWGWOWKFWNWFEWJFVQURVRUOWLCVHZUEZWKWFEWJ
      GUGZUCZWHAWKXQUHZXRAWQVHZXTAWKXQUJXRWKXQYBYAWLXQUKWKXQYBWKCWQWRWAUMUOBWSV
      HZWFEKGUGZUCZUPXBVHZWFELGUGZUCZUPYBXTUPAKLXEYCYBYEXTXEWSWQXFWAXEYDXSWFEKW
      JGUQURUSXGYFYBYHXTXGXBWQXHWAXGYGXSWFELWJGUQURUSABYCYEABYCUEZYEAYIXNXOAYCX
      KBAYCDBAYCDVHAWSDAXJWSDVJUACDEKJPVKVCWAUMABDSVPWBWCWDVNWEXLYHYFXLYGWFAYGW
      FUCZXKAXPYJTELGWFIXPEWFVAOVBVCVEVFVGVTUOWKWHXTWKGXSWFEWJGVQURVRUOVT $.
  $}

  ${
    elimifd.1 $e |- ( ph -> ( if ( ps , A , B ) = A -> ( ch <-> th ) ) ) $.
    elimifd.2 $e |- ( ph -> ( if ( ps , A , B ) = B -> ( ch <-> ta ) ) ) $.
    $( Elimination of a conditional operator contained in a wff ` ch ` .
       (Contributed by Thierry Arnoux, 25-Jan-2017.) $)
    elimifd $p |- ( ph -> ( ch <-> ( ( ps /\ th ) \/ ( -. ps /\ ta ) ) ) ) $=
      ( wn wo wa wb exmid biantrur a1i andir wceq syl5 pm5.32d iffalse orbi12d
      cif iftrue 3bitrd ) ACBBJZKZCLZBCLZUFCLZKZBDLZUFELZKCUHMAUGCBNOPUHUKMABUF
      CQPAUIULUJUMABCDBBFGUCZFRACDMBFGUDHSTAUFCEUFUNGRACEMBFGUAISTUBUE $.
  $}

  ${
    elim2if.1 $e |- ( if ( ph , A , if ( ps , B , C ) ) = A ->
                                                             ( ch <-> th ) ) $.
    elim2if.2 $e |- ( if ( ph , A , if ( ps , B , C ) ) = B ->
                                                             ( ch <-> ta ) ) $.
    elim2if.3 $e |- ( if ( ph , A , if ( ps , B , C ) ) = C ->
                                                             ( ch <-> et ) ) $.
    $( Elimination of two conditional operators contained in a wff ` ch ` .
       (Contributed by Thierry Arnoux, 25-Jan-2017.) $)
    elim2if $p |- ( ch <-> ( ( ph /\ th ) \/
                       ( -. ph /\ ( ( ps /\ ta ) \/ ( -. ps /\ et ) ) ) ) ) $=
      ( wa wn wo cif wceq wb eqeq1d biimtrrdi iftrue syl iffalse elimifd cases
      ) ACDBEMBNFMOAAGBHIPZPZGQCDRAGUFUAJUBANZBCEFHIUHUFHQUGHQCERUHUGUFHAGUFUCZ
      SKTUHUFIQUGIQCFRUHUGUFIUISLTUDUE $.

    elim2ifim.1 $e |- ( ph -> th ) $.
    elim2ifim.2 $e |- ( ( -. ph /\ ps ) -> ta ) $.
    elim2ifim.3 $e |- ( ( -. ph /\ -. ps ) -> et ) $.
    $( Elimination of two conditional operators for an implication.
       (Contributed by Thierry Arnoux, 25-Jan-2017.) $)
    elim2ifim $p |- ch $=
      ( wa wn wo ancli ex exmid pm4.42 ancld orim12i sylbi ax-mp elim2if mpbir
      imp ) CADPZAQZBEPZBQZFPZRZPZRZAUKRUQAUAAUJUKUPADMSUKUOUKUKBPZUKUMPZRUOUKB
      UBURULUSUNUKBULUKBEUKBENTUCUIUKUMUNUKUMFUKUMFOTUCUIUDUESUDUFABCDEFGHIJKLU
      GUH $.
  $}

  ${
    ifeq3da.1 $e |- ( if ( ps , E , F ) = E -> C = G ) $.
    ifeq3da.2 $e |- ( if ( ps , E , F ) = F -> C = H ) $.
    ifeq3da.3 $e |- ( ph -> G = A ) $.
    ifeq3da.4 $e |- ( ph -> H = B ) $.
    $( Given an expression ` C ` containing ` if ( ps , E , F ) ` , substitute
       (hypotheses .1 and .2) and evaluate (hypotheses .3 and .4) it for both
       cases at the same time.  (Contributed by Thierry Arnoux,
       13-Dec-2021.) $)
    ifeq3da $p |- ( ph -> if ( ps , A , B ) = C ) $=
      ( wa wceq cif syl adantl adantr eqtr2d iftrue wn iffalse ifeqda ) ABCDEAB
      NEHCBEHOZABBFGPZFOUEBFGUAJQRAHCOBLSTABUBZNEIDUGEIOZAUGUFGOUHBFGUCKQRAIDOU
      GMSTUD $.
  $}

  $( Deduce truth from a conditional operator value.  (Contributed by Thierry
     Arnoux, 20-Feb-2025.) $)
  ifnetrue $p |- ( ( A =/= B /\ if ( ph , A , B ) = A ) -> ph ) $=
    ( wne cif wceq wa wn iffalse adantl simplr simpll eqnetrd neneqd condan ) B
    CDZABCEZBFZGZAQCFZAHZTSABCIJSUAGZQCUBQBCPRUAKPRUALMNO $.

  $( Deduce falsehood from a conditional operator value.  (Contributed by
     Thierry Arnoux, 20-Feb-2025.) $)
  ifnefals $p |- ( ( A =/= B /\ if ( ph , A , B ) = B ) -> -. ph ) $=
    ( wne cif wceq iftrue adantl simplr simpll necomd eqnetrd neneqd pm2.65da
    wa ) BCDZABCEZCFZOZAQBFZATSABCGHSAOZQBUAQCBPRAIUABCPRAJKLMN $.

  $( The converse of ~ ifbi holds if the two values are not equal.
     (Contributed by Thierry Arnoux, 20-Feb-2025.) $)
  ifnebib $p |- ( A =/= B ->
               ( if ( ph , A , B ) = if ( ps , A , B ) <-> ( ph <-> ps ) ) ) $=
    ( wne cif wceq wb wa wn wo eqif ifnetrue adantrl simprl 2thd 2falsed jaodan
    ifnefals sylan2b ifbi adantl impbida ) CDEZACDFZBCDFGZABHZUFUDBUECGZIZBJZUE
    DGZIZKUGBUECDLUDUIUGULUDUIIABUDUHABACDMNUDBUHOPUDULIABUDUKAJUJACDSNUDUJUKOQ
    RTUGUFUDABCDUAUBUC $.

  $( Commute two nested conditionals.  (Contributed by Thierry Arnoux,
     4-May-2026.) $)
  ififcom $p |- if ( ph , if ( ps , A , B ) , B )
              = if ( ps , if ( ph , A , B ) , B ) $=
    ( wa cif wb wceq ancom ifbi ax-mp ifan 3eqtr3i ) ABEZCDFZBAEZCDFZABCDFDFBAC
    DFDFNPGOQHABINPCDJKABCDLBACDLM $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Set union
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x $.  $d B x $.
    $( Sufficient and necessary condition for a union to intersect with a given
       set.  (Contributed by Thierry Arnoux, 27-Jan-2020.) $)
    uniinn0 $p |- ( ( U. A i^i B ) =/= (/) <-> E. x e. A ( x i^i B ) =/= (/) )
      $=
      ( cv cin c0 wne wrex cuni wral wceq nne ralbii ralnex cvv cdif wss unissb
      wn disj2 3bitr4ri 3bitr3i necon1abii ) ADZCEZFGZABHZBIZCEZFUFSZABJUEFKZAB
      JZUGSUIFKZUJUKABUEFLMUFABNUHOCPZQUDUNQZABJUMULABUNRUHCTUKUOABUDCTMUAUBUC
      $.
  $}

  $( Express a class difference using unions and class complements.
     (Contributed by Thierry Arnoux, 21-Jun-2020.) $)
  difuncomp $p |- ( A C_ C -> ( A \ B ) = ( C \ ( ( C \ A ) u. B ) ) ) $=
    ( wss cdif cin cun wceq sseqin2 biimpi incom eqtr3di difeq1d difundi ineq1d
    dfss4 eqtrid indif2 eqtrdi eqtr4d ) ACDZABEACFZBEZCCAEZBGEZUAAUBBUACAFZAUBU
    AUFAHACIJCAKLMUAUEACBEZFZUCUAUECUDEZUGFUHCUDBNUAUIAUGUAUIAHACPJOQACBRST $.

  ${
    elpwunicl.1 $e |- ( ph -> A e. ~P ~P B ) $.
    $( Closure of a set union with regard to elementhood to a power set.
       (Contributed by Thierry Arnoux, 21-Jun-2020.)  (Proof shortened by BJ,
       6-Apr-2024.) $)
    elpwunicl $p |- ( ph -> U. A e. ~P B ) $=
      ( cpw wcel cuni elpwpwel sylib ) ABCEZEFBGJFDBCHI $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Indexed union - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y z $.  $d z A $.  $d z B $.  $d z C $.
    cbviunf.x $e |- F/_ x A $.
    cbviunf.y $e |- F/_ y A $.
    cbviunf.1 $e |- F/_ y B $.
    cbviunf.2 $e |- F/_ x C $.
    cbviunf.3 $e |- ( x = y -> B = C ) $.
    $( Rule used to change the bound variables in an indexed union, with the
       substitution specified implicitly by the hypothesis.  (Contributed by
       NM, 26-Mar-2006.)  (Revised by Andrew Salmon, 25-Jul-2011.) $)
    cbviunf $p |- U_ x e. A B = U_ y e. A C $=
      ( vz cv wcel wrex cab ciun nfcri weq eleq2d df-iun cbvrexfw abbii 3eqtr4i
      ) KLZDMZACNZKOUDEMZBCNZKOACDPBCEPUFUHKUEUGABCFGBKDHQAKEIQABRDEUDJSUAUBAKC
      DTBKCETUC $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y ph $.
    iuneq12daf.1 $e |- F/ x ph $.
    iuneq12daf.2 $e |- F/_ x A $.
    iuneq12daf.3 $e |- F/_ x B $.
    iuneq12daf.4 $e |- ( ph -> A = B ) $.
    iuneq12daf.5 $e |- ( ( ph /\ x e. A ) -> C = D ) $.
    $( Equality deduction for indexed union, deduction version.  (Contributed
       by Thierry Arnoux, 13-Mar-2017.) $)
    iuneq12daf $p |- ( ph -> U_ x e. A C = U_ x e. B D ) $=
      ( vy cv wcel wrex wb ciun wceq syl cab wal wa eleq2d rexbida rexeqf bitrd
      alrimiv abbi df-iun 3eqtr4g ) ALMZENZBCOZUKFNZBDOZPZLUAZBCEQZBDFQZRAUPLAU
      MUNBCOZUOAULUNBCGABMCNUBEFUKKUCUDACDRUTUOPJUNBCDHIUESUFUGUQUMLTUOLTURUSUM
      UOLUHBLCEUIBLDFUIUJS $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.
    iunin1f.1 $e |- F/_ x C $.
    $( Indexed union of intersection.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ uniiun to recover
       Enderton's theorem.  (Contributed by NM, 26-Mar-2004.)  (Revised by
       Thierry Arnoux, 2-May-2020.) $)
    iunin1f $p |- U_ x e. A ( B i^i C ) = ( U_ x e. A B i^i C ) $=
      ( vy cin ciun cv wcel wrex wa nfcri r19.41 elin rexbii eliun anbi1i eqriv
      3bitr4i ) FABCDGZHZABCHZDGZFIZUAJZABKZUEUCJZUEDJZLZUEUBJUEUDJUECJZUILZABK
      UKABKZUILUGUJUKUIABAFDEMNUFULABUECDOPUHUMUIAUEBCQRTAUEBUAQUEUCDOTS $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.
    $( Subset equivalence for an indexed union.  (Contributed by Thierry
       Arnoux, 17-Oct-2016.) $)
    ssiun3 $p |- ( A. y e. C E. x e. A y e. B <-> C C_ U_ x e. A B ) $=
      ( ciun wss cv wcel wi wal wral wrex df-ss df-ral eliun ralbii 3bitr2ri )
      EACDFZGBHZEITSIZJBKUABELTDIACMZBELBESNUABEOUAUBBEATCDPQR $.
  $}

  ${
    ssiun2sf.1 $e |- F/_ x A $.
    ssiun2sf.2 $e |- F/_ x C $.
    ssiun2sf.3 $e |- F/_ x D $.
    ssiun2sf.4 $e |- ( x = C -> B = D ) $.
    $( Subset relationship for an indexed union.  (Contributed by Thierry
       Arnoux, 31-Dec-2016.) $)
    ssiun2sf $p |- ( C e. A -> D C_ U_ x e. A B ) $=
      ( wcel ciun wss cv wi nfel nfiu1 nfss nfim wceq eleq1 imbi12d vtoclgf
      sseq1d ssiun2 pm2.43i ) DBJZEABCKZLZAMZBJZCUGLZNUFUHNADBGUFUHAADBGFOAEUGH
      ABCPQRUIDSZUJUFUKUHUIDBTULCEUGIUCUAABCUDUBUE $.
  $}

  ${
    $d i j n $.  $d j k n F $.  $d j k n ph $.
    iuninc.1 $e |- ( ph -> F Fn NN ) $.
    iuninc.2 $e |- ( ( ph /\ n e. NN ) -> ( F ` n ) C_ ( F ` ( n + 1 ) ) ) $.
    $( The union of an increasing collection of sets is its last element.
       (Contributed by Thierry Arnoux, 22-Jan-2017.) $)
    iuninc $p |- ( ( ph /\ i e. NN ) ->
      U_ n e. ( 1 ... i ) ( F ` n ) = ( F ` i ) ) $=
      ( vk wcel c1 cfz co cfv ciun wceq wi caddc iuneq1d fveq2 wa wsb vj imbi2d
      cv cn oveq2 eqeq12d csn cz 1z fzsn iuneq1 1ex iunxsn eqtri a1i cun simpll
      mp2b cuz elnnuz fzsuc sylbi iunxun ovex uneq2i eqtrdi simpr uneq1d simplr
      syl wss sbt sbim sban sbv clelsb1 anbi12i bitr2i wsbc csb sbsbc wb sbcssg
      cvv elv csbfv2g csbov1g fveq2i vex csbvargi oveq1i 3eqtri sseq12i 3bitrri
      csbfv imbi12i bitr4i mpbi ssequn1 sylib syl2anc 3eqtrd exp31 nnind impcom
      a2d ) BUCZUDHACIXGJKZCUCZDLZMZXGDLZNZACIUAUCZJKZXJMZXNDLZNZOACIIJKZXJMZID
      LZNZOACIGUCZJKZXJMZYCDLZNZOACIYCIPKZJKZXJMZYHDLZNZOAXMOUAGXGXNINZXRYBAYMX
      PXTXQYAYMCXOXSXJXNIIJUEQXNIDRUFUBXNYCNZXRYGAYNXPYEXQYFYNCXOYDXJXNYCIJUEQX
      NYCDRUFUBXNYHNZXRYLAYOXPYJXQYKYOCXOYIXJXNYHIJUEQXNYHDRUFUBXNXGNZXRXMAYPXP
      XKXQXLYPCXOXHXJXNXGIJUEQXNXGDRUFUBYBAXTCIUGZXJMZYAIUHHXSYQNXTYRNUIIUJCXSY
      QXJUKURCIXJYAULXIIDRUMUNUOYCUDHZAYGYLYSAYGYLYSASZYGSZYJYEYKUPZYFYKUPZYKUU
      AYSYJUUBNYSAYGUQZYSYJCYDYHUGZUPZXJMZUUBYSCYIUUFXJYSYCIUSLHYIUUFNYCUTIYCVA
      VBQUUGYECUUEXJMZUPUUBCYDUUEXJVCUUHYKYECYHXJYKYCIPVDXIYHDRUMVEUNVFVJUUAYEY
      FYKYTYGVGVHUUAAYSUUCYKNZYSAYGVIUUDAYSSZYFYKVKZUUIAXIUDHZSZXJXIIPKZDLZVKZO
      ZCGTZUUJUUKOZUUQCGFVLUURUUMCGTZUUPCGTZOUUSUUMUUPCGVMUUJUUTUUKUVAUUTACGTZU
      ULCGTZSUUJAUULCGVNUVBAUVCYSACGVOCGUDVPVQVRUVAUUPCYCVSZCYCXJVTZCYCUUOVTZVK
      ZUUKUUPCGWAUVDUVGWBGCYCXJUUOWDWCWEUVEYFUVFYKCYCDWOUVFCYCUUNVTZDLZCYCXIVTZ
      IPKZDLYKUVFUVINGCYCUUNWDDWFWEUVHUVKDUVHUVKNGCYCXIIPWDWGWEWHUVKYHDUVJYCIPC
      YCGWIWJWKWHWLWMWNWPWQWRYFYKWSWTXAXBXCXFXDXE $.
  $}

  ${
    $d x A $.  $d x O $.
    $( The intersection of a set is the complement of the union of the
       complements.  (Contributed by Thierry Arnoux, 19-Dec-2016.) $)
    iundifdifd $p |- ( A C_ ~P O ->
      ( A =/= (/) -> |^| A = ( O \ U_ x e. A ( O \ x ) ) ) ) $=
      ( cpw wss c0 cint cv cdif ciun wceq wa ciin iundif2 intiin difeq2i eqtr4i
      wne cuni intssuni2 unipw sseqtrdi dfss4 sylib eqtr2id ex ) BCDZEZBFRZBGZC
      ABCAHZIJZIZKUHUILZUMCCUJIZIZUJULUOCULCABUKMZIUOABCUKNUJUQCABOPQPUNUJCEUPU
      JKUNUJUGSCBUGTCUAUBUJCUCUDUEUF $.
  $}

  ${
    $d x A $.  $d x O $.
    iundifdif.o $e |- O e. _V $.
    iundifdif.2 $e |- A C_ ~P O $.
    $( The intersection of a set is the complement of the union of the
       complements.  TODO: shorten using ~ iundifdifd .  (Contributed by
       Thierry Arnoux, 4-Sep-2016.) $)
    iundifdif $p |- ( A =/= (/) -> |^| A = ( O \ U_ x e. A ( O \ x ) ) ) $=
      ( c0 wne cv cdif ciun cint ciin iundif2 intiin difeq2i eqtr4i wss wceq wa
      cpw cuni jctl intssuni2 unipw sseq2i biimpi 3syl dfss4 sylib eqtr2id ) BF
      GZCABCAHZIJZICCBKZIZIZUNUMUOCUMCABULLZIUOABCULMUNUQCABNOPOUKUNCQZUPUNRUKB
      CTZQZUKSUNUSUAZQZURUKUTEUBBUSUCVBURVACUNCUDUEUFUGUNCUHUIUJ $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d x y z C $.  $d x z D $.  $d x y F $.
    $d x y z ph $.
    iunrdx.1 $e |- ( ph -> F : A -onto-> C ) $.
    iunrdx.2 $e |- ( ( ph /\ y = ( F ` x ) ) -> D = B ) $.
    $( Re-index an indexed union.  (Contributed by Thierry Arnoux,
       6-Apr-2017.) $)
    iunrdx $p |- ( ph -> U_ x e. A B = U_ y e. C D ) $=
      ( vz cv wcel wrex cab ciun cfv wfo wf df-iun ffvelcdmda wceq foelrn sylan
      fof syl wa eleq2d rexxfrd bicomd abbidv 3eqtr4g ) AKLZEMZBDNZKOUMGMZCFNZK
      OBDEPCFGPAUOUQKAUQUOAUPUNCBBLZHQZFDADFURHADFHRZDFHSIDFHUEUFUAAUTCLZFMVAUS
      UBZBDNIBDFVAHUCUDAVBUGGEUMJUHUIUJUKBKDETCKFGTUL $.
  $}

  ${
    $d A y z $.  $d B z $.  $d C x z $.  $d D y z $.  $d ph x y z $.
    iunrnmptss.1 $e |- ( y = B -> C = D ) $.
    iunrnmptss.2 $e |- ( ( ph /\ x e. A ) -> B e. V ) $.
    $( A subset relation for an indexed union over the range of function
       expressed as a mapping.  (Contributed by Thierry Arnoux,
       27-Mar-2018.) $)
    iunrnmptss $p |- ( ph -> U_ y e. ran ( x e. A |-> B ) C C_ U_ x e. A D ) $=
      ( vz cv wcel cmpt wrex cab ciun wa wex df-iun wceq wral wb ralrimiva eqid
      crn df-rex elrnmptg syl anbi1d exbidv r19.41v eleq2d biimpa reximi sylbir
      exlimiv biimtrdi biimtrid ss2abdv 3sstr4g ) AKLZFMZCBDENZUFZOZKPVBGMZBDOZ
      KPCVEFQBDGQAVFVHKVFCLZVEMZVCRZCSZAVHVCCVEUGAVLVIEUAZBDOZVCRZCSVHAVKVOCAVJ
      VNVCAEHMZBDUBVJVNUCAVPBDJUDBDEVIVDHVDUEUHUIUJUKVOVHCVOVMVCRZBDOVHVMVCBDUL
      VQVGBDVMVCVGVMFGVBIUMUNUOUPUQURUSUTCKVEFTBKDGTVA $.
  $}

  ${
    $d C x $.  $d X x $.
    iunxunsn.1 $e |- ( x = X -> B = C ) $.
    $( Appending a set to an indexed union.  (Contributed by Thierry Arnoux,
       20-Nov-2023.) $)
    iunxunsn $p |- ( X e. V -> U_ x e. ( A u. { X } ) B = ( U_ x e. A B u. C )
       ) $=
      ( wcel csn cun ciun iunxun iunxsng uneq2d eqtrid ) FEHZABFIZJCKABCKZAQCKZ
      JRDJABQCLPSDRAFCDEGMNO $.

    $d D x $.  $d Y x $.
    iunxunpr.2 $e |- ( x = Y -> B = D ) $.
    $( Appending two sets to an indexed union.  (Contributed by Thierry Arnoux,
       20-Nov-2023.) $)
    iunxunpr $p |- ( ( X e. V /\ Y e. W )
       -> U_ x e. ( A u. { X , Y } ) B = ( U_ x e. A B u. ( C u. D ) ) ) $=
      ( wcel wa cpr cun ciun iunxun iunxprg uneq2d eqtrid ) HFLIGLMZABHINZOCPAB
      CPZAUBCPZOUCDEOZOABUBCQUAUDUEUCAHICDEFGJKRST $.
  $}

  ${
    $d A x y $.  $d A x z $.  $d B y $.  $d B z $.  $d C y $.  $d E x $.
    $d ph x y $.
    iunxpssiun1.1 $e |- ( ( ph /\ x e. A ) -> C C_ E ) $.
    $( Provide an upper bound for the indexed union of cartesian products.
       (Contributed by Thierry Arnoux, 13-Oct-2025.) $)
    iunxpssiun1 $p |- ( ph -> U_ x e. A ( B X. C ) C_ ( U_ x e. A B X. E ) ) $=
      ( vy cxp ciun cv csb wss wral wcel wa ssiun2 adantl nfcv nfcsb1v sseqtrdi
      csbeq1a cbviun xpss12 ralrimiva nfiun nfxp iunssf sylibr xpeq1i sseqtrrdi
      syl2anc ) ABCDEIZJZHCBHKZDLZJZFIZBCDJZFIAUMURMZBCNUNURMAUTBCABKCOZPZDUQME
      FMUTVBDUSUQVADUSMABCDQRBHCDUPHDSBUODTZBUODUBUCZUAGDUQEFUDULUEBCUMURBUQFHB
      CUPBCSVCUFBFSUGUHUIUSUQFVDUJUK $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Indexed intersection - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A t x y z $.  $d B t y z $.  $d V t $.
    $( Rewriting an indexed intersection into an intersection of its image set.
       (Contributed by Thierry Arnoux, 15-Jun-2024.) $)
    iinabrex $p |- ( A. x e. A B e. V
               -> |^|_ x e. A B = |^| { y | E. x e. A y = B } ) $=
      ( vt vz wcel wral cv cab wceq wi wal cvv nfra1 a1i ex wa wtru nfv alrimiv
      wrex ciin cint eleq2 vex rspa elabreximd adantl nfci nfre1 nfab nfel nfim
      nfal nfan elexd adantlr simplr wb tbtru sylib elabgt sylibr syl2anc eleq1
      rspe imbi12d spcgv syl21anc ralrimi impbida abbidv df-iin df-int 3eqtr4d
      imp ) DEHZACIZFJZDHZACIZFKZGJZBJDLZACUCZBKZHZWAWEHZMZGNZFKZACDUDZWHUEZVTW
      CWLFVTWCWLWCWLVTWCWKGWCWIWJWCWBWJABWEDCOWBACPWJAUAZWEDWAUFZWEOHWCGUGQWBAC
      UHUIRUBUJVTWLSZWBACVTWLAVSACPWKAGWIWJAAWEWHAFWEWPUKWGABWFACULUMUNWPUOUPUQ
      WRAJCHZWBWRWSSZDOHZWLDWHHZWBVTWSXAWLVTWSSDEVSACUHURUSZVTWLWSUTWTXAWFWGTVA
      ZMZBNZXBXCWSXFWRWSXEBWSWFXDWSWFSWGXDWFACVHWGVBVCRUBUJXAXFSXBTVAXBWGTBDOVD
      XBVBVEVFXAWLSXBWBXAWLXBWBMZWKXGGDOWEDLWIXBWJWBWEDWHVGWQVIVJVRVRVKRVLVMVNW
      NWDLVTAFCDVOQWOWMLVTFGWHVPQVQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Disjointness - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y A $.  $d x y B $.
    $( In case ` x ` is not free in ` B ` , disjointness is not so interesting
       since it reduces to cases where ` A ` is a singleton.  (Google Groups
       discussion with Peter Mazsa.)  (Contributed by Thierry Arnoux,
       26-Jul-2018.) $)
    disjnf $p |- ( Disj_ x e. A B <-> ( B = (/) \/ E* x x e. A ) ) $=
      ( vy cin c0 wceq cv wral wdisj wcel wmo inidm eqeq1i orbi1i disjor ralbii
      wo eqidd r19.32v orcom bitri 3bitri moel orbi2i 3bitr4i ) CCEZFGZAHZDHGZD
      BIZABIZRZCFGZULRABCJZUNUIBKALZRUHUNULUGCFCMNOUOUJUHRZDBIZABIUHUKRZABIUMBC
      CADUJCSPURUSABURUHUJRZDBIUSUQUTDBUJUHUAQUHUJDBTUBQUHUKABTUCUPULUNADBUDUEU
      F $.
  $}

  ${
    $d x y z $.  $d y z A $.  $d z B $.  $d z C $.
    cbvdisjf.1 $e |- F/_ x A $.
    cbvdisjf.2 $e |- F/_ y B $.
    cbvdisjf.3 $e |- F/_ x C $.
    cbvdisjf.4 $e |- ( x = y -> B = C ) $.
    $( Change bound variables in a disjoint collection.  (Contributed by
       Thierry Arnoux, 6-Apr-2017.) $)
    cbvdisjf $p |- ( Disj_ x e. A B <-> Disj_ y e. A C ) $=
      ( vz cv wcel wrmo wal wdisj wa wmo nfcri nfan df-rmo eleq1w eleq2d cbvmow
      nfv weq anbi12d 3bitr4i albii df-disj ) JKZDLZACMZJNUJELZBCMZJNACDOBCEOUL
      UNJAKCLZUKPZAQBKCLZUMPZBQULUNUPURABUOUKBUOBUDBJDGRSUQUMAABCFRAJEHRSABUEZU
      OUQUKUMABCUAUSDEUJIUBUFUCUKACTUMBCTUGUHAJCDUIBJCEUIUG $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.
    disjss1f.1 $e |- F/_ x A $.
    disjss1f.2 $e |- F/_ x B $.
    $( A subset of a disjoint collection is disjoint.  (Contributed by Thierry
       Arnoux, 6-Apr-2017.) $)
    disjss1f $p |- ( A C_ B -> ( Disj_ x e. B C -> Disj_ x e. A C ) ) $=
      ( vy wss cv wcel wrmo wal wdisj ssrmof alimdv df-disj 3imtr4g ) BCHZGIDJZ
      ACKZGLSABKZGLACDMABDMRTUAGSABCEFNOAGCDPAGBDPQ $.

    $( Equality theorem for disjoint collection.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
    disjeq1f $p |- ( A = B -> ( Disj_ x e. A C <-> Disj_ x e. B C ) ) $=
      ( wceq wdisj wss wi eqimss2 disjss1f syl eqimss impbid ) BCGZABDHZACDHZPC
      BIQRJCBKACBDFELMPBCIRQJBCNABCDEFLMO $.
  $}

  ${
    $d A y $.  $d B y $.  $d C y $.  $d ph x y $.
    disjxun0.1 $e |- ( ( ph /\ x e. B ) -> C = (/) ) $.
    $( Simplify a disjoint union.  (Contributed by Thierry Arnoux,
       27-Nov-2023.) $)
    disjxun0 $p |- ( ph -> ( Disj_ x e. ( A u. B ) C <-> Disj_ x e. A C ) ) $=
      ( vy cv wcel cun wrmo wal wdisj wa c0 wceq wn nel02 syl df-disj rmounid
      albidv 3bitr4g ) AGHZEIZBCDJZKZGLUEBCKZGLBUFEMBCEMAUGUHGAUEBCDABHDINEOPUE
      QFEUDRSUAUBBGUFETBGCETUC $.
  $}

  ${
    $d x A $.  $d x B $.
    $( A trivial partition into a subset and its complement.  (Contributed by
       Thierry Arnoux, 25-Dec-2016.) $)
    disjdifprg $p |- ( ( A e. V /\ B e. W ) ->
        Disj_ x e. { ( B \ A ) , A } x ) $=
      ( wcel wa c0 wceq cdif cpr wdisj simpr wb cvv id 0ex a1i adantr mpbiri cv
      csn disjxsn eqidd preqsnd mpbir2and disjeq1d wne cin elex disjprg syl3anc
      in0 pm2.61dane ad2antlr difeq2 dif0 eqtrdi preq12d adantl mpbird disjdifr
      difexg ad2antrr wss ssid ssdifeq0 notbii nssne2 sylan2br mpan pm2.61dan
      wn ) BDFZCEFZGZBHIZACBJZBKZAUAZLZVPVQGWAACHKZVTLZVOWCVNVQVOWCCHVOCHIZGZWC
      AHUBZVTLAHVTUCWEAWBWFVTWEWBWFIZWDHHIZVOWDMWEHUDVOWGWDWHGNWDVOCHHEOVOPHOFZ
      VOQRUESUFUGTVOCHUHZGZWCCHUIHIZCUMWKCOFZWIWJWCWLNVOWMWJCEUJSWIWKQRVOWJMACH
      VTCHOVTCIPVTHIPUKULTUNUOVQWAWCNVPVQAVSWBVTVQVRCBHVQVRCHJCBHCUPCUQURVQPUSU
      GUTVAVPVQVMZGZWAVRBUIHIZBCVBWOVROFZBOFZVRBUHZWAWPNVOWQVNWNCBEVCUOVNWRVOWN
      BDUJVDWNWSVPVRVRVEZWNWSVRVFWNWTBVRVEZVMWSXAVQBCVGVHVRBVRVIVJVKUTAVRBVTVRB
      OVTVRIPVTBIPUKULTVL $.
  $}

  ${
    $d x A $.  $d x B $.
    $( A trivial partition of a set into its difference and intersection with
       another set.  (Contributed by Thierry Arnoux, 25-Dec-2016.) $)
    disjdifprg2 $p |-
        ( A e. V -> Disj_ x e. { ( A \ B ) , ( A i^i B ) } x ) $=
      ( wcel cin cdif cpr wdisj cvv inex1g elex disjdifprg syl2anc difin preq1i
      cv wceq a1i disjeq1d mpbid ) BDEZABBCFZGZUCHZAQZIZABCGZUCHZUFIUBUCJEBJEUG
      BCDKBDLAUCBJJMNUBAUEUIUFUEUIRUBUDUHUCBCOPSTUA $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d z C $.  $d x z Y $.
    disjif.1 $e |- F/_ x C $.
    disjif.2 $e |- ( x = Y -> B = C ) $.
    $( Property of a disjoint collection: if ` B ( x ) = C ` and
       ` B ( Y ) = D ` , and ` x =/= Y ` , then ` B ` and ` C ` are disjoint.
       (Contributed by Thierry Arnoux, 30-Dec-2016.) $)
    disji2f $p |- ( ( Disj_ x e. A B /\ ( x e. A /\ Y e. A ) /\
      x =/= Y ) -> ( B i^i C ) = (/) ) $=
      ( vy vz cv wcel wa cin c0 wceq wo weq csb wral eqeq1d wdisj df-ne disjors
      wn equequ1 csbeq1 csbid eqtrdi ineq1d orbi12d eqeq2 csbhypf ineq2d rspc2v
      wne nfcv biimtrid impcom ord 3impia ) ABCUAZAJZBKEBKLZVBEUOZCDMZNOZVDVBEO
      ZUDVAVCLZVFVBEUBVHVGVFVCVAVGVFPZVAHIQZAHJZCRZAIJZCRZMZNOZPZIBSHBSVCVIABCH
      IUCVQVIAIQZCVNMZNOZPHIVBEBBHAQZVJVRVPVTHAIUEWAVOVSNWAVLCVNWAVLAVBCRCAVKVB
      CUFACUGUHUITUJVMEOZVRVGVTVFVMEVBUKWBVSVENWBVNDCAIECDAEUPFGULUMTUJUNUQURUS
      UQUT $.

    $( Property of a disjoint collection: if ` B ( x ) ` and ` B ( Y ) = D `
       have a common element ` Z ` , then ` x = Y ` .  (Contributed by Thierry
       Arnoux, 30-Dec-2016.) $)
    disjif $p |- ( ( Disj_ x e. A B /\ ( x e. A /\ Y e. A ) /\
      ( Z e. B /\ Z e. C ) ) -> x = Y ) $=
      ( wcel wa wdisj cv cin c0 wne wceq inelcm disji2f 3expia necon1d syl3an3
      3impia ) FCIFDIJABCKZALZBIEBIJZCDMZNOZUDEPZFCDQUCUEUGUHUCUEJUDEUFNUCUEUDE
      OUFNPABCDEGHRSTUBUA $.
  $}

  ${
    $d i j x $.  $d x A $.  $d j x B $.  $d i x C $.
    disjorf.1 $e |- F/_ i A $.
    disjorf.2 $e |- F/_ j A $.
    disjorf.3 $e |- ( i = j -> B = C ) $.
    $( Two ways to say that a collection ` B ( i ) ` for ` i e. A ` is
       disjoint.  (Contributed by Thierry Arnoux, 8-Mar-2017.) $)
    disjorf $p |- ( Disj_ i e. A B <->
      A. i e. A A. j e. A ( i = j \/ ( B i^i C ) = (/) ) ) $=
      ( vx cv wcel wal wceq wo wral wi ralcom4 wex bitri bitr4i wrmo c0 df-disj
      wdisj cin wa wn orcom df-or neq0 exbii imbi1i 19.23v 3bitri ralbii eleq2d
      elin nfv rmo4f albii 3bitr4i ) DABUDIJZBKZDAUAZILZDJEJMZBCUEZUBMZNZEAOZDA
      OZDIABUCVCVBCKZUFZVFPZEAOZILZDAOVODAOZILVKVEVODIAQVJVPDAVJVNILZEAOVPVIVRE
      AVIVHVFNVHUGZVFPZVRVFVHUHVHVFUIVTVMIRZVFPVRVSWAVFVSVBVGKZIRWAIVGUJWBVMIVB
      BCUQUKSULVMVFIUMTUNUOVNEIAQSUOVDVQIVCVLDEAFGVLDURVFBCVBHUPUSUTVAT $.
  $}

  ${
    $d i j x $.  $d i j A $.  $d i j B $.
    disjorsf.1 $e |- F/_ x A $.
    $( Two ways to say that a collection ` B ( i ) ` for ` i e. A ` is
       disjoint.  (Contributed by Thierry Arnoux, 8-Mar-2017.) $)
    disjorsf $p |- ( Disj_ x e. A B <-> A. i e. A A. j e. A
      ( i = j \/ ( [_ i / x ]_ B i^i [_ j / x ]_ B ) = (/) ) ) $=
      ( wdisj cv csb wceq cin c0 wo wral nfcsb1v csbeq1a cbvdisjf csbeq1 disjor
      nfcv bitri ) ABCGDBADHZCIZGUBEHZJUCAUDCIZKLJMEBNDBNADBCUCFDCTAUBCOAUBCPQB
      UCUEDEAUBUDCRSUA $.
  $}

  ${
    $d x y z $.  $d y z A $.  $d y z B $.  $d z C $.  $d x z Y $.
    disjif2.1 $e |- F/_ x A $.
    disjif2.2 $e |- F/_ x C $.
    disjif2.3 $e |- ( x = Y -> B = C ) $.
    $( Property of a disjoint collection: if ` B ( x ) ` and ` B ( Y ) = D `
       have a common element ` Z ` , then ` x = Y ` .  (Contributed by Thierry
       Arnoux, 6-Apr-2017.) $)
    disjif2 $p |- ( ( Disj_ x e. A B /\ ( x e. A /\ Y e. A ) /\
      ( Z e. B /\ Z e. C ) ) -> x = Y ) $=
      ( vy vz wcel wa cv cin c0 wceq wo weq csb wdisj wne wral disjorsf equequ1
      inelcm csbeq1 csbid eqtrdi ineq1d eqeq1d orbi12d eqeq2 nfcv ineq2d rspc2v
      csbhypf biimtrid impcom ord necon1ad 3impia syl3an3 ) FCLFDLMABCUAZANZBLE
      BLMZCDOZPUBZVEEQZFCDUFVDVFVHVIVDVFMZVIVGPVJVIVGPQZVFVDVIVKRZVDJKSZAJNZCTZ
      AKNZCTZOZPQZRZKBUCJBUCVFVLABCJKGUDVTVLAKSZCVQOZPQZRJKVEEBBJASZVMWAVSWCJAK
      UEWDVRWBPWDVOCVQWDVOAVECTCAVNVECUGACUHUIUJUKULVPEQZWAVIWCVKVPEVEUMWEWBVGP
      WEVQDCAKECDAEUNHIUQUOUKULUPURUSUTVAVBVC $.
  $}

  ${
    $d i j x y z A $.  $d i j y z B $.
    $( Rewriting a disjoint collection into a partition of its image set.
       (Contributed by Thierry Arnoux, 30-Dec-2016.) $)
    disjabrex $p |- ( Disj_ x e. A B
                                   -> Disj_ y e. { z | E. x e. A z = B } y ) $=
      ( vi vj wdisj cv wcel csb wa cab cuni wceq wral cvv simpllr simplr syl wb
      wrex nfdisj1 nfcv nfcsb1v nfcri nfan nfab nfuni nfcsb1 nfeq1 nfralw eqeq2
      nfv raleqbi1dv vex a1i csn simplll simprl simprr csbeq1a disjif syl122anc
      simpr eqeltrrd eleq2d mpbid jca impbida equcom bitrdi abbidv df-sn unieqd
      eqtr4di unisnv eqtrdi csbeq1 csbid ralrimiva elabreximd invdisj ) ADEHZAF
      IZDJZGIZAWEEKZJZLZFMZNZEKZBIZOZGWNPZBCIEOADUBCMZPBWQWNHWDWPBWQWDWMEOZGEPW
      PACWNEDQADEUCWOAGWNAWNUDAWMWNAWLEAWKWJAFWFWIAWFAUNAGWHAWEEUEZUFUGUHUIUJUK
      ULWOWRGWNEWNEWMUMUOWNQJWDBUPUQWDAIZDJZLZWRGEXBWGEJZLZWLWTOZWRXDWLWTURZNWT
      XDWKXFXDWKWEWTOZFMXFXDWJXGFXDWJWTWEOZXGXDWJXHXDWJLWDXAWFXCWIXHWDXAXCWJUSW
      DXAXCWJRXDWFWIUTXBXCWJSXDWFWIVAADEWHWEWGWSAWEEVBZVCVDXDXHLZWFWIXJWTWEDXDX
      HVEZWDXAXCXHRVFXJXCWIXBXCXHSXJXHXCWIUAXKXHEWHWGXIVGTVHVIVJAFVKVLVMFWTVNVP
      VOAVQVRXEWMAWTEKEAWLWTEVSAEVTVRTWAWBWABGWQWNWMWCT $.
  $}

  ${
    $d i j x y z $.  $d i j y z A $.  $d i j y z B $.
    disjabrexf.1 $e |- F/_ x A $.
    $( Rewriting a disjoint collection into a partition of its image set.
       (Contributed by Thierry Arnoux, 30-Dec-2016.)  (Revised by Thierry
       Arnoux, 9-Mar-2017.) $)
    disjabrexf $p |- ( Disj_ x e. A B
                                   -> Disj_ y e. { z | E. x e. A z = B } y ) $=
      ( vi vj wdisj cv wcel csb wa cab cuni wceq wral cvv nfcri syl wrex nfcsb1
      nfdisj1 nfcv nfcsb1v nfan nfuni nfeq1 nfralw eqeq2 raleqbi1dv vex a1i csn
      nfab simplll simpllr simprl simplr simprr csbeq1a disjif2 syl122anc simpr
      eqeltrrd wb eleq2d mpbid impbida equcom bitrdi abbidv df-sn unieqd unisnv
      jca eqtr4di eqtrdi csbeq1 csbid ralrimiva elabreximd invdisj ) ADEIZAGJZD
      KZHJZAWEELZKZMZGNZOZELZBJZPZHWNQZBCJEPADUACNZQBWQWNIWDWPBWQWDWMEPZHEQWPAC
      WNEDRADEUCWOAHWNAWNUDAWMWNAWLEAWKWJAGWFWIAAGDFSAHWHAWEEUEZSUFUOUGUBUHUIWO
      WRHWNEWNEWMUJUKWNRKWDBULUMWDAJZDKZMZWRHEXBWGEKZMZWLWTPZWRXDWLWTUNZOWTXDWK
      XFXDWKWEWTPZGNXFXDWJXGGXDWJWTWEPZXGXDWJXHXDWJMWDXAWFXCWIXHWDXAXCWJUPWDXAX
      CWJUQXDWFWIURXBXCWJUSXDWFWIUTADEWHWEWGFWSAWEEVAZVBVCXDXHMZWFWIXJWTWEDXDXH
      VDZWDXAXCXHUQVEXJXCWIXBXCXHUSXJXHXCWIVFXKXHEWHWGXIVGTVHVPVIAGVJVKVLGWTVMV
      QVNAVOVRXEWMAWTELEAWLWTEVSAEVTVRTWAWBWABHWQWNWMWCT $.
  $}

  ${
    $d x y z A $.  $d x y z F $.  $d y z B $.
    $( A preimage of a disjoint set is disjoint.  (Contributed by Thierry
       Arnoux, 7-Feb-2017.) $)
    disjpreima $p |- ( ( Fun F /\ Disj_ x e. A B )
                                              -> Disj_ x e. A ( `' F " B ) ) $=
      ( vy vz wdisj cima cv wceq csb cin c0 wral csbima12 cvv csbconstg imaeq1i
      wo elv wfun ccnv inpreima imaeq2 eqtrdi sylan9req ex eqtri ineq12i eqeq1i
      ima0 imbitrrdi orim2d ralimdv disjors 3imtr4g imp ) DUAZABCGZABDUBZCHZGZU
      REIZFIZJZAVCCKZAVDCKZLZMJZSZFBNZEBNVEAVCVAKZAVDVAKZLZMJZSZFBNZEBNUSVBURVK
      VQEBURVJVPFBURVIVOVEURVIUTVFHZUTVGHZLZMJZVOURVIWAURVIVTUTVHHZMVFVGDUCVIWB
      UTMHMVHMUTUDUTUKUEUFUGVNVTMVLVRVMVSVLAVCUTKZVFHVRAVCCUTOWCUTVFWCUTJEAVCUT
      PQTRUHVMAVDUTKZVGHVSAVDCUTOWDUTVGWDUTJFAVDUTPQTRUHUIUJULUMUNUNABCEFUOABVA
      EFUOUPUQ $.
  $}

  ${
    $d A x y z $.  $d B y z $.
    $( Rewriting a disjoint collection using the range of a mapping.
       (Contributed by Thierry Arnoux, 27-May-2020.) $)
    disjrnmpt $p |- ( Disj_ x e. A B -> Disj_ y e. ran ( x e. A |-> B ) y ) $=
      ( vz wdisj cv wceq wrex cab cmpt crn disjabrex wb eqid rnmpt ax-mp sylibr
      disjeq1 ) ACDFBEGDHACIEJZBGZFZBACDKZLZUAFZABECDMUDTHUEUBNAECDUCUCOPBUDTUA
      SQR $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.
    $( If a collection is disjoint, so is the collection of the intersections
       with a given set.  (Contributed by Thierry Arnoux, 14-Feb-2017.) $)
    disjin $p |- ( Disj_ x e. B C -> Disj_ x e. B ( C i^i A ) ) $=
      ( vy cv wcel wrmo wal cin wdisj elinel1 rmoimi alimi df-disj 3imtr4i ) EF
      ZDGZACHZEIQDBJZGZACHZEIACDKACTKSUBEUARACQDBLMNAECDOAECTOP $.

    $( If a collection is disjoint, so is the collection of the intersections
       with a given set.  (Contributed by Thierry Arnoux, 21-Jun-2020.) $)
    disjin2 $p |- ( Disj_ x e. B C -> Disj_ x e. B ( A i^i C ) ) $=
      ( vy cv wcel wrmo wal cin wdisj elinel2 rmoimi alimi df-disj 3imtr4i ) EF
      ZDGZACHZEIQBDJZGZACHZEIACDKACTKSUBEUARACQBDLMNAECDOAECTOP $.
  $}

  ${
    $d a c p q r x A $.  $d b d p q r y B $.  $d a c p C $.  $d b d p D $.
    $d q r x E $.  $d q r y F $.  $d q r ph $.
    disjxpin.1 $e |- ( x = ( 1st ` p ) -> C = E ) $.
    disjxpin.2 $e |- ( y = ( 2nd ` p ) -> D = F ) $.
    disjxpin.3 $e |- ( ph -> Disj_ x e. A C ) $.
    disjxpin.4 $e |- ( ph -> Disj_ y e. B D ) $.
    $( Derive a disjunction over a Cartesian product from the disjunctions over
       its first and second elements.  (Contributed by Thierry Arnoux,
       9-Mar-2018.) $)
    disjxpin $p |- ( ph -> Disj_ p e. ( A X. B ) ( E i^i F ) ) $=
      ( wceq cin csb c0 wo wa vq vr va vc vb vd cv cxp wral wdisj wcel c1st cfv
      c2nd xp1st ad2antrl ad2antll simpl sylib eqeq1 csbeq1 ineq1d eqeq1d eqeq2
      disjors orbi12d ineq2d rspc2v syl5 imp syl21anc xp2nd jca anddi wb xpopth
      orass adantl biimpd wss inss2 csbin ineq12i in4 eqtri cvv csbnestgw ax-mp
      wi vex fvex csbie csbeq2i csbfv 3eqtr3ri 3sstr4i sseq0 mpan adantld inss1
      a1i adantrd jaod orim12d mpd ralrimivva sylibr ) AUAUGZUBUGZOZJXHHIPZQZJX
      IXKQZPZROZSZUBDEUHZUIUAXQUIJXQXKUJAXPUAUBXQXQAXHXQUKZXIXQUKZTZTZXHULUMZXI
      ULUMZOZXHUNUMZXIUNUMZOZTZYDCYEGQZCYFGQZPZROZTZBYBFQZBYCFQZPZROZYGTZYQYLTZ
      SZSZSZXPYAYHYMSYTSZUUBYAYDYQSZYGYLSZTUUCYAUUDUUEYAYBDUKZYCDUKZAUUDXRUUFAX
      SXHDEUOUPXSUUGAXRXIDEUOUQAXTURZUUFUUGTZAUUDAUCUGZUDUGZOZBUUJFQZBUUKFQZPZR
      OZSZUDDUIUCDUIZUUIUUDABDFUJUURMBDFUCUDVEUSUUQUUDYBUUKOZYNUUNPZROZSUCUDYBY
      CDDUUJYBOZUULUUSUUPUVAUUJYBUUKUTUVBUUOUUTRUVBUUMYNUUNBUUJYBFVAVBVCVFUUKYC
      OZUUSYDUVAYQUUKYCYBVDUVCUUTYPRUVCUUNYOYNBUUKYCFVAVGVCVFVHVIVJVKYAYEEUKZYF
      EUKZAUUEXRUVDAXSXHDEVLUPXSUVEAXRXIDEVLUQUUHUVDUVETZAUUEAUEUGZUFUGZOZCUVGG
      QZCUVHGQZPZROZSZUFEUIUEEUIZUVFUUEACEGUJUVONCEGUEUFVEUSUVNUUEYEUVHOZYIUVKP
      ZROZSUEUFYEYFEEUVGYEOZUVIUVPUVMUVRUVGYEUVHUTUVSUVLUVQRUVSUVJYIUVKCUVGYEGV
      AVBVCVFUVHYFOZUVPYGUVRYLUVHYFYEVDUVTUVQYKRUVTUVKYJYICUVHYFGVAVGVCVFVHVIVJ
      VKVMYDYQYGYLVNUSYHYMYTVQUSYAYHXJUUAXOYAYHXJXTYHXJVOAXHXIDEDEVPVRVSYAYMXOY
      TYAYLXOYDYLXOWIYAXNYKVTYLXOJXHHQZJXIHQZPZJXHIQZJXIIQZPZPZUWFXNYKUWCUWFWAX
      NUWAUWDPZUWBUWEPZPUWGXLUWHXMUWIJXHHIWBJXIHIWBWCUWAUWDUWBUWEWDWEZYIUWDYJUW
      EJXHCJUGZUNUMZGQZQZCJXHUWLQZGQZUWDYIXHWFUKZUWNUWPOUAWJZJCXHUWLGWFWGWHJXHU
      WMICUWLGIUWKUNWKLWLZWMUWOYEOUWPYIOJXHUNWNCUWOYEGVAWHWOJXIUWMQZCJXIUWLQZGQ
      ZUWEYJXIWFUKZUWTUXBOUBWJZJCXIUWLGWFWGWHJXIUWMIUWSWMUXAYFOUXBYJOJXIUNWNCUX
      AYFGVAWHWOWCWPXNYKWQWRXAZWSYAYRXOYSYAYQXOYGYQXOWIYAXNYPVTYQXOUWGUWCXNYPUW
      CUWFWTUWJYNUWAYOUWBJXHBUWKULUMZFQZQZBJXHUXFQZFQZUWAYNUWQUXHUXJOUWRJBXHUXF
      FWFWGWHJXHUXGHBUXFFHUWKULWKKWLZWMUXIYBOUXJYNOJXHULWNBUXIYBFVAWHWOJXIUXGQZ
      BJXIUXFQZFQZUWBYOUXCUXLUXNOUXDJBXIUXFFWFWGWHJXIUXGHUXKWMUXMYCOUXNYOOJXIUL
      WNBUXMYCFVAWHWOWCWPXNYPWQWRXAXBYAYLXOYQUXEWSXCXCXDXEXFJXQXKUAUBVEXG $.
  $}

  ${
    $d a b k m n x y $.  $d a b m x y A $.  $d a b m x y B $.
    iundisjf.1 $e |- F/_ k A $.
    iundisjf.2 $e |- F/_ n B $.
    iundisjf.3 $e |- ( n = k -> A = B ) $.
    $( Rewrite a countable union as a disjoint union.  Cf. ~ iundisj .
       (Contributed by Thierry Arnoux, 31-Dec-2016.) $)
    iundisjf $p |- U_ n e. NN A = U_ n e. NN ( A \ U_ k e. ( 1 ..^ n ) B ) $=
      ( vx vm cn ciun c1 cv cfzo wcel wrex cr clt nfcv nfcri cdif csb crab cinf
      co wa cuz cfv wss wne ssrab2 nnuz sseqtri rabn0 biimpri infssuzcl sylancr
      c0 nfrab1 nfinf nfcsb1 wceq csbeq1a eleq2d elrabf sylib simpld simprd wbr
      nnred ltnrd eliun nfrexw nfrabw ad2antrr elfzouz eleqtrrdi ad2antlr simpr
      nfbr cle sylanbrc infssuzle elfzolt2 lelttrd rexlimd biimtrid mtod eldifd
      exp31 csbeq1 nfeq2 nfov oveq2 eqidd iuneq12df difeq12d rspcev syl2anc nfv
      nfcsb1v nfiun nfdif iuneq1d cbvrexw sylibr eldifi reximi impbii 3bitr4i
      eqriv ) HDJAKZDJACLDMZNUEZBKZUAZKZHMZAOZDJPZXRXPOZDJPZXRXLOXRXQOXTYBXTXRD
      IMZAUBZCLYCNUEZBKZUAZOZIJPZYBXTXSDJUCZQRUDZJOZXRDYKAUBZCLYKNUEZBKZUAZOZYI
      XTYLXRYMOZXTYKYJOZYLYRUFXTYJLUGUHZUIZYJURUJZYSYJJYTXSDJUKULUMZUUBXTXSDJUN
      UOYJLUPUQXSYRDYKJDYJQRXSDJUSDQSDRSUTZDJSZDHYMDYKAUUDVATXMYKVBAYMXRDYKAVCV
      DVEVFZVGZXTXRYMYOXTYLYRUUFVHXTXRYOOZYKYKRVIZXTYKXTYKUUGVJZVKUUHXRBOZCYNPX
      TUUICXRYNBVLXTUUKUUICYNXSCDJCJSZCHAETZVMCYKYKRCYJQRXSCDJUUMUULVNCQSCRSZUT
      ZUUNUUOVTXTCMZYNOZUUKUUIXTUUQUFZUUKUFZYKUUPYKXTYKQOUUQUUKUUJVOZUUSUUPUUQU
      UPJOZXTUUKUUQUUPYTJUUPLYKVPULVQVRZVJUUTUUSUUAUUPYJOZYKUUPWAVIUUCUUSUVAUUK
      UVCUVBUURUUKVSXSUUKDUUPJDUUPSUUEDHBFTXMUUPVBABXRGVDVEWBUUPYJLWCUQUUQUUPYK
      RVIXTUUKUUPLYKWDVRWEWJWFWGWHWIYHYQIYKJYCYKVBZYGYPXRUVDYDYMYFYODYCYKAWKUVD
      CYEYNBBCYCYKUUOWLCYESCLYKNCLSCNSUUOWMYCYKLNWNUVDBWOWPWQVDWRWSYAYHDIJYAIWT
      DHYGDYDYFDYCAXACDYEBDYESFXBXCTXMYCVBZXPYGXRUVEAYDXOYFDYCAVCUVECXNYEBXMYCL
      NWNXDWQVDXEXFYAXSDJXRAXOXGXHXIDXRJAVLDXRJXPVLXJXK $.

    $( A disjoint union is disjoint.  Cf. ~ iundisj2 .  (Contributed by Thierry
       Arnoux, 30-Dec-2016.) $)
    iundisj2f $p |- Disj_ n e. NN ( A \ U_ k e. ( 1 ..^ n ) B ) $=
      ( vx vy va vb cn c1 cv cfzo weq csb cin c0 wcel ciun cdif wdisj wceq wral
      co wo wtru tru eqeq12 csbeq1 ineqan12d eqeq1d orbi12d equcom bitrdi incom
      wa eqtrdi cr wss nnssre a1i biidd cle wbr w3a wn wne nesym clt wb nnre id
      leltne syl3an vex nfcsb1v nfcv nfiun nfdif csbeq1a oveq2 iuneq1d difeq12d
      wi csbief ineq12i cuz cfv simp1 nnuz eleqtrdi simp2 nnzd elfzo2 syl3anbrc
      simp3 nfcsbw csbhypf equcoms eqcomd ssiun2sf syl ssdifssd ssrind eqsstrid
      disjdif sseq0 sylancl 3expia 3adant3 sylbird biimtrrid orrd adantl wlogle
      cz mpan rgen2 disjors mpbir ) DLACMDNZOUFZBUAZUBZUCHIPZDHNZYFQZDINZYFQZRZ
      SUDZUGZILUEHLUEYNHILLUHYHLTZYJLTZURZYNUIUHJKPZDJNZYFQZDKNZYFQZRZSUDZUGYNY
      NHIJKLJHPZKIPZURZYRYGUUDYMYSYHUUAYJUJUUGUUCYLSUUEUUFYTYIUUBYKDYSYHYFUKDUU
      AYJYFUKULUMUNJIPZKHPZURZYRYGUUDYMUUJYRIHPYGYSYJUUAYHUJIHUOUPUUJUUCYLSUUJU
      UCYKYIRYLUUHUUIYTYKUUBYIDYSYJYFUKDUUAYHYFUKULYKYIUQUSUMUNLUTVAUHVBVCUHYQU
      RYNVDYOYPYHYJVEVFZVGZYNUHUULYGYMYGVHYJYHVIZUULYMYJYHVJUULUUMYHYJVKVFZYMYO
      YHUTTYPYJUTTUUKUUKUUNUUMVLYHVMYJVMUUKVNYHYJVOVPYOYPUUNYMWFUUKYOYPUUNYMYOY
      PUUNVGZYLCMYJOUFZBUAZDYJAQZUUQUBZRZVAUUTSUDYMUUOYLDYHAQZCMYHOUFZBUAZUBZUU
      SRUUTYIUVDYKUUSDYHYFUVDHVQDUVAUVCDYHAVRCDUVBBDUVBVSFVTWADHPZAUVAYEUVCDYHA
      WBUVECYDUVBBYCYHMOWCWDWEWGDYJYFUUSIVQDUURUUQDYJAVRCDUUPBDUUPVSFVTWADIPZAU
      URYEUUQDYJAWBUVFCYDUUPBYCYJMOWCWDWEWGWHUUOUVDUUQUUSUUOUVAUUQUVCUUOYHUUPTZ
      UVAUUQVAUUOYHMWIWJZTYJXRTUUNUVGUUOYHLUVHYOYPUUNWKWLWMUUOYJYOYPUUNWNWOYOYP
      UUNWRYHMYJWPWQCUUPBYHUVACUUPVSCYHVSZCDYHAUVIEWSCHPUVABUVABUDHCDHCNZABDUVJ
      VSFGWTXAXBXCXDXEXFXGUUQUURXHYLUUTXIXJXKXLXMXNXOXPXQXSXTDLYFHIYAYB $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d x y z C $.  $d x z D $.  $d x y F $.
    $d x y z ph $.
    disjrdx.1 $e |- ( ph -> F : A -1-1-onto-> C ) $.
    disjrdx.2 $e |- ( ( ph /\ y = ( F ` x ) ) -> D = B ) $.
    $( Re-index a disjunct collection statement.  (Contributed by Thierry
       Arnoux, 7-Apr-2017.) $)
    disjrdx $p |- ( ph -> ( Disj_ x e. A B <-> Disj_ y e. C D ) ) $=
      ( vz cv wcel wrmo wal wdisj wa wceq wreu df-disj cfv wf1o f1of ffvelcdmda
      syl f1ofveu sylan eqcom reubii sylib eleq2d rmoxfrd bicomd albidv 3bitr4g
      wf ) AKLZEMZBDNZKOUQGMZCFNZKOBDEPCFGPAUSVAKAVAUSAUTURCBBLZHUAZFDADFVBHADF
      HUBZDFHUPIDFHUCUEUDACLZFMZQVCVERZBDSZVEVCRZBDSAVDVFVHIBDFVEHUFUGVGVIBDVCV
      EUHUIUJAVIQGEUQJUKULUMUNBKDETCKFGTUO $.
  $}

  ${
    $d z A $.  $d z B $.
    $( Two ways to say that two classes are disjoint (or equal).  (Contributed
       by Thierry Arnoux, 4-Oct-2016.) $)
    disjex $p |- ( ( E. z ( z e. A /\ z e. B ) -> A = B ) <->
      ( A = B \/ ( A i^i B ) = (/) ) ) $=
      ( wceq cv wcel wa wex wn wo cin c0 orcom wne cab df-in neeq1i abn0 bitr2i
      wi necon2bbii orbi2i imor 3bitr4ri ) BCDZAEZBFUFCFGZAHZIZJUIUEJUEBCKZLDZJ
      UHUETUEUIMUKUIUEUHUJLUJLNUGAOZLNUHUJULLABCPQUGARSUAUBUHUEUCUD $.

    disjexc.1 $e |- ( x = y -> A = B ) $.
    $( A variant of ~ disjex , applicable for more generic families.
       (Contributed by Thierry Arnoux, 4-Oct-2016.) $)
    disjexc $p |- ( ( E. z ( z e. A /\ z e. B ) -> x = y ) ->
      ( A = B \/ ( A i^i B ) = (/) ) ) $=
      ( cv wcel wa wex wceq wi cin c0 wo imim2i wn orcom wne cab neeq1i 3bitr4i
      df-in abn0 bitr2i necon2bbii orbi2i imor sylibr ) CGZDHUJEHIZCJZAGBGKZLUL
      DEKZLZUNDEMZNKZOZUMUNULFPUNULQZOUSUNOURUOUNUSRUQUSUNULUPNUPNSUKCTZNSULUPU
      TNCDEUCUAUKCUDUEUFUGULUNUHUBUI $.
  $}

  ${
    $d i j x A $.  $d i j B $.  $d i j x C $.  $d i j x M $.  $d i j x V $.
    disjunsn.s $e |- ( x = M -> B = C ) $.
    $( Append an element to a disjoint collection.  Similar to ~ ralunsn ,
       ~ gsumunsn , etc.  (Contributed by Thierry Arnoux, 28-Mar-2018.) $)
    disjunsn $p |- ( ( M e. V /\ -. M e. A ) -> ( Disj_ x e. ( A u. { M } ) B
      <-> ( Disj_ x e. A B /\ ( U_ x e. A B i^i C ) = (/) ) ) ) $=
      ( vi vj wa wceq cin c0 wo wral wb ineq1d eqeq1d ralbidv bitrdi wn csn cun
      wcel wdisj cv csb ciun disjors eqeq1 csbeq1 orbi12d ralunsn bitrid ineq2d
      eqeq2 eqid orci biantru bitr4di anbi12d bitrd r19.26 anbi1i bitr4i adantr
      orcom ralbii r19.30 risset biorf sylnbi adantl imbitrrid biimtrrid ralimi
      wrex olc impbid1 nfv nfcsb1v nfcv nfin nfeq1 csbeq1a cbvralw a1i wss ss0b
      iunss iunin1 eqeq1i bitri nfcvd csbiegf 3bitr4d bitr4d anbi2d clel5 incom
      3bitr3ri anass anidm anbi2i ) EFUDZEBUDZUAZJZABEUBUCZCUEZABCUEZHUFZEKZAXL
      CUGZAECUGZLZMKZNZHBOZJZEIUFZKZXOAYACUGZLZMKZNZIBOZJZXKABCUHDLZMKZJZXEXJYH
      PXGXEXJXLYAKZXNYCLZMKZNZIBOZXRJZHBOZYGJZYHXEXJYOIXIOZHBOZYFIXIOZJZYSXJYTH
      XIOXEUUCAXICHIUIYTUUBHBEFXMYOYFIXIXMYLYBYNYEXLEYAUJXMYMYDMXMXNXOYCAXLECUK
      QRULSUMUNXEUUAYRUUBYGXEYTYQHBYOXRIBEFYAEKZYLXMYNXQYAEXLUPUUDYMXPMUUDYCXOX
      NAYAECUKZUORULUMSXEUUBYGEEKZXOXOLZMKZNZJYGYFUUIIBEFUUDYBUUFYEUUHYAEEUPUUD
      YDUUGMUUDYCXOXOUUEUORULUMUUIYGUUFUUHEUQURUSUTVAVBYRXTYGYRYPHBOZXSJXTYPXRH
      BVCXKUUJXSABCHIUIVDVEVDTVFXHYHYKYJJZYKXHXTYKYGYJXHXSYJXKXHXSXQHBOZYJXHXSU
      ULXSXQXMNZHBOZXHUULUUMXRHBXQXMVGVHUUNUULXHUULXMHBVQZNZXQXMHBVIXHUULUUOUUL
      NZUUPXGUULUUQPZXEXFUUOUURHEBVJUUOUULVKVLVMUUOUULVGTVNVOXQXRHBXQXMVRVPVSXE
      YJUULPXGXECDLZMKZABOZXNDLZMKZHBOZYJUULUVAUVDPXEUUTUVCAHBUUTHVTAUVBMAXNDAX
      LCWAADWBZWCWDAUFZXLKZUUSUVBMUVGCXNDAXLCWEQRWFWGYJUVAPXEYJUUSMWHZABOZUVAAB
      UUSUHZMWHUVJMKUVIYJUVJWIABUUSMWJUVJYIMABDCWKWLXAUVHUUTABUUSWIVHWMWGZXEXQU
      VCHBXEXPUVBMXEXODXNAECDFXEADWNGWOZUORSWPVFWQWRXHYGYEIBOZYJXHYGUVMYGYEYBNZ
      IBOZXHUVMUVNYFIBYEYBVGVHUVOUVMXHUVMYBIBVQZNZYEYBIBVIXHUVMUVPUVMNZUVQXGUVM
      UVRPZXEXFUVPUVSIBEWSUVPUVMVKVLVMUVPUVMVGTVNVOYEYFIBYEYBVRVPVSXEYJUVMPXGXE
      UVADYCLZMKZIBOZYJUVMXEUVAYCDLZMKZIBOZUWBUVAUWEPXEUUTUWDAIBUUTIVTAUWCMAYCD
      AYACWAUVEWCWDUVFYAKZUUSUWCMUWFCYCDAYACWEQRWFWGUWDUWAIBUWCUVTMYCDWTWLVHTUV
      KXEYEUWAIBXEYDUVTMXEXODYCUVLQRSWPVFWQVAUUKXKYJYJJZJYKXKYJYJXBUWGYJXKYJXCX
      DWMTVB $.
  $}

  ${
    $d A x $.
    $( Adding the empty element preserves disjointness.  (Contributed by
       Thierry Arnoux, 30-May-2020.) $)
    disjun0 $p |- ( Disj_ x e. A x -> Disj_ x e. ( A u. { (/) } ) x ) $=
      ( cv wdisj c0 wcel csn cun wss wceq snssi ssequn2 sylib disjeq1d biimparc
      wn wa ciun cin cvv simpl in0 a1i wb 0ex id disjunsn mpan adantl mpbir2and
      pm2.61dan ) ABACZDZEBFZABEGZHZULDZUNUQUMUNAUPBULUNUOBIUPBJEBKUOBLMNOUMUNP
      ZQZUQUMABULRZESEJZUMURUAVAUSUTUBUCURUQUMVAQUDZUMETFURVBUEABULEETULEJUFUGU
      HUIUJUK $.
  $}

  ${
    $d A x $.  $d D x $.  $d E x $.  $d Y x $.
    disjiunel.1 $e |- ( ph -> Disj_ x e. A B ) $.
    disjiunel.2 $e |- ( x = Y -> B = D ) $.
    disjiunel.3 $e |- ( ph -> E C_ A ) $.
    disjiunel.4 $e |- ( ph -> Y e. ( A \ E ) ) $.
    $( A set of elements B of a disjoint set A is disjoint with another element
       of that set.  (Contributed by Thierry Arnoux, 24-May-2020.) $)
    disjiunel $p |- ( ph -> ( U_ x e. E B i^i D ) = (/) ) $=
      ( wdisj ciun cin c0 wceq csn cun wa wcel eldifad snssd unssd disjss1 sylc
      wss wn wb eldifbd disjunsn syl2anc mpbid simprd ) ABFDLZBFDMENOPZABFGQZRZ
      DLZUNUOSZAUQCUFBCDLURAFUPCJAGCAGCFKUAZUBUCHBUQCDUDUEAGCTGFTUGURUSUHUTAGCF
      KUIBFDEGCIUJUKULUM $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.
    disjuniel.1 $e |- ( ph -> Disj_ x e. A x ) $.
    disjuniel.2 $e |- ( ph -> B C_ A ) $.
    disjuniel.3 $e |- ( ph -> C e. ( A \ B ) ) $.
    $( A set of elements B of a disjoint set A is disjoint with another element
       of that set.  (Contributed by Thierry Arnoux, 24-May-2020.) $)
    disjuniel $p |- ( ph -> ( U. B i^i C ) = (/) ) $=
      ( cuni cin cv ciun c0 uniiun ineq1i wceq id disjiunel eqtrid ) ADIZEJBDBK
      ZLZEJMTUBEBDNOABCUAEDEFUAEPQGHRS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Relations and Functions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Relations - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Restriction of a constant function (or other Cartesian product) outside of
     its domain.  (Contributed by Thierry Arnoux, 25-Jan-2017.) $)
  xpdisjres $p |- ( ( A i^i C ) = (/) -> ( ( A X. B ) |` C ) = (/) ) $=
    ( cin c0 wceq cxp cres cvv df-res xpdisj1 eqtrid ) ACDEFABGZCHMCIGDEMCJACBI
    KL $.

  $( Ordered pair elementhood outside of the diagonal.  (Contributed by Thierry
     Arnoux, 1-Jan-2020.) $)
  opeldifid $p |- ( Rel A -> ( <. X , Y >. e. ( A \ _I ) <-> ( <. X , Y >. e. A
    /\ X =/= Y ) ) ) $=
    ( wrel cid cdif wbr wne wa cop wcel cvv reldif brrelex2 sylan adantrr brdif
    wn ideqg df-br necon3bbid anbi2d bitrid pm5.21nd anbi1i 3bitr3g ) ADZBCAEFZ
    GZBCAGZBCHZIZBCJZUHKUMAKZUKIUGUIULCLKZUGUHDUIUOAEMBCUHNOUGUJUOUKBCANPUIUJBC
    EGZRZIUOULBCAEQUOUQUKUJUOUPBCBCLSUAUBUCUDBCUHTUJUNUKBCATUEUF $.

  $( Case when class difference in unaffected by restriction.  (Contributed by
     Thierry Arnoux, 1-Jan-2020.) $)
  difres $p |- ( A C_ ( B X. _V ) -> ( A \ ( C |` B ) ) = ( A \ C ) ) $=
    ( cvv cxp wss cres cdif cin df-res difeq2i cun difindi ssdif difid sseqtrdi
    c0 wceq ss0 eqtrid syl uneq2d un0 eqtrdi ) ABDEZFZACBGZHACUEIZHZACHZUGUHACB
    JKUFUIUJQLZUJUFUIUJAUEHZLUKACUEMUFULQUJUFULQFULQRUFULUEUEHQAUEUENUEOPULSUAU
    BTUJUCUDT $.

  $( Image of the difference with a Cartesian product.  (Contributed by Thierry
     Arnoux, 13-Dec-2017.) $)
  imadifxp $p |- ( C C_ A ->
    ( ( R \ ( A X. B ) ) " C ) = ( ( R " C ) \ B ) ) $=
    ( wss cxp cdif cima wceq ima0 imaeq2 eqtrdi difeq1d wne cun cin eqtrid cvv
    c0 crn 0dif 3eqtr4a adantl uncom un0 eqtr2i inundif imaeq1i imaundir eqtr3i
    wa difeq1i difundir eqtri inss2 imass1 ssdif mp2b cif xpima wn incom biimpi
    dfss2 eqtr3id simpl eqnetrd neneq iffalse 3syl sseqtrid ss0 syl cres df-ima
    difid df-res rneqi ineq1i xpss1 sslin rnss ancoms inss1 ax-mp indif2 difxp2
    ssn0 3sstr4i sseqtrd disj2 sylibr ssdisj syl2an2 disj3 sylib eqcomd uneq12d
    mp1i rnxp eqtr4id pm2.61dane ) CAEZDABFZGZCHZDCHZBGZIZCSCSIZXIXCXJXESHSXFXH
    XEJCSXEKXJXHSBGSXJXGSBXJXGDSHSCSDKDJLMBUALUBUCCSNZXCXIXKXCUKZXFSXFOZXHXMXFS
    OXFSXFUDXFUEUFXLXHDXDPZCHZBGZXFBGZOZXMXHXOXFOZBGXRXGXSBXNXEOZCHXGXSXTDCDXDU
    GUHXNXECUIUJULXOXFBUMUNXLXPSXQXFXLXPSEXPSIXLXDCHZBGZXPSXNXDEXOYAEXPYBEDXDUO
    XNXDCUPXOYABUQURXLYBBBGSXLYABBXLYAACPZSIZSBUSZBABCUTXLYCSNYDVAYEBIXLYCCSXCY
    CCIXKXCYCCAPZCCAVBXCYFCICAVDVCVEUCXKXCVFVGYCSVHYDSBVIVJQMBVPLVKXPVLVMXLXFXQ
    XLXFBPZSIXFXQIXLYGXECRFZPZTZBPZSXFYJBXFXECVNZTYJXECVOYLYIXECVQVRUNVSXCYJXEA
    RFZPZTZEZXKYOBPSIZYKSIXCYHYMEYIYNEYPCARVTYHYMXEWAYIYNWBVJXLASNZYQXCXKYRCAWH
    WCYRYORBGZEYQYRYOAYSFZTZYSYNYTEYOUUAEYRYMDPZXDGZYMXDGZYNYTUUBYMEUUCUUDEYMDW
    DUUBYMXDUQWEYMXEPYNUUCYMXEVBYMDXDWFUJARBWGWIYNYTWBWSAYSWTWJYOBWKWLVMYJYOBWM
    WNQXFBWOWPWQWRQXAWCXB $.

  $( A relation (set) is finite if and only if both its domain and range are
     finite.  (Contributed by Thierry Arnoux, 27-Aug-2017.) $)
  relfi $p |- ( Rel A ->
                       ( A e. Fin <-> ( dom A e. Fin /\ ran A e. Fin ) ) ) $=
    ( wrel cfn wcel cdm crn wa dmfi rnfi jca cxp xpfi relssdmrn ssfi syl2anr ex
    wss impbid2 ) ABZACDZAEZCDZAFZCDZGZTUBUDAHAIJSUETUEUAUCKZCDAUFQTSUAUCLAMUFA
    NOPR $.

  $( Restriction of the empty function.  (Contributed by Thierry Arnoux,
     20-Nov-2023.) $)
  0res $p |- ( (/) |` A ) = (/) $=
    ( c0 cres cvv cxp cin df-res 0in eqtri ) BACBADEZFBBAGJHI $.

  $( Build an equivalence relation from a function.  Two values are equivalent
     if they have the same image by the function.  See also ~ fcoinvbr .
     (Contributed by Thierry Arnoux, 3-Jan-2020.) $)
  fcoinver $p |- ( F Fn X -> ( `' F o. F ) Er X ) $=
    ( wfn ccnv ccom wrel cdm wceq cun wss wer relco a1i cima dmco df-rn eqtr3id
    crn eqtrid coass imaeq2i cnvimarndm fndm cnvco cnvcnvss coss2 ax-mp eqsstri
    cid cres wfun fnfun funcocnv2 coeq1d wf dffn3 fcoi2 sylbi eqtrd coeq2d ssid
    syl eqsstrdi unssd df-er syl3anbrc ) ABCZADZAEZFZVIGZBHVIDZVIVIEZIVIJBVIKVJ
    VGVHALMVGVKVHVHGZNZBVHAOVGVOVHARZNZBVPVNVHAPUAVGVQAGBAUBBAUCSQSVGVLVMVIVLVI
    JVGVLVHVHDZEZVIVHAUDVRAJVSVIJAUEVRAVHUFUGUHMVGVMVIVIVGVMVHAVIEZEVIVHAVITVGV
    TAVHVGVTAVHEZAEZAAVHATVGWBUIVPUJZAEZAVGWAWCAVGAUKWAWCHBAULAUMVBUNVGBVPAUOWD
    AHBAUPBVPAUQURUSQUTSVIVAVCVDBVIVEVF $.

  ${
    $d A z $.  $d F z $.  $d X z $.  $d Y z $.
    fcoinvbr.e $e |- .~ = ( `' F o. F ) $.
    $( Binary relation for the equivalence relation from ~ fcoinver .
       (Contributed by Thierry Arnoux, 3-Jan-2020.) $)
    fcoinvbr $p |- ( ( F Fn A /\ X e. A /\ Y e. A )
       -> ( X .~ Y <-> ( F ` X ) = ( F ` Y ) ) ) $=
      ( vz wfn wcel wbr wa wex cfv wceq wb bitrid eqcom fnbrfvb cvv bitr4d ccnv
      w3a cv ccom breqi brcog 3adant1 fvex eqvinc anbi12i exbii 3adant3 3adant2
      bitri anbi12d vex brcnvg mpan 3ad2ant3 anbi2d exbidv ) CAHZDAIZEAIZUBZDEB
      JZDGUCZCJZVGECUAZJZKZGLZDCMZECMZNZVCVDVFVLOVBVFDEVICUDZJVCVDKVLDEBVPFUEGD
      EVICAAUFPUGVOVMVGNZVNVGNZKZGLZVEVLVOVGVMNZVGVNNZKZGLVTGVMVNDCUHUIWCVSGWAV
      QWBVRVGVMQVGVNQUJUKUNVEVSVKGVEVSVHEVGCJZKVKVEVQVHVRWDVBVCVQVHOVDADVGCRULV
      BVDVRWDOVCAEVGCRUMUOVEVJWDVHVDVBVJWDOZVCVGSIVDWEGUPVGESACUQURUSUTTVAPT $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y ps $.
    brabgaf.0 $e |- F/ x ps $.
    brabgaf.1 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    brabgaf.2 $e |- R = { <. x , y >. | ph } $.
    $( The law of concretion for a binary relation.  (Contributed by Mario
       Carneiro, 19-Dec-2013.)  (Revised by Thierry Arnoux, 17-May-2020.) $)
    brabgaf $p |- ( ( A e. V /\ B e. W ) -> ( A R B <-> ps ) ) $=
      ( cop wcel wa cv wceq wex wb elisset copab df-br eleq2i bitri elopab nfe1
      wbr exdistrv nfbi nfex opeq12 copsexgw eqcoms bitr3d exlimi sylbir syl2an
      nfv syl bitrid ) EFGUGZEFMZACDUAZNZEHNZFINZOZBVAVBGNVDEFGUBGVCVBLUCUDVDVB
      CPZDPZMZQAOZDRZCRZVGBACDVBUEVEVHEQZCRZVIFQZDRZVMBSZVFCEHTDFITVOVQOVNVPOZD
      RZCRVRVNVPCDUHVTVRCVMBCVLCUFJUIVSVRDVMBDVLDCVKDUFUJBDURUIVSAVMBVSVJVBQAVM
      SZVHVIEFUKWAVBVJACDVBULUMUSKUNUOUOUPUQUTUT $.
  $}

  $( Two things in a binary relation belong to the relation's domain.
     (Contributed by Thierry Arnoux, 29-Aug-2017.) $)
  brelg $p |- ( ( R C_ ( C X. D ) /\ A R B ) -> ( A e. C /\ B e. D ) ) $=
    ( cxp wss wbr wa wcel ssbr imp brxp sylib ) ECDFZGZABEHZIABOHZACJBDJIPQREOA
    BKLABCDMN $.

  ${
    $d a b c d e f g h p q A $.  $d a b c d e f g h p q B $.
    $d a b c d e f g h p q C $.  $d a b c d e f g h p q D $.
    $d a b c d e f g h p q E $.  $d a b c d e f g h p q F $.
    $d a b c d e f g h p q G $.  $d a b c d e f g h p q H $.
    $d a b c d e f g h p q P $.  $d a ch $.  $d b th $.  $d c ta $.  $d d et $.
    $d e ze $.  $d f si $.  $d g rh $.  $d p q ps $.  $d a b c d e f g h mu $.
    br8d.1 $e |- ( a = A -> ( ps <-> ch ) ) $.
    br8d.2 $e |- ( b = B -> ( ch <-> th ) ) $.
    br8d.3 $e |- ( c = C -> ( th <-> ta ) ) $.
    br8d.4 $e |- ( d = D -> ( ta <-> et ) ) $.
    br8d.5 $e |- ( e = E -> ( et <-> ze ) ) $.
    br8d.6 $e |- ( f = F -> ( ze <-> si ) ) $.
    br8d.7 $e |- ( g = G -> ( si <-> rh ) ) $.
    br8d.8 $e |- ( h = H -> ( rh <-> mu ) ) $.
    br8d.10 $e |- ( ph -> R = { <. p , q >. |
       E. a e. P E. b e. P E. c e. P E. d e. P E. e e. P
       E. f e. P E. g e. P E. h e. P ( p = <. <. a , b >. , <. c , d >. >. /\
       q = <. <. e , f >. , <. g , h >. >. /\ ps ) } ) $.
    br8d.11 $e |- ( ph -> A e. P ) $.
    br8d.12 $e |- ( ph -> B e. P ) $.
    br8d.13 $e |- ( ph -> C e. P ) $.
    br8d.14 $e |- ( ph -> D e. P ) $.
    br8d.15 $e |- ( ph -> E e. P ) $.
    br8d.16 $e |- ( ph -> F e. P ) $.
    br8d.17 $e |- ( ph -> G e. P ) $.
    br8d.18 $e |- ( ph -> H e. P ) $.
    $( Substitution for an eight-place predicate.  (Contributed by Scott
       Fenton, 26-Sep-2013.)  (Revised by Mario Carneiro, 3-May-2015.)
       (Revised by Thierry Arnoux, 21-Mar-2019.) $)
    br8d $p |- ( ph ->
      ( <. <. A , B >. , <. C , D >. >. R <. <. E , F >. , <. G , H >. >. <->
        mu ) ) $=
      ( cop wbr cv wceq w3a wrex copab breqd opex eqeq1 3anbi1d rexbidv 3anbi2d
      2rexbidv eqid brab bitrdi wcel wb wa wi vex sylan9bb sylbi eqcoms biimp3a
      opth rexlimdva rexlimdvva simpl1l simpl1r simpl21 simpl22 simpl23 simpl31
      simpl32 simpl33 eqidd simpr opeq1 opeq2d 3anbi23d opeq2 rspc2ev syl113anc
      a1i eqeq2d 3anbi13d opeq1d rspc3ev syl31anc ex impbid syl233anc bitrd ) A
      KLVHZMNVHZVHZUAUBVHZUCUDVHZVHZPVIZYEUGVJZUHVJZVHZUIVJZUJVJZVHZVHZVKZYHQVJ
      ZRVJZVHZSVJZTVJZVHZVHZVKZBVLZTOVMZSOVMROVMZQOVMUJOVMZUIOVMUHOVMZUGOVMZJAY
      IYEYHUFVJZYPVKZUEVJZUUDVKZBVLZTOVMZSOVMROVMZQOVMUJOVMZUIOVMUHOVMZUGOVMZUF
      UEVNZVIUUKAPUVBYEYHUSVOUVAYQUUOBVLZTOVMZSOVMROVMZQOVMUJOVMZUIOVMUHOVMZUGO
      VMUUKUFUEYEYHUVBYCYDVPYFYGVPUULYEVKZUUTUVGUGOUVHUUSUVFUHUIOOUVHUURUVEUJQO
      OUVHUUQUVDRSOOUVHUUPUVCTOUVHUUMYQUUOBUULYEYPVQVRVSWAWAWAVSUUNYHVKZUVGUUJU
      GOUVIUVFUUIUHUIOOUVIUVEUUHUJQOOUVIUVDUUGRSOOUVIUVCUUFTOUVIUUOUUEYQBUUNYHU
      UDVQVTVSWAWAWAVSUVBWBWCWDAKOWEZLOWEZMOWEZNOWEZUAOWEZUBOWEZUCOWEZUDOWEZUUK
      JWFUTVAVBVCVDVEVFVGUVJUVKWGZUVLUVMUVNVLZUVOUVPUVQVLZVLZUUKJUWAUUJJUGOUWAY
      JOWEWGZUUIJUHUIOOUWBYKOWEYMOWEWGWGZUUHJUJQOOUWCYNOWEYROWEWGWGZUUGJRSOOUWD
      YSOWEUUAOWEWGWGZUUFJTOUUFJWHUWEUUBOWEWGYQUUEBJYQBFUUEJBFWFZYPYEYPYEVKYLYC
      VKZYOYDVKZWGUWFYLYOYCYDYJYKVPYMYNVPWNUWGBDUWHFUWGYJKVKZYKLVKZWGBDWFYJYKKL
      UGWIUHWIWNUWIBCUWJDUKULWJWKUWHYMMVKZYNNVKZWGDFWFYMYNMNUIWIUJWIWNUWKDEUWLF
      UMUNWJWKWJWKWLFJWFZUUDYHUUDYHVKYTYFVKZUUCYGVKZWGUWMYTUUCYFYGYRYSVPUUAUUBV
      PWNUWNFHUWOJUWNYRUAVKZYSUBVKZWGFHWFYRYSUAUBQWIRWIWNUWPFGUWQHUOUPWJWKUWOUU
      AUCVKZUUBUDVKZWGHJWFUUAUUBUCUDSWITWIWNUWRHIUWSJUQURWJWKWJWKWLWJWMXMWOWPWP
      WPWOUWAJUUKUWAJWGZUVJUVKUVLYEYCMYNVHZVHZVKZUUEEVLZTOVMZSOVMZROVMZQOVMUJOV
      MZUUKUVJUVKUVSUVTJWQUVJUVKUVSUVTJWRUVLUVMUVNUVRUVTJWSUWTUVMUVNUVOYEYEVKZY
      HYFUUCVHZVKZHVLZTOVMSOVMZUXHUVLUVMUVNUVRUVTJWTUVLUVMUVNUVRUVTJXAUVOUVPUVQ
      UVRUVSJXBUWTUVPUVQUXIYHYHVKZJUXMUVOUVPUVQUVRUVSJXCUVOUVPUVQUVRUVSJXDUWTYE
      XEUWTYHXEUWAJXFUXLUXIUXNJVLUXIYHYFUCUUBVHZVHZVKZIVLSTUCUDOOUWRUXKUXQHIUXI
      UWRUXJUXPYHUWRUUCUXOYFUUAUCUUBXGXHXNUQXIUWSUXQUXNIJUXIUWSUXPYHYHUWSUXOYGY
      FUUBUDUCXJXHXNURXIXKXLUXFUXMUXIUUEFVLZTOVMSOVMUXIYHUAYSVHZUUCVHZVKZGVLZTO
      VMSOVMUJQRNUAUBOOOUWLUXDUXRSTOOUWLUXCUXIEFUUEUWLUXBYEYEUWLUXAYDYCYNNMXJXH
      XNUNXOWAUWPUXRUYBSTOOUWPUUEUYAFGUXIUWPUUDUXTYHUWPYTUXSUUCYRUAYSXGXPXNUOXI
      WAUWQUYBUXLSTOOUWQUYAUXKGHUXIUWQUXTUXJYHUWQUXSYFUUCYSUBUAXJXPXNUPXIWAXQXR
      UUIUXHYEKYKVHZYOVHZVKZUUECVLZTOVMZSOVMROVMZQOVMUJOVMYEYCYOVHZVKZUUEDVLZTO
      VMZSOVMROVMZQOVMUJOVMUGUHUIKLMOOOUWIUUHUYHUJQOOUWIUUGUYGRSOOUWIUUFUYFTOUW
      IYQUYEBCUUEUWIYPUYDYEUWIYLUYCYOYJKYKXGXPXNUKXOVSWAWAUWJUYHUYMUJQOOUWJUYGU
      YLRSOOUWJUYFUYKTOUWJUYEUYJCDUUEUWJUYDUYIYEUWJUYCYCYOYKLKXJXPXNULXOVSWAWAU
      WKUYMUXGUJQOOUWKUYLUXERSOOUWKUYKUXDTOUWKUYJUXCDEUUEUWKUYIUXBYEUWKYOUXAYCY
      MMYNXGXHXNUMXOVSWAWAXQXRXSXTYAYB $.
  $}

  ${
    $d A x $.  $d F x $.  $d G x $.  $d R x $.  $d X x $.  $d ph x $.
    fnfvor.1 $e |- ( ph -> F Fn A ) $.
    fnfvor.2 $e |- ( ph -> G Fn A ) $.
    fnfvor.3 $e |- ( ph -> A e. V ) $.
    fnfvor.4 $e |- ( ph -> F oR R G ) $.
    fnfvor.5 $e |- ( ph -> X e. A ) $.
    $( Relation between two functions implies the same relation for the
       function value at a given ` X ` .  See also ~ fnfvof .  (Contributed by
       Thierry Arnoux, 15-Jan-2026.) $)
    fnfvor $p |- ( ph -> ( F ` X ) R ( G ` X ) ) $=
      ( vx cv cfv wbr wceq fveq2 breq12d eqidd cofr wral inidm wa ofrfval mpbid
      wcel rspcdva ) AMNZDOZUIEOZCPZGDOZGEOZCPMBGUIGQUJUMUKUNCUIGDRUIGERSADECUA
      PULMBUBKAMBBUJUKCBDEFFHIJJBUCAUIBUGUDZUJTUOUKTUEUFLUH $.
  $}

  ${
    $d A x y $.  $d C x $.  $d F x y $.  $d G x y $.  $d H x y $.  $d R x y $.
    $d ph x y $.
    ofrco.1 $e |- ( ph -> F Fn A ) $.
    ofrco.2 $e |- ( ph -> G Fn A ) $.
    ofrco.3 $e |- ( ph -> H : C --> A ) $.
    ofrco.4 $e |- ( ph -> A e. V ) $.
    ofrco.5 $e |- ( ph -> C e. W ) $.
    ofrco.6 $e |- ( ph -> F oR R G ) $.
    $( Function relation between function compositions.  (Contributed by
       Thierry Arnoux, 15-Jan-2026.) $)
    ofrco $p |- ( ph -> ( F o. H ) oR R ( G o. H ) ) $=
      ( vx vy wbr cfv wfn ccom cofr cv wral wcel wceq fveq2 breq12d inidm eqidd
      wa ofrfval mpbid adantr ffvelcdmda rspcdva ralrimiva fnfco syl2anc fvco3d
      wf simpr mpbird ) AEGUAZFGUAZDUBZRPUCZGSZESZVHFSZDRZPCUDAVKPCAVGCUEZUKZQU
      CZESZVNFSZDRZVKQBVHVNVHUFVOVIVPVJDVNVHEUGVNVHFUGUHAVQQBUDZVLAEFVFRVROAQBB
      VOVPDBEFHHJKMMBUIAVNBUEUKZVOUJVSVPUJULUMUNACBVGGLUOUPUQAPCCVIVJDCVDVEIIAE
      BTCBGVAZVDCTJLBCEGURUSAFBTVTVECTKLBCFGURUSNNCUIVMCBVGEGAVTVLLUNZAVLVBZUTV
      MCBVGFGWAWBUTULVC $.
  $}

  ${
    $d x y R $.
    $( Domain of an ordered-pair class abstraction.  (Contributed by Thierry
       Arnoux, 31-Aug-2017.) $)
    opabdm $p |- ( R = { <. x , y >. | ph } -> dom R = { x | E. y ph } ) $=
      ( copab wceq cdm wbr wex cab df-dm nfopab1 nfeq2 nfopab2 wcel df-br eleq2
      cv cop opabidw bitrdi bitrid exbid abbid eqtrid ) DABCEZFZDGBRZCRZDHZCIZB
      JACIZBJBCDKUGUKULBBDUFABCLMUGUJACCDUFABCNMUJUHUISZDOZUGAUHUIDPUGUNUMUFOAD
      UFUMQABCTUAUBUCUDUE $.

    $( Range of an ordered-pair class abstraction.  (Contributed by Thierry
       Arnoux, 31-Aug-2017.) $)
    opabrn $p |- ( R = { <. x , y >. | ph } -> ran R = { y | E. x ph } ) $=
      ( copab wceq crn wbr wex cab dfrn2 nfopab2 nfeq2 nfopab1 wcel df-br eleq2
      cv cop opabidw bitrdi bitrid exbid abbid eqtrid ) DABCEZFZDGBRZCRZDHZBIZC
      JABIZCJBCDKUGUKULCCDUFABCLMUGUJABBDUFABCNMUJUHUISZDOZUGAUHUIDPUGUNUMUFOAD
      UFUMQABCTUAUBUCUDUE $.
  $}

  ${
    $d A x y z $.  $d ph z $.
    opabssi.1 $e |- ( ph -> <. x , y >. e. A ) $.
    $( Sufficient condition for a collection of ordered pairs to be a subclass
       of a relation.  (Contributed by Peter Mazsa, 21-Oct-2019.)  (Revised by
       Thierry Arnoux, 18-Feb-2022.) $)
    opabssi $p |- { <. x , y >. | ph } C_ A $=
      ( vz copab cv cop wceq wa wex cab df-opab wcel eleq1 impel exlimivv abssi
      biimprd eqsstri ) ABCGFHZBHCHIZJZAKZCLBLZFMDABCFNUFFDUEUBDOZBCUDUCDOZUGAU
      DUGUHUBUCDPTEQRSUA $.
  $}

  ${
    $d A x y $.
    $( One direction of ~ opabid2 which holds without a ` Rel A ` requirement.
       (Contributed by Thierry Arnoux, 18-Feb-2022.) $)
    opabid2ss $p |- { <. x , y >. | <. x , y >. e. A } C_ A $=
      ( cv cop wcel id opabssi ) ADBDECFZABCIGH $.
  $}

  ${
    $d x y z $.  $d z A $.  $d z B $.
    eqrelrd2.1 $e |- F/ x ph $.
    eqrelrd2.2 $e |- F/ y ph $.
    eqrelrd2.3 $e |- F/_ x A $.
    eqrelrd2.4 $e |- F/_ y A $.
    eqrelrd2.5 $e |- F/_ x B $.
    eqrelrd2.6 $e |- F/_ y B $.
    $( A subclass relationship depends only on a relation's ordered pairs.
       Theorem 3.2(i) of [Monk1] p. 33.  (Contributed by NM, 2-Aug-1994.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.)  (Revised by Thierry
       Arnoux, 6-Nov-2017.) $)
    ssrelf $p |- ( Rel A -> ( A C_ B <->
                A. x A. y ( <. x , y >. e. A -> <. x , y >. e. B ) ) ) $=
      ( vz wss cv wcel wi wal nfss alrimi nfcri wrel cop ssel wex eleq1 imbi12d
      wceq biimprcd 2alimi nfim 19.23 albii bitri sylib com23 a2d alimdv df-rel
      cvv cxp df-ss elvv imbi2i 3bitri 3imtr4g com12 impbid2 ) DUAZDEMZBNCNUBZD
      OZVJEOZPZCQZBQZVIVNBBDEHJRVIVMCCDEIKRDEVJUCSSVOVHVIVOLNZDOZVPVJUGZCUDZBUD
      ZPZLQZVQVPEOZPZLQVHVIVOWAWDLVOVQVTWCVOVTVQWCVOVRWDPZCQZBQZVTWDPZVMWEBCVRW
      DVMVRVQVKWCVLVPVJDUEVPVJEUEUFUHUIWGVSWDPZBQWHWFWIBVRWDCVQWCCCLDITCLEKTUJU
      KULVSWDBVQWCBBLDHTBLEJTUJUKUMUNUOUPUQVHDUSUSUTZMVQVPWJOZPZLQWBDURLDWJVAWL
      WALWKVTVQBCVPVBVCULVDLDEVAVEVFVG $.

    eqrelrd2.7 $e |- ( ph -> ( <. x , y >. e. A <-> <. x , y >. e. B ) ) $.
    $( A version of ~ eqrelrdv2 with explicit nonfree declarations.
       (Contributed by Thierry Arnoux, 28-Aug-2017.) $)
    eqrelrd2 $p |- ( ( ( Rel A /\ Rel B ) /\ ph ) -> A = B ) $=
      ( wrel wa cv wcel wb wal alrimi wss cop adantl wi ssrelf bi2anan9 2albiim
      wceq eqss 3bitr4g adantr mpbird ) DMZEMZNZANDEUGZBOCOUAZDPZUPEPZQZCRZBRZA
      VAUNAUTBFAUSCGLSSUBUNUOVAQAUNDETZEDTZNUQURUCCRBRZURUQUCCRBRZNUOVAULVBVDUM
      VCVEABCDEFGHIJKUDABCEDFGJKHIUDUEDEUHUQURBCUFUIUJUK $.
  $}

  $( Biconditional for equivalent elements.  (Contributed by Thierry Arnoux,
     6-Jan-2020.) $)
  erbr3b $p |- ( ( R Er X /\ A R B ) -> ( A R C <-> B R C ) ) $=
    ( wer wbr wa simpll simplr simpr ertr3d ertrd impbida ) EDFZABDGZHZACDGZBCD
    GZQRHBACDEOPRIOPRJQRKLQSHABCDEOPSIOPSJQSKMN $.

  ${
    $d A y $.  $d B y $.  $d ph y $.  $d x y $.
    iunsnima.1 $e |- ( ph -> A e. V ) $.
    iunsnima.2 $e |- ( ( ph /\ x e. A ) -> B e. W ) $.
    $( Image of a singleton by an indexed union involving that singleton.
       (Contributed by Thierry Arnoux, 10-Apr-2020.) $)
    iunsnima $p |- ( ( ph /\ x e. A )
      -> ( U_ x e. A ( { x } X. B ) " { x } ) = B ) $=
      ( vy cv wcel wa csn cxp ciun cima cop vex elimasn wb opeliunxp baib eqrdv
      adantl bitrid ) ABJZCKZLZIBCUFMZDNOZUIPZDIJZUKKUFULQUJKZUHULDKZUJUFULBRIR
      SUGUMUNTAUMUGUNBCDULUAUBUDUEUC $.

    $d A x z $.  $d B z $.  $d C z $.  $d Y x z $.  $d ph z $.
    iunsnima2.1 $e |- F/_ x C $.
    iunsnima2.2 $e |- ( x = Y -> B = C ) $.
    $( Version of ~ iunsnima with different variables.  (Contributed by Thierry
       Arnoux, 22-Jun-2024.) $)
    iunsnima2 $p |- ( ( ph /\ Y e. A )
                   -> ( U_ x e. A ( { x } X. B ) " { Y } ) = C ) $=
      ( vz wcel wa cv csn cxp wb adantl ciun cima cop elimasng elvd opeliunxp2f
      cvv baib bitrd eqrdv ) AHCNZOZMBCBPQDRUAZHQUBZEULMPZUNNZHUOUCUMNZUOENZUKU
      PUQSZAUKUSMUMHUOCUGUDUETUKUQURSAUQUKURBCDHUOEKLUFUHTUIUJ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Functions - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x $.  $d B x $.  $d F x $.  $d ph x $.
    fconst7v.f $e |- ( ph -> F Fn A ) $.
    fconst7v.e $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = B ) $.
    $( An alternative way to express a constant function.  (Contributed by
       Glauco Siliprandi, 5-Feb-2022.)  Removed hyphotheses as suggested by SN
       (Revised by Thierry Arnoux, 10-Jan-2026.) $)
    fconst7v $p |- ( ph -> F = ( A X. { B } ) ) $=
      ( c0 wceq cxp wa a1i simpr wfn adantr wb mpbid wcel cvv nfcv xpeq1d fneq2
      csn wne 0xp adantl fn0 sylib 3eqtr4rd wf cv cfv wral fvexd eqeltrrd snidg
      syl eqeltrd ralrimiva ffnfvf sylanbrc adantlr n0limd fconst2g wo mpjaodan
      exmidne ) ACHIZECDUCZJZIZCHUDZAVHKZHVIJZHVJEVNHIVMVIUELVMCHVIAVHMUAVMEHNZ
      EHIVMECNZVOAVPVHFOVHVPVOPACHEUBUFQEUGUHUIAVLKZCVIEUJZVKAVRVLAVPBUKZEULZVI
      RZBCUMVRFAWABCAVSCRZKZVTDVIGWCDSRZDVIRWCVTDSGWCVSEUNUOZDSUPUQURUSBCVIEBCT
      BVITBETUTVAOVQWDVRVKPVQWDBCAVLMAWBWDVLWEVBVCCDSEVDUQQVHVLVEACHVGLVF $.
  $}

  ${
    $d F x $.  $d I x $.  $d X x $.  $d Y x $.  $d ph x $.
    constcof.1 $e |- ( ph -> F : X --> I ) $.
    constcof.2 $e |- ( ph -> Y e. V ) $.
    $( Composition with a constant function.  See also ~ fcoconst .
       (Contributed by Thierry Arnoux, 11-Jan-2026.) $)
    constcof $p |- ( ph -> ( ( I X. { Y } ) o. F ) = ( X X. { Y } ) ) $=
      ( vx csn cxp ccom wfn wf wcel fnconstg syl syl2anc cfv adantr fnfco cv wa
      simpr fvco3d wceq ffvelcdmda fvconst2g eqtrd fconst7v ) AIEFCFJKZBLZAUKCM
      ZECBNZULEMAFDOZUMHCFDPQGCEUKBUARAIUBZEOZUCZUPULSUPBSZUKSZFURECUPUKBAUNUQG
      TAUQUDUEURUOUSCOUTFUFAUOUQHTAECUPBGUGCFUSDUHRUIUJ $.
  $}

  ${
    $d f x z A $.  $d x f z B $.  $d f z ph $.  $d z ps $.  $d x y f z $.
    ac6sf2.y $e |- F/_ y B $.
    ac6sf2.1 $e |- F/ y ps $.
    ac6sf2.2 $e |- A e. _V $.
    ac6sf2.3 $e |- ( y = ( f ` x ) -> ( ph <-> ps ) ) $.
    $( Alternate version of ~ ac6 with bound-variable hypothesis.  (Contributed
       by NM, 2-Mar-2008.)  (Revised by Thierry Arnoux, 17-May-2020.) $)
    ac6sf2 $p |- ( A. x e. A E. y e. B ph ->
                E. f ( f : A --> B /\ A. x e. A ps ) ) $=
      ( vz wrex wral wsb cv wf wa wex nfcv nfs1v sbequ12 cbvrexfw ralbii sbhypf
      nfv cfv ac6s sylbi ) ADFMZCENADLOZLFMZCENEFGPZQBCENRGSUJULCEAUKDLFHLFTALU
      FADLUAADLUBUCUDUKBCLEFGJABDLCPUMUGIKUEUHUI $.
  $}

  ${
    $d A f x $.  $d B f x y $.  $d ch y $.  $d f ph x $.  $d f ps $.
    ac6mapd.1 $e |- ( y = ( f ` x ) -> ( ps <-> ch ) ) $.
    ac6mapd.2 $e |- ( ph -> A e. V ) $.
    ac6mapd.3 $e |- ( ph -> B e. W ) $.
    ac6mapd.4 $e |- ( ( ph /\ x e. A ) -> E. y e. B ps ) $.
    $( Axiom of choice equivalent, deduction form.  (Contributed by Thierry
       Arnoux, 13-Oct-2025.) $)
    ac6mapd $p |- ( ph -> E. f e. ( B ^m A ) A. x e. A ch ) $=
      ( cv wcel wral wa wex wrex cmap co wf ralrimiva ac6sg sylc elmapd biimprd
      anim1d eximdv mpd df-rex sylibr ) AHOZGFUAUBZPZCDFQZRZHSZUQHUOTAFGUNUCZUQ
      RZHSZUSAFIPBEGTZDFQVBLAVCDFNUDBCDEFGHIKUEUFAVAURHAUTUPUQAUPUTAGFUNJIMLUGU
      HUIUJUKUQHUOULUM $.
  $}

  $( Restriction of a function with a subclass of its domain.  (Contributed by
     Thierry Arnoux, 10-Oct-2017.) $)
  fnresin $p |- ( F Fn A -> ( F |` B ) Fn ( A i^i B ) ) $=
    ( wfn cin cres fnresin1 resindi fnresdm ineq1d incom wss resss dfss2 eqtr3i
    wceq mpbi eqtrdi eqtrid fneq1d mpbid ) CADZCABEZFZUCDCBFZUCDABCGUBUCUDUEUBU
    DCAFZUEEZUECABHUBUGCUEEZUEUBUFCUEACIJUECEZUHUEUECKUECLUIUEPCBMUECNQORSTUA
    $.

  $( Recover the original function from a point-added function.  See also
     ~ funresdfunsn and ~ fsnunres .  (Contributed by Thierry Arnoux,
     15-Feb-2026.) $)
  fresunsn $p |- ( ( F Fn A /\ X e. A /\ ( F ` X ) = Y )
                -> ( ( F |` ( A \ { X } ) ) u. { <. X , Y >. } ) = F ) $=
    ( wfn wcel cfv wceq w3a csn cdif cop cun cvv cdm resdmdfsn 3ad2ant1 difeq1d
    cres fndm reseq2d eqtr2id simp3 eqcomd opeq2d sneqd uneq12d biimpar 3adant3
    wfun fnfun eleq2d funresdfunsn syl2anc eqtrd ) BAEZCAFZCBGZDHZIZBACJZKZSZCD
    LZJZMBNVAKSZCURLZJZMZBUTVCVFVEVHUTVFBBOZVAKZSVCBCPUTVKVBBUTVJAVAUPUQVJAHUSA
    BTZQRUAUBUTVDVGUTDURCUTURDUPUQUSUCUDUEUFUGUTBUJZCVJFZVIBHUPUQVMUSABUKQUPUQV
    NUSUPVNUQUPVJACVLULUHUIBCUMUNUO $.

  ${
    $d x y A $.  $d x y B $.  $d y C $.  $d x D $.  $d x y ph $.
    f1o3d.1 $e |- ( ph -> F = ( x e. A |-> C ) ) $.
    f1o3d.2 $e |- ( ( ph /\ x e. A ) -> C e. B ) $.
    f1o3d.3 $e |- ( ( ph /\ y e. B ) -> D e. A ) $.
    f1o3d.4 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) ->
                    ( x = D <-> y = C ) ) $.
    $( Describe an implicit one-to-one onto function.  (Contributed by Thierry
       Arnoux, 23-Apr-2017.) $)
    f1o3d $p |- ( ph -> ( F : A -1-1-onto-> B /\ `' F = ( y e. B |-> D ) ) ) $=
      ( ccnv wceq wfn wcel syl wa copab wi wf1o cmpt wral ralrimiva eqid fneq1d
      fnmpt mpbird cv eleq1a impr biimpar exp42 com34 imp32 jcai biimpa impbida
      com23 opabbidv df-mpt eqtrdi cnveqd cnvopab a1i 3eqtr4d dff1o4 sylanbrc
      jca ) ADEHUAZHMZCEGUBZNAHDOZVKEOZVJAVMBDFUBZDOZAFEPZBDUCVPAVQBDJUDBDFVOEV
      OUEUGQADHVOIUFUHAVNVLEOZAGDPZCEUCVRAVSCEKUDCEGVLDVLUEUGQAEVKVLABUIZDPZCUI
      ZFNZRZCBSZWBEPZVTGNZRZCBSZVKVLAWDWHCBAWDWHAWDRWFWGAWAWCWFAWARVQWCWFTJFEWB
      UJQUKAWAWCWFWGTAWAWFWCWGAWAWFWCWGAWAWFRRZWGWCLULUMUNUOUPAWHRWAWCAWFWGWAAW
      FRVSWGWATKGDVTUJQUKAWFWGWAWCTAWFWAWGWCAWAWFWGWCTAWAWFWGWCWJWGWCLUQUMUSUNU
      OUPURUTAVKWDBCSZMWEAHWKAHVOWKIBCDFVAVBVCWDBCVDVBVLWINACBEGVAVEVFZUFUHDEHV
      GVHWLVI $.
  $}

  $( A function of nonempty domain is not empty.  (Contributed by Thierry
     Arnoux, 20-Nov-2023.) $)
  eldmne0 $p |- ( X e. dom F -> F =/= (/) ) $=
    ( cdm wcel c0 wne ne0i wceq dmeq dm0 eqtrdi necon3i syl ) BACZDNEFAEFNBGAEN
    EAEHNECEAEIJKLM $.

  $( Equinumerosity of the range of an injective function.  (Contributed by
     Thierry Arnoux, 7-Jul-2023.) $)
  f1rnen $p |- ( ( F : A -1-1-> B /\ A e. V ) -> ran F ~~ A ) $=
    ( wf1 wcel wa cima crn cen wfn wceq f1fn adantr fnima syl wss ssid f1imaeng
    wbr mp3an2 eqbrtrrd ) ABCEZADFZGZCAHZCIZAJUECAKZUFUGLUCUHUDABCMNACOPUCAAQUD
    UFAJTARABACDSUAUB $.

  ${
    f1oeq3dd.1 $e |- ( ph -> F : C -1-1-onto-> A ) $.
    f1oeq3dd.2 $e |- ( ph -> A = B ) $.
    $( Equality deduction for one-to-one onto functions.  (Contributed by
       Thierry Arnoux, 10-Jan-2026.) $)
    f1oeq3dd $p |- ( ph -> F : C -1-1-onto-> B ) $=
      ( wf1o f1oeq3d mpbid ) ADBEHDCEHFABCDEGIJ $.
  $}

  ${
    rinvbij.1 $e |- Fun F $.
    rinvbij.2 $e |- `' F = F $.
    rinvbij.3a $e |- ( F " A ) C_ B $.
    rinvbij.3b $e |- ( F " B ) C_ A $.
    rinvbij.4a $e |- A C_ dom F $.
    rinvbij.4b $e |- B C_ dom F $.
    $( Sufficient conditions for the restriction of an involution to be a
       bijection.  (Contributed by Thierry Arnoux, 7-Dec-2016.) $)
    rinvf1o $p |- ( F |` A ) : A -1-1-onto-> B $=
      ( cima cres wf1o cdm crn wf1 wss wfun mpbi mp2an wb wf fdmrn funeqi mpbir
      ccnv df-f1 mpbir2an f1ores funimass3 imaeq1i sseqtri eqssi f1oeq3 ax-mp
      wceq ) ACAJZCAKZLZABUQLZCMZCNZCOZAUTPURVBUTVACUAZCUEZQZCQZVCDCUBRVEVFDVDC
      EUCUDUTVACUFUGHUTVAACUHSUPBUOURUSTUPBFBVDAJZUPCBJAPZBVGPZGVFBUTPVHVITDIBA
      CUISRVDCAEUJUKULUPBAUQUMUNR $.
  $}

  $( Conditions for a restriction to be a one-to-one onto function.
     (Contributed by Thierry Arnoux, 7-Dec-2016.) $)
  fresf1o $p |- ( ( Fun F /\ C C_ ran F /\ Fun ( `' F |` C ) )
    -> ( F |` ( `' F " C ) ) : ( `' F " C ) -1-1-onto-> C ) $=
    ( wfun crn wss ccnv cres w3a cima wf1o wfn wceq funfn biimpi 3ad2ant3 simp2
    cdm df-rn mpbid syl sseqtrdi ssdmres sylib fneq2d funresd funcnvres2 funeqd
    simp1 mpbird df-ima eqcomi a1i dff1o2 syl3anbrc f1ocnv wb f1oeq1 3syl ) BCZ
    ABDZEZBFZAGZCZHZVBAIZAVCFZJZVFABVFGZJZVEAVFVCJZVHVEVCAKZVGCZVCDZVFLZVKVEVCV
    CQZKZVLVDUSVQVAVDVQVCMNOVEVPAVCVEAVBQZEVPALVEAUTVRUSVAVDPBRUAAVBUBUCUDSVEVM
    VICVEVFBUSVAVDUHZUEVEVGVIVEUSVGVILZVSABUFZTUGUIVOVEVFVNVBAUJUKULAVFVCUMUNAV
    FVCUOTVEUSVTVHVJUPVSWAVFAVGVIUQURS $.

  ${
    $d A x $.  $d F x $.
    $( The set of fixed points of ` F ` is the complement of the set of points
       moved by ` F ` .  (Contributed by Thierry Arnoux, 17-Nov-2023.) $)
    nfpconfp $p |- ( F Fn A -> ( A \ dom ( F \ _I ) ) = dom ( F i^i _I ) ) $=
      ( vx wfn cid cdif cdm cin cv wcel wn eldif cfv wceq fnelfp pm5.32da inss1
      wa wss dmss ax-mp sseqtrid sseld pm4.71rd wne fnelnfp notbid nne 3bitr4rd
      fndm bitrdi bitrid eqrdv ) BADZCABEFGZFZBEHZGZCIZUPJUSAJZUSUOJZKZRZUNUSUR
      JZUSAUOLUNUTVDRUTUSBMZUSNZRVDVCUNUTVDVFABUSOPUNVDUTUNURAUSUNBGZURAUQBSURV
      GSBEQUQBTUAABUJUBUCUDUNUTVBVFUNUTRZVBVEUSUEZKVFVHVAVIABUSUFUGVEUSUHUKPUIU
      LUM $.
  $}

  ${
    $d A f g $.  $d B f g $.  $d T f g $.  $d f g ph $.
    fmptco1f1o.a $e |- A = ( R ^m E ) $.
    fmptco1f1o.b $e |- B = ( R ^m D ) $.
    fmptco1f1o.f $e |- F = ( f e. A |-> ( f o. T ) ) $.
    fmptco1f1o.d $e |- ( ph -> D e. V ) $.
    fmptco1f1o.e $e |- ( ph -> E e. W ) $.
    fmptco1f1o.r $e |- ( ph -> R e. X ) $.
    fmptco1f1o.t $e |- ( ph -> T : D -1-1-onto-> E ) $.
    $( The action of composing (to the right) with a bijection is itself a
       bijection of functions.  (Contributed by Thierry Arnoux, 3-Jan-2021.) $)
    fmptco1f1o $p |- ( ph -> F : A -1-1-onto-> B ) $=
      ( wcel vg wf1o ccnv cv ccom cmpt wceq wa cmap co wf adantr simpr eleqtrdi
      a1i elmapi syl f1of syl2anc elmapg biimpar syl21anc eleqtrrdi f1ocnv 3syl
      fco coass cid cres ad2antrr f1ococnv1 coeq2d adantlr fcoi1 eqtr2id eqeq1d
      wb eqtrd eqcom wfo wfn f1ofo simplr elmapfn cocan2 syl3anc 3bitrrd anasss
      f1o3d simpld ) ABCIUBIUCUACUAUDZFUCZUEZUFUGAGUABCGUDZFUEZWMIIGBWOUFUGAOUO
      AWNBTZUHZWOEDUIUJZCWQELTZDJTZDEWOUKZWOWRTZAWSWPRULAWTWPPULWQHEWNUKZDHFUKZ
      XAWQWNEHUIUJZTZXCWQWNBXEAWPUMMUNWNEHUPUQAXDWPADHFUBZXDSDHFURUQULDHEWNFVFU
      SWSWTUHXBXAEDWOLJUTVAVBNVCAWKCTZUHZWMXEBXIWSHKTZHEWMUKZWMXETZAWSXHRULAXJX
      HQULXIDEWKUKZHDWLUKZXKXIWKWRTXMXIWKCWRAXHUMNUNWKEDUPUQZAXNXHAXGHDWLUBXNSD
      HFVDHDWLURVEULHDEWKWLVFUSWSXJUHXLXKEHWMLKUTVAVBZMVCAWPXHWNWMUGZWKWOUGZVQW
      QXHUHZXRWMFUEZWOUGZWOXTUGZXQXSWKXTWOXSXTWKWLFUEZUEZWKWKWLFVGXSYDWKVHDVIZU
      EZWKXSXGYDYFUGAXGWPXHSVJZXGYCYEWKDHFVKVLUQXSXMYFWKUGAXHXMWPXOVMDEWKVNUQVR
      VOVPYAYBVQXSXTWOVSUOXSDHFVTZWNHWAZWMHWAZYBXQVQXSXGYHYGDHFWBUQXSXFYIXSWNBX
      EAWPXHWCMUNWNEHWDUQAXHYJWPXIXLYJXPWMEHWDUQVMDHFWNWMWEWFWGWHWIWJ $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d C x $.  $d D y $.  $d E x y $.  $d F x y $.
    $d ph x y $.
    cofmpt2.1 $e |- ( ( ph /\ y = ( F ` x ) ) -> C = D ) $.
    cofmpt2.2 $e |- ( ( ph /\ y e. B ) -> C e. E ) $.
    cofmpt2.3 $e |- ( ph -> F : A --> B ) $.
    cofmpt2.4 $e |- ( ph -> D e. V ) $.
    $( Express composition of a maps-to function with another function in a
       maps-to notation.  (Contributed by Thierry Arnoux, 15-Jul-2023.) $)
    cofmpt2 $p |- ( ph -> ( ( y e. B |-> C ) o. F ) = ( x e. A |-> D ) ) $=
      ( cmpt cv cfv wf wceq wcel ccom fmpttd syl2anc wa eqid adantlr ffvelcdmda
      fcompt adantr fvmptd2 mpteq2dva eqtrd ) ACEFOZIUAZBDBPZIQZUMQZOZBDGOAEHUM
      RDEIRUNURSACEFHLUBMBUMIDEHUHUCABDUQGAUODTZUDCUPFGEUMJUMUEACPUPSFGSUSKUFAD
      EUOIMUGAGJTUSNUIUJUKUL $.
  $}

  ${
    $d A x y $.  $d B y $.  $d C x y $.  $d ph x y $.
    f1mptrn.1 $e |- ( ( ph /\ x e. A ) -> B e. C ) $.
    f1mptrn.2 $e |- ( ( ph /\ y e. C ) -> E! x e. A y = B ) $.
    $( Express injection for a mapping operation.  (Contributed by Thierry
       Arnoux, 3-May-2020.) $)
    f1mptrn $p |- ( ph -> Fun `' ( x e. A |-> B ) ) $=
      ( wcel wral cv wceq wreu cmpt ccnv wfun ralrimiva wa wf1o eqid f1ompt wfn
      crn dff1o2 simp2bi sylbir syl2anc ) AEFIZBDJZCKELBDMZCFJZBDENZOPZAUHBDGQA
      UJCFHQUIUKRDFULSZUMBCDFEULULTUAUNULDUBUMULUCFLDFULUDUEUFUG $.
  $}

  ${
    $d x y z $.  $d y z A $.  $d y z F $.
    dfimafnf.1 $e |- F/_ x A $.
    dfimafnf.2 $e |- F/_ x F $.
    $( Alternate definition of the image of a function.  (Contributed by Raph
       Levien, 20-Nov-2006.)  (Revised by Thierry Arnoux, 24-Apr-2017.) $)
    dfimafnf $p |- ( ( Fun F /\ A C_ dom F ) ->
                  ( F " A ) = { y | E. x e. A y = ( F ` x ) } ) $=
      ( vz wfun cdm wss wa cima cv cfv wceq wrex cab wbr wcel nfcv dfima2 eqcom
      wb ssel funbrfvb bitr3id ex syl9r imp31 rexbidva abbidv eqtr4id nfeq2 nfv
      nffv fveq2 eqeq2d cbvrexfw abbii eqtrdi ) DHZCDIZJZKZDCLZBMZGMZDNZOZGCPZB
      QZVFAMZDNZOZACPZBQVDVEVGVFDRZGCPZBQVKGBDCUAVDVJVQBVDVIVPGCVAVCVGCSZVIVPUC
      ZVCVRVGVBSZVAVSCVBVGUDVAVTVSVIVHVFOVAVTKVPVHVFUBVGVFDUEUFUGUHUIUJUKULVJVO
      BVIVNGACGCTEAVFVHAVGDFAVGTUOUMVNGUNVGVLOVHVMVFVGVLDUPUQURUSUT $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y F $.
    funimass4f.1 $e |- F/_ x A $.
    funimass4f.2 $e |- F/_ x B $.
    funimass4f.3 $e |- F/_ x F $.
    $( use ~ ffnfvf $)
    $( Membership relation for the values of a function whose image is a
       subclass.  (Contributed by Thierry Arnoux, 24-Apr-2017.) $)
    funimass4f $p |- ( ( Fun F /\ A C_ dom F ) ->
                    ( ( F " A ) C_ B <-> A. x e. A ( F ` x ) e. B ) ) $=
      ( vy wfun cdm wss wa cima cv cfv wcel wral nfss nfan wceq nffun funfvima2
      nfdm nfima ssel sylan9 ralrimi cab dfimafnf adantr abrexss adantl eqsstrd
      wrex impbida ) DIZBDJZKZLZDBMZCKZANZDOZCPZABQZUSVALVDABUSVAAUPURAADGUAABU
      QEADGUCRSAUTCADBGEUDFRSUSVBBPVCUTPVAVDBVBDUBUTCVCUEUFUGUSVELUTHNVCTABUNHU
      HZCUSUTVFTVEAHBDEGUIUJVEVFCKUSAHBVCCFUKULUMUO $.
  $}

  ${
    $d l A $.  $d l B $.  $d l W $.  $d k l Z $.  $d l ph $.
    suppss2f.p $e |- F/ k ph $.
    suppss2f.a $e |- F/_ k A $.
    suppss2f.w $e |- F/_ k W $.
    suppss2f.n $e |- ( ( ph /\ k e. ( A \ W ) ) -> B = Z ) $.
    suppss2f.v $e |- ( ph -> A e. V ) $.
    $( Show that the support of a function is contained in a set.  (Contributed
       by Thierry Arnoux, 22-Jun-2017.)  (Revised by AV, 1-Sep-2020.) $)
    suppss2f $p |- ( ph -> ( ( k e. A |-> B ) supp Z ) C_ W ) $=
      ( vl cmpt csupp co wa wi wsb bitri cv nfcv nfcsb1v csbeq1a cbvmptf oveq1i
      csb cdif wcel wceq sbt sbim sban sbf nfdif clelsb1fw anbi12i sbsbc wb cvv
      wsbc sbceq1g elv imbi12i mpbi suppss2 eqsstrid ) ADBCNZGOPMBDMUAZCUGZNZGO
      PFVHVKGODMBCVJIMBUBMCUBDVICUCDVICUDUEUFABVJMEFGADUABFUHZUIZQZCGUJZRZDMSZA
      VIVLUIZQZVJGUJZRZVPDMKUKVQVNDMSZVODMSZRWAVNVODMULWBVSWCVTWBADMSZVMDMSZQVS
      AVMDMUMWDAWEVRADMHUNDMVLDBFIJUOUPUQTWCVODVIVAZVTVODMURWFVTUSMDVICGUTVBVCT
      VDTVELVFVG $.
  $}

$(
  @{
    f1iniseg.g @e |- G = ( x e. B |-> ( `' F " { x } ) ) @.
    @( The initial segment, i.e. the preimage of singleton, is injective.
       (Contributed by Thierry Arnoux, 27-Jan-2020.) @)
    f1iniseg @p |- ( F : A --> B -> G : B -1-1-> ~P A ) @=
      ? @.
  @}
$)

  ${
    $d x y B $.  $d x y C $.  $d x y F $.  $d y G $.  $d x y .+ $.
    $d x y ph $.
    ofrn.1 $e |- ( ph -> F : A --> B ) $.
    ofrn.2 $e |- ( ph -> G : A --> B ) $.
    ofrn.3 $e |- ( ph -> .+ : ( B X. B ) --> C ) $.
    ofrn.4 $e |- ( ph -> A e. V ) $.
    $( The range of the function operation.  (Contributed by Thierry Arnoux,
       8-Jan-2017.) $)
    ofrn $p |- ( ph -> ran ( F oF .+ G ) C_ C ) $=
      ( vx vy cof co cv fovcdmda inidm off frnd ) ABDFGEOPAMNBBBECCDFGHHAMQNQDC
      CEKRIJLLBSTUA $.

    $d a z A $.  $d z B $.  $d a z F $.  $d a x z G $.  $d a z .+ $.
    $d a z ph $.  $d x y z a $.
    $( The range of the function operation.  (Contributed by Thierry Arnoux,
       21-Mar-2017.) $)
    ofrn2 $p |- ( ph -> ran ( F oF .+ G ) C_ ( .+ " ( ran F X. ran G ) ) ) $=
      ( vz va vx vy cv co crn wcel cfv wceq wrex cab cof cxp cima wa wfn simprl
      ffnd fnfvelrn syl2an2r simprr rspceov syl3anc rexlimdvaa cmpt inidm eqidd
      ss2abdv offval rneqd eqid rnmpt eqtrdi wss wb frnd xpss12 ovelimab eqabdv
      syl2anc 3sstr4d ) AMQZNQZFUAZVPGUAZERZUBZNBUCZMUDZVOOQPQERUBPGSZUCOFSZUCZ
      MUDFGEUERZSZEWDWCUFZUGZAWAWEMAVTWENBAVPBTZVTUHZUHVQWDTZVRWCTZVTWEAFBUIWKW
      JWLABCFIUKZAWJVTUJZBVPFULUMAGBUIWKWJWMABCGJUKZWOBVPGULUMAWJVTUNOPWDWCVQVR
      VOEUOUPUQVAAWGNBVSURZSWBAWFWQANBBVQVREBFGHHWNWPLLBUSAWJUHZVQUTWRVRUTVBVCN
      MBVSWQWQVDVEVFAWEMWIAECCUFZUIWHWSVGZVOWITWEVHAWSDEKUKAWDCVGWCCVGWTABCFIVI
      ABCGJVIWDCWCCVJVMOPWSWDWCVOEVKVMVLVN $.
  $}

  ${
    $d z A $.  $d z B $.  $d z C $.  $d y z G $.  $d x y z ph $.  $d x y S $.
    $d x y T $.  $d x y z F $.  $d x y z R $.  $d x y z U $.
    off2.1 $e |- ( ( ph /\ ( x e. S /\ y e. T ) ) -> ( x R y ) e. U ) $.
    off2.2 $e |- ( ph -> F : A --> S ) $.
    off2.3 $e |- ( ph -> G : B --> T ) $.
    off2.4 $e |- ( ph -> A e. V ) $.
    off2.5 $e |- ( ph -> B e. W ) $.
    off2.6 $e |- ( ph -> ( A i^i B ) = C ) $.
    $( The function operation produces a function - alternative form with all
       antecedents as deduction.  (Contributed by Thierry Arnoux,
       17-Feb-2017.) $)
    off2 $p |- ( ph -> ( F oF R G ) : C --> U ) $=
      ( vz cv cfv co cof cmpt ffnd eqid wcel wa eqidd offval mpteq1d eqtrd wral
      cin wf adantr inss1 eqsstrrdi sselda ffvelcdmd ralrimivva ovrspc2v fmpt3d
      inss2 syl21anc ) AUAFUAUBZKUCZVHLUCZGUDZJKLGUEUDZAVLUADEUPZVKUFUAFVKUFAUA
      DEVIVJGVMKLMNADHKPUGAEILQUGRSVMUHAVHDUIUJVIUKAVHEUIUJVJUKULAUAVMFVKTUMUNA
      VHFUIZUJZVIHUIVJIUIBUBCUBGUDJUIZCIUOBHUOZVKJUIVODHVHKADHKUQVNPURAFDVHAFVM
      DTDEUSUTVAVBVOEIVHLAEILUQVNQURAFEVHAFVMETDEVFUTVAVBAVQVNAVPBCHIOVCURBCHIJ
      GVIVJVDVGVE $.
  $}

  ${
    $d x A $.  $d x B $.  $d x F $.  $d x G $.  $d x R $.  $d x ph $.
    ofresid.1 $e |- ( ph -> F : A --> B ) $.
    ofresid.2 $e |- ( ph -> G : A --> B ) $.
    ofresid.3 $e |- ( ph -> A e. V ) $.
    $( Applying an operation restricted to the range of the functions does not
       change the function operation.  (Contributed by Thierry Arnoux,
       14-Feb-2018.) $)
    ofresid $p |- ( ph -> ( F oF R G ) = ( F oF ( R |` ( B X. B ) ) G ) ) $=
      ( vx cfv co cmpt cof ffvelcdmda df-ov ffnd eqidd offval cxp cres wcel cop
      cv wa opelxpd fvresd eqcomd 3eqtr4g mpteq2dva inidm 3eqtr4d ) AKBKUEZELZU
      NFLZDMZNKBUOUPDCCUAZUBZMZNEFDOMEFUSOMAKBUQUTAUNBUCUFZUOUPUDZDLZVBUSLZUQUT
      VAVDVCVAVBURDVAUOUPCCABCUNEHPABCUNFIPUGUHUIUOUPDQUOUPUSQUJUKAKBBUOUPDBEFG
      GABCEHRZABCFIRZJJBULZVAUOSZVAUPSZTAKBBUOUPUSBEFGGVEVFJJVGVHVITUM $.
  $}

  $(
    $d x y ph $.  $d x C $.  $d x D $.  $d y A $.  $d y B $.
    mptcnv.1 $e |- ( ph -> ( ( x e. A /\ y = B ) <-> ( y e. C /\ x = D ) ) ) $.
    #( The converse of a mapping function.
       (Contributed by Thierry Arnoux, 16-Jan-2017.) #)
    mptcnv   $p |- ( ph -> `' ( x e. A |-> B ) = ( y e. C |-> D ) ) $=
      ( cv wcel wceq wa copab ccnv cmpt cnvopab opabbidv eqtrd df-mpt
      a1i cnveqi 3eqtr4d ) ABIZDJCIZEKLZBCMZNZUDFJUCGKLZCBMZBDEOZNZCF
      GOZAUGUECBMZUIUGUMKAUEBCPTAUEUHCBHQRUKUGKAUJUFBCDESUATULUIKACBF
      GSTUB $.
  $)

  ${
    $d x y F $.  $d x y A $.
    $( Preimage of a class union.  (Contributed by Thierry Arnoux,
       7-Feb-2017.) $)
    unipreima $p |- ( Fun F -> ( `' F " U. A ) = U_ x e. A ( `' F " x ) ) $=
      ( vy wfun cdm wfn ccnv cuni cima cv ciun wceq wcel wa wrex wb a1i 3bitr4d
      elpreima funfn cfv r19.42v bicomi eluni2 anbi2i rexbidv eliun eqrdv sylbi
      ) CECCFZGZCHZBIZJZABUMAKZJZLZMCUAULDUOURULDKZUKNZUSCUBZUNNZOZUSUQNZABPZUS
      UONUSURNZULUTVAUPNZABPZOZUTVGOZABPZVCVEVIVKQULVKVIUTVGABUCUDRVCVIQULVBVHU
      TAVABUEUFRULVDVJABUKUSUPCTUGSUKUSUNCTVFVEQULAUSBUQUHRSUIUJ $.
  $}

  $( Value of a function producing ordered pairs.  (Contributed by Thierry
     Arnoux, 3-Jan-2017.) $)
  opfv $p |- ( ( ( Fun F /\ ran F C_ ( _V X. _V ) ) /\ x e. dom F ) ->
             ( F ` x ) = <. ( ( 1st o. F ) ` x ) , ( ( 2nd o. F ) ` x ) >. ) $=
    ( wfun crn cvv cxp wss wa cv cdm wcel cfv c1st c2nd cop ccom simplr adantlr
    wceq fvco fvelrn sseldd 1st2ndb sylib opeq12d eqtr4d ) BCZBDZEEFZGZHAIZBJKZ
    HZUKBLZUNMLZUNNLZOZUKMBPLZUKNBPLZOZUMUNUIKUNUQSUMUHUIUNUGUJULQUGULUNUHKUJUK
    BUARUBUNUCUDUGULUTUQSUJUGULHURUOUSUPUKMBTUKNBTUERUF $.

  ${
    $d x F $.  $d x Y $.  $d x Z $.
    $( The preimage of a Cartesian product is the intersection of the preimages
       of each component function.  (Contributed by Thierry Arnoux,
       6-Jun-2017.) $)
    xppreima $p |- ( ( Fun F /\ ran F C_ ( _V X. _V ) ) ->
      ( `' F " ( Y X. Z ) ) =
                   ( ( `' ( 1st o. F ) " Y ) i^i ( `' ( 2nd o. F ) " Z ) ) ) $=
      ( vx wfun cvv wss wa ccnv cima c1st wcel c2nd cdm crab cin wceq adantr wb
      cfv crn cxp cv ccom wfn funfn fncnvima2 sylbi elxp6 opeq12d eqeq2d eleq1d
      cop fvco anbi12d bitr4id adantlr opfv biantrurd wfo fo1st fofun ax-mp ssv
      funco mpan wf fof fdm mp2b sseqtrri ssid funimass3 mpan2 sselda eleqtrrdi
      mpbii dmco fvimacnv syl2anc fo2nd 3bitr2d rabbidva eqtrd ineq12i cnvimass
      dfin5 dmcoss sstri sseqin2 mpbi inrab 3eqtr3ri eqtrdi ) AEZAUAFFUBGZHZAIZ
      BCUBZJZDUCZKAUDZIBJZLZXAMAUDZICJZLZHZDANZOZXCXFPZWQWTXAATZWSLZDXIOZXJWOWT
      XNQZWPWOAXIUEXOAUFDXIWSAUGUHRWQXMXHDXIWQXAXILZHZXMXLXAXBTZXAXETZUMZQZXRBL
      ZXSCLZHZHZYDXHWOXPXMYESWPWOXPHZXMXLXLKTZXLMTZUMZQZYGBLZYHCLZHZHYEXLBCUIYF
      YAYJYDYMYFXTYIXLYFXRYGXSYHXAKAUNZXAMAUNZUJUKYFYBYKYCYLYFXRYGBYNULYFXSYHCY
      OULUOUOUPUQXQYAYDDAURUSWOXPYDXHSWPYFYBXDYCXGYFXBEZXAXBNZLYBXDSWOYPXPKEZWO
      YPFFKUTZYRVAFFKVBVCKAVEVFRYFXAWRKNZJZYQWOXIUUAXAWOAXIJZYTGZXIUUAGZUUBFYTU
      UBVDZYSFFKVGYTFQVAFFKVHFFKVIVJVKWOXIXIGZUUCUUDSXIVLZXIYTAVMVNVQVOKAVRVPXA
      BXBVSVTYFXEEZXAXENZLYCXGSWOUUHXPMEZWOUUHFFMUTZUUJWAFFMVBVCMAVEVFRYFXAWRMN
      ZJZUUIWOXIUUMXAWOUUBUULGZXIUUMGZUUBFUULUUEUUKFFMVGUULFQWAFFMVHFFMVIVJVKWO
      UUFUUNUUOSUUGXIUULAVMVNVQVOMAVRVPXACXEVSVTUOUQWBWCWDXIXCPZXIXFPZPXDDXIOZX
      GDXIOZPXKXJUUPUURUUQUUSDXIXCWGDXIXFWGWEUUPXCUUQXFXCXIGUUPXCQXCYQXIXBBWFKA
      WHWIXCXIWJWKXFXIGUUQXFQXFUUIXIXECWFMAWHWIXFXIWJWKWEXDXGDXIWLWMWN $.
  $}

  ${
    $d A p x y $.  $d B p x y $.
    $( Image of a cartesian product by ` 2nd ` .  (Contributed by Thierry
       Arnoux, 23-Jun-2024.) $)
    2ndimaxp $p |- ( A =/= (/) -> ( 2nd " ( A X. B ) ) = B ) $=
      ( vy vp vx c0 wne c2nd cxp cima wceq adantl wa cv wcel cfv wb cvv a1i vex
      ima0 xpeq2 xp0 eqtrdi imaeq2d id 3eqtr4a wrex xpnz wfo wfn fo2nd fofn wss
      mp1i ssv fvelimabd sylbi simpr xp2nd ad2antlr eqeltrrd r19.29an n0 biimpi
      wex ad2antrr cop opelxpi ancoms adantll fveqeq2 rspcedvd exlimddv impbida
      op2nd bitrd eqrdv pm2.61dane ) AFGZHABIZJZBKZBFBFKZWCVTWDHFJFWBBHUAWDWAFH
      WDWAAFIFBFAUBAUCUDUEWDUFUGLVTBFGZMZCWBBWFCNZWBOZDNZHPZWGKZDWAUHZWGBOZWFWA
      FGZWHWLQABUIWNDRWAWGHRRHUJHRUKWNULRRHUMUOWARUNWNWAUPSUQURWFWLWMWFWKWMDWAW
      FWIWAOZMZWKMWJWGBWPWKUSWOWJBOWFWKWIABUTVAVBVCWFWMMZENZAOZWLEVTWSEVFZWEWMV
      TWTEAVDVEVGWQWSMZWKWRWGVHZHPWGKZDXBWAWMWSXBWAOZWFWSWMXDWRWGABVIVJVKWIXBKW
      KXCQXAWIXBWGHVLLXCXAWRWGETCTVPSVMVNVOVQVRVS $.
  $}

  ${
    $d A x $.  $d ph x $.
    dmdju.1 $e |- ( ( ph /\ x e. A ) -> B =/= (/) ) $.
    $( Domain of a disjoint union of non-empty sets.  (Contributed by Thierry
       Arnoux, 5-Oct-2025.) $)
    dmdju $p |- ( ph -> dom U_ x e. A ( { x } X. B ) = A ) $=
      ( cv csn cxp ciun cdm dmiun wcel wa c0 wne wceq dmxp syl iuneq2dv eqtrid
      iunid eqtrdi ) ABCBFZGZDHZIJZBCUDIZCAUFBCUEJZIUGBCUEKABCUHUDAUCCLMDNOUHUD
      PEUDDQRSTBCUAUB $.
  $}

  ${
    $d A k $.
    $( Stronger version of ~ djussxp .  (Contributed by Thierry Arnoux,
       23-Jun-2024.) $)
    djussxp2 $p |- U_ k e. A ( { k } X. B ) C_ ( A X. U_ k e. A B ) $=
      ( cv csn cxp ciun nfcv nfiu1 nfxp iunssf wcel snssi ssiun2 xpss12 syl2anc
      wss mprgbir ) CACDZEZBFZGACABGZFZQUAUCQZCACAUAUCCAUBCAHCABIJKSALTAQBUBQUD
      SAMCABNTABUBOPR $.
  $}

  ${
    $d A u x $.  $d C c d y $.  $d U c d u y $.  $d U c d v y $.
    $d X c d x y $.  $d c d ph u v x y $.
    2ndresdju.u $e |- U = U_ x e. X ( { x } X. C ) $.
    2ndresdju.a $e |- ( ph -> A e. V ) $.
    2ndresdju.x $e |- ( ph -> X e. W ) $.
    2ndresdju.1 $e |- ( ph -> Disj_ x e. X C ) $.
    2ndresdju.2 $e |- ( ph -> U_ x e. X C = A ) $.
    $( The ` 2nd ` function restricted to a disjoint union is injective.
       (Contributed by Thierry Arnoux, 23-Jun-2024.) $)
    2ndresdju $p |- ( ph -> ( 2nd |` U ) : U -1-1-> A ) $=
      ( vu vy vd c2nd wcel cvv wa vv vc cres wf cv cfv wceq wi wral wf1 wfn wfo
      fo2nd fofn mp1i wss ssv a1i fnssresd simpr fvresd cxp csn djussxp2 xpeq2d
      ciun sseqtrid eqsstrid xp2nd syl eqeltrd ralrimiva ffnfv sylanbrc cop wex
      sselda nfv nfiu1 nfcxfr nfcri nfan nfcv nffv nfeq eleq2i eliunxp ad3antlr
      nfres sylbb bitri nfcsb1v nfex opeq1 eqeq2d eleq1w csbeq1a eleq2d anbi12d
      csb exbidv cbvexv1 ad5antlr wdisj ad9antr simp-5r simp-4r simp-7r simp-9r
      simplr simp-6r fveq2d op2nd eqtrdi eqtrd simp-8r simpllr disjif syl122anc
      vex 3eqtr3d opeq12d 3eqtr4d anasss expl exlimdvv mpd exlimdv exlimimdd ex
      ralrimivva dff13 ) AECQEUCZUDZNUEZYMUFZUAUEZYMUFZUGZYOYQUGZUHZUAEUINEUIEC
      YMUJAYMEUKYPCRZNEUIYNASEQSSQULQSUKAUMSSQUNUOESUPAEUQURUSAUUBNEAYOERZTZYPY
      OQUFZCUUDYOEQAUUCUTVAUUDYOHCVBZRUUECRAEUUFYOAEBHBUEZVCDVBZVFZUUFIAHBHDVFZ
      VBUUIUUFHDBVDAUUJCHMVEVGVHVQYOHCVIVJVKVLNECYMVMVNAUUANUAEEAUUCYQERZUUAUUD
      UUKTZYSYTUULYSTZYOUUGUBUEZVOZUGZUUGHRZUUNDRZTZTZUBVPZYTBUULYSBUUDUUKBAUUC
      BABVRBNEBEUUIIBHUUHVSVTZWAWBBUAEUVBWAWBBYPYRBYOYMBQEBQWCUVBWIZBYOWCWDBYQY
      MUVCBYQWCWDWEWBYTBVRUUCUVABVPZAUUKYSUUCYOUUIRUVDEUUIYOIWFBUBHDYOWGWJWHUUM
      UUTYTUBUUMUUPUUSYTUUMUUPTZUUQUURYTUVEUUQTZUURTZYQOUEZPUEZVOZUGZUVHHRZUVIB
      UVHDWTZRZTZTZPVPZOVPZYTUUKUVRUUDYSUUPUUQUURUUKYQUUGUVIVOZUGZUUQUVIDRZTZTZ
      PVPZBVPZUVRUUKYQUUIRUWEEUUIYQIWFBPHDYQWGWKUWDUVQBOUWDOVRUVPBPUVKUVOBUVKBV
      RUVLUVNBUVLBVRBPUVMBUVHDWLZWAWBWBWMUUGUVHUGZUWCUVPPUWGUVTUVKUWBUVOUWGUVSU
      VJYQUUGUVHUVIWNWOUWGUUQUVLUWAUVNBOHWPUWGDUVMUVIBUVHDWQZWRWSWSXAXBWJXCUVGU
      VPYTOPUVGUVKUVOYTUVGUVKTZUVLUVNYTUWIUVLTZUVNTZUUOUVJYOYQUWKUUGUVHUUNUVIUW
      KBHDXDZUUQUVLUURUUNUVMRUWGAUWLUUCUUKYSUUPUUQUURUVKUVLUVNLXEUVEUUQUURUVKUV
      LUVNXFUWIUVLUVNXJUVFUURUVKUVLUVNXGUWKUUNUVIUVMUWKYPYRUUNUVIUULYSUUPUUQUUR
      UVKUVLUVNXHUWKYPUUEUUNUWKYOEQAUUCUUKYSUUPUUQUURUVKUVLUVNXIVAUWKUUEUUOQUFU
      UNUWKYOUUOQUUMUUPUUQUURUVKUVLUVNXKZXLUUGUUNBXTUBXTXMXNXOUWKYRYQQUFZUVIUWK
      YQEQUUDUUKYSUUPUUQUURUVKUVLUVNXPVAUWKUWNUVJQUFUVIUWKYQUVJQUVGUVKUVLUVNXQZ
      XLUVHUVIOXTPXTXMXNXOYAZUWJUVNUTVKBHDUVMUVHUUNUWFUWHXRXSUWPYBUWMUWOYCYDYEY
      FYGYDYEYHYIYJYDYKNUAECYMYLVN $.

    $( The ` 2nd ` function restricted to a disjoint union is a bijection.  See
       also e.g. ~ 2ndconst .  (Contributed by Thierry Arnoux, 23-Jun-2024.) $)
    2ndresdjuf1o $p |- ( ph -> ( 2nd |` U ) : U -1-1-onto-> A ) $=
      ( c2nd cres wf1 wfo wf1o 2ndresdju ciun iunfo foeq3 biimpa sylancl df-f1o
      wceq sylanbrc ) AECNEOZPECUHQZECUHRABCDEFGHIJKLMSABHDTZCUFZEUJUHQZUIMBHDE
      IUAUKULUIUJCEUHUBUCUDECUHUEUG $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x F $.  $d x G $.  $d x H $.
    $d x ph $.
    xppreima2.1 $e |- ( ph -> F : A --> B ) $.
    xppreima2.2 $e |- ( ph -> G : A --> C ) $.
    xppreima2.3 $e |- H = ( x e. A |-> <. ( F ` x ) , ( G ` x ) >. ) $.
    $( The preimage of a Cartesian product is the intersection of the preimages
       of each component function.  (Contributed by Thierry Arnoux,
       7-Jun-2017.) $)
    xppreima2 $p |- ( ph -> ( `' H " ( Y X. Z ) ) =
                                         ( ( `' F " Y ) i^i ( `' G " Z ) ) ) $=
      ( ccnv cima c1st c2nd cvv wceq cfv cxp ccom cin wfun crn wss funmpt2 wcel
      cv cop ffvelcdmda opelxp sylanbrc fmptd frnd xpss sstrdi xppreima sylancr
      wa wfn wfo fo1st fofn ax-mp opex fnmpti ssv fnco mp3an a1i ffnd cdm simpr
      adantr dmmpti eleqtrrdi opfv fvmpt2 syl2anc eqtr3d fvex opth sylib simpld
      syl21anc eqfnfvd cnveqd imaeq1d fo2nd simprd ineq12d eqtrd ) AHNIJUAOZPHU
      BZNZIOZQHUBZNZJOZUCZFNZIOZGNZJOZUCAHUDZHUEZRRUAZUFZWNXASBCBUIZFTZXJGTZUJZ
      HMUGZAXGDEUAZXHACXOHABCXMXOHAXJCUHZUTZXKDUHXLEUHXMXOUHZACDXJFKUKACEXJGLUK
      XKXLDEULUMZMUNUODEUPUQZHIJURUSAWQXCWTXEAWPXBIAWOFABCWOFWOCVAZAPRVAZHCVAZX
      GRUFZYARRPVBYBVCRRPVDVEBCXMHXKXLVFZMVGZXGVHZRCPHVIVJVKACDFKVLXQXJWOTZXKSZ
      XJWRTZXLSZXQYHYJUJZXMSYIYKUTXQXJHTZYLXMXQXFXIXJHVMZUHYMYLSXFXQXNVKAXIXPXT
      VOXQXJCYNAXPVNZBCXMHYEMVPVQBHVRWFXQXPXRYMXMSYOXSBCXMXOHMVSVTWAYHYJXKXLXJW
      OWBXJWRWBWCWDZWEWGWHWIAWSXDJAWRGABCWRGWRCVAZAQRVAZYCYDYQRRQVBYRWJRRQVDVEY
      FYGRCQHVIVJVKACEGLVLXQYIYKYPWKWGWHWIWLWM $.
  $}

  ${
    $d x y B $.  $d x y F $.  $d x y V $.  $d y ps $.
    abfmpunirn.1 $e |- F = ( x e. V |-> { y | ph } ) $.
    abfmpunirn.2 $e |- { y | ph } e. _V $.
    abfmpunirn.3 $e |- ( y = B -> ( ph <-> ps ) ) $.
    $( Membership in a union of a mapping function-defined family of sets.
       (Contributed by Thierry Arnoux, 28-Sep-2016.) $)
    abfmpunirn $p |- ( B e. U. ran F <-> ( B e. _V /\ E. x e. V ps ) ) $=
      ( crn cuni wcel cvv wrex elex cab cv cfv wfn wb fnmpti fnunirn ax-mp wceq
      fvmpt2 mpan2 eleq2d rexbiia bitri elabg rexbidv bitrid biadanii ) EFKLZMZ
      ENMZBCGOZEUOPUPEADQZMZCGOZUQURUPECRZFSZMZCGOZVAFGTUPVEUACGUSFIHUBCEFGUCUD
      VDUTCGVBGMZVCUSEVFUSNMVCUSUEICGUSNFHUFUGUHUIUJUQUTBCGABDENJUKULUMUN $.
  $}

  ${
    $d x y B $.  $d x y F $.  $d x y V $.  $d y W $.  $d y ps $.
    rabfmpunirn.1 $e |- F = ( x e. V |-> { y e. W | ph } ) $.
    rabfmpunirn.2 $e |- W e. _V $.
    rabfmpunirn.3 $e |- ( y = B -> ( ph <-> ps ) ) $.
    $( Membership in a union of a mapping function-defined family of sets.
       (Contributed by Thierry Arnoux, 30-Sep-2016.) $)
    rabfmpunirn $p |- ( B e. U. ran F <-> E. x e. V ( B e. W /\ ps ) ) $=
      ( crn cuni wcel cvv wa wrex cv crab cmpt df-rab mpteq2i eqtri sepab ax-mp
      cab wceq eleq1 anbi12d abfmpunirn elex adantr rexlimivw pm4.71ri bitr4i )
      EFLMNEONZEHNZBPZCGQZPUSDRZHNZAPZURCDEFGFCGADHSZTCGVBDUFZTICGVCVDADHUAUBUC
      HONVDONJADHOUDUEUTEUGVAUQABUTEHUHKUIUJUSUPURUPCGUQUPBEHUKULUMUNUO $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y F $.  $d x y V $.  $d y W $.  $d x y ch $.
    $d x y ch $.  $d x y ph $.
    abfmpeld.1 $e |- F = ( x e. V |-> { y | ps } ) $.
    abfmpeld.2 $e |- ( ph -> { y | ps } e. _V ) $.
    abfmpeld.3 $e |- ( ph -> ( ( x = A /\ y = B ) -> ( ps <-> ch ) ) ) $.
    $( Membership in an element of a mapping function-defined family of sets.
       (Contributed by Thierry Arnoux, 19-Oct-2016.) $)
    abfmpeld $p |- ( ph -> ( ( A e. V /\ B e. W ) ->
        ( B e. ( F ` A ) <-> ch ) ) ) $=
      ( wcel wa wb cab cvv wceq wal cfv wsbc alrimiv csbexg fvmpts sylan2 csbab
      csb eqtrdi eleq2d adantl cv wi simpll ancomsd impl sbcied ex elabgt bitrd
      syl an13s ) AFINZGJNZOGFHUAZNZCPZVDVCAVGVDVCAOZOVFGBDFUBZEQZNZCVHVFVKPVDV
      HVEVJGVHVEDFBEQZUHZVJAVCVMRNZVEVMSAVLRNZDTVNAVODLUCDFVLRUDVADFVLIHRKUEUFB
      DEFUGUIUJUKVHVDEULGSZVICPZUMZETVKCPVHVREVHVPVQVHVPOBCDFIVCAVPUNVHVPDULFSZ
      BCPZAVPVSOVTUMVCAVSVPVTMUOUKUPUQURUCVICEGJUSUFUTVBUR $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y F $.  $d x y V $.  $d y W $.  $d x y ps $.
    $d y W $.
    abfmpel.1 $e |- F = ( x e. V |-> { y | ph } ) $.
    abfmpel.2 $e |- { y | ph } e. _V $.
    abfmpel.3 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    $( Membership in an element of a mapping function-defined family of sets.
       (Contributed by Thierry Arnoux, 19-Oct-2016.) $)
    abfmpel $p |- ( ( A e. V /\ B e. W ) -> ( B e. ( F ` A ) <-> ps ) ) $=
      ( wcel wa cab wb cvv wceq cv ancoms cfv wsbc csb csbex fvmpts mpan2 csbab
      eqtrdi eleq2d adantr wi wal simpl adantll sbcied ex alrimiv elabgt sylan2
      bitrd ) EHMZFIMZNFEGUAZMZFACEUBZDOZMZBVAVDVGPVBVAVCVFFVAVCCEADOZUCZVFVAVI
      QMVCVIRCEVHKUDCEVHHGQJUEUFACDEUGUHUIUJVBVAVGBPZVAVBDSFRZVEBPZUKZDULVJVAVM
      DVAVKVLVAVKNABCEHVAVKUMVKCSERZABPZVAVNVKVOLTUNUOUPUQVEBDFIURUSTUT $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.  $d y ph $.
    fmptdf2.p $e |- F/ x ph $.
    fmptdf2.a $e |- F/_ x A $.
    fmptdf2.c $e |- F/_ x C $.
    fmptdf2.1 $e |- ( ( ph /\ x e. A ) -> B e. C ) $.
    fmptdf2.2 $e |- F = ( x e. A |-> B ) $.
    $( Domain and codomain of the mapping operation; deduction form.  This
       version of ~ fmptd uses bound-variable hypothesis instead of distinct
       variable conditions.  (Contributed by Thierry Arnoux, 28-Mar-2017.) $)
    fmptdf2 $p |- ( ph -> F : A --> C ) $=
      ( vy wf cv csb wcel wa wsb bitri nfcv cmpt wral sbimi sban clelsb1fw wsbc
      sbf anbi12i sbsbc sbcel12 csbgfi eleq2i 3imtr3i ralrimiva nfcsb1v csbeq1a
      vex cbvmptf fmpt sylib feq1i sylibr ) ACEBCDUAZMZCEFMABLNZDOZEPZLCUBVDAVG
      LCABNCPZQZBLRZDEPZBLRZAVECPZQZVGVIVKBLJUCVJABLRZVHBLRZQVNAVHBLUDVOAVPVMAB
      LGUGBLCHUEUHSVLVKBVEUFZVGVKBLUIVQVFBVEEOZPVGBVEDEUJVREVFBVEELUQIUKULSSUMU
      NLCEVFVCBLCDVFHLCTLDTBVEDUOBVEDUPURUSUTCEFVCKVAVB $.
  $}

  ${
    $d u v w x y z $.  $d u v w z A $.  $d u y B $.  $d u w z F $.
    $d u w z G $.  $d u y R $.  $d u S $.  $d u v w z T $.  $d u w z ph $.
    fmptcof2.x $e |- F/_ x S $.
    fmptcof2.y $e |- F/_ y T $.
    fmptcof2.1 $e |- F/_ x A $.
    fmptcof2.2 $e |- F/_ x B $.
    fmptcof2.3 $e |- F/ x ph $.
    fmptcof2.4 $e |- ( ph -> A. x e. A R e. B ) $.
    fmptcof2.5 $e |- ( ph -> F = ( x e. A |-> R ) ) $.
    fmptcof2.6 $e |- ( ph -> G = ( y e. B |-> S ) ) $.
    fmptcof2.7 $e |- ( y = R -> S = T ) $.
    $( Composition of two functions expressed as ordered-pair class
       abstractions.  (Contributed by FL, 21-Jun-2012.)  (Revised by Mario
       Carneiro, 24-Jul-2014.)  (Revised by Thierry Arnoux, 10-May-2017.) $)
    fmptcof2 $p |- ( ph -> ( G o. F ) = ( x e. A |-> T ) ) $=
      ( wceq vz vw vu vv ccom cmpt relco mptrel cv wbr wa wex wcel csb cop wfun
      cfv r19.21bi eqid fmptdf2 feq1d mpbird ffund funbrfv imp sylan eqcomd a1d
      expimpd pm4.71rd exbidv fvex breq2 breq1 anbi12d ceqsexv cdm funfvbrb syl
      wf wb fdmd eleq2d bitr3d eqidd breq123d wi nfcri nffvmpt1 nfmpt nfcv nfbr
      fveq1d nfcsb1v nfeq2 nfbi nfim eleq1w fveq2 breq1d csbeq1a eqeq2d bibi12d
      imbi2d imbi12d cvv vex nfv nfan simpl eleq1d simpr adantr eqeq12d brabgaf
      df-mpt sylancl fvmpt2f syl2anc 3bitr4d expcom chvarfv impcom bitrd bitrid
      biantrurd pm5.32da opelco copab eleq2i anbi2d opelopabf 3bitr4g eqrelrdv
      eqeq1 bitri ) AUAUBJIUEZBDHUFZJIUGBDHUHAUAUIZUCUIZIUJZYTUBUIZJUJZUKZUCULZ
      YSDUMZUUBBYSHUNZTZUKZYSUUBUOZYQUMUUJYRUMZAUUEYTYSIUQZTZUUDUKZUCULZUUIAUUD
      UUNUCAUUDUUMAUUAUUCUUMAUUAUKZUUMUUCUUPUULYTAIUPZUUAUULYTTZADEIADEIVTDEBDF
      UFZVTABDFEUUSOMNAFEUMZBDPURZUUSUSUTADEIUUSQVAVBZVCZUUQUUAUURYSYTIVDVEVFVG
      VHVIVJVKUUOYSUULIUJZUULUUBJUJZUKZAUUIUUDUVFUCUULYSIVLUUMUUAUVDUUCUVEYTUUL
      YSIVMYTUULUUBJVNVOVPAUVFUUFYSUUSUQZUUBCEGUFZUJZUKUUIAUVDUUFUVEUVIAYSIVQZU
      MZUVDUUFAUUQUVKUVDWAUVCYSIVRVSAUVJDYSADEIUVBWBWCWDAUULUVGUUBUUBJUVHAYSIUU
      SQWMRAUUBWEWFVOAUUFUVIUUHUUFAUVIUUHWAZBUIZDUMZAUVMUUSUQZUUBUVHUJZUUBHTZWA
      ZWGZWGUUFAUVLWGZWGBUAUUFUVTBBUADMWHZAUVLBOUVIUUHBBUVGUUBUVHBDFYSWIBCEGNKW
      JBUUBWKWLBUUBUUGBYSHWNZWOWPWQWQUVMYSTZUVNUUFUVSUVTBUADWRZUWCUVRUVLAUWCUVP
      UVIUVQUUHUWCUVOUVGUUBUVHUVMYSUUSWSWTUWCHUUGUUBBYSHXAZXBXCXDXEAUVNUVRAUVNU
      KZFUUBUVHUJZUUTUVQUKZUVPUVQUWFUUTUUBXFUMUWGUWHWAUVAUBXGZCUIZEUMZYTGTZUKUW
      HCUCFUUBUVHEXFUUTUVQCUUTCXHCUUBHLWOXIUWJFTZYTUUBTZUKZUWKUUTUWLUVQUWOUWJFE
      UWMUWNXJXKUWOYTUUBGHUWMUWNXLUWMGHTUWNSXMXNVOCUCEGXPXOXQUWFUVOFUUBUVHUWFUV
      NUUTUVOFTAUVNXLUVABDFEMXRXSWTUWFUUTUVQUVAYFXTYAYBYCYGYDYEYDUCYSUUBJIUAXGZ
      UWIYHUUKUUJUVNUDUIZHTZUKZBUDYIZUMUUIYRUWTUUJBUDDHXPYJUWSUUFUWQUUGTZUKUUIB
      UDYSUUBUUFUXABUWABUWQUUGUWBWOXIUUIUDXHUWPUWIUWCUVNUUFUWRUXAUWDUWCHUUGUWQU
      WEXBVOUWQUUBTUXAUUHUUFUWQUUBUUGYOYKYLYPYMYN $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x C $.  $d x y D $.  $d x E $.
    fcomptf.1 $e |- F/_ x B $.
    $( Express composition of two functions as a maps-to applying both in
       sequence.  This version has one less distinct variable restriction
       compared to ~ fcompt .  (Contributed by Thierry Arnoux, 30-Jun-2017.) $)
    fcomptf $p |- ( ( A : D --> E /\ B : C --> D ) -> ( A o. B ) = ( x e. C |->
        ( A ` ( B ` x ) ) ) ) $=
      ( vy wf wa cv cfv wcel nfcv nff wfn cmpt wceq ffn sylib adantll ex adantl
      nfan ffvelcdm ralrimi dffn5f adantr dffn5 fveq2 fmptcof ) EFBIZDECIZJZAHD
      EAKZCLZHKZBLZUPBLCBUNUPEMZADULUMAAEFBABNAENZAFNOADECGADNUTOUDUNUODMZUSUMV
      AUSULDEUOCUEUAUBUFUNCDPZCADUPQRUMVBULDECSUCADCGUGTUNBEPZBHEURQRULVCUMEFBS
      UHHEBUITUQUPBUJUK $.
  $}

$(
  @{
    acrnmpt.0 @e |- ( ph -> A e. V ) @.
    acrnmpt.1 @e |- ( ( ph /\ j e. A ) -> B e. W ) @.
    acrnmpt.2 @e |- C = ran ( j e. A |-> B ) @.
    @( Axiom of choice for the range of a mapping to function.  (Contributed by
       Thierry Arnoux, 26-Jul-2020.) @)
    acrnmpt @p |- ( ph -> E. f ( f : C -1-1-onto-> ran f /\ ran f C_ A ) ) @=
      ? @.
  @}
$)

  ${
    acunirnmpt.0 $e |- ( ph -> A e. V ) $.
    acunirnmpt.1 $e |- ( ( ph /\ j e. A ) -> B =/= (/) ) $.
    ${
      $d j A $.  $d c f j y C $.  $d f j y ph $.
      acunirnmpt.2 $e |- C = ran ( j e. A |-> B ) $.
      $( Axiom of choice for the union of the range of a mapping to function.
         (Contributed by Thierry Arnoux, 6-Nov-2019.) $)
      acunirnmpt $p |- ( ph
        -> E. f ( f : C --> U. C /\ A. y e. C E. j e. A ( f ` y ) e. B ) ) $=
        ( vc cv wcel wral wa wex c0 cvv mpd cuni wf cfv wrex wceq simpr simplll
        wne simplr syl2anc eqnetrd cmpt crn eleq2i vex eqid elrnmpt ax-mp bitri
        wb bilani r19.29a ralrimiva wi mptexg rnexg eqeltrid raleq unieq feq23d
        3syl id anbi12d exbidv imbi12d ac5b vtoclg syl simpllr eleqtrd reximdva
        adantr ex ralimdva anim2d eximdv ) AEEUAZFMZUBZBMZWHUCZWJNZBEOZPZFQZWIW
        KDNZGCUDZBEOZPZFQAWJRUHZBEOZWOAWTBEAWJENZPZWJDUEZWTGCXCGMCNZPZXDPZWJDRX
        FXDUFXGAXEDRUHAXBXEXDUGXCXEXDUIJUJUKXBXDGCUDZAXBWJGCDULZUMZNZXHEXJWJKUN
        WJSNXKXHUTBUOGCDWJXISXIUPUQURUSVAZVBVCAESNXAWOVDZAEXJSKACHNXISNXJSNIGCD
        HVEXISVFVKVGWTBLMZOZXNXNUAZWHUBZWLBXNOZPZFQZVDXMLESXNEUEZXOXAXTWOWTBXNE
        VHYAXSWNFYAXQWIXRWMYAXNXPEWGWHYAVLXNEVIVJWLBXNEVHVMVNVOBXNFLUOVPVQVRTAW
        NWSFAWMWRWIAWLWQBEXCWLWQXCWLPZXHWQXCXHWLXLWBYBXDWPGCYBXEPZXDWPYCXDPWKWJ
        DXCWLXEXDVSYCXDUFVTWCWATWCWDWEWFT $.
    $}

    ${
      $d c f j x y A $.  $d c f y B $.  $d c f j x y C $.  $d c j D $.
      $d f j x y ph $.
      acunirnmpt2.2 $e |- C = U. ran ( j e. A |-> B ) $.
      acunirnmpt2.3 $e |- ( j = ( f ` x ) -> B = D ) $.
      $( Axiom of choice for the union of the range of a mapping to function.
         (Contributed by Thierry Arnoux, 7-Nov-2019.) $)
      acunirnmpt2 $p |- ( ph -> E. f ( f : C --> A /\ A. x e. C x e. D ) ) $=
        ( vy vc cv wcel wral wa cvv wrex wf wex cmpt crn wceq simplr wb elrnmpt
        vex eqid ax-mp sylib nfv nfcv nfmpt1 nfrn nfel wi simpllr simpr eleqtrd
        nfan ex reximdai mpd cuni eleq2i biimpi eluni2 adantl r19.29a ralrimiva
        mptexg rnexg uniexg 4syl eqeltrid id raleqdv anbi12d exbidv imbi12d cfv
        feq2d eleq2d ac6s vtoclg syl ) ABPZDQZHCUAZBERZECGPZUBZWJFQZBERZSZGUCZA
        WLBEAWJEQZSZWJNPZQZWLNHCDUDZUEZXAXBXEQZSZXCSZXBDUFZHCUAZWLXHXFXJXAXFXCU
        GXBTQXFXJUHNUJHCDXBXDTXDUKUIULUMXHXIWKHCXGXCHXAXFHXAHUNHXBXEHXBUOHXDHCD
        UPUQURVCXCHUNVCXHHPZCQZXIWKUSXHXLSZXIWKXMXISWJXBDXGXCXLXIUTXMXIVAVBVDVD
        VEVFWTXCNXEUAZAWTWJXEVGZQZXNWTXPEXOWJLVHVINWJXEVJUMVKVLVMAETQWMWSUSZAEX
        OTLACIQXDTQXETQXOTQJHCDIVNXDTVOXETVPVQVRWLBOPZRZXRCWNUBZWPBXRRZSZGUCZUS
        XQOETXREUFZXSWMYCWSYDWLBXREYDVSZVTYDYBWRGYDXTWOYAWQYDXRECWNYEWEYDWPBXRE
        YEVTWAWBWCWKWPBHXRCGOUJXKWJWNWDUFDFWJMWFWGWHWIVF $.
    $}

    aciunf1lem.a $e |- F/_ j A $.
    ${
      $d c f x y k A $.  $d c f k y B $.  $d c f x y C $.  $d c D $.
      $d f j k x y ph $.  $d j c $.
      acunirnmpt2f.c $e |- F/_ j C $.
      acunirnmpt2f.d $e |- F/_ j D $.
      acunirnmpt2f.2 $e |- C = U_ j e. A B $.
      acunirnmpt2f.3 $e |- ( j = ( f ` x ) -> B = D ) $.
      acunirnmpt2f.4 $e |- ( ( ph /\ j e. A ) -> B e. W ) $.
      $( Axiom of choice for the union of the range of a mapping to function.
         (Contributed by Thierry Arnoux, 7-Nov-2019.) $)
      acunirnmpt2f $p |- ( ph -> E. f ( f : C --> A /\ A. x e. C x e. D ) ) $=
        ( wcel cvv vy vk vc cv wrex wral wf wa wex cmpt crn wceq simplr wb eqid
        vex elrnmpt ax-mp sylib nfv nfcri nfan nfcv nfmpt1 nfrn nfel wi simpllr
        simpr eleqtrd ex reximdai mpd cuni ciun ralrimiva dfiun3g eqtrid eleq2d
        syl biimpa eluni2 r19.29a nfcsb1v csbeq1a cbvmptf mptexg eqeltrid rnexg
        csb uniexg 4syl eqeltrd raleqdv feq2d anbi12d exbidv imbi12d cfv ac6sf2
        id vtoclg ) ABUDZDSZHCUEZBEUFZECGUDZUGZXCFSZBEUFZUHZGUIZAXEBEAXCESZUHZX
        CUAUDZSZXEUAHCDUJZUKZXNXOXRSZUHZXPUHZXODULZHCUEZXEYAXSYCXNXSXPUMXOTSXSY
        CUNUAUPHCDXOXQTXQUOUQURUSYAYBXDHCXTXPHXNXSHAXMHAHUTHBENVAVBHXOXRHXOVCHX
        QHCDVDVEVFVBXPHUTVBYAHUDZCSZYBXDVGYAYEUHZYBXDYFYBUHXCXODXTXPYEYBVHYFYBV
        IVJVKVKVLVMXNXCXRVNZSZXPUAXRUEAXMYHAEYGXCAEHCDVOZYGPADJSZHCUFYIYGULAYJH
        CRVPHCDJVQVTVRZVSWAUAXCXRWBUSWCVPAETSXFXLVGZAEYGTYKACISZXQTSXRTSYGTSKYM
        XQUBCHUBUDZDWJZUJTHUBCDYOMUBCVCUBDVCHYNDWDHYNDWEWFUBCYOIWGWHXQTWIXRTWKW
        LWMXEBUCUDZUFZYPCXGUGZXIBYPUFZUHZGUIZVGYLUCETYPEULZYQXFUUAXLUUBXEBYPEUU
        BXAZWNUUBYTXKGUUBYRXHYSXJUUBYPECXGUUCWOUUBXIBYPEUUCWNWPWQWRXDXIBHYPCGMH
        BFOVAUCUPYDXCXGWSULDFXCQVSWTXBVTVM $.
    $}

    $d f j k y $.  $d f g k x y A $.  $d f g k x y B $.  $d g j k x ph $.
    $d j W $.
    aciunf1lem.1 $e |- ( ( ph /\ j e. A ) -> B e. W ) $.
    $( Choice in an index union.  (Contributed by Thierry Arnoux,
       8-Nov-2019.) $)
    aciunf1lem $p |- ( ph
      -> E. f ( f : U_ j e. A B -1-1-> U_ j e. A ( { j } X. B )
            /\ A. x e. U_ j e. A B ( 2nd ` ( f ` x ) ) = x ) ) $=
      ( vk cfv wcel wral wa wceq nfcv cvv vg vy ciun cv wf csb csn cxp wf1 c2nd
      wex nfiu1 nfcsb1v eqid csbeq1a acunirnmpt2f cop cmpt wi nfv nfan nff nfel
      nfralw wrex simplr simpld ad2antrr simpllr ffvelcdmd fvex snid a1i simprd
      nfra1 simpr rsp sylc jca opelxp sylibr sneq csbeq1 xpeq12d eleq2d syl2anc
      rspcev eliun nfxp cbvrexfw bitri bilani r19.29af2 ex ralrimi opth simprbi
      vex rgen2w fveq2 id opeq12d f1mpt opex fvmpt2 mpan2 syl fveq2d op2nd nfim
      eqtrdi eleq1w anbi2d eleq1d imbi12d chvarfv cbviunf iunexg eqeltrid f1eq1
      ralrimiva mptexg nfmpt1 nfeq fveq1 fveqeq2d ralbid spcegv 3syl adantr mpd
      anbi12d exlimddv ) AFCDUCZCUAUDZUEZBUDZFYQYONZDUFZOZBYNPZQZYNFCFUDZUGZDUH
      ZUCZEUDZUIZYQUUGNZUJNYQRZBYNPZQZEUKZUAABCDYNYSUAFGHIJKFCDULZFYRDUMZYNUNFY
      RDUOLUPAUUBQZYNUUFBYNYRYQUQZURZUIZYQUURNZUJNZYQRZBYNPZQZUUMUUPUUSUVCUUPUU
      QUUFOZBYNPZUUQUBUDZYONZUVGUQZRZYQUVGRZUSZUBYNPBYNPZQUUSUUPUVFUVMUUPUVEBYN
      AUUBBABUTYPUUABYPBUTYTBYNVOVAVAZUUPYQYNOZUVEUUPUVOQZYQDOZUVEFCUUPUVOFAUUB
      FAFUTZYPUUAFFYNCYOFYOSUUNKVBYTFBYNUUNFYQYSFYQSZUUOVCVDVAVAFYQYNUVSUUNVCVA
      FUUQUUFFUUQSZFCUUEULVCUVPUUCCOZQUVQQZUUQMUDZUGZFUWCDUFZUHZOZMCVEZUVEUWBYR
      COUUQYRUGZYSUHZOZUWHUWBYNCYQYOUVPYPUWAUVQUVPYPUUAAUUBUVOVFZVGVHUUPUVOUWAU
      VQVIVJUWBYRUWIOZYTQUWKUWBUWMYTUWMUWBYRYQYOVKZVLVMUVPYTUWAUVQUVPUUAUVOYTUV
      PYPUUAUWLVNUUPUVOVPZYTBYNVQVRVHVSYRYQUWIYSVTWAUWGUWKMYRCUWCYRRZUWFUWJUUQU
      WPUWDUWIUWEYSUWCYRWBFUWCYRDWCWDWEWGWFUVEUUQUUEOZFCVEUWHFUUQCUUEWHUWQUWGFM
      CKMCSZUWQMUTFUUQUWFUVTFUWDUWEFUWDSFUWCDUMZWIVCUUCUWCRZUUEUWFUUQUWTUUDUWDD
      UWEUUCUWCWBFUWCDUOZWDWEWJWKWAUVOUVQFCVEUUPFYQCDWHWLWMWNWOUVMUUPUVLBUBYNYN
      UVJYRUVHRUVKYRYQUVHUVGUWNBWRZWPWQWSVMVSBUBYNUUFUUQUVIUURUURUNZUVKYRUVHYQU
      VGYQUVGYOWTUVKXAXBXCWAUUPUVBBYNUVNUUPUVOUVBUVPUVAUUQUJNYQUVPUUTUUQUJUVPUV
      OUUTUUQRZUWOUVOUUQTOUXDYRYQXDBYNUUQTUURUXCXEXFXGXHYRYQUWNUXBXIXKWNWOVSAUV
      DUUMUSZUUBAYNTOZUURTOUXEACGOZUWEHOZMCPZUXFIAUXHMCAUWAQZDHOZUSAUWCCOZQZUXH
      USFMUXMUXHFAUXLFUVRFUWCCFUWCSKVCVAFUWEHUWSFHSVCXJUWTUXJUXMUXKUXHUWTUWAUXL
      AFMCXLXMUWTDUWEHUXAXNXOLXPYAUXGUXIQYNMCUWEUCTFMCDUWEKUWRMDSUWSUXAXQMCUWEG
      HXRXSWFBYNUUQTYBUULUVDEUURTUUGUURRZUUHUUSUUKUVCYNUUFUUGUURXTUXNUUJUVBBYNB
      UUGUURBUUGSBYNUUQYCYDUXNUUIUUTYQUJYQUUGUURYEYFYGYLYHYIYJYKYM $.
  $}

  ${
    $d A j k f $.  $d B f k $.  $d W j $.  $d f j k ph $.
    aciunf1.0 $e |- ( ph -> A e. V ) $.
    aciunf1.1 $e |- ( ( ph /\ j e. A ) -> B e. W ) $.
    $( Choice in an index union.  (Contributed by Thierry Arnoux,
       4-May-2020.) $)
    aciunf1 $p |- ( ph
        -> E. f ( f : U_ j e. A B -1-1-> U_ j e. A ( { j } X. B )
           /\ A. k e. U_ j e. A B ( 2nd ` ( f ` k ) ) = k ) ) $=
      ( c0 crab ciun cv wceq wral wa wcel eqidd wtru wne csn cxp wf1 cfv ssrab2
      wex cvv ssexg sylancr rabid bilani simprd nfrab1 simpld syldan aciunf1lem
      c2nd wss cdif nfv nfcv nfdif wn difrab rabtru difeq1i truan bitr4i rabbii
      df-ne 3eqtr3i a1i iuneq12df ralrimiva iunxdif3 syl eqtr3d xpeq2d f1eq123d
      xp0 eqtrdi raleqdv anbi12d exbidv mpbid ) AECKUAZEBLZCMZEWHENZUBZCUCZMZDN
      ZUDZFNZWNUEURUEWPOZFWIPZQZDUGEBCMZEBWLMZWNUDZWQFWTPZQZDUGAFWHCDEUHHAWHBUS
      BGRWHUHRWGEBUFIWHBGUIUJAWJWHRZQZWJBRZWGXEXGWGQAWGEBUKULZUMWGEBUNZAXEXGCHR
      XFXGWGXHUOJUPUQAWSXDDAWOXBWRXCAWIWTWMXAWNWNAWNSAEBCKOZEBLZUTZCMZWIWTAEXLW
      HCCAEVAZEBXKEBVBZXJEBUNZVCZXIXLWHOATEBLZXKUTTXJVDZQZEBLXLWHTXJEBVEXRBXKEB
      XOVFVGXTWGEBXTXSWGXSVHCKVKVIVJVLVMZACSVNAXJEXKPXMWTOAXJEXKAWJXKRZQZXGXJYB
      XGXJQAXJEBUKULUMZVOEBCXKXPVPVQVRZAEXLWLMZWMXAAEXLWHWLWLXNXQXIYAAWLSVNAWLK
      OZEXKPYFXAOAYGEXKYCWLWKKUCKYCCKWKYDVSWKWAWBVOEBWLXKXPVPVQVRVTAWQFWIWTYEWC
      WDWEWF $.
  $}

  ${
    $d a x y A $.  $d a x y B $.  $d a x y C $.  $d a x y F $.  $d a x y G $.
    $d a N $.  $d a x y R $.  $d a x y ph $.
    ofoprabco.1 $e |- F/_ a M $.
    ofoprabco.2 $e |- ( ph -> F : A --> B ) $.
    ofoprabco.3 $e |- ( ph -> G : A --> C ) $.
    ofoprabco.4 $e |- ( ph -> A e. V ) $.
    ofoprabco.5 $e |- ( ph ->
                            M = ( a e. A |-> <. ( F ` a ) , ( G ` a ) >. ) ) $.
    ofoprabco.6 $e |- ( ph -> N = ( x e. B , y e. C |-> ( x R y ) ) ) $.
    $( Function operation as a composition with an operation.  (Contributed by
       Thierry Arnoux, 4-Jun-2017.) $)
    ofoprabco $p |- ( ph -> ( F oF R G ) = ( N o. M ) ) $=
      ( cvv cv cfv cmpt co ccom cof wcel cop ffvelcdmda opelxpi syl2anc fvmpt2d
      cxp fveq2d wceq df-ov a1i cmpo adantr simprl simprr oveq12d ovexd 3eqtr2d
      wa ovmpod mpteq2dva wral ovex rgen2w eqid fmpo mpbi mpbiri fmpt3d fcomptf
      wf feq1d feqmptd offval2 3eqtr4rd ) AMDMUAZJUBZKUBZUCZMDWBHUBZWBIUBZGUDZU
      CKJUEZHIGUFUDAMDWDWHAWBDUGZVEZWDWFWGUHZKUBZWFWGKUDZWHWKWCWLKAMDWLJEFUMZRW
      KWFEUGWGFUGWLWOUGADEWBHOUIZADFWBIPUIZWFWGEFUJUKZULUNWNWMUOWKWFWGKUPUQWKBC
      WFWGEFBUAZCUAZGUDZWHKTAKBCEFXAURZUOWJSUSWKWSWFUOZWTWGUOZVEVEWSWFWTWGGWKXC
      XDUTWKXCXDVAVBWPWQWKWFWGGVCVFVDVGAWOTKVQZDWOJVQWIWEUOAXEWOTXBVQZXATUGZCFV
      HBEVHXFXGBCEFWSWTGVIVJBCEFXATXBXBVKVLVMAWOTKXBSVRVNAMDWLWOJRWRVOMKJDWOTNV
      PUKAMDWFWGGHILEFQWPWQAMDEHOVSAMDFIPVSVTWA $.
  $}

  ${
    $d p q s x y A $.  $d s x y B $.  $d s x y C $.  $d p q D $.
    $d p q s x y F $.  $d p q s x y G $.  $d p q s x y R $.  $d p q s x y ph $.
    ofpreima.1 $e |- ( ph -> F : A --> B ) $.
    ofpreima.2 $e |- ( ph -> G : A --> C ) $.
    ofpreima.3 $e |- ( ph -> A e. V ) $.
    ofpreima.4 $e |- ( ph -> R Fn ( B X. C ) ) $.
    $( Express the preimage of a function operation as a union of preimages.
       (Contributed by Thierry Arnoux, 8-Mar-2018.) $)
    ofpreima $p |- ( ph -> ( `' ( F oF R G ) " D ) = U_ p e. ( `' R " D )
         ( ( `' F " { ( 1st ` p ) } ) i^i ( `' G " { ( 2nd ` p ) } ) ) ) $=
      ( vs vq cfv wceq wcel wa vx vy cof co ccnv cima cv cop cmpt c1st csn c2nd
      cin ciun ccom nfmpt1 eqidd cxp wfn cmpo fnov sylib ofoprabco cnveqd cnvco
      eqtrdi imaeq1d imaco wbr wrex cab dfima2 vex cdm wfun wb funmpt funbrfv2b
      brcnv ax-mp dmmpti eleq2i anbi1i bitri fveq2 opeq12d fvmpt eqeq1d pm5.32i
      opex eqid 3bitri rexbii abbii nfv nfab1 nfcv wf ffn fniniseg 3syl anbi12d
      eliun elin anandi 3bitr4g adantr cnvimass fndmd sselda 1st2nd2 eqeq2 fvex
      sseqtrid opth bitrdi anbi2d bitr4d abid bitr4di bitr2id eqrd eqtrid eqtrd
      rexbidva ) AGHFUCUDZUEZEUFZOBOUGZGQZYIHQZUHZUIZUEZFUEZEUFZUFZJYPGUEJUGZUJ
      QZUKUFZHUEYRULQZUKUFZUMZUNZAYHYNYOUOZEUFYQAYGUUEEAYGFYMUOZUEUUEAYFUUFAUAU
      BBCDFGHYMFIOOBYLUPKLMAYMUQAFCDURZUSFUAUBCDUAUGUBUGFUDUTRNUAUBCDFVAVBVCVDF
      YMVEVFVGYNYOEVHVFAYQYRPUGZYNVIZJYPVJZPVKZUUDJPYNYPVLAUUKUUHBSZUUHGQZUUHHQ
      ZUHZYRRZTZJYPVJZPVKZUUDUUJUURPUUIUUQJYPUUIUUHYRYMVIZUULUUHYMQZYRRZTZUUQYR
      UUHYMJVMPVMVSUUTUUHYMVNZSZUVBTZUVCYMVOUUTUVFVPOBYLVQUUHYRYMVRVTUVEUULUVBU
      VDBUUHOBYLYMYJYKWJYMWKZWAWBWCWDUULUVBUUPUULUVAUUOYROUUHYLUUOBYMYIUUHRYJUU
      MYKUUNYIUUHGWEYIUUHHWEWFUVGUUMUUNWJWGWHWIWLWMWNAPUUSUUDAPWOUURPWPPUUDWQUU
      HUUDSUUHUUCSZJYPVJZAUUHUUSSZJUUHYPUUCXCAUVIUURUVJAUVHUUQJYPAYRYPSZTZUVHUU
      LUUMYSRZUUNUUARZTZTZUUQAUVHUVPVPUVKAUUHYTSZUUHUUBSZTUULUVMTZUULUVNTZTUVHU
      VPAUVQUVSUVRUVTABCGWRGBUSUVQUVSVPKBCGWSBYSUUHGWTXAABDHWRHBUSUVRUVTVPLBDHW
      SBUUAUUHHWTXAXBUUHYTUUBXDUULUVMUVNXEXFXGUVLUUPUVOUULUVLUUPUUOYSUUAUHZRZUV
      OUVLYRUUGSYRUWARUUPUWBVPAYPUUGYRAFVNYPUUGFEXHAUUGFNXIXNXJYRCDXKYRUWAUUOXL
      XAUUMUUNYSUUAUUHGXMUUHHXMXOXPXQXRYEUURPXSXTYAYBYCYCYD $.

    $( Express the preimage of a function operation as a union of preimages.
       This version of ~ ofpreima iterates the union over a smaller set.
       (Contributed by Thierry Arnoux, 8-Mar-2018.) $)
    ofpreima2 $p |- ( ph -> ( `' ( F oF R G ) " D ) =
         U_ p e. ( ( `' R " D ) i^i ( ran F X. ran G ) )
         ( ( `' F " { ( 1st ` p ) } ) i^i ( `' G " { ( 2nd ` p ) } ) ) ) $=
      ( cin ciun wceq eqtrdi c0 wcel cof co ccnv cima crn cxp c1st cfv csn c2nd
      cv cun ofpreima inundif iuneq1 ax-mp iunxun eqtr3i wa wo wn simpr eldifbd
      cop wi cdm cnvimass fndmd sseqtrid ssdifssd sselda 1st2nd2 elxp6 simplbi2
      cdif 3syl mtod ianor sylib disjsn orbi12i sylibr wf wfn ffnd dffn3 adantr
      fimacnvdisj ineq1 0in syl ex ineq2 in0 jaao syl2an2r iuneq2dv iun0 uneq2d
      mpd un0 eqtrd ) AGHFUAUBUCEUDZJFUCEUDZGUEZHUEZUFZOZGUCJUKZUGUHZUIZUDZHUCX
      IUJUHZUIZUDZOZPZJXDXGVOZXPPZULZXQAXCJXDXPPZXTABCDEFGHIJKLMNUMJXHXRULZXPPZ
      YAXTYBXDQYCYAQXDXGUNJYBXDXPUOUPJXHXRXPUQURRAXTXQSULXQAXSSXQAXSJXRSPSAJXRX
      PSAXIXRTZUSZXEXKOSQZXFXNOSQZUTZXPSQZYEXJXETZVAZXMXFTZVAZUTZYHYEYJYLUSZVAY
      NYEYOXIXGTZYEXIXDXGAYDVBVCYEXICDUFZTXIXJXMVDQZYOYPVEAXRYQXIAXDYQXGAFVFXDY
      QFEVGAYQFNVHVIVJVKXICDVLYPYRYOXIXEXFVMVNVPVQYJYLVRVSYFYKYGYMXEXJVTXFXMVTW
      AWBABXEGWCZYDBXFHWCZYHYIVEAGBWDYSABCGKWEBGWFVSAYTYDAHBWDYTABDHLWEBHWFVSWG
      YSYFYIYTYGYSYFYIYSYFUSXLSQZYIBXEXKGWHUUAXPSXOOSXLSXOWIXOWJRWKWLYTYGYIYTYG
      USXOSQZYIBXFXNHWHUUBXPXLSOSXOSXLWMXLWNRWKWLWOWPWTWQJXRWRRWSXQXARXB $.
  $}

  ${
    $d x y z $.  $d y F $.  $d y z ph $.
    funcnv5mpt.0 $e |- F/ x ph $.
    funcnv5mpt.1 $e |- F/_ x A $.
    funcnv5mpt.2 $e |- F/_ x F $.
    funcnv5mpt.3 $e |- F = ( x e. A |-> B ) $.
    funcnv5mpt.4 $e |- ( ( ph /\ x e. A ) -> B e. V ) $.
    ${
      $d y z A $.  $d y z B $.  $d x y C $.
      funcnv5mpt.5 $e |- ( x = z -> B = C ) $.
      $( Two ways to say that a function in maps-to notation is single-rooted.
         (Contributed by Thierry Arnoux, 1-Mar-2017.) $)
      funcnv5mpt $p |- ( ph -> ( Fun `' F <->
                                A. x e. A A. z e. A ( x = z \/ B =/= C ) ) ) $=
        ( vy cv wceq wal wral wi ccnv wfun wrmo wne wo funcnvmpt wa wcel wn wex
        nne eqvincg syl bitrid imbi1d orcom df-or bitri 3bitr4g ralbidv ralcom4
        19.23v bitrdi ralbida nfcv nfv eqeq2d rmo4f albii bitr4i bitr4di bitr4d
        wb ) AGUAUBOPZEQZBDUCZORZBPZCPQZEFUDZUEZCDSZBDSZABODEGHIJKLMUFAWCVOVNFQ
        ZUGZVSTZCDSZORZBDSZVQAWBWHBDIAVRDUHUGZWBWFORZCDSWHWJWAWKCDWJVTUIZVSTZWE
        OUJZVSTWAWKWJWLWNVSWLEFQZWJWNEFUKWJEHUHWOWNVMMOEFHULUMUNUOWAVTVSUEWMVSV
        TUPVTVSUQURWEVSOVBUSUTWFCODVAVCVDVQWGBDSZORWIVPWPOVOWDBCDJCDVEWDBVFVSEF
        VNNVGVHVIWGBODVAVJVKVL $.
    $}

    ${
      $d i j x $.  $d i j A $.  $d i j B $.  $d i F $.  $d x V $.  $d i j ph $.
      $( Two ways to say that a function in maps-to notation is single-rooted.
         (Contributed by Thierry Arnoux, 2-Mar-2017.) $)
      funcnv4mpt $p |- ( ph -> ( Fun `' F <->
        A. i e. A A. j e. A ( i = j \/ [_ i / x ]_ B =/= [_ j / x ]_ B ) ) ) $=
        ( cv csb nfcv cmpt wcel wa wsb nfcsb1v csbeq1a cbvmptf eqtri sbimi nfel
        nfv nfan weq eleq1w anbi2d sbiev eleq1d 3imtr3i csbeq1 funcnv5mpt ) AEF
        CBENZDOZBFNZDOGHAEUGECPZEGPGBCDQECURQLBECDURJUTEDPBUQDUAZBUQDUBZUCUDABN
        CRZSZBETDHRZBETAUQCRZSZURHRZVDVEBEMUEVDVGBEAVFBIBUQCBUQPJUFUHBEUIZVCVFA
        BECUJUKULVEVHBEBURHVABHPUFVIDURHVBUMULUNBUQUSDUOUP $.
    $}
  $}

  ${
    preimane.f $e |- ( ph -> Fun F ) $.
    preimane.x $e |- ( ph -> X =/= Y ) $.
    preimane.y $e |- ( ph -> X e. ran F ) $.
    preimane.1 $e |- ( ph -> Y e. ran F ) $.
    $( Different elements have different preimages.  (Contributed by Thierry
       Arnoux, 7-May-2023.) $)
    preimane $p |- ( ph -> ( `' F " { X } ) =/= ( `' F " { Y } ) ) $=
      ( csn cima wne wceq syl cin funimacnv wss snssd dfss2 sylib eqtrd ccnv wi
      crn wcel sneqrg necon3d mpd wfun 3netr4d imaeq2 necon3i ) ABBUAZCIZJZJZBU
      LDIZJZJZKUNUQKAUMUPUOURACDKUMUPKFAUMUPCDACBUCZUDUMUPLCDLUBGCDUSUEMUFUGAUO
      UMUSNZUMABUHZUOUTLEUMBOMAUMUSPUTUMLACUSGQUMUSRSTAURUPUSNZUPAVAURVBLEUPBOM
      AUPUSPVBUPLADUSHQUPUSRSTUIUNUQUOURUNUQBUJUKM $.
  $}

  ${
    $d A f t u v x y z $.  $d B f t u v x y z $.  $d F f k t u v x y z $.
    $d V f t u v y z $.
    $( Choose a set ` x ` containing a preimage of each element of a given set
       ` B ` .  (Contributed by Thierry Arnoux, 7-May-2023.) $)
    fnpreimac $p |- ( ( A e. V /\ F Fn A /\ B C_ ran F )
      -> E. x e. ~P A ( x ~~ B /\ ( F " x ) = B ) ) $=
      ( vy vf vz wcel wss cv cima cfv wral wa cen wceq cvv syl syl2anc vu vv vt
      vk wfn crn w3a ccnv csn cmpt cuni wf wex wbr cpw wrex cid c0 eqid elrnmpt
      wne wb simpr simpl3 sseldd inisegn0 sylib adantr eqnetrd r19.29an sylan2b
      elv ralrimiva simp2 simp1 jca fnex rnexg 3syl simp3 ssexd mptexg fvi 4syl
      raleqtrrdv fvex ac5b unieqd feq23d raleqdv anbi12d exbidv vex rnex simplr
      mpbid a1i frn nfv nfcv nfmpt1 nfrn nfuni nff nfan nfralw ad3antrrr cnvexg
      imaexg cnvimass fndmd sseqtrd elpwd ex ralrimi rnmptss sspwuni sstrd wf1o
      cdm wf1 wi wdisj ad5antr simpllr fveq2 id eleq12d rspcv imp anasss sylibr
      wfun f1f1orn f1oen3g ensymd ad2antrr ciun imaeq2 rspcev sndisj disjpreima
      fnfun sylancl disjrnmpt simp-4r disji syl122anc ralrimivva dff13 preimane
      eqeltrd sylancr necon4d sneq imaeq2d entr imass2 iunrnmptss cin funimacnv
      f1mpt imauni snssd dfss2 eqtrd iuneq2dv iunid eqtrdi ffund elrnmpt1s fdmd
      eqsstrid eleqtrrd fvelrn fniniseg simplbda fveqeq2 fvelimabd mpbird ssrdv
      eqssd breq1 eqeq1d exlimdv mpd ) BEIZDBUEZCDUFZJZUGZFCDUHZFKZUIZLZUJZUFZU
      WQUKZGKZULZHKZUWSMZUXAIZHUWQNZOZGUMZAKZCPUNZDUXGLZCQZOZABUOZUPZUWKUWQUQMZ
      UXNUKZUWSULZUXCHUXNNZOZGUMZUXFUWKUXAURVAZHUXNNUXSUWKUXTHUWQUXNUWKUXTHUWQU
      XAUWQIZUWKUXAUWOQZFCUPZUXTUYAUYCVBHFCUWOUXAUWPRUWPUSZUTVLUWKUYBUXTFCUWKUW
      MCIZOZUYBOUXAUWOURUYFUYBVCUYFUWOURVAZUYBUYFUWMUWIIUYGUYFCUWIUWMUWGUWHUWJU
      YEVDZUWKUYEVCZVEUWMDVFVGVHVIVJVKVMUWKCRIZUWPRIZUWQRIUXNUWQQUWKCUWIRUWKUWH
      UWGOZDRIZUWIRIUWKUWHUWGUWGUWHUWJVNZUWGUWHUWJVOVPZBEDVQZDRVRVSUWGUWHUWJVTZ
      WAZFCUWORWBZUWPRVRUWQRWCWDZWEHUXNGUWQUQWFWGSUWKUXRUXEGUWKUXPUWTUXQUXDUWKU
      XNUXOUWQUWRUWSUYTUWKUXNUWQUYTWHWIUWKUXCHUXNUWQUYTWJWKWLWPUWKUXEUXMGUWKUXE
      UXMUWKUWTUXDUXMUWKUWTOZUXDOZUWSUFZUXLIVUCCPUNZDVUCLZCQZOZUXMVUBVUCBRVUCRI
      VUBUWSGWMZWNWQVUBVUCUWRBVUBUWTVUCUWRJZUWKUWTUXDWOZUWQUWRUWSWRZSVUBUWQUXLJ
      ZUWRBJVUBUWOUXLIZFCNVULVUBVUMFCVUAUXDFUWKUWTFUWKFWSFUWQUWRUWSFUWSWTFUWPFC
      UWOXAXBZFUWQVUNXCXDXEUXCFHUWQVUNUXCFWSXFXEZVUBUYEVUMVUBUYEOZUWOBRVUPUYMUW
      LRIZUWORIZUWKUYMUWTUXDUYEUWKUYLUYMUYOUYPSZXGDRXHZUWLUWNRXIZVSZVUPUWODXTZB
      UWOVVCJVUPDUWNXJWQUWKVVCBQUWTUXDUYEUWKBDUYNXKXGXLXMXNXOFCUWOUXLUWPUYDXPSU
      WQBXQVGXRZXMVUBVUDVUFVUBVUCUWQPUNUWQCPUNVUDVUBUWQVUCVUBUWSRIUWQVUCUWSXSZU
      WQVUCPUNVUHVUBUWQUWRUWSYAZVVEVUBUWTUAKZUWSMZUBKZUWSMZQZVVGVVIQZYBZUBUWQNU
      AUWQNZOVVFVUBUWTVVNVUJVUBVVMUAUBUWQUWQVUBVVGUWQIZVVIUWQIZVVMVUBVVOOZVVPOZ
      VVKVVLVVRVVKOZHUWQUXAYCZVVOVVPVVHVVGIZVVHVVIIVVLVVSFCUWOYCZVVTVVSDYMZFCUW
      NYCVWBUWKVWCUWTUXDVVOVVPVVKUWKUWHVWCUYNBDUUCSZYDFCUUAFCUWNDUUBUUDFHCUWOUU
      ESVUBVVOVVPVVKYEZVVQVVPVVKWOZVVSVVOUXDVWAVWEVUAUXDVVOVVPVVKUUFZVVOUXDVWAU
      XCVWAHVVGUWQUXAVVGQZUXBVVHUXAVVGUXAVVGUWSYFVWHYGZYHYIYJTVVSVVHVVJVVIVVRVV
      KVCVVSVVPUXDVVJVVIIZVWFVWGVVPUXDVWJUXCVWJHVVIUWQUXAVVIQZUXBVVJUXAVVIUXAVV
      IUWSYFVWKYGZYHYIYJTUULHUWQUXAVVGVVIVVGVVIVVHVWIVWLUUGUUHXNYKUUIVPUAUBUWQU
      WRUWSUUJYLUWQUWRUWSYNSUWQVUCUWSRYOUUMYPVUBCUWQVUBUYKCUWQUWPXSZCUWQPUNUWKU
      YKUWTUXDUWKUYJUYKUYRUYSSYQVUBCRUWPYAZVWMVUBVURFCNZUWOUWLUCKZUIZLZQUWMVWPQ
      ZYBZUCCNZFCNZOVWNVUBVWOVXBVUBVURFCVUOVUBUYEVURVVBXNXOVUBVXAFCVUOVUBUYEVXA
      VUPVWTUCCVUPVWPCIZOZUWMVWPUWOVWRVXDUWMVWPVAZUWOVWRVAVXDVXEOZDUWMVWPUWKVWC
      UWTUXDUYEVXCVXEVWDYDVXDVXEVCVXFCUWIUWMUWKUWJUWTUXDUYEVXCVXEUYQYDZVUBUYEVX
      CVXEYEVEVXFCUWIVWPVXGVUPVXCVXEWOVEUUKXNUUNVMXNXOVPFUCCRUWOVWRUWPUYDVWSUWN
      VWQUWLUWMVWPUUOUUPZUVBYLCRUWPYNSCUWQUWPRYOTYPVUCUWQCUUQTVUBVUECVUBVUEDUWR
      LZCVUBUWTVUEVXIJZVUJUWTVUIVXJVUKVUCUWRDUURSSVUBVXIHUWQDUXALZYRZCHDUWQUVCU
      WKVXLCJUWTUXDUWKVXLFCDUWOLZYRZCUWKFHCUWOVXKVXMRUXAUWODYSUYFUYMVUQVURUWKUY
      MUYEVUSVHVUTVVAVSUUSUWKVXNFCUWNYRCUWKFCVXMUWNUYFVXMUWNUWIUUTZUWNUWKVXMVXO
      QZUYEUWKVWCVXPVWDUWNDUVASVHUYFUWNUWIJVXOUWNQUYFUWNCUWIUYFUWMCUYIUVDUYHXRU
      WNUWIUVEVGUVFUVGFCUVHUVIXLYQUVMXRVUBUCCVUEVUBVXCVWPVUEIZVUBVXCOZVXQUDKZDM
      VWPQZUDVUCUPZVXRVWRUWSMZVUCIZVYBDMVWPQZVYAVXRUWSYMVWRUWSXTZIVYCVXRUWQUWRU
      WSVUBUWTVXCVUJVHZUVJVXRVWRUWQVYEVXRVXCVWRRIZVWRUWQIZVUBVXCVCVXRVUQVYGUWKV
      UQUWTUXDVXCUWKUYMVUQVUSVUTSXGUWLVWQRXISFCUWOVWRVWPUWPRUYDVXHUVKTZVXRUWQUW
      RUWSVYFUVLUVNVWRUWSUVOTVXRUWHVYBVWRIZVYDUWKUWHUWTUXDVXCUYNXGZVXRVYHUXDVYJ
      VYIVUAUXDVXCWOVYHUXDVYJUXCVYJHVWRUWQUXAVWRQZUXBVYBUXAVWRUXAVWRUWSYFVYLYGY
      HYIYJTUWHVYJVYBBIVYDBVWPVYBDUVPUVQTVXTVYDUDVYBVUCVXSVYBVWPDUVRYTTVXRUDBVU
      CVWPDVYKVUBVUCBJVXCVVDVHUVSUVTXNUWAUWBVPUXKVUGAVUCUXLUXGVUCQZUXHVUDUXJVUF
      UXGVUCCPUWCVYMUXIVUECUXGVUCDYSUWDWKYTTYKXNUWEUWF $.
  $}

  ${
    $d p q F $.  $d p q X $.
    $( Exactly one point of a function's graph has a given first element.
       (Contributed by Thierry Arnoux, 1-Apr-2018.) $)
    fgreu $p |- ( ( Fun F /\ X e. dom F ) -> E! p e. F X = ( 1st ` p ) ) $=
      ( vq wfun cdm wcel wa cv c1st cfv wceq wral wrex cop syl2anc simpr eqtr4d
      wb cvv wreu funfvop c2nd wrel simplll funrel simplr 1st2nd simpllr opeq1d
      syl eqeltrrd funopfvb biimpar syl21anc opeq12d fveq2d fvex mpan2 ad3antlr
      op1stg eqtr2d impbida ralrimiva eqeq2 bibi2d ralbidv rspcev reu6 sylibr )
      AEZBAFZGZHZBCIZJKZLZVODIZLZSZCAMZDANZVQCAUAVNBBAKZOZAGVQVOWDLZSZCAMZWBBAU
      BVNWFCAVNVOAGZHZVQWEWIVQHZVOVPVOUCKZOZWDWJAUDZWHVOWLLWJVKWMVKVMWHVQUEZAUF
      UKVNWHVQUGZVOAUHPZWJBVPWCWKWIVQQZWJVKVMBWKOZAGZWCWKLZWNVKVMWHVQUIWJVOWRAW
      JVOWLWRWPWJBVPWKWQUJRWOULVNWTWSBWKAUMUNUOUPRWIWEHZVPWDJKZBXAVOWDJWIWEQUQV
      MXBBLZVKWHWEVMWCTGXCBAURBWCVLTVAUSUTVBVCVDWAWGDWDAVRWDLZVTWFCAXDVSWEVQVRW
      DVOVEVFVGVHPVQCDAVIVJ $.
  $}

  ${
    $d p q r A $.  $d p q Y $.
    $( If the converse of a relation ` A ` is a function, exactly one point of
       its graph has a given second element (that is, function value).
       (Contributed by Thierry Arnoux, 1-Apr-2018.) $)
    fcnvgreu $p |- ( ( ( Rel A /\ Fun `' A ) /\ Y e. ran A )
      -> E! p e. A Y = ( 2nd ` p ) ) $=
      ( vq vr ccnv wa wcel cv c2nd cfv wceq wreu c1st wb csn cxp simpr syl12anc
      cuni wrel wfun crn cdm df-rn fgreu adantll sylan2b cop cnvcnvss cnvssrndm
      eleq2i sseli dfdm4 xpeq12i eleqtrdi 2nd1st eqcomd relcnv cnvf1olem simpld
      syl mpan mpdan sselid adantl wral wrex simpll wss relssdmrn adantr sselda
      a1i simplr ad2antlr simprd sneqd cnveqd unieqd ad2antrr 3eqtr2d ralrimiva
      impbida eqeq2 bibi2d ralbidv rspcev syl2anc sylibr op2ndd eqeq2d reuxfr1d
      reu6 fvex mpbird ) AUAZAFZUBZGZBAUCZHZGBCIZJKZLZCAMZBDIZNKZLZDWRMZXBWTBWR
      UDZHZXJXAXKBAUEZULWSXLXJWQWRBDUFUGUHWTXFXJOXBWTXEXICDXGJKZXHUIZAWRXGWRHZX
      OAHWTXPWRFZAXOAUJXPXOXGPZFZTZLZXOXQHZXPXTXOXPXGXKWRUCZQZHXTXOLZXPXGXAAUDZ
      QZYDWRYGXGAUKUMXAXKYFYCXMAUNUOUPXGXKYCUQVBZURZWRUAZXPYAGZYBAUSZYJYKGZYBXG
      XOPZFZTZLZWRXGXOUTZVAVCVDVEVFWTXCAHZGZXCXOLZXGEIZLZOZDWRVGZEWRVHZUUADWRMY
      TXDXCNKUIZWRHZUUAXGUUGLZOZDWRVGZUUFYTWQYSUUGXCPZFZTZLZUUHWQWSYSVIZWTYSRZY
      TUUNUUGYTXCYFXAQZHUUNUUGLZWTAUURXCWQAUURVJWSAVKVLVMXCYFXAUQVBZURZWQYSUUOG
      GZUUHXCUUGPZFZTZLZAXCUUGUTZVASYTUUJDWRYTXPGZUUAUUIUVHUUAGZXGYPUUNUUGUVIYJ
      XPYAYQYJUVIYLVNYTXPUUAVOXPYAYTUUAYIVPYMYBYQYRVQSUVIUUMYOUVIUULYNUVIXCXOUV
      HUUARVRVSVTYTUUSXPUUAUUTWAWBUVHUUIGZXCUVEXTXOYTUVFXPUUIYTWQYSUUOUVFUUPUUQ
      UVAUVBUUHUVFUVGVQSWAUVJXSUVDUVJXRUVCUVJXGUUGUVHUUIRVRVSVTXPYEYTUUIYHVPWBW
      DWCUUEUUKEUUGWRUUBUUGLZUUDUUJDWRUVKUUCUUIUUAUUBUUGXGWEWFWGWHWIUUADEWRWNWJ
      UUAXEXIOWTUUAXDXHBXNXHXCXGJWOXGNWOWKWLVFWMVLWP $.
  $}

  ${
    $d y z A $.  $d z B $.  $d z C $.  $d x y z D $.  $d z F $.
    rnmposs.1 $e |- F = ( x e. A , y e. B |-> C ) $.
    $( The range of an operation given by the maps-to notation as a subset.
       (Contributed by Thierry Arnoux, 23-May-2017.) $)
    rnmposs $p |- ( A. x e. A A. y e. B C e. D -> ran F C_ D ) $=
      ( vz wcel wral crn cv wceq wrex rnmpo eqabri wa 2r19.29 wi eleq1 biimparc
      a1i rexlimivv syl ex biimtrid ssrdv ) EFJZBDKACKZIGLZFIMZUKJULENZBDOACOZU
      JULFJZUNIUKABICDEGHPQUJUNUOUJUNRUIUMRZBDOACOUOUIUMABCDSUPUOABCDUPUOTAMCJB
      MDJRUMUOUIULEFUAUBUCUDUEUFUGUH $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d C y $.
    $( Deduce subset relation of mapping-to function graphs from a subset
       relation of domains.  Alternative proof of ~ mptss .  (Contributed by
       Thierry Arnoux, 30-May-2020.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    mptssALT $p |- ( A C_ B -> ( x e. A |-> C ) C_ ( x e. B |-> C ) ) $=
      ( vy wss cv wcel wceq wa copab cmpt ssel anim1d ssopab2dv df-mpt 3sstr4g
      ) BCFZAGZBHZEGDIZJZAEKSCHZUAJZAEKABDLACDLRUBUDAERTUCUABCSMNOAEBDPAECDPQ
      $.
  $}

  ${
    $d x y z A $.  $d x y z R $.
    $( Alternative definition of the converse of a relation.  (Contributed by
       Thierry Arnoux, 31-Mar-2018.) $)
    dfcnv2 $p |- ( ran R C_ A ->
      `' R = U_ x e. A ( { x } X. ( `' R " { x } ) ) ) $=
      ( vz vy crn wss ccnv cv csn cima cxp ciun relcnv wrel wral wa vex bitr4di
      wcel relxp rgenw reliun mpbir cop cdm opeldm df-rn eleqtrrdi ssel2 sylan2
      ex pm4.71rd elimasn anbi2i weq sneq imaeq2d opeliunxp2 eqrelrdv ) CFZBGZD
      ECHZABAIZJZVCVEKZLZMZCNVHOVGOZABPVIABVEVFUAUBABVGUCUDVBDIZEIZUEZVCTZVJBTZ
      VKVCVJJZKZTZQZVLVHTVBVMVNVMQVRVBVMVNVBVMVNVMVBVJVATVNVMVJVCUFVAVJVKVCDRZE
      RZUGCUHUIVABVJUJUKULUMVQVMVNVCVJVKVSVTUNUOSABVFVJVKVPADUPVEVOVCVDVJUQURUS
      SUT $.
  $}

  ${
    $d A x $.
    partfun2.1 $e |- D = { x e. A | ph } $.
    $( Rewrite a function defined by parts, using a mapping and an if
       construct, into a union of functions on disjoint domains.  See also
       ~ partfun and ~ ifmpt2v .  (Contributed by Thierry Arnoux,
       25-Jan-2026.) $)
    partfun2 $p |- ( x e. A |-> if ( ph , B , C ) )
                  = ( ( x e. D |-> B ) u. ( x e. ( A \ D ) |-> C ) ) $=
      ( cv wcel cif cmpt cin cdif cun partfun reqabi baib ifbid mpteq2ia wss
      wceq ssrab3 sseqin2 mpbi mpteq1i uneq1i 3eqtr3i ) BCBHZFIZDEJZKBCFLZDKZBC
      FMEKZNBCADEJZKBFDKZUMNBCFDEOBCUJUNUHCIZUIADEUIUPAABFCGPQRSULUOUMBUKFDFCTU
      KFUAABCFGUBFCUCUDUEUFUG $.
  $}

  $( The range of a restriction to a singleton is a singleton.  See
     ~ dmressnsn .  (Contributed by Thierry Arnoux, 25-Jan-2026.) $)
  rnressnsn $p |- ( ( Fun F /\ A e. dom F ) -> ran ( F |` { A } ) = { ( F ` A )
    } ) $=
    ( wfun cdm wcel wa csn cres crn cfv cop wfn wceq funfn fnressn sylanb rneqd
    rnsnopg adantl eqtrd ) BCZABDZEZFZBAGHZIAABJZKGZIZUFGZUDUEUGUABUBLUCUEUGMBN
    UBABOPQUCUHUIMUAAUFUBRST $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Operations - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d w x y z A $.  $d w y z B $.  $d w C $.  $d w z D $.
    mpomptxf.0 $e |- F/_ x C $.
    mpomptxf.1 $e |- F/_ y C $.
    mpomptxf.2 $e |- ( z = <. x , y >. -> C = D ) $.
    $( Express a two-argument function as a one-argument function, or
       vice-versa.  In this version ` B ( x ) ` is not assumed to be constant
       w.r.t ` x ` .  (Contributed by Mario Carneiro, 29-Dec-2014.)  (Revised
       by Thierry Arnoux, 31-Mar-2018.) $)
    mpomptxf $p |- ( z e. U_ x e. A ( { x } X. B ) |-> C ) =
      ( x e. A , y e. B |-> D ) $=
      ( vw cv wcel wceq wa copab wex nfeq2 19.41 eqtr4i ciun cmpt df-mpt coprab
      csn cxp df-mpo cop eliunxp anbi1i exbii bitri anass eqeq2d anbi2d pm5.32i
      cmpo 2exbii 3bitr2i opabbii dfoprab2 ) CADALZUEEUFUAZFUBCLZVCMZKLZFNZOZCK
      PZABDEGUQZCKVCFUCVJVBDMBLZEMOZVFGNZOZABKUDZVIABKDEGUGVIVDVBVKUHNZVNOZBQAQ
      ZCKPVOVHVRCKVHVPVLOZBQZAQZVGOZVSVGOZBQZAQZVRVEWAVGABDEVDUIUJWEVTVGOZAQWBW
      DWFAVSVGBBVFFIRSUKVTVGAAVFFHRSULWCVQABWCVPVLVGOZOVQVPVLVGUMVPWGVNVPVGVMVL
      VPFGVFJUNUOUPULURUSUTVNABKCVATTT $.
  $}

  ${
    $d F f g x $.  $d R f g x $.
    $( Function operation with the empty function.  (Contributed by Thierry
       Arnoux, 27-May-2025.) $)
    of0r $p |- ( F oF R (/) ) = (/) $=
      ( vf vg vx cvv wcel c0 cof co wceq cv cdm cin cfv cmpt a1i dmeq mpteq1d
      wa cmpo df-of ineqan12d adantl dm0 ineq2i in0 eqtri mpt0 3eqtrd id ovmpod
      0ex reldmmpo ovprc1 pm2.61i ) BFGZBHAIZJHKUQCDBHFFECLZMZDLZMZNZELZUSOVDVA
      OAJZPZHURFURCDFFVFUAKUQEACDUBZQUQUSBKZVAHKZTZTZVFEBMZHMZNZVEPZEHVEPZHVJVF
      VOKUQVJEVCVNVEVHVIUTVLVBVMUSBRVAHRUCSUDVKEVNHVEVNHKVKVNVLHNHVMHVLUEUFVLUG
      UHQSVPHKVKEVEUIQUJUQUKHFGUQUMQZVQULBHURCDFFVFURVGUNUOUP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The mapping operation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Support of a function
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A k x y $.  $d B k x y z $.  $d D x y $.  $d F x y z $.  $d G k x y z $.
    $d Z k x y z $.  $d k ph x y z $.
    suppovss.f $e |- F = ( x e. A , y e. B |-> C ) $.
    suppovss.g $e |- G = ( x e. A |-> ( y e. B |-> C ) ) $.
    suppovss.a $e |- ( ph -> A e. V ) $.
    suppovss.b $e |- ( ph -> B e. W ) $.
    suppovss.z $e |- ( ph -> Z e. D ) $.
    suppovss.1 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> C e. D ) $.
    $( A bound for the support of an operation.  (Contributed by Thierry
       Arnoux, 19-Jul-2023.) $)
    suppovss $p |- ( ph -> ( F supp Z ) C_ ( ( G supp ( B X. { Z } ) ) X. U_ k
       e. ( G supp ( B X. { Z } ) ) ( ( G ` k ) supp Z ) ) ) $=
      ( wcel vz cxp csn csupp co cv cfv ciun wral wf ralrimivva fmpo sylib cdif
      wa cop simpr fveq2d df-ov simpllr eldifad simplr simplll syl12anc ovmpt4g
      wceq syl3anc eqtr3id cvv cmpt adantr mptexd fmptd ssidd a1i xpexd suppssr
      snex fveq1d syl2anc fvmpt2 anassrs fvmpt2d syl21anc syl fvconst2g 3eqtr3d
      3eqtrd adantl3r elxp2 bilani r19.29vva adantlr fvexd fmpt2d ssiun2 adantl
      wss fveq2 oveq1d cbviunv sseqtrdi c0 simpl wfn wb wi eleq1w anbi2d fneq1d
      wrex imbi12d ffnd chvarvv fnsuppeq0 biimpar ralrimiva nfcv iunxdif3 dfin4
      cin suppssdm fssdm sseqin2 iuneq1d eqtr3d sseqtrd cun difxp eleqtrdi elun
      wo mpjaodan suppss ) ADEUBZGUAIJEMUCZUBZUDUEZHYRHUFZJUGZMUDUEZUHZUBZMAFGT
      ZCEUIBDUIYOGIUJAUUDBCDESUKBCDEFGINULUMAUAUFZYOUUCUNZTZUOZUUEDYRUNZEUBZTZU
      UEIUGZMVFZUUEDEUUBUNZUBZTZAUUKUUMUUGAUUKUOUUEBUFZCUFZUPZVFZUUMBCUUIEAUUQU
      UITZUURETZUUTUUMUUKAUVAUOZUVBUOZUUTUOZUULUUSIUGZFMUVEUUEUUSIUVDUUTUQURUVE
      UVFUUQUURIUEZFUUQUURIUSZUVEUUQDTZUVBUUDUVGFVFZUVEUUQDYRAUVAUVBUUTUTZVAZUV
      CUVBUUTVBZUVEAUVIUVBUUDAUVAUVBUUTVCZUVLUVMSVDBCDEFIGNVEZVGVHUVEUURUUQJUGZ
      UGZUURYQUGZFMUVEAUVAUVQUVRVFUVNUVKUVCUURUVPYQADVIVIJKYRUUQYQABDCEFVJZVIJA
      UVIUOZCEFLAELTZUVIQVKZVLZOVMZAYRVNZPAEYPLVIQYPVITAMVRVOVPZVQVSVTUVEAUVIUV
      BUVQFVFZUVNUVLUVMUVTCEFUVPGUVTUVIUVSVITUVPUVSVFAUVIUQUWCBDUVSVIJOWAVTZAUV
      IUVBUUDSWBZWCZWDUVEMGTZUVBUVRMVFUVEAUWKUVNRWEUVMEMUURGWFVTWGWHWIUUKUUTCEX
      KBUUIXKABCUUEUUIEWJWKWLWMAUUPUUMUUGAUUPUOUUTUUMBCDUUNAUVIUURUUNTZUUTUUMUU
      PUVTUWLUOZUUTUOZUULUVFFMUWNUUEUUSIUWMUUTUQURUWNUVFUVGFUVHUWNUVIUVBUUDUVJA
      UVIUWLUUTUTZUWNUUREUUBUVTUWLUUTVBVAZUWNAUVIUVBUUDAUVIUWLUUTVCZUWOUWPSVDUV
      OVGVHUWNUVQFMUWNAUVIUVBUWGUWQUWOUWPUWJWDUWMUVQMVFUUTUVTEVIGUVPLUUBUURMUVT
      CCEFVIUVPGUWIUWHUVTUVBUOUURUVPWNWOZUVTUVPMUDUEZHDUUAUHZUUBUVTUWSBDUWSUHZU
      WTUVIUWSUXAWRABDUWSWPWQBHDUWSUUAUUQYSVFZUVPYTMUDUUQYSJWSZWTXAXBAUWTUUBVFU
      VIAHDUUIUNZUUAUHZUWTUUBAUUAXCVFZHUUIUIUXEUWTVFAUXFHUUIAYSUUITZUOZAYSDTZYT
      YQVFZUXFAUXGXDUXHYSDYRAUXGUQVAADVIVIJKYRYSYQUWDUWEPUWFVQAUXIUOZUXFUXJUXKY
      TEXEZUWAUWKUXFUXJXFUVTUVPEXEZXGUXKUXLXGBHUXBUVTUXKUXMUXLUXBUVIUXIABHDXHXI
      UXBEUVPYTUXCXJXLUVTEVIUVPUWRXMXNAUWAUXIQVKAUWKUXIRVKEYTGLMXOVGXPWDXQHDUUA
      UUIHUUIXRXSWEAHUXDYRUUAAUXDDYRYAZYRDYRXTAYRDWRUXNYRVFADVIYRJJYQYBUWDYCYRD
      YDUMVHYEYFVKYGUWBAUWKUVIRVKVQVKYFWHWIUUPUUTCUUNXKBDXKABCUUEDUUNWJWKWLWMUU
      HUUEUUJUUOYHZTUUKUUPYLUUHUUEUUFUXOAUUGUQYRUUBDEYIYJUUEUUJUUOYKUMYMYN $.
  $}

  ${
    elsuppfnd.1 $e |- ( ph -> F Fn A ) $.
    elsuppfnd.2 $e |- ( ph -> A e. V ) $.
    elsuppfnd.3 $e |- ( ph -> Z e. W ) $.
    elsuppfnd.4 $e |- ( ph -> X e. A ) $.
    elsuppfnd.5 $e |- ( ph -> ( F ` X ) =/= Z ) $.
    $( Deduce membership in the support of a function.  (Contributed by Thierry
       Arnoux, 5-Oct-2025.) $)
    elsuppfnd $p |- ( ph -> X e. ( F supp Z ) ) $=
      ( wfn wcel cfv wne csupp co w3a wa elsuppfn biimpar syl32anc ) ACBMZBDNZG
      ENZFBNZFCOGPZFCGQRNZHIJKLUDUEUFSUIUGUHTFCDEBGUAUBUC $.
  $}

  ${
    $d .0. x $.  $d .0. y $.  $d A x $.  $d B y $.  $d D x $.  $d F x $.
    $d O y $.  $d Y y $.  $d Z x $.  $d Z y $.  $d ph x $.  $d ph y $.
    fisuppov1.1 $e |- ( ph -> Z e. V ) $.
    fisuppov1.2 $e |- ( ph -> .0. e. X ) $.
    fisuppov1.3 $e |- ( ph -> A e. W ) $.
    fisuppov1.4 $e |- ( ph -> D C_ A ) $.
    fisuppov1.5 $e |- ( ( ph /\ x e. D ) -> B e. Y ) $.
    fisuppov1.6 $e |- ( ph -> F : A --> E ) $.
    fisuppov1.7 $e |- ( ph -> F finSupp .0. ) $.
    fisuppov1.8 $e |- ( ( ph /\ y e. Y ) -> ( .0. O y ) = Z ) $.
    $( Formula building theorem for finite support: operator with left
       annihilator.  (Contributed by Thierry Arnoux, 5-Oct-2025.) $)
    fisuppov1 $p |- ( ph -> ( x e. D |-> ( ( F ` x ) O B ) ) finSupp Z ) $=
      ( cv cfv co cmpt cvv ssexd mptexd wfun funmpt csupp cres feqresmpt oveq1d
      a1i wcel fexd ressuppss syl2anc eqsstrrd wa fvexd suppssov1 fsuppsssuppgd
      wss ) AHBFBUDZHUEZEIUFZUGZNUHJOABFVJUHAFDKRSUIUJPVKUKABFVJULUQUBABCVIEFMH
      NUMUFZIUHLNOABFVIUGZNUMUFHFUNZNUMUFZVLAVNVMNUMABDGFHUASUOUPAHUHURNLURVOVL
      VGADGKHUARUSQFHUHLNUTVAVBUCAVHFURVCVHHVDTQVEVF $.
  $}

  ${
    suppun2.1 $e |- ( ph -> F e. V ) $.
    suppun2.2 $e |- ( ph -> G e. W ) $.
    suppun2.3 $e |- ( ph -> Z e. X ) $.
    $( The support of a union is the union of the supports.  (Contributed by
       Thierry Arnoux, 5-Oct-2025.) $)
    suppun2 $p |- ( ph -> ( ( F u. G ) supp Z )
                         = ( ( F supp Z ) u. ( G supp Z ) ) ) $=
      ( cun ccnv cvv cima csupp co wcel wceq suppimacnv syl2anc csn cnvun eqtri
      cdif imaeq1i imaundir unexd uneq12d 3eqtr4a ) ABCKZLZMGUAUDZNZBLZULNZCLZU
      LNZKZUJGOPZBGOPZCGOPZKUMUNUPKZULNURUKVBULBCUBUEUNUPULUFUCAUJMQGFQZUSUMRAB
      CDEHIUGJUJMFGSTAUTUOVAUQABDQVCUTUORHJBDFGSTACEQVCVAUQRIJCEFGSTUHUI $.
  $}

  ${
    $d A x $.  $d B x $.  $d F x $.  $d Z x $.  $d ph x $.
    fdifsupp.1 $e |- ( ph -> A e. V ) $.
    fdifsupp.2 $e |- ( ph -> Z e. W ) $.
    fdifsupp.3 $e |- ( ph -> F Fn A ) $.
    $( Express the support of a function ` F ` outside of ` B ` in two
       different ways.  (Contributed by Thierry Arnoux, 5-Oct-2025.) $)
    fdifsupp $p |- ( ph -> ( ( F |` ( A \ B ) ) supp Z ) = ( ( F supp Z ) \ B )
       ) $=
      ( vx cdif csupp co wcel cfv wne wa cvv wb cres wfn difssd fnssresd difexd
      cv wn elsuppfn syl3anc eldif anbi1i a1i simpr fvresd neeq1d pm5.32da an32
      3bitr4d elexd anbi1d bitr2id 3bitrd eqrdv ) AKDBCLZUAZGMNZDGMNZCLZAKUFZVF
      OZVIVDOZVIVEPZGQZRZVIBOZVIDPZGQZRZVICOUGZRZVIVHOZAVEVDUBVDSOGFOZVJVNTABVD
      DJABCUCUDABCEHUEIVIVESFVDGUHUIAVKVQRZVOVSRZVQRZVNVTWCWETAVKWDVQVIBCUJUKUL
      AVKVMVQAVKRZVLVPGWFVIVDDAVKUMUNUOUPVTWETAVOVQVSUQULURWAVIVGOZVSRAVTVIVGCU
      JAWGVRVSADBUBBSOWBWGVRTJABEHUSIVIDSFBGUHUIUTVAVBVC $.
  $}

  ${
    $d F x $.  $d V x $.  $d W x $.  $d Z x $.
    $( Relation between the support ` ( F supp Z ) ` and the initial segment
       ` ( ``' F " { Z } ) ` .  (Contributed by Thierry Arnoux,
       25-Jun-2024.) $)
    suppiniseg $p |- ( ( Fun F /\ F e. V /\ Z e. W )
                    -> ( dom F \ ( F supp Z ) ) = ( `' F " { Z } ) ) $=
      ( vx wfun wcel w3a cdm csupp co cdif ccnv csn cima cv cfv wa wn wb biimpi
      eldif wceq wne wfn funfn elsuppfng syl3an1 notbid nne bitrdi fvex bitr4di
      baibd elsn pm5.32da bitrid 3ad2ant1 elpreima syl bitr4d eqrdv ) AFZABGZDC
      GZHZEAIZADJKZLZAMDNZOZVFEPZVIGZVLVGGZVLAQZVJGZRZVLVKGZVMVNVLVHGZSZRVFVQVL
      VGVHUBVFVNVTVPVFVNRZVTVODUCZVPWAVTVODUDZSWBWAVSWCVFVSVNWCVCAVGUEZVDVEVSVN
      WCRTVCWDAUFUAZVLABCVGDUGUHUNUIVODUJUKVODVLAULUOUMUPUQVFWDVRVQTVCVDWDVEWEU
      RVGVLVJAUSUTVAVB $.
  $}

  ${
    fsuppinisegfi.1 $e |- ( ph -> F e. V ) $.
    fsuppinisegfi.2 $e |- ( ph -> .0. e. W ) $.
    fsuppinisegfi.3 $e |- ( ph -> Y e. ( _V \ { .0. } ) ) $.
    fsuppinisegfi.4 $e |- ( ph -> F finSupp .0. ) $.
    $( The initial segment ` ( ``' F " { Y } ) ` of a nonzero ` Y ` is finite
       if ` F ` has finite support.  (Contributed by Thierry Arnoux,
       21-Jun-2024.) $)
    fsuppinisegfi $p |- ( ph -> ( `' F " { Y } ) e. Fin ) $=
      ( csupp co ccnv csn cima fsuppimpd cvv cdif wss wcel snssd imass2 syl2anc
      syl suppimacnvss sstrd ssfid ) ABFKLZBMZENZOZABFJPAUKUIQFNRZOZUHAUJULSUKU
      MSAEULIUAUJULUIUBUDABCTFDTUMUHSGHBCDFUEUCUFUG $.
  $}

  $( The restriction of a function to its support.  (Contributed by Thierry
     Arnoux, 25-Jun-2024.) $)
  fressupp $p |- ( ( Fun F /\ F e. V /\ Z e. W )
                -> ( F |` ( F supp Z ) ) = ( F \ ( _V X. { Z } ) ) ) $=
    ( wfun wcel w3a cdm csupp co cdif cres cun wceq 3ad2ant1 wss mp1i cin ccnv
    c0 cvv csn wrel funrel suppssdm undif biimpi eqcomd reldmun syl2anc difeq1d
    cxp resss sseqin2 mpbi cima suppiniseg reseq2d cnvrescnv funcnvres2 eqtr3id
    eqtr4d eqtrid indifbi sylib disjdif reseq2i resindi 3eqtr3i undif5 3eqtr3rd
    res0 ) AEZABFZDCFZGZAAAHZADIJZKZLZKZAVRLZVTMZVTKZAUADUBZULZKZWBVPAWCVTVPAUC
    ZVQVRVSMZNZAWCNVMVNWHVOAUDOVRVQPZWJVPADUEWKWIVQWKWIVQNVRVQUFUGUHQVRVSAUIUJU
    KVPAVTRZAWFRZNWAWGNVPWLVTWMVTAPWLVTNAVSUMVTAUNUOVPVTAASZWEUPZLZWMVPVSWOAABC
    DUQURVMVNWMWPNVOVMWMWNWELSWPWEAUSWEAUTVAOVBVCAVTWFVDVEWBVTRZTNWDWBNVPAVRVSR
    ZLATLWQTWRTAVRVQVFVGAVRVSVHAVLVIWBVTVJQVK $.

  ${
    $d A x $.  $d F x $.  $d V x $.  $d W x $.  $d Z x $.
    fdifsuppconst.1 $e |- A = ( dom F \ ( F supp Z ) ) $.
    $( A function is a zero constant outside of its support.  (Contributed by
       Thierry Arnoux, 22-Jun-2024.) $)
    fdifsuppconst $p |- ( ( Fun F /\ F e. V /\ Z e. W )
                       -> ( F |` A ) = ( A X. { Z } ) ) $=
      ( vx wfun wcel cres csn cxp wceq wa cdm wfn biimpi adantl cfv cvv co cdif
      funfn ad2antrr csupp difssd eqsstrid fnssresd fnconstg cv adantr ad3antlr
      dmexg simplr eleq2i fvdifsupp simpr fvresd adantll 3eqtr4d eqfnfvd 3impa
      fvconst2g ) BHZBCIZEDIZBAJZAEKLZMVDVENZVFNZGAVGVHVJBOZABVDBVKPZVEVFVDVLBU
      CQUDZVJAVKBEUEUAZUBZVKFVJVKVNUFUGUHVFVHAPVIAEDUIRVJGUJZAIZNZVPBSEVPVGSVPV
      HSZVRVKBTDVPEVJVLVQVMUKVEVKTIVDVFVQBCUMULVIVFVQUNVQVPVOIZVJVQVTAVOVPFUOQR
      UPVRVPABVJVQUQURVFVQVSEMVIAEVPDVCUSUTVAVB $.
  $}

  ${
    $d .0. x y $.  $d F x y $.  $d V x y $.  $d W x y $.
    $( The range of a function restricted to its support.  (Contributed by
       Thierry Arnoux, 25-Jun-2024.) $)
    ressupprn $p |- ( ( Fun F /\ F e. V /\ .0. e. W )
                   -> ran ( F |` ( F supp .0. ) ) = ( ran F \ { .0. } ) ) $=
      ( vy vx wcel crn cv cfv wceq wrex wne wa wfn cvv anbi1d pm5.32da fvelrnb
      wb wfun w3a csupp co cres cdif funfn biimpi 3ad2ant1 dmexg 3ad2ant2 simp3
      csn cdm elsuppfn syl3anc anass a1i biimprd impl fvresd eqeq1d ancom simpr
      neeq1d bitrid bitrd rexbidv2 wss suppssdm fnssres sylancl eldifsn r19.41v
      3bitrd syl 3bitr4g 3bitr4d eqrdv ) AUAZABGZDCGZUBZEAADUCUDZUEZHZAHZDUMUFZ
      WCFIZWEJZEIZKZFWDLZWIAJZWKKZWKDMZNZFAUNZLZWKWFGZWKWHGZWCWLWQFWDWRWCWIWDGZ
      WLNWIWRGZWNDMZNZWLNZXCXDWLNZNZXCWQNWCXBXEWLWCAWROZWRPGZWBXBXETVTWAXIWBVTX
      IAUGUHUIZWAVTXJWBABUJUKVTWAWBULWIAPCWRDUOUPZQXFXHTWCXCXDWLUQURWCXCXGWQWCX
      CNZXGXDWONZWQXMXDWLWOXMXDNZWJWNWKXOWIWDAWCXCXDXBWCXBXEXLUSUTVAVBRXNWOXDNX
      MWQXDWOVCXMWOXDWPXMWONWNWKDXMWOVDVERVFVGRVOVHWCWEWDOZWTWMTWCXIWDWRVIXPXKA
      DVJWRWDAVKVLFWDWKWESVPWCXIXAWSTXKXIWKWGGZWPNWOFWRLZWPNXAWSXIXQXRWPFWRWKAS
      QWKWGDVMWOWPFWRVNVQVPVRVS $.
  $}

  $( Express the support of a function as the preimage of its range except
     zero.  (Contributed by Thierry Arnoux, 24-Jun-2024.) $)
  supppreima $p |- ( ( Fun F /\ F e. V /\ Z e. W )
                            -> ( F supp Z ) = ( `' F " ( ran F \ { Z } ) ) ) $=
    ( wfun wcel w3a ccnv crn cima csn cdif cdm csupp co wceq cnvimarndm difeq1d
    a1i difpreima 3ad2ant1 wss suppssdm dfss4 mpbi suppiniseg difeq2d 3eqtr4rd
    eqtr3id ) AEZABFZDCFZGZAHZAIZJZUNDKZJZLZAMZURLZUNUOUQLJZADNOZUMUPUTURUPUTPU
    MAQSRUJUKVBUSPULUOUQATUAUMVCUTUTVCLZLZVAVCUTUBVEVCPADUCVCUTUDUEUMVDURUTABCD
    UFUGUIUH $.

  $( Finite support implies finite range.  (Contributed by Thierry Arnoux,
     24-Jun-2024.) $)
  fsupprnfi $p |- ( ( ( Fun F /\ F e. V ) /\ ( .0. e. W /\ F finSupp .0. ) )
                 -> ran F e. Fin ) $=
    ( wfun wcel wa cfsupp wbr csn cfn crn cdif snfi csupp wceq wfo cdm sylancr
    co cres simpll simplr simprl ressupprn syl3anc simprr fsuppimpd wss ssdmres
    suppssdm funresd funforn sylib foeq2 biimpa syl2anc eqeltrrd diffib biimpar
    mpbi fofi ) AEZABFZGZDCFZADHIZGZGZDJZKFZALZVJMZKFZVLKFZDNVIAADOTZUAZLZVMKVI
    VCVDVFVRVMPVCVDVHUBZVCVDVHUCVEVFVGUDABCDUEUFVIVPKFVPVRVQQZVRKFVIADVEVFVGUGU
    HVIVQRZVPPZWAVRVQQZVTVPARUIWBADUKVPAUJVAVIVQEWCVIVPAVSULVQUMUNWBWCVTWAVPVRV
    QUOUPSVPVRVQVBUQURVKVOVNVLVJUSUTS $.

  ${
    $d A x $.  $d B x $.  $d V x $.  $d Z x $.  $d ph x $.
    mptiffisupp.f $e |- F = ( x e. A |-> if ( x e. B , C , Z ) ) $.
    mptiffisupp.a $e |- ( ph -> A e. U ) $.
    mptiffisupp.b $e |- ( ph -> B e. Fin ) $.
    mptiffisupp.c $e |- ( ( ph /\ x e. B ) -> C e. V ) $.
    mptiffisupp.z $e |- ( ph -> Z e. W ) $.
    $( Conditions for a mapping function defined with a conditional to have
       finite support.  (Contributed by Thierry Arnoux, 20-Feb-2025.) $)
    mptiffisupp $p |- ( ph -> F finSupp Z ) $=
      ( cvv wcel cfn c0 eqtrdi cv cif cmpt mptexd eqeltrid funmpt2 a1i csupp co
      wfun cin cdif cun partfun eqtri oveq1i wss inss2 sselda syldan incom infi
      fmpttd syl eqeltrrid fidmfisupp difexg mptexg 3syl ccnv crn csn cima wceq
      funmpt supppreima mp3an2i simpr mpteq1d mpt0 cnveqd cnv0 imaeq1d 0ima wne
      eqid rnmptc difeq1d difid imaeq2d ima0 pm2.61dane eqtrd eqeltrdi isfsuppd
      wa 0fi fsuppun ) AGPIJAGBCBUAZDQZEJUBZUCZPKABCXAFLUDUEOGUJABCXAGKUFUGAGJU
      HUIBCDUKZEUCZBCDULZJUCZUMZJUHUIRGXGJUHGXBXGKBCDEJUNUOUPAXDXFJAXCHXDIJABXC
      EHAWSXCQWTEHQAXCDWSXCDUQACDURUGUSNUTVCAXCDCUKZRDCVAADRQXHRQMDCVBVDVEOVFAX
      FPIJACFQXEPQXFPQZLCDFVGBXEJPVHVIZOXFUJZABXEJVOZUGAXFJUHUIZSRAXMXFVJZXFVKZ
      JVLZULZVMZSXKAXIJIQXMXRVNXLXJOXFPIJVPVQAXRSVNXESAXESVNZWPZXRSXQVMSXTXNSXQ
      XTXNSVJSXTXFSXTXFBSJUCSXTBXESJAXSVRVSBJVTTWAWBTWCXQWDTAXESWEZWPZXRXNSVMSY
      BXQSXNYBXQXPXPULSYBXOXPXPYBBXEJXFXFWFAYAVRWGWHXPWITWJXNWKTWLWMWQWNWOWRUEW
      O $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Explicit Functions with one or two points as a domain
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    cosnopne.b $e |- ( ph -> B e. W ) $.
    cosnopne.c $e |- ( ph -> C e. X ) $.
    cosnopne.1 $e |- ( ph -> A =/= D ) $.
    $( Composition of two ordered pair singletons with non-matching domain and
       range.  (Contributed by Thierry Arnoux, 24-Sep-2023.) $)
    cosnopne $p |- ( ph -> ( { <. A , B >. } o. { <. C , D >. } ) = (/) ) $=
      ( cop csn cdm crn cin c0 wcel wceq dmsnopg syl rnsnopg wne eqtrd coemptyd
      ineq12d disjsn2 ) ABCKLZDEKLZAUGMZUHNZOBLZELZOZPAUIUKUJULACFQUIUKRHBCFSTA
      DGQUJULRIDEGUATUEABEUBUMPRJBEUFTUCUD $.
  $}

  ${
    cosnop.a $e |- ( ph -> A e. V ) $.
    cosnop.b $e |- ( ph -> B e. W ) $.
    cosnop.c $e |- ( ph -> C e. X ) $.
    $( Composition of two ordered pair singletons with matching domain and
       range.  (Contributed by Thierry Arnoux, 24-Sep-2023.) $)
    cosnop $p |- ( ph -> ( { <. A , B >. } o. { <. C , A >. } ) = { <. C , B >.
       } ) $=
      ( csn cxp ccom cop wcel c0 wne wceq xpsng syl2anc snnzg xpco 3syl coeq12d
      3eqtr3d ) ABKZCKZLZDKZUFLZMZUIUGLZBCNKZDBNKZMDCNKZABEOZUFPQUKULRHBEUAUIUF
      UGUBUCAUHUMUJUNAUPCFOZUHUMRHIBCEFSTADGOZUPUJUNRJHDBGESTUDAURUQULUORJIDCGF
      STUE $.
  $}

  ${
    $( Converse of a pair of ordered pairs.  (Contributed by Thierry Arnoux,
       24-Sep-2023.) $)
    cnvprop $p |- ( ( ( A e. V /\ B e. W ) /\ ( C e. V /\ D e. W ) )
       -> `' { <. A , B >. , <. C , D >. } = { <. B , A >. , <. D , C >. } ) $=
      ( wcel wa cop csn ccnv cun wceq cnvsng adantr adantl uneq12d df-pr cnveqi
      cpr cnvun eqtri 3eqtr4g ) AEGBFGHZCEGDFGHZHZABIZJZKZCDIZJZKZLZBAIZJZDCIZJ
      ZLUGUJTZKZUNUPTUFUIUOULUQUDUIUOMUEABEFNOUEULUQMUDCDEFNPQUSUHUKLZKUMURUTUG
      UJRSUHUKUAUBUNUPRUC $.
  $}

  ${
    brprop.a $e |- ( ph -> A e. V ) $.
    brprop.b $e |- ( ph -> B e. W ) $.
    brprop.c $e |- ( ph -> C e. V ) $.
    brprop.d $e |- ( ph -> D e. W ) $.
    $( Binary relation for a pair of ordered pairs.  (Contributed by Thierry
       Arnoux, 24-Sep-2023.) $)
    brprop $p |- ( ph -> ( X { <. A , B >. , <. C , D >. } Y
                        <-> ( ( X = A /\ Y = B ) \/ ( X = C /\ Y = D ) ) ) ) $=
      ( cop wbr csn wo wceq wa wcel cpr cun df-pr breqi bitri wb brsnop syl2anc
      brun orbi12d bitrid ) HIBCNZDENZUAZOZHIULPZOZHIUMPZOZQZAHBRICRSZHDRIERSZQ
      UOHIUPURUBZOUTHIUNVCULUMUCUDHIUPURUIUEAUQVAUSVBABFTCGTUQVAUFJKBCFGHIUGUHA
      DFTEGTUSVBUFLMDEFGHIUGUHUJUK $.

    $d A x $.  $d B x $.  $d C x $.  $d D x $.  $d ph x $.
    mptprop.1 $e |- ( ph -> A =/= C ) $.
    $( Rewrite pairs of ordered pairs as mapping to functions.  (Contributed by
       Thierry Arnoux, 24-Sep-2023.) $)
    mptprop $p |- ( ph -> { <. A , B >. , <. C , D >. }
                        = ( x e. { A , C } |-> if ( x = A , B , D ) ) ) $=
      ( cop cpr csn cun wceq cmpt wcel cv cif df-pr cin cdif fmptsn syl2anc wss
      incom prid1g snssi 3syl dfss2 eqtr3id mpteq1d eqtr4d wne difprsn1 uneq12d
      sylib syl partfun eqtr4di wb elsn2g ifbid mpteq2dv eqtrd eqtrid ) ACDNZEF
      NZOVJPZVKPZQZBCEOZBUAZCRZDFUBZSZVJVKUCAVNBVOVPCPZTZDFUBZSZVSAVNBVOVTUDZDS
      ZBVOVTUEZFSZQWCAVLWEVMWGAVLBVTDSZWEACGTZDHTVLWHRIJBCDGHUFUGABWDVTDAWDVTVO
      UDZVTVTVOUIAVTVOUHZWJVTRAWICVOTWKICEGUJCVOUKULVTVOUMUTUNUOUPAVMBEPZFSZWGA
      EGTFHTVMWMRKLBEFGHUFUGABWFWLFACEUQWFWLRMCEURVAUOUPUSBVOVTDFVBVCABVOWBVRAW
      AVQDFAWIWAVQVDIVPCGVEVAVFVGVHVI $.

    coprprop.e $e |- ( ph -> E e. X ) $.
    coprprop.f $e |- ( ph -> F e. X ) $.
    coprprop.1 $e |- ( ph -> E =/= F ) $.
    $( Composition of two pairs of ordered pairs with matching domain and
       range.  (Contributed by Thierry Arnoux, 24-Sep-2023.) $)
    coprprop $p |- ( ph -> ( { <. A , B >. , <. C , D >. } o. { <. E , A >. ,
       <. F , C >. } ) = { <. E , B >. , <. F , D >. } ) $=
      ( cun ccom cop csn cpr coundir c0 cosnop necomd uneq12d un0 eqtrdi eqtrid
      cosnopne 0un df-pr coeq12i coundi eqtri 3eqtr4g ) ABCUAZUBZDEUAZUBZSZFBUA
      ZUBZTZVCGDUAZUBZTZSZFCUAZUBZGEUAZUBZSUSVAUCZVDVGUCZTZVKVMUCAVFVLVIVNAVFUT
      VETZVBVETZSZVLUTVBVEUDAVTVLUESVLAVRVLVSUEABCFHIJKLPUFADEFBIJNPABDOUGULUHV
      LUIUJUKAVIUTVHTZVBVHTZSZVNUTVBVHUDAWCUEVNSVNAWAUEWBVNABCGDIJLQOULADEGHIJM
      NQUFUHVNUMUJUKUHVQVCVEVHSZTVJVOVCVPWDUSVAUNVDVGUNUOVCVEVHUPUQVKVMUNUR $.
  $}

  ${
    $d A x $.  $d F x $.  $d X x $.  $d Y x $.  $d ph x $.
    fmptunsnop.1 $e |- ( ph -> F Fn A ) $.
    fmptunsnop.2 $e |- ( ph -> X e. A ) $.
    fmptunsnop.3 $e |- ( ph -> Y e. B ) $.
    $( Two ways to express a function with a value replaced.  (Contributed by
       Thierry Arnoux, 5-Oct-2025.) $)
    fmptunsnop $p |- ( ph -> ( x e. A |-> if ( x = X , Y , ( F ` x ) ) )
                    = ( ( F |` ( A \ { X } ) ) u. { <. X , Y >. } ) ) $=
      ( csn cdif cun cv wceq cfv cif cmpt wcel adantl cop mptun difsnid mpteq1d
      cres syl wa wne eldifsni neneqd iffalsed mpteq2dva crn wfn wf dffn3 sylib
      difssd feqresmpt eqtr4d iftrue fmptsnd eqcomd uneq12d 3eqtr3a ) ABCFKZLZV
      FMZBNZFOZGVIEPZQZRBVGVLRZBVFVLRZMBCVLREVGUEZFGUAKZMBVGVFVLUBABVHCVLAFCSVH
      COICFUCUFUDAVMVOVNVPAVMBVGVKRVOABVGVLVKAVIVGSZUGZVJGVKVRVIFVQVIFUHAVICFUI
      TUJUKULABCEUMZVGEAECUNCVSEUOHCEUPUQACVFURUSUTAVPVNABFVLGCDVJVLGOAVJGVKVAT
      IJVBVCVDVE $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Isomorphisms - misc. additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Two ways to write a strictly decreasing function on the reals.
     (Contributed by Thierry Arnoux, 6-Apr-2017.) $)
  gtiso $p |- ( ( A C_ RR* /\ B C_ RR* ) ->
    ( F Isom < , `' < ( A , B ) <-> F Isom <_ , `' <_ ( A , B ) ) ) $=
    ( cxr wss clt ccnv wiso cle cxp cin cdif eqid wceq df-le wrel dfrel2 ineq1i
    wb mpbi isocnv3 a1i cnveqi cnvdif cnvxp ltrel difeq12i 3eqtri indif1 xpss12
    eqtri anidms sseqin2 difeq1d eqtr2id adantr isoeq2 syl adantl isoeq3 3bitrd
    wa sylib isocnv2 isores2 isores1 bitri lerel ax-mp 3bitr3ri bitr4di ) ADEZB
    DEZVBZABFFGZCHZABIGZAAJZKZIBBJZKZCHZABIVQCHZVNVPABVRFLZVTVOLZCHZABVSWECHZWB
    VPWFSVNABWDWEFVOCWDMWEMUAUBVNWDVSNZWFWGSVLWHVMVLVSDDJZVRKZFLZWDVSWIFLZVRKWK
    VQWLVRVQWIVOLZGWIGZVOGZLWLIWMOUCWIVOUDWNWIWOFDDUEFPWOFNUFFQTUGUHRWIVRFUIUKV
    LWJVRFVLVRWIEZWJVRNVLWPADADUJULVRWIUMVCUNUOUPABWDWEVSCUQURVNWEWANZWGWBSVMWQ
    VLVMWAWIVTKZVOLZWEWAWMVTKWSIWMVTORWIVTVOUIUKVMWRVTVOVMVTWIEZWRVTNVMWTBDBDUJ
    ULVTWIUMVCUNUOUSABVSWEWACUTURVAABVQICHZABVQGZVQCHZWBWCABVQICVDXAABVQWACHWBA
    BVQICVEABVQWACVFVGXBINZXCWCSIPXDVHIQTABXBVQICUQVIVJVK $.

  ${
    $d x y A $.  $d w x y z B $.  $d x y C $.  $d w x y z D $.  $d w x y z G $.
    $d w x y z H $.  $d x y R $.  $d w x y z S $.  $d w x y z ph $.
    isoun.1 $e |- ( ph -> H Isom R , S ( A , B ) ) $.
    isoun.2 $e |- ( ph -> G Isom R , S ( C , D ) ) $.
    isoun.3 $e |- ( ( ph /\ x e. A /\ y e. C ) -> x R y ) $.
    isoun.4 $e |- ( ( ph /\ z e. B /\ w e. D ) -> z S w ) $.
    isoun.5 $e |- ( ( ph /\ x e. C /\ y e. A ) -> -. x R y ) $.
    isoun.6 $e |- ( ( ph /\ z e. D /\ w e. B ) -> -. z S w ) $.
    isoun.7 $e |- ( ph -> ( A i^i C ) = (/) ) $.
    isoun.8 $e |- ( ph -> ( B i^i D ) = (/) ) $.
    $( Infer an isomorphism from a union of two isomorphisms.  (Contributed by
       Thierry Arnoux, 30-Mar-2017.) $)
    isoun $p |- ( ph -> ( H u. G ) Isom R , S ( ( A u. C ) , ( B u. D ) ) ) $=
      ( cun wf1o cv wbr cfv wb wral wiso cin c0 wceq isof1o f1oun syl22anc wcel
      syl wa wo elun isorel sylan wfn f1ofn adantr anim1i fvun1 syl3anc adantrr
      wi adantrl breq12d bitr4d anassrs 3expb 3expia ralrimiv ralrimiva wf f1of
      ffvelcdmda breq1 breq2 rspc2v syl2anc mpd fvun2 3brtr4d jaodan sylan2b ex
      2thd wn notbid mtbird 2falsed df-isom sylanbrc ) AFHUBZGIUBZMLUBZUCZBUDZC
      UDZJUEZXCXAUFZXDXAUFZKUEZUGZCWSUHZBWSUHWSWTJKXAUIAFGMUCZHILUCZFHUJUKULZGI
      UJUKULXBAFGJKMUIZXKNFGJKMUMUQZAHIJKLUIZXLOHIJKLUMUQZTUAFGHIMLUNUOAXJBWSAX
      CWSUPZURXICWSXRAXCFUPZXCHUPZUSXDWSUPZXIVJZXCFHUTAXSYBXTAXSURZYAXIYAYCXDFU
      PZXDHUPZUSZXIXDFHUTZYCYDXIYEAXSYDXIAXSYDURZURZXEXCMUFZXDMUFZKUEZXHAXNYHXE
      YLUGNFGXCXDJKMVAVBYIXFYJXGYKKAXSXFYJULZYDYCMFVCZLHVCZXMXSURYMAYNXSAXKYNXO
      FGMVDUQZVEAYOXSAXLYOXQHILVDUQZVEAXMXSTVFFHMLXCVGVHZVIAYDXGYKULZXSAYDURYNY
      OXMYDURYSAYNYDYPVEAYOYDYQVEAXMYDTVFFHMLXDVGVHZVKVLVMVNAXSYEXIAXSYEURZURZX
      EXHAXSYEXEPVOUUBYJXDLUFZXFXGKUUBDUDZEUDZKUEZEIUHZDGUHZYJUUCKUEZAUUHUUAAUU
      GDGAUUDGUPZURUUFEIAUUJUUEIUPUUFQVPVQVRVEUUBYJGUPZUUCIUPZUUHUUIVJAXSUUKYEA
      FGXCMAXKFGMVSXOFGMVTUQZWAVIAYEUULXSAHIXDLAXLHILVSXQHILVTUQZWAVKUUFUUIYJUU
      EKUEDEYJUUCGIUUDYJUUEKWBUUEUUCYJKWCWDWEWFAXSYMYEYRVIAYEXGUUCULZXSAYEURYNY
      OXMYEURUUOAYNYEYPVEAYOYEYQVEAXMYETVFFHMLXDWGVHZVKWHWLVNWIWJWKAXTURZYAXIYA
      UUQYFXIYGUUQYDXIYEAXTYDXIAXTYDURZURZXEXHAXTYDXEWMRVOUUSXHXCLUFZYKKUEZUUSU
      UFWMZEGUHZDIUHZUVAWMZAUVDUURAUVCDIAUUDIUPZURUVBEGAUVFUUEGUPUVBSVPVQVRVEUU
      SUUTIUPZYKGUPZUVDUVEVJAXTUVGYDAHIXCLUUNWAVIAYDUVHXTAFGXDMUUMWAVKUVBUVEUUT
      UUEKUEZWMDEUUTYKIGUUDUUTULUUFUVIUUDUUTUUEKWBWNUUEYKULUVIUVAUUEYKUUTKWCWNW
      DWEWFUUSXFUUTXGYKKAXTXFUUTULZYDUUQYNYOXMXTURUVJAYNXTYPVEAYOXTYQVEAXMXTTVF
      FHMLXCWGVHZVIAYDYSXTYTVKVLWOWPVNAXTYEXIAXTYEURZURZXEUUTUUCKUEZXHAXPUVLXEU
      VNUGOHIXCXDJKLVAVBUVMXFUUTXGUUCKAXTUVJYEUVKVIAYEUUOXTUUPVKVLVMVNWIWJWKWIW
      JVQVRBCWSWTJKXAWQWR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Disjointness (additional proof requiring functions)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d i j x $.  $d i j A $.  $d i j B $.  $d x V $.  $d i j ph $.
    disjdsct.0 $e |- F/ x ph $.
    disjdsct.1 $e |- F/_ x A $.
    disjdsct.2 $e |- ( ( ph /\ x e. A ) -> B e. ( V \ { (/) } ) ) $.
    disjdsct.3 $e |- ( ph -> Disj_ x e. A B ) $.
    $( A disjoint collection is distinct, i.e. each set in this collection is
       different of all others, provided that it does not contain the empty set
       This can be expressed as "the converse of the mapping function is a
       function", or "the mapping function is single-rooted".  (Cf. ~ funcnv )
       (Contributed by Thierry Arnoux, 28-Feb-2017.) $)
    disjdsct $p |- ( ph -> Fun `' ( x e. A |-> B ) ) $=
      ( vi vj cv wceq csb wne wral wcel wa c0 wsb cmpt ccnv wfun wdisj disjorsf
      wo cin sylib r19.21bi w3a simpr3 csn cdif eldifsni syl sban sbf clelsb1fw
      sbimi anbi12i bitri wsbc sbsbc sbcne12 csb0 neeq2i 3bitri 3ad2antr1 disj3
      3imtr3i biimpi neeq1d biimpa syl2anc 3anassrs orim2d mpd ralrimiva nfmpt1
      difn0 ex eqid funcnv4mpt mpbird ) ABCDUAZUBUCJLZKLZMZBWFDNZBWGDNZOZUFZKCP
      ZJCPAWMJCAWFCQZRZWLKCWOWGCQZRZWHWIWJUGSMZUFZWLWOWSKCAWSKCPZJCABCDUDWTJCPI
      BCDJKGUEUHUIUIWQWRWKWHWQWRWKAWNWPWRWKAWNWPWRUJRWRWISOZWKAWNWPWRUKAWPWNXAW
      RABLCQZRZBJTZDSOZBJTZWOXAXCXEBJXCDESULUMZQXEHDESUNUOUSXDABJTZXBBJTZRWOAXB
      BJUPXHAXIWNABJFUQBJCGURUTVAXFXEBWFVBWIBWFSNZOXAXEBJVCBWFDSVDXJSWIBWFVEVFV
      GVJVHWRXARWIWJUMZSOZWKWRXAXLWRWIXKSWRWIXKMWIWJVIVKVLVMWIWJVTUOVNVOWAVPVQV
      RVRABCDJKWEXGFGBCDVSWEWBHWCWD $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  First and second members of an ordered pair - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y z A $.  $d x y z B $.
    $( Definition for a restriction of the ` 1st ` (first member of an ordered
       pair) function.  (Contributed by Thierry Arnoux, 27-Sep-2017.) $)
    df1stres $p |- ( 1st |` ( A X. B ) ) = ( x e. A , y e. B |-> x ) $=
      ( vz c1st cxp cres cv wcel wa wceq coprab cvv df1st2 reseq1i resoprab cin
      cmpo resres incom wss xpss dfss2 mpbi eqtr3i eqtri 3eqtr3ri df-mpo eqtr4i
      reseq2i ) FCDGZHZAIZCJBIDJKEIUNLZKABEMZABCDUNSUOABEMZULHFNNGZHZULHZUPUMUQ
      USULABEOPUOABECDQUTFURULRZHUMFURULTVAULFULURRZVAULULURUAULURUBVBULLCDUCUL
      URUDUEUFUKUGUHABECDUNUIUJ $.

    $( Definition for a restriction of the ` 2nd ` (second member of an ordered
       pair) function.  (Contributed by Thierry Arnoux, 27-Sep-2017.) $)
    df2ndres $p |- ( 2nd |` ( A X. B ) ) = ( x e. A , y e. B |-> y ) $=
      ( vz c2nd cxp cres cv wcel wa wceq coprab cvv df2nd2 reseq1i resoprab cin
      cmpo resres incom wss xpss dfss2 mpbi eqtr3i eqtri 3eqtr3ri df-mpo eqtr4i
      reseq2i ) FCDGZHZAICJBIZDJKEIUNLZKABEMZABCDUNSUOABEMZULHFNNGZHZULHZUPUMUQ
      USULABEOPUOABECDQUTFURULRZHUMFURULTVAULFULURRZVAULULURUAULURUBVBULLCDUCUL
      URUDUEUFUKUGUHABECDUNUIUJ $.
  $}

  ${
    $d A x z $.  $d V x z $.  $d X x z $.
    $( The preimage of a singleton.  (Contributed by Thierry Arnoux,
       27-Apr-2020.) $)
    1stpreimas $p |- ( ( Rel A /\ X e. V ) ->
      ( `' ( 1st |` A ) " { X } ) = ( { X } X. ( A " { X } ) ) ) $=
      ( vz vx wcel wa c1st cima cxp cvv cfv c2nd wceq cop ad2antrl opeq1d eqtrd
      cv jca wrel cres ccnv csn 1st2ndb biimpi fvex elsn adantl simplr elimasng
      simprrr biimpa syl21anc eqeltrd fvres syl wss df-rel birani sselda simprr
      adantrr eqtr3d sylibr wrex eqeltrrd simpr eleq1d 1st2nd ad2ant2r rspcedvd
      wex simprl df-rex sylib elima3 impbida elxp7 a1i wfn wfo fo1st fofn ax-mp
      wb ssv fnssres mp2an fniniseg 3bitr4rd eqrdv ) AUAZCBFZGZDHAUBZUCCUDZIZWQ
      AWQIZJZWODSZKKJZFZXAHLZWQFZXAMLZWSFZGZGZXAAFZXAWPLZCNZGZXAWTFZXAWRFZWOXIX
      MWOXIGZXJXLXPXACXFOZAXPXAXDXFOZXQXCXAXRNZWOXHXCXSXAUEUFPXPXDCXFXIXDCNZWOX
      EXTXCXGXEXTXDCXAHUGUHZUFPUIZQRXPWNXGXGXQAFZWMWNXIUJWOXCXEXGULZYDWNXGGXGYC
      ACXFBWSUKUMUNUOZXPXKXDCXPXJXKXDNZYEXAAHUPZUQYBRTWOXMGZXCXHWOXJXCXLWOAXBXA
      WMAXBURWNAUSUTVAVCYHXEXGYHXTXEYHXKXDCXJYFWOXLYGPWOXJXLVBVDZYAVEZYHESZWQFY
      KXFOZAFZGEVMZXGYHYMEWQVFYNYHYMYCECWQYHXDCWQYIYJVGYHYKCNZGZYLXQAYPYKCXFYHY
      OVHQVIYHXAXQAYHXAXRXQWMXJXSWNXLXAAVJVKYHXDCXFYIQRWOXJXLVNVGVLYMEWQVOVPEXF
      AWQXAMUGVQVETTVRXNXIWFWOXAWQWSVSVTXOXMWFZWOWPAWAZYQHKWAZAKURYRKKHWBYSWCKK
      HWDWEAWGKAHWHWIACXAWPWJWEVTWKWL $.
  $}

  ${
    $d w A $.  $d w B $.  $d w C $.
    $( TODO shorten like in proof for ~ 1stmbfm ! $)
    $( The preimage by ` 1st ` is a 'vertical band'.  (Contributed by Thierry
       Arnoux, 13-Oct-2017.) $)
    1stpreima $p |- ( A C_ B ->
      ( `' ( 1st |` ( B X. C ) ) " A ) = ( A X. C ) ) $=
      ( vw wss c1st cxp cres ccnv cima cv cfv wcel wa cvv elxp7 anbi2i a1i an12
      wb c2nd anass ssel pm4.71d anbi1d 3bitr4d bitr4id bitrdi cnvresima eleq2i
      cin elin vex wfo wfn fo1st fofn elpreima mp2b mpbiran anbi1i 3bitri eqrdv
      3bitr4g ) ABEZDFBCGZHIAJZACGZVEDKZFLZAMZVIVFMZNZVIOOGMZVKVIUALCMZNNZVIVGM
      ZVIVHMVEVMVKVNVONZNZVPVEVMVKVNVJBMZVONNZNZVSVLWAVKVIBCPQVEVKVTNZVRNZVKVTV
      RNZNZVSWBWDWFTVEVKVTVRUBRVEVKWCVRVEVKVTABVJUCUDUEWBWFTVEWAWEVKVNVTVOSQRUF
      UGVKVNVOSUHVQVIFIAJZVFUKZMVIWGMZVLNVMVGWHVIVFAFUIUJVIWGVFULWIVKVLWIVIOMZV
      KDUMOOFUNFOUOWIWJVKNTUPOOFUQOVIAFURUSUTVAVBVIACPVDVC $.

    $( The preimage by ` 2nd ` is an 'horizontal band'.  (Contributed by
       Thierry Arnoux, 13-Oct-2017.) $)
    2ndpreima $p |- ( A C_ C ->
      ( `' ( 2nd |` ( B X. C ) ) " A ) = ( B X. A ) ) $=
      ( vw wss c2nd cxp cres ccnv cima cv cfv wcel wa cvv elxp7 anbi1i wb anass
      a1i c1st ssel pm4.71rd anbi2d bicomi 3bitrd bitr4id 3bitr3g cin cnvresima
      ancom eleq2i elin vex wfo fo2nd fofn elpreima mp2b mpbiran 3bitri 3bitr4g
      wfn eqrdv ) ACEZDFBCGZHIAJZBAGZVEDKZFLZAMZVIVFMZNZVIOOGMZVIUALBMZVKNNZVIV
      GMZVIVHMVEVLVKNZVNVONZVKNZVMVPVEVRVNVOVJCMZNNZVKNZVTVLWBVKVIBCPQVEVTVSWAV
      KNZNZVSWANZVKNZWCVEVKWDVSVEVKWAACVJUBUCUDWEWGRVEWGWEVSWAVKSUETWGWCRVEWFWB
      VKVNVOWASQTUFUGVLVKUKVNVOVKSUHVQVIFIAJZVFUIZMVIWHMZVLNVMVGWIVIVFAFUJULVIW
      HVFUMWJVKVLWJVIOMZVKDUNOOFUOFOVCWJWKVKNRUPOOFUQOVIAFURUSUTQVAVIBAPVBVD $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.  $d x y F $.
    $d x y G $.
    curry2ima.1 $e |- G = ( F o. `' ( 1st |` ( _V X. { C } ) ) ) $.
    $( The image of a curried function with a constant second argument.
       (Contributed by Thierry Arnoux, 25-Sep-2017.) $)
    curry2ima $p |- ( ( F Fn ( A X. B ) /\ C e. B /\ D C_ A ) ->
        ( G " D ) = { y | E. x e. D y = ( x F C ) } ) $=
      ( cxp wfn wcel wss cv wceq wrex cab cvv wf syl2anc w3a cima co wfun simp1
      cfv dffn2 sylib simp2 curry2f ffund simp3 fdmd sseqtrrd dfimafn curry2val
      cdm 3adant3 eqeq1d eqcom bitrdi rexbidv abbidv eqtrd ) GCDJZKZEDLZFCMZUAZ
      HFUBZANZHUFZBNZOZAFPZBQZVMVKEGUCZOZAFPZBQVIHUDFHUQZMVJVPOVICRHVIVERGSZVGC
      RHSVIVFWAVFVGVHUEVEGUGUHVFVGVHUICDERGHIUJTZUKVIFCVTVFVGVHULVICRHWBUMUNABF
      HUOTVIVOVSBVIVNVRAFVIVNVQVMOVRVIVLVQVMVFVGVLVQOVHCDEVKGHIUPURUSVQVMUTVAVB
      VCVD $.
  $}

  $( The preimage of a nonempty set is nonempty.  (Contributed by Thierry
     Arnoux, 9-Jun-2024.) $)
  preiman0 $p |- ( ( Fun F /\ A C_ ran F /\ A =/= (/) )
                -> ( `' F " A ) =/= (/) ) $=
    ( wfun crn wss c0 wne ccnv cima wceq w3a cin cdm df-rn ineq1i biimpi ineq2d
    wa dfss2 sseqin2 3ad2ant2 fimacnvinrn eqeq1d biimpa 3adant2 imadisj 3eqtr3a
    eqtrd sylib 3expia necon3d 3impia ) BCZABDZEZAFGBHZAIZFGUMUORUQFAFUMUOUQFJZ
    AFJUMUOURKZUNAUNLZLZUPMZUTLZAFUNVBUTBNOUOUMVAAJURUOVAUNALZAUOUTAUNUOUTAJAUN
    SPQUOVDAJAUNTPUHUAUSUPUTIZFJZVCFJUMURVFUOUMURVFUMUQVEFABUBUCUDUEUPUTUFUIUGU
    JUKUL $.

  ${
    $d A x y $.  $d F x y $.
    $( The intersection of an image set, as an indexed intersection of function
       values.  (Contributed by Thierry Arnoux, 15-Jun-2024.) $)
    intimafv $p |- ( ( Fun F /\ A C_ dom F )
                  -> |^| ( F " A ) = |^|_ x e. A ( F ` x ) ) $=
      ( vy wfun cdm wss wa cima cint cfv wceq wrex cab ciin dfimafn inteqd wcel
      cv cvv wral rgenw iinabrex ax-mp eqcom rexbii abbii inteqi eqtr4i eqtr4di
      fvex ) CEBCFGHZCBIZJASZCKZDSZLZABMZDNZJZABUOOZULUMUSADBCPQVAUPUOLZABMZDNZ
      JZUTUOTRZABUAVAVELVFABUNCUKUBADBUOTUCUDUSVDURVCDUQVBABUOUPUEUFUGUHUIUJ $.
  $}

$(
  @{
    coswap.1 @e |- ( ( x = ( 1st ` p ) /\ y = ( 2nd ` p ) )
                     -> ( ps <-> ch ) ) @.
    coswap.2 @e |- ( ( x = ( 2nd ` p ) /\ y = ( 1st ` p ) )
                     -> ( ps <-> th ) ) @.
    coswap.3 @e |- ( ( ph /\ p e. A ) -> ch ) @.
    @( A scheme that can be used for swapping ` 1st ` and ` 2nd ` arguments
       in a proof. @)
    coswap @p |- ( ( ph /\ p e. `' A ) -> th ) @=
      ? @.
  @}
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Countable Sets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( TODO - remove antecedent! $)
  $( A singleton is countable.  (Contributed by Thierry Arnoux,
     16-Sep-2016.) $)
  snct $p |- ( A e. V -> { A } ~<_ _om ) $=
    ( wcel csn c1o cen wbr com cdom ensn1g c0 csdm wne peano1 ne0ii 0sdom mpbir
    omex 0sdom1dom mpbi endomtr sylancl ) ABCADZEFGEHIGZUCHIGABJKHLGZUDUEHKMKHN
    OHRPQHSTUCEHUAUB $.

  $( TODO - remove antecedent! $)
  $( An unordered pair is countable.  (Contributed by Thierry Arnoux,
     16-Sep-2016.) $)
  prct $p |- ( ( A e. V /\ B e. W ) -> { A , B } ~<_ _om ) $=
    ( wcel wa cpr csn cun com cdom df-pr wbr snct unctb syl2an eqbrtrid ) ACEZB
    DEZFABGAHZBHZIZJKABLRTJKMUAJKMUBJKMSACNBDNTUAOPQ $.

  ${
    $d x y A $.  $d y B $.
    ${
      $d x B $.
      mpocti.1 $e |- A. x e. A A. y e. B C e. V $.
      $( An operation is countable if both its domains are countable.
         (Contributed by Thierry Arnoux, 17-Sep-2017.) $)
      mpocti $p |- ( ( A ~<_ _om /\ B ~<_ _om ) ->
                                         ( x e. A , y e. B |-> C ) ~<_ _om ) $=
        ( com cdom wbr wa cmpo cxp wfn wcel wral eqid fnmpo ax-mp xpct sylancr
        fnct ) CHIJDHIJKABCDELZCDMZNZUDHIJUCHIJEFOBDPACPUEGABCDEUCFUCQRSCDTUDUC
        UBUA $.
    $}

  $}

  ${
    $d x y $.  $d y A $.  $d y B $.
    mptctf.1 $e |- F/_ x A $.
    $( A countable mapping set is countable, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by Thierry
       Arnoux, 8-Mar-2017.) $)
    mptctf $p |- ( A ~<_ _om -> ( x e. A |-> B ) ~<_ _om ) $=
      ( com cdom wbr cmpt wfun cdm funmpt cvv wcel wss ctex crab eqid dmmpt cab
      eqsstri cv df-rab simpl ss2abi abid2f sseqtri ssdomg mpisyl domtr mpancom
      wa wfn funfn fnct sylanb sylancr ) BEFGZABCHZIZURJZEFGZUREFGZABCKUTBFGZUQ
      VAUQBLMUTBNVCBOUTCLMZABPZBABCURURQRVEAUABMZVDUKZASZBVDABUBVHVFASBVGVFAVFV
      DUCUDABDUEUFTTUTBLUGUHUTBEUIUJUSURUTULVAVBURUMUTURUNUOUP $.

    $( An image set of a countable set is countable, using bound-variable
       hypotheses instead of distinct variable conditions.  (Contributed by
       Thierry Arnoux, 8-Mar-2017.) $)
    abrexctf $p |- ( A ~<_ _om -> { y | E. x e. A y = B } ~<_ _om ) $=
      ( com cdom wbr cv wceq wrex cab cmpt crn eqid rnmpt mptctf rnct eqbrtrrid
      syl ) CFGHZBIDJACKBLACDMZNZFGABCDUBUBOPUAUBFGHUCFGHACDEQUBRTS $.
  $}

  ${
    $d A f g x $.  $d V f g $.  $d Z f g x $.
    $( Index a countable set with integers and pad with ` Z ` .  (Contributed
       by Thierry Arnoux, 1-Jun-2020.)  Avoid ~ ax-rep .  (Revised by GG,
       2-Apr-2026.) $)
    padct $p |- ( ( A ~<_ _om /\ Z e. V /\ -. Z e. A ) ->
     E. f ( f : NN --> ( A u. { Z } ) /\ A C_ ran f /\ Fun ( `' f |` A ) ) ) $=
      ( vg com wbr cen cn cun wf crn wss ccnv cres wf1o wa c0 wceq 3syl vx cdom
      csdm wo wcel wn csn cv wfun w3a wex brdom2 wi chash cfv cfz cfn isfinite2
      c1 co isfinite4 sylib adantr bren 3adant3 cdif cmpt f1of adantl fconstmpt
      cin cxp eqcomi wb fconst2g ad2antlr mpbiri disjdif a1i fun syl21anc undif
      fz1ssnn mpbi feq2i 3adantl3 wfo simpr f1ofo forn eqsstrrdi rnun sseqtrrdi
      ssun1 dff1o3 simprbi cnvun reseq1i resundir wfn dff1o4 fnresdm syl simpl3
      eqtri cnveqi ineqcom disjsn sylbbr xpdisjres eqtrid uneq12d eqtrdi funeqd
      cnvxp un0 mpbird vex nnex difexi snex xpex eqeltrri unex feq1 rneq sseq2d
      cnveq reseq1d 3anbi123d spcev syl3anc exlimddv 3expia nnenom entr sylancr
      cvv ensym mpan2 fss eqimsscd cima f1ocnv f1of1 ssid f1ores f1ofun 3jca ex
      wf1 eximdv mpd a1d jaoian 3impia syl3an1b ) AFUBGAFUCGZAFHGZUDZDCUEZDAUEU
      FZIADUGZJZBUHZKZAUVELZMZUVENZAOZUIZUJZBUKZAFULUUTUVAUVBUVMUURUVAUVBUVMUMU
      USUURUVAUVBUVMUURUVAUVBUJZUSAUNUOZUPUTZAEUHZPZUVMEUURUVAUVREUKZUVBUURUVAQ
      ZUVPAHGZUVSUURUWAUVAUURAUQUEUWAAURAVAVBVCUVPAEVDVBVEUVNUVRQZIUVDUVQUAIUVP
      VFZDVGZJZKZAUWELZMZUWENZAOZUIZUVMUURUVAUVRUWFUVBUVTUVRQZUVPUWCJZUVDUWEKZU
      WFUWLUVPAUVQKZUWCUVCUWDKZUVPUWCVKRSZUWNUVRUWOUVTUVPAUVQVHVIUWLUWPUWDUWCUV
      CVLZSZUWRUWDUAUWCDVJZVMZUVAUWPUWSVNUURUVRUWCDCUWDVOVPVQUWQUWLUVPIVRVSUVPU
      WCAUVCUVQUWDVTWAUWMIUVDUWEUVPIMUWMISUVOWCUVPIWBWDWEVBWFUURUVAUVRUWHUVBUWL
      AUVQLZUWDLZJZUWGUWLAUXBUXDUWLUVRUVPAUVQWGZUXBASUVTUVRWHUVPAUVQWIUVPAUVQWJ
      TUXBUXCWNWKUVQUWDWLWMWFUWBUWKUVQNZUIZUVRUXGUVNUVRUXEUXGUVPAUVQWOWPVIUWBUW
      JUXFUWBUWJUXFAOZUWDNZAOZJZUXFUWJUXFUXIJZAOUXKUWIUXLAUVQUWDWQWRUXFUXIAWSXE
      UWBUXKUXFRJUXFUWBUXHUXFUXJRUVRUXHUXFSZUVNUVRUXFAWTZUXMUVRUVQUVPWTUXNUVPAU
      VQXAWPAUXFXBXCVIUWBUVBUXJRSUURUVAUVBUVRXDUVBUXJUVCUWCVLZAOZRUXIUXOAUXIUWR
      NUXOUWDUWRUXAXFUWCUVCXOXEWRUVBUVCAVKRSZUXPRSUXQAUVCVKRSUVBUVCARXGADXHXIUV
      CUWCAXJXCXKXCXLUXFXPXMXKXNXQUVLUWFUWHUWKUJBUWEUVQUWDEXRUWRUWDYRUWTUWCUVCI
      UVPXSXTDYAYBYCYDUVEUWESZUVFUWFUVHUWHUVKUWKIUVDUVEUWEYEUXRUVGUWGAUVEUWEYFY
      GUXRUVJUWJUXRUVIUWIAUVEUWEYHYIXNYJYKYLYMYNUUSUVAQZUVMUVBUXSIAUVEPZBUKZUVM
      UXSIAHGZUYAUXSIFHGFAHGZUYBYOUUSUYCUVAAFYSVCIFAYPYQIABVDVBUXSUXTUVLBUXSUXT
      UVLUXSUXTQZUVFUVHUVKUYDUXTIAUVEKZUVFUXSUXTWHZIAUVEVHUYEAUVDMUVFAUVCWNIAUV
      DUVEUUAYTTUYDUVGAUYDUXTIAUVEWGUVGASUYFIAUVEWIIAUVEWJTUUBUYDAIUVIUUKZAUVIA
      UUCZUVJPZUVKUYDUXTAIUVIPUYGUYFIAUVEUUDAIUVIUUETUYGAAMUYIAUUFAIAUVIUUGYTAU
      YHUVJUUHTUUIUUJUULUUMUUNUUOUUPUUQ $.
    $( $j usage 'padct' avoids 'ax-rep'; $)
  $}

  ${
    $d a i j x y z A $.  $d a i j x y z B $.  $d a i j z C $.  $d a x y z D $.
    $d a x y I $.  $d a x y J $.  $d a x y z ph $.
    f1od2.1 $e |- F = ( x e. A , y e. B |-> C ) $.
    f1od2.2 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> C e. W ) $.
    f1od2.3 $e |- ( ( ph /\ z e. D ) -> ( I e. X /\ J e. Y ) ) $.
    f1od2.4 $e |- ( ph -> ( ( ( x e. A /\ y e. B ) /\ z = C ) <->
                            ( z e. D /\ ( x = I /\ y = J ) ) ) ) $.
    $( Sufficient condition for a binary function expressed in maps-to notation
       to be bijective.  (Contributed by Thierry Arnoux, 17-Aug-2017.) $)
    f1od2 $p |- ( ph -> F : ( A X. B ) -1-1-onto-> D ) $=
      ( wa wsbc va vi cxp wfn ccnv wf1o wcel wral ralrimivva fnmpo syl cop cmpt
      vj cv opelxpi ralrimiva eqid fnmpt c1st cfv c2nd csb wceq copab cvv elxp7
      anbi1i anass sbcbidv sbcan fvex sbcg ax-mp sbcel1v anbi12i sbceq2g sbcbii
      wb bitri 3bitri sbceq1g csbvargi eqeq1i 3bitr3g anbi2d bitrid xpss simprr
      adantrr eqeltrd sselid ex pm4.71rd eqop pm5.32i bitr2di bitrd coprab cmpo
      opabbidv df-mpo eqtri cnveqi nfcsb1v nfeq2 nfan nfcsbw simpl eleq1d simpr
      nfv nfcv anbi12d csbeq1a sylan9eqr eqeq2d cbvoprab12 opelxp bitrdi csbcom
      eleq1 csbcow csbeq2i csbopeq1a eqtr3id sseli adantr 3eqtri df-mpt 3eqtr4g
      cnvoprab fneq1d mpbird dff1o4 sylanbrc ) AIEFUCZUDZIUEZHUDZYQHIUFAGLUGZCF
      UHBEUHYRAUUABCEFPUIBCEFGILOUJUKAYTDHJKULZUMZHUDZAUUBMNUCZUGZDHUHUUDAUUFDH
      ADUOZHUGZSJMUGKNUGSUUFQJKMNUPUKZUQDHUUBUUCUUEUUCURUSUKAHYSUUCAUAUOZYQUGZU
      UGBUUJUTVAZCUUJVBVAZGVCZVCZVDZSZDUAVEZUUHUUJUUBVDZSZDUAVEYSUUCAUUQUUTDUAU
      UQUUJVFVFUCZUGZUULEUGZUUMFUGZSZSZUUPSZAUUTUUKUVFUUPUUJEFVGVHAUVGUVBUUHUUL
      JVDZUUMKVDZSZSZSZUUTUVGUVBUVEUUPSZSAUVLUVBUVEUUPVIAUVMUVKUVBABUOZEUGZCUOZ
      FUGZSZUUGGVDZSZCUUMTZBUULTZUUHUVNJVDZUVPKVDZSZSZCUUMTZBUULTZUVMUVKAUWAUWG
      BUULAUVTUWFCUUMRVJVJUWBUVOUVDSZUUGUUNVDZSZBUULTUWIBUULTZUWJBUULTZSUVMUWAU
      WKBUULUWAUVRCUUMTZUVSCUUMTZSUWKUVRUVSCUUMVKUWNUWIUWOUWJUWNUVOCUUMTZUVQCUU
      MTZSUWIUVOUVQCUUMVKUWPUVOUWQUVDUUMVFUGZUWPUVOVSUUJVBVLZUVOCUUMVFVMVNCUUMF
      VOVPVTUWRUWOUWJVSUWSCUUMUUGGVFVQVNVPVTVRUWIUWJBUULVKUWLUVEUWMUUPUWLUVOBUU
      LTZUVDBUULTZSUVEUVOUVDBUULVKUWTUVCUXAUVDBUULEVOUULVFUGZUXAUVDVSUUJUTVLZUV
      DBUULVFVMVNVPVTUXBUWMUUPVSUXCBUULUUGUUNVFVQVNVPWAUWHUUHUWCUVISZSZBUULTUUH
      BUULTZUXDBUULTZSUVKUWGUXEBUULUWGUUHCUUMTZUWECUUMTZSUXEUUHUWECUUMVKUXHUUHU
      XIUXDUWRUXHUUHVSUWSUUHCUUMVFVMVNUXIUWCCUUMTZUWDCUUMTZSUXDUWCUWDCUUMVKUXJU
      WCUXKUVIUWRUXJUWCVSUWSUWCCUUMVFVMVNUXKCUUMUVPVCZKVDZUVIUWRUXKUXMVSUWSCUUM
      UVPKVFWBVNUXLUUMKCUUMUWSWCWDVTVPVTVPVTVRUUHUXDBUULVKUXFUUHUXGUVJUXBUXFUUH
      VSUXCUUHBUULVFVMVNUXGUWCBUULTZUVIBUULTZSUVJUWCUVIBUULVKUXNUVHUXOUVIUXNBUU
      LUVNVCZJVDZUVHUXBUXNUXQVSUXCBUULUVNJVFWBVNUXPUULJBUULUXCWCWDVTUXBUXOUVIVS
      UXCUVIBUULVFVMVNVPVTVPWAWEWFWGAUUTUVBUUTSUVLAUUTUVBAUUTUVBAUUTSZUUEUVAUUJ
      MNWHUXRUUJUUBUUEAUUHUUSWIAUUHUUFUUSUUIWJWKWLWMWNUVBUUTUVKUVBUUSUVJUUHUUJJ
      KVFVFWOWFWPWQWRWGXAYSUVTBCDWSZUEUBUOZEUGZUNUOZFUGZSZUUGBUXTCUYBGVCZVCZVDZ
      SZUBUNDWSZUEUURIUXSIBCEFGWTUXSOBCDEFGXBXCXDUXSUYIUVTUYHBCDUBUNUVTUBXLUVTU
      NXLUYDUYGBUYDBXLBUUGUYFBUXTUYEXEXFXGUYDUYGCUYDCXLCUUGUYFCBUXTUYECUXTXMCUY
      BGXEXHXFXGUVNUXTVDZUVPUYBVDZSZUVRUYDUVSUYGUYLUVOUYAUVQUYCUYLUVNUXTEUYJUYK
      XIXJUYLUVPUYBFUYJUYKXKXJXNUYLGUYFUUGUYKUYJGUYEUYFCUYBGXOBUXTUYEXOXPXQXNXR
      XDUYHUUQUBUNDUAUUJUXTUYBULZVDZUUKUYDUUPUYGUYNUUKUYMYQUGUYDUUJUYMYQYBUXTUY
      BEFXSXTUYNUUOUYFUUGUYNUUOUBUULUNUUMUYFVCZVCZUYFUYPUBUULBUXTUUNVCZVCUUOUBU
      ULUYOUYQUYOBUXTUNUUMUYEVCZVCUYQUNBUUMUXTUYEYABUXTUYRUUNCUNUUMGYCYDXCYDBUB
      UULUUNYCXCUBUNUUJUYFYEYFXQXNUUKUVBUUPYQUVAUUJEFWHYGYHYLYIDUAHUUBYJYKYMYNY
      QHIYOYP $.
  $}

  ${
    $d f h G $.  $d f h R $.  $d f h S $.  $d f h T $.  $d f h ph $.
    fcobij.1 $e |- ( ph -> G : S -1-1-onto-> T ) $.
    fcobij.2 $e |- ( ph -> R e. U ) $.
    fcobij.3 $e |- ( ph -> S e. V ) $.
    fcobij.4 $e |- ( ph -> T e. W ) $.
    $( Composing functions with a bijection yields a bijection between sets of
       functions.  (Contributed by Thierry Arnoux, 25-Aug-2017.) $)
    fcobij $p |- ( ph -> ( f e. ( S ^m R ) |-> ( G o. f ) ) :
                                         ( S ^m R ) -1-1-onto-> ( T ^m R ) ) $=
      ( ccom wcel wa wf adantr elmapd wceq vh cmap ccnv cmpt eqid wf1o f1of syl
      co cv biimpa fco syl2anc mpbird f1ocnv 3syl cid cres simpr coeq2d eqtr4di
      wb coass simpll f1ococnv2 simplrr fcoi2 3eqtrrd f1ococnv1 simplrl impbida
      coeq1d f1o2d ) AFUACBUBUIZDBUBUIZGFUJZNZGUCZUAUJZNZFVNVQUDZWAUEAVPVNOZPZV
      QVOOZBDVQQZWCCDGQZBCVPQZWEAWFWBACDGUFZWFJCDGUGUHRAWBWGACBVPHELKSUKZBCDGVP
      ULUMAWDWEVBWBADBVQIEMKSRUNAVSVOOZPZVTVNOZBCVTQZWKDCVRQZBDVSQZWMAWNWJAWHDC
      VRUFWNJCDGUODCVRUGUPRAWJWOADBVSIEMKSUKZBDCVRVSULUMAWLWMVBWJACBVTHELKSRUNA
      WBWJPZPZVPVTTZVSVQTZWRWSPZVQGVRNZVSNZUQDURZVSNZVSXAVQGVTNXCXAVPVTGWRWSUSU
      TGVRVSVCVAXAXBXDVSXAAWHXBXDTAWQWSVDZJCDGVEUPVLXAWOXEVSTXAAWJWOXFAWBWJWSVF
      WPUMBDVSVGUHVHWRWTPZVTVRGNZVPNZUQCURZVPNZVPXGVTVRVQNXIXGVSVQVRWRWTUSUTVRG
      VPVCVAXGXHXJVPXGAWHXHXJTAWQWTVDZJCDGVIUPVLXGWGXKVPTXGAWBWGXLAWBWJWTVJWIUM
      BCVPVGUHVHVKVM $.

    $d f h O $.  $d f h Q $.  $d g h O $.  $d g h R $.  $d g h S $.  $d f X $.
    $d f Y $.
    fcobijfs.5 $e |- ( ph -> O e. S ) $.
    fcobijfs.6 $e |- Q = ( G ` O ) $.
    fcobijfs.7 $e |- X = { g e. ( S ^m R ) | g finSupp O } $.
    fcobijfs.8 $e |- Y = { h e. ( T ^m R ) | h finSupp Q } $.
    $( Composing finitely supported functions with a bijection yields a
       bijection between sets of finitely supported functions.  See also
       ~ mapfien .  (Contributed by Thierry Arnoux, 25-Aug-2017.)  (Revised by
       Thierry Arnoux, 1-Sep-2019.) $)
    fcobijfs $p |- ( ph -> ( f e. X |-> ( G o. f ) ) : X -1-1-onto-> Y ) $=
      ( cv cid cres ccom cmpt wf1o cfsupp wbr cmap co crab breq1 cbvrabv eqtr4i
      f1oi a1i mapfien wcel wceq ssrab3 sseli wa coass wf syl elmapi fco syl2an
      f1of fcoi1 eqtr3id sylan2 mpteq2dva f1oeq1d mpbid ) ANOGNJGUDZUECUFZUGUGZ
      UHZUINOGNJVSUGZUHZUIAICDCENOFGVTJLBFMKNHUDZKUJUKZHDCULUMZUNIUDZKUJUKZIWGU
      NUBWIWFIHWGWHWEKUJUOUPUQUCUACCVTUIACURUSPQRQSTUTANOWBWDAGNWAWCVSNVAAVSWGV
      AZWAWCVBNWGVSWFHWGNUBVCVDAWJVEZWAWCVTUGZWCJVSVTVFWKCEWCVGZWLWCVBADEJVGZCD
      VSVGWMWJADEJUIWNPDEJVLVHVSDCVICDEJVSVJVKCEWCVMVHVNVOVPVQVR $.
  $}

  ${
    $d G f h $.  $d O f $.  $d O g h $.  $d R f h $.  $d R g $.  $d S f h $.
    $d S g $.  $d T f h $.  $d T g $.  $d X f $.  $d Y f $.  $d f h ph $.
    fcobijfs2.1 $e |- ( ph -> G : R -1-1-onto-> S ) $.
    fcobijfs2.2 $e |- ( ph -> R e. U ) $.
    fcobijfs2.3 $e |- ( ph -> S e. V ) $.
    fcobijfs2.4 $e |- ( ph -> T e. W ) $.
    fcobijfs2.5 $e |- ( ph -> O e. T ) $.
    fcobijfs2.7 $e |- X = { g e. ( T ^m S ) | g finSupp O } $.
    fcobijfs2.8 $e |- Y = { h e. ( T ^m R ) | h finSupp O } $.
    $( Composing finitely supported functions with a bijection yields a
       bijection between sets of finitely supported functions.  See also
       ~ fcobijfs and ~ mapfien .  (Contributed by Thierry Arnoux,
       10-Jan-2026.) $)
    fcobijfs2 $p |- ( ph -> ( f e. X |-> ( f o. G ) ) : X -1-1-onto-> Y ) $=
      ( cid cres cv ccom cmpt wf1o cfv cfsupp cmap co crab breq1 cbvrabv eqtr4i
      wbr eqid f1oi a1i mapfien wcel fvresi syl breq2d rabbidv eqtr4di f1oeq3dd
      wceq ssrab3 sseli wa wf elmapi fco syl2anr fcoi2 sylan2 mpteq2dva f1oeq1d
      f1of mpbid ) AMNFMUBDUCZFUDZIUEZUEZUFZUGMNFMWDUFZUGAHUDZJWBUHZUIUPZHDBUJU
      KZULZNMWFAHCDBDMWLKFIWBLWIELJMGUDZJUIUPZGDCUJUKZULWHJUIUPZHWOULTWPWNHGWOW
      HWMJUIUMUNUOWLUQWIUQODDWBUGADURUSQRPRSUTAWLWPHWKULNAWJWPHWKAWIJWHUIAJDVAW
      IJVHSDJVBVCVDVEUAVFVGAMNWFWGAFMWEWDWCMVAAWCWOVAZWEWDVHZMWOWCWNGWOMTVIVJAW
      QVKBDWDVLZWRWQCDWCVLBCIVLZWSAWCDCVMABCIUGWTOBCIVTVCBCDWCIVNVOBDWDVPVCVQVR
      VSWA $.
  $}

  ${
    $d x A $.  $d x F $.  $d x Z $.  $d x ph $.
    suppss3.1 $e |- G = ( x e. A |-> B ) $.
    suppss3.a $e |- ( ph -> A e. V ) $.
    suppss3.z $e |- ( ph -> Z e. W ) $.
    suppss3.2 $e |- ( ph -> F Fn A ) $.
    suppss3.3 $e |- ( ( ph /\ x e. A /\ ( F ` x ) = Z ) -> B = Z ) $.
    $( Deduce a function's support's inclusion in another function's support.
       (Contributed by Thierry Arnoux, 7-Sep-2017.)  (Revised by Thierry
       Arnoux, 1-Sep-2019.) $)
    suppss3 $p |- ( ph -> ( G supp Z ) C_ ( F supp Z ) ) $=
      ( csupp co wcel wa wceq cvv cmpt oveq1i cv cfv simpl eldifi adantl wn csn
      cdif ccnv cima wfn fnex syl2anc suppimacnv eleq2d wb elpreima bitrd baibd
      syl notbid biimpd expimpd wne fvex eldifsn mpbiran necon2bbii 3imtr4g imp
      eldif syl3anc suppss2 eqsstrid ) AFIOPBCDUAZIOPEIOPZFVQIOJUBACDBGVRIABUCZ
      CVRUJQZRAVSCQZVSEUDZISZDISAVTUEVTWAAVSCVRUFUGAVTWCAWAVSVRQZUHZRWBTIUIUJZQ
      ZUHZVTWCAWAWEWHAWARZWEWHWIWDWGAWDWAWGAWDVSEUKWFULZQZWAWGRZAVRWJVSAETQZIHQ
      VRWJSAECUMZCGQWMMKCGEUNUOLETHIUPUOUQAWNWKWLURMCVSWFEUSVBUTVAVCVDVEVSCVRVM
      WGWBIWGWBTQWBIVFVSEVGWBTIVHVIVJVKVLNVNKVOVP $.
  $}

  ${
    $d B x y z $.  $d C x y z $.  $d F x $.  $d F y z $.  $d G y z $.
    $d Z y z $.  $d ph y z $.
    fsuppcurry1.g $e |- G = ( x e. B |-> ( C F x ) ) $.
    fsuppcurry1.z $e |- ( ph -> Z e. U ) $.
    fsuppcurry1.a $e |- ( ph -> A e. V ) $.
    fsuppcurry1.b $e |- ( ph -> B e. W ) $.
    fsuppcurry1.f $e |- ( ph -> F Fn ( A X. B ) ) $.
    fsuppcurry1.c $e |- ( ph -> C e. A ) $.
    fsuppcurry1.1 $e |- ( ph -> F finSupp Z ) $.
    $( Finite support of a curried function with a constant first argument.
       (Contributed by Thierry Arnoux, 7-Jul-2023.) $)
    fsuppcurry1 $p |- ( ph -> G finSupp Z ) $=
      ( cvv wcel vy vz wfun c2nd cxp cres csupp co cima cfn wss cfsupp wbr cmpt
      cv oveq2 cbvmptv eqtri mptexd eqeltrid funmpt2 a1i wfo fo2nd fofun funres
      ax-mp mp1i fsuppimpd imafi syl2anc wa ovexd fmptd cdif wn wceq eldif wrex
      cfv cop wne ad2antrr simplr opelxpd df-ov simpr neqned eqnetrrd eqnetrrid
      fvmptd3 wb wfn xpexd elsuppfn syl3anc mpbir2and fveq2d xpss adantr sselid
      fvresd op2ndg 3eqtrd rspcedeq1vd cin fofn fnresin mp2b ssv sseqin2 fneq2i
      mpbi cdm suppssdm fndmd sseqtrid sstrdi fvelimabd mpbird ex con1d sylan2b
      impr suppss suppssfifsupp syl32anc ) AHSTHUCZKFTZUDSSUEZUFZGKUGUHZUIZUJTZ
      HKUGUHYMUKHKULUMAHUADEUAUOZGUHZUNZSHBDEBUOZGUHZUNYQLBUADYSYPYRYOEGUPZUQUR
      ZAUADYPJOUSUTYHABDYSHLVAVBMAYKUCZYLUJTYNUDUCZUUBASSUDVCZUUCVDSSUDVEVGYJUD
      VFVHAGKRVIYKYLVJVKADSUAHYMKAUADYPSHAYODTZVLZEYOGVMUUAVNYODYMVOTAUUEYOYMTZ
      VPZVLYOHVTZKVQZYODYMVRAUUEUUHUUJUUFUUJUUGUUFUUJVPZUUGUUFUUKVLZUUGUBUOZYKV
      TZYOVQUBYLVSZUULUBEYOWAZYLUUNYOUULUUPYLTZUUPCDUEZTZUUPGVTZKWBZUULEYOCDAEC
      TZUUEUUKQWCZAUUEUUKWDZWEZUULUUTYPKEYOGWFUULUUIYPKUULBYOYSYPDHSLYTUVDUULEY
      OGVMWKUULUUIKUUFUUKWGWHWIWJAUUQUUSUVAVLWLZUUEUUKAGUURWMUURSTYIUVFPACDIJNO
      WNMUUPGSFUURKWOWPWCWQUULUUMUUPVQZVLZUUNUUPYKVTUUPUDVTZYOUVHUUMUUPYKUULUVG
      WGWRUVHUUPYJUDUVHUURYJUUPCDWSZUULUUSUVGUVEWTXAXBUVHUVBUUEUVIYOVQUULUVBUVG
      UVCWTUULUUEUVGUVDWTEYOCDXCVKXDXEAUUGUUOWLUUEUUKAUBYJYLYOYKYKYJWMZAYKSYJXF
      ZWMZUVKUUDUDSWMUVMVDSSUDXGSYJUDXHXIUVLYJYKYJSUKUVLYJVQYJXJYJSXKXMXLXMVBAY
      LUURYJAGXNYLUURGKXOAUURGPXPXQUVJXRXSWCXTYAYBYDYCYEYMHSFKYFYG $.
  $}

  ${
    $d A x y z $.  $d C x y z $.  $d F x y $.  $d F z $.  $d G y z $.
    $d Z y z $.  $d ph y z $.
    fsuppcurry2.g $e |- G = ( x e. A |-> ( x F C ) ) $.
    fsuppcurry2.z $e |- ( ph -> Z e. U ) $.
    fsuppcurry2.a $e |- ( ph -> A e. V ) $.
    fsuppcurry2.b $e |- ( ph -> B e. W ) $.
    fsuppcurry2.f $e |- ( ph -> F Fn ( A X. B ) ) $.
    fsuppcurry2.c $e |- ( ph -> C e. B ) $.
    fsuppcurry2.1 $e |- ( ph -> F finSupp Z ) $.
    $( Finite support of a curried function with a constant second argument.
       (Contributed by Thierry Arnoux, 7-Jul-2023.) $)
    fsuppcurry2 $p |- ( ph -> G finSupp Z ) $=
      ( cvv wcel vy vz wfun c1st cxp cres csupp co cima cfn wss cfsupp wbr cmpt
      cv oveq1 cbvmptv eqtri mptexd eqeltrid funmpt2 a1i wfo fo1st fofun funres
      ax-mp mp1i fsuppimpd imafi syl2anc wa ovexd fmptd cdif wn wceq eldif wrex
      cfv cop wne simplr ad2antrr opelxpd df-ov simpr neqned eqnetrrd eqnetrrid
      fvmptd3 wb wfn xpexd elsuppfn syl3anc mpbir2and fveq2d xpss adantr sselid
      fvresd op1stg 3eqtrd rspcedeq1vd cin fofn fnresin mp2b ssv sseqin2 fneq2i
      mpbi cdm suppssdm fndmd sseqtrid sstrdi fvelimabd mpbird ex con1d sylan2b
      impr suppss suppssfifsupp syl32anc ) AHSTHUCZKFTZUDSSUEZUFZGKUGUHZUIZUJTZ
      HKUGUHYMUKHKULUMAHUACUAUOZEGUHZUNZSHBCBUOZEGUHZUNYQLBUACYSYPYRYOEGUPZUQUR
      ZAUACYPINUSUTYHABCYSHLVAVBMAYKUCZYLUJTYNUDUCZUUBASSUDVCZUUCVDSSUDVEVGYJUD
      VFVHAGKRVIYKYLVJVKACSUAHYMKAUACYPSHAYOCTZVLZYOEGVMUUAVNYOCYMVOTAUUEYOYMTZ
      VPZVLYOHVTZKVQZYOCYMVRAUUEUUHUUJUUFUUJUUGUUFUUJVPZUUGUUFUUKVLZUUGUBUOZYKV
      TZYOVQUBYLVSZUULUBYOEWAZYLUUNYOUULUUPYLTZUUPCDUEZTZUUPGVTZKWBZUULYOECDAUU
      EUUKWCZAEDTZUUEUUKQWDZWEZUULUUTYPKYOEGWFUULUUIYPKUULBYOYSYPCHSLYTUVBUULYO
      EGVMWKUULUUIKUUFUUKWGWHWIWJAUUQUUSUVAVLWLZUUEUUKAGUURWMUURSTYIUVFPACDIJNO
      WNMUUPGSFUURKWOWPWDWQUULUUMUUPVQZVLZUUNUUPYKVTUUPUDVTZYOUVHUUMUUPYKUULUVG
      WGWRUVHUUPYJUDUVHUURYJUUPCDWSZUULUUSUVGUVEWTXAXBUVHUUEUVCUVIYOVQUULUUEUVG
      UVBWTUULUVCUVGUVDWTYOECDXCVKXDXEAUUGUUOWLUUEUUKAUBYJYLYOYKYKYJWMZAYKSYJXF
      ZWMZUVKUUDUDSWMUVMVDSSUDXGSYJUDXHXIUVLYJYKYJSUKUVLYJVQYJXJYJSXKXMXLXMVBAY
      LUURYJAGXNYLUURGKXOAUURGPXPXQUVJXRXSWDXTYAYBYDYCYEYMHSFKYFYG $.
  $}

  ${
    $d F i j $.  $d G i x $.  $d G j $.  $d R i x $.  $d R j $.  $d S i $.
    $d S j $.  $d T i x $.  $d T j $.  $d Y i x $.  $d Z i x $.  $d i ph x $.
    $d j ph $.
    offinsupp1.a $e |- ( ph -> A e. V ) $.
    offinsupp1.y $e |- ( ph -> Y e. U ) $.
    offinsupp1.z $e |- ( ph -> Z e. W ) $.
    offinsupp1.f $e |- ( ph -> F : A --> S ) $.
    offinsupp1.g $e |- ( ph -> G : A --> T ) $.
    offinsupp1.1 $e |- ( ph -> F finSupp Y ) $.
    offinsupp1.2 $e |- ( ( ph /\ x e. T ) -> ( Y R x ) = Z ) $.
    $( Finite support for a function operation.  (Contributed by Thierry
       Arnoux, 8-Jul-2023.) $)
    offinsupp1 $p |- ( ph -> ( F oF R G ) finSupp Z ) $=
      ( vi vj cof co cfsupp wbr csupp wcel fsuppimpd ssidd suppssof1 ssfid wfun
      cfn cvv wb cv wa ovexd inidm off ffund funisfsupp syl3anc mpbird ) AHIDUC
      ZUDZMUEUFZVGMUGUDZUNUHZAHLUGUDZVIAHLSUIABHICFGVKDEJLMAVKUJTQRNOUKULAVGUMV
      GUOUHMKUHVHVJUPACUOVGAUAUBCCCDEFUOHIJJAUAUQZEUHUBUQZFUHURURVLVMDUSQRNNCUT
      VAVBAHIVFUSPVGUOKMVCVDVE $.
  $}

  ${
    ffs2.1 $e |- C = ( B \ { Z } ) $.
    $( Rewrite a function's support based with its codomain rather than the
       universal class.  See also ~ fsuppeq .  (Contributed by Thierry Arnoux,
       27-Aug-2017.)  (Revised by Thierry Arnoux, 1-Sep-2019.) $)
    ffs2 $p |- ( ( A e. V /\ Z e. W /\ F : A --> B )
      -> ( F supp Z ) = ( `' F " C ) ) $=
      ( wcel wf w3a csupp co ccnv csn cdif cima wceq fsuppeq 3impia imaeq2i
      eqtr4di ) AEIZGFIZABDJZKDGLMZDNZBGOPZQZUGCQUCUDUEUFUIRBDAEFGSTCUHUGHUAUB
      $.
  $}

  ${
    ffsrn.z $e |- ( ph -> Z e. W ) $.
    ffsrn.0 $e |- ( ph -> F e. V ) $.
    ffsrn.1 $e |- ( ph -> Fun F ) $.
    ffsrn.2 $e |- ( ph -> ( F supp Z ) e. Fin ) $.
    $( The range of a finitely supported function is finite.  The proof uses
       ~ fnrndomnum rather than ~ fnrndomg , and so does not require ~ ax-ac .
       (Contributed by Thierry Arnoux, 27-Aug-2017.)  (Revised by Vincent
       Gonzalez, 24-Aug-2026.) $)
    ffsrn $p |- ( ph -> ran F e. Fin ) $=
      ( crn cvv cima cres cun cfn wceq wss wcel syl2anc syl ccnv csn cdif dfdm4
      wfun cdm dfrn4 eqtri wa wfn fnresdm sylbir sylancl imaundi reseq2i undif1
      df-fn ssequn2 mpbi imaeq2i resundi 3eqtr3i eqtr3di rneqd rnun eqtrdi cdom
      ssv wbr csupp co suppimacnv eqeltrrd finnum wfo cnvimass fores fnrndomnum
      ccrd fofn sylc domfi snfi df-ima funimacnv eqtr3id inss1 eqsstrdi sylancr
      cin ssfi unfi eqeltrd ) ABJZBBUAZKEUBZUCZLZMZJZBWOWPLZMZJZNZOAWNWSXBNZJXD
      ABXEABWOKLZMZBXEABUEZBUFZXFPZXGBPZHXIWOJXFBUDWOUGUHXHXJUIBXFUJXKBXFUQXFBU
      KULUMBWOWQWPNZLZMBWRXANZMXGXEXMXNBWOWQWPUNUOXMXFBXLKWOXLKWPNZKKWPUPWPKQXO
      KPWPVHWPKURUSUHUTUOBWRXAVAVBVCVDWSXBVEVFAWTORZXCORZXDORAWRORZWTWRVGVIZXPA
      BEVJVKZWROABCREDRXTWRPGFBCDEVLSIVMZAWRVSUFRZWSWRUJZXSAXRYBYAWRVNTAWRBWRLZ
      WSVOZYCAXHWRXIQYEHBWQVPWRBVQUMWRYDWSVTTWRWSVRWAWRWTWBSAWPORXCWPQXQEWCAXCW
      PWNWJZWPAXCBXALZYFBXAWDAXHYGYFPHWPBWETWFWPWNWGWHWPXCWKWIWTXCWLSWM $.
      $( $j usage 'ffsrn' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    cocnvf1o.1 $e |- ( ph -> F : A --> B ) $.
    cocnvf1o.2 $e |- ( ph -> G : A --> B ) $.
    cocnvf1o.3 $e |- ( ph -> H : A -1-1-onto-> A ) $.
    $( Composing with the inverse of a bijection.  (Contributed by Thierry
       Arnoux, 15-Jan-2026.) $)
    cocnvf1o $p |- ( ph -> ( F = ( G o. H ) <-> G = ( F o. `' H ) ) ) $=
      ( ccom wceq wa simpr coeq1d coass eqtrdi syl coeq2d wf fcoi1 eqtrd adantr
      ccnv cid cres wf1o f1ococnv2 eqtr2d f1ococnv1 impbida ) ADEFJZKZEDFUCZJZK
      ZAULLZUNEFUMJZJZEUPUNUKUMJURUPDUKUMAULMNEFUMOPAUREKULAUREUDBUEZJZEAUQUSEA
      BBFUFZUQUSKIBBFUGQRABCESUTEKHBCETQUAUBUHAUOLZUKDUMFJZJZDVBUKUNFJVDVBEUNFA
      UOMNDUMFOPAVDDKUOAVDDUSJZDAVCUSDAVAVCUSKIBBFUIQRABCDSVEDKGBCDTQUAUBUHUJ
      $.
  $}

  ${
    $d f g x A $.  $d f g x B $.  $d f g x C $.  $d f g x V $.  $d f g x W $.
    $d f g X $.  $d f g x Z $.
    resf1o.1 $e |- X = { f e. ( B ^m A ) | ( `' f " ( B \ { Z } ) ) C_ C } $.
    resf1o.2 $e |- F = ( f e. X |-> ( f |` C ) ) $.
    $( Restriction of functions to a superset of their support creates a
       bijection.  (Contributed by Thierry Arnoux, 12-Sep-2017.) $)
    resf1o $p |- ( ( ( A e. V /\ B e. W /\ C C_ A ) /\ Z e. B )
                                 -> F : X -1-1-onto-> ( B ^m C ) ) $=
      ( wcel wa cres cvv wceq wf syl ad2antrr c0 vg vx wss w3a cmap co cdif csn
      cv cxp cun resexg adantl simpr difexg 3ad2ant1 xpexg sylancl adantr unexg
      snex syl2anc adantlr ccnv cima reqabi anbi1i simprr simprll simp3 fssresd
      elmapi simp2 simp1 ssexd elmapg mpbird eqeltrd biimpi reseq2d wfn fnresdm
      undif ffn 3syl eqtr2d resundi eqtrdi eqcomd csupp cin simprlr simplr eqid
      wb ffs2 syl3anc sseqin2 3sstr4d simpl inundif fneq2i sylibr vex fnsuppres
      a1i inindif syl121anc mpbid uneq12d eqtrd ad2antrl fconst6g fun2 syl21anc
      jca disjdif feq12d biimpar cfv fveq1d ffnd fconstg ad3antlr fvun2 fvconst
      syl112anc 3eqtrd suppss eqsstrrd reseq1d res0 eqtr4i 3eqtr4ri fresaunres1
      reseq2i jca31 impbida bitrid f1od ) AFLZBGLZCAUCZUDZIBLZMZDUAHBCUEUFZDUIZ
      CNZUAUIZACUGZIUHZUJZUKZEOOKUUHHLZUUIOLUUFUUHCHULUMUUDUUJUUGLZUUNOLZUUEUUD
      UUPMUUPUUMOLZUUQUUDUUPUNUUDUURUUPUUDUUKOLZUULOLUURUUAUUBUUSUUCACFUOUPIVAU
      UKUULOOUQURUSUUJUUMUUGOUTVBVCUUOUUJUUIPZMUUHBAUEUFZLZUUHVDBUULUGZVEZCUCZM
      ZUUTMZUUFUUPUUHUUNPZMZUUOUVFUUTUVEDHUVAJVFVGUUFUVGUVIUUFUVGMZUUPUVHUVJUUJ
      UUIUUGUUFUVFUUTVHZUVJUUIUUGLZCBUUIQZUVJABCUUHUVJUVBABUUHQZUUFUVBUVEUUTVIZ
      UUHBAVLZRZUUDUUCUUEUVGUUAUUBUUCVJZSZVKUUDUVLUVMWOZUUEUVGUUDUUBCOLUVTUUAUU
      BUUCVMZUUDCAFUUAUUBUUCVNZUVRVOBCUUIGOVPVBSVQVRUVJUUHUUIUUHUUKNZUKZUUNUVJU
      UHUUHCUUKUKZNZUWDUVJUWFUUHANZUUHUVJUUCUWFUWGPUVSUUCUWEAUUHUUCUWEAPZCAWCVS
      ZVTRUVJUVNUUHAWAZUWGUUHPUVQABUUHWDZAUUHWBWEWFUUHCUUKWGWHUVJUUIUUJUWCUUMUV
      JUUJUUIUVKWIUVJUUHIWJUFZACWKZUCZUWCUUMPZUVJUVDCUWLUWMUUFUVBUVEUUTWLUVJUUA
      UUEUVNUWLUVDPZUUDUUAUUEUVGUWBSUUDUUEUVGWMZUVQABUVCUUHFBIUVCWNWPZWQUVJUUCU
      WMCPZUVSUUCUWSCAWRVSRWSUVJUVBUUEUWNUWOWOZUVOUWQUVBUUEMZUUHUWMUUKUKZWAZUUH
      OLZUUEUWMUUKWKTPZUWTUXAUWJUXCUXAUVBUVNUWJUVBUUEWTUVPUWKWEUXBAUUHACXAXBXCU
      XDUXADXDXFUVBUUEUNUXEUXAACXGXFUWMUUKUUHBOIXEXHVBXIXJXKXPUUFUVIMZUVBUVEUUT
      UXFUUBUUAUVNUVBUUDUUBUUEUVIUWASUUDUUAUUEUVIUWBSZUXFUWEBUUNQZUVNUXFCBUUJQZ
      UUKBUUMQZCUUKWKZTPZUXHUUPUXIUUFUVHUUJBCVLXLZUXFUUEUXJUUDUUEUVIWMZUUKIBXMR
      ZUXLUXFCAXQZXFCUUKBUUJUUMXNXOUXFUWEABUUNUUHUXFUUHUUNUUFUUPUVHVHZWIUXFUUCU
      WHUUDUUCUUEUVIUVRSUWIRXRXIZUUBUUAMUVBUVNBAUUHGFVPXSXOUXFUVDUWLCUXFUUAUUEU
      VNUWPUXGUXNUXRUWRWQUXFABUBUUHCIUXRUXFUBUIZUUKLZMZUXSUUHXTUXSUUNXTZUXSUUMX
      TZIUYAUXSUUHUUNUXFUVHUXTUXQUSYAUYAUUJCWAUUMUUKWAUXLUXTUYBUYCPUYACBUUJUXFU
      XIUXTUXMUSYBUYAUUKUULUUMUUEUUKUULUUMQZUUDUVIUXTUUKIBYCYDZYBUXLUYAUXPXFUXF
      UXTUNZCUUKUUJUUMUXSYEYGUYAUYDUXTUYCIPUYEUYFUUKIUXSUUMYFVBYHYIYJUXFUUIUUNC
      NZUUJUXFUUHUUNCUXQYKUXFUXIUXJUUJUXKNZUUMUXKNZPZUYGUUJPUXMUXOUYJUXFUUMTNZU
      UJTNZUYIUYHUYKTUYLUUMYLUUJYLYMUXKTUUMUXPYPUXKTUUJUXPYPYNXFCUUKBUUJUUMYOWQ
      WFYQYRYSYT $.
  $}

  ${
    $d f A $.  $d f B $.  $d f C $.
    maprnin.1 $e |- A e. _V $.
    maprnin.2 $e |- B e. _V $.
    $( Restricting the range of the mapping operator.  (Contributed by Thierry
       Arnoux, 30-Aug-2017.) $)
    maprnin $p |- ( ( B i^i C ) ^m A ) = { f e. ( B ^m A ) | ran f C_ C } $=
      ( cin cv wf cab cmap co wcel crn wss wa crab wfn wb ffn baibr syl pm5.32i
      df-f elmap anbi1i fin 3bitr4ri abbii inex1 mapval df-rab 3eqtr4i ) ABCGZD
      HZIZDJUOBAKLZMZUONCOZPZDJUNAKLUSDUQQUPUTDABUOIZUSPVAACUOIZPUTUPVAUSVBVAUO
      ARZUSVBSABUOTVBVCUSACUOUDUAUBUCURVAUSBAUOFEUEUFABCUOUGUHUIUNADBCFUJEUKUSD
      UQULUM $.
  $}

  ${
    $d w x y z A $.  $d w x y z F $.  $d x y R $.  $d w ph $.
    fpwrelmapffslem.1 $e |- A e. _V $.
    fpwrelmapffslem.2 $e |- B e. _V $.
    fpwrelmapffslem.3 $e |- ( ph -> F : A --> ~P B ) $.
    fpwrelmapffslem.4 $e |- ( ph ->
                        R = { <. x , y >. | ( x e. A /\ y e. ( F ` x ) ) } ) $.
    $( Lemma for ~ fpwrelmapffs .  For this theorem, the sets ` A ` and ` B `
       could be infinite, but the relation ` R ` itself is finite.
       (Contributed by Thierry Arnoux, 1-Sep-2017.)  (Revised by Thierry
       Arnoux, 1-Sep-2019.) $)
    fpwrelmapffslem $p |- ( ph -> ( R e. Fin
              <-> ( ran F C_ Fin /\ ( F supp (/) ) e. Fin ) ) ) $=
      ( vz cfn wcel wa c0 wceq wb wex cvv vw cdm crn csupp co wss cv copab wrel
      cfv relopabv releq mpbiri relfi 3syl cab wrex cuni ancom exbii fvex eleq2
      rexcom4 ceqsexv bitr3i rexbii r19.42v df-rex bitr2i a1i vex eleq1w anbi2d
      3bitr3ri exbidv elab eluniab 3bitr4g eqrdv eleq1d adantr wi cpw wf fnrnfv
      wfn ffn 0ex fex sylancl wfun ffund syl csn cdif crab cmpt ccnv cima mpan2
      opabdm suppimacnv feqmptd cnveqd imaeq1d eqtrd mptpreima eqtrdi suppvalfn
      eqid wne mp3an23 rabbii 3eqtr3d df-rab 19.42v eqtr4i 3eqtrd eqtr4d biimpa
      n0 abbii ffsrn eqeltrrd unifi unifi3 impbid1 bitr4d opabrn sseq1d 3bitr4d
      ex pm5.32da anbi1d bitrd 3bitrd ) AFMNZFUBZMNZFUCZMNZOZGPUDUEZMNZGUCZMUFZ
      OZUUFUUDOZAFBUGZDNZCUGZUUIGUJZNZOZBCUHZQZFUIZYQUUBRKUUPUUQUUOUIUUNBCUKFUU
      OULUMFUNUOAUUBYSUUFOUUGAYSUUAUUFAYSOZUUNBSZCUPZMNZLUGZUULQZBDUQZLUPZMUFZU
      UAUUFUURUVAUVEURZMNZUVFAUVAUVHRYSAUUTUVGMAUAUUTUVGAUUJUAUGZUULNZOZBSZUVIU
      VBNZUVDOZLSZUVIUUTNUVIUVGNUVLUVORAUVOUVJBDUQZUVLUVMUVCOZLSZBDUQUVQBDUQZLS
      UVPUVOUVQBLDVCUVRUVJBDUVRUVCUVMOZLSUVJUVTUVQLUVCUVMUSUTUVMUVJLUULUUIGVAUV
      BUULUVIVBVDVEVFUVSUVNLUVMUVCBDVGUTVNUVJBDVHVIVJUUSUVLCUVIUAVKUUKUVIQZUUNU
      VKBUWAUUMUVJUUJCUAUULVLVMVOVPUVDLUVIVQVRVSVTWAUURUVFUVHUURUVEMNZUVFUVHWBU
      URUUEUVEMAUUEUVEQZYSADEWCZGWDZGDWFZUWCJDUWDGWGZBLDGWEUOWAZUURGTTPPTNZUURW
      HVJAGTNZYSAUWEDTNZUWJJHDUWDTGWIZWJWAAGWKYSADUWDGJWLWAAYSUUDAYRUUCMAYRUUNC
      SZBUPZUUCAUUPYRUWNQKUUNBCFXAWMAUUCUULTPWNWOZNBDWPZUUMCSZBDWPZUWNAUUCBDUUL
      WQZWRZUWOWSZUWPAUUCGWRZUWOWSZUXAAUWEUWJUUCUXCQZJUWEUWKUWJHUWLWTUWJUWIUXDW
      HGTTPXBWTUOAUXBUWTUWOAGUWSABDUWDGJXCXDXEXFBDUULUWOUWSUWSXJXGXHZAUUCUULPXK
      ZBDWPZUWPUWRAUWEUWFUUCUXGQZJUWGUWFUWKUWIUXHHWHBGTTDPXIXLUOUXEUXGUWRQAUXFU
      WQBDCUULYAXMVJXNUWRUWNQAUWRUUJUWQOZBUPUWNUWQBDXOUWMUXIBUUJUUMCXPYBXQVJXRX
      SVTZXTYCYDUWBUVFUVHUVEYEYLWMUVEYFYGYHAUUAUVARYSAYTUUTMAUUPYTUUTQKUUNBCFYI
      WMVTWAUURUUEUVEMUWHYJYKYMAYSUUDUUFUXJYNYOUUGUUHRAUUDUUFUSVJYP $.
  $}

  ${
    $d f r x y A $.  $d f r x y B $.
    fpwrelmap.1 $e |- A e. _V $.
    fpwrelmap.2 $e |- B e. _V $.
    fpwrelmap.3 $e |- M = ( f e. ( ~P B ^m A ) |->
       { <. x , y >. | ( x e. A /\ y e. ( f ` x ) ) } ) $.
    $( Define a canonical mapping between functions from ` A ` into subsets of
       ` B ` and the relations with domain ` A ` and range within ` B ` .  Note
       that the same relation is used in ~ axdc2lem and ~ marypha2lem1 .
       (Contributed by Thierry Arnoux, 28-Aug-2017.) $)
    fpwrelmap $p |- M : ( ~P B ^m A ) -1-1-onto-> ~P ( A X. B ) $=
      ( wtru cv wcel wa cvv a1i adantr wceq wb nfv nfan vr cpw cmap co cxp wf1o
      cfv copab wbr crab cab abid2 fvexi opabex3d mptex simpr elmapi ffvelcdmda
      cmpt wss elelpwi syl2anc imdistanda ssopab2dv df-xp 3sstr4d velpw feqmptd
      ex sylibr nfopab1 nfeq2 df-rab nfopab2 adantllr df-br eleq2 bitrdi bitrid
      cop opabidw ad2antlr elfvdm adantl fdmd eleqtrd pm4.71rd ad2antrr biimpar
      cdm bitr4d jca biimpd adantld impbid abbid 3eqtr2rd mpteq2da eqtrd ssrab2
      wf elpwi2 fmpttd feq1d mpbird pwex elmap wrel xpss sstrdi df-rel relopabv
      elpwi id nfmpt1 nfci nfrab1 nfmpt nfcv brelg adantlr simpld simprd fveq1d
      sylan rabex eqid fvmpt2 mpan2 sylan9eq eleq2d rabid syldan mpbir2and expl
      simplbda bitr3id bitr4di eqrelrd2 syl21anc impbii f1od mptru ) DUBZCUCUDZ
      CDUEZUBZFUFJEUAUUEUUGAKZCLZBKZUUHEKZUGZLZMZABUHZACUUHUUJUAKZUIZBDUJZUSZFN
      NIJUUONLUUKUUELZJUUMABCNCNLJGOUUMBUKZNLJUUIMUVAUUHUUKBUULULZUMOUNPUUSNLJU
      UPUUGLZMACUURGUOOUUTUUPUUOQZMZUVCUUKUUSQZMZRJUVEUVGUVEUVCUVFUVEUUPUUFUTZU
      VCUVEUUOUUIUUJDLZMZABUHZUUPUUFUUTUUOUVKUTUVDUUTUUNUVJABUUTUUIUUMUVIUUTUUI
      MZUUMUVIUVLUUMMUUMUULUUDLZUVIUVLUUMUPUVLUVMUUMUUTCUUDUUHUUKUUKUUDCUQZURPU
      UJUULDVAVBZVIVCVDPUUTUVDUPUUFUVKQUVEABCDVEOVFUAUUFVGVJUVEUUKACUULUSZUUSUU
      TUUKUVPQUVDUUTACUUDUUKUVNVHPUVEACUULUURUUTUVDAUUTASAUUPUUOUUNABVKZVLTUVEU
      UIMZUURUVIUUQMZBUKZUVAUULUURUVTQUVRUUQBDVMOUVRUUMUVSBUVEUUIBUUTUVDBUUTBSB
      UUPUUOUUNABVNZVLTUUIBSZTUVRUUMUVSUVRUUMUVSUVRUUMMUVIUUQUUTUUIUUMUVIUVDUVO
      VOUVRUUQUUMUVRUUQUUNUUMUVDUUQUUNRUUTUUIUUQUUHUUJVTZUUPLZUVDUUNUUHUUJUUPVP
      ZUVDUWDUWCUUOLZUUNUUPUUOUWCVQUUNABWAZVRVSWBUUTUUMUUNRUVDUUIUUTUUMUUIUUTUU
      MUUIUUTUUMMUUHUUKWJZCUUMUUHUWHLUUTUUJUUHUUKWCWDUUTUWHCQUUMUUTCUUDUUKUVNWE
      PWFVIWGWHWKZWIWLVIUVRUUQUUMUVIUVRUUQUUMUWIWMWNWOWPUVAUULQUVRUVBOWQWRWSWLU
      VGUUTUVDUVGCUUDUUKXAZUUTUVGUWJCUUDUUSXAZUVCUWKUVFUVCACUURUUDUURUUDLUVCUUI
      MUURDNHUUQBDWTXBOXCPUVGCUUDUUKUUSUVCUVFUPZXDXEUUDCUUKDHXFGXGVJUVGUUPXHZUU
      OXHZUVGUVDUVGUUPNNUEZUTUWMUVGUUPUUFUWOUVCUVHUVFUUPUUFXMZPCDXIXJUUPXKVJUWN
      UVGUUNABXLOUVGXNUVGABUUPUUOUVCUVFAUVCASAUUKUUSACUURXOVLTUVCUVFBUVCBSBUUKU
      USBACUURBACUWBXPUUQBDXQXRVLTAUUPXSBUUPXSUVQUWAUVGUWDUUNUWFUWDUUQUVGUUNUWE
      UVGUUQUUNUVGUUQUUNUVGUUQMZUUIUUMUWQUUIUVIUVCUUQUVJUVFUVCUVHUUQUVJUWPUUHUU
      JCDUUPXTYEYAZYBZUWQUUMUVIUUQUWQUUIUVIUWRYCUVGUUQUPUVGUUQUUIUUMUVSRUWSUVGU
      UIMZUUMUUJUURLUVSUWTUULUURUUJUVGUUIUULUUHUUSUGZUURUVGUUHUUKUUSUWLYDUUIUUR
      NLUXAUURQUUQBDHYFACUURNUUSUUSYGYHYIYJYKUUQBDYLVRZYMYNWLVIUVGUUIUUMUUQUWTU
      UMUVIUUQUXBYPYOWOYQUWGYRYSYTWLUUAOUUBUUC $.

    fpwrelmapffs.1 $e |- S = { f e. ( ( ~P B i^i Fin ) ^m A ) |
       ( f supp (/) ) e. Fin } $.
    $( Define a canonical mapping between finite relations (finite subsets of a
       cartesian product) and functions with finite support into finite
       subsets.  (Contributed by Thierry Arnoux, 28-Aug-2017.)  (Revised by
       Thierry Arnoux, 1-Sep-2019.) $)
    fpwrelmapffs $p |- ( M |` S ) : S -1-1-onto-> ( ~P ( A X. B ) i^i Fin ) $=
      ( vr cv cfn co wcel wa crab wf1o wceq crn wss csupp cpw cmap cxp cres cin
      c0 wtru cfv copab fpwrelmap wb wf pwex elmap birani simpr fpwrelmapffslem
      a1i 3adant1 f1oresrab mptru maprnin nfcv nfrab1 rabeqf ax-mp rabrab dfin5
      3eqtri f1oeq23 mp2an reseq2i f1oeq1 bitr2i mpbi ) FMZUANUBZVSUIUCONPZQZFD
      UDZCUEOZRZLMZNPZLCDUFUDZRZGWEUGZSZEWHNUHZGEUGZSZWKUJWBWGFLWDWHAMZCPBMWOVS
      UKPQABULZGJWDWHGSUJABCDFGHIJUMVAVSWDPZWFWPTZWGWBUNUJWQWRQABCDWFVSHIWQCWCV
      SUOWRWCCVSDIUPZHUQURWQWRUSUTVBVCVDWNWEWIWMSZWKEWETWLWITWNWTUNEWAFWCNUHCUE
      OZRZWAFVTFWDRZRZWEKXAXCTXBXDTCWCNFHWSVEWAFXAXCFXAVFVTFWDVGVHVIVTWAFWDVJVL
      ZLWHNVKEWEWLWIWMVMVNWMWJTWTWKUNEWEGXEVOWEWIWMWJVPVIVQVR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Real and Complex Numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Value of the signum of a real number, expresssed using absolute value.
     (Contributed by Thierry Arnoux, 9-Nov-2025.) $)
  sgnval2 $p |- ( ( A e. RR /\ A =/= 0 ) -> ( sgn ` A ) = ( A / ( abs ` A ) )
      ) $=
    ( wcel cc0 wne wa cfv cdiv co wceq 0red cle wbr cneg c1 adantr simplr simpr
    oveq2d clt syl2an2r cr csgn cabs simpl cc recnd dividd negeqd eqtr3d absnid
    divneg2d adantlr cxr rexrd necomd leneltd sgnn 3eqtr4rd absidd ne0gt0d sgnp
    lecasei ) AUABZACDZEZAUBFZAAUCFZGHZIACVCVDUDZVEJVEACKLZEZAAMZGHZNMZVHVFVKAA
    GHZMVMVNVKAAVEAUEBVJVEAVIUFZOZVQVCVDVJPUKVKVONVEVONIZVJVEAVPVCVDQZUGZOUHUIV
    KVGVLAGVCVJVGVLIVDAUJULRVEAUMBZVJACSLVFVNIVEAVIUNZVKACVEVCVJVIOVKJVEVJQVECA
    DVJVEACVSUOOUPAUQTURVECAKLZEZVONVHVFVEVRWCVTOWDVGAAGWDAVEVCWCVIOZVEWCQZUSRV
    EWAWCCASLVFNIWBWDAWEWFVCVDWCPUTAVATURVB $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Complex operations - misc. additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The real representation of complex numbers is zero iff both its terms are
     zero.  Cf. ~ crne0 .  (Contributed by Thierry Arnoux, 20-Aug-2023.) $)
  creq0 $p |- ( ( A e. RR /\ B e. RR ) ->
                 ( ( A = 0 /\ B = 0 ) <-> ( A + ( _i x. B ) ) = 0 ) ) $=
    ( cr wcel wa cc0 wceq wne wo wn ci cmul co caddc neorian con2bii necon2bbid
    crne0 bitr4id ) ACDBCDEZAFGBFGEZAFHBFHIZJAKBLMNMZFGUBUAAFBFOPTUBUCFABRQS $.

  $( The imaginary unit ` _i ` is not one.  (Contributed by Thierry Arnoux,
     20-Aug-2023.) $)
  1nei $p |- 1 =/= _i $=
    ( c1 ci wceq cneg c2 cc0 0ne2 nesymi caddc oveq2 1p1e2 1pneg1e0 3eqtr3g mto
    co cmul id oveq12d 1t1e1 ixi neir ) ABABCZAADZCZUDEFCFEGHUDAAIOAUCIOEFAUCAI
    JKLMNUBAAPOBBPOAUCUBABABPUBQZUERSTMNUA $.

  $( An integer unit times itself.  (Contributed by Thierry Arnoux,
     23-Aug-2020.) $)
  1neg1t1neg1 $p |- ( N e. { -u 1 , 1 } -> ( N x. N ) = 1 ) $=
    ( c1 cneg cpr wcel wceq wo cmul co elpri oveq12d neg1mulneg1e1 eqtrdi 1t1e1
    id jaoi syl ) ABCZBDEARFZABFZGAAHIZBFZARBJSUBTSUARRHIBSARARHSOZUCKLMTUABBHI
    BTABABHTOZUDKNMPQ $.

  $( Multiplying by a positive integer ` M ` yields greater than or equal
     nonnegative integers.  (Contributed by Thierry Arnoux, 13-Dec-2021.) $)
  nnmulge $p |- ( ( M e. NN /\ N e. NN0 ) -> N <_ ( M x. N ) ) $=
    ( cn wcel cn0 wa c1 cmul co simpr nn0cnd mullidd 1red cr nnre adantr nn0red
    cle nn0ge0d wbr nnge1 lemul1ad eqbrtrrd ) ACDZBEDZFZGBHIBABHIRUFBUFBUDUEJZK
    LUFGABUFMUDANDUEAOPUFBUGQUFBUGSUDGARTUEAUAPUBUC $.

  ${
    submuladdd.1 $e |- ( ph -> A e. CC ) $.
    submuladdd.2 $e |- ( ph -> B e. CC ) $.
    submuladdd.3 $e |- ( ph -> C e. CC ) $.
    submuladdd.4 $e |- ( ph -> D e. CC ) $.
    $( The product of a difference and a sum.  Cf. ~ addmulsub .  (Contributed
       by Thierry Arnoux, 6-Jul-2025.) $)
    submuladdd $p |- ( ph -> ( ( A - B ) x. ( C + D ) )
           = ( ( ( A x. C ) + ( A x. D ) ) - ( ( B x. C ) + ( B x. D ) ) ) ) $=
      ( cmin co caddc cmul subcld addcld mulcomd cc wcel wceq oveq12d addmulsub
      syl22anc 3eqtrd ) ABCJKZDELKZMKUEUDMKZDBMKZEBMKZLKZDCMKZECMKZLKZJKZBDMKZB
      EMKZLKZCDMKZCEMKZLKZJKAUDUEABCFGNADEHIOPADQREQRBQRCQRUFUMSHIFGDEBCUAUBAUI
      UPULUSJAUGUNUHUOLADBHFPAEBIFPTAUJUQUKURLADCHGPAECIGPTTUC $.
  $}

  ${
    binom2subadd.1 $e |- ( ph -> A e. CC ) $.
    binom2subadd.2 $e |- ( ph -> B e. CC ) $.
    $( The difference of the squares of the sum and difference of two complex
       numbers ` A ` and ` B ` .  (Contributed by Thierry Arnoux,
       5-Nov-2025.) $)
    binom2subadd $p |- ( ph -> ( ( ( A + B ) ^ 2 ) - ( ( A - B ) ^ 2 ) )
                              = ( 4 x. ( A x. B ) ) ) $=
      ( caddc co c2 cexp cmin cmul c4 cc wcel wceq addcld subcld 2timesd eqtr4d
      subsq syl2anc ppncand pnncand oveq12d mul4d 3eqtrd 2t2e4 oveq1i eqtrdi
      2cnd ) ABCFGZHIGBCJGZHIGJGZHHKGZBCKGZKGZLUOKGAUMUKULFGZUKULJGZKGZHBKGZHCK
      GZKGUPAUKMNULMNUMUSOABCDEPABCDEQUKULTUAAUQUTURVAKAUQBBFGUTABCBDEDUBABDRSA
      URCCFGVAABCCDEEUCACERSUDAHBHCAUJZDVBEUEUFUNLUOKUGUHUI $.
  $}

  ${
    cjsubd.1 $e |- ( ph -> A e. CC ) $.
    cjsubd.2 $e |- ( ph -> B e. CC ) $.
    $( Complex conjugate distributes over subtraction.  (Contributed by Thierry
       Arnoux, 1-Jul-2025.) $)
    cjsubd $p |- ( ph -> ( * ` ( A - B ) ) = ( ( * ` A ) - ( * ` B ) ) ) $=
      ( cc wcel cmin co ccj cfv wceq cjsub syl2anc ) ABFGCFGBCHIJKBJKCJKHILDEBC
      MN $.
  $}

  ${
    re0cj.1 $e |- ( ph -> A e. CC ) $.
    re0cj.2 $e |- ( ph -> ( Re ` A ) = 0 ) $.
    $( The conjugate of a pure imaginary number is its negative.  (Contributed
       by Thierry Arnoux, 25-Jun-2025.) $)
    re0cj $p |- ( ph -> ( * ` A ) = -u A ) $=
      ( cre cfv ci cim cmul co cmin cneg ccj oveq1d df-neg eqtr4di remimd caddc
      cc0 replimd cc wcel ax-icn a1i imcld mulcld addlidd 3eqtrd negeqd 3eqtr4d
      recnd ) ABEFZGBHFZIJZKJZUNLZBMFBLAUOSUNKJUPAULSUNKDNUNOPABCQABUNABULUNRJS
      UNRJUNABCTAULSUNRDNAUNAGUMGUAUBAUCUDAUMABCUEUKUFUGUHUIUJ $.
  $}

  ${
    receqid.1 $e |- ( ph -> A e. RR ) $.
    receqid.2 $e |- ( ph -> A =/= 0 ) $.
    $( Real numbers equal to their own reciprocal have absolute value ` 1 ` .
       (Contributed by Thierry Arnoux, 9-Nov-2025.) $)
    receqid $p |- ( ph -> ( ( 1 / A ) = A <-> ( abs ` A ) = 1 ) ) $=
      ( cfv c1 wceq co csqrt cdiv a1i cr wcel cc0 cle wbr wb cc recnd 3bitr2rd
      cabs cexp absred sqrt1 eqcomd eqeq12d resqcld sqge0d 1red sqrt11 syl22anc
      c2 0le1 wne 1cnd div11 syl112anc sqdivid syl2anc eqeq1d eqcom ) ABUAEZFGB
      ULUBHZIEZFIEZGZBFBJHZGZVGBGZAVBVDFVEABCUCAVEFVEFGAUDKUEUFAVFVCFGZVCBJHZVG
      GZVHAVCLMNVCOPFLMNFOPZVFVJQABCUGZABCUHAUIVMAUMKVCFUJUKAVCRMFRMBRMZBNUNZVL
      VJQAVCVNSAUOABCSZDVCFBUPUQAVKBVGAVOVPVKBGVQDBURUSUTTVHVIQABVGVAKT $.
  $}

  ${
    $d A x y $.  $d B x y $.
    pythagreim.1 $e |- ( ph -> A e. RR ) $.
    pythagreim.2 $e |- ( ph -> B e. RR ) $.
    $( A simplified version of the Pythagorean theorem, where the points ` A `
       and ` B ` respectively lie on the imaginary and real axes, and the right
       angle is at the origin.  (Contributed by Thierry Arnoux, 2-Nov-2025.) $)
    pythagreim $p |- ( ph -> ( ( abs ` ( B - ( _i x. A ) ) ) ^ 2 )
                            = ( ( A ^ 2 ) + ( B ^ 2 ) ) ) $=
      ( ci cmul co cmin cfv caddc c2 cexp cr wcel wceq syl2anc oveq2d recnd cc
      ccj cabs cjreim2 ax-icn mulcld subcld addcld mulcomd eqtrd absvalsqd cneg
      a1i c1 sqmuld i2 oveq1i eqtrdi sqcld mulm1d subnegd addcomd 3eqtrd eqtr3d
      subsq 3eqtr4d ) ACFBGHZIHZVGUAJZGHZCVFKHZVGGHZVGUBJLMHBLMHZCLMHZKHZAVIVGV
      JGHVKAVHVJVGGACNOBNOVHVJPEDCBUCQRAVGVJACVFACESZAFBFTOAUDULZABDSZUEZUFZACV
      FVOVRUGUHUIAVGVSUJAVMVFLMHZIHZVNVKAWAVMVLUKZIHVMVLKHVNAVTWBVMIAVTUMUKZVLG
      HZWBAVTFLMHZVLGHWDAFBVPVQUNWEWCVLGUOUPUQAVLABVQURZUSUIRAVMVLACVOURZWFUTAV
      MVLWGWFVAVBACTOVFTOWAVKPVOVRCVFVDQVCVE $.
  $}

  ${
    efiargd.1 $e |- ( ph -> A e. CC ) $.
    efiargd.2 $e |- ( ph -> A =/= 0 ) $.
    $( The exponential of the "arg" function ` Im o. log ` , deduction version.
       (Contributed by Thierry Arnoux, 5-Nov-2025.) $)
    efiargd $p |- ( ph -> ( exp ` ( _i x. ( Im ` ( log ` A ) ) ) )
                         = ( A / ( abs ` A ) ) ) $=
      ( cc wcel cc0 wne ci clog cfv cim cmul co cabs cdiv wceq efiarg syl2anc
      ce ) ABEFBGHIBJKLKMNTKBBOKPNQCDBRS $.

    arginv.1 $e |- ( ph -> -. -u A e. RR+ ) $.
    $( The argument of the inverse of a complex number ` A ` .  (Contributed by
       Thierry Arnoux, 5-Nov-2025.) $)
    arginv $p |- ( ph -> ( Im ` ( log ` ( 1 / A ) ) ) = -u ( Im ` ( log ` A ) )
       ) $=
      ( c1 cdiv clog cfv cim cneg cc wcel wceq logcld wne cpi biimpa syl21anc
      wa co reccld recne0d cc0 crp wn lognegb necon3bbid logrec syl3anc negcon2
      fveq2d imnegd eqtrd ) AFBGUAZHIZJIBHIZKZJIUQJIZKAUPURJAUQLMZUPLMZUQUPKNZU
      PURNZABCDOZAUOABCDUBABCDUCOABLMZBUDPZUSQPZVBCDAVEVFBKUEMZUFZVGCDEVEVFTZVI
      VGVJVHUSQBUGUHRSBUIUJUTVATVBVCUQUPUKRSULAUQVDUMUN $.

    $( The argument of the conjugate of a complex number ` A ` .  (Contributed
       by Thierry Arnoux, 5-Nov-2025.) $)
    argcj $p |- ( ph -> ( Im ` ( log ` ( * ` A ) ) ) = -u ( Im ` ( log ` A ) )
       ) $=
      ( wcel ccj cfv clog cim cneg wceq wa cc0 wne crp wn simpr adantr fveq2d
      rpneg biimpar syl21anc relogcld reim0d negeqd neg0 eqtrdi 3eqtr4d reim0bd
      cr cjred cc ex necon3bd imp logcj syl2an2r logcld imcjd eqtrd pm2.61dan )
      ABUKFZBGHZIHZJHZBIHZJHZKZLAVCMZVHNVFVIVJVGVJBVJVCBNOZBKPFQZBPFZAVCRZAVKVC
      DSAVLVCESVCVKMVMVLBUAUBUCUDUEZVJVEVGJVJVDBIVJBVNULTTVJVINKNVJVHNVOUFUGUHU
      IAVCQZMZVFVGGHZJHVIVQVEVRJABUMFZVPBJHZNOZVEVRLCAVPWAAVCVTNAVTNLZVCAWBMBAV
      SWBCSAWBRUJUNUOUPBUQURTVQVGVQBAVSVPCSAVKVPDSUSUTVAVB $.
  $}

  ${
    quad3d.1 $e |- ( ph -> X e. CC ) $.
    quad3d.2 $e |- ( ph -> A e. CC ) $.
    quad3d.3 $e |- ( ph -> A =/= 0 ) $.
    quad3d.4 $e |- ( ph -> B e. CC ) $.
    quad3d.5 $e |- ( ph -> C e. CC ) $.
    quad3d.6 $e |- ( ph -> ( ( A x. ( X ^ 2 ) ) + ( ( B x. X ) + C ) ) = 0 ) $.
    $( Variant of quadratic equation with discriminant expanded.  (Contributed
       by Filip Cernatescu, 19-Oct-2019.)  Deduction version.  (Revised by
       Thierry Arnoux, 6-Jul-2025.) $)
    quad3d $p |- ( ph -> ( X = ( ( -u B + ( sqrt ` ( ( B ^ 2 )
                              - ( 4 x. ( A x. C ) ) ) ) ) / ( 2 x. A ) )
                        \/ X = ( ( -u B - ( sqrt ` ( ( B ^ 2 )
                              - ( 4 x. ( A x. C ) ) ) ) ) / ( 2 x. A ) ) ) ) $=
      ( c2 cmul co cdiv caddc c4 wceq oveq2d oveq1d cexp cmin csqrt cfv cneg wo
      2cnd mulcld cc0 wne 2ne0 a1i mulne0d divcld addcld sqmuld binom2d divdird
      divcan3d div23d oveq12d mulcomd divcan2d divassd divdiv1d 3eqtr2d addassd
      sqcld eqtr2d eqtrd mvlraddd df-neg eqtr4di 3eqtr3d negcld addcomd cc wcel
      sqdivd 4cn 4ne0 divmuldivd c1 dividd eqcomd mullidd eqtr3d mulm1d mulassd
      neg1cn eqtr4d 3eqtrd 2t2e4 sqvald eqnetrd negsubd subcld eqsqrtor syl2anc
      wb mpbid sqrtcld rdiv addlsub divnegd eqeq2d 3bitrd orbi12d ) ALBMNZECXIO
      NZPNZMNZCLUANZQBDMNZMNZUBNZUCUDZRZXLXQUEZRZUFZECUEZXQPNXIONZRZEYBXQUBNZXI
      ONZRZUFAXLLUANZXPRZYAAYHXILUANZXKLUANZMNYJXPYJONZMNXPAXIXKALBAUGZGUHZAEXJ
      FACXIIYNALBYMGLUIUJAUKULZHUMZUNZUOZUPAYKYLYJMAYKDUEZBONZXJLUANZPNZUUAYTPN
      ZYLAYKELUANZLEXJMNZMNZPNZUUAPNUUBAEXJFYQUQAUUGYTUUAPAUUDCBONZEMNZPNZBUUDM
      NZCEMNZPNZBONZUUGYTAUUNUUKBONZUULBONZPNUUJAUUKUULBABUUDGAEFVHZUHZACEIFUHZ
      GHURAUUOUUDUUPUUIPAUUDBUUQGHUSACEBIFGHUTVAVIAUUIUUFUUDPAUUIEUUHMNZLUUTLON
      ZMNUUFAUUHEACBIGHUNZFVBAUUTLAEUUHFUVBUHYMYOVCAUVAUUELMAUVAEUUHLONZMNUUEAE
      UUHLFUVBYMYOVDAUVCXJEMAUVCCBLMNZONXJACBLIGYMHYOVEAUVDXICOABLGYMVBSVJSVJSV
      FSAUUMYSBOAUUMUUKUULDPNPNZDUBNZYSAUUMDUVEAUUKUULUURUUSUOJAUUKUULDUURUUSJV
      GVKAUVFUIDUBNYSAUVEUIDUBKTDVLVMVJTVNTVJAYTUUAAYSBADJVOZGHUNZAXJYQVHVPAUUC
      XMYJONZXOUEZYJONZPNXMUVJPNZYJONYLAUUAUVIYTUVKPACXIIYNYPVSAQBMNZUVMONZYTMN
      ZUVMYSMNZUVMBMNZONYTUVKAUVMUVMYSBAQBQVQVRAVTULZGUHZUVSUVGGAQBUVRGQUIUJAWA
      ULHUMZHWBAWCYTMNUVOYTAWCUVNYTMAUVNWCAUVMUVSUVTWDWETAYTUVHWFWGAUVPUVJUVQYJ
      OAUVPWCUEZUVMDMNZMNZUWAXOMNUVJAUVPUVMUWAMNZDMNZUWAUVMMNZDMNUWCAUVPUVMUWAD
      MNZMNUWEAYSUWGUVMMAUWGYSADJWHWESAUVMUWADUVSUWAVQVRAWJULZJWIWKAUWDUWFDMAUV
      MUWAUVSUWHVBTAUWAUVMDUWHUVSJWIWLAUWBXOUWAMAQBDUVRGJWISAXOAQXNUVRABDGJUHUH
      ZWHWLAUVQXIXIMNZYJAUVQLXIMNZBMNZXILMNZBMNUWJAUVQLLMNZBMNZBMNUWLAUVMUWOBMA
      QUWNBMAUWNQUWNQRAWMULWETTAUWOUWKBMALLBYMYMGWITVJAUWKUWMBMALXIYMYNVBTAXILB
      YNYMGWIWLAXIYNWNZWKVAVNVAAXMUVJYJACIVHZAXOUWIVOAXIYNVHZAYJUWJUIUWPAXIXIYN
      YNYPYPUMWOZURAUVLXPYJOAXMXOUWQUWIWPTVFWLSAXPYJAXMXOUWQUWIWQZUWRUWSVCWLAXL
      VQVRXPVQVRYIYAWTAXIXKYNYRUHUWTXLXPWRWSXAAXRYDXTYGAXRXKXQXIONZREUXAXJUBNZR
      YDAXIXKXQYNYRAXPUWTXBZYPXCAEXJUXAFYQAXQXIUXCYNYPUNZXDAUXBYCEAUXBYBXIONZUX
      APNZYCAUXAXJUEZPNUXAUXEPNUXBUXFAUXGUXEUXAPACXIIYNYPXEZSAUXAXJUXDYQWPAUXAU
      XEUXDAYBXIACIVOZYNYPUNZVPVNAYBXQXIUXIUXCYNYPURWKXFXGAXTXKXSXIONZREUXKXJUB
      NZRYGAXIXKXSYNYRAXQUXCVOZYPXCAEXJUXKFYQAXSXIUXMYNYPUNZXDAUXLYFEAUXLUXEUXK
      PNZYBXSPNZXIONYFAUXKUXGPNUXKUXEPNUXLUXOAUXGUXEUXKPUXHSAUXKXJUXNYQWPAUXKUX
      EUXNUXJVPVNAYBXSXIUXIUXMYNYPURAUXPYEXIOAYBXQUXIUXCWPTVFXFXGXHXA $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Ordering on reals - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d b c A $.  $d b c B $.  $d b c C $.
    lt2addrd.1 $e |- ( ph -> A e. RR ) $.
    lt2addrd.2 $e |- ( ph -> B e. RR ) $.
    lt2addrd.3 $e |- ( ph -> C e. RR ) $.
    lt2addrd.4 $e |- ( ph -> A < ( B + C ) ) $.
    $( If the right-hand side of a 'less than' relationship is an addition,
       then we can express the left-hand side as an addition, too, where each
       term is respectively less than each term of the original right side.
       (Contributed by Thierry Arnoux, 15-Mar-2017.) $)
    lt2addrd $p |- ( ph -> E. b e. RR E. c e. RR
      ( A = ( b + c ) /\ b < B /\ c < C ) ) $=
      ( caddc co cmin cr wcel wceq clt wbr w3a resubcld cdiv readdcld rehalfcld
      c2 cv wrex recnd addcld subcld halfcld subsub4d oveq2d subadd23d 2halvesd
      cc eqeltrd addsubassd 3eqtr4d nncand 3eqtrrd crp wb difrp mpbid rphalfcld
      syl2anc ltsubrpd oveq1 eqeq2d breq1 3anbi12d 3anbi13d rspc2ev syl113anc
      oveq2 ) ACCDKLZBMLZUDUALZMLZNODVRMLZNOBVSVTKLZPZVSCQRZVTDQRZBEUEZFUEZKLZP
      ZWECQRZWFDQRZSZFNUFENUFACVRHAVQAVPBACDHIUBZGTUCZTADVRIWMTAWAVPVRVRKLZMLZV
      PVQMLBACVTVRMLZKLCDWNMLZKLWAWOAWPWQCKADVRVRADIUGZAVQAVPBACDACHUGZWRUHZABG
      UGZUIZUJZXCUKULACVRVTWSXCADVRWRXCUIUMACDWNWSWRAWNVQUOAVQXBUNZXBUPUQURAWNV
      QVPMXDULAVPBWTXAUSUTACVRHAVQABVPQRZVQVAOZJABNOVPNOXEXFVBGWLBVPVCVFVDVEZVG
      ADVRIXGVGWKWBWCWDSBVSWFKLZPZWCWJSEFVSVTNNWEVSPZWHXIWIWCWJXJWGXHBWEVSWFKVH
      VIWEVSCQVJVKWFVTPZXIWBWJWDWCXKXHWABWFVTVSKVOVIWFVTDQVJVLVMVN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Extended reals - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    nn0mnfxrd.1 $e |- ( ph -> A e. ( NN0 u. { -oo } ) ) $.
    $( Nonnegative integers or minus infinity are extended real numbers.
       (Contributed by Thierry Arnoux, 15-Feb-2026.) $)
    nn0mnfxrd $p |- ( ph -> A e. RR* ) $=
      ( cn0 wcel cxr cmnf wceq nn0re rexrd adantl mnfxr eleq1 mpbiri csn cun wo
      elunsn ibi syl mpjaodan ) ABDEZBFEZBGHZUBUCAUBBBIJKUDUCAUDUCGFELBGFMNKABD
      GOPZEZUBUDQZCUFUGBDGUERSTUA $.
  $}

  $( Trichotomy law for extended reals.  (Contributed by Thierry Arnoux,
     12-Sep-2017.) $)
  xrlelttric $p |- ( ( A e. RR* /\ B e. RR* ) -> ( A <_ B \/ B < A ) ) $=
    ( cxr wcel wa cle wbr clt wo wn pm2.1 xrlenlt orbi1d mpbiri ) ACDBCDEZABFGZ
    BAHGZIQJZQIQKOPRQABLMN $.

  $( Two extended reals which add up to zero are each other's negatives.
     (Contributed by Thierry Arnoux, 13-Jun-2017.) $)
  xaddeq0 $p |-
    ( ( A e. RR* /\ B e. RR* ) -> ( ( A +e B ) = 0 <-> A = -e B ) ) $=
    ( cxr wcel wa cxad cc0 wceq cxne cpnf cmnf syl simplr syl2anc oveq1d eqtr3d
    co simpr ex wne cr w3o wi elxr simpll rexrd xnegneg xnegcld xaddlid xaddcom
    xpncan ancoms adantr 3eqtr3d xnegeq wn renepnf mp1i eqnetrd neneqd xaddpnf2
    0re stoic1a nne sylib xnegmnf eqtr2di eqtrd renemnf xaddmnf2 xnegpnf sylanb
    3jaoian xnegcl ad2antlr xnegid 3eqtrd impbid ) ACDZBCDZEZABFQZGHZABIZHZVSAU
    ADZAJHZAKHZUBVTWCWEUCZAUDWFVTWIWGWHWFVTEZWCWEWJWCEZAIZIZAWDWKVSWMAHWKAWFVTW
    CUEUFZAUGLWKWLBHWMWDHWKGWLFQZWLBWKWLCDWOWLHWKAWNUHWLUILWKWBWLFQBAFQZWLFQZWO
    BWKWBWPWLFWKVSVTWBWPHWNWFVTWCMABUJNOWKWBGWLFWJWCROWJWQBHZWCVTWFWRBAUKULUMUN
    PWLBUOLPSWGVTEZWCWEWSWCEZAJWDWGVTWCUEZWTWDKIZJWTBKHZWDXBHWTBKTZUPZXCWTVTJBF
    QZJHZUPXEWGVTWCMWTXFJWTXFGJWTWBXFGWTAJBFXAOWSWCRPGUADZGJTWTVBGUQURUSUTVTXDX
    GBVAVCNBKVDVEBKUOLVFVGVHSWHVTEZWCWEXIWCEZAKWDWHVTWCUEZXJWDJIZKXJBJHZWDXLHXJ
    BJTZUPZXMXJVTKBFQZKHZUPXOWHVTWCMXJXPKXJXPGKXJWBXPGXJAKBFXKOXIWCRPXHGKTXJVBG
    VIURUSUTVTXNXQBVJVCNBJVDVEBJUOLVKVGVHSVMVLWAWEWCWAWEEZWBWDBFQZBWDFQZGXRAWDB
    FWAWEROXRWDCDZVTXSXTHVTYAVSWEBVNVOVSVTWEMWDBUJNVTXTGHVSWEBVPVOVQSVR $.

  ${
    rexmul2.a $e |- ( ph -> A e. RR ) $.
    rexmul2.b $e |- ( ph -> B e. RR* ) $.
    rexmul2.c $e |- ( ph -> C e. RR* ) $.
    rexmul2.1 $e |- ( ph -> 0 < C ) $.
    rexmul2.2 $e |- ( ph -> A = ( B *e C ) ) $.
    $( If the result ` A ` of an extended real multiplication is real, then its
       first factor ` B ` is also real.  See also ~ rexmul .  (Contributed by
       Thierry Arnoux, 26-Oct-2025.) $)
    rexmul2 $p |- ( ph -> B e. RR ) $=
      ( wcel cpnf wceq cmnf wa cxmu co adantr simpr oveq1d cxr cc0 clt xmulpnf2
      cr wbr syl2anc 3eqtrd wne renepnfd neneqd pm2.65da xmulmnf2 renemnfd elxr
      w3o sylib ecase23d ) ACUDJZCKLZCMLZAUSBKLAUSNZBCDOPZKDOPZKABVBLZUSIQVACKD
      OAUSRSAVCKLZUSADTJZUADUBUEZVEGHDUCUFQUGVABKABKUHUSABEUIQUJUKAUTBMLAUTNZBV
      BMDOPZMAVDUTIQVHCMDOAUTRSAVIMLZUTAVFVGVJGHDULUFQUGVHBMABMUHUTABEUMQUJUKAC
      TJURUSUTUOFCUNUPUQ $.
  $}

  $( The extended real numbers are unbounded below.  (Contributed by Thierry
     Arnoux, 18-Feb-2018.)  (Revised by AV, 28-Sep-2020.) $)
  xrinfm $p |- inf ( RR* , RR* , < ) = -oo $=
    ( cxr wss cmnf wcel clt cinf wceq ssid mnfxr infxrmnf mp2an ) AABCADAAEFCGA
    HIAJK $.

  ${
    le2halvesd.1 $e |- ( ph -> A e. RR ) $.
    le2halvesd.2 $e |- ( ph -> B e. RR ) $.
    le2halvesd.3 $e |- ( ph -> C e. RR ) $.
    le2halvesd.4 $e |- ( ph -> A <_ ( C / 2 ) ) $.
    le2halvesd.5 $e |- ( ph -> B <_ ( C / 2 ) ) $.
    $( A sum is less than the whole if each term is less than half.
       (Contributed by Thierry Arnoux, 29-Nov-2017.) $)
    le2halvesd $p |- ( ph -> ( A + B ) <_ C ) $=
      ( caddc co c2 cdiv cle rehalfcld le2addd recnd 2halvesd breqtrd ) ABCJKDL
      MKZTJKDNABCTTEFADGOZUAHIPADADGQRS $.
  $}

  $( A number is less than or equal to itself plus a nonnegative number.
     (Contributed by Thierry Arnoux, 28-Dec-2016.) $)
  xraddge02 $p |- ( ( A e. RR* /\ B e. RR* ) ->
    ( 0 <_ B -> A <_ ( A +e B ) ) ) $=
    ( cxr wcel wa cc0 cle wbr cxad co xrleid adantr simpl jctir xle2add mpancom
    wi 0xr mpand wb xaddrid breq1d sylibd ) ACDZBCDZEZFBGHZAFIJZABIJZGHZAUIGHZU
    FAAGHZUGUJUDULUEAKLUDFCDZEUFULUGEUJQUFUDUMUDUEMRNAFABOPSUDUJUKTUEUDUHAUIGAU
    AUBLUC $.

  $( A number is less than or equal to itself plus a nonnegative number.
     (Contributed by Thierry Arnoux, 19-Jul-2020.) $)
  xrge0addge $p |- ( ( A e. RR* /\ B e. ( 0 [,] +oo ) ) -> A <_ ( A +e B ) ) $=
    ( cc0 cpnf cicc co wcel cxr cle wbr wa cxad elxrge0 biimpi xraddge02 sylan2
    impr ) BCDEFGZAHGZBHGZCBIJZKZAABLFIJZRUBBMNSTUAUCABOQP $.

  ${
    $d b c A $.  $d b c B $.  $d b c C $.
    xlt2addrd.1 $e |- ( ph -> A e. RR ) $.
    xlt2addrd.2 $e |- ( ph -> B e. RR* ) $.
    xlt2addrd.3 $e |- ( ph -> C e. RR* ) $.
    xlt2addrd.4 $e |- ( ph -> B =/= -oo ) $.
    xlt2addrd.5 $e |- ( ph -> C =/= -oo ) $.
    xlt2addrd.6 $e |- ( ph -> A < ( B +e C ) ) $.
    $( If the right-hand side of a 'less than' relationship is an addition,
       then we can express the left-hand side as an addition, too, where each
       term is respectively less than each term of the original right side.
       (Contributed by Thierry Arnoux, 15-Mar-2017.) $)
    xlt2addrd $p |- ( ph -> E. b e. RR* E. c e. RR*
      ( A = ( b +e c ) /\ b < B /\ c < C ) ) $=
      ( cxad co wceq clt cxr wcel ad2antrr cr cv wbr w3a wrex cpnf wa cc0 rexrd
      0xr a1i xaddrid eqcomd ltpnf simplr breqtrrd 0ltpnf simpr breqtrrid oveq1
      syl eqeq2d breq1 3anbi12d oveq2 3anbi13d rspc2ev syl113anc wne c1 xnegcld
      cxne xaddcld cmnf renemnfd cneg cmin wo wn xrnepnf biimpi sylancom orcomd
      1xr neneqd pm2.53 sylc 1re rexsub sylancl resubcl eqeltrd rexneg renegcld
      xaddass syl222anc xaddcom syl2anc xnegid 3eqtrrd resubcld 3brtr4d eqbrtrd
      eqtrd oveq2d ltm1d pm2.61dane caddc breqtrd lt2addrd 3anbi1d 2rexbiia wss
      rexadd sylibr wi ressxr ssrexv ax-mp reximi 3syl ) ABEUAZFUAZMNZOZYACPUBZ
      YBDPUBZUCZFQUDZEQUDZCUEACUEOZUFZYIDUEYKDUEOZUFZBQRZUGQRZBBUGMNZOZBCPUBZUG
      DPUBZYIAYNYJYLABGUHZSZYOYMUIUJYMYNYQUUAYNYPBBUKZULUTYMBUECPYMBTRZBUEPUBAU
      UCYJYLGSBUMUTAYJYLUNUOYMUGUEDPUPYKYLUQURYGYQYRYSUCBBYBMNZOZYRYFUCEFBUGQQY
      ABOZYDUUEYEYRYFUUFYCUUDBYABYBMUSVAYABCPVBVCYBUGOZUUEYQYFYSYRUUGUUDYPBYBUG
      BMVDVAYBUGDPVBVEVFVGYKDUEVHZUFZBDVIVKZMNZVKZMNZQRUUKQRZBUUMUUKMNZOZUUMCPU
      BZUUKDPUBZYIUUIBUULAYNYJUUHYTSZUUIUUKUUIDUUJADQRZYJUUHISZUUIVIVIQRZUUIWCU
      JVJVLZVJZVLUVCUUIUUOBUULUUKMNZMNZYPBUUIYNBVMVHZUULQRZUULVMVHUUNUUKVMVHUUO
      UVFOUUSUUIBAUUCYJUUHGSZVNUVDUUIUULUUIUULUUKVOZTUUIUUKTRZUULUVJOUUIUUKDVIV
      PNZTUUIDTRZVITRZUUKUVLOUUIDVMOZUVMVQZUVOVRZUVMUUIUVMUVOYKUUHUUTUVMUVOVQZU
      VAUUTUUHUFUVRDVSVTZWAWBUUIDVMADVMVHZYJUUHKSWDUVOUVMWEZWFZWGDVIWHWIZUUIUVM
      UVNUVLTRUWBWGDVIWJWIZWKZUUKWLUTUUIUUKUWEWMWKVNUVCUUIUUKUWEVNBUULUUKWNWOUU
      IUVEUGBMUUIUVEUUKUULMNZUGUUIUVHUUNUVEUWFOUVDUVCUULUUKWPWQUUIUUNUWFUGOUVCU
      UKWRUTXCXDUUIYNYPBOZUUSUUBUTWSUUIBUVLVPNZUEUUMCPUUIUWHTRUWHUEPUBUUIBUVLUV
      IUWDWTUWHUMUTUUIUUMBUUKVPNZUWHUUIUUCUVKUUMUWIOUVIUWEBUUKWHWQUUIUUKUVLBVPU
      WCXDXCAYJUUHUNXAUUIUUKUVLDPUWCUUIDUWBXEXBYGUUPUUQUURUCBUUMYBMNZOZUUQYFUCE
      FUUMUUKQQYAUUMOZYDUWKYEUUQYFUWLYCUWJBYAUUMYBMUSVAYAUUMCPVBVCYBUUKOZUWKUUP
      YFUURUUQUWMUWJUUOBYBUUKUUMMVDVAYBUUKDPVBVEVFVGXFACUEVHZUFZYIDUEUWOYLUFZCU
      UJMNZQRZBUWQVKZMNZQRZBUWQUWTMNZOZUWQCPUBZUWTDPUBZYIUWPCUUJACQRZUWNYLHSZUW
      PVIUVBUWPWCUJVJVLZUWPBUWSAYNUWNYLYTSZUWPUWQUXHVJZVLZUWPUXBUWTUWQMNZBUWSUW
      QMNZMNZBUWPUWRUXAUXBUXLOUXHUXKUWQUWTWPWQUWPYNUVGUWSQRZUWSVMVHUWRUWQVMVHUX
      LUXNOUXIUWPBAUUCUWNYLGSZVNUXJUWPUWSUWPUWSUWQVOZTUWPUWQTRZUWSUXQOUWPUWQCVI
      VPNZTUWPCTRZUVNUWQUXSOUWPCVMOZUXTVQZUYAVRZUXTUWPUXTUYAUWPUXFUWNUXTUYAVQZU
      XGAUWNYLUNUXFUWNUFUYDCVSVTZWQWBUWPCVMACVMVHZUWNYLJSWDUYAUXTWEZWFZWGCVIWHW
      IZUWPUXTUVNUXSTRUYHWGCVIWJWIZWKZUWQWLUTUWPUWQUYKWMWKVNUXHUWPUWQUYKVNBUWSU
      WQWNWOUWPUXNYPBUWPUXMUGBMUWPUXMUWQUWSMNZUGUWPUXOUWRUXMUYLOUXJUXHUWSUWQWPW
      QUWPUWRUYLUGOUXHUWQWRUTXCXDUWPYNUWGUXIUUBUTXCWSUWPUWQUXSCPUYIUWPCUYHXEXBU
      WPBUXSVPNZUEUWTDPUWPUYMTRUYMUEPUBUWPBUXSUXPUYJWTUYMUMUTUWPUWTBUWQVPNZUYMU
      WPUUCUXRUWTUYNOUXPUYKBUWQWHWQUWPUWQUXSBVPUYIXDXCUWOYLUQXAYGUXCUXDUXEUCBUW
      QYBMNZOZUXDYFUCEFUWQUWTQQYAUWQOZYDUYPYEUXDYFUYQYCUYOBYAUWQYBMUSVAYAUWQCPV
      BVCYBUWTOZUYPUXCYFUXEUXDUYRUYOUXBBYBUWTUWQMVDVAYBUWTDPVBVEVFVGUWOUUHUFZYG
      FTUDZETUDZYHETUDZYIUYSBYAYBXGNZOZYEYFUCZFTUDETUDVUAUYSBCDEFAUUCUWNUUHGSUY
      SUYBUYCUXTUYSUXTUYAUYSUXFUWNUYDAUXFUWNUUHHSAUWNUUHUNUYEWQWBUYSCVMAUYFUWNU
      UHJSWDUYGWFZUYSUVPUVQUVMUYSUVMUVOUWOUUHUUTUVRAUUTUWNUUHISUVSWAWBUYSDVMAUV
      TUWNUUHKSWDUWAWFZUYSBCDMNZCDXGNZPABVUHPUBUWNUUHLSUYSUXTUVMVUHVUIOVUFVUGCD
      XMWQXHXIYGVUEEFTTYATRYBTRUFZYDVUDYEYFVUJYCVUCBYAYBXMVAXJXKXNUYTYHETTQXLZU
      YTYHXOXPYGFTQXQXRXSVUKVUBYIXOXPYHETQXQXRXTXFXF $.
  $}

  ${
    $d w x y z A $.
    $( Any subset of nonnegative extended reals has an infimum.  (Contributed
       by Thierry Arnoux, 16-Sep-2019.)  (Revised by AV, 4-Oct-2020.) $)
    xrge0infss $p |- ( A C_ ( 0 [,] +oo ) -> E. x e. ( 0 [,] +oo )
      ( A. y e. A -. y < x /\
        A. y e. ( 0 [,] +oo ) ( x < y -> E. z e. A z < y ) ) ) $=
      ( vw cc0 cpnf wss cv clt wbr wn wral wrex wi cxr wa wcel 0xr ralbidv cicc
      co ssel2 pnfxr iccgelb mp3an12 wb eliccxr xrlenlt sylancr mpbid ralrimiva
      cle syl ad3antrrr iccssxr ssralv ax-mp simplll a1i simplr simpr xrlelttrd
      sselid simpllr ex imim1d ralimdva syl5 adantll imp adantrl 0e0iccpnf wceq
      an32s breq2 notbid breq1 imbi1d anbi12d rspcev mpan syl2anc anim2d adantr
      elxrge0 sylanbrc weq wo xrletri mpjaodan sstr mpan2 xrinfmss r19.29a ) DF
      GUAUBZHZBIZEIZJKZLZBDMZWSWRJKZCIWRJKCDNZOZBPMZQZWRAIZJKZLZBDMZXHWRJKZXDOZ
      BWPMZQZAWPNZEPWQWSPRZQZXGQZWSFUMKZXPFWSUMKZXSXTQWRFJKZLZBDMZFWRJKZXDOZBWP
      MZXPWQYDXQXGXTWQYCBDWQWRDRQWRWPRZYCDWPWRUCYHFWRUMKZYCFPRZGPRYHYISUDFGWRUE
      UFYHYJWRPRYIYCUGSWRFGUHFWRUIUJUKUNULUOXRXTXGYGXRXTQZXFYGXBYKXFYGXQXTXFYGO
      WQXFXEBWPMZXQXTQZYGWPPHZXFYLOZFGUPZXEBWPPUQURZYMXEYFBWPYMYHQZYEXCXDYRYEXC
      YRYEQZWSFWRXQXTYHYEUSYJYSSUTYSWPPWRYPYMYHYEVAVDXQXTYHYEVEYRYEVBVCVFVGVHVI
      VJVKVLVOFWPRYDYGQZXPVMXOYTAFWPXHFVNZXKYDXNYGUUAXJYCBDUUAXIYBXHFWRJVPVQTUU
      AXMYFBWPUUAXLYEXDXHFWRJVRVSTVTWAWBWCXSYAQZWSWPRZXBYLQZXPUUBXQYAUUCWQXQXGY
      AVEXSYAVBWSWFWGXSUUDYAXRXGUUDWQXGUUDOXQWQXFYLXBYOWQYQUTWDWEVKWEXOUUDAWSWP
      AEWHZXKXBXNYLUUEXJXABDUUEXIWTXHWSWRJVPVQTUUEXMXEBWPUUEXLXCXDXHWSWRJVRVSTV
      TWAWCXSXQYJXTYAWIWQXQXGVAYJXSSUTWSFWJWCWKWQDPHZXGEPNWQYNUUFYPDWPPWLWMEBCD
      WNUNWO $.
  $}

  ${
    $d x y z B $.  $d x y z C $.  $d z ph $.
    xrge0infssd.1 $e |- ( ph -> C C_ B ) $.
    xrge0infssd.2 $e |- ( ph -> B C_ ( 0 [,] +oo ) ) $.
    $( Inequality deduction for infimum of a nonnegative extended real subset.
       (Contributed by Thierry Arnoux, 16-Sep-2019.)  (Revised by AV,
       4-Oct-2020.) $)
    xrge0infssd $p |- ( ph -> inf ( B , ( 0 [,] +oo ) , < )
                              <_ inf ( C , ( 0 [,] +oo ) , < ) ) $=
      ( vx vy vz cc0 cpnf clt cinf cxr wor wss cv wbr wral wrex wi cicc iccssxr
      co xrltso mp2 a1i wn wa xrge0infss syl infcl sselid sstrd infssd xrnltled
      soss ) ABIJUAUCZKLZCUQKLZAUQMURIJUBZAFGHUQBKUQKNZAUQMOMKNVAUTUDUQMKUPUEUF
      ZABUQOGPZFPZKQUGZGBRVDVCKQZHPVCKQZHBSTGUQRUHFUQSEFGHBUIUJZUKULAUQMUSUTAFG
      HUQCKVBACUQOVEGCRVFVGHCSTGUQRUHFUQSACBUQDEUMFGHCUIUJZUKULAFGHUQBCKVBDVIVH
      UNUO $.
  $}

  ${
    xrge0addcld.a $e |- ( ph -> A e. ( 0 [,] +oo ) ) $.
    xrge0addcld.b $e |- ( ph -> B e. ( 0 [,] +oo ) ) $.
    $( Nonnegative extended reals are closed under addition.  (Contributed by
       Thierry Arnoux, 16-Sep-2019.) $)
    xrge0addcld $p |- ( ph -> ( A +e B ) e. ( 0 [,] +oo ) ) $=
      ( cxad co cxr wcel cc0 cle wbr cpnf cicc wa elxrge0 simpld xaddcld simprd
      sylib xaddge0 syl22anc sylanbrc ) ABCFGZHIJUDKLZUDJMNGZIABCABHIZJBKLZABUF
      IUGUHODBPTZQZACHIZJCKLZACUFIUKULOECPTZQZRAUGUKUHULUEUJUNAUGUHUISAUKULUMSB
      CUAUBUDPUC $.
  $}

  ${
    xrge0subcld.a $e |- ( ph -> A e. ( 0 [,] +oo ) ) $.
    xrge0subcld.b $e |- ( ph -> B e. ( 0 [,] +oo ) ) $.
    xrge0subcld.c $e |- ( ph -> B <_ A ) $.
    $( Condition for closure of nonnegative extended reals under subtraction.
       (Contributed by Thierry Arnoux, 27-May-2020.) $)
    xrge0subcld $p |- ( ph -> ( A +e -e B ) e. ( 0 [,] +oo ) ) $=
      ( cxne cxad co cxr wcel cc0 cle wbr wa cpnf cicc iccssxr sselid xnegcld
      xaddcld wb xsubge0 syl2anc mpbird jca elxrge0 sylibr ) ABCGZHIZJKZLUJMNZO
      UJLPQIZKAUKULABUIAUMJBLPRZDSZACAUMJCUNESZTUAAULCBMNZFABJKCJKULUQUBUOUPBCU
      CUDUEUFUJUGUH $.
  $}

$(
  @{
    supxrge0ub.a @e |- ( ph -> A C_ ( 0 [,] +oo ) ) @.
    supxrge0ub.b @e |- ( ph -> B e. A ) @.
    @( A member of a set of nonnegative extended reals is less than or equal to
       the set's supremum.  (Contributed by Thierry Arnoux, 29-Jul-2020.) @)
    supxrge0ub @p |- ( ph -> B <_ sup ( A , ( 0 [,] +oo ) , < ) ) @=
      ? @.
  @}

  @{
    supxrge0lub.a @e |- ( ph -> A C_ ( 0 [,] +oo ) ) @.
    supxrge0lub.b @e |- ( ph -> B e. ( 0 [,] +oo ) ) @.
    @( The supremum of a set of nonnegative extended reals is less than or
       equal to an upper bound.  (Contributed by Thierry Arnoux,
       29-Jul-2020.) @)
    supxrge0lub @p |- ( ph ->
                 ( B < sup ( A , ( 0 [,] +oo ) , < ) <-> E. x e. A B < x ) ) @=
      ? @.

    @( The supremum of a set of nonnegative extended reals is less than or
       equal to an upper bound.  (Contributed by Thierry Arnoux,
       29-Jul-2020.) @)
    supxrge0leub @p |- ( ph ->
               ( sup ( A , ( 0 [,] +oo ) , < ) <_ B <-> A. x e. A x <_ B ) ) @=
      ? @.
  @}
$)

  ${
    $d A x y z $.
    infxrge0lb.a $e |- ( ph -> A C_ ( 0 [,] +oo ) ) $.
    infxrge0lb.b $e |- ( ph -> B e. A ) $.
    $( A member of a set of nonnegative extended reals is greater than or equal
       to the set's infimum.  (Contributed by Thierry Arnoux, 19-Jul-2020.)
       (Revised by AV, 4-Oct-2020.) $)
    infxrge0lb $p |- ( ph -> inf ( A , ( 0 [,] +oo ) , < ) <_ B ) $=
      ( vx vy vz cc0 cpnf clt cxr wor wss cv wbr wn wral wrex sselid co iccssxr
      cicc cinf xrltso soss mp2 a1i wi wa xrge0infss syl infcl sseldd inflb mpd
      wcel xrnltled ) ABIJUCUAZKUDZCAUSLUTIJUBZAFGHUSBKUSKMZAUSLNLKMVBVAUEUSLKU
      FUGUHZABUSNGOZFOZKPQGBRVEVDKPHOVDKPHBSUIGUSRUJFUSSDFGHBUKULZUMTAUSLCVAABU
      SCDEUNTACBUQCUTKPQEAFGHUSBCKVCVFUOUPUR $.
  $}

  ${
    $d A x y z $.  $d B x z $.  $d ph z $.
    infxrge0glb.a $e |- ( ph -> A C_ ( 0 [,] +oo ) ) $.
    infxrge0glb.b $e |- ( ph -> B e. ( 0 [,] +oo ) ) $.
    $( The infimum of a set of nonnegative extended reals is the greatest lower
       bound.  (Contributed by Thierry Arnoux, 19-Jul-2020.)  (Revised by AV,
       4-Oct-2020.) $)
    infxrge0glb $p |- ( ph ->
                 ( inf ( A , ( 0 [,] +oo ) , < ) < B <-> E. x e. A x < B ) ) $=
      ( vz vy cc0 cpnf cicc co clt wbr cv wrex wor cxr wss wral cinf wb iccssxr
      wcel xrltso soss mp2 a1i wn wi wa xrge0infss infglbb mpdan breq1 cbvrexvw
      syl bitr4di ) ACIJKLZMUADMNZGOZDMNZGCPZBOZDMNZBCPADUSUDUTVCUBFABHGUSCDMUS
      MQZAUSRSRMQVFIJUCUEUSRMUFUGUHACUSSHOZVDMNUIHCTVDVGMNVAVGMNGCPUJHUSTUKBUSP
      EBHGCULUQEUMUNVEVBBGCVDVADMUOUPUR $.

    $d ph x $.
    $( The infimum of a set of nonnegative extended reals is greater than or
       equal to a lower bound.  (Contributed by Thierry Arnoux, 19-Jul-2020.)
       (Revised by AV, 4-Oct-2020.) $)
    infxrge0gelb $p |- ( ph ->
               ( B <_ inf ( A , ( 0 [,] +oo ) , < ) <-> A. x e. A B <_ x ) ) $=
      ( vy vz cc0 cpnf clt wbr wn cv wrex cle wral cxr sselid wor cicc cinf wss
      co infxrge0glb notbid iccssxr xrltso soss mp2 a1i wi xrge0infss syl infcl
      wa xrlenltd wcel adantr sstrdi sselda ralbidva ralnex bitrdi 3bitr4d ) AC
      IJUAUDZKUBZDKLZMBNZDKLZBCOZMZDVGPLDVIPLZBCQZAVHVKABCDEFUEUFADVGAVFRDIJUGZ
      FSZAVFRVGVOABGHVFCKVFKTZAVFRUCRKTVQVOUHVFRKUIUJUKACVFUCGNZVIKLMGCQVIVRKLH
      NVRKLHCOULGVFQUPBVFOEBGHCUMUNUOSUQAVNVJMZBCQVLAVMVSBCAVICURZUPDVIADRURVTV
      PUSACRVIACVFREVOUTVAUQVBVJBCVCVDVE $.
  $}

  ${
    $d a b k u v w x y z X $.  $d a b k u v w x y z Y $.  $d k v w z Z $.
    $d k v w x y z ph $.
    xrofsup.1 $e |- ( ph -> X C_ RR* ) $.
    xrofsup.2 $e |- ( ph -> Y C_ RR* ) $.
    xrofsup.3 $e |- ( ph -> sup ( X , RR* , < ) =/= -oo ) $.
    xrofsup.4 $e |- ( ph -> sup ( Y , RR* , < ) =/= -oo ) $.
    xrofsup.5 $e |- ( ph -> Z = ( +e " ( X X. Y ) ) ) $.
    $( The supremum is preserved by extended addition set operation.  (Provided
       minus infinity is not involved as it does not behave well with
       addition.)  (Contributed by Thierry Arnoux, 20-Mar-2017.) $)
    xrofsup $p |- ( ph -> sup ( Z , RR* , < ) =
      ( sup ( X , RR* , < ) +e sup ( Y , RR* , < ) ) ) $=
      ( vx vy va vb cxr clt cxad wcel wbr wrex wa vz vk vu vv vw wss csup co cv
      cle wral wi wceq cxp cima cfv sseld anim12d imp xaddcl syl ralrimivva cop
      cr fveq2 df-ov eqtr4di eleq1d ralxp sylibr wfun cdm wb xaddf ax-mp xpss12
      wf ffun syl2anc sseqtrrdi funimass4 sylancr mpbird eqsstrd supxrcl eleq2d
      fdmi xaddcld pm5.32i nfvd ad2antrr simprl supxrub simprr xle2add syl22anc
      sseldd mp2and fvelima mpan adantl eqeq1d rexxp sylib ancom 2rexbii biimpa
      r19.29d2r breq1 reximi 19.9d2r sylbi ralrimiva w3a simplr simpr xlt2addrd
      cmnf wne nfv nfcv nfrexw nfan id ralrimivw adantr simplrr 3anassrs simp1d
      nfre1 simp-4l simplrl simpld simpllr simprd xlt2add supxrlub syl21anc ex
      jca32 biimpar sylan2 syl12anc simplll simplr2 sylanbrc reximddv2 reximdva
      simplr3 reeanv ancoms reximia 19.9d2rf elovimad breq2d rspcedv rexlimdvva
      a1i mpd supxr2 ) ADNUFBNOUGZCNOUGZPUHZNQUAUIZUVCUJRZUADUKUVDUVCORZUVDUBUI
      ZORZUBDSZULZUAVDUKDNOUGUVCUMADPBCUNZUOZNIAUVLNUFZUCUIZPUPZNQZUCUVKUKZAJUI
      ZKUIZPUHZNQZKCUKJBUKUVQAUWAJKBCAUVRBQZUVSCQZTZTUVRNQZUVSNQZTZUWAAUWDUWGAU
      WBUWEUWCUWFABNUVREUQACNUVSFUQURUSUVRUVSUTVAVBUVPUWAUCJKBCUVNUVRUVSVCZUMZU
      VOUVTNUWIUVOUWHPUPUVTUVNUWHPVEUVRUVSPVFVGZVHVIVJAPVKZUVKPVLZUFZUVMUVQVMNN
      UNZNPVQUWKVNUWNNPVRVOZAUVKUWNUWLABNUFZCNUFZUVKUWNUFEFBNCNVPVSUWNNPVNWGVTZ
      UCUVKNPWAWBWCWDAUVAUVBAUWPUVANQZEBWEZVAZAUWQUVBNQZFCWEZVAZWHAUVEUADAUVDDQ
      ZTAUVDUVLQZTZUVEAUXEUXFADUVLUVDIWFWIUXGUVEJKBCUXGUVEJWJUXGUVEKWJUXGUVTUVD
      UMZUVTUVCUJRZTZKCSZJBSZUVEKCSZJBSUXGUXIUXHTZKCSJBSUXLUXGUXIUXHJKBCUXGUXIJ
      KBCUXGUWDTZUVRUVAUJRZUVSUVBUJRZUXIUXOUWPUWBUXPAUWPUXFUWDEWKZUXGUWBUWCWLZB
      UVRWMVSUXOUWQUWCUXQAUWQUXFUWDFWKZUXGUWBUWCWNZCUVSWMVSUXOUWEUWFUWSUXBUXPUX
      QTUXIULUXOBNUVRUXRUXSWQUXOCNUVSUXTUYAWQUXOUWPUWSUXRUWTVAUXOUWQUXBUXTUXCVA
      UVRUVSUVAUVBWOWPWRVBUXGUVOUVDUMZUCUVKSZUXHKCSJBSUXFUYCAUWKUXFUYCUWOUCUVDU
      VKPWSWTXAUYBUXHUCJKBCUWIUVOUVTUVDUWJXBXCXDXHUXNUXJJKBCUXIUXHXEXFXDUXKUXMJ
      BUXJUVEKCUXHUXIUVEUVTUVDUVCUJXIXGXJXJVAXKXLXMAUVJUAVDAUVDVDQZTZUVFUVIUYEU
      VFTZUVDUDUIZUEUIZPUHZORZUECSUDBSZUVIUYFUWPUWQUVDLUIZMUIZPUHZUMZUYLUVAORZU
      YMUVBORZXNZMNSZLNSZUYKAUWPUYDUVFEWKAUWQUYDUVFFWKUYFUVDUVAUVBLMAUYDUVFXOAU
      WSUYDUVFUXAWKAUXBUYDUVFUXDWKAUVAXRXSUYDUVFGWKAUVBXRXSUYDUVFHWKUYEUVFXPXQU
      WPUWQTZUYTTZUYKLMNNVUAUYTMVUAMXTUYSMLNMNYAUYRMNYJYBYCVUBUYKLWJVUBUYKMWJVU
      BVUAUYRTZMNSZLNSUYKMNSZLNSVUBVUAUYRLMNNVUAVUAMNUKZLNUKUYTVUAVUFLNVUAVUAMN
      VUAYDYEYEYFVUAUYTXPXHVUDVUELNUYLNQZVUCUYKMNVUGUYMNQZTZVUCUYKVUIVUCTZUYLUY
      GORZUYMUYHORZTZUYJUDUEBCVUJUYGBQZTZUYHCQZTZVUMTZUYOVUIUYGNQZUYHNQZTTZVUMU
      YJVURUYOUYPUYQVUJVUNVUPVUMUYRVUIVUAUYRVUNVUPVUMXNZYGYHYIVURVUIVUSVUTVUIVU
      CVUNVUPVUMYKVURBNUYGVURUWPUWQVUJVUNVUPVUMVUAVUIVUAUYRVVBYLYHZYMVUJVUNVUPV
      UMYNWQVURCNUYHVURUWPUWQVVCYOVUOVUPVUMXOWQYTVUQVUMXPVVAVUMTUYOUYNUYIORZUYJ
      VVAVUMVVDUYLUYMUYGUYHYPUSUYOUYJVVDUVDUYNUYIOXIUUAUUBUUCVUCVUIVUMUECSUDBSZ
      VUCVUITZVUKUDBSZVULUECSZVVEVVFUWPVUGUYPVVGUWPUWQUYRVUIUUDVUCVUGVUHWLUYOUY
      PUYQVUAVUIUUEUWPVUGTUYPVVGUDBUYLYQXGYRVVFUWQVUHUYQVVHUWPUWQUYRVUIYNVUCVUG
      VUHWNUYOUYPUYQVUAVUIUUIUWQVUHTUYQVVHUECUYMYQXGYRVUKVULUDUEBCUUJUUFUUKUUGY
      SUUHUULVAUUMYRAUYKUVIULUYDUVFAUYJUVIUDUEBCAVUNVUPTZTZUVHUYJUBUYIDVVJUYIDQ
      ZUYIUVLQZVVJUYGUYHBCPAVUNVUPWLAVUNVUPWNUWKVVJUWOUURAUWMVVIUWRYFUUNAVVKVVL
      VMVVIADUVLUYIIWFYFWCVVJUVGUYIUMZTUVGUYIUVDOVVJVVMXPUUOUUPUUQWKUUSYSXMUAUB
      DUVCUUTWP $.
  $}

  ${
    $d x A $.
    $( The supremum of a nonempty set of extended reals which does not contain
       minus infinity is not minus infinity.  (Contributed by Thierry Arnoux,
       21-Mar-2017.) $)
    supxrnemnf $p |- ( ( A C_ RR* /\ A =/= (/) /\ -. -oo e. A ) ->
                     sup ( A , RR* , < ) =/= -oo ) $=
      ( vx cxr wss c0 wne cmnf wcel w3a clt csup wbr mnfxr a1i supxrcl 3ad2ant1
      wn wa biimprd sylc wrex simp1 jctir wceq simpl sselda simpr simplr nelneq
      cv syl2anc ngtmnft con1d reximdva0 3impa 3com23 supxrlub xrltne syl3anc )
      ACDZAEFZGAHQZIZGCHZACJKZCHZGVEJLZVEGFVDVCMNUTVAVFVBAOPVCUTVDRZGBUJZJLZBAU
      AZVGVCUTVDUTVAVBUBMUCUTVBVAVKUTVBVAVKUTVBRZVJBAVLVIAHZRZVICHZVIGUDZQZVJVL
      ACVIUTVBUEUFVNVMVBVQVLVMUGUTVBVMUHVIGAUIUKVOVJVPVOVPVJQVIULSUMTUNUOUPVHVG
      VKBAGUQSTGVEURUS $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Extended nonnegative integers - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Nonzero extended nonnegative integers are strictly greater than zero.
     (Contributed by Thierry Arnoux, 30-Jul-2023.) $)
  xnn0gt0 $p |- ( ( N e. NN0* /\ N =/= 0 ) -> 0 < N ) $=
    ( cxnn0 wcel cn0 cpnf wceq wo cc0 wne clt elxnn0 wa cn elnnne0 nngt0 sylbir
    wbr ancoms adantll 0ltpnf breq2 mpbiri adantl simpl mpjaodan sylanb ) ABCAD
    CZAEFZGZAHIZHAJQZAKUIUJLZUGUKUHUJUGUKUIUGUJUKUGUJLAMCUKANAOPRSUHUKULUHUKHEJ
    QTAEHJUAUBUCUIUJUDUEUF $.

  $( An extended nonnegative integer is neither 0 nor 1 if and only if it is
     greater than 1.  (Contributed by Thierry Arnoux, 21-Nov-2023.) $)
  xnn01gt $p |- ( N e. NN0* -> ( -. N e. { 0 , 1 } <-> 1 < N ) ) $=
    ( cxnn0 wcel cc0 c1 cpr wn wne wa c2 cle wbr clt nelpr xnn0n0n1ge2b cmin co
    cn0 wb 2nn0 xnn0lem1lt mpan 2m1e1 breq1i bitrdi 3bitrd ) ABCZADEFCGADHAEHIJ
    AKLZEAMLZADEBNAOUGUHJEPQZAMLZUIJRCUGUHUKSTJAUAUBUJEAMUCUDUEUF $.

  $( Finite multiplication in the extended nonnegative integers.  (Contributed
     by Thierry Arnoux, 30-Jul-2023.) $)
  nn0xmulclb $p |- ( ( ( A e. NN0* /\ B e. NN0* ) /\ ( A =/= 0 /\ B =/= 0 ) )
       -> ( ( A *e B ) e. NN0 <-> ( A e. NN0 /\ B e. NN0 ) ) ) $=
    ( cxnn0 wcel wa cc0 wne cxmu co cn0 wn cpnf wceq simpr cxr syl2anc cr nn0re
    clt eqneltrd simplr oveq1d xnn0xr ad5antlr simp-5r simprr ad3antrrr xnn0gt0
    wbr xmulpnf2 pnfnre2 mto oveq2d ad5antr simp-5l simprl xmulpnf1 xnn0nnn0pnf
    a1i wo ad5ant15 ad5ant25 orim12d pm3.13 impel mpjaodan condan cmul ad2antrl
    ex ad2antll rexmul nn0mulcl adantl eqeltrd impbida ) ACDZBCDZEZAFGZBFGZEZEZ
    ABHIZJDZAJDZBJDZEZWCWEEZWHWEWCWEWHKZUAWIWJEZALMZWEKBLMZWKWLEZWDLBHIZJWNALBH
    WKWLNUBWNWOLJWNBODZFBSUIZWOLMVRWPVQWBWEWJWLBUCUDWNVRWAWQVQVRWBWEWJWLUEWCWAW
    EWJWLVSVTWAUFUGBUHPBUJPLJDZKZWNWRLQDUKLRULZUSTTWKWMEZWDALHIZJXABLAHWKWMNUMX
    AXBLJXAAODZFASUIZXBLMVQXCVRWBWEWJWMAUCUNXAVQVTXDVQVRWBWEWJWMUOWCVTWEWJWMVSV
    TWAUPUGAUHPAUQPWSXAWTUSTTWIWFKZWGKZUTWLWMUTWJWIXEWLXFWMWIXEWLVQXEWLVRWBWEAU
    RVAVJWIXFWMVRXFWMVQWBWEBURVBVJVCWFWGVDVEVFVGWCWHEZWDABVHIZJXGAQDZBQDZWDXHMW
    FXIWCWGARVIWGXJWCWFBRVKABVLPWHXHJDWCABVMVNVOVP $.

  ${
    xnn0nnd.1 $e |- ( ph -> N e. NN0* ) $.
    xnn0nnd.2 $e |- ( ph -> N e. RR ) $.
    $( Conditions for an extended nonnegative integer to be a nonnegative
       integer.  (Contributed by Thierry Arnoux, 26-Oct-2025.) $)
    xnn0nn0d $p |- ( ph -> N e. NN0 ) $=
      ( cn0 wcel cpnf wceq cxnn0 wo elxnn0 sylib renepnfd neneqd olcnd ) ABEFZB
      GHZABIFPQJCBKLABGABDMNO $.

    xnn0nnd.3 $e |- ( ph -> 0 < N ) $.
    $( Conditions for an extended nonnegative integer to be a positive integer.
       (Contributed by Thierry Arnoux, 26-Oct-2025.) $)
    xnn0nnd $p |- ( ph -> N e. NN ) $=
      ( cn0 wcel cc0 clt wbr cn xnn0nn0d elnnnn0b sylanbrc ) ABFGHBIJBKGABCDLEB
      MN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Real number intervals - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d a b w x A $.  $d a b w x B $.  $d a b w x C $.
    $( Disjoint joining an open interval with a closed-below, open-above
       interval to form a closed-below, open-above interval.  (Contributed by
       Thierry Arnoux, 26-Sep-2017.) $)
    joiniooico $p |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\
      ( A < B /\ B <_ C ) ) -> ( ( ( A (,) B ) i^i ( B [,) C ) ) = (/)
      /\ ( ( A (,) B ) u. ( B [,) C ) ) = ( A (,) C ) ) ) $=
      ( va vb vx vw cxr wcel w3a clt wbr cle wa cioo co cico cin wceq xrltletr
      c0 cun df-ioo df-ico cv xrlenlt ixxdisj adantr ixxun jca ) AHIBHICHIJZABK
      LBCMLNZNABOPZBCQPZRUASZUMUNUBACOPSUKUOULDEFGABCQKKMKODEFUCZDEFUDZBGUEZUFZ
      UGUHDEFGABCQOKKMKOKMUPUQUSUPURBCTABURTUIUJ $.
  $}

  $( A right-open interval does not contain its right endpoint.  (Contributed
     by Thierry Arnoux, 5-Apr-2017.) $)
  ubico $p |- ( ( A e. RR /\ B e. RR* ) -> -. B e. ( A [,) B ) ) $=
    ( cr wcel cxr wa co cle wbr clt w3a simp3 simp1 ltnrd pm2.65i elico2 mtbiri
    cico ) ACDBEDFBABRGDBCDZABHIZBBJIZKZUBUASTUALUBBSTUAMNOABBPQ $.

  $( Equality in terms of 'less than or equal to', 'less than'.  (Contributed
     by Thierry Arnoux, 5-Jul-2017.) $)
  xeqlelt $p |- ( ( A e. RR* /\ B e. RR* ) ->
               ( A = B <-> ( A <_ B /\ -. A < B ) ) ) $=
    ( cxr wcel wa wceq cle wbr clt wn xrletri3 wb xrlenlt ancoms anbi2d bitrd )
    ACDZBCDZEZABFABGHZBAGHZETABIHJZEABKSUAUBTRQUAUBLBAMNOP $.

  $( Relate elementhood to a closed interval with elementhood to the same
     closed-below, open-above interval or to its upper bound.  (Contributed by
     Thierry Arnoux, 3-Jul-2017.) $)
  eliccelico $p |- ( ( A e. RR* /\ B e. RR* /\ A <_ B ) ->
                    ( C e. ( A [,] B ) <-> ( C e. ( A [,) B ) \/ C = B ) ) ) $=
    ( cxr wcel cle wbr w3a co wn wa simpl1 simpl2 biimpa syl21anc syl2anc sylib
    wi syl22anc ex cicc cico wceq wo clt simprl elicc1 simp1d simp3d jca simprr
    simp2d elico1 notbid df-3an notbii imnan imp xeqlelt biimpar pm5.6 icossicc
    bitr4i simpr sselid eqeltrd simpl3 breqtrrd xrleidd mpbir3and jaodan impbid
    eqbrtrd wb ) ADEZBDEZABFGZHZCABUAIZEZCABUBIZEZCBUCZUDZVRVTWBJZKZWCRVTWDRVRW
    FWCVRWFKZCDEZVPCBFGZCBUEGZJZWCWGVOVPVTWHVOVPVQWFLZVOVPVQWFMZVRVTWEUFZVOVPKZ
    VTKZWHACFGZWIWOVTWHWQWIHZABCUGZNZUHOZWMWGVOVPVTWIWLWMWNWPWHWQWIWTUIOWGWOWEW
    HWQWKWGVOVPWLWMUJZVRVTWEUKXAWGWOVTWQXBWNWPWHWQWIWTULPWOWEKZWHWQKZWKXCWHWQWJ
    HZJZXDWKRZWOWEXFWOWBXEABCUMUNNXFXDWJKZJXGXEXHWHWQWJUOUPXDWJUQVCQURSWHVPKWCW
    IWKKCBUSUTSTVTWBWCVAQVRWDVTVRWBVTWCVRWBKWAVSCABVBVRWBVDVEVRWCKZVTWHWQWIXICB
    DVRWCVDZVOVPVQWCMZVFXIABCFVOVPVQWCVGXJVHXICBBFXJXIBXKVIVMXIVOVPVTWRVNVOVPVQ
    WCLXKWSPVJVKTVL $.

  $( Relate elementhood to a closed-below, open-above interval with elementhood
     to the same open interval or to its lower bound.  (Contributed by Thierry
     Arnoux, 6-Jul-2017.) $)
  elicoelioo $p |- ( ( A e. RR* /\ B e. RR* /\ A < B ) ->
                    ( C e. ( A [,) B ) <-> ( C = A \/ C e. ( A (,) B ) ) ) ) $=
    ( cxr wcel clt wbr w3a co wceq wo wn wa wi cle simpl1 simpl2 biimpa syl2anc
    syl21anc cico cioo simprl elico1 simp1d simp2d simprr simp3d elioo1 3anan32
    jca notbid notbii imnan bitr4i sylib imp syl22anc xeqlelt ex eqcom imbitrdi
    biimpar pm5.6 orcom simpr eqeltrd xrleidd breqtrrd simpl3 eqbrtrd mpbir3and
    wb ioossico sselid jaodan impbid ) ADEZBDEZABFGZHZCABUAIZEZCAJZCABUBIZEZKZW
    AWCWFWDKZWGWAWCWFLZMZWDNWCWHNWAWJACJZWDWAWJWKWAWJMZVRCDEZACOGZACFGZLZWKVRVS
    VTWJPZWLVRVSWCWMWQVRVSVTWJQZWAWCWIUCZVRVSMZWCMZWMWNCBFGZWTWCWMWNXBHZABCUDZR
    ZUETZWLVRVSWCWNWQWRWSXAWMWNXBXEUFTWLWTWIWMXBWPWLVRVSWQWRUKZWAWCWIUGXFWLWTWC
    XBXGWSXAWMWNXBXEUHSWTWIMZWMXBMZWPXHWMWOXBHZLZXIWPNZWTWIXKWTWFXJABCUIULRXKXI
    WOMZLXLXJXMWMWOXBUJUMXIWOUNUOUPUQURVRWMMWKWNWPMACUSVCURUTACVAVBWCWFWDVDUPWF
    WDVEVBWAWGWCWAWDWCWFWAWDMZWCWMWNXBXNCADWAWDVFZVRVSVTWDPZVGXNAACOXNAXPVHXOVI
    XNCABFXOVRVSVTWDVJVKXNVRVSWCXCVMXPVRVSVTWDQXDSVLWAWFMWEWBCABVNWAWFVFVOVPUTV
    Q $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Intersection between two open-below, closed-above intervals sharing the
       same upper bound.  (Contributed by Thierry Arnoux, 7-Aug-2017.) $)
    iocinioc2 $p |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ A <_ B )
      -> ( ( A (,] C ) i^i ( B (,] C ) ) = ( B (,] C ) ) $=
      ( vx cxr wcel w3a cle wbr wa cioc co cin cv clt wb elioc1 syl2anc 3adant3
      bitr4d simpl1 simpl3 simpl2 anbi12d simp31 simp32 xrlelttrd simp33 3expia
      elin simp2 3jca pm4.71rd bitrid eqrdv ) AEFZBEFZCEFZGZABHIZJZDACKLZBCKLZM
      ZVCVADNZVDFZVEEFZBVEOIZVECHIZGZVEVCFZVFVEVBFZVKJZVAVJVEVBVCUJVAVMVGAVEOIZ
      VIGZVJJVJVAVLVOVKVJVAUPURVLVOPUPUQURUTUAZUPUQURUTUBZACVEQRVAUQURVKVJPUPUQ
      URUTUCZVQBCVEQRZUDVAVJVOUSUTVJVOUSUTVJGZVGVNVIUSUTVGVHVIUEZVTABVEUSUTUPVJ
      VPSUSUTUQVJVRSWAUSUTVJUKUSUTVGVHVIUFUGUSUTVGVHVIUHULUIUMTUNVSTUO $.
  $}

  ${
    $d x A $.
    xrdifh.1 $e |- A e. RR* $.
    $( Class difference of a half-open interval in the extended reals.
       (Contributed by Thierry Arnoux, 1-Aug-2017.) $)
    xrdifh $p |- ( RR* \ ( A [,] +oo ) ) = ( -oo [,) A ) $=
      ( vx cxr cpnf cicc co cdif cmnf wcel wn wa wbr cle wo w3a pm5.32i 3bitr4i
      wb mp2an cico clt biortn pnfge notnotd biorf syl orcom bitr4di w3o elicc1
      pnfxr notbii 3ianor 3orass 3bitri a1i 3bitr4rd xrltnle mpan2 bitr4d eldif
      cv 3anass mnfxr elico1 mnfle biantrurd eqriv ) CDAEFGZHZIAUAGZCVCZDJZVMVJ
      JZKZLVNVMAUBMZLZVMVKJVMVLJZVNVPVQVNVPAVMNMZKZVQVNWAVMENMZKZOZVNKZWDOZWAVP
      VNWDUCVNWAWCWAOZWDVNWCKWAWGSVNWBVMUDUEWCWAUFUGWAWCUHUIVPWFSVNVPVNVTWBPZKW
      EWAWCUJWFVOWHADJZEDJVOWHSBULAEVMUKTUMVNVTWBUNWEWAWCUOUPUQURVNWIVQWASBVMAU
      SUTVAQVMDVJVBVNIVMNMZVQPZVNWJVQLZLVSVRVNWJVQVDIDJWIVSWKSVEBIAVMVFTVNVQWLV
      NWJVQVMVGVHQRRVI $.
  $}

  $( Relate intersection of two open-below, closed-above intervals with the
     same upper bound with a conditional construct.  (Contributed by Thierry
     Arnoux, 7-Aug-2017.) $)
  iocinif $p |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) ->
      ( ( A (,] C ) i^i ( B (,] C ) )
                                = if ( A < B , ( B (,] C ) , ( A (,] C ) ) ) $=
    ( cxr wcel w3a clt wbr cioc co cin wceq wa wn wo cle iocinioc2 syldan ancld
    ex cif exmid xrltle 3adantl3 simpl2 simpl1 xrlenlt biimpar syl21anc 3ancoma
    imp simpr incom eqtr3id sylanbr orim12d mpi eqif sylibr ) ADEZBDEZCDEZFZABG
    HZACIJZBCIJZKZVFLZMZVDNZVGVELZMZOZVGVDVFVEUALVCVDVJOVMVDUBVCVDVIVJVLVCVDVHV
    CVDVHVCVDABPHZVHUTVAVDVNVBUTVAMVDVNABUCUKUDABCQRTSVCVJVKVCVJVKVCVJBAPHZVKVC
    VJMVAUTVJVOUTVAVBVJUEUTVAVBVJUFVCVJULVAUTMVOVJBAUGUHUIVCVAUTVBFZVOVKVAUTVBU
    JVPVOMVGVFVEKVEVFVEUMBACQUNUORTSUPUQVDVGVFVEURUS $.

  $( The difference between two open intervals sharing the same lower bound.
     (Contributed by Thierry Arnoux, 26-Sep-2017.) $)
  difioo $p |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ A < B )
            -> ( ( A (,) C ) \ ( A (,) B ) ) = ( B [,) C ) ) $=
    ( cxr wcel clt wbr wa cle cioo co wceq cin c0 cun wss simpll1 xrleidd simpr
    adantr w3a cdif incom joiniooico anassrs simpld eqtr3id simprd uncom simpl3
    cico ioossioo syl22anc ssequn2 sylib 3eqtr4d sylanbrc simpl2 xrltled ssdif0
    a1i difeq ico0 biimpar syl21anc eqtr4d wo xrlelttric syl2anc mpjaodan ) ADE
    ZBDEZCDEZUAZABFGZHZBCIGZACJKZABJKZUBZBCUKKZLZCBFGZVPVQHZWAVSMZNLWAVSOZVRVSO
    ZLWBWDWEVSWAMZNVSWAUCWDWHNLZVSWAOZVRLZVNVOVQWIWKHABCUDUEZUFUGWDWJVRWFWGWDWI
    WKWLUHWFWJLWDWAVSUIVAWDVSVRPZWGVRLWDVKVMAAIGZVQWMVKVLVMVOVQQZVPVMVQVKVLVMVO
    UJZTWDAWORVPVQSACABULUMVSVRUNUOUPVRVSWAVBUQVPWCHZVTNWAWQVRVSPZVTNLWQVKVLWNC
    BIGZWRVKVLVMVOWCQZVPVLWCVKVLVMVOURZTZWQAWTRWQCBVPVMWCWPTZXBVPWCSUSZABACULUM
    VRVSUTUOWQVLVMWSWANLZXBXCXDVLVMHXEWSBCVCVDVEVFVPVLVMVQWCVGXAWPBCVHVIVJ $.

  $( The difference between two closed-below, open-above intervals sharing the
     same upper bound.  (Contributed by Thierry Arnoux, 13-Oct-2017.) $)
  difico $p |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\
    ( A <_ B /\ B <_ C ) ) -> ( ( A [,) C ) \ ( B [,) C ) ) = ( A [,) B ) ) $=
    ( cxr wcel w3a cle wbr wa cico co cdif cun cin c0 icodisj undif4 syl adantr
    wceq difid uneq2i un0 eqtri a1i icoun difeq1d 3eqtr3rd ) ADEBDECDEFZABGHBCG
    HIZIZABJKZBCJKZUMLZMZULUMMZUMLZULACJKZUMLUIUOUQTZUJUIULUMNOTUSABCPULUMUMQRS
    UOULTUKUOULOMULUNOULUMUAUBULUCUDUEUKUPURUMABCUFUGUH $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Finite intervals of integers - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d M x $.
    $( Upper integer sets are a subset of the corresponding closed-below,
       open-above intervals.  (Contributed by Thierry Arnoux, 29-Dec-2021.) $)
    uzssico $p |- ( M e. ZZ -> ( ZZ>= ` M ) C_ ( M [,) +oo ) ) $=
      ( vx cz wcel cuz cfv cpnf cico co cv cle wbr wa cr zssre sseli a1i anim1d
      wi eluz1 wb zre elicopnf syl 3imtr4d ssrdv ) ACDZBAEFZAGHIZUGBJZCDZAUJKLZ
      MUJNDZULMZUJUHDUJUIDZUGUKUMULUKUMSUGCNUJOPQRAUJTUGANDUOUNUAAUBAUJUCUDUEUF
      $.
  $}

  $( A finite set of sequential integers that is a subset of ` NN0 ` .
     (Contributed by Thierry Arnoux, 8-Dec-2021.) $)
  fz2ssnn0 $p |- ( M e. NN0 -> ( M ... N ) C_ NN0 ) $=
    ( cn0 wcel cfz co cuz cfv fzssuz cc0 wss nn0uz eleq2i biimpi uzss sseqtrrdi
    syl sstrid ) ACDZABEFAGHZCABISTJGHZCSAUADZTUAKSUBCUAALMNJAOQLPR $.

  ${
    $d j N $.
    $( Upper set of the positive integers.  (Contributed by Thierry Arnoux,
       22-Aug-2017.) $)
    nndiffz1 $p |- ( N e. NN0 -> ( NN \ ( 1 ... N ) ) = ( ZZ>= ` ( N + 1 ) ) )
      $=
      ( vj cn0 wcel cn c1 cfz co caddc cz cle wbr wn wa wb baibd simpr pm5.32da
      zred cc0 cdif cuz cfv cv 1z nn0z elfz1 sylancr 3anass bitrdi notbid simpl
      w3a ltnled zltp1le bitr3d sylan adantr 1red simpll nn0red readdcld simplr
      clt bitrd 0p1e1 nn0ge0d leadd1dd eqbrtrrid letrd ex pm4.71rd bitr4d eldif
      0red elnnz1 anbi1i anass 3bitri a1i peano2nn0 nn0zd eluz1 3bitr4d eqrdv
      syl ) ACDZBEFAGHZUAZAFIHZUBUCZWGBUDZJDZFWLKLZWLWHDZMZNZNZWMWJWLKLZNZWLWID
      ZWLWKDZWGWMWQWSWGWMNZWQWNWSNWSXCWNWPWSXCWNNZWPWLAKLZMZWSXDWOXEXCWOWNXEWGW
      OWMWNXENZWGWOWMWNXEUMZWMXGNWGFJDAJDZWOXHOUEAUFZWLFAUGUHWMWNXEUIUJPPUKXCXF
      WSOZWNWGXIWMXKXJXIWMNZAWLVDLXFWSXLAWLXLAXIWMULSXLWLXIWMQSUNAWLUOUPUQURVER
      XCWSWNXCWSWNXCWSNZFWJWLXMUSZXMAFXMAWGWMWSUTZVAZXNVBXMWLWGWMWSVCSXMFTFIHWJ
      KVFXMTAFXMVOXPXNXMAXOVGVHVIXCWSQVJVKVLVMRXAWROWGXAWLEDZWPNWMWNNZWPNWRWLEW
      HVNXQXRWPWLVPVQWMWNWPVRVSVTWGWJJDXBWTOWGWJAWAWBWJWLWCWFWDWE $.
  $}

  ${
    $d n x y z A $.
    $( For any finite subset of ` NN ` , find a superset in the form of a set
       of sequential integers.  (Contributed by Thierry Arnoux,
       13-Sep-2017.) $)
    ssnnssfz $p |- ( A e. ( ~P NN i^i Fin ) -> E. n e. NN A C_ ( 1 ... n ) ) $=
      ( vx vy vz cn cfn wcel c1 cv cfz co wss wrex c0 wceq wa clt adantr wbr cr
      cpw cin 1nn simpr 0ss eqsstrdi oveq2 sseq2d sylancr wne csup elin simplbi
      rspcev elpwid wor nnssre ltso mp2 a1i simprbi fisupcl syl13anc sseldd cuz
      soss cfv sselda nnuz eleqtrdi cz cle nnzd wn wral wi fisup2g ssrexv supub
      sylc imp nnred lenltd mpbird eluz2 syl3anbrc eluzfz syl2anc ex pm2.61dane
      ssrdv ) AFUBZGUCHZAIBJZKLZMZBFNZAOWNAOPZQZIFHAIIKLZMZWRUDWTAOXAWNWSUEXAUF
      UGWQXBBIFWOIPWPXAAWOIIKUHUIUOUJWNAOUKZQZAFRULZFHAIXEKLZMZWRXDAFXEXDAFWNAW
      MHZXCWNXHAGHZAWMGUMZUNSUPZXDFRUQZXIXCAFMZXEAHZXLXDFUAMUARUQXLURUSFUARVGUT
      VAZWNXIXCWNXHXIXJVBSZWNXCUEZXKFARVCVDZVEXDCAXFXDCJZAHZXSXFHZXDXTQZXSIVFVH
      ZHXEXSVFVHHZYAYBXSFYCXDAFXSXKVIZVJVKYBXSVLHXEVLHXSXEVMTZYDYBXSYEVNYBXEYBA
      FXEXDXMXTXKSXDXNXTXRSVEZVNYBYFXEXSRTVOZXDXTYHXDCDEFAXSRXOXDXMXSDJZRTVODAV
      PYIXSRTYIEJRTEANVQDFVPQZCANZYJCFNXKXDXLXIXCXMYKXOXPXQXKCDEFARVRVDYJCAFVSW
      AVTWBYBXSXEYBXSYEWCYBXEYGWCWDWEXSXEWFWGXSIXEWHWIWJWLWQXGBXEFWOXEPWPXFAWOX
      EIKUHUIUOWIWK $.
  $}

  $( Elementhood of an integer and its predecessor in finite intervals of
     integers.  (Contributed by Thierry Arnoux, 1-Jan-2024.) $)
  fzm1ne1 $p |- ( ( K e. ( M ... N ) /\ K =/= M )
                -> ( K - 1 ) e. ( M ... ( N - 1 ) ) ) $=
    ( cfz co wcel wne wa c1 cmin caddc fzne1 cz elfzel1 elfzel2 elfzelz 1zzd id
    fzsubel biimp3a syl221anc syl adantr zcnd 1cnd pncand oveq1d eleqtrd ) ABCD
    EFZABGZHZAIJEZBIKEZIJEZCIJEZDEZBUODEUKAUMCDEFZULUPFZABCLUQUMMFZCMFZAMFZIMFZ
    UQURAUMCNAUMCOAUMCPUQQUQRUSUTHVAVBHUQURAIUMCSTUAUBUKUNBUODUKBIUKBUIBMFUJABC
    NUCUDUKUEUFUGUH $.

  $( Split the last element of a finite set of sequential integers.  More
     generic than ~ fzsuc .  (Contributed by Thierry Arnoux, 7-Nov-2016.) $)
  fzspl $p |- ( N e. ( ZZ>= ` M ) ->
                ( M ... N ) = ( ( M ... ( N - 1 ) ) u. { N } ) ) $=
    ( cuz cfv wcel cfz co c1 cmin caddc cun csn wceq eluzelz zcnd npcand cz syl
    1zzd eqtrd eleq1d ibir cle wbr eluzelre lem1d wa wb zsubcld eluz1 mpbir2and
    fzsplit2 syl2anc oveq1d fzsn uneq2d ) BACDZEZABFGZABHIGZFGZUTHJGZBFGZKZVABL
    ZKURVBUQEZBUTCDEZUSVDMURVFURVBBUQURBHURBABNZOURHURSZOPZUAUBURVGBQEZUTBUCUDZ
    VHURBABUEUFURUTQEVGVKVLUGUHURBHVHVIUIUTBUJRUKUTABULUMURVCVEVAURVCBBFGZVEURV
    BBBFVJUNURVKVMVEMVHBUORTUPT $.

  $( Split the last element of a finite set of sequential integers.  More
     generic than ~ fzsuc .  (Contributed by Thierry Arnoux, 22-Aug-2020.) $)
  fzdif2 $p |- ( N e. ( ZZ>= ` M )
     -> ( ( M ... N ) \ { N } ) = ( M ... ( N - 1 ) ) ) $=
    ( cuz cfv wcel cfz co csn cdif c1 cmin cun fzspl difeq1d difun2 eqtrdi wceq
    cin c0 wn cz eluzelz uzid uznfz 3syl disjsn sylibr disjdif2 syl eqtrd ) BAC
    DEZABFGZBHZIZABJKGFGZUMIZUOUKUNUOUMLZUMIUPUKULUQUMABMNUOUMOPUKUOUMRSQZUPUOQ
    UKBUOETZURUKBUAEBBCDEUSABUBBUCBABUDUEUOBUFUGUOUMUHUIUJ $.

  $( Split the last element of a half-open range of sequential integers.
     (Contributed by Thierry Arnoux, 5-Dec-2021.) $)
  fzodif2 $p |- ( N e. ( ZZ>= ` M ) -> ( ( M ..^ ( N + 1 ) ) \ { N } )
     = ( M ..^ N ) ) $=
    ( cuz cfv wcel caddc cfzo csn cdif cun fzosplitsn difeq1d difun2 eqtrdi cin
    c1 co c0 wceq wn fzonel disjsn mpbir disjdif2 mp1i eqtrd ) BACDEZABPFQGQZBH
    ZIZABGQZUIIZUKUGUJUKUIJZUIIULUGUHUMUIABKLUKUIMNUKUIORSZULUKSUGUNBUKETABUAUK
    BUBUCUKUIUDUEUF $.

  $( Set difference of two half-open range of sequential integers sharing the
     same starting value.  (Contributed by Thierry Arnoux, 2-Oct-2023.) $)
  fzodif1 $p |- ( K e. ( M ... N )
               -> ( ( M ..^ N ) \ ( M ..^ K ) ) = ( K ..^ N ) ) $=
    ( cfz co wcel cfzo cdif cun fzosplit difeq1d c0 difundir difid wceq fzodisj
    cin incom eqtri disj3 mpbi eqcomi uneq12i 0un 3eqtri eqtrdi ) ABCDEFZBCGEZB
    AGEZHUIACGEZIZUIHZUJUGUHUKUIBCAJKULUIUIHZUJUIHZILUJIUJUIUJUIMUMLUNUJUINUJUN
    UJUIQZLOUJUNOUOUIUJQLUJUIRBACPSUJUITUAUBUCUJUDUEUF $.

  ${
    $d x K $.  $d x M $.  $d x N $.
    $( Split a finite interval of integers into two parts.  (Contributed by
       Thierry Arnoux, 2-May-2017.) $)
    fzsplit3 $p |- ( K e. ( M ... N ) ->
      ( M ... N ) = ( ( M ... ( K - 1 ) ) u. ( K ... N ) ) ) $=
      ( vx cfz co wcel c1 wo wa cle wbr syl2anr cuz cz wb elfzuz elfzuz3 adantl
      cfv cmin cun cv cr elfzelz zred 1red resubcld lelttric 1zzd zsubcld elfz5
      clt elfzuzb syl eluz syl2an zlem1lt 3bitrd orbi12d mpbird adantr peano2uz
      rbaib caddc recnd npcand eleq1d mpbid uztrn syl2anc sylanbrc impbida elun
      jaodan bitr4di eqrdv ) ABCEFZGZDVRBAHUAFZEFZACEFZUBZVSDUCZVRGZWDWAGZWDWBG
      ZIZWDWCGVSWEWHVSWEJZWHWDVTKLZVTWDUMLZIZWEWDUDGVTUDGWLVSWEWDWDBCUEZUFVSAHV
      SAABCUEZUFZVSUGZUHWDVTUIMWIWFWJWGWKWEWDBNTZGZVTOGWFWJPVSWDBCQVSAHWNVSUJUK
      WDBVTULMWIWGWDANTZGZAWDKLZWKWICWDNTZGZWGWTPWEXCVSWDBCRSWGWTXCWDACUNVDUOVS
      AOGZWDOGZWTXAPWEWNWMAWDUPUQVSXDXEXAWKPWEWNWMAWDURUQUSUTVAVSWFWEWGVSWFJZWR
      XCWEWFWRVSWDBVTQSXFCWSGZAXBGZXCVSXGWFABCRVBXFVTHVEFZXBGZXHXFVTXBGZXJWFXKV
      SWDBVTRSWDVTVCUOVSXJXHPWFVSXIAXBVSAHVSAWOVFVSHWPVFVGVHVBVIACWDVJVKWDBCUNZ
      VLVSWGJWRXCWEWGWTAWQGWRVSWDACQABCQAWDBVJMWGXCVSWDACRSXLVLVOVMWDWAWBVNVPVQ
      $.
  $}

  ${
    $( Upper set of the nonnegative integers.  (Contributed by Thierry Arnoux,
       25-Jan-2026.) $)
    nn0diffz0 $p |- ( N e. NN0 -> ( NN0 \ ( 0 ... N ) ) = ( ZZ>= ` ( N + 1 ) )
       ) $=
      ( cn0 wcel cc0 cfz co cdif c1 caddc cfzo cuz cfv cun nn0uz eqtrid difeq1d
      wceq syl cin c0 peano2nn0 eleqtrdi fzouzsplit uncom cz nn0z fzval3 uneq1d
      ineq2d fzouzdisj ineqcomi eqtrdi undif5 3eqtr2d ) ABCZBDAEFZGDAHIFZJFZUQK
      LZMZUPGUSUPMZUPGZUSUOBUTUPUOBDKLZUTNUOUQVCCVCUTQUOUQBVCAUANUBDUQUCROPUOVA
      UTUPUOVAUPUSMUTUSUPUDUOUPURUSUOAUECUPURQAUFDAUGRZUHOPUOUSUPSZTQVBUSQUOVEU
      SURSTUOUPURUSVDUIURUSTDUQUJUKULUSUPUMRUN $.
  $}

  $( The proportion of one binomial coefficient to another with ` N ` decreased
     by 1.  (Contributed by Thierry Arnoux, 9-Nov-2016.) $)
  bcm1n $p |- ( ( K e. ( 0 ... ( N - 1 ) ) /\ N e. NN ) ->
    ( ( ( N - 1 ) _C K ) / ( N _C K ) ) = ( ( N - K ) / N ) ) $=
    ( cc0 c1 cmin co cfz wcel cn wa cbc cdiv wceq cmul cc wbr adantr clt mpbird
    nnne0d caddc bcp1n nnz adantl npcand oveq1d oveq12d oveq2d eqeq12d imbitrid
    zcnd 1cnd 3impia 3anidm13 wne crp cn0 cle elfznn0 simpr nnnn0d elfzelz zred
    wb cz elfzle2 zltlem1 syl2an ltled elfz2nn0 syl3anbrc bcrpcl syl rpcnd cneg
    subcld negsubdi2d resubcld recnd addlidd breqtrrd ltsubaddd lt0ne0d negne0d
    0red eqnetrrd divcld rpcnne0d divmul2 syl3anc bccl2 recdivd 3eqtr3d ) ACBDE
    FZGFHZBIHZJZDBAKFZWNAKFZLFZLFDBBAEFZLFZLFWSWRLFXABLFWQWTXBDLWQWTXBMZWRWSXBN
    FZMZWOWPXEWOWPWOXEWOWNDUAFZAKFZWSXFXFAEFZLFZNFZMWQXEAWNUBWQXGWRXJXDWQXFBAKW
    QBDWPBOHWOWPBBUCZUKUDZWQULUEZUFWQXIXBWSNWQXFBXHXALXMWQXFBAEXMUFUGUHUIUJUMUN
    WQWROHXBOHWSOHWSCUOZJXCXEVDWQWRWQACBGFHZWRUPHWQAUQHZBUQHABURPXOWOXPWPAWNUSQ
    WQBWOWPUTZVAWQABWQAWOAVEHZWPACWNVBZQVCZWQBWPBVEHZWOXKUDVCZWQABRPZAWNURPZWOY
    DWPACWNVFQWOXRYAYCYDVDWPXSXKABVGVHSZVIABVJVKZABVLVMVNZWQBXAXLWQBAXLWOAOHWPW
    OAXSUKQZVPZWQABEFZVOXACWQABYHXLVQWQYJWQYJWQABXTYBVRVSWQYJWQYJCRPACBUAFZRPWQ
    ABYKRYEWQBXLVTWAWQABCXTYBWQWEWBSWCWDWFZWGWQWSWOWSUPHWPAWNVLQZWHWRXBWSWIWJSU
    HWQWRWSYGWQWSYMVNWQWRWQXOWRIHYFABWKVMTWOXNWPWOWSAWNWKTQWLWQBXAXLYIWQBXQTYLW
    LWM $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Half-open integer ranges - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d k m n x N $.  $d k m x A $.  $d m x B $.
    iundisj3.0 $e |- F/_ n B $.
    iundisj3.1 $e |- ( n = k -> A = B ) $.
    $( Rewrite a countable union as a disjoint union, finite version.  Cf.
       ~ iundisj .  (Contributed by Thierry Arnoux, 15-Feb-2017.) $)
    iundisjfi $p |- U_ n e. ( 1 ..^ N ) A =
      U_ n e. ( 1 ..^ N ) ( A \ U_ k e. ( 1 ..^ n ) B ) $=
      ( vx vm c1 cfzo co ciun cv wcel wrex cr clt cn nfcv cdif crab cinf ssrab2
      csb cuz cfv wss c0 wne fzossnn nnuz sseqtri sstri rabn0 biimpri infssuzcl
      sylancr sselid nfrab1 nfinf nfcsb1 nfcri wceq csbeq1a eleq2d elrabf sylib
      simprd wbr nnssre ltnrd eliun ad2antrr elfzouz2 fzoss2 3syl sselda adantr
      wa nnred cle simpr sylanbrc elfzolt2 ad2antlr lelttrd rexlimdva2 biimtrid
      infssuzle eldifd csbeq1 oveq2 iuneq1d difeq12d rspcev syl2anc nfv nfcsb1v
      mtod nfiun nfdif cbvrexw sylibr eldifi reximi impbii 3bitr4i eqriv ) HDJE
      KLZAMZDXJACJDNZKLZBMZUAZMZHNZAOZDXJPZXQXOOZDXJPZXQXKOXQXPOXSYAXSXQDINZAUE
      ZCJYBKLZBMZUAZOZIXJPZYAXSXRDXJUBZQRUCZXJOZXQDYJAUEZCJYJKLZBMZUAZOZYHXSYIX
      JYJXRDXJUDZXSYIJUFUGZUHZYIUIUJZYJYIOZYIXJYRYQXJSYREUKZULUMUNZYTXSXRDXJUOU
      PYIJUQURZUSZXSXQYLYNXSYKXQYLOZXSUUAYKUUFVTUUDXRUUFDYJXJDYIQRXRDXJUTDQTDRT
      VAZDXJTZDHYLDYJAUUGVBVCXLYJVDAYLXQDYJAVEVFVGVHVIXSXQYNOZYJYJRVJZXSYJXSYIQ
      YJYISQYIXJSYQUUBUNVKUNUUDUSZVLUUIXQBOZCYMPXSUUJCXQYMBVMXSUULUUJCYMXSCNZYM
      OZVTZUULVTZYJUUMYJXSYJQOUUNUULUUKVNZUUPUUMUUPXJSUUMUUBUUOUUMXJOZUULXSYMXJ
      UUMXSYKEYJUFUGOYMXJUHUUEYJJEVOYJJEVPVQVRVSZUSWAUUQUUPYSUUMYIOZYJUUMWBVJUU
      CUUPUURUULUUTUUSUUOUULWCXRUULDUUMXJDUUMTUUHDHBFVCXLUUMVDABXQGVFVGWDUUMYIJ
      WJURUUNUUMYJRVJXSUULUUMJYJWEWFWGWHWIWTWKYGYPIYJXJYBYJVDZYFYOXQUVAYCYLYEYN
      DYBYJAWLUVACYDYMBYBYJJKWMWNWOVFWPWQXTYGDIXJXTIWRDHYFDYCYEDYBAWSCDYDBDYDTF
      XAXBVCXLYBVDZXOYFXQUVBAYCXNYEDYBAVEUVBCXMYDBXLYBJKWMWNWOVFXCXDXTXRDXJXQAX
      NXEXFXGDXQXJAVMDXQXJXOVMXHXI $.
  $}

  ${
    $d a b k n x y N $.  $d a b k x y A $.  $d a b x y B $.  $d k n x N $.
    iundisj2fi.0 $e |- F/_ n B $.
    iundisj2fi.1 $e |- ( n = k -> A = B ) $.
    $( A disjoint union is disjoint, finite version.  Cf. ~ iundisj2 .
       (Contributed by Thierry Arnoux, 16-Feb-2017.) $)
    iundisj2fi $p |- Disj_ n e. ( 1 ..^ N ) ( A \ U_ k e. ( 1 ..^ n ) B ) $=
      ( vx vy va vb c1 cfzo cv weq csb cin c0 wcel cr ciun cdif wdisj wceq wral
      co wo wtru tru eqeq12 csbeq1 ineqan12d eqeq1d orbi12d equcom bitrdi incom
      wa eqtrdi wss cn fzossnn nnssre sstri a1i biidd cle wbr w3a wne nesym clt
      wn wb sseli id leltne syl3an vex nfcsb1v nfcv nfiun nfdif csbeq1a iuneq1d
      wi oveq2 difeq12d csbief ineq12i cuz cfv simp1 sselid nnuz eleqtrdi simp2
      cz nnzd simp3 elfzo2 syl3anbrc csbhypf equcoms eqcomd syl ssdifssd ssrind
      ssiun2s eqsstrid disjdif sseq0 sylancl 3expia 3adant3 sylbird orrd adantl
      biimtrrid wlogle mpan rgen2 disjors mpbir ) DLEMUFZACLDNZMUFZBUAZUBZUCHIO
      ZDHNZYIPZDINZYIPZQZRUDZUGZIYEUEHYEUEYQHIYEYEUHYKYESZYMYESZURZYQUIUHJKOZDJ
      NZYIPZDKNZYIPZQZRUDZUGYQYQHIJKYEJHOZKIOZURZUUAYJUUGYPUUBYKUUDYMUJUUJUUFYO
      RUUHUUIUUCYLUUEYNDUUBYKYIUKDUUDYMYIUKULUMUNJIOZKHOZURZUUAYJUUGYPUUMUUAIHO
      YJUUBYMUUDYKUJIHUOUPUUMUUFYORUUMUUFYNYLQYOUUKUULUUCYNUUEYLDUUBYMYIUKDUUDY
      KYIUKULYNYLUQUSUMUNYETUTUHYEVATEVBZVCVDZVEUHYTURYQVFYRYSYKYMVGVHZVIZYQUHU
      UQYJYPYJVMYMYKVJZUUQYPYMYKVKUUQUURYKYMVLVHZYPYRYKTSYSYMTSUUPUUPUUSUURVNYE
      TYKUUOVOYETYMUUOVOUUPVPYKYMVQVRYRYSUUSYPWFUUPYRYSUUSYPYRYSUUSVIZYOCLYMMUF
      ZBUAZDYMAPZUVBUBZQZUTUVERUDYPUUTYODYKAPZCLYKMUFZBUAZUBZUVDQUVEYLUVIYNUVDD
      YKYIUVIHVSDUVFUVHDYKAVTCDUVGBDUVGWAFWBWCDHOZAUVFYHUVHDYKAWDUVJCYGUVGBYFYK
      LMWGWEWHWIDYMYIUVDIVSDUVCUVBDYMAVTCDUVABDUVAWAFWBWCDIOZAUVCYHUVBDYMAWDUVK
      CYGUVABYFYMLMWGWEWHWIWJUUTUVIUVBUVDUUTUVFUVBUVHUUTYKUVASZUVFUVBUTUUTYKLWK
      WLZSYMWRSUUSUVLUUTYKVAUVMUUTYEVAYKUUNYRYSUUSWMWNWOWPUUTYMUUTYEVAYMUUNYRYS
      UUSWQWNWSYRYSUUSWTYKLYMXAXBCUVABYKUVFCHOUVFBUVFBUDHCDHCNZABDUVNWAFGXCXDXE
      XIXFXGXHXJUVBUVCXKYOUVEXLXMXNXOXPXSXQXRXTYAYBDYEYIHIYCYD $.
  $}

  ${
    $d k A $.  $d k n M $.  $d k n N $.
    iundisjcnt.0 $e |- F/_ n B $.
    iundisjcnt.1 $e |- ( n = k -> A = B ) $.
    iundisjcnt.2 $e |- ( ph -> ( N = NN \/ N = ( 1 ..^ M ) ) ) $.
    $( Rewrite a countable union as a disjoint union.  (Contributed by Thierry
       Arnoux, 16-Feb-2017.) $)
    iundisjcnt $p |- ( ph -> U_ n e. N A =
      U_ n e. N ( A \ U_ k e. ( 1 ..^ n ) B ) ) $=
      ( cn wceq ciun c1 cfzo co wa simpr iuneq1d 3eqtr4a cv cdif nfcv iundisjfi
      iundisjf mpjaodan ) AGKLZEGBMZEGBDNEUAOPCMUBZMZLGNFOPZLZAUGQZEKBMEKUIMUHU
      JBCDEDBUCHIUEUMEGKBAUGRZSUMEGKUIUNSTAULQZEUKBMEUKUIMUHUJBCDEFHIUDUOEGUKBA
      ULRZSUOEGUKUIUPSTJUF $.
  $}

  ${
    $d k n M $.  $d k A $.  $d n N $.
    iundisj2cnt.0 $e |- F/_ n B $.
    iundisj2cnt.1 $e |- ( n = k -> A = B ) $.
    iundisj2cnt.2 $e |- ( ph -> ( N = NN \/ N = ( 1 ..^ M ) ) ) $.
    $( A countable disjoint union is disjoint.  Cf. ~ iundisj2 .  (Contributed
       by Thierry Arnoux, 16-Feb-2017.) $)
    iundisj2cnt $p |- ( ph -> Disj_ n e. N ( A \ U_ k e. ( 1 ..^ n ) B ) ) $=
      ( cn wceq c1 cfzo co wo cv wdisj disjeq1 mpbiri ciun cdif nfcv iundisj2fi
      iundisj2f jaoi syl ) AGKLZGMFNOZLZPEGBDMEQNOCUAUBZRZJUHULUJUHULEKUKRBCDED
      BUCHIUEEGKUKSTUJULEUIUKRBCDEFHIUDEGUIUKSTUFUG $.
  $}

  ${
    $( TODO shorten theorems using ~ iundisjcnt or ~ iundisj2cnt with ~ f1ocnt
       $)
    $d A f g $.
    $( Given a countable set ` A ` , number its elements by providing a
       one-to-one mapping either with ` NN ` or an integer range starting from
       1.  The domain of the function can then be used with ~ iundisjcnt or
       ~ iundisj2cnt .  (Contributed by Thierry Arnoux, 25-Jul-2020.) $)
    f1ocnt $p |- ( A ~<_ _om -> E. f ( f : dom f -1-1-onto-> A
      /\ ( dom f = NN \/ dom f = ( 1 ..^ ( ( # ` A ) + 1 ) ) ) ) ) $=
      ( vg com wbr wcel wf1o cn wceq c1 chash caddc co cfzo wo wa wex c0 adantl
      cc0 cdom cfn cv cdm cfv cfz eqidd dm0 a1i id f1oeq123d mpbiri fveq2 hash0
      f1o0 eqtrdi oveq1d 0p1e1 oveq2d fzo0 eqtr4d olcd jca dmeq orbi12d anbi12d
      0ex eqeq1d spcev syl f1odm f1oeq2d ibir cz simpl nnzd fzval3 eqtrd eximdv
      ex imp fz1f1o mpjaodan wn csdm isfinite notbii biimpi anim2i bren2 sylibr
      cen nnenom ensymi entr sylancl bren sylib f1oexbi orcd eximi pm2.61dan )
      ADUAEZAUBFZBUCZUDZAXEGZXFHIZXFJAKUEZJLMZNMZIZOZPZBQZXCXDPZARIZXOXIHFZJXIU
      FMZAXEGZBQZPZXQXOXPXQRUDZARGZYCHIZYCXKIZOZPZXOXQYDYGXQYDRRRGUOXQYCRARRRXQ
      RUGYCRIXQUHUIZXQUJUKULXQYFYEXQYCRXKYIXQXKJJNMRXQXJJJNXQXJTJLMJXQXITJLXQXI
      RKUETARKUMUNUPUQURUPUSJUTUPVAVBVCXNYHBRVGXERIZXGYDXMYGYJXFYCAAXERYJUJXERV
      DZYJAUGUKYJXHYEXLYFYJXFYCHYKVHYJXFYCXKYKVHVEVFVIVJSYBXOXPXRYAXOXRXTXNBXRX
      TXNXRXTPZXGXMXTXGXRXTXGXTXFXSAXEXSAXEVKZVLVMSYLXLXHYLXFXSXKXTXFXSIXRYMSYL
      XIVNFXSXKIYLXIXRXTVOVPJXIVQVJVRVBVCVTVSWASXDXQYBOXCABWBSWCXCXDWDZPZHAXEGZ
      BQZXOYOAHCUCGCQZYQYOAHWLEZYRYOADWLEZDHWLEYSYOXCADWEEZWDZPYTYNUUBXCYNUUBXD
      UUAAWFWGWHWIADWJWKHDWMWNADHWOWPAHCWQWRAHCBWSWRYPXNBYPXGXMYPXGYPXFHAXEHAXE
      VKZVLVMYPXHXLUUCWTVCXAVJXB $.
  $}

  $( NN and integer ranges starting from 1 are countable.  (Contributed by
     Thierry Arnoux, 25-Jul-2020.) $)
  fz1nnct $p |- ( ( A = NN \/ A = ( 1 ..^ M ) ) -> A ~<_ _om ) $=
    ( cn wceq com cdom wbr c1 cfzo nnct breq1 mpbiri wcel fzofi fict ax-mp jaoi
    co cfn ) ACDZAEFGZAHBIRZDZTUACEFGJACEFKLUCUAUBEFGZUBSMUDHBNUBOPAUBEFKLQ $.

  $( NN and integer ranges starting from 1 are a transitive family of set.
     (Contributed by Thierry Arnoux, 25-Jul-2020.) $)
  fz1nntr $p |- ( ( ( A = NN \/ A = ( 1 ..^ M ) ) /\ N e. A )
    -> ( 1 ..^ N ) C_ A ) $=
    ( cn wceq wcel c1 cfzo co wss fzossnn sseq2 mpbiri adantr wi cuz cfv fzoss2
    elfzouz2 syl eleq2 imbi12d imp jaoian ) ADEZCAFZGCHIZAJZAGBHIZEZUEUHUFUEUHU
    GDJCKADUGLMNUJUFUHUJUFUHOCUIFZUGUIJZOUKBCPQFULCGBSCGBRTUJUFUKUHULAUICUAAUIU
    GLUBMUCUD $.

  ${
    fzo0opth.1 $e |- ( ph -> M e. NN0 ) $.
    fzo0opth.2 $e |- ( ph -> N e. NN0 ) $.
    $( Equality for a half open integer range starting at zero is the same as
       equality of its upper bound, analogous to ~ fzopth and ~ fzoopth .
       (Contributed by Thierry Arnoux, 27-May-2025.) $)
    fzo0opth $p |- ( ph -> ( ( 0 ..^ M ) = ( 0 ..^ N ) <-> M = N ) ) $=
      ( cc0 wbr cfzo co wceq wb wa cz wcel nn0zd simpr c0 cle eqeq1d eqcom eqid
      clt 0z fzoopth mp3an2ani biantrur bitr4di oveq2d fzo0 eqtr3di bitrdi fzon
      0zd adantr syl2anc nn0le0eq0 biimpa sylan adantlr id 0le0 eqbrtrdi adantl
      cn0 impbida a1i 3bitrd 3bitr2d nn0ge0d 0red nn0red leloed mpbid mpjaodan
      wo ) AFBUBGZFBHIZFCHIZJZBCJZKFBJZAVPLVSFFJZVTLZVTFMNZABMNVPVPVSWCKUCABDOA
      VPPFCFBUDUEWBVTFUAUFUGAWALZVSVRQJZCFRGZVTWEVSQVRJWFWEVQQVRWEFFHIVQQWEFBFH
      AWAPZUHFUIUJSQVRTUKWEWDCMNZWGWFKWEUMAWIWAACEOUNFCULUOWEWGCFJZFCJZVTWEWGWJ
      AWGWJWAACVDNZWGWJEWLWGWJCUPUQURUSWJWGWEWJCFFRWJUTVAVBVCVEWJWKKWECFTVFWEFB
      CWHSVGVHAFBRGVPWAVOABDVIAFBAVJABDVKVLVMVN $.
  $}

  ${
    nn0difffzod.1 $e |- ( ph -> N e. ZZ ) $.
    nn0difffzod.2 $e |- ( ph -> M e. ( NN0 \ ( 0 ..^ N ) ) ) $.
    $( A nonnegative integer that is not in the half-open range from 0 to ` N `
       is at least ` N ` .  (Contributed by Thierry Arnoux, 20-Feb-2025.) $)
    nn0difffzod $p |- ( ph -> -. M < N ) $=
      ( cc0 cfzo co wcel wn cn0 cz clt wbr eldifbd eldifad wa wi w3a elfzo0z
      biimpri 3expa con3i imnan sylibr imp syl12anc ) ABFCGHZIZJZBKIZCLIZBCMNZJ
      ZABKUHEOABKUHEPDUJUKULQZUNUJUOUMQZJUOUNRUPUIUKULUMUIUIUKULUMSBCTUAUBUCUOU
      MUDUEUFUG $.
  $}

  ${
    $d F k $.  $d N k $.  $d Z k $.  $d k ph $.
    suppssnn0.f $e |- ( ph -> F Fn NN0 ) $.
    suppssnn0.n $e |- ( ( ( ph /\ k e. NN0 ) /\ N <_ k ) -> ( F ` k ) = Z ) $.
    suppssnn0.1 $e |- ( ph -> N e. ZZ ) $.
    $( Show that the support of a function is contained in an half-open
       nonnegative integer range.  (Contributed by Thierry Arnoux,
       20-Feb-2025.) $)
    suppssnn0 $p |- ( ph -> ( F supp Z ) C_ ( 0 ..^ N ) ) $=
      ( cn0 crn cc0 cfzo co wfn wf dffn3 sylib cv wcel adantr cdif cle wbr wceq
      wa cfv simpl eldifi adantl cr nn0red cz simpr nn0difffzod nltled syl21anc
      zred suppss ) AICJZBCKDLMZEACINIUSCOFICPQABRZIUTUASZUEZAVAISZDVAUBUCVACUF
      EUDAVBUGVBVDAVAIUTUHUIZVCDVAADUJSVBADHUQTVCVAVEUKVCVADADULSVBHTAVBUMUNUOG
      UPUR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The ` # ` (set size) function - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y A $.  $d y ph $.
    hashiunf.1 $e |- F/ x ph $.
    hashiunf.3 $e |- ( ph -> A e. Fin ) $.
    hashunif.4 $e |- ( ph -> A C_ Fin ) $.
    hashunif.5 $e |- ( ph -> Disj_ x e. A x ) $.
    $( The cardinality of a disjoint finite union of finite sets.  Cf.
       ~ hashuni .  (Contributed by Thierry Arnoux, 17-Feb-2017.) $)
    hashunif $p |- ( ph -> ( # ` U. A ) = sum_ x e. A ( # ` x ) ) $=
      ( vy cuni chash cfv cv ciun csu uniiun fveq2i cfn wdisj wceq a1i cbvdisjv
      sselda id sylib hashiun cbviunv fveq2d fveq2 cbvsumv 3eqtr4d eqtrid ) ACI
      ZJKBCBLZMZJKZCUMJKZBNZULUNJBCOPAHCHLZMZJKCURJKZHNZUOUQAHCUREACQURFUBABCUM
      RHCURRGBHCUMURUMURSUCZUAUDUEAUNUSJUNUSSABHCUMURVBUFTUGUQVASACUPUTBHUMURJU
      HUITUJUK $.
  $}

  $( The size of the Cartesian product of two finite sets is the product of
     their sizes.  This is a version of ~ hashxp valid for infinite sets, which
     uses extended real numbers.  (Contributed by Thierry Arnoux,
     27-May-2023.) $)
  hashxpe $p |- ( ( A e. V /\ B e. W )
                      -> ( # ` ( A X. B ) ) = ( ( # ` A ) *e ( # ` B ) ) ) $=
    ( wcel wa cfn chash cfv cxmu co wceq wn simpr syl cc0 eqtrdi cpnf syl2anc
    c0 cxp hashxp cr cn0 nn0ssre hashcl sselid anim12i rexmul eqtr4d wne xpeq2d
    cmul xp0 fveq2d hash0 simpl hashinf sylan adantr oveq12d pnfxr xmul01 ax-mp
    cxr clt wbr ad2antrr hashxrcl hashgt0 sylancom xmulpnf2 oveq1d xpexd simplr
    cvv eleq1 mpbiri necon3bi wo ioran xpeq0 necon3abii anbi12i 3bitr4i biimpri
    0fi df-ne intnanrd wi pm4.61 xpfir ex con3i sylbir 3eqtr4rd exmidne adantlr
    a1i mpjaodan xpeq1d xmul02 ad3antrrr ad4ant14 xmulpnf1 oveq2d intnand ianor
    0xp bilani exmidd ) ACEZBDEZFZAGEZBGEZFZABUAZHIZAHIZBHIZJKZLZXQMZXNXQFZXSXT
    YAUMKZYBYEXQXSYFLXNXQNZABUBOYEXTUCEZYAUCEZFZYBYFLYEXQYJYGXOYHXPYIXOUDUCXTUE
    AUFUGXPUDUCYAUEBUFUGUHOXTYAUIOUJXNYDFXOMZYCXPMZXNYKYCYDXNYKFZBTLZYCBTUKZYMY
    NFZXSPYBYPXSTHIZPYPXRTHYPXRATUATYPBTAYMYNNZULAUNQUOUPQYPYBRPJKZPYPXTRYAPJYM
    XTRLZYNXNXLYKYTXLXMUQZACURUSZUTYPYAYQPYPBTHYRUOUPQVARVEEZYSPLVBRVCVDQUJYMYO
    FZRYAJKZRYBXSUUDYAVEEZPYAVFVGZUUERLUUDXMUUFXNXMYKYOXLXMNZVHZBDVIOYMYOXMUUGU
    UIBDVJVKYAVLSUUDXTRYAJYMYTYOUUBUTVMUUDXRVPEZXRGEZMZXSRLZUUDABCDXNXLYKYOUUAV
    HUUIVNUUDXRTUKZYDUULUUDATUKZYOUUNUUDYKUUOXNYKYOVOZXOATATLZXOTGEZWGATGVQVRVS
    OYMYONUUNUUOYOFZUUQYNVTZMUUQMZYNMZFUUNUUSUUQYNWAUUTXRTABWBWCUUOUVAYOUVBATWH
    BTWHWDWEWFZSUUDXOXPUUPWIUUNYDFUUNXQWJZMUULUUNXQWKUUKUVDUUKUUNXQABWLWMWNWOZS
    XRVPURZSWPYNYOVTYMBTWQWSWTWRXNYLYCYDXNYLFZUUQYCUUOUVGUUQFZXSPYBUVHXSYQPUVHX
    RTHUVHXRTBUATUVHATBUVGUUQNZXABXIQUOUPQUVHYBPRJKZPUVHXTPYARJUVHXTYQPUVHATHUV
    IUOUPQUVGYARLZUUQXNXMYLUVKUUHBDURUSZUTVAUUCUVJPLVBRXBVDQUJUVGUUOFZXTRJKZRYB
    XSUVMXTVEEZPXTVFVGZUVNRLXLUVOXMYLUUOACVIXCXLUUOUVPXMYLACVJXDXTXESUVMYARXTJU
    VGUVKUUOUVLUTXFUVMUUJUULUUMUVMABCDXNXLYLUUOUUAVHXNXMYLUUOUUHVHVNUVMUUNYDUUL
    UVMUUOYOUUNUVGUUONUVMYLYOXNYLUUOVOZXPBTYNXPUURWGBTGVQVRVSOUVCSUVMXPXOUVQXGU
    VESUVFSWPUUQUUOVTUVGATWQWSWTWRYDYKYLVTXNXOXPXHXJWTXNXQXKWT $.

  $( Restate "set contains at least two elements" in terms of elementhood.
     (Contributed by Thierry Arnoux, 21-Nov-2023.) $)
  hashgt1 $p |- ( A e. V
               -> ( -. A e. ( `' # " { 0 , 1 } ) <-> 1 < ( # ` A ) ) ) $=
    ( wcel chash ccnv cc0 c1 cpr cima wn cfv clt wbr cvv wa cn0 cpnf csn cun wb
    wf wfn hashf ffn elpreima mp2b elex biantrurd bitr4id notbid cxnn0 hashxnn0
    xnn01gt syl bitrd ) ABCZADEFGHZICZJADKZUQCZJZGUSLMZUPURUTUPURANCZUTOZUTNPQR
    SZDUADNUBURVDTUCNVEDUDNAUQDUEUFUPVCUTABUGUHUIUJUPUSUKCVAVBTABULUSUMUNUO $.

  ${
    hashne0.1 $e |- ( ph -> A e. V ) $.
    hashne0.2 $e |- ( ph -> A =/= (/) ) $.
    $( Deduce that the size of a set is not zero.  (Contributed by Thierry
       Arnoux, 26-Oct-2025.) $)
    hashne0 $p |- ( ph -> 0 < ( # ` A ) ) $=
      ( chash cfv cxnn0 wcel cc0 wne clt wbr hashxnn0 hasheq0 necon3bid biimpar
      syl c0 syl2anc xnn0gt0 ) ABFGZHIZUBJKZJUBLMABCIZUCDBCNRAUEBSKZUDDEUEUDUFU
      EUBJBSBCOPQTUBUAT $.
  $}

  ${
    hashimaf1.1 $e |- ( ph -> F : A -1-1-> B ) $.
    hashimaf1.2 $e |- ( ph -> C C_ A ) $.
    hashimaf1.3 $e |- ( ph -> A e. V ) $.
    $( Taking the image of a set by a one-to-one function does not affect size.
       (Contributed by Thierry Arnoux, 18-Jan-2026.) $)
    hashimaf1 $p |- ( ph -> ( # ` ( F " C ) ) = ( # ` C ) ) $=
      ( cima cen wbr chash cfv wceq cpw wcel cres wf1o syl2anc sselpwd wf1 wss
      f1ores f1oeng ensymd hasheni syl ) AEDJZDKLUIMNDMNOADUIADBPZQDUIEDRZSZDUI
      KLADBFIHUAABCEUBDBUCULGHBCDEUDTDUIUJUKUETUFUIDUGUH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The greatest common divisor operator - misc. additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d Q p q x y $.
    $( Elementhood in the rational numbers, providing the canonical
       representation.  (Contributed by Thierry Arnoux, 9-Nov-2025.) $)
    elq2 $p |- ( Q e. QQ -> E. p e. ZZ E. q e. NN
                                ( Q = ( p / q ) /\ ( p gcd q ) = 1 ) ) $=
      ( vx vy wcel cv cdiv co wceq cgcd c1 wa cn wrex oveq1 eqeq2d eqeq1d cc0
      cz anbi12d oveq2 wne simpllr simplr nnzd nnne0d divgcdz syl3anc divgcdnnr
      cq syl2anc simpr nncnd gcdcld nn0cnd wn neneqd intnand necon3abid biimpar
      gcdeq0 syl21anc divcan7d eqtr4d divgcdcoprm0 jca 2rspcedvdw elq r19.29vva
      zcnd biimpi ) AUKFZADGZEGZHIZJZACGZBGZHIZJZVRVSKIZLJZMZBNOCTODETNVMVNTFZM
      ZVONFZMZVQMZWDAVNVNVOKIZHIZVSHIZJZWKVSKIZLJZMAWKVOWJHIZHIZJZWKWPKIZLJZMCB
      WKWPTNVRWKJZWAWMWCWOXAVTWLAVRWKVSHPQXAWBWNLVRWKVSKPRUAVSWPJZWMWRWOWTXBWLW
      QAVSWPWKHUBQXBWNWSLVSWPWKKUBRUAWIWEVOTFZVOSUCZWKTFVMWEWGVQUDZWIVOWFWGVQUE
      ZUFZWIVOXFUGZVNVOUHUIWIWGWEWPNFXFXEVOVNUJULWIWRWTWIAVPWQWHVQUMWIVNVOWJWIV
      NXEVKWIVOXFUNWIWJWIVNVOXEXGUOUPXHWIWEXCVNSJZVOSJZMZUQZWJSUCZXEXGWIXJXIWIV
      OSXHURUSWEXCMZXMXLXNXKWJSVNVOVBUTVAVCVDVEWIWEXCXDWTXEXGXHVNVOVFUIVGVHVMVQ
      ENODTODEAVIVLVJ $.
  $}

  ${
    znumd.1 $e |- ( ph -> Z e. ZZ ) $.
    $( Numerator of an integer.  (Contributed by Thierry Arnoux,
       4-May-2025.) $)
    znumd $p |- ( ph -> ( numer ` Z ) = Z ) $=
      ( cnumer cfv wceq cdenom c1 cq wcel cz cn cgcd co cdiv wa zq syl 1nn a1i
      gcd1 zcnd div1d eqcomd w3a qnumdenbi biimpa syl32anc simpld ) ABDEBFZBGEH
      FZABIJZBKJZHLJZBHMNHFZBBHONZFZUJUKPZAUMULCBQRCUNASTAUMUOCBUARAUPBABABCUBU
      CUDULUMUNUEUOUQPURBBHUFUGUHUI $.

    $( Denominator of an integer.  (Contributed by Thierry Arnoux,
       4-May-2025.) $)
    zdend $p |- ( ph -> ( denom ` Z ) = 1 ) $=
      ( cnumer cfv wceq cdenom c1 cq wcel cz cn cgcd co cdiv wa zq syl 1nn a1i
      gcd1 zcnd div1d eqcomd w3a qnumdenbi biimpa syl32anc simprd ) ABDEBFZBGEH
      FZABIJZBKJZHLJZBHMNHFZBBHONZFZUJUKPZAUMULCBQRCUNASTAUMUOCBUARAUPBABABCUBU
      CUDULUMUNUEUOUQPURBBHUFUGUHUI $.
  $}

  $( Numerator and denominator of the negative.  (Contributed by Thierry
     Arnoux, 27-Oct-2017.) $)
  numdenneg $p |- ( Q e. QQ -> ( ( numer ` -u Q ) = -u ( numer ` Q )
    /\ ( denom ` -u Q ) = ( denom ` Q ) ) ) $=
    ( cq wcel cneg cnumer cfv cz cdenom cn cgcd wceq cdiv qnegcl qnumcl znegcld
    co c1 wa qdencl eqtrd neggcd syl2anc qnumdencoprm qeqnumdivden negeqd nncnd
    nnzd zcnd nnne0d divnegd w3a qnumdenbi biimpa syl32anc ) ABCZADZBCZAEFZDZGC
    ZAHFZICZUSVAJPZQKZUPUSVALPZKZUPEFUSKUPHFVAKRZAMUOURANZOASZUOVCURVAJPZQUOURG
    CVAGCVCVJKVHUOVAVIUGURVAUAUBAUCTUOUPURVALPZDVEUOAVKAUDUEUOURVAUOURVHUHUOVAV
    IUFUOVAVIUIUJTUQUTVBUKVDVFRVGUPUSVAULUMUN $.

  $( Calculate the reduced form of a quotient using ` gcd ` .  This version
     extends ~ divnumden for the negative integers.  (Contributed by Thierry
     Arnoux, 25-Oct-2017.) $)
  divnumden2 $p |- ( ( A e. ZZ /\ B e. ZZ /\ -u B e. NN ) ->
       ( ( numer ` ( A / B ) ) = -u ( A / ( A gcd B ) )
      /\ ( denom ` ( A / B ) ) = -u ( B / ( A gcd B ) ) ) ) $=
    ( cz wcel cneg cdiv co cnumer cfv cgcd wceq cdenom cc0 wne zcnd syl 3adant2
    cq wa divneg2d cn zssq simp1 sselid simp2 nnne0 3ad2ant3 neg0 neeq2i sylibr
    w3a neneqd 0cnd neg11ad mtbid neqned qdivcl syl3anc qnumcl cc gcdcld nn0cnd
    simpl negcld intnand gcdeq0 necon3abid 3adant3 mpbird negne0d divcld fveq2d
    wn wb numdenneg simpld gcdneg oveq2d divnegd div2negd eqtrd 3eqtr4d 3eqtr3d
    divnumden neg11d eqtr4d simprd eqtr3d jca ) ACDZBCDZBEZUADZUKZABFGZHIZAABJG
    ZFGZEZKWOLIZBWQFGEZKWNWPAWQEZFGZWSWNWPXCWNWPWNWORDZWPCDWNARDBRDBMNXDWNCRAUB
    WJWKWMUCZUDWNCRBUBWJWKWMUEZUDWNBMWNWLMEZKBMKZWNWLXGWNWLMNZWLXGNWMWJXIWKWLUF
    UGXGMWLUHUIUJULWNBMWNBXFOZWNUMUNUOZUPZABUQURZWOUSPOWNAXBWJWMAUTDWKWJWMSZAWJ
    WMVCOQZWNWQWNWQWNABXEXFVAVBZVDZWNWQXPWNWQMNZAMKZXHSZVMZWNXHXSXKVEWJWKXRYAVN
    WMWJWKSXTWQMABVFVGVHVIZVJZVKWNWOEZHIZAWLFGZHIZWPEZXCEZWNYDYFHWNABXOXJXLTZVL
    WNXDYEYHKZXMXDYKYDLIZWTKZWOVOZVPPWNAAWLJGZFGZWRYGYIWNYOWQAFWJWKYOWQKWMABVQV
    HZVRWJWMYGYPKZWKXNYRYFLIZWLYOFGZKZAWLWDZVPQWNYIAEXBFGWRWNAXBXOXQYCVSWNAWQXO
    XPYBVTWAWBWCWEWNAWQXOXPYBTWFWNWTBXBFGZXAWNYLYSWTUUCWNYDYFLYJVLWNXDYMXMXDYKY
    MYNWGPWNYTWLWQFGZYSUUCWNYOWQWLFYQVRWJWMUUAWKXNYRUUAUUBWGQWNXAUUCUUDWNBWQXJX
    PYBTZWNBWQXJXPYBVSWHWBWCUUEWFWI $.

  ${
    expgt0b.n $e |- ( ph -> A e. RR ) $.
    expgt0b.m $e |- ( ph -> N e. NN ) $.
    expgt0b.1 $e |- ( ph -> -. 2 || N ) $.
    $( A real number ` A ` raised to an odd integer power is positive iff it is
       positive.  (Contributed by SN, 4-Mar-2023.)  Use the more standard
       ` -. 2 || N ` (Revised by Thierry Arnoux, 14-Jun-2025.) $)
    expgt0b $p |- ( ph -> ( 0 < A <-> 0 < ( A ^ N ) ) ) $=
      ( cc0 clt wbr cexp co wa wcel adantr simpr syl3anc ex wn wceq breq2d nnzd
      cr cz expgt0 wo 0red lttrid notbid notnotr 0re ltnri mtbiri eqcomd oveq1d
      0expd mtbird renegcld cc cn c2 cdvds recnd oexpneg biimpd nnnn0d reexpcld
      cneg pm2.46 biimtrdi 3syld lt0neg1d lt0neg2d 3imtr4d jaod syl5 impcon4bid
      sylbid ) AGBHIZGBCJKZHIZAVRVTAVRLBUBMZCUCMZVRVTAWAVRDNAWBVRACEUAZNAVROBCU
      DPQAVRRGBSZBGHIZUEZRZRZVTRZAVRWGAGBAUFZDUGUHWHWFAWIWFUIAWDWIWEAWDWIAWDLZV
      TGGCJKZHIZAWMRWDAWMGGHIGUJUKAWLGGHACEUOTULNWKVSWLGHWKBGCJWKGBAWDOUMUNTUPQ
      AGBVGZHIZVSVGZGHIZRZWEWIAWOGWNCJKZHIZGWPHIZWRAWOWTAWOLWNUBMZWBWOWTAXBWOAB
      DUQNAWBWOWCNAWOOWNCUDPQAWTXAAWSWPGHABURMCUSMUTCVAIRWSWPSABDVBEFBCVCPTVDAX
      AGWPSZWQUERWRAGWPWJAVSABCDACEVEVFZUQUGXCWQVHVIVJABDVKAVTWQAVSXDVLUHVMVNVO
      VQVP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Integers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Split 0 and 1 from the nonnegative integers.  (Contributed by Thierry
     Arnoux, 8-Jun-2025.) $)
  nn0split01 $p |- NN0 = ( { 0 , 1 } u. ( ZZ>= ` 2 ) ) $=
    ( cn0 cc0 cuz cfv c2 cfzo co cun c1 cpr nn0uz wcel wceq 2eluzge0 fzouzsplit
    ax-mp fzo0to2pr uneq1i 3eqtri ) ABCDZBEFGZECDZHZBIJZUBHKETLTUCMNBEOPUAUDUBQ
    RS $.

  $( The pair ` { 0 , 1 } ` does not overlap the rest of the nonnegative
     integers.  (Contributed by Thierry Arnoux, 8-Jun-2025.) $)
  nn0disj01 $p |- ( { 0 , 1 } i^i ( ZZ>= ` 2 ) ) = (/) $=
    ( cc0 c2 cfzo co cuz cfv cin c1 cpr c0 fzo0to2pr ineq1i fzouzdisj eqtr3i )
    ABCDZBEFZGAHIZPGJOQPKLABMN $.

  ${
    $d w x y $.  $d x A $.  $d w ph $.  $d x ch $.  $d x ps $.  $d x ta $.
    $d x th $.
    nnindf.x $e |- F/ y ph $.
    $( Substitutions. $)
    nnindf.1 $e |- ( x = 1 -> ( ph <-> ps ) ) $.
    nnindf.2 $e |- ( x = y -> ( ph <-> ch ) ) $.
    nnindf.3 $e |- ( x = ( y + 1 ) -> ( ph <-> th ) ) $.
    nnindf.4 $e |- ( x = A -> ( ph <-> ta ) ) $.
    $( Basis. $)
    nnindf.5 $e |- ps $.
    $( Induction step. $)
    nnindf.6 $e |- ( y e. NN -> ( ch -> th ) ) $.
    $( Principle of Mathematical Induction, using a bound-variable hypothesis
       instead of distinct variables.  (Contributed by Thierry Arnoux,
       6-May-2018.) $)
    nnindf $p |- ( A e. NN -> ta ) $=
      ( vw cn wcel c1 elrab crab wa caddc wral wss 1nn mpbir2an elrabi peano2nn
      cv a1d anim12d 3imtr4g mpcom rgen nfcv nfrabw nfv nfel2 wceq oveq1 eleq1d
      co cbvralfw mpbi peano5nni mp2an sseli sylib simprd ) HQRZVKEVKHAFQUAZRVK
      EUBQVLHSVLRZPUJZSUCVCZVLRZPVLUDZQVLUEVMSQRBUFNABFSQJTUGGUJZSUCVCZVLRZGVLU
      DVQVTGVLVRQRZVRVLRZVTAFVRQUHWAWACUBVSQRZDUBWBVTWAWAWCCDWAWCWAVRUIUKOULACF
      VRQKTADFVSQLTUMUNUOVTVPGPVLAGFQIGQUPUQZPVLUPVTPURGVOVLWDUSVRVNUTVSVOVLVRV
      NSUCVAVBVDVEPVLVFVGVHAEFHQMTVIVJ $.
  $}

  ${
    $d k m n ph $.  $d k m ps $.  $d k n ta $.  $d k n th $.  $d m n ch $.
    nn0min.0 $e |- ( n = 0 -> ( ps <-> ch ) ) $.
    nn0min.1 $e |- ( n = m -> ( ps <-> th ) ) $.
    nn0min.2 $e |- ( n = ( m + 1 ) -> ( ps <-> ta ) ) $.
    nn0min.3 $e |- ( ph -> -. ch ) $.
    nn0min.4 $e |- ( ph -> E. n e. NN ps ) $.
    $( Extracting the minimum positive integer for which a property ` ch ` does
       not hold.  This uses substitutions similar to ~ nn0ind .  (Contributed
       by Thierry Arnoux, 6-May-2018.) $)
    nn0min $p |- ( ph -> E. m e. NN0 ( -. th /\ ta ) ) $=
      ( vk wn cn0 wi cn c1 wceq notbid wa wral wrex adantr wsb wsbc cv nfv nfan
      nfra1 nfim dfsbcq2 imbi2d sbhypf caddc co sbequ12r cc0 wcel sbiev bitr3id
      0nn0 wb oveq1 0p1e1 eqtrdi 1nn eleq1 mpbiri sbcieg sbceq1d bitr3d imbi12d
      rspcv ax-mp mpan9 cbvralsvw nnnn0 syl biimtrid adantld a2d nnindf r19.21v
      3syl rgen mpbi ralnex sylib pm2.65da imnan ralbii sylnib dfrex2 sylibr )
      ADNZEUAZNZFOUBZNWQFOUCAWPENZPZFOUBZWSAXBBGQUCZAXCXBLUDAXBUAZBNZGQUBZXCNXD
      XEPZGQUBXDXFPXGGQXDBGMUEZNZPXDBGRUFZNZPXDWPPXDWTPXGMFGUGZXDXIFAXBFAFUHXAF
      OUJUIXIFUHUKMUGZRSZXIXKXDXNXHXJBGMRULTUMXMFUGZSZXIWPXDXPXHDBDGMXODGUHZIUN
      TUMXMXORUOUPZSZXIWTXDXSXHEBEGMXREGUHJUNTUMXMXLSZXIXEXDXTXHBBMGUQTUMACNZXB
      XKKUROUSXBYAXKPZPVBXAYBFUROXOURSZWPYAWTXKYCDCDBGFUEYCCBDGFXQIUTBCGFURCGUH
      HUNVATYCEXJYCBGXRUFZEXJYCXRRSZXRQUSZYDEVCYCXRURRUOUPRXOURRUOVDVEVFZYEYFRQ
      USVGXRRQVHVIBEGXRQJVJWEYCBGXRRYGVKVLTVMVNVOVPXOQUSZXDWPWTYHXBXAAXBXAFMUEZ
      MOUBZYHXAXAFMOVQYHXOOUSYJXAPXOVRYIXAMXOOXAMFUQVNVSVTWAWBWCWFXDXEGQWDWGBGQ
      WHWIWJXAWRFOWPEWKWLWMWQFOWNWO $.
  $}

  ${
    subne0nn.1 $e |- ( ph -> M e. CC ) $.
    subne0nn.2 $e |- ( ph -> N e. CC ) $.
    subne0nn.3 $e |- ( ph -> ( M - N ) e. NN0 ) $.
    subne0nn.4 $e |- ( ph -> M =/= N ) $.
    $( A nonnegative difference is positive if the two numbers are not equal.
       (Contributed by Thierry Arnoux, 17-Dec-2023.) $)
    subne0nn $p |- ( ph -> ( M - N ) e. NN ) $=
      ( cmin co cn0 wcel cc0 wne cn subne0d elnnne0 sylanbrc ) ABCHIZJKRLMRNKFA
      BCDEGORPQ $.
  $}

  ${
    ltesubnnd.1 $e |- ( ph -> M e. ZZ ) $.
    ltesubnnd.2 $e |- ( ph -> N e. NN ) $.
    $( Subtracting an integer number from another number decreases it.  See
       ~ ltsubrpd .  (Contributed by Thierry Arnoux, 18-Apr-2017.) $)
    ltesubnnd $p |- ( ph -> ( ( M + 1 ) - N ) <_ M ) $=
      ( c1 caddc co cmin cle zcnd 1cnd nncnd addsubd clt wbr zred nnrpd cz wcel
      ltsubrpd wb nnzd zsubcld zltp1le syl2anc mpbid eqbrtrd ) ABFGHCIHBCIHZFGH
      ZBJABFCABDKALACEMNAUIBOPZUJBJPZABCABDQACERUAAUISTBSTUKULUBABCDACEUCUDDUIB
      UEUFUGUH $.
  $}

  ${
    $d A k $.  $d C k $.  $d K k $.  $d ph k $.
    fprodeq02.1 $e |- ( k = K -> B = C ) $.
    fprodeq02.a $e |- ( ph -> A e. Fin ) $.
    fprodeq02.b $e |- ( ( ph /\ k e. A ) -> B e. CC ) $.
    fprodeq02.k $e |- ( ph -> K e. A ) $.
    fprodeq02.c $e |- ( ph -> C = 0 ) $.
    $( If one of the factors is zero the product is zero.  (Contributed by
       Thierry Arnoux, 11-Dec-2021.) $)
    fprodeq02 $p |- ( ph -> prod_ k e. A B = 0 ) $=
      ( cprod csn cmul co cc0 wceq wcel cc cfn cin c0 disjdif a1i cun wss snssd
      cdif undif sylib eqcomd fprodsplit 0cnd eqeltrd prodsn eqtrd oveq1d diffi
      syl2anc syl cv difssd sselda syldan fprodcl mul02d 3eqtrd ) ABCELFMZCELZB
      VHUHZCELZNOPVKNOPAVHVJCBEVHVJUAUBQAVHBUCUDAVHVJUEZBAVHBUFVLBQAFBJUGVHBUIU
      JUKHIULAVIPVKNAVIDPAFBRDSRVIDQJADPSKAUMUNCDEFBGUOUSKUPUQAVKAVJCEABTRVJTRH
      BVHURUTAEVAZVJRVMBRCSRAVJBVMABVHVBVCIVDVEVFVG $.
  $}

  ${
    $d A k l $.  $d B l $.  $d C k $.  $d k l ph $.
    fprodex01.1 $e |- ( k = l -> B = C ) $.
    fprodex01.a $e |- ( ph -> A e. Fin ) $.
    fprodex01.b $e |- ( ( ph /\ k e. A ) -> B e. { 0 , 1 } ) $.
    $( A product of factors equal to zero or one is zero exactly when one of
       the factors is zero.  (Contributed by Thierry Arnoux, 11-Dec-2021.) $)
    fprodex01 $p |- ( ph -> prod_ k e. A B = if ( A. l e. A C = 1 , 1 , 0 ) )
      $=
      ( c1 wceq wral cc0 cprod wa cv wcel adantr cc adantlr cif eqeq1d cbvralvw
      bilanri prodeq2d cfn cuz cfv wss prod1 olcs syl eqtr2d nfv nfra1 nfn nfan
      wn ad2antrr cpr cr pr01ssre ax-resscn sstri sselid simplr simpr fprodeq02
      wrex rexnal wi wo ralrimiva eleq1d sylib r19.21bi c0ex 1ex elpr2 reximdva
      orcomd ord mpd r19.29af2 eqcomd ifeqda ) ADJKZFBLZJMUABCENZAWHJMWIAWHOZWI
      BJENZJWJBCJECJKZEBLWHAWLWGEFBEPZFPZKZCDJGUBUCUDUEAWKJKZWHABUFQZWPHBMUGUHU
      IWQWPBEMUJUKULRUMAWHURZOZWIMWSDMKZWIMKZFBAWRFAFUNWHFWGFBUOUPUQXAFUNWSWNBQ
      ZOZWTOBCDEWNGWSWQXBWTAWQWRHRUSXCWMBQZCSQZWTWSXDXEXBAXDXEWRAXDOMJUTZSCXFVA
      SVBVCVDIVETTTWSXBWTVFXCWTVGVHWSWGURZFBVIZWTFBVIZXHWRAWGFBVJUDAXHXIVKWRAXG
      WTFBAXBOZWGWTXJWTWGXJDXFQZWTWGVLAXKFBACXFQZEBLXKFBLAXLEBIVMXLXKEFBWOCDXFG
      VNUCVOVPDMJVQVRVSVOWAWBVTRWCWDWEWFWE $.
  $}

  ${
    $d A k $.  $d B k $.  $d C k $.  $d E k $.  $d F k $.  $d G k $.  $d V k $.
    $d W k $.  $d X k $.  $d ph k $.
    prodpr.1 $e |- ( k = A -> D = E ) $.
    prodpr.2 $e |- ( k = B -> D = F ) $.
    prodpr.a $e |- ( ph -> A e. V ) $.
    prodpr.b $e |- ( ph -> B e. W ) $.
    prodpr.e $e |- ( ph -> E e. CC ) $.
    prodpr.f $e |- ( ph -> F e. CC ) $.
    prodpr.3 $e |- ( ph -> A =/= B ) $.
    $( A product over a pair is the product of the elements.  (Contributed by
       Thierry Arnoux, 1-Jan-2022.) $)
    prodpr $p |- ( ph -> prod_ k e. { A , B } D = ( E x. F ) ) $=
      ( cprod wceq wcel cc cpr csn cmul co wne cin c0 disjsn2 syl cun df-pr a1i
      cfn prfi cv wo vex elpr wa adantl adantr eqeltrd jaodan fprodsplit prodsn
      sylan2b syl2anc oveq12d eqtrd ) ABCUAZDEQBUBZDEQZCUBZDEQZUCUDFGUCUDAVKVMD
      VJEABCUEVKVMUFUGRPBCUHUIVJVKVMUJRABCUKULVJUMSABCUNULEUOZVJSAVOBRZVOCRZUPD
      TSZVOBCEUQURAVPVRVQAVPUSDFTVPDFRAJUTAFTSZVPNVAVBAVQUSDGTVQDGRAKUTAGTSZVQO
      VAVBVCVFVDAVLFVNGUCABHSVSVLFRLNDFEBHJVEVGACISVTVNGRMODGECIKVEVGVHVI $.

    prodtp.1 $e |- ( k = C -> D = G ) $.
    prodtp.c $e |- ( ph -> C e. X ) $.
    prodtp.g $e |- ( ph -> G e. CC ) $.
    prodtp.2 $e |- ( ph -> A =/= C ) $.
    prodtp.3 $e |- ( ph -> B =/= C ) $.
    $( A product over a triple is the product of the elements.  (Contributed by
       Thierry Arnoux, 1-Jan-2022.) $)
    prodtp $p |- ( ph -> prod_ k e. { A , B , C } D = ( ( E x. F ) x. G ) ) $=
      ( ctp cprod cpr csn cmul co wne cin c0 disjprsn syl2anc cun df-tp a1i cfn
      wceq wcel tpfi cv w3o cc vex eltp adantl adantr eqeltrd adantlr mpjao3dan
      wa simpr sylan2b fprodsplit prodpr prodsn oveq12d eqtrd ) ABCDUEZEFUFBCUG
      ZEFUFZDUHZEFUFZUIUJGHUIUJZIUIUJAWBWDEWAFABDUKCDUKWBWDULUMUTUCUDBCDUNUOWAW
      BWDUPUTABCDUQURWAUSVAABCDVBURFVCZWAVAAWGBUTZWGCUTZWGDUTZVDZEVEVAZWGBCDFVF
      VGAWKVMWHWLWIWJAWHWLWKAWHVMEGVEWHEGUTAMVHAGVEVAWHQVIVJVKAWIWLWKAWIVMEHVEW
      IEHUTANVHAHVEVAWIRVIVJVKAWJWLWKAWJVMEIVEWJEIUTATVHAIVEVAZWJUBVIVJVKAWKVNV
      LVOVPAWCWFWEIUIABCEFGHJKMNOPQRSVQADLVAWMWEIUTUAUBEIFDLTVRUOVSVT $.
  $}

  ${
    $d A k $.  $d D k $.  $d K k $.  $d k ph $.
    fsumub.1 $e |- ( k = K -> B = D ) $.
    fsumub.2 $e |- ( ph -> A e. Fin ) $.
    fsumub.3 $e |- ( ph -> sum_ k e. A B = C ) $.
    fsumub.4 $e |- ( ( ph /\ k e. A ) -> B e. RR+ ) $.
    fsumub.k $e |- ( ph -> K e. A ) $.
    $( An upper bound for a term of a positive finite sum.  (Contributed by
       Thierry Arnoux, 27-Dec-2021.) $)
    fsumub $p |- ( ph -> D <_ C ) $=
      ( csu cle cv wcel wa rpred rpge0d fsumge1 breqtrd ) AEBCFMDNABCEFGIAFOBPQ
      ZCKRUBCKSHLTJUA $.
  $}

  ${
    $d A f k l x y z $.  $d B f k l y z $.  $d C f x y z $.
    $d ph f k l x y z $.
    fsumiunle.1 $e |- ( ph -> A e. Fin ) $.
    fsumiunle.2 $e |- ( ( ph /\ x e. A ) -> B e. Fin ) $.
    fsumiunle.3 $e |- ( ( ( ph /\ x e. A ) /\ k e. B ) -> C e. RR ) $.
    fsumiunle.4 $e |- ( ( ( ph /\ x e. A ) /\ k e. B ) -> 0 <_ C ) $.
    $( Upper bound for a sum of nonnegative terms over an indexed union.  The
       inequality may be strict if the indexed union is non-disjoint, since in
       the right hand side, a summand may be counted several times.
       (Contributed by Thierry Arnoux, 1-Jan-2021.) $)
    fsumiunle $p |- ( ph ->
        sum_ k e. U_ x e. A B C <_ sum_ x e. A sum_ k e. B C ) $=
      ( vy cfv wceq wa csu cle cfn nfcv wcel syl2anc vf vl vz ciun cv wf1o c2nd
      crn wral csn cxp wss wbr wf1 wex aciunf1 f1f1orn anim1i frnd adantr eximi
      f1f jca syl csb csbeq1a nfcsb1v cbvsum ccnv csbeq1 snfi sylancr ralrimiva
      xpfi iunfi simprr ssfid simprl f1ocnv adantrlr nfv nfiu1 nfrn nfralw nfan
      nff1o nfss fveq2d simplr simp-4r simpld simprd ad2antrr 2fveq3 id eqeq12d
      simpr rspcva eqtr3d f1ocnvfv1 3eqtr2rd wrex f1ofn simpllr fvelrnb r19.29a
      wfn biimpa sselda eliun sylib r19.29af cc nfel nfim eleq1w anbi2d imbi12d
      wi eleq1d cr adantllr bilani chvarfv adantlr fsumf1o eqtrid eqcomd adantl
      recnd xp2nd nfel1 rspc imp cc0 c1st xp1st elsni simplll vex sylan2 breq2d
      fsumless eqbrtrrd a1i sumeq2sdv cop op2ndd csbeq1d anasss fsum2d breqtrrd
      nfbr eqtrd exlimddv ) ABCDUDZUAUEZUHZUUQUFZUBUEZUUQLUGLZUUTMZUBUUPUIZNZUU
      RBCBUEZUJZDUKZUDZULZNZUUPEFOZCDEFOZBOZPUMUAAUUPUVHUUQUNZUVCNZUAUOUVJUAUOA
      CDUABUBQQGHUPUVOUVJUAUVOUVDUVIUVNUUSUVCUUPUVHUUQUQURUVNUVIUVCUVNUUPUVHUUQ
      UUPUVHUUQVBUSUTVCVAVDAUVJNZUVKUVHFUCUEZUGLZEVEZUCOZUVMPUVPUURUVSUCOZUVKUV
      TPUVPUVKUWAUVPUVKUUPFKUEZEVEZKOUWAUUPEUWCFKFUWBEVFZKERZFUWBEVGZVHUVPUUPUW
      CUURUVSKUCUUQVIZUVRFUWBUVREVJUVPUVHUURAUVHQSZUVJACQSUVGQSZBCUIUWHGAUWIBCA
      UVECSZNZUVFQSDQSUWIUVEVKHUVFDVNVLVMBCUVGVOTUTZAUVDUVIVPZVQAUUSUVIUURUUPUW
      GUFZUVCAUUSUVINNUUSUWNAUUSUVIVRUUPUURUUQVSVDVTUVPUVQUURSZNZUVQUVGSZUVQUWG
      LZUVRMZBCUVPUWOBAUVJBABWAZUVDUVIBUUSUVCBBUUPUURUUQBUUQRZBCDWBZBUUQUXAWCWF
      UVBBUBUUPUXBUVBBWAWDWEBUURUVHBUURRBCUVGWBZWGWEWEUWOBWAWEUWPUWJNUWQNZFUEZU
      UQLZUVQMZUWSFUUPUXDUXEUUPSZNZUXGNZUVRUXEUXFUWGLZUWRUXJUXFUGLZUVRUXEUXJUXF
      UVQUGUXIUXGWQZWHUXJUXHUVCUXLUXEMZUXDUXHUXGWIZUXDUVCUXHUXGUXDUUSUVCUXDUVDU
      VIAUVJUWOUWJUWQWJWKZWLWMUVBUXNUBUXEUUPUUTUXEMZUVAUXLUUTUXEUUTUXEUGUUQWNUX
      QWOWPWRTWSUXJUUSUXHUXKUXEMUXDUUSUXHUXGUXDUUSUVCUXPWKZWMUXOUUPUURUXEUUQWTT
      UXJUXFUVQUWGUXMWHXAUXDUUQUUPXGZUWOUXGFUUPXBZUXDUUSUXSUXRUUPUURUUQXCVDUVPU
      WOUWJUWQXDUXSUWOUXTFUUPUVQUUQXEXHTXFUWPUVQUVHSZUWQBCXBZUVPUURUVHUVQUWMXIB
      UVQCUVGXJZXKXLAUWBUUPSZUWCXMSZUVJAUXHNZEXMSZXSAUYDNZUYEXSFKUYHUYEFUYHFWAF
      UWCXMUWFFXMRXNXOUXEUWBMZUYFUYHUYGUYEUYIUXHUYDAFKUUPXPXQUYIEUWCXMUWDXTZXRU
      YFUXEDSZUYGBCAUXHBUWTBUXEUUPBUXERUXBXNWEUYFUWJNUYKNEAUWJUYKEYASZUXHIYBYJU
      XHUYKBCXBABUXECDXJYCXLYDYEYFYGYHUVPUVHUVSUURUCUWLAUYAUVSYASZUVJAUYANZUWQU
      YMBCAUYABUWTBUVQUVHBUVQRUXCXNWEZUYNUWJNZUWQNZUVRDSZUYLFDUIZUYMUWQUYRUYPUV
      QUVFDYKZYIZUYPUYSUWQAUWJUYSUYAUWKUYLFDIVMYEUTUYRUYSUYMUYLUYMFUVRDFUVSYAFU
      VREVGZYLUXEUVRMZEUVSYAFUVREVFZXTYMYNTUYAUYBAUYCYCZXLYEAUYAYOUVSPUMZUVJUYN
      UWQVUFBCUYOUYQUYRYOEPUMZFDUIZVUFVUAUWQUYPUVQYPLZUVEMZUYRNZVUHUWQVUJUYRUWQ
      VUIUVFSVUJUVQUVFDYQVUIUVEYRVDUYTVCUYPVUKNAUWJVUHAUYAUWJVUKYSUYNUWJVUKWIUW
      KVUGFDJVMTUUAUYRVUHVUFVUGVUFFUVRDFYOUVSPFYORFPRVUBUUMVUCEUVSYOPVUDUUBYMYN
      TVUEXLYEUWMUUCUUDAUVMUVTMUVJAUVMCDUWCKOZBOUVTACUVLVULBUVLVULMADEUWCFKUWDU
      WEUWFVHUUEUUFAUCCDUWCUVSBKUVQUVEUWBUUGMZUWCUVSVUMFUWBUVREVUMUVRUWBUVEUWBU
      VQBYTKYTUUHYHUUIYHGHAUWJUWBDSZUYEUWKUYKNZUYGXSUWKVUNNZUYEXSFKVUPUYEFVUPFW
      AFUWCXMUWFYLXOUYIVUOVUPUYGUYEUYIUYKVUNUWKFKDXPXQUYJXRVUOEIYJYDUUJUUKUUNUT
      UULUUO $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Decimal numbers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    dfdec100.a $e |- A e. NN0 $.
    dfdec100.b $e |- B e. NN0 $.
    dfdec100.c $e |- C e. RR $.
    $( Split the hundreds from a decimal value.  (Contributed by Thierry
       Arnoux, 25-Dec-2021.) $)
    dfdec100 $p |- ; ; A B C = ( ( ; ; 1 0 0 x. A ) + ; B C ) $=
      ( c1 cc0 cmul co caddc dfdec10 oveq2i cc 10nn0 dec0u nn0cni mulcli oveq1i
      cdc eqeltrri recni addassi adddii mulassi eqtr3i 3eqtri eqtr2i 3eqtr2ri )
      GHTZHTZAIJZBCTZKJULUJBIJZCKJZKJULUNKJZCKJZABTZCTZUMUOULKBCLMULUNCUKAUJUJI
      JZUKNUJOPZUJUJUJOQZVBRUAADQZRUJBVBBEQZRCFUBUCUSUJURIJZCKJUQURCLVEUPCKVEUJ
      UJAIJZBKJZIJUJVFIJZUNKJUPURVGUJIABLMUJVFBVBUJAVBVCRVDUDVHULUNKUTAIJVHULUJ
      UJAVBVBVCUEUTUKAIVASUFSUGSUHUI $.
  $}

