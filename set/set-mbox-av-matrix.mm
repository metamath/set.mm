$[ set-main.mm $]
$[ set-mbox-so.mm $]
$[ set-typeset.mm $]
$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Monoids (extension)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Auxiliary theorems
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( If a class operation value for two operands is not the empty set, then the
     operands are contained in the domain of the class, and the class
     restricted to the operands is a function, analogous to ~ fvfundmfvn0 .
     (Contributed by AV, 27-Jan-2020.) $)
  ovn0dmfun $p |- ( ( A F B ) =/= (/)
               -> ( <. A , B >. e. dom F /\ Fun ( F |` { <. A , B >. } ) ) ) $=
    ( co c0 wne cop cfv cdm wcel csn cres wfun df-ov neeq1i fvfundmfvn0 sylbi
    wa ) ABCDZEFABGZCHZEFTCIJCTKLMRSUAEABCNOTCPQ $.

  ${
    $d C a b $.  $d X a b $.
    $( A Cartesian product with a singleton expressed as ordered-pair class
       abstraction.  (Contributed by AV, 27-Jan-2020.) $)
    xpsnopab $p |- ( { X } X. C ) = { <. a , b >. | ( a = X /\ b e. C ) } $=
      ( csn cxp cv wcel wa copab wceq df-xp velsn anbi1i opabbii eqtri ) BEZAFC
      GZQHZDGAHZIZCDJRBKZTIZCDJCDQALUAUCCDSUBTCBMNOP $.
  $}

  ${
    $d B x $.  $d C a b x $.
    $( A Cartesian product expressed as indexed union of ordered-pair class
       abstractions.  (Contributed by AV, 27-Jan-2020.) $)
    xpiun $p |- ( B X. C ) = U_ x e. B { <. a , b >. | ( a = x /\ b e. C ) } $=
      ( weq cv wcel wa ciun csn cxp wceq xpsnopab eqcomi a1i iuneq2i iunxpconst
      copab eqtr2i ) ABDAFEGCHIDESZJABAGZKCLZJBCLABUAUCUAUCMUBBHUCUACUBDENOPQAB
      CRT $.
  $}

  $( The domain of the domain of a function over a Cartesian square.
     (Contributed by AV, 13-Jan-2020.) $)
  fnxpdmdm $p |- ( F Fn ( A X. A ) -> dom dom F = A ) $=
    ( cxp wfn cdm wceq fndm dmeq dmxpid eqtrdi syl ) BAACZDBEZLFZMEZAFLBGNOLEAM
    LHAIJK $.

  ${
    cnfldsrngbas.r $e |- R = ( CCfld |`s S ) $.
    $( The base set of a subring of the field of complex numbers.  (Contributed
       by AV, 31-Jan-2020.) $)
    cnfldsrngbas $p |- ( S C_ CC -> S = ( Base ` R ) ) $=
      ( cc ccnfld cnfldbas ressbas2 ) BDAECFG $.

    $( The group addition operation of a subring of the field of complex
       numbers.  (Contributed by AV, 31-Jan-2020.) $)
    cnfldsrngadd $p |- ( S e. V -> + = ( +g ` R ) ) $=
      ( caddc ccnfld cnfldadd ressplusg ) BEFACDGH $.

    $( The ring multiplication operation of a subring of the field of complex
       numbers.  (Contributed by AV, 31-Jan-2020.) $)
    cnfldsrngmul $p |- ( S e. V -> x. = ( .r ` R ) ) $=
      ( ccnfld cmul cnfldmul ressmulr ) BEAFCDGH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Magmas, Semigroups and Monoids (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d B p x y $.  $d .+ p x y $.  $d .+^ p x y $.
    plusfreseq.1 $e |- B = ( Base ` M ) $.
    plusfreseq.2 $e |- .+ = ( +g ` M ) $.
    plusfreseq.3 $e |- .+^ = ( +f ` M ) $.
    $( If the empty set is not contained in the range of the group addition
       function of an extensible structure (not necessarily a magma), the
       restriction of the addition operation to (the Cartesian square of) the
       base set is the functionalization of it.  (Contributed by AV,
       28-Jan-2020.) $)
    plusfreseq $p |- ( (/) e/ ran .+^ -> ( .+ |` ( B X. B ) ) = .+^ ) $=
      ( vp vx vy cv cfv wceq wral ax-mp a1i co wcel eqcomd fveq2 wnel wfun cres
      c0 crn cxp wfn plusffn fnfun id wa plusfval rgen2 cop df-ov eqtr4di ralxp
      eqeq12d sylibr cdm fndm fveqressseq syl3anc ) UDCUEUAZCUBZVDHKZBLZVFCLZMZ
      HAAUFZNZBVJUCCMVEVDCVJUGZVEACDEGUHZVJCUIOPVDUJVDIKZJKZBQZVNVOCQZMZJANIANZ
      VKVSVDVRIJAAVNARVOARUKVQVPABCDVNVOEFGULSUMPVIVRHIJAAVFVNVOUNZMZVGVPVHVQWA
      VGVTBLVPVFVTBTVNVOBUOUPWAVHVTCLVQVFVTCTVNVOCUOUPURUQUSHBCVJVLVJCUTZMVMVLW
      BVJVJCVASOVBVC $.

    $( If the empty set is not contained in the base set of a magma, the
       restriction of the addition operation to (the Cartesian square of) the
       base set is the functionalization of it.  (Contributed by AV,
       28-Jan-2020.) $)
    mgmplusfreseq $p |- ( ( M e. Mgm /\ (/) e/ B )
                          -> ( .+ |` ( B X. B ) ) = .+^ ) $=
      ( cmgm wcel c0 wnel wa crn cxp cres wceq wf wss wi mgmplusf ssel nelcon3d
      frn 3syl imp plusfreseq syl ) DHIZJAKZLJCMZKZBAANZOCPUHUIUKUHULACQUJARZUI
      UKSACDEGTULACUCUMJUJJAUJAJUAUBUDUEABCDEFGUFUG $.
  $}

  ${
    $d M x y $.
    0mgm.b $e |- ( Base ` M ) = (/) $.
    $( A set with an empty base set is always a magma.  (Contributed by AV,
       25-Feb-2020.) $)
    0mgm $p |- ( M e. V -> M e. Mgm ) $=
      ( vx vy wcel cmgm cv cplusg cfv co wral ral0 cbs eqcomi eqid ismgm mpbiri
      c0 ) ABFAGFDHEHAIJZKSFESLZDSLUADMDESABTANJSCOTPQR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Examples and counterexamples for magmas, semigroups and monoids (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d B a b e x y $.  $d C a b e $.  $d M a b e x $.  $d ph a b x y $.
    opmpoismgm.b $e |- B = ( Base ` M ) $.
    opmpoismgm.p $e |- ( +g ` M ) = ( x e. B , y e. B |-> C ) $.
    opmpoismgm.n $e |- ( ph -> B =/= (/) ) $.
    opmpoismgm.c $e |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> C e. B ) $.
    $( A structure with a group addition operation in maps-to notation is a
       magma if the operation value is contained in the base set.  (Contributed
       by AV, 16-Feb-2020.) $)
    opmpoismgm $p |- ( ph -> M e. Mgm ) $=
      ( va vb ve cmgm wcel cv cmpo wral wa ralrimivva adantr simprl simprr eqid
      co ovmpoelrn syl3anc c0 wne wb wex n0 cplusg eqcomi ismgmn0 exlimiv sylbi
      cfv syl mpbird ) AFNOZKPZLPZBCDDEQZUEDOZLDRKDRZAVEKLDDAVBDOZVCDOZSZSEDOZC
      DRBDRZVGVHVEAVKVIAVJBCDDJTUAAVGVHUBAVGVHUCBCDDEDVDVBVCVDUDUFUGTADUHUIZVAV
      FUJZIVLMPZDOZMUKVMMDULVOVMMKLVNDFVDGFUMURVDHUNUOUPUQUSUT $.
  $}

  ${
    $d B a b c x y $.  $d C a b c x y $.  $d M a b c x $.  $d ph a b c x y $.
    copissgrp.b $e |- B = ( Base ` M ) $.
    copissgrp.p $e |- ( +g ` M ) = ( x e. B , y e. B |-> C ) $.
    copissgrp.n $e |- ( ph -> B =/= (/) ) $.
    copissgrp.c $e |- ( ph -> C e. B ) $.
    $( A structure with a constant group addition operation is a semigroup if
       the constant is contained in the base set.  (Contributed by AV,
       16-Feb-2020.) $)
    copissgrp $p |- ( ph -> M e. Smgrp ) $=
      ( va vb vc wcel cv co wceq wa eqidd weq cmgm cmpo csgrp adantr opmpoismgm
      wral simpl simpr3 ovmpod simpr1 eqtr4d sylan simpr2 oveq1d oveq2d 3eqtr4d
      w3a ralrimivvva cplusg cfv eqcomi issgrp sylanbrc ) AFUANKOZLOZBCDDEUBZPZ
      MOZVFPZVDVEVHVFPZVFPZQZMDUFLDUFKDUFFUCNABCDEFGHIAEDNZBOZDNCOZDNRJUDUEAVLK
      LMDDDAVDDNZVEDNZVHDNZUQZRZEVHVFPZVDEVFPZVIVKAVMVSWAWBQJVMVSRZWAEWBWCBCEVH
      DDEEVFDWCVFSZWCVNEQCMTZRRESVMVSUGZVMVPVQVRUHWFUIWCBCVDEDDEEVFDWDWCBKTZVOE
      QRRESVMVPVQVRUJWFWFUIUKULVTVGEVHVFVTBCVDVEDDEEVFDVTVFSZVTWGCLTRRESAVPVQVR
      UJAVPVQVRUMZAVMVSJUDZUIUNVTVJEVDVFVTBCVEVHDDEEVFDWHVTBLTWERRESWIAVPVQVRUH
      WJUIUOUPURKLMDFVFGFUSUTVFHVAVBVC $.
  $}

  ${
    $d B a c x y $.  $d C a c x y $.  $d M a c $.  $d ph a c x y $.
    copisnmnd.b $e |- B = ( Base ` M ) $.
    copisnmnd.p $e |- ( +g ` M ) = ( x e. B , y e. B |-> C ) $.
    copisnmnd.c $e |- ( ph -> C e. B ) $.
    copisnmnd.n $e |- ( ph -> 1 < ( # ` B ) ) $.
    $( A structure with a constant group addition operation and at least two
       elements is not a monoid.  (Contributed by AV, 16-Feb-2020.) $)
    copisnmnd $p |- ( ph -> M e/ Mnd ) $=
      ( va vc wrex wral wcel wa simpr wceq wn adantr cv cmpo co cmnd wnel chash
      wne cfv clt wbr cvv cbs fvexi a1i simpl hashgt12el2 syl3anc rexbii rexnal
      c1 df-ne bitri eqidd weq ovmpod eqtr3d ex ralimdva rexlimdva con3d bicomi
      ralbii ralnex 3bitr3i imbitrdi biimtrid syl5 mp2and cplusg eqcomi isnmnd
      syl ) AKUAZLUAZBCDDEUBZUCZWDUGZLDMZKDNZFUDUEAEDOZUTDUFUHUIUJZWIIJWJWKPZEW
      DUGZLDMZAWIWLDUKOZWKWJWNWOWLDFULGUMUNWJWKQWJWKUOEDUKLUPUQWNEWDRZLDNZSZAWI
      WNWPSZLDMWRWMWSLDEWDVAURWPLDUSVBAWRWFWDRZLDNZKDMZSZWIAXBWQAXAWQKDAWCDOZPZ
      WTWPLDXEWDDOZPZWTWPXGWTPWFEWDXGWFERWTXGBCWCWDDDEEWEDXGWEVCXGBKVDCLVDPPEVC
      XEXDXFAXDQTXEXFQXEWJXFAWJXDITTVETXGWTQVFVGVHVIVJXASZKDNWTSZLDMZKDNXCWIXHX
      JKDXJXHWTLDUSVKVLXAKDVMXJWHKDXIWGLDWGXIWFWDVAVKURVLVNVOVPVQVRLKDFWEGFVSUH
      WEHVTWAWB $.
  $}

  ${
    $d x z $.
    oddinmgm.e $e |- O = { z e. ZZ | E. x e. ZZ z = ( ( 2 x. x ) + 1 ) } $.
    $( 0 is not an odd integer.  (Contributed by AV, 3-Feb-2020.) $)
    0nodd $p |- 0 e/ O $=
      ( cc0 wcel cz c2 cv co c1 wceq wrex cneg cdiv eqcom cc 2ne0 w3a a1i caddc
      cmul halfnz eleq1 mtbii znegcl nsyl3 sylnibr wne ax-1cn 2cn divneg eqcomd
      wa mp3an eqeq1d halfcn zcn negcon1d bitrd mtbird 2cnd divmul2d mtbid cmin
      neg1cn 0cnd 1cnd mulcld subadd2 bicomd syl3anc df-neg eqcomi 3bitrd eqeq1
      wb nrex intnan rexbidv elrab2 mtbir nelir ) ECECFEGFZEHAIZUBJZKUAJZLZAGMZ
      UNWIWDWHAGWEGFZWHKNZWFLZWJWKHOJZWELZWLWJWNWENZKHOJZLZWJWPWOLZWQWRWOGFZWJW
      RWPGFWSUCWPWOGUDUEWEUFUGWOWPPUHWJWNWPNZWELWQWJWMWTWEWMWTLZWJKQFZHQFZHEUIZ
      XAUJUKRXBXCXDSWTWMKHULUMUOTUPWJWPWEWPQFWJUQTWEURZUSUTVAWJWKWEHWKQFWJVFTXE
      WJVBZXDWJRTVCVDWJWHWGELZEKVEJZWFLZWLWHXGVQWJEWGPTWJEQFZXBWFQFZXGXIVQWJVGW
      JVHWJHWEXFXEVIXJXBXKSXIXGEKWFVJVKVLWJXHWKWFXHWKLWJWKXHKVMVNTUPVOVAVRVSBIZ
      WGLZAGMWIBEGCXLELXMWHAGXLEWGVPVTDWAWBWC $.

    $( 1 is an odd integer.  (Contributed by AV, 3-Feb-2020.) $)
    1odd $p |- 1 e. O $=
      ( c1 wcel cz c2 cv cmul co caddc wceq wrex 1z cc0 0z id wb oveq2 rspcedvd
      2t0e0 eqtrdi oveq1d eqeq2d adantl 1e0p1 a1i ax-mp rexbidv elrab2 mpbir2an
      eqeq1 ) ECFEGFEHAIZJKZELKZMZAGNZOPGFZURQUSUQEPELKZMZAPGUSRUNPMZUQVASUSVBU
      PUTEVBUOPELVBUOHPJKPUNPHJTUBUCUDUEUFVAUSUGUHUAUIBIZUPMZAGNURBEGCVCEMVDUQA
      GVCEUPUMUJDUKUL $.

    $( 2 is not an odd integer.  (Contributed by AV, 3-Feb-2020.) $)
    2nodd $p |- 2 e/ O $=
      ( c2 wcel cz cv cmul co c1 caddc wceq wrex wa cdiv halfnz a1i wb cc eleq1
      mtbii con2i 1cnd zcn 2cnd cc0 wne 2ne0 divmul2d mtbid cmin mulcld subadd2
      eqcom bicomd syl3anc 2m1e1 eqeq1d 3bitrd mtbird nrex intnan eqeq1 rexbidv
      w3a elrab2 mtbir nelir ) ECECFEGFZEEAHZIJZKLJZMZAGNZOVOVJVNAGVKGFZVNKVLMZ
      VPKEPJZVKMZVQVSVPVSVRGFVPQVRVKGUAUBUCVPKVKEVPUDZVKUEZVPUFZEUGUHVPUIRUJUKV
      PVNVMEMZEKULJZVLMZVQVNWCSVPEVMUORVPETFZKTFZVLTFZWCWESWBVTVPEVKWBWAUMWFWGW
      HVFWEWCEKVLUNUPUQVPWDKVLWDKMVPURRUSUTVAVBVCBHZVMMZAGNVOBEGCWIEMWJVNAGWIEV
      MVDVEDVGVHVI $.

    oddinmgm.r $e |- M = ( CCfld |`s O ) $.
    $( Lemma 1 for ~ oddinmgm :  The base set of M is the set of all odd
       integers.  (Contributed by AV, 3-Feb-2020.) $)
    oddibas $p |- O = ( Base ` M ) $=
      ( cc wss cbs cfv wceq cz cv c2 cmul co c1 caddc wrex crab ssrab2 eqsstri
      zsscn sstri cnfldsrngbas ax-mp ) DGHDCIJKDLGDBMNAMOPQRPKALSZBLTLEUGBLUAUB
      UCUDCDFUEUF $.

    $( Lemma 2 for ~ oddinmgm :  The group addition operation of M is the
       addition of complex numbers.  (Contributed by AV, 3-Feb-2020.) $)
    oddiadd $p |- + = ( +g ` M ) $=
      ( cvv wcel caddc cplusg cfv wceq cv c2 cmul co c1 cz wrex zex rabex2
      cnfldsrngadd ax-mp ) DGHICJKLBMNAMOPQIPLARSBRDETUACDGFUBUC $.

    $( The structure of all odd integers together with the addition of complex
       numbers is not a magma.  Remark: the structure of the complementary
       subset of the set of integers, the even integers, is a magma, actually
       an abelian group, see ~ 2zrngaabl , and even a non-unital ring, see
       ~ 2zrng .  (Contributed by AV, 3-Feb-2020.) $)
    oddinmgm $p |- M e/ Mgm $=
      ( c1 wcel caddc co wnel cmgm 1odd c2 2nodd wceq wb 1p1e2 neleq1 ax-mp
      mpbir oddibas oddiadd isnmgm mp3an ) GDHZUFGGIJZDKZCLKABDEMZUIUHNDKZABDEO
      UGNPUHUJQRUGNDSTUADCGGIABCDEFUBABCDEFUCUDUE $.
  $}

  ${
    $d M x y $.
    nnsgrp.m $e |- M = ( CCfld |`s NN ) $.
    $( The structure of positive integers together with the addition of complex
       numbers is a magma.  (Contributed by AV, 4-Feb-2020.) $)
    nnsgrpmgm $p |- M e. Mgm $=
      ( vx vy c1 cn wcel cmgm 1nn cv caddc co wral nnaddcl rgen2 cfv wceq ax-mp
      cc cvv wss nnsscn cnfldsrngbas cplusg nnex cnfldsrngadd ismgmn0 mpbiri
      cbs ) EFGZAHGZIUJUKCJZDJZKLFGZDFMCFMUNCDFFULUMNOCDEFAKFSUAFAUIPQUBAFBUCRF
      TGKAUDPQUEAFTBUFRUGUHR $.

    $d M x y z $.
    $( The structure of positive integers together with the addition of complex
       numbers is a semigroup.  (Contributed by AV, 4-Feb-2020.) $)
    nnsgrp $p |- M e. Smgrp $=
      ( vx vy vz csgrp wcel cmgm cv caddc co wceq cn wral nnsgrpmgm cc nncn cfv
      ax-mp cvv addass syl3an 3expia ralrimiv rgen2 wss cbs nnsscn cnfldsrngbas
      wa cplusg nnex cnfldsrngadd issgrp mpbir2an ) AFGAHGCIZDIZJKEIZJKUPUQURJK
      JKLZEMNZDMNCMNABOUTCDMMUPMGZUQMGZUJUSEMVAVBURMGZUSVAUPPGVBUQPGVCURPGUSUPQ
      UQQURQUPUQURUAUBUCUDUECDEMAJMPUFMAUGRLUHAMBUISMTGJAUKRLULAMTBUMSUNUO $.

    $( The structure of positive integers together with the addition of complex
       numbers is not a monoid.  (Contributed by AV, 4-Feb-2020.) $)
    nnsgrpnmnd $p |- M e/ Mnd $=
      ( vz vx cv caddc co wne cn wrex cmnd wnel cfv wceq ax-mp cvv wcel a1i cc0
      c1 cc wss cbs nnsscn cnfldsrngbas cplusg cnfldsrngadd isnmnd 1nn wb oveq2
      nnex id neeq12d adantl nnne0 necomd cmin 1cnd nncn subadd2d eqeq1d bitr3d
      1m1e0 necon3bid mpbird rspcedvd mprg ) CEZDEZFGZVJHZDIJAKLCIDCIAFIUAUBIAU
      CMNUDAIBUEOIPQFAUFMNULAIPBUGOUHVIIQZVLVITFGZTHZDTITIQVMUIRVJTNZVLVOUJVMVP
      VKVNVJTVJTVIFUKVPUMUNUOVMVOSVIHVMVISVIUPUQVMVNTSVIVMTTURGZVINVNTNSVINVMTT
      VIVMUSZVRVIUTVAVMVQSVIVQSNVMVDRVBVCVEVFVGVH $.
  $}

  ${
    $d M x y z $.  $d e x $.
    nn0mnd.g $e |- M = { <. ( Base ` ndx ) , NN0 >. ,
                         <. ( +g ` ndx ) , + >. } $.
    $( The set of nonnegative integers under (complex) addition is a monoid.
       Example in [Lang] p. 6.  Remark: ` M ` could have also been written as
       ` ( CCfld |``s NN0 ) ` .  (Contributed by AV, 27-Dec-2023.) $)
    nn0mnd $p |- M e. Mnd $=
      ( vx vy vz ve wcel cv caddc co cn0 wceq wral wa nn0cn jca cc0 eqeq1d cvv
      cc cmnd wrex nn0addcl w3a 3anim123i 3expa addass syl ralrimiva rgen2 c0ex
      wex eleq1 oveq1 oveq2 anbi12d ralbidv 0nn0 addlidd addridd rgen ceqsexv2d
      pm3.2i df-rex mpbir cbs nn0ex grpbase ax-mp cplusg addex grpplusg ismnd
      cfv ) AUAGCHZDHZIJZKGZVQEHZIJVOVPVSIJIJLZEKMZNZDKMCKMZFHZVOIJZVOLZVOWDIJZ
      VOLZNZCKMZFKUBZNWCWKWBCDKKVOKGZVPKGZNZVRWAVOVPUCWNVTEKWNVSKGZNVOTGZVPTGZV
      STGZUDZVTWLWMWOWSWLWPWMWQWOWRVOOZVPOVSOUEUFVOVPVSUGUHUIPUJWKWDKGZWJNZFULX
      BQKGZQVOIJZVOLZVOQIJZVOLZNZCKMZNFQUKWDQLZXAXCWJXIWDQKUMXJWIXHCKXJWFXEWHXG
      XJWEXDVOWDQVOIUNRXJWGXFVOWDQVOIUORUPUQUPXCXIURXHCKWLXEXGWLVOWTUSWLVOWTUTP
      VAVCVBWJFKVDVEVCKIFACDEKSGKAVFVNLVGKIASBVHVIISGIAVJVNLVKKIASBVLVIVMVE $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Group sum operation (extension 1)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d k A $.  $d k B $.  $d k C $.  $d k D $.
    gsumsplit2f.n $e |- F/ k ph $.
    gsumsplit2f.b $e |- B = ( Base ` G ) $.
    gsumsplit2f.z $e |- .0. = ( 0g ` G ) $.
    gsumsplit2f.p $e |- .+ = ( +g ` G ) $.
    gsumsplit2f.g $e |- ( ph -> G e. CMnd ) $.
    gsumsplit2f.a $e |- ( ph -> A e. V ) $.
    gsumsplit2f.f $e |- ( ( ph /\ k e. A ) -> X e. B ) $.
    gsumsplit2f.w $e |- ( ph -> ( k e. A |-> X ) finSupp .0. ) $.
    gsumsplit2f.i $e |- ( ph -> ( C i^i D ) = (/) ) $.
    gsumsplit2f.u $e |- ( ph -> A = ( C u. D ) ) $.
    $( Split a group sum into two parts.  (Contributed by AV, 4-Sep-2019.) $)
    gsumsplit2f $p |- ( ph -> ( G gsum ( k e. A |-> X ) ) =
      ( ( G gsum ( k e. C |-> X ) ) .+ ( G gsum ( k e. D |-> X ) ) ) ) $=
      ( cmpt cgsu cres eqid fmptdf gsumsplit cun ssun1 sseqtrrid resmptd oveq2d
      co ssun2 oveq12d eqtrd ) AHGBJUBZUCUMHUQDUDZUCUMZHUQEUDZUCUMZFUMHGDJUBZUC
      UMZHGEJUBZUCUMZFUMABCDEFUQHIKMNOPQAGBJCUQLRUQUEUFSTUAUGAUSVCVAVEFAURVBHUC
      AGBDJADEUHZDBDEUIUAUJUKULAUTVDHUCAGBEJAVFEBEDUNUAUJUKULUOUP $.
  $}

  ${
    $d k A $.  $d k B $.  $d k G $.  $d k M $.
    gsumdifsndf.k $e |- F/_ k Y $.
    gsumdifsndf.n $e |- F/ k ph $.
    gsumdifsndf.b $e |- B = ( Base ` G ) $.
    gsumdifsndf.p $e |- .+ = ( +g ` G ) $.
    gsumdifsndf.g $e |- ( ph -> G e. CMnd ) $.
    gsumdifsndf.a $e |- ( ph -> A e. W ) $.
    gsumdifsndf.f $e |- ( ph -> ( k e. A |-> X ) finSupp ( 0g ` G ) ) $.
    gsumdifsndf.e $e |- ( ( ph /\ k e. A ) -> X e. B ) $.
    gsumdifsndf.m $e |- ( ph -> M e. A ) $.
    gsumdifsndf.y $e |- ( ph -> Y e. B ) $.
    gsumdifsndf.s $e |- ( ( ph /\ k = M ) -> X = Y ) $.
    $( Extract a summand from a finitely supported group sum.  (Contributed by
       AV, 4-Sep-2019.) $)
    gsumdifsndf $p |- ( ph -> ( G gsum ( k e. A |-> X ) )
                        = ( ( G gsum ( k e. ( A \ { M } ) |-> X ) ) .+ Y ) ) $=
      ( cmpt cgsu co csn cdif c0g cfv eqid cin c0 wss wceq snssd difin2 eqtr3di
      syl difid cun wcel difsnid eqcomd gsumsplit2f ccmn cmnmnd gsumsnfd oveq2d
      cmnd eqtrd ) AFEBIUBUCUDFEBGUEZUFZIUBUCUDZFEVJIUBUCUDZDUDVLJDUDABCVKVJDEF
      HIFUGUHZLMVNUINOPRQAVJVJUFZVKVJUJZUKAVJBULVOVPUMAGBSUNVJVJBUOUQVJURUPAVKV
      JUSZBAGBUTVQBUMSBGVAUQVBVCAVMJVLDAICJEFGBMAFVDUTFVHUTOFVEUQSTUALKVFVGVI
      $.
  $}

  ${
    gsumfsupp.b $e |- B = ( Base ` G ) $.
    gsumfsupp.z $e |- .0. = ( 0g ` G ) $.
    gsumfsupp.s $e |- I = ( F supp .0. ) $.
    gsumfsupp.g $e |- ( ph -> G e. CMnd ) $.
    gsumfsupp.a $e |- ( ph -> A e. V ) $.
    gsumfsupp.f $e |- ( ph -> F : A --> B ) $.
    gsumfsupp.w $e |- ( ph -> F finSupp .0. ) $.
    $( A group sum of a family can be restricted to the support of that family
       without changing its value, provided that that support is finite.  This
       corresponds to the definition of an (infinite) product in [Lang] p. 5,
       last two formulas.  (Contributed by AV, 27-Dec-2023.) $)
    gsumfsupp $p |- ( ph -> ( G gsum ( F |` I ) ) = ( G gsum F ) ) $=
      ( csupp co wss eqimss2i a1i gsumres ) ABCDEGFHIJLMNDHPQZFRAFUBKSTOUA $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Magmas and internal binary operations (alternate approach)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  With ~ df-mpo , binary operations are defined by a rule, and with ~ df-ov ,
  the value of a binary operation applied to two operands can be expressed.  In
  both cases, the two operands can belong to different sets, and the result can
  be an element of a third set.  However, according to Wikipedia "Binary
  operation", see ~ https://en.wikipedia.org/wiki/Binary_operation
  (19-Jan-2020), "... a binary operation on a set ` S ` is a mapping of the
  elements of the Cartesian product ` S X. S ` to S: ` f : S X. S --> S `.
  Because the result of performing the operation on a pair of elements of S
  is again an element of S, the operation is called a _closed_ binary operation
  on S (or sometimes expressed as having the property of closure).".  To
  distinguish this more restrictive definition (in Wikipedia and most of the
  literature) from the general case, we call binary operations mapping the
  elements of the Cartesian product ` S X. S ` _internal binary operations_,
  see ~ df-intop .  If, in addition, the result is also contained in the set
  ` S `, the operation is called _closed internal binary operation_, see
  ~ df-clintop .  Therefore, a "binary operation on a set ` S ` " according to
  Wikipedia is a "closed internal binary operation" in our terminology.  If the
  sets are different, the operation is explicitly called _external binary
  operation_ (see Wikipedia
  ~ https://en.wikipedia.org/wiki/Binary_operation#External_binary_operations
  ).

  Taking a step back, we define "laws" applicable for "binary operations"
  (which even need not to be functions), according to the definition in
  [Hall] p. 1 and [BourbakiAlg1] p. 1, p. 4 and p. 7. These laws are used, on
  the one hand, to specialize internal binary operations (see ~ df-clintop and
  ~ df-assintop ), and on the other hand to define the common algebraic
  structures like magmas, groups, rings, etc.  Internal binary operations,
  which obey these laws, are defined afterwards.  Notice that in
  [BourbakiAlg1] p. 1, p. 4 and p. 7, these operations are called "laws" by
  themselves.

  In the following, an alternate definition ~ df-cllaw for an internal binary
  operation is provided, which does not require function-ness, but only
  closure.  Therefore, this definition could be used as binary operation
  (Slot 2) defined for a magma as extensible structure, see ~ mgmplusgiopALT ,
  or for an alternate definition ~ df-mgm2 for a magma as extensible structure.
  Similar results are obtained for an associative operation (defining
  semigroups).

$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Laws for internal binary operations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  In this subsection, the "laws" applicable for "binary operations" according
  to the definition in [Hall] p. 1 and [BourbakiAlg1] p. 1, p. 4 and p. 7 are
  defined.  These laws are called "internal laws" in [BourbakiAlg1] p. xxi.

$)

  $c clLaw $.
  $c assLaw $.
  $c comLaw $.

  $( Extend class notation for the closure law. $)
  ccllaw $a class clLaw $.

  $( Extend class notation for the associative law. $)
  casslaw $a class assLaw $.

  $( Extend class notation for the commutative law. $)
  ccomlaw $a class comLaw $.

  ${
    $d m o x y $.
    $( The closure law for binary operations, see definitions of laws A0. and
       M0. in section 1.1 of [Hall] p. 1, or definition 1 in [BourbakiAlg1]
       p. 1: the value of a binary operation applied to two operands of a given
       sets is an element of this set.  By this definition, the closure law is
       expressed as binary relation: a binary operation is related to a set by
       ` clLaw ` if the closure law holds for this binary operation regarding
       this set.  Note that the binary operation needs not to be a function.
       (Contributed by AV, 7-Jan-2020.) $)
    df-cllaw $a |- clLaw = { <. o , m >. |
                             A. x e. m A. y e. m ( x o y ) e. m } $.

    $( The commutative law for binary operations, see definitions of laws A2.
       and M2. in section 1.1 of [Hall] p. 1, or definition 8 in [BourbakiAlg1]
       p. 7: the value of a binary operation applied to two operands equals the
       value of a binary operation applied to the two operands in reversed
       order.  By this definition, the commutative law is expressed as binary
       relation: a binary operation is related to a set by ` comLaw ` if the
       commutative law holds for this binary operation regarding this set.
       Note that the binary operation needs neither to be closed nor to be a
       function.  (Contributed by AV, 7-Jan-2020.) $)
    df-comlaw $a |- comLaw = { <. o , m >. |
                             A. x e. m A. y e. m ( x o y ) = ( y o x ) } $.
  $}

  ${
    $d m o x y z $.
    $( The associative law for binary operations, see definitions of laws A1.
       and M1. in section 1.1 of [Hall] p. 1, or definition 5 in [BourbakiAlg1]
       p. 4: the value of a binary operation applied the value of the binary
       operation applied to two operands and a third operand equals the value
       of the binary operation applied to the first operand and the value of
       the binary operation applied to the second and third operand.  By this
       definition, the associative law is expressed as binary relation: a
       binary operation is related to a set by ` assLaw ` if the associative
       law holds for this binary operation regarding this set.  Note that the
       binary operation needs neither to be closed nor to be a function.
       (Contributed by FL, 1-Nov-2009.)  (Revised by AV, 13-Jan-2020.) $)
    df-asslaw $a |- assLaw = { <. o , m >. | A. x e. m A. y e. m A. z e. m
                                     ( ( x o y ) o z ) = ( x o ( y o z ) ) } $.
  $}

  ${
    $d M m o x y $.  $d .o. m o x y $.
    $( The predicate "is a closed operation".  (Contributed by AV,
       13-Jan-2020.) $)
    iscllaw $p |- ( ( .o. e. V /\ M e. W )
               -> ( .o. clLaw M <-> A. x e. M A. y e. M ( x .o. y ) e. M ) ) $=
      ( vo vm cv co wcel wral ccllaw wceq simpr oveq adantr eleq12d raleqbidv
      wa df-cllaw brabga ) AIZBIZGIZJZHIZKZBUGLZAUGLUCUDFJZCKZBCLZACLGHFCMDEUEF
      NZUGCNZTZUIULAUGCUMUNOZUOUHUKBUGCUPUOUFUJUGCUMUFUJNUNUCUDUEFPQUPRSSABHGUA
      UB $.

    $( The predicate "is a commutative operation".  (Contributed by AV,
       20-Jan-2020.) $)
    iscomlaw $p |- ( ( .o. e. V /\ M e. W ) -> ( .o. comLaw M
                       <-> A. x e. M A. y e. M ( x .o. y ) = ( y .o. x ) ) ) $=
      ( vo vm cv co wceq wral ccomlaw wa simpr wb oveq eqeq12d adantr raleqbidv
      df-comlaw brabga ) AIZBIZGIZJZUDUCUEJZKZBHIZLZAUILUCUDFJZUDUCFJZKZBCLZACL
      GHFCMDEUEFKZUICKZNZUJUNAUICUOUPOZUQUHUMBUICURUOUHUMPUPUOUFUKUGULUCUDUEFQU
      DUCUEFQRSTTABHGUAUB $.

    $d X x y $.  $d Y x y $.
    $( Closure of a closed operation.  (Contributed by FL, 14-Sep-2010.)
       (Revised by AV, 21-Jan-2020.) $)
    clcllaw $p |- ( ( .o. clLaw M /\ X e. M /\ Y e. M )
                    -> ( X .o. Y ) e. M ) $=
      ( vx vy vo vm ccllaw wbr wcel co wa wi cv wral df-cllaw bropaex12 iscllaw
      cvv ovrspc2v expcom biimtrdi mpcom 3impib ) DAIJZBAKZCAKZBCDLAKZDTKATKMZU
      FUGUHMZUINZEOZFOZGOLHOZKFUOPEUOPGHDAIEFHGQRUJUFUMUNDLAKFAPEAPZULEFATTDSUK
      UPUIEFAAADBCUAUBUCUDUE $.
  $}

  ${
    $d M m o x y z $.  $d .o. m o x y z $.
    $( The predicate "is an associative operation".  (Contributed by FL,
       1-Nov-2009.)  (Revised by AV, 13-Jan-2020.) $)
    isasslaw $p |- ( ( .o. e. V /\ M e. W )
                     -> ( .o. assLaw M <-> A. x e. M A. y e. M A. z e. M
                           ( ( x .o. y ) .o. z ) = ( x .o. ( y .o. z ) ) ) ) $=
      ( vo vm cv co wceq wral casslaw wa simpr oveq eqidd oveq123d raleqbidv wb
      id eqeq12d adantr df-asslaw brabga ) AJZBJZHJZKZCJZUIKZUGUHUKUIKZUIKZLZCI
      JZMZBUPMZAUPMUGUHGKZUKGKZUGUHUKGKZGKZLZCDMZBDMZADMHIGDNEFUIGLZUPDLZOZURVE
      AUPDVFVGPZVHUQVDBUPDVIVHUOVCCUPDVIVFUOVCUAVGVFULUTUNVBVFUJUSUKUKUIGVFUBZU
      GUHUIGQVFUKRSVFUGUGUMVAUIGVJVFUGRUHUKUIGQSUCUDTTTABCIHUEUF $.

    $( Associativity of an associative operation.  (Contributed by FL,
       2-Nov-2009.)  (Revised by AV, 21-Jan-2020.) $)
    asslawass $p |- ( .o. assLaw M -> A. x e. M A. y e. M A. z e. M
                             ( ( x .o. y ) .o. z ) = ( x .o. ( y .o. z ) ) ) $=
      ( vo vm casslaw wbr cv co wceq wral cvv wcel df-asslaw bropaex12 isasslaw
      wa wb syl ibi ) EDHIZAJZBJZEKCJZEKUDUEUFEKEKLCDMBDMADMZUCENODNOSUCUGTUDUE
      FJZKUFUHKUDUEUFUHKUHKLCGJZMBUIMAUIMFGEDHABCGFPQABCDNNERUAUB $.
  $}

$( *** relation to magmas and semirings as defined before. *** $)

  ${
    $d M x y $.
    $( Slot 2 (group operation) of a magma as extensible structure is a closed
       operation on the base set.  (Contributed by AV, 13-Jan-2020.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    mgmplusgiopALT $p |- ( M e. Mgm -> ( +g ` M ) clLaw ( Base ` M ) ) $=
      ( vx vy cmgm wcel cplusg cfv cbs ccllaw wbr cv wral eqid mgmcl ralrimivva
      co 3expb cvv wa fvex wb pm3.2i iscllaw mp1i mpbird ) ADEZAFGZAHGZIJZBKZCK
      ZUGPUHEZCUHLBUHLZUFULBCUHUHUFUJUHEUKUHEULUHAUJUKUGUHMUGMNQOUGREZUHREZSUIU
      MUAUFUNUOAFTAHTUBBCUHRRUGUCUDUE $.
  $}

  ${
    $d G x y z $.
    $( Slot 2 (group operation) of a semigroup as extensible structure is an
       associative operation on the base set.  (Contributed by AV,
       13-Jan-2020.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    sgrpplusgaopALT $p |- ( G e. Smgrp -> ( +g ` G ) assLaw ( Base ` G ) ) $=
      ( vx vy vz cmgm wcel cv cplusg cfv co wceq cbs wral wa csgrp casslaw eqid
      wbr cvv fvex simpr issgrp wb isasslaw mp2an 3imtr4i ) AEFZBGZCGZAHIZJDGZU
      JJUHUIUKUJJUJJKDALIZMCULMBULMZNUMAOFUJULPRZUGUMUABCDULAUJULQUJQUBUJSFULSF
      UNUMUCAHTALTBCDULSSUJUDUEUF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Internal binary operations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  In this subsection, "internal binary operations" obeying different laws are
  defined.

$)

  $c intOp $.
  $c clIntOp $.
  $c assIntOp $.

  $( Extend class notation with class of internal (binary) operations for a
     set. $)
  cintop $a class intOp $.

  $( Extend class notation with class of closed operations for a set. $)
  cclintop $a class clIntOp $.

  $( Extend class notation with class of associative operations for a set. $)
  cassintop $a class assIntOp $.

  ${
    $d m n $.
    $( Function mapping a set to the class of all internal (binary) operations
       for this set.  (Contributed by AV, 20-Jan-2020.) $)
    df-intop $a |- intOp = ( m e. _V , n e. _V |-> ( n ^m ( m X. m ) ) ) $.
  $}

  ${
    $d m o $.
    $( Function mapping a set to the class of all closed (internal binary)
       operations for this set, see definition in section 1.2 of [Hall] p. 2,
       definition in section I.1 of [Bruck] p. 1, or definition 1 in
       [BourbakiAlg1] p. 1, where it is called "a law of composition".
       (Contributed by AV, 20-Jan-2020.) $)
    df-clintop $a |- clIntOp = ( m e. _V |-> ( m intOp m ) ) $.

    $( Function mapping a set to the class of all associative (closed internal
       binary) operations for this set, see definition 5 in [BourbakiAlg1]
       p. 4, where it is called "an associative law of composition".
       (Contributed by AV, 20-Jan-2020.) $)
    df-assintop $a |- assIntOp
                     = ( m e. _V |-> { o e. ( clIntOp ` m ) | o assLaw m } ) $.
  $}

  ${
    $d M m n $.  $d N m n $.  $d V m n $.  $d W m n $.
    $( The internal (binary) operations for a set.  (Contributed by AV,
       20-Jan-2020.) $)
    intopval $p |- ( ( M e. V /\ N e. W )
                     -> ( M intOp N ) = ( N ^m ( M X. M ) ) ) $=
      ( vm vn wcel wa cvv cv cxp cmap cintop cmpo wceq df-intop a1i adantl elex
      co simpr simpl sqxpeqd oveq12d adantr ovexd ovmpod ) ACGZBDGZHZEFABIIFJZE
      JZULKZLTZBAAKZLTZMIMEFIIUNNOUJEFPQULAOZUKBOZHZUNUPOUJUSUKBUMUOLUQURUAUSUL
      AUQURUBUCUDRUHAIGUIACSUEUIBIGUHBDSRUJBUOLUFUG $.

    $( An internal (binary) operation for a set.  (Contributed by AV,
       20-Jan-2020.) $)
    intop $p |- ( .o. e. ( M intOp N ) -> .o. : ( M X. M ) --> N ) $=
      ( vm vn cvv wcel wa cintop co wf cv cmap df-intop elmpocl intopval eleq2d
      cxp elmapi biimtrdi mpcom ) AFGBFGHZCABIJZGZAARZBCKZDEFFELDLZUGRMJABICDEN
      OUBUDCBUEMJZGUFUBUCUHCABFFPQCBUESTUA $.
  $}

  ${
    $d M m $.  $d V m $.
    $( The closed (internal binary) operations for a set.  (Contributed by AV,
       20-Jan-2020.) $)
    clintopval $p |- ( M e. V -> ( clIntOp ` M ) = ( M ^m ( M X. M ) ) ) $=
      ( vm wcel cv cintop co cxp cmap cclintop df-clintop wceq oveq12d intopval
      cvv id anidms sylan9eqr elex ovexd fvmptd2 ) ABDZCACEZUCFGZAAAHZIGZOJOCKU
      CALZUBUDAAFGZUFUGUCAUCAFUGPZUIMUBUHUFLAABBNQRABSUBAUEITUA $.

    $d M m o $.
    $( The associative (closed internal binary) operations for a set.
       (Contributed by AV, 20-Jan-2020.) $)
    assintopval $p |- ( M e. V
               -> ( assIntOp ` M ) = { o e. ( clIntOp ` M ) | o assLaw M } ) $=
      ( vm wcel cv casslaw wbr cclintop cfv crab cvv cassintop df-assintop wceq
      fveq2 breq2 rabeqbidv elex fvex rabex a1i fvmptd3 ) BCEZDBAFZDFZGHZAUFIJZ
      KUEBGHZABIJZKZLMLDANUFBOUGUIAUHUJUFBIPUFBUEGQRBCSUKLEUDUIAUJBITUAUBUC $.

    $( The associative (closed internal binary) operations for a set, expressed
       with set exponentiation.  (Contributed by AV, 20-Jan-2020.) $)
    assintopmap $p |- ( M e. V
           -> ( assIntOp ` M ) = { o e. ( M ^m ( M X. M ) ) | o assLaw M } ) $=
      ( wcel cassintop cfv cv casslaw wbr cclintop crab cxp cmap co assintopval
      clintopval rabeqdv eqtrd ) BCDZBEFAGBHIZABJFZKTABBBLMNZKABCOSTAUAUBBCPQR
      $.
  $}

  $( The predicate "is a closed (internal binary) operations for a set".
     (Contributed by FL, 2-Nov-2009.)  (Revised by AV, 20-Jan-2020.) $)
  isclintop $p |- ( M e. V
                  -> ( .o. e. ( clIntOp ` M ) <-> .o. : ( M X. M ) --> M ) ) $=
    ( wcel cclintop cfv cxp co wf clintopval eleq2d cvv wb sqxpexg elmapg mpdan
    cmap bitrd ) ABDZCAEFZDCAAAGZQHZDZUAACIZSTUBCABJKSUALDUCUDMABNAUACBLOPR $.

  $( A closed (internal binary) operation for a set.  (Contributed by AV,
     20-Jan-2020.) $)
  clintop $p |- ( .o. e. ( clIntOp ` M ) -> .o. : ( M X. M ) --> M ) $=
    ( cvv wcel cclintop cfv cxp wf elfvex isclintop biimpd mpcom ) ACDZBAEFDZAA
    GABHZBAEIMNOACBJKL $.

  ${
    $d M o $.  $d .o. o $.
    $( An associative (closed internal binary) operation for a set.
       (Contributed by AV, 20-Jan-2020.) $)
    assintop $p |- ( .o. e. ( assIntOp ` M )
                     -> ( .o. : ( M X. M ) --> M /\ .o. assLaw M ) ) $=
      ( vo cvv wcel cassintop cfv cxp wf casslaw wbr wa elfvex cmap assintopmap
      cv co crab eleq2d breq1 elrab elmapi anim1i sylbi biimtrdi mpcom ) ADEZBA
      FGZEZAAHZABIZBAJKZLZBAFMUGUIBCPZAJKZCAUJNQZRZEZUMUGUHUQBCADOSURBUPEZULLUM
      UOULCBUPUNBAJTUAUSUKULBAUJUBUCUDUEUF $.
  $}

  ${
    $d M o x y z $.  $d .o. o x y z $.
    $( The predicate "is an associative (closed internal binary) operations for
       a set".  (Contributed by FL, 2-Nov-2009.)  (Revised by AV,
       20-Jan-2020.) $)
    isassintop $p |- ( M e. V -> ( .o. e. ( assIntOp ` M )
                  <-> ( .o. : ( M X. M ) --> M /\ A. x e. M A. y e. M A. z e. M
                         ( ( x .o. y ) .o. z ) = ( x .o. ( y .o. z ) ) ) ) ) $=
      ( vo wcel cfv cv co wceq wral wa casslaw wbr crab eleq2d elrab cvv cxp wf
      cassintop cmap assintopmap breq1 bitrdi elmapi ad2antrl isasslaw impancom
      biimpd impcom jca ex sylbid cclintop wi isclintop biimprcd adantr sqxpexg
      fex sylan2 ancoms simpl bicomd syl2anc impr assintopval mpbir2and impbid
      wb ) DEHZFDUCIZHZDDUAZDFUBZAJZBJZFKCJZFKVSVTWAFKFKLCDMBDMADMZNZVNVPFDVQUD
      KZHZFDOPZNZWCVNVPFGJZDOPZGWDQZHWGVNVOWJFGDEUERWIWFGFWDWHFDOUFZSUGVNWGWCVN
      WGNVRWBWEVRVNWFFDVQUHUIWGVNWBWEVNWFWBWEVNNWFWBABCDWDEFUJULUKUMUNUOUPVNWCV
      PVNWCNZVPFDUQIZHZWFWCVNWNVRVNWNURWBVNWNVRDEFUSUTVAUMVNVRWBWFVNVRNZWBWFWOF
      THZVNWBWFVMVRVNWPVNVRVQTHWPDEVBVQDTFVCVDVEVNVRVFWPVNNWFWBABCDTEFUJVGVHULV
      IWLVPFWIGWMQZHWNWFNWLVOWQFVNVOWQLWCGDEVJVARWIWFGFWMWKSUGVKUOVL $.
  $}

  ${
    $d M x y $.  $d .o. x y $.
    $( The closure law holds for a closed (internal binary) operation for a
       set.  (Contributed by AV, 20-Jan-2020.) $)
    clintopcllaw $p |- ( .o. e. ( clIntOp ` M ) -> .o. clLaw M ) $=
      ( vx vy cclintop cfv wcel ccllaw wbr cv co wral cxp clintop ffnov simprbi
      wf wfn syl cvv wb elfvex iscllaw mpdan mpbird ) BAEFZGZBAHIZCJDJBKAGDALCA
      LZUGAAMZABQZUIABNUKBUJRUICDAAABOPSUGATGUHUIUABAEUBCDAUFTBUCUDUE $.
  $}

  ${
    $d M o $.  $d .o. o $.
    $( The closure low holds for an associative (closed internal binary)
       operation for a set.  (Contributed by FL, 2-Nov-2009.)  (Revised by AV,
       20-Jan-2020.) $)
    assintopcllaw $p |- ( .o. e. ( assIntOp ` M ) -> .o. clLaw M ) $=
      ( vo cvv wcel cassintop cfv ccllaw wbr elfvex cclintop casslaw wa cv crab
      assintopval eleq2d breq1 elrab bitrdi clintopcllaw adantr biimtrdi mpcom
      ) ADEZBAFGZEZBAHIZBAFJUEUGBAKGZEZBALIZMZUHUEUGBCNZALIZCUIOZEULUEUFUOBCADP
      QUNUKCBUIUMBALRSTUJUHUKABUAUBUCUD $.
  $}

  $( The associative low holds for a associative (closed internal binary)
     operation for a set.  (Contributed by FL, 2-Nov-2009.)  (Revised by AV,
     20-Jan-2020.) $)
  assintopasslaw $p |- ( .o. e. ( assIntOp ` M ) -> .o. assLaw M ) $=
    ( cassintop cfv wcel cxp wf casslaw wbr assintop simprd ) BACDEAAFABGBAHIAB
    JK $.

  ${
    $d M x y z $.  $d .o. x y z $.
    $( An associative (closed internal binary) operation for a set is
       associative.  (Contributed by FL, 2-Nov-2009.)  (Revised by AV,
       20-Jan-2020.) $)
    assintopass $p |- ( .o. e. ( assIntOp ` M )
                        -> A. x e. M A. y e. M A. z e. M
                             ( ( x .o. y ) .o. z ) = ( x .o. ( y .o. z ) ) ) $=
      ( cassintop cfv wcel cvv cv co wceq wral id elfvex casslaw assintopasslaw
      wbr wa isasslaw syl5ibcom mp2and ) EDFGZHZUDDIHZAJZBJZEKCJZEKUFUGUHEKEKLC
      DMBDMADMZUDNEDFOUDEDPRUDUESUIDEQABCDUCIETUAUB $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Alternative definitions for magmas and semigroups
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c MgmALT $.
  $c CMgmALT $.
  $c SGrpALT $.
  $c CSGrpALT $.

  $( Extend class notation with class of all magmas. $)
  cmgm2 $a class MgmALT $.

  $( Extend class notation with class of all commutative magmas. $)
  ccmgm2 $a class CMgmALT $.

  $( Extend class notation with class of all semigroups. $)
  csgrp2 $a class SGrpALT $.

  $( Extend class notation with class of all commutative semigroups. $)
  ccsgrp2 $a class CSGrpALT $.

  $( A _magma_ is a set equipped with a closed operation.  Definition 1 of
     [BourbakiAlg1] p. 1, or definition of a groupoid in section I.1 of [Bruck]
     p. 1.  Note:  The term "groupoid" is now widely used to refer to other
     objects:  (small) categories all of whose morphisms are invertible, or
     groups with a partial function replacing the binary operation.  Therefore,
     we will only use the term "magma" for the present notion in set.mm.
     (Contributed by AV, 6-Jan-2020.) $)
  df-mgm2 $a |- MgmALT = { m | ( +g ` m ) clLaw ( Base ` m ) } $.

  $( A _commutative magma_ is a magma with a commutative operation.  Definition
     8 of [BourbakiAlg1] p. 7.  (Contributed by AV, 20-Jan-2020.) $)
  df-cmgm2 $a |- CMgmALT = { m e. MgmALT | ( +g ` m ) comLaw ( Base ` m ) } $.

  $( A _semigroup_ is a magma with an associative operation.  Definition in
     section II.1 of [Bruck] p. 23, or of an "associative magma" in definition
     5 of [BourbakiAlg1] p. 4, or of a semigroup in section 1.3 of [Hall] p. 7.
     (Contributed by AV, 6-Jan-2020.) $)
  df-sgrp2 $a |- SGrpALT = { g e. MgmALT | ( +g ` g ) assLaw ( Base ` g ) } $.

  $( A _commutative semigroup_ is a semigroup with a commutative operation.
     (Contributed by AV, 20-Jan-2020.) $)
  df-csgrp2 $a |- CSGrpALT = { g e. SGrpALT |
                                ( +g ` g ) comLaw ( Base ` g ) } $.

  ${
    $d B m $.  $d M m $.  $d .o. m $.
    ismgmALT.b $e |- B = ( Base ` M ) $.
    ismgmALT.o $e |- .o. = ( +g ` M ) $.
    $( The predicate "is a magma".  (Contributed by AV, 16-Jan-2020.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ismgmALT $p |- ( M e. V -> ( M e. MgmALT <-> .o. clLaw B ) ) $=
      ( vm cv cplusg cfv cbs ccllaw wbr cmgm2 wceq fveq2 eqtr4di breq12d elab2g
      df-mgm2 ) GHZIJZUAKJZLMDALMGBNCUABOZUBDUCALUDUBBIJDUABIPFQUDUCBKJAUABKPEQ
      RGTS $.

    $( The predicate "is a commutative magma".  (Contributed by AV,
       20-Jan-2020.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    iscmgmALT $p |- ( M e. CMgmALT <-> ( M e. MgmALT /\ .o. comLaw B ) ) $=
      ( vm cplusg cfv cbs ccomlaw wbr cmgm2 ccmgm2 wceq breq12d breq12i bitr4di
      cv fveq2 df-cmgm2 elrab2 ) FRZGHZUBIHZJKZCAJKZFBLMUBBNZUEBGHZBIHZJKUFUGUC
      UHUDUIJUBBGSUBBISOCUHAUIJEDPQFTUA $.

    $( The predicate "is a semigroup".  (Contributed by AV, 16-Jan-2020.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    issgrpALT $p |- ( M e. SGrpALT <-> ( M e. MgmALT /\ .o. assLaw B ) ) $=
      ( vm cv cplusg cfv cbs casslaw cmgm2 csgrp2 wceq eqtr4di breq12d df-sgrp2
      wbr fveq2 elrab2 ) FGZHIZUAJIZKRCAKRFBLMUABNZUBCUCAKUDUBBHICUABHSEOUDUCBJ
      IAUABJSDOPFQT $.

    $( The predicate "is a commutative semigroup".  (Contributed by AV,
       20-Jan-2020.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    iscsgrpALT $p |- ( M e. CSGrpALT
                        <-> ( M e. SGrpALT /\ .o. comLaw B ) ) $=
      ( vm cplusg cfv cbs ccomlaw wbr csgrp2 ccsgrp2 wceq fveq2 breq12d breq12i
      cv bitr4di df-csgrp2 elrab2 ) FRZGHZUBIHZJKZCAJKZFBLMUBBNZUEBGHZBIHZJKUFU
      GUCUHUDUIJUBBGOUBBIOPCUHAUIJEDQSFTUA $.
  $}

  ${
    $d M x y $.
    $( Equivalence of the two definitions of a magma.  (Contributed by AV,
       16-Jan-2020.) $)
    mgm2mgm $p |- ( M e. MgmALT <-> M e. Mgm ) $=
      ( vx vy cmgm2 wcel cmgm cplusg cfv cbs ccllaw wbr eqid ismgmALT cv co cvv
      wral wb fvex iscllaw mp2an biimprd biimtrid sylbid pm2.43i mgmplusgiopALT
      ismgm mpbird impbii ) ADEZAFEZUJUKUJUJAGHZAIHZJKZUKUMADULUMLZULLZMUNBNCNU
      LOUMECUMQBUMQZUJUKULPEUMPEUNUQRAGSAISBCUMPPULTUAUJUKUQBCUMADULUOUPUGUBUCU
      DUEUKUJUNAUFUMAFULUOUPMUHUI $.
  $}

  ${
    $d M x y z $.
    $( Equivalence of the two definitions of a semigroup.  (Contributed by AV,
       16-Jan-2020.) $)
    sgrp2sgrp $p |- ( M e. SGrpALT <-> M e. Smgrp ) $=
      ( vx vy vz cmgm2 wcel cplusg cfv cbs casslaw wbr wa cmgm cv wceq wral cvv
      co fvex eqid csgrp2 csgrp mgm2mgm anbi1i wb pm3.2i isasslaw pm5.32i bitri
      mp1i issgrpALT issgrp 3bitr4i ) AEFZAGHZAIHZJKZLZAMFZBNZCNZUORDNZUORUTVAV
      BUORUORODUPPCUPPBUPPZLZAUAFAUBFURUSUQLVDUNUSUQAUCUDUSUQVCUOQFZUPQFZLUQVCU
      EUSVEVFAGSAISUFBCDUPQQUOUGUJUHUIUPAUOUPTZUOTZUKBCDUPAUOVGVHULUM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Rings (extension)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Nonzero rings (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d M v $.
    $( If the scalar ring of a module is the zero ring, the module is the zero
       module, i.e. the base set of the module is the singleton consisting of
       the identity element only.  (Contributed by AV, 17-Apr-2019.) $)
    lmod0rng $p |- ( ( M e. LMod /\ -. ( Scalar ` M ) e. NzRing )
                     -> ( Base ` M ) = { ( 0g ` M ) } ) $=
      ( vv clmod wcel csca cfv cnzr wn cbs c0g csn wceq crg wi eqid wa co mpcom
      syl ex lmodring chash c1 0ringnnzr cur 0ring01eq wral cvsca lmodvs1 eqcom
      biimpi oveq1 eqcoms lmod0vs sylan9eqr sylan9eq exp32 com12 impl ralrimiva
      cv wb c0 wne lmodbn0 eqsn adantl mpbird sylbird com23 imp ) ACDZAEFZGDHZA
      IFZAJFZKLZVMMDZVLVNVQNVMAVMOZUAVRVNVLVQVRVNVMIFZUBFUCLZVLVQNZVMUDVRWAWBVR
      WAPVMJFZVMUEFZLZWBVTVMWDWCVTOWCOZWDOZUFWEVLVQWEVLPZVQBVAZVPLZBVOUGZWHWJBV
      OWEVLWIVODZWJVLWLPZWEWJWDWIAUHFZQZWILZWMWEWJNWNWDVMVOAWIVOOZVSWNOZWGUIWPW
      MWEWJWPWMWEPWIWOVPWPWIWOLWOWIUJUKWEWMWOWCWIWNQZVPWOWSLWDWCWDWCWIWNULUMWNV
      MWCVOAWIVPWQVSWRWFVPOUNUOUPUQRURUSUTVLVQWKVBZWEVLVOVCVDWTVOAWQVEBVOVPVFSV
      GVHTSTVIVJRVK $.
  $}

  $( The additive inverse of the 1 in a nonzero ring is not zero ( -1 =/= 0 ).
     (Contributed by AV, 29-Apr-2019.) $)
  nzrneg1ne0 $p |- ( R e. NzRing
                     -> ( ( invg ` R ) ` ( 1r ` R ) ) =/= ( 0g ` R ) ) $=
    ( cnzr wcel cur cfv cminusg cui c0g wne crg nzrring eqid unitnegcl syl2anc2
    1unit nzrunit mpdan ) ABCZADEZAFEZEZAGEZCZUAAHEZIRAJCSUBCUCAKAUBSUBLZSLOAUB
    TSUETLMNUAAUBUDUEUDLPQ $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Ideals as non-unital rings
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d I x y $.  $d L y $.  $d R y $.  $d U x y $.  $d .0. y $.  $d .1. y $.
    $d .x. x y $.
    lidldomn1.l $e |- L = ( LIdeal ` R ) $.
    lidldomn1.t $e |- .x. = ( .r ` R ) $.
    lidldomn1.1 $e |- .1. = ( 1r ` R ) $.
    lidldomn1.0 $e |- .0. = ( 0g ` R ) $.
    $( If a (left) ideal (which is not the zero ideal) of a domain has a
       multiplicative identity element, the identity element is the identity of
       the domain.  (Contributed by AV, 17-Feb-2020.) $)
    lidldomn1 $p |- ( ( R e. Domn /\ ( U e. L /\ U =/= { .0. } ) /\ I e. U )
        -> ( A. x e. U ( ( I .x. x ) = x /\ ( x .x. I ) = x ) -> I = .1. ) ) $=
      ( vy wcel wa co wceq wi syl3anc adantr cdomn csn wne w3a cv wrex wral crg
      domnring 3ad2ant1 simp2l simp2r lidlnz weq oveq2 id eqeq12d oveq1 anbi12d
      rspcva cbs cfv wss lidlss 3ad2ant2 sseld com12 impcom ringlidm syl2anc wb
      eqid eqeq2 eqcoms adantl csg cgrp ringgrp syl a1i 3imp ringidcl grpsubeq0
      ringcl ringsubdir eqeq1d simpl1 3jca grpsubcl biimpd eqneqall jaod sylbid
      wo domneq0 sylbird mpdan ex com13 expd pm2.43b com14 imp rexlimdva mpd )
      BUANZDGNZDHUBUCZOZFDNZUDZMUEZHUCZMDUFZFAUEZCPZXOQZXOFCPZXOQZOZADUGZFEQZRZ
      XKBUHNZXGXHXNXFXIYDXJBUIZUJZXFXGXHXJUKXFXGXHXJULMBGDHILUMSXKXMYCMDXKXLDNZ
      XMYCRYAYGXMXKYBYAYGXMXKYBRZRZYGYAYGYIRZYGYAOFXLCPZXLQZXLFCPZXLQZOZYJXTYOA
      XLDAMUNZXQYLXSYNYPXPYKXOXLXOXLFCUOYPUPZUQYPXRYMXOXLXOXLFCURYQUQUSUTYLYJYN
      YLYGXMYHXKYGXMOZYLYBXKYRYLYBRZXKYROZEXLCPZXLQZYSYTYDXLBVAVBZNZUUBXKYDYRYF
      TZYRXKUUDYGXKUUDRXMXKYGUUDXKDUUCXLXIXFDUUCVCZXJXGUUFXHUUCDGBUUCVLZIVDTZVE
      VFVGTVHZUUCBCEXLUUGJKVIVJYTUUBOYLYKUUAQZYBUUBYLUUJVKZYTUUKXLUUAXLUUAYKVMV
      NVOYTUUJYBRUUBYTUUJYKUUABVPVBZPZHQZYBYTBVQNZYKUUCNZUUAUUCNZUUNUUJVKXKUUOY
      RXFXIUUOXJXFYDUUOYEBVRVSUJZTYTYDFUUCNZUUDUUPUUEXKUUSYRXFXIXJUUSXIXJUUSRRX
      FXIDUUCFUUHVFVTWAZTZUUIUUCBCFXLUUGJWDSYTYDEUUCNZUUDUUQUUEXKUVBYRXFXIUVBXJ
      XFYDUVBYEUUCBEUUGKWBVSUJZTZUUIUUCBCEXLUUGJWDSUUCBUULYKUUAHUUGLUULVLZWCSYT
      UUNFEUULPZXLCPZHQZYBYTUVGUUMHYTUUCBCUULFEXLUUGJUVEUUEUVAUVDUUIWEWFYTUVHUV
      FHQZXLHQZWNZYBYTXFUVFUUCNZUUDUVHUVKVKXFXIXJYRWGYTUUOUUSUVBUDZUVLXKUVMYRXK
      UUOUUSUVBUURUUTUVCWHTZUUCBUULFEUUGUVEWIVSUUIUUCBCUVFXLHUUGJLWOSYTUVIYBUVJ
      YTUVIYBYTUVMUVIYBVKUVNUUCBUULFEHUUGLUVEWCVSWJYRUVJYBRZXKXMUVOYGUVJXMYBYBX
      LHWKVGVOVOWLWMWPWPTWMWQWRWSWTTVSWRXAXBXCXDXE $.
  $}

  ${
    lidlabl.l $e |- L = ( LIdeal ` R ) $.
    lidlabl.i $e |- I = ( R |`s U ) $.
    $( A (left) ideal of a ring is an (additive) abelian group.  (Contributed
       by AV, 17-Feb-2020.) $)
    lidlabl $p |- ( ( R e. Ring /\ U e. L ) -> I e. Abel ) $=
      ( crg wcel wa cabl csubg cfv ringabl adantr lidlsubg subgabl syl2anc ) AG
      HZBDHZIAJHZBAKLHCJHRTSAMNADBEOBACFPQ $.

    $( A (left) ideal of a ring is a non-unital ring.  (Contributed by AV,
       17-Feb-2020.)  (Proof shortened by AV, 11-Mar-2025.) $)
    lidlrng $p |- ( ( R e. Ring /\ U e. L ) -> I e. Rng ) $=
      ( crg wcel wa crng csubg ringrng adantr simpr lidlsubg rnglidlrng syl3anc
      cfv ) AGHZBDHZIAJHZTBAKRHCJHSUATALMSTNADBEOABCDEFPQ $.

    $d B x y $.  $d I x y $.  $d L x y $.  $d R x y $.  $d U x y $.
    $d .0. x y $.
    zlidlring.b $e |- B = ( Base ` R ) $.
    zlidlring.0 $e |- .0. = ( 0g ` R ) $.
    $( The zero (left) ideal of a non-unital ring is a unital ring (the zero
       ring).  (Contributed by AV, 16-Feb-2020.) $)
    zlidlring $p |- ( ( R e. Ring /\ U = { .0. } ) -> I e. Ring ) $=
      ( vx vy wcel wceq wa cfv co wb mpbird eqid crg csn crng cv cmulr cbs wral
      wrex lidl0 adantr eleq1 adantl lidlrng syldan eqcoms ring0cl ringlz mpdan
      jca cvv c0g fvexi oveq2 id eqeq12d oveq1 anbi12d ralsng eqeq1d ovanraleqv
      mp1i rexsng lidlbas simpr sylan9eqr ressmulr oveqd raleqbidv rexeqbidv ex
      eqcomd sylbid mpd isringrng sylanbrc ) BUAMZCFUBZNZOZDUCMZKUDZLUDZDUEPZQZ
      WLNZWLWKWMQZWLNZOZLDUFPZUGZKWSUHZDUAMWFWHCEMZWJWIXBWGEMZWFXCWHBEFGJUIUJZW
      HXBXCRWFCWGEUKULSBCDEGHUMUNWIXCXAXDWIXCXBXAWHXCXBRZWFXEWGCWGCEUKUOULWIXBX
      AWIXBOZXAWKWLBUEPZQZWLNZWLWKXGQZWLNZOZLWGUGZKWGUHZWIXNXBWFXNWHWFXNFWLXGQZ
      WLNZWLFXGQZWLNZOZLWGUGZWFXTFFXGQZFNZYBOZWFFBUFPZMZYCYDBFYDTZJUPWFYEOYBYBY
      DBXGFFYFXGTZJUQZYHUSURFUTMZXTYCRWFFBVAJVBZXSYCLFUTWLFNZXPYBXRYBYKXOYAWLFW
      LFFXGVCYKVDZVEYKXQYAWLFWLFFXGVFYLVEVGVHVKSYIXNXTRWFYJXMXTKFUTXIXPLWLWKWLX
      GWGFWKFNXHXOWLWKFWLXGVFVIVJVLVKSUJUJXFWTXMKWSWGXBWIWSCWGBCDEGHVMWFWHVNVOZ
      XFWRXLLWSWGYMXFWOXIWQXKXFWNXHWLXFWMXGWKWLXBWMXGNWIXBXGWMCBDXGEHYGVPWAULZV
      QVIXFWPXJWLXFWMXGWLWKYNVQVIVGVRVSSVTWBWCKLWSDWMWSTWMTWDWE $.

    $( Only the zero (left) ideal or the unit (left) ideal of a domain is a
       unital ring.  (Contributed by AV, 18-Feb-2020.) $)
    uzlidlring $p |- ( ( R e. Domn /\ U e. L )
                       -> ( I e. Ring <-> ( U = { .0. } \/ U = B ) ) ) $=
      ( vx vy wcel cfv co wceq wa eqid syl adantr crg crng cmulr cbs wral cdomn
      cv wrex csn wo isringrng wb domnring anim1i lidlrng ibar bicomd adantl wn
      cur ressmulr eqcomd oveqd eqeq1d anbi12d ad2antlr ad2antrr ralbidv wne wi
      simp-4l lidlbas eleq1d ad3antlr biimpd necon3bd imp jca lidldomn1 syl3anc
      ibir simpr sylbid eleq2d eqeltrrd rexlimdva2 impancom lidl1el sylibd orrd
      ex zlidlring simprbi wreu ringideu reurex cin ressbas ineq1 eqtrdi eqtr3d
      inidm raleqbidv rexeqbidv mpbird jaod impbid bitrd mpdan bitrid ) DUAMZDU
      BMZKUGZLUGZDUCNZOZXNPZXNXMXOOZXNPZQZLDUDNZUEZKYAUHZQZBUFMZCEMZQZCFUIZPZCA
      PZUJZKLYADXOYARXORUKZYGXLYDYKULYGBUAMZYFQZXLYEYMYFBUMZUNZBCDEGHUOSYGXLQZY
      DYCYKXLYDYCULYGXLYCYDXLYCUPUQURYQYCYKYQYCYKYQYCQZYIYJYRYIUSZBUTNZCMZYJYQY
      SYCUUAYQYSQZYBUUAKYAUUBXMYAMZQZYBQXMYTCUUDYBXMYTPZUUDYBXMXNBUCNZOZXNPZXNX
      MUUFOZXNPZQZLYAUEZUUEUUDXTUUKLYAYQXTUUKULZYSUUCYFUUMYEXLYFXQUUHXSUUJYFXPU
      UGXNYFXOUUFXMXNYFUUFXOCBDUUFEHUUFRZVAVBZVCVDYFXRUUIXNYFXOUUFXNXMUUOVCVDVE
      ZVFVGVHUUDYEYAEMZYAYHVIZQZUUCUULUUEVJYEYFXLYSUUCVKUUBUUSUUCUUBUUQUURYFUUQ
      YEXLYSYFUUQYFYACEBCDEGHVLZVMWAVNYQYSUURYQYIYAYHYQYAYHPYIYQYACYHYFYACPZYEX
      LUUTVFVDVOVPVQVRTUUBUUCWBLBUUFYAYTXMEFGUUNYTRZJVSVTWCVQUUDXMCMZYBUUBUUCUV
      CUUBUUCUVCUUBYACXMYFUVAYEXLYSUUTVNWDVOVQTWEWFWGYQUUAYJULZYCYQYNUVDYGYNXLY
      PTABEYTCGIUVBWHSTWIWJWKYQYIYCYJYEYIYCVJZYFXLYEYMUVEYOYMYIYCYMYIQXKYCABCDE
      FGHIJWLXKXLYCYLWMSWKSVGYQYNXLQZYJYCVJYGYNXLYPUNUVFYJYCUVFYJQZYCUUKLAUEZKA
      UHZYNUVIXLYJYMUVIYFYMUVHKAWNUVILKABUUFIUUNWOUVHKAWPSTVGUVGYBUVHKYAAUVGCAW
      QZYAAYFUVJYAPYMXLYJCADEBHIWRVNYJUVJAPUVFYJUVJAAWQACAAWSAXBWTURXAZUVGXTUUK
      LYAAUVKYFUUMYMXLYJUUPVNXCXDXEWKSXFXGXHXIXJ $.

    $( A (left) ideal of a domain which is neither the zero ideal nor the unit
       ideal is not a unital ring.  (Contributed by AV, 18-Feb-2020.) $)
    lidldomnnring $p |- ( ( R e. Domn
                  /\ ( U e. L /\ U =/= { .0. } /\ U =/= B ) ) -> I e/ Ring ) $=
      ( cdomn wcel csn wne w3a wa crg wnel wceq wn neanior biimpi adantl df-nel
      wo 3adant1 wb uzlidlring 3ad2antr1 notbid bitrid mpbird ) BKLZCELZCFMZNZC
      ANZOZPZDQRZCUOSCASUEZTZURVBUMUPUQVBUNUPUQPVBCUOCAUAUBUFUCUTDQLZTUSVBDQUDU
      SVCVAUMUPUNVCVAUGUQABCDEFGHIJUHUIUJUKUL $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The non-unital ring of even integers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x z $.
    2zrng.e $e |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) } $.
    $( 0 is an even integer.  (Contributed by AV, 11-Feb-2020.) $)
    0even $p |- 0 e. E $=
      ( cc0 cv c2 cmul co wceq cz wrex crab wcel 0z cc 2cn 0zd wb oveq2 rexbidv
      eqeq2d adantl mul01 eqcomd rspcedvd ax-mp eqeq1 elrab mpbir2an eleqtrri )
      EBFZGAFZHIZJZAKLZBKMZCEUQNEKNEUNJZAKLZOGPNZUSQUTUREGEHIZJZAEKUTRUMEJZURVB
      SUTVCUNVAEUMEGHTUBUCUTVAEGUDUEUFUGUPUSBEKULEJUOURAKULEUNUHUAUIUJDUK $.

    $( 1 is not an even integer.  (Contributed by AV, 12-Feb-2020.) $)
    1neven $p |- 1 e/ E $=
      ( c1 wcel cz c2 cv cmul co wceq wrex wa cdiv halfnz eleq1a mtoi cc cc0 wb
      wne 1cnd zcn 2cnne0 a1i divmul2 syl3anc mtbid intnan eqeq1 rexbidv elrab2
      nrex mtbir nelir ) ECECFEGFZEHAIZJKZLZAGMZNVAUQUTAGURGFZEHOKZURLZUTVBVDVC
      GFPURGVCQRVBESFURSFHSFHTUBNZVDUTUAVBUCURUDVEVBUEUFEURHUGUHUIUNUJBIZUSLZAG
      MVABEGCVFELVGUTAGVFEUSUKULDUMUOUP $.

    $( 2 is an even integer.  (Contributed by AV, 12-Feb-2020.) $)
    2even $p |- 2 e. E $=
      ( c2 cv cmul co wceq cz wrex crab wcel 2z cc 2cn c1 1zzd wb oveq2 rexbidv
      eqeq2d adantl mulrid eqcomd rspcedvd ax-mp eqeq1 elrab mpbir2an eleqtrri
      ) EBFZEAFZGHZIZAJKZBJLZCEUQMEJMEUNIZAJKZNEOMZUSPUTUREEQGHZIZAQJUTRUMQIZUR
      VBSUTVCUNVAEUMQEGTUBUCUTVAEEUDUEUFUGUPUSBEJULEIUOURAJULEUNUHUAUIUJDUK $.

    ${
      $d a b i j k x z $.  $d E i j k $.
      2zlidl.u $e |- U = ( LIdeal ` ZZring ) $.
      $( The even integers are a (left) ideal of the ring of integers.
         (Contributed by AV, 20-Feb-2020.) $)
      2zlidl $p |- E e. U $=
        ( vj vk va vb wcel cz cv cmul co caddc c2 wceq wrex wa vi wss wral crab
        c0 wne ssrab2 eqsstri cc0 0even ne0ii weq eqeq1 rexbidv anbi12i simprll
        elrab2 simpl zmulcld adantl zaddcld oveq2 eqeq2d cbvrexvw simpr simp-4l
        adantr ad2antrl oveq2d simpllr oveq12d eqeqan12d zcn 2cnd mul12d oveq1d
        wi mulcld ad4antr adddid eqtr4d rspcedvd exp41 rexlimiva impcom expdcom
        cc sylbi imp sylanbrc sylan2b ralrimivva rgen czring zringbas zringmulr
        zringplusg islidl mpbir3an ) DCKDLUBDUEUFUAMZGMZNOZHMZPOZDKZHDUCGDUCZUA
        LUCDBMZQAMZNOZRZALSZBLUDLEXKBLUGUHUIDABDEUJUKXFUALWTLKZXEGHDDXADKZXCDKZ
        TXLXALKZXAXIRZALSZTZXCLKZXCXIRZALSZTZTZXEXMXRXNYBXKXQBXALDBGULXJXPALXGX
        AXIUMUNEUQXKYABXCLDBHULXJXTALXGXCXIUMUNEUQUOXLYCTZXDLKXDXIRZALSZXEYDXBX
        CYDWTXAXLYCURXLXOXQYBUPUSYCXSXLYBXSXRXSYAURUTUTVAYCXLYFXRYBXLYFVQZXQXOY
        BYGVQZXQXAQIMZNOZRZILSXOYHVQZXPYKAILAIULXIYJXAXHYIQNVBVCVDYKYLILYBYILKZ
        YKTZXOYGYAXSYNXOTZYGVQZYAXCQJMZNOZRZJLSXSYPVQZXTYSAJLAJULXIYRXCXHYQQNVB
        VCVDYSYTJLYQLKZYSTZXSYOXLYFUUBXSTZYOTZXLTZYEWTYJNOZYRPOZQWTYINOZYQPOZNO
        ZRAUUILUUEUUHYQUUEWTYIUUDXLVEUUDYMXLUUCYMYKXOUPVGUSUUAYSXSYOXLVFVAUUEXH
        UUIRXDUUGXIUUJUUDXDUUGRXLUUDXBUUFXCYRPUUDXAYJWTNYNYKUUCXOYMYKVEVHVIUUAY
        SXSYOVJVKVGXHUUIQNVBVLUUEUUGQUUHNOZYRPOUUJUUEUUFUUKYRPUUEWTQYIXLWTWGKUU
        DWTVMUTZUUEVNZUUDYIWGKZXLYNUUNUUCXOYMUUNYKYIVMVGVHVGZVOVPUUEQUUHYQUUMUU
        EWTYIUULUUOVRUUAYQWGKYSXSYOXLYQVMVSVTWAWBWCWDWHWEWFWDWHWEWIWEXKYFBXDLDX
        GXDRXJYEALXGXDXIUMUNEUQWJWKWLWMUALPWNNCDGHFWOWQWPWRWS $.

      2zrng.r $e |- R = ( ZZring |`s E ) $.
      $( The ring of integers restricted to the even integers is a non-unital
         ring, the "ring of even integers".  Remark: the structure of the
         complementary subset of the set of integers, the odd integers, is not
         even a magma, see ~ oddinmgm .  (Contributed by AV, 20-Feb-2020.) $)
      2zrng $p |- R e. Rng $=
        ( czring crg wcel crng zringring 2zlidl lidlrng mp2an ) IJKEDKCLKMABDEF
        GNIECDGHOP $.
    $}

    2zrngbas.r $e |- R = ( CCfld |`s E ) $.
    $( The base set of R is the set of all even integers.  (Contributed by AV,
       31-Jan-2020.) $)
    2zrngbas $p |- E = ( Base ` R ) $=
      ( cc wss cbs cfv wceq cv c2 cmul co cz wrex crab ssrab2 zsscn sstri ax-mp
      eqsstri cnfldsrngbas ) DGHDCIJKDBLMALNOKAPQZBPRZGEUFPGUEBPSTUAUCCDFUDUB
      $.

    $( The group addition operation of R is the addition of complex numbers.
       (Contributed by AV, 31-Jan-2020.) $)
    2zrngadd $p |- + = ( +g ` R ) $=
      ( cvv wcel caddc cplusg cfv wceq cv c2 cmul co cz wrex zex rabex2 ax-mp
      cnfldsrngadd ) DGHICJKLBMNAMOPLAQRBQDESTCDGFUBUA $.

    $( The additive identity of R is the complex number 0.  (Contributed by AV,
       11-Feb-2020.) $)
    2zrng0 $p |- 0 = ( 0g ` R ) $=
      ( ccnfld cmnd wcel cc0 cc wss c0g cfv wceq ccrg crg cncrng cz cv crngring
      ringmnd mp2b 0even c2 cmul co wrex crab ssrab2 eqsstri zsscn sstri cnfld0
      cnfldbas ress0g mp3an ) GHIZJDIDKLJCMNOGPIGQIURRGUAGUBUCABDEUDDSKDBTUEATU
      FUGOASUHZBSUISEUSBSUJUKULUMDKGCJFUOUNUPUQ $.

    $d E a b $.  $d R a b $.  $d a b x y z $.
    $( R is an (additive) magma.  (Contributed by AV, 6-Jan-2020.) $)
    2zrngamgm $p |- R e. Mgm $=
      ( wcel cv caddc co cz c2 cmul wceq wrex wa rexbidv wi adantr cc0 va vb vy
      cmgm wral eqeq1 elrab2 oveq2 eqeq2d cbvrexvw zaddcl ancoms syl2anr adantl
      simpl wb eqidd rspcedvd simpr oveqan12rd 2cnd cc zcn adddid eqtr4d eqeq1d
      mpbird rexlimdvaa rexlimiva imbitrrdi sylanbrc exp32 impancom com13 sylbi
      ex imp impcom syl2anb rgen2 crab 0z 2cn mul01 eqcomd ax-mp elrab mpbir2an
      0zd eleqtrri 2zrngbas 2zrngadd ismgmn0 mpbir ) CUDGZUAHZUBHZIJZDGZUBDUEUA
      DUEZWSUAUBDDWPDGWPKGZWPLAHZMJZNZAKOZPZWQKGZWQXCNZAKOZPZWSWQDGBHZXCNZAKOZX
      EBWPKDXKWPNXLXDAKXKWPXCUFQEUGXMXIBWQKDXKWQNXLXHAKXKWQXCUFQEUGXFXJWSXEXAXJ
      WSRZXEWPLUCHZMJZNZUCKOZXAXNRXDXQAUCKXBXONXCXPWPXBXOLMUHUIUJXJXAXRWSXGXAXI
      XRWSRXGXAPZXIXRWSXSXIXRPZPWRKGZWRXCNZAKOZWSXSYAXTXAXGYAWPWQUKULSXTXSYCXTX
      SWRLXKMJZNZBKOZYCXIXRXSYFRZXHXRYGRAKXBKGZXHPZXQYGUCKYIXOKGZXQPZPZXSYFYLXS
      PZYFLXOXBIJZMJZYDNZBKOYMYPYOYONZBYNKYLYNKGZXSYKYJYHYRYIYJXQUOYHXHUOXOXBUK
      UMSXKYNNZYPYQUPYMYSYDYOYOXKYNLMUHUIUNYMYOUQURYMYEYPBKYMWRYOYDYMWRXPXCIJZY
      OYLWRYTNXSYKYIWPXPWQXCIYJXQUSYHXHUSUTSYLYOYTNXSYLLXOXBYLVAYKXOVBGZYIYJUUA
      XQXOVCSUNYIXBVBGZYKYHUUBXHXBVCSSVDSVEVFQVGVPVHVIVQYBYEABKXBXKNXCYDWRXBXKL
      MUHUIUJVJVRXMYCBWRKDXKWRNXLYBAKXKWRXCUFQEUGVKVLVMVNVOVRVQVSVTTDGWOWTUPTXM
      BKWAZDTUUCGTKGTXCNZAKOZWBLVBGZUUEWCUUFUUDTLTMJZNZATKUUFWIXBTNZUUDUUHUPUUF
      UUIXCUUGTXBTLMUHUIUNUUFUUGTLWDWEURWFXMUUEBTKXKTNXLUUDAKXKTXCUFQWGWHEWJUAU
      BTDCIABCDEFWKABCDEFWLWMWFWN $.

    $d R x y z $.
    $( R is an (additive) semigroup.  (Contributed by AV, 4-Feb-2020.) $)
    2zrngasgrp $p |- R e. Smgrp $=
      ( va vy vb wcel cv caddc co wceq cz wral w3a cc elrabi zcn cmgm cmul wrex
      csgrp c2 crab 2zrngamgm 3anim123i addass 3syl rgen3 cbs 2zrngbas 2zrngadd
      cfv eqtr3i issgrp mpbir2an ) CUDJCUAJGKZHKZLMIKZLMUSUTVALMLMNZIBKUEAKUBMN
      AOUCZBOUFZPHVDPGVDPABCDEFUGVBGHIVDVDVDUSVDJZUTVDJZVAVDJZQUSOJZUTOJZVAOJZQ
      USRJZUTRJZVARJZQVBVEVHVFVIVGVJVCBUSOSVCBUTOSVCBVAOSUHVHVKVIVLVJVMUSTUTTVA
      TUHUSUTVAUIUJUKGHIVDCLDVDCULUOEABCDEFUMUPABCDEFUNUQUR $.

    $d E x y z $.
    $( R is an (additive) monoid.  (Contributed by AV, 11-Feb-2020.) $)
    2zrngamnd $p |- R e. Mnd $=
      ( vy cmnd wcel csgrp cv caddc co wceq wa wral wrex cc0 adantl cz 0even id
      2zrngasgrp wb oveq1 eqeq1d ovanraleqv cmul crab elrabi eleq2s zcnd addlid
      cc c2 addrid ralrimiva rspcedvd ax-mp 2zrngbas 2zrngadd ismnddef mpbir2an
      jca syl ) CHICJIAKZGKZLMZVGNZVGVFLMVGNOGDPZADQZABCDEFUCRDIZVKABDEUAVLVJRV
      GLMZVGNZVGRLMVGNZOZGDPZARDVLUBVFRNZVJVQUDVLVIVNGVGVFVGLDRVRVHVMVGVFRVGLUE
      UFUGSVLVPGDVGDIZVPVLVSVGUNIZVPVSVGVGTIVGBKUOVFUHMNATQZBTUIDWABVGTUJEUKULV
      TVNVOVGUMVGUPVDVESUQURUSDLACGABCDEFUTABCDEFVAVBVC $.

    $( R is a commutative (additive) monoid.  (Contributed by AV,
       11-Feb-2020.) $)
    2zrngacmnd $p |- R e. CMnd $=
      ( vy cc0 wcel caddc cfv wceq a1i cv co cc cz elrabi zcnd eleq2s 0even cbs
      ccmn 2zrngbas cplusg 2zrngadd cmnd 2zrngamnd cmul wrex crab adantr adantl
      wa c2 addcomd 3adant1 iscmnd ax-mp ) HDIZCUCIABDEUAUTAGDJCDCUBKLUTABCDEFU
      DMJCUEKLUTABCDEFUFMCUGIUTABCDEFUHMANZDIZGNZDIZVAVCJOVCVAJOLUTVBVDUNVAVCVB
      VAPIZVDVEVABNUOVAUIOLAQUJZBQUKZDVAVGIVAVFBVAQRSETULVDVCPIZVBVHVCVGDVCVGIV
      CVFBVCQRSETUMUPUQURUS $.

    $( R is an (additive) group.  (Contributed by AV, 6-Jan-2020.) $)
    2zrngagrp $p |- R e. Grp $=
      ( vy wcel cv caddc co cc0 wceq wrex cneg cz c2 cmul wa adantl weq rexbidv
      cgrp cmnd wral 2zrngamnd eqeq1 elrab2 znegcl adantr nfre1 wb oveq2 eqeq2d
      nfv negeq 2cnd mulneg2d eqcomd sylan9eqr rspcedvd cbvrexvw sylibr rexlimd
      zcn exp31 imp sylanbrc sylbi oveq1 eqeq1d crab elrabi eleq2s zcnd addcomd
      negcld negidd eqtrd rgen 2zrngbas 2zrngadd 2zrng0 isgrp mpbir2an ) CUCHCU
      DHBIZGIZJKZLMZBDNZGDUEABCDEFUFWJGDWGDHZWIWGOZWGJKZLMZBWLDWKWGPHZWGQAIZRKZ
      MZAPNZSZWLDHZWFWQMZAPNZWSBWGPDBGUAXBWRAPWFWGWQUGUBEUHWTWLPHZWLWQMZAPNZXAW
      OXDWSWGUIUJWOWSXFWOWRXFAPWOAUOXEAPUKWOWPPHZWRXFWOXGSZWRSZWLQWFRKZMZBPNXFX
      IXKWLQWPOZRKZMZBXLPXHXLPHZWRXGXOWOWPUITUJWFXLMZXKXNULXIXPXJXMWLWFXLQRUMUN
      TWRXHWLWQOZXMWGWQUPXGXQXMMWOXGXMXQXGQWPXGUQWPVEURUSTUTVAXEXKABPABUAWQXJWL
      WPWFQRUMUNVBVCVFVDVGXCXFBWLPDWFWLMZXBXEAPWFWLWQUGUBEUHVHVIXRWIWNULWKXRWHW
      MLWFWLWGJVJVKTWKWMWGWLJKLWKWLWGWKWGWKWGWOWGXCBPVLDXCBWGPVMEVNVOZVQXSVPWKW
      GXSVRVSVAVTDJBCLGABCDEFWAABCDEFWBABCDEFWCWDWE $.

    $( R is an (additive) abelian group.  (Contributed by AV, 11-Feb-2020.) $)
    2zrngaabl $p |- R e. Abel $=
      ( cabl wcel cgrp ccmn wa 2zrngagrp 2zrngacmnd pm3.2i isabl mpbir ) CGHCIH
      ZCJHZKQRABCDEFLABCDEFMNCOP $.

    $( The ring multiplication operation of R is the multiplication on complex
       numbers.  (Contributed by AV, 31-Jan-2020.) $)
    2zrngmul $p |- x. = ( .r ` R ) $=
      ( cvv wcel cmul cmulr cfv wceq cv c2 co cz wrex zex rabex2 cnfldsrngmul
      ax-mp ) DGHICJKLBMNAMIOLAPQBPDERSCDGFTUA $.

    $d M a b $.
    2zrngmmgm.1 $e |- M = ( mulGrp ` R ) $.
    $( R is a (multiplicative) magma.  (Contributed by AV, 11-Feb-2020.) $)
    2zrngmmgm $p |- M e. Mgm $=
      ( va vb vy wcel cv cmul co cz c2 wceq wrex wa eqeq1 rexbidv elrab2 zmulcl
      cmgm wral ad2ant2r wi nfre1 nfan nfim simpll simpl syl2an wb oveq2 eqeq2d
      nfv adantl oveq1 ad3antlr 2cnd cc ad3antrrr adantr mulassd eqtrd rspcedvd
      zcn exp41 rexlimi impcom imp cbvrexvw anbi2i bitri sylanbrc syl2anb rgen2
      cc0 0even 2zrngbas mgpbas 2zrngmul mgpplusg ismgmn0 ax-mp mpbir ) EUELZIM
      ZJMZNOZDLZJDUFIDUFZWMIJDDWJDLWJPLZWJQAMZNOZRZAPSZTZWKPLZWKWQRZAPSZTZWMWKD
      LBMZWQRZAPSZWSBWJPDXEWJRXFWRAPXEWJWQUAUBFUCXGXCBWKPDXEWKRXFXBAPXEWKWQUAUB
      FUCWTXDTWLPLZWLQKMZNOZRZKPSZWMWOXAXHWSXCWJWKUDUGWTXDXLWSWOXDXLUHZWRWOXMUH
      APWOXMAWOAURXDXLAXAXCAXAAURXBAPUIUJXLAURUKUKWPPLZWRWOXDXLXNWRTWOTZXDTZXKW
      LQWPWKNOZNOZRZKXQPXOXNXAXQPLXDXNWRWOULXAXCUMWPWKUDUNXIXQRZXKXSUOXPXTXJXRW
      LXIXQQNUPUQUSXPWLWQWKNOZXRWRWLYARXNWOXDWJWQWKNUTVAXPQWPWKXPVBXNWPVCLWRWOX
      DWPVIVDXDWKVCLZXOXAYBXCWKVIVEUSVFVGVHVJVKVLVMWMXHWLWQRZAPSZTXHXLTXGYDBWLP
      DXEWLRXFYCAPXEWLWQUAUBFUCYDXLXHYCXKAKPWPXIRWQXJWLWPXIQNUPUQVNVOVPVQVRVSVT
      DLWIWNUOABDFWAIJVTDENDCEHABCDFGWBWCCNEHABCDFGWDWEWFWGWH $.

    $d M y $.
    $( R is a (multiplicative) semigroup.  (Contributed by AV, 4-Feb-2020.) $)
    2zrngmsgrp $p |- M e. Smgrp $=
      ( va vy vb wcel cv cmul co cz wral w3a cc elrabi cmgm wceq wrex 2zrngmmgm
      csgrp crab 3anim123i zcn mulass 3syl rgen3 cbs cfv 2zrngbas mgpbas eqtr3i
      c2 2zrngmul mgpplusg issgrp mpbir2an ) EUELEUALIMZJMZNOKMZNOVBVCVDNONOUBZ
      KBMUQAMNOUBAPUCZBPUFZQJVGQIVGQABCDEFGHUDVEIJKVGVGVGVBVGLZVCVGLZVDVGLZRVBP
      LZVCPLZVDPLZRVBSLZVCSLZVDSLZRVEVHVKVIVLVJVMVFBVBPTVFBVCPTVFBVDPTUGVKVNVLV
      OVMVPVBUHVCUHVDUHUGVBVCVDUIUJUKIJKVGENDVGEULUMFDCEHABCDFGUNUOUPCNEHABCDFG
      URUSUTVA $.

    $( The ring of integers restricted to the even integers is a non-unital
       ring, the "ring of even integers".  Alternate version of ~ 2zrng , based
       on a restriction of the field of the complex numbers.  The proof is
       based on the facts that the ring of even integers is an additive abelian
       group (see ~ 2zrngaabl ) and a multiplicative semigroup (see
       ~ 2zrngmsgrp ).  (Contributed by AV, 11-Feb-2020.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    2zrngALT $p |- R e. Rng $=
      ( va vb vy wcel cv caddc co cmul wceq wral cc cz crng csgrp wa 2zrngmsgrp
      cabl 2zrngaabl c2 wrex crab elrabi zcnd eleq2s w3a adddi adddir jca rgen3
      syl3an 2zrngbas 2zrngadd 2zrngmul isrng mpbir3an ) CUALCUELEUBLIMZJMZKMZN
      OPOVDVEPOVDVFPOZNOQZVDVENOVFPOVGVEVFPONOQZUCZKDRJDRIDRABCDFGUFABCDEFGHUDV
      JIJKDDDVDDLVDSLZVEDLVESLZVFDLVFSLZVJVKVDBMUGAMPOQATUHZBTUIZDVDVOLVDVNBVDT
      UJUKFULVLVEVODVEVOLVEVNBVETUJUKFULVMVFVODVFVOLVFVNBVFTUJUKFULVKVLVMUMVHVI
      VDVEVFUNVDVEVFUOUPURUQIJKDNCPEABCDFGUSHABCDFGUTABCDFGVAVBVC $.

    $( R has no multiplicative (left) identity.  (Contributed by AV,
       12-Feb-2020.) $)
    2zrngnmlid $p |- A. b e. E E. a e. E ( b x. a ) =/= a $=
      ( cv cmul co wne wcel c2 a1i wceq cc c1 wrex 2even wb oveq2 id neeq12d cz
      adantl crab elrabi zcnd eleq2s wa cdiv 1neven elnelne2 mpan2 adantr simpr
      wnel 2cnd 2ne0 divcan4d 2cnne0 divid 3netr4d mulcld div11 syl3anc biimprd
      cc0 mp1i necon3d mpd mpdan rspcedvd rgen ) GKZFKZLMZVSNZFDUAGDVRDOZWAVRPL
      MZPNZFPDPDOWBABDHUBQVSPRZWAWDUCWBWEVTWCVSPVSPVRLUDWEUEUFUHWBVRSOZWDWFVRBK
      PAKLMRAUGUAZBUGUIZDVRWHOVRWGBVRUGUJUKHULWBWFUMZWCPUNMZPPUNMZNWDWIVRTWJWKW
      BVRTNZWFWBTDUTWLABDHUOVRTDUPUQURWIVRPWBWFUSZWIVAZPVKNZWIVBQVCPSOZWOUMZWKT
      RWIVDPVEVLVFWIWCPWJWKWIWJWKRZWCPRZWIWCSOWPWQWRWSUCWIVRPWMWNVGWNWQWIVDQWCP
      PVHVIVJVMVNVOVPVQ $.

    $( R has no multiplicative (right) identity.  (Contributed by AV,
       12-Feb-2020.) $)
    2zrngnmrid $p |- A. a e. ( E \ { 0 } ) A. b e. E ( a x. b ) =/= a $=
      ( cv co wne cc0 wcel wa cz wceq adantr c1 cmul cdif cc eldifsn wrex eqeq1
      csn rexbidv elrab2 zcn sylbi anim1i ancli cdiv wnel 1neven elnelne2 mpan2
      ad2antrl w3a simpr anim2i 3anass ancom bitri sylibr divcan3 divid 3netr4d
      c2 syl wb simpl mulcl syl2an div11 syl3anc biimprd necon3d mpd rgen2 ) FK
      ZGKZUALZWBMZFGDNUGUBZDWBWFOZWBUCOZWBNMZPZWCDOZWCUCOZPZWEWKWGWBDOZWIPWJWBD
      NUDWNWHWIWNWBQOZWBVJAKUALZRZAQUEZPWHBKZWPRZAQUEZWRBWBQDWSWBRWTWQAQWSWBWPU
      FUHHUIWOWHWRWBUJSUKULUKWKWLWKWCQOZWCWPRZAQUEZPWLXAXDBWCQDWSWCRWTXCAQWSWCW
      PUFUHHUIXBWLXDWCUJSUKUMWJWMPZWDWBUNLZWBWBUNLZMWEXEWCTXFXGWKWCTMZWJWLWKTDU
      OXHABDHUPWCTDUQURUSXEWLWHWIUTZXFWCRXEWJWLPZXIWMWLWJWKWLVAZVBXIWLWJPXJWLWH
      WIVCWLWJVDVEVFWCWBVGVKWJXGTRWMWBVHSVIXEWDWBXFXGXEXFXGRZWDWBRZXEWDUCOZWHWJ
      XLXMVLWJWHWLXNWMWHWIVMZXKWBWCVNVOWJWHWMXOSWJWMVMWDWBWBVPVQVRVSVTVOWA $.

    $( R has no multiplicative (left) identity.  (Contributed by AV,
       12-Feb-2020.) $)
    2zrngnmlid2 $p |- A. a e. ( E \ { 0 } ) A. b e. E ( b x. a ) =/= a $=
      ( cv cmul co wne wral wcel wceq cc cz elrabi cc0 csn 2zrngnmrid wa eldifi
      cdif wrex crab zcnd eleq2s syl mulcom syl2an eqcomd eqeq1d biimpd necon3d
      c2 ralimdva ralimia ax-mp ) FKZGKZLMZVBNZGDOZFDUAUBZUFZOVCVBLMZVBNZGDOZFV
      HOABCDEFGHIJUCVFVKFVHVBVHPZVEVJGDVLVCDPZUDZVIVBVDVBVNVIVBQVDVBQVNVIVDVBVN
      VDVIVLVBRPZVCRPZVDVIQVMVLVBDPVOVBDVGUEVOVBBKURAKLMQASUGZBSUHZDVBVRPVBVQBV
      BSTUIHUJUKVPVCVRDVCVRPVCVQBVCSTUIHUJVBVCULUMUNUOUPUQUSUTVA $.

    $( R is not a unital ring.  (Contributed by AV, 6-Jan-2020.) $)
    2zrngnring $p |- R e/ Ring $=
      ( vy vb va crg wcel cmnd cv cfv co cmul wral wn cgrp wceq cbs w3a w3o wne
      cplusg wa wrex 2zrngnmlid 2zrngbas mgpbas 2zrngmul mgpplusg isnmnd df-nel
      wnel sylib ax-mp 3mix2i 3ianor mpbir eqid isring mtbir nelir ) CLCLMCUAMZ
      ENMZAOZIOZBOZCUGPZQRQVIVJRQVIVKRQZVLQUBVIVJVLQVKRQVMVJVKRQVLQUBUHBCUCPZSI
      VNSAVNSZUDZVPTVGTZVHTZVOTZUEVRVQVSJOKOZRQVTUFKDUIJDSZVRABCDEKJFGHUJWAENUQ
      VRKJDERDCEHABCDFGUKULCREHABCDFGUMZUNUOENUPURUSUTVGVHVOVAVBAIBVNVLCREVNVCH
      VLVCWBVDVEVF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  A constructed not unital ring
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    cznrng.y $e |- Y = ( Z/nZ ` N ) $.
    cznrng.b $e |- B = ( Base ` Y ) $.
    cznrng.x $e |- X = ( Y sSet <. ( .r ` ndx ) ,
                                   ( x e. B , y e. B |-> C ) >. ) $.
    $( Lemma for ~ cznrng :  The base set of the ring constructed from a
       ` Z/nZ ` structure by replacing the (multiplicative) ring operation by a
       constant operation is the base set of the ` Z/nZ ` structure.
       (Contributed by AV, 16-Feb-2020.) $)
    cznrnglem $p |- B = ( Base ` X ) $=
      ( cbs cfv cnx cmulr cmpo cop csts co baseid basendxnmulrndx eqcomi fveq2i
      setsnid 3eqtri ) CGKLGMNLZABCCDOZPQRZKLFKLIUFUEKGSTUCUGFKFUGJUAUBUD $.

    $( The ring constructed from a ` Z/nZ ` structure by replacing the
       (multiplicative) ring operation by a constant operation is an abelian
       group.  (Contributed by AV, 16-Feb-2020.) $)
    cznabel $p |- ( ( N e. NN /\ C e. B ) -> X e. Abel ) $=
      ( cn wcel wa cabl cbs cfv fveq2i setsnid eqtr4i cplusg cn0 ccrg crg nnnn0
      adantr zncrng crngring ringabl 4syl cnx cmulr cmpo cop co basendxnmulrndx
      csts baseid plusgid plusgndxnmulrndx ablprop sylibr ) EKLZDCLZMZGNLZFNLVD
      EUALZGUBLGUCLVEVBVFVCEUDUEEGHUFGUGGUHUIFGFOPGUJUKPZABCCDULZUMUPUNZOPGOPFV
      IOJQVHVGOGUQUORSFTPVITPGTPFVITJQVHVGTGURUSRSUTVA $.

    $d B a b c x y $.  $d C a b c x y $.  $d N a b c x y $.  $d X a b c x $.
    $d Y a b c x y $.  $d .0. a b c x y $.
    cznrng.0 $e |- .0. = ( 0g ` Y ) $.
    $( The ring constructed from a ` Z/nZ ` structure by replacing the
       (multiplicative) ring operation by a constant operation is a non-unital
       ring.  (Contributed by AV, 17-Feb-2020.) $)
    cznrng $p |- ( ( N e. NN /\ C = .0. ) -> X e. Rng ) $=
      ( vb wcel wceq wa cfv cplusg co syl va vc cn cabl cmgp csgrp cv cmpo wral
      w3a crng ccrg wi cn0 nnnn0 zncrng crg crngring ring0cl eleq1a imp cznabel
      adantlr eqid cznrnglem mgpbas cnx cmulr cop csts fveq2i cvv czn fvexi cbs
      mpoex mulridx setsid mp2an mgpplusg eqcomi c0 ne0i adantl simpr copissgrp
      wne oveq1 ad3antlr ringmnd adantr anim1i mndlid eqtrd eqidd simpr1 simpr2
      cmnd ovmpod simpr3 oveq12d ad3antrrr ringacl syl3anc 3eqtr4rd ralrimivvva
      weq 3jca mpdan plusgid plusgndxnmulrndx setsnid eqtr4i eqtri isrng sylibr
      jca ) EUCNZDHOZPZFUDNZFUEQZUFNZUAUGZMUGZUBUGZGRQZSZABCCDUHZSZYDYEYISZYDYF
      YISZYGSZOZYDYEYGSZYFYISZYLYEYFYISZYGSZOZPZUBCUIMCUIUACUIZUJZFUKNXTDCNZUUB
      XRXSUUCXRGULNZXSUUCUMZXREUNNUUDEUOEGIUPTZUUDGUQNZUUEGURZUUGHCNUUECGHJLUSH
      CDUTTTTVAXTUUCPZYAYCUUAXRUUCYAXSABCDEFGIJKVBVCUUIABCDYBCFYBYBVDZABCDEFGIJ
      KVEZVFYIYBRQGVGVHQZYIVIVJSZYIYBFUUMUEKVKGVLNYIVLNYIUUMVHQZOGEVMIVNABCCDCG
      VOJVNZUUOVPVLYIVHVLGVQVRVSZVTWAUUCCWBWGXTCDWCWDXTUUCWEZWFUUIYTUAMUBCCCUUI
      YDCNZYECNZYFCNZUJZPZYNYSUVBDDYGSZDYMYJUVBUVCHDYGSZDXSUVCUVDOXRUUCUVADHDYG
      WHWIUVBGWRNZUUCPZUVDDOUUIUVFUVAXTUVEUUCXRUVEXSXRUUGUVEXRUUDUUGUUFUUHTZGWJ
      TWKWLWKCYGGDHJYGVDZLWMTWNZUVBYKDYLDYGUVBABYDYECCDDYICUVBYIWOZUVBAUAXGZBMX
      GPPDWOUUIUURUUSUUTWPZUUIUURUUSUUTWQZUUIUUCUVAUUQWKZWSUVBABYDYFCCDDYICUVJU
      VBUVKBUBXGZPPDWOUVLUUIUURUUSUUTWTZUVNWSZXAUVBABYDYHCCDDYICUVJUVBUVKBUGYHO
      PPDWOUVLUVBUUGUUSUUTYHCNXRUUGXSUUCUVAUVGXBZUVMUVPCYGGYEYFJUVHXCXDUVNWSXEU
      VBUVCDYRYPUVIUVBYLDYQDYGUVQUVBABYEYFCCDDYICUVJUVBAMXGUVOPPDWOUVMUVPUVNWSX
      AUVBABYOYFCCDDYICUVJUVBAUGYOOUVOPPDWOUVBUUGUURUUSYOCNUVRUVLUVMCYGGYDYEJUV
      HXCXDUVPUVNWSXEXQXFXHXIUAMUBCYGFYIYBUUKUUJYGUUMRQFRQYIUULRGXJXKXLFUUMRKVK
      XMYIUUNFVHQUUPUUMFVHFUUMKWAVKXNXOXP $.

    $( The ring constructed from a ` Z/nZ ` structure with ` 1 < n ` by
       replacing the (multiplicative) ring operation by a constant operation is
       not a unital ring.  (Contributed by AV, 17-Feb-2020.) $)
    cznnring $p |- ( ( N e. ( ZZ>= ` 2 ) /\ C e. B ) -> X e/ Ring ) $=
      ( c2 cfv wcel co cmulr wceq cvv c1 va vb vc cuz wa wn wnel cgrp cmgp cmnd
      crg cv cplusg cnx cmpo cop csts wral w3a eqid cznrnglem mgpbas fveq2i czn
      fvexi cbs mpoex mulridx setsid mp2an mgpplusg eqcomi simpr clt wbr cz cle
      chash eluz2 1lt2 wi cr 1red 2re a1i zre ltletr syl3anc expcomd 3imp sylbi
      cn eluz2nn znhash breqtrrd adantr copisnmnd df-nel sylib intn3an2d isring
      mpi syl sylnibr sylibr ) EMUDNOZDCOZUEZFUKOZUFFUKUGXHFUHOZFUINZUJOZUAULZU
      BULZUCULZFUMNZPGUNQNABCCDUOZUPUQPZQNZPXMXNXSPXMXOXSPZXPPRXMXNXPPXOXSPXTXN
      XOXSPXPPRUEUCCURUBCURUACURZUSXIXHXLXJYAXHXKUJUGXLUFXHABCDXKCFXKXKUTZABCDE
      FGIJKVAZVBXQXKUMNXRXQXKFXRUIKVCGSOXQSOXQXSRGEVDIVEABCCDCGVFJVEZYDVGSXQQSG
      VHVIVJVKVLXFXGVMXFTCVRNZVNVOXGXFTEYEVNXFMVPOZEVPOZMEVQVOZUSZTEVNVOZMEVSYI
      TMVNVOZYJVTYFYGYHYKYJWAZYGYHYLWAWAYFYGYKYHYJYGTWBOMWBOZEWBOYKYHUEYJWAYGWC
      YMYGWDWEEWFTMEWGWHWIWEWJXBWKXFEWLOYEEREWMCEGIJWNXCWOWPWQXKUJWRWSWTUAUBUCC
      XPFXSXKYCYBXPUTXRFQFXRKVLVCXAXDFUKWRXE $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The category of non-unital rings (alternate definition)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  As an alternative to ~ df-rngc , the "category of non-unital rings" can be
  defined as extensible structure consisting of three components/slots for the
  objects, morphisms and composition, according to ~ dfrngc2 .

$)

  $c RngCatALTV $.

  $( Extend class notation to include the category Rng.
     (New usage is discouraged.) $)
  crngcALTV $a class RngCatALTV $.

  ${
    $d b f g u v x y z $.
    $( Definition of the category Rng, relativized to a subset ` u ` .  This is
       the category of all non-unital rings in ` u ` and homomorphisms between
       these rings.  Generally, we will take ` u ` to be a weak universe or
       Grothendieck universe, because these sets have closure properties as
       good as the real thing.  (New usage is discouraged.)  (Contributed by
       AV, 27-Feb-2020.) $)
    df-rngcALTV $a |- RngCatALTV = ( u e. _V |-> [_ ( u i^i Rng ) / b ]_
              { <. ( Base ` ndx ) , b >. ,
                <. ( Hom ` ndx ) , ( x e. b , y e. b |-> ( x RngHom y ) ) >. ,
                <. ( comp ` ndx ) , ( v e. ( b X. b ) , z e. b |->
                                     ( g e. ( ( 2nd ` v ) RngHom z ) ,
                                       f e. ( ( 1st ` v ) RngHom ( 2nd ` v ) )
                                       |-> ( g o. f ) ) ) >. } ) $.

    $d b u v x y z B $.  $d b u v x y z U $.  $d b u .x. $.  $d b u H $.
    $d b u v x y z ph $.
    rngcvalALTV.c $e |- C = ( RngCatALTV ` U ) $.
    rngcvalALTV.u $e |- ( ph -> U e. V ) $.
    rngcvalALTV.b $e |- ( ph -> B = ( U i^i Rng ) ) $.
    rngcvalALTV.h $e |- ( ph -> H = ( x e. B , y e. B
                                      |-> ( x RngHom y ) ) ) $.
    rngcvalALTV.o $e |- ( ph -> .x. = ( v e. ( B X. B ) , z e. B |->
                                     ( g e. ( ( 2nd ` v ) RngHom z ) ,
                                       f e. ( ( 1st ` v ) RngHom ( 2nd ` v ) )
                                       |-> ( g o. f ) ) ) ) $.
    $( Value of the category of non-unital rings (in a universe).
       (New usage is discouraged.)  (Contributed by AV, 27-Feb-2020.) $)
    rngcvalALTV $p |- ( ph -> C = { <. ( Base ` ndx ) , B >. ,
                    <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .x. >. } ) $=
      ( cv cvv vu vb crngcALTV cfv cnx cbs cop chom cco ctp crng crnghm co cmpo
      cin cxp c2nd c1st ccom csb cmpt wceq df-rngcALTV a1i wcel vex inex1 ineq1
      wa adantl adantr eqtr4d simpr opeq2d mpoeq123dv ad2antrr sqxpeqd tpeq123d
      eqidd csbied2 elex syl tpex fvmptd eqtrid ) AGIUCUDUEUFUDZFUGZUEUHUDZLUGZ
      UEUIUDZHUGZUJZNAUAIUBUASZUKUOZWFUBSZUGZWHBCWOWOBSCSULUMZUNZUGZWJEDWOWOUPZ
      WOKJESZUQUDZDSULUMXAURUDXBULUMKSJSUSUNZUNZUGZUJZUTZWLTUCTUCUATXGVAVBABCDE
      UAJKUBVCVDAWMIVBZVIZUBWNFXFWLTWNTVEXIWMUKUAVFVGVDXIWNIUKUOZFXHWNXJVBAWMIU
      KVHVJAFXJVBXHPVKVLXIWOFVBZVIZWPWGWSWIXEWKXLWOFWFXIXKVMZVNXLWRLWHXLWRBCFFW
      QUNZLXLBCWOWOWQFFWQXMXMXLWQVSVOALXNVBXHXKQVPVLVNXLXDHWJXLXDEDFFUPZFXCUNZH
      XLEDWTWOXCXOFXCXLWOFXMVQXMXLXCVSVOAHXPVBXHXKRVPVLVNVRVTAIMVEITVEOIMWAWBWL
      TVEAWGWIWKWCVDWDWE $.
  $}

  ${
    $d f g v x y z $.  $d v x y z U $.  $d v x y z ph $.
    rngcbasALTV.c $e |- C = ( RngCatALTV ` U ) $.
    rngcbasALTV.b $e |- B = ( Base ` C ) $.
    rngcbasALTV.u $e |- ( ph -> U e. V ) $.
    $( Set of objects of the category of non-unital rings (in a universe).
       (New usage is discouraged.)  (Contributed by AV, 27-Feb-2020.) $)
    rngcbasALTV $p |- ( ph -> B = ( U i^i Rng ) ) $=
      ( vx vy vv vz vf vg cnx cfv cop cv crnghm co crng cin chom cmpo c2nd c1st
      cbs cco cxp ccom ctp cvv c1 c5 cdc rngcvalALTV catstr baseid snsstp1 wcel
      eqidd inex1g syl strfv3 ) ABDUAUBZOUGPVEQZOUCPIJVEVEIRJRSTUDZQZOUHPKLVEVE
      UIVEMNKRZUEPZLRSTVIUFPVJSTMRNRUJUDUDZQZUKCUGULUMUMUNUOQAIJLKVECVKDNMVGEFH
      AVEVAAVGVAAVKVAUPVKVEVGUQURVFVHVLUSADEUTVEULUTHDUAEVBVCGVD $.

    $d v x y z B $.
    ${
      rngchomfvalALTV.h $e |- H = ( Hom ` C ) $.
      $( Set of arrows of the category of non-unital rings (in a universe).
         (New usage is discouraged.)  (Contributed by AV, 27-Feb-2020.) $)
      rngchomfvalALTV $p |- ( ph
                            -> H = ( x e. B , y e. B |-> ( x RngHom y ) ) ) $=
        ( vv vz vf vg cfv cop chom cv cnx cbs crnghm co cmpo cco c2nd c1st ccom
        cxp ctp rngcbasALTV eqidd rngcvalALTV fveq2d eqtrid cvv wcel wceq fvexi
        mpoex c1 c5 cdc catstr homid snsstp2 strfv mp1i eqtr4d ) AGUAUBQDRZUASQ
        BCDDBTCTUCUDZUEZRZUAUFQMNDDUJDOPMTZUGQZNTUCUDVOUHQVPUCUDOTPTUIUEUEZRZUK
        ZSQZVMAGESQVTLAEVSSABCNMDEVQFPOVMHIKADEFHIJKULAVMUMAVQUMUNUOUPVMUQURVMV
        TUSABCDDVLDEUBJUTZWAVAVMVSSUQVBVBVCVDRVQDVMVEVFVKVNVRVGVHVIVJ $.

      $d x y X $.  $d x y Y $.
      rngchomALTV.x $e |- ( ph -> X e. B ) $.
      rngchomALTV.y $e |- ( ph -> Y e. B ) $.
      $( Set of arrows of the category of non-unital rings (in a universe).
         (New usage is discouraged.)  (Contributed by AV, 27-Feb-2020.) $)
      rngchomALTV $p |- ( ph -> ( X H Y ) = ( X RngHom Y ) ) $=
        ( vx vy cv crnghm co wceq rngchomfvalALTV wa oveq12 adantl ovexd ovmpod
        cvv ) AOPGHBBOQZPQZRSZGHRSZEUGAOPBCDEFIJKLUAUHGTUIHTUBUJUKTAUHGUIHRUCUD
        MNAGHRUEUF $.

      $( A morphism of non-unital rings is a function.
         (New usage is discouraged.)  (Contributed by AV, 27-Feb-2020.) $)
      elrngchomALTV $p |- ( ph -> ( F e. ( X H Y )
                                 -> F : ( Base ` X ) --> ( Base ` Y ) ) ) $=
        ( co wcel cbs cfv eqid crnghm wf rngchomALTV eleq2d rnghmf biimtrdi ) A
        EHIFPZQEHIUAPZQHRSZIRSZEUBAUGUHEABCDFGHIJKLMNOUCUDUIUJHIEUITUJTUEUF $.
    $}

    ${
      rngccofvalALTV.o $e |- .x. = ( comp ` C ) $.
      $( Composition in the category of non-unital rings.
         (New usage is discouraged.)  (Contributed by AV, 27-Feb-2020.) $)
      rngccofvalALTV $p |- ( ph -> .x. = ( v e. ( B X. B ) , z e. B |->
                                     ( g e. ( ( 2nd ` v ) RngHom z ) ,
                                       f e. ( ( 1st ` v ) RngHom ( 2nd ` v ) )
                                       |-> ( g o. f ) ) ) ) $=
        ( cco cfv cnx cop cv cvv vx cbs chom cxp c2nd crnghm c1st ccom cmpo ctp
        vy rngcbasALTV eqid rngchomfvalALTV eqidd rngcvalALTV fveq2d wcel fvexi
        co wceq sqxpexg ax-mp mpoex c1 cdc catstr ccoid snsstp3 strfv 3eqtr4g
        c5 ) AEOPQUBPDRZQUCPEUCPZRZQOPCBDDUDZDIHCSZUEPZBSUFUTVQUGPVRUFUTISHSUHU
        IZUIZRZUJZOPZFVTAEWBOAUAUKBCDEVTGHIVNJKMADEGJKLMULAUAUKDEGVNJKLMVNUMUNA
        VTUOUPUQNVTTURVTWCVACBVPDVSDTURVPTURDEUBLUSZDTVBVCWDVDVTWBOTVEVEVLVFRVT
        DVNVGVHVMVOWAVIVJVCVK $.

      $d f g F $.  $d f g G $.  $d f g v z X $.  $d f g v z Y $.
      $d f g v z Z $.  $d f g ph $.
      rngccoALTV.x $e |- ( ph -> X e. B ) $.
      rngccoALTV.y $e |- ( ph -> Y e. B ) $.
      rngccoALTV.z $e |- ( ph -> Z e. B ) $.
      rngccoALTV.f $e |- ( ph -> F e. ( X RngHom Y ) ) $.
      rngccoALTV.g $e |- ( ph -> G e. ( Y RngHom Z ) ) $.
      $( Composition in the category of non-unital rings.
         (New usage is discouraged.)  (Contributed by AV, 27-Feb-2020.) $)
      rngccoALTV $p |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) = ( G o. F ) ) $=
        ( vg vf vv vz crnghm ccom cop cvv cxp c2nd cfv c1st cmpo rngccofvalALTV
        co cv wceq simprl fveq2d wcel op2ndg syl2anc adantr eqtrd simprr op1stg
        wa oveq12d eqidd mpoeq123dv opelxpi ovex mpoex a1i ovmpod coeq12d coexg
        ) AUAUBGFJKUEUOZIJUEUOZUAUPZUBUPZUFZGFUFZIJUGZKDUOUHAUCUDWDKBBUIZBUAUBU
        CUPZUJUKZUDUPZUEUOZWFULUKZWGUEUOZWBUMUAUBVRVSWBUMZDUHAUDUCBCDEUBUAHLMNO
        UNAWFWDUQZWHKUQZVGZVGZUAUBWIWKWBVRVSWBWPWGJWHKUEWPWGWDUJUKZJWPWFWDUJAWM
        WNURZUSAWQJUQZWOAIBUTZJBUTZWSPQIJBBVAVBVCVDZAWMWNVEVHWPWJIWGJUEWPWJWDUL
        UKZIWPWFWDULWRUSAXCIUQZWOAWTXAXDPQIJBBVFVBVCVDXBVHWPWBVIVJAWTXAWDWEUTPQ
        IJBBVKVBRWLUHUTAUAUBVRVSWBJKUEVLIJUEVLVMVNVOAVTGUQZWAFUQZVGVGVTGWAFAXEX
        FURAXEXFVEVPTSAGVRUTFVSUTWCUHUTTSGFVRVSVQVBVO $.
    $}
  $}

  ${
    $d f g h w x y z B $.  $d f g h w x y z C $.  $d f g h w x y z U $.
    $d f g h w x y z V $.  $d x ph $.  $d x X $.
    rngccatALTV.c $e |- C = ( RngCatALTV ` U ) $.
    ${
      rngccatidALTV.b $e |- B = ( Base ` C ) $.
      $( Lemma for ~ rngccatALTV .  (New usage is discouraged.)  (Contributed
         by AV, 27-Feb-2020.) $)
      rngccatidALTV $p |- ( U e. V -> ( C e. Cat
                   /\ ( Id ` C ) = ( x e. B |-> ( _I |` ( Base ` x ) ) ) ) ) $=
        ( wcel cv wa cfv co crnghm wi adantl rngchomALTV ccom com13 3imp impcom
        vw vy vz vf vg chom w3a cco cid cbs cres cvv wceq eqidd crngcALTV fvexi
        vh a1i biid crng cin simpl rngcbasALTV eleq2 simprbi biimtrdi com12 mpd
        elin eqid idrnghm syl simpr eleqtrrd cop 3ad2ant1 simp1 3ad2ant3 eleq2d
        biimpd 3exp com14 expcom rngccoALTV wf simprl simprr elrngchomALTV syl8
        ex fcoi2 a1d eqtrd simp3 adantr 3ad2ant2 expdcom simp2l rnghmco syl2anc
        fcoi1 3eltr4d coass simp2r 3eqtr4a oveq1d oveq2d 3eqtr4d iscatd2 ) DEHZ
        UAIZBHZAIZBHZJZUBIZBHZUCIZBHZJZUDIZXKXMCUFKZLZHZUEIZXMXPYBLZHZUQIZXPXRY
        BLZHZUGZUGZUAAUBUCBCCUHKZUIXMUJKZUKZUDUEUQYBULBCUJKUMXJGURXJYBUNXJYMUNC
        ULHXJCDUOFUPURYLUSXJXNJZYOXMXMMLZXMXMYBLYPXMUTHZYOYQHZYPBDUTVAZUMZYRYPB
        CDEFGXJXNVBZVCXNUUAYRNXJUUAXNYRUUAXNXMYTHZYRBYTXMVDUUCXMDHYRXMDUTVIVEVF
        VGOVHYNXMYNVJVKVLZYPBCDYBEXMXMFGUUBYBVJZXJXNVMZUUFPVNXJYLJZYOYAXKXMVOZX
        MYMLLYOYAQZYAUUGBCYMDYAYOEXKXMXMFGXJYLVBZYMVJZYLXLXJXOXTXLYKXLXNVBZVPOZ
        YLXNXJXOXTXNYKXLXNVMZVPOZUUOYLXJYAXKXMMLZHZXOXTYKXJUUQNZYKXTXOUURYDYGXT
        XOUURNNYJXJXTXOYDUUQXJXTXOYDUUQNXJXTXOUGZYDUUQUUSYCUUPYAUUSBCDYBEXKXMFG
        XJXTXOVQZUUEXOXJXLXTUULVRXOXJXNXTUUNVRZPVSVTWAWBVPRSTZYLXJYSXOXTXJYSNZY
        KXNUVCXLXJXNYSUUDWCOZVPTWDYLXJUUIYAUMZXOXTYKXJUVENZXOYKUVFNXTYKXOUVFYDY
        GXOUVFNYJYDXOXJXKUJKZYNYAWEZUVEXJXOYDUVHXJXOYDUVHNXJXOJBCDYAYBEXKXMFGXJ
        XOVBUUEXJXLXNWFXJXLXNWGWHWJRUVGYNYAWKWIVPVGWLSTWMYLXJYEYOXMXMVOXPYMLLZY
        EUMZXOXTYKXJUVJNZYKXOXTUVKYGYDXOXTJZUVKNYJYGUVLXJUVJYGUVLXJUGZUVIYEYOQZ
        YEUVMBCYMDYOYEEXMXMXPFGYGUVLXJWNUUKUVLYGXNXJXOXNXTUUNWOZWPZUVPUVLYGXQXJ
        XOXQXSWFZWPYGUVLXJYSUVLUVCNYGXOUVCXTUVDWOURSYGUVLXJYEXMXPMLZHZXJUVLYGUV
        SXJUVLYGUVSNZXJUVLJZYGUVSUWAYFUVRYEUWABCDYBEXMXPFGXJUVLVBZUUEUVLXNXJUVO
        OZUVLXQXJUVQOZPVSVTWJRSWDUVMYNXPUJKZYEWEZUVNYEUMYGUVLXJUWFXJUVLYGUWFXJU
        VLYGUWFNUWABCDYEYBEXMXPFGUWBUUEUWCUWDWHWJRSYNUWEYEXAVLWMWAWPWQSTUUGYEYA
        QZXKXPMLZYEYAUUHXPYMLLZXKXPYBLUUGUVSUUQUWGUWHHYLXJUVSXOXTYKXJUVSNZYKXTX
        OUWJYGYDXTXOUWJNNYJXJXTXOYGUVSXJXTXOUVTUUSYGUVSUUSYFUVRYEUUSBCDYBEXMXPF
        GUUTUUEUVAXJXQXSXOWRZPVSVTWAWBWPRSTZUVBXKXMXPYEYAWSWTZUUGBCYMDYAYEEXKXM
        XPFGUUJUUKUUMUUOYLXQXJXOXQXSYKWROZUVBUWLWDZUUGBCDYBEXKXPFGUUJUUEUUMUWNP
        XBUUGYHYEQZYAUUHXRYMLZLZYHUWGXKXPVOXRYMLZLZYHYEXMXPVOXRYMLLZYAUWQLYHUWI
        UWSLUUGUWPYAQYHUWGQUWRUWTYHYEYAXCUUGBCYMDYAUWPEXKXMXRFGUUJUUKUUMUUOYLXS
        XJXOXQXSYKXDOZUVBUUGYHXPXRMLZHZUVSUWPXMXRMLHYLXJUXDXOXTYKXJUXDNZYKXTXOU
        XEYJYDXTXOUXENNYGXJXTXOYJUXDXJXTXOYJUXDNUUSYJUXDUUSYIUXCYHUUSBCDYBEXPXR
        FGUUTUUEUWKXJXQXSXOXDPVSVTWAWBVRRSTZUWLXMXPXRYHYEWSWTWDUUGBCYMDUWGYHEXK
        XPXRFGUUJUUKUUMUWNUXBUWMUXFWDXEUUGUXAUWPYAUWQUUGBCYMDYEYHEXMXPXRFGUUJUU
        KUUOUWNUXBUWLUXFWDXFUUGUWIUWGYHUWSUWOXGXHXI $.
    $}

    $( The category of non-unital rings is a category.  (Contributed by AV,
       27-Feb-2020.)  (New usage is discouraged.) $)
    rngccatALTV $p |- ( U e. V -> C e. Cat ) $=
      ( vx wcel ccat ccid cfv cbs cid cres cmpt wceq eqid rngccatidALTV simpld
      cv ) BCFAGFAHIEAJIZKERJILMNESABCDSOPQ $.

    rngcidALTV.b $e |- B = ( Base ` C ) $.
    rngcidALTV.o $e |- .1. = ( Id ` C ) $.
    rngcidALTV.u $e |- ( ph -> U e. V ) $.
    rngcidALTV.x $e |- ( ph -> X e. B ) $.
    rngcidALTV.s $e |- S = ( Base ` X ) $.
    $( The identity arrow in the category of non-unital rings is the identity
       function.  (Contributed by AV, 27-Feb-2020.)
       (New usage is discouraged.) $)
    rngcidALTV $p |- ( ph -> ( .1. ` X ) = ( _I |` S ) ) $=
      ( vx cfv cid cbs cvv wcel cres cv ccid cmpt ccat rngccatidALTV syl simprd
      wceq eqtrid fveq2 adantl reseq2d fvex resiexg mp1i fvmptd reseq2i eqtr4di
      wa ) AHFPQHRPZUAZQDUAAOHQOUBZRPZUAZVBBFSAFCUCPZOBVEUDZKACUETZVFVGUIZAEGTV
      HVIUTLOBCEGIJUFUGUHUJAVCHUIZUTVDVAQVJVDVAUIAVCHRUKULUMMVASTVBSTAHRUNVASUO
      UPUQDVAQNURUS $.
  $}

  ${
    rngcsectALTV.c $e |- C = ( RngCatALTV ` U ) $.
    rngcsectALTV.b $e |- B = ( Base ` C ) $.
    rngcsectALTV.u $e |- ( ph -> U e. V ) $.
    rngcsectALTV.x $e |- ( ph -> X e. B ) $.
    rngcsectALTV.y $e |- ( ph -> Y e. B ) $.
    ${
      rngcsectALTV.e $e |- E = ( Base ` X ) $.
      rngcsectALTV.n $e |- S = ( Sect ` C ) $.
      $( A section in the category of non-unital rings, written out.
         (Contributed by AV, 28-Feb-2020.)  (New usage is discouraged.) $)
      rngcsectALTV $p |- ( ph -> ( F ( X S Y ) G <-> ( F e. ( X RngHom Y )
                   /\ G e. ( Y RngHom X ) /\ ( G o. F ) = ( _I |` E ) ) ) ) $=
        ( co wcel wbr chom cfv cop cco ccid wceq w3a crnghm ccom cres eqid ccat
        cid rngccatALTV syl issect rngchomALTV eleq2d anbi12d anbi1d rngccoALTV
        adantr simprl simprr rngcidALTV eqeq12d pm5.32da bitrd df-3an 3bitr4g
        wa ) AGHJKDSUAGJKCUBUCZSZTZHKJVMSZTZHGJKUDJCUEUCZSSZJCUFUCZUCZUGZUHZGJK
        UISZTZHKJUISZTZHGUJZUNFUKZUGZUHZABCDVRVTGHVMJKMVMULZVRULZVTULZRAEITZCUM
        TNCEILUOUPOPUQAVOVQVLZWBVLZWEWGVLZWJVLZWCWKAWQWRWBVLWSAWPWRWBAVOWEVQWGA
        VNWDGABCEVMIJKLMNWLOPURUSAVPWFHABCEVMIKJLMNWLPOURUSUTVAAWRWBWJAWRVLZVSW
        HWAWIWTBCVREGHIJKJLMAWOWRNVCWMAJBTWROVCZAKBTWRPVCXAAWEWGVDAWEWGVEVBAWAW
        IUGWRABCFEVTIJLMWNNOQVFVCVGVHVIVOVQWBVJWEWGWJVJVKVI $.
    $}

    ${
      rngcinvALTV.n $e |- N = ( Inv ` C ) $.
      $( An inverse in the category of non-unital rings is the converse
         operation.  (Contributed by AV, 28-Feb-2020.)
         (New usage is discouraged.) $)
      rngcinvALTV $p |- ( ph -> ( F ( X N Y ) G
                              <-> ( F e. ( X RngIso Y ) /\ G = `' F ) ) ) $=
        ( co wa wcel wceq wbr csect cfv crnghm ccom cid cres crngim rngccatALTV
        cbs ccnv ccat syl eqid isinv rngcsectALTV df-3an bitrdi 3ancoma anbi12d
        w3a bitri anandi wf1o simplrl adantl wf anim12i ad2antlr simpr ad2antrl
        rnghmf jca32 fcof1o eqcom anbi2i sylib anass sylanbrc wb syl2anc anbi1d
        isrngim2 adantr mpbird rngimrnghm isrngim eleq1 eqcoms anbi2d sylan9bbr
        biimtrdi com12 expdimp coeq1 ad2antll rngimf1o f1ococnv1 eqtrd jca31 wi
        impcom biimpcd coeq2 f1ococnv2 impbida 3bitrd ) AEFIJGQUAEFIJCUBUCZQUAZ
        FEJIXHQUAZRZEIJUDQSZFJIUDQZSZRZFEUEZUFIUJUCZUGZTZRZXORZXTEFUEZUFJUJUCZU
        GZTZRZRZEIJUHQSZFEUKZTZRZABCXHEFGIJLPADHSCULSMCDHKUIUMNOXHUNZUOAXKXTXOY
        ERZRYGAXIXTXJYMAXIXLXNXSVAXTABCXHDXQEFHIJKLMNOXQUNZYLUPXLXNXSUQURAXJXNX
        LYEVAZYMABCXHDYCFEHJIKLMONYCUNZYLUPYOXLXNYEVAYMXNXLYEUSXLXNYEUQVBURUTXT
        XOYEVCURAYGYKAYGRZYKXLXQYCEVDZRZYJRZYQXLYRYJRZYTYGXLAXTXLXNYFVEVFYQXQYC
        EVGZYCXQFVGZRZYEXSRRZUUAYGUUEAYGUUDYEXSXOUUDXTYFXLUUBXNUUCXQYCIJEYNYPVL
        YCXQJIFYPYNVLVHVIYFYEYAXTYEVJVFXTXSYAYEXOXSVJVKVMVFUUEYRYIFTZRUUAXQYCEF
        VNUUFYJYRYIFVOVPVQUMXLYRYJVRVSAYKYTVTYGAYHYSYJAIBSZJBSZYHYSVTNOXQYCIJEB
        BYNYPWCWAWBWDWEAYKRZXTXOYFUUIXLXNXSYHXLAYJXQYCIJEYNYPWFVKYKAXNYHYJAXNYJ
        ARZYHXNUUJYHXOXNAYHXLYIXMSZRZYJXOAUUGUUHYHUULVTNOIJEBBWGWAZYJUUKXNXLUUK
        XNVTYIFYIFXMWHWIWJWKXLXNVJWLWMWNXBUUIXPYIEUEZXRYJXPUUNTAYHFYIEWOWPUUIYR
        UUNXRTYHYRAYJXQYCIJEYNYPWQVKZXQYCEWRUMWSZWTUUIXOUULYKAUULYHAUULXAYJAYHU
        ULUUMXCWDXBUUIXNUUKXLYJXNUUKVTAYHFYIXMWHWPWJWEZUUIXOXSYEUUQUUPUUIYBEYIU
        EZYDYJYBUURTAYHFYIEXDWPUUIYRUURYDTUUOXQYCEXEUMWSWTWTXFXG $.
    $}

    ${
      rngcisoALTV.n $e |- I = ( Iso ` C ) $.
      $( An isomorphism in the category of non-unital rings is a bijection.
         (Contributed by AV, 28-Feb-2020.)  (New usage is discouraged.) $)
      rngcisoALTV $p |- ( ph -> ( F e. ( X I Y )
                                  <-> F e. ( X RngIso Y ) ) ) $=
        ( co wcel cfv eqid syl cinv cdm crngim ccat rngccatALTV isoval wbr wfun
        eleq2d wb invfun funfvbrb ccnv wceq wa rngcinvALTV biimtrdi sylbid wrel
        simpl wi funrel releldm ex sylbird mpan2i impbid bitrd ) AEHIFPZQEHICUA
        RZPZUBZQZEHIUCPQZAVIVLEABCFVJHIKVJSZADGQCUDQLCDGJUETZMNOUFUIAVMVNAVMEEV
        KRZVKUGZVNAVKUHZVMVRUJABCVJHIKVOVPMNUKZEVKULTAVRVNVQEUMZUNZUOVNABCDEVQV
        JGHIJKLMNVOUPVNWBUTUQURAVNWAWAUNZVMWASAVNWCUOEWAVKUGZVMABCDEWAVJGHIJKLM
        NVOUPAVKUSZWDVMVAAVSWEVTVKVBTWEWDVMEWAVKVCVDTVEVFVGVH $.
    $}
  $}

  ${
    $d B x y $.  $d U x y $.  $d ph x y $.
    rngchomffvalALTV.c $e |- C = ( RngCatALTV ` U ) $.
    rngchomffvalALTV.b $e |- B = ( Base ` C ) $.
    rngchomffvalALTV.u $e |- ( ph -> U e. V ) $.
    rngchomffvalALTV.h $e |- F = ( Homf ` C ) $.
    $( The value of the functionalized Hom-set operation in the category of
       non-unital rings (in a universe) in maps-to notation for an operation.
       (Contributed by AV, 1-Mar-2020.)  (New usage is discouraged.) $)
    rngchomffvalALTV $p |- ( ph
                            -> F = ( x e. B , y e. B |-> ( x RngHom y ) ) ) $=
      ( chom cfv cv crnghm co wceq wfn eqid cmpo cxp rngchomfvalALTV ovex fneq1
      fnmpoi mpbiri fnhomeqhomf 3syl eqtrd ) AGEMNZBCDDBOZCOZPQZUAZAUKUORZUKDDU
      BZSZGUKRABCDEFUKHIJKUKTZUCZUPURUOUQSBCDDUNUOUOTULUMPUDUFUQUKUOUEUGDEGUKLJ
      USUHUIUTUJ $.
  $}

  ${
    $d C x y $.  $d U x y $.  $d ph x y $.  $d r s v w f x y $.
    rngchomrnghmresALTV.c $e |- C = ( RngCatALTV ` U ) $.
    rngchomrnghmresALTV.b $e |- B = ( Rng i^i U ) $.
    rngchomrnghmresALTV.u $e |- ( ph -> U e. V ) $.
    rngchomrnghmresALTV.f $e |- F = ( Homf ` C ) $.
    $( The value of the functionalized Hom-set operation in the category of
       non-unital rings (in a universe) as restriction of the non-unital ring
       homomorphisms.  (Contributed by AV, 2-Mar-2020.)
       (New usage is discouraged.) $)
    rngchomrnghmresALTV $p |- ( ph -> F = ( RngHom |` ( B X. B ) ) ) $=
      ( vx vy vv vw crng cv crnghm co cfv wceq vr vs cmpo cbs cxp cres wss eqid
      vf cin rngcbasALTV inss2 eqsstrdi resmpo syl2anc wfn cplusg cmulr wa wral
      cmap crab csb df-rnghm ovex rabex csbex fnmpoi a1i sylib 3eqtr4rd sqxpeqd
      fnov incom reseq12d rngchomffvalALTV ) AKLOOKPZLPZQRZUCZCUDSZWAUEZUFZKLWA
      WAVSUCZQBBUEZUFEAWAOUGZWFWCWDTAWADOUJZOAWACDFGWAUHZIUKZDOULUMZWJKLOOWAWAV
      SUNUOAQVTWEWBAQOOUEUPZQVTTWKAUAUBOOMUAPZUDSZNUBPZUDSZVQVRWLUQSRUIPZSVQWPS
      ZVRWPSZWNUQSRTVQVRWLURSRWPSWQWRWNURSRTUSLMPZUTKWSUTZUINPZWSVARZVBZVCZVCQK
      LNMUIUBUAVDMWMXDNWOXCWTUIXBXAWSVAVEVFVGVGVHVIKLOOQVMVJABWAAWGODUJZWABWGXE
      TADOVNVIWIBXETAHVIVKVLVOAKLWACDEFGWHIJVPVK $.
  $}

  ${
    rngcrescrhmALTV.u $e |- ( ph -> U e. V ) $.
    rngcrescrhmALTV.c $e |- C = ( RngCatALTV ` U ) $.
    rngcrescrhmALTV.r $e |- ( ph -> R = ( Ring i^i U ) ) $.
    rngcrescrhmALTV.h $e |- H = ( RingHom |` ( R X. R ) ) $.
    $( The category of non-unital rings (in a universe) restricted to the ring
       homomorphisms between unital rings (in the same universe).  (Contributed
       by AV, 1-Mar-2020.)  (New usage is discouraged.) $)
    rngcrescrhmALTV $p |- ( ph -> ( C |`cat H )
                           = ( ( C |`s R ) sSet <. ( Hom ` ndx ) , H >. ) ) $=
      ( cresc co cvv wcel crg cin crh cxp wfn wss crngcALTV fvexi eqtrdi inex1g
      eqid a1i incom syl eqeltrd cres inss1 eqsstrdi xpss12 syl2anc wb fnssresb
      rhmfn mp1i mpbird fneq1i sylibr rescval2 ) ABBEKLZCEMMVCUEBMNABDUAHUBUFAC
      DOPZMACODPZVDIODUGUCADFNVDMNGDOFUDUHUIAQCCRZUJZVFSZEVFSAVHVFOORZTZACOTZVK
      VJACVEOIODUKULZVLCOCOUMUNQVISVHVJUOAUQVIVFQUPURUSVFEVGJUTVAVB $.

    $d R x y $.
    $( Lemma 1 for ~ rhmsubcALTV .  (Contributed by AV, 2-Mar-2020.)
       (New usage is discouraged.) $)
    rhmsubcALTVlem1 $p |- ( ph -> H Fn ( R X. R ) ) $=
      ( vx vy wfn cv cghm co cmgp crh crg wceq cxp cfv cmhm cin cmpo eqid inex1
      ovex fnmpoi cres a1i dfrhm2 reseq1d eqsstrdi resmpo syl2anc 3eqtrd fneq1d
      wss inss1 mpbiri ) AECCUAZMKLCCKNZLNZOPZVCQUBVDQUBUCPZUDZUEZVBMKLCCVGVHVH
      UFVEVFVCVDOUHUGUIAVBEVHAERVBUJZKLSSVGUEZVBUJZVHEVITAJUKARVJVBRVJTALKULUKU
      MACSUSZVLVKVHTACSDUDSISDUTUNZVMKLSSCCVGUOUPUQURVA $.

    $( Lemma 2 for ~ rhmsubcALTV .  (Contributed by AV, 2-Mar-2020.)
       (New usage is discouraged.) $)
    rhmsubcALTVlem2 $p |- ( ( ph /\ X e. R /\ Y e. R )
                           -> ( X H Y ) = ( X RingHom Y ) ) $=
      ( wcel w3a cop crh cxp cfv co df-ov opelxpi 3adant1 fvresd fveq1i 3eqtr4g
      cres eqtri ) AGCMZHCMZNZGHOZPCCQZUFZRZUKPRGHESZGHPSUJUKULPUHUIUKULMAGHCCU
      AUBUCUOUKERUNGHETUKEUMLUDUGGHPTUE $.

    $d U y $.  $d V y $.  $d ph y $.
    $( Lemma 3 for ~ rhmsubcALTV .  (Contributed by AV, 2-Mar-2020.)
       (New usage is discouraged.) $)
    rhmsubcALTVlem3 $p |- ( ( ph /\ x e. R )
                       -> ( ( Id ` ( RngCatALTV ` U ) ) ` x ) e. ( x H x ) ) $=
      ( vy wcel wa cid cbs cfv crg cin wceq cv cres co crngcALTV eleq2d elinel1
      crh ccid biimtrdi imp eqid idrhm syl ccat cmpt adantr rngccatidALTV simpr
      cvv 3syl weq fveq2 reseq2d adantl crng eqtrdi ringrng anim2i elin 3imtr4i
      incom eqcomi fveq2i rngcbasALTV eleqtrrd resiexd rhmsubcALTVlem2 3anidm23
      fvexd fvmptd 3eltr4d ) ABUAZDMZNZOWBPQZUBZWBWBUGUCZWBEUDQZUHQZQWBWBFUCZWD
      WBRMZWFWGMAWCWKAWCWBRESZMWKADWLWBJUEWBREUFUIUJWEWBWEUKULUMWDLWBOLUAZPQZUB
      ZWFWHPQZWIUSWDEGMZWHUNMZWILWPWOUOTZNWSAWQWCHUPLWPWHEGWHUKWPUKUQWRWSURUTLB
      VAZWOWFTWDWTWNWEOWMWBPVBVCVDWDWBEVESZWPAWCWBXAMZAWCWBERSZMZXBADXCWBADWLXC
      JREVKVFUEWBEMZWKNXEWBVEMZNXDXBWKXFXEWBVGVHWBERVIWBEVEVIVJUIUJAWPXATWCAWPC
      EGIWHCPCWHIVLVMHVNUPVOWDWEUSWDWBPVSVPVTAWCWJWGTACDEFGWBWBHIJKVQVRWA $.

    $d R x y z $.  $d ph x $.
    $( Lemma 4 for ~ rhmsubcALTV .  (Contributed by AV, 2-Mar-2020.)
       (New usage is discouraged.) $)
    rhmsubcALTVlem4 $p |- ( ( ( ( ph /\ x e. R ) /\ ( y e. R /\ z e. R ) )
                             /\ ( f e. ( x H y ) /\ g e. ( y H z ) ) )
   -> ( g ( <. x , y >. ( comp ` ( RngCatALTV ` U ) ) z ) f ) e. ( x H z ) ) $=
      ( wcel wa co adantr crg ccom crh cop crngcALTV cfv cco simpl simpr adantl
      wceq rhmsubcALTVlem2 syl3anc eleq2d anbi12d rhmco ancoms biimtrdi imp cbs
      cv eqid ad3antrrr cin crng incom wss ringrng a1i ssrdv sslin syl eqsstrid
      wi rngcbasALTV 3sstr4d sselda impcom adantld crnghm rhmisrnghm rngccoALTV
      sseld com12 3eltr4d ) ABUTZFPZQZCUTZFPZDUTZFPZQZQZHUTZWEWHJRZPZIUTZWHWJJR
      ZPZQZQZWQWNUAZWEWJUBRZWQWNWEWHUCWJGUDUEZUFUEZRRWEWJJRZWMWTXBXCPZWMWTWNWEW
      HUBRZPZWQWHWJUBRZPZQXGWMWPXIWSXKWMWOXHWNWMAWFWIWOXHUJWGAWLAWFUGSZWGWFWLAW
      FUHSZWLWIWGWIWKUGUIZAEFGJKWEWHLMNOUKULUMZWMWRXJWQWMAWIWKWRXJUJXLXNWLWKWGW
      IWKUHUIZAEFGJKWHWJLMNOUKULUMZUNXKXIXGWEWHWJWQWNUOUPUQURXAXDUSUEZXDXEGWNWQ
      KWEWHWJXDVAZXRVAZAGKPWFWLWTLVBXEVAWMWEXRPZWTWGYAWLAFXRWEATGVCZGVDVCZFXRAY
      BGTVCZYCTGVEATVDVFYDYCVFABTVDWETPWEVDPVMAWEVGVHVITVDGVJVKVLNAXRXDGKXSXTLV
      NVOZVPSSWMWHXRPZWTWLWGYFWIWGYFVMWKWGWIYFAWIYFVMWFAFXRWHYEWBSWCSVQSWMWJXRP
      ZWTWGWLYGWGWKYGWIAWKYGVMWFAFXRWJYEWBSVRURSWTWMWNWEWHVSRPZWPWMYHVMWSWMWPYH
      WMWPXIYHXOWEWHWNVTUQWCSVQWMWTWQWHWJVSRPZWMWSYIWPWMWSXKYIXQWHWJWQVTUQVRURW
      AWMXFXCUJZWTWMAWFWKYJXLXMXPAEFGJKWEWJLMNOUKULSWD $.

    $d H f g x y z $.  $d R f g $.  $d U f g x z $.  $d ph f g z $.
    $( According to ~ df-subc , the subcategories ` ( Subcat `` C ) ` of a
       category ` C ` are subsets of the homomorphisms of ` C ` (see ~ subcssc
       and ~ subcss2 ).  Therefore, the set of unital ring homomorphisms is a
       "subcategory" of the category of non-unital rings.  (Contributed by AV,
       2-Mar-2020.)  (New usage is discouraged.) $)
    rhmsubcALTV $p |- ( ph -> H e. ( Subcat ` ( RngCatALTV ` U ) ) ) $=
      ( vx vg vf vy vz cfv wcel cv co wral crngcALTV csubc cssc wbr ccid cop wa
      chomf cco crh cres crnghm crng eqidd rhmsscrnghm wceq rngchomrnghmresALTV
      cxp cin eqid 3brtr4d rhmsubcALTVlem3 rhmsubcALTVlem4 ralrimivva ralrimiva
      a1i jca ccat rngccatALTV syl rhmsubcALTVlem1 issubc2 mpbir2and ) AEDUAPZU
      BPQEVNUHPZUCUDKRZVNUEPZPVPVPESQZLRMRVPNRZUFORZVNUIPZSSVPVTESQZLVSVTESZTMV
      PVSESZTZOCTNCTZUGZKCTAUJCCURUKZULUMDUSZWIURUKEVOUCACWIDFGIAWIUNUOEWHUPAJV
      FAWIVNDVOFVNUTZWIUTGVOUTZUQVAAWGKCAVPCQUGZVRWFAKBCDEFGHIJVBWLWENOCCWLVSCQ
      VTCQUGUGWBMLWDWCAKNOBCDMLEFGHIJVCVDVDVGVEAKNOVNCWAVQMLVOEWKVQUTWAUTADFQVN
      VHQGVNDFWJVIVJABCDEFGHIJVKVLVM $.

    $( The restriction of the category of non-unital rings to the set of unital
       ring homomorphisms is a category.  (Contributed by AV, 4-Mar-2020.)
       (New usage is discouraged.) $)
    rhmsubcALTVcat $p |- ( ph -> ( ( RngCatALTV ` U ) |`cat H ) e. Cat ) $=
      ( crngcALTV cfv cresc co eqid rhmsubcALTV subccat ) ADKLZREMNZESOABCDEFGH
      IJPQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The category of (unital) rings (alternate definition)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  As an alternative to ~ df-ringc , the "category of unital rings" can be
  defined as extensible structure consisting of three components/slots for the
  objects, morphisms and composition, according to ~ dfringc2 .

$)

  $c RingCatALTV $.

  $( Extend class notation to include the category Ring.
     (New usage is discouraged.) $)
  cringcALTV $a class RingCatALTV $.

  ${
    $d b f g u v x y z $.
    $( Definition of the category Ring, relativized to a subset ` u ` .  This
       is the category of all rings in ` u ` and homomorphisms between these
       rings.  Generally, we will take ` u ` to be a weak universe or
       Grothendieck universe, because these sets have closure properties as
       good as the real thing.  (Contributed by AV, 13-Feb-2020.)
       (New usage is discouraged.) $)
    df-ringcALTV $a |- RingCatALTV = ( u e. _V |-> [_ ( u i^i Ring ) / b ]_
              { <. ( Base ` ndx ) , b >. ,
                <. ( Hom ` ndx ) , ( x e. b , y e. b |-> ( x RingHom y ) ) >. ,
                <. ( comp ` ndx ) , ( v e. ( b X. b ) , z e. b |->
                                     ( g e. ( ( 2nd ` v ) RingHom z ) ,
                                       f e. ( ( 1st ` v ) RingHom ( 2nd ` v ) )
                                       |-> ( g o. f ) ) ) >. } ) $.

    $d b u v x y z B $.  $d b u v x y z U $.  $d b u .x. $.  $d b u H $.
    $d b u v x y z ph $.
    ringcvalALTV.c $e |- C = ( RingCatALTV ` U ) $.
    ringcvalALTV.u $e |- ( ph -> U e. V ) $.
    ringcvalALTV.b $e |- ( ph -> B = ( U i^i Ring ) ) $.
    ringcvalALTV.h $e |- ( ph -> H = ( x e. B , y e. B
                                      |-> ( x RingHom y ) ) ) $.
    ringcvalALTV.o $e |- ( ph -> .x. = ( v e. ( B X. B ) , z e. B |->
                                     ( g e. ( ( 2nd ` v ) RingHom z ) ,
                                       f e. ( ( 1st ` v ) RingHom ( 2nd ` v ) )
                                       |-> ( g o. f ) ) ) ) $.
    $( Value of the category of rings (in a universe).  (Contributed by AV,
       13-Feb-2020.)  (New usage is discouraged.) $)
    ringcvalALTV $p |- ( ph -> C = { <. ( Base ` ndx ) , B >. ,
                    <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .x. >. } ) $=
      ( cv cvv vu vb cringcALTV cfv cnx cbs cop chom cco ctp crg cin crh co cxp
      cmpo c2nd c1st ccom csb cmpt wceq df-ringcALTV wa wcel inex1 ineq1 adantl
      a1i adantr eqtr4d simpr opeq2d eqidd mpoeq123dv ad2antrr sqxpeqd tpeq123d
      vex csbied2 elex syl tpex fvmptd eqtrid ) AGIUCUDUEUFUDZFUGZUEUHUDZLUGZUE
      UIUDZHUGZUJZNAUAIUBUASZUKULZWFUBSZUGZWHBCWOWOBSCSUMUNZUPZUGZWJEDWOWOUOZWO
      KJESZUQUDZDSUMUNXAURUDXBUMUNKSJSUSUPZUPZUGZUJZUTZWLTUCTUCUATXGVAVBABCDEUA
      JKUBVCVIAWMIVBZVDZUBWNFXFWLTWNTVEXIWMUKUAVSVFVIXIWNIUKULZFXHWNXJVBAWMIUKV
      GVHAFXJVBXHPVJVKXIWOFVBZVDZWPWGWSWIXEWKXLWOFWFXIXKVLZVMXLWRLWHXLWRBCFFWQU
      PZLXLBCWOWOWQFFWQXMXMXLWQVNVOALXNVBXHXKQVPVKVMXLXDHWJXLXDEDFFUOZFXCUPZHXL
      EDWTWOXCXOFXCXLWOFXMVQXMXLXCVNVOAHXPVBXHXKRVPVKVMVRVTAIMVEITVEOIMWAWBWLTV
      EAWGWIWKWCVIWDWE $.
  $}

  ${
    $d B x $.  $d X x $.  $d ph x $.
    funcringcsetcALTV2.r $e |- R = ( RingCat ` U ) $.
    funcringcsetcALTV2.s $e |- S = ( SetCat ` U ) $.
    funcringcsetcALTV2.b $e |- B = ( Base ` R ) $.
    funcringcsetcALTV2.c $e |- C = ( Base ` S ) $.
    funcringcsetcALTV2.u $e |- ( ph -> U e. WUni ) $.
    funcringcsetcALTV2.f $e |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) ) $.
    $( Lemma 1 for ~ funcringcsetcALTV2 .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetcALTV2lem1 $p |- ( ( ph /\ X e. B )
                                  -> ( F ` X ) = ( Base ` X ) ) $=
      ( wcel wa cbs cfv wceq cv cvv cmpt adantr fveq2 adantl simpr fvexd fvmptd
      ) AICPZQZBIBUAZRSZIRSZCHUBAHBCUMUCTUJOUDULITUMUNTUKULIRUEUFAUJUGUKIRUHUI
      $.

    $( Lemma 2 for ~ funcringcsetcALTV2 .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetcALTV2lem2 $p |- ( ( ph /\ X e. B ) -> ( F ` X ) e. U ) $=
      ( wcel wa cfv cbs funcringcsetcALTV2lem1 ringcbasbas eqeltrd ) AICPQIHRIS
      RGABCDEFGHIJKLMNOTACEIGJLNUAUB $.

    $d C x $.
    $( Lemma 3 for ~ funcringcsetcALTV2 .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetcALTV2lem3 $p |- ( ph -> F : B --> C ) $=
      ( wf cv cbs cfv cmpt wcel wa ringcbasbas wceq cwun eqcomd adantr eleqtrrd
      setcbas eleqtrrdi fmpttd feq1d mpbird ) ACDHOCDBCBPZQRZSZOABCUNDAUMCTZUAZ
      UNFQRZDUQUNGURACEUMGIKMUBAURGUCUPAGURAFGUDJMUHUEUFUGLUIUJACDHUONUKUL $.

    $d B x y $.
    funcringcsetcALTV2.g $e |- ( ph -> G = ( x e. B , y e. B
                                        |-> ( _I |` ( x RingHom y ) ) ) ) $.
    $( Lemma 4 for ~ funcringcsetcALTV2 .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetcALTV2lem4 $p |- ( ph -> G Fn ( B X. B ) ) $=
      ( wfn cv cvv cxp cid crh co cres cmpo eqid wcel ovex resiexd ax-mp fnmpoi
      id fneq1d mpbiri ) AJDDUAZRBCDDUBBSZCSZUCUDZUEZUFZUPRBCDDUTVAVAUGUSTUHZUT
      TUHUQURUCUIVBUSTVBUMUJUKULAUPJVAQUNUO $.

    $d X y $.  $d Y x y $.  $d ph y $.
    $( Lemma 5 for ~ funcringcsetcALTV2 .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetcALTV2lem5 $p |- ( ( ph /\ ( X e. B /\ Y e. B ) )
        -> ( X G Y ) = ( _I |` ( X RingHom Y ) ) ) $=
      ( wa wcel cid cv crh co cres cvv cmpo adantr oveq12 adantl reseq2d simprl
      wceq simprr ovexd resiexd ovmpod ) AKDUAZLDUAZTZTZBCKLDDUBBUCZCUCZUDUEZUF
      ZUBKLUDUEZUFJUGAJBCDDVFUHUNVASUIVBVCKUNVDLUNTZTVEVGUBVHVEVGUNVBVCKVDLUDUJ
      UKULAUSUTUMAUSUTUOVBVGUGVBKLUDUPUQUR $.

    $( Lemma 6 for ~ funcringcsetcALTV2 .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetcALTV2lem6 $p |- ( ( ph /\ ( X e. B /\ Y e. B )
                        /\ H e. ( X RingHom Y ) ) -> ( ( X G Y ) ` H ) = H ) $=
      ( wcel wa crh w3a cfv cid cres wceq funcringcsetcALTV2lem5 3adant3 fveq1d
      co fvresi 3ad2ant3 eqtrd ) ALDUAMDUAUBZKLMUCULZUAZUDZKLMJULZUEKUFUQUGZUEZ
      KUSKUTVAAUPUTVAUHURABCDEFGHIJLMNOPQRSTUIUJUKURAVBKUHUPUQKUMUNUO $.

    $( Lemma 7 for ~ funcringcsetcALTV2 .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetcALTV2lem7 $p |- ( ( ph /\ X e. B )
        -> ( ( X G X ) ` ( ( Id ` R ) ` X ) ) = ( ( Id ` S ) ` ( F ` X ) ) ) $=
      ( wcel cfv wa ccid cid cbs cres wceq funcringcsetcALTV2lem5 anabsan2 cwun
      co crh eqid adantr simpr ringcid fveq12d crg ringcbas eleq2d elin simprbi
      cin biimtrdi fvresi 3syl funcringcsetcALTV2lem1 fveq2d ringcbasbas setcid
      imp idrhm eqtr2d 3eqtrd ) AKDSZUAZKFUBTZTZKKJUJZTUCKUDTZUEZUCKKUKUJZUEZTZ
      VTKITZGUBTZTZVOVQVTVRWBAVNVRWBUFABCDEFGHIJKKLMNOPQRUGUHVODFVSHVPUIKLNVPUL
      AHUISVNPUMZAVNUNVSULZUOUPVOKUQSZVTWASWCVTUFAVNWIAVNKHUQVBZSZWIADWJKADFHUI
      LNPURUSWKKHSWIKHUQUTVAVCVJVSKWHVKWAVTVDVEVOWFVSWETVTVOWDVSWEABDEFGHIKLMNO
      PQVFVGVOGHWEUIVSMWEULWGADFKHLNPVHVIVLVM $.

    $d B f $.  $d F f $.  $d X f $.  $d Y f $.  $d ph f $.
    $( Lemma 8 for ~ funcringcsetcALTV2 .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetcALTV2lem8 $p |- ( ( ph /\ ( X e. B /\ Y e. B ) )
                    -> ( X G Y ) : ( X ( Hom ` R ) Y )
                                   --> ( ( F ` X ) ( Hom ` S ) ( F ` Y ) ) ) $=
      ( wcel vf wa chom cfv co wf crh cmap cid cres wf1o f1oi f1of mp1i cv eqid
      cbs rhmf cvv fvex pm3.2i elmapg bicomd biimpa wceq funcringcsetcALTV2lem1
      wb simpr sylan2 simpl oveq12d adantr eleqtrrd syl5 funcringcsetcALTV2lem5
      ex ssrdv fssd cwun adantl ringchom funcringcsetcALTV2lem2 setchom feq123d
      mpbird ) AKDTZLDTZUBZUBZKLFUCUDZUEZKIUDZLIUDZGUCUDZUEZKLJUEZUFKLUGUEZWMWL
      UHUEZUIWQUJZUFWIWQWQWRWSWQWQWSUKWQWQWSUFWIWQULWQWQWSUMUNWIUAWQWRUAUOZWQTK
      UQUDZLUQUDZWTUFZWIWTWRTZXAXBKLWTXAUPXBUPURWIXCXDWIXCUBWTXBXAUHUEZWRWIXCWT
      XETZXBUSTZXAUSTZUBZXCXFVGWIXGXHLUQUTKUQUTVAXIXFXCXBXAWTUSUSVBVCUNVDWIWRXE
      VEXCWIWMXBWLXAUHWHAWGWMXBVEWFWGVHZABDEFGHILMNOPQRVFVIWHAWFWLXAVEWFWGVJZAB
      DEFGHIKMNOPQRVFVIVKVLVMVPVNVQVRWIWKWQWOWRWPWSABCDEFGHIJKLMNOPQRSVOWIDFHWJ
      VSKLMOAHVSTWHQVLZWJUPWHWFAXKVTWHWGAXJVTWAWIGHWNVSWLWMNXLWNUPWHAWFWLHTXKAB
      DEFGHIKMNOPQRWBVIWHAWGWMHTXJABDEFGHILMNOPQRWBVIWCWDWE $.

    $d Z x y $.
    $( Lemma 9 for ~ funcringcsetcALTV2 .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetcALTV2lem9 $p |- ( ( ph /\ ( X e. B /\ Y e. B /\ Z e. B )
                  /\ ( H e. ( X ( Hom ` R ) Y ) /\ K e. ( Y ( Hom ` R ) Z ) ) )
                  -> ( ( X G Z ) ` ( K ( <. X , Y >. ( comp ` R ) Z ) H ) )
                     = ( ( ( Y G Z ) ` K )
                         ( <. ( F ` X ) , ( F ` Y ) >. ( comp ` S ) ( F ` Z ) )
                         ( ( X G Y ) ` H ) ) ) $=
      ( wcel w3a chom cfv co wa cop cco wceq crh cwun adantr eqid simpr1 simpr2
      ringchom eleq2d simpr3 anbi12d ccom cid cres rhmco funcringcsetcALTV2lem5
      ancoms adantl fvresi syl 3adantr2 crg ringcbas inss1 eqsstrdi sseld com12
      wi cin 3ad2ant1 impcom 3ad2ant2 3ad2ant3 cbs wf ad2antrl ad2antll ringcco
      fveq12d funcringcsetcALTV2lem2 3ad2antr1 3ad2antr2 funcringcsetcALTV2lem1
      rhmf 3ad2antr3 feq23d mpbird simpll 3simpa funcringcsetcALTV2lem6 syl3anc
      wb ad2antlr simprl feq1d 3simpc simprr setcco coeq12d eqtrd sylbid 3impia
      3eqtr4d ex ) AMDUCZNDUCZODUCZUDZKMNFUEUFZUGZUCZLNOXSUGZUCZUHZLKMNUIOFUJUF
      ZUGUGZMOJUGZUFZLNOJUGUFZKMNJUGUFZMIUFZNIUFZUIOIUFZGUJUFZUGUGZUKZAXRUHZYDK
      MNULUGZUCZLNOULUGZUCZUHZYPYQYAYSYCUUAYQXTYRKYQDFHXSUMMNPRAHUMUCZXRTUNZXSU
      OZAXOXPXQUPAXOXPXQUQZURUSYQYBYTLYQDFHXSUMNOPRUUDUUEUUFAXOXPXQUTURUSVAYQUU
      BYPYQUUBUHZLKVBZVCMOULUGZVDZUFZUUHYHYOUUGUUHUUIUCZUUKUUHUKUUBUULYQUUAYSUU
      LMNOLKVEVGVHUUIUUHVIVJUUGYFUUHYGUUJYQYGUUJUKZUUBAXOXQUUMXPABCDEFGHIJMOPQR
      STUAUBVFVKUNUUGFYEHKLUMMNOPYQUUCUUBUUDUNZYEUOYQMHUCZUUBXRAUUOXOXPAUUOVRXQ
      AXOUUOADHMADHVLVSHADFHUMPRTVMHVLVNVOZVPVQVTWAUNYQNHUCZUUBXRAUUQXPXOAUUQVR
      XQAXPUUQADHNUUPVPVQWBWAUNYQOHUCZUUBXRAUURXQXOAUURVRXPAXQUURADHOUUPVPVQWCW
      AUNYSMWDUFZNWDUFZKWEZYQUUAUUSUUTMNKUUSUOUUTUOZWNWFZUUAUUTOWDUFZLWEZYQYSUU
      TUVDNOLUVBUVDUOWNWGZWHWIUUGYOYIYJVBUUHUUGGYNHYJYIUMYKYLYMQUUNYNUOYQYKHUCZ
      UUBAXPXOUVGXQABDEFGHIMPQRSTUAWJWKUNYQYLHUCZUUBAXOXPUVHXQABDEFGHINPQRSTUAW
      JWLUNYQYMHUCZUUBAXOXQUVIXPABDEFGHIOPQRSTUAWJWOUNUUGYKYLYJWEYKYLKWEZUUGUVJ
      UVAUVCYQUVJUVAXBUUBYQYKYLUUSUUTKAXPXOYKUUSUKXQABDEFGHIMPQRSTUAWMWKAXOXPYL
      UUTUKXQABDEFGHINPQRSTUAWMWLZWPUNWQUUGYKYLYJKUUGAXOXPUHZYSYJKUKAXRUUBWRZXR
      UVLAUUBXOXPXQWSXCYQYSUUAXDABCDEFGHIJKMNPQRSTUAUBWTXAZXEWQUUGYLYMYIWEYLYML
      WEZUUGUVOUVEUVFYQUVOUVEXBUUBYQYLYMUUTUVDLUVKAXOXQYMUVDUKXPABDEFGHIOPQRSTU
      AWMWOWPUNWQUUGYLYMYILUUGAXPXQUHZUUAYILUKUVMXRUVPAUUBXOXPXQXFXCYQYSUUAXGAB
      CDEFGHIJLNOPQRSTUAUBWTXAZXEWQXHUUGYILYJKUVQUVNXIXJXMXNXKXL $.

    $d a b c x y $.  $d B a b c h k $.  $d F a b c h k $.  $d G a b c h k $.
    $d R a b c h k $.  $d S a b c h k $.  $d ph a b c h k $.
    $( The "natural forgetful functor" from the category of unital rings into
       the category of sets which sends each ring to its underlying set (base
       set) and the morphisms (ring homomorphisms) to mappings of the
       corresponding base sets.  (Contributed by AV, 16-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetcALTV2 $p |- ( ph -> F ( R Func S ) G ) $=
      ( cfv eqid cv va vb vc vh vk cco ccid chom cwun wcel ringccat syl setccat
      ccat funcringcsetcALTV2lem3 funcringcsetcALTV2lem4 funcringcsetcALTV2lem8
      funcringcsetcALTV2lem7 funcringcsetcALTV2lem9 isfuncd ) AUAUBUCDEFFUFRZFU
      GRZUDUEGIJFUHRZGUGRZGUHRZGUFRZMNVCSVESVBSVDSVASVFSAHUIUJZFUNUJOFHUIKUKULA
      VGGUNUJOGHUILUMULABDEFGHIKLMNOPUOABCDEFGHIJKLMNOPQUPABCDEFGHIJUATZUBTZKLM
      NOPQUQABCDEFGHIJVHKLMNOPQURABCDEFGHIJUDTUETVHVIUCTKLMNOPQUSUT $.
  $}

  ${
    $d f g v x y z $.  $d v x y z U $.  $d v x y z ph $.
    ringcbasALTV.c $e |- C = ( RingCatALTV ` U ) $.
    ringcbasALTV.b $e |- B = ( Base ` C ) $.
    ringcbasALTV.u $e |- ( ph -> U e. V ) $.
    $( Set of objects of the category of rings (in a universe).  (Contributed
       by AV, 13-Feb-2020.)  (New usage is discouraged.) $)
    ringcbasALTV $p |- ( ph -> B = ( U i^i Ring ) ) $=
      ( vx vy vv vz vf vg cnx cfv cop cv crh co crg cin cbs chom cmpo c2nd c1st
      cco cxp ccom ctp cvv c1 cdc eqidd ringcvalALTV catstr baseid snsstp1 wcel
      c5 inex1g syl strfv3 ) ABDUAUBZOUCPVEQZOUDPIJVEVEIRJRSTUEZQZOUHPKLVEVEUIV
      EMNKRZUFPZLRSTVIUGPVJSTMRNRUJUEUEZQZUKCUCULUMUMVAUNQAIJLKVECVKDNMVGEFHAVE
      UOAVGUOAVKUOUPVKVEVGUQURVFVHVLUSADEUTVEULUTHDUAEVBVCGVD $.

    $d v x y z B $.
    ${
      ringchomfvalALTV.h $e |- H = ( Hom ` C ) $.
      $( Set of arrows of the category of rings (in a universe).  (Contributed
         by AV, 14-Feb-2020.)  (New usage is discouraged.) $)
      ringchomfvalALTV $p |- ( ph
                            -> H = ( x e. B , y e. B |-> ( x RingHom y ) ) ) $=
        ( vv vz vf vg cfv cop chom cv cnx cbs crh co cmpo cco cxp c2nd c1st ctp
        ccom ringcbasALTV eqidd ringcvalALTV fveq2d eqtrid cvv wcel fvexi mpoex
        wceq c1 c5 cdc catstr homid snsstp2 strfv mp1i eqtr4d ) AGUAUBQDRZUASQB
        CDDBTCTUCUDZUEZRZUAUFQMNDDUGDOPMTZUHQZNTUCUDVOUIQVPUCUDOTPTUKUEUEZRZUJZ
        SQZVMAGESQVTLAEVSSABCNMDEVQFPOVMHIKADEFHIJKULAVMUMAVQUMUNUOUPVMUQURVMVT
        VAABCDDVLDEUBJUSZWAUTVMVSSUQVBVBVCVDRVQDVMVEVFVKVNVRVGVHVIVJ $.

      $d x y X $.  $d x y Y $.
      ringchomALTV.x $e |- ( ph -> X e. B ) $.
      ringchomALTV.y $e |- ( ph -> Y e. B ) $.
      $( Set of arrows of the category of rings (in a universe).  (Contributed
         by AV, 14-Feb-2020.)  (New usage is discouraged.) $)
      ringchomALTV $p |- ( ph -> ( X H Y ) = ( X RingHom Y ) ) $=
        ( vx vy cv crh co wceq cvv ringchomfvalALTV oveq12 adantl ovexd ovmpod
        wa ) AOPGHBBOQZPQZRSZGHRSZEUAAOPBCDEFIJKLUBUHGTUIHTUGUJUKTAUHGUIHRUCUDM
        NAGHRUEUF $.

      $( A morphism of rings is a function.  (Contributed by AV, 14-Feb-2020.)
         (New usage is discouraged.) $)
      elringchomALTV $p |- ( ph -> ( F e. ( X H Y )
                                 -> F : ( Base ` X ) --> ( Base ` Y ) ) ) $=
        ( co wcel cbs cfv eqid crh wf ringchomALTV eleq2d rhmf biimtrdi ) AEHIF
        PZQEHIUAPZQHRSZIRSZEUBAUGUHEABCDFGHIJKLMNOUCUDUIUJHIEUITUJTUEUF $.
    $}

    ${
      ringccoALTV.o $e |- .x. = ( comp ` C ) $.
      $( Composition in the category of rings.  (Contributed by AV,
         14-Feb-2020.)  (New usage is discouraged.) $)
      ringccofvalALTV $p |- ( ph -> .x. = ( v e. ( B X. B ) , z e. B |->
                                     ( g e. ( ( 2nd ` v ) RingHom z ) ,
                                       f e. ( ( 1st ` v ) RingHom ( 2nd ` v ) )
                                       |-> ( g o. f ) ) ) ) $=
        ( cco cfv cnx cop cv cvv vx vy cbs chom cxp c2nd crh c1st ccom cmpo ctp
        ringcbasALTV eqid ringchomfvalALTV eqidd ringcvalALTV fveq2d wcel fvexi
        co wceq sqxpexg ax-mp mpoex c1 cdc catstr ccoid snsstp3 strfv 3eqtr4g
        c5 ) AEOPQUCPDRZQUDPEUDPZRZQOPCBDDUEZDIHCSZUFPZBSUGUTVQUHPVRUGUTISHSUIU
        JZUJZRZUKZOPZFVTAEWBOAUAUBBCDEVTGHIVNJKMADEGJKLMULAUAUBDEGVNJKLMVNUMUNA
        VTUOUPUQNVTTURVTWCVACBVPDVSDTURVPTURDEUCLUSZDTVBVCWDVDVTWBOTVEVEVLVFRVT
        DVNVGVHVMVOWAVIVJVCVK $.

      $d f g F $.  $d f g G $.  $d f g v z X $.  $d f g v z Y $.
      $d f g v z Z $.  $d f g ph $.
      ringccoALTV.x $e |- ( ph -> X e. B ) $.
      ringccoALTV.y $e |- ( ph -> Y e. B ) $.
      ringccoALTV.z $e |- ( ph -> Z e. B ) $.
      ringccoALTV.f $e |- ( ph -> F e. ( X RingHom Y ) ) $.
      ringccoALTV.g $e |- ( ph -> G e. ( Y RingHom Z ) ) $.
      $( Composition in the category of rings.  (Contributed by AV,
         14-Feb-2020.)  (New usage is discouraged.) $)
      ringccoALTV $p |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) = ( G o. F ) ) $=
        ( vg vf vv vz crh co cv ccom cop cvv cxp c2nd c1st cmpo ringccofvalALTV
        cfv wceq simprl fveq2d wcel op2ndg syl2anc adantr simprr oveq12d op1stg
        wa eqtrd eqidd mpoeq123dv opelxpi ovex mpoex a1i ovmpod coeq12d coexg )
        AUAUBGFJKUEUFZIJUEUFZUAUGZUBUGZUHZGFUHZIJUIZKDUFUJAUCUDWDKBBUKZBUAUBUCU
        GZULUPZUDUGZUEUFZWFUMUPZWGUEUFZWBUNUAUBVRVSWBUNZDUJAUDUCBCDEUBUAHLMNOUO
        AWFWDUQZWHKUQZVGZVGZUAUBWIWKWBVRVSWBWPWGJWHKUEWPWGWDULUPZJWPWFWDULAWMWN
        URZUSAWQJUQZWOAIBUTZJBUTZWSPQIJBBVAVBVCVHZAWMWNVDVEWPWJIWGJUEWPWJWDUMUP
        ZIWPWFWDUMWRUSAXCIUQZWOAWTXAXDPQIJBBVFVBVCVHXBVEWPWBVIVJAWTXAWDWEUTPQIJ
        BBVKVBRWLUJUTAUAUBVRVSWBJKUEVLIJUEVLVMVNVOAVTGUQZWAFUQZVGVGVTGWAFAXEXFU
        RAXEXFVDVPTSAGVRUTFVSUTWCUJUTTSGFVRVSVQVBVO $.
    $}
  $}

  ${
    $d f g h w x y z B $.  $d f g h w x y z C $.  $d f g h w x y z U $.
    $d f g h w x y z V $.  $d x ph $.  $d x X $.
    ringccatALTV.c $e |- C = ( RingCatALTV ` U ) $.
    ${
      ringccatidALTV.b $e |- B = ( Base ` C ) $.
      $( Lemma for ~ ringccatALTV .  (Contributed by AV, 14-Feb-2020.)
         (New usage is discouraged.) $)
      ringccatidALTV $p |- ( U e. V -> ( C e. Cat
                   /\ ( Id ` C ) = ( x e. B |-> ( _I |` ( Base ` x ) ) ) ) ) $=
        ( wcel cv wa cfv co crh simpl wi adantl ringchomALTV ccom com13 3imp vw
        vy vz vf vg vh chom w3a cco cid cbs cres cvv a1i eqidd cringcALTV fvexi
        wceq biid crg ringcbasALTV eleq2 elin simprbi biimtrdi com12 eqid idrhm
        cin mpd simpr eleqtrrd 3ad2ant1 simp1 3ad2ant3 eleq2d biimpd 3exp com14
        syl cop impcom expcom ringccoALTV wf simprl simprr elringchomALTV fcoi2
        ex syl8 eqtrd simp3 adantr 3ad2ant2 fcoi1 expdcom rhmco syl2anc 3eltr4d
        a1d coass simp2r 3eqtr4a oveq1d oveq2d 3eqtr4d iscatd2 ) DEHZUAIZBHZAIZ
        BHZJZUBIZBHZUCIZBHZJZUDIZXJXLCUGKZLZHZUEIZXLXOYALZHZUFIZXOXQYALZHZUHZUH
        ZUAAUBUCBCCUIKZUJXLUKKZULZUDUEUFYAUMBCUKKURXIGUNXIYAUOXIYLUOCUMHXICDUPF
        UQUNYKUSXIXMJZYNXLXLMLZXLXLYALYOXLUTHZYNYPHZYOBDUTVIZURZYQYOBCDEFGXIXMN
        ZVAXMYTYQOXIYTXMYQYTXMXLYSHZYQBYSXLVBUUBXLDHYQXLDUTVCVDVEVFPVJYMXLYMVGV
        HVTZYOBCDYAEXLXLFGUUAYAVGZXIXMVKZUUEQVLXIYKJZYNXTXJXLWAZXLYLLLYNXTRZXTU
        UFBCYLDXTYNEXJXLXLFGXIYKNZYLVGZYKXKXIXNXSXKYJXKXMNZVMPZYKXMXIXNXSXMYJXK
        XMVKZVMPZUUNYKXIXTXJXLMLZHZXNXSYJXIUUPOZYJXSXNUUQYCYFXSXNUUQOOYIXIXSXNY
        CUUPXIXSXNYCUUPOXIXSXNUHZYCUUPUURYBUUOXTUURBCDYAEXJXLFGXIXSXNVNZUUDXNXI
        XKXSUUKVOXNXIXMXSUUMVOZQVPVQVRVSVMSTWBZYKXIYRXNXSXIYROZYJXMUVBXKXIXMYRU
        UCWCPZVMWBWDYKXIUUHXTURZXNXSYJXIUVDOZXNYJUVEOXSYJXNUVEYCYFXNUVEOYIYCXNX
        IXJUKKZYMXTWEZUVDXIXNYCUVGXIXNYCUVGOXIXNJBCDXTYAEXJXLFGXIXNNUUDXIXKXMWF
        XIXKXMWGWHWJSUVFYMXTWIWKVMVFXATWBWLYKXIYDYNXLXLWAXOYLLLZYDURZXNXSYJXIUV
        IOZYJXNXSUVJYFYCXNXSJZUVJOYIYFUVKXIUVIYFUVKXIUHZUVHYDYNRZYDUVLBCYLDYNYD
        EXLXLXOFGYFUVKXIWMUUJUVKYFXMXIXNXMXSUUMWNZWOZUVOUVKYFXPXIXNXPXRWFZWOYFU
        VKXIYRUVKUVBOYFXNUVBXSUVCWNUNTYFUVKXIYDXLXOMLZHZXIUVKYFUVRXIUVKYFUVROZX
        IUVKJZYFUVRUVTYEUVQYDUVTBCDYAEXLXOFGXIUVKNZUUDUVKXMXIUVNPZUVKXPXIUVPPZQ
        VPVQWJSTWDUVLYMXOUKKZYDWEZUVMYDURYFUVKXIUWEXIUVKYFUWEXIUVKYFUWEOUVTBCDY
        DYAEXLXOFGUWAUUDUWBUWCWHWJSTYMUWDYDWPVTWLVRWOWQTWBUUFYDXTRZXJXOMLZYDXTU
        UGXOYLLLZXJXOYALUUFUVRUUPUWFUWGHYKXIUVRXNXSYJXIUVROZYJXSXNUWIYFYCXSXNUW
        IOOYIXIXSXNYFUVRXIXSXNUVSUURYFUVRUURYEUVQYDUURBCDYAEXLXOFGUUSUUDUUTXSXI
        XPXNXPXRNZWOZQVPVQVRVSWOSTWBZUVAXJXLXOYDXTWRWSZUUFBCYLDXTYDEXJXLXOFGUUI
        UUJUULUUNYKXPXIXSXNXPYJUWJWOPZUVAUWLWDZUUFBCDYAEXJXOFGUUIUUDUULUWNQWTUU
        FYGYDRZXTUUGXQYLLZLZYGUWFXJXOWAXQYLLZLZYGYDXLXOWAXQYLLLZXTUWQLYGUWHUWSL
        UUFUWPXTRYGUWFRUWRUWTYGYDXTXBUUFBCYLDXTUWPEXJXLXQFGUUIUUJUULUUNYKXRXIXN
        XPXRYJXCPZUVAUUFYGXOXQMLZHZUVRUWPXLXQMLHYKXIUXDXNXSYJXIUXDOZYJXSXNUXEYI
        YCXSXNUXEOOYFXIXSXNYIUXDXIXSXNYIUXDOUURYIUXDUURYHUXCYGUURBCDYAEXOXQFGUU
        SUUDUWKXIXPXRXNXCQVPVQVRVSVOSTWBZUWLXLXOXQYGYDWRWSWDUUFBCYLDUWFYGEXJXOX
        QFGUUIUUJUULUWNUXBUWMUXFWDXDUUFUXAUWPXTUWQUUFBCYLDYDYGEXLXOXQFGUUIUUJUU
        NUWNUXBUWLUXFWDXEUUFUWHUWFYGUWSUWOXFXGXH $.
    $}

    $( The category of rings is a category.  (Contributed by AV, 14-Feb-2020.)
       (New usage is discouraged.) $)
    ringccatALTV $p |- ( U e. V -> C e. Cat ) $=
      ( vx wcel ccat ccid cfv cbs cid cres cmpt wceq eqid ringccatidALTV simpld
      cv ) BCFAGFAHIEAJIZKERJILMNESABCDSOPQ $.

    ringcidALTV.b $e |- B = ( Base ` C ) $.
    ringcidALTV.o $e |- .1. = ( Id ` C ) $.
    ringcidALTV.u $e |- ( ph -> U e. V ) $.
    ringcidALTV.x $e |- ( ph -> X e. B ) $.
    ringcidALTV.s $e |- S = ( Base ` X ) $.
    $( The identity arrow in the category of rings is the identity function.
       (Contributed by AV, 14-Feb-2020.)  (New usage is discouraged.) $)
    ringcidALTV $p |- ( ph -> ( .1. ` X ) = ( _I |` S ) ) $=
      ( vx cfv cid cbs cvv wcel cres cv ccid cmpt ccat wa ringccatidALTV simprd
      wceq eqtrid fveq2 adantl reseq2d fvex resiexg mp1i fvmptd reseq2i eqtr4di
      syl ) AHFPQHRPZUAZQDUAAOHQOUBZRPZUAZVBBFSAFCUCPZOBVEUDZKACUETZVFVGUIZAEGT
      VHVIUFLOBCEGIJUGUTUHUJAVCHUIZUFVDVAQVJVDVAUIAVCHRUKULUMMVASTVBSTAHRUNVASU
      OUPUQDVAQNURUS $.
  $}

  ${
    ringcsectALTV.c $e |- C = ( RingCatALTV ` U ) $.
    ringcsectALTV.b $e |- B = ( Base ` C ) $.
    ringcsectALTV.u $e |- ( ph -> U e. V ) $.
    ringcsectALTV.x $e |- ( ph -> X e. B ) $.
    ringcsectALTV.y $e |- ( ph -> Y e. B ) $.
    ${
      ringcsectALTV.e $e |- E = ( Base ` X ) $.
      ringcsectALTV.n $e |- S = ( Sect ` C ) $.
      $( A section in the category of rings, written out.  (Contributed by AV,
         14-Feb-2020.)  (New usage is discouraged.) $)
      ringcsectALTV $p |- ( ph -> ( F ( X S Y ) G <-> ( F e. ( X RingHom Y )
                   /\ G e. ( Y RingHom X ) /\ ( G o. F ) = ( _I |` E ) ) ) ) $=
        ( co wcel wbr chom cfv cop cco ccid wceq w3a crh ccom cres ringccatALTV
        cid eqid syl issect wa ringchomALTV eleq2d anbi12d anbi1d adantr simprl
        simprr ringccoALTV ringcidALTV eqeq12d pm5.32da bitrd df-3an 3bitr4g
        ccat ) AGHJKDSUAGJKCUBUCZSZTZHKJVMSZTZHGJKUDJCUEUCZSSZJCUFUCZUCZUGZUHZG
        JKUISZTZHKJUISZTZHGUJZUMFUKZUGZUHZABCDVRVTGHVMJKMVMUNZVRUNZVTUNZRAEITZC
        VLTNCEILULUOOPUPAVOVQUQZWBUQZWEWGUQZWJUQZWCWKAWQWRWBUQWSAWPWRWBAVOWEVQW
        GAVNWDGABCEVMIJKLMNWLOPURUSAVPWFHABCEVMIKJLMNWLPOURUSUTVAAWRWBWJAWRUQZV
        SWHWAWIWTBCVREGHIJKJLMAWOWRNVBWMAJBTWROVBZAKBTWRPVBXAAWEWGVCAWEWGVDVEAW
        AWIUGWRABCFEVTIJLMWNNOQVFVBVGVHVIVOVQWBVJWEWGWJVJVKVI $.
    $}

    ${
      ringcinvALTV.n $e |- N = ( Inv ` C ) $.
      $( An inverse in the category of rings is the converse operation.
         (Contributed by AV, 14-Feb-2020.)  (New usage is discouraged.) $)
      ringcinvALTV $p |- ( ph ->
        ( F ( X N Y ) G <-> ( F e. ( X RingIso Y ) /\ G = `' F ) ) ) $=
        ( co wa wcel wceq wbr csect cfv crh ccom cid cbs cres ccnv ringccatALTV
        crs ccat syl eqid isinv w3a ringcsectALTV df-3an bitrdi 3ancoma anbi12d
        bitri anandi wf1o simplrl wf rhmf anim12i ad2antlr simpr ad2antrl jca32
        adantl fcof1o eqcom anbi2i sylib anass sylanbrc isrim a1i anbi1d adantr
        mpbird rimrhm isrim0 simprbi eleq1 syl5ibrcom imp coeq1 ad2antll rimf1o
        wb f1ococnv1 eqtrd jca31 biimpi anbi2d coeq2 f1ococnv2 impbida 3bitrd )
        AEFIJGQUAEFIJCUBUCZQUAZFEJIXDQUAZRZEIJUDQSZFJIUDQZSZRZFEUEZUFIUGUCZUHZT
        ZRZXKRZXPEFUEZUFJUGUCZUHZTZRZRZEIJUKQSZFEUIZTZRZABCXDEFGIJLPADHSCULSMCD
        HKUJUMNOXDUNZUOAXGXPXKYARZRYCAXEXPXFYIAXEXHXJXOUPXPABCXDDXMEFHIJKLMNOXM
        UNZYHUQXHXJXOURUSAXFXJXHYAUPZYIABCXDDXSFEHJIKLMONXSUNZYHUQYKXHXJYAUPYIX
        JXHYAUTXHXJYAURVBUSVAXPXKYAVCUSAYCYGAYCRZYGXHXMXSEVDZRZYFRZYMXHYNYFRZYP
        YCXHAXPXHXJYBVEVMYMXMXSEVFZXSXMFVFZRZYAXORRZYQYCUUAAYCYTYAXOXKYTXPYBXHY
        RXJYSXMXSIJEYJYLVGXSXMJIFYLYJVGVHVIYBYAXQXPYAVJVMXPXOXQYAXKXOVJVKVLVMUU
        AYNYEFTZRYQXMXSEFVNUUBYFYNYEFVOVPVQUMXHYNYFVRVSAYGYPWNYCAYDYOYFYDYOWNAX
        MXSIJEYJYLVTWAWBWCWDAYGRZXPXKYBUUCXHXJXOYDXHAYFIJEWEVKYGXJAYDYFXJYDXJYF
        YEXISZYDXHUUDIJEWFZWGFYEXIWHZWIWJVMUUCXLYEEUEZXNYFXLUUGTAYDFYEEWKWLUUCY
        NUUGXNTYDYNAYFXMXSIJEYJYLWMVKZXMXSEWOUMWPZWQUUCXKXHUUDRZYDUUJAYFYDUUJUU
        EWRVKUUCXJUUDXHYFXJUUDWNAYDUUFWLWSWDZUUCXKXOYAUUKUUIUUCXREYEUEZXTYFXRUU
        LTAYDFYEEWTWLUUCYNUULXTTUUHXMXSEXAUMWPWQWQXBXC $.
    $}

    ${
      ringcisoALTV.n $e |- I = ( Iso ` C ) $.
      $( An isomorphism in the category of rings is a bijection.  (Contributed
         by AV, 14-Feb-2020.)  (New usage is discouraged.) $)
      ringcisoALTV $p |- ( ph -> ( F e. ( X I Y )
                                  <-> F e. ( X RingIso Y ) ) ) $=
        ( co wcel cfv eqid syl cinv cdm crs ccat ringccatALTV isoval eleq2d wbr
        wfun wb invfun funfvbrb ccnv wceq wa ringcinvALTV simpl biimtrdi sylbid
        wrel wi funrel releldm ex sylbird mpan2i impbid bitrd ) AEHIFPZQEHICUAR
        ZPZUBZQZEHIUCPQZAVIVLEABCFVJHIKVJSZADGQCUDQLCDGJUETZMNOUFUGAVMVNAVMEEVK
        RZVKUHZVNAVKUIZVMVRUJABCVJHIKVOVPMNUKZEVKULTAVRVNVQEUMZUNZUOVNABCDEVQVJ
        GHIJKLMNVOUPVNWBUQURUSAVNWAWAUNZVMWASAVNWCUOEWAVKUHZVMABCDEWAVJGHIJKLMN
        VOUPAVKUTZWDVMVAAVSWEVTVKVBTWEWDVMEWAVKVCVDTVEVFVGVH $.
    $}
  $}

  ${
    ringcbasbasALTV.r $e |- C = ( RingCatALTV ` U ) $.
    ringcbasbasALTV.b $e |- B = ( Base ` C ) $.
    ringcbasbasALTV.u $e |- ( ph -> U e. WUni ) $.
    $( An element of the base set of the base set of the category of rings
       (i.e. the base set of a ring) belongs to the considered weak universe.
       (Contributed by AV, 15-Feb-2020.)  (New usage is discouraged.) $)
    ringcbasbasALTV $p |- ( ( ph /\ R e. B ) -> ( Base ` R ) e. U ) $=
      ( wcel cbs cfv crg cin cwun ringcbasALTV eleq2d wa wi elin cnx baseid imp
      simpl simpr wunstr ex syl11 adantr sylbi com12 sylbid ) ADBIZDJKEIZAULDEL
      MZIZUMABUNDABCENFGHOPUOAUMUODEIZDLIZQAUMRZDELSUPURUQENIZUPUMAUSUPUMUSUPQD
      EJTJKUAUSUPUCUSUPUDUEUFHUGUHUIUJUKUB $.
  $}

  ${
    $d B x $.  $d X x $.  $d ph x $.
    funcringcsetcALTV.r $e |- R = ( RingCatALTV ` U ) $.
    funcringcsetcALTV.s $e |- S = ( SetCat ` U ) $.
    funcringcsetcALTV.b $e |- B = ( Base ` R ) $.
    funcringcsetcALTV.c $e |- C = ( Base ` S ) $.
    funcringcsetcALTV.u $e |- ( ph -> U e. WUni ) $.
    funcringcsetcALTV.f $e |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) ) $.
    $( Lemma 1 for ~ funcringcsetcALTV .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetclem1ALTV $p |- ( ( ph /\ X e. B )
                                 -> ( F ` X ) = ( Base ` X ) ) $=
      ( wcel wa cbs cfv wceq cv cvv cmpt adantr fveq2 adantl simpr fvexd fvmptd
      ) AICPZQZBIBUAZRSZIRSZCHUBAHBCUMUCTUJOUDULITUMUNTUKULIRUEUFAUJUGUKIRUHUI
      $.

    $( Lemma 2 for ~ funcringcsetcALTV .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetclem2ALTV $p |- ( ( ph /\ X e. B ) -> ( F ` X ) e. U ) $=
      ( wcel wa cfv cbs funcringcsetclem1ALTV ringcbasbasALTV eqeltrd ) AICPQIH
      RISRGABCDEFGHIJKLMNOTACEIGJLNUAUB $.

    $d C x $.
    $( Lemma 3 for ~ funcringcsetcALTV .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetclem3ALTV $p |- ( ph -> F : B --> C ) $=
      ( wf cv cbs cfv cmpt wcel ringcbasbasALTV wceq cwun setcbas eqcomd adantr
      wa eleqtrrd eleqtrrdi fmpttd feq1d mpbird ) ACDHOCDBCBPZQRZSZOABCUNDAUMCT
      ZUGZUNFQRZDUQUNGURACEUMGIKMUAAURGUBUPAGURAFGUCJMUDUEUFUHLUIUJACDHUONUKUL
      $.

    $d B x y $.
    funcringcsetcALTV.g $e |- ( ph -> G = ( x e. B , y e. B
                                        |-> ( _I |` ( x RingHom y ) ) ) ) $.
    $( Lemma 4 for ~ funcringcsetcALTV .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetclem4ALTV $p |- ( ph -> G Fn ( B X. B ) ) $=
      ( wfn cv cvv cxp cid crh co cres cmpo eqid wcel ovex resiexd ax-mp fnmpoi
      id fneq1d mpbiri ) AJDDUAZRBCDDUBBSZCSZUCUDZUEZUFZUPRBCDDUTVAVAUGUSTUHZUT
      TUHUQURUCUIVBUSTVBUMUJUKULAUPJVAQUNUO $.

    $d X y $.  $d Y x y $.  $d ph y $.
    $( Lemma 5 for ~ funcringcsetcALTV .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetclem5ALTV $p |- ( ( ph /\ ( X e. B /\ Y e. B ) )
        -> ( X G Y ) = ( _I |` ( X RingHom Y ) ) ) $=
      ( wa wcel cid cv crh co cres cvv cmpo adantr oveq12 adantl reseq2d simprl
      wceq simprr ovexd resiexd ovmpod ) AKDUAZLDUAZTZTZBCKLDDUBBUCZCUCZUDUEZUF
      ZUBKLUDUEZUFJUGAJBCDDVFUHUNVASUIVBVCKUNVDLUNTZTVEVGUBVHVEVGUNVBVCKVDLUDUJ
      UKULAUSUTUMAUSUTUOVBVGUGVBKLUDUPUQUR $.

    $( Lemma 6 for ~ funcringcsetcALTV .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetclem6ALTV $p |- ( ( ph /\ ( X e. B /\ Y e. B )
                        /\ H e. ( X RingHom Y ) ) -> ( ( X G Y ) ` H ) = H ) $=
      ( wcel wa crh co w3a cfv cres funcringcsetclem5ALTV 3adant3 fveq1d fvresi
      cid wceq 3ad2ant3 eqtrd ) ALDUAMDUAUBZKLMUCUDZUAZUEZKLMJUDZUFKULUQUGZUFZK
      USKUTVAAUPUTVAUMURABCDEFGHIJLMNOPQRSTUHUIUJURAVBKUMUPUQKUKUNUO $.

    $( Lemma 7 for ~ funcringcsetcALTV .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetclem7ALTV $p |- ( ( ph /\ X e. B )
        -> ( ( X G X ) ` ( ( Id ` R ) ` X ) ) = ( ( Id ` S ) ` ( F ` X ) ) ) $=
      ( wcel cfv ccid cid cbs cres crh wceq funcringcsetclem5ALTV anabsan2 cwun
      wa eqid adantr simpr ringcidALTV fveq12d crg cin ringcbasALTV eleq2d elin
      co simprbi biimtrdi imp fvresi 3syl funcringcsetclem1ALTV ringcbasbasALTV
      idrhm fveq2d setcid eqtr2d 3eqtrd ) AKDSZUJZKFUATZTZKKJVAZTUBKUCTZUDZUBKK
      UEVAZUDZTZVTKITZGUATZTZVOVQVTVRWBAVNVRWBUFABCDEFGHIJKKLMNOPQRUGUHVODFVSHV
      PUIKLNVPUKAHUISVNPULZAVNUMVSUKZUNUOVOKUPSZVTWASWCVTUFAVNWIAVNKHUPUQZSZWIA
      DWJKADFHUILNPURUSWKKHSWIKHUPUTVBVCVDVSKWHVIWAVTVEVFVOWFVSWETVTVOWDVSWEABD
      EFGHIKLMNOPQVGVJVOGHWEUIVSMWEUKWGADFKHLNPVHVKVLVM $.

    $d B f $.  $d F f $.  $d X f $.  $d Y f $.  $d ph f $.
    $( Lemma 8 for ~ funcringcsetcALTV .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetclem8ALTV $p |- ( ( ph /\ ( X e. B /\ Y e. B ) )
                    -> ( X G Y ) : ( X ( Hom ` R ) Y )
                                   --> ( ( F ` X ) ( Hom ` S ) ( F ` Y ) ) ) $=
      ( wcel vf wa chom cfv co wf crh cmap cid cres wf1o f1oi f1of mp1i cv eqid
      cbs rhmf cvv fvex pm3.2i elmapg bicomd biimpa simpr funcringcsetclem1ALTV
      wb wceq sylan2 simpl oveq12d eleqtrrd ex syl5 ssrdv funcringcsetclem5ALTV
      adantr fssd cwun adantl ringchomALTV funcringcsetclem2ALTV setchom mpbird
      feq123d ) AKDTZLDTZUBZUBZKLFUCUDZUEZKIUDZLIUDZGUCUDZUEZKLJUEZUFKLUGUEZWMW
      LUHUEZUIWQUJZUFWIWQWQWRWSWQWQWSUKWQWQWSUFWIWQULWQWQWSUMUNWIUAWQWRUAUOZWQT
      KUQUDZLUQUDZWTUFZWIWTWRTZXAXBKLWTXAUPXBUPURWIXCXDWIXCUBWTXBXAUHUEZWRWIXCW
      TXETZXBUSTZXAUSTZUBZXCXFVGWIXGXHLUQUTKUQUTVAXIXFXCXBXAWTUSUSVBVCUNVDWIWRX
      EVHXCWIWMXBWLXAUHWHAWGWMXBVHWFWGVEZABDEFGHILMNOPQRVFVIWHAWFWLXAVHWFWGVJZA
      BDEFGHIKMNOPQRVFVIVKVQVLVMVNVOVRWIWKWQWOWRWPWSABCDEFGHIJKLMNOPQRSVPWIDFHW
      JVSKLMOAHVSTWHQVQZWJUPWHWFAXKVTWHWGAXJVTWAWIGHWNVSWLWMNXLWNUPWHAWFWLHTXKA
      BDEFGHIKMNOPQRWBVIWHAWGWMHTXJABDEFGHILMNOPQRWBVIWCWEWD $.

    $d Z x y $.
    $( Lemma 9 for ~ funcringcsetcALTV .  (Contributed by AV, 15-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetclem9ALTV $p |- ( ( ph /\ ( X e. B /\ Y e. B /\ Z e. B )
                  /\ ( H e. ( X ( Hom ` R ) Y ) /\ K e. ( Y ( Hom ` R ) Z ) ) )
                  -> ( ( X G Z ) ` ( K ( <. X , Y >. ( comp ` R ) Z ) H ) )
                     = ( ( ( Y G Z ) ` K )
                         ( <. ( F ` X ) , ( F ` Y ) >. ( comp ` S ) ( F ` Z ) )
                         ( ( X G Y ) ` H ) ) ) $=
      ( wcel w3a chom cfv co wa cop cco wceq crh cwun adantr eqid simpr1 simpr2
      ringchomALTV eleq2d simpr3 anbi12d ccom cid cres ancoms adantl fvresi syl
      rhmco funcringcsetclem5ALTV 3adantr2 simprl fveq12d funcringcsetclem2ALTV
      simprr ringccoALTV 3ad2antr1 3ad2antr2 3ad2antr3 wf funcringcsetclem1ALTV
      cbs ad2antrl wb feq23d mpbird simpll 3simpa funcringcsetclem6ALTV syl3anc
      ad2antlr feq1d ad2antll 3simpc setcco coeq12d eqtrd 3eqtr4d sylbid 3impia
      rhmf ex ) AMDUCZNDUCZODUCZUDZKMNFUEUFZUGZUCZLNOXGUGZUCZUHZLKMNUIOFUJUFZUG
      UGZMOJUGZUFZLNOJUGUFZKMNJUGUFZMIUFZNIUFZUIOIUFZGUJUFZUGUGZUKZAXFUHZXLKMNU
      LUGZUCZLNOULUGZUCZUHZYDYEXIYGXKYIYEXHYFKYEDFHXGUMMNPRAHUMUCZXFTUNZXGUOZAX
      CXDXEUPZAXCXDXEUQZURUSYEXJYHLYEDFHXGUMNOPRYLYMYOAXCXDXEUTZURUSVAYEYJYDYEY
      JUHZLKVBZVCMOULUGZVDZUFZYRXPYCYQYRYSUCZUUAYRUKYJUUBYEYIYGUUBMNOLKVIVEVFYS
      YRVGVHYQXNYRXOYTYEXOYTUKZYJAXCXEUUCXDABCDEFGHIJMOPQRSTUAUBVJVKUNYQDFXMHKL
      UMMNOPRYEYKYJYLUNZXMUOYEXCYJYNUNYEXDYJYOUNYEXEYJYPUNYEYGYIVLZYEYGYIVOZVPV
      MYQYCXQXRVBYRYQGYBHXRXQUMXSXTYAQUUDYBUOYEXSHUCZYJAXDXCUUGXEABDEFGHIMPQRST
      UAVNVQUNYEXTHUCZYJAXCXDUUHXEABDEFGHINPQRSTUAVNVRUNYEYAHUCZYJAXCXEUUIXDABD
      EFGHIOPQRSTUAVNVSUNYQXSXTXRVTXSXTKVTZYQUUJMWBUFZNWBUFZKVTZYGUUMYEYIUUKUUL
      MNKUUKUOUULUOZXAWCYEUUJUUMWDYJYEXSXTUUKUULKAXDXCXSUUKUKXEABDEFGHIMPQRSTUA
      WAVQAXCXDXTUULUKXEABDEFGHINPQRSTUAWAVRZWEUNWFYQXSXTXRKYQAXCXDUHZYGXRKUKAX
      FYJWGZXFUUPAYJXCXDXEWHWKUUEABCDEFGHIJKMNPQRSTUAUBWIWJZWLWFYQXTYAXQVTXTYAL
      VTZYQUUSUULOWBUFZLVTZYIUVAYEYGUULUUTNOLUUNUUTUOXAWMYEUUSUVAWDYJYEXTYAUULU
      UTLUUOAXCXEYAUUTUKXDABDEFGHIOPQRSTUAWAVSWEUNWFYQXTYAXQLYQAXDXEUHZYIXQLUKU
      UQXFUVBAYJXCXDXEWNWKUUFABCDEFGHIJLNOPQRSTUAUBWIWJZWLWFWOYQXQLXRKUVCUURWPW
      QWRXBWSWT $.

    $d a b c x y $.  $d B a b c h k $.  $d F a b c h k $.  $d G a b c h k $.
    $d R a b c h k $.  $d S a b c h k $.  $d ph a b c h k $.
    $( The "natural forgetful functor" from the category of rings into the
       category of sets which sends each ring to its underlying set (base set)
       and the morphisms (ring homomorphisms) to mappings of the corresponding
       base sets.  (Contributed by AV, 16-Feb-2020.)
       (New usage is discouraged.) $)
    funcringcsetcALTV $p |- ( ph -> F ( R Func S ) G ) $=
      ( cfv eqid cv va vb vc vh vk cco ccid chom cwun wcel ringccatALTV setccat
      funcringcsetclem3ALTV funcringcsetclem4ALTV funcringcsetclem8ALTV isfuncd
      ccat syl funcringcsetclem7ALTV funcringcsetclem9ALTV ) AUAUBUCDEFFUFRZFUG
      RZUDUEGIJFUHRZGUGRZGUHRZGUFRZMNVCSVESVBSVDSVASVFSAHUIUJZFUQUJOFHUIKUKURAV
      GGUQUJOGHUILULURABDEFGHIKLMNOPUMABCDEFGHIJKLMNOPQUNABCDEFGHIJUATZUBTZKLMN
      OPQUOABCDEFGHIJVHKLMNOPQUSABCDEFGHIJUDTUETVHVIUCTKLMNOPQUTUP $.
  $}

  ${
    $d S r $.  $d X r $.
    srhmsubcALTV.s $e |- A. r e. S r e. Ring $.
    srhmsubcALTV.c $e |- C = ( U i^i S ) $.
    $( Lemma 1 for ~ srhmsubcALTV .  (Contributed by AV, 19-Feb-2020.)
       (New usage is discouraged.) $)
    srhmsubcALTVlem1 $p |- ( ( U e. V /\ X e. C )
                          -> X e. ( Base ` ( RingCatALTV ` U ) ) ) $=
      ( wcel wa crg cin cringcALTV cfv cbs srhmsubclem1 adantl wceq eqid id
      ringcbasALTV adantr eleqtrrd ) CDIZEAIZJECKLZCMNZONZUEEUFIUDABCEFGHPQUDUH
      UFRUEUDUHUGCDUGSUHSUDTUAUBUC $.

    $d C r s $.  $d U r s $.  $d V r s $.  $d X r s $.  $d Y r s $.
    srhmsubcALTV.j $e |- J = ( r e. C , s e. C |-> ( r RingHom s ) ) $.
    $( Lemma 2 for ~ srhmsubcALTV .  (Contributed by AV, 19-Feb-2020.)
       (New usage is discouraged.) $)
    srhmsubcALTVlem2 $p |- ( ( U e. V /\ ( X e. C /\ Y e. C ) )
                      -> ( X J Y ) = ( X ( Hom ` ( RingCatALTV ` U ) ) Y ) ) $=
      ( wcel wa co crh cfv wceq adantl eqid cringcALTV chom cvv cmpo a1i oveq12
      simpl simpr ovexd ovmpod cbs srhmsubcALTVlem1 sylan2 ringchomALTV eqtr4d
      cv ) CEMZFAMZGAMZNZNZFGDOFGPOZFGCUAQZUBQZOVAIHFGAAIUPZHUPZPOZVBDUCDIHAAVG
      UDRVALUEVEFRVFGRNVGVBRVAVEFVFGPUFSUTURUQURUSUGZSUTUSUQURUSUHZSVAFGPUIUJVA
      VCUKQZVCCVDEFGVCTVJTUQUTUGVDTUTUQURFVJMVHABCEFIJKULUMUTUQUSGVJMVIABCEGIJK
      ULUMUNUO $.

    $d C f g x y z $.  $d J f g x y z $.  $d S x $.  $d U f g $.
    $d U r s x y z $.  $d V f g x y z $.
    $( According to ~ df-subc , the subcategories ` ( Subcat `` C ) ` of a
       category ` C ` are subsets of the homomorphisms of ` C ` (see ~ subcssc
       and ~ subcss2 ).  Therefore, the set of special ring homomorphisms
       (i.e., ring homomorphisms from a special ring to another ring of that
       kind) is a subcategory of the category of (unital) rings.  (Contributed
       by AV, 19-Feb-2020.)  (New usage is discouraged.) $)
    srhmsubcALTV $p |- ( U e. V -> J e. ( Subcat ` ( RingCatALTV ` U ) ) ) $=
      ( vx vy wcel cfv co wa crg crh wceq adantr vg vf vz cringcALTV csubc cssc
      chomf wbr cv ccid cop cco wral cin wss eleq1w vtoclri ssriv mp1i eqsstrid
      sslin chom ssid cbs eqid simpl srhmsubcALTVlem1 adantrr adantrl sseqtrrid
      ringchomALTV cvv oveq12 adantl simprl simprr ovexd ovmpod homfval 3sstr4d
      cmpo a1i ralrimivva cxp ovex fnmpoi homffn id ringcbasALTV eqcomd sqxpeqd
      wfn fneq2d mpbiri inex1g isssc mpbir2and cid cres elin2 sylbi ringcidALTV
      idrhm syl simpr 3eltr4d ccat ringccatALTV ad3antrrr ad2ant2r ad2ant2rl wi
      anim12i jca srhmsubcALTVlem2 eleq2d biimpcd impcom adantlr biimpd adantld
      imp catcocl eleqtrrd ralrimiva issubc2 ) CEMZDCUDNZUENMDYHUGNZUFUHZKUIZYH
      UJNZNZYKYKDOZMZUAUIZUBUIZYKLUIZUKUCUIZYHULNZOOZYKYSDOZMZUAYRYSDOZUMUBYKYR
      DOZUMZUCAUMLAUMZPZKAUMYGYJACQUNZUOUUEYKYRYIOZUOZLAUMKAUMYGACBUNZUUIIBQUOU
      ULUUIUOYGKBQGUIZQMYKQMZGYKBGKQUPHUQZURBQCVAUSUTYGUUKKLAAYGYKAMZYRAMZPZPZY
      KYRROZYKYRYHVBNZOZUUEUUJUUSUUTUUTUVBUUTVCUUSYHVDNZYHCUVAEYKYRYHVEZUVCVEZY
      GUURVFUVAVEZYGUUPYKUVCMZUUQABCEYKGHIVGZVHZYGUUQYRUVCMZUUPABCEYRGHIVGZVIZV
      KVJUUSGFYKYRAAUUMFUIZROZUUTDVLDGFAAUVNWASZUUSJWBUUMYKSZUVMYRSPUVNUUTSUUSU
      UMYKUVMYRRVMVNYGUUPUUQVOYGUUPUUQVPUUSYKYRRVQVRUUSUVCYHYIUVAYKYRYIVEZUVEUV
      FUVIUVLVSVTWCYGKLAUUIDYIVLDAAWDWLYGGFAAUVNDJUUMUVMRWEWFWBZYGYIUUIUUIWDZWL
      YIUVCUVCWDZWLUVCYHYIUVQUVEWGYGUVSUVTYIYGUUIUVCYGUVCUUIYGUVCYHCEUVDUVEYGWH
      WIWJWKWMWNCQEWOWPWQYGUUHKAYGUUPPZYOUUGUWAWRYKVDNZWSZYKYKROZYMYNUWAUUNUWCU
      WDMUUPUUNYGUUPYKCMZYKBMZPUUNYKCBAIWTUWFUUNUWEUUOVNXAVNUWBYKUWBVEZXCXDUWAU
      VCYHUWBCYLEYKUVDUVEYLVEZYGUUPVFZUVHUWGXBUWAGFYKYKAAUVNUWDDVLUVOUWAJWBUVPU
      VMYKSPUVNUWDSUWAUUMYKUVMYKRVMVNYGUUPXEZUWJUWAYKYKRVQVRXFUWAUUFLUCAAUWAUUQ
      YSAMZPZPZUUCUBUAUUEUUDUWMYQUUEMZYPUUDMZPZPZUUAYKYSROZUUBUWQUUAYKYSUVAOZUW
      RUWQUVCYHYTYQYPUVAYKYRYSUVEUVFYTVEZYGYHXGMUUPUWLUWPYHCEUVDXHZXIUWMUVGUWPU
      WAUVGUWLUVHTZTUWMUVJUWPYGUUQUVJUUPUWKUVKXJTUWMYSUVCMZUWPYGUWKUXCUUPUUQABC
      EYSGHIVGXKZTUWPUWMYQUVBMZUWNUWMUXEXLUWOUWMUWNUXEUWMUUEUVBYQUWMUUSUUEUVBSU
      WMYGUURUWAYGUWLUWITZUWAUUPUWLUUQUWJUUQUWKVFXMXNABCDEYKYRFGHIJXOXDXPXQTXRU
      WMUWPYPYRYSUVAOZMZUWMUWOUXHUWNUWMUWOUXHUWMUUDUXGYPYGUWLUUDUXGSUUPABCDEYRY
      SFGHIJXOXSXPXTYAYBYCUWMUWRUWSSUWPUWMUWSUWRUWMUVCYHCUVAEYKYSUVDUVEUXFUVFUX
      BUXDVKWJTYDUWMUUBUWRSUWPUWMGFYKYSAAUVNUWRDVLUVOUWMJWBUVPUVMYSSPUVNUWRSUWM
      UUMYKUVMYSRVMVNUWAUUPUWLUWJTUWAUUQUWKVPUWMYKYSRVQVRTYDWCWCXNYEYGKLUCYHAYT
      YLUBUAYIDUVQUWHUWTUXAUVRYFWQ $.

    $( The restriction of the category of (unital) rings to the set of special
       ring homomorphisms is a category.  (Contributed by AV, 19-Feb-2020.)
       (New usage is discouraged.) $)
    sringcatALTV $p |- ( U e. V -> ( ( RingCatALTV ` U ) |`cat J ) e. Cat ) $=
      ( wcel cringcALTV cfv cresc co eqid srhmsubcALTV subccat ) CEKCLMZSDNOZDT
      PABCDEFGHIJQR $.
  $}

  ${
    $d C r s $.  $d U r s $.  $d V r s $.
    crhmsubcALTV.c $e |- C = ( U i^i CRing ) $.
    crhmsubcALTV.j $e |- J = ( r e. C , s e. C |-> ( r RingHom s ) ) $.
    $( According to ~ df-subc , the subcategories ` ( Subcat `` C ) ` of a
       category ` C ` are subsets of the homomorphisms of ` C ` (see ~ subcssc
       and ~ subcss2 ).  Therefore, the set of commutative ring homomorphisms
       (i.e. ring homomorphisms from a commutative ring to a commutative ring)
       is a "subcategory" of the category of (unital) rings.  (Contributed by
       AV, 19-Feb-2020.)  (New usage is discouraged.) $)
    crhmsubcALTV $p |- ( U e. V -> J e. ( Subcat ` ( RingCatALTV ` U ) ) ) $=
      ( ccrg cv crg wcel crngring rgen srhmsubcALTV ) AIBCDEFFJZKLFIPMNGHO $.

    $( The restriction of the category of (unital) rings to the set of
       commutative ring homomorphisms is a category, the "category of
       commutative rings".  (Contributed by AV, 19-Feb-2020.)
       (New usage is discouraged.) $)
    cringcatALTV $p |- ( U e. V -> ( ( RingCatALTV ` U ) |`cat J ) e. Cat ) $=
      ( wcel cringcALTV cfv cresc co eqid crhmsubcALTV subccat ) BDIBJKZQCLMZCR
      NABCDEFGHOP $.
  $}

  ${
    $d C r s $.  $d U r s $.  $d V r s $.
    drhmsubcALTV.c $e |- C = ( U i^i DivRing ) $.
    drhmsubcALTV.j $e |- J = ( r e. C , s e. C |-> ( r RingHom s ) ) $.
    $( According to ~ df-subc , the subcategories ` ( Subcat `` C ) ` of a
       category ` C ` are subsets of the homomorphisms of ` C ` (see ~ subcssc
       and ~ subcss2 ).  Therefore, the set of division ring homomorphisms is a
       "subcategory" of the category of (unital) rings.  (Contributed by AV,
       20-Feb-2020.)  (New usage is discouraged.) $)
    drhmsubcALTV $p |- ( U e. V -> J e. ( Subcat ` ( RingCatALTV ` U ) ) ) $=
      ( cdr cv crg wcel drngring rgen srhmsubcALTV ) AIBCDEFFJZKLFIPMNGHO $.

    $( The restriction of the category of (unital) rings to the set of division
       ring homomorphisms is a category, the "category of division rings".
       (Contributed by AV, 20-Feb-2020.)  (New usage is discouraged.) $)
    drngcatALTV $p |- ( U e. V -> ( ( RingCatALTV ` U ) |`cat J ) e. Cat ) $=
      ( cdr cv crg wcel drngring rgen sringcatALTV ) AIBCDEFFJZKLFIPMNGHO $.

    $d D r s $.
    fldhmsubcALTV.d $e |- D = ( U i^i Field ) $.
    fldhmsubcALTV.f $e |- F = ( r e. D , s e. D |-> ( r RingHom s ) ) $.
    $( The restriction of the category of (unital) rings to the set of field
       homomorphisms is a category, the "category of fields".  (Contributed by
       AV, 20-Feb-2020.)  (New usage is discouraged.) $)
    fldcatALTV $p |- ( U e. V -> ( ( RingCatALTV ` U ) |`cat F ) e. Cat ) $=
      ( cfield cv crg wcel cdr ccrg wa isfld crngring adantl sylbi sringcatALTV
      rgen ) BMCDFGHHNZOPZHMUFMPUFQPZUFRPZSUGUFTUIUGUHUFUAUBUCUEKLUD $.

    $( The restriction of the category of division rings to the set of field
       homomorphisms is a category, the "category of fields".  (Contributed by
       AV, 20-Feb-2020.)  (New usage is discouraged.) $)
    fldcALTV $p |- ( U e. V
                    -> ( ( ( RingCatALTV ` U ) |`cat J ) |`cat F ) e. Cat ) $=
      ( cringcALTV cresc co cvv cxp cdr cin cfield wcel cfv ccat fvexd wfn ovex
      crh fnmpoi a1i inex1g eqeltrid wss ccrg df-field inss1 eqsstri sslin mp1i
      cv 3sstr4g rescabs fldcatALTV eqeltrd ) CFUAZCMUBZENODNOVEDNOUCVDVEABEDPP
      VDCMUDEAAQUEVDHGAAHUSZGUSZUGOZEJVFVGUGUFZUHUIDBBQUEVDHGBBVHDLVIUHUIVDACRS
      ZPICRFUJUKVDCTSZVJBATRULVKVJULVDTRUMSRUNRUMUOUPTRCUQURKIUTVAABCDEFGHIJKLV
      BVC $.

    $d D r s x y $.  $d F x y $.  $d J x y $.  $d U x y $.  $d V x y $.
    $( According to ~ df-subc , the subcategories ` ( Subcat `` C ) ` of a
       category ` C ` are subsets of the homomorphisms of ` C ` (see ~ subcssc
       and ~ subcss2 ).  Therefore, the set of field homomorphisms is a
       "subcategory" of the category of division rings.  (Contributed by AV,
       20-Feb-2020.)  (New usage is discouraged.) $)
    fldhmsubcALTV $p |- ( U e. V
                      -> F e. ( Subcat ` ( ( RingCatALTV ` U ) |`cat J ) ) ) $=
      ( vx vy wcel co cfield cdr a1i crh cringcALTV cfv cresc csubc cssc wbr cv
      crg ccrg cin elin simprbi crngring df-field eleq2s rgen srhmsubcALTV wral
      syl wss inss1 eqsstri sslin ax-mp sseq12i sylibr wa ssidd cvv cmpo oveq12
      wceq weq adantl simprl simpr ovexd ovmpod mpbir sseli ad2antrl ralrimivva
      3sstr4d cxp ovex fnmpoi inex1g eqeltrid isssc mpbir2and drhmsubcALTV eqid
      wfn wb subsubc ) CFOZDCUAUBZEUCPZUDUBOZDWQUDUBZOZDEUEUFZBQCDFGHHUGZUHOZHQ
      XDXCRUIUJZQXCXEOZXCUIOZXDXFXCROXGXCRUIUKULXCUMUSUNUOUPKLUQWPXBBAUTZMUGZNU
      GZDPZXIXJEPZUTZNBURMBURWPCQUJZCRUJZUTZXHXPWPQRUTXPQXERUNRUIVAVBQRCVCVDZSB
      XNAXOKIVEZVFWPXMMNBBWPXIBOZXJBOZVGZVGZXIXJTPZYCXKXLYBYCVHYBHGXIXJBBXCGUGZ
      TPZYCDVIDHGBBYEVJVLYBLSHMVMGNVMVGYEYCVLYBXCXIYDXJTVKVNZWPXSXTVOYAXTWPXSXT
      VPVNYBXIXJTVQZVRYBHGXIXJAAYEYCEVIEHGAAYEVJVLYBJSYFXSXIAOWPXTBAXIXHXPXQXRV
      SZVTWAYAXJAOZWPXTYIXSBAXJYHVTVNVNYGVRWCWBWPMNBADEVIDBBWDWMWPHGBBYEDLXCYDT
      WEZWFSEAAWDWMWPHGAAYEEJYJWFSWPAXOVIICRFWGWHWIWJWPEWTOWSXAXBVGWNACEFGHIJWK
      WQWREDWRWLWOUSWJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Prime rings (and integral domains)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section contains the definitions and teorems of section "Prime rings and
  integral domains" in JF's mathbox, transformed into extensible structures.

$)

  $c PrmRing $.

  $( Extend class notation with the class of prime rings. $)
  cprmrng $a class PrmRing $.

  $( Define the class of prime rings.  A ring is prime if the zero ideal is a
     prime ideal.  (Contributed by Jeff Madsen, 10-Jun-2010.)  (Revised by AV,
     18-Jun-2026.) $)
  df-prmring $a |- PrmRing = { r e. Ring |
                               { ( 0g ` r ) } e. ( PrmIdeal ` r ) } $.

  ${
    $d R r $.
    isprmrng.z $e |- .0. = ( 0g ` R ) $.
    isprmrng.p $e |- P = ( PrmIdeal ` R ) $.
    $( The predicate "is a prime ring".  (Contributed by Jeff Madsen,
       10-Jun-2010.)  (Revised by AV, 18-Jun-2026.) $)
    isprmrng $p |- ( R e. PrmRing <-> ( R e. Ring /\ { .0. } e. P ) ) $=
      ( vr cprmrng wcel crg c0g cfv cprmidl wa cv wceq fveq2 eleq12d df-prmring
      csn sneqd elrab2 sneqi eleq12i bicomi anbi2i bitri ) BGHBIHZBJKZSZBLKZHZM
      UGCSZAHZMFNZJKZSZUNLKZHUKFBIGUNBOZUPUIUQUJURUOUHUNBJPTUNBLPQFRUAUKUMUGUMU
      KULUIAUJCUHDUBEUCUDUEUF $.
  $}

  $( A prime ring is a nonzero ring.  (Contributed by AV, 26-Jun-2026.) $)
  prmringnzring $p |- ( R e. PrmRing -> R e. NzRing ) $=
    ( cprmrng wcel crg c0g cfv csn cprmidl wa cnzr eqid isprmrng cbs chash wceq
    c1 wi c0 0ringprmidl wn eleq2 noel pm2.21i biimtrdi syl ex 0ringnnzr bicomd
    con1bid ax1w sylbid pm2.61d imp sylbi ) ABCADCZAEFZGZAHFZCZIAJCZURAUPUPKURK
    LUOUSUTUOAMFZNFPOZUSUTQZUOVBVCUOVBIURROZVCVAAVAKSVDUSUQRCZUTURRUQUAVEUTUQUB
    UCUDUEUFUOVBTUTVCUOUTVBUOVBUTTAUGUHUIUOUTUSUJUKULUMUN $.

  $( A prime ring is a ring.  (Contributed by Jeff Madsen, 10-Jun-2010.)
     (Revised by AV, 18-Jun-2026.)  (Proof shortened by AV, 26-Jun-2026.) $)
  prmrngring $p |- ( R e. PrmRing -> R e. Ring ) $=
    ( cprmrng wcel cnzr crg prmringnzring nzrring syl ) ABCADCAECAFAGH $.

  ${
    $d B a b x y $.  $d R a b x y $.  $d U a b $.  $d .0. a b x y $.
    smprngprmrng.b $e |- B = ( Base ` R ) $.
    smprngprmrng.z $e |- .0. = ( 0g ` R ) $.
    smprngprmrng.u $e |- U = ( LIdeal ` R ) $.
    $( A simple ring (a nonzero ring whose only ideals are ` .0. ` and ` R ` )
       is a prime ring.  (Contributed by Jeff Madsen, 6-Jan-2011.)  (Revised by
       AV, 18-Jun-2026.) $)
    smprngprmrng $p |- ( ( R e. NzRing /\ U = { { .0. } , B } )
                         -> R e. PrmRing ) $=
      ( vx vy vb va wcel wceq wa cfv adantr cv wral wo eqid csn cpr crg cprmidl
      cnzr cprmrng nzrring clidl wne cmulr co wss lidl0 syl drnglidl1ne0 necomd
      wi wb cun df-pr eqeq2i id eqtr3id eleq2d anbi12d elun velsn orbi12i bitri
      anbi12i bitrdi sylbi adantl eqimss orcd a1i13 olcd wn wrex ringidcl nzrnz
      cur neneqd csrg ringsrg jca srgridm 3syl eqeq1d mtbird ovex sylnibr oveq1
      elsn eleq1d notbid oveq2 rspc2ev syl3anc rexnal2 pm2.21d ralbidv sylan9bb
      imbi1d syl5ibrcom ccased sylbid ralrimivv w3a isprmidl mpbir3and isprmrng
      sylib raleq sylanbrc ) BUELZCDUAZAUBZMZNZBUCLZXQBUDOZLZBUFLXPYAXSBUGZPXTY
      CXQBUHOZLZXQAUIZHQZIQZBUJOZUKZXQLZIJQZRZHKQZRZYOXQULZYMXQULZSZUQZJYERKYER
      ZXPYFXSXPYAYFYDBYEDYETFUMUNPXPYGXSXPAXQABDFEUOUPPXTYTKJYEYEXTYOYELZYMYELZ
      NZYOXQMZYOAMZSZYMXQMZYMAMZSZNZYTXSUUDUUKURZXPXSCXQUAZAUAZUSZMZUULXRUUOCXQ
      AUTVAUUPUUDYOUUOLZYMUUOLZNUUKUUPUUBUUQUUCUURUUPYEUUOYOUUPYECUUOGUUPVBVCZV
      DUUPYEUUOYMUUSVDVEUUQUUGUURUUJUUQYOUUMLZYOUUNLZSUUGYOUUMUUNVFUUTUUEUVAUUF
      KXQVGKAVGVHVIUURYMUUMLZYMUUNLZSUUJYMUUMUUNVFUVBUUHUVCUUIJXQVGJAVGVHVIVJVK
      VLVMXPUUKYTUQXSXPUUEUUHUUFUUIYTXPUUEUUHNYPYSUUEYSUUHUUEYQYRYOXQVNVOZPVPXP
      UUFUUHNYPYSUUHYSUUFUUHYRYQYMXQVNVQVMVPXPUUEUUINYPYSUUEYSUUIUVDPVPXPYTUUFU
      UINZYLIARZHARZYSUQXPUVGYSXPYLVRZIAVSHAVSZUVGVRXPBWBOZALZUVKUVJUVJYJUKZXQL
      ZVRZUVIXPYAUVKYDABUVJEUVJTZVTZUNZUVQXPUVLDMZUVMXPUVRUVJDMXPUVJDBUVJDUVOFW
      AWCXPUVLUVJDXPYABWDLZUVKNUVLUVJMYDYAUVSUVKBWEUVPWFABYJUVJUVJEYJTZUVOWGWHW
      IWJUVLDUVJUVJYJWKWNWLUVHUVNUVJYIYJUKZXQLZVRHIUVJUVJAAYHUVJMZYLUWBUWCYKUWA
      XQYHUVJYIYJWMWOWPYIUVJMZUWBUVMUWDUWAUVLXQYIUVJUVJYJWQWOWPWRWSYLHIAAWTXMXA
      UVEYPUVGYSUUFYPYNHARUUIUVGYNHYOAXNUUIYNUVFHAYLIYMAXNXBXCXDXEXFPXGXHXPYCYF
      YGUUAXIURZXSXPYAUWEYDHIAXQBYJKJEUVTXJUNPXKYBBDFYBTXLXO $.
  $}

  $( A division ring is a prime ring.  (Contributed by Jeff Madsen,
     6-Jan-2011.)  (Revised by AV, 18-Jun-2026.) $)
  drngprmrng $p |- ( R e. DivRing -> R e. PrmRing ) $=
    ( cdr wcel cnzr clidl cfv c0g csn cbs cpr wceq cprmrng drngnzr smprngprmrng
    eqid drngnidl syl2anc ) ABCADCAEFZAGFZHAIFZJKALCAMTARSTOZSOZROZPTARSUAUBUCN
    Q $.

  $( A commutative ring is a prime ring if and only if it is an integral
     domain.  (Contributed by AV, 27-Jun-2026.) $)
  crngprmringidom $p |- ( R e. CRing -> ( R e. PrmRing <-> R e. IDomn ) ) $=
    ( ccrg wcel cprmrng c0g cfv csn cprmidl wa cidom crg crngring eqid isprmrng
    wb a1i mpbirand ibar prmidl0 3bitrd ) ABCZADCZAEFZGAHFZCZUAUEIZAJCZUAUBAKCZ
    UEALUBUHUEIOUAUDAUCUCMZUDMNPQUAUERUFUGOUAAUCUISPT $.

  $( A commutative ring is a prime ring if and only if it is a domain.
     (Contributed by AV, 27-Jun-2026.) $)
  crngprmringdom $p |- ( R e. CRing -> ( R e. PrmRing <-> R e. Domn ) ) $=
    ( ccrg wcel cprmrng cidom cdomn crngprmringidom isidom baib bitrd ) ABCZADC
    AECZAFCZAGLKMAHIJ $.

  $( Alternate definition of the class of integral domains.  An integral domain
     is a commutative prime ring.  (Contributed by Jeff Madsen, 10-Jun-2010.)
     (Revised by AV, 27-Jun-2026.) $)
  dfidom2 $p |- IDomn = ( PrmRing i^i CRing ) $=
    ( vx cidom cprmrng ccrg cv wcel wa cdomn df-idom eleq2i elin biancomi bitri
    cin crngprmringdom bicomd bianim bitr4i eqriv ) ABCDNZAEZBFZUACFZUADFZGUATF
    UBUAHFZUDUCUBUADHNZFZUEUDGBUFUAIJUGUEUDUADHKLMUDUCUEUAOPQUACDKRS $.

  $( The predicate "is an integral domain":  An integral domain is a
     commutative prime ring.  (Contributed by Jeff Madsen, 10-Jun-2010.)
     (Revised by AV, 27-Jun-2026.) $)
  isidom2 $p |- ( R e. IDomn <-> ( R e. PrmRing /\ R e. CRing ) ) $=
    ( cprmrng ccrg cidom dfidom2 elin2 ) ABCDEF $.

  ${
    $d B a b $.  $d R a b $.  $d .0. a b $.  $d .x. a b $.
    isidom3.b $e |- B = ( Base ` R ) $.
    isidom3.t $e |- .x. = ( .r ` R ) $.
    isidom3.0 $e |- .0. = ( 0g ` R ) $.
    ${
      isidom3.1 $e |- .1. = ( 1r ` R ) $.
      $( The predicate "is a domain", alternate expression.  (Contributed by
         Jeff Madsen, 19-Jun-2010.)  (Revised by AV, 12-Jul-2026.) $)
      isidom3 $p |- ( R e. IDomn <-> ( R e. CRing /\ .0. =/= .1.
                                       /\ A. a e. B A. b e. B
                         ( ( a .x. b ) = .0. -> ( a = .0. \/ b = .0. ) ) ) ) $=
        ( wcel wa wne cv wceq wi wral cfv syl cidom cprmrng ccrg co w3a isidom2
        crg csn cprmidl eqid isprmrng clidl isprmidlc crngring biantrurd 3anass
        wo c2idl 2idl0 2idllidld wb ringidcl eleq2 eqcomd biimtrrdi syl5com c1o
        elsni cen 0ring01eqbi eqcom bitrdi ring0cl en1eqsn ex sylbird necon3bid
        wbr impbid ovex elsn orbi12i imbi12i a1i 2ralbidv anbi12d bitr3d bitrid
        velsn 3bitr3d pm5.32i ancom 3bitr4i bitri ) BUALBUBLZBUCLZMZWPEDNZFOZGO
        ZCUDZEPZWSEPZWTEPZUQZQZGARFARZUEZBUFWPWOMWPWRXGMZMWQXHWPWOXIWOBUGLZEUHZ
        BUISZLZMZWPXIXLBEJXLUJUKWPXMXKBULSLZXKANZXAXKLZWSXKLZWTXKLZUQZQZGARFARZ
        UEZXNXIFGAXKBCHIUMWPXJXMBUNZUOYCXOXPYBMZMZWPXIXOXPYBUPWPYEYFXIWPXOYEWPB
        XKWPXJXKBURSZLYDBYGEYGUJJUSTUTUOWPXPWRYBXGWPXKAEDWPXJXKAPZEDPZVAYDXJYHY
        IXJDALZYHYIABDHKVBYHYJDXKLZYIXKADVCYKDEDEVHVDVEVFXJYIAVGVIVRZYHXJYLDEPY
        IABDEHJKVJDEVKVLXJEALZYLYHQABEHJVMYMYLYHYMYLMAXKEAVNVDVOTVPVSTVQWPYAXFF
        GAAYAXFVAWPXQXBXTXEXAEWSWTCVTWAXRXCXSXDFEWIGEWIWBWCWDWEWFWGWHWJWHWKWOWP
        WLWPWRXGUPWMWN $.
    $}

    $d X a b $.  $d Y b $.
    $( A domain has no zero-divisors (besides zero).  (Contributed by Jeff
       Madsen, 19-Jun-2010.)  (Revised by AV, 12-Jul-2026.) $)
    idomnzd $p |- ( ( R e. IDomn /\ ( X e. B /\ Y e. B /\ ( X .x. Y ) = .0. ) )
                                                 -> ( X = .0. \/ Y = .0. ) ) $=
      ( va vb wcel co wceq wo wi cv wral eqeq1d eqeq1 cidom wa ccrg cur cfv wne
      eqid isidom3 simp3bi oveq1 orbi1d imbi12d oveq2 orbi2d syl5com expd 3imp2
      rspc2v ) BUALZDALZEALZDECMZFNZDFNZEFNZOZUSUTVAVCVFPZUSJQZKQZCMZFNZVHFNZVI
      FNZOZPZKARJARZUTVAUBVGUSBUCLFBUDUEZUFVPABCVQFJKGHIVQUGUHUIVOVGDVICMZFNZVD
      VMOZPJKDEAAVHDNZVKVSVNVTWAVJVRFVHDVICUJSWAVLVDVMVHDFTUKULVIENZVSVCVTVFWBV
      RVBFVIEDCUMSWBVMVEVDVIEFTUNULURUOUPUQ $.

    $( Cancellation law for domains.  (Contributed by Jeff Madsen, 6-Jan-2011.)
       (Revised by AV, 13-Jul-2026.) $)
    idomcanl $p |- ( ( ( R e. IDomn /\ ( X e. B /\ Y e. B /\ Z e. B ) )
                  /\ X =/= .0. ) -> ( ( X .x. Y ) = ( X .x. Z ) -> Y = Z ) ) $=
      ( wcel w3a wa co wceq adantr wi 3expb sylan wb cidom wne csg cfv eqid crg
      ccrg cdomn isidom crngring sylbi simpr1 simpr2 simpr3 ringsubdi eqeq1d wo
      ringgrpd grpsubcl adantlr idomnzd 3exp2 imp31 syldan exp43 3imp2 imbitrdi
      cgrp neor com23 sylbird ringcld grpsubeq0 bicomd syl3anc 3adantr1 3imtr4d
      imp ) BUAKZDAKZEAKZGAKZLZMZDFUBZMZDECNZDGCNZBUCUDZNZFOZEGWINZFOZWGWHOZEGO
      ZWFWKDWLCNZFOZWMWFWPWJFWDWPWJOWEWDABCWIDEGHIWIUEZVSBUFKZWCVSBUGKZBUHKZMWS
      BUIWTWSXABUJPUKZPZVSVTWAWBULZVSVTWAWBUMZVSVTWAWBUNZUOPUPWDWEWQWMQWDWQWEWM
      WDWQDFOWMUQZWEWMQVSVTWAWBWQXGQZVSVTWAWBXHVSVTMWAWBMZWLAKZXHVSXIXJVTVSBVHK
      ZXIXJVSBXBURZXKWAWBXJABWIEGHWRUSRSUTVSVTXJXHVSVTXJWQXGABCDWLFHIJVAVBVCVDV
      EVFWMDFVIVGVJVRVKWDWNWKTZWEWDXKWGAKZWHAKZXMVSXKWCXLPWDABCDEHIXCXDXEVLWDAB
      CDGHIXCXDXFVLXKXNXOLWKWNABWIWGWHFHJWRVMVNVOPWDWOWMTZWEVSWAWBXPVTVSXKXIXPX
      LXKWAWBXPXKWAWBLWMWOABWIEGFHJWRVMVNRSVPPVQ $.

    $( Cancellation law for domains.  (Contributed by Jeff Madsen, 6-Jan-2011.)
       (Revised by AV, 13-Jul-2026.) $)
    idomcanr $p |- ( ( ( R e. IDomn /\ ( X e. B /\ Y e. B /\ Z e. B ) )
                  /\ Z =/= .0. ) -> ( ( X .x. Z ) = ( Y .x. Z ) -> X = Y ) ) $=
      ( cidom wcel w3a wa wne co wceq wb ccrg crngcom cdomn 3adant3r2 3adant3r1
      isidom simplbi eqeq12d adantr wi 3anrot biimpri idomcanl sylanl2 sylbid
      sylan ) BKLZDALZEALZGALZMZNZGFOZNDGCPZEGCPZQZGDCPZGECPZQZDEQZUTVDVGRZVAUO
      BSLZUSVIUOVJBUALBUDUEVJUSNVBVEVCVFVJUPURVBVEQUQABCDGHITUBVJUQURVCVFQUPABC
      EGHITUCUFUNUGUSUOURUPUQMZVAVGVHUHVKUSURUPUQUIUJABCGDFEHIJUKULUM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Basic algebraic structures (extension)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Auxiliary theorems
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x A $.  $d x B $.  $d x y C $.
    $( Membership in a union of Cartesian products over its second component,
       analogous to ~ eliunxp .  (Contributed by AV, 30-Mar-2019.) $)
    eliunxp2 $p |- ( C e. U_ y e. B ( A X. { y } ) <->
      E. x E. y ( C = <. x , y >. /\ ( x e. A /\ y e. B ) ) ) $=
      ( cv csn cxp ciun wcel cop wceq wa wex wrel wral relxp rgenw excom exbii
      reliun mpbir elrel mpan sylibr pm4.71ri nfiu1 nfel2 19.41 19.41v biancomi
      eleq1 opeliun2xp bitrdi pm5.32i bitr3i 3bitr2i bitri ) EBDCBFZGZHZIZJZEAF
      ZUSKZLZVDCJZUSDJZMZMZANZBNZVJBNANVCVFANZBNZVCMVMVCMZBNVLVCVNVCVFBNANZVNVB
      OZVCVPVQVAOZBDPVRBDCUTQRBDVAUAUBABEVBUCUDVFBASUEUFVMVCBBEVBBDVAUGUHUIVOVK
      BVOVFVCMZANVKVFVCAUJVSVJAVFVCVIVFVCVEVBJZVIEVEVBULVTVGVHBCDVDUMUKUNUOTUPT
      UQVJBASUR $.
  $}

  ${
    $d w x y z $.  $d w x z A $.  $d w x z B $.  $d w x y C $.  $d w z D $.
    mpomptx2.1 $e |- ( z = <. x , y >. -> C = D ) $.
    $( Express a two-argument function as a one-argument function, or
       vice-versa.  In this version ` A ( y ) ` is not assumed to be constant
       w.r.t ` y ` , analogous to ~ mpomptx .  (Contributed by AV,
       30-Mar-2019.) $)
    mpomptx2 $p |- ( z e. U_ y e. B ( A X. { y } ) |-> C ) =
      ( x e. A , y e. B |-> D ) $=
      ( vw cv csn cxp ciun cmpt wcel wceq wa copab wex eqtr4i df-mpt coprab cop
      df-mpo eliunxp2 anbi1i 19.41vv anass eqeq2d anbi2d pm5.32i 2exbii 3bitr2i
      cmpo bitri opabbii dfoprab2 ) CBEDBJZKLMZFNCJZUSOZIJZFPZQZCIRZABDEGUNZCIU
      SFUAVFAJZDOUREOQZVBGPZQZABIUBZVEABIDEGUDVEUTVGURUCPZVJQZBSASZCIRVKVDVNCIV
      DVLVHQZBSASZVCQVOVCQZBSASVNVAVPVCABDEUTUEUFVOVCABUGVQVMABVQVLVHVCQZQVMVLV
      HVCUHVLVRVJVLVCVIVHVLFGVBHUIUJUKUOULUMUPVJABICUQTTT $.
  $}

  ${
    $d u w x y z $.  $d u w A $.  $d u w x y z B $.  $d u C $.  $d u x D $.
    $d u E $.
    cbvmpox2.1 $e |- F/_ z A $.
    cbvmpox2.2 $e |- F/_ y D $.
    cbvmpox2.3 $e |- F/_ z C $.
    cbvmpox2.4 $e |- F/_ w C $.
    cbvmpox2.5 $e |- F/_ x E $.
    cbvmpox2.6 $e |- F/_ y E $.
    cbvmpox2.7 $e |- ( y = z -> A = D ) $.
    cbvmpox2.8 $e |- ( ( y = z /\ x = w ) -> C = E ) $.
    $( Rule to change the bound variable in a maps-to function, using implicit
       substitution.  This version of ~ cbvmpo allows ` A ` to be a function of
       ` y ` , analogous to ~ cbvmpox .  (Contributed by AV, 30-Mar-2019.) $)
    cbvmpox2 $p |- ( x e. A , y e. B |-> C ) = ( w e. D , z e. B |-> E ) $=
      ( vu nfv nfan cv wcel wa wceq coprab cmpo nfeq2 nfcri weq eleq1w sylan9bb
      eleq2d simpr eleq1d anbi12d ancoms eqeq2d cbvoprab12 df-mpo 3eqtr4i ) AUA
      EUBZBUAZFUBZUCZRUAZGUDZUCZABRUEDUAZHUBZCUAZFUBZUCZVEIUDZUCZDCRUEABEFGUFDC
      HFIUFVGVNABRDCVDVFDVAVCDVADSVCDSTDVEGMUGTVDVFCVAVCCCAEJUHVCCSTCVEGLUGTVLV
      MAVIVKAVIASVKASTAVEINUGTVLVMBVIVKBBDHKUHVKBSTBVEIOUGTADUIZBCUIZUCZVDVLVFV
      MVQVAVIVCVKVOVAVHEUBVPVIADEUJVPEHVHPULUKVQVBVJFVOVPUMUNUOVQGIVEVPVOGIUDQU
      PUQUOURABREFGUSDCRHFIUSUT $.
  $}

  ${
    $d t u v x A $.  $d t u v x y B $.  $d t u v C $.
    dmmpossx2.1 $e |- F = ( x e. A , y e. B |-> C ) $.
    $( The domain of a mapping is a subset of its base classes expressed as
       union of Cartesian products over its second component, analogous to
       ~ dmmpossx .  (Contributed by AV, 30-Mar-2019.) $)
    dmmpossx2 $p |- dom F C_ U_ y e. B ( A X. { y } ) $=
      ( vu vt vv cv csb csn cxp ciun cfv cmpo nfcv nfcsb1v csbeq1a cdm c2nd weq
      c1st cmpt nfcsbw sylan9eqr cbvmpox2 cop vex op2ndd csbeq1d csbeq2dv eqtrd
      wceq op1std mpomptx2 3eqtr4i dmmptss nfxp sneq xpeq12d cbviun sseqtrri )
      FUAHDBHKZCLZVEMZNZOZBDCBKZMZNZOIVIBIKZUBPZAVMUDPZELZLZFABCDEQJHVFDBVEAJKZ
      ELZLZQFIVIVQUEABHJCDEVFVTHCRBVECSZHERJERABVEVSAVERAVRESUFBVEVSSBVECTZAJUC
      BHUCZEVSVTAVRETBVEVSTUGUHGJHIVFDVQVTVMVRVEUIUOZVQBVEVPLVTWDBVNVEVPVRVEVMJ
      UJZHUJZUKULWDBVEVPVSWDAVOVREVRVEVMWEWFUPULUMUNUQURUSBHDVLVHHVLRBVFVGWABVG
      RUTWCCVFVKVGWBVJVEVAVBVCVD $.
  $}

  ${
    $d B x y $.  $d A x $.
    mpoexxg2.1 $e |- F = ( x e. A , y e. B |-> C ) $.
    $( Existence of an operation class abstraction (version for dependent
       domains, i.e. the first base class may depend on the second base class),
       analogous to ~ mpoexxg .  (Contributed by AV, 30-Mar-2019.) $)
    mpoexxg2 $p |- ( ( B e. R /\ A. y e. B A e. S ) -> F e. _V ) $=
      ( wcel wral wa wfun cdm cvv mpofun cv csn cxp sylancr wss dmmpossx2 vsnex
      ciun xpexg mpan2 ralimi iunexg sylan2 ssexg funex ) DFJZCGJZBDKZLZHMHNZOJ
      ZHOJABCDEHIPUOUPBDCBQRZSZUDZUAUTOJZUQABCDEHIUBUNULUSOJZBDKVAUMVBBDUMUROJV
      BBUCCURGOUEUFUGBDUSFOUHUIUPUTOUJTOHUKT $.
  $}

  ${
    $d x y $.  $d x A $.  $d y B $.
    ovmpordx.1 $e |- ( ph -> F = ( x e. C , y e. D |-> R ) ) $.
    ovmpordx.2 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S ) $.
    ovmpordx.3 $e |- ( ( ph /\ y = B ) -> C = L ) $.
    ovmpordx.4 $e |- ( ph -> A e. L ) $.
    ovmpordx.5 $e |- ( ph -> B e. D ) $.
    ovmpordx.6 $e |- ( ph -> S e. X ) $.
    ${
      ovmpordxf.px $e |- F/ x ph $.
      ovmpordxf.py $e |- F/ y ph $.
      ovmpordxf.ay $e |- F/_ y A $.
      ovmpordxf.bx $e |- F/_ x B $.
      ovmpordxf.sx $e |- F/_ x S $.
      ovmpordxf.sy $e |- F/_ y S $.
      $( Value of an operation given by a maps-to rule, deduction form, with
         substitution of second argument, analogous to ~ ovmpodxf .
         (Contributed by AV, 30-Mar-2019.) $)
      ovmpordxf $p |- ( ph -> ( A F B ) = S ) $=
        ( co cmpo oveqd cv wcel w3a wceq wi wsbc eqid ovmpt4g a1i alrimi spsbcd
        wa adantr wb ad2antrr simpr adantlr 3eltr4d eleq1 adantl mpbird anassrs
        eqeltrd biimt syl3anc oveq12d eqeq12d bitr3d nfeq2 nfan wnf nfmpo2 nfcv
        nfov nfeq sbciedf nfmpo1 mpbid eqtrd ) ADEJUEDEBCFGHUFZUEZIAJWGDEMUGABU
        HZFUIZCUHZGUIZHLUIZUJZWIWKWGUEZHUKZULZCEUMZBDUMWHIUKZAWRBDKPAWRBSAWQCEG
        QAWQCTWQABCFGHWGLWGUNUOUPUQURUQURAWRWSBDKPAWIDUKZUSZWQWSCEGAEGUIZWTQUTX
        AWKEUKZUSZWPWQWSXDWJWLWMWPWQVAXDDKWIFADKUIWTXCPVBXAWTXCAWTVCUTZAXCFKUKW
        TOVDVEXDWLXBAXBWTXCQVBXCWLXBVAXAWKEGVFVGVHXDHILAWTXCHIUKNVIZAILUIWTXCRV
        BVJWNWPVKVLXDWOWHHIXDWIDWKEWGXEXAXCVCVMXFVNVOAWTCTCWIDUAVPVQWSCVRXACWHI
        CDEWGUABCFGHVSCEVTWAUDWBUPWCSWSBVRABWHIBDEWGBDVTBCFGHWDUBWAUCWBUPWCWEWF
        $.
    $}

    $d y A $.  $d x B $.  $d x y S $.  $d x y ph $.
    $( Value of an operation given by a maps-to rule, deduction form, with
       substitution of second argument, analogous to ~ ovmpodxf .  (Contributed
       by AV, 30-Mar-2019.) $)
    ovmpordx $p |- ( ph -> ( A F B ) = S ) $=
      ( nfv nfcv ovmpordxf ) ABCDEFGHIJKLMNOPQRABSACSCDTBETBITCITUA $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y D $.  $d x y H $.  $d x y L $.
    $d x y S $.
    ovmpox2.1 $e |- ( ( x = A /\ y = B ) -> R = S ) $.
    ovmpox2.2 $e |- ( y = B -> C = L ) $.
    ovmpox2.3 $e |- F = ( x e. C , y e. D |-> R ) $.
    $( The value of an operation class abstraction.  Variant of ~ ovmpoga which
       does not require ` D ` and ` x ` to be distinct.  (Contributed by Jeff
       Madsen, 10-Jun-2010.)  (Revised by Mario Carneiro, 20-Dec-2013.) $)
    ovmpox2 $p |- ( ( A e. L /\ B e. D /\ S e. H ) -> ( A F B ) = S ) $=
      ( wcel w3a cmpo wceq cv adantl a1i wa simp1 simp2 simp3 ovmpordx ) CKOZDF
      OZHJOZPZABCDEFGHIKJIABEFGQRUJNUAASCRBSDRZUBGHRUJLTUKEKRUJMTUGUHUIUCUGUHUI
      UDUGUHUIUEUF $.
  $}

  ${
    $d D x $.  $d G x $.  $d R x $.  $d Y x $.
    fdmdifeqresdif.f $e |- F = ( x e. D |-> if ( x = Y , X , ( G ` x ) ) ) $.
    $( The restriction of a conditional mapping to function values of a
       function having a domain which is a difference with a singleton equals
       this function.  (Contributed by AV, 23-Apr-2019.) $)
    fdmdifeqresdif $p |- ( G : ( D \ { Y } ) --> R
                           -> G = ( F |` ( D \ { Y } ) ) ) $=
      ( csn cdif wf cv wceq cfv cif cmpt cres wcel wa wn adantl iffalsed difssd
      eldifsnneq mpteq2dva reseq1i resmptd eqtrid wfn ffn dffn5 sylib 3eqtr4rd
      ) BGIZJZCEKZAUOALZGMZFUQENZOZPZAUOUSPZDUOQZEUPAUOUTUSUPUQUORZSURFUSVDURTU
      PUQBGUDUAUBUEUPVCABUTPZUOQVADVEUOHUFUPABUOUTUPBUNUCUGUHUPEUOUIEVBMUOCEUJA
      UOEUKULUM $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d M x y $.  $d R x y $.  $d V x y $.
    $d Y x y $.  $d .+ x y $.
    ofaddmndmap.r $e |- R = ( Base ` M ) $.
    ofaddmndmap.p $e |- .+ = ( +g ` M ) $.
    $( The function operation applied to the addition for functions (with the
       same domain) into a monoid is a function (with the same domain) into the
       monoid.  (Contributed by AV, 6-Apr-2019.) $)
    ofaddmndmap $p |- ( ( M e. Mnd /\ V e. Y
                          /\ ( A e. ( R ^m V ) /\ B e. ( R ^m V ) ) )
                        -> ( A oF .+ B ) e. ( R ^m V ) ) $=
      ( vx vy cmnd wcel co wa wf cv elmapi 3ad2ant3 cvv w3a simpl1 simprl mndcl
      cmap cof simprr syl3anc adantr adantl simp2 inidm off wb cbs fvexi elmapg
      sylancr mpbird ) ELMZFGMZADFUENZMZBVBMZOZUAZABCUFNZVBMZFDVGPZVFJKFFFCDDDA
      BGGVFJQZDMZKQZDMZOZOUTVKVMVJVLCNDMUTVAVEVNUBVFVKVMUCVFVKVMUGDCEVJVLHIUDUH
      VEUTFDAPZVAVCVOVDADFRUISVEUTFDBPZVAVDVPVCBDFRUJSUTVAVEUKZVQFULUMVFDTMVAVH
      VIUNDEUOHUPVQDFVGTGUQURUS $.
  $}

  ${
    mapsnop.f $e |- F = { <. X , Y >. } $.
    $( A singleton of an ordered pair as an element of the mapping operation.
       (Contributed by AV, 12-Apr-2019.) $)
    mapsnop $p |- ( ( X e. V /\ Y e. R /\ R e. W ) -> F e. ( R ^m { X } ) ) $=
      ( wcel w3a csn cmap co wf cop wceq wb fsng 3adant3 mpbiri cvv snssi simp3
      wss 3ad2ant2 fssd snex elmapg sylancl mpbird ) ECHZFAHZADHZIZBAEJZKLHZUNA
      BMZUMUNFJZABUMUNUQBMZBEFNJOZGUJUKURUSPULEFCABQRSUKUJUQAUCULFAUAUDUEUMULUN
      THUOUPPUJUKULUBEUFAUNBDTUGUHUI $.
  $}

  $( A function with a domain of two elements as element of the mapping
     operator applied to a pair.  (Contributed by AV, 20-May-2024.) $)
  fprmappr $p |- ( ( X e. V /\ ( A e. U /\ B e. W /\ A =/= B )
                            /\ ( C e. X /\ D e. X ) )
                   -> { <. A , C >. , <. B , D >. } e. ( X ^m { A , B } ) ) $=
    ( wcel wne w3a wa cop cpr cmap co wf 3simpa adantr cvv simpr simpl3 syl3anc
    fprg wss prssi adantl fssd 3adant1 simp1 prex a1i elmapd mpbird ) HFIZAEIZB
    GIZABJZKZCHIDHILZKZACMBDMNZHABNZOPIVCHVBQZUSUTVDUOUSUTLZVCCDNZHVBVEUPUQLZUT
    URVCVFVBQUSVGUTUPUQURRSUSUTUAUPUQURUTUBABCDEGHHUDUCUTVFHUEUSCDHUFUGUHUIVAHV
    CVBFTUOUSUTUJVCTIVAABUKULUMUN $.

  ${
    mapprop.f $e |- F = { <. X , A >. , <. Y , B >. } $.
    $( An unordered pair containing two ordered pairs as an element of the
       mapping operation.  (Contributed by AV, 16-Apr-2019.)  (Proof shortened
       by AV, 2-Jun-2024.) $)
    mapprop $p |- ( ( ( X e. V /\ A e. R ) /\ ( Y e. V /\ B e. R )
                     /\ ( X =/= Y /\ R e. W ) ) -> F e. ( R ^m { X , Y } ) ) $=
      ( wcel wa wne w3a cop cpr cmap co simp3r simpl simpr 3anim123i fprmappr
      anim12i 3adant3 syl3anc eqeltrid ) GEJZACJZKZHEJZBCJZKZGHLZCFJZKZMZDGANHB
      NOZCGHOPQZIUPUNUGUJUMMUHUKKZUQURJUIULUMUNRUIUGULUJUOUMUGUHSUJUKSUMUNSUAUI
      ULUSUOUIUHULUKUGUHTUJUKTUCUDGHABEFECUBUEUF $.
  $}

  $( A prime is not an integer multiple of another prime.  (Contributed by AV,
     23-May-2019.) $)
  ztprmneprm $p |- ( ( Z e. ZZ /\ A e. Prime /\ B e. Prime )
                     -> ( ( Z x. A ) = B -> A = B ) ) $=
    ( wcel cprime cmul co wceq wi wa wo cc0 adantr eqeq1d adantl ex syl clt wbr
    sylbi cz cn0 cr cneg cn elznn0nn elnn0 c1 c2 cuz cfv elnn1uz2 oveq1 mullidd
    prmz zcnd biimpd sylbid wn prmuz2 sylan2 eleq1 notbid pm2.24 com12 biimtrdi
    nprm com3l mpcom jaoi prmnn nnred mul02lem2 wne eqneqall eqcoms com23 elnnz
    elnnne0 lt0neg1 nngt0d simpr anim12ci orcd simprl mul2lt0bi mpbird wb breq1
    nnnn0 nn0nlt0 pm2.21d syldc sylbird adantld biimtrid imp 3impib ) CUADZAEDZ
    BEDZCAFGZBHZABHZIZWSCUBDZCUCDZCUDZUEDZJZKWTXAJZXEIZCUFXFXLXJXFCUEDZCLHZKXLC
    UGXMXLXNXMCUHHZCUIUJUKZDZKXLCULXOXLXQXOXKXEXOXKJZXCUHAFGZBHZXDXRXBXSBXOXBXS
    HXKCUHAFUMMNXKXTXDIXOXKXTXDXKXSABWTXSAHXAWTAWTAAUOUPUNMNUQOURPXQXKXEXBEDZUS
    ZXQXKJZXEXKXQAXPDZYBWTYDXAAUTMCAVGVAXCYBYCXDXCYBXAUSZYCXDIXCYAXAXBBEVBVCYCY
    EXDXKYEXDIZXQXAYFWTXAXDVDOOVEVFVHVIPVJTXNXCXKXDXNXCLAFGZBHZXKXDIXNXBYGBCLAF
    UMNXKYHXDXKYHLBHZXDXKYGLBWTYGLHZXAWTAUCDZYJWTAAVKZVLZAVMQMNXAYIXDIZWTXABUED
    ZYNBVKZYOBUBDZBLVNZJYNBVSYRYNYQYIYRXDYRXDIBLXDBLVOVPVEOTQOURVEVFVQVJTXGXIXL
    XIXHUADZLXHRSZJXGXLXHVRXGYTXLYSXGYTCLRSZXLCVTXGUUAXLXKXGUUAJZXBLRSZXEXKUUBU
    UCXKUUBJZUUCUUALARSZJZLCRSALRSJZKUUDUUFUUGXKUUEUUBUUAWTUUEXAWTAYLWAMXGUUAWB
    WCWDUUDCAXKXGUUAWEXKYKUUBWTYKXAYMMMWFWGPXKXCUUCXDXKXCUUCXDIXKXCJUUCBLRSZXDX
    CUUCUUHWHXKXBBLRWIOXKUUHXDIZXCXAUUIWTXAYOUUIYPYOYQUUIBWJYQUUHXDBWKWLQQOMURP
    VQWMPWNWOWPWQVJTWR $.

  $( 2 times 6 minus 3 times 4 equals 0.  (Contributed by AV, 24-May-2019.) $)
  2t6m3t4e0 $p |- ( ( 2 x. 6 ) - ( 3 x. 4 ) ) = 0 $=
    ( c2 c6 cmul co c3 c4 cmin caddc cc0 6cn 2timesi 2p2e4 eqcomi oveq2i adddii
    3cn 2cn 3t2e6 oveq12i 3eqtri addcli subidi eqtri ) ABCDZEFCDZGDBBHDZUFGDIUD
    UFUEUFGBJKUEEAAHDZCDEACDZUHHDUFFUGECUGFLMNEAAPQQOUHBUHBHRRSTSUFBBJJUAUBUC
    $.

  ${
    $d n x y z A $.
    $( For any finite subset of ` NN0 ` , find a superset in the form of a set
       of sequential integers, analogous to ~ ssnnssfz .  (Contributed by AV,
       30-Sep-2019.) $)
    ssnn0ssfz $p |- ( A e. ( ~P NN0 i^i Fin )
                      -> E. n e. NN0 A C_ ( 0 ... n ) ) $=
      ( vx vy vz cn0 cfn wcel cc0 cv cfz co wss wrex c0 wceq wa clt adantr wbr
      cpw cin 0nn0 simpr 0ss eqsstrdi oveq2 sseq2d rspcev sylancr wne csup elin
      simplbi elpwid wor nn0ssre ltso soss mp2 a1i simprbi fisupcl syl13anc cuz
      cr sseldd cfv sselda nn0uz eleqtrdi cz cle nn0zd wral fisup2g ssrexv sylc
      wn wi supub imp nn0red lenltd mpbird eluz2 syl3anbrc eluzfz syl2anc ssrdv
      ex pm2.61dane ) AFUAZGUBHZAIBJZKLZMZBFNZAOWNAOPZQZIFHAIIKLZMZWRUCWTAOXAWN
      WSUDXAUEUFWQXBBIFWOIPWPXAAWOIIKUGUHUIUJWNAOUKZQZAFRULZFHAIXEKLZMZWRXDAFXE
      XDAFWNAWMHZXCWNXHAGHZAWMGUMZUNSUOZXDFRUPZXIXCAFMZXEAHZXLXDFVFMVFRUPXLUQUR
      FVFRUSUTVAZWNXIXCWNXHXIXJVBSZWNXCUDZXKFARVCVDZVGXDCAXFXDCJZAHZXSXFHZXDXTQ
      ZXSIVEVHZHXEXSVEVHHZYAYBXSFYCXDAFXSXKVIZVJVKYBXSVLHXEVLHXSXEVMTZYDYBXSYEV
      NYBXEYBAFXEXDXMXTXKSXDXNXTXRSVGZVNYBYFXEXSRTVSZXDXTYHXDCDEFAXSRXOXDXMXSDJ
      ZRTVSDAVOYIXSRTYIEJRTEANVTDFVOQZCANZYJCFNXKXDXLXIXCXMYKXOXPXQXKCDEFARVPVD
      YJCAFVQVRWAWBYBXSXEYBXSYEWCYBXEYGWCWDWEXSXEWFWGXSIXEWHWIWKWJWQXGBXEFWOXEP
      WPXFAWOXEIKUGUHUIWIWL $.
  $}

  $( If the sum of two nonnegative integers is less than a third integer, then
     one of the summands is already less than this third integer.  (Contributed
     by AV, 19-Oct-2019.) $)
  nn0sumltlt $p |- ( ( a e. NN0 /\ b e. NN0 /\ c e. NN0 )
                    -> ( ( a + b ) < c -> b < c ) ) $=
    ( cv cn0 wcel w3a caddc co clt wbr cmin cr wb nn0re ltaddsub2 syl3an cle wa
    3adant2 cc0 nn0ge0 3ad2ant1 anim12ci subge02 bicomd syl 3ad2ant2 nn0resubcl
    mpbird wi ancoms 3ad2ant3 ltletr syl3anc mpan2d sylbid ) ADZEFZBDZEFZCDZEFZ
    GZURUTHIVBJKZUTVBURLIZJKZUTVBJKZUSURMFZVAUTMFZVCVBMFZVEVGNUROZUTOZVBOZURUTV
    BPQVDVGVFVBRKZVHVDVOUAURRKZUSVAVPVCURUBUCVDVKVISZVOVPNUSVCVQVAUSVIVCVKVLVNU
    DTVQVPVOVBURUEUFUGUJVDVJVFMFZVKVGVOSVHUKVAUSVJVCVMUHUSVCVRVAVCUSVRVBURUIULT
    VCUSVKVAVNUMUTVFVBUNUOUPUQ $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The binomial coefficient operation (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Pascal's rule for the binomial coefficient, generalized to all integers
     ` K ` , shifted down by 1.  (Contributed by AV, 8-Sep-2019.) $)
  bcpascm1 $p |- ( ( N e. NN /\ K e. ZZ ) ->
          ( ( ( N - 1 ) _C K ) + ( ( N - 1 ) _C ( K - 1 ) ) ) = ( N _C K ) ) $=
    ( cn wcel cz wa c1 cmin cbc caddc cn0 wceq nnm1nn0 bcpasc sylan nncn npcan1
    co cc syl adantr oveq1d eqtrd ) BCDZAEDZFZBGHRZAIRUGAGHRIRJRZUGGJRZAIRZBAIR
    UDUGKDUEUHUJLBMAUGNOUFUIBAIUDUIBLZUEUDBSDUKBPBQTUAUBUC $.

  ${
    $d N k $.
    $( The sum of binomial coefficients for a fixed positive ` N ` with
       alternating signs is zero.  Notice that this is not valid for ` N = 0 `
       (since ` ( ( -u 1 ^ 0 ) x. ( 0 _C 0 ) ) = ( 1 x. 1 ) = 1 ` ).  For a
       proof using Pascal's rule ( ~ bcpascm1 ) instead of the binomial theorem
       ( ~ binom ), see ~ altgsumbcALT .  (Contributed by AV, 13-Sep-2019.) $)
    altgsumbc $p |- ( N e. NN ->
                  sum_ k e. ( 0 ... N ) ( ( -u 1 ^ k ) x. ( N _C k ) ) = 0 ) $=
      ( cn wcel cc0 cexp co c1 cneg caddc cmul csu cc wceq syl oveq1d cz syl2an
      cn0 eqtrd cfz cv cbc 1cnd negid eqcomd 0exp negcld nnnn0 binom syl3anc wa
      cmin nnz elfzelz zsubcl 1exp neg1cn a1i elfznn0 expcl mullidd oveq2d bccl
      nn0cnd mulcomd sumeq2dv 3eqtr3rd ) BCDZEBFGHHIZJGZBFGZEEBUAGZVJAUBZFGZBVN
      UCGZKGZALZVIEVKBFVIHMDZEVKNVIUDZVSVKEHUEUFOPBUGVIVLVMVPHBVNUMGZFGZVOKGZKG
      ZALZVRVIVSVJMDZBSDZVLWENVTVIHVTUHBUIZHVJABUJUKVIVMWDVQAVIVNVMDZULZWDVPVOK
      GVQWJWCVOVPKWJWCHVOKGVOWJWBHVOKWJWAQDZWBHNVIBQDVNQDZWKWIBUNVNEBUOZBVNUPRW
      AUQOPWJVOVIWFVNSDVOMDWIWFVIURUSVNBUTVJVNVARZVBTVCWJVPVOWJVPVIWGWLVPSDWIWH
      WMVNBVDRVEWNVFTVGTVH $.
  $}

  ${
    $d N j k $.
    $( Alternate proof of ~ altgsumbc , using Pascal's rule ( ~ bcpascm1 )
       instead of the binomial theorem ( ~ binom ).  (Contributed by AV,
       8-Sep-2019.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    altgsumbcALT $p |- ( N e. NN ->
                  sum_ k e. ( 0 ... N ) ( ( -u 1 ^ k ) x. ( N _C k ) ) = 0 ) $=
      ( vj wcel cc0 cfz co c1 cexp cbc cmul cmin caddc cz wceq oveq2d cc syl2an
      csu a1i cn cneg cv wa elfzelz bcpascm1 sylan2 eqcomd ax-1cn negcl elfznn0
      cn0 expcl mpan adantl nnm1nn0 bccl nn0cnd peano2zm syl adddid eqtrd fzfid
      sumeq2dv neg1cn mulcld 1z zsubcld fsumadd 0zd nnz oveq12d fsumshft oveq1i
      oveq2 0p1e1 sumeq1d cuz cfv elnnuz biimpi elfznn expcld elfzel1 oveq1 clt
      fsump1 wbr nncn pncan1 nnnn0 eqeltrd nn0zd nnre ltm1 breqtrrd olcd bcval4
      wo syl3anc mul01d weq cbvsumv oveq1d fsumcl addridd 3eqtrd elnn0uz fsum1p
      cr sylib exp0d 0z zsubcl mp2an 0re mp1i orcd npcan1 expp1 mulcomd mulassd
      zcnd sumeq12rdv fsummulc2 eqtr4d addlidd mulm1d negidd ) BUADZEBFGZHUBZAU
      CZIGZBYMJGZKGZASYKYNBHLGZYMJGZKGZYNYQYMHLGZJGZKGZMGZASZHBFGZYLYTIGZUUAKGZ
      ASZYLUUHKGZMGZEYJYKYPUUCAYJYMYKDZUDZYPYNYRUUAMGZKGUUCUULYOUUMYNKUULUUMYOU
      UKYJYMNDZUUMYOOYMEBUEZYMBUFUGUHPUULYNYRUUAUUKYNQDZYJHQDZUUKUUPUIUUQYLQDZY
      MULDZUUPUUKHUJYMBUKZYLYMUMZRUNUOYJYQULDZUUNYRQDUUKBUPZUUOUVBUUNUDYRYMYQUQ
      URRZYJUVBYTNDZUUAQDZUUKUVCUUKUUNUVEUUOYMUSUTUVBUVEUDUUAYTYQUQZURZRVAVBVDY
      JUUDYKYSASZYKUUBASZMGUUJYJYKYSUUBAYJEBVCUULYNYRYJUURUUSUUPUUKUURYJVETZUUT
      UVARZUVDVFZUULYNUUAUVLYJUVBUVEUVFUUKUVCUUKYMHUUOHNDZUUKVGTVHUVHRVFZVIYJUV
      IUUHUVJUUIMYJUVIEHMGZBHMGZFGZYLCUCZHLGZIGZYQUVTJGZKGZCSHUVQFGZUWCCSZUUHYJ
      YSUWCACHEBUVNYJVGTYJVJBVKUVMYMUVTOYNUWAYRUWBKYMUVTYLIVOYMUVTYQJVOVLVMYJUV
      RUWDUWCCUVRUWDOYJUVPHUVQFVPVNTVQYJUWEUUEUWCCSZYLUVQHLGZIGZYQUWGJGZKGZMGUW
      FEMGZUUHYJUWCUWJCHBYJBHVRVSDBVTWAYJUVSUWDDZUDZUWAUWBUWMYLUVTUURUWMVETUWLU
      VTULDZYJUWLUVSUADUWNUVSUVQWBUVSUPUTUOWCYJUVBUVTNDZUWBQDUWLUVCUWLUVSHUVSHU
      VQUEUVSHUVQWDVHUVBUWOUDUWBUVTYQUQURRVFUVSUVQOZUWAUWHUWBUWIKUWPUVTUWGYLIUV
      SUVQHLWEZPUWPUVTUWGYQJUWQPVLWGYJUWJEUWFMYJUWJUWHEKGEYJUWIEUWHKYJUVBUWGNDU
      WGEWFWHZYQUWGWFWHZWSUWIEOUVCYJUWGYJUWGBULYJBQDUWGBOBWIBWJUTZBWKZWLZWMYJUW
      SUWRYJYQBUWGWFYJBXJDYQBWFWHBWNBWOUTUWTWPWQUWGYQWRWTPYJUWHYJYLUWGUVKUXBWCX
      AVBPYJUWKUUHEMGUUHYJUWFUUHEMUWFUUHOYJUUEUWCUUGCACAXBZUWAUUFUWBUUAKUXCUVTY
      TYLIUVSYMHLWEZPUXCUVTYTYQJUXDPVLXCTXDYJUUHYJUUEUUGAYJHBVCZYJYMUUEDZUDZUUF
      UUAUXGYLYTUURUXGVETZUXFYTULDZYJUXFYMUADUXIYMBWBYMUPUTZUOWCZUXGUUAYJUVBUVE
      UUAULDUXFUVCUXFYMHYMHBUEZYMHBWDVHUVGRURZVFZXEZXFVBXGXGYJUVJYLEIGZYQEHLGZJ
      GZKGZUVPBFGZUUBASZMGEUUIMGUUIYJUUBUXSAEBYJBULDBEVRVSDUXABXHXKUVOYMEOZYNUX
      PUUAUXRKYMEYLIVOUYBYTUXQYQJYMEHLWEPVLXIYJUXSEUYAUUIMYJUXSHEKGEYJUXPHUXREK
      YJYLUVKXLYJUVBUXQNDZUXQEWFWHZYQUXQWFWHZWSUXREOUVCUYCYJENDUVNUYCXMVGEHXNXO
      TYJUYDUYEEXJDUYDYJXPEWOXQXRUXQYQWRWTVLYJHUUQYJUITXAVBYJUYAUUEYLUUGKGZASUU
      IYJUXTUUEUUBUYFAYJUVPHBFUVPHOYJVPTXDUXGUUBUUFYLKGZUUAKGYLUUFKGZUUAKGUYFUX
      GYNUYGUUAKUXGYNYLYTHMGZIGZUYGUXGYMUYIYLIUXFYMUYIOZYJUXFYMQDZUYKUXFYMUXLYC
      UYLUYIYMYMXSUHUTUOPYJUURUXIUYJUYGOUXFUVKUXJYLYTXTRVBXDUXGUYGUYHUUAKUXGUUF
      YLUXKUXHYAXDUXGYLUUFUUAUXHUXKUXMYBXGYDYJUUEUUGYLAUXEUVKUXNYEYFVLYJUUIYJYL
      UUHUVKUXOVFYGXGVLVBYJUUJUUHUUHUBZMGEYJUUIUYMUUHMYJUUHUXOYHPYJUUHUXOYIVBXG
      $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The ` ZZ `-module ` ZZ X. ZZ `
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    zlmodzxz.z $e |- Z = ( ZZring freeLMod { 0 , 1 } ) $.
    $( The ` ZZ `-module ` ZZ X. ZZ ` is a (left) module with the ring of
       integers as base set.  (Contributed by AV, 20-May-2019.)  (Revised by
       AV, 10-Jun-2019.) $)
    zlmodzxzlmod $p |- ( Z e. LMod /\ ZZring = ( Scalar ` Z ) ) $=
      ( clmod wcel czring csca cfv wceq crg cc0 cpr cvv zringring prex frlmlmod
      c1 mp2an frlmsca pm3.2i ) ACDZEAFGHZEIDZJPKZLDZTMJPNZEAUCLBOQUBUDUAMUEEAU
      CILBRQS $.

    $( An element of the (base set of the) ` ZZ `-module ` ZZ X. ZZ ` .
       (Contributed by AV, 21-May-2019.)  (Revised by AV, 10-Jun-2019.) $)
    zlmodzxzel $p |- ( ( A e. ZZ /\ B e. ZZ )
                       -> { <. 0 , A >. , <. 1 , B >. } e. ( Base ` Z ) ) $=
      ( cz wcel wa cc0 cop c1 cpr czring cbs cfv cmap wf cvv pm3.2i mp1i crg co
      wne c0ex 1ex 0ne1 fprg mp3an13 zringbas sseqtrdi fssd wb fvex prex elmapg
      prssi mpbird cfn wceq zringring prfi eqid frlmfibas eleqtrd ) AEFBEFGZHAI
      JBIKZLMNZHJKZOUAZCMNZVDVEVHFZVGVFVEPZVDVGABKZVFVEHQFZJQFZGVDHJUBVGVLVEPVM
      VNUCUDRUEHJABQQEEUFUGVDVLEVFABEUOUHUIUJVFQFZVGQFZGVJVKUKVDVOVPLMULHJUMRVF
      VGVEQQUNSUPLTFZVGUQFZGVHVIURVDVQVRUSHJUTRLCVGVFTDVFVAVBSVC $.

    ${
      zlmodzxz.o $e |- .0. = { <. 0 , 0 >. , <. 1 , 0 >. } $.
      $( The ` 0 ` of the ` ZZ `-module ` ZZ X. ZZ ` .  (Contributed by AV,
         20-May-2019.)  (Revised by AV, 10-Jun-2019.) $)
      zlmodzxz0 $p |- .0. = ( 0g ` Z ) $=
        ( cc0 cop c1 cpr csn cxp c0g cfv cvv wcel wceq 1ex xpprsng mp3an czring
        c0ex crg zringring prex zring0 frlm0 mp2an 3eqtr2i ) AEEFGEFHZEGHZEIJZB
        KLZDEMNZGMNULUJUHOTPTEGEMMMQRSUANUIMNUJUKOUBEGUCSBUIMECUDUEUFUG $.
    $}

    $d A x $.  $d B x $.  $d C x $.
    ${
      zlmodzxzscm.t $e |- .xb = ( .s ` Z ) $.
      $( The scalar multiplication of the ` ZZ `-module ` ZZ X. ZZ ` .
         (Contributed by AV, 20-May-2019.)  (Revised by AV, 10-Jun-2019.) $)
      zlmodzxzscm $p |- ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ )
                    -> ( A .xb { <. 0 , B >. , <. 1 , C >. } )
                       = { <. 0 , ( A x. B ) >. , <. 1 , ( A x. C ) >. } ) $=
        ( vx cz wcel cc0 c1 cop cfv co cmul cvv a1i wceq fveq2 w3a czring cmulr
        cpr csn cxp cof cv cmpt prex wfn fnconstg 3ad2ant1 wa wne pm3.2i 3simpc
        c0ex 1ex 0ne1 fnprg syl3anc offvalfv cbs eqid simp1 zringbas zlmodzxzel
        eleqtrdi 3adant1 frlmvscafval ovexd oveq12d zringmulr 0elpr01 fvconst2g
        eqcomi sylancl fvpr1g oveq123d sylan9eqr 1elpr01 fvpr2g fmptpr 3eqtr4d
        simp2 simp3 ) AIJZBIJZCIJZUAZKLUDZAUEUFZKBMLCMUDZUBUCNZUGOHWLHUHZWMNZWP
        WNNZWOOZUIAWNDOKABPOZMLACPOZMUDWKHWLWOWMWNQWLQJWKKLUJRZWHWIWMWLUKWJWLAI
        ULUMWKKQJZLQJZUNZWIWJUNKLUOZWNWLUKXEWKXCXDURUSUPRWHWIWJUQXFWKUTRZKLBCQQ
        IIVAVBVCWKAEVDNZUBDWOWLUBVDNZQWNEFXHVEXIVEXBWKAIXIWHWIWJVFZVGVIWIWJWNXH
        JWHBCEFVHVJGWOVEVKWKHKLWTXAWSQQQQXCWKURRZXDWKUSRZWKABPVLWKACPVLWPKSZWKW
        SKWMNZKWNNZWOOWTXMWQXNWRXOWOWPKWMTWPKWNTVMWKXNAXOBWOPWOPSWKPWOVNVQRZWKW
        HKWLJXNASXJVOWLAKIVPVRWKXCWIXFXOBSXKWHWIWJWFXGKLBCQIVSVBVTWAWPLSZWKWSLW
        MNZLWNNZWOOXAXQWQXRWRXSWOWPLWMTWPLWNTVMWKXRAXSCWOPXPWKWHLWLJXRASXJWBWLA
        LIVPVRWKXDWJXFXSCSXLWHWIWJWGXGKLBCQIWCVBVTWAWDWE $.
    $}

    $d D x $.
    ${
      zlmodzxzadd.p $e |- .+ = ( +g ` Z ) $.
      $( The addition of the ` ZZ `-module ` ZZ X. ZZ ` .  (Contributed by AV,
         22-May-2019.)  (Revised by AV, 10-Jun-2019.) $)
      zlmodzxzadd $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) )
          -> ( { <. 0 , A >. , <. 1 , C >. } .+ { <. 0 , B >. , <. 1 , D >. } )
             = { <. 0 , ( A + B ) >. , <. 1 , ( C + D ) >. } ) $=
        ( cz wcel wa cc0 cop c1 co cfv cvv a1i syl3anc wceq vx czring cplusg cv
        cpr cof cmpt caddc cbs crg eqid zringring simpl zlmodzxzel syl2an simpr
        prex frlmplusgval wne wfn c0ex pm3.2i anim12i 0ne1 fnprg offvalfv ovexd
        1ex fveq2 adantr fvpr1g sylan9eqr adantl fvpr2g fmptpr zringplusg oveqi
        oveq12d eqcomi opeq2i preq12i eqtr3di 3eqtrd ) AIJZBIJZKZCIJZDIJZKZKZLA
        MNCMUEZLBMNDMUEZEOWKWLUBUCPZUFOUALNUEZUAUDZWKPZWOWLPZWMOZUGZLABUHOZMZNC
        DUHOZMZUEZWJFUIPZWMEUBWKWLWNUJQFGXEUKUBUJJWJULRWNQJWJLNUQRZWFWDWGWKXEJW
        IWDWEUMZWGWHUMZACFGUNUOWFWEWHWLXEJWIWDWEUPZWGWHUPZBDFGUNUOWMUKHURWJUAWN
        WMWKWLQXFWJLQJZNQJZKZWDWGKLNUSZWKWNUTXMWJXKXLVAVHVBRZWFWDWIWGXGXHVCXNWJ
        VDRZLNACQQIIVESWJXMWEWHKXNWLWNUTXOWFWEWIWHXIXJVCXPLNBDQQIIVESVFWJLABWMO
        ZMZNCDWMOZMZUEWSXDWJUALNXQXSWRQQQQXKWJVARZXLWJVHRZWJABWMVGWJCDWMVGWOLTZ
        WJWRLWKPZLWLPZWMOXQYCWPYDWQYEWMWOLWKVIWOLWLVIVRWJYDAYEBWMWJXKWDXNYDATYA
        WFWDWIXGVJXPLNACQIVKSWJXKWEXNYEBTYAWFWEWIXIVJXPLNBDQIVKSVRVLWONTZWJWRNW
        KPZNWLPZWMOXSYFWPYGWQYHWMWONWKVIWONWLVIVRWJYGCYHDWMWJXLWGXNYGCTYBWIWGWF
        XHVMXPLNACQIVNSWJXLWHXNYHDTYBWIWHWFXJVMXPLNBDQIVNSVRVLVOXRXAXTXCXQWTLWM
        UHABUHWMVPVSZVQVTXSXBNWMUHCDYIVQVTWAWBWC $.
    $}

    ${
      zlmodzxzsub.m $e |- .- = ( -g ` Z ) $.
      $( The subtraction of the ` ZZ `-module ` ZZ X. ZZ ` expressed as
         addition.  (Contributed by AV, 24-May-2019.)  (Revised by AV,
         10-Jun-2019.) $)
      zlmodzxzsubm $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) )
          -> ( { <. 0 , A >. , <. 1 , C >. } .- { <. 0 , B >. , <. 1 , D >. } )
        = ( { <. 0 , A >. , <. 1 , C >. }
            ( +g ` Z ) ( -u 1 ( .s ` Z ) { <. 0 , B >. , <. 1 , D >. } ) ) ) $=
        ( cz wcel wa cc0 cop c1 cpr co czring cfv wceq eqid cminusg cplusg cneg
        cvsca clmod cbs csca zlmodzxzlmod simpli a1i zlmodzxzel ad2ant2r simpri
        ad2ant2l zring1 lmodvsubval2 syl3anc zringinvg mp1i eqcomd oveq1d eqtrd
        1z oveq2d ) AIJZBIJZKCIJZDIJZKKZLAMNCMOZLBMNDMOZEPZVJNQUARZRZVKFUDRZPZF
        UBRZPZVJNUCZVKVOPZVQPVIFUEJZVJFUFRZJZVKWBJZVLVRSWAVIWAQFUGRSZFGUHZUIUJV
        EVGWCVFVHACFGUKULVFVHWDVEVGBDFGUKUNVJVKVQVONQEVMWBFWBTVQTHWAWEWFUMVOTVM
        TUOUPUQVIVPVTVJVQVIVNVSVKVOVIVSVNNIJVSVNSVIVCNURUSUTVAVDVB $.

      $( The subtraction of the ` ZZ `-module ` ZZ X. ZZ ` .  (Contributed by
         AV, 22-May-2019.)  (Revised by AV, 10-Jun-2019.) $)
      zlmodzxzsub $p |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ D e. ZZ ) )
          -> ( { <. 0 , A >. , <. 1 , C >. } .- { <. 0 , B >. , <. 1 , D >. } )
             = { <. 0 , ( A - B ) >. , <. 1 , ( C - D ) >. } ) $=
        ( cz wcel wa cc0 cop c1 cpr co wceq syl2an cc zcn cmin cplusg cfv caddc
        zsubcl simpr jca eqid zlmodzxzadd npcan adantr opeq2d adantl eqtrd cgrp
        preq12d cbs wb clmod csca zlmodzxzlmod lmodgrp mp1i zlmodzxzel ad2ant2r
        czring grpsubadd syl13anc mpbird ) AIJZBIJZKZCIJZDIJZKZKZLAMZNCMZOZLBMN
        DMOZEPLABUAPZMNCDUAPZMOZQZWCVTFUBUCZPZVSQZVPWFLWABUDPZMZNWBDUDPZMZOZVSV
        LWAIJZVKKWBIJZVNKWFWLQVOVLWMVKABUEZVJVKUFZUGVOWNVNCDUEZVMVNUFZUGWABWBDW
        EFGWEUHZUIRVPWIVQWKVRVPWHALVLWHAQZVOVJASJBSJWTVKATBTABUJRUKULVPWJCNVOWJ
        CQZVLVMCSJDSJXAVNCTDTCDUJRUMULUPUNVPFUOJZVSFUQUCZJZVTXCJZWCXCJZWDWGURFU
        SJZVFFUTUCQZKXBVPFGVAXGXBXHFVBUKVCVJVMXDVKVNACFGVDVEVLVKVNXEVOWPWRBDFGV
        DRVLWMWNXFVOWOWQWAWBFGVDRXCWEFEVSVTWCXCUHWSHVGVHVI $.
    $}
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Group sum operation (extension 2)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d k I $.  $d k M $.  $d k N $.  $d k R $.  $d k ph $.  $d k X $.
    mgpsumunsn.m $e |- M = ( mulGrp ` R ) $.
    mgpsumunsn.t $e |- .x. = ( .r ` R ) $.
    mgpsumunsn.r $e |- ( ph -> R e. CRing ) $.
    mgpsumunsn.n $e |- ( ph -> N e. Fin ) $.
    mgpsumunsn.i $e |- ( ph -> I e. N ) $.
    mgpsumunsn.a $e |- ( ( ph /\ k e. N ) -> A e. ( Base ` R ) ) $.
    ${
      mgpsumunsn.x $e |- ( ph -> X e. ( Base ` R ) ) $.
      mgpsumunsn.e $e |- ( k = I -> A = X ) $.
      $( Extract a summand/factor from the group sum for the multiplicative
         group of a unital ring.  (Contributed by AV, 29-Dec-2018.) $)
      mgpsumunsn $p |- ( ph -> ( M gsum ( k e. N |-> A ) )
                       = ( ( M gsum ( k e. ( N \ { I } ) |-> A ) ) .x. X ) ) $=
        ( cgsu co wcel cmpt csn cdif cun wceq difsnid syl eqcomd mpteq1d oveq2d
        cbs cfv eqid mgpbas mgpplusg ccrg crngmgp cfn diffi cv eldifi neldifsnd
        ccmn sylan2 gsumunsn eqtrd ) AGEHBUAZRSGEHFUBZUCZVHUDZBUAZRSGEVIBUARSID
        SAVGVKGRAEHVJBAVJHAFHTVJHUENHFUFUGUHUIUJAVICUKULZDEGFHBIVLCGJVLUMUNCDGJ
        KUOACUPTGVCTLCGJUQUGAHURTVIURTMHVHUSUGEUTZVITAVMHTBVLTVMHVHVAOVDNAFHVBP
        QVEVF $.
    $}

    ${
      $d k .0. $.
      mgpsumz.z $e |- .0. = ( 0g ` R ) $.
      mgpsumz.0 $e |- ( k = I -> A = .0. ) $.
      $( If the group sum for the multiplicative group of a unital ring
         contains a summand/factor that is the zero of the ring, the group sum
         itself is zero.  (Contributed by AV, 29-Dec-2018.) $)
      mgpsumz $p |- ( ph -> ( M gsum ( k e. N |-> A ) ) = .0. ) $=
        ( co wcel syl cmpt cgsu csn cdif ccrg crg cmnd cbs cfv crngring ringmnd
        eqid mndidcl 4syl mgpsumunsn wceq mgpbas ccmn crngmgp cfn eldifi sylan2
        diffi cv ralrimiva gsummptcl ringrz syl2anc eqtrd ) AGEHBUAUBRGEHFUCZUD
        ZBUAUBRZIDRZIABCDEFGHIJKLMNOACUESZCUFSZCUGSICUHUIZSLCUJZCUKVPCIVPULZPUM
        UNQUOAVOVLVPSVMIUPAVNVOLVQTAVPEGVKBVPCGJVRUQAVNGURSLCGJUSTAHUTSVKUTSMHV
        JVCTABVPSZEVKEVDZVKSAVTHSVSVTHVJVAOVBVEVFVPCDVLIVRKPVGVHVI $.
    $}

    ${
      $d k .1. $.
      mgpsumn.n $e |- .1. = ( 1r ` R ) $.
      mgpsumn.1 $e |- ( k = I -> A = .1. ) $.
      $( If the group sum for the multiplicative group of a unital ring
         contains a summand/factor that is the one of the ring, this summand/
         factor can be removed from the group sum.  (Contributed by AV,
         29-Dec-2018.) $)
      mgpsumn $p |- ( ph -> ( M gsum ( k e. N |-> A ) )
                            = ( M gsum ( k e. ( N \ { I } ) |-> A ) ) ) $=
        ( co wcel syl cmpt cgsu csn cdif ccrg crngring eqid ringidcl mgpsumunsn
        crg cbs cfv wceq mgpbas crngmgp cfn diffi cv eldifi ralrimiva gsummptcl
        ccmn sylan2 ringridm syl2anc eqtrd ) AHFIBUAUBRHFIGUCZUDZBUAUBRZEDRZVIA
        BCDFGHIEJKLMNOACUJSZECUKULZSACUESZVKLCUFTZVLCEVLUGZPUHTQUIAVKVIVLSVJVIU
        MVNAVLFHVHBVLCHJVOUNAVMHVBSLCHJUOTAIUPSVHUPSMIVGUQTABVLSZFVHFURZVHSAVQI
        SVPVQIVGUSOVCUTVAVLCDEVIVOKPVDVEVF $.
    $}
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Symmetric groups (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( A nonnegative integer to the power of itself is less than 6 if it is less
     than or equal to 2.  (Contributed by AV, 16-Mar-2019.) $)
  exple2lt6 $p |- ( ( N e. NN0 /\ N <_ 2 ) -> ( N ^ N ) < 6 ) $=
    ( cn0 wcel c2 cle wbr wa cc0 wceq c1 w3o cexp co c6 id oveq12d 1lt6 eqbrtri
    clt eqbrtrdi nn0le2is012 0exp0e1 cc ax-1cn exp1 ax-mp c4 sq2 4lt6 3jaoi syl
    ) ABCADEFGAHIZAJIZADIZKAALMZNSFZAUAULUPUMUNULUOHHLMZNSULAHAHLULOZURPUQJNSUB
    QRTUMUOJJLMZNSUMAJAJLUMOZUTPUSJNSJUCCUSJIUDJUEUFQRTUNUODDLMZNSUNADADLUNOZVB
    PVAUGNSUHUIRTUJUK $.

  ${
    pgrple2abl.g $e |- G = ( SymGrp ` A ) $.
    $( Every symmetric group on a set with at most 2 elements is abelian.
       (Contributed by AV, 16-Mar-2019.) $)
    pgrple2abl $p |- ( ( A e. V /\ ( # ` A ) <_ 2 ) -> G e. Abel ) $=
      ( wcel chash cfv c2 cle wbr wa cgrp cbs clt cabl symggrp adantr cn0 syl
      c6 cfa cfn wceq 2nn0 hashbnd mp3an2 eqid symghash cexp co cn hashcl faccl
      nnred nn0expcld nn0red 6re a1i facubnd exple2lt6 sylancom lelttrd eqbrtrd
      cr lt6abl syl2anc ) ACEZAFGZHIJZKZBLEZBMGZFGZTNJBOEVGVKVIABCDPQVJVMVHUAGZ
      TNVJAUBEZVMVNUCVGHREVIVOUDAHCUEUFZAVLBDVLUGZUHSVJVNVHVHUIUJZTVJVNVJVHREZV
      NUKEVJVOVSVPAULSZVHUMSUNVJVRVJVHVHVTVTUOUPTVDEVJUQURVJVSVNVRIJVTVHUSSVGVI
      VSVRTNJVTVHUTVAVBVCVLBVQVEVF $.

    $d A x y $.  $d G x y $.  $d V x y $.
    $( Every symmetric group on a set with more than 2 elements is not abelian,
       see also the remark in [Rotman] p. 28.  (Contributed by AV,
       21-Mar-2019.) $)
    pgrpgt2nabl $p |- ( ( A e. V /\ 2 < ( # ` A ) ) -> G e/ Abel ) $=
      ( vx vy wcel c2 cfv wbr wa co wceq wn cabl wrex eqid c3 cle sylibr clt cv
      chash cgrp cmnd cplusg cbs wral wnel wne cpmtr crn wss symgtrf cfn wi cn0
      ccom hashcl c1 caddc wb 2nn0 nn0ltp1le mpan 2p1e3 a1i breq1d bitrd biimpd
      adantld syl cpnf cxr 3re rexri pnfge ax-mp hashinf breqtrrid adantr com12
      pm2.61i pmtr3ncom rexcom syldan ssrexv reximdv mpsyl symgov adantl pm3.22
      neeq12d 2rexbidva mpbird rexnal df-ne bicomi rexbii bitr3i intnand df-nel
      ex ccmn isabl iscmn anbi2i bitri xchbinx ) ACGZHAUCIZUAJZKZBUDGZBUEGZEUBZ
      FUBZBUFIZLZXQXPXRLZMZFBUGIZUHZEYBUHZKZKZNBOUIZXMYEXNXMYDXOXMXSXTUJZFYBPZE
      YBPZYDNZXMYJXPXQURZXQXPURZUJZFYBPZEYBPZAUKIZULZYBUMZXMYOEYRPZYPYBAYRBYRQD
      YBQZUNZYSXMYNFYRPZEYRPZYTUUBXJXLRXKSJZUUDAUOGZXMUUEUPZUUFXKUQGZUUGAUSUUHX
      LUUEXJUUHXLUUEUUHXLHUTVALZXKSJZUUEHUQGUUHXLUUJVBVCHXKVDVEUUHUUIRXKSUUIRMU
      UHVFVGVHVIVJVKVLXMUUFNZUUEXJUUKUUEUPXLXJUUKUUEXJUUKKRVMXKSRVNGRVMSJRVOVPR
      VQVRACVSVTXCWAWBWCXJUUEKYNEYRPFYRPUUDAYQFECYQQWDYNEFYRYRWETWFYSUUCYOEYRYN
      FYRYBWGWHWIYOEYRYBWGWIXMYHYNEFYBYBXMXPYBGZXQYBGZKZKZXSYLXTYMUUNXSYLMXMAYB
      XRBXPXQDUUAXRQZWJWKUUOUUMUULKZXTYMMUUNUUQXMUULUUMWLWKAYBXRBXQXPDUUAUUPWJV
      LWMWNWOYKYCNZEYBPYJYCEYBWPUURYIEYBUURYANZFYBPYIYAFYBWPUUSYHFYBYHUUSXSXTWQ
      WRWSWTWSWTTXAXAYGBOGZYFBOXBUUTXNBXDGZKYFBXEUVAYEXNEFYBXRBUUAUUPXFXGXHXIT
      $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Divisibility (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    invginvrid.b $e |- B = ( Base ` R ) $.
    invginvrid.u $e |- U = ( Unit ` R ) $.
    invginvrid.n $e |- N = ( invg ` R ) $.
    invginvrid.i $e |- I = ( invr ` R ) $.
    invginvrid.t $e |- .x. = ( .r ` R ) $.
    $( Identity for a multiplication with additive and multiplicative inverses
       in a ring.  (Contributed by AV, 18-May-2018.) $)
    invginvrid $p |- ( ( R e. Ring /\ X e. B /\ Y e. U )
                      -> ( ( N ` Y ) .x. ( ( I ` ( N ` Y ) ) .x. X ) ) = X ) $=
      ( wcel w3a cfv co wceq eqid 3adant2 crg cur cmgp ringmgp 3ad2ant1 ringgrp
      cmnd unitcl grpinvcl syl2an unitnegcl ringinvcl syldan wa mgpbas mgpplusg
      cgrp simp2 mndass eqcomd syl13anc simp1 unitrinv syl2anc ringlidm 3adant3
      oveq1d 3eqtrd ) BUANZGANZHDNZOZHFPZVMEPZGCQCQZVMVNCQZGCQZBUBPZGCQZGVLBUCP
      ZUGNZVMANZVNANZVJVOVQRVIVJWAVKBVTVTSZUDUEVIVKWBVJVIBUQNHANWBVKBUFABDHIJUH
      ABFHIKUIUJTVIVKWCVJVIVKVMDNZWCBDFHJKUKZABDEVMJLIULUMTVIVJVKURWAWBWCVJOUNV
      QVOACVTVMVNGABVTWDIUOBCVTWDMUPUSUTVAVLVPVRGCVLVIWEVPVRRVIVJVKVBVIVKWEVJWF
      TBCDVREVMJLMVRSZVCVDVGVIVJVSGRVKABCVRGIMWGVEVFVH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The support of functions (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A w v $.  $d C w v $.  $d M w v $.  $d R w v $.  $d X w v $.
    $d V v w $.
    rmsuppss.r $e |- R = ( Base ` M ) $.
    $( The support of a mapping of a multiplication of zero with a function
       into a ring is empty.  (Contributed by AV, 10-Apr-2019.) $)
    rmsupp0 $p |- ( ( ( M e. Ring /\ V e. X /\ C = ( 0g ` M ) )
                      /\ A e. ( R ^m V ) )
                    -> ( ( v e. V |-> ( C ( .r ` M ) ( A ` v ) ) )
                         supp ( 0g ` M ) ) = (/) ) $=
      ( vw wcel c0g cfv wceq co wa cv wne crab c0 eqid crg w3a cmap cmulr csupp
      cmpt cvv weq fveq2 oveq2d cbvmptv simpl2 fvexd ovexd mptsuppd simpll3 cbs
      oveq1d simpll1 wi wf elmapi ffvelcdm eleqtrdi syl adantl imp ringlz eqtrd
      ex syl2anc neeq1d rabbidva wral neirr a1i ralrimivw rabeq0 sylibr 3eqtrd
      wn ) EUAJZFGJZCEKLZMZUBZBDFUCNJZOZAFCAPZBLZEUDLZNZUFZWDUENCIPZBLZWKNZWDQZ
      IFRWDWDQZIFRZSWHIFWPUGWMGUGWDAIFWLWPAIUHWJWOCWKWIWNBUIUJUKWBWCWEWGULWHEKU
      MWHWNFJZOZCWOWKUNUOWHWQWRIFXAWPWDWDXAWPWDWOWKNZWDXACWDWOWKWBWCWEWGWTUPURX
      AWBWOEUQLZJZXBWDMWBWCWEWGWTUSWHWTXDWGWTXDUTZWFWGFDBVAZXEBDFVBXFWTXDXFWTOW
      ODXCFDWNBVCHVDVJVEVFVGXCEWKWOWDXCTWKTWDTVHVKVIVLVMWHWRWAZIFVNWSSMWHXGIFXG
      WHWDVOVPVQWRIFVRVSVT $.

    $( The support of a mapping of a multiplication of a nonzero constant with
       a function into a (ring theoretic) domain equals the support of the
       function.  (Contributed by AV, 11-Apr-2019.) $)
    domnmsuppn0 $p |- ( ( ( M e. Domn /\ V e. X )
                       /\ ( C e. R /\ C =/= ( 0g ` M ) ) /\ A e. ( R ^m V ) )
               -> ( ( v e. V |-> ( C ( .r ` M ) ( A ` v ) ) ) supp ( 0g ` M ) )
                    = ( A supp ( 0g ` M ) ) ) $=
      ( vw wcel wa cfv wne co wceq syl 3ad2ant3 adantr ex cvv cdomn c0g cmap cv
      w3a cmulr crab cdm cmpt csupp wf elmapi fdm eqcomd oveq2 domnring anim12i
      crg 3adant3 eqid ringrz sylan9eqr necon3d simpl1l simpll2 wi ffvelcdm imp
      simpl simpr domnmuln0 syl112anc impbid rabeqbidva weq fveq2 oveq2d simp1r
      cbvmptv fvexd ovexd mptsuppd wfun elmapfun simp3 suppval1 syl3anc 3eqtr4d
      ) EUAJZFGJZKZCDJZCEUBLZMZKZBDFUCNZJZUEZCIUDZBLZEUFLZNZWMMZIFUGWTWMMZIBUHZ
      UGZAFCAUDZBLZXANZUIZWMUJNBWMUJNZWRXCXDIFXEWQWKFXEOZWOWQFDBUKZXLBDFULZXMXE
      FFDBUMUNPQWRWSFJZKZXCXDXPWTWMXBWMXPWTWMOZXBWMOXQXPXBCWMXANZWMWTWMCXAUOWRX
      RWMOZXOWREURJZWLKZXSWKWOYAWQWKXTWOWLWIXTWJEUPRWLWNVIUQUSDEXACWMHXAUTZWMUT
      ZVAPRVBSVCXPXDXCXPXDKWIWOWTDJZXDXCXPWIXDWIWJWOWQXOVDRWKWOWQXOXDVEXPYDXDWR
      XOYDWQWKXOYDVFZWOWQXMYEXNXMXOYDFDWSBVGSPQVHRXPXDVJDEXACWTWMHYBYCVKVLSVMVN
      WRIFXBTXJGTWMAIFXIXBAIVOXHWTCXAXGWSBVPVQVSWIWJWOWQVRWREUBVTZXPCWTXAWAWBWR
      BWCZWQWMTJXKXFOWQWKYGWOBDFWDQWKWOWQWEYFIWPTBWMWFWGWH $.

    $( The support of a mapping of a multiplication of a constant with a
       function into a ring is a subset of the support of the function.
       (Contributed by AV, 11-Apr-2019.) $)
    rmsuppss $p |- ( ( ( M e. Ring /\ V e. X /\ C e. R ) /\ A e. ( R ^m V ) )
               -> ( ( v e. V |-> ( C ( .r ` M ) ( A ` v ) ) ) supp ( 0g ` M ) )
                  C_ ( A supp ( 0g ` M ) ) ) $=
      ( vw wcel co wa cv cfv c0g wne crab csupp wceq cvv crg w3a cmap cmulr cdm
      cmpt oveq2 simpll1 simpll3 eqid ringrz syl2anc sylan9eqr necon3d ss2rabdv
      ex elmapi adantl rabeq syl sseqtrrd weq fveq2 oveq2d cbvmptv simpl2 fvexd
      fdmd ovexd mptsuppd wfun elmapfun simpr suppval1 syl3anc 3sstr4d ) EUAJZF
      GJZCDJZUBZBDFUCKZJZLZCIMZBNZEUDNZKZEONZPZIFQZWEWHPZIBUEZQZAFCAMZBNZWFKZUF
      ZWHRKBWHRKZWCWJWKIFQZWMWCWIWKIFWCWDFJZLZWEWHWGWHXAWEWHSZWGWHSXBXAWGCWHWFK
      ZWHWEWHCWFUGXAVQVSXCWHSVQVRVSWBWTUHVQVRVSWBWTUIDEWFCWHHWFUJWHUJUKULUMUPUN
      UOWCWLFSZWMWSSWBXDVTWBFDBBDFUQVHURWKIWLFUSUTVAWCIFWGTWQGTWHAIFWPWGAIVBWOW
      ECWFWNWDBVCVDVEVQVRVSWBVFWCEOVGZXACWEWFVIVJWCBVKZWBWHTJWRWMSWBXFVTBDFVLUR
      VTWBVMXEIWATBWHVNVOVP $.
  $}

  ${
    $d A v x $.  $d M v x $.  $d R v x $.  $d S x $.  $d V v x $.
    scmsuppss.s $e |- S = ( Scalar ` M ) $.
    scmsuppss.r $e |- R = ( Base ` S ) $.
    $( The support of a mapping of a scalar multiplication with a function of
       scalars is a subset of the support of the function of scalars.
       (Contributed by AV, 5-Apr-2019.) $)
    scmsuppss $p |- ( ( M e. LMod /\ V e. ~P ( Base ` M ) /\ A e. ( R ^m V ) )
               -> ( ( v e. V |-> ( ( A ` v ) ( .s ` M ) v ) ) supp ( 0g ` M ) )
                  C_ ( A supp ( 0g ` S ) ) ) $=
      ( vx wcel cfv co c0g wne crab wi wceq wa cvv eqid clmod cbs cpw w3a cvsca
      cmap cv cmpt cdm csupp wss wf elmapi fdm eqidd weq fveq2 id oveq12d simpr
      adantl ovex a1i fvmptd neeq1d oveq1 simplrr elelpwi expcom adantr lmod0vs
      syl2anc sylan9eqr ex necon3d sylbid ss2rabdv wb dmmpti rabeq mp1i sseq12d
      imp mpbird exp43 mpcom syl com13 3imp wfun funmpt 3ad2ant2 fvexd suppval1
      mptexg syl3anc elmapfun 3ad2ant3 simp3 3sstr4d ) EUAJZFEUBKZUCZJZBCFUFLZJ
      ZUDZIUGZAFAUGZBKZXIEUEKZLZUHZKZEMKZNZIXMUIZOZXHBKZDMKZNZIBUIZOZXMXOUJLZBX
      TUJLZXAXDXFXRYCUKZXFXDXAYFXFFCBULZXDXAYFPPZBCFUMYBFQZYGYHFCBUNYIYGXDXAYFY
      IYGRZXDXARZRZYFXPIFOZYAIFOZUKZYLXPYAIFYLXHFJZRZXPXSXHXKLZXONYAYQXNYRXOYQA
      XHXLYRFXMSYQXMUOAIUPZXLYRQYQYSXJXSXIXHXKXIXHBUQYSURUSVAYLYPUTYRSJYQXSXHXK
      VBVCVDVEYQXSXTYRXOYQXSXTQZYRXOQYTYQYRXTXHXKLZXOXSXTXHXKVFYQXAXHXBJZUUAXOQ
      YJXDXAYPVGYLYPUUBYKYPUUBPZYJXDUUCXAYPXDUUBXHFXBVHVIVJVAWCXKDXTXBEXHXOXBTG
      XKTXTTXOTVKVLVMVNVOVPVQYJYFYOVRZYKYIUUDYGYIXRYMYCYNXQFQXRYMQYIAFXLXMXJXIX
      KVBXMTVSXPIXQFVTWAYAIYBFVTWBVJVJWDWEWFWGWHWIXGXMWJZXMSJZXOSJYDXRQUUEXGAFX
      LWKVCXDXAUUFXFAFXLXCWOWLXGEMWMISSXMXOWNWPXGBWJZXFXTSJYEYCQXFXAUUGXDBCFWQW
      RXAXDXFWSXGDMWMIXESBXTWNWPWT $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Finitely supported functions (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A v $.  $d C v $.  $d M v $.  $d R v $.  $d X v $.  $d V v $.
    rmsuppfi.r $e |- R = ( Base ` M ) $.
    $( The support of a mapping of a multiplication of a constant with a
       function into a ring is finite if the support of the function is finite.
       (Contributed by AV, 11-Apr-2019.) $)
    rmsuppfi $p |- ( ( ( M e. Ring /\ V e. X /\ C e. R )
                       /\ A e. ( R ^m V ) /\ ( A supp ( 0g ` M ) ) e. Fin )
                     -> ( ( v e. V |-> ( C ( .r ` M ) ( A ` v ) ) )
                          supp ( 0g ` M ) ) e. Fin ) $=
      ( crg wcel w3a cmap co c0g cfv csupp cfn cv cmulr cmpt wss simp3 rmsuppss
      3adant3 ssfi syl2anc ) EIJFGJCDJKZBDFLMJZBENOZPMZQJZKUKAFCARBOESOMTUIPMZU
      JUAZULQJUGUHUKUBUGUHUMUKABCDEFGHUCUDUJULUEUF $.

    $( A mapping of a multiplication of a constant with a function into a ring
       is finitely supported if the function is finitely supported.
       (Contributed by AV, 9-Jun-2019.) $)
    rmfsupp $p |- ( ( ( M e. Ring /\ V e. X /\ C e. R )
                      /\ A e. ( R ^m V ) /\ A finSupp ( 0g ` M ) )
           -> ( v e. V |-> ( C ( .r ` M ) ( A ` v ) ) ) finSupp ( 0g ` M ) ) $=
      ( crg wcel w3a cmap co c0g cfv cfsupp wbr csupp cfn cvv cmulr cmpt funmpt
      cv wfun id fsuppimpd rmsuppfi syl3an3 wa wb mptexg 3ad2ant2 3ad2ant1 fvex
      a1i isfsupp sylancl mpbir2and ) EIJZFGJZCDJZKZBDFLMJZBENOZPQZKZAFCAUDBOEU
      AOMZUBZVEPQZVIUEZVIVERMSJZVKVGAFVHUCUPVFVCVDBVERMSJVLVFBVEVFUFUGABCDEFGHU
      HUIVGVITJZVETJVJVKVLUJUKVCVDVMVFVAUTVMVBAFVHGULUMUNENUOVITTVEUQURUS $.
  $}

  ${
    $d A v $.  $d M v $.  $d R v $.  $d V v $.
    scmsuppfi.s $e |- S = ( Scalar ` M ) $.
    scmsuppfi.r $e |- R = ( Base ` S ) $.
    $( The support of a mapping of a scalar multiplication with a function of
       scalars is finite if the support of the function of scalars is finite.
       (Contributed by AV, 5-Apr-2019.) $)
    scmsuppfi $p |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) )
                        /\ A e. ( R ^m V ) /\ ( A supp ( 0g ` S ) ) e. Fin )
                      -> ( ( v e. V |-> ( ( A ` v ) ( .s ` M ) v ) )
                                          supp ( 0g ` M ) ) e. Fin ) $=
      ( clmod wcel cbs cfv cpw wa cmap co c0g csupp cfn w3a cv cvsca cmpt simp3
      wss simpll simplr simpr 3jca 3adant3 scmsuppss syl ssfi syl2anc ) EIJZFEK
      LMJZNZBCFOPJZBDQLRPZSJZTZUTAFAUAZBLVBEUBLPUCEQLRPZUSUEZVCSJUQURUTUDVAUOUP
      URTZVDUQURVEUTUQURNUOUPURUOUPURUFUOUPURUGUQURUHUIUJABCDEFGHUKULUSVCUMUN
      $.

    $( A mapping of a scalar multiplication with a function of scalars is
       finitely supported if the function of scalars is finitely supported.
       (Contributed by AV, 9-Jun-2019.) $)
    scmfsupp $p |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) )
                       /\ A e. ( R ^m V ) /\ A finSupp ( 0g ` S ) )
           -> ( v e. V |-> ( ( A ` v ) ( .s ` M ) v ) ) finSupp ( 0g ` M ) ) $=
      ( clmod wcel cbs cfv wa co c0g cfsupp wbr csupp cfn cvv cpw cmap cv cvsca
      w3a cmpt funmpt a1i id fsuppimpd scmsuppfi syl3an3 mptexg adantl 3ad2ant1
      wfun wb fvex isfsupp sylancl mpbir2and ) EIJZFEKLUAZJZMZBCFUBNJZBDOLZPQZU
      EZAFAUCZBLVJEUDLNZUFZEOLZPQZVLUPZVLVMRNSJZVOVIAFVKUGUHVHVEVFBVGRNSJVPVHBV
      GVHUIUJABCDEFGHUKULVIVLTJZVMTJVNVOVPMUQVEVFVQVHVDVQVBAFVKVCUMUNUOEOURVLTT
      VMUSUTVA $.
  $}

  ${
    $d B v x $.  $d F v x $.  $d M v x $.  $d V v x $.  $d X v x $.
    $d .1. v x $.  $d .0. v x $.
    suppmptcfin.b $e |- B = ( Base ` M ) $.
    suppmptcfin.r $e |- R = ( Scalar ` M ) $.
    suppmptcfin.0 $e |- .0. = ( 0g ` R ) $.
    suppmptcfin.1 $e |- .1. = ( 1r ` R ) $.
    suppmptcfin.f $e |- F = ( x e. V |-> if ( x = X , .1. , .0. ) ) $.
    $( The support of a mapping with value 0 except of one is finite.
       (Contributed by AV, 27-Apr-2019.) $)
    suppmptcfin $p |- ( ( M e. LMod /\ V e. ~P B /\ X e. V )
                        -> ( F supp .0. ) e. Fin ) $=
      ( vv wcel wceq cfn cvv a1i clmod cpw w3a csupp co cif wne crab cmpt eqeq1
      cv weq ifbid cbvmptv eqtri simp2 c0g fvexi wa cur ifcld mptsuppd csn snfi
      wss wi wral wn iffalse adantr neeq1d eqid eqneqall ax-mp biimtrdi pm2.61i
      2a1 ex ralrimiva rabsssn sylibr ssfi sylancr eqeltrd ) FUAPZGBUBZPZHGPZUC
      ZEIUDUEOUKZHQZDIUFZIUGZOGUHZRWIOGWLSEWFSIEAGAUKZHQZDIUFZUIOGWLUINAOGWQWLA
      OULWPWKDIWOWJHUJUMUNUOWEWGWHUPISPZWIICUQLURZTWIWJGPUSZWKDISDSPWTDCUTMURTW
      RWTWSTVAVBWIHVCZRPWNXAVEZWNRPHVDWIWMWKVFZOGVGXBWIXCOGWKWTXCVFWKWTWMVQWKVH
      ZWTXCXDWTUSZWMIIUGZWKXEWLIIXDWLIQWTWKDIVIVJVKIIQXFWKVFIVLWKIIVMVNVOVRVPVS
      WMOGHVTWAXAWNWBWCWD $.

    $( A mapping with value 0 except of one is finitely supported.
       (Contributed by AV, 9-Jun-2019.) $)
    mptcfsupp $p |- ( ( M e. LMod /\ V e. ~P B /\ X e. V )
                      -> F finSupp .0. ) $=
      ( clmod wcel cpw w3a cfsupp cvv wbr wfun csupp co cfn cv wceq cif funmpt2
      a1i suppmptcfin wa wb cmpt mptexg eqeltrid 3ad2ant2 fvexi isfsupp sylancl
      c0g mpbir2and ) FOPZGBQZPZHGPZRZEISUAZEUBZEIUCUDUEPZVIVGAGAUFHUGDIUHZENUI
      UJABCDEFGHIJKLMNUKVGETPZITPVHVIVJULUMVEVCVLVFVEEAGVKUNTNAGVKVDUOUPUQICVAL
      URETTIUSUTVB $.
  $}

  ${
    $d A x $.  $d V x $.
    fsuppmptdmf.n $e |- F/ x ph $.
    fsuppmptdmf.f $e |- F = ( x e. A |-> Y ) $.
    fsuppmptdmf.a $e |- ( ph -> A e. Fin ) $.
    fsuppmptdmf.y $e |- ( ( ph /\ x e. A ) -> Y e. V ) $.
    fsuppmptdmf.z $e |- ( ph -> Z e. W ) $.
    $( A mapping with a finite domain is finitely supported.  (Contributed by
       AV, 4-Sep-2019.) $)
    fsuppmptdmf $p |- ( ph -> F finSupp Z ) $=
      ( fmptdf fdmfifsupp ) ACEDFHABCGEDILJNKMO $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Left modules (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d E x y $.  $d K x y $.  $d N x y $.  $d R x y $.  $d V x y $.
    $d W x y $.  $d X x y $.  $d .x. x y $.  $d .^ x y $.
    lmodvsmdi.v $e |- V = ( Base ` W ) $.
    lmodvsmdi.f $e |- F = ( Scalar ` W ) $.
    lmodvsmdi.s $e |- .x. = ( .s ` W ) $.
    lmodvsmdi.k $e |- K = ( Base ` F ) $.
    lmodvsmdi.p $e |- .^ = ( .g ` W ) $.
    lmodvsmdi.e $e |- E = ( .g ` F ) $.
    $( Multiple distributive law for scalar product (left-distributivity).
       (Contributed by AV, 5-Sep-2019.) $)
    lmodvsmdi $p |- ( ( W e. LMod /\ ( R e. K /\ N e. NN0 /\ X e. V ) ) ->
                     ( R .x. ( N .^ X ) ) = ( ( N E R ) .x. X ) ) $=
      ( wcel co wceq oveq1 vx vy cn0 w3a clmod wi wa cv cc0 caddc oveq2d oveq1d
      c1 eqeq12d imbi2d weq c0g cfv simpr adantr eqid mulg0 simpl anim1i ancomd
      lmodvs0 lmod0vs eqcomd 3eqtr2d eqtrd cplusg cmnd lmodgrp grpmndd ad2antll
      syl adantl syl3anc simprll mulgnn0cld lmodvsdi syl13anc sylan9eq lmodfgrp
      mulgnn0p1 lmodvsdir eqtr3d exp31 a2d nn0ind exp4c com12 3imp impcom ) AFQ
      ZGUCQZJHQZUDIUEQZAGJDRZBRZGACRZJBRZSZWOWPWQWRXCUFZWPWOWQXDUFWPWOWQWRXCWOW
      QUGZWRUGZAUAUHZJDRZBRZXGACRZJBRZSZUFXFAUIJDRZBRZUIACRZJBRZSZUFXFAUBUHZJDR
      ZBRZXRACRZJBRZSZUFXFAXRUMUJRZJDRZBRZYDACRZJBRZSZUFXFXCUFUAUBGXGUISZXLXQXF
      YJXIXNXKXPYJXHXMABXGUIJDTUKYJXJXOJBXGUIACTULUNUOUAUBUPZXLYCXFYKXIXTXKYBYK
      XHXSABXGXRJDTUKYKXJYAJBXGXRACTULUNUOXGYDSZXLYIXFYLXIYFXKYHYLXHYEABXGYDJDT
      UKYLXJYGJBXGYDACTULUNUOXGGSZXLXCXFYMXIWTXKXBYMXHWSABXGGJDTUKYMXJXAJBXGGAC
      TULUNUOXFXNAIUQURZBRZXPXFXMYNABXFWQXMYNSXEWQWRWOWQUSZUTZHDIJYNKYNVAZOVBVP
      UKXFYOYNEUQURZJBRZXPXFWRWOUGYOYNSXFWOWRXEWOWRWOWQVCZVDVEBEFIAYNLMNYRVFVPX
      FWRWQUGYTYNSXFWQWRXEWQWRYPVDVEBEYSHIJYNKLMYSVAZYRVGVPXFYSXOJBXFWOYSXOSXEW
      OWRUUAUTWOXOYSFCEAYSNUUBPVBVHVPULVIVJXRUCQZXFYCYIUUCXFYCYIUUCXFUGZYCUGYFY
      BAJBRZIVKURZRZYHUUDYCYFXTUUEUUFRZUUGUUDYFAXSJUUFRZBRZUUHUUDYEUUIABUUDIVLQ
      ZUUCWQYEUUISWRUUKUUCXEWRIIVMVNVOZUUCXFVCZXFWQUUCYQVQZHUUFDIXRJKOUUFVAZWEV
      RUKUUDWRWOXSHQWQUUJUUHSXFWRUUCXEWRUSVQZUUCWOWQWRVSZUUDHDIXRJKOUULUUMUUNVT
      UUNUUFABEFHIXSJKUUOLMNWAWBVJXTYBUUEUUFTWCUUDUUGYHSYCUUDYAAEVKURZRZJBRZUUG
      YHUUDWRYAFQWOWQUUTUUGSUUPUUDFCEXRANPWREVLQZUUCXEWREEILWDVNVOZUUMUUQVTUUQU
      UNUUFUURYAABEFHIJKUUOLMNUURVAZWFWBUUDUUSYGJBUUDYGUUSUUDUVAUUCWOYGUUSSUVBU
      UMUUQFUURCEXRANPUVCWEVRVHULWGUTVJWHWIWJWKWLWMWN $.
  $}

  ${
    $d B v $.  $d F v $.  $d M v $.  $d R v $.  $d S v $.  $d V v $.  $d Z v $.
    gsumlsscl.s $e |- S = ( LSubSp ` M ) $.
    gsumlsscl.r $e |- R = ( Scalar ` M ) $.
    gsumlsscl.b $e |- B = ( Base ` R ) $.
    $( Closure of a group sum in a linear subspace:  A (finitely supported) sum
       of scalar multiplications of vectors of a subset of a linear subspace is
       also contained in the linear subspace.  (Contributed by AV,
       20-Apr-2019.)  (Revised by AV, 28-Jul-2019.) $)
    gsumlsscl $p |- ( ( M e. LMod /\ Z e. S /\ V C_ Z )
                      -> ( ( F e. ( B ^m V ) /\ F finSupp ( 0g ` R ) )
            -> ( M gsum ( v e. V |-> ( ( F ` v ) ( .s ` M ) v ) ) ) e. Z ) ) $=
      ( wcel wss co cfv wa cvv adantr syl wi clmod w3a cmap c0g cfsupp cv cvsca
      wbr cmpt cgsu eqid cabl lmodabl ssexg ancoms 3adant1 csubg 3simpa lsssubg
      3ad2ant1 wf elmapi ffvelcdm ex ad2antrl imp ssel 3ad2ant3 syl12anc fmpttd
      lssvscl cbs cpw simp1 lssss sstr expcom a1i wb elpwg mpbird simprl simprr
      3imp jca scmfsupp syl3anc gsumsubgcl ) FUALZHDLZGHMZUBZEBGUCNLZECUDOUEUHZ
      PZFAGAUFZEOZWPFUGOZNZUIZUJNHLWLWOPZGHWTFQFUDOZXBUKWLFULLZWOWIWJXCWKFUMUTR
      WLGQLZWOWJWKXDWIWKWJXDGHDUNUOUPZRWLHFUQOLZWOWLWIWJPZXFWIWJWKURZDHFIUSSRXA
      AGWSHXAWPGLZPXGWQBLZWPHLZWSHLXAXGXIWLXGWOXHRRXAXIXJWMXIXJTZWLWNWMGBEVAZXL
      EBGVBXMXIXJGBWPEVCVDSVEVFXAXIXKWLXIXKTZWOWKWIXNWJGHWPVGVHRVFBDWRHCFWQWPJW
      RUKKIVKVIVJXAWIGFVLOZVMLZPZWMWNWTXBUEUHWLXQWOWLWIXPWIWJWKVNWLXPGXOMZWIWJW
      KXRWJWKXRTZTWIWJHXOMZXSDHXOFXOUKIVOWKXTXRGHXOVPVQSVRWDWLXDXPXRVSXEGXOQVTS
      WAWERWLWMWNWBWLWMWNWCAEBCFGJKWFWGWHVD $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Associative algebras (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    assaascl0.a $e |- A = ( algSc ` W ) $.
    assaascl0.f $e |- F = ( Scalar ` W ) $.
    assaascl0.w $e |- ( ph -> W e. AssAlg ) $.
    $( The scalar 0 embedded into an associative algebra corresponds to the 0
       of the associative algebra.  (Contributed by AV, 31-Jul-2019.) $)
    assaascl0 $p |- ( ph -> ( A ` ( 0g ` F ) ) = ( 0g ` W ) ) $=
      ( casa wcel clmod assalmod syl crg assaring ascl0 ) ABCDEFADHIZDJIGDKLAPD
      MIGDNLO $.

    $( The scalar 1 embedded into an associative algebra corresponds to the 1
       of the an associative algebra.  (Contributed by AV, 31-Jul-2019.) $)
    assaascl1 $p |- ( ph -> ( A ` ( 1r ` F ) ) = ( 1r ` W ) ) $=
      ( casa wcel clmod assalmod syl crg assaring ascl1 ) ABCDEFADHIZDJIGDKLAPD
      MIGDNLO $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Univariate polynomials (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    ply1vr1smo.p $e |- P = ( Poly1 ` R ) $.
    ply1vr1smo.i $e |- .1. = ( 1r ` R ) $.
    ply1vr1smo.t $e |- .x. = ( .s ` P ) $.
    ply1vr1smo.m $e |- G = ( mulGrp ` P ) $.
    ply1vr1smo.e $e |- .^ = ( .g ` G ) $.
    ply1vr1smo.x $e |- X = ( var1 ` R ) $.
    $( The variable in a polynomial expressed as scaled monomial.  (Contributed
       by AV, 12-Aug-2019.) $)
    ply1vr1smo $p |- ( R e. Ring -> ( .1. .x. ( 1 .^ X ) ) = X ) $=
      ( crg wcel co cfv cur wceq eqid c1 ply1sca fveq2d eqtrid oveq1d clmod cbs
      csca ply1lmod vr1cl mgpbas mulg1 syl eqeltrd lmodvs1 syl2anc 3eqtrd ) BNO
      ZDUAGEPZCPAUHQZRQZUSCPZUSGURDVAUSCURDBRQVAIURBUTRABNHUBUCUDUEURAUFOUSAUGQ
      ZOVBUSSABHUIURUSGVCURGVCOUSGSVCABGMHVCTZUJZVCEFGVCAFKVDUKLULUMZVEUNCVAUTV
      CAUSVDUTTJVATUOUPVFUQ $.
  $}

  ${
    ply1sclrmsm.k $e |- K = ( Base ` R ) $.
    ply1sclrmsm.p $e |- P = ( Poly1 ` R ) $.
    ply1sclrmsm.b $e |- E = ( Base ` P ) $.
    ply1sclrmsm.x $e |- X = ( var1 ` R ) $.
    ply1sclrmsm.s $e |- .x. = ( .s ` P ) $.
    ply1sclrmsm.m $e |- .X. = ( .r ` P ) $.
    ply1sclrmsm.n $e |- N = ( mulGrp ` P ) $.
    ply1sclrmsm.e $e |- .^ = ( .g ` N ) $.
    ply1sclrmsm.a $e |- A = ( algSc ` P ) $.
    $( The ring multiplication of a polynomial with a scalar polynomial is
       equal to the scalar multiplication of the polynomial with the
       corresponding scalar.  (Contributed by AV, 14-Aug-2019.) $)
    ply1sclrmsm $p |- ( ( R e. Ring /\ F e. K /\ Z e. E )
                      -> ( ( A ` F ) .X. Z ) = ( F .x. Z ) ) $=
      ( crg wcel w3a cfv co cur wceq wa cbs ply1sca fveq2d eqtrid eleq2d biimpa
      csca eqid asclval 3adant3 oveq1d eleq2i biimpi 3ad2ant2 ply1ring ringidcl
      syl simp1 3ad2ant1 simp3 ply1ass23l syl13anc ringlidm sylan oveq2d 3eqtrd
      3adant2 ) CUBUCZHIUCZLFUCZUDZHAUEZLEUFHBUGUEZDUFZLEUFZHWBLEUFZDUFZHLDUFVT
      WAWCLEVQVRWAWCUHZVSVQVRUIHBUPUEZUJUEZUCZWGVQVRWJVQIWIHVQICUJUEZWIMVQCWHUJ
      BCUBNUKULUMUNUOADWBWHWIBHUAWHUQWIUQQWBUQZURVFUSUTVTVQHWKUCZWBFUCZVSWDWFUH
      VQVRVSVGVRVQWMVSVRWMIWKHMVAVBVCVQVRWNVSVQBUBUCZWNBCNVDZFBWBOWLVEVFVHVQVRV
      SVIHFBCDEWKWBLNROWKUQQVJVKVTWELHDVQVSWELUHZVRVQWOVSWQWPFBEWBLORWLVLVMVPVN
      VO $.
  $}

  ${
    coe1sclmulval.p $e |- P = ( Poly1 ` R ) $.
    coe1sclmulval.b $e |- B = ( Base ` P ) $.
    coe1sclmulval.k $e |- K = ( Base ` R ) $.
    coe1sclmulval.a $e |- A = ( algSc ` P ) $.
    coe1sclmulval.s $e |- S = ( .s ` P ) $.
    coe1sclmulval.t $e |- .xb = ( .r ` P ) $.
    coe1sclmulval.u $e |- .x. = ( .r ` R ) $.
    $( The value of the coefficient vector of a polynomial multiplied on the
       left by a scalar.  (Contributed by AV, 14-Aug-2019.) $)
    coe1sclmulval $p |- ( ( R e. Ring /\ ( Y e. K /\ Z e. B ) /\ N e. NN0 )
        -> ( ( coe1 ` ( Y S Z ) ) ` N ) = ( Y .x. ( ( coe1 ` Z ) ` N ) ) ) $=
      ( wcel cfv crg wa cn0 w3a co cco1 cascl wceq simp1 simp2l simp2r cmgp cmg
      cv1 eqid ply1sclrmsm syl3anc eqcomd fveq2d fveq1d coe1sclmulfv eqtrd ) DU
      ASZJHSZKBSZUBZIUCSZUDZIJKEUEZUFTZTIJCUGTZTKFUEZUFTZTJIKUFTTGUEVHIVJVMVHVI
      VLUFVHVLVIVHVCVDVEVLVIUHVCVFVGUIVCVDVEVGUJVCVDVEVGUKVKCDEFBCULTZUMTZJHVND
      UNTZKNLMVPUOPQVNUOVOUOVKUOZUPUQURUSUTVKBCDFGHJKILMNVQQRVAVB $.
  $}

  ${
    ply1mulgsum.p $e |- P = ( Poly1 ` R ) $.
    ply1mulgsum.b $e |- B = ( Base ` P ) $.
    ply1mulgsum.a $e |- A = ( coe1 ` K ) $.
    ply1mulgsum.c $e |- C = ( coe1 ` L ) $.
    ply1mulgsum.x $e |- X = ( var1 ` R ) $.
    ply1mulgsum.pm $e |- .X. = ( .r ` P ) $.
    ply1mulgsum.sm $e |- .x. = ( .s ` P ) $.
    ply1mulgsum.rm $e |- .* = ( .r ` R ) $.
    ply1mulgsum.m $e |- M = ( mulGrp ` P ) $.
    ply1mulgsum.e $e |- .^ = ( .g ` M ) $.
    $d A a b n s $.  $d B a b n s $.  $d C a b n s $.  $d K a b n s $.
    $d L a b n s $.  $d R a b n s $.
    $( Lemma 1 for ~ ply1mulgsum .  (Contributed by AV, 19-Oct-2019.) $)
    ply1mulgsumlem1 $p |- ( ( R e. Ring /\ K e. B /\ L e. B )
        -> E. s e. NN0 A. n e. NN0 ( s < n -> ( ( A ` n ) = ( 0g ` R )
                                             /\ ( C ` n ) = ( 0g ` R ) ) ) ) $=
      ( vb va crg wcel w3a cv clt wbr cfv c0g wceq wi wral wrex wa eqid coe1ae0
      3ad2ant2 3ad2ant3 caddc co nn0addcl adantr wb breq1 imbi1d ralbidv adantl
      cn0 r19.26 cc nn0cn addcomd breq1d nn0sumltlt sylbid 3expia ancoms imim1d
      3adant3 com23 anim12d ancomd exp31 ralimdva biimtrrid rspcedvd expd com34
      imp impancom com14 impcom rexlimiva com13 mpcom mpd ) EUHUIZKBUIZLBUIZUJZ
      UFUKZHUKZULUMZXHAUNEUOUNZUPZUQZHVNURZUFVNUSZOUKZXHULUMZXKXHCUNXJUPZUTZUQZ
      HVNURZOVNUSZXDXCXNXEABDEHKXJUFRQPXJVAZVBVCUGUKZXHULUMZXQUQZHVNURZUGVNUSZX
      FXNYAUQZXEXCYGXDCBDEHLXJUGSQPYBVBVDYFXFYHUQUGVNXNXFYCVNUIZYFUTZYAXMXFYJYA
      UQUQZUFVNXMXGVNUIZYKYJYLXFXMYAYIYLYFXFXMYAUQUQYIYLUTZYFXMXFYAYMYFXMXFYAUQ
      YMXFYFXMUTZYAYMXFYNYAYMXFUTZYNUTZXTYCXGVEVFZXHULUMZXRUQZHVNURZOYQVNYOYQVN
      UIZYNYMUUAXFYCXGVGVHVHXOYQUPZXTYTVIYPUUBXSYSHVNUUBXPYRXRXOYQXHULVJVKVLVMY
      OYNYTYNYEXLUTZHVNURYOYTYEXLHVNVOYOUUCYSHVNYOXHVNUIZUTZYRUUCXRUUEYRUUCXRUU
      EYRUTZUUCUTXQXKUUFUUCXQXKUTUUFYEXQXLXKUUEYRYEXQUQUUEYEYRXQUUEYRYDXQYOUUDY
      RYDUQZYMUUDUUGUQZXFYLYIUUHYLYIUUDUUGYLYIUUDUJZYRXGYCVEVFZXHULUMYDUUIYQUUJ
      XHULYLYIYQUUJUPUUDYLYIUTYCXGYIYCVPUIYLYCVQVMYLXGVPUIYIXGVQVHVRWEVSUFUGHVT
      WAWBWCVHWOWDWFWOUUEYRXLXKUQUUEXLYRXKUUEYRXIXKYOUUDYRXIUQZYMUUDUUKUQXFYIYL
      UUDUUKUGUFHVTWBVHWOWDWFWOWGWOWHWIWFWJWKWOWLWIWFWMWNWPWQWRWSWTWSXAXB $.

    $d A l n x z $.  $d B l x z $.  $d C l x z $.  $d K l x z $.  $d L l x z $.
    $d R l x z $.  $d s l x z $.  $d .* s z $.
    $( Lemma 2 for ~ ply1mulgsum .  (Contributed by AV, 19-Oct-2019.) $)
    ply1mulgsumlem2 $p |- ( ( R e. Ring /\ K e. B /\ L e. B )
              -> E. s e. NN0 A. n e. NN0 ( s < n -> ( R gsum ( l e. ( 0 ... n )
                 |-> ( ( A ` l ) .* ( C ` ( n - l ) ) ) ) ) = ( 0g ` R ) ) ) $=
      ( vz vx cv clt wbr cfv c0g wceq wa wi cn0 wral wrex crg wcel w3a cc0 cmin
      cfz co cmpt cgsu ply1mulgsumlem1 c2 cmul 2nn0 id nn0mulcld ad2antrr breq1
      a1i wb imbi1d ralbidv adantl cle cr 2re nn0re remulcld adantr elfznn0 syl
      ltsub1d lesub2d resubcld resubcl syl2an lelttr syl3anc cc 2txmxeqx breq1d
      nn0cn sylibd expcomd sylbid ex com23 imp41 impcom fznn0sub2 breq2 fveqeq2
      imp anbi12d imbi12d rspcva simpr syl6 3syl com12 ad4antlr mpd cbs simplr1
      oveq2d simplr2 anim12i eqid coe1fvalcl ringrz syl2anc eqtrd bicomd expcom
      wn ltnle syl11 ad4antr weq simpl oveq1d cvv simplr3 ringlz pm2.61ian cmnd
      fznn0sub mpteq2dva 3ad2ant1 ovex jctir ad3antlr gsumz ralrimiva rexlimiva
      ringmnd rspcedvd mpcom ) UGUIZUHUIZUJUKZUURAULEUMULZUNZUURCULUUTUNZUOZUPZ
      UHUQURZUGUQUSEUTVAZKBVAZLBVAZVBZOUIZHUIZUJUKZEPVCUVKVEVFZPUIZAULZUVKUVNVD
      VFZCULZJVFZVGZVHVFZUUTUNZUPZHUQURZOUQUSZABCDEFGUHIJKLMNUGQRSTUAUBUCUDUEUF
      VIUVEUVIUWDUPUGUQUUQUQVAZUVEUOZUVIUWDUWFUVIUOZUWCVJUUQVKVFZUVKUJUKZUWAUPZ
      HUQURZOUWHUQUWEUWHUQVAUVEUVIUWEVJUUQVJUQVAUWEVLVQUWEVMVNVOUVJUWHUNZUWCUWK
      VRUWGUWLUWBUWJHUQUWLUVLUWIUWAUVJUWHUVKUJVPVSVTWAUWGUWJHUQUWGUVKUQVAZUOZUW
      IUWAUWNUWIUOZUVTEPUVMUUTVGZVHVFZUUTUWOUVSUWPEVHUWOPUVMUVRUUTUVNUUQWBUKZUW
      OUVNUVMVAZUOZUVRUUTUNUWRUWTUOZUVRUVOUUTJVFZUUTUXAUVQUUTUVOJUXAUUQUVPUJUKZ
      UVQUUTUNZUWTUWRUXCUWGUWMUWIUWSUWRUXCUPZUWEUWMUWIUWSUXEUPUPZUPUVEUVIUWEUWM
      UXFUWEUWMUOZUWSUWIUXEUXGUWSUWIUXEUPUXGUWSUOZUWIUWHUVNVDVFZUVPUJUKZUXEUXHU
      WHUVKUVNUWEUWHWCVAZUWMUWSUWEVJUUQVJWCVAUWEWDVQUUQWEZWFZVOZUXGUVKWCVAZUWSU
      WMUXOUWEUVKWEWAZWGUWSUVNWCVAZUXGUWSUVNUQVAZUXQUVNUVKWHZUVNWEZWIZWAZWJUXHU
      XJUXEUXHUXJUOUWRUWHUUQVDVFZUXIWBUKZUXCUXHUWRUYDVRUXJUXHUVNUUQUWHUYBUWEUUQ
      WCVAZUWMUWSUXLVOUXNWKWGUXHUXJUYDUXCUPUXHUYDUXJUXCUXHUYDUXJUOZUYCUVPUJUKZU
      XCUXHUYCWCVAZUXIWCVAZUVPWCVAZUYFUYGUPUWEUYHUWMUWSUWEUWHUUQUXMUXLWLVOUXGUX
      KUXQUYIUWSUWEUXKUWMUXMWGUYAUWHUVNWMWNUXGUXOUXQUYJUWSUXPUYAUVKUVNWMWNUYCUX
      IUVPWOWPUXHUYCUUQUVPUJUWEUYCUUQUNZUWMUWSUWEUUQWQVAUYKUUQWTUUQWRWIVOWSXAXB
      XKXCXDXCXDXEXDVOXFXGUWTUXCUXDUPZUWRUWOUWSUYLUVEUWSUYLUPUWEUVIUWMUWIUWSUVE
      UYLUWSUVPUVMVAUVPUQVAZUVEUYLUPUVNUVKXHUVPUVKWHUYMUVEUYLUYMUVEUOUXCUVPAULU
      UTUNZUXDUOZUXDUVDUXCUYOUPUHUVPUQUURUVPUNZUUSUXCUVCUYOUURUVPUUQUJXIUYPUVAU
      YNUVBUXDUURUVPUUTAXJUURUVPUUTCXJXLXMXNUYNUXDXOXPXDXQXRXSXKWAXTYCUXAUVFUVO
      EYAULZVAZUXBUUTUNUWTUVFUWRUWNUVFUWIUWSUVFUVGUVHUWFUWMYBVOZWAUXAUVGUXRUOZU
      YRUWTUYTUWRUWOUVGUWSUXRUWNUVGUWIUVFUVGUVHUWFUWMYDWGUXSYEWAABDEKUYQUVNSRQU
      YQYFZYGWIUYQEJUVOUUTVUAUDUUTYFZYHYIYJUWRYMZUWTUOZUVRUUTUVQJVFZUUTVUDUVOUU
      TUVQJUWTVUCUVOUUTUNZUWTVUCUUQUVNUJUKZVUFUWOUWSVUCVUGVRZUWEUWSVUHUPUVEUVIU
      WMUWIUXRUWEVUHUWSUWEUXRVUHUWEUXRUOVUGVUCUWEUYEUXQVUGVUCVRUXRUXLUXTUUQUVNY
      NWNYKYLUXSYOYPXKUWOUWSVUGVUFUPZUVEUWSVUIUPUWEUVIUWMUWIUXRUVEVUIUWSUXRUVEV
      UIUXRUVEUOVUGVUFUVNCULUUTUNZUOZVUFUVDVUGVUKUPUHUVNUQUHPYQZUUSVUGUVCVUKUUR
      UVNUUQUJXIVULUVAVUFUVBVUJUURUVNUUTAXJUURUVNUUTCXJXLXMXNVUFVUJYRXPXDUXSYOX
      SXKXCXGYSVUDUVFUVQUYQVAZVUEUUTUNUWTUVFVUCUYSWAVUDUVHUYMUOZVUMUWTVUNVUCUWO
      UVHUWSUYMUWNUVHUWIUVFUVGUVHUWFUWMUUAWGUVNVCUVKUUEYEWACBDELUYQUVPTRQVUAYGW
      IUYQEJUVQUUTVUAUDVUBUUBYIYJUUCUUFYCUWOEUUDVAZUVMYTVAZUOZUWQUUTUNUVIVUQUWF
      UWMUWIUVIVUOVUPUVFUVGVUOUVHEUUNUUGVCUVKVEUUHUUIUUJUVMPEYTUUTVUBUUKWIYJXDU
      ULUUOXDUUMUUP $.

    $d A k $.  $d B k $.  $d C k $.  $d K k $.  $d L k $.  $d R k $.
    $d .* k n $.  $d k l $.  $d k s $.
    $( Lemma 3 for ~ ply1mulgsum .  (Contributed by AV, 20-Oct-2019.) $)
    ply1mulgsumlem3 $p |- ( ( R e. Ring /\ K e. B /\ L e. B )
           -> ( k e. NN0 |-> ( R gsum ( l e. ( 0 ... k )
           |-> ( ( A ` l ) .* ( C ` ( k - l ) ) ) ) ) ) finSupp ( 0g ` R ) ) $=
      ( vn vs crg wcel w3a cvv cc0 cv cfz co cfv cmin cmpt cgsu c0g fvexd ovexd
      cn0 wa clt wbr wceq wi wral wrex csb ply1mulgsumlem2 vex csbov2g id oveq2
      fvoveq1 oveq2d mpteq12dv adantl csbied eqtrd ax-mp simpr eqtrid ex imim2d
      ralimdva reximdva mpd mptnn0fsupp ) EUHUIKBUILBUIUJZUFUKEOULHUMZUNUOZOUMZ
      AUPZWMWOUQUOCUPZJUOZURZUSUOZHUKEUTUPZUGWLEUTVAWLWMVCUIVDEWSUSVBWLUGUMZUFU
      MZVEVFZEOULXCUNUOZWPXCWOUQUOCUPZJUOZURZUSUOZXAVGZVHZUFVCVIZUGVCVJXDHXCWTV
      KZXAVGZVHZUFVCVIZUGVCVJABCDEFGUFIJKLMNUGOPQRSTUAUBUCUDUEVLWLXLXPUGVCWLXBV
      CUIVDZXKXOUFVCXQXCVCUIVDZXJXNXDXRXJXNXRXJVDXMXIXAXCUKUIZXMXIVGUFVMXSXMEHX
      CWSVKZUSUOXIHXCEWSUSUKVNXSXTXHEUSXSHXCWSXHUKXSVOWMXCVGZWSXHVGXSYAOWNWRXEX
      GWMXCULUNVPYAWQXFWPJWMXCWOCUQVQVRVSVTWAVRWBWCXRXJWDWEWFWGWHWIWJWK $.

    $d P n s $.  $d X k n s $.  $d .^ k n s $.  $d .x. k n s $.  $d k l n s $.
    $( Lemma 4 for ~ ply1mulgsum .  (Contributed by AV, 19-Oct-2019.) $)
    ply1mulgsumlem4 $p |- ( ( R e. Ring /\ K e. B /\ L e. B )
             -> ( k e. NN0 |-> ( ( R gsum ( l e. ( 0 ... k )
                  |-> ( ( A ` l ) .* ( C ` ( k - l ) ) ) ) ) .x. ( k .^ X ) ) )
                finSupp ( 0g ` P ) ) $=
      ( vn vs crg wcel w3a cvv cc0 cv cfz co cfv cmin cmpt cgsu c0g fvexd ovexd
      cn0 wa clt wbr wceq wi wral wrex csb ply1mulgsumlem2 vex csbov12g csbov2g
      oveq2 fvoveq1 oveq2d mpteq12dv adantl csbied eqtrd csbov1g csbvarg oveq1d
      id oveq12d ax-mp oveq1 csca ply1sca 3ad2ant1 ad2antrr fveq2d clmod mgpbas
      ply1lmod cmnd ply1ring ringmgp syl simpr vr1cl mulgnn0cld lmod0vs syl2anc
      eqid sylan9eqr eqtrid ex imim2d ralimdva reximdva mpd mptnn0fsupp ) EUHUI
      ZKBUIZLBUIZUJZUFUKEOULHUMZUNUOZOUMZAUPZXTYBUQUOCUPZJUOZURZUSUOZXTNIUOZFUO
      ZHUKDUTUPZUGXSDUTVAXSXTVCUIVDYGYHFVBXSUGUMZUFUMZVEVFZEOULYLUNUOZYCYLYBUQU
      OCUPZJUOZURZUSUOZEUTUPZVGZVHZUFVCVIZUGVCVJYMHYLYIVKZYJVGZVHZUFVCVIZUGVCVJ
      ABCDEFGUFIJKLMNUGOPQRSTUAUBUCUDUEVLXSUUBUUFUGVCXSYKVCUIZVDZUUAUUEUFVCUUHY
      LVCUIZVDZYTUUDYMUUJYTUUDUUJYTVDUUCYRYLNIUOZFUOZYJYLUKUIZUUCUULVGUFVMUUMUU
      CHYLYGVKZHYLYHVKZFUOUULHYLYGYHFUKVNUUMUUNYRUUOUUKFUUMUUNEHYLYFVKZUSUOYRHY
      LEYFUSUKVOUUMUUPYQEUSUUMHYLYFYQUKUUMWFXTYLVGZYFYQVGUUMUUQOYAYEYNYPXTYLULU
      NVPUUQYDYOYCJXTYLYBCUQVQVRVSVTWAVRWBUUMUUOHYLXTVKZNIUOUUKHYLXTNIUKWCUUMUU
      RYLNIHYLUKWDWEWBWGWBWHYTUUJUULYSUUKFUOZYJYRYSUUKFWIUUJUUSDWJUPZUTUPZUUKFU
      OZYJUUJYSUVAUUKFUUJEUUTUTXSEUUTVGZUUGUUIXPXQUVCXRDEUHPWKWLWMWNWEUUJDWOUIZ
      UUKBUIUVBYJVGXSUVDUUGUUIXPXQUVDXRDEPWQWLWMUUJBIMYLNBDMUDQWPUEXSMWRUIZUUGU
      UIXPXQUVEXRXPDUHUIUVEDEPWSDMUDWTXAWLWMUUHUUIXBXSNBUIZUUGUUIXPXQUVFXRBDENT
      PQXCWLWMXDFUUTUVABDUUKYJQUUTXGUBUVAXGYJXGXEXFWBXHXIXJXKXLXMXNXO $.

    $d A i $.  $d B m $.  $d C i $.  $d K i m n $.  $d L i m $.  $d P k $.
    $d R i m $.  $d .X. m n $.  $d .* i l m $.
    $( The product of two polynomials expressed as group sum of scaled
       monomials.  (Contributed by AV, 20-Oct-2019.) $)
    ply1mulgsum $p |- ( ( R e. Ring /\ K e. B /\ L e. B )
       -> ( K .X. L ) = ( P gsum ( k e. NN0 |-> ( ( R gsum ( l e. ( 0 ... k )
           |-> ( ( A ` l ) .* ( C ` ( k - l ) ) ) ) ) .x. ( k .^ X ) ) ) ) ) $=
      ( vn vm vi crg wcel w3a cv co cco1 cfv cn0 cc0 cfz cmin cmpt cgsu wceq wa
      coe1mul adantr fveq1d cvv eqidd weq oveq2 fvoveq1 oveq2d mpteq12dv adantl
      wral simpr ovexd fvmptd csb cbs c0g cmg cmgp fveq2i eqtri simp1 eqid ccmn
      ringcmn 3ad2ant1 ad2antrr fzfid simpll1 simp2 elfznn0 coe1fvalcl fznn0sub
      syl2an ringcl syl3anc ralrimiva gsummptcl wbr ply1mulgsumlem3 gsummoncoe1
      simp3 cfsupp vex csbov2g id csbied eqtrd mp1i fveq2 fveq1i eqtrdi oveq12d
      fveq2d cbvmptv a1i 3eqtrrd 3eqtrd wb ply1ring syl3an1 nn0ex csca ply1lmod
      syl clmod ply1sca eleqtrd mgpbas ringmgp vr1cl mulgnn0cld lmodvscl fmpttd
      cmnd ply1mulgsumlem4 gsumcl ply1coe1eq mpbid ) EUIUJZKBUJZLBUJZUKZUFULZKL
      GUMZUNUOZUOZUUHDHUPEOUQHULZURUMZOULZAUOZUULUUNUSUMZCUOZJUMZUTZVAUMZUULNIU
      MZFUMZUTZVAUMZUNUOZUOZVBZUFUPVOZUUIUVDVBZUUGUVGUFUPUUGUUHUPUJZVCZUUKUUHUG
      UPEUHUQUGULZURUMZUHULZKUNUOZUOZUVLUVNUSUMLUNUOZUOZJUMZUTZVAUMZUTZUOEUHUQU
      UHURUMZUVPUUHUVNUSUMZUVQUOZJUMZUTZVAUMZUVFUVKUUHUUJUWBUUGUUJUWBVBUVJUHBEG
      JUGKLDPUAUCQVDVEVFUVKUGUUHUWAUWHUPUWBVGUVKUWBVHUGUFVIZUWAUWHVBUVKUWIUVTUW
      GEVAUWIUHUVMUVSUWCUWFUVLUUHUQURVJUWIUVRUWEUVPJUVLUUHUVNUVQUSVKVLVMVLVNUUG
      UVJVPZUVKEUWGVAVQVRUVKUVFHUUHUUTVSZEOUWCUUOUUHUUNUSUMZCUOZJUMZUTZVAUMZUWH
      UVKUUTBDEHIFEVTUOZUUHNEWAUOZPQTIMWBUODWCUOZWBUOUEMUWSWBUDWDWEUUGUUDUVJUUD
      UUEUUFWFZVEUWQWGZUBUWRWGUVKUUTUWQUJHUPUVKUULUPUJZVCZUWQOEUUMUURUXAUUGEWHU
      JZUVJUXBUUDUUEUXDUUFEWIWJZWKUXCUQUULWLUXCUURUWQUJZOUUMUXCUUNUUMUJZVCUUDUU
      OUWQUJZUUQUWQUJZUXFUXCUUDUXGUUDUUEUUFUVJUXBWMVEUXCUUEUUNUPUJZUXHUXGUUGUUE
      UVJUXBUUDUUEUUFWNZWKUUNUULWOZABDEKUWQUUNRQPUXAWPZWRUXCUUFUUPUPUJZUXIUXGUU
      GUUFUVJUXBUUDUUEUUFXFZWKUUNUQUULWQZCBDELUWQUUPSQPUXAWPZWRUWQEJUUOUUQUXAUC
      WSZWTXAXBXAUUGHUPUUTUTUWRXGXCUVJABCDEFGHIJKLMNOPQRSTUAUBUCUDUEXDVEUWJXEUU
      HVGUJZUWKUWPVBUVKUFXHUXSUWKEHUUHUUSVSZVAUMUWPHUUHEUUSVAVGXIUXSUXTUWOEVAUX
      SHUUHUUSUWOVGUXSXJHUFVIZUUSUWOVBUXSUYAOUUMUURUWCUWNUULUUHUQURVJUYAUUQUWMU
      UOJUULUUHUUNCUSVKVLVMVNXKVLXLXMUVKUWOUWGEVAUWOUWGVBUVKOUHUWCUWNUWFOUHVIZU
      UOUVPUWMUWEJUYBUUOUVNAUOUVPUUNUVNAXNUVNAUVORXOXPUYBUWMUWDCUOUWEUYBUWLUWDC
      UUNUVNUUHUSVJXRUWDCUVQSXOXPXQXSXTVLYAYBXAUUGUUDUUIBUJZUVDBUJUVHUVIYCUWTUU
      DDUIUJZUUEUUFUYCDEPYDZBDGKLQUAWSYEUUGUPBUVCDVGDWAUOZQUYFWGUUDUUEDWHUJZUUF
      UUDUYDUYGUYEDWIYIWJUPVGUJUUGYFXTUUGHUPUVBBUUGUXBVCZDYJUJZUUTDYGUOZVTUOZUJ
      UVABUJUVBBUJUUGUYIUXBUUDUUEUYIUUFDEPYHWJVEUYHUUTUWQUYKUYHUWQOEUUMUURUXAUU
      GUXDUXBUXEVEUYHUQUULWLUYHUXFOUUMUYHUXGVCUUDUXHUXIUXFUUDUUEUUFUXBUXGWMUYHU
      UEUXJUXHUXGUUGUUEUXBUXKVEUXLUXMWRUYHUUFUXNUXIUXGUUGUUFUXBUXOVEUXPUXQWRUXR
      WTXAXBUYHEUYJVTUYHUUDEUYJVBUUGUUDUXBUWTVEDEUIPYKYIXRYLUYHBIMUULNBDMUDQYMU
      EUUGMYSUJZUXBUUDUUEUYLUUFUUDUYDUYLUYEDMUDYNYIWJVEUUGUXBVPUUGNBUJZUXBUUDUU
      EUYMUUFBDENTPQYOWJVEYPUUTFUYJUYKBDUVAQUYJWGUBUYKWGYQWTYRABCDEFGHIJKLMNOPQ
      RSTUAUBUCUDUEYTUUAUUJBUVEDEUFUUIUVDPQUUJWGUVEWGUUBWTUUC $.
  $}

  ${
    evl1at0.o $e |- O = ( eval1 ` R ) $.
    evl1at0.p $e |- P = ( Poly1 ` R ) $.
    ${
      evl1at0.0 $e |- .0. = ( 0g ` R ) $.
      evl1at0.z $e |- Z = ( 0g ` P ) $.
      $( Polynomial evaluation for the 0 scalar.  (Contributed by AV,
         10-Aug-2019.) $)
      evl1at0 $p |- ( R e. CRing -> ( ( O ` Z ) ` .0. ) = .0. ) $=
        ( ccrg wcel cfv cascl crg wceq crngring eqid ply1scl0 syl cbs eqcomd id
        fveq2d fveq1d cgrp ringgrp grpidcl 3syl evl1scad simprd eqtrd ) BJKZDEC
        LZLDDAMLZLZCLZLZDULDUMUPULEUOCULUOEULBNKZUOEOBPZUNABEDGUNQZHIRSUAUCUDUL
        UOATLZKUQDOULUNBTLZABVACDDFGVBQZUTVAQULUBULURBUEKDVBKUSBUFVBBDVCHUGUHZV
        DUIUJUK $.
    $}

    evl1at1.1 $e |- .1. = ( 1r ` R ) $.
    evl1at1.i $e |- I = ( 1r ` P ) $.
    $( Polynomial evaluation for the 1 scalar.  (Contributed by AV,
       10-Aug-2019.) $)
    evl1at1 $p |- ( R e. CRing -> ( ( O ` I ) ` .1. ) = .1. ) $=
      ( ccrg wcel cfv cascl crg wceq crngring eqid ply1scl1 syl cbs id ringidcl
      eqcomd fveq2d fveq1d evl1scad simprd eqtrd ) BJKZCDELZLCCAMLZLZELZLZCUICU
      JUMUIDULEUIULDUIBNKZULDOBPZUKABCDGUKQZHIRSUCUDUEUIULATLZKUNCOUIUKBTLZABUR
      ECCFGUSQZUQURQUIUAUIUOCUSKUPUSBCUTHUBSZVAUFUGUH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Univariate polynomials (examples)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    linply1.p $e |- P = ( Poly1 ` R ) $.
    linply1.b $e |- B = ( Base ` P ) $.
    linply1.k $e |- K = ( Base ` R ) $.
    linply1.x $e |- X = ( var1 ` R ) $.
    linply1.m $e |- .- = ( -g ` P ) $.
    linply1.a $e |- A = ( algSc ` P ) $.
    linply1.g $e |- G = ( X .- ( A ` C ) ) $.
    linply1.c $e |- ( ph -> C e. K ) $.
    ${
      linply1.r $e |- ( ph -> R e. Ring ) $.
      $( A term of the form ` x - C ` is a (univariate) polynomial, also called
         "linear polynomial".  (Part of ~ ply1remlem ).  (Contributed by AV,
         3-Jul-2019.) $)
      linply1 $p |- ( ph -> G e. B ) $=
        ( wcel cfv co cgrp crg ply1ring ringgrp vr1cl syl wf ply1sclf ffvelcdmd
        3syl grpsubcl syl3anc eqeltrid ) AGJDBUAZIUBZCQAEUCTZJCTZUPCTUQCTAFUDTZ
        EUDTURSEFKUEEUFULAUTUSSCEFJNKLUGUHAHCDBAUTHCBUISBCEFHKPMLUJUHRUKCEIJUPL
        OUMUNUO $.
    $}

    lineval.o $e |- O = ( eval1 ` R ) $.
    lineval.r $e |- ( ph -> R e. CRing ) $.
    lineval.v $e |- ( ph -> V e. K ) $.
    $( A term of the form ` x - C ` evaluated for ` x = V ` results in
       ` V - C ` (part of ~ ply1remlem ).  (Contributed by AV, 3-Jul-2019.) $)
    lineval $p |- ( ph -> ( ( O ` G ) ` V ) = ( V ( -g ` R ) C ) ) $=
      ( cfv co csg fveq2i fveq1i wcel wceq evl1vard evl1scad eqid simprd eqtrid
      evl1subd ) AKGJUDZUDKLDBUDZIUEZJUDZUDZKDFUFUDZUEZKUQUTGUSJSUGUHAUSCUIVAVC
      UJAHVBEFCLIURJKDKUAMONUBUCAHEFCJLKUAPOMNUBUCUKABHEFCJDKUAMORNUBTUCULQVBUM
      UPUNUO $.
  $}

  ${
    linevalexample.p $e |- P = ( Poly1 ` ZZring ) $.
    linevalexample.b $e |- B = ( Base ` P ) $.
    linevalexample.x $e |- X = ( var1 ` ZZring ) $.
    linevalexample.m $e |- .- = ( -g ` P ) $.
    linevalexample.a $e |- A = ( algSc ` P ) $.
    linevalexample.g $e |- G = ( X .- ( A ` 3 ) ) $.
    linevalexample.o $e |- O = ( eval1 ` ZZring ) $.
    $( The polynomial ` x - 3 ` over ` ZZ ` evaluated for ` x = 5 ` results in
       2.  (Contributed by AV, 3-Jul-2019.) $)
    linevalexample $p |- ( ( O ` ( X .- ( A ` 3 ) ) ) ` 5 ) = 2 $=
      ( c5 c3 cfv co czring wcel csg cmin c2 ccrg wceq zringcrng cz zringbas 3z
      eqid a1i id 5nn0 nn0zi lineval ax-mp zringsubgval mp2an 5cn 3cn 2cn 3p2e5
      subaddrii 3eqtr2i ) OGPAQERZFQQZOPSUAQZRZOPUBRZUCSUDTZVFVHUEUFVJABPCSVEUG
      EFOGHIUHJKLVEUJPUGTZVJUIUKNVJULOUGTZVJOUMUNZUKUOUPVLVKVIVHUEVMUIVGOPVGUJU
      QUROPUCUSUTVAVBVCVD $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Linear algebra (extension)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The subalgebras of diagonal and scalar matrices (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  In the following, alternative definitions for diagonal and scalar matrices
  are provided.  These definitions define diagonal and scalar matrices as
  _extensible structures_, whereas Definitions ~ df-dmat and ~ df-scmat define
  diagonal and scalar matrices as _sets_.

$)

  $c DMatALT ScMatALT $.

  $( Alternative notation for the algebra of diagonal matrices. $)
  cdmatalt $a class DMatALT $.

  $( Alternative notation for the algebra of scalar matrices. $)
  cscmatalt $a class ScMatALT $.

  ${
    $d a i j m n r $.
    $( Define the set of n x n diagonal (square) matrices over a set (usually a
       ring) r, see definition in [Roman] p. 4 or Definition 3.12 in [Hefferon]
       p. 240.  (Contributed by AV, 8-Dec-2019.) $)
    df-dmatalt $a |- DMatALT = ( n e. Fin , r e. _V |-> [_ ( n Mat r ) / a ]_
                       ( a |`s { m e. ( Base ` a ) | A. i e. n A. j e. n
                                 ( i =/= j -> ( i m j ) = ( 0g ` r ) ) } ) ) $.
  $}

  ${
    $d a c i j m n r $.
    $( Define the algebra of n x n scalar matrices over a set (usually a ring)
       r, see definition in [Connell] p. 57:  "A _scalar matrix_ is a diagonal
       matrix for which all the diagonal terms are equal, i.e., a matrix of the
       form cI_n".  (Contributed by AV, 8-Dec-2019.) $)
    df-scmatalt $a |- ScMatALT = ( n e. Fin , r e. _V |-> [_ ( n Mat r ) / a ]_
         ( a |`s { m e. ( Base ` a ) | E. c e. ( Base ` r ) A. i e. n A. j e. n
                             ( i m j ) = if ( i = j , c , ( 0g ` r ) ) } ) ) $.
  $}

  ${
    $d A n r $.  $d B m n r $.  $d N a i j m n r $.  $d R a i j m n r $.
    $d .0. n r $.
    dmatALTval.a $e |- A = ( N Mat R ) $.
    dmatALTval.b $e |- B = ( Base ` A ) $.
    dmatALTval.0 $e |- .0. = ( 0g ` R ) $.
    dmatALTval.d $e |- D = ( N DMatALT R ) $.
    $( The algebra of ` N ` x ` N ` diagonal matrices over a ring ` R ` .
       (Contributed by AV, 8-Dec-2019.) $)
    dmatALTval $p |- ( ( N e. Fin /\ R e. _V )
                    -> D = ( A |`s { m e. B | A. i e. N A. j e. N
                                     ( i =/= j -> ( i m j ) = .0. ) } ) ) $=
      ( va co cv wceq cress cfv cbs vn vr cfn wcel cvv wa cdmatalt wi wral crab
      wne cmat c0g csb ovexd fveq2 rabeqdv oveq12d adantl csbied oveq12 eqtr4di
      id fveq2d simpl eqeq2d imbi2d raleqbidv rabeqbidv eqtrd df-dmatalt ovmpoa
      ovex eqtrid ) HUCUDDUEUDUFCHDUGOAEPZFPZUKZVOVPGPOZIQZUHZFHUIZEHUIZGBUJZRO
      ZMUAUBHDUCUENUAPZUBPZULOZNPZVQVRWFUMSZQZUHZFWEUIZEWEUIZGWHTSZUJZROZUNZWDU
      GWEHQZWFDQZUFZWQWGWMGWGTSZUJZROZWDWTNWGWPXCUEWTWEWFULUOWHWGQZWPXCQWTXDWHW
      GWOXBRXDVCXDWMGWNXAWHWGTUPUQURUSUTWTWGAXBWCRWTWGHDULOAWEHWFDULVAJVBZWTWMW
      BGXABWTXAATSBWTWGATXEVDKVBWTWLWAEWEHWRWSVEZWTWKVTFWEHXFWTWJVSVQWTWIIVRWSW
      IIQWRWSWIDUMSIWFDUMUPLVBUSVFVGVHVHVIURVJEFGUAUBNVKAWCRVMVLVN $.

    $( The base set of the algebra of ` N ` x ` N ` diagonal matrices over a
       ring ` R ` , i.e. the set of all ` N ` x ` N ` diagonal matrices over
       the ring ` R ` .  (Contributed by AV, 8-Dec-2019.) $)
    dmatALTbas $p |- ( ( N e. Fin /\ R e. _V )
             -> ( Base ` D ) = { m e. B | A. i e. N A. j e. N
                                          ( i =/= j -> ( i m j ) = .0. ) } ) $=
      ( wcel cvv cbs cfv cv co wceq cfn wa wi wral crab cress dmatALTval fveq2d
      wne cin fvexi rabexg mp1i eqid ressbas inrab2 inidm rabeq eqtrid 3eqtr2d
      syl ) HUANDONUBZCPQAERZFRZUIVCVDGRSITUCFHUDEHUDZGBUEZUFSZPQZVFBUJZVFVBCVG
      PABCDEFGHIJKLMUGUHVBVFONZVIVHTBONVJVBBAPKUKVEGBOULUMVFBVGOAVGUNKUOVAVBVIV
      EGBBUJZUEZVFVEGBBUPVKBTVLVFTVBBUQVEGVKBURUMUSUT $.

    $d M i j m $.  $d .0. m $.
    $( An element of the base set of the algebra of ` N ` x ` N ` diagonal
       matrices over a ring ` R ` , i.e. an ` N ` x ` N ` diagonal matrix over
       the ring ` R ` .  (Contributed by AV, 8-Dec-2019.) $)
    dmatALTbasel $p |- ( ( N e. Fin /\ R e. _V ) -> ( M e. ( Base ` D )
                        <-> ( M e. B /\ A. i e. N A. j e. N
                                        ( i =/= j -> ( i M j ) = .0. ) ) ) ) $=
      ( vm wcel wa cv co wceq wral cfn cvv cbs cfv wne dmatALTbas eleq2d eqeq1d
      wi crab oveq imbi2d 2ralbidv elrab bitrdi ) HUAODUBOPZGCUCUDZOGEQZFQZUEZU
      RUSNQZRZISZUIZFHTEHTZNBUJZOGBOUTURUSGRZISZUIZFHTEHTZPUPUQVFGABCDEFNHIJKLM
      UFUGVEVJNGBVAGSZVDVIEFHHVKVCVHUTVKVBVGIURUSVAGUKUHULUMUNUO $.
  $}

  ${
    $d B m $.  $d N i j m $.  $d R i j m $.
    dmatbas.a $e |- A = ( N Mat R ) $.
    dmatbas.b $e |- B = ( Base ` A ) $.
    dmatbas.0 $e |- .0. = ( 0g ` R ) $.
    dmatbas.d $e |- D = ( N DMat R ) $.
    $( The set of all ` N ` x ` N ` diagonal matrices over (the ring) ` R ` is
       the base set of the algebra of ` N ` x ` N ` diagonal matrices over (the
       ring) ` R ` .  (Contributed by AV, 8-Dec-2019.) $)
    dmatbas $p |- ( ( N e. Fin /\ R e. V )
                    -> D = ( Base ` ( N DMatALT R ) ) ) $=
      ( vi vj vm cfn wcel cv co wceq wral wne crab cdmatalt cbs cfv dmatval cvv
      wa wi elex eqid dmatALTbas sylan2 eqtr4d ) EOPZDFPZUHCLQZMQZUAUQURNQRGSUI
      METLETNBUBZEDUCRZUDUEZABCDLMNEFGHIJKUFUPUODUGPVAUSSDFUJABUTDLMNEGHIJUTUKU
      LUMUN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Linear combinations
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  <HTML>
  According to Wikipedia ("Linear combination", 29-Mar-2019,
  ~ https://en.wikipedia.org/wiki/Linear_combination ) "In mathematics, a
  <b>linear combination</b> is an expression constructed from a set of terms by
  multiplying each term by a constant and adding the results (e.g., a linear
  combination of x and y would be any expression of the form ax + by, where a
  and b are constants).  The concept of linear combinations is central to
  linear algebra and related fields of mathematics."  In linear algebra, these
  "terms" are "vectors" (elements from vector spaces or left modules), and the
  constants are elements of the underlying field resp. ring.  This corresponds
  to the definition in [Lang] p. 129:  "Let M be a module over a ring A and let
  S be a subset of M.  By a <b>linear combination</b> of elements of S (with
  <b>coefficients</b> in A) one means a sum &sum;<sub>x &isin;S</sub>
  a<sub>x</sub>x where {a<sub>x</sub>} is a set of elements of A, ...".  In the
  definition in [Lang] p. 129, it is additionally claimed that "..., almost all
  of which [elements of A] are equal to 0.".  This is not necessarily required
  in the following definition ~ df-linc , but it is essential if additions and
  scalar multiplications of linear combinations are considered.  Therefore, we
  define the set of all linear combinations with finite support in ~ df-lco ,
  so that we can show that such sets are submodules of the corresponding
  modules, see ~ lincolss .
  <br>

  <b>Remark:</b>According to Wikipedia ("Linear span", 28-Apr-2019,
  ~ https://en.wikipedia.org/wiki/Linear_span ) "In linear algebra, the
  <b>linear span</b> (also called the linear hull or just span) of a set of
  vectors in a vector space [or module] is the intersection of all linear
  subspaces which each contain every vector in that set.", and "Alternately,
  the span of [a set] S may be defined as the set of all finite linear
  combinations of elements (vectors) of S". Whereas spans are defined according
  to the first approach in ~ df-lsp , the set of all linear combinations as
  defined by ~ df-lco follows the alternative approach. That both definitions
  are equivalent is shown by ~ lspeqlco .
  </HTML>

$)

  $c linC LinCo $.

  $( Extend class notation with the operation constructing a linear combination
     (of vectors from a left module). $)
  clinc $a class linC $.

  $( Extend class notation with the operation constructing a set of linear
     combinations (of vectors from a left module) with finite support. $)
  clinco $a class LinCo $.

  ${
    $d m s v x $.
    $( Define the operation constructing a linear combination.  Although this
       definition is taylored for linear combinations of vectors from left
       modules, it can be used for any structure having a ` Base ` , ` Scalar `
       s and a scalar multiplication ` .s ` .  (Contributed by AV,
       29-Mar-2019.) $)
    df-linc $a |- linC = ( m e. _V
           |-> ( s e. ( ( Base ` ( Scalar ` m ) ) ^m v ) , v e. ~P ( Base ` m )
                |-> ( m gsum ( x e. v |-> ( ( s ` x ) ( .s ` m ) x ) ) ) ) ) $.
  $}

  ${
    $d c m s v $.
    $( Define the operation constructing the set of all linear combinations for
       a set of vectors.  (Contributed by AV, 31-Mar-2019.)  (Revised by AV,
       28-Jul-2019.) $)
    df-lco $a |- LinCo = ( m e. _V , v e. ~P ( Base ` m )
           |-> { c e. ( Base ` m ) | E. s e. ( ( Base ` ( Scalar ` m ) ) ^m v )
       ( s finSupp ( 0g ` ( Scalar ` m ) ) /\ c = ( s ( linC ` m ) v ) ) } ) $.
  $}

  ${
    $d M m s v x $.  $d X m v $.
    $( A linear combination as operation.  (Contributed by AV, 30-Mar-2019.) $)
    lincop $p |- ( M e. X -> ( linC ` M )
            = ( s e. ( ( Base ` ( Scalar ` M ) ) ^m v ) , v e. ~P ( Base ` M )
                |-> ( M gsum ( x e. v |-> ( ( s ` x ) ( .s ` M ) x ) ) ) ) ) $=
      ( vm wcel cv csca cfv cbs cmap co cpw cvsca cmpt cgsu cmpo cvv fveq2 wceq
      clinc df-linc 2fveq3 pweqd id oveqd mpteq2dv oveq12d mpoeq123dv elex wral
      oveq1d fvex pwex ovexd ralrimivw eqid mpoexxg2 sylancr fvmptd3 ) CDGZFCEB
      FHZIJKJZBHZLMZVCKJZNZVCAVEAHZEHJZVIVCOJZMZPZQMZREBCIJKJZVELMZCKJZNZCAVEVJ
      VICOJZMZPZQMZRZSUBSABFEUCVCCUAZEBVFVHVNVPVRWBWDVDVOVELVCCKIUDUMWDVGVQVCCK
      TUEWDVCCVMWAQWDUFWDAVEVLVTWDVKVSVJVIVCCOTUGUHUIUJCDUKVBVRSGVPSGZBVRULWCSG
      VQCKUNUOVBWEBVRVBVOVELUPUQEBVPVRWBSSWCWCURUSUTVA $.

    $d S s v x $.  $d V s v x $.
    $( The value of a linear combination.  (Contributed by AV, 30-Mar-2019.) $)
    lincval $p |- ( ( M e. X /\ S e. ( ( Base ` ( Scalar ` M ) ) ^m V )
                      /\ V e. ~P ( Base ` M ) ) -> ( S ( linC ` M ) V )
                    = ( M gsum ( x e. V |-> ( ( S ` x ) ( .s ` M ) x ) ) ) ) $=
      ( vs vv wcel csca cfv cbs cmap co cpw w3a cv cmpt cgsu wceq cvv lincop wa
      clinc cvsca 3ad2ant1 oveqd simp2 simp3 ovexd simpr fveq1 oveq1d mpteq12dv
      cmpo adantr oveq2d oveq2 eqid ovmpox2 syl3anc eqtrd ) CEHZBCIJKJZDLMZHZDC
      KJNZHZOZBDCUCJZMBDFGVCGPZLMZVFCAVJAPZFPZJZVLCUDJZMZQZRMZUNZMZCADVLBJZVLVO
      MZQZRMZVHVIVSBDVBVEVIVSSVGAGCEFUAUEUFVHVEVGWDTHVTWDSVBVEVGUGVBVEVGUHVHCWC
      RUIFGBDVKVFVRWDVSTVDVMBSZVJDSZUBZVQWCCRWGAVJVPDWBWEWFUJWEVPWBSWFWEVNWAVLV
      OVLVMBUKULUOUMUPVJDVCLUQVSURUSUTVA $.
  $}

  ${
    $d i m s v $.
    $( Alternative definition of linear combinations using the function
       operation.  (Contributed by AV, 1-Apr-2019.) $)
    dflinc2 $p |- linC = ( m e. _V
           |-> ( s e. ( ( Base ` ( Scalar ` m ) ) ^m v ) , v e. ~P ( Base ` m )
                 |-> ( m gsum ( s oF ( .s ` m ) ( _I |` v ) ) ) ) ) $=
      ( vi clinc cvv cv csca cfv cbs cmap co cpw cmpt cgsu cmpo wcel wa wfn a1i
      cvsca cid cres cof df-linc elmapfn adantr fnresi vex inidm wel eqidd wceq
      fvresi adantl offval eqcomd oveq2d mpoeq3ia mpteq2i eqtri ) EBFCABGZHIJIZ
      AGZKLZVBJIMZVBDVDDGZCGZIZVGVBUAIZLNZOLZPZNBFCAVEVFVBVHUBVDUCZVJUDLZOLZPZN
      DABCUEBFVMVQCAVEVFVLVPVHVEQZVDVFQZRZVKVOVBOVTVOVKVTDVDVDVIVGVJVDVHVNFFVRV
      HVDSVSVHVCVDUFUGVNVDSVTVDUHTVDFQVTAUITZWAVDUJVTDAUKZRVIULWBVGVNIVGUMVTVDV
      GUNUOUPUQURUSUTVA $.
  $}

  ${
    $d B c m v $.  $d M c m s v $.  $d R c m s v $.  $d S m v $.
    $d V c m s v $.
    lcoop.b $e |- B = ( Base ` M ) $.
    lcoop.s $e |- S = ( Scalar ` M ) $.
    lcoop.r $e |- R = ( Base ` S ) $.
    $( A linear combination as operation.  (Contributed by AV, 5-Apr-2019.)
       (Revised by AV, 28-Jul-2019.) $)
    lcoop $p |- ( ( M e. X /\ V e. ~P B ) -> ( M LinCo V )
         = { c e. B | E. s e. ( R ^m V ) ( s finSupp ( 0g ` S )
                                           /\ c = ( s ( linC ` M ) V ) ) } ) $=
      ( wcel wa cvv cbs cfv c0g co wceq adantr vm vv cpw cfsupp clinc cmap wrex
      cv wbr crab clinco elex pweqi eleq2i bilani fvexi mp1i csca fveq2 eqtr4di
      rabexg 2fveq3 fveq2i eqtri simpr oveq12d eqcomd fveq2d eqtrd breq2d eqidd
      oveq123d eqeq2d anbi12d rexeqbidv rabeqbidv pweqd df-lco ovmpox syl3anc
      a1i ) DFLZEAUCZLZMZDNLZEDOPZUCZLZGUHZCQPZUDUIZHUHZWJEDUEPZRZSZMZGBEUFRZUG
      ZHAUJZNLZDEUKRWTSWBWFWDDFULTWDWIWBWCWHEAWGIUMUNUOANLXAWEADOIUPWSHANVAUQUA
      UBDENUAUHZOPZUCWJXBURPZQPZUDUIZWMWJUBUHZXBUEPZRZSZMZGXDOPZXGUFRZUGZHXCUJW
      TUKNWHXBDSZXGESZMZXNWSHXCAXOXCASXPXOXCWGAXBDOUSZIUTTXQXKWQGXMWRXQXLBXGEUF
      XQXLDURPZOPZBXOXLXTSXPXBDOURVBTBCOPXTKCXSOJVCVDUTXOXPVEZVFXQXFWLXJWPXQXEW
      KWJUDXOXEWKSXPXOXEXSQPWKXBDQURVBXOXSCQXOCXSCXSSXOJWAVGVHVITVJXQXIWOWMXQWJ
      WJXGEXHWNXOXHWNSXPXBDUEUSTXQWJVKYAVLVMVNVOVPXOXCWGXRVQUBUAGHVRVSVT $.

    $d C c s $.  $d S c $.
    $( The value of a linear combination.  (Contributed by AV, 5-Apr-2019.)
       (Revised by AV, 28-Jul-2019.) $)
    lcoval $p |- ( ( M e. X /\ V e. ~P B ) -> ( C e. ( M LinCo V )
                      <-> ( C e. B /\ E. s e. ( R ^m V ) ( s finSupp ( 0g ` S )
                                         /\ C = ( s ( linC ` M ) V ) ) ) ) ) $=
      ( vc wcel cpw wa co cv cfv wceq wrex clinco c0g wbr clinc cmap crab lcoop
      cfsupp eleq2d eqeq1 anbi2d rexbidv elrab bitrdi ) EGMFANMOZBEFUAPZMBHQZDU
      BRUHUCZLQZUQFEUDRPZSZOZHCFUEPZTZLAUFZMBAMURBUTSZOZHVCTZOUOUPVEBACDEFGHLIJ
      KUGUIVDVHLBAUSBSZVBVGHVCVIVAVFURUSBUTUJUKULUMUN $.
  $}

  ${
    $d B v $.  $d F v $.  $d M v $.  $d S v $.  $d V v $.  $d W v $.
    $d .0. v $.
    lincfsuppcl.b $e |- B = ( Base ` M ) $.
    lincfsuppcl.r $e |- R = ( Scalar ` M ) $.
    lincfsuppcl.s $e |- S = ( Base ` R ) $.
    lincfsuppcl.0 $e |- .0. = ( 0g ` R ) $.
    $( A linear combination of vectors (with finite support) is a vector.
       (Contributed by AV, 25-Apr-2019.)  (Revised by AV, 28-Jul-2019.) $)
    lincfsuppcl $p |- ( ( M e. LMod /\ ( V e. W /\ V C_ B )
                          /\ ( F e. ( S ^m V ) /\ F finSupp .0. ) )
                        -> ( F ( linC ` M ) V ) e. B ) $=
      ( vv wcel wa cmap co cfsupp cfv cbs clmod wss wbr w3a clinc cv cvsca cmpt
      cgsu csca cpw wceq simp1 fveq2i eqtri oveq1i eleq2i birani 3ad2ant3 elpwg
      a1i eqcomd sseq2d bitr2d biimpa 3ad2ant2 lincval syl3anc c0g eqid lmodcmn
      ccmn 3ad2ant1 simpl adantr wi wf elmapi ffvelcdm ex syl imp ssel lmodvscl
      adantl fmpttd simp3r breqtrdi scmfsupp syl211anc gsumcl eqeltrd ) EUANZFG
      NZFAUBZOZDCFPQZNZDHRUCZOZUDZDFEUESQZEMFMUFZDSZXCEUGSZQZUHZUIQZAXAWMDEUJSZ
      TSZFPQZNZFETSZUKNZXBXHULWMWPWTUMZWTWMXLWPWRXLWSWQXKDCXJFPCBTSXJKBXITJUNUO
      UPUQURUSWPWMXNWTWNWOXNWNXNFXMUBWOFXMGUTWNXMAFWNAXMAXMULWNIVAVBVCVDVEVFZMD
      EFUAVGVHXAFAXGEGEVISZIXQVJWMWPEVLNWTEVKVMWPWMWNWTWNWOVNVFXAMFXFAXAXCFNZOW
      MXDCNZXCANZXFANXAWMXRXOVOXAXRXSWTWMXRXSVPZWPWRYAWSWRFCDVQZYADCFVRYBXRXSFC
      XCDVSVTWAVOUSWBXAXRXTWPWMXRXTVPZWTWOYCWNFAXCWCWEVFWBXDXEBCAEXCIJXEVJKWDVH
      WFXAWMXNWRDBVISZRUCXGXQRUCXOXPWTWMWRWPWRWSVNUSXADHYDRWMWPWRWSWGLWHMDCBEFJ
      KWIWJWKWL $.
  $}

  ${
    $d B v $.  $d M v $.  $d R v $.  $d S v $.  $d V v $.
    linccl.b $e |- B = ( Base ` M ) $.
    linccl.r $e |- R = ( Base ` ( Scalar ` M ) ) $.
    $( A linear combination of vectors is a vector.  (Contributed by AV,
       31-Mar-2019.) $)
    linccl $p |- ( ( M e. LMod /\ ( V e. Fin /\ V C_ B /\ S e. ( R ^m V ) ) )
                    -> ( S ( linC ` M ) V ) e. B ) $=
      ( vv wcel cfn cmap co wa cfv cbs adantl cvv syl3anc c0g eqid clmod wss cv
      w3a clinc cvsca cmpt cgsu csca cpw wceq simpl oveq1i eleq2i biimpi sseq2i
      3ad2ant3 wb fvex ssex elpwg syl ibir 3ad2ant2 lincval ccmn lmodcmn adantr
      sylbi simpr1 wi wf fvexi elmapg ffvelcdm ex biimtrdi imp 3adant2 lmodvscl
      mpan ssel fmpttd cfsupp wbr anim2i simpr3 elmapi fvexd fdmfifsupp eqeltrd
      scmfsupp gsumcl ) DUAIZEJIZEAUBZCBEKLZIZUDZMZCEDUENLZDHEHUCZCNZXBDUFNZLZU
      GZUHLZAWTWNCDUINZONZEKLZIZEDONZUJIZXAXGUKWNWSULZWSXKWNWRWOXKWPWRXKWQXJCBX
      IEKGUMUNUOUQPWSXMWNWPWOXMWRWPEXLUBZXMAXLEFUPXOXMXOEQIXMXOUREXLDOUSUTEXLQV
      AVBVCVIVDZPHCDEUAVERWTEAXFDJDSNZFXQTWNDVFIWSDVGVHWNWOWPWRVJZWTHEXEAWTXBEI
      ZMWNXCBIZXBAIZXEAIWTWNXSXNVHWTXSXTWSXSXTVKZWNWOWRYBWPWOWRYBWOWREBCVLZYBBQ
      IWOWRYCURBXHOGVMBECQJVNWAYCXSXTEBXBCVOVPVQVRVSPVRWTXSYAWSXSYAVKZWNWPWOYDW
      REAXBWBVDPVRXCXDXHBADXBFXHTZXDTGVTRWCWTWNXMMWRCXHSNZWDWEXFXQWDWEWSXMWNXPW
      FWNWOWPWRWGWTEBCQYFWSYCWNWRWOYCWPCBEWHUQPXRWTXHSWIWJHCBXHDEYEGWLRWMWK $.
  $}

  ${
    $d M v $.
    $( The value of an empty linear combination.  (Contributed by AV,
       12-Apr-2019.) $)
    lincval0 $p |- ( M e. X -> ( (/) ( linC ` M ) (/) ) = ( 0g ` M ) ) $=
      ( vv wcel c0 clinc cfv co cv cvsca cmpt cgsu c0g csca cbs wceq c1o eqtrdi
      cvv a1i cmap cpw csn 0ex snid fvex map0e df1o2 eleqtrrid lincval mpd3an23
      mp1i 0elpw mpt0 oveq2d eqid gsum0 eqtrd ) ABDZEEAFGHZACECIZEGVAAJGHZKZLHZ
      AMGZUSEANGZOGZEUAHZDEAOGZUBDZUTVDPUSEEUCZVHEUDUEUSVHQVKVGSDVHQPUSVFOUFVGS
      UGULUHRUIVJUSVIUMTCEAEBUJUKUSVDAELHVEUSVCEALVCEPUSCVBUNTUOAVEVEUPUQRUR $.
  $}

  ${
    $d B v $.  $d F v $.  $d M v $.  $d V v $.  $d Y v $.
    lincvalsn.b $e |- B = ( Base ` M ) $.
    lincvalsn.s $e |- S = ( Scalar ` M ) $.
    lincvalsn.r $e |- R = ( Base ` S ) $.
    lincvalsn.t $e |- .x. = ( .s ` M ) $.
    $( The linear combination over a singleton.  (Contributed by AV,
       25-May-2019.) $)
    lincvalsng $p |- ( ( M e. LMod /\ V e. B /\ Y e. R )
                   -> ( { <. V , Y >. } ( linC ` M ) { V } ) = ( Y .x. V ) ) $=
      ( vv clmod wcel csn cfv co cbs wceq syl3anc w3a cop clinc cvsca cmpt cgsu
      cv csca cmap cpw simp1 cvv simp2 fveq2i eqtri eleq2i biimpi 3ad2ant3 eqid
      fvexd mapsnop snelpwi eleq2s 3ad2ant2 lincval cmnd lmodgrp 3ad2ant1 fvsng
      grpmndd 3adant1 oveq1d lmodvscl 3com23 eqeltrd fveq2 id gsumsn eqcomi a1i
      oveq12d eqidd oveq123d 3eqtrd ) EMNZFANZGBNZUAZFGUBOZFOZEUCPQZELWJLUGZWIP
      ZWLEUDPZQZUEUFQZFWIPZFWNQZGFDQWHWEWIEUHPZRPZWJUIQNZWJERPZUJNZWKWPSWEWFWGU
      KWHWFGWTNZWTULNXAWEWFWGUMZWGWEXDWFWGXDBWTGBCRPWTJCWSRIUNUOUPUQURWHWSRUTWT
      WIAULFGWIUSVATWFWEXCWGXCFXBAFXBVBHVCVDLWIEWJMVETWHEVFNZWFWRANWPWRSWEWFXFW
      GWEEEVGVJVHXEWHWRGFWNQZAWHWQGFWNWFWGWQGSWEFGABVIVKZVLWEWGWFXGANGWNCBAEFHI
      WNUSJVMVNVOWOAWRLEFAHWLFSZWMWQWLFWNWLFWIVPXIVQWAVRTWHWQGFFWNDWNDSWHDWNKVS
      VTXHWHFWBWCWD $.

    ${
      lincvalsn.f $e |- F = { <. V , Y >. } $.
      $( The linear combination over a singleton.  (Contributed by AV,
         12-Apr-2019.)  (Proof shortened by AV, 25-May-2019.) $)
      lincvalsn $p |- ( ( M e. LMod /\ V e. B /\ Y e. R )
                       -> ( F ( linC ` M ) { V } ) = ( Y .x. V ) ) $=
        ( clmod wcel w3a csn clinc cfv co cop oveq1i lincvalsng eqtrid ) FNOGAO
        HBOPEGQZFRSZTGHUAQZUEUFTHGDTEUGUEUFMUBABCDFGHIJKLUCUD $.
    $}

    $d W v $.
    lincvalpr.p $e |- .+ = ( +g ` M ) $.
    lincvalpr.f $e |- F = { <. V , X >. , <. W , Y >. } $.
    $( The linear combination over an unordered pair.  (Contributed by AV,
       16-Apr-2019.) $)
    lincvalpr $p |- ( ( ( M e. LMod /\ V =/= W ) /\ ( V e. B /\ X e. R )
             /\ ( W e. B /\ Y e. R ) ) -> ( F ( linC ` M ) { V , W } )
                                          = ( ( X .x. V ) .+ ( Y .x. W ) ) ) $=
      ( wcel cfv co vv clmod wne wa w3a cpr clinc cvsca cmpt cgsu csca cbs cmap
      cv cpw wceq simpl 3ad2ant1 cvv fveq2i eqtri eleq2i biimpi anim2i 3ad2ant2
      3ad2ant3 fvexd ancoms mapprop syl3anc birani prelpwi 3adant1 lincval ccmn
      syl2an lmodcmn adantr simpr 3anim123i 3anrot cop a1i fveq1d simprl simprr
      sylib fvpr1g eqtrd oveq1d eqid lmodvscl eqeltrd 3adant3 fvpr2g 3adant2 id
      fveq2 oveq12d gsumpr syl112anc eqcomd fveq1i eqtrid eqidd oveq123d 3eqtrd
      ) GUBRZHIUCZUDZHARZJCRZUDZIARZKCRZUDZUEZFHIUFZGUGSTZGUAXRUAUNZFSZXTGUHSZT
      ZUIUJTZHFSZHYBTZIFSZIYBTZBTZJHETZKIETZBTXQXHFGUKSZULSZXRUMTRZXRGULSZUORZX
      SYDUPXJXMXHXPXHXIUQZURXQXKJYMRZUDZXNKYMRZUDZXIYMUSRZUDZYNXMXJYSXPXLYRXKXL
      YRCYMJCDULSYMNDYLULMUTVAZVBVCVDVEXPXJUUAXMXOYTXNXOYTCYMKUUDVBVCVDVFXJXMUU
      CXPXIXHUUCXHUUBXIXHYLULVGVDVHURJKYMFAUSHIQVIVJXMXPYPXJXMHYORZIYORZYPXPXKU
      UEXLAYOHLVBVKXNUUFXOAYOILVBVKHIYOVLVPVMUAFGXRUBVNVJXQGVORZXKXNXIUEZYFARZY
      HARZYDYIUPXJXMUUGXPXHUUGXIGVQVRURXQXIXKXNUEUUHXJXIXMXKXPXNXHXIVSZXKXLUQZX
      NXOUQZVTXIXKXNWAWGXJXMUUIXPXJXMUDZYFJHYBTZAUUNYEJHYBUUNYEHHJWBIKWBUFZSZJU
      UNHFUUPFUUPUPZUUNQWCWDUUNXKXLXIUUQJUPZXJXKXLWEZXJXKXLWFZXJXIXMUUKVRHIJKAC
      WHZVJWIWJUUNXHXLXKUUOARXJXHXMYQVRUVAUUTJYBDCAGHLMYBWKZNWLVJWMWNXJXPUUJXMX
      JXPUDZYHKIYBTZAUVDYGKIYBUVDYGIUUPSZKUVDIFUUPUURUVDQWCWDUVDXNXOXIUVFKUPZXJ
      XNXOWEZXJXNXOWFZXJXIXPUUKVRHIJKACWOZVJWIWJUVDXHXOXNUVEARXJXHXPYQVRUVIUVHK
      YBDCAGILMUVCNWLVJWMWPYCAYFYHBUAGHIAALPXTHUPZYAYEXTHYBXTHFWRUVKWQWSXTIUPZY
      AYGXTIYBXTIFWRUVLWQWSWTXAXQYFYJYHYKBXQYEJHHYBEXQEYBEYBUPXQOWCXBZXQYEUUQJH
      FUUPQXCXQXKXLXIUUSXMXJXKXPUULVEXMXJXLXPXKXLVSVEXJXMXIXPUUKURZUVBVJXDXQHXE
      XFXQYGKIIYBEUVMXQYGUVFKIFUUPQXCXQXNXOXIUVGXPXJXNXMUUMVFXPXJXOXMXNXOVSVFUV
      NUVJVJXDXQIXEXFWSXG $.
  $}

  ${
    lincval1.b $e |- B = ( Base ` M ) $.
    lincval1.s $e |- S = ( Scalar ` M ) $.
    lincval1.r $e |- R = ( Base ` S ) $.
    lincval1.f $e |- F = { <. V , ( 0g ` S ) >. } $.
    $( The linear combination over a singleton mapping to 0.  (Contributed by
       AV, 12-Apr-2019.) $)
    lincval1 $p |- ( ( M e. LMod /\ V e. B )
                     -> ( F ( linC ` M ) { V } ) = ( 0g ` M ) ) $=
      ( clmod wcel wa csn clinc cfv co c0g cvsca eqid lmod0cl lincvalsn mpd3an3
      wceq adantr lmod0vs eqtrd ) EKLZFALZMDFNEOPQZCRPZFESPZQZERPZUHUIUKBLZUJUM
      UDUHUOUICBEUKHIUKTZUAUEABCULDEFUKGHIULTZJUBUCULCUKAEFUNGHUQUPUNTUFUG $.

    $( Properties of a linear combination over a singleton mapping to 0.
       (Contributed by AV, 12-Apr-2019.)  (Revised by AV, 28-Jul-2019.) $)
    lcosn0 $p |- ( ( M e. LMod /\ V e. B ) -> ( F e. ( R ^m { V } )
                               /\ F finSupp ( 0g ` S )
                               /\ ( F ( linC ` M ) { V } ) = ( 0g ` M ) ) ) $=
      ( clmod wcel wa csn cmap co c0g cfv cvv a1i cfsupp wbr clinc wceq lmod0cl
      simpr eqid adantr cbs fvexi mapsnop syl3anc wf elmapi syl snfi fdmfifsupp
      cfn fvex lincval1 3jca ) EKLZFALZMZDBFNZOPLZDCQRZUAUBDVEEUCRPEQRUDVDVCVGB
      LZBSLZVFVBVCUFVBVHVCCBEVGHIVGUGUEUHVIVDBCUIIUJTBDASFVGJUKULZVDVEBDSVGVDVF
      VEBDUMVJDBVEUNUOVEURLVDFUPTVGSLVDCQUSTUQABCDEFGHIJUTVA $.
  $}

  ${
    $d B v x $.  $d F v $.  $d M v x $.  $d V v x $.  $d .0. x $.
    lincvalsc0.b $e |- B = ( Base ` M ) $.
    lincvalsc0.s $e |- S = ( Scalar ` M ) $.
    lincvalsc0.0 $e |- .0. = ( 0g ` S ) $.
    lincvalsc0.z $e |- Z = ( 0g ` M ) $.
    lincvalsc0.f $e |- F = ( x e. V |-> .0. ) $.
    $( The linear combination where all scalars are 0.  (Contributed by AV,
       12-Apr-2019.) $)
    lincvalsc0 $p |- ( ( M e. LMod /\ V e. ~P B )
                     -> ( F ( linC ` M ) V ) = Z ) $=
      ( vv wcel cfv co cbs wceq cvv clmod wa clinc cv cvsca cmpt cgsu csca cmap
      cpw simpl wf eqcomi fveq2i lmod0cl adantr fmptd fvexd elmapg sylan mpbird
      wb pweqi eleq2i bilani lincval syl3anc simpr c0g fvexi weq fvmptg sylancl
      eqidd oveq1d wi elelpwi expcom adantl imp lmod0vs syl2anc eqtrd mpteq2dva
      eqid oveq2d cmnd lmodgrp grpmndd gsumz 3eqtrd ) EUAOZFBUJZOZUBZDFEUCPQZEN
      FNUDZDPZWQEUEPZQZUFZUGQZENFHUFZUGQZHWOWLDEUHPZRPZFUIQOZFERPZUJZOZWPXBSWLW
      NUKZWOXGFXFDULZWOAFGXFDWOGXFOZAUDFOWLXMWNCXFEGJXECRCXEJUMUNKUOUPUPMUQWLXF
      TOWNXGXLVBWLXERURXFFDTWMUSUTVAWNXJWLWMXIFBXHIVCVDVENDEFUAVFVGWOXAXCEUGWON
      FWTHWOWQFOZUBZWTGWQWSQZHXOWRGWQWSXOXNGTOWRGSWOXNVHGCVIKVJAWQGGFTDANVKGVNM
      VLVMVOXOWLWQBOZXPHSWOWLXNXKUPWOXNXQWNXNXQVPWLXNWNXQWQFBVQVRVSVTWSCGBEWQHI
      JWSWEKLWAWBWCWDWFWLEWGOWNXDHSWLEEWHWIFNEWMHLWJUTWK $.

    $d F x $.  $d R x $.  $d .0. v $.
    lcoc0.r $e |- R = ( Base ` S ) $.
    $( Properties of a linear combination where all scalars are 0.
       (Contributed by AV, 12-Apr-2019.)  (Revised by AV, 28-Jul-2019.) $)
    lcoc0 $p |- ( ( M e. LMod /\ V e. ~P B )
                  -> ( F e. ( R ^m V ) /\ F finSupp .0.
                       /\ ( F ( linC ` M ) V ) = Z ) ) $=
      ( vv wcel cvv a1i cfn clmod cpw wa cmap cfsupp wbr clinc cfv wceq lmod0cl
      co wf cv ad2antrr fmptd cbs fvexi elmapg sylan mpbird csupp wne crab cmpt
      wb weq eqidd cbvmptv eqtri simpr c0g mptsuppd c0 wn wral ralrimivw rabeq0
      neirr sylibr 0fi eqeltrd wfun funmpt2 funisfsupp syl3anc lincvalsc0 3jca
      ) FUAQZGBUBZQZUCZECGUDUKZQZEHUEUFZEGFUGUHUKIUIWKWMGCEULZWKAGHCEWHHCQWJAUM
      GQDCFHKOLUJUNNUOWHCRQZWJWMWOVEWPWHCDUPOUQSCGERWIURUSUTZWKWNEHVAUKZTQZWKWR
      HHVBZPGVCZTWKPGHREWIRHEAGHVDPGHVDNAPGHHAPVFHVGVHVIWHWJVJHRQZWKHDVKLUQZSZX
      BWKPUMGQUCXCSVLWKXAVMTWKWTVNZPGVOXAVMUIWKXEPGXEWKHVRSVPWTPGVQVSVMTQWKVTSW
      AWAWKEWBZWMXBWNWSVEXFWKAGHENWCSWQXDEWLRHWDWEUTABDEFGHIJKLMNWFWG $.
  $}

  ${
    $d B v x $.  $d F v $.  $d M v x $.  $d V v x $.  $d Z x $.  $d .0. x $.
    $d .1. x $.
    linc0scn0.b $e |- B = ( Base ` M ) $.
    linc0scn0.s $e |- S = ( Scalar ` M ) $.
    linc0scn0.0 $e |- .0. = ( 0g ` S ) $.
    linc0scn0.1 $e |- .1. = ( 1r ` S ) $.
    linc0scn0.z $e |- Z = ( 0g ` M ) $.
    linc0scn0.f $e |- F = ( x e. V |-> if ( x = Z , .1. , .0. ) ) $.
    $( If a set contains the zero element of a module, there is a linear
       combination being 0 where not all scalars are 0.  (Contributed by AV,
       13-Apr-2019.) $)
    linc0scn0 $p |- ( ( M e. LMod /\ V e. ~P B )
                      -> ( F ( linC ` M ) V ) = Z ) $=
      ( vv wcel cfv co wceq clmod cpw wa clinc cv cvsca cmpt cgsu csca cbs cmap
      simpl wf cif crg lmodring eqcomi fveq2i ringidcl ring0cl jca syl ad2antrr
      ifcl fmptd cvv fvex a1i elmapg sylan mpbird eleq2i bilani lincval syl3anc
      pweqi simpr cur fvexi c0g ifex weq eqeq1 ifbid fvmptg sylancl oveq1d ovif
      wb oveq2 adantl eqid lmod1cl ancli adantr lmodvs0 eqtrd wn elelpwi expcom
      wi imp lmod0vs syl2anc ifeqda 3eqtrd mpteq2dva cmnd lmodgrp grpmndd gsumz
      oveq2d ) FUAQZGBUBZQZUCZEGFUDRSZFPGPUEZERZXRFUFRZSZUGZUHSZFPGIUGZUHSZIXPX
      MEFUIRZUJRZGUKSQZGFUJRZUBZQZXQYCTXMXOULZXPYHGYGEUMZXPAGAUEZITZDHUNZYGEXPY
      NGQZUCDYGQZHYGQZUCZYPYGQXMYTXOYQXMCUOQZYTCFKUPUUAYRYSYGCDYFCUJCYFKUQURZMU
      SYGCHUUBLUTVAVBVCYODHYGVDVBOVEXMYGVFQZXOYHYMWIUUCXMYFUJVGVHYGGEVFXNVIVJVK
      XOYKXMXNYJGBYIJVPVLVMPEFGUAVNVOXPYBYDFUHXPPGYAIXPXRGQZUCZYAXRITZDHUNZXRXT
      SZUUFDXRXTSZHXRXTSZUNZIUUEXSUUGXRXTUUEUUDUUGVFQXSUUGTXPUUDVQUUFDHDCVRMVSH
      CVTLVSWAAXRYPUUGGVFEAPWBYOUUFDHYNXRIWCWDOWEWFWGUUHUUKTUUEUUFDHXRXTWHVHUUE
      UUFUUIUUJIUUEUUFUCZUUIDIXTSZIUUFUUIUUMTUUEXRIDXTWJWKUULXMDCUJRZQZUCZUUMIT
      XPUUPUUDUUFXMUUPXOXMUUODCUUNFKUUNWLZMWMWNWOVCXTCUUNFDIKXTWLZUUQNWPVBWQUUE
      UUJITZUUFWRUUEXMXRBQZUUSXPXMUUDYLWOXPUUDUUTXOUUDUUTXAXMUUDXOUUTXRGBWSWTWK
      XBXTCHBFXRIJKUURLNXCXDWOXEXFXGXLXMFXHQXOYEITXMFFXIXJGPFXNINXKVJXF $.
  $}

  ${
    $d B x $.  $d F x $.  $d G x $.  $d M x $.  $d S x $.  $d V x $.  $d X x $.
    $d .0. x $.  $d .x. x $.
    lincdifsn.b $e |- B = ( Base ` M ) $.
    lincdifsn.r $e |- R = ( Scalar ` M ) $.
    lincdifsn.s $e |- S = ( Base ` R ) $.
    lincdifsn.t $e |- .x. = ( .s ` M ) $.
    lincdifsn.p $e |- .+ = ( +g ` M ) $.
    lincdifsn.0 $e |- .0. = ( 0g ` R ) $.
    $( A vector is a linear combination of a set containing this vector.
       (Contributed by AV, 21-Apr-2019.)  (Revised by AV, 28-Jul-2019.) $)
    lincdifsn $p |- ( ( ( M e. LMod /\ V e. ~P B /\ X e. V )
                        /\ ( F e. ( S ^m V ) /\ F finSupp .0. )
                        /\ G = ( F |` ( V \ { X } ) ) )
          -> ( F ( linC ` M ) V )
             = ( ( G ( linC ` M ) ( V \ { X } ) ) .+ ( ( F ` X ) .x. X ) ) ) $=
      ( wcel co cfv vx clmod cpw w3a cmap cfsupp wbr wa cdif cres wceq clinc cv
      csn cvsca cmpt cgsu cbs simp11 fveq2i eqtri oveq1i eleq2i biimpi 3ad2ant2
      csca adantr pweqi 3ad2ant1 lincval syl3anc ccmn lmodcmn simp12 c0g anim2i
      3adant3 simp2l breq2i adantl scmfsupp simpl1 wi wf elmapi ffvelcdm ex a1d
      syl impcom elelpwi expcom eqid lmodvscl 3adantl3 3ad2ant3 syl5com 3adant1
      imp simp13 ancoms eqcomi a1i fveq2 oveq123d gsumdifsnd fveq1 fvres oveq1d
      sylan9eq mpteq2dva eqcomd oveq2d eqtrd feq23i sylib difssd fssresd mpbird
      id wb feq1 cvv fvex difexg elmapg sylancr wss elpwi sseq2i ssdifssd elpwg
      3eqtrd ) HUBRZIAUCZRZJIRZUDZFDIUESZRZFKUFUGZUHZGFIJUNZUIZUJZUKZUDZFIHULTZ
      SZHUAIUAUMZFTZUUJHUOTZSZUPZUQSZHUAUUDUUJGTZUUJUULSZUPZUQSZJFTZJESZBSZGUUD
      UUHSZUVABSUUGYNFHVFTZURTZIUESZRZIHURTZUCZRZUUIUUOUKYNYPYQUUBUUFUSZUUBYRUV
      GUUFYTUVGUUAYTUVGYSUVFFDUVEIUEDCURTUVENCUVDURMUTVAZVBVCVDVGVEYRUUBUVJUUFY
      PYNUVJYQYPUVJYOUVIIAUVHLVHVCVDZVEVIUAFHIUBVJVKUUGUUOHUAUUDUUMUPZUQSZUVABS
      UVBUUGIABUAHJYOUUMUVALPYRUUBHVLRZUUFYNYPUVPYQHVMVIVIYNYPYQUUBUUFVNUUGYNUV
      JUHZYTFCVOTZUFUGZUUNHVOTUFUGYRUUBUVQUUFYNYPUVQYQYPUVJYNUVMVPVQVIYRYTUUAUU
      FVRUUBYRUVSUUFUUAUVSYTUUAUVSKUVRFUFQVSVDVTVEUAFDCHIMNWAVKYRUUBUUJIRZUUMAR
      ZUUFYRUUBUHZUVTUHYNUUKDRZUUJARZUWAUWBYNUVTYNYPYQUUBWBZVGUWBUVTUWCUUBYRUVT
      UWCWCZYTYRUWFWCZUUAYTIDFWDZUWGFDIWEZUWHUWFYRUWHUVTUWCIDUUJFWFWGWHWIVGWJWS
      UWBUVTUWDYRUVTUWDWCZUUBYPYNUWJYQUVTYPUWDUUJIAWKWLVEVGWSUUKUULCDAHUUJLMUUL
      WMNWNVKWOYNYPYQUUBUUFWTYRUUBUVAARZUUFUWBYNUUTDRZJARZUWKUWEUUBYRUWLYTYRUWL
      WCUUAYTUWHYRUWLUWIYQYNUWHUWLWCYPUWHYQUWLIDJFWFWLWPWQVGWJYRUWMUUBYPYQUWMYN
      YQYPUWMJIAWKXAWRVGUUTECDAHJLMONWNVKVQUUJJUKZUUMUVAUKUUGUWNUUKUUTUUJJUULEU
      ULEUKUWNEUULOXBXCUUJJFXDUWNXTXEVTXFUUGUVOUUSUVABUUGUVNUURHUQUUGUURUVNUUGU
      AUUDUUQUUMUUGUUJUUDRZUHUUPUUKUUJUULUUGUWOUUPUUJUUETZUUKUUFYRUUPUWPUKUUBUU
      JGUUEXGWPUUJUUDFXHXJXIXKXLXMXIXNUUGUUSUVCUVABUUGUVCUUSUUGYNGUVEUUDUESRZUU
      DUVIRZUVCUUSUKUVKUUGUWQUUDUVEGWDZUUGUWSUUDUVEUUEWDZUUGIUVEUUDFUUBYRIUVEFW
      DZUUFYTUXAUUAYTUWHUXAUWIIDIUVEFIWMUVLXOXPVGVEUUGIUUCXQXRUUFYRUWSUWTYAUUBU
      UDUVEGUUEYBWPXSUUGUVEYCRUUDYCRZUWQUWSYAUVDURYDYRUUBUXBUUFYPYNUXBYQIUUCYOY
      EZVEVIUVEUUDGYCYCYFYGXSYRUUBUWRUUFYNYPUWRYQYNYPUHZUWRUUDUVHYHZYPUXEYNYPIA
      YHZUXEIAYIUXFIUVHUUCUXFIUVHYHAUVHILYJVDYKWIVTUXDUXBUWRUXEYAYPUXBYNUXCVTUU
      DUVHYCYLWIXSVQVIUAGHUUDUBVJVKXLXIYM $.
  $}

  ${
    $d B v x y $.  $d F v y $.  $d M v x y $.  $d V v x y $.  $d X v x y $.
    $d .0. x $.  $d .1. x $.
    linc1.b $e |- B = ( Base ` M ) $.
    linc1.s $e |- S = ( Scalar ` M ) $.
    linc1.0 $e |- .0. = ( 0g ` S ) $.
    linc1.1 $e |- .1. = ( 1r ` S ) $.
    linc1.f $e |- F = ( x e. V |-> if ( x = X , .1. , .0. ) ) $.
    $( A vector is a linear combination of a set containing this vector.
       (Contributed by AV, 18-Apr-2019.)  (Proof shortened by AV,
       28-Jul-2019.) $)
    linc1 $p |- ( ( M e. LMod /\ V e. ~P B /\ X e. V )
                  -> ( F ( linC ` M ) V ) = X ) $=
      ( vv wcel cfv co wceq cvv vy clmod cpw w3a clinc cvsca cmpt cgsu csca cbs
      cv cmap simp1 wf cif crg lmodring eqcomi fveq2i ringidcl ring0cl 3ad2ant1
      wa jca adantr ifcl fmptd wb fvex simp2 elmapg sylancr mpbird pweqi eleq2i
      syl biimpi 3ad2ant2 lincval syl3anc eqid cmnd lmodgrp grpmndd simp3 eqeq1
      c0g weq ifbid simpr lmod1cl lmod0cl fvmptd3 eqeltrd wi elelpwi expcom imp
      ifcld lmodvscl csupp wne crab csn fveq2 id oveq12d cbvmptv fvexd mptsuppd
      ovexd wral wss 2a1 wn simprr cur fvexi ifex fvmptg sylancl iffalse oveq1d
      eqtrd adantl lmod0vs syl2anc eqneqall ax-mp biimtrdi ex pm2.61i ralrimiva
      neeq1d rabsssn sylibr eqsstrd gsumpt ovex 3eqtrd iftrue 3adant1 lmodvs1
      ancoms ) FUBPZGBUCZPZHGPZUDZEGFUEQRZFUAGUAUKZEQZUUKFUFQZRZUGZUHRZHUUOQZHU
      UIUUEEFUIQZUJQZGULRPZGFUJQZUCZPZUUJUUPSUUEUUGUUHUMZUUIUUTGUUSEUNZUUIAGAUK
      ZHSZDIUOZUUSEUUIUVFGPZVCDUUSPZIUUSPZVCZUVHUUSPUUIUVLUVIUUEUUGUVLUUHUUECUP
      PZUVLCFKUQUVMUVJUVKUUSCDUURCUJCUURKURUSZMUTUUSCIUVNLVAVDVPVBVEUVGDIUUSVFV
      PNVGUUIUUSTPUUGUUTUVEVHUURUJVIUUEUUGUUHVJZUUSGETUUFVKVLVMUUGUUEUVCUUHUUGU
      VCUUFUVBGBUVAJVNVOVQVRUAEFGUBVSVTUUIGBUUOFUUFHFWGQZJUVPWAZUUEUUGFWBPUUHUU
      EFFWCWDVBUVOUUEUUGUUHWEZUUIUAGUUNBUUOUUIUUKGPZVCZUUEUULCUJQZPUUKBPZUUNBPU
      UIUUEUVSUVDVEUVTUULUUKHSZDIUOZUWAUVTAUUKUVHUWDGEUWANAUAWHUVGUWCDIUVFUUKHW
      FWIUUIUVSWJUVTUWCDIUWAUUIDUWAPZUVSUUEUUGUWEUUHDCUWAFKUWAWAZMWKVBVEUUIIUWA
      PZUVSUUEUUGUWGUUHCUWAFIKUWFLWLVBVEWSZWMUWHWNUUIUVSUWBUUGUUEUVSUWBWOUUHUVS
      UUGUWBUUKGBWPWQVRWRUULUUMCUWABFUUKJKUUMWAZUWFWTVTUUOWAZVGUUIUUOUVPXAROUKZ
      EQZUWKUUMRZUVPXBZOGXCZHXDZUUIOGUWMTUUOUUFTUVPUAOGUUNUWMUAOWHZUULUWLUUKUWK
      UUMUUKUWKEXEUWQXFXGXHUVOUUIFWGXIUUIUWKGPZVCZUWLUWKUUMXKXJUUIUWNUWKHSZWOZO
      GXLUWOUWPXMUUIUXAOGUWTUWSUXAWOUWTUWSUWNXNUWTXOZUWSUXAUXBUWSVCZUWNUVPUVPXB
      ZUWTUXCUWMUVPUVPUXCUWMIUWKUUMRZUVPUXCUWLIUWKUUMUXCUWLUWTDIUOZIUXCUWRUXFTP
      UWLUXFSUXBUUIUWRXPUWTDIDCXQMXRZICWGLXRXSAUWKUVHUXFGTEAOWHUVGUWTDIUVFUWKHW
      FWINXTYAUXBUXFISUWSUWTDIYBVEYDYCUXCUUEUWKBPZUXEUVPSUWSUUEUXBUUIUUEUWRUVDV
      EYEUWSUXHUXBUUIUWRUXHUUGUUEUWRUXHWOUUHUWRUUGUXHUWKGBWPWQVRWRYEUUMCIBFUWKU
      VPJKUWILUVQYFYGYDYNUVPUVPSUXDUWTWOUVQUWTUVPUVPYHYIYJYKYLYMUWNOGHYOYPYQYRU
      UIUUQHEQZHUUMRZDHUUMRZHUUIUUHUXJTPUUQUXJSUVRUXIHUUMYSUAHUUNUXJGTUUOUWCUUL
      UXIUUKHUUMUUKHEXEUWCXFXGUWJXTYAUUIUXIDHUUMUUIUUHDTPUXIDSUVRUXGAHUVHDGTEUV
      GDIUUANXTYAYCUUIUUEHBPZUXKHSUVDUUGUUHUXLUUEUUHUUGUXLHGBWPUUDUUBUUMDCBFHJK
      UWIMUUCYGYTYT $.
  $}

  ${
    $d F v $.  $d M v $.  $d S v $.  $d V v $.
    $( A linear combination of a subset of a linear subspace is also contained
       in the linear subspace.  (Contributed by AV, 20-Apr-2019.)  (Revised by
       AV, 28-Jul-2019.) $)
    lincellss $p |- ( ( M e. LMod /\ S e. ( LSubSp ` M ) /\ V C_ S )
                      -> ( ( F e. ( ( Base ` ( Scalar ` M ) ) ^m V )
                             /\ F finSupp ( 0g ` ( Scalar ` M ) ) )
                           -> ( F ( linC ` M ) V ) e. S ) ) $=
      ( vv clmod wcel clss cfv wss w3a csca cbs cmap co wa cvv wi eqid imp cmpt
      c0g cfsupp wbr clinc cvsca cgsu cpw wceq simpl1 simprl ssexg ancoms lssss
      cv sstr elpwg syl5ibrcom expcom syl mpd 3adant1 lincval syl3anc gsumlsscl
      adantr eqeltrd ex ) CFGZACHIZGZDAJZKZBCLIZMIZDNOGZBVNUBIUCUDZPZBDCUEIOZAG
      VMVRPZVSCEDEUOZBIWACUFIOUAUGOZAVTVIVPDCMIZUHGZVSWBUIVIVKVLVRUJVMVPVQUKVMW
      DVRVKVLWDVIVKVLPDQGZWDVLVKWEDAVJULUMVKVLWEWDRZVKAWCJZVLWFRVJAWCCWCSVJSZUN
      VLWGWFVLWGPWDWEDWCJDAWCUPDWCQUQURUSUTTVAVBVFEBCDFVCVDVMVRWBAGEVOVNVJBCDAW
      HVNSVOSVETVGVH $.
  $}

  ${
    $d M v w $.
    $( The set of empty linear combinations over a monoid is the singleton with
       the identity element of the monoid.  (Contributed by AV,
       12-Apr-2019.) $)
    lco0 $p |- ( M e. Mnd -> ( M LinCo (/) ) = { ( 0g ` M ) } ) $=
      ( vw vv cmnd wcel c0 co cv cfv c0g cfsupp wbr wceq cbs wrex crab csn eqid
      wa cvv clinco csca clinc cmap cpw 0elpw lcoop mpan2 fvex map0e mp1i df1o2
      c1o eqtrdi rexeqdv cfn lincval0 adantr eqeq2d anbi2d 0ex breq1 0fsupp 0fi
      wb ax-mp 2th bitrdi oveq1 anbi12d rexsng biantrurd 3bitr4d bitrd rabbidva
      a1i mndidcl rabsn syl 3eqtrd ) ADEZAFUAGZBHZAUBIZJIZKLZCHZWCFAUCIZGZMZSZB
      WDNIZFUDGZOZCANIZPZWGAJIZMZCWOPZWQQZWAFWOUEEWBWPMWOUFWOWLWDAFDBCWORZWDRWL
      RUGUHWAWNWRCWOWAWGWOEZSZWNWKBFQZOZWRXCWKBWMXDXCWMUMXDWLTEWMUMMXCWDNUIWLTU
      JUKULUNUOXCFUPEZWGFFWHGZMZSZXFWRSXEWRXCXHWRXFXCXGWQWGWAXGWQMXBADUQURUSUTF
      TEXEXIVEXCVAWKXIBFTWCFMZWFXFWJXHXJWFFWEKLZXFWCFWEKVBXKXFWETEXKWDJUITWEVCV
      FVDVGVHXJWIXGWGWCFFWHVIUSVJVKUKXCXFWRXFXCVDVPVLVMVNVOWAWQWOEWSWTMWOAWQXAW
      QRVQCWOWQVRVSVT $.
  $}

  ${
    $d M s v w $.  $d V s v w $.
    $( The zero vector is always a linear combination.  (Contributed by AV,
       12-Apr-2019.)  (Proof shortened by AV, 30-Jul-2019.) $)
    lcoel0 $p |- ( ( M e. LMod /\ V e. ~P ( Base ` M ) )
                   -> ( 0g ` M ) e. ( M LinCo V ) ) $=
      ( vs vv vw c0 wceq clmod wcel cbs cfv wa c0g clinco co adantr cfsupp eqid
      cv adantl cpw fvex snid oveq2 cgrp cmnd lmodgrp grpmnd lco0 3syl sylan9eq
      csn eleqtrrid wn csca wbr clinc cmap wrex lmod0vcl cmpt w3a eqidd cbvmptv
      lcoc0 wi simpl wb breq1 oveq1 eqeq2d eqcom bitrdi anbi12d ex com23 3impib
      rspcedv mpcom lcoval mpbir2and pm2.61ian ) BFGZAHIZBAJKZUAIZLZAMKZABNOZIZ
      WCWGLWHWHULZWIWHAMUBUCWCWGWIAFNOZWKBFANUDWDWLWKGZWFWDAUEIAUFIWMAUGAUHAUIU
      JPUKUMWCUNZWGLZWJWHWEIZCSZAUOKZMKZQUPZWHWQBAUQKZOZGZLZCWRJKZBUROZUSZWGWPW
      NWDWPWFWEAWHWERZWHRZUTPTDBWSVAZXFIZXJWSQUPZXJBXAOZWHGZVBZWOXGWGXOWNEWEXEW
      RXJABWSWHXHWRRZWSRXIDEBWSWSDSESGWSVCVDXERZVETXKXLXNWOXGVFXKWOXLXNLZXGXKWO
      XRXGVFXKWOLZXDXRCXJXFXKWOVGWQXJGZXDXRVHXSXTWTXLXCXNWQXJWSQVIXTXCWHXMGXNXT
      XBXMWHWQXJBXAVJVKWHXMVLVMVNTVRVOVPVQVSWGWJWPXGLVHWNWEWHXEWRABHCXHXPXQVTTW
      AWB $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d M x y $.  $d R x y $.  $d S x $.  $d V x y $.
    $d .+ x $.  $d .+b x y $.
    lincsum.p $e |- .+ = ( +g ` M ) $.
    lincsum.x $e |- X = ( A ( linC ` M ) V ) $.
    lincsum.y $e |- Y = ( B ( linC ` M ) V ) $.
    lincsum.s $e |- S = ( Scalar ` M ) $.
    lincsum.r $e |- R = ( Base ` S ) $.
    lincsum.b $e |- .+b = ( +g ` S ) $.
    $( The sum of two linear combinations is a linear combination, see also the
       proof in [Lang] p. 129.  (Contributed by AV, 4-Apr-2019.)  (Revised by
       AV, 28-Jul-2019.) $)
    lincsum $p |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) )
                      /\ ( A e. ( R ^m V ) /\ B e. ( R ^m V ) )
                      /\ ( A finSupp ( 0g ` S ) /\ B finSupp ( 0g ` S ) ) )
                    -> ( X .+ Y ) = ( ( A oF .+b B ) ( linC ` M ) V ) ) $=
      ( vx wcel cfv co vy clmod cbs cpw wa cmap c0g cfsupp wbr w3a cv cmpt cgsu
      cvsca cof clinc eqid ccmn lmodcmn adantr 3ad2ant1 simpr simpl wi ffvelcdm
      wf elmapi ex syl 3ad2ant2 elelpwi expcom adantl lmodvscl syl3anc eqidd id
      imp scmfsupp syl3an gsummptfsadd csca wceq wfn ad2antrl ad2antll offvalfv
      elmapfn 3adant3 cmnd lmodfgrp grpmndd ad3antrrr fveq2i eqtri eqcomi mndcl
      eleqtrdi fmpttd cvv wb fvex elmapg sylancr mpbird eqeltrd lincval anim12i
      cplusg anim1i fnfvof syl2anc a1i oveqd eqtrd lmodvsdir syl13anc mpteq2dva
      oveq1d oveq2d oveq12i oveq1i eleq2i biimpi oveq12d eqtrid 3eqtr4rd ) GUBR
      ZHGUCSZUDZRZUEZAEHUFTZRZBYMRZUEZAFUGSZUHUIZBYQUHUIZUEZUJZGQHQUKZASZUUBGUN
      SZTZUUBBSZUUBUUDTZCTZULZUMTZGQHUUEULZUMTZGQHUUGULZUMTZCTZABDUOTZHGUPSZTZI
      JCTZUUAQHYIUUEUUGCUUKGUUMYJGUGSZYIUQZUUTUQKYLYPGURRZYTYHUVBYKGUSUTVAYLYPY
      KYTYHYKVBZVAZUUAUUBHRZUEZYHUUCERZUUBYIRZUUEYIRUUAYHUVEYLYPYHYTYHYKVCZVAZU
      TZUUAUVEUVGYPYLUVEUVGVDZYTYNUVLYOYNHEAVFZUVLAEHVGZUVMUVEUVGHEUUBAVEVHVIZU
      TVJVRUUAUVEUVHYLYPUVEUVHVDZYTYKUVPYHUVEYKUVHUUBHYIVKVLVMZVAVRZUUCUUDFEYIG
      UUBUVANUUDUQZOVNVOUVFYHUUFERZUVHUUGYIRUVKUUAUVEUVTYPYLUVEUVTVDZYTYOUWAYNY
      OHEBVFZUWABEHVGZUWBUVEUVTHEUUBBVEVHVIZVMVJVRUVRUUFUUDFEYIGUUBUVANUVSOVNVO
      UUAUUKVPUUAUUMVPYLYLYPYNYTYRUUKUUTUHUIYLVQZYNYOVCYRYSVCQAEFGHNOVSVTYLYLYP
      YOYTYSUUMUUTUHUIUWEYNYOVBYRYSVBQBEFGHNOVSVTWAUUAUURGQHUUBUUPSZUUBUUDTZULZ
      UMTZUUJUUAYHUUPGWBSZUCSZHUFTZRYKUURUWIWCUVJUUAUUPUAHUAUKZASZUWMBSZDTZULZU
      WLYLYPUUPUWQWCYTYLYPUEZUAHDABYJYLYKYPUVCUTZYNAHWDZYLYOAEHWHZWEYOBHWDZYLYN
      BEHWHZWFWGWIYLYPUWQUWLRZYTUWRUXDHUWKUWQVFZUWRUAHUWPUWKUWRUWMHRZUEZFWJRZUW
      NUWKRUWOUWKRZUWPUWKRYHUXHYKYPUXFYHFFGNWKWLWMUXGUWNEUWKUWRUXFUWNERZYNUXFUX
      JVDZYLYOYNUVMUXKUVNUVMUXFUXJHEUWMAVEVHVIWEVREFUCSUWKOFUWJUCNWNWOZWRUWRUXF
      UXIYOUXFUXIVDZYLYNYOUWBUXMUWCUWBUXFUXIUWBUXFUEUWOEUWKHEUWMBVEUXLWRVHVIWFV
      RUWKDFUWNUWOUWJFUCFUWJNWPWNPWQVOWSUWRUWKWTRYKUXDUXEXAUWJUCXBUWSUWKHUWQWTY
      JXCXDXEWIXFUVDQUUPGHUBXGVOYLYPUWIUUJWCYTUWRUWHUUIGUMUWRQHUWGUUHUWRUVEUEZU
      WGUUCUUFFXISZTZUUBUUDTZUUHUXNUWFUXPUUBUUDUXNUWFUUCUUFDTZUXPUXNUWTUXBUEZYK
      UVEUEUWFUXRWCUWRUXSUVEYPUXSYLYNUWTYOUXBUXAUXCXHVMUTUWRYKUVEUWSXJHDABYJUUB
      XKXLUXNDUXOUUCUUFDUXOWCUXNPXMXNXOXSUXNYHUVGUVTUVHUXQUUHWCUWRYHUVEYLYHYPUV
      IUTZUTUWRUVEUVGYNUVLYLYOUVOWEVRUWRUVEUVTYOUWAYLYNUWDWFVRUWRUVEUVHYLUVPYPU
      VQUTVRCUXOUUCUUFUUDUWJEYIGUUBUVAKUWJUQUVSUXLFUWJXINWNXPXQXOXRXTWIXOUUAUUS
      AHUUQTZBHUUQTZCTZUUOIUYAJUYBCLMYAYLYPUYCUUOWCYTUWRUYAUULUYBUUNCUWRYHAUWLR
      ZYKUYAUULWCUXTYNUYDYLYOYNUYDYMUWLAEUWKHUFUXLYBZYCYDWEUWSQAGHUBXGVOUWRYHBU
      WLRZYKUYBUUNWCUXTYOUYFYLYNYOUYFYMUWLBUYEYCYDWFUWSQBGHUBXGVOYEWIYFYG $.
  $}

  ${
    $d A v x $.  $d F v $.  $d M v x $.  $d R v x $.  $d S v x $.  $d V v x $.
    $d .xb v $.  $d .x. v x $.
    lincscm.s $e |- .xb = ( .s ` M ) $.
    lincscm.t $e |- .x. = ( .r ` ( Scalar ` M ) ) $.
    lincscm.x $e |- X = ( A ( linC ` M ) V ) $.
    lincscm.r $e |- R = ( Base ` ( Scalar ` M ) ) $.
    lincscm.f $e |- F = ( x e. V |-> ( S .x. ( A ` x ) ) ) $.
    $( A linear combinations multiplied with a scalar is a linear combination,
       see also the proof in [Lang] p. 129.  (Contributed by AV, 9-Apr-2019.)
       (Revised by AV, 28-Jul-2019.) $)
    lincscm $p |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) )
                      /\ ( A e. ( R ^m V ) /\ S e. R )
                      /\ A finSupp ( 0g ` ( Scalar ` M ) ) )
                    -> ( S .xb X ) = ( F ( linC ` M ) V ) ) $=
      ( vv wcel cfv co adantr clmod cbs cpw wa cmap c0g cfsupp wbr w3a cv cvsca
      csca cmpt cgsu clinc cplusg eqid simp1l simpr 3ad2ant1 3ad2ant2 wi elmapi
      ffvelcdm syl imp elelpwi expcom adantl lmodvscl syl3anc scmfsupp 3adant2r
      wf ex gsumvsmul wceq crg lmodring eleq2i biimpi eleqtrdi ringcl fmptd cvv
      wb fvex elmapg sylancr mpbird lincval ovex fveq2 oveq2d sylancl lmodvsass
      fvmptg oveq1d syl13anc eqcomi a1i oveqd eqtrd mpteq2dva oveq1i 3eqtr4rd )
      HUAQZIHUBRZUCZQZUDZBCIUESZQZDCQZUDZBHULRZUFRUGUHZUIZHPIDPUJZBRZXSHUKRZSZE
      SZUMZUNSZDHPIYBUMZUNSZESGIHUORZSZDJESXRIXHHUPRZHXPEPCXIDYBHUFRZXHUQZXPUQZ
      NYKUQYJUQKXGXJXOXQURZXKXOXJXQXGXJUSUTZXOXKXNXQXMXNUSVAZXRXSIQZUDZXGXTCQZX
      SXHQZYBXHQXRXGYQYNTZXRYQYSXOXKYQYSVBZXQXMUUBXNXMICBVNZUUBBCIVCZUUCYQYSICX
      SBVDVOVETVAVFZXRYQYTXKXOYQYTVBZXQXJUUFXGYQXJYTXSIXHVGVHVIUTVFZXTYAXPCXHHX
      SYLYMYAUQZNVJVKXKXMXQYFYKUGUHXNPBCXPHIYMNVLVMVPXRYIHPIXSGRZXSYASZUMZUNSZY
      EXRXGGXPUBRZIUESZQZXJYIUULVQYNXRUUOIUUMGVNZXRAIDAUJZBRZFSZUUMGXRUUQIQZUDX
      PVRQZDUUMQZUURUUMQZUUSUUMQXRUVAUUTXKXOUVAXQXGUVAXJXPHYMVSTUTTXRUVBUUTXOXK
      UVBXQXNUVBXMXNUVBCUUMDNVTWAVIVATXRUUTUVCXOXKUUTUVCVBZXQXMUVDXNXMUUCUVDUUD
      UUCUUTUVCUUCUUTUDUURCUUMICUUQBVDNWBVOVETVAVFUUMXPFDUURUUMUQLWCVKOWDXRUUMW
      EQXJUUOUUPWFXPUBWGYOUUMIGWEXIWHWIWJYOPGHIUAWKVKXRUUKYDHUNXRPIUUJYCYRUUJDX
      TFSZXSYASZYCYRUUIUVEXSYAYRYQUVEWEQUUIUVEVQXRYQUSDXTFWLAXSUUSUVEIWEGUUQXSV
      QUURXTDFUUQXSBWMWNOWQWOWRYRUVFDYBYASZYCYRXGXNYSYTUVFUVGVQUUAXRXNYQYPTUUEU
      UGDXTYAFXPCXHHXSYLYMUUHNLWPWSYRYAEDYBYAEVQYREYAKWTXAXBXCXCXDWNXCXRJYGDEXR
      JBIYHSZYGJUVHVQXRMXAXRXGBUUNQZXJUVHYGVQYNXOXKUVIXQXMUVIXNXMUVIXLUUNBCUUMI
      UENXEVTWATVAYOPBHIUAWKVKXCWNXF $.
  $}

  ${
    $d C s x y $.  $d D s x y $.  $d M s x y $.  $d V s x y $.  $d .+ s x y $.
    lincsumcl.b $e |- .+ = ( +g ` M ) $.
    $( The sum of two linear combinations is a linear combination, see also the
       proof in [Lang] p. 129.  (Contributed by AV, 4-Apr-2019.)  (Proof
       shortened by AV, 28-Jul-2019.) $)
    lincsumcl $p |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) )
                      /\ ( C e. ( M LinCo V ) /\ D e. ( M LinCo V ) ) )
                   -> ( C .+ D ) e. ( M LinCo V ) ) $=
      ( vy vx vs clmod wcel cfv wa co cfsupp wceq eqid adantl wi adantr cbs cpw
      clinco csca c0g wbr clinc cmap wrex lcoval anbi12d simpll simprl lmodvacl
      syl3anc cplusg cof cmnd lmodfgrp grpmndd simpr anim12i ofaddmndmap anim1i
      simpl mndpfsupp oveq12 expcom com12 imp lincsum eqtrd breq1 eqeq2d rspcev
      cv oveq1 syl12anc exp41 rexlimiva expd impcom com13 wb mpbir2and sylbid
      ex ) DJKZEDUALZUBZKZMZADEUCNZKZBWMKZMZABCNZWMKZWLWPAWIKZGVPZDUDLZUELZOUFZ
      AWTEDUGLZNZPZMZGXAUALZEUHNZUIZMZBWIKZHVPZXBOUFZBXMEXDNZPZMZHXIUIZMZMZWRWL
      WNXKWOXSWIAXHXADEJGWIQZXAQZXHQZUJWIBXHXADEJHYAYBYCUJUKWLXTWRWLXTMZWRWQWIK
      ZIVPZXBOUFZWQYFEXDNZPZMZIXIUIZYDWHWSXLYEWHWKXTULXTWSWLWSXJXSULRXTXLWLXKXL
      XRUMRCWIDABYAFUNUOXTWLYKXSXKWLYKSZXRXLXKYLSZXQXLYMSHXIXKXLXMXIKZXQMZYLXJW
      SXLYOYLSZSXJWSXLYPXGWSXLMZYPSGXIWTXIKZXGMZYQYOWLYKYSYQMZYOMZWLMZWTXMXAUPL
      ZUQNZXIKZUUDXBOUFZWQUUDEXDNZPZYKUUBXAURKZWKYRYNMZUUEWLUUIUUAWHUUIWKWHXAXA
      DYBUSUTZTRWLWKUUAWHWKVARUUAUUJWLYTYRYOYNYRXGYQULYNXQVEVBTZWTXMUUCXHXAEWJY
      CUUCQZVCUOUUBUUIWKMZUUJXCXNMZUUFWLUUNUUAWHUUIWKUUKVDRUULUUAUUOWLYTXCYOXNY
      SXCYQYRXCXFUMTYNXNXPUMVBTZWTXMXHXAEWJYCVFUOUUBWQXEXOCNZUUGUUAWQUUQPZWLYTY
      OUURYSYOUURSZYQXGUUSYRXFUUSXCYOXFUURXQXFUURSZYNXPUUTXNXFXPUURAXEBXOCVGVHR
      RVIRRTVJTUUBWLUUJUUOUUQUUGPUUAWLVAUULUUPWTXMCUUCXHXADEXEXOFXEQXOQYBYCUUMV
      KUOVLYJUUFUUHMIUUDXIYFUUDPZYGUUFYIUUHYFUUDXBOVMUVAYHUUGWQYFUUDEXDVQVNUKVO
      VRVSVTWAWBWCVTWBWBWBWLWRYEYKMWDXTWIWQXHXADEJIYAYBYCUJTWEWGWFVJ $.
  $}

  ${
    $d C s v x $.  $d D s v x $.  $d M s v x $.  $d R s v x $.  $d V s v x $.
    $d .x. s x $.
    lincscmcl.s $e |- .x. = ( .s ` M ) $.
    lincscmcl.r $e |- R = ( Base ` ( Scalar ` M ) ) $.
    $( The multiplication of a linear combination with a scalar is a linear
       combination, see also the proof in [Lang] p. 129.  (Contributed by AV,
       11-Apr-2019.)  (Proof shortened by AV, 28-Jul-2019.) $)
    lincscmcl $p |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) )
                        /\ C e. R /\ D e. ( M LinCo V ) )
                      -> ( C .x. D ) e. ( M LinCo V ) ) $=
      ( vx vs vv wcel cfv wa co wceq eqid adantr ad2antrr adantl cbs cpw clinco
      clmod cv csca c0g cfsupp wbr clinc cmap wrex wb lcoval simpl simpr simprl
      lmodvscl syl3anc wi cmulr cmpt wf crg lmodring elmapi ffvelcdm ex syl imp
      ringcl fmpttd cvv fvexi elmapg sylancr mpbird w3a rmfsupp anim12i lincscm
      3jca oveq2 eqtrd breq1 eqeq2d anbi12d rspcev syl12anc rexlimiva mpbir2and
      oveq1 impcom sylbid 3impia ) EUDLZFEUAMZUBZLZNZACLZBEFUCOZLZABDOZXBLZWTXA
      NZXCBWQLZIUEZEUFMZUGMZUHUIZBXHFEUJMZOZPZNZICFUKOZULZNZXEWTXCXRUMXAWQBCXIE
      FUDIWQQZXIQZHUNRXFXRXEXFXRNZXEXDWQLZJUEZXJUHUIZXDYCFXLOZPZNZJXPULZYAWPXAX
      GYBWTWPXAXRWPWSUOSXFXAXRWTXAUPZRXFXGXQUQADXICWQEBXSXTGHURUSXRXFYHXQXGXFYH
      UTZXOXGYJUTIXPXHXPLZXONZXGYJYLXGNZXFYHYMXFNZKFAKUEZXHMZXIVAMZOZVBZXPLZYSX
      JUHUIZXDYSFXLOZPZYHYNYTFCYSVCZYNKFYRCYNYOFLZNXIVDLZXAYPCLZYRCLYNUUFUUEXFU
      UFYMWPUUFWSXAXIEXTVESZTRYNXAUUEXFXAYMYITRYNUUEUUGYLUUEUUGUTZXGXFYKUUIXOYK
      FCXHVCZUUIXHCFVFUUJUUEUUGFCYOXHVGVHVIRSVJCXIYQAYPHYQQZVKUSVLYNCVMLWSYTUUD
      UMCXIUAHVNXFWSYMWTWSXAWPWSUPRZTCFYSVMWRVOVPVQYNUUFWSXAVRZYKXKUUAXFUUMYMXF
      UUFWSXAUUHUULYIWBTYLYKXGXFYKXOUOZSYLXKXGXFYKXKXNUQSZKXHACXIFWRHVSUSYNXDAX
      MDOZUUBYLXDUUPPZXGXFXOUUQYKXNUUQXKBXMADWCTTSYNWTYKXANXKUUPUUBPYMWTXAUQYMY
      KXFXAYLYKXGUUNRYIVTUUOKXHCADYQYSEFXMGUUKXMQHYSQWAUSWDYGUUAUUCNJYSXPYCYSPZ
      YDUUAYFUUCYCYSXJUHWEUURYEUUBXDYCYSFXLWLWFWGWHWIVHVHWJWMWMWTXEYBYHNUMXAXRW
      QXDCXIEFUDJXSXTHUNSWKVHWNWO $.

    lincsumscmcl.b $e |- .+ = ( +g ` M ) $.
    $( The sum of a linear combination and a multiplication of a linear
       combination with a scalar is a linear combination.  (Contributed by AV,
       11-Apr-2019.) $)
    lincsumscmcl $p |- ( ( ( M e. LMod /\ V e. ~P ( Base ` M ) ) /\
                       ( C e. R /\ D e. ( M LinCo V ) /\ B e. ( M LinCo V ) ) )
                      -> ( ( C .x. D ) .+ B ) e. ( M LinCo V ) ) $=
      ( clmod wcel cbs cfv cpw wa clinco co w3a lincscmcl 3adant3r3 simpr3 jca
      lincsumcl syldan ) GLMHGNOPMQZBEMZCGHRSZMZAUIMZTZBCFSZUIMZUKQUMADSUIMUGUL
      QUNUKUGUHUJUNUKBCEFGHIJUAUBUGUHUJUKUCUDUMADGHKUEUF $.
  $}

  ${
    $d M a b s v x $.  $d V a b s v x $.
    $( According to the statement in [Lang] p. 129, the set ` ( LSubSp `` M ) `
       of all linear combinations of a set of vectors V is a submodule
       (_generated_ by V) of the module M. The elements of V are called
       _generators_ of ` ( LSubSp `` M ) ` .  (Contributed by AV,
       12-Apr-2019.) $)
    lincolss $p |- ( ( M e. LMod /\ V e. ~P ( Base ` M ) )
                     -> ( M LinCo V ) e. ( LSubSp ` M ) ) $=
      ( vx va vb vv vs clmod wcel cbs cfv cpw wa csca cplusg co eqidd c0g eqid
      cv clss cvsca clinco cfsupp wbr clinc wceq cmap wrex simpl biimtrdi ssrdv
      lcoval lcoel0 ne0d lincsumscmcl islssd ) AHIBAJKZLIMZCANKZJKZAOKZAUAKZAUB
      KZABUCPZUTURADEUSUTQUSVAQUSURQUSVBQUSVDQUSVCQUSFVEURUSFTZVEIVFURIZGTZUTRK
      UDUEVFVHBAUFKPUGMGVABUHPUIZMVGURVFVAUTABHGURSUTSVASZUMVGVIUJUKULUSVEARKAB
      UNUOETCTDTVBVAVDABVDSVJVBSUPUQ $.
  $}

  ${
    $d M f x $.  $d S f x $.  $d V f x $.
    $( Every linear combination of a subset of a linear subspace is also
       contained in the linear subspace.  (Contributed by AV, 20-Apr-2019.)
       (Proof shortened by AV, 30-Jul-2019.) $)
    ellcoellss $p |- ( ( M e. LMod /\ S e. ( LSubSp ` M ) /\ V C_ S )
                       -> A. x e. ( M LinCo V ) x e. S ) $=
      ( vf clmod wcel clss cfv wss w3a cv clinco co cbs wa eqid wi cvv com12 wb
      csca c0g wbr clinc wceq cmap wrex cpw simp1 lssss 3ad2ant2 sstr fvex ssex
      cfsupp elpwg biimprd mpcom syl ex 3ad2ant3 lcoval syl2anc lincellss eleq1
      mpd imbitrrid expd adantr com13 impr rexlimiva expimpd sylbid ralrimiv
      imp ) CFGZBCHIZGZDBJZKZALZBGZACDMNZWBWCWEGZWCCOIZGZELZCUBIZUCIUPUDZWCWIDC
      UEINZUFZPZEWJOIZDUGNZUHZPZWDWBVRDWGUIGZWFWRUAVRVTWAUJWBBWGJZWSVTVRWTWAVSB
      WGCWGQZVSQUKULWAVRWTWSRVTWAWTWSWAWTPDWGJZWSDBWGUMDSGZXBWSDWGCOUNUOXCWSXBD
      WGSUQURUSUTVAVBVGWGWCWOWJCDFEXAWJQWOQVCVDWBWHWQWDWQWBWHPZWDWNXDWDRZEWPWIW
      PGZWKWMXEXDWMXFWKPZWDWBWMXGWDRZRWHWMWBXHWMWBXGWDWBXGPWDWMWLBGZWBXGXIBWICD
      VEVQWCWLBVFVHVITVJVKVLVMTVNVOVP $.
  $}

  ${
    $d M f v x y $.  $d V f v x y $.
    $( A set of vectors of a module is a subset of the set of all linear
       combinations of the set.  (Contributed by AV, 18-Apr-2019.)  (Proof
       shortened by AV, 30-Jul-2019.) $)
    lcoss $p |- ( ( M e. LMod /\ V e. ~P ( Base ` M ) )
                  -> V C_ ( M LinCo V ) ) $=
      ( vv vf vx vy clmod wcel cbs cfv wa co cv cfsupp wbr wceq adantl weq eqid
      wb cpw clinco csca c0g clinc cmap wrex wi elelpwi expcom imp cur cif cmpt
      equequ1 ifbid cbvmptv mptcfsupp 3expa eqcomd wf lmod1cl lmod0cl ad3antrrr
      linc1 ifcld fmpttd fvex simplr elmapg sylancr mpbird breq1 eqeq2d anbi12d
      cvv oveq1 rspcedv mp2and lcoval adantr mpbir2and ex ssrdv ) AGHZBAIJZUAZH
      ZKZCBABUBLZWICMZBHZWKWJHZWIWLKZWMWKWFHZDMZAUCJZUDJZNOZWKWPBAUEJZLZPZKZDWQ
      IJZBUFLZUGZWIWLWOWHWLWOUHWEWLWHWOWKBWFUIUJQUKWNEBECRZWQULJZWRUMZUNZWRNOZW
      KXJBWTLZPZXFWEWHWLXKFWFWQXHXJABWKWRWFSZWQSZWRSZXHSZEFBXIFCRZXHWRUMEFRXGXR
      XHWREFCUOUPUQURUSWNXLWKWEWHWLXLWKPEWFWQXHXJABWKWRXNXOXPXQXJSVEUSUTWNXCXKX
      MKZDXJXEWNXJXEHZBXDXJVAZWNEBXIXDWEXIXDHWHWLEMBHWEXGXHWRXDXHWQXDAXOXDSZXQV
      BWQXDAWRXOYBXPVCVFVDVGWNXDVPHWHXTYATWQIVHWEWHWLVIXDBXJVPWGVJVKVLWPXJPZXCX
      STWNYCWSXKXBXMWPXJWRNVMYCXAXLWKWPXJBWTVQVNVOQVRVSWIWMWOXFKTWLWFWKXDWQABGD
      XNXOYBVTWAWBWCWD $.
  $}

  ${
    lspeqvlco.b $e |- B = ( Base ` M ) $.
    $( Lemma for ~ lspeqlco .  (Contributed by AV, 17-Apr-2019.) $)
    lspsslco $p |- ( ( M e. LMod /\ V e. ~P B )
                      -> ( ( LSpan ` M ) ` V ) C_ ( M LinCo V ) ) $=
      ( clmod wcel cpw wa clinco co clss cfv wss clspn simpl cbs eleq2i sylan2b
      pweqi eqid lincolss lcoss lspssp syl3anc ) BEFZCAGZFZHUEBCIJZBKLZFZCUHMZC
      BNLZLUHMUEUGOUGUECBPLZGZFZUJUFUNCAUMDSQZBCUARUGUEUOUKUPBCUBRUICUHULBUITUL
      TUCUD $.

    $d B s x $.  $d M s x y $.  $d V s x y $.
    $( Lemma for ~ lspeqlco .  (Contributed by AV, 20-Apr-2019.) $)
    lcosslsp $p |- ( ( M e. LMod /\ V e. ~P B )
                      -> ( M LinCo V ) C_ ( ( LSpan ` M ) ` V ) ) $=
      ( vx vs vy clmod wcel cpw wa clinco cfv cv wss wel wi wral ad2antlr eqid
      co clspn clss crab cint ellcoellss 3exp ad2antrr imp rspcv syld ralrimiva
      elequ1 elintrab sylibr wceq simpll elpwi lspval syl2anc eleqtrrd ex ssrdv
      vex ) BHIZCAJIZKZEBCLUAZCBUBMZMZVGENZVHIZVKVJIVGVLKZVKCFNZOZFBUCMZUDUEZVJ
      VMVOEFPZQZFVPRVKVQIVMVSFVPVMVNVPIZKVOGFPZGVHRZVRVMVTVOWBQZVEVTWCQVFVLVEVT
      VOWBGVNBCUFUGUHUIVLWBVRQVGVTWAVRGVKVHGEFUMUJSUKULVOFVKVPEVDUNUOVMVECAOZVJ
      VQUPVEVFVLUQVFWDVEVLCAURSFVPCVIABDVPTVITUSUTVAVBVC $.

    $( Equivalence of a _span_ of a set of vectors of a left module defined as
       the intersection of all linear subspaces which each contain every vector
       in that set (see ~ df-lsp ) and as the set of all linear combinations of
       the vectors of the set with finite support.  (Contributed by AV,
       20-Apr-2019.) $)
    lspeqlco $p |- ( ( M e. LMod /\ V e. ~P B )
                      -> ( M LinCo V ) = ( ( LSpan ` M ) ` V ) ) $=
      ( clmod wcel cpw wa clinco co clspn cfv lcosslsp lspsslco eqssd ) BEFCAGF
      HBCIJCBKLLABCDMABCDNO $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Linear independence
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

<HTML>
According to the definition in [Lang] p. 129: "A subset S of a module M is said
to be <b>linearly independent</b> (over [the ring] A) if whenever we have a
linear combination &sum;<sub>x &isin;S</sub> a<sub>x</sub>x which is equal to
0, then a<sub>x</sub>=0 for all x&isin;S."  This definition does not care for
the finiteness of the set S (because the definition of a linear combination
in [Lang] p.129 does already assure that only a finite number of coefficients
can be 0 in the sum).  Our definition ~ df-lininds does also neither claim that
the subset must be finite, nor that almost all coefficients within the linear
combination are 0.  If this is required, it must be explicitly stated as
precondition in the corresponding theorems.<br>
<br>
Usually, the linear independence is defined for vector spaces, see Wikipedia
("Linear independence", 15-Apr-2019,
~ https://en.wikipedia.org/wiki/Linear_independence ): "In the theory of vector
spaces, a set of vectors is said to be <b>linearly dependent</b> if at least
one of the vectors in the set can be defined as a linear combination of the
others; if no vector in the set can be written in this way, then the vectors
are said to be <b>linearly independent</b>."  Furthermore, "In order to allow
the number of linearly independent vectors in a vector space to be countably
infinite, it is useful to define linear dependence as follows. More generally,
let V be a vector space over a field K, and let {v<sub>i</sub> | i&isin;I} be a
family of elements of V.  The family is linearly dependent over K if there
exists a finite family {a<sub>j</sub> | j&isin;J} of elements of K, all
nonzero, such that &sum;<sub>j&isin;J</sub> a<sub>j</sub>v<sub>j</sub>=0.
A set X of elements of V is linearly independent if the corresponding
family{x}<sub>x&isin;X</sub> is linearly independent".
<br>
<b>Remark 1:</b> There are already definitions of (linearly) independent
families ( ~ df-lindf ) and (linearly) independent sets ( ~ df-linds ).  These
definitions are based on the principle "of vectors, no nonzero multiple of
which can be expressed as a linear combination of other elements" or (see ~
lbsind2 ) "every element is not in the span of the remainder of the [[set]".
The equivalence of Definitions ~ df-linds and ~ df-lininds for (linear)
independence for (left) modules is shown in ~ lindslininds .
<br>
<b>Remark 2:</b> Subsets of the base set of a (left) module are <b>linearly
dependent</b> if they are not linearly independent (see ~ df-lindeps ) or,
according to Wikipedia, "if at least one of the vectors in the set can be
defined as a linear combination of the others", see ~ islindeps2 .  The
reversed implication is not valid for arbitrary modules (but for arbitrary
vector spaces), because it requires a division by a coefficient.  Therefore,
the definition of Wikipedia is equivalent to our definition for (left) vector
spaces (see ~ isldepslvec2 ) and not for (left) modules in general.
</HTML>

$)

  $c linIndS linDepS $.

  $( Extend class notation with the relation between a module and its linearly
     independent subsets. $)
  clininds $a class linIndS $.

  $( Extend class notation with the relation between a module and its linearly
     dependent subsets. $)
  clindeps $a class linDepS $.

  ${
    $d f m s x $.
    $( Define the relation between a module and its linearly independent
       subsets.  (Contributed by AV, 12-Apr-2019.)  (Revised by AV,
       24-Apr-2019.)  (Revised by AV, 30-Jul-2019.) $)
    df-lininds $a |- linIndS = { <. s , m >. | ( s e. ~P ( Base ` m )
                /\ A. f e. ( ( Base ` ( Scalar ` m ) ) ^m s )
                    ( ( f finSupp ( 0g ` ( Scalar ` m ) )
                        /\ ( f ( linC ` m ) s ) = ( 0g ` m ) )
                      -> A. x e. s ( f ` x ) = ( 0g ` ( Scalar ` m ) ) ) ) } $.

    $( The class defining the relation between a module and its linearly
       independent subsets is a relation.  (Contributed by AV, 13-Apr-2019.) $)
    rellininds $p |- Rel linIndS $=
      ( vs vm vf vx cv cbs cfv cpw wcel csca c0g cfsupp wbr clinc co wceq wa wi
      wral cmap clininds df-lininds relopabiv ) AEZBEZFGHICEZUEJGZKGZLMUFUDUENG
      OUEKGPQDEUFGUHPDUDSRCUGFGUDTOSQABUADCBAUBUC $.
  $}

  ${
    $d m s $.
    $( Define the relation between a module and its linearly dependent subsets.
       (Contributed by AV, 26-Apr-2019.) $)
    df-lindeps $a |- linDepS = { <. s , m >. | -. s linIndS m } $.
  $}

  $( The classes of the module and its linearly independent subsets are sets.
     (Contributed by AV, 13-Apr-2019.) $)
  linindsv $p |- ( S linIndS M -> ( S e. _V /\ M e. _V ) ) $=
    ( clininds rellininds brrelex12i ) ABCDE $.

  ${
    $d B m s $.  $d E f m s $.  $d M f m s x $.  $d S f m s x $.  $d Z m s $.
    $d .0. m s $.
    islininds.b $e |- B = ( Base ` M ) $.
    islininds.z $e |- Z = ( 0g ` M ) $.
    islininds.r $e |- R = ( Scalar ` M ) $.
    islininds.e $e |- E = ( Base ` R ) $.
    islininds.0 $e |- .0. = ( 0g ` R ) $.
    $( The property of being a linearly independent subset.  (Contributed by
       AV, 13-Apr-2019.)  (Revised by AV, 30-Jul-2019.) $)
    islininds $p |- ( ( S e. V /\ M e. W ) -> ( S linIndS M
                  <-> ( S e. ~P B /\ A. f e. ( E ^m S )
                        ( ( f finSupp .0. /\ ( f ( linC ` M ) S ) = Z )
                          -> A. x e. S ( f ` x ) = .0. ) ) ) ) $=
      ( cfv c0g wceq eqtr4di vs vm cv cbs cpw wcel csca cfsupp clinc co wa wral
      wbr wi cmap clininds simpl fveq2 adantl pweqd eleq12d fveq2d breq2d eqidd
      oveq12d oveq123d eqeq12d anbi12d eqeq2d raleqbidv imbi12d df-lininds
      brabga ) UAUCZUBUCZUDQZUEZUFZEUCZVOUGQZRQZUHUMZVSVNVOUIQZUJZVORQZSZUKZAUC
      VSQZWASZAVNULZUNZEVTUDQZVNUOUJZULZUKDBUEZUFZVSJUHUMZVSDGUIQZUJZKSZUKZWHJS
      ZADULZUNZEFDUOUJZULZUKUAUBDGUPHIVNDSZVOGSZUKZVRWPWNXFXIVNDVQWOXGXHUQZXIVP
      BXHVPBSXGXHVPGUDQBVOGUDURLTUSUTVAXIWKXDEWMXEXIWLFVNDUOXHWLFSXGXHWLCUDQFXH
      VTCUDXHVTGUGQZCVOGUGURZNTZVBOTUSXJVEXIWGXAWJXCXIWBWQWFWTXIWAJVSUHXIWACRQZ
      JXIVTCRXIVTXKCXHVTXKSXGXLUSNTVBPTVCXIWDWSWEKXIVSVSVNDWCWRXHWCWRSXGVOGUIUR
      USXIVSVDXJVFXIWEGRQZKXHWEXOSXGVOGRURUSMTVGVHXIWIXBAVNDXJXIWAJWHXHWAJSXGXH
      WAXNJXHVTCRXMVBPTUSVIVJVKVJVHAEUBUAVLVM $.

    $( The implications of being a linearly independent subset.  (Contributed
       by AV, 13-Apr-2019.)  (Revised by AV, 30-Jul-2019.) $)
    linindsi $p |- ( S linIndS M -> ( S e. ~P B /\ A. f e. ( E ^m S )
                        ( ( f finSupp .0. /\ ( f ( linC ` M ) S ) = Z )
                          -> A. x e. S ( f ` x ) = .0. ) ) ) $=
      ( wbr wcel cv cfv wa cvv clininds cfsupp clinc co wceq wral cmap linindsv
      cpw wi wb islininds syl ibi ) DGUAOZDBUIPEQZHUBOUPDGUCRUDIUESAQUPRHUEADUF
      UJEFDUGUDUFSZUODTPGTPSUOUQUKDGUHABCDEFGTTHIJKLMNULUMUN $.

    $d F x f $.  $d .0. f $.  $d Z f $.
    $( The implications of being a linearly independent subset and a linear
       combination of this subset being 0.  (Contributed by AV, 24-Apr-2019.)
       (Revised by AV, 30-Jul-2019.) $)
    linindslinci $p |- ( ( S linIndS M /\ ( F e. ( E ^m S ) /\ F finSupp .0.
                                            /\ ( F ( linC ` M ) S ) = Z ) )
                         -> A. x e. S ( F ` x ) = .0. ) $=
      ( vf wbr co cfsupp wceq wi clininds cmap wcel clinc cfv w3a wral linindsi
      cv wa breq1 oveq1 eqeq1d anbi12d fveq1 ralbidv imbi12d rspcv com23 3impib
      cpw com12 simpl2im imp ) DGUAPZFEDUBQZUCZFHRPZFDGUDUEZQZISZUFZAUIZFUEZHSZ
      ADUGZVEDBVAUCOUIZHRPZVQDVIQZISZUJZVMVQUEZHSZADUGZTZOVFUGZVLVPTABCDOEGHIJK
      LMNUHVLWFVPVGVHVKWFVPTVGWFVHVKUJZVPWEWGVPTOFVFVQFSZWAWGWDVPWHVRVHVTVKVQFH
      RUKWHVSVJIVQFDVIULUMUNWHWCVOADWHWBVNHVMVQFUOUMUPUQURUSUTVBVCVD $.

    $d W f $.
    $( The property of being a linearly independent finite subset.
       (Contributed by AV, 27-Apr-2019.) $)
    islinindfis $p |- ( ( S e. Fin /\ M e. W )
                        -> ( S linIndS M <-> ( S e. ~P B /\ A. f e. ( E ^m S )
             ( ( f ( linC ` M ) S ) = Z -> A. x e. S ( f ` x ) = .0. ) ) ) ) $=
      ( cfn wcel wa wral wi clininds wbr cpw cv cfsupp clinc cfv wceq islininds
      co cmap wo pm4.79 cvv wf elmapi adantl simpll c0g fvexi fdmfifsupp adantr
      imim1i expd ax-1 jaoi sylbir com12 pm3.42 impbid1 ralbidva anbi2d bitrd
      a1i ) DPQZGHQZRZDGUAUBDBUCQZEUDZIUEUBZVSDGUFUGUJJUHZRAUDVSUGIUHADSZTZEFDU
      KUJZSZRVRWAWBTZEWDSZRABCDEFGPHIJKLMNOUIVQWEWGVRVQWCWFEWDVQVSWDQZRZWCWFWCW
      IWFWCVTWBTZWFULWIWFTZWBVTWAUMWJWKWFWJWIWAWBWIWARVTWBWIVTWAWIDFVSUNIWHDFVS
      UOVQVSFDUPUQVOVPWHURIUNQWIICUSOUTVNVAVBVCVDWFWIVEVFVGVHVTWAWBVIVJVKVLVM
      $.

    $( The property of being a linearly independent finite subset.
       (Contributed by AV, 27-Apr-2019.) $)
    islinindfiss $p |- ( ( M e. W /\ S e. Fin /\ S e. ~P B )
                        -> ( S linIndS M <-> A. f e. ( E ^m S )
               ( ( f ( linC ` M ) S ) = Z -> A. x e. S ( f ` x ) = .0. ) ) ) $=
      ( wcel cv cfv co wceq cfn cpw clininds wbr clinc wral wi cmap islinindfis
      wa wb ancoms 3adant3 3anibar ) GHPZDUAPZDBUBPZDGUCUDZEQZDGUERSJTAQUSRITAD
      UFUGEFDUHSUFZUOUPURUQUTUJUKZUQUPUOVAABCDEFGHIJKLMNOUIULUMUN $.
  $}

  ${
    $d M x f $.  $d S x f $.
    $( A linearly independent set is a subset of (the base set of) a module.
       (Contributed by AV, 13-Apr-2019.) $)
    linindscl $p |- ( S linIndS M -> S e. ~P ( Base ` M ) ) $=
      ( vf vx clininds wbr cbs cfv cpw wcel cv csca c0g cfsupp clinc co wceq wa
      wral eqid wi cmap linindsi simpld ) ABEFABGHZIJCKZBLHZMHZNFUFABOHPBMHZQRD
      KUFHUHQDASUACUGGHZAUBPSDUEUGACUJBUHUIUETUITUGTUJTUHTUCUD $.
  $}

  ${
    $d M m s $.  $d S m s $.
    $( A linearly dependent subset is not a linearly independent subset.
       (Contributed by AV, 26-Apr-2019.) $)
    lindepsnlininds $p |- ( ( S e. V /\ M e. W )
                            -> ( S linDepS M <-> -. S linIndS M ) ) $=
      ( vs vm cv clininds wbr wn clindeps wceq breq12 notbid df-lindeps brabga
      wa ) EGZFGZHIZJABHIZJEFABKCDRALSBLQTUARASBHMNFEOP $.
  $}

  ${
    $d E f $.  $d M f x $.  $d S f x $.
    islindeps.b $e |- B = ( Base ` M ) $.
    islindeps.z $e |- Z = ( 0g ` M ) $.
    islindeps.r $e |- R = ( Scalar ` M ) $.
    islindeps.e $e |- E = ( Base ` R ) $.
    islindeps.0 $e |- .0. = ( 0g ` R ) $.
    $( The property of being a linearly dependent subset.  (Contributed by AV,
       26-Apr-2019.)  (Revised by AV, 30-Jul-2019.) $)
    islindeps $p |- ( ( M e. W /\ S e. ~P B ) -> ( S linDepS M
             <-> E. f e. ( E ^m S ) ( f finSupp .0. /\ ( f ( linC ` M ) S ) = Z
                                      /\ E. x e. S ( f ` x ) =/= .0. ) ) ) $=
      ( wa wbr wn wrex wb wcel cpw clindeps clininds cfsupp clinc cfv wceq wral
      cv co wi cmap wne w3a lindepsnlininds ancoms islininds ibar bicomd adantl
      bitrd notbid rexnal rexbii bitr2i anbi2i pm4.61 df-3an 3bitr4i bitr3i a1i
      df-ne 3bitrd ) GHUAZDBUBZUAZPZDGUCQZDGUDQZRZEUJZIUEQZWBDGUFUGUKJUHZPZAUJW
      BUGZIUHZADUIZULZEFDUMUKZUIZRZWCWDWFIUNZADSZUOZEWJSZVQVOVSWATDGVPHUPUQVRVT
      WKVRVTVQWKPZWKVQVOVTWQTABCDEFGVPHIJKLMNOURUQVQWQWKTVOVQWKWQVQWKUSUTVAVBVC
      WLWPTVRWLWIRZEWJSWPWIEWJVDWRWOEWJWEWHRZPWEWNPWRWOWSWNWEWNWGRZADSWSWMWTADW
      FIVMVEWGADVDVFVGWEWHVHWCWDWNVIVJVEVKVLVN $.
  $}

  ${
    $d B z $.  $d E z $.  $d G z $.  $d M z $.  $d S z $.  $d X z $.  $d Y z $.
    lincext.b $e |- B = ( Base ` M ) $.
    lincext.r $e |- R = ( Scalar ` M ) $.
    lincext.e $e |- E = ( Base ` R ) $.
    lincext.0 $e |- .0. = ( 0g ` R ) $.
    lincext.z $e |- Z = ( 0g ` M ) $.
    lincext.n $e |- N = ( invg ` R ) $.
    lincext.f $e |- F = ( z e. S |-> if ( z = X , ( N ` Y ) , ( G ` z ) ) ) $.
    $( Property 1 of an extension of a linear combination.  (Contributed by AV,
       20-Apr-2019.)  (Revised by AV, 29-Apr-2019.) $)
    lincext1 $p |- ( ( ( M e. LMod /\ S e. ~P B )
                       /\ ( Y e. E /\ X e. S /\ G e. ( E ^m ( S \ { X } ) ) ) )
                     -> F e. ( E ^m S ) ) $=
      ( clmod wcel cpw wa csn cdif cmap co w3a wceq cfv cif cmpt cgrp csca eqid
      cv wf lmodfgrp ad2antrr eqeltrid simpr1 grpinvcl syl2anc wn wi elmapi wne
      biimpri anim2i eldifsn sylibr ffvelcdm sylan2 ex syl 3ad2ant3 adantl impl
      df-ne ifclda fmpttd cvv wb simpr cbs fvexi jctil adantr elmapg mpbird ) H
      UAUBZDBUCZUBZUDZKEUBZJDUBZGEDJUEUFZUGUHUBZUIZUDZFADAUQZJUJZKIUKZXBGUKZULZ
      UMZEDUGUHZTXAXGXHUBZDEXGURZXAADXFEXAXBDUBZUDXCXDXEEXAXDEUBZXKXCXACUNUBWPX
      LXACHUOUKZUNOWLXMUNUBWNWTXMHXMUPUSUTVAWOWPWQWSVBECIKPSVCVDUTXAXKXCVEZXEEU
      BZWTXKXNUDZXOVFZWOWSWPXQWQWSWREGURZXQGEWRVGXRXPXOXPXRXBWRUBZXOXPXKXBJVHZU
      DXSXNXTXKXTXNXBJVTVIVJXBDJVKVLWREXBGVMVNVOVPVQVRVSWAWBXAEWCUBZWNUDZXIXJWD
      WOYBWTWOWNYAWLWNWEECWFPWGWHWIEDXGWCWMWJVPWKVA $.

    $( Property 2 of an extension of a linear combination.  (Contributed by AV,
       20-Apr-2019.)  (Revised by AV, 30-Jul-2019.) $)
    lincext2 $p |- ( ( ( M e. LMod /\ S e. ~P B )
                         /\ ( Y e. E /\ X e. S /\ G e. ( E ^m ( S \ { X } ) ) )
                         /\ G finSupp .0. ) -> F finSupp .0. ) $=
      ( clmod wcel cpw wa csn cdif cmap w3a cfsupp wbr cvv cdm cfn wceq cfv cif
      co cv fvex ifex dmmpti difeq1i wss snssi 3ad2ant2 dfss4 eqeltrdi eqeltrid
      sylib snfi lincext1 3adant3 wfun elmapfun cres wf fdmdifeqresdif 3ad2ant3
      syl elmapi simp3 c0g fvexi a1i resfsupp ) HUAUBDBUCUBUDZKEUBZJDUBZGEDJUEZ
      UFZUGUQUBZUHZGLUIUJZUHZWJFGUKEDUGUQZLWNFULZWJUFDWJUFZUMWPDWJADAURZJUNZKIU
      OZWRGUOZUPFWSWTXAKIUSWRGUSUTTVAVBWNWQWIUMWNWIDVCZWQWIUNWLWFXBWMWHWGXBWKJD
      VDVEVEWIDVFVIJVJVGVHWFWLFWOUBZWMABCDEFGHIJKLMNOPQRSTVKVLZWNXCFVMXDFEDVNVS
      WLWFGFWJVOUNZWMWKWGXEWHWKWJEGVPXEGEWJVTADEFGWTJTVQVSVRVEWFWLWMWALUKUBWNLC
      WBQWCWDWE $.

    $d N z $.
    $( Property 3 of an extension of a linear combination.  (Contributed by AV,
       23-Apr-2019.)  (Revised by AV, 30-Jul-2019.) $)
    lincext3 $p |- ( ( ( M e. LMod /\ S e. ~P B )
                   /\ ( Y e. E /\ X e. S /\ G e. ( E ^m ( S \ { X } ) ) )
                   /\ ( G finSupp .0.
                   /\ ( Y ( .s ` M ) X ) = ( G ( linC ` M ) ( S \ { X } ) ) ) )
                     -> ( F ( linC ` M ) S ) = Z ) $=
      ( clmod wcel cpw wa csn cdif cmap co w3a cfsupp wbr cvsca cfv wceq cplusg
      clinc cres simp1l simp1r simp2 3ad2ant2 lincext1 lincext2 3adant3r elmapi
      3adant3 fdmdifeqresdif syl 3ad2ant3 eqid lincdifsn syl321anc oveq1 eqcoms
      wf adantl cminusg simpll elelpwi expcom com12 impcom simpr1 lmodvsneg cif
      wi cv iftrue fvexd fvmptd3 eqcomd oveq1d eqtr2d oveq2d syl3anc lmodvnegid
      cvv lmodvscl syl2anc eqtrd ) HUAUBZDBUCUBZUDZKEUBZJDUBZGEDJUEUFZUGUHUBZUI
      ZGLUJUKZKJHULUMZUHZGXFHUPUMZUHZUNZUDZUIZFDXLUHZXMJFUMZJXJUHZHUOUMZUHZMXPX
      AXBXEFEDUGUHUBZFLUJUKZGFXFUQUNZXQYAUNXAXBXHXOURXAXBXHXOUSXHXCXEXOXDXEXGUT
      ZVAXCXHYBXOABCDEFGHIJKLMNOPQRSTVBVFXCXHXIYCXNABCDEFGHIJKLMNOPQRSTVCVDXHXC
      YDXOXGXDYDXEXGXFEGVOYDGEXFVEADEFGKIUMZJTVGVHVIVABXTCEXJFGHDJLNOPXJVJZXTVJ
      ZQVKVLXPYAXKXSXTUHZMXOXCYAYIUNZXHXNYJXIYJXMXKXMXKXSXTVMVNVPVIXCXHYIMUNXOX
      CXHUDZYIXKXKHVQUMZUMZXTUHZMYKXSYMXKXTYKYMYFJXJUHXSYKBKXJCEIYLHJNOYGYLVJZP
      SXAXBXHVRZXHXCJBUBZXEXDXCYQWFXGXCXEYQXBXEYQWFXAXEXBYQJDBVSVTVPWAVAWBZXCXD
      XEXGWCZWDYKYFXRJXJYKXRYFYKAJAWGZJUNZYFYTGUMZWEYFDFWQTUUAYFUUBWHXHXEXCYEVP
      YKKIWIWJWKWLWMWNYKXAXKBUBZYNMUNYPYKXAXDYQUUCYPYSYRKXJCEBHJNOYGPWRWOXTYLBH
      XKMNYHRYOWPWSWTVFWTWT $.
  $}

  ${
    $d B f g s y z $.  $d M f g s y z $.  $d R f x z $.  $d S f g s x y z $.
    $d V g s y z $.  $d Z f g s y $.  $d .0. f g s x y z $.
    lindslinind.r $e |- R = ( Scalar ` M ) $.
    lindslinind.b $e |- B = ( Base ` R ) $.
    lindslinind.0 $e |- .0. = ( 0g ` R ) $.
    lindslinind.z $e |- Z = ( 0g ` M ) $.
    $( Implication 1 for ~ lindslininds .  (Contributed by AV, 25-Apr-2019.)
       (Revised by AV, 30-Jul-2019.)  (Proof shortened by II, 16-Feb-2023.) $)
    lindslinindsimp1 $p |- ( ( S e. V /\ M e. LMod )
            -> ( ( S e. ~P ( Base ` M ) /\ A. f e. ( B ^m S ) ( ( f finSupp .0.
                 /\ ( f ( linC ` M ) S ) = Z ) -> A. x e. S ( f ` x ) = .0. ) )
           -> ( S C_ ( Base ` M ) /\ A. s e. S A. y e. ( B \ { .0. } )
            -. ( y ( .s ` M ) s ) e. ( ( LSpan ` M ) ` ( S \ { s } ) ) ) ) ) $=
      ( vg wcel wa cfv wi vz clmod cbs cpw cv cfsupp wbr clinc co wceq wral wss
      cmap cvsca csn cdif clspn wn elpwi ad2antrl wrex weq cminusg cif cmpt w3a
      wo simpr anim2i ancomd ad2antrr eldifi adantl adantr simprl 3jca lincext2
      simprrl syl3anc lincext1 syl2anc breq1 oveq1 eqeq1d anbi12d fveq1 ralbidv
      eqid imbi12d rspcv syl exp4a mpid simprr lincext3 fveqeq2 cvv eqidd fvexd
      iftrue fvmptd cgrp lmodfgrp grpinvnzcl eldif fvex pm2.21 sylnbi simplbiim
      elsn com25 com24 impcom com13 imp sylbid syld embantd syldc exp5j expdimp
      expd pm2.01d olcd animorl pm2.61ian ralrimiva ralnex ralbii bitr3i sylibr
      ex ianor intnand clinco wb difexg ssdifssd elpwd jca eleq2d bicomd lcoval
      lspeqlco c0g eqcomi breq2i anbi1i rexbii anbi2i bitrdi mtbird ralrimivva
      bitrd ) EHQZGUBQZRZEGUCSZUDZQZFUEZIUFUGZUVAEGUHSZUIZJUJZRZAUEZUVASZIUJZAE
      UKZTZFCEUMUIZUKZRZEUURULZBUEZKUEZGUNSUIZEUVQUOZUPZGUQSSZQZURZBCIUOZUPZUKK
      EUKZRUUQUVNRZUVOUWFUUTUVOUUQUVMEUURUSZUTUWGUWCKBEUWEUWGUVQEQZUVPUWEQZRZRZ
      UWBUVRUURQZPUEZIUFUGZUVRUWNUVTUVCUIUJZRZPCUVTUMUIZVAZRZUWLUWSUWMUWLUWOURZ
      UWPURZVGZPUWRUKZUWSURZUWLUXCPUWRUWOUWLUWNUWRQZRZUXCUWOUXGRZUXBUXAUXHUWPUX
      GUWOUWPUXBTUXGUWOUWPUXBUWLUXFUWQUXBUWGUWKUXFUWQRZUXBTZUVNUUQUWKUXJTZUVMUU
      TUUQUXKTUVMUUTUUQUWKUXIUXBUUTUUQRZUWKRZUXIRZUVMUAEUAKVBZUVPDVCSZSZUAUEUWN
      SZVDZVEZEUVCUIZJUJZUVGUXTSZIUJZAEUKZTZUXBUXNUVMUXTIUFUGZUYFUXNUUPUUTRZUVP
      CQZUWIUXFVFZUWOUYGUXLUYHUWKUXIUXLUUTUUPUUQUUPUUTUUOUUPVHZVIZVJVKZUXNUYIUW
      IUXFUXMUYIUXIUWKUYIUXLUWJUYIUWIUVPCUWDVLVMVMVNUXMUWIUXIUXLUWIUWJVOZVNZUXM
      UXFUWQVOVPZUXMUXFUWOUWPVRUAUURDECUXTUWNGUXPUVQUVPIJUURWHZLMNOUXPWHZUXTWHZ
      VQVSUXNUVMUYGUYBUYEUXNUXTUVLQZUVMUYGUYBRZUYETZTUXNUYHUYJUYTUXMUYHUXIUXMUU
      TUUPUXLUUTUUPRUWKUYLVNVJVNUYPUAUURDECUXTUWNGUXPUVQUVPIJUYQLMNOUYRUYSVTWAU
      VKVUBFUXTUVLUVAUXTUJZUVFVUAUVJUYEVUCUVBUYGUVEUYBUVAUXTIUFWBVUCUVDUYAJUVAU
      XTEUVCWCWDWEVUCUVIUYDAEVUCUVHUYCIUVGUVAUXTWFWDWGWIWJWKWLWMUXNUYBUYEUXBUXN
      UYHUYJUWQUYBUYMUYPUXMUXFUWQWNUAUURDECUXTUWNGUXPUVQUVPIJUYQLMNOUYRUYSWOVSU
      XNUYEUVQUXTSZIUJZUXBUXNUWIUYEVUETUYOUYDVUEAUVQEUVGUVQIUXTWPWJWKUXNVUEUXQI
      UJZUXBUXNVUDUXQIUXMVUDUXQUJUXIUXMUAUVQUXSUXQEUXTWQUXMUXTWRUXOUXSUXQUJUXMU
      XOUXQUXRWTVMUYNUXMUVPUXPWSXAVNWDUXMVUFUXBTZUXIUWKUXLVUGUWIUWJUXLVUGTUXLUW
      JUWIVUGUUQUUTUWJUWIVUGTZTZUUPUUOUUTVUITUUPUWJUUTUUOVUHUUPDXBQZUWJUUTUUOVU
      HTTZTDGLXCVUJUWJVUKVUJUWJRUXQUWEQZVUKCDUXPUVPIMNUYRXDVULUXQCQUXQUWDQZURVU
      KUXQCUWDXEVUMVUFVUKUXQIUVPUXPXFXJVUFURVUFUUOUWIUUTUXBVUFUUOUWIUUTUXBTTTXG
      XKXHXIWKYLWKXLXMXMXNXOXMVNXPXQXRXSXTXMXMXOYAYBXMYCYDUXAUXGUXBYEYFYGUXEUWQ
      URZPUWRUKUXDUWQPUWRYHVUNUXCPUWRUWOUWPYMYIYJYKYNUWLUWBUVRGUVTYOUIZQZUWTUWL
      UUPUVTUUSQZUWBVUPYPUUQUUPUVNUWKUYKVKUWGVUQUWKUWGUVTUURWQUUOUVTWQQUUPUVNEU
      VSHYQVKUUTUVTUURULUUQUVMUUTEUURUVSUWHYRZUTYSVNUUPVUQRZVUPUWBVUSVUOUWAUVRU
      URGUVTUYQUUDUUAUUBWAUWLVUSVUPUWTYPUWGVUSUWKUWGUUPVUQUUQUUPUVNUYKVNUUTVUQU
      UQUVMUUTUVTUURWQEUVSUUSYQVURYSUTYTVNVUSVUPUWMUWNDUUESZUFUGZUWPRZPUWRVAZRU
      WTUURUVRCDGUVTUBPUYQLMUUCVVCUWSUWMVVBUWQPUWRVVAUWOUWPVUTIUWNUFIVUTNUUFUUG
      UUHUUIUUJUUKWKUUNUULUUMYTYL $.

    ${
      lindslinind.y $e |- Y = ( ( invg ` R ) ` ( f ` x ) ) $.
      lindslinind.g $e |- G = ( f |` ( S \ { x } ) ) $.
      $( Lemma 1 for ~ lindslinindsimp2 .  (Contributed by AV, 25-Apr-2019.) $)
      lindslinindimp2lem1 $p |- ( ( ( S e. V /\ M e. LMod )
                        /\ ( S C_ ( Base ` M ) /\ x e. S /\ f e. ( B ^m S ) ) )
                                  -> Y e. B ) $=
        ( wcel wa cfv clmod cbs wss cv cmap co w3a cminusg cgrp lmodfgrp adantl
        wf wi elmapi ffvelcdm a1d syl com13 3imp eqid grpinvcl syl2an eqeltrid
        ex ) DHRZGUARZSZDGUBTUCZAUDZDRZEUDZBDUEUFRZUGZSIVIVKTZCUHTZTZBPVGCUIRZV
        NBRZVPBRVMVFVQVECGLUJUKVHVJVLVRVLVJVHVRVLDBVKULZVJVHVRUMZUMVKBDUNVSVJVT
        VSVJSVRVHDBVIVKUOUPVDUQURUSBCVOVNMVOUTVAVBVC $.

      $( Lemma 2 for ~ lindslinindsimp2 .  (Contributed by AV, 25-Apr-2019.) $)
      lindslinindimp2lem2 $p |- ( ( ( S e. V /\ M e. LMod )
                        /\ ( S C_ ( Base ` M ) /\ x e. S /\ f e. ( B ^m S ) ) )
                                  -> G e. ( B ^m ( S \ { x } ) ) ) $=
        ( wcel wf cvv clmod wa cbs cfv wss cv cmap w3a csn cdif elmapi 3ad2ant3
        co cres adantl difss fssres sylancl feq1i sylibr wb fvexi difexg elmapg
        ad2antrr sylancr mpbird ) DHRZGUARZUBZDGUCUDUEZAUFZDRZEUFZBDUGUMRZUHZUB
        ZFBDVLUIZUJZUGUMRZVSBFSZVQVSBVNVSUNZSZWAVQDBVNSZVSDUEWCVPWDVJVOVKWDVMVN
        BDUKULUODVRUPDBVSVNUQURVSBFWBQUSUTVQBTRVSTRZVTWAVABCUCMVBVHWEVIVPDVRHVC
        VEBVSFTTVDVFVG $.

      $( Lemma 3 for ~ lindslinindsimp2 .  (Contributed by AV, 25-Apr-2019.)
         (Revised by AV, 30-Jul-2019.) $)
      lindslinindimp2lem3 $p |- ( ( ( S e. V /\ M e. LMod )
                        /\ ( S C_ ( Base ` M ) /\ x e. S )
                        /\ ( f e. ( B ^m S ) /\ f finSupp .0. ) )
                                  -> G finSupp .0. ) $=
        ( wcel wa cv clmod cbs cfv wss cmap co cfsupp wbr w3a csn cdif cres cvv
        simp3r c0g fvexi a1i fsuppres eqbrtrid ) DHRGUARSZDGUBUCUDATZDRSZETZBDU
        EUFRZVCJUGUHZSUIZFVCDVAUJUKZULJUGQVFVCUMVGJUTVBVDVEUNJUMRVFJCUONUPUQURU
        S $.

      $d G y $.
      $( Lemma 4 for ~ lindslinindsimp2 .  (Contributed by AV, 25-Apr-2019.)
         (Revised by AV, 30-Jul-2019.)  (Proof shortened by II,
         16-Feb-2023.) $)
      lindslinindimp2lem4 $p |- ( ( ( S e. V /\ M e. LMod )
                        /\ ( S C_ ( Base ` M ) /\ x e. S )
                        /\ ( f e. ( B ^m S ) /\ f finSupp .0.
                             /\ ( f ( linC ` M ) S ) = Z ) )
            -> ( M gsum ( y e. ( S \ { x } ) |-> ( ( f ` y ) ( .s ` M ) y ) ) )
               = ( Y ( .s ` M ) x ) ) $=
        ( wcel cfv clmod wa cbs wss cv cmap cfsupp wbr clinc wceq w3a csn cvsca
        co cdif cmpt cgsu wi cminusg cplusg cpw simpr adantr simprl wb ad2antrr
        cres elpwg mpbird adantl 3jca a1i eqid lincdifsn syl3anc eqeq1d lmodgrp
        simpl cgrp ad2antrl wf elmapi ffvelcdm expcom ad2antll syl5com lmodvscl
        imp cvv difexg ssdifss lindslinindimp2lem2 syl13anc lindslinindimp2lem3
        ssel2 jca lincfsuppcl grpinvid2 bitr4d eqcom csca fveq2i eqtri eleqtrdi
        oveq1i elpwd lincval fveq1i fvres eqtrd oveq1d mpteq2dva oveq2d eqeq12d
        lmodvsneg eqcomi biimpd sylbid biimtrid ex com23 3impia com12 ) EISZHUA
        SZUBZEHUCTZUDZAUEZESZUBZFUEZCEUFUNSZYLKUGUHZYLEHUITZUNZLUJZUKZHBEYIULZU
        OZBUEZYLTZUUAHUMTZUNZUPZUQUNZJYIUUCUNZUJZYRYFYKUBZUUHYMYNYQUUIUUHURYMYN
        UBZUUIYQUUHUUJUUIYQUUHURUUJUUIUBZYQYIYLTZYIUUCUNZHUSTZTZGYTYOUNZUJZUUHU
        UKYQUUPUUMHUTTZUNZLUJZUUQUUKYPUUSLUUKYEEYGVAZSZYJUKZUUJGYLYTVGZUJZYPUUS
        UJUUIUVCUUJUUIYEUVBYJYFYEYKYDYEVBZVCUUIUVBYHYFYHYJVDYDUVBYHVEYEYKEYGIVH
        VFVIYKYJYFYHYJVBZVJVKVJUUJUUIVRZUVEUUKRVLYGUURDCUUCYLGHEYIKYGVMZMNUUCVM
        ZUURVMZOVNVOVPUUKHVSSZUUMYGSZUUPYGSZUUQUUTVEYFUVLUUJYKYEUVLYDHVQVJVTUUK
        YEUULCSZYIYGSZUVMYFYEUUJYKUVFVTZUUJUUIUVOYMUUIUVOURYNYMECYLWAZUUIUVOYLC
        EWBYJUVRUVOURYFYHUVRYJUVOECYIYLWCWDWEWFVCWHZYKUVPUUJYFEYGYIWOWEZUULUUCD
        CYGHYIUVIMUVJNWGVOUUKYEYTWISZYTYGUDZUBZGCYTUFUNZSZGKUGUHZUBUVNUVQUUIUWC
        UUJUUIUWAUWBYDUWAYEYKEYSIWJVFZYHUWBYFYJEYGYSWKVTZWPVJUUKUWEUWFUUKYFYHYJ
        YMUWEUUJYFYKVDZYKYHUUJYFYHYJVRWEYKYJUUJYFUVGWEUUJYMUUIYMYNVRVCACDEFGHIJ
        KLMNOPQRWLWMZUUKYFYKUUJUWFUWIUUIYKUUJYFYKVBVJUVHACDEFGHIJKLMNOPQRWNVOWP
        YGDCGHYTWIKUVIMNOWQVOYGUURHUUNUUMUUPLUVIUVKPUUNVMZWRVOWSUUQUUPUUOUJZUUK
        UUHUUOUUPWTUUKUWLHBYTUUAGTZUUAUUCUNZUPZUQUNZUUOUJZUUHUUKUUPUWPUUOUUKYEG
        HXATZUCTZYTUFUNZSYTUVASZUUPUWPUJUVQUUKGUWDUWTUWJCUWSYTUFCDUCTUWSNDUWRUC
        MXBXCXEXDUUIUXAUUJUUIYTYGWIUWGUWHXFVJBGHYTUAXGVOVPUUKUWQUUHUUKUWPUUFUUO
        UUGUUKUWOUUEHUQUUKBYTUWNUUDUUKUUAYTSZUBZUWMUUBUUAUUCUXCUWMUUAUVDTZUUBUW
        MUXDUJUXCUUAGUVDRXHVLUXBUXDUUBUJUUKUUAYTYLXIVJXJXKXLXMUUKUUOUULDUSTZTZY
        IUUCUNUUGUUKYGUULUUCDCUXEUUNHYIUVIMUVJUWKNUXEVMUVQUVTUVSXOUUKUXFJYIUUCU
        XFJUJUUKJUXFQXPVLXKXJXNXQXRXSXRXTYAYBYCYB $.
    $}

    $d R g y $.  $d Z z $.
    $( Lemma 5 for ~ lindslinindsimp2 .  (Contributed by AV, 25-Apr-2019.)
       (Revised by AV, 30-Jul-2019.) $)
    lindslinindsimp2lem5 $p |- ( ( ( S e. V /\ M e. LMod )
                  /\ ( S C_ ( Base ` M ) /\ x e. S ) ) -> ( ( f e. ( B ^m S )
                     /\ ( f finSupp .0. /\ ( f ( linC ` M ) S ) = Z ) )
           -> ( A. y e. ( B \ { .0. } ) A. g e. ( B ^m ( S \ { x } ) )
                ( -. g finSupp .0.
                  \/ -. ( y ( .s ` M ) x ) = ( g ( linC ` M ) ( S \ { x } ) ) )
                                 -> ( f ` x ) = .0. ) ) ) $=
      ( cfv wceq wcel wa co vz cv clmod cbs wss cmap cfsupp wbr clinc cvsca csn
      wn cdif wo wral wi ax-1 2a1d cminusg wne wf elmapi ffvelcdm expcom adantl
      com12 syl adantr impcom biantrurd df-ne bicomi eldifsn cgrp lmodfgrp eqid
      3bitr4g grpinvnzcl sylan sylbid oveq1 eqeq1d notbid orbi2d ralbidv rspcva
      ex cres simpl simplrl simplrr lindslinindimp2lem2 syl13anc c0g id breq12d
      a1i eqeq2d orbi12d cvv breq2i biimpi fvexd fsuppres pm2.24d cmpt cgsu cpw
      csca simplr fveq2i eqtr2i oveq1i eleqtrrdi ssdifss wb difexg elpwg mpbird
      lincval syl3anc fvres oveq1d mpteq2dva oveq2d lindslinindimp2lem4 3eqtrrd
      w3a 3anass jaoi com23 mpcom syl5 expd syldc pm2.61i ) AUBZFUBZPZJQZEIRZHU
      CRZSZEHUDPZUEZYQERZSZSZYRCEUFTRZYRJUGUHZYREHUIPZTKQZSZSZGUBZJUGUHZULZBUBZ
      YQHUJPZTZUUOEYQUKZUMZUUKTZQZULZUNZGCUVBUFTZUOZBCJUKUMZUOZYTUPZUPUPYTUVKUU
      HUUNYTUVJUQURYTULZUUHUUNUVKUUHUUNSZUVLYSDUSPZPZUVIRZUVKUVMUVLYSUVIRZUVPUV
      MYSJUTZYSCRZUVRSUVLUVQUVMUVSUVRUUNUUHUVSUUIUUHUVSUPZUUMUUIECYRVAZUVTYRCEV
      BUUHUWAUVSUUGUWAUVSUPZUUCUUFUWBUUEUWAUUFUVSECYQYRVCVDVEVEVFVGVHVIVJUVRUVL
      YSJVKVLYSCJVMVQUVMUVQUVPUVMDVNRZUVQUVPUUHUWCUUNUUCUWCUUGUUBUWCUUADHLVOVEV
      HVHCDUVNYSJMNUVNVPVRVSWGVTUVMUVPUVJYTUVPUVJSUUQUVOYQUUSTZUVCQZULZUNZGUVGU
      OZUVMYTUVHUWHBUVOUVIUURUVOQZUVFUWGGUVGUWIUVEUWFUUQUWIUVDUWEUWIUUTUWDUVCUU
      RUVOYQUUSWAWBWCWDWEWFYRUVBWHZUVGRZUVMUWHYTUPUVMUUCUUEUUFUUIUWKUUHUUCUUNUU
      CUUGWIVHZUUCUUEUUFUUNWJUUCUUEUUFUUNWKUUNUUIUUHUUIUUMWIVEACDEFUWJHIUVOJKLM
      NOUVOVPZUWJVPZWLWMZUWKUWHUVMYTUWKUWHUVMYTUPZUWKUWHSUWJDWNPZUGUHZULZUWDUWJ
      UVBUUKTZQZULZUNZUWPUWGUXCGUWJUVGUUOUWJQZUUQUWSUWFUXBUXDUUPUWRUXDUUOUWJJUW
      QUGUXDWOJUWQQUXDNWQWPWCUXDUWEUXAUXDUVCUWTUWDUUOUWJUVBUUKWAWRWCWSWFUWSUWPU
      XBUVMUWSYTUVMUWRYTUVMYRWTUVBUWQUUNYRUWQUGUHZUUHUUMUXEUUIUUJUXEUULUUJUXEJU
      WQYRUGNXAXBVHVEVEUVMDWNXCXDXEVFUVMUXBYTUVMUXAYTUVMUWTHUAUVBUAUBZUWJPZUXFU
      USTZXFZXGTZHUAUVBUXFYRPZUXFUUSTZXFZXGTZUWDUVMUUBUWJHXIPZUDPZUVBUFTZRUVBUU
      DXHRZUWTUXJQUUHUUBUUNUUAUUBUUGXJVHUVMUWJUVGUXQUWOUXPCUVBUFCDUDPUXPMDUXOUD
      LXKXLXMXNUUHUXRUUNUUHUXRUVBUUDUEZUUGUXSUUCUUEUXSUUFEUUDUVAXOVHVEUUHUVBWTR
      ZUXRUXSXPUUCUXTUUGUUAUXTUUBEUVAIXQVHVHUVBUUDWTXRVGXSVHUAUWJHUVBUCXTYAUVMU
      XIUXMHXGUVMUAUVBUXHUXLUVMUXFUVBRZSUXGUXKUXFUUSUYAUXGUXKQUVMUXFUVBYRYBVEYC
      YDYEUVMUUCUUGUUIUUJUULYHZUXNUWDQUWLUUCUUGUUNXJUUNUYBUUHUUNUYBUYBUUNUUIUUJ
      UULYIVLXBVEAUACDEFUWJHIUVOJKLMNOUWMUWNYFYAYGXEVFYJVGWGYKYLYMYNYOYNYP $.

    $d B x $.  $d M x $.  $d R s $.  $d V f x $.  $d Z x $.
    $( Implication 2 for ~ lindslininds .  (Contributed by AV, 26-Apr-2019.)
       (Revised by AV, 30-Jul-2019.) $)
    lindslinindsimp2 $p |- ( ( S e. V /\ M e. LMod )
      -> ( ( S C_ ( Base ` M ) /\ A. s e. S A. y e. ( B \ { .0. } )
                   -. ( y ( .s ` M ) s ) e. ( ( LSpan ` M ) ` ( S \ { s } ) ) )
      -> ( S e. ~P ( Base ` M ) /\ A. f e. ( B ^m S ) ( ( f finSupp .0.
          /\ ( f ( linC ` M ) S ) = Z ) -> A. x e. S ( f ` x ) = .0. ) ) ) ) $=
      ( vg wcel wa wn wral clmod cbs cfv wss cv cvsca csn cdif clspn cpw cfsupp
      co wbr clinc wceq wi cmap simprl wb ad2antrr mpbird clinco simplr ssdifss
      elpwg wo adantl cvv difexg syl eqid lspeqlco eleq2d bicomd syl2anc notbid
      wrex lcoval eqcomi breq2i anbi1i rexbii anbi2i bitrdi ianor ralnex ralbii
      c0g bitr3i orbi2i bitri bitrd 2ralbidv wfal simpllr eldifi ssel2 lmodvscl
      ad2ant2lr syl3anc notnotd nbfal sylib orbi1d 2ralbidva r19.32v falim sneq
      difeq2d oveq2d oveq2 eqeq12d orbi2d raleqbidv rspcva lindslinindsimp2lem5
      ralbidv expr com14 ex pm2.43a imp expdimp ralrimdv ralrimiva expcom com12
      jaoi biimtrid sylbid impr jca ) EHQZGUAQZRZEGUBUCZUDZBUEZKUEZGUFUCZULZEYS
      UGZUHZGUIUCUCZQZSZBCIUGZUHZTKETZRZEYPUJZQZFUEZIUKUMUUMEGUNUCZULJUORZAUEZU
      UMUCIUOZAETUPZFCEUQULZTZRYOUUJRZUULUUTUVAUULYQYOYQUUIURYMUULYQUSYNUUJEYPH
      VEUTVAYOYQUUIUUTYOYQRZUUIUUAYPQZSZPUEZIUKUMZSZUUAUVEUUCUUNULZUOZSZVFZPCUU
      CUQULZTZVFZBUUHTKETZUUTUVBUUFUVNKBEUUHUVBUUFUUAGUUCVBULZQZSZUVNUVBUUEUVQU
      VBYNUUCUUKQZUUEUVQUSYMYNYQVCZUVBUVSUUCYPUDZYQUWAYOEYPUUBVDVGUVBUUCVHQZUVS
      UWAUSYMUWBYNYQEUUBHVIUTUUCYPVHVEVJVAZYNUVSRZUVQUUEUWDUVPUUDUUAYPGUUCYPVKZ
      VLVMVNVOVPUVBUVRUVCUVFUVIRZPUVLVQZRZSZUVNUVBUVQUWHUVBYNUVSUVQUWHUSUVTUWCU
      WDUVQUVCUVEDWHUCZUKUMZUVIRZPUVLVQZRUWHYPUUACDGUUCUAPUWELMVRUWMUWGUVCUWLUW
      FPUVLUWKUVFUVIUWJIUVEUKIUWJNVSVTWAWBWCWDVOVPUWIUVDUWGSZVFUVNUVCUWGWEUWNUV
      MUVDUWNUWFSZPUVLTUVMUWFPUVLWFUWOUVKPUVLUVFUVIWEWGWIWJWKWDWLWMUVBUVOWNUVMV
      FZBUUHTZKETZUUTUVBUVNUWPKBEUUHUVBYSEQZYRUUHQZRZRZUVDWNUVMUXBUVDSUVDWNUSUX
      BUVCUXBYNYRCQZYSYPQZUVCYMYNYQUXAWOUXAUXCUVBUWTUXCUWSYRCUUGWPVGVGYQUWSUXDY
      OUWTEYPYSWQWSYRYTDCYPGYSUWELYTVKMWRWTXAUVDXBXCXDXEUWRWNUVMBUUHTZKETZVFZUV
      BUUTUWRWNUXEVFZKETUXGUWQUXHKEWNUVMBUUHXFWGWNUXEKEXFWKUXGUVBUUTWNUVBUUTUPZ
      UXFUXIXGUVBUXFUUTUVBUXFRZUURFUUSUXJUUMUUSQZRUUOUUQAEUXJUXKUUOUUPEQZUUQUPZ
      UVBUXFUXKUUORZUXMUPUXLUXFUXNUVBUUQUXFUXLUXNUVBUUQUPUPZUXLUXFUXLUXOUPZUXLU
      XFRUVGYRUUPYTULZUVEEUUPUGZUHZUUNULZUOZSZVFZPCUXSUQULZTZBUUHTZUXPUXEUYFKUU
      PEYSUUPUOZUVMUYEBUUHUYGUVKUYCPUVLUYDUYGUUCUXSCUQUYGUUBUXREYSUUPXHXIZXJUYG
      UVJUYBUVGUYGUVIUYAUYGUUAUXQUVHUXTYSUUPYRYTXKUYGUUCUXSUVEUUNUYHXJXLVPXMXNX
      QXOUVBUXLUXNUYFUUQYOYQUXLUXNUYFUUQUPUPABCDEFPGHIJLMNOXPXRXSVJXTYAXSYBYCYD
      YEYFYHYGYIYJYJYKYLXT $.
  $}

  ${
    $d M f g s x $.  $d S f g s x $.  $d V f g s x $.
    $( Equivalence of definitions ~ df-linds and ~ df-lininds for (linear)
       independence for (left) modules.  (Contributed by AV, 26-Apr-2019.)
       (Proof shortened by AV, 30-Jul-2019.) $)
    lindslininds $p |- ( ( S e. V /\ M e. LMod )
                        -> ( S linIndS M <-> S e. ( LIndS ` M ) ) ) $=
      ( vf vx vg vs wcel clmod wa cbs cfv cv c0g wbr co wceq wral csn eqid csca
      cpw cfsupp clinc wi cmap wss cvsca clspn clininds clinds lindslinindsimp1
      cdif wn lindslinindsimp2 impbid islininds wb islinds2 adantl 3bitr4d ) AC
      HZBIHZJZABKLZUBHDMZBUALZNLZUCOVFABUDLPBNLZQJEMVFLVHQEARUEDVGKLZAUFPRJZAVE
      UGFMGMZBUHLZPAVLSUMBUILZLHUNFVJVHSUMRGARJZABUJOABUKLHZVDVKVOEFVJVGADBCVHV
      IGVGTZVJTZVHTZVITZULEFVJVGADBCVHVIGVQVRVSVTUOUPEVEVGADVJBCIVHVIVETZVTVQVR
      VSUQVCVPVOURVBGVEVGVMFAVNVJBIVHWAVMTVNTVQVRVSUSUTVA $.
  $}

  ${
    $d M f x $.
    $( The empty set is always a linearly independent subset.  (Contributed by
       AV, 13-Apr-2019.)  (Revised by AV, 27-Apr-2019.)  (Proof shortened by
       AV, 30-Jul-2019.) $)
    linds0 $p |- ( M e. V -> (/) linIndS M ) $=
      ( vf vx wcel c0 wbr cbs cfv cv c0g cfsupp co wceq wa wral wi cvv wb eqid
      clininds cpw csca clinc cmap csn ral0 2a1i 0ex breq1 oveq1 eqeq1d anbi12d
      fveq1 ralbidv imbi12d ralsng mp1i mpbird c1o fvex map0e eqtrdi raleqtrrdv
      df1o2 0elpw jctil islininds mpan ) ABEZFAUAGZFAHIZUBEZCJZAUCIZKIZLGZVNFAU
      DIZMZAKIZNZOZDJZVNIZVPNZDFPZQZCVOHIZFUEMZPZOZVJWJVMVJWGCFUFZWIVJWGCWLPZFV
      PLGZFFVRMZVTNZOZWCFIZVPNZDFPZQZWTVJWQWSDUGUHFREZWMXASVJUIWGXACFRVNFNZWBWQ
      WFWTXCVQWNWAWPVNFVPLUJXCVSWOVTVNFFVRUKULUMXCWEWSDFXCWDWRVPWCVNFUNULUOUPUQ
      URUSVJWIUTWLWHREWIUTNVJVOHVAWHRVBURVEVCVDVLVFVGXBVJVKWKSUIDVLVOFCWHARBVPV
      TVLTVTTVOTWHTVPTVHVIUS $.
  $}

  ${
    $d M f s x y $.  $d S f s x y $.
    $( A set containing the zero element of a module is always linearly
       dependent, if the underlying ring has at least two elements.
       (Contributed by AV, 13-Apr-2019.)  (Revised by AV, 27-Apr-2019.)  (Proof
       shortened by AV, 30-Jul-2019.) $)
    el0ldep $p |- ( ( ( M e. LMod /\ 1 < ( # ` ( Base ` ( Scalar ` M ) ) ) )
               /\ S e. ~P ( Base ` M ) /\ ( 0g ` M ) e. S ) -> S linDepS M ) $=
      ( vf vx vs vy clmod wcel cfv cbs wbr w3a cv cfsupp co wceq wne wrex eqid
      wb c1 csca chash clt cpw c0g clindeps clinc cmap cur cif cmpt eqeq1 ifbid
      wa cbvmptv mptcfsupp 3adant1r simp1l simp2 linc0scn0 syl2anc simp3 neeq1d
      fveq2 adantl cvv iftrue fvmptd3 crg lmodring anim1i 3ad2ant1 ring1ne0 syl
      fvexd eqnetrd rspcedvd wf lmod1cl ifcld adantr fmpttd elmapd mpbird breq1
      lmod0cl oveq1 eqeq1d fveq1 rexbidv 3anbi123d rspcedv mp3and islindeps ) B
      GHZUABUBIZJIZUCIUDKZUOZABJIZUEZHZBUFIZAHZLZABUGKZCMZWQUFIZNKZXHABUHIZOZXD
      PZDMZXHIZXIQZDARZLZCWRAUIOZRZXFEAEMZXDPZWQUJIZXIUKZULZXINKZYEAXKOZXDPZXNY
      EIZXIQZDARZXTWPXCXEYFWSFXAWQYCYEBAXDXIXASZWQSZXISZYCSZEFAYDFMZXDPZYCXIUKY
      AYPPYBYQYCXIYAYPXDUMUNUPUQURXFWPXCYHWPWSXCXEUSZWTXCXEUTZEXAWQYCYEBAXIXDYL
      YMYNYOXDSZYESZVAVBXFYJXDYEIZXIQZDXDAWTXCXEVCZXNXDPZYJUUCTXFUUEYIUUBXIXNXD
      YEVEVDVFXFUUBYCXIXFEXDYDYCAYEVGUUAYBYCXIVHUUDXFWQUJVPVIXFWQVJHZWSUOZYCXIQ
      WTXCUUGXEWPUUFWSWQBYMVKVLVMWRWQYCXIWRSZYOYNVNVOVQVRXFXRYFYHYKLZCYEXSXFYEX
      SHAWRYEVSXFEAYDWRXFYDWRHZYAAHWTXCUUJXEWPUUJWSWPYBYCXIWRYCWQWRBYMUUHYOVTWQ
      WRBXIYMUUHYNWGWAWBVMWBWCXFWRAYEVGXBXFWQJVPYSWDWEXHYEPZXRUUITXFUUKXJYFXMYH
      XQYKXHYEXINWFUUKXLYGXDXHYEAXKWHWIUUKXPYJDAUUKXOYIXIXNXHYEWJVDWKWLVFWMWNXF
      WPXCXGXTTYRYSDXAWQACWRBGXIXDYLYTYMUUHYNWOVBWE $.
  $}

  $( A set containing the zero element of a module over a nonzero ring is
     always linearly dependent.  (Contributed by AV, 14-Apr-2019.)  (Revised by
     AV, 27-Apr-2019.) $)
  el0ldepsnzr $p |- ( ( ( M e. LMod /\ ( Scalar ` M ) e. NzRing )
               /\ S e. ~P ( Base ` M ) /\ ( 0g ` M ) e. S ) -> S linDepS M ) $=
    ( clmod wcel c1 csca cfv cbs chash clt wbr cpw cnzr c0g clindeps w3a simp1l
    wa crg eqid isnzr2hash simprbi adantl 3ad2ant1 jca el0ldep syld3an1 ) BCDZE
    BFGZHGZIGJKZRABHGLDZUHUIMDZRZBNGADZABOKUNULUOPUHUKUHUMULUOQUNULUKUOUMUKUHUM
    UISDUKUJUIUJTUAUBUCUDUEABUFUG $.

  ${
    $d B f v x $.  $d E f v x $.  $d M f v x $.  $d R f v x $.  $d S f v x $.
    lindsrng01.b $e |- B = ( Base ` M ) $.
    lindsrng01.r $e |- R = ( Scalar ` M ) $.
    lindsrng01.e $e |- E = ( Base ` R ) $.
    $( Any subset of a module is always linearly independent if the underlying
       ring has at most one element.  Since the underlying ring cannot be the
       empty set (see ~ lmodsn0 ), this means that the underlying ring has only
       one element, so it is a zero ring.  (Contributed by AV, 14-Apr-2019.)
       (Revised by AV, 27-Apr-2019.) $)
    lindsrng01 $p |- ( ( M e. LMod /\ ( ( # ` E ) = 0 \/ ( # ` E ) = 1 )
                         /\ S e. ~P B ) -> S linIndS M ) $=
      ( vf vv vx wcel cfv wceq wi wa cvv wb adantr c0g clmod chash cc0 clininds
      c1 wo cpw wbr wne lmodsn0 cbs fvexi hasheq0 ax-mp eqneqall com12 biimtrid
      c0 syl csn crg lmodring eqid 0ring sylan cv cfsupp clinc wral cmap adantl
      co simpr wf snex jctil elmapg cmpt cxp fvex fconst2 fconstmpt bitri eqidd
      eqeq2i fvexd fvmptd ralrimiva breq1 oveq1 eqeq1d anbi12d fveq1 syl5ibrcom
      a1d ralbidv imbi12d sylbid ralrimiv raleqdv mpbird simpl ancomd islininds
      mpbir2and mpancom expcom jaoi expd 3imp ) EUALZDUBMZUCNZXLUENZUFZCAUGZLZC
      EUDUHZXOXKXQXROXOXKXQXRXMXKXQPZXROXNXSXMXRXKXMXROZXQXKDURUIZXTDBEGHUJXMDU
      RNZYAXRDQLXMYBRDBUKHULDQUMUNYBYAXRXRDURUOUPUQUSSUPXSXNXRDBTMZUTZNZXSXNPZX
      RXSBVALZXNYEXKYGXQBEGVBSDBYCHYCVCZVDVEYEYFPZXRXQIVFZYCVGUHZYJCEVHMZVLZETM
      ZNZPZJVFZYJMZYCNZJCVIZOZIDCVJVLZVIZYFXQYEXSXQXNXKXQVMSZVKYIUUCUUAIYDCVJVL
      ZVIZYIUUAIUUEYIYJUUELZCYDYJVNZUUAYIYDQLZXQPZUUGUUHRYFUUJYEYFXQUUIUUDYCVOV
      PVKYDCYJQXPVQUSUUHYJKCYCVRZNZYIUUAUUHYJCYDVSZNUULCYCYJBTVTWAUUMUUKYJKCYCW
      BWEWCYIUUAUULUUKYCVGUHZUUKCYLVLZYNNZPZYQUUKMZYCNZJCVIZOYIUUTUUQYIUUSJCYIY
      QCLZPZKYQYCYCCUUKQUVBUUKWDUVBKVFYQNPYCWDYIUVAVMUVBBTWFWGWHWOUULYPUUQYTUUT
      UULYKUUNYOUUPYJUUKYCVGWIUULYMUUOYNYJUUKCYLWJWKWLUULYSUUSJCUULYRUURYCYQYJU
      UKWMWKWPWQWNUQWRWSYEUUCUUFRYFYEUUAIUUBUUEDYDCVJWJWTSXAYIXQXKPZXRXQUUCPRYF
      UVCYEYFXKXQXSXNXBXCVKJABCIDEXPUAYCYNFYNVCGHYHXDUSXEXFXGXHXIUPXJ $.
  $}

  $( Any subset of a module over a zero ring is always linearly independent.
     (Contributed by AV, 27-Apr-2019.) $)
  lindszr $p |- ( ( M e. LMod /\ -. ( Scalar ` M ) e. NzRing
                    /\ S e. ~P ( Base ` M ) ) -> S linIndS M ) $=
    ( clmod wcel csca cfv cbs chash cc0 wceq c1 wo cnzr wn cpw clininds wbr w3a
    simp2 eqid crg wb lmodring 3ad2ant1 0ringnnzr syl olcd lindsrng01 syld3an2
    mpbird ) BCDZBEFZGFZHFZIJZUNKJZLULMDNZABGFZODZABPQUKUQUSRZUPUOUTUPUQUKUQUSS
    UTULUADZUPUQUBUKUQVAUSULBULTZUCUDULUEUFUJUGURULAUMBURTVBUMTUHUI $.

  ${
    $d B f s $.  $d M f s x y $.  $d S f s $.  $d X f s x y $.  $d Z f s $.
    $d .x. f s $.  $d .0. f s $.
    snlindsntor.b $e |- B = ( Base ` M ) $.
    snlindsntor.r $e |- R = ( Scalar ` M ) $.
    snlindsntor.s $e |- S = ( Base ` R ) $.
    snlindsntor.0 $e |- .0. = ( 0g ` R ) $.
    snlindsntor.z $e |- Z = ( 0g ` M ) $.
    snlindsntor.t $e |- .x. = ( .s ` M ) $.
    $( Lemma for ~ snlindsntor .  (Contributed by AV, 15-Apr-2019.) $)
    snlindsntorlem $p |- ( ( M e. LMod /\ X e. B )
                     -> ( A. f e. ( S ^m { X } ) ( ( f ( linC ` M ) { X } ) = Z
                                                   -> ( f ` X ) = .0. )
                          -> A. s e. S ( ( s .x. X ) = Z -> s = .0. ) ) ) $=
      ( wcel co wceq cvv clmod wa cv csn clinc cfv wi cmap wral cop wf eqidd wb
      fsng adantll mpbird snssi adantl fssd fvexi snex pm3.2i elmapg mp1i oveq1
      wss cbs eqeq1d fveq1 imbi12d lincvalsng 3expa sylan9bbr rspcdv ralrimdva
      fvsng ) FUAQZGAQZUBZEUCZGUDZFUEUFZRZISZGVTUFZHSZUGZECWAUHRZUIJUCZGDRZISZW
      IHSZUGZJCVSWICQZUBZWGWMEGWIUJUDZWHWOWPWHQZWACWPUKZWOWAWIUDZCWPWOWAWSWPUKZ
      WPWPSZWOWPULVRWNWTXAUMVQGWIACWPUNUOUPWNWSCVFVSWICUQURUSCTQZWATQZUBWQWRUMW
      OXBXCCBVGMUTGVAVBCWAWPTTVCVDUPVTWPSZWGWPWAWBRZISZGWPUFZHSZUGWOWMXDWDXFWFX
      HXDWCXEIVTWPWAWBVEVHXDWEXGHGVTWPVIVHVJWOXFWKXHWLWOXEWJIVQVRWNXEWJSACBDFGW
      IKLMPVKVLVHWOXGWIHVRWNXGWISVQGWIACVPUOVHVJVMVNVO $.

    $d B x $.  $d .0. y $.
    $( A singleton is linearly independent iff it does not contain a torsion
       element.  According to Wikipedia ("Torsion (algebra)", 15-Apr-2019,
       ~ https://en.wikipedia.org/wiki/Torsion_(algebra) ):  "An element m of a
       module M over a ring R is called a _torsion element_ of the module if
       there exists a regular element r of the ring (an element that is neither
       a left nor a right zero divisor) that annihilates m, i.e.,
       ` ( r .x. m ) = 0 ` .  In an integral domain (a commutative ring without
       zero divisors), every nonzero element is regular, so a torsion element
       of a module over an integral domain is one annihilated by a nonzero
       element of the integral domain."  Analogously, the definition in [Lang]
       p. 147 states that "An element x of [a module] E [over a ring R] is
       called a _torsion element_ if there exists ` a e. R ` , ` a =/= 0 ` ,
       such that ` a .x. x = 0 ` .  This definition includes the zero element
       of the module.  Some authors, however, exclude the zero element from the
       definition of torsion elements.  (Contributed by AV, 14-Apr-2019.)
       (Revised by AV, 27-Apr-2019.) $)
    snlindsntor $p |- ( ( M e. LMod /\ X e. B )
                          -> ( A. s e. ( S \ { .0. } ) ( s .x. X ) =/= Z
                               <-> { X } linIndS M ) ) $=
      ( vf wcel wa wceq wi vy vx clmod cv co wne csn cdif wral cpw cfsupp clinc
      wbr cfv cmap clininds wn df-ne ralbii raldifsni bitri cvsca cmpt cgsu cbs
      simpl adantr fveq2i oveq1i eleq2i bilani snelpwi ad3antlr lincval syl3anc
      csca eqtri eleq2s eqeq1d anbi2d cmnd lmodgrp grpmndd ad3antrrr simpllr wf
      elmapi adantl ffvelcdm sylan2 simprlr eqid lmodvscl expcom syl5com impcom
      snidg fveq2 id oveq12d gsumsn oveqi eqeq1i oveq1 imbi12d rspcva biimtrrid
      eqeq1 ex syl56 com23 sylbid adantld ralrimiva impexp cvv cfn snfi a1i c0g
      imp31 fvexi fdmfifsupp pm2.27 syl biimtrid ralimdva snlindsntorlem impbid
      syld wb fveqeq2 ralsng bicomd imbi2d ralbidv biantrurd 3bitrd bitrid snex
      islininds sylancr bitr4d ) EUCQZFAQZRZIUDZFDUEZHUFZICGUGUHZUIZFUGZAUJQZPU
      DZGUKUMZUUNUULEULUNUEZHSZRZUAUDZUUNUNGSZUAUULUIZTZPCUULUOUEZUIZRZUULEUPUM
      ZUUKUUHHSZUUGGSZTZICUIZUUFUVEUUKUVGUQZIUUJUIUVJUUIUVKIUUJUUHHURUSUVGICGUT
      VAUUFUVJUURFUUNUNZGSZTZPUVCUIZUVDUVEUUFUVJUVOUUFUVJUVOUUFUVJRZUVNPUVCUVPU
      UNUVCQZRZUURUUOEUBUULUBUDZUUNUNZUVSEVBUNZUEZVCVDUEZHSZRUVMUVRUUQUWDUUOUVR
      UUPUWCHUVRUUDUUNEVPUNZVEUNZUULUOUEZQZUULEVEUNZUJQZUUPUWCSUVPUUDUVQUUFUUDU
      VJUUDUUEVFZVGZVGUVQUWHUVPUVCUWGUUNCUWFUULUOCBVEUNUWFLBUWEVEKVHVQVIVJVKUUE
      UWJUUDUVJUVQUWJFUWIAFUWIVLJVRVMUBUUNEUULUCVNVOVSVTUVRUWDUVMUUOUVRUWDUVLFU
      WAUEZHSZUVMUVRUWCUWMHUVREWAQZUUEUWMAQZUWCUWMSUUDUWOUUEUVJUVQUUDEEWBWCWDUU
      DUUEUVJUVQWEUVQUVPUWPUVQUULCUUNWFZUVPUWPUUNCUULWGZUWQUVPUWPUWQUVPRUUDUVLC
      QZUUEUWPUVPUUDUWQUWLWHUVPUWQFUULQZUWSUUFUWTUVJUUEUWTUUDFAWQZWHVGUULCFUUNW
      IZWJUWQUUDUUEUVJWKUVLUWABCAEFJKUWAWLLWMVOWNWOWPUWBAUWMUBEFAJUVSFSZUVTUVLU
      VSFUWAUVSFUUNWRUXCWSWTXAVOVSUUFUVJUVQUWNUVMTZUUFUVQUVJUXDUVQUWQUUFUWSUVJU
      XDTUWRUUEUWQUWSTUUDUWQUUEUWSUUEUWQUWTUWSUXAUXBWJWNWHUWSUVJUXDUWNUVLFDUEZH
      SZUWSUVJRUVMUXEUWMHDUWAUVLFOXBXCUVIUXFUVMTIUVLCUUGUVLSZUVGUXFUVHUVMUXGUUH
      UXEHUUGUVLFDXDVSUUGUVLGXHXEXFXGXIXJXKYAXLXMXLXNXIUUFUVOUUQUVMTZPUVCUIUVJU
      UFUVNUXHPUVCUVNUUOUXHTZUUFUVQRZUXHUUOUUQUVMXOUXJUUOUXIUXHTUXJUULCUUNXPGUV
      QUWQUUFUWRWHUULXQQUXJFXRXSGXPQUXJGBXTMYBXSYCUUOUXHYDYEYFYGABCDPEFGHIJKLMN
      OYHYJYIUUFUVNUVBPUVCUUFUVMUVAUURUUFUVAUVMUUEUVAUVMYKUUDUUTUVMUAFAUUSFGUUN
      YLYMWHYNYOYPUUFUUMUVDUUEUUMUUDFAVLWHYQYRYSUUFUULXPQUUDUVFUVEYKFYTUWKUAABU
      ULPCEXPUCGHJNKLMUUAUUBUUC $.

    ${
      ldepsprlem.1 $e |- .1. = ( 1r ` R ) $.
      ldepsprlem.n $e |- N = ( invg ` R ) $.
      $( Lemma for ~ ldepspr .  (Contributed by AV, 16-Apr-2019.) $)
      ldepsprlem $p |- ( ( M e. LMod /\ ( X e. B /\ Y e. B /\ A e. S ) )
                          -> ( X = ( A .x. Y )
                 -> ( ( .1. .x. X ) ( +g ` M ) ( ( N ` A ) .x. Y ) ) = Z ) ) $=
        ( clmod wcel w3a wa co wceq cfv cplusg oveq2 oveq1d cmulr simpl lmod1cl
        adantr simpr3 simpr2 eqid lmodvsass syl13anc eqcomd crg lmodring syl2an
        simp3 ringlidm cgrp lmodfgrp grpinvcl lmodvsdir grprinv 3ad2antr2 eqtrd
        lmod0vs 3eqtr2d sylan9eqr ex ) GUAUBZIBUBZJBUBZADUBZUCZUDZIAJEUEZUFZFIE
        UEZAHUGZJEUEZGUHUGZUEZLUFWDWBWIFWCEUEZWGWHUEZLWDWEWJWGWHIWCFEUIUJWBWKFA
        CUKUGZUEZJEUEZWGWHUEZLWBWJWNWGWHWBWNWJWBVQFDUBZVTVSWNWJUFVQWAULZVQWPWAF
        CDGNOSUMUNVQVRVSVTUOZVQVRVSVTUPZFAEWLCDBGJMNROWLUQZURUSUTUJWBWOWCWGWHUE
        ZAWFCUHUGZUEZJEUEZLWBWNWCWGWHWBWMAJEVQCVAUBVTWMAUFWACGNVBVRVSVTVDZDCWLF
        AOWTSVEVCUJUJWBVQVTWFDUBZVSXDXAUFWQWRVQCVFUBZVTXFWACGNVGZXEDCHAOTVHVCWS
        WHXBAWFECDBGJMWHUQNROXBUQZVIUSWBXDKJEUEZLWBXCKJEVQXGVTXCKUFWAXHXEDXBCHA
        KOXIPTVJVCUJVQVRVSXJLUFVTECKBGJLMNRPQVMVKVLVNVLVOVP $.
    $}

    $d A f v $.  $d M v $.  $d R f v $.  $d X v $.  $d Y f v $.  $d .0. v $.
    $( If a vector is a scalar multiple of another vector, the (unordered pair
       containing the) two vectors are linearly dependent.  (Contributed by AV,
       16-Apr-2019.)  (Revised by AV, 27-Apr-2019.)  (Proof shortened by AV,
       30-Jul-2019.) $)
    ldepspr $p |- ( ( M e. LMod /\ ( X e. B /\ Y e. B /\ X =/= Y ) )
                     -> ( ( A e. S /\ X = ( A .x. Y ) )
                          -> { X , Y } linDepS M ) ) $=
      ( wcel wa wceq wi vf vv clmod wne w3a co cpr clindeps wbr cv cfsupp clinc
      cfv wrex cmap cur cop cminusg cvv wf 3simpa ad2antlr fvex pm3.2i a1i fprg
      simp3 syl3anc cfn prfi fvexi fdmfifsupp cplusg anim2i adantr eqid lmod1cl
      c0g simp1 anim12ci simp2 cgrp lmodfgrp simpl grpinvcl lincvalpr syl112anc
      syl2an simpll adantl 3jca jca simprr ldepsprlem sylc eqtrd wo wn lmodring
      crg eqcom csn 01eq0ring sneq eqeq2d eleq2 elsni anim1i ancomd lmodvs1 syl
      oveq1 eqneqall com12 3ad2ant3 sylbid ex com3r biimtrdi com23 mpd biimtrid
      impd com25 mpcom imp31 orc pm2.61d1 eqeq2i necon3abii orbi1i sylibr fvexd
      fvpr1g neeq1d fvpr2g orbi12d mpbird wb fveq2 rexprg cbs mapprop syl221anc
      jctir breq1 eqeq1d fveq1 rexbidv 3anbi123d rspcedv mp3and prelpwi 3adant3
      cpw islindeps syl2anc ) FUCQZGBQZHBQZGHUDZUEZRZADQZGAHEUFZSZRZGHUGZFUHUIZ
      UVCUVGRZUVIUAUJZIUKUIZUVKUVHFULUMZUFZJSZUBUJZUVKUMZIUDZUBUVHUNZUEZUADUVHU
      OUFZUNZUVJGCUPUMZUQHACURUMZUMZUQUGZIUKUIZUWFUVHUVMUFZJSZUVPUWFUMZIUDZUBUV
      HUNZUWBUVJUVHUWCUWEUGZUWFUSIUVJUUSUUTRZUWCUSQZUWEUSQZRZUVAUVHUWMUWFUTUVBU
      WNUURUVGUUSUUTUVAVAVBZUWQUVJUWOUWPCUPVCAUWDVCVDVEUVBUVAUURUVGUUSUUTUVAVGZ
      VBZGHUWCUWEBBUSUSVFVHUVHVIQUVJGHVJVEIUSQUVJICVRNVKVEVLUVJUWHUWCGEUFUWEHEU
      FFVMUMZUFZJUVJUURUVARZUUSUWCDQZRZUUTUWEDQZUWHUXBSUVCUXCUVGUVBUVAUURUWSVNV
      OUVCUXEUVGUURUXDUVBUUSUWCCDFLMUWCVPZVQZUUSUUTUVAVSZVTVOUVBUUTUURUVGUUSUUT
      UVAWAZVBZUVCCWBQZUVDUXFUVGUURUXLUVBCFLWCVOUVDUVFWDZDCUWDAMUWDVPZWEWHZBUXA
      DCEUWFFGHUWCUWEKLMPUXAVPUWFVPZWFWGUVJUURUUSUUTUVDUEZRUVFUXBJSUVJUURUXQUUR
      UVBUVGWIZUVJUUSUUTUVDUVBUUSUURUVGUXIVBZUXKUVGUVDUVCUXMWJWKWLUVCUVDUVFWMAB
      CDEUWCFUWDGHIJKLMNOPUXGUXNWNWOWPUVJUWLGUWFUMZIUDZHUWFUMZIUDZWQZUVJUYDUWCI
      UDZUWEIUDZWQZUVJUWCCVRUMZSZWRZUYFWQZUYGUVJUYIUYKUURUVBUVGUYIUYKTZCWTQZUUR
      UVBUVGUYLTTCFLWSUYMUYIUVBUVGUURUYKUYIUYHUWCSZUYMUVBUVGUURUYKTZTTZUWCUYHXA
      UYMUYNUYPUYMUYNRDUYHXBZSZUYPDCUWCUYHMUYHVPUXGXCUYNUYRUYPTUYMUYNUYRDUWCXBZ
      SZUYPUYNUYQUYSDUYHUWCXDXEUYTUVGUVBUYOUYTUVDUVFUVBUYOTZUYTUVDAUYSQZUVFVUAT
      ZDUYSAXFVUBAUWCSZVUCAUWCXGVUDUVFGUWCHEUFZSZVUAVUDUVEVUEGAUWCHEXLXEUVBUURV
      UFUYKUVBUURVUFUYKTUVBUURRZVUFGHSZUYKVUGVUEHGVUGUURUUTRVUEHSVUGUUTUURUVBUU
      TUURUXJXHXIEUWCCBFHKLPUXGXJXKXEUVBVUHUYKTZUURUVAUUSVUIUUTVUHUVAUYKUYKGHXM
      XNXOVOXPXQXRXSXKXSYCXTXSWJYAXQYBYDYEYFUYJUYFYGYHUYEUYJUYFUYIUWCIIUYHUWCNY
      IYJYKYLUVJUYAUYEUYCUYFUVJUXTUWCIUVJUUSUWOUVAUXTUWCSUXSUVJCUPYMUWTGHUWCUWE
      BUSYNVHYOUVJUYBUWEIUVJUUTUWPUVAUYBUWESUXKUVJAUWDYMUWTGHUWCUWEBUSYPVHYOYQY
      RUVJUWNUWLUYDYSUWRUWKUYAUYCUBGHBBUVPGSUWJUXTIUVPGUWFYTYOUVPHSUWJUYBIUVPHU
      WFYTYOUUAXKYRUVJUVTUWGUWIUWLUEZUAUWFUWAUVJUUSUXDUUTUXFUVADUSQZRUWFUWAQUXS
      UVCUXDUVGUURUXDUVBUXHVOVOUXKUXOUVJUVAVUKUWTDCUUBMVKUUEUWCUWEDUWFBUSGHUXPU
      UCUUDUVKUWFSZUVTVUJYSUVJVULUVLUWGUVOUWIUVSUWLUVKUWFIUKUUFVULUVNUWHJUVKUWF
      UVHUVMXLUUGVULUVRUWKUBUVHVULUVQUWJIUVPUVKUWFUUHYOUUIUUJWJUUKUULUVJUURUVHB
      UUOQZUVIUWBYSUXRUVBVUMUURUVGUUSUUTVUMUVAGHBUUMUUNVBUBBCUVHUADFUCIJKOLMNUU
      PUUQYRXQ $.
  $}

  ${
    lincresunit3lem3.b $e |- B = ( Base ` M ) $.
    lincresunit3lem3.r $e |- R = ( Scalar ` M ) $.
    lincresunit3lem3.e $e |- E = ( Base ` R ) $.
    lincresunit3lem3.u $e |- U = ( Unit ` R ) $.
    lincresunit3lem3.n $e |- N = ( invg ` R ) $.
    lincresunit3lem3.t $e |- .x. = ( .s ` M ) $.
    $( Lemma 3 for ~ lincresunit3 .  (Contributed by AV, 18-May-2019.) $)
    lincresunit3lem3 $p |- ( ( ( M e. LMod /\ X e. B /\ Y e. B ) /\ A e. U )
                -> ( ( ( N ` A ) .x. X ) = ( ( N ` A ) .x. Y ) <-> X = Y ) ) $=
      ( wcel co wceq adantr clmod w3a wa cfv cinvr cmulr cur 3simpa lmodvs1 syl
      eqid crg lmodring 3ad2ant1 unitnegcl 3ad2antl1 jca unitlinv eqcomd oveq1d
      sylan eqtr3d simpl1 ringinvcl cgrp lmodfgrp unitcl grpinvcl syl2an simpl2
      3jca lmodvsass oveq2 adantl simpl3 3eqtrd 3simpb ex impbid1 ) GUAQZIBQZJB
      QZUBZAEQZUCZAHUDZIDRZWFJDRZSZIJSZWEWIWJWEWIUCZIWFCUEUDZUDZWFCUFUDZRZIDRZC
      UGUDZJDRZJWEIWPSWIWEWQIDRZIWPWEVTWAUCZWSISWCWTWDVTWAWBUHTDWQCBGIKLPWQUKZU
      IUJWEWQWOIDWEWOWQWECULQZWFEQZUCZWOWQSZWEXBXCWCXBWDVTWAXBWBCGLUMZUNTVTWAWD
      XCWBVTXBWDXCXFCEHANOUOVAUPUQZCWNEWQWLWFNWLUKZWNUKZXAURZUJUSUTVBTWKWPWMWGD
      RZWMWHDRZWRWKVTWMFQZWFFQZWAUBZUCZWPXKSWEXPWIWEVTXOVTWAWBWDVCZWEXMXNWAWEXD
      XMXGFCEWLWFNXHMVDUJZWCCVEQZAFQXNWDVTWAXSWBCGLVFUNFCEAMNVGFCHAMOVHVIZVTWAW
      BWDVJVKUQTWMWFDWNCFBGIKLPMXIVLUJWIXKXLSWEWGWHWMDVMVNWKWOJDRZXLWRWKVTXMXNW
      BUBZUCYAXLSWKVTYBWEVTWIXQTWEYBWIWEXMXNWBXRXTVTWAWBWDVOVKTUQWMWFDWNCFBGJKL
      PMXIVLUJWKWOWQJDWKXDXEWEXDWIXGTXJUJUTVBVPWKVTWBUCZWRJSWEYCWIWCYCWDVTWAWBV
      QTTDWQCBGJKLPXAUIUJVPVRIJWFDVMVS $.
  $}

  ${
    lincresunit.b $e |- B = ( Base ` M ) $.
    lincresunit.r $e |- R = ( Scalar ` M ) $.
    lincresunit.e $e |- E = ( Base ` R ) $.
    lincresunit.u $e |- U = ( Unit ` R ) $.
    lincresunit.0 $e |- .0. = ( 0g ` R ) $.
    lincresunit.z $e |- Z = ( 0g ` M ) $.
    lincresunit.n $e |- N = ( invg ` R ) $.
    lincresunit.i $e |- I = ( invr ` R ) $.
    lincresunit.t $e |- .x. = ( .r ` R ) $.
    lincresunit.g $e |- G = ( s e. ( S \ { X } )
        |-> ( ( I ` ( N ` ( F ` X ) ) ) .x. ( F ` s ) ) ) $.
    $( Lemma 1 for properties of a specially modified restriction of a linear
       combination containing a unit as scalar.  (Contributed by AV,
       18-May-2019.) $)
    lincresunitlem1 $p |- ( ( ( S e. ~P B /\ M e. LMod /\ X e. S )
                              /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U ) )
                            -> ( I ` ( N ` ( F ` X ) ) ) e. E ) $=
      ( cpw wcel clmod w3a cmap co cfv wa crg lmodring 3ad2ant2 simpr unitnegcl
      adantr syl2an ringinvcl syl2anc ) CAUFUGZJUHUGZLCUGZUIZGFCUJUKUGZLGULZEUG
      ZUMZUMBUNUGZVHKULZEUGZVLIULFUGVFVKVJVDVCVKVEBJQUOUPZUSVFVKVIVMVJVNVGVIUQB
      EKVHSUBURUTFBEIVLSUCRVAVB $.

    $( Lemma for properties of a specially modified restriction of a linear
       combination containing a unit as scalar.  (Contributed by AV,
       18-May-2019.) $)
    lincresunitlem2 $p |- ( ( ( ( S e. ~P B /\ M e. LMod /\ X e. S )
                      /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U ) ) /\ Y e. S )
                       -> ( ( I ` ( N ` ( F ` X ) ) ) .x. ( F ` Y ) ) e. E ) $=
      ( cpw wcel clmod w3a cmap co cfv wa crg lmodring 3ad2ant2 lincresunitlem1
      adantr wi wf elmapi ffvelcdm ex syl ad2antrl imp ringcl syl3anc ) CAUGUHZ
      JUIUHZLCUHZUJZGFCUKULUHZLGUMZEUHZUNZUNZMCUHZUNBUOUHZVOKUMIUMZFUHZMGUMZFUH
      ZWAWCDULFUHVRVTVSVMVTVQVKVJVTVLBJRUPUQUSUSVRWBVSABCDEFGHIJKLNOPQRSTUAUBUC
      UDUEUFURUSVRVSWDVNVSWDUTZVMVPVNCFGVAZWEGFCVBWFVSWDCFMGVCVDVEVFVGFBDWAWCSU
      EVHVI $.

    $d B s $.  $d E s $.  $d F s $.  $d M s $.  $d S s $.  $d X s $.  $d U s $.
    $( Property 1 of a specially modified restriction of a linear combination
       containing a unit as scalar.  (Contributed by AV, 18-May-2019.) $)
    lincresunit1 $p |- ( ( ( S e. ~P B /\ M e. LMod /\ X e. S )
                           /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U ) )
                         -> G e. ( E ^m ( S \ { X } ) ) ) $=
      ( cpw wcel clmod w3a cmap co cfv wa csn cdif cv wf eldifi lincresunitlem2
      cmpt sylan2 fmpttd cvv wb cbs fvexi difexg 3ad2ant1 adantr elmapg sylancr
      mpbird eqeltrid ) CAUFZUGZJUHUGZLCUGZUIZGFCUJUKUGLGULZEUGUMZUMZHOCLUNZUOZ
      VSKULIULOUPZGULDUKZUTZFWCUJUKZUEWAWFWGUGZWCFWFUQZWAOWCWEFWDWCUGWAWDCUGWEF
      UGWDCWBURABCDEFGHIJKLWDMNOPQRSTUAUBUCUDUEUSVAVBWAFVCUGWCVCUGZWHWIVDFBVERV
      FVRWJVTVOVPWJVQCWBVNVGVHVIFWCWFVCVCVJVKVLVM $.

    $d I s $.  $d N s $.  $d .x. s $.
    ${
      $d B x $.  $d E x $.  $d F x $.  $d G x $.  $d M x $.  $d N x $.
      $d S x $.  $d U x $.  $d X x $.  $d .0. s x $.
      $( Property 2 of a specially modified restriction of a linear combination
         containing a unit as scalar.  (Contributed by AV, 18-May-2019.) $)
      lincresunit2 $p |- ( ( ( S e. ~P B /\ M e. LMod /\ X e. S )
                    /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U /\ F finSupp .0. ) )
                           -> G finSupp .0. ) $=
        ( vx cmap co wcel cfv cfsupp wbr w3a cpw clmod wi wa cvv wfun csupp cfn
        wss csn cdif difexg 3ad2ant1 adantl adantr cmpt mptexg eqeltrid funmpt2
        cv syl a1i c0g fvexi simpr fsuppimpd wfn wceq wral simplr simpll eldifi
        lincresunitlem2 syl21anc ralrimiva fnmpt elmapfn jca difssd simpr1 3jca
        fveq2 oveq2d simpllr oveq2 crg lmodring 3ad2ant2 lincresunitlem1 ancoms
        fvmptd3 ringrz syl2anc sylan9eqr ex suppfnss imp suppssfifsupp syl32anc
        eqtrd com23 3impia impcom ) GFCUGUHUIZLGUJZEUIZGMUKULZUMCAUNZUIZJUOUIZL
        CUIZUMZHMUKULZXQXSXTYEYFUPXQXSUQZYEXTYFYGYEXTYFUPYGYEUQZXTYFYHXTUQZHURU
        IZHUSZMURUIZGMUTUHZVAUIHMUTUHYMVBZYFYICLVCZVDZURUIZYJYHYQXTYEYQYGYBYCYQ
        YDCYOYAVEVFVGVHYQHOYPXRKUJIUJZOVMZGUJZDUHZVIURUEOYPUUAURVJVKVNYKYIOYPUU
        AHUEVLVOYLYIMBVPTVQZVOYIGMYHXTVRVSYHYNXTYHHYPVTZGCVTZUQZYPCVBZYBYLUMZUF
        VMZGUJZMWAZUUHHUJZMWAZUPZUFYPWBZYNYHUUCUUDYHUUAFUIZOYPWBUUCYHUUOOYPYHYS
        YPUIZUQYEYGYSCUIZUUOYGYEUUPWCYGYEUUPWDUUPUUQYHYSCYOWEVGABCDEFGHIJKLYSMN
        OPQRSTUAUBUCUDUEWFWGWHOYPUUAHFUEWIVNYGUUDYEXQUUDXSGFCWJVHVHWKYHUUFYBYLY
        HCYOWLYGYBYCYDWMYLYHUUBVOWNYHUUMUFYPYHUUHYPUIZUQZUUJUULUUSUUJUQZUUKYRUU
        IDUHZMUUTOUUHUUAUVAYPHFUEYSUUHWAYTUUIYRDYSUUHGWOWPYHUURUUJWCUUTYEYGUUHC
        UIZUVAFUIYGYEUURUUJWQUUSYGUUJYGYEUURWDVHUUSUVBUUJUURUVBYHUUHCYOWEVGVHAB
        CDEFGHIJKLUUHMNOPQRSTUAUBUCUDUEWFWGXDUUJUUSUVAYRMDUHZMUUIMYRDWRYHUVCMWA
        ZUURYHBWSUIZYRFUIZUVDYEUVEYGYCYBUVEYDBJQWTXAVGYEYGUVFABCDEFGHIJKLMNOPQR
        STUAUBUCUDUEXBXCFBDYRMRUDTXEXFVHXGXMXHWHUUEUUGUQUUNYNUFYPCHGYAURMXIXJWG
        VHYMHURURMXKXLXHXHXNXOXP $.
    $}

    $d s z $.
    $( Lemma 1 for ~ lincresunit3 .  (Contributed by AV, 17-May-2019.) $)
    lincresunit3lem1 $p |- ( ( ( S e. ~P B /\ M e. LMod /\ X e. S )
               /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U /\ z e. ( S \ { X } ) ) )
                 -> ( ( N ` ( F ` X ) ) ( .s ` M ) ( ( G ` z ) ( .s ` M ) z ) )
                    = ( ( F ` z ) ( .s ` M ) z ) ) $=
      ( cpw wcel clmod w3a cmap co cfv cv csn cdif wa cvsca fveq2 oveq2d simpr3
      cvv weq ovexd fvmptd3 oveq1d wceq simp2 adantr lmodfgrp 3ad2ant2 grpinvcl
      cgrp unitcl syl2an 3simpa anim2i eldifi adantl lincresunitlem2 syl2anc wi
      3ad2ant3 elpwi sseld syl5com com12 3ad2ant1 imp lmodvsass eqcomd syl13anc
      eqid crg lmodring wf elmapi ffvelcdm 3adant2 invginvrid syl3anc 3eqtrd )
      DBUGUHZKUIUHZMDUHZUJZHGDUKULUHZMHUMZFUHZAUNZDMUOZUPZUHZUJZUQZXHLUMZXJIUMZ
      XJKURUMZULZXRULXPXPJUMZXJHUMZEULZXJXRULZXRULZXPYBEULZXJXRULZYAXJXRULXOXSY
      CXPXRXOXQYBXJXRXOPXJXTPUNZHUMZEULYBXLIVBUFPAVCYHYAXTEYGXJHUSUTXFXGXIXMVAX
      OXTYAEVDVEVFUTXOXDXPGUHZYBGUHZXJBUHZYDYFVGXFXDXNXCXDXEVHVIXFCVMUHZXHGUHZY
      IXNXDXCYLXECKRVJVKXIXGYMXMGCFXHSTVNVKGCLXHSUCVLVOXOXFXGXIUQZUQXJDUHZYJXNY
      NXFXGXIXMVPVQXNYOXFXMXGYOXIXJDXKVRZWCVSBCDEFGHIJKLMXJNOPQRSTUAUBUCUDUEUFV
      TWAXFXNYKXCXDXNYKWBXEXNXCYKXMXGXCYKWBXIXMYOXCYKYPXCDBXJDBWDWEWFWCWGWHWIXD
      YIYJYKUJUQYFYDXPYBXRECGBKXJQRXRWMSUEWJWKWLXOYEYAXJXRXOCWNUHZYAGUHZXIYEYAV
      GXFYQXNXDXCYQXECKRWOVKVIXNYRXFXGXMYRXIXGDGHWPYOYRXMHGDWQYPDGXJHWRVOWSVSXN
      XIXFXGXIXMVHVSGCEFJLYAXHSTUCUDUEWTXAVFXB $.

    $d B z $.  $d E z $.  $d F z $.  $d G z $.  $d M z $.  $d N z $.  $d R z $.
    $d S z $.  $d U z $.  $d X z $.  $d Z z $.  $d .0. s z $.
    $( Lemma 2 for ~ lincresunit3 .  (Contributed by AV, 18-May-2019.)  (Proof
       shortened by AV, 30-Jul-2019.) $)
    lincresunit3lem2 $p |- ( ( ( S e. ~P B /\ M e. LMod /\ X e. S )
                    /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U /\ F finSupp .0. ) )
        -> ( ( N ` ( F ` X ) ) ( .s ` M )
             ( M gsum ( z e. ( S \ { X } ) |-> ( ( G ` z ) ( .s ` M ) z ) ) ) )
             = ( ( F |` ( S \ { X } ) ) ( linC ` M ) ( S \ { X } ) ) ) $=
      ( cpw wcel clmod w3a cmap co cfv cfsupp wbr wa cdif cres clinc cvsca cmpt
      csn cv cgsu csca cbs wceq simpl2 wss fveq2i oveq1i eleq2i biimpi 3ad2ant1
      eqtri adantl difssd elmapssres syl2anc elpwi ssdifssd cvv wb difexg elpwg
      syl mpbird eleq2s adantr lincval syl3anc simplr1 simplr2 lincresunit3lem1
      pweqi simpll simpr fvres eqcomd oveq1d eqtrd mpteq2dva oveq2d cplusg eqid
      syl13anc cgrp lmodfgrp 3ad2ant2 wf elmapi ffvelcdm expcom 3ad2ant3 impcom
      wi syl5com grpinvcl 3ad2antr1 lincresunit1 3adantr3 3syl imp eldifi ssel2
      lmodvscl c0g simp2 jca lincresunit2 breqtrdi scmfsupp breqtrrdi gsumvsmul
      ex 3eqtr2rd ) DBUGZUHZKUIUHZMDUHZUJZHGDUKULZUHZMHUMZFUHZHNUNUOZUJZUPZHDMV
      BZUQZURZUUJKUSUMULZKAUUJAVCZUUKUMZUUMKUTUMZULZVAZVDULZKAUUJUUDLUMZUUMIUMZ
      UUMUUOULZUUOULZVAZVDULUUSKAUUJUVAVAZVDULUUOULUUHYSUUKKVEUMZVFUMZUUJUKULUH
      ZUUJKVFUMZUGZUHZUULUURVGYRYSYTUUGVHZUUHHUVFDUKULZUHZUUJDVIUVGUUGUVMUUAUUC
      UUEUVMUUFUUCUVMUUBUVLHGUVFDUKGCVFUMUVFSCUVEVFRVJVOVKVLVMVNVPUUHDUUIVQHUVF
      DUUJVRVSUUAUVJUUGYRYSUVJYTUVJDUVIYQDUVIUHZUVJUUJUVHVIZUVNDUVHUUIDUVHVTWAU
      VNUUJWBUHZUVJUVOWCDUUIUVIWDUUJUVHWBWEWFWGBUVHQWOWHVNZWIAUUKKUUJUIWJWKUUHU
      VCUUQKVDUUHAUUJUVBUUPUUHUUMUUJUHZUPZUVBUUMHUMZUUMUUOULZUUPUVSUUAUUCUUEUVR
      UVBUWAVGUUAUUGUVRWPUUCUUEUUFUUAUVRWLUUCUUEUUFUUAUVRWMUUHUVRWQABCDEFGHIJKL
      MNOPQRSTUAUBUCUDUEUFWNXFUVSUVTUUNUUMUUOUVSUUNUVTUVRUUNUVTVGUUHUUMUUJHWRVP
      WSWTXAXBXCUUHUUJBKXDUMZKCUUOAGWBUUSUVAOQRSUBUWBXEUUOXEZUVKUUAUVPUUGYRYSUV
      PYTDUUIYQWDVNWIUUAUUEUUCUUSGUHZUUFUUAUUCUPCXGUHZUUDGUHZUWDUUAUWEUUCYSYRUW
      EYTCKRXHXIWIUUCUUAUWFUUCDGHXJZUUAUWFHGDXKYTYRUWGUWFXPYSUWGYTUWFDGMHXLXMXN
      XQXOGCLUUDSUCXRVSXSUVSYSUUTGUHZUUMBUHZUVABUHUUHYSUVRUVKWIUUHUVRUWHUUHIGUU
      JUKULUHZUUJGIXJZUVRUWHXPUUAUUCUUEUWJUUFBCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFXTY
      AZIGUUJXKUWKUVRUWHUUJGUUMIXLYOYBYCUUHUVRUWIUUAUVRUWIXPZUUGYRYSUWMYTYRDBVI
      ZUVRUWIDBVTUVRUUMDUHZUWNUWIXPUUMDUUIYDUWNUWOUWIDBUUMYEXMWFXQVNWIYCUUTUUOC
      GBKUUMQRUWCSYFWKUUHYSUVJUPZUWJICYGUMZUNUOZUVDOUNUOUUAUWPUUGUUAYSUVJYRYSYT
      YHUVQYIWIUWLUUHINUWQUNBCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFYJUAYKUWPUWJUWRUJUVD
      KYGUMOUNAIGCKUUJRSYLUBYMWKYNYP $.

    $d G s $.  $d R s $.  $d Z s $.
    $( Property 3 of a specially modified restriction of a linear combination
       in a vector space.  (Contributed by AV, 18-May-2019.)  (Proof shortened
       by AV, 30-Jul-2019.) $)
    lincresunit3 $p |- ( ( ( S e. ~P B /\ M e. LMod /\ X e. S )
                      /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U /\ F finSupp .0. )
                      /\ ( F ( linC ` M ) S ) = Z )
                         -> ( G ( linC ` M ) ( S \ { X } ) ) = X ) $=
      ( vz cpw wcel clmod w3a cmap co cfv cfsupp wbr clinc wceq cdif cvsca cmpt
      csn cv cgsu csca cbs simp2 3ad2ant1 wf wa 3simpa 3ad2ant2 lincresunitlem2
      simp1 jca eldifi syl2an fveq2i eqtri eleqtrdi fmptd wb fvex difexg elmapg
      cvv sylancr mpbird adantl wss ssdifss a1i elpwi impel elpwd expcom eleq2s
      wi pweqi imp 3adant2 lincval syl3anc cres cplusg simp3 3jca adantr 3simpb
      eqidd eqid lincdifsn eqeq1d fveq2 oveq12d cbvmptv oveq2d lincresunit3lem2
      id eqtr2d oveq1d cminusg lmodgrp elmapi ffvelcdm sselda lmodvscl lmodfgrp
      cgrp syl2anr grpinvcl syl2an2r ccmn lmodcmn simpll2 lincresunit1 3adantr3
      syl ffvelcdmda c0g sylbid ssel2 syl2imc fmpttd sseqtrdi breqtrdi scmfsupp
      lincresunit2 breqtrrdi gsumcl grpinvid2 lmodvsneg simpr2 lincresunit3lem3
      eqcom bitrdi syl31anc biimpd sylbird 3impia eqtrd ) CAUGZUHZJUIUHZLCUHZUJ
      ZGFCUKULUHZLGUMZEUHZGMUNUOZUJZGCJUPUMZULZNUQZUJZHCLVAZURZUVKULZJOUVPOVBZH
      UMZUVRJUSUMZULZUTZVCULZLUVNUVCHJVDUMZVEUMZUVPUKULUHZUVPJVEUMZUGZUHZUVQUWC
      UQUVEUVJUVCUVMUVBUVCUVDVFZVGUVNUWFUVPUWEHVHZUVNOUVPUVGKUMZIUMUVRGUMDULZUW
      EHUVNUVRUVPUHZVIUWMFUWEUVNUVEUVFUVHVIZVIUVRCUHZUWMFUHUWNUVNUVEUWOUVEUVJUV
      MVMUVJUVEUWOUVMUVFUVHUVIVJVKVNUVRCUVOVOZABCDEFGHIJKLUVRMNOPQRSTUAUBUCUDUE
      VLVPFBVEUMUWERBUWDVEQVQVRVSUEVTUVNUWEWEUHUVPWEUHZUWFUWKWAUWDVEWBUVEUVJUWR
      UVMUVBUVCUWRUVDCUVOUVAWCZVGZVGUWEUVPHWEWEWDWFWGUVEUVJUWIUVMUVBUVDUWIUVCUV
      BUVDUWIUVDUWIWQCUWHUVAUVDCUWHUHZUWIUVDUXAVIUVPUWGWEUXAUWRUVDCUVOUWHWCWHUV
      DCUWGWIZUVPUWGWIZUXAUXBUXCWQUVDCUWGUVOWJWKCUWGWLWMWNWOAUWGPWRWPWSWTVGOHJU
      VPUIXAXBUVEUVJUVMUWCLUQZUVEUVJVIZUVMGUVPXCZUVPUVKULZUVGLUVTULZJXDUMZULZNU
      QZUXDUXEUVLUXJNUXEUVCUVBUVDUJZUVFUVIVIZUXFUXFUQUVLUXJUQUVEUXLUVJUVEUVCUVB
      UVDUWJUVBUVCUVDVMUVBUVCUVDXEZXFXGUVJUXMUVEUVFUVHUVIXHWHUXEUXFXIAUXIBFUVTG
      UXFJCLMPQRUVTXJZUXIXJZTXKXBXLUXEUXKUWLUWCUVTULZUXHUXIULZNUQZUXDUXEUXJUXRN
      UXEUXGUXQUXHUXIUXEUXQUWLJUFUVPUFVBZHUMZUXTUVTULZUTZVCULZUVTULUXGUXEUWCUYD
      UWLUVTUXEUWBUYCJVCUWBUYCUQUXEOUFUVPUWAUYBUVRUXTUQZUVSUYAUVRUXTUVTUVRUXTHX
      MUYEXRXNXOWKXPXPUFABCDEFGHIJKLMNOPQRSTUAUBUCUDUEXQXSXTXLUXEUXSUXHJYAUMZUM
      ZUXQUQZUXDUXEJYHUHZUXHAUHZUXQAUHZUYHUXSWAUVEUYIUVJUVCUVBUYIUVDJYBVKXGUXEU
      VCUVGFUHZLAUHZUYJUVEUVCUVJUWJXGZUVJCFGVHZUVDUYLUVEUVFUVHUYOUVIGFCYCVGUXNC
      FLGYDYIZUVEUYMUVJUVBUVDUYMUVCUVBCALCAWLZYEWTXGZUVGUVTBFAJLPQUXORYFXBUXEUV
      CUWLFUHZUWCAUHZUYKUYNUVEBYHUHZUVJUYLUYSUVCUVBVUAUVDBJQYGVKUYPFBKUVGRUBYJY
      KUXEUVPAUWBJWENPUAUVEJYLUHZUVJUVCUVBVUBUVDJYMVKXGUVEUWRUVJUWTXGUXEOUVPUWA
      AUXEUWNVIUVCUVSFUHUVRAUHZUWAAUHUVBUVCUVDUVJUWNYNUXEUVPFUVRHUXEHFUVPUKULUH
      ZUVPFHVHUVEUVFUVHVUDUVIABCDEFGHIJKLMNOPQRSTUAUBUCUDUEYOYPZHFUVPYCYQYRUXEU
      WNVUCUVEUWNVUCWQZUVJUVBUVCVUFUVDUWNUWPUVBCAWIZVUCUWQUYQVUGUWPVUCCAUVRUUAW
      OUUBVGXGWSUVSUVTBFAJUVRPQUXORYFXBUUCUXEUWBJYSUMZNUNUXEUVCUWIVIZVUDHBYSUMZ
      UNUOUWBVUHUNUOUVEVUIUVJUVEUVCUWIUWJUVBUVDUWIUVCUVBUVDVIZUVPUWGWEUVBUWRUVD
      UWSXGVUKUVPAUWGUVBUVPAWIZUVDUVBVUGVULUYQCAUVOWJYQXGPUUDWNWTVNXGVUEUXEHMVU
      JUNABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUUGTUUEOHFBJUVPQRUUFXBUAUUHUUIZUWLUVTBFA
      JUWCPQUXORYFXBAUXIJUYFUXHUXQNPUXPUAUYFXJZUUJXBUXEUYHUWLLUVTULZUXQUQZUXDUX
      EUYGVUOUXQUXEAUVGUVTBFKUYFJLPQUXOVUNRUBUYNUYRUYPUUKXLUXEVUPUXDUXEUVCUYMUY
      TUVHVUPUXDWAUYNUYRVUMUVEUVFUVHUVIUULUVCUYMUYTUJUVHVIVUPLUWCUQUXDUVGABUVTE
      FJKLUWCPQRSUBUXOUUMLUWCUUNUUOUUPUUQYTUURYTYTUUSUUT $.

    $( Property 3 of a specially modified restriction of a linear combination
       in a vector space.  (Contributed by AV, 18-May-2019.)  (Proof shortened
       by AV, 30-Jul-2019.) $)
    lincreslvec3 $p |- ( ( ( S e. ~P B /\ M e. LVec /\ X e. S )
                   /\ ( F e. ( E ^m S ) /\ ( F ` X ) =/= .0. /\ F finSupp .0. )
                   /\ ( F ( linC ` M ) S ) = Z )
                         -> ( G ( linC ` M ) ( S \ { X } ) ) = X ) $=
      ( cpw wcel clvec w3a cmap co cfv wne cfsupp wbr clinc wceq clmod csn cdif
      lveclmod 3anim2i 3ad2ant1 simp21 wa wf elmapi ffvelcdm syl2anr simpr2 cdr
      simp3 wb lvecdrng 3ad2ant2 adantr drngunit mpbir2and 3adant3 lincresunit3
      syl syl131anc ) CAUFUGZJUHUGZLCUGZUIZGFCUJUKUGZLGULZMUMZGMUNUOZUIZGCJUPUL
      ZUKNUQZUIWCJURUGZWEUIZWGWHEUGZWJWMHCLUSUTWLUKLUQWFWKWOWMWDWNWCWEJVAVBVCWF
      WGWIWJWMVDWFWKWPWMWFWKVEZWPWHFUGZWIWKCFGVFZWEWRWFWGWIWSWJGFCVGVCWCWDWEVLC
      FLGVHVIWFWGWIWJVJWQBVKUGZWPWRWIVEVMWFWTWKWDWCWTWEBJQVNVOVPFBEWHMRSTVQWAVR
      VSWKWFWJWMWGWIWJVLVOWFWKWMVLABCDEFGHIJKLMNOPQRSTUAUBUCUDUEVTWB $.
  $}

  ${
    $d B f g s z $.  $d E f g s z $.  $d M f g s z $.  $d R f g s z $.
    $d S f g s z $.  $d Z f g s $.  $d .0. f g s $.
    islindeps2.b $e |- B = ( Base ` M ) $.
    islindeps2.z $e |- Z = ( 0g ` M ) $.
    islindeps2.r $e |- R = ( Scalar ` M ) $.
    islindeps2.e $e |- E = ( Base ` R ) $.
    islindeps2.0 $e |- .0. = ( 0g ` R ) $.
    $( Conditions for being a linearly dependent subset of a (left) module over
       a nonzero ring.  (Contributed by AV, 29-Apr-2019.)  (Proof shortened by
       AV, 30-Jul-2019.) $)
    islindeps2 $p |- ( ( M e. LMod /\ S e. ~P B /\ R e. NzRing )
                       -> ( E. s e. S E. f e. ( E ^m ( S \ { s } ) )
                      ( f finSupp .0. /\ ( f ( linC ` M ) ( S \ { s } ) ) = s )
                            -> S linDepS M ) ) $=
      ( vg wcel cfv wceq wa wrex vz clmod cpw cnzr w3a cv cfsupp wbr cdif clinc
      csn co cmap clindeps wne cur cminusg cif id 3adant3 ad3antrrr crg nzrring
      cmpt eqid ringidcl syl 3ad2ant3 simpllr simplr 3jca simprl lincext2 cvsca
      syl3anc simpl1 wi elelpwi expcom imp lmodvs1 syl2anc adantr eqcomd adantl
      3ad2ant2 sylan9eq lincext3 syl112anc jca cvv eqidd iftrue simpr fvexd c0g
      fvmptd nzrneg1ne0 neeqtrrd eqnetrd lincext1 wb breq1 oveq1 eqeq1d anbi12d
      a1i fveq1 neeq1d rspcedv mp2and rexlimdva2 reximdva df-3an r19.42v bitr4i
      rexbii rexcom bitri sylibr islindeps mpbird ex ) FUBPZCAUCPZBUDPZUEZDUFZG
      UGUHZYHCIUFZUKUIZFUJQZULZYJRZSZDEYKUMULZTZICTZCFUNUHZYGYRSZYSOUFZGUGUHZUU
      ACYLULZHRZYJUUAQZGUOZICTZUEZOECUMULZTZYTUUBUUDSZUUFSZOUUITZICTZUUJYGYRUUN
      YGYQUUMICYGYJCPZSZYOUUMDYPUUPYHYPPZSZYOSZUACUAUFZYJRZBUPQZBUQQZQZUUTYHQZU
      RZVDZGUGUHZUVGCYLULZHRZSZYJUVGQZGUOZUUMUUSUVHUVJUUSYDYESZUVBEPZUUOUUQUEZY
      IUVHYGUVNUUOUUQYOYDYEUVNYFUVNUSUTVAZUUSUVOUUOUUQYGUVOUUOUUQYOYFYDUVOYEYFB
      VBPUVOBVCEBUVBMUVBVEZVFVGVHVAYGUUOUUQYOVIUUPUUQYOVJVKZUURYIYNVLZUAABCEUVG
      YHFUVCYJUVBGHJLMNKUVCVEZUVGVEZVMVOUUSUVNUVPYIUVBYJFVNQZULZYMRUVJUVQUVSUVT
      UURYOUWDYJYMUUPUWDYJRZUUQUUPYDYJAPZUWEYDYEYFUUOVPYGUUOUWFYEYDUUOUWFVQYFUU
      OYEUWFYJCAVRVSWFVTUWCUVBBAFYJJLUWCVEUVRWAWBWCYNYJYMRYIYNYMYJYNUSWDWEWGUAA
      BCEUVGYHFUVCYJUVBGHJLMNKUWAUWBWHWIWJUURUVMYOUUPUVMUUQUUPUVLUVDGUUPUAYJUVF
      UVDCUVGWKUUPUVGWLUVAUVFUVDRUUPUVAUVDUVEWMWEYGUUOWNUUPUVBUVCWOWQYGUVDGUOZU
      UOYFYDUWGYEYFUVDBWPQZGBWRGUWHRYFNXGWSVHWCWTWCWCUUSUULUVKUVMSZOUVGUUIUUSUV
      NUVPUVGUUIPUVQUVSUAABCEUVGYHFUVCYJUVBGHJLMNKUWAUWBXAWBUUAUVGRZUULUWIXBUUS
      UWJUUKUVKUUFUVMUWJUUBUVHUUDUVJUUAUVGGUGXCUWJUUCUVIHUUAUVGCYLXDXEXFUWJUUEU
      VLGYJUUAUVGXHXIXFWEXJXKXLXMVTUUJUULICTZOUUITUUNUUHUWKOUUIUUHUUKUUGSUWKUUB
      UUDUUGXNUUKUUFICXOXPXQUULOIUUICXRXSXTYGYSUUJXBZYRYDYEUWLYFIABCOEFUBGHJKLM
      NYAUTWCYBYC $.

    $( Implication of being a linearly independent subset of a (left) module
       over a nonzero ring.  (Contributed by AV, 29-Apr-2019.)  (Proof
       shortened by AV, 30-Jul-2019.) $)
    islininds2 $p |- ( ( M e. LMod /\ S e. ~P B /\ R e. NzRing )
                   -> ( S linIndS M -> A. s e. S A. f e. ( E ^m ( S \ { s } ) )
          ( -. f finSupp .0. \/ ( f ( linC ` M ) ( S \ { s } ) ) =/= s ) ) ) $=
      ( clmod wcel wbr wn wrex bitri cpw cnzr w3a clininds clindeps cfsupp cdif
      cv csn clinc cfv co wne wo cmap wb lindepsnlininds ancoms 3adant3 con2bid
      wral wceq wa notnotb nne bicomi pm4.56 rexbii rexnal islindeps2 biimtrrid
      anbi12i con1d sylbid ) FOPZCAUAZPZBUBPZUCZCFUDQZCFUEQZRDUHZGUFQZRZWBCIUHZ
      UIUGZFUJUKULZWEUMZUNZDEWFUOULZVAZICVAZVSWAVTVOVQWAVTRUPZVRVQVOWMCFVPOUQUR
      USUTVSWLWAWLRZWCWGWEVBZVCZDWJSZICSZVSWAWRWKRZICSWNWQWSICWQWIRZDWJSWSWPWTD
      WJWPWDRZWHRZVCWTWCXAWOXBWCVDXBWOWGWEVEVFVLWDWHVGTVHWIDWJVITVHWKICVITABCDE
      FGHIJKLMNVJVKVMVN $.

    $d B s g y $.  $d E y $.  $d M y $.  $d R y $.  $d S y $.  $d Z y z $.
    $d .0. y z $.
    $( Alternative definition of being a linearly dependent subset of a (left)
       vector space.  In this case, the reverse implication of ~ islindeps2
       holds, so that both definitions are equivalent (see theorem 1.6 in
       [Roman] p. 46 and the note in [Roman] p. 112: if a nontrivial linear
       combination of elements (where not all of the coefficients are 0) in an
       R-vector space is 0, then and only then each of the elements is a linear
       combination of the others.  (Contributed by AV, 30-Apr-2019.)  (Proof
       shortened by AV, 30-Jul-2019.) $)
    isldepslvec2 $p |- ( ( M e. LVec /\ S e. ~P B )
                  -> ( E. s e. S E. f e. ( E ^m ( S \ { s } ) ) ( f finSupp .0.
               /\ ( f ( linC ` M ) ( S \ { s } ) ) = s ) <-> S linDepS M ) ) $=
      ( vg wcel wa cfv co wrex vz vy clvec cpw cv cfsupp wbr csn cdif wceq cmap
      clinc clindeps clmod cnzr wi lveclmod adantr simpr cdr drngnzr islindeps2
      lvecdrng syl syl3anc wne w3a islindeps df-3an r19.42v bitr4i rexbii bitri
      rexcom cminusg cinvr cmulr cmpt cui simplr ad2antrr 3jca ffvelcdm syl2anr
      elmapi anim12i drngunit mpbird simpll adantl lincresunit2 syl13anc simprr
      wf eqid fveq2 oveq2d cbvmptv lincreslvec3 syl131anc lincresunit1 syl12anc
      wb breq1 oveq1 eqeq1d anbi12d rspcedv mp2and rexlimdva2 reximdva biimtrid
      sylbid impbid ) FUCPZCAUDPZQZDUEZGUFUGZXRCIUEZUHUIZFULRZSZXTUJZQZDEYAUKSZ
      TZICTZCFUMUGZXQFUNPZXPBUOPZYHYIUPXOYJXPFUQZURXOXPUSXOYKXPXOBUTPZYKBFLVCZB
      VAVDURABCDEFGHIJKLMNVBVEXQYIOUEZGUFUGZYOCYBSHUJZXTYORZGVFZICTZVGZOECUKSZT
      ZYHIABCOEFUCGHJKLMNVHUUCYPYQQZYSQZOUUBTZICTZXQYHUUCUUEICTZOUUBTUUGUUAUUHO
      UUBUUAUUDYTQUUHYPYQYTVIUUDYSICVJVKVLUUEOIUUBCVNVMXQUUFYGICXQXTCPZQZUUEYGO
      UUBUUJYOUUBPZQZUUEQZUAYAYRBVORZRBVPRZRZUAUEZYORZBVQRZSZVRZGUFUGZUVAYAYBSZ
      XTUJZYGUUMXPYJUUIVGZUUKYRBVSRZPZYPUVBUUJUVEUUKUUEUUJXPYJUUIXOXPUUIVTZXOYJ
      XPUUIYLWAXQUUIUSZWBWAZUUJUUKUUEVTZUUMUVGYREPZYSQZUULUVLUUEYSUUKCEYOWNUUIU
      VLUUJYOECWEUVICEXTYOWCWDUUDYSUSWFUUMYMUVGUVMXCUUJYMUUKUUEXOYMXPUUIYNWAWAE
      BUVFYRGMUVFWOZNWGVDWHZUUEYPUULYPYQYSWIWJZABCUUSUVFEYOUVAUUOFUUNXTGHUAJLMU
      VNNKUUNWOZUUOWOZUUSWOZUVAWOZWKWLUUMXPXOUUIVGZUUKYSYPYQUVDUUJUWAUUKUUEUUJX
      PXOUUIUVHXOXPUUIWIUVIWBWAUVKUULUUDYSWMUVPUUEYQUULYPYQYSVTWJABCUUSUVFEYOUV
      AUUOFUUNXTGHUBJLMUVNNKUVQUVRUVSUAUBYAUUTUUPUBUEZYORZUUSSUUQUWBUJUURUWCUUP
      UUSUUQUWBYOWPWQWRWSWTUUMYEUVBUVDQZDUVAYFUUMUVEUUKUVGUVAYFPUVJUVKUVOABCUUS
      UVFEYOUVAUUOFUUNXTGHUAJLMUVNNKUVQUVRUVSUVTXAXBXRUVAUJZYEUWDXCUUMUWEXSUVBY
      DUVDXRUVAGUFXDUWEYCUVCXTXRUVAYAYBXEXFXGWJXHXIXJXKXLXMXN $.
  $}

  ${
    $d M s $.  $d S s $.
    $( A singleton not containing the zero element of a vector space is always
       linearly independent.  (Contributed by AV, 16-Apr-2019.)  (Revised by
       AV, 28-Apr-2019.) $)
    lindssnlvec $p |- ( ( M e. LVec /\ S e. ( Base ` M ) /\ S =/= ( 0g ` M ) )
                         -> { S } linIndS M ) $=
      ( vs clvec wcel cbs cfv c0g wne w3a cv cvsca co csca csn cdif wral adantl
      wa eqid clininds eldifsni simpl3 simpl1 eldifi simpl2 mpbir2and ralrimiva
      wbr lvecvsn0 clmod wb lveclmod anim1i 3adant3 snlindsntor syl mpbid ) BDE
      ZABFGZEZABHGZIZJZCKZABLGZMVBIZCBNGZFGZVHHGZOZPZQZAOBUAUIZVDVGCVLVDVEVLEZS
      ZVGVEVJIZVCVOVQVDVEVIVJUBRUSVAVCVOUCVPVEVFVHVIVJUTBAVBUTTZVFTZVHTZVITZVJT
      ZVBTZUSVAVCVOUDVOVEVIEVDVEVIVKUERUSVAVCVOUFUJUGUHVDBUKEZVASZVMVNULUSVAWEV
      CUSWDVABUMUNUOUTVHVIVFBAVJVBCVRVTWAWBWCVSUPUQUR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Simple left modules and the ` ZZ `-module
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d I r x y $.  $d R r x y $.  $d V r x y $.  $d I q $.  $d R q $.
    $d V q $.
    lmod1.m $e |- M = ( { <. ( Base ` ndx ) , { I } >. ,
                          <. ( +g ` ndx ) , { <. <. I , I >. , I >. } >. ,
                          <. ( Scalar ` ndx ) , R >. }
                     u. { <. ( .s ` ndx ) ,
                             ( x e. ( Base ` R ) , y e. { I } |-> y ) >. } ) $.
    $( Lemma 1 for ~ lmod1 .  (Contributed by AV, 28-Apr-2019.) $)
    lmod1lem1 $p |- ( ( I e. V /\ R e. Ring /\ r e. ( Base ` R ) )
                      -> ( r ( .s ` M ) I ) e. { I } ) $=
      ( wcel crg cv cbs cfv w3a cvsca co csn cvv wceq cop cmpo fvex a1i mpoexga
      snex sylancr lmodvsca syl eqcomd weq simprr simp3 3ad2ant1 ovmpod eqeltrd
      snidg ) DFIZCJIZGKZCLMZIZNZUSDEOMZPDDQZVBABUSDUTVDBKZDVCVDVBABUTVDVEUAZVC
      VBVFRIZVFVCSVBUTRIVDRIZVGCLUBVHVBDUEUCABUTVDVERRUDUFVDDDTDTQVFCERHUGUHUIV
      BAGUJVEDSUKUQURVAULUQURDVDIVADFUPUMZVIUNVIUO $.

    $( Lemma 2 for ~ lmod1 .  (Contributed by AV, 28-Apr-2019.) $)
    lmod1lem2 $p |- ( ( I e. V /\ R e. Ring /\ r e. ( Base ` R ) )
                 -> ( r ( .s ` M ) ( I ( +g ` M ) I ) )
                    = ( ( r ( .s ` M ) I ) ( +g ` M ) ( r ( .s ` M ) I ) ) ) $=
      ( wcel cv cbs cfv co csn cvv wceq snex mp1i cop eqcomd crg w3a cvsca cmpo
      cplusg wa fvex pm3.2i mpoexga lmodvsca simprr simp3 snidg 3ad2ant1 ovmpod
      syl weq lmodplusg oveqd df-ov simp1 fvsng sylancr eqtrid eqtrd oveq2d a1i
      opex oveq12d 3eqtr4d ) DFIZCUAIZGJZCKLZIZUBZVMDEUCLZMZDVMDDEUELZMZVQMVRVR
      VSMZVPABVMDVNDNZBJZDVQWBVPABVNWBWCUDZVQVPWDOIZWDVQPZVNOIZWBOIZUFWEVPWGWHC
      KUGZDQZUHABVNWBWCOOUIZRWBDDSZDSZNZWDCEOHUJZUPTVPAGUQWCDPUKZVKVLVOULZVKVLD
      WBIVODFUMUNZWRUOVPVTDVMVQVPVTDDWNMZDVPVSWNDDVPWNVSWNOIWNVSPVPWMQWBWNWDCEO
      HURRTUSVPWSWLWNLZDDDWNUTVPWLOIVKWTDPDDVHVKVLVOVAWLDOFVBVCVDVEZVFVPWAVTDVP
      VRDVRDVSVPABVMDVNWBWCDVQWBVPWDVQVPWEWFVPWGWHWEWIWHVPWJVGWKVCWOUPTWPWQWRWR
      UOZXBVIXAVEVJ $.

    $d M x y $.  $d q x y $.
    $( Lemma 3 for ~ lmod1 .  (Contributed by AV, 29-Apr-2019.) $)
    lmod1lem3 $p |- ( ( ( I e. V /\ R e. Ring )
                        /\ ( q e. ( Base ` R ) /\ r e. ( Base ` R ) ) )
                 -> ( ( q ( +g ` ( Scalar ` M ) ) r ) ( .s ` M ) I )
                    = ( ( q ( .s ` M ) I ) ( +g ` M ) ( r ( .s ` M ) I ) ) ) $=
      ( wcel wa cv cfv cplusg co wceq simprr syl adantr cvv crg csca cmpo cvsca
      cbs csn eqidd simplr cop lmodsca fveq2d eqcomd oveqd eqid ringacl syl3anc
      simprl eqeltrd snidg simpl ovmpod fvex snex mpoexga mp1i lmodvsca oveq12d
      pm3.2i weq lmodplusg df-ov opex jctil fvsng eqtrid 3eqtrd 3eqtr4d ) DFJZC
      UAJZKZHLZCUEMZJZGLZWBJZKZKZWAWDEUBMZNMZOZDABWBDUFZBLZUCZODWJDEUDMZOWADWNO
      ZWDDWNOZENMZOZWGABWJDWBWKWLDWMFWGWMUGWGALWJPWLDPZQWGWJWAWDCNMZOZWBWGWIWTW
      AWDWGWTWIWGVSWTWIPVRVSWFUHZVSCWHNWKDDUIZDUIZUFZWMCEUAIUJUKRULUMWGVSWCWEXA
      WBJXBVTWCWEUQZVTWCWEQZWBWTCWAWDWBUNWTUNUOUPURVTDWKJZWFVRXHVSDFUSSSZVTVRWF
      VRVSUTZSVAWGWNWMWJDWGWMWNWGWMTJZWMWNPWBTJZWKTJZKXKWGXLXMCUEVBDVCVHABWBWKW
      LTTVDVEWKXEWMCETIVFRULZUMWGWRDDWQODDXEOZDWGWODWPDWQWGABWADWBWKWLDWNWKXNWG
      AHVIWSQXFXIXIVAWGABWDDWBWKWLDWNWKXNWGAGVIWSQXGXIXIVAVGWGWQXEDDWGXEWQXETJX
      EWQPWGXDVCWKXEWMCETIVJVEULUMWGXOXCXEMZDDDXEVKWGXCTJZVRKZXPDPVTXRWFVTVRXQX
      JDDVLVMSXCDTFVNRVOVPVQ $.

    $( Lemma 4 for ~ lmod1 .  (Contributed by AV, 29-Apr-2019.) $)
    lmod1lem4 $p |- ( ( ( I e. V /\ R e. Ring )
                        /\ ( q e. ( Base ` R ) /\ r e. ( Base ` R ) ) )
                      -> ( ( q ( .r ` ( Scalar ` M ) ) r ) ( .s ` M ) I )
                         = ( q ( .s ` M ) ( r ( .s ` M ) I ) ) ) $=
      ( wcel crg wa cv cfv co cmulr cvv wceq simprr ovmpod cvsca csca cmpo fvex
      cbs csn snex pm3.2i a1i mpoexga cop lmodvsca 3syl eqcomd weq simprl snidg
      ad2antrr oveq2d simplr lmodsca fveq2d oveqd eqid syl3anc eqeltrd 3eqtr4rd
      syl ringcl ) DFJZCKJZLZHMZCUENZJZGMZVNJZLZLZVMDEUANZODVMVPDVTOZVTOVMVPEUB
      NZPNZOZDVTOVSABVMDVNDUFZBMZDVTWEVSABVNWEWFUCZVTVSVNQJZWEQJZLZWGQJWGVTRWJV
      SWHWICUEUDDUGUHUIABVNWEWFQQUJWEDDUKDUKUFZWGCEQIULUMUNZVSAHUOWFDRZSVLVOVQU
      PZVJDWEJVKVRDFUQURZWOTVSWADVMVTVSABVPDVNWEWFDVTWEWLVSAGUOWMSVLVOVQSZWOWOT
      USVSABWDDVNWEWFDVTWEWLVSAMWDRWMSVSWDVMVPCPNZOZVNVSWCWQVMVPVSWQWCVSVKWQWCR
      VJVKVRUTZVKCWBPWEWKWGCEKIVAVBVHUNVCVSVKVOVQWRVNJWSWNWPVNCWQVMVPVNVDWQVDVI
      VEVFWOWOTVG $.

    $( Lemma 5 for ~ lmod1 .  (Contributed by AV, 28-Apr-2019.) $)
    lmod1lem5 $p |- ( ( I e. V /\ R e. Ring )
                      -> ( ( 1r ` ( Scalar ` M ) ) ( .s ` M ) I ) = I ) $=
      ( wcel crg wa cfv cur cbs csn cv cvv wceq cop eqcomd adantl csca cmpo a1i
      cvsca fvex snex pm3.2i mpoexga lmodvsca 3syl simprr lmodsca eqid ringidcl
      fveq2d eqeltrd snidg adantr ovmpod ) DFHZCIHZJZABEUAKZLKZDCMKZDNZBOZDEUDK
      ZVFVBABVEVFVGUBZVHVBVEPHZVFPHZJZVIPHVIVHQVLVBVJVKCMUEDUFUGUCABVEVFVGPPUHV
      FDDRDRNZVICEPGUIUJSVBAOVDQVGDQUKVBVDCLKZVEVBVCCLVBCVCVACVCQUTVFVMVICEIGUL
      TSUOVAVNVEHUTVECVNVEUMVNUMUNTUPUTDVFHVADFUQURZVOUS $.

    $d I w x $.  $d M r q w $.
    $( The (smallest) structure representing a _zero module_ over an arbitrary
       ring.  (Contributed by AV, 29-Apr-2019.) $)
    lmod1 $p |- ( ( I e. V /\ R e. Ring ) -> M e. LMod ) $=
      ( vr vq wcel wa cfv co wceq wral cbs cop eqid cvv ax-mp vw crg cgrp cvsca
      csca cv csn cplusg w3a cmulr cur clmod cnx cpr grp1 fvex cmpo ctp grpbase
      cun snex opeq2i tpeq1 uneq1i eqtri lmodbase eqcomi grpplusg tpeq2 grpprop
      lmodplusg sylibr adantr lmodsca eqcomd adantl simpr eqeltrd fveq2d eleq2d
      anbi12d simpll simplr simprr 3jca lmod1lem1 lmod1lem2 lmod1lem3 lmod1lem4
      syl lmod1lem5 jca32 ex sylbid ralrimivv wb oveq2d eqeq12d 3anbi2d ralbidv
      oveq2 anbi1d ralsng eleq1d oveq1 oveq1d oveq12d 3anbi123d id bitrd mpbird
      2ralbidv islmod syl3anbrc ) DFJZCUBJZKZEUCJZEUELZUBJHUFZUAUFZEUDLZMZDUGZJ
      ZXTYAAUFZEUHLZMZYBMZYCXTYFYBMZYGMZNZIUFZXTXSUHLZMZYAYBMZYMYAYBMZYCYGMZNZU
      IZYMXTXSUJLZMZYAYBMZYMYCYBMZNZXSUKLZYAYBMZYANZKZKZUAYDOZAYDOZHXSPLZOIUUMO
      ZEULJXOXRXPXOUMPLZYDQZUMUHLZDDQDQZUGZQZUNZUCJXRDUVAFUVARZUOEUVAUVAPLZEPLZ
      UVCSJUVCUVDNUVAPUPUVCUUSABCPLZYDBUFUQZCESEUUPUUTUMUELCQZURZUMUDLUVFQUGZUT
      ZUUOUVCQZUUTUVGURZUVIUTGUVHUVLUVIUUPUVKNUVHUVLNYDUVCUUOYDSJZYDUVCNDVAZYDU
      USUVASUVBUSTVBUUPUVKUUTUVGVCTVDVEVFTVGUVAUHLZYGUVOSJUVOYGNUVAUHUPYDUVOUVF
      CESEUVJUUPUUQUVOQZUVGURZUVIUTGUVHUVQUVIUUTUVPNUVHUVQNUUSUVOUUQUUSSJUUSUVO
      NUURVAYDUUSUVASUVBVHTVBUUTUVPUUPUVGVITVDVEVKTVGVJVLVMXQXSCUBXPXSCNXOXPCXS
      YDUUSUVFCEUBGVNVOVPZXOXPVQVRXQUUNXTDYBMZYDJZXTDDYGMZYBMZUVSUVSYGMZNZYODYB
      MZYMDYBMZUVSYGMZNZUIZUUBDYBMZYMUVSYBMZNZUUFDYBMZDNZKZKZHUUMOIUUMOXQUWPIHU
      UMUUMXQYMUUMJZXTUUMJZKYMUVEJZXTUVEJZKZUWPXQUWQUWSUWRUWTXQUUMUVEYMXQXSCPUV
      RVSZVTXQUUMUVEXTUXBVTWAXQUXAUWPXQUXAKZUWIUWLUWNUXCUVTUWDUWHUXCXOXPUWTUIZU
      VTUXCXOXPUWTXOXPUXAWBXOXPUXAWCXQUWSUWTWDWEZABCDEFHGWFWJUXCUXDUWDUXEABCDEF
      HGWGWJABCDEFHIGWHWEABCDEFHIGWIXQUWNUXAABCDEFGWKVMWLWMWNWOXQUULUWPIHUUMUUM
      XQUULYEXTYADYGMZYBMZYCUVSYGMZNZYSUIZUUIKZUAYDOZUWPXOUULUXLWPXPUUKUXLADFYF
      DNZUUJUXKUAYDUXMYTUXJUUIUXMYLUXIYEYSUXMYIUXGYKUXHUXMYHUXFXTYBYFDYAYGXAWQU
      XMYJUVSYCYGYFDXTYBXAWQWRWSXBWTXCVMXOUXLUWPWPXPUXKUWPUADFYADNZUXJUWIUUIUWO
      UXNYEUVTUXIUWDYSUWHUXNYCUVSYDYADXTYBXAZXDUXNUXGUWBUXHUWCUXNUXFUWAXTYBYADD
      YGXEWQUXNYCUVSUVSYGUXOXFWRUXNYPUWEYRUWGYADYOYBXAUXNYQUWFYCUVSYGYADYMYBXAU
      XOXGWRXHUXNUUEUWLUUHUWNUXNUUCUWJUUDUWKYADUUBYBXAUXNYCUVSYMYBUXOWQWRUXNUUG
      UWMYADYADUUFYBXAUXNXIWRWAWAXCVMXJXLXKAUAYGYNYBUUAUUFXSUUMYDEHIUVMYDUVDNUV
      NYDUUSUVFCESGVFTYGRYBRXSRUUMRYNRUUARUUFRXMXN $.
  $}

  ${
    $d I a b i p z $.  $d R a b i p z $.  $d V a b i p z $.  $d Z i p z $.
    $d W p $.
    lmod1zr.r $e |- R = { <. ( Base ` ndx ) , { Z } >. ,
                       <. ( +g ` ndx ) , { <. <. Z , Z >. , Z >. } >. ,
                       <. ( .r ` ndx ) , { <. <. Z , Z >. , Z >. } >. } $.
    lmod1zr.m $e |- M = ( { <. ( Base ` ndx ) , { I } >. ,
                         <. ( +g ` ndx ) , { <. <. I , I >. , I >. } >. ,
                         <. ( Scalar ` ndx ) , R >. }
                    u. { <. ( .s ` ndx ) , { <. <. Z , I >. , I >. } >. } ) $.
    $( The (smallest) structure representing a _zero module_ over a zero ring.
       (Contributed by AV, 29-Apr-2019.) $)
    lmod1zr $p |- ( ( I e. V /\ Z e. W ) -> M e. LMod ) $=
      ( vz vi vp va vb wcel cnx cfv csn cop cv wceq wa cbs cplusg csca ctp cmpo
      cvsca cun clmod cxp c2nd wf elsni fveq2 adantl op2ndg ancoms snidg adantr
      cmpt eqeltrd sylan2 fmpttd cvv opex simpl fsng sylancr mpbid xpsng eqcomd
      wb mpteq1d eqtr3d vex op2ndd mpompt a1i snex rngbase mp1i mpoeq12 syl2anc
      eqidd 3eqtrd opeq2d sneqd uneq2d eqtrid crg ring1 id cbvmpov opeq2i sneqi
      weq uneq2i lmod1 ) BDNZFENZUAZCOUBPBQZROUCPBBRBRQROUDPARUEZOUGPZIJAUBPZXB
      JSZUFZRZQZUHZUIXACXCXDFBRZBRQZRZQZUHXJHXAXNXIXCXAXMXHXAXLXGXDXAXLKFQZXBUJ
      ZKSZUKPZUTZIJXOXBXFUFZXGXAKXKQZXRUTZXLXSXAYAXBYBULZYBXLTZXAKYAXRXBXQYANXA
      XQXKTZXRXBNXQXKUMXAYEUAXRXKUKPZXBYEXRYFTXAXQXKUKUNUOXAYFXBNYEXAYFBXBWTWSY
      FBTFBEDUPUQWSBXBNWTBDURUSVAUSVAVBVCXAXKVDNWSYCYDVLFBVEWSWTVFXKBVDDYBVGVHV
      IXAKYAXPXRXAXPYAWTWSXPYATFBEDVJUQVKVMVNXSXTTXAIJKXOXBXRXFISXFXQIVOJVOVPVQ
      VRXAXOXETZXBXBTXTXGTXOVDNYGXAFVSXOFFRFRQZAYHVDGVTWAXAXBWDIJXOXBXEXBXFWBWC
      WEWFWGWHWIWTWSAWJNXJUINAEFGWKLMABXJDXIXDLMXEXBMSZUFZRZQXCXHYKXGYJXDIJLMXE
      XBXFYIXFILWPXFWDJMWPWLWMWNWOWQWRVBVA $.

    $( There is a (left) module (a _zero module_) which is not a (left) vector
       space.  (Contributed by AV, 29-Apr-2019.) $)
    lmod1zrnlvec $p |- ( ( I e. V /\ Z e. W ) -> M e/ LVec ) $=
      ( wcel wa cfv cdr wn clvec wnel cvv cnx csn cop cnzr csca wceq cbs cplusg
      clmod cmulr ctp tpex eqeltri lmodsca rng1nnzr df-nel sylib drngnzr adantl
      mp1i nsyl eqneltrrd intnand eqid islvec xchbinx sylibr ) BDIZFEIZJZCUEIZC
      UAKZLIZJZMCNOZVFVIVGVFAVHLAPIAVHUBVFAQUCKFRSZQUDKFFSFSRZSZQUFKVMSZUGPGVLV
      NVOUHUIBRBBSBSRFBSBSRACPHUJUPVEALIZMVDVEATIZVPVEATOVQMAEFGUKATULUMAUNUQUO
      URUSVKCNIVJCNULVHCVHUTVAVBVC $.
  $}

  $( Left modules exist.  (Contributed by AV, 29-Apr-2019.) $)
  lmodn0 $p |- LMod =/= (/) $=
    ( vi vz cv cvv wcel wa cnx cbs cfv csn cop cplusg cmulr ctp cvsca cun clmod
    csca vex eqid c0 wne pm3.2i lmod1zr ne0i mp2b ) ACZDEZBCZDEZFGHIZUGJKGLIZUG
    UGKUGKJKGRIUKUIJKULUIUIKUIKJZKGMIUMKNZKNGOIUIUGKUGKJKJPZQEQUAUBUHUJASBSUCUN
    UGUODDUIUNTUOTUDQUOUEUF $.

  ${
    zlmodzxzequa.z $e |- Z = ( ZZring freeLMod { 0 , 1 } ) $.
    zlmodzxzequa.o $e |- .0. = { <. 0 , 0 >. , <. 1 , 0 >. } $.
    zlmodzxzequa.t $e |- .xb = ( .s ` Z ) $.
    zlmodzxzequa.m $e |- .- = ( -g ` Z ) $.

    ${
      zlmodzxzequa.a $e |- A = { <. 0 , 3 >. , <. 1 , 6 >. } $.
      zlmodzxzequa.b $e |- B = { <. 0 , 2 >. , <. 1 , 4 >. } $.
      $( Example of an equation within the ` ZZ `-module ` ZZ X. ZZ ` (see
         example in [Roman] p. 112 for a linearly dependent set).  (Contributed
         by AV, 22-May-2019.)  (Revised by AV, 10-Jun-2019.) $)
      zlmodzxzequa $p |- ( ( 2 .xb A ) .- ( 3 .xb B ) ) = .0. $=
        ( cc0 c2 c3 co cop c6 cz wcel cmul cmin c1 c4 cpr caddc 3cn 3p3e6 eqtri
        2timesi 3t2e6 oveq12i subidi opeq2i 2t6m3t4e0 preq12i oveq2i wceq 2z 3z
        6cn 6nn nnzi zlmodzxzscm mp3an zmulcl mp2an zlmodzxzsub mp4an 3eqtr4i
        4z ) MNOUAPZONUAPZUBPZQZUCNRUAPZOUDUAPZUBPZQZUEZMMQZUCMQZUENACPZOBCPZDP
        ZEVOWAVSWBVNMMVNRRUBPMVLRVMRUBVLOOUFPROUGUJUHUIUKULRVAUMUIUNVRMUCUOUNUP
        WEMVLQUCVPQUEZMVMQUCVQQUEZDPZVTWCWFWDWGDWCNMOQUCRQUEZCPZWFAWINCKUQNSTZO
        STZRSTZWJWFURUSUTRVBVCZNORCFGIVDVEUIWDOMNQUCUDQUEZCPZWGBWOOCLUQWLWKUDST
        ZWPWGURUTUSVKONUDCFGIVDVEUIULVLSTZVMSTZVPSTZVQSTZWHVTURWKWLWRUSUTNOVFVG
        WLWKWSUTUSONVFVGWKWMWTUSWNNRVFVGWLWQXAUTVKOUDVFVGVLVMVPVQDFGJVHVIUIHVJ
        $.

      $( Example of a linearly dependent set whose elements are not linear
         combinations of the others, see note in [Roman] p. 112).  (Contributed
         by AV, 23-May-2019.)  (Revised by AV, 10-Jun-2019.) $)
      zlmodzxznm $p |- A. i e. ZZ ( ( i .xb A ) =/= B /\ ( i .xb B ) =/= A ) $=
        ( wne wcel cc0 c3 c1 c2 cvv cv co wa cz cmul cop c6 cpr c4 wo wi cprime
        wceq 3prm 2prm ztprmneprm mp3an23 2re 2lt3 ltneii eqneqall syl6com ax-1
        mpi eqcoms pm2.61ine olcd c0ex ovex pm3.2i opthneg mp1i mpbird 0ne1 a1i
        wb orcd jca opex w3a prnebg bicomd syl3anc oveq2i 3z zlmodzxzscm eqtrid
        6nn nnzi 3netr4d 2z 4z rgen ) DUAZACUBZBNZWNBCUBZANZUCDUDWNUDOZWPWRWSPW
        NQUEUBZUFZRWNUGUEUBZUFZUHZPSUFZRUIUFZUHZWOBWSXDXGNZXAXENZXAXFNZUCZXCXEN
        XCXFNUCZUJZWSXKXLWSXIXJWSXIPPNZWTSNZUJZWSXOXNWSXOUKWTSWSWTSUMZQSUMZXOWS
        QULOZSULOZXQXRUKUNUOQSWNUPUQXOSQSQUMZSQNZXOSQURUSUTZXOSQVAVDVEVBXOWSVCV
        FVGPTOZWTTOZUCZXIXPVPWSYDYEVHWNQUEVIVJZPWTPSTTVKVLVMWSXJPRNZWTUINZUJZWS
        YHYIYHWSVNVOZVQYFXJYJVPWSYGPWTRUITTVKVLVMVRVQWSXATOZXCTOZUCZXETOZXFTOZU
        CZXAXCNZXHXMVPYNWSYLYMPWTVSRXBVSVJVOYQWSYOYPPSVSRUIVSVJVOWSYRYHWTXBNZUJ
        ZWSYHYSYKVQYFYRYTVPWSYGPWTRXBTTVKVLVMYNYQYRVTXMXHXAXCXEXFTTTTWAWBWCVMWS
        WOWNPQUFZRUGUFZUHZCUBZXDAUUCWNCLWDWSQUDOUGUDOUUDXDUMWEUGWHWIWNQUGCGHJWF
        UQWGBXGUMWSMVOWJWSPWNSUEUBZUFZRWNUIUEUBZUFZUHZUUCWQAWSUUIUUCNZUUFUUANZU
        UFUUBNZUCZUUHUUANUUHUUBNUCZUJZWSUUMUUNWSUUKUULWSUUKXNUUEQNZUJZWSUUPXNWS
        UUPUKUUEQWSUUEQUMZYAUUPWSXTXSUURYAUKUOUNSQWNUPUQYAYBUUPYCUUPSQVAVDVBUUP
        WSVCVFVGYDUUETOZUCZUUKUUQVPWSYDUUSVHWNSUEVIVJZPUUEPQTTVKVLVMWSUULYHUUEU
        GNZUJZWSYHUVBYKVQUUTUULUVCVPWSUVAPUUERUGTTVKVLVMVRVQWSUUFTOZUUHTOZUCZUU
        ATOZUUBTOZUCZUUFUUHNZUUJUUOVPUVFWSUVDUVEPUUEVSRUUGVSVJVOUVIWSUVGUVHPQVS
        RUGVSVJVOWSUVJYHUUEUUGNZUJZWSYHUVKYKVQUUTUVJUVLVPWSUVAPUUERUUGTTVKVLVMU
        VFUVIUVJVTUUOUUJUUFUUHUUAUUBTTTTWAWBWCVMWSWQWNXGCUBZUUIBXGWNCMWDWSSUDOU
        IUDOUVMUUIUMWKWLWNSUICGHJWFUQWGAUUCUMWSLVOWJVRWM $.
    $}
  $}

  ${
    zlmodzxzldep.z $e |- Z = ( ZZring freeLMod { 0 , 1 } ) $.
    zlmodzxzldep.a $e |- A = { <. 0 , 3 >. , <. 1 , 6 >. } $.
    zlmodzxzldep.b $e |- B = { <. 0 , 2 >. , <. 1 , 4 >. } $.
    $( A and B are not equal.  (Contributed by AV, 24-May-2019.)  (Revised by
       AV, 10-Jun-2019.) $)
    zlmodzxzldeplem $p |- A =/= B $=
      ( wne cc0 c3 cop c1 c2 c4 cvv wcel wa wo opex pm3.2i mpbir cpr 2re gtneii
      c6 2lt3 olci c0ex 3ex opthne 0ne1 orci prneimg mp2 neeq12i ) ABGHIJZKUDJZ
      UAZHLJZKMJZUAZGZUONOZUPNOZPZURNOZUSNOZPZPUOURGZUOUSGZPZUPURGUPUSGPZQVAVDV
      GVBVCHIRKUDRSVEVFHLRKMRSSVJVKVHVIVHHHGZILGZQVMVLLIUBUEUCUFHIHLUGUHUITVIHK
      GZIMGZQVNVOUJUKHIKMUGUHUITSUKUOUPURUSNNNNULUMAUQBUTEFUNT $.

    ${
      zlmodzxzequap.o $e |- .0. = { <. 0 , 0 >. , <. 1 , 0 >. } $.
      zlmodzxzequap.m $e |- .+ = ( +g ` Z ) $.
      zlmodzxzequap.t $e |- .xb = ( .s ` Z ) $.
      $( Example of an equation within the ` ZZ `-module ` ZZ X. ZZ ` (see
         example in [Roman] p. 112 for a linearly dependent set), written as a
         sum.  (Contributed by AV, 24-May-2019.)  (Revised by AV,
         10-Jun-2019.) $)
      zlmodzxzequap $p |- ( ( 2 .xb A ) .+ ( -u 3 .xb B ) ) = .0. $=
        ( cc0 c2 c3 co cop c4 wcel cz cmul cneg caddc c1 c6 cpr mulneg1i oveq2i
        3cn 2cn cc wceq mulcli wa cmin negsub mulcomi subidi eqtri eqtrdi mp2an
        opeq2i 4cn 6cn negsubi 2t6m3t4e0 preq12i 2z 6nn nnzi zlmodzxzscm znegcl
        3z mp3an ax-mp 4z oveq12i zmulcl zlmodzxzadd mp4an 3eqtr4i ) MNOUAPZOUB
        ZNUAPZUCPZQZUDNUEUAPZWCRUAPZUCPZQZUFZMMQZUDMQZUFNADPZWCBDPZCPZEWFWLWJWM
        WEMMWEWBONUAPZUBZUCPZMWDWRWBUCONUIUJUGUHWBUKSZWQUKSZWSMULNOUJUIUMZONUIU
        JUMWTXAUNWSWBWQUOPZMWBWQUPXCWBWBUOPMWQWBWBUOONUIUJUQUHWBXBURUSUTVAUSVBW
        IMUDWIWGORUAPZUBZUCPZMWHXEWGUCORUIVCUGUHXFWGXDUOPMWGXDNUEUJVDUMORUIVCUM
        VEVFUSUSVBVGWPMWBQUDWGQUFZMWDQUDWHQUFZCPZWKWNXGWOXHCWNNMOQUDUEQUFZDPZXG
        AXJNDHUHNTSZOTSZUETSZXKXGULVHVMUEVIVJZNOUEDFGLVKVNUSWOWCMNQUDRQUFZDPZXH
        BXPWCDIUHWCTSZXLRTSZXQXHULXMXRVMOVLVOZVHVPWCNRDFGLVKVNUSVQWBTSZWDTSZWGT
        SZWHTSZXIWKULXLXMYAVHVMNOVRVAXRXLYBXTVHWCNVRVAXLXNYCVHXONUEVRVAXRXSYDXT
        VPWCRVRVAWBWDWGWHCFGKVSVTUSJWA $.
    $}

    ${
      zlmodzxzldeplem.f $e |- F = { <. A , 2 >. , <. B , -u 3 >. } $.
      $( Lemma 1 for ~ zlmodzxzldep .  (Contributed by AV, 24-May-2019.)
         (Revised by AV, 10-Jun-2019.) $)
      zlmodzxzldeplem1 $p |- F e. ( ZZ ^m { A , B } ) $=
        ( cz cvv wcel cpr prex wa wf c2 c3 cc0 cop a1i cmap co zex cneg wss wne
        c1 c6 eqeltri c4 pm3.2i 2z 3nn0 nn0negzi zlmodzxzldeplem w3a fprg feq1i
        sylibr syl3anc prssi mp2an fss sylancl elmapg mpbird ) IJKZABLZJKZCIVHU
        AUBKZUCABMVGVINZVJVHICOZVKVHPQUDZLZCOZVNIUEZVLVKAJKZBJKZNZPIKZVMIKZNZAB
        UFZVOVSVKVQVRARQSZUGUHSZLJFWDWEMUIBRPSZUGUJSZLJGWFWGMUIUKTWBVKVTWAULQUM
        UNZUKTWCVKABDEFGUOTVSWBWCUPVHVNAPSBVMSLZOVOABPVMJJIIUQVHVNCWIHURUSUTVTW
        AVPULWHPVMIVAVBVHVNICVCVDIVHCJJVEVFVB $.

      $( Lemma 2 for ~ zlmodzxzldep .  (Contributed by AV, 24-May-2019.)
         (Revised by AV, 30-Jul-2019.) $)
      zlmodzxzldeplem2 $p |- F finSupp 0 $=
        ( cz cpr cmap co wcel cc0 cfsupp wbr zlmodzxzldeplem1 cvv elmapi a1i
        cfn prfi c0ex fdmfifsupp ax-mp ) CIABJZKLMZCNOPABCDEFGHQUGUFICRNCIUFSUF
        UAMUGABUBTNRMUGUCTUDUE $.

      $d A x $.  $d B x $.  $d F x $.  $d Z x $.
      $( Lemma 3 for ~ zlmodzxzldep .  (Contributed by AV, 24-May-2019.)
         (Revised by AV, 10-Jun-2019.) $)
      zlmodzxzldeplem3 $p |- ( F ( linC ` Z ) { A , B } ) = ( 0g ` Z ) $=
        ( cpr cfv co cvv wcel wceq czring cc0 cz ax-mp cop c2 vx clinc cv cvsca
        cmpt cgsu cplusg c0g csca cbs cmap cpw c1 ovex eqeltri zlmodzxzldeplem1
        cfrlm clmod wa zlmodzxzlmod simpr eqcomd fveq2i zringbas eqtri eleqtrri
        eqcomi oveq1i c3 c6 c4 3z 6nn nnzi zlmodzxzel mp2an 2z anbi12i mpbir2an
        4z eleq1i prelpwi lincval mp3an ccmn wne lmodcmn adantr zlmodzxzldeplem
        w3a prex 3pm3.2i simpli elmapi prid1 ffvelcdm mpan2 mp2b lmodvscl prid2
        wf eqid pm3.2i fveq2 oveq12d gsumpr cneg fveq1i 2ex fvpr1 negex oveq12i
        id fvpr2 zlmodzxz0 zlmodzxzequap 3eqtri ) CABIZDUBJKZDUAXRUAUCZCJZXTDUD
        JZKZUEUFKZACJZAYBKZBCJZBYBKZDUGJZKZDUHJZDLMCDUIJZUJJZXRUKKZMXRDUJJZULMZ
        XSYDNDOPUMIZUQKLEOYQUQUNUOCQXRUKKZYNABCDEFGHUPZYMQXRUKYMOUJJZQYLOUJDURM
        ZOYLNZUSZYLONDEUTZUUCOYLUUAUUBVAZVBRVCQYTVDVGZVEVHVFAYOMZBYOMZUSZYPUUIP
        VISZUMVJSZIZYOMZPTSZUMVKSZIZYOMZVIQMVJQMUUMVLVJVMVNVIVJDEVOVPZTQMVKQMUU
        QVQVTTVKDEVOVPZUUGUUMUUHUUQAUULYOFWABUUPYOGWAVRVSABYOWBRUACDXRLWCWDDWEM
        ZALMZBLMZABWFZWJYFYOMZYHYOMZUSYDYJNUUCUUTUUDUUAUUTUUBDWGWHRUVAUVBUVCAUU
        LLFUUJUUKWKUOZBUUPLGUUNUUOWKUOZABDEFGWIZWLUVDUVEUUAYEYMMUUGUVDUUAUUBUUD
        WMZYEQYMCYRMZXRQCXAZYEQMZYSCQXRWNZUVKAXRMUVLABUVFWOXRQACWPWQWRYMYTQYLOU
        JOYLUUCUUBUUDUUERVGVCUUFVEZVFAUULYOFUURUOYEYBYLYMYODAYOXBZYLXBZYBXBZYMX
        BZWSWDUUAYGYMMUUHUVEUVIYGQYMUVJUVKYGQMZYSUVMUVKBXRMUVSABUVGWTXRQBCWPWQW
        RUVNVFBUUPYOGUUSUOYGYBYLYMYODBUVOUVPUVQUVRWSWDXCYCYOYFYHYIUADABLLUVOYIX
        BZXTANZYAYEXTAYBXTACXDUWAXMXEXTBNZYAYGXTBYBXTBCXDUWBXMXEXFWDYJTAYBKZVIX
        GZBYBKZYIKYKYFUWCYHUWEYIYETAYBYEAATSBUWDSIZJZTACUWFHXHUVCUWGTNUVHABTUWD
        UVFXIXJRVEVHYGUWDBYBYGBUWFJZUWDBCUWFHXHUVCUWHUWDNUVHABTUWDUVGVIXKXNRVEV
        HXLABYIYBYKDEFGPPSUMPSIZYKUWIDEUWIXBXOVGUVTUVQXPVEXQ $.

      $d A y $.  $d B y $.  $d F y $.
      $( Lemma 4 for ~ zlmodzxzldep .  (Contributed by AV, 24-May-2019.)
         (Revised by AV, 10-Jun-2019.) $)
      zlmodzxzldeplem4 $p |- E. y e. { A , B } ( F ` y ) =/= 0 $=
        ( cvv wcel cfv cc0 wne cpr c3 cop c2 wceq neeq1d cv c1 c6 eqeltri c4 wa
        wrex prex 2ne0 cneg fveq1i zlmodzxzldeplem 2ex fvpr1 mp1i eqtrid mpbiri
        wo orcd fveq2 rexprg mpbird mp2an ) BJKZCJKZAUAZDLZMNZABCOUGZBMPQZUBUCQ
        ZOJGVJVKUHUDZCMRQZUBUEQZOJHVMVNUHUDVDVEUFZVIBDLZMNZCDLZMNZURVOVQVSVOVQR
        MNUIVOVPRMVOVPBBRQCPUJZQOZLZRBDWAIUKBCNWBRSVOBCEFGHULBCRVTVLUMUNUOUPTUQ
        USVHVQVSABCJJVFBSVGVPMVFBDUTTVFCSVGVRMVFCDUTTVAVBVC $.
    $}

    $d A x y $.  $d B x y $.  $d Z x y $.
    $( { A , B } is a linearly dependent set within the ` ZZ `-module
       ` ZZ X. ZZ ` (see example in [Roman] p. 112).  (Contributed by AV,
       22-May-2019.)  (Revised by AV, 10-Jun-2019.) $)
    zlmodzxzldep $p |- { A , B } linDepS Z $=
      ( vx vy cpr cc0 cfv co wceq cz c2 cop c3 wcel mp2an czring clindeps clinc
      wbr cv cfsupp c0g wrex zlmodzxzldeplem1 zlmodzxzldeplem2 zlmodzxzldeplem3
      wne w3a cmap cneg eqid zlmodzxzldeplem4 3pm3.2i breq1 oveq1 eqeq1d neeq1d
      fveq1 rexbidv 3anbi123d rspcev cvv cbs cpw wb c1 cfrlm ovex eqeltri c6 3z
      6nn nnzi zlmodzxzel c4 2z prelpwi clmod csca zlmodzxzlmod simpri zringbas
      4z zring0 islindeps mpbir ) ABIZCUAUCZGUDZJUEUCZWMWKCUBKZLZCUFKZMZHUDZWMK
      ZJUKZHWKUGZULZGNWKUMLZUGZAOPBQUNPIZXDRXFJUEUCZXFWKWOLZWQMZWSXFKZJUKZHWKUG
      ZULZXEABXFCDEFXFUOZUHXGXIXLABXFCDEFXNUIABXFCDEFXNUJHABXFCDEFXNUPUQXCXMGXF
      XDWMXFMZWNXGWRXIXBXLWMXFJUEURXOWPXHWQWMXFWKWOUSUTXOXAXKHWKXOWTXJJWSWMXFVB
      VAVCVDVESCVFRWKCVGKZVHRZWLXEVICTJVJIZVKLVFDTXRVKVLVMAXPRBXPRXQAJQPVJVNPIZ
      XPEQNRVNNRXSXPRVOVNVPVQQVNCDVRSVMBJOPVJVSPIZXPFONRVSNRXTXPRVTWGOVSCDVRSVM
      ABXPWASHXPTWKGNCVFJWQXPUOWQUOCWBRTCWCKMCDWDWEWFWHWISWJ $.

    $d A i $.  $d B i $.  $d F i $.  $d Z i $.
    $( Lemma 1 for ~ ldepsnlinc .  (Contributed by AV, 25-May-2019.)  (Revised
       by AV, 10-Jun-2019.) $)
    ldepsnlinclem1 $p |- ( F e. ( ( Base ` ZZring ) ^m { B } )
                             -> ( F ( linC ` Z ) { B } ) =/= A ) $=
      ( vi czring cfv co wcel wne cop wceq wa cc0 c2 cz eqid cbs csn cmap clinc
      wf elmapi c1 c4 cpr cvv prex eqeltri fsn2 cvsca oveq1 adantl zlmodzxzlmod
      clmod csca simpli a1i 2z zlmodzxzel mp2an simpl simpri lincvalsng syl3anc
      4z eqtrd cv wral wi zlmodzxznm r19.26 neeq1d rspcv zringbas eqcomi eleq2i
      csg birani syl11 sylbi ax-mp eqnetrd syl ) CIUAJZBUBZUCKLWIWHCUEZCWIDUDJZ
      KZAMZCWHWIUFWJBCJZWHLZCBWNNUBZOZPZWMBWHCBQRNZUGUHNZUIZUJGWSWTUKULUMWRWLWN
      BDUNJZKZAWRWLWPWIWKKZXCWQWLXDOWOCWPWIWKUOUPWRDURLZBDUAJZLZWOXDXCOXEWRXEID
      USJOZDEUQZUTVAXGWRBXAXFGRSLUHSLXAXFLVBVIRUHDEVCVDULVAWOWQVEXFWHIXBDBWNXFT
      XEXHXIVFWHTXBTZVGVHVJHVKZAXBKBMZXKBXBKZAMZPHSVLZWRXCAMZVMZABXBHDWAJZQQNUG
      QNUIZDEXSTXJXRTFGVNXOXLHSVLZXNHSVLZPXQXLXNHSVOYAXQXTWNSLZYAXPWRXNXPHWNSXK
      WNOXMXCAXKWNBXBUOVPVQWOYBWQWHSWNSWHVRVSVTWBWCUPWDWEWFWDWG $.

    $( Lemma 2 for ~ ldepsnlinc .  (Contributed by AV, 25-May-2019.)  (Revised
       by AV, 10-Jun-2019.) $)
    ldepsnlinclem2 $p |- ( F e. ( ( Base ` ZZring ) ^m { A } )
                             -> ( F ( linC ` Z ) { A } ) =/= B ) $=
      ( vi czring cfv co wcel wne cop wceq wa cc0 c6 cz eqid cbs csn cmap clinc
      wf elmapi c3 c1 cpr cvv prex eqeltri fsn2 cvsca oveq1 adantl zlmodzxzlmod
      clmod csca simpli a1i 6nn nnzi zlmodzxzel mp2an simpri lincvalsng syl3anc
      3z simpl eqtrd cv wral csg zlmodzxznm r19.26 neeq1d rspcv zringbas eqcomi
      wi eleq2i birani syl11 adantr sylbi ax-mp eqnetrd syl ) CIUAJZAUBZUCKLWKW
      JCUEZCWKDUDJZKZBMZCWJWKUFWLACJZWJLZCAWPNUBZOZPZWOAWJCAQUGNZUHRNZUIZUJFXAX
      BUKULUMWTWNWPADUNJZKZBWTWNWRWKWMKZXEWSWNXFOWQCWRWKWMUOUPWTDURLZADUAJZLZWQ
      XFXEOXGWTXGIDUSJOZDEUQZUTVAXIWTAXCXHFUGSLRSLXCXHLVIRVBVCUGRDEVDVEULVAWQWS
      VJXHWJIXDDAWPXHTXGXJXKVFWJTXDTZVGVHVKHVLZAXDKZBMZXMBXDKAMZPHSVMZWTXEBMZWA
      ZABXDHDVNJZQQNUHQNUIZDEYATXLXTTFGVOXQXOHSVMZXPHSVMZPXSXOXPHSVPYBXSYCWPSLZ
      YBXRWTXOXRHWPSXMWPOXNXEBXMWPAXDUOVQVRWQYDWSWJSWPSWJVSVTWBWCWDWEWFWGWHWFWI
      $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Differences between (left) modules and (left) vector spaces
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The class of all (left) vector spaces is a proper subclass of the class of
     all (left) modules.  Although it is obvious (and proven by ~ lveclmod )
     that every left vector space is a left module, there is (at least) one
     left module which is no left vector space, for example the zero module
     over the zero ring, see ~ lmod1zrnlvec .  (Contributed by AV,
     29-Apr-2019.) $)
  lvecpsslmod $p |- LVec C. LMod $=
    ( vv vi vz clvec clmod wpss wss wne cv lveclmod cvv wcel wa cnx cfv csn cop
    ctp vex eqid ssriv cbs cplusg csca cmulr cun wn pm3.2i lmod1zr lmod1zrnlvec
    cvsca wnel df-nel sylib jca nelne1 necomd mp2b df-pss mpbir2an ) DEFDEGDEHZ
    ADEAIJUABIZKLZCIZKLZMZNUBOZVBPQNUCOZVBVBQVBQPQNUDOVGVDPQVHVDVDQVDQPZQNUEOVI
    QRZQRNUKOVDVBQVBQPQPUFZELZVKDLUGZMZVAVCVEBSCSUHVFVLVMVJVBVKKKVDVJTZVKTZUIVF
    VKDULVMVJVBVKKKVDVOVPUJVKDUMUNUOVNEDVKEDUPUQURDEUSUT $.

  ${
    $d f m s v $.
    $( The reverse implication of ~ islindeps2 does not hold for arbitrary
       (left) modules, see note in [Roman] p. 112:  "... if a nontrivial linear
       combination of the elements ... in an R-module M is 0, ... where not all
       of the coefficients are 0, then we cannot conclude ... that one of the
       elements ... is a linear combination of the others."  This means that
       there is at least one left module having a linearly dependent subset in
       which there is at least one element which is not a linear combination of
       the other elements of this subset.  Such a left module can be
       constructed by using ~ zlmodzxzequa and ~ zlmodzxznm .  (Contributed by
       AV, 25-May-2019.)  (Revised by AV, 30-Jul-2019.) $)
    ldepsnlinc $p |- E. m e. LMod E. s e. ~P ( Base ` m ) ( s linDepS m
            /\ A. v e. s A. f e. ( ( Base ` ( Scalar ` m ) ) ^m ( s \ { v } ) )
               ( f finSupp ( 0g ` ( Scalar ` m ) )
                 -> ( f ( linC ` m ) ( s \ { v } ) ) =/= v ) ) $=
      ( czring cpr co wcel clindeps wbr cfv wne cbs cmap wral wceq mp2an oveq2d
      wi raleqbidv cc0 c1 cfrlm clmod cv csca c0g cfsupp csn cdif clinc wa wrex
      cpw eqid zlmodzxzlmod simpli c3 cop c6 c2 c4 cz 3z 6nn nnzi zlmodzxzel 2z
      prelpwi zlmodzxzldep ldepsnlinclem1 simpr eqcomd fveq2i oveq1i eleq2s a1d
      4z ax-mp rgen ldepsnlinclem2 prex difeq2d zlmodzxzldeplem difprsn1 eqtrdi
      sneq id neeq12d imbi2d difprsn2 ralpr mpbir2an pm3.2i breq1 difeq1 neeq1d
      anbi12d rspcev fveq2 pweqd 2fveq3 oveq1d breq2d imbi12d ralbidv rexeqbidv
      breq2 oveqd ) EUAUBFUCGZUDHZDUEZXJIJZBUEZXJUFKZUGKZUHJZXNXLAUEZUIZUJZXJUK
      KZGZXRLZSZBXOMKZXTNGZOZAXLOZULZDXJMKZUNZUMZXLCUEZIJZXNYMUFKZUGKZUHJZXNXTY
      MUKKZGZXRLZSZBYOMKZXTNGZOZAXLOZULZDYMMKZUNZUMZCUDUMXKEXOPZXJXJUOZUPZUQUAU
      RUSZUBUTUSZFZUAVAUSZUBVBUSZFZFZYKHZUUSXJIJZXQXNUUSXSUJZYAGZXRLZSZBYEUVBNG
      ZOZAUUSOZULZYLUUOYJHZUURYJHZUUTURVCHUTVCHUVJVDUTVEVFURUTXJUUKVGQVAVCHVBVC
      HUVKVHVRVAVBXJUUKVGQUUOUURYJVIQUVAUVHUUOUURXJUUKUUOUOZUURUOZVJUVHXQXNUURU
      IZYAGZUUOLZSZBYEUVNNGZOZXQXNUUOUIZYAGZUURLZSZBYEUVTNGZOZUVQBUVRXNUVRHUVPX
      QUVPXNEMKZUVNNGUVRUUOUURXNXJUUKUVLUVMVKYEUWFUVNNXOEMXKUUJULZXOEPUULUWGEXO
      XKUUJVLVMVSVNZVOVPVQVTUWCBUWDXNUWDHUWBXQUWBXNUWFUVTNGUWDUUOUURXNXJUUKUVLU
      VMWAYEUWFUVTNUWHVOVPVQVTUVGUVSUWEAUUOUURUUMUUNWBUUPUUQWBXRUUOPZUVEUVQBUVF
      UVRUWIUVBUVNYENUWIUVBUUSUVTUJZUVNUWIXSUVTUUSXRUUOWGWCUUOUURLZUWJUVNPUUOUU
      RXJUUKUVLUVMWDZUUOUURWEVSWFZRUWIUVDUVPXQUWIUVCUVOXRUUOUWIUVBUVNXNYAUWMRUW
      IWHWIWJTXRUURPZUVEUWCBUVFUWDUWNUVBUVTYENUWNUVBUUSUVNUJZUVTUWNXSUVNUUSXRUU
      RWGWCUWKUWOUVTPUWLUUOUURWKVSWFZRUWNUVDUWBXQUWNUVCUWAXRUURUWNUVBUVTXNYAUWP
      RUWNWHWIWJTWLWMWNYIUVIDUUSYKXLUUSPZXMUVAYHUVHXLUUSXJIWOUWQYGUVGAXLUUSUWQW
      HUWQYDUVEBYFUVFUWQXTUVBYENXLUUSXSWPZRUWQYCUVDXQUWQYBUVCXRUWQXTUVBXNYAUWRR
      WQWJTTWRWSQUUIYLCXJUDYMXJPZUUFYIDUUHYKUWSUUGYJYMXJMWTXAUWSYNXMUUEYHYMXJXL
      IXHUWSUUDYGAXLUWSUUAYDBUUCYFUWSUUBYEXTNYMXJMUFXBXCUWSYQXQYTYCUWSYPXPXNUHY
      MXJUGUFXBXDUWSYSYBXRUWSYRYAXNXTYMXJUKWTXIWQXETXFWRXGWSQ $.

    $( For (left) vector spaces, ~ isldepslvec2 provides an alternative
       definition of being a linearly dependent subset, whereas ~ ldepsnlinc
       indicates that there is not an analogous alternative definition for
       arbitrary (left) modules.  (Contributed by AV, 25-May-2019.)  (Revised
       by AV, 30-Jul-2019.) $)
    ldepslinc $p |- ( A. m e. LVec A. s e. ~P ( Base ` m ) ( s linDepS m
           <-> E. v e. s E. f e. ( ( Base ` ( Scalar ` m ) ) ^m ( s \ { v } ) )
               ( f finSupp ( 0g ` ( Scalar ` m ) )
                 /\ ( f ( linC ` m ) ( s \ { v } ) ) = v ) )
                      /\ -. A. m e. LMod A. s e. ~P ( Base ` m ) ( s linDepS m
           <-> E. v e. s E. f e. ( ( Base ` ( Scalar ` m ) ) ^m ( s \ { v } ) )
                             ( f finSupp ( 0g ` ( Scalar ` m ) )
                               /\ ( f ( linC ` m ) ( s \ { v } ) ) = v ) ) ) $=
      ( cv wbr cfv c0g co wa cbs wrex wral clvec clmod wn eqid wo bitri rexbii
      clindeps csca cfsupp csn cdif clinc wceq cmap wb wcel isldepslvec2 bicomd
      cpw rgen2 wne wi ldepsnlinc df-ne imbi2i imnan ralbii ralnex 2rexbii mpbi
      anbi2i orci r19.43 mpbir xor bicomi rexnal pm3.2i ) DEZCEZUAFZBEZVNUBGZHG
      ZUCFZVPVMAEZUDUEZVNUFGIZVTUGZJZBVQKGZWAUHIZLZAVMLZUIZDVNKGZUMZMZCNMWLCOMP
      ZWICDNWKVNNUJVMWKUJJWHVOWJVQVMBWEVNVRVNHGZAWJQWNQVQQWEQVRQUKULUNVOWHPZJZW
      HVOPJZRZDWKLZCOLZWMWTWPDWKLZWQDWKLZRZCOLZXDXACOLZXBCOLZRXEXFVOVSWBVTUOZUP
      ZBWFMZAVMMZJZDWKLCOLXEABCDUQXKWPCDOWKXJWOVOXJWGPZAVMMWOXIXLAVMXIWDPZBWFMX
      LXHXMBWFXHVSWCPZUPXMXGXNVSWBVTURUSVSWCUTSVAWDBWFVBSVAWGAVMVBSVEVCVDVFXAXB
      COVGVHWSXCCOWPWQDWKVGTVHWTWLPZCOLWMWSXOCOWSWIPZDWKLXOWRXPDWKXPWRVOWHVIVJT
      WIDWKVKSTWLCOVKSVDVL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Complexity theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Auxiliary theorems
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d F x $.  $d V x $.  $d W x $.  $d Z x $.
    $( If the range of a function does not contain the zero, the support of the
       function equals its domain.  (Contributed by AV, 20-May-2020.) $)
    suppdm $p |- ( ( ( Fun F /\ F e. V /\ Z e. W ) /\ Z e/ ran F )
                   -> ( F supp Z ) = dom F ) $=
      ( vx wfun wcel w3a crn wnel wa csupp co cv cfv wne cdm crab wceq suppval1
      adantr wral wn df-nel fvelrn 3ad2antl1 eleq1 syl5ibrcom necon3bd biimtrid
      wb eqcoms impancom ralrimiv rabid2 sylibr eqtr4d ) AFZABGZDCGZHZDAIZJZKZA
      DLMZENZAOZDPZEAQZRZVIVAVEVJSVCEBCADTUAVDVHEVIUBVIVJSVDVHEVIVAVFVIGZVCVHVC
      DVBGZUCVAVKKZVHDVBUDVMVLVGDVMVLVGDSVGVBGZURUSVKVNUTVFAUEUFVLVNUKDVGDVGVBU
      GULUHUIUJUMUNVHEVIUOUPUQ $.
  $}

  $( An integer greater than 1 is a complex number not equal to 0 or 1.
     (Contributed by AV, 23-May-2020.) $)
  eluz2cnn0n1 $p |- ( B e. ( ZZ>= ` 2 ) -> B e. ( CC \ { 0 , 1 } ) ) $=
    ( cn wcel c1 wne wa cc cc0 w3a c2 cuz cfv cdif nncn adantr nnne0 simpr 3jca
    cpr eluz2b3 eldifpr 3imtr4i ) ABCZADEZFZAGCZAHEZUDIAJKLCAGHDSMCUEUFUGUDUCUF
    UDANOUCUGUDAPOUCUDQRATAGHDUAUB $.

  $( The ratio of a real number to a positive real number is greater than or
     equal to 1 iff the divisor (the positive real number) is less than or
     equal to the dividend (the real number).  (Contributed by AV,
     26-May-2020.) $)
  divge1b $p |- ( ( A e. RR+ /\ B e. RR ) -> ( A <_ B <-> 1 <_ ( B / A ) ) ) $=
    ( crp wcel cr wa cle c1 cmul co cdiv wceq rpcn mullidd eqcomd adantr breq1d
    wbr cc0 clt wb 1red simpr rpregt0 lemuldiv syl3anc bitrd ) ACDZBEDZFZABGRHA
    IJZBGRZHBAKJGRZUJAUKBGUHAUKLUIUHUKAUHAAMNOPQUJHEDUIAEDSATRFZULUMUAUJUBUHUIU
    CUHUNUIAUDPHBAUEUFUG $.

  $( The ratio of a real number to a positive real number is greater than 1 iff
     the divisor (the positive real number) is less than the dividend (the real
     number).  (Contributed by AV, 30-May-2020.) $)
  divgt1b $p |- ( ( A e. RR+ /\ B e. RR ) -> ( A < B <-> 1 < ( B / A ) ) ) $=
    ( crp wcel cr wa clt wbr c1 cmul cdiv rpcn adantr mullidd eqcomd breq1d cc0
    co cc wb 1red simpr rpregt0 ltmuldiv syl3anc bitrd ) ACDZBEDZFZABGHIAJRZBGH
    ZIBAKRGHZUIAUJBGUIUJAUIAUGASDUHALMNOPUIIEDUHAEDQAGHFZUKULTUIUAUGUHUBUGUMUHA
    UCMIBAUDUEUF $.

  $( Equivalence for the "less than" relation between differences and sums.
     (Contributed by AV, 6-Jun-2020.) $)
  ltsubaddb $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) )
                    -> ( ( A - C ) < ( B - D ) <-> ( A + D ) < ( B + C ) ) ) $=
    ( cr wcel wa cmin co caddc clt wbr simplr recnd simprl simprr eqcomd breq2d
    addsubd simpll resubcl ad2ant2l ltsubaddd readdcl ad2ant2lr ltaddsubd
    3bitr4d ) AEFZBEFZGZCEFZDEFZGZGZABDHIZCJIZKLABCJIZDHIZKLACHIUOKLADJIUQKLUNU
    PURAKUNURUPUNBCDUNBUHUIUMMNUNCUJUKULOZNUNDUJUKULPZNSQRUNACUOUHUIUMTZUSUIULU
    OEFUHUKBDUAUBUCUNADUQVAUTUIUKUQEFUHULBCUDUEUFUG $.

  $( Equivalence for the "less than" relation between differences.
     (Contributed by AV, 6-Jun-2020.) $)
  ltsubsubb $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) )
                    -> ( ( A - C ) < ( B - D ) <-> ( A - B ) < ( C - D ) ) ) $=
    ( cr wcel wa cmin co caddc clt wbr cc wceq simprl simprr simplr w3a resubcl
    recnd subadd23 eqcomd syl3anc breq2d ad2ant2l ltsubadd2d ltsubaddd 3bitr4d
    simpll adantl ) AEFZBEFZGZCEFZDEFZGZGZACBDHIZJIZKLACDHIZBJIZKLACHIURKLABHIU
    TKLUQUSVAAKUQCMFZDMFZBMFZUSVANUQCUMUNUOOZTUQDUMUNUOPTUQBUKULUPQZTVBVCVDRVAU
    SCDBUAUBUCUDUQACURUKULUPUIZVEULUOUREFUKUNBDSUEUFUQABUTVGVFUPUTEFUMCDSUJUGUH
    $.

  $( Equivalence for the "less than" relation between differences and sums.
     (Contributed by AV, 6-Jun-2020.) $)
  ltsubadd2b $p |- ( ( ( A e. RR /\ B e. RR ) /\ ( C e. RR /\ D e. RR ) )
                    -> ( ( D - C ) < ( B - A ) <-> ( A + D ) < ( B + C ) ) ) $=
    ( cr wcel wa cmin co caddc clt wbr simpr recnd adantr adantl addsubd eqcomd
    cc simpl breq2d simprr simprl resubcl ancoms ltsubaddd ad2ant2lr ltaddsub2d
    readdcl 3bitr4d ) AEFZBEFZGZCEFZDEFZGZGZDBAHIZCJIZKLDBCJIZAHIZKLDCHIURKLADJ
    IUTKLUQUSVADKUQVAUSUQBCAUMBSFUPUMBUKULMNOUPCSFUMUPCUNUOTNPUMASFUPUMAUKULTZN
    OQRUAUQDCURUMUNUOUBZUMUNUOUCUMUREFZUPULUKVDBAUDUEOUFUQADUTUMUKUPVBOVCULUNUT
    EFUKUOBCUIUGUHUJ $.

  $( Distribution of division over subtraction by 1.  (Contributed by AV,
     6-Jun-2020.) $)
  divsub1dir $p |- ( ( A e. CC /\ B e. CC /\ B =/= 0 )
                     -> ( ( A / B ) - 1 ) = ( ( A - B ) / B ) ) $=
    ( cc wcel cc0 wne w3a cdiv co c1 cmin wa wceq 3simpc divid eqcomd divsubdir
    syl oveq2d syld3an3 eqtr4d ) ACDZBCDZBEFZGZABHIZJKIUFBBHIZKIZABKIBHIZUEJUGU
    FKUEUGJUEUCUDLZUGJMUBUCUDNZBORPSUBUCUDUJUIUHMUKABBQTUA $.

  $( An integer greater than 1 to the power of a negative integer is in the
     closed-below, open-above interval between 0 and 1.  (Contributed by AV,
     24-May-2020.) $)
  expnegico01 $p |- ( ( B e. ( ZZ>= ` 2 ) /\ N e. ZZ /\ N < 0 )
                      -> ( B ^ N ) e. ( 0 [,) 1 ) ) $=
    ( c2 cuz cfv wcel cz cc0 clt wbr w3a cexp co c1 cico cr cle adantr 3ad2ant1
    wa eluzelre eluz2nn nnne0d simpr 3jca 3adant3 reexpclz 0red simp2 reexpclzd
    wne syl nngt0d expgt0 syl3anc ltled eluz2gt1 ltexp2a syl32anc wceq eluzelcn
    0zd simp3 exp0d eqcomd breqtrrd cxr wb 0re 1xr pm3.2i elico2 mp1i mpbir3and
    ) ACDEFZBGFZBHIJZKZABLMZHNOMFZVSPFZHVSQJZVSNIJZVRAPFZAHUKZVPKZWAVOVPWFVQVOV
    PTWDWEVPVOWDVPCAUAZRVOWEVPVOAAUBZUCZRVOVPUDUEUFABUGULVRHVSVRUHVRABVOVPWDVQW
    GSZVOVPWEVQWISVOVPVQUIZUJVRWDVPHAIJZHVSIJWJWKVOVPWLVQVOAWHUMSABUNUOUPVRVSAH
    LMZNIVRWDVPHGFNAIJZVQVSWMIJWJWKVRVBVOVPWNVQAUQSVOVPVQVCABHURUSVOVPNWMUTVQVO
    WMNVOACAVAVDVESVFHPFZNVGFZTVTWAWBWCKVHVRWOWPVIVJVKHNVSVLVMVN $.

  $( An element of a half-open integer interval is either equal to the left
     bound of the interval or an element of a half-open integer interval with a
     lower bound increased by 1.  (Contributed by AV, 2-Jun-2020.) $)
  elfzolborelfzop1 $p |- ( K e. ( M ..^ N )
                           -> ( K = M \/ K e. ( ( M + 1 ) ..^ N ) ) ) $=
    ( cfzo co wcel cuz cfv cz clt wbr w3a wceq wo elfzo2 cle wi eluz2 wa cr zre
    c1 caddc wb leloe syl2an peano2z adantr ad2antrl simprlr simpl zltp1le 3jca
    mpbid simplrr simpr 3anbi1i bitri syl3anbrc olcd exp31 orc eqcoms 2a1d jaoi
    expd com12 sylbid 3impia sylbi 3imp ) ABCDEFABGHFZCIFZACJKZLABMZABUBUCEZCDE
    FZNZABCOVLVMVNVRVLBIFZAIFZBAPKZLVMVNVRQZQZBARVSVTWAWCVSVTSZWABAJKZBAMZNZWCV
    SBTFATFWAWGUDVTBUAAUABAUEUFWGWDWCWGWDVMWBWEWDVMSZWBQWFWEWHVNVRWEWHSZVNSZVQV
    OWJVPIFZVTVPAPKZLZVMVNVQWIWMVNWIWKVTWLWDWKWEVMVSWKVTBUGUHUIWEVSVTVMUJWIWEWL
    WEWHUKWDWEWLUDWEVMBAULUIUNUMUHWEWDVMVNUOWIVNUPVQAVPGHFZVMVNLWMVMVNLAVPCOWNW
    MVMVNVPARUQURUSUTVAWFVRWHVNVRABVOVQVBVCVDVEVFVGVHVIVJVKVJ $.

  $( 2 to the power of a positive integer decreased by 1 is less than or equal
     to 2 to the power of the integer minus 1.  (Contributed by AV,
     30-May-2020.) $)
  pw2m1lepw2m1 $p |- ( I e. NN -> ( 2 ^ ( I - 1 ) ) <_ ( ( 2 ^ I ) - 1 ) ) $=
    ( cn wcel c2 c1 cmin co cexp clt wbr cle cdiv 1lt2 nncn 1cnd 2cn cz syl2anc
    a1i wb nncand oveq2d cc cc0 wne 2ne0 nnz peano2zm expsubd wceq exp1 3eqtr3d
    syl breqtrrid crp cr 2nn nnm1nn0 nnexpcld nnrpd cn0 2z nnnn0 zexpcl sylancr
    mp1i zred divgt1b mpbird nnzd zltlem1 mpbid ) ABCZDAEFGZHGZDAHGZIJZVOVPEFGK
    JZVMVQEVPVOLGZIJZVMEDVSIMVMDAVNFGZHGDEHGZVSDVMWAEDHVMAEANVMOUAUBVMDAVNDUCCZ
    VMPSDUDUEVMUFSVMAQCVNQCAUGZAUHUMWDUIWCWBDUJVMPDUKVFULUNVMVOUOCVPUPCVQVTTVMV
    OVMDVNDBCVMUQSAURUSZUTVMVPVMDQCAVACVPQCZVBAVCDAVDVEZVGVOVPVHRVIVMVOQCWFVQVR
    TVMVOWEVJWGVOVPVKRVL $.

  $( If an integer is between another integer and its predecessor, the integer
     is equal to the other integer.  (Contributed by AV, 7-Jun-2020.) $)
  zgtp1leeq $p |- ( ( I e. ZZ /\ A e. ZZ )
                      -> ( ( ( A - 1 ) < I /\ I <_ A ) -> I = A ) ) $=
    ( cz wcel wa c1 cmin co clt wbr cle wceq simprr wi wb zlem1lt ancoms adantr
    cr zre biimprcd impcom letri3 syl2an mpbir2and ex ) BCDZACDZEZAFGHBIJZBAKJZ
    EZBALZUIULEUMUKABKJZUIUJUKMULUIUNUJUIUNNUKUIUNUJUHUGUNUJOABPQUARUBUIUMUKUNE
    OZULUGBSDASDUOUHBTATBAUCUDRUEUF $.

  $( An integer can be moved in and out of the floor of a difference.
     (Contributed by AV, 29-May-2020.) $)
  flsubz $p |- ( ( A e. RR /\ N e. ZZ ) -> ( |_ ` ( A - N ) ) =
                ( ( |_ ` A ) - N ) ) $=
    ( cr wcel cz wa cmin co cfl cfv cneg caddc cc wceq zcn negsub syl2an eqcomd
    recn fveq2d znegcl fladdz sylan2 reflcl recnd 3eqtrd ) ACDZBEDZFZABGHZIJABK
    ZLHZIJZAIJZUKLHZUNBGHZUIUJULIUIULUJUGAMDBMDZULUJNUHASBOZABPQRTUHUGUKEDUMUON
    BUAAUKUBUCUGUNMDUQUOUPNUHUGUNAUDUEURUNBPQUF $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Even and odd integers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d N m $.
    $( For each odd nonnegative integer there is a nonnegative integer which,
       multiplied by 2 and increased by 1, results in the odd nonnegative
       integer.  (Contributed by AV, 30-May-2020.) $)
    nn0onn0ex $p |- ( ( N e. NN0 /\ ( ( N + 1 ) / 2 ) e. NN0 )
                      -> E. m e. NN0 N = ( ( 2 x. m ) + 1 ) ) $=
      ( wcel c1 caddc co c2 cdiv cmin cv cmul wceq wrex nn0o wa simpr oveq1d cc
      cn0 syl wb oveq2 eqeq2d adantl nn0cn peano2cnm 2cnd cc0 wne 2ne0 divcan2d
      a1i npcan1 eqtr2d adantr rspcedvd syldan ) BSCZBDEFGHFSCBDIFZGHFZSCZBGAJZ
      KFZDEFZLZASMBNURVAOZVEBGUTKFZDEFZLZAUTSURVAPVBUTLZVEVIUAVFVJVDVHBVJVCVGDE
      VBUTGKUBQUCUDURVIVAURVHUSDEFZBURVGUSDEURUSGURBRCZUSRCBUEZBUFTURUGGUHUIURU
      JULUKQURVLVKBLVMBUMTUNUOUPUQ $.

    $( For each even nonnegative integer there is a nonnegative integer which,
       multiplied by 2, results in the even nonnegative integer.  (Contributed
       by AV, 30-May-2020.) $)
    nn0enn0ex $p |- ( ( N e. NN0 /\ ( N / 2 ) e. NN0 )
                      -> E. m e. NN0 N = ( 2 x. m ) ) $=
      ( cn0 wcel c2 cdiv co wa cv cmul wceq simpr oveq2 adantl eqeq2d cc0 nn0cn
      cc wne 2cnd 2ne0 a1i w3a divcan2 eqcomd syl3anc adantr rspcedvd ) BCDZBEF
      GZCDZHZBEAIZJGZKBEUJJGZKZAUJCUIUKLULUMUJKZHUNUOBUQUNUOKULUMUJEJMNOUIUPUKU
      IBRDZERDZEPSZUPBQUITUTUIUAUBURUSUTUCUOBBEUDUEUFUGUH $.

    $( For each even positive integer there is a positive integer which,
       multiplied by 2, results in the even positive integer.  (Contributed by
       AV, 5-Jun-2023.) $)
    nnennex $p |- ( ( N e. NN /\ ( N / 2 ) e. NN )
                    -> E. m e. NN N = ( 2 x. m ) ) $=
      ( cn wcel c2 cdiv co wa cv cmul wceq simpr wb oveq2 eqeq2d adantl cc0 wne
      cc nncn 2cnd 2ne0 a1i w3a divcan2 eqcomd syl3anc adantr rspcedvd ) BCDZBE
      FGZCDZHZBEAIZJGZKZBEUKJGZKZAUKCUJULLUNUKKZUPURMUMUSUOUQBUNUKEJNOPUJURULUJ
      BSDZESDZEQRZURBTUJUAVBUJUBUCUTVAVBUDUQBBEUEUFUGUHUI $.
  $}

  $( A positive integer is even or odd.  (Contributed by AV, 30-May-2020.) $)
  nneop $p |- ( N e. NN
                -> ( ( N / 2 ) e. NN \/ ( ( N + 1 ) / 2 ) e. NN ) ) $=
    ( cn wcel c1 caddc co c2 cdiv wn nneo biimprd orrd orcomd ) ABCZADEFGHFBCZA
    GHFBCZNOPNPOIAJKLM $.

  $( A positive integer is even or odd.  (Contributed by AV, 30-May-2020.) $)
  nneom $p |- ( N e. NN
                -> ( ( N / 2 ) e. NN \/ ( ( N - 1 ) / 2 ) e. NN0 ) ) $=
    ( cn wcel c2 cdiv co c1 caddc wo cmin cn0 nneop nnnn0 nn0o syl2an ex orim2d
    mpd ) ABCZADEFBCZAGHFDEFZBCZITAGJFDEFKCZIALSUBUCTSUBUCSAKCUAKCUCUBAMUAMANOP
    QR $.

  $( A nonnegative integer is even or odd.  (Contributed by AV,
     27-May-2020.) $)
  nn0eo $p |- ( N e. NN0
                -> ( ( N / 2 ) e. NN0 \/ ( ( N + 1 ) / 2 ) e. NN0 ) ) $=
    ( cn0 wcel c2 cdiv co cz c1 wo cc0 cle wbr simpr a1i divge0 syl22anc adantr
    wa cr elnn0z caddc nn0z zeo syl clt nn0re nn0ge0 2pos sylanbrc ex peano2nn0
    2re nn0red 1red 0le1 addge0d orim12d mpd ) ABCZADEFZGCZAHUAFZDEFZGCZIZUTBCZ
    VCBCZIUSAGCVEAUBAUCUDUSVAVFVDVGUSVAVFUSVARVAJUTKLZVFUSVAMUSVHVAUSASCJAKLDSC
    ZJDUELZVHAUFZAUGZVIUSULNZVJUSUHNZADOPQUTTUIUJUSVDVGUSVDRVDJVCKLZVGUSVDMUSVO
    VDUSVBSCJVBKLVIVJVOUSVBAUKUMUSAHVKUSUNVLJHKLUSUONUPVMVNVBDOPQVCTUIUJUQUR $.

  $( 2 to the power of a positive integer is even.  (Contributed by AV,
     2-Jun-2020.) $)
  nnpw2even $p |- ( N e. NN -> ( ( 2 ^ N ) / 2 ) e. NN ) $=
    ( cn wcel c2 c1 cmin cexp cdiv 2cnd cc0 wne 2ne0 a1i nnz expm1d 2nn nnm1nn0
    co nnexpcld eqeltrrd ) ABCZDAEFRZGRDAGRDHRBUADAUAIDJKUALMANOUADUBDBCUAPMAQS
    T $.

  $( The floor of an even integer divided by 2 is equal to the integer divided
     by 2.  (Contributed by AV, 7-Jun-2020.) $)
  zefldiv2 $p |- ( ( N e. ZZ /\ ( N / 2 ) e. ZZ )
                   -> ( |_ ` ( N / 2 ) ) = ( N / 2 ) ) $=
    ( c2 cdiv co cz wcel cfl cfv wceq flid adantl ) ABCDZEFLGHLIAEFLJK $.

  $( The floor of an odd integer divided by 2 is equal to the integer first
     decreased by 1 and then divided by 2.  (Contributed by AV, 7-Jun-2020.) $)
  zofldiv2 $p |- ( ( N e. ZZ /\ ( ( N + 1 ) / 2 ) e. ZZ )
                   -> ( |_ ` ( N / 2 ) ) = ( ( N - 1 ) / 2 ) ) $=
    ( cz wcel c1 caddc co c2 cdiv wa cfl cfv cmin wceq cc zcn npcan1 eqcomd cc0
    eqtrd wbr syl oveq1d wne peano2zm zcnd 1cnd 2cnne0 a1i divdir fveq2d adantr
    syl3anc cle clt halfge0 halflt1 pm3.2i cr wb zob biimpa halfre flbi2 mpbiri
    sylancl ) ABCZADEFGHFBCZIZAGHFZJKZADLFZGHFZDGHFZEFZJKZVLVFVJVOMVGVFVIVNJVFV
    IVKDEFZGHFZVNVFAVPGHVFANCZAVPMAOVRVPAAPQUAUBVFVKNCDNCGNCGRUCIZVQVNMVFVKAUDU
    EVFUFVSVFUGUHVKDGUIULSUJUKVHVOVLMZRVMUMTZVMDUNTZIZWAWBUOUPUQVHVLBCZVMURCVTW
    CUSVFVGWDAUTVAVBVMVLVCVEVDS $.

  $( The floor of an odd nonnegative integer divided by 2 is equal to the
     integer first decreased by 1 and then divided by 2.  (Contributed by AV,
     1-Jun-2020.)  (Proof shortened by AV, 7-Jun-2020.) $)
  nn0ofldiv2 $p |- ( ( N e. NN0 /\ ( ( N + 1 ) / 2 ) e. NN0 )
                        -> ( |_ ` ( N / 2 ) ) = ( ( N - 1 ) / 2 ) ) $=
    ( cn0 wcel cz c1 caddc co c2 cdiv cfl cfv cmin wceq nn0z zofldiv2 syl2an )
    ABCADCAEFGHIGZDCAHIGJKAELGHIGMQBCANQNAOP $.

  $( The floor of a positive integer divided by 2 is greater than or equal to
     the integer decreased by 1 and then divided by 2.  (Contributed by AV,
     1-Jun-2020.) $)
  flnn0div2ge $p |- ( N e. NN0 -> ( ( N - 1 ) / 2 ) <_ ( |_ ` ( N / 2 ) ) ) $=
    ( c2 cdiv co cn0 wcel c1 cfl cfv cle wbr wa cr syl adantl wceq cz adantr ex
    a1i caddc wo cmin nn0eo wi nn0re peano2rem crp 2rp lem1d lediv1dd nn0z flid
    breqtrrd nn0o rehalfcld cc0 clt wb 2pos pm3.2i lediv1 syl3anc mpbid flwordi
    2re eqbrtrrd syldc jaoi mpcom ) ABCDZEFZAGUADBCDEFZUBAEFZAGUCDZBCDZVKHIZJKZ
    AUDVLVNVRUEVMVLVNVRVLVNLZVPVKVQJVSVOABVNVOMFZVLVNAMFZVTAUFZAUGNZOVNWAVLWBOB
    UHFVSUITVNVOAJKZVLVNAWBUJZOUKVLVQVKPZVNVLVKQFWFVKULVKUMNRUNSVNVMVPEFZVRVNVM
    WGAUOSVNWGVRVNWGLZVPHIZVPVQJWHVPQFZWIVPPWGWJVNVPULOVPUMNWHVPMFZVKMFZVPVKJKZ
    WIVQJKVNWKWGVNVOWCUPRVNWLWGVNAWBUPRVNWMWGVNWDWMWEVNVTWABMFZUQBURKZLZWDWMUSW
    CWBWPVNWNWOVFUTVATVOABVBVCVDRVPVKVEVCVGSVHVIVJ $.

  $( The floor of the half of an odd positive integer is equal to the floor of
     the half of the integer decreased by 1.  (Contributed by AV,
     5-Jun-2012.) $)
  flnn0ohalf $p |- ( ( N e. NN0 /\ ( ( N + 1 ) / 2 ) e. NN0 )
                     -> ( |_ ` ( N / 2 ) ) = ( |_ ` ( ( N - 1 ) / 2 ) ) ) $=
    ( cn0 wcel c1 caddc co c2 cdiv wa cfl cfv cmin nn0ofldiv2 cz wceq nn0o flid
    nn0zd syl eqtr4d ) ABCADEFGHFBCIZAGHFJKADLFGHFZUBJKZAMUAUBNCUCUBOUAUBAPRUBQ
    ST $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The natural logarithm on complex numbers (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Logarithm of a complex power.  Generalization of ~ logcxp .  (Contributed
     by AV, 22-May-2020.) $)
  logcxp0 $p |- ( ( A e. ( CC \ { 0 } ) /\ B e. CC
                    /\ ( B x. ( log ` A ) ) e. ran log )
                 -> ( log ` ( A ^c B ) ) = ( B x. ( log ` A ) ) ) $=
    ( cc cc0 csn cdif wcel clog cfv cmul co crn w3a ccxp ce eldifi 3ad2ant1 wne
    eldifsni simp2 cxpefd fveq2d wceq logef 3ad2ant3 eqtrd ) ACDEZFGZBCGZBAHIJK
    ZHLGZMZABNKZHIUJOIZHIZUJULUMUNHULABUHUIACGUKACUGPQUHUIADRUKACDSQUHUIUKTUAUB
    UKUHUOUJUCUIUJUDUEUF $.

  $( The natural logarithm for a real number greater than 1 is greater than 0.
     (Contributed by AV, 25-May-2020.) $)
  regt1loggt0 $p |- ( B e. ( 1 (,) +oo ) -> 0 < ( log ` B ) ) $=
    ( c1 cpnf cioo co wcel cc0 clog cfv clt wbr cr cxr wa wb 1xr elioopnf ax-mp
    simprbi crp wceq log1 eqcomi a1i breq1d 1rp 0lt1 wi 0red 1red id lttr mpani
    syl3anc imdistani elrp 3imtr4i logltb sylancr bitr4d mpbird ) ABCDEFZGAHIZJ
    KZBAJKZVBALFZVEBMFVBVFVENZOPBAQRZSVBVDBHIZVCJKZVEVBGVIVCJGVIUAVBVIGUBUCUDUE
    VBBTFATFZVEVJOUFVGVFGAJKZNVBVKVFVEVLVFGBJKZVEVLUGVFGLFBLFVFVMVENVLUHVFUIVFU
    JVFUKGBAULUNUMUOVHAUPUQBAURUSUTVA $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Division of functions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c /_f $. $( The class for the division operator of two functions. $)

  $( Extend class notation with the division operator of two functions. $)
  cfdiv $a class /_f $.

  ${
    $d f g $.
    $( Define the division of two functions into the complex numbers.
       (Contributed by AV, 15-May-2020.) $)
    df-fdiv $a |- /_f = ( f e. _V , g e. _V
                          |-> ( ( f oF / g ) |` ( g supp 0 ) ) ) $.
  $}

  ${
    $d F f g x $.  $d G f g x $.  $d V f g x $.  $d W f g x $.
    $( The quotient of two functions into the complex numbers.  (Contributed by
       AV, 15-May-2020.) $)
    fdivval $p |- ( ( F e. V /\ G e. W )
                    -> ( F /_f G ) = ( ( F oF / G ) |` ( G supp 0 ) ) ) $=
      ( vf vg vx wcel wa cvv cv cdiv co cc0 csupp cres cfdiv wceq adantl elex
      cof cmpo df-fdiv a1i oveq12 oveq1 reseq12d adantr wfun cdm cin cfv funmpt
      cmpt offval3 funeqd mpbiri ovex resfunexg sylancl ovmpod ) ACHZBDHZIZEFAB
      JJEKZFKZLUAZMZVFNOMZPZABVGMZBNOMZPZQJQEFJJVJUBRVDEFUCUDVEARZVFBRZIZVJVMRV
      DVPVHVKVIVLVEAVFBVGUEVOVIVLRVNVFBNOUFSUGSVBAJHVCACTUHVCBJHVBBDTSVDVKUIZVL
      JHVMJHVDVQGAUJBUJUKZGKZAULVSBULLMZUNZUIGVRVTUMVDVKWAGLABCDUOUPUQBNOURVKVL
      JUSUTVA $.
  $}

  ${
    $d A x $.  $d F x $.  $d G x $.  $d V x $.
    $( The quotient of two functions into the complex numbers as mapping.
       (Contributed by AV, 16-May-2020.) $)
    fdivmpt $p |- ( ( F : A --> CC /\ G : A --> CC /\ A e. V )
                    -> ( F /_f G ) = ( x e. ( G supp 0 )
                                       |-> ( ( F ` x ) / ( G ` x ) ) ) ) $=
      ( cc wf wcel co cc0 csupp cres cdiv cfv cvv wceq fex eqtrd syl2anc wfn cv
      w3a cfdiv cof cmpt 3adant2 3adant1 wa fdivval offres wss ffn 3ad2ant1 cdm
      suppssdm fdm eqcomd 3ad2ant2 sseqtrrid fnssres ovexd inidm adantl offval
      fvres ) BFCGZBFDGZBEHZUBZCDUCIZCDJKIZLZDVKLZMUDZIZAVKAUAZCNZVPDNZMIUEVICO
      HZDOHZVJVOPVFVHVSVGBFECQUFVGVHVTVFBFEDQUGVSVTUHVJCDVNIVKLVOCDOOUIVKMCDOOU
      JRSVIAVKVKVQVRMVKVLVMOOVICBTZVKBUKZVLVKTVFVGWAVHBFCULUMVIDUNZVKBDJUOVGVFB
      WCPVHVGWCBBFDUPUQURUSZBVKCUTSVIDBTZWBVMVKTVGVFWEVHBFDULURWDBVKDUTSVIDJKVA
      ZWFVKVBVPVKHZVPVLNVQPVIVPVKCVEVCWGVPVMNVRPVIVPVKDVEVCVDR $.

    $( The quotient of two functions into the complex numbers is a function
       into the complex numbers.  (Contributed by AV, 16-May-2020.) $)
    fdivmptf $p |- ( ( F : A --> CC /\ G : A --> CC /\ A e. V )
                     -> ( F /_f G ) : ( G supp 0 ) --> CC ) $=
      ( vx cc wf wcel w3a cc0 csupp co cfdiv cv cdiv cmpt wa 3ad2ant2 ffvelcdmd
      cfv simpl1 wss cdm suppssdm fdm sseqtrid sselda simpl2 wne wfn simp3 0cnd
      wb ffn elsuppfn syl3anc simplbda divcld fmpttd fdivmpt feq1d mpbird ) AFB
      GZAFCGZADHZIZCJKLZFBCMLZGVGFEVGENZBTZVICTZOLZPZGVFEVGVLFVFVIVGHZQZVJVKVOA
      FVIBVCVDVEVNUAVFVGAVIVDVCVGAUBVEVDCUCVGACJUDAFCUEUFRUGZSVOAFVICVCVDVEVNUH
      VPSVFVNVIAHZVKJUIZVFCAUJZVEJFHVNVQVRQUMVDVCVSVEAFCUNRVCVDVEUKVFULVICDFAJU
      OUPUQURUSVFVGFVHVMEABCDUTVAVB $.

    $( The quotient of two functions into the real numbers is a function into
       the real numbers.  (Contributed by AV, 16-May-2020.) $)
    refdivmptf $p |- ( ( F : A --> RR /\ G : A --> RR /\ A e. V )
                       -> ( F /_f G ) : ( G supp 0 ) --> RR ) $=
      ( vx cr wf wcel w3a cc0 co cfv wa wss 3ad2ant2 ffvelcdmd cc ax-resscn a1i
      id csupp cfdiv cv cdiv simpl1 cdm suppssdm fdm sseqtrid sselda simpl2 wne
      cmpt wfn wb ffn simp3 0red elsuppfn syl3anc simplbda redivcld fmpttd wceq
      fssd 3anim123i fdivmpt syl feq1d mpbird ) AFBGZAFCGZADHZIZCJUAKZFBCUBKZGV
      OFEVOEUCZBLZVQCLZUDKZUMZGVNEVOVTFVNVQVOHZMZVRVSWCAFVQBVKVLVMWBUEVNVOAVQVL
      VKVOANVMVLCUFVOACJUGAFCUHUIOUJZPWCAFVQCVKVLVMWBUKWDPVNWBVQAHZVSJULZVNCAUN
      ZVMJFHWBWEWFMUOVLVKWGVMAFCUPOVKVLVMUQVNURVQCDFAJUSUTVAVBVCVNVOFVPWAVNAQBG
      ZAQCGZVMIVPWAVDVKWHVLWIVMVMVKAFQBVKTFQNZVKRSVEVLAFQCVLTWJVLRSVEVMTVFEABCD
      VGVHVIVJ $.

    $( The quotient of two functions into the complex numbers is a partial
       function.  (Contributed by AV, 16-May-2020.) $)
    fdivpm $p |- ( ( F : A --> CC /\ G : A --> CC /\ A e. V )
                  -> ( F /_f G ) e. ( CC ^pm A ) ) $=
      ( cc wf wcel w3a cvv cc0 csupp cfdiv wss cpm cnex a1i simp3 fdivmptf cdm
      co suppssdm wceq fdm eqcomd 3ad2ant2 sseqtrrid elpm2r syl22anc ) AEBFZAEC
      FZADGZHZEIGZUKCJKTZEBCLTZFUNAMUOEANTGUMULOPUIUJUKQABCDRULCSZUNACJUAUJUIAU
      PUBUKUJUPAAECUCUDUEUFEAUNUOIDUGUH $.

    $( The quotient of two functions into the real numbers is a partial
       function.  (Contributed by AV, 16-May-2020.) $)
    refdivpm $p |- ( ( F : A --> RR /\ G : A --> RR /\ A e. V )
                     -> ( F /_f G ) e. ( RR ^pm A ) ) $=
      ( cr wf wcel w3a cvv cc0 csupp co cfdiv wss cpm reex a1i simp3 refdivmptf
      cdm suppssdm wceq fdm eqcomd 3ad2ant2 sseqtrrid elpm2r syl22anc ) AEBFZAE
      CFZADGZHZEIGZUKCJKLZEBCMLZFUNANUOEAOLGUMULPQUIUJUKRABCDSULCTZUNACJUAUJUIA
      UPUBUKUJUPAAECUCUDUEUFEAUNUOIDUGUH $.

    $d X x $.
    $( The function value of a quotient of two functions into the complex
       numbers.  (Contributed by AV, 19-May-2020.) $)
    fdivmptfv $p |- ( ( ( F : A --> CC /\ G : A --> CC /\ A e. V )
                          /\ X e. ( G supp 0 ) )
                        -> ( ( F /_f G ) ` X ) = ( ( F ` X ) / ( G ` X ) ) ) $=
      ( vx cc wf wcel w3a cc0 csupp co wa cv cfv cdiv cfdiv wceq fveq2 cvv cmpt
      fdivmpt adantr oveq12d adantl simpr ovexd fvmptd ) AGBHAGCHADIJZECKLMZIZN
      ZFEFOZBPZUNCPZQMZEBPZECPZQMZUKBCRMZUAUJVAFUKUQUBSULFABCDUCUDUNESZUQUTSUMV
      BUOURUPUSQUNEBTUNECTUEUFUJULUGUMURUSQUHUI $.

    $( The function value of a quotient of two functions into the real numbers.
       (Contributed by AV, 19-May-2020.) $)
    refdivmptfv $p |- ( ( ( F : A --> RR /\ G : A --> RR /\ A e. V )
                             /\ X e. ( G supp 0 ) )
                        -> ( ( F /_f G ) ` X ) = ( ( F ` X ) / ( G ` X ) ) ) $=
      ( vx cr wf wcel w3a co cfv cdiv wceq cc id ax-resscn a1i fssd fveq2 csupp
      cc0 wa cv cfdiv cvv wss 3anim123i fdivmpt syl adantr oveq12d adantl simpr
      cmpt ovexd fvmptd ) AGBHZAGCHZADIZJZECUBUAKZIZUCZFEFUDZBLZVECLZMKZEBLZECL
      ZMKZVBBCUEKZUFVAVLFVBVHUONZVCVAAOBHZAOCHZUTJVMURVNUSVOUTUTURAGOBURPGOUGZU
      RQRSUSAGOCUSPVPUSQRSUTPUHFABCDUIUJUKVEENZVHVKNVDVQVFVIVGVJMVEEBTVEECTULUM
      VAVCUNVDVIVJMUPUQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Upper bounds
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c _O $. $( The class of the "big-O" function. $)

  $( Extend class notation with the class of the "big-O" function. $)
  cbigo $a class _O $.

  ${
    $d g f x m y $.
    $( Define the function "big-O", mapping a real function g to the set of
       real functions "of order g(x)".  Definition in section 1.1 of
       [AhoHopUll] p. 2.  This is a generalization of "big-O of one", see
       ~ df-o1 and ~ df-lo1 .  As explained in the comment of df-o1 , any big-O
       can be represented in terms of ` O(1) ` and division, see ~ elbigolo1 .
       (Contributed by AV, 15-May-2020.) $)
    df-bigo $a |- _O = ( g e. ( RR ^pm RR ) |-> { f e. ( RR ^pm RR ) |
                      E. x e. RR E. m e. RR A. y e. ( dom f i^i ( x [,) +oo ) )
                      ( f ` y ) <_ ( m x. ( g ` y ) ) } ) $.
  $}

  ${
    $d G g f x m y $.
    $( Set of functions of order G(x).  (Contributed by AV, 15-May-2020.) $)
    bigoval $p |- ( G e. ( RR ^pm RR ) -> ( _O ` G ) = { f e. ( RR ^pm RR ) |
                      E. x e. RR E. m e. RR A. y e. ( dom f i^i ( x [,) +oo ) )
                      ( f ` y ) <_ ( m x. ( G ` y ) ) } ) $=
      ( vg cv cfv cmul co cle wbr cdm cpnf cico wral cr wrex cpm crab cin cbigo
      wceq fveq1 oveq2d breq2d ralbidv 2rexbidv rabbidv df-bigo rabex fvmpt
      ovex ) FEBGZCGZHZDGZUNFGZHZIJZKLZBUOMAGNOJUAZPZDQRAQRZCQQSJZTUPUQUNEHZIJZ
      KLZBVBPZDQRAQRZCVETVEUBUREUCZVDVJCVEVKVCVIADQQVKVAVHBVBVKUTVGUPKVKUSVFUQI
      UNUREUDUEUFUGUHUIABCFDUJVJCVEQQSUMUKUL $.

    $( Reverse closure of the "big-O" function.  (Contributed by AV,
       16-May-2020.) $)
    elbigofrcl $p |- ( F e. ( _O ` G ) -> G e. ( RR ^pm RR ) ) $=
      ( vg vy vf vm vx cbigo cfv wcel cdm cr cpm co elfvdm cv cmul cle wrex cvv
      wbr cpnf cico cin wral crab cmpt df-bigo dmeqi wceq dmmptg ovex rabex a1i
      mprg eqtri eleqtrdi ) ABHIJBHKZLLMNZABHOURCUSDPZEPZIFPUTCPZIQNRUADVAKGPUB
      UCNUDUEFLSGLSZEUSUFZUGZKZUSHVEGDECFUHUIVDTJZVFUSUJCUSCUSVDTUKVGVBUSJVCEUS
      LLMULUMUNUOUPUQ $.

    $d F f m x y $.
    $( Properties of a function of order G(x).  (Contributed by AV,
       16-May-2020.) $)
    elbigo $p |- ( F e. ( _O ` G )
                   <-> ( F e. ( RR ^pm RR ) /\ G e. ( RR ^pm RR )
                   /\ E. x e. RR E. m e. RR A. y e. ( dom F i^i ( x [,) +oo ) )
                      ( F ` y ) <_ ( m x. ( G ` y ) ) ) ) $=
      ( vf cr cpm co wcel cbigo cfv wa cv cle wbr cdm cin wral wrex w3a bigoval
      cmul cpnf cico crab eleq2d wceq dmeq ineq1d fveq1 breq1d raleqbidv bitrdi
      2rexbidv elrab pm5.32i elbigofrcl pm4.71ri 3anan12 3bitr4i ) EGGHIZJZDEKL
      ZJZMVCDVBJZBNZDLZCNVGELUCIZOPZBDQZANUDUEIZRZSZCGTAGTZMZMVEVFVCVOUAVCVEVPV
      CVEDVGFNZLZVIOPZBVQQZVLRZSZCGTAGTZFVBUFZJVPVCVDWDDABFCEUBUGWCVOFDVBVQDUHZ
      WBVNACGGWEVSVJBWAVMWEVTVKVLVQDUIUJWEVRVHVIOVGVQDUKULUMUOUPUNUQVEVCDEURUSV
      FVCVOUTVA $.

    $d A m x y $.  $d B m x y $.  $d C m x y $.  $d M m x $.
    $( Properties of a function of order G(x) under certain assumptions.
       (Contributed by AV, 17-May-2020.) $)
    elbigo2 $p |- ( ( ( G : A --> RR /\ A C_ RR )
                  /\ ( F : B --> RR /\ B C_ A ) )
                   -> ( F e. ( _O ` G ) <-> E. x e. RR E. m e. RR A. y e. B
                           ( x <_ y -> ( F ` y ) <_ ( m x. ( G ` y ) ) ) ) ) $=
      ( cr wf wss wa cfv wcel cv co cle wbr wrex wi cvv cbigo cmul cdm cpnf cin
      cico wral cpm w3a elbigo df-3an bitri wb reex pm3.2i simpl adantl adantld
      a1i sstr2 impcom elpm2r syl12anc syl2anc ibar bicomd bitrid elin wceq fdm
      ad2antrl ad2antrr eleq2d anbi1d elicopnf ad3antlr sselda biantrurd bitr4d
      pm5.32da bitrd imbi1d impexp bitrdi ralbidv2 rexbidva ) CHGIZCHJZKZDHFIZD
      CJZKZKZFGUALMZBNZFLENZWOGLUBOPQZBFUCZANZUDUFOZUEZUGZEHRZAHRZWSWOPQZWQSZBD
      UGZEHRZAHRWNFHHUHOZMZGXIMZKZXDKZWMXDWNXJXKXDUIXMABEFGUJXJXKXDUKULWMXJXKXM
      XDUMWMHTMZXNKZWJDHJZXJXOWMXNXNUNUNUOUSZWLWJWIWJWKUPUQWLWIXPWKWIXPSWJWKWHX
      PWGDCHUTURUQVAZHHDFTTVBVCWMXOWIXKXQWIWLUPHHCGTTVBVDXLXDXMXLXDVEVFVDVGWMXC
      XHAHWMWSHMZKZXBXGEHXTWPHMZKZWQXFBXADYBWOXAMZWQSWODMZXEKZWQSYDXFSYBYCYEWQY
      CWOWRMZWOWTMZKZYBYEWOWRWTVHYBYHYDYGKYEYBYFYDYGYBWRDWOWMWRDVIZXSYAWJYIWIWK
      DHFVJVKVLVMVNYBYDYGXEYBYDKZYGWOHMZXEKZXEXSYGYLUMWMYAYDWSWOVOVPYJYKXEYBDHW
      OWMXPXSYAXRVLVQVRVSVTWAVGWBYDXEWQWCWDWEWFWFWA $.

    $( Sufficient condition for a function to be of order G(x).  (Contributed
       by AV, 18-May-2020.) $)
    elbigo2r $p |- ( ( ( G : A --> RR /\ A C_ RR )
                  /\ ( F : B --> RR /\ B C_ A ) /\ ( C e. RR /\ M e. RR
                 /\ A. x e. B ( C <_ x -> ( F ` x ) <_ ( M x. ( G ` x ) ) ) ) )
                   -> F e. ( _O ` G ) ) $=
      ( vy vm cr wf wss wcel cv cle wbr cfv cmul wi wral wa w3a cbigo wrex wceq
      breq1 imbi1d ralbidv oveq1 breq2d imbi2d rspc2ev 3ad2ant3 elbigo2 3adant3
      co wb mpbird ) BJFKBJLUAZCJEKCBLUAZDJMGJMDANZOPZVAEQZGVAFQZRUPZOPZSZACTZU
      BZUBEFUCQMZHNZVAOPZVCINZVDRUPZOPZSZACTZIJUDHJUDZVIUSVRUTVQVHVBVOSZACTHIDG
      JJVKDUEZVPVSACVTVLVBVOVKDVAOUFUGUHVMGUEZVSVGACWAVOVFVBWAVNVEVCOVMGVDRUIUJ
      UKUHULUMUSUTVJVRUQVIHABCIEFUNUOUR $.

    $( A function of order G(x) is a function.  (Contributed by AV,
       18-May-2020.) $)
    elbigof $p |- ( F e. ( _O ` G ) -> F : dom F --> RR ) $=
      ( vy vm vx cbigo cfv wcel cr cpm co cmul cle wbr cdm cpnf cico wrex reex
      cv cin wral w3a wf elbigo wss elpm2 simplbi 3ad2ant1 sylbi ) ABFGHAIIJKZH
      ZBUKHZCTZAGDTUNBGLKMNCAOZETPQKUAUBDIREIRZUCUOIAUDZECDABUEULUMUQUPULUQUOIU
      FIIASSUGUHUIUJ $.

    $( The domain of a function of order G(x) is a subset of the reals.
       (Contributed by AV, 18-May-2020.) $)
    elbigodm $p |- ( F e. ( _O ` G ) -> dom F C_ RR ) $=
      ( vy vm vx cbigo cfv wcel cr cpm co cmul cle wbr cdm cpnf cico wrex reex
      cv cin wral w3a wss elbigo wf elpm2 simprbi 3ad2ant1 sylbi ) ABFGHAIIJKZH
      ZBUKHZCTZAGDTUNBGLKMNCAOZETPQKUAUBDIREIRZUCUOIUDZECDABUEULUMUQUPULUOIAUFU
      QIIASSUGUHUIUJ $.

    $( The defining property of a function of order G(x).  (Contributed by AV,
       18-May-2020.) $)
    elbigoimp $p |- ( ( F e. ( _O ` G ) /\ F : A --> RR /\ A C_ dom G )
                   -> E. x e. RR E. m e. RR A. y e. A
                      ( x <_ y -> ( F ` y ) <_ ( m x. ( G ` y ) ) ) ) $=
      ( cbigo cfv wcel cr wf cdm wss cv cle wbr co wrex wa reex cmul wral simp1
      w3a wi cpm elbigofrcl elpm2 sylib 3ad2ant1 3simpc elbigo2 syl2anc mpbid
      wb ) EFGHIZCJEKZCFLZMZUDZUPANBNZOPVAEHDNVAFHUAQOPUEBCUBDJRAJRZUPUQUSUCUTU
      RJFKURJMSZUQUSSUPVBUOUPUQVCUSUPFJJUFQIVCEFUGJJFTTUHUIUJUPUQUSUKABURCDEFUL
      UMUN $.
  $}

  ${
    $d A m x y $.  $d F m x y $.  $d G m x y $.
    $( A function (into the positive reals) is of order G(x) iff the quotient
       of the function and G(x) (also a function into the positive reals) is an
       eventually upper bounded function.  (Contributed by AV, 20-May-2020.)
       (Proof shortened by II, 16-Feb-2023.) $)
    elbigolo1 $p |- ( ( A C_ RR /\ G : A --> RR+ /\ F : A --> RR+ )
                      -> ( F e. ( _O ` G ) <-> ( F /_f G ) e. <_O(1) ) ) $=
      ( vx vy vm cr wss crp wf cle wbr cfv co wrex wcel wa cc0 cvv wceq cv cmul
      w3a wi wral cfdiv cbigo clo1 cdiv clt rpssre a1i fssd 3ad2ant3 ffvelcdmda
      wb id adantr simplrr simpl2 rpregt0d 3jca ledivmul2 bicomd csupp 3ad2ant2
      syl reex ssex 3ad2ant1 cdm wfun crn wnel ffun adantl anim1ci fex 0red frn
      wn 0nrp ssneld mpi df-nel sylibr suppdm syl31anc fdm eqtrd 3adant3 eqcomd
      eleq2d biimpa refdivmptfv syl2anc breq1d bitr4d imbi2d ralbidva 2rexbidva
      simp1 ssidd elbigo2 syl22anc refdivmptf feq2d mpbird ello12 3bitr4d ) AGH
      ZAICJZAIBJZUCZDUAZEUAZKLZXPBMZFUAZXPCMZUBNKLZUDZEAUEZFGODGOZXQXPBCUFNZMZX
      SKLZUDZEAUEZFGODGOZBCUGMPZYEUHPZXNYCYIDFGGXNXOGPZXSGPZQZQZYBYHEAYPXPAPZQZ
      YAYGXQYRYAXRXTUINZXSKLZYGYRXRGPZYNXTGPRXTUJLQZUCZYAYTUPYRUUAYNUUBYPAGXPBX
      NAGBJZYOXMXKUUDXLXMAIGBXMUQIGHZXMUKULUMUNZURUOXNYMYNYQUSYRXTYPAIXPCXKXLXM
      YOUTUOVAVBUUCYTYAXRXSXTVCVDVGYRYFYSXSKYRUUDAGCJZASPZUCZXPCRVENZPZYFYSTYPU
      UIYQXNUUIYOXNUUDUUGUUHUUFXLXKUUGXMXLAIGCXLUQUUEXLUKULUMVFZXKXLUUHXMAGVHVI
      ZVJVBZURURYPYQUUKYPAUUJXPXNAUUJTYOXNUUJAXKXLUUJATXMXKXLQZUUJCVKZAUUOCVLZC
      SPZRGPRCVMZVNZUUJUUPTXLUUQXKAICVOVPUUOXLUUHQUURXKUUHXLUUMVQAISCVRVGUUOVSX
      LUUTXKXLUUSIHZUUTAICVTUVARUUSPWAZUUTUVARIPWAUVBWBUVAUUSIRUVAUQWCWDRUUSWEW
      FVGVPCSGRWGWHXLUUPATXKAICWIVPWJWKWLZURWMWNABCSXPWOWPWQWRWSWTXAXNUUGXKUUDA
      AHYKYDUPUULXKXLXMXBZUUFXNAXCDEAAFBCXDXEXNAGYEJZXKYLYJUPXNUVEUUJGYEJZXNUUI
      UVFUUNABCSXFVGXNAUUJGYEUVCXGXHUVDDEAFYEXIWPXJ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Logarithm to an arbitrary base (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The general logarithm, with a real base greater than 1, for a real number
     greater than or equal to 1 is greater than or equal to 0.  (Contributed by
     AV, 25-May-2020.) $)
  rege1logbrege0 $p |- ( ( B e. ( 1 (,) +oo ) /\ X e. ( 1 [,) +oo ) )
                       -> 0 <_ ( B logb X ) ) $=
    ( c1 cpnf co wcel wa cc0 clog cfv cle wbr cr wb ax-mp clt syl3anc adantr cc
    wne cioo cico cdiv clogb 1re elicopnf bilani logge0 syl crp simpl 0lt1 0red
    wi 1red id ltletr mpani imp elrpd sylbi relogcld adantl cxr 1xr regt1loggt0
    elioopnf lttr ge0div mpbid cpr cdif csn wceq w3a recn gt0ne0d simplbda 3jca
    ltlend eldifpr 3imtr4i jca eldifsn logbval syl2an breqtrrd ) ACDUAEFZBCDUBE
    FZGZHBIJZAIJZUCEZABUDEZKWJHWKKLZHWMKLZWJBMFZCBKLZGZWOWIWSWHCMFZWIWSNUECBUFO
    ZUGBUHUIWJWKMFZWLMFZHWLPLZWOWPNWIXBWHWIBWIWSBUJFXAWSBWQWRUKWQWRHBPLZWQHCPLZ
    WRXEULWQHMFZWTWQXFWRGXEUNWQUMWQUOWQUPHCBUQQURUSZUTVAVBVCWHXCWIWHAWHAMFZCAPL
    ZGZAUJFCVDFWHXKNVECAVGOZXKAXIXJUKXIXJHAPLZXIXFXJXMULXIXGWTXIXFXJGXMUNXIUMXI
    UOZXIUPZHCAVHQURUSZUTVAVBRWHXDWIAVFRWKWLVIQVJWHASHCVKVLFZBSHVMVLFZWNWMVNWIX
    KASFZAHTZACTZVOWHXQXKXSXTYAXIXSXJAVPRXKAXPVQXIXJCAKLYAXICAXNXOVTVRVSXLASHCW
    AWBWSBSFZBHTZGWIXRWSYBYCWQYBWRBVPRWSBXHVQWCXABSHWDWBABWEWFWG $.

  $( The general logarithm, with an integer base greater than 1, for a real
     number greater than or equal to 1 is greater than or equal to 0.
     (Contributed by AV, 25-May-2020.) $)
  rege1logbzge0 $p |- ( ( B e. ( ZZ>= ` 2 ) /\ X e. ( 1 [,) +oo ) )
                        -> 0 <_ ( B logb X ) ) $=
    ( c2 cuz cfv wcel c1 cpnf cioo co cico cc0 clogb cle wbr cz cr clt wa a1i
    w3a zre 3ad2ant2 1lt2 wi 1re 2re adantl ltletr syl3anc mpani 3impia jca cxr
    eluz2 wb 1xr elioopnf ax-mp 3imtr4i rege1logbrege0 sylan ) ACDEFZAGHIJFZBGH
    KJFLABMJNOCPFZAPFZCANOZUAZAQFZGAROZSZVCVDVHVIVJVFVEVIVGAUBZUCVEVFVGVJVEVFSZ
    GCROZVGVJUDVMGQFZCQFZVIVNVGSVJUEVOVMUFTVPVMUGTVFVIVEVLUHGCAUIUJUKULUMCAUOGU
    NFVDVKUPUQGAURUSUTABVAVB $.

  ${
    fllogbd.b $e |- ( ph -> B e. ( ZZ>= ` 2 ) ) $.
    fllogbd.x $e |- ( ph -> X e. RR+ ) $.
    fllogbd.e $e |- E = ( |_ ` ( B logb X ) ) $.
    $( A real number is between the base of a logarithm to the power of the
       floor of the logarithm of the number and the base of the logarithm to
       the power of the floor of the logarithm of the number plus one.
       (Contributed by AV, 23-May-2020.) $)
    fllogbd $p |- ( ph -> ( ( B ^ E ) <_ X /\ X < ( B ^ ( E + 1 ) ) ) ) $=
      ( cexp co cle wbr c1 caddc clt ccxp wcel syl zred cc cc0 clogb cfl cfv cr
      c2 cuz crp relogbzcl syl2anc eqbrtrid cz eluzelz eluz2b1 simprbi eqeltrid
      flle flcld cxpled mpbid zcnd cn eluz2nn nnne0d cxpexpzd cpr cdif csn wceq
      eluz2cnn0n1 wne wa rpcnne0 eldifsn sylibr cxplogb 3brtr3d flltp1 breqtrrd
      a1i oveq1d peano2zd cxpltd jca ) ABCHIZDJKDBCLMIZHIZNKABCOIZBBDUAIZOIZWDD
      JACWHJKWGWIJKACWHUBUCZWHJGAWHUDPZWJWHJKABUEUFUCPZDUGPZWKEFBDUHUIZWHUPQUJA
      BCWHABAWLBUKPZEUEBULQZRZAWLLBNKZEWLWOWRBUMUNQZACACWJUKGAWHWNUQUOZRWNURUSA
      BCABWPUTZABAWLBVAPEBVBQVCZWTVDABSTLVEVFPZDSTVGVFPZWIDVHAWLXCEBVIQAWMXDFWM
      DSPDTVJVKXDDVLDSTVMVNQBDVOUIZVPAWIBWEOIZDWFNAWHWENKWIXFNKAWHWJLMIZWENAWKW
      HXGNKWNWHVQQACWJLMCWJVHAGVSVTVRABWHWEWQWSWNAWEACWTWAZRWBUSXEABWEXAXBXHVDV
      PWC $.
  $}

  $( The logarithm of the product of a positive real number and the base to the
     power of a real number is the logarithm of the positive real number plus
     the real number.  (Contributed by AV, 29-May-2020.) $)
  relogbmulbexp $p |- ( ( B e. ( RR+ \ { 1 } ) /\ ( A e. RR+ /\ C e. RR ) )
                  -> ( B logb ( A x. ( B ^c C ) ) ) = ( ( B logb A ) + C ) ) $=
    ( crp c1 cdif wcel wa co cmul clogb caddc cc0 wceq wne adantr adantl oveq2d
    cc simpr csn cr ccxp cpr w3a rpcn rpne0 3jca eldifsn eldifpr 3imtr4i simprl
    eldifi relogbmulexp syl13anc sylbi logbid1 syl ax-1rid eqtrd ) BDEUAZFGZADG
    ZCUBGZHZHZBABCUCIJIKIZBAKIZCBBKIZJIZLIZVHCLIVFBSMEUDFGZVCBDGZVDVGVKNVBVLVEV
    MBEOZHZBSGZBMOZVNUEZVBVLVOVPVQVNVMVPVNBUFPVMVQVNBUGPVMVNTUHZBDEUIZBSMEUJUKP
    VBVCVDULVBVMVEBDVAUMPVEVDVBVCVDTQABBCUNUOVFVJCVHLVFVJCEJIZCVFVIECJVBVIENZVE
    VBVRWBVBVOVRVTVSUPBUQURPRVEWACNZVBVDWCVCCUSQQUTRUT $.

  $( The logarithm of the quotient of a positive real number and the base is
     the logarithm of the number minus 1.  (Contributed by AV, 29-May-2020.) $)
  relogbdivb $p |- ( ( B e. ( RR+ \ { 1 } ) /\ A e. RR+ )
                     -> ( B logb ( A / B ) ) = ( ( B logb A ) - 1 ) ) $=
    ( crp c1 csn cdif wcel wa cdiv co clogb cmin cc cc0 cpr wceq wne w3a adantr
    simpr eldifsn rpcn rpne0 3jca sylbi eldifpr sylibr eldifi relogbdiv logbid1
    syl12anc syl oveq2d eqtrd ) BCDEZFGZACGZHZBABIJKJZBAKJZBBKJZLJZUTDLJURBMNDO
    FGZUQBCGZUSVBPUPVCUQUPBMGZBNQZBDQZRZVCUPVDVGHZVHBCDUAVIVEVFVGVDVEVGBUBSVDVF
    VGBUCSVDVGTUDUEZBMNDUFUGSUPUQTUPVDUQBCUOUHSABBUIUKURVADUTLUPVADPZUQUPVHVKVJ
    BUJULSUMUN $.

  $( The logarithm of a number is nonnegative iff the number is greater than or
     equal to 1.  (Contributed by AV, 30-May-2020.) $)
  logbge0b $p |- ( ( B e. ( ZZ>= ` 2 ) /\ X e. RR+ )
                   -> ( 0 <_ ( B logb X ) <-> 1 <_ X ) ) $=
    ( c2 cuz cfv wcel crp cc0 co cle wbr c1 cr clt wb relogcl adantl syl adantr
    clog wa clogb relogbval breq2d eluz2nn nnrpd eluz2gt1 loggt0b mpbird ge0div
    cdiv syl3anc logge0b 3bitr2d ) ACDEFZBGFZUAZHABUBIZJKHBTEZATEZUKIZJKZHUSJKZ
    LBJKZUQURVAHJABUCUDUQUSMFZUTMFZHUTNKZVCVBOUPVEUOBPQUOVFUPUOAGFZVFUOAAUEUFZA
    PRSUOVGUPUOVGLANKZAUGUOVHVGVJOVIAUHRUISUSUTUJULUPVCVDOUOBUMQUN $.

  $( The logarithm of a number is less than 1 iff the number is less than the
     base of the logarithm.  (Contributed by AV, 30-May-2020.) $)
  logblt1b $p |- ( ( B e. ( ZZ>= ` 2 ) /\ X e. RR+ )
                   -> ( ( B logb X ) < 1 <-> X < B ) ) $=
    ( c2 cuz cfv wcel crp wa clogb co c1 clt wbr cr wb relogcl syl adantr bitrd
    clog cdiv relogbval breq1d cmul adantl 1red eluz2nn eluz2gt1 loggt0b mpbird
    cc0 nnrpd ltdivmul syl3anc recnd mulridd breq2d anim2i ancoms logltb bicomd
    jca wceq ) ACDEFZBGFZHZABIJZKLMBTEZATEZUAJZKLMZBALMZVFVGVJKLABUBUCVFVKVHVIK
    UDJZLMZVLVFVHNFZKNFVINFZUKVILMZHZVKVNOVEVOVDBPUEVFUFVDVRVEVDVPVQVDAGFZVPVDA
    AUGULZAPQZVDVQKALMZAUHVDVSVQWBOVTAUIQUJVBRVHKVIUMUNVFVNVHVILMZVLVFVMVIVHLVD
    VMVIVCVEVDVIVDVIWAUOUPRUQVFVEVSHZWCVLOVEVDWDVDVSVEVTURUSWDVLWCBAUTVAQSSS $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The binary logarithm
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  If the binary logarithm is used more often, a separate symbol/definition
  could be provided for it, e.g., log2 = ` ( x e. ( CC \ { 0 } ) `
  ` |-> ( 2 logb X ) ) `.  Then we can write "( log2 `` x )" (analogous to
  ` ( log x ) ` for the natural logarithm) instead of ` ( 2 logb x ) `.

$)

  $( The floor of a positive real number divided by 2 to the power of the floor
     of the logarithm to base 2 of the number is 1.  (Contributed by AV,
     26-May-2020.) $)
  fldivexpfllog2 $p |- ( X e. RR+
                     -> ( |_ ` ( X / ( 2 ^ ( |_ ` ( 2 logb X ) ) ) ) ) = 1 ) $=
    ( crp wcel c2 co cfl cfv cexp c1 cle wbr caddc clt wa cz cr a1i cc0 syl2anc
    wb clogb cdiv wceq cuz 2z uzid mp1i id eqid fllogbd 2re wne relogbzcl flcld
    2ne0 reexpclzd 2pos expgt0 syl3anc rpre divge1b bicomd biimprd cmul expp1zd
    elrpd 2cnd breq2d ltdivmul syl112anc bitr4d biimpd breq2i imbitrrdi anim12d
    1p1e2 mpd expne0d redivcld 1zzd flbi mpbird ) ABCZADDAUAEZFGZHEZUBEZFGIUCZI
    WGJKZWGIILEZMKZNZWCWFAJKZADWEILEHEZMKZNWLWCDWEADOCDDUDGCZWCUEDUFUGZWCUHZWEU
    IUJWCWMWIWOWKWCWIWMWCWFBCZAPCZWIWMTWCWFWCDWEDPCZWCUKQZDRULWCUOQZWCWDWCWPWCW
    DPCWQWRDAUMSUNZUPZWCXAWEOCRDMKZRWFMKZXBXDXFWCUQQDWEURUSZVFAUTZWSWTNWMWIWFAV
    AVBSVCWCWOWGDMKZWKWCWOXJWCWOAWFDVDEZMKZXJWCWNXKAMWCDWEWCVGZXCXDVEVHWCWTXAWF
    PCXGXJXLTXIXBXEXHADWFVIVJVKVLWJDWGMVPVMVNVOVQWCWGPCIOCWHWLTWCAWFXIXEWCDWEXM
    XCXDVRVSWCVTWGIWASWB $.

  $( A positive integer is 1 iff its binary logarithm is between 0 and 1.
     (Contributed by AV, 30-May-2020.) $)
  nnlog2ge0lt1 $p |- ( N e. NN -> ( N = 1
                           <-> ( 0 <_ ( 2 logb N ) /\ ( 2 logb N ) < 1 ) ) ) $=
    ( wcel c1 wceq cc0 c2 clogb co cle wbr clt wa wne anbi12d cfv wb cz syl2anc
    a1i sylbid cn 0le0 cc 2cn 2ne0 1ne2 necomi logb1 mp3an breqtrri 0lt1 pm3.2i
    eqbrtri oveq2 breq2d breq1d mpbiri cuz 2z uzid ax-mp nnrp logbge0b logblt1b
    crp cfl caddc df-2 breq2i anbi2d cr nnre 1zzd flbi bitr4d nnz eqcomd adantr
    flid syl simpr eqtrd ex impbid2 ) AUABZACDZEFAGHZIJZWGCKJZLZWFWJEFCGHZIJZWK
    CKJZLWLWMEEWKIUBFUCBFEMFCMWKEDUDUECFUFUGFUHUIZUJWKECKWNUKUMULWFWHWLWIWMWFWG
    WKEIACFGUNZUOWFWGWKCKWOUPNUQWEWJCAIJZAFKJZLZWFWEWHWPWIWQWEFFUROBZAVEBZWHWPP
    WSWEFQBWSUSFUTVASZAVBZFAVCRWEWSWTWIWQPXAXBFAVDRNWEWRAVFOZCDZWFWEWRWPACCVGHZ
    KJZLZXDWEWQXFWPWQXFPWEFXEAKVHVISVJWEAVKBCQBXDXGPAVLWEVMACVNRVOWEXDWFWEXDLAX
    CCWEAXCDXDWEXCAWEAQBXCADAVPAVSVTVQVRWEXDWAWBWCTTWD $.

  $( The floor of the binary logarithm of 2 to the power of a positive integer
     minus 1 is equal to the integer minus 1.  (Contributed by AV,
     31-May-2020.) $)
  logbpw2m1 $p |- ( I e. NN
                    -> ( |_ ` ( 2 logb ( ( 2 ^ I ) - 1 ) ) ) = ( I - 1 ) ) $=
    ( cn wcel c2 cexp co c1 cfl cfv cz cle wbr clt crp cr a1i nnrpd syl3anc syl
    wceq cmin clogb caddc wne 2rp cn0 2nn0 nnnn0 nn0expcld 2re 1zzd nnz leexp2d
    nnge1 1lt2 2cn exp1 ax-mp breq1d bitrd mpbid nn0ge2m1nn syl2anc 1ne2 necomi
    cc relogbcl flcld peano2zm cuz uzid nnlogbexp sylancr fveq2d flid eqtrd 2nn
    2z nnm1nn0 nnexpcld pw2m1lepw2m1 wb logbleb flwordi eqbrtrrd zred peano2rem
    nnnn0d nnre peano2re flle nnred ltm1d logblt npcan1 3brtr4d ltletrd lelttrd
    leidd nncn wa zgeltp1eq imp syl22anc ) ABCZDDAEFZGUAFZUBFZHIZJCZAGUAFZJCZXK
    XIKLZXIXKGUCFZMLZXIXKTZXEXHXEDNCZXGNCZDGUDZXHOCZXQXEUEPZXEXGXEXFUFCZDXFKLZX
    GBCZXEDADUFCXEUGPAUHZUIXEGAKLZYCAUNXEYFDGEFZXFKLYCXEDGADOCXEUJPXEUKAULZGDML
    XEUOPUMXEYGDXFKYGDTZXEDVFCYIUPDUQURPUSUTVAZXFVBZVCQZXSXEGDVDVEPZDXGVGZRZVHX
    EAJCZXLYHAVISZXEDDXKEFZUBFZHIZXKXIKXEYTXKHIZXKXEYSXKHXEDDVJICZXLYSXKTDJCUUB
    VRDVKURZYQDXKVLVMVNXEXLUUAXKTYQXKVOSVPXEYSOCZXTYSXHKLZYTXIKLXEXQYRNCZXSUUDY
    AXEYRXEDXKDBCXEVQPZAVSVTQZYMDYRVGRYOXEYRXGKLZUUEAWAXEUUBUUFXRUUIUUEWBUUBXEU
    UCPZUUHYLDYRXGWCRVAYSXHWDRWEXEXIXHXNXEXIXEXHXEXQXRXSXTYAXEXGXEYBYCYDXEXFXED
    AUUGYEVTZWHYJYKVCQYMYNRVHWFYOXEXKOCZXNOCXEAOCUULAWIZAWGSXKWJSZXEXTXIXHKLYOX
    HWKSXEXHDXFUBFZXNYOXEXQXFNCZXSUUOOCYAXEXFUUKQZYMDXFVGRUUNXEXGXFMLZXHUUOMLZX
    EXFXEXFUUKWLWMXEUUBXRUUPUURUUSWBUUJYLUUQDXGXFWNRVAXEAAUUOXNKXEAUUMWSXEUUBYP
    UUOATUUCYHDAVLVMXEAVFCXNATAWTAWOSWPWQWRXJXLXAXMXOXAXPXKXIXBXCXD $.

  $( The floor of the binary logarithm of 2 to the power of an element of a
     half-open integer interval bounded by powers of 2 is equal to the integer.
     (Contributed by AV, 31-May-2020.) $)
  fllog2 $p |- ( ( I e. NN0 /\ N e. ( ( 2 ^ I ) ..^ ( 2 ^ ( I + 1 ) ) ) )
                 -> ( |_ ` ( 2 logb N ) ) = I ) $=
    ( wcel c2 co c1 wa cfv cz cle wbr clt adantr adantl cc0 w3a a1i mp3an2i syl
    cr cn0 cexp caddc cfzo clogb cfl wceq nn0z crp wne 2rp elfzoelz zred cuz wi
    elfzo2 eluz2 2re 2pos expgt0 zre ad2antlr ltletr syl3anc mpand com23 3impia
    0red ex sylbi 3ad2ant1 impcom elrpd 1ne2 necomi relogbcl flcld cmin eluzelz
    wb zltlem1 sylan uzid ax-mp eluzelre 3jca 3ad2ant3 3ad2ant2 3exp com34 3imp
    2z adantlr peano2nn0 reexpcld peano2rem cn nn0p1nn 1lt2 expgt1 1red posdifd
    imp mpbid logbleb jca relogbzcl simpr flwordi logbpw2m1 nn0cn pncan1 breq2d
    eqtrd sylibd sylbid nn0re nn0ge0 flge0nn0 syl2anc nn0red rpexpcld nnlogbexp
    cc flle eqcomd eqled elfzole1 letrd flflp1 zgeltp1eq syl22anc ) AUACZBDAUBE
    ZDAFUCEZUBEZUDECZGZADBUEEZUFHZYRAICZYTICZYTAJKZAYTFUCELKZAYTUGZYMUUAYQAUHZM
    YRYSDUICZYRBUICZDFUJZYSTCZUKYRBYQBTCZYMYQBBYNYPULUMNYQYMOBLKZYQBYNUNHCZYPIC
    ZBYPLKZPZYMUULUOZBYNYPUPZUUMUUNUUQUUOUUMYNICZBICZYNBJKZPZUUQYNBUQZUUSUUTUVA
    UUQUUSUUTGZYMUVAUULUVDYMUVAUULUOZUVDYMGZOYNLKZUVAUULYMUVGUVDDTCZYMUUAODLKZU
    VGURUUFUVIYMUSQZDAUTZRNUVFOTCZYNTCZUUKUVGUVAGUULUOZUVFVHUVDUVMYMUUSUVMUUTYN
    VAZMMUUTUUKUUSYMBVAZVBOYNBVCZVDVEVIVFVGVJVKVJVLVMZUUIYRFDVNVOZQDBVPZRZVQYQY
    MUUCYQUUPYMUUCUOZUURUUMUUNUUOUWBUUMUUNGZUUOBYPFVREZJKZUWBUUMUUTUUNUUOUWEVTY
    NBVSBYPWAWBUWCYMUWEUUCUWCYMUWEUUCUOUWCYMGZUWEYSDUWDUEEZJKZUUCDDUNHCZUWFUUHU
    WDUICZUWEUWHVTDICUWIWLDWCWDZUUMYMUUHUUNUUMYMGBUUMUUKYMYNBWEZMUUMYMUULUUMUVB
    UUQUVCUUSUUTUVAUUQUUSUUTYMUVAUULUUSUUTYMUVEUUSUUTYMPZUVGUVAUULUWMUVHUUAUVIP
    ZUVGYMUUSUWNUUTYMUVHUUAUVIUVHYMURQZUUFUVJWFWGUVKSUWMUVLUVMUUKUVNUWMVHUUSUUT
    UVMYMUVOVKUUTUUSUUKYMUVPWHUVQVDVEWIWJWKVJXCZVMWMUWFUWDUWFYPTCZUWDTCZUWFDYOU
    VHUWFURQYMYOUACUWCAWNZNWOYPWPZSUWFFYPLKZOUWDLKZUWFUVHYOWQCZFDLKZPZUXAYMUXEU
    WCYMUVHUXCUXDUWOAWRZUXDYMWSQZWFNDYOWTZSUWFFYPUWFXAUUNUWQUUMYMYPVAVBXBXDVMDB
    UWDXERUWFUWHYTUWGUFHZJKZUUCUWFUWHUXJUWFUWHGUUJUWGTCZUWHUXJUWFUUJUWHUUGUWFUU
    HUUIUUJUKUWFBUWCUUKYMUUMUUKUUNUWLMMUUMYMUULUUNUWPWMVMUUIUWFUVSQUVTRMUWFUXKU
    WHUWFUWIUWJGZUXKYMUXLUWCYMUWIUWJUWIYMUWKQZYMUWDYMUWQUWRYMDYOUWOUWSWOZUWTSYM
    UXAUXBUVHYMUXCUXDUXAURUXFUXGUXHRYMFYPYMXAUXNXBXDVMXFNDUWDXGSMUWFUWHXHYSUWGX
    IVDVIUWFUXIAYTJUWFUXIYOFVREZAUWFUXCUXIUXOUGYMUXCUWCUXFNYOXJSYMUXOAUGZUWCYMA
    YDCUXPAXKAXLSNXNXMXOXPVIVFXPVGVJVLYRAUFHZYSJKZUUDYRUXQAYSYMUXQTCYQYMUXQYMAT
    CZOAJKUXQUACAXQZAXRAXSXTYAMYMUXSYQUXTMZUWAYMUXQAJKZYQYMUXSUYBUXTAYESMYRADYN
    UEEZYSUYAYMUYCTCZYQUUGYMYNUICZUUIUYDUKYMDAUUGYMUKQUUFYBZUUIYMUVSQDYNVPRMUWA
    YMAUYCJKYQYMAUYCUXTYMUYCAYMUWIUUAUYCAUGUXMUUFDAYCXTYFYGMYRUVAUYCYSJKZYQUVAY
    MBYNYPYHNUWIYRUYEUUHUVAUYGVTUWKYMUYEYQUYFMUVRDYNBXERXDYIYIYRUXSUUJUXRUUDVTU
    YAUWAAYSYJXTXDUUAUUBGUUCUUDGUUEYTAYKXCYLYF $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Binary length
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c #b $. $( The class of the binary length function. $)

  $( Extend class notation with the class of the binary length function. $)
  cblen $a class #b $.

  $( Define the binary length of an integer.  Definition in section 1.3 of
     [AhoHopUll] p. 12.  Although not restricted to integers, this definition
     is only meaningful for ` n e. ZZ ` or even for ` n e. CC ` .  (Contributed
     by AV, 16-May-2020.) $)
  df-blen $a |- #b = ( n e. _V |-> if ( n = 0 , 1 ,
                                 ( ( |_ ` ( 2 logb ( abs ` n ) ) ) + 1 ) ) ) $.

  ${
    $d N n $.  $d V n $.
    $( The binary length of an integer.  (Contributed by AV, 20-May-2020.) $)
    blenval $p |- ( N e. V -> ( #b ` N ) = if ( N = 0 , 1 ,
                                 ( ( |_ ` ( 2 logb ( abs ` N ) ) ) + 1 ) ) ) $=
      ( vn wcel cv cc0 wceq c1 c2 cabs cfv clogb co cfl caddc cif cblen df-blen
      cvv eqeq1 fveq2 oveq2d fveq2d oveq1d ifbieq2d elex 1ex ovex ifex fvmptd3
      a1i ) ABDZCACEZFGZHIUMJKZLMZNKZHOMZPAFGZHIAJKZLMZNKZHOMZPZSQSCRUMAGZUNUSU
      RVCHUMAFTVEUQVBHOVEUPVANVEUOUTILUMAJUAUBUCUDUEABUFVDSDULUSHVCUGVBHOUHUIUK
      UJ $.
  $}

  $( The binary length of 0.  (Contributed by AV, 20-May-2020.) $)
  blen0 $p |- ( #b ` 0 ) = 1 $=
    ( cc0 cblen cfv wceq c1 c2 cabs clogb cfl caddc cif wcel c0ex blenval ax-mp
    co cvv eqid iftruei eqtri ) ABCZAADZEFAGCHPICEJPZKZEAQLUAUDDMAQNOUBEUCARST
    $.

  $( The binary length of a "number" not being 0.  (Contributed by AV,
     20-May-2020.) $)
  blenn0 $p |- ( ( N e. V /\ N =/= 0 )
                 -> ( #b ` N ) = ( ( |_ ` ( 2 logb ( abs ` N ) ) ) + 1 ) ) $=
    ( wcel cc0 wne cblen cfv wceq c1 c2 cabs clogb co cfl cif blenval ifnefalse
    caddc sylan9eq ) ABCADEAFGADHIJAKGLMNGIRMZOTABPADITQS $.

  $( The binary length of a positive real number.  (Contributed by AV,
     20-May-2020.) $)
  blenre $p |- ( N e. RR+ -> ( #b ` N ) = ( ( |_ ` ( 2 logb N ) ) + 1 ) ) $=
    ( crp wcel cblen cfv c2 cabs clogb co cfl c1 caddc cc0 wne wceq rpne0 mpdan
    blenn0 rpre rpge0 absidd oveq2d fveq2d oveq1d eqtrd ) ABCZADEZFAGEZHIZJEZKL
    IZFAHIZJEZKLIUFAMNUGUKOAPABRQUFUJUMKLUFUIULJUFUHAFHUFAASATUAUBUCUDUE $.

  $( The binary length of a positive integer.  (Contributed by AV,
     21-May-2020.) $)
  blennn $p |- ( N e. NN -> ( #b ` N ) = ( ( |_ ` ( 2 logb N ) ) + 1 ) ) $=
    ( cn wcel cblen cfv c2 cabs clogb co cfl c1 caddc cc0 wne wceq nnne0 blenn0
    mpdan nnre nnnn0 nn0ge0d absidd oveq2d fveq2d oveq1d eqtrd ) ABCZADEZFAGEZH
    IZJEZKLIZFAHIZJEZKLIUGAMNUHULOAPABQRUGUKUNKLUGUJUMJUGUIAFHUGAASUGAATUAUBUCU
    DUEUF $.

  $( The binary length of a positive integer is a positive integer.
     (Contributed by AV, 25-May-2020.) $)
  blennnelnn $p |- ( N e. NN -> ( #b ` N ) e. NN ) $=
    ( cn wcel cblen cfv c2 clogb co cfl c1 caddc blennn cn0 cc0 cle wbr crp a1i
    cr syl2anc wne 2rp nnrp 1ne2 necomi relogbcl syl3anc cpnf cico cz uzid mp1i
    cuz 2z nnre nnge1 wa elicopnf ax-mp sylanbrc rege1logbzge0 flge0nn0 nn0p1nn
    wb 1re syl eqeltrd ) ABCZADEFAGHZIEZJKHZBALVHVJMCZVKBCVHVISCZNVIOPZVLVHFQCZ
    AQCFJUAZVMVOVHUBRAUCVPVHJFUDUERFAUFUGVHFFUMECZAJUHUIHCZVNFUJCVQVHUNFUKULVHA
    SCZJAOPZVRAUOAUPJSCVRVSVTUQVDVEJAURUSUTFAVATVIVBTVJVCVFVG $.

  $( The binary length of a nonnegative integer is a positive integer.
     (Contributed by AV, 28-May-2020.) $)
  blennn0elnn $p |- ( N e. NN0 -> ( #b ` N ) e. NN ) $=
    ( cn0 wcel cn cc0 wceq wo cblen cfv elnn0 blennnelnn fveq2 c1 blen0 eqeltri
    1nn eqeltrdi jaoi sylbi ) ABCADCZAEFZGAHIZDCZAJTUCUAAKUAUBEHIZDAEHLUDMDNPOQ
    RS $.

  $( The binary length of a power of 2 is the exponent plus 1.  (Contributed by
     AV, 30-May-2020.) $)
  blenpw2 $p |- ( I e. NN0 -> ( #b ` ( 2 ^ I ) ) = ( I + 1 ) ) $=
    ( cn0 wcel c2 cexp co cblen cfv clogb cfl c1 caddc cn wceq 2nn nnexpcl mpan
    syl cz eqtrd blennn cuz uzid mp1i nn0z nnlogbexp syl2anc fveq2d flid oveq1d
    2z ) ABCZDAEFZGHZDUMIFZJHZKLFZAKLFULUMMCZUNUQNDMCULURODAPQUMUARULUPAKLULUPA
    JHZAULUOAJULDDUBHCZASCZUOANDSCUTULUKDUCUDAUEZDAUFUGUHULVAUSANVBAUIRTUJT $.

  $( The binary length of a power of 2 minus 1 is the exponent.  (Contributed
     by AV, 31-May-2020.) $)
  blenpw2m1 $p |- ( I e. NN -> ( #b ` ( ( 2 ^ I ) - 1 ) ) = I ) $=
    ( cn wcel c2 cexp co c1 cmin cblen cfv clogb cfl caddc wceq cn0 cle wbr a1i
    2nn0 syl nnnn0 nn0expcld nnge1 2cnd exp1d eqcomd breq1d cr 2re 1zzd nnz clt
    1lt2 leexp2d bitr4d mpbird nn0ge2m1nn blennn logbpw2m1 oveq1d npcan1 3eqtrd
    syl2anc cc nncn ) ABCZDAEFZGHFZIJZDVHKFLJZGMFZAGHFZGMFZAVFVHBCZVIVKNVFVGOCD
    VGPQZVNVFDADOCVFSRAUAUBVFVOGAPQZAUCVFVODGEFZVGPQVPVFDVQVGPVFVQDVFDVFUDUEUFU
    GVFDGADUHCVFUIRVFUJAUKGDULQVFUMRUNUOUPVGUQVCVHURTVFVJVLGMAUSUTVFAVDCVMANAVE
    AVATVB $.

  $( A positive integer is between 2 to the power of its binary length minus 1
     and 2 to the power of its binary length.  (Contributed by AV,
     31-May-2020.) $)
  nnpw2blen $p |- ( N e. NN -> ( ( 2 ^ ( ( #b ` N ) - 1 ) ) <_ N
                                 /\ N < ( 2 ^ ( #b ` N ) ) ) ) $=
    ( wcel c2 cfv c1 cmin cexp cle wbr clt ccxp wceq crp wne a1i syl oveq2d cc0
    co cc cn cblen clogb cfl caddc cr 2rp nnrp 1ne2 relogbcl syl3anc flcld zcnd
    necomi pncan1 blennn oveq1d 2cnd 2ne0 cxpexpzd 3eqtr4d flle 2re 1lt2 cxpled
    zred mpbid cpr cdif csn 2cn eldifpr mpbir3an nnne0 eldifsn sylanbrc cxplogb
    nncn sylancr breqtrd eqbrtrd flltp1 peano2zd cxpltd 3brtr3d breqtrrd jca )
    AUABZCAUBDZEFSZGSZAHIACWIGSZJIWHWKCCAUCSZUDDZKSZAHWHCWNEUESZEFSZGSCWNGSWKWO
    WHWQWNCGWHWNTBWQWNLWHWNWHWMWHCMBZAMBCENZWMUFBZWRWHUGOAUHWSWHECUIUNZOCAUJUKZ
    ULZUMWNUOPQWHWJWQCGWHWIWPEFAUPZUQQWHCWNWHURZCRNZWHUSOZXCUTVAWHWOCWMKSZAHWHW
    NWMHIZWOXHHIWHWTXIXBWMVBPWHCWNWMCUFBWHVCOZECJIWHVDOZWHWNXCVFXBVEVGWHCTREVHV
    IBZATRVJVIBZXHALXLCTBXFWSVKUSXACTREVLVMWHATBARNXMAVRAVNATRVOVPCAVQVSZVTWAWH
    ACWPGSZWLJWHXHCWPKSZAXOJWHWMWPJIZXHXPJIWHWTXQXBWMWBPWHCWMWPXJXKXBWHWPWHWNXC
    WCZVFWDVGXNWHCWPXEXGXRUTWEWHWIWPCGXDQWFWG $.

  $( A positive integer is between 2 to the power of the binary length of the
     integer minus 1, and 2 to the power of the binary length of the integer.
     (Contributed by AV, 2-Jun-2020.) $)
  nnpw2blenfzo $p |- ( N e. NN -> N e. ( ( 2 ^ ( ( #b ` N ) - 1 ) )
                                         ..^ ( 2 ^ ( #b ` N ) ) ) ) $=
    ( cn wcel c2 cblen cfv c1 cmin co cexp cfzo cle wbr clt wa cz cn0 2z zexpcl
    sylancr nnpw2blen wb nnz blennnelnn nnm1nn0 syl nnnn0d elfzo syl3anc mpbird
    ) ABCZADAEFZGHIZJIZDULJIZKICZUNALMAUONMOZAUAUKAPCUNPCZUOPCZUPUQUBAUCUKDPCZU
    MQCZURRUKULBCVAAUDZULUEUFDUMSTUKUTULQCUSRUKULVBUGDULSTAUNUOUHUIUJ $.

  $( A positive integer is either 2 to the power of the binary length of the
     integer minus 1, or between 2 to the power of the binary length of the
     integer minus 1, increased by 1, and 2 to the power of the binary length
     of the integer.  (Contributed by AV, 2-Jun-2020.) $)
  nnpw2blenfzo2 $p |- ( N e. NN -> ( N = ( 2 ^ ( ( #b ` N ) - 1 ) )
                                   \/ N e. ( ( ( 2 ^ ( ( #b ` N ) - 1 ) ) + 1 )
                                             ..^ ( 2 ^ ( #b ` N ) ) ) ) ) $=
    ( cn wcel c2 cblen cfv c1 cmin cexp cfzo wceq nnpw2blenfzo elfzolborelfzop1
    co caddc wo syl ) ABCADAEFZGHNINZDRINZJNCASKASGONTJNCPALASTMQ $.

  $( Every positive integer can be represented as the sum of a power of 2 and a
     "remainder" less than the power.  (Contributed by AV, 31-May-2020.) $)
  nnpw2pmod $p |- ( N e. NN -> N = ( ( 2 ^ ( ( #b ` N ) - 1 ) )
                                  + ( N mod ( 2 ^ ( ( #b ` N ) - 1 ) ) ) ) ) $=
    ( cn wcel c2 c1 cmin co cexp cmo caddc wceq cr a1i cn0 cle wbr clt cmul 2cn
    wa cblen cfv crp nnre 2nn blennnelnn nnm1nn0 syl nnexpcld nnrpd modeqmodmin
    syl2anc cc0 nnred resubcld nnpw2blen subge0d ltsubadd2d cc exp1 eqcomd mp1i
    oveq1d nncnd 2timesd 1nn0 expaddd 1cnd pncan3d oveq2d eqtr3d 3eqtr3d breq2d
    bitrd anbi12d mpbird modid syl21anc eqtr2d nnz zmodcld nn0cnd subaddd mpbid
    nncn ) ABCZDAUAUBZEFGZHGZAWIIGZJGZAWFAWIFGZWJKWKAKWFWJWLWIIGZWLWFALCWIUCCZW
    JWMKAUDZWFWIWFDWHDBCWFUEMWFWGBCWHNCAUFZWGUGUHZUIZUJZAWIUKULWFWLLCWNUMWLOPZW
    LWIQPZTZWMWLKWFAWIWOWFWIWRUNZUOWSWFXBWIAOPZADWGHGZQPZTAUPWFWTXDXAXFWFAWIWOX
    CUQWFXAAWIWIJGZQPXFWFAWIWIWOXCXCURWFXGXEAQWFDWIRGDEHGZWIRGZXGXEWFDXHWIRDUSC
    ZDXHKWFSXJXHDDUTVAVBVCWFWIWFWIWRVDZVEWFDEWHJGZHGXIXEWFDEWHXJWFSMWQENCWFVFMV
    GWFXLWGDHWFEWGWFVHWFWGWPVDVIVJVKVLVMVNVOVPWLWIVQVRVSWFAWIWJAWEXKWFWJWFAWIAV
    TWRWAWBWCWDVA $.

  $( The binary length of 1.  (Contributed by AV, 21-May-2020.) $)
  blen1 $p |- ( #b ` 1 ) = 1 $=
    ( c1 cn wcel cblen cfv wceq 1nn c2 clogb co cfl caddc blennn cc0 cc wne 2cn
    2ne0 1ne2 ax-mp necomi logb1 mp3an fveq2i cz 0z flid eqtri a1i oveq1d 0p1e1
    eqtrdi eqtrd ) ABCZADEZAFGUNUOHAIJZKEZALJZAAMUNURNALJAUNUQNALUQNFUNUQNKEZNU
    PNKHOCHNPHAPUPNFQRAHSUAHUBUCUDNUECUSNFUFNUGTUHUIUJUKULUMT $.

  $( The binary length of 2.  (Contributed by AV, 21-May-2020.) $)
  blen2 $p |- ( #b ` 2 ) = 2 $=
    ( c2 cn wcel cblen cfv wceq 2nn clogb co cfl c1 caddc blennn cc cc0 wne 2cn
    2ne0 ax-mp a1i 1ne2 necomi logbid1 mp3an fveq2i cz flid eqtri oveq1d 3eqtrd
    1z 1p1e2 ) ABCZADEZAFGUMUNAAHIZJEZKLIKKLIZAAMUMUPKKLUPKFUMUPKJEZKUOKJANCAOP
    AKPUOKFQRKAUAUBAUCUDUEKUFCURKFUKKUGSUHTUIUQAFUMULTUJS $.

  ${
    $d N i r $.
    $( Every positive integer can be represented as the sum of a power of 2 and
       a "remainder" less than the power.  (Contributed by AV, 31-May-2020.) $)
    nnpw2p $p |- ( N e. NN -> E. i e. NN0 E. r e. ( 0 ..^ ( 2 ^ i ) )
                                    N = ( ( 2 ^ i ) + r ) ) $=
      ( cn wcel c2 cv cexp co caddc wceq cc0 cfzo wrex wb oveq2 eqeq2d rspcedvd
      cn0 adantl cfv c1 cmin blennnelnn nnm1nn0 syl oveq2d oveq1d rexeqbidv cmo
      cblen cz nnz 2nn a1i nnexpcld zmodfzo syl2anc nnpw2pmod ) BDEZBFAGZHIZCGZ
      JIZKZCLVBMIZNZBFBUKUAZUBUCIZHIZVCJIZKZCLVJMIZNZAVISUTVHDEVISEBUDVHUEUFZVA
      VIKZVGVNOUTVPVEVLCVFVMVPVBVJLMVAVIFHPZUGVPVDVKBVPVBVJVCJVQUHQUITUTVLBVJBV
      JUJIZJIZKZCVRVMUTBULEVJDEVRVMEBUMUTFVIFDEUTUNUOVOUPBVJUQURVCVRKZVLVTOUTWA
      VKVSBVCVRVJJPQTBUSRR $.

    $( A number is a positive integer iff it can be represented as the sum of a
       power of 2 and a "remainder" less than the power.  (Contributed by AV,
       31-May-2020.) $)
    nnpw2pb $p |- ( N e. NN <-> E. i e. NN0 E. r e. ( 0 ..^ ( 2 ^ i ) )
                                    N = ( ( 2 ^ i ) + r ) ) $=
      ( cn wcel c2 cv cexp caddc wceq cc0 cfzo wrex cn0 nnpw2p 2nn nnexpcl mpan
      co wa elfzonn0 nnnn0addcl syl2an eleq1 syl5ibrcom rexlimivv impbii ) BDEZ
      BFAGZHSZCGZISZJZCKUJLSZMANMABCOUMUHACNUNUINEZUKUNEZTUHUMULDEZUOUJDEZUKNEU
      QUPFDEUOURPFUIQRUKUJUAUJUKUBUCBULDUDUEUFUG $.
  $}

  $( The binary length of a nonnegative integer is 1 if the integer is 0 or 1.
     (Contributed by AV, 30-May-2020.) $)
  blen1b $p |- ( N e. NN0 -> ( ( #b ` N ) = 1 <-> ( N = 0 \/ N = 1 ) ) ) $=
    ( wcel cblen cfv c1 wceq cc0 wo c2 co caddc wbr clt wa crp a1i sylbid fveq2
    jaoi eqtrdi cn0 cn elnn0 clogb cfl blennn eqeq1d cle cmin wne 2rp nnrp 1ne2
    wi cr necomi relogbcl syl3anc flcld zcnd 1cnd addlsub 1m1e0 eqeq2d cz wb 0z
    flbi sylancl 3bitrd breq2i anbi2i nnlog2ge0lt1 biimpar olcd ex biimtrid orc
    0p1e1 a1d sylbi blen0 blen1 impbid1 ) AUABZACDZEFZAGFZAEFZHZWEAUBBZWHHWGWJU
    NZAUCWKWLWHWKWGIAUDJZUEDZEKJZEFZWJWKWFWOEAUFUGWKWPGWMUHLZWMGEKJZMLZNZWJWKWP
    WNEEUIJZFWNGFZWTWKWNEEWKWNWKWMWKIOBZAOBIEUJZWMUOBZXCWKUKPAULXDWKEIUMUPPIAUQ
    URZUSUTWKVAZXGVBWKXAGWNXAGFWKVCPVDWKXEGVEBXBWTVFXFVGWMGVHVIVJWTWQWMEMLZNZWK
    WJWSXHWQWREWMMVSVKVLWKXIWJWKXINWIWHWKWIXIAVMVNVOVPVQQQWHWJWGWHWIVRVTSWAWHWG
    WIWHWFGCDEAGCRWBTWIWFECDEAECRWCTSWD $.

  $( The binary length of a positive integer, doubled and increased by 1, is
     the binary length of the integer plus 1.  (Contributed by AV,
     30-May-2010.) $)
  blennnt2 $p |- ( N e. NN
                     -> ( #b ` ( 2 x. N ) ) = ( ( #b ` N ) + 1 ) ) $=
    ( cn wcel c2 cmul co cblen cfv clogb cfl c1 caddc wceq a1i blennn cc oveq2d
    2cn cc0 crp 2nn id nnmulcld syl nncn mulcomd cpr cdif cuz cz 2z eluz2cnn0n1
    uzid ax-mp mp1i nnrp 2rp relogbmul syl12anc wne 2ne0 necomi 3pm3.2i logbid1
    w3a 1ne2 3eqtrd fveq2d cr relogbcl syl3anc 1zzd fladdz syl2anc eqtrd oveq1d
    eqcomd ) ABCZDAEFZGHZDVSIFZJHZKLFZDAIFZJHKLFZKLFAGHZKLFVRVSBCVTWCMVRDADBCVR
    UANVRUBUCVSOUDVRWBWEKLVRWBWDKLFZJHZWEVRWAWGJVRWADADEFZIFZWDDDIFZLFZWGVRVSWI
    DIVRDADPCZVRRNAUEUFQVRDPSKUGUHCZATCZDTCZWJWLMDDUIHCZWNVRDUJCWQUKDUMUNDULUOA
    UPZWPVRUQNZADDURUSVRWKKWDLWMDSUTZDKUTZVEWKKMVRWMWTXARVAKDVFVBZVCDVDUOQVGVHV
    RWDVICZKUJCWHWEMVRWPWOXAXCWSWRXAVRXBNDAVJVKVRVLWDKVMVNVOVPVRWEWFKLVRWFWEAOV
    QVPVG $.

  $( The floor of the binary logarithm of an odd integer greater than 1 is the
     floor of the binary logarithm of the integer decreased by 1.  (Contributed
     by AV, 2-Jun-2020.) $)
  nnolog2flm1 $p |- ( ( N e. ( ZZ>= ` 2 ) /\ ( ( N + 1 ) / 2 ) e. NN )
                  -> ( |_ ` ( 2 logb N ) ) = ( |_ ` ( 2 logb ( N - 1 ) ) ) ) $=
    ( c2 cfv wcel c1 co cn wceq cexp wi syl wa wb adantl cle wbr cz a1i syl2anc
    cr cuz caddc cdiv clogb cfl cmin cblen cfzo wo eluz2nn nnpw2blenfzo2 bicomd
    wn nneo notnotb bitrdi con4bid simpl oveq1d cn0 blennnelnn nnnn0d 2m1e1 cc0
    cc wne 2cn 2ne0 1ne2 necomi logbid1 mp3an eluzle crp 2z uzid mp1i 2rp nnrpd
    logbleb syl3anc mpbid eqbrtrrid relogbcl 1zzd flge eqbrtrid 1red flcld zred
    2re lesubaddd blennn nn0ge2m1nn nnpw2even eqeltrd pm2.24d sylbid ex nnm1nn0
    breqtrrd ad2antlr nnpw2blenfzo npcan1 oveq2d eleqtrrd fllog2 clt w3a elfzo2
    nncnd eluz2 3anbi1i bitri 2nn jca nnexpcl peano2zm 3ad2ant2 adantr nnexpcld
    nnzd nnred leaddsub 3ad2ant3 imp syl3anbrc eleq1d mpbird ltle nnre reexpcld
    biimpcd syl11 simpll2 zlem1lt 3jca 3adant2 sylbi sylibr eqtr4d exp31 mpcom
    jaoi ) ABUACZDZAEUBFBUCFGDZBAUDFZUECZBAEUFFZUDFUECZHZABAUGCZEUFFZIFZHZAUUOE
    UBFZBUUMIFZUHFDZUIZUUFUUGUULJZUUFAGDZUUTAUJZAUKKUUPUUFUVAJUUSUUPUUFUVAUUPUU
    FLZUUGABUCFZGDZUMZUULUVDUUGUVGUVDUUGUMZUVFUVGUMUVDUVBUVHUVFMUUFUVBUUPUVCNUV
    BUVFUVHAUNULKUVFUOUPUQUVDUVFUULUVDUVEUUOBUCFZGUVDAUUOBUCUUPUUFURUSUVDUUNGDZ
    UVIGDUUFUVJUUPUUFUUMUTDZBUUMOPUVJUUFUVBUVKUVCUVBUUMAVAZVBZKZUUFBUUIEUBFZUUM
    OUUFBEUFFZUUIOPBUVOOPUUFUVPEUUIOVCUUFEUUHOPZEUUIOPZUUFEBBUDFZUUHOBVEDBVDVFB
    EVFZUVSEHVGVHEBVIVJZBVKVLUUFBAOPZUVSUUHOPZBAVMUUFBUUEDZBVNDZAVNDZUWBUWCMBQD
    UWDUUFVOBVPVQUWEUUFVRRZUUFAUVCVSZBBAVTWAWBWCUUFUUHTDZEQDUVQUVRMUUFUWEUWFUVT
    UWIUWGUWHUVTUUFUWARBAWDWAZUUFWEUUHEWFSWBWGUUFBEUUIBTDZUUFWKRUUFWHZUUFUUIUUF
    UUHUWJWIWJWLWBUUFUVBUUMUVOHUVCAWMKXAUUMWNSNUUNWOKWPWQWRWSUUSUUFUUGUULUUSUUF
    LZUUGLZUUIUUNUUKUWNUUNUTDZAUUOBUUNEUBFZIFZUHFZDUUIUUNHUUFUWOUUSUUGUUFUUMGDZ
    UWOUUFUVBUWSUVCUVLKZUUMWTZKZXBUWNAUUOUURUHFZUWRUWNUVBAUXCDUUFUVBUUSUUGUVCXB
    AXCKUWNUWQUURUUOUHUWNUWPUUMBIUWNUUMVEDZUWPUUMHZUUFUXDUUSUUGUUFUUMUWTXKZXBUU
    MXDZKXEXEXFUUNAXGSUWNUWOUUJUWRDZUUKUUNHUWNUWSUWOUUFUWSUUSUUGUWTXBUXAKUWMUXH
    UUGUWMUUJUUOUACDZUWQQDZUUJUWQXHPZXIZUXHUUSUUFUXLUUSUUQQDZAQDZUUQAOPZXIZUURQ
    DZAUURXHPZXIZUUFUXLJZUUSAUUQUACDZUXQUXRXIUXSAUUQUURXJUYAUXPUXQUXRUUQAXLXMXN
    UXPUXRUXTUXQUXPUXRLZUUFUXLUYBUUFLZUXIUXJUXKUYCUUOQDUUJQDZUUOUUJOPZUXIUYCUUO
    UYCBGDZUWOLZUUOGDUUFUYGUYBUUFUYFUWOUYFUUFXORZUXBXPNBUUNXQKYBUYBUYDUUFUXPUYD
    UXRUXNUXMUYDUXOAXRXSXTXTUYBUUFUYEUXPUUFUYEJZUXRUXOUXMUYIUXNUUFUXOUYEUUFUUOT
    DETDATDZUXOUYEMUUFUUOUUFBUUNUYHUXBYAYCUWLUUFAUVCYCUUOEAYDWAYMYEXTYFUUOUUJXL
    YGUYCUWQUYCUYFUWPUTDZLZUWQGDUUFUYLUYBUUFUYFUYKUYHUUFUYKUVKUVNUUFUXDUYKUVKMU
    XFUXDUWPUUMUTUXGYHKYIXPNBUWPXQKYBUYCUUJUURUWQXHUYCAUUROPZUUJUURXHPZUYBUUFUY
    MUXRUUFUYMJUXPUYJUURTDZLZUXRUYMUUFAUURYJUUFUVBUYPUVCUVBUYJUYOAYKUVBBUUMUWKU
    VBWKRUVMYLXPKYNNYFUYCUXNUXQUYMUYNMUXMUXNUXOUXRUUFYOUUFUXQUYBUUFUURUUFBUUMUY
    HUVNYAYBNAUURYPSWBUUFUWQUURHUYBUUFUWPUUMBIUUFUXDUXEUXFUXGKXENXAYQWSYRYSYFUU
    JUUOUWQXJYTXTUUNUUJXGSUUAUUBUUDUUCYF $.

  $( The binary length of the half of an even positive integer is the binary
     length of the integer minus 1.  (Contributed by AV, 30-May-2010.) $)
  blennn0em1 $p |- ( ( N e. NN /\ ( N / 2 ) e. NN0 )
                     -> ( #b ` ( N / 2 ) ) = ( ( #b ` N ) - 1 ) ) $=
    ( cn wcel c2 cdiv co cn0 wa cblen cfv c1 cmin wceq caddc cmul adantr eqcomd
    cc syl nncnd cc0 wne w3a nncn 2cnd 2ne0 a1i divcan2 fveq2d nn0enne blennnt2
    3jca biimpa eqtr2d blennnelnn 1cnd blennn0elnn adantl subadd2d mpbird ) ABC
    ZADEFZGCZHZAIJZKLFZVBIJZVDVFVGMVGKNFZVEMVDVEDVBOFZIJZVHVDAVIIVDARCZDRCZDUAU
    BZUCZAVIMVAVNVCVAVKVLVMAUDVAUEVMVAUFUGULPVNVIAADUHQSUIVDVBBCZVJVHMVAVCVOAUJ
    UMVBUKSUNVDVEKVGVAVERCVCVAVEAUOTPVDUPVCVGRCVAVCVGVBUQTURUSUTQ $.

  $( The binary length of an odd integer greater than 1 is the binary length of
     the half of the integer decreased by 1, increased by 1.  (Contributed by
     AV, 3-Jun-2020.) $)
  blennngt2o2 $p |- ( ( N e. ( ZZ>= ` 2 ) /\ ( ( N + 1 ) / 2 ) e. NN0 )
                      -> ( #b ` N ) = ( ( #b ` ( ( N - 1 ) / 2 ) ) + 1 ) ) $=
    ( c2 cfv wcel c1 caddc co cmin clogb cfl crp wceq adantr oveq1d a1i syl cc0
    wa cn clt cuz cdiv cn0 cblen csn cdif wne 2rp 1ne2 eldifsn mpbir2an uz2m1nn
    necomi nnrpd relogbdivb sylancr fveq2d cr cz relogbcl 1z jctir flsubz flcld
    syl3anc cc zcnd npcan1 wbr eluz2nn peano2nnd nnred eluzge2nn0 nn0p1gt0 2pos
    2re divgt0d nn0z anim12ci elnnz sylibr nnolog2flm1 syldan eqtr4d 3eqtrd nno
    blennn 3eqtr4rd ) ABUACDZAEFGZBUBGZUCDZRZBAEHGZBUBGZIGZJCZEFGZEFGZBAIGJCZEF
    GZWOUDCZEFGZAUDCZWMWRWTEFWMWRBWNIGZEHGZJCZEFGXEJCZEHGZEFGZWTWMWQXGEFWMWPXFJ
    WMBKEUEUFDZWNKDZWPXFLXKBKDZBEUGZUHEBUIUMZBKEUJUKWIXLWLWIWNAULUNZMWNBUOUPUQN
    WMXGXIEFWMXEURDZEUSDZRZXGXILWIXSWLWIXQXRWIXMXLXNXQXMWIUHOXPXNWIXOOBWNUTVEZV
    AVBMXEEVCPNWMXJXHWTWIXJXHLZWLWIXHVFDYAWIXHWIXEXTVDVGXHVHPMWIWLWKSDZWTXHLWMW
    KUSDZQWKTVIZRYBWIYDWLYCWIWJBWIWJWIAAVJZVKVLBURDWIVPOWIAUCDQWJTVIAVMAVNPQBTV
    IWIVOOVQWKVRVSWKVTWAAWBWCWDWENWMWOSDZXCWSLAWFYFXBWREFWOWGNPWIXDXALZWLWIASDY
    GYEAWGPMWH $.

  $( The binary length of an integer greater than 1 is the binary length of the
     integer divided by 2, increased by one.  (Contributed by AV,
     3-Jun-2020.) $)
  blengt1fldiv2p1 $p |- ( N e. ( ZZ>= ` 2 )
                       -> ( #b ` N ) = ( ( #b ` ( |_ ` ( N / 2 ) ) ) + 1 ) ) $=
    ( c2 cdiv co cn wcel c1 caddc cfv cblen wceq syl wa cn0 nnnn0 sylan2 ancoms
    cmin oveq1d eqcomd wo cuz cfl eluz2nn nneop wi blennn0em1 nnz fveq2d adantr
    cz flid cc blennnelnn nncnd npcan1 adantl 3eqtr3rd expcom syl11 blennngt2o2
    eluzge2nn0 nn0ofldiv2 syl2anr eqtrd ex jaoi mpcom ) ABCDZEFZAGHDBCDZEFZUAZA
    BUBIFZAJIZVIUCIZJIZGHDZKZVNAEFZVMAUDZAUELVJVNVSUFVLVTVJVSVNVJVTVSVJVTMZVIJI
    ZGHDZVOGRDZGHDZVRVOWBWCWEGHVTVJWCWEKZVJVTVINFWGVIOAUGPQSVJWDVRKVTVJWCVQGHVJ
    VIVPJVJVPVIVJVIUKFVPVIKVIUHVIULLTUISUJVTWFVOKZVJVTVOUMFWHVTVOAUNUOVOUPLUQUR
    USWAUTVLVNVSVLVNMZVOAGRDBCDZJIZGHDZVRVNVLVOWLKZVLVNVKNFZWMVKOZAVAPQWIWKVQGH
    WIWJVPJWIVPWJVNANFWNVPWJKVLAVBWOAVCVDTUISVEVFVGVH $.

  $( The binary length of an even positive integer is the binary length of the
     half of the integer, increased by 1.  (Contributed by AV, 29-May-2020.) $)
  blennn0e2 $p |- ( ( N e. NN /\ ( N / 2 ) e. NN0 )
                    -> ( #b ` N ) = ( ( #b ` ( N / 2 ) ) + 1 ) ) $=
    ( cn wcel c2 co wa clogb cfl cfv c1 caddc cblen cmin crp wceq adantr oveq1d
    2rp a1i syl cdiv cn0 csn cdif wne 1ne2 necomi eldifsn mpbir2an nnrp sylancr
    relogbdivb fveq2d cr cz relogbcl syl3anc 1zzd flsubz cc flcld npcan1 3eqtrd
    jca zcnd nn0enne biimpa blennn 3eqtr4rd ) ABCZADUAEZUBCZFZDVKGEZHIZJKEZJKEZ
    DAGEZHIZJKEZVKLIZJKEZALIZVMVPVSJKVMVPVRJMEZHIZJKEVSJMEZJKEZVSVMVOWEJKVMVNWD
    HVMDNJUCUDCZANCZVNWDOWHDNCZDJUEZRJDUFUGZDNJUHUIVJWIVLAUJZPADULUKUMQVMWEWFJK
    VMVRUNCZJUOCZFZWEWFOVJWPVLVJWNWOVJWJWIWKWNWJVJRSWMWKVJWLSDAUPUQZVJURVDPVRJU
    STQVJWGVSOZVLVJVSUTCWRVJVSVJVRWQVAVEVSVBTPVCQVMVKBCZWBVQOVJVLWSAVFVGWSWAVPJ
    KVKVHQTVJWCVTOVLAVHPVI $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Digits
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Generalization of ~ df-bits .  In contrast to ` digit ` , ` bits ` are
  defined for integers only.  The equivalence of both definitions for integers
  is shown in ~ dig2bits : if ` K ` and ` N ` are nonnegative integers, then
  ` ( ( K ( digit `` 2 ) N ) = 1 <-> K e. ( bits `` N ) ) ` .

$)

  $c digit $. $( The class of the digit extraction operation. $)

  $( Extend class notation with the class of the digit extraction operation. $)
  cdig $a class digit $.

  ${
    $d b k r $.
    $( Definition of an operation to obtain the ` k ` th digit of a nonnegative
       real number ` r ` in the positional system with base ` b ` . ` k = - 1 `
       corresponds to the first digit of the fractional part (for ` b = ` 10
       the first digit after the decimal point), ` k = ` 0 corresponds to the
       last digit of the integer part (for ` b = ` 10 the first digit before
       the decimal point).  See also ~ digit1 .  Examples (not formal):
       ( 234.567 ( digit `` 10 ) 0 ) = 4; ( 2.567 ( digit `` 10 ) -2 ) = 6;
       ( 2345.67 ( digit `` 10 ) 2 ) = 3.  (Contributed by AV, 16-May-2020.) $)
    df-dig $a |- digit = ( b e. NN |-> ( k e. ZZ , r e. ( 0 [,) +oo )
                            |-> ( ( |_ ` ( ( b ^ -u k ) x. r ) ) mod b ) ) ) $.

    $d B b k r $.
    $( Operation to obtain the ` k ` th digit of a nonnegative real number
       ` r ` in the positional system with base ` B ` .  (Contributed by AV,
       23-May-2020.) $)
    digfval $p |- ( B e. NN -> ( digit ` B ) = ( k e. ZZ , r e. ( 0 [,) +oo )
                            |-> ( ( |_ ` ( ( B ^ -u k ) x. r ) ) mod B ) ) ) $=
      ( vb cn wcel cz cc0 cpnf cico co cv cexp cmul cfl cfv cmo cmpo cvv id zex
      cneg cdig df-dig wceq oveq1 fvoveq1d oveq12d mpoeq3dv wa ovex pm3.2i eqid
      mpoexg mp1i fvmptd3 ) AEFZDABCGHIJKZDLZBLUBZMKZCLZNKOPZUSQKZRBCGURAUTMKZV
      BNKOPZAQKZRZEUCSBCDUDUSAUEZBCGURVDVGVIVCVFUSAQVIVAVEVBONUSAUTMUFUGVITUHUI
      UQTGSFZURSFZUJVHSFUQVJVKUAHIJUKULBCGURVGSSVHVHUMUNUOUP $.

    $d K k r $.  $d R k r $.
    $( The ` K ` th digit of a nonnegative real number ` R ` in the positional
       system with base ` B ` .  (Contributed by AV, 23-May-2020.) $)
    digval $p |- ( ( B e. NN /\ K e. ZZ /\ R e. ( 0 [,) +oo ) )
                   -> ( K ( digit ` B ) R )
                      = ( ( |_ ` ( ( B ^ -u K ) x. R ) ) mod B ) ) $=
      ( vk vr cn wcel cz cc0 cpnf cico co cv cneg cexp cmul cfl cfv cmo wceq wa
      w3a cdig cvv cmpo digfval negeq oveq2d adantr simpr oveq12d fveq2d oveq1d
      3ad2ant1 adantl simp2 simp3 ovexd ovmpod ) AFGZCHGZBIJKLZGZUBZDECBHVBADMZ
      NZOLZEMZPLZQRZASLZACNZOLZBPLZQRZASLZAUCRZUDUTVAVQDEHVBVKUETVCADEUFUNVECTZ
      VHBTZUAZVKVPTVDVTVJVOASVTVIVNQVTVGVMVHBPVRVGVMTVSVRVFVLAOVECUGUHUIVRVSUJU
      KULUMUOUTVAVCUPUTVAVCUQVDVOASURUS $.
  $}

  $( The ` K ` th digit of a nonnegative real number ` R ` in the positional
     system with base ` B ` is a nonnegative integer.  (Contributed by AV,
     28-May-2020.) $)
  digvalnn0 $p |- ( ( B e. NN /\ K e. ZZ /\ R e. ( 0 [,) +oo ) )
                    -> ( K ( digit ` B ) R ) e. NN0 ) $=
    ( cn wcel cz cc0 cpnf cico co w3a cdig cfv cneg cexp cmul cfl cmo 3ad2ant1
    cr cn0 digval nnre wne nnne0 znegcl 3ad2ant2 reexpclzd cle elrege0 3ad2ant3
    wbr simplbi remulcld flcld simp1 zmodcld eqeltrd ) ADEZCFEZBGHIJEZKZCBALMJA
    CNZOJZBPJZQMZARJUAABCUBVBVFAVBVEVBVDBVBAVCUSUTATEVAAUCSUSUTAGUDVAAUESUTUSVC
    FEVACUFUGUHVAUSBTEZUTVAVGGBUIULBUJUMUKUNUOUSUTVAUPUQUR $.

  $( The ` K ` th digit of a nonnegative real number ` R ` in the positional
     system with base ` B ` .  (Contributed by AV, 23-May-2020.) $)
  nn0digval $p |- ( ( B e. NN /\ K e. NN0 /\ R e. ( 0 [,) +oo ) )
                    -> ( K ( digit ` B ) R )
                       = ( ( |_ ` ( R / ( B ^ K ) ) ) mod B ) ) $=
    ( cn wcel cc0 co cfv cexp cmul cfl cmo cdiv wceq wa cc syl 3adant3 3ad2ant1
    oveq1d cn0 cpnf cico cdig cneg cz nn0z digval syl3an2 c1 nncn anim1i expneg
    w3a cle wbr elrege0 recn adantr sylbi 3ad2ant3 expcl nnne0 3ad2ant2 expne0d
    cr wne divrec2d eqtr4d fveq2d eqtrd ) ADEZCUAEZBFUBUCGEZUNZCBAUDHGZACUEIGZB
    JGZKHZALGZBACIGZMGZKHZALGVMVLCUFEZVNVPVTNCUGZABCUHUIVOVSWCALVOVRWBKVOVRUJWA
    MGZBJGWBVOVQWFBJVLVMVQWFNZVNVLVMOAPEZVMOZWGVLWHVMAUKZULZACUMQRTVOBWAVNVLBPE
    ZVMVNBVFEZFBUOUPZOWLBUQWMWLWNBURUSUTVAVOWIWAPEVLVMWIVNWKRACVBQVOACVLVMWHVNW
    JSVLVMAFVGVNAVCSVMVLWDVNWEVDVEVHVIVJTVK $.

  $( The digits of the fractional part of a nonnegative integer are 0.
     (Contributed by AV, 23-May-2020.) $)
  dignn0fr $p |- ( ( B e. NN /\ K e. ( ZZ \ NN0 ) /\ N e. NN0 )
                    -> ( K ( digit ` B ) N ) = 0 ) $=
    ( cn wcel cz cn0 co cmul cmo wceq cr wa syl2an 3adant3 3ad2ant3 cc 3ad2ant1
    cc0 eqtrd cdif w3a cdig cfv cneg cexp cfl cpnf cico id eldifi cle wbr nn0re
    nn0ge0 elrege0 sylanbrc digval syl3an nnz eldif znnn0nn sylbi nnnn0d zexpcl
    wn nn0z zmulcld flid syl oveq1d cdiv cmin wne nnre reexpcl recnd nn0cn nncn
    c1 nnne0 div23 syl3anc nnzd 3ad2ant2 expm1d eqcomd nnm1nn0 eqeltrd remulcld
    jca crp wb nnrp mod0 syl2anc mpbird ) ADEZBFGUAEZCGEZUBZBCAUCUDHZABUEZUFHZC
    IHZUGUDZAJHZSWRWRWSBFEZWTCSUHUIHEZXBXGKWRUJBFGUKWTCLEZSCULUMXICUNZCUOCUPUQA
    CBURUSXAXGXEAJHZSXAXFXEAJXAXEFEXFXEKXAXDCWRWSXDFEZWTWRAFEZXCGEZXMWSAUTZWSXC
    WSXHBGEVFMXCDEZBFGVABVBVCZVDZAXCVENOWTWRCFEWSCVGPZVHXEVIVJVKXAXLSKZXEAVLHZF
    EZXAYBAXCVTVMHZUFHZCIHZFXAYBXDAVLHZCIHZYFXAXDQEZCQEZAQEZASVNZMZYBYHKWRWSYIW
    TWRWSMXDWRALEXOXDLEZWSAVOXSAXCVPNZVQOWTWRYJWSCVRPWRWSYMWTWRYKYLAVSZAWAZWKRX
    DCAWBWCXAYGYECIXAYEYGXAAXCWRWSYKWTYPRWRWSYLWTYQRWSWRXCFEWTWSXCXRWDWEWFWGVKT
    XAYECWRWSYEFEZWTWRXNYDGEZYRWSXPWSXQYSXRXCWHVJAYDVENOXTVHWIXAXELEAWLEZYAYCWM
    XAXDCWRWSYNWTYOOWTWRXJWSXKPWJWRWSYTWTAWNRXEAWOWPWQTT $.

  $( Lemma for ~ dignnld .  (Contributed by AV, 25-May-2020.) $)
  dignn0ldlem $p |- ( ( B e. ( ZZ>= ` 2 ) /\ N e. NN
                        /\ K e. ( ZZ>= ` ( ( |_ ` ( B logb N ) ) + 1 ) ) )
                      -> N < ( B ^ K ) ) $=
    ( c2 cfv wcel co c1 w3a clt wbr cr 3ad2ant1 cc0 cle wa adantl cc wi adantr
    cuz cn clogb cfl caddc ccxp cexp nnre 3ad2ant2 eluzelre eluz2nn nn0ge0d syl
    nnnn0 crp nnrp relogbzcl sylan2 3adant3 recxpcld 3ad2ant3 cpr cdif csn wceq
    leidd eluz2cnn0n1 nncn nnne0 eldifsn sylanbrc cxplogb syl2an breqtrrd eluz2
    wne cz flltp1 zre ltletr syl3anc mpand com23 3impia com12 biimtrid eluz2gt1
    ex jca cxplt syl12anc mpbid lelttrd eluzelcn eluz2n0 eluzelz cxpexpz breq2d
    wb ) ADUAEFZCUBFZBACUCGZUDEHUEGZUAEFZIZCABUFGZJKZCABUGGZJKZXECAXBUFGZXFXAWT
    CLFXDCUHZUIXEAXBWTXAALFZXDDAUJZMZWTXANAOKZXDWTAUBFZXOAUKXPAAUNULUMMZWTXAXBL
    FZXDXAWTCUOFXRCUPACUQURZUSZUTXEABXNXQXDWTBLFZXAXCBUJVAZUTWTXACXJOKXDWTXAPZC
    CXJOXACCOKWTXACXKVFQWTARNHVBVCFCRNVDVCFZXJCVEXAAVGXACRFCNVPYDCVHCVICRNVJVKA
    CVLVMVNUSXEXBBJKZXJXFJKZWTXAXDYEXDXCVQFZBVQFZXCBOKZIZYCYEXCBVOYJYCYEYGYHYIY
    CYESYGYHPZYCYIYEYKYCYIYESYKYCPZXBXCJKZYIYEYLXRYMYCXRYKXSQZXBVRUMYLXRXCLFZYA
    YMYIPYESYNYKYOYCYGYOYHXCVSTTYKYAYCYHYAYGBVSQTXBXCBVTWAWBWHWCWDWEWFWDXEXLHAJ
    KZPZXRYAYEYFWSWTXAYQXDWTXLYPXMAWGWIMXTYBAXBBWJWKWLWMXEARFZANVPZYHXGXIWSWTXA
    YRXDDAWNMWTXAYSXDAWOMXDWTYHXAXCBWPVAYRYSYHIXFXHCJABWQWRWAWL $.

  $( The leading digits of a positive integer are 0.  (Contributed by AV,
     25-May-2020.) $)
  dignnld $p |- ( ( B e. ( ZZ>= ` 2 ) /\ N e. NN
                     /\ K e. ( ZZ>= ` ( ( |_ ` ( B logb N ) ) + 1 ) ) )
                   -> ( K ( digit ` B ) N ) = 0 ) $=
    ( c2 cfv wcel co c1 cmo cc0 cn0 cico 3ad2ant1 wa cr cle wbr syl wb clt cdig
    cuz cn clogb cfl caddc w3a cexp cdiv cpnf wceq eluz2nn crp anim2i relogbzcl
    nnrp nnre nnge1 elicopnf ax-mp sylibr rege1logbzge0 flge0nn0 peano2nn0 3syl
    jca 1re eluznn0 stoic3 nnnn0 nn0rp0 3ad2ant2 nn0digval syl3anc eluzelre wne
    eluz2n0 cz eluzelz 3ad2ant3 reexpclzd eluzelcn expne0d nn0ge0 nngt0d expgt0
    cc redivcld ge0div mpbid dignn0ldlem nnrpd rpexpcl 3adant2 divlt1lt syl2anc
    syl2an mpbird cxr 0re 1xr pm3.2i elico2 mp1i mpbir3and ico01fl0 oveq1d 0mod
    3eqtrd ) ADUBEFZCUCFZBACUDGZUEEZHUFGZUBEFZUGZBCAUAEGZCABUHGZUIGZUEEZAIGZJAI
    GZJXPAUCFZBKFZCJUJLGFZXQYAUKXJXKYCXOAULZMXJXKXNKFZXOYDXJXKNZXLOFZJXLPQZNXMK
    FYGYHYIYJYHXJCUMFZNYIXKYKXJCUPUNACUORYHXJCHUJLGFZNYJXKYLXJXKCOFZHCPQZNZYLXK
    YMYNCUQZCURVFHOFYLYOSVGHCUSUTVAUNACVBRVFXLVCXMVDVEBXNVHVIXKXJYEXOXKCKFZYECV
    JZCVKRVLACBVMVNXPXTJAIXPXSJHLGFZXTJUKXPYSXSOFZJXSPQZXSHTQZXPCXRXKXJYMXOYPVL
    ZXPABXJXKAOFZXODAVOMZXJXKAJVPXOAVQMZXOXJBVRFZXKXNBVSZVTZWAZXPABXJXKAWGFXODA
    WBMUUFUUIWCWHXPJCPQZUUAXKXJUUKXOXKYQUUKYRCWDRVLXPYMXROFJXRTQZUUKUUASUUCUUJX
    PUUDUUGJATQZUULUUEUUIXJXKUUMXOXJAYFWEMABWFVNCXRWIVNWJXPUUBCXRTQZABCWKXPYMXR
    UMFZUUBUUNSUUCXJXOUUOXKXJAUMFZUUGUUOXOXJAYFWLZUUHABWMWQWNCXRWOWPWRJOFZHWSFZ
    NYSYTUUAUUBUGSXPUURUUSWTXAXBJHXSXCXDXEXSXFRXGXPUUPYBJUKXJXKUUPXOUUQMAXHRXI
    $.

  $( The leading digits of a positive integer in a binary system are 0.
     (Contributed by AV, 25-May-2020.) $)
  dig2nn0ld $p |- ( ( N e. NN /\ K e. ( ZZ>= ` ( #b ` N ) ) )
                    -> ( K ( digit ` 2 ) N ) = 0 ) $=
    ( cn wcel cblen cfv cuz wa c2 clogb co cfl c1 caddc cdig cc0 wceq cz uzid
    2z mp1i simpl blennn fveq2d eleq2d biimpa dignnld syl3anc ) BCDZABEFZGFZDZH
    ZIIGFDZUIAIBJKLFMNKZGFZDZABIOFKPQIRDUNUMTISUAUIULUBUIULUQUIUKUPAUIUJUOGBUCU
    DUEUFIABUGUH $.

  $( The first (relevant) digit of a positive integer in a binary system is 1.
     (Contributed by AV, 26-May-2020.) $)
  dig2nn1st $p |- ( N e. NN -> ( ( ( #b ` N ) - 1 ) ( digit ` 2 ) N ) = 1 ) $=
    ( cn wcel cfv c1 cmin co c2 cexp cdiv cfl cc0 a1i syl cr wbr cdvds cz eqtrd
    wceq cblen cdig cmo cn0 cpnf cico 2nn blennnelnn nnm1nn0 nnre nnnn0 nn0ge0d
    cle elrege0 sylanbrc nn0digval syl3anc wn n2dvds1 clogb caddc blennn oveq1d
    cc cuz 2z uzid ax-mp nnrp relogbzcl sylancr flcld zcnd pncan1 oveq2d fveq2d
    crp fldivexpfllog2 breq2d mtbiri wb 2re reexpcld 2cnd 2ne0 expne0d redivcld
    wne nn0zd mod2eq1n2dvds mpbird ) ABCZAUADZEFGZAHUBDGZAHWNIGZJGZKDZHUCGZEWLH
    BCZWNUDCZALUEUFGCZWOWSTWTWLUGMWLWMBCXAAUHWMUINZWLAOCLAUMPXBAUJZWLAAUKULAUNU
    OHAWNUPUQWLWSETZHWRQPZURZWLXFHEQPUSWLWREHQWLWRAHHAUTGZKDZIGZJGZKDZEWLWQXKKW
    LWPXJAJWLWNXIHIWLWNXIEVAGZEFGZXIWLWMXMEFAVBVCWLXIVDCXNXITWLXIWLXHWLHHVEDCZA
    VQCZXHOCHRCXOVFHVGVHAVIZHAVJVKVLVMXIVNNSVOVOVPWLXPXLETXQAVRNSVSVTWLWRRCXEXG
    WAWLWQWLAWPXDWLHWNHOCWLWBMXCWCWLHWNWLWDHLWHWLWEMWLWNXCWIWFWGVLWRWJNWKS $.

  $( All digits of 0 are 0.  (Contributed by AV, 24-May-2020.) $)
  dig0 $p |- ( ( B e. NN /\ K e. ZZ ) -> ( K ( digit ` B ) 0 ) = 0 ) $=
    ( cn wcel cz wa cc0 cdig cfv co cneg cexp cmul cfl cmo cpnf wceq adantr syl
    eqtrd cico 0e0icopnf digval mp3an3 cc nncn wne znegcl adantl expclzd mul01d
    nnne0 fveq2d 0zd flid oveq1d crp nnrp 0mod ) ACDZBEDZFZBGAHIJZABKZLJZGMJZNI
    ZAOJZGUTVAGGPUAJDVCVHQUBAGBUCUDVBVHGAOJZGVBVGGAOVBVGGNIZGVBVFGNVBVEVBAVDUTA
    UEDVAAUFRUTAGUGVAAULRVAVDEDUTBUHUIUJUKUMVBGEDVJGQVBUNGUOSTUPUTVIGQZVAUTAUQD
    VKAURAUSSRTT $.

  $( The ` K ` th digit of a power to the base is either 1 or 0.  (Contributed
     by AV, 24-May-2020.) $)
  digexp $p |- ( ( B e. ( ZZ>= ` 2 ) /\ K e. NN0 /\ N e. NN0 )
                 -> ( K ( digit ` B ) ( B ^ N ) ) = if ( K = N , 1 , 0 ) ) $=
    ( cfv wcel cexp co cfl cmo c1 cc0 wa cz 3ad2ant1 wbr adantr wb syl ad2antrl
    wceq c2 cuz cn0 w3a cdiv cmin cdig cif wne eluzelcn eluz2nn nnne0d jca nn0z
    cc anim12i ancomd 3adant1 expsub syl2anc eqcomd fveq2d oveq1d cn cpnf simp2
    cico cr cle eluzelre reexpcl sylan simpr eluzge2nn0 nn0ge0d expge0d 3adant2
    elrege0 sylibr syl3anc nn0cn 3ad2ant3 3ad2ant2 subeq0ad mpbird oveq2d exp0d
    nn0digval eqtrd 1zzd flid eluz2gt1 1mod eqtr2d wn simprl1 adantl zsubcld wi
    clt nn0re sublt0d biimprd expnegico01 ico01fl0 crp nnrpd 0mod eluzelz lenlt
    impcom bicomd biimpd 3simpc nn0sub zexpcl expm1d wo pm4.56 axlttri biimtrid
    mpbid expdimp znnsub nnm1nn0 eqeltrd reexpclzd pm2.61ian ifeqda 3eqtr4d
    mod0 ) AUAUBDEZBUCEZCUCEZUDZACFGZABFGUEGZHDZAIGZACBUFGZFGZHDZAIGZBYPAUGDGZB
    CTZJKUHYOYRUUBAIYOYQUUAHYOUUAYQYOAUOEZAKUIZLZCMEZBMEZLZUUAYQTYLYMUUHYNYLUUF
    UUGUAAUJZYLAAUKZULZUMNYMYNUUKYLYMYNLZUUJUUIYMUUJYNUUIBUNZCUNZUPZUQURACBUSUT
    VAVBVCYOAVDEZYMYPKVEVGGEZUUDYSTYLYMUUSYNUUMNYLYMYNVFYOYPVHEZKYPVIOZLZUUTYLY
    NUVCYMYLYNLZUVAUVBYLAVHEZYNUVAUAAVJZACVKVLUVDACYLUVEYNUVFPYLYNVMYLKAVIOYNYL
    AAVNVOPVPUMVQYPVRVSAYPBWHVTYOUUEJKUUCYOUUELZUUCJAIGZJUVGUUBJAIUVGUUBJHDZJUV
    GUUAJHUVGUUAAKFGZJUVGYTKAFUVGYTKTZCBTZUVGBCYOUUEVMVAYOUVKUVLQUUEYOCBYNYLCUO
    EYMCWAWBYMYLBUOEYNBWAWCWDPWEWFYOUVJJTZUUEYLYMUVMYNYLAUULWGNPWIVBUVGJMEUVIJT
    UVGWJJWKRWIVCYOUVHJTZUUEYLYMUVNYNYLUVEJAWTOUVNUVFAWLAWMUTNPWNYOUUEWOZLZUUCK
    CBWTOZUVPUUCKTUVQUVPLZUUCKAIGZKUVRUUBKAIUVRUUAKJVGGEZUUBKTUVRYLYTMEZYTKWTOZ
    UVTYLYMYNUVOUVQWPYOUWAUVQUVOYMYNUWAYLUUOCBYNUUIYMUUQWQYMUUJYNUUPPWRURZSUVPU
    VQUWBYOUVQUWBWSUVOYOUWBUVQYOCBYNYLCVHEZYMCXAZWBYMYLBVHEZYNBXAZWCXBXCPXKAYTX
    DVTUUAXERVCYOUVSKTZUVQUVOYLYMUWHYNYLAXFEZUWHYLAUUMXGZAXHRNSWIUVQWOZUVPLZUUC
    UUAAIGZKUWLUUBUUAAIUWLUUAMEZUUBUUATUWLAMEZYTUCEZUWNYOUWOUWKUVOYLYMUWOYNUAAX
    INSZUWLBCVIOZUWPUVPUWKUWRYOUWKUWRWSZUVOYMYNUWSYLUUOUWKUWRUUOUWFUWDLZUWKUWRQ
    YMUWFYNUWDUWGUWEUPZUWTUWRUWKBCXJXLRXMURPXKUWLUUOUWRUWPQYOUUOUWKUVOYLYMYNXNS
    BCXORYBAYTXPUTUUAWKRVCUWLUWMKTZUUAAUEGZMEZUWLUXCAYTJUFGZFGZMYOUXCUXFTUWKUVO
    YOUXFUXCYOAYTYLYMUUFYNUULNYLYMUUGYNUUNNZUWCXQVASUWLUWOUXEUCEZUXFMEUWQUWLYTV
    DEZUXHUWLBCWTOZUXIUVPUWKUXJYOUVOUWKUXJUVOUWKLUUEUVQXRWOZYOUXJUUEUVQXSYOUXJU
    XKYOUWTUXJUXKQYMYNUWTYLUXAURBCXTRXCYAYCXKUWLUUJUUILZUXJUXIQYOUXLUWKUVOYMYNU
    XLYLUURURSBCYDRYBYTYERAUXEXPUTYFYOUXBUXDQZUWKUVOYOUUAVHEUWIUXMYOAYTYLYMUVEY
    NUVFNUXGUWCYGYLYMUWIYNUWJNUUAAYKUTSWEWIYHVAYIYJ $.

  $( All but one digits of 1 are 0.  (Contributed by AV, 24-May-2020.) $)
  dig1 $p |- ( ( B e. ( ZZ>= ` 2 ) /\ K e. ZZ )
               -> ( K ( digit ` B ) 1 ) = if ( K = 0 , 1 , 0 ) ) $=
    ( cc0 cle wbr c2 cfv wcel cz wa c1 co wceq ad2antrl cn0 syl3anc wn wi con3d
    a1i cuz cdig cif cexp exp0d eqcomd oveq2d simprl simpr anim2i ancomd elnn0z
    eluzelcn sylibr 0nn0 digexp eqtrd cn cdif eluz2nn simprr nn0ge0 impcom 1nn0
    eldifd dignn0fr 0le0 breq2 mpbiri iffalsed eqtr4d pm2.61ian ) CBDEZAFUAGHZB
    IHZJZBKAUBGZLZBCMZKCUCZMVMVPJZVRBACUDLZVQLZVTWAKWBBVQVNKWBMVMVOVNWBKVNAFAUM
    UEUFNUGWAVNBOHZCOHZWCVTMVMVNVOUHWAVOVMJWDWAVMVOVPVOVMVNVOUIUJUKBULUNWEWAUOT
    ABCUPPUQVMQZVPJZVRCVTWGAURHZBIOUSHKOHZVRCMVNWHWFVOAUTNWGBIOWFVNVOVAVPWFWDQV
    PWDVMWDVMRVPBVBTSVCVEWIWGVDTABKVFPWGVSKCVPWFVSQVPVSVMVSVMRVPVSVMCCDEVGBCCDV
    HVITSVCVJVKVL $.

  $( The ` 0 ` th digit of 1 is 1 in any positional system.  (Contributed by
     AV, 28-May-2020.) $)
  0dig1 $p |- ( B e. ( ZZ>= ` 2 ) -> ( 0 ( digit ` B ) 1 ) = 1 ) $=
    ( c2 cuz cfv wcel cc0 c1 cdig co wceq cif cz dig1 mpan2 eqid iftruei eqtrdi
    0z ) ABCDEZFGAHDIZFFJZGFKZGSFLETUBJRAFMNUAGFFOPQ $.

  $( The integers 0 and 1 correspond to their last bit.  (Contributed by AV,
     28-May-2010.) $)
  0dig2pr01 $p |- ( N e. { 0 , 1 } -> ( 0 ( digit ` 2 ) N ) = N ) $=
    ( cc0 c1 cpr wcel wceq wo c2 cdig cfv co elpri cn cz 2nn dig0 oveq2 3eqtr4a
    0z id mp2an cuz 2z uzid 0dig1 mp2b jaoi syl ) ABCDEABFZACFZGBAHIJZKZAFZABCL
    UIUMUJUIBBUKKZBULAHMEBNEUNBFOSHBPUAABBUKQUITRUJBCUKKZCULAHNEHHUBJEUOCFUCHUD
    HUEUFACBUKQUJTRUGUH $.

  $( A digit of a nonnegative integer ` N ` in a binary system is either 0 or
     1.  (Contributed by AV, 24-May-2020.) $)
  dig2nn0 $p |- ( ( N e. NN0 /\ K e. ZZ )
                  -> ( K ( digit ` 2 ) N ) e. { 0 , 1 } ) $=
    ( cn0 wcel cz wa c2 cdig cfv co cneg cexp cmul cfl cmo cc0 c1 a1i adantr cr
    cpr cn cpnf cico wceq 2nn simpr nn0rp0 digval syl3anc 2re wne znegcl adantl
    2ne0 reexpclzd nn0re remulcld flcld elmod2 syl eqeltrd ) BCDZAEDZFZABGHIJZG
    AKZLJZBMJZNIZGOJZPQUAZVEGUBDZVDBPUCUDJDZVFVKUEVMVEUFRVCVDUGVCVNVDBUHSGBAUIU
    JVEVJEDVKVLDVEVIVEVHBVEGVGGTDVEUKRGPULVEUORVDVGEDVCAUMUNUPVCBTDVDBUQSURUSVJ
    UTVAVB $.

  $( The last bit of an even integer is 0.  (Contributed by AV, 3-Jun-2010.) $)
  0dig2nn0e $p |- ( ( N e. NN0 /\ ( N / 2 ) e. NN0 )
                    -> ( 0 ( digit ` 2 ) N ) = 0 ) $=
    ( cn0 wcel c2 cdiv co wa cc0 cdig cfv cfl cmo a1i adantr c1 eqtrd oveq1d cz
    wceq nn0z cexp cn cpnf cico 2nn 0nn0 nn0rp0 nn0digval syl3anc 2cn exp0 mp1i
    cc oveq2d nn0cn div1d fveq2d flid syl adantl cr crp wb nn0re sylancl mpbird
    2rp mod0 ) ABCZADEFZBCZGZHADIJFZADHUAFZEFZKJZDLFZHVLDUBCZHBCZAHUCUDFCZVMVQS
    VRVLUEMVSVLUFMVIVTVKAUGNDAHUHUIVLVQAKJZDLFZHVLVPWADLVLVOAKVLVOAOEFZAVLVNOAE
    DUMCVNOSVLUJDUKULUNVIWCASVKVIAAUOUPNPUQQVLWBADLFZHVLWAADLVIWAASZVKVIARCWEAT
    AURUSNQVLWDHSZVJRCZVKWGVIVJTUTVLAVACZDVBCWFWGVCVIWHVKAVDNVGADVHVEVFPPP $.

  $( The last bit of an odd integer is 1.  (Contributed by AV, 3-Jun-2010.) $)
  0dig2nn0o $p |- ( ( N e. NN0 /\ ( ( N + 1 ) / 2 ) e. NN0 )
                    -> ( 0 ( digit ` 2 ) N ) = 1 ) $=
    ( cn0 wcel c1 co c2 cdiv cc0 cfv cfl cmo a1i adantr syl3anc eqtrd cz syl wb
    wceq mpbird caddc wa cdig cexp cpnf cico 2nn 0nn0 nn0rp0 nn0digval 2cn exp0
    cn cc mp1i oveq2d nn0cn div1d fveq2d oveq1d nn0z cdvds wbr wn adantl wne 2z
    flid 2ne0 peano2nn0 nn0zd dvdsval2 oddp1even mod2eq1n2dvds ) ABCZADUAEZFGEZ
    BCZUBZHAFUCIEZAFHUDEZGEZJIZFKEZDVSFUMCZHBCZAHUEUFECZVTWDSWEVSUGLWFVSUHLVOWG
    VRAUIMFAHUJNVSWDAJIZFKEZDVSWCWHFKVSWBAJVSWBADGEZAVSWADAGFUNCWADSVSUKFULUOUP
    VOWJASVRVOAAUQURMOUSUTVSWIAFKEZDVOWIWKSVRVOWHAFKVOAPCZWHASAVAZAVHQUTMVSWKDS
    ZFAVBVCVDZVSWOFVPVBVCZVSWPVQPCZVRWQVOVQVAVEVSFPCZFHVFZVPPCZWPWQRWRVSVGLWSVS
    VILVOWTVRVOVPAVJVKMFVPVLNTVOWOWPRZVRVOWLXAWMAVMQMTVSWLWNWORVOWLVRWMMAVNQTOO
    O $.

  $( The ` K ` th digit of a nonnegative integer ` N ` in a binary system is
     its ` K ` th bit.  (Contributed by AV, 24-May-2020.) $)
  dig2bits $p |- ( ( N e. NN0 /\ K e. NN0 )
                  -> ( ( K ( digit ` 2 ) N ) = 1 <-> K e. ( bits ` N ) ) ) $=
    ( cn0 wcel wa c2 cexp co cdiv cfv c1 wceq cz wb adantr a1i sylan cc0 nn0z
    cr cfl cmo cdvds wbr wn cdig cbits 2re reexpcl 2cnd wne 2ne0 adantl expne0d
    nn0re redivcld flcld mod2eq1n2dvds syl cpnf cico 2nn simpr nn0rp0 nn0digval
    cn syl3anc eqeq1d bitsval2 3bitr4d ) BCDZACDZEZBFAGHZIHZUAJZFUBHZKLZFVPUCUD
    UEZABFUFJHZKLABUGJDZVMVPMDVRVSNVMVOVMBVNVKBTDVLBUOOVKFTDZVLVNTDWBVKUHPFAUIQ
    VMFAVMUJFRUKVMULPVLAMDVKASUMUNUPUQVPURUSVMVTVQKVMFVFDZVLBRUTVAHDZVTVQLWCVMV
    BPVKVLVCVKWDVLBVDOFBAVEVGVHVKBMDVLWAVSNBSABVIQVJ $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Nonnegative integer as sum of its shifted digits
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Lemma 1 for ~ dignn0flhalf .  (Contributed by AV, 7-Jun-2012.) $)
  dignn0flhalflem1 $p |- ( ( A e. ZZ /\ ( ( A - 1 ) / 2 ) e. NN /\ N e. NN )
                           -> ( |_ ` ( ( A / ( 2 ^ N ) ) - 1 ) )
                              < ( |_ ` ( ( A - 1 ) / ( 2 ^ N ) ) ) ) $=
    ( cz wcel c1 cmin co c2 cdiv cexp cmo clt cr a1i 3ad2ant3 caddc wbr wceq wa
    cc0 cn w3a cfl cfv zre 3ad2ant1 crp rpexpcld rpred resubcld modcld peano2zm
    2rp nnz zred 1red readdcld cneg cif nnnn0 nnexpcld anim2i 3adant2 m1modmmod
    2nn syl wne wi zcn xp1d2m1eqxm1d2 eqcomd adantr eleq1d peano2z 1cnd halfcld
    cc addcld npcand imbitrid sylbid wn wb mod0 syl2an cmul nnzd nnm1nn0 zexpcl
    cn0 syl2anc adantl zmulcld ex zcnd negcld negsubd mvrladdd oveq2d 2cnd 2ne0
    simpr 1zzd zsubcld jca expsub syl21anc expn1 3eqtr3d rpcnne0d div12 syl3anc
    expcld divrecd 3eqtr4d sylibd zeo2 necon2ad 3syld com23 3imp iffalsed eqtrd
    neneqd neg1lt0 2re 1lt2 expgt1 mp3an13 posdifd mpbid renegcld 0red lttr mpi
    mpan2d recnd subsub4d 3brtr4d fldivmod eqbrtrd syl22anc modid0 modsubmodmod
    ltsubadd2b subid1d oveq1d modabs2 breqtrrd ltsub2dd ltdiv1dd expne0d fveq2d
    divsub1dir ) ACDZAEFGZHIGZUADZBUADZUBZAHBJGZFGZUVBUVAKGZFGZUVAIGZUUPUUPUVAK
    GZFGZUVAIGZAUVAIGZEFGZUCUDZUUPUVAIGUCUDZLUUTUVDUVGUVAUUTUVBUVCUUTAUVAUUOUUR
    AMDZUUSAUEZUFZUUSUUOUVAMDZUURUUSUVAUUSHBHUGDZUUSUMNBUNZUHZUIZOZUJZUUTUVBUVA
    UWBUUSUUOUVAUGDZUURUVSOZUKZUJUUTUUPUVFUUOUURUUPMDZUUSUUOUUPAULUOUFZUUTUUPUV
    AUWGUWDUKZUJUWDUUTAUVAUVCPGZFGAEUVFPGZFGUVDUVGLUUTUWJUWIAUUTEUVFUUTUPZUWHUQ
    UUTUVAUVCUWAUWEUQUVOUUTUWJUVAAUVAKGZPGZUWILUUTUVFUWLFGZUVAEFGZLQZUWJUWMLQZU
    UTUWNEURZUWOLUUTUWNUWLTRZUWOUWRUSZUWRUUTUUOUVAUADZSZUWNUWTRUUOUUSUXBUURUUSU
    XAUUOUUSHBHUADUUSVENZBUTVAVBVCAUVAVDVFUUTUWSUWOUWRUUTUWLTUUOUURUUSUWLTVGZUU
    OUUSUURUXDUUOUUSUURUXDVHUUOUUSSZUURUUQCDZAEPGZHIGZCDZUXDUURUXFVHUXEUUQUNNUX
    EUXFUXHEFGZCDZUXIUXEUUQUXJCUUOUUQUXJRZUUSUUOAVQDZUXLAVIZUXMUXJUUQAVJVKVFVLV
    MUXKUXJEPGZCDUXEUXIUXJVNUXEUXOUXHCUXEUXHEUXEUXGUXEAEUUOUXMUUSUXNVLZUXEVOZVR
    VPUXQVSVMVTWAUXEUXIUWLTUXEUWSAHIGZCDZUXIWBZUXEUWSUVICDZUXSUUOUVMUWCUWSUYAWC
    UUSUVNUVSAUVAWDWEUXEUYAHBEFGZJGZUVIWFGZCDZUXSUXEUYAUYEUXEUYASUYCUVIUXEUYCCD
    ZUYAUUSUYFUUOUUSHCDUYBWJDUYFUUSHUXCWGBWHZHUYBWIWKWLVLUXEUYAXBWMWNUXEUYDUXRC
    UXEAUYCUVAIGZWFGZAEHIGZWFGUYDUXRUXEUYHUYJAWFUXEHUYBBFGZJGZHUWRJGZUYHUYJUXEU
    YKUWRHJUXEUYBBUWRUXEBUUSBCDZUUOUVRWLZWOZUXEEUXQWPUXEBUWRPGUYBUXEBEUYPUXQWQV
    KWRWSUXEHVQDZHTVGZUYBCDZUYNSZUYLUYHRUXEWTZUYRUXEXANZUUSUYTUUOUUSUYSUYNUUSBE
    UVRUUSXCXDUVRXEWLHUYBBXFXGUXEUYQUYMUYJRVUAHXHVFXIWSUXEUYCVQDZUXMUVAVQDZUVAT
    VGZSUYDUYIRUUSVUCUUOUUSHUYBUUSWTZUYGXMWLUXPUXEUVAUXEHBUVQUXEUMNUYOUHXJUYCAU
    VAXKXLUXEAHUXPVUAVUBXNXOVMXPWAUUOUXSUXTWCUUSAXQVLXPXRXSWNXTYAYDYBYCUUSUUOUW
    RUWOLQZUURUUSUWRTLQZVUGYEUUSVUHTUWOLQZVUGUUSEUVALQZVUIHMDUUSEHLQVUJYFYGHBYH
    YIUUSEUVAUUSUPZUVTYJYKUUSUWRMDTMDUWOMDVUHVUISVUGVHUUSEVUKYLUUSYMUUSUVAEUVTV
    UKUJUWRTUWOYNXLYPYOOUUAUUTEMDUVPUWLMDUVFMDUWPUWQWCUWKUWAUUTAUVAUVOUWDUKZUWH
    EUVAUWLUVFUUEUUBYKUUTUVCUWLUVAPUUTUWLUVAUVAKGZFGZUVAKGZUWLUVAKGZUVCUWLUUTVU
    NUWLUVAKUUTVUNUWLTFGUWLUUTVUMTUWLFUUTUWCVUMTRUWDUVAUUCVFWSUUTUWLUUTUWLVULYQ
    UUFYCUUGUUTUVMUVPUWCVUOUVCRUVOUWAUWDAUVAUVAUUDXLUUTUVMUWCVUPUWLRUVOUWDAUVAU
    UHWKXIWSUUIUUJUUTAUVAUVCUUOUURUXMUUSUXNUFZUUTUVAUWAYQUUTUVCUWEYQYRUUTAEUVFV
    UQUUTVOUUTUVFUWHYQYRYSUUKUUTUVKUVBUVAIGZUCUDZUVEUUTUXMVUDVUEUVKVUSRVUQUUSUU
    OVUDUURUUSUVAUVTYQOUUSUUOVUEUURUUSHBVUFUYRUUSXANUVRUULOUXMVUDVUEUBUVJVURUCA
    UVAUUNUUMXLUUTUVBMDUWCVUSUVERUWBUWDUVBUVAYTWKYCUUTUWFUWCUVLUVHRUWGUWDUUPUVA
    YTWKYS $.

  $( Lemma 2 for ~ dignn0flhalf .  (Contributed by AV, 7-Jun-2012.) $)
  dignn0flhalflem2 $p |- ( ( A e. ZZ /\ ( ( A - 1 ) / 2 ) e. NN /\ N e. NN0 )
              -> ( |_ ` ( A / ( 2 ^ ( N + 1 ) ) ) )
                 = ( |_ ` ( ( |_ ` ( A / 2 ) ) / ( 2 ^ N ) ) ) ) $=
    ( cz wcel c1 cmin co c2 cdiv cfl cfv clt wbr cle wceq cr flcld a1i cc wa cn
    cn0 w3a cexp caddc zre rehalfcld zred 3ad2ant1 2re id reexpcld 3ad2ant3 cc0
    2cnd wne 2ne0 nn0z expne0d redivcld 1nn0 nn0addcld nn0p1nn dignn0flhalflem1
    simp3 peano2zd syl3an3 flsubz syl2anc eqcomd nnz zob imbitrrid imp zofldiv2
    1zzd syldan 3adant3 fvoveq1d cmul zcn 1cnd subcld crp 2rp rpcnne0d rpexpcld
    divdiv1 syl3an recnd mulcomd expp1d eqtr4d oveq2d fveq2d 3brtr4d reflcl syl
    eqtrd lediv1dd flwordi syl3anc rpcnd expp1zd breqtrrd zgtp1leeq syl22anc
    flle ) ACDZAEFGZHIGZUADZBUBDZUCZAHIGZJKZHBUDGZIGZJKZAHBEUEGZUDGZIGZJKZXNXSC
    DZYCCDZYCEFGZXSLMZXSYCNMZXSYCOZXNXRXNXPXQXIXLXPPDZXMXIXPXIXOXIAAUFZUGQUHUIX
    MXIXQPDXLXMHBHPDZXMUJRXMUKULUMZXNHBXNUOZHUNUPZXNUQRZXMXIBCDXLBURZUMZUSZUTZQ
    XNYBXNAYAXIXLAPDXMYKUIZXNHXTYLXNUJRXNBEXIXLXMVEZEUBDXNVARVBULXNHXTYNYPXNBYR
    VFUSUTZQXNYBEFGJKZXJYAIGZJKZYFXSLXMXIXLXTUADUUDUUFLMBVCAXTVDVGXNUUDYFXNYBPD
    ECDUUDYFOUUCXNVPYBEVHVIVJXNXSXKXQIGZJKUUFXNXPXKXQJIXIXLXPXKOZXMXIXLAEUEGHIG
    CDZUUHXIXLUUIXLUUIXIXKCDXKVKAVLVMVNAVOVQVRVSXNUUGUUEJXNUUGXJHXQVTGZIGZUUEXI
    XJSDXLHSDYOTZXMXQSDZXQUNUPTZUUGUUKOXIAEAWAZXIWBWCXLHHWDDZXLWERWFZXMXQXMHBUU
    PXMWERYQWGZWFZXJHXQWHWIXNUUJYAXJIXNUUJXQHVTGZYAXNHXQYNXNXQYMWJWKXNHBYNUUBWL
    WMWNWSWOWSWPXNXSXOXQIGZJKZYCNXNXRPDUVAPDXRUVANMXSUVBNMYTXNXOXQXNAUUAUGZYMYS
    UTXNXPXOXQXNXOPDZYJUVCXOWQWRUVCXNHBUUPXNWERYRWGXNUVDXPXONMUVCXOXHWRWTXRUVAX
    AXBXNYBUVAJXNUVAYBXNUVAAUUJIGZYBXIASDXLUULXMUUNUVAUVEOUUOUUQUUSAHXQWHWIXNUU
    JYAAIXNUUJUUTYAXNHXQYNXMXIUUMXLXMXQUURXCUMWKXNHBYNYPYRXDWMWNWSVJWOXEYDYETYG
    YHTYIYCXSXFVNXGVJ $.

  $( The digits of the half of an even nonnegative integer are the digits of
     the integer shifted by 1.  (Contributed by AV, 3-Jun-2010.) $)
  dignn0ehalf $p |- ( ( ( A / 2 ) e. NN0 /\ A e. NN0 /\ I e. NN0 )
                      -> ( ( I + 1 ) ( digit ` 2 ) A )
                         = ( I ( digit ` 2 ) ( A / 2 ) ) ) $=
    ( c2 cdiv co cn0 wcel cexp cfl cfv cmo cmul cc cc0 wne wa wceq a1i 3ad2ant3
    syl3anc w3a c1 caddc cdig nn0cn 3ad2ant2 2cnne0 2nn0 id nn0expcld 2cnd 2ne0
    nn0cnd expne0d jca divdiv1 mulcomd simp3 expp1d eqtr4d oveq2d eqtr2d fveq2d
    nn0z oveq1d cn cpnf cico 2nn peano2nn0 nn0rp0 nn0digval 3ad2ant1 3eqtr4d )
    ACDEZFGZAFGZBFGZUAZACBUBUCEZHEZDEZIJZCKEZVOCBHEZDEZIJZCKEZVTACUDJZEZBVOWIEZ
    VSWCWGCKVSWBWFIVSWFACWELEZDEZWBVSAMGZCMGCNOZPZWEMGZWENOZPZWFWMQVQVPWNVRAUEU
    FWPVSUGRVRVPWSVQVRWQWRVRWEVRCBCFGVRUHRVRUIUJUMZVRCBVRUKZWOVRULRBVDUNUOSACWE
    UPTVSWLWAADVSWLWECLEZWAVRVPWLXBQVQVRCWEXAWTUQSVSCBVSUKVPVQVRURZUSUTVAVBVCVE
    VSCVFGZVTFGZANVGVHEZGZWJWDQXDVSVIRZVRVPXEVQBVJSVQVPXGVRAVKUFCAVTVLTVSXDVRVO
    XFGZWKWHQXHXCVPVQXIVRVOVKVMCVOBVLTVN $.

  $( The digits of the rounded half of a nonnegative integer are the digits of
     the integer shifted by 1.  (Contributed by AV, 7-Jun-2010.) $)
  dignn0flhalf $p |- ( ( A e. ( ZZ>= ` 2 ) /\ I e. NN0 )
                       -> ( ( I + 1 ) ( digit ` 2 ) A )
                          = ( I ( digit ` 2 ) ( |_ ` ( A / 2 ) ) ) ) $=
    ( c2 cfv wcel cn0 c1 caddc co cdiv cfl wceq wi syl cmo 3ad2ant2 syl3anc cc0
    cr wbr cuz cdig wo eluzge2nn0 nn0eo w3a dignn0ehalf syl3an2 wa eluzelz nn0z
    cz zefldiv2 syl2anr eqcomd 3adant3 oveq2d eqtrd 3exp cexp cmin cn simp2 nno
    simp1 syl2anc simp3 dignn0flhalflem2 oveq1d cpnf 2nn a1i peano2nn0 3ad2ant3
    cico nn0rp0 nn0digval cle eluzelre rehalfcld clt nn0ge0d 2pos pm3.2i divge0
    2re syl21anc flge0nn0 3eqtr4d jaoi mpcom imp ) ACUADEZBFEZBGHIZACUBDZIZBACJ
    IZKDZWPIZLZWRFEZAGHICJIFEZUCZWMWNXAMZWMAFEZXDAUDZAUENXBWMXEMXCXBWMWNXAXBWMW
    NUFZWQBWRWPIZWTWMXBXFWNWQXILXGABUGUHXHWRWSBWPXBWMWRWSLWNXBWMUIWSWRWMAULEZWR
    ULEWSWRLXBCAUJZWRUKAUMUNUOUPUQURUSXCWMWNXAXCWMWNUFZACWOUTIJIKDZCOIZWSCBUTIJ
    IKDZCOIZWQWTXLXMXOCOXLXJAGVAICJIVBEZWNXMXOLWMXCXJWNXKPXLWMXCXQXCWMWNVCXCWMW
    NVEAVDVFXCWMWNVGZABVHQVIXLCVBEZWOFEZARVJVOIZEZWQXNLXSXLVKVLZWNXCXTWMBVMVNWM
    XCYBWNWMXFYBXGAVPNPCAWOVQQXLXSWNWSYAEZWTXPLYCXRXLWSFEZYDWMXCYEWNWMWRSERWRVR
    TZYEWMACAVSZVTWMASERAVRTCSEZRCWATZUIZYFYGWMAXGWBYJWMYHYIWFWCWDVLACWEWGWRWHV
    FPWSVPNCWSBVQQWIUSWJWKWL $.

  ${
    $d a i k x y $.
    $( Lemma for ~ nn0sumshdig (induction step, even multiplier).  (Contributed
       by AV, 3-Jun-2020.) $)
    nn0sumshdiglemA $p |- ( ( ( a e. NN /\ ( a / 2 ) e. NN ) /\ y e. NN )
                            -> ( A. x e. NN0 ( ( #b ` x ) = y
          -> x = sum_ k e. ( 0 ..^ y ) ( ( k ( digit ` 2 ) x ) x. ( 2 ^ k ) ) )
             -> ( ( #b ` a ) = ( y + 1 ) -> a = sum_ k e. ( 0 ..^ ( y + 1 ) )
                                ( ( k ( digit ` 2 ) a ) x. ( 2 ^ k ) ) ) ) ) $=
      ( vi wcel c2 co wa wceq cc0 cexp cmul csu wi cn0 c1 caddc adantl a1i cdiv
      cv cn cblen cfv cfzo cdig wral cmin nnnn0 blennn0em1 sylan2 fveqeq2 oveq2
      id oveq1d adantr sumeq2dv eqeq12d imbi12d rspcva simpr cc nncn pncan1 syl
      sylan9eq eqeq2d cfz nnz fzval3 eqcomd sumeq1d cuz elnn0uz sylib cpnf cico
      cz 2nn elfzelz nn0rp0 ad4antlr digvalnn0 syl3anc nn0cnd elfznn0 nn0expcld
      2nn0 mulcld oveq1 oveq12d 2cn exp0 oveq2i eqtrdi fsum1p 0dig2nn0e syl2anr
      ax-mp cr 1re mul02lem2 1z eqeltri 2cnd elfznn nnnn0d oveq1i eleq2s expcld
      0p1e1 fsumshftm ad4antr elfzonn0 dignn0ehalf expp1d elfzoelz 2re reexpcld
      recnd w3a mulass eqtrd 0cn fzoval oveq2d fzofi peano2zd peano2nn0 addlidd
      cfn fsumcl fsummulc1 3eqtr4d 3eqtrd weq cbvsumv ex com25 biimpac wne 2ne0
      divcan1d ad3antlr 3eqtrrd imim2i com13 com23 exp31 com14 expdcom mpid mpd
      sylbid impcom imp ) DUBZUCFZUURGUAHZUCFZIZBUBZUCFZAUBZUDUEUVCJZUVEKUVCUFH
      ZCUBZUVEGUGUEZHZGUVHLHZMHZCNZJZOZAPUHZUURUDUEZUVCQRHZJZUURKUVRUFHZUVHUURU
      VIHZUVKMHZCNZJZOZOZUVBUUTUDUEZUVQQUIHZJZUVDUWFOZUVAUUSUUTPFZUWIUUTUJZUURU
      KULUVAUUSUWIUWJOZUVAUUSUWKUWMUWLUWKUVAUUSUWMUWKUVPUWIUVDUVAUUSIZUWEUWKUVP
      UWIUVDUWNUWEOOOZUWKUVPIUWGUVCJZUUTUVGUVHUUTUVIHZUVKMHZCNZJZOZUWOUVOUXAAUU
      TPUVEUUTJZUVFUWPUVNUWTUVEUUTUVCUDUMUXBUVEUUTUVMUWSUXBUOUXBUVGUVLUWRCUXBUV
      LUWRJUVHUVGFUXBUVJUWQUVKMUVEUUTUVHUVIUNUPUQURUSUTVAUWNUWIUVDUXAUWEUWNUVSU
      VDUXAUWIUWDUWNUVSUVDUXAUWIUWDOOUWNUVSIZUVDIZUWIUXAUWDUXDUWIUWPUXAUWDOUXDU
      WHUVCUWGUXCUVDUWHUVRQUIHZUVCUXCUVQUVRQUIUWNUVSVBUPUVDUVCVCFUXEUVCJUVCVDUV
      CVEVFVGVHUXAUWPUXDUWDUWTUXDUWDOUWPUWTUXDUWDUWTUXDIZUWCUVGEUBZUUTUVIHZGUXG
      LHZMHZENZGMHZUUTGMHZUURUXDUWCUXLJUWTUXDUWCKUVCVIHZUWBCNKUURUVIHZQMHZKQRHZ
      UVCVIHZUWBCNZRHZUXLUXDUVTUXNUWBCUXDUXNUVTUXDUVCVSFZUXNUVTJUVDUYAUXCUVCVJZ
      SZKUVCVKVFVLVMUXDUWBUXPCKUVCUVDUVCKVNUEFZUXCUVDUVCPFUYDUVCUJUVCVOVPSUXDUV
      HUXNFZIZUWAUVKUYFUWAUYFGUCFZUVHVSFZUURKVQVRHZFZUWAPFZUYGUYFVTTUYEUYHUXDUV
      HKUVCWASUUSUYJUVAUVSUVDUYEUUSUURPFZUYJUURUJZUURWBVFZWCGUURUVHWDZWEWFUYEUV
      KVCFZUXDUYEUVKUYEGUVHGPFZUYEWITUVHUVCWGWHWFSWJUVHKJZUWBUXOGKLHZMHUXPUYRUW
      AUXOUVKUYSMUVHKUURUVIWKUVHKGLUNWLUYSQUXOMGVCFZUYSQJWMGWNWTWOWPWQUXDUXTKUX
      QQUIHZUVCQUIHZVIHZUXGQRHZUURUVIHZGVUDLHZMHZENZRHZUXLUXDUXPKUXSVUHRUXCUXPK
      JZUVDUWNVUJUVSUWNUXPKQMHZKUWNUXOKQMUUSUYLUWKUXOKJUVAUYMUWLUURWRWSUPQXAFVU
      KKJXBQXCWTWPUQUQUXDUWBVUGCEQUXQUVCQVSFUXDXDTUXQVSFUXDUXQQVSXLXDXETUYCUXDU
      VHUXRFZIZUWAUVKVUMUWAVUMUYGUYHUYJUYKUYGVUMVTTVULUYHUXDUVHUXQUVCWASUUSUYJU
      VAUVSUVDVULUYNWCUYOWEWFVULUYPUXDVULGUVHVULXFUVHPFUVHQUVCVIHZUXRUVHVUNFUVH
      UVHUVCXGXHUXQQUVCVIXLXIXJXKSWJUVHVUDJUWAVUEUVKVUFMUVHVUDUURUVIWKUVHVUDGLU
      NWLXMWLUXDUVGVUGENZUVGUXJGMHZENVUIUXLUXDUVGVUGVUPEUXDUXGUVGFZIZVUGUXHUXIG
      MHZMHZVUPVURVUEUXHVUFVUSMVURUWKUYLUXGPFZVUEUXHJUVAUWKUUSUVSUVDVUQUWLXNUUS
      UYLUVAUVSUVDVUQUYMWCVUQVVAUXDUXGUVCXOZSUURUXGXPWEVUQVUFVUSJUXDVUQGUXGVUQX
      FVVBXQSWLVURUXHVCFZUXIVCFZUYTVUTVUPJVURUXHVURUYGUXGVSFZUUTUYIFZUXHPFUYGVU
      RVTTZVUQVVEUXDUXGKUVCXRZSUVAVVFUUSUVSUVDVUQUVAUWKVVFUWLUUTWBVFXNGUUTUXGWD
      WEWFZVUQVVDUXDVUQUXIVUQGUXGGXAFVUQXSTVVBXTYASVURXFVVCVVDUYTYBVUPVUTUXHUXI
      GYCVLWEYDURUXDVUIKVUORHVUOUXDVUHVUOKRUXDVUCUVGVUGEUVDVUCUVGJUXCUVDVUCKVUB
      VIHZUVGUVDVUAKVUBVIVUAKJZUVDKVCFVVKYEKVEWTTUPUVDUYAVVJUVGJUYBUYAUVGVVJKUV
      CYFVLVFYDSVMYGUXDVUOUXDUVGVUGEUVGYLFUXDKUVCYHTZVURVUEVUFVURVUEVURUYGVUDVS
      FZUYJVUEPFVVGVUQVVMUXDVUQUXGVVHYISUUSUYJUVAUVSUVDVUQUYNWCGUURVUDWDWEWFVUQ
      VUFVCFUXDVUQVUFVUQGVUDUYQVUQWITZVUQVVAVUDPFVVBUXGYJVFWHWFSWJYMYKYDUXDUVGU
      XJGEVVLUXDXFVURUXHUXIVVIVUQVVDUXDVUQUXIVUQGUXGVVNVVBWHWFSWJYNYOYDYPSUXFUX
      KUUTGMUXFUUTUXKUXDUWTUUTUXKJUXDUWSUXKUUTUWSUXKJUXDUVGUWRUXJCECEYQUWQUXHUV
      KUXIMUVHUXGUUTUVIWKUVHUXGGLUNWLYRTVHUUAVLUPUXDUXMUURJZUWTUUSVVOUVAUVSUVDU
      USUURGUURVDUUSXFGKUUBUUSUUCTUUDUUESUUFYSUUGUUHUUOUUIUUJYTUUKVFYSYTUULUUMU
      UPUUNUUQ $.

    $( Lemma for ~ nn0sumshdig (induction step, odd multiplier).  (Contributed
       by AV, 7-Jun-2020.) $)
    nn0sumshdiglemB $p |- ( ( ( a e. NN /\ ( ( a - 1 ) / 2 ) e. NN0 )
                              /\ y e. NN ) -> ( A. x e. NN0 ( ( #b ` x ) = y
          -> x = sum_ k e. ( 0 ..^ y ) ( ( k ( digit ` 2 ) x ) x. ( 2 ^ k ) ) )
             -> ( ( #b ` a ) = ( y + 1 ) -> a = sum_ k e. ( 0 ..^ ( y + 1 ) )
                                ( ( k ( digit ` 2 ) a ) x. ( 2 ^ k ) ) ) ) ) $=
      ( vi wcel c1 co c2 cn0 wceq cc0 cmul csu wi caddc wa cc syl adantl cv cfv
      cn cmin cdiv cblen cfzo cdig cexp wral cuz wo elnn1uz2 1t1e1 eqcomi simpl
      csn oveq2 eqcoms fveq2 blen1 eqtrdi oveq2d fzo01 sylan9eqr sumeq1d oveq1d
      sumeq2sdv cvv c0ex ax-1cn mulcli oveq1 cpr 1ex prid2 0dig2pr01 ax-mp exp0
      2cn oveq12d sumsn mp2an adantr eqtrd 3eqtr4a ex a1d 2a1d eluzge2nn0 nn0ob
      wb bicomd blennngt2o2 sylbid fveqeq2 id eqeq12d imbi12d rspcva eqeq1 nncn
      imp ad2antll blennn0elnn nncnd ad2antrl 1cnd addcan2d eqcom cfz cz fzval3
      nnz eqcomd nnnn0 elnn0uz sylib cpnf cico 2nn a1i elfzelz nn0rp0 digvalnn0
      syl3anc nn0cnd 2nn0 elfznn0 nn0expcld mulcld oveq2i fsum1p 1z 2cnd oveq1i
      0p1e1 eleq2s jca com23 biimparc 0dig2nn0o syl2anc elfznn nnnn0d fsumshftm
      eqeltri expcld 3eqtrd elfzoelz elfzonn0 sumeq2dv 0cn pncan1 fzoval eqtr4d
      mulassd cfl simprlr dignn0flhalf syl2an eluzelz nn0z zob imbitrrid ancoms
      zofldiv2 expp1d sumeq12dv weq cbvsumv eqeq2i birani cfn fsummulc1 3eqtr4d
      fzofi wne w3a eluzelcn peano2cnm 2ne0 divcan1 pncan3 3eqtrrd imim2i com13
      3jca biimtrid com14 exp4c com35 pm2.43a com25 impcom mpd jaoi sylbi imp31
      ) DUAZUCFZUWTGUDHZIUEHZJFZBUAZUCFZAUAZUFUBUXEKZUXGLUXEUGHZCUAZUXGIUHUBZHZ
      IUXJUIHZMHZCNZKZOZAJUJZUWTUFUBZUXEGPHZKZUWTLUXTUGHZUXJUWTUXKHZUXMMHZCNZKZ
      OZOZUXAUWTGKZUWTIUKUBFZULUXDUXFUYHOZOZUWTUMUYIUYLUYJUYIUYHUXDUXFUYIUYGUXR
      UYIUYAUYFUYIUYAQZGGGMHZUWTUYEUYNGUNUOUYIUYAUPUYMUYELUQZUYDCNZUYNUYMUYBUYO
      UYDCUYAUYIUYBLUXSUGHZUYOUYBUYQKUXTUXSUXTUXSLUGURUSUYIUYQLGUGHUYOUYIUXSGLU
      GUYIUXSGUFUBGUWTGUFUTVAVBVCVDVBVEVFUYIUYPUYNKUYAUYIUYPUYOUXJGUXKHZUXMMHZC
      NZUYNUYIUYOUYDUYSCUYIUYCUYRUXMMUWTGUXJUXKURVGVHLVIFUYNRFUYTUYNKVJGGVKVKVL
      UYSUYNCLVIUXJLKZUYRGUXMGMVUAUYRLGUXKHZGUXJLGUXKVMGLGVNFVUBGKLGVOVPGVQVRVB
      VUAUXMILUIHZGUXJLIUIURZIRFZVUCGKVTIVSVRZVBWAWBWCVBWDWEWFWGWHWIUYJUXDUYKUY
      JUXDQZUXSUXCUFUBZGPHZKZUYKUYJUXDVUJUYJUXDUWTGPHIUEHZJFZVUJUYJUWTJFZUXDVUL
      WLUWTWJZVUMVULUXDUWTWKZWMSUYJVULVUJUWTWNWGWOXCUXDUYJVUJUYKOUXDUXRVUJUXFUY
      JUYGUXRUXDVUJUXFUYJUYGOOOZUXDUXRUXDVUPOZUXDUXRQVUHUXEKZUXCUXIUXJUXCUXKHZU
      XMMHZCNZKZOZVUQUXQVVCAUXCJUXGUXCKZUXHVURUXPVVBUXGUXCUXEUFWPVVDUXGUXCUXOVV
      AVVDWQVVDUXIUXNVUTCVVDUXLVUSUXMMUXGUXCUXJUXKURVGVHWRWSWTVVCUXDUYJUXFVUJUY
      GVVCUXDUYJUXFVUJUYGOUYAUXDUYJQZUXFQZVUJVVCUYFUYAVUJVVFVVCUYFOZUYAVUJUXTVU
      IKZVVFVVGOUXSUXTVUIXAUYAVVFVVHVVGUYAVVFVVHVVGOUYAVVFQZVVHUXEVUHKZVVGVVIUX
      EVUHGUXFUXERFUYAVVEUXEXBXDVVEVUHRFZUYAUXFUXDVVKUYJUXDVUHUXCXEXFWDXGVVIXHX
      IVVJVURVVIVVGUXEVUHXJVVCVURVVIUYFVVBVVIUYFOVURVVBVVIUYFVVBVVIQZUYEGLGPHZG
      UDHZUXEGUDHZXKHZEUAZGPHZUWTUXKHZIVVRUIHZMHZENZPHZGUXCIMHZPHZUWTVVIUYEVWCK
      VVBVVIUYELUXEXKHZUYDCNLUWTUXKHZGMHZVVMUXEXKHZUYDCNZPHVWCVVIUYBVWFUYDCVVIV
      WFUYBVVIUXEXLFZVWFUYBKUXFVWKUYAVVEUXEXNZXDZLUXEXMSXOVFVVIUYDVWHCLUXEUXFUX
      ELUKUBFZUYAVVEUXFUXEJFVWNUXEXPUXEXQXRXDVVIUXJVWFFZQZUYCUXMVWPUYCVVIVWOUYC
      JFZVVEVWOVWQOUYAUXFVVEVWOVWQVVEVWOQZIUCFZUXJXLFZUWTLXSXTHZFZVWQVWSVWRYAYB
      VWOVWTVVEUXJLUXEYCTVVEVXBVWOUYJVXBUXDUYJVUMVXBVUNUWTYDZSTWDIUWTUXJYEZYFWG
      XGXCYGVWOUXMRFZVVIVWOUXMVWOIUXJIJFZVWOYHYBUXJUXEYIYJYGTYKVUAUYDVWGVUCMHVW
      HVUAUYCVWGUXMVUCMUXJLUWTUXKVMVUDWAVUCGVWGMVUFYLVBYMVVIVWHGVWJVWBPVVIVWHUY
      NGVVIVWGGGMVVEVWGGKZUYAUXFVVEVUMVULVXGUYJVUMUXDVUNTUYJVULUXDUYJVUMVULUXDW
      LVUNVUOSUUAUWTUUBUUCXGVGUNVBVVIUYDVWACEGVVMUXEGXLFVVIYNYBVVMXLFVVIVVMGXLY
      QYNUUGYBVWMVVIUXJVWIFZQZUYCUXMVXIUYCVVIVXHVWQVVEVXHVWQOZUYAUXFUYJVXJUXDUY
      JVXHVWQUYJVXHQZVWSVWTVXBVWQVWSVXKYAYBVXHVWTUYJUXJVVMUXEYCTVXKVUMVXBUYJVUM
      VXHVUNWDVXCSVXDYFWGTXGXCYGVXHVXEVVIVXHIUXJVXHYOUXJJFUXJGUXEXKHZVWIUXJVXLF
      UXJUXJUXEUUDUUEVVMGUXEXKYQYPYRUUHTYKUXJVVRKUYCVVSUXMVVTMUXJVVRUWTUXKVMUXJ
      VVRIUIURWAUUFWAUUITVVLVWBVWDGPVVLUXIVVQUXCUXKHZIVVQUIHZIMHZMHZENZUXIVXMVX
      NMHZIMHZENZVWBVWDVVIVXQVXTKVVBVVIUXIVXPVXSEVVIVVQUXIFZQZVXSVXPVYBVXMVXNIV
      VIVYAVXMRFZVVEVYAVYCOUYAUXFVVEVYAVYCVVEVYAQZVXMVYDVWSVVQXLFZUXCVXAFZVXMJF
      VWSVYDYAYBVYAVYEVVEVVQLUXEUUJTVVEVYFVYAUXDVYFUYJUXCYDWDWDIUXCVVQYEYFYGZWG
      XGXCVYAVXNRFZVVIVYAVXNVYAIVVQVXFVYAYHYBVVQUXEUUKYJYGZTVYBYOUUQXOUULTVVIVW
      BVXQKVVBVVIVVPUXIVWAVXPEUXFVVPUXIKUYAVVEUXFVVPLVVOXKHZUXIUXFVVNLVVOXKVVNL
      KZUXFLRFVYKUUMLUUNVRZYBVGUXFVWKUXIVYJKVWLLUXEUUOSUUPXDVVIVVQVVPFZQZVVSVXM
      VVTVXOMVYNVVSVVQUWTIUEHUURUBZUXKHZVXMVVIUYJVVQJFZVVSVYPKVYMUYAUXDUYJUXFUU
      SVYQVVQVYJVVPVVQVVOYIVVNLVVOXKVYLYPYRZUWTVVQUUTUVAVYNVYOUXCVVQUXKVYNUWTXL
      FZVUKXLFZQZVYOUXCKVVIWUAVYMVVEWUAUYAUXFUYJUXDWUAVUGVYSVYTUYJVYSUXDIUWTUVB
      ZWDUYJUXDVYTUXDVYTUYJUXCXLFZUXCUVCUYJVYSVYTWUCWLWUBUWTUVDSUVEXCYSUVFXGWDU
      WTUVGSVCWEVYMVVTVXOKVVIVYMIVVQVYMYOVYRUVHTWAUVITVVLVWDUXIVXRENZIMHVXTVVLU
      XCWUDIMVVBUXCWUDKVVIVVAWUDUXCUXIVUTVXRCECEUVJVUSVXMUXMVXNMUXJVVQUXCUXKVMU
      XJVVQIUIURWAUVKUVLUVMVGVVLUXIVXRIEUXIUVNFVVLLUXEUVQYBVVLYOVVLVYAVXRRFZVVF
      VYAWUEOZVVBUYAVVEWUFUXFVVEVYAWUEVYDVXMVXNVYGVYAVYHVVEVYITYKWGWDXDXCUVOWEU
      VPVCVVFVWEUWTKZVVBUYAVVEWUGUXFVVEVWEGUXBPHZUWTVVEVWDUXBGPVVEUXBRFZVUEILUV
      RZUVSZVWDUXBKUYJWUKUXDUYJWUIVUEWUJUYJUWTRFZWUIIUWTUVTZUWTUWASUYJYOWUJUYJU
      WBYBUWHTUXBIUWCSVCVVEGRFZWULQZWUHUWTKUYJWUOUXDUYJWUNWULUYJXHWUMYSTGUWTUWD
      SWEWDXDUWEWGUWFUWGUWIWOWGYTWOYTUWJUWKUWLSWGUWMUWNUWOUWPWGUWQUWRUWS $.

    $( Lemma 1 for ~ nn0sumshdig (induction step).  (Contributed by AV,
       7-Jun-2020.) $)
    nn0sumshdiglem1 $p |- ( y e. NN
                    -> ( A. a e. NN0 ( ( #b ` a ) = y
                         -> a = sum_ k e. ( 0 ..^ y )
                             ( ( k ( digit ` 2 ) a ) x. ( 2 ^ k ) ) )
                      -> A. a e. NN0 ( ( #b ` a ) = ( y + 1 )
                         -> a = sum_ k e. ( 0 ..^ ( y + 1 ) )
                                ( ( k ( digit ` 2 ) a ) x. ( 2 ^ k ) ) ) ) ) $=
      ( vx cv cblen cfv wceq cc0 cfzo co c2 cmul csu wi cn0 cn wcel c1 eqtrdi
      cdig cexp wral caddc weq fveqeq2 id oveq2 oveq1d eqeq12d imbi12d cbvralvw
      sumeq2sdv wa wo elnn0 cdiv nn0sumshdiglemA nn0sumshdiglemB nneom mpjaodan
      cmin expimpd wb eqcom a1i nncn 1cnd addlsub 1m1e0 eqeq2d 3bitrd csn oveq1
      oveq2d 0p1e1 oveq2i fzo01 eqtri sumeq1d cc 0cn cz 2nn dig0 mp2an 2cn exp0
      0z ax-mp oveq12d 1re mul02lem2 sumsn eqtr2di biimtrdi adantl fveq2 eqeq1d
      cr blen0 adantr mpbird a1d jaoi sylbi com12 ralrimiv ex biimtrid ) CEZFGZ
      AEZHZXKIXMJKZBEZXKLUAGZKZLXPUBKZMKZBNZHZOZCPUCDEZFGXMHZYDXOXPYDXQKZXSMKZB
      NZHZOZDPUCZXMQRZXLXMSUDKZHZXKIYMJKZXTBNZHZOZCPUCZYCYJCDPCDUEZXNYEYBYIXKYD
      XMFUFYTXKYDYAYHYTUGYTXOXTYGBYTXRYFXSMXKYDXPXQUHUIUMUJUKULYLYKYSYLYKUNZYRC
      PXKPRZUUAYRUUBXKQRZXKIHZUOUUAYROZXKUPUUCUUEUUDUUCXKLUQKQRZUUEXKSVBKLUQKPR
      ZUUCUUFUNYLYKYRDABCURVCUUCUUGUNYLYKYRDABCUSVCXKUTVAUUDYLYKYRUUDYLUNZYRYKU
      UHYRSYMHZIYOXPIXQKZXSMKZBNZHZOZYLUUNUUDYLUUIXMIHZUUMYLUUIYMSHZXMSSVBKZHUU
      OUUIUUPVDYLSYMVEVFYLXMSSXMVGYLVHZUURVIYLUUQIXMUUQIHYLVJVFVKVLUUOUULIVMZUU
      KBNZIUUOYOUUSUUKBUUOYOIISUDKZJKZUUSUUOYMUVAIJXMISUDVNVOUVBISJKUUSUVASIJVP
      VQVRVSTVTIWARZUVCUUTIHWBWBUUKIBIWAXPIHZUUKISMKZIUVDUUJIXSSMUVDUUJIIXQKZIX
      PIIXQVNLQRIWCRUVFIHWDWILIWEWFTUVDXSLIUBKZSXPILUBUHLWARUVGSHWGLWHWJTWKSWTR
      UVEIHWLSWMWJTWNWFWOWPWQUUDYRUUNVDYLUUDYNUUIYQUUMUUDXLSYMUUDXLIFGSXKIFWRXA
      TWSUUDXKIYPUULUUDUGUUDYOXTUUKBUUDXRUUJXSMXKIXPXQUHUIUMUJUKXBXCXDVCXEXFXGX
      HXIXJ $.

    $d L a k x y $.
    $( Lemma 2 for ~ nn0sumshdig .  (Contributed by AV, 7-Jun-2020.) $)
    nn0sumshdiglem2 $p |- ( L e. NN -> A. a e. NN0 ( ( #b ` a ) = L
                           -> a = sum_ k e. ( 0 ..^ L )
                                  ( ( k ( digit ` 2 ) a ) x. ( 2 ^ k ) ) ) ) $=
      ( vy cv wceq cc0 cfzo co c2 csu wi cn0 wral c1 eqeq2 oveq2 sumeq1d wcel
      cc cblen cfv cdig cexp cmul csn caddc fzo01 eqtrdi eqeq2d imbi12d ralbidv
      vx weq wa 0cnd cpnf cico 2nn a1i 0zd nn0rp0 digvalnn0 syl3anc nn0cnd 1cnd
      cn cz mulcld jca adantr oveq1 2cn exp0 ax-mp oveq12d sumsn syl mulridd wo
      cpr blen1b biimpa vex elpr sylibr 0dig2pr01 3eqtrrd nn0sumshdiglem1 nnind
      ex rgen ) CEZUAUBZUMEZFZWMGWOHIZAEZWMJUCUBZIZJWRUDIZUEIZAKZFZLZCMNWNOFZWM
      GUFZXBAKZFZLZCMNWNDEZFZWMGXKHIZXBAKZFZLZCMNWNXKOUGIZFZWMGXQHIZXBAKZFZLZCM
      NWNBFZWMGBHIZXBAKZFZLZCMNUMDBWOOFZXEXJCMYHWPXFXDXIWOOWNPYHXCXHWMYHWQXGXBA
      YHWQGOHIXGWOOGHQUHUIRUJUKULUMDUNZXEXPCMYIWPXLXDXOWOXKWNPYIXCXNWMYIWQXMXBA
      WOXKGHQRUJUKULWOXQFZXEYBCMYJWPXRXDYAWOXQWNPYJXCXTWMYJWQXSXBAWOXQGHQRUJUKU
      LWOBFZXEYGCMYKWPYCXDYFWOBWNPYKXCYEWMYKWQYDXBAWOBGHQRUJUKULXJCMWMMSZXFXIYL
      XFUOZXHGWMWSIZOUEIZYNWMYMGTSZYOTSZUOZXHYOFYLYRXFYLYPYQYLUPYLYNOYLYNYLJVGS
      ZGVHSWMGUQURISYNMSYSYLUSUTYLVAWMVBJWMGVCVDVEZYLVFVIVJVKXBYOAGTWRGFZWTYNXA
      OUEWRGWMWSVLUUAXAJGUDIZOWRGJUDQJTSUUBOFVMJVNVOUIVPVQVRYMYNYLYNTSXFYTVKVSY
      MWMGOWASZYNWMFYMWMGFWMOFVTZUUCYLXFUUDWMWBWCWMGOCWDWEWFWMWGVRWHWKWLDACWIWJ
      $.

    $d A a k $.
    $( A nonnegative integer can be represented as sum of its shifted bits.
       (Contributed by AV, 7-Jun-2020.) $)
    nn0sumshdig $p |- ( A e. NN0 -> A = sum_ k e. ( 0 ..^ ( #b ` A ) )
                                    ( ( k ( digit ` 2 ) A ) x. ( 2 ^ k ) ) ) $=
      ( va cn0 wcel cblen cfv cn cc0 cfzo co cv cdig cexp cmul wceq blennn0elnn
      c2 csu wi wral nn0sumshdiglem2 wa fveqeq2 id oveq2 oveq1d adantr sumeq2dv
      eqid eqeq12d imbi12d rspcva mpi ex syl5 mpd ) ADEZAFGZHEZAIUSJKZBLZARMGZK
      ZRVBNKZOKZBSZPZAQUTCLZFGUSPZVIVAVBVIVCKZVEOKZBSZPZTZCDUAZURVHBUSCUBURVPVH
      URVPUCUSUSPZVHUSUJVOVQVHTCADVIAPZVJVQVNVHVIAUSFUDVRVIAVMVGVRUEVRVAVLVFBVR
      VLVFPVBVAEVRVKVDVEOVIAVBVCUFUGUHUIUKULUMUNUOUPUQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Algorithms for the multiplication of nonnegative integers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A k $.  $d B k $.
    $( Trivial algorithm to calculate the product of two nonnegative integers
       ` a ` and ` b ` by adding ` b ` to itself ` a ` times.  (Contributed by
       AV, 17-May-2020.) $)
    nn0mulfsum $p |- ( ( A e. NN0 /\ B e. NN0 )
                       -> ( A x. B ) = sum_ k e. ( 1 ... A ) B ) $=
      ( cn0 wcel wa c1 cfz co csu chash cfv cmul cfn wceq fzfid nn0cn fsumconst
      cc syl2an hashfz1 adantr oveq1d eqtr2d ) ADEZBDEZFZGAHIZBCJZUHKLZBMIZABMI
      UEUHNEBSEUIUKOUFUEGAPBQUHBCRTUGUJABMUEUJAOUFAUAUBUCUD $.

    $( Standard algorithm (also known as "long multiplication" or "grade-school
       multiplication") to calculate the product of two nonnegative integers
       ` a ` and ` b ` by multiplying the multiplicand ` b ` by each digit of
       the multiplier ` a ` and then add up all the properly shifted results.
       Here, the binary representation of the multiplier ` a ` is used, i.e.,
       the above mentioned "digits" are 0 or 1.  This is a similar result as
       provided by ~ smumul .  (Contributed by AV, 7-Jun-2020.) $)
    nn0mullong $p |- ( ( A e. NN0 /\ B e. NN0 )
           -> ( A x. B ) = sum_ k e. ( 0 ..^ ( #b ` A ) )
                           ( ( ( k ( digit ` 2 ) A ) x. ( 2 ^ k ) ) x. B ) ) $=
      ( cn0 wcel wa cmul co cc0 cblen cfv cv c2 csu adantr a1i cc adantl nn0cnd
      cfzo cdig cexp wceq nn0sumshdig oveq1d cfn fzofi nn0cn cpnf cico elfzoelz
      cn 2nn nn0rp0 digvalnn0 syl3anc elfzonn0 nn0expcld mulcld fsummulc1 eqtrd
      cz 2nn0 ) ADEZBDEZFZABGHIAJKZTHZCLZAMUAKHZMVIUBHZGHZCNZBGHVHVLBGHCNVFAVMB
      GVDAVMUCVEACUDOUEVFVHVLBCVHUFEVFIVGUGPVEBQEVDBUHRVFVIVHEZFZVJVKVOVJVOMULE
      ZVIVBEZAIUIUJHEZVJDEVPVOUMPVNVQVFVIIVGUKRVFVRVNVDVRVEAUNOOMAVIUOUPSVNVKQE
      VFVNVKVNMVIMDEVNVCPVIVGUQURSRUSUTVA $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  N-ary functions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  According to Wikipedia ("Arity", ~ https://en.wikipedia.org/wiki/Arity ,
  19-May-2024): "In logic, mathematics, and computer science, _arity_ is the
  number of arguments or operands taken by a function, operation or relation."

  N-ary functions are often also called multivariate functions, without
  indicating the actual number of arguments. See also Wikipedia
  ("Multivariate functions", 19-May-2024,
  ~ https://en.wikipedia.org/wiki/Function_(mathematics)#Multivariate_functions
  ): "A _multivariate function_, multivariable function, or function of several
  variables is a function that depends on several arguments.  ...  Formally, a
  function of n variables is a function whose domain is a set of n-tuples.
  For example, multiplication of integers is a function of two variables, or
  _bivariate function_, whose domain is the set of all ordered pairs (2-tuples)
  of integers, and whose codomain is the set of integers.  The same is true for
  every binary operation.  Commonly, an n-tuple is denoted enclosed between
  parentheses, such as in ( 1 , 2 , ... , n ).  When using functional notation,
  one usually omits the parentheses surrounding tuples, writing
  f ( x_1 , ... , x_n ) instead of f ( ( x_1 , ... , x_n ) ).  Given n sets
  X_1 , ... , X_n , the set of all n-tuples ( x_1 , ... , x_n ) such that
  x_1 is an element of X_1 , ... , x_n is an element of X_n is called the
  Cartesian product of X_1 , ... , X_n , and denoted X_1 X ... X X_n .
  Therefore, a multivariate function is a function that has a Cartesian product
  or a proper subset of a Cartesian product as a domain: ` f : U --> Y ` where
  where the domain ` U ` has the form
  ` U C_ ( ( ... ( ( X `` 1 ) X. ( X `` 2 ) ) X. ... ) X. ( X `` n ) ) `."

  In the following, n-ary functions are defined as mappings (see ~ df-map )
  from a finite sequence of arguments, which themselves are defined as
  mappings from the half-open range of nonnegative integers to the domain of
  each argument.  Furthermore, the definition is restricted to endofunctions,
  meaning that the domain(s) of the argument(s) is identical with its codomain.
  This means that the domains of all arguments are identical (in contrast to
  the definition in Wikipedia, see above: here, we have
  X_1 = X_2 = ... = X_n = X).

  For small n, n-ary functions correspond to "usual" functions with a different
  number of arguments:

  - n = 0 (nullary functions): These correspond actually to constants,
  see ~ 0aryfvalelfv and ~ mapsn : ` ( X ^m { (/) } ) `

  - n = 1 (unary functions): These correspond actually to usual endofunctions,
  see ~ 1aryenef and ~ efmndbas : ` ( X ^m X ) `

  - n = 2 (binary functions): These correspond to usual operations on two
  elements of the same set, also called "binary operation" (according to
  Wikipedia ("Binary operation", 19-May-2024,
  ~ https://en.wikipedia.org/wiki/Binary_operation ): "In mathematics, a binary
  operation or dyadic operation is a rule for combining two elements (called
  operands) to produce another element.  More formally, a binary operation is
  an operation of arity two.  More specifically, a binary operation on a set is
  a binary operation whose two domains and the codomain are the same set."
  Sometimes also called "closed internal binary operation"), see ~ 2aryenef and
  compare with ~ df-clintop : ` ( X ^m ( X X. X ) ) `.

  Instead of using indexed arguments (represented by a mapping as described
  above), elements of Cartesian exponentiations ` ( U ^^ N ) ` (see
  ~ df-finxp ) could have been used to represent multiple arguments.  However,
  this concept is not fully developed yet (it is within a mathbox), and it is
  currently based on ordinal numbers, e.g., ` ( U ^^ 2o ) `, instead of
  integers, e.g., ` ( U ^^ 2 ) `, which is not very practical.

  The definition df-ixp of infinite Cartesian product could also have been used
  to represent multiple arguments, but this would have been more cumbersome
  without any additional advantage. ~ naryfvalixp shows that both definitions
  are equivalent.

$)

  $c -aryF $.  $( Constant symbol for the n-ary functions. $)

  $( Extend the definition of a class to include the n-ary functions. $)
  cnaryf $a class -aryF $.

  ${
    $d n x $.
    $( Define the n-ary (endo)functions.  (Contributed by AV, 11-May-2024.)
       (Revised by TA and SN, 7-Jun-2024.) $)
    df-naryf $a |- -aryF = ( n e. NN0 , x e. _V
                             |-> ( x ^m ( x ^m ( 0 ..^ n ) ) ) ) $.
  $}

  ${
    $d I n x $.  $d N n x $.  $d X n x $.  $d f x y $.
    naryfval.i $e |- I = ( 0 ..^ N ) $.
    $( The set of the n-ary (endo)functions on a class ` X ` .  (Contributed by
       AV, 13-May-2024.) $)
    naryfval $p |- ( N e. NN0 -> ( N -aryF X ) = ( X ^m ( X ^m I ) ) ) $=
      ( vn vx vy vf cn0 wcel cvv cnaryf co cmap wceq cv cc0 cfzo wa c0 df-naryf
      simpr oveq2 eqtr4di adantr oveq12d ovex ovmpoa ex mpondm0 nsyl5 simpl cab
      wn wf df-map eqtr4d pm2.61d1 ) BIJZCKJZBCLMZCCANMZNMZOZUSUTVDEFBCIKFPZVEQ
      EPZRMZNMZNMVCLVFBOZVECOZSZVECVHVBNVIVJUBZVKVECVGANVLVIVGAOVJVIVGQBRMAVFBQ
      RUCDUDUEUFUFFEUACVBNUGUHUIUTUNVATVCUSUTSUTVATOUSUTUBFEVFVFQVERMNMNMLBCIKE
      FUAUJUKUTVBKJZSUTVCTOUTVMULFGGPVEHPUOHUMNCVBKKFGHUPUJUKUQUR $.

    $( The set of the n-ary (endo)functions on a class ` X ` expressed with the
       notation of infinite Cartesian products.  (Contributed by AV,
       19-May-2024.) $)
    naryfvalixp $p |- ( N e. NN0 -> ( N -aryF X ) = ( X ^m X_ x e. I X ) ) $=
      ( vn cn0 wcel cvv cnaryf co cixp cmap wceq wa cc0 cfzo eqtr4d c0 cv ovexi
      naryfval adantr ixpconstg sylan oveq2d ex wn simpr df-naryf mpondm0 nsyl5
      a1i reldmmap ovprc1 pm2.61d1 ) CGHZDIHZCDJKZDABDLZMKZNZUQURVBUQUROZUSDDBM
      KZMKZVAUQUSVENURBCDEUBUCVCUTVDDMUQBIHZURUTVDNVFUQBPCQEUAUMABDIIUDUEUFRUGU
      RUHUSSVAVCURUSSNUQURUIAFFTZVGPATQKMKMKJCDGIFAUJUKULDUTMUNUORUP $.

    $( An n-ary (endo)function on a set ` X ` .  (Contributed by AV,
       14-May-2024.) $)
    naryfvalel $p |- ( ( N e. NN0 /\ X e. V )
                       -> ( F e. ( N -aryF X ) <-> F : ( X ^m I ) --> X ) ) $=
      ( cn0 wcel cnaryf co cmap wf naryfval eleq2d cvv wb elmapg mpan2 sylan9bb
      ovex ) CGHZACEIJZHAEEBKJZKJZHZEDHZUCEALZUAUBUDABCEFMNUFUCOHUEUGPEBKTEUCAD
      OQRS $.

    $( Reverse closure for n-ary (endo)functions.  (Contributed by AV,
       14-May-2024.) $)
    naryrcl $p |- ( F e. ( N -aryF X ) -> ( N e. NN0 /\ X e. _V ) ) $=
      ( vx vn cn0 cvv cv cc0 cfzo co cmap cnaryf df-naryf elmpocl ) FGHIGJZRKFJ
      LMNMNMCDOAGFPQ $.

    $( The value of an n-ary (endo)function on a set ` X ` is an element of
       ` X ` .  (Contributed by AV, 14-May-2024.) $)
    naryfvalelfv $p |- ( ( F e. ( N -aryF X ) /\ A : I --> X )
                         -> ( F ` A ) e. X ) $=
      ( cnaryf co wcel wf wa cmap cn0 cvv naryrcl naryfvalel biimpd mpcom simpr
      adantr cc0 cfzo ovexi a1i elmapd biimpar sylan ffvelcdmd ) BDEGHIZCEAJZKE
      CLHZEABUIUKEBJZUJDMIZENIZKZUIULBCDEFOZUOUIULBCDNEFPQRTUIUOUJAUKIZUPUOUQUJ
      UOECANNUMUNSCNIUOCUADUBFUCUDUEUFUGUH $.
  $}

  ${
    $d N w $.  $d V w $.  $d X w $.
    $( An n-ary (endo)function on a set ` X ` expressed as a function over the
       set of words on ` X ` of length ` n ` .  (Contributed by AV,
       4-Jun-2024.) $)
    naryfvalelwrdf $p |- ( ( N e. NN0 /\ X e. V ) -> ( F e. ( N -aryF X )
                           <-> F : { w e. Word X | ( # ` w ) = N } --> X ) ) $=
      ( cn0 wcel wa cnaryf co cc0 cfzo cmap wf cv chash cfv wceq cword crab
      eqid naryfvalel wrdnval ancoms feq2d bitr4d ) CFGZEDGZHZBCEIJGEKCLJZMJZEB
      NAOPQCRAESTZEBNBUJCDEUJUAUBUIULUKEBUHUGULUKRACEDUCUDUEUF $.
  $}

  ${
    $d F x $.  $d V x $.  $d X x $.
    $( A nullary (endo)function on a set ` X ` is a singleton of an ordered
       pair with the empty set as first component.  A nullary function
       represents a constant: ` ( F `` (/) ) = C ` with ` C e. X ` , see also
       ~ 0aryfvalelfv .  Instead of ` ( F `` (/) ) ` , nullary functions are
       usually written as ` F ( ) ` in literature.  (Contributed by AV,
       15-May-2024.) $)
    0aryfvalel $p |- ( X e. V -> ( F e. ( 0 -aryF X )
                                   <-> E. x e. X F = { <. (/) , x >. } ) ) $=
      ( wcel cc0 cnaryf co c0 cmap wf csn cv cop wceq wrex wb 0ex cvv a1i feq2d
      cn0 0nn0 cfzo fzo0 eqcomi naryfvalel mpan mapdm0 cfv opeq2 sneqd rspceeqv
      wa fsn2 sylbi id fsnd feq1 syl5ibrcom rexlimiv impbii 3bitrd ) DCEZBFDGHE
      ZDIJHZDBKZILZDBKZBIAMZNZLZOZADPZFUBEVDVEVGQUCBIFCDFFUDHIFUEUFUGUHVDVFVHDB
      DCUIUAVIVNQVDVIVNVIIBUJZDEBIVONZLZOUNVNIDBRUOAVODVLVQBVJVOOVKVPVJVOIUKULU
      MUPVMVIADVJDEZVIVMVHDVLKVRIVJSDISEVRRTVRUQURVHDBVLUSUTVAVBTVC $.

    $( The value of a nullary (endo)function on a set ` X ` .  (Contributed by
       AV, 19-May-2024.) $)
    0aryfvalelfv $p |- ( F e. ( 0 -aryF X ) -> E. x e. X ( F ` (/) ) = x ) $=
      ( cc0 cn0 wcel cvv wa cnaryf co c0 cfv cv wceq wrex cfzo eqid naryrcl cop
      wi csn 0aryfvalel 0ex fvsng mpan fveq1 eqeq1d syl5ibrcom reximia biimtrdi
      adantl mpcom ) DEFZCGFZHBDCIJFZKBLZAMZNZACOZBDDPJZDCUTQRUNUOUSTUMUNUOBKUQ
      SUAZNZACOUSABGCUBVBURACUQCFZURVBKVALZUQNZKGFVCVEUCKUQGCUDUEVBUPVDUQKBVAUF
      UGUHUIUJUKUL $.
  $}

  $( A unary (endo)function on a set ` X ` .  (Contributed by AV,
     15-May-2024.) $)
  1aryfvalel $p |- ( X e. V -> ( F e. ( 1 -aryF X )
                                 <-> F : ( X ^m { 0 } ) --> X ) ) $=
    ( c1 cn0 wcel cnaryf co cc0 csn cmap wf wb 1nn0 cfzo eqcomi naryfvalel mpan
    fzo01 ) DEFCBFADCGHFCIJZKHCALMNATDBCIDOHTSPQR $.

  $( Closure of a unary (endo)function.  (Contributed by AV, 18-May-2024.) $)
  fv1arycl $p |- ( ( G e. ( 1 -aryF X ) /\ A e. X )
                   -> ( G ` { <. 0 , A >. } ) e. X ) $=
    ( c1 cnaryf co wcel cc0 cop csn cfv cn0 cvv wa wi cfzo eqid naryrcl wf a1i
    cmap 1aryfvalel w3a simp2 c0ex simp3 fsnd snex elmapd mpbird ffvelcdmd 3exp
    simp1 sylbid adantl mpcom imp ) BDCEFGZACGZHAIJZBKCGZDLGZCMGZNURUSVAOZBHDPF
    ZDCVEQRVCURVDOVBVCURCHJZUAFZCBSZVDBMCUBVCVHUSVAVCVHUSUCZVGCUTBVCVHUSUDVIUTV
    GGVFCUTSVIHAMCHMGVIUETVCVHUSUFUGVICVFUTMMVCVHUSUMVFMGVIHUHTUIUJUKULUNUOUPUQ
    $.

  ${
    $d A x $.  $d V x $.  $d X x $.
    1arympt1.f $e |- F = ( x e. ( X ^m { 0 } ) |-> ( A ` ( x ` 0 ) ) ) $.
    $( A unary (endo)function in maps-to notation.  (Contributed by AV,
       16-May-2024.) $)
    1arympt1 $p |- ( ( X e. V /\ A : X --> X ) -> F e. ( 1 -aryF X ) ) $=
      ( wcel wf c1 cnaryf co cc0 csn cmap cv cfv eqid id c0ex snid a1i ffvelcdm
      mapfvd sylan2 fmptd 1aryfvalel imbitrrid imp ) EDGZEEBHZCIEJKGZUJUKUIELMZ
      NKZECHUJAUMLAOZPZBPZECUNUMGZUJUOEGUPEGUQEULUNUMLUMQUQRLULGUQLSTUAUCEEUOBU
      BUDFUECDEUFUGUH $.

    $d B x $.
    $( The value of a unary (endo)function in maps-to notation.  (Contributed
       by AV, 16-May-2024.) $)
    1arympt1fv $p |- ( ( X e. V /\ B e. X )
                       -> ( F ` { <. 0 , B >. } ) = ( A ` B ) ) $=
      ( wcel wa cc0 cop csn cv cfv cmap co cvv wceq a1i c0ex cmpt adantl anim1i
      fveq1 adantr fvsng syl eqtrd fveq2d wf simpr fsnd wb elmapg sylan2 mpbird
      snex fvexd fvmptd ) FEHZCFHZIZAJCKLZJAMZNZBNZCBNFJLZOPZDQDAVHVFUARVBGSVBV
      DVCRZIZVECBVJVEJVCNZCVIVEVKRVBJVDVCUDUBVJJQHZVAIZVKCRVBVMVIUTVLVAVLUTTSUC
      UEJCQFUFUGUHUIVBVCVHHZVGFVCUJZVBJCQFVLVBTSUTVAUKULVAUTVGQHZVNVOUMVPVAJUQS
      FVGVCEQUNUOUPVBCBURUS $.
  $}

  ${
    $d F h x $.  $d X h x $.
    1arymaptfv.h $e |- H = ( h e. ( 1 -aryF X )
                            |-> ( x e. X |-> ( h ` { <. 0 , x >. } ) ) ) $.
    $( The value of the mapping of unary (endo)functions.  (Contributed by AV,
       18-May-2024.) $)
    1arymaptfv $p |- ( F e. ( 1 -aryF X )
                   -> ( H ` F ) = ( x e. X |-> ( F ` { <. 0 , x >. } ) ) ) $=
      ( cc0 cv cop csn cfv cmpt c1 cnaryf co cvv wceq fveq1 mpteq2dv wcel cfzo
      cn0 eqid naryrcl simprd mptexd fvmpt3 ) BCAEGAHIJZBHZKZLAEUHCKZLMENOZDPUI
      CQAEUJUKUHUICRSFUIULTZAEUJPUMMUBTEPTUIGMUAOZMEUNUCUDUEUFUG $.

    $d V h x $.
    $( The mapping of unary (endo)functions is a function into the set of
       endofunctions.  (Contributed by AV, 18-May-2024.) $)
    1arymaptf $p |- ( X e. V -> H : ( 1 -aryF X ) --> ( X ^m X ) ) $=
      ( wcel c1 cnaryf co cc0 cv cop csn cfv cmpt cmap wa wf fv1arycl adantll
      fmpttd simpl elmapd mpbird fmptd ) EDGZBHEIJZAEKALZMNBLZOZPZEEQJZCUGUJUHG
      ZRZULUMGEEULSUOAEUKEUNUIEGUKEGUGUIUJETUAUBUOEEULDDUGUNUCZUPUDUEFUF $.

    $d H f g $.  $d V f g h x y $.  $d X f g y $.
    $( The mapping of unary (endo)functions is a one-to-one function into the
       set of endofunctions.  (Contributed by AV, 19-May-2024.) $)
    1arymaptf1 $p |- ( X e. V -> H : ( 1 -aryF X ) -1-1-> ( X ^m X ) ) $=
      ( vf vg wcel co wf cv cfv wceq wi wral wa cc0 csn eqeq12d cnaryf cmap weq
      vy c1 wf1 1arymaptf cop cmpt 1arymaptfv ad2antrl ad2antll cvv fvex mpteqb
      wb mp1i 1aryfvalel anbi12d w3a wfn ffn adantr 3ad2ant2 adantl elmapi c0ex
      rgenw sylib opeq2 sneqd fveq2d rspccv 3ad2ant3 com12 fveq2 sylibrd impcom
      fsn2 syl eqfnfvd 3exp sylbid imp ralrimivva dff13 sylanbrc ) EDIZUEEUAJZE
      EUBJZCKGLZCMZHLZCMZNZGHUCZOZHWIPGWIPWIWJCUFABCDEFUGWHWQGHWIWIWHWKWIIZWMWI
      IZQZQZWOAERALZUHZSZWKMZUIZAEXDWMMZUIZNZWPXAWLXFWNXHWRWLXFNWHWSABWKCEFUJUK
      WSWNXHNWHWRABWMCEFUJULTXAXIXEXGNZAEPZWPXEUMIZAEPXIXKUPXAXLAEXDWKUNVHAEXEX
      GUMUOUQWHWTXKWPOZWHWTERSZUBJZEWKKZXOEWMKZQZXMWHWRXPWSXQWKDEURWMDEURUSWHXR
      XKWPWHXRXKUTZUDXOWKWMXRWHWKXOVAZXKXPXTXQXOEWKVBVCVDXRWHWMXOVAZXKXQYAXPXOE
      WMVBVEVDUDLZXOIZXSYBWKMZYBWMMZNZYCRYBMZEIZYBRYGUHZSZNZQZXSYFOYCXNEYBKYLYB
      EXNVFREYBVGVSVIYLXSYJWKMZYJWMMZNZYFYHXSYOOYKXSYHYOXKWHYHYOOXRXJYOAYGEXBYG
      NZXEYMXGYNYPXDYJWKYPXCYIXBYGRVJVKZVLYPXDYJWMYQVLTVMVNVOVCYKYFYOUPYHYKYDYM
      YEYNYBYJWKVPYBYJWMVPTVEVQVTVRWAWBWCWDWCWCWEGHWIWJCWFWG $.

    $d V a f g h x $.  $d X a $.
    $( The mapping of unary (endo)functions is a function onto the set of
       endofunctions.  (Contributed by AV, 18-May-2024.) $)
    1arymaptfo $p |- ( X e. V -> H : ( 1 -aryF X ) -onto-> ( X ^m X ) ) $=
      ( vf vg va wcel co wf cv cfv wceq wa cc0 cmpt adantl cvv cnaryf cmap wrex
      c1 wral wfo 1arymaptf elmapi eqid 1arympt1 sylan2 wb fveq2 eqeq2d feqmptd
      csn cop simplr fveq1 c0ex vex fvsn eqtrdi fveq2d simpr fsnd elmapg mpbird
      a1i snex ad4ant14 fvexd nfv nfmpt1 nfeq2 nfan nfcv mpteq2dva simpl mptexd
      fvmptdf fvmptd2 eqtr4d rspcedvd ralrimiva dffo3 sylanbrc ) EDJZUDEUAKZEEU
      BKZCLGMZHMZCNZOZHWIUCZGWJUEWIWJCUFABCDEFUGWHWOGWJWHWKWJJZPZWNWKIEQUPZUBKZ
      QIMZNZWKNZRZCNZOZHXCWIWPWHEEWKLZXCWIJWKEEUHZIWKXCDEXCUIUJUKZWLXCOZWNXEULW
      QXIWMXDWKWLXCCUMUNSWQWKAEAMZWKNZRZXDWQAEEWKWPXFWHXGSUOWQBXCAEQXJUQUPZBMZN
      ZRXLWICTFWQXNXCOZPZAEXOXKXQXJEJZPZIXMXBXKWSXNTWQXPXRURWTXMOZXBXKOXSXTXAXJ
      WKXTXAQXMNXJQWTXMUSQXJUTAVAVBVCVDSWHXRXMWSJZWPXPWHXRPZYAWREXMLZYBQXJTEQTJ
      YBUTVIWHXRVEVFXRWHWRTJZYAYCULYDXRQVJVIEWRXMDTVGUKVHVKXSXJWKVLXQXRIWQXPIWQ
      IVMIXNXCIWSXBVNVOVPXRIVMVPIXMVQIXKVQWAVRXHWQAEXKDWHWPVSVTWBWCWDWEHGWIWJCW
      FWG $.

    $( The mapping of unary (endo)functions is a one-to-one function onto the
       set of endofunctions.  (Contributed by AV, 19-May-2024.) $)
    1arymaptf1o $p |- ( X e. V -> H : ( 1 -aryF X ) -1-1-onto-> ( X ^m X ) ) $=
      ( wcel c1 cnaryf cmap wf1 wfo wf1o 1arymaptf1 1arymaptfo df-f1o sylanbrc
      co ) EDGHEIRZEEJRZCKSTCLSTCMABCDEFNABCDEFOSTCPQ $.
  $}

  ${
    $d X f h x $.  $d n x $.
    $( The set of unary (endo)functions and the set of endofunctions are
       equinumerous.  (Contributed by AV, 19-May-2024.) $)
    1aryenef $p |- ( 1 -aryF X ) ~~ ( X ^m X ) $=
      ( vh vf vx vn cvv wcel c1 cnaryf co cmap cen wbr cv wf1o wex cc0 cmpt a1i
      c0 cop csn ovex mptex eqid 1arymaptf1o f1oeq1 spcedv bren sylibr wn enref
      cfv 0ex cn0 cfzo df-naryf reldmmpo ovprc2 reldmmap ovprc1 3brtr4d pm2.61i
      ) AFGZHAIJZAAKJZLMZVDVEVFBNZOZBPVGVDVIVEVFCVEDAQDNZUAUBCNUMRZRZOBFVLVLFGV
      DCVEVKHAIUCUDSDCVLFAVLUEUFVEVFVHVLUGUHVEVFBUIUJVDUKZTTVEVFLTTLMVMTUNULSHA
      IEDUOFVJVJQENUPJKJKJIDEUQURUSAAKUTVAVBVC $.
  $}

  $( The set of unary (endo)functions and the base set of the monoid of
     endofunctions are equinumerous.  (Contributed by AV, 19-May-2024.) $)
  1aryenefmnd $p |- ( 1 -aryF X ) ~~ ( Base ` ( EndoFMnd ` X ) ) $=
    ( c1 cnaryf co cmap cefmnd cfv cbs cen 1aryenef eqid efmndbas breqtrri ) BA
    CDAAEDAFGZHGZIAJAONNKOKLM $.

  $( A binary (endo)function on a set ` X ` .  (Contributed by AV,
     20-May-2024.) $)
  2aryfvalel $p |- ( X e. V -> ( F e. ( 2 -aryF X )
                                 <-> F : ( X ^m { 0 , 1 } ) --> X ) ) $=
    ( c2 cn0 wcel cnaryf co cc0 c1 cpr cmap wf 2nn0 fzo0to2pr eqcomi naryfvalel
    wb cfzo mpan ) DEFCBFADCGHFCIJKZLHCAMRNAUADBCIDSHUAOPQT $.

  $( Closure of a binary (endo)function.  (Contributed by AV, 20-May-2024.) $)
  fv2arycl $p |- ( ( G e. ( 2 -aryF X ) /\ A e. X /\ B e. X )
                   -> ( G ` { <. 0 , A >. , <. 1 , B >. } ) e. X ) $=
    ( c2 cnaryf co wcel cc0 cop c1 cpr cfv cn0 cvv wa wi cfzo eqid w3a wf simp2
    naryrcl cmap wne c0ex 1ex 0ne1 3pm3.2i a1i fprmappr syld3an2 ffvelcdmd 3exp
    2aryfvalel sylbid adantl mpcom 3impib ) CEDFGHZADHZBDHZIAJKBJLZCMDHZENHZDOH
    ZPUTVAVBPZVDQZCIERGZEDVISUCVFUTVHQVEVFUTDIKLUDGZDCUAZVHCODUOVFVKVGVDVFVKVGT
    ZVJDVCCVFVKVGUBVFIOHZKOHZIKUEZTZVKVGVCVJHVPVLVMVNVOUFUGUHUIUJIKABOOODUKULUM
    UNUPUQURUS $.

  ${
    $d O x $.  $d V x $.  $d X x $.
    2arympt.f $e |- F = ( x e. ( X ^m { 0 , 1 } )
                          |-> ( ( x ` 0 ) O ( x ` 1 ) ) ) $.
    $( A binary (endo)function in maps-to notation.  (Contributed by AV,
       20-May-2024.) $)
    2arympt $p |- ( ( X e. V /\ O : ( X X. X ) --> X )
                    -> F e. ( 2 -aryF X ) ) $=
      ( wcel cxp wf wa c2 cnaryf co cc0 c1 cpr cfv a1i ffvelcdmd adantl cmap cv
      simplr elmapi 0elpr01 1elpr01 fovcdmd fmptd wb 2aryfvalel adantr mpbird )
      EDGZEEHECIZJZBKELMGZENOPZUAMZEBIZUOAURNAUBZQZOUTQZCMEBUOUTURGZJVAVBEEECUM
      UNVCUCVCVAEGUOVCUQENUTUTEUQUDZNUQGVCUERSTVCVBEGUOVCUQEOUTVDOUQGVCUFRSTUGF
      UHUMUPUSUIUNBDEUJUKUL $.

    $d A x $.  $d B x $.
    $( The value of a binary (endo)function in maps-to notation.  (Contributed
       by AV, 20-May-2024.) $)
    2arymptfv $p |- ( ( X e. V /\ A e. X /\ B e. X )
                      -> ( F ` { <. 0 , A >. , <. 1 , B >. } ) = ( A O B ) ) $=
      ( wcel w3a cc0 cop c1 cpr cfv co cvv wceq wa a1i cv cmap fveq1 adantl wne
      c0ex simp2 0ne1 3jca adantr fvpr1g syl eqtrd 1ex fvpr2g mp3an2i sylan9eqr
      simp3 oveq12d simp1 3pm3.2i 3simpc fprmappr syl3anc ovexd fvmptd2 ) GFIZB
      GIZCGIZJZAKBLMCLNZKAUAZOZMVLOZEPBCEPGKMNUBPZDQHVJVLVKRZSZVMBVNCEVQVMKVKOZ
      BVPVMVRRVJKVLVKUCUDVQKQIZVHKMUEZJZVRBRVJWAVPVJVSVHVTVSVJUFTVGVHVIUGVTVJUH
      TZUIUJKMBCQGUKULUMVPVJVNMVKOZCMVLVKUCMQIZVJVIVTWCCRUNVGVHVIURWBKMBCQGUOUP
      UQUSVJVGVSWDVTJZVHVISVKVOIVGVHVIUTWEVJVSWDVTUFUNUHVATVGVHVIVBKMBCQFQGVCVD
      VJBCEVEVF $.
  $}

  ${
    $d F h x y $.  $d X h x y $.
    2arymaptf.h $e |- H = ( h e. ( 2 -aryF X ) |-> ( x e. X , y e. X
                               |-> ( h ` { <. 0 , x >. , <. 1 , y >. } ) ) ) $.
    $( The value of the mapping of binary (endo)functions.  (Contributed by AV,
       21-May-2024.) $)
    2arymaptfv $p |- ( F e. ( 2 -aryF X ) -> ( H ` F ) = ( x e. X , y e. X
                               |-> ( F ` { <. 0 , x >. , <. 1 , y >. } ) ) ) $=
      ( cc0 cv cop c1 cpr cfv cmpo c2 cnaryf co cvv wceq wcel mpoeq3dv cn0 cfzo
      fveq1 eqid naryrcl mpoexga anidms simpl2im fvmpt3 ) CDABFFHAIJKBIJLZCIZMZ
      NZABFFUKDMZNOFPQZERULDSABFFUMUOUKULDUDUAGULUPTOUBTFRTZUNRTZULHOUCQZOFUSUE
      UFUQURABFFUMRRUGUHUIUJ $.

    $d V h x z $.  $d X y z $.
    $( The mapping of binary (endo)functions is a function into the set of
       binary operations.  (Contributed by AV, 21-May-2024.) $)
    2arymaptf $p |- ( X e. V -> H : ( 2 -aryF X ) --> ( X ^m ( X X. X ) ) ) $=
      ( vz wcel co cc0 cv cop c1 cpr cfv wa adantl vex opeq2d c2 cnaryf cmpo wf
      cxp cmap c1st c2nd simplr xp1st xp2nd fv2arycl syl3anc cmpt op1std op2ndd
      wceq preq12d fveq2d mpompt eqcomi fmptd wb cvv elmapg mpdan adantr mpbird
      sqxpexg ) FEIZCUAFUBJZABFFKALZMZNBLZMZOZCLZPZUCZFFFUEZUFJZDVJVQVKIZQZVSWA
      IZVTFVSUDZWCHVTKHLZUGPZMZNWFUHPZMZOZVQPZFVSWCWFVTIZQWBWGFIZWIFIZWLFIVJWBW
      MUIWMWNWCWFFFUJRWMWOWCWFFFUKRWGWIVQFULUMHVTWLUNVSABHFFWLVRWFVLVNMUQZWKVPV
      QWPWHVMWJVOWPWGVLKVLVNWFASZBSZUOTWPWIVNNVLVNWFWQWRUPTURUSUTVAVBVJWDWEVCZW
      BVJVTVDIWSFEVIFVTVSEVDVEVFVGVHGVB $.

    $d H f g $.  $d V a b f g h x y $.  $d X a b f g x y $.  $d a b f g z $.
    $( The mapping of binary (endo)functions is a one-to-one function into the
       set of binary operations.  (Contributed by AV, 22-May-2024.) $)
    2arymaptf1 $p |- ( X e. V
                       -> H : ( 2 -aryF X ) -1-1-> ( X ^m ( X X. X ) ) ) $=
      ( vf vg va vb wcel cv cfv wceq wi wral wa cc0 c1 vz c2 cnaryf co cxp cmap
      wf weq wf1 2arymaptf cop cpr cmpo 2arymaptfv ad2antrl ad2antll eqeq12d wb
      cvv fvex rgen2w mpo2eqb mp1i 2aryfvalel anbi12d w3a wfn ffn adantr adantl
      3ad2ant2 wrex elmapi wne 0ne1 c0ex ax-mp sylib opeq2 preq1d fveq2d preq2d
      1ex fprb rspc2va expcom 3ad2ant3 com12 fveq2 sylibrd rexlimivv syl impcom
      ex eqfnfvd 3exp sylbid imp ralrimivva dff13 sylanbrc ) FELZUBFUCUDZFFFUEU
      FUDZDUGHMZDNZIMZDNZOZHIUHZPZIXCQHXCQXCXDDUIABCDEFGUJXBXKHIXCXCXBXEXCLZXGX
      CLZRZRZXIABFFSAMZUKZTBMZUKZULZXENZUMZABFFXTXGNZUMZOZXJXOXFYBXHYDXLXFYBOXB
      XMABCXEDFGUNUOXMXHYDOXBXLABCXGDFGUNUPUQXOYEYAYCOZBFQAFQZXJYAUSLZBFQAFQYEY
      GURXOYHABFFXTXEUTVAABFFYAYCUSVBVCXBXNYGXJPZXBXNFSTULZUFUDZFXEUGZYKFXGUGZR
      ZYIXBXLYLXMYMXEEFVDXGEFVDVEXBYNYGXJXBYNYGVFZUAYKXEXGYNXBXEYKVGZYGYLYPYMYK
      FXEVHVIVKYNXBXGYKVGZYGYMYQYLYKFXGVHVJVKUAMZYKLZYOYRXENZYRXGNZOZYSYRSJMZUK
      ZTKMZUKZULZOZKFVLJFVLZYOUUBPZYSYJFYRUGZUUIYRFYJVMSTVNUUKUUIURVOJKSTFYRVPW
      CWDVQVRUUHUUJJKFFUUCFLUUEFLRZUUHUUJUULUUHRYOUUGXENZUUGXGNZOZUUBUULYOUUOPU
      UHYOUULUUOYGXBUULUUOPYNUULYGUUOYFUUOUUDXSULZXENZUUPXGNZOABUUCUUEFFAJUHZYA
      UUQYCUURUUSXTUUPXEUUSXQUUDXSXPUUCSVSVTZWAUUSXTUUPXGUUTWAUQBKUHZUUQUUMUURU
      UNUVAUUPUUGXEUVAXSUUFUUDXRUUETVSWBZWAUVAUUPUUGXGUVBWAUQWEWFWGWHVIUUHUUBUU
      OURUULUUHYTUUMUUAUUNYRUUGXEWIYRUUGXGWIUQVJWJWNWKWLWMWOWPWQWRWQWQWSHIXCXDD
      WTXA $.

    $d V a f g h x $.  $d X a $.
    $( The mapping of binary (endo)functions is a function onto the set of
       binary operations.  (Contributed by AV, 23-May-2024.) $)
    2arymaptfo $p |- ( X e. V
                       -> H : ( 2 -aryF X ) -onto-> ( X ^m ( X X. X ) ) ) $=
      ( vf vg va wcel co wf cv cfv wceq wa cc0 c1 cvv cnaryf cxp cmap wrex wral
      c2 wfo 2arymaptf cpr cmpt elmapi eqid 2arympt sylan2 wb fveq2 eqeq2d cmpo
      adantl wfn elmapfn fnov sylib cop w3a fveq1 wne 0ne1 c0ex vex fvpr1 ax-mp
      simp1r eqtrdi 1ex fvpr2 oveq12d fprg mp3an13 3adant1 wss prssi fssd simp1
      pm3.2i prex a1i elmapd mpbird 3adant1r ovexd nfmpt1 nfeq2 nfan nf3an nfcv
      fvmptdf mpoeq3dva mpoexga anidms adantr fvmptd2 eqtr4d rspcedvd ralrimiva
      nfv dffo3 sylanbrc ) FEKZUFFUALZFFFUBZUCLZDMHNZINZDOZPZIXJUDZHXLUEXJXLDUG
      ABCDEFGUHXIXQHXLXIXMXLKZQZXPXMJFRSUIZUCLZRJNZOZSYBOZXMLZUJZDOZPZIYFXJXRXI
      XKFXMMYFXJKXMFXKUKJYFXMEFYFULUMUNZXNYFPZXPYHUOXSYJXOYGXMXNYFDUPUQUSXSXMAB
      FFANZBNZXMLZURZYGXSXMXKUTZXMYNPXRYOXIXMFXKVAUSABFFXMVBVCXSCYFABFFRYKVDSYL
      VDUIZCNZOZURYNXJDTGXSYQYFPZQZABFFYRYMYTYKFKZYLFKZVEZJYPYEYMYAYQTXSYSUUAUU
      BVMYBYPPZYEYMPUUCUUDYCYKYDYLXMUUDYCRYPOZYKRYBYPVFRSVGZUUEYKPVHRSYKYLVIAVJ
      VKVLVNUUDYDSYPOZYLSYBYPVFUUFUUGYLPVHRSYKYLVOBVJVPVLVNVQUSXSUUAUUBYPYAKZYS
      XIUUAUUBUUHXRXIUUAUUBVEZUUHXTFYPMUUIXTYKYLUIZFYPUUAUUBXTUUJYPMZXIRTKZSTKZ
      QUUAUUBQUUFUUKUULUUMVIVOWEVHRSYKYLTTFFVRVSVTUUAUUBUUJFWAXIYKYLFWBVTWCUUIF
      XTYPETXIUUAUUBWDXTTKUUIRSWFWGWHWIWJWJUUCYKYLXMWKYTUUAUUBJXSYSJXSJXFJYQYFJ
      YAYEWLWMWNUUAJXFUUBJXFWOJYPWPJYMWPWQWRYIXIYNTKZXRXIUUNABFFYMEEWSWTXAXBXCX
      DXEIHXJXLDXGXH $.

    $( The mapping of binary (endo)functions is a one-to-one function onto the
       set of binary operations.  (Contributed by AV, 23-May-2024.) $)
    2arymaptf1o $p |- ( X e. V
                      -> H : ( 2 -aryF X ) -1-1-onto-> ( X ^m ( X X. X ) ) ) $=
      ( wcel cnaryf cxp cmap wf1 wfo wf1o 2arymaptf1 2arymaptfo df-f1o sylanbrc
      c2 co ) FEHSFITZFFFJKTZDLUAUBDMUAUBDNABCDEFGOABCDEFGPUAUBDQR $.
  $}

  ${
    $d X f h x y $.  $d n x $.
    $( The set of binary (endo)functions and the set of binary operations are
       equinumerous.  (Contributed by AV, 19-May-2024.) $)
    2aryenef $p |- ( 2 -aryF X ) ~~ ( X ^m ( X X. X ) ) $=
      ( vh vf vx vy vn cvv wcel c2 cnaryf co cmap cen wbr cv wf1o cc0 cop a1i
      c0 cxp wex c1 cpr cfv cmpo cmpt ovex mptex eqid 2arymaptf1o f1oeq1 spcedv
      bren sylibr wn 0ex enref cn0 cfzo df-naryf reldmmpo ovprc2 ovprc1 3brtr4d
      reldmmap pm2.61i ) AGHZIAJKZAAAUAZLKZMNZVHVIVKBOZPZBUBVLVHVNVIVKCVIDEAAQD
      OZRUCEORUDCOUEUFZUGZPBGVQVQGHVHCVIVPIAJUHUISDECVQGAVQUJUKVIVKVMVQULUMVIVK
      BUNUOVHUPZTTVIVKMTTMNVRTUQURSIAJFDUSGVOVOQFOUTKLKLKJDFVAVBVCAVJLVFVDVEVG
      $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Primitive recursive functions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  According to Wikipedia ("Primitive recursive function", 19-May-2024,
  ~ https://en.wikipedia.org/wiki/Primitive_recursive_function ): "In
  computability theory, a primitive recursive function is, roughly speaking, a
  function that can be computed by a computer program whose loops are all "for"
  loops (that is, an upper bound of the number of iterations of every loop is
  fixed before entering the loop). Primitive recursive functions form a strict
  subset of those general recursive functions that are also total functions."

  Furthermore: "A primitive recursive function takes a fixed number of
  arguments, each a natural number (nonnegative integer: {0, 1, 2, ...}), and
  returns a natural number. If it takes n arguments it is called n-ary.

  The basic primitive recursive functions are given by ... axioms:

    1. Constant functions

    2. Successor function

    3. Projection functions

  More complex primitive recursive functions can be obtained by applying the
  operations given by ... axioms:

    4. Composition operator

    5. Primitive recursion operator

  The primitive recursive functions are the basic functions and those obtained
  from the basic functions by applying these operations a finite number of
  times."

$)

$( TODO-AV: Definitions and related theorems $)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The Ackermann function
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  According to Wikipedia ("Ackermann function", 8-May-2024,
  ~ https://en.wikipedia.org/wiki/Ackermann_function ): "In computability
  theory, the Ackermann function, named after Wilhelm Ackermann, is one of the
  simplest and earliest-discovered examples of a total computable function that
  is not primitive recursive. ... One common version is the two-argument
  Ackermann-P&eacute;ter function developed by R&oacute;zsa P&eacute;ter and
  Raphael Robinson.  Its value grows very rapidly; for example, A(4,2) results
  in 2^65536-3 [[see ~ ackval42 )], an integer of 19,729 decimal digits."

  In the following, the Ackermann function is defined as iterated 1-ary
  function (also mentioned in Wikipedia), see ~ df-ack , based on a definition
  ` IterComp ` of "the n-th iterate of (a class/function) f", see ~ df-itco .
  As an illustration, we have ` ( ( IterComp `` F ) `` 3 ) `
  ` = ( F o. ( F o. F ) ) ) ` (see ~ itcoval3 ).

  The following recursive definition of the Ackermann function follows
  immediately from Definition ~ df-ack : ` ( ( Ack `` ( M + 1 ) ) `` N ) `
  ` = ( ( ( IterComp `` ( Ack `` M ) ) `` ( N + 1 ) ) `` 1 ) ) `.

  That Definition ~ df-ack is equivalent to P&eacute;ter's definition is
  proven by the following three theorems:

  ~ ackval0val : ` ( ( Ack `` 0 ) `` M ) = ( M + 1 ) ` ;
  ~ ackvalsuc0val : ` ( ( Ack `` ( M + 1 ) ) `` 0 ) = ( ( Ack `` M ) `` 1 ) ` ;
  ~ ackvalsucsucval : ` ( ( Ack `` ( M + 1 ) ) `` ( N + 1 ) ) `
                      ` = ( ( Ack `` M ) `` ( ( Ack `` ( M + 1 ) ) `` N ) ) ` .

  The initial values of the Ackermann function are calculated in the following
  four theorems:

  ~ ackval0012 : ` A ( 0 , 0 ) = 1 ` , ` A ( 0 , 1 ) = 2 ` ,
                 ` A ( 0 , 2 ) = 3 ` ;
  ~ ackval1012 : ` A ( 1 , 0 ) = 2 ` , ` A ( 1 , 1 ) = 3 ` ,
                 ` A ( 1 , 3 ) = 4 ` ;
  ~ ackval2012 : ` A ( 2 , 0 ) = 3 ` , ` A ( 2 , 1 ) = 5 ` ,
                 ` A ( 2 , 3 ) = 7 ` ;
  ~ ackval3012 : ` A ( 3 , 0 ) = 5 ` , ` A ( 3 , 1 ) = ; 1 3 ` ,
                 ` A ( 3 , 3 ) = ; 2 9 ` .

$)

  $c IterComp $.
  $c Ack $.

  $( Extend the definition of a class to include iterated functions. $)
  citco $a class IterComp $.

  $( Extend the definition of a class to include the Ackermann function
     operator. $)
  cack $a class Ack $.

  ${
    $d f g i j $.
    $( Define a function (recursively) that returns the n-th iterate of a class
       (usually a function) with regard to composition.  (Contributed by
       Thierry Arnoux, 28-Apr-2024.)  (Revised by AV, 2-May-2024.) $)
    df-itco $a |- IterComp = ( f e. _V
         |-> seq 0 ( ( g e. _V , j e. _V |-> ( f o. g ) ) ,
                     ( i e. NN0 |-> if ( i = 0 , ( _I |` dom f ) , f ) ) ) ) $.
  $}

  ${
    $d f i j n $.
    $( Define the Ackermann function (recursively).  (Contributed by Thierry
       Arnoux, 28-Apr-2024.)  (Revised by AV, 2-May-2024.) $)
    df-ack $a |- Ack = seq 0 ( ( f e. _V , j e. _V |-> ( n e. NN0
                             |-> ( ( ( IterComp ` f ) ` ( n + 1 ) ) ` 1 ) ) ) ,
                               ( i e. NN0 |-> if ( i = 0 ,
                                        ( n e. NN0 |-> ( n + 1 ) ) , i ) ) ) $.
  $}

  ${
    $d F f g i j $.
    $( The value of the function that returns the n-th iterate of a class
       (usually a function) with regard to composition.  (Contributed by AV,
       2-May-2024.) $)
    itcoval $p |- ( F e. V -> ( IterComp ` F )
           = seq 0 ( ( g e. _V , j e. _V |-> ( F o. g ) ) ,
                     ( i e. NN0 |-> if ( i = 0 , ( _I |` dom F ) , F ) ) ) ) $=
      ( vf wcel cvv cv ccom cmpo cn0 cc0 wceq cid cdm cres cif cmpt cseq id a1i
      citco df-itco eqidd mpoeq3dv dmeq reseq2d ifeq12d mpteq2dv seqeq123d elex
      coeq1 seqex fvmptd3 ) DEGZFDACHHFIZAIZJZKZBLBIMNZOUQPZQZUQRZSZMTACHHDURJZ
      KZBLVAODPZQZDRZSZMTZHUCHFABCUDUQDNZUTVGVEVKMMVMMUEVMACHHUSVFUQDURUMUFVMBL
      VDVJVMVAVCVIUQDVMVBVHOUQDUGUHVMUAUIUJUKDEULVLHGUPVGVKMUNUBUO $.
  $}

  ${
    $d F g i j $.  $d V i $.
    $( A function iterated zero times (defined as identity function).
       (Contributed by AV, 2-May-2024.) $)
    itcoval0 $p |- ( F e. V -> ( ( IterComp ` F ) ` 0 )
                               = ( _I |` dom F ) ) $=
      ( vg vj vi wcel cc0 citco cfv cvv cv ccom cmpo cn0 wceq cid cdm cres cmpt
      cif cseq itcoval fveq1d eqidd iftrue adantl 0nn0 a1i dmexg resiexd fvmptd
      0z seq1i eqtrd ) ABFZGAHIZIGCDJJACKLMZENEKGOZPAQZRZATZSZGUAZIUTUOGUPVCCED
      ABUBUCUOUTUQVBGULUOEGVAUTNVBJUOVBUDURVAUTOUOURUTAUEUFGNFUOUGUHUOUSJABUIUJ
      UKUMUN $.

    $d V g j $.
    $( A function iterated once.  (Contributed by AV, 2-May-2024.) $)
    itcoval1 $p |- ( ( Rel F /\ F e. V ) -> ( ( IterComp ` F ) ` 1 ) = F ) $=
      ( vg vj vi wcel c1 cfv cvv ccom cn0 cc0 wceq cres fveq1d adantl a1i eqtrd
      cv eqidd wrel wa citco cmpo cid cdm cmpt cseq itcoval co nn0uz 0nn0 1e0p1
      cif eqcomd itcoval0 ax-1ne0 neii eqeq1 mtbiri iffalsed 1nn0 fvmptd seqp1d
      simpr coeq2 ad2antrl dmexg resiexd elex coexg mpdan ovmpod coires1 adantr
      resdm eqtrid ) AUAZABFZUBZGAUCHZHZGCDIIACSZJZUDZEKESZLMZUEAUFZNZAUNZUGZLU
      HZHZAVSWBWMMVRVSGWAWLCEDABUIZOPVTWMWIAWEUJZAVTWIAWEWKGLLKUKLKFVTULQUMVSLW
      LHZWIMVRVSWPLWAHWIVSLWLWAVSWAWLWNUOOABUPRPVTEGWJAKWKBVTWKTWFGMZWJAMVTWQWG
      WIAWQWGGLMGLUQURWFGLUSUTVAPGKFVTVBQVRVSVEVCVDVTWOAWIJZAVSWOWRMVRVSCDWIAII
      WDWRWEIVSWETWCWIMWDWRMVSDSAMWCWIAVFVGVSWHIABVHVIZABVJVSWIIFWRIFWSAWIBIVKV
      LVMPVTWRAWHNZAAWHVNVRWTAMVSAVPVOVQRRR $.

    $( A function iterated twice.  (Contributed by AV, 2-May-2024.) $)
    itcoval2 $p |- ( ( Rel F /\ F e. V ) -> ( ( IterComp ` F ) ` 2 )
                                            = ( F o. F ) ) $=
      ( vg vj vi wcel c2 cfv cvv cv ccom cn0 cc0 fveq1d adantl c1 a1i eqidd wne
      wceq wrel wa citco cmpo cid cdm cres cmpt cseq co itcoval nn0uz 1nn0 df-2
      eqcomd itcoval1 eqtrd 2ne0 neeq1 mpbiri neneqd iffalsed 2nn0 simpr fvmptd
      cif seqp1d coeq2 ad2antrl elex coexg anidms ovmpod 3eqtrd ) AUAZABFZUBZGA
      UCHZHZGCDIIACJZKZUDZELEJZMTZUEAUFUGZAVFZUHZMUIZHZAAWBUJZAAKZVPVSWITVOVPGV
      RWHCEDABUKZNOVQAAWBWGGMPLULPLFVQUMQUNVQPWHHZPVRHZAVPWMWNTVOVPPWHVRVPVRWHW
      LUONOABUPUQVQEGWFALWGBVQWGRWCGTZWFATVQWOWDWEAWOWCMWOWCMSGMSURWCGMUSUTVAVB
      OGLFVQVCQVOVPVDVEVGVPWJWKTVOVPCDAAIIWAWKWBIVPWBRVTATWAWKTVPDJATVTAAVHVIAB
      VJZWPVPWKIFAABBVKVLVMOVN $.

    $( A function iterated three times.  (Contributed by AV, 2-May-2024.) $)
    itcoval3 $p |- ( ( Rel F /\ F e. V ) -> ( ( IterComp ` F ) ` 3 )
                                            = ( F o. ( F o. F ) ) ) $=
      ( vg vj vi wcel c3 cfv cvv cv ccom cn0 cc0 fveq1d adantl c2 a1i eqidd wne
      wceq wrel wa citco cmpo cid cdm cres cmpt cseq co itcoval nn0uz 2nn0 df-3
      eqcomd itcoval2 eqtrd 3ne0 neeq1 mpbiri neneqd iffalsed 3nn0 simpr fvmptd
      cif seqp1d coeq2 ad2antrl coexg anidms elex syldan ovmpod 3eqtrd ) AUAZAB
      FZUBZGAUCHZHZGCDIIACJZKZUDZELEJZMTZUEAUFUGZAVFZUHZMUIZHZAAKZAWCUJZAWKKZVQ
      VTWJTVPVQGVSWICEDABUKZNOVRWKAWCWHGMPLULPLFVRUMQUNVRPWIHZPVSHZWKVQWOWPTVPV
      QPWIVSVQVSWIWNUONOABUPUQVREGWGALWHBVRWHRWDGTZWGATVRWQWEWFAWQWDMWQWDMSGMSU
      RWDGMUSUTVAVBOGLFVRVCQVPVQVDVEVGVQWLWMTVPVQCDWKAIIWBWMWCIVQWCRWAWKTWBWMTV
      QDJATWAWKAVHVIVQWKIFZAABBVJZVKABVLVQWMIFZVQVQWRWTWSAWKBIVJVMVKVNOVO $.
  $}

  ${
    $d A n $.
    itcoval0mpt.f $e |- F = ( n e. A |-> B ) $.
    $( A mapping iterated zero times (defined as identity function).
       (Contributed by AV, 4-May-2024.) $)
    itcoval0mpt $p |- ( ( A e. V /\ A. n e. A B e. W )
                        -> ( ( IterComp ` F ) ` 0 ) = ( n e. A |-> n ) ) $=
      ( wcel wral cc0 citco cfv cid cmpt cdm cres cv fveq2i fveq1i cvv itcoval0
      wceq mptexg syl eqtrid dmmptg reseq2d mptresid eqtrdi sylan9eq ) AEHZBFHC
      AIZJDKLZLZMCABNZOZPZCACQNZUKUNJUOKLZLZUQJUMUSDUOKGRSUKUOTHUTUQUBCABEUCUOT
      UAUDUEULUQMAPURULUPAMCABFUFUGCAUHUIUJ $.
  $}

  ${
    $d F g i j $.  $d G i $.  $d V i $.  $d Y i $.
    $( The value of the function that returns the n-th iterate of a function
       with regard to composition at a successor.  (Contributed by AV,
       4-May-2024.) $)
    itcovalsuc $p |- ( ( F e. V /\ Y e. NN0 /\ ( ( IterComp ` F ) ` Y ) = G )
                       -> ( ( IterComp ` F ) ` ( Y + 1 ) )
                          = ( G ( g e. _V , j e. _V |-> ( F o. g ) ) F ) ) $=
      ( vi wcel cn0 cfv wceq co cvv cv cc0 fveq1d wa adantr wne 3ad2ant2 w3a c1
      citco caddc ccom cmpo cid cdm cres cif cmpt simp1 itcoval syl nn0uz simp2
      cseq eqeq1d biimp3a eqidd clt wbr nn0p1gt0 gt0ne0d wb neeq1 adantl mpbird
      eqid neneqd iffalsed peano2nn0 fvmptd seqp1d eqtrd ) CEHZFIHZFCUCJZJZDKZU
      AZFUBUDLZVRJZWBABMMCANUEUFZGIGNZOKZUGCUHUIZCUJZUKZOUQZJZDCWDLWAVPWCWKKVPV
      QVTULZVPWBVRWJAGBCEUMZPUNWADCWDWIWBOFIUOVPVQVTUPWBVIVPVQVTFWJJZDKVPVQQZVS
      WNDWOFVRWJVPVRWJKVQWMRPURUSWAGWBWHCIWIEWAWIUTWAWEWBKZQZWFWGCWQWEOWQWEOSZW
      BOSZWAWSWPWAWBVQVPOWBVAVBVTFVCTVDRWPWRWSVEWAWEWBOVFVGVHVJVKVQVPWBIHVTFVLT
      WLVMVNVO $.

    $d G g j $.  $d V g j $.  $d Y g j $.
    $( The value of the function that returns the n-th iterate of a function
       with regard to composition at a successor.  (Contributed by AV,
       4-May-2024.) $)
    itcovalsucov $p |- ( ( F e. V /\ Y e. NN0 /\ ( ( IterComp ` F ) ` Y ) = G )
                       -> ( ( IterComp ` F ) ` ( Y + 1 ) ) = ( F o. G ) ) $=
      ( vg vj wcel cn0 citco cfv wceq w3a c1 caddc co cvv ccom cmpo itcovalsuc
      cv eqidd coeq2 ad2antrl id fvex eqeltrdi eqcoms 3ad2ant3 elex 3ad2ant1 wa
      anim2i 3adant2 coexg syl ovmpod eqtrd ) ACGZDHGZDAIJZJZBKZLZDMNOUTJBAEFPP
      AETZQZRZOABQZEFABCDSVCEFBAPPVEVGVFPVCVFUAVDBKVEVGKVCFTAKVDBAUBUCVBURBPGZU
      SVHBVABVAKZBVAPVIUDDUTUEUFUGZUHURUSAPGVBACUIUJVCURVHUKZVGPGURVBVKUSVBVHUR
      VJULUMABCPUNUOUPUQ $.
  $}

  ${
    $d A x y $.  $d F x y $.  $d N x $.  $d ph x y $.
    itcovalendof.a $e |- ( ph -> A e. V ) $.
    itcovalendof.f $e |- ( ph -> F : A --> A ) $.
    itcovalendof.n $e |- ( ph -> N e. NN0 ) $.
    $( The n-th iterate of an endofunction is an endofunction.  (Contributed by
       AV, 7-May-2024.) $)
    itcovalendof $p |- ( ph -> ( ( IterComp ` F ) ` N ) : A --> A ) $=
      ( vx vy wcel cfv wf cc0 wceq fveq2 feq1d cid mpbird cvv citco cv c1 caddc
      cn0 co weq cdm cres wf1o f1oi f1of mp1i fdmd reseq2d fexd itcoval0 syl wa
      ccom ad2antrr simpr fcod simplr eqidd itcovalsucov syl3anc nn0indd mpdan
      ) ADUEKBBDCUALZLZMZHABBIUBZVJLZMBBNVJLZMZBBJUBZVJLZMZBBVQUCUDUFZVJLZMZVLI
      JDVMNOBBVNVOVMNVJPQIJUGBBVNVRVMVQVJPQVMVTOBBVNWAVMVTVJPQVMDOBBVNVKVMDVJPQ
      AVPBBRCUHZUIZMZAWEBBRBUIZMZBBWFUJWGABUKBBWFULUMABBWDWFAWCBRABBCGUNUOQSABB
      VOWDACTKZVOWDOABBECGFUPZCTUQURQSAVQUEKZUSZVSUSZWBBBCVRUTZMWLBBBCVRABBCMWJ
      VSGVAWKVSVBVCWLBBWAWMWLWHWJVRVROWAWMOAWHWJVSWIVAAWJVSVDWLVRVECVRTVQVFVGQS
      VHVI $.
  $}

  ${
    $d C n $.
    itcovalpc.f $e |- F = ( n e. NN0 |-> ( n + C ) ) $.
    $( Lemma 1 for ~ itcovalpc : induction basis.  (Contributed by AV,
       4-May-2024.) $)
    itcovalpclem1 $p |- ( C e. NN0 -> ( ( IterComp ` F ) ` 0 )
                          = ( n e. NN0 |-> ( n + ( C x. 0 ) ) ) ) $=
      ( cn0 wcel cc0 citco cfv cv cmpt cmul co caddc cvv wral nn0ex ovexd nn0cn
      wceq rgen itcoval0mpt mp2an wa mul01d adantr oveq2d addridd adantl eqtr2d
      mpteq2dva eqtrid ) AEFZGCHIIZBEBJZKZBEUOAGLMZNMZKEOFUOANMZOFZBEPUNUPTQUTB
      EUOEFZUOANRUAEUSBCOODUBUCUMBEUOURUMVAUDZURUOGNMZUOVBUQGUONUMUQGTVAUMAASUE
      UFUGVAVCUOTUMVAUOUOSUHUIUJUKUL $.

    $d C m $.  $d m n y $.
    $( Lemma 2 for ~ itcovalpc : induction step.  (Contributed by AV,
       4-May-2024.) $)
    itcovalpclem2 $p |- ( ( y e. NN0 /\ C e. NN0 )
            -> ( ( ( IterComp ` F ) ` y ) = ( n e. NN0 |-> ( n + ( C x. y ) ) )
                 -> ( ( IterComp ` F ) ` ( y + 1 ) )
                    = ( n e. NN0 |-> ( n + ( C x. ( y + 1 ) ) ) ) ) ) $=
      ( vm cv cn0 wcel wa cfv cmul co caddc cmpt wceq c1 cvv simpr nn0cnd citco
      ccom nn0ex mptex eqeltri simpl itcovalsucov mp3an2ani nn0mulcld nn0addcld
      simplr adantr eqidd oveq1 cbvmptv eqtri a1i fmptco addassd mulridd adantl
      nn0cn eqcomd oveq2d 1cnd adddid eqtr4d eqtrd mpteq2dva ex ) AGZHIZBHIZJZV
      KDUAKZKCHCGZBVKLMZNMZOZPZVKQNMZVOKZCHVPBWALMZNMZOZPVNVTJWBDVSUBZWEDRIVNVL
      VTVTWBWFPDCHVPBNMZOZRECHWGUCUDUEVLVMUFZVNVTSDVSRVKUGUHVNWFWEPVTVNWFCHVRBN
      MZOWEVNCFHHVRFGZBNMZWJVSDVNVPHIZJZVPVQVNWMSZWNBVKVLVMWMUKZVNVLWMWIULUIZUJ
      VNVSUMDFHWLOZPVNDWHWRECFHWGWLVPWKBNUNUOUPUQWKVRBNUNURVNCHWJWDWNWJVPVQBNMZ
      NMZWDWNVPVQBWNVPWOTWNVQWQTWNBWPTUSVNWTWDPWMVNWSWCVPNVNWSVQBQLMZNMWCVNBXAV
      QNVNXABVMXABPVLVMBBVBUTVAVCVDVNBVKQVNBVLVMSTVNVKWITVNVEVFVGVDULVHVIVHULVH
      VJ $.

    $d C n x y $.  $d F x y $.  $d I n x $.
    $( The value of the function that returns the n-th iterate of the "plus a
       constant" function with regard to composition.  (Contributed by AV,
       4-May-2024.) $)
    itcovalpc $p |- ( ( I e. NN0 /\ C e. NN0 ) -> ( ( IterComp ` F ) ` I )
                                     = ( n e. NN0 |-> ( n + ( C x. I ) ) ) ) $=
      ( vy cn0 wcel cfv cmul co caddc cmpt wceq cc0 fveq2 oveq2 oveq2d mpteq2dv
      eqeq12d vx citco cv c1 itcovalpclem1 wa itcovalpclem2 ancoms imp nn0indd
      wi ) AGHZDGHDCUBIZIZBGBUCZADJKZLKZMZNZULUAUCZUMIZBGUOAUTJKZLKZMZNOUMIZBGU
      OAOJKZLKZMZNFUCZUMIZBGUOAVIJKZLKZMZNZVIUDLKZUMIZBGUOAVOJKZLKZMZNZUSUAFDUT
      ONZVAVEVDVHUTOUMPWABGVCVGWAVBVFUOLUTOAJQRSTUTVINZVAVJVDVMUTVIUMPWBBGVCVLW
      BVBVKUOLUTVIAJQRSTUTVONZVAVPVDVSUTVOUMPWCBGVCVRWCVBVQUOLUTVOAJQRSTUTDNZVA
      UNVDURUTDUMPWDBGVCUQWDVBUPUOLUTDAJQRSTABCEUEULVIGHZUFVNVTWEULVNVTUKFABCEU
      GUHUIUJUH $.
  $}

  $( Lemma 1 for ~ itcovalt2lem2 .  (Contributed by AV, 6-May-2024.) $)
  itcovalt2lem2lem1 $p |- ( ( ( Y e. NN /\ C e. NN0 ) /\ N e. NN0 )
                            -> ( ( ( N + C ) x. Y ) - C ) e. NN0 ) $=
    ( cn wcel cn0 wa caddc co cmul cle wbr cmin cr adantl adantr simpr ad2antrr
    nn0red mpbid nn0re nn0addcld nnnn0 nn0mulcld nn0ge0 addge02d simpll nn0ge0d
    cc0 nnred c1 nnge1 lemulge11d letrd wb nn0sub syl2anc ) CDEZAFEZGZBFEZGZABA
    HIZCJIZKLZVDAMIFEZVBAVCVDUTANEZVAUSVGURAUAOPVBVCVBBAUTVAQZUTUSVAURUSQPZUBZS
    ZVBVDVBVCCVJURCFEUSVACUCRUDZSVBUIBKLZAVCKLVAVMUTBUEOVBABVBAVISVBBVHSUFTVBVC
    CVKVBCURUSVAUGUJVBVCVJUHURUKCKLUSVACULRUMUNVBUSVDFEVEVFUOVIVLAVDUPUQT $.

  $( Lemma 2 for ~ itcovalt2lem2 .  (Contributed by AV, 7-May-2024.) $)
  itcovalt2lem2lem2 $p |- ( ( ( Y e. NN0 /\ C e. NN0 ) /\ N e. NN0 )
                         -> ( ( 2 x. ( ( ( N + C ) x. ( 2 ^ Y ) ) - C ) ) + C )
                            = ( ( ( N + C ) x. ( 2 ^ ( Y + 1 ) ) ) - C ) ) $=
    ( wcel wa c2 caddc co cexp cmul cmin 2cnd simpr adantr nn0cnd 2nn0 ad2antrr
    cn0 a1i nn0mulcld c1 nn0addcld cc id nn0expcld mulcld nn0cn ad2antlr subdid
    oveq1d subsubd mul12d wceq mulcomd expp1d eqtr4d eqtrd 2txmxeqx syl oveq12d
    oveq2d 3eqtr2d ) CRDZARDZEZBRDZEZFBAGHZFCIHZJHZAKHJHZAGHFVJJHZFAJHZKHZAGHVL
    VMAKHZKHVHFCUAGHIHZJHZAKHVGVKVNAGVGFVJAVGLZVGVHVIVGVHVGBAVEVFMVEVDVFVCVDMZN
    ZUBZOZVCVIUCDVDVFVCVIVCFCFRDZVCPSVCUDZUEZOZQZUFVDAUCDZVCVFAUGZUHUIUJVGVLVMA
    VGVLVGFVJWCVGPSVGVHVIWAVCVIRDVDVFWEQTTOVGVMVEVMRDVFVEFAWCVEPSVSTNOVGAVTOUKV
    GVLVQVOAKVGVLVHFVIJHZJHVQVGFVHVIVRWBWGULVGWJVPVHJVCWJVPUMVDVFVCWJVIFJHVPVCF
    VIVCLZWFUNVCFCWKWDUOUPQVAUQVDVOAUMZVCVFVDWHWLWIAURUSUHUTVB $.

  ${
    $d C n $.
    itcovalt2.f $e |- F = ( n e. NN0 |-> ( ( 2 x. n ) + C ) ) $.
    $( Lemma 1 for ~ itcovalt2 : induction basis.  (Contributed by AV,
       5-May-2024.) $)
    itcovalt2lem1 $p |- ( C e. NN0 -> ( ( IterComp ` F ) ` 0 )
                     = ( n e. NN0 |-> ( ( ( n + C ) x. ( 2 ^ 0 ) ) - C ) ) ) $=
      ( cn0 wcel cc0 citco cfv cmpt caddc co c2 cmul cvv wa wceq nn0cnd eqtrd
      c1 cv cexp cmin wral nn0ex ovexd rgen pm3.2i itcoval0mpt mp1i simpr simpl
      2nn0 numexp0 a1i oveq2d nn0addcld mulridd mvrraddd eqcomd mpteq2dva ) AEF
      ZGCHIIZBEBUAZJZBEVDAKLZMGUBLZNLZAUCLZJEOFZMVDNLZAKLZOFZBEUDZPVCVEQVBVJVNU
      EVMBEVDEFZVKAKUFUGUHEVLBCOODUIUJVBBEVDVIVBVOPZVIVDVPVHVDAVPVDVBVOUKZRVPAV
      BVOULZRVPVHVFTNLVFVPVGTVFNVGTQVPMUMUNUOUPVPVFVPVFVPVDAVQVRUQRURSUSUTVAS
      $.

    $d C m $.  $d m n y $.
    $( Lemma 2 for ~ itcovalt2 : induction step.  (Contributed by AV,
       7-May-2024.) $)
    itcovalt2lem2 $p |- ( ( y e. NN0 /\ C e. NN0 )
            -> ( ( ( IterComp ` F ) ` y )
                          = ( n e. NN0 |-> ( ( ( n + C ) x. ( 2 ^ y ) ) - C ) )
                 -> ( ( IterComp ` F ) ` ( y + 1 ) ) = ( n e. NN0
                        |-> ( ( ( n + C ) x. ( 2 ^ ( y + 1 ) ) ) - C ) ) ) ) $=
      ( vm cv cn0 wcel wa cfv caddc co c2 cexp cmul cmin cmpt wceq cvv citco c1
      ccom nn0ex mptex eqeltri simpl simpr itcovalsucov mp3an2ani cn 2nn a1i id
      nnexpcld itcovalt2lem2lem1 sylanl1 eqidd oveq1d cbvmptv itcovalt2lem2lem2
      oveq2 eqtri fmptco mpteq2dva eqtrd adantr ex ) AGZHIZBHIZJZVIDUAKZKCHCGZB
      LMZNVIOMZPMBQMZRZSZVIUBLMZVMKZCHVONVTOMPMBQMZRZSVLVSJWADVRUCZWCDTIVLVJVSV
      SWAWDSDCHNVNPMZBLMZRZTECHWFUDUEUFVJVKUGVLVSUHDVRTVIUIUJVLWDWCSVSVLWDCHNVQ
      PMZBLMZRWCVLCFHHVQNFGZPMZBLMZWIVRDVJVPUKIVKVNHIVQHIVJNVINUKIVJULUMVJUNUOB
      VNVPUPUQVLVRURDFHWLRZSVLDWGWMECFHWFWLVNWJSWEWKBLVNWJNPVBUSUTVCUMWJVQSWKWH
      BLWJVQNPVBUSVDVLCHWIWBBVNVIVAVEVFVGVFVH $.

    $d C x y $.  $d F x y $.  $d I n x $.
    $( The value of the function that returns the n-th iterate of the "times 2
       plus a constant" function with regard to composition.  (Contributed by
       AV, 7-May-2024.) $)
    itcovalt2 $p |- ( ( I e. NN0 /\ C e. NN0 ) -> ( ( IterComp ` F ) ` I )
                     = ( n e. NN0 |-> ( ( ( n + C ) x. ( 2 ^ I ) ) - C ) ) ) $=
      ( cn0 cfv co c2 cexp cmul cmin cmpt wceq wi cc0 fveq2 oveq2 oveq2d oveq1d
      vx vy wcel citco cv caddc c1 mpteq2dv eqeq12d imbi2d itcovalt2lem1 pm2.27
      wa adantl itcovalt2lem2 syld ex com23 nn0ind imp ) DFUCAFUCZDCUDGZGZBFBUE
      AUFHZIDJHZKHZALHZMZNZVAUAUEZVBGZBFVDIVJJHZKHZALHZMZNZOVAPVBGZBFVDIPJHZKHZ
      ALHZMZNZOVAUBUEZVBGZBFVDIWCJHZKHZALHZMZNZOZVAWCUGUFHZVBGZBFVDIWKJHZKHZALH
      ZMZNZOVAVIOUAUBDVJPNZVPWBVAWRVKVQVOWAVJPVBQWRBFVNVTWRVMVSALWRVLVRVDKVJPIJ
      RSTUHUIUJVJWCNZVPWIVAWSVKWDVOWHVJWCVBQWSBFVNWGWSVMWFALWSVLWEVDKVJWCIJRSTU
      HUIUJVJWKNZVPWQVAWTVKWLVOWPVJWKVBQWTBFVNWOWTVMWNALWTVLWMVDKVJWKIJRSTUHUIU
      JVJDNZVPVIVAXAVKVCVOVHVJDVBQXABFVNVGXAVMVFALXAVLVEVDKVJDIJRSTUHUIUJABCEUK
      WCFUCZVAWJWQXBVAWJWQOXBVAUMWJWIWQVAWJWIOXBVAWIULUNUBABCEUOUPUQURUSUT $.
  $}

  ${
    $d M f i j n $.
    $( The Ackermann function at a successor of the first argument as a mapping
       of the second argument.  (Contributed by Thierry Arnoux, 28-Apr-2024.)
       (Revised by AV, 4-May-2024.) $)
    ackvalsuc1mpt $p |- ( M e. NN0 -> ( Ack ` ( M + 1 ) ) = ( n e. NN0
                  |-> ( ( ( IterComp ` ( Ack ` M ) ) ` ( n + 1 ) ) ` 1 ) ) ) $=
      ( vf vj vi cn0 wcel c1 caddc co cack cfv cvv cv citco cmpt cc0 fveq1i a1i
      wceq cmpo cif cseq df-ack nn0uz id eqid eqcomi eqidd wne nn0p1gt0 gt0ne0d
      wa adantr neeq1 adantl mpbird neneqd iffalsed simpr eqtrd peano2nn0 fveq2
      wb fvmptd seqp1d fveq1d mpteq2dv ad2antrl fvexd ovexd nn0ex ovmpod eqtrid
      mptex ) BFGZBHIJZKLVQCDMMAFHANHIJZCNZOLZLZLZPZUAZEFENZQTZAFVRPZWEUBZPZQUC
      ZLZAFHVRBKLZOLZLZLZPZVQKWJCEDAUDZRVPWKWLVQWDJWPVPWLVQWDWIVQQBFUEVPUFVQUGB
      WJLWLTVPBWJKKWJWQUHRSVPEVQWHVQFWIFVPWIUIVPWEVQTZUMZWHWEVQWSWFWGWEWSWEQWSW
      EQUJZVQQUJZVPXAWRVPVQBUKULUNWRWTXAVDVPWEVQQUOUPUQURUSVPWRUTVABVBZXBVEVFVP
      CDWLVQMMWCWPWDMVPWDUIVSWLTZWCWPTVPDNVQTXCAFWBWOXCHWAWNXCVRVTWMVSWLOVCVGVG
      VHVIVPBKVJVPBHIVKWPMGVPAFWOVLVOSVMVAVN $.
  $}

  ${
    $d M n $.  $d N n $.
    $( The Ackermann function at a successor of the first argument and an
       arbitrary second argument.  (Contributed by Thierry Arnoux,
       28-Apr-2024.)  (Revised by AV, 4-May-2024.) $)
    ackvalsuc1 $p |- ( ( M e. NN0 /\ N e. NN0 ) -> ( ( Ack ` ( M + 1 ) ) ` N )
                      = ( ( ( IterComp ` ( Ack ` M ) ) ` ( N + 1 ) ) ` 1 ) ) $=
      ( vn cn0 wcel wa c1 cv caddc cack cfv citco cvv cmpt ackvalsuc1mpt adantr
      co wceq fvoveq1 fveq1d adantl simpr fvexd fvmptd ) ADEZBDEZFZCBGCHZGIQAJK
      LKZKZKZGBGIQUIKZKZDAGIQJKZMUEUNCDUKNRUFCAOPUHBRZUKUMRUGUOGUJULUHBGUIISTUA
      UEUFUBUGGULUCUD $.
  $}

  ${
    $d f i j n $.
    $( The Ackermann function at 0.  (Contributed by AV, 2-May-2024.) $)
    ackval0 $p |- ( Ack ` 0 ) = ( n e. NN0 |-> ( n + 1 ) ) $=
      ( vf vj vi cc0 cack cfv cvv cn0 c1 cv caddc citco cmpt cmpo wceq cif wcel
      co ax-mp cseq df-ack fveq1i cz 0z seq1 0nn0 iftrue eqid nn0ex mptex fvmpt
      3eqtri ) EFGEBCHHAIJAKJLSZBKMGGGNOZDIDKZEPZAIUNNZUPQZNZEUAZGZEUTGZUREFVAB
      DCAUBUCEUDRVBVCPUEUOUTEUFTEIRVCURPUGDEUSURIUTUQURUPUHUTUIAIUNUJUKULTUM $.

    $( The Ackermann function at 1.  (Contributed by AV, 4-May-2024.) $)
    ackval1 $p |- ( Ack ` 1 ) = ( n e. NN0 |-> ( n + 2 ) ) $=
      ( vi c1 cack cfv cc0 caddc co cn0 cv cmpt c2 wcel wceq 1nn0 nn0cn syl a1i
      cc 3eqtrd citco 1e0p1 fveq2i 0nn0 ackvalsuc1mpt ax-mp peano2nn0 itcovalpc
      cmul ackval0 sylancl mullidd oveq2d mpteq2dv eqtrd fveq1d cvv eqidd oveq1
      adantl ovexd fvmptd peano2cn addcomd addassd 1p1e2 oveq2i mpteq2ia 3eqtri
      1cnd ) CDEFCGHZDEZAICAJZCGHZFDEZUAEEZEZKZAIVMLGHZKCVKDUBUCFIMVLVRNUDAFUEU
      FAIVQVSVMIMZVQCBIBJZVNGHZKZECVNGHZVSVTCVPWCVTVPBIWACVNUIHZGHZKZWCVTVNIMZC
      IMZVPWGNVMUGZOCBVOVNBUJUHUKVTBIWFWBVTWEVNWAGVTVNVTWHVNSMZWJVNPQULUMUNUOUP
      VTBCWBWDIWCUQVTWCURWACNWBWDNVTWACVNGUSUTWIVTORVTCVNGVAVBVTWDVNCGHVMCCGHZG
      HZVSVTCVNVTVJZVTVMSMWKVMPZVMVCQVDVTVMCCWOWNWNVEWMVSNVTWLLVMGVFVGRTTVHVI
      $.

    $( The Ackermann function at 2.  (Contributed by AV, 4-May-2024.) $)
    ackval2 $p |- ( Ack ` 2 ) = ( n e. NN0 |-> ( ( 2 x. n ) + 3 ) ) $=
      ( vi c2 cack cfv c1 caddc co cn0 cv citco cmpt cmul c3 wcel wceq 1nn0 a1i
      mulcld 3eqtrd df-2 fveq2i ackvalsuc1mpt ax-mp peano2nn0 ackval1 itcovalpc
      2nn0 sylancl fveq1d cvv eqidd oveq1 adantl ovexd fvmptd cc nn0cn peano2cn
      1cnd 2cnd addcomd id adddid oveq1d addassd 2t1e2 oveq1i 2p1e3 eqtri eqtrd
      oveq2d syl mpteq2ia 3eqtri ) CDEFFGHZDEZAIFAJZFGHZFDEZKEEZEZLZAICVRMHZNGH
      ZLCVPDUAUBFIOZVQWCPQAFUCUDAIWBWEVRIOZWBFBIBJZCVSMHZGHZLZEFWIGHZWEWGFWAWKW
      GVSIOCIOWAWKPVRUEUHCBVTVSBUFUGUIUJWGBFWJWLIWKUKWGWKULWHFPWJWLPWGWHFWIGUMU
      NWFWGQRWGFWIGUOUPWGVRUQOZWLWEPVRURWMWLWIFGHWDCFMHZGHZFGHZWEWMFWIWMUTZWMCV
      SWMVAZVRUSSVBWMWIWOFGWMCVRFWRWMVCZWQVDVEWMWPWDWNFGHZGHWEWMWDWNFWMCVRWRWSS
      WMCFWRWQSWQVFWMWTNWDGWTNPWMWTCFGHNWNCFGVGVHVIVJRVLVKTVMTVNVO $.

    $( The Ackermann function at 3.  (Contributed by AV, 7-May-2024.) $)
    ackval3 $p |- ( Ack ` 3 ) = ( n e. NN0
                                     |-> ( ( 2 ^ ( n + 3 ) ) - 3 ) ) $=
      ( vi c3 cack cfv c2 c1 caddc co cn0 cv cmpt cexp cmin wcel wceq c4 oveq1d
      cmul a1i citco df-3 fveq2i 2nn0 ackvalsuc1mpt peano2nn0 ackval2 itcovalt2
      ax-mp 3nn0 sylancl fveq1d eqidd oveq1 ax-1cn 3p1e4 addcomli eqtrdi adantl
      cvv 3cn 1nn0 ovexd fvmptd sq2 eqcomi 2cnd expaddd nn0cn 1cnd add12d 2p1e3
      oveq2i oveq2d 3eqtr2d 3eqtrd mpteq2ia 3eqtri ) CDEFGHIZDEZAJGAKZGHIZFDEZU
      AEEZEZLZAJFWACHIZMIZCNIZLCVSDUBUCFJOZVTWFPUDAFUEUIAJWEWIWAJOZWEGBJBKZCHIZ
      FWBMIZSIZCNIZLZEQWNSIZCNIZWIWKGWDWQWKWBJOCJOWDWQPWAUFZUJCBWCWBBUGUHUKULWK
      BGWPWSJWQUTWKWQUMWLGPZWPWSPWKXAWOWRCNXAWMQWNSXAWMGCHIQWLGCHUNCGQVAUOUPUQU
      RRRUSGJOWKVBTWKWRCNVCVDWKWRWHCNWKWRFFMIZWNSIFFWBHIZMIWHWKQXBWNSQXBPWKXBQV
      EVFTRWKFFWBWKVGZWTWJWKUDTVHWKXCWGFMWKXCWAVSHIWGWKFWAGXDWAVIWKVJVKVSCWAHVL
      VMURVNVORVPVQVR $.
  $}

  ${
    $d M x $.  $d n y $.  $d x y $.
    $( The Ackermann function at any nonnegative integer is an endofunction on
       the nonnegative integers.  (Contributed by AV, 8-May-2024.) $)
    ackendofnn0 $p |- ( M e. NN0 -> ( Ack ` M ) : NN0 --> NN0 ) $=
      ( vx vy vn cn0 cv cack cfv wf cc0 c1 caddc co wceq fveq2 feq1d weq wa cvv
      wcel peano2nn0 fmpti citco cmpt nn0ex a1i simplr adantl itcovalendof 1nn0
      ackval0 ffvelcdm sylancl eqid fmptd ackvalsuc1mpt adantr mpbird ex nn0ind
      ) EEBFZGHZIEEJGHZIEECFZGHZIZEEVDKLMZGHZIZEEAGHZIBCAVAJNEEVBVCVAJGOPBCQEEV
      BVEVAVDGOPVAVGNEEVBVHVAVGGOPVAANEEVBVJVAAGOPDEEDFZKLMZVCDUKVKUAZUBVDETZVF
      VIVNVFRZVIEEDEKVLVEUCHHZHZUDZIVODEVQEVRVOVKETZRZEEVPIKETVQETVTEVEVLSESTVT
      UEUFVNVFVSUGVSVLETVOVMUHUIUJEEKVPULUMVRUNUOVOEEVHVRVNVHVRNVFDVDUPUQPURUSU
      T $.
  $}

  $( The Ackermann function at any nonnegative integer is a function on the
     nonnegative integers.  (Contributed by AV, 4-May-2024.)  (Proof shortened
     by AV, 8-May-2024.) $)
  ackfnnn0 $p |- ( M e. NN0 -> ( Ack ` M ) Fn NN0 ) $=
    ( cn0 wcel cack cfv wf wfn ackendofnn0 ffn syl ) ABCBBADEZFKBGAHBBKIJ $.

  ${
    $d M m $.
    $( The Ackermann function at 0 (for the first argument).  This is the first
       equation of P&eacute;ter's definition of the Ackermann function.
       (Contributed by AV, 4-May-2024.) $)
    ackval0val $p |- ( M e. NN0 -> ( ( Ack ` 0 ) ` M ) = ( M + 1 ) ) $=
      ( vm cn0 wcel cv c1 caddc cc0 cack cfv cmpt wceq ackval0 a1i oveq1 adantl
      co id peano2nn0 fvmptd ) ACDZBABEZFGQZAFGQZCHIJZCUEBCUCKLUABMNUBALUCUDLUA
      UBAFGOPUARAST $.
  $}

  $( The Ackermann function at a successor (of the first argument).  This is
     the second equation of P&eacute;ter's definition of the Ackermann
     function.  (Contributed by AV, 4-May-2024.) $)
  ackvalsuc0val $p |- ( M e. NN0 -> ( ( Ack ` ( M + 1 ) ) ` 0 )
                                    = ( ( Ack ` M ) ` 1 ) ) $=
    ( cn0 wcel cc0 c1 caddc cack cfv citco wceq 0nn0 ackvalsuc1 mpan2 0p1e1 a1i
    co fveq2d wrel cvv eqtrd wfn wfun ackfnnn0 fnfun 3syl fvex itcoval1 sylancl
    funrel fveq1d ) ABCZDAEFPGHHZEDEFPZAGHZIHZHZHZEUNHUKDBCULUQJKADLMUKEUPUNUKU
    PEUOHZUNUKUMEUOUMEJUKNOQUKUNRZUNSCURUNJUKUNBUAUNUBUSAUCBUNUDUNUIUEAGUFUNSUG
    UHTUJT $.

  $( The Ackermann function at the successors.  This is the third equation of
     P&eacute;ter's definition of the Ackermann function.  (Contributed by AV,
     8-May-2024.) $)
  ackvalsucsucval $p |- ( ( M e. NN0 /\ N e. NN0 )
                          -> ( ( Ack ` ( M + 1 ) ) ` ( N + 1 ) )
            = ( ( Ack ` M ) ` ( ( Ack ` ( M + 1 ) ) ` N ) ) ) $=
    ( cn0 wcel wa c1 caddc cack cfv citco wceq ackvalsuc1 ccom cvv itcovalsucov
    co eqidd syl3anc wfn adantr peano2nn0 sylan2 adantl fveq1d crn wss ackfnnn0
    fvexd nn0ex a1i ackendofnn0 simpr itcovalendof ffnd frnd fnco fneq1d mpbird
    wf 1nn0 fvco2 sylancl eqtrd eqcomd fveq2d 3eqtrd ) ACDZBCDZEZBFGPZAFGPHIZIZ
    FVJFGPAHIZJIZIZIZFVJVNIZIZVMIZBVKIZVMIVHVGVJCDZVLVPKBUAZAVJLUBVIVPFVMVQMZIZ
    VSVIFVOWCVIVMNDZWAVQVQKVOWCKVIAHUHZVHWAVGWBUCVIVQQVMVQNVJORUDVIVQCSZFCDWDVS
    KVIWGVMBVNIZMZCSZVIVMCSZWHCSWHUECUFWJVGWKVHAUGTVICCWHVICVMBNCNDVIUIUJVGCCVM
    USVHAUKTVGVHULZUMZUNVICCWHWMUOCCVMWHUPRVICVQWIVIWEVHWHWHKVQWIKWFWLVIWHQVMWH
    NBORUQURUTCVMVQFVAVBVCVIVRVTVMVIVTVRABLVDVEVF $.

  $( The Ackermann function at (0,0), (0,1), (0,2).  (Contributed by AV,
     2-May-2024.) $)
  ackval0012 $p |- <. ( ( Ack ` 0 ) ` 0 ) ,
                      ( ( Ack ` 0 ) ` 1 ) ,
                      ( ( Ack ` 0 ) ` 2 ) >. = <. 1 , 2 , 3 >. $=
    ( vn cc0 cack cfv cn0 cv c1 caddc co cmpt wceq c2 cotp ackval0 oveq1 eqtrdi
    c3 wcel a1i fvmptd3 0p1e1 0nn0 1nn0 1p1e2 2nn0 2p1e3 3nn0 oteq123d ax-mp )
    BCDZAEAFZGHIZJKZBUJDZGUJDZLUJDZMGLQMKANZUMUNGUOLUPQUMABULGEUJEUQUKBKULBGHIG
    UKBGHOUAPBERUMUBSGERUMUCSZTUMAGULLEUJEUQUKGKULGGHILUKGGHOUDPURLERUMUESZTUMA
    LULQEUJEUQUKLKULLGHIQUKLGHOUFPUSQERUMUGSTUHUI $.

  $( The Ackermann function at (1,0), (1,1), (1,2).  (Contributed by AV,
     4-May-2024.) $)
  ackval1012 $p |- <. ( ( Ack ` 1 ) ` 0 ) ,
                      ( ( Ack ` 1 ) ` 1 ) ,
                      ( ( Ack ` 1 ) ` 2 ) >. = <. 2 , 3 , 4 >. $=
    ( vn c1 cack cfv cn0 cv c2 caddc co cmpt wceq cc0 cotp c3 oveq1 eqtrdi wcel
    c4 a1i fvmptd3 ackval1 2cn addlidi 0nn0 2nn0 1p2e3 1nn0 3nn0 2p2e4 oteq123d
    4nn0 ax-mp ) BCDZAEAFZGHIZJKZLUMDZBUMDZGUMDZMGNRMKAUAZUPUQGURNUSRUPALUOGEUM
    EUTUNLKUOLGHIGUNLGHOGUBUCPLEQUPUDSGEQUPUESZTUPABUONEUMEUTUNBKUOBGHINUNBGHOU
    FPBEQUPUGSNEQUPUHSTUPAGUOREUMEUTUNGKUOGGHIRUNGGHOUIPVAREQUPUKSTUJUL $.

  $( The Ackermann function at (2,0), (2,1), (2,2).  (Contributed by AV,
     4-May-2024.) $)
  ackval2012 $p |- <. ( ( Ack ` 2 ) ` 0 ) ,
                      ( ( Ack ` 2 ) ` 1 ) ,
                      ( ( Ack ` 2 ) ` 2 ) >. = <. 3 , 5 , 7 >. $=
    ( vn c2 cfv cn0 cmul co c3 caddc cc0 c1 c5 oveq2 oveq1d oveq1i eqtri eqtrdi
    wceq c7 wcel a1i cack cmpt cotp ackval2 2t0e0 3cn addlidi 0nn0 3nn0 fvmptd3
    cv 2t1e2 2cn 3p2e5 addcomli 1nn0 5nn0 2t2e4 4p3e7 2nn0 7nn0 oteq123d ax-mp
    c4 ) BUACZADBAUKZEFZGHFZUBQZIVECZJVECZBVECZUCGKRUCQAUDZVIVJGVKKVLRVIAIVHGDV
    EDVMVFIQZVHBIEFZGHFZGVNVGVOGHVFIBELMVPIGHFGVOIGHUENGUFUGOPIDSVIUHTGDSVIUITU
    JVIAJVHKDVEDVMVFJQZVHBJEFZGHFZKVQVGVRGHVFJBELMVSBGHFKVRBGHULNGBKUFUMUNUOOPJ
    DSVIUPTKDSVIUQTUJVIABVHRDVEDVMVFBQZVHBBEFZGHFZRVTVGWAGHVFBBELMWBVDGHFRWAVDG
    HURNUSOPBDSVIUTTRDSVIVATUJVBVC $.

  $( The Ackermann function at (3,0), (3,1), (3,2).  (Contributed by AV,
     7-May-2024.) $)
  ackval3012 $p |- <. ( ( Ack ` 3 ) ` 0 ) ,
                      ( ( Ack ` 3 ) ` 1 ) ,
                      ( ( Ack ` 3 ) ` 2 ) >. = <. 5 , ; 1 3 , ; 2 9 >. $=
    ( vn c3 cfv cn0 c2 caddc co cexp cmin wceq cc0 c1 c5 cdc 3cn eqtrdi c8 wcel
    a1i c4 cack cv cmpt cotp ackval3 oveq1 addlidi oveq2d oveq1d cu2 oveq1i 5cn
    c9 5p3e8 eqcomi mvrraddi eqtri 0nn0 5nn0 fvmptd3 ax-1cn 3p1e4 addcomli 1nn0
    2exp4 3nn0 deccl nn0cni eqid 3p3e6 decaddi 2cn 3p2e5 2exp5 2nn0 9nn0 9p3e12
    c6 2p1e3 decaddci oteq123d ax-mp ) BUACZADEAUBZBFGZHGZBIGZUCJZKWCCZLWCCZEWC
    CZUDMLBNZEUMNZUDJAUEZWHWIMWJWLWKWMWHAKWGMDWCDWNWDKJZWGEBHGZBIGZMWOWFWPBIWOW
    EBEHWOWEKBFGBWDKBFUFBOUGPUHUIWQQBIGMWPQBIUJUKQMBULOMBFGQUNUOUPUQPKDRWHURSMD
    RWHUSSUTWHALWGWLDWCDWNWDLJZWGETHGZBIGZWLWRWFWSBIWRWETEHWRWELBFGTWDLBFUFBLTO
    VAVBVCPUHUIWTLVRNZBIGWLWSXABIVEUKXAWLBWLLBVDVFVGZVHOWLBFGXALBVRWLBVDVFVFWLV
    IVJVKUOUPUQPLDRWHVDSWLDRWHXBSUTWHAEWGWMDWCDWNWDEJZWGEMHGZBIGZWMXCWFXDBIXCWE
    MEHXCWEEBFGMWDEBFUFBEMOVLVMVCPUHUIXEBENZBIGWMXDXFBIVNUKXFWMBWMEUMVOVPVGZVHO
    WMBFGXFEUMEBWMBVOVPVFWMVIVSVOVQVTUOUPUQPEDRWHVOSWMDRWHXGSUTWAWB $.

  $( The Ackermann function at (4,0).  (Contributed by AV, 9-May-2024.) $)
  ackval40 $p |- ( ( Ack ` 4 ) ` 0 ) = ; 1 3 $=
    ( cc0 c4 cack cfv c3 c1 caddc co cdc df-4 fveq2i fveq1i cn0 wcel wceq ax-mp
    c2 cotp c5 fvex 3nn0 ackvalsuc0val c9 ackval3012 otth simp2bi 3eqtri ) ABCD
    ZDAEFGHZCDZDZFECDZDZFEIZAUHUJBUICJKLEMNUKUMOUAEUBPAULDZUMQULDZRSUNQUCIZROZU
    MUNOZUDURUOSOUSUPUQOUOUMSUNUPUQAULTFULTQULTUEUFPUG $.

  $( The Ackermann function at (4,1).  (Contributed by AV, 9-May-2024.) $)
  ackval41a $p |- ( ( Ack ` 4 ) ` 1 ) = ( ( 2 ^ ; 1 6 ) - 3 ) $=
    ( vn c1 c4 cack cfv cc0 caddc co c3 cdc cexp cmin fveq2i cn0 wcel wceq 3nn0
    c2 c6 eqtri df-4 1e0p1 fveq12i 0nn0 ackvalsucsucval mp2an 3p1e4 fveq1i 1nn0
    ackval40 deccl oveq1 oveq2d oveq1d eqid 3p3e6 decaddi oveq2i oveq1i ackval3
    cv eqtrdi ovex fvmpt ax-mp ) BCDEZEFBGHZIBGHZDEZEZRBSJZKHZILHZBVGVFVICVHDUA
    MUBUCVJFVIEZIDEZEZVMINOFNOVJVPPQUDIFUEUFVPBIJZVOEZVMVNVQVOVNFVFEVQFVIVFVHCD
    UGMUHUJTMVQNOVRVMPBIUIQUKAVQRAVAZIGHZKHZILHZVMNVOVSVQPZWBRVQIGHZKHZILHVMWCW
    AWEILWCVTWDRKVSVQIGULUMUNWEVLILWDVKRKBISVQIUIQQVQUOUPUQURUSVBAUTVLILVCVDVET
    TT $.

  $( The Ackermann function at (4,1).  (Contributed by AV, 9-May-2024.) $)
  ackval41 $p |- ( ( Ack ` 4 ) ` 1 ) = ; ; ; ; 6 5 5 3 3 $=
    ( c1 c4 cack cfv c2 c6 cdc cexp co c3 cmin ackval41a 6nn0 5nn0 deccl 2exp16
    c5 3nn0 3p1e4 3cn eqid decsuc gbpart6 mvrraddi decsubi eqtri ) ABCDDEAFGHIZ
    JKIFQGZQGZJGZJGLUJFJUIBGUGJUIJUHQFQMNONOZROMRPUIJBUJUKRSUJUAUBFJJTTUCUDUEUF
    $.

  $( The Ackermann function at (4,2).  (Contributed by AV, 9-May-2024.) $)
  ackval42 $p |- ( ( Ack ` 4 ) ` 2 ) = ( ( 2 ^ ; ; ; ; 6 5 5 3 6 ) - 3 ) $=
    ( vn c2 c4 cack cfv c1 caddc co c3 cdc cexp cmin fveq2i cn0 wcel wceq mp2an
    c6 cle wbr c5 df-4 df-2 fveq12i 3nn0 ackvalsucsucval 3p1e4 fveq1i ackval41a
    1nn0 eqtri cc 2cn 6nn0 deccl expcl 3cn wa cvv ackval3 oveq1 npcan sylan9eqr
    cv oveq2d oveq1d 3re 4re 3lt4 ltleii sq2 breqtrri cr cuz 2re 1le2 nn0zi 1nn
    cz 2nn0 c9 2lt9 declei 2z eluz1i mpbir2an leexp2a mp3an 4nn0 eqeltri nn0rei
    9re nn0expcli letri wb nn0sub a1i ovexd fvmptd2 2exp16 oveq2i oveq1i 3eqtri
    mpbi ) BCDEZEFFGHZIFGHZDEZEZFXHEZIDEZEZBRUAJUAJIJRJZKHZILHZBXFXEXHCXGDUBMUC
    UDINOZFNOXIXLPUEUJIFUFQXLBFRJZKHZILHZXKEZBXRKHZILHZXOXJXSXKXJFXEEXSFXHXEXGC
    DUGMUHUIUKMXRULOZIULOZXTYBPBULOXQNOYCUMFRUJUNUOZBXQUPQUQYCYDURZAXSBAVDZIGHZ
    KHZILHYBNXKUSAUTYFYGXSPZURZYIYAILYKYHXRBKYJYFYHXSIGHXRYGXSIGVAXRIVBVCVEVFXS
    NOZYFIXRSTZYLIBBKHZSTYNXRSTZYMICYNSICVGVHVIVJVKVLBVMOFBSTXQBVNEOZYOVOVPYPXQ
    VSOBXQSTXQYEVQFRBVRUNVTBWAVOWLWBVJWCBXQWDWEWFBBXQWGWHIYNXRVGYNYNCNVKWIWJWKX
    RBXQVTYEWMZWKWNQXPXRNOYMYLWOUEYQIXRWPQXDWQYFYAILWRWSQYAXNILXRXMBKWTXAXBXCXC
    $.

  $( The Ackermann function at (4,2), expressed with powers of 2.  (Contributed
     by AV, 9-May-2024.) $)
  ackval42a $p |- ( ( Ack ` 4 ) ` 2 )
                  = ( ( 2 ^ ( 2 ^ ( 2 ^ ( 2 ^ 2 ) ) ) ) - 3 ) $=
    ( c2 c4 cack cfv c6 c5 cdc c3 cexp co cmin ackval42 sq2 oveq2i 2exp4 2exp16
    c1 eqtri eqtr2i oveq1i ) ABCDDAEFGFGHGEGZIJZHKJAAAAAIJZIJZIJZIJZHKJLUBUFHKU
    AUEAIUEAQEGZIJUAUDUGAIUDABIJUGUCBAIMNORNPSNTR $.

  $( The Ackermann function at (5,0).  (Contributed by AV, 9-May-2024.) $)
  ackval50 $p |- ( ( Ack ` 5 ) ` 0 ) = ; ; ; ; 6 5 5 3 3 $=
    ( cc0 c5 cack cfv c4 c1 caddc co c6 cdc c3 df-5 fveq2i fveq1i cn0 wcel wceq
    4nn0 ackvalsuc0val ax-mp ackval41 3eqtri ) ABCDZDAEFGHZCDZDZFECDDZIBJBJKJKJ
    AUCUEBUDCLMNEOPUFUGQRESTUAUB $.
