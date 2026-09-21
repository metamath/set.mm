$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Alexander van der Vekens
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  General auxiliary theorems (1)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Unordered and ordered pairs - extension for singletons
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x $.  $d B x $.
    $( If a class with one element is not a singleton, there is at least
       another element in this class.  (Contributed by AV, 6-Mar-2025.) $)
    n0nsn2el $p |- ( ( A e. B /\ B =/= { A } ) -> E. x e. B x =/= A ) $=
      ( wcel csn wne cv wrex wceq wn wral c0 wb ne0i eqsn syl biimprd con3d nne
      df-ne bicomi ralbii ralnex bitri con2bii 3imtr4g imp ) BCDZCBEZFZAGZBFZAC
      HZUHCUIIZJUKBIZACKZJUJUMUHUPUNUHUNUPUHCLFUNUPMCBNACBOPQRCUITUPUMUPULJZACK
      UMJUOUQACUQUOUKBSUAUBULACUCUDUEUFUG $.
  $}

  ${
    $d x y z $.
    $( There is a unique element of a singleton which is equal to another
       singleton.  (Contributed by AV, 24-Aug-2022.) $)
    eusnsn $p |- E! x { x } = { y } $=
      ( vz csn wceq weu weq wal wex equequ2 bibi2d albidv cvv sneqbg elv ax-gen
      cv wb speivw eu6 mpbir ) AQZDBQZDEZAFUDACGZRZAHZCIUGUDABGZRZAHCBCBGZUFUIA
      UJUEUHUDCBAJKLUIAUIAUBUCMNOPSUDACTUA $.
  $}

  ${
    $d x y $.
    $( If the class abstraction ` { x | ph } ` associated with the wff ` ph `
       is a singleton, the wff is true for the singleton element.  (Contributed
       by AV, 24-Aug-2022.) $)
    absnsb $p |- ( { x | ph } = { y } -> [ y / x ] ph ) $=
      ( cv cab wcel csn wb wal weq wi wceq wsb velsn bibi12i biimpr sylbi alimi
      abid nfab1 nfcv cleqf sb6 3imtr4i ) BDZABEZFZUECDZGZFZHZBIBCJZAKZBIUFUILA
      BCMUKUMBUKAULHUMUGAUJULABSBUHNOAULPQRBUFUIABTBUIUAUBABCUCUD $.
  $}

  ${
    $d x y $.  $d ph y $.
    $( Another way to express existential uniqueness of a wff ` ph ` : its
       associated class abstraction ` { x | ph } ` is a singleton.  Variant of
       ~ euabsn2 using existential uniqueness for the singleton element instead
       of existence only.  (Contributed by AV, 24-Aug-2022.) $)
    euabsneu $p |- ( E! x ph <-> E! y { x | ph } = { y } ) $=
      ( cab cv csn wceq wex wmo wa weu mosneq eqcom mobii biantru euabsn2 df-eu
      mpbi 3bitr4i ) ABDZCEFZGZCHZUCUBCIZJABKUBCKUDUCUATGZCIUDCTLUEUBCUATMNROAB
      CPUBCQS $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Unordered and ordered pairs - extension for unordered pairs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( An element of a proper unordered pair is the first element iff it is not
     the second element.  (Contributed by AV, 18-Jun-2020.) $)
  elprneb $p |- ( ( A e. { B , C } /\ B =/= C ) -> ( A = B <-> A =/= C ) ) $=
    ( cpr wcel wne wceq wb wo wi elpri neeq1 eqcoms pm5.1 ex sylbid neeq2 wa wn
    nesym sylan2b necon2abid sylbird jaoi syl imp ) ABCDEZBCFZABGZACFZHZUGUIACG
    ZIUHUKJZABCKUIUMULUIUHUJUKUHUJHBABACLMUIUJUKUIUJNOPULUHBAFZUKACBQULUNUKULUN
    RUIACUNULUISZULUOHBATULUONUAUBOUCUDUEUF $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Unordered and ordered pairs - extension for ordered pairs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Equality for ordered pairs implies equality of unordered pairs with the
     same elements.  (Contributed by AV, 9-Jul-2023.) $)
  oppr $p |- ( ( A e. V /\ B e. W )
                -> ( <. A , B >. = <. C , D >. -> { A , B } = { C , D } ) ) $=
    ( wcel wa cop wceq cpr opthg preq12 biimtrdi ) AEGBFGHABICDIJACJBDJHABKCDKJ
    ABCDEFLABCDMN $.

  $( Equality for unordered pairs corresponds to equality of unordered pairs
     with the same elements.  (Contributed by AV, 9-Jul-2023.) $)
  opprb $p |- ( ( ( A e. V /\ B e. W ) /\ ( C e. X /\ D e. Y ) )
            -> ( { A , B } = { C , D } <-> ( <. A , B >. = <. C , D >.
                                          \/ <. A , B >. = <. D , C >. ) ) ) $=
    ( wcel wa cpr wceq wo cop preq12bg wb opthg adantr orbi12d bitr4d ) AEIBFIJ
    ZCGIDHIJZJZABKCDKLACLBDLJZADLBCLJZMABNZCDNLZUFDCNLZMABCDEFGHOUCUGUDUHUEUAUG
    UDPUBABCDEFQRUAUHUEPUBABDCEFQRST $.

  ${
    $d A x y $.  $d B x y $.  $d a b x y $.  $d ph x y $.
    $( Lemma 1 for ~ or2expropbi and ~ ich2exprop .  (Contributed by AV,
       16-Jul-2023.) $)
    or2expropbilem1 $p |- ( ( A e. X /\ B e. X ) -> ( ( A = a /\ B = b )
                            -> ( ph -> E. x E. y ( <. A , B >. = <. x , y >.
                                    /\ [. y / b ]. [. x / a ]. ph ) ) ) ) $=
      ( wcel wa cv wceq cop wsbc wex cvv vex sbcid adantl opeq12 pm3.2i anim1ci
      a1i adantr sylbbr anim12ci nfv wb eqeq2d dfsbcq sbcbidv sylan9bbr anbi12d
      weq spc2ed sylc exp31 com23 ) DFIEFIJZADGKZLEHKZLJZDEMZBKZCKZMZLZAGVDNZHV
      ENZJZCOBOZUSAVBVKUSAJZVBJAUTPIZVAPIZJZJZVCUTVAMZLZAGUTNZHVANZJZVKVLVPVBUS
      VOAVOUSVMVNGQHQUAUCUBUDVLVTVBVRAVTUSVTVSAVSHRAGRUESDEUTVATUFAVJWABCUTVAPP
      WABUGWACUGBGUNZCHUNZJZVJWAUHAWDVGVRVIVTWDVFVQVCVDVEUTVATUIWCVIVHHVANWBVTV
      HHVEVAUJWBVHVSHVAAGVDUTUJUKULUMSUOUPUQUR $.

    $d A a b $.  $d B a b $.
    $( Lemma 2 for ~ or2expropbi and ~ ich2exprop .  (Contributed by AV,
       16-Jul-2023.) $)
    or2expropbilem2 $p |- ( E. a E. b ( <. A , B >. = <. a , b >. /\ ph )
                           <-> E. x E. y ( <. A , B >. = <. x , y >.
                                           /\ [. y / b ]. [. x / a ]. ph ) ) $=
      ( cop cv wceq wa wsbc nfv nfcv nfsbc1v nfsbcw nfan weq opeq12 sbceq1a
      eqeq2d sylan9bb anbi12d cbvex2v ) DEHZFIZGIZHZJZAKZUEBIZCIZHZJZAFUKLZGULL
      ZKFGBCUJBMUJCMUNUPFUNFMUOFGULFULNAFUKOPQUNUPGUNGMUOGULOQFBRZGCRZKZUIUNAUP
      USUHUMUEUFUGUKULSUAUQAUOURUPAFUKTUOGULTUBUCUD $.

    $d R a b x y $.  $d V a b $.  $d X a b $.  $d ph x y $.
    $( If two classes are strictly ordered, there is an ordered pair of both
       classes fulfilling a wff iff there is an unordered pair of both classes
       fulfilling the wff.  (Contributed by AV, 26-Aug-2023.) $)
    or2expropbi $p |- ( ( ( X e. V /\ R Or X )
                          /\ ( A e. X /\ B e. X /\ A R B ) )
         -> ( E. a E. b ( { A , B } = { a , b } /\ ( a R b /\ ph ) )
          <-> E. a E. b ( <. A , B >. = <. a , b >. /\ ( a R b /\ ph ) ) ) ) $=
      ( vx vy wcel wa cv wceq wex nfv nfex wi cvv adantl wor wbr w3a cpr nfsbcw
      cop wsbc nfcv nfsbc1v nfan wo wb preq12bg mpanr12 3adant3 or2expropbilem1
      vex breq12 ancoms wn soasym expd 3imp2 pm2.21d adantr sylbird impd sylbid
      ex jaod exlimd or2expropbilem2 imbitrrdi oppr anim1d 2eximdv impbid ) FEK
      ZFDUAZLZBFKZCFKZBCDUBZUCZLZBCUDGMZHMZUDNZWFWGDUBZALZLZHOZGOZBCUFZWFWGUFNZ
      WJLZHOGOZWEWMWNIMZJMZUFNZWJGWRUGZHWSUGZLZJOZIOZWQWEWLXEGWEGPXDGIXCGJWTXBG
      WTGPXAGHWSGWSUHWJGWRUIUEUJQQWEWKXEHWEHPXDHIXCHJWTXBHWTHPXAHWSUIUJQQWEWHWJ
      XEWEWHBWFNCWGNLZBWGNZCWFNZLZUKZWJXERZWDWHXJULZVTWAWBXLWCWAWBLZWFSKWGSKXLG
      UQHUQBCWFWGFFSSUMUNUOTWEXFXKXIWDXFXKRZVTWAWBXNWCWJIJBCFGHUPUOTWEXIXKWEXIL
      ZWIAXEXOWICBDUBZAXERZXIXPWIULZWEXHXGXRCWFBWGDURUSTWEXPXQRXIWEXPXQVTWAWBWC
      XPUTZVTWAWBWCXSRZVSXMXTRVRVSXMXTFDBCVAVITVBVCVDVEVFVGVIVJVHVGVKVKWJIJBCGH
      VLVMWDWQWMRZVTWAWBYAWCXMWPWKGHXMWOWHWJBCWFWGFFVNVOVPUOTVQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Relations - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A b $.  $d R b $.
    $( If there is a unique set which is related to a class, then the class
       must be a set.  (Contributed by AV, 25-Aug-2022.) $)
    eubrv $p |- ( E! b A R b -> A e. _V ) $=
      ( cvv wcel cv wbr weu brprcneu con4i ) ADEACFBGCHCABIJ $.

    $( If there is a unique set which is related to a class, then the class is
       an element of the domain of the relation.  (Contributed by AV,
       25-Aug-2022.) $)
    eubrdm $p |- ( E! b A R b -> A e. dom R ) $=
      ( cv wbr weu cvv wcel cio cdm eubrv iotaex a1i wsbc iota4 csb wb sbcbr12g
      ax-mp wceq csbconstg csbvargi breq12i sylbb syl breldmg syl3anc ) ACDZBEZ
      CFZAGHUICIZGHZAUKBEZABJHABCKULUJUICLZMUJUICUKNZUMUICOUOCUKAPZCUKUHPZBEZUM
      ULUOURQUNCUKAUHBGRSUPAUQUKBULUPATUNCUKAGUASCUKUNUBUCUDUEAUKGGBUFUG $.
  $}

  $( Element of the domain of a restriction to a singleton.  (Contributed by
     Alexander van der Vekens, 2-Jul-2017.) $)
  eldmressn $p |- ( B e. dom ( F |` { A } ) -> B = A ) $=
    ( wceq csn cdm cin cres wcel wa elin elsni adantr sylbi dmres eleq2s ) BADZ
    BAEZCFZGZCRHFBTIBRIZBSIZJQBRSKUAQUBBALMNCROP $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Definite description binder (inverted iota) - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y $.
    $( Example for a defined iota being the empty set, i.e., ` A. y x C_ y ` is
       a wff satisfied by a unique value ` x ` , namely ` x = (/) ` (the empty
       set is the one and only set which is a subset of every set).
       (Contributed by AV, 24-Aug-2022.) $)
    iota0def $p |- ( iota x A. y x C_ y ) = (/) $=
      ( c0 cvv wcel cv wss wal cio wceq 0ex wb wa al0ssb a1i iota5 mp2an ) CDEZ
      RAFZBFGBHZAICJKKRTACDTSCJLRRMBSNOPQ $.

    $( Example for an undefined iota being the empty set, i.e., ` A. y y e. x `
       is a wff not satisfied by a (unique) value ` x ` (there is no set, and
       therefore certainly no unique set, which contains every set).
       (Contributed by AV, 24-Aug-2022.) $)
    iota0ndef $p |- ( iota x A. y y e. x ) = (/) $=
      ( wel wal weu wn cio c0 wceq wex wmo wa intnanr df-eu mtbir iotanul ax-mp
      nalset ) BACBDZAEZFSAGHITSAJZSAKZLUAUBABRMSANOSAPQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Functions - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( If a function's value at an argument is the universal class (which can
     never be the case because of ~ fvex ), the function's value at this
     argument is any set (especially the empty set).  In short "If a function's
     value is a proper class, it is a set", which sounds strange/contradictory,
     but which is a consequence of that a contradiction implies anything (see
     ~ pm2.21i ).  (Contributed by Alexander van der Vekens, 26-May-2017.) $)
  fveqvfvv $p |- ( ( F ` A ) = _V -> ( F ` A ) = B ) $=
    ( cfv wceq cvv wcel wi fvex eleq1a ax-mp vprc pm2.21i syl eqcoms ) ACDZBEZF
    PFPEZFFGZQPFGRSHACIPFFJKSQLMNO $.

  $( Composition of two functions, similar to ~ fnco .  (Contributed by
     Alexander van der Vekens, 25-Jul-2017.) $)
  fnresfnco $p |- ( ( ( F |` ran G ) Fn ran G /\ G Fn B )
                    -> ( F o. G ) Fn B ) $=
    ( crn cres wfn wa ccom wfun cdm wceq fnfun funresfunco syl2an wss cin dmres
    fndm eqeq1i syl dfss2 sylbb2 adantr dmcosseq adantl eqtrd df-fn sylanbrc )
    BCDZEZUIFZCAFZGZBCHZIZUNJZAKUNAFUKUJICIUOULUIUJLACLBCMNUMUPCJZAUMUIBJZOZUPU
    QKUKUSULUKUJJZUIKZUSUIUJRVAUIURPZUIKUSUTVBUIBUIQSUIURUAUBTUCBCUDTULUQAKUKAC
    RUEUFUNAUGUH $.

  $( A composition restricted to a singleton is a function under certain
     conditions.  (Contributed by Alexander van der Vekens, 25-Jul-2017.) $)
  funcoressn $p |- ( ( ( ( G ` X ) e. dom F /\ Fun ( F |` { ( G ` X ) } ) )
                       /\ ( G Fn A /\ X e. A ) )
                     -> Fun ( ( F o. G ) |` { X } ) ) $=
    ( cfv cdm wcel csn cres wfun wa wfn ccom crn wceq syl adantr adantl fnfun
    wi dmressnsn df-fn simplbi2com imp cima fnsnfv df-ima reseq2d fneq12d mpbid
    eqtrdi funres funfnd fnresfnco syl2anc resco funeqi sylibr ) DCEZBFGZBUSHZI
    ZJZKZCALZDAGZKZKZBCDHZIZMZJZBCMVIIZJVHVKVJFZLZVLVHBVJNZIZVPLZVJVNLZVOVHVBVA
    LZVRVDVTVGUTVCVTUTVBFVAOZVCVTTUSBUAVTVCWAVBVAUBUCPUDQVHVAVPVBVQVHVAVPBVHVAC
    VIUEZVPVGVAWBOVDADCUFRCVIUGUKZUHWCUIUJVGVSVDVEVSVFVECJZVSACSWDVJVICULUMPQRV
    NBVJUNUOVNVKSPVMVKBCVIUPUQUR $.

  ${
    $d A x y $.  $d F x y $.  $d G x y $.  $d X x y $.  $d A z $.  $d F z $.
    $d G z $.  $d X z $.  $d y z $.
    $( A restriction to a singleton with a function value is a function under
       certain conditions.  (Contributed by Alexander van der Vekens,
       25-Jul-2017.)  (Proof shortened by Peter Mazsa, 2-Oct-2022.) $)
    funressnfv $p |- ( ( ( X e. dom ( F o. G ) /\ Fun ( ( F o. G ) |` { X } ) )
                         /\ ( G Fn A /\ X e. A ) )
                       -> Fun ( F |` { ( G ` X ) } ) ) $=
      ( vx vy vz cdm wcel wfun wa cv wbr wmo wi wceq adantl wb eqcoms ex relres
      ccom csn cres wfn cfv wrel wral dmfco biimpd funfni dmressnsn eleq2 velsn
      a1i dffun7 snidg adantr mpbid wex fvex isseti eqcom fnbrfvb breq1 biimpcd
      bitrid anim12ii eximdv mpi cvv simpr vex sylancl mpbird biantrurd bitr4id
      brcog brresi ad2antlr sylibd moimdv com23 rspcimdv com13 mpcom imp31 snid
      simplbiim biantrur mobidv bitr2di sylbi biimtrdi syl syl6com a1d ralrimiv
      pm2.43i sylanbrc ) DBCUBZHZIZXADUCZUDZJZKCAUEZDAIZKZKZBDCUFZUCZUDZUGZELZF
      LZXMMZFNZEXMHZUHXMJXNXJBXLUAUOXJXREXSXJXOXSIZXROZXCXFXIXJYAOZXCXIYBOXFXIX
      CXKBHIZYBXCYCOADCCJDCHIKXCYCDBCUIUJUKYCXSXLPZYBXKBULYDXTXJXRYDXTXOXLIZXJX
      ROZXSXLXOUMYEXOXKPZYFEXKUNYGXJXRYGXJKZXKXLIZXKXPBMZKZFNZXRXJYLYGXJYJFNZYL
      XCXFXIYMXEHZXDPZXCXFXIYMOZODXAULXFXCYOYPXFXEUGXOXPXEMZFNZEYNUHZXCYOYPOOEF
      XEUPYOXCYSYPYOXCYSYPOYOXCKZYRYPEDYNYTDXDIZDYNIZXCUUAYODXBUQQYOUUAUUBRZXCU
      UCXDYNXDYNDUMSURUSYTXODPZKZXIYRYMUUEXIYRYMOUUEXIKZYJYQFUUFYJDXPXEMZYQXIYJ
      UUGOUUEXIYJUUGXIYJKZUUGDXPXAMZUUHUUIDGLZCMZUUJXPBMZKZGUTZUUHUUJXKPZGUTUUN
      GXKDCVAZVBUUHUUOUUMGXIUUOUUKYJUULXIUUOUUKUUOXKUUJPXIUUKUUJXKVCADUUJCVDVGU
      JUUOYJUULYJUULRXKUUJXKUUJXPBVESVFVHVIVJXIUUIUUNRZYJXIXHXPVKIUUQXGXHVLFVMZ
      GDXPBCAVKVRVNURVOXHUUGUUIRXGYJXHUUGUUAUUIKUUIXDDXPXAUURVSXHUUAUUIDAUQVPVQ
      VTVOTQUUDUUGYQRZYTXIUUSDXODXOXPXEVESVTWAWBTWCWDTWEWIWEWFWGXJYJYKFYJYKRXJY
      IYJXKUUPWHWJUOWKUSQYHYKXQFYGYKXQRXJYGXQXKXPXMMYKXOXKXPXMVEXLXKXPBUURVSWLU
      RWKUSTWMWNWCWOWPWQWGWSWREFXMUPWT $.
  $}

  $( The value of a function ` F ` at a set ` A ` is in the range of the
     function ` F ` if ` A ` is in the domain of the function ` F ` .  It is
     sufficient that ` F ` is a function at ` A ` .  (Contributed by AV,
     1-Sep-2022.) $)
  funressndmfvrn $p |- ( ( Fun ( F |` { A } ) /\ A e. dom F )
                         -> ( F ` A ) e. ran F ) $=
    ( csn cres wfun cdm wcel wa cfv crn simpr fvressn adantl eldmressnsn fvelrn
    wceq sylan2 eqeltrrd fvrnressn sylc ) BACDZEZABFZGZHZUDABIZUAJZGUFBJGUBUDKU
    EAUAIZUFUGUDUHUFPUBBUCALMUDUBAUAFGUHUGGABNAUAOQRBUCAST $.

  ${
    $d y z F $.  $d x y z $.
    $( A function restricted to a singleton has at most one value for the
       singleton element as argument.  (Contributed by AV, 2-Sep-2022.) $)
    funressnvmo $p |- ( Fun ( F |` { x } ) -> E* y x F y ) $=
      ( vz cv csn cres wfun wrel wbr wmo wal dffun6 weq wb breq1 equcoms biimpd
      moimdv spimvw wcel vsnid vex brresi mpbiran biimpri moimi syl simplbiim )
      CAEZFZGZHULIDEZBEZULJZBKZDLZUJUNCJZBKZDBULMUQUJUNULJZBKZUSUPVADADANZUTUOB
      VBUTUOUTUOOADUJUMUNULPQRSTURUTBUTURUTUJUKUAURAUBUKUJUNCBUCUDUEUFUGUHUI $.
  $}

  ${
    $d x y A $.  $d x y F $.  $d y V $.
    $( A function restricted to a singleton has at most one value for the
       singleton element as argument.  (Contributed by AV, 2-Sep-2022.) $)
    funressnmo $p |- ( ( A e. V /\ Fun ( F |` { A } ) ) -> E* y A F y ) $=
      ( vx wcel csn cres wfun cv wbr wmo wceq sneq reseq2d funeqd breq1 imbi12d
      wi mobidv funressnvmo vtoclg imp ) BDFCBGZHZIZBAJZCKZALZCEJZGZHZIZUJUGCKZ
      ALZSUFUISEBDUJBMZUMUFUOUIUPULUEUPUKUDCUJBNOPUPUNUHAUJBUGCQTREACUAUBUC $.
  $}

  ${
    $d y A $.  $d y F $.  $d y V $.
    $( There is exactly one value of a class which is a function restricted to
       a singleton, analogous to ~ funeu . ` A e. _V ` is required because
       otherwise ` E! y A F y ` , see ~ brprcneu .  (Contributed by AV,
       7-Sep-2022.) $)
    funressneu $p |- ( ( ( A e. V /\ B e. W ) /\ Fun ( F |` { A } ) /\ A F B )
                       -> E! y A F y ) $=
      ( wcel wa csn cres wfun wbr w3a cv wex weu cdm simp1l simp1r syl simp3 wi
      breldmg syl3anc eldmg ibi wmo simpl anim1i 3adant3 funressnmo moeu sylib
      mpd ) BEGZCFGZHZDBIJKZBCDLZMZBANDLZAOZVAAPZUTBDQZGZVBUTUOUPUSVEUOUPURUSRU
      OUPURUSSUQURUSUABCEFDUCUDVEVBABDVDUEUFTUTVAAUGZVBVCUBUTUOURHZVFUQURVGUSUQ
      UOURUOUPUHUIUJABDEUKTVAAULUMUN $.
  $}

  $( Conditions for a restriction to be an onto function.  Part of ~ fresf1o .
     (Contributed by AV, 29-Sep-2024.) $)
  fresfo $p |- ( ( Fun F /\ C C_ ran F )
                 -> ( F |` ( `' F " C ) ) : ( `' F " C ) -onto-> C ) $=
    ( wfun crn wss wa cdm ccnv cima wfn funfn birani wceq sseqin2 biimpi eqcomd
    cin adantl eqidd rescnvimafod ) BCZABDZEZFZBGZABHAIZABUABUEJUCBKLUCAUBAQZMU
    AUCUGAUCUGAMAUBNOPRUDUFST $.

  ${
    $d B b f g $.  $d S b f g $.  $d V b g $.
    $( The class of all functions from a (proper) singleton into ` B ` is the
       union of all the singletons of (proper) ordered pairs over the elements
       of ` B ` as second component.  (Contributed by AV, 13-Sep-2024.) $)
    fsetsniunop $p |- ( S e. V -> { f | f : { S } --> B }
                                  = U_ b e. B { { <. S , b >. } } ) $=
      ( vg wcel csn cv wf cab cop ciun wrex wceq cfv wa fsn2g simpl simpr opeq2
      wb sneqd eqeq2d adantl rspcedvd biimtrdi adantr feq1d mpbird ex rexlimdva
      fsnd impbid velsn bicomi rexbii bitrdi vex feq1 elab eliun 3bitr4g eqrdv
      ) BDGZFBHZACIZJZCKZEABEIZLZHZHZMZVEVFAFIZJZVOVMGZEANZVOVIGVOVNGVEVPVOVLOZ
      EANZVRVEVPVTVEVPBVOPZAGZVOBWALZHZOZQZVTBAVODRWFVSWEEWAAWBWESVJWAOZVSWEUBW
      FWGVLWDVOWGVKWCVJWABUAUCUDUEWBWETUFUGVEVSVPEAVEVJAGZQZVSVPWIVSQZVPVFAVLJZ
      WIWKVSWIBVJDAVEWHSVEWHTUMUHWJVFAVOVLWIVSTUIUJUKULUNVSVQEAVQVSFVLUOUPUQURV
      HVPCVOFUSVFAVGVOUTVAEVOAVMVBVCVD $.

    $d B b y $.  $d S y $.
    $( The class of all functions from a (proper) singleton into ` B ` is the
       class of all the singletons of (proper) ordered pairs over the elements
       of ` B ` as second component.  (Contributed by AV, 13-Sep-2024.) $)
    fsetabsnop $p |- ( S e. V -> { f | f : { S } --> B }
                                 = { y | E. b e. B y = { <. S , b >. } } ) $=
      ( wcel csn cv wf cab cop ciun wceq wrex fsetsniunop iunsn eqtrdi ) CEGCHB
      DIJDKFBCFILHZHMAISNFBOAKBCDEFPFABSQR $.
  $}

  ${
    $d A x $.  $d B b x y $.  $d S b x y $.  $d V b x $.
    fsetsnf.a $e |- A = { y | E. b e. B y = { <. S , b >. } } $.
    fsetsnf.f $e |- F = ( x e. B |-> { <. S , x >. } ) $.
    $( The mapping of an element of a class to a singleton function is a
       function.  (Contributed by AV, 13-Sep-2024.) $)
    fsetsnf $p |- ( S e. V -> F : B --> A ) $=
      ( wcel cv cop csn wa wceq wrex simpr weq wb opeq2 sneqd eqeq2d eqidd snex
      adantl rspcedvd eqeq1 rexbidv elab2 sylibr fmptd ) EGKZADEALZMZNZCFUMUNDK
      ZOZUPEHLZMZNZPZHDQZUPCKURVBUPUPPZHUNDUMUQRHASZVBVDTURVEVAUPUPVEUTUOUSUNEU
      AUBUCUFURUPUDUGBLZVAPZHDQVCBUPCUOUEVFUPPVGVBHDVFUPVAUHUIIUJUKJUL $.

    $d B m n x $.  $d F m n $.  $d S m n $.  $d V m n $.
    $( The mapping of an element of a class to a singleton function is an
       injection.  (Contributed by AV, 13-Sep-2024.) $)
    fsetsnf1 $p |- ( S e. V -> F : B -1-1-> A ) $=
      ( vm vn wcel cv wceq weq wa cop csn cvv wf cfv wi wral wf1 fsetsnf wb a1i
      cmpt opeq2 sneqd adantl simpl snex simpr eqeq12d opex sneqr opthg adantrr
      fvmptd biimtrdi syl5 sylbid ralrimivva dff13 sylanbrc ) EGMZDCFUAKNZFUBZL
      NZFUBZOZKLPZUCZLDUDKDUDDCFUEABCDEFGHIJUFVHVOKLDDVHVIDMZVKDMZQZQZVMEVIRZSZ
      EVKRZSZOZVNVRVMWDUGVHVRVJWAVLWCVRAVIEANZRZSZWADFTFADWGUIOVRJUHZAKPZWGWAOV
      RWIWFVTWEVIEUJUKULVPVQUMWATMVRVTUNUHVAVRAVKWGWCDFTWHALPZWGWCOVRWJWFWBWEVK
      EUJUKULVPVQUOWCTMVRWBUNUHVAUPULWDVTWBOZVSVNVTWBEVIUQURVSWKEEOZVNQZVNVHVPW
      KWMUGVQEVIEVKGDUSUTWLVNUOVBVCVDVEKLDCFVFVG $.

    $d A m n $.  $d b m y $.  $d b n $.
    $( The mapping of an element of a class to a singleton function is a
       surjection.  (Contributed by AV, 13-Sep-2024.) $)
    fsetsnfo $p |- ( S e. V -> F : B -onto-> A ) $=
      ( vm vn wcel cv wceq wrex cop csn weq opeq2 wf cfv wral wfo fsetsnf eqeq1
      vex rexbidv elab2 sneqd eqeq2d cbvrexvw wa simpr cvv cmpt a1i adantl snex
      fvmptd eqcomd adantr eqtrd reximdva biimtrid imp ralrimiva dffo3 sylanbrc
      ex ) EGMZDCFUAKNZLNZFUBZOZLDPZKCUCDCFUDABCDEFGHIJUEVKVPKCVKVLCMZVPVQVLEHN
      ZQZRZOZHDPZVKVPBNZVTOZHDPWBBVLCKUGBKSWDWAHDWCVLVTUFUHIUIWBVLEVMQZRZOZLDPV
      KVPWAWGHLDHLSZVTWFVLWHVSWEVRVMETUJUKULVKWGVOLDVKVMDMZUMZWGVOWJWGUMVLWFVNW
      JWGUNWJWFVNOWGWJVNWFWJAVMEANZQZRZWFDFUOFADWMUPOWJJUQALSZWMWFOWJWNWLWEWKVM
      ETUJURVKWIUNWFUOMWJWEUSUQUTVAVBVCVJVDVEVEVFVGLKDCFVHVI $.

    $( The mapping of an element of a class to a singleton function is a
       bijection.  (Contributed by AV, 13-Sep-2024.) $)
    fsetsnf1o $p |- ( S e. V -> F : B -1-1-onto-> A ) $=
      ( wcel wf1 wfo wf1o fsetsnf1 fsetsnfo df-f1o sylanbrc ) EGKDCFLDCFMDCFNAB
      CDEFGHIJOABCDEFGHIJPDCFQR $.
  $}

  ${
    $d B b x y $.  $d B b f $.  $d S b x y $.  $d S f $.  $d V b x $.
    $( The class of all functions from a (proper) singleton into a proper class
       ` B ` is not a set.  (Contributed by AV, 13-Sep-2024.) $)
    fsetsnprcnex $p |- ( ( S e. V /\ B e/ _V )
                         -> { f | f : { S } --> B } e/ _V ) $=
      ( vy vb vx wcel cvv wnel wa csn cv wf cab cop wceq wn eqid df-nel wrex wb
      cmpt fsetsnf1o f1ovv syl notbid 3bitr4g biimpa fsetabsnop adantr neleq12d
      wf1o eqidd mpbird ) BDHZAIJZKZBLACMNCOZIJEMBFMPLQFAUAEOZIJZUPUQVAUPAIHZRU
      TIHZRUQVAUPVBVCUPAUTGABGMPLUCZUMVBVCUBGEUTABVDDFUTSVDSUDAUTVDUEUFUGAITUTI
      TUHUIURUSUTIIUPUSUTQUQEABCDFUJUKURIUNULUO $.
  $}

  ${
    cfsetsnfsetfv.f $e |- F = { f | ( f : A --> B
                                    /\ E. b e. B A. z e. A ( f ` z ) = b ) } $.
    $( The class of constant functions is a subclass of the class of functions.
       (Contributed by AV, 13-Sep-2024.) $)
    cfsetssfset $p |- F C_ { f | f : A --> B } $=
      ( cv wf cfv wceq wral wrex wa cab wss wi ss2ab simpl mpgbir eqsstri ) EBC
      DHZIZAHUBJFHKABLFCMZNZDOZUCDOZGUFUGPUEUCQDUEUCDRUCUDSTUA $.

    $d A a g $.  $d G g $.  $d V g $.  $d X a g $.  $d Y g $.
    cfsetsnfsetfv.g $e |- G = { x | x : { Y } --> B } $.
    cfsetsnfsetfv.h $e |- H = ( g e. G |-> ( a e. A |-> ( g ` Y ) ) ) $.
    $( The function value of the mapping of the class of singleton functions
       into the class of constant functions.  (Contributed by AV,
       13-Sep-2024.) $)
    cfsetsnfsetfv $p |- ( ( A e. V /\ X e. G )
                          -> ( H ` X ) = ( a e. A |-> ( X ` Y ) ) ) $=
      ( wcel cmpt wceq wa cfv cvv a1i fveq1 adantr mpteq2dva adantl simpr simpl
      cv mptexd fvmptd ) CJRZKHRZUAZFKMCLFUKZUBZSZMCLKUBZSZHIUCIFHUSSTUPQUDUQKT
      ZUSVATUPVBMCURUTVBURUTTMUKCRLUQKUEUFUGUHUNUOUIUPMCUTJUNUOUJULUM $.

    $d A b f z $.  $d B x $.  $d B a b f $.  $d F g $.  $d G a b z $.
    $d V a b z $.  $d Y a b f z $.  $d Y g x $.  $d b f g z $.
    $( The mapping of the class of singleton functions into the class of
       constant functions is a function.  (Contributed by AV, 14-Sep-2024.) $)
    cfsetsnfsetf $p |- ( ( A e. V /\ Y e. A ) -> H : G --> F ) $=
      ( wcel wa cv wceq cfv cmpt wral wrex cab cvv simpl adantr mptexd csn feq1
      wf vex elab2 bilani snidg adantl ffvelcdmd fmpttd eqeq2 ralbidv ralrimiva
      wb eqidd rspcedvd jca weq simpr fvexd nfcv nfmpt1 nfeq nfv fvmptdf eqeq1d
      nfan ralbidva rexbidv anbi12d elabd eleqtrrdi fmptd ) CJQZKCQZRZFHLCKFSZU
      AZUBZGIWEWFHQZRZWHCDESZULZBSZWKUAZMSZTZBCUCZMDUDZRZEUEGWJWSCDWHULZWGWOTZB
      CUCZMDUDZREWHUFWJLCWGJWEWCWIWCWDUGUHUIWJWTXCWJLCWGDWJWGDQLSCQWJKUJZDKWFWI
      XDDWFULZWEXDDASZULXEAWFHFUMXDDXFWFUKOUNUOWEKXDQZWIWDXGWCKCUPUQUHURZUHUSWJ
      XBWGWGTZBCUCZMWGDXHWOWGTZXBXJVCWJXKXAXIBCWOWGWGUTVAUQWJXIBCWJWMCQZRWGVDVB
      VEVFWKWHTZWLWTWRXCCDWKWHUKXMWQXBMDXMWPXABCXMXLRZWNWGWOXNLWMWGWGCWKUFXMXLU
      GXNLBVGRWGVDXMXLVHXNKWFVIXMXLLLWKWHLWKVJLCWGVKVLXLLVMVPLWMVJLWGVJVNVOVQVR
      VSVTNWAPWB $.

    $d A a m n $.  $d G m n $.  $d H m n $.  $d V m n $.  $d Y m n y $.
    $d g m n x $.
    $( The mapping of the class of singleton functions into the class of
       constant functions is an injection.  (Contributed by AV,
       14-Sep-2024.) $)
    cfsetsnfsetf1 $p |- ( ( A e. V /\ Y e. A ) -> H : G -1-1-> F ) $=
      ( vm vn wa wceq vy wcel wf cv cfv weq wral wf1 cfsetsnfsetf cfsetsnfsetfv
      wi cmpt ad2ant2r ad2ant2rl eqeq12d cvv wb ralrimiva mpteqb syl simplr idd
      fvexd rspcimdv csn vex elab2 anbi12i w3a simp3 simp1r fveq2 ralsng mpbird
      feq1 wfn ffn anim12i 3ad2ant2 eqfnfv 3exp biimtrid syld sylbid ralrimivva
      imp dff13 sylanbrc ) CJUBZKCUBZSZHGIUCQUDZIUEZRUDZIUEZTZQRUFZUKZRHUGQHUGH
      GIUHABCDEFGHIJKLMNOPUIWKWRQRHHWKWLHUBZWNHUBZSZSZWPLCKWLUEZULZLCKWNUEZULZT
      ZWQXBWMXDWOXFWIWSWMXDTWJWTABCDEFGHIJWLKLMNOPUJUMWIWTWOXFTWJWSABCDEFGHIJWN
      KLMNOPUJUNUOXBXGXCXETZLCUGZWQXBXCUPUBZLCUGXGXIUQXBXJLCXBLUDZCUBSKWLVCURLC
      XCXEUPUSUTXBXIXHWQXBXHXHLKCWIWJXAVAXBXKKTSXHVBVDWKXAXHWQUKZXAKVEZDWLUCZXM
      DWNUCZSZWKXLWSXNWTXOXMDAUDZUCZXNAWLHQVFXMDXQWLVOOVGXRXOAWNHRVFXMDXQWNVOOV
      GVHWKXPXHWQWKXPXHVIZWQUAUDZWLUEZXTWNUEZTZUAXMUGZXSYDXHWKXPXHVJXSWJYDXHUQW
      IWJXPXHVKYCXHUAKCXTKTYAXCYBXEXTKWLVLXTKWNVLUOVMUTVNXSWLXMVPZWNXMVPZSZWQYD
      UQXPWKYGXHXNYEXOYFXMDWLVQXMDWNVQVRVSUAXMWLWNVTUTVNWAWBWFWCWDWDWEQRHGIWGWH
      $.

    $d A a b y z $.  $d B b n x y z $.  $d F m n $.  $d H b $.  $d V y $.
    $d b f m z $.
    $( The mapping of the class of singleton functions into the class of
       constant functions is a surjection.  (Contributed by AV,
       14-Sep-2024.) $)
    cfsetsnfsetfo $p |- ( ( A e. V /\ Y e. A ) -> H : G -onto-> F ) $=
      ( wcel wa cv wceq vm vn vy wf cfv wrex wral wfo cfsetsnfsetf vex weq feq1
      fveq1 adantr eqeq1d ralbidva rexbidv anbi12d elab2 cmpt csn simpllr fmptd
      eqid snex mptex sylibr wb mpteq2dv eqeq2d adantl simpr eqidd snidg fvmptd
      ad6antlr eqtr4d ralimdva imp wfn ffn cvv nfv fnmptd jca eqfnfv syl mpbird
      ex fvexd rspcedvd simp-4l cfsetsnfsetfv sylan rexbidva rexlimdva biimtrid
      expimpd ralrimiv dffo3 sylanbrc ) CJQZKCQZRZHGIUDUASZUBSZIUEZTZUBHUFZUAGU
      GHGIUHABCDEFGHIJKLMNOPUIXDXIUAGXEGQCDXEUDZBSZXEUEZMSZTZBCUGZMDUFZRZXDXICD
      ESZUDZXKXRUEZXMTZBCUGZMDUFZRXQEXEGUAUJEUAUKZXSXJYCXPCDXRXEULYDYBXOMDYDYAX
      NBCYDXKCQZRXTXLXMYDXTXLTYEXKXRXEUMUNUOUPUQURNUSXDXJXPXIXDXJRZXOXIMDYFXMDQ
      ZRZXOXIYHXORZXIXELCKXFUEZUTZTZUBHUFYIYLXELCKUCKVAZXMUTZUEZUTZTZUBYNHYIYMD
      YNUDZYNHQYIUCYMXMDYNYFYGXOUCSZYMQVBYNVDVCYMDASZUDYRAYNHUCYMXMKVEVFYMDYTYN
      ULOUSVGXFYNTZYLYQVHYIUUAYKYPXEUUALCYJYOKXFYNUMVIVJVKYIYQXLXKYPUEZTZBCUGZY
      HXOUUDYHXNUUCBCYHYERZXNUUCUUEXNRZXLXMUUBUUEXNVLUUFLXKYOXMCYPDUUFYPVMUUFLB
      UKZRZUCKXMXMYMYNDUUHYNVMUUHYSKTRXMVMXCKYMQXBXJYGYEXNUUGKCVNVPUUFYGUUGYFYG
      YEXNVBZUNVOUUEYEXNYHYEVLUNUUIVOVQWIVRVSYIXECVTZYPCVTZRZYQUUDVHYHUULXOYFUU
      LYGYFUUJUUKXJUUJXDCDXEWAVKYFLCYOYPWBYFLWCYFLSCQRKYNWJYPVDWDWEUNUNBCXEYPWF
      WGWHWKYIXHYLUBHYIXFHQZRXGYKXEYIXBUUMXGYKTXBXCXJYGXOWLABCDEFGHIJXFKLMNOPWM
      WNVJWOWHWIWPWRWQWSUBUAHGIWTXA $.

    $( The mapping of the class of singleton functions into the class of
       constant functions is a bijection.  (Contributed by AV, 14-Sep-2024.) $)
    cfsetsnfsetf1o $p |- ( ( A e. V /\ Y e. A ) -> H : G -1-1-onto-> F ) $=
      ( wcel wa wf1 wfo wf1o cfsetsnfsetf1 cfsetsnfsetfo df-f1o sylanbrc ) CJQK
      CQRHGISHGITHGIUAABCDEFGHIJKLMNOPUBABCDEFGHIJKLMNOPUCHGIUDUE $.
  $}

  ${
    $d A a b f g y z $.  $d B a b f g y z $.  $d V a b g y z $.
    $( First version of proof for ~ fsetprcnex , which was much more
       complicated.  (Contributed by AV, 14-Sep-2024.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    fsetprcnexALT $p |- ( ( ( A e. V /\ A =/= (/) ) /\ B e/ _V )
                       -> { f | f : A --> B } e/ _V ) $=
      ( vz vb vy vg va wcel wa cvv wnel cv wf cfv cab wn wi eqid wceq wral wrex
      c0 wne wss abanssl wex n0 csn vex a1i fsetsnprcnex sylan df-nel cmpt wf1o
      sylib wb cfsetsnfsetf1o ancoms adantr f1ovv bicomd syl mtbird exp31 sylbi
      exlimiv impcom imp sylibr prcssprc sylancr ) ADJZAUDUEZKZBLMZKZABCNZOZENV
      TPFNUAEAUBFBUCZKCQZWACQZUFWCLMZWDLMWAWBCUGVSWCLJZRZWEVQVRWGVPVOVRWGSZVPGN
      ZAJZGUHVOWHSZGAUIWJWKGWJVOVRWGWJVOKZVRKZWFWIUJBVTOCQZLJZWMWNLMZWORWLWILJZ
      VRWPWQWLGUKULBWICLUMUNWNLUOURWMWNWCHWNIAWIHNPUPUPZUQZWFWOUSWLWSVRVOWJWSCE
      ABCHWCWNWRDWIIFWCTWNTWRTUTVAVBWSWOWFWNWCWRVCVDVEVFVGVIVHVJVKWCLUOVLWCWDVM
      VN $.
  $}

  ${
    fcores.f $e |- ( ph -> F : A --> B ) $.
    fcores.e $e |- E = ( ran F i^i C ) $.
    fcores.p $e |- P = ( `' F " C ) $.
    $( Lemma 1 for ~ fcores .  (Contributed by AV, 17-Sep-2024.) $)
    fcoreslem1 $p |- ( ph -> P = ( `' F " E ) ) $=
      ( ccnv cima crn cin wfun wceq ffund cnvimainrn syl eqcomd imaeq2i 3eqtr4g
      ) AGKZDLZUCGMDNZLZEUCFLAUFUDAGOUFUDPABCGHQDGRSTJFUEUCIUAUB $.

    fcores.x $e |- X = ( F |` P ) $.
    $( Lemma 2 for ~ fcores .  (Contributed by AV, 17-Sep-2024.) $)
    fcoreslem2 $p |- ( ph -> ran X = E ) $=
      ( crn cima ccnv cres df-ima wceq a1i cin rneqi eqtr2id fcoreslem1 imaeq2d
      eqcomi wfun ffund funimacnv syl inss1 eqsstri dfss2 sylib eqtrd 3eqtrd
      wss ) AHMZGENZGGOFNZNZFAURGEPZMZUQGEQVBUQRAUQVBHVALUAUESUBAEUSGABCDEFGIJK
      UCUDAUTFGMZTZFAGUFUTVDRABCGIUGFGUHUIAFVCUPZVDFRVEAFVCDTVCJVCDUJUKSFVCULUM
      UNUO $.

    $( Lemma 3 for ~ fcores .  (Contributed by AV, 13-Sep-2024.) $)
    fcoreslem3 $p |- ( ph -> X : P -onto-> E ) $=
      ( wfo cres ffnd crn cin wceq a1i ccnv cima rescnvimafod foeq1 mp1i mpbird
      wb ) AEFHMZEFGENZMZABDEFGABCGIOFGPDQRAJSEGTDUARAKSUBHUHRUGUIUFALEFHUHUCUD
      UE $.

    fcores.g $e |- ( ph -> G : C --> D ) $.
    fcores.y $e |- Y = ( G |` E ) $.
    $( Lemma 4 for ~ fcores .  (Contributed by AV, 17-Sep-2024.) $)
    fcoreslem4 $p |- ( ph -> ( Y o. X ) Fn P ) $=
      ( wfn crn wceq wss ccom cres ffnd cin a1i eqsstrdi fnssresd fneq1i sylibr
      inss2 wfo fcoreslem3 fofn syl fcoreslem2 eqimss fnco syl3anc ) AKGRZJFRZJ
      SZGUAZKJUBFRAIGUCZGRUTADGIADEIPUDAGHSZDUEZDGVFTAMUFVEDUKUGUHGKVDQUIUJAFGJ
      ULVAABCDFGHJLMNOUMFGJUNUOAVBGTVCABCDFGHJLMNOUPVBGUQUOGFKJURUS $.

    $d C x $.  $d F x $.  $d G x $.  $d P x $.  $d X x $.  $d Y x $.
    $d ph x $.
    $( Every composite function ` ( G o. F ) ` can be written as composition of
       restrictions of the composed functions (to their minimum domains).
       (Contributed by GL and AV, 17-Sep-2024.) $)
    fcores $p |- ( ph -> ( G o. F ) = ( Y o. X ) ) $=
      ( wf wcel cfv vx ccom ccnv cima wfn wfun ffund fcof syl2anc fneq2i sylibr
      ffnd fcoreslem4 cv wa cres fveq1i simpr fvresd eqtrid fveq2d crn cnvimass
      cin cdm sseli fvelrn syl2an eleq2i biimpi fvimacnvi elind eleqtrrdi eqtrd
      eqsstri wfo fcoreslem3 fof syl adantr fvco3d wss a1i sselda eqcomd eleq2d
      wb fdmd mpbird 3eqtr4rd eqfnfvd ) AUAFIHUBZKJUBZAWLHUCDUDZUEWLFUEAWNEWLAD
      EIRHUFZWNEWLRPABCHLUGZDEIHUHUIULFWNWLNUJUKABCDEFGHIJKLMNOPQUMAUAUNZFSZUOZ
      WQJTZKTZWQHTZITZWQWMTWQWLTWSXAXBKTZXCWSWTXBKWSWTWQHFUPZTXBWQJXEOUQWSWQFHA
      WRURZUSUTVAWSXDXBIGUPZTXCXBKXGQUQWSXBGIWSXBHVBZDVDGWSXHDXBAWOWQHVEZSZXBXH
      SWRWPFXIWQFWNXINHDVCVOZVFWQHVGVHAWOWQWNSZXBDSWRWPWRXLFWNWQNVIVJWQDHVKVHVL
      MVMUSUTVNWSFGWQKJAFGJRZWRAFGJVPXMABCDFGHJLMNOVQFGJVRVSVTXFWAWSBCWQIHABCHR
      WRLVTWSWQBSZXJAFXIWQFXIWBAXKWCWDAXNXJWGWRABXIWQAXIBABCHLWHWEWFVTWIWAWJWK
      $.

    $( Lemma for ~ fcoresf1 .  (Contributed by AV, 18-Sep-2024.) $)
    fcoresf1lem $p |- ( ( ph /\ Z e. P )
                        -> ( ( G o. F ) ` Z ) = ( Y ` ( X ` Z ) ) ) $=
      ( ccom cfv wcel wa wceq fcores fveq1d adantr wfo fcoreslem3 fof syl simpr
      wf fvco3d eqtrd ) ALFUAZUBZLIHSZTZLKJSZTZLJTKTAURUTUCUOALUQUSABCDEFGHIJKM
      NOPQRUDUEUFUPFGLKJAFGJULZUOAFGJUGVAABCDFGHJMNOPUHFGJUIUJUFAUOUKUMUN $.

    ${
      $d E x y $.  $d F y $.  $d G y $.  $d P a b x y $.  $d X a b y $.
      $d Y a b y $.  $d ph a b y $.
      fcoresf1.i $e |- ( ph -> ( G o. F ) : P -1-1-> D ) $.
      $( If a composition is injective, then the restrictions of its components
         to the minimum domains are injective.  (Contributed by GL and AV,
         18-Sep-2024.)  (Revised by AV, 7-Oct-2024.) $)
      fcoresf1 $p |- ( ph -> ( X : P -1-1-> E /\ Y : E -1-1-> D ) ) $=
        ( wceq wi vx vy va vb wf1 wf cv cfv wral wfo fcoreslem3 fof syl ccom wa
        dff13 wcel fcoresf1lem adantrr adantrl eqeq12d imbi1d a1i imim1d sylbid
        fveq2 ralimdvva adantld biimtrid mpd sylanbrc cres crn eqsstrdi fssresd
        cin inss2 feq1i sylibr wrex fcoreslem2 eqcomd eleq2d fofn fvelrnb bitrd
        wfn wb anbi12d fveqeq2 imbi12d eqeq2d equequ2 rspc2v adantl imim2d syld
        eqeq1 com23 impl eqeqan12rd eqeq12 ancoms syl5ibcom expd rexlimdva impd
        ex ralrimivv jca ) AFGJUEZGEKUEZAFGJUFZUAUGZJUHZUBUGZJUHZSZXNXPSZTZUBFU
        IUAFUIZXKAFGJUJZXMABCDFGHJLMNOUKZFGJULUMAFEIHUNZUEZYARYEFEYDUFZXNYDUHZX
        PYDUHZSZXSTZUBFUIUAFUIZUOZAYAUAUBFEYDUPZAYKYAYFAYJXTUAUBFFAXNFUQZXPFUQZ
        UOUOZYJXOKUHZXQKUHZSZXSTXTYPYIYSXSYPYGYQYHYRAYNYGYQSYOABCDEFGHIJKXNLMNO
        PQURUSAYOYHYRSYNABCDEFGHIJKXPLMNOPQURUTVAVBYPXRYSXSXRYSTYPXOXQKVFVCVDVE
        VGVHVIVJUAUBFGJUPVKAGEKUFZXNKUHZXPKUHZSZXSTZUBGUIUAGUIXLAGEIGVLZUFYTADE
        GIPAGHVMZDVPZDGUUGSAMVCUUFDVQVNVOGEKUUEQVRVSAUUDUAUBGGAXNGUQZXPGUQZUOUC
        UGZJUHZXNSZUCFVTZUDUGZJUHZXPSZUDFVTZUOUUDAUUHUUMUUIUUQAUUHXNJVMZUQZUUMA
        GUURXNAUURGABCDFGHJLMNOWAWBZWCAJFWGZUUSUUMWHAYBUVAYCFGJWDUMZUCFXNJWEUMW
        FAUUIXPUURUQZUUQAGUURXPUUTWCAUVAUVCUUQWHUVBUDFXPJWEUMWFWIAUUMUUQUUDAUUL
        UUQUUDTUCFAUUJFUQZUOZUUQUULUUDUVEUUPUULUUDTUDFUVEUUNFUQZUOZUUPUULUUDUVG
        UUKKUHZUUOKUHZSZUUKUUOSZTZUUPUULUOZUUDAUVDUVFUVLAYEUVDUVFUOZUVLTZRYEYLA
        UVOYMAYKUVOYFAUVNYKUVLAUVNYKUVLTAUVNUOZYKUUJYDUHZUUNYDUHZSZUUJUUNSZTZUV
        LUVNYKUWATAYJUWAUVQYHSZUUJXPSZTUAUBUUJUUNFFXNUUJSYIUWBXSUWCXNUUJYHYDWJX
        NUUJXPWRWKXPUUNSZUWBUVSUWCUVTUWDYHUVRUVQXPUUNYDVFWLUBUDUCWMWKWNWOUVPUWA
        UVJUVTTUVLUVPUVSUVJUVTUVPUVQUVHUVRUVIAUVDUVQUVHSUVFABCDEFGHIJKUUJLMNOPQ
        URUSAUVFUVRUVISUVDABCDEFGHIJKUUNLMNOPQURUTVAVBUVPUVTUVKUVJUVTUVKTUVPUUJ
        UUNJVFVCWPVEWQXHWSVHVIVJWTUVMUVJUUCUVKXSUULUUPUVHUUAUVIUUBUUKXNKVFUUOXP
        KVFXAUULUUPUVKXSWHUUKXNUUOXPXBXCWKXDXEXFWSXFXGVEXIUAUBGEKUPVKXJ $.
    $}

    $( A composition is injective iff the restrictions of its components to the
       minimum domains are injective.  (Contributed by GL and AV,
       7-Oct-2024.) $)
    fcoresf1b $p |- ( ph -> ( ( G o. F ) : P -1-1-> D
                              <-> ( X : P -1-1-> E /\ Y : E -1-1-> D ) ) ) $=
      ( ccom wf1 wa wf adantr simpr fcoresf1 ex f1co ancoms wb fcores f1eq1 syl
      wceq imbitrrid impbid ) AFEIHRZSZFGJSZGEKSZTZAUPUSAUPTBCDEFGHIJKABCHUAUPL
      UBMNOADEIUAUPPUBQAUPUCUDUEUSUPAFEKJRZSZURUQVAFGEKJUFUGAUOUTULUPVAUHABCDEF
      GHIJKLMNOPQUIFEUOUTUJUKUMUN $.

    ${
      fcoresfo.s $e |- ( ph -> ( G o. F ) : P -onto-> D ) $.
      $( If a composition is surjective, then the restriction of its first
         component to the minimum domain is surjective.  (Contributed by AV,
         17-Sep-2024.) $)
      fcoresfo $p |- ( ph -> Y : E -onto-> D ) $=
        ( wf wfo ccom cres crn cin wceq a1i inss2 eqsstrdi fssresd feq1i sylibr
        fcoreslem3 fof syl wb fcores eqcomd foeq1 mpbird foco2 syl3anc ) AGEKSZ
        FGJSZFEKJUAZTZGEKTAGEIGUBZSVBADEGIPAGHUCZDUDZDGVHUEAMUFVGDUGUHUIGEKVFQU
        JUKAFGJTVCABCDFGHJLMNOULFGJUMUNAVEFEIHUAZTZRAVDVIUEVEVJUOAVIVDABCDEFGHI
        JKLMNOPQUPUQFEVDVIURUNUSFGEKJUTVA $.
    $}

    $( A composition is surjective iff the restriction of its first component
       to the minimum domain is surjective.  (Contributed by GL and AV,
       7-Oct-2024.) $)
    fcoresfob $p |- ( ph -> ( ( G o. F ) : P -onto-> D
                              <-> Y : E -onto-> D ) ) $=
      ( wfo wa adantr ccom wf simpr fcoresfo fcoreslem3 anim1ci foco syl fcores
      wceq wb foeq1 mpbird impbida ) AFEIHUAZRZGEKRZAUPSBCDEFGHIJKABCHUBUPLTMNO
      ADEIUBUPPTQAUPUCUDAUQSZUPFEKJUAZRZURUQFGJRZSUTAVAUQABCDFGHJLMNOUEUFFGEKJU
      GUHURUOUSUJZUPUTUKAVBUQABCDEFGHIJKLMNOPQUITFEUOUSULUHUMUN $.

    $( A composition is bijective iff the restriction of its first component to
       the minimum domain is bijective and the restriction of its second
       component to the minimum domain is injective.  (Contributed by GL and
       AV, 7-Oct-2024.) $)
    fcoresf1ob $p |- ( ph -> ( ( G o. F ) : P -1-1-onto-> D
                           <-> ( X : P -1-1-> E /\ Y : E -1-1-onto-> D ) ) ) $=
      ( wf1 wfo wa ccom fcoresf1b fcoresfob anbi12d anass bitrdi df-f1o 3bitr4g
      wf1o anbi2i ) AFEIHUAZRZFEUKSZTZFGJRZGEKRZGEKSZTZTZFEUKUIUOGEKUIZTAUNUOUP
      TZUQTUSAULVAUMUQABCDEFGHIJKLMNOPQUBABCDEFGHIJKLMNOPQUCUDUOUPUQUEUFFEUKUGU
      TURUOGEKUGUJUH $.

    ${
      f1cof1blem.s $e |- ( ph -> ran F = C ) $.
      $( Lemma for ~ f1cof1b and ~ focofob .  (Contributed by AV,
         18-Sep-2024.) $)
      f1cof1blem $p |- ( ph -> ( ( P = A /\ E = C )
                              /\ ( X = F /\ Y = G ) ) ) $=
        ( wceq eqtrid wa ccnv crn cima eqcomd imaeq2d cdm cnvimarndm fdmd eqtrd
        cin simpr ineq1d inidm eqtrdi mpdan jca cres reseq2d freld resdm eqtr4d
        wrel syl jca32 ) AFBSZGDSZUAJHSKISAVFVGAFHUBZHUCZUDZBAFVHDUDVJNADVIVHAV
        IDRUEUFTZAVJHUGZBHUHZABCHLUITUJAGVIDUKZDMAVIDSZVNDSRAVOUAZVNDDUKDVPVIDD
        AVOULUMDUNUOUPTZUQAJHVLURZHAJHFURVROAFVLHAFVJVLVKVMUOUSTAHVCVRHSABCHLUT
        HVAVDUJAKIIUGZURZIAKIGURVTQAGVSIAGDVSVQADEIPUIVBUSTAIVCVTISADEIPUTIVAVD
        UJVE $.
    $}
  $}

  $( The composition of three bijections as bijection from the image of the
     domain onto the image of the range of the middle bijection.  (Contributed
     by AV, 15-Aug-2025.) $)
  3f1oss1 $p |- ( ( ( F : A -1-1-onto-> B /\ G : C -1-1-onto-> D
                   /\ H : E -1-1-onto-> I ) /\ ( C C_ A /\ D C_ E ) )
               -> ( ( H o. G ) o. `' F ) : ( F " C ) -1-1-onto-> ( H " D ) ) $=
    ( wf1o wss wa cima ccom cin syl 3ad2ant1 adantr wceq eqid w3a ccnv crn cres
    wf1 wf f1ocnv f1of1 cdm cnvimass f1of fdm eqcomd 3syl sseqtrrid f1ofn eqidd
    wfo wfn rescnvimafod fof f1resf1 syl3anc 3ad2ant2 inss2 f1ores sylancl forn
    f1ofo ineq1d incom dfss2 biimpi eqtrid ad2antrl eqtrd imaeq2d fnima f1oeq3d
    mpbird wrel f1orel dfrel2 sylib imaeq1d f1oeq2d fcoresf1ob mpbir2and simpl3
    bitrd simprr f1ocoima wb coass f1oeq1 ax-mp sylibr ) ABFJZCDGJZEIHJZUAZCAKZ
    DEKZLZLZFCMZHDMZHGFUBZNZNZJZXFXGHGNXHNZJZXEXFDXIJZWTXCXKXEXNXHUBZCMZXHUCZCO
    ZXHXPUDZUEZXRDGXRUDZJZXEBAXHUEZXPBKZXPXRXSUFZXTXAYCXDWRWSYCWTWRBAXHJZYCABFU
    GZBAXHUHPQRXAYDXDWRWSYDWTWRXHUIZXPBXHCUJWRYFBAXHUFZBYHSYGBAXHUKZYIYHBBAXHUL
    UMUNUOQRXEXPXRXSURYEXEBCXPXRXHXAXHBUSZXDWRWSYKWTWRYFYKYGBAXHUPPQRXEXRUQXEXP
    UQUTXPXRXSVAPBAXPXRXHVBVCXEYBXRGXRMZYAJZXECDGUEZXRCKYMXAYNXDWSWRYNWTCDGUHVD
    RXQCVECDXRGVFVGXEDYLXRYAXEYLDXEYLGCMZDXEXRCGXEXRACOZCXEXQACXAXQASZXDWRWSYQW
    TWRYFBAXHURYQYGBAXHVIBAXHVHUNQRVJXBYPCSXAXCXBYPCAOZCACVKXBYRCSCAVLVMVNVOVPV
    QXAYODSZXDWSWRYSWTWSYOGUCZDWSGCUSYOYTSCDGUPCGVRPWSCDGURYTDSCDGVICDGVHPVPVDR
    VPUMVSVTXEXNXPDXIJXTYBLXEXFXPDXIXEFXOCXEXOFXEFWAZXOFSXAUUAXDWRWSUUAWTABFWBQ
    RFWCWDUMWEWFXEBACDXPXRXHGXSYAXAYIXDWRWSYIWTWRYFYIYGYJPQRXRTXPTXSTXACDGUFZXD
    WSWRUUBWTCDGUKVDRYATWGWJWHWRWSWTXDWIXAXBXCWKXFDEIXIHWLVCXLXJSXMXKWMHGXHWNXF
    XGXLXJWOWPWQ $.

  $( The composition of three bijections as bijection from the image of the
     converse of the domain onto the image of the converse of the range of the
     middle bijection.  (Contributed by AV, 15-Aug-2025.) $)
  3f1oss2 $p |- ( ( ( F : A -1-1-onto-> B /\ G : C -1-1-onto-> D
                   /\ H : E -1-1-onto-> I ) /\ ( C C_ B /\ D C_ I ) )
         -> ( ( `' H o. G ) o. F ) : ( `' F " C ) -1-1-onto-> ( `' H " D ) ) $=
    ( wf1o w3a wss wa ccnv cima ccom f1ocnv id 3f1oss1 syl3anl wrel f1orel wceq
    wb dfrel2 biimpi eqcomd coeq2d f1oeq1d syl 3ad2ant1 adantr mpbird ) ABFJZCD
    GJZEIHJZKZCBLDILMZMFNZCOZHNZDOZVAGPZFPZJZUTVBVCUSNZPZJZUNBAUSJUOUOUPIEVAJUR
    VHABFQUOREIHQBACDIUSGVAESTUQVEVHUDZURUNUOVIUPUNFUAZVIABFUBVJUTVBVDVGVJFVFVC
    VJVFFVJVFFUCFUEUFUGUHUIUJUKULUM $.

  $( If the range of ` F ` equals the domain of ` G ` , then the composition
     ` ( G o. F ) ` is injective iff ` F ` and ` G ` are both injective.
     (Contributed by GL and AV, 19-Sep-2024.) $)
  f1cof1b $p |- ( ( F : A --> B /\ G : C --> D /\ ran F = C )
                  -> ( ( G o. F ) : A -1-1-> D
                       <-> ( F : A -1-1-> B /\ G : C -1-1-> D ) ) ) $=
    ( wf wceq wf1 wa cima cres eqid simpll adantr simpr ancomd f1eq123d biimpd
    wb crn w3a ccom ccnv simp1 simp2 simp3 f1cof1blem f1eq2 bicomd ancom anbi2i
    cin 3syl sylibr fcoresf1 simprl eqidd simprr anim12d sylc sylbida wfun ffrn
    impbid2 anbi1d df-f1 3bitr4g 3ad2ant1 f1eq3 3ad2ant3 bitrd anbi2d mpbird ex
    ax-1 f1cof1 ancoms cdm imaeq2 cnvimarndm eqtrdi eqcoms fdmd imbitrid impbid
    eqtrd syl ) ABEGZCDFGZEUAZCHZUBZADFEUCZIZABEIZCDFIZJZWMWOWRWMWOJZWQWPWSWQWP
    JZWQACEIZJZWMWOEUDZCKZDWNIZXBWMXEWOWMXDAHZWKCUMZCHZJZEXDLZEHZFXGLZFHZJZJZXF
    XEWOTZWMABCDXDXGEFXJXLWIWJWLUEZXGMZXDMZXJMZWIWJWLUFZXLMZWIWJWLUGUHZXFXHXNNX
    DADWNUIZUNUJWMXEJZXIXMXKJZJZXGDXLIZXDXGXJIZJXBWMYGXEWMXOYGYCYFXNXIXMXKUKULU
    OOYEYIYHYEABCDXDXGEFXJXLWMWIXEXQOXRXSXTWMWJXEYAOYBWMXEPUPQYGYHWQYIXAYGYHWQY
    GXGCDDXLFXIXMXKUQXIXHYFXFXHPOZYGDURRSYGYIXAYGXDAXGCXJEXIXMXKUSXFXHYFNYJRSUT
    VAVBWMWTXBTWOWMWPXAWQWMWPAWKEIZXAWIWJWPYKTWLWIWIXCVCZJAWKEGZYLJWPYKWIWIYMYL
    WIWIYMABEVDWIYMVPVEVFABEVGAWKEVGVHVIWLWIYKXATWJWKCAEVJVKVLVMOVNQVOWRXEWMWOW
    QWPXEABCDFEVQVRWMXFXPWMXDEVSZAWLWIXDYNHZWJYOCWKCWKHXDXCWKKYNCWKXCVTEWAWBWCV
    KWMABEXQWDWGYDWHWEWF $.

  $( If the domain of a function ` G ` is a subset of the range of a function
     ` F ` , then the composition ` ( G o. F ) ` is surjective iff ` G ` is
     surjective.  (Contributed by GL and AV, 29-Sep-2024.) $)
  funfocofob $p |- ( ( Fun F /\ G : A --> B /\ A C_ ran F )
            -> ( ( G o. F ) : ( `' F " A ) -onto-> B <-> G : A -onto-> B ) ) $=
    ( wfun wf crn wss w3a ccnv wfo cres wa cdm biimpi adantr eqid simpr ex wceq
    cima ccom cin fdmrn 3ad2ant1 simp2 fcoresfo sseqin2 3ad2ant3 eqtr4d reseq2d
    fdmd wrel freld resdm syl eqtrd eqidd foeq123d sylibd simpl1 simpl3 syl3anc
    focofo impbid ) CEZABDFZACGZHZIZCJAUAZBDCUBKZABDKZVJVLVHAUCZBDVNLZKZVMVJVLV
    PVJVLMCNZVHABVKVNCDCVKLZVOVJVQVHCFZVLVFVGVSVIVFVSCUDOUEPVNQVKQVRQVJVGVLVFVG
    VIUFZPVOQVJVLRUGSVJVNABBVODVJVODDNZLZDVJVNWADVJVNAWAVIVFVNATZVGVIWCAVHUHOUI
    ZVJABDVTULUJUKVJDUMWBDTVJABDVTUNDUOUPUQWDVJBURUSUTVJVMVLVJVMMVMVFVIVLVJVMRV
    FVGVIVMVAVFVGVIVMVBABDCVDVCSVE $.

  $( If the domain of a function ` G ` equals the range of a function ` F ` ,
     then the composition ` ( G o. F ) ` is surjective iff ` G ` is surjective.
     (Contributed by GL and AV, 29-Sep-2024.) $)
  fnfocofob $p |- ( ( F Fn A /\ G : B --> C /\ ran F = B )
                  -> ( ( G o. F ) : A -onto-> C <-> G : B -onto-> C ) ) $=
    ( wfn wf crn wceq w3a ccom wfo ccnv cima wb cdm cnvimarndm 3ad2ant1 eqtr2id
    fndm imaeq2 3ad2ant3 eqtrd foeq2 syl wss fnfun id eqimss2 funfocofob syl3an
    wfun bitrd ) DAFZBCEGZDHZBIZJZACEDKZLZDMZBNZCUSLZBCELZURAVBIUTVCOURAVAUPNZV
    BURVEDPZADQUNUOVFAIUQADTRSUQUNVEVBIUOUPBVAUAUBUCAVBCUSUDUEUNDULUOUOUQBUPUFV
    CVDOADUGUOUHBUPUIBCDEUJUKUM $.

  $( If the domain of a function ` G ` equals the range of a function ` F ` ,
     then the composition ` ( G o. F ) ` is surjective iff ` G ` and ` F ` as
     function to the domain of ` G ` are both surjective.  Symmetric version of
     ~ fnfocofob including the fact that ` F ` is a surjection onto its range.
     (Contributed by GL and AV, 20-Sep-2024.)  (Proof shortened by AV,
     29-Sep-2024.) $)
  focofob $p |- ( ( F : A --> B /\ G : C --> D /\ ran F = C )
                  -> ( ( G o. F ) : A -onto-> D
                       <-> ( F : A -onto-> C /\ G : C -onto-> D ) ) ) $=
    ( wf crn wceq w3a ccom wfo wa wfn wb ffn fnfocofob syl3an1 dffn4 sylib
    3ad2ant1 foeq3 3ad2ant3 mpbid biantrurd bitrd ) ABEGZCDFGZEHZCIZJZADFEKLZCD
    FLZACELZUMMUGEANZUHUJULUMOABEPZACDEFQRUKUNUMUKAUIELZUNUGUHUQUJUGUOUQUPAESTU
    AUJUGUQUNOUHUICAEUBUCUDUEUF $.

  $( If the range of ` F ` equals the domain of ` G ` , then the composition
     ` ( G o. F ) ` is bijective iff ` F ` and ` G ` are both bijective.
     (Contributed by GL and AV, 7-Oct-2024.) $)
  f1ocof1ob $p |- ( ( F : A --> B /\ G : C --> D /\ ran F = C )
                    -> ( ( G o. F ) : A -1-1-onto-> D
                      <-> ( F : A -1-1-> C /\ G : C -1-1-onto-> D ) ) ) $=
    ( wf crn wceq w3a ccom wf1 wfo wa wf1o wb ffrn 3ad2ant1 feq3 df-f1o f1cof1b
    3ad2ant3 mpbid syld3an1 wfn fnfocofob syl3an1 anbi12d bitrdi anbi2i 3bitr4g
    ffn anass ) ABEGZCDFGZEHZCIZJZADFEKZLZADUSMZNZACELZCDFLZCDFMZNZNZADUSOVCCDF
    OZNURVBVCVDNZVENVGURUTVIVAVEACEGZUOUNUQUTVIPURAUPEGZVJUNUOVKUQABEQRUQUNVKVJ
    PUOUPCAESUBUCACCDEFUAUDUNEAUEUOUQVAVEPABEULACDEFUFUGUHVCVDVEUMUIADUSTVHVFVC
    CDFTUJUK $.

  $( If the range of ` F ` equals the domain of ` G ` , then the composition
     ` ( G o. F ) ` is bijective iff ` F ` and ` G ` are both bijective.
     Symmetric version of ~ f1ocof1ob including the fact that ` F ` is a
     surjection onto its range.  (Contributed by GL and AV, 20-Sep-2024.)
     (Proof shortened by AV, 7-Oct-2024.) $)
  f1ocof1ob2 $p |- ( ( F : A --> B /\ G : C --> D /\ ran F = C )
                    -> ( ( G o. F ) : A -1-1-onto-> D
                      <-> ( F : A -1-1-onto-> C /\ G : C -1-1-onto-> D ) ) ) $=
    ( wf crn wceq w3a ccom wf1 wa f1ocof1ob wi f1f1orn f1oeq3 imbitrid 3ad2ant3
    wf1o f1of1 impbid1 anbi1d bitrd ) ABEGZCDFGZEHZCIZJZADFEKTACELZCDFTZMACETZU
    KMABCDEFNUIUJULUKUIUJULUHUEUJULOUFUJAUGETUHULACEPUGCAEQRSACEUAUBUCUD $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Alternative for Russell's definition of a description binder
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c iota' $.
  $( Extend class notation with an alternative for Russell's definition of a
     description binder (inverted iota). $)
  caiota $a class ( iota' x ph ) $.

  ${
    $d w x z $.  $d ph w z $.  $d ph w y $.  $d x y $.
    $( Soundness justification theorem for ~ df-aiota .  (Contributed by AV,
       24-Aug-2022.) $)
    aiotajust $p |- |^| { y | { x | ph } = { y } }
                    = |^| { z | { x | ph } = { z } } $=
      ( vw cab cv csn wceq weq sneq eqeq2d cbvabv eqtri inteqi ) ABFZCGZHZIZCFZ
      PDGZHZIZDFZTPEGZHZIZEFUDSUGCECEJRUFPQUEKLMUGUCEDEDJUFUBPUEUAKLMNO $.
  $}

  ${
    $d y x $.  $d y ph $.
    $( Alternate version of Russell's definition of a description binder, which
       can be read as "the unique ` x ` such that ` ph ` ", where ` ph `
       ordinarily contains ` x ` as a free variable.  Our definition is
       meaningful only when there is exactly one ` x ` such that ` ph ` is true
       (see ~ aiotaval ); otherwise, it is not a set (see ~ aiotaexb ), or even
       more concrete, it is the universe ` _V ` (see ~ aiotavb ).  Since this
       is an alternative for ~ df-iota , we call this symbol ` iota' `
       _alternate iota_ in the following.

       The advantage of this definition is the clear distinguishability of the
       defined and undefined cases: the alternate iota over a wff is defined
       iff it is a set (see ~ aiotaexb ).  With the original definition, there
       is no corresponding theorem ` ( E! x ph <-> ( iota x ph ) =/= (/) ) ` ,
       because ` (/) ` can be a valid unique set satisfying a wff (see, for
       example, ~ iota0def ).  Only the right to left implication would hold,
       see (negated) ~ iotanul .  For defined cases, however, both definitions
       ~ df-iota and ~ df-aiota are equivalent, see ~ reuaiotaiota .  (Proposed
       by BJ, 13-Aug-2022.)  (Contributed by AV, 24-Aug-2022.) $)
    df-aiota $a |- ( iota' x ph ) = |^| { y | { x | ph } = { y } } $.

    $( Alternate definition of the alternate version of Russell's definition of
       a description binder.  Definition 8.18 in [Quine] p. 56.  (Contributed
       by AV, 24-Aug-2022.) $)
    dfaiota2 $p |- ( iota' x ph ) = |^| { y | A. x ( ph <-> x = y ) } $=
      ( caiota cab cv csn wceq cint weq wb wal df-aiota absn abbii inteqi eqtri
      ) ABDABECFZGHZCEZIABCJKBLZCEZIABCMTUBSUACABRNOPQ $.
  $}

  ${
    $d x y $.  $d ph y $.
    $( The iota and the alternate iota over a wff ` ph ` are equal iff there is
       a unique satisfying value of ` { x | ph } = { y } ` .  (Contributed by
       AV, 25-Aug-2022.) $)
    reuabaiotaiota $p |- ( E! y { x | ph } = { y }
                         <-> ( iota x ph ) = ( iota' x ph ) ) $=
      ( cab csn wceq weu cuni cint cio caiota uniintab df-iota df-aiota eqeq12i
      cv bitr4i ) ABDCPEFZCGRCDZHZSIZFABJZABKZFRCLUBTUCUAABCMABCNOQ $.

    $( The iota and the alternate iota over a wff ` ph ` are equal iff there is
       a unique value ` x ` satisfying ` ph ` .  (Contributed by AV,
       25-Aug-2022.) $)
    reuaiotaiota $p |- ( E! x ph <-> ( iota x ph ) = ( iota' x ph ) ) $=
      ( vy weu cab cv csn wceq cio caiota euabsneu reuabaiotaiota bitri ) ABDAB
      ECFGHCDABIABJHABCKABCLM $.

    $( The alternate iota over a wff ` ph ` is a set iff there is a unique
       value ` x ` satisfying ` ph ` .  (Contributed by AV, 25-Aug-2022.) $)
    aiotaexb $p |- ( E! x ph <-> ( iota' x ph ) e. _V ) $=
      ( vy cab cv csn wceq wex cint cvv wcel weu caiota intexab df-aiota eleq1i
      euabsn2 3bitr4i ) ABDCEFGZCHSCDIZJKABLABMZJKSCNABCQUATJABCOPR $.

    $( The alternate iota over a wff ` ph ` is the universe iff there is no
       unique value ` x ` satisfying ` ph ` .  (Contributed by AV,
       25-Aug-2022.) $)
    aiotavb $p |- ( -. E! x ph <-> ( iota' x ph ) = _V ) $=
      ( vy caiota cvv wcel wceq weu cab cv csn wn intnex df-aiota eleq1i notbii
      cint eqeq1i 3bitr4i aiotaexb xchnxbir ) ABDZEFZUBEGZABHABICJKGCIZQZEFZLUF
      EGUCLUDUEMUCUGUBUFEABCNZOPUBUFEUHRSABTUA $.
  $}

  $( This is to ~ df-aiota what ~ iotauni is to ~ df-iota (it uses intersection
     like ~ df-aiota , similar to ~ iotauni using union like ~ df-iota ; we
     could also prove an analogous result using union here too, in the same way
     that we have ~ iotaint ).  (Contributed by BJ, 31-Aug-2024.) $)
  aiotaint $p |- ( E! x ph -> ( iota' x ph ) = |^| { x | ph } ) $=
    ( weu cio caiota cab cint wceq reuaiotaiota biimpi iotaint eqtr3d ) ABCZABD
    ZABEZABFGMNOHABIJABKL $.

  $( Alternate definition of ` iota' ` , using the ` if ` operator: this is to
     ~ df-aiota what ~ dfiota4 is to ~ df-iota .  It is simpler than ~ df-aiota
     and uses no dummy variables, so it would be the preferred definition if
     ` iota' ` becomes the description binder used in set.mm.  (Contributed by
     BJ, 31-Aug-2024.) $)
  dfaiota3 $p |- ( iota' x ph ) = if ( E! x ph , |^| { x | ph } , _V ) $=
    ( caiota weu cab cint cvv wceq wi wn aiotaint aiotavb biimpi ifval mpbir2an
    cif ) ABCZABDZABEFZGPHRQSHIRJZQGHZIABKTUAABLMRQSGNO $.

  $( If the iota over a wff ` ph ` is not empty, the alternate iota over ` ph `
     is a set.  (Contributed by AV, 25-Aug-2022.) $)
  iotan0aiotaex $p |- ( ( iota x ph ) =/= (/) -> ( iota' x ph ) e. _V ) $=
    ( cio c0 wne weu caiota cvv wcel iotanul necon1ai aiotaexb sylib ) ABCZDEAB
    FZABGHIONDABJKABLM $.

  $( The alternate iota over a wff ` ph ` is a set iff the iota and the
     alternate iota over ` ph ` are equal.  (Contributed by AV,
     25-Aug-2022.) $)
  aiotaexaiotaiota $p |- ( ( iota' x ph ) e. _V
                             <-> ( iota x ph ) = ( iota' x ph ) ) $=
    ( caiota cvv wcel weu cio wceq aiotaexb reuaiotaiota bitr3i ) ABCZDEABFABGL
    HABIABJK $.

  ${
    $d x y z $.  $d ph z $.
    $( Theorem 8.19 in [Quine] p. 57.  This theorem is the fundamental property
       of (alternate) iota.  (Contributed by AV, 24-Aug-2022.) $)
    aiotaval $p |- ( A. x ( ph <-> x = y ) -> ( iota' x ph ) = y ) $=
      ( vz weq wb wal caiota cio cv cab csn wceq eusnsn eqcom eubii mpbir eqeq1
      weu eubidv mpbiri absn reuabaiotaiota bitri 3imtr3i iotaval eqtrd ) ABCEF
      BGZABHZABIZCJZABKZUKLZMZULDJLZMZDSZUHUIUJMZUNUQUMUOMZDSZUTUOUMMZDSDCNUSVA
      DUMUOOPQUNUPUSDULUMUORTUAABUKUBUQUJUIMURABDUCUJUIOUDUEABCUFUG $.
  $}

  ${
    $d x y z $.
    $( Example for a defined alternate iota being the empty set, i.e.,
       ` A. y x C_ y ` is a wff satisfied by a unique value ` x ` , namely
       ` x = (/) ` (the empty set is the one and only set which is a subset of
       every set).  This corresponds to ~ iota0def .  (Contributed by AV,
       25-Aug-2022.) $)
    aiota0def $p |- ( iota' x A. y x C_ y ) = (/) $=
      ( vz c0 cvv wcel cv wss wal wceq wb caiota 0ex al0ssb ax-gen weq wi eqeq2
      bibi2d albidv imbi12d aiotaval vtoclg mp2 ) DEFAGZBGHBIZUEDJZKZAIZUFALZDJ
      ZMUHABUENOUFACPZKZAIZUJCGZJZQUIUKQCDEUODJZUNUIUPUKUQUMUHAUQULUGUFUODUERST
      UODUJRUAUFACUBUCUD $.

    $( Example for an undefined alternate iota being no set, i.e.,
       ` A. y y e. x ` is a wff not satisfied by a (unique) value ` x ` (there
       is no set, and therefore certainly no unique set, which contains every
       set).  This is different from ~ iota0ndef , where the iota still is a
       set (the empty set).  (Contributed by AV, 25-Aug-2022.) $)
    aiota0ndef $p |- ( iota' x A. y y e. x ) e/ _V $=
      ( wel wal caiota cvv wnel weu wn wex wa nalset intnanr df-eu mtbir df-nel
      wmo wcel aiotaexb xchbinxr mpbir ) BACBDZAEZFGZUBAHZIUEUBAJZUBAQZKUFUGABL
      MUBANOUDUCFRUEUCFPUBASTUA $.
  $}


$[ set-mbox-av-2reu.mm $]


$[ set-mbox-av-afv_aov.mm $]


$[ set-mbox-av-aux.mm $]


$[ set-mbox-av-nt.mm $]


$[ set-mbox-av-even-odd.mm $]


$[ set-mbox-av-graph.mm $]


$[ set-mbox-av-matrix.mm $]

$[ set-mbox-av-geo.mm $]

$( (End of Alexander van der Vekens's mathbox.) $)
