$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Bertrand's Ballot Problem
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $(
    $d c k i $.
    $d c i M $.
    $d c i N $.
    $d b c i x O $.
    $d i j k C $.
    $d c i j k F $.
    $d b c x E $.
    $d i j k J $.
    $d b c i x O $.
    $d b R $.
    $d k ph $.
  $)

  ${
    $d c M $.  $d c N $.  $d c O $.  $d i M $.  $d i N $.  $d i O $.  $d j M $.
    $d j N $.  $d j O $.  $d k M $.  $d k N $.  $d k O $.

    $( Two candidates A and B participate to an election,
      where A receives ` M ` votes and B receives ` N ` votes.
      Ballots are counted by picking ballot papers one by one,
      and we're evaluating the probability that A is ahead throughout the count

      We number the ballots picked using integers in ` ( 1 ... ( M + N ) ) ` .
      We then characterize a counting ` c ` as the set of indices in the
      counting sequence where A was picked.
      Thus, for a counting ` c C_ ( 1 ... ( M + N ) ) ` :
        "The ith ballot paper picked is for A" is expressed as ` i e. c `
        "The ith ballot paper picked is for B" is expressed as ` -. i e. c `
        "The number of ballot papers for A" is expressed as ` ( # ` c ) `
    $)

    ballotth.m $e |- M e. NN $.
    ballotth.n $e |- N e. NN $.

    $( ` O ` is the universe, all countings where A receives ` M ` votes
       out of ` M + N ` $)
    ballotth.o $e |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M } $.
    $( ` O ` is a set.  (Contributed by Thierry Arnoux, 7-Dec-2016.) $)
    ballotlemoex $p |- O e. _V $=
      ( cv chash cfv wceq c1 caddc co cfz cpw ovex pwex rabex2 ) DHIJAKDLABMNZO
      NZPCGUALTOQRS $.

    $( The size of the universe is a binomial coefficient.  (Contributed by
       Thierry Arnoux, 23-Nov-2016.) $)
    ballotlem1 $p |- ( # ` O ) = ( ( M + N ) _C M ) $=
      ( chash cfv cv wceq c1 caddc co cfz cpw crab cbc wcel cn fveq2i fzfi nnzi
      cfn cz hashbc mp2an cn0 wa pm3.2i nnaddcl nnnn0 mp2b hashfz1 ax-mp oveq1i
      3eqtr2i ) CHIDJHIAKDLABMNZONZPQZHIZUSHIZARNZURARNCUTHGUAUSUDSAUESVCVAKLUR
      UBAEUCDUSAUFUGVBURARURUHSZVBURKATSZBTSZUIURTSVDVEVFEFUJABUKURULUMURUNUOUP
      UQ $.

    ${
      $d c d $.  $d d C $.  $d d M $.  $d d N $.
      $( Elementhood in ` O ` .  (Contributed by Thierry Arnoux,
         17-Apr-2017.) $)
      ballotlemelo $p |- ( C e. O <->
                             ( C C_ ( 1 ... ( M + N ) ) /\ ( # ` C ) = M ) ) $=
        ( vd wcel c1 co cfz chash cfv wceq wa cv fveqeq2 crab caddc cpw cbvrabv
        wss eqtri elrab2 ovex elpw2 anbi1i bitri ) ADJAKBCUALZMLZUBZJZANOBPZQAU
        LUDZUOQIRZNOBPZUOIAUMDUQABNSDERZNOBPZEUMTURIUMTHUTUREIUMUSUQBNSUCUEUFUN
        UPUOAULKUKMUGUHUIUJ $.
    $}

    $( Let ` P ` be the uniform discrete probability measure over ` O ` . $)
    ballotth.p $e |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) ) $.

    ${
      $d c i M $.  $d c i N $.  $d c i x O $.

      $( The probability that the first vote picked in a count is a B.
         (Contributed by Thierry Arnoux, 23-Nov-2016.) $)
      ballotlem2 $p |- ( P ` { c e. O | -. 1 e. c } ) = ( N / ( M + N ) ) $=
        ( vi c1 wcel cfv co c2 wa cle wbr mp2an cv wn crab caddc cmin cbc chash
        cdiv cpw wceq cvv ballotlemoex ssrab2 elpwi2 fveq2 ovex fvmpt ax-mp cfz
        oveq1d an32 cuz wss 2eluzge1 fzss1 sspwi sseli clt 1lt2 1re ltnlei mpbi
        2re elfzle1 mto elelpwi ancom mtbi imnani jca cab ssin wo wb 1le2 1p1e2
        cin cn nnge1 nnrei le2addi eqbrtrri readdcli letri cz nnaddcl nnzi eluz
        mpbir elfzp12 biimpi orcanai oveq1i eleqtrdi ss2abi abid2 ineq1i eqtr3i
        1z inab 3sstr3i sstr mpan2 sylbi velpw wi wal ssab df-ex bicomi con1bii
        dfclel notbii imnang bitr4i 3bitr4ri bitr2i anbi12i 3imtr4i anbi1i cneg
        wex albii cc nncni 2cn ax-1cn 3eqtri eqtri cc0 impbii reqabi fveq2i cfn
        3bitr4i rabbia2 fzfi hashbc 2z eluz1i mpbir2an hashfz addcli negsubdi2i
        subadd23 mp3an negeqi oveq2i negsubi ballotlem1 oveq12i 0le1 0re cr crp
        2m1e1 nngt0i elrpii ltaddrp w3a 0z elfzm11 mpbir3an bcm1n pncan2 ) LFUA
        ZMZUBZFEUCZBNZCDUDOZLUEOZCUFOZUWACUFOZUHOZUWACUEOZUWAUHOZDUWAUHOUVTUVSU
        GNZEUGNZUHOZUWEUVSEUIZMUVTUWJUJUVSEUKCDEFGHIULUVRFEUMUNAUVSAUAZUGNZUWIU
        HOUWJUWKBUWLUVSUJUWMUWHUWIUHUWLUVSUGUOUTJUWHUWIUHUPUQURUWHUWCUWIUWDUHUV
        PUGNCUJZFPUWAUSOZUIZUCZUGNZUWHUWCUWQUVSUGUWNUVRFUWPEUVPLUWAUSOZUIZMZUVR
        QZUWNQUXAUWNQZUVRQUVPUWPMZUWNQUVPEMZUVRQUXAUVRUWNVAUXDUXBUWNUXDUXBUXDUX
        AUVRUWPUWTUVPUWOUWSPLVBNZMUWOUWSVCVDPLUWAVEURVFVGUXDUVQUVQUXDQZUXDUVQQU
        XGLUWOMZUXHPLRSZLPVHSUXIUBVILPVJVMVKVLLPUWAVNVOLUVPUWOVPVOUVQUXDVQVRVSV
        TUVPUWSVCZUVPKUAZLUJZUBZKWAZVCZQZUVPUWOVCZUXBUXDUXPUVPUWSUXNWGZVCZUXQUV
        PUWSUXNWBUXSUXRUWOVCUXQUXKUWSMZUXMQZKWAZUXKUWOMZKWAUXRUWOUYAUYCKUYAUXKL
        LUDOZUWAUSOZUWOUXTUXLUXKUYEMZUXTUXLUYFWCZUWAUXFMZUXTUYGWDUYHLUWARSZLPRS
        PUWARSZUYIWEUYDPUWARWFLCRSZLDRSZUYDUWARSCWHMZUYKGCWIURZDWHMZUYLHDWIURLL
        CDVJVJCGWJZDHWJZWKTWLZLPUWAVJVMCDUYPUYQWMWNTLWOMUWAWOMZUYHUYIWDXIUWAUYM
        UYOUWAWHMZGHCDWPTZWQZLUWAWRTWSUXKLUWAWTURXAXBUYDPUWAUSWFXCXDXEUXTKWAZUX
        NWGUYBUXRUXTUXMKXJVUCUWSUXNKUWSXFXGXHKUWOXFXKUVPUXRUWOXLXMXNUXAUXJUVRUX
        OFUWSXOUXOUXKUVPMZUXMXPKXQZUVRUXMKUVPXRUXLVUDQZKYLZUBVUFUBZKXQZUVRVUEVU
        IVUGVUGVUIUBVUFKXSXTYAUVQVUGKLUVPYBYCVUEVUDUXLQZUBZKXQVUIVUDUXLKYDVUHVU
        KKVUFVUJUXLVUDVQYCYMYEYFYGYHFUWOXOYIUUAYJUXEUXCUVRUWNFEUWTIUUBYJUUEUUFU
        UCUWOUGNZCUFOZUWRUWCUWOUUDMCWOMZVUMUWRUJPUWAUUGCGWQZFUWOCUUHTVULUWBCUFV
        ULUWALYKZUDOZUWBVULUWAPUEOLUDOZUWALPUEOZUDOZVUQUWAPVBNMZVULVURUJVVAUYSU
        YJVUBUYRPUWAUUIUUJUUKPUWAUULURUWAYNMPYNMLYNMVURVUTUJCDCGYOZDHYOZUUMZYPY
        QUWAPLUUOUUPVUSVUPUWAUDPLUEOZYKVUSVUPPLYPYQUUNVVELUVFUUQXHUURYRUWALVVDY
        QUUSYSXCXHXHCDEFGHIUUTUVAYSCYTUWBUSOMZUYTUWEUWGUJVVFVUNYTCRSZCUWAVHSZVU
        OYTLRSUYKVVGUVBUYNYTLCUVCVJUYPWNTCUVDMDUVEMVVHUYPDUYQDHUVGUVHCDUVITYTWO
        MUYSVVFVUNVVGVVHUVJWDUVKVUBCYTUWAUVLTUVMVUACUWAUVNTUWFDUWAUHCYNMDYNMUWF
        DUJVVBVVCCDUVOTXCYR $.
    $}

    $d c i F $.  $d j F $.  $d k F $.
    $( F is the difference between ballots for A and B among the ` i ` first
      ballots picked in a given count ` c ` .
      Those ballots for A are in ` c `, i.e. in ` ( ( 1 ... i ) i^i c ) ` .
      Those ballots for B are out of ` c `, i.e. in ` ( ( 1 ... i ) \ c ) ` $)
    ballotth.f $e |- F = ( c e. O |-> ( i e. ZZ |->
      ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) ) $.

    $d i c $.  $d i C $.
    ${
      $d b O $.  $d b C $.  $d b c $.  $d b i $.  $d i J $.
      ballotlemfval.c $e |- ( ph -> C e. O ) $.
      ballotlemfval.j $e |- ( ph -> J e. ZZ ) $.

      $d i ph $.
      $( The value of ` F ` .  (Contributed by Thierry Arnoux, 23-Nov-2016.) $)
      ballotlemfval $p |- ( ph -> ( ( F ` C ) ` J ) =
        ( ( # ` ( ( 1 ... J ) i^i C ) ) - ( # ` ( ( 1 ... J ) \ C ) ) ) ) $=
        ( chash cfv vb c1 cv cfz co cin cdif cmin cz cvv wcel cmpt simpl ineq2d
        wceq wa fveq2d difeq2d oveq12d mpteq2dva difeq2 mpteq2dv cbvmptv eqtr4i
        ineq2 zex mptex fvmpt syl oveq2 ineq1d difeq1d adantl ovexd fvmptd ) AE
        GUBEUCZUDUEZCUFZSTZVQCUGZSTZUHUEZUBGUDUEZCUFZSTZWCCUGZSTZUHUEZUICFTZUJA
        CJUKWIEUIWBULZUOQUACEUIVQUAUCZUFZSTZVQWKUGZSTZUHUEZULZWJJFWKCUOZEUIWPWB
        WRVPUIUKZUPZWMVSWOWAUHWTWLVRSWTWKCVQWRWSUMZUNUQWTWNVTSWTWKCVQXAURUQUSUT
        FKJEUIVQKUCZUFZSTZVQXBUGZSTZUHUEZULZULUAJWQULPUAKJWQXHWKXBUOZEUIWPXGXIW
        MXDWOXFUHXIWLXCSWKXBVQVEUQXIWNXESWKXBVQVAUQUSVBVCVDEUIWBVFVGVHVIVPGUOZW
        BWHUOAXJVSWEWAWGUHXJVRWDSXJVQWCCVPGUBUDVJZVKUQXJVTWFSXJVQWCCXKVLUQUSVMR
        AWEWGUHVNVO $.

      $( ` ( F `` C ) ` has values in ` ZZ ` .  (Contributed by Thierry Arnoux,
         23-Nov-2016.) $)
      ballotlemfelz $p |- ( ph -> ( ( F ` C ) ` J ) e. ZZ ) $=
        ( cfv wcel c1 cfz co cin chash cdif cmin ballotlemfval cfn cn0 wss fzfi
        cz inss1 ssfi mp2an hashcl ax-mp nn0zi difss zsubcl eqeltrdi ) AGCFSSUA
        GUBUCZCUDZUESZVCCUFZUESZUGUCZUMABCDEFGHIJKLMNOPQRUHVEUMTVGUMTVHUMTVEVDU
        ITZVEUJTVCUITZVDVCUKVIUAGULZVCCUNVCVDUOUPVDUQURUSVGVFUITZVGUJTVJVFVCUKV
        LVKVCCUTVCVFUOUPVFUQURUSVEVGVAUPVB $.
    $}

    ${
      $d i J $.  $d i ph $.
      ballotlemfp1.c $e |- ( ph -> C e. O ) $.
      ballotlemfp1.j $e |- ( ph -> J e. NN ) $.
      $( If the ` J ` th ballot is for A, ` ( F `` C ) ` goes up 1.  If the
         ` J ` th ballot is for B, ` ( F `` C ) ` goes down 1.  (Contributed by
         Thierry Arnoux, 24-Nov-2016.) $)
      ballotlemfp1 $p |- ( ph -> (
         ( -. J e. C -> ( ( F ` C ) ` J ) = ( ( ( F ` C ) ` ( J - 1 ) ) - 1 ) )
      /\ ( J e. C -> ( ( F ` C ) ` J ) = ( ( ( F ` C ) ` ( J - 1 ) ) + 1 ) )
        ) ) $=
        ( c1 wceq wcel wn cfv cmin co wi caddc cfz cin chash cdif ballotlemfval
        wa nnzd adantr cc cfn cn0 wss fzfi inss1 ssfi mp2an hashcl ax-mp nn0cni
        a1i diffi 1cnd subsub4d 1zzd zsubcld oveq1d csn cun cuz cn elnnuz sylib
        fzspl ineq1d indir eqtrdi syl c0 disjsn eqeq1i sylbb1 adantl uneq2d un0
        incom eqtrd fveq2d difeq1d difundir disj3 eqcomd sylan9eq cz uzid uznfz
        3syl difss sseli nsyl jctil hashunsng oveq12d 3eqtr4rd ex addsubd snssi
        sylc dfss2 simpr 3eqtrd difin2 difid ineq1i 0in eqtri 3eqtr4d jca ) AGC
        UAZUBZGCFUCZUCZGSUDUEZYGUCZSUDUEZTZUFYEYHYJSUGUEZTZUFAYFYLAYFUMZYHSGUHU
        EZCUIZUJUCZYPCUKZUJUCZUDUEZYKAYHUUATZYFABCDEFGHIJKLMNOPQAGRUNZULZUOYOSY
        IUHUEZCUIZUJUCZUUECUKZUJUCZUDUEZSUDUEUUGUUISUGUEZUDUEYKUUAYOUUGUUISUUGU
        PUAZYOUUGUUFUQUAZUUGURUAUUEUQUAZUUFUUEUSUUMSYIUTZUUECVAZUUEUUFVBVCZUUFV
        DVEVFZVGUUIUPUAZYOUUIUUHUQUAZUUIURUAUUNUUTUUOUUECVHVEUUHVDVEVFZVGYOVIVJ
        YOYJUUJSUDAYJUUJTZYFABCDEFYIHIJKLMNOPQAGSUUCAVKVLULZUOVMYOYRUUGYTUUKUDY
        OYQUUFUJYOYQUUFGVNZCUIZVOZUUFAYQUVFTZYFAGSVPUCUAZUVGAGVQUAUVHRGVRVSZUVH
        YQUUEUVDVOZCUIUVFUVHYPUVJCSGVTZWAUUEUVDCWBWCWDZUOYOUVFUUFWEVOUUFYOUVEWE
        UUFYFUVEWETZACUVDUIZWETYFUVMCGWFUVNUVEWECUVDWLWGWHZWIWJUUFWKWCWMWNYOYTU
        UHUVDVOZUJUCZUUKYOYSUVPUJAYFYSUUHUVDCUKZVOZUVPAUVHYSUVSTUVIUVHYSUVJCUKU
        VSUVHYPUVJCUVKWOUUEUVDCWPWCWDZYFUVRUVDUUHYFUVDUVRYFUVMUVDUVRTUVOUVDCWQV
        SWRWJWSWNYOGWTUAZUUTGUUHUAZUBZUMUVQUUKTAUWAYFUUCUOYOUWCUUTYOGUUEUAZUWBA
        UWDUBZYFAUWAGGVPUCUAZUWEUUCGXAZGSGXBZXCUOUUHUUEGUUECXDZXEXFUUNUUHUUEUSU
        UTUUOUWIUUEUUHVBVCXGUUHGWTXHXNWMXIXJWMXKAYEYNAYEUMZYHUUAYMAUUBYEUUDUOUW
        JUUGSUGUEZUUIUDUEUUJSUGUEUUAYMUWJUUGSUUIUULUWJUURVGUWJVIUUSUWJUVAVGXLUW
        JYRUWKYTUUIUDUWJYRUVFUJUCZUUFUVDVOZUJUCZUWKAYRUWLTYEAYQUVFUJUVLWNUOYEUW
        LUWNTAYEUVFUWMUJYEUVEUVDUUFYEUVDCUSZUVEUVDTGCXMZUVDCXOVSWJWNWIUWJYEUUMG
        UUFUAZUBZUMUWNUWKTAYEXPUWJUWRUUMUWJUWDUWQUWJUWAUWFUWEAUWAYEUUCUOUWGUWHX
        CUUFUUEGUUPXEXFUUQXGUUFGCXHXNXQUWJYTUVSUJUCZUUHWEVOZUJUCZUUIAYTUWSTYEAY
        SUVSUJUVTWNUOYEUWSUXATAYEUVSUWTUJYEUVRWEUUHYEUWOUVRWETUWPUWOUVRCCUKZUVD
        UIZWEUVDCCXRUXCWEUVDUIWEUXBWEUVDCXSXTUVDYAYBWCWDWJWNWIUWJUWTUUHUJUWTUUH
        TUWJUUHWKVGWNXQXIUWJYJUUJSUGAUVBYEUVCUOVMYCWMXKYD $.

      $d k i j $.  $d j k J $.  $d j k C $.  $d ph k $.
      ballotlemfc0.3 $e |- ( ph ->
                                E. i e. ( 1 ... J ) ( ( F ` C ) ` i ) <_ 0 ) $.
      ballotlemfc0.4 $e |- ( ph -> 0 < ( ( F ` C ) ` J ) ) $.
      $( ` F ` takes value 0 between negative and positive values.
         (Contributed by Thierry Arnoux, 24-Nov-2016.) $)
      ballotlemfc0 $p |- ( ph -> E. k e. ( 1 ... J ) ( ( F ` C ) ` k ) = 0 ) $=
        ( vj cv cfv cc0 wceq cle wbr c1 cfz co crab wrex wral wcel fveq2 breq1d
        wa elrab anbi1i simprlr caddc wn simprl adantrr clt cr cuz fzssuz uzssz
        cz sstri zssre sseli ltp1d 1red readdcld ltnled mpbid syl simprr adantr
        wi simpr fveq2d breq2d wb cn elnnuz sylib eluzfz2 eleq1 anc2li 1eluzge0
        syl5ibrcom fzss1 sseld ax-mp 0red adantl ballotlemfelz zred sylan2 syl6
        elfzelz imp bitr3d ex con2d cmin wo nn1m1nn oveq1 nnzd eqtr3d rexeqtrdv
        fzsn rexsng pm2.65da biortn notnotb mpbird 1cnd eleq2d eqeq2d sylibr 1z
        csn c2 a1i wss mpd breq1 syl2anc simplrr sylan oveq1d 0z adantlrr cfn
        orbi1i elfzp1 nncnd npcand oveq2d orbi2d orcom bitrdi pm5.6 jctil jctir
        bitr4di 3bitr3d biimpd fzaddel syl2an biimp3a 3anidm23 oveq12d 2eluzge1
        1p1e2 biimtrdi syld sylan2d rspccva sylan2br expr con3d mpsyl imdistani
        simpll elfznn ballotlemfp1 simpld pncand zlem1lt sylancl syl21anc ltled
        zcnd bitr4d syl12anc condan simprd mpdan notbid syldan zleltp1 mpan zre
        bitrd letri3d mpbir2and sylan2b c0 ssrab2 fzfi ssfi mp2an rabn0 fimaxre
        wne syl3anc reximddv elrabi anim1i reximi2 ) AFUCZCGUDZUDZUEUFZFEUCZUXI
        UDZUEUGUHZEUIHUJUKZULZUMUXKFUXOUMAUBUCZUXHUGUHZUBUXPUNZUXKFUXPUXHUXPUOZ
        UXSURAUXHUXOUOZUXJUEUGUHZURZUXSURZUXKUXTUYCUXSUXNUYBEUXHUXOUXLUXHUFUXMU
        XJUEUGUXLUXHUXIUPUQUSUTAUYDURZUXKUYBUEUXJUGUHZAUYAUYBUXSVAUYEUYFUXJUIVB
        UKZUEUGUHZVCZUYEUXHUIVBUKZUXIUDZUEUGUHZVCZUYIUYEUYJUXHUGUHZVCZUYMUYEUYA
        UYOAUYCUYAUXSAUYAUYBVDZVEUYAUXHUYJVFUHUYOUYAUXHUXOVGUXHUXOVKVGUXOUIVHUD
        ZVKUIHVIUIVJVLVMVLZVNZVOUYAUXHUYJUYSUYAUXHUIUYSUYAVPVQVRVSVTZUYEUXSUYJU
        XOUOZUYOUYMWCAUYCUXSWAAUYCVUAUXSAUYCVUAAUYBUXHHUFZVCZUYAVUAAVUBUYBAVUBU
        YBVCZAVUBURZUEHUXIUDZVFUHZVUDAVUGVUBUAWBVUEUEUXJVFUHZVUGVUDVUEUXJVUFUEV
        FVUEUXHHUXIAVUBWDWEWFAVUBVUHVUDWGZAVUBAUYAURVUIAVUBUYAAUYAVUBHUXOUOZAHU
        YQUOZVUJAHWHUOZVUKSHWIWJUIHWKVTUXHHUXOWLWOWMUYAAUXHUEHUJUKZUOZVUIUIUEVH
        UDUOZUYAVUNWCWNVUOUXOVUMUXHUIUEHWPZWQWRZAVUNURZUEUXJVURWSVURUXJVURBCDEG
        UXHIJKLMNOPQACKUOZVUNRWBVUNUXHVKUOZAUXHUEHXEWTXAZXBVRXCXDXFXGVSXHXIAUYA
        VUCURZUXHUIHUIXJUKZUJUKUOZVUAAUYAVUBVVDXKZWCVVBVVDWCAUYAVVEAUYAVVDVUBXK
        ZVVEAUXHUIVVCUIVBUKZUJUKZUOZVVDUXHVVGUFZXKZUYAVVFAVVCUYQUOZVVIVVKWGAVVC
        WHUOZVVLAVVMHUIUFZVVMXKZAVULVVOSHXLVTAVVMVVNVCZVCZVVMXKZVVOAVVPVVMVVRWG
        AVVNVUFUEUGUHZAVVNURZUXNEHYHZUMZVVSVVTUXNEUXOVWAAUXNEUXOUMZVVNTWBVVTHHU
        JUKZUXOVWAVVNVWDUXOUFAHUIHUJXMWTAVWDVWAUFZVVNAHVKUOVWEAHSXNZHXQVTWBXOXP
        AVWBVVSWGZVVNAVULVWGSUXNVVSEHWHUXLHUFUXMVUFUEUGUXLHUXIUPUQXRVTWBVSVVTVU
        GVVSVCZAVUGVVNUAWBAVUGVWHWGVVNAUEVUFAWSAVUFABCDEGHIJKLMNOPQRVWFXAXBVRWB
        VSXSVVPVVMXTVTVVNVVQVVMVVNYAUUAUULYBZVVCWIWJUXHUIVVCUUBVTAVVHUXOUXHAVVG
        HUIUJAHUIAHSUUCAYCUUDZUUEYDAVVJVUBVVDAVVGHUXHVWJYEUUFUUMVVDVUBUUGUUHUUN
        UYAVUBVVDUUIYFAVVDVUAAVVDURUYJUIUIVBUKZVVGUJUKZUOZVUAAVVDVWMAVVDVVDVWMA
        UIVKUOZVVCVKUOZURVUTVWNURVVDVWMWGVVDAVWOVWNAVVCVWIXNYGUUJVVDVUTVWNUXHUI
        VVCXEYGUUKUXHUIUIVVCUUOUUPUUQUURAVWMVUAWCVVDAVWMUYJYIHUJUKZUOVUAAVWLVWP
        UYJAVWKYIVVGHUJVWKYIUFAUVAYJVWJUUSYDVWPUXOUYJYIUYQUOVWPUXOYKUUTYIUIHWPW
        RVNUVBWBYLXHUVCUVDZXFZVEZUXSVUAURUYLUYNUXSVUAUYLUYNVUAUYLURUXSUYJUXPUOU
        YNUXNUYLEUYJUXOUXLUYJUFUXMUYKUEUGUXLUYJUXIUPUQUSUXRUYNUBUYJUXPUXQUYJUXH
        UGYMUVEUVFZUVGUVHYNYLUYEUYKUYGUFZUYMUYIWGUYEUYJCUOZVXAUYEVXBUYNUYEVXBVC
        ZURUXSVUAUYLUYNAUYCUXSVXCYOUYEVUAVXCVWSWBAUYCVXCUYLUXSAUYCURZVXCURZUYKU
        EVXEAUYJVUMUOZUYKVGUOAUYCVXCUVKZVUOVXEVUAVXFWNVXDVUAVXCVWRWBVUOUXOVUMUY
        JVUPWQUVIAVXFURZUYKVXHBCDEGUYJIJKLMNOPQAVUSVXFRWBVXFUYJVKUOAUYJUEHXEWTX
        AXBYNVXEWSVXEUYBUYKUEVFUHZAUYAUYBVXCYOVXEAVUNUYKUXJUIXJUKZUFZUYBVXIWGVX
        GVXEUYAVUNVXDUYAVXCUYPWBZVUQVTVXEUYKUYJUIXJUKZUXIUDZUIXJUKZUFZVXKVXDAVU
        AURZVXCVXPAUYCVUAVWQUVJZVXQVXCVXPVXQVXCVXPWCZVXBUYKVXNUIVBUKZUFZWCZVXQB
        CDEGUYJIJKLMNOPQAVUSVUARWBVUAUYJWHUOAUYJHUVLWTUVMZUVNXFYPVXEUYAVXPVXKWG
        VXLUYAVXOVXJUYKUYAVXNUXJUIXJUYAVXMUXHUXIUYAUXHUIUYAUXHUXHUIHXEUVTUYAYCU
        VOWEZYQYEVTVSVURVXKURUYBVXJUEVFUHZVXIVURUYBVYEWGZVXKVURUXJVKUOZUEVKUOZV
        YFVVAYRUXJUEUVPUVQWBVXKVXIVYEWGVURUYKVXJUEVFYMWTUWAUVRVSUVSYSVWTUWBUYEU
        YOVXCUYTWBUWCAUYCVXBVXAUXSVXDVXBURZVYAVXAVXDVXQVXBVYAVXRVXQVXBVYAVXQVXS
        VYBVYCUWDXFYPVYIUYAVYAVXAWGVXDUYAVXBUYPWBUYAVXTUYGUYKUYAVXNUXJUIVBVYDYQ
        YEVTVSYSUWEVXAUYLUYHUYKUYGUEUGYMUWFVTVSUYEVYGUYFUYIWGAUYCVYGUXSAUYCVUNV
        YGVXDUYAVUNUYPVUQVTVVAUWGVEZVYGUYFUEUYGVFUHZUYIVYHVYGUYFVYKWGYRUEUXJUWH
        UWIVYGUEUYGVYGWSVYGUXJUIUXJUWJVYGVPVQVRUWKVTYBUYEUXJUEUYEUXJVYJXBUYEWSU
        WLUWMUWNAUXPVGYKZUXPYTUOZUXPUWOUXBZUXSFUXPUMVYLAUXPUXOVGUXNEUXOUWPZUYRV
        LYJVYMAUXOYTUOUXPUXOYKVYMUIHUWQVYOUXOUXPUWRUWSYJAVWCVYNTUXNEUXOUWTYFFUB
        UXPUXAUXCUXDUXKUXKFUXPUXOUXTUYAUXKUXNEUXHUXOUXEUXFUXGVT $.
    $}

    ${
      $d i J $.  $d i ph $.  $d k i j $.  $d j k J $.  $d j k C $.  $d ph k $.
      ballotlemfcc.c $e |- ( ph -> C e. O ) $.
      ballotlemfcc.j $e |- ( ph -> J e. NN ) $.
      ballotlemfcc.3 $e |- ( ph ->
                                E. i e. ( 1 ... J ) 0 <_ ( ( F ` C ) ` i ) ) $.
      ballotlemfcc.4 $e |- ( ph -> ( ( F ` C ) ` J ) < 0 ) $.
      $( ` F ` takes value 0 between positive and negative values.
         (Contributed by Thierry Arnoux, 2-Apr-2017.) $)
      ballotlemfcc $p |- ( ph -> E. k e. ( 1 ... J ) ( ( F ` C ) ` k ) = 0 ) $=
        ( vj cv cfv cc0 wceq cle wbr c1 cfz co crab wrex wral wcel fveq2 breq2d
        wa elrab anbi1i cmin wn caddc simprl adantrr clt cr cz cuz fzssuz uzssz
        sstri zssre sseli ltp1d 1red readdcld ltnled mpbid syl wi simprr adantr
        simpr fveq2d breq1d wb cn elnnuz sylib eleq1 syl5ibrcom anc2li 1eluzge0
        eluzfz2 fzss1 sseld ax-mp elfzelz adantl ballotlemfelz zred 0red sylan2
        syl6 imp bitr3d ex con2d nn1m1nn csn oveq1 nnzd eqtr3d rexeqtrdv rexsng
        wo fzsn pm2.65da biortn notnotb orbi1i mpbird 1cnd eleq2d eqeq2d sylibr
        1z c2 a1i wss mpd syl2anc simplrr sylan oveq1d 0z breq2 adantlrr cfn c0
        elfzp1 nncnd npcand oveq2d orbi2d orcom bitrdi biimpd pm5.6 jctil jctir
        bitr4di 3bitr3d fzaddel syl2an biimp3a 3anidm23 1p1e2 2eluzge1 biimtrdi
        oveq12d syld sylan2d breq1 rspccva sylan2br expr con3d simpll imdistani
        mpsyl elfznn ballotlemfp1 simprd pncand zleltp1 sylancr bitr4d syl21anc
        zcnd ltled syl12anc mtand simpld mpdan notbid syldan mpan2 zre resubcld
        zlem1lt bitrd simprlr letri3d mpbir2and sylan2b ssrab2 fzfi mp2an rabn0
        wne ssfi fimaxre syl3anc reximddv elrabi anim1i reximi2 ) AFUCZCGUDZUDZ
        UEUFZFUEEUCZUXKUDZUGUHZEUIHUJUKZULZUMUXMFUXQUMAUBUCZUXJUGUHZUBUXRUNZUXM
        FUXRUXJUXRUOZUYAURAUXJUXQUOZUEUXLUGUHZURZUYAURZUXMUYBUYEUYAUXPUYDEUXJUX
        QUXNUXJUFUXOUXLUEUGUXNUXJUXKUPUQUSUTAUYFURZUXMUXLUEUGUHZUYDUYGUYHUEUXLU
        IVAUKZUGUHZVBZUYGUEUXJUIVCUKZUXKUDZUGUHZVBZUYKUYGUYLUXJUGUHZVBZUYOUYGUY
        CUYQAUYEUYCUYAAUYCUYDVDZVEUYCUXJUYLVFUHUYQUYCUXJUXQVGUXJUXQVHVGUXQUIVIU
        DZVHUIHVJUIVKVLVMVLZVNZVOUYCUXJUYLVUAUYCUXJUIVUAUYCVPVQVRVSVTZUYGUYAUYL
        UXQUOZUYQUYOWAAUYEUYAWBAUYEVUCUYAAUYEVUCAUYDUXJHUFZVBZUYCVUCAVUDUYDAVUD
        UYDVBZAVUDURZHUXKUDZUEVFUHZVUFAVUIVUDUAWCVUGUXLUEVFUHZVUIVUFVUGUXLVUHUE
        VFVUGUXJHUXKAVUDWDWEWFAVUDVUJVUFWGZAVUDAUYCURVUKAVUDUYCAUYCVUDHUXQUOZAH
        UYSUOZVULAHWHUOZVUMSHWIWJUIHWOVTUXJHUXQWKWLWMUYCAUXJUEHUJUKZUOZVUKUIUEV
        IUDUOZUYCVUPWAWNVUQUXQVUOUXJUIUEHWPZWQWRZAVUPURZUXLUEVUTUXLVUTBCDEGUXJI
        JKLMNOPQACKUOZVUPRWCVUPUXJVHUOZAUXJUEHWSWTXAZXBVUTXCVRXDXEXFXGVSXHXIAUY
        CVUEURZUXJUIHUIVAUKZUJUKUOZVUCAUYCVUDVVFXQZWAVVDVVFWAAUYCVVGAUYCVVFVUDX
        QZVVGAUXJUIVVEUIVCUKZUJUKZUOZVVFUXJVVIUFZXQZUYCVVHAVVEUYSUOZVVKVVMWGAVV
        EWHUOZVVNAVVOHUIUFZVVOXQZAVUNVVQSHXJVTAVVOVVPVBZVBZVVOXQZVVQAVVRVVOVVTW
        GAVVPUEVUHUGUHZAVVPURZUXPEHXKZUMZVWAVWBUXPEUXQVWCAUXPEUXQUMZVVPTWCVWBHH
        UJUKZUXQVWCVVPVWFUXQUFAHUIHUJXLWTAVWFVWCUFZVVPAHVHUOVWGAHSXMZHXRVTWCXNX
        OAVWDVWAWGZVVPAVUNVWISUXPVWAEHWHUXNHUFUXOVUHUEUGUXNHUXKUPUQXPVTWCVSVWBV
        UIVWAVBZAVUIVVPUAWCAVUIVWJWGVVPAVUHUEAVUHABCDEGHIJKLMNOPQRVWHXAXBAXCVRW
        CVSXSVVRVVOXTVTVVPVVSVVOVVPYAYBUUMYCZVVEWIWJUXJUIVVEUUBVTAVVJUXQUXJAVVI
        HUIUJAHUIAHSUUCAYDUUDZUUEYEAVVLVUDVVFAVVIHUXJVWLYFUUFUUNVVFVUDUUGUUHUUI
        UYCVUDVVFUUJYGAVVFVUCAVVFURUYLUIUIVCUKZVVIUJUKZUOZVUCAVVFVWOAVVFVVFVWOA
        UIVHUOZVVEVHUOZURVVBVWPURVVFVWOWGVVFAVWQVWPAVVEVWKXMYHUUKVVFVVBVWPUXJUI
        VVEWSYHUULUXJUIUIVVEUUOUUPUUQUURAVWOVUCWAVVFAVWOUYLYIHUJUKZUOVUCAVWNVWR
        UYLAVWMYIVVIHUJVWMYIUFAUUSYJVWLUVBYEVWRUXQUYLYIUYSUOVWRUXQYKUUTYIUIHWPW
        RVNUVAWCYLXHUVCUVDZXFZVEZUYAVUCURUYNUYPUYAVUCUYNUYPVUCUYNURUYAUYLUXRUOU
        YPUXPUYNEUYLUXQUXNUYLUFUXOUYMUEUGUXNUYLUXKUPUQUSUXTUYPUBUYLUXRUXSUYLUXJ
        UGUVEUVFUVGZUVHUVIYMYLUYGUYMUYIUFZUYOUYKWGUYGUYLCUOZVBZVXCUYGVXDUYPVUBU
        YGVXDURUYAVUCUYNUYPAUYEUYAVXDYNUYGVUCVXDVXAWCAUYEVXDUYNUYAAUYEURZVXDURZ
        UEUYMVXGXCVXGAUYLVUOUOZUYMVGUOAUYEVXDUVJZVUQVXGVUCVXHWNVXFVUCVXDVWTWCVU
        QUXQVUOUYLVURWQUVLAVXHURZUYMVXJBCDEGUYLIJKLMNOPQAVVAVXHRWCVXHUYLVHUOAUY
        LUEHWSWTXAXBYMVXGUYDUEUYMVFUHZAUYCUYDVXDYNVXGAVUPUYMUXLUIVCUKZUFZUYDVXK
        WGVXIVXGUYCVUPVXFUYCVXDUYRWCZVUSVTVXGUYMUYLUIVAUKZUXKUDZUIVCUKZUFZVXMVX
        FAVUCURZVXDVXRAUYEVUCVWSUVKZVXSVXDVXRVXSVXEUYMVXPUIVAUKZUFZWAZVXDVXRWAZ
        VXSBCDEGUYLIJKLMNOPQAVVAVUCRWCVUCUYLWHUOAUYLHUVMWTUVNZUVOXFYOVXGUYCVXRV
        XMWGVXNUYCVXQVXLUYMUYCVXPUXLUIVCUYCVXOUXJUXKUYCUXJUIUYCUXJUXJUIHWSUWAUY
        CYDUVPWEZYPYFVTVSVUTVXMURUYDUEVXLVFUHZVXKVUTUYDVYGWGZVXMVUTUEVHUOZUXLVH
        UOZVYHYQVVCUEUXLUVQUVRWCVXMVXKVYGWGVUTUYMVXLUEVFYRWTUVSUVTVSUWBYSVXBUWC
        UWDAUYEVXEVXCUYAVXFVXEURZVYBVXCVXFVXSVXEVYBVXTVXSVXEVYBVXSVYCVYDVYEUWEX
        FYOVYKUYCVYBVXCWGVXFUYCVXEUYRWCUYCVYAUYIUYMUYCVXPUXLUIVAVYFYPYFVTVSYSUW
        FVXCUYNUYJUYMUYIUEUGYRUWGVTVSUYGVYJUYHUYKWGAUYEVYJUYAAUYEVUPVYJVXFUYCVU
        PUYRVUSVTVVCUWHVEZVYJUYHUYIUEVFUHZUYKVYJVYIUYHVYMWGYQUXLUEUWLUWIVYJUYIU
        EVYJUXLUIUXLUWJVYJVPUWKVYJXCVRUWMVTYCAUYCUYDUYAUWNUYGUXLUEUYGUXLVYLXBUY
        GXCUWOUWPUWQAUXRVGYKZUXRYTUOZUXRUUAUXBZUYAFUXRUMVYNAUXRUXQVGUXPEUXQUWRZ
        UYTVLYJVYOAUXQYTUOUXRUXQYKVYOUIHUWSVYQUXQUXRUXCUWTYJAVWEVYPTUXPEUXQUXAY
        GFUBUXRUXDUXEUXFUXMUXMFUXRUXQUYBUYCUXMUXPEUXJUXQUXGUXHUXIVT $.
    $}

    ${
      $d b c M $.  $d b C $.
      $( ` ( F `` C ) ` finishes counting at ` ( M - N ) ` .  (Contributed by
         Thierry Arnoux, 25-Nov-2016.) $)
      ballotlemfmpn $p |- ( C e. O ->
                                     ( ( F ` C ) ` ( M + N ) ) = ( M - N ) ) $=
        ( wcel co cfv chash cmin wceq vb caddc c1 cfz cin cdif id cz cn nnaddcl
        mp2an nnzi a1i ballotlemfval wss cpw crab ssrab2 eqsstri elpwid sseqin2
        sseli sylib fveq2d cab rabssab eleq2s fveqeq2 cbvabv elab2g mpbid eqtrd
        cv cfn fzfi hashssdif sylancr cn0 nnnn0i hashfz1 mp1i oveq12d cc pncan2
        nncni 3eqtrd ) BHOZFGUBPZBEQQUCWHUDPZBUEZRQZWIBUFRQZSPFGSPWGABCDEWHFGHI
        JKLMNWGUGWHUHOWGWHFUIOGUIOWHUIOJKFGUJUKZULUMUNWGWKFWLGSWGWKBRQZFWGWJBRW
        GBWIUOZWJBTWGBWIHWIUPZBHIVMZRQFTZIWPUQZWPLWRIWPURUSVBUTZBWIVAVCVDWGBWRI
        VEZOZWNFTZXBBWSHWSXABWRIWPVFVBLVGUAVMZRQFTZXCUABXAHXDBFRVHWRXEIUAWQXDFR
        VHVIVJVKZVLWGWLWIRQZWNSPZWHFSPZGWGWIVNOWOWLXHTUCWHVOWTWIBVPVQWGXGWHWNFS
        WHVROXGWHTWGWHWMVSWHVTWAXFWBXIGTZWGFWCOGWCOXJFJWEGKWEFGWDUKUMWFWBVL $.
    $}

    $( ` ( F `` C ) ` always starts counting at 0 .  (Contributed by Thierry
       Arnoux, 25-Nov-2016.) $)
    ballotlemfval0 $p |- ( C e. O -> ( ( F ` C ) ` 0 ) = 0 ) $=
      ( cc0 cfv co chash c0 eqtri wcel cfz cin cdif cmin 0zd ballotlemfval fz10
      c1 id ineq1i incom 3eqtr2i fveq2i hash0 difeq1i 0dif oveq12i 0m0e0 eqtrdi
      in0 ) BHUAZOBEPPUIOUBQZBUCZRPZVCBUDZRPZUEQZOVBABCDEOFGHIJKLMNVBUJVBUFUGVH
      OOUEQOVEOVGOUEVESRPZOVDSRVDSBUCBSUCSVCSBUHUKBSULBVAUMUNUOTVGVIOVFSRVFSBUD
      SVCSBUHUPBUQTUNUOTURUSTUT $.

    $( E is the event where A is strictly ahead throughout the count. $)
    ballotth.e $e |- E = { c e. O | A. i e. ( 1 ... ( M + N ) )
      0 < ( ( F ` c ) ` i ) } $.

    ${
      $d c d $.  $d d i $.  $d d C $.  $d d F $.  $d d M $.  $d d N $.
      $d d O $.
      $( Elements of ` E ` .  (Contributed by Thierry Arnoux, 14-Dec-2016.) $)
      ballotleme $p |- ( C e. E <->
        ( C e. O /\ A. i e. ( 1 ... ( M + N ) ) 0 < ( ( F ` C ) ` i ) ) ) $=
        ( vd cc0 cfv clt cv wbr c1 caddc co cfz wral wceq fveq1d breq2d ralbidv
        fveq2 crab cbvrabv eqtri elrab2 ) RDUAZQUAZFSZSZTUBZDUCGHUDUEUFUEZUGZRU
        QBFSZSZTUBZDVBUGQBIEURBUHZVAVFDVBVGUTVERTVGUQUSVDURBFULUIUJUKERUQJUAZFS
        ZSZTUBZDVBUGZJIUMVCQIUMPVLVCJQIVHURUHZVKVADVBVMVJUTRTVMUQVIUSVHURFULUIU
        JUKUNUOUP $.
    $}

    ${
      $d i j C $.  $d c i F $.  $d j F $.  $d j M $.  $d j N $.  $d j O $.
      $( Elements of ` ( O \ E ) ` .  (Contributed by Thierry Arnoux,
         7-Dec-2016.) $)
      ballotlemodife $p |- ( C e. ( O \ E ) <->
        ( C e. O /\ E. i e. ( 1 ... ( M + N ) ) ( ( F ` C ) ` i ) <_ 0 ) ) $=
        ( vj wcel wn wa cdif cv cfv cc0 cle wbr c1 caddc co cfz wrex eldif wral
        clt wo wi df-or pm3.24 a1bi bitr4i ballotleme notbii anbi2i andi 3bitri
        ianor cr wss fz1ssfz0 a1i sseld imdistani simpl cz adantl ballotlemfelz
        wsb elfzelz zred sbimi sbv clelsb1 anbi12i bitri nfv fveq2 eleq1d sbiev
        sban weq 3imtr3i syl 0red lenltd rexbidva rexnal bitrdi pm5.32i 3bitr4i
        ) BIEUARBIRZBERZSZTZWTDUBZBFUCZUCZUDUEUFZDUGGHUHUIZUJUIZUKZTZBIEULWTWTS
        ZTZWTUDXFUNUFZDXIUMZSZTZUOZXQXCXKXRXMSZXQUPXQXMXQUQXSXQWTURUSUTXCWTWTXO
        TZSZTWTXLXPUOZTXRXBYAWTXAXTABCDEFGHIJKLMNOPVAVBVCYAYBWTWTXOVFVCWTXLXPVD
        VEWTXJXPWTXJXNSZDXIUKXPWTXGYCDXIWTXDXIRZTZXFUDYEWTXDUDXHUJUIZRZTZXFVGRZ
        WTYDYGWTXIYFXDXIYFVHWTXHVIVJVKVLWTQUBZYFRZTZQDVQZYJXEUCZVGRZQDVQYHYIYLY
        OQDYLYNYLABCDFYJGHIJKLMNOWTYKVMYKYJVNRWTYJUDXHVRVOVPVSVTYMWTQDVQZYKQDVQ
        ZTYHWTYKQDWIYPWTYQYGWTQDWAQDYFWBWCWDYOYIQDYIQWEQDWJYNXFVGYJXDXEWFWGWHWK
        WLYEWMWNWOXNDXIWPWQWRWSWD $.
    $}

    $( If the first pick is a vote for B, A is not ahead throughout the count.
       (Contributed by Thierry Arnoux, 25-Nov-2016.) $)
    ballotlem4 $p |- ( C e. O -> ( -. 1 e. C -> -. C e. E ) ) $=
      ( wcel c1 cc0 clt wn wa cv cfv wbr caddc co cfz wral cuz cn nnaddcl mp2an
      wrex elnnuz mpbi eluzfz1 ax-mp cmin cle 0le1 0re 1re lenlti cr wb ltsub13
      mp3an 0m0e0 breq2i bitri mtbir fveq2i ballotlemfval0 eqtrid oveq1d breq2d
      1m1e0 mtbiri adantr wi simpl 1nn a1i ballotlemfp1 simpld mpan2 imp mtbird
      wceq fveq2 notbid rspcev sylancr rexnal sylib ballotleme simprbi nsyl ex
      ) BIQZRBQZUAZBEQZUAXAXCUBZSDUCZBFUDZUDZTUEZDRGHUFUGZUHUGZUIZXDXEXIUAZDXKU
      NZXLUAXERXKQZSRXGUDZTUEZUAZXNXJRUJUDQZXOXJUKQZXSGUKQHUKQXTKLGHULUMXJUOUPR
      XJUQURZXEXQSRRUSUGZXGUDZRUSUGZTUEZXAYEUAXCXAYESSRUSUGZTUEZYGRSTUEZSRUTUEY
      HUAVASRVBVCVDUPYGRSSUSUGZTUEZYHSVEQZYKRVEQYGYJVFVBVBVCSSRVGVHYISRTVIVJVKV
      LXAYDYFSTXAYCSRUSXAYCSXGUDSYBSXGVRVMABCDFGHIJKLMNOVNVOVPVQVSVTXEXPYDSTXAX
      CXPYDWJZXAXOXCYLWAZYAXAXOUBZYMXBXPYCRUFUGWJWAYNABCDFRGHIJKLMNOXAXOWBRUKQY
      NWCWDWEWFWGWHVQWIXMXRDRXKXFRWJZXIXQYOXHXPSTXFRXGWKVQWLWMWNXIDXKWOWPXDXAXL
      ABCDEFGHIJKLMNOPWQWRWSWT $.

    $( From now on, we assume that A wins the poll. $)
    ballotth.mgtn $e |- N < M $.

    $d i k E $.  $d k C $.
    $( If A is not ahead throughout, there is a ` k ` where votes are tied.
       (Contributed by Thierry Arnoux, 1-Dec-2016.) $)
    ballotlem5 $p |- ( C e. ( O \ E ) ->
      E. k e. ( 1 ... ( M + N ) ) ( ( F ` C ) ` k ) = 0 ) $=
      ( wcel co cdif caddc eldifi cn a1i nnaddcld cv cfv cc0 cle ballotlemodife
      wbr cfz wrex simprbi cmin nnrei posdifi mpbi wceq ballotlemfmpn breqtrrid
      c1 clt syl ballotlemfc0 ) BJFUASZABCDEGHIUBTZHIJKLMNOPBJFUCZVGHIHUDSVGLUE
      IUDSVGMUEUFVGBJSZDUGBGUHZUHUIUJULDVCVHUMTUNABCDFGHIJKLMNOPQUKUOVGUIHIUPTZ
      VHVKUHZVDIHVDULUIVLVDULRIHIMUQHLUQURUSVGVJVMVLUTVIABCDGHIJKLMNOPVAVEVBVF
      $.

    $( Let I be the first time a tie is reached in a given count. $)
    ballotth.i $e |- I = ( c e. ( O \ E ) |-> inf ( { k e. ( 1 ... ( M + N ) )
      | ( ( F ` c ) ` k ) = 0 } , RR , < ) ) $.

    $d I k $.  $d c d k $.  $d c i k E $.
    ${
      $d d C $.  $d d E $.  $d d F $.  $d d M $.  $d d N $.  $d d O $.
      $( Value of ` I ` for a given counting ` C ` .  (Contributed by Thierry
         Arnoux, 1-Dec-2016.)  (Revised by AV, 6-Oct-2020.) $)
      ballotlemi $p |- ( C e. ( O \ E ) -> ( I ` C ) = inf (
       { k e. ( 1 ... ( M + N ) ) | ( ( F ` C ) ` k ) = 0 } , RR , < ) ) $=
        ( vd cv cfv cc0 wceq c1 caddc co cfz crab cr clt cinf cdif fveq2 fveq1d
        eqeq1d rabbidv infeq1d cmpt cbvmptv eqtri ltso infex fvmpt ) UABEUBZUAU
        BZGUCZUCZUDUEZEUFIJUGUHUIUHZUJZUKULUMZVFBGUCZUCZUDUEZEVKUJZUKULUMKFUNZH
        VGBUEZUKVLVQULVSVJVPEVKVSVIVOUDVSVFVHVNVGBGUOUPUQURUSHLVRVFLUBZGUCZUCZU
        DUEZEVKUJZUKULUMZUTUAVRVMUTTLUAVRWEVMVTVGUEZUKWDVLULWFWCVJEVKWFWBVIUDWF
        VFWAVHVTVGGUOUPUQURUSVAVBUKVQULVCVDVE $.
    $}

    $( Properties of ` ( I `` C ) ` .  (Contributed by Thierry Arnoux,
       12-Dec-2016.)  (Revised by AV, 6-Oct-2020.) $)
    ballotlemiex $p |- ( C e. ( O \ E ) -> ( ( I ` C ) e. ( 1 ... ( M + N ) )
      /\ ( ( F ` C ) ` ( I ` C ) ) = 0 ) ) $=
      ( cdif wcel cfv cv cc0 wceq c1 caddc co cfz crab wa cr clt ballotlemi wor
      cinf cfn c0 wne wss ltso a1i fzfi ssrab2 ssfi mp2an wrex ballotlem5 rabn0
      sylibr cz fzssuz uzssz sstri zssre fiinfcl syl13anc eqeltrd fveqeq2 elrab
      cuz sylib ) BKFUAUBZBHUCZEUDZBGUCZUCUEUFZEUGIJUHUIZUJUIZUKZUBWEWJUBWEWGUC
      UEUFZULWDWEWKUMUNUQZWKABCDEFGHIJKLMNOPQRSTUOWDUMUNUPZWKURUBZWKUSUTZWKUMVA
      ZWMWKUBWNWDVBVCWOWDWJURUBWKWJVAWOUGWIVDWHEWJVEZWJWKVFVGVCWDWHEWJVHWPABCDE
      FGIJKLMNOPQRSVIWHEWJVJVKWQWDWKWJUMWRWJVLUMWJUGWBUCVLUGWIVMUGVNVOVPVOVOVCU
      MWKUNVQVRVSWHWLEWEWJWFWEUEWGVTWAWC $.

    $d c E $.  $d i I $.
    ${
      $d c k y z $.  $d y z C $.  $d y z F $.  $d y z M $.  $d y z N $.
      $( The first tie cannot be reached at the first pick.  (Contributed by
         Thierry Arnoux, 12-Mar-2017.) $)
      ballotlemi1 $p |- ( ( C e. ( O \ E ) /\ -. 1 e. C ) ->
                                                           ( I ` C ) =/= 1 ) $=
        ( cdif wcel c1 wn wa cfv wceq cc0 cmin co 0re 1re resubcli clt wbr 0lt1
        cr wb ltsub23 mp3an 0m0e0 breq1i bitr2i mpbi gtneii nesymi caddc eldifi
        wi cn 1nn ballotlemfp1 simpld 1m1e0 fveq2i oveq1i ballotlemfval0 adantr
        a1i imp syl oveq1d 3eqtrrd eqeq1d mtbii cfz ballotlemiex simprd fveqeq2
        ad2antrr adantl mpbid mtand neqned ) BKFUAUBZUCBUBZUDZUEZBHUFZUCWRWSUCU
        GZUCBGUFZUFZUHUGZWRUHUCUIUJZUHUGXCUHXDXDUHUHUCUKULUMUHUCUNUOZXDUHUNUOZU
        PXFUHUHUIUJZUCUNUOZXEUHUQUBZUCUQUBXIXFXHURUKULUKUHUCUHUSUTXGUHUCUNVAVBV
        CVDVEVFWRXDXBUHWRXBUCUCUIUJZXAUFZUCUIUJZUHXAUFZUCUIUJZXDWOWQXBXLUGZWOWQ
        XOVIWPXBXKUCVGUJUGVIWOABCDGUCIJKLMNOPQBKFVHZUCVJUBWOVKVSVLVMVTXLXNUGWRX
        KXMUCUIXJUHXAVNVOVPVSWRXMUHUCUIWOXMUHUGZWQWOBKUBXQXPABCDGIJKLMNOPQVQWAV
        RWBWCWDWEWRWTUEWSXAUFUHUGZXCWOXRWQWTWOWSUCIJVGUJWFUJUBXRABCDEFGHIJKLMNO
        PQRSTWGWHWJWTXRXCURWRWSUCUHXAWIWKWLWMWN $.

      $( The first tie cannot be reached at the first pick.  (Contributed by
         Thierry Arnoux, 4-Apr-2017.) $)
      ballotlemii $p |- ( ( C e. ( O \ E ) /\ 1 e. C ) -> ( I ` C ) =/= 1 ) $=
        ( cdif wcel c1 wa cfv wceq caddc co 1e0p1 ax-1ne0 eqnetrri neii cmin wn
        cc0 eldifi 1nn a1i ballotlemfp1 simprd imp fveq2i oveq1i ballotlemfval0
        wi cn 1m1e0 adantr oveq1d 3eqtrrd eqeq1d mtbii ballotlemiex ad2antrr wb
        syl cfz fveqeq2 adantl mpbid mtand neqned ) BKFUAUBZUCBUBZUDZBHUEZUCWEW
        FUCUFZUCBGUEZUEZUOUFZWEUOUCUGUHZUOUFWJWKUOUCWKUOUIUJUKULWEWKWIUOWEWIUCU
        CUMUHZWHUEZUCUGUHZUOWHUEZUCUGUHZWKWCWDWIWNUFZWCWDUNWIWMUCUMUHUFVEWDWQVE
        WCABCDGUCIJKLMNOPQBKFUPZUCVFUBWCUQURUSUTVAWNWPUFWEWMWOUCUGWLUOWHVGVBVCU
        RWEWOUOUCUGWCWOUOUFZWDWCBKUBWSWRABCDGIJKLMNOPQVDVPVHVIVJVKVLWEWGUDWFWHU
        EUOUFZWJWCWTWDWGWCWFUCIJUGUHVQUHUBWTABCDEFGHIJKLMNOPQRSTVMUTVNWGWTWJVOW
        EWFUCUOWHVRVSVTWAWB $.

      $d k w y z $.  $d w C $.  $d w F $.  $d w M $.  $d w N $.
      $( The set of zeroes of ` F ` satisfies the conditions to have a
         supremum.  (Contributed by Thierry Arnoux, 1-Dec-2016.)  (Revised by
         AV, 6-Oct-2020.) $)
      ballotlemsup $p |- ( C e. ( O \ E ) -> E. z e. RR ( A. w e.
        { k e. ( 1 ... ( M + N ) ) | ( ( F ` C ) ` k ) = 0 } -. w < z
        /\ A. w e. RR ( z < w -> E. y e.
        { k e. ( 1 ... ( M + N ) ) | ( ( F ` C ) ` k ) = 0 } y < w )
        ) ) $=
        ( cdif wcel cr clt wor cv cfv cc0 wceq c1 caddc co cfz crab cfn wne wss
        c0 w3a wa wbr wn wral wrex fzfi ssrab2 ssfi mp2an a1i ballotlem5 sylibr
        wi rabn0 cn fz1ssnn nnssre sstri 3jca ltso jctil fiinf2g anim1i reximi2
        sseli 3syl ) ENIUDUEZUFUGUHZHUIEJUJUJUKULZHUMLMUNUOZUPUOZUQZURUEZWNVAUS
        ZWNUFUTZVBZVCDUIZCUIZUGVDVEDWNVFWTWSUGVDBUIWSUGVDBWNVGVODUFVFVCZCWNVGXA
        CUFVGWIWRWJWIWOWPWQWOWIWMURUEWNWMUTWOUMWLVHWKHWMVIZWMWNVJVKVLWIWKHWMVGW
        PAEFGHIJLMNOPQRSTUAUBVMWKHWMVPVNWQWIWNWMUFXBWMVQUFWLVRVSVTVTZVLWAWBWCCD
        BUFWNUGWDXAXACWNUFWTWNUEWTUFUEXAWNUFWTXCWGWEWFWH $.

      $( ` ( I `` C ) ` is the first tie.  (Contributed by Thierry Arnoux,
         1-Dec-2016.)  (Revised by AV, 6-Oct-2020.) $)
      ballotlemimin $p |- ( C e. ( O \ E ) ->
        -. E. k e. ( 1 ... ( ( I ` C ) - 1 ) ) ( ( F ` C ) ` k ) = 0 ) $=
        ( vw vz vy cdif wcel cv cfv cc0 wceq c1 cmin co cfz clt wbr cle elfzle2
        wa adantl cz elfzelz caddc ballotlemiex simpld elfzelzd zltlem1 syl2anr
        wb mpbird adantr wn cuz wss 1zzd zsubcld cn nnaddcl mp2an a1i nnred syl
        zred nnzd zlem1lt syl2anc mpbid ltled eluz fzss2 crab cr cinf wral wrex
        sseld rabid wi ballotlemsup wor ltso id inflb ballotlemi breq2d sylibrd
        notbid biimtrrid syland imp biid sylnib anassrs pm2.65da nrexdv ) BKFUD
        UEZEUFZBGUGZUGUHUIZEUJBHUGZUJUKULZUMULZXOXPYAUEZURZXRXPXSUNUOZYCYDXRYCY
        DXPXTUPUOZYBYEXOXPUJXTUQUSYBXPUTUEXSUTUEZYDYEVHXOXPUJXTVAXOXSUJIJVBULZX
        OXSUJYGUMULZUEZXSXQUGUHUIABCDEFGHIJKLMNOPQRSTVCVDZVEZXPXSVFVGVIVJXOYBXR
        YDVKZXOYBXRURZURYDYDXOYMYLXOYBXPYHUEZXRYLXOYAYHXPXOYGXTVLUGUEZYAYHVMXOY
        OXTYGUPUOZXOXTYGXOXTXOXSUJYKXOVNVOZWBXOYGYGVPUEZXOIVPUEJVPUEYRMNIJVQVRV
        SZVTXOXSYGUPUOZXTYGUNUOZXOYIYTYJXSUJYGUQWAXOYFYGUTUEZYTUUAVHYKXOYGYSWCZ
        XSYGWDWEWFWGXOXTUTUEUUBYOYPVHYQUUCXTYGWHWEVIXTUJYGWIWAWOYNXRURXPXREYHWJ
        ZUEZXOYLXREYHWPXOUUEXPUUDWKUNWLZUNUOZVKZYLXOUAUFZUBUFZUNUOVKUAUUDWMUUJU
        UIUNUOUCUFUUIUNUOUCUUDWNWQUAWKWMURUBWKWNZUUEUUHWQAUCUBUABCDEFGHIJKLMNOP
        QRSTWRUUKUBUAUCWKUUDXPUNWKUNWSUUKWTVSUUKXAXBWAXOYDUUGXOXSUUFXPUNABCDEFG
        HIJKLMNOPQRSTXCXDXFXEXGXHXIYDXJXKXLXMXN $.

      $( If the first vote is for B, the vote on the first tie is for A.
         (Contributed by Thierry Arnoux, 1-Dec-2016.) $)
      ballotlemic $p |- ( ( C e. ( O \ E ) /\ -. 1 e. C ) ->
                                                            ( I ` C ) e. C ) $=
        ( cdif wcel c1 wn wa cfv cv cc0 wceq cmin co wrex eldifi ad2antrr cn c2
        cfz cuz wne caddc ballotlemiex simpld elfznn adantr ballotlemi1 eluz2b3
        syl sylanbrc uz2m1nn cle wbr elnnuz biimpi eluzfz1 3syl wi ballotlemfp1
        1nn a1i imp 1m1e0 fveq2i oveq1i ballotlemfval0 oveq1d 3eqtrrd cr wb 0re
        0le1 1re suble0 mp2an mpbir eqbrtrrdi fveq2 breq1d rspcev syl2anc 1p0e1
        0lt1 simprd eqtr3d cz nnzd 1zzd zsubcld ballotlemfelz zcnd 1cnd subaddd
        0cnd mpbid eqtr3id breqtrid adantlr ballotlemfc0 ballotlemimin condan
        clt ) BKFUAUBZUCBUBZUDZUEZBHUFZBUBZEUGBGUFZUFUHUIEUCYEUCUJUKZUQUKZULZYD
        YFUDZUEZABCDEGYHIJKLMNOPQYABKUBZYCYKBKFUMZUNYDYHUOUBZYKYDYEUPURUFUBZYOY
        DYEUOUBZYEUCUSYPYAYQYCYAYEUCIJUTUKZUQUKUBZYQYAYSYEYGUFZUHUIZABCDEFGHIJK
        LMNOPQRSTVAZVBYEYRVCVGZVDABCDEFGHIJKLMNOPQRSTVEYEVFVHYEVIVGZVDYLUCYIUBZ
        UCYGUFZUHVJVKZDUGZYGUFZUHVJVKZDYIULYDUUEYKYDYOYHUCURUFUBZUUEUUDYOUUKYHV
        LVMUCYHVNVOVDYDUUGYKYDUUFUHUCUJUKZUHVJYDUUFUCUCUJUKZYGUFZUCUJUKZUHYGUFZ
        UCUJUKZUULYAYCUUFUUOUIZYAYCUURVPYBUUFUUNUCUTUKUIVPYAABCDGUCIJKLMNOPQYNU
        CUOUBYAVRVSVQVBVTUUOUUQUIYDUUNUUPUCUJUUMUHYGWAWBWCVSYDUUPUHUCUJYAUUPUHU
        IZYCYAYMUUSYNABCDGIJKLMNOPQWDVGVDWEWFUULUHVJVKZUHUCVJVKZWJUHWGUBUCWGUBU
        UTUVAWHWIWKUHUCWLWMWNWOVDUUJUUGDUCYIUUHUCUIUUIUUFUHVJUUHUCYGWPWQWRWSYAY
        KUHYHYGUFZXTVKYCYAYKUEZUHUCUVBXTXAUVCUCUCUHUTUKZUVBWTUVCUVBUCUJUKZUHUIU
        VDUVBUIUVCYTUVEUHYAYKYTUVEUIZYAYKUVFVPYFYTUVBUCUTUKUIVPYAABCDGYEIJKLMNO
        PQYNUUCVQVBVTYAUUAYKYAYSUUAUUBXBVDXCUVCUVBUCUHUVCUVBUVCABCDGYHIJKLMNOPQ
        YAYMYKYNVDUVCYEUCYAYEXDUBYKYAYEUUCXEVDUVCXFXGXHXIUVCXJUVCXLXKXMXNXOXPXQ
        YAYJUDYCYKABCDEFGHIJKLMNOPQRSTXRUNXS $.

      $( If the first vote is for A, the vote on the first tie is for B.
         (Contributed by Thierry Arnoux, 4-Apr-2017.) $)
      ballotlem1c $p |- ( ( C e. ( O \ E ) /\ 1 e. C ) ->
                                                         -. ( I ` C ) e. C ) $=
        ( cdif wcel c1 wa cfv cv cc0 wceq cmin co cfz eldifi ad2antrr cn c2 cuz
        wrex wne ballotlemiex simpld elfznn adantr ballotlemii eluz2b3 sylanbrc
        caddc syl uz2m1nn cle wbr fveq2 breq2d elnnuz biimpi eluzfz1 3syl 1e0p1
        0le1 breqtri wn wi 1nn a1i ballotlemfp1 simprd imp 1m1e0 ballotlemfval0
        fveq2i oveq1i oveq1d 3eqtrrd breqtrid rspcedvdw cneg df-neg eqtr3d 0cnd
        clt 1cnd cz nnzd 1zzd zsubcld ballotlemfelz zcnd subadd2d mpbird eqtrid
        neg1lt0 eqbrtrrdi adantlr ballotlemfcc ballotlemimin pm2.65da ) BKFUAUB
        ZUCBUBZUDZBHUEZBUBZEUFBGUEZUEUGUHEUCXSUCUIUJZUKUJZUQZXRXTUDZABCDEGYBIJK
        LMNOPQXPBKUBZXQXTBKFULZUMXRYBUNUBZXTXRXSUOUPUEUBZYHXRXSUNUBZXSUCURYIXPY
        JXQXPXSUCIJVFUJZUKUJUBZYJXPYLXSYAUEZUGUHZABCDEFGHIJKLMNOPQRSTUSZUTXSYKV
        AVGZVBABCDEFGHIJKLMNOPQRSTVCXSVDVEXSVHVGZVBYEUGDUFZYAUEZVIVJUGUCYAUEZVI
        VJZDUCYCYRUCUHYSYTUGVIYRUCYAVKVLXRUCYCUBZXTXRYHYBUCUPUEUBZUUBYQYHUUCYBV
        MVNUCYBVOVPVBXRUUAXTXRUGUGUCVFUJZYTVIUGUCUUDVIVRVQVSXRYTUCUCUIUJZYAUEZU
        CVFUJZUGYAUEZUCVFUJZUUDXPXQYTUUGUHZXPXQVTYTUUFUCUIUJUHWAXQUUJWAXPABCDGU
        CIJKLMNOPQYGUCUNUBXPWBWCWDWEWFUUGUUIUHXRUUFUUHUCVFUUEUGYAWGWIWJWCXRUUHU
        GUCVFXPUUHUGUHZXQXPYFUUKYGABCDGIJKLMNOPQWHVGVBWKWLWMVBWNXPXTYBYAUEZUGWS
        VJXQXPXTUDZUULUCWOZUGWSUUMUUNUGUCUIUJZUULUCWPUUMUUOUULUHUULUCVFUJZUGUHU
        UMYMUUPUGXPXTYMUUPUHZXPXTVTYMUULUCUIUJUHWAXTUUQWAXPABCDGXSIJKLMNOPQYGYP
        WDWEWFXPYNXTXPYLYNYOWEVBWQUUMUGUCUULUUMWRUUMWTUUMUULUUMABCDGYBIJKLMNOPQ
        XPYFXTYGVBUUMXSUCXPXSXAUBXTXPXSYPXBVBUUMXCXDXEXFXGXHXIXJXKXLXMXPYDVTXQX
        TABCDEFGHIJKLMNOPQRSTXNUMXO $.
    $}

    $( For a given count ` c ` , ` S ` is the operation reflecting the index
       in a count, before a tie is reached. $)
    ballotth.s $e |- S = ( c e. ( O \ E ) |-> ( i e. ( 1 ... ( M + N ) ) |->
                   if ( i <_ ( I ` c ) , ( ( ( I ` c ) + 1 ) - i ) , i ) ) ) $.

    $d c I $.
    ${
      $d c d i k M $.  $d c d i k N $.  $d d E $.  $d d C $.  $d d I $.
      $d d O $.
      $( Value of ` S ` .  (Contributed by Thierry Arnoux, 12-Apr-2017.) $)
      ballotlemsval $p |- ( C e. ( O \ E ) ->
        ( S ` C ) = ( i e. ( 1 ... ( M + N ) ) |->
                   if ( i <_ ( I ` C ) , ( ( ( I ` C ) + 1 ) - i ) , i ) ) ) $=
        ( vd c1 caddc co cfz cv cfv cle wbr cmin cif cmpt cdif wceq wcel fveq2d
        simpl breq2d oveq1d ifbieq1d mpteq2dva cbvmptv eqtri ovex mptex fvmpt
        wa ) UCBEUDJKUEUFZUGUFZEUHZUCUHZIUIZUJUKZVNUDUEUFZVLULUFZVLUMZUNZEVKVLB
        IUIZUJUKZVTUDUEUFZVLULUFZVLUMZUNLGUOZDVMBUPZEVKVRWDWFVLVKUQZVIZVOWAVQWC
        VLWHVNVTVLUJWHVMBIWFWGUSURZUTWHVPWBVLULWHVNVTUDUEWIVAVAVBVCDMWEEVKVLMUH
        ZIUIZUJUKZWKUDUEUFZVLULUFZVLUMZUNZUNUCWEVSUNUBMUCWEWPVSWJVMUPZEVKWOVRWQ
        WGVIZWLVOWNVQVLWRWKVNVLUJWRWJVMIWQWGUSURZUTWRWMVPVLULWRWKVNUDUEWSVAVAVB
        VCVDVEEVKWDUDVJUGVFVGVH $.

      $d i j $.  $d j I $.  $d j C $.  $d j E $.  $d j F $.  $d j J $.
      $d j F $.  $d j M $.  $d j N $.  $d j O $.
      $( Value of ` S ` evaluated at ` J ` for a given counting ` C ` .
         (Contributed by Thierry Arnoux, 12-Apr-2017.) $)
      ballotlemsv $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) ) ->
        ( ( S ` C ) ` J ) =
                     if ( J <_ ( I ` C ) , ( ( ( I ` C ) + 1 ) - J ) , J ) ) $=
        ( vj cdif wcel c1 caddc co cfz wa cv cfv cle wbr cmin cif cvv cmpt wceq
        ballotlemsval breq1 oveq2 ifbieq12d cbvmptv eqtrdi adantr breq1d oveq2d
        id simpr adantlr ovexd wn elex ad2antlr ifclda fvmptd ) BMGUEUFZJUGKLUH
        UIUJUIZUFZUKZUDJUDULZBIUMZUNUOZWDUGUHUIZWCUPUIZWCUQZJWDUNUOZWFJUPUIZJUQ
        ZVTBDUMZURVSWLUDVTWHUSZUTWAVSWLEVTEULZWDUNUOZWFWNUPUIZWNUQZUSWMABCDEFGH
        IKLMNOPQRSTUAUBUCVAEUDVTWQWHWNWCUTZWOWEWPWNWGWCWNWCWDUNVBWNWCWFUPVCWRVJ
        VDVEVFVGVSWCJUTZWHWKUTWAVSWSUKZWEWIWGWCWJJWTWCJWDUNVSWSVKZVHWTWCJWFUPXA
        VIXAVDVLVSWAVKWBWIWJJURWBWIUKWFJUPVMWAJURUFVSWIVNJVTVOVPVQVR $.
    $}

    $( ` S ` maps values less than ` ( I `` C ) ` to values greater than 1.
       (Contributed by Thierry Arnoux, 28-Apr-2017.) $)
    ballotlemsgt1 $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) )
      /\ J < ( I ` C ) ) -> 1 < ( ( S ` C ) ` J ) ) $=
      ( cdif wcel c1 caddc co cfz cfv clt wbr w3a cmin cz elfzelz 3ad2ant2 zred
      cc0 wceq ballotlemiex simpld elfzelzd 3ad2ant1 1red readdcld simp3 pncand
      zcnd 1cnd breqtrrd ltsub13d cle ballotlemsv 3adant3 ltled iftrued eqtrd
      cif ) BMGUDUEZJUFKLUGUHZUIUHZUEZJBIUJZUKULZUMZUFWDUFUGUHZJUNUHZJBDUJUJZUK
      WFJWGUFWFJWCVTJUOUEWEJUFWAUPUQURZWFWDUFWFWDVTWCWDUOUEWEVTWDUFWAVTWDWBUEWD
      BHUJUJUSUTABCEFGHIKLMNOPQRSTUAUBVAVBVCVDZURZWFVEZVFWMWFJWDWGUFUNUHUKVTWCW
      EVGZWFWDUFWFWDWKVIWFVJVHVKVLWFWIJWDVMULZWHJVSZWHVTWCWIWPUTWEABCDEFGHIJKLM
      NOPQRSTUAUBUCVNVOWFWOWHJWFJWDWJWLWNVPVQVRVK $.

    $( Domain of ` S ` for a given counting ` C ` .  (Contributed by Thierry
       Arnoux, 12-Apr-2017.) $)
    ballotlemsdom $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) ) ->
      ( ( S ` C ) ` J ) e. ( 1 ... ( M + N ) ) ) $=
      ( cdif wcel c1 caddc co cfz cfv cle wbr cmin cif ballotlemsv wss cc0 wceq
      wa cz ballotlemiex simpld elfzelzd ad2antrr cn nnaddcl mp2an nnzi elfzle2
      a1i syl w3a eluz2 fzss2 sylbir syl3anc simplr elfzle1 simpr elfzd fzrev3i
      cuz 1zzd wb 1cnd zcnd addcomd oveq1d eleq1d mpbid sseldd ifclda eqeltrd
      wn ) BMGUDUEZJUFKLUGUHZUIUHZUEZUSZJBDUJUJJBIUJZUKULZWTUFUGUHZJUMUHZJUNWQA
      BCDEFGHIJKLMNOPQRSTUAUBUCUOWSXAXCJWQWSXAUSZUFWTUIUHZWQXCXDWTUTUEZWPUTUEZW
      TWPUKULZXEWQUPZWOXFWRXAWOWTUFWPWOWTWQUEZWTBHUJUJUQURABCEFGHIKLMNOPQRSTUAU
      BVAVBZVCZVDZXGXDWPKVEUELVEUEWPVEUEOPKLVFVGVHVJXDXJXHWOXJWRXAXKVDWTUFWPVIV
      KXFXGXHVLWPWTWBUJUEXIWTWPVMWTUFWPVNVOVPXDUFWTUGUHZJUMUHZXEUEZXCXEUEZXDJXE
      UEXPXDJUFWTXDWCXMXDJUFWPWOWRXAVQZVCXDWRUFJUKULXRJUFWPVRVKWSXAVSVTJUFWTWAV
      KWOXPXQWDWRXAWOXOXCXEWOXNXBJUMWOUFWTWOWEWOWTXLWFWGWHWIVDWJWKWOWRXAWNVQWLW
      M $.

    $( The range ` ( 1 ... ( I `` C ) ) ` is invariant under ` ( S `` C ) ` .
       (Contributed by Thierry Arnoux, 28-Apr-2017.) $)
    ballotlemsel1i $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( I ` C ) ) ) ->
      ( ( S ` C ) ` J ) e. ( 1 ... ( I ` C ) ) ) $=
      ( cdif wcel c1 cfv cfz co wa 1zzd cz caddc cc0 wceq ballotlemiex elfzelzd
      simpld adantr cuz wss cle wbr cn nnaddcl mp2an nnzi a1i elfzle2 syl eluz2
      syl3anbrc fzss2 sselda ballotlemsdom syldan cmin elfzelz adantl zred 1red
      readdcld zcnd pncand breqtrrd lesubd cif ballotlemsv iftrued eqtrd elfznn
      1cnd ltesubnnd eqbrtrd elfzd ) BMGUDUEZJUFBIUGZUHUIZUEZUJZJBDUGUGZUFWQWTU
      KWPWQULUEZWSWPWQUFKLUMUIZWPWQUFXCUHUIZUEZWQBHUGUGUNUOABCEFGHIKLMNOPQRSTUA
      UBUPURZUQZUSZWTXAUFXCWPWSJXDUEZXAXDUEWPWRXDJWPXCWQUTUGUEZWRXDVAWPXBXCULUE
      ZWQXCVBVCZXJXGXKWPXCKVDUELVDUEXCVDUEOPKLVEVFVGVHWPXEXLXFWQUFXCVIVJWQXCVKV
      LWQUFXCVMVJVNZABCDEFGHIJKLMNOPQRSTUAUBUCVOVPUQWTUFWQUFUMUIZJVQUIZXAVBWTJX
      NUFWTJWSJULUEWPJUFWQVRVSVTWTWQUFWTWQXHVTWTWAZWBXPWTJWQXNUFVQUIVBWSJWQVBVC
      ZWPJUFWQVIVSZWTWQUFWTWQXHWCWTWLWDWEWFWTXAXQXOJWGZXOWPWSXIXAXSUOXMABCDEFGH
      IJKLMNOPQRSTUAUBUCWHVPWTXQXOJXRWIWJZWEWTXAXOWQVBXTWPWSXIXOWQVBVCXMWPXIUJW
      QJWPXBXIXGUSXIJVDUEWPJXCWKVSWMVPWNWO $.

    $d i j $.  $d j I $.  $d j C $.  $d j E $.  $d j F $.  $d j J $.  $d j F $.
    $d j M $.  $d j N $.  $d j O $.
    $( The defined ` S ` is a bijection, and an involution.  (Contributed by
       Thierry Arnoux, 14-Apr-2017.) $)
    ballotlemsf1o $p |- ( C e. ( O \ E ) ->
           ( ( S ` C ) : ( 1 ... ( M + N ) ) -1-1-onto-> ( 1 ... ( M + N ) ) /\
          `' ( S ` C ) = ( S ` C ) ) ) $=
      ( vj cdif wcel c1 caddc cfz cfv wf1o ccnv wceq cle wbr cmin ballotlemsval
      co cv cif cmpt wa ballotlemsv ballotlemsdom eqeltrrd oveq2 id breq1 cc cz
      cvv cc0 ballotlemiex simpld elfzelz peano2zd zcnd adantr nncand eqcomd cn
      syl ad2antll elfznn ltesubnnd vex a1i ovexd ifeqeqx simplrl impbida f1o3d
      ad2antrl ifbieq12d cbvmptv simprd 3eqtr4rd jca ) BLGUDUEZUFJKUGUQZUHUQZWT
      BDUIZUJZXAUKZXAULWRXBXCUCWTUCURZBIUIZUMUNZXEUFUGUQZXDUOUQZXDUSZUTZULZWREU
      CWTWTEURZXEUMUNZXGXLUOUQZXLUSZXIXAABCDEFGHIJKLMNOPQRSTUAUBUPZWRXLWTUEZVAX
      LXAUIXOWTABCDEFGHIXLJKLMNOPQRSTUAUBVBABCDEFGHIXLJKLMNOPQRSTUAUBVCVDWRXDWT
      UEZVAXDXAUIXIWTABCDEFGHIXDJKLMNOPQRSTUAUBVBABCDEFGHIXDJKLMNOPQRSTUAUBVCVD
      WRXQXRVAZVAZXLXIULXDXOULXTXFXMXHXEUMUNZEXNXLXGXHUOUQZVJVJXHXDUCXLXHXGUOVE
      XLXDULZVFZXLXHXEUMVGXLXDXEUMVGZXTYBXDXTXGXDWRXGVHUEXSWRXGWRXEWTUEZXGVIUEW
      RYFXEBHUIUIVKULABCEFGHIJKLMNOPQRSTUAVLVMZYFXEXEUFWSVNZVOWAVPVQZXRXDVHUEWR
      XQXRXDXDUFWSVNVPWBVRVSXTYAXFXTXEXDWRXEVIUEZXSWRYFYJYGYHWAVQZXRXDVTUEWRXQX
      DWSWCWBWDVQXDVJUEXTUCWEWFXTXGXDUOWGWHXTXMXFXNXEUMUNUCXHXDXGXNUOUQZVJVJXNX
      LEXDXNXGUOVEXDXLULVFXDXNXEUMVGXDXLXEUMVGXTYLXLXTXGXLYIXQXLVHUEWRXRXQXLXLU
      FWSVNVPWLVRVSXTXMVAZXEXLXTYJXMYKVQYMXQXLVTUEWRXQXRXMWIXLWSWCWAWDXLVJUEXTE
      WEWFXTXGXLUOWGWHWJWKZVMWREWTXOUTZXJXAXCYOXJULWREUCWTXOXIYCXMXFXNXLXHXDYEX
      LXDXGUOVEYDWMWNWFXPWRXBXKYNWOWPWQ $.

    $( The image by ` S ` of the first tie pick is the first pick.
       (Contributed by Thierry Arnoux, 14-Apr-2017.) $)
    ballotlemsi $p |- ( C e. ( O \ E ) -> ( ( S ` C ) ` ( I ` C ) ) = 1 ) $=
      ( cdif wcel cfv cle wbr c1 caddc co cmin cif cfz wceq ballotlemiex simpld
      cc0 ballotlemsv mpdan cr elfzelz zred syl leidd iftrued recnd 1cnd 3eqtrd
      pncan2d ) BLGUCUDZBIUEZBDUEUEZVKVKUFUGZVKUHUIUJVKUKUJZVKULZVNUHVJVKUHJKUI
      UJZUMUJUDZVLVOUNVJVQVKBHUEUEUQUNABCEFGHIJKLMNOPQRSTUAUOUPZABCDEFGHIVKJKLM
      NOPQRSTUAUBURUSVJVMVNVKVJVKVJVQVKUTUDVRVQVKVKUHVPVAVBVCZVDVEVJVKUHVJVKVSV
      FVJVGVIVH $.

    $d j k $.  $d j S $.  $d k J $.  $d k S $.
    $( The image by ` S ` of an interval before the first pick.  (Contributed
       by Thierry Arnoux, 5-May-2017.) $)
    ballotlemsima $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( I ` C ) ) ) ->
         ( ( S ` C ) " ( 1 ... J ) ) = ( ( ( S ` C ) ` J ) ... ( I ` C ) ) ) $=
      ( vj cdif wcel c1 cfv cfz co wa cima cz cv wss caddc imassrn wf1o wf ccnv
      crn wceq ballotlemsf1o simpld f1of frn 3syl sstrid cuz fzssuz uzssz sstri
      sstrdi adantr sselda elfzelz adantl wb wfn f1ofn syl ballotlemiex elfzuz3
      wrex cc0 uztrn syl2anc fzss2 fvelimab cmin cle wbr 1zzd nnzi zaddcl mp2an
      cif a1i elfzle1 elfzle2 letrd elfzd ballotlemsv syldan simpr iftrue eqtrd
      zred oveq1d eleq2d ad2antrr zcnd pncand oveq2d ad2antlr peano2zd syl22anc
      1cnd fzrev 3bitr2d risset eqcom cc adantlr addcld simplr subsub23 syl3anc
      bitr3id simpll eqeq1d bitr4d rexbidva 3bitrd eqrdav ) BMGUEUFZJUGBIUHZUIU
      JUFZUKZFBDUHZUGJUIUJZULZJYTUHZYQUIUJZUMYSUUBUMFUNZYPUUBUMUOYRYPUUBUGKLUPU
      JZUIUJZUMYPUUBYTVAZUUGYTUUAUQYPUUGUUGYTURZUUGUUGYTUSUUHUUGUOYPUUIYTUTYTVB
      ABCDEFGHIKLMNOPQRSTUAUBUCVCVDZUUGUUGYTVEUUGUUGYTVFVGVHUUGUGVIUHUMUGUUFVJU
      GVKVLVMVNVOUUEUUDUFZUUEUMUFZYSUUEUUCYQVPVQYSUULUKZUUEUUBUFZUDUNZYTUHZUUEV
      BZUDUUAWDZUUKYSUUNUURVRZUULYSYTUUGVSZUUAUUGUOZUUSYPUUTYRYPUUIUUTUUJUUGUUG
      YTVTWAVNYSUUFJVIUHZUFZUVAYSUUFYQVIUHUFZYQUVBUFZUVCYSYQUUGUFZUVDYPUVFYRYPU
      VFYQBHUHUHWEVBABCEFGHIKLMNOPQRSTUAUBWBVDZVNYQUGUUFWCWAYRUVEYPJUGYQWCVQYQU
      UFJWFWGJUGUUFWHWAZUDUUGUUAUUEYTWIWGVNUUMUUKYQUGUPUJZUUEWJUJZUUAUFZUUOUVJV
      BZUDUUAWDZUURUUMUUKUUEUVIJWJUJZYQUIUJZUFZUUEUVNUVIUGWJUJZUIUJZUFZUVKYSUUK
      UVPVRUULYSUUDUVOUUEYSUUCUVNYQUIYSUUCJYQWKWLZUVNJWQZUVNYPYRJUUGUFUUCUWAVBY
      SJUGUUFYSWMUUFUMUFZYSKUMUFLUMUFUWBKOWNLPWNKLWOWPWRZYRJUMUFZYPJUGYQVPZVQZY
      RUGJWKWLYPJUGYQWSVQYSJYQUUFYSJUWFXHYSYQYPYQUMUFZYRYPUVFUWGUVGYQUGUUFVPWAZ
      VNXHYSUUFUWCXHYRUVTYPJUGYQWTZVQYPYQUUFWKWLZYRYPUVFUWJUVGYQUGUUFWTWAVNXAXB
      ABCDEFGHIJKLMNOPQRSTUAUBUCXCXDYSYRUVTUWAUVNVBYPYRXEUWIUVTUVNJXFVGXGXIXJVN
      UUMUVRUVOUUEUUMUVQYQUVNUIUUMYQUGUUMYQYPUWGYRUULUWHXKZXLUUMXRXMXNXJUUMUGUM
      UFUWDUVIUMUFUULUVSUVKVRUUMWMYRUWDYPUULUWEXOUUMYQUWKXPYSUULXEUVIUUEUGJXSXQ
      XTUVKUVMVRUUMUDUVJUUAYAWRUUMUVLUUQUDUUAUUMUUOUUAUFZUKZUVLUVIUUOWJUJZUUEVB
      ZUUQUVLUVJUUOVBZUWMUWOUVJUUOYBUWMUVIYCUFUUEYCUFUUOYCUFUWPUWOVRUWMYQUGUWMY
      QYSUWLUWGUULYPUWGYRUWLUWHXKZYDXLUWMXRYEUWMUUEYSUULUWLYFXLUWMUUOUWLUUOUMUF
      ZUUMUUOUGJVPZVQXLUVIUUEUUOYGYHYIYSUWLUUQUWOVRUULYSUWLUKZUUPUWNUUEUWTUUPUU
      OYQWKWLZUWNUUOWQZUWNUWTYPUUOUUGUFUUPUXBVBYPYRUWLYJYSUUAUUGUUOUVHVOABCDEFG
      HIUUOKLMNOPQRSTUAUBUCXCWGUWTUXAUXBUWNVBUWTUUOJYQUWTUUOUWLUWRYSUWSVQXHUWTJ
      YRUWDYPUWLUWEXOXHUWTYQUWQXHUWLUUOJWKWLYSUUOUGJWTVQYRUVTYPUWLUWIXOXAUXAUWN
      UUOXFWAXGYKYDYLYMYNYLYO $.

    $d i k D $.
    $( If two countings share the same first tie, they also have the same swap
       function.  (Contributed by Thierry Arnoux, 18-Apr-2017.) $)
    ballotlemieq $p |- ( ( C e. ( O \ E ) /\ D e. ( O \ E ) /\
      ( I ` C ) = ( I ` D ) ) -> ( S ` C ) = ( S ` D ) ) $=
      ( cdif wcel cfv wceq w3a c1 caddc co cfz cv cle wbr cmin cif simpl breq2d
      cmpt wa oveq1d ifbieq1d mpteq2dva 3ad2ant3 ballotlemsval 3ad2ant1 3eqtr4d
      3ad2ant2 ) BMHUDZUEZCVJUEZBJUFZCJUFZUGZUHFUIKLUJUKULUKZFUMZVMUNUOZVMUIUJU
      KZVQUPUKZVQUQZUTZFVPVQVNUNUOZVNUIUJUKZVQUPUKZVQUQZUTZBEUFZCEUFZVOVKWBWGUG
      VLVOFVPWAWFVOVQVPUEZVAZVRWCVTWEVQWKVMVNVQUNVOWJURZUSWKVSWDVQUPWKVMVNUIUJW
      LVBVBVCVDVEVKVLWHWBUGVOABDEFGHIJKLMNOPQRSTUAUBUCVFVGVLVKWIWGUGVOACDEFGHIJ
      KLMNOPQRSTUAUBUCVFVIVH $.

    $( R is the operation reflecting the picks in a count, before a tie is
       reached. $)
    ballotth.r $e |- R = ( c e. ( O \ E ) |-> ( ( S ` c ) " c ) ) $.

    $d i S $.  $d c S $.
    ${
      $d d E $.  $d d O $.  $d d C $.  $d d S $.  $d c d i I $.
      $( Value of ` R ` .  (Contributed by Thierry Arnoux, 14-Apr-2017.) $)
      ballotlemrval $p |- ( C e. ( O \ E )
            -> ( R ` C ) = ( ( S ` C ) " C ) ) $=
        ( vd cv cfv cima cdif wceq fveq2 id imaeq12d cmpt cbvmptv cvv wcel fvex
        eqtri imaexg ax-mp fvmpt ) UEBUEUFZEUGZVCUHZBEUGZBUHZMHUIZDVCBUJZVDVFVC
        BVCBEUKVIULUMDNVHNUFZEUGZVJUHZUNUEVHVEUNUDNUEVHVLVEVJVCUJZVKVDVJVCVJVCE
        UKVMULUMUOUSVFUPUQVGUPUQBEURVFBUPUTVAVB $.
    $}

    $( The image of ` ( R `` C ) ` by ` ( S `` C ) ` .  (Contributed by Thierry
       Arnoux, 21-Apr-2017.) $)
    ballotlemscr $p |- ( C e. ( O \ E ) -> ( ( S ` C ) " ( R ` C ) ) = C ) $=
      ( cdif wcel cfv cima ccnv ballotlemrval imaeq2d c1 caddc co cfz wf1o wceq
      ballotlemsf1o simprd imaeq1d wf1 wss simpld f1of1 syl eldifi ballotlemelo
      chash simplbi f1imacnv syl2anc 3eqtr2d ) BMHUEUFZBEUGZBDUGZUHVNVNBUHZUHVN
      UIZVPUHZBVMVOVPVNABCDEFGHIJKLMNOPQRSTUAUBUCUDUJUKVMVQVNVPVMULKLUMUNUOUNZV
      SVNUPZVQVNUQZABCEFGHIJKLMNOPQRSTUAUBUCURZUSUTVMVSVSVNVAZBVSVBZVRBUQVMVTWC
      VMVTWAWBVCVSVSVNVDVEVMBMUFZWDBMHVFWEWDBVHUGKUQBKLMNOPQVGVIVEVSVSBVNVJVKVL
      $.

    $( Value of ` R ` evaluated at ` J ` .  (Contributed by Thierry Arnoux,
       17-Apr-2017.) $)
    ballotlemrv $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) ) ->
      ( J e. ( R ` C ) <->
              if ( J <_ ( I ` C ) , ( ( ( I ` C ) + 1 ) - J ) , J ) e. C ) ) $=
      ( cdif wcel c1 caddc co cfz wa cfv ccnv cima cle wbr cmin cif wfun cdm wb
      wf1o simpl wceq ballotlemsf1o simpld f1ofun simpr f1odm eleqtrrd fvimacnv
      syl2anc ballotlemsv eleq1d simprd imaeq1d ballotlemrval eqtr4d eleq2d syl
      3syl 3bitr3rd ) BNHUFUGZKUHLMUIUJUKUJZUGZULZKBEUMZUMZBUGZKWHUNZBUOZUGZKBJ
      UMZUPUQWNUHUIUJKURUJKUSZBUGKBDUMZUGZWGWHUTZKWHVAZUGWJWMVBWGWDWEWEWHVCZWRW
      DWFVDZWDWTWKWHVEZABCEFGHIJLMNOPQRSTUAUBUCUDVFZVGZWEWEWHVHWBWGKWEWSWDWFVIW
      GWDWTWSWEVEXAXDWEWEWHVJWBVKKBWHVLVMWGWIWOBABCEFGHIJKLMNOPQRSTUAUBUCUDVNVO
      WGWDWMWQVBXAWDWLWPKWDWLWHBUOWPWDWKWHBWDWTXBXCVPVQABCDEFGHIJLMNOPQRSTUAUBU
      CUDUEVRVSVTWAWC $.

    $( Value of ` R ` before the tie.  (Contributed by Thierry Arnoux,
       11-Apr-2017.) $)
    ballotlemrv1 $p |-
          ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) /\ J <_ ( I ` C ) ) ->
                     ( J e. ( R ` C ) <-> ( ( ( I ` C ) + 1 ) - J ) e. C ) ) $=
      ( cdif wcel caddc cfz cfv cle wbr w3a cmin cif ballotlemrv 3adant3 iftrue
      c1 co wb eleq1d 3ad2ant3 bitrd ) BNHUFUGZKUSLMUHUTUIUTUGZKBJUJZUKULZUMKBD
      UJUGZVHVGUSUHUTKUNUTZKUOZBUGZVJBUGZVEVFVIVLVAVHABCDEFGHIJKLMNOPQRSTUAUBUC
      UDUEUPUQVHVEVLVMVAVFVHVKVJBVHVJKURVBVCVD $.

    $( Value of ` R ` after the tie.  (Contributed by Thierry Arnoux,
       11-Apr-2017.) $)
    ballotlemrv2 $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) /\
      ( I ` C ) < J ) -> ( J e. ( R ` C ) <-> J e. C ) ) $=
      ( cdif wcel c1 caddc cfz cfv clt wbr w3a cle cmin cif ballotlemrv 3adant3
      co wb wn wa cz cuz fzssuz uzssz sstri cc0 wceq ballotlemiex simpld sselid
      adantr zred simpr ltnled biimp3a iffalsed eleq1d bitrd ) BNHUFUGZKUHLMUIU
      TZUJUTZUGZBJUKZKULUMZUNZKBDUKUGZKWFUOUMZWFUHUIUTKUPUTZKUQZBUGZKBUGWBWEWIW
      MVAWGABCDEFGHIJKLMNOPQRSTUAUBUCUDUEURUSWHWLKBWHWJWKKWBWEWGWJVBWBWEVCZWFKW
      NWFWBWFVDUGWEWBWDVDWFWDUHVEUKVDUHWCVFUHVGVHZWBWFWDUGWFBIUKUKVIVJABCFGHIJL
      MNOPQRSTUAUBUCVKVLVMVNVOWNKWNWDVDKWOWBWEVPVMVOVQVRVSVTWA $.

    $( Range of ` R ` is included in ` O ` .  (Contributed by Thierry Arnoux,
       17-Apr-2017.) $)
    ballotlemro $p |- ( C e. ( O \ E ) -> ( R ` C ) e. O ) $=
      ( cdif wcel cfv c1 caddc co cfz wss chash wceq cima ballotlemrval imassrn
      crn wf1o wfo ccnv ballotlemsf1o simpld forn 3syl sseqtrid eqsstrd cen wbr
      f1ofo wf1 f1of1 syl wa eldifi ballotlemelo sylib f1imaeng syl3anc eqbrtrd
      id hasheni simprd eqtrd sylanbrc ) BMHUEZUFZBDUGZUHKLUIUJUKUJZULWHUMUGZKU
      NWHMUFWGWHBEUGZBUOZWIABCDEFGHIJKLMNOPQRSTUAUBUCUDUPZWGWKURZWLWIWKBUQWGWIW
      IWKUSZWIWIWKUTWNWIUNWGWOWKVAWKUNABCEFGHIJKLMNOPQRSTUAUBUCVBVCZWIWIWKVJWIW
      IWKVDVEVFVGWGWJBUMUGZKWGWHBVHVIWJWQUNWGWHWLBVHWMWGWIWIWKVKZBWIULZWGWLBVHV
      IWGWOWRWPWIWIWKVLVMWGWSWQKUNZWGBMUFWSWTVNBMHVOBKLMNOPQVPVQZVCWGWAWIWIBWKW
      FVRVSVTWHBWBVMWGWSWTXAWCWDWHKLMNOPQVPWE $.

    $d i R $.
    ${
      $d u v C $.  $d u v I $.  $d u v J $.  $d u v R $.  $d u v S $.
      $d u v U $.  $d u v V $.
      $( ` .^ ` is the difference of counts of elements of ` U ` in / out of
         set ` V ` . $)
      ballotlemg $e |- .^ = ( u e. Fin , v e. Fin |->
                               ( ( # ` ( v i^i u ) ) - ( # ` ( v \ u ) ) ) ) $.
      $( Expand the value of ` .^ ` .  (Contributed by Thierry Arnoux,
         21-Apr-2017.) $)
      ballotlemgval $p |- ( ( U e. Fin /\ V e. Fin ) ->
                  ( U .^ V ) = ( ( # ` ( V i^i U ) ) - ( # ` ( V \ U ) ) ) ) $=
        ( cfn cv cin chash cfv cdif cmin wceq ineq2 fveq2d difeq2 oveq12d ineq1
        co difeq1 ovex ovmpo ) CBGQUJUJBUKZCUKZULZUMUNZVGVHUOZUMUNZUPVCQGULZUMU
        NZQGUOZUMUNZUPVCKVGGULZUMUNZVGGUOZUMUNZUPVCVHGUQZVJVRVLVTUPWAVIVQUMVHGV
        GURUSWAVKVSUMVHGVGUTUSVAVGQUQZVRVNVTVPUPWBVQVMUMVGQGVBUSWBVSVOUMVGQGVDU
        SVAUIVNVPUPVEVF $.

      ${
        $d u v U $.  $d u v V $.  $d u v W $.
        ballotlemgun.1 $e |- ( ph -> U e. Fin ) $.
        ballotlemgun.2 $e |- ( ph -> V e. Fin ) $.
        ballotlemgun.3 $e |- ( ph -> W e. Fin ) $.
        ballotlemgun.4 $e |- ( ph -> ( V i^i W ) = (/) ) $.
        $( A property of the defined ` .^ ` operator.  (Contributed by Thierry
           Arnoux, 26-Apr-2017.) $)
        ballotlemgun $p |- ( ph ->
                         ( U .^ ( V u. W ) ) = ( ( U .^ V ) + ( U .^ W ) ) ) $=
          ( cun cin chash cfv cdif cmin co caddc indir fveq2i wcel c0 wceq infi
          cfn syl ineq1d inindir 3eqtr3g hashun syl3anc eqtrid difundir difeq1d
          0in diffi difindir 0dif oveq12d cn0 hashcl 3syl nn0cnd addsub4d eqtrd
          unfi syl2anc ballotlemgval 3eqtr4d ) ARSUPZHUQZURUSZWOHUTZURUSZVAVBZR
          HUQZURUSZRHUTZURUSZVAVBZSHUQZURUSZSHUTZURUSZVAVBZVCVBZHWOLVBZHRLVBZHS
          LVBZVCVBAWTXBXGVCVBZXDXIVCVBZVAVBXKAWQXOWSXPVAAWQXAXFUPZURUSZXOWPXQUR
          RSHVDVEAXAVJVFZXFVJVFZXAXFUQZVGVHXRXOVHARVJVFZXSUMRHVIZVKASVJVFZXTUNS
          HVIZVKARSUQZHUQVGHUQYAVGAYFVGHUOVLRSHVMHVTVNXAXFVOVPVQAWSXCXHUPZURUSZ
          XPWRYGURRSHVRVEAXCVJVFZXHVJVFZXCXHUQZVGVHYHXPVHAYBYIUMRHWAZVKAYDYJUNS
          HWAZVKAYFHUTVGHUTYKVGAYFVGHUOVSRSHWBHWCVNXCXHVOVPVQWDAXBXGXDXIAXBAYBX
          SXBWEVFUMYCXAWFWGWHAXGAYDXTXGWEVFUNYEXFWFWGWHAXDAYBYIXDWEVFUMYLXCWFWG
          WHAXIAYDYJXIWEVFUNYMXHWFWGWHWIWJAHVJVFZWOVJVFZXLWTVHULAYBYDYOUMUNRSWK
          WLBCDEFGHIJKLMNOPQWOTUAUBUCUDUEUFUGUHUIUJUKWMWLAXMXEXNXJVCAYNYBXMXEVH
          ULUMBCDEFGHIJKLMNOPQRTUAUBUCUDUEUFUGUHUIUJUKWMWLAYNYDXNXJVHULUNBCDEFG
          HIJKLMNOPQSTUAUBUCUDUEUFUGUHUIUJUKWMWLWDWN $.
      $}

      $d i J $.
      $( Express the value of ` ( F `` C ) ` in terms of ` .^ ` .  (Contributed
         by Thierry Arnoux, 21-Apr-2017.) $)
      ballotlemfg $p |- ( ( C e. ( O \ E ) /\ J e. ( 0 ... ( M + N ) ) ) ->
                                  ( ( F ` C ) ` J ) = ( C .^ ( 1 ... J ) ) ) $=
        ( cdif wcel cc0 caddc co cfz wa cfv c1 chash cmin eldifi adantr elfzelz
        cin cz adantl ballotlemfval cfn wceq wss fzfi ballotlemelo simplbi ssfi
        sylancr syl fzfid ballotlemgval syl2anc eqtr4d ) DQJUJUKZNULOPUMUNZUOUN
        UKZUPZNDLUQUQURNUOUNZDVDUSUQWEDUJUSUQUTUNZDWEKUNZWDADEHLNOPQRSTUAUBUCWA
        DQUKZWCDQJVAVBZWCNVEUKWANULWBVCVFVGWDDVHUKZWEVHUKWGWFVIWDWHWJWIWHURWBUO
        UNZVHUKDWKVJZWJURWBVKWHWLDUSUQOVIDOPQRSTUAVLVMWKDVNVOVPWDURNVQABCEFGDHI
        JKLMOPQWERSTUAUBUCUDUEUFUGUHUIVRVSVT $.

      $( Express the value of ` ( F `` ( R `` C ) ) ` in terms of the newly
         defined ` .^ ` .  (Contributed by Thierry Arnoux, 21-Apr-2017.) $)
      ballotlemfrc $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( I ` C ) ) ) ->
        ( ( F ` ( R ` C ) ) ` J ) =
                              ( C .^ ( ( ( S ` C ) ` J ) ... ( I ` C ) ) ) ) $=
        ( cdif wcel c1 cfv cfz co wa cin chash cmin cima cres wf1o cen wbr wceq
        caddc wf1 wss ccnv ballotlemsf1o simpld syl adantr cuz cc0 ballotlemiex
        f1of1 elfzuz3 adantl uztrn syl2anc fzss2 ssinss1 f1ores ovex inex1 3syl
        f1oen hasheni ssdifssd difexg oveq12d ballotlemro elfzelz ballotlemfval
        cvv ax-mp cz cfn fzfi eldifi ballotlemelo simplbi sylancr ballotlemgval
        ssfi fzfid wfun dff1o3 simprbi imain ballotlemsima ballotlemscr ineq12d
        wfo eqtrd fveq2d imadif difeq12d eqtr4d 3eqtr4d ) DQJUJUKZNULDMUMZUNUOU
        KZUPZULNUNUOZDFUMZUQZURUMZYFYGUJZURUMZUSUODGUMZYHUTZURUMZYLYJUTZURUMZUS
        UOZNYGLUMUMDNYLUMZYCUNUOZKUOZYEYIYNYKYPUSYEYHYMYLYHVAZVBZYHYMVCVDYIYNVE
        YEULOPVFUOZUNUOZUUDYLVGZYHUUDVHZUUBYBUUEYDYBUUDUUDYLVBZUUEYBUUGYLVIZYLV
        EADEGHIJLMOPQRSTUAUBUCUDUEUFUGVJVKZUUDUUDYLVQVLVMZYEYFUUDVHZUUFYEUUCNVN
        UMZUKZUUKYEUUCYCVNUMUKZYCUULUKZUUMYEYCUUDUKZUUNYBUUPYDYBUUPYCDLUMUMVOVE
        ADEHIJLMOPQRSTUAUBUCUDUEUFVPVKVMYCULUUCVRVLYDUUOYBNULYCVRVSYCUUCNVTWANU
        LUUCWBVLZYFYGUUDWCVLUUDUUDYHYLWDWAYHYMUUAYFYGULNUNWEZWFWHYHYMWIWGYEYJYO
        YLYJVAZVBZYJYOVCVDYKYPVEYEUUEYJUUDVHUUTUUJYEYFUUDYGUUQWJUUDUUDYJYLWDWAY
        JYOUUSYFWPUKYJWPUKUURYFYGWPWKWQWHYJYOWIWGWLYEAYGEHLNOPQRSTUAUBUCYBYGQUK
        YDADEFGHIJLMOPQRSTUAUBUCUDUEUFUGUHWMVMYDNWRUKYBNULYCWNVSWOYEYTYSDUQZURU
        MZYSDUJZURUMZUSUOZYQYEDWSUKZYSWSUKYTUVEVEYEUUDWSUKDUUDVHZUVFULUUCWTYBUV
        GYDYBDQUKZUVGDQJXAUVHUVGDURUMOVEDOPQRSTUAXBXCVLVMUUDDXFXDYEYRYCXGABCEFG
        DHIJKLMOPQYSRSTUAUBUCUDUEUFUGUHUIXEWAYEYNUVBYPUVDUSYEYMUVAURYEYMYLYFUTZ
        YLYGUTZUQZUVAYBYMUVKVEZYDYBUUGUUHXHZUVLUUIUUGUUDUUDYLXOUVMUUDUUDYLXIXJZ
        YFYGYLXKWGVMYEUVIYSUVJDADEGHIJLMNOPQRSTUAUBUCUDUEUFUGXLZYBUVJDVEYDADEFG
        HIJLMOPQRSTUAUBUCUDUEUFUGUHXMVMZXNXPXQYEYOUVCURYEYOUVIUVJUJZUVCYBYOUVQV
        EZYDYBUUGUVMUVRUUIUVNYFYGYLXRWGVMYEUVIYSUVJDUVOUVPXSXPXQWLXTYA $.

      $( Reverse counting preserves a tie at the first tie.  (Contributed by
         Thierry Arnoux, 21-Apr-2017.) $)
      ballotlemfrci $p |- ( C e. ( O \ E ) ->
                                     ( ( F ` ( R ` C ) ) ` ( I ` C ) ) = 0 ) $=
        ( cdif wcel cfv c1 cfz co cc0 wceq caddc cuz ballotlemiex simpld elfzuz
        3syl ballotlemfrc mpdan ballotlemsi oveq1d oveq2d eqtrd fz1ssfz0 sselid
        eluzfz2 ballotlemfg simprd 3eqtr2d ) DPJUIUJZDMUKZDFUKLUKUKZDULVPUMUNZK
        UNZVPDLUKUKZUOVOVQDVPDGUKUKZVPUMUNZKUNZVSVOVPVRUJZVQWCUPVOVPULNOUQUNZUM
        UNZUJZVPULURUKUJWDVOWGVTUOUPZADEHIJLMNOPQRSTUAUBUCUDUEUSZUTZVPULWEVAULV
        PVKVBABCDEFGHIJKLMVPNOPQRSTUAUBUCUDUEUFUGUHVCVDVOWBVRDKVOWAULVPUMADEGHI
        JLMNOPQRSTUAUBUCUDUEUFVEVFVGVHVOVPUOWEUMUNZUJVTVSUPVOWFWKVPWEVIWJVJABCD
        EFGHIJKLMVPNOPQRSTUAUBUCUDUEUFUGUHVLVDVOWGWHWIVMVN $.

      $( Value of ` F ` for a reverse counting ` ( R `` C ) ` .  (Contributed
         by Thierry Arnoux, 27-Apr-2017.) $)
      ballotlemfrceq $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( I ` C ) ) )
        -> ( ( F ` C ) ` ( ( ( S ` C ) ` J ) - 1 ) )
                                            = -u ( ( F ` ( R ` C ) ) ` J ) ) $=
        ( cdif wcel c1 cfv cfz co wa cmin caddc cc0 wceq cneg ballotlemsel1i cz
        wb 1zzd ballotlemiex adantr simpld elfzelzd cuz wss elfzuz3 fzss2 simpr
        3syl sseldd ballotlemsdom syldan fzsubel syl22anc mpbid oveq1i eleqtrdi
        1m1e0 cle wbr zsubcld cn nnaddcl mp2an nnzi a1i elfzle2 syl clt zlem1lt
        syl2anc cr wi zred ltle sylbid eluz2 syl3anbrc ballotlemfg ballotlemfrc
        mpd sselda oveq12d cun fzsplit3 oveq2d fz1ssfz0 sseli sylan2 simprd cfn
        eqtr3d fzfi eldifi chash ballotlemelo simplbi ssfi sylancr fzfid cin c0
        ltm1 fzdisj ballotlemgun 3eqtr3rd ballotlemfelz zcnd ballotlemro addeq0
        eqtrd cc ) DQJUJUKZNULDMUMZUNUOZUKZUPZNDGUMUMZULUQUOZDLUMZUMZNDFUMZLUMU
        MZURUOZUSUTZUUGUUIVAUTZUUCUUJDULUUEUNUOZKUOZDUUDYTUNUOZKUOZURUOZUSUUCUU
        GUUNUUIUUPURYSUUBUUEUSOPURUOZUNUOZUKZUUGUUNUTYSUUBUUEUSYTULUQUOZUNUOZUK
        UUTUUCUUEULULUQUOZUVAUNUOZUVBUUCUUDUUAUKZUUEUVDUKZADEGHIJLMNOPQRSTUAUBU
        CUDUEUFUGVBZUUCULVCUKZYTVCUKZUUDVCUKUVHUVEUVFVDUUCVEZUUCYTULUURUUCYTULU
        URUNUOZUKZYTUUFUMZUSUTZYSUVLUVNUPUUBADEHIJLMOPQRSTUAUBUCUDUEUFVFZVGZVHZ
        VIUUCUUDULUURYSUUBNUVKUKUUDUVKUKUUCUUAUVKNUUCUVLUURYTVJUMUKUUAUVKVKUVQY
        TULUURVLYTULUURVMVOYSUUBVNZVPADEGHIJLMNOPQRSTUAUBUCUDUEUFUGVQVRVIZUVJUU
        DULULYTVSVTWAUVCUSUVAUNWDWBWCYSUVBUUSUUEYSUURUVAVJUMUKZUVBUUSVKYSUVAVCU
        KUURVCUKZUVAUURWEWFZUVTYSYTULYSYTULUURYSUVLUVNUVOVHZVIZYSVEWGZUWAYSUURO
        WHUKPWHUKUURWHUKSTOPWIWJWKWLZYSYTUURWEWFZUWBYSUVLUWGUWCYTULUURWMWNYSUWG
        UVAUURWOWFZUWBYSUVIUWAUWGUWHVDUWDUWFYTUURWPWQYSUVAWRUKUURWRUKUWHUWBWSYS
        UVAUWEWTYSUURUWFWTUVAUURXAWQXBXGUVAUURXCXDUVAUSUURVMWNXHVRABCDEFGHIJKLM
        UUEOPQRSTUAUBUCUDUEUFUGUHUIXEVRABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIXF
        XIUUCDUUAKUOZDUUMUUOXJZKUOUSUUQUUCUUAUWJDKUUCUVEUUAUWJUTUVGUUDULYTXKWNX
        LUUCUVMUWIUSYSUUBUVLUVMUWIUTZUVQUVLYSYTUUSUKUWKUVKUUSYTUURXMXNABCDEFGHI
        JKLMYTOPQRSTUAUBUCUDUEUFUGUHUIXEXOVRUUCUVLUVNUVPXPXRUUCABCEFGDHIJKLMOPQ
        UUMUUORSTUAUBUCUDUEUFUGUHUIYSDXQUKZUUBYSUVKXQUKDUVKVKZUWLULUURXSYSDQUKZ
        UWMDQJXTZUWNUWMDYAUMOUTDOPQRSTUAYBYCWNUVKDYDYEVGUUCULUUEYFUUCUUDYTYFUUC
        UUDWRUKUUEUUDWOWFUUMUUOYGYHUTUUCUUDUVSWTUUDYIULUUEUUDYTYJVOYKYLYQUUCUUG
        YRUKUUIYRUKUUKUULVDUUCUUGUUCADEHLUUEOPQRSTUAUBUCYSUWNUUBUWOVGUUCUUDULUV
        SUVJWGYMYNUUCUUIUUCAUUHEHLNOPQRSTUAUBUCYSUUHQUKUUBADEFGHIJLMOPQRSTUAUBU
        CUDUEUFUGUHYOVGUUCNULYTUVRVIYMYNUUGUUIYPWQWA $.
    $}

    $d k S $.  $d k J $.
    ${
      $d u v C $.  $d u v I $.  $d u v J $.  $d u v R $.  $d u v S $.
      $d w y z $.  $d c k y z $.  $d y z C $.  $d y z F $.  $d y z M $.
      $d y z N $.  $d k w y z $.  $d w C $.  $d w F $.  $d w M $.  $d w N $.
      $d i J $.
      $( Value of ` F ` for a reversed counting ` ( R `` C ) ` , before the
         first tie, cannot be zero.  (Contributed by Thierry Arnoux,
         25-Apr-2017.)  (Revised by AV, 6-Oct-2020.) $)
      ballotlemfrcn0 $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) /\
        J < ( I ` C ) ) -> ( ( F ` ( R ` C ) ) ` J ) =/= 0 ) $=
        ( vz vw vy vv vu cdif wcel c1 caddc co cfz cfv clt wbr w3a cc0 wne cmin
        wceq wn 1zzd cz cn nnaddcl mp2an nnzi wa ballotlemsdom elfzelzd 3adant3
        a1i zsubcld cle ballotlemsgt1 zltlem1 syl21anc zred 1red resubcld simp1
        biimpa ballotlemiex simpld elfzelz 3syl 3ad2ant2 elfzle1 ballotlemsel1i
        simp3 ltled elfzd syl2anc elfzle2 syl wb zlem1lt mpbid letrd wi cv crab
        cinf biid sylibr ballotlemi breq2d 3ad2ant1 wor ltso ballotlemsup inflb
        cr con2d sylc fveqeq2 elrab sylnib imnan neqned cneg ballotlemro adantr
        mpd adantl ballotlemfelz zcnd negeq0d cfn cin chash cmpo ballotlemfrceq
        eqid eqeq1d bitr4d necon3bid mpbird ) BNHUKULZKUMLMUNUOZUPUOZULZKBJUQZU
        RUSZUTZKBDUQZIUQUQZVAVBZKBEUQUQZUMVCUOZBIUQZUQZVAVBZUUIUUPVAUUIUUNUUEUL
        ZUUPVAVDZVEZUUIUUNUMUUDUUIVFZUUDVGULUUIUUDLVHULMVHULUUDVHULPQLMVIVJVKVP
        ZUUIUUMUMUUCUUFUUMVGULZUUHUUCUUFVLUUMUMUUDABCEFGHIJKLMNOPQRSTUAUBUCUDVM
        VNVOZUVAVQUUIUMVGULZUVCUMUUMURUSZUMUUNVRUSZUVAUVDABCEFGHIJKLMNOPQRSTUAU
        BUCUDVSUVEUVCVLUVFUVGUMUUMVTWFWAUUIUUNUUGUUDUUIUUMUMUUIUUMUVDWBUUIWCWDZ
        UUIUUGUUIUUCUUGUUEULZUUGVGULZUUCUUFUUHWEZUUCUVIUUGUUOUQVAVDABCFGHIJLMNO
        PQRSTUAUBUCWGWHZUUGUMUUDWIWJZWBZUUIUUDUVBWBUUIUUNUUGUVHUVNUUIUUMUUGVRUS
        ZUUNUUGURUSZUUIUUMUMUUGUPUOZULZUVOUUIUUCKUVQULZUVRUVKUUIKUMUUGUVAUVMUUF
        UUCKVGULZUUHKUMUUDWIWKZUUFUUCUMKVRUSUUHKUMUUDWLWKUUIKUUGUUIKUWAWBUVNUUC
        UUFUUHWNWOWPZABCEFGHIJKLMNOPQRSTUAUBUCUDWMWQUUMUMUUGWRWSUUIUVCUVJUVOUVP
        WTUVDUVMUUMUUGXAWQXBZWOUUIUUCUVIUUGUUDVRUSUVKUVLUUGUMUUDWRWJXCWPUUIUURU
        USVLZVEUURUUTXDUUIUUNGXEZUUOUQVAVDZGUUEXFZULZUWDUUIUUCUUNUWGXQURXGZURUS
        ZUWHVEUVKUUIUVPUWJUUIUVPUVPUWCUVPXHXIUUCUUFUVPUWJWTUUHUUCUUGUWIUUNURABC
        FGHIJLMNOPQRSTUAUBUCXJXKXLXBUUCUWHUWJUUCUFUGUHXQUWGUUNURXQURXMUUCXNVPAU
        HUFUGBCFGHIJLMNOPQRSTUAUBUCXOXPXRXSUWFUUSGUUNUUEUWEUUNVAUUOXTYAYBUURUUS
        YCXIYHYDUUIUUCUVSUULUUQWTUVKUWBUUCUVSVLZUUKVAUUPVAUWKUUKVAVDUUKYEZVAVDU
        USUWKUUKUWKUUKUWKAUUJCFIKLMNOPQRSTUUCUUJNULUVSABCDEFGHIJLMNOPQRSTUAUBUC
        UDUEYFYGUVSUVTUUCKUMUUGWIYIYJYKYLUWKUUPUWLVAAUIUJBCDEFGHUJUIYMYMUIXEZUJ
        XEZYNYOUQUWMUWNUKYOUQVCUOYPZIJKLMNOPQRSTUAUBUCUDUEUWOYRYQYSYTUUAWQUUB
        $.

      $( Range of ` R ` .  (Contributed by Thierry Arnoux, 19-Apr-2017.) $)
      ballotlemrc $p |- ( C e. ( O \ E ) -> ( R ` C ) e. ( O \ E ) ) $=
        ( vv vu cdif wcel cfv cv cc0 cle wbr c1 caddc cfz wrex ballotlemro wceq
        ballotlemiex simpld cfn cin chash cmin cmpo eqid ballotlemfrci eqbrtrdi
        co 0le0 fveq2 breq1d rspcev syl2anc ballotlemodife sylanbrc ) BMHUGZUHZ
        BDUIZMUHFUJZVTIUIZUIZUKULUMZFUNKLUOVJUPVJZUQZVTVRUHABCDEFGHIJKLMNOPQRST
        UAUBUCUDURVSBJUIZWEUHZWGWBUIZUKULUMZWFVSWHWGBIUIUIUKUSABCFGHIJKLMNOPQRS
        TUAUBUTVAVSWIUKUKULAUEUFBCDEFGHUFUEVBVBUEUJZUFUJZVCVDUIWKWLUGVDUIVEVJVF
        ZIJKLMNOPQRSTUAUBUCUDWMVGVHVKVIWDWJFWGWEWAWGUSWCWIUKULWAWGWBVLVMVNVOAVT
        CFHIKLMNOPQRSTVPVQ $.
    $}

    $d k i R $.
    ${
      $d k x y $.  $d x y C $.  $d y E $.  $d x y F $.  $d y I $.  $d x y M $.
      $d x y N $.  $d y O $.  $d y R $.  $d u v C $.  $d u v I $.  $d u v R $.
      $d u v S $.  $d u v y $.  $d i y $.
      $( Applying ` R ` does not change first ties.  (Contributed by Thierry
         Arnoux, 19-Apr-2017.)  (Revised by AV, 6-Oct-2020.) $)
      ballotlemirc $p |- ( C e. ( O \ E ) -> ( I ` ( R ` C ) ) = ( I ` C ) ) $=
        ( vy vv vu cdif wcel cfv cv cc0 wceq c1 caddc co cfz cr clt ballotlemrc
        crab cinf ballotlemi syl wor ltso a1i ballotlemiex simpld elfzelzd zred
        cfn cin chash cmin cmpo eqid ballotlemfrci fveqeq2 elrab sylanbrc wa wn
        wbr elrabi anim2i simpr ballotlemfrcn0 neneqd simprbi nsyl 3expa syldan
        w3a ex con2d imp sylancom infmin eqtrd ) BMHUHZUIZBDUJZJUJZGUKZXCIUJZUJ
        ULUMZGUNKLUOUPZUQUPZVAZURUSVBZBJUJZXBXCXAUIXDXKUMABCDEFGHIJKLMNOPQRSTUA
        UBUCUDUTAXCCFGHIJKLMNOPQRSTUAUBVCVDXBUEURXJXLUSURUSVEXBVFVGXBXLXBXLUNXH
        XBXLXIUIZXLBIUJUJULUMABCFGHIJKLMNOPQRSTUAUBVHVIZVJVKXBXMXLXFUJULUMZXLXJ
        UIXNAUFUGBCDEFGHUGUFVLVLUFUKZUGUKZVMVNUJXPXQUHVNUJVOUPVPZIJKLMNOPQRSTUA
        UBUCUDXRVQVRXGXOGXLXIXEXLULXFVSVTWAXBUEUKZXJUIZXBXSXIUIZWBZXSXLUSWDZWCZ
        XTYAXBXGGXSXIWEWFYBXTYDYBYCXTYBYCXTWCZYBYCYCYEYBYCWGXBYAYCYEXBYAYCWNZXS
        XFUJZULUMZXTYFYGULABCDEFGHIJXSKLMNOPQRSTUAUBUCUDWHWIXTYAYHXGYHGXSXIXEXS
        ULXFVSVTWJWKWLWMWOWPWQWRWSWT $.
    $}

    $( due to x used in ballotlemirc $)
    $d x c $.  $d x C $.  $d x F $.  $d x M $.  $d x N $.  $d c I $.  $d d S $.
    ${
      $d d i x k $.  $d d E $.  $d d I $.  $d d O $.
      $( Lemma for ~ ballotlemrinv .  (Contributed by Thierry Arnoux,
         18-Apr-2017.) $)
      ballotlemrinv0 $p |- ( ( C e. ( O \ E ) /\ D = ( ( S ` C ) " C ) ) ->
                             ( D e. ( O \ E ) /\ C = ( ( S ` D ) " D ) ) ) $=
        ( cdif wcel cfv cima wceq ballotlemrval adantr simpr eqtr4d ballotlemrc
        wa eqeltrrd ccnv c1 caddc cfz wf1o ballotlemsf1o simprd eqcomd imaeq12d
        co simpl ballotlemirc fveq2d eqtr3d ballotlemieq syl3anc imaeq1d simpld
        wf1 wss f1of1 3syl chash ballotlemelo simplbi f1imacnv syl2anc 3eqtr3rd
        eldifi jca ) BNIUFZUGZCBFUHZBUIZUJZUPZCWHUGZBCFUHZCUIZUJWMBEUHZCWHWMWQW
        KCWIWQWKUJWLABDEFGHIJKLMNOPQRSTUAUBUCUDUEUKULWIWLUMZUNZWIWQWHUGWLABDEFG
        HIJKLMNOPQRSTUAUBUCUDUEUOULUQZWMWJCUIWJURZWKUIZWPBWMWJXACWKWMXAWJWIXAWJ
        UJZWLWIUSLMUTVGVAVGZXDWJVBZXCABDFGHIJKLMNOPQRSTUAUBUCUDVCZVDULVEWRVFWMW
        JWOCWMWIWNBKUHZCKUHZUJWJWOUJWIWLVHZWTWMWQKUHZXGXHWIXJXGUJWLABDEFGHIJKLM
        NOPQRSTUAUBUCUDUEVIULWMWQCKWSVJVKABCDFGHIJKLMNOPQRSTUAUBUCUDVLVMVNWMXDX
        DWJVPZBXDVQZXBBUJWMWIXEXKXIWIXEXCXFVOXDXDWJVRVSWMWIBNUGZXLXIBNIWFXMXLBV
        TUHLUJBLMNOPQRWAWBVSXDXDBWJWCWDWEWG $.

      $( ` R ` is its own inverse : it is an involution.  (Contributed by
         Thierry Arnoux, 10-Apr-2017.) $)
      ballotlemrinv $p |- `' R = R $=
        ( vd cdif cv cfv cima cmpt ccnv wceq wtru wcel wa ballotlemrinv0 impbii
        wb a1i mptcnv mptru fveq2 id imaeq12d cbvmptv eqtri cnveqi 3eqtr4i ) ML
        GUEZMUFZDUGZVIUHZUIZUJZVLCUJCVMUDVHUDUFZDUGZVNUHZUIZVLVMVQUKULMUDVHVKVH
        VPVIVHUMVNVKUKUNZVNVHUMVIVPUKUNZUQULVRVSAVIVNBCDEFGHIJKLMNOPQRSTUAUBUCU
        OAVNVIBCDEFGHIJKLMNOPQRSTUAUBUCUOUPURUSUTUDMVHVPVKVNVIUKZVOVJVNVIVNVIDV
        AVTVBVCVDVECVLUCVFUCVG $.
    $}

    $( When the vote on the first tie is for A, the first vote is also for A on
       the reverse counting.  (Contributed by Thierry Arnoux, 18-Apr-2017.) $)
    ballotlem1ri $p |- ( C e. ( O \ E ) ->
                                     ( 1 e. ( R ` C ) <-> ( I ` C ) e. C ) ) $=
      ( cdif wcel c1 cfv caddc co cmin cfz cle wbr wb cuz cn nnaddcl mp2an nnuz
      eleqtri eluzfz1 cc0 ballotlemiex simpld elfzle1 syl ballotlemrv1 mpd3an23
      mp1i wceq elfzelzd zcnd 1cnd pncand eleq1d bitrd ) BMHUEUFZUGBDUHUFZBJUHZ
      UGUIUJUGUKUJZBUFZVTBUFVRUGUGKLUIUJZULUJZUFZUGVTUMUNZVSWBUOWCUGUPUHZUFWEVR
      WCUQWGKUQUFLUQUFWCUQUFOPKLURUSUTVAUGWCVBVJVRVTWDUFZWFVRWHVTBIUHUHVCVKABCF
      GHIJKLMNOPQRSTUAUBVDVEZVTUGWCVFVGABCDEFGHIJUGKLMNOPQRSTUAUBUCUDVHVIVRWAVT
      BVRVTUGVRVTVRVTUGWCWIVLVMVRVNVOVPVQ $.

    $d x k i $.  $d c k $.
    ${
      $d b E $.  $d b c O $.  $d b R $.

      $( ` R ` is a bijection between two subsets of ` ( O \ E ) ` : one where
         a vote for A is picked first, and one where a vote for B is picked
         first.  (Contributed by Thierry Arnoux, 12-Dec-2016.) $)
      ballotlem7 $p |- ( R |` { c e. ( O \ E ) | 1 e. c } ) :
      { c e. ( O \ E ) | 1 e. c } -1-1-onto-> { c e. ( O \ E ) | -. 1 e. c } $=
        ( vb c1 cv wcel cdif crab wn cfv cima funmpt2 ballotlemrinv wss wral wa
        rabid ballotlemrc adantr ballotlem1c ex ballotlem1ri notbid sylibrd imp
        jca sylbi rgen wceq eleq2 cbvrabv eleq2i bitr3i ralbii mpbi wfun cdm wb
        elrab ssrab2 cvv fvex imaexg ax-mp dmmpti sseqtrri nfrab1 nfmpt1 nfcxfr
        cmpt funimass4f mp2an mpbir ballotlemic rinvf1o ) UEMUFZUGZMLGUHZUIZWRU
        JZMWSUIZCMWSWQDUKZWQULZCUCUMZABCDEFGHIJKLMNOPQRSTUAUBUCUNCWTULXBUOZWQCU
        KZXBUGZMWTUPZXGWSUGZUEXGUGZUJZUQZMWTUPXIXMMWTWQWTUGWQWSUGZWRUQZXMWRMWSU
        RXOXJXLXNXJWRAWQBCDEFGHIJKLMNOPQRSTUAUBUCUSZUTXNWRXLXNWRWQIUKWQUGZUJZXL
        XNWRXRAWQBEFGHIJKLMNOPQRSTUAVAVBXNXKXQAWQBCDEFGHIJKLMNOPQRSTUAUBUCVCZVD
        VEVFVGVHVIXMXHMWTXMXGUEUDUFZUGZUJZUDWSUIZUGXHYBXLUDXGWSXTXGVJYAXKXTXGUE
        VKZVDVTYCXBXGYBXAUDMWSXTWQVJYAWRXTWQUEVKZVDVLVMVNVOVPCVQZWTCVRZUOXFXIVS
        XEWTWSYGWRMWSWAMWSXDCXCWBUGXDWBUGWQDWCXCWQWBWDWEUCWFZWGZMWTXBCWRMWSWHZX
        AMWSWHZMCMWSXDWKUCMWSXDWIWJZWLWMWNCXBULWTUOZXGWTUGZMXBUPZXJXKUQZMXBUPYO
        YPMXBWQXBUGXNXAUQZYPXAMWSURYQXJXKXNXJXAXPUTXNXAXKXNXAXQXKXNXAXQAWQBEFGH
        IJKLMNOPQRSTUAWOVBXSVEVFVGVHVIYPYNMXBYPXGYAUDWSUIZUGYNYAXKUDXGWSYDVTYRW
        TXGYAWRUDMWSYEVLVMVNVOVPYFXBYGUOYMYOVSXEXBWSYGXAMWSWAYHWGZMXBWTCYKYJYLW
        LWMWNYIYSWP $.
    $}

    $( There are as many countings with ties starting with a ballot for ` A `
       as there are starting with a ballot for ` B ` .  (Contributed by Thierry
       Arnoux, 7-Dec-2016.) $)
    ballotlem8 $p |- ( # ` { c e. ( O \ E ) | 1 e. c } )
                   = ( # ` { c e. ( O \ E ) | -. 1 e. c } ) $=
      ( c1 cv wcel cdif crab wn cres wf1o cen wbr chash cfv wceq ballotlem7 cvv
      ballotlemoex difexg ax-mp rabex f1oen hasheni mp2b ) UDMUEUFZMLGUGZUHZVFU
      IMVGUHZCVHUJZUKVHVIULUMVHUNUOVIUNUOUPABCDEFGHIJKLMNOPQRSTUAUBUCUQVHVIVJVF
      MVGLURUFVGURUFJKLMNOPUSLGURUTVAVBVCVHVIVDVE $.

    $d x c $.  $d x E $.  $d x O $.
    $( Bertrand's ballot problem : the probability that A is ahead throughout
       the counting.  The proof formalized here is a proof "by reflection", as
       opposed to other known proofs "by induction" or "by permutation".  This
       is Metamath 100 proof #30.  (Contributed by Thierry Arnoux,
       7-Dec-2016.) $)
    ballotth $p |- ( P ` E ) = ( ( M - N ) / ( M + N ) ) $=
      ( cfv c1 cdif chash cdiv co cmin caddc cmul wss wceq cc0 clt wbr cfz wral
      c2 crab ssrab2 eqsstri cpw wcel cfn fzfi pwfi mpbi ssfi mp2an elexi fveq2
      cv elpw oveq1d ovex fvmpt sylbir ax-mp hashssdif eqcomi cn0 hashcl nn0cni
      difss subsub23i oveq1i eqtr4i cc wne wa cbc ballotlem1 cle nnnn0i nnaddcl
      cn nnrei nn0addge1i elfz2nn0 mpbir3an bccl2 nnne0i pm3.2i divsubdir mp3an
      eqnetri dividi 3eqtri wn ballotlem8 cun rabxm fveq2i c0 sstri rabnc eqtri
      cin hashun elpw2 mpbir ballotlem2 nfrab1 dfssf ballotlem4 imdistani rabid
      eldif 3imtr4i simprbi sylanbrc oveq2i 2cn divassi 2timesi 3eqtr2i nncni
      wi mpgbir rabss2 3eqtr3i 3eqtr4ri mulcli addsub4i subidi addridi 3eqtr3ri
      eqssi subcli oveq12i ) GBUDZUELGUFZUGUDZLUGUDZUHUIZUJUIZUEUTKJKUKUIZUHUIZ
      ULUIZUJUIZJKUJUIZUUSUHUIZUUMUUPUUOUJUIZUUPUHUIZUUPUUPUHUIZUUQUJUIZUURUUMG
      UGUDZUUPUHUIZUVFGLUMZUUMUVJUNZGUOEVNMVNZHUDUDUPUQEUEUUSURUIZUSZMLVALSUVOM
      LVBVCZUVKGLVDZVEUVLGLGVFLVFVEZUVKGVFVEZUVNVDZVFVEZLUVTUMUVRUVNVFVEUWAUEUU
      SVGUVNVHVIZLUVMUGUDJUNZMUVTVAUVTPUWCMUVTVBVCZUVTLVJVKZUVPLGVJVKZVLVOAGAVN
      ZUGUDZUUPUHUIZUVJUVQBUWGGUNUWHUVIUUPUHUWGGUGVMVPQUVIUUPUHVQVRVSVTUVEUVIUU
      PUHUUPUVIUJUIZUUOUNUVEUVIUNUUOUWJUVRUVKUUOUWJUNUWEUVPLGWAVKWBUUPUVIUUOUUP
      UVRUUPWCVEUWELWDVTWEZUVIUVSUVIWCVEUWFGWDVTWEUUOUUNVFVEZUUOWCVEUVRUUNLUMZU
      WLUWELGWFZLUUNVJVKUUNWDVTWEZWGVIWHWIUUPWJVEZUUOWJVEUWPUUPUOWKZWLUVFUVHUNU
      WKUWOUWPUWQUWKUUPUUSJWMUIZUOJKLMNOPWNUWRJUOUUSURUIVEZUWRWRVEUWSJWCVEUUSWC
      VEJUUSWOUQJNWPUUSJWRVEKWRVEUUSWRVENOJKWQVKZWPJKJNWSKOWPWTJUUSXAXBJUUSXCVT
      XDXHZXEUUPUUOUUPXFXGUVGUEUUQUJUUPUWKUXAXIWHXJUVAUUQUEUJUEUVMVEZMUUNVAZUGU
      DZUXBXKZMUUNVAZUGUDZUKUIZUUPUHUIUXGUXGUKUIZUUPUHUIZUUQUVAUXHUXIUUPUHUXDUX
      GUXGUKABCDEFGHIJKLMNOPQRSTUAUBUCXLWHWHUUOUXHUUPUHUUOUXCUXFXMZUGUDZUXHUUNU
      XKUGUXBMUUNXNXOUXCVFVEZUXFVFVEZUXCUXFXTXPUNUXLUXHUNUWAUXCUVTUMUXMUWBUXCLU
      VTUXCUUNLUXBMUUNVBUWNXQUWDXQUVTUXCVJVKUWAUXFUVTUMUXNUWBUXFLUVTUXFUUNLUXEM
      UUNVBUWNXQUWDXQUVTUXFVJVKZUXBMUUNXRUXCUXFYAXGXSWHUVAUTUXGUUPUHUIZULUIUTUX
      GULUIZUUPUHUIUXJUUTUXPUTULUXEMLVAZBUDZUXRUGUDZUUPUHUIZUUTUXPUXRUVQVEZUXSU
      YAUNUYBUXRLUMUXEMLVBUXRLLVFUWEVLYBYCAUXRUWIUYAUVQBUWGUXRUNUWHUXTUUPUHUWGU
      XRUGVMVPQUXTUUPUHVQVRVTABJKLMNOPQYDUXTUXGUUPUHUXRUXFUGUXRUXFUXRUXFUMUVMUX
      RVEZUVMUXFVEZYTMMUXRUXFUXEMLYEUXEMUUNYEYFUYCUVMUUNVEZUXEUYDUVMLVEZUXEWLUY
      FUVMGVEXKZWLUYCUYEUYFUXEUYGAUVMBEGHJKLMNOPQRSYGYHUXEMLYIZUVMLGYJYKUYCUYFU
      XEUYHYLUXEMUUNYIYMUUAUWMUXFUXRUMUWNUXEMUUNLUUBVTUUJXOWHUUCYNUTUXGUUPYOUXG
      UXNUXGWCVEUXOUXFWDVTWEZUWKUXAYPUXQUXIUUPUHUXGUYIYQWHYRUUDYNUUSUTKULUIZUJU
      IZUUSUHUIZUUSUUSUHUIZUYJUUSUHUIZUJUIZUVDUVBUUSWJVEZUYJWJVEUYPUUSUOWKZWLUY
      LUYOUNUUSUWTYSZUTKYOKOYSZUUEUYPUYQUYRUUSUWTXDZXEUUSUYJUUSXFXGUYKUVCUUSUHU
      YKUUSKKUKUIZUJUIZUVCUYJVUAUUSUJKUYSYQYNVUBUVCKKUJUIZUKUIUVCUOUKUIUVCJKKKJ
      NYSZUYSUYSUYSUUFVUCUOUVCUKKUYSUUGYNUVCJKVUDUYSUUKUUHXJXSWHUYMUEUYNUVAUJUU
      SUYRUYTXIUTKUUSYOUYSUYRUYTYPUULUUIYR $.
  $}

