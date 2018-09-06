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
      We then characterise a counting ` c ` as the set of indices in the
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
      ( c1 caddc co cfz cpw ovex pwex cv chash cfv wceq crab ssrab2 eqsstri
      ssexi ) CHABIJZKJZLZUDHUCKMNCDOPQARZDUESUEGUFDUETUAUB $.

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
        ( vd wcel c1 co cfz chash cfv wceq wa cv fveq2 eqeq1d caddc cpw cbvrabv
        wss crab eqtri elrab2 ovex elpw2 anbi1i bitri ) ADJAKBCUALZMLZUBZJZANOZ
        BPZQAUMUDZUQQIRZNOZBPZUQIAUNDUSAPUTUPBUSANSTDERZNOZBPZEUNUEVAIUNUEHVDVA
        EIUNVBUSPVCUTBVBUSNSTUCUFUGUOURUQAUMKULMUHUIUJUK $.
    $}

    $( Let ` P ` be the uniform discrete probability measure over ` O ` . $)
    ballotth.p $e |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) ) $.

    ${
      $d c i M $.  $d c i N $.  $d c i x O $.

      $( The probability that the first vote picked in a count is a B
         (Contributed by Thierry Arnoux, 23-Nov-2016.) $)
      ballotlem2 $p |- ( P ` { c e. O | -. 1 e. c } ) = ( N / ( M + N ) ) $=
        ( vi c1 wcel cfv co c2 wa cle wbr mp2an cv wn crab caddc cmin cbc chash
        cdiv wceq ssrab2 ballotlemoex elpw2 mpbir fveq2 oveq1d ovex fvmpt ax-mp
        cpw wss cfz cab cuz cn 2nn nnge1 cz wb 1z 2z eluz fzss1 sspwb sseli clt
        mpbi 1lt2 1re 2re ltnlei elfzle1 mto elelpwi ancom mtbi imnani jca ssin
        cin wo 1p1e2 nnrei le2addi eqbrtrri readdcli letri nnaddcl nnzi elfzp12
        biimpi orcanai oveq1i syl6eleq ss2abi abid2 ineq1i eqtr3i 3sstr3i mpan2
        inab sstr sylbi vex elpw wi wal wex df-ex bicomi con1bii df-clel notbii
        ssab imnan bitr4i 3bitr4ri bitr2i anbi12i 3imtr4i anbi1i df-rab cneg cc
        albii nncni 2cn ax-1cn 3eqtri eqtri cc0 impbii rabeq2i an32 3eqtr4i cfn
        abbii fveq2i fzfi hashbc eluz1i mpbir2an hashfz addcli mp3an negsubdi2i
        subadd23 2m1e1 negeqi oveq2i negsubi ballotlem1 oveq12i w3a 0le1 0re cr
        crp nngt0i elrpii ltaddrp 3pm3.2i 0z elfzm11 bcm1n pncan2 ) LFUAZMZUBZF
        EUCZBNZCDUDOZLUEOZCUFOZUWACUFOZUHOZUWACUEOZUWAUHOZDUWAUHOUVTUVSUGNZEUGN
        ZUHOZUWEUVSEUSZMZUVTUWJUIUWLUVSEUTUVRFEUJUVSECDEFGHIUKULUMAUVSAUAZUGNZU
        WIUHOUWJUWKBUWMUVSUIUWNUWHUWIUHUWMUVSUGUNUOJUWHUWIUHUPUQURUWHUWCUWIUWDU
        HUVPUGNCUIZFPUWAVAOZUSZUCZUGNZUWHUWCUWRUVSUGUVPUWQMZUWOQZFVBUVPEMZUVRQZ
        FVBUWRUVSUXAUXCFUXAUVPLUWAVAOZUSZMZUVRQZUWOQZUXCUWTUXGUWOUWTUXGUWTUXFUV
        RUWQUXEUVPUWPUXDUTZUWQUXEUTPLVCNZMZUXIUXKLPRSZPVDMUXLVEPVFURZLVGMZPVGMU
        XKUXLVHVIVJLPVKTUMPLUWAVLURUWPUXDVMVPVNUWTUVQUVQUWTQZUWTUVQQUXOLUWPMZUX
        PPLRSZLPVOSUXQUBVQLPVRVSVTVPLPUWAWAWBLUVPUWPWCWBUVQUWTWDWEWFWGUVPUXDUTZ
        UVPKUAZLUIZUBZKVBZUTZQZUVPUWPUTZUXGUWTUYDUVPUXDUYBWIZUTZUYEUVPUXDUYBWHU
        YGUYFUWPUTUYEUXSUXDMZUYAQZKVBZUXSUWPMZKVBUYFUWPUYIUYKKUYIUXSLLUDOZUWAVA
        OZUWPUYHUXTUXSUYMMZUYHUXTUYNWJZUWAUXJMZUYHUYOVHUYPLUWARSZUXLPUWARSZUYQU
        XMUYLPUWARWKLCRSZLDRSZUYLUWARSCVDMZUYSGCVFURZDVDMZUYTHDVFURLLCDVRVRCGWL
        ZDHWLZWMTWNZLPUWAVRVSCDVUDVUEWOWPTUXNUWAVGMZUYPUYQVHVIUWAVUAVUCUWAVDMZG
        HCDWQTZWRZLUWAVKTUMUXSLUWAWSURWTXAUYLPUWAVAWKXBXCXDUYHKVBZUYBWIUYJUYFUY
        HUYAKXJVUKUXDUYBKUXDXEXFXGKUWPXEXHUVPUYFUWPXKXIXLUXFUXRUVRUYCUVPUXDFXMZ
        XNUYCUXSUVPMZUYAXOZKXPZUVRUYAKUVPYCUXTVUMQZKXQZUBVUPUBZKXPZUVRVUOVUSVUQ
        VUQVUSUBVUPKXRXSXTUVQVUQKLUVPYAYBVUOVUMUXTQZUBZKXPVUSVUNVVAKVUMUXTYDYNV
        URVVAKVUPVUTUXTVUMWDYBYNYEYFYGYHUVPUWPVULXNYIUUAYJUXCUXFUWOQZUVRQUXHUXB
        VVBUVRUWOFEUXEIUUBYJUXFUVRUWOUUCYEYEUUFUWOFUWQYKUVRFEYKUUDUUGUWPUGNZCUF
        OZUWSUWCUWPUUEMCVGMZVVDUWSUIPUWAUUHCGWRZFUWPCUUITVVCUWBCUFVVCUWALYLZUDO
        ZUWBVVCUWAPUEOLUDOZUWALPUEOZUDOZVVHUWAPVCNMZVVCVVIUIVVLVUGUYRVUJVUFPUWA
        VJUUJUUKPUWAUULURUWAYMMPYMMLYMMVVIVVKUICDCGYOZDHYOZUUMZYPYQUWAPLUUPUUNV
        VJVVGUWAUDPLUEOZYLVVJVVGPLYPYQUUOVVPLUUQUURXGUUSYRUWALVVOYQUUTYSXBXGXGC
        DEFGHIUVAUVBYSCYTUWBVAOMZVUHUWEUWGUIVVQVVEYTCRSZCUWAVOSZUVCZVVEVVRVVSVV
        FYTLRSUYSVVRUVDVUBYTLCUVEVRVUDWPTCUVFMDUVGMVVSVUDDVUEDHUVHUVICDUVJTUVKY
        TVGMVUGVVQVVTVHUVLVUJCYTUWAUVMTUMVUICUWAUVNTUWFDUWAUHCYMMDYMMUWFDUIVVMV
        VNCDUVOTXBYR $.
    $}

    $d c i F $.  $d j F $.  $d k F $.
    $( F is the difference between ballots for A and B
      among the i first ballots picked in a given count ` c ` .
      Those ballots for A are in ` c `, i.e. in ` ( ( 1 ... i ) i^i c ) `
      Those ballots for B are out of ` c `, i.e. in ` ( ( 1 ... i ) \ c ) ` $)
    ballotth.f $e |- F = ( c e. O |-> ( i e. ZZ |->
      ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) ) $.

    $d i c $.  $d i C $.
    ${
      $d b O $.  $d b C $.  $d b c $.  $d b i $.  $d i J $.
      ballotlemfval.c $e |- ( ph -> C e. O ) $.
      ballotlemfval.j $e |- ( ph -> J e. ZZ ) $.

      $d i ph $.
      $( The value of F. (Contributed by Thierry Arnoux, 23-Nov-2016.) $)
      ballotlemfval $p |- ( ph -> ( ( F ` C ) ` J ) =
        ( ( # ` ( ( 1 ... J ) i^i C ) ) - ( # ` ( ( 1 ... J ) \ C ) ) ) ) $=
        ( chash cfv vb c1 cv cfz co cin cdif cmin cz cvv wcel cmpt simpl ineq2d
        wceq wa fveq2d difeq2d oveq12d mpteq2dva difeq2 mpteq2dv cbvmptv eqtr4i
        ineq2 zex mptex fvmpt syl oveq2 ineq1d difeq1d adantl ovex a1i fvmptd )
        AEGUBEUCZUDUEZCUFZSTZVRCUGZSTZUHUEZUBGUDUEZCUFZSTZWDCUGZSTZUHUEZUICFTZU
        JACJUKWJEUIWCULZUOQUACEUIVRUAUCZUFZSTZVRWLUGZSTZUHUEZULZWKJFWLCUOZEUIWQ
        WCWSVQUIUKZUPZWNVTWPWBUHXAWMVSSXAWLCVRWSWTUMZUNUQXAWOWASXAWLCVRXBURUQUS
        UTFKJEUIVRKUCZUFZSTZVRXCUGZSTZUHUEZULZULUAJWRULPUAKJWRXIWLXCUOZEUIWQXHX
        JWNXEWPXGUHXJWMXDSWLXCVRVEUQXJWOXFSWLXCVRVAUQUSVBVCVDEUIWCVFVGVHVIVQGUO
        ZWCWIUOAXKVTWFWBWHUHXKVSWESXKVRWDCVQGUBUDVJZVKUQXKWAWGSXKVRWDCXLVLUQUSV
        MRWIUJUKAWFWHUHVNVOVP $.

      $( ` ( F `` C ) ` has values in ` ZZ ` .  (Contributed by Thierry Arnoux,
         23-Nov-2016.) $)
      ballotlemfelz $p |- ( ph -> ( ( F ` C ) ` J ) e. ZZ ) $=
        ( cfv wcel c1 cfz co cin chash cdif cmin ballotlemfval cfn cn0 wss fzfi
        cz inss1 ssfi mp2an hashcl ax-mp nn0zi difss zsubcl syl6eqel ) AGCFSSUA
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
        wa nnzd adantr csn cun c0 cuz cn elnnuz sylib fzspl ineq1d indir syl6eq
        syl disjsn eqeq1i bitr3i biimpi adantl uneq2d un0 3eqtrd fveq2d difeq1d
        incom a1i difundir disj3 eqcomd sylan9eq cz uzid uznfz 3syl difss sseli
        cfn nsyl wss fzfi ssfi mp2an jctil hashunsng sylc eqtrd oveq12d zsubcld
        1z oveq1d cc cn0 inss1 hashcl ax-mp nn0cni diffi ax-1cn subsub4d eqtr2d
        ex snssi df-ss simpr difin2 difid ineq1i in0 3eqtri addsubd eqtr4d jca
        ) AGCUAZUBZGCFUCZUCZGSUDUEZYHUCZSUDUEZTZUFYFYIYKSUGUEZTZUFAYGYMAYGUMZYI
        SGUHUEZCUIZUJUCZYQCUKZUJUCZUDUEZSYJUHUEZCUIZUJUCZUUCCUKZUJUCZSUGUEZUDUE
        ZYLAYIUUBTZYGABCDEFGHIJKLMNOPQAGRUNZULZUOYPYSUUEUUAUUHUDYPYRUUDUJYPYRUU
        DGUPZCUIZUQZUUDURUQZUUDAYRUUOTZYGAGSUSUCUAZUUQAGUTUAUURRGVAVBZUURYRUUCU
        UMUQZCUIUUOUURYQUUTCSGVCZVDUUCUUMCVEVFVGZUOYPUUNURUUDYGUUNURTZAYGUVCYGC
        UUMUIZURTUVCCGVHUVDUUNURCUUMVRVIVJVKZVLVMUUPUUDTYPUUDVNVSVOVPYPUUAUUFUU
        MUQZUJUCZUUHYPYTUVFUJAYGYTUUFUUMCUKZUQZUVFAUURYTUVITUUSUURYTUUTCUKUVIUU
        RYQUUTCUVAVQUUCUUMCVTVFVGZYGUVHUUMUUFYGUUMUVHYGUVCUUMUVHTUVEUUMCWAVBWBV
        MWCVPYPGWDUAZUUFWJUAZGUUFUAZUBZUMUVGUUHTAUVKYGUUKUOYPUVNUVLYPGUUCUAZUVM
        AUVOUBZYGAUVKGGUSUCUAZUVPUUKGWEZGSGWFZWGUOUUFUUCGUUCCWHZWIWKUUCWJUAZUUF
        UUCWLUVLSYJWMZUVTUUCUUFWNWOWPUUFGWDWQWRWSWTYPYLUUEUUGUDUEZSUDUEUUIYPYKU
        WCSUDAYKUWCTZYGABCDEFYJHIJKLMNOPQAGSUUKSWDUAAXBVSXAULZUOXCYPUUEUUGSUUEX
        DUAZYPUUEUUDWJUAZUUEXEUAUWAUUDUUCWLUWGUWBUUCCXFZUUCUUDWNWOZUUDXGXHXIZVS
        UUGXDUAZYPUUGUVLUUGXEUAUWAUVLUWBUUCCXJXHUUFXGXHXIZVSSXDUAZYPXKVSXLXMVOX
        NAYFYOAYFUMZYIUUBUUESUGUEZUUGUDUEZYNAUUJYFUULUOUWNYSUWOUUAUUGUDUWNYSUUO
        UJUCZUUDUUMUQZUJUCZUWOAYSUWQTYFAYRUUOUJUVBVPUOYFUWQUWSTAYFUUOUWRUJYFUUN
        UUMUUDYFUUMCWLZUUNUUMTGCXOZUUMCXPVBVMVPVLUWNYFUWGGUUDUAZUBZUMUWSUWOTAYF
        XQUWNUXCUWGUWNUVOUXBUWNUVKUVQUVPAUVKYFUUKUOUVRUVSWGUUDUUCGUWHWIWKUWIWPU
        UDGCWQWRVOUWNUUAUVIUJUCZUUFURUQZUJUCZUUGAUUAUXDTYFAYTUVIUJUVJVPUOYFUXDU
        XFTAYFUVIUXEUJYFUVHURUUFYFUWTUVHURTUXAUWTUVHCCUKZUUMUIZURUUMCCXRUXHURUU
        MUIUUMURUIURUXGURUUMCXSXTURUUMVRUUMYAYBVFVGVMVPVLUWNUXEUUFUJUXEUUFTUWNU
        UFVNVSVPVOWTUWNUWPUWCSUGUEYNUWNUUESUUGUWFUWNUWJVSUWMUWNXKVSUWKUWNUWLVSY
        CUWNYKUWCSUGAUWDYFUWEUOXCYDVOXNYE $.

      $d k i j $.  $d j k J $.  $d j k C $.  $d ph k $.
      ballotlemfc0.3 $e |- ( ph ->
                                E. i e. ( 1 ... J ) ( ( F ` C ) ` i ) <_ 0 ) $.
      ballotlemfc0.4 $e |- ( ph -> 0 < ( ( F ` C ) ` J ) ) $.
      $( ` F ` takes value 0 between negative and positive values.
         (Contributed by Thierry Arnoux, 24-Nov-2016.) $)
      ballotlemfc0 $p |- ( ph -> E. k e. ( 1 ... J ) ( ( F ` C ) ` k ) = 0 ) $=
        ( vj cv cfv cc0 wceq cle wbr c1 cfz co crab wrex wral wcel fveq2 breq1d
        wa elrab anbi1i simprlr caddc wn simprl adantrr clt cr cuz fzssuz uzssz
        sstri zssre sseli ltp1d 1re a1i readdcld ltnled mpbid syl simprr adantr
        cz wi simpr fveq2d breq2d wb cn elnnuz sylib eleq1 syl5ibrcom anc2li 1z
        eluzfz2 0le1 0z eluz1i mpbir2an fzss1 sseld ax-mp elfzelz ballotlemfelz
        0re adantl zred sylan2 syl6 imp bitr3d ex con2d cmin nn1m1nn oveq1 nnzd
        wo csn fzsn eqtr3d rexeqdv mpbird ax-1cn eleq2d eqeq2d sylibr 1p1e2 wss
        c2 mp2an mpd breq1 syl2anc simplrr sylan oveq1d adantlrr cfn syl6bbr cc
        rexsng pm2.65da biortn notnot orbi1i elfzp1 nncnd npcand oveq2d 3bitr3d
        orbi2d orcom syl6bb biimpd pm5.6 jctil fzaddel biimp3a 3anidm23 oveq12d
        jctir syl2an 1nn0 nn0addge1i breqtri 2z eluz mpbir syld sylan2d rspccva
        syl6bi sylan2br con3d simpll mpsyl imdistani elfznn ballotlemfp1 simpld
        expr zcnd pncand zlem1lt sylancl bitr4d syl21anc syl12anc condan simprd
        ltled mpdan notbid syldan zleltp1 mpan zre letri3d mpbir2and sylan2b c0
        bitrd wne ssrab2 fzfi ssfi rabn0 fimaxre syl3anc reximddv elrabi anim1i
        reximi2 ) AFUCZCGUDZUDZUEUFZFEUCZUXQUDZUEUGUHZEUIHUJUKZULZUMUXSFUYCUMAU
        BUCZUXPUGUHZUBUYDUNZUXSFUYDUXPUYDUOZUYGURAUXPUYCUOZUXRUEUGUHZURZUYGURZU
        XSUYHUYKUYGUYBUYJEUXPUYCUXTUXPUFUYAUXRUEUGUXTUXPUXQUPUQUSUTAUYLURZUXSUY
        JUEUXRUGUHZAUYIUYJUYGVAUYMUYNUXRUIVBUKZUEUGUHZVCZUYMUXPUIVBUKZUXQUDZUEU
        GUHZVCZUYQUYMUYRUXPUGUHZVCZVUAUYMUYIVUCAUYKUYIUYGAUYIUYJVDZVEUYIUXPUYRV
        FUHVUCUYIUXPUYCVGUXPUYCWCVGUYCUIVHUDZWCUIHVIUIVJVKVLVKZVMZVNUYIUXPUYRVU
        GUYIUXPUIVUGUIVGUOZUYIVOVPVQVRVSVTZUYMUYGUYRUYCUOZVUCVUAWDAUYKUYGWAAUYK
        VUJUYGAUYKVUJAUYJUXPHUFZVCZUYIVUJAVUKUYJAVUKUYJVCZAVUKURZUEHUXQUDZVFUHZ
        VUMAVUPVUKUAWBVUNUEUXRVFUHZVUPVUMVUNUXRVUOUEVFVUNUXPHUXQAVUKWEWFWGAVUKV
        UQVUMWHZAVUKAUYIURVURAVUKUYIAUYIVUKHUYCUOZAHVUEUOZVUSAHWIUOZVUTSHWJWKUI
        HWPVTUXPHUYCWLWMWNUYIAUXPUEHUJUKZUOZVURUIUEVHUDUOZUYIVVCWDVVDUIWCUOZUEU
        IUGUHWOWQUEUIWRWSWTZVVDUYCVVBUXPUIUEHXAZXBXCZAVVCURZUEUXRUEVGUOZVVIXFVP
        VVIUXRVVIBCDEGUXPIJKLMNOPQACKUOZVVCRWBVVCUXPWCUOZAUXPUEHXDXGXEZXHVRXIXJ
        XKXLVSXMXNAUYIVULURZUXPUIHUIXOUKZUJUKUOZVUJAUYIVUKVVPXSZWDVVNVVPWDAUYIV
        VQAUYIVVPVUKXSZVVQAUXPUIVVOUIVBUKZUJUKZUOZVVPUXPVVSUFZXSZUYIVVRAVVOVUEU
        OZVWAVWCWHAVVOWIUOZVWDAVWEHUIUFZVWEXSZAVVAVWGSHXPVTAVWEVWFVCZVCZVWEXSZV
        WGAVWHVWEVWJWHAVWFVUOUEUGUHZAVWFURZUYBEHXTZUMZVWKVWLUYBEUYCUMZVWNAVWOVW
        FTWBVWLUYBEUYCVWMVWLHHUJUKZUYCVWMVWFVWPUYCUFAHUIHUJXQXGAVWPVWMUFZVWFAHW
        CUOVWQAHSXRZHYAVTWBYBYCVSAVWNVWKWHZVWFAVVAVWSSUYBVWKEHWIUXTHUFUYAVUOUEU
        GUXTHUXQUPUQUUCVTWBVSVWLVUPVWKVCZAVUPVWFUAWBAVUPVWTWHVWFAUEVUOVVJAXFVPA
        VUOABCDEGHIJKLMNOPQRVWRXEXHVRWBVSUUDVWHVWEUUEVTVWFVWIVWEVWFUUFUUGUUAYDZ
        VVOWJWKUXPUIVVOUUHVTAVVTUYCUXPAVVSHUIUJAHUIAHSUUIUIUUBUOZAYEVPUUJZUUKYF
        AVWBVUKVVPAVVSHUXPVXCYGUUMUULVVPVUKUUNUUOUUPUYIVUKVVPUUQYHAVVPVUJAVVPUR
        UYRUIUIVBUKZVVSUJUKZUOZVUJAVVPVXFAVVPVVPVXFAVVEVVOWCUOZURVVLVVEURVVPVXF
        WHVVPAVXGVVEAVVOVXAXRWOUURVVPVVLVVEUXPUIVVOXDWOUVCUXPUIUIVVOUUSUVDUUTUV
        AAVXFVUJWDVVPAVXFUYRYKHUJUKZUOVUJAVXEVXHUYRAVXDYKVVSHUJVXDYKUFAYIVPVXCU
        VBYFVXHUYCUYRYKVUEUOZVXHUYCYJVXIUIYKUGUHZUIVXDYKUGUIUIVOUVEUVFYIUVGVVEY
        KWCUOVXIVXJWHWOUVHUIYKUVIYLUVJYKUIHXAXCVMUVNWBYMXMUVKUVLZXKZVEZUYGVUJUR
        UYTVUBUYGVUJUYTVUBVUJUYTURUYGUYRUYDUOVUBUYBUYTEUYRUYCUXTUYRUFUYAUYSUEUG
        UXTUYRUXQUPUQUSUYFVUBUBUYRUYDUYEUYRUXPUGYNUVMUVOZUWCUVPYOYMUYMUYSUYOUFZ
        VUAUYQWHUYMUYRCUOZVXOUYMVXPVUBUYMVXPVCZURUYGVUJUYTVUBAUYKUYGVXQYPUYMVUJ
        VXQVXMWBAUYKVXQUYTUYGAUYKURZVXQURZUYSUEVXSAUYRVVBUOZUYSVGUOAUYKVXQUVQZV
        VDVXSVUJVXTVVFVXRVUJVXQVXLWBVVDUYCVVBUYRVVGXBUVRAVXTURZUYSVYBBCDEGUYRIJ
        KLMNOPQAVVKVXTRWBVXTUYRWCUOAUYRUEHXDXGXEXHYOVVJVXSXFVPVXSUYJUYSUEVFUHZA
        UYIUYJVXQYPVXSAVVCUYSUXRUIXOUKZUFZUYJVYCWHVYAVXSUYIVVCVXRUYIVXQVUDWBZVV
        HVTVXSUYSUYRUIXOUKZUXQUDZUIXOUKZUFZVYEVXRAVUJURZVXQVYJAUYKVUJVXKUVSZVYK
        VXQVYJVYKVXQVYJWDZVXPUYSVYHUIVBUKZUFZWDZVYKBCDEGUYRIJKLMNOPQAVVKVUJRWBV
        UJUYRWIUOAUYRHUVTXGUWAZUWBXKYQVXSUYIVYJVYEWHVYFUYIVYIVYDUYSUYIVYHUXRUIX
        OUYIVYGUXPUXQUYIUXPUIUYIUXPUXPUIHXDUWDVXBUYIYEVPUWEWFZYRYGVTVSVVIVYEURU
        YJVYDUEVFUHZVYCVVIUYJVYSWHZVYEVVIUXRWCUOZUEWCUOZVYTVVMWRUXRUEUWFUWGWBVY
        EVYCVYSWHVVIUYSVYDUEVFYNXGUWHUWIVSUWMYSVXNUWJUYMVUCVXQVUIWBUWKAUYKVXPVX
        OUYGVXRVXPURZVYOVXOVXRVYKVXPVYOVYLVYKVXPVYOVYKVYMVYPVYQUWLXKYQWUCUYIVYO
        VXOWHVXRUYIVXPVUDWBUYIVYNUYOUYSUYIVYHUXRUIVBVYRYRYGVTVSYSUWNVXOUYTUYPUY
        SUYOUEUGYNUWOVTVSUYMWUAUYNUYQWHAUYKWUAUYGAUYKVVCWUAVXRUYIVVCVUDVVHVTVVM
        UWPVEZWUAUYNUEUYOVFUHZUYQWUBWUAUYNWUEWHWRUEUXRUWQUWRWUAUEUYOVVJWUAXFVPW
        UAUXRUIUXRUWSVUHWUAVOVPVQVRUXDVTYDUYMUXRUEUYMUXRWUDXHVVJUYMXFVPUWTUXAUX
        BAUYDVGYJZUYDYTUOZUYDUXCUXEZUYGFUYDUMWUFAUYDUYCVGUYBEUYCUXFZVUFVKVPWUGA
        UYCYTUOUYDUYCYJWUGUIHUXGWUIUYCUYDUXHYLVPAVWOWUHTUYBEUYCUXIYHFUBUYDUXJUX
        KUXLUXSUXSFUYDUYCUYHUYIUXSUYBEUXPUYCUXMUXNUXOVT $.
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
        sstri zssre sseli ltp1d 1re a1i readdcld ltnled mpbid syl simprr adantr
        wi simpr fveq2d breq1d wb cn elnnuz sylib eluzfz2 eleq1 syl5ibrcom 0le1
        anc2li 1z eluz1i mpbir2an fzss1 sseld elfzelz adantl ballotlemfelz zred
        0z ax-mp 0re sylan2 syl6 imp bitr3d ex con2d wo nn1m1nn oveq1 nnzd fzsn
        eqtr3d rexeqdv rexsng mpbird ax-1cn eleq2d eqeq2d sylibr c2 1p1e2 mp2an
        csn wss mpd syl2anc simplrr sylan oveq1d breq2 adantlrr cfn pm2.65da cc
        biortn notnot orbi1i syl6bbr elfzp1 npcand oveq2d orbi2d 3bitr3d syl6bb
        nncnd orcom biimpd pm5.6 jctil jctir fzaddel syl2an 3anidm23 nn0addge1i
        biimp3a oveq12d 1nn0 breqtri 2z eluz mpbir syl6bi sylan2d breq1 rspccva
        syld sylan2br expr con3d simpll mpsyl elfznn ballotlemfp1 simprd pncand
        imdistani zcnd zleltp1 sylancr bitr4d syl21anc ltled mtand simpld mpdan
        syl12anc notbid syldan zlem1lt mpan2 zre resubcld bitrd simprlr letri3d
        mpbir2and sylan2b c0 wne ssrab2 fzfi ssfi rabn0 fimaxre reximddv elrabi
        syl3anc anim1i reximi2 ) AFUCZCGUDZUDZUEUFZFUEEUCZUXSUDZUGUHZEUIHUJUKZU
        LZUMUYAFUYEUMAUBUCZUXRUGUHZUBUYFUNZUYAFUYFUXRUYFUOZUYIURAUXRUYEUOZUEUXT
        UGUHZURZUYIURZUYAUYJUYMUYIUYDUYLEUXRUYEUYBUXRUFUYCUXTUEUGUYBUXRUXSUPUQU
        SUTAUYNURZUYAUXTUEUGUHZUYLUYOUYPUEUXTUIVAUKZUGUHZVBZUYOUEUXRUIVCUKZUXSU
        DZUGUHZVBZUYSUYOUYTUXRUGUHZVBZVUCUYOUYKVUEAUYMUYKUYIAUYKUYLVDZVEUYKUXRU
        YTVFUHVUEUYKUXRUYEVGUXRUYEVHVGUYEUIVIUDZVHUIHVJUIVKVLVMVLZVNZVOUYKUXRUY
        TVUIUYKUXRUIVUIUIVGUOZUYKVPVQVRVSVTWAZUYOUYIUYTUYEUOZVUEVUCWDAUYMUYIWBA
        UYMVULUYIAUYMVULAUYLUXRHUFZVBZUYKVULAVUMUYLAVUMUYLVBZAVUMURZHUXSUDZUEVF
        UHZVUOAVURVUMUAWCVUPUXTUEVFUHZVURVUOVUPUXTVUQUEVFVUPUXRHUXSAVUMWEWFWGAV
        UMVUSVUOWHZAVUMAUYKURVUTAVUMUYKAUYKVUMHUYEUOZAHVUGUOZVVAAHWIUOZVVBSHWJW
        KUIHWLWAUXRHUYEWMWNWPUYKAUXRUEHUJUKZUOZVUTUIUEVIUDUOZUYKVVEWDVVFUIVHUOZ
        UEUIUGUHWQWOUEUIXFWRWSZVVFUYEVVDUXRUIUEHWTZXAXGZAVVEURZUXTUEVVKUXTVVKBC
        DEGUXRIJKLMNOPQACKUOZVVERWCVVEUXRVHUOZAUXRUEHXBXCXDZXEUEVGUOZVVKXHVQVSX
        IXJXKXLVTXMXNAUYKVUNURZUXRUIHUIVAUKZUJUKUOZVULAUYKVUMVVRXOZWDVVPVVRWDAU
        YKVVSAUYKVVRVUMXOZVVSAUXRUIVVQUIVCUKZUJUKZUOZVVRUXRVWAUFZXOZUYKVVTAVVQV
        UGUOZVWCVWEWHAVVQWIUOZVWFAVWGHUIUFZVWGXOZAVVCVWISHXPWAAVWGVWHVBZVBZVWGX
        OZVWIAVWJVWGVWLWHAVWHUEVUQUGUHZAVWHURZUYDEHYKZUMZVWMVWNUYDEUYEUMZVWPAVW
        QVWHTWCVWNUYDEUYEVWOVWNHHUJUKZUYEVWOVWHVWRUYEUFAHUIHUJXQXCAVWRVWOUFZVWH
        AHVHUOVWSAHSXRZHXSWAWCXTYAVTAVWPVWMWHZVWHAVVCVXASUYDVWMEHWIUYBHUFUYCVUQ
        UEUGUYBHUXSUPUQYBWAWCVTVWNVURVWMVBZAVURVWHUAWCAVURVXBWHVWHAVUQUEAVUQABC
        DEGHIJKLMNOPQRVWTXDXEVVOAXHVQVSWCVTUUAVWJVWGUUCWAVWHVWKVWGVWHUUDUUEUUFY
        CZVVQWJWKUXRUIVVQUUGWAAVWBUYEUXRAVWAHUIUJAHUIAHSUUMUIUUBUOZAYDVQUUHZUUI
        YEAVWDVUMVVRAVWAHUXRVXEYFUUJUUKVVRVUMUUNUULUUOUYKVUMVVRUUPYGAVVRVULAVVR
        URUYTUIUIVCUKZVWAUJUKZUOZVULAVVRVXHAVVRVVRVXHAVVGVVQVHUOZURVVMVVGURVVRV
        XHWHVVRAVXIVVGAVVQVXCXRWQUUQVVRVVMVVGUXRUIVVQXBWQUURUXRUIUIVVQUUSUUTUVC
        UVAAVXHVULWDVVRAVXHUYTYHHUJUKZUOVULAVXGVXJUYTAVXFYHVWAHUJVXFYHUFAYIVQVX
        EUVDYEVXJUYEUYTYHVUGUOZVXJUYEYLVXKUIYHUGUHZUIVXFYHUGUIUIVPUVEUVBYIUVFVV
        GYHVHUOVXKVXLWHWQUVGUIYHUVHYJUVIYHUIHWTXGVNUVJWCYMXMUVNUVKZXKZVEZUYIVUL
        URVUBVUDUYIVULVUBVUDVULVUBURUYIUYTUYFUOVUDUYDVUBEUYTUYEUYBUYTUFUYCVUAUE
        UGUYBUYTUXSUPUQUSUYHVUDUBUYTUYFUYGUYTUXRUGUVLUVMUVOZUVPUVQYNYMUYOVUAUYQ
        UFZVUCUYSWHUYOUYTCUOZVBZVXQUYOVXRVUDVUKUYOVXRURUYIVULVUBVUDAUYMUYIVXRYO
        UYOVULVXRVXOWCAUYMVXRVUBUYIAUYMURZVXRURZUEVUAVVOVYAXHVQVYAAUYTVVDUOZVUA
        VGUOAUYMVXRUVRZVVFVYAVULVYBVVHVXTVULVXRVXNWCVVFUYEVVDUYTVVIXAUVSAVYBURZ
        VUAVYDBCDEGUYTIJKLMNOPQAVVLVYBRWCVYBUYTVHUOAUYTUEHXBXCXDXEYNVYAUYLUEVUA
        VFUHZAUYKUYLVXRYOVYAAVVEVUAUXTUIVCUKZUFZUYLVYEWHVYCVYAUYKVVEVXTUYKVXRVU
        FWCZVVJWAVYAVUAUYTUIVAUKZUXSUDZUIVCUKZUFZVYGVXTAVULURZVXRVYLAUYMVULVXMU
        WDZVYMVXRVYLVYMVXSVUAVYJUIVAUKZUFZWDZVXRVYLWDZVYMBCDEGUYTIJKLMNOPQAVVLV
        ULRWCVULUYTWIUOAUYTHUVTXCUWAZUWBXKYPVYAUYKVYLVYGWHVYHUYKVYKVYFVUAUYKVYJ
        UXTUIVCUYKVYIUXRUXSUYKUXRUIUYKUXRUXRUIHXBUWEVXDUYKYDVQUWCWFZYQYFWAVTVVK
        VYGURUYLUEVYFVFUHZVYEVVKUYLWUAWHZVYGVVKUEVHUOZUXTVHUOZWUBXFVVNUEUXTUWFU
        WGWCVYGVYEWUAWHVVKVUAVYFUEVFYRXCUWHUWIVTUWJYSVXPUWNUWKAUYMVXSVXQUYIVXTV
        XSURZVYPVXQVXTVYMVXSVYPVYNVYMVXSVYPVYMVYQVYRVYSUWLXKYPWUEUYKVYPVXQWHVXT
        UYKVXSVUFWCUYKVYOUYQVUAUYKVYJUXTUIVAVYTYQYFWAVTYSUWMVXQVUBUYRVUAUYQUEUG
        YRUWOWAVTUYOWUDUYPUYSWHAUYMWUDUYIAUYMVVEWUDVXTUYKVVEVUFVVJWAVVNUWPVEZWU
        DUYPUYQUEVFUHZUYSWUDWUCUYPWUGWHXFUXTUEUWQUWRWUDUYQUEWUDUXTUIUXTUWSVUJWU
        DVPVQUWTVVOWUDXHVQVSUXAWAYCAUYKUYLUYIUXBUYOUXTUEUYOUXTWUFXEVVOUYOXHVQUX
        CUXDUXEAUYFVGYLZUYFYTUOZUYFUXFUXGZUYIFUYFUMWUHAUYFUYEVGUYDEUYEUXHZVUHVL
        VQWUIAUYEYTUOUYFUYEYLWUIUIHUXIWUKUYEUYFUXJYJVQAVWQWUJTUYDEUYEUXKYGFUBUY
        FUXLUXOUXMUYAUYAFUYFUYEUYJUYKUYAUYDEUXRUYEUXNUXPUXQWA $.
    $}

    ${
      $d b c M $.  $d b C $.
      $( ` ( F `` C ) ` finishes counting at ` ( M - N ) ` .  (Contributed by
         Thierry Arnoux, 25-Nov-2016.) $)
      ballotlemfmpn $p |- ( C e. O ->
                                     ( ( F ` C ) ` ( M + N ) ) = ( M - N ) ) $=
        ( wcel co cfv chash cmin wceq vb caddc c1 cfz cin cdif id cz cn nnaddcl
        mp2an nnzi a1i ballotlemfval wss cpw cv crab ssrab2 eqsstri sseli dfss1
        elpwid sylib fveq2d cab rabssab eleq2s fveq2 eqeq1d cbvabv elab2g mpbid
        eqtrd cfn fzfi hashssdif sylancr cn0 nnnn0i hashfz1 mp1i oveq12d pncan2
        cc nncni 3eqtrd ) BHOZFGUBPZBEQQUCWIUDPZBUEZRQZWJBUFRQZSPFGSPWHABCDEWIF
        GHIJKLMNWHUGWIUHOWHWIFUIOGUIOWIUIOJKFGUJUKZULUMUNWHWLFWMGSWHWLBRQZFWHWK
        BRWHBWJUOZWKBTWHBWJHWJUPZBHIUQZRQZFTZIWQURZWQLWTIWQUSUTVAVCZBWJVBVDVEWH
        BWTIVFZOZWOFTZXDBXAHXAXCBWTIWQVGVALVHUAUQZRQZFTZXEUABXCHXFBTXGWOFXFBRVI
        VJWTXHIUAWRXFTWSXGFWRXFRVIVJVKVLVMZVNWHWMWJRQZWOSPZWIFSPZGWHWJVOOWPWMXK
        TUCWIVPXBWJBVQVRWHXJWIWOFSWIVSOXJWITWHWIWNVTWIWAWBXIWCXLGTZWHFWEOGWEOXM
        FJWFGKWFFGWDUKUMWGWCVN $.
    $}

    $( ` ( F `` C ) ` always starts counting at 0 .  (Contributed by Thierry
       Arnoux, 25-Nov-2016.) $)
    ballotlemfval0 $p |- ( C e. O -> ( ( F ` C ) ` 0 ) = 0 ) $=
      ( cc0 cfv co chash c0 eqtri wcel c1 cfz cin cdif cmin id cz ballotlemfval
      0z a1i fz10 ineq1i incom 3eqtr2i fveq2i hash0 difeq1i 0dif oveq12i subidi
      in0 0cn syl6eq ) BHUAZOBEPPUBOUCQZBUDZRPZVFBUEZRPZUFQZOVEABCDEOFGHIJKLMNV
      EUGOUHUAVEUJUKUIVKOOUFQOVHOVJOUFVHSRPZOVGSRVGSBUDBSUDSVFSBULUMBSUNBVBUOUP
      UQTVJVLOVISRVISBUESVFSBULURBUSTUPUQTUTOVCVATVD $.

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
        ( vj wcel wa cc0 cdif wn cv cfv cle wbr c1 caddc co cfz wrex eldif wral
        clt wo wi df-or pm3.24 a1bi bitr4i ballotleme notbii anbi2i andi 3bitri
        ianor cr wss 0p1e1 oveq1i cz 0z fzp1ss ax-mp eqsstr3i a1i imdistani wsb
        sseld simpl elfzelz adantl ballotlemfelz zred sbimi nfv clelsb3 anbi12i
        sban sbf bitri weq fveq2 eleq1d sbie 3imtr3i syl lenltd rexbidva rexnal
        0re syl6bb pm5.32i 3bitr4i ) BIEUARBIRZBERZUBZSZXEDUCZBFUDZUDZTUEUFZDUG
        GHUHUIZUJUIZUKZSZBIEULXEXEUBZSZXETXKUNUFZDXNUMZUBZSZUOZYBXHXPYCXRUBZYBU
        PYBXRYBUQYDYBXEURUSUTXHXEXEXTSZUBZSXEXQYAUOZSYCXGYFXEXFYEABCDEFGHIJKLMN
        OPVAVBVCYFYGXEXEXTVFVCXEXQYAVDVEXEXOYAXEXOXSUBZDXNUKYAXEXLYHDXNXEXIXNRZ
        SZXKTYJXEXITXMUJUIZRZSZXKVGRZXEYIYLXEXNYKXIXNYKVHXEXNTUGUHUIZXMUJUIZYKY
        OUGXMUJVIVJTVKRYPYKVHVLTXMVMVNVOVPVSVQXEQUCZYKRZSZQDVRZYQXJUDZVGRZQDVRY
        MYNYSUUBQDYSUUAYSABCDFYQGHIJKLMNOXEYRVTYRYQVKRXEYQTXMWAWBWCWDWEYTXEQDVR
        ZYRQDVRZSYMXEYRQDWIUUCXEUUDYLXEQDXEQWFWJDQYKWGWHWKUUBYNQDYNQWFQDWLUUAXK
        VGYQXIXJWMWNWOWPWQTVGRYJXAVPWRWSXSDXNWTXBXCXDWK $.
    $}

    $( If the first pick is a vote for B, A is not ahead throughout the count
       (Contributed by Thierry Arnoux, 25-Nov-2016.) $)
    ballotlem4 $p |- ( C e. O -> ( -. 1 e. C -> -. C e. E ) ) $=
      ( wcel c1 cc0 clt wn wa cv cfv wbr caddc co cfz wral cuz cn nnaddcl mp2an
      wrex elnnuz mpbi eluzfz1 ax-mp cmin cle 0le1 0re 1re lenlti cr wb ltsub13
      mp3an subidi breq2i bitri mtbir 1m1e0 fveq2i ballotlemfval0 syl5eq oveq1d
      0cn breq2d mtbiri adantr wceq simpl 1nn a1i ballotlemfp1 simpld mpan2 imp
      wi mtbird fveq2 notbid rspcev sylancr rexnal sylib ballotleme simprbi ex
      nsyl ) BIQZRBQZUAZBEQZUAXBXDUBZSDUCZBFUDZUDZTUEZDRGHUFUGZUHUGZUIZXEXFXJUA
      ZDXLUNZXMUAXFRXLQZSRXHUDZTUEZUAZXOXKRUJUDQZXPXKUKQZXTGUKQHUKQYAKLGHULUMXK
      UOUPRXKUQURZXFXRSRRUSUGZXHUDZRUSUGZTUEZXBYFUAXDXBYFSSRUSUGZTUEZYHRSTUEZSR
      UTUEYIUAVASRVBVCVDUPYHRSSUSUGZTUEZYISVEQZYLRVEQYHYKVFVBVBVCSSRVGVHYJSRTSV
      RVIVJVKVLXBYEYGSTXBYDSRUSXBYDSXHUDSYCSXHVMVNABCDFGHIJKLMNOVOVPVQVSVTWAXFX
      QYESTXBXDXQYEWBZXBXPXDYMWJZYBXBXPUBZYNXCXQYDRUFUGWBWJYOABCDFRGHIJKLMNOXBX
      PWCRUKQYOWDWEWFWGWHWIVSWKXNXSDRXLXGRWBZXJXRYPXIXQSTXGRXHWLVSWMWNWOXJDXLWP
      WQXEXBXMABCDEFGHIJKLMNOPWRWSXAWT $.

    $( From now on, we assume that A wins the poll $)
    ballotth.mgtn $e |- N < M $.

    $d i k E $.  $d k C $.
    $( If A is not ahead throughout, there is a ` k ` where votes are tied.
       (Contributed by Thierry Arnoux, 1-Dec-2016.) $)
    ballotlem5 $p |- ( C e. ( O \ E ) ->
      E. k e. ( 1 ... ( M + N ) ) ( ( F ` C ) ` k ) = 0 ) $=
      ( wcel co cdif caddc eldifi cn a1i nnaddcld cv cfv cc0 cle ballotlemodife
      wbr cfz wrex simprbi cmin nnrei posdifi mpbi wceq ballotlemfmpn syl5breqr
      c1 clt syl ballotlemfc0 ) BJFUASZABCDEGHIUBTZHIJKLMNOPBJFUCZVGHIHUDSVGLUE
      IUDSVGMUEUFVGBJSZDUGBGUHZUHUIUJULDVCVHUMTUNABCDFGHIJKLMNOPQUKUOVGUIHIUPTZ
      VHVKUHZVDIHVDULUIVLVDULRIHIMUQHLUQURUSVGVJVMVLUTVIABCDGHIJKLMNOPVAVEVBVF
      $.

    $( Let I be the first time a tie is reached in a given count. $)
    ballotth.i $e |- I = ( c e. ( O \ E ) |-> sup ( { k e. ( 1 ... ( M + N ) )
      | ( ( F ` c ) ` k ) = 0 } , RR , `' < ) ) $.

    $d I k $.  $d c d k $.  $d c i k E $.
    ${
      $d d C $.  $d d E $.  $d d F $.  $d d M $.  $d d N $.  $d d O $.
      $( Value of ` I ` for a given counting ` C ` .  (Contributed by Thierry
         Arnoux, 1-Dec-2016.) $)
      ballotlemi $p |- ( C e. ( O \ E ) -> ( I ` C ) = sup (
       { k e. ( 1 ... ( M + N ) ) | ( ( F ` C ) ` k ) = 0 } , RR , `' < ) ) $=
        ( vd cv cfv cc0 wceq c1 caddc co cfz crab cr clt ccnv csup fveq2 fveq1d
        cdif rabbidv supeq1d cmpt cbvmptv eqtri wor ltso cnvso mpbi supex fvmpt
        eqeq1d ) UABEUBZUAUBZGUCZUCZUDUEZEUFIJUGUHUIUHZUJZUKULUMZUNZVJBGUCZUCZU
        DUEZEVOUJZUKVQUNKFUQZHVKBUEZUKVPWBVQWDVNWAEVOWDVMVTUDWDVJVLVSVKBGUOUPVI
        URUSHLWCVJLUBZGUCZUCZUDUEZEVOUJZUKVQUNZUTUAWCVRUTTLUAWCWJVRWEVKUEZUKWIV
        PVQWKWHVNEVOWKWGVMUDWKVJWFVLWEVKGUOUPVIURUSVAVBUKWBVQUKULVCUKVQVCVDUKUL
        VEVFVGVH $.
    $}

    $( Properties of ` ( I `` C ) ` .  (Contributed by Thierry Arnoux,
       12-Dec-2016.) $)
    ballotlemiex $p |- ( C e. ( O \ E ) -> ( ( I ` C ) e. ( 1 ... ( M + N ) )
      /\ ( ( F ` C ) ` ( I ` C ) ) = 0 ) ) $=
      ( cdif wcel cfv cv cc0 wceq c1 caddc co cfz crab clt ccnv csup ballotlemi
      wa cr wor cfn c0 wne wss ltso cnvso mpbi a1i fzfi ssrab2 mp2an ballotlem5
      ssfi wrex rabn0 sylibr cz cuz fzssuz uzssz sstri fisupcl syl13anc eqeltrd
      zssre fveq2 eqeq1d elrab sylib ) BKFUAUBZBHUCZEUDZBGUCZUCZUEUFZEUGIJUHUIZ
      UJUIZUKZUBWIWOUBWIWKUCZUEUFZUPWHWIWPUQULUMZUNZWPABCDEFGHIJKLMNOPQRSTUOWHU
      QWSURZWPUSUBZWPUTVAZWPUQVBZWTWPUBXAWHUQULURXAVCUQULVDVEVFXBWHWOUSUBWPWOVB
      XBUGWNVGWMEWOVHZWOWPVKVIVFWHWMEWOVLXCABCDEFGIJKLMNOPQRSVJWMEWOVMVNXDWHWPW
      OUQXEWOVOUQWOUGVPUCVOUGWNVQUGVRVSWCVSVSVFUQWPWSVTWAWBWMWREWIWOWJWIUFWLWQU
      EWJWIWKWDWEWFWG $.

    $d c E $.  $d i I $.
    ${
      $d c k y z $.  $d y z C $.  $d y z F $.  $d y z M $.  $d y z N $.
      $( The first tie cannot be reached at the first pick.  (Contributed by
         Thierry Arnoux, 12-Mar-2017.) $)
      ballotlemi1 $p |- ( ( C e. ( O \ E ) /\ -. 1 e. C ) ->
                                                           ( I ` C ) =/= 1 ) $=
        ( cdif wcel c1 wn wa cfv wceq cc0 cmin co wne 0re 1re resubcli clt 0lt1
        wbr cr wb ltsub23 mp3an 0cn subidi breq1i bitr2i mpbi gtneii necon3abii
        eqcom wi caddc eldifi cn 1nn a1i ballotlemfp1 simpld imp ballotlemfval0
        1m1e0 fveq2i oveq1i syl adantr oveq1d 3eqtrrd eqeq1d mtbii ballotlemiex
        cfz simprd ad2antrr fveq2 adantl mpbid mtand neneqad ) BKFUAUBZUCBUBZUD
        ZUEZBHUFZUCXAXBUCUGZUCBGUFZUFZUHUGZXAUHUCUIUJZUHUGZXFUHXGUKXHUDXGUHUHUC
        ULUMUNUHUCUOUQZXGUHUOUQZUPXJUHUHUIUJZUCUOUQZXIUHURUBZUCURUBXMXJXLUSULUM
        ULUHUCUHUTVAXKUHUCUOUHVBVCVDVEVFVGXHUHXGUHXGVIVHVFXAXGXEUHXAXEUCUCUIUJZ
        XDUFZUCUIUJZUHXDUFZUCUIUJZXGWRWTXEXPUGZWRWTXSVJWSXEXOUCVKUJUGVJWRABCDGU
        CIJKLMNOPQBKFVLZUCVMUBWRVNVOVPVQVRXPXRUGXAXOXQUCUIXNUHXDVTWAWBVOXAXQUHU
        CUIWRXQUHUGZWTWRBKUBYAXTABCDGIJKLMNOPQVSWCWDWEWFWGWHXAXCUEXBXDUFZUHUGZX
        FWRYCWTXCWRXBUCIJVKUJWJUJUBYCABCDEFGHIJKLMNOPQRSTWIWKWLXCYCXFUSXAXCYBXE
        UHXBUCXDWMWGWNWOWPWQ $.

      $( The first tie cannot be reached at the first pick.  (Contributed by
         Thierry Arnoux, 4-Apr-2017.) $)
      ballotlemii $p |- ( ( C e. ( O \ E ) /\ 1 e. C ) -> ( I ` C ) =/= 1 ) $=
        ( cdif wcel c1 wa cfv wceq cc0 caddc co wn 1e0p1 ax-1ne0 eqnetrri df-ne
        wne mpbi cmin wi eldifi cn 1nn a1i ballotlemfp1 simprd imp 1m1e0 fveq2i
        oveq1i ballotlemfval0 syl adantr oveq1d 3eqtrrd eqeq1d cfz ballotlemiex
        mtbii ad2antrr wb fveq2 adantl mpbid mtand neneqad ) BKFUAUBZUCBUBZUDZB
        HUEZUCWGWHUCUFZUCBGUEZUEZUGUFZWGUGUCUHUIZUGUFZWLWMUGUOWNUJUCWMUGUKULUMW
        MUGUNUPWGWMWKUGWGWKUCUCUQUIZWJUEZUCUHUIZUGWJUEZUCUHUIZWMWEWFWKWQUFZWEWF
        UJWKWPUCUQUIUFURWFWTURWEABCDGUCIJKLMNOPQBKFUSZUCUTUBWEVAVBVCVDVEWQWSUFW
        GWPWRUCUHWOUGWJVFVGVHVBWGWRUGUCUHWEWRUGUFZWFWEBKUBXBXAABCDGIJKLMNOPQVIV
        JVKVLVMVNVQWGWIUDWHWJUEZUGUFZWLWEXDWFWIWEWHUCIJUHUIVOUIUBXDABCDEFGHIJKL
        MNOPQRSTVPVDVRWIXDWLVSWGWIXCWKUGWHUCWJVTVNWAWBWCWD $.

      $d k w y z $.  $d w C $.  $d w F $.  $d w M $.  $d w N $.
      $( The set of zeroes of ` F ` satisfies the conditions to have a supremum
         (Contributed by Thierry Arnoux, 1-Dec-2016.) $)
      ballotlemsup $p |- ( C e. ( O \ E ) -> E. z e. RR ( A. w e.
        { k e. ( 1 ... ( M + N ) ) | ( ( F ` C ) ` k ) = 0 } -. z `' < w
        /\ A. w e. RR ( w `' < z -> E. y e.
        { k e. ( 1 ... ( M + N ) ) | ( ( F ` C ) ` k ) = 0 } w `' < y )
        ) ) $=
        ( cdif wcel cr clt ccnv wor cv cfv cc0 wceq c1 caddc co cfz crab cfn c0
        wne wss w3a wa wbr wn wral wrex fzfi ssrab2 ssfi mp2an ballotlem5 rabn0
        wi a1i sylibr cn fzssuz nnuz sseqtr4i nnssre sstri 3jca ltso cnvso mpbi
        cuz jctil fisup2g sseli anim1i reximi2 3syl ) ENIUDUEZUFUGUHZUIZHUJEJUK
        UKULUMZHUNLMUOUPZUQUPZURZUSUEZXAUTVAZXAUFVBZVCZVDCUJZDUJZWPVEVFDXAVGXGX
        FWPVEXGBUJWPVEBXAVHVODUFVGVDZCXAVHXHCUFVHWOXEWQWOXBXCXDXBWOWTUSUEXAWTVB
        XBUNWSVIWRHWTVJZWTXAVKVLVPWOWRHWTVHXCAEFGHIJLMNOPQRSTUAUBVMWRHWTVNVQXDW
        OXAWTUFXIWTVRUFWTUNWHUKVRUNWSVSVTWAWBWCWCZVPWDUFUGUIWQWEUFUGWFWGWICDBUF
        XAWPWJXHXHCXAUFXFXAUEXFUFUEXHXAUFXFXJWKWLWMWN $.

      $( ` ( I `` C ) ` is the first tie.  (Contributed by Thierry Arnoux,
         1-Dec-2016.) $)
      ballotlemimin $p |- ( C e. ( O \ E ) ->
        -. E. k e. ( 1 ... ( ( I ` C ) - 1 ) ) ( ( F ` C ) ` k ) = 0 ) $=
        ( vz vw vy cdif wcel cv cfv cc0 wceq c1 cmin co cfz clt wbr cle elfzle2
        wa adantl cz wb elfzelz caddc cn ballotlemiex simpld elfznn syl zltlem1
        nnzd syl2anr mpbird adantr wn ccnv cuz wss 1z a1i zsubcld nnaddcl mp2an
        zred nnred zlem1lt syl2anc mpbid ltled eluz fzss2 sseld crab rabid csup
        cr wral wrex wi ballotlemsup ltso cnvso mpbi id supub ballotlemi breq1d
        wor notbid sylibrd syl5bir syland ltrel relbrcnv sylnib pm2.65da nrexdv
        imp anassrs ) BKFUDUEZEUFZBGUGZUGUHUIZEUJBHUGZUJUKULZUMULZXSXTYEUEZURZY
        BXTYCUNUOZYGYHYBYGYHXTYDUPUOZYFYIXSXTUJYDUQUSYFXTUTUEYCUTUEZYHYIVAXSXTU
        JYDVBXSYCXSYCUJIJVCULZUMULZUEZYCVDUEXSYMYCYAUGUHUIABCDEFGHIJKLMNOPQRSTV
        EVFZYCYKVGVHVJZXTYCVIVKVLVMXSYFYBYHVNXSYFYBURZURYCXTUNVOZUOZYHXSYPYRVNZ
        XSYFXTYLUEZYBYSXSYEYLXTXSYKYDVPUGUEZYEYLVQXSUUAYDYKUPUOZXSYDYKXSYDXSYCU
        JYOUJUTUEXSVRVSVTZWCXSYKYKVDUEZXSIVDUEJVDUEUUDMNIJWAWBVSZWDXSYCYKUPUOZY
        DYKUNUOZXSYMUUFYNYCUJYKUQVHXSYJYKUTUEZUUFUUGVAYOXSYKUUEVJZYCYKWEWFWGWHX
        SYDUTUEUUHUUAUUBVAUUCUUIYDYKWIWFVLYDUJYKWJVHWKYTYBURXTYBEYLWLZUEZXSYSYB
        EYLWMXSUUKUUJWOYQWNZXTYQUOZVNZYSXSUAUFZUBUFZYQUOVNUBUUJWPUUPUUOYQUOUUPU
        CUFYQUOUCUUJWQWRUBWOWPURUAWOWQZUUKUUNWRAUCUAUBBCDEFGHIJKLMNOPQRSTWSUUQU
        AUBUCWOUUJXTYQWOYQXGZUUQWOUNXGUURWTWOUNXAXBVSUUQXCXDVHXSYRUUMXSYCUULXTY
        QABCDEFGHIJKLMNOPQRSTXEXFXHXIXJXKXQYCXTUNXLXMXNXRXOXP $.

      $( If the first vote is for B, the vote on the first tie is for A.
         (Contributed by Thierry Arnoux, 1-Dec-2016.) $)
      ballotlemic $p |- ( ( C e. ( O \ E ) /\ -. 1 e. C ) ->
                                                            ( I ` C ) e. C ) $=
        ( cdif wcel c1 wn wa cfv cv cc0 wceq cmin co wrex eldifi ad2antrr cn c2
        cfz cuz wne caddc ballotlemiex simpld elfznn adantr ballotlemi1 eluz2b3
        syl sylanbrc uz2m1nn cle wbr elnnuz biimpi eluzfz1 3syl wi ballotlemfp1
        1nn a1i imp 1m1e0 fveq2i oveq1i ballotlemfval0 oveq1d 3eqtrrd cr wb 0re
        1re suble0 mp2an mpbir syl6eqbrr fveq2 breq1d rspcev syl2anc clt ax-1cn
        0le1 0lt1 addid1i simprd eqtr3d cz nnzd 1z zsubcld ballotlemfelz cc 0cn
        zcnd subaddd syl5eqr syl5breq adantlr ballotlemfc0 ballotlemimin condan
        mpbid ) BKFUAUBZUCBUBZUDZUEZBHUFZBUBZEUGBGUFZUFUHUIEUCYFUCUJUKZUQUKZULZ
        YEYGUDZUEZABCDEGYIIJKLMNOPQYBBKUBZYDYLBKFUMZUNYEYIUOUBZYLYEYFUPURUFUBZY
        PYEYFUOUBZYFUCUSYQYBYRYDYBYFUCIJUTUKZUQUKUBZYRYBYTYFYHUFZUHUIZABCDEFGHI
        JKLMNOPQRSTVAZVBYFYSVCVGZVDABCDEFGHIJKLMNOPQRSTVEYFVFVHYFVIVGZVDYMUCYJU
        BZUCYHUFZUHVJVKZDUGZYHUFZUHVJVKZDYJULYEUUFYLYEYPYIUCURUFUBZUUFUUEYPUULY
        IVLVMUCYIVNVOVDYEUUHYLYEUUGUHUCUJUKZUHVJYEUUGUCUCUJUKZYHUFZUCUJUKZUHYHU
        FZUCUJUKZUUMYBYDUUGUUPUIZYBYDUUSVPYCUUGUUOUCUTUKUIVPYBABCDGUCIJKLMNOPQY
        OUCUOUBYBVRVSVQVBVTUUPUURUIYEUUOUUQUCUJUUNUHYHWAWBWCVSYEUUQUHUCUJYBUUQU
        HUIZYDYBYNUUTYOABCDGIJKLMNOPQWDVGVDWEWFUUMUHVJVKZUHUCVJVKZXAUHWGUBUCWGU
        BUVAUVBWHWIWJUHUCWKWLWMWNVDUUKUUHDUCYJUUIUCUIUUJUUGUHVJUUIUCYHWOWPWQWRY
        BYLUHYIYHUFZWSVKYDYBYLUEZUHUCUVCWSXBUVDUCUCUHUTUKZUVCUCWTXCUVDUVCUCUJUK
        ZUHUIUVEUVCUIUVDUUAUVFUHYBYLUUAUVFUIZYBYLUVGVPYGUUAUVCUCUTUKUIVPYBABCDG
        YFIJKLMNOPQYOUUDVQVBVTYBUUBYLYBYTUUBUUCXDVDXEUVDUVCUCUHUVDUVCUVDABCDGYI
        IJKLMNOPQYBYNYLYOVDUVDYFUCYBYFXFUBYLYBYFUUDXGVDUCXFUBUVDXHVSXIXJXMUCXKU
        BUVDWTVSUHXKUBUVDXLVSXNYAXOXPXQXRYBYKUDYDYLABCDEFGHIJKLMNOPQRSTXSUNXT
        $.

      $( If the first vote is for A, the vote on the first tie is for B.
         (Contributed by Thierry Arnoux, 4-Apr-2017.) $)
      ballotlem1c $p |- ( ( C e. ( O \ E ) /\ 1 e. C ) ->
                                                         -. ( I ` C ) e. C ) $=
        ( cdif wcel c1 wa cfv cv cc0 wceq cmin co cfz eldifi ad2antrr cn c2 cuz
        wrex wne ballotlemiex simpld elfznn adantr ballotlemii eluz2b3 sylanbrc
        caddc syl uz2m1nn cle wbr elnnuz biimpi eluzfz1 3syl 0le1 1e0p1 breqtri
        wn wi 1nn ballotlemfp1 simprd 1m1e0 fveq2i oveq1i ballotlemfval0 oveq1d
        a1i imp 3eqtrrd syl5breq fveq2 breq2d rspcev syl2anc cneg df-neg eqtr3d
        clt cc 0cn ax-1cn cz nnzd 1z zsubcld ballotlemfelz zcnd subadd2d mpbird
        syl5eq 0lt1 cr wb 1re lt0neg2 ax-mp mpbi syl6eqbrr adantlr ballotlemfcc
        ballotlemimin pm2.65da ) BKFUAUBZUCBUBZUDZBHUEZBUBZEUFBGUEZUEUGUHEUCYGU
        CUIUJZUKUJZUQZYFYHUDZABCDEGYJIJKLMNOPQYDBKUBZYEYHBKFULZUMYFYJUNUBZYHYFY
        GUOUPUEUBZYPYFYGUNUBZYGUCURYQYDYRYEYDYGUCIJVFUJZUKUJUBZYRYDYTYGYIUEZUGU
        HZABCDEFGHIJKLMNOPQRSTUSZUTYGYSVAVGZVBABCDEFGHIJKLMNOPQRSTVCYGVDVEYGVHV
        GZVBYMUCYKUBZUGUCYIUEZVIVJZUGDUFZYIUEZVIVJZDYKUQYFUUFYHYFYPYJUCUPUEUBZU
        UFUUEYPUULYJVKVLUCYJVMVNVBYFUUHYHYFUGUGUCVFUJZUUGVIUGUCUUMVIVOVPVQYFUUG
        UCUCUIUJZYIUEZUCVFUJZUGYIUEZUCVFUJZUUMYDYEUUGUUPUHZYDYEVRUUGUUOUCUIUJUH
        VSYEUUSVSYDABCDGUCIJKLMNOPQYOUCUNUBYDVTWHWAWBWIUUPUURUHYFUUOUUQUCVFUUNU
        GYIWCWDWEWHYFUUQUGUCVFYDUUQUGUHZYEYDYNUUTYOABCDGIJKLMNOPQWFVGVBWGWJWKVB
        UUKUUHDUCYKUUIUCUHUUJUUGUGVIUUIUCYIWLWMWNWOYDYHYJYIUEZUGWSVJYEYDYHUDZUV
        AUCWPZUGWSUVBUVCUGUCUIUJZUVAUCWQUVBUVDUVAUHUVAUCVFUJZUGUHUVBUUAUVEUGYDY
        HUUAUVEUHZYDYHVRUUAUVAUCUIUJUHVSYHUVFVSYDABCDGYGIJKLMNOPQYOUUDWAWBWIYDU
        UBYHYDYTUUBUUCWBVBWRUVBUGUCUVAUGWTUBUVBXAWHUCWTUBUVBXBWHUVBUVAUVBABCDGY
        JIJKLMNOPQYDYNYHYOVBUVBYGUCYDYGXCUBYHYDYGUUDXDVBUCXCUBUVBXEWHXFXGXHXIXJ
        XKUGUCWSVJZUVCUGWSVJZXLUCXMUBUVGUVHXNXOUCXPXQXRXSXTYAYDYLVRYEYHABCDEFGH
        IJKLMNOPQRSTYBUMYC $.
    $}

    $( For a given count ` c ` , ` S ` is the operation reflecting the index
       in a count, before a tie is reached. $)
    ballotth.s $e |- S = ( c e. ( O \ E ) |-> ( i e. ( 1 ... ( M + N ) ) |->
                   if ( i <_ ( I ` c ) , ( ( ( I ` c ) + 1 ) - i ) , i ) ) ) $.

    $d c I $.
    ${
      $d c d i k M $.  $d c d i k N $.  $d d E $.  $d d C $.  $d d I $.
      $d d O $.
      $( Value of ` S ` (Contributed by Thierry Arnoux, 12-Apr-2017.) $)
      ballotlemsval $p |- ( C e. ( O \ E ) ->
        ( S ` C ) = ( i e. ( 1 ... ( M + N ) ) |->
                   if ( i <_ ( I ` C ) , ( ( ( I ` C ) + 1 ) - i ) , i ) ) ) $=
        ( vd c1 caddc co cfz cv cfv cle wbr cmin cif cmpt cdif wceq wcel fveq2d
        simpl breq2d oveq1d eqidd ifbieq12d mpteq2dva cbvmptv eqtri mptex fvmpt
        wa ovex ) UCBEUDJKUEUFZUGUFZEUHZUCUHZIUIZUJUKZVOUDUEUFZVMULUFZVMUMZUNZE
        VLVMBIUIZUJUKZWAUDUEUFZVMULUFZVMUMZUNLGUOZDVNBUPZEVLVSWEWGVMVLUQZVIZVPW
        BVRVMWDVMWIVOWAVMUJWIVNBIWGWHUSURZUTWIVQWCVMULWIVOWAUDUEWJVAVAWIVMVBVCV
        DDMWFEVLVMMUHZIUIZUJUKZWLUDUEUFZVMULUFZVMUMZUNZUNUCWFVTUNUBMUCWFWQVTWKV
        NUPZEVLWPVSWRWHVIZWMVPWOVMVRVMWSWLVOVMUJWSWKVNIWRWHUSURZUTWSWNVQVMULWSW
        LVOUDUEWTVAVAWSVMVBVCVDVEVFEVLWEUDVKUGVJVGVH $.

      $d i j $.  $d j I $.  $d j C $.  $d j E $.  $d j F $.  $d j J $.
      $d j F $.  $d j M $.  $d j N $.  $d j O $.
      $( Value of ` S ` evaluated at ` J ` for a given counting ` C ` .
         (Contributed by Thierry Arnoux, 12-Apr-2017.) $)
      ballotlemsv $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) ) ->
        ( ( S ` C ) ` J ) =
                     if ( J <_ ( I ` C ) , ( ( ( I ` C ) + 1 ) - J ) , J ) ) $=
        ( vj cdif wcel c1 caddc co cfz wa cv cfv cle wbr cmin cif cvv cmpt wceq
        ballotlemsval breq1 oveq2 ifbieq12d cbvmptv syl6eq adantr breq1d oveq2d
        id simpr adantlr ovex a1i wn elex ad2antlr ifclda fvmptd ) BMGUEUFZJUGK
        LUHUIUJUIZUFZUKZUDJUDULZBIUMZUNUOZWEUGUHUIZWDUPUIZWDUQZJWEUNUOZWGJUPUIZ
        JUQZWABDUMZURVTWMUDWAWIUSZUTWBVTWMEWAEULZWEUNUOZWGWOUPUIZWOUQZUSWNABCDE
        FGHIKLMNOPQRSTUAUBUCVAEUDWAWRWIWOWDUTZWPWFWQWOWHWDWOWDWEUNVBWOWDWGUPVCW
        SVJVDVEVFVGVTWDJUTZWIWLUTWBVTWTUKZWFWJWHWDWKJXAWDJWEUNVTWTVKZVHXAWDJWGU
        PXBVIXBVDVLVTWBVKWCWJWKJURWKURUFWCWJUKWGJUPVMVNWBJURUFVTWJVOJWAVPVQVRVS
        $.
    $}

    $( ` S ` maps values less than ` ( I `` C ) ` to values greater than 1.
       (Contributed by Thierry Arnoux, 28-Apr-2017.) $)
    ballotlemsgt1 $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) )
      /\ J < ( I ` C ) ) -> 1 < ( ( S ` C ) ` J ) ) $=
      ( cdif wcel c1 caddc co cfz cfv clt wbr w3a cmin cz elfzelz 3ad2ant2 zred
      cc0 wceq ballotlemiex simpld syl 3ad2ant1 cr 1re a1i readdcld zcnd ax-1cn
      simp3 cc pncand breqtrrd ltsub13d cle cif ballotlemsv 3adant3 ltled eqtrd
      iftrue ) BMGUDUEZJUFKLUGUHZUIUHZUEZJBIUJZUKULZUMZUFWGUFUGUHZJUNUHZJBDUJUJ
      ZUKWIJWJUFWIJWFWCJUOUEWHJUFWDUPUQURZWIWGUFWIWGWCWFWGUOUEZWHWCWGWEUEZWNWCW
      OWGBHUJUJUSUTABCEFGHIKLMNOPQRSTUAUBVAVBWGUFWDUPVCVDZURZUFVEUEWIVFVGZVHWRW
      IJWGWJUFUNUHUKWCWFWHVKZWIWGUFWIWGWPVIUFVLUEWIVJVGVMVNVOWIWLJWGVPULZWKJVQZ
      WKWCWFWLXAUTWHABCDEFGHIJKLMNOPQRSTUAUBUCVRVSWIWTXAWKUTWIJWGWMWQWSVTWTWKJW
      BVCWAVN $.

    $( Domain of ` S ` for a given counting ` C ` .  (Contributed by Thierry
       Arnoux, 12-Apr-2017.) $)
    ballotlemsdom $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) ) ->
      ( ( S ` C ) ` J ) e. ( 1 ... ( M + N ) ) ) $=
      ( cdif wcel c1 caddc co cfz wa cfv cle wbr cmin cif ballotlemsv cz fzssuz
      wss cuz uzssz sstri cc0 wceq ballotlemiex simpld sseldi ad2antrr cn mp2an
      nnaddcl nnzi a1i elfzle2 syl eluz2 fzss2 sylbir syl3anc 1z simplr elfzle1
      w3a simpr elfz4 syl32anc fzrev3i wb cc ax-1cn addcomd oveq1d eleq1d mpbid
      zcnd sseldd wn ifclda eqeltrd ) BMGUDUEZJUFKLUGUHZUIUHZUEZUJZJBDUKUKJBIUK
      ZULUMZXEUFUGUHZJUNUHZJUOXBABCDEFGHIJKLMNOPQRSTUAUBUCUPXDXFXHJXBXDXFUJZUFX
      EUIUHZXBXHXIXEUQUEZXAUQUEZXEXAULUMZXJXBUSZWTXKXCXFWTXBUQXEXBUFUTUKUQUFXAU
      RUFVAVBZWTXEXBUEZXEBHUKUKVCVDABCEFGHIKLMNOPQRSTUAUBVEVFZVGZVHZXLXIXAKVIUE
      LVIUEXAVIUEOPKLVKVJVLVMXIXPXMWTXPXCXFXQVHXEUFXAVNVOXKXLXMWCXAXEUTUKUEXNXE
      XAVPXEUFXAVQVRVSXIUFXEUGUHZJUNUHZXJUEZXHXJUEZXIJXJUEZYBXIUFUQUEZXKJUQUEUF
      JULUMZXFYDYEXIVTVMXSXIXBUQJXOWTXCXFWAZVGXIXCYFYGJUFXAWBVOXDXFWDJUFXEWEWFJ
      UFXEWGVOWTYBYCWHXCXFWTYAXHXJWTXTXGJUNWTUFXEUFWIUEWTWJVMWTXEXRWOWKWLWMVHWN
      WPWTXCXFWQWAWRWS $.

    $( The range ` ( 1 ... ( I `` C ) ) ` is invariant under ` ( S `` C ) ` .
       (Contributed by Thierry Arnoux, 28-Apr-2017.) $)
    ballotlemsel1i $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( I ` C ) ) ) ->
      ( ( S ` C ) ` J ) e. ( 1 ... ( I ` C ) ) ) $=
      ( cdif wcel c1 cfv cfz co wa cz cle wbr a1i caddc cc0 ballotlemiex simpld
      1z wceq elfzelz syl adantr cuz nnaddcl mp2an nnzi elfzle2 eluz2 syl3anbrc
      wss cn fzss2 sselda ballotlemsdom syldan cmin adantl zred cr 1re readdcld
      zcnd cc ax-1cn pncand breqtrrd lesubd cif ballotlemsv iftrue eqtrd elfznn
      ltesubnnd eqbrtrd elfz4 syl32anc ) BMGUDUEZJUFBIUGZUHUIZUEZUJZUFUKUEZWSUK
      UEZJBDUGUGZUKUEZUFXEULUMXEWSULUMXEWTUEXCXBUSUNWRXDXAWRWSUFKLUOUIZUHUIZUEZ
      XDWRXIWSBHUGUGUPUTABCEFGHIKLMNOPQRSTUAUBUQURZWSUFXGVAVBZVCZXBXEXHUEZXFWRX
      AJXHUEZXMWRWTXHJWRXGWSVDUGUEZWTXHVKWRXDXGUKUEZWSXGULUMZXOXKXPWRXGKVLUELVL
      UEXGVLUEOPKLVEVFVGUNWRXIXQXJWSUFXGVHVBWSXGVIVJWSUFXGVMVBVNZABCDEFGHIJKLMN
      OPQRSTUAUBUCVOVPXEUFXGVAVBXBUFWSUFUOUIZJVQUIZXEULXBJXSUFXBJXAJUKUEWRJUFWS
      VAVRVSXBWSUFXBWSXLVSUFVTUEXBWAUNZWBYAXBJWSXSUFVQUIULXAJWSULUMZWRJUFWSVHVR
      ZXBWSUFXBWSXLWCUFWDUEXBWEUNWFWGWHXBXEYBXTJWIZXTWRXAXNXEYDUTXRABCDEFGHIJKL
      MNOPQRSTUAUBUCWJVPXBYBYDXTUTYCYBXTJWKVBWLZWGXBXEXTWSULYEWRXAXNXTWSULUMXRW
      RXNUJWSJWRXDXNXKVCXNJVLUEWRJXGWMVRWNVPWOXEUFWSWPWQ $.

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
      syl ad2antll elfznn ltesubnnd vex a1i ovex ifeqeqx ad2antrl simplrl f1o3d
      impbida ifbieq12d cbvmptv simprd 3eqtr4rd jca ) BLGUDUEZUFJKUGUQZUHUQZWTB
      DUIZUJZXAUKZXAULWRXBXCUCWTUCURZBIUIZUMUNZXEUFUGUQZXDUOUQZXDUSZUTZULZWREUC
      WTWTEURZXEUMUNZXGXLUOUQZXLUSZXIXAABCDEFGHIJKLMNOPQRSTUAUBUPZWRXLWTUEZVAXL
      XAUIXOWTABCDEFGHIXLJKLMNOPQRSTUAUBVBABCDEFGHIXLJKLMNOPQRSTUAUBVCVDWRXDWTU
      EZVAXDXAUIXIWTABCDEFGHIXDJKLMNOPQRSTUAUBVBABCDEFGHIXDJKLMNOPQRSTUAUBVCVDW
      RXQXRVAZVAZXLXIULXDXOULXTXFXMXHXEUMUNZEXNXLXGXHUOUQZVJVJXHXDUCXLXHXGUOVEX
      LXDULZVFZXLXHXEUMVGXLXDXEUMVGZXTYBXDXTXGXDWRXGVHUEXSWRXGWRXEWTUEZXGVIUEWR
      YFXEBHUIUIVKULABCEFGHIJKLMNOPQRSTUAVLVMZYFXEXEUFWSVNZVOWAVPVQZXRXDVHUEWRX
      QXRXDXDUFWSVNVPWBVRVSXTYAXFXTXEXDWRXEVIUEZXSWRYFYJYGYHWAVQZXRXDVTUEWRXQXD
      WSWCWBWDVQXDVJUEXTUCWEWFXHVJUEXTXGXDUOWGWFWHXTXMXFXNXEUMUNUCXHXDXGXNUOUQZ
      VJVJXNXLEXDXNXGUOVEXDXLULVFXDXNXEUMVGXDXLXEUMVGXTYLXLXTXGXLYIXQXLVHUEWRXR
      XQXLXLUFWSVNVPWIVRVSXTXMVAZXEXLXTYJXMYKVQYMXQXLVTUEWRXQXRXMWJXLWSWCWAWDXL
      VJUEXTEWEWFXNVJUEXTXGXLUOWGWFWHWLWKZVMWREWTXOUTZXJXAXCYOXJULWREUCWTXOXIYC
      XMXFXNXLXHXDYEXLXDXGUOVEYDWMWNWFXPWRXBXKYNWOWPWQ $.

    $( The image by ` S ` of the first tie pick is the first pick.
       (Contributed by Thierry Arnoux, 14-Apr-2017.) $)
    ballotlemsi $p |- ( C e. ( O \ E ) -> ( ( S ` C ) ` ( I ` C ) ) = 1 ) $=
      ( cdif wcel cfv cle wbr c1 caddc co cmin cif cfz wceq ballotlemiex simpld
      cc0 ballotlemsv mpdan cr elfzelz syl leidd iftrue recnd cc ax-1cn pncan2d
      zred a1i 3eqtrd ) BLGUCUDZBIUEZBDUEUEZVMVMUFUGZVMUHUIUJVMUKUJZVMULZVPUHVL
      VMUHJKUIUJZUMUJUDZVNVQUNVLVSVMBHUEUEUQUNABCEFGHIJKLMNOPQRSTUAUOUPZABCDEFG
      HIVMJKLMNOPQRSTUAUBURUSVLVOVQVPUNVLVMVLVSVMUTUDVTVSVMVMUHVRVAVIVBZVCVOVPV
      MVDVBVLVMUHVLVMWAVEUHVFUDVLVGVJVHVK $.

    $d j k $.  $d j S $.  $d k J $.  $d k S $.
    $( The image by ` S ` of an interval before the first pick.  (Contributed
       by Thierry Arnoux, 5-May-2017.) $)
    ballotlemsima $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( I ` C ) ) ) ->
         ( ( S ` C ) " ( 1 ... J ) ) = ( ( ( S ` C ) ` J ) ... ( I ` C ) ) ) $=
      ( vj cdif wcel c1 cfv cfz co wa cima cz cv wss caddc imassrn wf1o wf ccnv
      crn wceq ballotlemsf1o simpld f1of frn 3syl syl5ss cuz fzssuz uzssz sstri
      syl6ss adantr sselda elfzelz adantl wb wfn f1ofn syl ballotlemiex elfzuz3
      wrex cc0 uztrn syl2anc fzss2 fvelimab cmin cle wbr cif 1z a1i nnzi zaddcl
      mp2an elfzle1 zred elfzle2 letrd elfz4 syl32anc ballotlemsv syldan iftrue
      simpr eqtrd oveq1d eleq2d ad2antrr ax-1cn pncand oveq2d ad2antlr peano2zd
      zcnd cc fzrev syl22anc 3bitr2d risset eqcom adantlr addcld simplr syl3anc
      subsub23 syl5bbr simpll eqeq1d bitr4d rexbidva 3bitrd eqrdav ) BMGUEUFZJU
      GBIUHZUIUJUFZUKZFBDUHZUGJUIUJZULZJUUAUHZYRUIUJZUMYTUUCUMFUNZYQUUCUMUOYSYQ
      UUCUGKLUPUJZUIUJZUMYQUUCUUAVAZUUHUUAUUBUQYQUUHUUHUUAURZUUHUUHUUAUSUUIUUHU
      OYQUUJUUAUTUUAVBABCDEFGHIKLMNOPQRSTUAUBUCVCVDZUUHUUHUUAVEUUHUUHUUAVFVGVHU
      UHUGVIUHUMUGUUGVJUGVKVLVMVNVOUUFUUEUFZUUFUMUFZYTUUFUUDYRVPVQYTUUMUKZUUFUU
      CUFZUDUNZUUAUHZUUFVBZUDUUBWDZUULYTUUOUUSVRZUUMYTUUAUUHVSZUUBUUHUOZUUTYQUV
      AYSYQUUJUVAUUKUUHUUHUUAVTWAVNYTUUGJVIUHZUFZUVBYTUUGYRVIUHUFZYRUVCUFZUVDYT
      YRUUHUFZUVEYQUVGYSYQUVGYRBHUHUHWEVBABCEFGHIKLMNOPQRSTUAUBWBVDZVNYRUGUUGWC
      WAYSUVFYQJUGYRWCVQYRUUGJWFWGJUGUUGWHWAZUDUUHUUBUUFUUAWIWGVNUUNUULYRUGUPUJ
      ZUUFWJUJZUUBUFZUUPUVKVBZUDUUBWDZUUSUUNUULUUFUVJJWJUJZYRUIUJZUFZUUFUVOUVJU
      GWJUJZUIUJZUFZUVLYTUULUVQVRUUMYTUUEUVPUUFYTUUDUVOYRUIYTUUDJYRWKWLZUVOJWMZ
      UVOYQYSJUUHUFZUUDUWBVBYTUGUMUFZUUGUMUFZJUMUFZUGJWKWLZJUUGWKWLUWCUWDYTWNWO
      UWEYTKUMUFLUMUFUWEKOWPLPWPKLWQWRWOZYSUWFYQJUGYRVPZVQZYSUWGYQJUGYRWSVQYTJY
      RUUGYTJUWJWTYTYRYQYRUMUFZYSYQUVGUWKUVHYRUGUUGVPWAZVNWTYTUUGUWHWTYSUWAYQJU
      GYRXAZVQYQYRUUGWKWLZYSYQUVGUWNUVHYRUGUUGXAWAVNXBJUGUUGXCXDABCDEFGHIJKLMNO
      PQRSTUAUBUCXEXFYTYSUWAUWBUVOVBYQYSXHUWMUWAUVOJXGVGXIXJXKVNUUNUVSUVPUUFUUN
      UVRYRUVOUIUUNYRUGUUNYRYQUWKYSUUMUWLXLZXRUGXSUFZUUNXMWOXNXOXKUUNUWDUWFUVJU
      MUFUUMUVTUVLVRUWDUUNWNWOYSUWFYQUUMUWIXPUUNYRUWOXQYTUUMXHUVJUUFUGJXTYAYBUV
      LUVNVRUUNUDUVKUUBYCWOUUNUVMUURUDUUBUUNUUPUUBUFZUKZUVMUVJUUPWJUJZUUFVBZUUR
      UVMUVKUUPVBZUWRUWTUVKUUPYDUWRUVJXSUFUUFXSUFUUPXSUFUXAUWTVRUWRYRUGUWRYRYTU
      WQUWKUUMYQUWKYSUWQUWLXLZYEXRUWPUWRXMWOYFUWRUUFYTUUMUWQYGXRUWRUUPUWQUUPUMU
      FZUUNUUPUGJVPZVQXRUVJUUFUUPYIYHYJYTUWQUURUWTVRUUMYTUWQUKZUUQUWSUUFUXEUUQU
      UPYRWKWLZUWSUUPWMZUWSUXEYQUUPUUHUFUUQUXGVBYQYSUWQYKYTUUBUUHUUPUVIVOABCDEF
      GHIUUPKLMNOPQRSTUAUBUCXEWGUXEUXFUXGUWSVBUXEUUPJYRUXEUUPUWQUXCYTUXDVQWTUXE
      JYSUWFYQUWQUWIXPWTUXEYRUXBWTUWQUUPJWKWLYTUUPUGJXAVQYSUWAYQUWQUWMXPXBUXFUW
      SUUPXGWAXIYLYEYMYNYOYMYP $.

    $d i k D $.
    $( If two countings share the same first tie, they also have the same swap
       function.  (Contributed by Thierry Arnoux, 18-Apr-2017.) $)
    ballotlemieq $p |- ( ( C e. ( O \ E ) /\ D e. ( O \ E ) /\
      ( I ` C ) = ( I ` D ) ) -> ( S ` C ) = ( S ` D ) ) $=
      ( cdif wcel cfv wceq w3a c1 caddc co cfz cv cle wbr cmin cif simpl breq2d
      oveq1d eqidd ifbieq12d mpteq2dva 3ad2ant3 ballotlemsval 3ad2ant1 3ad2ant2
      cmpt wa 3eqtr4d ) BMHUDZUEZCVKUEZBJUFZCJUFZUGZUHFUIKLUJUKULUKZFUMZVNUNUOZ
      VNUIUJUKZVRUPUKZVRUQZVHZFVQVRVOUNUOZVOUIUJUKZVRUPUKZVRUQZVHZBEUFZCEUFZVPV
      LWCWHUGVMVPFVQWBWGVPVRVQUEZVIZVSWDWAVRWFVRWLVNVOVRUNVPWKURZUSWLVTWEVRUPWL
      VNVOUIUJWMUTUTWLVRVAVBVCVDVLVMWIWCUGVPABDEFGHIJKLMNOPQRSTUAUBUCVEVFVMVLWJ
      WHUGVPACDEFGHIJKLMNOPQRSTUAUBUCVEVGVJ $.

    $( R is the operation reflecting the picks in a count,
       before a tie is reached. $)
    ballotth.r $e |- R = ( c e. ( O \ E ) |-> ( ( S ` c ) " c ) ) $.

    $d i S $.  $d c S $.
    ${
      $d c d i $.  $d d E $.  $d d I $.  $d d O $.  $d d C $.  $d d S $.
      $d c I $.  $d i J $.  $d i I $.
      $( Value of ` R ` .  (Contributed by Thierry Arnoux, 14-Apr-2017.) $)
      ballotlemrval $p |- ( C e. ( O \ E )
            -> ( R ` C ) = ( ( S ` C ) " C ) ) $=
        ( vd cv cfv cima cdif wceq fveq2 id imaeq12d cmpt cbvmptv cvv wcel fvex
        eqtri imaexg ax-mp fvmpt ) UEBUEUFZEUGZVCUHZBEUGZBUHZMHUIZDVCBUJZVDVFVC
        BVCBEUKVIULUMDNVHNUFZEUGZVJUHZUNUEVHVEUNUDNUEVHVLVEVJVCUJZVKVDVJVCVJVCE
        UKVMULUMUOUSVFUPUQVGUPUQBEURVFBUPUTVAVB $.
    $}

    $( The image of ` ( R `` C ) ` by ` ( S `` C ) ` (Contributed by Thierry
       Arnoux, 21-Apr-2017.) $)
    ballotlemscr $p |- ( C e. ( O \ E ) -> ( ( S ` C ) " ( R ` C ) ) = C ) $=
      ( cdif wcel cfv cima ccnv ballotlemrval imaeq2d c1 caddc co cfz wf1o wceq
      ballotlemsf1o simprd imaeq1d wf1 wss simpld f1of1 syl eldifi ballotlemelo
      chash simplbi f1imacnv syl2anc 3eqtr2d ) BMHUEUFZBEUGZBDUGZUHVNVNBUHZUHVN
      UIZVPUHZBVMVOVPVNABCDEFGHIJKLMNOPQRSTUAUBUCUDUJUKVMVQVNVPVMULKLUMUNUOUNZV
      SVNUPZVQVNUQZABCEFGHIJKLMNOPQRSTUAUBUCURZUSUTVMVSVSVNVAZBVSVBZVRBUQVMVTWC
      VMVTWAWBVCVSVSVNVDVEVMBMUFZWDBMHVFWEWDBVHUGKUQBKLMNOPQVGVIVEVSVSBVNVJVKVL
      $.

    ${
      $( Value of ` R ` evaluated at ` J ` .  (Contributed by Thierry Arnoux,
         17-Apr-2017.) $)
      ballotlemrv $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) ) ->
        ( J e. ( R ` C ) <->
              if ( J <_ ( I ` C ) , ( ( ( I ` C ) + 1 ) - J ) , J ) e. C ) ) $=
        ( cdif wcel c1 caddc co cfz wa cfv ccnv cima cle wbr cmin cif wfun wf1o
        cdm wb simpl wceq ballotlemsf1o simpld f1ofun 3syl simpr f1odm eleqtrrd
        fvimacnv syl2anc ballotlemsv eleq1d simprd imaeq1d ballotlemrval eqtr4d
        eleq2d syl 3bitr3rd ) BNHUFUGZKUHLMUIUJUKUJZUGZULZKBEUMZUMZBUGZKWHUNZBU
        OZUGZKBJUMZUPUQWNUHUIUJKURUJKUSZBUGKBDUMZUGZWGWHUTZKWHVBZUGWJWMVCWGWDWE
        WEWHVAZWRWDWFVDZWDWTWKWHVEZABCEFGHIJLMNOPQRSTUAUBUCUDVFZVGZWEWEWHVHVIWG
        KWEWSWDWFVJWGWDWTWSWEVEXAXDWEWEWHVKVIVLKBWHVMVNWGWIWOBABCEFGHIJKLMNOPQR
        STUAUBUCUDVOVPWGWDWMWQVCXAWDWLWPKWDWLWHBUOWPWDWKWHBWDWTXBXCVQVRABCDEFGH
        IJLMNOPQRSTUAUBUCUDUEVSVTWAWBWC $.

      $( Value of ` R ` before the tie.  (Contributed by Thierry Arnoux,
         11-Apr-2017.) $)
      ballotlemrv1 $p
       |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) /\ J <_ ( I ` C ) ) ->
                     ( J e. ( R ` C ) <-> ( ( ( I ` C ) + 1 ) - J ) e. C ) ) $=
  ( cdif wcel c1 caddc co cfz cfv cle wbr w3a cif wb ballotlemrv 3adant3 iftrue
  cmin eleq1d 3ad2ant3 bitrd ) BNHUFUGZKUHLMUIUJUKUJUGZKBJULZUMUNZUOKBDULUGZVHV
  GUHUIUJKVAUJZKUPZBUGZVJBUGZVEVFVIVLUQVHABCDEFGHIJKLMNOPQRSTUAUBUCUDUEURUSVHVE
  VLVMUQVFVHVKVJBVHVJKUTVBVCVD $.

      $( Value of ` R ` after the tie.  (Contributed by Thierry Arnoux,
         11-Apr-2017.) $)
      ballotlemrv2 $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) /\
        ( I ` C ) < J ) -> ( J e. ( R ` C ) <-> J e. C ) ) $=
        ( cdif wcel c1 caddc co cfz cfv clt wbr w3a cle cmin cif wb ballotlemrv
        3adant3 wn wceq wa cz cuz fzssuz uzssz sstri ballotlemiex simpld sseldi
        cc0 adantr zred simpr ltnled biimp3a iffalse syl eleq1d bitrd ) BNHUFUG
        ZKUHLMUIUJZUKUJZUGZBJULZKUMUNZUOZKBDULUGZKWGUPUNZWGUHUIUJKUQUJZKURZBUGZ
        KBUGWCWFWJWNUSWHABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUTVAWIWMKBWIWKVBZWMKVCWCW
        FWHWOWCWFVDZWGKWPWGWCWGVEUGWFWCWEVEWGWEUHVFULVEUHWDVGUHVHVIZWCWGWEUGWGB
        IULULVMVCABCFGHIJLMNOPQRSTUAUBUCVJVKVLVNVOWPKWPWEVEKWQWCWFVPVLVOVQVRWKW
        LKVSVTWAWB $.

      $( Range of ` R ` is included in ` O ` .  (Contributed by Thierry Arnoux,
         17-Apr-2017.) $)
      ballotlemro $p |- ( C e. ( O \ E ) -> ( R ` C ) e. O ) $=
        ( cdif wcel cfv c1 caddc co cfz wss wceq cima ballotlemrval crn imassrn
        chash wf1o wfo ccnv ballotlemsf1o simpld forn 3syl syl5sseq eqsstrd cen
        f1ofo wbr wf1 f1of1 syl wa eldifi ballotlemelo sylib id syl3anc eqbrtrd
        f1imaeng hasheni simprd eqtrd sylanbrc ) BMHUEZUFZBDUGZUHKLUIUJUKUJZULW
        HURUGZKUMWHMUFWGWHBEUGZBUNZWIABCDEFGHIJKLMNOPQRSTUAUBUCUDUOZWGWKUPZWLWI
        WKBUQWGWIWIWKUSZWIWIWKUTWNWIUMWGWOWKVAWKUMABCEFGHIJKLMNOPQRSTUAUBUCVBVC
        ZWIWIWKVIWIWIWKVDVEVFVGWGWJBURUGZKWGWHBVHVJWJWQUMWGWHWLBVHWMWGWIWIWKVKZ
        BWIULZWGWLBVHVJWGWOWRWPWIWIWKVLVMWGWSWQKUMZWGBMUFWSWTVNBMHVOBKLMNOPQVPV
        QZVCWGVRWIWIBWKWFWAVSVTWHBWBVMWGWSWTXAWCWDWHKLMNOPQVPWE $.
    $}

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
        co difeq1 ovex ovmpt2 ) CBGQUJUJBUKZCUKZULZUMUNZVGVHUOZUMUNZUPVCQGULZUM
        UNZQGUOZUMUNZUPVCKVGGULZUMUNZVGGUOZUMUNZUPVCVHGUQZVJVRVLVTUPWAVIVQUMVHG
        VGURUSWAVKVSUMVHGVGUTUSVAVGQUQZVRVNVTVPUPWBVQVMUMVGQGVBUSWBVSVOUMVGQGVD
        USVAUIVNVPUPVEVF $.

      ${
        $d u v U $.  $d u v V $.  $d u v W $.
        ballotlemgun.1 $e |- ( ph -> U e. Fin ) $.
        ballotlemgun.2 $e |- ( ph -> V e. Fin ) $.
        ballotlemgun.3 $e |- ( ph -> W e. Fin ) $.
        ballotlemgun.4 $e |- ( ph -> ( V i^i W ) = (/) ) $.
        $( A property of the defined ` .^ ` operator (Contributed by Thierry
           Arnoux, 26-Apr-2017.) $)
        ballotlemgun $p |- ( ph ->
                         ( U .^ ( V u. W ) ) = ( ( U .^ V ) + ( U .^ W ) ) ) $=
          ( cun cin chash cfv cdif cmin co caddc indir fveq2i wcel c0 wceq infi
          cfn syl ineq1d inindir incom in0 eqtr3i 3eqtr3g hashun syl3anc syl5eq
          difundir diffi difeq1d difindir 0dif oveq12d cn0 hashcl 3syl addsub4d
          nn0cnd eqtrd unfi syl2anc ballotlemgval 3eqtr4d ) ARSUPZHUQZURUSZWQHU
          TZURUSZVAVBZRHUQZURUSZRHUTZURUSZVAVBZSHUQZURUSZSHUTZURUSZVAVBZVCVBZHW
          QLVBZHRLVBZHSLVBZVCVBAXBXDXIVCVBZXFXKVCVBZVAVBXMAWSXQXAXRVAAWSXCXHUPZ
          URUSZXQWRXSURRSHVDVEAXCVJVFZXHVJVFZXCXHUQZVGVHXTXQVHARVJVFZYAUMRHVIZV
          KASVJVFZYBUNSHVIZVKARSUQZHUQVGHUQZYCVGAYHVGHUOVLRSHVMHVGUQYIVGHVGVNHV
          OVPVQXCXHVRVSVTAXAXEXJUPZURUSZXRWTYJURRSHWAVEAXEVJVFZXJVJVFZXEXJUQZVG
          VHYKXRVHAYDYLUMRHWBZVKAYFYMUNSHWBZVKAYHHUTVGHUTYNVGAYHVGHUOWCRSHWDHWE
          VQXEXJVRVSVTWFAXDXIXFXKAXDAYDYAXDWGVFUMYEXCWHWIWKAXIAYFYBXIWGVFUNYGXH
          WHWIWKAXFAYDYLXFWGVFUMYOXEWHWIWKAXKAYFYMXKWGVFUNYPXJWHWIWKWJWLAHVJVFZ
          WQVJVFZXNXBVHULAYDYFYRUMUNRSWMWNBCDEFGHIJKLMNOPQWQTUAUBUCUDUEUFUGUHUI
          UJUKWOWNAXOXGXPXLVCAYQYDXOXGVHULUMBCDEFGHIJKLMNOPQRTUAUBUCUDUEUFUGUHU
          IUJUKWOWNAYQYFXPXLVHULUNBCDEFGHIJKLMNOPQSTUAUBUCUDUEUFUGUHUIUJUKWOWNW
          FWP $.
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
        eluzfz2 3syl ballotlemfrc mpdan ballotlemsi oveq1d oveq2d eqtrd wss cn0
        1nn0 nn0uz eleqtri fzss1 ax-mp sseldi ballotlemfg simprd 3eqtr2d ) DPJU
        IUJZDMUKZDFUKLUKUKZDULWBUMUNZKUNZWBDLUKUKZUOWAWCDWBDGUKUKZWBUMUNZKUNZWE
        WAWBWDUJZWCWIUPWAWBULNOUQUNZUMUNZUJZWBULURUKUJWJWAWMWFUOUPZADEHIJLMNOPQ
        RSTUAUBUCUDUEUSZUTZWBULWKVAULWBVBVCABCDEFGHIJKLMWBNOPQRSTUAUBUCUDUEUFUG
        UHVDVEWAWHWDDKWAWGULWBUMADEGHIJLMNOPQRSTUAUBUCUDUEUFVFVGVHVIWAWBUOWKUMU
        NZUJWFWEUPWAWLWQWBULUOURUKZUJWLWQVJULVKWRVLVMVNULUOWKVOVPWPVQABCDEFGHIJ
        KLMWBNOPQRSTUAUBUCUDUEUFUGUHVRVEWAWMWNWOVSVT $.

      $( Value of ` F ` for a reverse counting ` ( R `` C ) ` .  (Contributed
         by Thierry Arnoux, 27-Apr-2017.) $)
      ballotlemfrceq $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( I ` C ) ) )
        -> ( ( F ` C ) ` ( ( ( S ` C ) ` J ) - 1 ) )
                                            = -u ( ( F ` ( R ` C ) ) ` J ) ) $=
        ( cdif wcel c1 cfv cfz co wa cmin caddc cc0 wceq cneg ballotlemsel1i cz
        wb 1z a1i ballotlemiex adantr simpld elfzelz syl cuz elfzuz3 fzss2 3syl
        simpr sseldd ballotlemsdom syldan fzsubel syl22anc mpbid 1m1e0 syl6eleq
        wss oveq1i cle wbr zsubcld cn nnaddcl mp2an elfzle2 clt zlem1lt syl2anc
        nnzi cr zred sylbid mpd eluz2 syl3anbrc sselda ballotlemfg ballotlemfrc
        wi ltle oveq12d cun fzsplit3 oveq2d cn0 nn0uz eleqtri fzss1 ax-mp sseli
        1nn0 sylan2 simprd eqtr3d cfn eldifi chash ballotlemelo simplbi sylancr
        fzfi ssfi fzfid c0 ltm1 fzdisj ballotlemgun 3eqtr3rd ballotlemfelz zcnd
        cin cc eqtrd ballotlemro addeq0 ) DQJUJUKZNULDMUMZUNUOZUKZUPZNDGUMUMZUL
        UQUOZDLUMZUMZNDFUMZLUMUMZURUOZUSUTZUULUUNVAUTZUUHUUODULUUJUNUOZKUOZDUUI
        UUEUNUOZKUOZURUOZUSUUHUULUUSUUNUVAURUUDUUGUUJUSOPURUOZUNUOZUKZUULUUSUTU
        UDUUGUUJUSUUEULUQUOZUNUOZUKUVEUUHUUJULULUQUOZUVFUNUOZUVGUUHUUIUUFUKZUUJ
        UVIUKZADEGHIJLMNOPQRSTUAUBUCUDUEUFUGVBZUUHULVCUKZUUEVCUKZUUIVCUKZUVMUVJ
        UVKVDUVMUUHVEVFZUUHUUEULUVCUNUOZUKZUVNUUHUVRUUEUUKUMZUSUTZUUDUVRUVTUPUU
        GADEHIJLMOPQRSTUAUBUCUDUEUFVGZVHZVIZUUEULUVCVJZVKUUHUUIUVQUKZUVOUUDUUGN
        UVQUKUWEUUHUUFUVQNUUHUVRUVCUUEVLUMUKUUFUVQWEUWCUUEULUVCVMUUEULUVCVNVOUU
        DUUGVPZVQADEGHIJLMNOPQRSTUAUBUCUDUEUFUGVRVSUUIULUVCVJVKZUVPUUIULULUUEVT
        WAWBUVHUSUVFUNWCWFWDUUDUVGUVDUUJUUDUVCUVFVLUMUKZUVGUVDWEUUDUVFVCUKUVCVC
        UKZUVFUVCWGWHZUWHUUDUUEULUUDUVRUVNUUDUVRUVTUWAVIZUWDVKZUVMUUDVEVFWIZUWI
        UUDUVCOWJUKPWJUKUVCWJUKSTOPWKWLWQVFZUUDUUEUVCWGWHZUWJUUDUVRUWOUWKUUEULU
        VCWMVKUUDUWOUVFUVCWNWHZUWJUUDUVNUWIUWOUWPVDUWLUWNUUEUVCWOWPUUDUVFWRUKUV
        CWRUKUWPUWJXGUUDUVFUWMWSUUDUVCUWNWSUVFUVCXHWPWTXAUVFUVCXBXCUVFUSUVCVNVK
        XDVSABCDEFGHIJKLMUUJOPQRSTUAUBUCUDUEUFUGUHUIXEVSABCDEFGHIJKLMNOPQRSTUAU
        BUCUDUEUFUGUHUIXFXIUUHDUUFKUOZDUURUUTXJZKUOUSUVBUUHUUFUWRDKUUHUVJUUFUWR
        UTUVLUUIULUUEXKVKXLUUHUVSUWQUSUUDUUGUVRUVSUWQUTZUWCUVRUUDUUEUVDUKUWSUVQ
        UVDUUEULUSVLUMZUKUVQUVDWEULXMUWTXSXNXOULUSUVCXPXQXRABCDEFGHIJKLMUUEOPQR
        STUAUBUCUDUEUFUGUHUIXEXTVSUUHUVRUVTUWBYAYBUUHABCEFGDHIJKLMOPQUURUUTRSTU
        AUBUCUDUEUFUGUHUIUUDDYCUKZUUGUUDUVQYCUKDUVQWEZUXAULUVCYIUUDDQUKZUXBDQJY
        DZUXCUXBDYEUMOUTDOPQRSTUAYFYGVKUVQDYJYHVHUUHULUUJYKUUHUUIUUEYKUUHUUIWRU
        KUUJUUIWNWHUURUUTYSYLUTUUHUUIUWGWSUUIYMULUUJUUIUUEYNVOYOYPUUAUUHUULYTUK
        UUNYTUKUUPUUQVDUUHUULUUHADEHLUUJOPQRSTUAUBUCUUDUXCUUGUXDVHUUHUUIULUWGUV
        PWIYQYRUUHUUNUUHAUUMEHLNOPQRSTUAUBUCUUDUUMQUKUUGADEFGHIJLMOPQRSTUAUBUCU
        DUEUFUGUHUUBVHUUHUUGNVCUKUWFNULUUEVJVKYQYRUULUUNUUCWPWB $.
    $}

    $d k S $.  $d k J $.
    ${
      $d u v C $.  $d u v I $.  $d u v J $.  $d u v R $.  $d u v S $.
      $d w y z $.  $d c k y z $.  $d y z C $.  $d y z F $.  $d y z M $.
      $d y z N $.  $d k w y z $.  $d w C $.  $d w F $.  $d w M $.  $d w N $.
      $d i J $.
      $( Value of ` F ` for a reversed counting ` ( R `` C ) ` , before the
         first tie, cannot be zero .  (Contributed by Thierry Arnoux,
         25-Apr-2017.) $)
      ballotlemfrcn0 $p |- ( ( C e. ( O \ E ) /\ J e. ( 1 ... ( M + N ) ) /\
        J < ( I ` C ) ) -> ( ( F ` ( R ` C ) ) ` J ) =/= 0 ) $=
        ( vz vw vy vv vu cdif wcel c1 caddc co cfz cfv clt wbr w3a cc0 wne cmin
        wceq wn cz cle 1z a1i cn nnaddcl mp2an wa ballotlemsdom elfzelz 3adant3
        nnzi syl zsubcld ballotlemsgt1 zltlem1 biimpa syl21anc zred cr resubcld
        1re simp1 ballotlemiex 3syl 3ad2ant2 elfzle1 simp3 ltled elfz4 syl32anc
        simpld ballotlemsel1i syl2anc elfzle2 wb zlem1lt mpbid letrd wi cv crab
        ccnv csup fvex brcnv sylibr ballotlemi breq1d 3ad2ant1 wor ballotlemsup
        ovex ltso cnvso mpbi supub con2d sylc fveq2 eqeq1d elrab sylnib neneqad
        imnan mpd cneg ballotlemro adantr adantl ballotlemfelz zcnd negeq0d cfn
        chash cin cmpt2 eqid ballotlemfrceq bitr4d necon3bid mpbird ) BNHUKULZK
        UMLMUNUOZUPUOZULZKBJUQZURUSZUTZKBDUQZIUQUQZVAVBZKBEUQUQZUMVCUOZBIUQZUQZ
        VAVBZUUNUVAVAUUNUUSUUJULZUVAVAVDZVEZUUNUMVFULZUUIVFULZUUSVFULUMUUSVGUSZ
        UUSUUIVGUSUVCUVFUUNVHVIZUVGUUNUUILVJULMVJULUUIVJULPQLMVKVLVQVIZUUNUURUM
        UUHUUKUURVFULZUUMUUHUUKVMUURUUJULUVKABCEFGHIJKLMNOPQRSTUAUBUCUDVNUURUMU
        UIVOVRVPZUVIVSUUNUVFUVKUMUURURUSZUVHUVIUVLABCEFGHIJKLMNOPQRSTUAUBUCUDVT
        UVFUVKVMUVMUVHUMUURWAWBWCUUNUUSUULUUIUUNUURUMUUNUURUVLWDUMWEULUUNWGVIWF
        ZUUNUULUUNUUHUULUUJULZUULVFULZUUHUUKUUMWHZUUHUVOUULUUTUQVAVDABCFGHIJLMN
        OPQRSTUAUBUCWIWQZUULUMUUIVOWJZWDZUUNUUIUVJWDUUNUUSUULUVNUVTUUNUURUULVGU
        SZUUSUULURUSZUUNUURUMUULUPUOZULZUWAUUNUUHKUWCULZUWDUVQUUNUVFUVPKVFULZUM
        KVGUSZKUULVGUSUWEUVIUVSUUKUUHUWFUUMKUMUUIVOWKZUUKUUHUWGUUMKUMUUIWLWKUUN
        KUULUUNKUWHWDUVTUUHUUKUUMWMWNKUMUULWOWPZABCEFGHIJKLMNOPQRSTUAUBUCUDWRWS
        UURUMUULWTVRUUNUVKUVPUWAUWBXAUVLUVSUURUULXBWSXCZWNUUNUUHUVOUULUUIVGUSUV
        QUVRUULUMUUIWTWJXDUUSUMUUIWOWPUUNUVCUVDVMZVEUVCUVEXEUUNUUSGXFZUUTUQZVAV
        DZGUUJXGZULZUWKUUNUUHUWOWEURXHZXIZUUSUWQUSZUWPVEUVQUUNUULUUSUWQUSZUWSUU
        NUWBUWTUWJUULUUSURBJXJUURUMVCXRXKXLUUHUUKUWTUWSXAUUMUUHUULUWRUUSUWQABCF
        GHIJLMNOPQRSTUAUBUCXMXNXOXCUUHUWPUWSUUHUFUGUHWEUWOUUSUWQWEUWQXPZUUHWEUR
        XPUXAXSWEURXTYAVIAUHUFUGBCFGHIJLMNOPQRSTUAUBUCXQYBYCYDUWNUVDGUUSUUJUWLU
        USVDUWMUVAVAUWLUUSUUTYEYFYGYHUVCUVDYJXLYKYIUUNUUHUWEUUQUVBXAUVQUWIUUHUW
        EVMZUUPVAUVAVAUXBUUPVAVDUUPYLZVAVDUVDUXBUUPUXBUUPUXBAUUOCFIKLMNOPQRSTUU
        HUUONULUWEABCDEFGHIJLMNOPQRSTUAUBUCUDUEYMYNUWEUWFUUHKUMUULVOYOYPYQYRUXB
        UVAUXCVAAUIUJBCDEFGHUJUIYSYSUIXFZUJXFZUUAYTUQUXDUXEUKYTUQVCUOUUBZIJKLMN
        OPQRSTUAUBUCUDUEUXFUUCUUDYFUUEUUFWSUUG $.

      $( Range of ` R ` .  (Contributed by Thierry Arnoux, 19-Apr-2017.) $)
      ballotlemrc $p |- ( C e. ( O \ E ) -> ( R ` C ) e. ( O \ E ) ) $=
        ( vv vu cdif wcel cfv cv cc0 cle wbr c1 caddc cfz wrex ballotlemro wceq
        co ballotlemiex simpld cfn cin chash cmin cmpt2 eqid ballotlemfrci 0le0
        syl6eqbr fveq2 breq1d rspcev syl2anc ballotlemodife sylanbrc ) BMHUGZUH
        ZBDUIZMUHFUJZVTIUIZUIZUKULUMZFUNKLUOUTUPUTZUQZVTVRUHABCDEFGHIJKLMNOPQRS
        TUAUBUCUDURVSBJUIZWEUHZWGWBUIZUKULUMZWFVSWHWGBIUIUIUKUSABCFGHIJKLMNOPQR
        STUAUBVAVBVSWIUKUKULAUEUFBCDEFGHUFUEVCVCUEUJZUFUJZVDVEUIWKWLUGVEUIVFUTV
        GZIJKLMNOPQRSTUAUBUCUDWMVHVIVJVKWDWJFWGWEWAWGUSWCWIUKULWAWGWBVLVMVNVOAV
        TCFHIKLMNOPQRSTVPVQ $.
    $}

    $d k i R $.
    ${
      $d k x y z $.  $d x y z C $.  $d y E $.  $d x y z F $.  $d y I $.
      $d x y z M $.  $d x y z N $.  $d y O $.  $d y R $.  $d u v C $.
      $d u v I $.  $d u v J $.  $d u v R $.  $d u v S $.  $d u v y U $.
      $d u v y V $.  $d i y $.
      $( Applying ` R ` does not change first ties.  (Contributed by Thierry
         Arnoux, 19-Apr-2017.) $)
      ballotlemirc $p |- ( C e. ( O \ E ) -> ( I ` ( R ` C ) ) = ( I ` C ) ) $=
        ( vy vv vu cdif wcel cfv cv cc0 wceq c1 caddc co cfz crab clt ccnv csup
        cr ballotlemrc ballotlemi syl wor ltso cnvso a1i cz ballotlemiex simpld
        mpbi elfzelz zred cfn chash cmin cmpt2 ballotlemfrci fveq2 eqeq1d elrab
        cin eqid sylanbrc wa wbr wn elrabi anim2i cvv adantr vex brcnvg sylancl
        wb biimpa w3a ballotlemfrcn0 neneqd simprbi nsyl 3expa syldan con2d imp
        ex sylancom supmax eqtrd ) BMHUHZUIZBDUJZJUJZGUKZXNIUJZUJZULUMZGUNKLUOU
        PZUQUPZURZVBUSUTZVAZBJUJZXMXNXLUIXOYDUMABCDEFGHIJKLMNOPQRSTUAUBUCUDVCAX
        NCFGHIJKLMNOPQRSTUAUBVDVEXMUEVBYBYEYCVBYCVFZXMVBUSVFYFVGVBUSVHVMVIXMYEX
        MYEYAUIZYEVJUIXMYGYEBIUJUJULUMABCFGHIJKLMNOPQRSTUAUBVKVLZYEUNXTVNVEVOXM
        YGYEXQUJZULUMZYEYBUIYHAUFUGBCDEFGHUGUFVPVPUFUKZUGUKZWDVQUJYKYLUHVQUJVRU
        PVSZIJKLMNOPQRSTUAUBUCUDYMWEVTXSYJGYEYAXPYEUMXRYIULXPYEXQWAWBWCWFXMUEUK
        ZYBUIZXMYNYAUIZWGZYEYNYCWHZWIZYOYPXMXSGYNYAWJWKYQYOYSYQYRYOYQYRYOWIZYQY
        RYNYEUSWHZYTYQYRUUAYQYGYNWLUIYRUUAWQXMYGYPYHWMUEWNYEYNYAWLUSWOWPWRXMYPU
        UAYTXMYPUUAWSZYNXQUJZULUMZYOUUBUUCULABCDEFGHIJYNKLMNOPQRSTUAUBUCUDWTXAY
        OYPUUDXSUUDGYNYAXPYNUMXRUUCULXPYNXQWAWBWCXBXCXDXEXHXFXGXIXJXK $.
    $}

    $( due to x used in ballotlemirc $)
    $d x c $.  $d x C $.  $d x F $.  $d x M $.  $d x N $.  $d c I $.
    $d d e S $.
    ${
      $d d e i x k $.  $d d e E $.  $d d e I $.  $d d e O $.
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
        wb a1i mptcnv trud fveq2 id imaeq12d cbvmptv eqtri cnveqi 3eqtr4i ) MLG
        UEZMUFZDUGZVIUHZUIZUJZVLCUJCVMUDVHUDUFZDUGZVNUHZUIZVLVMVQUKULMUDVHVKVHV
        PVIVHUMVNVKUKUNZVNVHUMVIVPUKUNZUQULVRVSAVIVNBCDEFGHIJKLMNOPQRSTUAUBUCUO
        AVNVIBCDEFGHIJKLMNOPQRSTUAUBUCUOUPURUSUTUDMVHVPVKVNVIUKZVOVJVNVIVNVIDVA
        VTVBVCVDVECVLUCVFUCVG $.
    $}

    ${
      $( When the vote on the first tie is for A, the first vote is also for A
         on the reverse counting.  (Contributed by Thierry Arnoux,
         18-Apr-2017.) $)
      ballotlem1ri $p |- ( C e. ( O \ E ) ->
                                     ( 1 e. ( R ` C ) <-> ( I ` C ) e. C ) ) $=
        ( cdif wcel c1 cfv caddc co cfz cle wbr wb cuz cn nnaddcl mp2an eleqtri
        cmin nnuz eluzfz1 mp1i cc0 ballotlemiex simpld elfzle1 syl ballotlemrv1
        wceq mpd3an23 cz elfzelz zcnd cc ax-1cn a1i pncand eleq1d bitrd ) BMHUE
        UFZUGBDUHUFZBJUHZUGUIUJUGUTUJZBUFZWCBUFWAUGUGKLUIUJZUKUJZUFZUGWCULUMZWB
        WEUNWFUGUOUHZUFWHWAWFUPWJKUPUFLUPUFWFUPUFOPKLUQURVAUSUGWFVBVCWAWCWGUFZW
        IWAWKWCBIUHUHVDVJABCFGHIJKLMNOPQRSTUAUBVEVFZWCUGWFVGVHABCDEFGHIJUGKLMNO
        PQRSTUAUBUCUDVIVKWAWDWCBWAWCUGWAWCWAWKWCVLUFWLWCUGWFVMVHVNUGVOUFWAVPVQV
        RVSVT $.
    $}

    $d x k i $.  $d c k $.
    ${
      $d b E $.  $d b c O $.  $d b R $.

      $( ` R ` is a bijection between two subsets of ` ( O \ E ) ` : one where
         a vote for A is picked first, and one where a vote for B is picked
         first (Contributed by Thierry Arnoux, 12-Dec-2016.) $)
      ballotlem7 $p |- ( R |` { c e. ( O \ E ) | 1 e. c } ) :
      { c e. ( O \ E ) | 1 e. c } -1-1-onto-> { c e. ( O \ E ) | -. 1 e. c } $=
        ( vb c1 cv wcel cdif crab wn cfv cima funmpt2 ballotlemrinv wss wral wa
        rabid ballotlemrc adantr ballotlem1c ex ballotlem1ri notbid sylibrd imp
        jca sylbi rgen wceq eleq2 cbvrabv eleq2i bitr3i ralbii mpbi wfun cdm wb
        elrab ssrab2 cvv fvex imaexg ax-mp dmmpti sseqtr4i nfrab1 nfmpt1 nfcxfr
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

    ${
      $( There are as many countings with ties starting with a ballot for A as
         there are starting with a ballot for B. (Contributed by Thierry
         Arnoux, 7-Dec-2016.) $)
      ballotlem8 $p |- ( # ` { c e. ( O \ E ) | 1 e. c } )
                     = ( # ` { c e. ( O \ E ) | -. 1 e. c } ) $=
        ( c1 cv wcel cdif crab wn cres wf1o cen wbr chash cfv wceq ballotlemoex
        ballotlem7 cvv difexg ax-mp rabex f1oen hasheni mp2b ) UDMUEUFZMLGUGZUH
        ZVFUIMVGUHZCVHUJZUKVHVIULUMVHUNUOVIUNUOUPABCDEFGHIJKLMNOPQRSTUAUBUCURVH
        VIVJVFMVGLUSUFVGUSUFJKLMNOPUQLGUSUTVAVBVCVHVIVDVE $.
    $}

    $d x c $.  $d x C $.  $d x E $.  $d x O $.
    $( Bertrand's ballot problem : the probability that A is ahead throughout
       the counting.  (Contributed by Thierry Arnoux, 7-Dec-2016.) $)
    ballotth $p |- ( P ` E ) = ( ( M - N ) / ( M + N ) ) $=
      ( cfv c1 cdif chash cdiv co cmin caddc cmul wss wceq cc0 clt wbr cfz wral
      c2 crab ssrab2 eqsstri cpw wcel cfn fzfi pwfi mpbi ssfi mp2an elexi fveq2
      cv elpw oveq1d ovex fvmpt sylbir ax-mp hashssdif eqcomi cn0 hashcl nn0cni
      difss subsub23i oveq1i eqtr4i cc wne wa cbc ballotlem1 cle nnnn0i nnaddcl
      cn nnrei nn0addge1i elfz2nn0 mpbir3an bccl2 nnne0i pm3.2i divsubdir mp3an
      eqnetri dividi 3eqtri wn ballotlem8 cun rabxm fveq2i c0 sstri rabnc eqtri
      hashun elpw2 mpbir ballotlem2 wi nfrab1 dfss2f ballotlem4 imdistani rabid
      cin eldif 3imtr4i simprbi sylanbrc oveq2i divassi 2timesi 3eqtr2i nncni
      2cn mpgbir rabss2 3eqtr3i 3eqtr4ri mulcli addsub4i subidi addid1i oveq12i
      eqssi subcli 3eqtr3ri ) GBUDZUELGUFZUGUDZLUGUDZUHUIZUJUIZUEUTKJKUKUIZUHUI
      ZULUIZUJUIZJKUJUIZUUSUHUIZUUMUUPUUOUJUIZUUPUHUIZUUPUUPUHUIZUUQUJUIZUURUUM
      GUGUDZUUPUHUIZUVFGLUMZUUMUVJUNZGUOEVNMVNZHUDUDUPUQEUEUUSURUIZUSZMLVALSUVO
      MLVBVCZUVKGLVDZVEUVLGLGVFLVFVEZUVKGVFVEZUVNVDZVFVEZLUVTUMUVRUVNVFVEUWAUEU
      USVGUVNVHVIZLUVMUGUDJUNZMUVTVAUVTPUWCMUVTVBVCZUVTLVJVKZUVPLGVJVKZVLVOAGAV
      NZUGUDZUUPUHUIZUVJUVQBUWGGUNUWHUVIUUPUHUWGGUGVMVPQUVIUUPUHVQVRVSVTUVEUVIU
      UPUHUUPUVIUJUIZUUOUNUVEUVIUNUUOUWJUVRUVKUUOUWJUNUWEUVPLGWAVKWBUUPUVIUUOUU
      PUVRUUPWCVEUWELWDVTWEZUVIUVSUVIWCVEUWFGWDVTWEUUOUUNVFVEZUUOWCVEUVRUUNLUMZ
      UWLUWELGWFZLUUNVJVKUUNWDVTWEZWGVIWHWIUUPWJVEZUUOWJVEUWPUUPUOWKZWLUVFUVHUN
      UWKUWOUWPUWQUWKUUPUUSJWMUIZUOJKLMNOPWNUWRJUOUUSURUIVEZUWRWRVEUWSJWCVEUUSW
      CVEJUUSWOUQJNWPUUSJWRVEKWRVEUUSWRVENOJKWQVKZWPJKJNWSKOWPWTJUUSXAXBJUUSXCV
      TXDXHZXEUUPUUOUUPXFXGUVGUEUUQUJUUPUWKUXAXIWHXJUVAUUQUEUJUEUVMVEZMUUNVAZUG
      UDZUXBXKZMUUNVAZUGUDZUKUIZUUPUHUIUXGUXGUKUIZUUPUHUIZUUQUVAUXHUXIUUPUHUXDU
      XGUXGUKABCDEFGHIJKLMNOPQRSTUAUBUCXLWHWHUUOUXHUUPUHUUOUXCUXFXMZUGUDZUXHUUN
      UXKUGUXBMUUNXNXOUXCVFVEZUXFVFVEZUXCUXFYJXPUNUXLUXHUNUWAUXCUVTUMUXMUWBUXCL
      UVTUXCUUNLUXBMUUNVBUWNXQUWDXQUVTUXCVJVKUWAUXFUVTUMUXNUWBUXFLUVTUXFUUNLUXE
      MUUNVBUWNXQUWDXQUVTUXFVJVKZUXBMUUNXRUXCUXFXTXGXSWHUVAUTUXGUUPUHUIZULUIUTU
      XGULUIZUUPUHUIUXJUUTUXPUTULUXEMLVAZBUDZUXRUGUDZUUPUHUIZUUTUXPUXRUVQVEZUXS
      UYAUNUYBUXRLUMUXEMLVBUXRLLVFUWEVLYAYBAUXRUWIUYAUVQBUWGUXRUNUWHUXTUUPUHUWG
      UXRUGVMVPQUXTUUPUHVQVRVTABJKLMNOPQYCUXTUXGUUPUHUXRUXFUGUXRUXFUXRUXFUMUVMU
      XRVEZUVMUXFVEZYDMMUXRUXFUXEMLYEUXEMUUNYEYFUYCUVMUUNVEZUXEUYDUVMLVEZUXEWLU
      YFUVMGVEXKZWLUYCUYEUYFUXEUYGAUVMBEGHJKLMNOPQRSYGYHUXEMLYIZUVMLGYKYLUYCUYF
      UXEUYHYMUXEMUUNYIYNUUAUWMUXFUXRUMUWNUXEMUUNLUUBVTUUJXOWHUUCYOUTUXGUUPYTUX
      GUXNUXGWCVEUXOUXFWDVTWEZUWKUXAYPUXQUXIUUPUHUXGUYIYQWHYRUUDYOUUSUTKULUIZUJ
      UIZUUSUHUIZUUSUUSUHUIZUYJUUSUHUIZUJUIZUVDUVBUUSWJVEZUYJWJVEUYPUUSUOWKZWLU
      YLUYOUNUUSUWTYSZUTKYTKOYSZUUEUYPUYQUYRUUSUWTXDZXEUUSUYJUUSXFXGUYKUVCUUSUH
      UYKUUSKKUKUIZUJUIZUVCUYJVUAUUSUJKUYSYQYOVUBUVCKKUJUIZUKUIUVCUOUKUIUVCJKKK
      JNYSZUYSUYSUYSUUFVUCUOUVCUKKUYSUUGYOUVCJKVUDUYSUUKUUHXJXSWHUYMUEUYNUVAUJU
      USUYRUYTXIUTKUUSYTUYSUYRUYTYPUUIUULYR $.
  $}

