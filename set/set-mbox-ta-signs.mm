  $( Condition for an integer interval to be a subset of a half-open integer
     interval.  (Contributed by Thierry Arnoux, 8-Oct-2018.) $)
  fzssfzo $p |- ( K e. ( M ..^ N ) -> ( M ... K ) C_ ( M ..^ N ) ) $=
    ( cfzo co wcel cfz cmin cuz cfv wss wceq elfzoel2 fzoval syl eleq2d elfzuz3
    c1 cz ibi fzss2 3syl sseqtrrd ) ABCDEZFZBAGEZBCRHEZGEZUDUEAUHFZUGAIJFUFUHKU
    EUIUEUDUHAUECSFUDUHLABCMBCNOZPTABUGQABUGUAUBUJUC $.

  ${
    $d x y B $.  $d k x y K $.  $d x y M $.  $d k x y N $.  $d k x y P $.
    $d k x y ph $.
    gsumncl.k $e |- K = ( Base ` M ) $.
    gsumncl.w $e |- ( ph -> M e. Mnd ) $.
    gsumncl.p $e |- ( ph -> P e. ( ZZ>= ` N ) ) $.
    gsumncl.b $e |- ( ( ph /\ k e. ( N ... P ) ) -> B e. K ) $.
    $( Closure of a group sum in a non-commutative monoid.  (Contributed by
       Thierry Arnoux, 8-Oct-2018.) $)
    gsumncl $p |- ( ph -> ( M gsum ( k e. ( N ... P ) |-> B ) ) e. K ) $=
      ( vx vy cfz co cfv cmnd cv wcel wa cmpt cplusg fmpttd gsumval2 ffvelcdmda
      cgsu cseq eqid adantr simprl simprr mndcl syl3anc seqcl eqeltrd ) AFDGCNO
      ZBUAZUFOCFUBPZUQGUGPEAEURUQFGCQHURUHZIJADUPBEKUCZUDALMUREUQGCJAUPELRZUQUT
      UEAVAESZMRZESZTZTFQSZVBVDVAVCUROESAVFVEIUIAVBVDUJAVBVDUKEURFVAVCHUSULUMUN
      UO $.

    $d i B $.  $d k C $.  $d i k N $.  $d i k P $.  $d i k ph $.
    gsumnunsn.a $e |- .+ = ( +g ` M ) $.
    gsumnunsn.l $e |- ( ph -> C e. K ) $.
    gsumnunsn.c $e |- ( ( ph /\ k = ( P + 1 ) ) -> B = C ) $.
    $( Closure of a group sum in a non-commutative monoid.  (Contributed by
       Thierry Arnoux, 8-Oct-2018.) $)
    gsumnunsn $p |- ( ph -> ( M gsum ( k e. ( N ... ( P + 1 ) ) |-> B ) )
      = ( ( M gsum ( k e. ( N ... P ) |-> B ) ) .+ C ) ) $=
      ( co cfv wcel wceq vi c1 caddc cfz cmpt cseq cgsu cuz seqp1 cmnd peano2uz
      syl cv wa adantlr ad2antrr eqeltrd elfzp1 biimpa mpjaodan fmpttd gsumval2
      wo wb cres fvres adantl fzssp1 resmpt ax-mp fveq1i eqtr3di seqfveq eqtr4d
      wss eqidd eluzfz2 fvmptd eqcomd oveq12d 3eqtr4d ) ADUBUCQZEFIWBUDQZBUEZIU
      FZRZDWERZWBWDRZEQZHWDUGQHFIDUDQZBUEZUGQZCEQADIUHRZSZWFWITLEWDIDUIULAGEWDH
      IWBUJJNKAWNWBWMSZLIDUKULZAFWCBGAFUMZWCSZUNZWQWJSZBGSZWQWBTZAWTXAWRMUOWSXB
      UNBCGAXBBCTWRPUOACGSWRXBOUPUQAWRWTXBVCZAWNWRXCVDLWQIDURULUSUTVAVBAWLWGCWH
      EAWLDEWKIUFRWGAGEWKHIDUJJNKLAFWJBGMVAVBAEUAWDWKIDLAUAUMZWJSZUNXDWDWJVEZRZ
      XDWDRZXDWKRXEXGXHTAXDWJWDVFVGXDXFWKWJWCVOXFWKTIDVHFWCWJBVIVJVKVLVMVNAWHCA
      FWBBCWCWDGAWDVPPAWOWBWCSWPIWBVQULOVRVSVTWA $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Operations on words
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d i A $.  $d i B $.  $d i K $.  $d i M $.  $d i N $.  $d i ph $.
    ccatmulgnn0dir.a $e |- A = ( ( 0 ..^ M ) X. { K } ) $.
    ccatmulgnn0dir.b $e |- B = ( ( 0 ..^ N ) X. { K } ) $.
    ccatmulgnn0dir.c $e |- C = ( ( 0 ..^ ( M + N ) ) X. { K } ) $.
    ccatmulgnn0dir.k $e |- ( ph -> K e. S ) $.
    ccatmulgnn0dir.m $e |- ( ph -> M e. NN0 ) $.
    ccatmulgnn0dir.n $e |- ( ph -> N e. NN0 ) $.
    $( Concatenation of words follow the rule ~ mulgnn0dir (although applying
       ~ mulgnn0dir would require ` S ` to be a set).  In this case ` A ` is
       ` <" K "> ` to the power ` M ` in the free monoid.  (Contributed by
       Thierry Arnoux, 5-Oct-2018.) $)
    ccatmulgnn0dir $p |- ( ph -> ( A ++ B ) = C ) $=
      ( cc0 chash co cfzo wcel wceq vi cfv caddc cmin cif cmpt cconcat cmul csn
      cv c1 cxp fveq2i cfn fzofi snfi hashxp mp2an cn0 hashfzo0 hashsng oveq12d
      eqtri syl eqtrid nn0cnd mulridd eqtrd oveq2d simpll simpr eleqtrd fconstg
      wa wf a1i feq1d mpbird fvconst sylan syl2anc wn cz eqeltrd nn0zd fzocatel
      simplr syl22anc ifeqda mpteq12dva ovex snex xpex eqeltri ccatfval 3eqtr4g
      cvv fconstmpt ) AUAOBPUBZCPUBZUCQZRQZUAUJZOWSRQZSZXCBUBZXCWSUDQZCUBZUEZUF
      ZUAOGHUCQZRQZFUFZBCUGQZDAUAXBXIXLFAXAXKORAWSGWTHUCAWSGUKUHQZGAWSOGRQZPUBZ
      FUIZPUBZUHQZXOWSXPXRULZPUBZXTBYAPIUMXPUNSXRUNSZYBXTTOGUOFUPZXPXRUQURVCAXQ
      GXSUKUHAGUSSXQGTMGUTVDAFESZXSUKTLFEVAVDZVBVEAGAGMVFVGVHZAWTHUKUHQZHAWTOHR
      QZPUBZXSUHQZYHWTYIXRULZPUBZYKCYLPJUMYIUNSYCYMYKTOHUOYDYIXRUQURVCAYJHXSUKU
      HAHUSSYJHTNHUTVDYFVBVEAHAHNVFVGVHZVBVIAXCXBSZVNZXEXFXHFYPXEVNZAXCXPSZXFFT
      ZAYOXEVJZYQXCXDXPYPXEVKYQAXDXPTYTAWSGORYGVIVDVLAXPXRBVOZYRYSAUUAXPXRYAVOZ
      AYEUUBLXPFEVMVDAXPXRBYABYATAIVPVQVRXPFXCBVSVTWAYPXEWBZVNZAXGYISZXHFTZAYOU
      UCVJZUUDXGOWTRQZYIUUDYOUUCWSWCSWTWCSXGUUHSAYOUUCWGYPUUCVKUUDWSUUDAWSUSSUU
      GAWSGUSYGMWDVDWEUUDWTUUDAWTUSSUUGAWTHUSYNNWDVDWEXCWSWTWFWHUUDAUUHYITUUGAW
      THORYNVIVDVLAYIXRCVOZUUEUUFAUUIYIXRYLVOZAYEUUJLYIFEVMVDAYIXRCYLCYLTAJVPVQ
      VRYIFXGCVSVTWAWIWJBWQSCWQSXNXJTBYAWQIXPXROGRWKFWLZWMWNCYLWQJYIXROHRWKUUKW
      MWNUABCWQWQWOURDXLXRULXMKUAXLFWRVCWP $.
  $}

  ${
    ofcccat.1 $e |- ( ph -> F e. Word S ) $.
    ofcccat.2 $e |- ( ph -> G e. Word S ) $.
    ofcccat.3 $e |- ( ph -> K e. T ) $.
    $( Letterwise operations on word concatenations.  (Contributed by Thierry
       Arnoux, 5-Oct-2018.) $)
    ofcccat $p |- ( ph -> ( ( F ++ G ) oFC R K )
      = ( ( F oFC R K ) ++ ( G oFC R K ) ) ) $=
      ( cconcat co cc0 chash cfv cfzo wcel cmul wceq syl csn cxp cof cofc cword
      wf fconst6g iswrdi 3syl cfn fzofi snfi hashxp mp2an c1 cn0 lencl hashfzo0
      hashsng oveq12d nn0cnd mulridd eqtrd eqtr2id ofccat cvv ccatcl wrdf ovexd
      syl2anc ofcof caddc ccatlen oveq2d xpeq1d ccatmulgnn0dir 3eqtr4a 3eqtr4d
      eqid ) AEFKLZMENOZPLZGUAZUBZMFNOZPLZWCUBZKLZBUCZLZEWDWILZFWGWILZKLVTGBUDZ
      LZEGWMLZFGWMLZKLABCDEFWDWGHIAGDQZWBDWDUFWDDUEZQJWBGDUGDWAWDUHUIAWQWFDWGUF
      WGWRQJWFGDUGDWEWGUHUIAWDNOZWBNOZWCNOZRLZWAWBUJQWCUJQZWSXBSMWAUKGULZWBWCUM
      UNAXBWAUORLWAAWTWAXAUORAECUEZQZWAUPQZWTWASHCEUQZWAURUIAWQXAUOSJGDUSTZUTAW
      AAWAAXFXGHXHTZVAVBVCVDAWGNOZWFNOZXARLZWEWFUJQXCXKXMSMWEUKXDWFWCUMUNAXMWEU
      ORLWEAXLWEXAUORAFXEQZWEUPQZXLWESICFUQZWEURUIXIUTAWEAWEAXNXOIXPTZVAVBVCVDV
      EAWNVTMVTNOZPLZWCUBZWILWJAXSCGBVTVFDAVTXEQZXSCVTUFAXFXNYAHICEFVGVJCVTVHTA
      MXRPVIJVKAXTWHVTWIAMWAWEVLLZPLZWCUBZYDXTWHYDVSZAXSYCWCAXRYBMPAXFXNXRYBSHI
      CCEFVMVJVNVOAWDWGYDDGWAWEWDVSWGVSYEJXJXQVPVQVNVCAWOWKWPWLKAWBCGBEVFDAXFWB
      CEUFHCEVHTAMWAPVIJVKAWFCGBFVFDAXNWFCFUFICFVHTAMWEPVIJVKUTVR $.
  $}

  ${
    $d i A $.  $d i B $.  $d i R $.  $d i S $.  $d i T $.
    $( Letterwise operations on a single letter word.  (Contributed by Thierry
       Arnoux, 7-Oct-2018.) $)
    ofcs1 $p |- ( ( A e. S /\ B e. T )
      -> ( <" A "> oFC R B ) = <" ( A R B ) "> ) $=
      ( vi wcel wa cs1 co cc0 csn cmpt cvv wceq cop s1val cn0 0nn0 fmptsn simpr
      cofc snex a1i cv simpll mpan eqtrd adantr ofcfval2 ovex ax-mp mp2an eqtri
      eqtr4di ) ADGZBEGZHZAIZBCUBJFKLZABCJZMZVAIZURFUTABCUSNEDUTNGURKUCUDUPUQUA
      UPUQFUEUTGUFUPUSFUTAMZOUQUPUSKAPLZVDADQKRGZUPVEVDOSFKARDTUGUHUIUJVCKVAPLZ
      VBVANGZVCVGOABCUKZVANQULVFVHVGVBOSVIFKVARNTUMUNUO $.
  $}

  $( Letterwise operations on a double letter word.  (Contributed by Thierry
     Arnoux, 9-Oct-2018.) $)
  ofcs2 $p |- ( ( A e. S /\ B e. S /\ C e. T )
    -> ( <" A B "> oFC R C ) = <" ( A R C ) ( B R C ) "> ) $=
    ( wcel w3a cs2 cofc cs1 cconcat df-s2 oveq1i simp1 s1cld wceq ofcs1 syl2anc
    co simp2 simp3 ofcccat eqtrid oveq12d eqtr4di eqtrd ) AEGZBEGZCFGZHZABIZCDJ
    ZTZAKZCUMTZBKZCUMTZLTZACDTZBCDTZIZUKUNUOUQLTZCUMTUSULVCCUMABMNUKDEFUOUQCUKA
    EUHUIUJOZPUKBEUHUIUJUAZPUHUIUJUBZUCUDUKUSUTKZVAKZLTVBUKUPVGURVHLUKUHUJUPVGQ
    VDVFACDEFRSUKUIUJURVHQVEVFBCDEFRSUEUTVAMUFUG $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Polynomials with real coefficients - misc additions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    plyrecld.1 $e |- ( ph -> F e. ( Poly ` RR ) ) $.
    plyrecld.2 $e |- ( ph -> X e. RR ) $.
    $( Closure of a polynomial with real coefficients.  (Contributed by Thierry
       Arnoux, 18-Sep-2018.) $)
    plyrecld $p |- ( ph -> ( F ` X ) e. RR ) $=
      ( cr cres cfv wcel wceq fvres syl cply wf plyreres ffvelcdmd eqeltrrd ) A
      CBFGZHZCBHZFACFISTJECFBKLAFFCRABFMHIFFRNDBOLEPQ $.
  $}

  ${
    signsply0.d $e |- D = ( deg ` F ) $.
    signsply0.c $e |- C = ( coeff ` F ) $.
    signsply0.b $e |- B = ( C ` D ) $.

    ${
      $d k x C $.  $d k x D $.  $d k x F $.  $d x G $.
      signsplypnf.g $e |- G = ( x e. RR+ |-> ( x ^ D ) ) $.
      $( The quotient of a polynomial ` F ` by a monic monomial of same degree
         ` G ` converges to the highest coefficient of ` F ` .  (Contributed by
         Thierry Arnoux, 18-Sep-2018.) $)
      signsplypnf $p |- ( F e. ( Poly ` RR ) -> ( F oF / G ) ~~>r B ) $=
        ( vk cr wcel cdiv co crp cc0 cmpt cc cvv cply cfv cof cfzo cv cexp cmul
        csu csn caddc crli cfz plyf ffnd wral wfn ovex rgenw mp1i cnex a1i reex
        fnmpt rpssre ssexi wss wceq ax-resscn sstri sseqin2 coeid2 fvmpt2 mpan2
        cin mpbi adantl offval wa fzfid sselda cn0 dgrcl eqeltrid adantr expcld
        cdgr wf coef3 ad2antrr elfznn0 ffvelcdmd mulcld wne rpne0 nn0zd expne0d
        cz fsumdivc c0 c1 fzosn ineq2d fzodisj eqtr3di syl cun fzval3 cuz nn0uz
        eleqtrdi fzosplitsn eqtrd divcld fsumsplit mpteq2dva sumex cfn elfzonn0
        fzofi ovexd ad2antlr adantlr divassd fvexd wbr rlimconst cmin ccxp cneg
        sylancr zsubcld cxpexpzd oveq2d expnegd zcnd negsubdi2d breqtrd eqbrtrd
        nn0cnd nn0red 3eqtr2d expsubd clt elfzolt2 difrp biimpa syl21anc cxplim
        eqbrtrrd rlimmul mul01d fsumrlim wo olcd sumz fveq2 oveq2 oveq12d sumsn
        oveq1d syl2anc divcan4d rlimadd addlidd eqtr4di ) ELUAUBMZEFNUCOZAPQDUD
        OZKUEZCUBZAUEZUVIUFOZUGOZUVKDUFOZNOZKUHZDUIZUVOKUHZUJOZRZBUKUVFUVGAPQDU
        LOZUVMKUHZUVNNOZRUVTUVFASPUWBUVNNPEFTTUVFSSELEUMUNUVNTMZAPUOFPUPUVFUWDA
        PUVKDUFUQZURAPUVNFTJVCUSSTMUVFUTVAPTMUVFPLVBVDVEVAPSVFZSPVNPVGPLSVDVHVI
        ZPSVJVOCLKEDUVKHGVKUVKPMZUVKFUBUVNVGZUVFUWHUWDUWIUWEAPUVNTFJVLVMVPVQUVF
        APUWCUVSUVFUWHVRZUWCUWAUVOKUHUVSUWJUWAUVMUVNKUWJQDVSZUWJUVKDUVFPSUVKUWF
        UVFUWGVAVTZUVFDWAMZUWHUVFDEWFUBWAGLEWBWCZWDZWEZUWJUVIUWAMZVRZUVJUVLUWRW
        ASUVICUVFWASCWGZUWHUWQCLEHWHZWIUWQUVIWAMZUWJUVIDWJVPZWKUWRUVKUVIUWJUVKS
        MZUWQUWLWDZUXBWEWLZUWJUVKDUWLUWHUVKQWMZUVFUVKWNZVPZUVFDWQMZUWHUVFDUWNWO
        ZWDZWPZWRUWJUVHUVQUVOUWAKUWJUXIUVHUVQVNZWSVGUXKUXIUVHDDWTUJOZUDOZVNUXMW
        SUXIUXOUVQUVHDXAXBQDUXNXCXDXEUVFUWAUVHUVQXFZVGUWHUVFUWAQUXNUDOZUXPUVFUX
        IUWAUXQVGUXJQDXGXEUVFDQXHUBZMUXQUXPVGUVFDWAUXRUWNXIXJQDXKXEXLWDUWKUWRUV
        MUVNUXEUWJUVNSMZUWQUWPWDUWRUVKDUXDUWJUXFUWQUXHWDUWJUXIUWQUXKWDWPXMXNXLX
        OXLUVFUVTQDCUBZUJOZBUKUVFAPUVPUVRQUXTTUVPTMUWJUVHUVOKXPVAUVRTMUWJUVQUVO
        KXPVAUVFAPUVPRUVHQKUHZQUKUVFAPUVHUVOQKTPLVFZUVFVDVAUVHXQMZUVFQDXSVAZUVF
        UWHUVIUVHMZVRVRUVMUVNNXTUVFUYFVRZAPUVORAPUVJUVLUVNNOZUGOZRZQUKUYGAPUVOU
        YIUYGUWHVRZUVJUVLUVNUYKWASUVICUVFUWSUYFUWHUWTWIUYFUXAUVFUWHUVIDXRZYAZWK
        UYKUVKUVIUVFUWHUXCUYFUWLYBZUYMWEUVFUWHUXSUYFUWPYBUYKUVKDUYNUWHUXFUYGUXG
        VPZUVFUWHUXIUYFUXKYBZWPYCXOUYGUYJUVJQUGOQUKUYGAPUVJUYHUVJQTUYKUVICYDUYK
        UVLUVNNXTUYGUYCUVJSMAPUVJRUVJUKYEVDUYGWASUVICUVFUWSUYFUWTWDUYFUXAUVFUYL
        VPZWKZAPUVJYFYJUYGAPWTUVKDUVIYGOZYHOZNOZRZAPUYHRQUKUYGAPVUAUYHUYKVUAUVK
        UVIDYGOZUFOZUYHUYKVUAWTUVKUYSUFOZNOUVKUYSYIZUFOVUDUYKUYTVUEWTNUYKUVKUYS
        UYNUYOUYKDUVIUYPUYKUVIUYMWOZYKZYLYMUYKUVKUYSUYNUYOVUHYNUYKVUFVUCUVKUFUY
        KDUVIUYKDUYPYOUYKUVIUYMYSYPYMUUAUYKUVKUVIDUYNUYOUYPVUGUUBXLXOUYGUYSPMZV
        UBQUKYEUYGUVILMZDLMZUVIDUUCYEZVUIUYGUVIUYQYTUYGDUVFUWMUYFUWNWDYTUYFVULU
        VFUVIQDUUDVPVUJVUKVRVULVUIUVIDUUEUUFUUGUYSAUUHXEUUIUUJUYGUVJUYRUUKYQYRU
        ULUVFUVHUXRVFZUYDUUMUYBQVGUVFUYDVUMUYEUUNUVHKQUUOXEYQUVFAPUVRRAPUXTRZUX
        TUKUVFAPUVRUXTUWJUVRUXTUVNUGOZUVNNOZUXTUWJUWMVUPSMUVRVUPVGUWOUWJVUOUVNU
        WJUXTUVNUVFUXTSMZUWHUVFWASDCUWTUWNWKZWDZUWPWLUWPUXLXMUVOVUPKDWAUVIDVGZU
        VMVUOUVNNVUTUVJUXTUVLUVNUGUVIDCUUPUVIDUVKUFUUQUURUUTUUSUVAUWJUXTUVNVUSU
        WPUXLUVBXLXOUVFUYCVUQVUNUXTUKYEVDVURAPUXTYFYJYRUVCUVFUYAUXTBUVFUXTVURUV
        DIUVEYQYR $.
    $}

    ${
      $d d e f x B $.  $d d x z B $.  $d f C $.  $d d e f x D $.
      $d d e f x z F $.  $d d e f x z ph $.
      signsply0.a $e |- A = ( C ` 0 ) $.
      signsply0.1 $e |- ( ph -> F e. ( Poly ` RR ) ) $.
      signsply0.2 $e |- ( ph -> F =/= 0p ) $.
      signsply0.3 $e |- ( ph -> ( A x. B ) < 0 ) $.
      $( Lemma for the rule of signs, based on Bolzano's intermediate value
         theorem for polynomials :  If the lowest and highest coefficient ` A `
         and ` B ` are of opposite signs, the polynomial admits a positive
         root.  (Contributed by Thierry Arnoux, 19-Sep-2018.) $)
      signsply0 $p |- ( ph -> E. z e. RR+ ( F ` z ) = 0 ) $=
        ( crp wcel cc0 wa wbr clt vd vf vx ve cneg cv cfv wceq wrex cle cexp co
        cdiv cmin cabs wi wral simplr simpr rpxr xrleidd ad2antlr breq2d fveq2d
        oveq1d oveq12d fvoveq1d breq1d imbi12d rspcdv syl3c caddc cply ad2antrr
        id cr rpred plyrecld cn0 cdgr dgrcl syl eqeltrid reexpcld rpcnd expne0d
        rpne0d cz redivcld wf 0re syl2anc absdifltd cc recnd adantr wb rpexpcld
        wn 0red ltnled mpbird syldan cioo rpgt0d wss ax-resscn sstrdi ad3antrrr
        sylancr ad4antr sselda simplll a1i ffvelcdmd jca cpnf pnfge pnfxr ioorp
        cxr 0xr ssrexv 3syl mpd cmpt crli cvv rpssre eqidd eqbrtrrd mpbid ax-mp
        c1 cnex imbi2d rexralbidv r19.29a wne c0p nn0zd coef2 renegcld simplbda
        mpan2 ffvelcdmda negidd breqtrd ge0divd notbid 3bitr4d cicc ccncf plycn
        iccssre negelrp biimpa sylancl 0nn0 mul2lt0rlt0 breqtrdi breqtrrd ivth2
        coefv0 0le0 ioossioo mpanl12 sseqtrdi cico cof plyf ffnd wfn ovex rgenw
        eqid fnmpt mp1i sstri ssexi cin sseqin2 mpbi ovexd fvmptd oveq1 cbvmptv
        offval signsplypnf expcld divcld ralrimiva rlim3 icossioo mp4an sseqtri
        1red 0lt1 ralimi subidd simprbda gt0divd 3anassrs mul2lt0rgt0 eqbrtrrid
        w3a simpr1 eqbrtrd ivth wo dgreq0 necon3bid neeq1i sylibr rpneg biimprd
        orrd mpjaodan ) ADUEZOPZBUFGUGQUHZBOUIZDOPZAUXTRZUAUFZUBUFZUJSZUYFGUGZU
        YFFUKULZUMULZDUNULUOUGZUXSTSZUPZUBOUQZUYBUAOUYDUYEOPZRZUYNUYEGUGZQTSZUY
        BUYPUYNUYQUYEFUKULZUMULZDUNULUOUGZUXSTSZUYRUYPUYNRUYOUYNUYEUYEUJSZVUBUY
        DUYOUYNURUYPUYNUSUYOVUCUYDUYNUYOUYEUYEUTZVAZVBUYOUYMVUCVUBUPUBUYEOUYOVO
        ZUYOUYFUYEUHZRZUYGVUCUYLVUBVUHUYFUYEUYEUJUYOVUGUSZVCZVUHUYKVUAUXSTVUHUY
        JUYTDUOUNVUHUYHUYQUYIUYSUMVUHUYFUYEGVUIVDVUHUYFUYEFUKVUIVEVFVGZVHVIVJVK
        UYPVUBRZUYRUYTQTSZVULUYTDUXSVLULZQTUYPVUBDUXSUNULUYTTSUYTVUNTSUYPUYTDUX
        SUYPUYQUYSUYPGUYEAGVPVMUGPZUXTUYOLVNUYPUYEUYDUYOUSZVQZVRZUYPUYEFVUQAFVS
        PZUXTUYOAFGVTUGZVSHAVUOVUTVSPLVPGWAWBWCZVNWDUYPUYEFUYPUYEVUPWEUYPUYEVUP
        WGAFWHPZUXTUYOAFVVAUUAZVNZWFWIZADVPPZUXTUYOAVUOVUSVVFLVVAVUOVUSRDFEUGZV
        PJVUOVSVPFEVUOQVPPZVSVPEWJZWKEVPGIUUBZUUEUUFWCWLZVNZUYPDVVLUUCWMUUDUYPV
        UNQUHVUBUYPDADWNPZUXTUYOADVVKWOZVNUUGWPUUHUYPUYRVUMWQVUBUYPQUYQUJSZWSQU
        YTUJSZWSUYRVUMUYPVVOVVPUYPUYQUYSVURUYPUYEFVUPVVDWRUUIUUJUYPUYQQVURUYPWT
        ZXAUYPUYTQVVEVVQXAUUKWPXBXCUYPUYRRZUYABQUYEXDULZUIZUYBVVRUCQUYEWNQGBVVR
        WTZVVRUYEUYDUYOUYRURZVQZVWAVVRUYEVWBXEVVRQUYEUULULZVPWNVVRVVHUYEVPPZVWD
        VPXFZWKVWCQUYEUUOZXJZXGXHAGWNWNUUMULPZUXTUYOUYRAVUOVWILVPGUUNWBZXIVVRUC
        UFZVWDPZRGVWKAVUOUXTUYOUYRVWLLXKVVRVWDVPVWKVWHXLVRVVRUYRQQGUGZTSUYPUYRU
        SVVRQQEUGZVWMTVVRADQTSZQVWNTSAUXTUYOUYRXMZVVRVVFUXTVWOVVRAVVFVWPVVKWBUY
        DUXTUYOUYRAUXTUSZVNVVFUXTVWODUUPUUQWLAVWORQCVWNTACDACVWNVPKAVSVPQEAVUOV
        VHVVILWKVVJUURQVSPAUUSXNXOWCZVVKNUUTKUVAWLAVWMVWNUHZUXTUYOUYRAVUOVWSLEV
        PGIUVDWBZXIUVBXPUVCVVRUYOVVSOXFZVVTUYBUPZVWBUYOVVSQXQXDULZOUYOQQUJSZUYE
        XQUJSZVVSVXCXFZUVEUYOUYEYAPVXEVUDUYEXRWBQYAPZXQYAPZVXDVXERVXFYBXSQXQQUY
        EUVFUVGXJXTUVHZUYABVVSOYCZYDYEXCUYDUYGUYKUDUFZTSZUPZUBOUQZUAOUIZUDOUQZU
        YNUAOUIZAVXPUXTAVXNUAYNXQUVIULZUIZUDOUQZVXPAUBOUYJYFZDYGSVXTAGUCOVWKFUK
        ULZYFZUMUVJULZVYADYGAUBWNOUYHUYIUMOGVYCYHYHAWNWNGAVUOWNWNGWJZLVPGUVKWBZ
        UVLVYBYHPZUCOUQVYCOUVMAVYGUCOVWKFUKUVNUVOUCOVYBVYCYHVYCUVPUVQUVRWNYHPAY
        OXNOYHPAOWNYOOVPWNYIXGUVSZUVTXNOWNXFWNOUWAOUHVYHOWNUWBUWCAUYFWNPRUYHYJA
        UYFOPZRZUCUYFVYBUYIOVYCYHVYJVYCYJVYJVWKUYFUHZRVWKUYFFUKVYJVYKUSVEAVYIUS
        ZVYJUYFFUKUWDUWEUWHAVUOVYDDYGSLUBDEFGVYCHIJUCUBOVYBUYIVWKUYFFUKUWFUWGUW
        IWBYKAUDUAUBOUYJDYNAUYJWNPUBOVYJUYHUYIVYJWNWNUYFGAVYEVYIVYFWPVYJUYFVYLW
        EZXOVYJUYFFVYMAVUSVYIVVAWPUWJVYJUYFFVYMVYJUYFVYLWGAVVBVYIVVCWPWFUWKUWLO
        VPXFZAYIXNVVNAUWQUWMYLVXSVXOUDOVXROXFVXSVXOUPVXRVXCOVXGVXHQYNTSXQXQUJSZ
        VXRVXCXFYBXSUWRVXHVYOXSXQXRYMQXQYNXQUWNUWOXTUWPVXNUAVXROYCYMUWSWBZWPUYD
        VXOVXQUDUXSOVWQUYDVXKUXSUHZRZVXMUYMUAUBOOVYRVXLUYLUYGVYRVXKUXSUYKTUYDVY
        QUSVCYPYQVJYEYRAUYCRZUYGUYKDTSZUPZUBOUQZUYBUAOVYSUYORZWUBQUYQTSZUYBWUCW
        UBVUADTSZWUDWUCWUBRUYOWUBVUCWUEVYSUYOWUBURWUCWUBUSUYOVUCVYSWUBVUEVBUYOW
        UAVUCWUEUPUBUYEOVUFVUHUYGVUCVYTWUEVUJVUHUYKVUADTVUKVHVIVJVKWUCWUERZWUDQ
        UYTTSZWUFDDUNULZQUYTTWUCWUHQUHWUEWUCDAVVMUYCUYOVVNVNUWTWPWUCWUEWUHUYTTS
        UYTDDVLULTSWUCUYTDDWUCUYQUYSWUCGUYEAVUOUYCUYOLVNVYSOVPUYEVYNVYSYIXNXLZV
        RZWUCUYEFWUIAVUSUYCUYOVVAVNWDWUCUYEFWUCUYEWUIWOWUCUYEVYSUYOUSZWGAVVBUYC
        UYOVVCVNZWFWIAVVFUYCUYOVVKVNZWUMWMUXAYKWUCWUDWUGWQWUEWUCUYQUYSWUJWUCUYE
        FWUKWULWRUXBWPXBXCWUCWUDRZVVTUYBWUNUCQUYEWNQGBWUNWTZWUNUYEVYSUYOWUDURZV
        QZWUOWUNUYEWUPXEWUNVWDVPWNWUNVVHVWEVWFWKWUQVWGXJZXGXHAVWIUYCUYOWUDVWJXI
        WUNVWLRGVWKAVUOUYCUYOWUDVWLLXKWUNVWDVPVWKWURXLVRWUNVWMQTSWUDWUNVWMVWNQT
        AVWSUYCUYOWUDVWTXIWUNVWNCQTKWUNAQDTSZCQTSAUYCUYOWUDXMAUYCUYOWUDWUSAUYCU
        YOWUDUXFRDAUYCUYOWUDUXGXEUXCACDVWRVVKNUXDWLUXEUXHWUCWUDUSXPUXIWUNUYOVXA
        VXBWUPVXIVXJYDYEXCVYSVXPWUBUAOUIZAVXPUYCVYPWPVYSVXOWUTUDDOAUYCUSVYSVXKD
        UHZRZVXMWUAUAUBOOWVBVXLVYTUYGWVBVXKDUYKTVYSWVAUSVCYPYQVJYEYRAVVFDQYSZUX
        TUYCUXJVVKAVVGQYSZWVCAGYTYSWVDMAGYTVVGQAVUOGYTUHVVGQUHWQLEVPGFHIUXKWBUX
        LYLDVVGQJUXMUXNVVFWVCRZUXTUYCWVEUYCUXTWSDUXOUXPUXQWLUXR $.
    $}
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Descartes's rule of signs
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Sign changes in a word over real numbers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    signsw.p $e |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 }
      |-> if ( b = 0 , a , b ) ) $.

    ${
      $d a b X $.  $d a b Y $.
      $( The value of the skipping 0 sign operation.  (Contributed by Thierry
         Arnoux, 9-Sep-2018.) $)
      signspval $p |- ( ( X e. { -u 1 , 0 , 1 } /\ Y e. { -u 1 , 0 , 1 } )
        -> ( X .+^ Y ) = if ( Y = 0 , X , Y ) ) $=
        ( c1 cneg cc0 ctp wcel wceq cif co ifcl cv ifeq1 eqeq1 id ifbieq2d
        ovmpog mpd3an3 ) BGHIGJZKCUCKCILZBCMZUCKBCANUELUDBCUCODEBCUCUCEPZILZDPZ
        UFMUEAUGBUFMUCUGUHBUFQUFCLZUGUDUFCBUFCIRUISTFUAUB $.
    $}

    ${
      $d a b u $.
      $( Neutral element property of ` .+^ ` .  (Contributed by Thierry Arnoux,
         9-Sep-2018.) $)
      signsw0glem $p |-
        A. u e. { -u 1 , 0 , 1 } ( ( 0 .+^ u ) = u /\ ( u .+^ 0 ) = u ) $=
        ( cc0 cv co wceq wa cneg ctp wcel cif c0ex tpid2 signspval mpan eqtrdi
        c1 iftrue id eqtr4d iffalse pm2.61i mpan2 eqid iftruei jca rgen ) FAGZB
        HZUKIZUKFBHZUKIZJATKZFTLZUKUQMZUMUOURULUKFIZFUKNZUKFUQMZURULUTIUPFTOPZB
        FUKCDEQRUSUTUKIUSUTFUKUSFUKUAUSUBUCUSFUKUDUESURUNFFIZUKFNZUKURVAUNVDIVB
        BUKFCDEQUFVCUKFFUGUHSUIUJ $.
    $}

    signsw.w $e |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. ,
      <. ( +g ` ndx ) , .+^ >. } $.
    $( The base of ` W ` is the unordered triple reprensenting the possible
       signs.  (Contributed by Thierry Arnoux, 9-Sep-2018.) $)
    signswbase $p |- { -u 1 , 0 , 1 } = ( Base ` W ) $=
      ( c1 cneg cc0 ctp cvv wcel cbs cfv wceq tpex grpbase ax-mp ) GHZIGJZKLTBM
      NOSIGPTABKFQR $.

    ${
      $d a b $.
      $( The operation of ` W ` .  (Contributed by Thierry Arnoux,
         9-Sep-2018.) $)
      signswplusg $p |- .+^ = ( +g ` W ) $=
        ( cvv wcel cplusg cfv wceq c1 cneg cc0 ctp cv cif cmpo tpex mpoex ax-mp
        eqeltri grpplusg ) AGHABIJKACDLMZNLOZUEDPZNKCPUFQZRGECDUEUEUGUDNLSZUHTU
        BUEABGFUCUA $.

      $d a b u $.  $d e u .+^ $.  $d e u W $.
      $( The neutral element of ` W ` .  (Contributed by Thierry Arnoux,
         9-Sep-2018.) $)
      signsw0g $p |- 0 = ( 0g ` W ) $=
        ( vu ve c0g cfv cc0 c1 cneg ctp cv co wceq wa wral wtru wcel c0ex tpid2
        signsw0glem pm3.2i wb signswbase eqid signswplusg wrex oveq1 ovanraleqv
        eqeq1d rspcev mp2an a1i ismgmid mptru mpbi eqcomi ) BIJZKKLMZKLNZUAZKGO
        ZAPZVEQZVEKAPVEQRGVCSZRZVAKQZVDVHVBKLUBUCZGACDEUDZUEVIVJUFTGVCAKHBVAABC
        DEFUGVAUHABCDEFUIHOZVEAPZVEQZVEVMAPVEQRGVCSZHVCUJZTVDVHVQVKVLVPVHHKVCVO
        VGGVEVMVEAVCKVMKQVNVFVEVMKVEAUKUMULUNUOUPUQURUSUT $.

      $d a b e u v w .+^ $.  $d e u v w W $.
      $( ` W ` is a monoid structure on ` { -u 1 , 0 , 1 } ` which operation
         retains the right side, but skips zeroes.  This will be used for
         skipping zeroes when counting sign changes.  (Contributed by Thierry
         Arnoux, 9-Sep-2018.) $)
      signswmnd $p |- W e. Mnd $=
        ( vu vv vw ve wcel cv co cc0 wceq wral wa cif sylan9eq ad2antrr cmnd c1
        cneg ctp wrex signspval eqeltrd w3a stoic3 iftrue adantr 3adant3 adantl
        ifcl 3eqtrd simp1 3adant1 simpl2 wn simpl3 ifclda syl2anc iftrued eqtrd
        id eqtr4d ad2antlr iffalse simpr eqeq1d mtbird iffalsed pm2.61dan 3expa
        ralrimiva jca rgen2 c0ex tpid2 signsw0glem ovanraleqv rspcev signswbase
        oveq1 mp2an signswplusg ismnd mpbir2an ) BUAKGLZHLZAMZUBUCZNUBUDZKZWKIL
        ZAMZWIWJWOAMZAMZOZIWMPZQZHWMPGWMPJLZWIAMZWIOZWIXBAMWIOQGWMPZJWMUEZXAGHW
        MWMWIWMKZWJWMKZQZWNWTXIWKWJNOZWIWJRZWMAWIWJCDEUFZXJWIWJWMUNUGZXIWSIWMXG
        XHWOWMKZWSXGXHXNUHZWONOZWSXOXPQZXJWSXQXJQZWPWIWRXRWPWKXKWIXQWPWKOXJXOXP
        WPXPWKWORZWKXGXHWNXNWPXSOZXMAWKWOCDEUFUIZXPWKWOUJZSUKXOWKXKOZXPXJXGXHYC
        XNXLULZTXJXKWIOXQXJWIWJUJUMUOXRWRWQNOZWIWQRZWIXOWRYFOZXPXJXOXGWQWMKYGXG
        XHXNUPXOWQXPWJWORZWMXHXNWQYHOZXGAWJWOCDEUFUQZXOXPWJWOWMXGXHXNXPURXGXHXN
        XPUSZUTVAUGAWIWQCDEUFVBZTXRYEWIWQXQXJWQWJNXOXPWQYHWJYJXPWJWOUJZSXJVESVC
        VDVFXQXJUSZQZWPWJWRYOWPXSWKWJXOXTXPYNYATXPXSWKOXOYNYBVGYOWKXKWJXOYCXPYN
        YDTYNXKWJOXQXJWIWJVHUMVDUOYOWRYFWQWJXOYGXPYNYLTYOYEWIWQYOYEXJXQYNVIYOWQ
        WJNYOWQYHWJXOYIXPYNYJTXPYHWJOXOYNYMVGVDZVJVKVLYPUOVFVMXOYKQZWPWOWRXOYKW
        PXSWOYAXPWKWOVHSYQWRYFWQWOXOYGYKYLUKYQYEWIWQYQYEXPXOYKVIYQWQWONXOYKWQYH
        WOYJXPWJWOVHSZVJVKVLYRUOVFVMVNVOVPVQNWMKNWIAMZWIOZWINAMWIOQGWMPZXFWLNUB
        VRVSGACDEVTXEUUAJNWMXDYTGWIXBWIAWMNXBNOXCYSWIXBNWIAWDVJWAWBWEWMAJBGHIAB
        CDEFWCABCDEFWFWGWH $.
    $}

    $d a b X $.
    $( The zero-skipping operation propagates nonzeros.  (Contributed by
       Thierry Arnoux, 11-Oct-2018.) $)
    signswrid $p |- ( X e. { -u 1 , 0 , 1 } -> ( X .+^ 0 ) = X ) $=
      ( c1 cneg cc0 ctp wcel co wceq cif c0ex tpid2 signspval mpan2 eqid iftrue
      mp1i eqtrd ) CHIZJHKZLZCJAMZJJNZCJOZCUFJUELUGUINUDJHPQACJDEFRSUHUICNUFJTU
      HCJUAUBUC $.

    $d a b Y $.
    $( The zero-skipping operation keeps nonzeros.  (Contributed by Thierry
       Arnoux, 12-Oct-2018.) $)
    signswlid $p |- ( ( ( X e. { -u 1 , 0 , 1 } /\ Y e. { -u 1 , 0 , 1 } )
      /\ Y =/= 0 ) -> ( X .+^ Y ) = Y ) $=
      ( c1 cneg cc0 ctp wcel wa wne co wceq cif signspval adantr simpr iffalsed
      neneqd eqtrd ) CIJKILZMDUEMNZDKOZNZCDAPZDKQZCDRZDUFUIUKQUGACDEFGSTUHUJCDU
      HDKUFUGUAUCUBUD $.

    $( The zero-skipping operation propagates nonzeros.  (Contributed by
       Thierry Arnoux, 11-Oct-2018.) $)
    signswn0 $p |- ( ( ( X e. { -u 1 , 0 , 1 } /\ Y e. { -u 1 , 0 , 1 } )
      /\ X =/= 0 ) -> ( X .+^ Y ) =/= 0 ) $=
      ( c1 cneg cc0 ctp wcel wa wne co wceq cif signspval neeq1 adantr wn simpr
      simplr neqned ifbothda eqnetrd ) CIJKILZMDUHMNZCKOZNZCDAPZDKQZCDRZKUIULUN
      QUJACDEFGSUAUMUJDKOUNKOUKCDCUNKTDUNKTUIUJUMUDUKUMUBZNDKUKUOUCUEUFUG $.

    $( The zero-skipping operation changes value when the operands change
       signs.  (Contributed by Thierry Arnoux, 9-Oct-2018.) $)
    signswch $p |- ( ( X e. { -u 1 , 1 } /\ Y e. { -u 1 , 0 , 1 } )
      -> ( ( X .+^ Y ) =/= X <-> ( X x. Y ) < 0 ) ) $=
      ( c1 wcel cc0 wa co wne wceq cmul clt wbr wb breq1d cpr ctp cif csn df-pr
      cneg cun snsstp1 snsstp3 unssi eqsstri sseli signspval sylan neeq1d neeq1
      bibi1d wn neirr a1i 0re ltnri simpr oveq2d wss neg1cn ax-1cn prssi simpll
      cc mp2an sselid mul01d eqtrd mtbiri 2falsed simplr tpcomb eleqtrdi neqned
      jca cdif eldifsn neg1ne0 ax-1ne0 diftpsn3 eleq2i bitr3i sylib 0le1 lenlti
      cle 1re mpbi neg1mulneg1e1 breq1i mtbir 2false oveq2 mpbiri adantl neg1rr
      bibi12d neg1lt0 0lt1 lttri gtneii mulridi 2th elpri mpjaodan adantr neeq2
      eqbrtri oveq1 mpbird necomi mulcomi wo ad2antrr ifbothda bitrd ) CIUFZIUA
      ZJZDYCKIUBZJZLZCDAMZCNDKOZCDUCZCNZCDPMZKQRZYHYIYKCYECYFJYGYIYKOYDYFCYDYCU
      DZIUDZUGYFYCIUEYOYPYFYCKIUHYCKIUIUJUKULACDEFGUMUNUOYJCCNZYNSDCNZYNSZYLYNS
      YHCDCYKOYQYLYNCYKCUPUQDYKOYRYLYNDYKCUPUQYHYJLZYQYNYQURYTCUSUTYTYNKKQRKVAV
      BYTYMKKQYTYMCKPMKYTDKCPYHYJVCVDYTCYTYDVJCYCVJJIVJJYDVJVEVFVGYCIVJVHVKYEYG
      YJVIVLVMVNTVOVPYHYJURZLZCYCOZYSCIOZUUBDYDJZUUCYSUUBDYCIKUBZJZDKNZLZUUEUUB
      UUGUUHUUBDYFUUFYEYGUUAVQYCKIVRVSUUBDKYHUUAVCVTWAUUIDUUFKUDWBZJUUEDUUFKWCU
      UJYDDYCKNIKNUUJYDOWDWEYCIKWFVKWGWHWIZUUEUUCLYSDYCNZYCDPMZKQRZSZUUEUUOUUCU
      UEDYCOZUUODIOZUUPUUOUUEUUPUUOYCYCNZYCYCPMZKQRZSUURUUTYCUSUUTIKQRZKIWLRUVA
      URWJKIVAWMWKWNZUUSIKQWOWPWQWRUUPUULUURUUNUUTDYCYCUPUUPUUMUUSKQDYCYCPWSTXC
      WTXAUUQUUOUUEUUQUUOIYCNZYCIPMZKQRZSUVCUVEYCIXBYCKQRKIQRYCIQRXDXEYCKIXBVAW
      MXFVKXGZUVDYCKQYCVFXHXDXNZXIUUQUULUVCUUNUVEDIYCUPUUQUUMUVDKQDIYCPWSTXCWTX
      ADYCIXJZXKXLUUCYSUUOSUUEUUCYRUULYNUUNCYCDXMUUCYMUUMKQCYCDPXOTXCXAXPUNUUBU
      UEUUDYSUUKUUEUUDLYSDINZIDPMZKQRZSZUUEUVLUUDUUEUUPUVLUUQUUPUVLUUEUUPUVLYCI
      NZIYCPMZKQRZSUVMUVOIYCUVFXQUVEUVOUVGUVDUVNKQYCIVFVGXRWPWNXIUUPUVIUVMUVKUV
      ODYCIUPUUPUVJUVNKQDYCIPWSTXCWTXAUUQUVLUUEUUQUVLIINZIIPMZKQRZSUVPUVRIUSUVR
      UVAUVBUVQIKQIVGXHWPWQWRUUQUVIUVPUVKUVRDIIUPUUQUVJUVQKQDIIPWSTXCWTXAUVHXKX
      LUUDYSUVLSUUEUUDYRUVIYNUVKCIDXMUUDYMUVJKQCIDPXOTXCXAXPUNYEUUCUUDXSYGUUACY
      CIXJXTXKYAYB $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Counting sign changes in a word over real numbers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    signslema.1 $e |- ( ph -> E e. NN0 ) $.
    signslema.2 $e |- ( ph -> F e. NN0 ) $.
    signslema.3 $e |- ( ph -> G e. NN0 ) $.
    signslema.4 $e |- ( ph -> H e. NN0 ) $.
    signslema.5 $e |- ( ph -> ( E < G /\ -. 2 || ( G - E ) ) ) $.
    signslema.6 $e |- ( ph -> ( ( H - G ) - ( F - E ) ) e. { 0 , 2 } ) $.
    $( Computational part of ~~? signwlemn .  (Contributed by Thierry Arnoux,
       29-Sep-2018.) $)
    signslema $p |- ( ph -> ( F < H /\ -. 2 || ( H - F ) ) ) $=
      ( clt wbr c2 cmin co cdvds cc0 adantr wcel wn wceq simpld nn0cnd subeq0ad
      wa subcld biimpa breq2d wb nn0red posdifd 3bitr4rd mpbid 0red cr resubcld
      2pos breq2 mpbiri biimpar sylan2 lttrd mpbird wo sub4d eqeltrrd ovex elpr
      cpr sylib mpjaodan simprd mtbird caddc cz 2z nn0zd zsubcld dvdsaddr mtbid
      sylancr 2cnd subaddd jca ) ACELMZNECOPZQMZUAZAWGDBOPZOPZRUBZWFWKNUBZAWLUF
      ZBDLMZWFAWOWLAWONWJQMZUAZJUCZSWNRWGLMZRWJLMZWFWOWNWGWJRLAWLWGWJUBAWGWJAEC
      AEIUDZACGUDZUGZADBADHUDZABFUDZUGZUEUHZUIAWFWSUJZWLACEACGUKZAEIUKZULZSAWOW
      TUJZWLABDABFUKZADHUKZULZSUMUNAWMUFZWFWSXPRWJWGXPUOAWJUPTWMADBXNXMUQZSAWGU
      PTWMAECXJXIUQZSXPWOWTAWOWMWRSAXLWMXOSUNWMARWKLMZWJWGLMZWMXSRNLMURWKNRLUSU
      TAXTXSAWJWGXQXRULVAVBVCAXHWMXKSVDAWKRNVJZTWLWMVEAEDOPCBOPOPWKYAAEDCBXAXDX
      BXEVFKVGWKRNWGWJOVHVIVKZVLAWLWIWMWNWHWPAWQWLAWOWQJVMZSWNWGWJNQXGUIVNXPNWJ
      NVOPZQMZWHAYEUAWMAWPYEYCANVPTWJVPTWPYEUJVQADBADHVRABFVRVSNWJVTWBWASXPYDWG
      NQAWMYDWGUBAWGWJNXCXFAWCWDUHUIWAYBVLWE $.
  $}

  ${
    signsv.p $e |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 }
      |-> if ( b = 0 , a , b ) ) $.
    signsv.w $e |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. ,
      <. ( +g ` ndx ) , .+^ >. } $.
    signsv.t $e |- T = ( f e. Word RR |-> ( n e. ( 0 ..^ ( # ` f ) ) |->
      ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( f ` i ) ) ) ) ) ) $.
    signsv.v $e |- V = ( f e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` f ) )
      if ( ( ( T ` f ) ` j ) =/= ( ( T ` f ) ` ( j - 1 ) ) , 1 , 0 ) ) $.

    ${
      $d f i n F $.  $d f W $.
      $( Value of the zero-skipping sign word.  (Contributed by Thierry Arnoux,
         8-Oct-2018.) $)
      signstfv $p |- ( F e. Word RR -> ( T ` F ) = ( n e. ( 0 ..^ ( # ` F ) )
        |-> ( W gsum ( i e. ( 0 ... n ) |-> ( sgn ` ( F ` i ) ) ) ) ) ) $=
        ( cc0 cfv cfzo co cmpt cv chash cfz csgn cgsu cr cword wceq oveq2d wcel
        fveq2 wa simpl fveq1d fveq2d mpteq2dva mpteq12dv ovex mptex fvmpt ) CGF
        PCUAZUBQZRSZIDPFUAUCSZDUAZVAQZUDQZTZUESZTFPGUBQZRSZIDVDVEGQZUDQZTZUESZT
        UFUGBVAGUHZFVCVIVKVOVPVBVJPRVAGUBUKUIVPVHVNIUEVPDVDVGVMVPVEVDUJZULZVFVL
        UDVRVEVAGVPVQUMUNUOUPUIUQNFVKVOPVJRURUSUT $.
    $}

    ${
      $d f i n F $.  $d i n N $.  $d f n W $.
      $( Value of the zero-skipping sign word.  (Contributed by Thierry Arnoux,
         8-Oct-2018.) $)
      signstfval $p |- ( ( F e. Word RR /\ N e. ( 0 ..^ ( # ` F ) ) )
        -> ( ( T ` F ) ` N )
           = ( W gsum ( i e. ( 0 ... N ) |-> ( sgn ` ( F ` i ) ) ) ) ) $=
        ( cc0 cfv co cgsu cr cword wcel chash cfzo wa cv cfz csgn cmpt cvv wceq
        signstfv adantr simpr oveq2d mpteq1d ovexd fvmptd ) GUAUBUCZHQGUDRUESZU
        CZUFZFHJDQFUGZUHSZDUGGRUIRZUJZTSZJDQHUHSZVFUJZTSVAGBRZUKUTVKFVAVHUJULVB
        ABCDEFGIJKLMNOPUMUNVCVDHULZUFZVGVJJTVMDVEVIVFVMVDHQUHVCVLUOUPUQUPUTVBUO
        VCJVJTURUS $.
    $}

    ${
      $d a b .+^ $.  $d f i n F $.  $d i n N $.  $d f i n W $.
      $( Closure of the zero skipping sign word.  (Contributed by Thierry
         Arnoux, 9-Oct-2018.) $)
      signstcl $p |- ( ( F e. Word RR /\ N e. ( 0 ..^ ( # ` F ) ) )
        -> ( ( T ` F ) ` N ) e. { -u 1 , 0 , 1 } ) $=
        ( cr wcel cc0 cfv cword chash cfzo co wa cfz cv csgn cmpt cgsu cneg ctp
        c1 signstfval signswbase cmnd signswmnd a1i cuz wss cn0 fzo0ssnn0 nn0uz
        sseqtri sselda cxr wf ad2antrr fzssfzo adantl ffvelcdmd rexrd sgncl syl
        wrdf gsumncl eqeltrd ) GQUARZHSGUBTZUCUDZRZUEZHGBTTJDSHUFUDZDUGZGTZUHTZ
        UIUJUDUMUKSUMULZABCDEFGHIJKLMNOPUNWBWFHDWGJSAJKLMNUOJUPRWBAJKLMNUQURVRV
        TSUSTZHVTWHUTVRVTVAWHVSVBVCVDURVEWBWDWCRZUEZWEVFRWFWGRWJWEWJVTQWDGVRVTQ
        GVGWAWIQGVOVHWBWCVTWDWAWCVTUTVRHSVSVIVJVEVKVLWEVMVNVPVQ $.

      $( The zero skipping sign word is a word.  (Contributed by Thierry
         Arnoux, 8-Oct-2018.) $)
      signstf $p |- ( F e. Word RR -> ( T ` F ) e. Word RR ) $=
        ( cr wcel cc0 cfv c1 cword chash cfzo co wf cfz csgn cmpt cgsu signstfv
        cv wa cneg ctp wss neg1rr 0re 1re tpssi mp3an signswbase cmnd signswmnd
        a1i cuz cn0 fzo0ssnn0 nn0uz sseqtri sselda wrdf ad2antrr fzssfzo adantl
        cxr ffvelcdmd rexrd sgncl syl gsumncl sselid fmpt3d iswrdi ) GPUAZQZRGU
        BSZUCUDZPGBSZUEWHWDQWEFWGIDRFUKZUFUDZDUKZGSZUGSZUHUIUDZPWHABCDEFGHIJKLM
        NOUJWEWIWGQZULZTUMZRTUNZPWNWQPQRPQTPQWRPUOUPUQURWQRTPUSUTWPWMWIDWRIRAIJ
        KLMVAIVBQWPAIJKLMVCVDWEWGRVESZWIWGWSUOWEWGVFWSWFVGVHVIVDVJWPWKWJQZULZWL
        VOQWMWRQXAWLXAWGPWKGWEWGPGUEWOWTPGVKVLWPWJWGWKWOWJWGUOWEWIRWFVMVNVJVPVQ
        WLVRVSVTWAWBPWFWHWCVS $.

      $( Length of the zero skipping sign word.  (Contributed by Thierry
         Arnoux, 8-Oct-2018.) $)
      signstlen $p |- ( F e. Word RR -> ( # ` ( T ` F ) ) = ( # ` F ) ) $=
        ( cr wcel cfv chash co cword cc0 cfzo wfn wceq csgn cmpt cgsu ovex eqid
        cfz fnmpti signstfv fneq1d mpbiri hashfn syl cn0 lencl hashfzo0 eqtrd
        cv ) GPUAQZGBRZSRZUBGSRZUCTZSRZVFVCVDVGUDZVEVHUEVCVIFVGIDUBFVBUKTDVBGRU
        FRUGZUHTZUGZVGUDFVGVKVLIVJUHUIVLUJULVCVGVDVLABCDEFGHIJKLMNOUMUNUOVGVDUP
        UQVCVFURQVHVFUEPGUSVFUTUQVA $.

      $d f i n K $.
      $( Sign of a single letter word.  (Contributed by Thierry Arnoux,
         8-Oct-2018.) $)
      signstf0 $p |- ( K e. RR -> ( T ` <" K "> ) = <" ( sgn ` K ) "> ) $=
        ( cr wcel cc0 cfv wceq cs1 chash cfzo co cv cfz csgn cmpt cgsu c1 s1len
        csn oveq2i fzo01 eqtri a1i wa simpr eleqtrdi velsn sylib oveq2 cz ax-mp
        0z fzsn eqtrdi mpteq1d oveq2d adantl cmnd cneg ctp signswmnd 0re cxr id
        s1fv eqeltrd rexrd sgncl signswbase 2fveq3 gsumsn syl3anc adantr fveq2d
        syl 3eqtrd syldan mpteq12dva cword s1cl signstfv sgnclre fmptsn sylancr
        cop s1val eqtrd 3eqtr4d ) GPQZFRGUAZUBSZUCUDZIDRFUEZUFUDZDUEZXCSUGSZUHZ
        UIUDZUHZFRULZGUGSZUHZXCBSZXNUAZXBFXEXKXMXNXEXMTXBXERUJUCUDXMXDUJRUCGUKU
        MUNUOZUPXBXFXEQZXFRTZXKXNTXBXSUQZXFXMQXTYAXFXEXMXBXSURXRUSFRUTVAXBXTUQX
        KIDXMXIUHZUIUDZRXCSZUGSZXNXTXKYCTXBXTXJYBIUIXTDXGXMXIXTXGRRUFUDZXMXFRRU
        FVBRVCQYFXMTVERVFVDVGVHVIVJXBYCYETZXTXBIVKQZRPQZYEUJVLRUJVMZQZYGYHXBAIJ
        KLMVNUPYIXBVOUPXBYDVPQYKXBYDXBYDGPGPVRZXBVQVSVTYDWAWHXIYJYEDIRPAIJKLMWB
        XHRUGXCWCWDWEWFXBYEXNTXTXBYDGUGYLWGWFWIWJWKXBXCPWLQXPXLTGPWMABCDEFXCHIJ
        KLMNOWNWHXBXQRXNWRULZXOXBXNPQZXQYMTGWOZXNPWSWHXBYIYNYMXOTVOYOFRXNPPWPWQ
        WTXA $.
    $}

    $d a b .+^ $.  $d f i n F $.  $d f i n K $.  $d f i n W $.
    $( Zero-skipping sign in a word compared to a shorter word.  (Contributed
       by Thierry Arnoux, 8-Oct-2018.) $)
    signstfvn $p |- ( ( F e. ( Word RR \ { (/) } ) /\ K e. RR )
      -> ( ( T ` ( F ++ <" K "> ) ) ` ( # ` F ) )
        = ( ( ( T ` F ) ` ( ( # ` F ) - 1 ) ) .+^ ( sgn ` K ) ) ) $=
      ( cr wcel cc0 co cword c0 csn cdif wa chash cfv cfz cs1 cconcat csgn cmpt
      cv cgsu c1 cmin caddc cneg ctp signswbase signswmnd a1i cn0 cuz cn eldifi
      cmnd wne lencl syl eldifsn hasheq0 necon3bid biimpar sylbi elnnne0 adantr
      sylanbrc nnm1nn0 nn0uz eleqtrdi cxr cfzo wf ccatws1cl wrdf wceq cz fzoval
      nn0zd fzossfz eqsstrrdi s1cl ccatlen sylan2 oveq2i eqtrdi oveq2d peano2zd
      s1len nn0cnd 1cnd pncand 3eqtrd sseqtrrd sselda sylanl1 rexrd signswplusg
      ffvelcdmd sgncl rexr adantl id npcand sylan9eqr ccatws1ls eqtrd gsumnunsn
      fveq2d mpteq1d simpll ad2antlr eleq2d ccatval1 syl3anc mpteq2dva sylan wo
      oveq1d 3eqtr3d eqid olci wb fzosplitsni mpbiri signstfval syl2anc fzo0end
      eleqtrrd 3eqtr4d ) GQUAZUBUCZUDRZHQRZUEZJDSGUFUGZUHTZDUMZGHUIZUJTZUGZUKUG
      ZULZUNTZJDSUUGUOUPTZUHTZUUIGUGZUKUGZULZUNTZHUKUGZATZUUGUUKBUGUGZUUPGBUGUG
      ZUVBATUUFJDSUUPUOUQTZUHTZUUMULZUNTJDUUQUUMULZUNTZUVBATUUOUVCUUFUUMUVBUUPA
      DUOURSUOUSZJSAJKLMNUTJVGRUUFAJKLMNVAVBUUFUUPVCSVDUGZUUFUUGVERZUUPVCRUUDUV
      MUUEUUDUUGVCRZUUGSVHZUVMUUDGUUBRZUVNGUUBUUCVFZQGVIZVJUUDUVPGUBVHZUEUVOGUU
      BUBVKUVPUVOUVSUVPUUGSGUBGUUBVLVMVNVOUUGVPVRZVQUUGVSVJVTWAUUFUUIUUQRZUEZUU
      LWBRUUMUVKRUWBUULUUDUVPUUEUWAUULQRUVQUVPUUEUEZUWAUEZSUUKUFUGZWCTZQUUIUUKU
      WDUUKUUBRZUWFQUUKWDUWCUWGUWAQGHWEZVQQUUKWFVJUWCUUQUWFUUIUWCUUQUUHUWFUWCUU
      QSUUGWCTZUUHUVPUWIUUQWGZUUEUVPUUGWHRZUWJUVPUUGUVRWJZSUUGWIVJVQZSUUGWKWLUW
      CUWFSUUGUOUQTZWCTZSUWNUOUPTZUHTZUUHUWCUWEUWNSWCUWCUWEUUGUUJUFUGZUQTZUWNUU
      EUVPUUJUUBRZUWEUWSWGHQWMZQQGUUJWNWOUWRUOUUGUQHWTWPWQWRZUWCUWNWHRUWOUWQWGU
      WCUUGUVPUWKUUEUWLVQWSSUWNWIVJUWCUWPUUGSUHUVPUWPUUGWGUUEUVPUUGUOUVPUUGUVRX
      AZUVPXBZXCVQWRXDXEXFXJXGXHUULXKVJAJKLMNXIUUEUVBUVKRZUUDUUEHWBRUXEHXLHXKVJ
      XMUUFUUIUVFWGZUEUULHUKUUDUVPUUEUXFUULHWGUVQUWCUXFUEZUULUUGUUKUGZHUXGUUIUU
      GUUKUXFUWCUUIUVFUUGUXFXNUVPUVFUUGWGZUUEUVPUUGUOUXCUXDXOZVQXPXTUWCUXHHWGUX
      FQGHXQVQXRXGXTXSUUFUVHUUNJUNUUFDUVGUUHUUMUUFUVFUUGSUHUUDUXIUUEUUDUVPUXIUV
      QUXJVJVQWRYAWRUUFUVJUVAUVBAUUFUVIUUTJUNUUDUVPUUEUVIUUTWGUVQUWCDUUQUUMUUSU
      WDUULUURUKUWDUVPUWTUUIUWIRZUULUURWGUVPUUEUWAYBUUEUWTUVPUWAUXAYCUWCUXKUWAU
      WCUWIUUQUUIUWMYDVNQQGUUJUUIYEYFXTYGYHWRYJYKUUDUVPUUEUVDUUOWGZUVQUWCUWGUUG
      UWFRUXLUWHUWCUUGUWOUWFUVPUUGUWORZUUEUVPUXMUUGUWIRZUUGUUGWGZYIZUXOUXNUUGYL
      YMUVPUUGUVLRUXMUXPYNUVPUUGVCUVLUVRVTWASUUGUUGYOVJYPVQUXBYTABCDEFUUKUUGIJK
      LMNOPYQYRYHUUFUVEUVAUVBAUUDUVEUVAWGZUUEUUDUVPUUPUWIRZUXQUVQUUDUVMUXRUVTUU
      GYSVJABCDEFGUUPIJKLMNOPYQYRVQYJUUA $.

    ${
      $d a b F $.  $d a b f i n N $.  $d a b T $.
      signsvtn0.1 $e |- N = ( # ` F ) $.
      $( If the last letter is nonzero, then this is the zero-skipping sign.
         (Contributed by Thierry Arnoux, 8-Oct-2018.)  (Proof shortened by AV,
         3-Nov-2022.) $)
      signsvtn0 $p |- ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` ( N - 1 ) ) =/= 0
        ) -> ( ( T ` F ) ` ( N - 1 ) ) = ( sgn ` ( F ` ( N - 1 ) ) ) ) $=
        ( wcel cc0 wceq cr cword c0 csn cdif c1 cmin co cfv wne csgn chash cfzo
        wa cs1 wf eldifsn birani simpld adantr wrdf cn lennncl lbfzo0 ffvelcdmd
        syl sylibr signstf0 simpr eqtr3id eqs1 syl2anc fveq2d oveq1 1m1e0 s1eqd
        eqtrdi 3eqtr4d fveq12d cneg ctp cxr oveq1i fzo0end eqeltrid rexrd sgncl
        3syl s1fv eqtrd cres cconcat cpfx clsw cfz fzossfz sselid pfxres oveq1d
        pfxlswccat eqcomd oveq2i a1i reseq2d lsw eqtr4d oveq12d wfn wss ffn cn0
        oveq2d fneq2d mpbird nnnn0d nn0z fzossrbm1 fnssres hashfn nnm1nn0 pfxcl
        cz hashfzo0 eqeltrrd nncnd 1cnd subne0d eqnetrd fveq2 hash0 necon3i jca
        signstfvn signstcl sgn0bi necon3bid biimpar signswlid syl21anc 3eqtrd
        pm2.61dane ) GUAUBZUCUDUEZRZHUFUGUHZGUIZSUJZUNZUUEGBUIZUIZUUFUKUIZTHUFU
        UHHUFTZUNZUUJSUUKUOZUIZUUKUUMUUESUUIUUNUUMSGUIZUOZBUIZUUPUKUIZUOZUUIUUN
        UUMUUPUARUURUUTTUUMSGULUIZUMUHZUASGUUMGUUBRZUVBUAGUPZUUHUVCUULUUHUVCGUC
        UJZUUDUVCUVEUNZUUGGUUBUCUQURZUSZUTZUAGVAZVFUUMUVAVBRZSUVBRUUHUVKUULUUHU
        VFUVKUVGUAGVCZVFZUTUVAVDVGVEABCDEFUUPIJKLMNOPVHVFUUMGUUQBUUMUVCUVAUFTGU
        UQTUVIUUMUVAHUFQUUHUULVIZVJUAGVKVLVMUUMUULUUNUUTTUVNUULUUKUUSUULUUFUUPU
        KUULUUESGUULUUEUFUFUGUHSHUFUFUGVNVOVQZVMVMVPVFVRUUMUULUUESTUVNUVOVFVSUU
        MUUKUFVTSUFWAZRZUUOUUKTUUHUVQUULUUHUUFWBRZUVQUUHUUFUUHUVBUAUUEGUUHUVCUV
        DUVHUVJVFUUHUUEUVAUFUGUHZUVBHUVAUFUGQWCZUUHUVFUVKUVSUVBRUVGUVLUVAWDWHZW
        EVEZWFZUUFWGVFZUTUUKUVPWIVFWJUUHHUFUJZUNZUUJGSUUEUMUHZWKZULUIZUWHUUFUOZ
        WLUHZBUIZUIZUWIUFUGUHZUWHBUIUIZUUKAUHZUUKUUHUUJUWMTUWEUUHUUEUWIUUIUWLUU
        HGUWKBUUHGUVSWMUHZGWNUIZUOZWLUHZGSUVSUMUHZWKZUWSWLUHGUWKUUHUWQUXBUWSWLU
        UHUVCUVSSUVAWOUHZRUWQUXBTUVHUUHUVBUXCUVSSUVAWPUWAWQUAGUVSWRVLZWSUUHUVFG
        UWTTUVGUVFUWTGUAGWTXAVFUUHUWHUXBUWJUWSWLUUHUWGUXAGUWGUXATUUHUUEUVSSUMUV
        TXBXCXDZUUHUUFUWRUUHUUFUVSGUIZUWRUUHUUEUVSGUUEUVSTUUHUVTXCVMUUDUWRUXFTU
        UGGUUCXEUTXFVPXGVRVMUUHUWIUUEUUHUWIUWGULUIZUUEUUHUWHUWGXHZUWIUXGTUUHGSH
        UMUHZXHZUWGUXIXIZUXHUUHUXJGUVBXHZUUHUVCUVDUXLUVHUVJUVBUAGXJWHUUHUXIUVBG
        UUHHUVASUMHUVATUUHQXCXLXMXNUUHHXKRHYBRUXKUUHHUUHHUVAVBQUVMWEZXOHXPHXQWH
        UXIUWGGXRVLUWGUWHXSVFUUHHVBRZUUEXKRUXGUUETUXMHXTUUEYCWHWJZXAVSUTUWFUWHU
        UCRZUUFUARZUWMUWPTUWFUWHUUBRZUWHUCUJZUNZUXPUWFUXRUXSUUHUXRUWEUUHUWQUWHU
        UBUUHUWQUXBUWHUXDUXEXFUUHUVCUWQUUBRUVHUAGUVSYAVFYDUTZUWFUWISUJUXSUWFUWI
        UUESUUHUWIUUETUWEUXOUTUWFHUFUWFHUUHUXNUWEUXMUTYEUWFYFUUHUWEVIYGYHUWHUCU
        WISUWHUCTUWIUCULUISUWHUCULYIYJVQYKVFYLZUWHUUBUCUQVGUUHUXQUWEUWBUTABCDEF
        UWHUUFIJKLMNOPYMVLUWFUWOUVPRZUVQUUKSUJZUWPUUKTUWFUXRUWNSUWIUMUHRZUYCUYA
        UWFUXTUWIVBRUYEUYBUAUWHVCUWIWDWHABCDEFUWHUWNIJKLMNOPYNVLUUHUVQUWEUWDUTU
        UHUYDUWEUUHUVRUUGUYDUWCUUDUUGVIUVRUYDUUGUVRUUKSUUFSUUFYOYPYQVLUTAJUWOUU
        KKLMNYRYSYTUUA $.
    $}

    ${
      $d i n N $.
      $( Zero-skipping sign in a word compared to a shorter word.  (Contributed
         by Thierry Arnoux, 8-Oct-2018.) $)
      signstfvp $p |- ( ( F e. Word RR /\ K e. RR /\ N e. ( 0 ..^ ( # ` F ) ) )
        -> ( ( T ` ( F ++ <" K "> ) ) ` N ) = ( ( T ` F ) ` N ) ) $=
        ( cr wcel cfv cword cc0 chash cfzo co w3a cfz cv cconcat csgn cmpt cgsu
        cs1 wa wceq simpl1 3ad2ant2 adantr wss fzssfzo 3ad2ant3 sselda ccatval1
        syl3anc fveq2d mpteq2dva oveq2d ccatws1cl 3adant3 caddc cuz lencl nn0zd
        s1cl c1 uzidd peano2uz fzoss2 3syl 3adant2 ccatlen sylan2 oveq2i eqtrdi
        s1len eleqtrrd signstfval syl2anc 3eqtr4d ) GRUAZSZHRSZIUBGUCTZUDUEZSZU
        FZKDUBIUGUEZDUHZGHUMZUIUEZTZUJTZUKZULUEZKDWQWRGTZUJTZUKZULUEZIWTBTTZIGB
        TTZWPXCXGKULWPDWQXBXFWPWRWQSZUNZXAXEUJXLWKWSWJSZWRWNSXAXEUOWKWLWOXKUPWP
        XMXKWLWKXMWOHRVNZUQURWPWQWNWRWOWKWQWNUSWLIUBWMUTVAVBRRGWSWRVCVDVEVFVGWP
        WTWJSZIUBWTUCTZUDUEZSXIXDUOWKWLXOWORGHVHVIWPIUBWMVOVJUEZUDUEZXQWKWOIXSS
        WLWKWNXSIWKWMWMVKTZSXRXTSWNXSUSWKWMWKWMRGVLVMVPWMWMVQWMUBXRVRVSVBVTWPXP
        XRUBUDWPXPWMWSUCTZVJUEZXRWKWLXPYBUOZWOWLWKXMYCXNRRGWSWAWBVIYAVOWMVJHWEW
        CWDVGWFABCDEFWTIJKLMNOPQWGWHWKWOXJXHUOWLABCDEFGIJKLMNOPQWGVTWI $.

      $d e f i k m n $.  $d g m F $.  $d m N $.  $d a b e g k m n T $.
      $( In case the first letter is not zero, the zero skipping sign is never
         zero.  (Contributed by Thierry Arnoux, 10-Oct-2018.) $)
      signstfvneq0 $p |- ( ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 )
        /\ N e. ( 0 ..^ ( # ` F ) ) ) -> ( ( T ` F ) ` N ) =/= 0 ) $=
        ( c0 cc0 cfv wa vm vg ve vk cr cword csn cdif wcel chash cfzo co simpll
        wne eldifad eldifsni ad2antrr simplr simpr cv wceq fveq2 neeq1d wral wi
        jca cs1 cconcat neeq1 fveq1 anbi12d oveq2d fveq1d raleqbidv imbi12d weq
        neirr intnanr pm2.21i cbvralvw imbi2i anbi2i wn noel eqtrdi fzo0 eleq2d
        hash0 mtbiri pm2.21dd simp-6l simp-6r signstfvp syl3anc simp-5l simplrr
        adantl 3anassrs s1cl ad2antlr cn cmin lennncl adantlr fzo0end elfzolt3b
        w3a c1 3syl ccatval1 biimpa syl21anc simp-5r rspcdva eqnetrd pm2.61dane
        mp2and fveq2d simp-4r simplrl simprd csgn oveq1 ccatlid sylan9eq adantr
        syl signstf0 eqtrd fveq12d sgnclre s1fv cxr wb sgn0bi necon3bid biimpar
        rexr syl2anc ad4ant14 eldifsn biimpri cneg ctp signstcl syldan ad5ant15
        signstfvn sgncl ad4antlr simplll simpllr adantllr signswn0 cuz caddc wo
        anassrs cn0 lencl nn0uz eleqtrdi ad4antr fzosplitsni mpjaodan ralrimiva
        ccatws1len sylanbr exp31 wrdind imp ) GUEUFZQUGZUHZUIZRGSZRUNZTZHRGUJSZ
        UKULZUIZTZGUVLUIZGQUNZUVQTZUWAHGBSZSZRUNZUWBGUVLUVMUVOUVQUWAUMUOUWBUWDU
        VQUVOUWDUVQUWAGUVLQUPUQUVOUVQUWAURVFUVRUWAUSUWCUWETZUWATUAUTZUWFSZRUNZU
        WHUAUVTHUWJHVAUWKUWGRUWJHUWFVBVCUWIUWLUAUVTVDZUWAUWCUWEUWMUBUTZQUNZRUWN
        SZRUNZTZUWJUWNBSZSZRUNZUARUWNUJSZUKULZVDZVEQQUNZRQSZRUNZTZUWJQBSZSZRUNZ
        UARQUJSZUKULZVDZVEUCUTZQUNZRUXOSZRUNZTZUWJUXOBSZSZRUNZUARUXOUJSZUKULZVD
        ZVEZUXOUDUTZVGZVHULZQUNZRUYISZRUNZTZUWJUYIBSZSZRUNZUARUYIUJSZUKULZVDZVE
        UWEUWMVEUBUCUDGUEUWNQVAZUWRUXHUXDUXNUYTUWOUXEUWQUXGUWNQQVIUYTUWPUXFRRUW
        NQVJVCVKUYTUXAUXKUAUXCUXMUYTUXBUXLRUKUWNQUJVBVLUYTUWTUXJRUYTUWJUWSUXIUW
        NQBVBVMVCVNVOUBUCVPZUWRUXSUXDUYEVUAUWOUXPUWQUXRUWNUXOQVIVUAUWPUXQRRUWNU
        XOVJVCVKVUAUXAUYBUAUXCUYDVUAUXBUYCRUKUWNUXOUJVBVLVUAUWTUYARVUAUWJUWSUXT
        UWNUXOBVBVMVCVNVOUWNUYIVAZUWRUYMUXDUYSVUBUWOUYJUWQUYLUWNUYIQVIVUBUWPUYK
        RRUWNUYIVJVCVKVUBUXAUYPUAUXCUYRVUBUXBUYQRUKUWNUYIUJVBVLVUBUWTUYORVUBUWJ
        UWSUYNUWNUYIBVBVMVCVNVOUWNGVAZUWRUWEUXDUWMVUCUWOUWDUWQUVQUWNGQVIVUCUWPU
        VPRRUWNGVJVCVKVUCUXAUWLUAUXCUVTVUCUXBUVSRUKUWNGUJVBVLVUCUWTUWKRVUCUWJUW
        SUWFUWNGBVBVMVCVNVOUXHUXNUXEUXGQVQVRVSUXOUVLUIZUYGUEUIZTZUYFUYMUYSVUFUY
        FTVUFUXSFUTZUXTSZRUNZFUYDVDZVEZTZUYMUYSVUKUYFVUFVUJUYEUXSVUIUYBFUAUYDFU
        AVPVUHUYARVUGUWJUXTVBVCZVTWAWBVULUYMTZUYPUAUYRVUNUWJUYRUIZTZUWJUYDUIZUY
        PUWJUYCVAZVUPVUQTZUYPUXOQVUSUXOQVAZTVUQUYPVUPVUQVUTURVUTVUQWCVUSVUTVUQU
        WJQUIUWJWDVUTUYDQUWJVUTUYDRRUKULQVUTUYCRRUKVUTUYCUXLRUXOQUJVBWHWEZVLRWF
        WEWGWIWQWJVUSUXPTZUYOUYARVVBVUDVUEVUQUYOUYAVAVUDVUEVUKUYMVUOVUQUXPWKVUD
        VUEVUKUYMVUOVUQUXPWLVUPVUQUXPURZABCDEFUXOUYGUWJIJKLMNOPWMWNVVBVUIUYBFUY
        DUWJVUMVVBUXPUXRVUJVUSUXPUSZVVBVUFUXPUYLUXRVUFVUKUYMVUOVUQUXPWOVVDVUNVU
        OVUQUXPUYLVULUYJUYLVUOVUQUXPXGWPWRVUFUXPTZUYLUXRVVEUYKUXQRVVEVUDUYHUVLU
        IZRUYDUIZUYKUXQVAVUDVUEUXPUMVUEVVFVUDUXPUYGUEWSZWTVVEUYCXAUIZUYCXHXBULZ
        UYDUIZVVGVUDUXPVVIVUEUEUXOXCZXDUYCXEZVVJRUYCXFXIUEUEUXOUYHRXJWNVCXKZXLV
        UFVUKUYMVUOVUQUXPXMXQVVCXNXOXPVUPVURTZUYOUYCUYNSZRVVOUWJUYCUYNVUPVURUSX
        RVUPVVPRUNZVURVULUYMVUOVVQVULUYMVUOTZTZVVQUXOQVVSVUTTZVUTVUEUYLVVQVVSVU
        TUSVUDVUEVUKVVRVUTXSVVTUYJUYLVULUYMVUOVUTXTYAVUTVUETZUYLTZVVPUYGYBSZRVW
        BVVPRVWCVGZSZVWCVWBUYCRUYNVWDVWBUYNUYHBSZVWDVWAUYNVWFVAUYLVWAUYIUYHBVUT
        VUEUYIQUYHVHULZUYHUXOQUYHVHYCVUEVVFVWGUYHVAVVHUEUYHYDYGYEZXRYFVUEVWFVWD
        VAVUTUYLABCDEFUYGIJKLMNOPYHWTYIVUTUYCRVAVUEUYLVVAUQYJVUEVWEVWCVAZVUTUYL
        VUEVWCUEUIVWIUYGYKVWCUEYLYGWTYIVWBVUEUYGRUNZVWCRUNZVUTVUEUYLURVWAUYLVWJ
        VWAUYKUYGRVWAUYKRUYHSZUYGVWARUYIUYHVWHVMVUEVWLUYGVAVUTUYGUEYLWQYIVCXKVU
        EVWKVWJVUEVWCRUYGRVUEUYGYMUIZVWCRVAUYGRVAYNUYGYRZUYGYOYGYPYQYSXOXLVVSUX
        PTZVVPVVJUXTSZVWCAULZRVUFUXPVVPVWQVAZVUKVVRVVEUXOUVNUIZVUEVWRVUDUXPVWSV
        UEVWSVUDUXPTZUXOUVLQUUAUUBXDVUDVUEUXPURABCDEFUXOUYGIJKLMNOPUUHYSYTVWOVW
        PXHUUCRXHUUDZUIZVWCVXAUIZVWPRUNZVWQRUNVUDUXPVXBVUEVUKVVRVUDUXPVVKVXBVWT
        VVIVVKVVLVVMYGABCDEFUXOVVJIJKLMNOPUUEUUFUUGVUEVXCVUDVUKVVRUXPVUEVWMVXCV
        WNUYGUUIYGUUJVWOVUIVXDFUYDVVJVUGVVJVAVUHVWPRVUGVVJUXTVBVCVWOUXPUXRVUJVV
        SUXPUSZVWOVUFUXPUYLUXRVUFVUKVVRUXPUUKVXEVWOUYJUYLVULUYMVUOUXPXTYAVVNXLV
        UFVUKVVRUXPUULXQVUFVVRUXPVVKVUKVUFVVRTUXPTVVIVVKVUDUXPVVIVUEVVRVVLYTVVM
        YGUUMXNAJVWPVWCKLMNUUNXLXOXPUURYFXOVUPUYCRUUOSZUIZUWJRUYCXHUUPULZUKULZU
        IZVUQVURUUQZVUDVXGVUEVUKUYMVUOVUDUYCUUSVXFUEUXOUUTUVAUVBUVCVUFVUOVXJVUK
        UYMVUFVUOVXJVUFUYRVXIUWJVUFUYQVXHRUKVUDUYQVXHVAVUEUEUXOUYGUVGYFVLWGXKYT
        VXGVXJVXKRUYCUWJUVDXKYSUVEUVFUVHUVIUVJUVKYFUWIUWAUSXNXL $.

      $( Closure of the zero skipping sign in case the first letter is not
         zero.  (Contributed by Thierry Arnoux, 10-Oct-2018.) $)
      signstfvcl $p |- ( ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 )
        /\ N e. ( 0 ..^ ( # ` F ) ) ) -> ( ( T ` F ) ` N ) e. { -u 1 , 1 } ) $=
        ( wcel cc0 cfv c1 cr cword c0 csn cdif wne wa chash cfzo co cneg simpll
        ctp cpr eldifad signstcl sylancom signstfvneq0 eldifsn sylanbrc difeq1i
        tpcomb wceq neg1ne0 ax-1ne0 diftpsn3 mp2an eqtri eleqtrdi ) GUAUBZUCUDZ
        UEQZRGSRUFZUGZHRGUHSUIUJQZUGZHGBSSZTUKZRTUMZRUDZUEZVRTUNZVPVQVSQZVQRUFV
        QWAQVNVOGVJQWCVPGVJVKVLVMVOULUOABCDEFGHIJKLMNOPUPUQABCDEFGHIJKLMNOPURVQ
        VSRUSUTWAVRTRUMZVTUEZWBVSWDVTVRRTVBVAVRRUFTRUFWEWBVCVDVEVRTRVFVGVHVI $.
    $}

    ${
      $d e f g i k n F $.  $d g G $.  $d e g i k n N $.  $d e g k T $.
      $( Zero-skipping sign in a word compared to a shorter word.  (Contributed
         by Thierry Arnoux, 11-Oct-2018.) $)
      signstfvc $p |- ( ( F e. Word RR /\ G e. Word RR
        /\ N e. ( 0 ..^ ( # ` F ) ) )
        -> ( ( T ` ( F ++ G ) ) ` N ) = ( ( T ` F ) ` N ) ) $=
        ( cr wcel cfv vg ve vk cword cc0 chash cfzo co cconcat wceq wa cv wi c0
        cs1 fveq2d fveq1d eqeq1d imbi2d weq ccatrid adantr s1cl ccatass syl3an3
        oveq2 3expb adantlr ccatcl ad2ant2r simprr wss cuz cz cle wbr lencl cn0
        nn0zd syl caddc nn0red nn0addge1 syl2an breqtrrd eluz2 syl3anbrc fzoss2
        ccatlen simplr sseldd signstfvp eqtr3d id sylan9eq ex expcom a2d wrdind
        syl3anc 3impib 3com12 ) HRUDZSZGXCSZIUEGUFTZUGUHZSZIGHUIUHZBTZTZIGBTZTZ
        UJZXDXEXHXNXEXHUKZIGUAULZUIUHZBTZTZXMUJZUMXOIGUNUIUHZBTZTZXMUJZUMXOIGUB
        ULZUIUHZBTZTZXMUJZUMXOIGYEUCULZUOZUIUHZUIUHZBTZTZXMUJZUMXOXNUMUAUBUCHRX
        PUNUJZXTYDXOYQXSYCXMYQIXRYBYQXQYABXPUNGUIVFUPUQURUSUAUBUTZXTYIXOYRXSYHX
        MYRIXRYGYRXQYFBXPYEGUIVFUPUQURUSXPYLUJZXTYPXOYSXSYOXMYSIXRYNYSXQYMBXPYL
        GUIVFUPUQURUSXPHUJZXTXNXOYTXSXKXMYTIXRXJYTXQXIBXPHGUIVFUPUQURUSXEYDXHXE
        IYBXLXEYAGBRGVAUPUQVBYEXCSZYJRSZUKZXOYIYPXOUUCYIYPUMXOUUCUKZYIYPUUDYIYO
        YHXMUUDIYFYKUIUHZBTZTZYOYHUUDIUUFYNUUDUUEYMBXEUUCUUEYMUJZXHXEUUAUUBUUHU
        UBXEUUAYKXCSUUHYJRVCRGYEYKVDVEVGVHUPUQUUDYFXCSZUUBIUEYFUFTZUGUHZSUUGYHU
        JXEUUAUUIXHUUBRGYEVIZVJXOUUAUUBVKUUDXGUUKIXEUUAXGUUKVLZXHUUBXEUUAUKZUUJ
        XFVMTSZUUMUUNXFVNSZUUJVNSXFUUJVOVPUUOXEUUPUUAXEXFRGVQZVSVBUUNUUJUUNUUIU
        UJVRSUULRYFVQVTVSUUNXFXFYEUFTZWAUHZUUJVOXEXFRSUURVRSXFUUSVOVPUUAXEXFUUQ
        WBRYEVQXFUURWCWDRRGYEWIWEXFUUJWFWGXFUEUUJWHVTVJXEXHUUCWJWKABCDEFYFYJIJK
        LMNOPQWLWTWMYIWNWOWPWQWRWSXAXB $.
    $}

    ${
      $d g i m n F $.  $d f g i m n N $.  $d g m T $.
      $( Restriction of a zero skipping sign to a subword.  (Contributed by
         Thierry Arnoux, 11-Oct-2018.) $)
      signstres $p |- ( ( F e. Word RR /\ N e. ( 0 ... ( # ` F ) ) )
        -> ( ( T ` F ) |` ( 0 ..^ N ) ) = ( T ` ( F |` ( 0 ..^ N ) ) ) ) $=
        ( cr wcel cc0 cfv vm vg cword chash cfz co wa cfzo cres cin wfn signstf
        wf wrdf ffn signstlen oveq2d fneq2d mpbid fnresin syl adantr wss wb cuz
        3syl elfzuz3 fzoss2 adantl incom wceq dfss2 biimpi eqtr3id wrdres wrdfn
        4syl fnssres syl2an hashfn cn0 elfznn0 hashfzo0 3eqtrd cv cconcat fvres
        ad3antlr simpr fveq2d fveq1d ad3antrrr simplr eleq2d ad2antrr signstfvc
        eqtrd biimpar syl3anc wrex wrdsplex r19.29a eqfnfvd ) GQUCZRZHSGUDTZUEU
        FRZUGZUASHUHUFZGBTZXIUIZGXIUIZBTZXHXKSXFUHUFZXIUJZUKZXKXIUKZXEXPXGXEXJX
        NUKZXPXEXJSXJUDTZUHUFZUKZXRXEXJXDRXTQXJUMYAABCDEFGIJKLMNOPULQXJUNXTQXJU
        OVFXEXTXNXJXEXSXFSUHABCDEFGIJKLMNOPUPUQURUSXNXIXJUTVAVBXHXIXNVCZXPXQVDX
        GYBXEXGXFHVETRYBHSXFVGHSXFVHVAZVIYBXOXIXKYBXOXIXNUJZXIXIXNVJYBYDXIVKXIX
        NVLVMVNURVAUSXHXMSXMUDTZUHUFZUKZXMXIUKXHXLXDRZXMXDRYFQXMUMYGQHGVOZABCDE
        FXLIJKLMNOPULQXMUNYFQXMUOVQXHYFXIXMXHYEHSUHXHYEXLUDTZXIUDTZHXHYHYEYJVKY
        IABCDEFXLIJKLMNOPUPVAXHXLXIUKZYJYKVKXEGXNUKYBYLXGQGVPYCXNXIGVRVSXIXLVTV
        AZXGYKHVKZXEXGHWARYNHXFWBHWCVAVIZWDUQURUSXHUAWEZXIRZUGZGXLUBWEZWFUFZVKZ
        YPXKTZYPXMTZVKUBXDYRYSXDRZUGZUUAUGZUUBYPXJTZYPYTBTZTZUUCYQUUBUUGVKXHUUD
        UUAYPXIXJWGWHUUFYPXJUUHUUFGYTBUUEUUAWIWJWKUUFYHUUDYPSYJUHUFZRZUUIUUCVKX
        HYHYQUUDUUAYIWLYRUUDUUAWMYRUUKUUDUUAXHUUKYQXHUUJXIYPXHYJHSUHXHYJYKHYMYO
        WQUQWNWRWOABCDEFXLYSYPIJKLMNOPWPWSWDXHUUAUBXDWTYQUBQHGXAVBXBXC $.
    $}

    ${
      $d a b F $.  $d a b f i n N $.  $d a b T $.
      signstfveq0.1 $e |- N = ( # ` F ) $.
      $( Lemma for ~ signstfveq0 .  (Contributed by Thierry Arnoux,
         11-Oct-2018.) $)
      signstfveq0a $p |- ( ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 )
        /\ ( F ` ( N - 1 ) ) = 0 ) -> N e. ( ZZ>= ` 2 ) ) $=
        ( cc0 wne c1 cr cword c0 csn cdif wcel cfv wa cmin co wceq cn c2 simpll
        cuz cn0 eldifad chash lencl syl eldifsn sylib hasheq0 necon3bid biimpar
        eqeltrid neeq1i sylibr elnnne0 sylanbrc simplr simpr necomd oveq1 1m1e0
        neeqtrrd eqtrdi fveq2d necon3i eluz2b3 ) GUAUBZUCUDZUEUFZRGUGZRSZUHZHTU
        IUJZGUGZRUKZUHZHULUFZHTSZHUMUOUGUFWJHUPUFZHRSZWKWJGWAUFZWMWJGWAWBWCWEWI
        UNZUQWOHGURUGZUPQUAGUSVFUTWJWOGUCSZUHZWNWJWCWSWPGWAUCVAVBWSWQRSZWNWOWTW
        RWOWQRGUCGWAVCVDVEHWQRQVGVHUTHVIVJWJWHWDSWLWJWDWHWJWDRWHWCWEWIVKWFWIVLV
        PVMHTWHWDHTUKZWGRGXAWGTTUIUJRHTTUIVNVOVQVRVSUTHVTVJ $.

      $( In case the last letter is zero, the zero skipping sign is the same as
         the previous letter.  (Contributed by Thierry Arnoux, 11-Oct-2018.)
         (Proof shortened by AV, 4-Nov-2022.) $)
      signstfveq0 $p |- ( ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 )
          /\ ( F ` ( N - 1 ) ) = 0 )
        -> ( ( T ` F ) ` ( N - 1 ) ) = ( ( T ` F ) ` ( N - 2 ) ) ) $=
        ( wcel cc0 c1 cr cword c0 csn cdif cfv wne wa cmin co wceq cpfx cconcat
        chash cs1 csgn simpll eldifad pfxcl syl cfz cn0 cle wbr 1nn0 a1i nn0red
        c2 cn 2re lencl eqeltrid 1le2 cz cuz w3a signstfveq0a eluz2 sylib letrd
        simp3d fznn0 mpbir2and fznn0sub2 oveq2i eleqtrdi pfxlen syl2anc uz2m1nn
        wb eqeltrd nnne0 fveq2 hash0 eqtrdi necon3i sylanbrc simpr 0re eqeltrdi
        eldifsn signstfvn clsw oveq1i lsw ad2antrr eqcomi fveq2i eqcomd oveq12d
        s1eqd pfxlswccat eqtrd fveq2d fveq12d cfzo nn0cnd 1cnd subsub4d fzo0end
        caddc eqeltrrd oveq2d eleqtrrd signstfvp syl3anc fveq1d oveq1d 3eqtr4rd
        1p1e2 sgn0 adantl cneg ctp clt uznn0sub eluz2nn crp 2rp ltsubrpd elfzo0
        syl3anbrc signstcl signswrid 3eqtr3d ) GUAUBZUCUDZUEZRZSGUFSUGZUHZHTUIU
        JZGUFZSUKZUHZGUULULUJZUNUFZUUPUUMUOZUMUJZBUFZUFZUUQTUIUJZUUPBUFZUFZUUMU
        PUFZAUJZUULGBUFZUFHVHUIUJZUVGUFZUUOUUPUUHRZUUMUARZUVAUVFUKUUOUUPUUFRZUU
        PUCUGZUVJUUOGUUFRZUVLUUOGUUFUUGUUIUUJUUNUQZURZUAGUULUSUTZUUOUUQVIRZUVMU
        UOUUQUULVIUUOUVNUULSGUNUFZVAUJZRUUQUULUKUVPUUOUULSHVAUJZUVTUUOTUWARZUUL
        UWARUUOUWBTVBRZTHVCVDZUWCUUOVEVFZUUOTVHHUUOTUWEVGVHUARUUOVJVFUUOHUUOHUV
        SVBQUUOUVNUVSVBRUVPUAGVKUTVLZVGZTVHVCVDUUOVMVFUUOVHVNRZHVNRZVHHVCVDZUUO
        HVHVOUFRZUWHUWIUWJVPABCDEFGHIJKLMNOPQVQZVHHVRVSWAVTUUOHVBRUWBUWCUWDUHWJ
        UWFTHWBUTWCTHWDUTHUVSSVAQWEWFUAGUULWGWHZUUOUWKUULVIRZUWLHWIUTZWKUVRUUQS
        UGUVMUUQWLUUPUCUUQSUUPUCUKUUQUCUNUFSUUPUCUNWMWNWOWPUTUTUUPUUFUCXAWQUUOU
        UMSUAUUKUUNWRWSWTZABCDEFUUPUUMIJKLMNOPXBWHUUOUUQUULUUTUVGUUOUUSGBUUOUUS
        GUVSTUIUJZULUJZGXCUFZUOZUMUJZGUUOUUPUWRUURUWTUMUUPUWRUKUUOUULUWQGULHUVS
        TUIQXDWEVFUUOUWTUURUUOUWSUUMUUOUWSUWQGUFZUUMUUIUWSUXBUKUUJUUNGUUHXEXFUW
        QUULGUVSHTUIHUVSQXGXDXHWOXKXIXJUUOUVNGUCUGUHZUXAGUKUUOUUIUXCUVOGUUFUCXA
        VSUAGXLUTXMZXNUWMXOUUOUVFUVISAUJZUVIUUOUVDUVIUVESAUUOUVHUUTUFZUVHUVCUFZ
        UVIUVDUUOUVLUVKUVHSUUQXPUJZRUXFUXGUKUVQUWPUUOUVHSUULXPUJZUXHUUOUULTUIUJ
        ZUVHUXIUUOUXJHTTYAUJZUIUJZUVHUUOHTTUUOHUWFXQUUOXRZUXMXSZUXKVHHUIYJWEZWO
        UUOUWNUXJUXIRUWOUULXTUTYBUUOUUQUULSXPUWMYCYDABCDEFUUPUUMUVHIJKLMNOPYEYF
        UUOUVHUVGUUTUUOGUUSBUUOUUSGUXDXIXNYGUUOUVBUVHUVCUUOUVBUXLUVHUUOUVBUXJUX
        LUUOUUQUULTUIUWMYHUXNXMUXOWOXNYIUUNUVESUKUUKUUNUVESUPUFSUUMSUPWMYKWOYLX
        JUUOUVITYMSTYNRZUXEUVIUKUUOUVNUVHSUVSXPUJZRUXPUVPUUOUVHSHXPUJZUXQUUOUVH
        VBRZHVIRZUVHHYOVDUVHUXRRUUOUWKUXSUWLVHHYPUTUUOUWKUXTUWLHYQUTUUOHVHUWGVH
        YRRUUOYSVFYTUVHHUUAUUBHUVSSXPQWEWFABCDEFGUVHIJKLMNOPUUCWHAJUVIKLMNUUDUT
        XMUUE $.
    $}

    ${
      $d f j F $.  $d f T $.
      $( The value of ` V ` , which represents the number of times the sign
         changes in a word.  (Contributed by Thierry Arnoux, 7-Oct-2018.) $)
      signsvvfval $p |- ( F e. Word RR -> ( V ` F ) =
        sum_ j e. ( 1 ..^ ( # ` F ) )
          if ( ( ( T ` F ) ` j ) =/= ( ( T ` F ) ` ( j - 1 ) ) , 1 , 0 ) ) $=
        ( c1 chash cfv cfzo co cv cmin wne cc0 cif csu cr cword wceq fveq2 wcel
        oveq2d fveq1d neeq12d ifbid adantr sumeq12dv sumex fvmpt ) CGPCUAZQRZST
        ZEUAZUTBRZRZVCPUBTZVDRZUCZPUDUEZEUFPGQRZSTZVCGBRZRZVFVLRZUCZPUDUEZEUFUG
        UHHUTGUIZVBVKVIVPEVQVAVJPSUTGQUJULVQVIVPUIVCVBUKVQVHVOPUDVQVEVMVGVNVQVC
        VDVLUTGBUJZUMVQVFVDVLVRUMUNUOUPUQOVKVPEURUS $.

      $( ` V ` is a function.  (Contributed by Thierry Arnoux, 8-Oct-2018.) $)
      signsvvf $p |- V : Word RR --> NN0 $=
        ( cn0 c1 cfv cc0 wcel a1i cr cword cv chash cfzo cmin wne cif csu fzofi
        co cfn wa 1nn0 wn 0nn0 ifclda fsumnn0cl fmpti ) CUAUBZOPCUCZUDQZUEUKZEU
        CZVABQZQVDPUFUKVEQUGZPRUHZEUIGNVAUTSZVCVGEVCULSVHPVBUJTVHVDVCSUMZVFPROP
        OSVIVFUMUNTROSVIVFUOUMUPTUQURUS $.

      $( There is no change of sign in the empty word.  (Contributed by Thierry
         Arnoux, 8-Oct-2018.) $)
      signsvf0 $p |- ( V ` (/) ) = 0 $=
        ( c0 cfv c1 cfzo co cc0 chash cv cmin wne cif cr cword wcel signsvvfval
        csu wceq wrd0 ax-mp hash0 oveq2i cle wbr 0le1 cz wb 1z fzon mp2an eqtri
        0z mpbi sumeq1i sum0 3eqtri ) OGPZQOUAPZRSZEUBZOBPZPVMQUCSVNPUDQTUEZEUJ
        ZOVOEUJTOUFUGUHVJVPUKUFULABCDEFOGHIJKLMNUIUMVLOVOEVLQTRSZOVKTQRUNUOTQUP
        UQZVQOUKZURQUSUHTUSUHVRVSUTVAVEQTVBVCVFVDVGVOEVHVI $.

      $d f j K $.
      $( In a single-letter word, which represents a constant polynomial, there
         is no change of sign.  (Contributed by Thierry Arnoux, 8-Oct-2018.) $)
      signsvf1 $p |- ( K e. RR -> ( V ` <" K "> ) = 0 ) $=
        ( cr cfv c1 cfzo co wcel cs1 chash cmin wne cc0 cif csu cword wceq s1cl
        cv signsvvfval syl c0 s1len oveq2i fzo0 eqtri sumeq1i sum0 eqtrdi ) GPU
        AZGUBZHQZRVDUCQZSTZEULZVDBQZQVHRUDTVIQUERUFUGZEUHZUFVCVDPUIUAVEVKUJGPUK
        ABCDEFVDHIJKLMNOUMUNVKUOVJEUHUFVGUOVJEVGRRSTUOVFRRSGUPUQRURUSUTVJEVAUSV
        B $.
    $}

    ${
      $d a b i j n F $.  $d a b j n K $.  $d a b f j n T $.
      $( Number of changes in a word compared to a shorter word.  (Contributed
         by Thierry Arnoux, 12-Oct-2018.) $)
      signsvfn $p |- ( ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 )
        /\ K e. RR ) -> ( V ` ( F ++ <" K "> ) ) = ( ( V ` F ) +
        if ( ( ( ( T ` F ) ` ( ( # ` F ) - 1 ) ) x. K ) < 0 , 1 , 0 ) ) ) $=
        ( wcel cc0 cfv c1 cr cword c0 csn cdif wne wa cs1 cconcat co chash cfzo
        cv cmin cif csu cmul clt wbr wceq eldifi s1cl ccatcl syl2an signsvvfval
        caddc syl ccatlen s1len oveq2i eqtrdi oveq2d sumeq1d cn eldifsn lennncl
        cuz sylbi nnuz eleqtrdi adantr cfz cc 1cnd wn 0cnd ifclda fveq2 fvoveq1
        neeq12d ifbid fzosump1 3eqtrd adantlr eldifad simplr wss fzo0ss1 sselda
        a1i signstfvp syl3anc cz cn0 elfzoel2 adantl 1nn0 eluzmn sylancl fzoss2
        simpl elfzo1elm1fzo0 sseldd sumeq2dv eqtr4d csgn simpr fzo0end ad2antrr
        signstfvn cneg cpr ctp wb signstfvcl syldan rexr sgncl signswch syl2anc
        cxr rexrd sgnsgn breq1d neg1rr 1re prssi mp2an sselid sgnmulsgn sgnclre
        sylancom 3bitr4d 3bitrd oveq12d eqtrd ) GUAUBZUCUDZUEQZRGSRUFZUGZHUAQZU
        GZGHUHZUIUJZISZTGUKSZULUJZEUMZUUOBSZSZUUSTUNUJZUUTSZUFZTRUOZEUPZUUQUUTS
        ZUUQTUNUJZUUTSZUFZTRUOZVFUJZGISZUVHGBSZSZHUQUJRURUSZTRUOZVFUJUUIUULUUPU
        VLUTUUJUUIUULUGZUUPTUUOUKSZULUJZUVEEUPZTUUQTVFUJZULUJZUVEEUPUVLUVRUUOUU
        GQZUUPUWAUTUUIGUUGQZUUNUUGQZUWDUULGUUGUUHVAZHUAVBZUAGUUNVCVDABCDEFUUOIJ
        KLMNOPVEVGUVRUVTUWCUVEEUVRUVSUWBTULUVRUVSUUQUUNUKSZVFUJZUWBUUIUWEUWFUVS
        UWJUTUULUWGUWHUAUAGUUNVHVDUWITUUQVFHVIVJVKVLVMUVRUVEUVKETUUQUUIUUQTVQSZ
        QUULUUIUUQVNUWKUUIUWEGUCUFUGUUQVNQZGUUGUCVOUAGVPVRZVSVTWAUVRUUSTUUQWBUJ
        QUGZUVDTRWCUWNUVDUGWDUWNUVDWEUGWFWGUUSUUQUTZUVDUVJTRUWOUVAUVGUVCUVIUUSU
        UQUUTWHUUSUUQTUUTUNWIWJWKWLWMWNUUMUVFUVMUVKUVQVFUUIUULUVFUVMUTUUJUVRUVF
        UURUUSUVNSZUVBUVNSZUFZTRUOZEUPZUVMUVRUURUVEUWSEUVRUUSUURQZUGZUVDUWRTRUX
        BUVAUWPUVCUWQUXBUWEUULUUSRUUQULUJZQUVAUWPUTUVRUWEUXAUVRGUUGUUHUUIUULXKW
        OZWAZUUIUULUXAWPZUVRUURUXCUUSUURUXCWQUVRUUQWRWTWSABCDEFGHUUSIJKLMNOPXAX
        BUXBUWEUULUVBUXCQUVCUWQUTUXEUXFUXBRUVHULUJZUXCUVBUXBUUQUVHVQSQZUXGUXCWQ
        UXBUUQXCQZTXDQUXHUXAUXIUVRUUSTUUQXEXFXGUUQTXHXIUVHRUUQXJVGUXAUVBUXGQUVR
        UUSUUQXLXFXMABCDEFGHUVBIJKLMNOPXAXBWJWKXNUVRUWEUVMUWTUTUXDABCDEFGIJKLMN
        OPVEVGXOWNUUMUVJUVPTRUUMUVJUVOHXPSZAUJZUVOUFZUVOUXJUQUJRURUSZUVPUUMUVGU
        XKUVIUVOUUIUULUVGUXKUTUUJABCDEFGHIJKLMNOPXTWNUUMUWEUULUVHUXCQZUVIUVOUTU
        UIUULUWEUUJUXDWNUUKUULXQZUUIUXNUUJUULUUIUWLUXNUWMUUQXRVGXSZABCDEFGHUVHI
        JKLMNOPXAXBWJUUMUVOTYAZTYBZQZUXJUXQRTYCQZUXLUXMYDUUKUULUXNUXSUXPABCDEFG
        UVHIJKLMNOPYEYFZUULUXTUUKUULHYKQZUXTHYGHYHVGXFAJUVOUXJKLMNYIYJUUMUVOXPS
        ZUXJXPSZUQUJZRURUSZUYCUXJUQUJZRURUSZUXMUVPUUMUYEUYGRURUUMUYDUXJUYCUQUUM
        UYBUYDUXJUTUUMHUXOYLHYMVGVLYNUUMUVOUAQZUXJUAQZUXMUYFYDUUMUXRUAUVOUXQUAQ
        TUAQUXRUAWQYOYPUXQTUAYQYRUYAYSZUULUYJUUKHUUAXFUVOUXJYTYJUUKUULUYIUVPUYH
        YDUYKUVOHYTUUBUUCUUDWKUUEUUF $.
    $}

    ${
      signsvf.e $e |- ( ph -> E e. ( Word RR \ { (/) } ) ) $.
      signsvf.0 $e |- ( ph -> ( E ` 0 ) =/= 0 ) $.
      signsvf.f $e |- ( ph -> F = ( E ++ <" A "> ) ) $.
      signsvf.a $e |- ( ph -> A e. RR ) $.
      signsvf.n $e |- N = ( # ` E ) $.
      ${
        $d a b f i j $.  $d a b f i j n A $.  $d a b f i j n E $.
        $d a b f j n T $.
        signsvt.b $e |- B = ( ( T ` E ) ` ( N - 1 ) ) $.
        $( Adding a letter of the same sign as the highest coefficient does not
           change the sign.  (Contributed by Thierry Arnoux, 12-Oct-2018.) $)
        signsvtp $p |- ( ( ph /\ 0 < ( A x. B ) ) -> ( V ` F ) = ( V ` E ) ) $=
          ( cc0 cmul co clt wbr wa cfv chash c1 cmin cif caddc wceq cs1 cconcat
          fveq2d cr cword csn cdif wcel wne signsvfn syl21anc eqtrd adantr 0red
          c0 cfzo wf eldifad signstf wrdf 3syl cn eldifsn sylib lennncl fzo0end
          signstlen syl oveq2d eleqtrrd ffvelcdmd remulcld simpr eqtri eqeltrid
          oveq1i fveq2i mulcomd breqtrrd breqtrdi ltnsymd iffalsed cn0 signsvvf
          recnd a1i nn0cnd addridd 3eqtrd ) AUGBCUHUIZUJUKZULZKMUMZJMUMZJUNUMZU
          OUPUIZJEUMZUMZBUHUIZUGUJUKZUOUGUQZURUIZXMUGURUIXMAXLYAUSXJAXLJBUTVAUI
          ZMUMZYAAKYBMUCVBAJVCVDZVNVEZVFVGZUGJUMUGVHBVCVGZYCYAUSUAUBUDDEFGHIJBM
          NOPQRSTVIVJVKVLXKXTUGXMURXKXSUOUGXKUGXRXKVMXKXQBXKUGXPUNUMZVOUIZVCXOX
          PXKJYDVGZXPYDVGYIVCXPVPXKJYDYEAYFXJUAVLVQZDEFGHIJMNOPQRSTVRVCXPVSVTXK
          XOUGXNVOUIZYIXKYJJVNVHULZXNWAVGXOYLVGAYMXJAYFYMUAJYDVNWBWCVLVCJWDXNWE
          VTXKYHXNUGVOXKYJYHXNUSYKDEFGHIJMNOPQRSTWFWGWHWIWJZAYGXJUDVLZWKXKUGCBU
          HUIZXRUJXKUGXIYPUJAXJWLXKCBXKCXKCXQVCCLUOUPUIZXPUMXQUFYQXOXPLXNUOUPUE
          WOWPWMZYNWNXDXKBYOXDWQWRCXQBUHYRWOWSWTXAWHXKXMXKXMXKYDXBJMYDXBMVPXKDE
          FGHIMNOPQRSTXCXEYKWJXFXGXH $.

        $( Adding a letter of a different sign as the highest coefficient
           changes the sign.  (Contributed by Thierry Arnoux, 12-Oct-2018.) $)
        signsvtn $p |- ( ( ph /\ ( A x. B ) < 0 ) -> ( ( V ` F ) - ( V ` E ) )
          = 1 ) $=
          ( cmul co cc0 clt wbr wa cfv cmin c1 wceq caddc chash cif cs1 cconcat
          fveq2d cr cword c0 csn cdif wne signsvfn syl21anc eqtrd adantr oveq1i
          wcel eqtri cfzo wf eldifad signstf wrdf 3syl cn eldifsn sylib lennncl
          fveq2i fzo0end signstlen syl oveq2d eleqtrrd ffvelcdmd eqeltrid recnd
          mulcomd simpr eqbrtrd eqbrtrrid iftrued eqtr2d cn0 signsvvf a1i s1cld
          ccatcl syl2anc eqeltrd nn0cnd 1cnd subaddd mpbird ) ABCUGUHZUIUJUKZUL
          ZKMUMZJMUMZUNUHUOUPXPUOUQUHZXOUPXNXOXPJURUMZUOUNUHZJEUMZUMZBUGUHZUIUJ
          UKZUOUIUSZUQUHZXQAXOYEUPXMAXOJBUTZVAUHZMUMZYEAKYGMUCVBAJVCVDZVEVFZVGV
          NZUIJUMUIVHBVCVNZYHYEUPUAUBUDDEFGHIJBMNOPQRSTVIVJVKVLXNYDUOXPUQXNYCUO
          UIXNYBCBUGUHZUIUJCYABUGCLUOUNUHZXTUMYAUFYNXSXTLXRUOUNUEVMWFVOZVMXNYMX
          LUIUJXNCBXNCXNCYAVCYOXNUIXTURUMZVPUHZVCXSXTXNJYIVNZXTYIVNYQVCXTVQXNJY
          IYJAYKXMUAVLVRZDEFGHIJMNOPQRSTVSVCXTVTWAXNXSUIXRVPUHZYQXNYRJVEVHULZXR
          WBVNXSYTVNAUUAXMAYKUUAUAJYIVEWCWDVLVCJWEXRWGWAXNYPXRUIVPXNYRYPXRUPYSD
          EFGHIJMNOPQRSTWHWIWJWKWLWMWNXNBAYLXMUDVLZWNWOAXMWPWQWRWSWJWTXNXOXPUOX
          NXOXNYIXAKMYIXAMVQXNDEFGHIMNOPQRSTXBXCZXNKYGYIAKYGUPXMUCVLXNYRYFYIVNY
          GYIVNYSXNBVCUUBXDVCJYFXEXFXGWLXHXNXPXNYIXAJMUUCYSWLXHXNXIXJXK $.
      $}

      ${
        $d a b f i j n A $.  $d a b f i j n E $.  $d a b f i n N $.
        $d a b f j n T $.
        signsvf.b $e |- B = ( E ` ( N - 1 ) ) $.
        $( Adding a letter of the same sign as the highest coefficient does not
           change the sign.  (Contributed by Thierry Arnoux, 12-Oct-2018.) $)
        signsvfpn $p |- ( ( ph /\ 0 < ( B x. A ) )
          -> ( V ` F ) = ( V ` E ) ) $=
          ( cc0 cmul co clt wbr c1 cmin cfv wceq wa csgn recnd cc chash cfzo cr
          cword wcel wf c0 csn eldifad wrdf syl oveq1i wne cdif eldifsn lennncl
          cn sylib fzo0end 3syl eqeltrid ffvelcdmd mulcomd wb sgnmulsgp syl2anc
          breq2d bitr3d biimpa adantr simpr gt0ne0d mulne0bad eqnetrrid eqtr4di
          signsvtn0 fveq2i fveq2d cxr rexrd sgnsgn eqtrd oveq2d sgnclre eqeltrd
          breqtrrd mpbird eqid signsvtp syldan ) AUGCBUHUIZUJUKZUGBLULUMUIZJEUN
          UNZUHUIUJUKZKMUNJMUNUOAXKUPZXNUGBUQUNZXMUQUNZUHUIZUJUKZXOUGXPCUQUNZUH
          UIZXRUJAXKUGYAUJUKZAUGBCUHUIZUJUKZXKYBAYCXJUGUJABCABUDURZACXLJUNZUSUF
          AYFAUGJUTUNZVAUIZVBXLJAJVBVCZVDZYHVBJVEAJYIVFVGZUAVHVBJVIVJAXLYGULUMU
          IZYHLYGULUMUEVKAYJJVFVLUPZYGVPVDYLYHVDAJYIYKVMVDZYMUAJYIVFVNVQVBJVOYG
          VRVSVTWAZURVTZWBWFABVBVDZCVBVDZYDYBWCUDACYFVBUFYOVTZBCWDWEWGWHXOXQXTX
          PUHXOXQXTUQUNZXTXOXMXTUQXOYNYFUGVLZXMXTUOAYNXKUAWIXOYFCUGUFXOCBACUSVD
          XKYPWIABUSVDXKYEWIXOXJAXKWJWKWLWMYNUUAUPXMYFUQUNXTDEFGHIJLMNOPQRSTUEW
          OCYFUQUFWPWNWEZWQXOCWRVDYTXTUOXOCAYRXKYSWIZWSCWTVJXAXBXEXOYQXMVBVDXNX
          SWCAYQXKUDWIXOXMXTVBUUBXOYRXTVBVDUUCCXCVJXDBXMWDWEXFABXMDEFGHIJKLMNOP
          QRSTUAUBUCUDUEXMXGXHXI $.

        $( Adding a letter of a different sign as the highest coefficient
           changes the sign.  (Contributed by Thierry Arnoux, 12-Oct-2018.) $)
        signsvfnn $p |- ( ( ph /\ ( B x. A ) < 0 )
          -> ( ( V ` F ) - ( V ` E ) ) = 1 ) $=
          ( cmul co cc0 clt wbr c1 cmin cfv wceq wa csgn cr cword csn cdif wcel
          c0 wne adantr cc chash cfzo wf eldifad wrdf oveq1i cn eldifsn lennncl
          sylib fzo0end 3syl eqeltrid ffvelcdmd recnd simpr mulne0bad eqnetrrid
          syl lt0ne0d signsvtn0 fveq2i eqtr4di syl2anc fveq2d cxr sgnsgn oveq2d
          rexrd eqtrd mulcomd breq1d wb sgnmulsgn bitr3d biimpa eqbrtrd sgnclre
          eqeltrd mpbird eqid signsvtn syldan ) ACBUGUHZUIUJUKZBLULUMUHZJEUNUNZ
          UGUHUIUJUKZKMUNJMUNUMUHULUOAXKUPZXNBUQUNZXMUQUNZUGUHZUIUJUKZXOXRXPCUQ
          UNZUGUHZUIUJXOXQXTXPUGXOXQXTUQUNZXTXOXMXTUQXOJURUSZVCUTZVAVBZXLJUNZUI
          VDZXMXTUOAYEXKUAVEXOYFCUIUFXOCBACVFVBXKACYFVFUFAYFAUIJVGUNZVHUHZURXLJ
          AJYCVBZYIURJVIAJYCYDUAVJURJVKWEAXLYHULUMUHZYILYHULUMUEVLAYJJVCVDUPZYH
          VMVBYKYIVBAYEYLUAJYCVCVNVPURJVOYHVQVRVSVTZWAVSZVEABVFVBXKABUDWAZVEXOX
          JAXKWBWFWCWDYEYGUPXMYFUQUNXTDEFGHIJLMNOPQRSTUEWGCYFUQUFWHWIWJZWKXOCWL
          VBYBXTUOXOCACURVBZXKACYFURUFYMVSZVEZWOCWMWEWPWNAXKYAUIUJUKZABCUGUHZUI
          UJUKZXKYTAUUAXJUIUJABCYOYNWQWRABURVBZYQUUBYTWSUDYRBCWTWJXAXBXCXOUUCXM
          URVBXNXSWSAUUCXKUDVEXOXMXTURYPXOYQXTURVBYSCXDWEXEBXMWTWJXFABXMDEFGHIJ
          KLMNOPQRSTUAUBUCUDUEXMXGXHXI $.
      $}
    $}

$(
    @{
      @( Shifting the whole word to the right (i.e., multiplying the
         corresponding polynomial by ` x ` ) does not change the parity of the
         sign changes.  (Contributed by Thierry Arnoux, 9-Sep-2018.) @)
      signwmulx @p |- ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 )
       -> ( V ` ( <" 0 "> ++ F ) ) = ( V ` F ) ) @=
      ? @.
    @}

    @{
      @( If the first and last coefficients in the word are of opposite sign,
         there is an odd number of sign changes.  (Contributed by Thierry
         Arnoux, 9-Sep-2018.) @)
      signwtog @p |- ( ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 )
          /\ ( ( F ` 0 ) x. ( F ` ( ( # ` F ) - 1 ) ) ) < 0 )
        -> -. 2 || ( V ` F ) ) @=
      ? @.
    @}
$)

    ${
      $d a b f i j $.  $d a b j F $.  $d a b f j n T $.
      $( Adding a zero as the highest coefficient does not change the parity of
         the sign changes.  (Contributed by Thierry Arnoux, 12-Oct-2018.) $)
      signlem0 $p |- ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 )
       -> ( V ` ( F ++ <" 0 "> ) ) = ( V ` F ) ) $=
        ( wcel cc0 cfv co c1 cr cword c0 csn cdif wne wa cs1 cconcat chash cmin
        cmul clt wbr cif caddc wceq 0re signsvfn mpan2 ltnri cneg cpr cc neg1cn
        wss ax-1cn prssi cfzo cn eldifsn birani lennncl fzo0end 3syl signstfvcl
        mp2an mpdan sselid mul01d breq1d mtbiri iffalsed oveq2d cn0 wf signsvvf
        a1i simpl eldifad ffvelcdmd nn0cnd addridd 3eqtrd ) GUAUBZUCUDZUEPZQGRQ
        UFZUGZGQUHUISHRZGHRZGUJRZTUKSZGBRRZQULSZQUMUNZTQUOZUPSZXAQUPSXAWSQUAPWT
        XHUQURABCDEFGQHIJKLMNOUSUTWSXGQXAUPWSXFTQWSXFQQUMUNQURVAWSXEQQUMWSXDWST
        VBZTVCZVDXDXIVDPTVDPXJVDVFVEVGXITVDVHVQWSXCQXBVISPZXDXJPWSGWOPGUCUFUGZX
        BVJPXKWQXLWRGWOUCVKVLUAGVMXBVNVOABCDEFGXCHIJKLMNOVPVRVSVTWAWBWCWDWSXAWS
        XAWSWOWEGHWOWEHWFWSABCDEFHIJKLMNOWGWHWSGWOWPWQWRWIWJWKWLWMWN $.
    $}

$(
    @{
      signlem.x @e |- ( ph -> X e. RR ) @.
      signlem.y @e |- ( ph -> Y e. RR ) @.
      signlem.z @e |- ( ph -> Z e. RR ) @.
      signlem.f @e |- ( ph -> G = ( F ++ <" Z "> ) ) @.
      signlem.g @e |- ( ph -> H = ( F ++ <" Y X "> ) ) @.
      signlem.h @e |- ( ph -> F e. ( Word RR \ { (/) } ) ) @.
      signlem.0 @e |- ( ph -> ( H ` 0 ) =/= 0 ) @.
      @( Inserting any coefficient just before the highest one does not change
         the parity.  @)
      signlem1 @p |- ( ( ph /\ 0 < ( Z x. X ) )
        -> ( ( V ` H ) - ( V ` G ) ) e. { 0 , 2 } ) @=
        ? @.

      @( Inserting a coefficient of opposed sign after the highest changes the
         parity.  @)
      signlem2 @p |- ( ( ( ph /\ ( Z x. X ) < 0 ) /\ 0 < ( Y x. Z ) )
        -> ( ( V ` H ) - ( V ` G ) ) = 1 ) @=
        ? @.

      signlem3.i @e |- ( ph -> J = ( ( T ` F ) ` ( ( # ` F ) - 1 ) ) ) @.
      @( Replacing a leading zero with two coefficients of opposed sign changes
         the parity.  @)
      signlem34 @p |- ( ( ph /\ Z = 0 /\ ( X x. Y ) < 0 )
        -> ( V ` H ) = ( ( V ` G ) + if ( ( sgn ` Y ) =/= J , 1 , 0 ) ) ) @=
        ? @.

      @( Replacing a leading zero with two coefficients of opposed sign changes
         the parity.  @)
      signlem3 @p |- ( ( ( ph /\ Z = 0 /\ ( X x. Y ) < 0 ) /\ ( Y x. J ) < 0 )
        -> ( ( V ` H ) - ( V ` G ) ) = 2 ) @=
        ? @.

      @( Replacing a leading zero with two coefficients of opposed sign changes
         the parity.  @)
      signlem4 @p |- ( ( ( ph /\ Z = 0 /\ ( X x. Y ) < 0 ) /\ 0 < ( Y x. J ) )
        -> ( ( V ` H ) - ( V ` G ) ) = 1 ) @=
        ? @.
    @}
$)
    signs.h $e |- H =
      ( ( <" 0 "> ++ F ) oF - ( ( F ++ <" 0 "> ) oFC x. C ) ) $.

    ${
      $d x y C $.  $d x y F $.
      $( ` H ` , corresponding to the word ` F ` multiplied by ` ( x - C ) ` ,
         as a function.  (Contributed by Thierry Arnoux, 29-Sep-2018.) $)
      signshf $p |- ( ( F e. Word RR /\ C e. RR+ )
        -> H : ( 0 ..^ ( ( # ` F ) + 1 ) ) --> RR ) $=
        ( cr co vx vy cword wcel crp wa cc0 chash cfv c1 caddc cfzo cs1 cconcat
        cmul cofc cmin cof wf cvv cv resubcl adantl s1cl ax-mp ccatcl mpan wrdf
        0re syl 1cnd lencl nn0cnd wceq ccatlen s1len oveq1i eqtrdi oveq2d feq2d
        comraddd mpbid remulcl mpan2 ccatws1len ovexd rpre ofcf inidm off feq1i
        adantr sylibr ) HSUCZUDZAUEUDZUFZUGHUHUIZUJUKTZULTZSUGUMZHUNTZHXAUNTZAU
        OUPTZUQURTZUSWTSIUSWQUAUBWTWTWTUQSSSXBXDUTUTUAVAZSUDUBVAZSUDUFZXFXGUQTS
        UDWQXFXGVBVCWOWTSXBUSZWPWOUGXBUHUIZULTZSXBUSZXIWOXBWNUDZXLXAWNUDZWOXMUG
        SUDXNVIUGSVDVEZSXAHVFVGSXBVHVJWOXKWTSXBWOXJWSUGULWOXJUJWRWOVKWOWRSHVLVM
        WOXJXAUHUIZWRUKTZUJWRUKTXNWOXJXQVNXOSSXAHVOVGXPUJWRUKUGVPVQVRWAVSVTWBWL
        WQUAUBWTAUOSSSXCUTXHXFXGUOTSUDWQXFXGWCVCWOWTSXCUSZWPWOUGXCUHUIZULTZSXCU
        SZXRWOXCWNUDZYAWOXNYBXOSHXAVFWDSXCVHVJWOXTWTSXCWOXSWSUGULSHUGWEVSVTWBWL
        WQUGWSULWFZWPASUDWOAWGVCWHYCYCWTWIWJWTSIXERWKWM $.
    $}

    $( ` H ` , corresponding to the word ` F ` multiplied by ` ( x - C ) ` , is
       a word.  (Contributed by Thierry Arnoux, 29-Sep-2018.) $)
    signshwrd $p |- ( ( F e. Word RR /\ C e. RR+ ) -> H e. Word RR ) $=
      ( cr wcel cword crp wa cc0 chash cfv c1 caddc co cfzo signshf iswrdi syl
      wf ) HSUAZTAUBTUCUDHUEUFUGUHUIZUJUISIUNIUOTABCDEFGHIJKLMNOPQRUKSUPIULUM
      $.

    $( Length of ` H ` , corresponding to the word ` F ` multiplied by
       ` ( x - C ) ` .  (Contributed by Thierry Arnoux, 14-Oct-2018.) $)
    signshlen $p |- ( ( F e. Word RR /\ C e. RR+ ) ->
      ( # ` H ) = ( ( # ` F ) + 1 ) ) $=
      ( cr wcel cword crp wa chash cfv cc0 c1 caddc co cfzo wf wfn wceq signshf
      ffn hashfn 3syl cn0 lencl adantr 1nn0 a1i nn0addcld hashfzo0 syl eqtrd )
      HSUATZAUBTZUCZIUDUEZUFHUDUEZUGUHUIZUJUIZUDUEZVLVIVMSIUKIVMULVJVNUMABCDEFG
      HIJKLMNOPQRUNVMSIUOVMIUPUQVIVLURTVNVLUMVIVKUGVGVKURTVHSHUSUTUGURTVIVAVBVC
      VLVDVEVF $.

    $( ` H ` is not the empty word.  (Contributed by Thierry Arnoux,
       14-Oct-2018.) $)
    signshnz $p |- ( ( F e. Word RR /\ C e. RR+ ) -> H =/= (/) ) $=
      ( wcel cc0 cr cword crp wa chash cfv wne c0 c1 caddc signshlen cn0 adantr
      co cn lencl nn0p1nn eqeltrd nnne0d wceq signshwrd hasheq0 necon3bid mpbid
      syl wb ) HUAUBZSZAUCSZUDZIUEUFZTUGIUHUGVJVKVJVKHUEUFZUIUJUNZUOABCDEFGHIJK
      LMNOPQRUKVJVLULSZVMUOSVHVNVIUAHUPUMVLUQVEURUSVJVKTIUHVJIVGSVKTUTIUHUTVFAB
      CDEFGHIJKLMNOPQRVAIVGVBVEVCVD $.

$(
    @{
      @( Value of the coefficient of ` H ` , corresponding to the word ` F `
         multiplied by ` ( x - C ) ` .  @)
      signhv @p |- ( ( F e. Word RR /\ I e. ( 1 ..^ ( # ` F ) ) )
        -> ( H ` I ) = ( ( F ` ( I - 1 ) ) - ( ( F ` I ) x. C ) ) ) @=
        ? @.

      @( Value of the lowest coefficient of ` H ` , corresponding to the word
         ` F ` multiplied by ` ( x - C ) ` .  @)
      signhv0 @p |- ( F e. Word RR -> ( H ` 0 ) = -u ( ( F ` 0 ) x. C ) ) @=
        ? @.

      @( The lowest coefficient of ` H ` cannot be zero .  @)
      signshn0 @p |- ( ( F e. Word RR /\ C e. RR+ ) -> ( H ` 0 ) =/= 0 ) @=
        ? @.

      @( Value of the highest coefficient of ` H ` , corresponding to the word
         ` F ` multiplied by ` ( x - C ) ` .  @)
      signhvn @p |- ( F e. Word RR ->
        ( H ` ( ( # ` H ) - 1 ) ) = ( F ` ( ( # ` F ) - 1 ) ) ) @=
        ? @.
    @}

    @{
      signhtv.n @e |- N = ( # ` F ) @.
      signhtv.j @e |- J = ( ( T ` F ) ` ( N - 2 ) ) @.
      signhtv.k @e |- K = ( ( T ` H ) ` ( N - 1 ) ) @.
      @( Lemma for ~ signwlem @)
      signhtv @p |- ( ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 )
        /\ ( F ` ( N - 1 ) ) = 0 ) -> J = K ) @=
        ? @.
    @}

    @( The rule of signs for words : value of the coefficient word for a
       monomial with one positive root ` C `  (Contributed by Thierry Arnoux,
       28-Sep-2018.) @)
    signwlem0g @p |- ( ( ( K e. RR /\ C e. RR+ ) /\ F = <" K "> ) ->
      H = <" -u ( K x. C ) K "> ) @=
      ( co cr wcel crp cs1 wceq cc0 cconcat cmul cofc cmin cof cneg oveq2 oveq1
      cs2 oveq1d oveq12d eqtrid adantl df-s2 eqcomi a1i simpl s1cld simpr rpred
      wa ofcccat ofcs1 syldan syl2anc recnd mul02d s1eqd eqtrd eqtr4di remulcld
      0re ofs2 syl22anc df-neg subid1d s2eqd 3eqtrd adantr ) JUAUBZAUCUBZVGZHJU
      DZUEZVGIUFUDZWIUGTZWIWKUGTZAUHUIZTZUJUKZTZJAUHTZULZJUOZWJIWQUEWHWJIWKHUGT
      ZHWKUGTZAWNTZWPTWQSWJXAWLXCWOWPHWIWKUGUMWJXBWMAWNHWIWKUGUNUPUQURUSWHWQWTU
      EWJWHWQUFJUOZWRUFUOZWPTZUFWRUJTZJUFUJTZUOZWTWHWLXDWOXEWPWLXDUEWHXDWLUFJUT
      VAVBWHWOWIAWNTZWKAWNTZUGTZXEWHUHUAUAWIWKAWHJUAWFWGVCZVDWHUFUAUFUAUBZWHVRV
      BZVDWHAWFWGVEVFZVHWHXLWRUDZWKUGTXEWHXJXQXKWKUGWFWGAUAUBZXJXQUEXPJAUHUAUAV
      IVJWHXKUFAUHTZUDZWKWHXNXRXKXTUEXOXPUFAUHUAUAVIVKWHXSUFWHAWHAXPVLVMVNVOUQW
      RUFUTVPVOUQWHXNWFWRUAUBXNXFXIUEXOXMWHJAXMXPVQXOUFJWRUFUJUAUAVSVTWHXGXHWSJ
      XGWSUEWHWSXGWRWAVAVBWHJWHJXMVLWBWCWDWEVO @.

    @( The rule of signs for words : change of signs for a monomial with one
       positive root ` C ` .  (Contributed by Thierry Arnoux, 28-Sep-2018.) @)
    signwlem0gv @p |- ( ( K e. ( RR \ { 0 } ) /\ C e. RR+ /\ F = <" K "> )
      -> ( V ` H ) = 1 ) @=
      ( cc0 cr csn cdif wcel crp cs1 wceq w3a cfv cneg cmul co cconcat chash c1
      clt wbr cif caddc cs2 simp1 eldifad simp2 simp3 signwlem0g syl21anc df-s2
      cmin eqtrdi fveq2d cword c0 wne renegcld s1cld s1nz a1i neneqd elsng syl
      wb mtbird eldifd s1fv recnd wa eldifsn sylib simprd negne0d eqnetrd rpred
      remulcld signsvfn signsvf1 csgn signstf0 s1len 1m1e0 fveq12d sgnclre 3syl
      oveq1d eqtrd eqeltrd sgnmul syl2anc cxr sgnsgn sgnmulrp2 oveq12d mulneg1d
      rexrd msqgt0d lt0neg2d mpbid sgnn 3eqtr3d 3eqtrd sgnnbi iftrue 0p1e1 ) JU
      ATUBZUCUDZAUEUDZHJUFUGZUHZIKUIJUJZUFZJAUKULZUFUMULZKUIZYIKUIZYIUNUIZUOVHU
      LZYICUIZUIZYJUKULZTUPUQZUOTURZUSULZUOYGIYKKYGIYHYJUTZYKYGJUAUDZYEYFIUUBUG
      YGJUAYCYDYEYFVAZVBZYDYEYFVCZYDYEYFVDABCDEFGHIJKLMNOPQRSVEVFYHYJVGVIVJYGYI
      UAVKZVLUBZUCUDTYIUIZTVMYJUAUDZYLUUAUGYGYIUUGUUHYGYHUAYGJUUEVNZVOZYGYIUUHU
      DZYIVLUGZYGYIVLYIVLVMYGYHVPVQVRYGYIUUGUDUUMUUNWAUULYIVLUUGVSVTWBWCYGUUIYH
      TYGYHUAUDZUUIYHUGUUKYHUAWDVTYGJYGJUUEWEZYGUUCJTVMZYGYDUUCUUQWFUUDJUATWGWH
      WIZWJWKYGJAUUEYGAUUFWLWMZBCDEFGYIYJKLMNOPQRWNVFYGUUATUOUSULUOYGYMTYTUOUSY
      GUUOYMTUGUUKBCDEFGYHKLMNOPQRWOVTYGYSYTUOUGYGYRWPUIZUOUJZUGZYSYGUUTYQWPUIZ
      YJWPUIZUKULZYHWPUIZJWPUIZUKULZUVAYGYQUAUDUUJUUTUVEUGYGYQUVFUAYGYQTUVFUFZU
      IZUVFYGYOTYPUVIYGUUOYPUVIUGUUKBCDEFGYHKLMNOPQRWQVTYGYOUOUOVHULTYGYNUOUOVH
      YNUOUGYGYHWRVQXCWSVIWTYGUUOUVFUAUDZUVJUVFUGUUKYHXAZUVFUAWDXBXDZYGUUOUVKUU
      KUVLVTXEZUUSYQYJXFXGYGUVCUVFUVDUVGUKYGUVCUVFWPUIZUVFYGYQUVFWPUVMVJYGYHXHU
      DUVOUVFUGYGYHUUKXMYHXIVTXDYGUUCYEUVDUVGUGUUEUUFJAXJXGXKYGYHJUKULZWPUIZJJU
      KULZUJZWPUIZUVHUVAYGUVPUVSWPYGJJUUPUUPXLVJYGUUOUUCUVQUVHUGUUKUUEYHJXFXGYG
      UVSXHUDUVSTUPUQZUVTUVAUGYGUVSYGUVRYGJJUUEUUEWMZVNXMYGTUVRUPUQUWAYGJUUEUUR
      XNYGUVRUWBXOXPUVSXQXGXRXSYGYRXHUDUVBYSWAYGYRYGYQYJUVNUUSWMXMYRXTVTXPYSUOT
      YAVTXKYBVIXS @.

    @( The rule of signs for words : initial step.  (Contributed by Thierry
       Arnoux, 28-Sep-2018.) @)
    signwlem0 @p |- ( ( K e. ( RR \ { 0 } ) /\ C e. RR+ /\ F = <" K "> )
      -> ( ( V ` F ) < ( V ` H )  /\ -. 2 || ( ( V ` H ) - ( V ` F ) ) ) ) @=
      ( c2 cr cc0 csn cdif wcel crp cs1 wceq w3a cfv clt cmin co cdvds wn c1
      wbr 0lt1 simp3 fveq2d simp1 eldifad signsvf1 syl eqtrd signwlem0gv mpbiri
      breq12d cz 2z iddvds ax-mp caddc wb 1z oddp1even 1p1e2 breq2i bitri mpbir
      ax-1cn subid1i notbii oveq12d breq2d notbid jca ) JUAUBUCZUDUEZAUFUEZHJUG
      ZUHZUIZHKUJZIKUJZUKUQZTWOWNULUMZUNUQZUOZWMWPUBUPUKUQURWMWNUBWOUPUKWMWNWKK
      UJZUBWMHWKKWIWJWLUSUTWMJUAUEWTUBUHWMJUAWHWIWJWLVAVBBCDEFGJKLMNOPQRVCVDVEZ
      ABCDEFGHIJKLMNOPQRSVFZVHVGWMWSTUPUBULUMZUNUQZUOZXETUPUNUQZUOZXGTTUNUQZTVI
      UEXHVJTVKVLXGTUPUPVMUMZUNUQZXHUPVIUEXGXJVNVOUPVPVLXITTUNVQVRVSVTXDXFXCUPT
      UNUPWAWBVRWCVTWMWRXDWMWQXCTUNWMWOUPWNUBULXBXAWDWEWFVGWG @.

    @{
      signs.g @e |- G =
        ( ( <" 0 "> ++ E ) oF - ( ( E ++ <" 0 "> ) oFC x. C ) ) @.
      signs.n @e |- N = ( # ` E ) @.
      signs.j @e |- Z = ( E ` ( N - 1 ) ) @.

      signwlem.1 @e |- ( ph -> E e. ( Word RR \ { (/) } ) ) @.
      signwlem.2 @e |- ( ph -> ( E ` 0 ) =/= 0 ) @.
      signwlem.3 @e |- ( ph -> F = ( E ++ <" K "> ) ) @.
      signwlem.4 @e |- ( ph -> K e. RR ) @.
      signwlem.5 @e |- ( ph -> C e. RR+ ) @.
      @( The words with an additional positive root, ` G ` and ` H ` , have a
         common subword. @)
      signwlems @p |- ( ph -> ( G |` ( 0 ..^ N ) ) = ( H |` ( 0 ..^ N ) ) ) @=
        ? @.

      @( Decompose ` G ` into highest letter and common subword. @)
      signwlemg @p |- ( ph -> G = ( ( G |` ( 0 ..^ N ) ) ++ <" Z "> ) ) @=
        ? @.

      @( Decompose ` H ` into highest 2 letters and common subword. @)
      signwlemh @p |- ( ph -> H = ( ( G |` ( 0 ..^ N ) ) ++
        <" ( Z - ( K x. C ) ) K "> ) ) @=
        ? @.

      @( Main Lemma for fhe rule of signs : multiplying by a polynomial
         ` ( x .- C ) ` has the same effect on words of length ` ( N + 1 ) ` .
         (Contributed by Thierry Arnoux, 30-Sep-2018.) @)
      signwlem @p |- ( ph -> ( ( ( V ` H ) - ( V ` G ) )
        - ( ( V ` F ) - ( V ` E ) ) ) e. { 0 , 2 } ) @=
        ( cfv cmin co cc0 c2 wcel cmul wceq wa cn0 cr wf a1i cs1 cconcat c0 syl
        syl2anc eqeltrd signshwrd ffvelcdmd adantr nn0cnd cfzo cres simpr
        oveq1d
        cs2 cc recnd mul02d eqtrd oveq2d c1 chash wrdf cn wne eldifsn sylib cfn
        wb wrdfin hashnncl 3syl mpbird eqeltrid eqtrdi cfz caddc sselid eqtr4di
        eleqtrrd s1cld 0re syl3anc fveq2d jca sylibr signlem0 subeq0bd eqeltrdi
        oveq12d adantlr simpll wo biimpa imp remulcld ad2antrr mulne0d syl21anc
        mulcld clt simplll simplr cneg msqgt0d mulassd mpbid eqtr3d eqcomd csgn
        wbr eqid rexrd mpjaodan pm2.61dane cpr signsvvf crp eldifad s1cl ccatcl
        cword csn rpred cdif simprd fzo0end oveq2i eleqtrdi subid1d s2eqd df-s2
        signwlemh cop csubstr fzssp1 hashcl eluzfz2 nn0uz eleq2s 4syl signshlen
        cuz oveq1i swrd0valOLD swrdcl eqeltrrd ccatass signwlemg signshnz
        signshn0
        3eqtr4d eqtr4d ffvelcdm sylancr s1eqd subidi c0ex prid1 wn df-ne
        mul0ord
        wi df-or biimtrid necon1d resubcld signstf fzossfz cz nnzd fzval3
        eleqtrd
        0cn signstlen rpne0 necomd neeq1d subne0d signstfvneq0 pm2.21d mulneg2d
        neneqd w3a rpgt0 mulgt0d breqtrd lt0neg2d eqbrtrd 3jca
        swrd0lenOLD signhv0
        df-neg ccatlen eqcomi s1len oveq12i 3eqtrd lbfzo0 fveq1d eqnetrd mulne0
        peano2nnd ccatval1 syl22anc negne0d fvres cvv signstres sylancl fveq12d
        signlem3 sylancom eqtr3id signstfveq0 signhtv sgnmul sgnmulrp2 mulneg1d
        sgnclre sgnneg 3eqtr2rd negcon1ad ax-1cn cxr sgnnbi sgnpbi signsvtp 2cn
        subid1i 2re elexi prid2 signlem4 negeqd signsvtn 1m1e0 lttri2d ltmul1dd
        mulcomd 3brtr3d ltned mulne0bad lttrd posdifd subdird breqtrrd signlem2
        ovex mpdan signsvfnn signsvfpn signlem1 elpr ) ALOUMZKOUMZUNUOZJOUMZIOU
        MZUNUOZUNUOZUPUQUUAZURZQMUSUOZUPAVWIUPUTZVAZVWHMUPAMUPUTZVWHVWJAVWLVAZV
        WFUPVWGVWMVWFUPUPUNUOZUPVWMVWBUPVWEUPUNVWMVVTVWAVWMVVTAVVTVBURVWLAVCUUG
        ZVBLOVWOVBOVDZACDEFGHOPRSTUAUBUCUUBZVEAJVWOURZBUUCURZLVWOURAJIMVFZVGUOZ
        VWOUJAIVWOURZVWTVWOURZVXAVWOURAIVWOVHUUHZUHUUDZAMVCURZVXCUKMVCUUEVIZVCI
        VWTUUFVJVKZULBCDEFGHJLOPRSTUAUBUCUDVLVJVMVNVOVWMVVTKUPVFZVGUOZOUMZVWAVW
        MLVXJOVWMLKUPNVPUOZVQZQVFZVGUOZVXIVGUOZVXJVWMVXMQMBUSUOZUNUOZMVTZVGUOZV
        XMVXNVXIVGUOZVGUOZLVXPVWMVXSVYAVXMVGVWMVXSQUPVTVYAVWMVXRMQUPVWMVXRQUPUN
        UOQVWMVXQUPQUNVWMVXQUPBUSUOZUPVWMMUPBUSAVWLVRZVSVWMBABWAURZVWLABABULUUI
        ZWBZVNWCWDWEVWMQAQWAURZVWLAQAQNWFUNUOZIUMZVCUGAUPIWGUMZVPUOZVCVYIIAVXBV
        YLVCIVDVXEVCIWHVIAVYIVXLVYLANWIURVYIVXLURZANVYKWIUFAVYKWIURZIVHWJZAVXBV
        YOAIVWOVXDUUJZURZVXBVYOVAUHIVWOVHWKWLUUKAVXBIWMURZVYNVYOWNVXEVCIWOZIWPW
        QWRZWSZNUULVIZNVYKUPVPUFUUMUUNVMWSZWBZVNUUOWDVYDUUPQUPUUQWTWEALVXTUTVWL
        ABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUURZVNAVXPVYBUTZVWLAVXMVWOU
        RZVXNVWOURVXIVWOURWUFAKUPNUUSUUTUOZVXMVWOAKVWOURZNUPKWGUMZXAUOZURZWUHVX
        MUTAVXBVWSWUIVXEULBCDEFGHIKOPRSTUAUBUCUEVLVJZANUPNWFXBUOZXAUOZWUKAUPNXA
        UOZWUONUPNUVAAVXBVYRNVBURNWUPURZVXEVYSVYRNVYKVBUFIUVBWSWUQNUPUVHUMVBUPN
        UVCUVDUVEUVFXCAWUJWUNUPXAAWUJVYKWFXBUOZWUNAVXBVWSWUJWURUTVXEULBCDEFGHIK
        OPRSTUAUBUCUEUVGVJNVYKWFXBUFUVIXDZWEXEZVCKNUVJVJZAWUIWUHVWOURWUMVCKUPNU
        VKVIUVLZAQVCWUCXFAUPVCUPVCURZAXGVEZXFVCVXMVXNVXIUVMXHVNUVQVWMKVXOVXIVGA
        KVXOUTVWLABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUVNZVNVSUVRXIAVXKV
        WAUTZVWLAKVYPURZUPKUMUPWJZWVFAWUIKVHWJZVAWVGAWUIWVIWUMAVXBVWSWVIVXEULBC
        DEFGHIKOPRSTUAUBUCUEUVOVJXJKVWOVHWKXKZAVXBVWSWVHVXEULBCDEFGHIKOPRSTUAUB
        UCUEUVPVJZCDEFGHKOPRSTUAUBUCXLVJVNWDXMVWMVWCVWDAVWCWAURZVWLAVWCAVWPVWRV
        WCVBURVWQVXHVWOVBJOUVSUVTVOZVNVWMVWCIVXIVGUOZOUMZVWDVWMJWVNOVWMJVXAWVNA
        JVXAUTVWLUJVNVWMVWTVXIIVGVWMMUPVYDUWAWEWDXIAWVOVWDUTZVWLAVYQUPIUMZUPWJZ
        WVPUHUICDEFGHIOPRSTUAUBUCXLVJVNWDXMXOUPUWSUWBZWTUPUQUWCUWDZXNXPVWKMUPWJ
        ZVAAWWAQUPUTZVWHAVWJWWAXQVWKWWAVRVWKWWAWWBVWKQUPMUPQUPWJWWBUWEZVWKVWLQU
        PUWFVWKWWBVWLXRZWWCVWLUWHAVWJWWDAQMWUDAMUKWBZUWGXSWWBVWLUWIWLUWJUWKXTAW
        WAVAZWWBVAZVWHVXRVYIKDUMZUMZUSUOZUPWWGWWJUPUTZVWHWWGWWKVWHWWGWWJUPWWGVX
        RWWIWWFVXRWAURWWBWWFVXRAVXRVCURZWWAAQVXQWUCAMBUKVYFYAZUWLZVNWBVNWWGWWIA
        WWIVCURZWWAWWBAUPWWHWGUMZVPUOZVCVYIWWHAWUIWWHVWOURWWQVCWWHVDWUMCDEFGHKO
        PRSTUAUBUCUWMVCWWHWHWQAVYIUPWUNVPUOZWWQAVYIWUPWWRAVXLWUPVYIUPNUWNWUBXCA
        NUWOURWUPWWRUTANWUAUWPUPNUWQVIUWRZAWWPWUNUPVPAWWPWUJWUNAWUIWWPWUJUTWUMC
        DEFGHKOPRSTUAUBUCUWTVIWUSWDWEXEVMZYBWBWWGQVXQAVYHWWAWWBWUDYBAVXQWAURWWA
        WWBAMBWWEVYGYEZYBZWWGQVXQWJUPVXQWJZWWFWXCWWBWWFVXQUPWWFMBAMWAURZWWAWWEV
        NAVYEWWAVYGVNAWWAVRZABUPWJZWWAAVWSWXFULBUXAVIZVNYCUXBVNWWGQUPVXQWWFWWBV
        RZUXCWRUXDAWWBWWIUPWJZWWAAWWBVAZWVGWVHVYIUPWUJVPUOZURZWXIAWVGWWBWVJVNAW
        VHWWBWVKVNAWXLWWBAVYIWWRWXKWWSAWUJWUNUPVPWUSWEXEVNCDEFGHKVYIOPRSTUAUBUC
        UXEYDXPYCUXHUXFXTWWGWWJUPWJZVAWWJUPYFYPZVWHUPWWJYFYPZWWGWXNVWHWXMWWGWXN
        VAZVWFUQVWGWXPVWFUQUPUNUOZUQWXPVWBUQVWEUPUNWWGWXNAWWBMVXRUSUOZUPYFYPZUX
        IZVWBUQUTZWXPAWWBWXSAWWAWWBWXNYGZWWFWWBWXNYHWWGWXSWXNWWGWXRMVXQUSUOZYIZ
        UPYFWWGWXRMVXQYIZUSUOWYDWWGVXRWYEMUSWWGVXRUPVXQUNUOWYEWWGQUPVXQUNWXHVSV
        XQUXRXDZWEWWGMVXQAWXDWWAWWBWWEYBZWXBUXGWDWWGUPWYCYFYPWYDUPYFYPWWGUPMMUS
        UOZBUSUOWYCYFWWGWYHBWWGMMAVXFWWAWWBUKYBZWYIYAABVCURZWWAWWBVYFYBZWWGMWYI
        WWFWWAWWBWXEVNYJAUPBYFYPZWWAWWBAVWSWYLULBUXJVIYBUXKWWGMMBWYGWYGAVYEWWAW
        WBVYGYBYKUXLWWGWYCWWGMVXQWYIWWGMBWYIWYKYAZYAUXMYLUXNZVNUXOACDEFGHVXMKLW
        WIOPMVXRQRSTUAUBUCUKWWNWUCWVEWUEAWUGVXMVHWJZVAVXMVYPURAWUGWYOWVBAVXMWGU
        MZWIURZWYOAWYPNWIAWUHWGUMZWYPNAWUHVXMWGWVAXIAWUIWULWYRNUTWUMWUTVCKNUXPV
        JYMZWUAVKAWUGVXMWMURWYQWYOWNWVBVCVXMWOVXMWPWQYLXJVXMVWOVHWKXKZAUPLUMZUP
        JUMZBUSUOZYIZUPAVWRXUAXUDUTVXHBCDEFGHJLOPRSTUAUBUCUDUXQVIAXUCAXUBBAXUBA
        UPJWGUMZVPUOZVCUPJAVWRXUFVCJVDVXHVCJWHVIAXUEWIURUPXUFURAXUEWUNWIAXUEVXA
        WGUMZVYKVWTWGUMZXBUOZWUNAJVXAWGUJXIAVXBVXCXUGXUIUTVXEVXGVCIVWTUXSVJXUIW
        UNUTAVYKNXUHWFXBNVYKUFUXTMUYAUYBVEUYCANWUAUYHVKXUEUYDXKVMWBZVYGYEAXUBWA
        URXUBUPWJVYEWXFXUCUPWJXUJAXUBWVQUPAXUBUPVXAUMZWVQAUPJVXAUJUYEAVXBVXCUPV
        YLURZXUKWVQUTVXEVXGAVYNXULVYTVYKUYDXKVCIVWTUPUYIXHWDUIUYFVYGWXGXUBBUYGU
        YJUYKUYFZAVYIWWHVXLVQZUMZWWIWYPWFUNUOZVXMDUMZUMAVYMXUOWWIUTWUBVYIVXLWWH
        UYLVIAVYIXUPXUNXUQAWUIVXLUYMURXUNXUQUTWUMUPNVPVVNVXLCDEFGHKOPRSTUAUBUCU
        YNUYOANWYPWFUNAWYPNWYSYNVSUYPYMZUYQUYRWXPVWCVWDWXPAWVLWYBWVMVIWXPAUPMVY
        IIDUMZUMZUSUOZYFYPZVWCVWDUTWYBWXPXVAYOUMZWFUTZXVBWXPXVCWWJYOUMZYIZWFWWG
        XVCXVFUTZWXNWWGXVCMYOUMZXUTYOUMZUSUOZXVFWWGVXFXUTVCURZXVCXVJUTWYIWWGXUT
        WWIVCWWGAWWBXUTWWIUTAWWAWWBXQZWXHWXJXUTNUQUNUOXUSUMZWWIWXJVYQWVRVYJUPUT
        ZXUTXVMUTAVYQWWBUHVNZAWVRWWBUIVNZWXJVYJQUPUGAWWBVRUYSZCDEFGHINOPRSTUAUB
        UCUFUYTYDWXJVYQWVRXVNXVMWWIUTXVOXVPXVQBCDEFGHIKXVMWWINOPRSTUAUBUCUEUFXV
        MYQWWIYQVUAYDWDVJZWWGAWWOXVLWWTVIZVKZMXUTVUBVJWWGXVJVXQYOUMZWWIYOUMZUSU
        OZXVFWWGXVHXWAXVIXWBUSWWGXWAXVHWWGVXFVWSXWAXVHUTWYIWWGAVWSXVLULVIMBVUCV
        JYNWWGXUTWWIYOXVRXIXOWWGXVFXWCWWGXWCXVEWWGXWAXWBWWGXWAWWGAVXQVCURZXWAVC
        URXVLWWMVXQVUEWQWBZWWGXWBWWGWWOXWBVCURXVSWWIVUEVIWBZYEWWGXVEVXRYOUMZXWB
        USUOZXWAYIZXWBUSUOXWCYIWWGAXVEXWHUTZXVLAWWLWWOXWJWWNWWTVXRWWIVUBVJVIWWG
        XWIXWGXWBUSWWGWYEYOUMZXWIXWGWWGXWDXWKXWIUTWYMVXQVUFVIWWGWYEVXRYOWWGVXRW
        YEWYFYNXIYMVSWWGXWAXWBXWEXWFVUDVUGVUHYNWDWDZVNWXPWFXVEWFWAURWXPVUIVEWXP
        XVEWFYIZWXPXVEXWMUTZWXNWWGWXNVRWXPWWJVUJURZXWNWXNWNWWGXWOWXNWWGWWJWWGVX
        RWWIWWGAWWLXVLWWNVIXVSYAYRZVNWWJVUKVIWRYNVUHWDWXPXVAVUJURZXVDXVBWNWXPXV
        AWXPMXUTWXPAVXFWYBUKVIWWGXVKWXNXVTVNYAYRXVAVULVIYLAMXUTCDEFGHIJNOPRSTUA
        UBUCUHUIUJUKUFXUTYQZVUMVJXMXOUQVUNVUOZWTUPUQUQVCVUPVUQVURZXNXPWWGWXOVWH
        WXMWWGWXOVAZVWFUPVWGXXAVWFWFWFUNUOZUPXXAVWBWFVWEWFUNWWGWXOWXTVWBWFUTZXX
        AAWWBWXSAWWAWWBWXOYGZWWFWWBWXOYHWWGWXSWXOWYNVNUXOACDEFGHVXMKLWWIOPMVXRQ
        RSTUAUBUCUKWWNWUCWVEWUEWYTXUMXURVUSUYRXXAAXVAUPYFYPZVWEWFUTXXDXXAXVCXWM
        UTZXXEXXAXVCXVFXWMWWGXVGWXOXWLVNXXAXVEWFXXAXVEWFUTZWXOWWGWXOVRXXAXWOXXG
        WXOWNWWGXWOWXOXWPVNWWJVULVIWRVUTWDXXAXWQXXFXXEWNWWGXWQWXOWWGXVAWWGMXUTW
        YIXVTYAYRVNXVAVUKVIYLAMXUTCDEFGHIJNOPRSTUAUBUCUHUIUJUKUFXWRVVAVJXOVVBWT
        WVTXNXPWWFWXMWXNWXOXRZWWBAWXMXXHWWAAWXMXXHAWWJUPAVXRWWIWWNWWTYAWVDVVCXS
        XPXPYSYTYDYTAVWIUPWJZVAVWIUPYFYPZVWHUPVWIYFYPZAXXJVWHXXIAXXJVAZVWFUPVWG
        XXLVWFXXBUPXXLVWBWFVWEWFUNXXLUPVXRQUSUOZYFYPXXCXXLUPQQUSUOZVXQQUSUOZUNU
        OZXXMYFXXLXXOXXNYFYPZUPXXPYFYPZXXLXXOUPXXNXXLVXQQXXLMBAVXFXXJUKVNZAWYJX
        XJVYFVNYAAQVCURXXJWUCVNZYAWVCXXLXGVEZXXLQQXXTXXTYAXXLVWIBUSUOZVYCXXOUPY
        FXXLVWIUPBXXLQMXXTXXSYAZXYAAVWSXXJULVNAXXJVRZVVDAXYBXXOUTXXJAXYBQVXQUSU
        OXXOAQMBWUDWWEVYGYKAQVXQWUDWXAVVEWDVNXXLBAVYEXXJVYGVNWCVVFXXLQXXTXXLQMA
        VYHXXJWUDVNAWXDXXJWWEVNXXLVWIUPXYCXYDVVGVVHYJVVIAXXQXXRWNXXJAXXOXXNAVXQ
        QWWMWUCYAAQQWUCWUCYAVVJVNYLAXXMXXPUTXXJAQVXQQWUDWXAWUDVVKVNVVLACDEFGHVX
        MKLOPMVXRQRSTUAUBUCUKWWNWUCWVEWUEWYTXUMVVMVVOAMQCDEFGHIJNOPRSTUAUBUCUHU
        IUJUKUFUGVVPXOVVBWTWVTXNXPAXXKVWHXXIAXXKVAZVWBUPUTZVWHWYAXYEXYFVAZVWFUP
        VWGXYGVWFVWNUPXYGVWBUPVWEUPUNXYEXYFVRXYEVWEUPUTZXYFXYEVWCVWDAWVLXXKWVMV
        NAMQCDEFGHIJNOPRSTUAUBUCUHUIUJUKUFUGVVQXMZVNXOWVSWTWVTXNXYEWYAVAZVWFUQV
        WGXYJVWFWXQUQXYJVWBUQVWEUPUNXYEWYAVRXYEXYHWYAXYIVNXOXWSWTXWTXNXYEVWBVWG
        URXYFWYAXRACDEFGHVXMKLOPMVXRQRSTUAUBUCUKWWNWUCWVEWUEWYTXUMVVRVWBUPUQVVT
        VWAUNVVNVVSWLYSXPAXXIXXJXXKXRAVWIUPAQMWUCUKYAWVDVVCXSYSYT @.

      signwlemn.1 @e |- ( ph -> ( V ` E ) < ( V ` G ) ) @.
      signwlemn.2 @e |- ( ph -> -. 2 || ( ( V ` G ) - ( V ` E ) ) ) @.
      @( The rule of signs for words : induction step.  (Contributed by Thierry
         Arnoux, 27-Sep-2018.) @)
      signwlemn @p |- ( ph
        -> ( ( V ` F ) < ( V ` H )  /\ -. 2 || ( ( V ` H ) - ( V ` F ) ) ) ) @=
        ( cfv cr cword cn0 wf signsvvf a1i c0 csn eldifad ffvelcdmd cconcat
        wcel
        cs1 s1cl syl ccatcl syl2anc eqeltrd crp signshwrd clt wbr cmin cdvds
        co c2 wn jca chash c1 eqid signwlem signslema ) AIOUOZJOUOKOUOZLOUOAUPU
        QZURIOWKUROUSACDEFGHOPRSTUAUBUCUTVAZAIWKVBVCUHVDZVEAWKURJOWLAJIMVHZVFVT
        ZWKUJAIWKVGZWNWKVGZWOWKVGWMAMUPVGWQUKMUPVIVJUPIWNVKVLVMZVEAWKURKOWLAWPB
        VNVGZKWKVGWMULBCDEFGHIKOPRSTUAUBUCUEVOVLVEAWKURLOWLAJWKVGWSLWKVGWRULBCD
        EFGHJLOPRSTUAUBUCUDVOVLVEAWIWJVPVQWAWJWIVRVTVSVQWBUMUNWCABCDEFGHIJKLMIW
        DUOZOPWTWEVRVTIUOZRSTUAUBUCUDUEWTWFXAWFUHUIUJUKULWGWH @.
    @}

    @{
      @d e f k C @.  @d e f k V @.  @d f F @.  @d f H @.
      @( The rule of signs for words : multiplying by a polynomial
         ` ( x .- C ) ` changes the parity of the number of sign changes.
         (Contributed by Thierry Arnoux, 27-Sep-2018.) @)
      signw @p |- ( ( F e. ( Word RR \ { (/) } ) /\ ( F ` 0 ) =/= 0 /\ C e. RR+
      ) -> ( ( V ` F ) < ( V ` H )  /\ -. 2 || ( ( V ` H ) - ( V ` F ) ) ) ) @=
        ( cc0 co ve vk cr cword c0 csn cdif cfv wne crp w3a clt wbr c2 cdvds
        wcel cmin wn simp1 eldifad eldifsn sylib simprd simp2 simp3 cs1 cconcat
        wa cv cmul cofc cof wceq neeq1 fveq1 neeq1d 3anbi12d imbi1d fveq2 oveq2
        oveq1 oveq1d oveq12d fveq2d breq12d breq2d notbid anbi12d imbi12d neirr
        eqtr4di con3i ax-mp pm2.21i simpllr simpr s1cl ccatlid 3syl fveq1d s1fv
        wi eqtrd syl simplr2 eqnetrrd jca sylibr simplr3 eqid signwlem0 syl3anc
        adantllr simplll velsn necon3bbii chash cfzo s1cld hashgt0 syl2anc cz
        wb
        eldifd 0z cfn wrdfin hashcl fzolb2 sylancr mpbird ccatval1 3jca simp-4r
        nn0zd mpd c1 simp11 simpl2 ex 3adant3 eqidd simp13 signwlemn pm2.61dane
        simp3l simp3r wrdind imp syl13anc ) HUCUDZUEUFZUGZUPZSHUHZSUIZAUJUPZUKZ
        HUUKUPZHUEUIZUUPUUQHJUHZIJUHZULUMZUNUVBUVAUQTZUOUMZURZVHZUURHUUKUULUUNU
        UPUUQUSZUTUURUUSUUTUURUUNUUSUUTVHUVHHUUKUEVAVBVCUUNUUPUUQVDUUNUUPUUQVEU
        USUUTUUPUUQUKZUVGDVIZUEUIZSUVJUHZSUIZUUQUKZUVJJUHZSVFZUVJVGTZUVJUVPVGTZ
        AVJVKZTZUQVLZTZJUHZULUMZUNUWCUVOUQTZUOUMZURZVHZXBUEUEUIZSUEUHZSUIZUUQUK
        ZUWHXBUAVIZUEUIZSUWMUHZSUIZUUQUKZUWMJUHZUVPUWMVGTZUWMUVPVGTZAUVSTZUWATZ
        JUHZULUMZUNUXCUWRUQTZUOUMZURZVHZXBZUWMUBVIZVFZVGTZUEUIZSUXLUHZSUIZUUQUK
        ZUXLJUHZUVPUXLVGTZUXLUVPVGTZAUVSTZUWATZJUHZULUMZUNUYBUXQUQTZUOUMZURZVHZ
        XBZUVIUVGXBDUAUBHUCUVJUEVMZUVNUWLUWHUYIUVKUWIUVMUWKUUQUVJUEUEVNUYIUVLUW
        JSSUVJUEVOVPVQVRUVJUWMVMZUVNUWQUWHUXHUYJUVKUWNUVMUWPUUQUVJUWMUEVNUYJUVL
        UWOSSUVJUWMVOVPVQUYJUWDUXDUWGUXGUYJUVOUWRUWCUXCULUVJUWMJVSZUYJUWBUXBJUY
        JUVQUWSUVTUXAUWAUVJUWMUVPVGVTUYJUVRUWTAUVSUVJUWMUVPVGWAWBWCWDZWEUYJUWFU
        XFUYJUWEUXEUNUOUYJUWCUXCUVOUWRUQUYLUYKWCWFWGWHWIUVJUXLVMZUVNUXPUWHUYGUY
        MUVKUXMUVMUXOUUQUVJUXLUEVNUYMUVLUXNSSUVJUXLVOVPVQUYMUWDUYCUWGUYFUYMUVOU
        XQUWCUYBULUVJUXLJVSZUYMUWBUYAJUYMUVQUXRUVTUXTUWAUVJUXLUVPVGVTUYMUVRUXSA
        UVSUVJUXLUVPVGWAWBWCWDZWEUYMUWFUYEUYMUWEUYDUNUOUYMUWCUYBUVOUXQUQUYOUYNW
        CWFWGWHWIUVJHVMZUVNUVIUWHUVGUYPUVKUUTUVMUUPUUQUVJHUEVNUYPUVLUUOSSUVJHVO
        VPVQUYPUWDUVCUWGUVFUYPUVOUVAUWCUVBULUVJHJVSZUYPUWBIJUYPUWBUVPHVGTZHUVPV
        GTZAUVSTZUWATIUYPUVQUYRUVTUYTUWAUVJHUVPVGVTUYPUVRUYSAUVSUVJHUVPVGWAWBWC
        RWKWDZWEUYPUWFUVEUYPUWEUVDUNUOUYPUWCUVBUVOUVAUQVUAUYQWCWFWGWHWIUWLUWHUW
        IURUWLURUEWJUWLUWIUWIUWKUUQUSWLWMWNUWMUUKUPZUXJUCUPZVHZUXIUYHVUDUXIVHZU
        XPUYGVUEUXPVHZUYGUWMUEVUDUXPUWMUEVMZUYGUXIVUDUXPVHZVUGVHZUXJUCSUFUGUPZU
        UQUXLUXKVMUYGVUIVUCUXJSUIZVHVUJVUIVUCVUKVUBVUCUXPVUGWOZVUIUXNUXJSVUIUXN
        SUXKUHZUXJVUISUXLUXKVUIUXLUEUXKVGTZUXKVUIUWMUEUXKVGVUHVUGWPWBVUIVUCUXKU
        UKUPZVUNUXKVMVULUXJUCWQUCUXKWRWSXCZWTVUIVUCVUMUXJVMVULUXJUCXAXDXCUXMUXO
        UUQVUDVUGXEXFXGUXJUCSVAXHUXMUXOUUQVUDVUGXIVUPABCDEFGUXLUYAUXJJKLMNOPQUY
        AXJZXKXLXMVUFUWNVHZUWMUUMUPZUWPUUQUKZVUCUXHUYGVUDUXPUWNVUTUXIVUHUWNVHZV
        USUWPUUQVVAUWMUUKUULVUBVUCUXPUWNXNZVVAUWNUWMUULUPZURVUHUWNWPZVVCUWMUEUA
        UEXOXPXHYDVVAUXNUWOSVVAVUBVUOSSUWMXQUHZXRTUPZUXNUWOVMVVBVVAUXJUCVUBVUCU
        XPUWNWOXSVVAVVFSVVEULUMZVVAVUBUWNVVGVVBVVDUWMUUKXTYAVVASYBUPVVEYBUPZVVF
        VVGYCYEVVAVUBUWMYFUPZVVHVVBUCUWMYGVVIVVEUWMYHYOWSSVVEYIYJYKUCUWMUXKSYLX
        LUXMUXOUUQVUDUWNXEXFZUXMUXOUUQVUDUWNXIZYMXMVUBVUCUXIUXPUWNYNVURUWQUXHVU
        RUWNUWPUUQVUDUXPUWNUWNUXIVVDXMVUDUXPUWNUWPUXIVVJXMVUDUXPUWNUUQUXIVVKXMY
        MVUDUXIUXPUWNWOYPVUTVUCUXHUKZABCDEFGUWMUXLUXBUYAUXJVVEJKVVEYQUQTUWMUHZL
        MNOPQVUQUXBXJVVEXJVVMXJVUSUWPUUQVUCUXHYRVUTVUCUWPUXHVUSUWPUUQVUCYSUUAVV
        LUXLUUBVUTVUCUXHVDVUSUWPUUQVUCUXHUUCVUTVUCUXDUXGUUFVUTVUCUXDUXGUUGUUDXL
        UUEYTYTUUHUUIUUJ @.
    @}
  $)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Sign changes in a polynomial with real coefficients
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

$(
  @{
    signs.p @e |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 }
      |-> if ( b = 0 , a , b ) ) @.
    signs.w @e |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. ,
      <. ( +g ` ndx ) , .+^ >. } @.
    signs.t @e |- T = ( w e. Word RR |-> ( n e. ( 0 ..^ ( # ` w ) ) |->
      ( W gsum ( i e. ( 0 ..^ n ) |-> ( sgn ` ( w ` i ) ) ) ) ) ) @.
    signs.u @e |- U = ( w e. Word RR |-> sum_ j e. ( 1 ..^ ( # ` w ) )
      if ( ( ( T ` w ) ` j ) =/= ( ( T ` w ) ` ( j - 1 ) ) , 1 , 0 ) ) @.
    signs.v @e |- V = ( f e. ( Poly ` RR ) |->
      ( U ` ( ( coeff ` f ) |` ( 0 ... ( deg ` f ) ) ) ) ) @.

    @( Sign changes for a polynomial.  (Contributed by Thierry Arnoux,
       20-Sep-2018.) @)
    signsvf @p |- V : ( Poly ` RR ) --> NN0 @=
      ? @.

    @( Sign changes for a polynomial.  (Contributed by Thierry Arnoux,
       20-Sep-2018.) @)
    signsvval @p |- ( F e. ( Poly ` RR )
      -> ( V ` F ) = ( U ` ( ( coeff ` F ) |` ( 0 ... ( deg ` F ) ) ) ) ) @=
      ? @.

    @( Multiplying a polynomial by ` Xp ` does not change the parity of the
       sign changes.  (Contributed by Thierry Arnoux, 20-Sep-2018.) @)
    signsmulx @p |- ( F e. ( ( Poly ` RR ) \ { 0p } )
      -> ( V ` ( F oF x. Xp ) ) = ( V ` F ) ) @=
      ? @.

    signs.z @e |- Z = ( ( `' F " { 0 } ) i^i RR+ ) @.
    signs.l @e |- L = ( ( V ` F ) - ( # ` Z ) ) @.

    @( Descartes's rule of signs, initial step.  @)
    signsz0 @p |- ( ( F e. ( ( Poly ` RR ) \ { 0p } ) /\ ( # ` Z ) = 0 )
      -> ( 0 <_ L /\ 2 || L ) ) @=
      ? @.

    @{
      signszn.y @e |- Y = ( ( `' G " { 0 } ) i^i RR+ ) @.
      signszn.k @e |- K = ( ( V ` G ) - ( # ` Y ) ) @.
      signszn.1 @e |- ( ( G e. ( ( Poly ` RR ) \ { 0p } )
        /\ ( # ` Y ) = N ) -> ( 0 <_ K /\ 2 || K ) ) @.
      @( Descartes's rule of signs, induction step.  @)
      signszn @p |- ( ( F e. ( ( Poly ` RR ) \ { 0p } )
        /\ ( # ` Z ) = ( N + 1 ) ) -> ( 0 <_ L /\ 2 || L ) ) @=
        ? @.
    @}

    @( Descartes's rule of signs.  The difference ` L ` between the number of
       changes of signs ` ( V `` F ) ` of a nonzero polynomial ` F ` and the
       number of nonnegative roots of ` F ` is positive and a multiple of 2.
       @)
    signs @p |- ( F e. ( ( Poly ` RR ) \ { 0p } ) -> ( 0 <_ L /\ 2 || L ) ) @=
      ? @.
  @}
$)

