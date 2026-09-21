$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Sequences defined by strong recursion
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c seqstr $.

  $( Sequences defined by strong recursion. $)
  csseq $a class seqstr $.

  ${
    $d m f x y $.
    $( Define a builder for sequences by strong recursion, i.e., by computing
       the value of the n-th element of the sequence from all preceding
       elements and not just the previous one.  (Contributed by Thierry Arnoux,
       21-Apr-2019.) $)
    df-sseq $a |- seqstr = ( m e. _V , f e. _V |-> ( m u. ( lastS o.
      seq ( # ` m ) ( ( x e. _V , y e. _V |-> ( x ++ <" ( f ` x ) "> ) ) ,
      ( NN0 X. { ( m ++ <" ( f ` m ) "> ) } ) ) ) ) ) $.
  $}

  ${
    iwrdsplit.s $e |- ( ph -> S e. _V ) $.
    iwrdsplit.f $e |- ( ph -> F : NN0 --> S ) $.
    iwrdsplit.n $e |- ( ph -> N e. NN0 ) $.
    $( Lemma for ~ sseqp1 .  (Contributed by Thierry Arnoux, 25-Apr-2019.) $)
    subiwrd $p |- ( ph -> ( F |` ( 0 ..^ N ) ) e. Word S ) $=
      ( cc0 cfzo co cres wf cword wcel cn0 wss fzo0ssnn0 fssres sylancl iswrdi
      syl ) AHDIJZBCUBKZLZUCBMNAOBCLUBOPUDFDQOBUBCRSBDUCTUA $.

    $( Length of a subword of an infinite word.  (Contributed by Thierry
       Arnoux, 25-Apr-2019.) $)
    subiwrdlen $p |- ( ph -> ( # ` ( F |` ( 0 ..^ N ) ) ) = N ) $=
      ( cc0 cfzo co cres chash cfv wfn wceq cn0 wss ffnd fzo0ssnn0 syl hashfzo0
      fnssres sylancl hashfn wcel eqtrd ) ACHDIJZKZLMZUGLMZDAUHUGNZUIUJOACPNUGP
      QUKAPBCFRDSPUGCUBUCUGUHUDTADPUEUJDOGDUATUF $.

    $( Lemma for ~ sseqp1 .  (Contributed by Thierry Arnoux, 25-Apr-2019.)
       (Proof shortened by AV, 14-Oct-2022.) $)
    iwrdsplit $p |- ( ph -> ( F |` ( 0 ..^ ( N + 1 ) ) )
      = ( ( F |` ( 0 ..^ N ) ) ++ <" ( F ` N ) "> ) ) $=
      ( cc0 c1 co cfzo cres cfv cpfx cs1 cconcat wcel wceq cle cfz cmin clsw c0
      caddc chash cword wne cn0 1nn0 a1i nn0addcld subiwrd wbr cr 1re nn0addge2
      sylancr subiwrdlen breqtrrd wb wrdlenge1n0 mpbird pfxlswccat syl2anc 1cnd
      syl nn0cnd mvrraddd oveq2d nn0fz0 sylib wa elfz0add imp syl21anc eleqtrrd
      pfxres wss fzossfzop1 resabs1 3syl 3eqtrd lsw fveq2d fzonn0p1 fvres s1eqd
      oveq12d eqtr3d ) ACHDIUDJZKJZLZWLUEMZIUAJZNJZWLUBMZOZPJZWLCHDKJZLZDCMZOZP
      JAWLBUFZQZWLUCUGZWRWLRABCWJEFADIGIUHQZAUIUJZUKZULZAXEIWMSUMZAIWJWMSAIUNQD
      UHQZIWJSUMUOGIDUPUQABCWJEFXHURZUSAXDXEXJUTXIBWLVAVFVBBWLVCVDAWOWTWQXBPAWO
      WLDNJZWLWSLZWTAWNDWLNAWMDIADGVGAVEXLVHZVIAXDDHWMTJZQXMXNRXIADHWJTJZXPAXKX
      FDHDTJQZDXQQZGXGAXKXRGDVJVKXKXFVLXRXSDIDVMVNVOAWMWJHTXLVIVPBWLDVQVDAXKWSW
      KVRXNWTRGDVSCWSWKVTWAWBAWPXAAWPWNWLMZDWLMZXAAXDWPXTRXIWLXCWCVFAWNDWLXOWDA
      XKDWKQYAXARGDWEDWKCWFWAWBWGWHWI $.
  $}

  ${
    $d f m x y F $.  $d f m x y M $.  $d f m x y ph $.
    sseqval.1 $e |- ( ph -> S e. _V ) $.
    sseqval.2 $e |- ( ph -> M e. Word S ) $.
    sseqval.3 $e |- W = ( Word S i^i ( `' # " ( ZZ>= ` ( # ` M ) ) ) ) $.
    sseqval.4 $e |- ( ph -> F : W --> S ) $.
    $( Value of the strong sequence builder function.  The set ` W ` represents
       here the words of length greater than or equal to the lenght of the
       initial sequence ` M ` .  (Contributed by Thierry Arnoux,
       21-Apr-2019.) $)
    sseqval $p |- ( ph -> ( M seqstr F ) = ( M u. ( lastS o. seq ( # ` M ) ( (
      x e. _V , y e. _V |-> ( x ++ <" ( F ` x ) "> ) ) ,
      ( NN0 X. { ( M ++ <" ( F ` M ) "> ) } ) ) ) ) ) $=
      ( vm vf cvv clsw cfv cconcat co chash wcel cs1 cmpo cn0 csn cxp cseq ccom
      cv cun csseq df-sseq a1i wa simprl fveq2d w3a simp1rr fveq1d s1eqd oveq2d
      wceq mpoeq3dva simprr fveq12d oveq12d sneqd xpeq2d seqeq123d coeq2d cword
      uneq12d elex syl ccnv cuz cima wrdexg inex1g 3syl eqeltrid fexd wfun cmin
      cin c1 df-lsw funmpt2 seqex cofunexg syl2anc unexg ovmpod ) ALMFENNLUHZOB
      CNNBUHZWNMUHZPZUAZQRZUBZUCWMWMWOPZUAZQRZUDZUEZWMSPZUFZUGZUIZFOBCNNWNWNEPZ
      UAZQRZUBZUCFFEPZUAZQRZUDZUEZFSPZUFZUGZUIZUJNUJLMNNXHUBVAABCMLUKULAWMFVAZW
      OEVAZUMUMZWMFXGXTAYBYCUNZYDXFXSOYDWSXLXDXQXEXRYDWMFSYEUOYDBCNNWRXKYDWNNTZ
      CUHNTZUPZWQXJWNQYHWPXIYHWNWOEYBYCAYFYGUQURUSUTVBYDXCXPUCYDXBXOYDWMFXAXNQY
      EYDWTXMYDWMFWOEAYBYCVCYEVDUSVEVFVGVHVIVKAFDVJZTFNTZIFYIVLVMZAGDNEKAGYISVN
      XRVOPVPZWDZNJADNTYINTYMNTHDNVQYIYLNVRVSVTWAAYJXTNTZYANTYKAOWBZXSNTZYNYOAB
      NWNSPWEWCRWNPOBWFWGULYPAXLXQXRWHULOXSNWIWJFXTNNWKWJWL $.

    ${
      sseqfv1.4 $e |- ( ph -> N e. ( 0 ..^ ( # ` M ) ) ) $.
      $( Value of the strong sequence builder function at one of its initial
         values.  (Contributed by Thierry Arnoux, 21-Apr-2019.) $)
      sseqfv1 $p |- ( ph -> ( ( M seqstr F ) ` N ) = ( M ` N ) ) $=
        ( vx co cfv clsw cvv wfn wcel syl a1i vy csseq cs1 cconcat cmpo cn0 csn
        cv cxp chash cseq ccom cun sseqval fveq1d cc0 cfzo cuz wceq cword wrdfn
        cin c0 crn wss c1 cmin fvex df-lsw fnmpti cz lencl nn0zd seqfn ssv fnco
        syl3anc fzouzdisj fvun1 syl112anc eqtrd ) AEDCUBMZNEDOLUAPPLUHZWCCNUCUD
        MUEZUFDDCNUCUDMUGUIZDUJNZUKZULZUMZNZEDNZAEWBWIALUABCDFGHIJUNUOADUPWFUQM
        ZQZWHWFURNZQZWLWNVBVCUSZEWLRWJWKUSADBUTRZWMHBDVASAOPQZWGWNQZWGVDZPVEZWO
        WRALPWCUJNVFVGMZWCNOXBWCVHLVIVJTAWFVKRWSAWFAWQWFUFRHBDVLSVMWDWEWFVNSXAA
        WTVOTPWNOWGVPVQWPAUPWFVRTKWLWNDWHEVSVTWA $.
    $}

    $( A strong recursive sequence is a function over the nonnegative integers.
       (Contributed by Thierry Arnoux, 23-Apr-2019.) $)
    sseqfn $p |- ( ph -> ( M seqstr F ) Fn NN0 ) $=
      ( vx vy co cn0 wfn clsw cvv cfv cc0 wcel a1i csseq cv cs1 cconcat csn cxp
      cmpo chash cseq ccom cun cfzo cuz cword wrdfn syl crn c1 cmin fvex df-lsw
      wss fnmpti cz lencl nn0zd seqfn 3syl ssv fnco syl3anc cin fzouzdisj fnund
      c0 wceq sseqval nn0uz elnn0uz fzouzsplit sylbi eqtrid fneq12d mpbird ) AD
      CUALZMNDOJKPPJUBZWFCQUCUDLUGZMDDCQUCUDLUEUFZDUHQZUIZUJZUKZRWIULLZWIUMQZUK
      ZNAWMWNDWKADBUNSZDWMNGBDUOUPAOPNZWJWNNZWJUQZPVBZWKWNNWQAJPWFUHQURUSLZWFQO
      XAWFUTJVAVCTAWPWIVDSWRGWPWIBDVEZVFWGWHWIVGVHWTAWSVITPWNOWJVJVKWMWNVLVOVPA
      RWIVMTVNAMWOWEWLAJKBCDEFGHIVQAMRUMQZWOVRAWPWIMSZXCWOVPZGXBXDWIXCSXEWIVSRW
      IVTWAVHWBWCWD $.

    $( Lemma for ~ sseqf amd ~ sseqp1 .  (Contributed by Thierry Arnoux,
       25-Apr-2019.) $)
    sseqmw $p |- ( ph -> M e. W ) $=
      ( cword chash ccnv cfv cuz cima cin cvv wcel elex syl cz lencl nn0zd uzid
      3syl cn0 cpnf csn cun wf wfn wa wb hashf ffn elpreima mp2b sylanbrc elind
      eleqtrrdi ) ADBJZKLDKMZNMZOZPEAVAVDDGADQRZVBVCRZDVDRZADVARZVEGDVASTAVHVBU
      ARVFGVHVBBDUBUCVBUDUEQUFUGUHUIZKUJKQUKVGVEVFULUMUNQVIKUOQDVCKUPUQURUSHUT
      $.

    $d a b x y F $.  $d a b x y M $.  $d w S $.  $d a b w x y W $.
    $d a b w x y ph $.
    $( A strong recursive sequence is a function over the nonnegative integers.
       (Contributed by Thierry Arnoux, 23-Apr-2019.)  (Proof shortened by AV,
       7-Mar-2022.) $)
    sseqf $p |- ( ph -> ( M seqstr F ) : NN0 --> S ) $=
      ( cn0 co wf chash cfv clsw cvv c0 wceq wcel wa vx vy vw va csseq cc0 cfzo
      vb cuz cun cv cs1 cconcat cmpo csn cxp cseq ccom cin cword wrdf cdif cres
      syl cdm wral vex a1i cmin fvex df-lsw dmmpti eleqtrrdi eldifsn ccnv inss1
      c1 wne cima eqsstri sseli lswcl sylan sylbi adantl jca ralrimiva wfn wfun
      wb fnmpti fnfun ffvresb mp2b sylibr eqid cz lencl nn0zd ovex simpr adantr
      elnn0uz sylib uztrn syl2anc nn0uz fvconst2g sseqmw ffvelcdmd s1cld ccatcl
      sylancr caddc ccatws1len uzid peano2uz 3syl eqeltrd ffn elpreima sylanbrc
      cpnf hashf elind eqidd simprl fveq2d s1eqd oveq12d ovmpod eldifi ad2antrl
      ccatws1n0 sselid eleqtrdi elin2d simpl2im seqf fco2 fzouzdisj fun sseqval
      syl21anc fzouzsplit eqtrid unidm eqcomd feq123d mpbird ) AJBDCUEKZLUFDMNZ
      UGKZUULUINZUJZBBUJZDOUAUBPPUAUKZUUQCNZULZUMKZUNZJDDCNZULZUMKZUOUPZUULUQZU
      RZUJZLZAUUMBDLZUUNBUVGLZUUMUUNUSQRZUVIADBUTZSZUVJGBDVAVDAEQUOZVBZBOUVPVCL
      ZUUNUVPUVFLUVKAUCUKZOVEZSZUVRONBSZTZUCUVPVFZUVQAUWBUCUVPAUVRUVPSZTZUVTUWA
      UWEUVRPUVSUVRPSUWEUCVGVHUAPUUQMNVQVIKZUUQNZOUWFUUQVJZUAVKZVLVMUWDUWAAUWDU
      VRESZUVRQVRZTUWAUVREQVNUWJUVRUVMSUWKUWAEUVMUVREUVMMVOUUNVSZUSZUVMHUVMUWLV
      PVTZWABUVRWBWCWDWEWFWGOPWHOWIUVQUWCWJUAPUWGOUWHUWIWKPOWLUCUVPBOWMWNWOAUDU
      HUVAUVPUVEUULUUNUUNWPAUVNUULWQSZGUVNUULBDWRZWSVDZAUDUKZUUNSZTZUWRUVENZUVD
      UVPUWTUVDPSZUWRJSUXAUVDRDUVCUMWTZUWTUWRUFUINZJUWTUWSUULUXDSZUWRUXDSAUWSXA
      UWTUULJSZUXEAUXFUWSAUVNUXFGUWPVDXBUULXCZXDUULUWRUFXEXFXGVMJUVDUWRPXHXMUWT
      UVDESZUVDQVRZUVDUVPSAUXHUWSAUVDUWMEAUVMUWLUVDAUVNUVCUVMSUVDUVMSGAUVBBAEBD
      CIABCDEFGHIXIXJXKBDUVCXLXFAUXBUVDMNZUUNSZUVDUWLSZUXBAUXCVHAUXJUULVQXNKZUU
      NAUVNUXJUXMRGBDUVBXOVDAUWOUULUUNSUXMUUNSUWQUULXPUULUULXQXRXSPJYCUOUJZMLZM
      PWHZUXLUXBUXKTWJYDPUXNMXTZPUVDUUNMYAWNYBYEHVMXBAUXIUWSAUVNUXIGBDUVBYNVDXB
      UVDEQVNYBXSAUWRUVPSZUHUKZUVPSZTZTZUWRUXSUVAKUWRUWRCNZULZUMKZUVPUYBUAUBUWR
      UXSPPUUTUYEUVAPUYBUVAYFUYBUUQUWRRZUBUKUXSRZTTZUUQUWRUUSUYDUMUYBUYFUYGYGZU
      YHUURUYCUYHUUQUWRCUYIYHYIYJUWRPSZUYBUDVGVHUXSPSUYBUHVGVHUYEPSZUYBUWRUYDUM
      WTVHZYKUYBUYEESUYEQVRZUYEUVPSUYBUYEUWMEUYBUVMUWLUYEUYBUWRUVMSZUYDUVMSUYEU
      VMSUYBEUVMUWRUWNUXRUWRESAUXTUWREUVOYLZYMZYOUYBUYCBUYBEBUWRCAEBCLUYAIXBUYP
      XJXKBUWRUYDXLXFUYBUYKUYEMNZUUNSZUYEUWLSZUYLUYBUYQUWRMNZVQXNKZUUNUYBUYNUYQ
      VUARUXRUYNAUXTUXREUVMUWRUWNUYOYOYMZBUWRUYCXOVDUYBUYJUYTUUNSZVUAUUNSUYBUWR
      UWLSZUYJVUCTZUYBUVMUWLUWRUYBUWREUWMUYPHYPYQUXOUXPVUDVUEWJYDUXQPUWRUUNMYAW
      NXDUULUYTXQYRXSUXOUXPUYSUYKUYRTWJYDUXQPUYEUUNMYAWNYBYEHVMUYBUYNUYMVUBBUWR
      UYCYNVDUYEEQVNYBXSYSUUNUVPBOUVFYTXFUVLAUFUULUUAVHUUMUUNBBDUVGUUBUUDAJUUOB
      UUPUUKUVHAUAUBBCDEFGHIUUCAJUXDUUOXGAUVNUXFUXDUUORZGUWPUXFUXEVUFUXGUFUULUU
      EWDXRUUFAUUPBUUPBRABUUGVHUUHUUIUUJ $.

    $d i F $.  $d i M $.  $d i S $.  $d i ph $.
    $( The first elements in the strong recursive sequence are the sequence
       initializer.  (Contributed by Thierry Arnoux, 23-Apr-2019.) $)
    sseqfres $p |- ( ph -> ( ( M seqstr F ) |` ( 0 ..^ ( # ` M ) ) ) = M ) $=
      ( vi csseq co cc0 chash cfv wceq wcel adantr cn0 wfn cfzo cres cv wral wa
      cvv cword wf simpr sseqfv1 ralrimiva wss wb sseqfn syl fzo0ssnn0 fvreseq1
      wrdfn a1i syl21anc mpbird ) ADCKLZMDNOZUALZUBDPZJUCZVBOVFDOPZJVDUDZAVGJVD
      AVFVDQZUEBCDVFEABUFQVIFRADBUGQZVIGRHAEBCUHVIIRAVIUIUJUKAVBSTDVDTZVDSULZVE
      VHUMABCDEFGHIUNAVJVKGBDURUOVLAVCUPUSJSVDVBDUQUTVA $.

    ${
      $d a b x y F $.  $d a b x y M $.  $d a b x y ph $.
      sseqfv2.4 $e |- ( ph -> N e. ( ZZ>= ` ( # ` M ) ) ) $.
      $( Value of the strong sequence builder function.  (Contributed by
         Thierry Arnoux, 21-Apr-2019.) $)
      sseqfv2 $p |- ( ph -> ( ( M seqstr F ) ` N ) = ( lastS ` ( seq ( # ` M )
        ( ( x e. _V , y e. _V |-> ( x ++ <" ( F ` x ) "> ) ) ,
        ( NN0 X. { ( M ++ <" ( F ` M ) "> ) } ) ) ` N ) ) ) $=
        ( co cfv clsw cvv wfn wcel syl va vb csseq cs1 cconcat cmpo cn0 csn cxp
        cv chash cseq ccom cun sseqval fveq1d cc0 cfzo cuz cin wceq cword wrdfn
        c0 crn wss c1 cmin fvex df-lsw fnmpti a1i cz lencl nn0zd seqfn ssv fnco
        syl3anc fzouzdisj fvun2 syl112anc wfun cdm fnfun fvexd ovexd eqid caddc
        wa seqf2 fdmd eleqtrrd fvco syl2anc 3eqtrd ) AGFEUCNZOGFPBCQQBUJZWREOUD
        UENUFZUGFFEOUDUENUHUIZFUKOZULZUMZUNZOZGXCOZGXBOPOZAGWQXDABCDEFHIJKLUOUP
        AFUQXAURNZRZXCXAUSOZRZXHXJUTVDVAZGXJSXEXFVAAFDVBSZXIJDFVCTAPQRZXBXJRZXB
        VEZQVFZXKXNABQWRUKOVGVHNZWROPXRWRVIBVJVKVLAXAVMSXOAXAAXMXAUGSJDFVNTVOZW
        SWTXAVPTZXQAXPVQVLQXJPXBVRVSXLAUQXAVTVLMXHXJFXCGWAWBAXBWCZGXBWDZSXFXGVA
        AXOYAXTXJXBWETAGXJYBMAXJQXBAUAUBQQWSWTXAXJAXAWTWFAUAUJZQSUBUJZQSWJWJYCY
        DWSWGXJWHXSAYCXAVGWINUSOSWJYCWTWFWKWLWMGPXBWNWOWP $.

      $d i n x y F $.  $d i n x y M $.  $d i N $.  $d a b i n x y ph $.
      $( Value of the strong sequence builder function at a successor.
         (Contributed by Thierry Arnoux, 24-Apr-2019.) $)
      sseqp1 $p |- ( ph -> ( ( M seqstr F ) ` N ) =
        ( F ` ( ( M seqstr F ) |` ( 0 ..^ N ) ) ) ) $=
        ( co cfv cvv cs1 cconcat cn0 chash wcel wceq vx vy vi vn va vb csseq cv
        cmpo csn cxp cseq clsw cc0 cfzo cres sseqfv2 cuz wi caddc fveq2 reseq2d
        c1 oveq2 fveq2d s1eqd oveq12d eqeq12d imbi2d ovex cword lencl fvconst2g
        cz syl sylancr nn0zd seq1 sseqfres 3eqtr4d a1i wa seqp1 adantl id eqidd
        3syl cbvmpov simprl fvexd ovmpod eqtrd adantr simpr wss sseqf fzo0ssnn0
        wf fssres sylancl iswrdi ccnv cima cin eluznn0 sylan subiwrdlen eqeltrd
        elex cpnf cun wfn hashf ffn elpreima sylanbrc elind eleqtrrdi ffvelcdmd
        wb mp2b lswccats1 syl2anc 3eqtrrd oveq2d iwrdsplit ex expcom a2d uzind4
        mpcom 3eqtrd ) AEDCUGLZMEUAUBNNUAUHZYNCMZOZPLZUIZQDDCMZOZPLZUJUKZDRMZUL
        ZMZUMMYMUNEUOLZUPZUUGCMZOZPLZUMMZUUHAUAUBBCDEFGHIJKUQAUUEUUJUMEUUCURMZS
        ZAUUEUUJTZKAUCUHZUUDMZYMUNUUOUOLZUPZUURCMZOZPLZTZUSAUUCUUDMZYMUNUUCUOLZ
        UPZUVECMZOZPLZTZUSZAUDUHZUUDMZYMUNUVKUOLZUPZUVNCMZOZPLZTZUSAUVKVCUTLZUU
        DMZYMUNUVSUOLZUPZUWBCMZOZPLZTZUSAUUNUSUCUDUUCEUUOUUCTZUVBUVIAUWGUUPUVCU
        VAUVHUUOUUCUUDVAUWGUURUVEUUTUVGPUWGUUQUVDYMUUOUUCUNUOVDVBZUWGUUSUVFUWGU
        URUVECUWHVEVFVGVHVIUUOUVKTZUVBUVRAUWIUUPUVLUVAUVQUUOUVKUUDVAUWIUURUVNUU
        TUVPPUWIUUQUVMYMUUOUVKUNUOVDVBZUWIUUSUVOUWIUURUVNCUWJVEVFVGVHVIUUOUVSTZ
        UVBUWFAUWKUUPUVTUVAUWEUUOUVSUUDVAUWKUURUWBUUTUWDPUWKUUQUWAYMUUOUVSUNUOV
        DVBZUWKUUSUWCUWKUURUWBCUWLVEVFVGVHVIUUOETZUVBUUNAUWMUUPUUEUVAUUJUUOEUUD
        VAUWMUURUUGUUTUUIPUWMUUQUUFYMUUOEUNUOVDVBZUWMUUSUUHUWMUURUUGCUWNVEVFVGV
        HVIUVJUUCVNSZAUUCUUBMZUUAUVCUVHAUUANSUUCQSZUWPUUATDYTPVJADBVKZSZUWQHBDV
        LZVOZQUUAUUCNVMVPAUWSUWOUVCUWPTHUWSUUCUWTVQYRUUBUUCVRWGAUVEDUVGYTPABCDF
        GHIJVSZAUVFYSAUVEDCUXBVEVFVGVTWAUVKUULSZAUVRUWFAUXCUVRUWFUSAUXCWBZUVRUW
        FUXDUVRWBZUVTUVLUVLCMZOZPLZUWEUXDUVTUXHTUVRUXDUVTUVLUVSUUBMZYRLZUXHUXCU
        VTUXJTAYRUUBUUCUVKWCWDUXDUEUFUVLUXINNUEUHZUXKCMZOZPLZUXHYRNYRUEUFNNUXNU
        ITUXDUAUBUEUFNNYQUXNUXNYNUXKTZYNUXKYPUXMPUXOWEUXOYOUXLYNUXKCVAVFVGUBUHU
        FUHZTUXNWFWHWAUXDUXKUVLTZUXPUXITZWBWBZUXKUVLUXMUXGPUXDUXQUXRWIZUXSUXLUX
        FUXSUXKUVLCUXTVEVFVGUXDUVKUUDWJUXDUVSUUBWJUXHNSUXDUVLUXGPVJWAWKWLWMUXEU
        VLUWBUXGUWDPUXEUVQUVNUVKYMMZOZPLZUVLUWBUXEUVPUYBUVNPUXEUVOUYAUXEUYAUVLU
        MMZUVQUMMZUVOUXDUYAUYDTUVRUXDUAUBBCDUVKFABNSUXCGWMZAUWSUXCHWMIAFBCWRUXC
        JWMZAUXCWNZUQWMUXEUVLUVQUMUXDUVRWNZVEUXDUYEUVOTZUVRUXDUVNUWRSZUVOBSUYJA
        UYKUXCAUVMBUVNWRZUYKAQBYMWRZUVMQWOUYLABCDFGHIJWPZUVKWQQBUVMYMWSWTBUVKUV
        NXAVOWMZUXDFBUVNCUYGUXDUVNUWRRXBUULXCZXDZFUXDUWRUYPUVNUYOUXDUVNNSZUVNRM
        ZUULSZUVNUYPSZUXDUYKUYRUYOUVNUWRXIVOUXDUYSUVKUULUXDBYMUVKUYFAUYMUXCUYNW
        MZAUWQUXCUVKQSUXAUVKUUCXEXFZXGUYHXHNQXJUJXKZRWRZRNXLZVUAUYRUYTWBXTXMNVU
        DRXNZNUVNUULRXOYAXPXQIXRXSUVOBUVNYBYCWMYDVFYEUYIUXDUWBUYCTUVRUXDBYMUVKU
        YFVUBVUCYFWMVTZUXEUXFUWCUXEUVLUWBCVUHVEVFVGWLYGYHYIYJYKVEAUUGUWRSZUUHBS
        UUKUUHTAUUFBUUGWRZVUIAUYMUUFQWOVUJUYNEWQQBUUFYMWSWTBEUUGXAVOZAFBUUGCJAU
        UGUYQFAUWRUYPUUGVUKAUUGNSZUUGRMZUULSZUUGUYPSZAVUIVULVUKUUGUWRXIVOAVUMEU
        ULABYMEGUYNAUWQUUMEQSUXAKEUUCXEYCXGKXHVUEVUFVUOVULVUNWBXTXMVUGNUUGUULRX
        OYAXPXQIXRXSUUHBUUGYBYCYL $.
    $}
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Fibonacci Numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Fibci $.

  $( The Fibonacci sequence. $)
  cfib $a class Fibci $.

  $( Define the Fibonacci sequence, where that each element is the sum of the
     two preceding ones, starting from 0 and 1.  (Contributed by Thierry
     Arnoux, 25-Apr-2019.) $)
  df-fib $a |- Fibci = ( <" 0 1 "> seqstr (
      w e. ( Word NN0 i^i ( `' # " ( ZZ>= ` 2 ) ) )
    |-> ( ( w ` ( ( # ` w ) - 2 ) ) + ( w ` ( ( # ` w ) - 1 ) ) ) ) ) $.

  $( Lemma for ~ fib0 , ~ fib1 and ~ fibp1 .  (Contributed by Thierry Arnoux,
     25-Apr-2019.) $)
  fiblem $p |- ( w e. ( Word NN0 i^i ( `' # " ( ZZ>= ` 2 ) ) )
    |-> ( ( w ` ( ( # ` w ) - 2 ) ) + ( w ` ( ( # ` w ) - 1 ) ) ) ) :
    ( Word NN0 i^i ( `' # " ( ZZ>= ` ( # ` <" 0 1 "> ) ) ) ) --> NN0 $=
    ( cn0 chash cc0 c1 cfv cuz cima cin c2 cmin co caddc fveq2i wcel wf syl cvv
    cn eleqtrrdi cword ccnv cs2 cv cmpt s2len eqcomi imaeq2i eqid mpteq12i cfzo
    ineq2i elin simplbi wrdf clt wbr wa simprbi cpnf csn cun wfn hashf elpreima
    wb ffn mp2b sylib simprd uznn0sub cz 1zzd 1p1e2 peano2uzr syl2anc nnred crp
    nnuz 2rp a1i ltsubrpd elfzo0 syl3anbrc ffvelcdmd fzo0end nn0addcld fmpti )
    ABUAZCUBZDEUCCFZGFZHZIZBAUDZCFZJKLZWOFZWPEKLZWOFZMLZAWIWJJGFZHZIZXAUEAXDXAW
    NXAXCWMWIXBWLWJJWKGWKJDEUFUGNZUHULXAUIUJWOWNOZWRWTXFDWPUKLZBWQWOXFWOWIOZXGB
    WOPXFXHWOWMOZWOWIWMUMZUNBWOUOQZXFWQBOZWPSOZWQWPUPUQWQXGOXFWPXBOXLXFWPWLXBXF
    WOROZWPWLOZXFXIXNXOURZXFXHXIXJUSRBUTVAVBZCPCRVCXIXPVFVDRXQCVGRWOWLCVEVHVIVJ
    XETZJWPVKQXFWPEGFZSXFEVLOWPEEMLZGFZOWPXSOXFVMXFWPXBYAXRXTJGVNNTEWPVOVPVSTZX
    FWPJXFWPYBVQJVROXFVTWAWBWQWPWCWDWEXFXGBWSWOXKXFXMWSXGOYBWPWFQWEWGWH $.

  $( Value of the Fibonacci sequence at index 0.  (Contributed by Thierry
     Arnoux, 25-Apr-2019.) $)
  fib0 $p |- ( Fibci ` 0 ) = 0 $=
    ( vw cc0 cfib cfv c1 cs2 cn0 chash c2 cuz cima cin cmin wceq wtru wcel 0nn0
    co a1i cfzo cword ccnv caddc cmpt csseq df-fib fveq1i nn0ex 1nn0 s2cld eqid
    cv cvv wf fiblem 2nn lbfzo0 mpbir s2len oveq2i eleqtrri sseqfv1 mptru s2fv0
    cn ax-mp 3eqtri ) BCDBBEFZAGUAZHUBZIJDKLAULZHDZIMRVKDVLEMRVKDUCRUDZUERZDZBV
    HDZBBCVNAUFUGVOVPNOGVMVHBVIVJVHHDZJDKLZGUMPOUHSOBEGBGPZOQSEGPOUISUJVRUKVRGV
    MUNOAUOSBBVQTRZPOBBITRZVTBWAPIVEPUPIUQURVQIBTBEUSUTVASVBVCVSVPBNQBEGVDVFVG
    $.

  $( Value of the Fibonacci sequence at index 1.  (Contributed by Thierry
     Arnoux, 25-Apr-2019.) $)
  fib1 $p |- ( Fibci ` 1 ) = 1 $=
    ( vw c1 cfib cfv cc0 cs2 cn0 chash c2 cuz cima cin cmin wceq wtru wcel 1nn0
    co a1i cfzo cword ccnv caddc cmpt csseq df-fib fveq1i nn0ex 0nn0 s2cld eqid
    cv cvv wf fiblem cn clt wbr 2nn 1lt2 elfzo0 mpbir3an s2len eleqtrri sseqfv1
    oveq2i mptru s2fv1 ax-mp 3eqtri ) BCDBEBFZAGUAZHUBZIJDKLAULZHDZIMRVNDVOBMRV
    NDUCRUDZUERZDZBVKDZBBCVQAUFUGVRVSNOGVPVKBVLVMVKHDZJDKLZGUMPOUHSOEBGEGPOUISB
    GPZOQSUJWAUKWAGVPUNOAUOSBEVTTRZPOBEITRZWCBWDPWBIUPPBIUQURQUSUTBIVAVBVTIETEB
    VCVFVDSVEVGWBVSBNQEBGVHVIVJ $.

  ${
    $d t w $.  $d t N $.
    $( Value of the Fibonacci sequence at higher indices.  (Contributed by
       Thierry Arnoux, 25-Apr-2019.) $)
    fibp1 $p |- ( N e. NN -> ( Fibci ` ( N + 1 ) ) = ( ( Fibci ` ( N - 1 ) )
      + ( Fibci ` N ) ) ) $=
      ( vw vt wcel c1 caddc cfib cfv cc0 cn0 chash cuz cmin wceq a1i cvv oveq1d
      co c2 wf cn cs2 cword ccnv cima cin cv cmpt csseq cfzo cres df-fib fveq1i
      nn0ex 0nn0 1nn0 s2cld eqid fiblem eluzp1p1 nnuz eleq2s s2len 1p1e2 eqtr4i
      fveq2i eleqtrrdi sseqp1 id fveq2 fveq12d oveq12d cbvmptv wa simpr reseq1d
      eqtr4d fveq2d sseqf feq1d nnnn0 nn0addcld subiwrdlen eqtrd nncn 1cnd 2cnd
      mpbird adantr addsubassd subsub2d 2m1e1 oveq2i 3eqtr2d fveq1d clt nnm1nn0
      wbr peano2nn nnre cr 2re readdcld crp 2rp ltaddrpd ltsub1dd eqtrdi elfzo0
      breqtrd syl3anbrc fvres syl 3eqtrd simpl nncnd pncand cfz nn0fz0 sylib cz
      1red nnz fzval3 eleqtrd syldan subiwrd ovex eqeltri eleqtrdi eqeltrd cpnf
      resex csn cun wfn wb hashf ffn elpreima sylanbrc elind eqeltrrd fvmptd
      mp2b ) AUADZAEFRZGHZUUGIEUBZBJUCZKUDZSLHZUEZUFZBUGZKHZSMRZUUOHZUUPEMRZUUO
      HZFRZUHZUIRZHZUVCIUUGUJRZUKZUVBHAEMRZGHZAGHZFRZUUHUVDNUUFUUGGUVCBULZUMOUU
      FJUVBUUIUUGUUJUUKUUIKHZLHZUEUFZJPDUUFUNOZUUFIEJIJDUUFUOOEJDUUFUPOZUQZUVNU
      RZUVNJUVBTUUFBUSOZUUFUUGEEFRZLHZUVMUUGUWADAELHUAEAUTVAVBZUVLUVTLUVLSUVTIE
      VCVDVEVFVGVHUUFCUVFCUGZKHZSMRZUWCHZUWDEMRZUWCHZFRZUVJUUNUVBPUVBCUUNUWIUHN
      UUFBCUUNUVAUWIUUOUWCNZUURUWFUUTUWHFUWJUUQUWEUUOUWCUWJVIZUWJUUPUWDSMUUOUWC
      KVJZQVKUWJUUSUWGUUOUWCUWKUWJUUPUWDEMUWLQVKVLVMOUUFUWCUVFNZUWCGUVEUKZNZUWI
      UVJNUUFUWMVNZUWCUVFUWNUUFUWMVOUWPGUVCUVEGUVCNZUWPUVKOVPVQUUFUWOVNZUWFUVHU
      WHUVIFUWRUWFUVGUWCHUVGUWNHZUVHUWRUWEUVGUWCUWRUWEUUGSMRZUVGUWRUWDUUGSMUWRU
      WDUWNKHZUUGUWRUWCUWNKUUFUWOVOZVRUUFUXAUUGNUWOUUFJGUUGUVOUUFJJGTJJUVCTUUFJ
      UVBUUIUVNUVOUVQUVRUVSVSUUFJJGUVCUWQUUFUVKOZVTWHZUUFAEAWAZUVPWBZWCZWIWDZQU
      UFUWTUVGNUWOUUFUWTAESMRFRASEMRZMRZUVGUUFAESAWEZUUFWFZUUFWGZWJUUFASEUXKUXM
      UXLWKUXJUVGNUUFUXIEAMWLWMOWNWIWDVRUWRUVGUWCUWNUXBWOUWRUVGUVEDZUWSUVHNUUFU
      XNUWOUUFUVGJDUUGUADUVGUUGWPWRUXNAWQAWSUUFUVGASFRZEMRZUUGWPUUFAUXOEAWTZUUF
      ASUXQSXADUUFXBOXCUUFYBUUFASUXQSXDDUUFXEOXFXGUUFUXPAUXIFRUUGUUFASEUXKUXMUX
      LWJUXIEAFWLWMXHXJUVGUUGXIXKWIUVGUVEGXLXMXNUWRUWHAUWCHAUWNHZUVIUWRUWGAUWCU
      WRUWGUUGEMRAUWRUWDUUGEMUXHQUWRAEUWRAUUFUWOXOXPUWRWFXQWDVRUWRAUWCUWNUXBWOU
      WRAUVEDZUXRUVINUUFUXSUWOUUFAIAXRRZUVEUUFAJDAUXTDUXEAXSXTUUFAYADUXTUVENAYC
      IAYDXMYEWIAUVEGXLXMXNVLYFUUFUWNUVFUUNUUFGUVCUVEUXCVPUUFUUJUUMUWNUUFJGUUGU
      VOUXDUXFYGUUFUWNPDZUXAUULDZUWNUUMDZUYAUUFGUVEGUVCPUVKUUIUVBUIYHYIYMOUUFUX
      AUUGUULUXGUUFUUGUWAUULUWBUVTSLVDVFYJYKPJYLYNYOZKTKPYPUYCUYAUYBVNYQYRPUYDK
      YSPUWNUULKYTUUEUUAUUBUUCUVJPDUUFUVHUVIFYHOUUDXN $.
  $}

  $( Value of the Fibonacci sequence at index 2.  (Contributed by Thierry
     Arnoux, 25-Apr-2019.) $)
  fib2 $p |- ( Fibci ` 2 ) = 1 $=
    ( c1 caddc co cfib cfv c2 1p1e2 fveq2i cmin cc0 wcel wceq fibp1 ax-mp 1m1e0
    cn 1nn fib0 eqtri fib1 oveq12i 0p1e1 3eqtri eqtr3i ) AABCZDEZFDEAUEFDGHUFAA
    ICZDEZADEZBCZJABCAAPKUFUJLQAMNUHJUIABUHJDEJUGJDOHRSTUAUBUCUD $.

  $( Value of the Fibonacci sequence at index 3.  (Contributed by Thierry
     Arnoux, 25-Apr-2019.) $)
  fib3 $p |- ( Fibci ` 3 ) = 2 $=
    ( c2 c1 caddc co cfib cfv c3 2p1e3 fveq2i cmin cn wcel wceq 2nn fibp1 ax-mp
    2m1e1 fib1 eqtri fib2 oveq12i 1p1e2 3eqtri eqtr3i ) ABCDZEFZGEFAUEGEHIUFABJ
    DZEFZAEFZCDZBBCDAAKLUFUJMNAOPUHBUIBCUHBEFBUGBEQIRSTUAUBUCUD $.

  $( Value of the Fibonacci sequence at index 4.  (Contributed by Thierry
     Arnoux, 25-Apr-2019.) $)
  fib4 $p |- ( Fibci ` 4 ) = 3 $=
    ( c3 c1 caddc co cfib cfv c4 3p1e4 fveq2i cmin c2 wcel wceq 3nn fibp1 ax-mp
    cn 3m1e2 fib2 eqtri fib3 oveq12i 1p2e3 3eqtri eqtr3i ) ABCDZEFZGEFAUFGEHIUG
    ABJDZEFZAEFZCDZBKCDAAQLUGUKMNAOPUIBUJKCUIKEFBUHKERISTUAUBUCUDUE $.

  $( Value of the Fibonacci sequence at index 5.  (Contributed by Thierry
     Arnoux, 25-Apr-2019.) $)
  fib5 $p |- ( Fibci ` 5 ) = 5 $=
    ( c4 c1 caddc co cfib cfv c5 4p1e5 fveq2i cmin c2 c3 cn wcel wceq 4nn fibp1
    ax-1cn 3cn addcomli ax-mp 4cn 3p1e4 subaddrii fib3 eqtri fib4 oveq12i 3p2e5
    2cn 3eqtri eqtr3i ) ABCDZEFZGEFGUMGEHIUNABJDZEFZAEFZCDZKLCDGAMNUNUROPAQUAUP
    KUQLCUPLEFKUOLEABLUBRSLBASRUCTUDIUEUFUGUHLKGSUJUITUKUL $.

  $( Value of the Fibonacci sequence at index 6.  (Contributed by Thierry
     Arnoux, 25-Apr-2019.) $)
  fib6 $p |- ( Fibci ` 6 ) = 8 $=
    ( c5 c1 caddc co cfib cfv c6 c8 5p1e6 fveq2i cmin c3 cn wcel wceq c4 ax-1cn
    5cn 4cn addcomli fibp1 ax-mp 4p1e5 subaddrii fib4 eqtri fib5 oveq12i 3eqtri
    5nn 3cn 5p3e8 eqtr3i ) ABCDZEFZGEFHUNGEIJUOABKDZEFZAEFZCDZLACDHAMNUOUSOUJAU
    AUBUQLURACUQPEFLUPPEABPRQSPBASQUCTUDJUEUFUGUHALHRUKULTUIUM $.

