$(
###############################################################################
  ZFC (ZERMELO-FRAENKEL WITH CHOICE) SET THEORY
###############################################################################

  In this section we add the Axiom of Choice ~ ax-ac , as well as weaker forms
  such as the axiom of countable choice ~ ax-cc and dependent choice ~ ax-dc .
  We introduce these weaker forms so that theorems that do not need the full
  power of the axiom of choice, but need more than simple ZF, can use these
  intermediate axioms instead.

  The combination of the Zermelo-Fraenkel axioms and the axiom of choice is
  often abbreviated as ZFC.  The axiom of choice is widely accepted, and ZFC is
  the most commonly-accepted fundamental set of axioms for mathematics.

  However, there have been and still are some lingering controversies about the
  Axiom of Choice.  The axiom of choice does not satisfy those who wish to have
  a constructive proof (e.g., it will not satisfy intuitionistic logic).  Thus,
  we make it easy to identify which proofs depend on the axiom of choice or its
  weaker forms.

$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  ZFC Set Theory - add Countable Choice and Dependent Choice
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Introduce the Axiom of Countable Choice
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d f x z $.
    $( The axiom of countable choice (CC), also known as the axiom of
       denumerable choice.  It is clearly a special case of ~ ac5 , but is weak
       enough that it can be proven using DC (see ~ axcc ).  It is, however,
       strictly stronger than ZF and cannot be proven in ZF. It states that any
       countable collection of nonempty sets must have a choice function.
       (Contributed by Mario Carneiro, 9-Feb-2013.) $)
    ax-cc $a |- ( x ~~ _om ->
       E. f A. z e. x ( z =/= (/) -> ( f ` z ) e. z ) ) $.
  $}

  ${
    $d A a f z $.  $d A k n $.  $d A f n $.  $d F f g $.  $d G g n $.
    $d K n $.  $d n z $.
    axcc2lem.1 $e |- K = ( n e. _om |->
                       if ( ( F ` n ) = (/) , { (/) } , ( F ` n ) ) ) $.
    axcc2lem.2 $e |- A = ( n e. _om |-> ( { n } X. ( K ` n ) ) ) $.
    axcc2lem.3 $e |- G = ( n e. _om |-> ( 2nd ` ( f ` ( A ` n ) ) ) ) $.
    $( Lemma for ~ axcc2 .  (Contributed by Mario Carneiro, 8-Feb-2013.) $)
    axcc2lem $p |- E. g ( g Fn _om /\ A. n e. _om
                    ( ( F ` n ) =/= (/) -> ( g ` n ) e. ( F ` n ) ) ) $=
      ( vz c0 wne cfv wcel wi com wa cvv wceq vk va cv crn wral wfn c2nd fnmpti
      wex fvex w3a csn cxp vsnex xpex fvmpt2 mpan2 vex cif iftrue neeq1d mpbiri
      snnz 0ex wn iffalse neqne eqnetrd pm2.61i p0ex ifex xpnz sylancr fnfvelrn
      biimpi mpan neeq1 fveq2 id eleq12d imbi12d rspccv syl5 mpdi impcom eleq2d
      adantr mpbid xp2nd syl 3adant3 3ad2ant1 eqcomd ifnefalse 3ad2ant3 3eltr3d
      wb eqtrd 3expia expcom ralrimiv omex fnex mp2an fneq1 fveq1 eleq1d imbi2d
      ralbidv anbi12d spcev wf1 cen wbr wf a1i fmptd ax-mp sneq xpeq12d fvmpt3i
      adantl eqeq2d eqeq1d xp11 sneqr biimtrdi sylbid rgen2 dff13 mpbir2an wf1o
      f1f1orn f1oen ensym 3syl cmpt rneqi cdm eqeltri dmmptg funmpt funrnex mp2
      wfun mprg breq1 raleq exbidv ax-cc vtocl mp2b exlimiiv ) KUCZLMZUUNBUCZNZ
      UUNOZPZKAUDZUEZCUCZQUFZDUCZENZLMZUVDUVBNZUVEOZPZDQUEZRZCUIZBUVAFQUFZUVFUV
      DFNZUVEOZPZDQUEZUVLDQUVDANZUUPNZUGNZFUVSUGUJZJUHZUVAUVPDQUVDQOZUVAUVPUWCU
      VAUVFUVOUWCUVAUVFUKZUVTUVDGNZUVNUVEUWCUVAUVTUWEOZUVFUWCUVARZUVSUVDULZUWEU
      MZOZUWFUWGUVSUVROZUWJUVAUWCUWKUVAUWCUVRLMZUWKUWCUVRUWILUWCUWISOZUVRUWITZU
      WHUWEDUNUVDGUJUOZDQUWISAIUPUQZUWCUWHLMZUWELMZUWILMZUVDDURZVCZUWCUWRUVELTZ
      LULZUVEUSZLMZUXBUXEUXBUXEUXCLMLVDVCUXBUXDUXCLUXBUXCUVEUTVAVBUXBVEUXDUVELU
      XBUXCUVEVFUVELVGVHVIUWCUWEUXDLUWCUXDSOUWEUXDTZUXBUXCUVEVJUVDEUJVKDQUXDSGH
      UPUQZVAVBZUWQUWRRUWSUWHUWEVLVOVMVHUWCUVRUUTOZUVAUWLUWKPZAQUFUWCUXIDQUWIAU
      WOIUHQUVDAVNVPUUSUXJKUVRUUTUUNUVRTZUUOUWLUURUWKUUNUVRLVQUXKUUQUVSUUNUVRUU
      NUVRUUPVRUXKVSVTWAWBWCWDWEUWCUWKUWJWQUVAUWCUVRUWIUVSUWPWFWGWHUVSUWHUWEWIW
      JWKUWDUVNUVTUWCUVAUVNUVTTZUVFUWCUVTSOUXLUWADQUVTSFJUPUQWLWMUWDUWEUXDUVEUW
      CUVAUXFUVFUXGWLUVFUWCUXDUVETUVAUVELUXCUVEWNWOWRWPWSWTXAUVKUVMUVQRCFUVMQSO
      ZFSOUWBXBQSFXCXDUVBFTZUVCUVMUVJUVQQUVBFXEUXNUVIUVPDQUXNUVHUVOUVFUXNUVGUVN
      UVEUVDUVBFXFXGXHXIXJXKVMQSAXLZUUTQXMXNZUVABUIZUXOQSAXOZUVRUAUCZANZTZUVDUX
      STZPZUAQUEDQUEUXMUXRXBUXMDQUWISAUWMUXMUWCRUWOXPIXQXRUYCDUAQQUWCUXSQOZRZUY
      AUVRUXSULZUXSGNZUMZTZUYBUYEUXTUYHUVRUYDUXTUYHTUWCDUXSUWIUYHQAUYBUWHUYFUWE
      UYGUVDUXSXSUVDUXSGVRXTIUWOYAYBYCUYEUYIUWIUYHTZUYBUYEUVRUWIUYHUWCUWNUYDUWP
      WGYDUWCUYJUYBPUYDUWCUYJUWHUYFTZUWEUYGTZRZUYBUWCUWQUWRUYJUYMWQUXAUXHUWHUWE
      UYFUYGYEVMUYKUYBUYLUVDUXSUWTYFWGYGWGYHYHYIDUAQSAYJYKUXOQUUTAYLQUUTXMXNUXP
      QSAYMQUUTAXBYNQUUTYOYPUBUCZQXMXNZUUSKUYNUEZBUIZPUXPUXQPUBUUTUUTDQUWIYQZUD
      ZSAUYRIYRUYRYSZSOUYRUUEUYSSOUYTQSUWMUYTQTDQDQUWISUUAUWMUWCUWOXPUUFXBYTDQU
      WIUUBSUYRUUCUUDYTUYNUUTTZUYOUXPUYQUXQUYNUUTQXMUUGVUAUYPUVABUUSKUYNUUTUUHU
      UIWAUBKBUUJUUKUULUUM $.
  $}

  ${
    $d F f g m n $.
    $( A possibly more useful version of ax-cc using sequences instead of
       countable sets.  The Axiom of Infinity is needed to prove this, and
       indeed this implies the Axiom of Infinity.  (Contributed by Mario
       Carneiro, 8-Feb-2013.) $)
    axcc2 $p |- E. g ( g Fn _om /\ A. n e. _om
                    ( ( F ` n ) =/= (/) -> ( g ` n ) e. ( F ` n ) ) ) $=
      ( vm vf com cv csn cfv c0 wceq cif cmpt cxp c2nd nfcv fveq2 nffvmpt1 nffv
      cbvmpt fveqeq2 ifbieq2d nfxp sneq xpeq12d 2fveq3 fveq2d axcc2lem ) DFDGZH
      ZUIDFUICIZJKZJHZUKLZMZIZNZMZEABCDFUIURIEGZIZOIZMUODBFUNBGZCIZJKZUMVCLZBUN
      PDVEPUIVBKZULVDUKVCUMUIVBJCUAUIVBCQUBTDBFUQVBHZVBUOIZNBUQPDVGVHDVGPDFUNVB
      RUCVFUJVGUPVHUIVBUDUIVBUOQUETDBFVAVBURIZUSIZOIBVAPDVJODOPDVIUSDUSPDFUQVBR
      SSVFUTVJOUIVBUSURUFUGTUH $.
  $}

  ${
    $d F f g h k m $.  $d N f g h k m n $.
    axcc3.1 $e |- F e. _V $.
    axcc3.2 $e |- N ~~ _om $.
    $( A possibly more useful version of ~ ax-cc using sequences ` F ( n ) `
       instead of countable sets.  The Axiom of Infinity is needed to prove
       this, and indeed this implies the Axiom of Infinity.  (Contributed by
       Mario Carneiro, 8-Feb-2013.)  (Revised by Mario Carneiro,
       26-Dec-2014.) $)
    axcc3 $p |- E. f ( f Fn N /\ A. n e. N
                    ( F =/= (/) -> ( f ` n ) e. F ) ) $=
      ( vh vg vm cv wfn c0 wne cfv wcel wi wa com cvv wceq vk wral wex cmpt cen
      wbr relen brrelex1i mptexg mp2b wf1o bren mpbi ccnv ccom axcc2 f1of fnfco
      w3a sylan2 adantlr 3adant1 nfmpt1 nfeq2 nfv nf3an ffvelcdmda fveq2 neeq1d
      wf eleq12d imbi12d rspcv 3ad2antl3 f1ocnv fvco3 syl2an2r f1ocnvfv1 fveq2d
      syl fveq1 eqid fvmpt2 mpan2 sylan9eq 3eqtrd 3expa 3adantl2 3ad2ant3 sylan
      3adant2 eleq1d eleq2d bitr3d sylibd com23 3exp com34 imp32 3impia ralrimi
      ex vex coex fneq1 imbi2d ralbidv anbi12d spcev syl2anc exlimdv mpi vtocle
      ) AJZDKZCLMZBJZXNNZCOZPZBDUBZQZAUCZUABDCUDZDRUEUFZDSOYDSOFDRUEUGUHBDCSUIU
      JUAJZYDTZDRGJZUKZGUCZYCYEYJFDRGULUMYGYIYCGYGHJZRKZIJZYFYHUNZUOZNZLMZYMYKN
      ZYPOZPZIRUBZQZHUCYIYCPZHIYOUPYGUUBUUCHYGUUBYIYCYGUUBYIUSZYKYHUOZDKZXPXQUU
      ENZCOZPZBDUBZYCUUBYIUUFYGYLYIUUFUUAYIYLDRYHVJZUUFDRYHUQZRDYKYHURUTVAVBUUD
      UUIBDYGUUBYIBBYFYDBDCVCVDUUBBVEYIBVEVFYGUUBYIXQDOZUUIPZYGYLUUAYIUUNPYGYLY
      IUUAUUNYGYLYIUUAUUNPYGYLYIUSZUUMUUAUUIUUOUUMUUAUUIPUUOUUMQZUUAXQYHNZYONZL
      MZUUQYKNZUUROZPZUUIYIYGUUMUUAUVBPZYLYIUUMQZUUQROZUVCYIDRXQYHUULVGZYTUVBIU
      UQRYMUUQTZYQUUSYSUVAUVGYPUURLYMUUQYOVHZVIUVGYRUUTYPUURYMUUQYKVHUVHVKVLVMV
      TVNUUPUUSXPUVAUUHUUPUURCLYGYIUUMUURCTZYLYGYIUUMUVIYGYIUUMUSUURUUQYNNZYFNZ
      XQYFNZCYIUUMUURUVKTZYGYIRDYNVJZUUMUVEUVMYIRDYNUKUVNDRYHVORDYNUQVTUVFRDUUQ
      YFYNVPVQVBYIUUMUVKUVLTYGUVDUVJXQYFDRXQYHVRVSVBYGUUMUVLCTYIYGUUMUVLXQYDNZC
      XQYFYDWAUUMCSOUVOCTEBDCSYDYDWBWCWDWEWKWFWGWHZVIUUPUUGUUROUVAUUHUUPUUGUUTU
      URUUOUUKUUMUUGUUTTYIYGUUKYLUULWIDRXQYKYHVPWJWLUUPUURCUUGUVPWMWNVLWOXBWPWQ
      WRWSWTXAYBUUFUUJQAUUEYKYHHXCGXCXDXNUUETZXOUUFYAUUJDXNUUEXEUVQXTUUIBDUVQXS
      UUHXPUVQXRUUGCXQXNUUEWAWLXFXGXHXIXJWQXKXLXKXLXM $.
  $}

  ${
    $d A f n x $.  $d N f n $.  $d f ph $.  $d ps x $.
    axcc4.1 $e |- A e. _V $.
    axcc4.2 $e |- N ~~ _om $.
    axcc4.3 $e |- ( x = ( f ` n ) -> ( ph <-> ps ) ) $.
    $( A version of ~ axcc3 that uses wffs instead of classes.  (Contributed by
       Mario Carneiro, 7-Apr-2013.) $)
    axcc4 $p |- ( A. n e. N E. x e. A ph ->
                    E. f ( f : N --> A /\ A. n e. N ps ) ) $=
      ( wrex wral cv wfn wcel wi wa wex ralimi syl6 crab c0 wne cfv rabex axcc3
      wf rabn0 pm2.27 sylbir elrab imbitrdi ral2imi simpl ffnfv imbitrrdi simpr
      anim2d adantld jcad eximdv mpi ) ACDKZFGLZEMZGNZACDUAZUBUCZFMVEUDZVGOZPZF
      GLZQZERGDVEUGZBFGLZQZEREFVGGACDHUEIUFVDVMVPEVDVMVNVOVDVMVFVIDOZFGLZQVNVDV
      LVRVFVDVLVQBQZFGLZVRVCVKVSFGVCVKVJVSVCVHVKVJPACDUHVHVJUIUJABCVIDJUKULUMZV
      SVQFGVQBUNSTURFGDVEUOUPVDVLVOVFVDVLVTVOWAVSBFGVQBUQSTUSUTVAVB $.
  $}

  ${
    $d f g x y $.
    $( An ~ ax-cc equivalent: every set has choice sets of length ` _om ` .
       (Contributed by Mario Carneiro, 31-Aug-2015.) $)
    acncc $p |- AC_ _om = _V $=
      ( vx vy vg vf com wacn cvv cv wcel cfv wral wex cpw c0 cdif cmap co wb wa
      csn vex omex isacn mp2an wfn wne wi axcc2 wf elmapi ffvelcdm eldifsni syl
      sylan id syl5com ralimdva adantld eximdv mpi mprgbir 2th eqriv ) AEFZGAHZ
      VDIZVEGIZVFBHZCHZJVHDHZJZIZBEKZCLZDVEMZNTOZEPQZVGEGIVFVNDVQKRAUAZUBBEDCGG
      VEUCUDVJVQIZVIEUEZVKNUFZVLUGZBEKZSZCLVNCBVJUHVSWDVMCVSWCVMVTVSWBVLBEVSVHE
      IZSWAWBVLVSEVPVJUIZWEWAVJVPEUJWFWESVKVPIWAEVPVHVJUKVKVONULUMUNWBUOUPUQURU
      SUTVAVRVBVC $.
  $}

  ${
    $d A f n x $.  $d N f n $.  $d f ph $.  $d ps x $.
    axcc4dom.1 $e |- A e. _V $.
    axcc4dom.2 $e |- ( x = ( f ` n ) -> ( ph <-> ps ) ) $.
    $( Relax the constraint on ~ axcc4 to dominance instead of equinumerosity.
       (Contributed by Mario Carneiro, 18-Jan-2014.) $)
    axcc4dom $p |- ( ( N ~<_ _om /\ A. n e. N E. x e. A ph ) ->
                    E. f ( f : N --> A /\ A. n e. N ps ) ) $=
      ( com cdom wbr wral wf wa wex cen wi raleq breq1 wrex cv csdm brdom2 wcel
      wo cfn isfinite ac6sfi ex sylbir cif wceq feq2 anbi12d imbi12d omex enref
      exbidv elimhyp axcc4 dedth jaoi sylbi imp ) GJKLZACDUAZFGMZGDEUBZNZBFGMZO
      ZEPZVFGJUCLZGJQLZUFVHVMRZGJUDVNVPVOVNGUGUEZVPGUHVQVHVMABFCGDEIUIUJUKVOVPV
      GFVOGJULZMZVRDVINZBFVRMZOZEPZRGJGVRUMZVHVSVMWCVGFGVRSWDVLWBEWDVJVTVKWAGVR
      DVIUNBFGVRSUOUSUPABCDEFVRHVOVRJQLJJQLGJGVRJQTJVRJQTJUQURUTIVAVBVCVDVE $.
  $}

  ${
    $d A b c n $.  $d A m n y $.  $d B b c $.  $d C c k n $.  $d b j k n $.
    $d b n y $.
    domtriomlem.1 $e |- A e. _V $.
    domtriomlem.2 $e |- B = { y | ( y C_ A /\ y ~~ ~P n ) } $.
    domtriomlem.3 $e |- C = ( n e. _om |->
                              ( ( b ` n ) \ U_ k e. n ( b ` k ) ) ) $.
    $( Lemma for ~ domtriom .  (Contributed by Mario Carneiro, 9-Feb-2013.) $)
    domtriomlem $p |- ( -. A e. Fin -> _om ~<_ A ) $=
      ( vc wcel cv com wral wex wbr wi wa cen vm vj cfn wn cfv cdom wfn wne wss
      c0 cpw cab cvv pwex simpl ss2abi df-pw sseqtrri ssexi eqeltri enref axcc3
      omex nfv nfra1 nfan ccrd nnfi pwfi sylib ficardom isinf wceq breq2 anbi2d
      exbidv rspcv syl5 3syl finnum cardid2 entr expcom 4syl anim2d eximdv syld
      cdm neeq1i bitri imbitrrdi com12 adantr rsp adantl ralrimi 3adant2 3expib
      abn0 mpdd mpi axcc2 w3a simp2 fvex sseq1 breq1 anbi12d elab2 simprbi ciun
      ralimi cdif fveq2 pweq breq12d cbvralvw csdm peano2 omelon onelssi ssralv
      weq csuc pwsdompw ex sdomdif eldifi biimtrdi sseld imp sylanbrc wel nnord
      word eleq1 3ad2ant3 3impib pm2.21dd 3exp syl6 difexi fvmpt2 mpan2 sylibrd
      biimtrid neeq1d syl5com jca wf1 eleq2d simplbi syl9 com23 com13 ffnfv w3o
      wf ordtri3or syl2an cbviunv iuneq1 eqtrid difeq12d rspccv mpbidi 3ad2ant1
      eleq12d syl11 imbitrid ssiun2 3ad2ant2 eldifbd 3adant1 2a1 ssiun2s eldifn
      a1i 3imp 3jaoi 3expia mpid com3r expd ralrimd ralrimiv dff13 19.8ad brdom
      sylibr exlimdv mpd exlimiv syl ) BUCLUDZFMZGMZUEZCLZFNOZGPZNBUFQZUWOUWQNU
      GZCUJUHZUWSRZFNOZSZGPUXAGFCNCAMZBUIZUXHUWPUKZTQZSZAULZUMIUXMBUKZBHUNUXMUX
      IAULUXNUXLUXIAUXIUXKUOUPABUQURUSUTNVCVAVBUWOUXGUWTGUWOUXCUXFUWTUWOUXFUWTU
      XCUWOUXFSZUWSFNUWOUXFFUWOFVDUXEFNVEVFUXOUWPNLZUXDUWSUWOUXPUXDRUXFUXPUWOUX
      DUXPUWOUXLAPZUXDUXPUWOUXIUXHUXJVGUEZTQZSZAPZUXQUXPUXJUCLZUXRNLZUWOUYARUXP
      UWPUCLUYBUWPVHUWPVIVJZUXJVKUWOUXIUXHUAMZTQZSZAPZUANOUYCUYAABUAVLUYHUYAUAU
      XRNUYEUXRVMZUYGUXTAUYIUYFUXSUXIUYEUXRUXHTVNVOVPVQVRVSUXPUXTUXLAUXPUXSUXKU
      XIUXPUYBUXJVGWHLUXRUXJTQZUXSUXKRUYDUXJVTUXJWAUXSUYJUXKUXHUXRUXJWBWCWDWEWF
      WGUXDUXMUJUHUXQCUXMUJIWIUXLAWSWJWKWLWMUXFUXPUXERUWOUXEFNWNWOWTWPWQWRWFXAU
      WTUXBGUWTKMZNUGZUWPUYKUEZUWPDUEZLZFNOZSZKPZUXBUWTUYLUYNUJUHZUYORZFNOZSZKP
      UYRKFDXBUWTVUBUYQKUWTUYLVUAUYQUWTUYLVUAXCUYLUYPUWTUYLVUAXDUWTVUAUYPUYLUWT
      VUASZUYOFNUWTVUAFUWSFNVEZUYTFNVEVFVUCUXPUYSUYOUWTUXPUYSRVUAUWTUWRUXJTQZFN
      OZUXPUYSUWSVUEFNUWSUWRBUIZVUEUXLVUGVUESAUWRCUWPUWQXEZUXHUWRVMUXIVUGUXKVUE
      UXHUWRBXFUXHUWRUXJTXGXHIXIZXJXLUXPVUFUWREUWPEMZUWQUEZXKZXMZUJUHZUYSVUFVUK
      VUJUKZTQZENOZUXPVUNVUEVUPFENFEYCZUWRVUKUXJVUOTUWPVUJUWQXNZUWPVUJXOXPXQUXP
      VUQVULUWRXRQZVUNUXPVUQVUPEUWPYDZOZVUTUXPVVANLVVANUIVUQVVBRUWPXSNVVAXTYAVU
      PEVVANYBVSUXPVVBVUTUWQEFYEYFWGVULUWRYGUUAUUFUXPUYNVUMUJUXPVUMUMLUYNVUMVMU
      WRVULVUHUUBFNVUMUMDJUUCUUDZUUGUUEUUHWMVUAUXPUYTRUWTUYTFNWNWOWTWPWQUUIWRWF
      XAUWTUYQUXBKUWTUYLUYPUXBUWTUYLUYPXCZNBUYKUUJZKPUXBVVDVVEKVVDNBUYKUURZVUJU
      YKUEZUYMVMZEFYCZRZFNOZENOZVVEVVDUYLUYMBLZFNOZVVFUWTUYLUYPXDUWTUYPVVNUYLUW
      TUYPSVVMFNUWTUYPFVUDUYOFNVEZVFUWTUYPUXPVVMRUXPUYPUWTVVMUXPUYPUYOUWTVVMRUY
      PUXPUYOUYOFNWNZWLUXPUWTUYOVVMUXPUWTUWSUYOVVMRUWTUXPUWSUWSFNWNWLUXPUYOUYMU
      WRLZUWSVVMUXPUYOUYMVUMLZVVQUXPUYNVUMUYMVVCUUKZUYMUWRVULYHZYIUWSUWRBUYMUWS
      VUGVUEVUIUULYJUUMWGUUNWGUUOYKWPWQFNBUYKUUPYLUYPUWTVVLUYLUYPVVKENUYPVUJNLZ
      VVJFNVVOVWAFVDUYPVWAUXPVVJVWAUXPSZVVHUYPVVIVWBVVHEFYMZVVIFEYMZUUQZUYPVVIR
      ZVWAVUJYOUWPYOVWEUXPVUJYNUWPYNVUJUWPUUSUUTVWAUXPVVHVWEVWFRVWEVWAUXPVVHXCZ
      VWFVWCVWGVWFRVVIVWDVWCVWGUYPVVIVWCVWGUYPXCUYMVULLZVVIVWCVWGUYPVWHVWGUYPSZ
      UYMVUKLZVWCVWHVWGUYPVWJVWGUYPVVGVUKUBVUJUBMZUWQUEZXKZXMZLZVWJVWAUXPUYPVWO
      RVVHVVRFNOVWAVWOUYPVVRVWOFVUJNVURUYMVVGVUMVWNUWPVUJUYKXNVURUWRVUKVULVWMVU
      SVURVULUBUWPVWLXKVWMEUBUWPVUKVWLVUJVWKUWQXNUVAUBUWPVUJVWLUVBUVCUVDUVHUVEU
      YPVVRFNVVOUXPUYOVVRUYPVVPVVSUVFZWPUVIUVGZVVHVWAVWOVWJRUXPVWOVVGVUKLVVHVWJ
      VVGVUKVWMYHVVGUYMVUKYPUVJYQWGYKVWCVUKVULUYMEUWPVUKUVKYJVRYRVWGUYPVWHUDVWC
      VWIUYMUWRVULVWGUYPVVRUXPVWAUYPVVRRVVHUYPUXPVVRVWPWLUVLYKZUVMUVNYSYTVVIVWG
      UYPUVOVWDVWGUYPVVIVWDVWGUYPXCUYMVWMLZVVIVWDVWGUYPVWSVWIVVRVWDVWSVWRVVRVVQ
      VWDVWSVVTVWDUWRVWMUYMUBVUJVWLUWPUWRVWKUWPUWQXNUVPYJVRVRYRVWDVWGUYPVWSUDZV
      WGUYPVWTRRVWDVWGUYPVWOVWTVWQVVHVWAVWOVWTRUXPVVHVWOUYMVWNLVWTVVGUYMVWNYPUY
      MVUKVWMUVQYIYQWGUVRUVSYSYTUVTWLUWAUWBUWCUWDUWEUWFYQEFNBUYKUWGYLUWHNBKHUWI
      UWJWRUWKUWLUWMUWN $.
  $}

  ${
    $d A b n y $.  $d b j k m n y $.
    domtriom.1 $e |- A e. _V $.
    $( Trichotomy of equinumerosity for ` _om ` , proven using countable
       choice.  Equivalently, all Dedekind-finite sets (as in ~ isfin4-2 ) are
       finite in the usual sense and conversely.  (Contributed by Mario
       Carneiro, 9-Feb-2013.) $)
    domtriom $p |- ( _om ~<_ A <-> -. A ~< _om ) $=
      ( vy vn vm vb vj vk com cdom wbr csdm wn domnsym cfn cfv ciun cdif fveq2
      cv wcel isfinite wss cpw cen wa cab cmpt eqid weq cbviunv iuneq1 difeq12d
      eqtrid cbvmptv domtriomlem sylnbir impbii ) IAJKZAILKZMIANUTAOUAUSAUBCACT
      ZAUCVADTZUDUEKUFCUGZEIETZFTZPZGVDGTZVEPZQZRZUHHDFBVCUIEDIVJVBVEPZHVBHTZVE
      PZQZREDUJZVFVKVIVNVDVBVESVOVIHVDVMQVNGHVDVHVMVGVLVESUKHVDVBVMULUNUMUOUPUQ
      UR $.
  $}

  $( Under countable choice, the IV-finite sets (Dedekind-finite) coincide with
     I-finite (finite in the usual sense) sets.  (Contributed by Mario
     Carneiro, 16-May-2015.) $)
  fin41 $p |- Fin4 = Fin $=
    ( vx cfin4 cfn cv com csdm wbr cdom wn vex domtriom con2bii isfinite wb cvv
    wcel isfin4-2 elv 3bitr4ri eqriv ) ABCADZEFGZEUAHGZIZUACPUABPZUCUBUAAJKLUAM
    UEUDNAUAOQRST $.

  ${
    $d x y w A $.
    dominf.1 $e |- A e. _V $.
    $( A nonempty set that is a subset of its union is infinite.  This version
       is proved from ~ ax-cc .  See ~ dominfac for a version proved from
       ~ ax-ac .  The axiom of Regularity is used for this proof, via
       ~ inf3lem6 , and its use is necessary: otherwise the set ` A = { A } `
       or ` A = { (/) , A } ` (where the second example even has nonempty
       well-founded part) provides a counterexample.  (Contributed by Mario
       Carneiro, 9-Feb-2013.) $)
    dominf $p |- ( ( A =/= (/) /\ A C_ U. A ) -> _om ~<_ A ) $=
      ( vx vy vw cv c0 wne cuni wss wa com cdom wbr wi eqid csdm wn cfn wcel id
      wceq neeq1 unieq sseq12d anbi12d breq2 imbi12d cpw cvv cin crab cmpt crdg
      cres wf1 inf3lem6 vpwex f1dom pwfi biimpi isfinite 3imtr3i con3i domtriom
      vex 3imtr4i 3syl vtocl ) CFZGHZVJVJIZJZKZLVJMNZOAGHZAAIZJZKZLAMNZOCABVJAU
      BZVNVSVOVTWAVKVPVMVRVJAGUCWAVJAVLVQWAUAVJAUDUEUFVJALMUGUHVNLVJUIZDUJEFVJU
      KDFJEVJULUMZGUNLUOZUPLWBMNZVOCDEAAWDWCWCPWDPBBUQLWBWDCURZUSWBLQNZRVJLQNZR
      WEVOWHWGVJSTZWBSTZWHWGWIWJVJUTVAVJVBWBVBVCVDWBWFVEVJCVFVEVGVHVI $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Introduce the Axiom of Dependent Choice
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d f n x y z $.
    $( Dependent Choice.  Axiom DC1 of [Schechter] p. 149.  This theorem is
       weaker than the Axiom of Choice but is stronger than Countable Choice.
       It shows the existence of a sequence whose values can only be shown to
       exist (but cannot be constructed explicitly) and also depend on earlier
       values in the sequence.  Dependent choice is equivalent to the statement
       that every (nonempty) pruned tree has a branch.  This axiom is redundant
       in ZFC; see ~ axdc .  But ZF+DC is strictly weaker than ZF+AC, so this
       axiom provides for theorems that do not need the full power of AC.
       (Contributed by Mario Carneiro, 25-Jan-2013.) $)
    ax-dc $a |- ( ( E. y E. z y x z /\ ran x C_ dom x ) ->
                  E. f A. n e. _om ( f ` n ) x ( f ` suc n ) ) $.
  $}

  ${
    $d s t $.  $d s t x $.  $d f x $.  $d f n s t x $.
    $( The Axiom of Dependent Choice implies Infinity, the way we have stated
       it.  Thus, we have _Inf+AC_ implies _DC_ and _DC_ implies _Inf_, but
       _AC_ does not imply _Inf_.  (Contributed by Mario Carneiro,
       25-Jan-2013.) $)
    dcomex $p |- _om e. _V $=
      ( vn vf vs vt cfv c1o cop csn wbr com wral wcel cdm wss wceq syl 1oex wex
      vx cv csuc cvv c0 wne 1n0 df-br elsni fvex opth1 sylbi tz6.12i vex breldm
      mpsyl ralimi dfss3 sylibr dmex ssex crn wa wi snex fvsn wfun funsn dmsnop
      snid eleqtrri funbrfvb mp2an mpbi breq12 spc2ev ax-mp breq 2exbidv mpbiri
      wb ssid rnsnop 3sstr4i rneq dmeq sseq12d pm5.5 syl2anc exbidv bitrd ax-dc
      ralbidv vtocl exlimiiv ) ATZBTZEZWNUAZWOEZFFGZHZIZAJKZJUBLZBXBJWOMZNZXCXB
      WNXDLZAJKXEXAXFAJXAWNFWOIZXFFUCUDXAWPFOZXGUEXAWPWRGZWTLZXHWPWRWTUFXJXIWSO
      XHXIWSUGWPWRFFWNWOUHWQWOUHUIPUJWNFWOUKUNWNFWOAULQUMPUOAJXDUPUQJXDWOBULURU
      SPCTZDTZSTZIZDRCRZXMUTZXMMZNZVAZWPWRXMIZAJKZBRZVBZXBBRZSWTWSVCXMWTOZYCYBY
      DYEXOXRYCYBVSYEXOXKXLWTIZDRCRZFFWTIZYGFWTEFOZYHFFQQVDWTVEFWTMZLYIYHVSFFQQ
      VFFFHZYJFQVHFFQVGZVIFFWTVJVKVLYFYHCDFFQQXKFXLFWTVMVNVOYEXNYFCDXKXLXMWTVPV
      QVRYEXRWTUTZYJNYKYKYMYJYKVTFFQWAYLWBYEXPYMXQYJXMWTWCXMWTWDWEVRXSYBWFWGYEY
      AXBBYEXTXAAJWPWRXMWTVPWKWHWISCDBAWJWLWM $.
  $}

  ${
    $d A g h $.  $d A h x y $.  $d F g h $.  $d F h x y $.  $d G g k $.
    $d G k x y $.  $d R h k r x $.  $d r x y $.
    axdc2lem.1 $e |- A e. _V $.
    axdc2lem.2 $e |- R = { <. x , y >. | ( x e. A /\ y e. ( F ` x ) ) } $.
    axdc2lem.3 $e |- G = ( x e. _om |-> ( h ` x ) ) $.
    $( Lemma for ~ axdc2 .  We construct a relation ` R ` based on ` F ` such
       that ` x R y ` iff ` y e. ( F `` x ) ` , and show that the "function"
       described by ~ ax-dc can be restricted so that it is a real function
       (since the stated properties only show that it is the superset of a
       function).  (Contributed by Mario Carneiro, 25-Jan-2013.)  (Revised by
       Mario Carneiro, 26-Jun-2015.) $)
    axdc2lem $p |- ( ( A =/= (/) /\ F : A --> ( ~P A \ { (/) } ) ) -> E. g
      ( g : _om --> A /\ A. k e. _om ( g ` suc k ) e. ( F ` ( g ` k ) ) ) ) $=
      ( c0 wa cfv com wex wcel wceq cvv vr wne cpw csn cdif wf cv csuc wbr wral
      cdm crn wss crab copab dmeqi cab 19.42v abbii dmopab df-rab 3eqtr4i eqtri
      ffvelcdm eldifsni n0 sylib ralrimiva rabid2 sylibr eqtr4id biimparc rneqi
      syl neeq1d rnopab wi eldifi elelpwi expcom 3syl expimpd eqsstrid sseqtrrd
      exlimdv abssdv adantl cun cuni cxp fvrn0 elssuni ax-mp sseli anim2i df-xp
      ssopab2i 3sstr4i pwex difexi ssex p0ex unexg sylancl uniexd xpexg sylancr
      frn ssexg eldm exbii bitr2i dmeq bitrid rneq sseq12d anbi12d breq ralbidv
      exbidv imbi12d ax-dc vtoclg mp2and simpr fveq2 fveq2d breq12d rspccv fvex
      vex suceq breldm syl6 imp adantll wb ex eleq1 fveq1 eleq2 ad2antrr impcom
      mpbid fmptd fvmpt peano2 fvmptg eleq2d anbi2d brab simprbi ralimia adantr
      biimtrrdi cmpt rgenw eqid fmpt mpbi dcomex rnex unex fex2 eqeltri eleq12d
      mp3an feq1 spcev syl2anc exlimiv sylc ) CMUBZCCUCZMUDZUEZHUFZNZGUGZFUGZOZ
      UVSUHZUVTOZDUIZGPUJZFQZUVQPCEUGZUFZUWBUWGOZUVSUWGOZHOZRZGPUJZNZEQZUVRDUKZ
      MUBZDULZUWPUMZUWFUVQUWQUVMUVQUWPCMUVQUWPBUGZAUGZHOZRZBQZACUNZCUWPUXACRZUX
      CNZABUOZUKZUXEDUXHKUPUXGBQZAUQUXFUXDNZAUQUXIUXEUXJUXKAUXFUXCBURUSUXGABUTU
      XDACVAVBVCUVQUXDACUJCUXESUVQUXDACUVQUXFNZUXBUVPRZUXDCUVPUXAHVDZUXMUXBMUBU
      XDUXBUVNMVEBUXBVFVGVNVHUXDACVIVJVKZVOVLUVQUWSUVMUVQUWRCUWPUVQUWRUXGAQZBUQ
      ZCUWRUXHULUXQDUXHKVMUXGABVPVCUVQUXPBCUVQUXGUWTCRZAUVQUXFUXCUXRUXLUXMUXBUV
      NRZUXCUXRVQUXNUXBUVNUVOVRUXCUXSUXRUWTUXBCVSVTWAWBWEWFWCUXOWDWGUVRDTRZUWQU
      WSNZUWFVQZUVRDCHULZUVOWHZWIZWJZUMUYFTRZUXTUXHUXFUWTUYERZNZABUODUYFUXGUYIA
      BUXCUYHUXFUXBUYEUWTUXBUYDRUXBUYEUMHUXAWKUXBUYDWLWMWNWOWQKABCUYEWPWRUVRCTR
      UYETRUYGJUVRUYDTUVRUYCTRZUVOTRUYDTRUVRUYCUVPUMZUYJUVQUYKUVMCUVPHXHWGUYCUV
      PUVNUVOCJWSWTXAVNXBUYCUVOTTXCXDXECUYETTXFXGDUYFTXIXGUXAUWTUAUGZUIBQZAQZUY
      LULZUYLUKZUMZNZUWAUWCUYLUIZGPUJZFQZVQUYBUADTUYLDSZUYRUYAVUAUWFVUBUYNUWQUY
      QUWSUYNUYPMUBZVUBUWQVUCUXAUYPRZAQUYNAUYPVFVUDUYMABUXAUYLAYKXJXKXLVUBUYPUW
      PMUYLDXMZVOXNVUBUYOUWRUYPUWPUYLDXOVUEXPXQVUBUYTUWEFVUBUYSUWDGPUWAUWCUYLDX
      RXSXTYAUAABFGYBYCVNYDUVMUVQYEUWEUVQUWOVQFUWEUVQUWOUWEUVQNPCIUFZUWBIOZUVSI
      OZHOZRZGPUJZUWOUVQUWEVUFUVQUWPCSZUWEVUFVQUXOVULUWEVUFVULUWENZAPUXAUVTOZCI
      VUMUXAPRZNVUNUWPRZVUNCRZUWEVUOVUPVULUWEVUOVUPUWEVUOVUNUXAUHZUVTOZDUIZVUPU
      WDVUTGUXAPUVSUXASZUWAVUNUWCVUSDUVSUXAUVTYFVVAUWBVURUVTUVSUXAYLYGYHYIVUNVU
      SDUXAUVTYJVURUVTYJYMYNYOYPVULVUPVUQYQUWEVUOUWPCVUNUUAUUBUUDLUUEYRVNUUCUWE
      VUKUVQUWDVUJGPUVSPRZUWDVUHVUGDUIZVUJVVBVUHUWAVUGUWCDAUVSVUNUWAPIUXAUVSUVT
      YFLUVSUVTYJUUFVVBUWBPRUWCTRVUGUWCSUVSUUGUWBUVTYJAUWBVUNUWCPTIUXAUWBUVTYFL
      UUHXDYHVVCVUHCRZVUJUXGVVDUWTVUIRZNVVDVUJNABVUHVUGDUVSIYJUWBIYJUXAVUHSZUXF
      VVDUXCVVEUXAVUHCYSVVFUXBVUIUWTUXAVUHHYFUUIXQUWTVUGSVVEVUJVVDUWTVUGVUIYSUU
      JKUUKUULUUOUUMUUNUWNVUFVUKNEIIAPVUNUUPZTLPUVTULZUVOWHZVVGUFZPTRVVITRVVGTR
      VUNVVIRZAPUJVVJVVKAPUVTUXAWKUUQAPVVIVUNVVGVVGUURUUSUUTUVAVVHUVOUVTFYKUVBX
      BUVCPVVIVVGTTUVDUVGUVEUWGISZUWHVUFUWMVUKPCUWGIUVHVVLUWLVUJGPVVLUWIVUGUWKV
      UIUWBUWGIYTVVLUWJVUHHUVSUWGIYTYGUVFXSXQUVIUVJYRUVKUVL $.
  $}

  ${
    $d A g h k $.  $d A h k s t x y $.  $d F g h k $.  $d F h k s t x y $.
    $d g h k n $.  $d h n x y $.
    axdc2.1 $e |- A e. _V $.
    $( An apparent strengthening of ~ ax-dc (but derived from it) which shows
       that there is a denumerable sequence ` g ` for any function that maps
       elements of a set ` A ` to nonempty subsets of ` A ` such that
       ` g ( x + 1 ) e. F ( g ( x ) ) ` for all ` x e. _om ` .  The finitistic
       version of this can be proven by induction, but the infinite version
       requires this new axiom.  (Contributed by Mario Carneiro,
       25-Jan-2013.) $)
    axdc2 $p |- ( ( A =/= (/) /\ F : A --> ( ~P A \ { (/) } ) ) -> E. g
      ( g : _om --> A /\ A. k e. _om ( g ` suc k ) e. ( F ` ( g ` k ) ) ) ) $=
      ( vx vy vs vt vh vn cv wcel cfv wa copab com weq eleq1w fveq2 cmpt adantr
      wb eleq2d sylan9bb anbi12d cbvopabv cbvmptv axdc2lem ) FGAHLZAMZILZUJDNZM
      ZOZHIPBJCDKQKLZJLZNZUAEUOFLZAMZGLUSDNZMZOHIFGHFRZIGRZOUKUTUNVBVCUKUTUCVDH
      FASUBVCUNULVAMVDVBVCUMVAULUJUSDTUDIGVASUEUFUGKFQURUSUQNUPUSUQTUHUI $.
  $}

  ${
    $d A n s $.
    axdc3lem.1 $e |- A e. _V $.
    axdc3lem.2 $e |- S = { s | E. n e. _om ( s : suc n --> A /\
       ( s ` (/) ) = C /\ A. k e. n ( s ` suc k ) e. ( F ` ( s ` k ) ) ) } $.
    $( The class ` S ` of finite approximations to the DC sequence is a set.
       (We derive here the stronger statement that ` S ` is a subset of a
       specific set, namely ` ~P ( _om X. A ) ` .)  (Contributed by Mario
       Carneiro, 27-Jan-2013.)  Remove unnecessary distinct variable
       conditions.  (Revised by David Abernethy, 18-Mar-2014.) $)
    axdc3lem $p |- S e. _V $=
      ( com cxp cpw dcomex xpex pwex cv csuc cfv wcel wss wf wceq wral w3a wrex
      c0 cab wa fssxp peano2 cvv con0 omelon2 ax-mp onelssi xpss1 3syl sylan9ss
      velpw sylibr ancoms 3ad2antr1 rexlimiva abssi eqsstri ssexi ) CJAKZLZVGJA
      MHNOCEPZQZAGPZUAZUFVKRBUBZDPZQVKRVNVKRFRSDVIUCZUDZEJUEZGUGVHIVQGVHVPVKVHS
      ZEJVIJSZVMVLVRVOVLVSVRVLVSUHVKVGTVRVLVSVKVJAKZVGVJAVKUIVSVJJSVJJTVTVGTVIU
      JJVJJUKSJULSMUMUNUOVJJAUPUQURGVGUSUTVAVBVCVDVEVF $.
  $}

  ${
    $d A g h $.  $d A n s $.  $d C g h $.  $d C n s $.  $d F g h $.
    $d F n s $.  $d G i j k m $.  $d S i j k m $.  $d S i k s $.
    $d S j m u v $.  $d S i x y $.  $d a b h j m u v $.  $d g h k $.
    $d h i j k m $.  $d h i k s $.  $d h i x y $.  $d k n s $.  $d s u v $.
    axdc3lem2.1 $e |- A e. _V $.
    axdc3lem2.2 $e |- S = { s | E. n e. _om ( s : suc n --> A /\
       ( s ` (/) ) = C /\ A. k e. n ( s ` suc k ) e. ( F ` ( s ` k ) ) ) } $.
    axdc3lem2.3 $e |- G = ( x e. S |-> { y e. S |
                             ( dom y = suc dom x /\ ( y |` dom x ) = x ) } ) $.
    $( Lemma for ~ axdc3 .  We have constructed a "candidate set" ` S ` , which
       consists of all finite sequences ` s ` that satisfy our property of
       interest, namely ` s ( x + 1 ) e. F ( s ( x ) ) ` on its domain, but
       with the added constraint that ` s ( 0 ) = C ` .  These sets are
       possible "initial segments" of the _infinite_ sequence satisfying these
       constraints, but we can leverage the standard ~ ax-dc (with no initial
       condition) to select a sequence of ever-lengthening finite sequences,
       namely ` ( h `` n ) : m --> A ` (for some integer ` m ` ).  We let our
       "choice" function select a sequence whose domain is one more than the
       last one, and agrees with the previous one on its domain.  Thus, the
       application of vanilla ~ ax-dc yields a sequence of sequences whose
       domains increase without bound, and whose union is a function which has
       all the properties we want.  In this lemma, we show that given the
       sequence ` h ` , we can construct the sequence ` g ` that we are after.
       (Contributed by Mario Carneiro, 30-Jan-2013.) $)
    axdc3lem2 $p |- ( E. h ( h : _om --> S /\
        A. k e. _om ( h ` suc k ) e. ( G ` ( h ` k ) ) ) ->
      E. g ( g : _om --> A /\ ( g ` (/) ) = C /\
        A. k e. _om ( g ` suc k ) e. ( F ` ( g ` k ) ) ) ) $=
      ( com wcel wa wceq wi vj vm vi vu vv vb va cv wf csuc cfv wral c0 w3a wex
      crn wfun cdm wss wel fveq2 dmeqd eleq12d eleq2 sseq2d imbi12d anbi12d weq
      id peano1 ffvelcdm mpan2 cab wrex word syl peano2 syl2anc 3ad2ant1 impcom
      nnord rexlimiva ss2abi eqsstri sseli fvex dmeq eleq2d eleq1d sylib simpld
      elab adantr ancoms adantrr suceq fveq2d simprd ordsucelsuc 3syl cres crab
      wb eqeq1d wo sseq1d biimprd com13 anim12d ex imp expcom ralrimdv ralrimiv
      syl6 frn rexlimivw sstrdi sseld vex imbitrdi wfn fvelrnb raleqbi1dv rspcv
      rspccv 3imp orcd 3exp com3r sseq12 rexlimdv ssel fnfvelrn funssfv syl3anc
      com23 fveq1 mpd adantlr cuni elequ2 0elsuc eleq1 biimprcd syl5com pm2.21i
      fdm noel jctir 2fveq3 rspcva adantrl eqeq2d reseq2d eqeq12d rabbidv rabex
      axdc3lem fvmpt reseq1 elrab bitrdi bitr4d biimpd resss sseq1 mpbii elsuci
      simplbda pm2.27 sstr2 a1d jaoi finds2 ffun funeq anim12i ordtri3or adantl
      ffn eqimss 2a1d olcd 3jaoi mpcom orbi12d biimpcd rexlimiv biimtrdi sylbid
      w3o exp4b com24 sylan jcad fununi syldan cop eldm2 eluni2 opeldm a1i elnn
      simprbi expcomd biimtrid exlimdv ciun eliuni dmuni eleqtrrdi impbid eqrdv
      syl2anr rnuni abid iunss sylibr eqsstrid biimpri sylanbr syl21anc sylancl
      df-fn df-f elssuni simp2 eqtrd nfv nfra1 ad2antrr syl2an mpan9 biimpa rsp
      nfan syl9r 3adant2 sstr syl3c ordtr trsuc 4syl simpl simpr mpbird ralrimi
      wtr rnex uniex feq1 ralbidv 3anbi123d spcev exlimiv ) PEGUHZUIZHUHZUJZVUQ
      UKZVUSVUQUKKUKZQZHPULZRZPCFUHZUIZUMVVFUKZDSZVUTVVFUKZVUSVVFUKZJUKZQZHPULZ
      UNZFUOZGVVEPCVUQUPZUUAZUIZUMVVRUKZDSZVUTVVRUKZVUSVVRUKZJUKZQZHPULZVVPVVEV
      VRUQZVVRURZPSZVVRUPZCUSZVVSVURVVDUAUHZVUQUKZUBUHZVUQUKZUSZUAVWNULZUBPULZV
      WGVVEVWQUBPVVEVWNPQZVWPUAVWNVWSVVEUAUBUTZVWPTZVWSVVERZVWNVWOURZQZVXAVWSVV
      EVXDVXARZVXEUMUMVUQUKZURZQZVWLUMQZVWMVXFUSZTZRZUCUHZVXMVUQUKZURZQZUAUCUTZ
      VWMVXNUSZTZRZVXMUJZVYAVUQUKZURZQZVWLVYAQZVWMVYBUSZTZRZVVEUBUCVWNUMSZVXDVX
      HVXAVXKVYIVWNUMVXCVXGVYIVIVYIVWOVXFVWNUMVUQVAZVBVCVYIVWTVXIVWPVXJVWNUMVWL
      VDVYIVWOVXFVWMVYJVEVFVGUBUCVHZVXDVXPVXAVXSVYKVWNVXMVXCVXOVYKVIVYKVWOVXNVW
      NVXMVUQVAZVBVCVYKVWTVXQVWPVXRUBUCUAUUBVYKVWOVXNVWMVYLVEVFVGVWNVYASZVXDVYD
      VXAVYGVYMVWNVYAVXCVYCVYMVIVYMVWOVYBVWNVYAVUQVAZVBVCVYMVWTVYEVWPVYFVWNVYAV
      WLVDVYMVWOVYBVWMVYNVEVFVGVURVXLVVDVURVXHVXKVURVXFEQZVXHVURUMPQZVYOVJPEUMV
      UQVKVLVYOVXHVXGPQZVYOVXFUMLUHZURZQZVYSPQZRZLVMZQVXHVYQRZEWUCVXFEIUHZUJZCV
      YRUIZUMVYRUKZDSZVUTVYRUKZVUSVYRUKZJUKZQZHWUEULZUNZIPVNZLVMZWUCNWUPWUBLWUO
      WUBIPWUOWUEPQZWUBWUGWUIWURWUBTWUNWUGVYSWUFSZWURWUBWUFCVYRUUHZWURUMWUFQZWU
      FPQZWUSWUBTWURWUEVOZWVAWUEWAZWUEUUCVPWUEVQWUSWUBWVAWVBRWUSVYTWVAWUAWVBVYS
      WUFUMVDVYSWUFPUUDVGUUEVRUUFVSVTWBWCWDZWEWUBWUDLVXFUMVUQWFZVYRVXFSZVYTVXHW
      UAVYQWVGVYSVXGUMVYRVXFWGZWHWVGVYSVXGPWVHWIVGWLWJWKVPZVXIVXJVWLUUIUUGUUJWM
      VXMPQZVVEVXTVYHTZWVJVVERVXNEQZVYBVXNKUKZQZWVKWVJVURWVLVVDVURWVJWVLPEVXMVU
      QVKWNWOWVJVVDWVNVURVVCWVNHVXMPHUCVHZVVAVYBVVBWVMWVOVUTVYAVUQVUSVXMWPWQVUS
      VXMKVUQUUKVCUULUUMWVLWVNRZVXPVYDVXSVYGWVPVXPVYDWVPVXPVYAVXOUJZQZVYDWVLVXP
      WVRXCZWVNWVLVXOPQZVXOVOWVSWVLUMVXOQZWVTWVLVXNWUCQWWAWVTRZEWUCVXNWVEWEWUBW
      WBLVXNVXMVUQWFVYRVXNSZVYTWWAWUAWVTWWCVYSVXOUMVYRVXNWGZWHWWCVYSVXOPWWDWIVG
      WLWJWRVXOWAVXMVXOWSWTWMWVPVYCWVQVYAWVPVYCWVQSZVYBVXOXAZVXNSZWVLWVNVYBEQZW
      WEWWGRZWVLWVNVYBBUHZURZWVQSZWWJVXOXAZVXNSZRZBEXBZQWWHWWIRWVLWVMWWPVYBAVXN
      WWKAUHZURZUJZSZWWJWWRXAZWWQSZRZBEXBWWPEKWWQVXNSZWXCWWOBEWXDWWTWWLWXBWWNWX
      DWWSWVQWWKWXDWWRVXOSWWSWVQSWWQVXNWGZWWRVXOWPVPUUNWXDWXAWWMWWQVXNWXDWWRVXO
      WWJWXEUUOWXDVIUUPVGUUQOWWOBECDEHIJLMNUUSUURUUTWHWWOWWIBVYBEWWJVYBSZWWLWWE
      WWNWWGWXFWWKVYCWVQWWJVYBWGXDWXFWWMWWFVXNWWJVYBVXOUVAXDVGUVBUVCUVJZWKWHUVD
      UVEWVPWWGVXNVYBUSZVXSVYGTWVPWWEWWGWXGWRWWGWWFVYBUSWXHVYBVXOUVFWWFVXNVYBUV
      GUVHVYEVXSWXHVYFVYEVXQUAUCVHZXEVXSWXHVYFTZTZVWLVXMUVIVXQWXKWXIVXQVXSVXRWX
      JVXQVXRUVKVWMVXNVYBUVLXOWXIWXJVXSWXIVYFWXHWXIVWMVXNVYBVWLVXMVUQVAXFXGUVMU
      VNVPXHWTXIVRXJUVOXKZWRXLXMXNVURVWRRZUDUHZUQZWXNUEUHZUSZWXPWXNUSZXEZUEVVQU
      LZRZUDVVQULVWGWXMWYAUDVVQWXMWXNVVQQZWXOWXTVURWYBWXOTVWRVURWYBWXNVYRUQZLVM
      ZQWXOVURVVQWYDWXNVURVVQEWYDPEVUQXPZEWUQWYDNWUPWYCLWUOWYCIPWUGWUIWYCWUNWUF
      CVYRUVPVSXQWCWDXRXSWYCWXOLWXNUDXTZVYRWXNUVQWLYAWMVURVUQPYBZVWRWYBWXTTPEVU
      QUWAZWYGVWRRWYBWXSUEVVQWYGVWRWYBWXPVVQQZWXSTTWYGWYIWYBVWRWXSWYGWYIUFUHZVU
      QUKZWXPSZUFPVNZWYBVWRWXSTZTUFPWXPVUQYCWYGWYBWYMWYNWYGWYBUGUHZVUQUKZWXNSZU
      GPVNZWYMWYNTUGPWXNVUQYCWYRWYLWYNUFPWYQWYJPQZWYLWYNTZTUGPWYOPQZWYSWYQWYTXU
      AWYSWYQWYLWYNXUAWYSRZVWRWYQWYLRZWXSXUBVWRWYPWYKUSZWYKWYPUSZXEZXUCWXSTWYOV
      OZWYJVOZRZXUBVWRXUFTZXUAXUGWYSXUHWYOWAWYJWAUVRXUIUGUFUTZUGUFVHZUFUGUTZUWL
      XUBXUJTZWYOWYJUVSXUKXUNXULXUMXUBVWRXUKXUFXUBVWRXUKXUFXUBVWRXUKUNXUDXUEXUB
      VWRXUKXUDWYSVWRXUKXUDTZTXUAWYSVWRVWMWYKUSZUAWYJULZXUOVWQXUQUBWYJPVWPXUPUA
      VWNWYJUBUFVHVWOWYKVWMVWNWYJVUQVAVEYDYEXUPXUDUAWYOWYJUAUGVHVWMWYPWYKVWLWYO
      VUQVAXFYFXOUVTYGYHYIYJXULXUFXUBVWRXULWYPWYKSZXUFWYOWYJVUQVAXURXUDXUEWYPWY
      KUWBYHVPUWCXUBVWRXUMXUFXUBVWRXUMXUFXUBVWRXUMUNXUEXUDXUBVWRXUMXUEXUAVWRXUM
      XUETZTWYSXUAVWRVWMWYPUSZUAWYOULZXUSVWQXVAUBWYOPVWPXUTUAVWNWYOUBUGVHVWOWYP
      VWMVWNWYOVUQVAVEYDYEXUTXUEUAWYJWYOUAUFVHVWMWYKWYPVWLWYJVUQVAXFYFXOWMYGUWD
      YIYJUWEVPUWFXUCXUFWXSXUCXUDWXQXUEWXRWYPWXNWYKWXPYKWYLWYQXUEWXRXCWYKWXPWYP
      WXNYKWNUWGUWHXOYQUWMYQUWIYLUWJYQUWKUWNXKXMUWOUWPXNVVQUDUEUWQVPUWRZVVEUBVW
      HPVVEVWNVWHQZVWSVURXVCVWSTVVDXVCVWNWXNUWSZVVRQZUDUOVURVWSUDVWNVVRUBXTZUWT
      VURXVEVWSUDXVEXVDWXPQZUEVVQVNVURVWSUEXVDVVQUXAVURXVGVWSUEVVQVURXVGWYIVWSV
      URXVGWYIRVWNWXPURZQZXVHPQZRVWSVURXVGXVIWYIXVJXVGXVITVURVWNWXNWXPXVFWYFUXB
      UXCVURVVQWUCUSZWYIXVJTVURVVQEWUCWYEWVEXRZXVKWYIWXPWUCQZXVJVVQWUCWXPYMXVMU
      MXVHQZXVJWUBXVNXVJRLWXPUEXTLUEVHZVYTXVNWUAXVJXVOVYSXVHUMVYRWXPWGZWHXVOVYS
      XVHPXVPWIVGWLUXEXOVPXIVWNXVHUXDXOUXFYLUXGUXHUXGWMVWSVVEXVCVXBVWNUDVVQWXNU
      RZUXIZVWHVXBVWOVVQQZVXDVWNXVRQVWSVURXVSVVDVURWYGVWSXVSVWSWYHVWSVIPVWNVUQY
      NUXOWOVXBVXDVXAWXLWKZUDVWOXVQVXCVVQVWNWXNVWOWGUXJVRUDVVQUXKUXLXLUXMUXNVUR
      VWKVVDVURVWJLVVQVYRUPZUXIZCLVVQUXPVURXWACUSZLVVQULXWBCUSVURXWCLVVQVURVVQX
      WCLVMZUSZVYRVVQQZXWCTVURVVQEXWDWYEEWUQXWDNWUPXWCLWUOXWCIPWUGWUIXWCWUNWUFC
      VYRXPVSXQWCWDXRXWEXWFVYRXWDQXWCVVQXWDVYRYMXWCLUXQYAVPXNLVVQXWACUXRUXSUXTW
      MVWGVWIRVVRPYBZVWKVVSVVRPUYEVVSXWGVWKRPCVVRUYFUYAUYBUYCVVEVVTUMVXFUKZDVVE
      VWGVXFVVRUSZVXHVVTXWHSXVBVVEVXFVVQQZXWIVURXWJVVDVURWYGVYPXWJWYHVJPUMVUQYN
      UYDWMZVXFVVQUYGVPVURVXHVVDWVIWMUMVVRVXFYOYPVVEXWJXWHDSZXWKVURXWJXWLTZVVDV
      URVVQWUILVMZUSZXWMVURVVQEXWNWYEEWUQXWNNWUPWUILWUOWUIIPWUGWUIWUNUYHXQWCWDX
      RXWOXWJVXFXWNQXWLVVQXWNVXFYMWUIXWLLVXFWVFWVGWUHXWHDUMVYRVXFYRXDWLYAVPWMYS
      UYIVVEVWEHPVURVVDHVURHUYJVVCHPUYKUYQVVEVUSPQZVWEVVEXWPRZVWEVUTVVAUKZVUSVV
      AUKZJUKZQZXWQVVQEUSZVVAVVQQZVUTVVAURZQZXXAVURXXBVVDXWPWYEUYLVURXWPXXCVVDV
      URWYGVUTPQZXXCXWPWYHVUSVQZPVUTVUQYNUYMZYTVVEVXDUBPULZXWPXXEVVEVXDUBPVWSVV
      EVXDXVTXLXNXWPXXFXXIXXETXXGVXDXXEUBVUTPVWNVUTSZVWNVUTVXCXXDXXJVIXXJVWOVVA
      VWNVUTVUQVAVBVCYEVPUYNZXXBXXCVVAVUTVYSQZWUMTZLVMZQXXEXXATZXXBVVQXXNVVAXXB
      EXXNUSVVQXXNUSEWUQXXNNWUPXXMLWUOXXMIPWUOWURXXMWUGWUNWURXXMTZWUIWUGWUNXXPW
      UGXXLWURWUNWUMWUGXXLWURWUNWUMTTZWUGXXLRVUTWUFQZXXQWUGWUSXXLXXRWUTWUSXXLXX
      RVYSWUFVUTVDUYOUWOWUNWURXXRWUMWURXXRHIUTZWUNWUMWURXXSXXRWURWVCXXSXXRXCWVD
      VUSWUEWSVPXGWUMHWUEUYPUYRXHVPXJUWNXKUYSVTWBWCWDVVQEXXNUYTVLXSXXMXXOLVVAVU
      TVUQWFZVYRVVASZXXLXXEWUMXXAXYAVYSXXDVUTVYRVVAWGZWHXYAWUJXWRWULXWTVUTVYRVV
      AYRXYAWUKXWSJVUSVYRVVAYRWQVCVFWLYAVUAXWQVWBXWRSZVWCXWSSZVWEXXAXCXWQVWGVVA
      VVRUSZXXEXYCVVEVWGXWPXVBWMZVURXWPXYEVVDVURXWPRZXXCXYEXXHVVAVVQUYGVPYTZXXK
      VUTVVRVVAYOYPXWQVWGXYEVUSXXDQZXYDXYFXYHXWQXXEXYIXXKVURXWPXXEXYITZVVDXYGXX
      DPQZXXDVOXXDVUIZXYJXYGUMXXDQZXYKXYGXXCXYMXYKRZXXHVURXXCXYNTXWPVURXXCVVAWU
      CQXYNVURVVQWUCVVAXVLXSWUBXYNLVVAXXTXYAVYTXYMWUAXYKXYAVYSXXDUMXYBWHXYAVYSX
      XDPXYBWIVGWLYAWMYSWRXXDWAXXDVUBXYLXXEXYIXXDVUSVUCXJVUDYTYSVUSVVRVVAYOYPXY
      CXYDRZVWBXWRVWDXWTXYCXYDVUEXYOVWCXWSJXYCXYDVUFWQVCVRVUGXJVUHVVOVVSVWAVWFU
      NFVVRVVQVUQGXTVUJVUKVVFVVRSZVVGVVSVVIVWAVVNVWFPCVVFVVRVULXYPVVHVVTDUMVVFV
      VRYRXDXYPVVMVWEHPXYPVVJVWBVVLVWDVUTVVFVVRYRXYPVVKVWCJVUSVVFVVRYRWQVCVUMVU
      NVUOYPVUP $.
  $}

  ${
    $d A m $.  $d A n s $.  $d B k m n $.  $d B k n s $.  $d C m $.
    $d C n s $.  $d F m $.  $d F n s $.
    axdc3lem3.1 $e |- A e. _V $.
    axdc3lem3.2 $e |- S = { s | E. n e. _om ( s : suc n --> A /\
       ( s ` (/) ) = C /\ A. k e. n ( s ` suc k ) e. ( F ` ( s ` k ) ) ) } $.
    axdc3lem3.3 $e |- B e. _V $.
    $( Simple substitution lemma for ~ axdc3 .  (Contributed by Mario Carneiro,
       27-Jan-2013.) $)
    axdc3lem3 $p |- ( B e. S <-> E. m e. _om ( B : suc m --> A /\
       ( B ` (/) ) = C /\ A. k e. m ( B ` suc k ) e. ( F ` ( B ` k ) ) ) ) $=
      ( wcel cv csuc wf c0 cfv wceq com wral w3a wrex eleq2i feq1 eqeq1d fveq2d
      cab fveq1 eleq12d ralbidv 3anbi123d rexbidv elab weq suceq feq2d 3anbi13d
      raleq cbvrexvw 3bitri ) BDMBGNZOZAINZPZQVDRZCSZENZOZVDRZVHVDRZHRZMZEVBUAZ
      UBZGTUCZIUHZMVCABPZQBRZCSZVIBRZVHBRZHRZMZEVBUAZUBZGTUCZFNZOZABPZVTWDEWHUA
      ZUBZFTUCDVQBKUDVPWGIBLVDBSZVOWFGTWMVEVRVGVTVNWEVCAVDBUEWMVFVSCQVDBUIUFWMV
      MWDEVBWMVJWAVLWCVIVDBUIWMVKWBHVHVDBUIUGUJUKULUMUNWFWLGFTGFUOZVRWJWEWKVTWN
      VCWIABVBWHUPUQWDEVBWHUSURUTVA $.
  $}

  ${
    $d A g h k $.  $d A k m n p x z $.  $d A h k s x $.  $d C g h k $.
    $d C k m n p z $.  $d C h k s $.  $d F g h k $.  $d F k m n p x z $.
    $d F h k s x $.  $d G h k $.  $d S h k s x $.  $d S k m x z $.
    $d S h x y $.  $d m x y z $.  $d n s x z $.
    axdc3lem4.1 $e |- A e. _V $.
    axdc3lem4.2 $e |- S = { s | E. n e. _om ( s : suc n --> A /\
       ( s ` (/) ) = C /\ A. k e. n ( s ` suc k ) e. ( F ` ( s ` k ) ) ) } $.
    axdc3lem4.3 $e |- G = ( x e. S |-> { y e. S |
                             ( dom y = suc dom x /\ ( y |` dom x ) = x ) } ) $.
    $( Lemma for ~ axdc3 .  We have constructed a "candidate set" ` S ` , which
       consists of all finite sequences ` s ` that satisfy our property of
       interest, namely ` s ( x + 1 ) e. F ( s ( x ) ) ` on its domain, but
       with the added constraint that ` s ( 0 ) = C ` .  These sets are
       possible "initial segments" of the _infinite_ sequence satisfying these
       constraints, but we can leverage the standard ~ ax-dc (with no initial
       condition) to select a sequence of ever-lengthening finite sequences,
       namely ` ( h `` n ) : m --> A ` (for some integer ` m ` ).  We let our
       "choice" function select a sequence whose domain is one more than the
       last one, and agrees with the previous one on its domain.  Thus, the
       application of vanilla ~ ax-dc yields a sequence of sequences whose
       domains increase without bound, and whose union is a function which has
       all the properties we want.  In this lemma, we show that ` S ` is
       nonempty, and that ` G ` always maps to a nonempty subset of ` S ` , so
       that we can apply ~ axdc2 .  See ~ axdc3lem2 for the rest of the proof.
       (Contributed by Mario Carneiro, 27-Jan-2013.) $)
    axdc3lem4 $p |- ( ( C e. A /\ F : A --> ( ~P A \ { (/) } ) ) ->
                E. g ( g : _om --> A /\ ( g ` (/) ) = C /\
                  A. k e. _om ( g ` suc k ) e. ( F ` ( g ` k ) ) ) ) $=
      ( wcel c0 wa cfv wceq wi vh vm vz vp cpw csn cdif wf com cv csuc wral wex
      w3a wne wrex peano1 eqid wb fsng mpan mpbiri snssi fssd suc0 feq2i sylibr
      cop fvsng ral0 a1i 3jca suceq feq2d raleq 3anbi13d sylancr snex axdc3lem3
      rspcev ne0d cdm cres crab cvv axdc3lem ssrab2 wn vex ffvelcdm sylan2 elsn
      necon3bbii sylib syl cun expcom 3syl 3ad2ant3 3ad2ant1 simplr word adantr
      wss cin adantl mpbird nnord disjsn df-suc ex a1d ancoms 3adant1 3imp wfun
      eleq2 eqtrid syl2anc funssfv syl3anc eqeq1d biimpar 3adant2 nf3an 3adant3
      nfv impcom biimparc syl2an fveq2d eleq12d 3adant2l 3expib fveq2 eqtrd mpd
      com3r 3impd com12 elpwi2 simp2 sucid mpan2 eldifn n0 bitri simp32 elelpwi
      fvex eldifi peano2 dmex mp2an simpr snssd fss fdm eleq1 ordirr mtbid sneq
      fun2d uneq2d eqtr4di ad2antlr mpbid adantrd ffun funsn jctir dmsnop funun
      ineq2i ssun1 0elsuc eleq2d adantrl nfra1 elsuci rsp ad2ant2lr ordsucelsuc
      adantlr biimpa 3adant1r ssun2 eqeq2d snid eleqtrri eqeltrrdi fvsn eqtr3di
      syl3an3 3expa 3adant1l biimprd jaoi impd ralrimi syl13anc unex 3coml 3exp
      expd sylcom com23 mpdi imp resundir wrel frel resdm incom eqeq1i wfn fnsn
      wo fnresdisj ax-mp 3bitr3ri uneq12d eqtrdi uneq2i dmun 3eqtr4i jctil dmeq
      un0 reseq1 anbi12d 3exp2 exlimdv mpan2d 3expd rexlimiv sylbi rabn0 eldifd
      rabex fmptd axdc2 axdc3lem2 ) DCOZCCUEZPUFZUGZIUHZQUIEUAUJZUHGUJZUKZVUIRV
      UJVUIRJROGUIULQUAUMZUICFUJZUHPVUMRDSVUKVUMRVUJVUMRIROGUIULUNFUMVUDEPUOEEU
      EZVUFUGZJUHVULVUHVUDEPDVHZUFZVUDUBUJZUKZCVUQUHZPVUQRDSZVUKVUQRVUJVUQRIROZ
      GVURULZUNZUBUIUPZVUQEOVUDPUIOZPUKZCVUQUHZVVAVVBGPULZUNZVVEUQVUDVVHVVAVVIV
      UDVUFCVUQUHVVHVUDVUFDUFZCVUQVUDVUFVVKVUQUHZVUQVUQSZVUQURVVFVUDVVLVVMUSUQP
      DUICVUQUTVAVBDCVCVDVVGVUFCVUQVEVFVGVVFVUDVVAUQPDUICVIVAVVIVUDVVBGVJVKVLVV
      DVVJUBPUIVURPSZVUTVVHVVCVVIVVAVVNVUSVVGCVUQVURPVMVNVVBGVURPVOVPVTVQCVUQDE
      GUBHIKLMVUPVRVSVGWAVUHAEBUJZWBZAUJZWBZUKZSZVVOVVRWCZVVQSZQZBEWDZVUOJVUHVV
      QEOZQZVWDVUNVUFVWDVUNOVWFVWDEWECDEGHIKLMWFZVWCBEWGUUAVKVWFVWDPUOZVWDVUFOZ
      WHVWFVWCBEUPZVWHVWEVUHVWJVWEVUSCVVQUHZPVVQRZDSZVUKVVQRZVUJVVQRZIRZOZGVURU
      LZUNZUBUIUPVUHVWJTZCVVQDEGUBHIKLMAWIZVSVWSVWTUBUIVWSVURUIOZVWTVWKVWMVWRVX
      BVWTTZVWMVWRVWKVXCVWMVWRVWKVXBVWTVWRVWKVXBUNZVUHVWMVWJVXDVUHVWKVWMVWJTVWR
      VWKVXBUUBVUHVWKQZVWMVXDVWJVXEUCUJZVURVVQRZIRZOZUCUMZVWMVXDVWJTTZVXEVXHVUG
      OZVXJVWKVUHVXGCOZVXLVWKVURVUSOVXMVURUBWIUUCVUSCVURVVQWJUUDCVUGVXGIWJWKZVX
      LVXHVUFOZWHZVXJVXHVUEVUFUUEVXPVXHPUOVXJVXOVXHPVXHPVXGIUUJWLWMUCVXHUUFUUGW
      NWOVUHVXJVXKTVWKVUHVXIVXKUCVUHVXIVWMVXDVWJVUHVXIVWMVXDUNZQZVVQVVRVXFVHZUF
      ZWPZEOZVYAWBZVVSSZVYAVVRWCZVVQSZQZVWJVUHVXQVYBVUHVXQVWKVYBVXIVWMVWRVWKVXB
      UUHVUHVWKVXQVYBVUHVWKVXQVYBTVXEVXIVWMVXDVYBVXEVXIVXFCOZVWMVXDVYBTZTVXEVXL
      VXHVUEOZVXIVYHTVXNVXHVUEVUFUUKVXIVYJVYHVXFVXHCUUIWQWRVXIVYHVWMVYIVXIVYHVW
      MQZVXDVYBVXDVXIVYKVYBVXDVXIVYKUNZUDUJZUKZCVYAUHZPVYARZDSZVUKVYARZVUJVYARZ
      IRZOZGVYMULZUNZUDUIUPZVYBVYLVUSUIOZVUSUKZCVYAUHZVYQWUAGVUSULZWUDVXDVXIWUE
      VYKVXBVWRWUEVWKVURUULZWSWTVXDVXIVYKWUGVWKVXBVXIVYKWUGTZTZVWRVXBVWKWUKVXBV
      WKQZWUJVXIWULVYHWUGVWMWULVYHWUGWULVYHQZVUSVVRUFZWPZCVYAUHWUGWUMVUSWUNCVVQ
      VXTVXBVWKVYHXAWUMWUNVXFUFZVXTUHZWUPCXDWUNCVXTUHVVRWEOZVXFWEOZWUQVVQVXAUUM
      ZUCWIZWURWUSQWUQVXTVXTSVXTURVVRVXFWEWEVXTUTVBUUNWUMVXFCWULVYHUUOUUPWUNWUP
      CVXTUUQVQWULVUSWUNXEPSZVYHVWKVXBVVRVUSSZWVBVUSCVVQUURZVXBWVCQZVVRVUSOZWHW
      VBWVEVVRVVROZWVFWVEVVRUIOZVVRXBZWVGWHZWVEWVHWUEVXBWUEWVCWUIXCWVCWVHWUEUSV
      XBVVRVUSUIUUSXFXGZVVRXHZVVRUUTZWRZWVCWVGWVFUSVXBVVRVUSVVRXQXFUVAVUSVVRXIV
      GWKXCUVCWUMWUOWUFCVYAVWKWUOWUFSZVXBVYHVWKWVCWVOWVDWVCWUOVUSVUSUFZWPWUFWVC
      WUNWVPVUSVVRVUSUVBUVDVUSXJUVEWOUVFVNUVGXKUVHXLXMXNXOVXDVYKVYQVXIVXDVWMVYQ
      VYHVXDVYQVWMVWKVXBVYQVWMUSZVWRVXBVWKWVQWULVYPVWLDWULVYAXPZVVQVYAXDZPVVROZ
      VYPVWLSWULVVQXPZVXTXPZQVVRVXTWBZXEZPSZWVRWULWWAWWBVWKWWAVXBVUSCVVQUVIXFVV
      RVXFWUTWVAUVJUVKVWKVXBWVCWWEWVDWVEWWDVVRWUNXEZPWWCWUNVVRVVRVXFWVAUVLZUVNW
      VEWVJWWFPSZWVNVVRVVRXIZVGXRWKVVQVXTUVMXSZWVSWULVVQVXTUVOZVKWULWVTPVUSOZVX
      BWWLVWKVXBVURXBZWWLVURXHZVURUVPWOXCVWKWVTWWLUSVXBVWKVVRVUSPWVDUVQXFXGPVYA
      VVQXTYAYBXMXNYCUVRYDVYLWUAGVUSVXDVXIVYKGVWRVWKVXBGVWQGVURUVSVWKGYGVXBGYGY
      EVXIGYGVYKGYGYEVXDVXIVUJVUSOZWUATVYKWWOVXDVXIQWUAWWOVXDVXIWUAWWOVWRVWKVXB
      VXIWUATZVWRWWOVWKVXBWWPTZTVWRWWOQZVWKWWQWWRVWKQZWWOWWQVWRWWOVWKXAWWOVXBWW
      SWWPWWOVUJVUROZVUJVURSZUXRVXBWWSWWPTZTZVUJVURUVTWWTWXCWXAVXBWWTWXBVXBWWTQ
      ZWWRVWKWWPWXDWWRVWKUNZWUAVXIWXEWUAVWQWXDWWRVWQVWKWWTVWRVWQVXBWWOVWRWWTVWQ
      VWQGVURUWAYHUWBYFWXDWWOVWKWUAVWQUSVWRWXDWWOVWKUNZVYRVWNVYTVWPWXDVWKVYRVWN
      SZWWOWXDVWKQZWVRWVSVUKVVROZWXGVXBVWKWVRWWTWWJUWDWVSWXHWWKVKWXDVUKVUSOZWVC
      WXIVWKVXBWWTWXJVXBWWMWWTWXJUSWWNVUJVURUWCWOUWEWVDWVCWXIWXJVVRVUSVUKXQYIYJ
      VUKVYAVVQXTYAYDWXFVYSVWOIVXBWWOVWKVYSVWOSZWWTVXBWWOVWKUNZWVRWVSVUJVVROZWX
      KVXBVWKWVRWWOWWJYDWVSWXLWWKVKWWOVWKWXMVXBVWKWWOWVCWXMWVDWVCWXMWWOVVRVUSVU
      JXQYIWKXNVUJVYAVVQXTYAZUWFYKYLYMXGXLYNWQWXAVXBWXBWXAVXBQZWWRVWKWWPWXOWWRV
      WKUNWUAVXIWXOWWOVWKWUAVXIUSVWRWXOWWOVWKUNZVYRVXFVYTVXHWXOVWKVYRVXFSZWWOWX
      AVXBVWKWXQWXAVXBVWKUNZVYRVUKVXTRZVXFWXRWVRVXTVYAXDZVUKWWCOZVYRWXSSVXBVWKW
      VRWXAWWJXNWXTWXRVXTVVQUWGVKWXAVWKWYAVXBVWKWXAWVCWYAWVDWXAWVCQVUKVVRWWCWXA
      VVRVUKSZWVCWXAVUKVUSVVRVUJVURVMUWHYCZVVRWUNWWCVVRWUTUWIWWGUWJUWKWKYDVUKVY
      AVXTXTYAVWKWXAVXBWVCWXSVXFSZWVDWXAVXBWVCUNWYBWYDWXAWVCWYBVXBWYCYDWYBVVRVX
      TRWXSVXFVVRVUKVXTYOVVRVXFWUTWVAUWLUWMWOUWNYPUWOYDWXPVYSVXGIWXPVYSVWOVXGVX
      BWWOVWKWXKWXAWXNUWPWXOWWOVWOVXGSZVWKWXAWYEVXBVUJVURVVQYOXCWTYPYKYLYMUWQYN
      XKUWRWOYRYQXKWQYSUWSYTYFUWTWUCWUGVYQWUHUNUDVUSUIVYMVUSSZVYOWUGWUBWUHVYQWY
      FVYNWUFCVYAVYMVUSVMVNWUAGVYMVUSVOVPVTUXACVYADEGUDHIKLMVVQVXTVXAVXSVRUXBVS
      VGUXCUXDUXEUXFYSXKUXGUXHUXIVXRVYFVYDVXQVYFVUHVXDVXIVYFVWMVWKVXBVYFVWRVXBV
      WKVYFWULVYEVVQVVRWCZVXTVVRWCZWPZVVQVVQVXTVVRUXJWULWYIVVQPWPVVQWULWYGVVQWY
      HPVWKWYGVVQSZVXBVWKVVQUXKWYJVUSCVVQUXLVVQUXMWOXFWULWVHWYHPSZVWKVXBWVCWVHW
      VDWVKWKWVHWVJWYKWVHWVIWVJWVLWVMWOWUNVVRXEZPSZWWHWYKWVJWYLWWFPWUNVVRUXNUXO
      VXTWUNUXPWYMWYKUSVVRVXFWUTWVAUXQWUNVVRVXTUXSUXTWWIUYAWNWOUYBVVQUYIUYCXRXM
      XNWSXFVVRWWCWPVVRWUNWPVYCVVSWWCWUNVVRWWGUYDVVQVXTUYEVVRXJUYFUYGVWCVYGBVYA
      EVVOVYASZVVTVYDVWBVYFWYNVVPVYCVVSVVOVYAUYHYBWYNVWAVYEVVQVVOVYAVVRUYJYBUYK
      VTXSUYLUYMXCYQYRUYNYRUYOYRXOYTUYPUYQYHVWCBEUYRVGVWIVWDPVWDPVWCBEVWGUYTWLW
      MVGUYSNVUAEUAGJVWGVUBYJABCDEFUAGHIJKLMNVUCWO $.
  $}

  ${
    $d A g k $.  $d A k n s t x $.  $d A k n t x y $.  $d C g k $.
    $d C k n s t x $.  $d C k n t x y $.  $d F g k $.  $d F j k n s t x $.
    $d F j k n t x y $.
    axdc3.1 $e |- A e. _V $.
    $( Dependent Choice.  Axiom DC1 of [Schechter] p. 149, with the addition of
       an initial value ` C ` .  This theorem is weaker than the Axiom of
       Choice but is stronger than Countable Choice.  It shows the existence of
       a sequence whose values can only be shown to exist (but cannot be
       constructed explicitly) and also depend on earlier values in the
       sequence.  (Contributed by Mario Carneiro, 27-Jan-2013.) $)
    axdc3 $p |- ( ( C e. A /\ F : A --> ( ~P A \ { (/) } ) ) ->
                E. g ( g : _om --> A /\ ( g ` (/) ) = C /\
                  A. k e. _om ( g ` suc k ) e. ( F ` ( g ` k ) ) ) ) $=
      ( vx vy vn vt vj vs cv csuc c0 cfv wceq wcel wral com wf w3a wrex cab cdm
      cres wa crab cmpt feq1 fveq1 eqeq1d fveq2d eleq12d ralbidv suceq cbvralvw
      2fveq3 bitrdi 3anbi123d rexbidv cbvabv eqid axdc3lem4 ) GHABIMZNZAJMZUAZO
      VGPZBQZKMZNZVGPZVKVGPZEPZRZKVESZUBZITUCZJUDZCDIEGVTHMZUEGMZUEZNQWAWCUFWBQ
      UGHVTUHUIZLFVSVFALMZUAZOWEPZBQZDMZNZWEPZWIWEPEPZRZDVESZUBZITUCJLVGWEQZVRW
      OITWPVHWFVJWHVQWNVFAVGWEUJWPVIWGBOVGWEUKULWPVQVLWEPZVKWEPZEPZRZKVESWNWPVP
      WTKVEWPVMWQVOWSVLVGWEUKWPVNWREVKVGWEUKUMUNUOWTWMKDVEVKWIQZWQWKWSWLXAVLWJW
      EVKWIUPUMVKWIEWEURUNUQUSUTVAVBWDVCVD $.
  $}

  ${
    $d g h i k m n s t x z A $.  $d g h i k m z C $.  $d g h n s t x z F $.
    $d h i k m z G $.
    axdc4lem.1 $e |- A e. _V $.
    axdc4lem.2 $e |- G
        = ( n e. _om , x e. A |-> ( { suc n } X. ( n F x ) ) ) $.
    $( Lemma for ~ axdc4 .  (Contributed by Mario Carneiro, 31-Jan-2013.)
       (Revised by Mario Carneiro, 16-Nov-2013.) $)
    axdc4lem $p |- ( ( C e. A /\ F : ( _om X. A ) --> ( ~P A \ { (/) } ) ) ->
                E. g ( g : _om --> A /\ ( g ` (/) ) = C /\
                  A. k e. _om ( g ` suc k ) e. ( k F ( g ` k ) ) ) ) $=
      ( vz wcel com c0 wa cfv wceq wex wi c2nd vh vm vi vt vs cxp cpw csn wf cv
      cdif cop csuc wral w3a peano1 opelxpi mpan simp2 fovcdm wss peano2 eldifi
      co snssd elpw2 xpss12 sylan2b syl2an snex ovex xpex sylibr syl2anc eldifn
      elpw wn wne elsn necon3bbii vex sucex snnz xpnz biimpi 3syl eldifd 3expib
      sylbi ralrimivv fmpo sylib dcomex ccom cvv 2ndcof 3ad2ant1 adantl mp3an23
      axdc3 fex2 syl fvco3 mpan2 fveq2 3ad2ant2 eqtrd op2ndg nfv eqeq12d exbidv
      opeq1 weq opeq2 eqeq2d df-ov simplr ffvelcdm eleq1 opelxp2 biimtrdi suceq
      sneqd oveq1 xpeq12d oveq2 xpeq2d ovmpo fveq2d eleq12d exlimiv com3l com12
      imp elxp op2nd eqtrdi oveq2d ex fveq1 sylan9eqr nfra1 nfan spcegv eqtr4di
      nf3an 3ad2antr2 mpan9 2fveq3 rspcv ad2antlr eleq2 biimpac adantrr sylsyld
      velsn eximi expcom cbvexvw syl8ib impancom 3adant2 finds2 ralrimiv rspccv
      3impia simp21 simp3 rspa 3adant1 simpl simprr impel eqtr3id eleq2d sylan2
      3ad2antl3 simpll biimprcd impcom exlimivv sylbid syl121anc 3expia ralrimi
      exp4c 3imp 3jca feq1 eqeq1d ralbidv 3anbi123d spcedv exlimdv adantr mpd )
      CBLZMBUFZBUGZNUHZUKZGUIZOMUWRUAUJZUIZNUXCPZNCULZQZEUJZUMZUXCPZUXHUXCPZHPZ
      LZEMUNZUOZUARZMBDUJZUIZNUXQPZCQZUXIUXQPZUXHUXHUXQPZGVDZLZEMUNZUOZDRZUWQUX
      FUWRLZUWRUWRUGZUWTUKZHUIZUXPUXBNMLZUWQUYHUPNCMBUQURUXBFUJZUMZUHZUYMAUJZGV
      DZUFZUYJLZABUNFMUNUYKUXBUYSFAMBUXBUYMMLZUYPBLZUYSUXBUYTVUAUOZUYRUYIUWTVUB
      UYTUYQUXALZUYRUYILZUXBUYTVUAUSUYMUYPUXAMBGUTZUYTVUCOUYRUWRVAZVUDUYTUYOMVA
      ZUYQUWSLZVUFVUCUYTUYNMUYMVBVEUYQUWSUWTVCVUHVUGUYQBVAVUFUYQBIVFUYOMUYQBVGV
      HVIUYRUWRUYOUYQUYNVJUYMUYPGVKZVLZVPVMVNVUBVUCUYQUWTLZVQZUYRUWTLZVQZVUEUYQ
      UWSUWTVOVULUYRNVRZVUNVULUYQNVRZVUOVUKUYQNUYQNVUIVSVTUYONVRZVUPVUOUYNUYMFW
      AWBWCVUQVUPOVUOUYOUYQWDWEURWIVUMUYRNUYRNVUJVSVTVMWFWGWHWJFAMBUYRUYJHJWKWL
      UWRUXFUAEHMBWMIVLWTVIUWQUXPUYGSUXBUWQUXOUYGUAUWQUXOUYGUWQUXOOZUYFMBTUXCWN
      ZUIZNVUSPZCQZUXIVUSPZUXHUXHVUSPZGVDZLZEMUNZUODWOVUSVURVUTVUSWOLZUXOVUTUWQ
      UXDUXGVUTUXNMMBUXCWPWQWRZVUTMWOLBWOLVVHWMIMBVUSWOWOXAWSXBVURVUTVVBVVGVVIU
      XOUWQVVAUXFTPZCUXOVVAUXETPZVVJUXDUXGVVAVVKQZUXNUXDUYLVVLUPMUWRNTUXCXCXDWQ
      UXGUXDVVKVVJQUXNUXEUXFTXEXFXGUYLUWQVVJCQUPNCMBXHURUUAVURVVFEMUWQUXOEUWQEX
      IUXDUXGUXNEUXDEXIUXGEXIUXMEMUUBUUFUUCUWQUXOUXHMLZVVFUWQUXOVVMUOUXKUXHKUJZ
      ULZQZKRZUXDVVMUXMVVFUWQUXOVVMVVQVURUBUJZUXCPZVVRVVNULZQZKRZUBMUNVVMVVQSVU
      RVWBUBMVVRMLVURVWBVWBUXENVVNULZQZKRZUCUJZUXCPZVWFVVNULZQZKRZVWFUMZUXCPZVW
      KVVNULZQZKRZVURUBUCVVRNQZVWAVWDKVWPVVSUXEVVTVWCVVRNUXCXEVVRNVVNXLXJXKUBUC
      XMZVWAVWIKVWQVVSVWGVVTVWHVVRVWFUXCXEVVRVWFVVNXLXJXKVVRVWKQZVWAVWNKVWRVVSV
      WLVVTVWMVVRVWKUXCXEVVRVWKVVNXLXJXKUWQUXDUXGVWEUXNUWQUXGVWEVWDUXGKCBVVNCQV
      WCUXFUXEVVNCNXNXOUUDYNUUGVURVWFMLZVWJVWOSZUXOVWSVWTSZUWQUXDUXNVXAUXGUXDVW
      SUXNVWTUXDVWSOZUXNVWJVWLVWKUDUJZULZQZUDRZVWOVWJVXBUXNVXFVWIVXBUXNVXFSZSKV
      XBVWIVXGVXBVWIOZVWGHPZVWKUHZVWFVVNGVDZUFZQZUXNVWLVXILZVXFVXHVXIVWFVVNHVDZ
      VXLVWIVXIVXOQVXBVWIVXIVWHHPVXOVWGVWHHXEVWFVVNHXPUUEWRVXHVWSVVNBLZVXOVXLQU
      XDVWSVWIXQVXBVWGUWRLZVWIVXPMUWRVWFUXCXRVWIVXQVWHUWRLVXPVWGVWHUWRXSVWFVVNM
      BXTYAUUHFAVWFVVNMBUYRVXLHVXJVWFUYPGVDZUFFUCXMZUYOVXJUYQVXRVXSUYNVWKUYMVWF
      YBYCUYMVWFUYPGYDYEAKXMZVXRVXKVXJUYPVVNVWFGYFYGJVXJVXKVWKVJVWFVVNGVKVLYHVN
      XGVWSUXNVXNSUXDVWIUXMVXNEVWFMEUCXMZUXJVWLUXLVXIVYAUXIVWKUXCUXHVWFYBYIUXHV
      WFHUXCUUIYJUUJUUKVXMVXNVWLVXLLZVXFVXIVXLVWLUULVYBVWLUEUJZVXCULZQZVYCVXJLZ
      VXCVXKLZOOZUDRZUERVXFUEUDVWLVXJVXKYOVYIVXFUEVYHVXEUDVYEVYFVXEVYGVYFVYEVXE
      VYFVYDVXDVWLVYFVYCVWKQVYDVXDQUEVWKUUPVYCVWKVXCXLWIXOUUMUUNUUQYKWIYAUUOUUR
      YKYLVXEVWNUDKUDKXMVXDVWMVWLVXCVVNVWKXNXOUUSUUTUVAUVBWRYMUVCYMUVDVWBVVQUBU
      XHMUBEXMZVWAVVPKVYJVVSUXKVVTVVOVVRUXHUXCXEVVRUXHVVNXLXJXKUVEXBUVFUWQUXDUX
      GUXNVVMUVGUWQUXOVVMUVHUXOVVMUXMUWQUXNUXDVVMUXMUXGUXMEMUVIUVQUVJVVQUXDVVMO
      ZUXMVVFVVPVYKUXMVVFSZSKVVPVYKVYLVVPVYKOZUXMUXJUXIUHZUXHVVNGVDZUFZLZVVFVYM
      UXLVYPUXJVYMUXLVVOHPZVYPVYMUXKVVOHVVPVYKUVKYIVYMVVMVXPVYRVYPQVVPUXDVVMUVL
      VVPUXKUWRLZVXPVYKVVPVYSVVOUWRLVXPUXKVVOUWRXSUXHVVNMBXTYAMUWRUXHUXCXRUVMVV
      MVXPOVYRUXHVVNHVDVYPUXHVVNHXPFAUXHVVNMBUYRVYPHVYNUXHUYPGVDZUFFEXMZUYOVYNU
      YQVYTWUAUYNUXIUYMUXHYBYCUYMUXHUYPGYDYEVXTVYTVYOVYNUYPVVNUXHGYFYGJVYNVYOUX
      IVJUXHVVNGVKVLYHUVNVNXGUVOVVPVYKVYQVVFSVYQVVPVYKVVFVYQUXJVYDQZVYCVYNLZVXC
      VYOLZOZOZUDRUERVVPVYKVVFSSZUEUDUXJVYNVYOYOWUFWUGUEUDWUEWUBWUGWUDWUBWUGSWU
      CWUDWUBVVPVYKVVFWUBVVPOZVYKOZVVFWUDWUIVVCVXCVVEVYOWUIVVCVYDTPZVXCWUIVVCUX
      JTPZWUJVYKVVCWUKQZWUHVVMUXDUXIMLWULUXHVBMUWRUXITUXCXCUVPWRWUIUXJVYDTWUBVV
      PVYKUVRYIXGVYCVXCUEWAUDWAYPYQWUIVVDVVNUXHGWUIVVDVVOTPZVVNWUIVVDUXKTPZWUMV
      YKVVDWUNQWUHMUWRUXHTUXCXCWRWUIUXKVVOTWUBVVPVYKXQYIXGUXHVVNEWAKWAYPYQYRYJU
      VSUWFWRUVTUWAWIYLYNUWBYSYKUWGUWCUWDUWEUWHUXQVUSQZUXRVUTUXTVVBUYEVVGMBUXQV
      USUWIWUOUXSVVACNUXQVUSYTUWJWUOUYDVVFEMWUOUYAVVCUYCVVEUXIUXQVUSYTWUOUYBVVD
      UXHGUXHUXQVUSYTYRYJUWKUWLUWMYSUWNUWOUWP $.
  $}

  ${
    $d A g k n x $.  $d C g k $.  $d F g k n x $.
    axdc4.1 $e |- A e. _V $.
    $( A more general version of ~ axdc3 that allows the function ` F ` to vary
       with ` k ` .  (Contributed by Mario Carneiro, 31-Jan-2013.) $)
    axdc4 $p |- ( ( C e. A /\ F : ( _om X. A ) --> ( ~P A \ { (/) } ) ) ->
                E. g ( g : _om --> A /\ ( g ` (/) ) = C /\
                  A. k e. _om ( g ` suc k ) e. ( k F ( g ` k ) ) ) ) $=
      ( vx vn com cv csuc csn co cxp cmpo eqid axdc4lem ) GABCDHEHGIAHJZKLRGJEM
      NOZFSPQ $.
  $}

  ${
    $d A c f h $.  $d A f h i n y $.  $d A c h k $.  $d A f h w z $.
    $d F c h k $.  $d F h i k z $.  $d G g z $.  $d G i z $.  $d f g h x $.
    axcclem.1 $e |- A = ( x \ { (/) } ) $.
    axcclem.2 $e |- F = ( n e. _om , y e. U. A |-> ( f ` n ) ) $.
    axcclem.3 $e |- G = ( w e. A |-> ( h ` suc ( `' f ` w ) ) ) $.
    $( Lemma for ~ axcc .  (Contributed by Mario Carneiro, 2-Feb-2013.)
       (Revised by Mario Carneiro, 16-Nov-2013.) $)
    axcclem $p |- ( x ~~ _om ->
       E. g A. z e. x ( z =/= (/) -> ( g ` z ) e. z ) ) $=
      ( cv com c0 cfv wcel wceq vk vc vi cen wbr wne wi wral wex cdom wn wa cfn
      csdm isfinite2 csn cdif eleq1i cun undif1 snfi unfi mpan2 eqeltrrid ssun1
      wss ssfi sylancl sylbi cvv wb isfiniteg ax-mp sdomnen 3syl con2i sdomentr
      dcomex expcom mtod vex difss eqsstri ssdomg mp2 jctil sylibr entr mpancom
      bren2 ensym wf1o bren cuni wf csuc co f1of peano1 eldifn eleq2s fvex elsn
      ffvelcdm notbii neq0 bitr2i syl w3a cxp cpw elunii sylan2 difeq1i 3eqtr4i
      ffvelcdmda difabs pwuni ssdif sseli ralrimivw ralrimiva fmpo sylib adantl
      eqsstrri difexi eqeltri uniex axdc4 syl2anc exlimiv suceq fveq2d 3ad2ant3
      fveq2 imp 3adant1 3adant2 3ad2ant1 3simpb eximi ex mpcom velsn necon3bbii
      eleq2i eldif sylbbr sylan2br simpl wrex wfo f1ofo foelrn sylan id oveq12d
      ccnv eleq12d rspcv eqcom f1ocnvfv biimtrid eqcomd simpr eqidd ovmpo eleq1
      3adant3 3eltr3d mpbird fvmpt simp3 3eltr4d 3exp com3r 3expd rexlimiv mpid
      com4r impd impancom syl5 expd ralrimiv cmpt crn fvrn0 eqid fmpt mpbi rnex
      rgenw p0ex unex fex2 mp3an fveq1 eleq1d imbi2d ralbidv spcev exlimddv ) A
      OZPUDUEZEPUDUEZPEUDUEZCOZQUFZUXIGOZRZUXISZUGZCUXEUHZGUIZEUXEUDUEZUXFUXGUX
      FEUXEUJUEZEUXEUNUEZUKZULUXQUXFUXTUXRUXFUXSEPUNUEZUYAUXFUYAEUMSZUXEUMSZUXF
      UKZEUOUYBUXEQUPZUQZUMSZUYCEUYFUMLURUYGUXEUYEUSZUMSUXEUYHVFUYCUYGUYHUYFUYE
      USZUMUXEUYEUTUYGUYEUMSUYIUMSQVAUYFUYEVBVCVDUXEUYEVEUYHUXEVGVHVIUYCUXEPUNU
      EZUYDPVJSUYCUYJVKVRUXEVLVMUXEPVNVIVOVPUXSUXFUYAEUXEPVQVSVTUXEVJSEUXEVFUXR
      AWAZEUYFUXELUXEUYEWBWCEUXEVJWDWEWFEUXEWJWGEUXEPWHWIEPWKUXHPEFOZWLZFUIUXPP
      EFWMUYMUXPFUYMPEWNZHOZWOZUAOZWPZUYORZUYQUYQUYORZJWQZSZUAPUHZULZUXPHUBOZQU
      YLRZSZUBUIZUYMVUDHUIZUYMVUFESZVUHUYMPEUYLWOQPSVUJPEUYLWRZWSPEQUYLXDVHZVUJ
      VUFUYESZUKZVUHVUNVUFUYFEVUFUXEUYEWTLXAVUNVUFQTZUKVUHVUMVUOVUFQQUYLXBXCXEU
      BVUFXFXGWGXHVUGUYMVUIUGUBVUGUYMVUIVUGUYMULZUYPQUYORVUETZVUCXIZHUIZVUIVUPV
      UEUYNSZPUYNXJUYNXKZUYEUQZJWOZVUSUYMVUGVUJVUTVULVUEVUFEXLXMUYMVVCVUGUYMIOZ
      UYLRZVVBSZBUYNUHZIPUHVVCUYMVVGIPUYMVVDPSULVVEESZVVGUYMPEVVDUYLVUKXPVVHVVF
      BUYNEVVBVVEEEUYEUQZVVBUYFUYEUQUYFVVIEUXEUYEXQEUYFUYELXNLXOEVVAVFVVIVVBVFE
      XREVVAUYEXSVMYFXTYAXHYBIBPUYNVVEVVBJMYCYDYEUYNVUEHUAJEEUYFVJLUXEUYEUYKYGY
      HZYIYJYKVURVUDHUYPVUQVUCUUAUUBXHUUCYLUUDUYMVUDULZUXJUXIKRZUXISZUGZCUXEUHZ
      UXPVVKVVNCUXEVVKUXIUXESZUXJVVMVVPUXJULUXIESZVVKVVMUXJVVPUXIUYESZUKZVVQVVR
      UXIQCQUUEUUFVVQUXIUYFSVVPVVSULEUYFUXILUUGUXIUXEUYEUUHUUIUUJUYMVVQVUDVVMUY
      MVVQULZUYPVUCVVMVVTUYPUYMVUCVVMUGZUYMVVQUUKVVTUXIUCOZUYLRZTZUCPUULZUYPUYM
      VWAUGUGZUYMPEUYLUUMVVQVWEPEUYLUUNUCPEUXIUYLUUOUUPVWDVWFUCPVWDUYPUYMVWBPSZ
      VWAVWDUYPUYMVWGVWAUYPUYMVWGXIZVUCVWDVVMVWHVUCVWDVVMVWHVUCVWDXIZUXIUYLUUSZ
      RZWPZUYORZVWCVVLUXIVWIVWBWPZUYORZVWBVWBUYORZJWQZVWMVWCVWHVUCVWOVWQSZVWDVW
      HVUCVWRVWGUYPVUCVWRUGUYMVUBVWRUAVWBPUYQVWBTZUYSVWOVUAVWQVWSUYRVWNUYOUYQVW
      BYMYNVWSUYQVWBUYTVWPJVWSUUQUYQVWBUYOYPUURUUTUVAYOYQUVJVWIVWNVWLUYOVWIVWBV
      WKTZVWNVWLTVWHVWDVWTVUCVWHVWDULVWKVWBVWHVWDVWKVWBTZUYMVWGVWDVXAUGUYPVWDVW
      CUXITUYMVWGULVXAUXIVWCUVBPEVWBUXIUYLUVCUVDYRYQUVEYSVWBVWKYMXHYNVWHVUCVWQV
      WCTZVWDUYPVWGVXBUYMUYPVWGULVWGVWPUYNSVXBUYPVWGUVFPUYNVWBUYOXDIBVWBVWPPUYN
      VVEVWCJVWCVVDVWBUYLYPBOVWPTVWCUVGMVWBUYLXBUVHYKYSYTUVKVWIVVQVVLVWMTVWIVVQ
      VWCESZVWHVUCVXCVWDUYMVWGVXCUYPUYMPEVWBUYLVUKXPYRYTVWDVWHVVQVXCVKVUCUXIVWC
      EUVIYOUVLDUXIDOZVWJRZWPZUYORZVWMEKVXDUXITZVXFVWLUYOVXHVXEVWKTVXFVWLTVXDUX
      IVWJYPVXEVWKYMXHYNNVWLUYOXBUVMXHVWHVUCVWDUVNUVOUVPUVQUVRUWAUVSXHUVTUWBUWC
      UWDUWEUWFUXOVVOGKKDEVXGUWGZVJNEUYOUWHZUYEUSZVXIWOZEVJSVXKVJSVXIVJSVXGVXKS
      ZDEUHVXLVXMDEUYOVXFUWIUWNDEVXKVXGVXIVXIUWJUWKUWLVVJVXJUYEUYOHWAUWMUWOUWPE
      VXKVXIVJVJUWQUWRYHUXKKTZUXNVVNCUXEVXNUXMVVMUXJVXNUXLVVLUXIUXIUXKKUWSUWTUX
      AUXBUXCXHUXDYLVIVO $.
  $}

  ${
    $d f t u v w x y z $.
    $( Although CC can be proven trivially using ~ ac5 , we prove it here using
       DC. (New usage is discouraged.)  (Contributed by Mario Carneiro,
       2-Feb-2013.) $)
    axcc $p |- ( x ~~ _om ->
       E. f A. z e. x ( z =/= (/) -> ( f ` z ) e. z ) ) $=
      ( vy vw vv vu vt cv c0 csn cdif com cuni cfv cmpo ccnv csuc cmpt eqid
      axcclem ) ADBEAIJKLZFCGHHDMUBNHIFIZOPZEUBEIUCQORGIOSZUBTUDTUETUA $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  ZFC Set Theory - add the Axiom of Choice
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Introduce the Axiom of Choice
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z w v u t $.
    $( Axiom of Choice.  The Axiom of Choice (AC) is usually considered an
       extension of ZF set theory rather than a proper part of it.  It is
       sometimes considered philosophically controversial because it asserts
       the existence of a set without telling us what the set is.  ZF set
       theory that includes AC is called ZFC.

       The unpublished version given here says that given any set ` x ` , there
       exists a ` y ` that is a collection of unordered pairs, one pair for
       each nonempty member of ` x ` .  One entry in the pair is the member of
       ` x ` , and the other entry is some arbitrary member of that member of
       ` x ` .  See the rewritten version ~ ac3 for a more detailed
       explanation.  Theorem ~ ac2 shows an equivalent written compactly with
       restricted quantifiers.

       This version was specifically crafted to be short when expanded to
       primitives.  Kurt Maes' 5-quantifier version ~ ackm is slightly shorter
       when the biconditional of ~ ax-ac is expanded into implication and
       negation.  In ~ axac3 we allow the constant ` CHOICE ` to represent the
       Axiom of Choice; this simplifies the representation of theorems like
       ~ gchac (the Generalized Continuum Hypothesis implies the Axiom of
       Choice).

       Standard textbook versions of AC are derived as ~ ac8 , ~ ac5 , and
       ~ ac7 .  The Axiom of Regularity ~ ax-reg (among others) is used to
       derive our version from the standard ones; this reverse derivation is
       shown as Theorem ~ dfac2b .  Equivalents to AC are the well-ordering
       theorem ~ weth and Zorn's lemma ~ zorn .  See ~ ac4 for comments about
       stronger versions of AC.

       In order to avoid uses of ~ ax-reg for derivation of AC equivalents, we
       provide ~ ax-ac2 (due to Kurt Maes), which is equivalent to the standard
       AC of textbooks.  The derivation of ~ ax-ac2 from ~ ax-ac is shown by
       Theorem ~ axac2 , and the reverse derivation by ~ axac .  Therefore, new
       proofs should normally use ~ ax-ac2 instead.
       (New usage is discouraged.)  (Contributed by NM, 18-Jul-1996.) $)
    ax-ac $a |- E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. v A. u ( E. t
              ( ( u e. w /\ w e. t ) /\ ( u e. t /\ t e. y ) ) <-> u = v ) ) $.

    $( Axiom of Choice expressed with the fewest number of different variables.
       The penultimate step shows the logical equivalence to ~ ax-ac .
       (New usage is discouraged.)  (Contributed by NM, 14-Aug-2003.) $)
    zfac $p |- E. x A. y A. z ( ( y e. z /\ z e. w ) -> E. w A. y ( E. w
              ( ( y e. z /\ z e. w ) /\ ( y e. w /\ w e. x ) ) <-> y = w ) ) $=
      ( vu vt vv wel wa wex weq wal elequ2 elequ1 anbi12d cbvexvw bitrdi anbi1d
      wb wi ax-ac equequ2 bibi2d anbi2d bibi1i albidv exbidv imbi2i 2albii mpbi
      equequ1 bibi12d cbvalvw exbii ) BCHZCDHZIZECHZCFHZIZEFHZFAHZIZIZFJZEGKZSZ
      ELZGJZTZCLBLZAJUQUQBDHZDAHZIZIZDJZBDKZSZBLZDJZTZCLBLZAJDABCGEFUAVKWBAVJWA
      BCVIVTUQVHVSGDGDKZVHURUPIZEDHZVMIZIZDJZEDKZSZELVSWCVGWJEWCVGVEWISWJWCVFWI
      VEGDEUBUCVEWHWIVDWGFDFDKZUTWDVCWFWKUSUPURFDCMUDWKVAWEVBVMFDEMFDANOOPUEQUF
      WJVREBEBKZWHVPWIVQWLWGVODWLWDUQWFVNWLURUOUPEBCNRWLWEVLVMEBDNROUGEBDUKULUM
      QPUHUIUNUJ $.

    $( Axiom of Choice equivalent.  By using restricted quantifiers, we can
       express the Axiom of Choice with a single explicit conjunction.  (If you
       want to figure it out, the rewritten equivalent ~ ac3 is easier to
       understand.)  Note: ~ aceq0 shows the logical equivalence to ~ ax-ac .
       (New usage is discouraged.)  (Contributed by NM, 18-Jul-1996.) $)
    ac2 $p |- E. y A. z e. x A. w e. z E! v e. z E. u e. y
              ( z e. u /\ v e. u ) $=
      ( vt wel wa cv wrex wreu wral wex weq wb wal wi ax-ac aceq0 mpbir ) CFHEF
      HIFBJKECJZLDUBMCAJMBNCDHDAHIFDHDGHIFGHGBHIIGNFEOPFQENRDQCQBNABCDEFGSABCDE
      FGTUA $.
  $}

  ${
    $d x y z w v u $.
    $( Axiom of Choice using abbreviations.  The logical equivalence to ~ ax-ac
       can be established by chaining ~ aceq0 and ~ aceq2 .  A standard
       textbook version of AC is derived from this one in ~ dfac2a , and this
       version of AC is derived from the textbook version in ~ dfac2b , showing
       their logical equivalence (see ~ dfac2 ).

       The following sketch will help you understand this version of the axiom.
       Given any set ` x ` , the axiom says that there exists a ` y ` that is a
       collection of unordered pairs, one pair for each nonempty member of
       ` x ` .  One entry in the pair is the member of ` x ` , and the other
       entry is some arbitrary member of that member of ` x ` .  Using the
       Axiom of Regularity, we can show that ` y ` is really a set of _ordered_
       pairs, very similar to the ordered pair construction ~ opthreg .  The
       key theorem for this (used in the proof of ~ dfac2b ) is ~ preleq .
       With this modified definition of ordered pair, it can be seen that ` y `
       is actually a choice function on the members of ` x ` .

       For example, suppose ` x = { { 1 , 2 } , { 1 , 3 } , { 2 , 3 , 4 } } ` .
       Let us try ` y = { { { 1 , 2 } , 1 } , { { 1 , 3 } , 1 } , `
       ` { { 2 , 3 , 4 } , 2 } } ` .  For the member (of ` x ` )
       ` z = { 1 , 2 } ` , the only assignment to ` w ` and ` v ` that
       satisfies the axiom is ` w = 1 ` and ` v = { { 1 , 2 } , 1 } ` , so
       there is exactly one ` w ` as required.  We verify the other two members
       of ` x ` similarly.  Thus, ` y ` satisfies the axiom.  Using our
       modified ordered pair definition, we can say that ` y ` corresponds to
       the choice function ` { <. { 1 , 2 } , 1 >. , <. { 1 , 3 } , 1 >. , `
       ` <. { 2 , 3 , 4 } , 2 >. } ` .  Of course other choices for ` y ` will
       also satisfy the axiom, for example
       ` y = { { { 1 , 2 } , 2 } , { { 1 , 3 } , 1 } , `
       ` { { 2 , 3 , 4 } , 4 } } ` .  What AC tells us is that there exists at
       least one such ` y ` , but it doesn't tell us which one.

       (New usage is discouraged.)  (Contributed by NM, 19-Jul-1996.) $)
    ac3 $p |- E. y A. z e. x ( z =/= (/) -> E! w e. z E. v e. y
              ( z e. v /\ w e. v ) ) $=
      ( vu wel wa cv wrex wreu wral wex c0 wne wi ac2 aceq2 mpbi ) CFGEFGHFBIZJ
      ECIZKDUALCAIZLBMUANOCEGDEGHETJDUAKPCUBLBMABCDEFQABCDEFRS $.
  $}

  ${
    $d x y z v u $.
    $( In order to avoid uses of ~ ax-reg for derivation of AC equivalents, we
       provide ~ ax-ac2 , which is equivalent to the standard AC of textbooks.
       This appears to be the shortest known equivalent to the standard AC when
       expressed in terms of set theory primitives.  It was found by Kurt Maes
       as Theorem ~ ackm .  We removed the leading quantifier to make it
       slightly shorter, since we have ~ ax-gen available.  The derivation of
       ~ ax-ac2 from ~ ax-ac is shown by Theorem ~ axac2 , and the reverse
       derivation by ~ axac .  Note that we use ~ ax-reg to derive ~ ax-ac from
       ~ ax-ac2 , but not to derive ~ ax-ac2 from ~ ax-ac .  (Contributed by
       NM, 19-Dec-2016.) $)
    ax-ac2 $a |- E. y A. z E. v A. u (
       ( y e. x /\ ( z e. y -> ( ( v e. x /\ -. y = v ) /\ z e. v ) ) ) \/
           ( -. y e. x /\ ( z e. x -> ( ( v e. z /\ v e. y ) /\
               ( ( u e. z /\ u e. y ) -> u = v ) ) ) ) ) $.
  $}

  ${
    $d v w x y z $.
    $( This theorem asserts that the constant ` CHOICE ` is a theorem, thus
       eliminating it as a hypothesis while assuming ~ ax-ac2 as an axiom.
       (Contributed by Mario Carneiro, 6-May-2015.)  (Revised by NM,
       20-Dec-2016.)  (Proof modification is discouraged.) $)
    axac3 $p |- CHOICE $=
      ( vy vx vz vw vv wac wel weq wn wa wi wal wex ax-ac2 ax-gen dfackm mpbir
      wo ) FABGZCAGDBGADHIJCDGJKJSICBGDCGDAGJECGEAGJEDHKJKJRELDMCLAMZBLTBBACDEN
      OBACDEPQ $.
  $}

  ${
    $d x y z v u $.
    $( A remarkable equivalent to the Axiom of Choice that has only five
       quantifiers (when expanded to use only the primitive predicates ` = `
       and ` e. ` and in prenex normal form), discovered and proved by Kurt
       Maes.  This establishes a new record, reducing from 6 to 5 the largest
       number of quantified variables needed by any ZFC axiom.  The
       ZF-equivalence to AC is shown by Theorem ~ dfackm .  Maes found this
       version of AC in April 2004 (replacing a longer version, also with five
       quantifiers, that he found in November 2003).  See Kurt Maes, "A
       5-quantifier ( ` e. , = ` )-expression ZF-equivalent to the Axiom of
       Choice", ~ https://doi.org/10.48550/arXiv.0705.3162 .

       The original FOM posts are:
       ~ https://fomarchive.ugent.be/2003-November/007631.html
       ~ https://fomarchive.ugent.be/2003-November/007641.html .  (Contributed
       by NM, 29-Apr-2004.)  (Revised by Mario Carneiro, 17-May-2015.)
       (Proof modification is discouraged.) $)
    ackm $p |- A. x E. y A. z E. v A. u (
       ( y e. x /\ ( z e. y -> ( ( v e. x /\ -. y = v ) /\ z e. v ) ) ) \/
           ( -. y e. x /\ ( z e. x -> ( ( v e. z /\ v e. y ) /\
               ( ( u e. z /\ u e. y ) -> u = v ) ) ) ) ) $=
      ( wac cv wcel wceq wn wa wi wo wal wex axac3 dfackm mpbi ) FBGZAGZHZCGZSH
      DGZTHSUCIJKUBUCHKLKUAJUBTHUCUBHUCSHKEGZUBHUDSHKUDUCILKLKMENDOCNBOANPABCDE
      QR $.
  $}

  ${
    $d x y z v u $.
    $( Derive ~ ax-ac2 from ~ ax-ac .  (Contributed by NM, 19-Dec-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    axac2 $p |- E. y A. z E. v A. u (
       ( y e. x /\ ( z e. y -> ( ( v e. x /\ -. y = v ) /\ z e. v ) ) ) \/
           ( -. y e. x /\ ( z e. x -> ( ( v e. z /\ v e. y ) /\
               ( ( u e. z /\ u e. y ) -> u = v ) ) ) ) ) $=
      ( wel weq wn wa wi wo wal wex wac cv c0 wne wrex wreu wral dfac2a ac3 mpg
      dfackm mpbi spi ) BAFZCBFDAFBDGHICDFIJIUGHCAFDCFDBFIECFEBFIEDGJIJIKELDMCL
      BMZANUHALCOZPQCEFDEFIEBORDUISJCAOTBMNAABCDEUAABCDEUBUCABCDEUDUEUF $.
  $}

  ${
    $d x y z w v u t $.
    $( Derive ~ ax-ac from ~ ax-ac2 .  Note that ~ ax-reg is used by the proof.
       (Contributed by NM, 19-Dec-2016.)
       (Proof modification is discouraged.) $)
    axac $p |- E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. v A. u ( E. t
              ( ( u e. w /\ w e. t ) /\ ( u e. t /\ t e. y ) ) <-> u = v ) ) $=
      ( wel wa wex weq wb wal wi wac axac3 dfac0 mpbi spi ) CDHDAHIFDHDGHIFGHGB
      HIIGJFEKLFMEJNDMCMBJZAOTAMPABCDEFGQRS $.
  $}

  ${
    axaci.1 $e |- ( CHOICE <-> A. x ph ) $.
    $( Apply a choice equivalent.  (Contributed by Mario Carneiro,
       17-May-2015.) $)
    axaci $p |- ph $=
      ( wac wal axac3 mpbi spi ) ABDABEFCGH $.
  $}

  $( All sets are well-orderable under choice.  (Contributed by Mario Carneiro,
     28-Apr-2015.) $)
  cardeqv $p |- dom card = _V $=
    ( wac ccrd cdm cvv wceq axac3 dfac10 mpbi ) ABCDEFGH $.

  $( All sets are well-orderable under choice.  (Contributed by Stefan O'Rear,
     28-Feb-2015.) $)
  numth3 $p |- ( A e. V -> A e. dom card ) $=
    ( wcel cvv ccrd cdm elex cardeqv eleqtrrdi ) ABCADEFABGHI $.

  ${
    $d f x A $.
    numth.1 $e |- A e. _V $.
    $( Numeration theorem: any set is equinumerous to some ordinal (using AC).
       Theorem 10.3 of [TakeutiZaring] p. 84.  (Contributed by NM,
       20-Oct-2003.) $)
    numth2 $p |- E. x e. On x ~~ A $=
      ( ccrd cdm wcel cv cen wbr con0 wrex cvv numth3 ax-mp isnum2 mpbi ) BDEFZ
      AGBHIAJKBLFQCBLMNABOP $.

    $( Numeration theorem: every set can be put into one-to-one correspondence
       with some ordinal (using AC).  Theorem 10.3 of [TakeutiZaring] p. 84.
       (Contributed by NM, 10-Feb-1997.)  (Proof shortened by Mario Carneiro,
       8-Jan-2015.) $)
    numth $p |- E. x e. On E. f f : x -1-1-onto-> A $=
      ( cv cen wbr con0 wrex wf1o wex numth2 bren rexbii mpbi ) AEZBFGZAHIPBCEJ
      CKZAHIABDLQRAHPBCMNO $.
  $}

  ${
    $d x f $.
    $( An Axiom of Choice equivalent similar to the Axiom of Choice (first
       form) of [Enderton] p. 49.  (Contributed by NM, 29-Apr-2004.) $)
    ac7 $p |- E. f ( f C_ x /\ f Fn dom x ) $=
      ( cv wss cdm wfn wa wex df-ac axaci ) BCZACZDKLEFGBHAABIJ $.
  $}

  ${
    $d f x R $.
    $( An Axiom of Choice equivalent similar to the Axiom of Choice (first
       form) of [Enderton] p. 49.  (Contributed by NM, 23-Jul-2004.) $)
    ac7g $p |- ( R e. A -> E. f ( f C_ R /\ f Fn dom R ) ) $=
      ( vx cv wss cdm wfn wex wceq sseq2 dmeq fneq2d anbi12d exbidv ac7 vtoclg
      wa ) CEZDEZFZSTGZHZRZCISBFZSBGZHZRZCIDBATBJZUDUHCUIUAUEUCUGTBSKUIUBUFSTBL
      MNODCPQ $.
  $}

  ${
    $d x z f $.
    $( Equivalent of Axiom of Choice.  We do not insist that ` f ` be a
       function.  However, Theorem ~ ac5 , derived from this one, shows that
       this form of the axiom does imply that at least one such set ` f ` whose
       existence we assert is in fact a function.  Axiom of Choice of
       [TakeutiZaring] p. 83.

       Takeuti and Zaring call this "weak choice" in contrast to "strong
       choice" ` E. F A. z ( z =/= (/) -> ( F `` z ) e. z ) ` , which asserts
       the existence of a universal choice function but requires second-order
       quantification on (proper) class variable ` F ` and thus cannot be
       expressed in our first-order formalization.  However, it has been shown
       that ZF plus strong choice is a conservative extension of ZF plus weak
       choice.  See Ulrich Felgner, "Comparison of the axioms of local and
       universal choice", _Fundamenta Mathematica_, 71, 43-62 (1971).

       Weak choice can be strengthened in a different direction to choose from
       a collection of proper classes; see ~ ac6s5 .  (Contributed by NM,
       21-Jul-1996.) $)
    ac4 $p |- E. f A. z e. x ( z =/= (/) -> ( f ` z ) e. z ) $=
      ( cv c0 wne cfv wcel wi wral wex dfac3 axaci ) BDZEFNCDGNHIBADJCKAABCLM
      $.
  $}

  ${
    $d x y f A $.
    ac4c.1 $e |- A e. _V $.
    $( Equivalent of Axiom of Choice (class version).  (Contributed by NM,
       10-Feb-1997.) $)
    ac4c $p |- E. f A. x e. A ( x =/= (/) -> ( f ` x ) e. x ) $=
      ( vy cv c0 wne cfv wcel wi wral wex wceq raleq exbidv ac4 vtocl ) AFZGHSC
      FISJKZAEFZLZCMTABLZCMEBDUABNUBUCCTAUABOPEACQR $.
  $}

  ${
    $d f x y A $.
    ac5.1 $e |- A e. _V $.
    $( An Axiom of Choice equivalent: there exists a function ` f ` (called a
       choice function) with domain ` A ` that maps each nonempty member of the
       domain to an element of that member.  Axiom AC of [BellMachover] p. 488.
       Note that the assertion that ` f ` be a function is not necessary; see
       ~ ac4 .  (Contributed by NM, 29-Aug-1999.) $)
    ac5 $p |- E. f ( f Fn A /\ A. x e. A ( x =/= (/) -> ( f ` x ) e. x ) ) $=
      ( vy cv wfn c0 wne cfv wcel wi wral wex wceq fneq2 raleq anbi12d exbidv
      wa dfac4 axaci vtocl ) CFZEFZGZAFZHIUGUDJUGKLZAUEMZTZCNZUDBGZUHABMZTZCNEB
      DUEBOZUJUNCUOUFULUIUMUEBUDPUHAUEBQRSUKEEACUAUBUC $.
  $}

  ${
    $d x f A $.
    ac5b.1 $e |- A e. _V $.
    $( Equivalent of Axiom of Choice.  (Contributed by NM, 31-Aug-1999.) $)
    ac5b $p |- ( A. x e. A x =/= (/) ->
               E. f ( f : A --> U. A /\ A. x e. A ( f ` x ) e. x ) ) $=
      ( cv c0 wne wral cuni ccrd cdm wcel wn wf cfv wa wex cvv uniex numth3
      mp1i neirr neeq1 rspccv mtoi ac5num syl2anc ) AEZFGZABHZBIZJKLZFBLZMBUKCE
      ZNUHUNOUHLABHPCQUKRLULUJBDSUKRTUAUJUMFFGZFUBUIUOAFBUHFFUCUDUEABCUFUG $.
  $}

  ${
    $d f g x z A $.  $d f g x y z B $.  $d f g z ph $.  $d g y ps $.  $d g V $.
    ac6num.1 $e |- ( y = ( f ` x ) -> ( ph <-> ps ) ) $.
    $( A version of ~ ac6 which takes the choice as a hypothesis.  (Contributed
       by Mario Carneiro, 27-Aug-2015.) $)
    ac6num $p |- ( ( A e. V /\ U_ x e. A { y e. B | ph } e. dom card /\
      A. x e. A E. y e. B ph ) -> E. f ( f : A --> B /\ A. x e. A ps ) ) $=
      ( vg vz wcel wrex wral cv cfv wa c0 wceq cvv crab ciun ccrd cdm cmpt cuni
      w3a crn wf wex wn cab nfiu1 nfel1 wss ssiun2 ssexg expcom ralrimi dfiun2g
      syl5 syl eqid rnmpt unieqi eqtr4di id eqeltrrd 3ad2ant2 simp3 necom rabn0
      wne df-ne 3bitr3i ralbii ralnex bitri sylib wb 0ex elrnmpt sylnibr ac5num
      ax-mp syl2anc wfn ffn anim1i fveq2 eleq12d ralrnmptw anbi2d imbitrid wsbc
      simpl1 mptexd elrabi ralimi ad2antll fmpt nfcv elrabsf simprbi jca nfmpt1
      feq1 nfeq2 fvex sbcie fveq1 fvmpt2 mpan2 sylan9eq sbceq1d bitr3id ralbida
      anbi12d spcedv ex syld exlimdv mpd ) EHLZCEADFUAZUBZUCUDZLZADFMZCENZUGZCE
      YEUEZUHZYMUFZJOZUIZKOZYOPZYQLZKYMNZQZJUJZEFGOZUIZBCENZQZGUJZYKYNYGLZRYMLZ
      UKUUBYHYDUUHYJYHYFYNYGYHYFYQYESZCEMKULZUFZYNYHYETLZCENZYFUULSYHUUMCECYFYG
      CEYEUMUNCOZELZYEYFUOZYHUUMCEYEUPUUQYHUUMYEYFYGUQURVAUSZCKEYETUTVBYMUUKCKE
      YEYLYLVCZVDVEVFYHVGVHVIYKRYESZCEMZUUIYKYJUVAUKZYDYHYJVJYJUUTUKZCENUVBYIUV
      CCEYERVMRYEVMYIUVCYERVKADFVLRYEVNVOVPUUTCEVQVRVSRTLUUIUVAVTWACEYERYLTUUSW
      BWEWCKYMJWDWFYKUUAUUGJYKUUAYOYMWGZYEYOPZYELZCENZQZUUGUUAUVDYTQYKUVHYPUVDY
      TYMYNYOWHWIYKYTUVGUVDYKUUNYTUVGVTYHYDUUNYJUURVIYSUVFCKEYEYLTUUSUUJYRUVEYQ
      YEYQYEYOWJUUJVGWKWLVBWMWNYKUVHUUGYKUVHQZUUFEFCEUVEUEZUIZADUVEWOZCENZQGTUV
      JUVICEUVEHYDYHYJUVHWPWQUVIUVKUVMUVIUVEFLZCENZUVKUVGUVOYKUVDUVFUVNCEADUVEF
      WRWSWTCEFUVEUVJUVJVCZXAVSUVGUVMYKUVDUVFUVLCEUVFUVNUVLADUVEFDFXBXCXDWSWTXE
      UUCUVJSZUUDUVKUUEUVMEFUUCUVJXGUVQBUVLCECUUCUVJCEUVEXFXHBADUUOUUCPZWOUVQUU
      PQZUVLABDUVRUUOUUCXIIXJUVSADUVRUVEUVQUUPUVRUUOUVJPZUVEUUOUUCUVJXKUUPUVETL
      UVTUVESYEYOXICEUVETUVJUVPXLXMXNXOXPXQXRXSXTYAYBYC $.
  $}

  ${
    $d f x A $.  $d f x y B $.  $d f ph $.  $d y ps $.
    ac6.1 $e |- A e. _V $.
    ac6.2 $e |- B e. _V $.
    ac6.3 $e |- ( y = ( f ` x ) -> ( ph <-> ps ) ) $.
    $( Equivalent of Axiom of Choice.  This is useful for proving that there
       exists, for example, a sequence mapping natural numbers to members of a
       larger set ` B ` , where ` ph ` depends on ` x ` (the natural number)
       and ` y ` (to specify a member of ` B ` ).  A stronger version of this
       theorem, ~ ac6s , allows ` B ` to be a proper class.  (Contributed by
       NM, 18-Oct-1999.)  (Revised by Mario Carneiro, 27-Aug-2015.) $)
    ac6 $p |- ( A. x e. A E. y e. B ph ->
              E. f ( f : A --> B /\ A. x e. A ps ) ) $=
      ( cvv wcel crab ciun ccrd cdm wrex wral cv wss wf rgenw iunss mpbir ssexi
      wa wex ssrab2 numth3 ax-mp ac6num mp3an12 ) EKLCEADFMZNZOPLZADFQCEREFGSUA
      BCERUFGUGHUNKLUOUNFIUNFTUMFTZCERUPCEADFUHUBCEUMFUCUDUEUNKUIUJABCDEFGKJUKU
      L $.
  $}

  ${
    $d A f x y z $.  $d B f y z $.
    ac6c4.1 $e |- A e. _V $.
    ac6c4.2 $e |- B e. _V $.
    $( Equivalent of Axiom of Choice. ` B ` is a collection ` B ( x ) ` of
       nonempty sets.  (Contributed by Mario Carneiro, 22-Mar-2013.) $)
    ac6c4 $p |- ( A. x e. A B =/= (/) ->
               E. f ( f Fn A /\ A. x e. A ( f ` x ) e. B ) ) $=
      ( vy vz c0 wne wral cv wcel wrex cfv wa wex nfv cbvralw nfel2 csb ciun wf
      wfn nfcsb1v nfcv nfne weq csbeq1a neeq1d n0 nfre1 eleq2d rspce eliun rspe
      sylibr sylancom exlimd biimtrid ralimia sylbi iunex eleq1 ac6 ffn eleq12d
      ex fveq2 biimpri anim12i eximi 3syl ) CIJZABKZGLZAHLZCUAZMZGABCUBZNZHBKZB
      VTDLZUCZVQWCOZVRMZHBKZPZDQWCBUDZALZWCOZCMZABKZPZDQVOVRIJZHBKWBVNWOAHBVNHR
      AVRIAVQCUEZAIUFUGAHUHZCVRIAVQCUIZUJSWOWAHBWOVSGQVQBMZWAGVRUKWSVSWAGWSGRVS
      GVTULWSVSWAWSVSVPVTMZWAWSVSPVPCMZABNWTXAVSAVQBAVPVRWPTWQCVRVPWRUMUNAVPBCU
      OUQVSGVTUPURVHUSUTVAVBVSWFHGBVTDEABCEFVCVPWEVRVDVEWHWNDWDWIWGWMBVTWCVFWMW
      GWLWFAHBWLHRAWEVRWPTWQWKWECVRWJVQWCVIWRVGSVJVKVLVM $.

    $( Equivalent of Axiom of Choice. ` B ` is a collection ` B ( x ) ` of
       nonempty sets.  Remark after Theorem 10.46 of [TakeutiZaring] p. 98.
       (Contributed by Mario Carneiro, 22-Mar-2013.) $)
    ac6c5 $p |- ( A. x e. A B =/= (/) -> E. f A. x e. A ( f ` x ) e. B ) $=
      ( c0 wne wral cv wfn cfv wcel wa wex ac6c4 exsimpr syl ) CGHABIDJZBKZAJSL
      CMABIZNDOUADOABCDEFPTUADQR $.

    $d A f x $.  $d B f $.
    $( An Axiom of Choice equivalent: the infinite Cartesian product of
       nonempty classes is nonempty.  Axiom of Choice (second form) of
       [Enderton] p. 55 and its converse.  (Contributed by Mario Carneiro,
       22-Mar-2013.) $)
    ac9 $p |- ( A. x e. A B =/= (/) <-> X_ x e. A B =/= (/) ) $=
      ( vf c0 wne wral cixp cv wfn cfv wcel wa wex ac6c4 n0 vex elixp bitr2i
      exbii sylib ixpn0 impbii ) CGHABIZABCJZGHZUFFKZBLAKUIMCNABIOZFPZUHABCFDEQ
      UHUIUGNZFPUKFUGRULUJFABCUIFSTUBUAUCABCUDUE $.
  $}

  ${
    $d x f z A $.  $d x y f z B $.  $d f z ph $.  $d y z ps $.
    ac6s.1 $e |- A e. _V $.
    ac6s.2 $e |- ( y = ( f ` x ) -> ( ph <-> ps ) ) $.
    $( Equivalent of Axiom of Choice.  Using the Boundedness Axiom ~ bnd2 , we
       derive this strong version of ~ ac6 that doesn't require ` B ` to be a
       set.  (Contributed by NM, 4-Feb-2004.) $)
    ac6s $p |- ( A. x e. A E. y e. B ph ->
                E. f ( f : A --> B /\ A. x e. A ps ) ) $=
      ( vz wrex wral cv wss wa wex wf bnd2 vex ac6 anim2i fss expcom anim1d imp
      eximi eximdv exlimiv 3syl ) ADFKCELJMZFNZADUJKCELZOZJPUKEUJGMZQZBCELZOZGP
      ZOZJPEFUNQZUPOZGPZACDJEFHRUMUSJULURUKABCDEUJGHJSITUAUFUSVBJUKURVBUKUQVAGU
      KUOUTUPUOUKUTEUJFUNUBUCUDUGUEUHUI $.

    $( Equivalent of Axiom of Choice.  Contrapositive of ~ ac6s .  (Contributed
       by NM, 10-Jun-2007.) $)
    ac6n $p |- ( A. f ( f : A --> B -> E. x e. A ps ) ->
                E. x e. A A. y e. B ph ) $=
      ( cv wf wn wral wa wex wrex wi wal cfv bitri wceq notbid ac6s con3i albii
      dfrex2 imbi2i alinexa dfral2 rexbii rexnal 3imtr4i ) EFGJZKZBLZCEMZNGOZLZ
      ALZDFPZCEMZLZUNBCEPZQZGRZADFMZCEPZVAUQUSUOCDEFGHDJCJUMSUAABIUBUCUDVEUNUPL
      ZQZGRURVDVIGVCVHUNBCEUFUGUEUNUPGUHTVGUTLZCEPVBVFVJCEADFUIUJUTCEUKTUL $.

    $( Generalization of the Axiom of Choice to classes.  Slightly strengthened
       version of ~ ac6s3 .  (Contributed by NM, 29-Sep-2006.) $)
    ac6s2 $p |- ( A. x e. A E. y ph -> E. f ( f Fn A /\ A. x e. A ps ) ) $=
      ( wex wral cvv wrex cv wfn wa rexv ralbii wf ac6s ffn anim1i eximi sylbir
      syl ) ADIZCEJADKLZCEJZFMZENZBCEJZOZFIZUFUECEADPQUGEKUHRZUJOZFIULABCDEKFGH
      SUNUKFUMUIUJEKUHTUAUBUDUC $.

    $( Generalization of the Axiom of Choice to classes.  Theorem 10.46 of
       [TakeutiZaring] p. 97.  (Contributed by NM, 3-Nov-2004.) $)
    ac6s3 $p |- ( A. x e. A E. y ph -> E. f A. x e. A ps ) $=
      ( wex wral cv wfn wa ac6s2 exsimpr syl ) ADICEJFKELZBCEJZMFIRFIABCDEFGHNQ
      RFOP $.
  $}

  ${
    $d A f x z $.  $d B f x y z $.  $d f z ph $.  $d y z ps $.
    ac6sg.1 $e |- ( y = ( f ` x ) -> ( ph <-> ps ) ) $.
    $( ~ ac6s with sethood as antecedent.  (Contributed by FL, 3-Aug-2009.) $)
    ac6sg $p |- ( A e. V -> ( A. x e. A E. y e. B ph ->
                E. f ( f : A --> B /\ A. x e. A ps ) ) ) $=
      ( vz wrex cv wral wf wa wex wi wceq raleq feq2 anbi12d exbidv imbi12d vex
      ac6s vtoclg ) ADFKZCJLZMZUHFGLZNZBCUHMZOZGPZQUGCEMZEFUJNZBCEMZOZGPZQJEHUH
      ERZUIUOUNUSUGCUHESUTUMURGUTUKUPULUQUHEFUJTBCUHESUAUBUCABCDUHFGJUDIUEUF $.
  $}

  ${
    $d f x z A $.  $d x y f z B $.  $d f z ph $.  $d z ps $.
    ac6sf.1 $e |- F/ y ps $.
    ac6sf.2 $e |- A e. _V $.
    ac6sf.3 $e |- ( y = ( f ` x ) -> ( ph <-> ps ) ) $.
    $( Version of ~ ac6 with bound-variable hypothesis.  (Contributed by NM,
       2-Mar-2008.) $)
    ac6sf $p |- ( A. x e. A E. y e. B ph ->
                E. f ( f : A --> B /\ A. x e. A ps ) ) $=
      ( vz wrex wral wsb cv wf wa wex cbvrexsvw ralbii cfv sbhypf ac6s sylbi )
      ADFLZCEMADKNZKFLZCEMEFGOZPBCEMQGRUEUGCEADKFSTUFBCKEFGIABDKCOUHUAHJUBUCUD
      $.
  $}

  ${
    $d f x y A $.  $d f y B $.
    ac6s4.1 $e |- A e. _V $.
    $( Generalization of the Axiom of Choice to proper classes. ` B ` is a
       collection ` B ( x ) ` of nonempty, possible proper classes.
       (Contributed by NM, 29-Sep-2006.) $)
    ac6s4 $p |- ( A. x e. A B =/= (/) ->
               E. f ( f Fn A /\ A. x e. A ( f ` x ) e. B ) ) $=
      ( vy c0 wne wral cv wcel wex wfn cfv wa n0 ralbii eleq1 ac6s2 sylbi ) CGH
      ZABIFJZCKZFLZABIDJZBMAJUENZCKZABIODLUAUDABFCPQUCUGAFBDEUBUFCRST $.

    $( Generalization of the Axiom of Choice to proper classes. ` B ` is a
       collection ` B ( x ) ` of nonempty, possible proper classes.  Remark
       after Theorem 10.46 of [TakeutiZaring] p. 98.  (Contributed by NM,
       27-Mar-2006.) $)
    ac6s5 $p |- ( A. x e. A B =/= (/) -> E. f A. x e. A ( f ` x ) e. B ) $=
      ( c0 wne wral cv wfn cfv wcel wa wex ac6s4 exsimpr syl ) CFGABHDIZBJZAIRK
      CLABHZMDNTDNABCDEOSTDPQ $.
  $}

  ${
    $d x z y w v $.
    $( An Axiom of Choice equivalent.  Given a family ` x ` of mutually
       disjoint nonempty sets, there exists a set ` y ` containing exactly one
       member from each set in the family.  Theorem 6M(4) of [Enderton] p. 151.
       (Contributed by NM, 14-May-2004.) $)
    ac8 $p |- ( ( A. z e. x z =/= (/) /\
                   A. z e. x A. w e. x ( z =/= w -> ( z i^i w ) = (/) ) ) ->
               E. y A. z e. x E! v v e. ( z i^i y ) ) $=
      ( cv c0 wne wral cin wceq wi wa wcel weu wex dfac5 axaci ) CFZGHCAFZISDFZ
      HSUAJGKLDTICTIMEFSBFJNEOCTIBPLAABCDEQR $.
  $}

  ${
    $d f x A $.  $d f B $.
    ac9.1 $e |- A e. _V $.
    $( An Axiom of Choice equivalent: the infinite Cartesian product of
       nonempty classes is nonempty.  Axiom of Choice (second form) of
       [Enderton] p. 55 and its converse.  This is a stronger version of the
       axiom in Enderton, with no existence requirement for the family of
       classes ` B ( x ) ` (achieved via the Collection Principle ~ cp ).
       (Contributed by NM, 29-Sep-2006.) $)
    ac9s $p |- ( A. x e. A B =/= (/) <-> X_ x e. A B =/= (/) ) $=
      ( vf c0 wne wral cixp cv wfn cfv wcel wa wex ac6s4 n0 vex elixp exbii
      bitr2i sylib ixpn0 impbii ) CFGABHZABCIZFGZUEEJZBKAJUHLCMABHNZEOZUGABCEDP
      UGUHUFMZEOUJEUFQUKUIEABCUHERSTUAUBABCUCUD $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  AC equivalents:  well-ordering, Zorn's lemma
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y A $.
    $( Any set is strictly dominated by some ordinal.  (Contributed by NM,
       22-Oct-2003.) $)
    numthcor $p |- ( A e. V -> E. x e. On A ~< x ) $=
      ( vy cv csdm wbr con0 wrex wceq breq1 rexbidv cpw cen vpwex numth2 canth2
      vex ensym sdomentr sylancr reximi ax-mp vtoclg ) DEZAEZFGZAHIZBUFFGZAHIDB
      CUEBJUGUIAHUEBUFFKLUFUEMZNGZAHIUHAUJDOPUKUGAHUKUEUJFGUJUFNGUGUEDRQUFUJSUE
      UJUFTUAUBUCUD $.
  $}

  ${
    $d A x y $.
    $( Well-ordering theorem: any set ` A ` can be well-ordered.  This is an
       equivalent of the Axiom of Choice.  Theorem 6 of [Suppes] p. 242.  First
       proved by Ernst Zermelo (the "Z" in ZFC) in 1904.  (Contributed by Mario
       Carneiro, 5-Jan-2013.) $)
    weth $p |- ( A e. V -> E. x x We A ) $=
      ( vy cv wwe wex wceq weeq2 exbidv dfac8 axaci vtoclg ) DEZAEZFZAGZBOFZAGD
      BCNBHPRANBOIJQDDAKLM $.
  $}

  ${
    $d a b f g r s u v w x y z A $.  $d a b f u v y D $.
    $d a b f g r s u v x y z F $.  $d a b f g r s u v w x y z R $.  $d v C $.
    $( Generator function.  ` w ` is a well-ordering on ` A ` . $)
    zorn2lem.3 $e |- F =
      recs ( ( f e. _V |-> ( iota_ v e. C A. u e. C -. u w v ) ) ) $.
    $( Auxiliary sets. $)
    zorn2lem.4 $e |- C = { z e. A | A. g e. ran f g R z } $.
    zorn2lem.5 $e |- D = { z e. A | A. g e. ( F " x ) g R z } $.
    $( Lemma for ~ zorn2 .  (Contributed by NM, 3-Apr-1997.)  (Revised by Mario
       Carneiro, 9-May-2015.) $)
    zorn2lem1 $p |- ( ( x e. On /\ ( w We A /\ D =/= (/) ) ) ->
                   ( F ` x ) e. D ) $=
      ( cv con0 wcel wral cvv wwe c0 wne wa cfv wbr wn crio cres cmpt wceq tfr2
      adantr wfun wfn tfr1 fnfun ax-mp vex resfunexg mp2an crn crab cima df-ima
      rneq eqtr4di eleq2d imbi1d rabbidv 3eqtr4g riotaeqbidv eqid riotaex fvmpt
      ralbidv2 eqtrdi wreu wss simprl wor weso ad2antrl soex sylancl rabexd a1i
      ssrab3 simprr wereu syl13anc riotacl syl eqeltrd ) APZQRZFCPZUAZHUBUCZUDZ
      UDZWOLUEZEPZDPWQUFUGZEHSZDHUHZHXAXBLWOUIZJTXDEGSZDGUHZUJZUEZXFWPXBXKUKWTW
      OLXJMULUMXGTRZXKXFUKLUNZWOTRXLLQUOXMLXJMUPQLUQURAUSLWOTUTVAJXGXIXFTXJJPZX
      GUKZXHXEDGHXOKPZBPIUFZKXNVBZSZBFVCXQKLWOVDZSZBFVCGHXOXSYABFXOXQXQKXRXTXOX
      PXRRXPXTRXQXOXRXTXPXOXRXGVBXTXNXGVFLWOVEVGVHVIVPVJNOVKZXOXDXDEGHXOXCGRXCH
      RXDXOGHXCYBVHVIVPVLXJVMXEDHVNVOURVQXAXEDHVRZXFHRXAWRHTRHFVSZWSYCWPWRWSVTX
      AYABFHTOXAFWQWAZWQTRFTRWRYEWPWSFWQWBWCCUSFWQTWDWEWFYDXAYABFHOWHWGWPWRWSWI
      DEFHWQTWJWKXEDHWLWMWN $.

    $( Lemma for ~ zorn2 .  (Contributed by NM, 3-Apr-1997.)  (Revised by Mario
       Carneiro, 9-May-2015.) $)
    zorn2lem2 $p |- ( ( x e. On /\ ( w We A /\ D =/= (/) ) ) ->
                   ( y e. x -> ( F ` y ) R ( F ` x ) ) ) $=
      ( cv con0 wcel wbr wwe c0 wne cfv cima wral zorn2lem1 wceq ralbidv elrab2
      wa breq2 simprbi syl wi wfn wss cvv wn crio cmpt tfr1 onss fnfvima 3expia
      sylancr adantr breq1 rspccv sylsyld ) AQZRSZGDQZUAIUBUCUKZUKZLQZVKMUDZJTZ
      LMVKUEZUFZBQZVKSZWAMUDZVSSZWCVQJTZVOVQISZVTACDEFGHIJKLMNOPUGWFVQGSVTVPCQZ
      JTZLVSUFVTCVQGIWGVQUHWHVRLVSWGVQVPJULUIPUJUMUNVLWBWDUOZVNVLMRUPZVKRUQZWIM
      KURFQEQVMTUSFHUFEHUTVANVBVKVCWJWKWBWDRVKMWAVDVEVFVGVRWELWCVSVPWCVQJVHVIVJ
      $.

    $( Lemma for ~ zorn2 .  (Contributed by NM, 3-Apr-1997.)  (Revised by Mario
       Carneiro, 9-May-2015.) $)
    zorn2lem3 $p |- ( ( R Po A /\ ( x e. On /\ ( w We A /\ D =/= (/) ) ) ) ->
                   ( y e. x -> -. ( F ` x ) = ( F ` y ) ) ) $=
      ( cv wcel wa wbr wpo con0 wwe c0 wne cfv wceq wn wi zorn2lem2 adantl cima
      wral ssrab3 zorn2lem1 sselid breq1 biimprcd poirr nsyli com12 sylan2 syld
      ) GJUAZAQZUBRGDQUCIUDUESSZSBQZVERZVGMUFZVEMUFZJTZVJVIUGZUHZVFVHVKUIVDABCD
      EFGHIJKLMNOPUJUKVFVDVJGRZVKVMUIVFIGVJLQCQJTLMVEULUMCGIPUNACDEFGHIJKLMNOPU
      OUPVKVDVNSZVMVKVLVJVJJTZVOVLVPVKVJVIVJJUQURGVJJUSUTVAVBVC $.

    $( Lemma for ~ zorn2 .  (Contributed by NM, 3-Apr-1997.)  (Revised by Mario
       Carneiro, 9-May-2015.) $)
    zorn2lem4 $p |- ( ( R Po A /\ w We A ) -> E. x e. On D = (/) ) $=
      ( vy con0 cvv wcel wi wpo cv wwe wa c0 wceq wrex crn pm3.24 wne wal df-ne
      wn wral ralbii df-ral ralnex 3bitr3i wor weso adantr vex soex sylancl cfv
      wfn wb wbr crio cmpt tfr1 fvelrnb ax-mp nfa1 nfan ssrab3 zorn2lem1 sselid
      nfv cima eleq1 syl5ibcom exp32 com12 a2d imp rexlimd biimtrid ssrdv ssexd
      spsd adantl ccnv wfun zorn2lem3 exp45 com23 alrimdv alimdv r2al imbitrrdi
      ex imp4a cres wss ssid tz7.48lem mpan wrel cdm fnrel fndmi relssres mp2an
      eqimssi cnveqi funeqi sylib syl6 onprc funrnex df-rn eleq1i dfdm4 3imtr4g
      eqtr3i mtoi jcad biimtrrid mt3i ) FIUAZFCUBZUCZUDZHUEUFZAQUGZLUHZRSZYRUMZ
      UDZYRUIYPUMZAUBZQSZHUEUJZTZAUKZYNYTUUDAQUNYOUMZAQUNUUFUUAUUDUUGAQHUEULUOU
      UDAQUPYOAQUQURYNUUFYRYSYMUUFYRTYKYMUUFYRYMUUFUDZYQFRUUHFYLUSZYLRSFRSYMUUI
      UUFFYLUTVACVBFYLRVCVDUUHPYQFPUBZYQSZUUBLVEZUUJUFZAQUGZUUHUUJFSZLQVFZUUKUU
      NVGLJREUBDUBYLVHUMEGUNDGVIVJMVKZAQUUJLVLVMUUHUUMUUOAQYMUUFAYMAVSUUEAVNVOU
      UOAVSYMUUFUUCUUMUUOTZTZYMUUEUUSAYMUUCUUDUURUUCYMUUDUURTUUCYMUUDUURUUCYMUU
      DUDUDZUULFSUUMUUOUUTHFUULKUBBUBIVHKLUUBVTUNBFHOVPABCDEFGHIJKLMNOVQVRUULUU
      JFWAWBWCWDWEWKWFWGWHWIWJXBWLYNUUFLWMZWNZYSYNUUFUULUUJLVEUFUMZPUUBUNAQUNZU
      VBYNUUFUUCUUJUUBSZUDUVCTZPUKZAUKUVDYNUUEUVGAYNUUEUVFPYNUUEUUCUVEUVCYNUUCU
      UDUVEUVCTZYKYMUUCUUDUVHTZTYKUUCYMUVIYKUUCYMUUDUVHAPBCDEFGHIJKLMNOWOWPWQWF
      WEXCWRWSUVCAPQUUBWTXAUVDLQXDZWMZWNZUVBQQXEUVDUVLQXFAPQLUUQXGXHUVKUVAUVJLL
      XIZLXJZQXEUVJLUFUUPUVMUUQQLXKVMUVNQQLUUQXLZXOLQXMXNXPXQXRXSUVBYRQRSZXTUVB
      UVAXJZRSZUVAUHZRSZYRUVPUVRUVBUVTRUVAYAWDYQUVQRLYBYCQUVSRUVNQUVSUVOLYDYFYC
      YEYGXSYHYIYJ $.

    ${
      $d x u v f s r a b H $.
      $( Auxiliary set.  ` H ` is ` D ` with ` x ` substituted for ` y ` . $)
      zorn2lem.7 $e |- H = { z e. A | A. g e. ( F " y ) g R z } $.
      $( Lemma for ~ zorn2 .  (Contributed by NM, 4-Apr-1997.)  (Revised by
         Mario Carneiro, 9-May-2015.) $)
      zorn2lem5 $p |- ( ( ( w We A /\ x e. On ) /\ A. y e. x H =/= (/) ) ->
            ( F " x ) C_ A ) $=
        ( cv wcel vs wwe con0 wa c0 wne wral cima cfv wceq wrex wfun wfn cvv wn
        wbr crio cmpt tfr1 fnfun ax-mp fvelima mpan nfra1 nfan wi df-ral onelon
        nfv wal ssrab3 zorn2lem1 sselid eleq1 imbitrid sylani com12 exp43 com3r
        imp a2d spsd biimtrid rexlimd syl5 ssrdv ) GDSZUBZASZUCTZUDZNUEUFZBWIUG
        ZUDZUAMWIUHZGUASZWOTZBSZMUIZWPUJZBWIUKZWNWPGTZMULZWQXAMUCUMXCMKUNFSESWG
        UPUOFHUGEHUQUROUSUCMUTVABWPWIMVBVCWNWTXBBWIWKWMBWKBVIWLBWIVDVEXBBVIWKWM
        WRWITZWTXBVFZVFZWMXDWLVFZBVJWKXFWLBWIVGWKXGXFBWKXDWLXEWHWJXDWLXEVFZVFWJ
        XDWHXHWJXDWHWLXEWTWJXDUDZWHWLUDZUDXBXIWTWRUCTZXJXBWIWRVHXKXJUDZWSGTWTXB
        XLNGWSLSCSJUPLMWRUHUGCGNRVKBCDEFGHNJKLMOPRVLVMWSWPGVNVOVPVQVRVSVTWAWBWC
        VTWDWEWF $.

      $( Lemma for ~ zorn2 .  (Contributed by NM, 4-Apr-1997.)  (Revised by
         Mario Carneiro, 9-May-2015.) $)
      zorn2lem6 $p |- ( R Po A ->
   ( ( ( w We A /\ x e. On ) /\ A. y e. x H =/= (/) ) -> R Or ( F " x ) ) ) $=
        ( wa wi vs vr vb va wpo wwe con0 wcel wne wral cima wbr weq w3o wor wss
        cv c0 poss zorn2lem5 syl11 cfv wceq wex wfn wfun cvv wn crio cmpt fnfun
        tfr1 wrex fvelima df-rex sylib anim12d an4 2exbii exdistrv bitri sylibr
        ex mp2b neeq1i ralbii imaeq2 raleqdv rabbidv neeq1d rspccv sylbi onelon
        crab anim12dan word ordtri3or syl2an eqid zorn2lem2 adantll breq12 syl6
        eloni biimpcd com23 adantrrl imp fveq2 eqeq12 imbitrid adantl wb ancoms
        adantlr adantrrr 3orim123d syl5 exp31 com4r syl6c exp4a com3r a2d imp4b
        exlimdvv ralrimivv jca2 df-so imbitrrdi ) GJUEZGDUQZUFZAUQZUGUHZSZNURUI
        ZBYNUJZSZMYNUKZJUEZUAUQZUBUQZJULZUAUBUMZUUCUUBJULZUNZUBYTUJUAYTUJZSYTJU
        OYKYSUUAUUHYTGUPYKUUAYSYTGJUSABCDEFGHIJKLMNOPQRUTVAYSUUGUAUBYTYTUUBYTUH
        ZUUCYTUHZSZUCUQZYNUHZUDUQZYNUHZSZUULMVBZUUBVCZUUNMVBZUUCVCZSZSZUDVDUCVD
        ZYSUUGUUKUUMUURSZUCVDZUUOUUTSZUDVDZSZUVCMUGVEMVFZUUKUVHTMKVGFUQEUQYLULV
        HFHUJEHVIVJOVLUGMVKUVIUUIUVEUUJUVGUVIUUIUVEUVIUUISUURUCYNVMUVEUCUUBYNMV
        NUURUCYNVOVPWCUVIUUJUVGUVIUUJSUUTUDYNVMUVGUDUUCYNMVNUUTUDYNVOVPWCVQWDUV
        CUVDUVFSZUDVDUCVDUVHUVBUVJUCUDUUMUUOUURUUTVRVSUVDUVFUCUDVTWAWBYSUVBUUGU
        CUDYPYRUUPUVAUUGYRUUPLUQCUQJULZLMUULUKZUJZCGWNZURUIZUVKLMUUNUKZUJZCGWNZ
        URUIZSZTZYPUUPUVAUUGTZTYRUVKLMBUQZUKZUJZCGWNZURUIZBYNUJZUWAYQUWGBYNNUWF
        URRWEWFUWHUUMUVOUUOUVSUWGUVOBUULYNBUCUMZUWFUVNURUWIUWEUVMCGUWIUVKLUWDUV
        LUWCUULMWGWHWIWJWKUWGUVSBUUNYNBUDUMZUWFUVRURUWJUWEUVQCGUWJUVKLUWDUVPUWC
        UUNMWGWHWIWJWKVQWLYPUUPUVTUWBYMYOUUPUVTUWBTZTYOUUPYMUWKYOUUPYMUVTUWBYOU
        UPUULUGUHZUUNUGUHZSZUWNYMUVTSZUWBTYOUUPUWNYOUUMUWLUUOUWMYNUULWMYNUUNWMW
        OWCZUWPUWNUWOUVAUWNUUGUWNUWOUVAUWNUUGTUWNUULUUNUHZUCUDUMZUUNUULUHZUNZUW
        NUWOSZUVASZUUGUWLUULWPUUNWPUWTUWMUULXDUUNXDUULUUNWQWRUXBUWQUUDUWRUUEUWS
        UUFUXAUVAUWQUUDTZUWNYMUVSUVAUXCTUVOUWNYMUVSSZSZUWQUVAUUDUXEUWQUUQUUSJUL
        ZUVAUUDTUWMUXDUWQUXFTUWLUDUCCDEFGHUVRJKLMOPUVRWSWTXAUVAUXFUUDUUQUUBUUSU
        UCJXBXEXCXFXGXHUVAUWRUUETUXAUWRUUQUUSVCUVAUUEUULUUNMXIUUQUUBUUSUUCXJXKX
        LUXAUVAUWSUUFTZUWNYMUVOUVAUXGTUVSUWNYMUVOSZSZUWSUVAUUFUXIUWSUUSUUQJULZU
        VAUUFTUWLUXHUWSUXJTUWMUCUDCDEFGHUVNJKLMOPUVNWSWTXOUVAUXJUUFUUTUURUXJUUF
        XMUUSUUCUUQUUBJXBXNXEXCXFXPXHXQXRXSXTYAYBYCXHYDXRYEYFXRYGYHUAUBYTJYIYJ
        $.

      $( Lemma for ~ zorn2 .  (Contributed by NM, 6-Apr-1997.)  (Revised by
         Mario Carneiro, 9-May-2015.) $)
      zorn2lem7 $p |- ( ( A e. dom card /\ R Po A /\
      A. s ( ( s C_ A /\ R Or s ) -> E. a e. A A. r e. s ( r R a \/ r = a ) ) )
                  -> E. a e. A A. b e. A -. a R b ) $=
        ( ccrd cdm wcel wpo cv wss wor wa wbr weq wo wral wrex wal wwe wex ween
        wi wn c0 wceq con0 zorn2lem4 cima imaeq2 raleqdv rabbidv 3eqtr4g eqeq1d
        crab onminex df-ne ralbii anbi2i rexbii sylibr zorn2lem5 zorn2lem6 jcad
        wne a1i wfn wfun cvv crio cmpt tfr1 fnfun vex funimaex mp2b sseq1 soeq2
        anbi12d raleq rexbidv imbi12d spcv sylan9 adantld imp noel sseld 3anass
        w3a potr sylan2br expcomd breq1 biimprcd jaod exp42 sylan9r com24 com23
        adantl imp31 a2d ralimdv2 cbvralvw breq2 ralbidv elrab wb eleq2 bitr3id
        eqeq1i sylbi biimpd expdimp biimtrid exp32 com34 mtoi exp4a com4r impd
        ex pm2.43a com4l ralrimdv expd reximdvai com12 adantr imp32 exp45 imp4a
        mpd com3l rexlimiv 3syl adantlr pm2.43i expcom exlimiv 3impib ) GUCUDUE
        ZGJUFZOUGZGUHZUVBJUIZUJZPUGZQUGZJUKZPQULZUMZPUVBUNZQGUOZUTZOUPZUVGRUGZJ
        UKZVAZRGUNZQGUOZUUTGDUGZUQZDURUVAUVNUJZUVSUTZGDUSUWAUWCDUWBUWAUVSUWBUWA
        UJZUVSUVAUWAUWDUVSUTZUVNUVAUWAUJIVBVCZAVDUOZUWFNVBWBZBAUGZUNZUJZAVDUOZU
        WEACDEFGHIJKLMSTUAVEUWGUWFNVBVCZVAZBUWIUNZUJZAVDUOUWLUWFUWMABABULZINVBU
        WQLUGZCUGZJUKZLMUWIVFZUNZCGVLZUWTLMBUGZVFZUNZCGVLINUWQUXBUXFCGUWQUWTLUX
        AUXEUWIUXDMVGVHVIUAUBVJVKVMUWKUWPAVDUWJUWOUWFUWHUWNBUWINVBVNVOVPVQVRUWK
        UWEAVDUWDUWIVDUEZUWKUVSUWDUXGUWFUWJUVSUWBUWAUXGUWFUWJUVSUTZUTUWBUWFUWAU
        XGUJZUXHUWBUWFUXIUWJUVSUWBUWFUXIUWJUJZUJZUJUVJPUXAUNZQGUOZUVSUWBUXKUXMU
        WBUXJUXMUWFUVAUXJUXAGUHZUXAJUIZUJZUVNUXMUVAUXJUXNUXOUXJUXNUTUVAABCDEFGH
        IJKLMNSTUAUBVSZWCABCDEFGHIJKLMNSTUAUBVTWAUVMUXPUXMUTOUXAMVDWDMWEUXAWFUE
        MKWFFUGEUGUVTUKVAFHUNEHWGWHSWIVDMWJMUWIAWKWLWMUVBUXAVCZUVEUXPUVLUXMUXRU
        VCUXNUVDUXOUVBUXAGWNUVBUXAJWOWPUXRUVKUXLQGUVJPUVBUXAWQWRWSWTXAXBXCUWBUW
        FUXJUXMUVSUTZUVAUWFUXJUXSUTZUTUVNUWFUVAUXTUWFUVAUXJUXSUWFUVAUXJUJZUJZUX
        LUVRQGUYBUVGGUEZUXLUVRUYBUYCUXLUJUVQRGUYBUYCUXLUVOGUEZUVQUTUYDUYBUYCUXL
        UVQUYDUWFUYAUYCUXLUVQUTZUTZUWFUYDUYAUYFUTUWFUYDUYAUYDUYFUWFUYDUYAUYDUYF
        UTUTUWFUYDUJZUYAUYCUYDUYEUYGUYAUYCUYDUYEUYGUYAUYCUYDUJZUXLUVQUYGUYAUYHU
        JZUJUXLUJUVPUVOVBUEZUVOXDUYGUYIUXLUVPUYJUTUYGUYIUVPUXLUYJUYGUYIUVPUXLUY
        JUTUYIUVPUJZUXLUVFUVOJUKZPUXAUNZUYGUYJUYKUVJUYLPUXAUXAUYKUVFUXAUEZUVJUY
        LUYAUYHUVPUYNUVJUYLUTZUTZUYAUVPUYHUYPUYAUYNUYHUVPUYOUXJUYNUVFGUEZUVAUYH
        UVPUYOUTUTUXJUXAGUVFUXQXEUVAUYQUYHUVPUYOUVAUYQUYHUJZUJZUVPUJUVHUYLUVIUY
        SUVPUVHUYLUTUYSUVHUVPUYLUYRUVAUYQUYCUYDXGUVHUVPUJUYLUTUYQUYCUYDXFGUVFUV
        GUVOJXHXIXJXCUVPUVIUYLUTUYSUVIUYLUVPUVFUVGUVOJXKXLXRXMXNXOXPXQXSXTYAUYM
        UWRUVOJUKZLUXAUNZUYGUYJUYLUYTPLUXAUVFUWRUVOJXKYBUWFUYDVUAUYJUWFUYDVUAUJ
        ZUYJVUBUVOUXCUEZUWFUYJUXBVUACUVOGCRULUWTUYTLUXAUWSUVOUWRJYCYDYEUWFUXCVB
        VCVUCUYJYFIUXCVBUAYIUXCVBUVOYGYJYHYKYLYMXOYNYOXSYPXNYQYOYTYRUUAYSUUBYSU
        UCUUDUUEYNUUFUUGUUHUUKUUIXQYLUUJUULUUMUUNUUOUUPUUQUURYJUUS $.
    $}
  $}

  ${
    $d x y z w v u g h t s r q d k m n R $.
    $d x y z w v u g h t s r q d k m n A $.
    $( Zorn's Lemma of [Monk1] p. 117.  This version of ~ zorn2 avoids the
       Axiom of Choice by assuming that ` A ` is well-orderable.  (Contributed
       by NM, 6-Apr-1997.)  (Revised by Mario Carneiro, 9-May-2015.) $)
    zorn2g $p |- ( ( A e. dom card /\ R Po A /\
      A. w ( ( w C_ A /\ R Or w ) -> E. x e. A A. z e. w ( z R x \/ z = x ) ) )
                  -> E. x e. A A. y e. A -. x R y ) $=
      ( vr vq vm vk vv vd vs vh vg vn cv wbr wral crab vu vt crn cvv crio crecs
      wn cmpt cima wceq weq breq1 notbid cbvralvw breq2 ralbidv cbvriotavw rneq
      bitrid raleqdv rabbidv riotaeqbidv eqtrid cbvmptv ax-mp cbvrabv zorn2lem7
      recseq eqid ) UAUBGHIJEHQZKQZFRZHLQZUCZSZKETZMQZGQZFRZMNUDOQZPQZVJRZUGZOV
      LHNQZUCZSZKETZSZPWGUEZUHZUFZUAQUISGETZFLMWKVSMWKUBQUISGETZDCABWJLUDJQZIQZ
      VJRZUGZJVPSZIVPUEZUHZUJWKWTUFUJNLUDWIWSNLUKZWIWQJWGSZIWGUEWSWHXBPIWGWHWNW
      AVJRZUGZJWGSPIUKZXBWCXDOJWGOJUKWBXCVTWNWAVJULUMUNXEXDWQJWGXEXCWPWAWOWNVJU
      OUMUPUSUQXAXBWRIWGVPXAWFVOKEXAVLHWEVNWDVMURUTVAZXAWQJWGVPXFUTVBVCVDWJWTVH
      VEVOVSMVNSZKGEVOVQVKFRZMVNSKGUKZXGVLXHHMVNVJVQVKFULUNXIXHVSMVNVKVRVQFUOUP
      USVFWLVIWMVIVG $.

    $( Zorn's Lemma.  If the union of every chain (with respect to inclusion)
       in a set belongs to the set, then the set contains a maximal element.
       Theorem 6M of [Enderton] p. 151.  This version of ~ zorn avoids the
       Axiom of Choice by assuming that ` A ` is well-orderable.  (Contributed
       by NM, 12-Aug-2004.)  (Revised by Mario Carneiro, 9-May-2015.) $)
    zorng $p |- ( ( A e. dom card /\ A. z ( ( z C_ A /\ [C.] Or z ) ->
       U. z e. A ) ) -> E. x e. A A. y e. A -. x C. y ) $=
      ( vu wcel cv wss crpss wa wi wal wbr wn wral wrex wpss wceq wo sylib ccrd
      cdm wor cuni risset eqimss2 unissb vex brrpss orbi1i bitr4i ralbii sylibr
      sspss reximi sylbi imim2i alimi porpss zorn2g mp3an2 sylan2 notbii rexbii
      wpo ) DUAUBFZCGZDHVGIUCJZVGUDZDFZKZCLZJAGZBGZIMZNZBDOZADPZVMVNQZNZBDOZADP
      VLVFVHEGZVMIMZWBVMRZSZEVGOZADPZKZCLZVRVKWHCVJWGVHVJVMVIRZADPWGAVIDUEWJWFA
      DWJWBVMHZEVGOZWFWJVIVMHWLVIVMUFEVGVMUGTWEWKEVGWEWBVMQZWDSWKWCWMWDWBVMAUHU
      IUJWBVMUNUKULUMUOUPUQURVFDIVEWIVRDUSABECDIUTVAVBVQWAADVPVTBDVOVSVMVNBUHUI
      VCULVDT $.

    $( Variant of Zorn's lemma ~ zorng in which ` (/) ` , the union of the
       empty chain, is not required to be an element of ` A ` .  (Contributed
       by Jeff Madsen, 5-Jan-2011.)  (Revised by Mario Carneiro,
       9-May-2015.) $)
    zornn0g $p |- ( ( A e. dom card /\ A =/= (/) /\ A. z ( ( z C_ A /\
      z =/= (/) /\ [C.] Or z ) -> U. z e. A ) )
                                  -> E. x e. A A. y e. A -. x C. y ) $=
      ( vw wcel c0 wne cv wss crpss wor w3a cuni wi wral wrex wa ax-mp wceq cdm
      ccrd wal wpss wn csn cun simp2 simp1 snfi finnum unnum sylancl cdif uncom
      cfn sseq2i ssundif bitri difss soss wb ssdif0 uni0b biimpri eleq1d sylbir
      imbi2d difexi sseq1 neeq1 soeq2 3anbi123d unieq imbi12d com12 3expa an32s
      vex spcv unidif0 eleq1i elun1 sylbi syl6 0ex elun2 pm2.61ne sylan2 sylanb
      snid 2a1i alrimiv 3ad2ant3 zorng syl2anc ssun1 ssralv reximi rexun psseq1
      wo simpr 0pss bitrdi notbid ralbidv rexsn eqsn biimpar sylan2b rexeqtrrdv
      nne jaodan ) DUBUAZFZDGHZCIZDJZXRGHZXRKLZMZXRNZDFZOZCUCZMZXQAIZBIZUDZUEZB
      DGUFZUGZPZAYMQZYKBDPZADQZXPXQYFUHYGYMXOFZEIZYMJZYSKLZRZYSNZYMFZOZEUCZYOYG
      XPYLXOFZYRXPXQYFUIYLUPFUUGGUJYLUKSDYLULUMYFXPUUFXQYFUUEEUUBYFUUDYTYSYLUNZ
      DJZUUAYFUUDOZYTYSYLDUGZJUUIYMUUKYSDYLUOUQYSYLDURUSUUAUUIUUHKLZUUJUUHYSJUU
      AUULOYSYLUTUUHYSKVASUUIUULRZUUJYFGYMFZOUUHGUUHGTZUUDUUNYFUUOYSYLJZUUDUUNV
      BYSYLVCUUPUUCGYMUUCGTUUPYSVDVEVFVGVHUUMUUHGHZRYFUUHNZDFZUUDUUIUUQUULYFUUS
      OZUUIUUQUULUUTYFUUIUUQUULMZUUSYEUVAUUSOCUUHYSYLEVSVIXRUUHTZYBUVAYDUUSUVBX
      SUUIXTUUQYAUULXRUUHDVJXRUUHGVKXRUUHKVLVMUVBYCUURDXRUUHVNVFVOVTVPVQVRUUSUU
      CDFUUDUURUUCDYSWAWBUUCDYLWCWDWEUUNUUMYFGYLFUUNGWFWKGYLDWGSWLWHWIWJVPWMWNA
      BEYMWOWPYOXQYPAYMQZYQYNYPAYMDYMJYNYPODYLWQYKBDYMWRSWSUVCXQYQYPAYLQZXBYQYP
      ADYLWTXQYQYQUVDXQYQXCXQUVDRYPAYLDXQUVDXCUVDXQYIGTZBDPZDYLTZYPUVFAGWFYHGTZ
      YKUVEBDUVHYKYIGHZUEUVEUVHYJUVIUVHYJGYIUDUVIYHGYIXAYIXDXEXFYIGXMXEXGXHXQUV
      GUVFBDGXIXJXKXLXNXKWIWP $.
  $}

  ${
    $d w x y z A $.  $d w x y z R $.
    zornn0.1 $e |- A e. _V $.
    $( Zorn's Lemma of [Monk1] p. 117.  This theorem is equivalent to the Axiom
       of Choice and states that every partially ordered set ` A ` (with an
       ordering relation ` R ` ) in which every totally ordered subset has an
       upper bound, contains at least one maximal element.  The main proof
       consists of lemmas ~ zorn2lem1 through ~ zorn2lem7 ; this final piece
       mainly changes bound variables to eliminate the hypotheses of
       ~ zorn2lem7 .  (Contributed by NM, 6-Apr-1997.)  (Revised by Mario
       Carneiro, 9-May-2015.) $)
    zorn2 $p |- ( ( R Po A /\
      A. w ( ( w C_ A /\ R Or w ) -> E. x e. A A. z e. w ( z R x \/ z = x ) ) )
                  -> E. x e. A A. y e. A -. x R y ) $=
      ( ccrd cdm wcel wpo cv wss wor wa wbr weq wral wrex cvv wal numth3 zorn2g
      wo wi wn ax-mp mp3an1 ) EHIJZEFKDLZEMUJFNOCLALZFPCAQUDCUJRAESUEDUAUKBLFPU
      FBERAESETJUIGETUBUGABCDEFUCUH $.

    $( Zorn's Lemma.  If the union of every chain (with respect to inclusion)
       in a set belongs to the set, then the set contains a maximal element.
       This theorem is equivalent to the Axiom of Choice.  Theorem 6M of
       [Enderton] p. 151.  See ~ zorn2 for a version with general partial
       orderings.  (Contributed by NM, 12-Aug-2004.) $)
    zorn $p |- ( A. z ( ( z C_ A /\ [C.] Or z ) -> U. z e. A ) ->
                E. x e. A A. y e. A -. x C. y ) $=
      ( ccrd cdm wcel cv wss crpss wor wa cuni wi wal wpss wn wral cvv numth3
      wrex ax-mp zorng mpan ) DFGHZCIZDJUGKLMUGNDHOCPAIBIQRBDSADUBDTHUFEDTUAUCA
      BCDUDUE $.

    $( Variant of Zorn's lemma ~ zorn in which ` (/) ` , the union of the empty
       chain, is not required to be an element of ` A ` .  (Contributed by Jeff
       Madsen, 5-Jan-2011.) $)
    zornn0 $p |- ( ( A =/= (/) /\ A. z ( ( z C_ A /\ z =/= (/) /\
      [C.] Or z ) -> U. z e. A ) ) -> E. x e. A A. y e. A -. x C. y ) $=
      ( ccrd cdm wcel c0 wne cv wss crpss wor w3a cuni wi wal wpss cvv wn ax-mp
      wral wrex numth3 zornn0g mp3an1 ) DFGHZDIJCKZDLUIIJUIMNOUIPDHQCRAKBKSUABD
      UCADUDDTHUHEDTUEUBABCDUFUG $.
  $}

  ${
    $d a x y z C $.  $d x y D $.  $d a f u v w x y z G $.  $d a f u w y z ph $.
    $d a f u w x y z A $.  $d a f u w x y z B $.  $d x z F $.
    ttukeylem.1 $e |- ( ph ->
      F : ( card ` ( U. A \ B ) ) -1-1-onto-> ( U. A \ B ) ) $.
    ttukeylem.2 $e |- ( ph -> B e. A ) $.
    ttukeylem.3 $e |- ( ph -> A. x ( x e. A <-> ( ~P x i^i Fin ) C_ A ) ) $.
    $( Lemma for ~ ttukey .  Expand out the property of being an element of a
       property of finite character.  (Contributed by Mario Carneiro,
       15-May-2015.) $)
    ttukeylem1 $p |- ( ph -> ( C e. A <-> ( ~P C i^i Fin ) C_ A ) ) $=
      ( cvv wcel cpw cfn cin wss cdom cun ccrd ssexg wb wi elex a1i wa wbr cuni
      id cdif ssun1 undif1 sseqtrri cfv wfo fvex wf1o f1ofo focdmex mpsyl unexg
      syl2anc sylancr uniexb sylibr syl2anr infpwfidom reldom brrelex1i 3syl ex
      syl cv wal wceq eleq1 pweq ineq1d sseq1d bibi12d spcgv syl5com pm5.21ndd
      ) AEJKZECKZELZMNZCOZWCWBUAAECUBUCAWFWBAWFUDWEJKZEWEPUEWBWFWFCJKZWGAWFUGAC
      UFZJKZWHAWIWIDUHZDQZOWLJKZWJWIWIDQWLWIDUIWIDUJUKAWKJKZDCKWMWKRULZJKAWOWKF
      UMZWNWKRUNAWOWKFUOWPGWOWKFUPVJWOWKJFUQURHWKDJCUSUTWIWLJSVACVBVCWECJSVDEVE
      EWEPVFVGVHVIABVKZCKZWQLZMNZCOZTZBVLWBWCWFTZIXBXCBEJWQEVMZWRWCXAWFWQECVNXD
      WTWECXDWSWDMWQEVOVPVQVRVSVTWA $.

    $( Lemma for ~ ttukey .  A property of finite character is closed under
       subsets.  (Contributed by Mario Carneiro, 15-May-2015.) $)
    ttukeylem2 $p |- ( ( ph /\ ( C e. A /\ D C_ C ) ) -> D e. A ) $=
      ( wcel wss wa cpw cfn cin wi wb ttukeylem1 adantr simpr sspwd ssrin sstr2
      3syl 3imtr4d impancom impr ) AECKZFELZFCKZAUJUIUKAUJMZENZOPZCLZFNZOPZCLZU
      IUKULUPUMLUQUNLUOURQULFEAUJUAUBUPUMOUCUQUNCUDUEAUIUORUJABCDEGHIJSTAUKURRU
      JABCDFGHIJSTUFUGUH $.

    ttukeylem.4 $e |- G = recs ( ( z e. _V |-> if ( dom z = U. dom z ,
      if ( dom z = (/) , B , U. ran z ) , ( ( z ` U. dom z ) u.
      if ( ( ( z ` U. dom z ) u. { ( F ` U. dom z ) } ) e. A ,
        { ( F ` U. dom z ) } , (/) ) ) ) ) ) $.
    $( Lemma for ~ ttukey .  (Contributed by Mario Carneiro, 11-May-2015.) $)
    ttukeylem3 $p |- ( ( ph /\ C e. On ) -> ( G ` C ) = if ( C = U. C ,
      if ( C = (/) , B , U. ( G " C ) ) , ( ( G ` U. C ) u. if ( ( ( G ` U. C )
         u. { ( F ` U. C ) } ) e. A , { ( F ` U. C ) } , (/) ) ) ) ) $=
      ( con0 wcel cfv cvv wceq c0 cif cun wa cres cv cdm cuni crn csn cmpt cima
      tfr2 adantl eqidd simpr dmeqd wfn wss tfr1 ad2antlr fnssres sylancr fndmd
      eqtrd unieqd eqeq12d eqeq1d rneqd df-ima eqtr4di ifbieq2d fveq12d uneq12d
      onss fveq2d sneqd eleq1d ifbieq12d wn csuc onuni ad3antlr sucidg syl word
      eloni orduniorsuc orcanai eleqtrrd fvresd uneq1d ifbid ifeq2da wfun fnfun
      wo ax-mp resfunexg elexd funimaexg mpan uniexd ifcl syl2an fvex snex ifex
      0ex unex sylancl fvmptd ) AFMNZUAZFHOZHFUBZCPCUCZUDZXOUEZQZXORQZEXNUFZUEZ
      SZXPXNOZYBXPGOZUGZTZDNZYDRSZTZSZUHZOZFFUEZQZFRQZEHFUIZUEZSZYLHOZYRYLGOZUG
      ZTZDNZYTRSZTZSZXJXLYKQAFHYJLUJUKXKCXMYIUUEPYJPXKYJULXKXNXMQZUAZYIYMYQYLXM
      OZUUHYTTZDNZYTRSZTZSUUEUUGXQYMYAYHYQUULUUGXOFXPYLUUGXOXMUDFUUGXNXMXKUUFUM
      ZUNUUGFXMUUGHMUOZFMUPZXMFUOHYJLUQZXJUUOAUUFFVLURMFHUSUTVAVBZUUGXOFUUQVCZV
      DUUGXRYNXTYPEUUGXOFRUUQVEUUGXSYOUUGXSXMUFYOUUGXNXMUUMVFHFVGVHVCVIUUGYBUUH
      YGUUKUUGXPYLXNXMUUMUURVJZUUGYFUUJYDRYTRUUGYEUUIDUUGYBUUHYDYTUUSUUGYCYSUUG
      XPYLGUURVMVNZVKVOUUTUUGRULVPVKVPUUGYMUULUUDYQUUGYMVQZUAZUUHYRUUKUUCUVBYLF
      HUVBYLYLVRZFUVBYLMNZYLUVCNXJUVDAUUFUVAFVSVTYLMWAWBUUGYMFUVCQZUUGFWCZYMUVE
      WNXJUVFAUUFFWDURFWEWBWFWGWHZUVBUUJUUBYTRUVBUUIUUADUVBUUHYRYTUVGWIVOWJVKWK
      VBXKHWLZXJXMPNUUNUVHUUPMHWMWOZAXJUMHFMWPUTXKYQPNZUUDPNUUEPNAEPNYPPNUVJXJA
      EDJWQXJYOPUVHXJYOPNUVIHFMWRWSWTYNEYPPXAXBYRUUCYLHXCUUBYTRYSXDXFXEXGYMYQUU
      DPXAXHXIVB $.

    $( Lemma for ~ ttukey .  (Contributed by Mario Carneiro, 15-May-2015.) $)
    ttukeylem4 $p |- ( ph -> ( G ` (/) ) = B ) $=
      ( c0 cfv cuni wceq cima cif cun wcel iftruei con0 0elon ttukeylem3 eqcomi
      csn mpan2 uni0 eqid eqtri eqtrdi ) ALGMZLLNZOZLLOZEGLPNZQZULGMZUQULFMUEZR
      DSURLQRZQZEALUASUKUTOUBABCDELFGHIJKUCUFUTUPEUMUPUSULLUGUDTUNEUOLUHTUIUJ
      $.

    $( Lemma for ~ ttukey .  The ` G ` function forms a (transfinitely long)
       chain of inclusions.  (Contributed by Mario Carneiro, 15-May-2015.) $)
    ttukeylem5 $p |- ( ( ph /\ ( C e. On /\ D e. On /\ C C_ D ) ) ->
      ( G ` C ) C_ ( G ` D ) ) $=
      ( va con0 wcel wss cfv wi wceq vy wa cv sseq2 fveq2 sseq2d imbi12d imbi2d
      wral r19.21v wo wb onsseleq ad4ant23 cuni c0 cima cif csn cun wfn cvv cdm
      crn cmpt tfr1 simplr onss syl simprr fnfvima mp3an2i elssuni iffalse 3syl
      wn n0i sseqtrrd adantr simplrl csuc vuniex sucid word orduniorsuc orcanai
      eloni eleqtrrid mpd ssun1 sstrdi ifbothda ttukeylem3 ad4ant13 expr eqimss
      rspcdva a1i jaod sylbid ex expcom a2d biimtrid tfis3 expdcom 3imp2 ) AFOP
      ZGOPZFGQZFIRZGIRZQZXIAXHXJXMSZAXHUBZFUAUCZQZXKXPIRZQZSZSZXOFNUCZQZXKYBIRZ
      QZSZSZXOXNSUANGXPYBTZXTYFXOYHXQYCXSYEXPYBFUDYHXRYDXKXPYBIUEUFUGUHXPGTZXTX
      NXOYIXQXJXSXMXPGFUDYIXRXLXKXPGIUEUFUGUHYGNXPUIXOYFNXPUIZSXPOPZYAXOYFNXPUJ
      YKXOYJXTXOYKYJXTSXOYKUBZYJXTYLYJUBZXQFXPPZFXPTZUKZXSXHYKXQYPULAYJFXPUMUNY
      MYNXSYOYLYJYNXSYLYJYNUBZUBZXKXPXPUOZTZXPUPTZEIXPUQZUOZURZYSIRZUUEYSHRUSZU
      TDPUUFUPURZUTZURZXRYTXKUUDQZXKUUHQXKUUIQYRUUDUUHUUDUUIXKUDUUHUUIXKUDYRUUJ
      YTYRXKUUCUUDYRXKUUBPZXKUUCQIOVAYRXPOQZYNUUKICVBCUCZVCZUUNUOZTUUNUPTEUUMVD
      UOURUUOUUMRZUUPUUOHRUSZUTDPUUQUPURUTURVEMVFYRYKUULXOYKYQVGZXPVHVIYLYJYNVJ
      ZOXPIFVKVLXKUUBVMVIYRYNUUAVPUUDUUCTUUSXPFVQUUAEUUCVNVOVRVSYRYTVPZUBZXKUUE
      UUHUVAFYSQZXKUUEQZUVAYNUVBYRYNUUTUUSVSFXPVMVIUVAYFUVBUVCSNXPYSYBYSTZYCUVB
      YEUVCYBYSFUDUVDYDUUEXKYBYSIUEUFUGYLYJYNUUTVTUVAYSYSWAZXPYSUAWBWCYRYTXPUVE
      TZYRYKXPWDYTUVFUKUURXPWGXPWEVOWFWHWQWIUUEUUGWJWKWLAYKXRUUITXHYQABCDEXPHIJ
      KLMWMWNVRWOYOXSSYMYOXKXRTXSFXPIUEXKXRWPVIWRWSWTXAXBXCXDXEXFXG $.

    $( Lemma for ~ ttukey .  (Contributed by Mario Carneiro, 15-May-2015.) $)
    ttukeylem6 $p |- ( ( ph /\ C e. suc ( card ` ( U. A \ B ) ) ) ->
      ( G ` C ) e. A ) $=
      ( vu con0 wcel cfv wa wi wceq c0 vy va vw vf cuni cdif ccrd cardon onsuci
      vv csuc onelon sylan cv eleq1 fveq2 eleq1d imbi12d imbi2d wral r19.21v wb
      a1i word wss onordi ordelss sselda biimt syl ralbidva cima cif csn simprl
      cun onssi sselid ttukeylem3 syldan ad3antrrr wn cpw cfn cin wf wrex simpr
      wex elin2d ciun elin1d wfn wfun cvv cdm crn cmpt tfr1 fnfun funiunfv mp2b
      elpwid sseqtrrdi dfss3 eliun ralbii bitri sylib eleq2d ac6sfi syl2anc wne
      simp-4l simplrr ad2antrr simprrl adantr frn onss sstrd adantrr dffn4 fofi
      wfo ffn dm0rn0 eqeq1d bitr3id necon3bid biimpar sseldd rspcdva ttukeylem2
      fdmd ad2antrl expr ex ifclda uneq2 ordunifi syl3anc ffvelcdm vex ssonunii
      adantl simprr fnfvelrn elssuni ttukeylem5 syl13anc sseld anassrs ralimdva
      rnex expimpd impr sylibr syl12anc 0ss mpanr2 mpdan pm2.61ne exlimdv ssrdv
      mpd ttukeylem1 mpbird eqtr3id vuniex sucid eloni orduniorsuc 3syl orcanai
      un0 eleqtrrid ifbothda eqeltrd sylbird com23 a2i sylbi tfis3 impd mpcom
      wo ) FNOZAFDUEEUFZUGPZUKZOZQFHPZDOZAUWKNOZUWLUWHUWOAUWJUWIUHUIZVCUWKFULUM
      UWHAUWLUWNAUAUNZUWKOZUWQHPZDOZRZRZAUBUNZUWKOZUXCHPZDOZRZRZAUWLUWNRZRUAUBF
      UWQUXCSZUXAUXGAUXJUWRUXDUWTUXFUWQUXCUWKUOUXJUWSUXEDUWQUXCHUPUQURUSUWQFSZU
      XAUXIAUXKUWRUWLUWTUWNUWQFUWKUOUXKUWSUWMDUWQFHUPUQURUSUXHUBUWQUTZUXBRUWQNO
      ZUXLAUXGUBUWQUTZRUXBAUXGUBUWQVAAUXNUXAAUWRUXNUWTAUWRUXNUWTRAUWRQZUXNUXFUB
      UWQUTZUWTUXOUXFUXGUBUWQUXOUXCUWQOQUXDUXFUXGVBUXOUWQUWKUXCAUWKVDZUWRUWQUWK
      VEUXQAUWKUWPVFVCUWKUWQVGUMVHUXDUXFVIVJVKAUWRUXPUWTAUWRUXPQZQZUWSUWQUWQUEZ
      SZUWQTSZEHUWQVLUEZVMZUXTHPZUYEUXTGPVNZVPZDOZUYFTVMZVPZVMZDAUXRUXMUWSUYKSU
      XSUWKNUWQUWKUWPVQAUWRUXPVOVRZABCDEUWQGHIJKLVSVTUXSUYAUYDUYJDUXSUYAQZUYBEU
      YCDAEDOZUXRUYAUYBJWAUYMUYCDOZUYBWBUYMUYOUYCWCZWDWEZDVEZUYMUCUYQDUYMUCUNZU
      YQOZUYSDOZUYMUYTQZUYSUWQUDUNZWFZMUNZVUEVUCPZHPZOZMUYSUTZQZUDWIZVUAVUBUYSW
      DOZVUEUJUNZHPZOZUJUWQWGZMUYSUTZVUKVUBUYPWDUYSUYMUYTWHZWJZVUBUYSUJUWQVUNWK
      ZVEZVUQVUBUYSUYCVUTVUBUYSUYCVUBUYPWDUYSVURWLXCHNWMHWNVUTUYCSHCWOCUNZWPZVV
      CUEZSVVCTSEVVBWQUEVMVVDVVBPZVVEVVDGPVNZVPDOVVFTVMVPVMWRLWSNHWTUJUWQHXAXBX
      DVVAVUEVUTOZMUYSUTVUQMUYSVUTXEVVGVUPMUYSUJVUEUWQVUNXFXGXHXIVUOVUHMUJUYSUW
      QUDVUMVUFSVUNVUGVUEVUMVUFHUPXJXKXLVUBVUJVUAUDUYMUYTVUJVUAUYMUYTVUJQZQZVUA
      TDOZUYSTUYSTDUOVVIUYSTXMZQZAVUCWQZUEZHPZDOZUYSVVOVEZVUAAUXRUYAVVHVVKXNVVL
      UXFVVPUBUWQVVNUXCVVNSUXEVVODUXCVVNHUPUQUYMUXPVVHVVKAUWRUXPUYAXOXPVVLVVMUW
      QVVNVVLVUDVVMUWQVEZVVIVUDVVKUYMUYTVUDVUIXQZXRZUYSUWQVUCXSZVJZVVLVVMNVEZVV
      MWDOZVVMTXMZVVNVVMOVVLVVMUWQNVWBVVLUXMUWQNVEZUXSUXMUYAVVHVVKUYLWAUWQXTZVJ
      YAVVLVULUYSVVMVUCYEZVWDVVIVULVVKUYMUYTVULVUJVUSYBXRVVLVUCUYSWMZVWHVVLVUDV
      WIVVTUYSUWQVUCYFZVJUYSVUCYCXIUYSVVMVUCYDXLVVIVWEVVKVVIVVMTUYSTVVMTSVUCWPZ
      TSVVIUYSTSVUCYGVVIVWKUYSTVVIUYSUWQVUCVVSYOYHYIYJYKVVMUUAUUBYLYMVVLVUEVVOO
      ZMUYSUTZVVQVVIVWMVVKUYMUYTVUJVWMVUBVUDVUIVWMVUBVUDQVUHVWLMUYSVUBVUDVUEUYS
      OZVUHVWLRVUBVUDVWNQZQZVUGVVOVUEVWPAVUFNOVVNNOZVUFVVNVEZVUGVVOVEAUXRUYAUYT
      VWOXNVWPUWQNVUFVWPUXMVWFUXSUXMUYAUYTVWOUYLWAVWGVJZVWOVUFUWQOVUBUYSUWQVUEV
      UCUUCUUFYLVWPVWCVWQVWPVVMUWQNVUDVVRVUBVWNVWAYPVWSYAVVMVUCUDUUDUUOUUEVJVWP
      VUFVVMOZVWRVWPVWIVWNVWTVUDVWIVUBVWNVWJYPVUBVUDVWNUUGUYSVUEVUCUUHXLVUFVVMU
      UIVJABCDEVUFVVNGHIJKLUUJUUKUULUUMUUNUUPUUQXRMUYSVVOXEUURABDEVVOUYSGIJKYNU
      USAVVJUXRUYAVVHAUYNVVJJAUYNTEVEVVJEUUTABDEETGIJKYNUVAUVBWAUVCYQUVDUVFYRUV
      EAUYOUYRVBUXRUYAABDEUYCGIJKUVGXPUVHXRYSUYHUYHUYEDOZUYJDOUXSUYAWBZQZUYFTUY
      FUYISUYGUYJDUYFUYIUYEYTUQTUYISZUYEUYJDVXDUYEUYETVPUYJUYEUVPTUYIUYEYTUVIUQ
      VXCUYHWHVXCVXAUYHWBVXCUXFVXAUBUWQUXTUXCUXTSUXEUYEDUXCUXTHUPUQAUWRUXPVXBXO
      VXCUXTUXTUKZUWQUXTUAUVJUVKUXSUYAUWQVXESZUXSUXMUWQVDUYAVXFUWGUYLUWQUVLUWQU
      VMUVNUVOUVQYMXRUVRYSUVSYQUVTYRUWAUWBUWCVCUWDUWEUWF $.

    $( Lemma for ~ ttukey .  (Contributed by Mario Carneiro, 15-May-2015.) $)
    ttukeylem7 $p |- ( ph -> E. x e. A ( B C_ x /\ A. y e. A -. x C. y ) ) $=
      ( cfv wcel wss wn wa c0 con0 wceq cuni cdif ccrd wpss wral wrex csuc fvex
      va cv sucid ttukeylem6 mpan2 ttukeylem4 w3a cardon 0ss 3pm3.2i ttukeylem5
      0elon eqsstrrd wi simprr cun ssun1 undif1 sseqtrri ccnv simpl wf1o f1ocnv
      wf f1of 3syl adantr eldifi simprll elunii syl2anc eldifn eldifd ffvelcdmd
      ad2antll onelon sylancr onsuc syl a1i word onordi ordsucss mpsyl syl13anc
      csn ssun2 eloni ordunisuc fveq2d f1ocnvfv2 eqtr2d ordelss eqsstrd simprlr
      cif velsn sstrd eqeltrrd snssd unssd ttukeylem2 syl12anc iftrued eleqtrrd
      sylibr sselid cima ttukeylem3 syldan sucidg ordirr nelne1 neeqtrrd neneqd
      iffalsed eqtrd sseldd expr ssrdv sstrid eqssd npss ralrimiva sseq2 psseq1
      wne notbid ralbidv anbi12d rspcev ) AEUAZFUBZUCMZHMZENZFUUCOZUUCCUJZUDZPZ
      CEUEZFBUJZOZUUJUUFUDZPZCEUEZQZBEUFAUUBUUBUGNUUDUUBUUAUCUHUKABDEFUUBGHIJKL
      ULUMAFRHMZUUCABDEFGHIJKLUNARSNZUUBSNZRUUBOZUOUUPUUCOUUQUURUUSUTUUAUPZUUBU
      QURABDEFRUUBGHIJKLUSUMVAZAUUHCEAUUFENZQUUCUUFOZUUCUUFTZVBUUHAUVBUVCUVDAUV
      BUVCQZQZUUCUUFAUVBUVCVCUVFUUFUUFFUBZFVDZUUCUUFUUFFVDUVHUUFFVEUUFFVFVGUVFU
      VGFUUCUVFUIUVGUUCAUVEUIUJZUVGNZUVIUUCNAUVEUVJQZQZUVIGVHZMZUGZHMZUUCUVIUVL
      AUVOSNZUURUVOUUBOZUVPUUCOAUVKVIZUVLUVNSNZUVQUVLUURUVNUUBNZUVTUUTUVLUUAUUB
      UVIUVMAUUAUUBUVMVLZUVKAUUBUUAGVJZUUAUUBUVMVJUWBIUUBUUAGVKUUAUUBUVMVMVNVOU
      VLUVIYTFUVLUVIUUFNZUVBUVIYTNUVJUWDAUVEUVIUUFFVPWCZAUVBUVCUVJVQZUVIUUFEVRV
      SUVJUVIFNPAUVEUVIUUFFVTWCWAZWBZUUBUVNWDWEZUVNWFWGZUURUVLUUTWHZUUBWIZUVLUW
      AUVRUUBUUTWJZUWHUVNUUBWKWLABDEFUVOUUBGHIJKLUSWMUVLUVIUVOUAZHMZUWOUWNGMZWN
      ZVDZENZUWQRXDZVDZUVPUVLUWTUXAUVIUWTUWOWOUVLUVIUWQUWTUVLUVIUWPTUVIUWQNUVLU
      WPUVNGMZUVIUVLUWNUVNGUVLUVTUVNWIZUWNUVNTUWIUVNWPZUVNWQVNZWRUVLUWCUVIUUANU
      XBUVITAUWCUVKIVOUWGUUBUUAUVIGWSVSWTZUIUWPXEXNUVLUWSUWQRUVLAUVBUWRUUFOUWSU
      VSUWFUVLUWOUWQUUFUVLUWOUUCUUFUVLUWOUVNHMZUUCUVLUWNUVNHUXEWRUVLAUVTUURUVNU
      UBOZUXGUUCOUVSUWIUWKUVLUWLUWAUXHUWMUWHUUBUVNXAWEABDEFUVNUUBGHIJKLUSWMXBAU
      VBUVCUVJXCXFUVLUWPUUFUVLUVIUWPUUFUXFUWEXGXHXIABEFUUFUWRGIJKXJXKXLXMXOUVLU
      VPUVOUWNTZUVORTFHUVOXPUAXDZUXAXDZUXAAUVKUVQUVPUXKTUWJABDEFUVOGHIJKLXQXRUV
      LUXIUXJUXAUVLUVOUWNUVLUVOUVNUWNUVLUVNUVONZUVNUVNNPZUVOUVNYOUVLUWAUXLUWHUV
      NUUBXSWGUVLUVTUXCUXMUWIUXDUVNXTVNUVNUVOUVNYAVSUXEYBYCYDYEXMYFYGYHAUUEUVEU
      VAVOXIYIYJYGUUCUUFYKXNYLUUOUUEUUIQBUUCEUUJUUCTZUUKUUEUUNUUIUUJUUCFYMUXNUU
      MUUHCEUXNUULUUGUUJUUCUUFYNYPYQYRYSXK $.
  $}

  ${
    $d f w x y z A $.  $d f w x y z B $.
    $( The Teichm&uuml;ller-Tukey Lemma ~ ttukey with a slightly stronger
       conclusion: we can set up the maximal element of ` A ` so that it also
       contains some given ` B e. A ` as a subset.  (Contributed by Mario
       Carneiro, 15-May-2015.) $)
    ttukey2g $p |- ( ( U. A e. dom card /\ B e. A /\
      A. x ( x e. A <-> ( ~P x i^i Fin ) C_ A ) )
        -> E. x e. A ( B C_ x /\ A. y e. A -. x C. y ) ) $=
      ( vf vz vw cuni ccrd cdm wcel cv wss wa cfv cvv wceq c0 cif cun cpw wb wn
      cfn cin wal wpss wral wrex cdif difss ssnum mpan2 wf1o wex cen wbr isnum3
      wi bren bitri w3a crn csn cmpt crecs simp1 simp2 simp3 dmeq unieqd eqeq1d
      eqeq12d rneq ifbieq2d id fveq12d fveq2d uneq12d eleq1d ifbieq1d ifbieq12d
      sneqd cbvmptv recseq ax-mp ttukeylem7 3expib exlimiv sylbi syl 3impib ) C
      HZIJZKZDCKZALZCKWQUAUDUECMUBAUFZDWQMWQBLUGUCBCUHNACUIZWOWMDUJZWNKZWPWRNWS
      USZWOWTWMMXAWMDUKWMWTULUMXAWTIOZWTELZUNZEUOZXBXAXCWTUPUQXFWTURXCWTEUTVAXE
      XBEXEWPWRWSXEWPWRVBABFCDXDGPGLZJZXHHZQZXHRQZDXGVCZHZSZXIXGOZXOXIXDOZVDZTZ
      CKZXQRSZTZSZVEZVFZXEWPWRVGXEWPWRVHXEWPWRVIYCFPFLZJZYFHZQZYFRQZDYEVCZHZSZY
      GYEOZYMYGXDOZVDZTZCKZYORSZTZSZVEZQYDUUAVFQGFPYBYTXGYEQZXJYHXNYAYLYSUUBXHY
      FXIYGXGYEVJZUUBXHYFUUCVKZVMUUBXKYIXMYKDUUBXHYFRUUCVLUUBXLYJXGYEVNVKVOUUBX
      OYMXTYRUUBXIYGXGYEUUBVPUUDVQZUUBXSYQXQYORUUBXRYPCUUBXOYMXQYOUUEUUBXPYNUUB
      XIYGXDUUDVRWCZVSVTUUFWAVSWBWDYCUUAWEWFWGWHWIWJWKWL $.

    $( The Teichm&uuml;ller-Tukey Lemma ~ ttukey stated with the "choice" as an
       antecedent (the hypothesis ` U. A e. dom card ` says that ` U. A ` is
       well-orderable).  (Contributed by Mario Carneiro, 15-May-2015.) $)
    ttukeyg $p |- ( ( U. A e. dom card /\ A =/= (/) /\
      A. x ( x e. A <-> ( ~P x i^i Fin ) C_ A ) )
        -> E. x e. A A. y e. A -. x C. y ) $=
      ( vz cuni ccrd cdm wcel c0 wne cv cpw cfn cin wss wb wal wpss wn wrex wex
      wral wi n0 w3a wa ttukey2g simpr reximi syl 3exp exlimdv biimtrid 3imp )
      CEFGHZCIJZAKZCHUQLMNCOPAQZUQBKRSBCUBZACTZUPDKZCHZDUAUOURUTUCZDCUDUOVBVCDU
      OVBURUTUOVBURUEVAUQOZUSUFZACTUTABCVAUGVEUSACVDUSUHUIUJUKULUMUN $.
  $}

  ${
    $d x y A $.
    ttukey.1 $e |- A e. _V $.
    $( The Teichm&uuml;ller-Tukey Lemma, an Axiom of Choice equivalent.  If
       ` A ` is a nonempty collection of finite character, then ` A ` has a
       maximal element with respect to inclusion.  Here "finite character"
       means that ` x e. A ` iff every finite subset of ` x ` is in ` A ` .
       (Contributed by Mario Carneiro, 15-May-2015.) $)
    ttukey $p |- ( ( A =/= (/) /\ A. x ( x e. A <-> ( ~P x i^i Fin ) C_ A ) )
       -> E. x e. A A. y e. A -. x C. y ) $=
      ( cuni ccrd cdm wcel c0 wne cv cpw cfn cin wss wb wal wpss wn cvv ttukeyg
      wral wrex uniex numth3 ax-mp mp3an1 ) CEZFGHZCIJAKZCHUJLMNCOPAQUJBKRSBCUB
      ACUCUHTHUICDUDUHTUEUFABCUAUG $.
  $}

  ${
    $d F w y z $.  $d K w y z $.  $d g w y $.  $d s w y $.  $d w x y z $.
    axdclem.1 $e |- F = ( rec ( ( y e. _V |->
                            ( g ` { z | y x z } ) ) , s ) |` _om ) $.
    $( Lemma for ~ axdc .  (Contributed by Mario Carneiro, 25-Jan-2013.) $)
    axdclem $p |- ( ( A. y e. ~P dom x ( y =/= (/) -> ( g ` y ) e. y )
      /\ ran x C_ dom x /\ E. z ( F ` K ) x z ) ->
      ( K e. _om -> ( F ` K ) x ( F ` suc K ) ) ) $=
      ( vw cv c0 wne cfv wcel wss wbr cab wceq fvex nfcv wi cdm cpw crn wex w3a
      wral csuc neeq1 abn0 bitrdi eleq2 breq2 cbvabv eleq2i bitr4di elab breq2d
      com fveq2 bitrd imbi12d rspcv vex brelrn abssi sstr mpan dmex elpw2 syl11
      sylibr 3imp cvv breq1 abbidv fveq2d frsucmpt mpan2 syl5ibrcom ) BJZKLZWAD
      JZMZWANZUAZBAJZUBZUCZUGZWGUDZWHOZFEMZCJZWGPZCUEZUFWMFUHEMZWGPFUSNZWMWOCQZ
      WCMZWGPZWJWLWPXAWSWINZWJWPXAUAZWLWFXCBWSWIWAWSRZWBWPWEXAXDWBWSKLWPWAWSKUI
      WOCUJUKXDWEWMWDWGPZXAXDWEWDWMIJZWGPZIQZNZXEXDWEWDWSNXIWAWSWDULXHWSWDXGWOI
      CXFWNWMWGUMUNUOUPXGXEIWDWAWCSXFWDWMWGUMUQUKXDWDWTWMWGWAWSWCUTURVAVBVCWLWS
      WHOZXBWSWKOWLXJWOCWKWMWNWGFESCVDVEVFWSWKWHVGVHWSWHWGAVDVIVJVLVKVMWRWQWTWM
      WGWRWTVNNWQWTRWSWCSBGJZFWAWNWGPZCQZWCMWTEVNBXKTBFTBWTTHWAWMRZXMWSWCXNXLWO
      CWAWMWNWGVOVPVQVRVSURVT $.
  $}

  ${
    $d F f n $.  $d F k n y z $.  $d f g n x $.  $d g k n s y $.
    $d g k n x y z $.
    axdclem2.1 $e |- F = ( rec ( ( y e. _V |->
                             ( g ` { z | y x z } ) ) , s ) |` _om ) $.
    $( Lemma for ~ axdc .  Using the full Axiom of Choice, we can construct a
       choice function ` g ` on ` ~P dom x ` .  From this, we can build a
       sequence ` F ` starting at any value ` s e. dom x ` by repeatedly
       applying ` g ` to the set ` ( F `` x ) ` (where ` x ` is the value from
       the previous iteration).  (Contributed by Mario Carneiro,
       25-Jan-2013.) $)
    axdclem2 $p |- ( E. z s x z -> ( ran x C_ dom x ->
       E. f A. n e. _om ( f ` n ) x ( f ` suc n ) ) ) $=
      ( cv c0 cfv wcel wi wbr wex csuc com cvv wceq vk wne cdm cpw wral crn wss
      w3a wfn cab cmpt crdg cres frfnom fneq1i mpbir a1i omex fnexd fveq2 suceq
      fveq2d breq12d fveq1i fr0g elv eqtri breq1i biimpri eximi axdclem syl3an3
      peano1 mpi 3com23 wa fvex brelrn ssel syl5 imbitrdi ad2antll peano2 com3r
      eldm 3expia imp syld 3adantr2 ex finds2 com12 ralrimiv fveq1 ralbidv 3exp
      spcedv vex dmex pwex ac4c exlimiiv ) BJZKUBXCEJZLXCMNBAJZUCZUDZUEZHJZCJZX
      EOZCPZXEUFZXFUGZFJZDJZLZXOQZXPLZXEOZFRUEZDPZNNEXHXLXNYBXHXLXNUHZYAXOGLZXR
      GLZXEOZFRUEDSGYCRGSGRUIZYCYGBSXCXJXEOCUJXDLUKZXIULRUMZRUIXIYHUNRGYIIUOUPU
      QRSMYCURUQUSYCYFFRXORMYCYFYFKGLZKQZGLZXEOZUAJZGLZYNQZGLZXEOZYQYPQZGLZXEOZ
      YCFUAXOKTZYDYJYEYLXEXOKGUTUUBXRYKGXOKVAVBVCXOYNTZYDYOYEYQXEXOYNGUTUUCXRYP
      GXOYNVAVBVCXOYPTZYDYQYEYTXEXOYPGUTUUDXRYSGXOYPVAVBVCXHXNXLYMXLXHXNYJXJXEO
      ZCPZYMXKUUECUUEXKYJXIXJXEYJKYILZXIKGYIIVDUUGXITHXISYHVEVFVGVHVIVJXHXNUUFU
      HKRMYMVMABCEGKHIVKVNVLVOYNRMZYCYRUUANZUUHXHXNUUIXLUUHXHXNVPZVPYRYQXJXEOCP
      ZUUAXNYRUUKNUUHXHXNYRYQXFMZUUKYRYQXMMXNUULYOYQXEYNGVQYPGVQZVRXMXFYQVSVTCY
      QXEUUMWEWAWBUUHUUJUUKUUANUUJUUKUUHUUAXHXNUUKUUHUUANUUHYPRMXHXNUUKUHUUAYNW
      CABCEGYPHIVKVTWFWDWGWHWIWJWKWLWMXPGTZXTYFFRUUNXQYDXSYEXEXOXPGWNXRXPGWNVCW
      OWQWPBXGEXFXEAWRWSWTXAXB $.
  $}

  ${
    $d f n x y z v g u w $.
    $( This theorem derives ~ ax-dc using ~ ax-ac and ~ ax-inf .  Thus, _AC_
       implies _DC_, but not vice-versa (so that ZFC is strictly stronger than
       ZF+DC).  (New usage is discouraged.)  (Contributed by Mario Carneiro,
       25-Jan-2013.) $)
    axdc $p |- ( ( E. y E. z y x z /\ ran x C_ dom x ) ->
       E. f A. n e. _om ( f ` n ) x ( f ` suc n ) ) $=
      ( vv vg vu vw cv wbr wex crn cfv com cvv cab cmpt crdg wceq cdm csuc wral
      wss cres weq breq2 cbvabv breq1 abbidv eqtrid fveq2d cbvmptv rdgeq1 ax-mp
      wi reseq1i axdclem2 exlimiv imp ) BJZCJZAJZKCLZBLVCMVCUAUDZEJZDJZNVFUBVGN
      VCKEOUCDLZVDVEVHUPBAFCDGEHPHJZIJZVCKZIQZGJZNZRZVASZOUEBVPFPFJZVBVCKZCQZVM
      NZRZVASZOVOWATVPWBTHFPVNVTHFUFZVLVSVMWCVLVIVBVCKZCQVSVKWDICVJVBVIVCUGUHWC
      WDVRCVIVQVBVCUIUJUKULUMVAVOWAUNUOUQURUSUT $.
  $}

  $( An onto function implies dominance of domain over range.  Lemma 10.20 of
     [Kunen] p. 30.  This theorem uses the axiom of choice ~ ac7g .  The axiom
     of choice is not needed for finite sets, see ~ fodomfi .  See also
     ~ fodomnum .  (Contributed by NM, 23-Jul-2004.)  (Proof shortened by BJ,
     20-May-2024.) $)
  fodomg $p |- ( A e. V -> ( F : A -onto-> B -> B ~<_ A ) ) $=
    ( wcel ccrd cdm wfo cdom wbr wi numth3 fodomnum syl ) ADEAFGEABCHBAIJKADLAB
    CMN $.

  ${
    fodom.1 $e |- A e. _V $.
    $( An onto function implies dominance of domain over range.  (Contributed
       by NM, 23-Jul-2004.) $)
    fodom $p |- ( F : A -onto-> B -> B ~<_ A ) $=
      ( cvv wcel wfo cdom wbr wi fodomg ax-mp ) AEFABCGBAHIJDABCEKL $.
  $}

  ${
    $d x A $.
    $( The domain of a countable set is countable.  The proof uses ~ fodomnum
       rather than ~ fodomg , and so does not require ~ ax-ac .  (Contributed
       by Thierry Arnoux, 29-Dec-2016.)  (Revised by Vincent Gonzalez,
       24-Aug-2026.) $)
    dmct $p |- ( A ~<_ _om -> dom A ~<_ _om ) $=
      ( vx com cdom wbr cdm cvv cres dmresv ccrd wcel c1st cfv cmpt wfo syl2anc
      cv a1i mpisyl domtr wss con0 omelon ondomen resss ssnum crn wfn fvex eqid
      id fnmpti dffn4 mpbi wrel wceq wb relres reldm foeq3 mp2b fodomnum ssdomg
      mpbir ctex mpancom eqbrtrrid ) ACDEZAFAGHZFZCDAIVHVJVIDEZVICDEZVJCDEVHVIJ
      FZKZVIVJBVIBQZLMZNZOZVKVHAVMKZVIAUAZVNVHCUBKZVHVSWAVHUCRVHUKCAUDPVTVHAGUE
      ZRAVIUFPVRVIVQUGZVQOZVQVIUHWDBVIVPVQVOLUIVQUJULVIVQUMUNVIUOVJWCUPVRWDUQAG
      URBVIUSVJWCVIVQUTVAVDVIVJVQVBSVIADEZVHVLVHAGKVTWEAVEWBVIAGVCSVIACTVFVJVIC
      TPVG $.
      $( $j usage 'dmct' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d x A $.
    $( Obsolete version of ~ dmct as of 26-Aug-2026.  (Contributed by Thierry
       Arnoux, 29-Dec-2016.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dmctOLD $p |- ( A ~<_ _om -> dom A ~<_ _om ) $=
      ( vx com cdom wbr cdm cvv cres dmresv wcel cv c1st cfv cmpt wfo wss resss
      ctex mpisyl domtr ssexg sylancr crn fvex eqid fnmpti dffn4 mpbi wrel wceq
      wfn relres reldm foeq3 mp2b mpbir fodomg ssdomg mpancom syl2anc eqbrtrrid
      wb ) ACDEZAFAGHZFZCDAIVCVEVDDEZVDCDEZVECDEVCVDGJZVDVEBVDBKZLMZNZOZVFVCVDA
      PZAGJZVHAGQZARZVDAGUAUBVLVDVKUCZVKOZVKVDUKVRBVDVJVKVILUDVKUEUFVDVKUGUHVDU
      IVEVQUJVLVRVBAGULBVDUMVEVQVDVKUNUOUPVDVEVKGUQSVDADEZVCVGVCVNVMVSVPVOVDAGU
      RSVDACTUSVEVDCTUTVA $.
  $}

  $( The range of a countable set is countable.  (Contributed by Thierry
     Arnoux, 29-Dec-2016.) $)
  rnct $p |- ( A ~<_ _om -> ran A ~<_ _om ) $=
    ( com cdom wbr ccnv cdm crn cnvct dmct df-rn breq1i biimpri 3syl ) ABCDAEZB
    CDNFZBCDZAGZBCDZAHNIRPQOBCAJKLM $.

  ${
    $d f A $.  $d f B $.
    $( Equivalence of an onto mapping and dominance for a nonempty set.
       Proposition 10.35 of [TakeutiZaring] p. 93.  (Contributed by NM,
       29-Jul-2004.) $)
    fodomb $p |- ( ( A =/= (/) /\ E. f f : A -onto-> B ) <->
                 ( (/) ~< B /\ B ~<_ A ) ) $=
      ( c0 wne cv wfo wa csdm wbr cdom wceq eqeq1d wb cvv wcel mpcom 0sdomg syl
      adantl wex cdm fof fdmd crn dm0rn0 forn bitrid necon3bid biimpac vex dmex
      bitr3d eqeltrrdi focdmex mpbird ex fodomg exlimdv imp sdomdomtr brrelex2i
      jca2 reldom mpbid fodomr jca impbii ) ADEZABCFZGZCUAZHDBIJZBAKJZHZVIVLVOV
      IVKVOCVIVKVMVNVIVKVMVIVKHVMBDEZVKVIVPVKADBDVKVJUBZDLZADLBDLZVKVQADVKABVJA
      BVJUCUDZMVRVJUEZDLVKVSVJUFVKWABDABVJUGMUHUMUIUJVKVMVPNZVIVKBOPZWBAOPZVKWC
      VKAVQOVTVJCUKULUNZABOVJUOQBORSTUPUQWDVKVNWEABVJOURQVCUSUTVOVIVLVODAIJZVID
      BAVAVOWDWFVINVNWDVMBAKVDVBTAORSVEABCVFVGVH $.
  $}

  $( When assuming AC, weak and usual dominance coincide.  It is not known if
     this is an AC equivalent.  (Contributed by Stefan O'Rear, 11-Feb-2015.)
     (Revised by Mario Carneiro, 5-May-2015.) $)
  wdomac $p |- ( X ~<_* Y <-> X ~<_ Y ) $=
    ( cwdom wbr cvv wcel cdom relwdom brrelex2i reldom ccrd cdm numth3 wdomnumr
    wb syl pm5.21nii ) ABCDZBEFZABGDZABCHIABGJISBKLFRTOBEMABNPQ $.

  ${
    $d f x y A $.  $d f x y B $.
    brdom3.2 $e |- B e. _V $.
    $( Equivalence to a dominance relation.  (Contributed by NM,
       27-Mar-2007.) $)
    brdom3 $p |- ( A ~<_ B <-> E. f ( A. x E* y x f y /\
                 A. x e. A E. y e. B y f x ) ) $=
      ( cdom wbr cv wmo wal wrex wral wa wex c0 wceq cvv syl wss wfo wo wn csdm
      wi wne wcel wb reldom brrelex1i 0sdomg df-ne bitrdi biimpar fodomr ancoms
      syldan pm5.6 mpbi br0 nex exmo ax-gen rzal 0ex breq mobidv albidv rexbidv
      mtpor ralbidv anbi12d spcev sylancr wfun fofun wrel dffun6 simprbi wf jca
      dffo4 eximi jaoi cxp cin cdm wfn inss1 ssbri moimi relinxp mpbiran sylibr
      crn alimi funfnd rninxp biimpri anim12i df-fo inex1 dmex fodom inss2 dmss
      vex ax-mp dmxpss sstri ssdomg mp2 domtr mpan2 3syl exlimiv impbii ) CDGHZ
      AIZBIZEIZHZBJZAKZXTXSYAHZBDLZACMZNZEOZXRCPQZDCYAUAZEOZUBZYIXRYJUCZNYLUEXR
      YMUEXRYNPCUDHZYLXRYOYNXRYOCPUFZYNXRCRUGYOYPUHCDGUIUJCRUKSCPULUMUNYOXRYLDC
      EUOUPUQXRYJYLURUSYJYIYLYJXSXTPHZBJZAKZXTXSPHZBDLZACMZYIYRAYQBOYRYQBXSXTUT
      VAYQBVBVJVCUUAACVDYHYSUUBNEPVEYAPQZYDYSYGUUBUUCYCYRAUUCYBYQBXSXTYAPVFVGVH
      UUCYFUUAACUUCYEYTBDXTXSYAPVFVIVKVLVMVNYKYHEYKYDYGYKYAVOZYDDCYAVPUUDYAVQYD
      ABYAVRVSSYKDCYAVTYGBADCYAWBVSWAWCWDSYHXREYHYADCWEZWFZWGZCUUFUAZCUUGGHZXRY
      HUUFUUGWHZUUFWOCQZNUUHYDUUJYGUUKYDUUFYDXSXTUUFHZBJZAKZUUFVOZYCUUMAUULYBBU
      UFYAXSXTYAUUEWIWJWKWPUUOUUFVQUUNDCYAWLABUUFVRWMWNWQUUKYGBADCYAWRWSWTUUGCU
      UFXAWNUUGCUUFUUFYAUUEEXGXBXCXDUUIUUGDGHZXRDRUGUUGDTUUPFUUGUUEWGZDUUFUUETU
      UGUUQTYAUUEXEUUFUUEXFXHDCXIXJUUGDRXKXLCUUGDXMXNXOXPXQ $.

    $( An equivalence to a dominance relation.  (Contributed by NM,
       29-Mar-2007.) $)
    brdom5 $p |- ( A ~<_ B <->
  E. f ( A. x e. B E* y x f y /\ A. x e. A E. y e. B y f x ) ) $=
      ( cdom wbr cv wmo wral wrex wa wex wal cdm wcel wss sylibr cvv brdom3 cxp
      alral anim1i eximi sylbi cin wfo wfn crn wceq wrel wfun inss2 dmss dmxpss
      ax-mp sstri sseli inss1 ssbri moimi imim12i ralimi2 relinxp dffun7 funfnd
      jctil rninxp biimpri anim12i df-fo vex inex1 fodom ssdomg mp2 domtr mpan2
      dmex 3syl exlimiv impbii ) CDGHZAIZBIZEIZHZBJZADKZWFWEWGHBDLACKZMZENZWDWI
      AOZWKMZENWMABCDEFUAWOWLEWNWJWKWIADUCUDUEUFWLWDEWLWGDCUBZUGZPZCWQUHZCWRGHZ
      WDWLWQWRUIZWQUJCUKZMWSWJXAWKXBWJWQWJWQULZWEWFWQHZBJZAWRKZMWQUMWJXFXCWIXEA
      DWRWEWRQWEDQWIXEWRDWEWRWPPZDWQWPRWRXGRWGWPUNWQWPUOUQDCUPURZUSXDWHBWQWGWEW
      FWGWPUTVAVBVCVDDCWGVEVHABWQVFSVGXBWKBADCWGVIVJVKWRCWQVLSWRCWQWQWGWPEVMVNV
      TVOWTWRDGHZWDDTQWRDRXIFXHWRDTVPVQCWRDVRVSWAWBWC $.

    $( An equivalence to a dominance relation.  (Contributed by NM,
       28-Mar-2007.)  (Revised by NM, 16-Jun-2017.) $)
    brdom4 $p |- ( A ~<_ B <->
           E. f ( A. x e. B E* y e. A x f y /\ A. x e. A E. y e. B y f x ) ) $=
      ( cdom wbr cv wrmo wral wa wex wmo wal syl cdm crn wcel wss brdom3 anim1i
      wrex mormo alimi alral eximi sylbi cxp cin wfo wceq wrel wfun inss2 ax-mp
      wfn dmss dmxpss sstri sseli rnssi rnxpss inss1 ssbri anim12i moimi df-rmo
      3imtr4i imim12i ralimi2 relinxp jctil dffun9 sylibr funfnd rninxp biimpri
      df-fo vex inex1 dmex fodom cvv ssdomg mp2 domtr sylancl exlimiv impbii )
      CDGHZAIZBIZEIZHZBCJZADKZWMWLWNHBDUCACKZLZEMZWKWOBNZAOZWRLZEMWTABCDEFUAXCW
      SEXBWQWRXBWPAOWQXAWPAWOBCUDUEWPADUFPUBUGUHWSWKEWSCWNDCUIZUJZQZGHZXFDGHZWK
      WSXFCXEUKZXGWSXEXFUQZXERZCULZLXIWQXJWRXLWQXEWQXEUMZWLWMXEHZBXKJZAXFKZLXEU
      NWQXPXMWPXOADXFWLXFSWLDSWPXOXFDWLXFXDQZDXEXDTXFXQTWNXDUOZXEXDURUPDCUSUTZV
      AWMCSZWOLZBNWMXKSZXNLZBNWPXOYCYABYBXTXNWOXKCWMXKXDRCXEXDXRVBDCVCUTVAXEWNW
      LWMWNXDVDVEVFVGWOBCVHXNBXKVHVIVJVKDCWNVLVMABXEVNVOVPXLWRBADCWNVQVRVFXFCXE
      VSVOXFCXEXEWNXDEVTWAWBWCPDWDSXFDTXHFXSXFDWDWEWFCXFDWGWHWIWJ $.
  $}

  ${
    $d f g x y A v w z $.  $d f g x y B v w z $.
    brdom7disj.1 $e |- A e. _V $.
    brdom7disj.2 $e |- B e. _V $.
    brdom7disj.3 $e |- ( A i^i B ) = (/) $.
    $( An equivalence to a dominance relation for disjoint sets.  (Contributed
       by NM, 29-Mar-2007.)  (Revised by NM, 16-Jun-2017.) $)
    brdom7disj $p |- ( A ~<_ B <-> E. f ( A. x e. B E* y e. A { x , y } e. f
        /\ A. x e. A E. y e. B { y , x } e. f ) ) $=
      ( vv vz vw wbr cv wral wrex wa cpr wcel wceq cab cdom wrmo wex brdom4 cop
      vg weq wb wne cin incom eqtri disjne mp3an1 vex opthpr syl equcom anbi12i
      c0 bitr2di df-br a1i anbi12d rexbidva rexbidv rexcom zfpair2 eqeq1 anbi1d
      2rexbidv elab bitr4i adantr breq1 breq2 ceqsrex2v rmobidva ralbiia ancoms
      bitrd eqcom ancom 3bitr4g bicomi bitrid csn snex simpl ss2abi df-sn ssexi
      sseqtrri ab2rexex2 eleq2 rmobidv ralbidv spcev exlimiv copab preq1 eleq1d
      syl2anbr preq2 eqid brab rmobii ralbii rexbii df-opab vuniex prid1 elunii
      cvv cuni mpan adantl prid2 eqeltrri abexex eqeltri breq impbii bitri ) CD
      UALAMZBMZUFMZLZBCUBZADNZYFYEYGLZBDOZACNZPZUFUCZYEYFQZEMZRZBCUBZADNZYFYEQZ
      YQRZBDOZACNZPZEUCZABCDUFGUDYOUUFYNUUFUFYJYPIMZJMZKMZQZSZUUHUUIUEYGRZPZJDO
      KCOZITZRZBCUBZADNZUUAUUORZBDOZACNZUUFYMUUQYIADYEDRZUUPYHBCUVBYFCRZPUUPJAU
      GZKBUGZPZUUHUUIYGLZPZKCOZJDOZYHUVBUUPUVJUHUVCUVBUVJYPUUJSZUULPZKCOZJDOZUU
      PUVBUVIUVMJDUVBUVHUVLKCUVBUUICRZPZUVFUVKUVGUULUVPUVKAJUGZBKUGZPZUVFUVPYEU
      UIUIZUVKUVSUHDCUJZUTSZUVBUVOUVTUWACDUJUTDCUKHULZDCYEUUIUMUNYEYFUUHUUIAUOZ
      BUOZJUOZKUOZUPUQUVQUVDUVRUVEAJURBKURUSVAUVGUULUHUVPUUHUUIYGVBZVCVDVEVFUVN
      UVLJDOKCOZUUPUVLJKDCVGUUNUWIIYPABVHUUGYPSZUUMUVLKJCDUWJUUKUVKUULUUGYPUUJV
      IVJVKVLVMVAVNUVGYEUUIYGLYHJKYEYFDCUUHYEUUIYGVOUUIYFYEYGVPVQWAVRVSUUTYLACY
      ECRZUUSYKBDUWKYFDRZPUUSKAUGZJBUGZPZUVGPZJDOZKCOZYKUWKUUSUWRUHUWLUUSUUAUUJ
      SZUULPZJDOZKCOZUWKUWRUUNUXBIUUABAVHUUGUUASZUUMUWTKJCDUXCUUKUWSUULUUGUUAUU
      JVIVJVKVLUWKUXAUWQKCUWKUWTUWPJDUWKUUHDRZPZUWSUWOUULUVGUXEUUJUUASZUWNUWMPZ
      UWSUWOUXEUUHYEUIZUXFUXGUHUXDUWKUXHUWBUXDUWKUXHUWCDCUUHYEUMUNVTUUHUUIYFYEU
      WFUWGUWEUWDUPUQUUAUUJWBUWMUWNWCWDUULUVGUHUXEUVGUULUWHWEVCVDVEVFWFVNUVGUUH
      YEYGLYKKJYEYFCDUUIYEUUHYGVPUUHYFYEYGVOVQWAVEVSUUEUURUVAPEUUOUUMKJICDFGUUM
      ITZUUJWGZUUJWHUXIUUKITUXJUUMUUKIUUKUULWIWJIUUJWKWMWLWNYQUUOSZYTUURUUDUVAU
      XKYSUUQADUXKYRUUPBCYQUUOYPWOWPWQUXKUUCUUTACUXKUUBUUSBDYQUUOUUAWOVFWQVDWRX
      CWSUUEYOEYTYEYFUUIUUHQZYQRZKJWTZLZBCUBZADNZYFYEUXNLZBDOZACNZYOUUDUXPYSADU
      XOYRBCUXMYEUUHQZYQRYRKJYEYFUXNUWDUWEUWMUXLUYAYQUUIYEUUHXAXBUWNUYAYPYQUUHY
      FYEXDXBUXNXEZXFXGXHUXSUUCACUXRUUBBDUXMYFUUHQZYQRUUBKJYFYEUXNUWEUWDUVEUXLU
      YCYQUUIYFUUHXAXBUVDUYCUUAYQUUHYEYFXDXBUYBXFXIXHYNUXQUXTPUFUXNUXNUUGUUIUUH
      UEZSZUXMPZJUCZKUCITXNUXMKJIXJUYGKIYQXOZEXKZUYFUUIUYHRZJUXMUYJUYEUUIUXLRUX
      MUYJUUIUUHUWGXLUUIUXLYQXMXPXQWSUYFJIUYHUYIUXMUUHUYHRZUYEUUHUXLRUXMUYKUUIU
      UHUWFXRUUHUXLYQXMXPXQUYFITUYEITZUYDWGUYLXNIUYDWKUYDWHXSUYFUYEIUYEUXMWIWJW
      LXTXTYAYGUXNSZYJUXQYMUXTUYMYIUXPADUYMYHUXOBCYEYFYGUXNYBWPWQUYMYLUXSACUYMY
      KUXRBDYFYEYGUXNYBVFWQVDWRXCWSYCYD $.

    $( An equivalence to a dominance relation for disjoint sets.  (Contributed
       by NM, 5-Apr-2007.) $)
    brdom6disj $p |- ( A ~<_ B <-> E. f ( A. x e. B E* y
      { x , y } e. f /\ A. x e. A E. y e. B { y , x } e. f ) ) $=
      ( vv vz vw wbr cv wral wrex wa cpr wcel wceq cab cdom wmo wex cop zfpair2
      vg brdom5 eqeq1 anbi1d df-br anbi2i bitr4di 2rexbidv wi weq wne wb cin c0
      elab incom eqtri disjne mp3an1 vex opthpr breq12 biimprd biimtrdi impd ex
      syl adantrd rexlimdvv biimtrid moimdv ralimia ancoms eqcom 3bitr4g bicomi
      ancom anbi12d rexbidva rexbidv bitrid breq2 breq1 ceqsrex2v bitrd ralbiia
      a1i adantr biimpri snex simpl ss2abi df-sn sseqtrri ssexi ab2rexex2 eleq2
      csn mobidv ralbidv spcev syl2an exlimiv copab preq1 preq2 eqid brab mobii
      eleq1d ralbii rexbii cvv df-opab cuni vuniex prid1 elunii adantl eqeltrri
      mpan prid2 abexex eqeltri breq syl2anbr impbii bitri ) CDUALAMZBMZUFMZLZB
      UBZADNZYOYNYPLZBDOZACNZPZUFUCZYNYOQZEMZRZBUBZADNZYOYNQZUUFRZBDOZACNZPZEUC
      ZABCDUFGUGUUDUUOUUCUUOUFYSUUEIMZJMZKMZQZSZUUQUURUDYPRZPZJDOKCOZITZRZBUBZA
      DNZUUJUVDRZBDOZACNZUUOUUBYRUVFADYNDRZUVEYQBUVEUUEUUSSZUUQUURYPLZPZJDOKCOZ
      UVKYQUVCUVOIUUEABUEUUPUUESZUVBUVNKJCDUVPUVBUVLUVAPUVNUVPUUTUVLUVAUUPUUEUU
      SUHUIUVMUVAUVLUUQUURYPUJZUKULUMUTUVKUVNYQKJCDUVKUURCRZUVNYQUNZUUQDRZUVKUV
      RUVSUVKUVRPZUVLUVMYQUWAUVLAJUOBKUOPZUVMYQUNUWAYNUURUPZUVLUWBUQDCURZUSSZUV
      KUVRUWCUWDCDURUSDCVAHVBZDCYNUURVCVDYNYOUUQUURAVEZBVEZJVEZKVEZVFVLUWBYQUVM
      YNUUQYOUURYPVGVHVIVJVKVMVNVOVPVQUVJUUBUVIUUAACYNCRZUVHYTBDUWKYODRZPUVHKAU
      OZJBUOZPZUVMPZJDOZKCOZYTUWKUVHUWRUQUWLUVHUUJUUSSZUVAPZJDOZKCOZUWKUWRUVCUX
      BIUUJBAUEUUPUUJSZUVBUWTKJCDUXCUUTUWSUVAUUPUUJUUSUHUIUMUTUWKUXAUWQKCUWKUWT
      UWPJDUWKUVTPZUWSUWOUVAUVMUXDUUSUUJSZUWNUWMPZUWSUWOUXDUUQYNUPZUXEUXFUQUVTU
      WKUXGUWEUVTUWKUXGUWFDCUUQYNVCVDVRUUQUURYOYNUWIUWJUWHUWGVFVLUUJUUSVSUWMUWN
      WBVTUVAUVMUQUXDUVMUVAUVQWAWLWCWDWEWFWMUVMUUQYNYPLYTKJYNYOCDUURYNUUQYPWGUU
      QYOYNYPWHWIWJWDWKWNUUNUVGUVJPEUVDUVBKJICDFGUVBITZUUSXCZUUSWOUXHUUTITUXIUV
      BUUTIUUTUVAWPWQIUUSWRWSWTXAUUFUVDSZUUIUVGUUMUVJUXJUUHUVFADUXJUUGUVEBUUFUV
      DUUEXBXDXEUXJUULUVIACUXJUUKUVHBDUUFUVDUUJXBWEXEWCXFXGXHUUNUUDEUUIYNYOUURU
      UQQZUUFRZKJXIZLZBUBZADNZYOYNUXMLZBDOZACNZUUDUUMUXOUUHADUXNUUGBUXLYNUUQQZU
      UFRUUGKJYNYOUXMUWGUWHUWMUXKUXTUUFUURYNUUQXJXOUWNUXTUUEUUFUUQYOYNXKXOUXMXL
      ZXMXNXPUXRUULACUXQUUKBDUXLYOUUQQZUUFRUUKKJYOYNUXMUWHUWGKBUOUXKUYBUUFUURYO
      UUQXJXOJAUOUYBUUJUUFUUQYNYOXKXOUYAXMXQXPUUCUXPUXSPUFUXMUXMUUPUURUUQUDZSZU
      XLPZJUCZKUCITXRUXLKJIXSUYFKIUUFXTZEYAZUYEUURUYGRZJUXLUYIUYDUURUXKRUXLUYIU
      URUUQUWJYBUURUXKUUFYCYFYDXHUYEJIUYGUYHUXLUUQUYGRZUYDUUQUXKRUXLUYJUURUUQUW
      IYGUUQUXKUUFYCYFYDUYEITUYDITZUYCXCUYKXRIUYCWRUYCWOYEUYEUYDIUYDUXLWPWQWTYH
      YHYIYPUXMSZYSUXPUUBUXSUYLYRUXOADUYLYQUXNBYNYOYPUXMYJXDXEUYLUUAUXRACUYLYTU
      XQBDYOYNYPUXMYJWEXEWCXFYKXHYLYM $.
  $}

  $( Once we allow AC, the "strongest" definition of finite set becomes
     equivalent to the "weakest" and the entire hierarchy collapses.
     (Contributed by Stefan O'Rear, 29-Oct-2014.) $)
  fin71ac $p |- Fin7 = Fin $=
    ( wac cfin7 cfn wceq axac3 dfacfin7 mpbi ) ABCDEFG $.

  $( An image of a function under a set is dominated by the set.  Proposition
     10.34 of [TakeutiZaring] p. 92.  (Contributed by NM, 23-Jul-2004.) $)
  imadomg $p |- ( A e. B -> ( Fun F -> ( F " A ) ~<_ A ) ) $=
    ( wcel wfun cima cres cdm cdom wbr wa crn df-ima cvv resfunexg dmexd funres
    wfo funforn expcom sylib adantr fodomg eqbrtrid wss cin dmres inss1 eqsstri
    sylc ssdomg mpi domtr sylan2 syld ) ABDZCEZCAFZCAGZHZIJZURAIJZUQUPVAUQUPKZU
    RUSLZUTICAMVCUTNDUTVDUSRZVDUTIJVCUSNCABOPUQVEUPUQUSEVEACQUSSUAUBUTVDUSNUCUJ
    UDTVAUPVBUPVAUTAIJZVBUPUTAUEVFUTACHZUFACAUGAVGUHUIUTABUKULURUTAUMUNTUO $.

  $( A version of ~ imadomg that does not require the axiom of choice ~ ax-ac .
     (Contributed by Vincent Gonzalez, 25-Aug-2026.) $)
  imadomnum $p |- ( A e. dom card -> ( Fun F -> ( F " A ) ~<_ A ) ) $=
    ( ccrd cdm wcel wfun cima cdom wbr cin cres crn df-ima wfn wss inss1 adantr
    wa sylib cvv ssnum mpan2 funres funfn dmres fneq2i adantl fodomnum biimtrid
    wfo dffn4 sylc eqbrtrid wi elex ssdomg syl mpi domtr syl2anc ex ) ACDZEZBFZ
    BAGZAHIZVCVDRZVEABDZJZHIVIAHIZVFVGVEBAKZLZVIHBAMVGVIVBEZVKVINZVLVIHIZVCVMVD
    VCVIAOZVMAVHPZAVIUAUBQVDVNVCVDVKVKDZNZVNVDVKFVSABUCVKUDSVRVIVKBAUEUFSUGVNVI
    VLVKUJVMVOVIVKUKVIVLVKUHUIULUMVCVJVDVCVPVJVQVCATEVPVJUNAVBUOVIATUPUQURQVEVI
    AUSUTVA $.
    $( $j usage 'imadomnum' avoids 'ax-ac' 'ax-ac2'; $)

  $( The image by a function of a countable set is countable.  The proof uses
     ~ imadomnum rather than ~ imadomg , and so does not require ~ ax-ac .
     (Contributed by Thierry Arnoux, 27-Mar-2018.)  (Revised by Vincent
     Gonzalez, 25-Aug-2026.) $)
  fimact $p |- ( ( A ~<_ _om /\ Fun F ) -> ( F " A ) ~<_ _om ) $=
    ( com cdom wbr wfun wa cima ccrd cdm wcel con0 omelon simpl ondomen syl2anc
    a1i simpr imadomnum sylc domtr ) ACDEZBFZGZBAHZADEZUBUECDEUDAIJKZUCUFUDCLKZ
    UBUGUHUDMQUBUCNZCAOPUBUCRABSTUIUEACUAP $.
    $( $j usage 'fimact' avoids 'ax-ac' 'ax-ac2'; $)

  $( Obsolete version of ~ fimact as of 26-Aug-2026.  (Contributed by Thierry
     Arnoux, 27-Mar-2018.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  fimactOLD $p |- ( ( A ~<_ _om /\ Fun F ) -> ( F " A ) ~<_ _om ) $=
    ( com cdom wbr wfun wa cima cvv wcel ctex imadomg sylan simpl domtr syl2anc
    imp ) ACDEZBFZGBAHZADEZRTCDERAIJZSUAAKUBSUAAIBLQMRSNTACOP $.

  $( A version of ~ fnrndomg that does not require the axiom of choice
     ~ ax-ac .  (Contributed by Vincent Gonzalez, 17-Aug-2026.) $)
  fnrndomnum $p |- ( A e. dom card -> ( F Fn A -> ran F ~<_ A ) ) $=
    ( wfn crn wfo ccrd cdm wcel cdom wbr dffn4 fodomnum biimtrid ) BACABDZBEAFG
    HNAIJABKANBLM $.
    $( $j usage 'fnrndomnum' avoids 'ax-ac' 'ax-ac2'; $)

  $( The range of a function is dominated by its domain.  This theorem requires
     the axiom of choice ~ ax-ac2 ; see ~ fnrndomnum for a version that does
     not.  (Contributed by NM, 1-Sep-2004.)  (Proof shortened by Vincent
     Gonzalez, 17-Aug-2026.) $)
  fnrndomg $p |- ( A e. B -> ( F Fn A -> ran F ~<_ A ) ) $=
    ( wcel ccrd cdm wfn crn cdom wbr wi numth3 fnrndomnum syl ) ABDAEFDCAGCHAIJ
    KABLACMN $.

  $( Obsolete version of ~ fnrndomg as of 18-Aug-2026.  (Contributed by NM,
     1-Sep-2004.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  fnrndomgOLD $p |- ( A e. B -> ( F Fn A -> ran F ~<_ A ) ) $=
    ( wfn crn wfo wcel cdom wbr dffn4 fodomg biimtrid ) CADACEZCFABGMAHIACJAMCB
    KL $.

  $( If the domain of a function is countable, the function is countable.  The
     proof uses ~ fnrndomnum rather than ~ fnrndomg , and so does not require
     ~ ax-ac .  (Contributed by Thierry Arnoux, 29-Dec-2016.)  (Revised by
     Vincent Gonzalez, 24-Aug-2026.) $)
  fnct $p |- ( ( F Fn A /\ A ~<_ _om ) -> F ~<_ _om ) $=
    ( wfn com cdom wbr wa crn cxp cvv wcel wss ctex adantl adantr sylc sylancom
    cdm syl2anc domtr wfun wb eleq1d mpbird fnfun funrnex xpexd wf dffn3 birani
    fndm fssxp syl ssdomg cen xpdom1g omex ccrd con0 omelon simpr ondomen simpl
    a1i fnrndomnum xpdom2g sylancr xpomen domentr sylancl ) BACZADEFZGZBABHZIZE
    FZVODEFZBDEFVMVOJKBVOLZVPVMAVNJJVLAJKZVKAMNZVMBRZJKZBUAZVNJKZVMWBVSVTVKWBVS
    UBVLVKWAAJABUKUCOUDVKWCVLABUEOJBUFPZUGVMAVNBUHZVRVKWFVLABUIUJAVNBULUMBVOJUN
    PVMVODDIZEFZWGDUOFVQVMVODVNIZEFZWIWGEFZWHVKVLWDWJWEADVNJUPQVMDJKVNDEFZWKUQV
    KVLVNAEFZWLVMAURRKZVKWMVMDUSKZVLWNWOVMUTVDVKVLVADAVBSVKVLVCABVEPVNADTQVNDDJ
    VFVGVOWIWGTSVHVOWGDVIVJBVODTS $.
    $( $j usage 'fnct' avoids 'ax-ac' 'ax-ac2'; $)

  $( Obsolete version of ~ fnct as of 26-Aug-2026.  (Contributed by Thierry
     Arnoux, 29-Dec-2016.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  fnctOLD $p |- ( ( F Fn A /\ A ~<_ _om ) -> F ~<_ _om ) $=
    ( wfn com cdom wbr wa crn cxp cvv wcel wss ctex adantl adantr sylc sylancom
    cdm domtr syl2anc wfun wb eleq1d mpbird fnfun funrnex xpexd wf dffn3 birani
    fndm fssxp syl ssdomg cen xpdom1g omex simpl xpdom2g sylancr xpomen domentr
    fnrndomg sylancl ) BACZADEFZGZBABHZIZEFZVIDEFZBDEFVGVIJKBVILZVJVGAVHJJVFAJK
    ZVEAMNZVGBRZJKZBUAZVHJKZVGVPVMVNVEVPVMUBVFVEVOAJABUKUCOUDVEVQVFABUEOJBUFPZU
    GVGAVHBUHZVLVEVTVFABUIUJAVHBULUMBVIJUNPVGVIDDIZEFZWADUOFVKVGVIDVHIZEFZWCWAE
    FZWBVEVFVRWDVSADVHJUPQVGDJKVHDEFZWEUQVEVFVHAEFZWFVGVMVEWGVNVEVFURAJBVCPVHAD
    SQVHDDJUSUTVIWCWASTVAVIWADVBVDBVIDST $.

  ${
    $d x A $.
    $( A countable mapping set is countable.  (Contributed by Thierry Arnoux,
       29-Dec-2016.) $)
    mptct $p |- ( A ~<_ _om -> ( x e. A |-> B ) ~<_ _om ) $=
      ( com cdom wbr cmpt wfun cdm funmpt cvv wcel wss ctex eqid dmmptss ssdomg
      mpisyl domtr mpancom wfn funfn fnct sylanb sylancr ) BDEFZABCGZHZUGIZDEFZ
      UGDEFZABCJUIBEFZUFUJUFBKLUIBMULBNABCUGUGOPUIBKQRUIBDSTUHUGUIUAUJUKUGUBUIU
      GUCUDUE $.
  $}

  ${
    $d f g x y z A $.  $d f g y z B $.  $d f g x y z C $.  $d f y z T $.
    $d f ph $.
    iunfo.1 $e |- T = U_ x e. A ( { x } X. B ) $.
    $( Existence of an onto function from a disjoint union to a union.
       (Contributed by Mario Carneiro, 24-Jun-2013.)  (Revised by Mario
       Carneiro, 18-Jan-2014.) $)
    iunfo $p |- ( 2nd |` T ) : T -onto-> U_ x e. A B $=
      ( vy vz ciun c2nd wfo wfn wceq cvv wss mp2an cv cfv wrex wcel eliun fo2nd
      cres crn wf fof ffn mp2b ssv fnssres cima df-ima eleq2i bitri xp2nd eleq1
      csn cxp imbitrid reximdv biimtrid impcom rexlimiva nfiu1 nfcxfr nfrexw wa
      nfv cop ssiun2 adantr vsnid opelxp mpbiran bilanri sseldd eleqtrrdi op2nd
      fveqeq2 rspcev sylancl ex rexlimi impbii wb fvelimab 3bitr4i eqriv eqtr3i
      vex df-fo mpbir2an ) DABCHZIDUBZJWMDKZWMUCZWLLIMKZDMNZWNMMIJMMIUDWPUAMMIU
      EMMIUFUGZDUHZMDIUIOIDUJZWOWLIDUKFWTWLGPZIQZFPZLZGDRZXCCSZABRZXCWTSZXCWLSX
      EXGXDXGGDXDXADSZXGXIXAAPZUPZCUQZSZABRZXDXGXIXAABXLHZSXNDXOXAEULAXABXLTUMX
      DXMXFABXMXBCSXDXFXAXKCUNXBXCCUOURUSUTVAVBXFXEABXDAGDADXOEABXLVCVDXDAVGVEX
      JBSZXFXEXPXFVFZXJXCVHZDSXRIQXCLZXEXQXRXODXQXLXOXRXPXLXONXFABXLVIVJXRXLSZX
      FXPXTXJXKSXFAVKXJXCXKCVLVMVNVOEVPXJXCAWIFWIVQXDXSGXRDXAXRXCIVRVSVTWAWBWCW
      PWQXHXEWDWRWSGMDXCIWEOAXCBCTWFWGWHDWLWMWJWK $.

    iundomg.2 $e |- ( ph -> U_ x e. A ( C ^m B ) e. AC_ A ) $.
    iundomg.3 $e |- ( ph -> A. x e. A B ~<_ C ) $.
    $( An upper bound for the cardinality of a disjoint indexed union, with
       explicit choice principles. ` B ` depends on ` x ` and should be thought
       of as ` B ( x ) ` .  (Contributed by Mario Carneiro, 1-Sep-2015.) $)
    iundom2g $p |- ( ph -> T ~<_ ( A X. C ) ) $=
      ( vy vg cfv wf1 wral wa wcel wb cvv syl wceq vf vz cmap co ciun cv wf csb
      wex cxp cdom wbr wacn brdomi adantl f1f reldom brrelex2i brrelex1i elmapd
      wrex imbitrrid wss ssiun2 adantr sseld syld eximdv df-rex sylibr ralimiaa
      ancrd mpd nfv nfiu1 nfcv nfcsb1v nfrexw weq csbeq1a f1eq2 rexbidv cbvralw
      sylib f1eq1 acni3 syl2anc fveq2 bitrd c0 wn wne df-ne acnrcl wi rexlimivw
      nff1 r19.2z expcom xpexg syl6an biimtrrid xpeq1 0xp 0ex eqeltrdi pm2.61d2
      eqeltri c1st cop csn eleq2i eliun bitri r19.29 xp1st ad2antll elsni simpl
      eqeltrd fveq2d fveq1d ad2antrl xp2nd ffvelcdmd opelxpd rexlimiva biimtrid
      c2nd fvex opth simpr eqeq2d djussxp eqsstri simprl sselid simpll csbeq1d
      ex rspc nfel2 eqcomd eleqtrd rexlimi imp adantrr ralrimiv eleq12d rspccva
      sylc sylan adantrl eleqtrrd f1fveq syl12anc bitr3d pm5.32da simprr xpopth
      bitrid dom2d syl5com adantld exlimdv ) ACBCEDUCUDZUEZUAUFZUGZBJUFZDUHZEUV
      JUVHLZMZJCNZOZUAUIZFCEUJZUKULZAUVGCUMPZUVKEKUFZMZKUVGVAZJCNZUVPHADEUVTMZK
      UVGVAZBCNZUWCADEUKULZBCNZUWFIUWGUWEBCBUFZCPZUWGOZUVTUVGPZUWDOZKUIZUWEUWKU
      WDKUIZUWNUWGUWOUWJDEKUNUOUWKUWDUWMKUWKUWDUWLUWKUWDUVTUVFPZUWLUWDUWPUWKDEU
      VTUGZDEUVTUPUWGUWPUWQQUWJUWGEDUVTRRDEUKUQURZDEUKUQUSUTUOVBUWKUVFUVGUVTUWJ
      UVFUVGVCUWGBCUVFVDVEVFVGVLVHVMUWDKUVGVIVJVKSUWEUWBBJCUWEJVNUWABKUVGBCUVFV
      OBUVKEUVTBUVTVPBUVJDVQZBEVPZWQVRBJVSZUWDUWAKUVGUXADUVKTZUWDUWAQBUVJDVTZDU
      VKEUVTWASWBWCWDUWAUVMJKCUAUVGUVKEUVTUVLWEWFWGAUVOUVRUAAUVNUVRUVIUVNDEUWIU
      VHLZMZBCNZAUVRUXEUVMBJCUXEJVNBUVKEUVLBUVLVPUWSUWTWQUXAUXEDEUVLMZUVMUXAUXD
      UVLTUXEUXGQUWIUVJUVHWHDEUXDUVLWESUXAUXBUXGUVMQUXCDUVKEUVLWASWIWCAUVQRPZUX
      FUVRACWJTZUXHUXIWKCWJWLZAUXHCWJWMACRPZUXJERPZUXHAUVSUXKHCUVGWNSAUWHUXJUXL
      WOIUXJUWHUXLUXJUWHOUWGBCVAUXLUWGBCWRUWGUXLBCUWRWPSWSSCERRWTXAXBUXIUVQWJEU
      JZRCWJEXCUXMWJREXDXEXHXFXGUXFJUBFUVQUVJXILZUVJYILZUXNUVHLZLZXJZUBUFZXILZU
      XSYILZUXTUVHLZLZXJZRUVJFPZUVJUWIXKZDUJZPZBCVAZUXFUXRUVQPZUYEUVJBCUYGUEZPU
      YIFUYKUVJGXLBUVJCUYGXMXNZUXFUYIUYJUXFUYIOZUXEUYHOZBCVAZUYJUXEUYHBCXOZUYNU
      YJBCUWJUYNOZUXNUXQCEUYQUXNUWICUYQUXNUYFPZUXNUWITUYHUYRUWJUXEUVJUYFDXPXQUX
      NUWIXRSZUWJUYNXSXTUYQUXQUXOUXDLEUYQUXOUXPUXDUYQUXNUWIUVHUYSYAYBUYQDEUXOUX
      DUXEDEUXDUGUWJUYHDEUXDUPYCUYHUXODPUWJUXEUVJUYFDYDXQZYEXTYFYGSYTYHUXFUYEUX
      SFPZOZUXRUYDTZJUBVSZQVUCUXNUXTTZUXQUYCTZOZUXFVUBOZVUDUXNUXQUXTUYCUVJXIYJU
      XOUXPYJYKVUHVUGVUEUXOUYATZOZVUDVUHVUEVUFVUIVUHVUEOZUXQUYAUXPLZTZVUFVUIVUK
      VULUYCUXQVUKUYAUXPUYBVUKUXNUXTUVHVUHVUEYLZYAYBYMVUKBUXNDUHZEUXPMZUXOVUOPZ
      UYAVUOPVUMVUIQVUKUXNCPZUXFVUPVUKUVJCRUJZPZVURVUHVUTVUEVUHFVUSUVJFUYKVUSGB
      CDYNYOZUXFUYEVUAYPYQZVEUVJCRXPSUXFVUBVUEYRUXEVUPBUXNCBVUOEUXPBUXPVPBUXNDV
      QZUWTWQUWIUXNTZUXEDEUXPMZVUPVVDUXDUXPTUXEVVEQUWIUXNUVHWHDEUXDUXPWESVVDDVU
      OTZVVEVUPQBUXNDVTZDVUOEUXPWASWIUUAUUKVUHVUQVUEUXFUYEVUQVUAUXFUYEVUQUYEUYI
      UXFVUQUYLUXFUYIVUQUYMUYOVUQUYPUYNVUQBCBUXOVUOVVCUUBUWJUYNVUQUYQUXODVUOUYT
      UYQVVDVVFUYQUXNUWIUYSUUCVVGSUUDYTUUESYTYHZUUFUUGVEVUKUYABUXTDUHZVUOVUHUYA
      VVIPZVUEUXFVUAVVJUYEUXFVUQJFNVUAVVJUXFVUQJFVVHUUHVUQVVJJUXSFVUDUXOUYAVUOV
      VIUVJUXSYIWHVUDBUXNUXTDUVJUXSXIWHYSUUIUUJUULUUMVEVUKBUXNUXTDVUNYSUUNVUOEU
      XOUYAUXPUUOUUPUUQUURVUHVUTUXSVUSPVUJVUDQVVBVUHFVUSUXSVVAUXFUYEVUAUUSYQUVJ
      UXSCRCRUUTWGWIUVAYTUVBUVCXBUVDUVEVM $.

    iundomg.4 $e |- ( ph -> ( A X. C ) e. AC_ U_ x e. A B ) $.
    $( An upper bound for the cardinality of an indexed union, with explicit
       choice principles. ` B ` depends on ` x ` and should be thought of as
       ` B ( x ) ` .  (Contributed by Mario Carneiro, 1-Sep-2015.) $)
    iundomg $p |- ( ph -> U_ x e. A B ~<_ ( A X. C ) ) $=
      ( ciun cdom wbr cxp wacn wcel c2nd cres wfo iundom2g acndom2 iunfo mpisyl
      sylc fodomacn domtr syl2anc ) ABCDKZFLMZFCENZLMZUHUJLMAFUHOZPZFUHQFRZSUIA
      UKUJULPUMABCDEFGHITZJUHFUJUAUDBCDFGUBFUHUNUEUCUOUHFUJUFUG $.
  $}

  ${
    $d x A $.  $d x B $.
    $( An upper bound for the cardinality of an indexed union. ` C ` depends on
       ` x ` and should be thought of as ` C ( x ) ` .  (Contributed by NM,
       26-Mar-2006.) $)
    iundom $p |- ( ( A e. V /\ A. x e. A C ~<_ B ) ->
        U_ x e. A C ~<_ ( A X. B ) ) $=
      ( wcel cdom wbr wral wa cxp ciun cmap wacn cvv iunexg numth3 numacn sylc
      reldom cv csn eqid ccrd cdm simpl ovex rgenw sylancl syl brrelex1i ralimi
      co simpr sylan2 iundom2g brrelex2i 3syl iundomg ) BEFZDCGHZABIZJZABDCABAU
      AUBDKLZVDUCZVCUTABCDMUMZLZUDUEZFZVGBNFUTVBUFZVCVGOFZVIVCUTVFOFZABIVKVJVLA
      BCDMUGUHABVFEOPUIVGOQUJBEVGRSZUTVBUNZVCABDLZOFZBCKZVHFZVQVONFVBUTDOFZABIV
      PVAVSABDCGTUKULABDEOPUOVCVDVQGHVQOFVRVCABDCVDVEVMVNUPVDVQGTUQVQOQURVOOVQR
      SUS $.

    $( An upper bound for the cardinality of a union.  Theorem 10.47 of
       [TakeutiZaring] p. 98.  (Contributed by NM, 25-Mar-2006.)  (Proof
       shortened by Mario Carneiro, 1-Sep-2015.) $)
    unidom $p |- ( ( A e. V /\ A. x e. A x ~<_ B ) -> U. A ~<_ ( A X. B ) ) $=
      ( wcel cv cdom wbr wral wa cuni ciun cxp uniiun iundom eqbrtrid ) BDEAFZC
      GHABIJBKABQLBCMGABNABCQDOP $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y F $.
    uniimadom.1 $e |- A e. _V $.
    uniimadom.2 $e |- B e. _V $.
    $( An upper bound for the cardinality of the union of an image.  Theorem
       10.48 of [TakeutiZaring] p. 99.  (Contributed by NM, 25-Mar-2006.) $)
    uniimadom $p |- ( ( Fun F /\ A. x e. A ( F ` x ) ~<_ B ) ->
                 U. ( F " A ) ~<_ ( A X. B ) ) $=
      ( vy wfun cv cdom wbr wral cxp cvv wcel adantr wi wrex syl syl2anc cfv wa
      cima cuni funimaex wceq fvelima ex breq1 biimpd reximi r19.36v syl6 com23
      imp ralrimiv unidom imadomg ax-mp xpdom1 domtr ) DHZAIDUAZCJKZABLZUBZDBUC
      ZUDZVGCMZJKZVIBCMZJKZVHVKJKVFVGNOZGIZCJKZGVGLVJVBVMVEDBEUEPVFVOGVGVBVEVNV
      GOZVOQVBVPVEVOVBVPVCVNUFZABRZVEVOQZVBVPVRAVNBDUGUHVRVDVOQZABRVSVQVTABVQVD
      VOVCVNCJUIUJUKVDVOABULSUMUNUOUPGVGCNUQTVBVLVEVBVGBJKZVLBNOVBWAQEBNDURUSVG
      BCFUTSPVHVIVKVAT $.
  $}

  ${
    $d x z A $.  $d x z B $.  $d z F $.
    uniimadomf.1 $e |- F/_ x F $.
    uniimadomf.2 $e |- A e. _V $.
    uniimadomf.3 $e |- B e. _V $.
    $( An upper bound for the cardinality of the union of an image.  Theorem
       10.48 of [TakeutiZaring] p. 99.  This version of ~ uniimadom uses a
       bound-variable hypothesis in place of a distinct variable condition.
       (Contributed by NM, 26-Mar-2006.) $)
    uniimadomf $p |- ( ( Fun F /\ A. x e. A ( F ` x ) ~<_ B ) ->
                 U. ( F " A ) ~<_ ( A X. B ) ) $=
      ( vz cv cfv cdom wbr wral wfun cima cuni cxp nfv nfcv nffv nfbr weq fveq2
      breq1d cbvralw uniimadom sylan2b ) AIZDJZCKLZABMDNHIZDJZCKLZHBMDBOPBCQKLU
      JUMAHBUJHRAULCKAUKDEAUKSTAKSACSUAAHUBUIULCKUHUKDUCUDUEHBCDFGUFUG $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Cardinal number theorems using Axiom of Choice
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x A $.
    cardval.1 $e |- A e. _V $.
    $( The value of the cardinal number function.  Definition 10.4 of
       [TakeutiZaring] p. 85.  See ~ cardval2 for a simpler version of its
       value.  (Contributed by NM, 21-Oct-2003.)  (Revised by Mario Carneiro,
       28-Apr-2015.) $)
    cardval $p |- ( card ` A ) = |^| { x e. On | x ~~ A } $=
      ( cvv wcel ccrd cdm cfv cen wbr con0 crab cint wceq numth3 cardval3 mp2b
      cv ) BDEBFGEBFHARBIJAKLMNCBDOABPQ $.

    $( Any set is equinumerous to its cardinal number.  Proposition 10.5 of
       [TakeutiZaring] p. 85.  (Contributed by NM, 22-Oct-2003.)  (Revised by
       Mario Carneiro, 28-Apr-2015.) $)
    cardid $p |- ( card ` A ) ~~ A $=
      ( cvv wcel ccrd cdm cfv cen wbr numth3 cardid2 mp2b ) ACDAEFDAEGAHIBACJAK
      L $.
  $}

  $( Any set is equinumerous to its cardinal number.  Closed theorem form of
     ~ cardid .  (Contributed by David Moews, 1-May-2017.) $)
  cardidg $p |- ( A e. B -> ( card ` A ) ~~ A ) $=
    ( wcel cvv ccrd cfv cen wbr elex cdm cardeqv eleq2i cardid2 sylbir syl ) AB
    CADCZAEFAGHZABIPAEJZCQRDAKLAMNO $.

  ${
    cardidd.1 $e |- ( ph -> A e. B ) $.
    $( Any set is equinumerous to its cardinal number.  Deduction form of
       ~ cardid .  (Contributed by David Moews, 1-May-2017.) $)
    cardidd $p |- ( ph -> ( card ` A ) ~~ A ) $=
      ( wcel ccrd cfv cen wbr cardidg syl ) ABCEBFGBHIDBCJK $.
  $}

  ${
    $d x y $.
    $( The cardinality function is a function with domain the well-orderable
       sets.  Assuming AC, this is the universe.  (Contributed by Mario
       Carneiro, 6-Jun-2013.)  (Revised by Mario Carneiro, 13-Sep-2013.) $)
    cardf $p |- card : _V --> On $=
      ( vy vx cv cen wbr con0 wrex cab ccrd wf cvv cardf2 cdm fdmi eqtr3i feq2i
      cardeqv mpbi ) ACBCDEAFGBHZFIJKFIJBALZSKFIIMSKSFITNQOPR $.
  $}

  $( Two sets are equinumerous iff their cardinal numbers are equal.  This
     important theorem expresses the essential concept behind "cardinality" or
     "size".  This theorem appears as Proposition 10.10 of [TakeutiZaring]
     p. 85, Theorem 7P of [Enderton] p. 197, and Theorem 9 of [Suppes] p. 242
     (among others).  The Axiom of Choice is required for its proof.  Related
     theorems are ~ hasheni and the finite-set-only ~ hashen .

     This theorem is also known as Hume's Principle.  Gottlob Frege's
     two-volume _Grundgesetze der Arithmetik_ used his Basic Law V to prove
     this theorem.  Unfortunately Basic Law V caused Frege's system to be
     inconsistent because it was subject to Russell's paradox (see ~ ru ).
     Later scholars have found that Frege primarily used Basic Law V to Hume's
     Principle.  If Basic Law V is replaced by Hume's Principle in Frege's
     system, much of Frege's work is restored. _Grundgesetze der Arithmetik_,
     once Basic Law V is replaced, proves "Frege's theorem" (the Peano axioms
     of arithmetic can be derived in second-order logic from Hume's principle).
     See ~ https://plato.stanford.edu/entries/frege-theorem .  We take a
     different approach, using first-order logic and ZFC, to prove the Peano
     axioms of arithmetic.

     The theory of cardinality can also be developed without AC by introducing
     "card" as a primitive notion and stating this theorem as an axiom, as is
     done with the axiom for cardinal numbers in [Suppes] p. 111.  Finally, if
     we allow the Axiom of Regularity, we can avoid AC by defining the cardinal
     number of a set as the set of all sets equinumerous to it and having the
     least possible rank (see ~ karden ).  (Contributed by NM, 22-Oct-2003.) $)
  carden $p |- ( ( A e. C /\ B e. D ) ->
               ( ( card ` A ) = ( card ` B ) <-> A ~~ B ) ) $=
    ( wcel wa ccrd cfv wceq cen wbr numth3 ad2antrr cardid2 ensym 3syl ad2antlr
    cdm simpr cardidd eqbrtrd entr syl2anc ex carden2b impbid1 ) ACEZBDEZFZAGHZ
    BGHZIZABJKZUIULUMUIULFZAUJJKZUJBJKUMUNAGRZEZUJAJKUOUGUQUHULACLMANUJAOPUNUJU
    KBJUIULSUNBUPUHBUPEUGULBDLQTUAAUJBUBUCUDABUEUF $.

  $( Only the empty set has cardinality zero.  (Contributed by NM,
     23-Apr-2004.) $)
  cardeq0 $p |- ( A e. V -> ( ( card ` A ) = (/) <-> A = (/) ) ) $=
    ( wcel ccrd cfv c0 cen wbr cvv wb 0ex carden mpan2 card0 eqeq2i en0 3bitr3g
    wceq ) ABCZADEZFDEZRZAFGHZTFRAFRSFICUBUCJKAFBILMUAFTNOAPQ $.

  ${
    unsnen.1 $e |- A e. _V $.
    unsnen.2 $e |- B e. _V $.
    $( Equinumerosity of a set with a new element added.  (Contributed by NM,
       7-Nov-2008.) $)
    unsnen $p |- ( -. B e. A -> ( A u. { B } ) ~~ suc ( card ` A ) ) $=
      ( wcel wn csn cun ccrd cfv csuc cen cin wceq wbr disjsn word cardon cvv
      c0 onordi orddisj ax-mp cardid ensymi fvex en2sn mp2an unen mpanl12 mpan2
      wa sylbir df-suc breqtrrdi ) BAEFZABGZHZAIJZUSGZHZUSKLUPAUQMTNZURVALOZABP
      VBUSUTMTNZVCUSQVDUSARUAUSUBUCAUSLOUQUTLOZVBVDULVCUSAACUDUEBSEUSSEVEDAIUFB
      USSSUGUHAUSUQUTUIUJUKUMUSUNUO $.
  $}

  $( Two sets have the dominance relationship iff their cardinalities have the
     subset relationship.  Equation i of [Quine] p. 232.  (Contributed by NM,
     22-Oct-2003.)  (Revised by Mario Carneiro, 30-Apr-2015.) $)
  carddom $p |- ( ( A e. V /\ B e. W ) ->
               ( ( card ` A ) C_ ( card ` B ) <-> A ~<_ B ) ) $=
    ( wcel ccrd cdm cfv wss cdom wbr wb numth3 carddom2 syl2an ) ACEAFGZEBPEAFH
    BFHIABJKLBDEACMBDMABNO $.

  $( Two sets have the strict dominance relationship iff their cardinalities
     have the membership relationship.  Corollary 19.7(2) of [Eisenberg]
     p. 310.  (Contributed by NM, 22-Oct-2003.)  (Revised by Mario Carneiro,
     30-Apr-2015.) $)
  cardsdom $p |- ( ( A e. V /\ B e. W ) ->
               ( ( card ` A ) e. ( card ` B ) <-> A ~< B ) ) $=
    ( wcel ccrd cdm cfv csdm wbr wb numth3 cardsdom2 syl2an ) ACEAFGZEBOEAFHBFH
    EABIJKBDEACLBDLABMN $.

  $( Trichotomy law for dominance and strict dominance.  This theorem is
     equivalent to the Axiom of Choice.  (Contributed by NM, 4-Jan-2004.)
     (Revised by Mario Carneiro, 30-Apr-2015.) $)
  domtri $p |- ( ( A e. V /\ B e. W ) -> ( A ~<_ B <-> -. B ~< A ) ) $=
    ( wcel ccrd cdm cdom wbr csdm wn wb numth3 domtri2 syl2an ) ACEAFGZEBPEABHI
    BAJIKLBDEACMBDMABNO $.

  $( Trichotomy of equinumerosity and strict dominance.  This theorem is
     equivalent to the Axiom of Choice.  Theorem 8 of [Suppes] p. 242.
     (Contributed by NM, 4-Jan-2004.) $)
  entric $p |- ( ( A e. V /\ B e. W ) -> ( A ~< B \/ A ~~ B \/ B ~< A ) ) $=
    ( wcel wa csdm wbr cen wo wn cdom domtri biimprd brdom2 imbitrdi con1d orrd
    w3o df-3or sylibr ) ACEBDEFZABGHZABIHZJZBAGHZJUCUDUFSUBUEUFUBUFUEUBUFKZABLH
    ZUEUBUHUGABCDMNABOPQRUCUDUFTUA $.

  $( Trichotomy of dominance and strict dominance.  (Contributed by NM,
     4-Jan-2004.) $)
  entri2 $p |- ( ( A e. V /\ B e. W ) -> ( A ~<_ B \/ B ~< A ) ) $=
    ( wcel wa csdm wbr cen w3o cdom entric brdom2 orbi1i df-3or bitr4i sylibr
    wo ) ACEBDEFABGHZABIHZBAGHZJZABKHZUARZABCDLUDSTRZUARUBUCUEUAABMNSTUAOPQ $.

  $( Trichotomy of dominance.  This theorem is equivalent to the Axiom of
     Choice.  Part of Proposition 4.42(d) of [Mendelson] p. 275.  (Contributed
     by NM, 4-Jan-2004.) $)
  entri3 $p |- ( ( A e. V /\ B e. W ) -> ( A ~<_ B \/ B ~<_ A ) ) $=
    ( wcel wa cdom wbr csdm wo entri2 sdomdom orim2i syl ) ACEBDEFABGHZBAIHZJOB
    AGHZJABCDKPQOBALMN $.

  $( A set strictly dominates iff its cardinal strictly dominates.
     (Contributed by NM, 30-Oct-2003.) $)
  sdomsdomcard $p |- ( A ~< B <-> A ~< ( card ` B ) ) $=
    ( csdm wbr ccrd cfv cen cvv wcel cdm relsdom brrelex2i numth3 cardid2 ensym
    4syl sdomentr mpdan sdomsdomcardi impbii ) ABCDZABEFZCDZUABUBGDZUCUABHIBEJI
    UBBGDUDABCKLBHMBNUBBOPABUBQRABST $.

  $( Cantor's theorem in terms of cardinals.  This theorem tells us that no
     matter how large a cardinal number is, there is a still larger cardinal
     number.  Theorem 18.12 of [Monk1] p. 133.  (Contributed by NM,
     5-Nov-2003.) $)
  canth3 $p |- ( A e. V -> ( card ` A ) e. ( card ` ~P A ) ) $=
    ( wcel ccrd cfv cpw csdm wbr canth2g cvv wb pwexg cardsdom mpdan mpbird ) A
    BCZADEAFZDECZAQGHZABIPQJCRSKABLAQBJMNO $.

  $( Every infinite class is equinumerous to its Cartesian square.  This
     theorem, which is equivalent to the axiom of choice over ZF, provides the
     basis for infinite cardinal arithmetic.  Proposition 10.40 of
     [TakeutiZaring] p. 95.  This is a corollary of ~ infxpen (used via
     ~ infxpidm2 ).  (Contributed by NM, 17-Sep-2004.)  (Revised by Mario
     Carneiro, 9-Mar-2013.) $)
  infxpidm $p |- ( _om ~<_ A -> ( A X. A ) ~~ A ) $=
    ( ccrd cdm wcel com cdom wbr cxp cen cvv reldom brrelex2i infxpidm2 mpancom
    numth3 syl ) ABCDZEAFGZAAHAIGRAJDQEAFKLAJOPAMN $.

  ${
    $d x y z A $.
    $( The class of ordinals dominated by a given set is an ordinal.  Theorem
       56 of [Suppes] p. 227.  This theorem can be proved without the axiom of
       choice, see ~ hartogs .  (Contributed by NM, 7-Nov-2003.)
       (Proof modification is discouraged.)  Use ~ hartogs instead.
       (New usage is discouraged.) $)
    ondomon $p |- ( A e. V -> { x e. On | x ~<_ A } e. On ) $=
      ( vy vz wcel cv cdom wbr con0 crab word wss wa wi wal cvv imp breq1 ccrd
      wtr onelon vex onelss ssdomg mpsyl domtr anim2i anassrs sylan exp31 com12
      jca impd elrab 3imtr4g gen2 dftr2 mpbir ssrab2 ordon trssord mp3an wb cpw
      csdm cfv wceq pwexg numth3 cardval2 3syl fvex eqeltrrdi wral elex canth2g
      cdm domsdomtr sylan2 expcom ralrimivw syl ss2rabd ssexd elong mpbiri ) BC
      FZAGZBHIZAJKZJFZWKLZWKUAZWKJMJLWMWNDGZEGZFZWPWKFZNWOWKFZOZEPDPWTDEWQWRWSW
      QWPJFZWPBHIZNWOJFZWOBHIZNZWRWSWQXAXBXEXAWQXBXEOXAWQXBXEXAWQNZXCWOWPHIZNXB
      XEXFXCXGWPWOUBWPQFXFWOWPMZXGEUCXAWQXHWPWOUDRWOWPQUEUFUMXCXGXBXEXGXBNXDXCW
      OWPBUGUHUIUJUKULUNWJXBAWPJWIWPBHSUOWJXDAWOJWIWOBHSUOUPRUQDEWKURUSWJAJUTVA
      WKJVBVCWHWKQFWLWMVDWHWKWIBVEZVFIZAJKZQWHXKXITVGZQWHXIQFXITVRFXLXKVHBCVIXI
      QVJAXIVKVLXITVMVNWHWJXJAJWHBQFZWJXJOZAJVOBCVPXMXNAJWJXMXJXMWJBXIVFIXJBQVQ
      WIBXIVSVTWAWBWCWDWEWKQWFWCWG $.
  $}

  ${
    $d x y A $.  $d y V $.
    $( The smallest ordinal that strictly dominates a set is a cardinal.
       (Contributed by NM, 28-Oct-2003.)  (Revised by Mario Carneiro,
       20-Sep-2014.) $)
    cardmin $p |- ( A e. V -> ( card ` |^| { x e. On | A ~< x } ) =
                      |^| { x e. On | A ~< x } ) $=
      ( vy wcel cv csdm wbr con0 crab cint wral ccrd cfv wceq wrex syl cvv nfcv
      breq2 numthcor onintrab2 sylib cdom wa wn wi onelon ex onnminsb wb domtri
      syli vex mpan sylibrd nfrab1 nfint nfbr onminsb jctird domsdomtr ralrimiv
      syl6 iscard sylanbrc ) BCEZBAFZGHZAIJZKZIEZDFZVKGHZDVKLVKMNVKOVGVIAIPZVLA
      BCUAZVIAUBUCZVGVNDVKVGVMVKEZVMBUDHZBVKGHZUEVNVGVRVSVTVGVRBVMGHZUFZVSVRVGV
      MIEZWBVGVLVRWCUGVQVLVRWCVKVMUHUIQVIWAAVMVHVMBGTUJUMVMREVGVSWBUKDUNVMBRCUL
      UOUPVGVOVTVPVIVTAABVKGABSAGSAVJVIAIUQURUSVHVKBGTUTQVAVMBVKVBVDVCDVKVEVF
      $.
  $}

  ${
    $d A x $.  $d V x $.
    $( A set is finite iff its cardinal is a natural number.  (Contributed by
       Jeff Madsen, 2-Sep-2009.) $)
    ficard $p |- ( A e. V -> ( A e. Fin <-> ( card ` A ) e. _om ) ) $=
      ( vx wcel cfn ccrd cfv com cv cen wrex isfi wa wceq carden wi cardnn eqtr
      wbr adantl expcom syl eleq1a syld sylbird rexlimdva biimtrid eqcomd mpbid
      ex ancld breq2 rspcev sylibr syl6 impbid ) ABDZAEDZAFGZHDZURACIZJSZCHKZUQ
      UTCALZUQVBUTCHUQVAHDZMVBUSVAFGZNZUTAVABHOVEVGUTPUQVEVGUSVANZUTVEVFVANZVGV
      HPVAQVGVIVHUSVFVARUAUBVAHUSUCUDTUEUFUGUQUTUTAUSJSZMZURUQUTVJUQUTVJUQUTMUS
      USFGZNZVJUTVMUQUTVLUSUSQUHTAUSBHOUIUJUKVKVCURVBVJCUSHVAUSAJULUMVDUNUOUP
      $.
  $}

  $( Equivalence between two infiniteness criteria for sets.  To avoid the
     axiom of infinity, we include it as a hypothesis.  (Contributed by Scott
     Fenton, 20-Feb-2026.) $)
  infinfg $p |- ( ( _om e. _V /\ A e. B ) -> ( -. A e. Fin <-> _om ~<_ A ) ) $=
    ( com cvv wcel wa cfn wn csdm cdom wb isfiniteg adantr notbid domtri bitr4d
    wbr ) CDEZABEZFZAGEZHACIQZHCAJQTUAUBRUAUBKSALMNCADBOP $.
  $( $j usage 'infinfg' avoids 'ax-inf' 'ax-inf2'; $)

  $( Equivalence between two infiniteness criteria for sets.  (Contributed by
     David Moews, 1-May-2017.)  (Proof shortened by Scott Fenton,
     20-Feb-2026.) $)
  infinf $p |- ( A e. B -> ( -. A e. Fin <-> _om ~<_ A ) ) $=
    ( com cvv wcel cfn wn cdom wbr wb omex infinfg mpan ) CDEABEAFEGCAHIJKABLM
    $.

  ${
    $d F x $.
    unirnfdomd.1 $e |- ( ph -> F : T --> Fin ) $.
    unirnfdomd.2 $e |- ( ph -> -. T e. Fin ) $.
    unirnfdomd.3 $e |- ( ph -> T e. V ) $.
    $( The union of the range of a function from an infinite set into the class
       of finite sets is dominated by its domain.  Deduction form.
       (Contributed by David Moews, 1-May-2017.) $)
    unirnfdomd $p |- ( ph -> U. ran F ~<_ T ) $=
      ( vx crn cxp cdom wbr com cvv wcel wral cfn syl2anc syl domtr cuni cen cv
      wfn ffnd fnex rnexg wf wss frn dfss3 sylib fict ralimi 3syl fnrndomg sylc
      unidom omex xpdom1 wn wb infinf mpbid xpdom2g infxpidm domentr ) ACIZUAZB
      BJZKLZVJBUBLZVIBKLAVIBMJZKLZVMVJKLZVKAVIVHMJZKLZVPVMKLZVNAVHNOZHUCZMKLZHV
      HPZVQACNOZVSACBUDZBDOZWCABQCEUEZGBDCUFRCNUGSABQCUHZVTQOZHVHPZWBEWGVHQUIWI
      BQCUJHVHQUKULWHWAHVHVTUMUNUOHVHMNURRAVHBKLZVRAWEWDWJGWFBDCUPUQVHBMUSUTSVI
      VPVMTRAWEMBKLZVOGABQOVAZWKFAWEWLWKVBGBDVCSVDZMBBDVERVIVMVJTRAWKVLWMBVFSVI
      VJBVGR $.
  $}

  ${
    konigth.1 $e |- A e. _V $.
    konigth.2 $e |- S = U_ i e. A ( M ` i ) $.
    konigth.3 $e |- P = X_ i e. A ( N ` i ) $.
    ${
      $d A a e f i $.  $d D a e $.  $d E a i $.  $d M a f $.  $d N a e f $.
      $d P a e f $.  $d S a e f $.
      konigth.4 $e |- D = ( i e. A |-> ( a e. ( M ` i ) |->
        ( ( f ` a ) ` i ) ) ) $.
      konigth.5 $e |- E = ( i e. A |-> ( e ` i ) ) $.
      $( Lemma for ~ konigth .  (Contributed by Mario Carneiro,
         22-Feb-2013.) $)
      konigthlem $p |- ( A. i e. A ( M ` i ) ~< ( N ` i ) -> S ~< P ) $=
        ( cfv c0 wcel cvv cv csdm wbr wral wn wfo wex crn cdif wne wa cdom fvex
        wfn cmpt eqid fnmpti wceq mptex fvmpt2 fneq1d mpbiri fnrndomg domsdomtr
        mpan2 mpsyl sylan sdomdif syl ralimiaa difexi ac6c5 equid eldifi eleq1d
        cixp imbitrrid ralimia jctil eqeltri elixp sylibr eleqtrrdi wrex foelrn
        expcom ciun eleq2i eliun bitri nfra1 nfv nfan w3a ad2antrl fveq1 fveq1d
        sylan9eq eqcomd eqtr3d fnfvelrn adantl eqeltrd 3adant1 simp1 simp3l rsp
        wi eldifn syl6 sylc pm2.21dd expd rexlimd biimtrid com23 rexlimdv syl9r
        3expia mpd mt2i exlimiv 3syl nexdv 0dom 0sdom sylib ralimi neeq1i rgenw
        ex mpan ixpexg ax-mp ac9 3bitr4i wb iunex domtri mp2an biimpri notnotrd
        fodomr syl2an mtand ) GUAZIQZUUFJQZUBUCZGAUDZDCUBUCZUUJUUKUEZDCFUAZUFZF
        UGZUUJUUNFUUJUUHUUFBQZUHZUIZRUJZGAUDUUFEUAZQZUURSZGAUDZEUGUUNUEZUUIUUSG
        AUUFASZUUIUKUUQUUHUBUCZUUSUVEUUQUUGULUCZUUIUVFUUGTSUVEUUPUUGUNZUVGUUFIU
        MZUVEUVHKUUGUUFKUAZUUMQZQZUOZUUGUNKUUGUVLUVMUUFUVKUMZUVMUPZUQUVEUUGUUPU
        VMUVEUVMTSUUPUVMURKUUGUVLUVIUSGAUVMTBOUTVEZVAVBZUUGTUUPVCVFUUQUUGUUHVDV
        GUUQUUHVHVIVJGAUURELUUHUUQUUFJUMZVKVLUVCUVDEUVCUUNUUMUUMURZFVMUVCHCSZUU
        NUVSUEZXHUVCHGAUUHVPZCUVCHAUNZUUFHQZUUHSZGAUDZUKHUWBSUVCUWFUWCUVBUWEGAU
        VBUWEUVEUVAUUHSUVAUUHUUQVNUVEUWDUVAUUHUVEUVATSUWDUVAURZUUFUUTUMZGAUVATH
        PUTVEZVOVQVRGAUVAHUWHPUQVSGAUUHHHGAUVAUOTPGAUVALUSVTWAWBNWCUVTUUNHUVKUR
        ZKDWDZUVCUWAUUNUVTUWKKDCHUUMWEWFUVCUWJUWAKDUVCUWJUVJDSZUWAUVCUWJUWLUWAX
        HUWLUVJUUGSZGAWDZUVCUWJUKZUWAUWLUVJGAUUGWGZSUWNDUWPUVJMWHGUVJAUUGWIWJUW
        OUWMUWAGAUVCUWJGUVBGAWKUWJGWLWMUWAGWLUWOUVEUWMUWAUVCUWJUVEUWMUKZUWAUVCU
        WJUWQWNZUVAUUQSZUWAUWJUWQUWSUVCUWJUWQUKZUVAUVJUUPQZUUQUWTUWDUVAUXAUVEUW
        GUWJUWMUWIWOUWJUWQUWDUVLUXAUUFHUVKWPUWQUXAUVLUVEUWMUXAUVJUVMQZUVLUVEUVJ
        UUPUVMUVPWQUWMUVLTSUXBUVLURUVNKUUGUVLTUVMUVOUTVEWRWSWRWTUWQUXAUUQSZUWJU
        VEUVHUWMUXCUVQUUGUVJUUPXAVGXBXCXDUWRUVCUVEUWSUEZUVCUWJUWQXEUVCUWJUVEUWM
        XFUVCUVEUVBUXDUVBGAXGUVAUUHUUQXIXJXKXLXSXMXNXOYKXPXQXRXTYAYBYCYDUUJRCUB
        UCZCDULUCZUUOUULUUJUUHRUJZGAUDZUXEUUIUXGGAUUIRUUHUBUCZUXGRUUGULUCUUIUXI
        UUGUVIYERUUGUUHVDYLUUHUVRYFYGYHCRUJUWBRUJUXEUXHCUWBRNYICCUWBTNUUHTSZGAU
        DUWBTSUXJGAUVRYJGAUUHTYMYNVTZYFGAUUHLUVRYOYPWBUXFUULCTSDTSUXFUULYQUXKDU
        WPTMGAUUGLUVIYRVTCDTTYSYTUUADCFUUCUUDUUEUUB $.
    $}
    $d A a e f i $.  $d A a e i j $.  $d M a b e f $.  $d N a e f $.
    $d P a e f $.  $d S a e f $.  $d b e f i $.
    $( Konig's Theorem.  If ` m ( i ) ~< n ( i ) ` for all ` i e. A ` , then
       ` sum_ i e. A m ( i ) ~< prod_ i e. A n ( i ) ` , where the sums and
       products stand in for disjoint union and infinite cartesian product.
       The version here is proven with unions rather than disjoint unions for
       convenience, but the version with disjoint unions is clearly a special
       case of this version.  The Axiom of Choice is needed for this proof, but
       it contains AC as a simple corollary (letting ` m ( i ) = (/) ` , this
       theorem says that an infinite cartesian product of nonempty sets is
       nonempty), so this is an AC equivalent.  Theorem 11.26 of
       [TakeutiZaring] p. 107.  (Contributed by Mario Carneiro,
       22-Feb-2013.) $)
    konigth $p |- ( A. i e. A ( M ` i ) ~< ( N ` i ) -> S ~< P ) $=
      ( vb vf ve vj va cv cfv cmpt weq fveq2 cbvmptv fveq1d mpteq2i konigthlem
      ) ADAJDOZEPZUDJOZKOZPZPZQZQBCLKDMAMOZLOZPZQEFNGHIDAUJNUEUDNOZUGPZPZQJNUEU
      IUPJNRUDUHUOUFUNUGSUATUBMDAUMUDULPUKUDULSTUC $.
  $}

  $( The power set of an aleph dominates the successor aleph.  (The Generalized
     Continuum Hypothesis says they are equinumerous, see ~ gch3 or
     ~ gchaleph2 .)  (Contributed by NM, 27-Aug-2005.) $)
  alephsucpw $p |- ( aleph ` suc A ) ~<_ ~P ( aleph ` A ) $=
    ( csuc cale cfv cpw cdom wbr csdm wn alephsucpw2 cvv wcel fvex domtri mp2an
    wb pwex mpbir ) ABZCDZACDZEZFGZUBTHGIZAJTKLUBKLUCUDPSCMUAACMQTUBKKNOR $.

  $( The set exponentiation of 2 to the aleph-zero has cardinality of at least
     aleph-one.  (If we were to assume the Continuum Hypothesis, their
     cardinalities would be the same.)  (Contributed by NM, 7-Jul-2004.) $)
  aleph1 $p |- ( aleph ` 1o ) ~<_ ( 2o ^m ( aleph ` (/) ) ) $=
    ( c1o cale cfv c0 csuc c2o cmap co cdom df-1o fveq2i cpw wbr alephsucpw cen
    wb fvex pw2en domen2 ax-mp mpbi eqbrtri ) ABCDEZBCZFDBCZGHZIAUCBJKUDUELZIMZ
    UDUFIMZDNUGUFOMUHUIPUEDBQRUGUFUDSTUAUB $.

  ${
    $d x y z A $.
    $( An alternate way to express the value of the aleph function for nonzero
       arguments.  Theorem 64 of [Suppes] p. 229.  (Contributed by NM,
       15-Nov-2003.) $)
    alephval2 $p |- ( ( A e. On /\ (/) e. A ) -> ( aleph ` A ) =
                    |^| { x e. On | A. y e. A ( aleph ` y ) ~< x } ) $=
      ( vz con0 wcel cale cfv csdm wbr wral wceq wa ccrd com cdom wi cvv wss wb
      cv crab c0 wn alephordi ralrimiv alephon jctil breq2 ralbidv elrab sylibr
      cint cardsdomelir alephcard eqcomi eleq2s wo omex vex entri3 mp2an cardom
      carddom sseq1i bitr3i cardidm cardalephex mpbii alephord ancoms breq1 cen
      wrex cardid sdomen1 ax-mp bitr3di sylan9bb breq1d sdomirr sdomen2 bitr3id
      fveq2 rspcv mtbiri nsyli com12 adantl rexlimdva2 syl5 biimtrid adantr wne
      sylbird ne0i onelon alephgeom ssdomg sylbi sylan2 domnsym syl expr r19.2z
      domtr ex syl2im rexnal imbitrdi expimpd a1d com3r mpi simprbi con3i syl56
      jaod ssrab2 oneqmini syl2an2r ) CEFZCGHZBUAZGHZAUAZIJZBCKZAEUBZFZUCCFZDUA
      ZYIFZUDZDYCKZYCYIUMLZYBYCEFZYEYCIJZBCKZMYJYBYSYQYBYRBCYDCUEUFCUGUHYHYSAYC
      EYFYCLYGYRBCYFYCYEIUIUJUKULYBYKMZYNDYCYLYCFYLYCIJZYTYEYLIJZBCKZUDZYNUUAYL
      YCNHZYCYLYCUNUUEYCCUOUPUQYTOYLPJZYLOPJZURZUUAUUDQZORFZYLRFZUUHUSDUTZOYLRR
      VAVBYTUUFUUIUUGYBUUFUUIQYKUUFOYLNHZSZYBUUIUUFONHZUUMSZUUNUUJUUKUUPUUFTUSU
      ULOYLRRVDVBUUOOUUMVCVEVFUUNUUMYFGHZLZAEVNZYBUUIUUNUUMNHUUMLUUSYLVGAUUMVHV
      IYBUURUUIAEYBYFEFZMZUURMUUAYFCFZUUDUVAUVBUUQYCIJZUURUUAUUTYBUVBUVCTYFCVJV
      KUURUUMYCIJZUVCUUAUUMUUQYCIVLUUMYLVMJZUVDUUATYLUULVOZUUMYLYCVPVQVRVSUURUV
      BUUDQUVAUVBUURUUDUVBUUCUUQYLIJZUURUUBUVGBYFCYDYFLYEUUQYLIYDYFGWDVTWEUURUV
      GUUQUUQIJZUUQWAUVGUUQUUMIJZUURUVHUVEUVIUVGTUVFUUMYLUUQWBVQUUMUUQUUQIUIWCW
      FWGWHWIWOWJWKWLWMUUGUUAYTUUDUUGYTUUDQUUAUUGYBYKUUDYKUUGYBMZUUDYKUVJUUBUDZ
      BCVNZUUDYKCUCWNZUVJUVKBCKZUVLCUCWPUVJUVKBCUUGYBYDCFZUVKYBUVOMUUGYDEFZUVKC
      YDWQUUGUVPMYLYEPJZUVKUVPUUGOYEPJZUVQUVPOYESZUVRYDWRYEEFUVSUVRQYDUGOYEEWSV
      QWTYLOYEXFXAYLYEXBXCXAXDUFUVMUVNUVLUVKBCXEXGXHUUBBCXIXJWHXKXLXMXRXNYMUUCY
      MYLEFUUCYHUUCAYLEYFYLLYGUUBBCYFYLYEIUIUJUKXOXPXQUFYIESYJYOMYPQYHAEXSDYCYI
      XTVQYA $.
  $}

  ${
    $d x y w A $.
    dominfac.1 $e |- A e. _V $.
    $( A nonempty set that is a subset of its union is infinite.  This version
       is proved from ~ ax-ac .  See ~ dominf for a version proved from
       ~ ax-cc .  (Contributed by NM, 25-Mar-2007.) $)
    dominfac $p |- ( ( A =/= (/) /\ A C_ U. A ) -> _om ~<_ A ) $=
      ( vx vy vw cv c0 wne cuni wss wa com cdom wbr wi cvv eqid csdm wn wcel id
      wceq neeq1 unieq sseq12d anbi12d breq2 imbi12d cpw cin crab cmpt crdg wf1
      cres inf3lem6 vpwex f1dom cfn pwfi biimpi isfinite 3imtr3i wb omex domtri
      con3i mp2an vex 3imtr4i 3syl vtocl ) CFZGHZVMVMIZJZKZLVMMNZOAGHZAAIZJZKZL
      AMNZOCABVMAUBZVQWBVRWCWDVNVSVPWAVMAGUCWDVMAVOVTWDUAVMAUDUEUFVMALMUGUHVQLV
      MUIZDPEFVMUJDFJEVMUKULZGUMLUOZUNLWEMNZVRCDEAAWGWFWFQWGQBBUPLWEWGCUQZURWEL
      RNZSZVMLRNZSZWHVRWLWJVMUSTZWEUSTZWLWJWNWOVMUTVAVMVBWEVBVCVGLPTZWEPTWHWKVD
      VEWILWEPPVFVHWPVMPTVRWMVDVECVILVMPPVFVHVJVKVL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Cardinal number arithmetic using Axiom of Choice
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x A $.
    $( The countable union of countable sets is countable (indexed union
       version of ~ unictb ).  (Contributed by Mario Carneiro, 18-Jan-2014.) $)
    iunctb $p |- ( ( A ~<_ _om /\ A. x e. A B ~<_ _om ) ->
                 U_ x e. A B ~<_ _om ) $=
      ( com cdom wbr wral wa ciun cxp cv csn cmap wacn wcel ctex iunexg sylancl
      cvv sylc eqid co simpl adantr ovex rgenw acncc eleqtrrdi acndom simpr cen
      omex xpdom1g sylancr xpomen domentr ccrd ralimi syl2an con0 omelon onenon
      cdm ax-mp numacn mpisyl acndom2 iundomg domtr syl2anc ) BDEFZCDEFZABGZHZA
      BCIZBDJZEFVPDEFZVODEFVNABCDABAKLCJIZVRUAVNVKABDCMUBZIZDNZOVTBNOVKVMUCZVNV
      TSWAVNBSOZVSSOZABGVTSOVKWCVMBPZUDWDABDCMUEUFABVSSSQRUGUHBDVTUITVKVMUJVNVQ
      DVONZOZVPWFOVNVPDDJZEFZWHDUKFVQVNDSOVKWIULWBBDDSUMUNUOVPWHDUPRZVNVOSOZDUQ
      VCOZWGVKWCCSOZABGWKVMWEVLWMABCPURABCSSQUSDUTOWLVADVBVDVOSDVEVFVOVPDVGTVHW
      JVOVPDVIVJ $.
  $}

  ${
    $d x A $.
    $( The countable union of countable sets is countable.  Theorem 6Q of
       [Enderton] p. 159.  See ~ iunctb for indexed union version.
       (Contributed by NM, 26-Mar-2006.) $)
    unictb $p |- ( ( A ~<_ _om /\ A. x e. A x ~<_ _om ) -> U. A ~<_ _om ) $=
      ( com cdom wbr cv wral wa cuni ciun uniiun iunctb eqbrtrid ) BCDEAFZCDEAB
      GHBIABNJCDABKABNLM $.
  $}

  ${
    $d x A $.  $d x B $.
    $( An exponentiation law for infinite cardinals.  Similar to Lemma 6.2 of
       [Jech] p. 43.  (Contributed by NM, 1-Oct-2004.)  (Proof shortened by
       Mario Carneiro, 30-Apr-2015.) $)
    infmap $p |- ( ( _om ~<_ A /\ B ~<_ A ) ->
                      ( A ^m B ) ~~ { x | ( x C_ A /\ x ~~ B ) } ) $=
      ( com cdom wbr cmap co ccrd cdm wcel cv wss cen cab cvv ovex numth3 ax-mp
      wa infmap2 mp3an3 ) DBEFCBEFBCGHZIJKZUCALZBMUECNFTAONFUCPKUDBCGQUCPRSABCU
      AUB $.
  $}

  $( The sum of two alephs is their maximum.  Equation 6.1 of [Jech] p. 42.
     (Contributed by NM, 29-Sep-2004.)  (Revised by Mario Carneiro,
     30-Apr-2015.) $)
  alephadd $p |- ( ( aleph ` A ) |_| ( aleph ` B ) ) ~~
                 ( ( aleph ` A ) u. ( aleph ` B ) ) $=
    ( con0 wcel cale cfv cdju cun cen wbr wn cvv wa wceq mp2an c0 cxp com ax-mp
    fvex djuex cdm alephfnon fndmi eleq2i notbii csn c1o df-dju xpundir 3eqtr2i
    xp0 ndmfv djueq12 syl2an adantr adantl uneq12d 3eqtr4a syl2anbr eqeng mpsyl
    un0 eqtrdi wss alephgeom cdom ssdomg ccrd alephon onenon infdju mp3an12 syl
    ex wi sylbi djucomen entr sylancr uncom breqtrdi pm2.61ii ) ACDZBCDZAEFZBEF
    ZGZWFWGHZIJZWDKZWEKZWJWHLDZWKWLMWHWINZWJWFLDZWGLDZWMAETZBETZWFWGLLUAOWKAEUB
    ZDZKZBWSDZKZWNWLWTWDWSCACEUCUDZUEUFXBWEWSCBXDUEUFXAXCMZPPGZPWHWIXFPUGZPQUHU
    GZPQHXGXHHZPQPPPUIXGXHPUJXIULUKXAWFPNZWGPNZWHXFNXCAEUMZBEUMZWFPWGPUNUOXEWIP
    PHPXEWFPWGPXAXJXCXLUPXCXKXAXMUQURPVCVDUSUTWHWILVAVBVOWDRWFVEZWJAVFXNRWFVGJZ
    WJWOXNXOVPWQRWFLVHSWFVIUBZDZWGXPDZXOWJWFCDXQAVJWFVKSZWGCDXRBVJWGVKSZWFWGVLV
    MVNVQWERWGVEZWJBVFYARWGVGJZWJWPYAYBVPWRRWGLVHSYBWHWGWFHZWIIYBWHWGWFGZIJZYDY
    CIJZWHYCIJWOWPYEWQWRWFWGLLVROXRXQYBYFXTXSWGWFVLVMWHYDYCVSVTWGWFWAWBVNVQWC
    $.

  $( The product of two alephs is their maximum.  Equation 6.1 of [Jech] p. 42.
     (Contributed by NM, 29-Sep-2004.)  (Revised by Mario Carneiro,
     30-Apr-2015.) $)
  alephmul $p |- ( ( A e. On /\ B e. On ) ->
  ( ( aleph ` A ) X. ( aleph ` B ) ) ~~ ( ( aleph ` A ) u. ( aleph ` B ) ) ) $=
    ( con0 wcel cale cfv com cdom wbr wa wss alephgeom cvv wi fvex ssdomg ax-mp
    sylbi alephon onenon ccrd cdm wne cxp cun cen jctil infn0 syl infxp syl2an
    c0 ) ACDZAEFZUAUBZDZGUNHIZJBEFZUODZURULUCZJUNURUDUNURUEUFIBCDZUMUQUPUMGUNKZ
    UQALUNMDVBUQNAEOGUNMPQRUNCDUPASUNTQUGVAUTUSVAGURKZUTBLVCGURHIZUTURMDVCVDNBE
    OGURMPQURUHUIRURCDUSBSURTQUGUNURUJUK $.

  $( An exponentiation law for alephs.  Lemma 6.1 of [Jech] p. 42.
     (Contributed by NM, 29-Sep-2004.)  (Revised by Mario Carneiro,
     30-Apr-2015.) $)
  alephexp1 $p |- ( ( ( A e. On /\ B e. On ) /\ A C_ B ) ->
             ( ( aleph ` A ) ^m ( aleph ` B ) ) ~~ ( 2o ^m ( aleph ` B ) ) ) $=
    ( con0 wcel wa wss cale cfv cmap cen wbr c2o com cdom cvv fvex sylib ssdomg
    co ax-mp cpw ccrd cdm alephon onenon mp1i simplr alephgeom mpsyl word ordom
    2onn ordelss mp2an simpll sstrid alephord3 biimtrdi imp csdm canth2 sdomdom
    wi domtr sylancl mappwen syl22anc wb pw2en enen2 ) ACDZBCDZEZABFZEZAGHZBGHZ
    ISZVQUAZJKZVRLVQISZJKZVOVQUBUCDZMVQNKZLVPNKZVPVSNKZVTVQCDWCVOBUDVQUEUFVQODZ
    VOMVQFZWDBGPZVOVLWHVKVLVNUGBUHQMVQORUIVPODVOLVPFWEAGPVOLMVPMUJLMDLMFUKULMLU
    MUNVOVKMVPFVKVLVNUOAUHQUPLVPORUIVOVPVQNKZVQVSNKZWFVMVNWJVMVNVPVQFZWJABUQWGW
    LWJVCWIVPVQORTURUSVQVSUTKWKVQWIVAVQVSVBTVPVQVSVDVEVPVQVFVGVSWAJKVTWBVHVQWIV
    IVSWAVRVJTQ $.

  ${
    $d x A $.
    $( An alternate representation of a successor aleph.  Compare ~ alephsuc
       and ~ alephsuc2 .  Equality can be obtained by taking the ` card ` of
       the right-hand side then using ~ alephcard and ~ carden .  (Contributed
       by NM, 23-Oct-2004.) $)
    alephsuc3 $p |- ( A e. On ->
                     ( aleph ` suc A ) ~~ { x e. On | x ~~ ( aleph ` A ) } ) $=
      ( con0 wcel cale cfv cen wbr crab cdif cdom csdm wceq ccrd alephon onenon
      cv ax-mp com cvv csuc alephsuc2 alephcard cdm cardval2 eqtr3i difeq12d wn
      a1i wa difrab bren2 rabbii eqtr4i eqtr2di mp1i wss onsucb alephgeom bitri
      wi fvex ssdomg sylbi alephordilem1 infdif syl3anc eqbrtrd ensymd ) BCDZAQ
      ZBEFZGHZACIZBUAZEFZVJVNVPVLJZVPGVJVQVKVLKHZACIZVKVLLHZACIZJZVNVJVPVSVLWAA
      BUBVLWAMVJVLNFZVLWABUCVLNUDZDZWCWAMVLCDWEBOVLPRAVLUERUFUIUGWBVRVTUHUJZACI
      VNVRVTACUKVMWFACVKVLULUMUNUOVJVPWDDZSVPKHZVLVPLHVQVPGHVPCDWGVJVOOVPPUPVJS
      VPUQZWHVJVOCDWIBURVOUSUTVPTDWIWHVAVOEVBSVPTVCRVDBVEVPVLVFVGVHVI $.

    $( An expression equinumerous to 2 to an aleph power.  The proof equates
       the two laws for cardinal exponentiation ~ alephexp1 (which works if the
       base is less than or equal to the exponent) and ~ infmap (which works if
       the exponent is less than or equal to the base).  They can be equated
       only when the base is equal to the exponent, and this is the result.
       (Contributed by NM, 23-Oct-2004.) $)
    alephexp2 $p |- ( A e. On -> ( 2o ^m ( aleph ` A ) ) ~~
                      { x | ( x C_ ( aleph ` A ) /\ x ~~ ( aleph ` A ) ) } ) $=
      ( con0 wcel cale cfv cmap co cv wss cen wbr wa cab c2o com cdom cvv ax-mp
      sylancl alephgeom wi fvex ssdomg sylbi domrefg wb pm3.2 pm2.43i alephexp1
      infmap ssid enen1 syl mpbid ) BCDZBEFZUQGHZAIZUQJUSUQKLMANZKLZOUQGHZUTKLZ
      UPPUQQLZUQUQQLZVAUPPUQJZVDBUAUQRDZVFVDUBBEUCZPUQRUDSUEVGVEVHUQRUFSAUQUQUK
      TUPURVBKLZVAVCUGUPUPUPMZBBJVIUPVJUPUPUHUIBULBBUJTURVBUTUMUNUO $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Cofinality using the Axiom of Choice
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A f x y $.  $d A f y z $.
    $( A successor aleph is regular.  Theorem 11.15 of [TakeutiZaring] p. 103.
       (Contributed by Mario Carneiro, 9-Mar-2013.) $)
    alephreg $p |- ( cf ` ( aleph ` suc A ) ) = ( aleph ` suc A ) $=
      ( vf vx vy vz con0 wcel cale cfv ccf csdm wbr wa cdom cv wss wral syl2anc
      cvv c0 csuc wceq wn alephordilem1 cxp wf1 wrex wex alephon cff1 ciun fvex
      ax-mp sucex iunex wf f1f ad2antrr simplr wb oneli ffvelcdm onelon sylancr
      onsssuc sylan2 anassrs rexbidva eliun ancoms ralbidva dfss3 biimpa ssdomg
      bitr4di mpsyl simprl onsuc wlim alephislim sylbi syl breq1 ccrd alephcard
      limsuc iscard simprbi vtoclri alephsucdom imbitrrid syl5 expdimp ralrimiv
      sylbid iundom domtr expcom exlimdv mpi cen com alephgeom mpan xpdom1 syl6
      infxpen domentr sylsyld domnsym ex mt2d wo cfon cfle onsseleq mpbii mp2an
      imp ori cf0 cdm alephfnon fndmi eleq2i onsucb bitr4i ndmfv sylnbir fveq2d
      3eqtr4a pm2.61i ) AFGZAUAZHIZJIZYOUBZYMYPYOGZUCYQYMYRAHIZYOKLZAUDYMYRYTUC
      ZYMYRMZYOYSNLZUUAUUBYOYPYSUEZNLZUUDYSNLZUUCUUBYPYOBOZUFZCOZDOZUUGIZPZDYPU
      GZCYOQZMZBUHZUUEYOFGZUUPYNUIZCDYOBUJUMUUBUUOUUEBUUOUUBUUEUUOUUBMZYODYPUUK
      UAZUKZNLZUVAUUDNLZUUEUVASGUUSYOUVAPZUVBDYPUUTYOJULZUUKUUJUUGULUNUOUUSYPYO
      UUGUPZUUNUVDUUHUVFUUNUUBYPYOUUGUQURZUUHUUNUUBUSUVFUUNUVDUVFUUNUUIUVAGZCYO
      QUVDUVFUUMUVHCYOUUIYOGUVFUUIFGZUUMUVHUTZYOUUIUURVAUVIUVFUVJUVIUVFMZUUMUUI
      UUTGZDYPUGUVHUVKUULUVLDYPUVIUVFUUJYPGZUULUVLUTZUVFUVMMZUVIUUKFGZUVNUVOUUQ
      UUKYOGZUVPUURYPYOUUJUUGVBZYOUUKVCVDUUIUUKVEVFVGVHDUUIYPUUTVIVOVJVFVKCYOUV
      AVLVOVMRYOUVASVNVPUUSYMUVFUVCUUOYMYRVQUVGYMUVFMZYPSGUUTYSNLZDYPQUVCUVEUVS
      UVTDYPYMUVFUVMUVTUVOUVQYMUVTUVRYMUVQUUTYOGZUVTYMYNFGZUVQUWAUTZAVRUWBYOVSU
      WCYNVTYOUUKWFWAWBUWAUVTYMUUTYOKLZEOZYOKLZUWDEUUTYOUWEUUTYOKWCYOWDIYOUBZUW
      FEYOQZYNWEUWGUUQUWHEYOWGWHUMZWIUUTAWJWKWOWLWMWNDYPYSUUTSWPVDRYOUVAUUDWQRW
      RWSWTYMYRUUFYMYSYSUEZYSXALZYRUUDUWJNLZUUFYMXBYSPZUWKAXCYSFGUWMUWKAUIYSXGX
      DWAYMYRYPYSNLZUWLYRUWNYMYPYOKLZUWFUWOEYPYOUWEYPYOKWCUWIWIYPAWJWKYPYSYSAHU
      LXEXFUWLUWKUUFUUDUWJYSXHWRXIXSYOUUDYSWQRYOYSXJWBXKXLYRYQYPFGZUUQYRYQXMZYO
      XNUURUWPUUQMYPYOPUWQYOXOYPYOXPXQXRXTWBYMUCZTJITYPYOYAUWRYOTJYMYNHYBZGZYOT
      UBUWTUWBYMUWSFYNFHYCYDYEAYFYGYNHYHYIZYJUXAYKYL $.
  $}

  ${
    $d A f w y z $.  $d A f x y $.  $d H x $.
    pwcfsdom.1 $e |- H = ( y e. ( cf ` ( aleph ` A ) ) |->
       ( har ` ( f ` y ) ) ) $.
    $( A corollary of Konig's Theorem ~ konigth .  Theorem 11.28 of
       [TakeutiZaring] p. 108.  (Contributed by Mario Carneiro,
       20-Mar-2013.) $)
    pwcfsdom $p |- ( aleph ` A ) ~<
       ( ( aleph ` A ) ^m ( cf ` ( aleph ` A ) ) ) $=
      ( vx con0 wcel cale cfv ccf csdm wbr c0 wceq cvv wa com c2o wss cmap csuc
      vz vw co cv wrex wlim w3o onzsl biimpi aleph0 fveq2i 3eqtr4i 2fveq3 fveq2
      cfom 3eqtr4a cdom cpw cen fvex canth2 pw2en sdomentr mp2an alephon omelon
      alephgeom 2onn onelss mp2 sstr mpan sylbi mpsyl mapdom1 sdomdomtr sylancr
      ssdomg syl oveq2 breq2d syl5ibrcom syl5 alephreg rexlimivw wi wf wsmo w3a
      wral cixp limelon ciun crn cuni cab wfn ffn fnrnfv unieqd dfiun2 ad2antrl
      eqtr4di fnfvelrn sylan rspcev rexlimdva2 ralimdv imp adantl wb alephislim
      sseq2 adantr coflim syl2an mpbird eqtr3d char ffvelcdm oneli ccrd harcard
      iscard simprbi ax-mp domrefg elharval mpan2 3syl ralrimiva eqid eleq2i wn
      frn cmpt c1o eqtrdi biimpri breq1 rspccv harcl fvmptg konigth eqbrtrrd ex
      alephlim eleq2d eliun alephcard cardsdomelir sylbir domnsym ontri1 sylibr
      ovex con2i alephord2i ontr2 syl2anr biimtrid sylbid sylan9r cbvmptv eqtri
      fmptd ss2ixp ixpconst sseqtrdi adantrr syl2anc 3adant2 wex cfsmo exlimiiv
      expcom a1i 3jaod mpd cdm alephfnon fndmi ndmfv wne 1n0 0sdom mpbir id cf0
      1oex oveq12d 0ex map0e breq12d mpbiri sylnbir pm2.61i ) BGHZBIJZUXAUXAKJZ
      UAUEZLMZUWTBNOZBFUFZUBZOZFGUGZBPHBUHQZUIZUXDUWTUXKFBUJUKUWTUXEUXDUXIUXJUX
      EUXBUXAOZUWTUXDUXENIJZKJZUXMUXBUXARKJRUXNUXMUQUXMRKULUMULUNBNKIUOBNIUPURU
      WTUXDUXLUXAUXAUXAUAUEZLMZUWTUXASUXAUAUEZLMZUXQUXOUSMZUXPUXAUXAUTZLMUXTUXQ
      VAMUXRUXABIVBZVCUXAUYAVDUXAUXTUXQVEVFUWTSUXAUSMZUXSUXAGHZUWTSUXATZUYBBVGZ
      UWTRUXATZUYDBVISRTZUYFUYDRGHSRHUYGVHVJRSVKVLSRUXAVMVNVOSUXAGVTVPSUXAUXAVQ
      WAUXAUXQUXOVRVSUXLUXCUXOUXALUXBUXAUXAUAWBWCWDZWEUXIUXLUWTUXDUXHUXLFGUXHUX
      GIJZKJUYIUXBUXAUXFWFBUXGKIUOBUXGIUPURWGUYHWEUXJUXDWHZUWTUXBUXACUFZWIZUYKW
      JZUCUFZUDUFZUYKJZTZUDUXBUGZUCUXAWLZWKZUYJCUYLUYSUYJUYMUXJUYLUYSQZUXDUXJVU
      AQUXAFUXBUXFDJZWMZLMZVUCUXCUSMZUXDUXJUWTVUAVUDBPWNZUWTVUAQZFUXBUXFUYKJZWO
      ZUXAVUCLVUGUYKWPZWQZVUIUXAUYLVUKVUIOUWTUYSUYLVUKAUFZVUHOFUXBUGAWRZWQZVUIU
      YLUYKUXBWSZVUKVUNOUXBUXAUYKWTZVUOVUJVUMFAUXBUYKXAXBWAFAUXBVUHUXFUYKVBZXCX
      EXDVUGVUKUXAOZUYNVULTZAVUJUGZUCUXAWLZVUAVVAUWTUYLUYSVVAUYLUYRVUTUCUXAUYLU
      YQVUTUDUXBUYLUYOUXBHZQUYPVUJHZUYQVUTUYLVUOVVBVVCVUPUXBUYOUYKXFXGVUSUYQAUY
      PVUJVULUYPUYNXOXHXGXIXJXKXLUWTUXAUHZVUJUXATZVURVVAXMVUAUWTVVDBXNUKUYLVVEU
      YSUXBUXAUYKYQXPUCAUXAVUJXQXRXSXTUYLVUIVUCLMZUWTUYSUYLVUHVUBLMZFUXBWLVVFUY
      LVVGFUXBUYLUXFUXBHZQZVVGVUHVUHYAJZLMZVVIVUHUXAHZVUHGHZVVKUXBUXAUXFUYKYBZU
      XAVUHUYEYCVULVVJLMZAVVJWLZVVMVUHVVJHZVVKVVJYDJVVJOZVVPVUHYEVVRVVJGHZVVPAV
      VJYFYGYHVVMVUHVUHUSMZVVQVUHPHVVTVUQVUHPYIYHVVQVVMVVTQVUHVUHYJUUAYKVVOVVKA
      VUHVVJVULVUHVVJLUUBUUCVPYLVVHVVGVVKXMUYLVVHVUBVVJVUHLVVHVVSVUBVVJOVUHUUDZ
      AUXFVULUYKJYAJZVVJUXBGDVULUXFYAUYKUOZEUUEYKWCXLXSYMUXBVUCVUIFUYKDUXAKVBZV
      UIYNVUCYNUUFWAXDUUGXGUXJUYLVUEUYSUXCPHUXJUYLQZVUCUXCTZVUEUXAUXBUAUURVWEUX
      BUXADWIZVUBUXATZFUXBWLZVWFVWEFUXBVVJUXADVWEVVHVVJUXAHZUYLVVHVVLUXJVWJUYLV
      VHVVLVVNUUHUXJVVLVUHABVULIJZWOZHZVWJUXJUXAVWLVUHABPUUIUUJUXJUWTVWMVWJWHVU
      FVWMVUHVWKHZABUGUWTVWJAVUHBVWKUUKUWTVWNVWJABVWNVVJVWKTZVWKUXAHZVWJUWTVULB
      HZQVWNVUHVWKLMZVWOVWNVUHVWKYDJZHVWRVWSVWKVUHVULUULYOVUHVWKUUMUUNVWRVWKVVJ
      HZYPZVWOVWTVWRVWTVWKVUHUSMZVWRYPVWTVWKGHZVXBVUHVWKYJYGVWKVUHUUOWAUUSVVSVX
      CVWOVXAXMVWAVULVGVVJVWKUUPVFUUQWAUWTVWQVWPVULBUUTXKVVSUYCVWOVWPQVWJWHVWAU
      YEVVJVWKUXAUVAVFUVBXIUVCWAUVDUVEXKDAUXBVWBYRFUXBVVJYREAFUXBVWBVVJVWCUVFUV
      GUVHVWGVWHFUXBUYCVWGVVHQVUBUXAHVWHUYEUXBUXAUXFDYBUXAVUBVKVPYMVWIVUCFUXBUX
      AWMUXCFUXBVUBUXAUVIFUXBUXAVWDUYAUVJUVKYLVUCUXCPVTVPUVLUXAVUCUXCVRUVMUVRUV
      NUYCUYTCUVOUYEUCUDUXACUVPYHUVQUVSUVTUWAUWTBIUWBZHZUXDVXDGBGIUWCUWDYOVXEYP
      UXANOZUXDBIUWEVXFUXDNYSLMZVXGYSNUWFUWGYSUWLUWHUWIVXFUXANUXCYSLVXFUWJZVXFU
      XCNNUAUEZYSVXFUXANUXBNUAVXHVXFUXBNKJNUXANKUPUWKYTUWMNPHVXIYSOUWNNPUWOYHYT
      UWPUWQWAUWRUWS $.
  $}

  ${
    $d x y z A $.  $d x B $.
    cfpwsdom.1 $e |- B e. _V $.
    $( A corollary of Konig's Theorem ~ konigth .  Theorem 11.29 of
       [TakeutiZaring] p. 108.  (Contributed by Mario Carneiro,
       20-Mar-2013.) $)
    cfpwsdom $p |- ( 2o ~<_ B ->
        ( aleph ` A ) ~< ( cf ` ( card ` ( B ^m ( aleph ` A ) ) ) ) ) $=
      ( con0 wcel cdom wbr cale cfv cmap co ccf csdm cen wceq com cvv ax-mp c1o
      c0 vx vy vz c2o ccrd wi wa cxp ovex cardid ensymi cv wrex crn wn cpw fvex
      canth2 pw2en sdomentr mapdom1 sdomdomtr sylancr cfn wb ficard fict sylbir
      mp2an wss alephgeom alephon ssdomg sylbi domtr syl2an domnsym syl cardidm
      expcom con2d cun wo iscard3 elun df-or 3bitri syl56 wfn alephfnon fvelrnb
      mpbi imbitrdi char cmpt pwcfsdom id fveq2 oveq12d breq12d mpbii rexlimivw
      eqid syl6 ensdomtr enref mapen mapxpen mp3an entri sylancl xpdom2 infxpen
      imp biimpi domentr csuc nsuceq0 nemtbir df-2o breq1i breq2 bitrid biimpcd
      dom0 adantld mtoi mapdom2 expl com12 mt2d domtri biimpri nsyl2 cdm eleq2i
      ex fndm eqtrdi fveq2d ndmfv sylnbir wne 1oex 0sdom mpbir oveq2 map0e 1onn
      1n0 cardnn df-1o fveq2i 0elon cfsuc eqtri mpbiri a1d pm2.61i ) ADEZUDBFGZ
      AHIZBUVBJKZUEIZLIZMGZUFZUUTUVAUVFUUTUVAUGZUVEUVBFGZUVFUVHUVIUVCBUVBUVEUHZ
      JKZMGZUVHUVCUVDUVEJKZMGZUVMUVKNGUVLUVHUVCUVDNGUVDUVMMGZUVNUVDUVCUVCBUVBJU
      IZUJZUKUUTUVAUVOUUTUVAUAULZHIZUVDOZUADUMZUVOUUTUVAUVDHUNZEZUWAUVAUVBUVCMG
      ZUUTUVDPEZUOZUWCUVAUVBUDUVBJKZMGZUWGUVCFGUWDUVBUVBUPZMGUWIUWGNGUWHUVBAHUQ
      ZURUVBUWJUSUVBUWIUWGUTVIUDBUVBVAUVBUWGUVCVBVCUUTUWEUWDUWEUUTUWDUOZUWEUUTU
      GUVCUVBFGZUWKUWEUVCPFGZPUVBFGZUWLUUTUWEUVCVDEZUWMUVCQEUWOUWEVEUVPUVCQVFRU
      VCVGVHUUTPUVBVJZUWNAVKZUVBDEZUWPUWNUFAVLZPUVBDVMRVNUVCPUVBVOVPUVCUVBVQVRV
      TWAUVDUEIUVDOZUWFUWCUFZUVCVSUWTUVDPUWBWBEUWEUWCWCUXAUVDWDUVDPUWBWEUWEUWCW
      FWGWLWHHDWIZUWCUWAVEWJUADUVDHWKRWMUVTUVOUADUVTUVSUVSUVSLIZJKZMGUVOUBUVRUC
      UBUXCUBULUCULIWNIWOZUXEXCWPUVTUVSUVDUXDUVMMUVTWQZUVTUVSUVDUXCUVEJUXFUVSUV
      DLWRWSWTXAXBXDXNUVCUVDUVMXEVCUVMUVCUVEJKZUVKUVDUVCNGUVEUVENGUVMUXGNGUVQUV
      EUVDLUQZXFUVDUVCUVEUVEXGVIBQEZUWRUVEQEZUXGUVKNGCUWSUXHBUVBUVEQDQXHXIXJUVC
      UVMUVKUTXKUVIUVHUVLUOZUVIUUTUVAUXKUVIUUTUGZUVAUGUVKUVCFGZUXKUXLUVJUVBFGZU
      VJTOZBTOZUGZUOUXMUVAUVIUVJUVBUVBUHZFGUXRUVBNGZUXNUUTUVEUVBUVBUWJXLUUTUWRU
      WPUXSUWSUUTUWPUWQXOUVBXMVCUVJUXRUVBXPVPUVAUXQSXQZTFGZUYAUXTTSXRUXTYEXSUVA
      UXPUYAUXOUXPUVAUYAUVAUXTBFGUXPUYAUDUXTBFXTYABTUXTFYBYCYDYFYGUVJUVBBYHVPUV
      KUVCVQVRYIYJYKUVIUVFUOZUXJUVBQEUVIUYBVEUXHUWJUVEUVBQQYLVIYMYNYQUUTUOUVBTO
      ZUVGUUTAHYOZEUYCUYDDAUXBUYDDOWJDHYRRYPAHUUAUUBUYCUVFUVAUYCUVFTSMGZUYESTUU
      CUUJSUUDUUEUUFUYCUVBTUVESMUYCWQUYCUVESLIZSUYCUVDSLUYCUVDSUEIZSUYCUVCSUEUY
      CUVCBTJKZSUVBTBJUUGUXIUYHSOCBQUUHRYSYTSPEUYGSOUUISUUKRYSYTUYFTXQZLIZSSUYI
      LUULUUMTDEUYJSOUUNTUUORUUPYSWTUUQUURVRUUS $.
  $}

  $( From ~ canth2 , we know that ` ( aleph `` 0 ) < ( 2 ^ _om ) ` , but we
     cannot prove that ` ( 2 ^ _om ) = ( aleph `` 1 ) ` (this is the Continuum
     Hypothesis), nor can we prove that it is less than any bound whatsoever
     (i.e. the statement ` ( aleph `` A ) < ( 2 ^ _om ) ` is consistent for any
     ordinal ` A ` ).  However, we can prove that ` ( 2 ^ _om ) ` is not equal
     to ` ( aleph `` _om ) ` , nor ` ( aleph `` ( aleph `` _om ) ) ` , on
     cofinality grounds, because by Konig's Theorem ~ konigth (in the form of
     ~ cfpwsdom ), ` ( 2 ^ _om ) ` has uncountable cofinality, which eliminates
     limit alephs like ` ( aleph `` _om ) ` .  (The first limit aleph that is
     _not_ eliminated is ` ( aleph `` ( aleph `` 1 ) ) ` , which has cofinality
     ` ( aleph `` 1 ) ` .)  (Contributed by Mario Carneiro, 21-Mar-2013.) $)
  alephom $p |- ( card ` ( 2o ^m _om ) ) =/= ( aleph ` _om ) $=
    ( com csdm wbr wn c2o cmap ccrd cfv cale wne sdomirr wceq ccf cvv wcel cdom
    co c0 aleph0 ax-mp 2onn elexi domrefg cfpwsdom oveq2i fveq2i eqeq1i biimpri
    mp2b fveq2d wlim limom alephsing cfom eqtri eqtrdi breq12d mpbii necon3bi
    a1i ) AABCZDEAFQZGHZAIHZJAKVAVCVDVCVDLZRIHZEVFFQZGHZMHZBCZVAENOEEPCVJEAUAUB
    ZENUCREVKUDUIVEVFAVIABVFALVESUTVEVIVDMHZAVEVHVDMVHVDLVEVHVCVDVGVBGVFAEFSUEU
    FUGUHUJVLAMHZAAUKVLVMLULAUMTUNUOUPUQURUST $.

  ${
    $d x y $.
    $( The beth function is strictly monotone.  This function is not strictly
       the beth function, but rather beth_A is the same as
       ` ( card `` ( R1 `` ( _om +o A ) ) ) ` , since conventionally we start
       counting at the first infinite level, and ignore the finite levels.
       (Contributed by Mario Carneiro, 6-Jun-2013.)  (Revised by Mario
       Carneiro, 2-Jun-2015.) $)
    smobeth $p |- Smo ( card o. R1 ) $=
      ( vy vx ccrd cr1 cdm con0 wfn crn wss wfun ax-mp r1fnon mpbi cep wcel cfv
      wf wa wb sylan ccom ccnv cima cv cen wbr wrex cab cardf2 ffun fnfun funco
      mp2an funfn cres rnco resss rnssi frn sstri df-f mpbir2an dmco feq2i word
      eqsstri wtr wwe elpreima simplbi onelon simprbi adantr r1ord2 imp syl2anc
      wral ssnum sylanbrc rgen2 dftr5 mpbir cnvimass cvv dffn2 fdmi epweon wess
      sseqtri df-ord wi csdm r1sdom cardsdom2 mpbird wceq fvco2 sylancr 3eltr4d
      mp2 ex adantl issmo ) ABCDUAZDUBCEZUCZXDEZFXDQZXFFXDQXHXDXGGZXDHZFIXDJZXI
      CJZDJZXKAUDZBUDZUEUFAFUGBUHZFCQZXLBAUIZXPFCUJKDFGZXMLFDUKKCDULUMXDUNMXJCD
      HZUOZHZFCDUPYBCHZFYACCXTUQURXQYCFIXRXPFCUSKUTVFXGFXDVAVBXGXFFXDCDVCZVDMXF
      VEXFVGZXFNVHZYEXNXFOZAXOVQBXFVQYGBAXFXOXOXFOZXNXOOZRZXNFOZXNDPZXEOZYGYHXO
      FOZYIYKYHYNXODPZXEOZXSYHYNYPRSLFXOXEDVIKZVJZXOXNVKTZYJYPYLYOIZYMYHYPYIYHY
      NYPYQVLVMZYHYNYIYTYRYNYIYTXNXOVNVOTYOYLVRVPZXSYGYKYMRSLFXNXEDVIKVSVTBAXFW
      AWBXFFIFNVHYFXFDEFDXEWCFWDDXSFWDDQLFDWEMWFWIWGXFFNWHWTXFWJVBYHYIXNXDPZXOX
      DPZOZWKYGYHYIUUEYJYLCPZYOCPZUUCUUDYJUUFUUGOZYLYOWLUFZYHYNYIUUIYRXOXNWMTYJ
      YMYPUUHUUISUUBUUAYLYOWNVPWOYJXSYKUUCUUFWPLYSFCDXNWQWRYJXSYNUUDUUGWPLYHYNY
      IYRVMFCDXOWQWRWSXAXBYDXC $.
  $}

$( I decided to comment out the Card class for now.  We have too many
   definitions, and this one doesn't really buy us much. $)

$(
  @c Card @. @( Class of all cardinal numbers @)

  @( Extend class definition to include the class of all cardinal numbers. @)
  ccdn @a class Card @.

  @( Define the class of all cardinal numbers.  The notation "Card" is used
     in Exercise 5(G) of [JustWeese] p. 174.  It should not be confused with
     the lowercase "card" for the cardinal number function ~ df-card .  @)
  df-cardn @a |- Card = ( _om u. ran aleph ) @.

  @( Membership in the class of cardinal numbers. @)
  elcard @p |- ( A e. Card <-> ( card ` A ) = A ) @=
    ( ccdn wcel com cale crn cun ccrd cfv wceq df-cardn eleq2i iscard3 bitr4i )
    ABCADEFGZCAHIAJBOAKLAMN @.
    @( [31-Dec-2004] @) @( [23-Sep-2004] @)

  @( The cardinality of a set is a cardinal number. @)
  cardel @p |- ( card ` A ) e. Card @=
    ( ccrd cfv ccdn wcel wceq cardidm elcard mpbir ) ABCZDEJBCJFAGJHI @.
    @( [16-Jan-2005] @) @( [23-Sep-2004] @)

  @( A natural number is a cardinal number. @)
  nncard @p |- ( A e. _om -> A e. Card ) @=
    ( com wcel ccrd cfv wceq ccdn cardnn elcard sylibr ) ABCADEAFAGCAHAIJ @.
    @( [16-Jan-2005] @) @( [23-Sep-2004] @)

  @( An alternate definition of the class of all cardinal numbers. @)
  cardnum2 @p |- Card = { x | ( card ` x ) = x } @=
    ( ccdn com cale crn cun cv ccrd cfv wceq cab df-cardn wcel iscard3 bicomi
    eqabi eqcomi eqtr4i ) BCDEFZAGZHITJZAKZLSUBUAASUATSMTNOPQR @.
    @( [25-Jan-2005] @) @( [23-Sep-2004] @)

  @( The class of cardinal numbers is a proper class.  Exercise 5(G)(b) of
     [JustWeese] p. 174. @)
  cardnprc @p |- -. Card e. _V @=
    ( vx ccdn cvv wcel cv ccrd cfv wceq cab cardprc cardnum2 eleq1i mtbir ) BCD
    AEZFGNHAIZCDAJBOCAKLM @.
    @( [25-Jan-2005] @) @( [23-Sep-2004] @)

  @( The class of transfinite cardinals (the range of the aleph function) is a
     proper class. @)
  alephprc2 @p |- -. ran aleph e. _V @=
    ( cale crn cvv wcel com cun ccdn cardnprc df-cardn eleq1i mtbi omex wa
    unexb biimpi mpan mto ) ABZCDZERFZCDZGCDUAHGTCIJKECDZSUALUBSMUAERNOPQ @.
    @( [19-Feb-2005] @) @( [23-Sep-2004] @)
$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  ZFC Axioms with no distinct variable requirements
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( A lemma for proving conditionless ZFC axioms.  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  (Contributed by NM,
     1-Jan-2002.)  (New usage is discouraged.) $)
  nd1 $p |- ( A. x x = y -> -. A. x y e. z ) $=
    ( weq wal wel elirrv wsb stdpc4 nfnth elequ1 sbie sylib mto axc11 mtoi ) AB
    DAEBCFZAEQBEZRCCFZCGZRQBCHSQBCIQSBCSBTJBCCKLMNQABOP $.

  $( A lemma for proving conditionless ZFC axioms.  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  (Contributed by NM,
     1-Jan-2002.)  (New usage is discouraged.) $)
  nd2 $p |- ( A. x x = y -> -. A. x z e. y ) $=
    ( weq wal wel elirrv wsb stdpc4 nfnth elequ2 sbie sylib mto axc11 mtoi ) AB
    DAECBFZAEQBEZRCCFZCGZRQBCHSQBCIQSBCSBTJBCCKLMNQABOP $.

  $( A lemma for proving conditionless ZFC axioms.  (Contributed by NM,
     2-Jan-2002.) $)
  nd3 $p |- ( A. x x = y -> -. A. z x e. y ) $=
    ( weq wal wel wn elirrv elequ2 mtbii sps sp nsyl ) ABDZAEABFZOCENOGANAAFOAH
    ABAIJKOCLM $.

  $( A lemma for proving conditionless ZFC axioms.  Usage of this theorem is
     discouraged because it depends on ~ ax-13 .  (Contributed by NM,
     2-Jan-2002.)  (New usage is discouraged.) $)
  nd4 $p |- ( A. x x = y -> -. A. z y e. x ) $=
    ( wel wal wn nd3 aecoms ) BADCEFBABACGH $.

  ${
    $d x w $.  $d y w $.  $d z w $.
    $( A version of the Axiom of Extensionality with no distinct variable
       conditions.  Usage of this theorem is discouraged because it depends on
       ~ ax-13 .  (Contributed by NM, 14-Aug-2003.)
       (New usage is discouraged.) $)
    axextnd $p |- E. x ( ( x e. y <-> x e. z ) -> y = z ) $=
      ( vw wel wb weq wal wex wi wn nfnae wnfc nfcvf nfcrd elequ1 syl6 ax6e ax7
      cv wa nfan adantr adantl nfbid bibi12d a1i cbvald biimtrrdi 19.8a aleximi
      axextg ex mpi a1d equcomi pm2.61ii 19.35ri ) ABEZACEZFZBCGZAABGZAHZACGZAH
      ZVAAHZVBAIZJZVDKZVFKZVIVJVKUAZVGVBVHVLVGDBEZDCEZFZDHVBVLVOVADAVJVKAABALAC
      ALUBVLVMVNAVLADBTZVJAVPMVKABNUCOVLADCTZVKAVQMVJACNUDOUEDAGZVOVAFJVLVRVMUS
      VNUTDABPDACPUFUGUHBCDULUIVBAUJQUMVDVHVGVDVEAIVHACRVCVEVBAABCSUKUNUOVFVHVG
      VFVCAIVHABRVEVCVBAVEVCCBGVBACBSCBUPQUKUNUOUQUR $.
  $}

  ${
    $d x z w $.  $d x y w $.  $d w ph $.
    $( Lemma for the Axiom of Replacement with no distinct variable conditions.
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 2-Jan-2002.)  (New usage is discouraged.) $)
    axrepndlem1 $p |- ( -. A. y y = z -> E. x ( E. y A. z ( ph -> z = y ) ->
                 A. z ( z e. x <-> E. x ( x e. y /\ A. y ph ) ) ) ) $=
      ( vw weq wal wn wi wex wel wa wb nfnae a1i cv imbi12d cbvald exbid adantl
      wsb axrep2 wnf nfs1v nfcvd nfcvf2 nfeqd nfimd sbequ12r equequ1 nfvd nfcrd
      nfald nfand nfexd nfbid elequ1 nfeqf2 nfan1 albid anbi2d bibi12d ex mpbii
      exbidv ) CDFCGHZADEUAZECFZIZEGZCJZEBKZBCKZVGCGZLZBJZMZEGZIZBJADCFZIZDGZCJ
      ZDBKZVMACGZLZBJZMZDGZIZBJVGBCEUBVFVSWJBCDBNZVFVKWCVRWIVFVJWBCCDCNZVFVIWAE
      DCDDNZVFVGVHDVGDUCVFADEUDOZVFDEPZCPZVFDWOUECDUFZUGUHEDFZVIWAMIVFWRVGAVHVT
      AEDUIZEDCUJQORSVFVQWHEDWMVFVLVPDVFVLDUKVFVODBWKVFVMVNDVFDBWPWQULVFVGDCWLW
      NUMUNUOUPVFWRVQWHMVFWRLZVLWDVPWGWRVLWDMVFEDBUQTWTVOWFBWTVNWEVMWTVGACVFWRC
      WLCDEURUSWRVGAMVFWSTUTVAVEVBVCRQSVD $.
  $}

  ${
    $d x w $.  $d y w $.  $d z w $.  $d w ph $.
    $( Lemma for the Axiom of Replacement with no distinct variable conditions.
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 2-Jan-2002.)  (Proof shortened by Mario Carneiro,
       6-Dec-2016.)  (New usage is discouraged.) $)
    axrepndlem2 $p |- ( ( ( -. A. x x = y /\ -. A. x x = z ) /\ -. A. y y = z )
                 -> E. x ( E. y A. z ( ph -> z = y ) ->
                     A. z ( z e. x <-> E. x ( x e. y /\ A. y ph ) ) ) ) $=
      ( vw weq wal wn wa wi wex wel wb nfnae nfan cv wnfc adantl adantr nfeqd
      wsb axrepndlem1 wnf nfs1v nfcvf nfimd nfald nfexd nfcvd nfeld nfand nfbid
      a1i nfv nfcvf2 nfan1 sbequ12r imbi1d albid exbid elequ2 elequ1 anbi12d ex
      cbvexd bibi12d imbi12d imbitrid imp ) BCFBGHZBDFBGHZIZCDFCGHZADCFZJZDGZCK
      ZDBLZBCLZACGZIZBKZMZDGZJZBKZVMABEUAZVNJZDGZCKZDELZECLZWGCGZIZEKZMZDGZJZEK
      VLWFWGECDUBVLWRWEEBVJVKBBCBNBDBNOZVLWJWQBVLWIBCVJVKCBCCNBDCNOZVLWHBDVJVKD
      BCDNBDDNOZVLWGVNBWGBUCVLABEUDUMZVLBDPZCPZVKBXCQVJBDUERZVJBXDQVKBCUESZTUFU
      GUHVLWPBDXAVLWKWOBVLBXCEPZXEVLBXGUIZUJVLWNBEVLEUNVLWLWMBVLBXGXDXHXFUJVLWG
      BCWTXBUGUKZUHULUGUFVLEBFZWRWEMVLXJIZWJVQWQWDXKWIVPCVLXJCWTVLCXGBPZVLCXGUI
      VJCXLQVKBCUOSTUPZXKWHVODVLXJDXAVLDXGXLVLDXGUIVKDXLQVJBDUORTUPZXJWHVOMVLXJ
      WGAVNAEBUQZURRUSUTXKWPWCDXNXKWKVRWOWBXJWKVRMVLEBDVARVLWOWBMXJVLWNWAEBWSXI
      VLXJWNWAMXKWLVSWMVTXJWLVSMVLEBCVBRXKWGACXMXJWGAMVLXORUSVCVDVESVFUSVGVDVEV
      HVI $.
  $}

  $( A version of the Axiom of Replacement with no distinct variable
     conditions.  Usage of this theorem is discouraged because it depends on
     ~ ax-13 .  (Contributed by NM, 2-Jan-2002.)
     (New usage is discouraged.) $)
  axrepnd $p |- E. x ( E. y A. z ( ph -> z = y ) ->
               A. z ( A. y z e. x <-> E. x ( A. z x e. y /\ A. y ph ) ) ) $=
    ( weq wal wi wex wa wn nfnae nfan cv wnfc nfcvf2 nfae intnanrd nexd 2falsed
    aecoms wb axrepndlem2 nfcvf adantl ad2antrr nfeld nf5rd sp impbid1 ad2antlr
    wel anbi1d exbid bibi12d albid imbi2d mpbid exp31 nd2 nd3 alrimi a1d 19.8ad
    nd4 nd1 pm2.61iii ) BCEBFZBDEBFZCDECFZADCEGDFCHZDBUKZCFZBCUKZDFZACFZIZBHZUA
    ZDFZGZBHZVGJZVHJZVIJZWAWBWCIZWDIZVJVKVMVOIZBHZUAZDFZGZBHWAABCDUBWFWKVTBWEWD
    BWBWCBBCBKBDBKLCDBKLZWFWJVSVJWFWIVRDWEWDDWBWCDBCDKBDDKLCDDKLWFVKVLWHVQWFVKV
    LWFVKCWFCDMZBMZWDCWMNWECDUCUDWBCWNNWCWDBCOUEUFUGVKCUHUIWFWGVPBWLWFVMVNVOWFV
    MVNWFVMDWFDWNCMZWCDWNNWBWDBDOUJWDDWONWECDOUDUFUGVMDUHUIULUMUNUOUPUMUQURVGVT
    BVGVSVJVGVRDBCDPVGVLVQVLJCBCBDUSTVGVPBBCBPVGVNVOBCDUTQRSVAVBVCVHVTBVHVSVJVH
    VRDBDDPVHVLVQBDCVDVHVPBBDBPVHVNVOVNJZDBDBCVETQRSVAVBVCVIVTBVIVSVJVIVRDCDDPV
    IVLVQCDBVEVIVPBCDBPVIVNVOWPDCDCBUSTQRSVAVBVCVF $.

  ${
    $d x y w $.  $d x z w $.
    $( Lemma for the Axiom of Union with no distinct variable conditions.
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 2-Jan-2002.)  (New usage is discouraged.) $)
    axunndlem1 $p |- E. x A. y ( E. x ( y e. x /\ x e. z ) -> y e. x ) $=
      ( vw weq wal wel wa wi wn cv en2lp elequ2 anbi2d mtbii nexdv nfnae exbidv
      wex sps pm2.21d axc4i 19.8ad zfun nfcvf nfcrd nfand nfexd nfimd wb elequ1
      nfvd anbi1d imbi12d a1i cbvald mpbii pm2.61i ) BCEZBFZBAGZACGZHZASZVAIZBF
      ZASZUTVFAUSVEBUTVDVAUTVCAUSVCJBUSVAABGZHVCBKAKLUSVHVBVABCAMNOTPUAUBUCUTJZ
      DAGZVBHZASZVJIZDFZASVGADCUDVIVNVFAVIVMVEDBBCBQVIVLVJBVIVKBABCAQVIVJVBBVIV
      JBULZVIBACKBCUEUFUGUHVOUIDBEZVMVEUJIVIVPVLVDVJVAVPVKVCAVPVJVAVBDBAUKZUMRV
      QUNUOUPRUQUR $.
  $}

  ${
    $d x w $.  $d y w $.  $d z w $.
    $( A version of the Axiom of Union with no distinct variable conditions.
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 2-Jan-2002.)  (New usage is discouraged.) $)
    axunnd $p |- E. x A. y ( E. x ( y e. x /\ x e. z ) -> y e. x ) $=
      ( vw weq wal wel wa wex wi wn nfnae nfan cv wnfc nfcvf adantr nfcvd nfae
      wb axunndlem1 nfv nfeld adantl nfand nfexd nfimd nfald nfcvf2 nfeqd nfan1
      elequ2 elequ1 anbi12d a1i cbvexd imbi12d albid ex mpbii elirrv mtbiri sps
      intnanrd nexd pm2.21d alrimi 19.8ad intnand pm2.61ii ) ABEZAFZACEZAFZBAGZ
      ACGZHZAIZVOJZBFZAIZVLKZVNKZWAWBWCHZBDGZDCGZHZDIZWEJZBFZDIWADBCUAWDWJVTDAW
      BWCAABALACALMZWDWIABWBWCBABBLACBLMZWDWHWEAWDWGADWDDUBWDWEWFAWDABNZDNZWBAW
      MOWCABPQWDAWNRZUCZWDAWNCNZWOWCAWQOWBACPUDUCUEZUFWPUGUHWDDAEZWJVTTWDWSHZWI
      VSBWDWSBWLWDBWNANZWDBWNRWBBXAOWCABUIQUJUKWTWHVRWEVOWDWHVRTWSWDWGVQDAWKWRW
      SWGVQTJWDWSWEVOWFVPDABULZDACUMUNUOUPQWSWEVOTWDXBUDUQURUSUPUTUSVLVTAVLVSBA
      BBSVLVRVOVLVQAABASVKVQKZAVKVOVPVKVOBBGBVAABBULVBVDVCVEVFVGVHVNVTAVNVSBACB
      SVNVRVOVNVQAACASVMXCAVMVPVOVMVPCCGCVAACCUMVBVIVCVEVFVGVHVJ $.
  $}

  $( Lemma for the Axiom of Power Sets with no distinct variable conditions.
     (Contributed by NM, 4-Jan-2002.) $)
  axpowndlem1 $p |- ( A. x x = y -> ( -. x = y ->
             E. x A. y ( A. x ( E. z x e. y -> A. y x e. z ) -> y e. x ) ) ) $=
    ( weq wn wel wex wal wi pm2.24 sps ) ABDZLEABFCGACFBHIAHBAFIBHAGZIALMJK $.

  ${
    $d x w $.  $d z y w $.
    $( Lemma for the Axiom of Power Sets with no distinct variable conditions.
       Revised to remove a redundant antecedent from the consequence.  Usage of
       this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 4-Jan-2002.)  (Proof shortened by Mario Carneiro,
       6-Dec-2016.)  (Revised and shortened by Wolf Lammen, 9-Jun-2019.)
       (New usage is discouraged.) $)
    axpowndlem2 $p |- ( -. A. x x = y -> ( -. A. x x = z ->
         E. x A. y ( A. x ( E. z x e. y -> A. y x e. z ) -> y e. x ) ) ) $=
      ( vw weq wal wel wex wi wa nfnae cv nfeld adantr nfald adantl wb nfan1 ex
      wnf wn zfpow 19.8a imim12i alimi imim1i eximii nfan nfv nfcvd nfcvf nfexd
      sp nfimd nfeqf2 naecoms elequ1 exbid adantll albid adantlr imbi12d cbvald
      elequ2 cbvexd mpbii ) ABEAFUAZACEAFUAZABGZCHZACGZBFZIZAFZBAGZIZBFZAHZVGVH
      JZDBGZCHZDCGZBFZIZDFZBDGZIZBFZDHVRVTWBIZDFZWFIZBFWHDDBCUBWKWGBWEWJWFWDWID
      VTWAWCWBVTCUCWBBUMUDUEUFUEUGVSWHVQDAVGVHAABAKACAKUHZVSWGABVGVHBABBKZACBKZ
      UHZVSWEWFAVSWDADVSDUIVSWAWCAVGWAATVHVGVTACABCKVGADLZBLZVGAWPUJZABUKZMULNV
      HWCATVGVHWBABWNVHAWPCLVHAWPUJACUKMOPUNZOVGWFATVHVGAWQWPWSWRMNUNOVSDAEZWHV
      QQVSXAJZWGVPBVSXABWOVGXABTZVHXCBABADUOUPZNRXBWEVNWFVOVSWEVNQXAVSWDVMDAWLW
      TVSXAWDVMQXBWAVJWCVLVHXAWAVJQVGVHXAJVTVICVHXACACCKXACTCACADUOUPRXAVTVIQVH
      DABUQPURUSVGXAWCVLQVHVGXAJWBVKBVGXABWMXDRXAWBVKQVGDACUQPUTVAVBSVCNXAWFVOQ
      VSDABVDPVBUTSVEVFS $.
  $}

  ${
    $d x w $.  $d y z w $.
    $( Lemma for the Axiom of Power Sets with no distinct variable conditions.
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 4-Jan-2002.)  (Revised by Mario Carneiro,
       10-Dec-2016.)  (Proof shortened by Wolf Lammen, 10-Jun-2019.)
       (New usage is discouraged.) $)
    axpowndlem3 $p |- ( -. x = y ->
               E. x A. y ( A. x ( E. z x e. y -> A. y x e. z ) -> y e. x ) ) $=
      ( vw weq wal wel wex wi wn cv c0 wceq wcel nfnae nfeld adantl exbid nfae
      wb sp csn p0ex eleq2 imbi2d albidv spcev 0ex snid mpbiri mpg neq0 con1bii
      eleq1 imbi1i albii exbii mpbir nfcvf2 nfcvd nfexd nfnd nfimd nfeqf2 nfan1
      wa elequ2 notbid elequ1 imbi12d cbvald mpbii axc11r alnex 3imtr3g pm2.21d
      ex nd3 jad spsd imim1d alimd eximd syl5com axpowndlem2 pm2.61d nsyl5 ) AB
      EZAFZWHABGZCHZACGBFZIZAFZBAGZIZBFZAHZWHAUAWIJZACEAFZWRWSWJAHZJZWOIZBFZAHZ
      WTWRWSADGZAHZJZDAGZIZDFZAHZXEXLDKZLMZXIIZDFZAHZXNXMLUBZNZIZXQDXPXTDFAXRUC
      AKZXRMZXOXTDYBXIXSXNYAXRXMUDUEUFUGXNXSLXRNLUHUIXMLXRUNUJUKXKXPAXJXODXHXNX
      IXNXGAXMULUMUOUPUQURWSXKXDAABAOZWSXJXCDBABBOWSXHXIBWSXGBWSXFBAYCWSBYAXMAB
      USZWSBXMUTZPVAVBWSBXMYAYEYDPVCWSDBEZXJXCTWSYFVFZXHXBXIWOYGXGXAYGXFWJAWSYF
      AYCABDVDVEYFXFWJTWSDBAVGQRVHYFXIWOTWSDBAVIQVJVQVKRVLWTXDWQAACASWTXCWPBACB
      SWTWNXBWOWTWMXBAWTWKWLXBWTWJJZCFYHAFWKJXBYHCAVMWJCVNWJAVNVOWTWLXBACBVRVPV
      SVTWAWBWCWDABCWEWFWG $.
  $}

  ${
    $d x w $.  $d y w $.  $d z w $.
    $( Lemma for the Axiom of Power Sets with no distinct variable conditions.
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 4-Jan-2002.)  (Proof shortened by Mario Carneiro,
       10-Dec-2016.)  (New usage is discouraged.) $)
    axpowndlem4 $p |- ( -. A. y y = x -> ( -. A. y y = z -> ( -. x = y
      -> E. x A. y ( A. x ( E. z x e. y -> A. y x e. z ) -> y e. x ) ) ) ) $=
      ( vw weq wal wn wel wi nfnae nfan cv wnfc adantr nfcvd nfeqd nfeld adantl
      wex wb axpowndlem3 ax-gen nfcvf nfnd nfv nfexd nfald nfimd equequ2 notbid
      wa nfcvf2 nfan1 elequ2 exbid biidd cbvald imbi12d albid elequ1 ex 19.21bi
      a1i mpbii ) BAEBFGZBCEBFGZABEZGZABHZCSZACHZBFZIZAFZBAHZIZBFZASZIZVEVFUKZV
      SBVTADEZGZADHZCSZVKDFZIZAFZDAHZIZDFZASZIZDFVSBFWLDADCUAUBVTWLVSDBVEVFBBAB
      JBCBJKZVTWBWKBVTWABVTBALZDLZVEBWNMVFBAUCNZVTBWOOZPUDVTWJBAVEVFABAAJBCAJKZ
      VTWIBDVTDUEZVTWGWHBVTWFBAWRVTWDWEBVTWCBCVEVFCBACJBCCJKZVTBWNWOWPWQQUFVTVK
      BDWSVTBWNCLZWPVFBXAMVEBCUCRQZUGUHUGVTBWOWNWQWPQUHZUGUFUHVTDBEZWLVSTVTXDUK
      ZWBVHWKVRXDWBVHTVTXDWAVGDBAUIUJRVTWKVRTXDVTWJVQAWRVTWIVPDBWMXCVTXDWIVPTXE
      WGVNWHVOXEWFVMAVTXDAWRVTAWOBLZVTAWOOVEAXFMVFBAULNPUMXEWDVJWEVLXEWCVICVTXD
      CWTVTCWOXFVTCWOOVFCXFMVEBCULRPUMXDWCVITVTDBAUNRUOVTWEVLTXDVTVKVKDBWMXBXDV
      KVKTIVTXDVKUPVCUQNURUSXDWHVOTVTDBAUTRURVAUQUONURVAUQVDVBVA $.
  $}

  ${
    $d x w $.  $d y w $.
    $( A version of the Axiom of Power Sets with no distinct variable
       conditions.  Usage of this theorem is discouraged because it depends on
       ~ ax-13 .  (Contributed by NM, 4-Jan-2002.)
       (New usage is discouraged.) $)
    axpownd $p |- ( -. x = y ->
               E. x A. y ( A. x ( E. z x e. y -> A. y x e. z ) -> y e. x ) ) $=
      ( vw weq wal wn wel wex wi axpowndlem4 axpowndlem1 aecoms a1d wa nfnae cv
      wb 19.8ad alnex nfae nfan el nfcvf2 nfcvd nfeld elequ2 cbvexd mpbii df-ex
      a1i sylib adantr biidd dral1 3bitr3g nd2 mtt syl bitrd dral2 adantl mtbid
      pm2.21d alrimi ex pm2.61i pm2.61ii ) BAEBFBCEBFZABEZGZABHZCIZACHBFZJZAFZB
      AHZJZBFZAIZJZABCKWAABABCLZMVJAFZVIWAJWCWAVIWBNWCGZVIWAWDVIOZVTVKWEVSAWEVR
      BWDVIBABBPZBCBUAUBWEVPVQWEVLBIZGZAFZVPWDWIGZVIWDWGAIWJWDWGAWDADHZDIWGADUC
      WDWKVLDBWFWDBAQDQZABUDWDBWLUEUFDBEWKVLRJWDDBAUGUKUHUISWGAUJULUMVIWIVPRWDW
      HVOBCAVIWHVMGZVOVIVLGZBFWNCFWHWMWNWNBCVIWNUNUOVLBTVLCTUPVIVNGWMVORBCAUQVN
      VMURUSUTVAVBVCVDVESNVFVGVH $.
  $}

$(
  @{
    @d x z @.  @d y z @.
    axpowndNEWlem1 @p |- ( A. x x = y ->
        ( ( A. x x = y -> E. z A. x ( E. z z e. y -> x e. z ) )
         -> E. x A. y ( A. x ( E. z x e. y -> A. y x e. z ) -> y e. x ) ) ) @=
      ( weq wal wel wex wi cv csn c0 wceq wn wcel wa en2lp vex snid biantru
      mtbir snnzOLD a1bi mtbi neq0 imbi1i albii bicomi snex eqeq1 notbid eleq1
    imbi12d spcv sylbi mto hbae wb elequ2 sps exbidv imbi1d albidh mtbii nexdv
     pm2.21d a2i com12 ) ABDZAEZCBFZCGZACFZHZAEZCGZHVIABFCGVLBEHAEBAFHBEAGZVIVO
      VPVIVOVPVIVNCVICAFZCGZVLHZAEZVNVTCIZJZKLZMZWBWANZHZWEWFWEWEWAWBNZOWBWAPWG
      WEWACQZRSTWDWEWAWHUAUBUCVTAIZKLZMZVLHZAEZWFWMVTWLVSAWKVRVLCWIUDUEUFUGWLWF
      AWBWAUHWIWBLZWKWDVLWEWNWJWCWIWBKUIUJWIWBWAUKULUMUNUOVIVSVMAABAUPVIVRVKVLV
      IVQVJCVHVQVJUQAABCURUSUTVAVBVCVDVEVFVG @.
  @}

  @{
    @d x w @.  @d y w @.
   axpowndNEW @p |- ( ( A. x x = y -> E. z A. x ( E. z z e. y -> x e. z ) ) ->
               E. x A. y ( A. x ( E. z x e. y -> A. y x e. z ) -> y e. x ) ) @=
?@.
  @}
$)

  $( Lemma for the Axiom of Regularity with no distinct variable conditions.
     Usage of this theorem is discouraged because it depends on ~ ax-13 .
     (Contributed by NM, 3-Jan-2002.)  (New usage is discouraged.) $)
  axregndlem1 $p |- ( A. x x = z -> ( x e. y ->
               E. x ( x e. y /\ A. z ( z e. x -> -. z e. y ) ) ) ) $=
    ( wel wex weq wal wn wi wa 19.8a nfae elirrv elequ1 mtbii sps alrimi anim2i
    pm2.21d expcom eximd syl5 ) ABDZUCAEACFZAGZUCCADZCBDHZIZCGZJZAEUCAKUEUCUJAA
    CALUCUEUJUEUIUCUEUHCACCLUEUFUGUDUFHAUDAADUFAMACANOPSQRTUAUB $.

  ${
    $d x w $.  $d z y w $.
    $( Lemma for the Axiom of Regularity with no distinct variable conditions.
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 3-Jan-2002.)  (Proof shortened by Mario Carneiro,
       10-Dec-2016.)  (New usage is discouraged.) $)
    axregndlem2 $p |- ( x e. y ->
                 E. x ( x e. y /\ A. z ( z e. x -> -. z e. y ) ) ) $=
      ( vw weq wal wel wn wi wa wex nfnae nfan cv nfcvd wnfc nfcvf nfeld wb ex
      axreg2 ax-gen adantr nfv adantl nfnd nfimd nfald nfand nfexd simpr eleq1d
      nfcvf2 nfeqd nfan1 eleq2d imbi1d albid anbi12d cbvexd cbvald mpbii elirrv
      imbi12d 19.21bi elequ2 mtbii sps pm2.21d axregndlem1 pm2.61ii ) ABEZAFZAC
      EAFZABGZVOCAGZCBGZHZIZCFZJZAKZIZVMHZVNHZWCWDWEJZWCAWFDBGZWGCDGZVRIZCFZJZD
      KZIZDFWCAFWMDDBCUAUBWFWMWCDAWDWEAABALACALMZWFWGWLAWFADNZBNZWFAWOOZWDAWPPW
      EABQUCZRZWFWKADWFDUDWFWGWJAWSWFWIACWDWECABCLACCLMZWFWHVRAWFACNZWOWEAXAPWD
      ACQUEZWQRWFVQAWFAXAWPXBWRRUFUGUHUIZUJUGWFDAEZWMWCSWFXDJZWGVOWLWBXEWOANZWP
      WFXDUKZULZWFWLWBSXDWFWKWADAWNXCWFXDWKWASXEWGVOWJVTXHXEWIVSCWFXDCWTWFCWOXF
      WFCWOOWECXFPWDACUMUEUNUOXEWHVPVRXEWOXFXAXGUPUQURUSTUTUCVDTVAVBVETVMVOWBVL
      VOHAVLAAGVOAVCABAVFVGVHVIABCVJVK $.
  $}

  ${
    $d x w $.  $d y w $.  $d z w $.
    $( A version of the Axiom of Regularity with no distinct variable
       conditions.  Usage of this theorem is discouraged because it depends on
       ~ ax-13 .  (Contributed by NM, 3-Jan-2002.)  (Proof shortened by Wolf
       Lammen, 18-Aug-2019.)  (New usage is discouraged.) $)
    axregnd $p |- ( x e. y ->
                 E. x ( x e. y /\ A. z ( z e. x -> -. z e. y ) ) ) $=
      ( vw weq wal wel wn wi wa wex axregndlem2 nfnae wnf cv nfcvf nfcrd adantr
      nfan elequ1 nfnd adantl nfimd wb notbid imbi12d a1i cbvald exbid imbitrid
      anbi2d axregndlem1 aecoms 19.8a nfae elirrv elequ2 mtbii a1d alimi anim2i
      ex expcom eximd syl5 pm2.61ii ) CAECFZCBEZCFZABGZVJCAGZCBGZHZIZCFZJZAKZIZ
      VGHZVIHZVRVJVJDAGZDBGZHZIZDFZJZAKVSVTJZVQABDLWGWFVPAVSVTACAAMCBAMSWGWEVOV
      JWGWDVNDCVSVTCCACMCBCMSWGWAWCCVSWACNVTVSCDAOCAPQRVTWCCNVSVTWBCVTCDBOCBPQU
      AUBUCDCEZWDVNUDIWGWHWAVKWCVMDCATWHWBVLDCBTUEUFUGUHUKUIUJVBVRACABCULUMVJVJ
      AKVIVQVJAUNVIVJVPACBAUOVJVIVPVIVOVJVHVNCVHVMVKVHCCGVLCUPCBCUQURUSUTVAVCVD
      VEVF $.
  $}

  ${
    $d x w $.  $d z y w $.
    $( Lemma for the Axiom of Infinity with no distinct variable conditions.
       (New usage is discouraged.)  (Contributed by NM, 5-Jan-2002.) $)
    axinfndlem1 $p |- ( A. x y e. z -> E. x ( y e. x /\
                 A. y ( y e. x -> E. z ( y e. z /\ z e. x ) ) ) ) $=
      ( vw weq wal wel wa wex wi wn nfnae nfan cv wnfc nfcvf adantr nfcvd nfeld
      adantl zfinf nfand nfexd nfimd nfald wb simpr eleq2d nfcvf2 elequ2 anbi2d
      nfeqd nfan1 exbid imbi12d albid anbi12d cbvexd mpbii a1d pm2.21d pm2.61ii
      ex nd1 nd2 ) ABEAFZACEAFZBCGZAFZBAGZVJVHCAGZHZCIZJZBFZHZAIZJZVFKZVGKZVRVS
      VTHZVQVIWABDGZWBVHCDGZHZCIZJZBFZHZDIVQDBCUAWAWHVPDAVSVTAABALACALMWAWBWGAW
      AABNZDNZVSAWIOVTABPQZWAAWJRZSZWAWFABVSVTBABBLACBLMZWAWBWEAWMWAWDACVSVTCAB
      CLACCLMZWAVHWCAWAAWICNZWKVTAWPOVSACPTZSWAAWPWJWQWLSUBUCUDUEUBWADAEZWHVPUF
      WAWRHZWBVJWGVOWSWJANZWIWAWRUGUHZWSWFVNBWAWRBWNWABWJWTWABWJRVSBWTOVTABUIQU
      LUMWSWBVJWEVMXAWSWDVLCWAWRCWOWACWJWTWACWJRVTCWTOVSACUITULUMWRWDVLUFWAWRWC
      VKVHDACUJUKTUNUOUPUQVCURUSUTVCVFVIVQABCVDVAVGVIVQACBVEVAVB $.
  $}

  ${
    $d x w $.  $d y w $.  $d z w $.
    $( A version of the Axiom of Infinity with no distinct variable conditions.
       (New usage is discouraged.)  (Contributed by NM, 5-Jan-2002.) $)
    axinfnd $p |- E. x ( y e. z -> ( y e. x /\
                 A. y ( y e. x -> E. z ( y e. z /\ z e. x ) ) ) ) $=
      ( vw wel wa wex wi wal weq wn nfnae nfan cv nfcvd wnfc nfeld adantr wb ex
      axinfndlem1 ax-gen nfcvf adantl nfald nfand nfexd nfimd nfeqd nfan1 simpr
      nfcvf2 eleq1d albid anbi1d exbid imbi12d cbvald anbi12d mpbii 19.21bi nd1
      aecoms pm2.21d nd3 pm2.61ii 19.35ri ) BCEZBAEZVIVHCAEZFZCGZHZBIZFZABAJBIZ
      BCJBIZVHAIZVOAGZHZVPKZVQKZVTWAWBFZVTBWCDCEZAIZDAEZWFWDVJFZCGZHZDIZFZAGZHZ
      DIVTBIWMDADCUAUBWCWMVTDBWAWBBBABLBCBLMZWCWEWLBWCWDBAWAWBABAALBCALMZWCBDNZ
      CNZWCBWPOZWBBWQPWABCUCUDZQZUEWCWKBAWOWCWFWJBWCBWPANZWRWABXAPWBBAUCRZQZWCW
      IBDWAWBDBADLBCDLMWCWFWHBXCWCWGBCWAWBCBACLBCCLMZWCWDVJBWTWCBWQXAWSXBQUFUGU
      HZUEUFUGUHWCDBJZWMVTSWCXFFZWEVRWLVSXGWDVHAWCXFAWOWCAWPBNZWCAWPOWAAXHPWBBA
      ULRUIUJZXGWPXHWQWCXFUKZUMZUNXGWKVOAXIXGWFVIWJVNXGWPXHXAXJUMZWCWJVNSXFWCWI
      VMDBWNXEWCXFWIVMSXGWFVIWHVLXLXGWGVKCWCXFCXDWCCWPXHWCCWPOWBCXHPWABCULUDUIU
      JXGWDVHVJXKUOUPUQTURRUSUPUQTURUTVATVPVRVSVRKABABCVBVCVDVQVRVSBCAVEVDVFVG
      $.
  $}

  $( Lemma for the Axiom of Choice with no distinct variable conditions.  Usage
     of this theorem is discouraged because it depends on ~ ax-13 .
     (Contributed by NM, 3-Jan-2002.)  (New usage is discouraged.) $)
  axacndlem1 $p |- ( A. x x = y ->
            E. x A. y A. z ( A. x ( y e. z /\ z e. w ) -> E. w A. y ( E. w
          ( ( y e. z /\ z e. w ) /\ ( y e. w /\ w e. x ) ) <-> y = w ) ) ) $=
    ( weq wal wel wa wex wb wi nfae simpl alimi nd1 pm2.21d syl5 alrimi 19.8ad
    ) ABEAFZBCGZCDGZHZAFZUCBDGDAGHHDIBDEJBFDIZKZCFZBFATUGBABBLTUFCABCLUDUAAFZTU
    EUCUAAUAUBMNTUHUEABCOPQRRS $.

  $( Lemma for the Axiom of Choice with no distinct variable conditions.  Usage
     of this theorem is discouraged because it depends on ~ ax-13 .
     (Contributed by NM, 3-Jan-2002.)  (New usage is discouraged.) $)
  axacndlem2 $p |- ( A. x x = z ->
            E. x A. y A. z ( A. x ( y e. z /\ z e. w ) -> E. w A. y ( E. w
          ( ( y e. z /\ z e. w ) /\ ( y e. w /\ w e. x ) ) <-> y = w ) ) ) $=
    ( weq wal wel wa wex wb wi nfae simpr alimi nd1 pm2.21d syl5 alrimi 19.8ad
    ) ACEAFZBCGZCDGZHZAFZUCBDGDAGHHDIBDEJBFDIZKZCFZBFATUGBACBLTUFCACCLUDUBAFZTU
    EUCUBAUAUBMNTUHUEACDOPQRRS $.

  $( Lemma for the Axiom of Choice with no distinct variable conditions.  Usage
     of this theorem is discouraged because it depends on ~ ax-13 .
     (Contributed by NM, 3-Jan-2002.)  (New usage is discouraged.) $)
  axacndlem3 $p |- ( A. y y = z ->
            E. x A. y A. z ( A. x ( y e. z /\ z e. w ) -> E. w A. y ( E. w
          ( ( y e. z /\ z e. w ) /\ ( y e. w /\ w e. x ) ) <-> y = w ) ) ) $=
    ( weq wal wel wa wex wb wi nfae simpl alimi nd3 pm2.21d alrimi axc4i 19.8ad
    syl5 ) BCEZBFZBCGZCDGZHZAFZUEBDGDAGHHDIBDEJBFDIZKZCFZBFAUAUIBUBUHCBCCLUFUCA
    FZUBUGUEUCAUCUDMNUBUJUGBCAOPTQRS $.

  ${
    $d x v $.  $d y z w v $.
    $( Lemma for the Axiom of Choice with no distinct variable conditions.
       (New usage is discouraged.)  (Contributed by NM, 8-Jan-2002.)  (Proof
       shortened by Mario Carneiro, 10-Dec-2016.) $)
    axacndlem4 $p |- E. x A. y A. z ( A. x ( y e. z /\ z e. w ) ->
              E. w A. y ( E. w ( ( y e. z /\ z e. w ) /\ ( y e. w /\ w e. x ) )
                     <-> y = w ) ) $=
      ( vv weq wal wel wa wex wb wi wn nfnae nf3an cv wnfc nfeld nfcvd nfeqd sp
      w3a nfcvf 3ad2ant2 3ad2ant1 3ad2ant3 nfand nfexd nfbid nfald nfimd nfcvf2
      nfan1 nf5rd adantr impbid1 simpr eleq2d anbi2d exbid bibi1d albid imbi12d
      zfac ex cbvexd mpbii 3exp axacndlem2 axacndlem1 nfae alimi pm2.21d alrimi
      nd2 syl5 19.8ad pm2.61iii ) ACFAGZABFAGZADFAGZBCHZCDHZIZAGZWDBDHZDAHZIZIZ
      DJZBDFZKZBGZDJZLZCGZBGZAJZVSMZVTMZWAMZWRWSWTXAUBZWDWDWFDEHZIZIZDJZWKKZBGZ
      DJZLZCGZBGZEJWREBCDVDXBXLWQEAWSWTXAAACANABANADANOXBXKABWSWTXABACBNABBNADB
      NOZXBXJACWSWTXACACCNABCNADCNOZXBWDXIAXBWBWCAXBABPZCPZWTWSAXOQXAABUCUDZWSW
      TAXPQXAACUCUEZRXBAXPDPZXRXAWSAXSQWTADUCUFZRUGZXBXHADWSWTXADACDNABDNADDNOZ
      XBXGABXMXBXFWKAXBXEADYBXBWDXDAYAXBWFXCAXBAXOXSXQXTRXBAXSEPZXTXBAYCSRUGUGU
      HXBAXOXSXQXTTUIUJUHUKUJUJXBEAFZXLWQKXBYDIZXKWPBXBYDBXMXBBYCAPZXBBYCSWTWSB
      YFQXAABULUDTUMZYEXJWOCXBYDCXNXBCYCYFXBCYCSWSWTCYFQXAACULUETUMYEWDWEXIWNYE
      WDWEXBWDWELYDXBWDAYAUNUOWDAUAUPYEXHWMDXBYDDYBXBDYCYFXBDYCSXAWSDYFQWTADULU
      FTUMZYEXGWLBYGYEXFWJWKYEXEWIDYHYEXDWHWDYEXCWGWFYEYCYFXSXBYDUQURUSUSUTVAVB
      UTVCVBVBVEVFVGVHABCDVIABCDVJWAWQAWAWPBADBVKWAWOCADCVKWEWCAGZWAWNWDWCAWBWC
      UQVLWAYIWNADCVOVMVPVNVNVQVR $.
  $}

  ${
    $d x v $.  $d y v $.  $d z w v $.
    $( Lemma for the Axiom of Choice with no distinct variable conditions.
       (New usage is discouraged.)  (Contributed by NM, 3-Jan-2002.)  (Proof
       shortened by Mario Carneiro, 10-Dec-2016.) $)
    axacndlem5 $p |- E. x A. y A. z ( A. x ( y e. z /\ z e. w ) ->
              E. w A. y ( E. w ( ( y e. z /\ z e. w ) /\ ( y e. w /\ w e. x ) )
                     <-> y = w ) ) $=
      ( vv weq wal wel wa wex wb wn nfnae nf3an cv nfcvd wnfc nfcvf nfeld nfeqd
      wi w3a axacndlem4 3ad2ant1 3ad2ant3 nfand nfald nfv 3ad2ant2 nfexd nfcvf2
      nfbid nfimd nfan1 simpr eleq1d anbi1d albid anbi12d eqeq1d bibi12d cbvald
      exbid adantr imbi12d mpbii 3exp axacndlem3 axacndlem1 aecoms en2lp elequ2
      ex nfae anbi2d mtbii sps pm2.21d spsd alrimi axc4i 19.8ad pm2.61iii ) BCF
      BGZBAFBGZBDFZBGZBCHZCDHZIZAGZWJBDHZDAHZIZIZDJZWFKZBGZDJZUAZCGZBGZAJZWDLZW
      ELZWGLZXCXDXEXFUBZECHZWIIZAGZXIEDHZWMIZIZDJZEDFZKZEGZDJZUAZCGZEGZAJXCAECD
      UCXGYAXBAXDXEXFABCAMBAAMBDAMNZXGXTXAEBXDXEXFBBCBMBABMBDBMNZXGXSBCXDXEXFCB
      CCMBACMBDCMNZXGXJXRBXGXIBAYBXGXHWIBXGBEOZCOZXGBYEPZXDXEBYFQXFBCRUDZSXGBYF
      DOZYHXFXDBYIQXEBDRUEZSUFZUGXGXQBDXDXEXFDBCDMBADMBDDMNZXGXPBEXGEUHXGXNXOBX
      GXMBDYLXGXIXLBYKXGXKWMBXGBYEYIYGYJSXGBYIAOZYJXEXDBYMQXFBARUISUFUFUJXGBYEY
      IYGYJTULZUGUJUMUGXGEBFZXTXAKXGYOIZXSWTCXGYOCYDXGCYEBOZXGCYEPXDXECYQQXFBCU
      KUDTUNYPXJWKXRWSYPXIWJAXGYOAYBXGAYEYQXGAYEPXEXDAYQQXFBAUKUITUNYPXHWHWIYPY
      EYQYFXGYOUOZUPUQZURXGXRWSKYOXGXQWRDYLXGXPWQEBYCYNXGYOXPWQKYPXNWPXOWFYPXMW
      ODXGYODYLXGDYEYQXGDYEPXFXDDYQQXEBDUKUETUNYPXIWJXLWNYSYPXKWLWMYPYEYQYIYRUP
      UQUSVCYPYEYQYIYRUTVAVMVBVCVDVEURVMVBVCVFVGABCDVHXCABABCDVIVJWGXBAWFXABWGW
      TCBDCVNWGWJWSAWGWJWSWFWJLBWFWHCBHZIWJYQYFVKWFYTWIWHBDCVLVOVPVQVRVSVTWAWBW
      C $.
  $}

  ${
    $d x v $.  $d y v $.  $d z v $.  $d w v $.
    $( A version of the Axiom of Choice with no distinct variable conditions.
       (New usage is discouraged.)  (Contributed by NM, 3-Jan-2002.)  (Proof
       shortened by Mario Carneiro, 10-Dec-2016.) $)
    axacnd $p |- E. x A. y A. z ( A. x ( y e. z /\ z e. w ) -> E. w A. y
       ( E. w ( ( y e. z /\ z e. w ) /\ ( y e. w /\ w e. x ) ) <-> y = w ) ) $=
      ( vv weq wal wel wa wex wb wn nfnae nf3an cv wnfc nfcvf nfcvd nfeld nfeqd
      axacndlem5 3ad2ant2 3ad2ant3 nfand nfald 3ad2ant1 nfexd nfbid nfimd nfan1
      w3a nfcvf2 simpr eleq2d eleq1d anbi12d albid anbi1d bibi1d imbi12d cbvald
      wi exbid ex mpbii 3exp axacndlem2 aecoms axacndlem3 nfae nd3 pm2.21d syl5
      alimi axc4i alrimi 19.8ad pm2.61iii ) CAFCGZCBFCGZCDFZCGZBCHZCDHZIZAGZWEB
      DHZDAHZIZIZDJZBDFZKZBGZDJZVBZCGZBGZAJZVSLZVTLZWBLZWSWTXAXBUKZBEHZEDHZIZAG
      ZXFWIIZDJZWLKZBGZDJZVBZEGZBGZAJWSABEDUAXCXOWRAWTXAXBACAAMCBAMCDAMNZXCXNWQ
      BWTXAXBBCABMCBBMCDBMNZXCXMWPECWTXAXBCCACMCBCMCDCMNXCXGXLCXCXFCAXPXCXDXECX
      CCBOZEOZXAWTCXRPXBCBQUBZXCCXSRZSXCCXSDOZYAXBWTCYBPXACDQUCZSUDZUEXCXKCDWTX
      AXBDCADMCBDMCDDMNZXCXJCBXQXCXIWLCXCXHCDYEXCXFWICYDXCWGWHCXCCXRYBXTYCSXCCY
      BAOZYCWTXACYFPXBCAQUFSUDUDUGXCCXRYBXTYCTUHUEUGUIXCECFZXMWPKXCYGIZXGWFXLWO
      YHXFWEAXCYGAXPXCAXSCOZXCAXSRWTXAAYIPXBCAULUFTUJYHXDWCXEWDYHXSYIXRXCYGUMZU
      NYHXSYIYBYJUOUPZUQYHXKWNDXCYGDYEXCDXSYIXCDXSRXBWTDYIPXACDULUCTUJZYHXJWMBX
      CYGBXQXCBXSYIXCBXSRXAWTBYIPXBCBULUBTUJYHXIWKWLYHXHWJDYLYHXFWEWIYKURVCUSUQ
      VCUTVDVAUQVCVEVFWSACABCDVGVHWSBCABCDVIVHWBWRAWBWQBCDBVJWAWPCWFWDAGZWBWOWE
      WDAWCWDUMVNWBYMWOCDAVKVLVMVOVPVQVR $.
  $}

  ${
    $d x y z w v u t $.
    $( Axiom of Extensionality ~ ax-ext , reproved from conditionless ZFC
       version and predicate calculus.  Usage of this theorem is discouraged
       because it depends on ~ ax-13 .  (Contributed by NM, 15-Aug-2003.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    zfcndext $p |- ( A. z ( z e. x <-> z e. y ) -> x = y ) $=
      ( cv wcel wb wceq axextnd 19.36iv ) CDZADZEJBDZEFKLGCCABHI $.

    $( Axiom of Replacement ~ ax-rep , reproved from conditionless ZFC axioms.
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 15-Aug-2003.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    zfcndrep $p |- ( A. w E. y A. z ( A. y ph -> z = y ) ->
                     E. y A. z ( z e. y <-> E. w ( w e. x /\ A. y ph ) ) ) $=
      ( wal cv wceq wi wex wcel wa wb nfe1 nfv nfa1 nfex nfbi nfal exbii elequ2
      nfan nfim anbi1d exbidv bibi2d albidv imbi2d axrepnd 19.3v anbi1i bibi12i
      albii imbi2i mpbi chvar 19.35i 19.3 anbi2i a1i bibi12d cbvexv1 sylib ) AC
      FZDGZCGZHIDFZCJZEFVEEGZKZVIBGZKZVDCFZLZEJZMZDFZEJVEVFKZVLVDLZEJZMZDFZCJVH
      VQEVHVJVIVFKZVMLZEJZMZDFZIZEJZVHVQIZEJCBWJCEVHVQCVGCNVPCDVJVOCVJCOVNCEVLV
      MCVLCOVDCPUBQRSZUCQVFVKHZWHWJEWLWGVQVHWLWFVPDWLWEVOVJWLWDVNEWLWCVLVMCBEUA
      UDUEUFUGUHUEVHVJCFZWCDFZVMLZEJZMZDFZIZEJWIVDECDUIWSWHEWRWGVHWQWFDWMVJWPWE
      VJCUJWOWDEWNWCVMWCDUJUKTULUMUNTUOUPUQVQWBECWKWAEDVRVTEVREOVSENRSVIVFHZVPW
      ADWTVJVRVOVTECDUAVOVTMWTVNVSEVMVDVLVDCACPURUSTUTVAUGVBVC $.

    $( Axiom of Union ~ ax-un , reproved from conditionless ZFC axioms.  Usage
       of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 15-Aug-2003.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    zfcndun $p |- E. y A. z ( E. w ( z e. w /\ w e. x ) -> z e. y ) $=
      ( cv wcel wa wex wi wal axunnd elequ2 elequ1 anbi12d cbvexvw imbi1i albii
      wceq exbii mpbir ) CEZDEZFZUBAEZFZGZDHZUABEZFZIZCJZBHUIUHUDFZGZBHZUIIZCJZ
      BHBCAKUKUPBUJUOCUGUNUIUFUMDBUBUHRUCUIUEULDBCLDBAMNOPQST $.

    $( Axiom of Power Sets ~ ax-pow , reproved from conditionless ZFC axioms.
       The proof uses the "Axiom of Twoness" ~ dtru .  Usage of this theorem is
       discouraged because it depends on ~ ax-13 .  (Contributed by NM,
       15-Aug-2003.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    zfcndpow $p |- E. y A. z ( A. w ( w e. z -> w e. x ) -> z e. y ) $=
      ( cv wcel wi wal wceq wn dtru exnal mpbir nfe1 axpownd albii imbi1i exbii
      wex elequ1 exlimi ax-mp 19.9v 19.3v imbi12i mpbi imbi12d cbvalvw ) DEZCEZ
      FZUIAEZFZGZDHZUJBEZFZGZCHZBSUPUJFZUPULFZGZBHZUQGZCHZBSZUTASZVACHZGZBHZUQG
      ZCHZBSZVFUPUJIZJZBSZVMVPVNBHJBCKVNBLMVOVMBVLBNBCAOUAUBVLVEBVKVDCVJVCUQVIV
      BBVGUTVHVAUTAUCVACUDUEPQPRUFUSVEBURVDCUOVCUQUNVBDBUIUPIUKUTUMVADBCTDBATUG
      UHQPRM $.

    $( Axiom of Regularity ~ ax-reg , reproved from conditionless ZFC axioms.
       Usage of this theorem is discouraged because it depends on ~ ax-13 .
       (Contributed by NM, 15-Aug-2003.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    zfcndreg $p |- ( E. y y e. x ->
                 E. y ( y e. x /\ A. z ( z e. y -> -. z e. x ) ) ) $=
      ( cv wcel wn wi wal wa wex nfe1 axregnd exlimi ) BDZADZEZPCDZNEQOEFGCHIZB
      JBRBKBACLM $.

    $( Axiom of Infinity ~ ax-inf , reproved from conditionless ZFC axioms.
       Since we have already reproved Extensionality, Replacement, and Power
       Sets above, we are justified in referencing Theorem ~ el in the proof.
       (New usage is discouraged.)  (Proof modification is discouraged.)
       (Contributed by NM, 15-Aug-2003.) $)
    zfcndinf $p |- E. y ( x e. y /\
                 A. z ( z e. y -> E. w ( z e. w /\ w e. y ) ) ) $=
      ( cv wcel wa wex wi wal el nfv nfe1 nfim nfal nfan axinfnd 19.37iv elequ1
      nfex exlimi ax-mp wceq anbi1d exbidv imbi12d cbvalvw anbi2i exbii mpbir )
      AEZBEZFZCEZULFZUNDEZFZUPULFZGZDHZIZCJZGZBHUMUMUKUPFZURGZDHZIZAJZGZBHZVDDH
      VJADKVDVJDVIDBUMVHDUMDLZVGDAUMVFDVKVEDMNOPTVDVIBBADQRUAUBVCVIBVBVHUMVAVGC
      AUNUKUCZUOUMUTVFCABSVLUSVEDVLUQVDURCADSUDUEUFUGUHUIUJ $.

    $( Axiom of Choice ~ ax-ac , reproved from conditionless ZFC axioms.
       (Contributed by NM, 15-Aug-2003.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    zfcndac $p |- E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. v A. u ( E. t
              ( ( u e. w /\ w e. t ) /\ ( u e. t /\ t e. y ) ) <-> u = v ) ) $=
      ( cv wcel wa wex wceq wb wal wi 2albii exbii elequ2 elequ1 anbi12d axacnd
      imbi1i equequ2 bibi2d anbi2d cbvexvw bibi1i bitrdi albidv equequ1 bibi12d
      19.3v mpbi anbi1d exbidv cbvalvw imbi2i mpbir ) CHZDHZIZUTAHZIZJZFHZUTIZU
      TGHZIZJZVEVGIZVGBHZIZJZJZGKZVEEHZLZMZFNZEKZOZDNCNZBKVDVDUSVBIZVBVKIZJZJZA
      KZUSVBLZMZCNZAKZOZDNCNZBKZVDBNZWKOZDNCNZBKWNBCDAUAWQWMBWPWLCDWOVDWKVDBULU
      BPQUMWBWMBWAWLCDVTWKVDVSWJEAVPVBLZVSVFVCJZVEVBIZWDJZJZAKZVEVBLZMZFNWJWRVR
      XEFWRVRVOXDMXEWRVQXDVOEAFUCUDVOXCXDVNXBGAVGVBLZVIWSVMXAXFVHVCVFGADRUEXFVJ
      WTVLWDGAFRGABSTTUFUGUHUIXEWIFCVEUSLZXCWGXDWHXGXBWFAXGWSVDXAWEXGVFVAVCFCDS
      UNXGWTWCWDFCASUNTUOFCAUJUKUPUHUFUQPQUR $.
  $}

$(
  @{
    @d x y z w @.
    zfcndpowNEW @p |- E. x A. y ( A. x ( x e. y -> x e. z ) -> y e. x ) @=
     ( wel wi wal wex weq wa wb zfcndrep hbae 19.9rOLD equid a1bi albii exbii
       bitri
      imbi1i mpbir 19.37 mpbi ax-gen biantru bibi2i bicomi biimpr sylbi alimi
      eximi syl axpowndNEW ax-mp 19.9rvOLD ax-5 19.3rOLD imbi12i )
      ABDZACDZEZAFZBADZE
      ZBFZAGURCGZUSBFZEZAFZVBEZBFZAGZABHZAFZCBDZCGZUSEZAFZCGZEVKVMUSVNAAHZBFZIZ
      CGZJZAFZCGZVRVMWDEZCGZVMWEEWGVSVLEZAFZBGZWDEZCGVSCBAKWFWKCVMWJWDVMVMBGWJV
      MBABBLMVMWIBVLWHAVSVLANZOPQRSQTVMWDCABCLUAUBWDVQCWCVPAWCUSVOJZVPWMWCVOWBU
      SVNWACVTVNVSBWLUCUDQUEUFUSVOUGUHUIUJUKABCULUMVDVJAVCVIBVAVHVBUTVGAURVEUSV
      FURCUNUSBUSBUOUPUQPSPQT @.
  @}
$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  The Generalized Continuum Hypothesis
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Sets satisfying the Generalized Continuum Hypothesis
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c GCH $.

  $( Extend class notation to include the collection of sets that satisfy the
     GCH. $)
  cgch $a class GCH $.

  ${
    $d x y $.
    $( Define the collection of "GCH-sets", or sets for which the generalized
       continuum hypothesis holds.  In this language the generalized continuum
       hypothesis can be expressed as ` GCH = _V ` .  A set ` x ` satisfies the
       generalized continuum hypothesis if it is finite or there is no set
       ` y ` strictly between ` x ` and its powerset in cardinality.  The
       continuum hypothesis is equivalent to ` _om e. GCH ` .  (Contributed by
       Mario Carneiro, 15-May-2015.) $)
    df-gch $a |- GCH = ( Fin u. { x | A. y -. ( x ~< y /\ y ~< ~P x ) } ) $.
  $}

  ${
    $d x y A $.
    $( Elementhood in the collection of GCH-sets.  (Contributed by Mario
       Carneiro, 15-May-2015.) $)
    elgch $p |- ( A e. V -> ( A e. GCH <-> ( A e. Fin \/
      A. x -. ( A ~< x /\ x ~< ~P A ) ) ) ) $=
      ( vy cgch wcel cfn cv csdm wbr cpw wa wn wal cab cun df-gch eleq2i elun
      wo bitri wceq breq1 pweq breq2d anbi12d notbid albidv elabg orbi2d bitrid
      ) BEFZBGFZBDHZAHZIJZUOUNKZIJZLZMZANZDOZFZTZBCFZUMBUOIJZUOBKZIJZLZMZANZTUL
      BGVBPZFVDEVLBDAQRBGVBSUAVEVCVKUMVAVKDBCUNBUBZUTVJAVMUSVIVMUPVFURVHUNBUOIU
      CVMUQVGUOIUNBUDUEUFUGUHUIUJUK $.

    $( A finite set is a GCH-set.  (Contributed by Mario Carneiro,
       15-May-2015.) $)
    fingch $p |- Fin C_ GCH $=
      ( vx vy cfn cv csdm wbr cpw wa wn wal cab cun cgch ssun1 df-gch sseqtrri
      ) CCADZBDZEFRQGEFHIBJAKZLMCSNABOP $.

    $d x B $.
    $( The only GCH-sets which have other sets between it and its power set are
       finite sets.  (Contributed by Mario Carneiro, 15-May-2015.) $)
    gchi $p |- ( ( A e. GCH /\ A ~< B /\ B ~< ~P A ) -> A e. Fin ) $=
      ( vx cgch wcel csdm wbr cpw cfn wa cv wn wal wex relsdom brrelex1i adantl
      cvv wceq breq2 breq1 anbi12d spcegv mpcom df-ex sylib wo elgch ibi orcomd
      ord syl5 3impib ) ADEZABFGZBAHZFGZAIEZUOUQJZACKZFGZUTUPFGZJZLCMZLZUNURUSV
      CCNZVEBREZUSVFUQVGUOBUPFOPQVCUSCBRUTBSVAUOVBUQUTBAFTUTBUPFUAUBUCUDVCCUEUF
      UNVDURUNURVDUNURVDUGCADUHUIUJUKULUM $.

    $( If ` A <_ B < ~P A ` , and ` A ` is an infinite GCH-set, then ` A = B `
       in cardinality.  (Contributed by Mario Carneiro, 15-May-2015.) $)
    gchen1 $p |- ( ( ( A e. GCH /\ -. A e. Fin ) /\ ( A ~<_ B /\ B ~< ~P A ) )
      -> A ~~ B ) $=
      ( cgch wcel cfn wn wa cdom wbr cpw csdm cen simprl 3com23 3expia con3dimp
      gchi an32s adantrl bren2 sylanbrc ) ACDZAEDZFZGZABHIZBAJKIZGGUFABKIZFZABL
      IUEUFUGMUEUGUIUFUBUGUDUIUBUGGUHUCUBUGUHUCUBUHUGUCABQNOPRSABTUA $.

    $( If ` A < B <_ ~P A ` , and ` A ` is an infinite GCH-set, then
       ` B = ~P A ` in cardinality.  (Contributed by Mario Carneiro,
       15-May-2015.) $)
    gchen2 $p |- ( ( ( A e. GCH /\ -. A e. Fin ) /\ ( A ~< B /\ B ~<_ ~P A ) )
      -> B ~~ ~P A ) $=
      ( cgch wcel cfn wn wa csdm wbr cpw cdom simprr gchi 3expia con3dimp an32s
      cen adantrr bren2 sylanbrc ) ACDZAEDZFZGZABHIZBAJZKIZGGUGBUFHIZFZBUFQIUDU
      EUGLUDUEUIUGUAUEUCUIUAUEGUHUBUAUEUHUBABMNOPRBUFST $.

    $( If ` A <_ B <_ ~P A ` , and ` A ` is an infinite GCH-set, then either
       ` A = B ` or ` B = ~P A ` in cardinality.  (Contributed by Mario
       Carneiro, 15-May-2015.) $)
    gchor $p |- ( ( ( A e. GCH /\ -. A e. Fin ) /\ ( A ~<_ B /\ B ~<_ ~P A ) )
      -> ( A ~~ B \/ B ~~ ~P A ) ) $=
      ( cgch wcel cfn wn wa cdom wbr cpw csdm cen wo simprr brdom2 sylib gchen1
      wi expr adantrr orim1d mpd ) ACDAEDFGZABHIZBAJZHIZGGZBUEKIZBUELIZMZABLIZU
      IMUGUFUJUCUDUFNBUEOPUGUHUKUIUCUDUHUKRUFUCUDUHUKABQSTUAUB $.

    $( The property of being a GCH-set is a cardinal invariant.  (Contributed
       by Mario Carneiro, 15-May-2015.) $)
    engch $p |- ( A ~~ B -> ( A e. GCH <-> B e. GCH ) ) $=
      ( vx cen wbr cfn wcel cv csdm cpw wa wn wal wo cgch syl cvv relen elgch
      wb enfi sdomen1 sdomen2 anbi12d notbid albidv orbi12d brrelex1i brrelex2i
      pwen 3bitr4d ) ABDEZAFGZACHZIEZUNAJZIEZKZLZCMZNZBFGZBUNIEZUNBJZIEZKZLZCMZ
      NZAOGZBOGZULUMVBUTVHABUAULUSVGCULURVFULUOVCUQVEABUNUBULUPVDDEUQVETABUJUPV
      DUNUCPUDUEUFUGULAQGVJVATABDRUHCAQSPULBQGVKVITABDRUICBQSPUK $.
  $}

  $( Under certain conditions, a GCH-set can demonstrate trichotomy of
     dominance.  Lemma for ~ gchac .  (Contributed by Mario Carneiro,
     15-May-2015.) $)
  gchdomtri $p |- ( ( A e. GCH /\ ( A |_| A ) ~~ A /\ B ~<_ ~P A ) ->
      ( A ~<_ B \/ B ~<_ A ) ) $=
    ( cgch wcel cdju cen wbr cpw cdom wo wa wn csdm sdomdom cvv djudoml syl2anc
    wb adantr 3syl w3a cfn con3i reldom brrelex1i 3ad2ant3 fidomtri2 sylan orrd
    imbitrrid simp1 djulepw 3adant1 syl22anc djucomen domentr domen2 syl5ibrcom
    simpr gchor imp olcd simpl1 canth2g simpl2 syl enen2 adantl mpbird pwdjudom
    pwen endom domtr orcd jaodan syldan pm2.61dan ) ACDZAAEZAFGZBAHZIGZUAZAUBDZ
    ABIGZBAIGZJZWCWDKZWEWFWELWFWHABMGZLZWIWEABNUCWCBODZWDWFWJRWBVRWKVTBWAIUDUEU
    FZBAOUGUHUJUIWCWDLZAABEZFGZWNWAFGZJZWGWCWMKVRWMAWNIGZWNWAIGZWQWCVRWMVRVTWBU
    KZSWCWMUSWCWRWMWCVRWKWRWTWLABCOPQSWCWSWMVTWBWSVRABULUMSAWNUTUNWCWOWGWPWCWOK
    WFWEWCWOWFWCWFWOBWNIGZWCBBAEZIGZXBWNFGZXAWCWKVRXCWLWTBAOCPQWCWKVRXDWLWTBAOC
    UOQBXBWNUPQAWNBUQURVAVBWCWPKZWEWFXEAWAIGZWABIGZWEXEVRAWAMGXFVRVTWBWPVCACVDA
    WANTXEVSHZWNFGZXHWNIGXGXEXIXHWAFGZXEVTXJVRVTWBWPVEVSAVKVFWPXIXJRWCWNWAXHVGV
    HVIXHWNVLABVJTAWABVMQVNVOVPVQ $.

  ${
    $d u y B $.  $d a b r s t u v w x y z F $.  $d a b n r s t u v w x y z X $.
    $d r u w x y z M $.  $d r u w x y z N $.  $d a b n r s t u v w x y z ph $.
    $d a r s t w x z A $.  $d r u w x y z R $.  $d r u w x y z Y $.
    $d r u x y z S $.
    fpwwe2.1 $e |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\
      ( r We x /\ A. y e. x [. ( `' r " { y } ) / u ].
        ( u F ( r i^i ( u X. u ) ) ) = y ) ) } $.
    $( Lemma for ~ fpwwe2 .  (Contributed by Mario Carneiro, 3-Jun-2015.) $)
    fpwwe2cbv $p |- W = { <. a , s >. | ( ( a C_ A /\ s C_ ( a X. a ) ) /\
      ( s We a /\ A. z e. a [. ( `' s " { z } ) / v ].
        ( v F ( s i^i ( v X. v ) ) ) = z ) ) } $=
      ( cv wss cxp wa cin wceq wsbc weq wwe co ccnv csn cima copab simpl sseq1d
      wral simpr sqxpeqd sseq12d anbi12d weeq12d ineq2d oveq12d eqeq1d cbvsbcvw
      id imaeq2d eqeq2 sbceqbid bitrid cbvralvw cnveqd imaeq1d ineq1d raleqbidv
      sneq oveq2d cbvopabv eqtri ) HAMZFNZJMZVMVMOZNZPZVMVOUAZEMZVOVTVTOZQZGUBZ
      BMZRZEVOUCZWDUDZUEZSZBVMUIZPZPZAJUFKMZFNZIMZWMWMOZNZPZWMWOUAZDMZWOWTWTOZQ
      ZGUBZCMZRZDWOUCZXDUDZUEZSZCWMUIZPZPZKIUFLWLXLAJKIAKTZJITZPZVRWRWKXKXOVNWN
      VQWQXOVMWMFXMXNUGZUHXOVOWOVPWPXMXNUJZXOVMWMXPUKULUMXOVSWSWJXJXOVMWMVOWOXQ
      XPUNWJWTVOXAQZGUBZXDRZDWFXGUEZSZCVMUIXOXJWIYBBCVMWIXSWDRZDWHSBCTZYBWEYCED
      WHEDTZWCXSWDYEVTWTWBXRGYEUSZYEWAXAVOYEVTWTYFUKUOUPUQURYDYCXTDWHYAYDWGXGWF
      WDXDVIUTWDXDXSVAVBVCVDXOYBXICVMWMXPXOXTXEDYAXHXOWFXFXGXOVOWOXQVEVFXOXSXCX
      DXOXRXBWTGXOVOWOXAXQVGVJUQVBVHVCUMUMVKVL $.

    $d a b n r s t u v w x y z W $.
    $( Lemma for ~ fpwwe2 .  (Contributed by Mario Carneiro, 15-May-2015.) $)
    fpwwe2lem1 $p |- W C_ ( ~P A X. ~P ( A X. A ) ) $=
      ( cv wss cxp wa wwe cin co copab cpw wcel velpw sylibr wceq ccnv csn cima
      wsbc wral simpll simplr xpss12 syl2anc sstrd jca ssopab2i df-xp 3sstr4i )
      AIZDJZGIZUPUPKZJZLUPURMCIZURVAVAKNEOBIZUACURUBVBUCUDUEBUPUFLZLZAGPUPDQZRZ
      URDDKZQZRZLZAGPFVEVHKVDVJAGVDVFVIVDUQVFUQUTVCUGZADSTVDURVGJVIVDURUSVGUQUT
      VCUHVDUQUQUSVGJVKVKUPDUPDUIUJUKGVGSTULUMHAGVEVHUNUO $.

    fpwwe2.2 $e |- ( ph -> A e. V ) $.
    $( Lemma for ~ fpwwe2 .  (Contributed by Mario Carneiro, 19-May-2015.)
       (Revised by AV, 20-Jul-2024.) $)
    fpwwe2lem2 $p |- ( ph -> ( X W R <-> ( ( X C_ A /\ R C_ ( X X. X ) ) /\
      ( R We X /\ A. y e. X [. ( `' R " { y } ) / u ].
        ( u F ( R i^i ( u X. u ) ) ) = y ) ) ) ) $=
      ( wss cxp wa cv wceq cvv wcel wbr wwe cin co ccnv csn cima wsbc wral wrel
      relopabiv brrelex12 sylan adantr simprll ssexd xpexd simprlr simpl sseq1d
      a1i jca simpr sqxpeqd sseq12d anbi12d weeq12d cnveqd ineq1d oveq2d eqeq1d
      imaeq1d sbceqbid raleqbidv brabga pm5.21nd ) AJFIUAZJENZFJJOZNZPZJFUBZDQZ
      FWCWCOZUCZGUDZCQZRZDFUEZWGUFZUGZUHZCJUIZPZPZJSTZFSTZPZAIUJZVQWRWSABQZENZK
      QZWTWTOZNZPZWTXBUBZWCXBWDUCZGUDZWGRZDXBUEZWJUGZUHZCWTUIZPZPZBKILUKVAJFIUL
      UMAWOPZWPWQXPJEHAEHTWOMUNAVRVTWNUOUPZXPFVSSXPJJSSXQXQUQAVRVTWNURUPVBXOWOB
      KJFISSWTJRZXBFRZPZXEWAXNWNXTXAVRXDVTXTWTJEXRXSUSZUTXTXBFXCVSXRXSVCZXTWTJY
      AVDVEVFXTXFWBXMWMXTWTJXBFYBYAVGXTXLWLCWTJYAXTXIWHDXKWKXTXJWIWJXTXBFYBVHVL
      XTXHWFWGXTXGWEWCGXTXBFWDYBVIVJVKVMVNVFVFLVOVP $.

    ${
      fpwwe2lem3.4 $e |- ( ph -> X W R ) $.
      $( Lemma for ~ fpwwe2 .  (Contributed by Mario Carneiro, 19-May-2015.)
         (Revised by AV, 20-Jul-2024.) $)
      fpwwe2lem3 $p |- ( ( ph /\ B e. X ) -> ( ( `' R " { B } ) F
        ( R i^i ( ( `' R " { B } ) X. ( `' R " { B } ) ) ) ) = B ) $=
        ( wcel wa wceq wss cvv cv cxp cin co ccnv csn cima wsbc wral fpwwe2lem2
        wwe mpbid simprrd sneq imaeq2d eqeq2 sbceqbid rspccva sylan wb cnvimass
        wbr cdm relopabiv brrelex2i dmexg 3syl ssexg sylancr id sqxpeqd oveq12d
        ineq2d eqeq1d sbcieg syl adantr ) AFKPZQDUAZGVSVSUBZUCZHUDZFRZDGUEZFUFZ
        UGZUHZWFGWFWFUBZUCZHUDZFRZAWBCUAZRZDWDWLUFZUGZUHZCKUIZVRWGAKESGKKUBSQZK
        GUKZWQAKGJVBZWRWSWQQQOABCDEGHIJKLMNUJULUMWPWGCFKWLFRZWMWCDWOWFXAWNWEWDW
        LFUNUOWLFWBUPUQURUSAWGWKUTZVRAWFTPZXBAWFGVCZSXDTPZXCGWEVAAWTGTPXEOKGJBU
        AZESLUAZXFXFUBSQXFXGUKVSXGVTUCHUDWLRDXGUEWNUGUHCXFUIQQBLJMVDVEGTVFVGWFX
        DTVHVIWCWKDWFTVSWFRZWBWJFXHVSWFWAWIHXHVJZXHVTWHGXHVSWFXIVKVMVLVNVOVPVQU
        L $.
    $}

    fpwwe2.3 $e |- ( ( ph /\ ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) ) ->
      ( x F r ) e. A ) $.
    $( Lemma for ~ fpwwe2 .  (Contributed by Mario Carneiro, 15-May-2015.)
       (Revised by AV, 20-Jul-2024.)  (Proof shortened by Matthew House,
       10-Sep-2025.) $)
    fpwwe2lem4 $p |- ( ( ph /\ ( X C_ A /\ R C_ ( X X. X ) /\ R We X ) ) ->
      ( X F R ) e. A ) $=
      ( wss cxp wwe w3a wcel cvv co wa cv adantr simpr1 ssexd xpexd simpr2 wceq
      wi simpl sseq1d simpr sqxpeqd sseq12d weeq12d 3anbi123d oveq12 imbi12d ex
      eleq1d vtocl2d syldbl2 ) AJEOZFJJPZOZJFQZRZJFGUAZESZAVHUBZBUCZEOZKUCZVLVL
      PZOZVLVNQZRZVLVNGUAZESZUJZVHVJUJBKJFTTVKJEHAEHSVHMUDAVDVFVGUEUFZVKFVETVKJ
      JTTWBWBUGAVDVFVGUHUFVLJUIZVNFUIZUBZVRVHVTVJWEVMVDVPVFVQVGWEVLJEWCWDUKZULW
      EVNFVOVEWCWDUMZWEVLJWFUNUOWEVLJVNFWGWFUPUQWEVSVIEVLJVNFGURVAUSAWAVHAVRVTN
      UTUDVBVC $.

    ${
      fpwwe2lem8.x $e |- ( ph -> X W R ) $.
      fpwwe2lem8.y $e |- ( ph -> Y W S ) $.
      fpwwe2lem8.m $e |- M = OrdIso ( R , X ) $.
      fpwwe2lem8.n $e |- N = OrdIso ( S , Y ) $.
      ${
        fpwwe2lem5.1 $e |- ( ph -> B e. dom M ) $.
        fpwwe2lem5.2 $e |- ( ph -> B e. dom N ) $.
        fpwwe2lem5.3 $e |- ( ph -> ( M |` B ) = ( N |` B ) ) $.
        $( Lemma for ~ fpwwe2 .  (Contributed by Mario Carneiro, 18-May-2015.)
           (Revised by AV, 20-Jul-2024.) $)
        fpwwe2lem5 $p |- ( ( ph /\ C R ( M ` B ) ) ->
          ( C e. X /\ C e. Y /\ ( `' M ` C ) = ( `' N ` C ) ) ) $=
          ( cfv wbr wa wcel ccnv wceq cxp wss wwe cv cin co csn cima fpwwe2lem2
          wsbc wral mpbid simplrd brxp simplbi syl6 imp crn imassrn cdm wfo cep
          ssbrd wf1o wiso cvv relopabiv brrelex1i simprld syl2anc adantr isof1o
          syl oiiso f1ofo forn 3syl sseqtrid f1ocnvfv2 simpr eqbrtrd wb wf f1of
          f1ocnv ffvelcdmd isorel syl12anc mpbird epelg wfn mpbir2and imacnvcnv
          ffn elpreima eleqtrdi cres rneqd df-ima 3eqtr4g eleqtrd sseldd cnveqd
          wfun dff1o3 simprbi funcnvres 3eqtr3d fveq1d fvresd 3jca ) AGFKUHZHUI
          ZUJZGOUKZGPUKGKULZUHZGLULZUHZUMAYFYHAYFGYEOOUNZUIZYHAHYMGYEAOEUOZHYMU
          OZOHUPZDUQZHYRYRUNZURJUSCUQZUMDHULYTUTZVAVCCOVDZUJZAOHNUIZYOYPUJZUUCU
          JUAABCDEHJMNOQRSVBVEZVFVPYNYHYEOUKGYEOOVGVHVIVJZYGLFVAZPGYGLVKZUUHPLF
          VLYGLVMZPLVQZUUJPLVNZUUIPUMYGUUJPVOILVRZUUKAUUMYFAPVSUKZPIUPZUUMAPINU
          IZUUNUBPINBUQZEUOQUQZUUQUUQUNUOUJUUQUURUPYRUURYSURJUSYTUMDUURULUUAVAV
          CCUUQVDUJUJBQNRVTZWAWFAPEUOIPPUNUOUJZUUOYRIYSURJUSYTUMDIULUUAVAVCCPVD
          ZAUUPUUTUUOUVAUJUJUBABCDEIJMNPQRSVBVEWBPILVSUDWGWCWDUUJPVOILWEWFZUUJP
          LWHUUJPLWIWJWKYGGKFVAZUUHYGGYIULFVAZUVCYGGUVDUKZYHYJFUKZUUGYGYJFVOUIZ
          UVFYGUVGYJKUHZYEHUIZYGUVHGYEHYGKVMZOKVQZYHUVHGUMYGUVJOVOHKVRZUVKAUVLY
          FAOVSUKZYQUVLAUUDUVMUAOHNUUSWAWFAUUEYQUUBUUFWBOHKVSUCWGWCWDZUVJOVOHKW
          EWFZUUGUVJOGKWLWCAYFWMWNYGUVLYJUVJUKFUVJUKZUVGUVIWOUVNYGOUVJGYIYGUVKO
          UVJYIVQOUVJYIWPZUVOUVJOKWROUVJYIWQWJZUUGWSAUVPYFUEWDZUVJOYJFVOHKWTXAX
          BYGUVPUVGUVFWOUVSYJFUVJXCWFVEYGUVQYIOXDUVEYHUVFUJWOUVROUVJYIXGOGFYIXH
          WJXEKFXFXIZYGKFXJZVKLFXJZVKUVCUUHYGUWAUWBAUWAUWBUMYFUGWDZXKKFXLLFXLXM
          XNZXOYGGYIUVCXJZUHGYKUUHXJZUHYJYLYGGUWEUWFYGUWAULZUWBULZUWEUWFYGUWAUW
          BUWCXPYGUVKYIXQZUWGUWEUMUVOUVKUVJOKVNUWIUVJOKXRXSFKXTWJYGUUKYKXQZUWHU
          WFUMUVBUUKUULUWJUUJPLXRXSFLXTWJYAYBYGGUVCYIUVTYCYGGUUHYKUWDYCYAYD $.

        $( Lemma for ~ fpwwe2 .  (Contributed by Mario Carneiro, 18-May-2015.)
           (Revised by AV, 20-Jul-2024.) $)
        fpwwe2lem6 $p |- ( ( ph /\ C R ( M ` B ) ) -> ( C S ( N ` B ) /\
          ( D R ( M ` B ) -> ( C R D <-> C S D ) ) ) ) $=
          ( cfv wbr wa wb wi ccnv cdm wf1o wcel wceq cep cvv wwe cv wss cxp cin
          wiso co csn cima wsbc wral relopabiv brrelex1i syl fpwwe2lem2 simprld
          mpbid syl2anc adantr isof1o fpwwe2lem5 simp2d f1ocnvfv2 simp3d simp1d
          oiiso simpr eqbrtrd f1ocnv f1of 3syl ffvelcdmd isorel syl12anc mpbird
          wf eqbrtrrd adantrr adantrl breq12d isocnv simplrd ssbrd brxp simplbi
          imp 3bitr4d expr jca ) AGFLUIZIUJZUKZGFMUIZJUJHXJIUJZGHIUJZGHJUJZULZU
          MXLGMUNZUIZMUIZGXMJXLMUOZQMUPZGQUQZXTGURXLYAQUSJMVFZYBAYDXKAQUTUQZQJV
          AZYDAQJOUJZYEUCQJOBVBZEVCRVBZYHYHVDVCUKYHYIVADVBZYIYJYJVDZVEKVGCVBZUR
          DYIUNYLVHZVIVJCYHVKUKUKBROSVLZVMVNAQEVCJQQVDVCUKZYFYJJYKVEKVGYLURDJUN
          YMVIVJCQVKZAYGYOYFYPUKUKUCABCDEJKNOQRSTVOVQVPQJMUTUEWFVRZVSZYAQUSJMVT
          VNZXLGPUQZYCGLUNZUIZXSURZABCDEFGIJKLMNOPQRSTUAUBUCUDUEUFUGUHWAZWBZYAQ
          GMWCVRXLXSFUSUJZXTXMJUJZXLUUBXSFUSXLYTYCUUCUUDWDZXLUUBFUSUJZUUBLUIZXJ
          IUJZXLUUJGXJIXLLUOZPLUPZYTUUJGURXLUULPUSILVFZUUMAUUNXKAPUTUQZPIVAZUUN
          APIOUJZUUOUBPIOYNVMVNAPEVCZIPPVDZVCZUKZUUPYJIYKVEKVGYLURDIUNYMVIVJCPV
          KZAUUQUVAUUPUVBUKZUKUBABCDEIKNOPRSTVOVQZVPPILUTUDWFVRZVSZUULPUSILVTVN
          ZXLYTYCUUCUUDWEZUULPGLWCVRAXKWGWHXLUUNUUBUULUQFUULUQZUUIUUKULUVFXLPUU
          LGUUAXLUUMPUULUUAUPPUULUUAWPUVGUULPLWIPUULUUAWJWKUVHWLAUVIXKUFVSUULPU
          UBFUSILWMWNWOWQXLYDXSYAUQFYAUQZUUFUUGULYRXLQYAGXRXLYBQYAXRUPQYAXRWPYS
          YAQMWIQYAXRWJWKUUEWLAUVJXKUGVSYAQXSFUSJMWMWNVQWQAXKXNXQAXKXNUKZUKZUUB
          HUUAUIZUSUJZXSHXRUIZUSUJZXOXPUVLUUBXSUVMUVOUSAXKUUCXNUUHWRAXNUVMUVOUR
          ZXKAXNUKZHPUQZHQUQZUVQABCDEFHIJKLMNOPQRSTUAUBUCUDUEUFUGUHWAZWDWSWTUVL
          PUULIUSUUAVFZYTUVSXOUVNULUVLUUNUWBAUUNUVKUVEVSUULPUSILXAVNAXKYTXNUVHW
          RAXNUVSXKUVRHXJUUSUJZUVSAXNUWCAIUUSHXJAUURUUTUVCUVDXBXCXFUWCUVSXJPUQH
          XJPPXDXEVNWSPUULGHIUSUUAWMWNUVLQYAJUSXRVFZYCUVTXPUVPULUVLYDUWDAYDUVKY
          QVSYAQUSJMXAVNAXKYCXNUUEWRAXNUVTXKUVRUVSUVTUVQUWAWBWSQYAGHJUSXRWMWNXG
          XHXI $.
      $}

      fpwwe2lem8.s $e |- ( ph -> dom M C_ dom N ) $.
      $( Lemma for ~ fpwwe2 .  Show by induction that the two isometries ` M `
         and ` N ` agree on their common domain.  (Contributed by Mario
         Carneiro, 15-May-2015.)  (Proof shortened by Peter Mazsa,
         23-Sep-2022.)  (Revised by AV, 20-Jul-2024.) $)
      fpwwe2lem7 $p |- ( ph -> M = ( N |` dom M ) ) $=
        ( vw vz cdm cres wf wfn oif ffn mp1i fnssresd cv wcel wa wceq con0 word
        cfv oicl ordelon mpan wi eleq1w eqeq12d imbi12d imbi2d wral r19.21v wss
        fveq2 a1i ordelss sselda pm2.27 syl ralimdva wb fnssres syl2an2r adantr
        sylan sstrd eqfnfv syl2anc fvres ralbiia bitrdi ccnv csn cxp cin co wbr
        cima ad2antrr wwe w3a simpll simplr simpr fpwwe2lem6 simpld impbida cvv
        eqcomd fvex vex eliniseg ax-mp 3bitr4g eqrdv relinxp cop anbi12d simprd
        impr sylan2b pm5.32da df-br brinxp2 bitr3i sqxpeqd ineq2d eqtrd oveq12d
        eqrelrdv ffvelcdmi adantl fpwwe2lem3 3eqtr3d ex sylbird com23 a2i sylbi
        syld tfis2 com3l mpdi imp eqtr4d eqfnfvd ) AUDIUFZIJUUEUGZUUEMIUHIUUEUI
        ZAMFIUAUJZUUEMIUKULZAJUFZUUEJUUJNJUHJUUJUIZANGJUBUJZUUJNJUKULZUCUMAUDUN
        ZUUEUOZUPZUUNIUTZUUNJUTZUUNUUFUTZAUUOUUQUURUQZAUUOUUNURUOZUUTUUEUSZUUOU
        VAMFIUAVAZUUEUUNVBVCUVAAUUOUUTAUUOUUTVDZVDZACUNZUUEUOZUVFIUTZUVFJUTZUQZ
        VDZVDZUDCUUNUVFUQZUVDUVKAUVMUUOUVGUUTUVJUDCUUEVEUVMUUQUVHUURUVIUUNUVFIV
        LUUNUVFJVLVFVGVHUVLCUUNVIZUVEVDUVAUVNAUVKCUUNVIZVDUVEAUVKCUUNVJAUVOUVDA
        UUOUVOUUTAUUOUVOUUTVDUUPUVOUVJCUUNVIZUUTUUPUVKUVJCUUNUUPUVFUUNUOZUPUVGU
        VKUVJVDUUPUUNUUEUVFAUVBUUOUUNUUEVKZUVBAUVCVMUUEUUNVNWCZVOUVGUVJVPVQVRUU
        PUVPIUUNUGZJUUNUGZUQZUUTUUPUWBUVFUVTUTZUVFUWAUTZUQZCUUNVIZUVPUUPUVTUUNU
        IZUWAUUNUIZUWBUWFVSAUUGUUOUVRUWGUUIUVSUUEUUNIVTWAAUUKUUOUUNUUJVKUWHUUMU
        UPUUNUUEUUJUVSAUUEUUJVKUUOUCWBWDUUJUUNJVTWACUUNUVTUWAWEWFUWEUVJCUUNUVQU
        WCUVHUWDUVIUVFUUNIWGUVFUUNJWGVFWHWIUUPUWBUUTUUPUWBUPZFWJUUQWKWPZFUWJUWJ
        WLZWMZHWNZGWJUURWKWPZGUWNUWNWLZWMZHWNZUUQUURUWIUWJUWNUWLUWPHUWICUWJUWNU
        WIUVFUUQFWOZUVFUURGWOZUVFUWJUOZUVFUWNUOZUWIUWRUWSUWIUWRUPZUWSUEUNZUUQFW
        OZUVFUXCFWOZUVFUXCGWOZVSZVDZUWIBCDEUUNUVFUXCFGHIJKLMNOPAEKUOUUOUWBQWQZU
        WIABUNZEVKOUNZUXJUXJWLVKUXJUXKWRWSUXJUXKHWNEUOAUUOUWBWTZRWCZAMFLWOUUOUW
        BSWQZANGLWOUUOUWBTWQZUAUBAUUOUWBXAZUUPUUNUUJUOZUWBAUUEUUJUUNUCVOZWBZUUP
        UWBXBZXCZXDUWIUWSUPUWRUXCUURGWOUXFUXEVSVDUWIBCDEUUNUVFUXCGFHJIKLNMOPUXI
        UXMUXOUXNUBUAUXSUXPUWIUVTUWAUXTXGXCXDXEUUQXFUOZUWTUWRVSUUNIXHZFUUQUVFXF
        CXIZXJZXKUURXFUOUXAUWSVSUUNJXHGUURUVFXFUYDXJXKXLXMZUWIUWLGUWKWMZUWPUWIC
        UEUWLUYGUWJUWJFXNUWJUWJGXNUWIUWTUXCUWJUOZUPZUXEUPZUYIUXFUPZUVFUXCXOZUWL
        UOZUYLUYGUOZUWIUYIUXEUXFUYIUWIUWRUXDUPZUXGUYBUYIUYOVSUYCUYBUWTUWRUYHUXD
        UYEFUUQUXCXFUEXIXJXPXKUWIUWRUXDUXGUXBUWSUXHUYAXQXRXSXTUYMUVFUXCUWLWOUYJ
        UVFUXCUWLYAUWJUWJUVFUXCFYBYCUYNUVFUXCUYGWOUYKUVFUXCUYGYAUWJUWJUVFUXCGYB
        YCXLYHUWIUWKUWOGUWIUWJUWNUYFYDYEYFYGUWIAUUQMUOZUWMUUQUQUXLUUPUYPUWBUUOU
        YPAUUEMUUNIUUHYIYJWBABCDEUUQFHKLMOPQSYKWFUWIAUURNUOZUWQUURUQUXLUUPUYQUW
        BUUPUXQUYQUXRUUJNUUNJUULYIVQWBABCDEUURGHKLNOPQTYKWFYLYMYNYRYMYOYPYQVMYS
        YTUUAUUBUUOUUSUURUQAUUNUUEJWGYJUUCUUD $.

      $( Lemma for ~ fpwwe2 .  Given two well-orders ` <. X , R >. ` and
         ` <. Y , S >. ` of parts of ` A ` , one is an initial segment of the
         other.  (The ` O C_ P ` hypothesis is in order to break the symmetry
         of ` X ` and ` Y ` .)  (Contributed by Mario Carneiro, 15-May-2015.)
         (Proof shortened by Peter Mazsa, 23-Sep-2022.)  (Revised by AV,
         20-Jul-2024.) $)
      fpwwe2lem8 $p |- ( ph -> ( X C_ Y /\ R = ( S i^i ( Y X. X ) ) ) ) $=
        ( wss cxp cin wceq cdm cima cres crn cep wiso wf1o wfo cvv wcel wwe wbr
        cv wa co ccnv csn wsbc relopabiv brrelex1i syl fpwwe2lem2 mpbid simprld
        wral oiiso syl2anc isof1o f1ofo fpwwe2lem7 rneqd eqtr3d eqtr4di imassrn
        forn 4syl df-ima sseqtrid eqsstrd wrel simplrd relxp relss mpisyl jctir
        relinxp cop ssbrd brxp imbitrdi brinxp2 wfn isocnv adantr f1ofn simprll
        3syl cfv simprr wb simprlr sseldd isorel syl12anc fvex epeli sylib wfun
        cnveqd fnfun funcnvres fveq1d eleqtrd fvresd wf f1of ffvelcdmd eqeltrrd
        eqtrd word wi ordtr1 ax-mp elpreimad imacnvcnv eleqtrrd jca ex biimtrid
        oicl breq12d sylan df-br eqidd isores3 syl3anc simprl 3bitr4d biantrurd
        sselda adantrr bitr4di bitrd pm5.21ndd 3bitr3g eqrelrdv2 mpancom ) AMNU
        DZFGNMUEUFZUGZAMJIUHZUIZNAMJUURUJZUKZUUSAIUKZMUVAAUURMULFIUMZUURMIUNUUR
        MIUOUVBMUGAMUPUQZMFURZUVCAMFLUSZUVDSMFLBUTZEUDOUTZUVGUVGUEUDVAUVGUVHURD
        UTZUVHUVIUVIUEZUFHVBCUTZUGDUVHVCUVKVDZUIVECUVGVLVAVABOLPVFZVGVHAMEUDZFM
        MUEZUDZVAZUVEUVIFUVJUFHVBUVKUGDFVCUVLUIVECMVLZAUVFUVQUVEUVRVAZVASABCDEF
        HKLMOPQVIVJZVKMFIUPUAVMVNZUURMULFIVOUURMIVPUURMIWBWCAIUUTABCDEFGHIJKLMN
        OPQRSTUAUBUCVQZVRVSJUURWDVTZAJUKZUUSNJUURWAAJUHZNULGJUMZUWENJUNUWENJUOU
        WDNUGANUPUQZNGURZUWFANGLUSZUWGTNGLUVMVGVHANEUDGNNUEUDVAZUWHUVIGUVJUFHVB
        UVKUGDGVCUVLUIVECNVLZAUWIUWJUWHUWKVAVATABCDEGHKLNOPQVIVJVKNGJUPUBVMVNZU
        WENULGJVOUWENJVPUWENJWBWCWEWFZFWGZUUPWGZVAAUUQAUWNUWOAUVPUVOWGUWNAUVNUV
        PUVSUVTWHZMMWIFUVOWJWKNMGWMWLABCFUUPAUVGUVKFUSZUVGUVKUUPUSZUVGUVKWNZFUQ
        UWSUUPUQAUVGMUQZUVKMUQZVAZUWQUWRAUWQUVGUVKUVOUSUXBAFUVOUVGUVKUWPWOUVGUV
        KMMWPWQUWRUVGNUQZUXAVAZUVGUVKGUSZVAZAUXBNMUVGUVKGWRZAUXFUXBAUXFVAZUWTUX
        AUXHUVGJVCZVCUURUIZMUXHNUVGUURUXIUXHNUWEGULUXIUMZNUWEUXIUNUXINWSZAUXKUX
        FAUWFUXKUWLUWENULGJWTVHXAZNUWEGULUXIVONUWEUXIXBXDZAUXCUXAUXEXCZUXHUVGUX
        IXEZUVKUXIXEZUQZUXQUURUQZUXPUURUQZUXHUXPUXQULUSZUXRUXHUXEUYAAUXDUXEXFUX
        HUXKUXCUVKNUQUXEUYAXGUXMUXOUXHMNUVKAUUOUXFUWMXAAUXCUXAUXEXHZXINUWEUVGUV
        KGULUXIXJXKVJUXPUXQUVKUXIXLXMXNUXHUVKIVCZXEZUXQUURUXHUYDUVKUXIUUSUJZXEU
        XQUXHUVKUYCUYEUXHUYCUUTVCZUYEUXHIUUTAIUUTUGZUXFUWBXAXPUXHUXLUXIXOUYFUYE
        UGUXNNUXIXQUURJXRXDYFXSUXHUVKUUSUXIUXHUVKMUUSUYBAMUUSUGZUXFUWCXAZXTYAYF
        UXHMUURUVKUYCAMUURUYCYBZUXFAUVCMUURFULUYCUMZMUURUYCUNUYJUWAUURMULFIWTZM
        UURFULUYCVOMUURUYCYCWCXAUYBYDYEUURYGUXRUXSVAUXTYHMFIUAYQUXPUXQUURYIYJVN
        YKUXHMUUSUXJUYIJUURYLVTYMUYBYNYOYPAUXBUWQUWRXGAUXBVAZUWQUXEUWRUYMUVGUYC
        XEZUYDULUSZUVGUYFXEZUVKUYFXEZULUSZUWQUXEUYMUYNUYPUYDUYQULUYMUVGUYCUYFUY
        MIUUTAUYGUXBUWBXAXPZXSUYMUVKUYCUYFUYSXSYRAUYKUXBUWQUYOXGAUVCUYKUWAUYLVH
        MUURUVGUVKFULUYCXJYSUYMUUSUURGULUYFUMZUVGUUSUQUVKUUSUQUXEUYRXGAUYTUXBAU
        URUUSULGUUTUMZUYTAUWFUURUWEUDUUSUUSUGVUAUWLUCAUUSUUAUWENULGJUURUUSUUBUU
        CUURUUSULGUUTWTVHXAUYMUVGMUUSAUWTUXAUUDAUYHUXBUWCXAZXTUYMUVKMUUSAUWTUXA
        XFZVUBXTUUSUURUVGUVKGULUYFXJXKUUEUYMUXEUXFUWRUYMUXDUXEUYMUXCUXAAUWTUXCU
        XAAMNUVGUWMUUGUUHVUCYNUUFUXGUUIUUJYOUUKUVGUVKFYTUVGUVKUUPYTUULUUMUUNYN
        $.
    $}

    ${
      fpwwe2lem9.4 $e |- ( ph -> X W R ) $.
      fpwwe2lem9.6 $e |- ( ph -> Y W S ) $.
      $( Lemma for ~ fpwwe2 .  Given two well-orders ` <. X , R >. ` and
         ` <. Y , S >. ` of parts of ` A ` , one is an initial segment of the
         other.  (Contributed by Mario Carneiro, 15-May-2015.)  (Revised by AV,
         20-Jul-2024.) $)
      fpwwe2lem9 $p |- ( ph -> ( ( X C_ Y /\ R = ( S i^i ( Y X. X ) ) ) \/
                                ( Y C_ X /\ S = ( R i^i ( X X. Y ) ) ) ) ) $=
        ( wss adantr coi cdm wo cxp cin wceq wa word eqid oicl ordtri2or2 mp2an
        wcel cv wwe w3a co adantlr wbr simpr fpwwe2lem8 ex orim12d mpi ) AKFUAZ
        UBZLGUAZUBZSZVHVFSZUCZKLSFGLKUDUEUFUGZLKSGFKLUDUEUFUGZUCVFUHVHUHVKKFVEV
        EUIZUJLGVGVGUIZUJVFVHUKULAVIVLVJVMAVIVLAVIUGBCDEFGHVEVGIJKLMNAEIUMZVIOT
        ABUNZESMUNZVQVQUDSVQVRUOUPZVQVRHUQEUMZVIPURAKFJUSZVIQTALGJUSZVIRTVNVOAV
        IUTVAVBAVJVMAVJUGBCDEGFHVGVEIJLKMNAVPVJOTAVSVTVJPURAWBVJRTAWAVJQTVOVNAV
        JUTVAVBVCVD $.
    $}

    fpwwe2.4 $e |- X = U. dom W $.
    $( Lemma for ~ fpwwe2 .  (Contributed by Mario Carneiro, 15-May-2015.)
       (Revised by AV, 20-Jul-2024.) $)
    fpwwe2lem10 $p |- ( ph -> W : dom W --> ~P ( X X. X ) ) $=
      ( vw vs wss cv wa wceq vt cdm wfn crn cxp cpw wf wrel wbr wi wal wfun wwe
      cin co ccnv csn cima wsbc relopabiv a1i simprr fpwwe2lem2 simprbda simprd
      wral adantrl adantr dfss2 sylib eqtrd adantrr wcel w3a adantlr fpwwe2lem9
      eqtr2d simprl mpjaodan ex alrimiv alrimivv dffun2 sylanbrc funfnd wex vex
      elrn releldmi adantl elssuni syl sseqtrrdi xpss12 syl2anc sstrd imbitrrdi
      cuni velpw exlimdv biimtrid ssrdv df-f ) AHHUBZUCHUDZIIUEZUFZQXDXGHUGAHAH
      UHZORZPRZHUIZXIUARZHUIZSZXJXLTZUJZUAUKZPUKOUKHULXHABRZEQZJRZXRXRUEQZSXRXT
      UMZDRZXTYCYCUEZUNFUOCRZTDXTUPYEUQZURUSCXRVFSSBJHKUTZVAAXQOPAXPUAAXNXOAXNS
      ZXIXIQZXJXLXIXIUEZUNZTZSZXOYIXLXJYJUNZTZSZYHYMSZXJYKXLYHYIYLVBYQXLYJQZYKX
      LTYHYRYMAXMYRXKAXMSXIEQZYRAXMYSYRSXIXLUMYCXLYDUNFUOYETDXLUPYFURUSCXIVFSAB
      CDEXLFGHXIJKLVCVDVEVGVHXLYJVIVJVKYHYPSZXLYNXJYHYIYOVBYTXJYJQZYNXJTYHUUAYP
      AXKUUAXMAXKSZYSUUAAXKYSUUASXIXJUMYCXJYDUNFUOYETDXJUPYFURUSCXIVFSABCDEXJFG
      HXIJKLVCVDVEZVLVHXJYJVIVJVQYHBCDEXJXLFGHXIXIJKAEGVMXNLVHAXSYAYBVNXRXTFUOE
      VMXNMVOAXKXMVRAXKXMVBVPVSVTWAWBOPUAHWCWDWEAPXEXGXJXEVMXKOWFAXJXGVMZOXJHPW
      GWHAXKUUDOAXKXJXFQZUUDAXKUUEUUBXJYJXFUUCUUBXIIQZUUFYJXFQUUBXIXDWRZIUUBXIX
      DVMZXIUUGQXKUUHAXIXJHYGWIWJXIXDWKWLNWMZUUIXIIXIIWNWOWPVTPXFWSWQWTXAXBXDXG
      HXCWD $.

    $( Lemma for ~ fpwwe2 .  (Contributed by Mario Carneiro, 18-May-2015.)
       (Proof shortened by Peter Mazsa, 23-Sep-2022.)  (Revised by AV,
       20-Jul-2024.) $)
    fpwwe2lem11 $p |- ( ph -> X e. dom W ) $=
      ( va vw wbr wcel wss wa vs vn vv vz vt vb cuni cdm cxp wwe cv cin co wceq
      ccnv cima wsbc wral cpw wex vex fpwwe2lem2 simpld velpw sylibr ex exlimdv
      eldm biimtrid ssrdv sspwuni sylib elrn simprd releldmi adantl elssuni syl
      syl2anc jca wfr w3o c0 wne wn wrex wi wal eleq2i eluni2 bitri cvv simplrr
      a1i simprr simprl cop df-br adantr ad2antrr wb syl12anc ssbrd mpd simplbi
      brxp brinxp2 breqd mpbird elind sseldd eqsstrdi wo mpjaodan expr rexlimdv
      biimtrrid exp32 alrimiv anbi12i wor weso simplrl solin relelrni 3orim123d
      bitr4i idd adantrr ad2antrl ssexd imp impr sylan2 impbid eliniseg 3bitr4g
      breq2 elv relinxp crn csn simprbda eqsstrid relopabiv sseqtrrdi xpss12 n0
      sstrd ssel2 inex2 simplbda ad2ant2r wefr inss2 inelcm fri syl22anc elin1d
      ralnex simprll simp-4l simprlr mpbid elin2d syl21anbrc breq1 rspcev inss1
      adantlr fpwwe2lem9 mtod ralrimiva reximssdv expimpd df-fr reeanv exdistrv
      w3a ad2antll exp31 exlimdvv rexlimdvv ralrimivv dfwe2 sylanbrc fpwwe2lem3
      fpwwe2cbv simpr anasss cnvimass xpexd dmexd ssexg sylancr id olc syl6 a1d
      elequ1 biimprd jaodan jctird imbitrrdi ancld bitrdi sylibrd com24 imbi12d
      brin equsalvw eqrdv sylan9eqr sqxpeqd ineq2d anbi12d orc adantrl pm5.32da
      sylan2b bitr3i eqrelrdv eqtrd oveq12d eqeq1d sbcied ralrimiv mpbir2and )
      AIHUUAZUGZHQZIHUHZRAUYKIESZUYJIIUIZSZTIUYJUJZDUKZUYJUYQUYQUIZULZFUMZCUKZU
      NZDUYJUOVUAUUBZUPZUQZCIURZTAUYMUYOAIUYLUGZENAUYLEUSZSVUGESAOUYLVUHOUKZUYL
      RZVUIUAUKZHQZUAUTZAVUIVUHRZUAVUIHOVAZVHZAVULVUNUAAVULVUNAVULTZVUIESZVUNVU
      QVURVUKVUIVUIUIZSZAVULVURVUTTZVUIVUKUJZUYQVUKUYRULFUMVUAUNDVUKUOVUCUPZUQC
      VUIURZTZABCDEVUKFGHVUIJKLVBZUUCZVCOEVDVEVFVGVIVJUYLEVKVLUUDZAUYIUYNUSZSUY
      OAUAUYIVVIVUKUYIRZVULOUTAVUKVVIRZOVUKHUAVAVMAVULVVKOAVULVVKVUQVUKUYNSVVKV
      UQVUKVUSUYNVUQVURVUTVVGVNZVUQVUIISZVVMVUSUYNSVUQVUIVUGIVUQVUJVUIVUGSVULVU
      JAVUIVUKHBUKZESZJUKZVVNVVNUISZTVVNVVPUJZUYQVVPUYRULFUMVUAUNDVVPUOVUCUPUQC
      VVNURTTBJHKUUEZVOVPVUIUYLVQVRNUUFZVVTVUIIVUIIUUGVSUUIUAUYNVDVEVFVGVIVJUYI
      UYNVKVLZVTAUYPVUFAIUYJWAZVUAPUKZUYJQZVUAVWCUNZVWCVUAUYJQZWBZPIURCIURUYPAU
      BUKZISZVWHWCWDZTVWCUCUKZUYJQZWEZPVWHURZUCVWHWFZWGZUBWHVWBAVWPUBAVWIVWJVWO
      VWJVUAVWHRZCUTAVWITZVWOCVWHUUHVWRVWQVWOCAVWIVWQVWOAVWIVWQTZTZVUAVUIRZOUYL
      WFZVWOVWTVUAIRZVXBVWSVXCAVWHIVUAUUJVPVXCVUAVUGRVXBIVUGVUANWIOVUAUYLWJWKZV
      LVWTVXAVWOOUYLVUJVUMVWTVXAVWOWGZVUPVWTVULVXEUAVWTVULVXAVWOVWTVULVXATZTZUD
      UKZVWKVUKQZWEUDVWHVUIULZURZVWNUCVWHVXJVXGVXJWLRZVUIVUKWAZVXJVUISZVXJWCWDZ
      VXKUCVXJWFVXLVXGVUIVWHVUOUUKWNVXGVVBVXMAVULVVBVWSVXAVUQVVBVVDAVULVVAVVEVV
      FUULVCZUUMVUIVUKUUNVRVXNVXGVWHVUIUUOWNVXGVWQVXAVXOAVWIVWQVXFWMVWTVULVXAWO
      VUAVWHVUIUUPVSUCUDVUIVXJWLVUKUUQUURVXGVWKVXJRZVXKTZTZVWHVUIVWKVXGVXQVXKWP
      ZUUSVXSVWMPVWHVXSVWCVWHRZTZVWLVXIUDVXJWFZVYBVXKVYCWEVXGVXQVXKVYAWMVXIUDVX
      JUUTVLVWLVWCVWKWQZUEUKZRZUEUYIWFZVYBVYCVWLVYDUYJRVYGVWCVWKUYJWRUEVYDUYIWJ
      WKVYBVYFVYCUEUYIVYEUYIRZUFUKZVYEHQZUFUTZVYBVYFVYCWGZUFVYEHUEVAVMZVYBVYJVY
      LUFVXSVYAVYJVYLVYFVWCVWKVYEQZVXSVYAVYJTZTVYCVWCVWKVYEWRVXSVYOVYNVYCVXSVYO
      VYNTZTZVUIVYISZVUKVYEVYIVUIUIZULZUNZTZVYCVYIVUISZVYEVUKVUIVYIUIZULZUNZTZV
      YQWUBTZVWCVXJRZVWCVWKVUKQZVYCWUHVWHVUIVWCVYQVYAWUBVXSVYAVYJVYNUVAZWSWUHVW
      CVWKVUSQZVWCVUIRZWUHWUJWULWUHWUJVWCVWKVYTQZWUHVWCVYIRZVWKVUIRZVYNWUNVYQWU
      OWUBVYQVWCVWKVYIVYIUIZQZWUOVYQVYNWURVXSVYOVYNWOVYQVYEWUQVWCVWKVYQAVULVYJV
      YEWUQSZAVWSVXFVXRVYPUVBZVXGVULVXRVYPVWTVULVXAWPWTZVXSVYAVYJVYNUVCZAVULVYJ
      TZTZVYIESZWUSWVDWVEWUSTZVYIVYEUJZUYQVYEUYRULFUMVUAUNDVYEUOVUCUPUQCVYIURZT
      ZWVDVYJWVFWVITZAVULVYJWOZAVYJWVJXAWVCABCDEVYEFGHVYIJKLVBWSUVDZVCVNZXBXCXD
      WURWUOVWKVYIRVWCVWKVYIVYIXFXEVRZWSVXSWUPVYPWUBVXSVWHVUIVWKVXTUVEWTVXSVYOV
      YNWUBWMVYIVUIVWCVWKVYEXGUVFWUHVUKVYTVWCVWKVYQVYRWUAWOXHXIZWUHVUKVUSVWCVWK
      VYQVUTWUBVYQAVULVUTWUTWVAVVLVSWSXCXDWULWUMWUPVWCVWKVUIVUIXFXEVRXJWVOVXIWU
      JUDVWCVXJVXHVWCVWKVUKUVGUVHZVSVYQWUGTZWUIWUJVYCWVQVWHVUIVWCVYQVYAWUGWUKWS
      WVQVYIVUIVWCVYQWUCWUFWPVYQWUOWUGWVNWSXKXJWVQVYNWUJVXSVYOVYNWUGWMWVQVYEVUK
      VWCVWKWVQVYEWUEVUKVYQWUCWUFWOVUKWUDUVIZXLXCXDWVPVSVYQAVULVYJWUBWUGXMZWUTW
      VAWVBWVDBCDEVUKVYEFGHVUIVYIJKAEGRZWVCLWSAVVOVVQVVRUVSVVNVVPFUMERWVCMUVJAV
      ULVYJWPWVKUVKZXBXNXOXQXOVGVIXPVIUVLUVMUVNXRVGVIXPXDXOVGVIUVOXSUBUCPIUYJUV
      PVEAVWGCPIIVXCVWCIRZTZVXAWUOTZUFUYLWFOUYLWFZAVWGWWCVXBWUOUFUYLWFZTWWEVXCV
      XBWWBWWFVXDWWBVWCVUGRWWFIVUGVWCNWIUFVWCUYLWJWKXTVXAWUOOUFUYLUYLUVQYGAWWDV
      WGOUFUYLUYLVUJVYIUYLRZTZWVCUEUTUAUTZAWWDVWGWGZWWHVUMVYJUEUTZTWWIVUJVUMWWG
      WWKVUPUEVYIHUFVAVHXTVULVYJUAUEUVRYGAWVCWWJUAUEAWVCWWDVWGWVDWWDTZWUBVWGWUG
      WWLWUBTZVUAVWCVYEQZVWEVWCVUAVYEQZWBZVWGWWMVYIVYEYAZVUAVYIRWUOWWPWWMWVGWWQ
      WVDWVGWWDWUBWVDWVGWVHWVDWVFWVIWVLVNVCWTVYIVYEYBVRWWMVUIVYIVUAWWLVYRWUAWPW
      VDVXAWUOWUBYCXKWVDVXAWUOWUBWMVYIVUAVWCVYEYDXBWWMWWNVWDVWEVWEWWOVWFWWMVYEU
      YJVUAVWCWWMVYHVYEUYJSWVDVYHWWDWUBVYJVYHAVULVYIVYEHVVSYEUVTWTVYEUYIVQVRZXC
      WWMVWEYHWWMVYEUYJVWCVUAWWRXCYFXDWWLWUGTZVUAVWCVUKQZVWEVWCVUAVUKQZWBZVWGWW
      SVUIVUKYAZVXAWUMWXBWWSVVBWXCWVDVVBWWDWUGAVULVVBVYJVXPYIWTVUIVUKYBVRWVDVXA
      WUOWUGYCWWSVYIVUIVWCWWLWUCWUFWPWVDVXAWUOWUGWMXKVUIVUAVWCVUKYDXBWWSWWTVWDV
      WEVWEWXAVWFWWSVUKUYJVUAVWCWWSVVJVUKUYJSZWVDVVJWWDWUGVULVVJAVYJVUIVUKHVVSY
      EZYJWTVUKUYIVQZVRZXCWWSVWEYHWWSVUKUYJVWCVUAWXGXCYFXDWVDWVSWWDWWAWSXNUWAUW
      BVIUWCVIUWDCPIUYJUWEUWFAVUECIVXCVXBAVUEVXDAVXAVUEOUYLVUJVUMAVXAVUEWGZVUPA
      VULWXHUAAVULVXAVUEAVXFTZVUEVVCVUKVVCVVCUIZULZFUMZVUAUNZAVULVXAWXMVUQUDPUF
      EVUAVUKFGHVUIUEBCPUFDEFHUEJUDKUWHAWVTVULLWSAVULUWIUWGUWJWXIVUBWXMDVUDWLWX
      IVUDUYJUHZSWXNWLRVUDWLRUYJVUCUWKWXIUYJWLAUYJWLRVXFAUYJUYNWLAIIWLWLAIEGLVV
      HYKZWXOUWLVWAYKWSUWMVUDWXNWLUWNUWOWXIUYQVUDUNZTZUYTWXLVUAWXQUYQVVCUYSWXKF
      WXPWXIUYQVUDVVCWXPUWPWXIUDVUDVVCWXIVXHVUAUYJQZVXHVUAVUKQZVXHVUDRZVXHVVCRZ
      WXIWXRWXSWXIVWCVUAUNZVXHVWCUYJQZVXHVWCVUKQZWGZWGZPWHWXRWXSWGZWXIWYFPWXIWY
      BWYEWYBWXIWXAWYBXMZWYEWYBWXAUWQWYCVXHVWCWQZVYERZUEUYIWFZWXIWYHTZWYDWYCWYI
      UYJRWYKVXHVWCUYJWRUEWYIUYIWJWKWYLWYJWYDUEUYIVYHVYKWYLWYJWYDWGZVYMWYLVYJWY
      MUFWXIWYHVYJWYMWGZAVULVXAWYHWYNWGVUQVYJWYHVXAWYMAVULVYJWYHVXAWYMWGWGWVDWY
      HVXAWYMWYJVXHVWCVYEQZWVDWYHVXATZTZWYDVXHVWCVYEWRWYQWUBWYOWYDWGWUGWYQWUBTZ
      WYOWYOVXHVWCVYSQZTZWYDWYRWYOWYSWYRWYOVXHVYIRZWUMTWYSWYRWYOXUAWUMWYRWYOVXH
      VWCWUQQZXUAWYRVYEWUQVXHVWCWVDWUSWYPWUBWVMWTXCXUBXUAWUOVXHVWCVYIVYIXFXEUWR
      WYQWUMWUBWVDWYHVXAWUMWVDWXAVXAWUMWGZWYBWVDWXATZWUMVXAXUDVWCVUAVUSQZWUMWVD
      WXAXUEWVDVUKVUSVWCVUAAVULVUTVYJVVLYIXCYLXUEWUMVXAVWCVUAVUIVUIXFXEVRUWSWYB
      XUCWVDWYBWUMVXAPCOUWTUXAVPUXBYMWSUXCVXHVWCVYIVUIXFUXDUXEWYRWYDVXHVWCVYTQW
      YTWYRVUKVYTVXHVWCWYQVYRWUAWOXHVXHVWCVYEVYSUXJUXFUXGWYQWUGTZVYEVUKVXHVWCXU
      FVYEWUEVUKWYQWUCWUFWOWVRXLXCWVDWVSWYPWWAWSXNXQXRXOUXHYMYLVGVIXPVIZYNVFXSW
      YEWYGPCWYBWYCWXRWYDWXSVWCVUAVXHUYJYRVWCVUAVXHVUKYRUXIUXKVLWXIVUKUYJVXHVUA
      WXIVVJWXDVULVVJAVXAWXEYJWXFVRZXCYOWXTWXRXACUYJVUAVXHWLUDVAZYPYSWYAWXSXACV
      UKVUAVXHWLXUIYPZYSYQUXLUXMZWXQUYSUYJWXJULZWXKWXQUYRWXJUYJWXQUYQVVCXUKUXNU
      XOWXIXULWXKUNWXPWXIUDPXULWXKVVCVVCUYJYTVVCVVCVUKYTWXIWYAVWCVVCRZTZWYCTZXU
      NWYDTZWYIXULRZWYIWXKRZWXIXUNWYCWYDXUNWXIWXSWXATZWYCWYDXAXUNXUSXACVUAWLRWY
      AWXSXUMWXAXUJVUKVUAVWCWLPVAYPUXPYSWXIXUSTZWYCWYDWXIWXAWYEWXSWXAWXIWYHWYEW
      XAWYBUXQXUGYNUXRXUTVUKUYJVXHVWCWXIWXDXUSXUHWSXCYOUXTUXSXUQVXHVWCXULQXUOVX
      HVWCXULWRVVCVVCVXHVWCUYJXGUYAXURVXHVWCWXKQXUPVXHVWCWXKWRVVCVVCVXHVWCVUKXG
      UYAYQUYBWSUYCUYDUYEUYFXIXRVGVIXPVIUYGVTABCDEUYJFGHIJKLVBUYHIUYJHVVSVOVR
      $.

    $( Lemma for ~ fpwwe2 .  (Contributed by Mario Carneiro, 18-May-2015.)
       (Revised by AV, 20-Jul-2024.) $)
    fpwwe2lem12 $p |- ( ph -> ( X F ( W ` X ) ) e. X ) $=
      ( wcel wa wss wbr wceq c0 vz va vb vs cfv co wn csn cun ssun2 cdm cxp wwe
      cuni cv cin ccnv cima wsbc wral adantr w3a adantlr 3syl fpwwe2lem2 simpld
      wb mpbid simprd unssd ssun1 xpss12 mp2an a1i jca wfr w3o wrex wi ad2antrr
      wne ssbrd brxp simplbi syl6 mtod nsyl wo brun bitrdi ioran bitri sylanbrc
      notbid ralsn mpbird ex cvv vex syl uncom sseqtrdi sylib simpr idd simprbi
      adantl biimtrid ad3antrrr sylibr elun ssbri elsni cnvimass sylancr simplr
      mpd eliniseg elv sylan9eqr ineq2d indir incom sstrid disjsn eqtrid xpeq2d
      sqxpeqd xp0 eqtrdi un0 eqtrd oveq12d eqeq1d sbcied crn cres ax-mp uneq12d
      eqtri fpwwe2lem11 cpw wf wfun fpwwe2lem10 ffun funfvbrb fpwwe2lem4 syldan
      3jca snssd sstrdi wal cdif ssdif0 simpllr ovex breq2 rexsn bilani simplrr
      sssn neneqd orcnd raleqdv rexeqbidv biimtrrid difexg mp1i simplrl ssundif
      breq1 wefr fri syl22anc eldifn pm2.21d syl5 con3d ralimdv jctird sseqtrri
      jaod undif1 ralun ssralv eldifi jctild expimpd reximdv2 pm2.61dne alrimiv
      mpsyl df-fr anbi12i weso solin sylan 3orim123d ancomd 3mix3 bilanri 3mix1
      eqtr3 syl2an 3mix2d ccased ralrimivv dfwe2 fpwwe2cbv fpwwe2lem3 fvex snex
      wor xpexg sylancl unexg dmexd ssexg id nelne2 necon3ai biorf orcom bitr4i
      syl2anc bitr2di 3bitr4g eqrdv inxp dmss dmxpid ssneldd uneq2d eqcomd rnss
      eleq1d df-rn rnxpid 3sstr3g sseld sylbid ndmima sneqd imaeq2d df-ima ssid
      cnvxp reseq1i xpssres rneqi snnz rnxp cnvun imaeq1i imaundir eqtr3i dfss2
      3eqtr4g xpindi 3eqtr3g jaodan ralrimiva mpbir2and relopabiv releldmi snss
      sylan2b elssuni sseqtrrdi pm2.18da ) AIIHUEZFUFZIOZAVVNUGZPZVVMUHZIQVVNVV
      PVVQIVVQUIZIVVQIUJZVVPVVRHUKZUNZIVVPVVRVVLIVVQULZUIZHRZVVRVVTOVVRVWAQVVPV
      WDVVREQZVWCVVRVVRULZQZPZVVRVWCUMZDUOZVWCVWJVWJULZUPZFUFZCUOZSZDVWCUQZVWNU
      HZURZUSZCVVRUTZPZVVPVWEVWGVVPIVVQEVVPIEQZVVLIIULZQZVVPVXBVXDPZIVVLUMZVWJV
      VLVWKUPFUFVWNSDVVLUQZVWQURZUSCIUTZPZVVPIVVLHRZVXEVXJPVVPIVVTOZVXKVVPBCDEF
      GHIJKAEGOVVOLVAZABUOZEQZJUOZVXNVXNULQZVXNVXPUMZVBVXNVXPFUFEOVVOMVCZNUUAZV
      VPVVTVXCUUBZHUUCHUUDVXLVXKVGVVPBCDEFGHIJKVXMVXSNUUEVVTVYAHUUFIHUUGVDVHZVV
      PBCDEVVLFGHIJKVXMVEVHZVFZVFZVVPVVMEAVVOVXBVXDVXFVBVVMEOVVPVXBVXDVXFVYEVVP
      VXBVXDVYDVIZVVPVXFVXIVVPVXEVXJVYCVIVFZUUJABCDEVVLFGHIJKLMUUHUUIUUKVJVVPVV
      LVWBVWFVVPVVLVXCVWFVYFIVVRQZVYHVXCVWFQIVVQVKZVYIIVVRIVVRVLVMUULVWBVWFQZVV
      PVYHVVQVVRQVYJVYIVVSIVVRVVQVVRVLVMVNVJVOVVPVWIVWTVVPVVRVWCVPZVXNVWNVWCRZV
      XNVWNSZVWNVXNVWCRZVQZCVVRUTBVVRUTVWIVVPVXNVVRQZVXNTWAZPZUAUOZVWNVWCRZUGZU
      AVXNUTZCVXNVRZVSZBUUMVYKVVPWUDBVVPVYRWUCVVPVYRPZWUCVXNVVQUUNZTWUFTSVXNVVQ
      QZWUEWUCVXNVVQUUOWUEWUGWUCWUEWUGPZWUCVVMVWNVWCRZUGZCVVQVRZWUHVVMVVMVVLRZU
      GZVVMVVMVWBRZUGZWUKWUHWULVVNAVVOVYRWUGUUPZWUHWULVVMVVMVXCRZVVNWUHVVLVXCVV
      MVVMVVPVXDVYRWUGVYFVTWBWUQVVNVVNVVMVVMIIWCWDWEWFWUHVVNWUNWUPWUNVVNVVMVVQO
      VVMVVMIVVQWCWDWGWUKWULWUNWHZUGZWUMWUOPWUJWUSCVVMIVVLFUUQZVWNVVMSZWUIWURWV
      AWUIVVMVVMVWCRWURVWNVVMVVMVWCUURVVMVVMVVLVWBWIWJWNUUSWULWUNWKWLWMWUHWUBWU
      JCVXNVVQWUHVXNTSZVXNVVQSZWUGWVBWVCWHWUEVXNVVMUVBUUTWUHVXNTVVPVYPVYQWUGUVA
      UVCUVDZWUHWUBWUAUAVVQUTZWUJWUHWUAUAVXNVVQWVDUVEWUAWUJUAVVMWUTVYSVVMSZVYTW
      UIVYSVVMVWNVWCUVLZWNWOWJUVFWPWQUVGWUEWUFTWAZWUCWUEWVHPZVYSVWNVVLRZUGZUAWU
      FUTZCWUFVRZWUCWVIWUFWROZIVVLVPZWUFIQZWVHWVMVXNWROWVNWVIBWSVXNVVQWRUVHUVIV
      VPWVOVYRWVHVVPVXFWVOVYGIVVLUVMWTVTWVIVXNVVQIUIZQWVPWVIVXNVVRWVQVVPVYPVYQW
      VHUVJIVVQXAXBVXNVVQIUVKXCWUEWVHXDCUAIWUFWRVVLUVNUVOWVIWVLWUBCWUFVXNWVIVWN
      WUFOZWVLVWNVXNOZWUBPWVIWVRPZWVLWUBWVSWVTWVLWUAUAWUFUTZWVEPZWUBWVTWVLWWAWV
      EWVTWVKWUAUAWUFWVTVYTWVJVYTWVJVYSVWNVWBRZWHZWVTWVJVYSVWNVVLVWBWIZWVTWVJWV
      JWWCWVTWVJXEWWCVWNVVQOZWVTWVJWWCVYSIOWWFVYSVWNIVVQWCXFZWVTWWFWVJWVRWWFUGW
      VIVWNVXNVVQUVPXGZUVQUVRUWCXHUVSUVTWVTVVMVWNVVLRZUGZVVMVWNVWBRZUGZWVEWVTWW
      IVVNVVPVVOVYRWVHWVRAVVOXDXIWVTWWIVVMVWNVXCRZVVNWVTVVLVXCVVMVWNVVPVXDVYRWV
      HWVRVYFXIWBWWMVVNVWNIOZVVMVWNIIWCWDWEWFWVTWWFWWKWWHWWKVVNWWFVVMVWNIVVQWCX
      FWGWVEWWIWWKWHZUGZWWJWWLPWUAWWPUAVVMWUTWVFVYTWWOWVFVYTWUIWWOWVGVVMVWNVVLV
      WBWIWJWNWOWWIWWKWKWLWMUWAVXNWUFVVQUIZQWWBWUAUAWWQUTWUBVXNVXNVVQUIWWQVXNVV
      QVKVXNVVQUWDUWBWUAUAWUFVVQUWEWUAUAVXNWWQUWFUWMWEWVRWVSWVIVWNVXNVVQUWGXGUW
      HUWIUWJXQWQUWKWQUWLBCUAVVRVWCUWNXJVVPVYOBCVVRVVRVXNVVROZVWNVVROZPVXNIOZVX
      NVVQOZWHZWWNWWFWHZPVVPVYOWWRWXBWWSWXCVXNIVVQXKVWNIVVQXKZUWOVVPWWTWWNWXAWW
      FVYOVVPWWTWWNPZVYOVVPWXEPZVXNVWNVVLRZVYMVWNVXNVVLRZVQZVYOVVPIVVLUXNZWXEWX
      IVVPVXFWXJVYGIVVLUWPWTIVXNVWNVVLUWQUWRWXFWXGVYLVYMVYMWXHVYNWXFVVLVWCVXNVW
      NVVLVWCQWXFVVLVWBVKVNZWBWXFVYMXEWXFVVLVWCVWNVXNWXKWBUWSXQWQVVPWXAWWNPZVYO
      VVPWXLPZVWNVXNVWBRZVYNVYOWXMWWNWXAPWXNWXMWXAWWNVVPWXLXDUWTVWNVXNIVVQWCXJV
      WBVWCVWNVXNVWBVVLUJZXLVYNVYLVYMUXAVDWQVVPWWTWWFPZVYOVVPWXPPVXNVWNVWBRZVYL
      VYOWXQWXPVVPVXNVWNIVVQWCUXBVWBVWCVXNVWNWXOXLVYLVYMVYNUXCVDWQWXAWWFPZVYOVS
      VVPWXRVYMVYLVYNWXAVXNVVMSWVAVYMWWFVXNVVMXMVWNVVMXMZVXNVWNVVMUXDUXEUXFVNUX
      GXHUXHBCVVRVWCUXIWMVVPVWSCVVRWWSVVPWXCVWSWXDVVPWWNVWSWWFVVPWWNPZVWSVXHVVL
      VXHVXHULZUPZFUFZVWNSZVVPUBUAUCEVWNVVLFGHIUDBCUAUCDEFHUDJUBKUXJVXMVYBUXKWX
      TVWOWYDDVWRWRVVPVWRWROZWWNVVPVWRVWCUKZQWYFWROWYEVWCVWQXNVVPVWCWRVVPVVLWRO
      VWBWROZVWCWROIHUXLVVPVXLVVQWROWYGVXTVVMUXMIVVQVVTWRUXOUXPVVLVWBWRWRUXQXOU
      XRVWRWYFWRUXSXOZVAWXTVWJVWRSZPZVWMWYCVWNWYJVWJVXHVWLWYBFWYIWXTVWJVWRVXHWY
      IUXTZWXTUAVWRVXHWXTVYTWVJVYSVWROZVYSVXHOZWXTWVJWWCWVJWHZVYTWXTVWNVVMWAZWW
      CUGWVJWYNVGWXTWWNVVOWYOVVPWWNXDAVVOWWNXPZVWNVVMIUYAUYFWWCVWNVVMWWCWWFWVAW
      WGWXSWTUYBWWCWVJUYCVDWYNWWDVYTWWCWVJUYDWWEUYEUYGWYLVYTVGCVWCVWNVYSWRUAWSZ
      XRXSWYMWVJVGCVVLVWNVYSWRWYQXRXSUYHUYIXTZWYJVWLVWCWYAUPZWYBWYJVWKWYAVWCWYJ
      VWJVXHWYRYHYAWXTWYSWYBSWYIWXTWYSWYBTUIZWYBWXTWYSWYBVWBWYAUPZUIWYTVVLVWBWY
      AYBWXTXUATWYBWXTXUAIVXHUPZVVQVXHUPZULZTIVVQVXHVXHUYJWXTXUDXUBTULTWXTXUCTX
      UBWXTXUCVXHVVQUPZTVVQVXHYCWXTVVMVXHOUGXUETSWXTVXHIVVMWXTVXHVVLUKZIVVLVWQX
      NWXTXUFVXCUKZIWXTVXDXUFXUGQVVPVXDWWNVYFVAVVLVXCUYKWTIUYLXBYDWYPUYMVXHVVMY
      EXJYFYGXUBYIYJYFUYNYFWYBYKYJVAYLYMYNYOWPVVPWWFPZVWSVVMVWNSZXUHVWNVVMWWFWV
      AVVPWXSXGZUYOXUHVWOXUIDVWRWRVVPWYEWWFWYHVAXUHWYIPZVWMVVMVWNXUKVWJIVWLVVLF
      WYIXUHVWJVWRIWYKXUHVXHVWBUQZVWQURZUIZTIUIZVWRIXUHVXHTXUMIXUHVWNVXGUKZOZUG
      VXHTSXUHXUQVVNAVVOWWFXPZXUHXUQVVMXUPOVVNXUHVWNVVMXUPXUJUYQXUHXUPIVVMXUHVV
      LYPZVXCYPZXUPIXUHVXDXUSXUTQVVPVXDWWFVYFVAZVVLVXCUYPWTVVLUYRIUYSUYTVUAVUBW
      FVWNVXGVUCWTXUHXUMXULVVQURZIXUHVWQVVQXULXUHVWNVVMXUJVUDVUEXVBXULVVQYQZYPZ
      IXULVVQVUFXVDVVQIULZYPZIXVCXVEXVCXVEVVQYQZXVEXULXVEVVQIVVQVUHVUIVVQVVQQXV
      GXVESVVQVUGVVQIVVQVUJYRYTVUKVVQTWAXVFISVVMWUTVULVVQIVUMYRYTYTYJYSVWRVXGXU
      LUIZVWQURXUNVWPXVHVWQVVLVWBVUNVUOVXGXULVWQVUPYTITUIIXUOIYKITXAVUQVUSXTZXU
      KVWLVWCVXCUPZVVLXUKVWKVXCVWCXUKVWJIXVIYHYAXUHXVJVVLSWYIXUHXVJVVLTUIZVVLXU
      HXVJVVLVXCUPZVWBVXCUPZUIXVKVVLVWBVXCYBXUHXVLVVLXVMTXUHVXDXVLVVLSXVAVVLVXC
      VURXCXUHIVVQIUPZULITULXVMTXUHXVNTIXUHXVNIVVQUPZTVVQIYCXUHVVOXVOTSXURIVVMY
      EXJYFYGIVVQIVUTIYIVVAYSYFVVLYKYJVAYLYMYNYOWPVVBVVHVVCVOAVWDVWHVXAPVGVVOAB
      CDEVWCFGHVVRJKLVEVAVVDVVRVWCHVXOVXQPVXRVWJVXPVWKUPFUFVWNSDVXPUQVWQURUSCVX
      NUTPPBJHKVVEVVFVVRVVTVVIVDNVVJYDVVMIWUTVVGXJVVK $.

    $( Given any function ` F ` from well-orderings of subsets of ` A ` to
       ` A ` , there is a unique well-ordered subset ` <. X , ( W `` X ) >. `
       which "agrees" with ` F ` in the sense that each initial segment maps to
       its upper bound, and such that the entire set maps to an element of the
       set (so that it cannot be extended without losing the well-ordering).
       This theorem can be used to prove ~ dfac8a .  Theorem 1.1 of
       [KanamoriPincus] p. 415.  (Contributed by Mario Carneiro, 18-May-2015.)
       (Revised by AV, 20-Jul-2024.) $)
    fpwwe2 $p |- ( ph ->
      ( ( Y W R /\ ( Y F R ) e. Y ) <-> ( Y = X /\ R = ( W ` X ) ) ) ) $=
      ( wcel wa wceq wss vw vz wbr co cfv cdm wfun wb cxp cpw fpwwe2lem10 ffund
      funbrfv2b syl simprbda adantrr cuni elssuni sseqtrrdi cin wi simpl a1i c0
      cdif simplrr wne cv wn wral wrex cvv wfr adantr wwe ccnv cima fpwwe2lem11
      wsbc funfvbrb mpbid fpwwe2lem2 ad2antrr simpld ssexd difexd simprd difssd
      csn wefr fri syl21anc ssdif0 indif1 eqeq1i vex eliniseg elv notbii ralbii
      expr disj bitri 3bitr2i cnvimass dmss dmxpid sseqtrdi sstrid sylib sseq1d
      sseqin2 bitr3id eldifn ad2antrl eleq1w notbid syl5ibrcom con2d imp simprr
      rexbidv breqd eldifi simpr brxp sylanbrc brin rbaib bitrd ad3antrrr ssbrd
      biimpa simplbi sylibr ex eqssd dfss2 eqtrd jca syl6 sylbird mtod wor weso
      sselda wo sotric ioran bitrdi syl12anc mpbir2and ssrdv in32 ineq1d eqtr3d
      inss2 xpss1 3eqtr3a sqxpeqd ineq2d oveq12d fpwwe2lem3 eqneltrd rexlimdvaa
      mpdan sylbid syld necon4ad mpd adantlr simprl fpwwe2lem9 eqbrtrrd funbrfv
      w3a mpjaod sylc eqcomd fpwwe2lem12 breq12 oveq12 eleq12d anbi12d impbid )
      AKFIUCZKFGUDZKQZRZKJSZFJIUEZSZRZAUWIUWMAUWIRZUWJUWLUWNKJUWNKIUFZQZKJTZAUW
      FUWPUWHAUWFUWPKIUEFSZAIUGZUWFUWPUWRRUHAUWOJJUIZUJIABCDEGHIJLMNOPUKULZKFIU
      MUNUOUPUWPKUWOUQJKUWOURPUSUNZUWNJKTZUWKFKJUIUTSZRZUXCUWQFUWKJKUIZUTZSZRZU
      XEUXCVAUWNUXCUXDVBVCUWNUXIUXCUWNUXIRZJKVEZVDSZUXCUXJUWHUXLAUWFUWHUXIVFUXJ
      UWHUXKVDUXJUXKVDVGZUAVHZUBVHZUWKUCZVIZUAUXKVJZUBUXKVKZUWHVIZUXJUXKVLQZJUW
      KVMZUXKJTZUXMUXSVAUXJJKVLUXJJEHUWNEHQZUXIAUYDUWINVNZVNZUXJJETZUWKUWTTZUXJ
      UYGUYHRZJUWKVOZDVHZUWKUYKUYKUIZUTGUDCVHZSDUWKVPZUYMWIZVQVSCJVJZRZAUYIUYQR
      ZUWIUXIAJUWKIUCZUYRAJUWOQZUYSABCDEGHIJLMNOPVRAUWSUYTUYSUHUXAJIVTUNWAZABCD
      EUWKGHIJLMNWBWAWCZWDZWDWEWFUXJUYJUYBUXJUYJUYPUXJUYIUYQVUBWGWDZJUWKWJUNUXJ
      JKWHUYAUYBRUYCUXMUXSUBUAJUXKVLUWKWKXAWLUXJUXSUYNUXOWIZVQZKTZUBUXKVKUXTUXJ
      UXRVUGUBUXKUXRJVUFUTZKTZUXJVUGVUIVUHKVEZVDSUXKVUFUTZVDSZUXRVUHKWMVUKVUJVD
      JVUFKWNWOVULUXNVUFQZVIZUAUXKVJUXRUAUXKVUFXBVUNUXQUAUXKVUMUXPVUMUXPUHUBUWK
      UXOUXNVLUAWPWQWRZWSWTXCXDUXJVUHVUFKUXJVUFJTVUHVUFSUXJVUFUWKUFZJUWKVUEXEUX
      JVUPUWTUFZJUXJUYHVUPVUQTUXJUYGUYHVUCWGUWKUWTXFUNJXGXHXIVUFJXLXJXKXMYBUXJV
      UGUXTUBUXKUXJUXOUXKQZVUGRZRZUWGUXOKVUTUWGVUFUWKVUFVUFUIZUTZGUDZUXOVUTKVUF
      FVVBGVUTKVUFVUTUAKVUFVUTUXNKQZVUMVUTVVDRZUXPVUMVVEUXPUXNUXOSZVIZUXOUXNUWK
      UCZVIZVUTVVDVVGVUTVVFVVDVUTVVDVIVVFUXOKQZVIZVURVVKUXJVUGUXOJKXNXOZVVFVVDV
      VJUAUBKXPXQXRXSXTVVEVVHVVJVUTVVKVVDVVLVNVVEVVHUXOUXNFUCZVVJVVEVVMUXOUXNUX
      GUCZVVHVVEFUXGUXOUXNUXJUXHVUSVVDUWNUWQUXHYAWCYCVVEUXOUXNUXFUCZVVNVVHUHVVE
      UXOJQZVVDVVOVUTVVPVVDVURVVPUXJVUGUXOJKYDXOZVNZVUTVVDYEUXOUXNJKYFYGVVNVVHV
      VOUXOUXNUWKUXFYHYIUNYJVVEVVMUXOUXNKKUIZUCZVVJVVEFVVSUXOUXNUWNFVVSTZUXIVUS
      VVDUWNKETZVWAUWNVWBVWARZKFVOUYKFUYLUTGUDUYMSDFVPUYOVQVSCKVJRZAUWFVWCVWDRZ
      UWHAUWFVWEABCDEFGHIKLMNWBYMUPWDWGZYKYLVVTVVJVVDUXOUXNKKYFYNUUAUUBUUCVVEJU
      WKUUDZUXNJQZVVPUXPVVGVVIRZUHVVEUYJVWGUXJUYJVUSVVDVUDWCJUWKUUEUNVUTKJUXNUW
      NUWQUXIVUSUXBWCZUUFVVRVWGVWHVVPRRUXPVVFVVHUUGVIVWIJUXNUXOUWKUUHVVFVVHUUIU
      UJUUKUULVUOYOYPUUMUXJVURVUGYAYQZVUTFUWKVVSUTZVVBVUTUXGVVSUTZVWLUXFUTZFVWL
      UWKUXFVVSUUNVUTFVVSUTZVWMFVUTFUXGVVSUWNUWQUXHVUSVFUUOVUTVWAVWOFSUWNVWAUXI
      VUSVWFWCFVVSYRXJUUPVUTVWLUXFTVWNVWLSVUTVWLVVSUXFUWKVVSUUQVUTUWQVVSUXFTVWJ
      KJKUURUNXIVWLUXFYRXJUUSVUTVVSVVAUWKVUTKVUFVWKUUTUVAYSUVBVUTVVPVVCUXOSVVQV
      UTBCDEUXOUWKGHIJLMUXJUYDVUSUYFVNUWNUYSUXIVUSAUYSUWIVUAVNZWCUVCUVFYSVVLUVD
      UVEUVGUVHUVIUVJJKWMYOYPUWNBCDEUWKFGHIJKLMUYEABVHZETLVHZVWQVWQUITVWQVWRVOU
      VPVWQVWRGUDEQUWIOUVKVWPAUWFUWHUVLZUVMUVQYQZUWNUWKFUWNUWSJFIUCUWKFSAUWSUWI
      UXAVNUWNKJFIVWTVWSUVNJFIUVOUVRUVSYTYPAUWIUWMUYSJUWKGUDZJQZRAUYSVXBVUAABCD
      EGHIJLMNOPUVTYTUWMUWFUYSUWHVXBKJFUWKIUWAUWMUWGVXAKJKJFUWKGUWBUWJUWLVBUWCU
      WDXRUWE $.
  $}

  ${
    $d a r s x A $.  $d a r s u x y z F $.  $d r u x y ph $.  $d r u x y R $.
    $d r u x y X $.  $d r u x y Y $.
    fpwwe.1 $e |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\
      ( r We x /\ A. y e. x ( F ` ( `' r " { y } ) ) = y ) ) } $.
    $( Lemma for ~ fpwwe .  (Contributed by Mario Carneiro, 15-May-2015.) $)
    fpwwecbv $p |- W = { <. a , s >. | ( ( a C_ A /\ s C_ ( a X. a ) ) /\
      ( s We a /\ A. z e. a ( F ` ( `' s " { z } ) ) = z ) ) } $=
      ( cv wss cxp wa cima cfv wceq wral weq anbi12d wwe csn copab simpl sseq1d
      ccnv simpr sqxpeqd sseq12d weeq12d sneq imaeq2d fveq2d id cbvralvw cnveqd
      eqeq12d imaeq1d fveqeq2d raleqbidv bitrid cbvopabv eqtri ) FAKZDLZHKZVDVD
      MZLZNZVDVFUAZVFUFZBKZUBZOZEPZVLQZBVDRZNZNZAHUCIKZDLZGKZVTVTMZLZNZVTWBUAZW
      BUFZCKZUBZOZEPWHQZCVTRZNZNZIGUCJVSWNAHIGAISZHGSZNZVIWEVRWMWQVEWAVHWDWQVDV
      TDWOWPUDZUEWQVFWBVGWCWOWPUGZWQVDVTWRUHUITWQVJWFVQWLWQVDVTVFWBWSWRUJVQVKWI
      OZEPZWHQZCVDRWQWLVPXBBCVDBCSZVOXAVLWHXCVNWTEXCVMWIVKVLWHUKULUMXCUNUQUOWQX
      BWKCVDVTWRWQWTWJWHEWQVKWGWIWQVFWBWSUPURUSUTVATTVBVC $.

    $d r u x y W $.
    fpwwe.2 $e |- ( ph -> A e. V ) $.
    $( Lemma for ~ fpwwe .  (Contributed by Mario Carneiro, 15-May-2015.)
       (Revised by AV, 20-Jul-2024.) $)
    fpwwelem $p |- ( ph -> ( X W R <-> ( ( X C_ A /\ R C_ ( X X. X ) ) /\
      ( R We X /\ A. y e. X ( F ` ( `' R " { y } ) ) = y ) ) ) ) $=
      ( wss cxp wa cv wceq cvv wcel anbi12d wbr wwe ccnv csn cima cfv wral wrel
      relopabiv brrelex12 sylan adantr simprll ssexd xpexd simprlr simpl sseq1d
      a1i jca simpr sqxpeqd sseq12d weeq12d imaeq1d fveqeq2d raleqbidv pm5.21nd
      cnveqd brabga ) AIEHUAZIDMZEIINZMZOZIEUBZEUCZCPZUDZUEZFUFVRQZCIUGZOZOZIRS
      ZERSZOZAHUHZVKWGWHABPZDMZJPZWIWINZMZOZWIWKUBZWKUCZVSUEZFUFVRQZCWIUGZOZOZB
      JHKUIUSIEHUJUKAWDOZWEWFXBIDGADGSWDLULAVLVNWCUMUNZXBEVMRXBIIRRXCXCUOAVLVNW
      CUPUNUTXAWDBJIEHRRWIIQZWKEQZOZWNVOWTWCXFWJVLWMVNXFWIIDXDXEUQZURXFWKEWLVMX
      DXEVAZXFWIIXGVBVCTXFWOVPWSWBXFWIIWKEXHXGVDXFWRWACWIIXGXFWQVTVRFXFWPVQVSXF
      WKEXHVIVEVFVGTTKVJVH $.

    fpwwe.3 $e |- ( ( ph /\ x e. ( ~P A i^i dom card ) ) -> ( F ` x ) e. A ) $.
    fpwwe.4 $e |- X = U. dom W $.
    $( Given any function ` F ` from the powerset of ` A ` to ` A ` , ~ canth2
       gives that the function is not injective, but we can say rather more
       than that.  There is a unique well-ordered subset
       ` <. X , ( W `` X ) >. ` which "agrees" with ` F ` in the sense that
       each initial segment maps to its upper bound, and such that the entire
       set maps to an element of the set (so that it cannot be extended without
       losing the well-ordering).  This theorem can be used to prove ~ dfac8a .
       Theorem 1.1 of [KanamoriPincus] p. 415.  (Contributed by Mario Carneiro,
       18-May-2015.)  (Revised by AV, 20-Jul-2024.) $)
    fpwwe $p |- ( ph ->
      ( ( Y W R /\ ( F ` Y ) e. Y ) <-> ( Y = X /\ R = ( W ` X ) ) ) ) $=
      ( cfv wcel wa wceq cvv vu wbr c1st ccom co cop df-ov wfn fo1st fofn ax-mp
      wfo opex fvco2 mp2an eqtri cv wss cxp wwe ccnv cima wral bropaex12 op1stg
      csn syl fveq2d eqtrid eleq1d pm5.32i copab cin wsbc vex cnvex imaex inex1
      opco1i fveq2 eqeq1d sbcie ralbii anbi2i opabbii eqtr4i w3a cpw ccrd simp1
      cdm velpw sylibr 19.8a 3ad2ant3 ween elind sylan2 eqeltrid fpwwe2 bitr3id
      wex ) JEHUBZJFPZJQZRXCJEFUCUDZUEZJQZRAJISEIHPSRXCXHXEXCXGXDJXCXGJEUFZUCPZ
      FPZXDXGXIXFPZXKJEXFUGUCTUHZXITQXLXKSTTUCULXMUITTUCUJUKJEUMTFUCXIUNUOUPXCX
      JJFXCJTQETQRXJJSBUQZDURZKUQZXNXNUSURZRZXNXPUTZXPVAZCUQZVFZVBZFPZYASZCXNVC
      ZRZRZBKJEHLVDJETTVEVGVHVIVJVKABCUADEXFGHIJKHYHBKVLXRXSUAUQZXPYIYIUSZVMZXF
      UEZYASZUAYCVNZCXNVCZRZRZBKVLLYQYHBKYPYGXRYOYFXSYNYECXNYMYEUAYCXTYBXPKVOZV
      PVQYIYCSZYLYDYAYSYLYIFPYDYIYKFUAVOXPYJYRVRVSYIYCFVTVIWAWBWCWDWDWEWFMAXOXQ
      XSWGZRXNXPXFUEXNFPZDXNXPFBVOYRVSYTAXNDWHZWIWKZVMQUUADQYTUUBUUCXNYTXOXNUUB
      QXOXQXSWJBDWLWMYTXSKXBZXNUUCQXSXOUUDXQXSKWNWOXNKWPWMWQNWRWSOWTXA $.
  $}

  ${
    $d r x y A $.  $d r x y B $.  $d r x y D $.  $d r x y F $.  $d r x y V $.
    $d y C $.  $d r x y W $.
    canth4.1 $e |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\
      ( r We x /\ A. y e. x ( F ` ( `' r " { y } ) ) = y ) ) } $.
    canth4.2 $e |- B = U. dom W $.
    canth4.3 $e |- C = ( `' ( W ` B ) " { ( F ` B ) } ) $.
    $( An "effective" form of Cantor's theorem ~ canth .  For any function
       ` F ` from the powerset of ` A ` to ` A ` , there are two definable sets
       ` B ` and ` C ` which witness non-injectivity of ` F ` .  Corollary 1.3
       of [KanamoriPincus] p. 416.  (Contributed by Mario Carneiro,
       18-May-2015.) $)
    canth4 $p |- ( ( A e. V /\ F : D --> A /\ ( ~P A i^i dom card ) C_ D ) ->
      ( B C_ A /\ C C. B /\ ( F ` B ) = ( F ` C ) ) ) $=
      ( wcel wss cfv wceq wa simpld simprd wf cpw ccrd cdm cin w3a wpss cxp wwe
      ccnv cv csn cima wral wbr eqid pm3.2i simp1 simpl2 simp3 sselda ffvelcdmd
      fpwwe mpbiri fpwwelem mpbid cnvimass eqsstri dmss syl dmxpid sseqtrdi wor
      sstrid wn weso sonr syl2anc eleq2i wb fvex eliniseg ax-mp bitri ssnelpssd
      cvv sylnibr sneq imaeq2d eqtr4di fveq2d id eqeq12d rspcdva eqcomd 3jca )
      CHNZFCGUAZCUBUCUDUEZFOZUFZDCOZEDUGDGPZEGPZQXAXBDIPZDDUHZOZXAXBXGRZDXEUIZX
      EUJZBUKZULZUMZGPZXKQZBDUNZRZXADXEIUOZXHXQRXAXRXCDNZXAXRXSRDDQZXEXEQZRXTYA
      DUPXEUPUQXAABCXEGHIDDJKWQWRWTURZXAAUKZWSNZRFCYCGWQWRWTYDUSXAWSFYCWQWRWTUT
      VAVBLVCVDZSXAABCXEGHIDJKYBVEVFZSZSXAEDXCXAEXEUDZDEXJXCULZUMZYHMXEYIVGVHXA
      YHXFUDZDXAXGYHYKOXAXBXGYGTXEXFVIVJDVKVLVNXAXRXSYETZXAXCXCXEUOZXCENZXADXEV
      MZXSYMVOXAXIYOXAXIXPXAXHXQYFTZSDXEVPVJYLDXCXEVQVRYNXCYJNZYMEYJXCMVSXCWFNY
      QYMVTDGWAZXEXCXCWFYRWBWCWDWGWEXAXDXCXAXOXDXCQBDXCXKXCQZXNXDXKXCYSXMEGYSXM
      YJEYSXLYIXJXKXCWHWIMWJWKYSWLWMXAXIXPYPTYLWNWOWP $.

    $( Lemma for ~ canthnum .  (Contributed by Mario Carneiro, 19-May-2015.) $)
    canthnumlem $p |- ( A e. V -> -. F : ( ~P A i^i dom card ) -1-1-> A ) $=
      ( wcel wceq wa cfv wss wb elpw2g cv cpw ccrd cdm cin wf1 wpss wf w3a ssid
      f1f canth4 mp3an3 sylan2 simp3d simp1d adantr mpbird wwe wex cxp ccnv csn
      simpr cima wral eqid pm3.2i simpl ffvelcdmda fpwwe mpbiri simpld fpwwelem
      wbr mpbid simprld fvex weeq1 spcev sylibr elind simp2d pssssd sstrd ssnum
      syl ween syl2anc f1fveq syl12anc pssned necomd neneqd pm2.65da ) CGMZCUAZ
      UBUCZUDZCFUEZDENZWOWSOZDFPZEFPNZWTXADCQZEDUFZXCWSWOWRCFUGZXDXEXCUHZWRCFUJ
      ZWOXFWRWRQXGWRUIABCDEWRFGHIJKLUKULUMZUNXAWSDWRMEWRMXCWTRWOWSVCZXAWPWQDXAD
      WPMZXDXAXDXEXCXIUOZWOXKXDRWSDCGSUPUQXADITZURZIUSZDWQMZXADDHPZURZXOXAXDXQD
      DUTQOZXRXQVABTZVBVDFPXTNBDVEZXADXQHVNZXSXRYAOOXAYBXBDMZXAYBYCODDNZXQXQNZO
      YDYEDVFXQVFVGXAABCXQFGHDDIJWOWSVHZXAWRCATFXAWSXFXJXHWFVIKVJVKVLXAABCXQFGH
      DIJYFVMVOVPXNXRIXQDHVQDXMXQVRVSWFDIWGVTZWAXAWPWQEXAEWPMZECQZXAEDCXAEDXAXD
      XEXCXIWBZWCZXLWDWOYHYIRWSECGSUPUQXAXPEDQEWQMYGYKDEWEWHWAWRCDEFWIWJVOXADEX
      AEDXAEDYJWKWLWMWN $.
  $}

  ${
    $d a f r s x y z $.  $d a f r s x z A $.  $d a f s z V $.
    $( The set of well-orderable subsets of a set ` A ` strictly dominates
       ` A ` .  A stronger form of ~ canth2 .  Corollary 1.4(a) of
       [KanamoriPincus] p. 417.  (Contributed by Mario Carneiro,
       19-May-2015.) $)
    canthnum $p |- ( A e. V -> A ~< ( ~P A i^i dom card ) ) $=
      ( vx vf va vz vr vy vs wcel cdm cdom wbr cfn cvv wss cv wa cfv eqid pwexg
      cpw ccrd cin cen csdm inex1g infpwfidom 3syl syl finnum ssriv sslin ax-mp
      ssdomg mpisyl domtr syl2anc wf1o wex wf1 cxp wwe ccnv csn cima wceq copab
      wral cuni fpwwecbv canthnumlem f1of1 nsyl nexdv ensym bren sylib sylanbrc
      wn brsdom ) ABJZAAUBZUCKZUDZLMZAWEUEMZVTAWEUFMWBAWCNUDZLMZWHWELMZWFWBWCOJ
      ZWHOJWIABUAZWCNOUGAUHUIWBWEOJZWHWEPZWJWBWKWMWLWCWDOUGUJNWDPWNCNWDCQZUKULN
      WDWCUMUNWHWEOUOUPAWHWEUQURWBWEADQZUSZDUTZWGWBWQDWBWEAWPVAWQEFAWOAPGQZWOWO
      VBPRWOWSVCWSVDHQZVEVFWPSWTVGHWOVIRRCGVHZKVJZXBXASVDXBWPSVEVFZWPBXAICHFAWP
      XAIGEXATVKXBTXCTVLWEAWPVMVNVOWGWEAUEMWRAWEVPWEADVQVRVNAWEWAVS $.
  $}

  ${
    $d r u x y B $.  $d r x C $.  $d f r u v w x y O $.  $d f r u v w x y V $.
    $d a f r s v w x y z $.  $d a f r s u v w x y A $.  $d r u x y F $.
    $d r u x y W $.
    canthwe.1 $e |- O = { <. x , r >. |
      ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) } $.
    ${
      canthwe.2 $e |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\
      ( r We x /\ A. y e. x [. ( `' r " { y } ) / u ].
        ( u F ( r i^i ( u X. u ) ) ) = y ) ) } $.
      canthwe.3 $e |- B = U. dom W $.
      canthwe.4 $e |- C = ( `' ( W ` B ) " { ( B F ( W ` B ) ) } ) $.
      $( Lemma for ~ canthwe .  (Contributed by Mario Carneiro,
         31-May-2015.) $)
      canthwelem $p |- ( A e. V -> -. F : O -1-1-> A ) $=
        ( wcel co wa wceq wss wf1 cfv wbr ccnv csn cima pm3.2i simpl cv cxp wwe
        w3a cop df-ov wf f1f ad2antlr copab opabidw bilanri eleqtrrdi ffvelcdmd
        eqid eqeltrid fpwwe2 mpbiri simprd cin xpeq12i ineq2i simpld fpwwe2lem3
        oveq12i mpdan eqtrid 3eqtr3g wb simpr cdm cnvimass wsbc wral fpwwe2lem2
        mpbid dmss syl dmxpss sstrdi sstrid eqsstrid sstrd a1i wess sylc weinxp
        inss2 sylib cvv fvex cnvex imaex eqeltri sseq1d sqxpeqd sseq12d weeq12d
        inex1 3anbi123d opelopaba syl3anbrc opelopabga syl2anc mpbir3and f1fveq
        ssexd syl12anc opth1 eleqtrrd eleqtrdi ovex eliniseg weso sonr pm2.65da
        wor wn ) DIPZHDGUAZEEJUBZGQZYJYIUCZYGYHRZYJYIUDZYJUEZUFZPZYKYLYJFYOYLYJ
        EFYLEYIJUCZYJEPZYLYQYRREESZYIYISZRYSYTEVCYIVCUGYLABCDYIGIJEEKMYGYHUHZYL
        AUIZDTZKUIZUUBUUBUJZTZUUBUUDUKZULZRZUUBUUDGQUUBUUDUMZGUBDUUBUUDGUNUUIHD
        UUJGYHHDGUOYGUUHHDGUPUQUUIUUJUUHAKURZHUUJUUKPUUHYLUUHAKUSUTLVAVBVDNVEVF
        ZVGZYLFYIFFUJZVHZUMZEYIUMZSZFESYLUUPGUBZUUQGUBZSZUURYLFUUOGQZYJUUSUUTYL
        UVBYOYIYOYOUJZVHZGQZYJFYOUUOUVDGOUUNUVCYIFYOFYOOOVIVJVMYLYRUVEYJSUUMYLA
        BCDYJYIGIJEKMUUAYLYQYRUULVKZVLVNVOFUUOGUNEYIGUNVPYLYHUUPHPUUQHPUVAUURVQ
        YGYHVRYLUUPUUKHYLFDTZUUOUUNTZFUUOUKZUUPUUKPYLFEDYLFYOEOYLYOYIVSZEYIYNVT
        YLUVJEEUJZVSZEYLYIUVKTZUVJUVLTYLEDTZUVMYLUVNUVMRZEYIUKZCUIZYIUVQUVQUJVH
        GQBUIZSCYMUVRUEUFWABEWBZRZYLYQUVOUVTRUVFYLABCDYIGIJEKMUUAWCWDZVKZVGZYIU
        VKWEWFEEWGWHWIWJZYLUVNUVMUWBVKZWKUVHYLYIUUNWPWLYLFYIUKZUVIYLFETUVPUWFUW
        DYLUVPUVSYLUVOUVTUWAVGVKZFEYIWMWNFYIWOWQUUHUVGUVHUVIULAKFUUOFYOWROYMYNY
        IEJWSZWTXAXBZYIUUNUWHXGZUUBFSZUUDUUOSZRZUUCUVGUUFUVHUUGUVIUWMUUBFDUWKUW
        LUHZXCUWMUUDUUOUUEUUNUWKUWLVRZUWMUUBFUWNXDXEUWMUUBFUUDUUOUWOUWNXFXHXIXJ
        LVAYLUUQUUKHYLUUQUUKPZUVNUVMUVPUWEUWCUWGYLEWRPYIWRPZUWPUVNUVMUVPULZVQYL
        EDIUUAUWEXOUWQYLUWHWLUUHUWRAKEYIWRWRUUBESZUUDYISZRZUUCUVNUUFUVMUUGUVPUX
        AUUBEDUWSUWTUHZXCUXAUUDYIUUEUVKUWSUWTVRZUXAUUBEUXBXDXEUXAUUBEUUDYIUXCUX
        BXFXHXKXLXMLVAHDUUPUUQGXNXPWDFUUOEYIUWIUWJXQWFXROXSYLYRYPYKVQUUMYIYJYJE
        EYIGXTYAWFWDYLEYIYEZYRYKYFYLUVPUXDUWGEYIYBWFUUMEYJYIYCXLYD $.
    $}

    $( The set of well-orders of a set ` A ` strictly dominates ` A ` .  A
       stronger form of ~ canth2 .  Corollary 1.4(b) of [KanamoriPincus]
       p. 417.  (Contributed by Mario Carneiro, 31-May-2015.) $)
    canthwe $p |- ( A e. V -> A ~< O ) $=
      ( vu vv vf wcel wbr cvv cxp wss cv wa csn c0 wceq eqid vy vw va vs vz cen
      cdom csdm cpw wwe w3a copab simp1 velpw sylibr simp2 xpss12 syl2anc sstrd
      wn jca ssopab2i df-xp 3sstr4i pwexg sqxpexg pwexd xpexd ssexg sylancr cop
      simpr snssd 0ss a1i wrel rel0 br0 wesn mpbiri mp1i vsnex 0ex simpl sseq1d
      sqxpeqd sseq12d weeq12d 3anbi123d opelopaba syl3anbrc eleqtrrdi ex weq wb
      opth2 mpbiran2 sneqbg elv bitri 2a1i dom2d mpd wf1o wex wf1 cin ccnv cima
      wsbc wral cdm cuni fpwwe2cbv canthwelem f1of1 nsyl nexdv ensym bren sylib
      co cfv brsdom sylanbrc ) BDJZBCUGKZBCUFKZUTBCUHKYFCLJZYGYFCBUIZBBMZUIZMZN
      YMLJYIAOZBNZEOZYNYNMZNZYNYPUJZUKZAEULZYNYJJZYPYLJZPZAEULCYMYTUUDAEYTUUBUU
      CYTYOUUBYOYRYSUMZABUNUOYTYPYKNUUCYTYPYQYKYOYRYSUPYTYOYOYQYKNUUEUUEYNBYNBU
      QURUSEYKUNUOVAVBFAEYJYLVCVDYFYJYLLLBDVEYFYKLBDVFVGVHCYMLVIVJYFGHBCGOZQZRV
      KZHOZQZRVKZLYFUUFBJZUUHCJYFUULPZUUHUUACUUMUUGBNZRUUGUUGMZNZUUGRUJZUUHUUAJ
      UUMUUFBYFUULVLVMUUPUUMUUOVNVORVPZUUQUUMVQUURUUQUUFUUFRKUTUUFUUFVRUUFRVSVT
      WAYTUUNUUPUUQUKAEUUGRGWBWCYNUUGSZYPRSZPZYOUUNYRUUPYSUUQUVAYNUUGBUUSUUTWDZ
      WEUVAYPRYQUUOUUSUUTVLZUVAYNUUGUVBWFWGUVAYNUUGYPRUVCUVBWHWIWJWKFWLWMUUHUUK
      SZGHWNZWOYFUULUUIBJPUVDUUGUUJSZUVEUVDUVFRRSRTUUGRUUJRHWBWCWPWQUVFUVEWOGUU
      FUUILWRWSWTXAXBXCYFCBIOZXDZIXEZYHYFUVHIYFCBUVGXFUVHAUAUBBUCOZBNUDOZUVJUVJ
      MNPUVJUVKUJUUIUVKUUIUUIMXGUVGYBUEOZSHUVKXHUVLQXIXJUEUVJXKPPUCUDULZXLXMZUV
      NUVMYCZXHUVNUVOUVGYBQXIZUVGCDUVMEFUCUEUAUBHBUVGUVMEUDAUVMTXNUVNTUVPTXOCBU
      VGXPXQXRYHCBUFKUVIBCXSCBIXTYAXQBCYDYE $.
  $}

  ${
    $d x A $.
    $( Lemma for ~ canthp1 .  (Contributed by Mario Carneiro, 18-May-2015.) $)
    canthp1lem1 $p |- ( 1o ~< A -> ( A |_| 2o ) ~<_ ~P A ) $=
      ( vx c1o csdm wbr c2o cdju cxp cdom cpw wcel c0 wceq csn cen cvv syl pwen
      sylib syl2anc 1sdom2 djuxpdom mpan2 cv wn wex sdom0 breq2 mtbiri con2i wa
      neq0 relsdom brrelex2i adantr enrefg cpr df2o2 pwpw0 eqtr4i 0ex vex en2sn
      cdif mp2an ax-mp eqbrtri xpen sylancl vsnex pwex uncom simpr snssd eqtrid
      cun wss undif difexd canth2g domunsn 3syl xpdom1g sylancr endomtr pwdjuen
      eqbrtrrd ensymd domentr cin a1i disjdifr endjudisj syl3anc exlimddv domtr
      breqtrd ) CADEZAFGZAFHZIEZWTAJZIEZWSXBIEWRCFDEXAUAAFUBUCWRBUDZAKZXCBWRALM
      ZUEXEBUFXFWRXFWRCLDECUGALCDUHUIUJBAULSWRXEUKZWTAXDNZVDZXHGZJZIEZXKXBOEZXC
      XGWTXIJZXHJZHZIEZXPXKOEXLXGWTAXOHZOEZXRXPIEZXQXGAAOEZFXOOEXSXGAPKZYAWRYBX
      ECADUMUNUOZAPUPQFLNZJZXOOFLYDUQYEURUSUTYDXHOEZYEXOOELPKXDPKYFVABVBLXDPPVC
      VEYDXHRVFVGAAFXOVHVIXGXOPKAXNIEXTXHBVJZVKXGXIXHVPZAXNIXGYHXHXIVPZAXIXHVLX
      GXHAVQYIAMXGXDAWRXEVMVNXHAVRSVOZXGXIPKZXIXNDEYHXNIEXGAXHPYCVSZXIPVTXIXNXD
      WAWBWGAXNXOPWCWDWTXRXPWETXGXKXPXGYKXHPKZXKXPOEYLYGXIXHPPWFVIWHWTXPXKWITXG
      XJAOEXMXGXJYHAOXGYKYMXIXHWJLMZXJYHOEYLYMXGYGWKYNXGXHAWLWKXIXHPPWMWNYJWQXJ
      ARQWTXKXBWITWOWSWTXBWPT $.
  $}

  ${
    $d r x y A $.  $d r x y B $.  $d r x y H $.  $d r x y ph $.  $d r x y W $.
    canthp1lem2.1 $e |- ( ph -> 1o ~< A ) $.
    canthp1lem2.2 $e |- ( ph -> F : ~P A -1-1-onto-> ( A |_| 1o ) ) $.
    canthp1lem2.3 $e |- ( ph ->
      G : ( ( A |_| 1o ) \ { ( F ` A ) } ) -1-1-onto-> A ) $.
    canthp1lem2.4 $e |- H = ( ( G o. F ) o.
      ( x e. ~P A |-> if ( x = A , (/) , x ) ) ) $.
    canthp1lem2.5 $e |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\
      ( r We x /\ A. y e. x ( H ` ( `' r " { y } ) ) = y ) ) } $.
    canthp1lem2.6 $e |- B = U. dom W $.
    $( Lemma for ~ canthp1 .  (Contributed by Mario Carneiro, 18-May-2015.) $)
    canthp1lem2 $p |- -. ph $=
      ( c1o wcel wceq c0 cdju cpw cen wbr cvv wf1o csdm relsdom brrelex2i pwexd
      syl f1oeng syl2anc ensymd wn c2o cdom cfn wpss canth2g wb sdomen2 sdomnen
      com mpbid ccrd cdm con0 omelon onenon ax-mp wss cfv ccnv csn cima cin w3a
      wf ccom cdif cres cv cif cmpt wfun wfo dff1o3 simprbi f1ofo f1ofn fnresdm
      wfn foeq1 4syl mpbird f1osng sylancl pwidg fnressn f1oeq1d resdif syl3anc
      cop fvex f1oco f1oeq1 sylibr f1of wa wne a1i eldifsn sylanbrc eqid pssned
      resco fveq1i sselpwd fvco3d 3eqtr3d adantr eqeq1 id ifbieq2d ifcl sylancr
      fvmptd3 neneqd iffalsed fveq2d fvresd mpd wwe cxp cun df-2o 1oex df-dju
      mto 0elpw sdom0 breq2 mtbii necon2ai ad2antrr simplr neqned ifclda fmpttd
      simpr fcod crn frnd cores eqtr4di feq1d inss1 canth4 simp1d simp2d necomd
      wi simp3d 3eqtr3g pssssd sstrd pssne sylan9eq sspsstr sylan eqtrd anim12i
      3eqtr4d wf1 f1of1 f1fveq syl12anc ex necon3ad npss sylib wex wral elinel1
      pm3.2i ffvelcdm syl2an fpwwe mpbiri fpwwelem simprld weeq1 spcev eqeltrrd
      simpld ween domtri2 infdju1 biimtrrdi ensym syl6 mt3d 2onn djufi isfinite
      nnsdom csuc sssucid sseqtrri xpss2 unss2 mp1i ssun2 snid eleqtrri opelxpi
      sucid mp2an sselii wo 1n0 neii opelxp1 elsni word 1onn nnord mp2b opelxp2
      ordirr pm3.2ni elun mtbir ssnelpss mp2ani psseq12i php3 sdomdomtr pm2.65i
      canthp1lem1 ) ADQUAZDUBZUCUDZAVUCVUBAVUCUERVUCVUBFUFZVUCVUBUCUDZADUEAQDUG
      UDZDUERZKQDUGUHUIUKZUJLVUCVUBUEFULUMZUNAVUBVUCUGUDZVUDUOAVUBDUPUAZUGUDZVU
      LVUCUQUDZVUKAVULURRZVUBVULUSZVUMAVULVDUGUDZVUOADVDUGUDZUPVDUGUDZVUQAVURDV
      UBUCUDZADVUBUGUDZVUTUOADVUCUGUDZVVAAVUHVVBVUIDUEUTUKAVUFVVBVVAVAVUJVUCVUB
      DVBUKVEDVUBVCUKAVURUOZVUBDUCUDZVUTAVVCVDDUQUDZVVDAVDVFVGZRZDVVFRVVEVVCVAV
      DVHRVVGVIVDVJVKAEDVVFAEDVLZEDSZAVVHEIVMZVNZEHVMZVOVPZEUSZVVLVVMHVMZSZAVUH
      VUCDHVSZVUCVVFVQZVUCVLZVVHVVNVVPVRVUIAVUCDGFVTZVUCDVOZWAZWBZBVUCBWCZDSZTV
      WDWDZWEZVTZVSVVQAVUCVWBDVWCVWGAVWBDVWCUFZVWBDVWCVSAVWBDGFVWBWBZVTZUFZVWIA
      VUBDFVMZVOZWAZDGUFVWBVWOVWJUFZVWLMAFVNWFZVUCVUBFVUCWBZWGZVWAVWNFVWAWBZWGZ
      VWPAVUEVWQLVUEVUCVUBFWGZVWQVUCVUBFWHWIUKAVWSVXBAVUEVXBLVUCVUBFWJUKAVUEFVU
      CWMZVWRFSVWSVXBVALVUCVUBFWKZVUCFWLVUCVUBVWRFWNWOWPAVWAVWNVWTUFZVXAAVXEVWA
      VWNDVWMXDVOZUFZAVUHVWMUERVXGVUIDFXEDVWMUEUEWQWRAVWAVWNVWTVXFAVXCDVUCRZVWT
      VXFSAVUEVXCLVXDUKAVUHVXHVUIDUEWSUKVUCDFWTUMXAWPVWAVWNVWTWJUKVUCVWAVUBVWNF
      XBXCVWBVWODGVWJXFUMVWCVWKSVWIVWLVAGFVWBXQVWBDVWCVWKXGVKXHZVWBDVWCXIUKABVU
      CVWFVWBAVWDVUCRZXJZVWETVWDVWBVXKVWEXJZTVUCRZTDXKZTVWBRVXMVXLDUUAZXLAVXNVX
      JVWEAVUGVXNKVUGTDTDSQTUGUDVUGQUUBTDQUGUUCUUDUUEUKUUFTVUCDXMXNVXKVWEUOZXJZ
      VXJVWDDXKVWDVWBRAVXJVXPUUGVXQVWDDVXKVXPUUKUUHVWDVUCDXMXNUUIUUJZUULAVUCDVW
      HHAVWHVVTVWGVTZHAVWGUUMVWBVLVWHVXSSAVUCVWBVWGVXRUUNVVTVWGVWBUUOUKNUUPUUQV
      EZVVSAVUCVVFUURXLBCDEVVMVUCHUEIJOPVVMXOUUSXCZUUTZAEDUSZUOZVVHVVIUVCAEVVMX
      KVYDAVVMEAVVMEAVVHVVNVVPVYAUVAZXPUVBAVYCEVVMAVYCEVVMSZAVYCXJZEVWCVMZVVMVW
      CVMZSZVYFVYGEVVTVMZVVMVVTVMZVYHVYIVYGEVWGVMZVVTVMZVVMVWGVMZVVTVMZVYKVYLAV
      YNVYPSVYCAEVXSVMZVVMVXSVMZVYNVYPAVVLVVOVYQVYRAVVHVVNVVPVYAUVDEHVXSNXRVVMH
      VXSNXRUVEAVUCVWBEVVTVWGVXRAEDUEVUIVYBXSZXTAVUCVWBVVMVVTVWGVXRAVVMDUEVUIAV
      VMEDAVVMEVYEUVFZVYBUVGXSZXTYAYBVYGVYMEVVTAVYCVYMVVITEWDZEABEVWFWUBVUCVWGV
      UCVWGXOZVWDESZVWEVVIVWDETVWDEDYCWUDYDYEVYSAVXMEVUCRZWUBVUCRVXOVYSVVITEVUC
      YFYGYHVYCVVITEVYCEDEDUVHZYIYJUVIYKVYGVYOVVMVVTVYGVYOVVMDSZTVVMWDZVVMAVYOW
      UHSVYCABVVMVWFWUHVUCVWGVUCWUCVWDVVMSZVWEWUGVWDVVMTVWDVVMDYCWUIYDYEWUAAVXM
      VVMVUCRZWUHVUCRVXOWUAWUGTVVMVUCYFYGYHYBVYGWUGTVVMVYGVVMDVYGVVMDAVVMEVLVYC
      VVMDUSVYTVVMEDUVJUVKXPZYIYJUVLYKYAVYGEVWBVVTVYGWUEEDXKZXJEVWBRZAWUEVYCWUL
      VYSWUFUVMEVUCDXMXHZYLVYGVVMVWBVVTVYGWUJVVMDXKVVMVWBRZAWUJVYCWUAYBWUKVVMVU
      CDXMXNZYLUVNVYGVWBDVWCUVOZWUMWUOVYJVYFVAAWUQVYCAVWIWUQVXIVWBDVWCUVPUKYBWU
      NWUPVWBDEVVMVWCUVQUVRVEUVSUVTYMEDUWAUWBYMAEJWCZYNZJUWCZEVVFRAEVVJYNZWUTAV
      VHVVJEEYOVLXJZWVAVVKCWCZVOVPHVMWVCSCEUWDZAEVVJIUDZWVBWVAWVDXJXJAWVEVVLERZ
      AWVEWVFXJEESZVVJVVJSZXJWVGWVHEXOVVJXOUWFABCDVVJHUEIEEJOVUIAVVQVXJVWDHVMDR
      VWDVVRRVXTVWDVUCVVFUWEVUCDVWDHUWGUWHPUWIUWJUWPABCDVVJHUEIEJOVUIUWKVEUWLWU
      SWVAJVVJEIXEEWURVVJUWMUWNUKEJUWQXHUWOVDDUWRYGDUWSUWTVUBDUXAUXBUXCUPVDRVUS
      UXDUPUXGVKDUPUXEWRVULUXFXHATVOZDYOZQVOZQYOZYPZWVJWVKUPYOZYPZUSZVUPAWVMWVO
      VLZWVPWVLWVNVLZWVQAQUPVLWVRQQUXHZUPQUXIYQUXJQUPWVKUXKVKWVLWVNWVJUXLUXMWVQ
      QQXDZWVORWVTWVMRZUOWVPWVNWVOWVTWVNWVJUXNQWVKRQUPRWVTWVNRQYRUXOQWVSUPQYRUX
      RYQUXPQQWVKUPUXQUXSUXTWWAWVTWVJRZWVTWVLRZUYAWWBWWCWWBQTSZQTUYBUYCWWBQWVIR
      WWDQQWVIDUYDQTUYEUKYTWWCQQRZQVDRQUYFWWEUOUYGQUYHQUYKUYIQQWVKQUYJYTUYLWVTW
      VJWVLUYMUYNWVMWVOWVTUYOUYPUKVUBWVMVULWVODQYSDUPYSUYQXHVULVUBUYRUMAVUGVUNK
      DVUAUKVUBVULVUCUYSUMVUBVUCVCUKUYT $.
  $}

  ${
    $d a f g r s w x y z A $.
    $( A slightly stronger form of Cantor's theorem:  For ` 1 < n ` ,
       ` n + 1 < 2 ^ n ` .  Corollary 1.6 of [KanamoriPincus] p. 417.
       (Contributed by Mario Carneiro, 18-May-2015.) $)
    canthp1 $p |- ( 1o ~< A -> ( A |_| 1o ) ~< ~P A ) $=
      ( vf vg vx va vs vz vw c1o csdm wbr cdom cen c2o cvv wcel wfal cv wa wceq
      vy vr cdju cpw 1sdom2 sdomdom ax-mp relsdom brrelex2i djudom2 canthp1lem1
      wn sylancr domtr syl2anc fal wf1o wex ensym bren sylib cfv csn cdif pwidg
      f1of syl ffvelcdm syl2anr dju1dif syl2an2r wss cxp wwe ccnv cima ccom cif
      wf c0 cmpt wral copab cdm cuni simpll simplr simpr eqeq1 ifbieq2d cbvmptv
      id coeq2i eqid fpwwecbv canthp1lem2 pm2.21i exlimddv ex exlimdv syl5 mtoi
      brsdom sylanbrc ) IAJKZAIUCZAUDZLKZXFXGMKZULXFXGJKXEXFANUCZLKZXJXGLKXHXEI
      NLKZAOPZXKINJKXLUEINUFUGIAJUHUIZINAOUJUMAUKXFXJXGUNUOXEXIQUPXIXGXFBRZUQZB
      URZXEQXIXGXFMKXQXFXGUSXGXFBUTVAXEXPQBXEXPQXEXPSZXFAXOVBZVCVDZACRZUQZQCXRX
      TAMKZYBCURXEXMXPXSXFPZYCXNXPXGXFXOVSAXGPZYDXEXGXFXOVFXEXMYEXNAOVEVGXGXFAX
      OVHVIAXSOVJVKXTACUTVAXRYBSZQYFDUAAERZAVLFRZYGYGVMVLSYGYHVNYHVOGRZVCVPYAXO
      VQZHXGHRZATZVTYKVRZWAZVQZVBYITGYGWBSSEFWCZWDWEZXOYAYOYPUBXEXPYBWFXEXPYBWG
      XRYBWHYNDXGDRZATZVTYRVRZWAYJHDXGYMYTYKYRTZYLYSYKYRVTYKYRAWIUUAWLWJWKWMEGU
      AAYOYPUBFDYPWNWOYQWNWPWQWRWSWTXAXBXFXGXCXD $.
  $}

  $( The exclusion of finite sets from consideration in ~ df-gch is necessary,
     because otherwise finite sets larger than a singleton would violate the
     GCH property.  (Contributed by Mario Carneiro, 10-Jun-2015.) $)
  finngch $p |- ( ( A e. Fin /\ 1o ~< A ) ->
      ( A ~< ( A |_| 1o ) /\ ( A |_| 1o ) ~< ~P A ) ) $=
    ( cfn wcel c1o cdju csdm wbr cfin4 cfin2 cfin3 fin12 fin23 fin34 3syl sylib
    cpw isfin4p1 canthp1 anim12i ) ABCZAADEZFGZDAFGUAAPFGTAHCZUBTAICAJCUCAKALAM
    NAQOARS $.

  $( An infinite GCH-set is idempotent under cardinal successor.  (Contributed
     by Mario Carneiro, 18-May-2015.) $)
  gchdju1 $p |- ( ( A e. GCH /\ -. A e. Fin ) -> ( A |_| 1o ) ~~ A ) $=
    ( cgch wcel cfn wn wa c1o cdju cdom wbr cpw csdm cen com a1i djudoml sylan2
    1onn mp1i syl simpr wb nnfi fidomtri2 domfi sylbird mt3d canthp1 jca gchen1
    wi ex mpdan ensymd ) ABCZADCZEZFZAAGHZURAUSIJZUSAKLJZFAUSMJURUTVAUQUOGNCZUT
    VBUQROAGBNPQURGALJZVAURVCUPUOUQUAURVCEZAGIJZUPUQUOGDCZVEVDUBVBVFUQRGUCZSAGB
    UDQURVFVEUPUKVBVFURRVGSVFVEUPGAUEULTUFUGAUHTUIAUSUJUMUN $.

  $( An infinite GCH-set is Dedekind-infinite.  (Contributed by Mario Carneiro,
     31-May-2015.) $)
  gchinf $p |- ( ( A e. GCH /\ -. A e. Fin ) -> _om ~<_ A ) $=
    ( cgch wcel cfn wn wa c1o cdju cen wbr com gchdju1 ensymd cfin4 wb isfin4-2
    cdom adantr csdm isfin4p1 sdomnen sylbi biimtrrdi mt4d ) ABCZADCEZFZAAGHZIJ
    ZKAQJZUGUHAALMUGUJEZANCZUIEZUEULUKOUFABPRULAUHSJUMATAUHUAUBUCUD $.

  ${
    $d n r w x z $.  $d n y z D $.  $d a b s v y F $.  $d w y G $.  $d w y K $.
    $d a b r s v x y z H $.  $d a b n r s v x z ph $.  $d n z ps $.  $d s R $.
    $d a n r s x y z A $.  $d a b s v W $.  $d a b s v Z $.  $d a s Y $.
    pwfseqlem4.g $e |- ( ph -> G : ~P A -1-1-> U_ n e. _om ( A ^m n ) ) $.
    pwfseqlem4.x $e |- ( ph -> X C_ A ) $.
    pwfseqlem4.h $e |- ( ph -> H : _om -1-1-onto-> X ) $.
    pwfseqlem4.ps $e |- ( ps <->
      ( ( x C_ A /\ r C_ ( x X. x ) /\ r We x ) /\ _om ~<_ x ) ) $.
    pwfseqlem4.k $e |- ( ( ph /\ ps ) ->
      K : U_ n e. _om ( x ^m n ) -1-1-> x ) $.
    pwfseqlem4.d $e |- D = ( G ` { w e. x |
      ( ( `' K ` w ) e. ran G /\ -. w e. ( `' G ` ( `' K ` w ) ) ) } ) $.
    $( Lemma for ~ pwfseq .  Derive a contradiction by diagonalization.
       (Contributed by Mario Carneiro, 31-May-2015.) $)
    pwfseqlem1 $p |- ( ( ph /\ ps ) ->
        D e. ( U_ n e. _om ( A ^m n ) \ U_ n e. _om ( x ^m n ) ) ) $=
      ( wa wcel vy com cv cmap co ciun ccnv cfv crn crab cpw wf1 adantr f1f syl
      wn wf wss ssrab2 cxp wwe w3a cdom wbr simprl1 sylan2b sstrid rabex sylibr
      vex elpw ffvelcdmd eqeltrid wb pm5.19 ffvelcdm sylancom wf1o wceq f1f1orn
      f1ocnvfv1 wfn f1fn fnfvelrn syl2anc eqeltrd fveq2 eleq1d id 2fveq3 notbid
      eleq12d anbi12d elrab2 anass bitr4i baib eqtrdi fveq2d eqtrd eleq2d bitrd
      cbvrabv ex mtoi eldifd ) ABSZFGUBEGUCZUDUEUFZGUBCUCZXHUDUEUFZXGFDUCZJUGZU
      HZHUIZTZXLXNHUGZUHZTZUPZSZDXJUJZHUHZXIRXGEUKZXIYBHXGYDXIHULZYDXIHUQAYEBMU
      MZYDXIHUNUOXGYBEURYBYDTZXGYBXJEYADXJUSBAXJEURZLUCZXJXJUTURZXJYIVAZVBUBXJV
      CVDZSYHPYHYJYKYLAVEVFVGYBEYADXJCVJVHVKVIZVLVMXGFXKTZFJUHZYBTZYPUPZVNZYPVO
      XGYNYRXGYNSZYPYOYOXMUHZXQUHZTZUPZYQYSYOXJTZYTXOTZYPUUCVNXGYNXKXJJUQZUUDYS
      XKXJJULZUUFXGUUGYNQUMZXKXJJUNUOXKXJFJVPVQYSYTFXOXGYNXKJUIZJVRZYTFVSYSUUGU
      UJUUHXKXJJVTUOXKUUIFJWAVQZXGFXOTYNXGFYCXORXGHYDWBZYGYCXOTXGYEUULYFYDXIHWC
      UOYMYDYBHWDWEVMUMWFYPUUDUUESZUUCYPUUDUUEUUCSZSUUMUUCSUAUCZXMUHZXOTZUUOUUP
      XQUHZTZUPZSZUUNUAYOXJYBUUOYOVSZUUQUUEUUTUUCUVBUUPYTXOUUOYOXMWGWHUVBUUSUUB
      UVBUUOYOUURUUAUVBWIUUOYOXQXMWJWLWKWMYAUVADUAXJXLUUOVSZXPUUQXTUUTUVCXNUUPX
      OXLUUOXMWGWHUVCXSUUSUVCXLUUOXRUURUVCWIXLUUOXQXMWJWLWKWMXCWNUUDUUEUUCWOWPW
      QWEYSUUBYPYSUUAYBYOYSUUAYCXQUHZYBYSYTYCXQYSYTFYCUUKRWRWSXGUVDYBVSZYNXGYDX
      OHVRZYGUVEXGYEUVFYFYDXIHVTUOYMYDXOYBHWAWEUMWTXAWKXBXDXEXF $.

    $d a r s x V $.
    pwfseqlem4.f $e |- F = ( x e. _V , r e. _V |-> if ( x e. Fin ,
     ( H ` ( card ` x ) ) , ( D ` |^| { z e. _om | -. ( D ` z ) e. x } ) ) ) $.
    $( Lemma for ~ pwfseq .  (Contributed by Mario Carneiro, 18-Nov-2014.)
       (Revised by AV, 18-Sep-2021.) $)
    pwfseqlem2 $p |- ( ( Y e. Fin /\ R e. V ) ->
        ( Y F R ) = ( H ` ( card ` Y ) ) ) $=
      ( va vs cv co ccrd cfv wceq cfn oveq1 2fveq3 eqeq12d eqeq1d nfcv cvv wcel
      oveq2 com crab cint cif cmpo nfmpo1 nfcxfr nfov nfeq1 nfmpo2 weq vex fvex
      wn ifex ovmpt4g mp3an iftrue eqtrid adantr vtocl2gaf vtocl2ga ) UEUGZUFUG
      ZJUHZWCUIUJLUJZUKZPWDJUHZPUIUJLUJZUKPHJUHZWIUKUEUFPHULNWCPUKWEWHWFWIWCPWD
      JUMWCPLUIUNUOWDHUKWHWJWIWDHPJUTUPCUGZQUGZJUHZWKUIUJZLUJZUKZWCWLJUHZWFUKWG
      CQWCWDULNCWCUQZQWCUQZQWDUQZCWQWFCWCWLJWRCJCQURURWKULUSZWODUGGUJWKUSVNDVAV
      BVCZGUJZVDZVEZUDCQURURXDVFVGCWLUQVHVIQWEWFQWCWDJWSQJXEUDCQURURXDVJVGWTVHV
      ICUEVKWMWQWOWFWKWCWLJUMWKWCLUIUNUOQUFVKWQWEWFWLWDWCJUTUPXAWPWLNUSXAWMXDWO
      WKURUSWLURUSXDURUSWMXDUKCVLQVLXAWOXCWNLVMXBGVMVOCQURURXDJURUDVPVQXAWOXCVR
      VSVTWAWB $.

    $( Lemma for ~ pwfseq .  Using the construction ` D ` from ~ pwfseqlem1 ,
       produce a function ` F ` that maps any well-ordered infinite set to an
       element outside the set.  (Contributed by Mario Carneiro,
       31-May-2015.) $)
    pwfseqlem3 $p |- ( ( ph /\ ps ) -> ( x F r ) e. ( A \ x ) ) $=
      ( vy wa cv co cfv wcel com crab cint cdif cfn ccrd cif cvv wceq fvex ifex
      wn vex ovmpt4g mp3an csdm wbr cdom wss cxp wwe w3a simprbi adantl domnsym
      syl isfinite iffalsed eqtrid cmap ciun wrex pwfseqlem1 eldif sylib simpld
      sylnibr eliun wf elmapi ad2antll wral ssiun2 ad2antrl simprd adantr elmap
      ssneldd wfn wb ffnfv baib 3syl bitrid mtbid con0 nnon ssrab2 omsson sstri
      ffn wne word ordom simprl ordelss sylancr rexnal sylibr ssrexv sylc rabn0
      c0 onint sselid ontri1 syl2anc wi ssintrab syl2an imbi2d bitr4di pm5.74da
      con34b bi2.04 bitrdi elnn pm2.27 expcom a2d fveq2 eleq1d notbid ffvelcdmd
      sylbid ralimdv2 biimtrid sylbird cbvrabv elrab2 eldifd rexlimddv eqeltrd
      mt3d ) ABUCZCUDZNUDZIUEZDUDZGUFZUUMUGZUSZDUHUIZUJZGUFZFUUMUKZUULUUOUUMULU
      GZUUMUMUFZKUFZUVBUNZUVBUUMUOUGUUNUOUGUVGUOUGUUOUVGUPCUTZNUTUVDUVFUVBUVEKU
      QUVAGUQURCNUOUOUVGIUOUAVAVBUULUVDUVFUVBUULUUMUHVCVDZUVDUULUHUUMVEVDZUVIUS
      BUVJABUUMFVFUUNUUMUUMVGVFUUMUUNVHVIUVJRVJVKUHUUMVLVMUUMVNWDVOVPUULGFHUDZV
      QUEZUGZUVBUVCUGHUHUULGHUHUVLVRZUGZUVMHUHVSUULUVOGHUHUUMUVKVQUEZVRZUGUSZUU
      LGUVNUVQUKUGUVOUVRUCABCEFGHJKLMNOPQRSTVTGUVNUVQWAWBZWCHGUHUVLWEWBUULUVKUH
      UGZUVMUCZUCZUVBFUUMUWBUVKFUVAGUVMUVKFGWFZUULUVTGFUVKWGWHZUWBUVAUVKUGZUURD
      UVKWIZUWBGUVPUGZUWFUWBUVPUVQGUVTUVPUVQVFUULUVMHUHUVPWJWKUULUVRUWAUULUVOUV
      RUVSWLWMWOUWGUVKUUMGWFZUWBUWFUUMUVKGUVHHUTWNUWBUWCGUVKWPZUWHUWFWQUWDUVKFG
      XHUWHUWIUWFDUVKUUMGWRWSWTXAXBZUWBUWEUSZUVKUVAVFZUWFUWBUVKXCUGZUVAXCUGUWLU
      WKWQUVTUWMUULUVMUVKXDZWKUWBUUTXCUVAUUTUHXCUUSDUHXEXFXGZUWBUUTXCVFUUTXTXIZ
      UVAUUTUGZUWOUWBUUSDUHVSZUWPUWBUVKUHVFZUUSDUVKVSZUWRUWBUHXJUVTUWSXKUULUVTU
      VMXLUHUVKXMXNUWBUWFUSUWTUWJUURDUVKXOXPUUSDUVKUHXQXRUUSDUHXSXPUUTYAXNZYBUV
      KUVAYCYDUWLUUSUVKUUPVFZYEZDUHWIUWBUWFUUSDUVKUHYFUWBUXCUURDUHUVKUVTUUPUHUG
      ZUXCYEZUUPUVKUGZUURYEZYEUULUVMUVTUXEUXFUXDUURYEZYEZUXGUVTUXEUXDUXGYEUXIUV
      TUXDUXCUXGUVTUXDUCZUXCUUSUXFUSZYEUXGUXJUXBUXKUUSUVTUWMUUPXCUGUXBUXKWQUXDU
      WNUUPXDUVKUUPYCYGYHUXFUURYKYIYJUXDUXFUURYLYMUVTUXFUXHUURUXFUVTUXHUURYEZUX
      FUVTUCUXDUXLUUPUVKYNUXDUURYOVMYPYQUUBWKUUCUUDUUEUUKUUAUWBUWQUVBUUMUGZUSZU
      XAUWQUVAUHUGUXNUBUDZGUFZUUMUGZUSZUXNUBUVAUHUUTUXOUVAUPZUXQUXMUXSUXPUVBUUM
      UXOUVAGYRYSYTUUSUXRDUBUHUUPUXOUPZUURUXQUXTUUQUXPUUMUUPUXOGYRYSYTUUFUUGVJV
      MUUHUUIUUJ $.

    $( Lemma for ~ pwfseqlem4 .  (Contributed by Mario Carneiro,
       7-Jun-2016.) $)
    pwfseqlem4a $p |- ( ( ph /\ ( a C_ A /\ s C_ ( a X. a ) /\ s We a ) ) ->
      ( a F s ) e. A ) $=
      ( cv wss cxp wwe w3a wa com csdm wbr co wcel cfn isfinite wi ccrd cfv cvv
      wceq simpr vex pwfseqlem2 sylancl wf wf1o f1of syl fssd ficardom ffvelcdm
      syl2an eqeltrd ex adantr biimtrrid wn cdom cdm wb omelon onenon ax-mp wex
      con0 simpr3 19.8ad ween sylibr domtri2 sylancr cdif nfcv crab cint nfmpo2
      nfv cif cmpo nfcxfr nfov nfel1 nfim weq sseq1 weeq1 3anbi23d anbi1d oveq2
      anbi2d eleq1d imbi12d nfmpo1 xpeq12 anidms sseq2d weeq2 3anbi123d anbi12d
      breq2 bitrid oveq1 difeq2 eleq12d pwfseqlem3 chvarfv eldifad expr sylbird
      pm2.61d ) APUDZFUEZNUDZYLYLUFZUEZYLYNUGZUHZUIZYLUJUKULZYLYNIUMZFUNZYTYLUO
      UNZYSUUBYLUPAUUCUUBUQYRAUUCUUBAUUCUIZUUAYLURUSZKUSZFUUDUUCYNUTUNUUAUUFVAA
      UUCVBNVCABCDEFGYNHIJKLUTMYLOQRSTUAUBUCVDVEAUJFKVFUUEUJUNUUFFUNUUCAUJMFKAU
      JMKVGUJMKVFSUJMKVHVIRVJYLVKUJFUUEKVLVMVNVOVPVQYSYTVRZUJYLVSULZUUBYSUJURVT
      ZUNZYLUUIUNZUUHUUGWAUJWFUNUUJWBUJWCWDYSYQNWEUUKYSYQNAYMYPYQWGWHYLNWIWJUJY
      LWKWLAYRUUHUUBAYRUUHUIZUIZUUAFYLAYMOUDZYOUEZYLUUNUGZUHZUUHUIZUIZYLUUNIUMZ
      FYLWMZUNZUQZUUMUUAUVAUNZUQONUUMUVDOUUMOWROUUAUVAOYLYNIOYLWNOICOUTUTCUDZUO
      UNUVEURUSKUSDUDGUSUVEUNVRDUJWOWPGUSWSZWTZUCCOUTUTUVFWQXAOYNWNXBXCXDONXEZU
      USUUMUVBUVDUVHUURUULAUVHUUQYRUUHUVHUUOYPUUPYQYMUUNYNYOXFYLUUNYNXGXHXIXKUV
      HUUTUUAUVAUUNYNYLIXJXLXMABUIZUVEUUNIUMZFUVEWMZUNZUQUVCCPUUSUVBCUUSCWRCUUT
      UVACYLUUNICYLWNCIUVGUCCOUTUTUVFXNXACUUNWNXBXCXDCPXEZUVIUUSUVLUVBUVMBUURAB
      UVEFUEZUUNUVEUVEUFZUEZUVEUUNUGZUHZUJUVEVSULZUIUVMUURTUVMUVRUUQUVSUUHUVMUV
      NYMUVPUUOUVQUUPUVEYLFXFUVMUVOYOUUNUVMUVOYOVAUVEYLUVEYLXOXPXQUVEYLUUNXRXSU
      VEYLUJVSYAXTYBXKUVMUVJUUTUVKUVAUVEYLUUNIYCUVEYLFYDYEXMABCDEFGHIJKLMOQRSTU
      AUBUCYFYGYGYHYIYJYK $.

    pwfseqlem4.w $e |- W = { <. a , s >. |
    ( ( a C_ A /\ s C_ ( a X. a ) ) /\ ( s We a /\ A. b e. a
      [. ( `' s " { b } ) / v ]. ( v F ( s i^i ( v X. v ) ) ) = b ) ) } $.
    pwfseqlem4.z $e |- Z = U. dom W $.
    $( Lemma for ~ pwfseq .  Derive a final contradiction from the function
       ` F ` in ~ pwfseqlem3 .  Applying ~ fpwwe2 to it, we get a certain
       maximal well-ordered subset ` Z ` , but the defining property
       ` ( Z F ( W `` Z ) ) e. Z ` contradicts our assumption on ` F ` , so we
       are reduced to the case of ` Z ` finite.  This too is a contradiction,
       though, because ` Z ` and its preimage under ` ( W `` Z ) ` are distinct
       sets of the same cardinality and in a subset relation, which is
       impossible for finite sets.  (Contributed by Mario Carneiro,
       31-May-2015.)  (Proof shortened by Matthew House, 10-Sep-2025.) $)
    pwfseqlem4 $p |- -. ph $=
      ( ccrd cfv wbr ccnv csn cima wcel co cfn cvv wceq com csdm wss cxp wwe wa
      w3a cv cin wsbc wral eqid pm3.2i cpw cmap ciun wf1 omex ovex iunex f1dmex
      sylancl pwexb sylibr pwfseqlem4a fpwwe2 mpbiri simpld fpwwe2lem2 mpbid id
      3expa adantrr syl simprd ssexd fvexd simpl sseq1d sqxpeqd sseq12d weeq12d
      wi simpr 3anbi123d oveq12 eleq12d breq1d imbi12d wn cdom wb omelon onenon
      cdm con0 ax-mp wex simpr3 19.8ad ween domtri2 cdif nfcv nfcxfr nfov nfel1
      nfv nfim weq sseq1 anbi2d chvarfv sylbird fvex pwfseqlem2 ficardom finnum
      ex syl2anc sylancr crab cint cif cmpo nfmpo2 weeq1 3anbi23d anbi1d eleq1d
      oveq2 nfmpo1 xpeq12 anidms sseq2d weeq2 breq2 anbi12d bitrid oveq1 difeq2
      pwfseqlem3 eldifbd expr con4d mp2d isfinite eqeltrrd cen fpwwe2lem3 mpdan
      vtocl2d cnvimass dmss dmxpss sstrdi sstrid ssfid inex1 eqtr3d wf1o f1fveq
      f1of1 syl12anc eqcomd carden2 wpss dfpss2 baib php3 sdomnen mt4d eleqtrrd
      eliniseg sylib wor weso sonr pm2.65i ) APUJUKZLUKZUXAPNUKZULZAUXAUXBUMZUX
      AUNZUOZUPZUXCAUXAPUXFAPUXBJUQZUXAPAPURUPZUXBUSUPUXHUXAUTAPVAVBULZUXIAPGVC
      ZUXBPPVDZVCZPUXBVEZVGZUXHPUPZUXJAUXKUXMVFZUXNFVHZUXBUXRUXRVDVIJUQTVHZUTFU
      XDUXSUNUOVJTPVKZVFZVFZUXOAPUXBNULZUYBAUYCUXPAUYCUXPVFPPUTZUXBUXBUTZVFUYDU
      YEPVLUXBVLVMASTFGUXBJUSNPPQUHAGVNZUSUPZGUSUPAUYFIVAGIVHZVOUQZVPZKVQUYJUSU
      PUYGUAIVAUYIVRGUYHVOVSVTUYFUYJUSKWAWBGWCWDZABCDEGHIJKLMOQRSUAUBUCUDUEUFUG
      WEUIWFWGZWHZASTFGUXBJUSNPQUHUYKWIWJZUXQUXNUXOUXTUXKUXMUXNUXOUXOWKWLWMWNAU
      YCUXPUYLWOZASVHZGVCZQVHZUYPUYPVDZVCZUYPUYRVEZVGZUYPUYRJUQZUYPUPZUYPVAVBUL
      ZXCZXCUXOUXPUXJXCZXCSQPUXBUSUSAPGUSUYKAUXKUXMAUXQUYAUYNWHZWHWPAPNWQUYPPUT
      ZUYRUXBUTZVFZVUBUXOVUFVUGVUKUYQUXKUYTUXMVUAUXNVUKUYPPGVUIVUJWRZWSVUKUYRUX
      BUYSUXLVUIVUJXDZVUKUYPPVULWTXAVUKUYPPUYRUXBVUMVULXBXEVUKVUDUXPVUEUXJVUKVU
      CUXHUYPPUYPPUYRUXBJXFVULXGVUKUYPPVAVBVULXHXIXIAVUBVUFAVUBVFZVUEVUDVUNVUEX
      JZVAUYPXKULZVUDXJZVUNVAUJXOZUPZUYPVURUPZVUPVUOXLVAXPUPVUSXMVAXNXQVUNVUAQX
      RVUTVUNVUAQAUYQUYTVUAXSXTUYPQYAWDVAUYPYBUUAAVUBVUPVUQAVUBVUPVFZVFZVUCGUYP
      AUYQRVHZUYSVCZUYPVVCVEZVGZVUPVFZVFZUYPVVCJUQZGUYPYCZUPZXCZVVBVUCVVJUPZXCR
      QVVBVVMRVVBRYHRVUCVVJRUYPUYRJRUYPYDRJCRUSUSCVHZURUPVVNUJUKLUKDVHHUKVVNUPX
      JDVAUUBUUCHUKUUDZUUEZUGCRUSUSVVOUUFYERUYRYDYFYGYIRQYJZVVHVVBVVKVVMVVQVVGV
      VAAVVQVVFVUBVUPVVQVVDUYTVVEVUAUYQVVCUYRUYSYKUYPVVCUYRUUGUUHUUIYLVVQVVIVUC
      VVJVVCUYRUYPJUUKUUJXIABVFZVVNVVCJUQZGVVNYCZUPZXCVVLCSVVHVVKCVVHCYHCVVIVVJ
      CUYPVVCJCUYPYDCJVVPUGCRUSUSVVOUULYECVVCYDYFYGYICSYJZVVRVVHVWAVVKVWBBVVGAB
      VVNGVCZVVCVVNVVNVDZVCZVVNVVCVEZVGZVAVVNXKULZVFVWBVVGUDVWBVWGVVFVWHVUPVWBV
      WCUYQVWEVVDVWFVVEVVNUYPGYKVWBVWDUYSVVCVWBVWDUYSUTVVNUYPVVNUYPUUMUUNUUOVVN
      UYPVVCUUPXEVVNUYPVAXKUUQUURUUSYLVWBVVSVVIVVTVVJVVNUYPVVCJUUTVVNUYPGUVAXGX
      IABCDEGHIJKLMORUAUBUCUDUEUFUGUVBYMYMUVCUVDYNUVEYSUVLUVFPUVGWDZPNYOZABCDEG
      HUXBIJKLMUSOPRUAUBUCUDUEUFUGYPWBUYOUVHZAUXFPUVIULZUXFPUTZAUXFUJUKZUWTUTZV
      WLAUWTVWNAUXAVWNLUKZUTZUWTVWNUTZAUXFUXBUXFUXFVDZVIZJUQZUXAVWPAUXAPUPZVXAU
      XAUTVWKASTFGUXAUXBJUSNPQUHUYKUYMUVJUVKAUXFURUPZVWTUSUPVXAVWPUTAPUXFVWIAUX
      FUXBXOZPUXBUXEUVMAVXDUXLXOZPAUXMVXDVXEVCAUXKUXMVUHWOUXBUXLUVNWNPPUVOUVPUV
      QZUVRZUXBVWSVWJUVSABCDEGHVWTIJKLMUSOUXFRUAUBUCUDUEUFUGYPWBUVTAVAOLVQZUWTV
      AUPZVWNVAUPZVWQVWRXLAVAOLUWAVXHUCVAOLUWCWNAUXIVXIVWIPYQWNAVXCVXJVXGUXFYQW
      NVAOUWTVWNLUWBUWDWJUWEAUXFVURUPZPVURUPZVWOVWLXLAVXCVXKVXGUXFYRWNAUXIVXLVW
      IPYRWNUXFPUWFYTWJAVWMXJZUXFPUWGZVWLXJZAUXFPVCZVXNVXMXLVXFVXNVXPVXMUXFPUWH
      UWIWNAUXIVXNVXOXCVWIUXIVXNVXOUXIVXNVFUXFPVBULVXOPUXFUWJUXFPUWKWNYSWNYNUWL
      UWMUXAUSUPUXGUXCXLUWTLYOZUXBUXAUXAUSVXQUWNXQUWOAPUXBUWPZVXBUXCXJAUXNVXRAU
      XNUXTAUXQUYAUYNWOWHPUXBUWQWNVWKPUXAUXBUWRYTUWS $.
  $}

  ${
    $d a b c d i j m n s w z G $.  $d a b c d j m r s t w z H $.  $d f k x P $.
    $d a b c d f i j k m n r s t u v w x y z $.  $d a b k n r s t w x y z ph $.
    $d a b c d i j m n s w z K $.  $d b N $.  $d k n x y z ps $.  $d n y S $.
    $d a b c d n r s t w z A $.  $d b u v x y O $.
    pwfseqlem5.g $e |- ( ph -> G : ~P A -1-1-> U_ n e. _om ( A ^m n ) ) $.
    pwfseqlem5.x $e |- ( ph -> X C_ A ) $.
    pwfseqlem5.h $e |- ( ph -> H : _om -1-1-onto-> X ) $.
    pwfseqlem5.ps $e |- ( ps <->
      ( ( t C_ A /\ r C_ ( t X. t ) /\ r We t ) /\ _om ~<_ t ) ) $.
    pwfseqlem5.n $e |- ( ph -> A. b e. ( har ` ~P A ) ( _om C_ b ->
      ( N ` b ) : ( b X. b ) -1-1-onto-> b ) ) $.
    pwfseqlem5.o $e |- O = OrdIso ( r , t ) $.
    pwfseqlem5.t $e |- T =
      ( u e. dom O , v e. dom O |-> <. ( O ` u ) , ( O ` v ) >. ) $.
    pwfseqlem5.p $e |- P = ( ( O o. ( N ` dom O ) ) o. `' T ) $.
    pwfseqlem5.s $e |- S = seqom ( ( k e. _V , f e. _V |->
      ( x e. ( t ^m suc k ) |-> ( ( f ` ( x |` k ) ) P ( x ` k ) ) ) ) ,
      { <. (/) , ( O ` (/) ) >. } ) $.
    pwfseqlem5.q $e |- Q = ( y e. U_ n e. _om ( t ^m n ) |->
      <. dom y , ( ( S ` dom y ) ` y ) >. ) $.
    pwfseqlem5.i $e |- I = ( x e. _om , y e. t |-> <. ( O ` x ) , y >. ) $.
    pwfseqlem5.k $e |- K = ( ( P o. I ) o. Q ) $.
    $( Lemma for ~ pwfseq .  Although in some ways ~ pwfseqlem4 is the "main"
       part of the proof, one last aspect which makes up a remark in the
       original text is by far the hardest part to formalize.  The main proof
       relies on the existence of an injection ` K ` from the set of finite
       sequences on an infinite set ` x ` to ` x ` .  Now this alone would not
       be difficult to prove; this is mostly the claim of ~ fseqen .  However,
       what is needed for the proof is a _canonical_ injection on these sets,
       so we have to start from scratch pulling together explicit bijections
       from the lemmas.

       If one attempts such a program, it will mostly go through, but there is
       one key step which is inherently nonconstructive, namely the proof of
       ~ infxpen .  The resolution is not obvious, but it turns out that
       reversing an infinite ordinal's Cantor normal form absorbs all the
       non-leading terms ( ~ cnfcom3c ), which can be used to construct a
       pairing function explicitly using properties of the ordinal exponential
       ( ~ infxpenc ).  (Contributed by Mario Carneiro, 31-May-2015.) $)
    pwfseqlem5 $p |- -. ph $=
      ( vz vi vw vc vd vj vm vs va cv ccnv cfv crn wcel wn wa crab cvv cfn ccrd
      com cint cif cmpo wss cxp wwe cin wceq csn cima wsbc wral copab cuni cmap
      co cdm ciun ccom wf1 wf1o cep wiso vex w3a cdom wbr simprl3 sylan2b oiiso
      sylancr isof1o syl cardom cen simprr oien ensymd domentr syl2anc wb ax-mp
      con0 onenon mp1i wi f1oeq1d adantr a1i sylibr f1oco cmpt wf feqmptd mpbid
      cop xpf1o f1oeq1 f1of1 cres f1co c0 eqid omelon oion elv mpbird eqsstrrid
      carddom2 cardonle sstrd cpw char sseq2 fveq2 xpeq12 anidms f1oeq2d f1oeq3
      3bitrd imbi12d omex ovex iunex f1dmex sylancl simprl1 ssdomg sylc canth2g
      pwexb csdm sdomdom 3syl endomtr elharval sylanbrc rspcdva mpd f1of f1ocnv
      domtr f1ssres f1f1orn feqresmpt cid mptresid eqcomi f1oi mpbiri f1f xpss1
      4syl f1ss peano1 sseldd ffvelcdmd fseqenlem2 f1eq1 fpwwe2cbv pwfseqlem4
      frn ) ABGUQURUSHURVFZSVGVHZPVIVJUWTUXAPVGVHVJVKVLURGVFZVMPVHZOGUCVNVNUXBV
      OVJUXBVPVHQVHUQVFUXCVHUXBVJVKUQVQVMVRUXCVHVSVTZPQSUTVFZHWAVAVFZUXEUXEWBWA
      VLUXEUXFWCVBVFZUXFUXGUXGWBWDUXDWMVCVFZWEVBUXFVGUXHWFWGWHVCUXEWIVLVLUTVAWJ
      ZUBUXIWNWKZVDUCVEUDUEUFUGUHABVLZOVQUXBOVFZWLWMWOZUXBIRWPZJWPZWQZUXMUXBSWQ
      ZUXKVQUXBWBZUXBUXNWQZUXMUXRJWQUXPUXKUXBUXBWBZUXBIWQZUXRUXTRWQZUXSUXKUXTUX
      BIWRZUYAUXKUXTUXBUAUAWNZTVHZWPZLVGZWPZWRZUYCUXKUYDUYDWBZUXBUYFWRZUXTUYJUY
      GWRZUYIUXKUYDUXBUAWRZUYJUYDUYEWRZUYKUXKUYDUXBWSUCVFZUAWTZUYMUXKUXBVNVJZUX
      BUYOWCZUYPGXAZBAUXBHWAZUYOUXTWAZUYRXBZVQUXBXCXDZVLZUYRUHUYTVUAUYRVUCAXEXF
      ZUXBUYOUAVNUJXGXHUYDUXBWSUYOUAXIXJZUXKVQUYDWAZUYNUXKVQUYDVPVHZUYDUXKVQVQV
      PVHZVUHXKUXKVUIVUHWAZVQUYDXCXDZUXKVUCUXBUYDXLXDVUKBAVUDVUCUHAVUBVUCXMXFUX
      KUYDUXBUXKUYQUYRUYDUXBXLXDZUYSVUEUXBUYOUAVNUJXNXHZXOVQUXBUYDXPXQUXKVQVPWN
      ZVJZUYDVUNVJZVUJVUKXRVQXTVJVUOUUAVQYAXSUYDXTVJZVUPUXKVUQGUXBUYOUAVNUJUUBU
      UCZUYDYAYBVQUYDUUFXHUUDUUEVUQVUHUYDWAUXKVURUYDUUGYBUUHZUXKVQUDVFZWAZVUTVU
      TWBZVUTVUTTVHZWRZYCZVUGUYNYCUDHUUIZUUJVHZUYDVUTUYDWEZVVAVUGVVDUYNVUTUYDVQ
      UUKVVHVVDVVBVUTUYEWRUYJVUTUYEWRUYNVVHVVBVUTVVCUYEVUTUYDTUULYDVVHVVBUYJVUT
      UYEVVHVVBUYJWEVUTUYDVUTUYDUUMUUNUUOVUTUYDUYJUYEUUPUUQUURAVVEUDVVGWIBUIYEU
      XKVUQUYDVVFXCXDZUYDVVGVJVUQUXKVURYFUXKVULUXBVVFXCXDZVVIVUMUXKUXBHXCXDZHVV
      FXCXDZVVJUXKHVNVJZUYTVVKUXKVVFVNVJZVVMUXKVVFOVQHUXLWLWMZWOZPWQZVVPVNVJVVN
      AVVQBUEYEOVQVVOUUSHUXLWLUUTUVAVVFVVPVNPUVBUVCHUVHYGZBAVUDUYTUHUYTVUAUYRVU
      CAUVDXFUXBHVNUVEUVFUXKVVMHVVFUVIXDVVLVVRHVNUVGHVVFUVJUVKUXBHVVFUVSXQUYDUX
      BVVFUVLXQVVFUYDUVMUVNUVOUVPUYJUYDUXBUAUYEYHXQUXKUYJUXTLWRZUYLUXKUYJUXTFEU
      YDUYDFVFUAVHZEVFUAVHZYMVTZWRZVVSUXKFEUYDUXBUYDUXBVVTVWAUXKUYMUYDUXBFUYDVV
      TYIZWRVUFUXKUYDUXBUAVWDUXKFUYDUXBUAUXKUYMUYDUXBUAYJVUFUYDUXBUAUVQXJZYKYDY
      LUXKUYMUYDUXBEUYDVWAYIZWRVUFUXKUYDUXBUAVWFUXKEUYDUXBUAVWEYKYDYLYNLVWBWEVV
      SVWCXRUKUYJUXTLVWBYOXSYGUYJUXTLUVRXJUXTUYJUXBUYFUYGYHXQIUYHWEUYCUYIXRULUX
      TUXBIUYHYOXSYGZUXTUXBIYPXJUXKUXRUAVQYQZVIZUXBWBZRWQZVWJUXTWAZUYBUXKUXRVWJ
      RWRZVWKUXKUXRVWJCDVQUXBCVFUAVHZDVFZYMVTZWRZVWMUXKCDVQVWIUXBUXBVWNVWOUXKVQ
      VWIVWHWRZVQVWICVQVWNYIZWRUXKVQUXBVWHWQZVWRUXKUYDUXBUAWQZVUGVWTUXKUYMVXAVU
      FUYDUXBUAYPXJVUSUYDUXBVQUAUVTXQZVQUXBVWHUWAXJUXKVQVWIVWHVWSUXKCUYDUXBVQUA
      VWEVUSUWBYDYLDUXBVWOYIZUWCUXBYQZWEZUXBUXBVXCWRZUXKVXDVXCDUXBUWDUWEVXEVXFU
      XBUXBVXDWRUXBUWFUXBUXBVXCVXDYOUWGYBYNRVWPWEVWMVWQXRUOUXRVWJRVWPYOXSYGUXRV
      WJRYPXJUXKVWTVQUXBVWHYJVWIUXBWAVWLVXBVQUXBVWHUWHVQUXBVWHUWSVWIUXBUXBUWIUW
      JUXRVWJUXTRUWKXQUXRUXTUXBIRYRXQUXKCDUXBYSUAVHMONIKJVNUYQUXKUYSYFUXKUYDUXB
      YSUAVWEUXKVQUYDYSVUSYSVQVJUXKUWLYFUWMUWNVWGUMUNUWOUXMUXRUXBUXNJYRXQSUXOWE
      UXQUXPXRUPUXMUXBSUXOUWPXSYGUXCYTUXDYTUTVCUDUSVBHUXDUXIVDVAVEUXIYTUWQUXJYT
      UWR $.
  $}

  ${
    $d b f g h k m n p r s t u w x y z A $.
    $( The powerset of a Dedekind-infinite set does not inject into the set of
       finite sequences.  The proof is due to Halbeisen and Shelah.
       Proposition 1.7 of [KanamoriPincus] p. 418.  (Contributed by Mario
       Carneiro, 31-May-2015.) $)
    pwfseq $p |- ( _om ~<_ A -> -. ~P A ~<_ U_ n e. _om ( A ^m n ) ) $=
      ( vt vh vb vm vg vx vy vk vw com cv cmap co wss wa wf1o cfv eqid vu vr vz
      vs vp vf cvv wcel cdom wbr cpw ciun wn reldom brrelex2i cen wex domeng wi
      bren cxp char wral con0 harcl infxpenc2 wf1 wwe w3a coi cdm ccom cop cmpo
      ax-mp ccnv csuc cres cmpt c0 csn cseqom wceq oveq2 cbviunv bilani simpllr
      f1eq3 simplll biid simplr sseq2 fveq2 f1oeq1d xpeq12 anidms f1oeq3 3bitrd
      wb f1oeq2d imbi12d cbvralvw sylib mpteq1i pwfseqlem5 imnani nexdv nsyl ex
      brdomi exlimdv mpi exlimiv sylbi imp biimtrdi mpcom ) AUGUHZLAUIUJZAUKZBL
      ABMZNOZULZUIUJZUMZLAUIUNUOXRXSLCMZUPUJZYFAPZQZCUQYECLAUGURYIYECYGYHYEYGLY
      FDMZRZDUQYHYEUSZLYFDUTYKYLDYKYHYEYKYHQZLEMZPZYNYNVAZYNYNFMZSZRZUSZEXTVBSZ
      VCZFUQZYEUUAVDUHUUCXTVEUUAFEVFVOYMUUBYEFYMUUBYEYMUUBQZXTYCGMZVGZGUQYDUUDU
      UFGUUDUUFUUDUUFQZUAMZAPUBMZUUHUUHVAPUUHUUIVHVILUUHUIUJQZHIUCUDUAAUUHUUIVJ
      ZUUKVKZYQSVLUDUCUULUULUDMUUKSUCMUUKSVMVNZVPVLZIBLUUHYANOZULZIMZVKZUUQUURU
      EUFUGUGHUUHUEMZVQNOHMZUUSVRUFMSUUSUUTSUUNOVSVNVTVTUUKSVMWAWBZSSVMZVSZUVAU
      UMUFUEJUUEYJHILUUHUUTUUKSUUQVMVNZUUNUVDVLUVCVLZYQUUKYFUBKUUFXTJLAJMZNOZUL
      ZUUEVGZUUDYCUVHWCUUFUVIWSBJLYBUVGYAUVFANWDWEYCUVHXTUUEWHVOWFYKYHUUBUUFWGY
      KYHUUBUUFWIUUJWJUUGUUBLKMZPZUVJUVJVAZUVJUVJYQSZRZUSZKUUAVCYMUUBUUFWKYTUVO
      EKUUAYNUVJWCZYOUVKYSUVNYNUVJLWLUVPYSYPYNUVMRUVLYNUVMRUVNUVPYPYNYRUVMYNUVJ
      YQWMWNUVPYPUVLYNUVMUVPYPUVLWCYNUVJYNUVJWOWPWTYNUVJUVLUVMWQWRXAXBXCUUKTUUM
      TUUNTUVATIUUPJLUUHUVFNOZULUVBBJLUUOUVQYAUVFUUHNWDWEXDUVDTUVETXEXFXGXTYCGX
      JXHXIXKXLXIXMXNXOXMXPXQ $.

    $( The powerset of a Dedekind-infinite set does not inject into its
       Cartesian product with itself.  (Contributed by Mario Carneiro,
       31-May-2015.)  (Proof shortened by AV, 18-Jul-2022.) $)
    pwxpndom2 $p |- ( _om ~<_ A -> -. ~P A ~<_ ( A |_| ( A X. A ) ) ) $=
      ( vn vx com cdom wbr cv cmap co c1o c2o cen c0 wceq cvv wcel a1i ensym wn
      wss cpw cxp cdju ciun pwfseq wi cun cin reldom brrelex2i csn df1o2 oveq2i
      id 0ex mapsnend eqbrtrid 3syl map2xp wa cdm elmapi fdmd adantr csuc sucid
      1oex df-2o eleqtrri 1on onirri nelneq2 mp2an adantl eqeq1d mtbiri pm2.65i
      elin mtbir eq0rdv djuenun syl3anc omex ovex iunex 1onn oveq2 ssiun2s 2onn
      ax-mp unssi ssdomg mp2 endomtr sylancl domtr expcom syl mtod ) DAEFZAUAZA
      AAUBZUCZEFZXABDABGZHIZUDZEFZABUEWTXCXGEFZXDXHUFWTXCAJHIZAKHIZUGZLFZXLXGEF
      ZXIWTAXJLFZXBXKLFZXJXKUHZMNXMWTAOPZXJALFXODAEUIUJZXRXJAMUKZHIALJXTAHULUMX
      RAMOOXRUNMOPXRUOQUPUQXJARURWTXRXKXBLFXPXSAOUSXKXBRURWTCXQCGZXQPZSWTYBYAXJ
      PZYAXKPZUTZYEYAVAZJNZYCYGYDYCJAYAYAAJVBVCVDYEYGKJNZJKPJJPSYHSJJVEKJVGVFVH
      VIJVJVKJKJVLVMYEYFKJYDYFKNYCYDKAYAYAAKVBVCVNVOVPVQYAXJXKVRVSQVTAXJXBXKWAW
      BXGOPXLXGTXNBDXFWCAXEHWDWEXJXKXGJDPXJXGTWFBDXFJXJXEJAHWGWHWJKDPXKXGTWIBDX
      FKXKXEKAHWGWHWJWKXLXGOWLWMXCXLXGWNWOXDXIXHXAXCXGWPWQWRWS $.
  $}

  $( The powerset of a Dedekind-infinite set does not inject into its Cartesian
     product with itself.  (Contributed by Mario Carneiro, 31-May-2015.) $)
  pwxpndom $p |- ( _om ~<_ A -> -. ~P A ~<_ ( A X. A ) ) $=
    ( com cdom wbr cpw cxp cdju pwxpndom2 cen cvv wcel reldom brrelex2i djudoml
    wi xpexd syl2anc djucomen domentr domtr expcom syl mtod ) BACDZAEZAAFZCDZUE
    AUFGZCDZAHUDUFUHCDZUGUIOUDUFUFAGZCDZUKUHIDZUJUDUFJKZAJKZULUDAAJJBACLMZUPPZU
    PUFAJJNQUDUNUOUMUQUPUFAJJRQUFUKUHSQUGUJUIUEUFUHTUAUBUC $.

  $( The powerset of a Dedekind-infinite set does not inject into its cardinal
     sum with itself.  (Contributed by Mario Carneiro, 31-May-2015.) $)
  pwdjundom $p |- ( _om ~<_ A -> -. ~P A ~<_ ( A |_| A ) ) $=
    ( com cdom wbr cpw cdju cxp pwxpndom2 wi cvv wcel c1o cen c0 csn xpeq1i 0ex
    df1o2 domtr syl2anc reldom brrelex2i xpsnen2g eqbrtrid ensymd wss omex word
    sylancr ordom 1onn ordelss mp2an ssdomg mpan xpdom1g endomtr djudom2 expcom
    mp2 syl mtod ) BACDZAEZAAFZCDZVDAAAGZFZCDZAHVCVEVHCDZVFVIIVCAVGCDZAJKZVJVCA
    LAGZMDVMVGCDZVKVCVMAVCVMNOZAGZAMLVOARPVCNJKVLVPAMDQBACUAUBZNAJJUCUIUDUEVCVL
    LACDZVNVQLBCDZVCVRBJKLBUFZVSUGBUHLBKVTUJUKBLULUMLBJUNUTLBASUOLAAJUPTAVMVGUQ
    TVQAVGAJURTVFVJVIVDVEVHSUSVAVB $.

  $( An infinite GCH-set is idempotent under cardinal sum.  Part of Lemma 2.2
     of [KanamoriPincus] p. 419.  (Contributed by Mario Carneiro,
     31-May-2015.) $)
  gchdjuidm $p |- ( ( A e. GCH /\ -. A e. Fin ) -> ( A |_| A ) ~~ A ) $=
    ( cgch wcel cfn wn cdju cdom wbr cpw csdm cen simpl djudoml syl2anc canth2g
    wa adantr syl cvv mpdan sdomdom reldom brrelex1i djudom1 pwexd domtr pwdju1
    djudom2 c1o gchdju1 pwen entr domentr com gchinf pwdjundom ensym endom nsyl
    brsdom sylanbrc jca gchen1 ensymd ) ABCZADCEZPZAAAFZVGAVHGHZVHAIZJHZPAVHKHV
    GVIVKVGVEVEVIVEVFLZVLAABBMNVGVHVJGHZVHVJKHZEVKVGVHVJVJFZGHZVOVJKHZVMVGAVJGH
    ZVPVGAVJJHZVRVEVSVFABOQAVJUARVRVHVJAFZGHZVTVOGHZVPVRASCWAAVJGUBUCZAVJASUDTV
    RVJSCWBVRASWCUEAVJVJSUHTVHVTVOUFNRVGVOAUIFZIZKHZWEVJKHZVQVEWFVFABUGQVGWDAKH
    WGAUJWDAUKRVOWEVJULNVHVOVJUMNVGVJVHGHZVNVGUNAGHWHEAUOAUPRVNVJVHKHWHVHVJUQVJ
    VHURRUSVHVJUTVAVBAVHVCTVD $.

  $( An infinite GCH-set is idempotent under cardinal product.  Part of Lemma
     2.2 of [KanamoriPincus] p. 419.  (Contributed by Mario Carneiro,
     31-May-2015.) $)
  gchxpidm $p |- ( ( A e. GCH /\ -. A e. Fin ) -> ( A X. A ) ~~ A ) $=
    ( cgch wcel cfn wn wa cxp cdom wbr cpw csdm cen c0 cvv ensymd adantr syldan
    c1o syl2anc syl csn 0ex a1i xpsneng sylan2 df1o2 wne wceq eqeltrdi necon3bi
    id 0fi adantl 0sdomg mpbird 0sdom1dom sylib xpdom2g endomtr canth2g sdomdom
    wb eqbrtrrid xpdom1g pwexg domtr cdju simpl pwdjuen gchdjuidm pwen entr com
    domentr gchinf pwxpndom ensym endom nsyl brsdom sylanbrc jca gchen1 mpdan )
    ABCZADCZEZFZAAAGZWHAWIHIZWIAJZKIZFAWILIWHWJWLWHAAMUAZGZLIWNWIHIZWJWHWNAWGWE
    MNCZWNALIWPWGUBUCAMBNUDUEOWEWGWMAHIWOWHWMRAHUFWHMAKIZRAHIWHWQAMUGZWGWRWEWFA
    MAMUHZAMDWSUKULUIUJUMWEWQWRVBWGABUNPUOAUPUQVCWMAABURQAWNWIUSSWHWIWKHIZWIWKL
    IZEWLWHWIWKWKGZHIZXBWKLIZWTWHWIWKAGZHIZXEXBHIZXCWEWGAWKHIZXFWHAWKKIZXHWEXIW
    GABUTPAWKVATZAWKABVDQWHWKNCZXHXGWEXKWGABVEPXJAWKWKNURSWIXEXBVFSWHXBAAVGZJZL
    IXMWKLIZXDWHXMXBWEWGWEXMXBLIWEWGVHAABBVIQOWHXLALIXNAVJXLAVKTXBXMWKVLSWIXBWK
    VNSWHWKWIHIZXAWHVMAHIXOEAVOAVPTXAWKWILIXOWIWKVQWKWIVRTVSWIWKVTWAWBAWIWCWDO
    $.

  $( A relationship between dominance over the powerset and strict dominance
     when the sets involved are infinite GCH-sets.  Proposition 3.1 of
     [KanamoriPincus] p. 421.  (Contributed by Mario Carneiro, 31-May-2015.) $)
  gchpwdom $p |- ( ( _om ~<_ A /\ A e. GCH /\ B e. GCH ) ->
      ( A ~< B <-> ~P A ~<_ B ) ) $=
    ( com cdom wbr cgch wcel csdm cpw cdju cen cvv pwexd djudoml syl2anc wi syl
    ex wn 3syl w3a wa simpl2 simpl3 domen2 syl5ibrcom djucomen entr ensym endom
    syl6 wb domsdomtr 3ad2antl1 sdomnsym isfinite sylnibr gchdjuidm pwen domen1
    cfn pwdjudom canth2g sdomdomtr gchi 3expia 3ad2antl2 simpl1 domnsym pm2.21d
    biimtrid 3syld syl5 sylbird wo domentr sdomdom adantl pwdom djudom1 djudom2
    syld domtr c1o pwdju1 gchdju1 gchor syl22anc mpjaod reldom brrelex1i sylbir
    pwexb mpancom impbid1 ) CADEZAFGZBFGZUAZABHEZAIZBDEZWSWTXBWSWTUBZBXABJZKEZX
    BXDBIZKEZXCXBXEXAXDDEZXCXALGZWRXHXCAFWPWQWRWTUCMZWPWQWRWTUDZXABLFNOBXDXAUEU
    FXCXGXFBXAJZDEZXBXCXGXLXFKEZXMXCXLXDKEZXGXNPXCWRXIXOXKXJBXAFLUGOZXOXGXNXLXD
    XFUHRQXNXFXLKEXMXLXFUIXFXLUJQUKXCXMBBJZIZXLDEZXBXCXQBKEZXRXFKEXSXMULXCWRBVA
    GZSZXTXKXCBCHEZYAXCCBHEZYCSWPWQWTYDWRCABUMUNCBUOQBUPUQZBUROXQBUSXRXFXLUTTXS
    XFXADEZXCXBBXAVBXCYFBXAHEZAVAGZXBXCWRBXFHEZYFYGPXKBFVCZYIYFYGBXFXAVDRTWQWPW
    TYGYHPWRWQWTYGYHABVEVFVGYHACHEZXCXBAUPXCYKXBXCWPYKSWPWQWRWTVHCAVIQVJVKVLVMV
    NWBXCWRYBBXDDEZXDXFDEZXEXGVOXKYEXCBXLDEZXOYLXCWRXIYNXKXJBXAFLNOXPBXLXDVPOXC
    XDXFXFJZDEZYOXFKEZYMXCXDXFBJZDEZYRYODEZYPXCXAXFDEZWRYSXCABDEZUUAWTUUBWSABVQ
    VRABVSQXKXAXFBFVTOXCBXFDEZXFLGYTXCWRYIUUCXKYJBXFVQTXCBFXKMBXFXFLWAOXDYRYOWC
    OXCYOBWDJZIZKEZUUEXFKEZYQXCWRUUFXKBFWEQXCUUDBKEZUUGXCWRYBUUHXKYEBWFOUUDBUSQ
    YOUUEXFUHOXDYOXFVPOBXDWGWHWIRAXAHEZXBWTXBXIUUIXABDWJWKXIALGUUIAWMALVCWLQAXA
    BVDWNWO $.

  $( If ` ( aleph `` A ) ` is a GCH-set and its powerset is well-orderable,
     then the successor aleph ` ( aleph `` suc A ) ` is equinumerous to the
     powerset of ` ( aleph `` A ) ` .  (Contributed by Mario Carneiro,
     15-May-2015.) $)
  gchaleph $p |- ( ( A e. On /\ ( aleph ` A ) e. GCH /\
    ~P ( aleph ` A ) e. dom card ) ->
    ( aleph ` suc A ) ~~ ~P ( aleph ` A ) ) $=
    ( con0 wcel cale cfv cgch cpw ccrd cdm w3a csuc cdom wbr csdm wn wb domtri2
    com cvv syl2anc cen alephsucpw2 alephon onenon ax-mp sylancr mpbiri cfn wss
    simp3 simp1 alephgeom sylib ssdomg mpsyl domnsym syl isfinite sylnibr simp2
    fvex wi alephordilem1 3ad2ant1 gchi 3expia mtod sylancl mpbird sbth ) ABCZA
    DEZFCZVLGZHIZCZJZAKZDEZVNLMZVNVSLMZVSVNUAMVQVTVNVSNMOZAUBVQVSVOCZVPVTWBPVSB
    CWCVRUCVSUDUEZVKVMVPUJZVSVNQUFUGVQWAVSVNNMZOZVQWFVLUHCZVQVLRNMZWHVQRVLLMZWI
    OVLSCVQRVLUIZWJADVAVQVKWKVKVMVPUKAULUMRVLSUNUORVLUPUQVLURUSVQVMVLVSNMZWFWHV
    BVKVMVPUTVKVMWLVPAVCVDVMWLWFWHVLVSVEVFTVGVQVPWCWAWGPWEWDVNVSQVHVIVSVNVJT $.

  $( If ` ( aleph `` A ) ` and ` ( aleph `` suc A ) ` are GCH-sets, then the
     successor aleph ` ( aleph `` suc A ) ` is equinumerous to the powerset of
     ` ( aleph `` A ) ` .  (Contributed by Mario Carneiro, 31-May-2015.) $)
  gchaleph2 $p |- ( ( A e. On /\ ( aleph ` A ) e. GCH /\
    ( aleph ` suc A ) e. GCH ) ->
    ( aleph ` suc A ) ~~ ~P ( aleph ` A ) ) $=
    ( con0 wcel cale cfv cgch csuc cpw ccrd cdm cen wbr char cdom harcl alephon
    w3a csdm onenon com harsdom wb wss simp1 alephgeom sylib ssdomg mpsyl simp2
    mp2b wceq alephsuc simp3 eqeltrrd gchpwdom syl3anc ondomen sylancr gchaleph
    syl mpbii syld3an3 ) ABCZADEZFCZAGDEZFCZVDHZIJZCZVFVHKLVCVEVGQZVDMEZBCVHVLN
    LZVJVDOVKVDVLRLZVMVDBCZVDVICVNAPZVDSVDUAUJVKTVDNLZVEVLFCVNVMUBVOVKTVDUCZVQV
    PVKVCVRVCVEVGUDZAUEUFTVDBUGUHVCVEVGUIVKVFVLFVKVCVFVLUKVSAULUTVCVEVGUMUNVDVL
    UOUPVAVLVHUQURAUSVB $.

  ${
    $d x A $.
    $( If ` A + ~~ ~P A ` , then ` A ` is a GCH-set.  The much simpler converse
       to ~ gchhar .  (Contributed by Mario Carneiro, 2-Jun-2015.) $)
    hargch $p |- ( ( har ` A ) ~~ ~P A -> A e. GCH ) $=
      ( vx char cfv cpw cen wbr cgch wcel cfn cv csdm wa cdom ccrd con0 syl cvv
      wn wb wal wo wi cdm harcl sdomdom ondomen sylancr ax-mp cardsdom2 sylancl
      onenon ibir harcard eleqtrdi elharval simprbi cardid2 domen1 3syl domnsym
      mpbid con2i sdomen2 notbid imnan sylib alrimiv olcd relen brrelex2i pwexb
      imbitrid sylibr elgch mpbird ) ACDZAEZFGZAHIZAJIZABKZLGZWBVRLGZMSZBUAZUBZ
      VSWFWAVSWEBVSWCWDSZUCWEWCWBVQLGZSVSWHWIWCWIWBANGZWCSWIWBODZANGZWJWIWKVQIZ
      WLWIWKVQODZVQWIWKWNIZWIWBOUDZIZVQWPIZWOWITWIVQPIZWBVQNGWQAUEZWBVQUFVQWBUG
      UHZWSWRWTVQULUIWBVQUJUKUMAUNUOWMWKPIWLAWKUPUQQWIWQWKWBFGWLWJTXAWBURWKWBAU
      SUTVBWBAVAQVCVSWIWDVQVRWBVDVEVMWCWDVFVGVHVIVSARIZVTWGTVSVRRIXBVQVRFVJVKAV
      LVNBARVOQVP $.

    $( If ` ( aleph `` suc A ) ` is equinumerous to the powerset of
       ` ( aleph `` A ) ` , then ` ( aleph `` A ) ` is a GCH-set.  (Contributed
       by Mario Carneiro, 15-May-2015.) $)
    alephgch $p |- ( ( aleph ` suc A ) ~~ ~P ( aleph ` A ) ->
      ( aleph ` A ) e. GCH ) $=
      ( vx csuc cale cfv cpw cen wbr cfn wcel cv csdm wa wn wo cgch alephnbtwn2
      wal sdomen2 cvv anbi2d mtbii alrimiv olcd wb fvex elgch ax-mp sylibr ) AC
      DEZADEZFZGHZUKIJZUKBKZLHZUOULLHZMZNZBRZOZUKPJZUMUTUNUMUSBUMUPUOUJLHZMURAU
      OQUMVCUQUPUJULUOSUAUBUCUDUKTJVBVAUEADUFBUKTUGUHUI $.
  $}

  $( It is sufficient to require that all alephs are GCH-sets to ensure the
     full generalized continuum hypothesis.  (The proof uses the Axiom of
     Regularity.)  (Contributed by Mario Carneiro, 15-May-2015.) $)
  gch2 $p |- ( GCH = _V <-> ran aleph C_ GCH ) $=
    ( vx cgch cvv wceq cale wss wcel ccrd cfv com mpbi a1i cen wbr wac fnfvelrn
    con0 alephfnon sylancr sseldd crn ssv sseq2 mpbiri cun cardidm iscard3 elun
    cv wo wi cfn fingch nnfi sselid ssel jaod mpi cdm vex cpw wral csuc alephon
    wb wa simpr simpl wfn onsuc adantl gchaleph2 isnumi ralrimiva dfac12 sylibr
    syl3anc dfac10 sylib eleqtrrid cardid2 engch 3syl mpbid 2thd eqrdv impbii )
    BCDZEUAZBFZWHWJWICFWIUBBCWIUCUDWJABCWJAUIZBGZWKCGZWJWKHIZBGZWLWJWNJGZWNWIGZ
    UJZWOWNJWIUEGZWRWNHIWNDWSWKUFWNUGKWNJWIUHKWJWPWOWQWPWOUKWJWPULBWNUMWNUNUOLW
    IBWNUPUQURWJWKHUSZGWNWKMNWOWLVEWJWKCWTAUTZWJOWTCDWJWKEIZVAZWTGZAQVBOWJXDAQW
    JWKQGZVFZWKVCZEIZQGXHXCMNZXDXGVDXFXEXBBGXHBGXIWJXEVGZXFWIBXBWJXEVHZXFEQVIZX
    EXBWIGRXJQWKEPSTXFWIBXHXKXFXLXGQGZXHWIGRXEXMWJWKVJVKQXGEPSTWKVLVQXHXCVMSVNA
    VOVPVRVSVTWKWAWNWKWBWCWDWMWJXALWEWFWG $.

  $( An equivalent formulation of the generalized continuum hypothesis.
     (Contributed by Mario Carneiro, 15-May-2015.) $)
  gch3 $p |- ( GCH = _V <->
    A. x e. On ( aleph ` suc x ) ~~ ~P ( aleph ` x ) ) $=
    ( cgch cvv wceq cv csuc cale cfv cpw cen con0 wral wcel wa simpr fvex simpl
    wbr eleqtrrid sylibr gchaleph2 syl3anc ralrimiva crn wss wf alephgch ralimi
    wfn alephfnon ffnfv mpbiran frnd gch2 impbii ) BCDZAEZFZGHZUQGHZIJRZAKLZUPV
    AAKUPUQKMZNZVCUTBMZUSBMVAUPVCOVDUTCBUQGPUPVCQZSVDUSCBURGPVFSUQUAUBUCVBGUDBU
    EUPVBKBGVBVEAKLZKBGUFZVAVEAKUQUGUHVHGKUIVGUJAKBGUKULTUMUNTUO $.

  ${
    $d x A $.
    $( The equivalence of two versions of the Generalized Continuum Hypothesis.
       The right-hand side is the standard version in the literature.  The
       left-hand side is a version devised by Kannan Nambiar, which he calls
       the Axiom of Combinatorial Sets.  For the notation and motivation behind
       this axiom, see his paper, "Derivation of Continuum Hypothesis from
       Axiom of Combinatorial Sets", available at
       ~ http://www.e-atheneum.net/science/derivation&#95;ch.pdf .  The
       equivalence of the two sides provides a negative answer to Open Problem
       2 in
       ~ http://www.e-atheneum.net/science/open&#95;problem&#95;print.pdf .
       The key idea in the proof below is to equate both sides of ~ alephexp2
       to the successor aleph using ~ enen2 .  (Contributed by NM,
       1-Oct-2004.) $)
    gch-kn $p |- ( A e. On -> ( ( aleph ` suc A ) ~~
                { x | ( x C_ ( aleph ` A ) /\ x ~~ ( aleph ` A ) ) } <->
                ( aleph ` suc A ) ~~ ( 2o ^m ( aleph ` A ) ) ) ) $=
      ( con0 wcel csuc cale cfv c2o co cen wbr cv wss wa cab wb alephexp2 enen2
      cmap syl bicomd ) BCDZBEFGZHBFGZSIZJKZUCALZUDMUGUDJKNAOZJKZUBUEUHJKUFUIPA
      BQUEUHUCRTUA $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Derivation of the Axiom of Choice
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    gchaclem.1 $e |- ( ph -> _om ~<_ A ) $.
    gchaclem.3 $e |- ( ph -> ~P C e. GCH ) $.
    gchaclem.4 $e |- ( ph ->
      ( A ~<_ C /\ ( B ~<_ ~P C -> ~P A ~<_ B ) ) ) $.
    $( Lemma for ~ gchac (obsolete, used in Sierpi&#324;ski's proof).
       (Contributed by Mario Carneiro, 15-May-2015.) $)
    gchaclem $p |- ( ph ->
      ( A ~<_ ~P C /\ ( B ~<_ ~P ~P C -> ~P A ~<_ B ) ) ) $=
      ( cpw cdom wbr wi cvv wcel syl 3syl domtr syl2anc adantr com ex brrelex2i
      simpld csdm reldom canth2g sdomdom wo wa cgch cdju cen pwdjuidm gchdomtri
      simpr syl3anc pwdom simprd jaod syld jca ) ABDHZIJZCVAHIJZBHZCIJZKABDIJZD
      VAIJZVBAVFCVAIJZVEKZGUBZADLMZDVAUCJVGAVFVKVJBDIUDUANDLUEDVAUFOBDVAPQAVCVA
      CIJZVHUGZVEAVCVMAVCUHZVAUIMZVAVAUJVAUKJZVCVMAVOVCFRVNSDIJZVPAVQVCASBIJVFV
      QEVJSBDPQRDULNAVCUNVACUMUOTAVLVEVHAVFVDVAIJZVLVEKVJBDUPVRVLVEVDVACPTOAVFV
      IGUQURUSUT $.
  $}

  $( A "local" form of ~ gchac .  If ` A ` and ` ~P A ` are GCH-sets, then the
     Hartogs number of ` A ` is ` ~P A ` (so ` ~P A ` and a fortiori ` A ` are
     well-orderable).  The proof is due to Specker.  Theorem 2.1 of
     [KanamoriPincus] p. 419.  (Contributed by Mario Carneiro, 31-May-2015.) $)
  gchhar $p |- ( ( _om ~<_ A /\ A e. GCH /\ ~P A e. GCH ) ->
      ( har ` A ) ~~ ~P A ) $=
    ( com cdom wbr cgch wcel cpw cen cdju con0 djudoml sylancr csdm sylancl cvv
    wn syl2anc syl entr domentr w3a char cfv harcl cfn domnsym 3ad2ant1 sylnibr
    simp3 isfinite sylnib fvexd djuex canth2g pwdjuen pwexd cwdom simp2 harwdom
    pwfi cxp wdompwdom 3syl xpdom2g xpexd ensymd enrefg gchxpidm pwen gchdjuidm
    endomtr sdomdomtr gchen1 syl22anc djucomen harndom domen2 syl5ibrcom brsdom
    djuen mtoi sylanbrc sdomdom djudom1 djudom2 domtr gchen2 endom pwdjudom
    sbth ) BACDZAEFZAGZEFZUAZAUBUCZWMCDZWMWPCDZWPWMHDWOWPWPWMIZCDZWSWMHDWQWOWPJ
    FZWNWTAUDZWKWLWNUIZWPWMJEKLWOWMWSWOWMWMWPIZHDZXDWSHDZWMWSHDWOWNWMUEFZPZWMXD
    CDZXDWMGZMDZXEXCWOAUEFZXGWOABMDZXLWKWLXMPWNBAUFUGAUJUHZAUTUKZWOWNXAXIXCXBWM
    WPEJKNWOXDXDGZMDZXPXJCDZXKWOXDOFZXQWOWNWPOFZXSXCWOAUBULZWMWPEOUMQXDOUNRWOXP
    XJWPGZVAZHDZYCXJCDZXRWOWNXAYDXCXBWMWPEJUONWOYCXJAAVAZGZGZVAZCDZYIXJHDZYEWOX
    JOFYBYHCDZYJWOWMEXCUPWOWLWPYGUQDYLWKWLWNURZEAUSWPYGVBVCYBYHXJOVDQWOYIWMYGIZ
    GZHDYOXJHDZYKWOYOYIWOWNYGOFYOYIHDXCWOYFOWOAAEEYMYMVEUPWMYGEOUOQVFWOYNWMHDZY
    PWOYNWMWMIZHDZYRWMHDZYQWOWMWMHDZYGWMHDZYSWOWNUUAXCWMEVGRWOYFAHDZUUBWOWLXLPZ
    UUCYMXNAVHQYFAVIRWMWMYGWMVTQWOWNXHYTXCXOWMVJQZYNYRWMSQYNWMVIRYIYOXJSQYCYIXJ
    TQXPYCXJVKQXDXPXJVLQWMXDVMVNWOWNXTXFXCYAWMWPEOVOQWMXDWSSQVFWPWSWMTQZWOAAIZG
    ZAWPIZHDZUUHUUICDWRWOUUHWMHDZWMUUIHDUUJWOUUGAHDZUUKWOWLUUDUULYMXNAVJQUUGAVI
    RWOUUIWMWOWLUUDAUUIMDZUUIWMCDZUUIWMHDYMXNWOAUUICDZAUUIHDZPUUMWOWLXAUUOYMXBA
    WPEJKNWOUUPWPACDZAVPWOUUQUUPWPUUICDZWOWPWPAIZCDZUUSUUIHDZUURWOXAWLUUTXBYMWP
    AJEKLWOXAWLUVAXBYMWPAJEVOLWPUUSUUITQAUUIWPVQVRWAAUUIVSWBWOUUIYRCDZYTUUNWOUU
    IXDCDZXDYRCDZUVBWOAWMCDZXAUVCWOWLAWMMDUVEYMAEUNAWMWCVCXBAWMWPJWDNWOWQWNUVDU
    UFXCWPWMWMEWEQUUIXDYRWFQUUEUUIYRWMTQAUUIWGVNVFUUHWMUUISQUUHUUIWHAWPWIVCWPWM
    WJQ $.

  $( A "local" form of ~ gchac .  If ` A ` and ` ~P A ` are GCH-sets, then
     ` ~P A ` is well-orderable.  The proof is due to Specker.  Theorem 2.1 of
     [KanamoriPincus] p. 419.  (Contributed by Mario Carneiro, 15-May-2015.) $)
  gchacg $p |- ( ( _om ~<_ A /\ A e. GCH /\ ~P A e. GCH ) ->
      ~P A e. dom card ) $=
    ( com cdom wbr cgch wcel cpw w3a char cfv con0 cen ccrd harcl gchhar isnumi
    cdm sylancr ) BACDAEFAGZEFHAIJZKFTSLDSMQFANAOTSPR $.

  $( The Generalized Continuum Hypothesis implies the Axiom of Choice.  The
     original proof is due to Sierpi&#324;ski (1947); we use a refinement of
     Sierpi&#324;ski's result due to Specker.  (Contributed by Mario Carneiro,
     15-May-2015.) $)
  gchac $p |- ( GCH = _V -> CHOICE ) $=
    ( vx cgch cvv wceq ccrd cdm wac wcel com cun wss cpw cdom wbr vex omex unex
    cv eleqtrrid sylancl ssun2 ssdomg mp2 id pwex gchacg mp3an2i canth2 sdomdom
    csdm ax-mp numdom ssun1 ssnum a1i 2thd eqrdv dfac10 sylibr ) BCDZEFZCDGUTAV
    ACUTARZVAHZVBCHZUTVBIJZVAHZVBVEKVCUTVELZVAHZVEVGMNZVFIVEMNZUTVEBHVGBHVHVECH
    IVEKVJVBIAOZPQZIVBUAIVECUBUCUTVECBVLUTUDZSUTVGCBVEVLUEVMSVEUFUGVEVGUJNVIVEV
    LUHVEVGUIUKVGVEULTVBIUMVEVBUNTVDUTVKUOUPUQURUS $.

