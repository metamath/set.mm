$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Ender Ting
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Interesting facts
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Less-than class is never reflexive.  (Contributed by Ender Ting,
       22-Nov-2024.)  Prefer to specify theorem domain and then apply ~ ltnri .
       (New usage is discouraged.) $)
    et-ltneverrefl $p |- -. A < A $=
      ( cxr wcel clt wbr wn xrltnr cop opelxp1 con3i ltrelxr sseli nsyl sylnibr
      cxp df-br pm2.61i ) ABCZAADEZFAGRFZAAHZDCZSTUABBOZCZUBUDRAABBIJDUCUAKLMAA
      DPNQ $.
  $}

  ${
    $( Alternative proof that equality is left-Euclidean, using ~ ax7 directly
       instead of utility theorems; done for practice.  (Contributed by Ender
       Ting, 21-Dec-2024.) $)
    et-equeucl $p |- ( x = z -> ( y = z -> x = y ) ) $=
      ( weq wi equid ax7 com12 ax-mp syl ) ACDZCADZBCDZABDZEAADZKLEAFKOLACAGHIM
      LNMCBDZLNEBBDZMPEBFMQPBCBGHILPNCABGHJHJ $.
  $}

  ${
    $( The square root of a negative number is not a real number.  (Contributed
       by Ender Ting, 5-Jan-2025.) $)
    et-sqrtnegnre $p |- ( ( A e. RR /\ A < 0 ) -> -. ( sqrt ` A ) e. RR ) $=
      ( cr wcel cc0 clt wbr wa cle wi csqrt cfv simpr 0red ltnled biimpd impcom
      wn id jcnd ancoms c2 cexp co wceq recn sqsqrtd sqge0 breq2 syl2imc nsyl )
      ABCZADEFZGUKDAHFZIZAJKZBCZULUKUNQULUKGUKUMULUKLUKULUMQZUKULUQUKADUKRUKMNO
      PSTUKUOUAUBUCZAUDZUPDURHFZUMUKAAUEUFUOUGUSUTUMURADHUHOUIUJ $.
  $}

  ${
    quantgodel.s $e |- ( ph <-> -. A. x ph ) $.
    $( There can be no formula asserting its own non-universality, in parallel
       to ~ bj-babygodel ; proof path is shorter but relying on a property of
       specialization which provability predicates do not have.  For a matching
       proof, see ~ quantgodelALT .  (Contributed by Ender Ting,
       9-May-2026.) $)
    quantgodel $p |- F. $=
      ( wal wfal wn sp sylib pm2.01i mpbir ax-gen pm2.24ii ) ABDZEABAMFZMMANABG
      CHIZCJKOL $.
    $( $j usage 'quantgodel' avoids 'ax-10'; $)

    $( There can be no formula asserting its own non-universality; follows the
       steps of ~ bj-babygodel .  (Contributed by Ender Ting, 7-May-2026.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    quantgodelALT $p |- F. $=
      ( wal wfal alfal falim sps mt2 biimpi alimi hba1 pm2.21 al2imi sylc con3i
      wn sylibr ax-mp ax-gen pm2.24ii ) ABDZEABEBDZQZAUCEQBDZBFEUEQZBUFGHIUDUBQ
      ZAUBUCUBUGBDUBBDUCAUGBAUGCJZKABLUGUBEBUBEMNOPCRSZTAUGUIUHSUA $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Increasing sequences and subsequences
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d B t $.  $d R t $.  $d T t $.  $d k ph t $.
    ormklocald.1 $e |- ( ph -> R Or S ) $.
    ormklocald.2 $e |- ( ph -> A. k e. ( 0 ..^ ( T + 1 ) ) ( B ` k ) e. S ) $.
    ormklocald.3 $e |- ( ph -> A. k e. ( 0 ..^ T ) A. t e. ( 1 ..^ ( T + 1 ) )
                       ( k < t -> ( B ` k ) R ( B ` t ) ) ) $.
    $( If elements of a certain sequence are ordered with respect to a certain
       relation, then its consecutive elements satisfy that relation (so-called
       "local monotonicity").  (Contributed by Ender Ting, 30-Apr-2025.) $)
    ormklocald $p  |- ( ph -> A. k e. ( 0 ..^ T ) ( B ` k ) R ( B ` ( k + 1 ) )
                      ) $=
      ( cfv c1 caddc co wbr cc0 cfzo wcel clt wi cv wa wex wceq isseti elfzoelz
      ovex zred ltp1d breq2 syl5ibrcom adantl cz 1z fzoaddel mpan2 0p1e1 oveq1i
      eleqtrdi eleq1 wral r19.21bi ex syld mpdd fveq2 breq2d mpbidi eximdv ax5e
      mpi syl ralrimiva ) AGUAZCKZVNLMNZCKZDOZGPFQNZAVNVSRZUBZVRBUCZVRWABUAZVPU
      DZBUCWBBVPVNLMUGUEWAWDVRBWDVOWCCKZDOZVRWAWAWDVNWCSOZWFVTWDWGTAVTWGWDVNVPS
      OVTVNVTVNVNPFUFUHUIWCVPVNSUJUKULWAWDWCLFLMNZQNZRZWGWFTZVTWDWJTAVTWJWDVPWI
      RVTVPPLMNZWHQNZWIVTLUMRVPWMRUNVNPFLUOUPWLLWHQUQURUSWCVPWIUTUKULWAWJWKWAWK
      BWIAWKBWIVAGVSJVBVBVCVDVEWDWEVQVODWCVPCVFVGVHVIVKVRBVJVLVM $.
  $}

  ${
    $d B a b k $.  $d R a b k $.  $d S k $.  $d T a b k $.  $d T a k t $.
    $d a b k ph $.  $d ph t $.
    ormkglobd.1 $e |- ( ph -> R Or S ) $.
    ormkglobd.2 $e |- ( ph -> A. k e. ( 0 ..^ ( T + 1 ) ) ( B ` k ) e. S ) $.
    ormkglobd.3 $e |- ( ph -> A. k e. ( 0 ..^ T ) ( B ` k ) R ( B ` ( k + 1 ) )
                      ) $.
    $( If all adjacent elements of a certain sequence are ordered according to
       a relation which is a total order on S, then any element is so related
       to anything to right of it (so-called "global monotonicity").  Deduction
       form.  (Contributed by Ender Ting, 30-Apr-2025.) $)
    ormkglobd $p |- ( ph -> A. k e. ( 0 ..^ T ) A. t e. ( 1 ..^ ( T + 1 ) ) ( k
                    < t -> ( B ` k ) R ( B ` t ) ) ) $=
      ( vb wbr wi cc0 co c1 wcel wa cle adantl va cv clt cfv cfzo caddc w3a 2a1
      cz imp jcad elfzoelz adantr zltp1led biimpd zred elfzoel2 1red elfzop1le2
      a1d cr 3jca leadd1 biimprd sylc 3jcad ex fveq2 breq2d weq r19.21bi simp1l
      wceq wor syl cfz elfzofz fzval3 eleqtrd sylan2 3ad2ant1 cn0 simp21 simp1r
      0red readdcld elfzole1 0le1 addge0d simp22 letrd elnn0z sylanbrc peano2zd
      simp23 ltp1d lttrd elfzo0z syl3anbrc eleq1w anbi2d imbitrid sylbird ax6ev
      eleq1d exlimiiv syl2anc 1nn0 nn0addcld ltadd1dd ovex eleq1 vtocle fvoveq1
      a1i simp3 breq12d imbitrrid sylbid ax6evr sotrd fzindd syl8 ralrimivv ) A
      GUBZBUBZUCLZYECUDZYFCUDZDLZMGBNFUEOZPFPUFOZUEOZAYEYKQZYFYMQZRZYGAYNRZYFUI
      QZYEPUFOZYFSLZYFFSLZUGZRZYJAYPYGUUCMAYPRZYGYQUUBUUDYGAYNAYPYGAMAYPYGUHUJY
      PYGYNMZAYNYOUUEYNYOYGUHUJTUKYPYGUUBMAYPYGYRYTUUAYPYRYGYOYRYNYFPYLULTZUTYP
      YGYTYPYEYFYNYEUIQZYOYENFULZUMUUFUNUOYPUUAYGYPYFVAQZFVAQZPVAQZUGZYFPUFOYLS
      LZUUAYPUUIUUJUUKYPYFUUFUPYPFYNFUIQZYOYENFUQZUMUPYPURVBYOUUMYNYFPYLUSTUULU
      UAUUMYFFPVCVDVEUTVFTUKVGYQYHUAUBZCUDZDLYHYSCUDZDLZYHKUBZCUDZDLZYHUUTPUFOZ
      CUDZDLYJUAKYFYSFUUPYSVMUUQUURYHDUUPYSCVHVIUAKVJUUQUVAYHDUUPUUTCVHVIUUPUVC
      VMUUQUVDYHDUUPUVCCVHVIUABVJUUQYIYHDUUPYFCVHVIAUUSGYKJVKZYQUUTUIQZYSUUTSLZ
      UUTFUCLZUGZUVBUGZEDYHUVAUVDUVJAEDVNAYNUVIUVBVLZHVOYQUVIYHEQZUVBYNAYENYLUE
      OZQZUVLYNYENFVPOZUVMYENFVQYNUUNUVOUVMVMUUONFVRVOVSAUVLGUVMIVKZVTWAUVJAUUT
      UVMQZUVAEQZUVKUVJUUTWBQZYLUIQZUUTYLUCLUVQUVJUVFNUUTSLUVSYQUVFUVGUVHUVBWCZ
      UVJNYSUUTUVJWEUVJYEPUVJYEUVJYNUUGAYNUVIUVBWDZUUHVOUPZUVJURZWFUVJUUTUWAUPZ
      UVJYEPUWCUWDUVJYNNYESLUWBYENFWGVONPSLUVJWHXOWIYQUVFUVGUVHUVBWJWKUUTWLWMZU
      VJFUVJYNUUNUWBUUOVOZWNZUVJUUTFYLUWEUVJFUWGUPZUVJFPUWIUWDWFYQUVFUVGUVHUVBW
      OZUVJFUWIWPWQUUTYLWRWSGKVJZAUVQRZUVRMGUWKUWLAUVNRZUVRUWKUVNUVQAGKUVMWTXAU
      WMUVLUWKUVRUVPUWKYHUVAEYEUUTCVHXEXBXCGKXDXFXGUVJAUVCUVMQZUVDEQZUVKUVJUVCW
      BQUVTUVCYLUCLUWNUVJUUTPUWFPWBQUVJXHXOXIUWHUVJUUTFPUWEUWIUWDUWJXJUVCYLWRWS
      AUWNRZUWOMGUVCUUTPUFXKYEUVCVMZUWPUWMUWOUWQUVNUWNAYEUVCUVMXLXAUWMUVLUWQUWO
      UVPUWQYHUVDEYEUVCCVHXEXBXCXMXGYQUVIUVBXPUVJAUUTYKQZUVAUVDDLZUVKUVJUVSUUNU
      VHUWRUWFUWGUWJUUTFWRWSKGVJZAUWRRZUWSMGUWTUXAYQUWSUWTUWRYNAKGYKWTXAYQUWSUW
      TUUSUVEUWTUVAYHUVDUURDUUTYECVHUUTYEPCUFXNXQXRXSGKXTXFXGYAYQYEYNUUGAUUHTWN
      YNUUNAUUOTYNYSFSLAYENFUSTYBYCYD $.
  $}

  ${
    $d A x $.  $d W x $.  $d I x $.  $d .< x $.  $d ph x $.
    chnsubseq.1 $e |- ( ph -> W e. ( .< Chain A ) ) $.
    chnsubseq.2 $e |- ( ph -> I e. ( < Chain ( 0 ..^ ( # ` W ) ) ) ) $.
    $( A subsequence of a chain is a word.  (Contributed by Ender Ting,
       22-Jan-2026.) $)
    chnsubseqword $p |- ( ph -> ( W o. I ) e. Word A ) $=
      ( vx cc0 cfzo co wf cn0 cword wcel chash cfv adantr chnwrd syl cv ccom wa
      wrex wceq cchn wrdf clt fcod simpr oveq2d feq2d mpbird lencl iswrd sylibr
      rspcime ) AIHUAZJKZBEDUBZLZHMUDUTBNZOAVAHDPQZMAURVCUEZUCZVAIVCJKZBUTLVEVF
      IEPQJKZBEDVEEVBOVGBELVEBECAEBCUFOVDFRSBEUGTVEDVGNOZVFVGDLAVHVDAVGDUHGSZRV
      GDUGTUIVEUSVFBUTVEURVCIJAVDUJUKULUMAVHVCMOVIVGDUNTUQBUTHUOUP $.

    $( A subsequence of a chain has the same length as its indexing sequence.
       (Contributed by Ender Ting, 22-Jan-2026.) $)
    chnsubseqwl $p |- ( ph -> ( # ` ( W o. I ) ) = ( # ` I ) ) $=
      ( cc0 chash cfv cfzo co wceq cdm wcel syl wrddm wbr wb c0 ccom crn wss wf
      cword clt chnwrd wrdf frnd sseqtrrd dmcosseq chnsubseqword 3eqtr3d wa cn0
      cz 0z lencl nn0zd fzoopth mp3an2ani eqid biantrur bitr4di cle oveq2d fzo0
      simpr eqtr3di eqeq1d eqcom bitrdi 0zd adantr fzon syl2anc nn0le0eq0 sylan
      biimpa adantlr id 0le0 eqbrtrdi adantl impbida a1i 3bitrd 3bitr2d nn0ge0d
      wo 0red nn0red leloed mpbid mpjaodan ) AHEDUAZIJZKLZHDIJZKLZMZWQWSMZAWPNZ
      DNZWRWTADUBZENZUCXCXDMAXEHEIJKLZXFAWTXGDADXGUEOZWTXGDUDAXGDUFGUGZXGDUHPUI
      AEBUEZOXFXGMABECFUGBEQPUJEDUKPAWPXJOZXCWRMABCDEFGULZBWPQPAXHXDWTMXIXGDQPU
      MAHWQUFRZXAXBSHWQMZAXMUNXAHHMZXBUNZXBHUPOZAWQUPOXMXMXAXPSUQAWQAXKWQUOOXLB
      WPURPZUSAXMVHHWSHWQUTVAXOXBHVBVCVDAXNUNZXAWTTMZWSHVERZXBXSXATWTMXTXSWRTWT
      XSHHKLWRTXSHWQHKAXNVHZVFHVGVIVJTWTVKVLXSXQWSUPOZYAXTSXSVMAYCXNAWSAXHWSUOO
      ZXIXGDURPZUSVNHWSVOVPXSYAWSHMZHWSMZXBXSYAYFAYAYFXNAYDYAYFYEYDYAYFWSVQVSVR
      VTYFYAXSYFWSHHVEYFWAWBWCWDWEYFYGSXSWSHVKWFXSHWQWSYBVJWGWHAHWQVERXMXNWJAWQ
      XRWIAHWQAWKAWQXRWLWMWNWOWN $.

    chnsubseq.3 $e |- ( ph -> .< Po A ) $.
    $( An order-preserving subsequence of an ordered chain is itself a chain.
       (Contributed by Ender Ting, 22-Jan-2026.) $)
    chnsubseq $p |- ( ph -> ( W o. I ) e. ( .< Chain A ) ) $=
      ( vx wcel co cfv wbr cc0 adantr chash cfzo clt syl cz ccom cword cmin cdm
      cv c1 csn cdif wral cchn chnsubseqword wa wpo wf chnwrd wrdf eldifi wrddm
      wceq chnsubseqwl oveq2d eqtrd eleq2d biimpa sylan2 ffvelcdmd cn0 elfzonn0
      cle cn simpr eldifsnbd elnnne0 sylanbrc nnm1ge0 cr nn0red peano2rem lencl
      wne ltm1d adantl eleqtrd elfzolt2 breqtrd lttrd wb elfzoelz peano2zm 3syl
      0zd nn0zd elfzo syl3anc mpbir2and 3eqtr4d difeq1d chnltm1 syl3anbrc chnlt
      elfzo0z fvco3d 3brtr4d ralrimiva ischn ) AEDUAZBUBJZIUEZUFUCKZXFLZXHXFLZC
      MZIXFUDZNUGZUHZUIXFBCUJZJABCDEFGUKZAXLIXOAXHXOJZULZXIDLZELXHDLZELXJXKCXSB
      ECXTYAABCUMXRHOAEXPJXRFOXSNDPLZQKZNEPLZQKZXHDXSDYEUBJZYCYEDUNAYFXRAYEDRGU
      OZOYEDUPSZXRAXHXMJZXHYCJZXHXMXNUQZAYIYJAXMYCXHAXMNXFPLZQKZYCAXGXMYMUSZXQB
      XFURSZAYLYBNQABCDEFGUTZVAZVBVCVDVEZVFZXSXTVGJZYATJZXTYARMXTNYAQKJXSXTYEJY
      TXSYCYEXIDYHXSXIYCJZNXIVIMZXIYBRMZXSXHVJJZUUCXSXHVGJZXHNVTUUEXSYJUUFYRXHY
      BVHSZXSXHXMNAXRVKVLXHVMVNXHVOSXSXIXHYBXSXHVPJXIVPJXSXHUUGVQZXHVRSUUHXSYBA
      YBVGJZXRAYFUUIYGYEDVSSZOVQXSXHUUHWAXSXHYLYBRXSXHYMJXHYLRMXSXHXMYMXRYIAYKW
      BAYNXRYOOWCXHNYLWDSAYLYBUSXRYPOWEWFXSXITJZNTJYBTJZUUBUUCUUDULWGXSYJXHTJUU
      KYRXHNYBWHXHWIWJXSWKAUULXRAYBUUJWLOXINYBWMWNWOZVFXTYDVHSXSYAYEJUUAYSYANYD
      WHSXSYEDRXHADYERUJJXRGOAXRXHDUDZXNUHZJAXOUUOXHAXMUUNXNAYMYCXMUUNYQYOAYFUU
      NYCUSYGYEDURSWPWQVCVDWRXTYAXAWSWTXSYCYEXIEDYHUUMXBXSYCYEXHEDYHYRXBXCXDBXF
      CIXEVN $.

    $( Length of a subsequence is bounded by the length of original chain.
       (Contributed by Ender Ting, 30-Jan-2026.) $)
    chnsuslle $p |- ( ph -> ( # ` ( W o. I ) ) <_ ( # ` W ) ) $=
      ( chash cfv cc0 cfzo co ccom cle clt cr wpo syl wcel cvv wor ltso sopo wi
      mp1i wss fzossz zssre sstri a1i poss mpd ovexd chnpolleha chnsubseqwl cn0
      cz wceq cword chnwrd lencl hashfzo0 eqcomd 3brtr4d ) ADIJKEIJZLMZIJZEDNIJ
      VFOAVGDPUAAQPRZVGPRZQPUBVIAUCQPUDUFAVGQUGZVIVJUEVKAVGURQKVFUHUIUJUKVGQPUL
      SUMGAKVFLUNUOABCDEFGUPAVHVFAVFUQTZVHVFUSAEBUTTVLABECFVABEVBSVFVCSVDVE $.
  $}

  ${
    $d J c d i j x $.  $d I c d i j x $.  $d .~ c d i j x $.  $d A c d i j x $.
    $d C c d i j x $.  $d ph c d i j x $.
    chner.1 $e |- ( ph -> .~ Er A ) $.
    chner.2 $e |- ( ph -> C e. ( .~ Chain A ) ) $.
    chner.3 $e |- ( ph -> J e. ( 0 ..^ ( # ` C ) ) ) $.
    $( In a chain constructed on an equivalence relation, the last element is
       equivalent to any.  This theorem is a translation of ~ chnub to
       equivalence relations.  (Contributed by Ender Ting, 29-Jan-2026.) $)
    chnerlem1 $p |- ( ph -> ( C ` J ) .~ ( lastS ` C ) ) $=
      ( vi cfv wbr cc0 chash cfzo co wceq fveq2 c0 wcel wa vc vd vj clsw breq1d
      vx cv wral cs1 cconcat oveq2d fveq1 breq12d raleqbidv weq cbvralvw bitrid
      wne wn cn hash0 0nnn eqneltri fzo0n0 mtbir nne mpbi rzal mp1i cchn wo wer
      ad6antr simp-5r erref cword simp-6r chnwrd c1 csn simplr caddc ccatws1len
      syl eqtr2di eqcomd adantl oveq1d 0p1e1 eqtrd eleqtrd fzo01 eleqtrdi elsnd
      eqtrdi syl3anc lswccats1 syl2anc 3brtr4d adantr simpr simp-4r neneq orcnd
      ccats1val2 ersym eqbrtrd ccats1val1 ralbidva mpbid ad2antrr cuz cn0 lencl
      wb simp-7r elnn0uz biimpi 3syl fzosplitsni df-ne olcnd rspcdva pm2.61dane
      bilani ertrd breqtrrd ralrimiva chnind ) AIUGZCJZCUDJZDKZECJZYLDKILCMJZNO
      ZEYJEPYKYNYLDYJECQUEAYJUAUGZJZYQUDJZDKZILYQMJZNOZUHZYJRJZRUDJZDKZILRMJZNO
      ZUHZYJUBUGZJZUUJUDJZDKZILUUJMJZNOZUHZUCUGZUUJUFUGZUIUJOZJZUUSUDJZDKZUCLUU
      SMJZNOZUHZYMIYPUHUFBCDUAUBYQRPZYTUUFIUUBUUHUVFUUAUUGLNYQRMQUKUVFYRUUDYSUU
      EDYJYQRULYQRUDQUMUNUAUBUOZYTUUMIUUBUUOUVGUUAUUNLNYQUUJMQUKUVGYRUUKYSUULDY
      JYQUUJULYQUUJUDQUMUNUUCUUQYQJZYSDKZUCUUBUHYQUUSPZUVEYTUVIIUCUUBIUCUOZYRUV
      HYSDYJUUQYQQUEUPUVJUVIUVBUCUUBUVDUVJUUAUVCLNYQUUSMQUKUVJUVHUUTYSUVADUUQYQ
      UUSULYQUUSUDQUMUNUQYQCPZYTYMIUUBYPUVLUUAYOLNYQCMQUKUVLYRYKYSYLDYJYQCULYQC
      UDQUMUNGUUHRPZUUIAUUHRURZUSUVMUVNUUGUTSUUGLUTVAVBVCUUGVDVEUUHRVFVGUUFIUUH
      VHVIAUUJBDVJSZTZUURBSZTZUUJRPZUULUURDKZVKZTZUUPTZUVBUCUVDUWCUUQUVDSZTZUVB
      UUJRUWEUVSTZUURUURUUTUVADUWFUURDBABDVLZUVOUVQUWAUUPUWDUVSFVMUVPUVQUWAUUPU
      WDUVSVNZVOUWFUUJBVPSZUVQUUQUUNPZUUTUURPZUWFBUUJDAUVOUVQUWAUUPUWDUVSVQVRZU
      WHUWFUUQLUUNUWFUUQLUWFUUQLVSNOZLVTUWFUUQUVDUWMUWCUWDUVSWAUWFUVCVSLNUWFUVC
      UUNVSWBOZVSUWFUWIUVCUWNPZUWLBUUJUURWCZWDUWFUWNLVSWBOVSUWFUUNLVSWBUVSUUNLP
      UWEUVSLUUNUVSUUNUUGLUUJRMQVAWEZWFWGWHWIWOWJUKWKWLWMWNUVSLUUNPUWEUWQWGWJUU
      RUUQBUUJXEZWPUWFUWIUVQUVAUURPZUWLUWHUURBUUJWQZWRWSUWEUUJRURZTZUUTUURUVADU
      XBUUTUULUURDBAUWGUVOUVQUWAUUPUWDUXAFVMZUXBUUTUULDKZUUQUUNUXBUWJTZUUTUURUU
      LDUXEUWIUVQUWJUWKUXBUWIUWJUXBBUUJDAUVOUVQUWAUUPUWDUXAVQVRZWTUVPUVQUWAUUPU
      WDUXAUWJVQUXBUWJXAUWRWPUXBUURUULDKUWJUXBUULUURDBUXCUXBUVSUVTUVRUWAUUPUWDU
      XAXBUXAUVSUSUWEUUJRXCWGXDZXFWTXGUXBUUQUUNURZTZYJUUSJZUULDKZUXDIUUOUUQUVKU
      XJUUTUULDYJUUQUUSQUEUXIUUPUXKIUUOUHZUWBUUPUWDUXAUXHXBUVPUUPUXLXOUVQUWAUUP
      UWDUXAUXHUVPUUMUXKIUUOUVPYJUUOSZTZUUKUXJUULDUXNUXJUUKUXNUWIUXMUXJUUKPUXNB
      UUJDAUVOUXMWAVRUVPUXMXAUURYJBUUJXHWRWFUEXIVMXJUXIUUQUUOSZUWJUXIUUQLUWNNOZ
      SZUXOUWJVKZUWEUXQUXAUXHUWEUUQUVDUXPUWCUWDXAUWEUVCUWNLNUWEUWIUWOUWEBUUJDAU
      VOUVQUWAUUPUWDVNVRUWPWDUKWKXKUXIUUNLXLJSZUXQUXRXOUXIUWIUUNXMSZUXSUXIBUUJD
      AUVOUVQUWAUUPUWDUXAUXHXPVRBUUJXNUXTUXSUUNXQXRXSLUUNUUQXTWDXJUXHUWJUSUXBUU
      QUUNYAYEYBYCYDUXGYFUXBUWIUVQUWSUXFUVPUVQUWAUUPUWDUXAVNUWTWRYGYDYHYIHYC $.

    $( Lemma for ~ chner where the I-th element comes before the J-th.
       (Contributed by Ender Ting, 29-Jan-2026.) $)
    chnerlem2 $p |- ( ( ph /\ I e. ( 0 ..^ J ) ) -> ( C ` I ) .~ ( C ` J ) ) $=
      ( cc0 cfzo co wcel wa c1 cfv adantr syl wceq syl2anc caddc cpfx clsw cchn
      wer chash cfz fzofzp1 pfxchn wo animorrl cuz wb cn0 elfzonn0 elnn0uz 3syl
      biimpi fzosplitsni mpbird simpr cword chnwrd pfxlen oveq2d eleqtrrd pfxfv
      syldan chnerlem1 syl3anc cmin fz0add1fz1 pfxfvlsw cz elfzoel2 adantl zcnd
      lencl 1cnd pncand fveq2d eqtrd 3brtr3d ) AEJFKLMZNZECFOUALZUBLZPZWGUCPZEC
      PZFCPZDWEBWGDEABDUEWDGQWEBCDWFACBDUDMWDHQWEFJCUFPZKLMZWFJWLUGLMZAWMWDIQJW
      LFUHZRZUIAWDEJWFKLZMZEJWGUFPZKLZMWEWRWDEFSZUJZAWDXAUKWEFJULPMZWRXBUMAXCWD
      AWMFUNMZXCIFWLUOXDXCFUPURUQQJFEUSRUTZAWRNZEWQWTAWRVAXFWSWFJKXFCBVBMZWNWSW
      FSAXGWRABCDHVCZQAWNWRAWMWNIWORQBCWFVDTVEVFVHVIWEXGWNWRWHWJSAXGWDXHQZWPXEE
      WFBCVGVJWEWIWFOVKLZCPZWKWEXGWFOWLUGLMZWIXKSXIAXLWDAWLUNMZWMXLAXGXMXHBCVRR
      IWLFVLTQWFBCVMTWEXJFCWEFOWEFWDFVNMAEJFVOVPVQWEVSVTWAWBWC $.

    chner.4 $e |- ( ph -> I e. ( 0 ..^ ( # ` C ) ) ) $.
    $( Lemma for ~ chner - trichotomy of integers within the word's domain.
       (Contributed by Ender Ting, 29-Jan-2026.) $)
    chnerlem3 $p |- ( ph -> ( I e. ( 0 ..^ J ) \/ J e. ( 0 ..^ I ) \/ I = J ) )
      $=
      ( clt wbr w3o cc0 cfzo co wcel cr syl adantr wceq chash cfv elfzoelz zred
      cz lttri4 syl2anc 3orcomb sylib wa cn0 elfzonn0 simpr 3jca elfzo0z sylibr
      w3a ex idd 3orim123d mpd ) AEFKLZFEKLZEFUAZMZENFOPQZFNEOPQZVEMAVCVEVDMZVF
      AERQFRQVIAEAENCUBUCZOPZQZEUFQZJENVJUDSZUEAFAFVKQZFUFQZIFNVJUDSZUEEFUGUHVC
      VEVDUIUJAVCVGVDVHVEVEAVCVGAVCUKZEULQZVPVCURVGVRVSVPVCAVSVCAVLVSJEVJUMSTAV
      PVCVQTAVCUNUOEFUPUQUSAVDVHAVDUKZFULQZVMVDURVHVTWAVMVDAWAVDAVOWAIFVJUMSTAV
      MVDVNTAVDUNUOFEUPUQUSAVEUTVAVB $.

    $( Any two elements are equivalent in a chain constructed on an equivalence
       relation.  (Contributed by Ender Ting, 29-Jan-2026.) $)
    chner $p |- ( ph -> ( C ` I ) .~ ( C ` J ) ) $=
      ( cc0 cfzo co wcel cfv wbr wceq chnerlem2 wa adantr wer ersym fveq2 cword
      adantl chash chnwrd wrdsymbcl syl2anc erref eqbrtrd chnerlem3 mpjao3dan )
      AEKFLMNECOZFCOZDPFKELMNZEFQZABCDEFGHIRAUPSUOUNDBABDUAZUPGTABCDFEGHJRUBAUQ
      SZUNUOUODUQUNUOQAEFCUCUEUSUODBAURUQGTAUOBNZUQACBUDNFKCUFOLMNUTABCDHUGIFBC
      UHUITUJUKABCDEFGHIJULUM $.
  $}

  ${
    $d n A $.  $d n B $.  $d n C $.  $d n .< $.  $d n R $.
    $( A word in two alphabets is also a word under their intersection.
       (Contributed by Ender Ting, 24-Jul-2026.) $)
    wrddin $p |- ( ( A e. Word B /\ A e. Word C ) -> A e. Word ( B i^i C ) ) $=
      ( cword wcel wa cc0 chash cfv cfzo co cin wrdf anim12i fin sylibr iswrdb
      wf ) ABDEZACDEZFZGAHIJKZBCLZARZAUCDEUAUBBARZUBCARZFUDSUETUFBAMCAMNUBBCAOP
      UCAQP $.

    $( A word whose alphabet is intersection of two classes is also a word in
       each of those alphabets.  (Contributed by Ender Ting, 24-Jul-2026.) $)
    wrddrin $p |- ( A e. Word ( B i^i C ) -> ( A e. Word B /\ A e. Word C ) )
      $=
      ( cin cword wcel wss inss1 sswrd ax-mp sseli inss2 jca ) ABCDZEZFABEZFACE
      ZFOPANBGOPGBCHNBIJKOQANCGOQGBCLNCIJKM $.

    $( Distribution of word class constructor over class intersection.
       (Contributed by Ender Ting, 24-Jul-2026.) $)
    wrddin2 $p |- Word ( B i^i C ) = ( Word B i^i Word C ) $=
      ( vn cin cword cv wcel wa wrddrin wrddin impbii elin bitr4i eqriv ) CABDE
      ZAEZBEZDZCFZOGZSPGSQGHZSRGTUASABISABJKSPQLMN $.

    $( Words in either of two alphabets are words in their union.  (Contributed
       by Ender Ting, 24-Jul-2026.) $)
    wrddun $p |- ( ( A e. Word B \/ A e. Word C ) -> A e. Word ( B u. C ) ) $=
      ( cword wcel cun wss ssun1 sswrd ax-mp sseli ssun2 jaoi ) ABDZEABCFZDZEAC
      DZENPABOGNPGBCHBOIJKQPACOGQPGCBLCOIJKM $.

    $( Superadditivity of word constructor.  Class of words over union alphabet
       includes all words over either alphabet in the union; if ` B ` and ` C `
       are non-empty and different, then this subclass relation is strict
       because of the words which have symbols both from ` B ` and from ` C ` .
       (Contributed by Ender Ting, 24-Jul-2026.) $)
    wrddun2 $p |- ( Word B u. Word C ) C_ Word ( B u. C ) $=
      ( vn cword cun cv wcel wo elun wrddun sylbi ssriv ) CADZBDZEZABEDZCFZOGQM
      GQNGHQPGQMNIQABJKL $.

    $( A chain in two alphabets at once is also a chain in their intersection.
       (Contributed by Ender Ting, 24-Jul-2026.) $)
    chndin $p |- ( ( A e. ( R Chain B ) /\ A e. ( R Chain C ) ) -> A e.
      ( R Chain ( B i^i C ) ) ) $=
      ( vn cchn wcel wa cin cword cv c1 cmin co cfv wbr cdm id chnwrd ischn cc0
      csn cdif wral wrddin syl2an simprbi adantr sylanbrc ) ABDFGZACDFGZHABCIZJ
      GZEKZLMNAOUNAODPEAQUAUBUCUDZAULDFGUJABJGZACJGUMUKUJBADUJRSUKCADUKRSABCUEU
      FUJUOUKUJUPUOBADETUGUHULADETUI $.

    $( A chain whose alphabet is intersection of two classes is also a chain in
       each of those alphabets.  (Contributed by Ender Ting, 24-Jul-2026.) $)
    chndrin $p |- ( A e. ( R Chain ( B i^i C ) ) -> ( A e. ( R Chain B ) /\
      A e. ( R Chain C ) ) ) $=
      ( cin cchn wcel wss inss1 chndss ax-mp sseli inss2 jca ) ABCEZDFZGABDFZGA
      CDFZGPQAOBHPQHBCIOBDJKLPRAOCHPRHBCMOCDJKLN $.

    $( Distribution of chain class constructor over alphabet intersection.
       (Contributed by Ender Ting, 24-Jul-2026.) $)
    chndin2 $p |- ( R Chain ( B i^i C ) ) = (
      ( R Chain B ) i^i ( R Chain C ) ) $=
      ( vn cin cchn cv wcel wa chndrin chndin impbii elin bitr4i eqriv ) DABECF
      ZACFZBCFZEZDGZPHZTQHTRHIZTSHUAUBTABCJTABCKLTQRMNO $.

    $( Chains in either of two alphabets are chains in their union.
       (Contributed by Ender Ting, 24-Jul-2026.) $)
    chndun $p |- ( ( A e. ( R Chain B ) \/ A e. ( R Chain C ) ) -> A e.
      ( R Chain ( B u. C ) ) ) $=
      ( cchn wcel cun wss ssun1 chndss ax-mp sseli ssun2 jaoi ) ABDEZFABCGZDEZF
      ACDEZFOQABPHOQHBCIBPDJKLRQACPHRQHCBMCPDJKLN $.

    $( Superaddivity of chain constructor over alphabet parameter.
       (Contributed by Ender Ting, 24-Jul-2026.) $)
    chndun2 $p |- ( ( R Chain B ) u. ( R Chain C ) ) C_
      ( R Chain ( B u. C ) ) $=
      ( vn cchn cun cv wcel wo elun chndun sylbi ssriv ) DACEZBCEZFZABFCEZDGZPH
      RNHROHIRQHRNOJRABCKLM $.

    $( Satisfying two chain relations makes a chain under their intersection.
       (Contributed by Ender Ting, 24-Jul-2026.) $)
    chnrin $p |- ( ( A e. ( R Chain B ) /\ A e. ( .< Chain B ) ) -> A e.
      ( ( R i^i .< ) Chain B ) ) $=
      ( vn cchn wcel wa cword cv c1 cmin cfv wral ischn adantr simprbi r19.21bi
      wbr sylanbrc co cin cdm cc0 csn cdif simplbi adantl brin ralrimiva ) ABCF
      GZABDFGZHZABIGZEJZKLUAAMZUOAMZCDUBZSZEAUCUDUEUFZNABURFGUKUNULUKUNUPUQCSZE
      UTNZBACEOZUGPUMUSEUTUMUOUTGHVAUPUQDSZUSUMVAEUTUKVBULUKUNVBVCQPRUMVDEUTULV
      DEUTNZUKULUNVEBADEOQUHRUPUQCDUITUJBAUREOT $.

    $( A chain of elements satisfying two relations at once is a chain under
       either of them.  (Contributed by Ender Ting, 24-Jul-2026.) $)
    chnrrin $p |- ( A e. ( ( R i^i .< ) Chain B ) -> ( A e. ( R Chain B ) /\
      A e. ( .< Chain B ) ) ) $=
      ( cin cchn wcel wss inss1 chnrss ax-mp sseli inss2 jca ) ABCDEZFZGABCFZGA
      BDFZGPQAOCHPQHCDIBCOJKLPRAODHPRHCDMBDOJKLN $.

    $( Distribution of chain class constructor over relation intersection.
       (Contributed by Ender Ting, 24-Jul-2026.) $)
    chnrin2 $p |- ( ( R i^i .< ) Chain B ) = (
      ( R Chain B ) i^i ( .< Chain B ) ) $=
      ( vn cin cchn cv wcel wa chnrrin chnrin impbii elin bitr4i eqriv ) DABCEF
      ZABFZACFZEZDGZPHZTQHTRHIZTSHUAUBTABCJTABCKLTQRMNO $.

    $( Satisfying either of two chain relations is sufficient to make a chain
       under their union.  (Contributed by Ender Ting, 24-Jul-2026.) $)
    chnrun $p |- ( ( A e. ( R Chain B ) \/ A e. ( .< Chain B ) ) -> A e.
      ( ( R u. .< ) Chain B ) ) $=
      ( cchn wcel cun wss ssun1 chnrss ax-mp sseli ssun2 jaoi ) ABCEZFABCDGZEZF
      ABDEZFOQACPHOQHCDIBPCJKLRQADPHRQHDCMBPDJKLN $.

    $( Superadditivity of chain constructor over relation parameter.
       (Contributed by Ender Ting, 24-Jul-2026.) $)
    chnrun2 $p |- ( ( R Chain B ) u. ( .< Chain B ) ) C_
      ( ( R u. .< ) Chain B ) $=
      ( vn cchn cun cv wcel wo elun chnrun sylbi ssriv ) DABEZACEZFZABCFEZDGZPH
      RNHROHIRQHRNOJRABCKLM $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Scratchpad for number theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    evenwodadd.1 $e |- ( ph -> I e. ZZ ) $.
    evenwodadd.2 $e |- ( ph -> J e. ZZ ) $.
    evenwodadd.3 $e |- ( ph -> -. 2 || J ) $.
    $( If an integer is multiplied by its sum with an odd number (thus changing
       its parity), the result is even.  (Contributed by Ender Ting,
       30-Apr-2025.) $)
    evenwodadd $p |- ( ph -> 2 || ( I x. ( I + J ) ) ) $=
      ( c2 cdvds wbr caddc co cmul cz wcel wi 2z zaddcld mp3an2i wn wa 4anpull2
      dvdsmultr1 w3a opoe sylbir ex syl3anc dvdsmultr2 syld pm2.61d ) AGBHIZGBB
      CJKZLKHIZGMNZABMNZULMNZUKUMOPDABCDEQZGBULUBRAUKSZGULHIZUMAUOCMNZGCHISZURU
      SODEFUOUTVAUCZURUSVBURTUOURTUTVATTUSUOURUTVAUABCUDUEUFUGUNAUOUPUSUMOPDUQG
      BULUHRUIUJ $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Scratchpad for math on real numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    squeezedltsq.1 $e |- ( ph -> A e. RR ) $.
    squeezedltsq.2 $e |- ( ph -> B e. RR ) $.
    squeezedltsq.3 $e |- ( ph -> C e. RR ) $.
    squeezedltsq.4 $e |- ( ph -> A < B ) $.
    squeezedltsq.5 $e |- ( ph -> B < C ) $.
    $( If a real value is squeezed between two others, its square is less than
       square of at least one of them.  Deduction form.  (Contributed by Ender
       Ting, 31-Oct-2025.) $)
    squeezedltsq $p |- ( ph -> ( ( B x. B ) < ( A x. A ) \/ ( B x. B ) < ( C x.
      C ) ) ) $=
      ( cc0 cle wbr cmul co clt wa cr wcel adantr mpbid renegcld simpr le0neg1d
      cneg ltnegd lt2msq1 syl211anc wb wceq mul2negd syl breq12d anim1i syl3anc
      recn wo 0re letric sylancl orim12da ) ACJKLZJCKLZCCMNZBBMNZOLZVCDDMNOLZAV
      APZCUDZVHMNZBUDZVJMNZOLZVEVGVHQRZJVHKLZVJQRZVHVJOLZVLAVMVAACFUASVGVAVNAVA
      UBVGCACQRZVAFSUCTAVOVAABEUASAVPVAABCOLVPHABCEFUETSVHVJUFUGAVLVEUHVAAVIVCV
      KVDOAVQVIVCUIFVQCCCUOZVRUJUKABQRZVKVDUIEVSBBBUOZVTUJUKULSTAVBPVQVBPDQRZCD
      OLZVFAVQVBFUMAWAVBGSAWBVBISCDUFUNAVQJQRVAVBUPFUQCJURUSUT $.
  $}

  ${
    $d x t p A $.
    $( Square root of a natural number is algebraic.  (Contributed by Ender
       Ting, 21-Jul-2026.) $)
    sqrtnnaa $p |- ( A e. NN -> ( sqrt ` A ) e. AA ) $=
      ( vx vt cn wcel cfv cc cv cc0 wceq cz c0p c2 cexp cmin a1i cvv ovex eqtrd
      co vp csqrt cply csn cdif wrex caa nncn sqrtcld cmpt cxp cof fveq1 eqeq1d
      wss c1 cn0 zsscn 1z plypow mp3an nnz plyconst sylancr caddc zaddcl adantl
      2nn0 wa cmul zmulcl cneg neg1z plysub wne 0cn wfn wral rgenw mptfnf sylib
      nfcv fnconstg cnex 0cnd fnfvof syl22anc oveq1 fvmpt ax-mp eqtri fvconst2g
      eqid sq0 mpdan oveq12d nnne0 necomd subne0d eqnetrd ne0p eldifsnd sqsqrtd
      syl subidd rspcedvdw elaa sylanbrc ) ADEZAUBFZGEZXJBHZFZIJZBKUCFZLUDUEZUF
      XJUGEXIAAUHZUIZXIXNXJCGCHZMNTZUJZGAUDUKZOULTZFZIJBYCXPXLYCJXMYDIXJXLYCUMU
      NXIYCXOLXIBUAKYAYBYAXOEZXIKGUOZUPKEMUQEYEURUSVHCKMUTVAPXIYFAKEYBXOEURAVBA
      KVCVDXLKEUAHZKEVIZXLYGVETKEXIXLYGVFVGYHXLYGVJTKEXIXLYGVKVGUPVLKEXIVMPVNXI
      IGEZIYCFZIVOYCLVOVPXIYJIAOTZIXIYJIYAFZIYBFZOTZYKXIYAGVQZYBGVQZGQEZYIYJYNJ
      XIXTQEZCGVRZYOYSXIYRCGXSMNRVSPCGXTCGWBVTWAZGADWCZYQXIWDPZXIWEZGOYAYBQIWFW
      GXIYLIYMAOYLIJXIYLIMNTZIYIYLUUDJVPCIXTUUDGYAXSIMNWHYAWMZIMNRWIWJWNWKPXIYI
      YMAJUUCGAIDWLWOWPSXIIAUUCXQXIAIAWQWRWSWTIYCXAVDXBXIYDAAOTZIXIYDXJYAFZXJYB
      FZOTZUUFXIYOYPYQXKYDUUIJYTUUAUUBXRGOYAYBQXJWFWGXIUUGAUUHAOXIUUGXJMNTZAXIX
      KUUGUUJJXRCXJXTUUJGYAXSXJMNWHUUEXJMNRWIXDXIAXQXCSXIXKUUHAJXRGAXJDWLWOWPSX
      IAXQXESXFXJBXGXH $.

    $( Square root of a nonzero rational is algebraic.  (Contributed by Ender
       Ting, 22-Jul-2026.) $)
    sqrtnzqaa $p |- ( ( A e. QQ /\ A =/= 0 ) -> ( sqrt ` A ) e. AA ) $=
      ( vx vt cq wcel cc0 wne wa cfv cc wceq 3syl c2 cexp co c1 a1i syl2anc cvv
      cmin vp csqrt cv cply c0p csn cdif wrex caa simpl qcn sqrtcl cmpt cxp cof
      fveq1 eqeq1d wss cn0 qsscn cz 1z ax-mp plypow mp3an plyconst caddc qaddcl
      zq 2nn0 adantl cmul qmulcl cneg plysub 0cnd wfn fnconstg adantr wral ovex
      neg1z rgenw nfcv mptfnf mpbi jctil cnex 0cn pm3.2i fnfvof oveq1 fvmpt sq0
      eqid eqtri fvconst2g oveq12d eqtrd bilani subne0d eqnetrd eldifsnd sqrtth
      necom ne0p subid rspcedvdw elqaa sylanbrc ) ADEZAFGZHZAUBIZJEZXNBUCZIZFKZ
      BDUDIZUEUFUGZUHXNUIEXMXKAJEZXOXKXLUJZAUKZAULZLZXMXRXNCJCUCZMNOZUMZJAUFUNZ
      TUOOZIZFKBYJXTXPYJKXQYKFXNXPYJUPUQXMYJXSUEXMBUADYHYIYHXSEZXMDJURZPDEZMUSE
      YLUTPVAEYNVBPVIVCVJCDMVDVEQXMYMXKYIXSEYMXMUTQYBADVFRXPDEUAUCZDEHZXPYOVGOD
      EXMXPYOVHVKYPXPYOVLODEXMXPYOVMVKPVNZDEZXMYQVAEYRWBYQVIVCQVOXMFJEZFYJIZFGY
      JUEGXMVPZXMYTFATOZFXMYTFYHIZFYIIZTOZUUBXMYHJVQZYIJVQZHZJSEZYSHZYTUUEKXMUU
      GUUFXKUUGXLJADVRVSYGSEZCJVTUUFUUKCJYFMNWAWCCJYGCJWDWEWFWGZUUJXMUUIYSWHWIW
      JQJTYHYISFWKRXMUUCFUUDATUUCFKXMUUCFMNOZFYSUUCUUMKWICFYGUUMJYHYFFMNWLYHWOZ
      FMNWAWMVCWNWPQXMXKYSUUDAKYBUUAJAFDWQRWRWSXMFAUUAXKYAXLYCVSZXLFAGXKAFXEWTX
      AXBFYJXFRXCXMYKAATOZFXMYKXNYHIZXNYIIZTOZUUPXMUUHUUIXOHYKUUSKUULXMXOUUIYEW
      HWGJTYHYISXNWKRXMUUQAUURATXMUUQXNMNOZAXMYAXOUUQUUTKUUOYDCXNYGUUTJYHYFXNMN
      WLUUNXNMNWAWMLXMXKYAUUTAKYBYCAXDLWSXMXKXOUURAKYBYEJAXNDWQRWRWSXMXKYAUUPFK
      YBYCAXGLWSXHXNBXIXJ $.

    $( Square root of a rational number is algebraic.  (Contributed by Ender
       Ting, 22-Jul-2026.) $)
    sqrtqaa $p |- ( A e. QQ -> ( sqrt ` A ) e. AA ) $=
      ( cq wcel csqrt cfv caa wceq fveq2 sqrt0 eqtrdi eqeltrdi adantl sqrtnzqaa
      cc0 0aa pm2.61dane ) ABCZADEZFCZANANGZSQTRNFTRNDENANDHIJOKLAMP $.
  $}

  ${
    $d k x y $.
    $( Certain number sets and fields form a tower.  In particular, singleton
       1, natural numbers, natural numbers with zero, integers, rationals,
       algebraic reals (notice that current definition allows algebraic numbers
       to be complex thus the restriction), reals and complex number sets are a
       tower of proper subsets.  (Contributed by Ender Ting, 31-Jul-2026.) $)
    numtowerdt $p |- <" { 1 } NN NN0 ZZ QQ ( AA i^i RR ) RR CC "> e.
                     ( [C.] Chain _V ) $=
      ( c1 cn cn0 cz cq caa cr cc cvv crpss wcel wtru co a1i cfv wbr wceq ax-mp
      wpss c2 vk csn cin cs8 cchn cs7 cs1 cconcat df-s8 cnex cs6 df-s7 reex cs5
      df-s6 inex2 cs4 df-s5 qex cs3 df-s4 zex df-s3 nn0ex df-s2 nnex snex s1chn
      cs2 clsw c0 lsws1 wss wn 1nn 1ex snss mpbi 2nn wne 1re 1lt2 gtneii pm3.2i
      wa nelsn ssnelpss mp2 brrpss mpbir eqbrtri olcd chnccats1 eqeltrid nthruz
      lsws2 simpli lsws3 simpri lsws4 nthruc chash cmin c4 cword s5cli c5 s5len
      oveq1i 5m1e4 eqtri fveq2i s4cli s4len cats1fvn csqrt qssaa qssre sqrtnnaa
      lsw 3eqtri ssini sqrt2re elini sqrt2irr neli s6cli c6 s6len 6m1e5 cv cneg
      cfa cexp csu inss2 aaliou3r aaliou3 elinel1 c7 s7cli s7len 7m1e6 mptru
      mto ) AUBZBCDEFGUCZGHUDZIJUEZKLUUHUUFBCDEUUGGUFZHUGUHMUUIUUFBCDEUUGGHUILI
      JUUJHHIKLUJNLUUJUUFBCDEUUGUKZGUGUHMUUIUUFBCDEUUGGULZLIJUUKGGIKZLUMNLUUKUU
      FBCDEUNZUUGUGUHMUUIUUFBCDEUUGUOZLIJUUNUUGUUGIKZLGFUMUPZNLUUNUUFBCDUQZEUGU
      HMUUIUUFBCDEURZLIJUUREEIKZLUSNLUURUUFBCUTZDUGUHMUUIUUFBCDVALIJUVADDIKZLVB
      NLUVAUUFBVIZCUGUHMUUIUUFBCVCLIJUVCCCIKZLVDNLUVCUUFUGZBUGUHMUUIUUFBVELIJUV
      EBBIKZLVFNLIJUUFUUFIKZLAVGZNVHLUVEVJOZBJPZUVEVKQUVJLUVIUUFBJUVGUVIUUFQUVH
      UUFIVLRUUFBJPUUFBSZUUFBVMZTBKZTUUFKVNZWEUVKABKUVLVOABVPVQVRUVMUVNVSTAVTUV
      NATWAWBWCTAWFRWDUUFBTWGWHUUFBVFWIWJWKNWLWMWNLUVCVJOZCJPZUVCVKQUVPLUVOBCJU
      VFUVOBQVFUUFBIWPRBCJPBCSZUVQCDSZWOWQBCVDWIWJWKNWLWMWNLUVAVJOZDJPZUVAVKQUV
      TLUVSCDJUVDUVSCQVDUUFBCIWRRCDJPUVRUVQUVRWOWSCDVBWIWJWKNWLWMWNLUURVJOZEJPZ
      UURVKQUWBLUWADEJUVBUWADQVBUUFBCDIWTRDEJPDESZBDSZUWCUWDUWCWEZEGSZGHSZWEZXA
      WQWSDEUSWIWJWKNWLWMWNLUUNVJOZUUGJPZUUNVKQUWJLUWIEUUGJUWIUUNXBOZAXCMZUUNOZ
      XDUUNOZEUUNIXEZKUWIUWMQUUFBCDEXFZUUNUWOXTRUWLXDUUNUWLXGAXCMXDUWKXGAXCUUFB
      CDEXHZXIXJXKXLUUTUWNEQUSUURUUNXDIEUUSUUFBCDXMUUFBCDXNXORYAEUUGJPEUUGSZEUU
      GVMTXPOZUUGKZUWSEKVNZWEUWREFGXQXRYBUWTUXAUWSFGUVMUWSFKVSTXSRYCYDUWSEYEYFW
      DEUUGUWSWGWHEUUGUUQWIWJWKNWLWMWNLUUKVJOZGJPZUUKVKQUXCLUXBUUGGJUXBUUKXBOZA
      XCMZUUKOZXGUUKOZUUGUUKUWOKUXBUXFQUUFBCDEUUGYGZUUKUWOXTRUXEXGUUKUXEYHAXCMX
      GUXDYHAXCUUFBCDEUUGYIZXIYJXKXLUUPUXGUUGQUUQUUNUUKXGIUUGUUOUWPUWQXORYAUUGG
      JPUUGGSZUUGGVMBTUAYKYMOYLYNMUAYOZGKZUXKUUGKZVNZWEUXJFGYPUXLUXNUAYQUXMUXKF
      KUXKFUAYRYFUXKFGYSUUEWDUUGGUXKWGWHUUGGUMWIWJWKNWLWMWNLUUJVJOZHJPZUUJVKQUX
      PLUXOGHJUXOUUJXBOZAXCMZUUJOZYHUUJOZGUUJUWOKUXOUXSQUUFBCDEUUGGUUAUUJUWOXTR
      UXRYHUUJUXRYTAXCMYHUXQYTAXCUUFBCDEUUGGUUBXIUUCXKXLUUMUXTGQUMUUKUUJYHIGUUL
      UXHUXIXORYAGHJPUWGUWFUWGUWEUWHXAWSWSGHUJWIWJWKNWLWMWNUUD $.
  $}

  $( Triple-angle formula for sine, in pure sine form.  (Contributed by Ender
     Ting, 16-Mar-2026.) $)
  sin3t $p |- ( A e. CC -> ( sin ` ( 3 x. A ) ) = ( ( 3 x. ( sin ` A ) ) - ( 4
                x. ( ( sin ` A ) ^ 3 ) ) ) ) $=
    ( wcel c3 cmul co csin cfv c2 c1 caddc ccos c4 cexp cmin wceq mulcld oveq2d
    3eqtrd a1i oveq12d cc df-3 oveq1i 2cnd 1cnd id adddird eqtrid fveq2d sinadd
    syl2anc sin2t oveq1d sincl coscl coscld mullid sqvald sqcld sincossq eqtr3d
    mulassd mvlladdd subdid mulridd cn0 2nn0 expp1d mulcomd 3eqtrrd 3nn0 expcld
    eqtrd cos2tsin subdird addsub4d 2p1e3 2p2e4 eqcomi 3eqtr4rd 3eqtr2d ) AUABZ
    CADEZFGHADEZIADEZJEZFGZWDFGZWEKGZDEZWDKGZWEFGZDEZJEZCAFGZDEZLWOCMEZDEZNEZWB
    WCWFFWBWCHIJEZADEWFCWTADUBUCWBHIAWBUDZWBUEZWBUFZUGUHUIWBWDUABWEUABWGWNOWBHA
    XAXCPWBIAXBXCPZWDWEUJUKWBWNHWODEZHWQDEZNEZIWODEZHWOHMEZDEZWODEZNEZJEXEXHJEZ
    XFXKJEZNEWSWBWJXGWMXLJWBWJHWOAKGZDEZDEZWIDEHXPWIDEZDEZXGWBWHXQWIDAULUMWBHXP
    WIXAWBWOXOAUNZAUOZPWBWEXDUPVBWBXSHWOIXINEZDEZDEHWOWQNEZDEXGWBXRYCHDWBXRXPXO
    DEWOXOXODEZDEYCWBWIXOXPDWBWEAKAUQZUIQWBWOXOXOXTYAYAVBWBYEYBWODWBXOHMEZYEYBW
    BXOYAURWBXIYGIWBWOXTUSZWBXOYAUSAUTVCVAQRQWBYCYDHDWBYCWOIDEZWOXIDEZNEYDWBWOI
    XIXTXBYHVDWBYIWOYJWQNWBWOXTVEWBWQWOWTMEXIWODEZYJWBCWTWOMCWTOWBUBSQWBWOHXTHV
    FBWBVGSVHWBXIWOYHXTVIZVJZTVMQWBHWOWQXAXTWBWOCXTCVFBWBVKSVLZVDRRWBWMIXJNEZWO
    DEXLWBWKYOWLWODAVNWBWEAFYFUITWBIXJWOXBWBHXIXAYHPZXTVOVMTWBXEXHXFXKWBHWOXAXT
    PWBIWOXBXTPWBHWQXAYNPWBXJWOYPXTPVPWBXMWPXNWRNWBWTWODEXMWPWBHIWOXAXBXTUGWBWT
    CWODWTCOWBVQSUMVAWBHHJEZWQDEXFXFJEWRXNWBHHWQXAXAYNUGWBLYQWQDLYQOWBYQLVRVSSU
    MWBXKXFXFJWBXKHYKDEHYJDEXFWBHXIWOXAYHXTVBWBYKYJHDYLQWBYJWQHDYMQRQVTTWAR $.

  $( Triple-angle formula for cosine, in pure cosine form.  (Contributed by
     Ender Ting, 16-Mar-2026.) $)
  cos3t $p |- ( A e. CC -> ( cos ` ( 3 x. A ) ) = ( ( 4 x. ( ( cos ` A ) ^ 3 )
                ) - ( 3 x. ( cos ` A ) ) ) ) $=
    ( cc wcel c3 cmul co ccos cfv c2 c1 caddc csin cmin cexp mulcld oveq12d a1i
    wceq oveq2d 3eqtrd c4 df-3 oveq1i 2cnd 1cnd id adddird eqtrid fveq2d cosadd
    syl2anc cos2t mullid coscl sqcld subdird mulassd oveq2i 2nn0 expp1d eqtr2id
    cn0 eqtrd oveq1d sin2t sincl mul12d sqvald eqcomd sincossq mvlraddd mulridd
    subdid mulcomd 3eqtrrd 3nn0 expcld subadd4d 2p2e4 eqtr3d 1p2e3 ) ABCZDAEFZG
    HIAEFZJAEFZKFZGHZWDGHZWEGHZEFZWDLHZWELHZEFZMFZUAAGHZDNFZEFZDWOEFZMFZWBWCWFG
    WBWCIJKFZAEFWFDWTAEUBUCWBIJAWBUDZWBUEZWBUFZUGUHUIWBWDBCWEBCWGWNRWBIAXAXCOWB
    JAXBXCOWDWEUJUKWBWNIWPEFZJWOEFZMFZIWOEFZXDMFZMFXDXDKFZXEXGKFZMFWSWBWJXFWMXH
    MWBWJIWOINFZEFZJMFZWOEFXLWOEFZXEMFXFWBWHXMWIWOEAULWBWEAGAUMZUIPWBXLJWOWBIXK
    XAWBWOAUNZUOZOXBXPUPWBXNXDXEMWBXNIXKWOEFZEFXDWBIXKWOXAXQXPUQWBXRWPIEWBWPWOW
    TNFZXRDWTWONUBURWBWOIXPIVBCWBUSQUTZVASVCVDTWBWMIALHZWOEFZEFZYAEFZIWOWPMFZEF
    ZXHWBWKYCWLYAEAVEWBWEALXOUIPWBYDIYBYAEFZEFYFWBIYBYAXAWBYAWOAVFZXPOYHUQWBYGY
    EIEWBYGWOYAINFZEFZWOJXKMFZEFZYEWBYGYAWOYAEFEFWOYAYAEFZEFYJWBYAWOYAYHXPYHUQW
    BYAWOYAYHXPYHVGWBYMYIWOEWBYIYMWBYAYHVHVISTWBYIYKWOEWBYIXKJWBYAYHUOXQAVJVKSW
    BYLWOJEFZWOXKEFZMFYEWBWOJXKXPXBXQVMWBYNWOYOWPMWBWOXPVLWBWPXSXRYOWBDWTWONDWT
    RWBUBQSXTWBXKWOXQXPVNVOPVCTSVCWBIWOWPXAXPWBWODXPDVBCWBVPQVQZVMTPWBXDXEXGXDW
    BIWPXAYPOZWBJWOXBXPOWBIWOXAXPOYQVRWBXIWQXJWRMWBIIKFZWPEFXIWQWBIIWPXAXAYPUGW
    BYRUAWPEYRUARWBVSQVDVTWBJIKFZWOEFXJWRWBJIWOXBXAXPUGWBYSDWOEYSDRWBWAQVDVTPTT
    $.

  $(
  @( Four-times-angle formula for sine.  (Contributed by Ender Ting,
     ?date?.) @)
  sin4t @p |- ( A e. CC -> ( sin ` ( 4 x. A ) ) = ? ) @= ? @.

  @( Four-times-angle formula for cosine.  (Contributed by Ender Ting,
     ?date?.) @)
  cos4t @p |- ( A e. CC -> ( cos ` ( 4 x. A ) ) = ? ) @= ? @.
  $)

  $( Lemma 1 for quintupled angle sine calculation, expanding triple-angle sine
     times double-angle cosine.  (Contributed by Ender Ting, 16-Mar-2026.) $)
  sin5tlem1 $p |- ( N e. CC -> ( ( ( 3 x. N ) - ( 4 x. ( N ^ 3 ) ) ) x. ( 1 - (
    2 x. ( N ^ 2 ) ) ) ) = ( ( ( 8 x. ( N ^ 5 ) ) - ( ; 1 0 x. ( N ^ 3 ) ) ) +
    ( 3 x. N ) ) ) $=
    ( cc wcel c3 cmul co c4 cexp cmin c1 c2 caddc c8 c5 a1i mulcld wceq oveq12d
    eqtrd c6 cc0 cdc 3cn id 4cn cn0 3nn0 expcld 1cnd 2cnd mulsubd oveq1d addcld
    sqcl addcomd addsubd mul4d 2t4e8 2nn0 expaddd 3p2e5 addcomli oveq2i eqtr3di
    2cn 3t2e6 expp1d mulcomd eqtr2id mullidd 6cn adddird 6p4e10 3eqtr2d mulridd
    df-3 3eqtrd ) ABCZDAEFZGADHFZEFZIFJKAKHFZEFZIFEFVSJEFZWCWAEFZLFZVSWCEFZJWAE
    FZLFZIFZWEWIIFZWDLFZMANHFZEFZJUAUBZVTEFZIFZVSLFVRVSWAJWCVRDADBCVRUCOZVRUDZP
    ZVRGVTGBCVRUEOZVRADWSDUFCVRUGOZUHZPZVRUIZVRKWBVRUJZAUNZPZUKVRWJWEWDLFZWIIFW
    LVRWFXIWIIVRWDWEVRVSJWTXEPZVRWCWAXHXDPZUOULVRWEWDWIXKXJVRWGWHVRVSWCWTXHPVRJ
    WAXEXDPUMUPSVRWKWQWDVSLVRWEWNWIWPIVRWEKGEFZWBVTEFZEFWNVRKWBGVTXFXGXAXCUQVRX
    LMXMWMEXLMQVRUROVRAKDLFZHFXMWMVRAKDWSXBKUFCVRUSOZUTXNNAHDKNUCVEVAVBVCVDRSVR
    WITVTEFZWALFTGLFZVTEFWPVRWGXPWHWALVRWGDKEFZAWBEFZEFXPVRDAKWBWRWSXFXGUQVRXRT
    XSVTEXRTQVRVFOVRVTAKJLFZHFZXSDXTAHVPVCVRYAWBAEFXSVRAKWSXOVGVRWBAXGWSVHSVIRS
    VRWAXDVJRVRTGVTTBCVRVKOXAXCVLVRXQWOVTEXQWOQVRVMOULVNRVRVSWTVORVQ $.

  $( Lemma 2 for quintupled angle sine calculation, multiplicating triple angle
     cosine by cosine straight and converting into sine.  (Contributed by Ender
     Ting, 16-Apr-2026.) $)
  sin5tlem2 $p |- ( ( N e. CC /\ M e. CC /\ ( N ^ 2 ) = ( 1 - ( M ^ 2 ) ) )
    -> ( ( ( 4 x. ( N ^ 3 ) ) - ( 3 x. N ) ) x. N ) = ( ( 4 x. ( ( 1 - ( 2 x.
    ( M ^ 2 ) ) ) + ( M ^ 4 ) ) ) - ( 3 x. ( 1 - ( M ^ 2 ) ) ) ) ) $=
    ( cc wcel c2 cexp co c1 cmin wceq c4 cmul caddc a1i cn0 3nn0 oveq2d oveq12d
    c3 eqtrd w3a 4cn simp1 expcld mulcld 3cn subdird mulassd 2t2e4 df-4 id 2nn0
    eqtri expmuld expp1d 3eqtr3rd 3ad2ant1 oveq1 3ad2ant3 3eqtrd 1cnd binom2sub
    simp2 syl2anc sq1 mullidd eqcomi eqtr2d sqval eqcomd oveq2 ) BCDZACDZBEFGZH
    AEFGZIGZJZUAZKBSFGZLGZSBLGZIGBLGVTBLGZWABLGZIGKHEVOLGZIGZAKFGZMGZLGZSVPLGZI
    GVRVTWABVRKVSKCDVRUBNZVRBSVLVMVQUCZSODZVRPNUDZUEVRSBSCDVRUFNZWKUEWKUGVRWBWH
    WCWIIVRWBKVPEFGZLGZWHVRWBKVSBLGZLGKVNEFGZLGZWPVRKVSBWJWMWKUHVRWQWRKLVLVMWQW
    RJVQVLBEELGZFGBSHMGZFGWRWQVLWTXABFWTXAJVLWTKXAUIUJUMNQVLBEEVLUKZEODZVLULNZX
    DUNVLBSXBWLVLPNUOUPUQQVQVLWSWPJVMVQWRWOKLVNVPEFURQUSUTVRWOWGKLVRWOHEFGZEHVO
    LGZLGZIGZVOEFGZMGZWGVRHCDVOCDWOXJJVRVAVRAEVLVMVQVCZXCVRULNZUDZHVOVBVDVRXHWE
    XIWFMVRXEHXGWDIXEHJVRVENVRXFVOELVRVOXMVFQRVRWFAWTFGXIVRKWTAFKWTJVRWTKUIVGNQ
    VRAEEXKXLXLUNVHRTQTVRWCSBBLGZLGSVNLGZWIVRSBBWNWKWKUHVRXNVNSLVLVMXNVNJVQVLVN
    XNBVIVJUQQVQVLXOWIJVMVNVPSLVKUSUTRT $.

  $( Lemma 3 for quintupled angle sine calculation, multiplicating triple angle
     cosine by double angle sine.  (Contributed by Ender Ting, 16-Apr-2026.) $)
  sin5tlem3 $p |- ( ( N e. CC /\ M e. CC /\ ( N ^ 2 ) = ( 1 - ( M ^ 2 ) ) )
    -> ( ( ( 4 x. ( N ^ 3 ) ) - ( 3 x. N ) ) x. ( 2 x. ( M x. N ) ) ) = ( ( ( 4
    x. ( ( 1 - ( 2 x. ( M ^ 2 ) ) ) + ( M ^ 4 ) ) ) - ( 3 x. ( 1 - ( M ^ 2 ) )
    ) ) x. ( 2 x. M ) ) ) $=
    ( cc wcel c2 cexp co c1 cmin wceq w3a c4 c3 caddc simp2 simp1 oveq2d mulcld
    cmul a1i mulcomd 2cnd mul12d eqtrd 4cn cn0 3nn0 expcld 3cn subcld sin5tlem2
    mulassd oveq1d 3eqtr2d ) BCDZACDZBEFGHAEFGZIGZJZKZLBMFGZSGZMBSGZIGZEABSGZSG
    ZSGVDBEASGZSGZSGVDBSGZVGSGLHEUQSGIGALFGNGSGMURSGIGZVGSGUTVFVHVDSUTVFEBASGZS
    GVHUTVEVKESUTABUOUPUSOZUOUPUSPZUAQUTEBAUTUBZVMVLUCUDQUTVDBVGUTVBVCUTLVALCDU
    TUETUTBMVMMUFDUTUGTUHRUTMBMCDUTUITVMRUJVMUTEAVNVLRULUTVIVJVGSABUKUMUN $.

  $( Lemma 4 for quintupled angle sine calculation: expanding lemma 3 result to
     difference of polynomials.  (Contributed by Ender Ting, 17-Apr-2026.) $)
  sin5tlem4 $p |- ( ( N e. CC /\ M e. CC /\ ( N ^ 2 ) = ( 1 - ( M ^ 2 ) ) )
    -> ( ( ( 4 x. ( N ^ 3 ) ) - ( 3 x. N ) ) x. ( 2 x. ( M x. N ) ) ) = (
      ( ( ( 8 x. ( M ^ 5 ) ) - ( ; 1 6 x. ( M ^ 3 ) ) ) + ( 8 x. M ) ) -
      ( ( 6 x. M ) - ( 6 x. ( M ^ 3 ) ) ) ) ) $=
    ( cc wcel c2 cexp co c1 cmin wceq c4 c3 cmul caddc c8 c5 a1i mulcld oveq12d
    c6 w3a cdc sin5tlem3 4cn 1cnd 2cnd sqcl subcld id cn0 expcld addcld subdird
    4nn0 3cn mul4d 4t2e8 oveq1d addsubd eqcomd 5nn0 mullid expp1d oveq2d eqtr3d
    4p1e5 joinlmuladdmuld comraddd mulassd 2p1e3 eqtrd 3eqtrd 8cn subdid adddid
    2nn0 3nn0 8t2e16 16nn0 nn0cni 3t2e6 6cn 3ad2ant2 ) BCDZACDZBEFGHAEFGZIGZJZU
    AKBLFGMGLBMGIGEABMGMGMGKHEWFMGZIGZAKFGZNGZMGZLWGMGZIGEAMGZMGZOAPFGZMGZHTUBZ
    ALFGZMGZIGOAMGZNGZTAMGTWTMGIGZIGZABUCWEWDWPXEJWHWEWPWMWOMGZWNWOMGZIGXEWEWMW
    NWOWEKWLKCDWEUDQZWEWJWKWEHWIWEUEZWEEWFWEUFZAUGZRZUHWEAKWEUIZKUJDWEUNQZUKZUL
    ZRWELWGLCDWEUOQZWEHWFXIXKUHZRWEEAXJXMRUMWEXFXCXGXDIWEXFKEMGZWLAMGZMGZWRXBNG
    ZXAIGZXCWEKWLEAXHXPXJXMUPWEYAOXTMGZOWQANGZMGZOEMGZWTMGZIGZYCWEXSOXTMXSOJWEU
    QQURWEYDOYEEWTMGZIGZMGYFOYJMGZIGYIWEXTYKOMWEXTHWKNGZWIIGZAMGYMAMGZWIAMGZIGY
    KWEWLYNAMWEYNWLWEHWKWIXIXOXLUSUTURWEYMWIAWEHWKXIXOULXLXMUMWEYOYEYPYJIWEYOAW
    QXMWEAPXMPUJDWEVAQUKZWEHAWKAWQNGXIXMXOWEHAMGZAWKAMGZWQNAVBZWEAKHNGZFGYSWQWE
    AKXMXNVCWEUUAPAFUUAPJWEVFQVDVESVGVHWEYPEWFAMGZMGYJWEEWFAXJXKXMVIWEUUBWTEMWE
    AEHNGZFGUUBWTWEAEXMEUJDWEVPQVCWEUUCLAFUUCLJWEVJQVDVEZVDVKSVLVDWEOYEYJOCDWEV
    MQZWEWQAYQXMULWEEWTXJWEALXMLUJDWEVQQUKZRVNWEYLYHYFIWEYHYLWEOEWTUUEXJUUFVIUT
    VDVLWEYFYBYHXAIWEOWQAUUEYQXMVOWEYGWSWTMYGWSJWEVRQURSVLWEWRXBXAWEOWQUUEYQRWE
    OAUUEXMRWEWSWTWSCDWEWSVSVTQUUFRUSVLWEXGLEMGZWGAMGZMGTAWTIGZMGXDWELWGEAXQXRX
    JXMUPWEUUGTUUHUUIMUUGTJWEWAQWEUUHYRUUBIGUUIWEHWFAXIXKXMUMWEYRAUUBWTIYTUUDSV
    KSWETAWTTCDWEWBQXMUUFVNVLSVKWCVK $.

  $( Lemma 5 for quintupled angle sine calculation: sine of triple-angle and
     double-angle sum, as a polynomial in sine straight.  (Contributed by Ender
     Ting, 17-Apr-2026.) $)
  sin5tlem5 $p |- ( ( N e. CC /\ M e. CC /\ ( N ^ 2 ) = ( 1 - ( M ^ 2 ) ) )
    -> ( ( ( ( 3 x. M ) - ( 4 x. ( M ^ 3 ) ) ) x. ( 1 - ( 2 x. ( M ^ 2 ) ) ) )
         + ( ( ( 4 x. ( N ^ 3 ) ) - ( 3 x. N ) ) x. ( 2 x. ( M x. N ) ) ) ) =
    ( ( ( ; 1 6 x. ( M ^ 5 ) ) - ( ; 2 0 x. ( M ^ 3 ) ) ) + ( 5 x. M ) ) ) $=
    ( cc wcel c2 cexp co c1 cmin wceq c3 cmul caddc c8 a1i mulcld oveq1d oveq2d
    c5 c6 w3a c4 cc0 cdc sin5tlem1 3ad2ant2 sin5tlem4 oveq12d 8cn id 6cn subcld
    cn0 5nn0 expcld 16nn0 nn0cni 3nn0 addcld addcomd addsubsub23 eqtrd comraddd
    10nn nncni 3cn add4d addsub4d 8p8e16 eqcomi adddird 10p10e20 subdird eqcomd
    subsubd dec10p mvrraddd 3eqtr3d 3eqtr4rd 2cn 6p2e8 mvrladdi oveq2i 3eqtr3rd
    3p2e5 eqtri 3eqtrd ) BCDZACDZBEFGHAEFGZIGJZUAZKALGZUBAKFGZLGIGHEWJLGIGLGZUB
    BKFGLGKBLGIGEABLGLGLGZMGNASFGZLGZHUCUDZWNLGZIGZWMMGZWRHTUDZWNLGZIGZNALGZMGZ
    TALGZTWNLGZIGZIGZMGZXCWQLGZEUCUDZWNLGZIGZSALGZMGZWLWOXBWPXKMWIWHWOXBJWKAUEU
    FABUGUHWIWHXLXRJWKWIXLXBXEXIMGZXFXHIGZMGZMGXAXSMGZWMXTMGZMGXRWIXKYAXBMWIXKX
    TXSWIXFXHWINANCDWIUIOZWIUJZPZWITATCDWIUKOZYEPZULZWIXEXIWIWRXDWINWQYDWIASYES
    UMDWIUNOUOZPZWIXCWNXCCDWIXCUPUQOZWIAKYEKUMDWIUROUOZPZULZWITWNYGYMPZUSZWIXKX
    FXEMGZXJIGXTXSMGWIXGYRXJIWIXEXFYOYFUTQWIXFXEXHXIYFYOYHYPVAVBVCRWIXAWMXSXTWI
    WRWTYKWIWSWNWSCDWIWSVDVEOZYMPZULWIKAKCDWIVFOZYEPYQYIVGWIYBXPYCXQMWIWRWRMGZW
    TWTMGZIGXAXAMGXPYBWIWRWRWTWTYKYKYTYTVHWIXMUUBXOUUCIWIXMNNMGZWQLGUUBWIXCUUDW
    QLXCUUDJWIUUDXCVIVJOQWINNWQYDYDYJVKVBWIXOWSWSMGZWNLGUUCWIXNUUEWNLXNUUEJWIUU
    EXNVLVJOQWIWSWSWNYSYSYMVKVBUHWIXSXAXAMWIWRXDXIIGZIGWRXCTIGZWNLGZIGXSXAWIUUF
    UUHWRIWIUUHUUFWIXCTWNYLYGYMVMVNRWIWRXDXIYKYNYPVOWIUUHWTWRIWIUUGWSWNLWIXCWST
    YSYGXCWSTMGZJWIUUIXCTVPVJOVQQRVRRVSWIKNTIGZMGZALGWMUUJALGZMGXQYCWIKUUJAUUAW
    INTYDYGULYEVKWIUUKSALUUKSJWIUUKKEMGSUUJEKMNTEUKVTTEMGNWAVJWBWCWEWFOQWIUULXT
    WMMWINTAYDYGYEVMRWDUHWGUFVB $.

  $( Five-times-angle formula for sine, in pure sine form.  (Contributed by
     Ender Ting, 17-Apr-2026.) $)
  sin5t $p |- ( A e. CC -> ( sin ` ( 5 x. A ) ) = ( ( ( ; 1 6 x. ( ( sin ` A )
    ^ 5 ) ) - ( ; 2 0 x. ( ( sin ` A ) ^ 3 ) ) ) + ( 5 x. ( sin ` A ) ) ) ) $=
    ( cc wcel c5 cmul co csin cfv c3 c2 caddc c4 cexp cmin c1 ccos cdc wceq a1i
    oveq12d c6 cc0 3p2e5 eqcomi oveq1d 3cn 2cnd id adddird fveq2d mulcld sinadd
    eqtrd syl2anc sin3t cos2tsin cos3t sin2t coscl sincl sqcld sincossq syl3anc
    mvlladdd sin5tlem5 3eqtrd ) ABCZDAEFZGHIAEFZJAEFZKFZGHZIAGHZEFLVMIMFZEFNFZO
    JVMJMFZEFNFZEFZLAPHZIMFEFIVSEFNFZJVMVSEFEFZEFZKFZOUAQVMDMFEFJUBQVNEFNFDVMEF
    KFZVGVHVKGVGVHIJKFZAEFVKVGDWEAEDWERVGWEDUCUDSUEVGIJAIBCVGUFSZVGUGZVGUHZUIUM
    UJVGVLVIGHZVJPHZEFZVIPHZVJGHZEFZKFZWCVGVIBCVJBCVLWORVGIAWFWHUKVGJAWGWHUKVIV
    JULUNVGWKVRWNWBKVGWIVOWJVQEAUOAUPTVGWLVTWMWAEAUQAURTTUMVGVSBCVMBCVSJMFZOVPN
    FRWCWDRAUSZAUTZVGVPWPOVGVMWRVAVGVSWQVAAVBVDVMVSVEVCVF $.

  $( Five-times-angle formula for cosine, in pure cosine form.  (Contributed by
     Ender Ting, 20-Apr-2026.) $)
  cos5t $p |- ( A e. CC -> ( cos ` ( 5 x. A ) ) = ( ( ( ; 1 6 x. ( ( cos ` A )
    ^ 5 ) ) - ( ; 2 0 x. ( ( cos ` A ) ^ 3 ) ) ) + ( 5 x. ( cos ` A ) ) ) ) $=
    ( cc wcel c5 cmul co cfv cpi c2 cmin csin c1 cexp caddc wceq 2cn a1i oveq1d
    c3 c4 ccos cdiv c6 cdc cc0 cz picn 2ne0 divcli id mulcld subcld 1zzd sinper
    5cn syl2anc subdid mullidi eqcomi 2picn divcan2i oveq2i 2t2e4 oveq1i eqtr3i
    mulassi 3eqtri oveq12d 1cnd 4cn adddird ax-1cn df-5 comraddi 3eqtr2d mulcli
    addsubd 3eqtr2rd fveq2d sinhalfpim syl 3eqtr3rd sin5t oveq2d 3eqtrd ) ABCZD
    AEFZUAGZDHIUBFZAJFZEFZKGZLUCUDZWJKGZDMFZEFZIUEUDZWNSMFZEFZJFZDWNEFZNFZWMAUA
    GZDMFZEFZWQXCSMFZEFZJFZDXCEFZNFWFWIWGJFZLIHEFZEFZNFZKGZXJKGZWLWHWFXJBCLUFCX
    NXOOWFWIWGWIBCWFHIUGPUHUIZQZWFDADBCWFUOQZWFUJZUKZULWFUMXJLUNUPWFXMWKKWFWKDW
    IEFZWGJFWIXLNFZWGJFXMWFDWIAXRXQXSUQWFYBYAWGJWFYBLWIEFZTWIEFZNFLTNFZWIEFYAWF
    WIYCXLYDNWIYCOWFYCWIWIXPURUSQXLYDOWFXLXKIIWIEFZEFZYDXKUTURHYFIEYFHHIUGPUHVA
    USVBIIEFZWIEFYGYDIIWIPPXPVFYHTWIEVCVDVEVGQVHWFLTWIWFVITBCWFVJQXQVKWFYEDWIEY
    EDOWFDYEDTLVJVLVMVNUSQRVORWFWIXLWGXQXLBCWFLXKVLUTVPQXTVQVRVSWFWGBCXOWHOXTWG
    VTWAWBWFWJBCWLXBOWFWIAXQXSULWJWCWAWFWTXHXAXINWFWPXEWSXGJWFWOXDWMEWFWNXCDMAV
    TZRWDWFWRXFWQEWFWNXCSMYIRWDVHWFWNXCDEYIWDVHWE $.

  $( Five-times-angle formula for cosine, substitution helper.  (Contributed by
     Ender Ting, 9-May-2026.) $)
  cos5teq $p |- ( ( A e. CC /\ B = ( 5 x. A ) /\ C = ( cos ` A ) ) -> ( cos ` B
     ) = ( ( ( ; 1 6 x. ( C ^ 5 ) ) - ( ; 2 0 x. ( C ^ 3 ) ) ) + ( 5 x. C ) ) )
     $=
    ( cc wcel c5 cmul co wceq ccos cfv w3a cdc cexp c3 cmin caddc oveq1d oveq2d
    oveq12d c1 c6 cc0 simp2 fveq2d cos5t 3ad2ant1 eqcom biimpi 3ad2ant3 3eqtrd
    c2 ) ADEZBFAGHZIZCAJKZIZLZBJKUNJKZUAUBMZUPFNHZGHZULUCMZUPONHZGHZPHZFUPGHZQH
    ZUTCFNHZGHZVCCONHZGHZPHZFCGHZQHZURBUNJUMUOUQUDUEUMUOUSVHIUQAUFUGUQUMVHVOIUO
    UQVFVMVGVNQUQVBVJVEVLPUQVAVIUTGUQUPCFNUQUPCICUPUHUIZRSUQVDVKVCGUQUPCONVPRST
    UQUPCFGVPSTUJUK $.

  ${
    goldpolyfactor.1 $e |- F e. CC $.
    $( Factorization of a polynomial which has golden ratio among its roots,
       done by term-by-term-by-term multiplying and summing a few shorter
       polynomials.  (Contributed by Ender Ting, 24-Jul-2026.) $)
    goldpolyfactor $p |- ( ( ( ( ( F ^ 2 ) - F ) - 1 ) x. ( ( ( F ^ 2 ) - F )
      - 1 ) ) x. ( F + 2 ) )
      = ( ( ( ( F ^ 5 ) - ( 5 x. ( F ^ 3 ) ) ) + ( 5 x. F ) ) + 2 ) $=
      ( c2 cexp co cmin c1 cmul caddc c4 c5 subcli ax-1cn cc wcel eqtri oveq12i
      wceq oveq1i 2cn sqcli subdii subdiri cn0 expadd mp3an 2p2e4 oveq2i eqtr3i
      c3 2nn0 mulcomi df-3 expp1 mp2an eqtr2i mullidi sqvali eqcomi 4nn0 subsub
      3nn0 nnncan2 subsub4 2timesi eqtr4i 3eqtri mulridi mulcli addcli wtru a1i
      expcl addsubsub23 mptru adddii adddiri df-5 mulassi df-4 mul32i 2t2e4 4cn
      addassi add4i ppncan addsub4i npcan comraddi 3eqtrri 3eqtr2i 3eqtr4ri
      5nn0 ) ACDEZAFEZGFEZWPHEZACIEZHEAJDEZCAUJDEZHEZFEZWNFEZCAHEZIEZGIEZWRHEXF
      AHEZXFCHEZIEZAKDEZKWTHEZFEZKAHEZIEZCIEZWQXFWRHWQWPWOHEZWPGHEZFEXBAIEZWPFE
      ZXFWPWOGWOGWNAABUAZBLZMLZYAMUBXPXRXQWPFXPWPWNHEZWPAHEZFEWSWTFEZWNFEZWTWNF
      EZAFEZFEZXRWPWNAYBXTBUBYCYFYDYHFYCWOWNHEZGWNHEZFEYFWOGWNYAMXTUCYJYEYKWNFY
      JWNWNHEZAWNHEZFEYEWNAWNXTBXTUCYLWSYMWTFACCIEZDEZYLWSANOZCUDOZYQYOYLRBUKUK
      ACCUEUFYNJADUGUHUIYMWNAHEZWTAWNBXTULWTACGIEZDEZYRUJYSADUMUHYPYQYTYRRBUKAC
      UNUOUPZPQPWNXTUQQPYDWOAHEZGAHEZFEYHWOGAYAMBUCUUBYGUUCAFUUBYRAAHEZFEYGWNAA
      XTBBUCYRWTUUDWNFUUAWNUUDABURZUSQPABUQZQPQYIYFYGFEZAIEZXRYFNOYGNOYPYIUUHRY
      EWNWSWTYPJUDOZWSNOZBUTAJVMUOZYPUJUDOZWTNOZBVBAUJVMUOZLZXTLWTWNUUNXTLBYFYG
      AVAUFUUGXBAIUUGYEWTFEZXBYENOUUMWNNOZUUGUUPRUUOUUNXTYEWTWNVCUFUUPWSWTWTIEZ
      FEZXBUUJUUMUUMUUPUUSRUUKUUNUUNWSWTWTVDUFXAUURWSFWTUUNVEUHVFPSPVGWPYBVHQXS
      XRWOFEZGIEZXFXRNOWONOGNOXSUVARXBAWSXAUUKCWTTUUNVIZLZBVJYAMXRWOGVAUFUUTXEG
      IUUTXCAAIEZIEZXEUUTUVERVKXBAWNAXBNOVKUVCVLYPVKBVLZUUQVKXTVLUVFVNVOXDUVDXC
      IABVEUHVFSPVGSXFACXEGXCXDXBWNUVCXTLZCATBVIZVJZMVJBTVPXIXJCWSHEZFEZWTFEZCW
      NHEZIEZAIEZUVJJWTHEZFEZUVMFEZJAHEZIEZCIEZIEUVOUVTIEZCIEXOXGUVOXHUWAIXGXEA
      HEZUUCIEUVOXEGAUVIMBVQUWCUVNUUCAIUWCXCAHEZXDAHEZIEUVNXCXDAUVGUVHBVQUWDUVL
      UWEUVMIUWDXBAHEZYRFEUVLXBWNAUVCXTBUCUWFUVKYRWTFUWFWSAHEZXAAHEZFEUVKWSXAAU
      UKUVBBUCUWGXJUWHUVJFXJAJGIEZDEZUWGKUWIADVRUHYPUUIUWJUWGRBUTAJUNUOUPUWHCWT
      AHEZHEUVJCWTATUUNBVSWSUWKCHWSAUJGIEZDEZUWKJUWLADVTUHYPUULUWMUWKRBVBAUJUNU
      OPUHVFQPUUAQPUWECUUDHEUVMCAATBBVSWNUUDCHUUEUHVFQPUUFQPXHXECHEZGCHEZIEUWAX
      EGCUVIMTVQUWNUVTUWOCIUWNXCCHEZXDCHEZIEUVTXCXDCUVGUVHTVQUWPUVRUWQUVSIUWPXB
      CHEZWNCHEZFEUVRXBWNCUVCXTTUCUWRUVQUWSUVMFUWRWSCHEZXACHEZFEUVQWSXACUUKUVBT
      UCUWTUVJUXAUVPFWSCUUKTULUXACCHEZWTHEUVPCWTCTUUNTWAUXBJWTHWBSPQPWNCXTTULQP
      UWQUXBAHEUVSCACTBTWAUXBJAHWBSPQPCTUQQPQUVOUVTCUVNAUVLUVMUVKWTXJUVJYPKUDOX
      JNOZBWMAKVMUOZCWSTUUKVIZLZUUNLZCWNTXTVIZVJZBVJUVRUVSUVQUVMUVJUVPUXEJWTWCU
      UNVIZLZUXHLZJAWCBVIZVJTWDUWBXNCIUWBUVNUVRIEZAUVSIEZIEXNUVNAUVRUVSUXIBUXLU
      XMWEUXNXLUXOXMIUXNUVLUVQIEZUVKUVJIEZWTUVPIEZFEXLUVLNOUVMNOUVQNOUXNUXPRUXG
      UXHUXKUVLUVMUVQWFUFUVKUVJWTUVPUXFUXEUUNUXJWGUXQXJUXRXKFUXCUVJNOUXQXJRUXDU
      XEXJUVJWHUOXKGJIEZWTHEGWTHEZUVPIEUXRKUXSWTHKJGWCMVRWIZSGJWTMWCUUNVQUXTWTU
      VPIWTUUNUQSWJQWKUXSAHEUUCUVSIEXMUXOGJAMWCBVQKUXSAHUYASAUUCUVSIUUCAUUFUSSW
      LQPSWKVG $.
  $}

  $( TODO: promote ~ 5ne0 and minify the block, or all usages of ~ 5pos $)

  ${
    goldra.val $e |- F = ( 2 x. ( cos ` ( _pi / 5 ) ) ) $.
    $( The golden ratio is a real value.  (Contributed by Ender Ting,
       15-Mar-2026.) $)
    goldrarr $p |- F e. RR $=
      ( c2 cpi c5 cdiv co ccos cfv cmul cr 2re wcel pire 5pos gt0ne0ii redivcli
      5re recoscl ax-mp remulcli eqeltri ) ACDEFGZHIZJGKBCUDLUCKMUDKMDENREROPQU
      CSTUAUB $.

    $( Alternative trigonometric formula for the golden ratio.  (Contributed by
       Ender Ting, 15-Mar-2026.) $)
    goldrasin $p |- F = ( 2 x. ( sin ` ( _pi x. ( 3 / ; 1 0 ) ) ) ) $=
      ( c2 cpi c5 cdiv co ccos cfv cmul c3 c1 cmin picn 5cn 2cn eqtri wtru wcel
      cc cc0 cdc csin 5re 5pos gt0ne0ii divreci wceq subreci caddc 3p2e5 eqcomi
      2ne0 3cn mvrraddi 5t2e10 mulcomli oveq12i wb 10re recni divcli a1i reccli
      10pos halfcn subexsub mptru oveq2i subdii oveq1i fveq2i mulcli coshalfpim
      mpbi ax-mp ) ACDEFGZHIZJGCDKLUAUBZFGZJGZUCIZJGBVRWBCJVRDCFGZWAMGZHIZWBVQW
      DHVQDLCFGZJGZWAMGZWDVQDLEFGZJGZWHDENOEUDUEUFZUGWJDWFVTMGZJGWHWIWLDJVTWFWI
      MGZUHZWIWLUHZWMVTWMECMGZCEJGZFGVTCEPOUMWKUIWPKWQVSFEKCUNPKCUJGEUKULUOECVS
      OPUPUQURQULWNWOUSRVTWIWFVTTSRKVSUNVSUTVAVSUTVEUFVBZVCWITSREOWKVDVCWFTSRVF
      VCVGVHVOVIDWFVTNVFWRVJQQWGWCWAMWCWGDCNPUMUGULVKQVLWATSWEWBUHDVTNWRVMWAVNV
      PQVIQ $.

    $( Golden ratio is positive.  (Contributed by Ender Ting, 16-Apr-2026.) $)
    goldrapos $p |- 0 < F $=
      ( cc0 c2 cpi c5 cdiv co clt 2re cr wcel pire 5re ax-mp wbr wtru crp a1i
      wb ccos cmul 5pos gt0ne0ii redivcli recoscl 2pos cneg cioo pipos divgt0ii
      cfv halfpire lt0neg2 mpbi neghalfpire 0re lttri 2lt5 2rp 5rp pirp ltdiv2d
      mp2an mptru neghalfpirx rexri elioo2 mpbir3an cosq14gt0 mulgt0ii breqtrri
      cxr w3a ) CDEFGHZUAULZUBHAIDVPJVOKLZVPKLEFMNFNUCUDUEZVOUFOUGVOEDGHZUHZVSU
      IHLZCVPIPWAVQVTVOIPZVOVSIPZVRVTCIPZCVOIPWBCVSIPZWDEDMJUJUGUKVSKLWEWDTUMVS
      UNOUOEFMNUJUCUKVTCVOUPUQVRURVDDFIPZWCUSWFWCTQDFEDRLQUTSFRLQVASERLQVBSVCVE
      UOVTVMLVSVMLWAVQWBWCVNTVFVSUMVGVTVSVOVHVDVIVOVJOVKBVL $.

    $( The golden ratio is a positive real.  (Contributed by Ender Ting,
       16-Apr-2026.) $)
    goldrarp $p |- F e. RR+ $=
      ( goldrarr goldrapos elrpii ) AABCABDE $.

    $( Lemma 1 for determining the value of golden ratio.  (Contributed by
       Ender Ting, 9-May-2026.) $)
    goldracos5teq $p |- ( cos ` _pi ) = ( ( ( ; 1 6 x. ( ( F / 2 ) ^ 5 ) ) -
       ( ; 2 0 x. ( ( F / 2 ) ^ 3 ) ) ) + ( 5 x. ( F / 2 ) ) ) $=
      ( cpi c5 cdiv co cc wcel cmul wceq c2 ccos cfv c1 c6 cdc cexp picn eqcomi
      5cn cc0 cmin caddc 5re 5pos gt0ne0ii divcli divcan2i 2cn coscl ax-mp 2ne0
      c3 mvllmuli cos5teq mp3an ) CDEFZGHZCDUQIFZJAKEFZUQLMZJCLMNOPUTDQFIFKUAPU
      TUMQFIFUBFDUTIFUCFJCDRTDUDUEUFZUGZUSCCDRTVBUHSVAUTKVAAUIURVAGHVCUQUJUKULA
      KVAIFBSUNSUQCUTUOUP $.

    $( Lemma 2 for determining the value of golden ratio.  (Contributed by
       Ender Ting, 9-May-2026.) $)
    goldratmolem2 $p |- -u 1 = ( ( ( ( F ^ 5 ) / 2 ) - ( 5 x. ( ( F ^ 3 ) / 2
       ) ) ) + ( 5 x. ( F / 2 ) ) ) $=
      ( c1 c2 cdiv co c5 cexp cmul cc0 c3 cc wcel wa wceq mp3an oveq2i 2cn 4cn
      c4 cpi ccos cfv c6 cdc cmin caddc cneg goldracos5teq cospi goldrarr recni
      wne cn0 2cnne0 5nn0 expdiv expcl mp2an 2ne0 5nn nnzi expne0i pm3.2i 16nn0
      cz nn0cni 1nn0 decnncl nnne0i divdiv2 mulcomi oveq1i divassi 3eqtrri exp1
      6nn ax-mp eqcomi ax-1cn 4p1e5 mvlladdi eqtri 4z expsub 3eqtri 3nn0 5t4e20
      2exp4 5cn 3z divcli mulassi 4ne0 4t2e8 cu2 divmuli mpbir oveq12i 3eqtr3i
      c8 ) UAUBUCCUDUEZADEFZGHFZIFZDJUEZXCKHFZIFZUFFZGXCIFZUGFCUHAGHFZDEFZGAKHF
      ZDEFZIFZUFFZXJUGFABUIUJXIXPXJUGXEXLXHXOUFXEXBXKDGHFZEFZIFZXKXQXBEFZEFZXLX
      DXRXBIALMZDLMZDJUMZNZGUNMZXDXROAABUKULZUOUPADGUQPQYAXKXBIFZXQEFZXBXKIFZXQ
      EFXSXKLMZXQLMZXQJUMZNXBLMZXBJUMZNYAYIOYBYFYKYGUPAGURUSZYLYMYCYFYLRUPDGURU
      SZYCYDGVFMZYMRUTGVAVBZDGVCPZVDYNYOXBVEVGZXBCUDVHVQVIVJVDXKXQXBVKPYHYJXQEX
      KXBYPUUAVLVMXBXKXQUUAYPYQYTVNVOXTDXKEDXTDDGTUFFZHFZXQDTHFZEFZXTDDCHFZUUCU
      UFDYCUUFDORDVPVRVSCUUBDHTCGSVTWAWBQWCYEYRTVFMZNUUCUUEOUOYRUUGYSWDVDDGTWEU
      SUUDXBXQEWIQWFVSQWFXHXFXMDKHFZEFZIFZGTUUIIFZIFZXOXGUUIXFIYBYEKUNMZXGUUIOY
      GUOWGADKUQPQUUJGTIFZUUIIFUULXFUUNUUIIUUNXFWHVSVMGTUUIWJSXMUUHYBUUMXMLMZYG
      WGAKURUSZYCUUMUUHLMZRWGDKURUSZYCYDKVFMUUHJUMZRUTWKDKVCPZWLWMWCUUKXNGIUUKX
      MUUHTEFZEFZXNUVBXMTIFZUUHEFZTXMIFZUUHEFUUKUUOUUQUUSNTLMZTJUMZNUVBUVDOUUPU
      UQUUSUURUUTVDUVFUVGSWNVDXMUUHTVKPUVCUVEUUHEXMTUUPSVLVMTXMUUHSUUPUURUUTVNV
      OUVADXMEUVADOTDIFZUUHOUVHXAUUHWOUUHXAWPVSWCUUHTDUURSRWNWQWRQWCQWFWSVMWT
      $.

    $( Lemma 3 for determining the value of golden ratio.  (Contributed by
       Ender Ting, 23-Jul-2026.) $)
    goldratmolem3 $p |- ( ( ( ( F ^ 5 ) - ( 5 x. ( F ^ 3 ) ) ) + ( 5 x. F ) )
        + 2 ) = 0 $=
      ( c5 co c3 cmul cmin caddc c2 cdiv 2cn cc wcel mp2an 2ne0 divcli divcan1i
      5cn mulcli eqtri cexp cc0 wceq cneg goldratmolem2 oveq1i mulm1i cn0 recni
      c1 goldrarr 5nn0 expcl 3nn0 subcli adddiri subdiri mulassi oveq2i oveq12i
      3eqtr3ri wb addcli addeq0 mpbir ) ACUADZCAEUADZFDZGDZCAFDZHDZIHDUBUCZVKIU
      DZUCZUJUDZIFDVFIJDZCVGIJDZFDZGDZCAIJDZFDZHDZIFDZVMVKVOWBIFABUEUFIKUGWCVSI
      FDZWAIFDZHDVKVSWAIVPVRVFIALMZCUHMVFLMAABUKUIZULACUMNZKOPZCVQRVGIWFEUHMVGL
      MWGUNAEUMNZKOPZSZUOCVTRAIWGKOPZSKUPWDVIWEVJHWDVPIFDZVRIFDZGDVIVPVRIWIWLKU
      QWNVFWOVHGVFIWHKOQWOCVQIFDZFDVHCVQIRWKKURWPVGCFVGIWJKOQUSTUTTWECVTIFDZFDV
      JCVTIRWMKURWQACFAIWGKOQUSTUTTVAVKLMILMVLVNVBVIVJVFVHWHCVGRWJSUOCARWGSVCKV
      KIVDNVE $.

    $( Lemma 4 for determining the value of golden ratio.  (Contributed by
       Ender Ting, 24-Jul-2026.) $)
    goldratmolem4 $p |- ( ( ( F ^ 2 ) - F ) - 1 ) = 0 $=
      ( c2 cexp co cmin c1 cmul cc0 wceq caddc goldrarr readdcli goldrapos 2pos
      2re wo c5 subcli mpbi addgt0ii gt0ne0ii neii goldpolyfactor goldratmolem3
      c3 recni eqtri sqcli ax-1cn mulcli 2cn addcli mul0ori orcom mtpor msq0i )
      ACDEZAFEZGFEZUTHEZIJZUTIJACKEZIJZVBVCIVCACABLZPMACVEPABNOUAUBUCVBVDQZVDVB
      QVAVCHEZIJVFVGARDERAUFDEHEFERAHEKECKEIAAVEUGZUDABUEUHVAVCUTUTUSGURAAVHUIV
      HSUJSZVIUKACVHULUMUNTVBVDUOTUPUTVIUQT $.

    $( Value of the golden ratio.  (Contributed by Ender Ting, 24-Jul-2026.) $)
    goldratval $p |- F = ( ( 1 + ( sqrt ` 5 ) ) / 2 ) $=
      ( c1 cneg c5 caddc co c2 cmul cdiv wceq cmin cc0 clt wbr 0re ax-1cn cc c4
      wtru csqrt cfv wn 1lt5 cle wb 0le1 5nn0 nn0ge0i 1re 5re sqrtlti negneg1e1
      mp2an mpbi sqrt1 eqtr4i sqrtpclii recni addridi 3brtr4i neg1rr ltsubadd2i
      5pos renegcli mpbir resubcli remulcli 2pos 2t1e2 breqtrri ltdiv1ii gtneii
      2re div0i breqtri redivcli ltnsymi ax-mp goldrapos breq2 cexp wo goldrarr
      mpbii mto sqcli addcli negsubi mullidi mulm1i oveq1i oveq12i wcel subsub4
      negdii mp3an 3eqtr4ri goldratmolem4 eqtr3i wne ax-1ne0 a1i neg1cn subnegi
      1cnd 4cn neg1sqe1 oveq2i mulneg2i mulridi negeqi df-5 comraddi quad mptru
      3eqtri ori mt3 eqtri ) ACDZDZEUAUBZFGZHCIGZJGZCYCFGZHJGAYFKZAYBYCLGZYEJGZ
      KZYKMYJNOZYJMNOYLUCYJMYEJGZMNYIMNOZYJYMNOYNYBYCMFGZNOCUAUBZYCYBYONCENOZYP
      YCNOZUDMCUEOMEUEOYQYRUFUGEUHUICEUJUKULUNUOYBCYPUMUPUQYCYCEUKVDURZUSUTVAYB
      YCMYAVBVEZYSPVCVFYIMYEYBYCYTYSVGZPHCVNUJVHZMHYENVIVJVKZVLUOYEYEUUBUSMYEPU
      UCVMZVOVPYJMYIYEUUAUUBUUDVQPVRVSYKMANOYLABVTAYJMNWAWEWFYHYKCAHWBGZIGZYAAI
      GZYAFGZFGZMKZYHYKWCZUUEALGCLGZUUIMUUEACFGZDZFGUUEUUMLGZUUIUULUUEUUMAAABWD
      USZWGZACUUPQWHWIUUFUUEUUHUUNFUUEUUQWJUUHADZYAFGUUNUUGUURYAFAUUPWKWLACUUPQ
      WPUQWMUUERWNARWNZCRWNUULUUOKUUQUUPQUUEACWOWQWRABWSWTUUJUUKUFTCYAYAEATXFCM
      XATXBXCYARWNTXDXCZUUTUUSTUUPXCEYAHWBGZSCYAIGZIGZLGZKTCSDZLGCSFGUVDECSQXGX
      EUVACUVCUVELXHUVCSYAIGSCIGZDUVEUVBYASIYAXDWJXISCXGQXJUVFSSXGXKXLXQWMESCXG
      QXMXNWRXCXOXPUOXRXSYDYGYEHJYBCYCFUMWLVJWMXT $.
  $}

  $( TODO: emil = ( x e. CC* , y e. CC* |-> ( exp* ` x ) - ( log* ` y ) )
     Exponent-Minus-Logarithm basis for elementary functions, courtesy Andrzej
     Odrzywolek's work at arXiv:2603.21852v2

     Infinity-safe restrictions:
     - RR: use ( RR u. (positive imaginary axis) )
     - CC: TODO: find
  $)

  ${
    $d x y $.
    lambert0.1 $e |- R = `' ( x e. CC |-> ( x x. ( exp ` x ) ) ) $.
    $( A value of Lambert W (product logarithm) function at zero.  (Contributed
       by Ender Ting, 13-Nov-2025.) $)
    lambert0 $p |- 0 R 0 $=
      ( vy cc0 wbr cc cv ce cfv cmul co wceq wa wtru wb c0ex adantr tbtru mpbir
      cmpt ccnv wcel copab eqcom biimpi eqeltrrd simpr c1 ax-1cn eqeltri mul02i
      0cnd ef0 fveq2d oveq12d eqtr3id eqtrd sylib eqid braba df-mpt breqi brcnv
      jca ) EEBFEEAGAHZVFIJZKLZUAZUBZFZVKEEVIFZVLEEVFGUCZDHZVHMZNZADUDZFZVRVROP
      VPOADEEVQQQVFEMZVNEMZNZVPVPOPWAVMVOVSVMVTVSEVFGVSEVFMVFEUEUFZVSUMUGRWAVNE
      VHVSVTUHVSEVHMVTVSEEEIJZKLVHWCWCUIGUNUJUKULVSEVFWCVGKWBVSEVFIWBUOUPUQRURV
      EVPSUSVQUTVAVRSTEEVIVQADGVHVBVCTEEVIQQVDTEEBVJCVCT $.
  $}

  ${
    $d x y $.
    lamberte.1 $e |- R = `' ( x e. CC |-> ( x x. ( exp ` x ) ) ) $.
    $( A value of Lambert W (product logarithm) function at ` _e ` .
       (Contributed by Ender Ting, 13-Nov-2025.) $)
    lamberte $p |- _e R 1 $=
      ( vy ceu c1 wbr cc cv ce cfv cmul co wceq wa wtru wb 1ex crp mpbir biimpi
      cmpt ccnv wcel copab epr elexi eqcom ax-1cn eqeltrrdi adantr simpr rpssre
      df-e ax-resscn sstri sselii eqeltrri mullidi eqtr4i oveq12d eqtr3id eqtrd
      cr fveq2d jca tbtru sylib eqid braba df-mpt breqi brcnv ) EFBGEFAHAIZVNJK
      ZLMZUBZUCZGZVSFEVQGZVTFEVNHUDZDIZVPNZOZADUEZGZWFWFPQWDPADFEWERESUFUGZVNFN
      ZWBENZOZWDWDPQWJWAWCWHWAWIWHVNFHWHFVNNVNFUHUAZUIUJUKWJWBEVPWHWIULWHEVPNWI
      WHEFFJKZLMZVPWMWLEWLEWLHUNSHESVDHUMUOUPUFUQURUSUNUTWHFVNWLVOLWKWHFVNJWKVE
      VAVBUKVCVFWDVGVHWEVIVJWFVGTFEVQWEADHVPVKVLTEFVQWGRVMTEFBVRCVLT $.
  $}

  $( Complex conjugation operator is not a polynomial with complex
     coefficients.  Indeed; if it was, then multiplying ` x ` conjugate by
     ` x ` itself and adding 1 would yield a nowhere-zero non-constant
     polynomial, contrary to the ~ fta .  (Contributed by Ender Ting,
     8-Dec-2025.) $)
  cjnpoly $p |- -. * e. ( Poly ` CC ) $=
    ( vx ccj cc cfv wcel c1 cidp cmul co caddc cc0 wceq cvv wfn wtru ax-mp cdgr
    cid cn ax-1cn cply cv csn cxp cof wrex cnex wa fconstmpt fnmpti cres fnresi
    1ex df-idp fneq1i mpbir a1i wf cjf ffn inidm offn mptru fnfvof mpanl12 mpan
    fvconst2 oveq1d fveq1i fvres eqtrid fvi oveq2d 3eqtrd 1red cjmulrcl clt wbr
    eqtrd 0lt1 cjmulge0 addgtge0d gt0ne0d eqnetrd neneqd nrex wss ssid plyconst
    mp2an plyid plymulcl plyaddcl sylancr c0p wne 1re cjre ax-1ne0 eqnetri ne0p
    3eqtri dgrid eqcomi eqid dgrmul mpan2 cn0 dgrcl nn0cn 1cnd addcomd eqeltrrd
    cr nn0p1nn syl eqeltrd nngt0d 0dgr dgradd2 mp3an2i fta syl2anc mto ) BCUADZ
    EZAUBZCFUCUDZGBHUEIZJUEIZDZKLZACUFZYLACYGCEZYKKYNYKFYGYGBDZHIZJIZKYNYKYGYHD
    ZYGYIDZJIZFYSJIYQCMEZYNYKYTLZUGYHCNYICNZUUAYNUHZUUBACFYHUMACFUIUJUUCOCCHCGB
    MMGCNZOUUERCUKZCNCULCGUUFUNUOUPZUQBCNZOCCBURUUHUSCCBUTPZUQUUAOUGUQZUUJCVAVB
    VCCJYHYIMYGVDVEVFYNYRFYSJCFYGUMVGVHYNYSYPFJYNYSYGGDZYOHIZYPUUAYNYSUULLZUGUU
    EUUHUUDUUMUUGUUICHGBMYGVDVEVFYNUUKYGYOHYNUUKYGRDZYGYNUUKYGUUFDUUNYGGUUFUNVI
    YGCRVJVKYGCVLVSVHVSVMVNYNYQYNFYPYNVOYGVPKFVQVRYNVTUQYGWAWBWCWDWEWFYFYJYEEZY
    JQDZSEYMYFYHYEEZYIYEEZUUOCCWGZFCEZUUQCWHZTFCWIWJZGYEEZYFUURUUSUUTUVCUVATCWK
    WJZCGBWLVFZCYHYIWMWNYFUUPYIQDZSUUQYFUURKUVFVQVRUUPUVFLUVBUVEYFUVFYFUVFFBQDZ
    JIZSYFBWOWPZUVFUVHLZUUTFBDZKWPUVITUVKFKFXNEUVKFLWQFWRPWSWTFBXAWJUVCGWOWPZYF
    UVIUHUVJUVDUUTFGDZKWPUVLTUVMFKUVMFUUFDZFRDZFFGUUFUNVIUUTUVNUVOLTFCRVJPFMEUV
    OFLUMFMVLPXBWSWTFGXAWJCGBFUVGGQDFXCXDUVGXEXFVEXGYFUVGXHEZUVHSECBXIUVPUVGFJI
    UVHSUVPUVGFUVGXJUVPXKXLUVGXOXMXPXQZXRCYHYIKUVFYHQDZKUUTUVRKLTFXSPXDUVFXEXTY
    AUVQXQACYJYBYCYD $.

  $( The tangent function is not a polynomial with complex coefficients, as it
     is not defined on the whole complex plane.  (Contributed by Ender Ting,
     10-Dec-2025.) $)
  tannpoly $p |- -. tan e. ( Poly ` CC ) $=
    ( vx ctan cc cply cfv wcel cpi c2 cdiv co cdm ccos ccnv cc0 cdif cosf ax-mp
    csn wf mto cima coshalfpi c0ex snid eqeltri eldifn wfun wb ffun picn halfcl
    mt2 fdmi eleqtrri fvimacnv mp2an mtbi cv csin df-tan dmmptss sseli wceq fdm
    plyf eleq2 mpbiri 3syl ) BCDEFZGHIJZBKZFZVLVJLMCNRZOZUAZFZVJLEZVNFZVPVRVQVM
    FVQNVMUBNUCUDUEVQCVMUFULLUGZVJLKZFVRVPUHCCLSVSPCCLUIQVJCVTGCFVJCFZUJGUKQZCC
    LPUMUNVJVNLUOUPUQVKVOVJAVOAURZUSEWCLEIJBAUTVAVBTVICCBSVKCVCZVLCBVECCBVDWDVL
    WAWBVKCVJVFVGVHT $.

  ${
    $d x y z t $.
    $( Sine function is not a polynomial with complex coefficients.  Indeed, it
       has infinitely many zeros but is not constant zero, contrary to ~ fta1 .
       (Contributed by Ender Ting, 10-Dec-2025.) $)
    sinnpoly $p |- -. sin e. ( Poly ` CC ) $=
      ( vz vx vy vt csin cc cfv wcel cn cfn cc0 cz cv cpi co c0p wa ax-mp wceq
      c4 cply nnnfi ccnv csn cima cmul cmpt wf1 cdgr cle wbr wne cr 4re resincl
      chash clt sin4lt0 cxp df-0p fveq1i 4cn c0ex fvconst2 eqtri breqtrri fveq1
      ltneii necon3i eqid fta1 mpan2 simpld wf wmo wal sinkpi snid eqeltrdi cdm
      wfun wb sinf ffun zcn picn mulcl sylancl eleqtrrdi fvimacnv sylancr mpbid
      fmpti vex eleq1w adantr eqeq1 oveq1 eqeq2d sylan9bbr anbi12d df-mpt braba
      fdmi mobii albii cdiv simpr oveq1d pine0 divcan4 mp3an23 syl eqtr2d moimi
      moeq mpgbir dff12 mpbir2an wss f1fi nnssz ssfi mto ) EFUAGHZIJHZUBYEEUCKU
      DZUEZJHZLYHALAMZNUFOZUGZUHZYFYEYIYHUPGEUIGUJUKZYEEPULZYIYNQTEGZTPGZULYOYP
      YQTUMHYPUMHUNTUORYPKYQUQURYQTFYGUSZGZKTPYRUTVATFHYSKSVBFKTVCVDRVEVFVHEPYP
      YQTEPVGVIRYHFEYHVJVKVLVMYMLYHYLVNBMZCMZYLUKZBVOZCVPZALYHYKYLYLVJYJLHZYKEG
      ZYGHZYKYHHZUUEUUFKYGYJVQKVCVRVSUUEEWAZYKEVTZHUUGUUHWBFFEVNUUIWCFFEWDRUUEY
      KFUUJUUEYJFHNFHZYKFHYJWEWFYJNWGWHFFEWCXDWIYKYGEWJWKWLWMUUDYTLHZUUAYTNUFOZ
      SZQZBVOZCUUCUUPCUUBUUOBUUEDMZYKSZQUUOADYTUUAYLBWNCWNYJYTSZUUQUUASZQUUEUUL
      UURUUNUUSUUEUULWBUUTABLWOWPUUTUURUUAYKSUUSUUNUUQUUAYKWQUUSYKUUMUUAYJYTNUF
      WRWSWTXAADLYKXBXCXEXFYTUUANXGOZSZBVOUUPBUVAXPUUOUVBBUUOUVAUUMNXGOZYTUUOUU
      AUUMNXGUULUUNXHXIUUOYTFHZUVCYTSZUULUVDUUNYTWEWPUVDUUKNKULUVEWFXJYTNXKXLXM
      XNXORXQBCLYHYLXRXSYIYMQLJHILXTYFLYHYLYAYBLIYCWHWHYD $.
  $}

  ${
    $d x y z $.

    $( Real square root is not a polynomial with real coefficients, because its
       value is imaginary for negative arguments.  (Contributed by Ender Ting,
       22-Jul-2026.) $)
    sqrtrrnpoly $p |- -. sqrt e. ( Poly ` RR ) $=
      ( csqrt cr cply cfv wcel cres wf c1 cneg neg1rr fvres ax-mp sqrtm1 eqcomi
      wceq ci inelr eqneltri ffvelcdm mto mpan2 plyreres ) ABCDEBBABFZGZUDHIZUC
      DZBEZUFUEADZBUEBEZUFUHOJUEBAKLUHPBPUHMNQRRUDUIUGJBBUEUCSUATAUBT $.

    $( Square root function is not polynomial with complex coefficients either.
       Otherwise, its composition with a square monomial - the identity - would
       have to be of even degree.  (Contributed by Ender Ting, 22-Jul-2026.) $)
    sqrtnpoly $p |- -. sqrt e. ( Poly ` CC ) $=
      ( vx vy csqrt cc cfv wcel c2 c1 cdvds wbr cdgr syl cexp cidp wceq cid cvv
      co wfn a1i cply n2dvds1 cmul cz dgrcl nn0zd 2z dvdsmul1 mpan cv cmpt ccom
      cres df-idp wa wss wral wb idfn wf ovex rgenw nfcv mpbi sqrtf fnfco mp2an
      mptfnf pm3.2i ssv fvreseq1 sqrtcl oveq1 fvmpt sqrtth eqtr2d fvco3 3eqtr4d
      eqid fvi mprgbir eqtr2i fveq2d cc0 wne cn0 ax-1cn 2nn0 sqcl mullid eqcomd
      ax-1ne0 mpteq2ia dgr1term mp3an eqcomi ssid plypow id dgrco dgrid 3eqtr3d
      breqtrd mto ) CDUAEZFZGHIJUBXFGGCKEZUCRZHIXFXGUDFZGXHIJZXFXGDCUEUFGUDFXIX
      JUGGXGUHUILXFADAUJZGMRZUKZCULZKENKEZXHHXFXNNKXNNOXFNPDUMZXNUNXPXNOZBUJZPE
      ZXRXNEZOZBDPQSZXNDSZUODQUPXQYABDUQURYBYCUSXMDSZDDCUTZYCXLQFZADUQYDYFADXKG
      MVAVBADXLADVCVHVDVEDDXMCVFVGVIDVJBQDPXNVKVGXRDFZXRXRCEZXMEZXSXTYGYIYHGMRZ
      XRYGYHDFYIYJOXRVLAYHXLYJDXMXKYHGMVMXMVSYHGMVAVNLXRVOVPXRDVTYEYGXTYIOVEDDX
      RXMCVQUIVRWAWBTWCXFDXMCGXGXMKEZGHDFZHWDWEGWFFZYKGOWGWLWHAHXMGADXLHXLUCRZX
      KDFXLDFZXLYNOXKWIYOYNXLXLWJWKLWMWNWOWPXGVSXMXEFZXFDDUPYLYMYPDWQWGWHADGWRW
      OTXFWSWTXOHOXFXATXBXCXD $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Turing Machine Finite Reach theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d U a b i y z $.  $d I a b i y z $.  $d ph a b i y z $.  $d S a b i y z $.
    $d A a b i y z $.  $d T a b i y z $.
    tmach.finalph $e |- ( ph -> U e. Fin ) $.
    tmach.exindex $e |- ( ph -> I e. _V ) $.
    tmach.tapelist $e |- ( ph -> T = ( U ^m I ) ) $.
    tmach.scanmap $e |- ( ph -> S : T --> ( ~P I i^i Fin ) ) $.
    tmach.agreemap $e |- ( ph -> A = ( z e. T |-> { y e. T | ( y |` ( S ` z ) )
      = ( z |` ( S ` z ) ) } ) ) $.
    tmach.agreement $e |- ( ph -> A. z e. T A. y e. ( A ` z ) ( S ` y )
      = ( S ` z ) ) $.
    $( The class of all tapes is a set.  (Contributed by Ender Ting,
       27-Jul-2026.) $)
    tmachlem-extapes $p |- ( ph -> T e. _V ) $=
      ( cmap co cvv ovex eqeltrdi ) AFGHOPQKGHORS $.

    $( Execution on any tape only scanned a finite number of cells.
       (Contributed by Ender Ting, 27-Jul-2026.) $)
    tmachlem-finscan $p |- ( ( ph /\ a e. T ) -> ( S ` a ) e. Fin ) $=
      ( cv wcel wa cpw cfn cfv cin ffvelcdmda elin2d ) AIPZFQRHSZTUEEUAAFUFTUBU
      EEMUCUD $.

    $( Any tape belongs to its own agreement set.  (Contributed by Ender Ting,
       27-Jul-2026.) $)
    tmachlem-agreeself $p |- ( ( ph /\ a e. T ) -> a e. ( A ` a ) ) $=
      ( cv cfv cres wceq cvv wcel wa crab wtru wb reseq1 tbtru sylib simpr trud
      weq elrabd fveq2 reseq2d reseq12d eqeq12d rabbidv adantr tmachlem-extapes
      id cmpt wss ssrab2 a1i ssexd fvmptd4 eleqtrrd ) AIPZFUAZUBZVHBPZVHEQZRZVH
      VLRZSZBFUCZVHDQVJVOUDBVHFBIUKVOVOUDUEVKVHVLUFVOUGUHAVIUIZVJUJULVJCVHVKCPZ
      EQZRZVRVSRZSZBFUCZVPFDTCIUKZWBVOBFWDVTVMWAVNWDVSVLVKVRVHEUMZUNWDVRVHVSVLW
      DUTWEUOUPUQADCFWCVASVINURVQAVPTUAVIAVPFTABCDEFGHJKLMNOUSVPFVBAVOBFVCVDVEU
      RVFVG $.

    $( Agreement set can be written as infinite product of acceptable values
       for tape's cells.  (Contributed by Ender Ting, 27-Jul-2026.) $)
    tmachlem-agreeprod $p |- ( ( ph /\ a e. T ) -> ( A ` a ) = X_ i e. I
      if ( i e. ( S ` a ) , { ( a ` i ) } , U ) ) $=
      ( wcel wa adantr cfn cv cfv cres wceq crab csn cif cixp cvv fveq2 reseq2d
      weq reseq12d eqeq12d rabbidv cmpt simpr tmachlem-extapes wss ssrab2 ssexd
      id a1i fvmptd4 cmap ciun wral snfi ad2antrr ifcld ralrimiva ixpssmapg syl
      co cun ifssun wf eleq2d biimpd imp elmapi ffvelcdmda snssd sylib sseqtrid
      ssequn1 iunssd mapss syl2an2r sstrd sseqtrrd wfn wi wb simplr fvex sylibr
      mpd elsn iftrued eleqtrrd a1dd cpw cin elin1d elpwid sselda eleqtrd elsnd
      ex impbid wn iffalsed pm2.21d pm2.61dan ralbidv2 elmapfn biantrurd bitr2d
      a1d adantlr vex elixp fvreseq syl21anc 3bitr4d eqrrabd eqtr4d ) AJUAZFQZR
      ZYIDUBBUAZYIEUBZUCZYIYMUCZUDZBFUEZHIHUAZYMQZYRYIUBZUFZGUGZUHZYKCYIYLCUAZE
      UBZUCZUUDUUEUCZUDZBFUEZYQFDUICJULZUUHYPBFUUJUUFYNUUGYOUUJUUEYMYLUUDYIEUJZ
      UKUUJUUDYIUUEYMUUJVBUUKUMUNUOADCFUUIUPUDYJOSAYJUQYKYQFUIAFUIQYJABCDEFGIKL
      MNOPURSYQFUSYKYPBFUTVCVAVDYKYPBFUUCYKUUCGIVEVNZFYKUUCHIUUBVFZIVEVNZUULYKU
      UBTQZHIVGUUCUUNUSYKUUOHIYKYRIQZRZYSUUAGTUUATQUUQYTVHVCAGTQZYJUUPKVIVJVKHI
      UUBTVLVMAUURYJUUMGUSUUNUULUSKYKHIUUBGUUQUUAGVOZUUBGYSUUAGVPUUQUUAGUSUUSGU
      DUUQYTGYKIGYRYIYKYIUULQZIGYIVQAYJUUTAYJUUTAFUULYIMVRVSVTZYIGIWAVMWBWCUUAG
      WFWDWEWGUUMGITWHWIWJAFUULUDYJMSWKYKYLFQZRZYLIWLZYRYLUBZUUBQZHIVGZRZUVEYTU
      DZHYMVGZYLUUCQZYPUVCUVJUVGUVHUVCUVIUVFHYMIUVCYSYSUVIWMZUUPUVFWMZWNUVCYSRZ
      UVLUVMUVNUVLUVFUUPUVNUVLUVFUVNUVLRZUVEUUAUUBUVOUVIUVEUUAQUVOYSUVIUVCYSUVL
      WOZUVNUVLUQWRUVEYTYRYLWPWSWQUVOYSUUAGUVPWTXAXJXBUVNUVMUVIYSUVNUVMUVIUVNUV
      MRZUVEYTUVQUVEUUBUUAUVQUUPUVFUVNUUPUVMUVCYMIYRYKYMIUSZUVBYKYMIYKIXCZTYMAF
      UVSTXDYIENWBXEXFSZXGSUVNUVMUQWRUVQYSUUAGUVCYSUVMWOWTXHXIXJXBXKUVCYSXLZRZU
      VLUVMUWBUVMUVLUWBUUPUVFUWBUUPRZUVEGUUBUWBIGYRYLUVCIGYLVQZUWAUVCYLUULQZUWD
      YKUVBUWEAUVBUWEWMYJAUVBUWEAFUULYLMVRVSZSVTYLGIWAVMSWBUWCYSUUAGUVCUWAUUPWO
      XMXAXJXTUWBUVMUVLUWBUVMRYSUVIUVCUWAUVMWOXNXJXKXOXPUVCUVDUVGAUVBUVDYJAUVBR
      UWEUVDAUVBUWEUWFVTYLGIXQVMYAZXRXSUVKUVHWNUVCHIUUBYLBYBYCVCUVCUVDYIIWLZUVR
      YPUVJWNUWGYKUWHUVBYKUUTUWHUVAYIGIXQVMSUVTHIYMYLYIYDYEYFYGYH $.

    $( Product (discrete) topology of tapes is compact by Tychonoff's theorem.
       To work for infinite index sets (such as ` ZZ ` for ` I ` which is the
       main interpretation), it requires Choice.  (Contributed by Ender Ting,
       27-Jul-2026.) $)
    tmachlem-tpcomp $p |- ( ph -> ( Xt_ ` ( i e. I |-> ~P U ) ) e. Comp ) $=
      ( cvv wcel ccmp cpw cmpt wf cpt cfv cv discmp sylib adantr fmpttd syl2anc
      cfn ptcmp ) AIPQIRHIGSZTZUAUMUBUCRQKAHIULRAULRQZHUDIQAGUJQUNJGUEUFUGUHIUM
      PUKUI $.

    $( The base set of product topology of tapes is the set of tapes.
       (Contributed by Ender Ting, 28-Jul-2026.) $)
    tmachlem-tpbase $p |- ( ph -> U. ( Xt_ ` ( i e. I |-> ~P U ) ) = T ) $=
      ( cvv wcel wceq cfn cmap cpw cuni cixp cmpt cpt cfv ctop distop ralrimivw
      wral syl eqid ptunimpt syl2anc unipw a1i oveq1d eqeltrd ixpconstg 3eqtr4d
      co eqtr3d ) AHIGUAZUBZUCZHIVCUDUEUFZUBZFAIPQZVCUGQZHIUJVEVGRKAVIHIAGSQVIJ
      GSUHUKUIHIVFVCPVFULUMUNAVDITVAZGITVAVEFAVDGITVDGRAGUOUPZUQAVHVDSQVEVJRKAV
      DGSVKJURHIVDPSUSUNLUTVB $.

    $( Topology lemma.  (Contributed by Ender Ting, 27-Jul-2026.) $)
    tmachlem-tpitem $p |- ( ( ph /\ a e. I ) -> ( ( i e. I |-> ~P U ) ` a )
      = ~P U ) $=
      ( cv wcel wa cvv cpw cmpt eqid weq eqidd simpr cfn pwexd adantr fvmptd3 )
      AJQZIRZSHUKGUAZUMIHIUMUBZTUNUCHJUDUMUEAULUFAUMTRULAGUGKUHUIUJ $.

    $( Agreement sets are open in the product topology of tapes.  (Contributed
       by Ender Ting, 27-Jul-2026.) $)
    tmachlem-tpopen $p |- ( ( ph /\ a e. T ) -> X_ b e. I if ( b e. ( S ` a ) ,
      { ( a ` b ) } , U ) e. ( Xt_ ` ( i e. I |-> ~P U ) ) ) $=
      ( cv wcel wa cfv csn cif cpw cmpt cvv adantr ctop distop tmachlem-finscan
      cfn syl fmpttd co wf eleq2d biimpa elmapi ffvelcdmda snelpwi simpll pwidg
      cmap 3syl ifcld wceq tmachlem-tpitem adantlr eleqtrrd cdif cuni wn eldifn
      adantl iffalsed eldifi syl2anc unieqd unipw eqtrdi eqtr4d ptopn ) AJRZFSZ
      TZIKRZWCEUAZSZWFWCUAZUBZGUCZKHIGUDZUEZUFWGAIUFSWDMUGWEHIWLUHWEWLUHSZHRISA
      WNWDAGUKSZWNLGUKUIULUGUGUMABCDEFGIJLMNOPQUJWEWFISZTZWKWLWFWMUAZWQWHWJGWLW
      QWIGSWJWLSWEIGWFWCWEWCGIVCUNZSZIGWCUOAWDWTAFWSWCNUPUQWCGIURULUSWIGUTULWQA
      WOGWLSAWDWPVALGUKVBVDVEAWPWRWLVFZWDABCDEFGHIKLMNOPQVGZVHVIWEWFIWGVJSZTZWK
      GWRVKZXDWHWJGXCWHVLWEWFIWGVMVNVOXDXEWLVKGXDWRWLXDAWPXAAWDXCVAXCWPWEWFIWGV
      PVNXBVQVRGVSVTWAWB $.

    $( Variable-renaming lemma connecting ~ tmachlem-agreeprod and
       ~ tmachlem-tpopen .  (Contributed by Ender Ting, 27-Jul-2026.) $)
    tmachlem-tpopen2 $p |- ( ( ph /\ a e. T ) -> ( A ` a ) e. ( Xt_ `
      ( b e. I |-> ~P U ) ) ) $=
      ( vi cv wcel cfv csn cif cixp cpw cmpt tmachlem-agreeprod tmachlem-tpopen
      wa cpt eqeltrd ) AIRZFSUHUKDTQHQRZUKETSULUKTUAGUBUCJHGUDUEUITABCDEFGQHIKL
      MNOPUFABCDEFGJHIQKLMNOPUGUJ $.

    $( Union of all agreement sets only includes tapes.  (Contributed by Ender
       Ting, 28-Jul-2026.) $)
    tmachlem-uassst $p |- ( ph -> U. ran A C_ T ) $=
      ( crn cuni cv cres cvv wcel cfv wceq crab ciun cmpt wral tmachlem-extapes
      rneqd unieqd wa adantr wss ssrab2 a1i ralrimiva dfiun3g syl eqtr4d iunssd
      ssexd eqsstrd ) ADOZPZCFBQCQZEUAZRVDVERUBZBFUCZUDZFAVCCFVGUEZOZPZVHAVBVJA
      DVIMUHUIAVGSTZCFUFVHVKUBAVLCFAVDFTZUJZVGFSAFSTVMABCDEFGHIJKLMNUGUKVGFULVN
      VFBFUMUNZUTUOCFVGSUPUQURACFVGFVOUSVA $.

    $( Product topology of tapes has an open cover.  (Contributed by Ender
       Ting, 28-Jul-2026.) $)
    tmachlem-exlargecover $p |- ( ph -> U. ran A = T ) $=
      ( va crn cuni tmachlem-uassst cv wcel wa cfv tmachlem-agreeself elfvunirn
      syl eqelssd ) AODPQZFABCDEFGHIJKLMNRAOSZFTUAUHUHDUBTUHUGTABCDEFGHOIJKLMNU
      CUHUHDUDUEUF $.

    $( Product topology of tapes admits finite cover.  (Contributed by Ender
       Ting, 28-Jul-2026.) $)
    tmachlem-extpcover $p |- ( ph -> E. a e. ( ~P ran A i^i Fin ) U. ( Xt_ `
      ( i e. I |-> ~P U ) ) = U. a ) $=
      ( vb cfv wcel cv cpw cmpt cpt ccmp crn wss cuni wceq wrex tmachlem-tpcomp
      cfn cin wfn wral cres crab cvv tmachlem-extapes ssrab2 a1i ralrimivw nfcv
      ssexd mptfnf sylib fneq1d mpbird tmachlem-tpopen2 syl2anc tmachlem-tpbase
      ralrimiva fnfvrnss tmachlem-exlargecover eqtr4d eqid cmpcov syl3anc ) AHI
      GUAUBUCRZUDSDUEZVRUFZVRUGZVSUGZUHWAJTUGUHJVSUAUKULUIABCDEFGHIKLMNOPUJADFU
      MZQTDRVRSZQFUNVTAWCCFBTCTZERZUOWEWFUOUHZBFUPZUBZFUMZAWHUQSZCFUNWJAWKCFAWH
      FUQABCDEFGIKLMNOPURWHFUFAWGBFUSUTVCVACFWHCFVBVDVEAFDWIOVFVGAWDQFABCDEFGIQ
      HKLMNOPVHVKQFVRDVLVIAWAFWBABCDEFGHIKLMNOPVJABCDEFGIKLMNOPVMVNVSVRWAJWAVOV
      PVQ $.

    $( Particular properties of the finite cover of agreesets.  (Contributed by
       Ender Ting, 28-Jul-2026.) $)
    tmachlem-exagreecover $p |- ( ph -> E. a ( a C_ ran A /\ a e. Fin /\
      T = U. a ) ) $=
      ( vi cpw cfn wcel wceq cv crn cin cmpt cpt cfv cuni wa tmachlem-extpcover
      wex wss w3a wrex df-rex sylib simprl elin1d elpwid elin2d tmachlem-tpbase
      adantr simprr eqtr3d 3jca ex eximdv mpd ) AIUAZDUBZQZRUCZSZPHGQUDUEUFUGZV
      HUGZTZUHZIUJZVHVIUKZVHRSZFVNTZULZIUJAVOIVKUMVQABCDEFGPHIJKLMNOUIVOIVKUNUO
      AVPWAIAVPWAAVPUHZVRVSVTWBVHVIWBVJRVHAVLVOUPZUQURWBVJRVHWCUSWBVMFVNAVMFTVP
      ABCDEFGPHJKLMNOUTVAAVLVOVBVCVDVEVFVG $.

    $( Scans for all tapes of a single agreement set are identical.
       (Contributed by Ender Ting, 28-Jul-2026.) $)
    tmachlem-agreesn $p |- ( ( ph /\ a e. T ) -> ( S " ( A ` a ) )
      = { ( S ` a ) } ) $=
      ( cv wcel wa cfv wral cima csn nfv wfun cpw cfn cin ffund adantr wceq weq
      fveq2 eqeq2d cbvralvw sylib r19.21bi fvex elsn2 sylibr tmachlem-agreeself
      raleqbidv funimassd cdm wi fdmd eleq2d biimpar funfvima syl2anc mpd snssd
      eqssd ) AIPZFQZRZEVMDSZUAZVMESZUBZVOBVPVSEVOBUCAEUDZVNAFHUEUFUGZEMUHUIZVO
      BPZVPQRWCESZVRUJZWDVSQVOWEBVPAWEBVPTZIFAWDCPZESZUJZBWGDSZTZCFTWFIFTOWKWFC
      IFCIUKZWIWEBWJVPWGVMDULWLWHVRWDWGVMEULUMVAUNUOUPUPWDVRVMEUQURUSVBVOVRVQVO
      VMVPQZVRVQQZABCDEFGHIJKLMNOUTVOVTVMEVCZQZWMWNVDWBAWPVNAWOFVMAFWAEMVEVFVGV
      PVMEVHVIVJVKVL $.

    $( Any agreement set has a finite (singleton) list of possible scans.
       (Contributed by Ender Ting, 28-Jul-2026.) $)
    tmachlem-agreefin $p |- ( ( ph /\ b e. ran A ) -> ( S " b ) e. Fin ) $=
      ( va cv wcel wa wceq crn cfv cima cfn cdm wrex wfun cres crab cmpt funmpt
      wi funeqd mpbiri elrnrexdm syl imp csn simprr imaeq2d simpll simprl dmeqd
      cvv tmachlem-extapes wss ssrab2 a1i ssexd ralrimivw dmmptg eqtrd ad2antrr
      wral eleqtrd tmachlem-agreesn syl2anc snfi eqeltrdi rexlimddv ) AIQZDUARZ
      SZWAPQZDUBZTZEWAUCZUDRPDUEZAWBWFPWHUFZADUGZWBWIULAWJCFBQCQZEUBZUHWKWLUHTZ
      BFUIZUJZUGCFWNUKADWONUMUNPDWAUOUPUQWCWDWHRZWFSZSZWGWDEUBZURZUDWRWGEWEUCZW
      TWRWAWEEWCWPWFUSUTWRAWDFRXAWTTAWBWQVAWRWDWHFWCWPWFVBAWHFTWBWQAWHWOUEZFADW
      ONVCAWNVDRZCFVNXBFTAXCCFAWNFVDABCDEFGHJKLMNOVEWNFVFAWMBFVGVHVIVJCFWNVDVKU
      PVLVMVOABCDEFGHPJKLMNOVPVQVLWSVRVSVT $.

    $( There is a finite number of different scan sets.  (Contributed by Ender
       Ting, 28-Jul-2026.) $)
    tmachlem-franscan $p |- ( ph -> ran S e. Fin ) $=
      ( va vi cima crn cfn wcel wfn wceq cpw cin ffnd fnima syl cv wss cuni w3a
      tmachlem-exagreecover ciun simpr3 imaeq2d imauni eqtrdi simpr2 wel simpll
      wa simplr1 simpr sseldd tmachlem-agreefin syl2anc ralrimiva iunfi eqeltrd
      wral exlimddv eqeltrrd ) AEFQZERZSAEFUAVMVNUBAFHUCSUDELUEFEUFUGAOUHZDRZUI
      ZVOSTZFVOUJZUBZUKZVMSTOABCDEFGHOIJKLMNULAWAVAZVMPVOEPUHZQZUMZSWBVMEVSQWEW
      BFVSEAVQVRVTUNUOPEVOUPUQWBVRWDSTZPVOVJWESTAVQVRVTURWBWFPVOWBPOUSZVAZAWCVP
      TWFAWAWGUTWHVOVPWCVQVRVTAWGVBWBWGVCVDABCDEFGHPIJKLMNVEVFVGPVOWDVHVFVIVKVL
      $.

    $( Any scan set is finite.  (Contributed by Ender Ting, 28-Jul-2026.) $)
    tmachlem-fssscan $p |- ( ph -> ran S C_ Fin ) $=
      ( crn cpw cfn cin frnd inss2 sstrdi ) AEOHPZQRZQAFUCELSUBQTUA $.

    $( Folk theorem.  For any algorithm deterministically processing a stream
       of data (essentially, an infinite tape with cell indices ` I ` and
       finite alphabet ` U ` ), if it terminates on every possible input, then
       it never looks beyond a finite portion ` U. ran S ` of the input.

       Termination is expressed here with a weaker condition: that an execution
       may only look at a finite number of cells.  Obviously, a program which
       finishes in a finite number of steps can only scan finite set of cells.

       This theorem has many corollaries, such as: any encoding scheme able to
       represent all integers has at least one non-decodable tape (in other
       terms, encoding of the infinity).

       I no longer have the source for this theorem but I believe I first read
       about it on LessWrong.  My gratitude to Grok for suggesting that this
       theorem will require Axiom of Choice, and to DeepSeek for suggesting the
       topology-based proof route.  (Contributed by Ender Ting,
       28-Jul-2026.) $)
    tmachfullfin $p |- ( ph -> U. ran S e. Fin ) $=
      ( crn cfn wcel wss cuni tmachlem-franscan tmachlem-fssscan unifi syl2anc
      ) AEOZPQUDPRUDSPQABCDEFGHIJKLMNTABCDEFGHIJKLMNUAUDUBUC $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Scratchpad for probability theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $(
    This theorem will show that a given distribution in RR may be satisfied by
    a relatively short sequence of value transfers.
    ${
      paysd.1 $e |- ( ph -> A e. Fin ) $.
      paysd.2 $e |- ( ph -> B : A --> RR ) $.
      paysd.3 $e |- ( ph -> sum_ k e. A ( B ` k ) = 0 ) $.
      paysd.4 $e |- ( ph -> C = (/) ) $.
      paysd $p |- ( ph -> ( C e. Word ( ( A X. A ) X. RR ) /\ ( # ` C ) <_ ( #
        ` A ) ) ) $= ( cxp cr cword wcel chash cfv cle wbr c0 wrd0 a1i eqeltrd
        cc0 wceq fveq2 hash0 eqtrdi syl cfn cn0 hashcl nn0ge0d eqbrtrd jca )
        ACBBFGFZHZICJZKZBULKZLZMACNZUKEUPUKIAUJOPQAUMRZUNU
        OACUPSZUMUQSEURUMUPULKUQCUPULTUAUBUCAUNABUDIUNUEID BUFUCUGUHUI $.
    $}
  $)

$( (End of Ender Ting's mathbox.) $)
