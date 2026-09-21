$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Matthew House
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Relations on well-ordered indexed unions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d ph t $.  $d A m n o p q r s t u v w x $.  $d A x y z $.
    $d B m n o p q r s t u v w $.  $d B y z $.  $d C y z $.  $d D y z $.
    $d E n o s t $.  $d F m n o p q r s t y z $.  $d R m n o p q r s t u v w $.
    $d R y z $.  $d S m n o p q r s t y z $.  $d T n o p q r $.  $d V p q t $.
    weiun.1 $e |- F = ( w e. U_ x e. A B |-> ( iota_ u e. { x e. A | w e. B }
        A. v e. { x e. A | w e. B } -. v R u ) ) $.
    weiun.2 $e |- T = { <. y , z >. | ( ( y e. U_ x e. A B /\
        z e. U_ x e. A B ) /\ ( ( F ` y ) R ( F ` z ) \/
        ( ( F ` y ) = ( F ` z ) /\ y [_ ( F ` y ) / x ]_ S z ) ) ) } $.
    $( Value of the relation constructed in ~ weiunpo , ~ weiunso , ~ weiunfr ,
       and ~ weiunse .  (Contributed by Matthew House, 8-Sep-2025.) $)
    weiunval $p |- ( C T D <-> ( ( C e. U_ x e. A B /\
        D e. U_ x e. A B ) /\ ( ( F ` C ) R ( F ` D ) \/
        ( ( F ` C ) = ( F ` D ) /\ C [_ ( F ` C ) / x ]_ S D ) ) ) ) $=
      ( cfv wbr wceq wa cv csb ciun simpl fveq2d simpr breq12d eqeq12d breq123d
      wo csbeq1d anbi12d orbi12d brab2a ) BUAZNQZCUAZNQZKRZUPURSZUOUQAUPLUBZRZT
      ZUJINQZJNQZKRZVDVESZIJAVDLUBZRZTZUJBCIJAGHUCZVKMUOISZUQJSZTZUSVFVCVJVNUPV
      DURVEKVNUOINVLVMUDZUEZVNUQJNVLVMUFZUEZUGVNUTVGVBVIVNUPVDURVEVPVRUHVNUOIUQ
      JVAVHVOVNAUPVDLVPUKVQUIULUMPUN $.

    ${
      weiunlem.3 $e |- ( ph -> R We A ) $.
      weiunlem.4 $e |- ( ph -> R Se A ) $.
      $( Lemma for ~ weiunpo , ~ weiunso , ~ weiunfr , and ~ weiunse .
         (Contributed by Matthew House, 23-Aug-2025.) $)
      weiunlem $p |- ( ph -> ( F : U_ x e. A B --> A /\
          A. t e. U_ x e. A B t e. [_ ( F ` t ) / x ]_ B /\
          A. s e. A A. t e. [_ s / x ]_ B -. s R ( F ` t ) ) ) $=
        ( vr wwe wse ciun wf cv cfv csb wcel wral wbr w3a wfn crab crio riotaex
        wn wa fnmpti a1i wceq weq breq2 notbid ralbidv cbvriotavw rabbidv breq1
        eleq1w cbvralvw raleqdv bitrid riotaeqbidv eqtrid fvmpt3i adantl c0 wne
        wreu wrex eliun rabn0 bitr4i wss ssrab2 wereu2 sylan2b riotacl2 eqeltrd
        mpanr1 elrabi 3syl ralrimiva ffnfv sylanbrc wsbc dfsbcq elrabsf simprbi
        nfcv vtoclga sbcel2 sylib anbi2i bitri bilanri ne0d sylibr elrab syldan
        syl rsp sylc ralrimivva 3jca syl2anc ) AIKUAZIKUBZBIJUCZINUDZHUEZBXTNUF
        ZJUGUHZHXRUIZOUEZYAKUJZUPZHBYDJUGZUIOIUIZUKRSXPXQUQZXSYCYHYINXRULZYAIUH
        ZHXRUIXSYJYIEXRFUEZGUEZKUJZUPZFEUEJUHZBIUMZUIZGYQUNZNYRGYQUOZPURUSYIYKH
        XRYIXTXRUHZUQZYAYDTUEZKUJZUPZOXTJUHZBIUMZUIZTUUGUMZUHZYAUUGUHZYKUUBYAUU
        HTUUGUNZUUIUUAYAUULUTYIEXTYSUULXRNEHVAZYSYLUUCKUJZUPZFYQUIZTYQUNUULYRUU
        PGTYQGTVAZYOUUOFYQUUQYNUUNYMUUCYLKVBVCVDVEUUMUUPUUHTYQUUGUUMYPUUFBIEHJV
        HVFZUUPUUEOYQUIUUMUUHUUOUUEFOYQFOVAUUNUUDYLYDUUCKVGVCVIUUMUUEOYQUUGUURV
        JVKVLVMPYTVNVOUUBUUHTUUGVRZUULUUIUHUUAYIUUGVPVQZUUSUUAUUFBIVSUUTBXTIJVT
        UUFBIWAWBZYIUUGIWCUUTUUSUUFBIWDTOIUUGKWEWIWFUUHTUUGWGXJWHZUUHTYAUUGWJZU
        UFBYAIWJWKWLHXRINWMWNYIYBHXRUUBUUFBYAWOZYBUUBUUJUUKUVDUVBUVCUUFBYDWOZUV
        DOYAUUGUUFBYDYAWPYDUUGUHZYDIUHZUVEUUFBYDIBIWSWQZWRWTWKBYAXTJXAXBWLYIYFO
        HIYGYIUVGXTYGUHZUQZUQZYFOUUGUIZUVFYFYIUVJUUAUVLUVKUUTUUAUVKUUGYDUVFUVJY
        IUVFUVGUVEUQUVJUVHUVEUVIUVGBYDXTJXAXCXDXEZXFUVAXGUUBUUJUVLUVBUUJUUKUVLU
        UHUVLTYAUUGUUCYAUTZUUEYFOUUGUVNUUDYEUUCYAYDKVBVCVDXHWRXJXIUVMYFOUUGXKXL
        XMXNXO $.

      weiunfrlem.5 $e |- E =
          ( iota_ p e. ( F " r ) A. q e. ( F " r ) -. q R p ) $.
      weiunfrlem.6 $e |- ( ph -> r C_ U_ x e. A B ) $.
      weiunfrlem.7 $e |- ( ph -> r =/= (/) ) $.
      $( Lemma for ~ weiunfr .  (Contributed by Matthew House, 23-Aug-2025.) $)
      weiunfrlem $p |- ( ph -> ( E e. ( F " r ) /\ A. t e. r -. ( F ` t ) R E
          /\ A. t e. ( r i^i [_ E / x ]_ B ) ( F ` t ) = E ) ) $=
        ( vo vn vs cv cima wcel cfv wbr wn wral wceq csb cin crab crio wreu wwe
        wa wse wss c0 wne ciun wf weiunlem simp1d fimassd fdmd sseqtrrd sseqin2
        cdm sylib eqnetrd imadisjlnd wereu2 syl22anc riotacl2 syl simpr breq12d
        weq simpl notbid cbvraldva cbvrabv 3eltr4g breq2 elrab simpld simprd wb
        ralbidv wfn ffnd breq1 ralima syl2anc mpbid elin1d rspa syl2an2r csbeq1
        wel raleqbidv simp3d sseldd rspcdva elin2d wor adantr sotrieq2 syl12anc
        weso ffvelcdmd mpbir2and ralrimiva 3jca ) ANOPUIZUJZUKZHUIZOULZNKUMZUNZ
        HYCUOZYGNUPZHYCBNJUQZURZUOAYEUFUIZNKUMZUNZUFYDUOZANYNUGUIZKUMZUNZUFYDUO
        ZUGYDUSZUKYEYQVCAQUIZRUIZKUMZUNZQYDUOZRYDUTZUUGRYDUSZNUUBAUUGRYDVAZUUHU
        UIUKAIKVBZIKVDYDIVEYDVFVGUUJUAUBABIJVHZIOYCAUULIOVIZYFBYGJUQUKHUULUOZUH
        UIZYGKUMZUNZHBUUOJUQZUOZUHIUOZABCDEFGHIJKLMOUHSTUAUBVJZVKZVLZAOYCAOVPZY
        CURZYCVFAYCUVDVEUVEYCUPAYCUULUVDUDAUULIOUVBVMVNYCUVDVOVQUEVRVSRQIYDKVTW
        AUUGRYDWBWCUCUUAUUGUGRYDUGRWFZYTUUFUFQYDUVFUFQWFZVCZYSUUEUVHYNUUCYRUUDK
        UVFUVGWDUVFUVGWGWEWHWIWJWKUUAYQUGNYDYRNUPZYTYPUFYDUVIYSYOYRNYNKWLWHWQWM
        VQZWNZAYQYJAYEYQUVJWOAOUULWRYCUULVEZYQYJWPAUULIOUVBWSUDYPYIUFHUULYCOYNY
        GUPYOYHYNYGNKWTWHXAXBXCZAYKHYMAYFYMUKZVCZYKYINYGKUMZUNZAYJUVNHPXHYIUVMU
        VOYCYLYFAUVNWDZXDZYIHYCXEXFAUVQHYLUOZUVNYFYLUKUVQAUUSUVTUHINUUONUPZUUQU
        VQHUURYLBUUONJXGUWAUUPUVPUUONYGKWTWHXIAUUMUUNUUTUVAXJAYDINUVCUVKXKZXLUV
        OYCYLYFUVRXMUVQHYLXEXFUVOIKXNZYGIUKNIUKZYKYIUVQVCWPAUWCUVNAUUKUWCUAIKXR
        WCXOUVOUULIYFOAUUMUVNUVBXOUVOYCUULYFAUVLUVNUDXOUVSXKXSAUWDUVNUWBXOIYGNK
        XPXQXTYAYB $.
    $}

    $( A partial ordering on an indexed union can be constructed from a
       well-ordering on its index class and a collection of partial orderings
       on its members.  (Contributed by Matthew House, 23-Aug-2025.) $)
    weiunpo $p |- ( ( R We A /\ R Se A /\ A. x e. A S Po B ) ->
        T Po U_ x e. A B ) $=
      ( vt vs wral wbr wa wcel vp vq vr wwe wse wpo w3a cv wn ciun cfv wceq csb
      wi wo wor simpl1 weso syl wf simpl2 weiunlem simp1d simpr1 ffvelcdmd sonr
      syl2anc csbeq1 poeq12d nfv nfcsb1v nfpo weq csbeq1a cbvralw sylib rspcdva
      simpl3 fveq2 csbeq1d eleq12d simp2d poirr intnand ioran sylanbrc weiunval
      simprbi nsyl simpr3 jca simpr2 sotr syl13anc orc syl6 simprll simprr orcd
      id eqbrtrd ex simprl simprrl breqtrd eqtrd simprlr simprrr breqd eleqtrrd
      mpbird adantr potr mp2and ccased syl2ani biimpri syl6an ralrimivvva df-po
      olcd sylibr ) GIUDZGIUEZHJUFZAGQZUGZUAUHZYHKRZUIZYHUBUHZKRZYKUCUHZKRZSZYH
      YMKRZUNZSZUCAGHUJZQUBYSQUAYSQYSKUFYGYRUAUBUCYSYSYSYGYHYSTZYKYSTZYMYSTZUGZ
      SZYJYQUUDYHLUKZUUEIRZUUEUUEULZYHYHAUUEJUMZRZSZUOZYIUUDUUFUIZUUJUIUUKUIUUD
      GIUPZUUEGTZUULUUDYCUUMYCYDYFUUCUQZGIURUSZUUDYSGYHLUUDYSGLUTZOUHZAUURLUKZH
      UMZTZOYSQZPUHZUUSIRUIOAUVCHUMZQPGQZUUDABCDEFOGHIJKLPMNUUOYCYDYFUUCVAVBZVC
      ZYGYTUUAUUBVDZVEZGUUEIVFVGUUDUUIUUGUUDAUUEHUMZUUHUFZYHUVJTZUUIUIUUDUVDAUV
      CJUMZUFZUVKPGUUEUVCUUEULUVDUVJUVMUUHAUVCUUEJVHAUVCUUEHVHVIUUDYFUVNPGQYCYD
      YFUUCVRYEUVNAPGYEPVJAUVDUVMAUVCJVKAUVCHVKVLAPVMHUVDJUVMAUVCJVNAUVCHVNVIVO
      VPUVIVQZUUDUVAUVLOYSYHOUAVMZUURYHUUTUVJUVPWTUVPAUUSUUEHUURYHLVSVTWAUUDUUQ
      UVBUVEUVFWBZUVHVQZUVJYHUUHWCVGWDUUFUUJWEWFYIYTYTSUUKABCDEFGHYHYHIJKLMNWGW
      HWIUUDYTUUBSZYOUUEYMLUKZIRZUUEUVTULZYHYMUUHRZSZUOZYPUUDYTUUBUVHYGYTUUAUUB
      WJZWKYLUUDUUEYKLUKZIRZUUEUWGULZYHYKUUHRZSZUOZUWGUVTIRZUWGUVTULZYKYMAUWGJU
      MZRZSZUOZUWEYNYLYTUUASUWLABCDEFGHYHYKIJKLMNWGWHYNUUAUUBSUWRABCDEFGHYKYMIJ
      KLMNWGWHUUDUWHUWMUWKUWQUWEUUDUWHUWMSZUWAUWEUUDUUMUUNUWGGTUVTGTUWSUWAUNUUP
      UVIUUDYSGYKLUVGYGYTUUAUUBWLZVEUUDYSGYMLUVGUWFVEGUUEUWGUVTIWMWNUWAUWDWOWPU
      UDUWKUWMSZUWEUUDUXASZUWAUWDUXBUUEUWGUVTIUUDUWIUWJUWMWQUUDUWKUWMWRXAWSXBUU
      DUWHUWQSZUWEUUDUXCSZUWAUWDUXDUUEUWGUVTIUUDUWHUWQXCUUDUWHUWNUWPXDXEWSXBUUD
      UWKUWQSZUWEUUDUXESZUWDUWAUXFUWBUWCUXFUUEUWGUVTUUDUWIUWJUWQWQZUUDUWKUWNUWP
      XDXFZUXFUWJYKYMUUHRZUWCUUDUWIUWJUWQXGUXFUXIUWPUUDUWKUWNUWPXHUXFUUHUWOYKYM
      UXFAUUEUWGJUXGVTXIXKUXFUVKUVLYKUVJTYMUVJTUWJUXISUWCUNUUDUVKUXEUVOXLUUDUVL
      UXEUVRXLUXFYKAUWGHUMZUVJUUDYKUXJTZUXEUUDUVAUXKOYSYKOUBVMZUURYKUUTUXJUXLWT
      UXLAUUSUWGHUURYKLVSVTWAUVQUWTVQXLUXFAUUEUWGHUXGVTXJUXFYMAUVTHUMZUVJUUDYMU
      XMTZUXEUUDUVAUXNOYSYMOUCVMZUURYMUUTUXMUXOWTUXOAUUSUVTHUURYMLVSVTWAUVQUWFV
      QXLUXFAUUEUVTHUXHVTXJUVJYHYKYMUUHXMWNXNWKYAXBXOXPYPUVSUWESABCDEFGHYHYMIJK
      LMNWGXQXRWKXSUAUBUCYSKXTYB $.

    $( A strict ordering on an indexed union can be constructed from a
       well-ordering on its index class and a collection of strict orderings on
       its members.  (Contributed by Matthew House, 23-Aug-2025.) $)
    weiunso $p |- ( ( R We A /\ R Se A /\ A. x e. A S Or B ) ->
        T Or U_ x e. A B ) $=
      ( vs vt wcel wa wbr csb wwe wse wor wral w3a ciun wpo sopo ralimi weiunpo
      vq vr syl3an3 cv cfv weq w3o wceq wo simplrl animorrl weiunval syl21anbrc
      simplrr 3mix1d csbeq1 soeq12d simpll3 nfv nfcsb1v nfso csbeq1a cbvralw wf
      sylib wn simpl1 simpl2 weiunlem simp1d simprl ffvelcdmd adantr rspcdva id
      fveq2 csbeq1d eleq12d simp2d simpr eleqtrrd solin syl12anc simpllr anim1i
      olcd sylanbrc ex idd simplr eqcomd breqdi jca 3orim123d mpd 3mix3d simprr
      weso syl mpjao3dan issod ) GIUAZGIUBZHJUCZAGUDZUEZUKULAGHUFZKXOXLXMHJUGZA
      GUDXQKUGXNXRAGHJUHUIABCDEFGHIJKLMNUJUMXPUKUNZXQQZULUNZXQQZRZRZXSLUOZYALUO
      ZISZXSYAKSZUKULUPZYAXSKSZUQZYEYFURZYFYEISZYDYGRZYHYIYJYNXTYBYGYLXSYAAYEJT
      ZSZRZUSZYHXPXTYBYGUTXPXTYBYGVDYDYGYQVAABCDEFGHXSYAIJKLMNVBZVCVEYDYLRZYPYI
      YAXSYOSZUQZYKYTAYEHTZYOUCZXSUUCQZYAUUCQUUBYTAOUNZHTZAUUFJTZUCZUUDOGYEUUFY
      EURUUGUUCUUHYOAUUFYEJVFAUUFYEHVFVGYTXOUUIOGUDXLXMXOYCYLVHXNUUIAOGXNOVIAUU
      GUUHAUUFJVJAUUFHVJVKAOUPHUUGJUUHAUUFJVLAUUFHVLVGVMVOYDYEGQZYLYDXQGXSLYDXQ
      GLVNZPUNZAUULLUOZHTZQZPXQUDZUUFUUMISVPPUUGUDOGUDZYDABCDEFPGHIJKLOMNXLXMXO
      YCVQZXLXMXOYCVRVSZVTZXPXTYBWAWBZWCWDYTUUOUUEPXQXSPUKUPZUULXSUUNUUCUVBWEUV
      BAUUMYEHUULXSLWFWGWHYDUUPYLYDUUKUUPUUQUUSWIWCZXPXTYBYLUTZWDYTYAAYFHTZUUCY
      TUUOYAUVEQPXQYAPULUPZUULYAUUNUVEUVFWEUVFAUUMYFHUULYALWFWGWHUVCXPXTYBYLVDZ
      WDYTAYEYFHYDYLWJZWGWKUUCXSYAYOWLWMYTYPYHYIYIUUAYJYTYPYHYTYPRZYCYRYHXPYCYL
      YPWNUVIYQYGYTYLYPUVHWOWPYSWQWRYTYIWSYTUUAYJYTUUARZYBXTYMYFYEURZYAXSAYFJTZ
      SZRZUSZYJYTYBUUAUVGWCYTXTUUAUVDWCUVJUVNYMUVJUVKUVMUVJYEYFYDYLUUAWTZXAUVJY
      OUVLYAXSUVJAYEYFJUVPWGYTUUAWJXBXCWPABCDEFGHYAXSIJKLMNVBZVCWRXDXEYDYMRZYJY
      HYIUVRYBXTUVOYJXPXTYBYMVDXPXTYBYMUTYDYMUVNVAUVQVCXFYDGIUCZUUJYFGQYGYLYMUQ
      YDXLUVSUURGIXHXIUVAYDXQGYALUUTXPXTYBXGWBGYEYFIWLWMXJXK $.

    $( A well-founded relation on an indexed union can be constructed from a
       well-ordering on its index class and a collection of well-founded
       relations on its members.  (Contributed by Matthew House,
       23-Aug-2025.) $)
    weiunfr $p |- ( ( R We A /\ R Se A /\ A. x e. A S Fr B ) ->
        T Fr U_ x e. A B ) $=
      ( vr vt wral wa wbr wn vo vn vm vq vp vs wwe wse wfr w3a cv ciun wss wrex
      wne wal cima crio csb cin cvv wceq csbeq1 freq12d simpl3 nfv nfcsb1v nffr
      c0 wi weq csbeq1a cbvralw sylib wf cfv wcel simpl1 simpl2 weiunlem simp1d
      fimassd eqid simprl simprr weiunfrlem sseldd rspcdva inss2 a1i inex1 wfun
      vex ffund fvelima syl2anc wel simplrl simp2d syldan csbeq1d eleqtrd elind
      r19.21bi ne0d rexlimddv frd elin1d wo fveq2 breq1d ad2antrr simpr fveqeq2
      notbid simp3d breq2d mtbird breq1 simplr id eleq12d ad3antrrr eqtrd breqd
      adantr ex imnan pm4.56 biimpi intnand sylnibr ralrimiva reximssdv alrimiv
      weiunval df-fr sylibr ) GIUGZGIUHZHJUIZAGQZUJZOUKZAGHULZUMZUUDVIUOZRZUAUK
      ZUBUKZKSZTZUAUUDQZUBUUDUNZVJZOUPUUEKUIUUCUUOOUUCUUHUUNUUCUUHRZUCUKZUUJAUD
      UKUEUKISTUDLUUDUQZQUEUURURZJUSZSZTZUCUUDAUUSHUSZUTZQZUUMUBUUDUVDUUPUBUCUV
      CUVDUUTVAUUPAUFUKZHUSZAUVFJUSZUIZUVCUUTUIUFGUUSUVFUUSVBUVGUVCUVHUUTAUVFUU
      SJVCAUVFUUSHVCVDUUPUUBUVIUFGQYSYTUUBUUHVEUUAUVIAUFGUUAUFVFAUVGUVHAUVFJVGA
      UVFHVGVHAUFVKHUVGJUVHAUVFJVLAUVFHVLVDVMVNUUPUURGUUSUUPUUEGLUUDUUPUUEGLVOZ
      PUKZAUVKLVPZHUSZVQZPUUEQZUVFUVLISTPUVGQUFGQZUUPABCDEFPGHIJKLUFMNYSYTUUBUU
      HVRZYSYTUUBUUHVSZVTZWAZWBUUPUUSUURVQZUVLUUSISZTZPUUDQZUVLUUSVBZPUVDQZUUPA
      BCDEFPGHIJKUUSLOUDUEMNUVQUVRUUSWCUUCUUFUUGWDZUUCUUFUUGWEWFZWAZWGWHUVDUVCU
      MUUPUUDUVCWIWJUVDVAVQUUPUUDUVCOWMWKWJUUPUWEUVDVIUOPUUDUUPLWLUWAUWEPUUDUNU
      UPUUEGLUVTWNUWIPUUSUUDLWOWPUUPPOWQZUWERZRZUVDUVKUWLUUDUVCUVKUUPUWJUWEWDZU
      WLUVKUVMUVCUUPUWKUVKUUEVQUVNUWLUUDUUEUVKUUCUUFUUGUWKWRUWMWGUUPUVNPUUEUUPU
      VJUVOUVPUVSWSZXDWTUWLAUVLUUSHUUPUWJUWEWEXAXBXCXEXFXGUUPUUJUVDVQZUVERZRZUU
      DUVCUUJUUPUWOUVEWDXHUWQUULUAUUDUWQUAOWQZRZUUIUUEVQZUUJUUEVQRZUUILVPZUUJLV
      PZISZUXBUXCVBZUUIUUJAUXBJUSZSZRZXIZRUUKUWSUXIUXAUWSUXDTZUXHTZUXITZUWSUXDU
      XBUUSISZUWSUWCUXMTPUUDUUIPUAVKZUWBUXMUXNUVLUXBUUSIUVKUUILXJZXKXOUWSUWAUWD
      UWFUUPUWAUWDUWFUJUWPUWRUWHXLZWSUWQUWRXMZWHUWSUXCUUSUXBIUWSUWEUXCUUSVBZPUV
      DUUJUVKUUJUUSLXNUWSUWAUWDUWFUXPXPUUPUWOUVEUWRWRWHZXQXRUWSUXEUXGTZVJUXKUWS
      UXEUXTUWSUXERZUXGUUIUUJUUTSZUYAUVBUYBTUCUVDUUIUCUAVKUVAUYBUUQUUIUUJUUTXSX
      OUWQUVEUWRUXEUUPUWOUVEWEXLUYAUUDUVCUUIUWQUWRUXEXTUYAUUIAUXBHUSZUVCUYAUVNU
      UIUYCVQPUUEUUIUXNUVKUUIUVMUYCUXNYAUXNAUVLUXBHUXOXAYBUUPUVOUWPUWRUXEUWNYCU
      WSUWTUXEUWSUUDUUEUUIUUPUUFUWPUWRUWGXLUXQWGYFWHUYAAUXBUUSHUYAUXBUXCUUSUWSU
      XEXMUWSUXRUXEUXSYFYDZXAXBXCWHUYAUXFUUTUUIUUJUYAAUXBUUSJUYDXAYEXRYGUXEUXGY
      HVNUXJUXKRUXLUXDUXHYIYJWPYKABCDEFGHUUIUUJIJKLMNYPYLYMYNYGYOOUBUAUUEKYQYR
      $.

    $( The relation constructed in ~ weiunpo , ~ weiunso , ~ weiunfr , and
       ~ weiunwe is set-like if all members of the indexed union are sets.
       (Contributed by Matthew House, 23-Aug-2025.) $)
    weiunse $p |- ( ( R We A /\ R Se A /\ A. x e. A B e. V ) ->
        T Se U_ x e. A B ) $=
      ( vs vt wcel wral cvv vq vp vr wwe wse w3a cv wbr ciun wa cfv csn cun csb
      crab simpl2 wf wn simpl1 weiunlem simpr ffvelcdmd seex syl2anc snex unexg
      simp1d sylancl wss ssrab2 a1i snssd unssd simpl3 ralimi syl nfcsb1v nfel1
      elex nfv weq csbeq1a eleq1d cbvralw sylib ssralv sylc wceq 3ad2ant1 simp2
      iunexg breq1 elrab elun1 sylbir sylan fvex elsn elun2 ad2antrl wo simprbi
      weiunval 3ad2ant3 mpjaodan id fveq2 csbeq1d eleq12d simp2d rspcdva csbeq1
      eliuni rabssdv ssexd ralrimiva df-se sylibr ) GIUDZGIUEZHMRZAGSZUFZUAUGZU
      BUGZKUHZUAAGHUIZUOZTRZUBYGSYGKUEYCYIUBYGYCYEYGRZUJZYHPUCUGZYELUKZIUHZUCGU
      OZYMULZUMZAPUGZHUNZUIZTYKYQTRZYSTRZPYQSZYTTRYKYOTRZYPTRUUAYKXTYMGRUUDXSXT
      YBYJUPZYKYGGYELYKYGGLUQZQUGZAUUGLUKZHUNZRZQYGSZYRUUHIUHURQYSSPGSZYKABCDEF
      QGHIJKLPNOXSXTYBYJUSUUEUTZVGZYCYJVAVBZUCGYMIVCVDYMVEYOYPTTVFVHYKYQGVIUUBP
      GSZUUCYKYOYPGYOGVIYKYNUCGVJVKYKYMGUUOVLVMYKHTRZAGSZUUPYKYBUURXSXTYBYJVNYA
      UUQAGHMVSVOVPUUQUUBAPGUUQPVTAYSTAYRHVQVRAPWAHYSTAYRHWBWCWDWEUUBPYQGWFWGPY
      QYSTTWKVDYKYFUAYGYTYKYDYGRZYFUFZYDLUKZYQRZYDAUVAHUNZRZYDYTRUUTUVAYMIUHZUV
      BUVAYMWHZYDYEAUVAJUNUHZUJZUUTUVAGRZUVEUVBUUTYGGYDLYKUUSUUFYFUUNWIYKUUSYFW
      JZVBUVIUVEUJUVAYORUVBYNUVEUCUVAGYLUVAYMIWLWMUVAYOYPWNWOWPUVFUVBUUTUVGUVFU
      VAYPRUVBUVAYMYDLWQWRUVAYPYOWSWOWTYFYKUVEUVHXAZUUSYFUUSYJUJUVKABCDEFGHYDYE
      IJKLNOXCXBXDXEUUTUUJUVDQYGYDQUAWAZUUGYDUUIUVCUVLXFUVLAUUHUVAHUUGYDLXGXHXI
      YKUUSUUKYFYKUUFUUKUULUUMXJWIUVJXKPUVAYSUVCYQYDAYRUVAHXLXMVDXNXOXPUBUAYGKX
      QXR $.

    $( A well-ordering on an indexed union can be constructed from a
       well-ordering on its index class and a collection of well-orderings on
       its members.  (Contributed by Matthew House, 23-Aug-2025.) $)
    weiunwe $p |- ( ( R We A /\ R Se A /\ A. x e. A S We B ) ->
        T We U_ x e. A B ) $=
      ( wwe wral wfr wor ralimi syl3an3 wse w3a ciun wefr weiunfr weiunso df-we
      weso sylanbrc ) GIOZGIUAZHJOZAGPZUBAGHUCZKQZUNKRZUNKOUMUJUKHJQZAGPUOULUQA
      GHJUDSABCDEFGHIJKLMNUETUMUJUKHJRZAGPUPULURAGHJUHSABCDEFGHIJKLMNUFTUNKUGUI
      $.
  $}

  ${
    $d A s t u v w x y z $.  $d B s t u v w y z $.  $d S s t y z $.  $d V s $.
    $( An indexed union of sets is numerable if its index set is numerable and
       there exists a collection of well-orderings on its members.
       (Contributed by Matthew House, 23-Aug-2025.) $)
    numiunnum $p |- ( ( A e. dom card /\ A. x e. A ( B e. V /\ S We B ) ) ->
        U_ x e. A B e. dom card ) $=
      ( vt vs vy vz vw vv vu wcel wwe wa wral cv wex wbr cvv ccrd dfac8b adantr
      cdm ciun wn crab crio cmpt cfv wceq csb wo copab cxp simpll simplr r19.26
      sylib simpld syl2anc xpexd wss opabssxp a1i ssexd wse simpr exse ad2antrr
      iunexg simprd eqid weiunwe syl3anc weeq1 spcedv exlimddv ween sylibr ) BU
      AUDZMZCEMZCDNZOABPZOZABCUEZFQZNZFRZWGWAMWFBGQZNZWJGWBWLGRWEGBUBUCWFWLOZWI
      WGHQZWGMIQZWGMOWNJWGKQLQWKSUFKJQCMABUGZPLWPUHUIZUJZWOWQUJZWKSWRWSUKWNWOAW
      RDULSOUMZOHIUNZNZFTXAWMXAWGWGUOZTWMWGWGTTWMWBWCABPZWGTMWBWEWLUPWMXDWDABPZ
      WMWEXDXEOWBWEWLUQWCWDABURUSZUTABCWAEVKVAZXGVBXAXCVCWMWTHIWGWGVDVEVFWMWLBW
      KVGZXEXBWFWLVHWBXHWEWLBWKWAVIVJWMXDXEXFVLAHIJKLBCWKDXAWQWQVMXAVMVNVOWGWHX
      AVPVQVRWGFVSVT $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Axiom of Transitive Containment
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d w x y z $.
    $( Axiom of Transitive Containment, derived as a theorem from ~ ax-ext ,
       ~ ax-rep , and ~ ax-inf2 .  Use ~ ax-tco instead.  (Contributed by
       Matthew House, 6-Apr-2026.)  (New usage is discouraged.) $)
    axtco $p |- E. y ( x e. y /\
        A. z ( z e. y -> A. w ( w e. z -> w e. y ) ) ) $=
      ( cv csn wss wtr wa wi wal w3a wel vsnex tz9.1 vex snss wral dftr3 df-ss
      ralbii df-ral 3bitrri anbi12i biimpri 3adant3 eximii ) AEZFZBEZGZUJHZUICE
      ZGUMHIUJUMGJCKZLABMZCBMDCMDBMJDKZJCKZIZBBCUIANOUKULURUNURUKULIUOUKUQULUHU
      JAPQULUMUJGZCUJRUPCUJRUQCUJSUSUPCUJDUMUJTUAUPCUJUBUCUDUEUFUG $.

    $( The Axiom of Transitive Containment of ZF set theory.  It was derived as
       ~ axtco above and is therefore redundant if we assume ~ ax-ext ,
       ~ ax-rep and ~ ax-inf2 , but we state it as a separate axiom here so
       that its uses can be identified more easily.  It states that a
       transitive set ` y ` exists that contains a given set ` x ` .  In
       particular, the transitive closure of ` x ` is a set, since it is a
       subset of ` y ` , see ~ df-tc .

       Traditionally, this statement is not counted as an axiom at all, but as
       a theorem from Replacement and Infinity.  In fact, from the transitive
       closure of ` x ` we can construct the set of iterated unions of ` x `
       (and vice versa), and Skolem took the existence of the latter set as a
       motivation for introducing the Axiom of Replacement.  But Transitive
       Containment is strictly weaker than either of those axioms, so many
       authors identify it as its own axiom when investigating subsystems of
       ZF, such as Zermelo set theory or finitist set theory.  We follow this
       separation in order to avoid nonessential usage of the stronger axioms.

       There are two main versions of this axiom that appear in the literature:
       the _strong form_ ` |- E. y ( x e. y /\ Tr y ) ` , see ~ axtco1 and
       ~ axtco1g , and the _weak form_ ` |- E. y ( x C_ y /\ Tr y ) ` , see
       ~ axtco2 and ~ axtco2g .  The weak form follows directly from the strong
       form, see ~ axtco2 .  But the strong form only follows from the weak
       form if we allow ~ el or one of its variants, see ~ axtco1from2 .  We
       take the strong form here as the axiom, since it is slightly shorter
       when expanded to primitive symbols.  Yet the weak form turns out to be
       more suitable for ~ axtcond for reasons of syntax.  (Contributed by
       Matthew House, 6-Apr-2026.) $)
    ax-tco $a |- E. y ( x e. y /\
        A. z ( z e. y -> A. w ( w e. z -> w e. y ) ) ) $.
    $( $j restatement 'ax-tco' of 'axtco'; $)
  $}

  ${
    $d v x y $.  $d v w y z $.
    $( Strong form of the Axiom of Transitive Containment.  See ~ ax-tco for
       more information.  In particular, this theorem generalizes the statement
       of ~ ax-tco , allowing it to be written with only three variables, since
       ` x ` need not be distinct from both ` z ` and ` w ` .  (Contributed by
       Matthew House, 7-Apr-2026.) $)
    axtco1 $p |- E. y ( x e. y /\
        A. z ( z e. y -> A. w ( w e. z -> w e. y ) ) ) $=
      ( vv wel wi wal wa wex weq elequ1 anbi1d exbidv ax-tco chvarvv ) EBFZCBFD
      CFDBFGDHGCHZIZBJABFZRIZBJEAEAKZSUABUBQTREABLMNEBCDOP $.
  $}

  ${
    $d x y z $.  $d w y z $.
    $( Weak form of the Axiom of Transitive Containment.  See ~ ax-tco for more
       information.  In particular, this theorem shows the derivation of the
       weak form from the strong form.  (Contributed by Matthew House,
       6-Apr-2026.) $)
    axtco2 $p |- E. y A. z ( ( z = x \/ z e. y ) ->
        A. w ( w e. z -> w e. y ) ) $=
      ( wel wi wal weq axtco1 elequ1 biimprcd imim1d alimdv jao al2imi syli imp
      wa wo eximii ) ABEZCBEZDCEDBEFDGZFZCGZRCAHZUBSUCFZCGZBABCDIUAUEUHUEUAUFUC
      FZCGUHUAUDUICUAUFUBUCUFUBUACABJKLMUIUDUGCUFUCUBNOPQT $.
  $}

  ${
    $d v x y $.  $d u v w y z $.
    $( Strong form ~ axtco1 of the Axiom of Transitive Containment, derived
       from the weak form ~ axtco2 .  See ~ ax-tco for more information.  As
       written, the proof uses ~ ax-pr via ~ el , but we could alternatively
       use ~ ax-pow via ~ elALT2 .  Use ~ axtco1 instead.  (Contributed by
       Matthew House, 6-Apr-2026.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    axtco1from2 $p |- E. y ( x e. y /\
        A. z ( z e. y -> A. w ( w e. z -> w e. y ) ) ) $=
      ( vv vu wel wi wal wex weq elequ1 anbi1d exbidv axtco2 orc elequ2 biimprd
      wa wo imbi12d spvv syl9 embantd spimvw com12 olc imim1i alimi jca2 eximdv
      mpi el exlimiiv chvarvv ) EBGZCBGZDCGZDBGZHZDIZHZCIZSZBJZABGZVCSZBJEAEAKZ
      VDVGBVHUPVFVCEABLMNEFGZVEFVICFKZUQTZVAHZCIZBJVEFBCDOVIVMVDBVIVMUPVCVMVIUP
      VLVIUPHZCFVJVKVAVNVJUQPVJVIECGZVAUPVJVOVICFEQRUTVOUPHDEDEKURVOUSUPDECLDEB
      LUAUBUCUDUEUFVLVBCUQVKVAUQVJUGUHUIUJUKULEFUMUNUO $.
  $}

  ${
    $d A w x y z $.
    $( Strong form of the Axiom of Transitive Containment using class variables
       and abbreviations.  See ~ ax-tco for more information.  (Contributed by
       Matthew House, 6-Apr-2026.) $)
    axtco1g $p |- ( A e. V -> E. x ( A e. x /\ Tr x ) ) $=
      ( vy vz vw wel wi wal wa wex cv wcel wtr wceq eleq1 wb wss wral dftr3 a1i
      df-ss ralbii df-ral 3bitrri anbi12d exbidv axtco1 vtoclg ) DAGZEAGFEGFAGH
      FIZHEIZJZAKBALZMZUNNZJZAKDBCDLZBOZUMUQAUSUJUOULUPURBUNPULUPQUSUPELZUNRZEU
      NSUKEUNSULEUNTVAUKEUNFUTUNUBUCUKEUNUDUEUAUFUGDAEFUHUI $.
  $}

  ${
    $d A x $.
    $( Weak form of the Axiom of Transitive Containment using class variables
       and abbreviations.  See ~ ax-tco for more information.  (Contributed by
       Matthew House, 6-Apr-2026.) $)
    axtco2g $p |- ( A e. V -> E. x ( A C_ x /\ Tr x ) ) $=
      ( wcel cv wtr wa wex wss axtco1g trss imdistanri eximi syl ) BCDBAEZDZOFZ
      GZAHBOIZQGZAHABCJRTAQPSOBKLMN $.
  $}

  ${
    $d t u v w x $.  $d t u v w y $.  $d t u v w z $.
    $( A version of the Axiom of Transitive Containment with no distinct
       variable conditions.  Usage of this theorem is discouraged because it
       depends on ~ ax-13 .  (Contributed by Matthew House, 6-Apr-2026.)
       (New usage is discouraged.) $)
    axtcond $p |- E. y A. z ( ( z = x \/ z e. y ) ->
        A. x ( x e. z -> x e. y ) ) $=
      ( vv vw vt vu weq wal wel wo wi wn nfnae wnf wb adantl elequ2 nfae notbid
      wex w3a axtco2 nf3an nfv equequ2 orbi1d elequ1 imbi12d cbvalvw a1i albidv
      dvelimnf naecoms 3ad2ant1 wa nfeqf2 3ad2ant3 nfan1 simpl2 equequ1 elequ12
      syl ancoms orbi12d nfan adantr nfand albid expr 3adantl3 cbvaldw ex mpbii
      cbvexdw 3exp sps biimprd alrimi a1d 19.8ad ax-nul biimprcd elirrv pm2.21d
      mtbii alimi spvv alrimdd pm2.61i syl6 jaod eximd mpi imbi1d exbid pm2.61d
      imbitrrid pm2.61iii ) ABHZAIZACHZAIZBCHZBIZCAHZCBJZKZACJZABJZLZAIZLZCIZBU
      AZXAMZXCMZXEMZXOXPXQXRUBZDAHZDEJZKZADJZAEJZLZAIZLZDIZEUAXOAEDAUCXSYHXNEBX
      PXQXRBABBNACBNBCBNZUDXPXQYHBOZXRYJBADFHZYAKZFDJZFEJZLZFIZLZDIZYHBAFYRBUEF
      AHZYQYGDYSYLYBYPYFYSYKXTYAFADUFUGYPYFPYSYOYEFAYSYMYCYNYDFADUHFAEUHUIUJUKU
      IZULUMUNUOXSEBHZYHXNPXSUUAUPZYGXMDCXSUUACXPXQXRCABCNACCNBCCNZUDXRXPUUACOZ
      XQUUDCBCBEUQUNURUSUUBXQYGCOZXPXQXRUUAUTUUECAYQYGCAFYQCUEYTUMUNVCXPXQUUADC
      HZYGXMPZLXRXPXQUPZUUAUUFUUGUUHUUAUUFUPZUPZYBXHYFXLUUIYBXHPUUHUUIXTXFYAXGU
      UFXTXFPUUADCAVAQUUFUUAYAXGPDCEBVBVDVEQUUJYEXKAUUHUUIAXPXQAABANACANZVFUUHU
      UAUUFAXPUUAAOXQABEUQVGXQUUFAOXPACDUQQVHUSUUIYEXKPUUHUUIYCXIYDXJUUFYCXIPUU
      ADCARQUUAYDXJPUUFEBARVGUIQVIUIVJVKVLVMVOVNVPXAXEXOXEXOLXAXEXNBXEXMCBCCSXE
      XLXHXEXKABCASXEXJXIXDXJXIPBBCARVQVRVSVTVSWAZUKXRXOXACBHZXGKZXLLZCIZBUAZXR
      GBJZMZGIZBUAUUQBGWBXRUUTUUPBYIXRUUTUUOCUUCUUTCOCBGFJZMZGIZUUTCBFUVCCUEFBH
      ZUVBUUSGUVDUVAUURFBGRTULUMUNUUTUUOLXRUUTUUMXLXGUUTUUMGCJZMZGIZXLUUMUVGUUT
      UUMUVFUUSGUUMUVEUURCBGRTULWCXCUVGXLLXCXLUVGXBXKAXBXIXJXBAAJXIAWDACARWFWEW
      GZVTXQUVGXKAUUKUVCUVGACFUVCAUEFCHZUVBUVFGUVIUVAUVEFCGRTULUMUVGXKLXQUVGXIX
      JUVFXIMGAGAHUVEXIGACUHTWHWEUKWIWJWKUUTXGXLUUSXGMGCGCHUURXGGCBUHTWHWEWLUKW
      IWMWNXAXNUUPBABBSXAXMUUOCABCSXAXHUUNXLXAXFUUMXGWTXFUUMPAABCUFVQUGWOVIWPWR
      WQXCXNBXCXMCACCSXCXLXHUVHVTVSWAUULWS $.
  $}

  ${
    $d u v w x y z $.
    $( Derivation of ~ ax-un from ~ ax-tco .  Use ~ ax-un instead.
       (Contributed by Matthew House, 6-Apr-2026.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    axuntco $p |- E. y A. z ( E. w ( z e. w /\ w e. x ) -> z e. y ) $=
      ( vv vu wel wi wal wa wex ax-tco elequ1 elequ2 imbi1d albidv imbi12d spvv
      weq syl6 syl6d impcom impcomd exlimdv alrimiv eximii ) ABGZEBGZFEGZFBGZHZ
      FIZHZEIZJZCDGZDAGZJZDKCBGZHZCIBABEFLUOUTCUOURUSDUOUQUPUSUNUGUQUPUSHZHUNUG
      UQDBGZVAUNUGFAGZUJHZFIZUQVBHZUMUGVEHEAEASZUHUGULVEEABMVGUKVDFVGUIVCUJEAFN
      OPQRVDVFFDFDSVCUQUJVBFDAMFDBMQRTUNVBFDGZUJHZFIZVAUMVBVJHEDEDSZUHVBULVJEDB
      MVKUKVIFVKUIVHUJEDFNOPQRVIVAFCFCSVHUPUJUSFCDMFCBMQRTUAUBUCUDUEUF $.
  $}

  ${
    $d w x y z $.
    $( Derivation of ~ ax-nul from ~ ax-reg and ~ ax-tco .  Use ~ ax-nul
       instead.  (Contributed by Matthew House, 7-Apr-2026.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    axnulregtco $p |- E. x A. y -. y e. x $=
      ( vz vw wel wi wal wa wn wex weq elequ1 biimprd spimevw ax-reg syl pm2.65
      al2imi imim2i impd aleximi mpan9 ax-tco exlimiiv ) CDEZADEZBAEZBDEZFZBGZF
      ZAGZHUGIZBGZAJZDUEUFUGUHIFZBGZHZAJZULUOUEUFAJUSUEUFACACKUFUEACDLMNDABOPUK
      URUNAUKUFUQUNUJUQUNFUFUIUPUMBUGUHQRSTUAUBCDABUCUD $.
  $}

  ${
    $d w x y z $.
    $( Derivation of ~ el from ~ ax-tco .  Use ~ el instead.  (Contributed by
       Matthew House, 7-Apr-2026.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    elALTtco $p |- E. y x e. y $=
      ( vz vw wel wi wal wa ax-tco simpl eximii ) ABEZCBEDCEDBEFDGFCGZHLBABCDIL
      MJK $.
  $}

  ${
    $d A x $.
    tz9.1ctco.1 $e |- A e. _V $.
    $( Version of ~ tz9.1c derived from ~ ax-tco .  (Contributed by Matthew
       House, 6-Apr-2026.) $)
    tz9.1ctco $p |- |^| { x | ( A C_ x /\ Tr x ) } e. _V $=
      ( cv wss wtr wa wex cab cint cvv wcel axtco2g ax-mp intexab mpbi ) BADZEQ
      FGZAHZRAIJKLBKLSCABKMNRAOP $.
  $}

  ${
    $d A x y z $.
    tz9.1tco.1 $e |- A e. _V $.
    $( Version of ~ tz9.1 derived from ~ ax-tco .  (Contributed by Matthew
       House, 6-Apr-2026.) $)
    tz9.1tco $p |- E. x ( A C_ x /\ Tr x /\
        A. y ( ( A C_ y /\ Tr y ) -> x C_ y ) ) $=
      ( vz cv wss wtr wa cab cint wceq wi wal w3a tz9.1ctco isseti ssmin mpbiri
      treq sseq2 wral ralab2 simpr mpgbir trint ax-mp eqimss ssintab sylib 3jca
      eximii ) AFZCBFZGZUNHZIZBJZKZLZCUMGZUMHZUQUMUNGMBNZOAAUSBCDPQUTVAVBVCUTVA
      CUSGUPBCRUMUSCUASUTVBUSHZEFZHZEURUBZVDVGUQUPMBUQVFUPEBVEUNTUCUOUPUDUEEURU
      FUGUMUSTSUTUMUSGVCUMUSUHUQBUMUIUJUKUL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Transitive closure of a class
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x $.
    $( Every nonempty transitive set contains the empty set ` (/) ` as an
       element, a consequence of Regularity.  If we assume Transitive
       Containment, then we can omit the ` A e. V ` hypothesis, see ~ tr0el .
       (Contributed by Matthew House, 6-Apr-2026.) $)
    tr0elw $p |- ( ( A e. V /\ A =/= (/) /\ Tr A ) -> (/) e. A ) $=
      ( vx wcel c0 wne wtr wa cv cin wceq wrex zfreg wss trss dfss eqeq2 bitrid
      imp syl5ibcom wi eleq1 biimpcd adantl syld rexlimdva syl5com 3impia ) ABD
      ZAEFZAGZEADZUIUJHCIZAJZEKZCALUKULCABMUKUOULCAUKUMADZHZUOUMEKZULUQUMANZUOU
      RUKUPUSAUMOSUSUMUNKUOURUMAPUNEUMQRTUPURULUAUKURUPULUMEAUBUCUDUEUFUGUH $.
  $}

  ${
    $d A x $.
    $( Every nonempty transitive class contains the empty set ` (/) ` as an
       element, a consequence of Regularity and Transitive Containment.
       (Contributed by Matthew House, 6-Apr-2026.) $)
    tr0el $p |- ( ( A =/= (/) /\ Tr A ) -> (/) e. A ) $=
      ( vx c0 wne cv cin wceq wrex wtr wcel zfregs wa wss trss imp eqeq2 bitrid
      dfss syl5ibcom wi eleq1 biimpcd adantl syld rexlimdva mpan9 ) ACDBEZAFZCG
      ZBAHAIZCAJZBAKUJUIUKBAUJUGAJZLZUIUGCGZUKUMUGAMZUIUNUJULUOAUGNOUOUGUHGUIUN
      UGARUHCUGPQSULUNUKTUJUNULUKUGCAUAUBUCUDUEUF $.
  $}

  $c TC+ $.

  $( Extend class notation with the transitive closure of a class.
     (Contributed by Matthew House, 6-Apr-2026.) $)
  cttc $a class TC+ A $.

  ${
    $d A x y $.
    $( Transitive closure of a class.  Unlike ` ( TC `` A ) ` (see ~ df-tc ),
       this definition works even if ` A ` or its transitive closure is a
       proper class.  Note that unless we assume Transitive Containment, the
       transitive closure of a set may be a proper class.  If we only assume
       Regularity, then the class of sets whose transitive closure is a set is
       precisely the class of well-founded sets, see ~ ttcwf3 .  (Contributed
       by Matthew House, 6-Apr-2026.) $)
    df-ttc $a |- TC+ A =
        U_ x e. A U. ( rec ( ( y e. _V |-> U. y ) , { x } ) " _om ) $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( Equality theorem for transitive closure.  (Contributed by Matthew House,
       6-Apr-2026.) $)
    ttceq $p |- ( A = B -> TC+ A = TC+ B ) $=
      ( vx wceq cvv cuni cmpt csn crdg com cima ciun cttc iuneq1 df-ttc 3eqtr4g
      vy cv ) ABDCAQEQRFGCRHIJKFZLCBSLAMBMCABSNCQAOCQBOP $.
  $}

  ${
    ttceqi.1 $e |- A = B $.
    $( Equality inference for transitive closure.  (Contributed by Matthew
       House, 6-Apr-2026.) $)
    ttceqi $p |- TC+ A = TC+ B $=
      ( wceq cttc ttceq ax-mp ) ABDAEBEDCABFG $.
  $}

  ${
    ttceqd.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for transitive closure.  (Contributed by Matthew
       House, 6-Apr-2026.) $)
    ttceqd $p |- ( ph -> TC+ A = TC+ B ) $=
      ( wceq cttc ttceq syl ) ABCEBFCFEDBCGH $.
  $}

  ${
    $d x y z $.  $d A y z $.
    nfttc.1 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for transitive closure.  (Contributed
       by Matthew House, 6-Apr-2026.) $)
    nfttc $p |- F/_ x TC+ A $=
      ( vy vz cttc cvv cv cuni cmpt csn crdg cima ciun df-ttc nfcv nfiun nfcxfr
      com ) ABFDBEGEHIJDHKLSMIZNDEBODABTCATPQR $.
  $}

  ${
    $d A x y z $.
    $( The transitive closure contains its argument as a subclass.
       (Contributed by Matthew House, 6-Apr-2026.) $)
    ttcid $p |- A C_ TC+ A $=
      ( vz vx vy cttc cv wcel cvv cuni cmpt csn crdg com cima ciun vsnid c0 cfv
      con0 wceq vsnex rdg0 wfn wss rdgfnon omsson peano1 fnfvima mp3an eqeltrri
      elunii mp2an weq sneq rdgeq2 imaeq1d unieqd eliuni mpan2 df-ttc eleqtrrdi
      syl ssriv ) BAAEZBFZAGZVECADHDFIJZCFZKZLZMNZIZOZVDVFVEVGVEKZLZMNZIZGZVEVM
      GVEVNGVNVPGVRBPQVORZVNVPVNVGBUAUBVOSUCMSUDQMGVSVPGVNVGUEUFUGSMVOQUHUIUJVE
      VNVPUKULCVEVLVQAVECBUMZVKVPVTVJVOMVTVIVNTVJVOTVHVEUNVIVNVGUOVBUPUQURUSCDA
      UTVAVC $.
  $}

  ${
    $d u v w x y z $.  $d A u v x y $.
    $( The transitive closure of a class is transitive.  (Contributed by
       Matthew House, 6-Apr-2026.) $)
    ttctr $p |- Tr TC+ A $=
      ( vu vv vx vy vz vw cv wcel wa wal cvv cuni com wrex cfv wb eluniima wceq
      ax-mp cttc wtr wel cmpt csn crdg cima ciun wfun rdgfun csuc peano2 elunii
      wi con0 nnon fvex uniex eqid unieq rdgsucmpt2 sylancl eleq2d sylan2 fveq2
      biimpar rspcev syl2an2r sylibr rexlimdvaa biimtrid reximdv 3imtr4g df-ttc
      an12s eliun eleq2i imp gen2 dftr2 mpbir ) AUAZUBBCUCZCHZWBIZJBHZWBIZUNZCK
      BKWHBCWCWEWGWCWDDAELEHZMZUDZDHUEZUFZNUGMZUHZIZWFWOIZWEWGWCWDWNIZDAOWFWNIZ
      DAOWPWQWCWRWSDAWRWDFHZWMPZIZFNOZWCWSWMUIZWRXCQWLWKUJZFNWDWMRTWCXBWSFNWTNI
      ZWCXBWSXFWCXBJZJWFGHZWMPZIZGNOZWSXFWTUKZNIXGWFXLWMPZIZXKWTULXGXFWFXAMZIZX
      NWFWDXAUMXFXNXPXFXMXOWFXFWTUOIXOLIXMXOSWTUPXAWTWMUQUREGWLWTWJXOXHMWMLWMUS
      XHWIUTXHXAUTVAVBVCVFVDXJXNGXLNXHXLSXIXMWFXHXLWMVEVCVGVHXDWSXKQXEGNWFWMRTV
      IVOVJVKVLDWDAWNVPDWFAWNVPVMWBWOWDDEAVNZVQWBWOWFXQVQVMVRVSBCWBVTWA $.
  $}

  $( The transitive closure of a class is transitive.  (Contributed by Matthew
     House, 6-Apr-2026.) $)
  ttctr2 $p |- ( A e. TC+ B -> A C_ TC+ B ) $=
    ( cttc wtr wcel wss wi ttctr trss ax-mp ) BCZDAKEAKFGBHKAIJ $.

  $( The transitive closure of a class is transitive.  (Contributed by Matthew
     House, 6-Apr-2026.) $)
  ttctr3 $p |- U. TC+ A C_ TC+ A $=
    ( cttc wtr cuni wss ttctr df-tr mpbi ) ABZCIDIEAFIGH $.

  ${
    $d w x y z $.  $d A x y $.  $d B w x z $.
    $( The transitive closure of ` A ` is a subclass of every transitive class
       containing ` A ` .  (Contributed by Matthew House, 6-Apr-2026.) $)
    ttcmin $p |- ( ( A C_ B /\ Tr B ) -> TC+ A C_ B ) $=
      ( vx vy vz vw wss wa cvv cv cuni com ciun wcel cfv wceq c0 fveq2 eqsstrid
      sseq1d wtr cttc cmpt csn crdg cima df-ttc ssel2 wfun rdgfun funiunfv csuc
      ax-mp weq vsnex rdg0 snssi w3a con0 nnon fvex uniex eqid unieq rdgsucmpt2
      adantr sylancl 3ad2ant1 uniss 3ad2ant3 simp2r df-tr eqsstrd finds2 impcom
      sylib sstrd 3exp iunssd eqsstrrid sylan an32s ) ABGZBUAZHZAUBCADIDJZKZUCZ
      CJZUDZUEZLUFKZMBCDAUGWECAWLBWCWIANZWDWLBGZWCWMHWIBNZWDWNABWIUHWOWDHZWLELE
      JZWKOZMZBWKUIWSWLPWJWHUJELWKUKUMWPELWRBWQLNWPWRBGZWTQWKOZBGZFJZWKOZBGZXCU
      LZWKOZBGZWPEFWQQPWRXABWQQWKRTEFUNWRXDBWQXCWKRTWQXFPWRXGBWQXFWKRTWOXBWDWOX
      AWJBWJWHCUOUPWIBUQSVFXCLNZWPXEXHXIWPXEURZXGXDKZBXIWPXGXKPZXEXIXCUSNXKINXL
      XCUTXDXCWKVAVBDEWJXCWGXKWQKWKIWKVCWQWFVDWQXDVDVEVGVHXJXKBKZBXEXIXKXMGWPXD
      BVIVJXJWDXMBGXIWOWDXEVKBVLVPVQVMVRVNVOVSVTWAWBVSS $.
  $}

  $( If the transitive closure of a class is a set, then the class is a set.
     (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcexrg $p |- ( TC+ A e. V -> A e. _V ) $=
    ( cttc wss wcel cvv ttcid ssexg mpan ) AACZDJBEAFEAGAJBHI $.

  $( A transitive closure contains the transitive closures of all its
     subclasses.  (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcss $p |- ( A C_ TC+ B -> TC+ A C_ TC+ B ) $=
    ( cttc wss wtr ttctr ttcmin mpan2 ) ABCZDIEACIDBFAIGH $.

  $( The subclass relationship is inherited by transitive closures.
     (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcss2 $p |- ( A C_ B -> TC+ A C_ TC+ B ) $=
    ( wss cttc ttcid sstr mpan2 ttcss syl ) ABCZABDZCZADKCJBKCLBEABKFGABHI $.

  $( A transitive closure contains the transitive closures of all its elements.
     (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcel $p |- ( A e. TC+ B -> TC+ A C_ TC+ B ) $=
    ( cttc wcel wss wtr ttctr2 ttctr ttcmin sylancl ) ABCZDAKEKFACKEABGBHAKIJ
    $.

  $( Elements turn into subclasses upon taking transitive closures.
     (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcel2 $p |- ( A e. B -> TC+ A C_ TC+ B ) $=
    ( wcel cttc wss ttcid sseli ttcel syl ) ABCABDZCADJEBJABFGABHI $.

  $( The transitive closure of a transitive class is the class itself.
     (Contributed by Matthew House, 6-Apr-2026.) $)
  ttctrid $p |- ( Tr A -> TC+ A = A ) $=
    ( wtr cttc wss ssid ttcmin mpan ttcid a1i eqssd ) ABZACZAAADKLADAEAAFGALDKA
    HIJ $.

  $( The transitive closure operation is idempotent.  (Contributed by Matthew
     House, 6-Apr-2026.) $)
  ttcidm $p |- TC+ TC+ A = TC+ A $=
    ( cttc wtr wceq ttctr ttctrid ax-mp ) ABZCHBHDAEHFG $.

  $( Transitivity of ` A C_ TC+ B ` relationship.  (Contributed by Matthew
     House, 6-Apr-2026.) $)
  ssttctr $p |- ( ( A C_ TC+ B /\ B C_ TC+ C ) -> A C_ TC+ C ) $=
    ( cttc wss ttcss sstr sylan2 ) BCDZEABDZEJIEAIEBCFAJIGH $.

  $( Transitivity of ` A e. TC+ B ` relationship.  (Contributed by Matthew
     House, 6-Apr-2026.) $)
  elttctr $p |- ( ( A e. TC+ B /\ B e. TC+ C ) -> A e. TC+ C ) $=
    ( cttc wcel ttcel sseld impcom ) BCDZEZABDZEAIEJKIABCFGH $.

  ${
    $d w x y z $.  $d A w y z $.  $d V y z $.
    $( A shorter expression for the transitive closure of a set.  (Contributed
       by Matthew House, 6-Apr-2026.) $)
    dfttc2g $p |- ( A e. V -> TC+ A =
        U. ( rec ( ( x e. _V |-> U. x ) , A ) " _om ) ) $=
      ( vw vy vz wcel cvv cv cuni com wss c0 cfv con0 wceq fveq2 ax-mp sseq1d
      wa cttc cmpt crdg wtr rdg0g rdgfnon omsson peano1 fnfvima mp3an eqeltrrdi
      cima wfn elssuni syl wel wal wrex csuc peano2 elunii nnon fvex uniex eqid
      unieq rdgsucmpt2 sylancl eleq2d biimpar sylan2 rspcev syl2an2r rexlimdvaa
      wi an12s wfun wb rdgfun eluniima 3imtr4g imp gen2 dftr2 mpbir ttcmin ciun
      funiunfv weq ttcid uniss ttctr3 sstrdi imbitrrid a1d finds2 impcom iunssd
      eqsstrdi eqsstrrid eqssd ) BCGZBUAZAHAIZJZUBZBUCZKULZJZXBBXILZXIUDZXCXILX
      BBXHGXJXBBMXGNZXHBCXFUEZXGOUMKOLMKGXLXHGBXFUFUGUHOKXGMUIUJUKBXHUNUOXKDEUP
      ZEIZXIGZTDIZXIGZVOZEUQDUQXSDEXNXPXRXNXOFIZXGNZGZFKURZXQXOXGNZGZEKURZXPXRX
      NYBYFFKXTKGZXNYBYFYGXTUSZKGXNYBTZXQYHXGNZGZYFXTUTYIYGXQYAJZGZYKXQXOYAVAYG
      YKYMYGYJYLXQYGXTOGYLHGYJYLPXTVBYAXTXGVCVDAEBXTXEYLXOJXGHXGVEXOXDVFXOYAVFV
      GVHZVIVJVKYEYKEYHKXOYHPZYDYJXQXOYHXGQZVIVLVMVPVNXGVQZXPYCVRBXFVSZFKXOXGVT
      RYQXRYFVRYREKXQXGVTRWAWBWCDEXIWDWEBXIWFVHXBXIEKYDWGZXCYQYSXIPYREKXGWHRXBE
      KYDXCXOKGXBYDXCLZYTXLXCLYAXCLZYJXCLZXBEFXOMPYDXLXCXOMXGQSEFWIYDYAXCXOXTXG
      QSYOYDYJXCYPSXBXLBXCXMBWJWSYGUUAUUBVOXBUUAUUBYGYLXCLUUAYLXCJXCYAXCWKBWLWM
      YGYJYLXCYNSWNWOWPWQWRWTXA $.
  $}

  $( The transitive closure of the empty set is the empty set.  (Contributed by
     Matthew House, 6-Apr-2026.) $)
  ttc0 $p |- TC+ (/) = (/) $=
    ( c0 wtr cttc wceq tr0 ttctrid ax-mp ) ABACADEAFG $.

  $( A class has an empty transitive closure iff it is the empty set.
     (Contributed by Matthew House, 6-Apr-2026.) $)
  ttc00 $p |- ( A = (/) <-> TC+ A = (/) ) $=
    ( c0 wceq cttc ttceq ttc0 eqtrdi wss ttcid sseq2 mpbii ss0 syl impbii ) ABC
    ZADZBCZOPBDBABEFGQABHZOQAPHRAIPBAJKALMN $.

  ${
    $d x y $.  $d A y $.  $d B y $.
    $( Distribute proper substitution through a transitive closure.
       (Contributed by Matthew House, 6-Apr-2026.) $)
    csbttc $p |- [_ A / x ]_ TC+ B = TC+ [_ A / x ]_ B $=
      ( vy cvv wcel cttc csb cv csbeq1 ttceqd eqeq12d vex nfcsb1v nfttc csbeq1a
      wceq weq c0 csbprc csbief vtoclg wn ttc0 eqtrdi eqtr4d pm2.61i ) BEFZABCG
      ZHZABCHZGZQZADIZUIHZAUNCHZGZQUMDBEUNBQZUOUJUQULAUNBUIJURUPUKAUNBCJKLAUNUI
      UQDMAUPAUNCNOADRCUPAUNCPKUAUBUHUCZUJSULABUITUSULSGSUSUKSABCTKUDUEUFUG $.
  $}

  $( Relationship between ` TC+ A ` and ` TC+ U. A ` : we can decompose
     ` TC+ A ` into the elements of ` TC+ U. A ` plus the elements of ` A `
     itself.  (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcuniun $p |- TC+ A = ( TC+ U. A u. A ) $=
    ( cttc cun wss wtr ssun2 uniun ttctr3 ttcid unssi eqsstri ssun3 ax-mp df-tr
    cuni mpbir ttcmin mp2an unissi sstri ttcss eqssi ) ABZAOZBZACZAUFDUFEZUCUFD
    AUEFUGUFOZUFDZUHUEDUIUHUEOZUDCUEUEAGUJUDUEUDHUDIJKUHUEALMUFNPAUFQRUEAUCUDUC
    DUEUCDUDUCOUCAUCAIZSAHTUDAUAMUKJUB $.

  ${
    $d A x y $.
    $( Relationship between ` TC+ A ` and ` U_ x e. A TC+ x ` : we can
       decompose ` TC+ A ` into the elements of ` U_ x e. A TC+ x ` plus the
       elements of ` A ` itself.  (Contributed by Matthew House,
       6-Apr-2026.) $)
    ttciunun $p |- TC+ A = ( U_ x e. A TC+ x u. A ) $=
      ( vy cttc cv ciun cun wss ssun2 dftr3 wcel wo elun wral ttctr rgenw ttcid
      wtr wi mprgbir triun trss mp2b ttceq ssiun2s sstrid jaoi sylbi syl ttcmin
      ssun3 mp2an iunss ttcel2 unssi eqssi ) BDZABAEZDZFZBGZBVAHVARZUQVAHBUTIVB
      CEZVAHZCVACVAJVCVAKZVCUTHZVDVEVCUTKZVCBKZLVFVCUTBMVGVFVHUSRZABNUTRVGVFSVI
      ABUROPABUSUAUTVCUBUCVHVCVCDZUTVCQABUSVCVJURVCUDUEUFUGUHVCUTBUKUITBVAUJULU
      TBUQUTUQHUSUQHABABUSUQUMURBUNTBQUOUP $.
  $}

  ${
    $d A x $.  $d B x $.
    $( Distribute union of two classes through a transitive closure.
       (Contributed by Matthew House, 6-Apr-2026.) $)
    ttcun $p |- TC+ ( A u. B ) = ( TC+ A u. TC+ B ) $=
      ( vx cv cttc ciun cun un4 ttciunun iunxun uneq1i eqtri uneq12i 3eqtr4i )
      CACDEZFZCBOFZGZABGZGZPAGZQBGZGSEZAEZBEZGPQABHUCCSOFZSGTCSIUFRSCABOJKLUDUA
      UEUBCAICBIMN $.
  $}

  $( Distribute union of a class through a transitive closure.  (Contributed by
     Matthew House, 6-Apr-2026.) $)
  ttcuni $p |- TC+ U. A = U. TC+ A $=
    ( cuni cttc wss wtr ttcid unissi ttctr3 df-tr mpbir ttcmin mp2an cun unieqi
    ttcuniun uniun eqtri unssi eqsstri eqssi ) ABZCZACZBZUAUDDUDEZUBUDDAUCAFGUE
    UDBUDDUDUCAHGUDIJUAUDKLUDUBBZUAMZUBUDUBAMZBUGUCUHAONUBAPQUFUAUBUAHUAFRST $.

  ${
    $d x y $.  $d A y $.  $d B y $.
    $( Distribute indexed union through a transitive closure.  (Contributed by
       Matthew House, 6-Apr-2026.) $)
    ttciun $p |- TC+ U_ x e. A B = U_ x e. A TC+ B $=
      ( vy ciun cttc cun iunxiun uneq1i iunun eqtr4i ttciunun wceq wcel iuneq2i
      cv a1i 3eqtr4i ) DABCEZDPFZEZSGZABDCTEZCGZEZSFABCFZEUBABUCEZSGUEUAUGSDABC
      THIABUCCJKDSLABUFUDUFUDMAPBNDCLQOR $.
  $}

  $( The transitive closure of a power class is contained in the power class of
     the transitive closure.  (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcpwss $p |- TC+ ~P A C_ ~P TC+ A $=
    ( cpw cttc wss wtr ttcid sspwi ttctr pwtr mpbi ttcmin mp2an ) ABZACZBZDOEZM
    CODANAFGNEPAHNIJMOKL $.

  $( The transitive closure is contained in the singleton transitive closure.
     (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcsnssg $p |- ( A e. V -> TC+ A C_ TC+ { A } ) $=
    ( wcel csn cttc wss snidg ttcel2 syl ) ABCAADZCAEJEFABGAJHI $.

  $( The singleton transitive closure contains its argument ` A ` as an
     element.  (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcsnidg $p |- ( A e. V -> A e. TC+ { A } ) $=
    ( wcel csn cttc ttcid snidg sselid ) ABCADZIEAIFABGH $.

  $( The singleton transitive closure is the minimal transitive class
     containing ` A ` as an element.  (Contributed by Matthew House,
     6-Apr-2026.) $)
  ttcsnmin $p |- ( ( A e. B /\ Tr B ) -> TC+ { A } C_ B ) $=
    ( wcel csn wss wtr cttc snssi ttcmin sylan ) ABCADZBEBFKGBEABHKBIJ $.

  ${
    $d A x $.
    $( Relationship between ` TC+ { A } ` and ` TC+ A ` : the former contains
       the additional element ` A ` .  (Contributed by Matthew House,
       6-Apr-2026.) $)
    ttcsng $p |- ( A e. V -> TC+ { A } = ( TC+ A u. { A } ) ) $=
      ( vx wcel csn cttc cv ciun cun ttciunun ttceq iunxsng uneq1d eqtrid ) ABD
      ZAEZFCPCGZFZHZPIAFZPICPJOSTPCARTBQAKLMN $.
  $}

  $( If the transitive closure of a class is a set, then its singleton
     transitive closure is a set.  (Contributed by Matthew House,
     6-Apr-2026.) $)
  ttcsnexg $p |- ( TC+ A e. V -> TC+ { A } e. _V ) $=
    ( cttc wcel csn cun cvv wceq ttcexrg ttcsng syl snex unexg mpan2 eqeltrd )
    ACZBDZAEZCZPRFZGQAGDSTHABIAGJKQRGDTGDALPRBGMNO $.

  $( The transitive closure of a set is a set iff its singleton transitive
     closure is a set.  (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcsnexbig $p |- ( A e. V -> ( TC+ A e. _V <-> TC+ { A } e. _V ) ) $=
    ( wcel cttc cvv csn ttcsnexg wss ttcsnssg ssexg sylan ex impbid2 ) ABCZADZE
    CZAFDZECZAEGNRPNOQHRPABIOQEJKLM $.

  $( The singleton transitive closure of a transitive set is its successor.
     (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcsntrsucg $p |- ( ( A e. V /\ Tr A ) -> TC+ { A } = suc A ) $=
    ( wcel wtr csn cttc cun csuc ttcsng ttctrid uneq1d df-suc eqtr4di sylan9eq
    ) ABCADZAEZFAFZPGZAHZABIORAPGSOQAPAJKALMN $.

  ${
    $d A x y $.  $d V x $.
    $( If the transitive closure of ` A ` is a set, then its value is
       ` ( TC `` A ) ` .  If we assume Transitive Containment, then we can
       weaken the hypothesis to ` A e. V ` , see ~ dfttc3g .  (Contributed by
       Matthew House, 6-Apr-2026.) $)
    dfttc3gw $p |- ( TC+ A e. V -> TC+ A = ( TC ` A ) ) $=
      ( vy vx cttc wcel ctc cfv cv wss wtr wa cab cint ssmin wral treq cvv wceq
      wi ralab2 simpr mpgbir trint ax-mp ttcmin mp2an df-tc cleq1 ttcexrg ttcid
      adantl wex ttctr sseq2 anbi12d spcegv mp2ani intexab sylib fvmptd2 pm3.2i
      sseqtrrid intmin3 eqsstrd eqssd ) AEZBFZVGAGHZVHACIZJZVJKZLZCMZNZVGVIAVOJ
      VOKZVGVOJVLCAODIZKZDVNPZVPVSVMVLTCVMVRVLDCVQVJQUAVKVLUBUCDVNUDUEAVOUFUGVH
      DAVQVJJVLLCMNZVORGRDCUHVQASVTVOSVHVLVQACUIULABUJVHVMCUMZVORFVHAVGJZVGKZWA
      AUKZAUNZVMWBWCLZCVGBVJVGSVKWBVLWCVJVGAUOVJVGQUPZUQURVMCUSUTVAZVCVHVIVOVGW
      HVMWFCVGBWGWBWCWDWEVBVDVEVF $.
  $}

  $( A set is well-founded iff its transitive closure is well-founded.  As a
     corollary, the transitive closure of any well-founded set is a set.
     (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcwf $p |- ( A e. U. ( R1 " On ) <-> TC+ A e. U. ( R1 " On ) ) $=
    ( cr1 con0 cima cuni wcel cttc crnk cfv csuc cpw wss r1rankidb r1tr sylancl
    wtr ttcmin fvex elpw2 sylibr cdm rankdmr1 r1sucg ax-mp eleqtrrdi r1elwf syl
    wceq ttcid sswf mpan2 impbii ) ABCDEZFZAGZUMFZUNUOAHIZJZBIZFUPUNUOUQBIZKZUS
    UNUOUTLZUOVAFUNAUTLUTPVBAMUQNAUTQOUOUTUQBRSTUQBUAFUSVAUHAUBUQUCUDUEUOURUFUG
    UPAUOLUNAUIUOAUJUKUL $.

  ${
    $d A x $.
    $( If a transitive closure class is a set, then it is well-founded,
       assuming Regularity.  (Contributed by Matthew House, 6-Apr-2026.) $)
    ttcwf2 $p |- ( TC+ A e. _V <-> TC+ A e. U. ( R1 " On ) ) $=
      ( vx cttc cvv wcel cr1 con0 cima cuni wss cdif c0 wceq wn cv sylib sylibr
      wne cin wb wrex wa simpl eldifad ttctr2 syl inssdif0 bilanri eqsstrrd vex
      dfss2 r1elss eldifbd pm2.65da nrex a1i difexg zfreg sylan mtand nne eleq1
      ssdif0 sseq1 bibi12d vtoclg mpbird elex impbii ) ACZDEZVJFGHIZEZVKVMVJVLJ
      ZVKVJVLKZLMZVNVKVOLRZNVPVKVQBOZVOSLMZBVOUAZVTNVKVSBVOVRVOEZVSVRVLEZWAVSUB
      ZVRVLJZWBWCVRVRVJSZVLWCVRVJJZWEVRMWCVRVJEWFWCVRVJVLWAVSUCZUDVRAUEUFVRVJUK
      PWEVLJVSWAVRVJVLUGUHUIVRBUJULZQWCVRVJVLWGUMUNUOUPVKVODEVQVTVJVLDUQBVODURU
      SUTVOLVAPVJVLVCQWBWDTVMVNTBVJDVRVJMWBVMWDVNVRVJVLVBVRVJVLVDVEWHVFVGVJVLVH
      VI $.
  $}

  $( The sets whose transitive closures are sets are precisely the well-founded
     sets, assuming Regularity.  (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcwf3 $p |- ( TC+ A e. _V <-> A e. U. ( R1 " On ) ) $=
    ( cttc cvv wcel cr1 con0 cima cuni ttcwf2 ttcwf bitr4i ) ABZCDLEFGHZDAMDAIA
    JK $.

  $( If a transitive closure is a set, then it contains ` (/) ` as an element
     iff it is nonempty, assuming Regularity.  If we also assume Transitive
     Containment, then we can remove the ` TC+ A e. V ` hypothesis, see
     ~ ttc0el .  (Contributed by Matthew House, 6-Apr-2026.) $)
  ttc0elw $p |- ( TC+ A e. V -> ( A =/= (/) <-> (/) e. TC+ A ) ) $=
    ( wne cttc wcel ttc00 necon3bii wtr ttctr tr0elw mp3an3 ne0i adantl impbida
    c0 bitrid ) AOCADZOCZQBEZOQEZAOQOAFGSRTSRQHTAIQBJKTRSQOLMNP $.

  ${
    $d A x y $.  $d C y z $.  $d D x y z $.
    dfttc4lem1.1 $e |- B = { x | E. y ( ( A i^i y ) =/= (/) /\
        A. z e. y ( ( z i^i y ) = (/) -> z = x ) ) } $.
    dfttc4lem1.2 $e |- C e. _V $.
    dfttc4lem1.3 $e |- D e. _V $.
    $( Lemma for ~ dfttc4 .  (Contributed by Matthew House, 6-Apr-2026.) $)
    dfttc4lem1 $p |- ( ( ( A i^i C ) =/= (/) /\
        A. z e. C ( ( z i^i C ) = (/) -> z = D ) ) -> D e. B ) $=
      ( cin c0 wne cv wceq wi wral wa wex ineq2 neeq1d eqeq1d imbi1d raleqbi1dv
      wcel anbi12d spcev weq eqeq2 imbi2d ralbidv anbi2d exbidv elab2 sylibr )
      DFKZLMZCNZFKZLOZURGOZPZCFQZRZDBNZKZLMZURVEKZLOZVAPZCVEQZRZBSZGEUEVLVDBFIV
      EFOZVGUQVKVCVNVFUPLVEFDTUAVJVBCVEFVNVIUTVAVNVHUSLVEFURTUBUCUDUFUGVGVICAUH
      ZPZCVEQZRZBSVMAGEJANZGOZVRVLBVTVQVKVGVTVPVJCVEVTVOVAVIVSGURUIUJUKULUMHUNU
      O $.
  $}

  ${
    $d u v w x y z $.  $d A u w x y $.  $d B u v w $.
    dfttc4lem2.1 $e |- B = { x | E. y ( ( A i^i y ) =/= (/) /\
        A. z e. y ( ( z i^i y ) = (/) -> z = x ) ) } $.
    $( Lemma for ~ dfttc4 .  (Contributed by Matthew House, 6-Apr-2026.) $)
    dfttc4lem2 $p |- ( A C_ B /\ Tr B ) $=
      ( vu vv vw cv wcel cin c0 wne wceq weq wi wral wn wa wss wtr csn necon2ai
      disjsn biimpi elsni a1d rgen vsnex vex dfttc4lem1 sylancl ssriv wel simpr
      wal wex ineq2d neeq1d eqeq1d simpl eqeq2d imbi12d anbi12d cbvexdvaw elab2
      raleqbidvv cun undisj2 biimpri simpld necon3i imim1i simprd sylib biimprd
      a1i elequ2 con3d pm2.21 syl56 syli com3r ralimdv ralun mpan2 syl6 anim12d
      unex exlimdv biimtrid imp gen2 dftr2 mpbir pm3.2i ) DEUAEUBZGDEGJZDKZDWSU
      CZLZMNCJZXALMOZCGPZQZCXARWSEKZWTXBMXBMOZWTSDWSUEUFUDXFCXAXCXAKZXEXDXCWSUG
      ZUHUIABCDEXAWSFGUJZGUKZULUMUNWRGHUOZHJZEKZTXGQZHUQGUQXPGHXMXOXGXODIJZLZMN
      ZXCXQLZMOZCHPZQZCXQRZTZIURZXMXGDBJZLZMNZXCYGLZMOZCAPZQZCYGRZTZBURYFAXNEHU
      KAHPZYOYEBIYPBIPZTZYIXSYNYDYRYHXRMYRYGXQDYPYQUPZUSUTYRYMYCCYGXQYSYRYKYAYL
      YBYRYJXTMYRYGXQXCYSUSVAYRAJXNXCYPYQVBVCVDVHVEVFFVGXMYEXGIXMYEDXQXAVIZLZMN
      ZXCYTLMOZXEQZCYTRZTXGXMXSUUBYDUUEXSUUBQXMUUAMXRMUUAMOZXRMOZXHUUGXHTUUFDXQ
      XAVJVKVLVMVRXMYDUUDCXQRZUUEXMYCUUDCXQYCUUCXMXEUUCYCYBXMXEQZUUCYAYBUUCYAXD
      YAXDTUUCXCXQXAVJVKZVLVNUUCGCUOZSZYBXMSUUIUUCXDUULUUCYAXDUUJVOXCWSUEVPYBXM
      UUKYBUUKXMCHGVSVQVTXMXEWAWBWCWDWEUUHUUDCXARUUEUUDCXAXIXEUUCXJUHUIUUDCXQXA
      WFWGWHWIABCDEYTWSFXQXAIUKXKWJXLULWHWKWLWMWNGHEWOWPWQ $.
  $}

  ${
    $d w x y z $.  $d A w x y $.
    $( An alternative expression for the transitive closure of a class,
       assuming Regularity.  A set ` x ` is contained in the transitive closure
       of ` A ` iff we can construct an ` e. ` -chain from ` x ` to an element
       of ` A ` .  This weak definition is primarily useful for proving
       ~ elttcirr .  (Contributed by Matthew House, 6-Apr-2026.) $)
    dfttc4 $p |- TC+ A = { x | E. y ( ( A i^i y ) =/= (/) /\
        A. z e. y ( ( z i^i y ) = (/) -> z = x ) ) } $=
      ( vw cv cin c0 wne wceq weq wi wral wa wex wss ax-mp wcel vex cvv cab wtr
      cttc eqid dfttc4lem2 ttcmin equequ2 imbi2d ralbidv anbi2d elab wrex inex2
      exbidv ttcid ssrin ssn0 mpan zfreg sylancr wel simpl elin2d inass elinel1
      ttctr2 syl dfss2 sylib ineq1d eqtr3id eqeq1d biimpa ineq1 equequ1 imbi12d
      rspcv com23 sylc com12 eleq1w biimpcd adantr sylcom imp rexlimdvaa elin1d
      mpan9 exlimiv sylbi ssriv eqssi ) DUCZDBFZGZHIZCFZWNGZHJZCAKZLZCWNMZNZBOZ
      AUAZDXEPXEUBNWMXEPABCDXEXEUDUEDXEUFQEXEWMEFZXERWPWSCEKZLZCWNMZNZBOZXFWMRZ
      XDXKAXFESAEKZXCXJBXMXBXIWPXMXAXHCWNXMWTXGWSAECUGUHUIUJUNUKXJXLBXJWMWNXFWP
      AFZWMWNGZGZHJZAXOULZXIXFXORZWPXOTRXOHIZXRWNWMBSUMWOXOPZWPXTDWMPYADUODWMWN
      UPQWOXOUQURAXOTUSUTXIXQXSAXOXIXNXORZXQNZXSXIYCXMXSYCXIXMYCABVAZXNWNGZHJZX
      IXMLYCWMWNXNYBXQVBVCYBXQYFYBXPYEHYBXPXNWMGZWNGYEXNWMWNVDYBYGXNWNYBXNWMPZY
      GXNJYBXNWMRYHXNWMWNVEXNDVFVGXNWMVHVIVJVKVLVMYDXIYFXMXHYFXMLCXNWNWTWSYFXGX
      MWTWRYEHWQXNWNVNVLCAEVOVPVQVRVSVTYBXMXSLXQXMYBXSAEXOWAWBWCWDWEWFWHWGWIWJW
      KWL $.
  $}

  ${
    $d A w x y $.
    $( Irreflexivity of ` A e. TC+ B ` relationship.  This is a consequence of
       Regularity, but it does not require Transitive Containment.  We use the
       alternative expression ~ dfttc4 to construct a set in which ` A ` is
       both ` e. ` -minimal and not ` e. ` -minimal.  (Contributed by Matthew
       House, 6-Apr-2026.) $)
    elttcirr $p |- -. A e. TC+ A $=
      ( vy vw vx cttc wcel cv cin c0 wne wceq wi wral wa wex wrex cvv vex ineq1
      eqeq1d wss inss2 ssn0 mpan zfreg sylancr rexraleqim sylan wn neneq adantr
      weq pm2.65i nex eqeq2 imbi2d ralbidv anbi2d exbidv dfttc4 elab2g ibi mto
      ) AAEZFZABGZHZIJZCGZVFHZIKZVIAKZLZCVFMZNZBOZVOBVOVGIKZVHDGZVFHZIKZDVFPZVN
      VQVHVFQFVFIJZWABRVGVFUAVHWBAVFUBVGVFUCUDDVFQUEUFVTVKVQCDVFACDULZVJVSIVIVR
      VFSTVRAKZVSVGIVRAVFSTUGUHVHVQUIVNVGIUJUKUMUNVEVPVHVKWCLZCVFMZNZBOVPDAVDVD
      WDWGVOBWDWFVNVHWDWEVMCVFWDWCVLVKVRAVIUOUPUQURUSDBCAUTVAVBVC $.
  $}

  ${
    $d x y z $.  $d A x y $.
    $( The transitive closure of a set is a set, assuming Transitive
       Containment.  (Contributed by Matthew House, 6-Apr-2026.) $)
    ttcexg $p |- ( A e. V -> TC+ A e. _V ) $=
      ( vy vx vz wcel cv wss wtr wa wex cttc cvv sseq1 anbi1d exbidv wi wal vex
      wceq w3a tz9.1 3simpa eximii vtoclg ttcmin ssexg sylancl exlimiv syl ) AB
      FACGZHZUKIZJZCKZALZMFZDGZUKHZUMJZCKUODABURATZUTUNCVAUSULUMURAUKNOPUSUMURE
      GZHVBIJUKVBHQERZUAUTCCEURDSUBUSUMVCUCUDUEUNUQCUNUPUKHUKMFUQAUKUFCSUPUKMUG
      UHUIUJ $.
  $}

  $( A class is a set iff its transitive closure is a set, assuming Transitive
     Containment.  (Contributed by Matthew House, 6-Apr-2026.) $)
  ttcexbi $p |- ( A e. _V <-> TC+ A e. _V ) $=
    ( cvv wcel cttc ttcexg ttcexrg impbii ) ABCADBCABEABFG $.

  $( The transitive closure of a set ` A ` is ` ( TC `` A ) ` , assuming
     Transitive Containment.  (Contributed by Matthew House, 6-Apr-2026.) $)
  dfttc3g $p |- ( A e. V -> TC+ A = ( TC ` A ) ) $=
    ( wcel cttc cvv ctc cfv wceq ttcexg dfttc3gw syl ) ABCADZECLAFGHABIAEJK $.

  $( A transitive closure contains ` (/) ` as an element iff it is nonempty,
     assuming Regularity and Transitive Containment.  (Contributed by Matthew
     House, 6-Apr-2026.) $)
  ttc0el $p |- ( A =/= (/) <-> (/) e. TC+ A ) $=
    ( c0 wne cttc wcel ttc00 necon3bii wtr ttctr tr0el mpan2 ne0i impbii bitri
    ) ABCADZBCZBOEZABOBAFGPQPOHQAIOJKOBLMN $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Stronger axioms of regularity
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section contains some experiments related to the Axiom of Regularity
  ~ ax-reg .  As written, ~ ax-reg cannot guarantee that all sets are
  well-founded unless we further assume ~ ax-inf / ~ ax-inf2 ; in particular,
  ~ ax-reg alone is insufficient to assert that every set has a transitive
  closure ( ~ tz9.1 ), even though this is true among the hereditarily finite
  sets.

  The underlying cause of this issue is that ~ ax-reg requires a witness set to
  detect non-well-foundedness, but if all sets are hereditarily finite, then
  there may be no such witness set for an infinite descending ` e. ` -chain.
  The question is, how can we strengthen ~ ax-reg so that we get a true "Axiom
  of Foundation" even in the absence of ~ ax-inf / ~ ax-inf2 (e.g., so that we
  can prove ~ unir1 ` U. ( R1 " On ) = _V ` )?

  There are a few possible solutions.  First, we can directly strengthen
  ~ ax-reg into ~ ax-regs , which asserts that every class ` { x | ph } ` has
  an ` e. ` -minimal element.  Second, we can keep ~ ax-reg and add ~ ax-tco ,
  which asserts that every set is a member of a transitive set.  Third, we can
  replace ~ ax-reg with a set-induction axiom ~ mh-setind .  Fourth, we can
  take ~ unir1 as an axiom and derive everything from that.  This list is far
  from exhaustive.

  In this section, we prove that these four listed principles are equivalent.
  We see that ~ ax-regs implies the other three principles: ~ ax-reg + ~ ax-tco
  via ~ axreg + ~ tz9.1regs , ~ mh-setind via ~ setindregs , and ~ unir1 via
  ~ unir1regs .  So we just have to show that ~ ax-regs is implied by each of
  the other three.

  Some questions:  When expanded to primitives, what is the shortest single
  axiom equivalent to these, over ZF minus ~ ax-reg and ~ ax-inf / ~ ax-inf2 ?
  One candidate is ~ mh-setind , with 19 primitives.  What is the shortest
  single axiom not using any wff variables?  The conjunction of ~ ax-reg +
  ~ ax-tco , expanded using ~ mh-regprimbi and slightly simplified, comes out
  to 42 primitives.  Can we do better?
$)

  ${
    $d x y $.  $d ph y $.
    $( Principle of set induction ~ setind , written with primitive symbols.
       (Contributed by Matthew House, 4-Mar-2026.) $)
    mh-setind $p |- ( A. y ( A. x ( x e. y -> ph ) ->
        A. x ( x = y -> ph ) ) -> ph ) $=
      ( wel wi wal weq cv cab wss wcel cvv wceq setind ssab wsb df-clab imbi12i
      sb6 bitri albii abv 3imtr3i 19.21bi ) BCDAEBFZBCGAEBFZEZCFZABCHZABIZJZUIU
      JKZEZCFUJLMUHABFCUJNUMUGCUKUEULUFABUIOULABCPUFACBQABCSTRUAABUBUCUD $.
  $}

  ${
    $d x z $.  $d y z $.  $d ph z $.
    $( A version of ~ mh-setind with no distinct variable conditions.
       (Contributed by Matthew House, 5-Mar-2026.)
       (New usage is discouraged.) $)
    mh-setindnd $p |- ( A. y ( A. x ( x e. y -> ph ) ->
        A. x ( x = y -> A. y ph ) ) -> ph ) $=
      ( vz wel wi wal weq alimi elequ2 a1i embantd spsd nfnae naecoms wnf nfimd
      sp nfald wb imim2i imim1i elirrv mtbii pm2.21d wn dveel1 nf5d nfa1 nfeqf1
      wa nfeqf2 nfan1 imbi1d albid equequ2 imbi12d ex cbvaldw mh-setind 19.21bi
      adantl biimtrrdi pm2.61i syl ) BCEZAFZBGZBCHZACGZFZBGZFZCGVFVJFZBGZVLFZCG
      ZAVMVPCVOVHVLVNVGBVJAVFACRZUAIUBIVIBGZVQAFVSVPACVSVOVLAVIVNBVIVFVJVIBBEVF
      BUCBCBJUDUEIVSVKABVSVIVJAVIBRVJAFVSVRKLMLMVSUFZVQBDEZVJFZBGZBDHZVJFZBGZFZ
      DGZAVTWGVPDCBCCNZVTWCWFCVTWBCBBCBNZVTWAVJCVTWACWIWAWACGFCBCBDUGOUHVJCPVTA
      CUIKZQSVTWECBWJVTWDVJCWDCPCBCBDUJOWKQSQVTDCHZWGVPTVTWLUKZWCVOWFVLWMWBVNBV
      TWLBWJBCDULUMZWLWBVNTVTWLWAVFVJDCBJUNVBUOWMWEVKBWNWLWEVKTVTWLWDVIVJDCBUPU
      NVBUOUQURUSWHACVJBDUTVAVCVDVE $.
  $}

  ${
    $d r u w x y z $.  $d v x $.  $d s t u $.  $d ph r u w y z $.
    $d ph u v y z $.
    regsfromregtco.1 $e |- ( E. y y e. w ->
        E. y ( y e. w /\ A. z ( z e. y -> -. z e. w ) ) ) $.
    regsfromregtco.2 $e |- E. u ( v e. u /\
        A. t ( t e. u -> A. s ( s e. t -> s e. u ) ) ) $.
    $( Derivation of ~ ax-regs from ~ ax-reg + ~ ax-tco .  (Contributed by
       Matthew House, 4-Mar-2026.) $)
    regsfromregtco $p |- ( E. x ph -> E. y ( A. x ( x = y -> ph ) /\
        A. z ( z e. y -> -. A. x ( x = z -> ph ) ) ) ) $=
      ( vr wsb wex wel wn wi wal wa cv weq wtr vex elequ1 sbequ anbi12d adantlr
      spcev crab rabex wceq wcel eleq2 elrab bitrdi exbidv notbid imbi2d albidv
      imbi12d vtocl syl wb imnan trel imp anass1rs imbibi mpsyl pm5.74da anim2i
      biimpar exp44 com3l imp4c eximdv ad2antlr mpd wss wral dftr3 df-ss ralbii
      ex df-ral 3bitri anbi2i exbii mpbir exlimiiv exlimiv nfv sb8ef bicomi sb6
      notbii imbi2i albii anbi12i 3imtr3i ) ABFMZFNZABCMZDCOZABDMZPZQZDRZSZCNZA
      BNZBCUAAQBRZXDBDUAAQBRZPZQZDRZSZCNXAXJFFGOZGTZUBZSZXAXJQGYAXAXJYAXASZCGOZ
      XCSZXDDGOZXESZPZQZDRZSZCNZXJYBYDCNZYKXRXAYLXTYDXRXASCFTFUCCFUAYCXRXCXACFG
      UDACFBUEUFUHUGCEOZCNZYMXDDEOZPZQZDRZSZCNZQYLYKQEABLMZLXSUIZUUALXSGUCUJETZ
      UUBUKZYNYLYTYKUUDYMYDCUUDYMCTZUUBULYDUUCUUBUUEUMUUAXCLUUEXSALCBUEUNUOZUPU
      UDYSYJCUUDYMYDYRYIUUFUUDYQYHDUUDYPYGXDUUDYOYFUUDYODTZUUBULYFUUCUUBUUGUMUU
      AXELUUGXSALDBUEUNUOUQURUSUFUPUTJVAVBXTYKXJQXRXAXTYJXICXTYCXCYIXIXCXTYCYIX
      IQXCXTYCYIXIXTYCSZYISXHXCUUHXHYIUUHXGYHDUUHXDXFYGYEXFQYGVCUUHXDSYEXFYGVCY
      EXEVDXTXDYCYEXTXDYCSYEXSUUGUUEVEVFVGYEXFYGVHVIVJUSVLVKVMVNVOVPVQVRWDYAGNX
      RHGOIHOIGOQIRZQHRZSZGNKYAUUKGXTUUJXRXTHTZXSVSZHXSVTUUIHXSVTUUJHXSWAUUMUUI
      HXSIUULXSWBWCUUIHXSWEWFWGWHWIWJWKXKXBABFAFWLWMWNXIXQCXCXLXHXPABCWOXGXODXF
      XNXDXEXMABDWOWPWQWRWSWHWT $.
    $( $j usage 'regsfromregtco' avoids 'ax-reg' 'ax-inf' 'ax-inf2' 'ax-cc'
       'ax-dc' 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d x y z $.  $d ph z $.
    regsfromsetind.1 $e |- ( A. y ( A. x ( x e. y -> -. ph ) ->
        A. x ( x = y -> -. ph ) ) -> -. ph ) $.
    $( Derivation of ~ ax-regs from ~ mh-setind .  (Contributed by Matthew
       House, 4-Mar-2026.) $)
    regsfromsetind $p |- ( E. x ph -> E. y ( A. x ( x = y -> ph ) /\
        A. z ( z e. y -> -. A. x ( x = z -> ph ) ) ) ) $=
      ( wex wel wn wi wal weq wa nfia1 nfal nfn con2i exlimi exnalimn nfv nfna1
      nfim elequ1 wsb sbequ12 sb6 bitrdi notbid imbi12d cbvalv1 alinexa xchbinx
      sbalex imbi12i con2b bitri albii xchbinxr sylibr ) ABFBCGZAHZIZBJZBCKZUTI
      ZBJZIZCJZHZVCAIBJZDCGZBDKZAIZBJZHZIZDJZLCFZAVHBVGBVFBCVAVDBMNOVGAEPQVQVIV
      PHIZCJVGVIVPCRVFVRCVFVPVIHZIVRVBVPVEVSVAVOBDVADSVJVNBVJBSVLBTUAVKUSVJUTVN
      BDCUBVKAVMVKAABDUCVMABDUDABDUEUFUGUHUIVEVCALBFVIVCABUJABCULUKUMVPVIUNUOUP
      UQUR $.
    $( $j usage 'regsfromsetind' avoids 'ax-reg' 'ax-inf' 'ax-inf2' 'ax-cc'
       'ax-dc' 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d x y z $.  $d ph y z $.
    regsfromunir1.1 $e |- U. ( R1 " On ) = _V $.
    $( Derivation of ~ ax-regs from ~ unir1 .  (Contributed by Matthew House,
       4-Mar-2026.) $)
    regsfromunir1 $p |- ( E. x ph -> E. y ( A. x ( x = y -> ph ) /\
        A. z ( z e. y -> -. A. x ( x = z -> ph ) ) ) ) $=
      ( wex cv crnk cfv cima wceq wrex wcel wn wi wal weq c0 con0 ax-mp cab wel
      cint wa wne wss cr1 cuni wf rankf fimass wfn wb ffn cvv sseqtrri fnimaeq0
      ssv mp2an necon3bii biimpri sylancr fvelimab 3imtr3i vex eleqtrri rankelb
      onint abn0 eleq2 biimpd fnfvima mp3an12 onnmin con2i syl56 alrimiv reximi
      df-rex wsb df-clab sb6 bitri notbii imbi2i albii anbi12i exbii sylbb 3syl
      ) ABFZCGZHIZHABUAZJZUCZKZCWNLZDCUBZDGZWNMZNZOZDPZCWNLZBCQAOBPZWSBDQAOBPZN
      ZOZDPZUDZCFZWNRUEZWPWOMZWKWRXMWOSUFZWORUEZXNUGSJUHZSHUIZXOUJXQSHWNUKTZXPX
      MWORWNRHXQULZWNXQUFZWORKWNRKUMXRXTUJXQSHUNTZWNUOXQWNUREUPZXQWNHUQUSUTVAWO
      VHVBABVIXTYAXNWRUMYBYCCXQWNWPHVCUSVDWQXDCWNWQXCDWSWTHIZWMMZWQYDWPMZXBWLXQ
      MWSYEOWLUOXQCVEEVFWTWLVGTWQYEYFWMWPYDVJVKXAYFXAXOYDWOMZYFNXSXTYAXAYGYBYCX
      QWNHWTVLVMWOYDVNVBVOVPVQVRXEWLWNMZXDUDZCFXLXDCWNVSYIXKCYHXFXDXJYHABCVTXFA
      CBWAABCWBWCXCXIDXBXHWSXAXGXAABDVTXGADBWAABDWBWCWDWEWFWGWHWIWJ $.
    $( $j usage 'regsfromunir1' avoids 'ax-reg' 'ax-inf' 'ax-inf2' 'ax-cc'
       'ax-dc' 'ax-ac' 'ax-ac2'; $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Short axioms written in primitive symbols
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d ph x y z $.  $d A x z $.  $d B x y z $.  $d F x y z $.
    mh-inf3f1.1 $e |- ( ph -> F : A -1-1-> A ) $.
    mh-inf3f1.2 $e |- ( ph -> B e. ( A \ ran F ) ) $.
    $( A variant of ~ inf3 .  If ` F ` is a one-to-one function from ` A ` into
       itself, and ` B ` is an element outside its range, then
       ` ( rec ( F , B ) |`` _om ) ` is a one-to-one function yielding an
       infinite sequence of distinct elements from ` A ` .  If ` A ` is a set,
       we can use this theorem to prove ` _om e. _V ` via ~ f1dmex .
       (Contributed by Matthew House, 13-Apr-2026.) $)
    mh-inf3f1 $p |- ( ph -> ( rec ( F , B ) |` _om ) : _om -1-1-> A ) $=
      ( vy vx vz com cfv wne wral wcel c0 wceq fveq2 eleq1d syl wa crdg cres wf
      wel cv wi wf1 csuc weq crn cdif fr0g eqeltrd eldifad f1f ffvelcdmda frsuc
      imbitrrid expd finds2 com12 ralrimiv wfn frfnom mpbiran sylibr raleqbi1dv
      ffnfv neeq1d ral0 a1i nfra1 nfan ad3antlr neeq2d wrex peano2b elnn ancoms
      sylanb ad4ant24 nnsuc sylan simp-4r simprr simpllr eqeltrrd word wb nnord
      ad5antlr ordsucelsuc mpbird rspcdva simp-5l ad4antr simprl sylc necon3bid
      f1fveq syl12anc sylan9eqr adantl neeqtrrd rexlimddv ffnd adantr fnfvelrnd
      nfv elneeldif syl2anc ad2antrr pm2.61ne eqnetrd exp31 rsp syl6com adantrd
      ralrimia ralrimivv con0 wss omsson onelfvnef1 mp3an2 ) AJBDCUAJUBZUCZGHUD
      HUEZYFKZGUEZYFKZLZUFZGJMHJMZJBYFUGZAYIBNZHJMZYGAYPHJYHJNZAYPYPOYFKZBNIUEZ
      YFKZBNZYTUHZYFKZBNZAHIYHOPZYIYSBYHOYFQZRHIUIZYIUUABYHYTYFQZRYHUUCPZYIUUDB
      YHUUCYFQZRAYSBDUJZAYSCBUULUKZACUUMNYSCPFCUUMDULSFUMZUNYTJNZAUUBUUEAUUBTUU
      EUUOUUADKZBNABBUUADABBDUGZBBDUCEBBDUOSZUPUUOUUDUUPBCYTDUQZRURUSUTZVAVBYGY
      FJVCYQCDVDHJBYFVHVEVFZAYMHGJJAYRYMYJJNZYRAYLGYHMZYMUVCYSYKLZGOMZUUAYKLZGY
      TMZUUDYKLZGUUCMZAHIYLUVDGYHOUUFYIYSYKUUGVIVGYLUVFGYHYTUUHYIUUAYKUUIVIVGYL
      UVHGYHUUCUUJYIUUDYKUUKVIVGUVEAUVDGVJVKAUUOUVGUVIUFAUUOUVGUVIAUUOTZUVGTZUV
      HGUUCUVJUVGGUVJGXIUVFGYTVLVMUVKYJUUCNZTZUUDUUPYKUUOUUDUUPPAUVGUVLUUSVNUVM
      UUPYKLZUUPYSLZYJOYJOPYKYSUUPYJOYFQVOUVMYJOLZTZYJYHUHZPZUVNHJUVMUVBUVPUVSH
      JVPUUOUVLUVBAUVGUUOUUCJNZUVLUVBYTVQUVLUVTUVBYJUUCVRVSVTWAHYJWBWCUVQYRUVST
      ZTZUUPYIDKZYKUWBUUPUWCLZUUAYILZUWBUVFUWEGYTYHGHUIYKYIUUAYJYHYFQVOUVJUVGUV
      LUVPUWAWDUWBHIUDZUVRUUCNZUWBYJUVRUUCUVQYRUVSWEUVKUVLUVPUWAWFWGUWBYTWHZUWF
      UWGWIUUOUWHAUVGUVLUVPUWAYTWJWKYHYTWLSWMWNUWBUUQUUBYPUWDUWEWIUWBAUUQAUUOUV
      GUVLUVPUWAWOZESUVJUUBUVGUVLUVPUWAAJBYTYFUVAUPZWPUWBYRAYPUVQYRUVSWQUWIUUTW
      RUUQUUBYPTTUUPUWCUUAYIBBUUAYIDWTWSXAWMUWAYKUWCPUVQUVSYRYKUVRYFKUWCYJUVRYF
      QCYHDUQXBXCXDXEUVJUVOUVGUVLUVJUUPUULNYSUUMNZUVOUVJBUUADADBVCUUOABBDUURXFX
      GUWJXHAUWKUUOUUNXGUULBUUPYSXJXKXLXMXNXSXOVAUTYLGYHXPXQXRXTYGJYAYBYNYOYCHG
      JBYFYDYEXK $.
    $( $j usage 'mh-inf3f1' avoids 'ax-rep' 'ax-pow' 'ax-reg' 'ax-inf'
       'ax-inf2'; $)
  $}

  ${
    $d x y z $.
    mh-inf3sn.1 $e |- E. x ( (/) e. x /\ A. y e. x { y } e. x ) $.
    $( Version of ~ inf3 for the set of Zermelo ordinals ` (/) ` ,
       ` { (/) } ` , ` { { (/) } } ` , ` { { { (/) } } } ` , etc., where the
       successor of ` y ` is ` { y } ` .  Unlike ~ inf3 , the proof does not
       require ~ ax-reg , since the singleton properties ~ snnz and ~ sneqr are
       sufficient to guarantee that all elements of the sequence are distinct.
       (Contributed by Matthew House, 13-Apr-2026.) $)
    mh-inf3sn $p |- _om e. _V $=
      ( vz c0 cv wcel csn wral wa com cvv cmpt crdg cres wf1 wceq weq wi vex wn
      simpr sneqr rgen2w eqid sneq f1mpt sylanblrc crn simpl wrex necomd neneqd
      wel snnzg nrex vsnex elrnmpti mtbir a1i eldifd mh-inf3f1 sylancl exlimiiv
      f1dmex ) EAFZGZBFZHZVFGBVFIZJZKLGZAVKKVFBVFVIMZENKOZPVFLGVLVKVFEVMVKVJVID
      FZHZQBDRSZDVFIBVFIVFVFVMPVGVJUBVQBDVFVFVHVOBTUCUDBDVFVFVIVPVMVMUEZVHVOUFU
      GUHVKEVFVMUIZVGVJUJEVSGZUAVKVTEVIQZBVFUKWABVFBAUNZEVIWBVIEVHVFUOULUMUPBVF
      VIEVMVRBUQURUSUTVAVBATKVFLVNVEVCCVD $.
    $( $j usage 'mh-inf3sn' avoids 'ax-pow' 'ax-reg' 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d w x $.  $d w y $.  $d w z $.
    $( Shortest possible version of ~ ax-pr in primitive symbols.  (Contributed
       by Matthew House, 13-Apr-2026.) $)
    mh-prprimbi $p |- ( E. z A. w ( ( w = x \/ w = y ) -> w e. z ) <->
        -. A. z ( x e. z -> -. y e. z ) ) $=
      ( weq wo wel wi wal wa wn jaob albii 19.26 elequ1 equsalvw anbi12i 3bitri
      wex exbii exnalimn bitri ) DAEZDBEZFDCGZHZDIZCSACGZBCGZJZCSUHUIKHCIKUGUJC
      UGUCUEHZUDUEHZJZDIUKDIZULDIZJUJUFUMDUCUEUDLMUKULDNUNUHUOUIUEUHDADACOPUEUI
      DBDBCOPQRTUHUICUAUB $.
    $( $j usage 'mh-prprimbi' avoids 'ax-ext' 'ax-sep' 'ax-nul' 'ax-pr'
       'ax-reg'; $)
  $}

  ${
    $d u v w x z $.  $d u v w y z $.
    $( Shortest possible version of ~ ax-un in primitive symbols.  (Contributed
       by Matthew House, 13-Apr-2026.) $)
    mh-unprimbi $p |- ( E. y A. z ( E. w ( z e. w /\ w e. x ) -> z e. y ) <->
        -. A. y -. A. z ( z e. x -> A. w ( w e. z -> w e. y ) ) ) $=
      ( vv vu wel wa wex wi wal weq elequ1 imbi12d elequ12 adantl adantr bitrid
      wn wb imbi2d elequ2 imbi1d alcomw impexp bi2.04 ancoms 19.23v albii exbii
      cbval2vw 3bitr4i 19.21v 3bitr3i df-ex bitri ) CDGZDAGZHZDICBGZJZCKZBICAGZ
      DCGZDBGZJZDKJZCKZBIVHSBKSVBVHBUSUTJZDKZCKZVCVFJZDKZCKZVBVHEFGZFAGZEBGZJZJ
      ZFKEKVSEKFKVKVNVSCFGZVPUTJZJEDGZURVQJZJEFDCECLZVOVTVRWAECFMWDVQUTVPECBMUA
      NFDLZVOWBVRWCFDEUBWEVPURVQFDAMUCNUDVIVSCDEFVIUQURUTJZJCELZDFLZHZVSUQURUTU
      EWIUQVOWFVRCEDFOWIURVPUTVQWHURVPTWGDFAMPWGUTVQTWHCEBMQNNRUKVLVSCDFEVLVDVC
      VEJZJCFLZDELZHZVSVCVDVEUFWMVDVOWJVRWLWKVDVOTDECFOUGWMVCVPVEVQWKVCVPTWLCFA
      MQWLVEVQTWKDEBMPNNRUKULVJVACUSUTDUHUIVMVGCVCVFDUMUIUNUJVHBUOUP $.
    $( $j usage 'mh-unprimbi' avoids 'ax-11' 'ax-ext' 'ax-sep' 'ax-nul' 'ax-pr'
       'ax-un' 'ax-reg'; $)
  $}

  ${
    $d x y z $.
    $( Shortest possible version of ~ ax-reg in primitive symbols.  The
       equivalence is nontrivial, but it still follows solely from the axioms
       of predicate calculus.  (Contributed by Matthew House, 13-Apr-2026.) $)
    mh-regprimbi $p |- ( ( E. y y e. x ->
        E. y ( y e. x /\ A. z ( z e. y -> -. z e. x ) ) ) <->
        -. A. y -. A. z ( ( y e. x -> z e. y ) -> -. z e. x ) ) $=
      ( wel wex wn wi wal elequ1 cbvexvw df-ex bitri imbi1i jarl alimdv con3rr3
      wa com12 con4d 3bitri pm4.71rd pm5.5 imbi1d albidv pm5.32i bitr2di exbidv
      pm5.74i ala1 alrimiv 19.2d biantrur pm4.83 ) BADZBEZUNCBDZCADZFZGZCHZQZBE
      ZGURCHZFZVBGZUNUPGZURGZCHZBEZVHFBHFUOVDVBUOUQCEVDUNUQBCBCAIJUQCKLMVEVDVIG
      ZVCVIGZVJQVIVDVBVIVDVAVHBVDVHUNVHQVAVDVHUNVDUNVHUNFZVHVCVLVGURCVGVLURUNUP
      URNROPSUAUNVHUTUNVGUSCUNVFUPURUNUPUBUCUDUEUFUGUHVKVJVCVHBVCVHBURVFCUIUJUK
      ULVCVIUMTVHBKT $.
    $( $j usage 'mh-regprimbi' avoids 'ax-ext' 'ax-sep' 'ax-nul' 'ax-pr'
       'ax-reg'; $)
  $}

  ${
    $d x y z $.
    $( Shortest possible axiom of infinity in primitive symbols.  Deriving
       ~ ax-inf or ~ ax-inf2 from this axiom requires ~ ax-ext , ~ ax-rep , and
       ~ ax-reg , see ~ inf3 and ~ inf0 .  (Contributed by Matthew House,
       13-Apr-2026.) $)
    mh-infprim1bi $p |- ( E. x ( x =/= (/) /\ x C_ U. x ) <->
        -. A. x -. A. y -. A. z ( ( y e. x -> y e. z ) -> -. z e. x ) ) $=
      ( cv c0 wne cuni wss wa wex wel wi wn exbidv bitrid pm5.74i albii 3bitr2i
      wal bitri exnelv a1bi 19.23v n0 pm2.21 biantrurd df-ss eluni biimt anbi1d
      wcel anbi12ci 19.26 pm4.83 exnalimn exbii df-ex ) ADZEFZURURGZHZIZAJBAKZB
      CKZLZCAKZMLCSMZBSZAJVHMASMVBVHAVBVCVEVFIZCJZLZBSZVCMZVJLZBSZIVKVNIZBSVHUS
      VOVAVLUSVMBJZUSLVMUSLZBSVOVQUSABUAUBVMUSBUCVRVNBVMUSVJUSVFCJVMVJCURUDVMVF
      VICVMVEVFVCVDUEUFNOPQRVAVCBDZUTUKZLZBSVLBURUTUGWAVKBVCVTVJVTVDVFIZCJVCVJC
      VSURUHVCWBVICVCVDVEVFVCVDUIUJNOPQTULVKVNBUMVPVGBVPVJVGVCVJUNVEVFCUOTQRUPV
      HAUQT $.
    $( $j usage 'mh-infprim1bi' avoids 'ax-pr' 'ax-un' 'ax-reg' 'ax-inf'
       'ax-inf2'; $)
  $}

  ${
    $d w x y z $.
    $( Shortest possible axiom of infinity in primitive symbols not requiring
       ~ ax-reg .  Deriving ~ ax-inf or ~ ax-inf2 from this axiom requires
       ~ ax-ext and ~ ax-rep , see ~ mh-inf3sn and ~ inf0 .  (Contributed by
       Matthew House, 13-Apr-2026.) $)
    mh-infprim2bi $p |- ( E. x ( (/) e. x /\ A. y e. x { y } e. x ) <->
        -. A. x -. A. y A. z ( A. w ( w e. y -> -. ( w e. x -> -. w = z ) ) ->
        y e. x ) ) $=
      ( c0 cv wcel csn wral wa wel weq wn wi wal cin cpw eleq1 imbi12d 3bitri
      wex sneq eleq1d cbvralvw df-ral bitri anbi2i cpr pwin raleqi pwsn 3bitrri
      ralin 0ex vsnex wceq 0elpw a1bi bitr4di snelpw ralpr 3bitr3i albii 19.28v
      vex ineq1d pweqd eleq2d imbi1d eleq1w elequ1 alcomw wss velpw df-ss velsn
      elin anbi2ci df-an imbi2i imbi1i 2albii exbii df-ex ) EAFZGZBFZHZWEGZBWEI
      ZJZAUADBKZDAKZDCLZMNMZNZDOZBAKZNZCOBOZAUAWTMAOMWKWTAWKWFCAKZCFZHZWEGZNZCO
      ZJZWGXCWEPZQZGZWRNZCOBOZWTWJXFWFWJXDCWEIXFWIXDBCWEBCLWHXCWEWGXBUBUCUDXDCW
      EUEUFUGWFXEJZCOXKBOZCOXGXLXMXNCWGWEQZGZWRNZBEXCUHZIZWRBXIIZXMXNXTWRBXCQZX
      OPZIXQBYAIXSWRBXIYBXCWEUIUJWRBYAXOUMXQBYAXRXBUKUJULXQWFXEBEXCUNCUOWGEUPZX
      QEXOGZWFNWFYCXPYDWRWFWGEXORWGEWERSYDWFWEUQURUSWGXCUPZXPXAWRXDYEXPXCXOGXAW
      GXCXORXBWECVEUTUSWGXCWERSVAWRBXIUEVBVCWFXECVDXKWGDFZHZWEPZQZGZWRNYFXIGZWM
      NCBDDCDLZXJYJWRYLXIYIWGYLXHYHYLXCYGWEXBYFUBVFVGVHVIBDLXJYKWRWMBDXIVJBDAVK
      SVLVBXKWSBCXJWQWRXJWGXHVMWLYFXHGZNZDOWQBXHVNDWGXHVOYNWPDYMWOWLYMYFXCGZWMJ
      WMWNJWOYFXCWEVQYOWNWMDXBVPVRWMWNVSTVTVCTWAWBTWCWTAWDUF $.
    $( $j usage 'mh-infprim2bi' avoids 'ax-11' 'ax-reg' 'ax-inf' 'ax-inf2'; $)
  $}

  ${
    $d x y z $.
    $( An axiom of infinity in primitive symbols not requiring ~ ax-reg .  This
       version of the axiom was designed by Stefan O'Rear for his zf2.nql
       program, see ~ https://github.com/sorear/metamath-turing-machines .  It
       directly implies ~ ax-inf , but deriving ~ ax-inf2 requires ~ ax-ext and
       ~ ax-rep , see ~ mh-inf3sn .  (Contributed by Matthew House,
       13-Apr-2026.) $)
    mh-infprim3bi $p |- ( E. y ( x e. y /\ A. z e. y { z } e. y ) <->
        -. A. y -. -. ( x e. y -> -. A. x ( x e. y -> -. A. z -. -. ( z e. y ->
        -. A. y -. ( ( y e. z -> y = x ) -> -. ( y = x -> y e. z ) ) ) ) ) ) $=
      ( wel cv csn wcel wral wa wex weq wi wn wb bitri df-an exbii df-ex 3bitri
      wal eleq1d cbvralvw dfclel dfcleq velsn bibi2i dfbi1 albii anbi2ci ralbii
      sneq wceq df-ral anbi2i ) ABDZCEZFZBEZGZCURHZIZBJUOUOCBDZBCDZBAKZLVDVCLML
      MZBTZMLMZMCTMZLATZMLMZBJVJMBTMVAVJBVAUOVIIVJUTVIUOUTAEZFZURGZAURHVHAURHVI
      USVMCAURCAKUQVLURUPVKUKUAUBVMVHAURVMUPVLULZVBIZCJVGCJVHCVLURUCVOVGCVOVBVF
      IVGVNVFVBVNVCURVLGZNZBTVFBUPVLUDVQVEBVQVCVDNVEVPVDVCBVKUEUFVCVDUGOUHOUIVB
      VFPOQVGCRSUJVHAURUMSUNUOVIPOQVJBRO $.
    $( $j usage 'mh-infprim3bi' avoids 'ax-sep' 'ax-nul' 'ax-pr' 'ax-reg'
       'ax-inf' 'ax-inf2'; $)
  $}

$( (End of Matthew House's mathbox.) $)
