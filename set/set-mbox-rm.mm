$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Rodolfo Medina
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Partitions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    prtlem60.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    prtlem60.2 $e |- ( ps -> ( th -> ta ) ) $.
    $( Lemma for ~ prter3 .  (Contributed by Rodolfo Medina, 9-Oct-2010.) $)
    prtlem60 $p |- ( ph -> ( ps -> ( ch -> ta ) ) ) $=
      ( wi a1i syldd ) ABCDEFBDEHHAGIJ $.
  $}

  ${
    bicomdd.1 $e |- ( ph -> ( ps -> ( ch <-> th ) ) ) $.
    $( Commute two sides of a biconditional in a deduction.  (Contributed by
       Rodolfo Medina, 19-Oct-2010.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
    bicomdd $p |- ( ph -> ( ps -> ( th <-> ch ) ) ) $=
      ( wb bicom imbitrdi ) ABCDFDCFECDGH $.
  $}

  ${
    jca2r.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jca2r.2 $e |- ( ps -> th ) $.
    $( Inference conjoining the consequents of two implications.  (Contributed
       by Rodolfo Medina, 17-Oct-2010.) $)
    jca2r $p |- ( ph -> ( ps -> ( th /\ ch ) ) ) $=
      ( wi a1i jcad ) ABDCBDGAFHEI $.
  $}

  ${
    jca3.1 $e |- ( ph -> ( ps -> ch ) ) $.
    jca3.2 $e |- ( th -> ta ) $.
    $( Inference conjoining the consequents of two implications.  (Contributed
       by Rodolfo Medina, 14-Oct-2010.) $)
    jca3 $p |- ( ph -> ( ps -> ( th -> ( ch /\ ta ) ) ) ) $=
      ( wa wi imp a1d jca2 ex ) ABDCEHIABHZDCENCDABCFJKGLM $.
  $}

  $( Lemma for ~ prter3 : a rearrangement of conjuncts.  (Contributed by
     Rodolfo Medina, 20-Oct-2010.) $)
  prtlem70 $p |- ( ( ( ( ps /\ et ) /\ ( ( ph /\ th ) /\ ( ch /\ ta ) ) )
                        /\ ph ) <-> ( ( ph /\ ( ps /\ ( ch /\ ( th /\ ta ) ) )
    ) /\ et ) ) $=
    ( wa anass anbi1i anandi ancom 3bitr4ri bitri 3bitri an4 anbi2i ) BFGZADGZC
    EGZGZGZAGZABDGZGZSGZFGZAUCSGZGZFGABCDEGZGGZGZFGABGZRGZSGZFGULTGZFGZUFUBUNUO
    FULRSHIUEUNFUDUMSABDJIIUBULFGZTGZFULGZTGZUPAQGZTGAUAGURUBAQTHUQVATABFHIUAAK
    LUQUSTULFKIUTFUOGUPFULTHFUOKMNLUEUHFAUCSHIUHUKFUGUJAUGBCGUIGUJBDCEOBCUIHMPI
    N $.

  ${
    ibdr.1 $e |- ( ph -> ( ch -> ( ps <-> ch ) ) ) $.
    $( Reverse of ~ ibd .  (Contributed by Rodolfo Medina, 30-Sep-2010.) $)
    ibdr $p |- ( ph -> ( ch -> ps ) ) $=
      ( bicomdd ibd ) ACBACBCDEF $.
  $}

  $( Lemma for ~ prter3 .  (Contributed by Rodolfo Medina, 19-Oct-2010.) $)
  prtlem100 $p |- ( E. x e. A ( B e. x /\ ph ) <->
                        E. x e. ( A \ { (/) } ) ( B e. x /\ ph ) ) $=
    ( cv wcel wa csn cdif wne anass eldifsn anbi1i ne0i pm4.71ri bitri 3bitr4ri
    c0 anbi2i rexbii2 ) DBEZFZAGZUCBCCRHIZUACFZUARJZGZUCGUEUFUCGZGUAUDFZUCGUEUC
    GUEUFUCKUIUGUCUACRLMUCUHUEUCUFUBGZAGUHUBUJAUBUFUADNOMUFUBAKPSQT $.

  ${
    $d u v x r $.  $d u v x s $.  $d u v x A $.
    $( Lemma for ~ prter1 , ~ prter2 , ~ prter3 and ~ prtex .  (Contributed by
       Rodolfo Medina, 25-Sep-2010.)  (Proof shortened by Mario Carneiro,
       11-Dec-2016.) $)
    prtlem5 $p |- ( [ s / v ] [ r / u ] E. x e. A ( u e. x /\ v e. x )
                        <-> E. x e. A ( r e. x /\ s e. x ) ) $=
      ( wel wa wrex weq elequ1 bi2anan9r rexbidv 2sbievw ) CAGZBAGZHZADIFAGZEAG
      ZHZADIBCFEBEJZCFJZHQTADUBORUAPSCFAKBEAKLMN $.
  $}

  $( Lemma for ~ prter2 .  (Contributed by Rodolfo Medina, 17-Oct-2010.) $)
  prtlem80 $p |- ( A e. B -> -. A e. ( C \ { A } ) ) $=
    ( wcel neldifsnd ) ABDACE $.

  ${
    $d x y z $.  $d x y w $.
    $( A closed form of ~ brabsb .  (Contributed by Rodolfo Medina,
       13-Oct-2010.) $)
    brabsb2 $p |- ( R = { <. x , y >. | ph }
                        -> ( z R w <-> [ z / x ] [ w / y ] ph ) ) $=
      ( copab wceq cv wbr cop wcel wsb breq df-br bitrdi vopelopabsb ) FABCGZHZ
      DIZEIZFJZTUAKRLZACEMBDMSUBTUARJUCTUAFRNTUAROPABCDEQP $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d ph x $.  $d ph y $.
    eqbrrdv2.1 $e |- ( ( ( Rel A /\ Rel B ) /\ ph )
                        -> ( x A y <-> x B y ) ) $.
    $( Other version of ~ eqbrrdiv .  (Contributed by Rodolfo Medina,
       30-Sep-2010.) $)
    eqbrrdv2 $p |- ( ( ( Rel A /\ Rel B ) /\ ph ) -> A = B ) $=
      ( wrel wa wceq cv wbr cop wcel df-br 3bitr3g eqrelrdv2 anabss5 ) DGEGHZAD
      EIRAHZBCDESBJZCJZDKTUAEKTUALZDMUBEMFTUADNTUAENOPQ $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Lemma for ~ prter3 .  (Contributed by Rodolfo Medina, 25-Sep-2010.) $)
    prtlem9 $p |- ( A e. B -> E. x e. B [ x ] .~ = [ A ] .~ ) $=
      ( wcel cv wceq wrex cec risset eceq1 reximi sylbi ) BCEAFZBGZACHNDIBDIGZA
      CHABCJOPACNBDKLM $.
  $}

  ${
    $d v w $.  $d v z $.  $d v A $.  $d v .~ $.
    $( Lemma for ~ prter3 .  (Contributed by Rodolfo Medina, 14-Oct-2010.)
       (Revised by Mario Carneiro, 12-Aug-2015.) $)
    prtlem10 $p |- ( .~ Er A -> ( z e. A -> ( z .~ w <->
        E. v e. A ( z e. [ v ] .~ /\ w e. [ v ] .~ ) ) ) ) $=
      ( wer cv wcel wbr cec wa wrex wb wi simpr simpl erref breq1 vex elec expr
      weq anbi12d rspcev syl2anc simplll simprl simprr ertr3d rexlimdva2 impbid
      anbi12i rexbii bitr4di ex ) DEFZAGZDHZUQBGZEIZUQCGZEJZHZUSVBHZKZCDLZMUPUR
      KZUTVAUQEIZVAUSEIZKZCDLZVFVGUTVKVGURUQUQEIZUTVKNUPUROZVGUQEDUPURPVMQURVLU
      TVKVJVLUTKCUQDCAUBVHVLVIUTVAUQUQERVAUQUSERUCUDUAUEVGVJUTCDVGVADHZKZVJKUQV
      AUSEDUPURVNVJUFVOVHVIUGVOVHVIUHUIUJUKVEVJCDVCVHVDVIUQVAEASCSZTUSVAEBSVPTU
      LUMUNUO $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x .~ $.
    $( Lemma for ~ prter2 .  (Contributed by Rodolfo Medina, 12-Oct-2010.) $)
    prtlem11 $p |- ( B e. D ->
                        ( C e. A -> ( B = [ C ] .~ -> B e. ( A /. .~ ) ) ) ) $=
      ( vx wcel cec wceq cqs wa cv wrex eceq1 rspceeqv elqsg imbitrrid expd ) B
      DGZCAGZBCEHZIZBAEJGZTUBKUCSBFLZEHZIFAMFCAUEUABUDCENOFABEDPQR $.
  $}

  ${
    $d x y $.
    $( Lemma for ~ prtex and ~ prter3 .  (Contributed by Rodolfo Medina,
       13-Oct-2010.) $)
    prtlem12 $p |- ( .~ = { <. x , y >. | E. u e. A ( x e. u /\ y e. u ) }
                        -> Rel .~ ) $=
      ( wel wa wrex copab wceq wrel relopabv releq mpbiri ) EACFBCFGCDHZABIZJEK
      PKOABLEPMN $.
  $}

  ${
    $d u v x y A $.  $d v w x y $.  $d v x y z $.
    prtlem13.1 $e |- .~ = { <. x , y >. | E. u e. A ( x e. u /\ y e. u ) } $.
    $( Lemma for ~ prter1 , ~ prter2 , ~ prter3 and ~ prtex .  (Contributed by
       Rodolfo Medina, 13-Oct-2010.)  (Revised by Mario Carneiro,
       12-Aug-2015.) $)
    prtlem13 $p |- ( z .~ w <-> E. v e. A ( z e. v /\ w e. v ) ) $=
      ( wel wa wrex cv vex weq elequ2 anbi12d cbvrexvw elequ1 bi2anan9 rexbidv
      bitrid braba ) AFJZBFJZKZFGLZCEJZDEJZKZEGLZABCMDMHCNDNUGAEJZBEJZKZEGLACOZ
      BDOZKZUKUFUNFEGFEOUDULUEUMFEAPFEBPQRUQUNUJEGUOULUHUPUMUIACESBDESTUAUBIUC
      $.

    $d u v w x y z A $.  $d w z .~ $.
    $( Lemma for ~ prtex , ~ prter2 and ~ prter3 .  (Contributed by Rodolfo
       Medina, 14-Oct-2010.)  (Revised by Mario Carneiro, 12-Aug-2015.) $)
    prtlem16 $p |- dom .~ = U. A $=
      ( vz vw vv cdm cuni cv wcel wbr wex wel wa wrex vex eldm prtlem13 adantrr
      exbii elunii ancoms rexlimiva exlimiv eluni2 elequ1 anbi2d pm4.24 bitr4di
      weq rexbidv spcev sylbi impbii 3bitri eqriv ) GEJZDKZGLZUTMVBHLENZHOGIPZH
      IPZQZIDRZHOZVBVAMZHVBEGSZTVCVGHABGHICDEFUAUCVHVIVGVIHVFVIIDILZDMZVDVIVEVD
      VLVIVBVKDUDUEUBUFUGVIVDIDRZVHIVBDUHVGVMHVBVJHGUMZVFVDIDVNVFVDVDQVDVNVEVDV
      DHGIUIUJVDUKULUNUOUPUQURUS $.

    $( Lemma for ~ prter2 and also a property of partitions .  (Contributed by
       Rodolfo Medina, 15-Oct-2010.)  (Revised by Mario Carneiro,
       12-Aug-2015.) $)
    prtlem400 $p |- -. (/) e. ( U. A /. .~ ) $=
      ( c0 cuni cqs wcel wne neirr cdm wceq prtlem16 elqsn0 mpan mto ) GDHZEIJZ
      GGKZGLEMSNTUAABCDEFOSGEPQR $.
  $}

  $( Introduce the partition predicate. $)
  $c Prt $.

  $( Extend the definition of a wff to include the partition predicate. $)
  wprt $a wff Prt A $.

  ${
    $d x y A $.
    $( Define the partition predicate.  (Contributed by Rodolfo Medina,
       13-Oct-2010.) $)
    df-prt $a |- ( Prt A <-> A. x e. A A. y e. A ( x = y \/
                                                ( x i^i y ) = (/) ) ) $.
  $}

  ${
    $d x y A $.  $d x y .~ $.  $d x y X $.
    $( The quotient set of an equivalence relation is a partition.
       (Contributed by Rodolfo Medina, 13-Oct-2010.) $)
    erprt $p |- ( .~ Er X -> Prt ( A /. .~ ) ) $=
      ( vx vy wer cv wceq cin c0 wo cqs wral wprt wa simpl simprl simprr qsdisj
      wcel ralrimivva df-prt sylibr ) CBFZDGZEGZHUEUFIJHKZEABLZMDUHMUHNUDUGDEUH
      UHUDUEUHTZUFUHTZOZOAUEUFBCUDUKPUDUIUJQUDUIUJRSUADEUHUBUC $.
  $}

  ${
    $d u v w x y z $.  $d x y z A $.
    $( Lemma for ~ prter1 , ~ prter2 and ~ prtex .  (Contributed by Rodolfo
       Medina, 13-Oct-2010.) $)
    prtlem14 $p |- ( Prt A -> ( ( x e. A /\ y e. A )
                                -> ( ( w e. x /\ w e. y ) -> x = y ) ) ) $=
      ( wprt cv wcel wa wceq cin c0 wo wi wral df-prt rsp2 sylbi elin wn wal sp
      eq0 pm2.21d biimtrrid jao1i syl6 ) DEZAFZDGBFZDGHZUHUIIZUHUIJZKIZLZCFZUHG
      UOUIGHZUKMUGUNBDNADNUJUNMABDOUNABDDPQUKUMUPUPUOULGZUMUKUOUHUIRUMUQUKUMUQS
      ZCTURCULUBURCUAQUCUDUEUF $.

    $( Lemma for ~ prter1 and ~ prtex .  (Contributed by Rodolfo Medina,
       13-Oct-2010.) $)
    prtlem15 $p |- ( Prt A -> ( E. x e. A E. y e. A ( ( u e. x /\ w e. x )
                        /\ ( w e. y /\ v e. y ) )
                        -> E. z e. A ( u e. z /\ v e. z ) ) ) $=
      ( wprt wel wa wrex cv wcel wi anabs7 an43 anbi2i 3bitr4ri weq elequ2 syl8
      prtlem14 anbi2d imbitrrid imp4a syl7bi expdimp rexlimdv reximdva cbvrexvw
      an3 anbi12d imbitrdi ) GHZFAIZDAIZJDBIZEBIZJJZBGKZAGKUOEAIZJZAGKFCIZECIZJ
      ZCGKUNUTVBAGUNALGMZJUSVBBGUNVFBLGMZUSVBNZUSUPUQJZUSJZUNVFVGJZVBVIUOURJZVI
      JZJVMVJUSVLVIOUSVMVIUOUPUQURPZQVNRUNVKVIUSVBUNVKVIABSZVHABDGUBUSVBVOVLUOU
      PUQURUKVOVAURUOABETUCUDUAUEUFUGUHUIVBVEACGACSUOVCVAVDACFTACETULUJUM $.
  $}

  ${
    $d x y A $.  $d z x $.  $d z y $.  $d y w $.
    $( Lemma for ~ prter2 .  (Contributed by Rodolfo Medina, 15-Oct-2010.) $)
    prtlem17 $p |- ( Prt A -> ( ( x e. A /\ z e. x )
                                        -> ( E. y e. A ( z e. y /\ w e. y )
                                                -> w e. x ) ) ) $=
      ( wprt cv wcel wel wa wrex wi wex df-rex an32 weq prtlem14 elequ2 biimprd
      syl8 exp4a impd biimtrrid expd imp5a imp4b exlimdv biimtrid ex ) EFZAGEHZ
      CAIZJZCBIZDBIZJZBEKZDAIZLUQBGEHZUPJZBMUJUMJZURUPBENVAUTURBUJUMUSUPURUJUMU
      SUNUOURUJUMUSUNUOURLZLZUMUSJUKUSJZULJUJVCUKUSULOUJVDULVCUJVDULUNVBUJVDULU
      NJABPZVBABCEQVEURUOABDRSTUAUBUCUDUEUFUGUHUI $.
  $}

  ${
    $d p q r u v w x y z A $.  $d p v w z .~ $.  $d v w z S $.
    prtlem18.1 $e |- .~ = { <. x , y >. | E. u e. A ( x e. u /\ y e. u ) } $.
    $( Lemma for ~ prter2 .  (Contributed by Rodolfo Medina, 15-Oct-2010.)
       (Revised by Mario Carneiro, 12-Aug-2015.) $)
    prtlem18 $p |- ( Prt A ->
      ( ( v e. A /\ z e. v ) -> ( w e. v <-> z .~ w ) ) ) $=
      ( vp wprt cv wcel wel wa wbr wi wrex rspe prtlem13 imbitrrdi a1i prtlem17
      expr syl7bi impbidd ) GKZELGMZCENZOZDENZCLDLHPZUJUKULQQUGUJUKUIUKOZEGRZUL
      UHUIUKUNUMEGSUDABCDEFGHITUAUBULCJNDJNOJGRUGUJUKABCDJFGHITEJCDGUCUEUF $.

    $( Lemma for ~ prter2 .  (Contributed by Rodolfo Medina, 15-Oct-2010.)
       (Revised by Mario Carneiro, 12-Aug-2015.) $)
    prtlem19 $p |- ( Prt A -> ( ( v e. A /\ z e. v ) -> v = [ z ] .~ ) ) $=
      ( vw wprt cv wcel wa cec wceq wbr wb prtlem18 imp vex elec bitr4di eqrdv
      ex ) FJZDKZFLCKZUFLMZUFUGGNZOUEUHMZIUFUIUJIKZUFLZUGUKGPZUKUILUEUHULUMQABC
      IDEFGHRSUKUGGITCTUAUBUCUD $.

    $( Every partition generates an equivalence relation.  (Contributed by
       Rodolfo Medina, 13-Oct-2010.)  (Revised by Mario Carneiro,
       12-Aug-2015.) $)
    prter1 $p |- ( Prt A -> .~ Er U. A ) $=
      ( vz vw vp vv vq vr cv wbr wi wa wal wel wrex prtlem13 wprt wrel cdm cuni
      wceq wer relopabiv prtlem16 prtlem15 anbi12i reeanv bitr4i 3imtr4g pm3.22
      a1i reximi 3imtr4i jctil alrimivv alrimiv dfer2 syl3anbrc ) DUAZEUBZEUCDU
      DZUEZGMZHMZENZVHVGENZOZVIVHIMZENZPZVGVLENZOZPZIQHQZGQVEEUFVDVCACRBCRPCDSA
      BEFUGUOVFVCABCDEFUHUOVCVRGVCVQHIVCVPVKVCGJRZHJRZPZHKRIKRPZPKDSJDSZGLRILRP
      LDSVNVOJKLHIGDUIVNWAJDSZWBKDSZPWCVIWDVMWEABGHJCDEFTZABHIKCDEFTUJWAWBJKDDU
      KULABGILCDEFTUMWDVTVSPZJDSVIVJWAWGJDVSVTUNUPWFABHGJCDEFTUQURUSUTGHIVEEVAV
      B $.

    $( The equivalence relation generated by a partition is a set if and only
       if the partition itself is a set.  (Contributed by Rodolfo Medina,
       15-Oct-2010.)  (Revised by Mario Carneiro, 12-Aug-2015.) $)
    prtex $p |- ( Prt A -> ( .~ e. _V <-> A e. _V ) ) $=
      ( wprt cvv wcel cuni wer wb prter1 erexb syl uniexb bitr4di ) DGZEHIZDJZH
      IZDHIRTEKSUALABCDEFMTENODPQ $.

    $( The quotient set of the equivalence relation generated by a partition
       equals the partition itself.  (Contributed by Rodolfo Medina,
       17-Oct-2010.) $)
    prter2 $p |- ( Prt A -> ( U. A /. .~ ) = ( A \ { (/) } ) ) $=
      ( vp vv vz c0 cv wcel wa wceq wrex wex bitri df-rex wral wi wprt cuni cqs
      csn cdif wne cec rexcom4 r19.41v exbii rexbii elqs eluni2 anbi1i 3bitr4ri
      vex prtlem19 ralrimivv 2r19.29 ex syl biimtrid reximi syl6 19.41v simprbi
      eqtr3 imbitrrdi wn prtlem400 nelelne mp1i jcad eldifsn neldifsn n0el mpbi
      risset rspec eldifi jca ancomsd elunii jca2r cvv prtlem11 elv imp 3imtr3g
      eximdv 19.9v syl5 impbid eqrdv ) DUAZGDUBZEUCZDJUDZUEZWOGKZWQLZWTWSLZWOXA
      WTDLZWTJUFZMXBWOXAXCXDWOXAHKZWTNZHDOZXCWOXAXFIXEOZHDOZXGWOXAXEIKZEUGZNZWT
      XKNZMZIXEOZHDOZXIXAXMIXEOZHDOZWOXPXJXELZXMMZIPZHDOZXSHDOZXMMZIPZXRXAYBXTH
      DOZIPYEXTHIDUHYFYDIXSXMHDUIUJQXQYAHDXMIXERUKXAXMIWPOZYEIWPWTEGUPULYGXJWPL
      ZXMMZIPYEXMIWPRYIYDIYHYCXMHXJDUMUNUJQQUOWOXLIXESHDSZXRXPTWOXLHIDXEABIHCDE
      FUQURYJXRXPXLXMHIDXEUSUTVAVBXOXHHDXNXFIXEXEWTXKVGVCVCVDXHXFHDXHXSIPZXFXHX
      SXFMIPYKXFMXFIXERXSXFIVEQVFVCVDHWTDVRVHJWQLVIXAXDTWOABCDEFVJJWQWTVKVLVMWT
      DJVNVHXBXJWTLZIPZXCMZWOXAXBYMXCYMGWSJWSLVIYMGWSSJDVOGIWSVPVQVSWTDWRVTWAWO
      YLXCMZIPXAIPYNXAWOYOXAIWOYOYIXAWOYOXMYHWOXCYLXMABIGCDEFUQWBXJWTDWCWDYHXMX
      AYHXMXATTGWPWTXJWEEWFWGWHVDWJYLXCIVEXAIWKWIWLWMWN $.

    $( For every partition there exists a unique equivalence relation whose
       quotient set equals the partition.  (Contributed by Rodolfo Medina,
       19-Oct-2010.)  (Proof shortened by Mario Carneiro, 12-Aug-2015.) $)
    prter3 $p |- ( ( S Er U. A /\ ( U. A /. S ) = ( A \ { (/) } ) ) ->
        .~ = S ) $=
      ( vz vw vv wrel c0 wceq wa wel wrex cv wbr wb wcel cuni wer cqs csn errel
      adantr relopabiv prtlem13 cec simpll wne simprl ad2antll eldifsn sylanbrc
      cdif ne0i simplr eleqtrrd simprr qsel syl3anc eleq2d elec bitrdi pm5.32da
      vex anassrs rexbidva simpr ercl eluni2 ex pm4.71rd r19.41v bitr4di bitr4d
      sylib bitrid adantl eqbrrdv2 mpanl1 mpancom ) FKZDUAZFUBZWEFUCZDLUDUPZMZN
      ZEFMZWFWDWIWEFUEUFEKZWDWJWKACOBCONCDPABEGUGWJHIEFWJHQZIQZERZWMWNFRZSWLWDN
      WOHJOZIJOZNZJDPZWJWPABHIJCDEGUHWJWTWQWPNZJDPZWPWJWSXAJDWJJQZDTZNWQWRWPWJX
      DWQWRWPSWJXDWQNZNZWRWNWMFUIZTWPXFXCXGWNXFWFXCWGTWQXCXGMWFWIXEUJXFXCWHWGXF
      XDXCLUKZXCWHTWJXDWQULWQXHWJXDXCWMUQUMXCDLUNUOWFWIXEURUSWJXDWQUTWEXCWMFWEV
      AVBVCWNWMFIVGHVGVDVEVHVFVIWJWPWQJDPZWPNXBWJWPXIWJWPXIWJWPNZWMWETXIXJWMWNF
      WEWFWIWPUJWJWPVJVKJWMDVLVRVMVNWQWPJDVOVPVQVSVTWAWBWC $.
  $}

$( (End of Rodolfo Medina's mathbox.) $)
