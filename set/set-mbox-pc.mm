$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Paul Chapman
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Prime numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Finite set induction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The ` # ` (set size) function
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Real and complex numbers (cont.)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d k m $.
    $( Utility lemma to convert between ` m <_ k ` and ` k e. ( ZZ>= `` m ) `
       in limit theorems.  (Contributed by Paul Chapman, 10-Nov-2012.) $)
    climuzcnv $p |- ( m e. NN -> ( ( k e. ( ZZ>= ` m ) -> ph ) <->
                                   ( k e. NN -> ( m <_ k -> ph ) ) ) ) $=
      ( cv cn wcel cuz cfv wi cle wbr wa elnnuz uztrn sylan2b sylibr expcom nnz
      c1 cz eluzle a1i jcad biimpri syl3an1 syl3an2 3expib impbid imbi1d impexp
      w3a eluz2 bitrdi ) CDZEFZBDZUNGHFZAIUPEFZUNUPJKZLZAIURUSAIIUOUQUTAUOUQUTU
      OUQURUSUQUOURUQUOLUPSGHZFZURUOUQUNVAFVBUNMUNUPSNOUPMPQUQUSIUOUNUPUAUBUCUO
      URUSUQURUOUPTFZUSUQUPRUOUNTFZVCUSUQUNRUQVDVCUSUKUNUPULUDUEUFUGUHUIURUSAUJ
      UM $.
  $}

  ${
    $d k w x y z F $.  $d k w y z H $.  $d k z M $.  $d k w y z ph $.
    $d k G $.
    sinccvg.1 $e |- ( ph -> F : NN --> ( RR \ { 0 } ) ) $.
    sinccvg.2 $e |- ( ph -> F ~~> 0 ) $.
    sinccvg.3 $e |- G = ( x e. ( RR \ { 0 } ) |-> ( ( sin ` x ) / x ) ) $.
    sinccvg.4 $e |- H = ( x e. CC |-> ( 1 - ( ( x ^ 2 ) / 3 ) ) ) $.
    sinccvg.5 $e |- ( ph -> M e. NN ) $.
    sinccvg.6 $e |- ( ( ph /\ k e. ( ZZ>= ` M ) ) ->
                      ( abs ` ( F ` k ) ) < 1 ) $.
    $( ` ( ( sin `` x ) / x ) ~~> 1 ` as (real) ` x ~~> 0 ` .  (Contributed by
       Paul Chapman, 10-Nov-2012.)  (Revised by Mario Carneiro,
       21-May-2014.) $)
    sinccvglem $p |- ( ph -> ( G o. F ) ~~> 1 ) $=
      ( c1 cc0 wcel cc co c3 cdiv vy vz vw ccom cvv cuz cfv eqid nnzd cli cv c2
      wfun cexp cmin funmpt2 cn cr csn cdif wf nnex sylancl cofunexg sylancr wa
      fex wne adantr eluznn sylan ffvelcdmd eldifsn sylib simpld recnd sqcl 3cn
      ax-1cn 3ne0 divcl mp3an23 syl subcl fmpti ccncf crp cabs clt wi wral wrex
      wbr cmpt ccnfld ctopn ccn wtru ctopon cnfldtopon 1cnd cnmptc divccn mp2an
      a1i sqcn oveq1 cnmpt11 ctx subcn cnmpt12f mptru cncfcn1 cncfi mp3an1 wceq
      3eltr4i fvco3 syldan climcn1lem 0cn oveq1d eqtrdi oveq2d fvmpt csin eqtrd
      ovex 1re eqeltrd fveq2 id oveq12d resincld simprd cmul eqbrtrd cneg ltled
      cle sq0i div0i 1m0e1 1ex breqtrdi resqcld nndivre resubcl redivcld abscld
      ax-mp 3nn subdird mullidd caddc df-3 oveq2i cn0 2nn0 expp1 absresq eqtrid
      div23d eqtr2d cioc absrpcld rpgt0d ltle mpd cxr w3a wb syl3anbrc sin01bnd
      0xr elioc2 ltmuldivd mpbid sinneg eqeq1d syl5ibrcom absord mpjaod breqtrd
      div2negd 3brtr4d mulridd breqtrrd ltdivmuld mpbird eqbrtrrd climsqz ) ANC
      FDUDZEDUDZGUEGUFUGZUWOUHZAGLUIZAUWMOFUGZNUJAUAUBUCOCDUWMFGUEUWOUWPIAFUMDU
      EPZUWMUEPBQNBUKZULUNRZSTRZUORZFKUPAUQUROUSUTZDVAZUQUEPUWSHVBUQUXDUEDVGVCZ
      FDUEVDVEUWQACUKZUWOPZVFZUXGDUGZUXIUXJURPZUXJOVHZUXIUXJUXDPZUXKUXLVFUXIUQU
      XDUXGDAUXEUXHHVIAGUQPUXHUXGUQPZLUXGGVJVKZVLZUXJUROVMVNZVOZVPZBQQUXCFKUWTQ
      PZNQPUXBQPZUXCQPVSUXTUXAQPZUYAUWTVQUYBSQPZSOVHZUYAVRVTUXASWAWBWCNUXBWDVEW
      EFQQWFRZPOQPZUAUKZWGPUCUKZOUORWHUGUBUKWIWMUYHFUGUWRUORWHUGUYGWIWMWJUCQWKU
      BWGWLBQUXCWNZWOWPUGZUYJWQRZFUYEUYIUYKPWRBNUXBUOUYJUYJUYJUYJQUYJQWSUGPWRUY
      JUYJUHZWTXEZWRBNUYJUYJQQUYMUYMWRXAXBWRBUAUXAUYGSTRZUXBUYJUYJUYJQQUYMBQUXA
      WNUYKPWRBUYJUYLXFXEUYMUAQUYNWNUYKPZWRUYCUYDUYOVRVTUASUYJUYLXCXDXEUYGUXAST
      XGXHUOUYJUYJXIRUYJWQRPWRUYJUYLXJXEXKXLKUYJUYLXMXQUBUCQQOUYGFXNXOAUXHUXNUX
      GUWMUGZUXJFUGZXPZUXOAUXEUXNUYRHUQUXDUXGFDXRVKXSZXTUYFUWRNXPYABOUXCNQFUWTO
      XPZUXCNOUORNUYTUXBONUOUYTUXBOSTROUYTUXAOSTUWTUUAYBSVRVTUUBYCYDUUCYCKUUDYE
      UUKUUEAEUMUWSUWNUEPBUXDUWTYFUGZUWTTRZEJUPUXFEDUEVDVEUXIUYPNUXJULUNRZSTRZU
      ORZURUXIUYPUYQVUEUYSUXIUXJQPZUYQVUEXPUXSBUXJUXCVUEQFUWTUXJXPZUXBVUDNUOVUG
      UXAVUCSTUWTUXJULUNXGYBYDKNVUDUOYHYEWCYGZUXINURPZVUDURPZVUEURPYIUXIVUCURPS
      UQPVUJUXIUXJUXRUUFZUULVUCSUUGVCZNVUDUUHVEZYJUXIUXGUWNUGZUXJYFUGZUXJTRZURU
      XIVUNUXJEUGZVUPAUXHUXNVUNVUQXPZUXOAUXEUXNVURHUQUXDUXGEDXRVKXSUXIUXMVUQVUP
      XPUXPBUXJVUBVUPUXDEVUGVUAVUOUWTUXJTUWTUXJYFYKVUGYLYMJVUOUXJTYHYEWCYGZUXIV
      UOUXJUXIUXJUXRYNZUXRUXIUXKUXLUXQYOZUUIZYJUXIVUEVUPUYPVUNYTUXIVUEVUPVUMVVB
      UXIVUEUXJWHUGZYFUGZVVCTRZVUPWIUXIVUEVVCYPRZVVDWIWMVUEVVEWIWMUXIVVFVVCVVCS
      UNRZSTRZUORZVVDWIUXIVVFNVVCYPRZVUDVVCYPRZUORVVIUXINVUDVVCUXIXAUXIVUDVULVP
      UXIVVCUXIUXJUXSUUJZVPZUUMUXIVVJVVCVVKVVHUOUXIVVCVVMUUNUXIVVHVUCVVCYPRZSTR
      VVKUXIVVGVVNSTUXIVVGVVCULNUUORZUNRZVVNSVVOVVCUNUUPUUQUXIVVPVVCULUNRZVVCYP
      RZVVNUXIVVCQPULUURPVVPVVRXPVVMUUSVVCULUUTVCUXIVVQVUCVVCYPUXIUXKVVQVUCXPUX
      RUXJUVAWCYBYGUVBYBUXIVUCVVCSUXIVUCVUKVPVVMUYCUXIVRXEUYDUXIVTXEUVCUVDYMYGU
      XIVVIVVDWIWMZVVDVVCWIWMZUXIVVCONUVERPZVVSVVTVFUXIVVCURPZOVVCWIWMZVVCNYTWM
      ZVWAVVLUXIVVCUXIUXJUXSVVAUVFZUVGUXIVVCNWIWMZVWDMUXIVWBVUIVWFVWDWJVVLYIVVC
      NUVHVCUVIOUVJPVUIVWAVWBVWCVWDUVKUVLUVOYIONVVCUVPXDUVMVVCUVNWCZVOYQUXIVUEV
      VDVVCVUMUXIVVCVVLYNZVWEUVQUVRUXIVVCUXJXPZVVEVUPXPZVVCUXJYRZXPZVWIVWJWJUXI
      VWIVVDVUOVVCUXJTVVCUXJYFYKVWIYLYMXEUXIVWJVWLVWKYFUGZVWKTRZVUPXPUXIVWNVUOY
      RZVWKTRVUPUXIVWMVWOVWKTUXIVUFVWMVWOXPUXSUXJUVSWCYBUXIVUOUXJUXIVUOVUTVPUXS
      VVAUWEYGVWLVVEVWNVUPVWLVVDVWMVVCVWKTVVCVWKYFYKVWLYLYMUVTUWAUXIUXJUXRUWBUW
      CZUWDYSVUHVUSUWFUXIVUNVUPNYTVUSUXIVUPNVVBVUIUXIYIXEZUXIVVEVUPNWIVWPUXIVVE
      NWIWMVVDVVCNYPRZWIWMUXIVVDVVCVWRWIUXIVVSVVTVWGYOUXIVVCVVMUWGUWHUXIVVDNVVC
      VWHVWQVWEUWIUWJUWKYSYQUWL $.
  $}

  ${
    $d j k n x F $.
    $( ` ( ( sin `` x ) / x ) ~~> 1 ` as (real) ` x ~~> 0 ` .  (Contributed by
       Paul Chapman, 10-Nov-2012.)  (Proof shortened by Mario Carneiro,
       21-May-2014.) $)
    sinccvg $p |- ( ( F : NN --> ( RR \ { 0 } ) /\ F ~~> 0 ) ->
      ( ( x e. ( RR \ { 0 } ) |-> ( ( sin ` x ) / x ) ) o. F ) ~~> 1 ) $=
      ( vk vj vn cn cc0 cli wbr wa cv cfv cabs c1 clt cdiv co cmpt wcel eqid cr
      csn cdif wf cuz wral csin ccom nnuz 1zzd crp 1rp eqidd simpr climi0 cc c2
      a1i cexp cmin simpll simplr simprl simprr weq 2fveq3 breq1d rspccva sylan
      c3 sinccvglem rexlimddv ) FUAGUBUCZBUDZBGHIZJZCKZBLZMLZNOIZCDKZUELZUFZAVM
      AKZUGLWDPQRZBUHNHIDFVPVRNDCBNFUIVPUJNUKSVPULURVPVQFSJVRUMVNVOUNUOVPWAFSZW
      CJZJZAEBWEAUPNWDUQUSQVJPQUTQRZWAVNVOWGVAVNVOWGVBWETWITVPWFWCVCWHWCEKZWBSW
      JBLMLZNOIZVPWFWCVDVTWLCWJWBCEVEVSWKNOVQWJMBVFVGVHVIVKVL $.
  $}

  ${
    $d n y $.  $d k P $.  $d k n R $.
    circum.1 $e |- A = ( ( 2 x. _pi ) / n ) $.
    circum.2 $e |-
      P = ( n e. NN |-> ( ( 2 x. n ) x. ( R x. ( sin ` ( A / 2 ) ) ) ) ) $.
    circum.3 $e |- R e. RR $.
    $( The circumference of a circle of radius ` R ` , defined as the limit as
       ` n ~~> +oo ` of the perimeter of an inscribed n-sided isogons, is
       ` ( ( 2 x. _pi ) x. R ) ` .  (Contributed by Paul Chapman, 10-Nov-2012.)
       (Proof shortened by Mario Carneiro, 21-May-2014.) $)
    circum $p |- P ~~> ( ( 2 x. _pi ) x. R ) $=
      ( c2 cpi cmul co wtru cn cdiv csin cfv cr cc0 wcel cc vk vy c1 cli wbr cv
      cmpt cvv nnuz 1zzd csn cdif ccom wne wa crp pirp rpdivcl sylancr rprene0d
      nnrp eldifsn sylibr adantl eqidd wceq fveq2 id oveq12d wf eqid fmpti pire
      fmptco recni divcnv mp1i sinccvg eqbrtrrd 2re remulcli nnex mptex eqeltri
      a1i resincld eldifsni redivcld fco mp2an mptru feq1i mpbi ffvelcdmi recnd
      eldifi nncn nnne0 divassd oveq1d simpr nndivre 2ne0 divcan3d eqtrd fveq2d
      rpne0d divcan2d eqtr4d oveq2d oveq2 ovex fvmpt mulassd mulcl mul4d mul32d
      eqeltrrd 3eqtr2d eqtrid 3eqtr4d climmulc2 mulridi breqtri ) BHIJKZCJKZUCJ
      KZYFUDBYGUDUELUCYFUADMIDUFZNKZOPZYINKZUGZBUCUHMUILUJLUBQRUKZULZUBUFZOPZYO
      NKZUGZDMYIUGZUMZYLUCUDLDUBMYNYIYQYKYSYRYHMSZYIYNSZLUUAYIQSYIRUNUOUUBUUAYI
      UUAIUPSZYHUPSYIUPSUQYHVAIYHURUSUTYIQRVBVCZVDLYSVELYRVEYOYIVFZYPYJYOYINYOY
      IOVGUUEVHVIVNZLMYNYSVJZYSRUDUEZYTUCUDUEDMYNYIYSYSVKUUDVLZITSZUUHLIVMVOZID
      VPVQUBYSVRUSVSYFTSLYFYECHIVTVMWAGWAVOZWEBUHSLBDMHYHJKZCAHNKZOPZJKZJKZUGUH
      FDMUUQWBWCWDWELUAUFZMSZUOZUURYLPZUUSUVAQSLMQUURYLMQYTVJZMQYLVJYNQYRVJUUGU
      VBUBYNQYQYRYRVKYOYNSZYPYOUVCYOYOQYMWPZWFUVDYOQRWGWHVLUUIMYNQYRYSWIWJMQYTY
      LYTYLVFUUFWKWLWMWNVDWOZUUTHUURJKZCYEUURNKZHNKZOPZJKZJKZYFIUURNKZOPZUVLNKZ
      JKZUURBPZYFUVAJKUUTUVKUVFCUVLJKZUVNJKZJKUVFUVQJKZUVNJKUVOUUTUVJUVRUVFJUUT
      UVJCUVLUVNJKZJKUVRUUTUVIUVTCJUUTUVIUVMUVTUUTUVHUVLOUUTUVHHUVLJKZHNKUVLUUT
      UVGUWAHNUUTHIUURHTSZUUTHVTVOZWEZUUJUUTUUKWEZUUSUURTSZLUURWQVDZUUSUURRUNLU
      URWRVDZWSWTUUTUVLHUUTUVLUUTIQSUUSUVLQSVMLUUSXAIUURXBUSZWOZUWDHRUNUUTXCWEX
      DXEXFUUTUVMUVLUUTUVMUUTUVLUWIWFWOUWJUUTUVLUUTUUCUURUPSZUVLUPSUQUUSUWKLUUR
      VAVDIUURURUSXGXHXIXJUUTCUVLUVNCTSZUUTCGVOZWEZUWJUUTUVAUVNTUUSUVAUVNVFLDUU
      RYKUVNMYLYHUURVFZYJUVMYIUVLNUWOYIUVLOYHUURINXKZXFUWPVIYLVKUVMUVLNXLXMVDZU
      VEXRZXNXIXJUUTUVFUVQUVNUUTUWBUWFUVFTSUWCUWGHUURXOUSUUTUWLUVLTSUVQTSUWMUWJ
      CUVLXOUSUWRXNUUTUVSYFUVNJUUTUVSHCJKZUURUVLJKZJKZYFUUTHUURCUVLUWDUWGUWNUWJ
      XPUUTUXAUWSIJKYFUUTUWTIUWSJUUTIUURUWEUWGUWHXHXJUUTHCIUWDUWNUWEXQXEXEWTXSU
      USUVPUVKVFLDUURUUQUVKMBUWOUUMUVFUUPUVJJYHUURHJXKUWOUUOUVICJUWOUUNUVHOUWOA
      UVGHNUWOAYEYHNKUVGEYHUURYENXKXTWTXFXJVIFUVFUVJJXLXMVDUUTUVAUVNYFJUWQXJYAY
      BWKYFUULYCYD $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Miscellaneous theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Membership in a curtailed finite sequence of integers.  (Contributed by
     Paul Chapman, 17-Nov-2012.) $)
  elfzm12 $p |- ( N e. NN ->
                  ( M e. ( 1 ... ( N - 1 ) ) -> M e. ( 1 ... N ) ) ) $=
    ( cn wcel c1 cmin co cfz cz cuz cfv wss nnz cle wbr zre lem1d peano2zm eluz
    wb mpancom mpbird fzss2 3syl sseld ) BCDZEBEFGZHGZEBHGZAUFBIDZBUGJKDZUHUILB
    MUJUKUGBNOZUJBBPQUGIDUJUKULTBRUGBSUAUBUGEBUCUDUE $.

  ${
    $d F k $.  $d N k $.
    nn0seqcvg.1 $e |- F : NN0 --> NN0 $.
    nn0seqcvg.2 $e |- N = ( F ` 0 ) $.
    nn0seqcvg.3 $e |- ( k e. NN0 -> ( ( F ` ( k + 1 ) ) =/= 0 ->
                                      ( F ` ( k + 1 ) ) < ( F ` k ) ) ) $.
    $( A strictly-decreasing nonnegative integer sequence with initial term
       ` N ` reaches zero by the ` N ` th term.  Inference version.
       (Contributed by Paul Chapman, 31-Mar-2011.) $)
    nn0seqcvg $p |- ( F ` N ) = 0 $=
      ( c1 wceq cfv cc0 eqid cn0 wf a1i cv wcel caddc co wne clt wbr nn0seqcvgd
      wi adantl ax-mp ) GGHZCBIJHGKUFABCLLBMUFDNCJBIHUFENAOZLPUGGQRBIZJSUHUGBIT
      UAUCUFFUDUBUE $.
  $}

  $( Division of both sides of 'less than or equal to' by a nonnegative number.
     (Contributed by Paul Chapman, 7-Sep-2007.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  lediv2aALT $p |- ( ( ( A e. RR /\ 0 < A ) /\ ( B e. RR /\ 0 < B ) /\
                     ( C e. RR /\ 0 <_ C ) ) ->
                   ( A <_ B -> ( C / B ) <_ ( C / A ) ) ) $=
    ( cr wcel cc0 clt wbr wa cle w3a c1 cdiv co anim12i ancoms syl recn adantr
    cc wi wne gt0ne0 rereccl syldan 3adant3 simp3 df-3an sylanbrc lemul2a ex wb
    cmul lerec wceq jca 3anass sylibr divrec 3adant1 3adant2 breq12d 3imtr4d )
    ADEZFAGHZIZBDEZFBGHZIZCDEZFCJHZIZKZLBMNZLAMNZJHZCVNUMNZCVOUMNZJHZABJHZCBMNZ
    CAMNZJHVMVNDEZVODEZVLKZVPVSUAVMWCWDIZVLWEVFVIWFVLVIVFWFVIWCVFWDVGVHBFUBZWCB
    UCZBUDUEVDVEAFUBZWDAUCZAUDUEOPUFVFVIVLUGWCWDVLUHUIWEVPVSVNVOCUJUKQVFVIVTVPU
    LVLABUNUFVMWAVQWBVRJVIVLWAVQUOZVFVLVIWKVLVIIZCTEZBTEZWGKZWKWLWMWNWGIZIWOVLW
    MVIWPVJWMVKCRSZVIWNWGVGWNVHBRSWHUPOWMWNWGUQURCBUSQPUTVFVLWBVRUOZVIVLVFWRVLV
    FIZWMATEZWIKZWRWSWMWTWIIZIXAVLWMVFXBWQVFWTWIVDWTVEARSWJUPOWMWTWIUQURCAUSQPV
    AVBVC $.

  ${
    abs2sqlei.1 $e |- A e. CC $.
    abs2sqlei.2 $e |- B e. CC $.
    $( The absolute values of two numbers compare as their squares.
       (Contributed by Paul Chapman, 7-Sep-2007.) $)
    abs2sqlei $p |- ( ( abs ` A ) <_ ( abs ` B ) <->
                     ( ( abs ` A ) ^ 2 ) <_ ( ( abs ` B ) ^ 2 ) ) $=
      ( cc0 cabs cfv cle wbr c2 cexp co wb absge0i abscli le2sqi mp2an ) EAFGZH
      IEBFGZHIRSHIRJKLSJKLHIMACNBDNRSACOBDOPQ $.
  $}

  ${
    abs2sqlti.1 $e |- A e. CC $.
    abs2sqlti.2 $e |- B e. CC $.
    $( The absolute values of two numbers compare as their squares.
       (Contributed by Paul Chapman, 7-Sep-2007.) $)
    abs2sqlti $p |- ( ( abs ` A ) < ( abs ` B ) <->
                     ( ( abs ` A ) ^ 2 ) < ( ( abs ` B ) ^ 2 ) ) $=
      ( cc0 cabs cfv cle wbr clt c2 cexp co wb absge0i abscli lt2sqi mp2an ) EA
      FGZHIEBFGZHISTJISKLMTKLMJINACOBDOSTACPBDPQR $.
  $}

  $( The absolute values of two numbers compare as their squares.  (Contributed
     by Paul Chapman, 7-Sep-2007.) $)
  abs2sqle $p |- ( ( A e. CC /\ B e. CC ) ->
                    ( ( abs ` A ) <_ ( abs ` B ) <->
                      ( ( abs ` A ) ^ 2 ) <_ ( ( abs ` B ) ^ 2 ) ) ) $=
    ( cc wcel cabs cfv cle wbr c2 cexp co wb cc0 cif wceq breq1d bibi12d breq2d
    fveq2 0cn oveq1d oveq1 syl elimel abs2sqlei dedth2h ) ACDZBCDZAEFZBEFZGHZUI
    IJKZUJIJKZGHZLUGAMNZEFZUJGHZUPIJKZUMGHZLUPUHBMNZEFZGHZURVAIJKZGHZLABMMAUOOZ
    UKUQUNUSVEUIUPUJGAUOESZPVEULURUMGVEUIUPIJVFUAPQBUTOZUQVBUSVDVGUJVAUPGBUTESZ
    RVGUJVAOZUSVDLVHVIUMVCURGUJVAIJUBRUCQUOUTAMCTUDBMCTUDUEUF $.

  $( The absolute values of two numbers compare as their squares.  (Contributed
     by Paul Chapman, 7-Sep-2007.) $)
  abs2sqlt $p |- ( ( A e. CC /\ B e. CC ) ->
                    ( ( abs ` A ) < ( abs ` B ) <->
                      ( ( abs ` A ) ^ 2 ) < ( ( abs ` B ) ^ 2 ) ) ) $=
    ( cc wcel cabs cfv clt wbr c2 cexp co wb cc0 cif wceq breq1d bibi12d breq2d
    fveq2 0cn oveq1d oveq1 syl elimel abs2sqlti dedth2h ) ACDZBCDZAEFZBEFZGHZUI
    IJKZUJIJKZGHZLUGAMNZEFZUJGHZUPIJKZUMGHZLUPUHBMNZEFZGHZURVAIJKZGHZLABMMAUOOZ
    UKUQUNUSVEUIUPUJGAUOESZPVEULURUMGVEUIUPIJVFUAPQBUTOZUQVBUSVDVGUJVAUPGBUTESZ
    RVGUJVAOZUSVDLVHVIUMVCURGUJVAIJUBRUCQUOUTAMCTUDBMCTUDUEUF $.

  ${
    abs2difi.1 $e |- A e. CC $.
    abs2difi.2 $e |- B e. CC $.
    $( Difference of absolute values.  (Contributed by Paul Chapman,
       7-Sep-2007.) $)
    abs2difi $p |- ( ( abs ` A ) - ( abs ` B ) ) <_ ( abs ` ( A - B ) ) $=
      ( cc wcel cabs cfv cmin co cle wbr abs2dif mp2an ) AEFBEFAGHBGHIJABIJGHKL
      CDABMN $.
  $}

  ${
    abs2difabsi.1 $e |- A e. CC $.
    abs2difabsi.2 $e |- B e. CC $.
    $( Absolute value of difference of absolute values.  (Contributed by Paul
       Chapman, 7-Sep-2007.) $)
    abs2difabsi $p |- ( abs ` ( ( abs ` A ) - ( abs ` B ) ) ) <_
                     ( abs ` ( A - B ) ) $=
      ( cc wcel cabs cfv cmin co cle wbr abs2difabs mp2an ) AEFBEFAGHBGHIJGHABI
      JGHKLCDABMN $.
  $}

$( (End of Paul Chapman's mathbox.) $)
