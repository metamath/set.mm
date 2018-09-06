
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                Mathbox for Thierry Arnoux
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$[ set/main.mm $]

$[ set/mbox/ta/basics.mm $]
$[ set/mbox/ta/xdiv.mm $]
$[ set/mbox/ta/algtop.mm $]
$[ set/mbox/ta/ucm.mm $]
$[ set/mbox/ta/rrhom.mm $]
$[ set/mbox/ta/logb.mm $]
$[ set/mbox/ta/ind.mm $]
$[ set/mbox/ta/esum.mm $]
$[ set/mbox/ta/ofc.mm $]
$[ set/mbox/ta/meas.mm $]
$[ set/mbox/ta/itgm.mm $]

  ${
    $d x y A $.  $d x y B $. $d x y ph $.
    spc2ed.x $e |- F/ x ch $.
    spc2ed.y $e |- F/ y ch $.
    spc2ed.1 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ps <-> ch ) ) $.
    $( Existential specialization with 2 quantifiers, using implicit
       substitution. (Contributed by Thierry Arnoux, 23-Aug-2017.) $)
    spc2ed $p |- ( ( ph /\ ( A e. V /\ B e. W ) ) -> ( ch -> E. x E. y ps ) )
      $=
      ( wcel wa cv wceq wex wi elisset nfv anim12i eeanv sylibr anim2i biimparc
      nfan anass bicomi ancom anbi1i bitri imbi1i mpbi ex eximd impancom syl )
      AFHMZGIMZNZNADOFPZEOGPZNZEQZDQZNCBEQZDQZRUTVEAUTVADQZVBEQZNVEURVHUSVIDFHS
      EGISUAVAVBDEUBUCUDACVEVGACNZVDVFDACDADTJUFVJVCBEACEAETKUFVJVCBCAVCNZNZBRV
      JVCNZBRVKBCLUEVLVMBVLCANZVCNZVMVOVLCAVCUGUHVNVJVCCAUIUJUKULUMUNUOUOUPUQ
      $.

    $( Specialization with 2 quantifiers, using implicit substitution.
       (Contributed by Thierry Arnoux, 23-Aug-2017.) $)
    spc2d $p |- ( ( ph /\ ( A e. V /\ B e. W ) ) -> ( A. x A. y ps -> ch ) ) $=
      ( wal wn wex wcel wa nfn cv wceq 2nalexn con1bii notbid spc2ed syl5bir
      con1d ) BEMDMZBNZEODOZNAFHPGIPQQZCUGUIBDEUAUBUJCUIAUHCNDEFGHICDJRCEKRADSF
      TESGTQQBCLUCUDUFUE $.
  $}

  ${
    $d x A $. $d x B $. $d x ps $.
    $( Membership in a restricted class abstraction, using implicit
       substitution.  (Closed theorem version of ~ elrab3 .)
       (Contributed by Thierry Arnoux, 31-Aug-2017.) $)
    elrab3t $p |- ( ( A. x ( x = A -> ( ph <-> ps ) ) /\ A e. B ) ->
                                           ( A e. { x e. B | ph } <-> ps ) ) $=
      ( cv wceq wb wi wal wcel wa cab crab simpr nfa1 nfv nfan simpl 19.21bi
      eleq1 biimparc biantrurd bibi1d adantl mpbid alrimi elabgt syl2anc df-rab
      pm5.74da eleq2i bibi1i sylibr ) CFZDGZABHZIZCJZDEKZLZDUOEKZALZCMZKZBHZDAC
      ENZKZBHVAUTUPVCBHZIZCJVFUSUTOVAVJCUSUTCURCPUTCQRVAURVJVAURCUSUTSTUTURVJHU
      SUTUPUQVIUTUPLZAVCBVKVBAUPVBUTUODEUAUBUCUDUKUEUFUGVCBCDEUHUIVHVEBVGVDDACE
      UJULUMUN $.
  $}

  ${
    $d a w x y z $. $d a w ph $. $d w ps $.
    cnvoprab.x $e |- F/ x ps $.
    cnvoprab.y $e |- F/ y ps $.
    cnvoprab.1 $e |- ( a = <. x , y >. -> ( ps <-> ph ) ) $.
    cnvoprab.2 $e |- ( ps -> a e. ( _V X. _V ) ) $.
    $( TODO - simplify with ~ dfoprab3 $)
    $( The converse of a class abstraction of nested ordered pairs.
       (Contributed by Thierry Arnoux, 17-Aug-2017.) $)
    cnvoprab $p |- `' { <. <. x , y >. , z >. | ph } = { <. z , a >. | ps } $=
      ( vw copab cv cop wceq wa wex excom cvv wcel ccnv coprab cab opeq1 eqeq2d
      wi opex anbi12d spcegv ax-mp eximi nfv nfan nfex 19.9 cxp adantl c1st cfv
      sylib c2nd wb eqcom anbi12i eqopi sylan2br bicomd syl spc2ed mp2ani mpcom
      fvex exlimiv impbii exbii bitr2i 3bitr2ri abbii df-oprab df-opab 3eqtr4ri
      ex cnveqi cnvopab eqtr3i ) BFELZUAACDEUBZUABEFLWFWGKMZCMZDMZNZEMZNZOZAPZE
      QDQZCQZKUCWHFMZWLNZOZBPZEQFQZKUCWGWFWQXBKXBXAFQZEQWODQZCQZEQZWQXAFERXEXCE
      XEXCXEXCCQXCXDXCCXDXCDQXCWOXCDWKSTWOXCUFWIWJUGXAWOFWKSWRWKOZWTWNBAXGWSWMW
      HWRWKWLUDUEIUHZUIUJUKXCDXADFWTBDWTDULHUMZUNUOUTUKXCCXACFWTBCWTCULGUMZUNUO
      UTXAXEFWRSSUPTZXAXEBXKWTJUQXKWRURUSZSTZWRVAUSZSTZXAXEUFZWRURVLWRVAVLXKXMX
      OPXPXKWOXACDXLXNSSXJXIXKWIXLOZWJXNOZPZPXGWOXAVBXSXKXLWIOZXNWJOZPXGXTXQYAX
      RXLWIVCXNWJVCVDWRWIWJSSVEVFXGXAWOXHVGVHVIWBVJVKVMVNVOWQXDEQZCQXFWPYBCWODE
      RVOXDCERVPVQVRACDEKVSBFEKVTWAWCBFEWDWE $.
  $}

  ${
    $d a x y z A $. $d a x y z B $. $d a z C $. $d a x y z D $.
    $d a x y I $. $d a x y J $. $d a x y z ph $.
    f1od2.1 $e |- F = ( x e. A , y e. B |-> C ) $.
    f1od2.2 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> C e. W ) $.
    f1od2.3 $e |- ( ( ph /\ z e. D ) -> ( I e. X /\ J e. Y ) ) $.
    f1od2.4 $e |- ( ph -> ( ( ( x e. A /\ y e. B ) /\ z = C ) <->
                            ( z e. D /\ ( x = I /\ y = J ) ) ) ) $.
    $( Describe an implicit one-to-one onto function of two variables.
       (Contributed by Thierry Arnoux, 17-Aug-2017.) $)
    f1od2 $p |- ( ph -> F : ( A X. B ) -1-1-onto-> D ) $=
      ( wa wsbc va cxp wfn ccnv wf1o wcel wral ralrimivva fnmpt2 syl cv opelxpi
      cop cmpt ralrimiva eqid fnmpt c1st cfv c2nd wceq copab elxp7 anbi1i anass
      csb sbcbidv sbcan wb fvex sbcg ax-mp sbcel1v anbi12i bitri sbceq2g sbcbii
      3bitri sbceq1g csbvarg eqeq1i 3bitr3g anbi2d syl5bb simprr adantrr sseldi
      xpss eqeltrd ex pm4.71rd eqop pm5.32i syl6rbb bitrd opabbidv coprab cmpt2
      cvv df-mpt2 eqtri cnveqi nfv nfcv nfcsb1 nfeq nfan nfcsb opelxp csbopeq1a
      syl6bb eqeq2d anbi12d adantr cnvoprab df-mpt 3eqtr4g fneq1d mpbird dff1o4
      eleq1 sseli sylanbrc ) AIEFUBZUCZIUDZHUCZYDHIUEAGLUFZCFUGBEUGYEAYHBCEFPUH
      BCEFGILOUIUJAYGDHJKUMZUNZHUCZAYIMNUBZUFZDHUGYKAYMDHADUKZHUFZSJMUFKNUFSYMQ
      JKMNULUJZUODHYIYJYLYJUPUQUJAHYFYJAUAUKZYDUFZYNBYQURUSZCYQUTUSZGVFZVFZVAZS
      ZDUAVBZYOYQYIVAZSZDUAVBYFYJAUUDUUGDUAUUDYQWSWSUBZUFZYSEUFZYTFUFZSZSZUUCSZ
      AUUGYRUUMUUCYQEFVCVDAUUNUUIYOYSJVAZYTKVAZSZSZSZUUGUUNUUIUULUUCSZSAUUSUUIU
      ULUUCVEAUUTUURUUIABUKZEUFZCUKZFUFZSZYNGVAZSZCYTTZBYSTZYOUVAJVAZUVCKVAZSZS
      ZCYTTZBYSTZUUTUURAUVHUVNBYSAUVGUVMCYTRVGVGUVIUVBUUKSZYNUUAVAZSZBYSTUVPBYS
      TZUVQBYSTZSUUTUVHUVRBYSUVHUVECYTTZUVFCYTTZSUVRUVEUVFCYTVHUWAUVPUWBUVQUWAU
      VBCYTTZUVDCYTTZSUVPUVBUVDCYTVHUWCUVBUWDUUKYTWSUFZUWCUVBVIYQUTVJZUVBCYTWSV
      KVLCYTFVMVNVOUWEUWBUVQVIUWFCYTYNGWSVPVLVNVOVQUVPUVQBYSVHUVSUULUVTUUCUVSUV
      BBYSTZUUKBYSTZSUULUVBUUKBYSVHUWGUUJUWHUUKBYSEVMYSWSUFZUWHUUKVIYQURVJZUUKB
      YSWSVKVLVNVOUWIUVTUUCVIUWJBYSYNUUAWSVPVLVNVRUVOYOUVJUUPSZSZBYSTZUURUVNUWL
      BYSUVNYOCYTTZUVLCYTTZSUWLYOUVLCYTVHUWNYOUWOUWKUWEUWNYOVIUWFYOCYTWSVKVLUWO
      UVJCYTTZUVKCYTTZSUWKUVJUVKCYTVHUWPUVJUWQUUPUWEUWPUVJVIUWFUVJCYTWSVKVLUWQC
      YTUVCVFZKVAZUUPUWEUWQUWSVIUWFCYTUVCKWSVSVLUWRYTKUWEUWRYTVAUWFCYTWSVTVLWAV
      OVNVOVNVOVQUWMYOBYSTZUWKBYSTZSUURYOUWKBYSVHUWTYOUXAUUQUWIUWTYOVIUWJYOBYSW
      SVKVLUXAUVJBYSTZUUPBYSTZSUUQUVJUUPBYSVHUXBUUOUXCUUPUXBBYSUVAVFZJVAZUUOUWI
      UXBUXEVIUWJBYSUVAJWSVSVLUXDYSJUWIUXDYSVAUWJBYSWSVTVLWAVOUWIUXCUUPVIUWJUUP
      BYSWSVKVLVNVOVNVOVOWBWCWDAUUGUUIUUGSUUSAUUGUUIAUUGUUIAUUGSZYLUUHYQMNWHUXF
      YQYIYLAYOUUFWEAYOYMUUFYPWFWIWGWJWKUUIUUGUURUUIUUFUUQYOYQJKWSWSWLWCWMWNWOW
      DWPYFUVGBCDWQZUDUUEIUXGIBCEFGWRUXGOBCDEFGWTXAXBUVGUUDBCDUAYRUUCBYRBXCBYNU
      UBBYNXDBYSUUABYSXDXEXFXGYRUUCCYRCXCCYNUUBCYNXDCBYSUUACYSXDCYTGCYTXDXEXHXF
      XGYQUVAUVCUMZVAZYRUVEUUCUVFUXIYRUXHYDUFUVEYQUXHYDYAUVAUVCEFXIXKUXIUUBGYNB
      CYQGXJXLXMYRUUIUUCYDUUHYQEFWHYBXNXOXADUAHYIXPXQXRXSYDHIXTYC $.
  $}

  ${
    $d k A $. $d k n B $.
    $( A lower bound for an exponentiation.
       (Contributed by Thierry Arnoux, 19-Aug-2017.) $)
    nexple $p |- ( ( A e. NN0 /\ B e. RR /\ 2 <_ B  ) -> A <_ ( B ^ A ) ) $=
     ( cn0 wcel cr c2 cle wbr w3a cexp co cc0 wceq wi c1 id oveq2 breq12d letrd
     a1i vk vn cn wa simpr simpl2 simpl3 3jca cv caddc biidd imbi12d simpl 1nn0
     imbi2d 1re 2re 2nn nnge1 ax-mp expge1d cmul simp1 nnnn0d readdcld 3ad2ant2
     nn0red remulcld reexpcld leadd2dd times2d breqtrrd nn0ge0d simp2r lemul2ad
     syl recnd 0nn0 2nn0 nn0ge0 simp3 lemul1ad cc expp1 syl2anc 3expia ex nnind
     a2d 3impib 0le1 oveq2d exp0d eqtrd 3brtr4d elnn0 biimpi 3ad2ant1 mpjaodan
     wo ) ACDZBEDZFBGHZIZAUCDZABAJKZGHZALMZXDXEUDZXEXBXCIXGXIXEXBXCXDXEUEXAXBXC
     XEUFXAXBXCXEUGUHXEXBXCXGXBXCUDZUAUIZBXKJKZGHZNXJOBOJKZGHZNXJUBUIZBXPJKZGHZ
     NXJXPOUJKZBXSJKZGHZNXJXGNUAUBAXKOMZXJXJXMXOYBXJUKYBXKOXLXNGYBPXKOBJQRULXKX
     PMZXMXRXJYCXKXPXLXQGYCPXKXPBJQRUOXKXSMZXJXJXMYAYDXJUKYDXKXSXLXTGYDPXKXSBJQ
     RULXKAMZXJXJXMXGYEXJUKYEXKAXLXFGYEPXKABJQRULXJBOXBXCUMZOCDXJUNTXJOFBOEDZXJ
     UPTFEDZXJUQTZYFOFGHZXJFUCDYJURFUSUTTXBXCUEZSVAXPUCDZXJXRYAYLXJXRYANYLXJXRY
     AYLXJXRIZXSXQBVBKZXTGYMXSXPBVBKZYNYMXPOYMXPYMXPYLXJXRVCZVDZVGZYGYMUPTZVEZY
     MXPBYRXJYLXBXRYFVFZVHZYMXQBYMBXPUUAYQVIZUUAVHYMXSXPFVBKZYOYTYMXPFYRYHYMUQT
     ZVHUUBYMXSXPXPUJKUUDGYMOXPXPYSYRYRYMYLOXPGHYPXPUSVPVJYMXPYMXPYRVQVKVLYMFBX
     PUUEUUAYRYMXPYQVMYLXBXCXRVNVOSYMXPXQBYRUUCUUAXJYLLBGHXRXJLFBXJLLCDXJVRTVGY
     IYFLFGHZXJFCDUUFVSFVTUTTYKSVFYLXJXRWAWBSYMBWCDXPCDXTYNMYMBUUAVQYQBXPWDWEVL
     WFWGWIWHWJVPXDXHUDZLOAXFGLOGHUUGWKTXDXHUEZUUGXFBLJKOUUGALBJUUHWLUUGBUUGBXA
     XBXCXHUFVQWMWNWOXAXBXEXHWTZXCXAUUIAWPWQWRWS $.
  $}

  ${
    $d f h G $. $d f h R $. $d f h S $. $d f h T $. $d f h ph $.
    fcobij.1 $e |- ( ph -> G : S -1-1-onto-> T ) $.
    fcobij.2 $e |- ( ph -> R e. U ) $.
    fcobij.3 $e |- ( ph -> S e. V ) $.
    fcobij.4 $e |- ( ph -> T e. W ) $.
    $( Composing functions with a bijection yields a bijection between sets of
       functions. (Contributed by Thierry Arnoux, 25-Aug-2017.) $)
    fcobij $p |- ( ph -> ( f e. ( S ^m R ) |-> ( G o. f ) ) :
                                         ( S ^m R ) -1-1-onto-> ( T ^m R ) ) $=
      ( ccom wcel wa wf adantr syl2anc wceq vh cmap co ccnv cmpt eqid wf1o f1of
      cv syl elmapg biimpa fco mpbird f1ocnv 3syl cid cres simpr coeq2d syl6eqr
      wb coass simpll f1ococnv2 coeq1d simplrr 3eqtrrd f1ococnv1 simplrl impbid
      fcoi2 ex f1o2d ) AFUACBUBUCZDBUBUCZGFUIZNZGUDZUAUIZNZFVOVRUEZWBUFAVQVOOZP
      ZVRVPOZBDVRQZWDCDGQZBCVQQZWFAWGWCACDGUGZWGJCDGUHUJRAWCWHACHOZBEOZWCWHVBLK
      CBVQHEUKSULZBCDGVQUMSAWEWFVBZWCADIOZWKWMMKDBVRIEUKSRUNAVTVPOZPZWAVOOZBCWA
      QZWPDCVSQZBDVTQZWRAWSWOAWIDCVSUGWSJCDGUODCVSUHUPRAWOWTAWNWKWOWTVBMKDBVTIE
      UKSULZBDCVSVTUMSAWQWRVBZWOAWJWKXBLKCBWAHEUKSRUNAWCWOPZPZVQWATZVTVRTZXDXEX
      FXDXEPZVRGVSNZVTNZUQDURZVTNZVTXGVRGWANXIXGVQWAGXDXEUSUTGVSVTVCVAXGXHXJVTX
      GAWIXHXJTAXCXEVDZJCDGVEUPVFXGWTXKVTTXGAWOWTXLAWCWOXEVGXASBDVTVLUJVHVMXDXF
      XEXDXFPZWAVSGNZVQNZUQCURZVQNZVQXMWAVSVRNXOXMVTVRVSXDXFUSUTVSGVQVCVAXMXNXP
      VQXMAWIXNXPTAXCXFVDZJCDGVIUPVFXMWHXQVQTXMAWCWHXRAWCWOXFVJWLSBCVQVLUJVHVMV
      KVN $.

    $d f h O $. $d f h Q $. $d g h O $. $d g h R $. $d g h S $.
    $d f X $. $d f Y $.
    fcobijfs.5 $e |- ( ph -> O e. S ) $.
    fcobijfs.6 $e |- Q = ( G ` O ) $.
    fcobijfs.7 $e |- X =
                      { g e. ( S ^m R ) | ( `' g " ( _V \ { O } ) ) e. Fin } $.
    fcobijfs.8 $e |- Y =
                      { h e. ( T ^m R ) | ( `' h " ( _V \ { Q } ) ) e. Fin } $.
    $( Composing finitely supported functions with a bijection yields a
       bijection between sets of finitely supported functions.
       See also ~ mapfien . (Contributed by Thierry Arnoux, 25-Aug-2017.) $)
    fcobijfs $p |- ( ph -> ( f e. X |-> ( G o. f ) ) :  X -1-1-onto-> Y ) $=
      ( cv cid cres ccom cmpt wf1o ccnv cvv csn cdif cima cfn wcel cmap co crab
      nfcv nfv wceq eqidd imaeq1d eleq1d cbvrabcsf eqtr4i f1oi a1i elex mapfien
      cnveq syl wb ssrab2 eqsstri sseli wa coass f1of elmapi fco syl2an syl5eqr
      wf fcoi1 sylan2 mpteq2dva f1oeq1 mpbid ) ANOGNJGUDZUECUFZUGUGZUHZUIZNOGNJ
      WKUGZUHZUIZAICDCENOGWLJBKNHUDZUJZUKKULUMZUNZUOUPZHDCUQURZUSZIUDZUJZXAUNZU
      OUPZIXDUSUBXIXCIHXDXDHXDUTIXDUTXIHVAXCIVAXFWSVBZXDVCXJXHXBUOXJXGWTXAXFWSV
      LVDVEVFVGUCUACCWLUIACVHVIPACFUPCUKUPQCFVJVMZADLUPDUKUPRDLVJVMXKAEMUPEUKUP
      SEMVJVMTVKAWNWQVBWOWRVNAGNWMWPWKNUPAWKXDUPZWMWPVBNXDWKNXEXDUBXCHXDVOVPVQA
      XLVRZWMWPWLUGZWPJWKWLVSXMCEWPWEZXNWPVBADEJWEZCDWKWEXOXLADEJUIXPPDEJVTVMWK
      DCWACDEJWKWBWCCEWPWFVMWDWGWHNOWNWQWIVMWJ $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y C $.  $d x y ph $.  $d y ps $.  $d x ch $.
    frabbijd.1 $e |- F = ( x e. A |-> C ) $.
    frabbijd.2 $e |- ( ph -> F : A -1-1-onto-> B ) $.
    frabbijd.3 $e |- ( ( ph /\ x e. A /\ y = C ) -> ( ch <-> ps ) ) $.
    $( Build a bijection between restricted abstract builders, given a
       bijection between the base classes, decduction version.
       (Contributed by Thierry Arnoux, 17-Aug-2018.) $)
    frabbijd $p |- ( ph -> ( F |` { x e. A | ps } ) :
                               { x e. A | ps } -1-1-onto-> { y e. B | ch } ) $=
    ( crab ccnv cres wf1o syl wceq wb wcel wfun f1ofun funcnvcnv 3syl wf1 wss
      cima f1ocnv f1of1 ssrab2 f1ores sylancl mptpreima cv wa wi 3expia alrimiv
      wal wral f1of fmpt sylibr r19.21bi elrab3t syl2anc rabbidva syl5eq f1oeq3
      wf mpbid f1orescnv rescnvcnv f1oeq1 ax-mp sylib ) ABDFMZCEGMZINZNZVQOZPZV
      QVRIVQOZPZAVTUAZVRVQVSVROZPZWBAFGIPZIUAWEKFGIUBIUCUDAVRVSVRUGZWFPZWGAGFVS
      UEZVRGUFWJAGFVSPZWKAWHWLKFGIUHQGFVSUIQCEGUJGFVRVSUKULAWIVQRWJWGSAWIHVRTZD
      FMVQDFHVRIJUMAWMBDFADUNFTZUOZEUNHRZCBSZUPZEUSHGTZWMBSWOWREAWNWPWQLUQURAWS
      DFAFGIVJZWSDFUTAWHWTKFGIVAQDFGHIJVBVCVDCBEHGVEVFVGVHWIVQVRWFVIQVKVQVRVSVL
      VFWAWCRWBWDSIVQVMVQVRWAWCVNVOVP $.
  $}

  ${
    $d x A $. $d x F $. $d x Z $. $d x ph $.
    suppss3.1 $e |- G = ( x e. A |-> B ) $.
    suppss3.2 $e |- ( ph -> F Fn A ) $.
    suppss3.3 $e |- ( ( ph /\ x e. A /\ ( F ` x ) = Z ) -> B = Z ) $.
    $( Deduce a function's support's inclusion in another function's support.
       (Contributed by Thierry Arnoux, 7-Sep-2017.) $)
    suppss3 $p |- ( ph ->
                    ( `' G " ( _V \ { Z } ) ) C_ ( `' F " ( _V \ { Z } ) ) ) $=
      ( ccnv cvv csn cdif cima cmpt wcel wa wceq wn cnveqi imaeq1i cv cfv simpl
      eldif simplbi adantl wfn wb elpreima syl baibd notbid biimpd expimpd fvex
      wne eldifsn mpbiran necon2bbii syl6ibr syl5bi syl3anc suppss2 syl5eqss
      imp ) AFKZLGMNZOBCDPZKZVIOEKVIOZVHVKVIFVJHUAUBACDBVLGABUCZCVLNQZRAVMCQZVM
      EUDZGSZDGSAVNUEVNVOAVNVOVMVLQZTZVMCVLUFZUGUHAVNVQVNVOVSRZAVQVTAWAVPVIQZTZ
      VQAVOVSWCAVORZVSWCWDVRWBAVRVOWBAECUIVRVOWBRUJICVMVIEUKULUMUNUOUPWBVPGWBVP
      LQVPGURVMEUQVPLGUSUTVAVBVCVGJVDVEVF $.
  $}

  ${
    ffs2.1 $e |- C = ( B \ { Z } ) $.
    $( Rewrite a function's support based with its range rather than the
       universal class. See also ~ nn0supp for a more specific version.
       (Contributed by Thierry Arnoux, 27-Aug-2017.) $)
    ffs2 $p |- ( F : A --> B -> ( `' F " ( _V \ { Z } ) ) = ( `' F " C ) ) $=
      ( wf ccnv cvv cima csn cdif cdm crn dfdm4 dfrn4 eqtri wceq difpreima syl
      fdm syl5eqr fimacnv eqtr4d difeq1d wfun ffun imaeq2i syl5eq 3eqtr4d ) ABD
      GZDHZIJZULEKZJZLZULBJZUOLZULIUNLJZULCJZUKUMUQUOUKUMAUQUKUMDMZAVAULNUMDOUL
      PQABDUAUBABDUCUDUEUKDUFZUSUPRABDUGZIUNDSTUKVBUTURRVCVBUTULBUNLZJURCVDULFU
      HBUNDSUITUJ $.
  $}

  ${
    $d x A $.
    $( If a union is finite, then all its elements are finite. See ~ unifi .
       (Contributed by Thierry Arnoux, 27-Aug-2017.) $)
    unifi3 $p |- ( U. A e. Fin -> A C_ Fin ) $=
      ( vx cuni cfn wcel cv wss elssuni ssfi ex syl5 ssrdv ) ACZDEZBADBFZAEOMGZ
      NODEZOAHNPQMOIJKL $.
  $}

  ${
    $d x A $. $d x F $. $d x Z $.
    ffsrn.0 $e |- ( ph -> F e. _V ) $.
    ffsrn.1 $e |- ( ph -> Fun F ) $.
    ffsrn.2 $e |- ( ph -> ( `' F " ( _V \ { Z } ) ) e. Fin ) $.
    $( The range of a finitely supported function is finite.
       (Contributed by Thierry Arnoux, 27-Aug-2017.) $)
    ffsrn $p |- ( ph -> ran F e. Fin ) $=
      ( crn cvv cima cres cun cfn wss wceq eqtri reseq2i wfn sylancl wcel syl
      ccnv csn cdif undif1 ssv ssequn2 mpbi imaeq2i imaundi resundi eqtr3i wfun
      cdm dfdm4 dfrn4 wa df-fn fnresdm sylbir syl5reqr rneqd rnun a1i eqtrd wbr
      cdom wfo cnvimass fores fofn wi cnvexg imaexg 3syl fnrndomg domfi syl2anc
      mpd snfi cin df-ima funimacnv syl5eqr inss1 syl6eqss ssfi sylancr eqeltrd
      unfi ) ABGZBBUAZHCUBZUCZIZJZGZBWKWLIZJZGZKZLAWJWOWRKZGZWTABXAAXABWKHIZJZB
      BWKWMWLKZIZJZXDXAXFXCBXEHWKXEHWLKZHHWLUDWLHMXHHNWLUEWLHUFUGOUHPXGBWNWQKZJ
      XAXFXIBWKWMWLUIPBWNWQUJOUKABULZBUMZXCNZXDBNZEXKWKGXCBUNWKUOOXJXLUPBXCQXMB
      XCUQXCBURUSRUTVAXBWTNAWOWRVBVCVDAWPLSZWSLSZWTLSAWNLSWPWNVFVEZXNFAWOWNQZXP
      AWNBWNIZWOVGZXQAXJWNXKMXSEBWMVHWNBVIRWNXRWOVJTAWNHSZXQXPVKABHSWKHSXTDBHVL
      WKWMHVMVNWNHWOVOTVRWNWPVPVQAWLLSWSWLMXOCVSAWSWLWJVTZWLAWSBWQIZYABWQWAAXJY
      BYANEWLBWBTWCWLWJWDWEWLWSWFWGWPWSWIVQWH $.
  $}


  ${
    $d f g x A $. $d f g x B $. $d f g x C $. $d f g x V $. $d f g x W $.
    $d f g X $. $d f g x Z $.
    resf1o.1 $e |- X = { f e. ( B ^m A ) | ( `' f " ( B \ { Z } ) ) C_ C } $.
    resf1o.2 $e |- F = ( f e. X |-> ( f |` C ) ) $.
    $( Restriction of functions to a superset of their support creates a
       bijection. (Contributed by Thierry Arnoux, 12-Sep-2017.) $)
    resf1o $p |- ( ( ( A e. V /\ B e. W /\ C C_ A ) /\ Z e. B )
                                 -> F : X -1-1-onto-> ( B ^m C ) ) $=
      ( wcel wa cres cvv syl2anc wceq wf syl c0 vg vx wss w3a cmap cdif csn cxp
      co cv resexg adantl simpr difexg 3ad2ant1 snex xpexg sylancl adantr unexg
      cun adantlr ccnv cima rabeq2i anbi1i simprr simprll elmapi simp3 ad2antrr
      fssres simp2 simp1 ssexg elmapg mpbird eqeltrd biimpi reseq2d wfn fnresdm
      wb undif ffn 3syl eqtr2d resundi syl6eq wi eqcom imbi2i mpbi simprlr eqid
      cin ffs2 dfss1 3sstr4d simplr inundif fneq2i sylibr inindif a1i fnsuppres
      simpl syl3anc mpbid uneq12d eqtrd jca ad2ant2r fconstg snssi disjdif fun2
      ex fss syl21anc eqcomd feq12d biimpar cfv fveq1d ad3antlr fvun2 syl112anc
      fvconst 3eqtrd suppss eqsstr3d reseq1d res0 eqtr4i reseq2i 3eqtr4ri jca31
      fresaunres1 impbid syl5bb f1od ) AFLZBGLZCAUCZUDZIBLZMZDUAHBCUEUIZDUJZCNZ
      UAUJZACUFZIUGZUHZVAZEOOKUUJHLZUUKOLUUHUUJCHUKULUUFUULUUILZUUPOLZUUGUUFUUR
      MUURUUOOLZUUSUUFUURUMZUUFUUTUURUUFUUMOLZUUNOLUUTUUCUUDUVBUUEACFUNUOIUPUUM
      UUNOOUQURUSUULUUOUUIOUTPVBUUQUULUUKQZMUUJBAUEUIZLZUUJVCZBUUNUFZVDZCUCZMZU
      VCMZUUHUURUUJUUPQZMZUUQUVJUVCUVIDHUVDJVEVFUUHUVKUVMUUHUVKUVMUUHUVKMZUURUV
      LUVNUULUUKUUIUUHUVJUVCVGZUVNUUKUUILZCBUUKRZUVNABUUJRZUUEUVQUVNUVEUVRUUHUV
      EUVIUVCVHZUUJBAVIZSZUUFUUEUUGUVKUUCUUDUUEVJZVKZABCUUJVLPUUFUVPUVQWCZUUGUV
      KUUFUUDCOLZUWDUUCUUDUUEVMZUUFUUEUUCUWEUWBUUCUUDUUEVNZCAFVOPBCUUKGOVPPVKVQ
      VRUVNUUJUUKUUJUUMNZVAZUUPUVNUUJUUJCUUMVAZNZUWIUVNUWKUUJANZUUJUVNUUEUWKUWL
      QUWCUUEUWJAUUJUUEUWJAQZCAWDVSZVTSUVNUVRUUJAWAZUWLUUJQUWAABUUJWEZAUUJWBWFW
      GUUJCUUMWHWIUVNUUKUULUWHUUOUVNUVCWJUVNUUKUULQZWJUVOUVCUWQUVNUULUUKWKWLWMU
      VNUVFOUUNUFVDZACWPZUCZUWHUUOQZUVNUVHCUWRUWSUUHUVEUVIUVCWNUVNUVRUWRUVHQZUW
      AABUVGUUJIUVGWOWQZSUVNUUEUWSCQZUWCUUEUXDCAWRVSSWSUVNUVEUUGUWTUXAWCZUVSUUF
      UUGUVKWTUVEUUGMZUUJUWSUUMVAZWAZUWSUUMWPTQZUUGUXEUXFUWOUXHUXFUVEUVRUWOUVEU
      UGXGUVTUWPWFUXGAUUJACXAXBXCUXIUXFACXDXEUVEUUGUMUWSUUMUUJBIXFXHPXIXJXKXLXR
      UUHUVMUVKUUHUVMMZUVEUVIUVCUXJUUDUUCUVRUVEUUFUUDUUGUVMUWFVKUUFUUCUUGUVMUWG
      VKUXJUWJBUUPRZUVRUXJCBUULRZUUMBUUORZCUUMWPZTQZUXKUXJUURUXLUUFUURUURUUGUVL
      UVAXMUULBCVISZUXJUUGUXMUUFUUGUVMWTUUGUUMUUNUUORZUUNBUCUXMUUMIBXNZIBXOUUMU
      UNBUUOXSPSZUXOUXJCAXPZXECUUMBUULUUOXQXTUXJUWJABUUPUUJUXJUUJUUPUUHUURUVLVG
      ZYAUXJUUEUWMUUFUUEUUGUVMUWBVKUWNSYBXIZUUDUUCMUVEUVRBAUUJGFVPYCXTUXJUVHUWR
      CUXJUVRUXBUYBUXCSUXJABUBUUJCIUYBUXJUBUJZUUMLZMZUYCUUJYDUYCUUPYDZUYCUUOYDZ
      IUYEUYCUUJUUPUXJUVLUYDUYAUSYEUYEUULCWAZUUOUUMWAZUXOUYDUYFUYGQUYEUXLUYHUXJ
      UXLUYDUXPUSCBUULWESUYEUXQUYIUUGUXQUUFUVMUYDUXRYFZUUMUUNUUOWESUXOUYEUXTXEU
      XJUYDUMZCUUMUULUUOUYCYGYHUYEUXQUYDUYGIQUYJUYKUUMIUYCUUOYIPYJYKYLUXJUUKUUP
      CNZUULUXJUUJUUPCUYAYMUXJUXLUXMUULUXNNZUUOUXNNZQZUYLUULQUXPUXSUYOUXJUUOTNZ
      UULTNZUYNUYMUYPTUYQUUOYNUULYNYOUXNTUUOUXTYPUXNTUULUXTYPYQXECUUMBUULUUOYSX
      HWGYRXRYTUUAUUB $.
  $}

  $( Two things in a binary relation belong to the relation's domain.
     (Contributed by Thierry Arnoux, 29-Aug-2017.) $)
  brelg $p |- ( ( R C_ ( C X. D ) /\ A R B ) -> ( A e. C /\ B e. D ) ) $=
    ( cxp wss wbr wa wcel id ssbrd imp brxp sylib ) ECDFZGZABEHZIABPHZACJBDJIQR
    SQEPABQKLMABCDNO $.

  $( A relation (set) is finite if and only if both its domain and range are
     finite. (Contributed by Thierry Arnoux, 27-Aug-2017.) $)
  relfi $p |- ( Rel A ->
                       ( A e. Fin <-> ( dom A e. Fin /\ ran A e. Fin ) ) ) $=
    ( wrel cfn wcel cdm crn wa wi dmfi rnfi jca a1i cxp adantl relssdmrn adantr
    wss xpfi ssfi syl2anc ex impbid ) ABZACDZAEZCDZAFZCDZGZUDUIHUCUDUFUHAIAJKLU
    CUIUDUCUIGUEUGMZCDZAUJQZUDUIUKUCUEUGRNUCULUIAOPUJASTUAUB $.

  ${
    $d x y R $.
    $( Domain of an ordered-pair class abstraction.
       (Contributed by Thierry Arnoux, 31-Aug-2017.) $)
    opabdm $p |- ( R = { <. x , y >. | ph } -> dom R = { x | E. y ph } ) $=
      ( copab wceq cdm cv wbr wex cab df-dm nfcv nfopab1 nfeq nfopab2 cop df-br
      wcel eleq2 opabid syl6bb syl5bb exbid abbid syl5eq ) DABCEZFZDGBHZCHZDIZC
      JZBKACJZBKBCDLUHULUMBBDUGBDMABCNOUHUKACCDUGCDMABCPOUKUIUJQZDSZUHAUIUJDRUH
      UOUNUGSADUGUNTABCUAUBUCUDUEUF $.

    $( Range of an ordered-pair class abstraction.
       (Contributed by Thierry Arnoux, 31-Aug-2017.) $)
    opabrn $p |- ( R = { <. x , y >. | ph } -> ran R = { y | E. x ph } ) $=
      ( copab wceq crn cv wbr wex cab dfrn2 nfcv nfopab2 nfeq nfopab1 cop df-br
      wcel eleq2 opabid syl6bb syl5bb exbid abbid syl5eq ) DABCEZFZDGBHZCHZDIZB
      JZCKABJZCKBCDLUHULUMCCDUGCDMABCNOUHUKABBDUGBDMABCPOUKUIUJQZDSZUHAUIUJDRUH
      UOUNUGSADUGUNTABCUAUBUCUDUEUF $.
  $}


  ${
    $d x y z $. $d z A $. $d z B $.
    eqrelrd2.1 $e |- F/ x ph $.
    eqrelrd2.2 $e |- F/ y ph $.
    eqrelrd2.3 $e |- F/_ x A $.
    eqrelrd2.4 $e |- F/_ y A $.
    eqrelrd2.5 $e |- F/_ x B $.
    eqrelrd2.6 $e |- F/_ y B $.
    $( A subclass relationship depends only on a relation's ordered pairs.
       Theorem 3.2(i) of [Monk1] p. 33.  (Contributed by NM, 2-Aug-1994.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.) (Revised by Thierry
       Arnoux, 6-Nov-2017.) $)
    ssrelf $p |- ( Rel A -> ( A C_ B <->
                A. x A. y ( <. x , y >. e. A -> <. x , y >. e. B ) ) ) $=
      ( vz wss cv wcel wi wal nfss alrimi nfel wrel cop ssel wceq wex nfv eleq1
      imbi12d biimprcd 2alimi nfcv nfim 19.23 albii bitri sylib com23 a2d alimd
      cvv cxp df-rel dfss2 elvv imbi2i 3bitri 3imtr4g com12 impbid2 ) DUAZDEMZB
      NCNUBZDOZVLEOZPZCQZBQZVKVPBBDEHJRVKVOCCDEIKRDEVLUCSSVQVJVKVQLNZDOZVRVLUDZ
      CUEZBUEZPZLQZVSVREOZPZLQVJVKVQWCWFLVQLUFVQVSWBWEVQWBVSWEVQVTWFPZCQZBQZWBW
      FPZVOWGBCVTWFVOVTVSVMWEVNVRVLDUGVRVLEUGUHUIUJWIWAWFPZBQWJWHWKBVTWFCVSWECC
      VRDCVRUKZITCVREWLKTULUMUNWAWFBVSWEBBVRDBVRUKZHTBVREWMJTULUMUOUPUQURUSVJDU
      TUTVAZMVSVRWNOZPZLQWDDVBLDWNVCWPWCLWOWBVSBCVRVDVEUNVFLDEVCVGVHVI $.

    eqrelrd2.7 $e |- ( ph -> ( <. x , y >. e. A <-> <. x , y >. e. B ) ) $.
    $( A version of ~ eqrelrdv2 with explicit non-free declarations.
       (Contributed by Thierry Arnoux, 28-Aug-2017.) $)
    eqrelrd2 $p |- ( ( ( Rel A /\ Rel B ) /\ ph ) -> A = B ) $=
      ( wrel wa cv wcel wb wal alrimi wss cop adantl wi ssrelf bi2anan9 2albiim
      wceq eqss 3bitr4g adantr mpbird ) DMZEMZNZANDEUGZBOCOUAZDPZUPEPZQZCRZBRZA
      VAUNAUTBFAUSCGLSSUBUNUOVAQAUNDETZEDTZNUQURUCCRBRZURUQUCCRBRZNUOVAULVBVDUM
      VCVEABCDEFGHIJKUDABCEDFGJKHIUDUEDEUHUQURBCUFUIUJUK $.
  $}

  $( Abstract builder restricted to another restricted abstract builder
     (Contributed by Thierry Arnoux, 30-Aug-2017.) $)
  rabrab $p |- { x e. { x e. A | ph } | ps } = { x e. A | ( ph /\ ps ) } $=
    ( cv crab wcel wa cab rabid anbi1i anass bitri abbii df-rab 3eqtr4i ) CEZAC
    DFZGZBHZCIQDGZABHZHZCIBCRFUBCDFTUCCTUAAHZBHUCSUDBACDJKUAABLMNBCROUBCDOP $.

  ${
    $d f A $. $d f B $. $d f C $.
    maprnin.1 $e |- A e. _V $.
    maprnin.2 $e |- B e. _V $.
    $( Restricting the range of the mapping operator
       (Contributed by Thierry Arnoux, 30-Aug-2017.) $)
    maprnin $p |- ( ( B i^i C ) ^m A ) = { f e. ( B ^m A ) | ran f C_ C } $=
      ( cin cv wf cab cmap co wcel crn wss wa crab wfn wb ffn baibr syl pm5.32i
      df-f elmap anbi1i fin 3bitr4ri abbii inex1 mapval df-rab 3eqtr4i ) ABCGZD
      HZIZDJUOBAKLZMZUONCOZPZDJUNAKLUSDUQQUPUTDABUOIZUSPVAACUOIZPUTUPVAUSVBVAUO
      ARZUSVBSABUOTVBVCUSACUOUDUAUBUCURVAUSBAUOFEUEUFABCUOUGUHUIUNADBCFUJEUKUSD
      UQULUM $.
  $}

  ${
    $d w x y z A $. $d w x y z F $. $d x y R $. $d w ph $.
    fpwrelmapffslem.1 $e |- A e. _V $.
    fpwrelmapffslem.2 $e |- B e. _V $.
    fpwrelmapffslem.3 $e |- ( ph -> F : A --> ~P B ) $.
    fpwrelmapffslem.4 $e |- ( ph ->
                        R = { <. x , y >. | ( x e. A /\ y e. ( F ` x ) ) } ) $.
    $( Lemma for ~ fpwrelmapffslem . For this theorem, the sets ` A `
       and ` B ` could be infinite, but the relation ` R ` itself is finite.
       (Contributed by Thierry Arnoux, 1-Sep-2017.) $)
    fpwrelmapffslem $p |- ( ph -> ( R e. Fin
              <-> ( ran F C_ Fin /\ ( `' F " ( _V \ { (/) } ) ) e. Fin ) ) ) $=
      ( vz cfn wcel wa wb wceq syl wex a1i vw cdm crn ccnv cvv c0 csn cdif cima
      wss wrel cfv copab relopab releq mpbiri relfi cab wrex cuni rexcom4 ancom
      cv exbii nfv fvex ceqsex bitr3i rexbii r19.42v 3bitr3ri df-rex bitr2i vex
      eleq2 biidd eleq1 anbi12d exbid elab eluniab 3bitr4g eleq1d adantr wi cpw
      eqrdv wf wfn ffn fnrnfv 3syl sylancl wfun ffun opabdm crab feqmptd cnveqd
      fex cmpt imaeq1d mptpreima syl6eq wne fnniniseg2 n0 rabbiia df-rab 19.42v
      eqid abbii eqtr4i 3eqtrd eqtr4d biimpa ffsrn eqeltrrd unifi unifi3 impbid
      3eqtr3d ex bitr4d opabrn sseq1d 3bitr4d pm5.32da anbi1d bitrd 3bitrd ) AF
      MNZFUBZMNZFUCZMNZOZGUDZUEUFUGUHZUIZMNZGUCZMUJZOZUUCUUAOZAFUKZYLYQPAFBVCZD
      NZCVCZUUGGULZNZOZBCUMZQZUUFKUUNUUFUUMUKUULBCUNFUUMUOUPRFUQRAYQYNUUCOUUDAY
      NYPUUCAYNOZUULBSZCURZMNZLVCZUUJQZBDUSZLURZMUJZYPUUCUUOUURUVBUTZMNZUVCAUUR
      UVEPYNAUUQUVDMAUAUUQUVDAUUHUAVCZUUJNZOZBSZUVFUUSNZUVAOZLSZUVFUUQNUVFUVDNU
      VIUVLPAUVLUVGBDUSZUVIUVJUUTOZLSZBDUSUVNBDUSZLSUVMUVLUVNBLDVAUVOUVGBDUVOUU
      TUVJOZLSUVGUVQUVNLUUTUVJVBVDUVJUVGLUUJUVGLVEUUGGVFUUSUUJUVFVOVGVHVIUVPUVK
      LUVJUUTBDVJVDVKUVGBDVLVMTUUPUVICUVFUAVNUUIUVFQZUULUVHBUVRBVEUVRUUHUUHUUKU
      VGUVRUUHVPUUIUVFUUJVQVRVSVTUVALUVFWAWBWGWCWDUUOUVCUVEUUOUVBMNZUVCUVEWEUUO
      UUBUVBMAUUBUVBQZYNADEWFZGWHZGDWIZUVTJDUWAGWJZBLDGWKWLWDZUUOGUFAGUENZYNAUW
      BDUENUWFJHDUWAUEGWTWMWDAGWNZYNAUWBUWGJDUWAGWORWDAYNUUAAYMYTMAYMUULCSZBURZ
      YTAUUNYMUWIQKUULBCFWPRAYTUUJYSNBDWQZUUKCSZBDWQZUWIAYTBDUUJXAZUDZYSUIUWJAY
      RUWNYSAGUWMABDUWAGJWRWSXBBDUUJYSUWMUWMXKXCXDZAYTUUJUFXEZBDWQZUWJUWLAUWBUW
      CYTUWQQJUWDBDUFGXFWLUWOUWQUWLQAUWPUWKBDUWPUWKPUUHCUUJXGTXHTYBUWLUWIQAUWLU
      UHUWKOZBURUWIUWKBDXIUWHUWRBUUHUUKCXJXLXMTXNXOWCZXPXQXRUVSUVCUVEUVBXSYCRUV
      EUVCWEUUOUVBXTTYAYDAYPUURPYNAYOUUQMAUUNYOUUQQKUULBCFYERWCWDUUOUUBUVBMUWEY
      FYGYHAYNUUAUUCUWSYIYJUUDUUEPAUUAUUCVBTYK $.
  $}

  ${
     $d f r x y A $. $d f r x y B $.
    fpwrelmap.1 $e |- A e. _V $.
    fpwrelmap.2 $e |- B e. _V $.
    fpwrelmap.3 $e |- M = ( f e. ( ~P B ^m A ) |->
       { <. x , y >. | ( x e. A /\ y e. ( f ` x ) ) } ) $.
    $( Define a canonical mapping between functions from ` A ` into subsets of
       ` B ` and the relations with domain ` A ` and range within ` B ` .
       Note that the same relation is used in ~ axdc2lem and ~ marypha2lem1 .
       (Contributed by Thierry Arnoux,  28-Aug-2017.) $)
    fpwrelmap $p |- M : ( ~P B ^m A ) -1-1-onto-> ~P ( A X. B ) $=
      ( wcel wa cvv a1i adantr ex wss wceq wb nfv nfan vr cpw cmap co wf1o wtru
      cxp cv cfv copab wbr crab cmpt wi wal cab simpr ffvelrnda elelpwi syl2anc
      elmapi alrimiv abss sylbir syl opabex3d adantl mptex imdistanda ssopab2dv
      ssex df-xp sseq12d mpbird vex elpwg ax-mp sylibr feqmptd nfcv nfeq df-rab
      nfopab1 nfopab2 adantlr imp cop df-br eleq2 opabid syl6bb syl5bb ad2antlr
      cdm elfvdm fdm eleqtrd pm4.71rd ad2antrr bitr4d bicomd biimpa jca adantld
      biimpd impbid abbid abid2 3eqtr2rd mpteq2da eqtrd ssrab2 ssexi mpbir eqid
      wf fmptd feq1d pwex elmapg mp2an wrel biimpi syl6ss df-rel relopab nfmpt1
      xpss nfrab1 nfmpt brelg sylan simpld simprd simpll fveq1d fvmpt2 syl21anc
      id nfci mpan2 sylan9eq eleq2d mpbir2and simplbda expimpd syl5bbr eqrelrd2
      rabid syl6bbr impbii f1od trud ) DUBZCUCUDZCDUGZUBZFUEUFEUAUUOUUQAUHZCJZB
      UHZUUREUHZUIZJZKZABUJZACUURUUTUAUHZUKZBDULZUMZFLLIUVAUUOJZUVELJUFUVJUVCAB
      CCLJZUVJGMUVJUUSKZUVCUUTDJZUNZBUOZUVCBUPZLJZUVLUVNBUVLUVCUVMUVLUVCKUVCUVB
      UUNJZUVMUVLUVCUQUVLUVRUVCUVJCUUNUURUVAUVAUUNCVAZURNUUTUVBDUSUTOZVBUVOUVPD
      PUVQUVCBDVCUVPDHVKVDVEVFVGUVILJUFUVFUUQJZKACUVHGVHMUVJUVFUVEQZKZUWAUVAUVI
      QZKZRUFUWCUWEUWCUWAUWDUWCUVFUUPPZUWAUWCUWFUVEUUSUVMKZABUJZPZUVJUWIUWBUVJU
      VDUWGABUVJUUSUVCUVMUVTVIVJNUWCUVFUVEUUPUWHUVJUWBUQUUPUWHQUWCABCDVLMVMVNUV
      FLJUWAUWFRUAVOUVFUUPLVPVQZVRUWCUVAACUVBUMZUVIUVJUVAUWKQUWBUVJACUUNUVAUVSV
      SNUWCACUVBUVHUVJUWBAUVJASAUVFUVEAUVFVTZUVDABWCZWATUWCUUSKZUVHUVMUVGKZBUPZ
      UVPUVBUVHUWPQUWNUVGBDWBMUWNUVCUWOBUWCUUSBUVJUWBBUVJBSBUVFUVEBUVFVTZUVDABW
      DZWATUUSBSZTUWNUVCUWOUWNUVCUWOUWNUVCKUVMUVGUWNUVCUVMUVJUUSUVNUWBUVTWEWFUW
      NUVCUVGUWNUVGUVCUWNUVGUVDUVCUWBUVGUVDRUVJUUSUVGUURUUTWGZUVFJZUWBUVDUURUUT
      UVFWHZUWBUXAUWTUVEJZUVDUVFUVEUWTWIUVDABWJZWKWLWMUVJUVCUVDRUWBUUSUVJUVCUUS
      UVJUVCUUSUVJUVCKUURUVAWNZCUVCUURUXEJUVJUUTUURUVAWOVGUVJUXECQZUVCUVJCUUNUV
      AXPZUXFUVSCUUNUVAWPVENWQOWRWSWTZXAXBXCOUWNUVGUVCUVMUWNUVGUVCUXHXEXDXFXGUV
      PUVBQUWNBUVBXHMXIXJXKXCUWEUVJUWBUWEUXGUVJUWEUXGCUUNUVIXPZUWAUXIUWDUWAACUV
      HUUNUVIUVHUUNJZUWAUUSKUXJUVHDPZUVGBDXLZUVHLJZUXJUXKRUVHDHUXLXMZUVHDLVPVQX
      NMUVIXOZXQNUWECUUNUVAUVIUWAUWDUQZXRVNUUNLJUVKUVJUXGRDHXSGUUNCUVALLXTYAVRU
      WEUVFYBZUVEYBZUWEUWBUWEUVFLLUGZPUXQUWEUVFUUPUXSUWAUWFUWDUWAUWFUWJYCZNCDYH
      YDUVFYEVRUXRUWEUVDABYFMUWEYSUWEABUVFUVEUWAUWDAUWAASAUVAUVIAUVAVTACUVHYGWA
      TUWAUWDBUWABSBUVAUVIBUVAVTBACUVHBACUWSYTUVGBDYIYJWATUWLUWQUWMUWRUWEUXAUVD
      UXCUXAUVGUWEUVDUXBUWEUVGUVDUWEUVGUVDUWEUVGKZUUSUVCUYAUUSUVMUWAUVGUWGUWDUW
      AUWFUVGUWGUXTUURUUTCDUVFYKYLWEZYMZUYAUVCUVMUVGUYAUUSUVMUYBYNUWEUVGUQUYAUW
      AUWDUUSUVCUWORUWAUWDUVGYOUWEUWDUVGUXPNUYCUWEUUSKZUVCUUTUVHJUWOUYDUVBUVHUU
      TUWEUUSUVBUURUVIUIZUVHUWEUURUVAUVIUXPYPUUSUXMUYEUVHQUXNACUVHLUVIUXOYQUUAU
      UBUUCUVGBDUUIWKZYRUUDXCOUWEUUSUVCUVGUYDUVCUVGUYDUVCUVMUVGUYFUUEOUUFXFUUGU
      XDUUJUUHYRXCUUKMUULUUM $.

    fpwrelmapffs.1 $e |- S = { f e. ( ( ~P B i^i Fin ) ^m A ) |
       ( `' f " ( _V \ { (/) } ) ) e. Fin } $.
    $( Define a canonical mapping between finite relations (finite subsets of a
       cartesian product) and functions with finite support into finite subsets
       (Contributed by Thierry Arnoux,  28-Aug-2017.) $)
    fpwrelmapffs $p |- ( M |` S ) : S -1-1-onto-> ( ~P ( A X. B ) i^i Fin ) $=
      ( vr cv cfn cvv wcel crab wf1o wceq wb crn wss ccnv c0 csn cdif cima cmap
      wa cpw co cxp cres cin wtru cfv copab fpwrelmap a1i wf simpl elmapg mp2an
      pwex sylib simpr fpwrelmapffslem 3adant1 frabbijd trud nfcv nfrab1 rabeqf
      maprnin ax-mp rabrab 3eqtri dfin5 f1oeq23 reseq2i f1oeq1 bitr2i mpbi ) FM
      ZUANUBZWDUCOUDUEUFUGNPZUIZFDUJZCUHUKZQZLMZNPZLCDULUJZQZGWJUMZRZEWMNUNZGEU
      MZRZWPUOWGWLFLWIWMAMZCPBMWTWDUPPUIABUQZGJWIWMGRUOABCDFGHIJURUSWDWIPZWKXAS
      ZWLWGTUOXBXCUIZABCDWKWDHIXDXBCWHWDUTZXBXCVAWHOPCOPXBXETDIVDZHWHCWDOOVBVCV
      EXBXCVFVGVHVIVJWSWJWNWRRZWPEWJSWQWNSWSXGTEWFFWHNUNCUHUKZQZWFFWEFWIQZQZWJK
      XHXJSXIXKSCWHNFHXFVNWFFXHXJFXHVKWEFWIVLVMVOWEWFFWIVPVQZLWMNVREWJWQWNWRVSV
      CWRWOSXGWPTEWJGXLVTWJWNWRWOWAVOWBWC $.
  $}

  ${
    $d k F $. $d k M $. $d k S $. $d k ph $.
    fsumcvg4.s $e |- S = ( ZZ>= ` M ) $.
    fsumcvg4.m $e |- ( ph -> M e. ZZ ) $.
    fsumcvg4.c $e |- ( ph -> F : S --> CC ) $.
    fsumcvg4.f $e |- ( ph -> ( `' F " ( CC \ { 0 } ) ) e. Fin ) $.
    $( A serie with finite support is a finite sum, and therefore converges.
       (Contributed by Thierry Arnoux, 6-Sep-2017.) $)
    fsumcvg4 $p |- ( ph -> seq M ( + , F ) e. dom ~~> ) $=
      ( vk cc cc0 cdif cima wceq 3syl syl wcel wa wo eqid ccnv csn cv wfun ffun
      cfv wf difpreima difss syl6eqss fimacnv sseqtrd wn cif exmidd biantru a1i
      wb wne crab cvv ffs2 wfn fnniniseg2 eqtr3d eleq2d rabid syl6bb necon2bbid
      baibd biimprd pm4.71d orbi12d mpbid eqif sylibr sselda ffvelrnda fsumcvg3
      ffn syldan ) ACUAZJKUBZLZMZIUCZCUFZICDBEFHAWEWBJMZBAWEWHWBWCMZLZWHABJCUGZ
      CUDWEWJNGBJCUEJWCCUHOWHWIUIUJAWKWHBNGBJCUKPULZAWFBQZRZWFWEQZWGWGNZRZWOUMZ
      WGKNZRZSZWGWOWGKUNNWNWOWRSXAWNWOUOWNWOWQWRWTWOWQURWNWPWOWGTUPUQWNWRWSWNWS
      WRWNWOWGKAWOWMWGKUSZAWOWFXBIBUTZQWMXBRAWEXCWFAWBVAWCLMZWEXCAWKXDWENGBJWDC
      KWDTVBPAWKCBVCXDXCNGBJCVTIBKCVDOVEVFXBIBVGVHVJVIVKVLVMVNWOWGWGKVOVPAWOWMW
      GJQAWEBWFWLVQABJWFCGVRWAVS $.
  $}

$[ set/mbox/ta/eulerpart.mm $]
$[ set/mbox/ta/proba.mm $]
$[ set/mbox/ta/ballot.mm $]

$( (End of Thierry Arnoux's mathbox.) $)
