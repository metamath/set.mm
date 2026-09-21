$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Jeff Madsen
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logic and set theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A w x y z $.  $d B w x z $.  $d C w x y $.  $d D w x y $.  $d F w x y $.
    $d ph w x z $.  $d ps w x y $.  $d ch w x y $.
    unirep.1 $e |- ( y = D -> ( ph <-> ps ) ) $.
    unirep.2 $e |- ( y = D -> B = C ) $.
    unirep.3 $e |- ( y = z -> ( ph <-> ch ) ) $.
    unirep.4 $e |- ( y = z -> B = F ) $.
    unirep.5 $e |- B e. _V $.
    $( Define a quantity whose definition involves a choice of representative,
       but which is uniquely determined regardless of the choice.  (Contributed
       by Jeff Madsen, 1-Jun-2011.) $)
    unirep $p |- ( ( A. y e. A A. z e. A ( ( ph /\ ch ) -> B = F ) /\
            ( D e. A /\ ps ) ) -> ( iota x E. y e. A ( ph /\ x = B ) ) = C ) $=
      ( wa wceq wi wrex vw wral cv cio eqidd ancli eqeq2d anbi12d rspcev sylan2
      wcel adantl cvv weu wb csb nfcvd csbiegf csbex eqeltrrdi ad2antrl wex wal
      eqeq1 anbi2d rexbidv spcegv adantr r19.29 pm3.35 eqeq12 syl5ibrcom ancoms
      syl mpd an4 expimpd biimtrid ancomsd expdimp rexlimivw imp sylan an32s ex
      alrimivv cbvrexvw bitrdi eu4 sylanbrc iota2 syl2anc mpbid ) ACQZHKRZSZFGU
      BZEGUBZJGUKZBQZQZAIHRZQZEGTZADUCZHRZQZEGTZDUDIRZWTXDWRBWSBIIRZQZXDBXJBIUE
      UFXCXKEJGEUCZJRZABXBXJLXMHIIMUGUHUIUJZULXAIUMUKZXHDUNZXDXIUOWSXOWRBWSIEJH
      UPUMEJHIGWSEIUQMUREJHPUSUTZVAXAXHDVBZXHCUAUCZKRZQZFGTZQXEXSRZSZUAVCDVCXPW
      TXRWRWTXDXRXNWSXDXRSZBWSXOYEXQXHXDDIUMXEIRZXGXCEGYFXFXBAXEIHVDVEVFZVGVNVH
      VOULXAYDDUAWRYDWTWRXHYBYCWRXHQWQXGQZEGTYBYCSZWQXGEGVIYHYIEGYHYBYCWQYBXGYC
      WQYBQWPYAQZFGTZXGYCWPYAFGVIYKXGYCYJXGYCSFGWPYAXGYCWPXGYAYCXGYAQWNXFXTQZQW
      PYCAXFCXTVPWPWNYLYCWNWPYLYCSWNWPQYCYLWOWNWOVJXEHXSKVKVLVMVQVRVSVTWAWBWCWD
      WEWAVNVQVHWFXHYBDUAYCXHAXSHRZQZEGTYBYCXGYNEGYCXFYMAXEXSHVDVEVFYNYAEFGXLFU
      CRZACYMXTNYOHKXSOUGUHWGWHWIWJXHXDDIUMYGWKWLWM $.
  $}

  ${
    $d ph x z $.  $d B x y z $.  $d A x z $.
    cover2.1 $e |- B e. _V $.
    cover2.2 $e |- A = U. B $.
    $( Two ways of expressing the statement "there is a cover of ` A ` by
       elements of ` B ` such that for each set in the cover, ` ph ` ".  Note
       that ` ph ` and ` x ` must be distinct.  (Contributed by Jeff Madsen,
       20-Jun-2010.) $)
    cover2 $p |- ( A. x e. A E. y e. B ( x e. y /\ ph )
                        <-> E. z e. ~P B ( U. z = A /\ A. y e. z ph ) ) $=
      ( cv wcel wa wrex wral cuni wceq cpw crab cvv ssrab2 eleq2 wb nfra1 sseli
      elpwi2 wal unissi eleqtrrdi imbitrrdi impbid2 alrimi dfcleq sylibr nfrab1
      rsp elunirab nfeq2 rabid simprbi biimtrdi ralrimi eqeq1d anbi1d mpbiran2d
      unieq rspcev sylancr wi elpwi r19.29r expcom ssrexv sylan9r sylan biimpar
      wss eluni2 sylib impel anassrs ralrimiva anasss ancom2s rexlimiva impbii
      ) BIZCIZJZAKZCFLZBEMZDIZNZEOZACWKMZKZDFPZLZWJACFQZWPJWRNZEOZWQWRFRGACFSZU
      DWJWEWSJZWEEJZUAZBUEWTWJXDBWIBEUBWJXBXCXBWEFNZEWSXEWEWRFXAUFUCHUGWJXCWIXB
      WIBEUNACWEFUOUHUIUJBWSEUKULWOWTDWRWPWKWROZWOWTWNXFACWKCWKWRACFUMUPXFWFWKJ
      WFWRJZAWKWRWFTXGWFFJAACFUQURUSUTXFWMWTWNXFWLWSEWKWRVDVAVBVCVEVFWOWJDWPWKW
      PJZWNWMWJXHWNWMWJXHWNKZWMKWIBEXIWMXCWIXIWGCWKLZWIWMXCKZXHWKFVOZWNXJWIVGWK
      FVHWNXJWHCWKLZXLWIXJWNXMWGACWKVIVJWHCWKFVKVLVMXKWEWLJZXJWMXNXCWLEWETVNCWE
      WKVPVQVRVSVTWAWBWCWD $.
  $}

  ${
    $d ph b x z $.  $d B b x y z $.  $d A b x z $.
    cover2g.1 $e |- A = U. B $.
    $( Two ways of expressing the statement "there is a cover of ` A ` by
       elements of ` B ` such that for each set in the cover, ` ph ` ".  Note
       that ` ph ` and ` x ` must be distinct.  (Contributed by Jeff Madsen,
       21-Jun-2010.) $)
    cover2g $p |- ( B e. C -> ( A. x e. A E. y e. B ( x e. y /\ ph )
                        <-> E. z e. ~P B ( U. z = A /\ A. y e. z ph ) ) ) $=
      ( vb wel wa cv wrex cuni wral wceq cpw unieq eqtr4di rexeq raleqbidv pweq
      eqeq2d anbi1d rexeqbidv vex eqid cover2 vtoclbg ) BCJAKZCILZMZBUKNZODLZNZ
      UMPZACUNOZKZDUKQZMUJCFMZBEOUOEPZUQKZDFQZMIFGUKFPZULUTBUMEVDUMFNEUKFRHSZUJ
      CUKFTUAVDURVBDUSVCUKFUBVDUPVAUQVDUMEUOVEUCUDUEABCDUMUKIUFUMUGUHUI $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d ch x y $.
    brabg2.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    brabg2.2 $e |- ( y = B -> ( ps <-> ch ) ) $.
    brabg2.3 $e |- R = { <. x , y >. | ph } $.
    brabg2.4 $e |- ( ch -> A e. C ) $.
    $( Relation by a binary relation abstraction.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    brabg2 $p |- ( B e. D -> ( A R B <-> ch ) ) $=
      ( wcel wbr cvv brabg com3l mpdi relopabiv brrelex1i biimpd exbiri impbid
      wi wa ex ) GIOZFGJPZCUIUJFQOZCFGJADEJMUAUBUKUIUJCUKUIUJCUFUKUIUGUJCABCDEF
      GQIJKLMRUCUHSTUICFHOZUJNULUICUJULUIUJCABCDEFGHIJKLMRUDSTUE $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d ch x y $.
    opelopab3.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    opelopab3.2 $e |- ( y = B -> ( ps <-> ch ) ) $.
    opelopab3.3 $e |- ( ch -> A e. C ) $.
    $( Ordered pair membership in an ordered pair class abstraction, with a
       reduced hypothesis.  (Contributed by Jeff Madsen, 29-May-2011.) $)
    opelopab3 $p |- ( B e. D -> ( <. A , B >. e.
                            { <. x , y >. | ph } <-> ch ) ) $=
      ( wcel cop copab cvv wa cxp anim1i ancoms elopaelxp opelxp1 syl opelopabg
      elexd pm5.21nd ) GIMZFGNZADEOMZCFPMZUGQZUIUGUKUIUJUGUIUHPPRMUJADEUHUAFGPP
      UBUCSTCUGUKCUJUGCFHLUESTABCDEFGPIJKUDUF $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d F x y $.  $d G x y $.  $d H x y $.
    $( Cancellation of a surjective function from the right side of a
       composition.  (Contributed by Jeff Madsen, 1-Jun-2011.)  (Proof
       shortened by Mario Carneiro, 27-Dec-2014.) $)
    cocanfo $p |- ( ( ( F : A -onto-> B /\ G Fn B /\ H Fn B )
                                    /\ ( G o. F ) = ( H o. F ) ) -> G = H ) $=
      ( vx vy wfo wfn ccom wceq wa cv cfv wral syl fvco3 sylan wb fveq2 wcel wf
      w3a simplr fveq1d simpl1 fof 3eqtr3d ralrimiva eqeq12d cbvfo mpbid eqfnfv
      3adant1 adantr mpbird ) ABCHZDBIZEBIZUCZDCJZECJZKZLZDEKZFMZDNZVFENZKZFBOZ
      VDGMZCNZDNZVLENZKZGAOZVJVDVOGAVDVKAUAZLZVKVANZVKVBNZVMVNVRVKVAVBUTVCVQUDU
      EVDABCUBZVQVSVMKVDUQWAUQURUSVCUFZABCUGPZABVKDCQRVDWAVQVTVNKWCABVKECQRUHUI
      VDUQVPVJSWBVOVIGFABCVLVFKVMVGVNVHVLVFDTVLVFETUJUKPULUTVEVJSZVCURUSWDUQFBD
      EUMUNUOUP $.
  $}

  ${
    brresi2.1 $e |- B e. _V $.
    $( Restriction of a binary relation.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    brresi2 $p |- ( A ( R |` C ) B -> A R B ) $=
      ( cres resss ssbri ) DCFDABDCGH $.
  $}

  ${
    $d ph x $.  $d ph y $.
    fnopabeqd.1 $e |- ( ph -> B = C ) $.
    $( Equality deduction for function abstractions.  (Contributed by Jeff
       Madsen, 19-Jun-2011.) $)
    fnopabeqd $p |- ( ph -> { <. x , y >. | ( x e. A /\ y = B ) }
                          = { <. x , y >. | ( x e. A /\ y = C ) } ) $=
      ( cv wcel wceq wa eqeq2d anbi2d opabbidv ) ABHDIZCHZEJZKOPFJZKBCAQROAEFPG
      LMN $.
  $}

  ${
    $d A x $.  $d C x $.  $d D x $.  $d R x $.
    fvopabf4g.1 $e |- C e. _V $.
    fvopabf4g.2 $e |- ( x = A -> B = C ) $.
    fvopabf4g.3 $e |- F = ( x e. ( R ^m D ) |-> B ) $.
    $( Function value of an operator abstraction whose domain is a set of
       functions with given domain and range.  (Contributed by Jeff Madsen,
       1-Dec-2009.)  (Revised by Mario Carneiro, 12-Sep-2015.) $)
    fvopabf4g $p |- ( ( D e. X /\ R e. Y /\ A : D --> R ) -> ( F ` A ) = C ) $=
      ( wcel wf w3a cmap co cfv wceq wb elmapg ancoms biimp3ar fvmpt syl ) EHMZ
      FIMZEFBNZOBFEPQZMZBGRDSUFUGUJUHUGUFUJUHTFEBIHUAUBUCABCDUIGKLJUDUE $.
  $}

  ${
    $d C x y $.  $d B y $.  $d H x y $.  $d A x y $.
    fnopabco.1 $e |- ( x e. A -> B e. C ) $.
    fnopabco.2 $e |- F = { <. x , y >. | ( x e. A /\ y = B ) } $.
    fnopabco.3 $e |- G = { <. x , y >. | ( x e. A /\ y = ( H ` B ) ) } $.
    $( Composition of a function with a function abstraction.  (Contributed by
       Jeff Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro, 27-Dec-2014.) $)
    fnopabco $p |- ( H Fn C -> G = ( H o. F ) ) $=
      ( cfv cmpt cv wcel wceq wa copab df-mpt eqtr4i wfn ccom adantl a1i biimpi
      dffn5 fveq2 fmptco eqtr4id ) HEUAZGACDHLZMZHFUBGANCOZBNZUKPQABRULKABCUKST
      UJABCEDUNHLZUKFHUMDEOUJIUCFACDMZPUJFUMUNDPQABRUPJABCDSTUDUJHBEUOMPBEHUFUE
      UNDHUGUHUI $.
  $}

  ${
    $d A x y $.  $d B y $.  $d C y $.  $d M x y $.  $d R x y $.  $d S x y $.
    opropabco.1 $e |- ( x e. A -> B e. R ) $.
    opropabco.2 $e |- ( x e. A -> C e. S ) $.
    opropabco.3 $e |- F = { <. x , y >. | ( x e. A /\ y = <. B , C >. ) } $.
    opropabco.4 $e |- G = { <. x , y >. | ( x e. A /\ y = ( B M C ) ) } $.
    $( Composition of an operator with a function abstraction.  (Contributed by
       Jeff Madsen, 11-Jun-2010.) $)
    opropabco $p |- ( M Fn ( R X. S ) -> G = ( M o. F ) ) $=
      ( cop cv wcel wceq wa copab cxp opelxpi syl2anc cfv eqeq2i anbi2i opabbii
      co df-ov eqtri fnopabco ) ABCDEOZFGUAZHIJAPCQZDFQEGQULUMQKLDEFGUBUCMIUNBP
      ZDEJUHZRZSZABTUNUOULJUDZRZSZABTNURVAABUQUTUNUPUSUODEJUIUEUFUGUJUK $.
  $}

  $( Composition with a function and then with the converse.  (Contributed by
     Jeff Madsen, 2-Sep-2009.) $)
  cocnv $p |- ( ( Fun F /\ Fun G ) ->
                              ( ( F o. G ) o. `' G ) = ( F |` ran G ) ) $=
    ( wfun ccom ccnv crn cres coass cid wceq funcocnv2 adantl coeq2d resco wrel
    wa funrel coi1 syl reseq1d adantr eqtr3id eqtrd eqtrid ) ACZBCZPZABDBEZDABU
    HDZDZABFZGZABUHHUGUJAIUKGZDZULUGUIUMAUFUIUMJUEBKLMUGUNAIDZUKGZULAIUKNUEUPUL
    JUFUEUOAUKUEAOUOAJAQARSTUAUBUCUD $.

  $( Cancel a composition by a bijection by preapplying the converse.
     (Contributed by Jeff Madsen, 2-Sep-2009.)  (Proof shortened by Mario
     Carneiro, 27-Dec-2014.) $)
  f1ocan1fv $p |- ( ( Fun F /\ G : A -1-1-onto-> B /\ X e. B ) ->
                            ( ( F o. G ) ` ( `' G ` X ) ) = ( F ` X ) ) $=
    ( wfun wf1o wcel w3a ccnv ccom wf wceq f1of 3ad2ant2 f1ocnv simp3 ffvelcdmd
    cfv syl fvco3 syl2anc f1ocnvfv2 3adant1 fveq2d eqtrd ) CFZABDGZEBHZIZEDJZSZ
    CDKSZULDSZCSZECSUJABDLZULAHUMUOMUHUGUPUIABDNOUJBAEUKUHUGBAUKLZUIUHBAUKGUQAB
    DPBAUKNTOUGUHUIQRABULCDUAUBUJUNECUHUIUNEMUGABEDUCUDUEUF $.

  $( Cancel a composition by the converse of a bijection by preapplying the
     bijection.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
  f1ocan2fv $p |- ( ( Fun F /\ G : A -1-1-onto-> B /\ X e. A ) ->
                            ( ( F o. `' G ) ` ( G ` X ) ) = ( F ` X ) ) $=
    ( wfun wf1o wcel w3a ccnv cfv ccom wceq f1orel dfrel2 sylib 3ad2ant2 fveq1d
    wrel fveq2d f1ocnv f1ocan1fv syl3an2 eqtr3d ) CFZABDGZEAHZIZEDJZJZKZCUILZKZ
    EDKZULKECKZUHUKUNULUHEUJDUFUEUJDMZUGUFDSUPABDNDOPQRTUFUEBAUIGUGUMUOMABDUABA
    CUIEUBUCUD $.

  ${
    $d x f A $.  $d B f $.  $d C f $.
    $( Intersection of Cartesian products over the same base set.  (Contributed
       by Jeff Madsen, 2-Sep-2009.) $)
    inixp $p |- ( X_ x e. A B i^i X_ x e. A C ) = X_ x e. A ( B i^i C ) $=
      ( vf cixp cin cv wfn cfv wcel wral wa an4 anidm r19.26 elin anbi12i elixp
      bicomi ralbii bitr3i bitri vex 3bitr4i ineqri ) EABCFZABDFZABCDGZFZEHZBIZ
      AHUKJZCKZABLZMZULUMDKZABLZMZMZULUMUIKZABLZMZUKUGKZUKUHKZMUKUJKUTULULMZUOU
      RMZMVCULUOULURNVFULVGVBULOVGUNUQMZABLVBUNUQABPVHVAABVAVHUMCDQTUAUBRUCVDUP
      VEUSABCUKEUDZSABDUKVISRABUIUKVISUEUF $.
  $}

  ${
    $d A a b h s u w x $.  $d R a b h s u w x $.  $d S a b h s u w x $.
    $d F a b h s u w x $.  $d B a b h s u w x $.  $d C a b h s u w x $.
    $d X a h s u w x $.  $d P a h s u $.
    upixp.1 $e |- X = X_ b e. A ( C ` b ) $.
    upixp.2 $e |- P = ( w e. A |-> ( x e. X |-> ( x ` w ) ) ) $.
    $( Universal property of the indexed Cartesian product.  (Contributed by
       Jeff Madsen, 2-Sep-2009.)  (Proof shortened by Mario Carneiro,
       12-Sep-2015.) $)
    upixp $p |- ( ( A e. R /\ B e. S /\ A. a e. A
                  ( F ` a ) : B --> ( C ` a ) ) -> E! h ( h : B --> X
                        /\ A. a e. A ( F ` a ) = ( ( P ` a ) o. h ) ) ) $=
      ( vu vs wcel cfv wceq cv wf wral w3a cmpt cvv ccom wa wi wal weu 3ad2ant2
      mptexg cixp ffvelcdm expcom ralimdv impcom 3ad2antl3 fveq2 fveq1d eleq12d
      cbvralvw sylib simpl1 mptelixpg syl mpbird cbvixpv eqtri eleqtrrdi fmpttd
      wb nfv nfra1 nf3an eqid fvex fvmpt3i adantl mpteq2dv adantlr eqidd ixpexg
      rgenw ax-mp eqeltri mptex fveq1 rsp 3ad2ant3 imp feqmptd 3eqtr4rd ralrimi
      fmptco ex simprl simplrr coeq1d eqeq12d rspccva sylan fvco3 adantr 3eqtrd
      eqtrd mpteq2dva wfn eleqtrdi ixpfn dffn5 eqtr4d alrimiv feq1 coeq2 eqeq2d
      ralbidv anbi12d eqeu syl121anc ) CGRZDHRZDLUAZESZYDJSZUBZLCUCZUDZPDQCPUAZ
      QUAZJSZSZUEZUEZUFRZDKYOUBZYFYDFSZYOUGZTZLCUCZDKIUAZUBZYFYRUUBUGZTZLCUCZUH
      ZUUBYOTZUIZIUJUUGIUKYCYBYPYHPDYNHUMULYIPDYNKYIYJDRZUHZYNQCYKESZUNZKUUKYNU
      UMRZYMUULRZQCUCZUUKYJYFSZYERZLCUCZUUPYHYBUUJUUSYCUUJYHUUSUUJYGUURLCYGUUJU
      URDYEYJYFUOUPUQURUSUURUUOLQCYDYKTZUUQYMYEUULUUTYJYFYLYDYKJUTZVAYDYKEUTVBV
      CVDUUKYBUUNUUPVMYBYCYHUUJVEQCYMUULGVFVGVHKMCMUAZESZUNZUUMNMQCUVCUULUVBYKE
      UTVIVJVKZVLYIYTLCYBYCYHLYBLVNYCLVNYGLCVOVPYIYDCRZYTYIUVFUHZPDYDYNSZUEPDUU
      QUEYSYFUVGPDUVHUUQUVFUVHUUQTYIQYDYMUUQCYNYKYDTYJYLYFYKYDJUTVAYNVQYJYLVRVS
      VTWAUVGPADKYNYDAUAZSZUVHYOYRYIUUJYNKRUVFUVEWBUVGYOWCUVFYRAKUVJUEZTYIBYDAK
      BUAZUVISZUEZUVKCFUVLYDTAKUVMUVJUVLYDUVIUTWAOAKUVMKUVDUFNUVCUFRZMCUCUVDUFR
      UVOMCUVBEVRWEMCUVCUFWDWFWGWHZVSVTYDUVIYNWIWPUVGPDYEYFYIUVFYGYHYBUVFYGUIYC
      YGLCWJWKWLWMWNWQWOYIUUIIYIUUGUUHYIUUGUHZUUBPDYJUUBSZUEYOUVQPDKUUBYIUUCUUF
      WRZWMUVQPDYNUVRUVQUUJUHZYNQCYKUVRSZUEZUVRUVTQCYMUWAUVTYKCRZUHZYMYJYKFSZUU
      BUGZSZUVRUWESZUWAUWDYJYLUWFUVTUUFUWCYLUWFTZYIUUCUUFUUJWSUUEUWILYKCUUTYFYL
      UUDUWFUVAUUTYRUWEUUBYDYKFUTWTXAXBXCVAUVTUWGUWHTZUWCUVQUUCUUJUWJUVSDKYJUWE
      UUBXDXCXEUWDUWHUVRAKYKUVISZUEZSZUWAUWDUVRUWEUWLUWCUWEUWLTUVTBYKUVNUWLCFUV
      LYKTAKUVMUWKUVLYKUVIUTWAOUVPVSVTVAUVTUWMUWATZUWCUVTUVRKRZUWNUVQUUCUUJUWOU
      VSDKYJUUBUOXCZAUVRUWKUWAKUWLYKUVIUVRWIUWLVQYKUVIVRVSVGXEXGXFXHUVTUVRCXIZU
      VRUWBTUVTUVRUVDRUWQUVTUVRKUVDUWPNXJMCUVCUVRXKVGQCUVRXLVDXMXHXMWQXNUUGYQUU
      AUHIYOUFUUHUUCYQUUFUUADKUUBYOXOUUHUUEYTLCUUHUUDYSYFUUBYOYRXPXQXRXSXTYA $.
  $}

  ${
    $d A x y $.
    abrexdom.1 $e |- ( y e. A -> E* x ph ) $.
    $( An indexed set is dominated by the indexing set.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    abrexdom $p |- ( A e. V -> { x | E. y e. A ph } ~<_ A ) $=
      ( wcel wrex cab cv wa copab crn cdom wex df-rex abbii wbr cvv wmo cdm wfn
      rnopab eqtr4i wss dmopabss ssexg mpan funopab wi moanimv mpbir mpgbir a1i
      wfun funfn sylib fnrndomg sylc ssdomg mpi domtr syl2anc eqbrtrid ) DEGZAC
      DHZBIZCJDGZAKZCBLZMZDNVGVICOZBIVKVFVLBACDPQVICBUCUDVEVKVJUAZNRZVMDNRZVKDN
      RVEVMSGZVJVMUBZVNVMDUEZVEVPACBDUFZVMDEUGUHVEVJUOZVQVTVEVTVIBTZCVICBUIWAVH
      ABTUJFVHABUKULUMUNVJUPUQVMSVJURUSVEVRVOVSVMDEUTVAVKVMDVBVCVD $.
  $}

  ${
    $d A x y $.  $d B x $.
    $( An indexed set is dominated by the indexing set.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    abrexdom2 $p |- ( A e. V -> { x | E. y e. A x = B } ~<_ A ) $=
      ( cv wceq wmo wcel moeq a1i abrexdom ) AFDGZABCEMAHBFCIADJKL $.
  $}

  ${
    $d A x y z f $.  $d B x y z f $.  $d ph z f $.  $d ps z $.
    ac6gf.1 $e |- F/ y ps $.
    ac6gf.2 $e |- ( y = ( f ` x ) -> ( ph <-> ps ) ) $.
    $( Axiom of Choice.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    ac6gf $p |- ( ( A e. C /\ A. x e. A E. y e. B ph ) ->
                                E. f ( f : A --> B /\ A. x e. A ps ) ) $=
      ( vz wrex wral wcel wsb cv wf wa wex cbvrexsvw ralbii cfv sbhypf sylan2b
      ac6sg imp ) ADFLZCEMEGNZADKOZKFLZCEMZEFHPZQBCEMRHSZUGUJCEADKFTUAUHUKUMUIB
      CKEFHGABDKCPULUBIJUCUEUFUD $.
  $}

  ${
    $d A x y c z w v $.  $d B x y c z w v $.  $d ph c z w v $.
    $( If for every element of an indexing set ` A ` there exists a
       corresponding element of another set ` B ` , then there exists a subset
       of ` B ` consisting only of those elements which are indexed by ` A ` .
       Used to avoid the Axiom of Choice in situations where only the range of
       the choice function is needed.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    indexa $p |- ( ( B e. M /\ A. x e. A E. y e. B ph ) -> E. c
          ( c C_ B /\ A. x e. A E. y e. c ph /\ A. y e. c E. x e. A ph ) ) $=
      ( vz vw vv wcel cv wsbc wrex wral nfv wa sbceq2a nfcv nfsbc1v cvv wss w3a
      crab wex rabexg ssrab2 nfre1 rspcev ancoms anim1ci anasss sbcbidv rexbidv
      a1i wceq elrab sylibr sylancom nfsbcw nfrexw cbvrexfw sylib exp31 rexlimd
      nfrabw ralimia cbvrexw bitrdi simprbi rgen 3jca sseq1 nfeq2 rexeqf ralbid
      raleqf 3anbi123d spcegv imp syl2an ) EFKACHLZMZBILZMZIDNZHEUDZUAKZWGEUBZA
      CWGNZBDOZABDNZCWGOZUCZGLZEUBZACWONZBDOZWLCWOOZUCZGUEZACENZBDOZWFHEFUFXCWI
      WKWMWIXCWFHEUGUOXBWJBDBLZDKZAWJCEXECPACWGUHXECLZEKZAWJXEXGQZAQZACJLZMZJWG
      NZWJXHAXFWGKZXLXIXGABWDMZIDNZQZXMAXHXPAXEXGXPAXEQXOXGXEAXOXNAIXDDABWDRZUI
      UJUKULUJWFXOHXFEWBXFUPZWEXNIDXRWCABWDACWBRUMUNZUQURXKAJXFWGACXJRZUIUSXKAJ
      CWGJWGSWFCHEWECIDCDSWCCBWDCWDSACWBTUTVACESVFZACXJTAJPXTVBVCVDVEVGWMXCWLCW
      GXMXGWLWFWLHXFEXRWFXOWLXSXNAIBDABWDTAIPXQVHVIUQVJVKUOVLWHWNXAWTWNGWGUAWOW
      GUPZWPWIWRWKWSWMWOWGEVMYBWQWJBDBWOWGWFBHEWEBIDBDSWCBWDTVABESVFVNACWOWGCWO
      SZYAVOVPWLCWOWGYCYAVQVRVSVTWA $.
  $}

  ${
    $d A c f x y $.  $d B c f x y $.  $d ph f c $.
    $( If for every element of an indexing set ` A ` there exists a
       corresponding element of another set ` B ` , then there exists a subset
       of ` B ` consisting only of those elements which are indexed by ` A ` ,
       and which is dominated by the set ` A ` .  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    indexdom $p |- ( ( A e. M /\ A. x e. A E. y e. B ph ) ->
            E. c ( ( c ~<_ A /\ c C_ B ) /\ ( A. x e. A E. y e. c ph
                                        /\ A. y e. c E. x e. A ph ) ) ) $=
      ( vf wcel wrex wral wa cv wex cdom wbr wss cvv adantr anbi12d wf cfv wsbc
      nfsbc1v sbceq1a ac6gf crn wfn cdm fdm vex dmex eqeltrrdi ffn fnrndomg frn
      sylc nfv nfra1 nfan wfun ffun eleq2d biimpar syl2anc adantlr rspa adantll
      fvelrn rspesbca ex ralrimi nfcv nfralw wceq fvelrnb syl rsp adantl eqcoms
      wb wi biimprcd syl6 reximdai sylbid breq1 sseq1 rexeq ralbidv raleq spcev
      rnex syl22anc exlimiv ) DFIACEJBDKLDEHMZUAZACBMZWPUBZUCZBDKZLZHNGMZDOPZXC
      EQZLZACXCJZBDKZABDJZCXCKZLZLZGNZAWTBCDEFHACWSUDZACWSUEZUFXBXMHXBWPUGZDOPZ
      XPEQZACXPJZBDKZXICXPKZXMWQXQXAWQDRIWPDUHZXQWQDWPUIZRDEWPUJZWPHUKZULUMDEWP
      UNZDRWPUOUQSWQXRXADEWPUPSXBXSBDWQXABWQBURWTBDUSUTZXBWRDIZXSXBYHLWSXPIZWTX
      SWQYHYIXAWQYHLWPVAZWRYCIZYIWQYJYHDEWPVBSWQYKYHWQYCDWRYDVCVDWRWPVIVEVFXAYH
      WTWQWTBDVGVHACWSXPVJVEVKVLXBXICXPWQXACWQCURWTCBDCDVMXNVNUTXBCMZXPIZWSYLVO
      ZBDJZXIWQYMYOWAZXAWQYBYPYFBDYLWPVPVQSXBYNABDYGXBYHWTYNAWBXAYHWTWBWQWTBDVR
      VSYNAWTAWTWAYLWSXOVTWCWDWEWFVLXLXQXRLZXTYALZLGXPWPYEWMXCXPVOZXFYQXKYRYSXD
      XQXEXRXCXPDOWGXCXPEWHTYSXHXTXJYAYSXGXSBDACXCXPWIWJXICXCXPWKTTWLWNWOVQ $.
  $}

  ${
    $d R x y z $.  $d A x y z $.  $d B x y z $.  $d C x y $.
    $( A subset of a well-founded set has an infimum.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    frinfm $p |- ( ( R Fr A /\ ( B e. C /\ B C_ A /\ B =/= (/) ) ) ->
                    E. x e. A ( A. y e. B -. x `' R y /\
                    A. y e. A ( y `' R x -> E. z e. B y `' R z ) ) ) $=
      ( wfr wcel wss c0 wa cv wbr wn wral wrex wi vex ex wne w3a ccnv fri exp43
      ancom1s 3imp2 ssel2 adantrr brcnv biimpi ralimi ad2antll rspcev ralrimivw
      con3i breq2 ad2antrl jca32 reximdv2 adantl 3ad2antr2 mpd ) DGHZEFIZEDJZEK
      UAZUBLBMZAMZGNZOZBEPZAEQZVIVHGUCZNZOZBEPZVHVIVNNZVHCMZVNNZCEQZRZBDPZLZADQ
      ZVDVEVFVGVMVDVEVFVGVMVEVDVFVGLVMABDEFGUDUFUEUGVDVEVFVMWERZVGVFWFVDVFVLWDA
      EDVFVIEIZVLLZVIDIZWDLVFWHLWIVQWCVFWGWIVLEDVIUHUIVLVQVFWGVKVPBEVOVJVOVJVIV
      HGASBSUJUKUPULUMWGWCVFVLWGWBBDWGVRWAVTVRCVIEVSVIVHVNUQUNTUOURUSTUTVAVBVC
      $.
  $}

  ${
    $d A x y z $.  $d B x y z $.  $d C x y z $.  $d R x y z $.
    $( A nonempty subset of a well-ordered set has a lower bound.  (Contributed
       by Jeff Madsen, 2-Sep-2009.) $)
    welb $p |- ( ( R We A /\ ( B e. C /\ B C_ A /\ B =/= (/) ) ) ->
              ( `' R Or B /\ E. x e. B ( A. y e. B -. x `' R y /\
                        A. y e. B ( y `' R x -> E. z e. B y `' R z ) ) ) ) $=
      ( wwe wcel wss c0 w3a wa wor cv wbr wral wrex syl 3ad2antr2 wne ccnv wess
      wn wi impcom weso cnvso sylib wfr ssidd 3anim2i adantl frinfm syl2anc jca
      wefr ) DGHZEFIZEDJZEKUAZLZMZEGUBZNZAOZBOZVDPUDBEQVGVFVDPVGCOVDPCERUEBEQMA
      ERZURUSUTVEVAURUTMZEGNZVEVIEGHZVJUTURVKEDGUCUFZEGUGSEGUHUITVCEGUJZUSEEJZV
      ALZVHURUSUTVMVAVIVKVMVLEGUQSTVBVOURUTVNUSVAUTEUKULUMABCEEFGUNUOUP $.
  $}

  ${
    $d A x y z $.  $d B x y z $.  $d C x y z $.  $d R x y z $.
    $( Existence of supremum.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    supex2g $p |- ( A e. C -> sup ( B , A , R ) e. _V ) $=
      ( vx vy vz wcel csup cv wbr wn wral wrex wi wa crab cuni cvv df-sup
      rabexg uniexd eqeltrid ) ACHZBADIEJZFJZDKLFBMUFUEDKUFGJDKGBNOFAMPZEAQZRSE
      FGBADTUDUHSUGEACUAUBUC $.
  $}

  ${
    $d A x y z $.  $d B x y z $.  $d R x y z $.
    $( Closure of supremum.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    supclt $p |- ( ( R Or A /\ E. x e. A ( A. y e. B -. x R y /\ A. y e. A
            ( y R x -> E. z e. B y R z ) ) ) -> sup ( B , A , R ) e. A ) $=
      ( wor cv wbr wn wral wrex wi wa simpl simpr supcl ) DFGZAHZBHZFIJBEKTSFIT
      CHFICELMBDKNADLZNABCDEFRUAORUAPQ $.
  $}

  ${
    $d A x y z $.  $d B x y z $.  $d C x y z $.  $d R x y z $.
    $( Upper bound property of supremum.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    supubt $p |- ( ( R Or A /\ E. x e. A ( A. y e. B -. x R y /\
                        A. y e. A ( y R x -> E. z e. B y R z ) ) ) ->
                                ( C e. B -> -. sup ( B , A , R ) R C ) ) $=
      ( wor cv wbr wn wral wrex wi wa simpl simpr supub ) DGHZAIZBIZGJKBELUATGJ
      UACIGJCEMNBDLOADMZOABCDEFGSUBPSUBQR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Real and complex numbers; integers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A u v w x y z $.  $d B u v w x y z $.  $d ph u v w y $.
    $( Combine a finite set of lower bounds.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    filbcmb $p |- ( ( A e. Fin /\ A =/= (/) /\ B C_ RR ) ->
                      ( A. x e. A E. y e. B A. z e. B ( y <_ z -> ph )
                    -> E. y e. B A. z e. B ( y <_ z -> A. x e. A ph ) ) ) $=
      ( vw vu vv cfn wcel cr cv cle wi wral wrex wa ssel2 adantlr wne reex ssex
      c0 wss w3a wbr cvv indexfi 3expia sylan2 3adant2 rexn0 rexlimivw 3ad2ant2
      r19.2z syl ex ad2antrr sstr ancoms fimaxre sylan anasss ancom2s 3ad2antl3
      anassrs syld a1dd 3impd nfv nfcv nfre1 nfralw nfan nfra1 nfrexw weq breq1
      imbi1d ralbidv cbvrexvw rsp adantrr ad2ant2r adantr rspccva adantll letrd
      simplrr pm2.27 ad2antlr mpid syl5 rexlimdva biimtrid ralimdva an32s exp32
      imp ralrimi reximdai ssrexv exp43 3ad2ant3 mpdd ) EJKZEUDUAZFLUEZUFZCMZDM
      ZNUGZAOZDFPZCFQBEPZGMZFUEZXOCXQQZBEPZXOBEQCXQPZUFZGJQZXMABEPZOZDFPZCFQZXG
      XIXPYCOZXHXIXGFUHKZYHFLUBUCXGYIXPYCXOBCEFUHGUIUJUKULXJYBYGGJXJXQJKZRZYBHM
      ZXKNUGZHXQPZCXQQZYGYKXRXTYAYOYKXRXTYAYOOOYKXRRZXTYOYAYPXTXQUDUAZYOXJXTYQO
      ZYJXRXHXGYRXIXHXTYQXHXTRXSBEQYQXSBEUPXSYQBEXOCXQUMUNUQURUOUSXJYJXRYQYOOZX
      IXGYJXRRYSXHXIXRYJYSXIXRYJYSXIXRRZXQLUEZYJYSXRXIUUAXQFLUTVAUUAYJYQYOCHXQV
      BUJVCVDVEVFVGVHVIURVJXJYBYOYGOZOZYJXIXGUUCXHXIXRXTYAUUBXIXRXTYAUUBYTXTYAR
      ZRYOYFCXQQZYGYTXTYOUUEOYAYTXTRZYNYFCXQYTXTCYTCVKXSCBECEVLXOCXQVMVNVOUUFXK
      XQKZYNYFUUFUUGYNRZRYEDFUUFUUHDYTXTDYTDVKXSDBEDEVLXODCXQDXQVLXNDFVPVQVNVOU
      UHDVKVOYTUUHXTXLFKZYEOYTUUHRZXTRUUIXMYDUUJUUIXMRZXTYDUUJUUKRZXTYDUULXSABE
      XSIMZXLNUGZAOZDFPZIXQQUULBMEKZRZAXOUUPCIXQCIVRZXNUUODFUUSXMUUNAXKUUMXLNVS
      VTWAWBUURUUPAIXQUULUUMXQKZUUPAOUUQUUPUUIUUOOZUULUUTRZAUUODFWCUVBUVAUUNAUV
      BUUMXKXLUUJUUTUUMLKZUUKYTUUTUVCUUHXIXRUUTUVCXRUUTRXIUUMFKUVCXQFUUMSFLUUMS
      UKVGTTUUJXKLKZUUKUUTYTUUGUVDYNXIXRUUGUVDXRUUGRXIXKFKUVDXQFXKSFLXKSUKVGWDU
      SUULXLLKZUUTYTUUIUVEUUHXMXIUUIUVEXRFLXLSTWEWFUUJUUTUUMXKNUGZUUKUUHUUTUVFY
      TYNUUTUVFUUGYMUVFHUUMXQYLUUMXKNVSWGWHWHTUUJUUIXMUUTWJWIUUKUVAUUOOZUUJUUTU
      UIUVGXMUUIUUOWKWFWLWMWNTWOWPWQWTWRWSWRXAWSXBWDXRUUEYGOXIUUDYFCXQFXCWLVHXD
      VJXEWFXFWOVH $.
  $}

  $( Membership of a product in a finite interval of integers.  (Contributed by
     Jeff Madsen, 17-Jun-2010.) $)
  fzmul $p |- ( ( M e. ZZ /\ N e. ZZ /\ K e. NN ) -> ( J e. ( M ... N ) ->
                        ( K x. J ) e. ( ( K x. M ) ... ( K x. N ) ) ) ) $=
    ( cz wcel w3a cfz co cle wbr cmul wb wi wa cr zre 3expa zmulcl ex elfz1 cc0
    cn 3adant3 clt nnre nngt0 jca lemul2 syl3an biimpd adantllr ancom1s anim12d
    adantlll 3anim123d elfz 3coml nnz syl11 imp sylibrd an32s exp4b 3impd 3impa
    syl6 sylbid ) CEFZDEFZBUCFZGACDHIFZAEFZCAJKZADJKZGZBALIZBCLIZBDLIZHIFZVIVJV
    LVPMVKACDUAUDVIVJVKVPVTNVIVJOZVKOZVMVNVOVTWBVMVNVOVTWAVMVKVNVOOZVTNWAVMOZVK
    OZWCVRVQJKZVQVSJKZOZVTWEVNWFVOWGVIVMVKVNWFNVJVIVMOVKOVNWFVIVMVKVNWFMZVICPFV
    MAPFZVKBPFZUBBUEKZOZWICQAQZVKWKWLBUFBUGUHZCABUIUJRUKULVJVMVKVOWGNVIVJVMOVKO
    VOWGVMVJVKVOWGMZVMVJVKWPVMWJVJDPFVKWMWPWNDQWOADBUIUJRUMUKUOUNWDVKVTWHMZVIVJ
    VMVKWQNBEFZVIVJVMGZWQVKWRWSVREFZVSEFZVQEFZGWQWRVIWTVJXAVMXBWRVIWTBCSTWRVJXA
    BDSTWRVMXBBASTUPXBWTXAWQVQVRVSUQURVGBUSUTRVAVBVCVDVEVFVH $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Sequences and sums
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d f g h j k n w x y A $.  $d h j k m w x J $.  $d f g h j k m n w x y M $.
    $d g j ch $.  $d j m n w x F $.  $d f h j k x y ps $.  $d f g j n x y si $.
    $d f g h j k m n w x G $.  $d j n w x y ph $.  $d n w x y th $.  $d h V $.
    $d h j k n w x y ta $.  $d f g h j k m n w x y Z $.
    sdc.1 $e |- Z = ( ZZ>= ` M ) $.
    sdc.2 $e |- ( g = ( f |` ( M ... n ) ) -> ( ps <-> ch ) ) $.
    sdc.3 $e |- ( n = M -> ( ps <-> ta ) ) $.
    sdc.4 $e |- ( n = k -> ( ps <-> th ) ) $.
    sdc.5 $e |- ( ( g = h /\ n = ( k + 1 ) ) -> ( ps <-> si ) ) $.
    sdc.6 $e |- ( ph -> A e. V ) $.
    sdc.7 $e |- ( ph -> M e. ZZ ) $.
    sdc.8 $e |- ( ph -> E. g ( g : { M } --> A /\ ta ) ) $.
    sdc.9 $e |- ( ( ph /\ k e. Z ) -> ( ( g : ( M ... k ) --> A /\ th ) ->
                  E. h ( h : ( M ... ( k + 1 ) ) --> A /\
                         g = ( h |` ( M ... k ) ) /\ si ) ) ) $.
    ${
      sdc.10 $e |- J = { g | E. n e. Z ( g : ( M ... n ) --> A /\ ps ) } $.
      sdc.11 $e |- F = ( w e. Z , x e. J |-> { h | E. k e. Z
     ( h : ( M ... ( k + 1 ) ) --> A /\ x = ( h |` ( M ... k ) ) /\ si ) } ) $.
      ${
        sdc.12 $e |- F/ k ph $.
        sdc.13 $e |- ( ph -> G : Z --> J ) $.
        sdc.14 $e |- ( ph -> ( G ` M ) : ( M ... M ) --> A ) $.
        sdc.15 $e |- ( ( ph /\ w e. Z ) ->
                       ( G ` ( w + 1 ) ) e. ( w F ( G ` w ) ) ) $.
        $( Lemma for ~ sdc .  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
        sdclem2 $p |- ( ph -> E. f ( f : Z --> A /\ A. n e. Z ch ) ) $=
          ( vm cv cfv cmpt wf cfz wsbc wral wex wcel wrex ffvelcdmda cab eleq2i
          co wa nfcv nfsbc1v nfan nfrexw fvex wceq feq1 sbceq1a anbi12d rexbidv
          nfv elabf bitri sylib weq cdm fdm adantr wi caddc fveq2 oveq2 mpteq1d
          cuz c1 eqeq12d imbi2d cz id fveq12d eqid fvmpt adantl elfz1eq ralrimi
          fveq1d ex wfn fnmpti sylancl a1i cres w3a cvv simpr wss cmap ovex syl
          ssexg sylancr eqeq1 reseq1 eqeq2d fzssp1 eleqtrdi fzopth simprd ax-mp
          wb resmpt fvres eluzfz2 syl5ibrcom sylbid mpd eqtrdi bitrd sbcbidv wo
          fveq2d eqtr2d ffnd eqfnfv mpbird 3simpa reximi ss2abi fvexi imbitrrid
          simpl elmapg mpan2 abssdv a1d abrexex2g 3anbi2d abbidv eleq1d imbi12d
          ovmpt4g 3com12 3exp vtoclga eqsstrdi sseldd elab simprl fssres simprr
          syl3c fneq1d mpbiri fndmd eqtr3d simplr oveq1d oveq2d reseq2d eqtr2di
          fdmd mpbid elfzp1 eqtrd syl5ibcom eqeltrrd peano2uz 4syl ralrimiv ffn
          eqcomd jaod ad2antrl eqfnfv2 mpbir2and expr imbi1d expimpd expcom a2d
          rexlimd sylbir uzind4 eleq2s impcom dmeqd dmmptg mprg eqeq1d biimtrdi
          syl5 equcoms biimpcd sylcom rexlimdvw simpld ffvelcdmd cbvmptv fmptdf
          feq2d sbceq1dd mpteq1 dfsbcq cbvralvw sylibr mptex resex sbcie fzssuz
          3syl vex sseqtrri sbceq1d bitr3id ralbidv spcev syl2anc ) ATIUPTUPUQZ
          UYSPURZURZUSZUTZBKUPRNUQZVAVJZVUAUSZVBZNTVCZTIJUQZUTZCNTVCZVKZJVDAMTM
          UQZVUMPURZURZIVUBULAVUMTVEZVKZRVUMVAVJZIVUMVUNVUQVURIVUNUTZDKVUNVBZVU
          QVUEIVUNUTZBKVUNVBZVKZNTVFZVUSVUTVKZVUQVUNQVEZVVDATQVUMPUMVGVVFVUNVUE
          IKUQZUTZBVKZNTVFZKVHZVEVVDQVVKVUNUJVIVVJVVDKVUNVVCKNTKTVLVVAVVBKVVAKW
          BBKVUNVMVNVOVUMPVPVVGVUNVQZVVIVVCNTVVLVVHVVABVVBVUEIVVGVUNVRBKVUNVSVT
          WAWCWDWEVUQVVCVVENTVUQVVCMNWFZVVEVVCVUNWGZVUEVQZVUQVVMVVAVVOVVBVUEIVU
          NWHWIVUQVVORRVQZVVMVKZVVMVUQVVOVURVUEVQZVVQVUQVVNVURVUEVUQVVNUPVURVUA
          USZWGZVURVUQVUNVVSVUPAVUNVVSVQZAVWAWJZVUMRWOURZTAGUQZPURZUPRVWDVAVJZV
          UAUSZVQZWJARPURZUPRRVAVJZVUAUSZVQZWJZAHUQZPURZUPRVWNVAVJZVUAUSZVQZWJA
          VWNWPWKVJZPURZUPRVWSVAVJZVUAUSZVQZWJVWBGHRVUMVWDRVQZVWHVWLAVXDVWEVWIV
          WGVWKVWDRPWLVXDUPVWFVWJVUAVWDRRVAWMWNWQWRGHWFZVWHVWRAVXEVWEVWOVWGVWQV
          WDVWNPWLVXEUPVWFVWPVUAVWDVWNRVAWMWNWQWRVWDVWSVQZVWHVXCAVXFVWEVWTVWGVX
          BVWDVWSPWLVXFUPVWFVXAVUAVWDVWSRVAWMWNWQWRGMWFZVWHVWAAVXGVWEVUNVWGVVSV
          WDVUMPWLVXGUPVWFVURVUAVWDVUMRVAWMWNWQWRVWMRWSVEAVWLVUMVWIURZVUMVWKURZ
          VQZMVWJVCZAVXJMVWJULAVUMVWJVEZVXJAVXLVKZVXIVUOVXHVXLVXIVUOVQAUPVUMVUA
          VUOVWJVWKUPMWFZUYSVUMUYTVUNUYSVUMPWLVXNWTXAZVWKXBZVUMVUNVPXCXDVXMVUMV
          UNVWIVXMVUMRPVXLVUMRVQAVUMRXEXDUUBXGUUCXHXFAVWIVWJXIVWKVWJXIVWLVXKYKA
          VWJIVWIUNUUDUPVWJVUAVWKUYSUYTVPZVXPXJMVWJVWIVWKUUEXKUUFXLVWNVWCVEZAVW
          RVXCVXRVWNTVEZAVWRVXCWJZWJTVWCVWNUAVIAVXSVXTAVXSVKZRVUMWPWKVJZVAVJZIV
          WTUTZVWOVWTVURXMZVQZVKZMTVFZVXTVYAVWTVYCILUQZUTZVWOVYIVURXMZVQZVKZMTV
          FZLVHZVEVYHVYAVWNVWOOVJZVYOVWTVYAVYPVYJVYLFXNZMTVFZLVHZVYOVYAVWOQVEVX
          SVYSXOVEZVYPVYSVQZATQVWNPUMVGAVXSXPVYAVYSVYOXQVYOXOVEZVYTVYRVYNLVYQVY
          MMTVYJVYLFUUGUUHUUIZVYATXOVEVYMLVHZXOVEZMTVCWUBTRWOUAUUJZVYAWUEMTAVXS
          MULVXSMWBVNZVYAWUEVUPVYAWUDIVYCXRVJZXQZWUHXOVEWUEVYAISVEZWUIAWUJVXSUF
          WIWUJVYMLWUHVYMVYIWUHVEZWUJVYJVYJVYLUULWUJVYCXOVEWUKVYJYKRVYBVAXSIVYC
          VYISXOUUMUUNUUKUUOXTIVYCXRXSWUDWUHXOYAXKUUPXFVYMMLTXOXOUUQYBVYSVYOXOY
          AYBVXSVYJVWDVYKVQZFXNZMTVFZLVHZXOVEZVWNVWDOVJZWUOVQZWJZWJVXSVYTWUAWJZ
          WJGVWOQVWDVWOVQZWUSWUTVXSWVAWUPVYTWURWUAWVAWUOVYSXOWVAWUNVYRLWVAWUMVY
          QMTWVAWULVYLVYJFVWDVWOVYKYCUURWAUUSZUUTWVAWUQVYPWUOVYSVWDVWOVWNOWMWVB
          WQUVAWRVWDQVEZVXSWUPWURVXSWVCWUPWURHGTQWUOOXOUKUVBUVCUVDUVEUVLWUCUVFU
          OUVGVYNVYHLVWTVWSPVPVYIVWTVQZVYMVYGMTWVDVYJVYDVYLVYFVYCIVYIVWTVRWVDVY
          KVYEVWOVYIVWTVURYDYEVTWAUVHWEVYAVYGVXTMTWUGVXTMWBVYAVUPVYGVXTWJVYAVUP
          VKZVYDVYFVXTWVEVYDVKVXTVYFVYEVWQVQZVXCWJWVEVYDWVFVXCWVEVYDWVFVKZVKZVX
          CVYCVXAVQZVWDVWTURZVWDVXBURZVQZGVYCVCZWVHVYBVWSRVAWVHVUMVWNWPWKWVHVVP
          MHWFZWVHVURVWPVQZVVPWVNVKZWVHVYEWGVURVWPWVHVURIVYEWVHVYDVURVYCXQVURIV
          YEUTWVEVYDWVFUVIRVUMYFVYCIVURVWTUVJXKUWBWVHVWPVYEWVHVYEVWPXIVWQVWPXIU
          PVWPVUAVWQVXQVWQXBXJWVHVWPVYEVWQWVEVYDWVFUVKZUVMUVNUVOUVPZWVHVUMVWCVE
          ZWVOWVPYKWVHVUMTVWCVYAVUPWVGUVQUAYGZRVWNRVUMYHXTUWCYIZUVRZUVSWVHWVLGV
          YCWVHVWDVYCVEZVWDVURVEZVWDVYBVQZUUAZWVLWVHWVSWWCWWFYKWVTVWDRVUMUWDXTW
          VHWWDWVLWWEWVHVWDVYEURZVWDVXBVURXMZURZVQWWDWVLWVHVWDVYEWWHWVHVYEVWQWW
          HWVQWVHWWHVXBVWPXMZVWQWVHVURVWPVXBWVRUVTVWPVXAXQWWJVWQVQRVWNYFUPVXAVW
          PVUAYLYJUWAUWEXGWWDWWGWVJWWIWVKVWDVURVWTYMVWDVURVXBYMWQUWFWVHWWEVXFWV
          LWVHVYBVWSVWDWWBYEWVHWVLVXFVWSVWTURZVWSVXBURZVQWVHWWLWWKWVHVXRVWSVWCV
          EVWSVXAVEWWLWWKVQWVHVUMVWNVWCWWAWVTUWGRVWNUWHRVWSYNUPVWSVUAWWKVXAVXBU
          YSVWSVQZUYSVWSUYTVWTUYSVWSPWLWWMWTXAVXBXBZVWSVWTVPXCUWIUWLVXFWVJWWKWV
          KWWLVWDVWSVWTWLVWDVWSVXBWLWQYOYPUWMYPUWJWVHVWTVYCXIZVXBVXAXIVXCWVIWVM
          VKYKVYDWWOWVEWVFVYCIVWTUWKUWNUPVXAVUAVXBVXQWWNXJGVYCVXAVWTVXBUWOXKUWP
          UWQVYFVWRWVFVXCVWOVYEVWQYCUWRYOUWSXHUXBYQUWTUXCUXAUXDUAUXEUXFZUXGVUAX
          OVEZVVTVURVQUPVURUPVURVUAXOUXHWWQUYSVURVEVXQXLUXIYRUXJVUQWVSVVRVVQYKV
          UQVUMTVWCAVUPXPUAYGZRVUDRVUMYHXTYSVVPVVMXPUXKUXLVVMVVCVVEVVCVVEYKNMNM
          WFZVVAVUSVVBVUTWWSVUEVURIVUNVUDVUMRVAWMZUYAWWSBDKVUNUDYTVTUXMUXNUXOUX
          PYQZUXQVUQWVSVUMVURVEWWRRVUMYNXTUXRUPMTVUAVUOVXOUXSUXTADKVVSVBZMTVCVU
          HAWXBMTULAVUPWXBVUQDKVUNVVSWWPVUQVUSVUTWXAYIUYBXHXFVUGWXBNMTWWSVUGBKV
          VSVBZWXBWWSVUEVURVQVUFVVSVQVUGWXCYKWWTUPVUEVURVUAUYCBKVUFVVSUYDUYKWWS
          BDKVVSUDYTYSUYEUYFVULVUCVUHVKJVUBUPTVUAWUFUYGVUIVUBVQZVUJVUCVUKVUHTIV
          UIVUBVRWXDCVUGNTCBKVUIVUEXMZVBWXDVUGBCKWXEVUIVUEJUYLUYHUBUYIWXDBKWXEV
          UFWXDWXEVUBVUEXMZVUFVUIVUBVUEYDVUETXQWXFVUFVQVUEVWCTRVUDUYJUAUYMUPTVU
          EVUAYLYJYRUYNUYOUYPVTUYQUYR $.
      $}

      $d g h k ph $.
      $( Lemma for ~ sdc .  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
      sdclem1 $p |- ( ph -> E. f ( f : Z --> A /\ A. n e. Z ch ) ) $=
        ( vj vm csn cv wf wa wral wex cz wcel cc0 cif cuz cfv wceq c1 caddc w3a
        co cvv cxp cpw c0 cdif cfz wrex cab fvexi cmap wss simpl wb ovex elmapg
        sylancl imbitrrid abssdv ssexg ralrimivw abrexex2g eqeltrid adantr uzid
        sylancr syl eleqtrrdi simprl feq2d mpbird simprr oveq2 anbi12d syl12anc
        fzsn rspcev eqabri sylibr cres wne peano2uzs ad2antlr simpr1 simpr3 vex
        wsbc weq wi a1i sbc2iedv ad2antrr nfv nfcv nfsbc1v nfan sbceq1a sbcbidv
        nfsbcw rspce eleq2i nfrexw feq1 rexbidv sylib iftrued fveq2d sylan nfab
        eqtr4di nfre1 nfcxfr elabf rexlimdva2 elpw2g cbvrexvw reximdva imbitrdi
        bitri rexcom4 biimtrid ss2abdv eqsstrid sselda 3anbi2d exbidv elab abn0
        eqeq1 adantlr eldifsn sylanbrc adantrl ralrimivva xpeq1d biimpar syldan
        fmpo elimel eqid axdc4uz syl3anc abbii eqtri feq3 ax-mp bitrdi fveqeq2d
        raleqdv 3anbi123d simpll nff cmpo nfmpo nfov nfel2 nfralw simpr2 feq12d
        0z nf3an fvoveq1 id fveq2 oveq12d eleq12d rspccva sdclem2 ex sylbid mpd
        exlimdv exlimddv ) AQUMZIKUNZUOZEUPZSIJUNUOCNSUQUPJURZKUGAUXEUPZQUSUTZQ
        VAVBZVCVDZPUKUNZUOZUXIUXKVDUXCVEZULUNZVFVGVIUXKVDZUXNUXNUXKVDZOVIZUTZUL
        UXJUQZVHZUKURZUXFUXGPVJUTZUXCPUTZUXJPVKZPVLZVMUMVNZOUOZUYAAUYBUXEAPQNUN
        ZVOVIZIUXCUOZBUPZNSVPZKVQZVJUIASVJUTUYKKVQZVJUTZNSUQUYMVJUTSQVCTVRAUYON
        SAUYNIUYIVSVIZVTUYPVJUTUYOAUYKKUYPUYKUXCUYPUTZAUYJUYJBWAAIRUTZUYIVJUTUY
        QUYJWBUEQUYHVOWCIUYIUXCRVJWDWEWFWGIUYIVSWCUYNUYPVJWHWEWIUYKNKSVJVJWJWNW
        KZWLUXGUYLUYCUXGQSUTQQVOVIZIUXCUOZEUYLUXGQQVCVDZSUXGUXHQVUBUTAUXHUXEUFW
        LZQWMWOTWPUXGVUAUXDAUXDEWQZUXGUYTUXBIUXCUXGUXHUYTUXBVEZVUCQXDZWOWRWSAUX
        DEWTUYKVUAEUPNQSUYHQVEZUYJVUABEVUGUYIUYTIUXCUYHQQVOXAWRUBXBXEXCUYLKPUIX
        FXGAUXESPVKZUYFOUOZUYGUXGQMUNZVFVGVIZVOVIZILUNZUOZGUNZVUMQVUJVOVIZXHZVE
        ZFVHZMSVPZLVQZUYFUTZGPUQHSUQVUIUXGVVBHGSPUXGVUOPUTZVVBHUNZSUTZUXGVVCUPZ
        VVAUYEUTZVVAVMXIZVVBVVFVVGVVAPVTZAVVIUXEVVCAVUTLPAVUSVUMPUTZMSAVUJSUTZU
        PZVUSUPZUYIIVUMUOZBKVUMXOZUPZNSVPZVVJVVMVUKSUTZVUNBNVUKXOZKVUMXOZVVQVVK
        VVRAVUSQVUJSTXJXKVVLVUNVURFXLVVMVVTFVVLVUNVURFXMAVVTFWBVVKVUSABFKNVUMVU
        KLXNZVUJVFVGWCKLXPZUYHVUKVEZUPBFWBXQAUDXRXSXTWSVVPVUNVVTUPNVUKSVUNVVTNV
        UNNYAVVSNKVUMNVUMYBBNVUKYCYGYDVWCVVNVUNVVOVVTVWCUYIVULIVUMUYHVUKQVOXAWR
        VWCBVVSKVUMBNVUKYEYFXBYHXCVVJVUMUYMUTVVQPUYMVUMUIYIUYLVVQKVUMVVPKNSKSYB
        VVNVVOKVVNKYABKVUMYCYDYJVWAVWBUYKVVPNSVWBUYJVVNBVVOUYIIUXCVUMYKBKVUMYEX
        BYLUUAUUGXGUUBWGXTVVFUYBVVGVVIWBAUYBUXEVVCUYSXTVVAPVJUUCWOWSAVVCVVHUXEA
        VVCUPZVUTLURZVVHVWDVUOVUNUXCVUQVEZFVHZMSVPZLURZKVQZUTVWEAPVWJVUOAPUYMVW
        JUIAUYLVWIKUYLVUPIUXCUOZDUPZMSVPZAVWIUYKVWLNMSNMXPZUYJVWKBDVWNUYIVUPIUX
        CUYHVUJQVOXAWRUCXBUUDZAVWMVWGLURZMSVPVWIAVWLVWPMSUHUUEVWGMLSUUHUUFUUIUU
        JUUKUULVWIVWEKVUOGXNKGXPZVWHVUTLVWQVWGVUSMSVWQVWFVURVUNFUXCVUOVUQUUQUUM
        YLUUNUUOYMVUTLUUPXGUURVVAUYEVMUUSUUTUVAUVBHGSPVVAUYFOUJUVFYMAUYGVUIAUYD
        VUHUYFOAUXJSPAUXJVUBSAUXIQVCAUXHQVAUFYNYOTYRUVCWRUVDUVEPUXCUKULOUXIVJUX
        JQVAUSUWHUVGUXJUVHUVIUVJUXGUXTUXFUKUXGUXTSVWMKVQZUXKUOZQUXKVDZUXCVEZUXR
        ULSUQZVHZUXFUXGUXLVWSUXMVXAUXSVXBUXGUXLSPUXKUOZVWSUXGUXJSPUXKUXGUXJVUBS
        UXGUXIQVCUXGUXHQVAVUCYNZYOTYRZWRPVWRVEVXDVWSWBPUYMVWRUIUYLVWMKVWOUVKUVL
        ZPVWRSUXKUVMUVNZUVOUXGUXIQUXCUXKVXEUVPUXGUXRULUXJSVXFUVQUVRUXGVXCUXFUXG
        VXCUPZBCDEFGHIJKLMNOUXKPQRSTUAUBUCUDAUYRUXEVXCUEXTAUXHUXEVXCUFXTZAUXEKU
        RUXEVXCUGXTVXIAVVKVWLVWPXQAUXEVXCUVSUHYPUIUJUXGVXCMUXGMYAVWSVXAVXBMMSVW
        RUXKMUXKYBMSYBZVWMMKVWLMSYSYQZUVTVXAMYAUXRMULSVXKMUXOUXQMUXNUXPOMUXNYBM
        OHGSPVVAUWAUJHGMSPVVAVXKMPVWRVXGVXLYTVUTMLVUSMSYSYQUWBYTMUXPYBUWCUWDUWE
        UWIYDVXIVWSVXDUXGVWSVXAVXBXLVXHXGVXIUYTIVWTUOUXDUXGUXDVXCVUDWLVXIUYTUXB
        IVWTUXCUXGVWSVXAVXBUWFVXIUXHVUEVXJVUFWOUWGWSVXIVXBVVEVVDVFVGVIUXKVDZVVD
        VVDUXKVDZOVIZUTZUXGVWSVXAVXBXMUXRVXPULVVDSULHXPZUXOVXMUXQVXOUXNVVDVFUXK
        VGUWJVXQUXNVVDUXPVXNOVXQUWKUXNVVDUXKUWLUWMUWNUWOYPUWPUWQUWRUWTUWSUXA $.
    $}

    $d g h k ph $.
    $( Strong dependent choice.  Suppose we may choose an element of ` A ` such
       that property ` ps ` holds, and suppose that if we have already chosen
       the first ` k ` elements (represented here by a function from
       ` 1 ... k ` to ` A ` ), we may choose another element so that all
       ` k + 1 ` elements taken together have property ` ps ` .  Then there
       exists an infinite sequence of elements of ` A ` such that the first
       ` n ` terms of this sequence satisfy ` ps ` for all ` n ` .  This
       theorem allows to construct infinite sequences where each term depends
       on all the previous terms in the sequence.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Proof shortened by Mario Carneiro, 3-Jun-2014.) $)
    sdc $p |- ( ph -> E. f ( f : Z --> A /\ A. n e. Z ch ) ) $=
      ( vx vy vj cv cfz co wf wa wrex cab c1 caddc cres wceq w3a cmpo weq oveq2
      feq2d anbi12d cbvrexvw abbii mpoeq123i eqidd eqeq1 3anbi2d rexbidv abbidv
      eqid cbvmpov eqtr3i sdclem1 ) ABCDEFUEUFGHIJKLUGHOMKUHZUIUJZGIUHZUKZDULZK
      OUMZIUNZMVQUOUPUJUIUJGJUHZUKZHUHZWDVRUQZURZFUSZKOUMZJUNZUTZMLUHZUIUJZGVSU
      KZBULZLOUMZIUNZMNOPQRSTUAUBUCUDWRVMUGHOWRWKUTWLUFUEOWRWEUEUHZWGURZFUSZKOU
      MZJUNZUTUGHOWRWKOWCWKOVMWQWBIWPWALKOLKVAZWOVTBDXDWNVRGVSWMVQMUIVBVCSVDVEV
      FWKVMVGUGHUFUEOWRWKXCWKUGUFVAWKVHHUEVAZWJXBJXEWIXAKOXEWHWTWEFWFWSWGVIVJVK
      VLVNVOVP $.
  $}

  ${
    $d C c f n $.  $d A a b c d f g m n x $.  $d M a b c d f g j k m n x $.
    $d Z a b c d g j m n x $.  $d N a b c d f g j k m n $.  $d R a b d $.
    $d ph c d f g j k m $.  $d ps a $.  $d ch a b c d g m n $.
    $d th c d f g n $.  $d ta a b c d g m $.  $d et a b g m $.
    fdc.1 $e |- A e. _V $.
    fdc.2 $e |- M e. ZZ $.
    fdc.3 $e |- Z = ( ZZ>= ` M ) $.
    fdc.4 $e |- N = ( M + 1 ) $.
    fdc.5 $e |- ( a = ( f ` ( k - 1 ) ) -> ( ph <-> ps ) ) $.
    fdc.6 $e |- ( b = ( f ` k ) -> ( ps <-> ch ) ) $.
    fdc.7 $e |- ( a = ( f ` n ) -> ( th <-> ta ) ) $.
    fdc.8 $e |- ( et -> C e. A ) $.
    fdc.9 $e |- ( et -> R Fr A ) $.
    fdc.10 $e |- ( ( et /\ a e. A ) -> ( th \/ E. b e. A ph ) ) $.
    fdc.11 $e |- ( ( ( et /\ ph ) /\ ( a e. A /\ b e. A ) ) -> b R a ) $.
    $( Finite version of dependent choice.  Construct a function whose value
       depends on the previous function value, except at a final point at which
       no new value can be chosen.  The final hypothesis ensures that the
       process will terminate.  The proof does not use the Axiom of Choice.
       (Contributed by Jeff Madsen, 18-Jun-2010.) $)
    fdc $p |- ( et -> E. n e. Z E. f ( f : ( M ... n ) --> A /\
              ( ( f ` M ) = C /\ ta ) /\ A. k e. ( N ... n ) ch ) ) $=
      ( vc vd vm vg vx vj wcel cv cfz co wf cfv wceq wa wral w3a wex c0 wss wbr
      wrex wn wi wsbc cuz ax-mp csn sylancr adantr a1i feq1 fveq1 eqeq1d eqtrdi
      cz wb sbceq2a anbi12d oveq2 feq2d fvex sbcie fveq2 sbceq1d bitr3id anbi2d
      syl c1 caddc oveq1i clt ltp1i raleqdv 3anbi123d exbidv rspcev adantll weq
      mpbi eqeq2 anbi1d 3anbi2d ad2antll cmin bitri sbceqbid ad2antlr eleq1 cif
      rexbidv eleq2s cle ltnlei elfzle1 biimtrdi com12 adantl iffalsed 1z com23
      mtoi ex imp ax-1cn cc fvmpt eqeq1 fvoveq1 ifbieq2d ifex sselid cvv sylibr
      crab cdif uzid eleqtrri cop eqid elexi vex fsn mpbir snssi fss fzsn feq2i
      fvsn simpr snex spcev syl12anc zrei peano2z fzn mp2an eqtri ral0 mpbiran2
      df-3an bitrdi a1d breq1 expcom dfrex2 imbitrdi con2d eldif simplbi2 dfss4
      ssrab2 eleq2i elrab3 bitrid sylibd cbvrexvw sbcbidv ralbidv rexbii imbi1d
      cbvexvw peano2uzs imbi12d imbi2d cmpt wo peano2uz elfzp12 iftrue biimprcd
      eleq1d ad2antrr 1re readdcli elfzelz eluzelz fzsubel biimpd mpanr2 mpanl1
      peano2zd mpd recni pncan3oi pncan sylancl oveq12d eleqtrd ffvelcdm sylan2
      zcnd anassrs ancom1s eqeltrd jaod sylbid ralrimiv fmpt adantlll 3ad2antr1
      sylib eluzfz1 eluzfz2 wne eluzle zleltp1 mpbid ltne neneqd fveq2d biimpar
      cr 3eqtrd ad2ant2l 3ad2antr2 eluzp1p1 fveq2i eleqtrrdi biimpa oveq1 eqtrd
      adantlr eqeq2i sylbi ltleii eluz2 mpbir3an fzss1 fzaddel gtneii ifnefalse
      mpanr12 simprl biimparc adantlrr eqeltri rspcva sylan fzssp1 subadd eqcom
      breqtrri mp3an23 addcomi biimtrid mp2b lttri syldan an32s adantlrl jaodan
      ralrimiva cbvralvw adantllr adantrlr ovex mptex syl121anc chvarvv syl2anc
      3adantr1 exlimdv rexlimdva 3syld an42s rexlimdvaa mpjaodan sylibrd notbii
      iman bitr4i imbitrrdi nrexdv df-ne wfr difss difexg expr biimtrrid ssdif0
      fri mt3d eqssd rabid2 ) FHGUOMLUPZUQURZGJUPZUSZMVXOUTZUIUPZVAZEVBZCKNVXMU
      QURZVCZVDZJVEZLOVIZUIGVCZVXPVXQHVAZEVBZVYBVDZJVEZLOVIZUEFGVYEUIGUUBZVAVYF
      FGVYLFGVYLUUCZVFVAZGVYLVGFVYNUJUPZPUPZIVHZVJUJVYMVCZPVYMVIZFVYRPVYMFVYPVY
      MUOZVYRVJZFVYRVYTFVYRVYPGUOZVYPVYLUOZVKZVYTVJZFWUBVYRWUCFWUBVYRWUCVKFWUBV
      BZVYRVXPVXQVYPVAZEVBZVYBVDZJVEZLOVIZWUCWUFDVYRWUKVKZAQGVIZWUFDVBWUKVYRWUB
      DWUKFWUBDVBZMOUOMMUQURZGVXOUSZWUGDPVXQVLZVBZVBZJVEZWUKMMVMUTZOMWCUOZMWVAU
      OSMUUDVNTUUEWUNWUOGMVYPUUFZVOZUSZMWVDUTZVYPVAZDWUTWUBWVEDWUBMVOZGWVDUSZWV
      EWUBWVHVYPVOZWVDUSZWVJGVGWVIWVKWVDWVDVAWVDUUGMVYPWVDMWCSUUHZPUUIZUUJUUKVY
      PGUULWVHWVJGWVDUUMVPWUOWVHGWVDWVBWUOWVHVASMUUNVNUUOUUAVQWVGWUNMVYPWVLWVMU
      UPZVRWUBDUUQWUSWVEWVGDVBZVBJWVDWVCUURVXOWVDVAZWUPWVEWURWVOWUOGVXOWVDVSWVP
      WUGWVGWUQDWVPVXQWVFVYPMVXOWVDVTZWAWVPWUGWUQDWDWVPVXQWVFVYPWVQWVNWBDPVXQWE
      WOWFWFUUSUUTWUJWUTLMOVXMMVAZWUIWUSJWVRWUIWUPWURCKVFVCZVDZWUSWVRVXPWUPWUHW
      URVYBWVSWVRVXNWUOGVXOVXMMMUQWGWHWVREWUQWUGEDPVXMVXOUTZVLZWVRWUQDEPWWAVXMV
      XOWIUDWJZWVRDPWWAVXQVXMMVXOWKWLWMWNWVRCKVYAVFWVRVYANMUQURZVFVXMMNUQWGWWDM
      WPWQURZMUQURZVFNWWEMUQUAWRMWWEWSVHZWWFVFVAZMMSUVAZWTZWWEWCUOZWVBWWGWWHWDW
      VBWWKSMUVBVNZSWWEMUVCUVDXGUVEWBXAXBWVTWUSWVSCKUVFWUPWURWVSUVHUVGUVIXCXDVP
      XEUVJWUFWUMWULWUFAWULQGFAWUBQUPZGUOZWULFAVBZWUBWWNVBZVBZVYRWWMVYMUOZVJZVX
      PVXQWWMVAZEVBZVYBVDZJVEZLOVIZWUKWWQWWRVYRWWQWWRVYQUJVYMVIZWUAWWQWWMVYPIVH
      ZWWRWXEVKUHWWRWXFWXEVYQWXFUJWWMVYMVYOWWMVYPIUVKXDUVLWOVYQUJVYMUVMUVNUVOWW
      NWWSWXDVKWWOWUBWWNWWSWWMGVYMUUCZUOZWXDWXHWWNWWSWWMGVYMUVPUVQWXHWWMVYLUOWW
      NWXDWXGVYLWWMVYLGVGZWXGVYLVAVYEUIGUVSZVYLGUVRXGUVTVYEWXDUIWWMGUIQXFZVYDWX
      CLOWXKVYCWXBJWXKVXTWXAVXPVYBWXKVXSWWTEVXRWWMVXQXHXIXJXCXRUWAUWBUWCXKWXDMU
      KUPZUQURZGULUPZUSZMWXNUTZWWMVAZDPWXLWXNUTZVLZVBZAQKUPZWXNUTZVLZPWYAWPXLUR
      ZWXNUTZVLZKNWXLUQURZVCZVDZULVEZUKOVIZWWQWUKWXDWXMGVXOUSZWWTDPWXLVXOUTZVLZ
      VBZCKWYGVCZVDZJVEZUKOVIWYKWXCWYRLUKOLUKXFZWXBWYQJWYSVXPWYLWXAWYOVYBWYPWYS
      VXNWXMGVXOVXMWXLMUQWGWHWYSEWYNWWTEWWBWYSWYNWWCWYSDPWWAWYMVXMWXLVXOWKWLWMW
      NWYSCKVYAWYGVXMWXLNUQWGXAXBXCUWDWYRWYJUKOWYQWYIJULJULXFZWYLWXOWYOWXTWYPWY
      HWXMGVXOWXNVSWYTWWTWXQWYNWXSWYTVXQWXPWWMMVXOWXNVTWAWYTDPWYMWXRWXLVXOWXNVT
      WLWFWYTCWYFKWYGCAQWYAVXOUTZVLZPWYDVXOUTZVLZWYTWYFXUDBQXUAVLZCXUBXUEPXUCWY
      DVXOWIVYPXUCVAABQXUAUBUWEWJBCQXUAWYAVXOWIUCWJXMZWYTXUBWYCPXUCWYEWYDVXOWXN
      VTWYTAQXUAWYBWYAVXOWXNVTWLXNWMUWFXBUWIUWGXMWWQWYJWUKUKOWWQWXLOUOZVBZWYIWU
      KULXUHWYIWUKXUHWYIVBWXLWPWQURZOUOZMXUIUQURZGVXOUSZWUGDPXUIVXOUTZVLZVBZCKN
      XUIUQURZVCZVDZJVEZWUKXUGXUJWWQWYIMWXLOTUWJXOXUHWYIXUSAWWPXUGWYIXUSVKZFAWU
      BXUGXUTWWNAQVYOVLZWUBVBZXUGVBZWXOWXPVYOVAZWXSVBZWYHVDZXUSVKZVKZAWUBVBZXUG
      VBZXUTVKUJQUJQXFZXVCXVJXVGXUTXVKXVBXVIXUGXVKXVAAWUBAQVYOWEXIXIXVKXVFWYIXU
      SXVKXVEWXTWXOWYHXVKXVDWXQWXSVYOWWMWXPXHXIXJUWHUWKXVAPVXRVLZVXRGUOZVBZXUGV
      BZXVFXULVXSXUNVBZXUQVDZJVEZVKZVKXVHUIPUIPXFZXVOXVCXVSXVGXVTXVNXVBXUGXVTXV
      LXVAXVMWUBXVAPVXRWEVXRVYPGXPWFXIXVTXVRXUSXVFXVTXVQXURJXVTXVPXUOXULXUQXVTV
      XSWUGXUNVXRVYPVXQXHZXIXJXCUWLUWKXVOXVFXVRXVOXVFVBXUKGUMXUKUMUPZMVAZVXRXWB
      WPXLURZWXNUTZXQZUWMZUSZMXWGUTZVXRVAZDPXUIXWGUTZVLZAQWYAXWGUTZVLZPWYDXWGUT
      ZVLZKXUPVCZXVRXVOXVEWXOXWHWYHXVMXUGWXOXWHXVLXVMXUGVBWXOVBZXWFGUOZUMXUKVCX
      WHXWRXWSUMXUKXWRXWBXUKUOZXWCXWBWWEXUIUQURZUOZUWNZXWSXUGXWTXXCWDZXVMWXOXUG
      XUIWVAUOZXXDXXEWXLWVAOMWXLUWOZTXSXWBMXUIUWPWOXOXWRXWCXWSXXBXVMXWCXWSVKXUG
      WXOXWCXWSXVMXWCXWFVXRGXWCVXRXWEUWQZUWSUWRUWTXUGWXOXXBXWSVKXVMXUGWXOVBZXXB
      XWSXXHXXBVBZXWFXWEGXXIXWCVXRXWEXXBXWCVJXXHXXBXWCWWEMXTVHZWWGXXJVJWWJMWWEW
      WIMWPWWIUXAUXBZYAXGXWCXXBXXJXWCXXBMXXAUOXXJXWBMXXAXPMWWEXUIYBYCYDYIYEYFWX
      OXUGXXBXWEGUOZWXOXUGXXBXXLXUGXXBVBZWXOXWDWXMUOXXLXXMXWDWWEWPXLURZXUIWPXLU
      RZUQURZWXMXXMXWBWCUOZXWDXXPUOZXXBXXQXUGXWBWWEXUIUXCYEXUGXXBXXQXXRVKXUGXXQ
      XXBXXRXUGXUIWCUOZXXQXXBXXRVKZVKXUGWXLWXLWCUOZWXLWVAOMWXLUXDTXSZUXIZXXSXXQ
      XXTWWKXXSXXQXXTWWLWWKXXSVBZXXQWPWCUOZXXTYGXYDXXQXYEVBVBXXBXXRXWBWPWWEXUIU
      XEUXFUXGUXHYJWOYHYKUXJXUGXXPWXMVAXXBXUGXXNMXXOWXLUQXXNMVAXUGMWPMWWIUXKZYL
      UXLZVRXUGWXLYMUOWPYMUOZXXOWXLVAXUGWXLXYBUXSYLWXLWPUXMUXNZUXOVQUXPWXMGXWDW
      XNUXQUXRUXTUYAUYBYJXEUYCUYDUYEUMXUKGXWFXWGXWGUUGZUYFUYIUYGUYHXUGXWJXVNXVF
      XUGMXUKUOZXWJXYKWXLWVAOWXLWVAUOZXXEXYKXXFMXUIUYJWOTXSUMMXWFVXRXUKXWGXXGXY
      JUIUUIZYNWOZXOXVOWXOXVEXWLWYHXUGWXSXWLXVNXVDXUGXWLWXSXUGDPXWKWXRXUGXWKXUI
      MVAZVXRXXOWXNUTZXQZXYPWXRXUGXUIXUKUOZXWKXYQVAXYRWXLWVAOXYLXXEXYRXXFMXUIUY
      KWOTXSUMXUIXWFXYQXUKXWGXWBXUIVAXWCXYOXWEXYPVXRXWBXUIMYOXWBXUIWPWXNXLYPYQX
      YJXYOVXRXYPXYMXXOWXNWIYRYNWOXUGXYOVXRXYPXUGXUIMXUGMUYTUOMXUIWSVHZXUIMUYLW
      WIXUGMWXLXTVHZXYSXYTWXLWVAOMWXLUYMTXSXUGWVBXYAXYTXYSWDSXYBMWXLUYNVPUYOMXU
      IUYPVPUYQYFXUGXXOWXLWXNXYIUYRVUAWLUYSVUBVUCXVOXVEWYHXWQWXOXVOXVDWYHXWQWXS
      XVLXUGXVDWYHVBZXWQXVMXVLXUGVBZYUAVBZAQUNUPZXWGUTZVLZPYUDWPXLURZXWGUTZVLZU
      NXUPVCXWQYUCYUIUNXUPYUCYUDXUPUOZYUDNVAZYUDNWPWQURZXUIUQURZUOZUWNZYUIYUBYU
      JYUOYUAXUGYUJYUOXVLXUGYUJYUOXUGXUINVMUTZUOYUJYUOWDXUGXUIWWEVMUTZYUPXUIYUQ
      UOWXLWVAOMWXLVUDTXSNWWEVMUAVUEVUFYUDNXUIUWPWOVUGXEVUJYUCYUKYUIYUNYUBXVDYU
      KYUIWYHYUBXVDYUKYUIXVLXUGXVDYUKVBZYUIXUGYURVBZYUIXVLYUSYUFXVAPYUHVXRYUSYU
      HXWIVXRYUKYUHXWIVAXUGXVDYUKYUGMXWGYUKYUGNWPXLURZMYUDNWPXLVUHYUTXXNMNWWEWP
      XLUAWRXYGUVEWBUYRXKXUGXWJYURXYNVQVUIYUSAQYUEVYOYUSYUEWWEXWGUTZWXPVYOYUKYU
      EYVAVAZXUGXVDYUKYUDWWEVAZYVBNWWEYUDUAVUKYUDWWEXWGWKVULXKXUGYVAWXPVAYURXUG
      YVAWWEMVAZVXRWXPXQZWXPXUGWWEXUKUOYVAYVEVAXUGXXAXUKWWEWWEWVAUOZXXAXUKVGYVF
      WVBWWKMWWEXTVHSWWLMWWEWWIXXKWWJVUMMWWEVUNVUOZWWEMXUIVUPVNXUGMWXMUOZWWEXXA
      UOZYVHWXLWVAOMWXLUYJTXSXUGWVBXYAYVHYVIWDZSXYBWVBXYAVBWVBXYEYVJSYGMWPMWXLV
      UQVUTVPUYOYSUMWWEXWFYVEXUKXWGXWBWWEVAZXWCYVDXWEWXPVXRXWBWWEMYOYVKXWDMWXNY
      VKXWDXXNMXWBWWEWPXLVUHXYGWBUYRYQXYJYVDVXRWXPXYMMWXNWIYRYNWOWWEMUYLYVEWXPV
      AMWWEWWIWWJVURWWEMVXRWXPVUSVNWBVQXUGXVDYUKVVAVUAWLXNVVBUXTUXTVVCXUGYUAYUN
      YUIXVLXUGWYHYUNYUIXVDXUGYUNWYHYUIXUGYUNVBZWYHAQYUGWXNUTZVLZPYUGWPXLURZWXN
      UTZVLZYUIYVLYUGWYGUOWYHYVQYVLYUGYULWPXLURZXXOUQURZWYGYVLYUDWCUOZYUGYVSUOZ
      YUNYVTXUGYUDYULXUIUXCZYEXUGYUNYVTYWAVKXUGYVTYUNYWAXUGYULWCUOZXXSYVTYUNYWA
      VKZVKNWCUOYWCNWWEWCUAWWLVVDZNUVBVNXYCYWCXXSVBZYVTYWDYWFYVTXYEYWDYGYWFYVTX
      YEVBVBYUNYWAYUDWPYULXUIUXEUXFUXGYJVPYHYKUXJXUGYVSWYGVAYUNXUGYVRNXXOWXLUQY
      VRNVAXUGNWPNNYWEUVAZUXKYLUXLVRXYIUXOVQUXPZWYFYVQKYUGWYGWYAYUGVAZWYCYVNPWY
      EYVPWYAYUGWPWXNXLYPYWIAQWYBYVMWYAYUGWXNWKWLXNVVEVVFYVLYUIYVQYVLYUFYVNPYUH
      YVPYVLYUHYUGMVAZVXRYVPXQZYVPYVLYUGXUKUOYUHYWKVAYVLXUPXUKYUGNWVAUOZXUPXUKV
      GNWWEWVAUAYVGVVDZNMXUIVUPVNYVLWYGXUPYUGNWXLVVGYWHYSYSUMYUGXWFYWKXUKXWGXWB
      YUGVAXWCYWJXWEYVPVXRXWBYUGMYOXWBYUGWPWXNXLYPYQXYJYWJVXRYVPXYMYVOWXNWIYRYN
      WOYVLYWJVXRYVPYUNYWJVJXUGYUNYWJYULWWEXTVHZWWEYULWSVHYWNVJWWEWWEWPWQURYULW
      SWWEXXKWTNWWEWPWQUAWRVVJWWEYULXXKNWPYWGUXAUXBZYAXGYUNYWJWPMWQURZYUDVAZYWN
      YUNYUDYMUOZYWJYWQWDZYUNYUDYWBUXSYWRXYHMYMUOYWSYLXYFYUDWPMVVHVVKWOYWQYVCYU
      NYWNYWQYUDYWPVAYVCYWPYUDVVIYWPWWEYUDWPMYLXYFVVLVUKXMYVCYUNYWNYVCYUNWWEYUM
      UOYWNYUDWWEYUMXPWWEYULXUIYBYCYDVVMUYDYIYEYFVUIYVLAQYUEYVMYVLYUEYUDMVAZVXR
      YVMXQZYVMYVLYUDXUKUOYUEYXAVAYVLYUMXUKYUDYWLYULWVAUOYUMXUKVGYWMMNUWOYULMXU
      IVUPVVNXUGYUNUUQYSUMYUDXWFYXAXUKXWGUMUNXFXWCYWTXWEYVMVXRXWBYUDMYOXWBYUDWP
      WXNXLYPYQXYJYWTVXRYVMXYMYUGWXNWIYRYNWOYVLYWTVXRYVMYUNYWTVJXUGYUNYWTYULMXT
      VHZMYULWSVHZYXBVJMNWSVHNYULWSVHYXCMWWENWSWWJUAVVJNYWGWTMNYULWWIYWGYWOVVOU
      VDMYULWWIYWOYAXGYWTYUNYXBYWTYUNMYUMUOYXBYUDMYUMXPMYULXUIYBYCYDYIYEYFVUIWL
      XNUYSVVPVVQVVRUYGVVSVVPVVTYUIXWPUNKXUPUNKXFZYUFXWNPYUHXWOYUDWYAWPXWGXLYPY
      XDAQYUEXWMYUDWYAXWGWKWLXNVWAUYIVWBVWCVWIXVQXWHXWJXWLVBZXWQVDJXWGUMXUKXWFM
      XUIUQVWDVWEVXOXWGVAZXULXWHXVPYXEXUQXWQXUKGVXOXWGVSYXFVXSXWJXUNXWLYXFVXQXW
      IVXRMVXOXWGVTWAYXFDPXUMXWKXUIVXOXWGVTWLWFYXFCXWPKXUPCXUDYXFXWPXUFYXFXUBXW
      NPXUCXWOWYDVXOXWGVTYXFAQXUAXWMWYAVXOXWGVTWLXNWMUWFXBUUSVWFYJVWGVWGVVCUYGY
      KWUJXUSLXUIOVXMXUIVAZWUIXURJYXGVXPXULWUHXUOVYBXUQYXGVXNXUKGVXOVXMXUIMUQWG
      WHYXGEXUNWUGEWWBYXGXUNWWCYXGDPWWAXUMVXMXUIVXOWKWLWMWNYXGCKVYAXUPVXMXUINUQ
      WGXAXBXCXDVWHYJVWJVWKVVMVWLVWMVWNYKUGVWOWUBWUCWUKWDFVYEWUKUIVYPGXVTVYDWUJ
      LOXVTVYCWUIJXVTVXTWUHVXPVYBXVTVXSWUGEXWAXIXJXCXRUWAYEVWPYJYHWUEWUBWUCVJVB
      ZVJWUDVYTYXHVYPGVYLUVPVWQWUBWUCVWRVWSVWTUVOYKVXAVYNVJVYMVFUYLZFVYSVYMVFVX
      BFGIVXCZVYMGVGZYXIVYSVKUFGVYLVXDYXJYXKYXIVYSVYMYTUOZYXJYXKYXIVBVYSGYTUOYX
      LRGVYLYTVXEVNPUJGVYMYTIVXIUXHVXFUXNVXGVXJGVYLVXHUUAWXIFWXJVRVXKVYEUIGVXLU
      YIVYEVYKUIHGVXRHVAZVYDVYJLOYXMVYCVYIJYXMVXTVYHVXPVYBYXMVXSVYGEVXRHVXQXHXI
      XJXCXRVVEVWH $.
  $}

  ${
    $d A a b c d f n $.  $d R a b d $.  $d M a b c d f k n $.
    $d Z a b c d n $.  $d N a b c d f k n $.  $d ph d f k $.  $d ps a d $.
    $d ch a b c d n $.  $d th d f n $.  $d ta a b c d $.  $d et a b c d f n $.
    $d ze b c d f n $.  $d si a c $.
    fdc1.1 $e |- A e. _V $.
    fdc1.2 $e |- M e. ZZ $.
    fdc1.3 $e |- Z = ( ZZ>= ` M ) $.
    fdc1.4 $e |- N = ( M + 1 ) $.
    fdc1.5 $e |- ( a = ( f ` M ) -> ( ze <-> si ) ) $.
    fdc1.6 $e |- ( a = ( f ` ( k - 1 ) ) -> ( ph <-> ps ) ) $.
    fdc1.7 $e |- ( b = ( f ` k ) -> ( ps <-> ch ) ) $.
    fdc1.8 $e |- ( a = ( f ` n ) -> ( th <-> ta ) ) $.
    fdc1.9 $e |- ( et -> E. a e. A ze ) $.
    fdc1.10 $e |- ( et -> R Fr A ) $.
    fdc1.11 $e |- ( ( et /\ a e. A ) -> ( th \/ E. b e. A ph ) ) $.
    fdc1.12 $e |- ( ( ( et /\ ph ) /\ ( a e. A /\ b e. A ) ) -> b R a ) $.
    $( Variant of ~ fdc with no specified base value.  (Contributed by Jeff
       Madsen, 18-Jun-2010.) $)
    fdc1 $p |- ( et -> E. n e. Z E. f ( f : ( M ... n ) --> A /\
                          ( si /\ ta ) /\ A. k e. ( N ... n ) ch ) ) $=
      ( vc vd cv cfz co wf wa wral w3a wex wrex wcel wsbc wi wceq eleq1w anbi2d
      sbceq2a anbi12d imbi1d cfv wsb c1 cmin sbsbc sbhypf bitr3id simprl adantr
      nfv wfr wo nfsbc1v nfcv nfor nfim sbceq1a rexbidv orbi12d imbi12d chvarfv
      nfrexw adantlr wbr nfan anbi1d breq2 adantllr fdc anassrs idd dfsbcq fvex
      sbcie bitr3di biimpcd adantl anim1d 3anim123d reximdv mpd chvarvv r19.29a
      eximdv ) FGNMUMZUNUOIKUMZUPZHEUQZCLOXOUNUOURZUSZKUTZMPVAZQIFUKUMZIVBZUQZG
      QYCVCZUQZYBVDFQUMZIVBZUQZGUQZYBVDUKQYCYHVEZYGYKYBYLYEYJYFGYLYDYIFUKQIVFVG
      GQYCVHVIVJYGXQNXPVKZYCVEZEUQZXSUSZKUTZMPVAZYBFYDYFYRAQULUMZVCZBCDQYSVCZEF
      YDYFUQZUQIYCJKLMNOPULRSTUAUBYTAQULVLYSLUMVMVNUOXPVKZVEBAQULVOABQULUUCBQVT
      UDVPVQUEUUADQULVLYSXOXPVKZVEEDQULVODEQULUUDEQVTUFVPVQFYDYFVRFIJWAUUBUHVSF
      YSIVBZUUAYTRIVAZWBZUUBYJDARIVAZWBZVDFUUEUQZUUGVDQULUUJUUGQUUJQVTUUAUUFQDQ
      YSWCYTQRIQIWDAQYSWCZWLWEWFYHYSVEZYJUUJUUIUUGUULYIUUEFQULIVFZVGUULDUUAUUHU
      UFDQYSWGUULAYTRIAQYSWGZWHWIWJUIWKWMFYTUUERUMZIVBZUQZUUOYSJWNZUUBFAUQZYIUU
      PUQZUQZUUOYHJWNZVDFYTUQZUUQUQZUURVDQULUVDUURQUVCUUQQFYTQFQVTUUKWOUUQQVTWO
      UURQVTWFUULUVAUVDUVBUURUULUUSUVCUUTUUQUULAYTFUUNVGUULYIUUEUUPUUMWPVIYHYSU
      UOJWQWJUJWKWRWSWTYGYQYAMPYGYPXTKYGXQXQYOXRXSXSYGXQXAYGYNHEYFYNHVDYEYNYFHY
      NGQYMVCYFHGQYMYCXBGHQYMNXPXCUCXDXEXFXGXHYGXSXAXIXNXJXKXLUGXM $.
  $}

  ${
    $d F m n p q s $.  $d A m n p q s $.  $d R m n p q s $.
    $( Two ways to say that a sequence respects a partial order.  (Contributed
       by Jeff Madsen, 2-Sep-2009.) $)
    seqpo $p |- ( ( R Po A /\ F : NN --> A ) ->
                  ( A. s e. NN ( F ` s ) R ( F ` ( s + 1 ) ) <-> A. m e. NN
                    A. n e. ( ZZ>= ` ( m + 1 ) ) ( F ` m ) R ( F ` n ) ) ) $=
      ( cn wa cv cfv c1 caddc wbr wral cuz wcel wi wceq fveq2 breq2d wpo imbi2d
      vp vq wf co cz fvoveq1 breq12d rspccva adantl peano2nn elnnuz sylib uztrn
      a1i sylibr expcom syl imdistani ad2ant2l ex ffvelcdm adantrr adantrl 3jca
      sylan2 potr expcomd syl5 expdimp adantr mpdd anasss com12 uzind4 ralrimiv
      w3a anassrs ralrimiva breq1d raleqbidv rspcv imdistanri nnzd uzid impbid1
      a2d ) ABUAZGAEUEZHZFIZEJZWLKLUFZEJZBMZFGNZCIZEJZDIZEJZBMZDWRKLUFZOJZNZCGN
      ZWKWQXFWKWQHZXECGWKWQWRGPZXEWKWQXHHZHZXBDXDWTXDPXJXBXJWSUCIZEJZBMZQXJWSXC
      EJZBMZQZXJWSUDIZEJZBMZQXJWSXQKLUFZEJZBMZQXJXBQUCUDXCWTXKXCRZXMXOXJYCXLXNW
      SBXKXCESTUBXKXQRZXMXSXJYDXLXRWSBXKXQESTUBXKXTRZXMYBXJYEXLYAWSBXKXTESTUBXK
      WTRZXMXBXJYFXLXAWSBXKWTESTUBXPXCUGPXIXOWKWPXOFWRGWLWRRWMWSWOXNBWLWRESWLWR
      KELUHUIUJUKUPXQXDPZXJXSYBXJYGXSYBQZWKWQXHYGYHQXGXHYGYHXHYGHXHXQGPZHZXGYHX
      HYGYIXHXCKOJZPZYGYIQXHXCGPYLWRULXCUMUNYGYLYIYGYLHXQYKPYIXCXQKUOXQUMUQURUS
      UTXGYJXRYABMZYHXGYJYMWQYIYMWKXHWPYMFXQGWLXQRWMXRWOYABWLXQESWLXQKELUHUIUJV
      AVBWKYJYMYHQZQWQWIWJYJYNWJYJHZWSAPZXRAPZYAAPZVRZWIYNYOYPYQYRWJXHYPYIGAWRE
      VCVDWJYIYQXHGAXQEVCVEWJYIYRXHYIWJXTGPYRXQULGAXTEVCVGVEVFWIYSYNWIYSHXSYMYB
      AWSXRYABVHVIVBVJVKVLVMVJVKVNVOWHVPVOVQVSVTVBXFWPFGXFWLGPZHWMXABMZDWNOJZNZ
      YTHWPYTXFUUCXEUUCCWLGWRWLRZXBUUADXDUUBWRWLKOLUHUUDWSWMXABWRWLESWAWBWCWDYT
      UUCWNUUBPZWPYTWNUGPUUEYTWNWLULWEWNWFUSUUAWPDWNUUBWTWNRXAWOWMBWTWNESTUJVGU
      SVTWG $.
  $}

  ${
    $d F k m n p q $.  $d A k m n p q $.
    $( An increasing sequence of positive integers takes on indefinitely large
       values.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    incsequz $p |- ( ( F : NN --> NN /\ A. m e. NN
                    ( F ` m ) < ( F ` ( m + 1 ) ) /\ A e. NN ) ->
                                  E. n e. NN ( F ` n ) e. ( ZZ>= ` A ) ) $=
      ( vk cn cv cfv c1 caddc co wbr wcel cuz wrex wa wi wceq fveq2 cr vp vq wf
      clt wral eleq2d rexbidv imbi2d c0 wne 1nn ne0ii ffvelcdm elnnuz ralrimiva
      sylib r19.2z sylancr adantr peano2nn adantl nnre ad2antrr adantlr adantll
      cle nnred 1red leadd1d fvoveq1 breq12d rspcv imdistani wb sylan2 nnltp1le
      syl2anc biimpa anasss anass1rs peano2re syl letr syl3anc mpan2d sylbid cz
      adantlrr nnzd eluz syl2an adantrlr anassrs peano2zd 3imtr4d eleq1d rspcev
      nnz syl6an rexlimdva cbvrexvw imbitrdi ex a2d nnind com12 3impia ) FFDUCZ
      BGZDHZXIIJKDHZUDLZBFUEZAFMZCGZDHZANHZMZCFOZXNXHXMPZXSXTXPUAGZNHZMZCFOZQXT
      XPINHZMZCFOZQXTXPUBGZNHZMZCFOZQXTXPYHIJKZNHZMZCFOZQXTXSQUAUBAYAIRZYDYGXTY
      PYCYFCFYPYBYEXPYAINSUFUGUHYAYHRZYDYKXTYQYCYJCFYQYBYIXPYAYHNSUFUGUHYAYLRZY
      DYOXTYRYCYNCFYRYBYMXPYAYLNSUFUGUHYAARZYDXSXTYSYCXRCFYSYBXQXPYAANSUFUGUHXH
      YGXMXHFUIUJYFCFUEYGIFUKULXHYFCFXHXOFMZPZXPFMZYFFFXODUMZXPUNUPUOYFCFUQURUS
      YHFMZXTYKYOUUDXTYKYOQUUDXTPZYKEGZDHZYMMZEFOZYOUUEYJUUICFUUEYTPZXOIJKZFMZY
      JUUKDHZYMMZUUIYTUULUUEXOUTZVAUUJYHXPVFLZYLUUMVFLZYJUUNUUJUUPYLXPIJKZVFLZU
      UQUUJYHXPIUUDYHTMZXTYTYHVBZVCXTYTXPTMZUUDXHYTUVBXMUUAXPUUCVGVDVEUUJVHVIUU
      JUUSUURUUMVFLZUUQXTYTUVCUUDXHYTXMUVCYTXMPXHYTXPUUMUDLZPUVCYTXMUVDXLUVDBXO
      FXIXORXJXPXKUUMUDXIXODSXIXOIDJVJVKVLVMXHYTUVDUVCUUAUVDUVCUUAUUBUUMFMZUVDU
      VCVNUUCYTXHUULUVEUUOFFUUKDUMZVOXPUUMVPVQVRVSVOVTVEUUDXHYTUUSUVCPUUQQZXMUU
      DXHPYTPYLTMZUURTMZUUMTMZUVGUUDUVHXHYTUUDUUTUVHUVAYHWAWBVCXHYTUVIUUDUUAUUR
      UUAUUBUURFMUUCXPUTWBVGVEXHYTUVJUUDYTXHUULUVJUUOXHUULPZUUMUVFVGVOVEYLUURUU
      MWCWDWHWEWFUUDXTYTYJUUPVNZUUDXHYTUVLXMUUDYHWGMXPWGMUVLUUAYHWRZUUAXPUUCWIY
      HXPWJWKWLWMUUDXTYTUUNUUQVNZUUDXHYTUVNXMUUDYLWGMUUMWGMZUVNUUAUUDYHUVMWNYTX
      HUULUVOUUOUVKUUMUVFWIVOYLUUMWJWKWLWMWOUUHUUNEUUKFUUFUUKRUUGUUMYMUUFUUKDSW
      PWQWSWTUUHYNECFUUFXORUUGXPYMUUFXODSWPXAXBXCXDXEXFXG $.

    $( An increasing sequence of positive integers takes on indefinitely large
       values.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    incsequz2 $p |- ( ( F : NN --> NN /\ A. m e. NN
            ( F ` m ) < ( F ` ( m + 1 ) ) /\ A e. NN ) ->
              E. n e. NN A. k e. ( ZZ>= ` n ) ( F ` k ) e. ( ZZ>= ` A ) ) $=
      ( vp vq cn cv cfv c1 caddc clt wbr wral wcel cuz wa wi cr wf w3a incsequz
      co wrex wpo wb wss nnssre wor ltso sopo ax-mp poss seqpo biimpd imdistani
      mp2 mpan wceq wo uzp1 fveq2 adantl ffvelcdm nnzd uzid syl adantr adantllr
      cz eqeltrd fvoveq1 breq1d raleqbidv breq2d sylan adantlll peano2nn elnnuz
      rspccva sylib uztrn ancoms sylibr sylan2 anassrs cle zre ltle syl2an eluz
      sylibrd syl2anc mpd jaodan ex ralrimdva stoic3 reximdvai ) HHEUAZCIZEJXBK
      LUDEJMNCHOZAHPZUBZDIZEJZAQJZPZDHUEBIZEJZXHPZBXFQJZOZDHUEACDEUCXEXIXNDHXAX
      CXAFIZEJZGIZEJZMNZGXOKLUDQJZOZFHOZRZXDXFHPZXIXNSZSXAXCYBXAXCYBHMUFZXAXCYB
      UGHTUHTMUFZYFUITMUJYGUKTMULUMHTMUNURHMFGECUOUSUPUQYCXDRZYDYEYHYDRXIXLBXMY
      CYDXJXMPZXIXLSZXDYCYDRZYIRXKXGQJZPZYJYIYKXJXFUTZXJXFKLUDZQJZPZVAYMXFXJVBY
      KYNYMYQXAYDYNYMYBXAYDRZYNRXKXGYLYNXKXGUTYRXJXFEVCVDYRXGYLPZYNYRXGVKPZYSYR
      XGHHXFEVEVFZXGVGVHVIVLVJYKYQRXGXKMNZYMYBYDYQUUBXAYBYDRXGXRMNZGYPOZYQUUBYA
      UUDFXFHXOXFUTZXSUUCGXTYPXOXFKQLVMUUEXPXGXRMXOXFEVCVNVOWAUUCUUBGXJYPXQXJUT
      XRXKXGMXQXJEVCVPWAVQVRXAYDYQUUBYMSZYBYRYQRYTXKVKPZUUFYRYTYQUUAVIXAYDYQUUG
      YDYQRXAXJHPZUUGYDYOKQJZPZYQUUHYDYOHPUUJXFVSYOVTWBUUJYQRXJUUIPZUUHYQUUJUUK
      YOXJKWCWDXJVTWEVQXAUUHRXKHHXJEVEVFWFWGYTUUGRUUBXGXKWHNZYMYTXGTPXKTPUUBUUL
      SUUGXGWIXKWIXGXKWJWKXGXKWLWMWNVJWOWPWFYMXIXLXGXKAWCWQVHVJWRWQWSWTWO $.
  $}

  ${
    $d A x $.  $d B x $.
    $( A bounded above set of positive integers is finite.  (Contributed by
       Jeff Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro, 28-Feb-2014.) $)
    nnubfi $p |- ( ( A C_ NN /\ B e. NN ) -> { x e. A | x < B } e. Fin ) $=
      ( cn wss wcel wa cc0 cfz co cfn cv wbr wi cn0 nnnn0 syl adantlr cr nnre
      clt crab fzfi wral cle adantr ad3antlr ad2antlr ltle syl2anc imp elfz2nn0
      ssel2 syl3anbrc ex ralrimiva rabss sylibr ssfi sylancr ) BDEZCDFZGZHCIJZK
      FALZCUAMZABUBZVDEZVGKFHCUCVCVFVEVDFZNZABUDVHVCVJABVCVEBFZGZVFVIVLVFGVEOFZ
      COFZVECUEMZVIVLVMVFVAVKVMVBVAVKGZVEDFZVMBDVEUMZVEPQRUFVBVNVAVKVFCPUGVLVFV
      OVLVESFZCSFZVFVONVAVKVSVBVPVQVSVRVETQRVBVTVAVKCTUHVECUIUJUKVECULUNUOUPVFA
      BVDUQURVDVGUSUT $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( An infinite set of positive integers is unbounded above.  (Contributed
       by Jeff Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro,
       28-Feb-2014.) $)
    nninfnub $p |- ( ( A C_ NN /\ -. A e. Fin /\ B e. NN )
                                  -> { x e. A | B < x } =/= (/) ) $=
      ( vy cn wss cfn wcel wn cv clt wbr c0 wa wral wi cr adantlr ralimdva cc0
      crab wne wal eq0 breq2 elrab notbii imnan sylbb2 alimi ralrid ssel2 nnred
      wceq cle nnre ad2antlr lenlt biimprd syl2anc cfz co cn0 w3a nnnn0d adantr
      fzfi nnnn0 ad3antlr simpr 3jca ex elfz2nn0 imbitrrdi dfss3 sylibr sylancr
      imp ssfi syld syl5 biimtrid necon3bd an32s 3impa ) BEFZBGHZIZCEHZCAJZKLZA
      BUAZMUBZWFWIWHWMWFWINZWHWMWNWGWLMWLMUNDJZWLHZIZDUCZWNWGDWLUDWRCWOKLZIZDBO
      ZWNWGWRWTDBWQWOBHZWTPZDWQXBWSNZIXCWPXDWKWSAWOBWJWOCKUEUFUGXBWSUHUIUJUKWNX
      AWOCUOLZDBOZWGWNWTXEDBWNXBNZWOQHZCQHZWTXEPWFXBXHWIWFXBNZWOBEWOULZUMRWIXIW
      FXBCUPUQXHXINXEWTWOCURUSUTSWNXFWGWNXFNZTCVAVBZGHBXMFZWGTCVGXLWOXMHZDBOZXN
      WNXFXPWNXEXODBXGXEWOVCHZCVCHZXEVDZXOXGXEXSXGXENXQXRXEXGXQXEWFXBXQWIXJWOXK
      VERVFWIXRWFXBXECVHVIXGXEVJVKVLWOCVMVNSVRDBXMVOVPXMBVSVQVLVTWAWBWCVRWDWE
      $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Topology
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( An open set is open in the subspace topology.  (Contributed by Jeff
     Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro, 15-Dec-2013.) $)
  subspopn $p |- ( ( ( J e. Top /\ A e. V ) /\ ( B e. J /\ B C_ A ) )
                                    -> B e. ( J |`t A ) ) $=
    ( ctop wcel wa wss crest co wi w3a elrestr wceq dfss2 eleq1 sylbi syl5ibcom
    cin wb 3expa impr ) CEFZADFZGBCFZBAHZBCAIJZFZUCUDUEUFUHKUCUDUELBASZUGFZUFUH
    BACEDMUFUIBNUJUHTBAOUIBUGPQRUAUB $.

  ${
    $d J x y $.  $d N x $.  $d S x y $.
    $( Neighborhoods are closed under finite intersection.  (Contributed by
       Jeff Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro, 25-Nov-2013.) $)
    neificl $p |- ( ( ( J e. Top /\ N C_ ( ( nei ` J ) ` S ) ) /\
              ( N e. Fin /\ N =/= (/) ) ) -> |^| N e. ( ( nei ` J ) ` S ) ) $=
      ( vx vy ctop wcel cnei cfv wss cfn c0 wne wa cint simprl cv w3a wi wral
      wal cin innei 3expib ralrimivv fiint sylib wceq sseq1 neeq1 eleq1 3ancomb
      3anbi123d 3anass bitri bitrdi inteq eleq1d imbi12d spcgv syl5 com3l mpdi
      impl ) BFGZCABHIIZJZCKGZCLMZNZCOZVFGZVEVGVJNZVHVLVGVHVIPVHVEVMVLVEDQZVFJZ
      VNLMZVNKGZRZVNOZVFGZSZDUAZVHVMVLSZVEVNEQZUBVFGZEVFTDVFTWBVEWEDEVFVFVEVNVF
      GWDVFGWEABWDVNUCUDUEDEDVFUFUGWAWCDCKVNCUHZVRVMVTVLWFVRVGVIVHRZVMWFVOVGVPV
      IVQVHVNCVFUIVNCLUJVNCKUKUMWGVGVHVIRVMVGVIVHULVGVHVIUNUOUPWFVSVKVFVNCUQURU
      SUTVAVBVCVD $.
  $}

  ${
    lpss2.1 $e |- X = U. J $.
    $( Limit points of a subset are limit points of the larger set.
       (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    lpss2 $p |- ( ( J e. Top /\ A C_ X /\ B C_ A ) ->
                          ( ( limPt ` J ) ` B ) C_ ( ( limPt ` J ) ` A ) ) $=
      ( lpss3 ) ABCDEF $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Metric spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d M u v w x y $.  $d X u v w x y $.  $d Y u v w x y $.  $d F u v w x y $.
    $d A u v w x y $.  $d N u v w $.
    metf1o.2 $e |- N = ( x e. Y , y e. Y |-> ( ( F ` x ) M ( F ` y ) ) ) $.
    $( Use a bijection with a metric space to construct a metric on a set.
       (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    metf1o $p |- ( ( Y e. A /\ M e. ( Met ` X ) /\
                                F : Y -1-1-onto-> X ) -> N e. ( Met ` Y ) ) $=
      ( wcel cfv cv co wceq wb wral wa wi ffvelcdm ex vu vv vw cmet wf1o w3a cr
      cxp wf cc0 caddc cle wbr f1of anim12d syl metcl sylan9r 3adant1 ralrimivv
      3expib fmpo sylib fveq2 oveq1d oveq2d ovex ovmpo eqeq1d adantl imp meteq0
      adantll 3expb adantlr syldan wf1 f1of1 f1fveq sylan 3bitrd mettri2 expcom
      ancoms impcom anassrs adantr oveq12d breq12d ralrimiva jca 3adantl1 ismet
      mpbird 3ad2ant1 mpbir2and ) HCJZEGUDKJZHGDUEZUFZFHUDKJZHHUHUGFUIZUALZUBLZ
      FMZUJNZXCXDNZOZXEUCLZXCFMZXIXDFMZUKMZULUMZUCHPZQZUBHPUAHPZWTALZDKZBLZDKZE
      MZUGJZBHPAHPXBWTYBABHHWRWSXQHJZXSHJZQZYBRWQWSYEXRGJZXTGJZQZWRYBWSHGDUIZYE
      YHRHGDUNZYIYCYFYDYGYIYCYFHGXQDSTYIYDYGHGXSDSTUOUPWRYFYGYBXRXTEGUQVAURUSUT
      ABHHYAUGFIVBVCWTXOUAUBHHWTXCHJZXDHJZQZXOWRWSYMXOWQWRWSQZYMQZXHXNYOXFXCDKZ
      XDDKZEMZUJNZYPYQNZXGYMXFYSOYNYMXEYRUJABXCXDHHYAYRFYPXTEMXQXCNXRYPXTEXQXCD
      VDVEXSXDNZXTYQYPEXSXDDVDZVFIYPYQEVGVHZVIVJYNYMYPGJZYQGJZQZYSYTOZWSYMUUFWR
      WSYMUUFWSYIYMUUFRYJYIYKUUDYLUUEYIYKUUDHGXCDSTYIYLUUEHGXDDSTUOZUPVKVMWRUUF
      UUGWSWRUUDUUEUUGYPYQEGVLVNVOVPWSYMYTXGOZWRWSHGDVQYMUUIHGDVRHGXCXDDVSVTVMW
      AYOXMUCHYOXIHJZQXMYRXIDKZYPEMZUUKYQEMZUKMZULUMZYNYMUUJUUOYNYMUUJQZUUFUUKG
      JZQZUUOWSUUPUURWRWSUUPUURWSYIUUPUURRYJYIYMUUFUUJUUQUUHYIUUJUUQHGXIDSTUOUP
      VKVMWRUURUUOWSUURWRUUOUUQUUFWRUUORZUUQUUDUUEUUSWRUUQUUDUUEUFUUOYPYQUUKEGW
      BWCVNWDWEVOVPWFYMUUJXMUUOOYNUUPXEYRXLUUNULYMXEYRNUUJUUCWGUUPXJUULXKUUMUKY
      KUUJXJUULNZYLUUJYKUUTABXIXCHHYAUULFUUKXTEMZXQXINXRUUKXTEXQXIDVDVEZXSXCNXT
      YPUUKEXSXCDVDVFIUUKYPEVGVHWDVOYLUUJXKUUMNZYKUUJYLUVCABXIXDHHYAUUMFUVAUVBU
      UAXTYQUUKEUUBVFIUUKYQEVGVHWDVMWHWIVMWNWJWKWLTUTWQWRXAXBXPQOWSUAUBUCCFHWMW
      OWP $.
  $}

  ${
    blssp.2 $e |- N = ( M |` ( S X. S ) ) $.
    $( A ball in the subspace metric.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Revised by Mario Carneiro, 5-Jan-2014.) $)
    blssp $p |- ( ( ( M e. ( Met ` X ) /\ S C_ X ) /\
        ( Y e. S /\ R e. RR+ ) ) ->
      ( Y ( ball ` N ) R ) = ( ( Y ( ball ` M ) R ) i^i S ) ) $=
      ( cmet cfv wcel wss wa crp cxmet cin cxr cbl co wceq metxmet simprl sylib
      ad2antrr simplr sseqin2 eleqtrrd rpxr ad2antll blres syl3anc ) CEHIJZBEKZ
      LZFBJZAMJZLZLZCENIJZFEBOZJAPJZFADQIRFACQIRBOSUKURULUPCETUCUQFBUSUMUNUOUAU
      QULUSBSUKULUPUDBEUEUBUFUOUTUMUNAUGUHDCFAEBGUIUJ $.
  $}

  ${
    $d k n x D $.  $d k n x F $.  $d k n x M $.  $d k n x N $.  $d k n x ph $.
    $d k n X $.
    mettrifi.2 $e |- ( ph -> D e. ( Met ` X ) ) $.
    mettrifi.3 $e |- ( ph -> N e. ( ZZ>= ` M ) ) $.
    mettrifi.4 $e |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. X ) $.
    $( Generalized triangle inequality for arbitrary finite sums.  (Contributed
       by Jeff Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro,
       4-Jun-2014.) $)
    mettrifi $p |- ( ph -> ( ( F ` M ) D ( F ` N ) ) <_
           sum_ k e. ( M ... ( N - 1 ) ) ( ( F ` k ) D ( F ` ( k + 1 ) ) ) ) $=
      ( cfz co wcel cfv c1 cle wbr wi wceq oveq2d vx vn cmin cv csu cuz eluzfz2
      caddc syl eleq1 fveq2 sumeq1d breq12d imbi12d imbi2d cz cc0 0le0 a1i cmet
      oveq1 wral eluzfz1 ralrimiva eleq1d sylc met0 syl2anc c0 clt eluzel2 zred
      rspcv ltm1d peano2zm fzn syl2anc2 mpbid sum0 eqtrdi 3brtr4d a1d peano2fzr
      wb wa adantl imim1d w3a 3ad2ant1 simp3 cbvralvw sylib 3impia rsp syl13anc
      ex mettri cr metcl syl3anc readdcld fzfid adantr wss elfzuz3 fzss2 sselda
      3ad2antl1 syldan elfzuz peano2uz eluzp1p1 uztrn elfzuzb sylanbrc fsumrecl
      rspccva sylan letr mpand fzssp1 cc eluzelz 3ad2ant2 ax-1cn npcan sseqtrid
      zcnd sylancl leadd1d simp2 recnd fvoveq1 oveq12d fsumm1 breq2d bitr4d a2d
      pncan 3imtr4d 3expia syld expcom uzind4 mpcom mpd ) AFEFKLZMZEDNZFDNZBLZE
      FOUCLZKLZCUDZDNZUUNOUHLZDNZBLZCUEZPQZAFEUFNZMZUUHIEFUGUIUVBAUUHUUTRZIAUAU
      DZUUGMZUUIUVDDNZBLZEUVDOUCLZKLZUURCUEZPQZRZRAEUUGMZUUIUUIBLZEEOUCLZKLZUUR
      CUEZPQZRZRZAUBUDZUUGMZUUIUWADNZBLZEUWAOUCLZKLZUURCUEZPQZRZRAUWAOUHLZUUGMZ
      UUIUWJDNZBLZEUWJOUCLZKLZUURCUEZPQZRZRAUVCRUAUBEFUVDESZUVLUVSAUWSUVEUVMUVK
      UVRUVDEUUGUJUWSUVGUVNUVJUVQPUWSUVFUUIUUIBUVDEDUKTUWSUVIUVPUURCUWSUVHUVOEK
      UVDEOUCVATULUMUNUOUVDUWASZUVLUWIAUWTUVEUWBUVKUWHUVDUWAUUGUJUWTUVGUWDUVJUW
      GPUWTUVFUWCUUIBUVDUWADUKTUWTUVIUWFUURCUWTUVHUWEEKUVDUWAOUCVATULUMUNUOUVDU
      WJSZUVLUWRAUXAUVEUWKUVKUWQUVDUWJUUGUJUXAUVGUWMUVJUWPPUXAUVFUWLUUIBUVDUWJD
      UKTUXAUVIUWOUURCUXAUVHUWNEKUVDUWJOUCVATULUMUNUOUVDFSZUVLUVCAUXBUVEUUHUVKU
      UTUVDFUUGUJUXBUVGUUKUVJUUSPUXBUVFUUJUUIBUVDFDUKTUXBUVIUUMUURCUXBUVHUULEKU
      VDFOUCVATULUMUNUOUVTEUPMZAUVRUVMAUQUQUVNUVQPUQUQPQAURUSABGUTNMZUUIGMZUVNU
      QSHAUVMUUOGMZCUUGVBZUXEAUVBUVMIEFVCUIAUXFCUUGJVDZUXFUXECEUUGUUNESUUOUUIGU
      UNEDUKVEVMVFZUUIBGVGVHAUVQVIUURCUEUQAUVPVIUURCAUVOEVJQZUVPVISZAEAEAUVBUXC
      IEFVKUIZVLVNAUXCUVOUPMUXJUXKWDUXLEVOEUVOVPVQVRULUURCVSVTWAWBUSUWAUVAMZAUW
      IUWRAUXMUWIUWRRAUXMWEZUWIUWKUWHRUWRUXNUWKUWBUWHUXMUWKUWBRAUXMUWKUWBUWAEFW
      CWPWFZWGUXNUWKUWHUWQAUXMUWKUWHUWQRAUXMUWKWHZUWDUWCUWLBLZUHLZEUWAKLZUURCUE
      ZPQZUWMUXTPQZUWHUWQUXPUWMUXRPQZUYAUYBUXPUXDUXEUWLGMZUWCGMZUYCAUXMUXDUWKHW
      IZAUXMUXEUWKUXIWIZUXPUWKUXGUYDAUXMUWKWJZAUXMUXGUWKUXHWIZUXFUYDCUWJUUGUUNU
      WJSUUOUWLGUUNUWJDUKVEVMVFZUXPUYEUBUUGVBZUWBUYEUXPUXGUYKUYIUXFUYECUBUUGUUN
      UWASZUUOUWCGUUNUWADUKZVEWKWLZAUXMUWKUWBUXOWMZUYEUBUUGWNVFZUUIUWLUWCBGWQWO
      UXPUWMWRMZUXRWRMUXTWRMUYCUYAWEUYBRUXPUXDUXEUYDUYQUYFUYGUYJUUIUWLBGWSWTUXP
      UWDUXQUXPUXDUXEUYEUWDWRMUYFUYGUYPUUIUWCBGWSWTZUXPUXDUYEUYDUXQWRMUYFUYPUYJ
      UWCUWLBGWSWTZXAUXPUXSUURCUXPEUWAXBUXPUUNUXSMZWEZUXDUXFUUQGMZUURWRMZUXPUXD
      UYTUYFXCUXPUYTUUNUUGMZUXFUXPUXSUUGUUNUXPFUWAUFNMZUXSUUGXDUXPUWBVUEUYOUWAE
      FXEUIUWAEFXFUIXGAUXMVUDUXFUWKJXHXIUXPUYTUUPUUGMZVUBVUAUUPUVAMZFUUPUFNZMZV
      UFVUAUUNUVAMZVUGUYTVUJUXPUUNEUWAXJWFEUUNXKUIVUAFUWJUFNMZUWJVUHMZVUIUXPVUK
      UYTUXPUWKVUKUYHUWJEFXEUIXCVUAUWAUUNUFNMZVULUYTVUMUXPUUNEUWAXEWFUUNUWAXLUI
      UWJFUUPXMVHUUPEFXNXOUXPUYKVUFVUBUYNUYEVUBUBUUPUUGUWAUUPSUWCUUQGUWAUUPDUKV
      EXQXRXIUUOUUQBGWSWTZXPUWMUXRUXTXSWTXTUXPUWHUXRUWGUXQUHLZPQUYAUXPUWDUWGUXQ
      UYRUXPUWFUURCUXPEUWEXBUXPUUNUWFMUYTVUCUXPUWFUXSUUNUXPEUWEOUHLZKLUWFUXSEUW
      EYAUXPVUPUWAEKUXPUWAYBMZOYBMZVUPUWASUXPUWAUXMAUWAUPMUWKEUWAYCYDYHZYEUWAOY
      FYITYGXGVUNXIXPUYSYJUXPUXTVUOUXRPUXPUURUXQCEUWAAUXMUWKYKVUAUURVUNYLUYLUUO
      UWCUUQUWLBUYMUUNUWAODUHYMYNYOYPYQUXPUWPUXTUWMPUXPUWOUXSUURCUXPUWNUWAEKUXP
      VUQVURUWNUWASVUSYEUWAOYSYITULYPYTUUAYRUUBUUCYRUUDUUEUUF $.
  $}

  ${
    $d j k n x D $.  $d j k n x F $.  $d j k x G $.  $d x J $.  $d j k n x X $.
    $d j k m n x A $.  $d j k m n x B $.  $d j k n x ph $.  $d j k x Y $.
    lmclim2.2 $e |- ( ph -> D e. ( Met ` X ) ) $.
    lmclim2.3 $e |- ( ph -> F : NN --> X ) $.
    ${
      lmclim2.4 $e |- J = ( MetOpen ` D ) $.
      lmclim2.5 $e |- G = ( x e. NN |-> ( ( F ` x ) D Y ) ) $.
      lmclim2.6 $e |- ( ph -> Y e. X ) $.
      $( A sequence in a metric space converges to a point iff the distance
         between the point and the elements of the sequence converges to 0.
         (Contributed by Jeff Madsen, 2-Sep-2009.)  (Proof shortened by Mario
         Carneiro, 5-Jun-2014.) $)
      lmclim2 $p |- ( ph -> ( F ( ~~>t ` J ) Y <-> G ~~> 0 ) ) $=
        ( vk vj cfv wbr wcel wral cn clm cv co clt cuz wrex crp wa cc0 cli cmet
        c1 cxmet metxmet syl nnuz 1zzd eqidd lmmbrf cabs cvv cmpt mptex eqeltri
        nnex a1i wceq fveq2 oveq1d ovex fvmpt adantl cr adantr ffvelcdmda metcl
        syl3anc recnd clim0c wb eluznn cle metge0 absidd breq1d sylan2 ralbidva
        anassrs rexbidva ralbidv biantrurd 3bitrrd bitrd ) ADHFUAPQHGRZNUBZDPZH
        CUCZBUBZUDQZNOUBZUEPZSZOTUFZBUGSZUHZEUIUJQZABWPCHONDFULGTKACGUKPRZCGUMP
        RICGUNUOUPAUQZAWOTRZUHZWPURJUSAXFWQUTPZWRUDQZNXASZOTUFZBUGSXDXEABWQONEU
        LVATUPXHEVARAEBTWRDPZHCUCZVBVALBTXPVEVCVDVFXIWOEPWQVGABWOXPWQTEWRWOVGXO
        WPHCWRWODVHVILWPHCVJVKVLXJWQXJXGWPGRZWNWQVMRAXGXIIVNZATGWODJVOZAWNXIMVN
        ZWPHCGVPVQZVRVSAXNXCBUGAXMXBOTAWTTRZUHXLWSNXAAYBWOXARZXLWSVTZYBYCUHAXIY
        DWOWTWAXJXKWQWRUDXJWQYAXJXGXQWNUIWQWBQXRXSXTWPHCGWCVQWDWEWFWHWGWIWJAWNX
        DMWKWLWM $.
    $}

    geomcau.4 $e |- ( ph -> A e. RR ) $.
    geomcau.5 $e |- ( ph -> B e. RR+ ) $.
    geomcau.6 $e |- ( ph -> B < 1 ) $.
    geomcau.7 $e |- ( ( ph /\ k e. NN ) ->
      ( ( F ` k ) D ( F ` ( k + 1 ) ) ) <_ ( A x. ( B ^ k ) ) ) $.
    $( If the distance between consecutive points in a sequence is bounded by a
       geometric sequence, then the sequence is Cauchy.  (Contributed by Jeff
       Madsen, 2-Sep-2009.)  (Proof shortened by Mario Carneiro,
       5-Jun-2014.) $)
    geomcau $p |- ( ph -> F e. ( Cau ` D ) ) $=
      ( vm cfv wcel co wbr cn cmul vj vn vx ccau cv clt cuz wral wrex cexp cmin
      crp c1 cdiv cabs cmpt cc0 cli cn0 cvv nnuz 1zzd rpcnd rpred rpge0d absidd
      eqbrtrd expcnv cr 1re resubcl sylancr wb posdif sylancl mpbid elrpd recnd
      rerpdivcld nnex mptex a1i wa cc wceq nnnn0 adantl oveq2 eqid fvmpt syl cz
      nnz rpexpcl syl2an eqeltrd adantr mulcomd oveq1d oveq2d 3eqtr4d climmulc2
      ovex weq mul01d breqtrd remulcld clim0c wi uzid fvoveq1d breq1d rspcv cle
      3syl cmet simpl ffvelcdm eluznn metcl syl3anc csu ad2antrl nn0zd ad2antrr
      wf eluznn0 sylan reexpcld caddc cfz simpll elfzuz sylan2 syl2anc fsumrecl
      mpbird letrd adantlr eqidd cseq geolim2 eqtr4d rpexpcld wne rpne0d div12d
      isermulc2 isumclim cdm seqex breldm isumrecl eqeltrrd abscld fzfid simprl
      ffvelcdmda peano2nn simprr mettrifi fsumle wss fzssuz 0red metge0 divge0d
      ledivmul2d mulge0d isumless leabsd rpre ad2antlr lelttr anassrs ralrimdva
      mpand syld reximdva ralimdva mpd cxmet metxmet iscauf ) AFDUDOPUAUEZFOZUB
      UEZFOZDQZUCUEZUFRZUBUWEUGOZUHZUASUIZUCULUHZACUWGUJQZBUMCUKQZUNQZTQZUOOZUW
      JUFRZUBUWLUHZUASUIZUCULUHZUWOANSCNUEZUJQZUWRTQZUPZUQURRUXDAUXHUWRUQTQUQUR
      AUQUWRUBNUSUXFUPZUXHUMUTSVAAVBZACNACKVCZACUOOZCUMUFACACKVDZACKVEVFLVGZVHA
      UWRABUWQJAUWQAUMVIPZCVIPZUWQVIPVJUXMUMCVKVLZACUMUFRZUQUWQUFRZLAUXPUXOUXRU
      XSVMUXMVJCUMVNVOVPVQZVSZVRZUXHUTPANSUXGVTWAWBZAUWGSPZWCZUWGUXIOZUWPWDUYEU
      WGUSPZUYFUWPWEUYDUYGAUWGWFWGNUWGUXFUWPUSUXIUXEUWGCUJWHZUXIWICUWGUJXCWJWKZ
      UYEUWPACULPZUWGWLPUWPULPUYDKUWGWMCUWGWNWOZVCZWPUYEUWSUWRUWPTQUWGUXHOZUWRU
      YFTQUYEUWPUWRUYLAUWRWDPUYDUYBWQWRUYDUYMUWSWEANUWGUXGUWSSUXHNUBXDUXFUWPUWR
      TUYHWSUXHWIUWPUWRTXCWJWGZUYEUYFUWPUWRTUYIWTXAXBAUWRUYBXEXFAUCUWSUAUBUXHUM
      UTSVAUXJUYCUYNUYEUWSUYEUWPUWRUYEUWPUYKVDAUWRVIPUYDUYAWQXGVRXHVPAUXCUWNUCU
      LAUWJULPZWCZUXBUWMUASUYPUWESPZWCZUXBCUWEUJQZUWRTQZUOOZUWJUFRZUWMUYRUWEWLP
      ZUWEUWLPUXBVUBXIUYQVUCUYPUWEWMWGUWEXJUXAVUBUBUWEUWLUBUAXDZUWTVUAUWJUFVUDU
      WPUYSUWRUOTUWGUWECUJWHXKXLXMXOUYRVUBUWKUBUWLUYPUYQUWGUWLPZVUBUWKXIUYPUYQV
      UEWCZWCZUWIVUAXNRZVUBUWKAVUFVUHUYOAVUFWCZUWIUYTVUAVUIDGXPOPZUWFGPZUWHGPZU
      WIVIPZAVUJVUFHWQZASGFYFZUYQVUKVUFIUYQVUEXQSGUWEFXRWOAVUOUYDVULVUFIUWGUWEX
      SSGUWGFXRWOUWFUWHDGXTYAZVUIUWLBCEUEZUJQZTQZEYBZUYTVIVUIVUSUYTENUWLBUXFTQZ
      UPZUWEUWLUWLWIZVUIUWEUYQUWEUSPZAVUEUWEWFYCZYDZVUQUWLPZVUQVVBOZVUSWEVUINVU
      QVVAVUSUWLVVBNEXDUXFVURBTUXEVUQCUJWHZWTVVBWIBVURTXCWJWGZVUIVVGWCZVUSVVKBV
      URABVIPZVUFVVGJYEZVVKCVUQAUXPVUFVVGUXMYEVUIVVDVVGVUQUSPVVEVUQUWEYGYHYIZXG
      ZVRVUIYJVVBUWEUUAZBUYSUWQUNQZTQZUYTURVUIVVQBENUWLUXFUPZVVBUWEUWLVVCVVFABW
      DPVUFABJVRWQZVUICEVVSUWEACWDPVUFUXKWQAUXLUMUFRVUFUXNWQVVEVVGVUQVVSOZVURWE
      VUINVUQUXFVURUWLVVSVVIVVSWICVUQUJXCWJWGZUUBVVKVWAVURWDVWBVVKVURVVNVRWPVVK
      VVHVUSBVWATQVVJVVKVWAVURBTVWBWTUUCUUHZVUIBUYSUWQVVTVUIUYSVUICUWEAUYJVUFKW
      QVVFUUDVCAUWQWDPVUFAUWQUXQVRWQAUWQUQUUEVUFAUWQUXTUUFWQUUGXFUUIZVUIVUSEVVB
      UWEUWLVVCVVFVVJVVOVUIVVPVVRURRVVPURUUJPVWCVVPVVRURYJVVBUWEUUKBVVQTXCUULWK
      ZUUMZUUNZVUIUYTVUIUYTVWGVRUUOZVUIUWIVUTUYTXNVUIUWIUWEUWGUMUKQZYKQZVUQFOZV
      UQUMYJQZFOZDQZEYBZVUTVUPVUIVWJVWNEVUIUWEVWIUUPZVUIVUQVWJPZWCZAVUQSPZVWNVI
      PZAVUFVWQYLZVWQVUIVVGVWSVUQUWEVWIYMZVUIUYQVVGVWSAUYQVUEUUQVUQUWEXSYHZYNZA
      VWSWCZVUJVWKGPZVWMGPZVWTAVUJVWSHWQZASGVUQFIUURZAVUOVWLSPVXGVWSIVUQUUSSGVW
      LFXRWOZVWKVWMDGXTYAZYOZYPZVWFVUIDEFUWEUWGGVUNAUYQVUEUUTVUQUWEUWGYKQPVUIVV
      GVXFVUQUWEUWGYMVVKAVWSVXFAVUFVVGYLZVXCVXIYOYNUVAVUIVWOVWJVUSEYBVUTVXMVUIV
      WJVUSEVWPVWQVUIVVGVUSVIPVXBVVOYNZYPVWFVUIVWJVWNVUSEVWPVXLVXOVWRAVWSVWNVUS
      XNRZVXAVXDMYOUVBVUIVWJVUSEVVBUWEUWLVVCVVFVWPVWJUWLUVCVUIUWEVWIUVDWBVVJVVO
      VVKBVURVVMVVNVVKAVWSUQBXNRVXNVXCVXEUQVWNVURUNQZBVXEUVEVXEVWNVURVXKAUYJVUQ
      WLPVURULPZVWSKVUQWMCVUQWNWOZVSAVVLVWSJWQZVXEVWNVURVXKVXSVXEVUJVXFVXGUQVWN
      XNRVXHVXIVXJVWKVWMDGUVFYAUVGVXEVXQBXNRVXPMVXEVWNBVURVXKVXTVXSUVHYQYRYOVVK
      VURVVKAVWSVXRVXNVXCVXSYOVEUVIVWEUVJYRYRVWDXFVUIUYTVWGUVKYRYSVUGVUMVUAVIPZ
      UWJVIPZVUHVUBWCUWKXIAVUFVUMUYOVUPYSAVUFVYAUYOVWHYSUYOVYBAVUFUWJUVLUVMUWIV
      UAUWJUVNYAUVQUVOUVPUVRUVSUVTUWAAUCUWHUWFDUAUBFUMGSVAAVUJDGUWBOPHDGUWCWKUX
      JUYEUWHYTAUYQWCUWFYTIUWDYQ $.
  $}

  ${
    $d j k m n x D $.  $d j k m n x G $.  $d j k m n x ph $.  $d j k m n x X $.
    $d j k m x F $.  $d k m n N $.  $d j m n x W $.  $d j k m x Z $.
    $d j n M $.
    caures.1 $e |- Z = ( ZZ>= ` M ) $.
    caures.3 $e |- ( ph -> M e. ZZ ) $.
    caures.4 $e |- ( ph -> D e. ( Met ` X ) ) $.
    ${
      caures.5 $e |- ( ph -> F e. ( X ^pm CC ) ) $.
      $( The restriction of a Cauchy sequence to an upper set of integers is
         Cauchy.  (Contributed by Jeff Madsen, 2-Sep-2009.)  (Revised by Mario
         Carneiro, 5-Jun-2014.) $)
      caures $p |- ( ph ->
                     ( F e. ( Cau ` D ) <-> ( F |` Z ) e. ( Cau ` D ) ) ) $=
        ( vk vj vx cc co wcel cfv wral wa cvv cpm cdm clt wbr w3a cuz wrex cres
        crp ccau uztrn2 adantll biantrurd dmres elin2 bitr4di ralbidva rexbidva
        cv 3anbi1d ralbidv cmet wss elfvdm syl cnex ssid cz uzssz zsscn eqsstri
        sstri pmss12g mpanl12 sylancl fvexi pmresg sylancr sseldd 3bitr3d cxmet
        metxmet eqidd iscau4 wceq fvres adantl 3bitr4d ) ACENUAOZPZKUSZCUBZPZWK
        CQZEPZWNLUSZCQZBOMUSUCUDZUEZKWPUFQZRZLFUGZMUIRZSZCFUHZWIPZWKXEUBZPZWOWR
        UEZKWTRZLFUGZMUIRZSZCBUJQZPXEXNPAXCXLXDXMAXBXKMUIAXAXJLFAWPFPZSZWSXIKWT
        XPWKWTPZSZWMXHWOWRXRWMWKFPZWMSXHXRXSWMXOXQXSADWKWPFGUKULUMWKFWLXGCFUNUO
        UPUTUQURVAAWJXCJUMAXFXLAEFUAOZWIXEAEVBUBZPZNTPZXTWIVCZABEVBQPZYBIBEVBVD
        VEVFEEVCFNVCYBYCSYDEVGFDUFQZNGYFVHNDVIVJVLVKEFENYATVMVNVOAFTPWJXEXTPFDU
        FGVPJEFNCTVQVRVSUMVTAMWNWQBLKCDEFGAYEBEWAQPIBEWBVEZHAXSSWNWCXPWQWCWDAMW
        NWQBLKXEDEFGYGHXSWKXEQWNWEAWKFCWFWGXOWPXEQWQWEAWPFCWFWGWDWH $.
    $}

    caushft.4 $e |- W = ( ZZ>= ` ( M + N ) ) $.
    caushft.5 $e |- ( ph -> N e. ZZ ) $.
    caushft.7 $e |- ( ( ph /\ k e. Z ) -> ( F ` k ) = ( G ` ( k + N ) ) ) $.
    caushft.8 $e |- ( ph -> F e. ( Cau ` D ) ) $.
    caushft.9 $e |- ( ph -> G : W --> X ) $.
    $( A shifted Cauchy sequence is Cauchy.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Revised by Mario Carneiro, 5-Jun-2014.) $)
    caushft $p |- ( ph -> G e. ( Cau ` D ) ) $=
      ( cfv wcel vn vm vx vj ccau cv co clt wbr cuz wral wrex crp cdm caddc w3a
      cc cpm wa cmet cxmet metxmet wceq ralrimiva fveq2 fvoveq1 eqeq12d rspccva
      sylan iscau4 mpbid simprd cz eleq2i biimpi eluzadd syl2anr eleqtrrdi cmin
      syl simplr eleqtrdi eluzelz ad2antrr eluzsub syl3anc ralimi oveq1d breq1d
      simpr simp3 syl2im adantl npcand fveq2d wf uztrn2 ffvelcdmd adantr metsym
      rspcv zcnd sylibd ralrimdva raleqbidv rspcev syl6an rexlimdva ralimdv mpd
      eqtrd zaddcld eqidd iscauf mpbird ) AEBUESZTUAUFZESZUBUFZESZBUGZUCUFZUHUI
      ZUBXQUJSZUKZUAHULZUCUMUKZACUFZDUNTZYHGUOUGESZITZYJUDUFZGUOUGZESZBUGZYBUHU
      IZUPZCYLUJSZUKZUDJULZUCUMUKZYGADIUQURUGTZUUAADXPTUUBUUAUSQAUCYJYNBUDCDFIJ
      KABIUTSTZBIVASTMBIVBVTZLPAYHDSZYJVCZCJUKYLJTZYLDSZYNVCZAUUFCJPVDUUFUUICYL
      JYHYLVCUUEUUHYJYNYHYLDVEYHYLGEUOVFVGVHVIVJVKVLAYTYFUCUMAYSYFUDJAUUGUSZYMH
      TZYSYNXTBUGZYBUHUIZUBYMUJSZUKZYFUUJYMFGUOUGZUJSZHUUGYLFUJSZTZGVMTZYMUUQTA
      UUGUUSJUURYLKVNVOOGFYLVPVQNVRZUUJYSUUMUBUUNUUJXSUUNTZUSZYSXSGVSUGZGUOUGZE
      SZYNBUGZYBUHUIZUUMUVCUVDYRTZYSYPCYRUKUVHUVCYLVMTZUUTUVBUVIUVCUUSUVJUVCYLJ
      UURAUUGUVBWAKWBFYLWCVTAUUTUUGUVBOWDUUJUVBWJGYLXSWEWFYQYPCYRYIYKYPWKWGYPUV
      HCUVDYRYHUVDVCZYOUVGYBUHUVKYJUVFYNBYHUVDGEUOVFWHWIXAWLUVCUVGUULYBUHUVCUVG
      XTYNBUGZUULUVCUVFXTYNBUVCUVEXSEUVCXSGUVCXSUVBXSVMTUUJYMXSWCWMXBAGUQTUUGUV
      BAGOXBWDWNWOWHUVCUUCXTITYNITZUVLUULVCAUUCUUGUVBMWDUVCHIXSEAHIEWPZUUGUVBRW
      DUUJUUKUVBXSHTZUVAUUPXSYMHNWQVIWRUUJUVMUVBUUJHIYMEAUVNUUGRWSUVAWRWSXTYNBI
      WTWFXKWIXCXDYEUUOUAYMHXQYMVCZYCUUMUBYDUUNXQYMUJVEUVPYAUULYBUHUVPXRYNXTBXQ
      YMEVEWHWIXEXFXGXHXIXJAUCXTXRBUAUBEUUPIHNUUDAFGLOXLAUVOUSXTXMAXQHTUSXRXMRX
      NXO $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Continuous maps and homeomorphisms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x $.
    constcncf.1 $e |- F = ( x e. CC |-> A ) $.
    $( A constant function is a continuous function on ` CC ` .  (Contributed
       by Jeff Madsen, 2-Sep-2009.)  (Moved into main set.mm as ~ cncfmptc and
       may be deleted by mathbox owner, JM. --MC 12-Sep-2015.)  (Revised by
       Mario Carneiro, 12-Sep-2015.) $)
    constcncf $p |- ( A e. CC -> F e. ( CC -cn-> CC ) ) $=
      ( cc wcel cmpt ccncf co wss ssid cncfmptc mp3an23 eqeltrid ) BEFZCAEBGZEE
      HIZDOEEJZRPQFEKZSABEELMN $.
  $}

  ${
    $d J x $.  $d K x $.  $d F x $.  $d X x $.  $d Y x $.  $d A x $.  $d B x $.
    cnres2.1 $e |- X = U. J $.
    cnres2.2 $e |- Y = U. K $.
    $( The restriction of a continuous function to a subset is continuous.
       (Contributed by Jeff Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro,
       15-Dec-2013.) $)
    cnres2 $p |- ( ( ( J e. Top /\ K e. Top ) /\ ( A C_ X /\ B C_ Y ) /\
                ( F e. ( J Cn K ) /\ A. x e. A ( F ` x ) e. B ) ) -> ( F |` A )
                  e. ( ( J |`t A ) Cn ( K |`t B ) ) ) $=
      ( ctop wcel wa wss ccn co cfv crest syl2anc wb cv wral cres simp3l simp2l
      w3a cnrest ctopon crn simp1r toptopon sylib cima df-ima simp3r cdm wf cnf
      wfun ffun 3syl wceq fdm funimass4 mpbird eqsstrrid simp2r cnrest2 syl3anc
      sseqtrrd mpbid ) EKLZFKLZMZBGNZCHNZMZDEFOPLZAUADQCLABUBZMZUFZDBUCZEBRPZFO
      PLZWBWCFCRPOPLZWAVRVOWDVNVQVRVSUDZVNVOVPVTUEZBDEFGIUGSWAFHUHQLZWBUIZCNVPW
      DWETWAVMWHVLVMVQVTUJFHJUKULWAWIDBUMZCDBUNWAWJCNZVSVNVQVRVSUOWADUSZBDUPZNW
      KVSTWAVRGHDUQZWLWFDEFGHIJURZGHDUTVAWABGWMWGWAVRWNWMGVBWFWOGHDVCVAVJABCDVD
      SVEVFVNVOVPVTVGCWBWCFHVHVIVK $.
  $}

  $( A continuous function is continuous onto its image.  (Contributed by Jeff
     Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro, 15-Dec-2013.) $)
  cnresima $p |- ( ( J e. Top /\ K e. Top /\ F e. ( J Cn K ) )
                            -> F e. ( J Cn ( K |`t ran F ) ) ) $=
    ( ctop wcel ccn co w3a crn crest simp3 cuni ctopon cfv wss wb eqid toptopon
    simp2 sylib ssidd cnf frnd 3ad2ant3 cnrest2 syl3anc mpbid ) BDEZCDEZABCFGEZ
    HZUJABCAIZJGFGEZUHUIUJKUKCCLZMNEZULULOULUNOZUJUMPUKUIUOUHUIUJSCUNUNQZRTUKUL
    UAUJUHUPUIUJBLZUNAABCURUNURQUQUBUCUDULABCUNUEUFUG $.

  ${
    $d A x $.  $d B x $.  $d J x $.  $d K x $.
    cncfres.1 $e |- A C_ CC $.
    cncfres.2 $e |- B C_ CC $.
    cncfres.3 $e |- F = ( x e. CC |-> C ) $.
    cncfres.4 $e |- G = ( x e. A |-> C ) $.
    cncfres.5 $e |- ( x e. A -> C e. B ) $.
    cncfres.6 $e |- F e. ( CC -cn-> CC ) $.
    cncfres.7 $e |- J = ( MetOpen ` ( ( abs o. - ) |` ( A X. A ) ) ) $.
    cncfres.8 $e |- K = ( MetOpen ` ( ( abs o. - ) |` ( B X. B ) ) ) $.
    $( A continuous function on complex numbers restricted to a subset.
       (Contributed by Jeff Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro,
       12-Sep-2015.) $)
    cncfres $p |- G e. ( J Cn K ) $=
      ( ccncf co wcel cc ccn wf fmpti wss wb cmpt cres wceq resmpt ax-mp eqtr4i
      eqeltrri rescncf mp2 eqeltri cncfcdm mp2an cabs cmin ccom cncfmet eleqtri
      mpbir cxp eqid ) FBCQRZGHUARZFVFSZBCFUBZABCDFLMUCCTUDZFBTQRZSVHVIUEJFATDU
      FZBUGZVKFABDUFZVMLBTUDZVMVNUHIATBDUIUJUKVOVLTTQRZSVMVKSIEVLVPKNULTTBVLUMU
      NUOBTCFUPUQVCVOVJVFVGUHIJBCURUSUTZBBVDUGZVQCCVDUGZGHVRVEVSVEOPVAUQVB $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Boundedness
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c TotBnd $.
  $c Bnd $.
  $( Extend class notation with the class of totally bounded metric spaces. $)
  ctotbnd $a class TotBnd $.
  $( Extend class notation with the class of bounded metric spaces. $)
  cbnd $a class Bnd $.

  ${
    $d b d m v x y $.
    $( Define the class of totally bounded metrics.  A metric space is totally
       bounded iff it can be covered by a finite number of balls of any given
       radius.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    df-totbnd $a |- TotBnd = ( x e. _V |-> { m e. ( Met ` x ) |
      A. d e. RR+ E. v e. Fin ( U. v = x /\
        A. b e. v E. y e. x b = ( y ( ball ` m ) d ) ) } ) $.
  $}

  ${
    $d b d m v x M $.  $d b d m v x y X $.
    $( The predicate "is a totally bounded metric space".  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    istotbnd $p |- ( M e. ( TotBnd ` X ) <-> ( M e. ( Met ` X ) /\
      A. d e. RR+ E. v e. Fin ( U. v = X /\
        A. b e. v E. x e. X b = ( x ( ball ` M ) d ) ) ) ) $=
      ( vm vy ctotbnd cfv wcel cmet cv wceq wrex wral wa cfn crp ralbidv cvv co
      cuni cbl elfvex adantr crab fveq2 eqeq2 rexeq anbi12d rabeqbidv df-totbnd
      rexbidv rabex fvmpt eleq2d oveqd eqeq2d anbi2d elrab bitrdi pm5.21nii
      fvex ) CDIJZKZDUAKZCDLJZKZBMZUCZDNZEMZAMZFMZCUDJZUBZNZADOZEVJPZQZBROZFSPZ
      QZCDIUEVIVGWCCDLUEUFVGVFCVLVMVNVOGMZUDJZUBZNZADOZEVJPZQZBROZFSPZGVHUGZKWD
      VGVEWNCHDVKHMZNZWHAWOOZEVJPZQZBROZFSPZGWOLJZUGWNUAIWODNZXAWMGXBVHWODLUHXC
      WTWLFSXCWSWKBRXCWPVLWRWJWODVKUIXCWQWIEVJWHAWODUJTUKUNTULHABGEFUMWMGVHDLVD
      UOUPUQWMWCGCVHWECNZWLWBFSXDWKWABRXDWJVTVLXDWIVSEVJXDWHVRADXDWGVQVMXDWFVPV
      NVOWECUDUHURUSUNTUTUNTVAVBVC $.
  $}

  ${
    $d M d v b x $.  $d X d v b x $.
    $( The predicate "is a totally bounded metric space."  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    istotbnd2 $p |- ( M e. ( Met ` X ) -> ( M e. ( TotBnd ` X ) <->
       A. d e. RR+ E. v e. Fin ( U. v = X /\
         A. b e. v E. x e. X b = ( x ( ball ` M ) d ) ) ) ) $=
      ( ctotbnd cfv wcel cmet cv cuni wceq cbl co wrex wral wa cfn crp istotbnd
      baib ) CDGHICDJHIBKZLDMEKAKFKCNHOMADPEUCQRBSPFTQABCDEFUAUB $.
  $}

  ${
    $d b d f v w x M $.  $d b d f v w x X $.
    $( A metric space is totally bounded iff there is a finite &epsilon;-net
       for every positive &epsilon;.  This differs from the definition in
       providing a finite set of ball centers rather than a finite set of
       balls.  (Contributed by Mario Carneiro, 12-Sep-2015.) $)
    istotbnd3 $p |- ( M e. ( TotBnd ` X ) <-> ( M e. ( Met ` X ) /\ A. d e. RR+
      E. v e. ( ~P X i^i Fin ) U_ x e. v ( x ( ball ` M ) d ) = X ) ) $=
      ( vw vb vf cfv wcel cv wceq wrex wral wa cfn crp ciun wss syl ctotbnd cbl
      cmet cuni co cpw cin istotbnd wf wex oveq1 eqeq2d ac6sfi ad2antlr simprrl
      wi ex crn frnd wfo simplr ffnd dffn4 sylib fofi syl2anc elfpw sylanbrc wb
      wfn eleq2d rexrn eliun 3bitr4g eqrdv simprrr iuneq2 uniiun simprl eqtr3id
      3eqtr2d iuneq1 eqeq1d rspcev expr exlimdv syld expimpd rexlimdva cmpt cab
      simprbi ad2antrl mptfi rnfi 3syl ovex dfiun3 simprr rnmpt simplbi ss2abdv
      eqid ssrexv eqsstrid unieq ssabral sseq1 bitr3id anbi12d syl12anc ralbidv
      impbid pm5.32i bitri ) CDUAIJCDUCIJZFKZUDZDLZGKZAKZEKZCUBIZUEZLZADMZGXQNZ
      OZFPMZEQNZOXPABKZYDRZDLZBDUFPUGZMZEQNZOAFCDGEUHXPYJYPXPYIYOEQXPYIYOXPYHYO
      FPXPXQPJZOZXSYGYOYRXSOZYGXQDHKZUIZXTXTYTIZYBYCUEZLZGXQNZOZHUJZYOYQYGUUGUP
      XPXSYQYGUUGYEUUDGAXQDHYAUUBLZYDUUCXTYAUUBYBYCUKZULUMUQUNYSUUFYOHYRXSUUFYO
      YRXSUUFOZOZYTURZYNJZAUULYDRZDLZYOUUKUULDSUULPJZUUMUUKXQDYTYRXSUUAUUEUOZUS
      UUKYQXQUULYTUTZUUPXPYQUUJVAUUKYTXQVJZUURUUKXQDYTUUQVBZXQYTVCVDXQUULYTVEVF
      UULDVGVHUUKUUNGXQUUCRZGXQXTRZDUUKBUUNUVAUUKYKYDJZAUULMZYKUUCJZGXQMZYKUUNJ
      YKUVAJUUKUUSUVDUVFVIUUTUVCUVEAGXQYTUUHYDUUCYKUUIVKVLTAYKUULYDVMGYKXQUUCVM
      VNVOUUKUUEUVBUVALYRXSUUAUUEVPGXQXTUUCVQTUUKUVBXRDGXQVRYRXSUUFVSVTWAYMUUOB
      UULYNYKUULLYLUUNDAYKUULYDWBWCWDVFWEWFWGWHWIXPYMYIBYNXPYKYNJZYMYIXPUVGYMOO
      ZAYKYDWJZURZPJZUVJUDZDLZUVJYFGWKZSZYIUVHYKPJZUVIPJUVKUVGUVPXPYMUVGYKDSZUV
      PYKDVGZWLWMAYKYDWNUVIWOWPUVHUVLYLDAYKYDYAYBYCWQWRXPUVGYMWSVTUVHUVJYEAYKMZ
      GWKUVNAGYKYDUVIUVIXCWTUVHUVSYFGUVHUVQUVSYFUPUVGUVQXPYMUVGUVQUVPUVRXAWMYEA
      YKDXDTXBXEYHUVMUVOOFUVJPXQUVJLZXSUVMYGUVOUVTXRUVLDXQUVJXFWCYGXQUVNSUVTUVO
      YFGXQXGXQUVJUVNXHXIXJWDXKWEWIXMXLXNXO $.
  $}

  ${
    $d b d v x M $.  $d b d v x X $.
    $( The predicate "totally bounded" implies ` M ` is a metric space.
       (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    totbndmet $p |- ( M e. ( TotBnd ` X ) -> M e. ( Met ` X ) ) $=
      ( vv vb vx vd ctotbnd cfv wcel cmet cv cuni wceq cbl co wrex wral cfn crp
      wa istotbnd simplbi ) ABGHIABJHICKZLBMDKEKFKANHOMEBPDUCQTCRPFSQECABDFUAUB
      $.
  $}

  ${
    $d r v x M $.
    $( The metric (there is only one) on the empty set is totally bounded.
       (Contributed by Mario Carneiro, 16-Sep-2015.) $)
    0totbnd $p |- ( X = (/) ->
      ( M e. ( TotBnd ` X ) <-> M e. ( Met ` X ) ) ) $=
      ( vx vv vr c0 wceq ctotbnd cfv wcel cmet fveq2 eleq2d cv cbl ciun cpw cfn
      co crp cin wrex wral 0elpw elin mpbir2an iuneq1 eqeq1d rspcev mp2an rgenw
      0fi 0iun istotbnd3 mpbiran2 bitr4id bitrd ) BFGZABHIZJAFHIZJZABKIZJZURUSU
      TABFHLMURVAAFKIZJZVCVAVECDNZCNENAOISZPZFGZDFQZRUAZUBZETUCVLETFVKJZCFVGPZF
      GZVLVMFVJJFRJFUDULFVJRUEUFCVGUMVIVODFVKVFFGVHVNFCVFFVGUGUHUIUJUKCDAFEUNUO
      URVBVDABFKLMUPUQ $.
  $}

  ${
    $d b c d f u v w x y z M $.  $d b c d f u v w x y z X $.
    $d c d f u v w x y z N $.  $d b c d f u v w x y z Y $.
    sstotbnd.2 $e |- N = ( M |` ( Y X. Y ) ) $.
    $( Condition for a subset of a metric space to be totally bounded.
       (Contributed by Mario Carneiro, 12-Sep-2015.) $)
    sstotbnd2 $p |- ( ( M e. ( Met ` X ) /\ Y C_ X ) ->
      ( N e. ( TotBnd ` Y ) <-> A. d e. RR+ E. v e. ( ~P X i^i Fin )
        Y C_ U_ x e. v ( x ( ball ` M ) d ) ) ) $=
      ( vy vz wcel wss wa co cin crp wral wceq syl c0 vw vc vf cmet cfv ctotbnd
      cv cbl ciun cpw cfn wrex cxp cres metres2 eqeltrid istotbnd3 baib simpllr
      sspwd ssrind simprl sseldd simprr wel cxmet metxmet ad4antr elfpw simplbi
      wb adantl sselda simp-4r sseqin2 sylib eleqtrrd rpxrd blres syl3anc inss1
      eqsstrdi ralrimiva ss2iun adantrr eqsstrrd ex reximdv2 ralimdva sylbid c2
      cxr jca cdiv wi simpr rphalfcld oveq2 iuneq2d sseq2d rexbidv rspcv wne wf
      crab simprbi ad2antrl ssrab2 ssfi sylancl oveq1 ineq1d incom eqtrdi dfin5
      wex weq neeq1d rabn0 bitrdi rgen cima mpbird wfn elpreima imaeq2d eleq12d
      elrab id adantr syl2anc cbviunv ad4antlr iunss sylibr eqtrid sylan syl2an
      sstrd syld eleq1 ac6sfi cdm ccnv w3a fdm feq2d ffn baibd ralbidva ralrab2
      3jca simpr2 frnd ffnd simpr1 fnfi rnfi sylanbrc rpxr blssm iunin1 simplrr
      crn sseqtrdi 0ss sseq1 mpbiri a1i simpr3 imbi12d rspccva ad5antr cnvimass
      cr sstrid rpred simplbda blhalf syl22anc sseli ffvelcdm sseqtrrd fnfvelrn
      simp-5r ssiun2s adantlr pm2.61dne iuneq1 eqeq1d rspcev exlimdv rexlimdvaa
      eqssd mpd ralrimdva sylibrd impbid ) CEUDUEKZFELZMZDFUFUEKZFABUGZAUGZGUGZ
      CUHUEZNZUIZLZBEUJZUKOZULZGPQZUXAUXBAUXCUXDUXEDUHUEZNZUIZFRZBFUJZUKOZULZGP
      QZUXMUXADFUDUEZKZUXBUYAVKUXADCFFUMUNUYBHCFEUOUPZUXBUYCUYAABDFGUQURSUXAUXT
      UXLGPUXAUXEPKZMZUXQUXIBUXSUXKUYFUXCUXSKZUXQMZUXCUXKKZUXIMUYFUYHMZUYIUXIUY
      JUXSUXKUXCUYJUXRUXJUKUYJFEUWSUWTUYEUYHUSUTVAUYFUYGUXQVBVCUYJFUXPUXHUYFUYG
      UXQVDUYFUYGUXPUXHLZUXQUYFUYGMZUXOUXGLZAUXCQUYKUYLUYMAUXCUYLABVEZMZUXOUXGF
      OZUXGUYOCEVFUEKZUXDEFOZKUXEWLKUXOUYPRUWSUYQUWTUYEUYGUYNCEVGZVHUYOUXDFUYRU
      YLUXCFUXDUYGUXCFLZUYFUYGUYTUXCUKKZUXCFVIVJVLVMUYOUWTUYRFRZUWSUWTUYEUYGUYN
      VNFEVOZVPVQUYOUXEUXAUYEUYGUYNUSVRDCUXDUXEEFHVSVTUXGFWAWBWCAUXCUXOUXGWDSWE
      WFWMWGWHWIWJUXAUXMAUAUGZUXDUBUGZUXNNZUIZFRZUAUXSULZUBPQZUXBUXAUXMVUIUBPUX
      AVUEPKZMZUXMFAUXCUXDVUEWKWNNZUXFNZUIZLZBUXKULZVUIVULVUMPKUXMVUQWOVULVUEUX
      AVUKWPWQUXLVUQGVUMPUXEVUMRZUXIVUPBUXKVURUXHVUOFVURAUXCUXGVUNUXEVUMUXDUXFW
      RWSWTXAXBSVULVUPVUIBUXKVULUYIVUPMZMZVUNFOZTXCZAUXCXEZFUCUGZXDZIUGZVVDUEZV
      VFVUMUXFNZKZIVVCQZMZUCXPZVUIVUTVVCUKKZJUGZVVHKZJFULZIVVCQVVLVUTVUAVVCUXCL
      VVMUYIVUAVULVUPUYIUXCELZVUAUXCEVIZXFXGZVVBAUXCXHZUXCVVCXIXJVVPIVVCVVFVVCK
      ZIBVEZVVPVVBVVPAVVFUXCAIXQZVVBVVOJFXEZTXCVVPVWCVVAVWDTVWCVVAFVVHOZVWDVWCV
      VAVVHFOZVWEVWCVUNVVHFUXDVVFVUMUXFXKZXLZVVHFXMXNJFVVHXOXNXRVVOJFXSXTYHXFYA
      VVOVVIIJVVCFUCVVNVVGVVHUUAUUBXJVUTVVKVUIUCVUTVVKVVDUUCZUXCLZVWIFVVDXDZVVB
      UXDVVDUUDZVUNYBZKZWOZAUXCQZUUEZVUIVUTVUAVVKVWQWOVVSVUAVVKVWQVUAVVKMZVWJVW
      KVWPVWRVWIVVCUXCVVEVWIVVCRVUAVVJVVCFVVDUUFXGZVVTWBVWRVWKVVEVUAVVEVVJVBVWR
      VWIVVCFVVDVWSUUGYCVWRVVFVWLVVHYBZKZIVVCQZVWPVWRVXBVVJVUAVVEVVJVDVVEVXBVVJ
      VKVUAVVJVVEVXAVVIIVVCVVEVXAVWAVVIVVEVVDVVCYDVXAVWAVVIMVKVVCFVVDUUHVVCVVFV
      VHVVDYESUUIUUJXGYCVVBVXAVWNIAUXCIAXQZVVFUXDVWTVWMVXCYIVXCVVHVUNVWLVVFUXDV
      UMUXFXKYFYGUUKVPUULWGSVUTVWQVUIVUTVWQMZVVDUVDZUXSKZAVXEVUFUIZFRZVUIVXDVXE
      FLVXEUKKZVXFVXDVWIFVVDVUTVWJVWKVWPUUMZUUNZVXDVVDUKKZVXIVXDVVDVWIYDZVWIUKK
      ZVXLVXDVWIFVVDVXJUUOZVXDVUAVWJVXNVUTVUAVWQVVSYJVUTVWJVWKVWPUUPZUXCVWIXIYK
      VWIVVDUUQYKVVDUURSVXEFVIUUSVXDVXGJVXEVVNVUEUXNNZUIZFAJVXEVUFVXQUXDVVNVUEU
      XNXKYLVXDVXRFVXDVXQFLZJVXEQVXRFLVXDVXSJVXEVXDVVNVXEKZMZDFVFUEKZVVNFKVUEWL
      KZVXSVYAUYCVYBUXAUYCVUKVUSVWQVXTUYDVHDFVGSVXDVXEFVVNVXKVMVUKVYCUXAVUSVWQV
      XTVUEUUTZYMDVVNVUEFUVAVTWCJVXEVXQFYNYOVXDFIUXCVWFUIZVXRVXDVYEIUXCVVHUIZFO
      ZFIUXCFVVHUVBVXDFVYFLVYGFRVXDFVUOVYFVULUYIVUPVWQUVCAIUXCVUNVVHVWGYLUVEFVY
      FVOVPYPVXDVWFVXRLZIUXCQVYEVXRLVXDVYHIUXCVXDVWBMZVYHVWFTVWFTRZVYHWOVYIVYJV
      YHTVXRLVXRUVFVWFTVXRUVGUVHUVIVYIVWFTXCZVXAVYHVXDVWPVWBVYKVXAWOZVUTVWJVWKV
      WPUVJVWOVYLAVVFUXCVWCVVBVYKVWNVXAVWCVVAVWFTVWHXRVWCUXDVVFVWMVWTVWCYIVWCVU
      NVVHVWLVWGYFYGUVKUVLYQVYIVXAVYHVXDVXAVYHVWBVXDVXAMZVWFVVGVUEUXNNZVXRVYMVW
      FVVGVUEUXFNZFOZVYNVYMVVHVYOFVYMUYQVVFEKVUEUVOKVVIVVHVYOLUWSUYQUWTVUKVUSVW
      QVXAUYSUVMZVXDVWTEVVFVXDVWTVWIEVVDVVHUVNZVXDVWIUXCEVXPVUTVVQVWQUYIVVQVULV
      UPUYIVVQVUAVVRVJXGYJYSUVPVMVYMVUEUXAVUKVUSVWQVXAVNUVQVXDVXMVXAVVIVXOVXMVX
      AVVFVWIKZVVIVWIVVFVVHVVDYEUVRYQVUECEVVFVVGUVSUVTVAVYMUYQVVGUYRKVYCVYNVYPR
      VYQVYMVVGFUYRVXDVWKVYSVVGFKVXAVXJVWTVWIVVFVYRUWAZVWIFVVFVVDUWBYRVYMUWTVUB
      UWSUWTVUKVUSVWQVXAUWEVUCVPVQVUKVYCUXAVUSVWQVXAVYDYMDCVVGVUEEFHVSVTUWCVYMV
      VGVXEKZVYNVXRLVXDVXMVYSWUAVXAVXOVYTVWIVVFVVDUWDYRJVXEVXQVVGVYNVVNVVGVUEUX
      NXKUWFSYSUWGWGYTUWHWCIUXCVWFVXRYNYOWFUWNYPVUHVXHUAVXEUXSVUDVXERVUGVXGFAVU
      DVXEVUFUWIUWJUWKYKWGYTUWLUWOUWMYTUWPUXAUYCUXBVUJVKUYDUXBUYCVUJAUADFUBUQUR
      SUWQUWR $.

    $( Condition for a subset of a metric space to be totally bounded.
       (Contributed by Jeff Madsen, 2-Sep-2009.)  (Proof shortened by Mario
       Carneiro, 12-Sep-2015.) $)
    sstotbnd $p |- ( ( M e. ( Met ` X ) /\ Y C_ X ) ->
      ( N e. ( TotBnd ` Y ) <-> A. d e. RR+ E. v e. Fin ( Y C_ U. v /\
        A. b e. v E. x e. X b = ( x ( ball ` M ) d ) ) ) ) $=
      ( vu vf cfv wcel wss wa cv ciun cfn wrex wceq vy cmet ctotbnd cbl cpw cin
      co crp wral cuni sstotbnd2 cmpt crn cab elfpw simprbi mptfi rnfi ad2antrl
      3syl simprr eqid rnmpt wi simplbi ssrexv syl ss2abdv eqsstrid ovex dfiun3
      unieq eqtr4di sseq2d ssabral sseq1 bitr3id anbi12d syl12anc rexlimdvaa wf
      rspcev wex oveq1 eqeq2d ac6sfi adantrl adantl frn wfo simplrl dffn4 sylib
      wfn ffn fofi syl2anc sylanbrc simprrl adantr uniiun iuneq2 eqtrid sseqtrd
      ad2antll eleq2d rexrn eliun 3bitr4g eqrdv sseqtrrd iuneq1 exlimddv impbid
      ralbidv bitrd ) CEUBLMFENOZDFUCLMFAJPZAPZHPZCUDLZUGZQZNZJEUERUFZSZHUHUIFB
      PZUJZNZGPZYBTZAESZGYGUIZOZBRSZHUHUIAJCDEFHIUKXQYFYOHUHXQYFYOXQYDYOJYEXQXR
      YEMZYDOOZAXRYBULZUMZRMZYDYSYLGUNZNZYOYPYTXQYDYPXRRMZYRRMYTYPXRENZUUCXREUO
      ZUPAXRYBUQYRURUTUSXQYPYDVAYQYSYKAXRSZGUNUUAAGXRYBYRYRVBVCYQUUFYLGYPUUFYLV
      DZXQYDYPUUDUUGYPUUDUUCUUEVEYKAXREVFVGUSVHVIYNYDUUBOBYSRYGYSTZYIYDYMUUBUUH
      YHYCFUUHYHYSUJYCYGYSVLAXRYBXSXTYAVJVKVMVNYMYGUUANUUHUUBYLGYGVOYGYSUUAVPVQ
      VRWBVSVTXQYNYFBRXQYGRMZYNOZOZYGEKPZWAZYJYJUULLZXTYAUGZTZGYGUIZOZYFKUUJUUR
      KWCZXQUUIYMUUSYIYKUUPGAYGEKXSUUNTZYBUUOYJXSUUNXTYAWDZWEWFWGWHUUKUUROZUULU
      MZYEMZFAUVCYBQZNZYFUVBUVCENZUVCRMZUVDUUMUVGUUKUUQYGEUULWIUSUVBUUIYGUVCUUL
      WJZUVHXQUUIYNUURWKUVBUULYGWNZUVIUUMUVJUUKUUQYGEUULWOUSZYGUULWLWMYGUVCUULW
      PWQUVCEUOWRUVBFGYGUUOQZUVEUVBFYHUVLUUKYIUURXQUUIYIYMWSWTUUQYHUVLTUUKUUMUU
      QYHGYGYJQUVLGYGXAGYGYJUUOXBXCXEXDUVBUVJUVEUVLTUVKUVJUAUVEUVLUVJUAPZYBMZAU
      VCSUVMUUOMZGYGSUVMUVEMUVMUVLMUVNUVOAGYGUULUUTYBUUOUVMUVAXFXGAUVMUVCYBXHGU
      VMYGUUOXHXIXJVGXKYDUVFJUVCYEXRUVCTYCUVEFAXRUVCYBXLVNWBWQXMVTXNXOXP $.

    $( Use a net that is not necessarily finite, but for which only finitely
       many balls meet the subset.  (Contributed by Mario Carneiro,
       14-Sep-2015.) $)
    sstotbnd3 $p |- ( ( M e. ( Met ` X ) /\ Y C_ X ) ->
      ( N e. ( TotBnd ` Y ) <-> A. d e. RR+ E. v e. ~P X
        ( Y C_ U_ x e. v ( x ( ball ` M ) d ) /\
          { x e. v | ( ( x ( ball ` M ) d ) i^i Y ) =/= (/) } e. Fin ) ) ) $=
      ( vy vw cfv wcel wss wa cv ciun cfn wrex crp wral vz cmet ctotbnd cbl cin
      co c0 wne crab cpw sstotbnd2 elin rabfi anim2i sylbi ancoms sylib reximi2
      ralimi biimtrdi ssrab2 elpwi ad2antlr sstrid simprr elfpw sylanbrc inelcm
      an12 ssel2 eliun expcom ancrd reximdv impcom sylancom wceq eleq2d rexrab2
      oveq1 bitri sylibr ssrdv ad2antrl iuneq1 sseq2d rspcev syl2anc rexlimdva2
      ex ralimdv sylibrd impbid ) CEUBKLFEMNZDFUCKLZFABOZAOZGOZCUDKZUFZPZMZWTFU
      EUGUHZAWPUIZQLZNZBEUJZRZGSTZWNWOXBBXGQUEZRZGSTXIABCDEFGHUKXKXHGSXBXFBXJXG
      WPXJLZXBNXBWPXGLZXENZNZXMXFNXBXLXOXLXNXBXLXMWPQLZNXNWPXGQULXPXEXMXCAWPUMU
      NUOUNUPXBXMXEVIUQURUSUTWNXIFIJOZIOZWRWSUFZPZMZJXJRZGSTWOWNXHYBGSWNXFYBBXG
      WNXMNZXFNZXDXJLZFIXDXSPZMZYBYDXDEMXEYEYDXDWPEXCAWPVAXMWPEMWNXFWPEVBVCVDYC
      XBXEVEXDEVFVGXBYGYCXEXBUAFYFXBUAOZFLZYHYFLZXBYINZXCYHWTLZNZAWPRZYJXBYIYLA
      WPRZYNYKYHXALYOFXAYHVJAYHWPWTVKUQYIYOYNYIYLYMAWPYIYLXCYLYIXCYHWTFVHVLVMVN
      VOVPYJYHXSLZIXDRYNIYHXDXSVKXCYPYLIAWPXRWQVQXSWTYHXRWQWRWSVTVRVSWAWBWJWCWD
      YAYGJXDXJXQXDVQXTYFFIXQXDXSWEWFWGWHWIWKIJCDEFGHUKWLWM $.
  $}

  ${
    $d b d v x M $.  $d b d v x S $.  $d b d v x X $.
    $( A subset of a totally bounded metric space is totally bounded.
       (Contributed by Jeff Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro,
       12-Sep-2015.) $)
    totbndss $p |- ( ( M e. ( TotBnd ` X ) /\ S C_ X ) ->
        ( M |` ( S X. S ) ) e. ( TotBnd ` S ) ) $=
      ( vv vb vx vd ctotbnd cfv wcel wss wa cxp cres cv wceq wrex wral cfn crp
      cuni co cmet istotbnd simprbi sseq2 biimprcd anim1d reximdv ralimdv mpan9
      cbl wb totbndmet eqid sstotbnd sylan mpbird ) BCHIJZACKZLBAAMNZAHIJZADOZU
      AZKZEOFOGOBULIUBPFCQEVCRZLZDSQZGTRZUSVDCPZVFLZDSQZGTRZUTVIUSBCUCIJZVMFDBC
      EGUDUEUTVLVHGTUTVKVGDSUTVJVEVFVJVEUTVDCAUFUGUHUIUJUKUSVNUTVBVIUMBCUNFDBVA
      CAEGVAUOUPUQUR $.
  $}

  ${
    $d s v x y M $.  $d r v x y N $.  $d r v x y ph $.  $d r s v x y X $.
    $d s v x y R $.
    equivtotbnd.1 $e |- ( ph -> M e. ( TotBnd ` X ) ) $.
    equivtotbnd.2 $e |- ( ph -> N e. ( Met ` X ) ) $.
    equivtotbnd.3 $e |- ( ph -> R e. RR+ ) $.
    equivtotbnd.4 $e |- ( ( ph /\ ( x e. X /\ y e. X ) ) ->
      ( x N y ) <_ ( R x. ( x M y ) ) ) $.
    $( If the metric ` M ` is "strongly finer" than ` N ` (meaning that there
       is a positive real constant ` R ` such that
       ` N ( x , y ) <_ R x. M ( x , y ) ` ), then total boundedness of ` M `
       implies total boundedness of ` N ` .  (Using this theorem twice in each
       direction states that if two metrics are strongly equivalent, then one
       is totally bounded iff the other is.)  (Contributed by Mario Carneiro,
       14-Sep-2015.) $)
    equivtotbnd $p |- ( ph -> N e. ( TotBnd ` X ) ) $=
      ( vv vr vs cfv wcel cv co crp wss cmet cbl ciun wceq cpw cfn wrex ctotbnd
      cin wral wa cdiv simpr adantr rpdivcld istotbnd3 simprbi syl oveq2 eqeq1d
      iuneq2d rexbidv rspcv sylc elfpw simplbi adantl sselda metss2lem anass1rs
      cmopn adantlr syldan ralrimiva ss2iun sseq1 syl5ibcom cxmet cxr ad3antrrr
      eqid metxmet simpllr rpxrd blssm syl3anc sylibr jctild imbitrrdi reximdva
      iunss eqss mpd sylanbrc ) AFGUAOZPZBLQZBQZMQZFUBORZUCZGUDZLGUEUFUIZUGZMSU
      JFGUHOZPIAXDMSAWSSPZUKZBWQWRWSDULRZEUBOZRZUCZGUDZLXCUGZXDXGXHSPBWQWRNQZXI
      RZUCZGUDZLXCUGZNSUJZXMXGWSDAXFUMADSPXFJUNUOXGEXEPZXSAXTXFHUNXTEWOPZXSBLEG
      NUPZUQURXRXMNXHSXNXHUDZXQXLLXCYCXPXKGYCBWQXOXJXNXHWRXIUSVAUTVBVCVDXGXLXBL
      XCXGWQXCPZUKZXLXAGTZGXATZUKXBYEXLYGYFYEXKXATZXLYGYEXJWTTZBWQUJYHYEYIBWQYE
      WRWQPZWRGPZYIYEWQGWRYDWQGTZXGYDYLWQUFPWQGVEVFVGVHZXGYKYIYDAYKXFYIABCFEDWS
      FVKOZEVKOZGYNWAYOWAIAXTYAHXTYAXSYBVFURJKVIVJVLVMVNBWQXJWTVOURXKGXAVPVQYEW
      TGTZBWQUJYFYEYPBWQYEYJUKZFGVROPZYKWSVSPYPYQWPYRAWPXFYDYJIVTFGWBURYMYQWSAX
      FYDYJWCWDFWRWSGWEWFVNBWQWTGWKWGWHXAGWLWIWJWMVNBLFGMUPWN $.
  $}

  ${
    $d m r x y $.
    $( Define the class of bounded metrics.  A metric space is bounded iff it
       can be covered by a single ball.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    df-bnd $a |- Bnd = ( x e. _V |-> { m e. ( Met ` x ) |
      A. y e. x E. r e. RR+ x = ( y ( ball ` m ) r ) } ) $.
  $}

  ${
    $d d m r s x y z M $.  $d d r y N $.  $d d r y P $.  $d d m r s x y z X $.
    $d r x R $.  $d r x S $.  $d d r x y Y $.
    $( The predicate "is a bounded metric space".  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Revised by Mario Carneiro, 12-Sep-2015.) $)
    isbnd $p |- ( M e. ( Bnd ` X ) <-> ( M e. ( Met ` X ) /\
        A. x e. X E. r e. RR+ X = ( x ( ball ` M ) r ) ) ) $=
      ( vm vy cbnd cfv wcel cvv cmet cv cbl co wceq crp wrex wral elfvex crab
      adantr fveq2 eqeq1 rexbidv raleqbi1dv rabeqbidv df-bnd rabex fvmpt eleq2d
      wa fvex oveqd eqeq2d ralbidv elrab bitrdi pm5.21nii ) BCGHZIZCJIZBCKHZIZC
      ALZDLZBMHZNZOZDPQZACRZUKZBCGSVCVAVJBCKSUAVAUTBCVDVEELZMHZNZOZDPQZACRZEVBT
      ZIVKVAUSVRBFCFLZVNOZDPQZAVSRZEVSKHZTVRJGVSCOZWBVQEWCVBVSCKUBWAVPAVSCWDVTV
      ODPVSCVNUCUDUEUFFAEDUGVQEVBCKULUHUIUJVQVJEBVBVLBOZVPVIACWEVOVHDPWEVNVGCWE
      VMVFVDVEVLBMUBUMUNUDUOUPUQUR $.

    $( A bounded metric space is a metric space.  (Contributed by Mario
       Carneiro, 16-Sep-2015.) $)
    bndmet $p |- ( M e. ( Bnd ` X ) -> M e. ( Met ` X ) ) $=
      ( vx vy cbnd cfv wcel cmet cv cbl co wceq crp wrex wral isbnd simplbi ) A
      BEFGABHFGBCIDIAJFKLDMNCBOCABDPQ $.

    $( A "bounded extended metric" (meaning that it satisfies the same
       condition as a bounded metric, but with "metric" replaced with "extended
       metric") is a metric and thus is bounded in the conventional sense.
       (Contributed by Mario Carneiro, 12-Sep-2015.) $)
    isbndx $p |- ( M e. ( Bnd ` X ) <-> ( M e. ( *Met ` X ) /\
        A. x e. X E. r e. RR+ X = ( x ( ball ` M ) r ) ) ) $=
      ( vy cbnd cfv wcel cmet cv cbl co crp wral wa cr wf cxr vex sylanbrc wceq
      wrex cxmet isbnd metxmet cxp simpr wfn xmetf ffn 3syl ccnv wbr w3a simprr
      cima cec wss rpxr eqid blssec 3expa sylan2 adantrr eqsstrd sselda elec wb
      sylib xmeterval ad3antrrr mpbid simp3d ralrimiva rexlimdvaa impcom ismet2
      ralimdva ffnov ex impbid2 pm5.32ri bitri ) BCFGHBCIGHZCAJZDJZBKGLZUAZDMUB
      ZACNZOBCUCGHZWJOABCDUDWJWDWKWJWDWKBCUEWJWKWDWJWKOZWKCCUFZPBQZWDWJWKUGZWLB
      WMUHZWEEJZBLPHZECNZACNZWNWLWKWMRBQWPWOBCUIWMRBUJUKWKWJWTWKWIWSACWKWECHZOZ
      WHWSDMXBWFMHZWHOZOZWRECXEWQCHZOZXAXFWRXGWEWQBULPUPZUMZXAXFWRUNZXGWQWEXHUQ
      ZHXIXECXKWQXECWGXKXBXCWHUOXBXCWGXKURZWHXCXBWFRHZXLWFUSWKXAXMXLBWEXHWFCXHU
      TZVAVBVCVDVEVFWQWEXHESASVGVIWKXIXJVHXAXDXFWEWQBXHCXNVJVKVLVMVNVOVRVPAECCP
      BVSTBCVQTVTWAWBWC $.

    $( The predicate "is a bounded metric space".  Uses a single point instead
       of an arbitrary point in the space.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    isbnd2 $p |- ( ( M e. ( Bnd ` X ) /\ X =/= (/) ) <-> ( M e. ( *Met ` X ) /\
                E. x e. X E. r e. RR+ X = ( x ( ball ` M ) r ) ) ) $=
      ( vy vs cfv wcel wa cv co wceq crp wrex eqeq2d c2 wss wi cr sylan2 c0 wne
      cbnd cxmet cbl wral isbndx anbi1i anass r19.2z oveq1 oveq2 cbvrex2vw cmul
      ancoms 2rp rpmulcl mpan ad2antll ad2antrr cdiv cc0 rpcn 2cnd 2ne0 a1i w3a
      cc divcan3 eqcomd syl3anc oveq2d biimpd adantr imp simpr biimpac 2re rpre
      remulcl sylancr blhalf expr anasss anassrs eqsstrd syldan adantl cxr rpxr
      eleq2 blssm syl3an3 3expa an32s eqssd rspceeqv syl2anc ralrimdva biimtrid
      ex rexlimdvva rexn0 jcad impbid2 pm5.32i 3bitri ) BCUCGHZCUAUBZIBCUDGHZCA
      JZDJZBUEGZKZLZDMNZACUFZIZXIIXJXQXIIZIXJXPACNZIXHXRXIABCDUGUHXJXQXIUIXJXSX
      TXJXSXTXIXQXTXPACUJUOXJXTXQXIXTCEJZFJZXMKZLZFMNECNXJXQXOYDCYAXLXMKZLADEFC
      MXKYALXNYECXKYAXLXMUKOXLYBLYEYCCXLYBYAXMULOUMXJYDXQEFCMXJYACHZYBMHZIZIZYD
      XPACYIXKCHZIZYDXPYKYDIZPYBUNKZMHZCXKYMXMKZLXPYIYNYJYDYGYNXJYFPMHYGYNUPPYB
      UQURZUSUTYLCYOYKYDCYAYMPVAKZXMKZLZCYOQYKYDYSYIYDYSRZYJYGYTXJYFYGYDYSYGYCY
      RCYGYBYQYAXMYGYBVHHZPVHHZPVBUBZYBYQLYBVCYGVDUUCYGVEVFUUAUUBUUCVGYQYBYBPVI
      VJVKVLOVMUSVNVOYKYSICYRYOYKYSVPYIYJYSYRYOQZYJYSIYIXKYRHZUUDYSYJUUECYRXKWK
      VQYIUUEUUDXJYFYGUUEUUDRZYGXJYFIZYMSHZUUFYGPSHYBSHUUHVRYBVSPYBVTWAUUGUUHUU
      EUUDYMBCYAXKWBWCTWDVOTWEWFWGYKYOCQZYDXJYJYHUUIYHXJYJIYNUUIYGYNYFYPWHXJYJY
      NUUIYNXJYJYMWIHUUIYMWJBXKYMCWLWMWNTWOVNWPDYMMXNYOCXLYMXKXMULWQWRXAWSXBWTX
      TXIRXJXPACXCVFXDXEXFXG $.

    $( A metric space is bounded iff the metric function maps to some bounded
       real interval.  (Contributed by Mario Carneiro, 13-Sep-2015.) $)
    isbnd3 $p |- ( M e. ( Bnd ` X ) <-> ( M e. ( Met ` X ) /\
        E. x e. RR M : ( X X. X ) --> ( 0 [,] x ) ) ) $=
      ( vy vr vz wcel cc0 co cr wa c0 wceq wral syl adantr sylancr crp cle wbr
      cbnd cfv cmet cxp cv cicc wrex bndmet wne 0re ne0ii wfn crn wss metf ffnd
      wf ad2antrr cdm fdmd xpeq2 xp0 eqtrdi sylan9eq dm0rn0 sylib eqsstrdi df-f
      0ss sylanbrc ralrimiva r19.2z cbl cxmet isbnd2 simprbi wi c2 cmul simprlr
      2re rpred remulcl simpll simprl simprr metcl syl3anc metge0 caddc simprll
      readdcld mettri2 syl13anc clt simplrr eleqtrd metxmet rpxr ad2antlr elbl2
      cxr wb syl22anc mpbid lt2addd recnd 2timesd breqtrrd lelttrd ltled elicc2
      w3a mpbir3and ralrimivva ffnov oveq2 feq3d rspcev syl2anc expr rexlimdvva
      mpd pm2.61dane jca c1 simpllr simpr met0 simplr fovcdmd eqbrtrrd ge0p1rpd
      simp3d crab fovcdm 3expa adantlll simp1d peano2re ltp1d rexrd blval isbnd
      rabid2 sylibr eqtr4d rspceeqv r19.29an impbii ) BCUAUBGZBCUCUBGZCCUDZHAUE
      ZUFIZBUQZAJUGZKUUKUULUUQBCUHZUUKUUQCLUUKCLMZKZJLUIUUPAJNUUQHJUJUKUUTUUPAJ
      UUTUUNJGZKZBUUMULZBUMZUUOUNUUPUUKUVCUUSUVAUUKUULUVCUURUULUUMJBBCUOZUPZOUR
      UVBUVDLUUOUVBBUSZLMZUVDLMUUTUVHUVAUUKUUSUVGUUMLUUKUUMJBUUKUULUUMJBUQUURUV
      EOUTUUSUUMCLUDLCLCVACVBVCVDPBVEVFUUOVIVGUUMUUOBVHVJVKUUPAJVLQUUKCLUIZKZCD
      UEZEUEZBVMUBZIZMZERUGZDCUGZUUQUVJBCVNUBGZUVQDBCEVOVPUUKUVQUUQVQZUVIUUKUUL
      UVSUURUULUVOUUQDECRUULUVKCGZUVLRGZKZUVOUUQUULUWBUVOKZKZVRUVLVSIZJGZUUMHUW
      EUFIZBUQZUUQUWDVRJGUVLJGZUWFWAUWDUVLUULUVTUWAUVOVTWBZVRUVLWCQZUWDUVCUUNFU
      EZBIZUWGGZFCNACNUWHUULUVCUWCUVFPUWDUWNAFCCUWDUUNCGZUWLCGZKZKZUWNUWMJGZHUW
      MSTZUWMUWESTZUWRUULUWOUWPUWSUULUWCUWQWDZUWDUWOUWPWEZUWDUWOUWPWFZUUNUWLBCW
      GWHZUWRUULUWOUWPUWTUXBUXCUXDUUNUWLBCWIWHUWRUWMUWEUXEUWDUWFUWQUWKPZUWRUWMU
      VKUUNBIZUVKUWLBIZWJIZUWEUXEUWRUXGUXHUWRUULUVTUWOUXGJGUXBUWDUVTUWQUULUVTUW
      AUVOWKPZUXCUVKUUNBCWGWHZUWRUULUVTUWPUXHJGZUXBUXJUXDUVKUWLBCWGWHZWLUXFUWRU
      ULUVTUWOUWPUWMUXISTUXBUXJUXCUXDUUNUWLUVKBCWMWNUWRUXIUVLUVLWJIUWEWOUWRUXGU
      XHUVLUVLUXKUXMUWDUWIUWQUWJPZUXNUWRUUNUVNGZUXGUVLWOTZUWRUUNCUVNUXCUULUWBUV
      OUWQWPZWQUWRUVRUVLXBGZUVTUWOUXOUXPXCUWRUULUVRUXBBCWRZOZUWCUXRUULUWQUWAUXR
      UVTUVOUVLWSWTWTZUXJUXCUUNBUVKUVLCXAXDXEUWRUWLUVNGZUXHUVLWOTZUWRUWLCUVNUXD
      UXQWQUWRUVRUXRUVTUWPUYBUYCXCUXTUYAUXJUXDUWLBUVKUVLCXAXDXEXFUWRUVLUWRUVLUX
      NXGXHXIXJXKUWRHJGZUWFUWNUWSUWTUXAXMXCUJUXFHUWEUWMXLQXNXOAFCCUWGBXPVJUUPUW
      HAUWEJUUNUWEMUUOUWGBUUMUUNUWEHUFXQXRXSXTYAYBOPYCYDYEUULUUPUUKAJUULUVAKZUU
      PKZUULUVPDCNUUKUULUVAUUPWDZUYFUVPDCUYFUVTKZUUNYFWJIZRGCUVKUYIUVMIZMUVPUYH
      UUNUULUVAUUPUVTYGZUYHUVKUVKBIZHUUNSUYHUULUVTUYLHMUYFUULUVTUYGPZUYFUVTYHZU
      VKBCYIXTUYHUYLJGZHUYLSTZUYLUUNSTZUYHUYLUUOGZUYOUYPUYQXMZUYHUVKUVKUUOCCBUY
      EUUPUVTYJUYNUYNYKUYHUYDUVAUYRUYSXCUJUYKHUUNUYLXLQXEYNYLYMUYHCUXHUYIWOTZFC
      YOZUYJUYHUYTFCNCVUAMUYHUYTFCUYHUWPKZUXHUUNUYIVUBUXLHUXHSTZUXHUUNSTZVUBUXH
      UUOGZUXLVUCVUDXMZUUPUVTUWPVUEUYEUUPUVTUWPVUEUVKUWLUUOCCBYPYQYRUYHVUEVUFXC
      ZUWPUYHUYDUVAVUGUJUYKHUUNUXHXLQPXEZYSUYHUVAUWPUYKPZUYHUYIJGZUWPUYHUVAVUJU
      YKUUNYTOZPVUBUXLVUCVUDVUHYNVUBUUNVUIUUAXJVKUYTFCUUEUUFUYHUVRUVTUYIXBGUYJV
      UAMUYHUULUVRUYMUXSOUYNUYHUYIVUKUUBFBUVKUYICUUCWHUUGEUYIRUVNUYJCUVLUYIUVKU
      VMXQUUHXTVKDBCEUUDVJUUIUUJ $.

    $( A metric space is bounded iff the metric function maps to some bounded
       real interval.  (Contributed by Mario Carneiro, 22-Sep-2015.) $)
    isbnd3b $p |- ( M e. ( Bnd ` X ) <-> ( M e. ( Met ` X ) /\
        E. x e. RR A. y e. X A. z e. X ( y M z ) <_ x ) ) $=
      ( cfv wcel cc0 cv co wf cr wrex wa cle wbr wral wb 3expb adantlr cbnd cxp
      cmet cicc isbnd3 wfn metf adantr ffnov baib 3syl 0red simplr metcl metge0
      ffn w3a elicc2 df-3an bitrdi baibd syl22anc 2ralbidva bitrd pm5.32i bitri
      rexbidva ) DEUAFGDEUCFGZEEUBZHAIZUDJZDKZALMZNVHBIZCIZDJZVJOPZCEQBEQZALMZN
      ADEUEVHVMVSVHVLVRALVHVJLGZNZVLVPVKGZCEQBEQZVRWAVILDKZDVIUFZVLWCRVHWDVTDEU
      GUHVILDUPVLWEWCBCEEVKDUIUJUKWAWBVQBCEEWAVNEGZVOEGZNZNZHLGZVTVPLGZHVPOPZWB
      VQRWIULVHVTWHUMVHWHWKVTVHWFWGWKVNVODEUNSTVHWHWLVTVHWFWGWLVNVODEUOSTWJVTNZ
      WBWKWLNZVQWMWBWKWLVQUQWNVQNHVJVPURWKWLVQUSUTVAVBVCVDVGVEVF $.

    $( A subset of a bounded metric space is bounded.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    bndss $p |- ( ( M e. ( Bnd ` X ) /\ S C_ X ) ->
        ( M |` ( S X. S ) ) e. ( Bnd ` S ) ) $=
      ( vy vr vx cmet cfv wcel cv cbl co wceq crp wrex wral wa cbnd cin an32s
      wss cxp metres2 adantlr wi ssel2 ancoms oveq1 eqeq2d rexbidv rspcva sylan
      cres adantlll dfss biimpi incom ineq1 sylan9eq adantll eqid blssp anassrs
      eqtrdi an4s adantr eqtr4d reximdva imp syldan ralrimiva jca isbnd 3imtr4i
      ex anbi1i ) BCGHIZCDJZEJZBKHZLZMZENOZDCPZQZACUAZQZBAAUBUMZAGHIZAFJZVSWHKH
      LZMZENOZFAPZQBCRHIZWFQWHARHIWGWIWNVQWFWIWDBACUCUDWGWMFAWEWJAIZWFWMWEWPQWF
      WMVQWPWDWFWMUEVQWPQZWDQWFWMWQWFWDWMWQWFQZWDCWJVSVTLZMZENOZWMWPWFWDXAVQWPW
      FQWJCIZWDXAWFWPXBACWJUFUGWCXADWJCVRWJMZWBWTENXCWAWSCVRWJVSVTUHUIUJUKULUNW
      RXAWMWRWTWLENWRVSNIZQZWTWLXEWTQAWSASZWKWRWTAXFMZXDWFWTXGWQWFWTACASZXFWFAA
      CSZXHWFAXIMACUOUPACUQVDCWSAURUSUTUDXEWKXFMZWTWQWFXDXJVQWFWPXDXJVSABWHCWJW
      HVAVBVEVCVFVGVOVHVIVJTVOTVITVKVLWOWEWFDBCEVMVPFWHAEVMVN $.

    $( A ball is bounded.  (Contributed by Jeff Madsen, 2-Sep-2009.)  (Proof
       shortened by Mario Carneiro, 15-Jan-2014.) $)
    blbnd $p |- ( ( M e. ( *Met ` X ) /\ Y e. X /\ R e. RR ) ->
          ( M |` ( ( Y ( ball ` M ) R ) X. ( Y ( ball ` M ) R ) ) ) e.
            ( Bnd ` ( Y ( ball ` M ) R ) ) ) $=
      ( vx vr cxmet cfv wcel cbl co c0 wceq wa crp wrex syl3an3 adantr syl3anc
      cv cr w3a cxp cres cbnd wral wss simp1 rexr blssm xmetres2 syl2anc adantl
      cxr rzal isbndx sylanbrc wne simpl2 simpl3 cc0 clt wbr xbln0 biimpa elrpd
      blcntr cin elind rexrd eqid blres inidm eqtr2di rspceov isbnd2 pm2.61dane
      wb simpld ) BCGHIZDCIZAUAIZUBZBDABJHKZWDUCUDZWDUEHIZWDLWCWDLMZNWEWDGHIZWD
      ETFTWEJHZKMFOPZEWDUFZWFWCWHWGWCVTWDCUGZWHVTWAWBUHZWBVTWAAUNIZWLAUIZBDACUJ
      QBWDCUKULZRWGWKWCWJEWDUOUMEWEWDFUPUQWCWDLURZNZWFWQWRWHWJEWDPZWFWQNWCWHWQW
      PRWRDWDIZAOIZWDDAWIKZMWSWRVTWAXAWTWCVTWQWMRZVTWAWBWQUSZWRAVTWAWBWQUTZWCWQ
      VAAVBVCZWBVTWAWNWQXFVRWOBDACVDQVEVFZBDACVGSZXGWRXBWDWDVHZWDWRVTDCWDVHIWNX
      BXIMXCWRCWDDXDXHVIWRAXEVJWEBDACWDWEVKVLSWDVMVNEFWDODAWDWIVOSEWEWDFVPUQVSV
      Q $.

    ssbnd.2 $e |- N = ( M |` ( Y X. Y ) ) $.
    $( A subset of a metric space is bounded iff it is contained in a ball
       around ` P ` , for any ` P ` in the larger space.  (Contributed by Mario
       Carneiro, 14-Sep-2015.) $)
    ssbnd $p |- ( ( M e. ( Met ` X ) /\ P e. X ) ->
      ( N e. ( Bnd ` Y ) <-> E. d e. RR Y C_ ( P ( ball ` M ) d ) ) ) $=
      ( vy vr cfv wcel wa cv co wss cr wrex c0 wceq cdm cmet cbl wi wne cc0 0re
      cbnd ne0ii 0ss sseq1 mpbiri ralrimivw r19.2z sylancr a1i cxmet crp isbnd2
      wral caddc simplll cxp cin cres dmeqi dmres eqtri cxr xmetf eqtr3id dfss2
      fdmd sylibr ad2antlr metf ad3antrrr sseqtrd dmss syl dmxpid simprl sseldd
      3sstr3g simpllr metcl syl3anc ad2antll readdcld metxmet elind blres inss1
      rpre rpxr cmin cle wbr leidd recnd pncand breqtrrd blss2 syl33anc eqsstrd
      sstrid oveq2 sseq2d rspcev syl2anc rexbidv syl5ibrcom rexlimdvva biimtrid
      expimpd expdimp pm2.61dne ex simprr xpss12 resabs1d eqtr4di blbnd syl3an1
      3expa adantrr bndss eqeltrrd rexlimdvaa impbid ) BDUAJKZADKZLZCEUGJZKZEAF
      MZBUBJZNZOZFPQZYLYNYSYLYNLZYSERERSZYSUCYTUUAPRUDYRFPUSYSUEPUFUHUUAYRFPUUA
      YRRYQOYQUIERYQUJUKULYRFPUMUNUOYLYNERUDZYSYNUUBLCEUPJKZEHMZIMZCUBJNZSZIUQQ
      HEQZLYLYSHCEIURYLUUCUUHYSYLUUCLZUUGYSHIEUQUUIUUDEKZUUEUQKZLZLZYSUUGUUFYQO
      ZFPQZUUMUUDABNZUUEUTNZPKZUUFAUUQYPNZOZUUOUUMUUPUUEUUMYJUUDDKZYKUUPPKYJYKU
      UCUULVAZUUMEDUUDUUMEEVBZTZDDVBZTZEDUUMUVCUVEOUVDUVFOUUMUVCBTZUVEUUCUVCUVG
      OZYLUULUUCUVCUVGVCZUVCSUVHUUCUVICTZUVCUVJBUVCVDZTUVICUVKGVEBUVCVFVGUUCUVC
      VHCCEVIVLVJUVCUVGVKVMVNYJUVGUVESYKUUCUULYJUVEPBBDVOVLVPVQUVCUVEVRVSEVTDVT
      WCUUIUUJUUKWAZWBZYJYKUUCUULWDZUUDABDWEWFZUUKUUEPKZUUIUUJUUEWMWGZWHZUUMUUF
      UUDUUEYPNZEVCZUUSUUMBDUPJKZUUDDEVCKUUEVHKZUUFUVTSUUMYJUWAUVBBDWIZVSZUUMDE
      UUDUVMUVLWJUUKUWBUUIUUJUUEWNWGCBUUDUUEDEGWKWFUUMUVTUVSUUSUVSEWLUUMUWAUVAY
      KUVPUURUUPUUQUUEWONZWPWQUVSUUSOUWDUVMUVNUVQUVRUUMUUPUUPUWEWPUUMUUPUVOWRUU
      MUUPUUEUUMUUPUVOWSUUMUUEUVQWSWTXABUUDAUUEUUQDXBXCXEXDUUNUUTFUUQPYOUUQSYQU
      USUUFYOUUQAYPXFXGXHXIUUGYRUUNFPEUUFYQUJXJXKXLXNXMXOXPXQYLYRYNFPYLYOPKZYRL
      LZBYQYQVBZVDZUVCVDZCYMUWGUWJUVKCUWGBUVCUWHUWGYRYRUVCUWHOYLUWFYRXRZUWKEYQE
      YQXSXIXTGYAUWGUWIYQUGJKZYRUWJYMKYLUWFUWLYRYJYKUWFUWLYJUWAYKUWFUWLUWCYOBDA
      YBYCYDYEUWKEUWIYQYFXIYGYHYI $.
  $}

  ${
    $d d v w x y z M $.  $d d v x y z X $.
    $( A totally bounded metric space is bounded.  This theorem fails for
       extended metrics - a bounded extended metric is a metric, but there are
       totally bounded extended metrics that are not metrics (if we were to
       weaken ~ istotbnd to only require that ` M ` be an extended metric).  A
       counterexample is the discrete extended metric (assigning distinct
       points distance ` +oo ` ) on a finite set.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Proof shortened by Mario Carneiro, 12-Sep-2015.) $)
    totbndbnd $p |- ( M e. ( TotBnd ` X ) -> M e. ( Bnd ` X ) ) $=
      ( vx vv vd vz cfv wcel cv c1 co wceq crp wral cr clt wss syl3anc adantr
      c0 vy ctotbnd cmet cbl ciun cpw cfn cin wrex cbnd totbndmet 1rp istotbnd3
      vw simprbi oveq2 iuneq2d eqeq1d rexbidv rspcv mpsyl wa caddc cmpt simplll
      crn csup elfpw simplbi ad2antrl sselda simpllr metcl cc0 cle wbr ge0p1rpd
      metge0 fmpttd frnd wne mptfi rnfi 3syl simplr simprr eleqtrrd ne0i dm0rn0
      cdm ovex eqid dmmpti eqeq1i iuneq1 sylbi 0iun eqtrdi sylbir rpssre sstrdi
      necon3i wor w3a ltso fisupcl mpan sseldd cxmet cmin metxmet ad2antrr 1red
      fimaxre2 syl2anc cvv elrnmpt1 mpan2 adantl suprub syl31anc leaddsub mpbid
      wb blss2 syl33anc ralrimiva nfcv nfmpt1 nfrn nfsup nfov nfss oveq1 sseq1d
      nfv cbvralw sylibr iunss eqsstrrd cxr rpxrd rspceeqv rexlimdvaa ralrimdva
      blssm eqssd isbnd baib sylibrd sylc ) ABUBGHZABUCGHZCDIZCIZJAUDGZKZUEZBLZ
      DBUFUGUHZUIZABUJGHZABUKJMHUULCUUNUUOEIZUUPKZUEZBLZDUUTUIZEMNZUVAULUULUUMU
      VHCDABEUMUOUVGUVAEJMUVCJLZUVFUUSDUUTUVIUVEUURBUVICUUNUVDUUQUVCJUUOUUPUPUQ
      URUSUTVAUUMUVABUAIZUVCUUPKZLEMUIZUABNZUVBUUMUVAUVLUABUUMUVJBHZVBZUUSUVLDU
      UTUVOUUNUUTHZUUSVBZVBZFUUNFIZUVJAKZJVCKZVDZVFZOPVGZMHBUVJUWDUUPKZLUVLUVRU
      WCMUWDUVRUUNMUWBUVRFUUNUWAMUVRUVSUUNHZVBZUVTUWGUUMUVSBHZUVNUVTOHZUUMUVNUV
      QUWFVEZUVRUUNBUVSUVPUUNBQZUVOUUSUVPUWKUUNUGHZUUNBVHZVIVJVKZUUMUVNUVQUWFVL
      ZUVSUVJABVMRZUWGUUMUWHUVNVNUVTVOVPUWJUWNUWOUVSUVJABVRRVQVSVTZUVRUWCUGHZUW
      CTWAZUWCOQZUWDUWCHZUVPUWRUVOUUSUVPUWLUWBUGHUWRUVPUWKUWLUWMUOFUUNUWAWBUWBW
      CWDVJZUVRUVJUURHUURTWAUWSUVRUVJBUURUUMUVNUVQWEZUVOUVPUUSWFZWGUURUVJWHUWCT
      UURTUWCTLUWBWJZTLZUURTLUWBWIUXFUURCTUUQUEZTUXFUUNTLUURUXGLUXEUUNTFUUNUWAU
      WBUVTJVCWKZUWBWLZWMWNCUUNTUUQWOWPCUUQWQWRWSXBWDZUVRUWCMOUWQWTXAZOPXCUWRUW
      SUWTXDUXAXEOUWCPXFXGRZXHZUVRBUWEUVRBUURUWEUXDUVRUUQUWEQZCUUNNZUURUWEQUVRU
      VSJUUPKZUWEQZFUUNNUXOUVRUXQFUUNUWGABXIGHZUWHUVNJOHZUWDOHZUVTUWDJXJKVOVPZU
      XQUVRUXRUWFUUMUXRUVNUVQABXKXLZSUWNUWOUWGXMZUVRUXTUWFUVRUWCOUWDUXKUXLXHSZU
      WGUWAUWDVOVPZUYAUWGUWTUWSUNIUVCVOVPUNUWCNEOUIZUWAUWCHZUYEUVRUWTUWFUXKSZUV
      RUWSUWFUXJSUWGUWTUWRUYFUYHUVRUWRUWFUXBSEUNUWCXNXOUWFUYGUVRUWFUWAXPHUYGUXH
      FUUNUWAUWBXPUXIXQXRXSEUNUWCUWAXTYAUWGUWIUXSUXTUYEUYAYDUWPUYCUYDUVTJUWDYBR
      YCAUVSUVJJUWDBYEYFYGUXNUXQCFUUNFUUQUWEFUUQYHFUVJUWDUUPFUVJYHFUUPYHFUWCOPF
      UWBFUUNUWAYIYJFOYHFPYHYKYLYMUXQCYPUUOUVSLUUQUXPUWEUUOUVSJUUPYNYOYQYRCUUNU
      UQUWEYSYRYTUVRUXRUVNUWDUUAHUWEBQUYBUXCUVRUWDUXMUUBAUVJUWDBUUFRUUGEUWDMUVK
      UWEBUVCUWDUVJUUPUPUUCXOUUDUUEUVBUUMUVMUAABEUUHUUIUUJUUK $.
  $}

  ${
    $d r x y M $.  $d r s x y N $.  $d r x y ph $.  $d r s x y X $.
    $d s x y R $.
    equivbnd.1 $e |- ( ph -> M e. ( Bnd ` X ) ) $.
    equivbnd.2 $e |- ( ph -> N e. ( Met ` X ) ) $.
    equivbnd.3 $e |- ( ph -> R e. RR+ ) $.
    equivbnd.4 $e |- ( ( ph /\ ( x e. X /\ y e. X ) ) ->
      ( x N y ) <_ ( R x. ( x M y ) ) ) $.
    $( If the metric ` M ` is "strongly finer" than ` N ` (meaning that there
       is a positive real constant ` R ` such that
       ` N ( x , y ) <_ R x. M ( x , y ) ` ), then boundedness of ` M ` implies
       boundedness of ` N ` .  (Using this theorem twice in each direction
       states that if two metrics are strongly equivalent, then one is bounded
       iff the other is.)  (Contributed by Mario Carneiro, 14-Sep-2015.) $)
    equivbnd $p |- ( ph -> N e. ( Bnd ` X ) ) $=
      ( vs vr wcel cv co cle wbr wral cr cmet cfv wrex cbnd isbnd3b simprbi syl
      wa cmul rpred remulcl sylan bndmet adantr metcl 3expb simplr crp ad2antrr
      lemul2d adantlr wi remulcld syl3anc mpand sylbid ralimdvva breq2 2ralbidv
      letr wceq rspcev syl6an rexlimdva mpd sylanbrc ) AFGUAUBZNZBOZCOZFPZLOZQR
      ZCGSBGSZLTUCZFGUDUBZNIAVSVTEPZMOZQRZCGSBGSZMTUCZWEAEWFNZWKHWLEVQNZWKMBCEG
      UEUFUGAWJWEMTAWHTNZUHZDWHUIPZTNZWJWAWPQRZCGSBGSZWEADTNZWNWQADJUJZDWHUKULZ
      WOWIWRBCGGWOVSGNZVTGNZUHZUHZWIDWGUIPZWPQRZWRXFWGWHDWOWMXEWGTNZAWMWNAWLWMH
      EGUMUGUNWMXCXDXIVSVTEGUOUPULZAWNXEUQADURNWNXEJUSUTXFWAXGQRZXHWRAXEXKWNKVA
      XFWATNZXGTNWQXKXHUHWRVBWOVRXEXLAVRWNIUNVRXCXDXLVSVTFGUOUPULXFDWGAWTWNXEXA
      USXJVCWOWQXEXBUNWAXGWPVJVDVEVFVGWDWSLWPTWBWPVKWCWRBCGGWBWPWAQVHVIVLVMVNVO
      LBCFGUEVP $.
  $}

  ${
    bnd2lem.1 $e |- D = ( M |` ( Y X. Y ) ) $.
    $( Lemma for ~ equivbnd2 and similar theorems.  (Contributed by Jeff
       Madsen, 16-Sep-2015.) $)
    bnd2lem $p |- ( ( M e. ( Met ` X ) /\ D e. ( Bnd ` Y ) ) -> Y C_ X ) $=
      ( cmet cfv wcel cbnd wa cxp cdm wss cres resss dmss wceq cr metf dmxpid
      eqsstri mp1i wf bndmet fdm 3syl adantl fdmd adantr 3sstr3d syl 3sstr3g )
      BCFGHZADIGHZJZDDKZLZCCKZLZDCUOUPURMUQUSMUOALZBLZUPURABMUTVAMUOABUPNBEBUPO
      UAABPUBUNUTUPQZUMUNADFGHUPRAUCVBADUDADSUPRAUEUFUGUMVAURQUNUMURRBBCSUHUIUJ
      UPURPUKDTCTUL $.
  $}

  ${
    $d x y C $.  $d x y D $.  $d x y ph $.  $d x y R $.  $d x y S $.
    $d x y Y $.
    equivbnd2.1 $e |- ( ph -> M e. ( Met ` X ) ) $.
    equivbnd2.2 $e |- ( ph -> N e. ( Met ` X ) ) $.
    equivbnd2.3 $e |- ( ph -> R e. RR+ ) $.
    equivbnd2.4 $e |- ( ph -> S e. RR+ ) $.
    equivbnd2.5 $e |- ( ( ph /\ ( x e. X /\ y e. X ) ) ->
      ( x N y ) <_ ( R x. ( x M y ) ) ) $.
    equivbnd2.6 $e |- ( ( ph /\ ( x e. X /\ y e. X ) ) ->
      ( x M y ) <_ ( S x. ( x N y ) ) ) $.
    equivbnd2.7 $e |- C = ( M |` ( Y X. Y ) ) $.
    equivbnd2.8 $e |- D = ( N |` ( Y X. Y ) ) $.
    equivbnd2.9 $e |- ( ph -> ( C e. ( TotBnd ` Y ) <-> C e. ( Bnd ` Y ) ) ) $.
    $( If balls are totally bounded in the metric ` M ` , then balls are
       totally bounded in the equivalent metric ` N ` .  (Contributed by Mario
       Carneiro, 15-Sep-2015.) $)
    equivbnd2 $p |- ( ph -> ( D e. ( TotBnd ` Y ) <-> D e. ( Bnd ` Y ) ) ) $=
      ( ctotbnd cfv wcel cbnd totbndbnd wa simpr cxp cres cmet wss adantr sylan
      bnd2lem metres2 syl2anc eqeltrid crp cv co cmul cle wbr anim12dan adantlr
      sselda syldan wceq oveqi ovres eqtrid adantl 3brtr4d equivbnd equivtotbnd
      oveq2d biimpar bndmet ex impbid2 ) AEKUAUBZUCZEKUDUBZUCZEKUEAWDWBAWDUFZBC
      FDEKAWDDWCUCZDWAUCZWEBCGEDKAWDUGWEDHKKUHZUIZKUJUBZRWEHJUJUBZUCZKJUKZWIWJU
      CAWLWDLULAIWKUCWDWMMEIJKSUNUMZHKJUOUPUQAGURUCWDOULWEBUSZKUCZCUSZKUCZUFZUF
      ZWOWQHUTZGWOWQIUTZVAUTZWOWQDUTZGWOWQEUTZVAUTVBWEWSWOJUCZWQJUCZUFZXAXCVBVC
      ZWEWPXFWRXGWEKJWOWNVFWEKJWQWNVFVDZAXHXIWDQVEVGWSXDXAVHWEWSXDWOWQWIUTXADWI
      WOWQRVIWOWQKKHVJVKVLZWTXEXBGVAWSXEXBVHWEWSXEWOWQIWHUIZUTXBEXLWOWQSVIWOWQK
      KIVJVKVLZVPVMVNAWGWFTVQVGWDEWJUCAEKVRVLAFURUCWDNULWTXBFXAVAUTZXEFXDVAUTVB
      WEWSXHXBXNVBVCZXJAXHXOWDPVEVGXMWTXDXAFVAXKVPVMVOVSVT $.
  $}

  ${
    $d x z $.  $d a r z A $.  $d a r z C $.  $d f g k m r v y D $.  $d x y R $.
    $d f g k m r v w x y B $.  $d f g k r w y z E $.  $d a f g k r w x y ph $.
    $d f g k v w x y I $.  $d x S $.  $d f g k r w y z V $.  $d x Y $.
    prdsbnd.y $e |- Y = ( S Xs_ R ) $.
    prdsbnd.b $e |- B = ( Base ` Y ) $.
    prdsbnd.v $e |- V = ( Base ` ( R ` x ) ) $.
    prdsbnd.e $e |- E = ( ( dist ` ( R ` x ) ) |` ( V X. V ) ) $.
    prdsbnd.d $e |- D = ( dist ` Y ) $.
    prdsbnd.s $e |- ( ph -> S e. W ) $.
    prdsbnd.i $e |- ( ph -> I e. Fin ) $.
    prdsbnd.r $e |- ( ph -> R Fn I ) $.
    ${
      prdsbnd.m $e |- ( ( ph /\ x e. I ) -> E e. ( Bnd ` V ) ) $.
      $( The product metric over finite index set is bounded if all the factors
         are bounded.  (Contributed by Mario Carneiro, 13-Sep-2015.) $)
      prdsbnd $p |- ( ph -> D e. ( Bnd ` B ) ) $=
        ( vm vk vw vf vg vz cmet cfv wcel cxp cc0 cv cicc co wf wrex cbnd cprds
        cr cmpt cds cbs cvv eqid fvexd bndmet syl prdsmet wfn wceq dffn5 oveq2d
        sylib eqtrid fveq2d 3eltr4d wral cfn wex isbnd3 simprbi ralrimiva oveq2
        wa feq3d ac6sfi syl2anc crn csn cun clt csup wss frn adantl 0red adantr
        snssd unssd c0 wne wfo ffn dffn4 fofi snfi unfi sylancl ssun2 c0ex snid
        syl2an sselii ne0i mp1i wor w3a ltso fisupcl mpan syl3anc sseldd simprl
        cle wbr simprr metcl cxr eleqtrd adantlr prdsbascl r19.21bi ad2ant2r wb
        0re elicc2 sylancr suprub syl31anc sylanbrc metf ad2antrr metge0 oveqdr
        adantrr 3syl prdsdsval3 eqtrd ffvelcdm ad2ant2lr fovcdmd mpbid fimaxre2
        simp3d ssun1 ad2antlr fnfvelrn sselid expr ralimdva impr ovex ralrnmptw
        letrd rgenw breq1 ax-mp sylibr breq1d syl5ibrcom ralrimiv ralunb fmpttd
        elsni frnd ressxr sstrdi rexrd supxrleub mpbird eqbrtrd mpbir3and an32s
        a1i ralrimivva ffnov rspcev exlimddv ) ADCUGUHZUIZCCUJZUKUAULZUMUNZDUOZ
        UAUSUPZDCUQUHUIAFBHBULZEUHZUTZURUNZVAUHZUWSVBUHZUGUHDUWIABUXAUWTUWQFGHI
        JUWSVCUWSVDZUXAVDZNOUWTVDZQRAUWPHUIZWDZUWPEVEUXFGIUQUHUIZGIUGUHUIZTGIVF
        VGZVHADKVAUHUWTPAKUWSVAAKFEURUNUWSLAEUWRFURAEHVIEUWRVJSBHEVKVMVLVNZVOVN
        ZACUXAUGACKVBUHUXAMAKUWSVBUXJVOVNZVOVPZAHUSUBULZUOZIIUJZUKUWPUXNUHZUMUN
        ZGUOZBHVQZWDZUWOUBAHVRUIZUXPUKUCULZUMUNZGUOZUCUSUPZBHVQUYAUBVSRAUYFBHUX
        FUXGUYFTUXGUXHUYFUCGIVTWAVGWBUYEUXSBUCHUSUBUYCUXQVJUYDUXRGUXPUYCUXQUKUM
        WCWEWFWGAUYAWDZUXNWHZUKWIZWJZUSWKWLZUSUIZUWKUKUYKUMUNZDUOZUWOAUXOUYLUXT
        AUXOWDZUYJUSUYKUYOUYHUYIUSUXOUYHUSWMAHUSUXNWNWOAUYIUSWMUXOAUKUSAWPWRWQW
        SZUYOUYJVRUIZUYJWTXAZUYJUSWMZUYKUYJUIZUYOUYHVRUIZUYIVRUIUYQAUYBHUYHUXNX
        BZVUAUXORUXOUXNHVIZVUBHUSUXNXCZHUXNXDVMHUYHUXNXEXLUKXFUYHUYIXGXHZUKUYJU
        IZUYRUYOUYIUYJUKUYIUYHXIUKXJXKXMZUYJUKXNZXOUYPUSWKXPUYQUYRUYSXQUYTXRUSU
        YJWKXSXTYAYBZUUEZUYGDUWKVIZUDULZUEULZDUNZUYMUIZUECVQUDCVQUYNAVUKUYAAUWJ
        UWKUSDUOVUKUXMDCUUAUWKUSDXCUUFWQUYGVUOUDUECCAVULCUIZVUMCUIZWDZUYAVUOAVU
        RWDZUYAWDZVUOVUNUSUIZUKVUNYDYEZVUNUYKYDYEZVUTUWJVUPVUQVVAAUWJVURUYAUXMU
        UBZVUSVUPUYAAVUPVUQYCZWQZVUSVUQUYAAVUPVUQYFZWQZVULVUMDCYGYAVUTUWJVUPVUQ
        VVBVVDVVFVVHVULVUMDCUUCYAVUTVUNBHUWPVULUHZUWPVUMUHZGUNZUTZWHZUYIWJZYHWK
        WLZUYKYDVUSVUNVVOVJUYAVUSVUNVULVUMUWTUNVVOAVURUDUEDUWTUXKUUDVUSBUXAUWTU
        WQFGVULVUMHIJVRVCUWSUXBUXCAFJUIVURQWQZAUYBVURRWQZVUSUWQVCUIBHVUSUXEWDZU
        WPEVEWBZVUSVULCUXAVVEACUXAVJVURUXLWQZYIZVUSVUMCUXAVVGVVTYIZNOUXDUUGUUHW
        QVUTVVOUYKYDYEZUYCUYKYDYEZUCVVNVQZVUTVWDUCVVMVQZVWDUCUYIVQVWEVUTVVKUYKY
        DYEZBHVQZVWFVUSUXOUXTVWHVUSUXOWDZUXSVWGBHVWIUXEUXSVWGVWIUXEUXSWDZWDZVVK
        UXQUYKVUSUXEVVKUSUIZUXOUXSVVRUXHVVIIUIZVVJIUIZVWLAUXEUXHVURUXIYJVUSVWMB
        HVUSBUXAUWQFVULHIJVRVCUWSUXBUXCVVPVVQVVSNVWAYKYLZVUSVWNBHVUSBUXAUWQFVUM
        HIJVRVCUWSUXBUXCVVPVVQVVSNVWBYKYLZVVIVVJGIYGYAZYMUXOUXEUXQUSUIZVUSUXSHU
        SUWPUXNUUIUUJZVWIUYLVWJAUXOUYLVURVUIYJWQVWKVWLUKVVKYDYEZVVKUXQYDYEZVWKV
        VKUXRUIZVWLVWTVXAXQZVWKVVIVVJUXRIIGVWIUXEUXSYFVUSUXEVWMUXOUXSVWOYMVUSUX
        EVWNUXOUXSVWPYMUUKVWKUKUSUIZVWRVXBVXCYNYOVWSUKUXQVVKYPYQUULUUNVWKUYSUYR
        UYCUFULYDYEUCUYJVQUFUSUPZUXQUYJUIUXQUYKYDYEVWIUYSVWJAUXOUYSVURUYPYJWQVU
        FUYRVWKVUGVUHXOVWIVXEVWJAUXOVXEVURUYOUYSUYQVXEUYPVUEUFUCUYJUUMWGZYJWQVW
        KUYHUYJUXQUYHUYIUUOVWKVUCUXEUXQUYHUIUXOVUCVUSVWJVUDUUPVWIUXEUXSYCHUWPUX
        NUUQWGUURUFUCUYJUXQYRYSUVDUUSUUTUVAVVKVCUIZBHVQVWFVWHYNVXGBHVVIVVJGUVBU
        VEVWDVWGBUCHVVKVVLVCVVLVDUYCVVKUYKYDUVFUVCUVGUVHVUTVWDUCUYIVUTVWDUYCUYI
        UIZUKUYKYDYEZVUTUYSUYRVXEVUFVXIAUXOUYSVURUXTUYPYMVUFUYRVUTVUGVUHXOAUXOV
        XEVURUXTVXFYMVUFVUTVUGUWDUFUCUYJUKYRYSVXHUYCUKUYKYDUYCUKUVNUVIUVJUVKVWD
        UCVVMUYIUVLYTVUTVVNYHWMZUYKYHUIVWCVWEYNVUSVXJUYAVUSVVNUSYHVUSVVMUYIUSVU
        SHUSVVLVUSBHVVKUSVWQUVMUVOVUSUKUSVUSWPWRWSUVPUVQWQVUTUYKAUYAUYLVURVUJYJ
        ZUVRUCVVNUYKUVSWGUVTUWAVUTVXDUYLVUOVVAVVBVVCXQYNYOVXKUKUYKVUNYPYQUWBUWC
        UWEUDUECCUYMDUWFYTUWNUYNUAUYKUSUWLUYKVJUWMUYMDUWKUWLUYKUKUMWCWEUWGWGUWH
        UADCVTYT $.
    $}

    ${
      prdstotbnd.m $e |- ( ( ph /\ x e. I ) -> E e. ( TotBnd ` V ) ) $.
      $( The product metric over finite index set is totally bounded if all the
         factors are totally bounded.  (Contributed by Mario Carneiro,
         20-Sep-2015.) $)
      prdstotbnd $p |- ( ph -> D e. ( TotBnd ` B ) ) $=
        ( vy vv vr vf vz vw vg cmet cfv wcel cbl ciun wceq cpw cfn cin wrex crp
        cv co wral ctotbnd cmpt cprds cds cbs cvv eqid wa totbndmet syl prdsmet
        fvexd wfn dffn5 sylib oveq2d eqtrid fveq2d 3eltr4d wex adantr istotbnd3
        simprbi r19.21bi df-rex rexv bitr4i an32s ralrimiva eleq1 iuneq1 eqeq1d
        wf anbi12d ac6sfi syl2anc cixp wss elfpw simplbi ralimi ad2antll ss2ixp
        fnfi fndmd prdsbas rgenw ax-mp eqtr4di ad2antrr sseqtrrd ixpfi sylanbrc
        ixpeq2 cxmet metxmet rpxr blssm 3expa syl2an ssralv iunss sylibr eleq2d
        cxr sylc vex elixp eliun 3bitr4i eleq2 bitr3id biimprd ral2imi eleqtrrd
        wi adantl ex imbitrrdi syl5 sylbid imp oveq1 simpl anim12i biimpa ixpfn
        simpr simp-4l sseldd simp-4r fveq2 cbvmptv oveq2i oveqdr adantlr simprl
        ffn eleqtrd cc0 clt wbr rpgt0 prdsbl eqtrd syl12anc jca mpd ssrdv eqssd
        eximdv rspcev exlimddv ) ADCUHUIZUJZUAUBUSZUAUSZUCUSZDUKUIZUTZULZCUMZUB
        CUNUOUPZUQZUCURVADCVBUIUJAFBHBUSZEUIZVCZVDUTZVEUIZUWIVFUIZUHUIDUVOABUWK
        UWJUWGFGHIJUWIVGUWIVHUWKVHNOUWJVHQRAUWFHUJZVIZUWFEVMUWMGIVBUIUJZGIUHUIU
        JZTGIVJVKZVLADKVEUIZUWJPAKUWIVEAKFEVDUTUWILAEUWHFVDAEHVNZEUWHUMSBHEVOVP
        VQVRZVSVRACUWKUHACKVFUIZUWKMAKUWIVFUWSVSVRVSVTZAUWEUCURAUVSURUJZVIZHVGU
        DUSZWNZUWFUXDUIZIUNUOUPZUJZUEUXFUEUSZUVSGUKUIZUTZULZIUMZVIZBHVAZVIZUWEU
        DUXCHUOUJZUFUSZUXGUJZUEUXRUXKULZIUMZVIZUFVGUQZBHVAUXPUDWAAUXQUXBRWBZUXC
        UYCBHAUWLUXBUYCUWMUXBVIUYAUFUXGUQZUYCUWMUYEUCURUWMUWNUYEUCURVAZTUWNUWOU
        YFUEUFGIUCWCWDVKWEUYEUYBUFWAUYCUYAUFUXGWFUYBUFWGWHVPWIWJUYBUXNBUFHVGUDU
        XRUXFUMZUXSUXHUYAUXMUXRUXFUXGWKUYGUXTUXLIUEUXRUXFUXKWLWMWOWPWQUXCUXPVIZ
        BHUXFWRZUWDUJZUAUYIUWAULZCUMZUWEUYHUYICWSZUYIUOUJZUYJUYHUYIBHIWRZCUYHUX
        FIWSZBHVAZUYIUYOWSZUXOUYQUXCUXEUXNUYPBHUXHUYPUXMUXHUYPUXFUOUJZUXFIWTZXA
        WBXBXCBHUXFIXDVKZACUYOUMZUXBUXPACBHUWGVFUIZWRZUYOABCKEFHJUOLQAUWRUXQEUO
        UJSRHEXEWQMAHESXFXGIVUCUMZBHVAUYOVUDUMVUEBHNXHBHIVUCXOXIXJZXKZXLZUYHUXQ
        UYSBHVAZUYNUXCUXQUXPUYDWBZUXOVUIUXCUXEUXNUYSBHUXHUYSUXMUXHUYPUYSUYTWDWB
        XBXCBHUXFXMWQUYICWTXNUYHUYKCUYHUWACWSZUAUYIVAZUYKCWSUYHUYMVUKUACVAZVULV
        UHUXCVUMUXPADCXPUIUJZUVSYFUJZVUMUXBAUVPVUNUXADCXQVKUVSXRZVUNVUOVIVUKUAC
        VUNUVRCUJZVUOVUKVUNVUQVUOVUKDUVRUVSCXSXTWIWJYAWBVUKUAUYICYBYGUAUYIUWACY
        CYDUYHUGCUYKUYHUGUSZCUJZVURUWAUJZUAUYIUQZVURUYKUJUYHVUSVVAUYHVUSVIZHVGU
        VRWNZUWFUVRUIZUXFUJZUWFVURUIZVVDUVSUXJUTZUJZVIZBHVAZVIZUAWAZVVAVVBUXQUX
        IUXFUJZVVFUXKUJZVIZUEVGUQZBHVAZVVLUYHUXQVUSVUJWBUYHVUSVVQUYHVUSVURUYOUJ
        ZVVQUYHCUYOVURVUGYEZVVRVVFIUJZBHVAZUYHVVQVVRVURHVNZVWABHIVURUGYHZYIWDUX
        OVWAVVQYQUXCUXEUXNVVTVVPBHUXMVVTVVPYQUXHUXMVVPVVTVVPVVFUXLUJZUXMVVTVVNU
        EUXFUQVVOUEWAVWDVVPVVNUEUXFWFUEVVFUXFUXKYJVVOUEWGYKUXLIVVFYLYMYNYRYOXCU
        UAUUBUUCVVOVVIBUEHVGUAUXIVVDUMZVVMVVEVVNVVHUXIVVDUXFWKVWEUXKVVGVVFUXIVV
        DUVSUXJUUDYEWOWPWQVVBVVLUVRUYIUJZVUTVIZUAWAVVAVVBVVKVWGUAVVBVVKVWGVVBVV
        KVIZVWFVUTVVKVWFVVBVVKUVRHVNZVVEBHVAZVIVWFVVCVWIVVJVWJHVGUVRUUSVVIVVEBH
        VVEVVHUUEXBUUFBHUXFUVRUAYHYIYDYRZVWHVURBHVVGWRZUWAVWHVWBVVHBHVAZVURVWLU
        JVVBVWBVVKVVBVVRVWBUYHVUSVVRVVSUUGBHIVURUUHVKWBVVJVWMVVBVVCVVIVVHBHVVEV
        VHUUIXBXCBHVVGVURVWCYIXNVWHAVUQUXBUWAVWLUMAUXBUXPVUSVVKUUJZVWHUVRUYOCVW
        HUYIUYOUVRUYHUYRVUSVVKVUAXKVWKUUKVWHAVUBVWNVUFVKYPAUXBUXPVUSVVKUULAVUQU
        XBVIZVIZUWAUVRUVSFUAHUVREUIZVCZVDUTZVEUIZUKUIZUTVWLAVWOUAUCUVTVXAADVWTU
        KADUWQVWTPAKVWSVEAKUWIVWSUWSVWRUWHFVDUABHVWQUWGUVRUWFEUUMUUNUUOZXJZVSVR
        VSUUPVWPBUVSVWSVFUIZVWTUVRUWGFGHIJVWSVGVXBVXDVHNOVWTVHAFJUJVWOQWBAUXQVW
        ORWBVWPUWLVIUWFEVMAUWLGIXPUIUJZVWOUWMUWOVXEUWPGIXQVKUUQVWPUVRCVXDAVUQUX
        BUURACVXDUMVWOACUWTVXDMAKVWSVFVXCVSVRWBUUTUXBVUOAVUQVUPXCUXBUVAUVSUVBUV
        CAVUQUVSUVDXCUVEUVFUVGYPUVHYSUVLVUTUAUYIWFYTUVIYSUAVURUYIUWAYJYTUVJUVKU
        WCUYLUBUYIUWDUVQUYIUMUWBUYKCUAUVQUYIUWAWLWMUVMWQUVNWJUAUBDCUCWCXN $.
    $}

    prdsbnd2.c $e |- C = ( D |` ( A X. A ) ) $.
    prdsbnd2.e $e |- ( ( ph /\ x e. I ) -> E e. ( Met ` V ) ) $.
    prdsbnd2.m $e |- ( ( ph /\ x e. I ) ->
      ( ( E |` ( y X. y ) ) e. ( TotBnd ` y ) <->
        ( E |` ( y X. y ) ) e. ( Bnd ` y ) ) ) $.
    $( If balls are totally bounded in each factor, then balls are bounded in a
       metric product.  (Contributed by Mario Carneiro, 16-Sep-2015.) $)
    prdsbnd2 $p |- ( ph -> ( C e. ( TotBnd ` A ) <-> C e. ( Bnd ` A ) ) ) $=
      ( va vr ctotbnd cfv wcel cbnd totbndbnd wi c0 wceq cmet 0totbnd imbitrrid
      bndmet a1i wne cv wex n0 wa cbl co wss cr wrex simprr wb cmpt cds cbs cvv
      cprds fvexd prdsmet dffn5 sylib oveq2d eqtrid fveq2d 3eltr4d adantr simpr
      eqid wfn bnd2lem syl2an simprl sseldd ssbnd syl2anc mpbid cxp cres xpss12
      resabs1d eqtr4di crp simpll cc0 clt wbr ne0d cxmet ad2antrr metxmet rexrd
      cxr syl xbln0 syl3anc elrpd cress cfn fveq2 2fveq3 sqxpeqd reseq12d eqidd
      ovex oveq123d oveq12d cbvmptv fnmpti adantlr wral eleqtrd reseq2d eleq12d
      ralrimiva ad2antll eqtr4d oveq2i fveq2i cixp eqtrd r19.21bi simplrr rpred
      blbnd xpeq12 anidms bibi12d imbi2d vtocl mpbird fvmpt adantl ressds ax-mp
      prdsbascl rpxr blssm reseq1i prdstotbnd ressprdsds ixpeq2dva oveqdr rpgt0
      ressbas2 prdsbl prdsbas3 3eqtr4rd 3eltr3d syl12anc totbndss exp32 exlimdv
      eqeltrrd rexlimddv biimtrid pm2.61dne impbid2 ) AFDUHUIZUJZFDUKUIUJZFDULA
      UVTUVSUMZDUNDUNUOZUWAUMAUVTUVSUWBFDUPUIUJFDUSFDUQURUTDUNVAUFVBZDUJZUFVCAU
      WAUFDVDAUWDUWAUFAUWDUVTUVSAUWDUVTVEZVEZDUWCUGVBZGVFUIZVGZVHZUVSUGVIUWFUVT
      UWJUGVIVJZAUWDUVTVKUWFGEUPUIZUJZUWCEUJZUVTUWKVLAUWMUWEAIBKBVBZHUIZVMZVQVG
      ZVNUIZUWRVOUIZUPUIGUWLABUWTUWSUWPIJKLMUWRVPUWRWHZUWTWHZQRUWSWHTUAAUWOKUJZ
      VEZUWOHVRZUDVSAGNVNUIZUWSSANUWRVNANIHVQVGUWROAHUWQIVQAHKWIHUWQUOUBBKHVTWA
      WBWCZWDWCAEUWTUPAENVOUIZUWTPANUWRVOUXGWDWCZWDWEZWFUWFDEUWCAUWMUVTDEVHUWEU
      XJUWDUVTWGFGEDUCWJWKAUWDUVTWLZWMZUWCGFEDUGUCWNWOWPUWFUWGVIUJZUWJVEZVEZGUW
      IUWIWQZWRZDDWQZWRZFUVRUXOUXSGUXRWRFUXOGUXRUXPUXOUWJUWJUXRUXPVHUWFUXMUWJVK
      ZUXTDUWIDUWIWSWOWTUCXAUXOUXQUWIUHUIZUJZUWJUXSUVRUJUXOAUWNUWGXBUJZUYBAUWEU
      XNXCUWFUWNUXNUXLWFZUXOUWGUWFUXMUWJWLZUXOUWIUNVAZXDUWGXEXFZUXOUWIUWCUXODUW
      IUWCUXTUWFUWDUXNUXKWFWMXGUXOGEXHUIUJZUWNUWGXLUJZUYFUYGVLUXOUWMUYHAUWMUWEU
      XNUXJXIGEXJXMUYDUXOUWGUYEXKGUWCUWGEXNXOWPXPAUWNUYCVEZVEZICKCVBZHUIZUYLUWC
      UIZUWGUYMVNUIZUYMVOUIZUYPWQZWRZVFUIZVGZXQVGZVMZVQVGZVNUIZVUCVOUIZUHUIUXQU
      YAUYKBVUEVUDVUBIUWOVUBUIZVNUIZVUFVOUIZVUHWQZWRZKVUHMVUCVUCWHVUEWHVUHWHVUJ
      WHVUDWHAIMUJUYJTWFZAKXRUJUYJUAWFZVUBKWIUYKBKUWPUWOUWCUIZUWGJVFUIZVGZXQVGZ
      VUBUWPVUOXQYDZCBKVUAVUPUYLUWOUOZUYMUWPUYTVUOXQUYLUWOHXSZVURUYNVUMUWGUWGUY
      SVUNVURUYRJVFVURUYRUWPVNUIZLLWQZWRZJVURUYOVUTUYQVVAUYLUWOVNHXTVURUYPLVURU
      YPUWPVOUILUYLUWOVOHXTQXAYAYBRXAWDUYLUWOUWCXSVURUWGYCYEYFZYGZYHUTUYKUXCVEZ
      JVUOVUOWQZWRZVUOUHUIZVUJVUHUHUIVVEVVGVVHUJZVVGVUOUKUIZUJZVVEJLXHUIUJZVUML
      UJZUXMVVKVVEJLUPUIUJZVVLAUXCVVNUYJUDYIJLXJXMZUYKVVMBKUYKBUWTUWPIUWCKLMXRV
      PUWRUXAUXBVUKVULAUWPVPUJZBKYJUYJAVVPBKUXEYNWFQUYKUWCEUWTAUWNUYCWLZAEUWTUO
      UYJUXIWFYKUUOUUAZVVEUWGAUWNUYCUXCUUBUUCUWGJLVUMUUDXOAUXCVVIVVKVLZUYJUXDJU
      YLUYLWQZWRZUYLUHUIZUJZVWAUYLUKUIZUJZVLZUMUXDVVSUMCVUOVUMUWGVUNYDZUYLVUOUO
      ZVWFVVSUXDVWHVWCVVIVWEVVKVWHVWAVVGVWBVVHVWHVVTVVFJVWHVVTVVFUOUYLVUOUYLVUO
      UUEUUFYLZUYLVUOUHXSYMVWHVWAVVGVWDVVJVWIUYLVUOUKXSYMUUGUUHUEUUIYIUUJVVEVUJ
      VUTVVFWRZVVGVVEVUGVUTVUIVVFVVEVUGVUPVNUIZVUTVVEVUFVUPVNUXCVUFVUPUOUYKCUWO
      VUAVUPKVUBVVCVUBWHVUQUUKUULZWDVUOVPUJZVUTVWKUOVWGVUOVUTUWPVUPVPVUPWHZVUTW
      HUUMUUNXAVVEVUHVUOVVEVUHVUPVOUIZVUOVVEVUFVUPVOVWLWDVVEVUOLVHZVUOVWOUOVVEV
      VLVVMUYIVWPVVOVVRUYKUYIUXCUYCUYIAUWNUWGUUPYOZWFJVUMUWGLUUQXOZVUOLVUPUWPVW
      NQUVDXMZYPZYAYBVVEVVGVVBVVFWRVWJJVVBVVFRUURVVEVUTVVFVVAVVEVWPVWPVVFVVAVHV
      WRVWRVUOLVUOLWSWOWTWCYPVVEVUHVUOUHVWTWDWEUUSUYKVUDGIBKVUPVMZVQVGZVOUIZVXC
      WQZWRUXQUYKBVUOVXCGUWPIIMVUDVXBKMXRVPNVPANUWRUOUYJUXGWFUYKVXBYCVXCWHZSVUC
      VXBVNVUBVXAIVQVVDYQZYRVUKVUKVULVVEUWOHVRZVWMVVEVWGUTUUTUYKVXDUXPGUYKVXCUW
      IUYKBKVUOYSZBKVWOYSUWIVXCUYKBKVUOVWOVWSUVAUYKUWIUWCUWGICKUYMVMZVQVGZVNUIZ
      VFUIZVGVXHAUYJUFUGUWHVXLAGVXKVFAGUXFVXKSANVXJVNANUWRVXJUXGVXIUWQIVQCBKUYM
      UWPVUSYGYQZXAZWDWCWDUVBUYKBUWGVXJVOUIZVXKUWCUWPIJKLMVXJVPVXMVXOWHQRVXKWHV
      UKVULVXGVVOUYKUWCEVXOVVQAEVXOUOUYJAEUXHVXOPANVXJVOVXNWDWCWFYKVWQUYCUYGAUW
      NUWGUVCYOUVEYTUYKBVXCVUPIKVWOMXRVPVXBVXBWHVXEVUKVULUYKVUPVPUJZBKVXPVVEVUQ
      UTYNVWOWHUVFUVGZYAYLYTUYKVUEUWIUHUYKVUEVXCUWIVUCVXBVOVXFYRVXQWCWDUVHUVIUX
      TDUXQUWIUVJWOUVMUVNUVKUVLUVOUVPUVQ $.
  $}

  ${
    $d a b d r x y z D $.  $d d r x y z X $.
    cntotbnd.d $e |- D = ( ( abs o. - ) |` ( X X. X ) ) $.
    $( A subset of the complex numbers is totally bounded iff it is bounded.
       (Contributed by Mario Carneiro, 14-Sep-2015.) $)
    cntotbnd $p |- ( D e. ( TotBnd ` X ) <-> D e. ( Bnd ` X ) ) $=
      ( vx vz cfv wcel cabs co cc cgz cmul c1 caddc ci cr clt wbr wceq cle cbnd
      vy vr vd va vb ctotbnd totbndbnd cv cmin ccom cbl ciun wss cin c0 wne cfn
      crab wa cpw wrex crp wral cmpt crn rpcn gzcn mulcl cre cdiv c2 cfl cim cz
      cnmet rerpdivcld halfre readdcl sylancl flcld syl2anc syl abscld 1re cexp
      rpcnd zcnd ax-icn sylancr recnd replimd rpred oveq2d subdid fveq2d oveq1d
      a1i eqtrd resubcld resqcld absresq rddif absge0d cc0 halfgt0 le2sqd mpbid
      zred eqbrtrrd halfcn mpbi lelttrd mpbird eqid cnmetdval rpge0d absidd cxr
      absmuld wb cnxmet oveq2 eleq2d rspcev ovex oveq1 imbitrrdi mp2an ad2antlr
      cvv 0cn wi adantr wn letrd absled elfz syl3anc eqeq2d adantl syl2an elpw2
      fmpttd frnd cnex sylibr bnd2lem sselda adantrl recld simprl gzreim rpne0d
      cmet imcld divcld subcld addsub4d redivd imdivd oveq12d 3eqtr4d absreimsq
      mpan resqcli elrpii rpge0 sqvali halflt1 ltmul1ii mullidi breqtri eqbrtri
      mp1i lt2halvesd sq1 breqtrrdi 0le1 lt2sqd ltmul2dd mulcld divcan2d eqtr3d
      eqbrtrd 3eqtrrd mulridd 3brtr3d cxmet ad2antrl elbl2 syl22anc eliun rgenw
      rpxr expr rexrnmptw ax-mp bitri ssrdv ssbnd birani cneg cfz cmpo cxp fzfi
      wfo xpfi fnmpoi dffn4 fofi elrnmpti elgz simp2bi simpllr simplrl readdcld
      wfn peano2zd absrele simplrr sslin adantlr rpxrd rexrd bldisj 3exp2 imp32
      cxad w3a syl32anc sseq0 syl6an necon3ad imp rexadd subid1d breq12d ltnled
      mtbid ltmuldiv2d flltp1 znegcld simp3bi absimle rspc2ev ex elrnmpo ineq1d
      lttrd ltled eleq1 imbi12d syl5ibrcom rexlimdva biimtrid 3imp rabssdv ssfi
      neeq1d rexlimddv iuneq1 sseq2d rabeq anbi12d syl12anc ralrimiva sstotbnd3
      eleq1d impbii ) ABUGFGZABUAFGZABUHVVMVVLBDUBUIZDUIZUCUIZHUJUKZULFZIZUMZUN
      ZVVSBUOZUPUQZDVVNUSZURGZUTZUBJVAZVBZUCVCVDZVVMVWHUCVCVVMVVPVCGZUTZEKVVPEU
      IZLIZVEZVFZVWGGZBDVWOVVSUMZUNZVWCDVWOUSZURGZVWHVWKVWOJUNVWPVWKKJVWNVWKEKV
      WMJVWKVVPJGZVWLJGZVWMJGZVWLKGZVWJVXAVVMVVPVGUUAVWLVHZVVPVWLVIUUBZUUDUUEVW
      OJUUFUUCUUGVWKUBBVWQVWKVVNBGZVVNVWMVVPVVRIZGZEKVBZVVNVWQGZVVMVWJVXGVXJVVM
      VWJVXGUTUTZVVNVJFZVVPVKIZMVLVKIZNIZVMFZOVVNVNFZVVPVKIZVXONIZVMFZLIZNIZKGZ
      VVNVVPVYCLIZVVPVVRIZGZVXJVXLVXQVOGVYAVOGVYDVXLVXPVXLVXNPGZVXOPGZVXPPGVXLV
      XMVVPVXLVVNVVMVXGVVNJGZVWJVVMBJVVNVVQJUUOFGZVVMBJUNZVPAVVQJBCUUHUVEZUUIUU
      JZUUKVVMVWJVXGUULZVQZVRVXNVXOVSVTWAZVXLVXTVXLVXSPGZVYIVXTPGVXLVXRVVPVXLVV
      NVYNUUPVYOVQZVRVXSVXOVSVTWAZVXQVYAUUMWBZVXLVYGVYEVVNVVQIZVVPQRZVXLVVPVYCV
      VNVVPVKIZUJIZHFZLIZVVPMLIWUBVVPQVXLWUFMVVPVXLWUEVXLVYCWUDVXLVYDVYCJGWUAVY
      CVHWCZVXLVVNVVPVYNVXLVVPVYOWGZVXLVVPVYOUUNZUUQZUURZWDZMPGVXLWEWRZVYOVXLWU
      FMQRWUFVLWFIZMVLWFIZQRVXLWUOMWUPQVXLWUOVXQVXNUJIZVLWFIZVYAVXSUJIZVLWFIZNI
      ZMQVXLWUOWUQOWUSLIZNIZHFZVLWFIZWVAVXLWUFWVDVLWFVXLWUEWVCHVXLVYCVXNOVXSLIZ
      NIZUJIWUQVYBWVFUJIZNIWUEWVCVXLVXQVYBVXNWVFVXLVXQVYQWHVXLOJGZVYAJGVYBJGWIV
      XLVYAVYTWHZOVYAVIWJVXLVXNVYPWKVXLWVIVXSJGWVFJGWIVXLVXSVYSWKZOVXSVIWJUUSVX
      LWUDWVGVYCUJVXLWUDWUDVJFZOWUDVNFZLIZNIWVGVXLWUDWUKWLVXLWVLVXNWVNWVFNVXLVV
      PVVNVXLVVPVYOWMZVYNWUJUUTVXLWVMVXSOLVXLVVPVVNWVOVYNWUJUVAWNUVBWSWNVXLWVBW
      VHWUQNVXLOVYAVXSWVIVXLWIWRWVJWVKWOWNUVCWPWQVXLWUQPGZWUSPGZWVEWVASVXLVXQVX
      NVXLVXQVYQXIVYPWTZVXLVYAVXSVXLVYAVYTXIVYSWTZWUQWUSUVDWBWSVXLWURWUTMVXLWUQ
      WVRXAZVXLWUSWVSXAZWUNVXLWURVXOVLWFIZVXOWVTWWBPGVXLVXOVRUVFWRZVYIVXLVRWRZV
      XLWUQHFZVLWFIZWURWWBTVXLWVPWWFWURSWVRWUQXBWCVXLWWEVXOTRZWWFWWBTRVXLVYHWWG
      VYPVXNXCWCVXLWWEVXOVXLWUQVXLWUQWVRWKZWDWWDVXLWUQWWHXDVXOVCGXEVXOTRVXLVXOV
      RXFUVGVXOUVHUVOZXGXHXJWWBVXOQRVXLWWBVXOVXOLIZVXOQVXOXKUVIWWJMVXOLIZVXOQVX
      OMQRWWJWWKQRUVJVXOMVXOVRWEVRXFUVKXLVXOXKUVLUVMUVNWRZXMVXLWUTWWBVXOWWAWWCW
      WDVXLWUSHFZVLWFIZWUTWWBTVXLWVQWWNWUTSWVSWUSXBWCVXLWWMVXOTRZWWNWWBTRVXLVYR
      WWOVYSVXSXCWCVXLWWMVXOVXLWUSVXLWUSWVSWKZWDWWDVXLWUSWWPXDWWIXGXHXJWWLXMUVP
      UWEUVQUVRVXLWUFMWUMWUNVXLWUEWULXDXEMTRVXLUVSWRUVTXNUWAVXLWUBVYEVVNUJIZHFZ
      VVPHFZWUFLIZWUGVXLVYEJGZVYJWUBWWRSVXLVVPVYCWUIWUHUWBZVYNVYEVVNVVQVVQXOZXP
      WBVXLVVPWUELIZHFWWRWWTVXLWXDWWQHVXLWXDVYEVVPWUDLIZUJIWWQVXLVVPVYCWUDWUIWU
      HWUKWOVXLWXEVVNVYEUJVXLVVNVVPVYNWUIWUJUWCWNWSWPVXLVVPWUEWUIWULXTUWDVXLWWS
      VVPWUFLVXLVVPWVOVXLVVPVYOXQXRWQUWFVXLVVPWUIUWGUWHVXLVVQJUWIFGZVVPXSGZWXAV
      YJVYGWUCYAWXFVXLYBWRVWJWXGVVMVXGVVPUWOUWJWXBVYNVVNVVQVYEVVPJUWKUWLXNVXIVY
      GEVYCKVWLVYCSZVXHVYFVVNWXHVWMVYEVVPVVRVWLVYCVVPLYCWQYDYEWBUWPVXKVVNVVSGZD
      VWOVBZVXJDVVNVWOVVSUWMVWMYKGZEKVDWXJVXJYAWXKEKVVPVWLLYFZUWNWXIVXIEDKVWMVW
      NYKVWNXOZVVOVWMSZVVSVXHVVNVVOVWMVVPVVRYGZYDUWQUWRUWSYHUWTVWKBXEUDUIZVVRIZ
      UNZVWTUDPVVMWXRUDPVBZVWJVYKXEJGZVVMWXSYAVPYLXEVVQAJBUDCUXAYIUXBVWKWXPPGZW
      XRUTZUTZUEUFVVPWXPNIZVVPVKIZVMFZMNIZUXCZWYGUXDIZWYIVVPUEUIZOUFUIZLIZNIZLI
      ZUXEZVFZURGZVWSWYPUNVWTWYIWYIUXFZURGZWYRWYPWYOUXHZWYQWYIURGZXUAWYSWYHWYGU
      XGZXUBWYIWYIUXIYIWYOWYRUXSWYTUEUFWYIWYIWYNWYOWYOXOZVVPWYMLYFZUXJWYRWYOUXK
      XLWYRWYPWYOUXLYIWYCVWCDVWOWYPWYCVVOVWOGZVWCVVOWYPGZXUEWXNEKVBWYCVWCXUFYMZ
      EKVWMVVOVWNWXMWXLUXMWYCWXNXUGEKWYCVXDUTZXUGWXNVXHBUOZUPUQZVWMWYPGZYMXUHXU
      JVWMWYNSZUFWYIVBUEWYIVBZXUKXUHXUJXUMXUHXUJUTZVWLVJFZWYIGZVWLVNFZWYIGZVWMV
      VPXUOOXUQLIZNIZLIZSZXUMXUNXUPWYHXUOTRXUOWYGTRUTZXUNXUOHFZWYGTRXVCXUNXVDVW
      LHFZWYGXUNXUOXUNXUOVXDXUOVOGZWYCXUJVXDVXBXVFXUQVOGZVWLUXNZUXOYJZWHWDXUNVW
      LVXDVXBWYCXUJVXEYJZWDZXUNWYGXUNWYFXUNWYEXUNWYDVVPXUNVVPWXPXUNVVPXUHVWJXUJ
      VVMVWJWYBVXDUXPZYNZWMZXUHWYAXUJVWKWYAWXRVXDUXQZYNZUXRZXVMVQZWAUXTZXIZXUNV
      XBXVDXVETRXVJVWLUYAWCXUNXVEWYGXVKXVTXUNXVEWYEWYGXVKXVRXVTXUNVVPXVELIZWYDQ
      RXVEWYEQRXUNVWMHFZXWAWYDQXUNXWBWWSXVELIXWAXUNVVPVWLXUNVVPXVMWGXVJXTXUNWWS
      VVPXVELXUNVVPXVNXUNVVPXVMXQXRWQWSXUNXWBWYDQRWYDXWBTRZYOXUNVVPWXPUYJIZVWMX
      EVVQIZTRZXWCXUHXUJXWFYOXUHXWFXUIUPXUHXUIVXHWXQUOZUNZXWFXWGUPSZXUIUPSXUHWX
      RXWHVWKWYAWXRVXDUYBBWXQVXHUYCWCXUHWXFVXCWXTWXGWXPXSGZXWFXWIYMZWXFXUHYBWRV
      WKVXDVXCWYBVXFUYDZWXTXUHYLWRXUHVVPXVLUYEXUHWXPXVOUYFWXFVXCWXTUYKZWXGXWJXW
      KXWMWXGXWJXWFXWIVVQVWMXEVVPWXPJUYGUYHUYIUYLXUIXWGUYMUYNUYOUYPXUNXWDWYDXWE
      XWBTXUNVVPPGWYAXWDWYDSXVNXVPVVPWXPUYQWBXUNXWEVWMXEUJIZHFZXWBXUNVXCWXTXWEX
      WOSXUHVXCXUJXWLYNZYLVWMXEVVQWXCXPVTXUNXWNVWMHXUNVWMXWPUYRWPWSUYSVUAXUNXWB
      WYDXUNVWMXWPWDXVQUYTXNXJXUNXVEWYDVVPXVKXVQXVMVUBXHXUNWYEPGWYEWYGQRXVRWYEV
      UCWCVUKVULZYPXUNXUOWYGXUNXUOXVIXIXVTYQXHXUNXVFWYHVOGZWYGVOGZXUPXVCYAXVIXU
      NWYGXVSVUDZXVSXUOWYHWYGYRYSXNXUNXURWYHXUQTRXUQWYGTRUTZXUNXUQHFZWYGTRXXAXU
      NXXBXVEWYGXUNXUQXUNXUQVXDXVGWYCXUJVXDVXBXVFXVGXVHVUEYJZWHWDXVKXVTXUNVXBXX
      BXVETRXVJVWLVUFWCXWQYPXUNXUQWYGXUNXUQXXCXIXVTYQXHXUNXVGXWRXWSXURXXAYAXXCX
      WTXVSXUQWYHWYGYRYSXNXUNVWLXUTVVPLXUNVWLXVJWLWNXULXVBVWMVVPXUOWYLNIZLIZSUE
      UFXUOXUQWYIWYIWYJXUOSZWYNXXEVWMXXFWYMXXDVVPLWYJXUOWYLNYGWNYTWYKXUQSZXXEXV
      AVWMXXGXXDXUTVVPLXXGWYLXUSXUONWYKXUQOLYCWNWNYTVUGYSVUHUEUFWYIWYIWYNVWMWYO
      XUCXUDVUIYHWXNVWCXUJXUFXUKWXNVWBXUIUPWXNVVSVXHBWXOVUJVVAVVOVWMWYPVUMVUNVU
      OVUPVUQVURVUSWYPVWSVUTWJVVBVWFVWRVWTUTUBVWOVWGVVNVWOSZVWAVWRVWEVWTXXHVVTV
      WQBDVVNVWOVVSVVCVVDXXHVWDVWSURVWCDVVNVWOVVEVVJVVFYEVVGVVHVVMVYKVYLVVLVWIY
      AVPVYMDUBVVQAJBUCCVVIWJXNVVK $.
  $}

  ${
    $d x y A $.  $d x y I $.
    cnpwstotbnd.y $e |- Y = ( ( CCfld |`s A ) ^s I ) $.
    cnpwstotbnd.d $e |- D = ( ( dist ` Y ) |` ( X X. X ) ) $.
    $( A subset of ` A ^ I ` , where ` A C_ CC ` , is totally bounded iff it is
       bounded.  (Contributed by Mario Carneiro, 14-Sep-2015.) $)
    cnpwstotbnd $p |- ( ( A C_ CC /\ I e. Fin ) ->
        ( D e. ( TotBnd ` X ) <-> D e. ( Bnd ` X ) ) ) $=
      ( wss wcel ccnfld cfv cxp cds cres cbs cvv eqid cmet fveq2d eleq1d vx cfn
      vy cc wa cress co csca csn cprds ctotbnd cbnd cv fvexd simpr wfn fnconstg
      ovex mp1i cms cnfldms cnex ssex ad2antrr ressms sylancr syl wceq fvconst2
      msmet adantl sqxpeqd reseq12d 3eltr4d totbndbnd cnfldbas ressbas2 bnd2lem
      wi eleqtrrd syl5 cabs cmin ccom cntotbnd a1i sseq2d biimpa xpss12 syl2anc
      ex resabs1d adantr cnfldds ressds reseq1d eqtr4d 3bitr4d pm5.21ndd pwsval
      wb prdsbnd2 eqtrid ) AUDHZCUBIZUEZJAUFUGZUHKZCXGUILZUJUGZMKZDDLZNZDUKKZIX
      MDULKZIBXNIBXOIXFUAUCDXJOKZXMXKXIXHUAUMZXIKZMKZXROKZXTLZNZCXTPXJXJQXPQXTQ
      YBQXKQXFXGUHUNXDXEUOZXGPIZXICUPXFJAUFURZCXGPUQUSXMQXFXQCIZUEZXGMKZXGOKZYI
      LZNZYIRKZYBXTRKYGXGUTIZYKYLIYGJUTIAPIZYMVAXDYNXEYFAUDVBVCVDZAJPVEVFYKXGYI
      YIQYKQVJVGZYGXSYHYAYJYGXRXGMYFXRXGVHXFCXGXQYEVIVKZSYGXTYIYGXRXGOYQSZVLVMZ
      YGXTYIRYRSVNYGYKUCUMZYTLZNZYTUKKZIZUUBYTULKZIZYBUUANZUUCIUUGUUEIYGYTAHZUU
      DUUFUUDUUFYGUUHUUBYTVOYGYKARKZIZUUFUUHVSYGYKYLUUIYPYGAYIRXDAYIVHXEYFAUDXG
      JXGQZVPVQVDZSVTUUJUUFUUHUUBYKAYTUUBQVRWKVGZWAUUMYGUUHUUDUUFXAYGUUHUEZWBWC
      WDZUUANZUUCIZUUPUUEIZUUDUUFUUQUURXAUUNUUPYTUUPQWEWFUUNUUBUUPUUCUUNUUBYHUU
      ANUUPUUNYHUUAYJUUNYTYIHZUUSUUAYJHYGUUHUUSYGAYIYTUULWGWHZUUTYTYIYTYIWIWJWL
      UUNUUOYHUUAUUNYNUUOYHVHYGYNUUHYOWMAUUOJXGPUUKWNWOVGWPWQZTUUNUUBUUPUUEUVAT
      WRWKWSYGUUGUUBUUCYGYBYKUUAYSWPZTYGUUGUUBUUEUVBTWRXBXFBXMXNXFBEMKZXLNXMGXF
      UVCXKXLXFEXJMXFYDXEEXJVHYEYCXGXHCPUBEFXHQWTVFSWPXCZTXFBXMXOUVDTWR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Isometries
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Ismty $.
  $( Extend class notation with the class of metric space isometries. $)
  cismty $a class Ismty $.

  ${
    $d m n f x y $.
    $( Define a function which takes two metric spaces and returns the set of
       isometries between the spaces.  An isometry is a bijection which
       preserves distance.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    df-ismty $a |- Ismty = ( m e. U. ran *Met , n e. U. ran *Met |->
        { f | ( f : dom dom m -1-1-onto-> dom dom n /\ A. x e. dom dom m
            A. y e. dom dom m ( x m y ) = ( ( f ` x ) n ( f ` y ) ) ) } ) $.
  $}

  ${
    $d M m n f x y $.  $d N m n f x y $.  $d X m n f x y $.  $d Y m n f x y $.
    $( The set of isometries between two metric spaces.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    ismtyval $p |- ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) ) ->
      ( M Ismty N ) = { f | ( f : X -1-1-onto-> Y /\ A. x e. X A. y e. X
                            ( x M y ) = ( ( f ` x ) N ( f ` y ) ) ) } ) $=
      ( vm vn cxmet cfv wcel wa cv cdm wf1o co wceq wral wb crn cuni cab cismty
      cvv cmpo df-ismty a1i cxp dmeq xmetf fdmd sylan9eqr ad2ant2r dmeqd dmxpid
      cxr eqtrdi f1oeq2d ad2ant2l f1oeq3 bitrd oveq eqeqan12d raleqbidv anbi12d
      syl adantl abbidv fvssunirn simpl sselid simpr cmap wf f1of adantr elfvdm
      wss elmapg syl2anr imbitrrid abssdv ovex ssex ovmpod ) DFJKZLZEGJKZLZMZHI
      DEJUAUBZWLHNZOZOZINZOZOZCNZPZANZBNZWMQZXAWSKZXBWSKZWPQZRZBWOSZAWOSZMZCUCZ
      FGWSPZXAXBDQZXDXEEQZRZBFSZAFSZMZCUCZUDUEUDHIWLWLXKUFRWKABCHIUGUHWKWMDRZWP
      ERZMZMZXJXRCYCWTXLXIXQYCWTFWRWSPZXLYCWOFWRWSYCWOFFUIZOFYCWNYEWHXTWNYERWJY
      AXTWHWNDOYEWMDUJWHYEUQDDFUKULUMUNUOFUPURZUSYCWRGRYDXLTYCWRGGUIZOGYCWQYGWJ
      YAWQYGRWHXTYAWJWQEOYGWPEUJWJYGUQEEGUKULUMUTUOGUPURWRGFWSVAVGVBYCXHXPAWOFY
      FYCXGXOBWOFYFYBXGXOTWKXTYAXCXMXFXNXAXBWMDVCXDXEWPEVCVDVHVEVEVFVIWKWGWLDJF
      VJWHWJVKVLWKWIWLEJGVJWHWJVMVLWKXSGFVNQZVSXSUELWKXRCYHXRWSYHLZWKFGWSVOZXLY
      JXQFGWSVPVQWJGJOZLFYKLYIYJTWHEGJVRDFJVRGFWSYKYKVTWAWBWCXSYHGFVNWDWEVGWF
      $.
  $}

  ${
    $d M f x y $.  $d N f x y $.  $d X f x y $.  $d Y f x y $.  $d F f x y $.
    $( The condition "is an isometry".  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    isismty $p |- ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) ) ->
      ( F e. ( M Ismty N ) <-> ( F : X -1-1-onto-> Y /\ A. x e. X A. y e. X
                              ( x M y ) = ( ( F ` x ) N ( F ` y ) ) ) ) ) $=
      ( vf cxmet cfv wcel wa co cv wf1o wceq wral cvv elfvdm fveq1 cab ismtyval
      cismty eleq2d wi wb wf cdm f1of adantr syl3an 3expib com12 f1oeq1 oveq12d
      fex2 eqeq2d 2ralbidv anbi12d elab3g syl bitrd ) DFIJKZEGIJKZLZCDEUCMZKCFG
      HNZOZANZBNZDMZVIVGJZVJVGJZEMZPZBFQAFQZLZHUAZKZFGCOZVKVICJZVJCJZEMZPZBFQAF
      QZLZVEVFVRCABHDEFGUBUDVEWFCRKZUEVSWFUFWFVEWGWFVCVDWGWFFGCUGZVCFIUHZKVDGWI
      KWGVTWHWEFGCUIUJDFISEGISFGCWIWIUPUKULUMVQWFHCRVGCPZVHVTVPWEFGVGCUNWJVOWDA
      BFFWJVNWCVKWJVLWAVMWBEVIVGCTVJVGCTUOUQURUSUTVAVB $.
  $}

  ${
    $d u v x y F $.  $d u v x y M $.  $d u v x y N $.  $d u v x y X $.
    $d u v x y Y $.
    $( The inverse of an isometry is an isometry.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    ismtycnv $p |- ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) ) ->
                      ( F e. ( M Ismty N ) -> `' F e. ( N Ismty M ) ) ) $=
      ( vx vy vu vv cxmet cfv wcel wa wf1o cv co wceq wral cismty wi ex anim12d
      f1ocnv adantr f1ocnvdm imdistani oveq1 fveq2 oveq1d eqeq12d oveq2d rspc2v
      oveq2 impcom adantll syl f1ocnvfv2 adantrr adantrl oveq12d adantlr eqtr2d
      ccnv ralrimivva jca a1i isismty wb ancoms 3imtr4d ) BDJKLZCEJKLZMZDEANZFO
      ZGOZBPZVOAKZVPAKZCPZQZGDRFDRZMZEDAVCZNZHOZIOZCPZWFWDKZWGWDKZBPZQZIERHERZM
      ZABCSPLWDCBSPLZWCWNTVMWCWEWMVNWEWBDEAUCUDWCWLHIEEWCWFELZWGELZMZMZWKWIAKZW
      JAKZCPZWHWSWCWIDLZWJDLZMZMWKXBQZWCWRXEVNWRXETWBVNWPXCWQXDVNWPXCDEWFAUEUAV
      NWQXDDEWGAUEUAUBUDUFWBXEXFVNXEWBXFWAXFWIVPBPZWTVSCPZQFGWIWJDDVOWIQZVQXGVT
      XHVOWIVPBUGXIVRWTVSCVOWIAUHUIUJVPWJQZXGWKXHXBVPWJWIBUMXJVSXAWTCVPWJAUHUKU
      JULUNUOUPVNWRXBWHQWBVNWRMWTWFXAWGCVNWPWTWFQWQDEWFAUQURVNWQXAWGQWPDEWGAUQU
      SUTVAVBVDVEVFFGABCDEVGVLVKWOWNVHHIWDCBEDVGVIVJ $.
  $}

  ${
    $d x y F $.  $d x y M $.  $d x y N $.  $d x y P $.  $d x R $.  $d x y X $.
    $d x y Y $.
    $( The image of a ball under an isometry is another ball.  (Contributed by
       Jeff Madsen, 31-Jan-2014.) $)
    ismtyima $p |- ( ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) /\
       F e. ( M Ismty N ) ) /\ ( P e. X /\ R e. RR* ) ) ->
               ( F " ( P ( ball ` M ) R ) ) = ( ( F ` P ) ( ball ` N ) R ) ) $=
      ( vx vy cxmet cfv wcel co wa cbl wceq adantr syl3anc wb clt cismty w3a cv
      cxr cima crn imassrn wf1o wf wral isismty biimp3a simpld f1of frnd sstrid
      syl sseld wss simpl2 simprl ffvelcdm syl2anc simprr blssm ccnv wbr simpl1
      simplrr simplrl f1ocnv sylan elbl2 syl22anc wi simprd oveq1 fveq2 eqeq12d
      oveq1d oveq2 oveq2d rspc2v impancom imp syldan breq1d bitrd f1of1 f1elima
      3syl wf1 f1ocnvfv2 simpr eqeltrd 3bitr4d eleq1d 3bitr3d pm5.21ndd eqrdv
      ex ) DFJKLZEGJKLZCDEUAMLZUBZAFLZBUDLZNZNZHCABDOKMZUEZACKZBEOKMZXIHUCZGLZX
      NXKLZXNXMLZXIXKGXNXIXKCUFGCXJUGXIFGCXIFGCUHZFGCUIZXIXRXNIUCZDMZXNCKZXTCKZ
      EMZPZIFUJHFUJZXEXRYFNZXHXBXCXDYGHICDEFGUKULQZUMZFGCUNUQZUOUPURXIXMGXNXIXC
      XLGLZXGXMGUSXBXCXDXHUTZXIXSXFYKYJXEXFXGVAZFGACVBVCZXEXFXGVDZEXLBGVERURXIX
      OXPXQSXIXONZXNCVFZKZCKZXKLZYSXMLZXPXQYPYRXJLZXLYSEMZBTVGZYTUUAYPUUBAYRDMZ
      BTVGZUUDYPXBXGXFYRFLZUUBUUFSXIXBXOXBXCXDXHVHZQXEXFXGXOVIZXEXFXGXOVJXIGFYQ
      UIZXOUUGXIXRGFYQUHUUJYIFGCVKGFYQUNWKGFXNYQVBVLZYRDABFVMVNYPUUEUUCBTXIXOUU
      GUUEUUCPZUUKXIUUGUULXIXFYFUUGUULVOYMXIXRYFYHVPXFUUGYFUULYEUULAXTDMZXLYCEM
      ZPHIAYRFFXNAPZYAUUMYDUUNXNAXTDVQUUOYBXLYCEXNACVRVTVSXTYRPZUUMUUEUUNUUCXTY
      RADWAUUPYCYSXLEXTYRCVRWBVSWCWDVCWEWFWGWHYPFGCWLZUUGXJFUSZYTUUBSXIUUQXOXIX
      RUUQYIFGCWIUQQUUKXIUURXOXIXBXFXGUURUUHYMYODABFVERQFGCYRXJWJRYPXCXGYKYSGLU
      UAUUDSXIXCXOYLQUUIXIYKXOYNQYPYSXNGXIXRXOYSXNPYIFGXNCWMVLZXIXOWNWOYSEXLBGV
      MVNWPYPYSXNXKUUSWQYPYSXNXMUUSWQWRXAWSWT $.
  $}

  ${
    $d r u w x y z F $.  $d f r u w z J $.  $d f r u w x y z N $.  $d r w ph $.
    $d f u K $.  $d f x y M $.  $d f u x y X $.  $d f r u w x y z Y $.
    ismtyhmeo.1 $e |- J = ( MetOpen ` M ) $.
    ismtyhmeo.2 $e |- K = ( MetOpen ` N ) $.
    ${
      ismtyhmeolem.3 $e |- ( ph -> M e. ( *Met ` X ) ) $.
      ismtyhmeolem.4 $e |- ( ph -> N e. ( *Met ` Y ) ) $.
      ismtyhmeolem.5 $e |- ( ph -> F e. ( M Ismty N ) ) $.
      $( Lemma for ~ ismtyhmeo .  (Contributed by Jeff Madsen, 2-Sep-2009.)
         (Revised by Mario Carneiro, 12-Sep-2015.) $)
      ismtyhmeolem $p |- ( ph -> F e. ( J Cn K ) ) $=
        ( co wcel cv cfv wral wceq cxr vu vx vy vz vw vr ccn ccnv cima cbl wf1o
        wf crn cismty wa cxmet isismty syl2anc mpbid simpld f1of syl cxp adantr
        wb wi ismtycnv mpd simprl simprr ismtyima syl32anc f1ocnv 3syl ffvelcdm
        simpl syl2an blopn syl3anc eqeltrd ralrimivva cop fveq2 eqtr4di imaeq2d
        df-ov eleq1d ralxp sylibr cpw wfn blf ffn imaeq2 ralrn mpbird mopntopon
        4syl ctopon ctg mopnval tgcn mpbir2and ) ABCDUGNOGHBULZBUHZUAPZUIZCOZUA
        FUJQZUMZRZAGHBUKZXDAXLUBPZUCPZENXMBQXNBQFNSUCGRUBGRZABEFUNNOZXLXOUOZMAE
        GUPQOZFHUPQOZXPXQVEKLUBUCBEFGHUQURUSUTZGHBVAVBAXKXEUDPZXIQZUIZCOZUDHTVC
        ZRZAXEUEPZUFPZXINZUIZCOZUFTRUEHRYFAYKUEUFHTAYGHOZYHTOZUOZUOZYJYGXEQZYHE
        UJQNZCYOXSXRXEFEUNNOZYLYMYJYQSAXSYNLVDAXRYNKVDZAYRYNAXPYRMAXRXSXPYRVFKL
        BEFGHVGURVHVDAYLYMVIAYLYMVJZYGYHXEFEHGVKVLYOXRYPGOZYMYQCOYSAHGXEULZYLUU
        AYNAXLHGXEUKUUBXTGHBVMHGXEVAVNYLYMVPHGYGXEVOVQYTEYPYHCGIVRVSVTWAYDYKUDU
        EUFHTYAYGYHWBZSZYCYJCUUDYBYIXEUUDYBUUCXIQYIYAUUCXIWCYGYHXIWFWDWEWGWHWIA
        XSYEHWJZXIULXIYEWKXKYFVELFHWLYEUUEXIWMXHYDUAUDYEXIXFYBSXGYCCXFYBXEWNWGW
        OWRWPAUAXJBCDGHAXRCGWSQOKECGIWQVBAXSDXJWTQSLFDHJXAVBAXSDHWSQOLFDHJWQVBX
        BXC $.
    $}

    $( An isometry is a homeomorphism on the induced topology.  (Contributed by
       Jeff Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro, 12-Sep-2015.) $)
    ismtyhmeo $p |- ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) ) ->
                      ( M Ismty N ) C_ ( J Homeo K ) ) $=
      ( vf cxmet cfv wcel wa cismty co chmeo cv ccn ccnv ismtyhmeolem simpr imp
      simpll simplr ismtycnv ishmeo sylanbrc ex ssrdv ) CEJKLZDFJKLZMZICDNOZABP
      OZULIQZUMLZUOUNLZULUPMZUOABROLUOSZBAROLUQURUOABCDEFGHUJUKUPUCZUJUKUPUDZUL
      UPUATURUSBADCFEHGVAUTULUPUSDCNOLUOCDEFUEUBTUOABUFUGUHUI $.
  $}

  ${
    $d r w x y z F $.  $d r w x y z M $.  $d r w y z N $.  $d r w x y z X $.
    $d r w y z Y $.
    $( Lemma for ~ ismtybnd .  (Contributed by Jeff Madsen, 2-Sep-2009.)
       (Proof shortened by Mario Carneiro, 19-Jan-2014.) $)
    ismtybndlem $p |- ( ( N e. ( *Met ` Y ) /\ F e. ( M Ismty N ) ) ->
        ( M e. ( Bnd ` X ) -> N e. ( Bnd ` Y ) ) ) $=
      ( vx vr vy vz vw cfv wcel co wa cv wceq crp wrex wral wi cxmet cismty cbl
      cbnd w3a ccnv wf1o wf isismty biimp3a simpld f1ocnv f1of ffvelcdmda oveq1
      3syl eqeq2d rexbidv rspcv syl cima imaeq2 wfo f1ofo foima adantr cxr rpxr
      adantl anim12dan ismtyima syldan f1ocnvfv2 syl2an oveq1d eqeq12d imbitrid
      simpl eqtrd reximdva syld ralrimdva simp2 jctild 3expib com12 impd isbndx
      anassrs 3imtr4g ) CEUAKLZABCUBMLZNZBDUAKLZDFOZGOZBUCKZMZPZGQRZFDSZNWKEHOZ
      WPCUCKZMZPZGQRZHESZNZBDUDKLCEUDKLWMWNXAXHWNWMXAXHTZWNWKWLXIWNWKWLUEZXAXGW
      KXJXAXFHEXJXBELZNZXADXBAUFZKZWPWQMZPZGQRZXFXLXNDLZXAXQTXJEDXBXMXJDEAUGZED
      XMUGEDXMUHXJXSIOZJOZBMXTAKYAAKCMPJDSIDSZWNWKWLXSYBNIJABCDEUIUJUKZDEAULEDX
      MUMUPUNZWTXQFXNDWOXNPZWSXPGQYEWRXODWOXNWPWQUOUQURUSUTXLXPXEGQXJXKWPQLZXPX
      ETXPADVAZAXOVAZPXJXKYFNZNZXEDXOAVBYJYGEYHXDXJYGEPZYIXJXSDEAVCYKYCDEAVDDEA
      VEUPVFYJYHXNAKZWPXCMZXDXJYIXRWPVGLZNYHYMPXJXKXRYFYNYDYFYNXJWPVHVIVJXNWPAB
      CDEVKVLYJYLXBWPXCXJXSXKYLXBPYIYCXKYFVRDEXBAVMVNVOVSVPVQWIVTWAWBWNWKWLWCWD
      WEWFWGFBDGWHHCEGWHWJ $.

    $( Isometries preserve boundedness.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Revised by Mario Carneiro, 19-Jan-2014.) $)
    ismtybnd $p |- ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) /\
      F e. ( M Ismty N ) ) -> ( M e. ( Bnd ` X ) <-> N e. ( Bnd ` Y ) ) ) $=
      ( cxmet cfv wcel cismty w3a cbnd ismtybndlem 3adant1 ccnv ismtycnv 3impia
      co wi 3adant2 syld3an3 impbid ) BDFGHZCEFGHZABCIQHZJBDKGHZCEKGHZUCUDUEUFR
      UBABCDELMUBUCUDANZCBIQHZUFUERZUBUCUDUHABCDEOPUBUHUIUCUGCBEDLSTUA $.
  $}

  ${
    $d u v A $.  $d u v x y F $.  $d u v x y M $.  $d u v x y N $.  $d u v S $.
    $d u v T $.  $d u v x y X $.  $d u v x y Y $.
    ismtyres.2 $e |- B = ( F " A ) $.
    ismtyres.3 $e |- S = ( M |` ( A X. A ) ) $.
    ismtyres.4 $e |- T = ( N |` ( B X. B ) ) $.
    $( A restriction of an isometry is an isometry.  The condition ` A C_ X `
       is not necessary but makes the proof easier.  (Contributed by Jeff
       Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro, 12-Sep-2015.) $)
    ismtyres $p |- ( ( ( M e. ( *Met ` X ) /\ N e. ( *Met ` Y ) ) /\
      ( F e. ( M Ismty N ) /\ A C_ X ) ) -> ( F |` A ) e. ( S Ismty T ) ) $=
      ( vu cxmet cfv wcel wa co wceq syl2anc vv vx vy cismty wss cres cima wf1o
      cv wf1 isismty simprbda adantrr f1of1 syl simprr f1ores biimpa wi anim12d
      wral imp oveq1 fveq2 oveq1d eqeq12d oveq2 oveq2d rspc2v adantlrl adantlll
      ssel an32s oveqi ovres eqtrid adantl fvres ad2antrl ad2antll oveq12d wfun
      cxp f1ofun f1odm sseq2d biimparc funfvima2 eleqtrrdi adantrl ovresd eqtrd
      cdm adantlrr 3eqtr4d ralrimivva wb xmetres2 eqeltrid ad2ant2rl simplr crn
      mpdan imassrn eqsstri f1ofo forn 3syl sseqtrid fveq2i eleqtrdi mpbir2and
      wfo ) FHNOPZGINOPZQZEFGUDRPZAHUEZQZQZEAUFZCDUDRPZAEAUGZYAUHZMUIZUAUIZCRZY
      EYAOZYFYAOZDRZSZUAAVAMAVAZXTHIEUJZXRYDXTHIEUHZYMXPXQYNXRXPXQYNUBUIZUCUIZF
      RZYOEOZYPEOZGRZSZUCHVAUBHVAZUBUCEFGHIUKZULUMZHIEUNUOXPXQXRUPHIAEUQTXTYNUU
      BQZYLXPXQUUEXRXPXQUUEUUCURUMXPXRUUEYLXQXPXRQUUEQZYKMUAAAUUFYEAPZYFAPZQZQY
      EYFFRZYEEOZYFEOZGRZYGYJXRUUEUUIUUJUUMSZXPXRUUBUUIUUNYNXRUUIUUBUUNXRUUIQZU
      UBUUNUUOYEHPZYFHPZQZUUBUUNUSXRUUIUURXRUUGUUPUUHUUQAHYEVLAHYFVLUTVBUUAUUNY
      EYPFRZUUKYSGRZSUBUCYEYFHHYOYESZYQUUSYTUUTYOYEYPFVCUVAYRUUKYSGYOYEEVDVEVFY
      PYFSZUUSUUJUUTUUMYPYFYEFVGUVBYSUULUUKGYPYFEVDVHVFVIUOVBVMVJVKUUIYGUUJSUUF
      UUIYGYEYFFAAWCUFZRUUJCUVCYEYFKVNYEYFAAFVOVPVQXRUUEUUIYJUUMSZXPXRYNUUIUVDU
      UBXRYNQZUUIQZYJUUKUULDRZUUMUVFYHUUKYIUULDUUGYHUUKSUVEUUHYEAEVRVSUUHYIUULS
      UVEUUGYFAEVRVTWAUVFUVGUUKUULGBBWCUFZRUUMDUVHUUKUULLVNUVFUUKUULGBUVEUUGUUK
      BPUUHUVEUUGQUUKYCBUVEUUGUUKYCPZUVEEWBZAEWMZUEZUUGUVIUSYNUVJXRHIEWDVQZYNUV
      LXRYNUVKHAHIEWEWFWGZAYEEWHTVBJWIUMUVEUUHUULBPUUGUVEUUHQUULYCBUVEUUHUULYCP
      ZUVEUVJUVLUUHUVOUSUVMUVNAYFEWHTVBJWIWJWKVPWLWNVKWOWPVJXCXTCANOZPZDYCNOZPY
      BYDYLQWQXNXRUVQXOXQXNXRQCUVCUVPKFAHWRWSWTXTDBNOZUVRXTDUVHUVSLXTXOBIUEUVHU
      VSPXNXOXSXAXTEXBZBIBYCUVTJEAXDXEXTYNHIEXMUVTISUUDHIEXFHIEXGXHXIGBIWRTWSBY
      CNJXJXKMUAYACDAYCUKTXL $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Heine-Borel Theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d n t x y A $.  $d k n r t u x y F $.  $d g k t x G $.  $d g k r t x ph $.
    $d g k m n r t u v x y z D $.  $d g k m r t u x y z M $.  $d m n x y z T $.
    $d g n t u v y B $.  $d g k m n r t u v x y z J $.  $d g n t u v x y z U $.
    $d g t y z ps $.  $d k m n t u v x y z S $.  $d g k m n r t u v x y z X $.
    $d m n t u v y C $.  $d g n t x y z K $.  $d k t x Y $.  $d k v x Z $.
    heibor.1 $e |- J = ( MetOpen ` D ) $.
    ${
      $d m F $.  $d m n u y ph $.
      heibor1.3 $e |- ( ph -> D e. ( Met ` X ) ) $.
      heibor1.4 $e |- ( ph -> J e. Comp ) $.
      heibor1.5 $e |- ( ph -> F e. ( Cau ` D ) ) $.
      heibor1.6 $e |- ( ph -> F : NN --> X ) $.
      $( Lemma for ~ heibor1 .  A compact metric space is complete.  This proof
         works by considering the collection ` cls ( F " ( ZZ>= `` n ) ) ` for
         each ` n e. NN ` , which has the finite intersection property because
         any finite intersection of upper integer sets is another upper integer
         set, so any finite intersection of the image closures will contain
         ` ( F " ( ZZ>= `` m ) ) ` for some ` m ` .  Thus, by compactness, the
         intersection contains a point ` y ` , which must then be the
         convergent point of ` F ` .  (Contributed by Jeff Madsen,
         17-Jan-2014.)  (Revised by Mario Carneiro, 5-Jun-2014.) $)
      heibor1lem $p |- ( ph -> F e. dom ( ~~>t ` J ) ) $=
        ( vk vu cfv wrex wcel c0 wss wi cn wa vy vr vm vn cv cima wceq cuz cint
        crn cdm ccld cpw cfi wex syl imassrn sseqtrd sstrid eqid syl2anc eleq1a
        wn fvex cfn cin bitri wne raleq anbi2d inteq sseq2d rexbidv imbi12d weq
        wral cc0 cz wfn wf uzf ax-mp fnfvelrn mp2an imaeq2 sseq1d rspcev ssralv
        cvv a1i vex eqeq1 sylib uzin2 inss2 inss1 imass2 expcom syl6 impd com23
        syl5 imp c1 nnuz n0 exlimdv sylancr rexlimdva adantr mpd sylan2b eleq2d
        ssn0 wb wbr wal co clt fveq2d mpbid ralimi ad2antrr ad2antll sylc rpxrd
        syl3anc sseli caddc ad3antrrr eluznn ad2ant2lr ffvelcdmd syl22anc metcl
        crp cr rpred mpan2d anassrs ccl cab clm ccmp ctop cxmet metxmet mopntop
        cuni cmet frnd mopnuni clscld rexlimdvw abssdv elpw2 elin velpw ssabral
        sylibr anbi1i csn cun ffn 0z ssv int0 sseqtrri ssun1 anim2i ssun2 ralsn
        imim1i sscls sseq2 syl5ibrcom anim12i ss2in intunsn sseqtrrdi rexlimdvv
        ssin reeanv cbvrexvw 3imtr3g expd sylcom findcard2 impr ffnd 1z eqeltri
        com12 mpan2 uzn0 wfun fnfun fndm sseqtrrid funfvima2 ne0i necomd neneqd
        nrexdv 0ex zex pwex frn ssexi abrexex sylnibr cmptop cmpfi fveq2 notbid
        elfi neeq1d bitrdi rspccv syl3c wrel lmrel r19.23v albii ceqsalv ralbii
        ibi eleq2 ralcom4 bitr3i elintab 3bitr4i rspceeqv mpbir intss1 sseqtrrd
        elab clsss3 sselda c2 cdiv w3a cpm ccau 1zzd iscau3 simprd simp3 reximi
        cc rphalfcl breq2 2ralbidv rspccva syl2an cbl ffund nnz simplr ad2antrl
        rspcv cxr blopn blcntr clsndisj syl32anc fvelima sylan2 adantl biimtrid
        reximdv ex r19.29 uznnssnn simprlr simplrl elbl3 simprr lt2add 2halvesd
        simpllr rpcnd breq2d sylibd mettri2 syl13anc readdcld lelttr mpand syld
        ralimdva expr reximdva ssrexv sylsyld syldanl ralrimiva eqidd mpbir2and
        cle lmmbrf sylan2br releldm exlimddv ) AUAUEZKUEZCLUEZUFZDUUAMZMZUGZLUH
        UJZNZKUUBZUIZOZCDUUCMZUKOZUAADUUDOZVXNDULMZUMZOZPVXNUNMZOZVCZVXPUAUOZHA
        VXNVXTQVYBAVXMKVXTAVXKVXFVXTOZLVXLAVXJVXTOZVXKVYGRADUUEOZVXHDUUIZQZVYHA
        BEUUFMOZVYIABEUUJMOZVYLGBEUUGUPZBDEFUUHUPZAVXHCUJZVYJCVXGUQZAVYPEVYJASE
        CJUUKZAVYLEVYJUGVYNBDEFUULUPZURZUSVXHDVYJVYJUTZUUMVAVXJVXTVXFVBUPUUNUUO
        VXNVXTDULVDUUPUUTAPUBUEZUIZUGZUBVXNUMZVEVFZNZVYDAWUDUBWUFWUBWUFOZAVXMKW
        UBVPZWUBVEOZTZWUDVCWUHWUBWUEOZWUJTWUKWUBWUEVEUUQWULWUIWUJWULWUBVXNQWUIU
        BVXNUURVXMKWUBUUSVGUVAVGAWUKTZPWUCWUMWUCPWUMCVXFUFZWUCQZKVXLNZWUCPVHZAW
        UIWUJWUPWUJAWUITZWUPAVXMKUCUEZVPZTZWUNWUSUIZQZKVXLNZRAVXMKPVPZTZWUNPUIZ
        QZKVXLNZRAVXMKVXEVPZTZWUNVXEUIZQZKVXLNZRZAVXMKVXEUDUEZUVBZUVCZVPZTZWUNW
        VRUIZQZKVXLNZRZWURWUPRUCUAUDWUBWUSPUGZWVAWVFWVDWVIWWEWUTWVEAVXMKWUSPVIV
        JWWEWVCWVHKVXLWWEWVBWVGWUNWUSPVKVLVMVNUCUAVOZWVAWVKWVDWVNWWFWUTWVJAVXMK
        WUSVXEVIVJWWFWVCWVMKVXLWWFWVBWVLWUNWUSVXEVKVLVMVNWUSWVRUGZWVAWVTWVDWWCW
        WGWUTWVSAVXMKWUSWVRVIVJWWGWVCWWBKVXLWWGWVBWWAWUNWUSWVRVKVLVMVNUCUBVOZWV
        AWURWVDWUPWWHWUTWUIAVXMKWUSWUBVIVJWWHWVCWUOKVXLWWHWVBWUCWUNWUSWUBVKVLVM
        VNWVIWVFVQUHMZVXLOZCWWIUFZWVGQZWVIUHVRVSZVQVROWWJVRVRUMZUHVTZWWMWAVRWWN
        UHUVDWBZUVEVRVQUHWCWDWWKWIWVGWWKUVFUVGUVHWVHWWLKWWIVXLVXFWWIUGWUNWWKWVG
        VXFWWICWEWFWGWDWJWVOWWDRVXEVEOWVOWVTWVNWWCWVTWVKWVNWVSWVJAVXEWVRQWVSWVJ
        RVXEWVQUVIVXMKVXEWVRWHWBUVJUVMAWVSWVNWWCRZWVSWVPVXJUGZLVXLNZAWWQWVSVXMK
        WVQVPZWWSWVQWVRQWVSWWTRWVQVXEUVKVXMKWVQWVRWHWBVXMWWSKWVPUDWKZKUDVOVXKWW
        RLVXLVXFWVPVXJWLVMUVLWMAWWSWVNWWCAWWRWVMTZKVXLNLVXLNCWUSUFZWWAQZUCVXLNZ
        WWSWVNTWWCAWXBWXELKVXLVXLVXGVXLOVXFVXLOZTVXGVXFVFZVXLOZAWXBWXERVXGVXFWN
        AWXBWXHWXEAWXBCWXGUFZWWAQZWXHWXERAWWRWVMWXJAWWRVXHWVPQZWVMWXJRAWXKWWRVX
        HVXJQZAVYIVYKWXLVYOAVXHEVYJAVXHVYPEVYQVYRUSVYSURVXHDVYJWUAUVNVAWVPVXJVX
        HUVOUVPWVMWXKWXJWVMWXKTZWXIWVLWVPVFZWWAWXMWXIWUNVXHVFZWXNWXGVXFQZWXGVXG
        QZWXIWXOQZVXGVXFWOVXGVXFWPWXPWXQTWXIWUNQZWXIVXHQZTWXRWXPWXSWXQWXTWXGVXF
        CWQWXGVXGCWQUVQWXIWUNVXHUWBWMWDWUNWVLVXHWVPUVRUSVXEWVPWXAUVSUVTWRWSWTWX
        HWXJWXEWXDWXJUCWXGVXLWUSWXGUGWXCWXIWWAWUSWXGCWEWFWGWRWSXAXBUWAWWRWVMLKV
        XLVXLUWCWXDWWBUCKVXLUCKVOWXCWUNWWAWUSVXFCWEWFUWDUWEUWFXBXCUWGWJUWHUWMUW
        IAWUPWUQRZWUKACSVSZWYAASECJUWJWYBWUOWUQKVXLWYBWXFTZWUNPVHZWUOWUQRWYCCVX
        FSVFZUFZWUNQZWYFPVHZWYDWYEVXFQWYGVXFSWPWYEVXFCWQWBWYBWXFWYHWXFVXEWYEOZU
        AUOZWYBWYHWXFWYEPVHZWYJWXFWYEVXLOZWYKWXFSVXLOZWYLSXDUHMZVXLXEWWMXDVROWY
        NVXLOWWPUWKVRXDUHWCWDUWLZVXFSWNUWNWYEUWOUPUAWYEXFWMWYBWYIWYHUAWYBWYIVXE
        CMZWYFOZWYHWYBCUWPZWYECUKZQWYIWYQRSCUWQWYBSWYEWYSVXFSWOSCUWRUWSWYEVXECU
        WTVAWYFWYPUXAWSXGXBXCWYFWUNXNXHWUOWYDWUQWUNWUCXNWRUPXIUPXJXKUXBUXCXLUXD
        PWIOVXNWIOVYDWUGXOUXELKVXLVXJVXLWWNVRUXFUXGWWOVXLWWNQWAVRWWNUHUXHWBUXIU
        XJUBPVXNWIWIUXPWDUXKVXSPWUSUNMZOZVCZWVBPVHZRZUCVYAVPZVYBVYEVYFRZRVXSXUE
        VXSVYIVXSXUEXODUXLUCDUXMUPUYGXUDXUFUCVXNVYAWUSVXNUGZXUBVYEXUCVYFXUGXUAV
        YDXUGWYTVYCPWUSVXNUNUXNXMUXOXUGXUCVXOPVHVYFXUGWVBVXOPWUSVXNVKUXQUAVXOXF
        UXRVNUXSUPUXTAVXPTVXQUYACVXEVXQXPZVXRDUYBVXPAVXEVXJOZLVXLVPZXUHVXKVXEVX
        FOZRZLVXLVPZKXQZVXMXUKRZKXQXUJVXPXUMXUOKVXKXUKLVXLUYCUYDXUJXULKXQZLVXLV
        PXUNXUPXUILVXLXUKXUIKVXJVXHVXIVDVXFVXJVXEUYHUYEUYFXULLKVXLUYIUYJVXMKVXE
        UAWKUYKUYLZAXUJTZXUHVXEEOZWVPCMZVXEBXRZWUBXSXPZUDVXFUHMZVPZKSNZUBYPVPZX
        UJAVXPXUSXUQAVXOEVXEAVXOCSUFZVXIMZEXVHVXNOZVXOXVHQXVIXVHVXJUGZLVXLNZWYM
        XVHXVHUGXVKWYOXVHUTLSVXLVXJXVHXVHVXGSUGVXHXVGVXIVXGSCWEXTUYMWDVXMXVKKXV
        HXVGVXIVDVXFXVHUGVXKXVJLVXLVXFXVHVXJWLVMUYQUYNXVHVXNUYOWBAXVHVYJEAVYIXV
        GVYJQXVHVYJQVYOAXVGVYPVYJCSUQVYTUSXVGDVYJWUAUYRVAVYSUYPUSUYSXLZXURXVEUB
        YPXURWUBYPOZTZVXFCMZXUTBXRZWUBUYTVUAXRZXSXPZUDXVCVPZKWUSUHMZVPZUCSNZXVE
        XURXVPVXEXSXPZUDXVCVPZKXVTVPZUCSNZUAYPVPZXVQYPOZXWBXVMAXWGXUJAVXFWYSOZX
        VOEOZXWDVUBZKXVTVPZUCSNZUAYPVPZXWGACEVUJVUCXROZXWNACBVUDMOXWOXWNTIAUABU
        CKUDCXDESXEVYNAVUEZVUFYAVUGXWMXWFUAYPXWLXWEUCSXWKXWDKXVTXWIXWJXWDVUHYBV
        UIYBUPXJWUBVUKZXWFXWBUAXVQYPVXEXVQUGZXWEXWAUCSXWRXWCXVRKUDXVTXVCVXEXVQX
        VPXSVULVUMVMVUNVUOXVNXWAXVEUCSXURXVMWUSSOZXWAXVERXURXVMXWSTZTZXWAXVOVXE
        XVQBVUPMXRZOZKXVTNZXVEXXAWYRXXBCXVTUFZVFZPVHZXXDAWYRXUJXWTASECJVUQYCXXA
        VYIXXEVYJQZVXEXXEVXIMZOZXXBDOZVXEXXBOZXXGAVYIXUJXWTVYOYCAXXHXUJXWTAXXEV
        YPVYJCXVTUQVYTUSYCXXAXVTVXLOZXUJXXJXWSXXMXURXVMXWSWWMWUSVROXXMWWPWUSVUR
        VRWUSUHWCXHYDAXUJXWTVUSXUIXXJLXVTVXLVXGXVTUGZVXJXXIVXEXXNVXHXXEVXIVXGXV
        TCWEXTXMVVAYEXXAVYLXUSXVQVVBOZXXKAVYLXUJXWTVYNYCZXURXUSXWTXVLXJZXXAXVQX
        VMXWHXURXWSXWQVUTZYFBVXEXVQDEFVVCYGXXAVYLXUSXWHXXLXXPXXQXXRBVXEXVQEVVDY
        GVXEXXEXXBDVYJWUAVVEVVFXXGWVPXXFOZUDUOWYRXXDUDXXFXFWYRXXSXXDUDWYRXXSXXD
        WYRXXSTZXVOWVPUGZKXVTNZXXDXXSWYRWVPXXEOXYBXXFXXEWVPXXBXXEWOYHKWVPXVTCVV
        GVVHXXTXYAXXCKXVTXXTWVPXXBOZXYAXXCRXXSXYCWYRXXFXXBWVPXXBXXEWPYHVVIWVPXX
        BXVOVBUPVVKXKVVLXGVVJYEXWAXXDTXVSXXCTZKXVTNZXXAXVEXVSXXCKXVTVVMAXUJXUSX
        WTXYEXVERXVLAXUSTZXWTTZXVTSQZXYEXVDKXVTNXVEXWSXYHXYFXVMWUSVVNYDXYGXYDXV
        DKXVTXYGVXFXVTOZTZXVSXXCXVDXYJXXCXVSXVDXYGXYIXXCXVSXVDRXYGXYIXXCTZTXVRX
        VBUDXVCXYGXYKWVPXVCOZXVRXVBRXYGXYKXYLTZTZXVRXVPXVOVXEBXRZYIXRZWUBXSXPZX
        VBXYNXVRXYPXVQXVQYIXRZXSXPZXYQXYNXVRXYOXVQXSXPZXYSXYNXXCXYTXYGXYIXXCXYL
        VVOXYNVYLXXOXUSXWJXXCXYTXOAVYLXUSXWTXYMVYNYJXYNXVQXYNXVMXWHXYFXVMXWSXYM
        VVPZXWQUPZYFAXUSXWTXYMVWAZXYNSEVXFCASECVTXUSXWTXYMJYJZXWTXYKVXFSOZXYFXY
        LXWSXYIYUEXVMXXCVXFWUSYKYLYLZYMZXVOBVXEXVQEVVQYNYAXYNXVPYQOZXYOYQOZXVQY
        QOZYUJXVRXYTTXYSRXYNVYMXWJXUTEOZYUHAVYMXUSXWTXYMGYJZYUGXYNSEWVPCYUDXYNY
        UEXYLWVPSOZYUFXYGXYKXYLVVRWVPVXFYKVAYMZXVOXUTBEYOYGZXYNVYMXWJXUSYUIYULY
        UGYUCXVOVXEBEYOYGZXYNXVQYUBYRZYUQXVPXYOXVQXVQVVSYNYSXYNXYRWUBXYPXSXYNWU
        BXYNWUBYUAVWBVVTVWCVWDXYNXVAXYPVWTXPZXYQXVBXYNVYMXWJYUKXUSYURYULYUGYUNY
        UCXUTVXEXVOBEVWEVWFXYNXVAYQOZXYPYQOWUBYQOYURXYQTXVBRXYNVYMYUKXUSYUSYULY
        UNYUCXUTVXEBEYOYGXYNXVPXYOYUOYUPVWGXYNWUBYUAYRXVAXYPWUBVWHYGVWIVWJYTVWK
        VWLXAWTVWMXVDKXVTSVWNVWOVWPXBYSYTXIXKVWQAXUHXUSXVFTXOXUJAUBXUTBVXEKUDCD
        XDESFVYNXEXWPAYUMTXUTVWRJVXAXJVWSVXBCVXEVXQVXCXHVXD $.
    $}

    $( One half of ~ heibor , that does not require any Choice.  A compact
       metric space is complete and totally bounded.  We prove completeness in
       ~ cmpcmet and total boundedness here, which follows trivially from the
       fact that the set of all ` r ` -balls is an open cover of ` X ` , so
       finitely many cover ` X ` .  (Contributed by Jeff Madsen,
       16-Jan-2014.) $)
    heibor1 $p |- ( ( D e. ( Met ` X ) /\ J e. Comp ) ->
                    ( D e. ( CMet ` X ) /\ D e. ( TotBnd ` X ) ) ) $=
      ( vx vy vz vr cfv wcel wa cv wi wral ralrimiva cuni wceq wrex cfn crp clm
      cmet ccmp ccmet ctotbnd cn wf ccau simpll simplr simprl simprr heibor1lem
      cdm expr c1 nnuz 1zzd simpl iscmet3 mpbird cbl co cab cpw cin wss metxmet
      cxmet cxr id rpxr blopn syl3an 3com23 eleq1a syl rexlimdva adantlr abssdv
      3expa ad2antrr mopnuni blcntr syl3an1 elabrex adantl elunii syl2anc nfre1
      ovex nfcv nfab nfuni dfss3f sylibr eqsstrrd unissd eqssd eqid cmpcov elin
      syl3anc ancom bitri anbi1i anass rexbii2 sylib eqcom eqeq1d anbi1d bitrid
      bitr2id elpwi ssabral anim2i biimtrdi reximdv mpd istotbnd sylanbrc jca )
      ACUBIJZBUCJZKZACUDIJZACUEIJZYFYGUFCELZUGZYIBUAIUNJZMZEAUHIZNYFYLEYMYFYIYM
      JZYJYKYFYNYJKZKAYIBCDYDYEYOUIYDYEYOUJYFYNYJUKYFYNYJULUMUOOYFAEBUPCUFUQDYF
      URYDYEUSZUTVAYFYDYIPZCQZFLZGLZHLZAVBIZVCZQZGCRZFYINZKZESRZHTNYHYPYFUUHHTY
      FUUATJZKZYIUUEFVDZVEZJZBPZYQQZKZESRZUUHUUJUUOEUULSVFZRZUUQUUJYEUUKBVGUUNU
      UKPZQUUSYDYEUUIUJUUJUUEFBYDUUIUUEYSBJZMYEYDUUIKZUUDUVAGCUVBYTCJZKZUUCBJZU
      UDUVAMYDUUIUVCUVEYDUVCUUIUVEYDACVIIJZUVCUVCUUIUUAVJJUVEACVHZUVCVKUUAVLAYT
      UUABCDVMVNVOWAUUCBYSVPVQVRVSVTZUUJUUNUUTUUJUUNCUUTUUJUVFCUUNQYDUVFYEUUIUV
      GWBABCDWCVQZUUJYTUUTJZGCNZCUUTVGYDUUIUVKYEUVBUVJGCUVDYTUUCJZUUCUUKJZUVJYD
      UUIUVCUVLYDUVCUUIUVLYDUVFUVCUUIUVLUVGAYTUUACWDWEVOWAUVCUVMUVBGFCUUCYTUUAU
      UBWKWFWGYTUUCUUKWHWIOVSGCUUTGCWLGUUKUUEGFUUDGCWJWMWNWOWPWQUUJUUKBUVHWRWSU
      UKBUUNEUUNWTXAXCUUOUUPEUURSYIUURJZUUOKYISJZUUMKZUUOKUVOUUPKUVNUVPUUOUVNUU
      MUVOKUVPYIUULSXBUUMUVOXDXEXFUVOUUMUUOXGXEXHXIUUJUUPUUGESUUJUUPYRUUMKZUUGU
      UPUUOUUMKUUJUVQUUMUUOXDUUJUUOYRUUMYRCYQQUUJUUOYQCXJUUJCUUNYQUVIXKXNXLXMUU
      MUUFYRUUMYIUUKVGUUFYIUUKXOUUEFYIXPXIXQXRXSXTOGEACFHYAYBYC $.

    ${
      heibor.3 $e |- K = { u | -. E. v e. ( ~P U i^i Fin ) u C_ U. v } $.
      ${
        heiborlem1.4 $e |- B e. _V $.
        $( Lemma for ~ heibor .  We work with a fixed open cover ` U `
           throughout.  The set ` K ` is the set of all subsets of ` X ` that
           admit no finite subcover of ` U ` .  (We wish to prove that ` K ` is
           empty.)  If a set ` C ` has no finite subcover, then any finite
           cover of ` C ` must contain a set that also has no finite subcover.
           (Contributed by Jeff Madsen, 23-Jan-2014.) $)
        heiborlem1 $p |- ( ( A e. Fin /\ C C_ U_ x e. A B /\ C e. K ) ->
                            E. x e. A B e. K ) $=
          ( vt cfn wcel wss wrex wa wn ciun cv cuni cpw wral wceq sseq1 rexbidv
          cin notbid elab2 con2bii ralbii ralnex bitr2i wf cfv wex unieq sseq2d
          wi ac6sfi adantr elab2g ibi crn frn ad2antrl inss1 sstrdi sspwuni vex
          ex sylib rnex uniex elpw sylibr wfo wfn dffn4 fofi syldan inss2 unifi
          ffn syl2anc elind adantlr simplr fnfvelrn sylan adantll elssuni uniss
          3syl sstr2 syl5com ralimdva iunss sstrd rspcev nsyl3 exlimdv biimtrid
          impr syld con4d 3impia ) DOPZFADEUAZQZFJPZEJPZADRZXJXLSZXOXMXOTZEBUBZ
          UCZQZBHUDZOUIZRZADUEZXPXMTZYDXNTZADUEXQYCYFADXNYCCUBZXSQZBYBRZTZYCTCE
          JMYGEUFZYIYCYKYHXTBYBYGEXSUGUHUJLUKULUMXNADUNUOXPYDDYBNUBZUPZEAUBZYLU
          QZUCZQZADUEZSZNURZYEXJYDYTVAXLXJYDYTXTYQABDYBNXRYOUFXSYPEXRYOUSUTVBVM
          VCXPYSYENXPYSYEXMFXSQZBYBRZXPYSSZXMUUBTZYJUUDCFJJYGFUFZYIUUBUUEYHUUAB
          YBYGFXSUGUHUJLVDVEUUCYLVFZUCZYBPZFUUGUCZQZUUBXJYSUUHXLXJYSSZYAOUUGUUK
          UUGHQZUUGYAPUUKUUFYAQUULUUKUUFYBYAYMUUFYBQXJYRDYBYLVGVHZYAOVIVJUUFHVK
          VNUUGHUUFYLNVLVOVPVQVRUUKUUFOPZUUFOQUUGOPXJYSDUUFYLVSZUUNUUKYLDVTZUUO
          YMUUPXJYRDYBYLWFZVHDYLWAVNDUUFYLWBWCUUKUUFYBOUUMYAOWDVJUUFWEWGWHWIUUC
          FXKUUIXJXLYSWJXJYSXKUUIQZXLUUKEUUIQZADUEZUURXJYMYRUUTXJYMSZYQUUSADUVA
          YNDPZSZYPUUIQZYQUUSUVCYOUUFPZYOUUGQUVDYMUVBUVEXJYMUUPUVBUVEUUQDYNYLWK
          WLWMYOUUFWNYOUUGWOWPEYPUUIWQWRWSXFADEUUIWTVRWIXAUUAUUJBUUGYBXRUUGUFXS
          UUIFXRUUGUSUTXBWGXCVMXDXGXEXHXI $.
      $}

      heibor.4 $e |- G = { <. y , n >. |
                          ( n e. NN0 /\ y e. ( F ` n ) /\ ( y B n ) e. K ) } $.
      ${
        heiborlem2.5 $e |- A e. _V $.
        heiborlem2.6 $e |- C e. _V $.
        $( Lemma for ~ heibor .  Substitutions for the set ` G ` .
           (Contributed by Jeff Madsen, 23-Jan-2014.) $)
        heiborlem2 $p |- ( A G C <-> ( C e. NN0 /\
                            A e. ( F ` C ) /\ ( A B C ) e. K ) ) $=
          ( cn0 wcel cv cfv co w3a wceq eleq1 oveq1 eleq1d 3anbi23d fveq2 oveq2
          eleq2d 3anbi123d brab ) IUAZSTZAUAZUOJUBZTZUQUOEUCZMTZUDUPDURTZDUOEUC
          ZMTZUDFSTZDFJUBZTZDFEUCZMTZUDAIDFKQRUQDUEZUSVBVAVDUPUQDURUFVJUTVCMUQD
          UOEUGUHUIUOFUEZUPVEVBVGVDVIUOFSUFVKURVFDUOFJUJULVKVCVHMUOFDEUKUHUMPUN
          $.
      $}

      $d x B $.
      heibor.5 $e |- B = ( z e. X , m e. NN0 |->
                            ( z ( ball ` D ) ( 1 / ( 2 ^ m ) ) ) ) $.
      heibor.6 $e |- ( ph -> D e. ( CMet ` X ) ) $.
      heibor.7 $e |- ( ph -> F : NN0 --> ( ~P X i^i Fin ) ) $.
      heibor.8 $e |- ( ph -> A. n e. NN0 X = U_ y e. ( F ` n ) ( y B n ) ) $.
      $( Lemma for ~ heibor .  Using countable choice ~ ax-cc , we have fixed
         in advance a collection of finite ` 2 ^ -u n ` nets ` ( F `` n ) ` for
         ` X ` (note that an ` r ` -net is a set of points in ` X ` whose ` r `
         -balls cover ` X ` ).  The set ` G ` is the subset of these points
         whose corresponding balls have no finite subcover (i.e. in the set
         ` K ` ).  If the theorem was false, then ` X ` would be in ` K ` , and
         so some ball at each level would also be in ` K ` .  But we can say
         more than this; given a ball ` ( y B n ) ` on level ` n ` , since
         level ` n + 1 ` covers the space and thus also ` ( y B n ) ` , using
         ~ heiborlem1 there is a ball on the next level whose intersection with
         ` ( y B n ) ` also has no finite subcover.  Now since the set ` G ` is
         a countable union of finite sets, it is countable (which needs ~ ax-cc
         via ~ iunctb ), and so we can apply ~ ax-cc to ` G ` directly to get a
         function from ` G ` to itself, which points from each ball in ` K ` to
         a ball on the next level in ` K ` , and such that the intersection
         between these balls is also in ` K ` .  (Contributed by Jeff Madsen,
         18-Jan-2014.) $)
      heiborlem3 $p |- ( ph -> E. g A. x e. G
          ( ( g ` x ) G ( ( 2nd ` x ) + 1 ) /\
            ( ( B ` x ) i^i ( ( g ` x ) B ( ( 2nd ` x ) + 1 ) ) ) e. K ) ) $=
        ( vt cuni cv wf cfv c2nd c1 caddc co wbr cin wcel wa wral wex cdom wrex
        com cn0 csn cxp ciun cvv wss nn0ex fvex vsnex xpex iunex c1st wrel wceq
        cop w3a relopabiv 1st2nd mpan eleq1d bitr4di heiborlem2 bitrdi ibi snid
        df-br opelxp mpbiran2 fveq2 xpeq12d eleq2d rspcev sylan2br eliun sylibr
        sneq 3adant3 syl eqeltrd ssriv ssdomg mp2 cn nn0ennn nnenom entri endom
        cen ax-mp vex xpsnen cfn inss2 ffvelcdmda sselid csdm sylancr ralrimiva
        cpw ffvelcdm syl2an oveq1 eqtrid oveq2 eqtrd ineq2d c2 cexp cdiv adantl
        elpwid oveq2d ovex syl2anc adantr syl3anc sylib heiborlem1 sylbi iunctb
        isfinite sdomdom endomtr domtr simp1d peano2nn0 cbviunv iuneq1d iuneq2d
        iunin2 eqeq2d rspccva cbl fveq2d df-ov eqtr4di inss1 simp2d ovmpo cxmet
        sseldd cxr ccmet cmetmet metxmet 2nn nnexpcl nnrpd rpreccld rpxrd blssm
        cmet eqsstrd dfss2 eqtr3d eqimss2 simp3d mopnuni sseqtrd sselda adantrr
        inex1 id unisn uniiun eqtr3i sseqtri mp3an12 eleq1 rexsn biimpri syl3an
        snfi 3expb simprr jca32 ex reximdv2 mpd cmopn fvexi uniex breq1 anbi12d
        axcc4dom exsimpr ) ANOUFZJUGZUHZBUGZUXJUIZUXLUJUIZUKULUMZNUNZUXLGUIZUXM
        UXOGUMZUOZPUPZUQZBNURZUQJUSZUYBJUSANVBUTUNZUEUGZUXONUNZUXQUYEUXOGUMZUOZ
        PUPZUQZUEUXIVAZBNURUYCANUEVCUYEMUIZUYEVDZVEZVFZUTUNZUYOVBUTUNZUYDUYOVGU
        PNUYOVHUYPUEVCUYNVIUYLUYMUYEMVJZUEVKVLVMBNUYOUXLNUPZUXLUXLVNUIZUXNVQZUY
        ONVOUYSUXLVUAVPLUGZVCUPCUGZVUBMUIZUPVUCVUBGUMZPUPVRCLNTVSUXLNVTWAZUYSUX
        NVCUPZUYTUXNMUIZUPZUYTUXNGUMZPUPZVRZVUAUYOUPZUYSVULUYSUYSUYTUXNNUNZVULU
        YSUYSVUANUPVUNUYSUXLVUANVUFWBUYTUXNNWHWCCEFUYTGUXNHILMNOPRSTUXLVNVJUXLU
        JVJZWDWEWFZVUGVUIVUMVUKVUGVUIUQVUAUYNUPZUEVCVAZVUMVUIVUGVUAVUHUXNVDZVEZ
        UPZVURVVAVUIUXNVUSUPUXNVUOWGUYTUXNVUHVUSWIWJVUQVVAUEUXNVCUYEUXNVPZUYNVU
        TVUAVVBUYLVUHUYMVUSUYEUXNMWKUYEUXNWRWLWMWNWOUEVUAVCUYNWPWQWSWTXAXBNUYOV
        GXCXDAVCVBUTUNZUYNVBUTUNZUEVCURUYQVCVBXJUNVVCVCXEVBXFXGXHVCVBXIXKAVVDUE
        VCAUYEVCUPUQZUYNUYLXJUNUYLVBUTUNZVVDUYLUYEUYRUEXLZXMVVEUYLXNUPZVVFVVEQY
        AZXNUOZXNUYLVVIXNXOZAVCVVJUYEMUCXPXQVVHUYLVBXRUNVVFUYLUUCUYLVBUUDUUAWTU
        YNUYLVBUUEXSXTUEVCUYNUUBXSNUYOVBUUFXSAUYKBNAUYSUQZUYIUEUXOMUIZVAZUYKVVL
        VVMXNUPUXQUEVVMUYHVFZVHZUXQPUPZVVNVVLVVJXNVVMVVKAVCVVJMUHZUXOVCUPZVVMVV
        JUPUYSUCUYSVUGVVSUYSVUGVUIVUKVUPUUGZUXNUUHWTZVCVVJUXOMYBYCZXQVVLVVOUXQV
        PVVPVVLVVOUXQUEVVMUYGVFZUOZUXQUEVVMUXQUYGUULVVLUXQQUOZVWDUXQVVLQVWCUXQA
        QCVUDVUEVFZVPZLVCURVVSQVWCVPZUYSUDVWAVWGVWHLUXOVCVUBUXOVPZVWFVWCQVWIVWF
        UEVVMUYEVUBGUMZVFZVWCVWIVWFUEVUDVWJVFVWKCUEVUDVUEVWJVUCUYEVUBGYDUUIVWIU
        EVUDVVMVWJVUBUXOMWKUUJYEVWIUEVVMVWJUYGVUBUXOUYEGYFUUKYGUUMUUNYCYHVVLUXQ
        QVHVWEUXQVPVVLUXQUYTUKYIUXNYJUMZYKUMZHUUOUIZUMZQVVLUXQVUJVWOUYSUXQVUJVP
        AUYSUXQVUAGUIVUJUYSUXLVUAGVUFUUPUYTUXNGUUQUURZYLVVLUYTQUPZVUGVUJVWOVPVV
        LVUHQUYTVVLVUHQVVLVVJVVIVUHVVIXNUUSZAVVRVUGVUHVVJUPUYSUCVVTVCVVJUXNMYBY
        CXQYMUYSVUIAUYSVUGVUIVUKVUPUUTYLUVCZUYSVUGAVVTYLZDKUYTUXNQVCDUGZUKYIKUG
        ZYJUMZYKUMZVWNUMVWOGUYTVXDVWNUMVXAUYTVXDVWNYDVXBUXNVPZVXDVWMUYTVWNVXEVX
        CVWLUKYKVXBUXNYIYJYFYNYNUAUYTVWMVWNYOUVAYPYGVVLHQUVBUIUPZVWQVWMUVDUPVWO
        QVHAVXFUYSAHQUVNUIUPZVXFAHQUVEUIUPVXGUBHQUVFWTHQUVGWTZYQVWSVVLVWMVVLVWL
        VVLVWLVVLYIXEUPVUGVWLXEUPUVHVWTYIUXNUVIXSUVJUVKUVLHUYTVWMQUVMYRUVOUXQQU
        VPYSUVQYEUXQVVOUVRWTUYSVVQAUYSUXQVUJPVWPUYSVUGVUIVUKVUPUVSXAYLUEEFVVMUY
        HUXQHIOPRSUXQUYGUXLGVJUWDYTYRVVLUYIUYJUEVVMUXIVVLUYEVVMUPZUYIUQZUYEUXIU
        PZUYJUQVVLVXJUQVXKUYFUYIVVLVXIVXKUYIVVLVVMUXIUYEVVLVVMQUXIVVLVVMQVVLVVJ
        VVIVVMVWRVWBXQYMAQUXIVPZUYSAVXFVXLVXHHOQRUVTWTYQUWAUWBUWCVVLVXIUYIUYFVV
        LVVSVXIVXIUYIUYGPUPZUYFUYSVVSAVWAYLVXIUWEUYIUXJPUPZJUYGVDZVAZVXMVXOXNUP
        UYHJVXOUXJVFZVHUYIVXPUYGUWOUYHUYGVXQUXQUYGXOVXOUFUYGVXQUYGUYEUXOGYOZUWF
        JVXOUWGUWHUWIJEFVXOUXJUYHHIOPRSJXLYTUWJVXNVXMJUYGVXRUXJUYGPUWKUWLYSUYFV
        VSVXIVXMVRCEFUYEGUXOHILMNOPRSTVVGUXNUKULYOWDUWMUWNUWPVVLVXIUYIUWQUWRUWS
        UWTUXAXTUYJUYAUEUXIJBNOOHUXBRUXCUXDUYEUXMVPZUYFUXPUYIUXTUYEUXMUXONUXEVX
        SUYHUXSPVXSUYGUXRUXQUYEUXMUXOGYDYHWBUXFUXGYPUXKUYBJUXHWT $.

      ${
        heibor.9 $e |- ( ph -> A. x e. G
             ( ( T ` x ) G ( ( 2nd ` x ) + 1 ) /\
              ( ( B ` x ) i^i ( ( T ` x ) B ( ( 2nd ` x ) + 1 ) ) ) e. K ) ) $.
        heibor.10 $e |- ( ph -> C G 0 ) $.
        heibor.11 $e |- S = seq 0 ( T ,
                           ( m e. NN0 |-> if ( m = 0 , C , ( m - 1 ) ) ) ) $.
        $( Lemma for ~ heibor .  Using the function ` T ` constructed in
           ~ heiborlem3 , construct an infinite path in ` G ` .  (Contributed
           by Jeff Madsen, 23-Jan-2014.) $)
        heiborlem4 $p |- ( ( ph /\ A e. NN0 ) -> ( S ` A ) G A ) $=
          ( vk cn0 wcel cfv wbr cv wi cc0 c1 caddc co wceq fveq2 breq12d imbi2d
          id cmin cif cmpt cseq fveq1i cz 0z seq1 ax-mp eqtri cvv w3a relopabiv
          0nn0 brrelex1i syl iftrue eqid fvmptg sylancr eqtrid eqbrtrd wa df-br
          cin cop c2nd wral df-ov eqtr4di fvex vex op2ndd oveq1d oveq12d eleq1d
          ineq12d anbi12d rspccv biimtrid cuz seqp1 nn0uz eleq2s oveq1i 3eqtr4g
          eqeq1 oveq1 ifbieq2d peano2nn0 cn wn nn0p1nn neneqd iffalse 3syl ovex
          nnne0 eqeltrdi fvmptd3 nn0cn ax-1cn pncan sylancl 3eqtrd oveq2d eqtrd
          cc breq1d biimprd adantrd syl9r a2d nn0ind impcom ) GULUMAGKUNZGQUOZA
          BUPZKUNZUUDQUOZUQAURKUNZURQUOZUQAUKUPZKUNZUUIQUOZUQAUUIUSUTVAZKUNZUUL
          QUOZUQAUUCUQBUKGUUDURVBZUUFUUHAUUOUUEUUGUUDURQUUDURKVCUUOVFVDVEUUDUUI
          VBZUUFUUKAUUPUUEUUJUUDUUIQUUDUUIKVCUUPVFVDVEUUDUULVBZUUFUUNAUUQUUEUUM
          UUDUULQUUDUULKVCUUQVFVDVEUUDGVBZUUFUUCAUURUUEUUBUUDGQUUDGKVCUURVFVDVE
          AUUGIURQAUUGURNULNUPZURVBZIUUSUSVGVAZVHZVIZUNZIUUGURLUVCURVJZUNZUVDUR
          KUVEUJVKURVLUMUVFUVDVBVMLUVCURVNVOVPAURULUMIVQUMZUVDIVBVTAIURQUOUVGUI
          IURQOUPZULUMCUPZUVHPUNUMUVIUVHHVASUMVRCOQUCVSWAWBNURUVBIULVQUVCUUTIUV
          AWCUVCWDZWEWFWGUIWHUUIULUMZAUUKUUNAUUKUUJUUILVAZUULQUOZUUJUUIHVAZUVLU
          ULHVAZWKZSUMZWIZUVKUUNUUKUUJUUIWLZQUMZAUVRUUJUUIQWJAUUDLUNZUUDWMUNZUS
          UTVAZQUOZUUDHUNZUWAUWCHVAZWKZSUMZWIZBQWNUVTUVRUQUHUWIUVRBUVSQUUDUVSVB
          ZUWDUVMUWHUVQUWJUWAUVLUWCUULQUWJUWAUVSLUNUVLUUDUVSLVCUUJUUILWOWPZUWJU
          WBUUIUSUTUUJUUIUUDUUIKWQUKWRWSWTZVDUWJUWGUVPSUWJUWEUVNUWFUVOUWJUWEUVS
          HUNUVNUUDUVSHVCUUJUUIHWOWPUWJUWAUVLUWCUULHUWKUWLXAXCXBXDXEWBXFUVKUVMU
          UNUVQUVKUUNUVMUVKUUMUVLUULQUVKUUMUUJUULUVCUNZLVAZUVLUVKUULUVEUNZUUIUV
          EUNZUWMLVAZUUMUWNUWOUWQVBUUIURXGUNULLUVCURUUIXHXIXJUULKUVEUJVKUUJUWPU
          WMLUUIKUVEUJVKXKXLUVKUWMUUIUUJLUVKUWMUULURVBZIUULUSVGVAZVHZUWSUUIUVKN
          UULUVBUWTULUVCVQUVJUUSUULVBUUTUWRUVAUWSIUUSUULURXMUUSUULUSVGXNXOUUIXP
          UVKUWTUWSVQUVKUULXQUMZUWRXRUWTUWSVBUUIXSUXAUULURUULYDXTUWRIUWSYAYBZUU
          LUSVGYCYEYFUXBUVKUUIYNUMUSYNUMUWSUUIVBUUIYGYHUUIUSYIYJYKYLYMYOYPYQYRY
          SYTUUA $.

        heibor.12 $e |- M = ( n e. NN |->
                            <. ( S ` n ) , ( 3 / ( 2 ^ n ) ) >. ) $.
        $( Lemma for ~ heibor .  The function ` M ` is a set of
           point-and-radius pairs suitable for application to ~ caubl .
           (Contributed by Jeff Madsen, 23-Jan-2014.) $)
        heiborlem5 $p |- ( ph -> M : NN --> ( X X. RR+ ) ) $=
          ( vk cv cfv c3 c2 cexp co cdiv cop crp cxp wcel cn wral cn0 nnnn0 cpw
          wf wa cfn cin ffvelcdmda sselid elpwid wbr heiborlem4 fvex heiborlem2
          inss1 vex simp2bi sseldd sylan2 ralrimiva fveq2 eleq1d cbvralvw sylib
          syl weq wi 3re 3pos elrpii 2nn nnexpcl sylancr rpdivcl opelxpi expcom
          nnrpd ralimia fmpt ) ANUMZJUNZUOUPXEUQURZUSURZUTZTVAVBZVCZNVDVEZVDXJS
          VIAXFTVCZNVDVEZXLAULUMZJUNZTVCZULVDVEXNAXQULVDXOVDVCAXOVFVCZXQXOVGAXR
          VJZXOOUNZTXPXSXTTXSTVHZVKVLZYAXTYAVKVTAVFYBXOOUFVMVNVOXSXPXOPVPZXPXTV
          CZABCDEFXOGHIJKLMNOPQRTUAUBUCUDUEUFUGUHUIUJVQYCXRYDXPXOGURRVCCEFXPGXO
          ILNOPQRUAUBUCXOJVRULWAVSWBWJWCWDWEXQXMULNVDULNWKXPXFTXOXEJWFWGWHWIXMX
          KNVDXEVDVCZXHVAVCZXMXKWLYEUOVAVCXGVAVCYFUOWMWNWOYEXGYEUPVDVCXEVFVCXGV
          DVCWPXEVGUPXEWQWRXBUOXGWSWRXMYFXKXFXHTVAWTXAWJXCWJNVDXJXISUKXDWI $.

        $( Lemma for ~ heibor .  Since the sequence of balls connected by the
           function ` T ` ensures that each ball nontrivially intersects with
           the next (since the empty set has a finite subcover, the
           intersection of any two successive balls in the sequence is
           nonempty), and each ball is half the size of the previous one, the
           distance between the centers is at most ` 3 / 2 ` times the size of
           the larger, and so if we expand each ball by a factor of ` 3 ` we
           get a nested sequence of balls.  (Contributed by Jeff Madsen,
           23-Jan-2014.) $)
        heiborlem6 $p |- ( ph -> A. k e. NN
      ( ( ball ` D ) ` ( M ` ( k + 1 ) ) ) C_ ( ( ball ` D ) ` ( M ` k ) ) ) $=
          ( cv c1 caddc co cfv wss cn wcel wa c3 cexp cdiv cn0 cmin cle wbr syl
          c2 cr adantr cpw wf cfn cin sylancl elpwid heiborlem4 fvex heiborlem2
          sylan2 ovex simp2bi sseldd crp 3re 2nn nnexpcl nnrpd adantl rerpdivcl
          sylancr mpan wn c0 wne wceq oveq1 weq oveq2 oveq2d ovmpo wi cop fveq2
          df-ov eqtr4di oveq1d oveq12d ineq12d syl2anc cuni wrex rpreccld rpred
          mpd cxr rpxrd syl3anc cc0 cif fveq1i oveq1i cvv ax-1cn eqtrd cmul 3cn
          cc rpcn rpne0 2cn mp3an12 2cnne0 divcan5 mp3an13 eqtr3d opeq12d opex
          cbl nnnn0 cxmet cmet ccmet cmetmet metxmet inss1 fss peano2nn0 syl2an
          ffvelcdm ffvelcdmda sylancom df-br c2nd op2ndd breq12d eleq1d anbi12d
          vex wral rspccv biimtrid simpld simprd 0elpw 0fi elin mpbir2an sseq2d
          0ss unieq rspcev mp2an sseq1 rexbidv notbid elab2 con2bii mpbi nelne2
          0ex eqnetrrd rexadd breq1d w3a bldisj 3exp2 syl32anc sylbird necon3ad
          cxad imp32 rpaddcld metcl letrid ord cmpt cseq cuz seqp1 nn0uz eleq2s
          3eqtr4g eqeq1 ifbieq2d nn0p1nn nnne0 neneqd iffalsed eqeltrdi fvmptd3
          eqid nn0cn pncan 3eqtrd metsym 2timesi pncan3oi df-3 3eqtri divsubdir
          mulcli divdir 3eqtr3a mulcom expp1 eqtr4d 2t1e2 3eqtr4d 3brtr4d blss2
          a1i syl33anc peano2nn fvmpt fveq2d 3sstr4d ralrimiva ) AMUMZUNUOUPZTU
          QZIUUAUQZUQZVUATUQZVUDUQZURMUSAVUAUSUTZVAZVUBJUQZVBVJVUBVCUPZVDUPZVUD
          UPZVUAJUQZVBVJVUAVCUPZVDUPZVUDUPZVUEVUGVUHAVUAVEUTZVUMVUQURZVUAUUBAVU
          RVAZIUAUUCUQUTZVUJUAUTVUNUAUTZVULVKUTZVUPVKUTZVUJVUNIUPZVUPVULVFUPZVG
          VHVUSAVVAVURAIUAUUDUQUTZVVAAIUAUUEUQUTVVGUFIUAUUFVIZIUAUUGVIVLZVUTVUB
          PUQZUAVUJVUTVVJUAAVEUAVMZPVNZVUBVEUTZVVJVVKUTVURAVEVVKVOVPZPVNVVNVVKU
          RVVLUGVVKVOUUHVEVVNVVKPUUIVQZVUAUUJZVEVVKVUBPUULUUKVRZVUTVUJVUBQVHZVU
          JVVJUTZVURAVVMVVRVVPABCDEFVUBGHIJKLNOPQRSUAUBUCUDUEUFUGUHUIUJUKVSWBVV
          RVVMVVSVUJVUBGUPSUTCEFVUJGVUBILOPQRSUBUCUDVUBJVTVUAUNUOWCZWAWDVIWEVUT
          VUAPUQZUAVUNVUTVWAUAAVEVVKVUAPVVOUUMVRVUTVUNVUAQVHZVUNVWAUTZABCDEFVUA
          GHIJKLNOPQRSUAUBUCUDUEUFUGUHUIUJUKVSZVWBVURVWCVUNVUAGUPZSUTCEFVUNGVUA
          ILOPQRSUBUCUDVUAJVTZMUVAZWAWDVIWEZVUTVBVKUTZVUKWFUTZVVCWGVURVWJAVURVU
          KVURVJUSUTZVVMVUKUSUTWHVVPVJVUBWIWMWJZWKVBVUKWLWMVUTVWIVUOWFUTZVVDWGV
          URVWMAVURVUOVWKVURVUOUSUTWHVJVUAWIWNWJZWKVBVUOWLWMVUTVUNVUNVUAKUPZIUP
          ZUNVUOVDUPZUNVUKVDUPZUOUPZVVEVVFVGVUTVWSVWPVGVHZWOZVWPVWSVGVHZVUTVUNV
          WQVUDUPZVWOVWRVUDUPZVPZWPWQVXAVUTVWEVWOVUBGUPZVPZVXEWPVUTVWEVXCVXFVXD
          AVURVVBVWEVXCWRVWHDNVUNVUAUAVEDUMZUNVJNUMZVCUPZVDUPZVUDUPZVXCGVUNVXKV
          UDUPVXHVUNVXKVUDWSNMWTZVXKVWQVUNVUDVXMVXJVUOUNVDVXIVUAVJVCXAXBXBUEVUN
          VWQVUDWCXCUUNVUTVWOUAUTZVVMVXFVXDWRVUTVVJUAVWOVVQVUTVWOVUBQVHZVWOVVJU
          TZVUTVXOVXGSUTZVUTVWBVXOVXQVAZVWDAVWBVXRXDVURVWBVUNVUAXEZQUTZAVXRVUNV
          UAQUUOABUMZKUQZVYAUUPUQZUNUOUPZQVHZVYAGUQZVYBVYDGUPZVPZSUTZVAZBQUVBVX
          TVXRXDUIVYJVXRBVXSQVYAVXSWRZVYEVXOVYIVXQVYKVYBVWOVYDVUBQVYKVYBVXSKUQV
          WOVYAVXSKXFVUNVUAKXGXHZVYKVYCVUAUNUOVUNVUAVYAVWFVWGUUQXIZUURVYKVYHVXG
          SVYKVYFVWEVYGVXFVYKVYFVXSGUQVWEVYAVXSGXFVUNVUAGXGXHVYKVYBVWOVYDVUBGVY
          LVYMXJXKUUSUUTUVCVIUVDVLXQZUVEVXOVVMVXPVXFSUTCEFVWOGVUBILOPQRSUBUCUDV
          UNVUAKWCVVTWAWDVIWEZVURVVMAVVPWKDNVWOVUBUAVEVXLVXDGVWOVXKVUDUPVXHVWOV
          XKVUDWSVXIVUBWRZVXKVWRVWOVUDVYPVXJVUKUNVDVXIVUBVJVCXAXBXBUEVWOVWRVUDW
          CXCXLXKVUTVXQWPSUTZWOZVXGWPWQVUTVXOVXQVYNUVFWPEUMZXMZURZELVMZVOVPZXNZ
          VYRWPWUCUTZWPWPXMZURZWUDWUEWPWUBUTWPVOUTLUVGUVHWPWUBVOUVIUVJWUFUVLWUA
          WUGEWPWUCVYSWPWRVYTWUFWPVYSWPUVMUVKUVNUVOVYQWUDFUMZVYTURZEWUCXNZWOWUD
          WOFWPSUWCWUHWPWRZWUJWUDWUKWUIWUAEWUCWUHWPVYTUVPUVQUVRUCUVSUVTUWAVXGWP
          SUWBVQUWDVUTVWTVXEWPVUTVWTVWQVWRUWMUPZVWPVGVHZVXEWPWRZVUTWULVWSVWPVGV
          UTVWQVKUTVWRVKUTWULVWSWRVUTVWQVURVWQWFUTAVURVUOVWNXOWKZXPVUTVWRVURVWR
          WFUTAVURVUKVWLXOWKZXPVWQVWRUWEXLUWFVUTVVAVVBVXNVWQXRUTZVWRXRUTZWUMWUN
          XDZVVIVWHVYOVUTVWQWUOXSVUTVWRWUPXSVVAVVBVXNUWGZWUQWURWUSWUTWUQWURWUMW
          UNIVUNVWOVWQVWRUAUWHUWIUWNUWJUWKUWLXQVUTVWTVXBVUTVWSVWPVUTVWSVUTVWQVW
          RWUOWUPUWOXPVUTVVGVVBVXNVWPVKUTAVVGVURVVHVLZVWHVYOVUNVWOIUAUWPXTUWQUW
          RXQVUTVVEVWOVUNIUPZVWPVUTVUJVWOVUNIVURVUJVWOWRAVURVUJVUNVUBNVEVXIYAWR
          ZHVXIUNVFUPZYBZUWSZUQZKUPZVWOVURVUBKWVFYAUWTZUQZVUAWVIUQZWVGKUPZVUJWV
          HWVJWVLWRVUAYAUXAUQVEKWVFYAVUAUXBUXCUXDVUBJWVIUKYCVUNWVKWVGKVUAJWVIUK
          YCYDUXEVURWVGVUAVUNKVURWVGVUBYAWRZHVUBUNVFUPZYBZWVNVUAVURNVUBWVEWVOVE
          WVFYEWVFUXNVYPWVCWVMWVDWVNHVXIVUBYAUXFVXIVUBUNVFWSUXGVVPVURWVOWVNYEVU
          RWVMHWVNVURVUBUSUTZWVMWOVUAUXHWVPVUBYAVUBUXIUXJVIUXKZVUBUNVFWCUXLUXMW
          VQVURVUAYJUTUNYJUTZWVNVUAWRVUAUXOYFVUAUNUXPVQUXQXBYGWKXIVUTVVGVXNVVBW
          VBVWPWRWVAVYOVWHVWOVUNIUAUXRXTYGVURVVFVWSWRAVURVJVBYHUPZVUKVDUPZVULVF
          UPZVJVUKVDUPZVWRUOUPZVVFVWSVURWVSVBVFUPZVUKVDUPZVJUNUOUPZVUKVDUPZWWAW
          WCWWDWWFVUKVDWWDVBVBUOUPZVBVFUPVBWWFWVSWWHVBVFVBYIUXSYDVBVBYIYIUXTUYA
          UYBYDVURVWJWWEWWAWRZVWLVWJVUKYJUTZVUKYAWQZWWIVUKYKZVUKYLZWVSYJUTVBYJU
          TZWWJWWKVAZWWIVJVBYMYIUYDYIWVSVBVUKUYCYNXLVIVURVWJWWGWWCWRZVWLVWJWWJW
          WKWWPWWLWWMVJYJUTZWVRWWOWWPYMYFVJUNVUKUYEYNXLVIUYFVURVUPWVTVULVFVURWV
          SVJVUOYHUPZVDUPZVUPWVTVURVWMWWSVUPWRZVWNVWMVUOYJUTZVUOYAWQZWWTVUOYKZV
          UOYLZWWNWXAWXBVAZWWQVJYAWQVAZWWTYIYOVBVUOVJYPYQXLVIVURWWRVUKWVSVDVURW
          WRVUOVJYHUPZVUKVURWWQWXAWWRWXGWRYMVURVWMWXAVWNWXCVIVJVUOUYGWMWWQVURVU
          KWXGWRYMVJVUAUYHWNUYIZXBYRXIVURVWQWWBVWRUOVURVJUNYHUPZWWRVDUPZVWQWWBV
          URVWMWXJVWQWRZVWNVWMWXAWXBWXKWXCWXDWVRWXEWXFWXKYFYOUNVUOVJYPYQXLVIVUR
          WXIVJWWRVUKVDWXIVJWRVURUYJUYNWXHXJYRXIUYKWKUYLIVUJVUNVULVUPUAUYMUYOWB
          VUIVUEVUJVULXEZVUDUQVUMVUIVUCWXLVUDVUHVUCWXLWRZAVUHWVPWXMVUAUYPOVUBOU
          MZJUQZVBVJWXNVCUPZVDUPZXEZWXLUSTWXNVUBWRZWXOVUJWXQVULWXNVUBJXFWXSWXPV
          UKVBVDWXNVUBVJVCXAXBYSULVUJVULYTUYQVIWKUYRVUJVULVUDXGXHVUHVUGVUQWRAVU
          HVUGVUNVUPXEZVUDUQVUQVUHVUFWXTVUDOVUAWXRWXTUSTOMWTZWXOVUNWXQVUPWXNVUA
          JXFWYAWXPVUOVBVDWXNVUAVJVCXAXBYSULVUNVUPYTUYQUYRVUNVUPVUDXGXHWKUYSUYT
          $.

        $( Lemma for ~ heibor .  Since the sizes of the balls decrease
           exponentially, the sequence converges to zero.  (Contributed by Jeff
           Madsen, 23-Jan-2014.) $)
        heiborlem7 $p |- A. r e. RR+ E. k e. NN ( 2nd ` ( M ` k ) ) < r $=
          ( cv cfv c2nd clt wbr cn wrex crp wcel c3 c2 cexp co cdiv c1 3re 3pos
          elrpii rpdivcl mpan2 cr 2re 1lt2 expnlbnd mp3an23 syl wa cmul cn0 2nn
          wceq nnnn0 nnexpcl sylancr nnrpd cc0 wne rpcn rpne0 3cn divrec mp3an1
          cc syl2anc adantl breq1d nnrecred rpre pm3.2i ltmuldiv2 syl2anr bitrd
          wb mp3an3 rexbidva mpbird cop fveq2 oveq2 oveq2d opeq12d fvmpt fveq2d
          opex fvex ovex op2nd eqtrdi rexbiia sylibr rgen ) MUNZTUOZUPUOZUBUNZU
          QURZMUSUTZUBVAYHVAVBZVCVDYEVEVFZVGVFZYHUQURZMUSUTZYJYKYOVHYLVGVFZYHVC
          VGVFZUQURZMUSUTZYKYQVAVBZYSYKVCVAVBYTVCVIVJVKYHVCVLVMYTVDVNVBVHVDUQUR
          YSVOVPYQVDMVQVRVSYKYNYRMUSYKYEUSVBZVTZYNVCYPWAVFZYHUQURZYRUUBYMUUCYHU
          QUUAYMUUCWDZYKUUAYLVAVBZUUEUUAYLUUAVDUSVBYEWBVBYLUSVBWCYEWEVDYEWFWGZW
          HUUFYLWPVBZYLWIWJZUUEYLWKYLWLVCWPVBUUHUUIUUEWMVCYLWNWOWQVSWRWSUUAYPVN
          VBZYHVNVBZUUDYRXFZYKUUAYLUUGWTYHXAUUJUUKVCVNVBZWIVCUQURZVTUULUUMUUNVI
          VJXBYPYHVCXCXGXDXEXHXIYIYNMUSUUAYGYMYHUQUUAYGYEJUOZYMXJZUPUOYMUUAYFUU
          PUPOYEOUNZJUOZVCVDUUQVEVFZVGVFZXJUUPUSTUUQYEWDZUURUUOUUTYMUUQYEJXKUVA
          UUSYLVCVGUUQYEVDVEXLXMXNUMUUOYMXQXOXPUUOYMYEJXRVCYLVGXSXTYAWSYBYCYD
          $.

        heibor.13 $e |- ( ph -> U C_ J ) $.
        ${
          heibor.14 $e |- Y e. _V $.
          heibor.15 $e |- ( ph -> Y e. Z ) $.
          heibor.16 $e |- ( ph -> Z e. U ) $.
          heibor.17 $e |- ( ph -> ( 1st o. M ) ( ~~>t ` J ) Y ) $.
          $( Lemma for ~ heibor .  The previous lemmas establish that the
             sequence ` M ` is Cauchy, so using completeness we now consider
             the convergent point ` Y ` .  By assumption, ` U ` is an open
             cover, so ` Y ` is an element of some ` Z e. U ` , and some ball
             centered at ` Y ` is contained in ` Z ` .  But the sequence
             contains arbitrarily small balls close to ` Y ` , so some element
             ` ball ( M `` n ) ` of the sequence is contained in ` Z ` .  And
             finally we arrive at a contradiction, because ` { Z } ` is a
             finite subcover of ` U ` that covers ` ball ( M `` n ) ` , yet
             ` ball ( M `` n ) e. K ` .  For convenience, we write this
             contradiction as ` ph -> ps ` where ` ph ` is all the accumulated
             hypotheses and ` ps ` is anything at all.  (Contributed by Jeff
             Madsen, 22-Jan-2014.) $)
          heiborlem8 $p |- ( ph -> ps ) $=
            ( vk vr vt cv cbl cfv co wss crp wrex cxmet wcel ccmet cmet cmetmet
            metxmet 3syl sseldd mopni2 syl3anc wa c2nd c2 cdiv clt wbr rphalfcl
            wn cn wceq breq2 rexbidv heiborlem7 vtoclri adantl nnnn0 heiborlem4
            syl cn0 fvex vex heiborlem2 simp3bi sylan2 ad2ant2r wi c1st c1 cexp
            cxr cle ad2antrr cxp heiborlem5 ffvelcdmda nnexpcl sylancr rpreccld
            xp1st 2nn nnrpd ad2antrl rpxrd xp2nd c3 1le3 cr oveq2 oveq2d fveq2d
            cop weq ovex eqtrdi syl2anc 3sstr3d cuni ad2antlr sstrd cfn sseq2d
            cc0 wb elrp 1re lediv1 mp3an12 sylbi mpbii fveq2 opeq12d opex fvmpt
            op2nd breqtrrd ssbl syl221anc oveq1 ovmpo op1st oveq1d eqtr3d df-ov
            3re 1st2nd2 eqtr4id ctop mopntop blssm mopnuni sscls simprr blsscls
            ccl eqid syl23anc eqsstrrd rpre ccom clm heiborlem6 caublcls 3expia
            mpdan imp blhalf syl22anc sstr2 cpw cin csn biimpar snssd snex elpw
            unisng sylibr snfi a1i elind unieq rspcev sylan syldan sseq1 notbid
            elab2 con2bii sylib ex syld mt2d rexlimddv nrexdv pm2.21dd ) AUBCVC
            ZJVDVEZVFZUCVGZCVHVIZBAJUAVJVEVKZUCRVKUBUCVKUXSAJUAVLVEVKJUAVMVEVKU
            XTUHJUAVNJUAVOVPZAMRUCUOURVQUQCUCJUBRUAUDVRVSAUXRCVHAUXOVHVKZVTZUTV
            CZTVEZWAVEZUXOWBWCVFZWDWEZUXRWGUTWHUYBUYHUTWHVIZAUYBUYGVHVKZUYIUXOW
            FZUYFVAVCZWDWEZUTWHVIUYIVAUYGVHUYLUYGWIUYMUYHUTWHUYLUYGUYFWDWJWKACD
            EFGHIJKLMUTNOPQRSTUAVAUDUEUFUGUHUIUJUKULUMUNWLWMWQWNUYCUYDWHVKZUYHV
            TZVTZUXRUYDKVEZUYDHVFZSVKZAUYNUYSUYBUYHUYNAUYDWRVKZUYSUYDWOZAUYTVTU
            YQUYDQWEZUYSACDEFGUYDHIJKLMNOPQRSUAUDUEUFUGUHUIUJUKULUMWPVUBUYTUYQU
            YDPVEVKUYSDFGUYQHUYDJMOPQRSUDUEUFUYDKWSZUTWTXAXBWQXCXDUYPUXRUYRUCVG
            ZUYSWGZUYPUYRUXQVGUXRVUDXEUYPUYRUYEUXPVEZUXQUYPUYEXFVEZXGWBUYDXHVFZ
            WCVFZUXPVFZVUGUYFUXPVFZUYRVUFUYPUXTVUGUAVKZVUIXIVKUYFXIVKZVUIUYFXJW
            EVUJVUKVGAUXTUYBUYOUYAXKZUYPUYEUAVHXLZVKZVULAUYNVUPUYBUYHAWHVUOUYDT
            ACDEFGHIJKLMNOPQRSTUAUDUEUFUGUHUIUJUKULUMUNXMZXNXDZUYEUAVHXRWQZUYPV
            UIUYNVUIVHVKUYCUYHUYNVUHUYNVUHUYNWBWHVKUYTVUHWHVKXSVUAWBUYDXOXPXTZX
            QYAYBUYPUYFUYPVUPUYFVHVKVURUYEUAVHYCWQYBZUYPVUIYDVUHWCVFZUYFXJUYNVU
            IVVBXJWEZUYCUYHUYNVUHVHVKZVVCVUTVVDXGYDXJWEZVVCYEVVDVUHYFVKUUAVUHWD
            WEVTZVVEVVCUUBZVUHUUCXGYFVKYDYFVKVVFVVGUUDUVCXGYDVUHUUEUUFUUGUUHWQY
            AUYNUYFVVBWIUYCUYHUYNUYFUYQVVBYJZWAVEVVBUYNUYEVVHWAOUYDOVCZKVEZYDWB
            VVIXHVFZWCVFZYJVVHWHTOUTYKZVVJUYQVVLVVBVVIUYDKUUIVVMVVKVUHYDWCVVIUY
            DWBXHYGYHUUJUNUYQVVBUUKUULZYIUYQVVBVUCYDVUHWCYLZUUMYMYAUUNJVUGVUIUY
            FUAUUOUUPUYPVUGUYDHVFZVUJUYRUYPVULUYTVVPVUJWIVUSUYNUYTUYCUYHVUAYAEN
            VUGUYDUAWREVCZXGWBNVCZXHVFZWCVFZUXPVFVUJHVUGVVTUXPVFVVQVUGVVTUXPUUQ
            NUTYKZVVTVUIVUGUXPVWAVVSVUHXGWCVVRUYDWBXHYGYHYHUGVUGVUIUXPYLUURYNUY
            PVUGUYQUYDHUYNVUGUYQWIUYCUYHUYNVUGVVHXFVEUYQUYNUYEVVHXFVVNYIUYQVVBV
            UCVVOUUSYMYAUUTUVAUYPVUKVUGUYFYJZUXPVEVUFVUGUYFUXPUVBUYPUYEVWBUXPUY
            PVUPUYEVWBWIVURUYEUAVHUVDWQYIUVEZYOUYPVUFVUFRUVMVEZVEZUXQUYPRUVFVKZ
            VUFRYPZVGVUFVWEVGUYPUXTVWFVUNJRUAUDUVGWQUYPVUKUAVUFVWGUYPUXTVULVUMV
            UKUAVGVUNVUSVVAJVUGUYFUAUVHVSVWCUYPUXTUAVWGWIVUNJRUAUDUVIWQYOVUFRVW
            GVWGUVNUVJYNUYPVWEVUGUYGUXPVFZUXQUYPVWEVUKVWDVEZVWHUYPVUKVUFVWDVWCY
            IUYPUXTVULVUMUYGXIVKUYHVWIVWHVGVUNVUSVVAUYPUYGUYBUYJAUYOUYKYQYBUYCU
            YNUYHUVKJVUGUYFUYGRUAUDUVLUVOUVPZUYPUXTVULUXOYFVKZUBVWHVKVWHUXQVGVU
            NVUSUYBVWKAUYOUXOUVQYQUYPVWEVWHUBVWJAUYNUBVWEVKZUYBUYHAUYNVWLAXFTUV
            RUBRUVSVEWEZUYNVWLXEUSAVWMUYNVWLAUYDJUBVBTRUAUYAVUQACDEFGHIJKLMVBNO
            PQRSTUAUDUEUFUGUHUIUJUKULUMUNUVTUDUWAUWBUWCUWDXDVQUXOJUAVUGUBUWEUWF
            YRYRYRUYRUXQUCUWGWQAVUDVUEXEUYBUYOAVUDVUEAVUDVTUYRFVCZYPZVGZFMUWHZY
            SUWIZVIZVUEAVUDUYRUCUWJZYPZVGZVWSAVXBVUDAVXAUCUYRAUCMVKVXAUCWIURUCM
            UWOWQYTUWKAVWTVWRVKVXBVWSAVWQYSVWTAVWTMVGVWTVWQVKAUCMURUWLVWTMUCUWM
            UWNUWPVWTYSVKAUCUWQUWRUWSVWPVXBFVWTVWRVWNVWTWIVWOVXAUYRVWNVWTUWTYTU
            XAUXBUXCUYSVWSGVCZVWOVGZFVWRVIZWGVWSWGGUYRSUYQUYDHYLVXCUYRWIZVXEVWS
            VXFVXDVWPFVWRVXCUYRVWOUXDWKUXEUEUXFUXGUXHUXIXKUXJUXKUXLUXMUXN $.
        $}

        heiborlem9.14 $e |- ( ph -> U. U = X ) $.
        $( Lemma for ~ heibor .  Discharge the hypotheses of ~ heiborlem8 by
           applying ~ caubl to get a convergent point and adding the open cover
           assumption.  (Contributed by Jeff Madsen, 20-Jan-2014.) $)
        heiborlem9 $p |- ( ph -> ps ) $=
          ( vt vk vr c1st ccom clm cfv cv wcel cuni wrex ctopon wbr cxmet ccmet
          cmet cmetmet metxmet 3syl mopntopon syl cdm heiborlem5 heiborlem6 clt
          ccau c2nd cn crp wral heiborlem7 a1i cmetcau syl2anc cha wfun methaus
          caubl wb lmfun funfvbrb mpbid eleqtrrd eluni2 sylib wa adantr cn0 cpw
          lmcl cfn cin wf co ciun wceq c1 cc0 wss fvex simprr simprl heiborlem8
          caddc rexlimddv ) AURTUSZRUTVAZVAZUOVBZVCZBUOMAYBMVDZVCYDUOMVEAYBUAYE
          ARUAVFVAVCZXTYBYAVGZYBUAVCAJUAVHVAVCZYFAJUAVIVAVCZJUAVJVAVCYHUFJUAVKJ
          UAVLVMZJRUAUBVNVOAXTYAVPVCZYGAYIXTJVTVAVCYKUFAJUPTUAUQYJACDEFGHIJKLMN
          OPQRSTUAUBUCUDUEUFUGUHUIUJUKULVQACDEFGHIJKLMUPNOPQRSTUAUBUCUDUEUFUGUH
          UIUJUKULVRUPVBTVAWAVAUQVBVSVGUPWBVEUQWCWDAACDEFGHIJKLMUPNOPQRSTUAUQUB
          UCUDUEUFUGUHUIUJUKULWEWFWLJXTRUAUBWGWHARWIVCZYAWJYKYGWMAYHYLYJJRUAUBW
          KVORWNXTYAWOVMWPZYBXTRUAXDWHUNWQUOYBMWRWSAYCMVCZYDWTZWTBCDEFGHIJKLMNO
          PQRSTUAYBYCUBUCUDUEAYIYOUFXAAXBUAXCXEXFPXGYOUGXAAUADOVBZPVADVBYPHXHXI
          XJOXBWDYOUHXAACVBZLVAZYQWAVAXKXRXHZQVGYQHVAYRYSHXHXFSVCWTCQWDYOUIXAAI
          XLQVGYOUJXAUKULAMRXMYOUMXAXTYAXNAYNYDXOAYNYDXPAYGYOYMXAXQXS $.
      $}

      $d v ph $.
      $( Lemma for ~ heibor .  The last remaining piece of the proof is to find
         an element ` C ` such that ` C G 0 ` , i.e. ` C ` is an element of
         ` ( F `` 0 ) ` that has no finite subcover, which is true by
         ~ heiborlem1 , since ` ( F `` 0 ) ` is a finite cover of ` X ` , which
         has no finite subcover.  Thus, the rest of the proof follows to a
         contradiction, and thus there must be a finite subcover of ` U ` that
         covers ` X ` , i.e. ` X ` is compact.  (Contributed by Jeff Madsen,
         22-Jan-2014.) $)
      heiborlem10 $p |- ( ( ph /\ ( U C_ J /\ U. J = U. U ) ) ->
                          E. v e. ( ~P U i^i Fin ) U. J = U. v ) $=
        ( vx vg vt wss cuni wceq wa cv cpw cfn cin wrex wcel wn cc0 co cfv ciun
        wi cn0 wf 0nn0 inss2 ffvelcdm sselid sylancl wral fveq2 iuneq12d eqeq2d
        oveq2 rspccva eqimss syl w3a heiborlem1 weq oveq1 eleq1d cbvrexvw sylib
        ovex 3expia syl2anc adantr wbr c0ex heiborlem2 c2nd c1 caddc heiborlem3
        vex wex ad2antrr cmin cif cmpt cseq cn c3 c2 cexp cdiv cop ccmet simprr
        oveq1d breq12d oveq12d ineq12d anbi12d cbvralvw simprl ifbieq2d cbvmptv
        eqeq1 seqeq3 ax-mp eqid simplrl cmet cxmet cmetmet metxmet mopnuni 4syl
        eqtr2d heiborlem9 expr exlimdv mpd sylan2br 3exp2 rexlimdv syld pm2.01d
        mpi wb cdm elfvdm sseq1 rexbidv notbid elab2g 3syl con2bid mpbird inss1
        sseq1d sseli elpwid sstr unissd syl2anr biantrud bitr4di bitrd rexbidva
        eqss mpbid ) AHMUFZMUGZHUGZUHZUIZUIZODUJZUGZUFZDHUKZULUMZUNZUVEUVKUHZDU
        VNUNUVIUVOONUOZUPZUVIUVQUVIUVQUCUJZUQFURZNUOZUCUQKUSZUNZUVRAUVQUWCVAZUV
        HAUWBULUOZOBUWBBUJZUQFURZUTZUFZUWDAVBOUKZULUMZKVCZUQVBUOZUWEUAVDUWLUWMU
        IUWKULUWBUWJULVEVBUWKUQKVFVGVHAOUWHUHZUWIAOBJUJZKUSZUWFUWOFURZUTZUHZJVB
        VIZUWMUWNUBVDUWSUWNJUQVBUWOUQUHZUWRUWHOUXABUWPUWBUWQUWGUWOUQKVJUWOUQUWF
        FVMVKVLVNVHOUWHVOVPUWEUWIUVQUWCUWEUWIUVQVQUWGNUOZBUWBUNUWCBDEUWBUWGOGHM
        NPQUWFUQFWDVRUXBUWABUCUWBBUCVSUWGUVTNUWFUVSUQFVTWAWBWCWEWFWGUVIUWAUVRUC
        UWBUVIUWMUVSUWBUOZUWAUVRVAVAVDUVIUWMUXCUWAUVRUWMUXCUWAVQUVIUVSUQLWHZUVR
        BDEUVSFUQGHJKLMNPQRUCWOWIWJUVIUXDUIZUVSUDUJZUSZUVSWKUSZWLWMURZLWHZUVSFU
        SZUXGUXIFURZUMZNUOZUIZUCLVIZUDWPZUVRAUXQUVHUXDAUCBCDEFGHUDIJKLMNOPQRSTU
        AUBWNWQUXEUXPUVRUDUVIUXDUXPUVRUVIUXDUXPUIZUIZUVRUEBCDEFUVSGUXFUDVBUXFUQ
        UHZUVSUXFWLWRURZWSZWTZUQXAZUXFHIJKLMNJXBUWOUYDUSXCXDUWOXEURXFURXGWTZOPQ
        RSAGOXHUSUOZUVHUXRTWQAUWLUVHUXRUAWQAUWTUVHUXRUBWQUXSUXPUEUJZUXFUSZUYGWK
        USZWLWMURZLWHZUYGFUSZUYHUYJFURZUMZNUOZUIZUELVIUVIUXDUXPXIUXOUYPUCUELUCU
        EVSZUXJUYKUXNUYOUYQUXGUYHUXIUYJLUVSUYGUXFVJZUYQUXHUYIWLWMUVSUYGWKVJXJZX
        KUYQUXMUYNNUYQUXKUYLUXLUYMUVSUYGFVJUYQUXGUYHUXIUYJFUYRUYSXLXMWAXNXOWCUV
        IUXDUXPXPUYCIVBIUJZUQUHZUVSUYTWLWRURZWSZWTZUHUYDUXFVUDUQXAUHUDIVBUYBVUC
        UDIVSUXTVUAUYAVUBUVSUXFUYTUQXSUXFUYTWLWRVTXQXRUXFUYCVUDUQXTYAUYEYBAUVDU
        VGUXRYCUVIUVFOUHUXRUVIOUVEUVFAOUVEUHZUVHAUYFGOYDUSUOGOYEUSUOVUETGOYFGOY
        GGMOPYHYIZWGAUVDUVGXIYJWGYKYLYMYNYOYPYTYQYRYSUVIUVQUVOAUVQUVOUPZUUAZUVH
        AUYFOXHUUBZUOVUHTGOXHUUCEUJZUVKUFZDUVNUNZUPVUGEONVUIVUJOUHZVULUVOVUMVUK
        UVLDUVNVUJOUVKUUDUUEUUFQUUGUUHWGUUIUUJUVIUVLUVPDUVNUVIUVJUVNUOZUIZUVLUV
        EUVKUFZUVPVUOOUVEUVKAVUEUVHVUNVUFWQUULVUOVUPVUPUVKUVEUFZUIUVPVUOVUQVUPV
        UNUVJHUFZUVDVUQUVIVUNUVJHUVNUVMUVJUVMULUUKUUMUUNAUVDUVGXPVURUVDUIUVJMUV
        JHMUUOUUPUUQUURUVEUVKUVBUUSUUTUVAUVC $.
    $}

    $( Generalized Heine-Borel Theorem.  A metric space is compact iff it is
       complete and totally bounded.  See ~ heibor1 and ~ heiborlem1 for a
       description of the proof.  (Contributed by Jeff Madsen, 2-Sep-2009.)
       (Revised by Mario Carneiro, 28-Jan-2014.) $)
    heibor $p |- ( ( D e. ( Met ` X ) /\ J e. Comp ) <->
                   ( D e. ( CMet ` X ) /\ D e. ( TotBnd ` X ) ) ) $=
      ( vr vv vm vy vn vt wcel wa cv wceq cfn wrex wral cn0 co ciun vu cmet cfv
      vz vk ccmp ccmet ctotbnd heibor1 cmetmet adantr ctop cuni cpw cin metxmet
      wi cxmet mopntop 3syl wf c1 c2 cexp cdiv cbl wex crp istotbnd simprbi 2nn
      cn nnexpcl mpan nnrpd rpreccld oveq2 eqeq2d rexbidv ralbidv anbi2d syl2an
      rspccva expcom adantl ac6sfi adantrl w3a crn simp3l frnd mopnuni 3ad2ant1
      oveq1 wss sseqtrd cmopn fvexi uniex elpw2 sylibr simp2l wfo wfn ffn dffn4
      sylib sylan2 syl2anc elind eleq2d rexrn eliun 3bitr4g eqrdv simp3r uniiun
      iuneq2 eqtrid syl simp2r 3eqtr2rd iuneq1 rspceeqv 3expia adantrrr exlimdv
      fofi mpd rexlimdvaa syld ralrimdva pwex inex1 com eqid simpl weq iuneq2dv
      oveq2d nn0ennn nnenom entri axcc4 syl6 elpwi cab copab pweqd ineq1d feq3d
      cmpo wn biimpar adantrr cbviunv id inss1 sseqtrrid fss syl2anr ffvelcdmda
      elpwid sselda simplr ovex ovmpo biimprd ralimdva impr fveq2 iuneq1d eqtrd
      cbvralvw heiborlem10 exp32 syl5 ralrimiv ex imp iscmp sylanbrc jca impbii
      ) ACUBUCKZBUFKZLACUGUCKZACUHUCKZLZABCDUIUWIUWEUWFUWGUWEUWHACUJZUKUWIBULKZ
      BUMZEMZUMNZUWLFMZUMZNFUWMUNOUOZPZUQZEBUNZQZUWFUWGUWKUWHUWGUWEACURUCKZUWKU
      WJACUPZABCDUSUTUKUWGUWHUXAUWGUWHRUWLUNZOUOZGMZVAZCHIMZUXFUCZHMZVBVCUXHVDS
      ZVESZAVFUCZSZTZNZIRQZLZGVGZUXAUWGUWHCHJMZUXNTZNZJUXEPZIRQUXSUWGUWHUYCIRUW
      GUXHRKZLZUWHUAMZUMZCNZUWOUXNNZHCPZFUYFQZLZUAOPZUYCUYDUWHUYMUQUWGUWHUYDUYM
      UWHUYHUWOUXJUWMUXMSZNZHCPZFUYFQZLZUAOPZEVHQZUXLVHKUYMUYDUWHUWEUYTHUAACFEV
      IVJUYDUXKUYDUXKVCVLKUYDUXKVLKVKVCUXHVMVNVOVPUYSUYMEUXLVHUWMUXLNZUYRUYLUAO
      VUAUYQUYKUYHVUAUYPUYJFUYFVUAUYOUYIHCVUAUYNUXNUWOUWMUXLUXJUXMVQVRVSVTWAVSW
      CWBWDWEUYEUYLUYCUAOUYEUYFOKZUYLLZLZUYFCUXFVAZUWOUWOUXFUCZUXLUXMSZNZFUYFQZ
      LZGVGZUYCVUCVUKUYEVUBUYKVUKUYHUYIVUHFHUYFCGUXJVUFNZUXNVUGUWOUXJVUFUXLUXMW
      NZVRWFWGWEVUDVUJUYCGUYEVUBUYHVUJUYCUQUYKUYEVUBUYHLZVUJUYCUYEVUNVUJWHZUXFW
      IZUXEKCHVUPUXNTZNUYCVUOUXDOVUPVUOVUPUWLWOVUPUXDKVUOVUPCUWLVUOUYFCUXFUYEVU
      NVUEVUIWJZWKUYEVUNCUWLNZVUJUWGVUSUYDUWGUWEUXBVUSUWJUXCABCDWLUTZUKWMWPVUPU
      WLBBAWQDWRWSZWTXAVUOVUBVUEVUPOKZUYEVUBUYHVUJXBVURVUEVUBUYFVUPUXFXCZVVBVUE
      UXFUYFXDZVVCUYFCUXFXEZUYFUXFXFXGUYFVUPUXFYHXHXIXJVUOVUQFUYFVUGTZUYGCVUOVU
      EVVDVUQVVFNVURVVEVVDEVUQVVFVVDUWMUXNKZHVUPPUWMVUGKZFUYFPUWMVUQKUWMVVFKVVG
      VVHHFUYFUXFVULUXNVUGUWMVUMXKXLHUWMVUPUXNXMFUWMUYFVUGXMXNXOUTVUOVUIUYGVVFN
      UYEVUNVUEVUIXPVUIUYGFUYFUWOTVVFFUYFXQFUYFUWOVUGXRXSXTUYEVUBUYHVUJYAYBJVUP
      UXEUYAVUQCHUXTVUPUXNYCYDXIYEYFYGYIYJYKYLUYBUXPJUXEGIRUXDOUWLVVAYMYNRVLYOU
      UAUUBUUCUXTUXINUYAUXOCHUXTUXIUXNYCVRUUDUUEUWGUXRUXAGUWGUXRUXAUWGUXRLZUWSE
      UWTUWMUWTKUWMBWOZVVIUWSUWMBUUFVVIVVJUWNUWRVVIJUDFUAUDGCRUDMZVBVCUXFVDSZVE
      SZUXMSZUULZAUWMGUEUXFUEMZRKUXTVVPUXFUCZKZUXTVVPVVOSZUYFUWPWOFUWQPUUMUAUUG
      ZKWHJUEUUHZBVVTCDVVTYPVWAYPVVOYPZUWGUXRYQUWGUXGRCUNZOUOZUXFVAZUXQUWGVWEUX
      GUWGVWDUXEUXFRUWGVWCUXDOUWGCUWLVUTUUIZUUJUUKUUNUUOVVICJUXIUXTUXHVVOSZTZNZ
      IRQZCJVVQVVSTZNZUERQUWGUXGUXQVWJUWGUXGLZUXPVWIIRVWMUYDLZVWIUXPVWNVWHUXOCV
      WNVWHHUXIUXJUXHVVOSZTUXOJHUXIVWGVWOUXTUXJUXHVVOWNUUPVWNHUXIVWOUXNVWNUXJUX
      IKZLUXJCKUYDVWOUXNNVWNUXICUXJVWNUXICVWMRVWCUXHUXFUXGUXGUXEVWCWORVWCUXFVAU
      WGUXGUUQUWGUXDUXEVWCUXDOUURVWFUUSRUXEVWCUXFUUTUVAUVBUVCUVDVWMUYDVWPUVEUDG
      UXJUXHCRVVNUXNVVOUXJVVMUXMSVVKUXJVVMUXMWNGIYRZVVMUXLUXJUXMVWQVVLUXKVBVEUX
      FUXHVCVDVQYTYTVWBUXJUXLUXMUVFUVGXIYSXSVRUVHUVIUVJVWIVWLIUERIUEYRZVWHVWKCV
      WRVWHJVVQVWGTVWKVWRJUXIVVQVWGUXHVVPUXFUVKUVLVWRJVVQVWGVVSVWRVVRLUXHVVPUXT
      VVOVWRVVRYQYTYSUVMVRUVNXGUVOUVPUVQUVRUVSYGYKUVTEFBUWLUWLYPUWAUWBUWCUWD $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Banach Fixed Point Theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d j k x y z D $.  $d j k x y z G $.  $d j k x y z J $.  $d j k w x y ph $.
    $d j k A $.  $d j k w x y z F $.  $d j k x y K $.  $d j k w x y z X $.
    bfp.2 $e |- ( ph -> D e. ( CMet ` X ) ) $.
    bfp.3 $e |- ( ph -> X =/= (/) ) $.
    bfp.4 $e |- ( ph -> K e. RR+ ) $.
    bfp.5 $e |- ( ph -> K < 1 ) $.
    bfp.6 $e |- ( ph -> F : X --> X ) $.
    bfp.7 $e |- ( ( ph /\ ( x e. X /\ y e. X ) ) ->
                  ( ( F ` x ) D ( F ` y ) ) <_ ( K x. ( x D y ) ) ) $.
    ${
      bfp.8 $e |- J = ( MetOpen ` D ) $.
      bfp.9 $e |- ( ph -> A e. X ) $.
      bfp.10 $e |- G = seq 1 ( ( F o. 1st ) , ( NN X. { A } ) ) $.
      $( Lemma for ~ bfp .  The sequence ` G ` , which simply starts from any
         point in the space and iterates ` F ` , satisfies the property that
         the distance from ` G ( n ) ` to ` G ( n + 1 ) ` decreases by at least
         ` K ` after each step.  Thus, the total distance from any ` G ( i ) `
         to ` G ( j ) ` is bounded by a geometric series, and the sequence is
         Cauchy.  Therefore, it converges to a point ` ( ( ~~>t `` J ) `` G ) `
         since the space is complete.  (Contributed by Jeff Madsen,
         17-Jun-2014.) $)
      bfplem1 $p |- ( ph -> G ( ~~>t ` J ) ( ( ~~>t ` J ) ` G ) ) $=
        ( co vk vj clm cfv cdm wcel wbr ccmet ccau cdiv cmet cmetmet c1 cn nnuz
        syl 1zzd algrf cr ffvelcdmd metcl syl3anc rerpdivcld cv caddc cexp cmul
        cle wi wceq fveq2 fvoveq1 oveq12d oveq2 oveq2d breq12d imbi2d leidd 1nn
        algr0 algrp1 mpan2 fveq2d eqtrd rpred recnd exp1d divcan1d 3brtr4d wral
        rpne0d ffvelcdmda peano2nn ffvelcdm syl2an jca ralrimivva adantr oveq1d
        wa oveq1 rspc2v sylc remulcld adantl nnnn0d reexpcld letr mpand cc0 clt
        wf wb cn0 nnnn0 reexpcl rpgt0d lemul1 syl112anc cc mulcomd expp1 eqtr4d
        mulassd bitrd sylan2 breq1d 3imtr4d expcom nnind impcom geomcau cmetcau
        a2d syl2anc cha wfun cxmet metxmet 3syl methaus lmfun funfvbrb mpbid )
        AGHUCUDZUEUFZGGUUEUDUUEUGZAEJUHUDUFZGEUIUDUFUUFKADDFUDZETZIUJTZIEUAGJAU
        UHEJUKUDUFZKEJULUPZADGJFUMUNUOSAUQZROURZAUUJIAUULDJUFUUIJUFUUJUSUFUUMRA
        JJDFORUTDUUIEJVAVBZMVCZMNUAVDZUNUFZAUURGUDZUURUMVETZGUDZETZUUKIUURVFTZV
        GTZVHUGZAUBVDZGUDZUVGUMVETGUDZETZUUKIUVGVFTZVGTZVHUGZVIAUMGUDZUMUMVETGU
        DZETZUUKIUMVFTZVGTZVHUGZVIAUVFVIZAUVBUVAUMVETGUDZETZUUKIUVAVFTZVGTZVHUG
        ZVIUVTUBUAUURUVGUMVJZUVMUVSAUWFUVJUVPUVLUVRVHUWFUVHUVNUVIUVOEUVGUMGVKUV
        GUMUMGVEVLVMUWFUVKUVQUUKVGUVGUMIVFVNVOVPVQUVGUURVJZUVMUVFAUWGUVJUVCUVLU
        VEVHUWGUVHUUTUVIUVBEUVGUURGVKUVGUURUMGVEVLVMUWGUVKUVDUUKVGUVGUURIVFVNVO
        VPVQZUVGUVAVJZUVMUWEAUWIUVJUWBUVLUWDVHUWIUVHUVBUVIUWAEUVGUVAGVKUVGUVAUM
        GVEVLVMUWIUVKUWCUUKVGUVGUVAIVFVNVOVPVQUWHAUUJUUJUVPUVRVHAUUJUUPVRAUVNDU
        VOUUIEADGJFUMUNUOSUUNRVTZAUVOUVNFUDZUUIAUMUNUFUVOUWKVJVSADGJFUMUMUNUOSU
        UNROWAWBAUVNDFUWJWCWDVMAUVRUUKIVGTUUJAUVQIUUKVGAIAIAIMWEZWFZWGVOAUUJIAU
        UJUUPWFUWMAIMWKWHWDWIUUSAUVFUWEAUUSUVFUWEVIAUUSWTZIUVCVGTZUWDVHUGZUUTFU
        DZUVBFUDZETZUWDVHUGZUVFUWEUWNUWSUWOVHUGZUWPUWTUWNUUTJUFZUVBJUFZWTBVDZFU
        DZCVDZFUDZETZIUXDUXFETZVGTZVHUGZCJWJBJWJZUXAUWNUXBUXCAUNJUURGUUOWLZAUNJ
        GXLUVAUNUFZUXCUUSUUOUURWMZUNJUVAGWNWOZWPAUXLUUSAUXKBCJJPWQWRUXKUXAUWQUX
        GETZIUUTUXFETZVGTZVHUGBCUUTUVBJJUXDUUTVJZUXHUXQUXJUXSVHUXTUXEUWQUXGEUXD
        UUTFVKWSUXTUXIUXRIVGUXDUUTUXFEXAVOVPUXFUVBVJZUXQUWSUXSUWOVHUYAUXGUWRUWQ
        EUXFUVBFVKVOUYAUXRUVCIVGUXFUVBUUTEVNVOVPXBXCUWNUWSUSUFZUWOUSUFUWDUSUFUX
        AUWPWTUWTVIUWNUULUWQJUFUWRJUFUYBAUULUUSUUMWRZUWNJJUUTFAJJFXLUUSOWRZUXMU
        TUWNJJUVBFUYDUXPUTUWQUWREJVAVBUWNIUVCAIUSUFZUUSUWLWRZUWNUULUXBUXCUVCUSU
        FZUYCUXMUXPUUTUVBEJVAVBZXDUWNUUKUWCAUUKUSUFUUSUUQWRZUWNIUVAUYFUWNUVAUUS
        UXNAUXOXEXFXGXDUWSUWOUWDXHVBXIUWNUVFUVCIVGTZUVEIVGTZVHUGZUWPUWNUYGUVEUS
        UFUYEXJIXKUGZUVFUYLXMUYHUWNUUKUVDUYIAUYEUURXNUFZUVDUSUFUUSUWLUURXOZIUUR
        XPWOZXDUYFAUYMUUSAIMXQWRUVCUVEIXRXSUWNUYJUWOUYKUWDVHUWNUVCIUWNUVCUYHWFA
        IXTUFZUUSUWMWRZYAUWNUYKUUKUVDIVGTZVGTUWDUWNUUKUVDIUWNUUKUYIWFUWNUVDUYPW
        FUYRYDUWNUWCUYSUUKVGAUYQUYNUWCUYSVJUUSUWMUYOIUURYBWOVOYCVPYEUWNUWBUWSUW
        DVHUWNUVBUWQUWAUWREADGJFUURUMUNUOSUUNROWAUUSAUXNUWAUWRVJUXOADGJFUVAUMUN
        UOSUUNROWAYFVMYGYHYIYNYJYKYLEGHJQYMYOAHYPUFZUUEYQUUFUUGXMAUULEJYRUDUFUY
        TUUMEJYSEHJQUUAYTHUUBGUUEUUCYTUUD $.

      $( Lemma for ~ bfp .  Using the point found in ~ bfplem1 , we show that
         this convergent point is a fixed point of ` F ` .  Since for any
         positive ` x ` , the sequence ` G ` is in ` B ( x / 2 , P ) ` for all
         ` k e. ( ZZ>= `` j ) ` (where ` P = ( ( ~~>t `` J ) `` G ) ` ), we
         have ` D ( G ( j + 1 ) , F ( P ) ) <_ D ( G ( j ) , P ) < x / 2 ` and
         ` D ( G ( j + 1 ) , P ) < x / 2 ` , so ` F ( P ) ` is in every
         neighborhood of ` P ` and ` P ` is a fixed point of ` F ` .
         (Contributed by Jeff Madsen, 5-Jun-2014.) $)
      bfplem2 $p |- ( ph -> E. z e. X ( F ` z ) = z ) $=
        ( vk vj clm cfv wcel wceq cv wrex ctopon wbr cmet cxmet cmetmet metxmet
        ccmet syl mopntopon 3syl bfplem1 lmcl syl2anc co cc0 cle caddc crp wral
        wa clt c2 cdiv cuz cn c1 adantr nnuz eqidd rphalfcl adantl lmmcvg simpr
        1zzd ralimi cz wi nnz fveq2 oveq1d breq1d rspcv peano2uz algrp1 adantlr
        uzid sylibd jcad cr ad2antrr wf algrf ffvelcdmda syl3anc ffvelcdmd rpre
        metcl ad2antlr readdcld mettri2 syl13anc cmul rpred remulcld ralrimivva
        lt2halves jca oveq1 oveq2d breq12d oveq2 rspc2v sylc metge0 1re sylancl
        1red ltle mpd lemul1ad recnd mullidd breqtrd letrd leadd1dd mpand 3syld
        lelttr syl5 rexlimdva wb 0re syl2an breqtrrd ralrimiva alrple mpbir2and
        addlidd mpbird letri3 meteq0 mpbid id eqeq12d rspcev ) AHIUCUDZUDZKUEZU
        UOGUDZUUOUFZDUGZGUDZUUSUFZDKUHAIKUIUDUEZHUUOUUNUJZUUPAFKUKUDUEZFKULUDUE
        ZUVBAFKUOUDUEUVDLFKUMUPZFKUNZFIKRUQURABCEFGHIJKLMNOPQRSTUSZUUOHIKUTVAZA
        UUQUUOFVBZVCUFZUURAUVKUVJVCVDUJZVCUVJVDUJZAUVLUVJVCBUGZVEVBZVDUJZBVFVGZ
        AUVPBVFAUVNVFUEZVHZUVJUVNUVOVDUVSUVJUVNVIUJZUVJUVNVDUJZUVSUAUGZHUDZKUEZ
        UWCUUOFVBZUVNVJVKVBZVIUJZVHZUAUBUGZVLUDZVGZUBVMUHUVTUVSUWCFUUOUWFUBUAHI
        VNKVMRUVSUVDUVEAUVDUVRUVFVOUVGUPVPUVSWBUVSUWBVMUEVHUWCVQAUVCUVRUVHVOUVR
        UWFVFUEAUVNVRVSVTUVSUWKUVTUBVMUWKUWGUAUWJVGZUVSUWIVMUEZVHZUVTUWHUWGUAUW
        JUWDUWGWAWCUWNUWLUWIHUDZUUOFVBZUWFVIUJZUWOGUDZUUOFVBZUWFVIUJZVHZUWPUWSV
        EVBZUVNVIUJZUVTUWNUWLUWQUWTUWNUWIWDUEZUWIUWJUEZUWLUWQWEUWMUXDUVSUWIWFVS
        ZUWIWNZUWGUWQUAUWIUWJUWBUWIUFZUWEUWPUWFVIUXHUWCUWOUUOFUWBUWIHWGWHWIWJUR
        UWNUWLUWIVNVEVBZHUDZUUOFVBZUWFVIUJZUWTUWNUXEUXIUWJUEUWLUXLWEUWNUXDUXEUX
        FUXGUPUWIUWIWKUWGUXLUAUXIUWJUWBUXIUFZUWEUXKUWFVIUXMUWCUXJUUOFUWBUXIHWGW
        HWIWJURUWNUXKUWSUWFVIUWNUXJUWRUUOFAUWMUXJUWRUFUVRAEHKGUWIVNVMVPTAWBZSPW
        LWMWHWIWOWPUWNUWPWQUEZUWSWQUEZUVNWQUEZUXAUXCWEUWNUVDUWOKUEZUUPUXOAUVDUV
        RUWMUVFWRZUVSVMKUWIHAVMKHWSUVRAEHKGVNVMVPTUXNSPWTVOXAZAUUPUVRUWMUVIWRZU
        WOUUOFKXEXBZUWNUVDUWRKUEZUUPUXPUXSUWNKKUWOGAKKGWSUVRUWMPWRZUXTXCZUYAUWR
        UUOFKXEXBZUVRUXQAUWMUVNXDZXFZUWPUWSUVNXNXBUWNUVJUXBVDUJZUXCUVTUWNUVJUWR
        UUQFVBZUWSVEVBZUXBAUVJWQUEZUVRUWMAUVDUUQKUEZUUPUYLUVFAKKUUOGPUVIXCZUVIU
        UQUUOFKXEXBZWRZUWNUYJUWSUWNUVDUYCUYMUYJWQUEUXSUYEUWNKKUUOGUYDUYAXCZUWRU
        UQFKXEXBZUYFXGUWNUWPUWSUYBUYFXGZUWNUVDUYCUYMUUPUVJUYKVDUJUXSUYEUYQUYAUU
        QUUOUWRFKXHXIUWNUYJUWPUWSUYRUYBUYFUWNUYJJUWPXJVBZUWPUYRUWNJUWPAJWQUEZUV
        RUWMAJNXKZWRZUYBXLUYBUWNUXRUUPVHUVNGUDZCUGZGUDZFVBZJUVNVUEFVBZXJVBZVDUJ
        ZCKVGBKVGZUYJUYTVDUJZUWNUXRUUPUXTUYAXOAVUKUVRUWMAVUJBCKKQXMWRVUJVULUWRV
        UFFVBZJUWOVUEFVBZXJVBZVDUJBCUWOUUOKKUVNUWOUFZVUGVUMVUIVUOVDVUPVUDUWRVUF
        FUVNUWOGWGWHVUPVUHVUNJXJUVNUWOVUEFXPXQXRVUEUUOUFZVUMUYJVUOUYTVDVUQVUFUU
        QUWRFVUEUUOGWGXQVUQVUNUWPJXJVUEUUOUWOFXSXQXRXTYAUWNUYTVNUWPXJVBUWPVDUWN
        JVNUWPVUCUWNYEUYBUWNUVDUXRUUPVCUWPVDUJUXSUXTUYAUWOUUOFKYBXBAJVNVDUJZUVR
        UWMAJVNVIUJZVUROAVUAVNWQUEVUSVURWEVUBYCJVNYFYDYGWRYHUWNUWPUWNUWPUYBYIYJ
        YKYLYMYLUWNUYLUXBWQUEUXQUYIUXCVHUVTWEUYPUYSUYHUVJUXBUVNYPXBYNYOYQYRYGAU
        YLUXQUVTUWAWEUVRUYOUYGUVJUVNYFUUAYGUVSUVNUVSUVNUVRUXQAUYGVSYIUUFUUBUUCA
        UYLVCWQUEZUVLUVQYSUYOYTBUVJVCUUDYDUUGAUVDUYMUUPUVMUVFUYNUVIUUQUUOFKYBXB
        AUYLVUTUVKUVLUVMVHYSUYOYTUVJVCUUHYDUUEAUVDUYMUUPUVKUURYSUVFUYNUVIUUQUUO
        FKUUIXBUUJUVAUURDUUOKUUSUUOUFZUUTUUQUUSUUOUUSUUOGWGVVAUUKUULUUMVA $.
    $}

    $( Banach fixed point theorem, also known as contraction mapping theorem.
       A contraction on a complete metric space has a unique fixed point.  We
       show existence in the lemmas, and uniqueness here - if ` F ` has two
       fixed points, then the distance between them is less than ` K ` times
       itself, a contradiction.  (Contributed by Jeff Madsen, 2-Sep-2009.)
       (Proof shortened by Mario Carneiro, 5-Jun-2014.) $)
    bfp $p |- ( ph -> E! z e. X ( F ` z ) = z ) $=
      ( wcel c1 wbr co cle cc0 vw cv cfv wceq wrex wa weq wi wral c0 wne wex n0
      wreu sylib c1st ccom csn cxp cseq cmopn ccmet adantr crp clt cmul adantlr
      cn wf eqid simpr bfplem2 exlimddv cmin oveq12 adantl eqbrtrrd cmet cr syl
      cmetmet ad2antrr simplrl simplrr metcl syl3anc rpred remulcld mpbird 1cnd
      suble0d recnd subdird mullidd oveq1d eqtrd resubcl sylancr mul01d 3brtr4d
      1re wb 0red posdif sylancl mpbid lemul2 syl112anc metge0 letri3 mpbir2and
      0re meteq0 ex ralrimivva fveq2 id eqeq12d anbi1d equequ1 imbi12d cbvralvw
      ralbidv reu4 sylanbrc ) ADUBZFUCZYFUDZDHUEZYHCUBZFUCZYJUDZUFZDCUGZUHZCHUI
      ZDHUIZYHDHUNAUAUBZHOZYIUAAHUJUKZYSUAULJUAHUMUOAYSUFBCDYREFFUPUQVHYRURUSPU
      TZEVAUCZGHAEHVBUCOZYSIVCAYTYSJVCAGVDOYSKVCAGPVEQZYSLVCAHHFVIYSMVCABUBZHOZ
      YJHOZUFZUUEFUCZYKERZGUUEYJERZVFRZSQZYSNVGUUBVJAYSVKUUAVJVLVMAUUIUUEUDZYLU
      FZBCUGZUHZCHUIZBHUIYQAUUQBCHHAUUHUFZUUOUUPUUSUUOUFZUUKTUDZUUPUUTUVAUUKTSQ
      ZTUUKSQZUUTUVBPGVNRZUUKVFRZUVDTVFRZSQZUUTUUKUULVNRZTUVEUVFSUUTUVHTSQUUKUU
      LSQUUTUUJUUKUULSUUOUUJUUKUDUUSUUIUUEYKYJEVOVPUUSUUMUUONVCVQUUTUUKUULUUTEH
      VRUCOZUUFUUGUUKVSOZAUVIUUHUUOAUUCUVIIEHWAVTWBZAUUFUUGUUOWCZAUUFUUGUUOWDZU
      UEYJEHWEWFZUUTGUUKAGVSOZUUHUUOAGKWGZWBZUVNWHWKWIUUTUVEPUUKVFRZUULVNRUVHUU
      TPGUUKUUTWJUUTGUVQWLUUTUUKUVNWLZWMUUTUVRUUKUULVNUUTUUKUVSWNWOWPUUTUVDUUTU
      VDAUVDVSOZUUHUUOAPVSOZUVOUVTXAUVPPGWQWRWBZWLWSWTUUTUVJTVSOZUVTTUVDVEQZUVB
      UVGXBUVNUUTXCUWBAUWDUUHUUOAUUDUWDLAUVOUWAUUDUWDXBUVPXAGPXDXEXFWBUUKTUVDXG
      XHWIUUTUVIUUFUUGUVCUVKUVLUVMUUEYJEHXIWFUUTUVJUWCUVAUVBUVCUFXBUVNXLUUKTXJX
      EXKUUTUVIUUFUUGUVAUUPXBUVKUVLUVMUUEYJEHXMWFXFXNXOUURYPBDHBDUGZUUQYOCHUWEU
      UOYMUUPYNUWEUUNYHYLUWEUUIYGUUEYFUUEYFFXPUWEXQXRXSBDCXTYAYCYBUOYHYLDCHYNYG
      YKYFYJYFYJFXPYNXQXRYDYE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Euclidean space
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Rn $.
  $( Extend class notation with the n-dimensional Euclidean space. $)
  crrn $a class Rn $.

  ${
    $d i x y k $.
    $( Define n-dimensional Euclidean space as a metric space with the standard
       Euclidean norm given by the quadratic mean.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    df-rrn $a |- Rn = ( i e. Fin |->
       ( x e. ( RR ^m i ) , y e. ( RR ^m i ) |-> ( sqrt `
         sum_ k e. i ( ( ( x ` k ) - ( y ` k ) ) ^ 2 ) ) ) ) $.
  $}

  ${
    $d k n x y G $.  $d i j k m n x y z I $.  $d j k n M $.  $d j k n x ph $.
    $d k A $.  $d x J $.  $d j k n x y P $.  $d k n R $.  $d i j k x y z X $.
    $d j k m n t x y F $.
    rrnval.1 $e |- X = ( RR ^m I ) $.
    $( The n-dimensional Euclidean space.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Revised by Mario Carneiro, 13-Sep-2015.) $)
    rrnval $p |- ( I e. Fin -> ( Rn ` I ) = ( x e. X , y e. X |-> ( sqrt `
          sum_ k e. I ( ( ( x ` k ) - ( y ` k ) ) ^ 2 ) ) ) ) $=
      ( vi cr cv cmap co cfv csu csqrt cmpo wf cvv wcel wral cc cmin cexp oveq2
      c2 cfn crrn wceq eqtr4di sumeq1 fveq2d mpoeq123dv df-rrn cxp crn c0 fvrn0
      csn cun rgen2w eqid fmpo mpbi ovex eqeltri xpex wss sqrtf frn ax-mp ssexi
      cnex p0ex unex fex2 mp3an fvmpt ) GDABHGIZJKZVRVQCIZAILVSBILUAKUDUBKZCMZN
      LZOABEEDVTCMZNLZOZUEUFVQDUGZABVRVRWBEEWDWFVRHDJKZEVQDHJUCFUHZWHWFWAWCNVQD
      VTCUIUJUKABGCULEEUMZNUNZUOUQZURZWEPZWIQRWLQRWEQRWDWLRZBESAESWMWNABEENWCUP
      USABEEWDWLWEWEUTVAVBEEEWGQFHDJVCVDZWOVEWJWKWJTVKTTNPWJTVFVGTTNVHVIVJVLVMW
      IWLWEQQVNVOVP $.

    $( The value of the Euclidean metric.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Revised by Mario Carneiro, 13-Sep-2015.) $)
    rrnmval $p |- ( ( I e. Fin /\ F e. X /\ G e. X ) -> ( F ( Rn ` I ) G ) =
        ( sqrt ` sum_ k e. I ( ( ( F ` k ) - ( G ` k ) ) ^ 2 ) ) ) $=
      ( vx vy cfn wcel cv cfv cmin co c2 cexp csu csqrt wceq fveq1 w3a crrn cvv
      cmpo rrnval 3ad2ant1 oveqan12d oveq1d sumeq2sdv fveq2d adantl simp2 simp3
      wa fvexd ovmpod ) DIJZBEJZCEJZUAZGHBCEEDAKZGKZLZVAHKZLZMNZOPNZAQZRLZDVABL
      ZVACLZMNZOPNZAQZRLZDUBLZUCUQURVPGHEEVIUDSUSGHADEFUEUFVBBSZVDCSZUNZVIVOSUT
      VSVHVNRVSDVGVMAVSVFVLOPVQVRVCVJVEVKMVAVBBTVAVDCTUGUHUIUJUKUQURUSULUQURUSU
      MUTVNRUOUP $.

    $( Euclidean space is a metric space.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Proof shortened by Mario Carneiro, 5-Jun-2014.) $)
    rrnmet $p |- ( I e. Fin -> ( Rn ` I ) e. ( Met ` X ) ) $=
      ( vx vy vk wcel cr cfv wf co cc0 wceq wb caddc wral wa c2 cexp csqrt crrn
      vz cfn cxp cv cle wbr cmet cmin csu cmpo simpl simprl eleqtrdi elmapi syl
      cmap ffvelcdmda simprr resubcld resqcld fsumrecl sqge0d fsumge0 resqrtcld
      ralrimivva eqid fmpo sylib rrnval feq1d mpbird sqrt00 syl2anc bitrd recnd
      fsum00 cc sqeq0 subeq0ad ralbidva rrnmval 3expb eqeq1d wfn eqfnfv 3bitr4d
      ffnd simpll adantlr simpr trirn npncand oveq1d sumeq2dv sqsubswap 3brtr3d
      fveq2d adantr w3a 3adant3r 3adant3l oveq12d 3expa an32s 3brtr4d ralrimiva
      jca cvv ovex eqeltri ismet ax-mp sylanbrc ) AUCGZBBUDZHAUAIZJZDUEZEUEZXQK
      ZLMZXSXTMZNZYAUBUEZXSXQKZYEXTXQKZOKZUFUGZUBBPZQZEBPDBPZXQBUHIGZXOXRXPHDEB
      BAFUEZXSIZYNXTIZUIKZRSKZFUJZTIZUKZJZXOYTHGZEBPDBPUUBXOUUCDEBBXOXSBGZXTBGZ
      QZQZYSUUGAYRFXOUUFULZUUGYNAGZQZYQUUJYOYPUUGAHYNXSUUGXSHAUQKZGAHXSJUUGXSBU
      UKXOUUDUUEUMCUNXSHAUOUPZURZUUGAHYNXTUUGXTUUKGAHXTJUUGXTBUUKXOUUDUUEUSCUNX
      THAUOUPZURZUTZVAZVBZUUGAYRFUUHUUQUUJYQUUPVCZVDZVEVFDEBBYTHUUAUUAVGVHVIXOX
      PHXQUUADEFABCVJVKVLXOYKDEBBUUGYDYJUUGYTLMZYOYPMZFAPZYBYCUUGUVAYRLMZFAPZUV
      CUUGUVAYSLMZUVEUUGYSHGLYSUFUGUVAUVFNUURUUTYSVMVNUUGAYRFUUHUUQUUSVQVOUUGUV
      DUVBFAUUJUVDYQLMZUVBUUJYQVRGUVDUVGNUUJYQUUPVPYQVSUPUUJYOYPUUJYOUUMVPZUUJY
      PUUOVPZVTVOWAVOUUGYAYTLXOUUDUUEYAYTMZFXSXTABCWBWCZWDUUGXSAWEXTAWEYCUVCNUU
      GAHXSUULWHUUGAHXTUUNWHFAXSXTWFVNWGUUGYIUBBUUGYEBGZQZYTAYNYEIZYOUIKRSKZFUJ
      ZTIZAUVNYPUIKZRSKFUJTIZOKZYAYHUFUVMAYOUVNUIKZUVROKZRSKZFUJZTIAUWARSKZFUJZ
      TIZUVSOKYTUVTUFUVMAUWAUVRFXOUUFUVLWIUVMUUIQZYOUVNUUGUUIYOHGUVLUUMWJUVMAHY
      NYEUVMYEUUKGAHYEJUVMYEBUUKUUGUVLWKCUNYEHAUOUPURZUTUWHUVNYPUWIUUGUUIYPHGUV
      LUUOWJUTWLUVMUWDYSTUVMAUWCYRFUWHUWBYQRSUWHYOUVNYPUUGUUIYOVRGZUVLUVHWJZUWH
      UVNUWIVPZUUGUUIYPVRGUVLUVIWJWMWNWOWRUVMUWGUVQUVSOUVMUWFUVPTUVMAUWEUVOFUWH
      UWJUVNVRGUWEUVOMUWKUWLYOUVNWPVNWOWRWNWQUUGUVJUVLUVKWSXOUVLUUFYHUVTMZXOUVL
      UUFUWMXOUVLUUFWTYFUVQYGUVSOXOUVLUUDYFUVQMUUEFYEXSABCWBXAXOUVLUUEYGUVSMUUD
      FYEXTABCWBXBXCXDXEXFXGXHVFBXIGYMXRYLQNBUUKXICHAUQXJXKDEUBXIXQBXLXMXN $.

    rrndstprj1.1 $e |- M = ( ( abs o. - ) |` ( RR X. RR ) ) $.
    $( The distance between two points in Euclidean space is greater than the
       distance between the projections onto one coordinate.  (Contributed by
       Jeff Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro, 13-Sep-2015.) $)
    rrndstprj1 $p |- ( ( ( I e. Fin /\ A e. I ) /\ ( F e. X /\ G e. X
                    ) ) -> ( ( F ` A ) M ( G ` A ) ) <_ ( F ( Rn ` I ) G ) ) $=
      ( vk wcel wa cfv cmin co c2 cexp cle wbr cr wceq cfn cabs cv csqrt simpll
      csu crrn wf simprl eleqtrdi elmapi syl ffvelcdmda simprr resubcld resqcld
      sqge0d fveq2 oveq12d oveq1d simplr fsumge1 ffvelcdmd absresq cc0 fsumrecl
      fsumge0 resqrtth syl2anc 3brtr4d abscld resqrtcld absge0d sqrtge0d le2sqd
      cmap recnd mpbird remetdval rrnmval 3expb adantlr ) DUAJZADJZKZBFJZCFJZKZ
      KZABLZACLZMNZUBLZDIUCZBLZWNCLZMNZOPNZIUFZUDLZWJWKENZBCDUGLNZQWIWMWTQRWMOP
      NZWTOPNZQRWIWLOPNZWSXCXDQWIDWRXEIAWCWDWHUEZWIWNDJKZWQXGWOWPWIDSWNBWIBSDVP
      NZJDSBUHWIBFXHWEWFWGUIGUJBSDUKULZUMWIDSWNCWICXHJDSCUHWICFXHWEWFWGUNGUJCSD
      UKULZUMUOZUPZXGWQXKUQZWNATZWQWLOPXNWOWJWPWKMWNABURWNACURUSUTWCWDWHVAZVBWI
      WLSJXCXETWIWJWKWIDSABXIXOVCZWIDSACXJXOVCZUOZWLVDULWIWSSJVEWSQRXDWSTWIDWRI
      XFXLVFZWIDWRIXFXLXMVGZWSVHVIVJWIWMWTWIWLWIWLXRVQZVKWIWSXSXTVLWIWLYAVMWIWS
      XSXTVNVOVRWIWJSJWKSJXAWMTXPXQWJWKEHVSVIWCWHXBWTTZWDWCWFWGYBIBCDFGVTWAWBVJ
      $.

    $( Bound on the distance between two points in Euclidean space given bounds
       on the distances in each coordinate.  This theorem and ~ rrndstprj1 can
       be used to show that the supremum norm and Euclidean norm are
       equivalent.  (Contributed by Jeff Madsen, 2-Sep-2009.)  (Revised by
       Mario Carneiro, 13-Sep-2015.) $)
    rrndstprj2 $p |- ( ( ( I e. ( Fin \ { (/) } ) /\ F e. X /\ G e. X ) /\
      ( R e. RR+ /\ A. n e. I ( ( F ` n ) M ( G ` n ) ) < R ) ) ->
        ( F ( Rn ` I ) G ) < ( R x. ( sqrt ` ( # ` I ) ) ) ) $=
      ( vk wcel cfv co clt wbr c2 cexp cmul wceq cr cfn c0 csn cdif w3a cv wral
      crp wa crrn cmin csqrt chash simpl1 eldifad simpl2 simpl3 rrnmval syl3anc
      csu wne eldifsni syl wf eleqtrdi elmapi ffvelcdmda resubcld resqcld rpred
      cmap simprl adantr absresq remetdval syl2anc simprr fveq2 oveq12d rspccva
      breq1d sylan eqbrtrrd recnd abscld absge0d cc0 rpge0d lt2sqd mpbid fsumlt
      cabs cle fsumrecl sqge0d fsumge0 resqrtth cn hashnncl mpbird nnrpd oveq2d
      rpcnd mulcomd eqtrd rpsqrtcld sqmuld fsumconst 3eqtr4d resqrtcld rpmulcld
      wb cc 3brtr4d sqrtge0d eqbrtrd ) EUAUBUCZUDKZCGKZDGKZUEZAUHKZBUFZCLZYCDLZ
      FMZANOZBEUGZUIZUIZCDEUJLMZEJUFZCLZYLDLZUKMZPQMZJUTZULLZAEUMLZULLZRMZNYJEU
      AKZXSXTYKYRSYJEUAXQXRXSXTYIUNZUOZXRXSXTYIUPZXRXSXTYIUQZJCDEGHURUSYJYRUUAN
      OYRPQMZUUAPQMZNOYJYQEAPQMZJUTZUUGUUHNYJEYPUUIJUUDYJXREUBVAZUUCEUAUBVBVCZY
      JYLEKZUIZYOUUNYMYNYJETYLCYJCTEVKMZKETCVDYJCGUUOUUEHVECTEVFVCVGZYJETYLDYJD
      UUOKETDVDYJDGUUOUUFHVEDTEVFVCVGZVHZVIZYJUUITKUUMYJAYJAYAYBYHVLZVJZVIZVMUU
      NYOWLLZPQMZYPUUINUUNYOTKUVDYPSUURYOVNVCUUNUVCANOUVDUUINOUUNYMYNFMZUVCANUU
      NYMTKYNTKUVEUVCSUUPUUQYMYNFIVOVPYJYHUUMUVEANOZYAYBYHVQYGUVFBYLEYCYLSZYFUV
      EANUVGYDYMYEYNFYCYLCVRYCYLDVRVSWAVTWBWCUUNUVCAUUNYOUUNYOUURWDZWEYJATKUUMU
      VAVMUUNYOUVHWFYJWGAWMOUUMYJAUUTWHVMWIWJWCWKYJYQTKWGYQWMOUUGYQSYJEYPJUUDUU
      SWNZYJEYPJUUDUUSUUNYOUURWOWPZYQWQVPYJUUIYTPQMZRMZYSUUIRMZUUHUUJYJUVLUUIYS
      RMUVMYJUVKYSUUIRYJYSTKWGYSWMOUVKYSSYJYSYJYSYJYSWRKZUUKUULYJUUBUVNUUKXLUUD
      EWSVCWTXAZVJYJYSUVOWHYSWQVPXBYJUUIYSYJUUIUVBWDZYJYSUVOXCXDXEYJAYTYJAUUTXC
      YJYTYJYSUVOXFZXCXGYJUUBUUIXMKUUJUVMSUUDUVPEUUIJXHVPXIXNYJYRUUAYJYQUVIUVJX
      JYJUUAYJAYTUUTUVQXKZVJYJYQUVIUVJXOYJUUAUVRWHWIWTXP $.

    rrncms.3 $e |- J = ( MetOpen ` ( Rn ` I ) ) $.
    rrncms.4 $e |- ( ph -> I e. Fin ) $.
    rrncms.5 $e |- ( ph -> F e. ( Cau ` ( Rn ` I ) ) ) $.
    rrncms.6 $e |- ( ph -> F : NN --> X ) $.
    rrncms.7 $e |- P = ( m e. I |->
                         ( ~~> ` ( t e. NN |-> ( ( F ` t ) ` m ) ) ) ) $.
    $( Lemma for ~ rrncms .  (Contributed by Jeff Madsen, 6-Jun-2014.)
       (Revised by Mario Carneiro, 13-Sep-2015.) $)
    rrncmslem $p |- ( ph -> F e. dom ( ~~>t ` J ) ) $=
      ( vk cfv wcel cn vx vj vn vy clm wrel wbr cdm lmrel cv crrn clt wral wrex
      co cuz crp cr cmap wf wfn cmpt cli fvex fnmpti a1i nnuz 1zzd cvv wceq weq
      wa c1 fveq2 fveq1d eqid fvmpt adantl ffvelcdmda eleqtrdi elmapi syl an32s
      eqeltrd recnd cmin cabs ccau cmet cxmet rrnmet metxmet eqidd iscauf mpbid
      cfn adantr cle ad3antrrr simpllr eluznn adantll ffvelcdmd simplr adantllr
      syl3anc metcl ad2antrr ralimdva reximdva remetdval fveq2d breq1d ralbidva
      wi syl2anc rexbidva sylibd mpd ralrimiva sylanbrc wb sylancr mpbird csqrt
      c0 cc0 csu adantlr simplrr eqtrdi simplrl expr cz 1z rexuz3 ax-mp anassrs
      sylan2 rpcnd rrndstprj1 syl22anc metsym breqtrd remet simpll lelttr mpand
      rpre ad2antlr oveq12d eqtr4d ralbidv nnex caucvg climdm mpteq2dv breqtrrd
      mptex sylib climrecl ffnfv reex elmapg eleqtrrdi 1nn cexp rrnmval sumeq1d
      c2 sum0 eqtrd sqrt0 rpgt0d eqbrtrd eqtr4di raleqdv rspcev wne cdiv simprl
      chash simprr hashnncl nnrpd rpsqrtcld rpdivcld climi2 bitr3id bitrid cmul
      rexfiuz cdif eldifsn rrndstprj2 syl31anc rpne0d divcan1d breq2d pm2.61dne
      csn w3a lmmbrf mpbir2and releldm ) AGUERZUFECUXFUGZEUXFUHSGUIAUXGCISZQUJZ
      ERZCFUKRZUOZUAUJZULUGZQUBUJZUPRZUMZUBTUNZUAUQUMACURFUSUOZIACUXSSZFURCUTZA
      CFVAZUCUJZCRZURSZUCFUMUYAUYBADFBTDUJZBUJZERZRZVBZVCRZCUYJVCVDPVEVFAUYEUCF
      AUYCFSZVLZUYDQBTUYCUYHRZVBZVMTVGUYMVHUYMUYOUYOVCRZUYDVCUYMUYOVCUHSUYOUYPV
      CUGUYMUAUBQUYOVMVITVGUYMUXITSZVLZUXIUYORZUYRUYSUYCUXJRZURUYQUYSUYTVJZUYMB
      UXIUYNUYTTUYOBQVKUYCUYHUXJUYGUXIEVNVOUYOVPZUYCUXJVDVQZVRAUYQUYLUYTURSZAUY
      QVLZFURUYCUXJVUEUXJUXSSFURUXJUTVUEUXJIUXSATIUXIEOVSZJVTUXJURFWAWBVSWCZWDZ
      WEUYMUXOERZUXJUXKUOZUXMULUGZQUXPUMZUBTUNZUAUQUMZUYSUXOUYORZWFUOZWGRZUXMUL
      UGZQUXPUMZUBTUNZUAUQUMZAVUNUYLAEUXKWHRSVUNNAUAUXJVUIUXKUBQEVMITVGAUXKIWIR
      SZUXKIWJRSAFWPSZVVBMFIJWKWBZUXKIWLWBZAVHZVUEUXJWMZAUXOTSZVLZVUIWMOWNWOWQU
      YMVUNUYTUYCVUIRZHUOZUXMULUGZQUXPUMZUBTUNZUAUQUMVVAUYMVUMVVNUAUQUYMUXMUQSZ
      VLZVULVVMUBTVVPVVHVLZVUKVVLQUXPVVQUXIUXPSZVLZVVKVUJWRUGZVUKVVLUYMVVHVVRVV
      TVVOUYMVVHVLZVVRVLZVVKUXJVUIUXKUOZVUJWRVWBVVCUYLUXJISZVUIISZVVKVWCWRUGAVV
      CUYLVVHVVRMWSAUYLVVHVVRWTVWBTIUXIEATIEUTZUYLVVHVVROWSZVVHVVRUYQUYMUXIUXOX
      AZXBZXCZVWBTIUXOEVWGUYMVVHVVRXDXCZUYCUXJVUIFHIJKUUAUUBVWBVVBVWDVWEVWCVUJV
      JAVVBUYLVVHVVRVVDWSZVWJVWKUXJVUIUXKIUUCXFUUDXEVVSVVKURSZVUJURSZUXMURSZVVT
      VUKVLVVLXOUYMVVHVVRVWMVVOVWBHURWIRSZVUDVVJURSZVWMVWPVWBHKUUEVFVWBUYMUYQVU
      DUYMVVHVVRUUFVWIVUGXPZVWAVWQVVRAVVHUYLVWQVVIFURUYCVUIVVIVUIUXSSFURVUIUTVV
      IVUIIUXSATIUXOEOVSJVTVUIURFWAWBVSWCWQZUYTVVJHURXGXFXEUYMVVHVVRVWNVVOVWBVV
      BVWEVWDVWNVWLVWKVWJVUIUXJUXKIXGXFXEVVPVWOVVHVVRVVOVWOUYMUXMUUIVRXHVVKVUJU
      XMUUGXFUUHXIXJXIUYMVVNVUTUAUQUYMVVMVUSUBTVWAVVLVURQUXPVWBVVKVUQUXMULVWBVV
      KUYTVVJWFUOZWGRZVUQVWBVUDVWQVVKVXAVJVWRVWSUYTVVJHKXKXPVWBVUPVWTWGVWBUYSUY
      TVUOVVJWFVWBUYQVUAVWIVUCWBVVHVUOVVJVJUYMVVRBUXOUYNVVJTUYOBUBVKUYCUYHVUIUY
      GUXOEVNVOVUBUYCVUIVDVQUUJUUKXLUULXMXNXQUUMXRXSUYOVISUYMBTUYNUUNUUSVFUUOUY
      OUUPUUTUYLUYDUYPVJADUYCUYKUYPFCDUCVKZUYJUYOVCVXBBTUYIUYNUYFUYCUYHVNUUQXLP
      UYOVCVDVQVRUURZVUHUVAZXTUCFURCUVBYAAURVISVVCUXTUYAYBUVCMURFCVIWPUVDYCYDJU
      VEZAUXRUAUQAVVOVLUXRFYFAVVOFYFVJZUXRAVVOVXFVLZVLZVMTSUXNQTUMZUXRUVFVXHUXN
      QTVXHUYQVLZUXLYGUXMULVXJUXLYGYERZYGVXJUXLFUDUJZUXJRVXLCRWFUOUVJUVGUOZUDYH
      ZYERZVXKVXJVVCVWDUXHUXLVXOVJAVVCVXGUYQMXHAUYQVWDVXGVUFYIAUXHVXGUYQVXEXHUD
      UXJCFIJUVHXFVXJVXNYGYEVXJVXNYFVXMUDYHYGVXJFYFVXMUDAVVOVXFUYQYJUVIVXMUDUVK
      YKXLUVLUVMYKVXJUXMAVVOVXFUYQYLUVNUVOXTUXQVXIUBVMTUXOVMVJZUXNQUXPTVXPUXPVM
      UPRTUXOVMUPVNVGUVPUVQUVRYCYMAVVOFYFUVSZUXRAVVOVXQVLZVLZUYTUYDHUOZUXMFUWBR
      ZYERZUVTUOZULUGZUCFUMZQUXPUMZUBTUNZUXRVXSVYGVYDQUXPUMZUBYNUNZUCFUMZVXSVYI
      UCFVXSUYLVLZVYIUYTUYDWFUOWGRZVYCULUGZQUXPUMZUBTUNZVYKUYDUYTVYCUBQUYOVMTVG
      VYKVHVXSVYCUQSZUYLVXSUXMVYBAVVOVXQUWAVXSVYAVXSVYAVXSVYATSZVXQAVVOVXQUWCVX
      SVVCVYQVXQYBAVVCVXRMWQZFUWDWBYDUWEUWFZUWGZWQUYQVUAVYKVUCVRAUYLUYOUYDVCUGV
      XRVXCYIUWHVYIVYHUBTUNZVYKVYOVMYNSZWUAVYIYBYOVYDUBQVMTVGYPYQVYKVYHVYNUBTVY
      KVVHVLVYDVYMQUXPVYKVVHVVRVYDVYMYBZVVHVVRVLZVYKUYQWUCVWHVYKUYQVLZVXTVYLVYC
      ULWUEVUDUYEVXTVYLVJAUYLUYQVUDVXRVUGXEVYKUYEUYQAUYLUYEVXRVXDYIWQUYTUYDHKXK
      XPXMYSYRXNXQUWIYDXTVYGVYFUBYNUNZVXSVYJWUBVYGWUFYBYOVYEUBQVMTVGYPYQVXSVVCW
      UFVYJYBVYRVYDFUBQUCUWLWBUWJYDVXSVYFUXQUBTVXSVVHVLVYEUXNQUXPVXSVVHVVRVYEUX
      NXOZWUDVXSUYQWUGVWHVXSUYQVLZVYEUXLVYCVYBUWKUOZULUGZUXNWUHFWPYFUXAUWMSZVWD
      UXHVYPVYEWUJXOWUHVVCVXQWUKAVVCVXRUYQMXHAVVOVXQUYQYJFWPYFUWNYAVXSTIUXIEAVW
      FVXROWQVSAUXHVXRUYQVXEXHVXSVYPUYQVYTWQWUKVWDUXHUXBVYPVYEWUJVYCUCUXJCFHIJK
      UWOYMUWPWUHWUIUXMUXLULWUHUXMVYBWUHUXMAVVOVXQUYQYLYTWUHVYBVXSVYBUQSUYQVYSW
      QZYTWUHVYBWULUWQUWRUWSXRYSYRXIXJXSYMUWTXTAUAUXJUXKCUBQEGVMITLVVEVGVVFVVGO
      UXCUXDECUXFUXEYC $.
  $}

  ${
    $d f m t I $.  $d f X $.
    rrncms.1 $e |- X = ( RR ^m I ) $.
    $( Euclidean space is complete.  (Contributed by Jeff Madsen, 2-Sep-2009.)
       (Revised by Mario Carneiro, 13-Sep-2015.) $)
    rrncms $p |- ( I e. Fin -> ( Rn ` I ) e. ( CMet ` X ) ) $=
      ( vf vt vm cfn wcel crrn cfv ccmet cn cv wf cmopn clm wa cmpt cr eqid cdm
      wi ccau wral cli cabs cmin ccom cxp cres simpll simplr simpr rrncmslem ex
      ralrimiva c1 nnuz 1zzd rrnmet iscmet3 mpbird ) AGHZAIJZBKJHLBDMZNZVEVDOJZ
      PJUAHZUBZDVDUCJZUDVCVIDVJVCVEVJHZQZVFVHVLVFQEFAELFMEMVEJJRUEJRZFVEAVGUFUG
      UHSSUIUJZBCVNTVGTZVCVKVFUKVCVKVFULVLVFUMVMTUNUOUPVCVDDVGUQBLURVOVCUSABCUT
      VAVB $.
  $}

  ${
    $d k r z F $.  $d k r z G $.  $d k r z I $.  $d k r z ph $.  $d k r z X $.
    $d k r D $.
    rrnequiv.y $e |- Y = ( ( CCfld |`s RR ) ^s I ) $.
    rrnequiv.d $e |- D = ( dist ` Y ) $.
    rrnequiv.1 $e |- X = ( RR ^m I ) $.
    $( The supremum metric on ` RR ^ I ` is a metric.  (Contributed by Jeff
       Madsen, 15-Sep-2015.) $)
    repwsmet $p |- ( I e. Fin -> D e. ( Met ` X ) ) $=
      ( vk cfn wcel ccnfld csca cfv cr cds cbs cmet cvv eqid wceq cress csn cxp
      co cprds cabs cmin ccom cres cmpt fconstmpt oveq2i wss ax-resscn cnfldbas
      cc ressbas2 ax-mp reex cnfldds ressds reseq1i fvexd id cv wa ovex prdsmet
      a1i remet resssca pwsval mpan fveq2d eqtrid cmap pwsbas eqtrd 3eltr4d ) B
      IJZKLMZBKNUAUDZUBUCZUEUDZOMZWDPMZQMACQMVTHWFWEWBWAUFUGUHZNNUCZUIZBNRWDRWC
      HBWBUJWAUEHBWBUKULWFSNUPUMNWBPMTUNNUPWBKWBSZUOUQURZWGWBOMZWHNRJZWGWLTUSNW
      GKWBRWJUTVAURVBWESVTKLVCVTVDWBRJZVTHVEBJVFZKNUAVGZVIWINQMJWOWIWISVJVIVHVT
      ADOMWEFVTDWDOWNVTDWDTWPWBWABRIDEWMWAWBLMTUSNWAKWBRWJWASVKURVLVMZVNVOVTCWF
      QVTCNBVPUDZWFGVTWRDPMZWFWNVTWRWSTWPNWBBRIDEWKVQVMVTDWDPWQVNVRVOVNVS $.

    rrnequiv.i $e |- ( ph -> I e. Fin ) $.
    $( The supremum metric on ` RR ^ I ` is equivalent to the ` Rn ` metric.
       (Contributed by Jeff Madsen, 15-Sep-2015.) $)
    rrnequiv $p |- ( ( ph /\ ( F e. X /\ G e. X ) ) ->
      ( ( F D G ) <_ ( F ( Rn ` I ) G ) /\
        ( F ( Rn ` I ) G ) <_ ( ( sqrt ` ( # ` I ) ) x. ( F D G ) ) ) ) $=
      ( vk wcel co cfv cle wbr cr cvv adantr vz vr wa crrn chash cmul cabs cmin
      csqrt cv ccom cxp cres cmpt crn cc0 csn cun cxr clt csup csca cress cprds
      ccnfld cds wceq ovex reex eqid resssca ax-mp pwsval sylancr fveq2d eqtrid
      cfn oveqd cbs fconstmpt oveq2i a1i ralrimiva simprl cmap cc wss ax-resscn
      cnfldbas ressbas2 pwsbas eleqtrd simprr cnfldds ressds reseq1i prdsdsval3
      fvexd eqtrd wral rrndstprj1 an32s sylanl1 wb rgenw breq1 ralrnmptw sylibr
      cmet rrnmet syl metge0 syl3anc breq1d syl5ibrcom ralrimiv ralunb sylanbrc
      elsni prdsbascl r19.21bi metcl syl2anc ressxr sselid mpbird eqbrtrd c0 wf
      wfn eleqtrdi elmapi ffn 3syl caddc crp readdcld lelttrd ad2antrr recnd cn
      remet mp3an1 fmpttd frnd sstrdi 0xr snssd supxrleub rzal eqfnfv imbitrrid
      unssd imp oveq1d met0 cn0 hashcl nn0red nn0ge0d repwsmet sqrtge0d mulge0d
      resqrtcld wne remulcld rpre ad2antll cdiv cdif eldifsn hashnncl rpsqrtcld
      nnrpd rpdivcld rpred 0red ltaddrpd elrpd adantlr elrnmpt1 sylancl supxrub
      ssun1 simpr breqtrrd rrndstprj2 syl32anc adddird mulcomd divcan1d oveq12d
      rpne0d breqtrd ltled anassrs alrple pm2.61dane jca ) ACFMZDFMZUCZUCZCDBNZ
      CDEUDOZNZPQUXFEUEOZUIOZUXDUFNZPQZUXCUXDLELUJZCOZUXKDOZUGUHUKZRRULZUMZNZUN
      ZUOZUPUQZURZUSUTVAZUXFPUXCUXDCDVEVBOZEVERVCNZUQULZVDNZVFOZNUYBUXCBUYGCDUX
      CBGVFOUYGIUXCGUYFVFUXCUYDSMZEVQMZGUYFVGVERVCVHZAUYIUXBKTZUYDUYCESVQGHRSMZ
      UYCUYDVBOVGVIRUYCVEUYDSUYDVJZUYCVJVKVLVMVNZVOVPVRUXCLUYFVSOZUYGUYDUYCUXPC
      DERSVQSUYFUYELEUYDUNUYCVDLEUYDVTWAZUYOVJZUXCVEVBWRZUYKUXCUYHLEUYHUXCUXKEM
      ZUCZUYJWBWCZUXCCFUYOAUWTUXAWDZUXCFREWENZUYOJUXCVUCGVSOZUYOUXCUYHUYIVUCVUD
      VGUYJUYKRUYDESVQGHRWFWGRUYDVSOVGWHRWFUYDVEUYMWIWJVLZWKVNUXCGUYFVSUYNVOWSV
      PZWLZUXCDFUYOAUWTUXAWMZVUFWLZVUEUXNUYDVFOZUXOUYLUXNVUJVGVIRUXNVEUYDSUYMWN
      WOVLWPUYGVJWQWSZUXCUYBUXFPQZUAUJZUXFPQZUAUYAWTZUXCVUNUAUXSWTZVUNUAUXTWTVU
      OUXCUXQUXFPQZLEWTZVUPUXCVUQLEAUYIUXBUYSVUQKUYIUYSUXBVUQUXKCDEUXPFJUXPVJZX
      AXBXCWCUXQSMZLEWTVUPVURXDVUTLEUXLUXMUXPVHZXEVUNVUQLUAEUXQUXRSUXRVJZVUMUXQ
      UXFPXFXGVLXHUXCVUNUAUXTUXCVUNVUMUXTMZUPUXFPQZUXCUXEFXIOZMZUWTUXAVVDUXCUYI
      VVFUYKEFJXJXKZVUBVUHCDUXEFXLXMVVCVUMUPUXFPVUMUPXSXNXOXPVUNUAUXSUXTXQXRUXC
      UYAUSWGZUXFUSMVULVUOXDUXCUXSUXTUSUXCUXSRUSUXCERUXRUXCLEUXQRUYTUXLRMZUXMRM
      ZUXQRMZUXCVVILEUXCLUYOUYDUYCCERSVQSUYFUYPUYQUYRUYKVUAVUEVUGXTYAUXCVVJLEUX
      CLUYOUYDUYCDERSVQSUYFUYPUYQUYRUYKVUAVUEVUIXTYAUXPRXIOMVVIVVJVVKUXPVUSUUBU
      XLUXMUXPRYBUUCYCZUUDUUEYDUUFUXCUPUSUPUSMUXCUUGWBUUHUUMZUXCRUSUXFYDUXCVVFU
      WTUXAUXFRMZVVGVUBVUHCDUXEFYBXMZYEUAUYAUXFUUIYCYFYGUXCUXJEYHUXCEYHVGZUCZUX
      FDDUXENZUXIPVVQCDDUXEUXCVVPCDVGZVVPVVSUXCUXLUXMVGZLEWTZVVTLEUUJUXCCEYJZDE
      YJZVVSVWAXDUXCCVUCMERCYIVWBUXCCFVUCVUBJYKCREYLERCYMYNUXCDVUCMERDYIVWCUXCD
      FVUCVUHJYKDREYLERDYMYNLECDUUKYCUULUUNUUOUXCVVRUXIPQVVPUXCVVRUPUXIPUXCVVFU
      XAVVRUPVGVVGVUHDUXEFUUPYCUXCUXHUXDUXCUXGUXCUXGUXCUYIUXGUUQMUYKEUURXKZUUSZ
      UXCUXGVWDUUTZUVDZUXCBVVEMZUWTUXAUXDRMZUXCUYIVWHUYKBEFGHIJUVAXKZVUBVUHCDBF
      YBXMZUXCUXGVWEVWFUVBUXCVWHUWTUXAUPUXDPQZVWJVUBVUHCDBFXLXMZUVCYGTYGUXCEYHU
      VEZUCZUXJUXFUXIUBUJZYONZPQZUBYPWTZVWOVWRUBYPUXCVWNVWPYPMZVWRUXCVWNVWTUCZU
      CZUXFVWQUXCVVNVXAVVOTVXBUXIVWPUXCUXIRMZVXAUXCUXHUXDVWGVWKUVFZTVWTVWPRMUXC
      VWNVWPUVGUVHZYQVXBUXFUXDVWPUXHUVINZYONZUXHUFNZVWQUTVXBEVQYHUQUVJMZUWTUXAV
      XGYPMUXQVXGUTQZLEWTUXFVXHUTQVXBUYIVWNVXIUXCUYIVXAUYKTZUXCVWNVWTWDZEVQYHUV
      KXRUXCUWTVXAVUBTUXCUXAVXAVUHTVXBVXGVXBUXDVXFUXCVWIVXAVWKTZVXBVXFVXBVWPUXH
      UXCVWNVWTWMVXBUXGVXBUXGVXBUXGUUAMZVWNVXLVXBUYIVXNVWNXDVXKEUVLXKYFUVNUVMZU
      VOZUVPZYQZVXBUPUXDVXGVXBUVQVXMVXRUXCVWLVXAVWMTVXBUXDVXFVXMVXPUVRZYRUVSVXB
      VXJLEVXBUYSUCZUXQUXDVXGUXCUYSVVKVXAVVLUVTVXBVWIUYSVXMTVXBVXGRMUYSVXRTVXTU
      XQUYBUXDPVXTVVHUXQUYAMUXQUYBPQUXCVVHVXAUYSVVMYSVXTUXSUYAUXQUXSUXTUWDVXTUY
      SVUTUXQUXSMVXBUYSUWEVVALEUXQUXRSVVBUWAUWBYEUYAUXQUWCYCUXCUXDUYBVGVXAUYSVU
      KYSUWFVXBUXDVXGUTQUYSVXSTYRWCVXGLCDEUXPFJVUSUWGUWHVXBVXHUXDUXHUFNZVXFUXHU
      FNZYONVWQVXBUXDVXFUXHVXBUXDVXMYTZVXBVXFVXQYTVXBUXHUXCUXHRMVXAVWGTYTZUWIVX
      BVYAUXIVYBVWPYOVXBUXDUXHVYCVYDUWJVXBVWPUXHVXBVWPVXEYTVYDVXBUXHVXOUWMUWKUW
      LWSUWNUWOUWPWCUXCUXJVWSXDZVWNUXCVVNVXCVYEVVOVXDUBUXFUXIUWQYCTYFUWRUWS $.
  $}

  ${
    $d x y I $.  $d x y M $.  $d x y Y $.
    rrntotbnd.1 $e |- X = ( RR ^m I ) $.
    rrntotbnd.2 $e |- M = ( ( Rn ` I ) |` ( Y X. Y ) ) $.
    $( A set in Euclidean space is totally bounded iff its is bounded.
       (Contributed by Jeff Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro,
       16-Sep-2015.) $)
    rrntotbnd $p |- ( I e. Fin ->
                      ( M e. ( TotBnd ` Y ) <-> M e. ( Bnd ` Y ) ) ) $=
      ( vx vy wcel cr co cfv c1 eqid syl cle wbr wa cmul adantr cfn ccnfld cpws
      cress cds cres chash csqrt caddc crrn repwsmet rrnmet hashcl nn0re nn0ge0
      cxp cn0 resqrtcld cc0 sqrtge0d ge0p1rpd crp 1rp cv cmet metcl 3expb sylan
      a1i simprl simprr w3a metge0 syl3anc simpld remulcld peano2re id rrnequiv
      jca simprd lep1d lemul1a syl31anc letrd recnd mullidd breqtrrd cc ctotbnd
      wss cbnd wb ax-resscn cnpwstotbnd mpan equivbnd2 ) AUAIZGHUBJUDKAUCKZUELZ
      DDUPUFZBAUGLZUHLZMUIKZMWTAUJLZCDWTACWSWSNZWTNZEUKZACEULZWRXCWRXBUQIZXCJIZ
      AUMZXJXBXBUNZXBUOZUROZWRXJUSXCPQXLXJXBXMXNUTOVAMVBIWRVCVIWRGVDZCIZHVDZCIZ
      RZRZXPXRXEKZXCXPXRWTKZSKZXDYCSKZWRXECVELZIZXTYBJIZXIYGXQXSYHXPXRXECVFVGVH
      ZYAXCYCWRXKXTXOTZYAYCJIZUSYCPQZYAWTYFIZXQXSYKYLRZWRYMXTXHTWRXQXSVJWRXQXSV
      KYMXQXSVLYKYLXPXRWTCVFXPXRWTCVMVTVNZVOZVPYAXDYCWRXDJIZXTWRXKYQXOXCVQOTZYP
      VPYAYCYBPQZYBYDPQZWRWTXPXRACWSXFXGEWRVRVSZWAYAXKYQYNXCXDPQYDYEPQYJYRYOYAX
      CYJWBXCXDYCWCWDWEYAYCYBMYBSKPYAYSYTUUAVOYAYBYAYBYIWFWGWHXANZFJWIWKWRXADWJ
      LIXADWLLIWMWNJXAADWSXFUUBWOWPWQ $.
  $}

  ${
    rrnheibor.1 $e |- X = ( RR ^m I ) $.
    rrnheibor.2 $e |- M = ( ( Rn ` I ) |` ( Y X. Y ) ) $.
    rrnheibor.3 $e |- T = ( MetOpen ` M ) $.
    rrnheibor.4 $e |- U = ( MetOpen ` ( Rn ` I ) ) $.
    $( Heine-Borel theorem for Euclidean space.  A subset of Euclidean space is
       compact iff it is closed and bounded.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Revised by Mario Carneiro, 22-Sep-2015.) $)
    rrnheibor $p |- ( ( I e. Fin /\ Y C_ X ) ->
               ( T e. Comp <-> ( Y e. ( Clsd ` U ) /\ M e. ( Bnd ` Y ) ) ) ) $=
      ( cfn wcel wss wa ccmp ccmet cfv cmet wb adantr ccld cbnd crrn rrnmet cxp
      ctotbnd cres metres2 eqeltrid sylan biantrurd heibor bitrdi eleq1i rrncms
      cmetss syl bitrid rrntotbnd anbi12d bitrd ) CKLZFEMZNZAOLZDFPQZLZDFUFQLZN
      ZFBUAQLZDFUBQLZNVDVEDFRQZLZVENVIVDVMVEVBCUCQZERQLZVCVMCEGUDVOVCNDVNFFUEUG
      ZVLHVNFEUHUIUJUKDAFIULUMVDVGVJVHVKVGVPVFLZVDVJDVPVFHUNVDVNEPQLZVQVJSVBVRV
      CCEGUOTVNBEFJUPUQURVBVHVKSVCCDEFGHUSTUTVA $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Intervals (continued)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d k x y z A $.  $d k y z F $.  $d y z R $.  $d k y z V $.
    ismrer1.1 $e |- R = ( ( abs o. - ) |` ( RR X. RR ) ) $.
    ismrer1.2 $e |- F = ( x e. RR |-> ( { A } X. { x } ) ) $.
    $( An isometry between ` RR ` and ` RR ^ 1 ` .  (Contributed by Jeff
       Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro, 22-Sep-2015.) $)
    ismrer1 $p |- ( A e. V -> F e. ( R Ismty ( Rn ` { A } ) ) ) $=
      ( vy vz vk wcel cr csn co cv cfv wceq cmin c2 cexp cmap cismty cxp xpeq1d
      wf1o crrn wral cmpt sneq mpteq2dv eqtr4di f1oeq1d oveq2d f1oeq3 syl bitrd
      wb eqid reex vex mapsnf1o3 vtoclg csu csqrt cabs xpeq2d snex xpex fvmpt3i
      wa cc fveq1d adantr cvv fvconst2g sylancr sylan9eqr adantl oveq12d oveq1d
      snidg resubcl absresq eqtr4d recnd abscld sqcld eqeltrd fveq2 sumsn eqtrd
      syldan fveq2d absge0d sqrtsqd wf f1of ffvelcdmda anim12dan rrnmval mp3an1
      cfn snfi remetdval 3eqtr4rd ralrimivva rexmet cmet rrnmet metxmet isismty
      cxmet mp2b mp2an sylanbrc ) BEKZLLBMZUANZDUEZHOZIOZCNZXTDPZYADPZXQUFPZNZQ
      ZILUGHLUGZDCYEUBNKZLLXTMZUANZALYJAOZMZUCZUHZUEZXSHBEXTBQZYPLYKDUEZXSYQLYK
      YODYQYOALXQYMUCZUHDYQALYNYSYQYJXQYMXTBUIZUDUJGUKULYQYKXRQYRXSUQYQYJXQLUAY
      TUMYKXRLDUNUOUPALYJYOXTYJURUSHUTZYOURVAVBZXPYGHILLXPXTLKZYALKZVJZVJZXQJOZ
      YCPZUUGYDPZRNZSTNZJVCZVDPZXTYARNZVEPZYFYBUUFUUMUUOSTNZVDPUUOUUFUULUUPVDUU
      FUULBYCPZBYDPZRNZSTNZUUPXPUUEUUTVKKUULUUTQUUFUUTUUPVKUUFUUTUUNSTNZUUPUUFU
      USUUNSTUUFUUQXTUURYARUUEXPUUQBXQYJUCZPZXTUUCUUQUVCQUUDUUCBYCUVBAXTYSUVBLD
      YLXTQYMYJXQYLXTUIVFGXQYMBVGYLVGVHZVIVLVMXPXTVNKBXQKZUVCXTQUUABEWAZXQXTBVN
      VOVPVQUUEXPUURBXQYAMZUCZPZYAUUDUURUVIQUUCUUDBYDUVHAYAYSUVHLDYLYAQYMUVGXQY
      LYAUIVFGUVDVIVLVRXPYAVNKUVEUVIYAQIUTUVFXQYABVNVOVPVQVSVTUUFUUNLKZUUPUVAQU
      UEUVJXPXTYAWBVRZUUNWCUOWDZUUFUUOUUFUUOUUFUUNUUFUUNUVKWEZWFZWEWGWHUUKUUTJB
      EUUGBQZUUJUUSSTUVOUUHUUQUUIUURRUUGBYCWIUUGBYDWIVSVTWJWLUVLWKWMUUFUUOUVNUU
      FUUNUVMWNWOWKUUFYCXRKZYDXRKZVJYFUUMQZXPUUCUVPUUDUVQXPLXRXTDXPXSLXRDWPUUBL
      XRDWQUOZWRXPLXRYADUVSWRWSXQXBKZUVPUVQUVRBXCZJYCYDXQXRXRURZWTXAUOUUEYBUUOQ
      XPXTYACFXDVRXEXFCLXLPKYEXRXLPKZYIXSYHVJUQCFXGUVTYEXRXHPKUWCUWAXQXRUWBXIYE
      XRXJXMHIDCYELXRXKXNXO $.
  $}

  ${
    $d x y z $.
    reheibor.2 $e |- M = ( ( abs o. - ) |` ( Y X. Y ) ) $.
    reheibor.3 $e |- T = ( MetOpen ` M ) $.
    reheibor.4 $e |- U = ( topGen ` ran (,) ) $.
    $( Heine-Borel theorem for real numbers.  A subset of ` RR ` is compact iff
       it is closed and bounded.  (Contributed by Jeff Madsen, 2-Sep-2009.)
       (Revised by Mario Carneiro, 22-Sep-2015.) $)
    reheibor $p |- ( Y C_ RR -> ( T e. Comp <->
                               ( Y e. ( Clsd ` U ) /\ M e. ( Bnd ` Y ) ) ) ) $=
      ( cr wss c1o cfv c0 cxp cres wcel co wb cismty eqid cxmet vx vy vz csn cv
      crrn cmpt cima cmopn ccmp ccld cbnd wa cfn cmap df1o2 eqeltri crn imassrn
      snfi wf1o wf cabs cmin ccom wceq wral cvv 0ex ismrer1 ax-mp fveq2i oveq2i
      eleqtrri rexmet cmet rrnmet metxmet mp2b mp2an mpbi simpli f1of frn sstri
      isismty a1i rrnheibor sylancr chmph chmeo cc cnxmet id ax-resscn xmetres2
      sstrdi eqeltrid ismtyhmeo syl2anc ismtyres syl22anc xpss12 anidms eqtr4di
      wbr resabs1d oveq1d eleqtrd sseldd syl cmphmph wi hmphsym impbid cioo ctg
      hmphi tgioo eqtri sselii ctopon retopon toponunii hmeocld syl3anc anbi12d
      ismtybnd 3bitr4d ) DHIZJUFKZUAHLUDZUAUEUDMUGZDUHZYNMNZUIKZUJOZYNYKUIKZUKK
      OZYOYNULKOZUMZAUJOZDBUKKOZCDULKOZUMYJJUNOZYNHJUOPZIZYQUUAQJYLUNUPLUTUQZUU
      GYJYNYMURZUUFYMDUSHUUFYMVAZHUUFYMVBUUIUUFIUUJUBUEZUCUEZVCVDVEZHHMZNZPUUKY
      MKUULYMKYKPVFUCHVGUBHVGZYMUUOYKRPZOZUUJUUPUMZYMUUOYLUFKZRPZUUQLVHOYMUVAOV
      IUALUUOYMVHUUOSZYMSVJVKYKUUTUUORJYLUFUPVLVMVNZUUOHTKOZYKUUFTKOZUURUUSQUUO
      UVBVOZUUEYKUUFVPKOUVEUUHJUUFUUFSZVQYKUUFVRVSZUBUCYMUUOYKHUUFWFVTWAWBHUUFY
      MWCHUUFYMWDVSWEWGZYPYRJYOUUFYNUVGYOSZYPSZYRSZWHWIYJAYPWJXFZUUBYQQYJYMDNZA
      YPWKPZOUVMYJCYORPZUVOUVNYJCDTKZOZYOYNTKOZUVPUVOIYJCUUMDDMZNZUVQEYJUUMWLTK
      ODWLIUWAUVQOWMYJDHWLYJWNZWOWQUUMDWLWPWIWRZYJUVEUUGUVSUVHUVIYKYNUUFWPWIZAY
      PCYODYNFUVKWSWTYJUVNUUOUVTNZYORPZUVPYJUVDUVEUURYJUVNUWFOUVDYJUVFWGUVEYJUV
      HWGUURYJUVCWGUWBDYNUWEYOYMUUOYKHUUFYNSUWESUVJXAXBYJUWECYORYJUWEUWACYJUUMU
      VTUUNYJUVTUUNIDHDHXCXDXGEXEXHXIZXJUVNAYPXRXKUVMUUBYQAYPXLUVMYPAWJXFYQUUBX
      MAYPXNYPAXLXKXOXKYJUUCYSUUDYTYJYMBYRWKPZOYJUUCYSQUUQUWHYMUVDUVEUUQUWHIUVF
      UVHBYRUUOYKHUUFBXPURXQKZUUOUIKZGUUOUWJUVBUWJSXSXTUVLWSVTUVCYAUWBDYMBYRHHB
      BUWIHYBKGYCUQYDYEWIYJUVRUVSUVNUVPOUUDYTQUWCUWDUWGUVNCYODYNYHYFYGYI $.
  $}

  ${
    $d r x y A $.  $d r x y B $.  $d r x y J $.  $d r x y M $.
    iccbnd.1 $e |- J = ( A [,] B ) $.
    iccbnd.2 $e |- M = ( ( abs o. - ) |` ( J X. J ) ) $.
    $( A closed interval in ` RR ` is bounded.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Proof shortened by Mario Carneiro, 22-Sep-2015.) $)
    iccbnd $p |- ( ( A e. RR /\ B e. RR ) -> M e. ( Bnd ` J ) ) $=
      ( vx vy vr cr wcel wa cfv cv co cle wbr wral cmin cc cmet wrex cbnd cnmet
      cabs ccom cxp cres cicc iccssre eqsstrid ax-resscn sstrdi metres2 sylancr
      wss eqeltrid resubcl ancoms oveqi wceq ovres adantl eqtrid anim12dan eqid
      sselda cnmetdval syl eqtrd caddc w3a simprr eleqtrdi elicc2 adantr simp1d
      wb mpbid syl2anc simpll simprl simplr simp3d lesub1dd subled simp2d letrd
      readdcld lesub2dd lesubadd2d absdifled mpbir2and eqbrtrd ralrimivva breq2
      2ralbidv rspcev isbnd3b sylanbrc ) AJKZBJKZLZDCUAMZKGNZHNZDOZINZPQZHCRGCR
      ZIJUBZDCUCMKXCDUESUFZCCUGUHZXDFXCXLTUAMKCTUPXMXDKUDXCCJTXCCABUIOZJEABUJUK
      ULUMZXLCTUNUOUQXCBASOZJKZXGXPPQZHCRGCRZXKXBXAXQBAURUSZXCXRGHCCXCXECKZXFCK
      ZLZLZXGXEXFSOUEMZXPPYDXGXEXFXLOZYEYDXGXEXFXMOZYFDXMXEXFFUTYCYGYFVAXCXEXFC
      CXLVBVCVDYDXETKZXFTKZLYFYEVAXCYAYHYBYIXCCTXEXOVGXCCTXFXOVGVEXEXFXLXLVFVHV
      IVJYDYEXPPQXFXPSOZXEPQXEXFXPVKOZPQYDYJAXEYDXFJKZXQYJJKYDYLAXFPQZXFBPQZYDX
      FXNKZYLYMYNVLZYDXFCXNXCYAYBVMEVNXCYOYPVRYCABXFVOVPVSZVQZXCXQYCXTVPZXFXPUR
      VTXAXBYCWAZYDXEJKZAXEPQZXEBPQZYDXEXNKZUUAUUBUUCVLZYDXECXNXCYAYBWBEVNXCUUD
      UUEVRYCABXEVOVPVSZVQZYDXFAXPYRYTYSYDXFBAYRXAXBYCWCZYTYDYLYMYNYQWDWEWFYDUU
      AUUBUUCUUFWGWHYDXEBYKUUGUUHYDXFXPYRYSWIYDUUAUUBUUCUUFWDYDBXFSOXPPQBYKPQYD
      AXFBYTYRUUHYDYLYMYNYQWGWJYDBXFXPUUHYRYSWKVSWHYDXEXFXPUUGYRYSWLWMWNWOXJXSI
      XPJXHXPVAXIXRGHCCXHXPXGPWPWQWRVTIGHDCWSWT $.
  $}

  ${
    icccmpALT.1 $e |- J = ( A [,] B ) $.
    icccmpALT.2 $e |- M = ( ( abs o. - ) |` ( J X. J ) ) $.
    icccmpALT.3 $e |- T = ( MetOpen ` M ) $.
    $( A closed interval in ` RR ` is compact.  Alternate proof of ~ icccmp
       using the Heine-Borel theorem ~ heibor .  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Proof shortened by Mario Carneiro, 14-Aug-2014.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    icccmpALT $p |- ( ( A e. RR /\ B e. RR ) -> T e. Comp ) $=
      ( cr wcel wa ccmp cioo crn ctg cfv ccld cbnd cicc co icccld iccbnd wss wb
      eqeltrid iccssre eqsstrid eqid reheibor syl mpbir2and ) AIJBIJKZCLJZDMNOP
      ZQPZJZEDRPJZULDABSTZUOFABUAUEABDEFGUBULDIUCUMUPUQKUDULDURIFABUFUGCUNEDGHU
      NUHUIUJUK $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Operation properties
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Obsolete part of JM's mathbox as of 13-Aug-2026.

  This and the following sections contain outdated material.  All relevant
  definitions and theorems are available based on extensible structures, which
  is the preferred way in set.mm to deal with groups, rings and related
  structures.

  All definitions and theorems in the following are marked as deprecated
  (containing the tag "(New usage is discouraged.)" in their comments).
  In most cases, the corresponding definitions and theorems based on extensible
  structures are indicated within the comments.

  This and the following sections in JM's mathox will be removed from set.mm on
  13-Aug-2027, unless there are any objections.

$)

  $c Ass $.

  $( Extend class notation with a device to add associativity to internal
     operations. $)
  cass $a class Ass $.

  ${
    $d g x y z $.
    $( A device to add associativity to various sorts of internal operations.
       The definition is meaningful when ` g ` is a magma at least.
       (Contributed by FL, 1-Nov-2009.)  (New usage is discouraged.) $)
    df-ass $a |- Ass = { g | A. x e. dom dom g A. y e. dom dom g
    A. z e. dom dom g ( ( x g y ) g z ) = ( x g ( y g z ) ) } $.
  $}

  $c ExId $.

  $( Extend class notation with the class of all the internal operations with
     an identity element. $)
  cexid $a class ExId $.

  ${
    $d g x y $.
    $( A device to add an identity element to various sorts of internal
       operations.  (Contributed by FL, 2-Nov-2009.)
       (New usage is discouraged.) $)
    df-exid $a |- ExId = { g | E. x e. dom dom g A. y e. dom dom g
    ( ( x g y ) = y /\ ( y g x ) = y ) } $.
  $}

  ${
    $d G g x y z $.  $d X g x y z $.
    isass.1 $e |- X = dom dom G $.
    $( The predicate "is an associative operation".  (Contributed by FL,
       1-Nov-2009.)  (New usage is discouraged.) $)
    isass $p |- ( G e. A -> ( G e. Ass <-> A. x e. X A. y e. X A. z e. X
      ( ( x G y ) G z ) = ( x G ( y G z ) ) ) ) $=
      ( vg cv co wceq cdm wral wcel w3a wi wal eleq2d oveq eqtrd cass 3anbi123d
      dmeq oveq1d oveq2d eqeq12d imbi12d albidv 2albidv r3al 3bitr4g eqcomi a1i
      dmeqd raleqdv raleqbidv 2ralbidv 3bitrd df-ass elab2g ) AIZBIZHIZJZCIZVCJ
      ZVAVBVEVCJZVCJZKZCVCLZLZMBVKMAVKMZVAVBEJZVEEJZVAVBVEEJZEJZKZCFMZBFMAFMZHE
      UADVCEKZVLVQCELZLZMZBWBMZAWBMZWCBFMZAFMVSVTVAVKNZVBVKNZVEVKNZOZVIPZCQZBQA
      QVAWBNZVBWBNZVEWBNZOZVQPZCQZBQAQVLWEVTWLWRABVTWKWQCVTWJWPVIVQVTWGWMWHWNWI
      WOVTVKWBVAVTVJWAVCEUCUNZRVTVKWBVBWSRVTVKWBVEWSRUBVTVFVNVHVPVTVFVMVEVCJVNV
      TVDVMVEVCVAVBVCESUDVMVEVCESTVTVHVAVOVCJVPVTVGVOVAVCVBVEVCESUEVAVOVCESTUFU
      GUHUIVIABCVKVKVKUJVQABCWBWBWBUJUKVTWDWFAWBFWBFKVTFWBGULUMZVTWCBWBFWTUOUPV
      TWCVRABFFVTVQCWBFWTUOUQURABCHUSUT $.
  $}

  ${
    $d G g x y $.  $d X g x y $.
    isexid.1 $e |- X = dom dom G $.
    $( The predicate ` G ` has a left and right identity element.  (Contributed
       by FL, 2-Nov-2009.)  (Revised by Mario Carneiro, 22-Dec-2013.)
       (New usage is discouraged.) $)
    isexid $p |- ( G e. A -> ( G e. ExId <-> E. x e. X A. y e. X
      ( ( x G y ) = y /\ ( y G x ) = y ) ) ) $=
      ( vg cv co wceq wa cdm wral wrex cexid dmeq dmeqd eqtr4di oveq eqeq1d
      anbi12d raleqbidv rexeqbidv df-exid elab2g ) AHZBHZGHZIZUGJZUGUFUHIZUGJZK
      ZBUHLZLZMZAUONUFUGDIZUGJZUGUFDIZUGJZKZBEMZAENGDOCUHDJZUPVBAUOEVCUODLZLEVC
      UNVDUHDPQFRZVCUMVABUOEVEVCUJURULUTVCUIUQUGUFUGUHDSTVCUKUSUGUGUFUHDSTUAUBU
      CABGUDUE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Groups and related structures
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Magma $.

  $( Extend class notation with the class of all magmas. $)
  cmagm $a class Magma $.

  ${
    $d g t $.
    $( Obsolete version of ~ df-mgm as of 3-Feb-2020.  A magma is a binary
       internal operation.  (Contributed by FL, 2-Nov-2009.)
       (New usage is discouraged.) $)
    df-mgmOLD $a |- Magma = { g | E. t g : ( t X. t ) --> t } $.
  $}

  ${
    $d G g t $.  $d X t $.
    ismgmOLD.1 $e |- X = dom dom G $.
    $( Obsolete version of ~ ismgm as of 3-Feb-2020.  The predicate "is a
       magma".  (Contributed by FL, 2-Nov-2009.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ismgmOLD $p |- ( G e. A -> ( G e. Magma <-> G : ( X X. X ) --> X ) ) $=
      ( vt vg wcel cmagm cv cdm wceq cxp wf wa wex c0 wi dmeq wb cvv exbidv f00
      df-mgmOLD elab2g dm0 dmeqi eqtri eqtr2di adantr sylbi xpeq12 anidms feq23
      feq1 syl mpancom eqeq1 imbi12d mpbiri wn fdm wne df-ne dmxp sylbir eqeq1d
      biimpcd eqcoms com12 pm2.61i pm4.71ri exbii bitrdi dmexg xpeq12i ceqsexgv
      3syl eqcomi feq23i bitrd ) BAGZBHGZEIZBJZJZKZWCWCLZWCBMZNZEOZCCLZCBMZWAWB
      WHEOZWJWGWCFIZMZEOWMFBHAWNBKWOWHEWGWCWNBUNUAEFUCUDWHWIEWHWFWCPKZWHWFQZWPW
      QPPLZPBMZPWEKZQWSBPKZWRPKZNWTWRBUBXAWTXBXAWDPJZKZWTBPRXDWEXCJZPWDXCRXEXCP
      XCPUEUFUEUGUHUOUIUJWPWHWSWFWTWGWRKZWPWHWSSWPXFWCPWCPUKULWGWCWRPBUMUPWCPWE
      UQURUSWHWPUTZWFWHWDWGKWEWGJZKXGWFQZWGWCBVAWDWGRXIXHWEXGXHWEKWFXGXHWCWEXGW
      CPVBXHWCKWCPVCWCWCVDVEVFVGVHVQVIVJVKVLVMWAWDTGWETGWJWLSBAVNWDTVNWHWLEWETW
      FWHWEWELZWEBMZWLWGXJKZWFWHXKSWFXLWCWEWCWEUKULWGWCXJWEBUMUPXJWEWKCBWECWECC
      WEDVRZXMVOXMVSVMVPVQVT $.
  $}

  ${
    clmgmOLD.1 $e |- X = dom dom G $.
    $( Obsolete version of ~ mgmcl as of 3-Feb-2020.  Closure of a magma.
       (Contributed by FL, 14-Sep-2010.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    clmgmOLD $p |- ( ( G e. Magma /\ A e. X /\ B e. X ) -> ( A G B ) e. X ) $=
      ( cmagm wcel co wi cxp wf ismgmOLD fovcdm 3exp biimtrdi pm2.43i 3imp ) CF
      GZADGZBDGZABCHDGZRSTUAIIZRRDDJDCKZUBFCDELUCSTUAABDDDCMNOPQ $.
  $}

  ${
    $d G u x y $.  $d X u x y $.
    opidonOLD.1 $e |- X = dom dom G $.
    $( Obsolete version of ~ mgmidpfod as of 23-Jan-2020.  An operation with a
       left and right identity element is onto.  (Contributed by FL,
       2-Nov-2009.)  (Revised by Mario Carneiro, 22-Dec-2013.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    opidonOLD $p |- ( G e. ( Magma i^i ExId ) ->
      G : ( X X. X ) -onto-> X ) $=
      ( vy vu vx cmagm cexid cin wcel cxp wf cv co wceq wrex wral wfo sseli syl
      inss1 ismgmOLD ibi wa inss2 isexid biimpd sylc simpl ralimi oveq2 eqeq12d
      id rspcv eqcom eqeq1d bitrid rspcev ex syld syl5 reximdv impcom ralrimiva
      foov sylanbrc ) AGHIZJZBBKZBALZDMZEMZFMZANZOZFBPZEBPZDBQZVIBARVHAGJZVJVGG
      AGHUASVSVJGABCUBUCTVHVNVMOZVMVLANVMOZUDZFBQZEBPZVRVHAHJZWEWDVGHAGHUESZWFW
      EWEWDEFHABCUFUGUHWDVQDBVKBJZWDVQWGWCVPEBWCVTFBQZWGVPWBVTFBVTWAUIUJWGWHVLV
      KANZVKOZVPVTWJFVKBVMVKOZVNWIVMVKVMVKVLAUKZWKUMULUNWGWJVPVOWJFVKBVOVNVKOWK
      WJVKVNUOWKVNWIVKWLUPUQURUSUTVAVBVCVDTEFDBBBAVEVF $.
  $}

  $( Obsolete version of ~ mgmidprnd as of 23-Jan-2020.  Range of an operation
     with a left and right identity element.  (Contributed by FL, 2-Nov-2009.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  rngopidOLD $p |- ( G e. ( Magma i^i ExId ) -> ran G = dom dom G ) $=
    ( cmagm cexid cin wcel cdm cxp wfo crn wceq eqid opidonOLD forn syl ) ABCDE
    AFFZOGZOAHAIOJAOOKLPOAMN $.

  ${
    opidon2OLD.1 $e |- X = ran G $.
    $( Obsolete version of ~ mgmfod as of 23-Jan-2020.  An operation with a
       left and right identity element is onto.  (Contributed by FL,
       2-Nov-2009.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    opidon2OLD $p |- ( G e. ( Magma i^i ExId ) ->
      G : ( X X. X ) -onto-> X ) $=
      ( cmagm cexid cin wcel cdm cxp wfo eqid opidonOLD wceq crn eqtr2id xpeq12
      forn wb anidms syl foeq2 foeq3 bitrd biimpd mpcom ) ADEFGAHHZUFIZUFAJZBBI
      ZBAJZAUFUFKLUFBMZUHUJUHBANUFCUGUFAQOUKUHUJUKUHUIUFAJZUJUKUGUIMZUHULRUKUMU
      FBUFBPSUGUIUFAUATUFBUIAUBUCUDUET $.
  $}

  ${
    $d G u x $.  $d X u x $.
    isexid2.1 $e |- X = ran G $.
    $( Obsolete theorem.  If ` G e. ( Magma i^i ExId ) ` , then it has a left
       and right identity element that belongs to the range of the operation.
       (Contributed by FL, 12-Dec-2009.)  (Revised by Mario Carneiro,
       22-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    isexid2 $p |- ( G e. ( Magma i^i ExId ) -> E. u e. X A. x e. X
      ( ( u G x ) = x /\ ( x G u ) = x ) ) $=
      ( crn wceq cmagm cexid cin wcel cv co wa wral wrex cdm raleq rexeqbi1dv
      wi rngopidOLD elin eqid isexid ibi a1d adantl sylbi eqeq2 imbitrrid mpcom
      imbi12d com12 sylibrd ax-mp ) DCFZGZCHIJKZBLZALZCMUTGUTUSCMUTGNZADOZBDPZT
      EUQURVAAUPOZBUPPZVCURUQVEUPCQQZGZURUQVETZCUAURVHVGDVFGZVAAVFOZBVFPZTZURCH
      KZCIKZNVLCHIUBVNVLVMVNVKVIVNVKBAICVFVFUCUDUEUFUGUHVGUQVIVEVKUPVFDUIVDVJBU
      PVFVAAUPVFRSULUJUKUMVBVDBDUPVAADUPRSUNUO $.
  $}

  ${
    $d G u x y $.  $d X u x y $.
    exidu1.1 $e |- X = ran G $.
    $( Obsolete theorem, use ~ mgmidmo or ~ mndideu instead.  Uniqueness of the
       left and right identity element of a magma when it exists.  (Contributed
       by FL, 12-Dec-2009.)  (Revised by Mario Carneiro, 22-Dec-2013.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    exidu1 $p |- ( G e. ( Magma i^i ExId ) ->
      E! u e. X A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) ) $=
      ( vy cmagm wcel cv co wceq wa wral weq ralimi id eqeq12d rspcv syl5 oveq1
      cexid wrex wi wreu isexid2 simpl oveq2 simpr im2anan9r eqtr2 equcomd syl6
      cin rgen2 eqeq1d ovanraleqv reu4 sylanblrc ) CGUAUMHBIZAIZCJZUTKZUTUSCJUT
      KZLZADMZBDUBVEFIZUTCJZUTKZUTVFCJZUTKZLZADMZLZBFNZUCZFDMBDMVEBDUDABCDEUEVO
      BFDDUSDHZVFDHZLVMUSVFCJZVFKZVRUSKZLZVNVQVEVSVPVLVTVEVBADMVQVSVDVBADVBVCUF
      OVBVSAVFDAFNZVAVRUTVFUTVFUSCUGWBPQRSVLVJADMVPVTVKVJADVHVJUHOVJVTAUSDABNZV
      IVRUTUSUTUSVFCTWCPQRSUIWAFBVRVFUSUJUKULUNVEVLBFDVBVHAUTUSUTCDVFVNVAVGUTUS
      VFUTCTUOUPUQUR $.
  $}

  ${
    $d G u x $.  $d X u x $.
    idrval.1 $e |- X = ran G $.
    idrval.2 $e |- U = ( GId ` G ) $.
    $( Obsolete theorem, use ~ idvalriota instead.  The value of the identity
       element.  (Contributed by FL, 12-Dec-2009.)  (Revised by Mario Carneiro,
       22-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    idrval $p |- ( G e. A -> U = ( iota_ u e. X
                   A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) ) ) $=
      ( wcel cgi cfv cv co wceq wa wral crio gidval eqtrid ) ECIDEJKBLZALZEMUAN
      UATEMUANOAFPBFQHABECFGRS $.
  $}

  ${
    $d G u x $.  $d X u x $.
    iorlid.1 $e |- X = ran G $.
    iorlid.2 $e |- U = ( GId ` G ) $.
    $( Obsolete theorem, use ~ mgmidcl instead.  A magma right and left
       identity belongs to the underlying set of the operation.  (Contributed
       by FL, 12-Dec-2009.)  (Revised by Mario Carneiro, 22-Dec-2013.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    iorlid $p |- ( G e. ( Magma i^i ExId ) -> U e. X ) $=
      ( vu vx cmagm cexid cin wcel cv co wceq wa wral crio idrval wreu exidu1
      riotacl syl eqeltrd ) BHIJZKZAFLZGLZBMUGNUGUFBMUGNOGCPZFCQZCGFUDABCDERUEU
      HFCSUICKGFBCDTUHFCUAUBUC $.
  $}

  ${
    $d A x $.  $d G u x $.  $d U u x $.  $d X u x $.
    cmpidelt.1 $e |- X = ran G $.
    cmpidelt.2 $e |- U = ( GId ` G ) $.
    $( Obsolete theorem, use ~ mgmlrid instead.  A magma right and left
       identity element keeps the other elements unchanged.  (Contributed by
       FL, 12-Dec-2009.)  (Revised by Mario Carneiro, 22-Dec-2013.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    cmpidelt $p |- ( ( G e. ( Magma i^i ExId ) /\ A e. X ) ->
      ( ( U G A ) = A /\ ( A G U ) = A ) ) $=
      ( vx vu cmagm cexid cin wcel cv co wceq wa wral crio oveq1 eqeq12d idrval
      eqcomd wreu iorlid exidu1 eqeq1d ovanraleqv riota2 syl2anc mpbird anbi12d
      wb oveq2 id rspccva sylan ) CIJKZLZBGMZCNZUSOZUSBCNZUSOZPZGDQZADLBACNZAOZ
      ABCNZAOZPZURVEHMZUSCNZUSOZUSVKCNUSOPGDQZHDRZBOZURBVOGHUQBCDEFUAUBURBDLVNH
      DUCVEVPULBCDEFUDGHCDEUEVNVEHDBVMVAGUSVKUSCDBVKBOVLUTUSVKBUSCSUFUGUHUIUJVD
      VJGADUSAOZVAVGVCVIVQUTVFUSAUSABCUMVQUNZTVQVBVHUSAUSABCSVRTUKUOUP $.
  $}

  $c SemiGrp $.

  $( Extend class notation with the class of all semigroups. $)
  csem $a class SemiGrp $.

  $( Obsolete version of ~ df-sgrp as of 3-Feb-2020.  A semigroup is an
     associative magma.  (Contributed by FL, 2-Nov-2009.)
     (New usage is discouraged.) $)
  df-sgrOLD $a |- SemiGrp = ( Magma i^i Ass ) $.

  $( Obsolete version of ~ sgrpmgm as of 3-Feb-2020.  A semigroup is a magma.
     (Contributed by FL, 2-Nov-2009.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  smgrpismgmOLD $p |- ( G e. SemiGrp -> G e. Magma ) $=
    ( cmagm wcel cass cin csem elin simplbi df-sgrOLD eleq2s ) ABCZABDEZFALCKAD
    CABDGHIJ $.

  ${
    $d G x y z $.  $d X x y z $.
    issmgrpOLD.1 $e |- X = dom dom G $.
    $( Obsolete version of ~ issgrp as of 3-Feb-2020.  The predicate "is a
       semigroup".  (Contributed by FL, 2-Nov-2009.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    issmgrpOLD $p |- ( G e. A -> ( G e. SemiGrp
       <-> ( G : ( X X. X ) --> X /\ A. x e. X A. y e. X A. z e. X
         ( ( x G y ) G z ) = ( x G ( y G z ) ) ) ) ) $=
      ( csem wcel cmagm cass cin cxp wf cv co wceq wral wa bitrid elin ismgmOLD
      df-sgrOLD eleq2i isass anbi12d ) EHIEJKLZIZEDIZFFMFENZAOZBOZEPCOZEPUKULUM
      EPEPQCFRBFRAFRZSZHUGEUCUDUHEJIZEKIZSUIUOEJKUAUIUPUJUQUNDEFGUBABCDEFGUEUFT
      T $.
  $}

  ${
    $d G x y z $.  $d X x y z $.
    smgrpmgm.1 $e |- X = dom dom G $.
    $( Obsolete theorem, use ~ sgrpmgm instead.  A semigroup is a magma.
       (Contributed by FL, 2-Nov-2009.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    smgrpmgm $p |- ( G e. SemiGrp -> G : ( X X. X ) --> X ) $=
      ( vx vy vz csem wcel wf cv co wceq wral issmgrpOLD simpl biimtrdi pm2.43i
      cxp wa ) AGHZBBRBAIZTTUADJZEJZAKFJZAKUBUCUDAKAKLFBMEBMDBMZSUADEFGABCNUAUE
      OPQ $.
  $}

  ${
    $d G x y z $.  $d X x y z $.
    smgrpassOLD.1 $e |- X = dom dom G $.
    $( Obsolete version of ~ sgrpass as of 3-Feb-2020.  A semigroup is
       associative.  (Contributed by FL, 2-Nov-2009.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    smgrpassOLD $p |- ( G e. SemiGrp ->
      A. x e. X A. y e. X A. z e. X ( ( x G y ) G z ) = ( x G ( y G z ) ) ) $=
      ( csem wcel cv co wceq wral cxp wf wa issmgrpOLD simpr biimtrdi pm2.43i )
      DGHZAIZBIZDJCIZDJUAUBUCDJDJKCELBELAELZTTEEMEDNZUDOUDABCGDEFPUEUDQRS $.
  $}

  $c MndOp $.

  $( Extend class notation with the class of all monoids. $)
  cmndo $a class MndOp $.

  $( Obsolete definition, use ~ df-mnd instead.  A monoid is a semigroup with
     an identity element.  (Contributed by FL, 2-Nov-2009.)
     (New usage is discouraged.) $)
  df-mndo $a |- MndOp = ( SemiGrp i^i ExId ) $.

  $( Obsolete version of ~ mndsgrp as of 3-Feb-2020.  A monoid is a semigroup.
     (Contributed by FL, 2-Nov-2009.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  mndoissmgrpOLD $p |- ( G e. MndOp -> G e. SemiGrp ) $=
    ( csem wcel cexid cin cmndo elin simplbi df-mndo eleq2s ) ABCZABDEZFALCKADC
    ABDGHIJ $.

  $( Obsolete theorem, use ~ mndid instead.  A monoid has an identity element.
     (Contributed by FL, 2-Nov-2009.)  (New usage is discouraged.)  (New usage
     is discouraged.)  (Proof modification is discouraged.) $)
  mndoisexid $p |- ( G e. MndOp -> G e. ExId ) $=
    ( cexid wcel csem cin cmndo elinel2 df-mndo eleq2s ) ABCADBEFADBGHI $.

  $( Obsolete version of ~ mndmgm as of 3-Feb-2020.  A monoid is a magma.
     (Contributed by FL, 2-Nov-2009.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  mndoismgmOLD $p |- ( G e. MndOp -> G e. Magma ) $=
    ( cmndo wcel csem cmagm mndoissmgrpOLD smgrpismgmOLD syl ) ABCADCAECAFAGH
    $.

  $( Obsolete theorem, use ~ mndmgm and/or ~ mndid instead.  A monoid is a
     magma with an identity element.  (Contributed by FL, 18-Feb-2010.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  mndomgmid $p |- ( G e. MndOp -> G e. ( Magma i^i ExId ) ) $=
    ( cmndo wcel cmagm cexid mndoismgmOLD mndoisexid elind ) ABCDEAAFAGH $.

  ${
    $d G x y $.  $d X x y $.
    ismndo.1 $e |- X = dom dom G $.
    $( Obsolete theorem, use ~ ismnddef instead.  The predicate "is a monoid".
       (Contributed by FL, 2-Nov-2009.)  (Revised by Mario Carneiro,
       22-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ismndo $p |- ( G e. A -> ( G e. MndOp
     <-> ( G e. SemiGrp /\ E. x e. X A. y e. X
      ( ( x G y ) = y /\ ( y G x ) = y ) ) ) ) $=
      ( cmndo wcel csem cexid cin cv co wceq wa wral wrex df-mndo eleq2i bitrid
      elin isexid anbi2d ) DGHDIJKZHZDCHZDIHZALZBLZDMUINUIUHDMUINOBEPAEQZOZGUDD
      RSUEUGDJHZOUFUKDIJUAUFULUJUGABCDEFUBUCTT $.
  $}

  ${
    $d G x y z $.  $d X x y z $.
    ismndo1.1 $e |- X = dom dom G $.
    $( Obsolete theorem, use ~ ismnd instead.  The predicate "is a monoid".
       (Contributed by FL, 2-Nov-2009.)  (Revised by Mario Carneiro,
       22-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ismndo1 $p |- ( G e. A -> ( G e. MndOp <->
      ( G : ( X X. X ) --> X /\
        A. x e. X A. y e. X A. z e. X
          ( ( x G y ) G z ) = ( x G ( y G z ) ) /\
        E. x e. X A. y e. X
         ( ( x G y ) = y /\ ( y G x ) = y ) ) ) ) $=
      ( wcel cmndo csem cv co wceq wa wral wrex cxp wf w3a ad2antrl smgrpassOLD
      ismndo smgrpmgm simprr 3simpa issmgrpOLD imbitrrid imp simpr3 jca impbida
      3jca bitrd ) EDHZEIHEJHZAKZBKZELZUQMUQUPELUQMNBFOAFPZNZFFQFERZURCKZELUPUQ
      VBELELMCFOBFOAFOZUSSZABDEFGUBUNUTVDUNUTNVAVCUSUOVAUNUSEFGUCTUOVCUNUSABCEF
      GUATUNUOUSUDULUNVDNUOUSUNVDUOVDUOUNVAVCNVAVCUSUEABCDEFGUFUGUHUNVAVCUSUIUJ
      UKUM $.
  $}

  ${
    $d G x y z $.  $d X x y z $.
    ismndo2.1 $e |- X = ran G $.
    $( Obsolete theorem, use ~ ismnd instead.  The predicate "is a monoid".
       (Contributed by FL, 2-Nov-2009.)  (Revised by Mario Carneiro,
       22-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ismndo2 $p |- ( G e. A -> ( G e. MndOp <->
      ( G : ( X X. X ) --> X /\
        A. x e. X A. y e. X A. z e. X
          ( ( x G y ) G z ) = ( x G ( y G z ) ) /\
        E. x e. X A. y e. X
         ( ( x G y ) = y /\ ( y G x ) = y ) ) ) ) $=
      ( wcel cdm wceq cxp wf cv co wral wrex w3a wi a1i wb cmndo wa cmagm cexid
      crn cin mndomgmid rngopidOLD syl eqtrid fdm dmeqd dmxpid eqtr2di 3ad2ant1
      eqid ismndo1 xpid11 biimpri feq23 mpancom raleqbi1dv rexeqbi1dv 3anbi123d
      raleq bibi2d syl5ibrcom pm5.21ndd ) EDHZFEIZIZJZEUAHZFFKZFELZAMZBMZENZCMZ
      ENVPVQVSENENJZCFOZBFOZAFOZVRVQJVQVPENVQJUBZBFOZAFPZQZVMVLRVIVMFEUEZVKGVME
      UCUDUFHWHVKJEUGEUHUIUJSWGVLRVIVOWCVLWFVOVKVNIFVOVJVNVNFEUKULFUMUNUOSVIVMW
      GTVLVMVKVKKZVKELZVTCVKOZBVKOZAVKOZWDBVKOZAVKPZQZTABCDEVKVKUPUQVLWGWPVMVLV
      OWJWCWMWFWOVNWIJZVLVOWJTWQVLFVKURUSVNFWIVKEUTVAWBWLAFVKWAWKBFVKVTCFVKVEVB
      VBWEWNAFVKWDBFVKVEVCVDVFVGVH $.
  $}

  ${
    $d G w x y z $.
    $( Obsolete theorem, use ~ grpmnd instead.  A group is a monoid.
       (Contributed by FL, 2-Nov-2009.)  (Revised by Mario Carneiro,
       22-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    grpomndo $p |- ( G e. GrpOp -> G e. MndOp ) $=
      ( vx vy vz vw cgr wcel cmndo crn cxp wf cv co wceq wral wrex wa w3a eqid
      wi isgrpo biimpd grpoidinv simpl ralimi reximi biimprcd 3exp impcom com3l
      ismndo2 syl mpcom expdcom a1i com13 3imp syli pm2.43i ) AFGZAHGZUTUTAIZVB
      JVBAKZBLZCLZAMZDLZAMVDVEVGAMAMNDVBOCVBOBVBOZELZVDAMVDNVEVDAMZVINCVBPQBVBO
      EVBPZRZVAUTUTVLBCDEFAVBVBSZUAUBVCVHVKUTVATZVKVHVCVNVHVCVNTTVKUTVHVCVAVFVE
      NVJVENQZVIVEAMVDNVEVIAMVDNQEVBPZQZCVBOZBVBPZUTVHVCQZVATZCEBAVBVMUCVSVOCVB
      OZBVBPZUTWATVRWBBVBVQVOCVBVOVPUDUEUFVTWCUTVAVCVHWCVNTVCVHWCVNUTVAVCVHWCRB
      CDFAVBVMUKUGUHUIUJULUMUNUOUPUQURUS $.
  $}

  ${
    exidcl.1 $e |- X = ran G $.
    $( Obsolete theorem, use ~ mgmcl instead.  Closure of the binary operation
       of a magma with identity.  (Contributed by Jeff Madsen, 16-Jun-2011.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    exidcl $p |- ( ( G e. ( Magma i^i ExId ) /\ A e. X /\ B e. X )
                                            -> ( A G B ) e. X ) $=
      ( cmagm cexid cin wcel w3a co cdm wa crn rngopidOLD eqtrid eleq2d anbi12d
      pm5.32i inss1 sseli eqid clmgmOLD syl3an1 3expb sylbi 3impb wceq 3ad2ant1
      eleqtrrd ) CFGHZIZADIZBDIZJABCKZCLLZDULUMUNUOUPIZULUMUNMZMULAUPIZBUPIZMZM
      UQULURVAULUMUSUNUTULDUPAULDCNUPECOPZQULDUPBVBQRSULUSUTUQULCFIUSUTUQUKFCFG
      TUAABCUPUPUBUCUDUEUFUGULUMDUPUHUNVBUIUJ $.
  $}

  ${
    $d G x $.  $d Y x $.  $d X x $.  $d U u x $.  $d H u x $.
    exidres.1 $e |- X = ran G $.
    exidres.2 $e |- U = ( GId ` G ) $.
    exidres.3 $e |- H = ( G |` ( Y X. Y ) ) $.
    $( Obsolete theorem, use ~ 0gisid instead.  Lemma for ~ exidres and
       ~ exidresid .  (Contributed by Jeff Madsen, 8-Jun-2010.)  (Revised by
       Mario Carneiro, 23-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    exidreslem $p |- ( ( G e. ( Magma i^i ExId ) /\ Y C_ X /\ U e. Y ) ->
                              ( U e. dom dom H /\ A. x e. dom dom H
                            ( ( U H x ) = x /\ ( x H U ) = x ) ) ) $=
      ( wcel wss cdm co wceq wa wral cxp sylib eqtrid dmeqd cmagm cexid cin w3a
      cres dmeqi xpss12 anidms wfo opidon2OLD fof fdm 3syl sseq2d imbitrrid imp
      cv wf ssdmres dmxpid eqtrdi eleq2d biimp3ar ssel2 cmpidelt sylan2 anassrs
      adantrl oveqi ovres eqeq1d ancoms anbi12d adantl mpbird ralrimiva 3adant3
      wb 3impa raleqtrrdv jca ) CUAUBUCJZFEKZBFJZUDZBDLZLZJZBAUQZDMZWINZWIBDMZW
      INZOZAWGPWBWCWHWDWBWCOZWGFBWOWGFFQZLZFWOWFWPWOWFCWPUEZLZWPDWRIUFZWOWPCLZK
      ZWSWPNZWBWCXBWCXBWBWPEEQZKZWCXEFEFEUGUHWBXAXDWPWBXDECUIXDECURXAXDNCEGUJXD
      ECUKXDECULUMUNUOUPZWPCUSZRSTFUTZVAVBVCWEWNAFWGWBWCWDWNAFPWOWDOWNAFWOWDWIF
      JZWNWOWDXIOZOWNBWICMZWINZWIBCMZWINZOZWOXIXOWDWBWCXIXOWCXIOWBWIEJXOFEWIVDW
      IBCEGHVEVFVGVHXJWNXOVRWOXJWKXLWMXNXJWJXKWIXJWJBWIWRMXKDWRBWIIVIBWIFFCVJSV
      KXJWLXMWIXIWDWLXMNXIWDOWLWIBWRMXMDWRWIBIVIWIBFFCVJSVLVKVMVNVOVGVPVSWEWGWQ
      FWEWFWPWEWFWSWPWTWEXBXCWBWCXBWDXFVQXGRSTXHVAVTWA $.

    $( Obsolete theorem, use ~ idressidex instead.  The restriction of a binary
       operation with identity to a subset containing the identity has an
       identity element.  (Contributed by Jeff Madsen, 8-Jun-2010.)  (Revised
       by Mario Carneiro, 23-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    exidres $p |- ( ( G e. ( Magma i^i ExId ) /\ Y C_ X /\ U e. Y )
                                                      -> H e. ExId ) $=
      ( vu vx cexid wcel cv co wceq wa cdm wral syl cvv cin wss wrex exidreslem
      cmagm w3a oveq1 eqeq1d ovanraleqv rspcev wb cxp cres resexg eqeltrid eqid
      isexid 3ad2ant1 mpbird ) BUEKUAZLZEDUBZAELZUFZCKLZIMZJMZCNZVGOZVGVFCNVGOP
      JCQQZRZIVJUCZVDAVJLAVGCNZVGOZVGACNVGOPJVJRZPVLJABCDEFGHUDVKVOIAVJVIVNJVGV
      FVGCVJAVFAOVHVMVGVFAVGCUGUHUIUJSVAVBVEVLUKZVCVACTLVPVACBEEULZUMTHBVQUTUNU
      OIJTCVJVJUPUQSURUS $.

    $( Obsolete theorem, use ~ idressid instead.  The restriction of a binary
       operation with identity to a subset containing the identity has the same
       identity element.  (Contributed by Jeff Madsen, 8-Jun-2010.)  (Revised
       by Mario Carneiro, 23-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    exidresid $p |- ( ( ( G e. ( Magma i^i ExId ) /\ Y C_ X /\ U e. Y ) /\
                                        H e. Magma ) -> ( GId ` H ) = U ) $=
      ( vu vx cmagm cexid wcel wa cv co wceq wral cvv adantr cin wss w3a resexg
      cgi cfv crn crio cxp cres eqeltrid eqid gidval 3ad2ant1 exidreslem simprd
      syl exidres elin rngopidOLD sylbir ancoms sylan raleqtrrdv wreu wb simpld
      cdm eleqtrrd exidu1 oveq1 eqeq1d ovanraleqv riota2 syl2anc mpbid eqtrd )
      BKLUAZMZEDUBZAEMZUCZCKMZNZCUEUFZIOZJOZCPZWGQZWGWFCPWGQNJCUGZRZIWJUHZAWBWE
      WLQZWCVSVTWMWAVSCSMWMVSCBEEUIZUJSHBWNVRUDUKJICSWJWJULZUMUQUNTWDAWGCPZWGQZ
      WGACPWGQNZJWJRZWLAQZWDWRJCVHVHZWJWBWRJXARZWCWBAXAMZXBJABCDEFGHUOZUPTWBCLM
      ZWCWJXAQZABCDEFGHURZWCXEXFWCXENZCVRMZXFCKLUSZCUTVAVBVCZVDWDAWJMWKIWJVEZWS
      WTVFWDAXAWJWBXCWCWBXCXBXDVGTXKVIWBXEWCXLXGWCXEXLXHXIXLXJJICWJWOVJVAVBVCWK
      WSIWJAWIWQJWGWFWGCWJAWFAQWHWPWGWFAWGCVKVLVMVNVOVPVQ $.
  $}

  ${
    abl4pnp.1 $e |- X = ran G $.
    abl4pnp.2 $e |- D = ( /g ` G ) $.
    $( Obsolete theorem, use ~ ablsub4 instead.  A commutative/associative law
       for Abelian groups.  (Contributed by Jeff Madsen, 11-Jun-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ablo4pnp $p |- ( ( G e. AbelOp /\ ( ( A e. X /\ B e. X ) /\
                  ( C e. X /\ F e. X ) ) ) -> ( ( A G B ) D ( C G F ) ) =
                                            ( ( A D C ) G ( B D F ) ) ) $=
      ( cablo wcel wa co wceq w3a 3expib anim1d 3anass imp syldan df-3an oveq1d
      ablomuldiv sylan2br adantrrr cgr wi ablogrpo grpocl imbitrrdi ablodivdiv4
      syl grpodivcl an4 3imtr4g grpomuldivass sylan 3eqtr3d ) FJKZAGKZBGKZLZCGK
      ZEGKZLZLZLZABFMZCDMZEDMZACDMZBFMZEDMZVHCEFMDMZVKBEDMFMZVGVIVLEDUSVBVCVIVL
      NZVDVBVCLUSUTVAVCOVPUTVAVCUAABCDFGHIUCUDUEUBUSVFVHGKZVCVDOZVJVNNUSVFVRUSV
      FVQVELVRUSVBVQVEUSFUFKZVBVQUGFUHZVSUTVAVQABFGHUIPULQVQVCVDRUJSVHCEDFGHIUK
      TUSVSVFVMVONZVTVSVFVKGKZVAVDOZWAVSVFWCVSUTVCLZVAVDLZLWBWELVFWCVSWDWBWEVSU
      TVCWBACDFGHIUMPQUTVAVCVDUNWBVAVDRUOSVKBEDFGHIUPTUQUR $.
  $}

  ${
    grpeqdivid.1 $e |- X = ran G $.
    grpeqdivid.2 $e |- U = ( GId ` G ) $.
    grpeqdivid.3 $e |- D = ( /g ` G ) $.
    $( Obsolete theorem, use ~ grpsubeq0 instead.  Two group elements are equal
       iff their quotient is the identity.  (Contributed by Jeff Madsen,
       6-Jan-2011.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    grpoeqdivid $p |- ( ( G e. GrpOp /\ A e. X /\ B e. X ) ->
                                              ( A = B <-> ( A D B ) = U ) ) $=
      ( cgr wcel w3a wceq grpodivid 3adant2 oveq1 eqeq1d syl5ibrcom grponpcan
      co grpolid eqeq12d imbitrid impbid ) EJKZAFKZBFKZLZABMZABCTZDMZUHUKUIBBCT
      ZDMZUEUGUMUFBCDEFGIHNOUIUJULDABBCPQRUKUJBETZDBETZMUHUIUJDBEPUHUNAUOBABCEF
      GISUEUGUOBMUFBDEFGHUAOUBUCUD $.
  $}

  ${
    $d x y z A $.
    grposnOLD.1 $e |- A e. _V $.
    $( The group operation for the singleton group.  Obsolete, use ~ grp1 .
       instead.  (Contributed by NM, 4-Nov-2006.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    grposnOLD $p |- { <. <. A , A >. , A >. } e. GrpOp $=
      ( vx vy vz cop csn wf cv wcel co velsn oveq2 oveq1 eqtrdi sylan9eq eqtr4d
      wceq wa sylbi snex cxp wf1o opex f1osn f1of ax-mp xpsn feq2i w3a cfv fvsn
      mpbir df-ov eqtri oveq1d sylan9eqr 3impa oveq2d 3impb syl3anb snid id a1i
      isgrpoi ) CDEAAAFZAFGZAAGZAUAVHVHUBZVHVGHVFGZVHVGHZVJVHVGUCVKVFAAAUDZBUEV
      JVHVGUFUGVIVJVHVGAABBUHUIUMCIZVHJZVMARZDIZVHJVPARZEIZVHJVRARZVMVPVGKZVRVG
      KZVMVPVRVGKZVGKZRCALZDALEALVOVQVSUJWAAWCVOVQVSWAARVSVOVQSZWAVTAVGKZAVRAVT
      VGMWEWFAAVGKZAWEVTAAVGVOVQVTAVPVGKZAVMAVPVGNVQWHWGAVPAAVGMWGVFVGUKAAAVGUN
      VFAVLBULUOZOPUPWIOUQURVOVQVSWCARVOVQVSSZWCAWBVGKZAVMAWBVGNWJWKWGAWJWBAAVG
      VQVSWBAVRVGKZAVPAVRVGNVSWLWGAVRAAVGMWIOPUSWIOPUTQVAABVBZVNVOAVMVGKZVMRWDV
      OWNAVMVOWNWGAVMAAVGMWIOZVOVCQTAVHJVNWMVDVNVOWNARWDWOTVE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Group homomorphism and isomorphism
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c GrpOpHom $.

  $( Obsolete version of ~ cghm as of 15-Mar-2020.  Extend class notation to
     include the class of group homomorphisms.  (New usage is discouraged.) $)
  cghomOLD $a class GrpOpHom $.

  ${
    $d f g h x y $.
    $( Obsolete version of ~ df-ghm as of 15-Mar-2020.  Define the set of group
       homomorphisms from ` g ` to ` h ` .  (Contributed by Paul Chapman,
       25-Feb-2008.)  (New usage is discouraged.) $)
    df-ghomOLD $a |- GrpOpHom = ( g e. GrpOp , h e. GrpOp |->
        { f | ( f : ran g --> ran h /\ A. x e. ran g A. y e. ran g
                     ( ( f ` x ) h ( f ` y ) ) = ( f ` ( x g y ) ) ) } ) $.
  $}

  ${
    $d f x y F $.  $d f g h x y G $.  $d f g h x y H $.  $d g h S $.
    elghomlem1OLD.1 $e |- S = { f | ( f : ran G --> ran H /\ A. x e. ran G
      A. y e. ran G ( ( f ` x ) H ( f ` y ) ) = ( f ` ( x G y ) ) ) } $.
    $( Obsolete as of 15-Mar-2020.  Lemma for ~ elghomOLD .  (Contributed by
       Paul Chapman, 25-Feb-2008.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    elghomlem1OLD $p |- ( ( G e. GrpOp /\ H e. GrpOp )
        -> ( G GrpOpHom H ) = S ) $=
      ( vg vh cgr wcel cvv co wceq crn cv cfv wral wf wa cghomOLD fabexg syl2an
      rnexg rneq feq2d oveq fveq2d eqeq2d raleqbidv anbi12d abbidv feq3d eqeq1d
      cab 2ralbidv eqtr4di df-ghomOLD ovmpog mpd3an3 ) EJKZFJKZCLKZEFUAMCNVAEOZ
      LKFOZLKVCVBEJUDFJUDAPZDPZQZBPZVGQZFMZVFVIEMZVGQZNZBVDRAVDRZDVDVELLCGUBUCH
      IEFJJHPZOZIPZOZVGSZVHVJVRMZVFVIVPMZVGQZNZBVQRZAVQRZTZDUOCUAVDVSVGSZWAVMNZ
      BVDRZAVDRZTZDUOZLVPENZWGWLDWNVTWHWFWKWNVQVDVSVGVPEUEZUFWNWEWJAVQVDWOWNWDW
      IBVQVDWOWNWCVMWAWNWBVLVGVFVIVPEUGUHUIUJUJUKULVRFNZWMVDVEVGSZVOTZDUOCWPWLW
      RDWPWHWQWKVOWPVSVEVGVDVRFUEUMWPWIVNABVDVDWPWAVKVMVHVJVRFUGUNUPUKULGUQABDH
      IURUSUT $.

    $( Obsolete as of 15-Mar-2020.  Lemma for ~ elghomOLD .  (Contributed by
       Paul Chapman, 25-Feb-2008.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    elghomlem2OLD $p |- ( ( G e. GrpOp /\ H e. GrpOp )
      -> ( F e. ( G GrpOpHom H )
      <-> ( F : ran G --> ran H /\ A. x e. ran G A. y e. ran G
          ( ( F ` x ) H ( F ` y ) ) = ( F ` ( x G y ) ) ) ) ) $=
      ( cgr wcel wa co crn wf cv cfv wceq wral cvv fveq1 cghomOLD elghomlem1OLD
      eleq2d wb elex oveq12d eqeq12d 2ralbidv anbi12d elab2g biimpd mpcom rnexg
      feq1 wi fex expcom syl adantrd biimprd syli impbid2 adantr bitrd ) FIJZGI
      JZKZEFGUALZJECJZFMZGMZENZAOZEPZBOZEPZGLZVMVOFLZEPZQZBVJRAVJRZKZVGVHCEABCD
      FGHUBUCVEVIWBUDVFVEVIWBESJZVIWBECUEWCVIWBVJVKDOZNZVMWDPZVOWDPZGLZVRWDPZQZ
      BVJRAVJRZKWBDECSWDEQZWEVLWKWAVJVKWDEUNWLWJVTABVJVJWLWHVQWIVSWLWFVNWGVPGVM
      WDETVOWDETUFVRWDETUGUHUIHUJZUKULWBVEWCVIVEVLWCWAVEVJSJZVLWCUOFIUMVLWNWCVJ
      VKSEUPUQURUSWCVIWBWMUTVAVBVCVD $.
  $}

  ${
    $d F f x y $.  $d G f x y $.  $d H f x y $.  $d X x y $.
    elghomOLD.1 $e |- X = ran G $.
    elghomOLD.2 $e |- W = ran H $.
    $( Obsolete version of ~ isghm as of 15-Mar-2020.  Membership in the set of
       group homomorphisms from ` G ` to ` H ` .  (Contributed by Paul Chapman,
       3-Mar-2008.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    elghomOLD $p |- ( ( G e. GrpOp /\ H e. GrpOp ) ->
      ( F e. ( G GrpOpHom H ) <-> ( F : X --> W /\ A. x e. X A. y e. X
        ( ( F ` x ) H ( F ` y ) ) = ( F ` ( x G y ) ) ) ) ) $=
      ( vf cgr wcel wa co crn wf cv cfv wceq wral cghomOLD elghomlem2OLD feq23i
      cab eqid raleqi raleqbii anbi12i bitr4di ) DKLEKLMCDEUANLDOZEOZCPZAQZCRBQ
      ZCRENUMUNDNZCRSZBUJTZAUJTZMGFCPZUPBGTZAGTZMABUJUKJQZPUMVBRUNVBRENUOVBRSBU
      JTAUJTMJUDZJCDEVCUEUBUSULVAURGFUJUKCHIUCUTUQAGUJHUPBGUJHUFUGUHUI $.
  $}

  ${
    $d A x y $.  $d B y $.  $d F x y $.  $d G x y $.  $d H x y $.  $d X x y $.
    ghomlinOLD.1 $e |- X = ran G $.
    $( Obsolete version of ~ ghmlin as of 15-Mar-2020.  Linearity of a group
       homomorphism.  (Contributed by Paul Chapman, 3-Mar-2008.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ghomlinOLD $p |- ( ( ( G e. GrpOp /\ H e. GrpOp
        /\ F e. ( G GrpOpHom H ) ) /\ ( A e. X /\ B e. X ) ) ->
                    ( ( F ` A ) H ( F ` B ) ) = ( F ` ( A G B ) ) ) $=
      ( vx vy cgr wcel co cv cfv wceq wral wa fveq2 fveq2d eqeq12d cghomOLD w3a
      crn eqid elghomOLD biimp3a simprd oveq1d oveq1 oveq2d oveq2 rspc2v mpan9
      wf ) DJKZEJKZCDEUALKZUBZHMZCNZIMZCNZELZUSVADLZCNZOZIFPHFPZAFKBFKQACNZBCNZ
      ELZABDLZCNZOZURFEUCZCUNZVGUOUPUQVOVGQHICDEVNFGVNUDUEUFUGVFVMVHVBELZAVADLZ
      CNZOHIABFFUSAOZVCVPVEVRVSUTVHVBEUSACRUHVSVDVQCUSAVADUISTVABOZVPVJVRVLVTVB
      VIVHEVABCRUJVTVQVKCVABADUKSTULUM $.
  $}

  ${
    $d F x y $.  $d G x y $.  $d H x y $.
    ghomidOLD.1 $e |- U = ( GId ` G ) $.
    ghomidOLD.2 $e |- T = ( GId ` H ) $.
    $( Obsolete version of ~ ghmid as of 15-Mar-2020.  A group homomorphism
       maps identity element to identity element.  (Contributed by Paul
       Chapman, 3-Mar-2008.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ghomidOLD $p |- ( ( G e. GrpOp /\ H e. GrpOp /\ F e. ( G GrpOpHom H ) ) ->
                   ( F ` U ) = T ) $=
      ( vx vy cgr wcel co cfv wceq crn wa eqid 3ad2ant1 mpdan cv w3a ghomlinOLD
      cghomOLD grpoidcl jca grpolid fveq2d eqtrd wb wf elghomOLD biimp3a simpld
      wral ffvelcdmd wi grpoid ex 3ad2ant2 mpd mpbird ) DJKZEJKZCDEUCLKZUAZBCMZ
      ANZVFVFELZVFNZVEVHBBDLZCMZVFVEBDOZKZVMPVHVKNVEVMVMVBVCVMVDBDVLVLQZFUDZRZV
      PUEBBCDEVLVNUBSVBVCVKVFNVDVBVJBCVBVMVJBNVOBBDVLVNFUFSUGRUHVEVFEOZKZVGVIUI
      ZVEVLVQBCVEVLVQCUJZHTZCMITZCMELWAWBDLCMNIVLUNHVLUNZVBVCVDVTWCPHICDEVQVLVN
      VQQZUKULUMVPUOVCVBVRVSUPVDVCVRVSVFAEVQWDGUQURUSUTVA $.
  $}

  ${
    $d F x y $.  $d G x y $.  $d H x y $.  $d X x y $.
    ghomf.1 $e |- X = ran G $.
    ghomf.2 $e |- W = ran H $.
    $( Obsolete theorem, use ~ ghmf instead.  Mapping property of a group
       homomorphism.  (Contributed by Jeff Madsen, 1-Dec-2009.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ghomf $p |- ( ( G e. GrpOp /\ H e. GrpOp /\ F e. ( G GrpOpHom H ) )
                                                  -> F : X --> W ) $=
      ( vx vy cgr wcel cghomOLD co wf wa cv cfv wceq wral elghomOLD simprbda
      3impa ) BJKZCJKZABCLMKZEDANZUCUDOUEUFHPZAQIPZAQCMUGUHBMAQRIESHESHIABCDEFG
      TUAUB $.
  $}

  ${
    $d S u v x y $.  $d T u v x y $.  $d G u v x y $.  $d H u v x y $.
    $d K u v x y $.
    $( Obsolete theorem, use ~ ghmco instead.  The composition of two group
       homomorphisms is a group homomorphism.  (Contributed by Jeff Madsen,
       1-Dec-2009.)  (Revised by Mario Carneiro, 27-Dec-2014.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ghomco $p |- ( ( ( G e. GrpOp /\ H e. GrpOp /\ K e. GrpOp ) /\
                    ( S e. ( G GrpOpHom H ) /\ T e. ( H GrpOpHom K ) ) ) ->
                                      ( T o. S ) e. ( G GrpOpHom K ) ) $=
      ( vx vy vu vv cgr wcel cghomOLD co wa cv cfv wceq wral wi ad2ant2r w3a wf
      crn fco ancoms a1i ffvelcdm anim12dan fveq2 oveq1d fvoveq1 eqeq12d oveq2d
      oveq2 fveq2d rspc2va sylan an32s adantllr sylan9eq anasss fvco3 ad2ant2rl
      ccom oveq12d adantlr eqid grpocl sylan2 anassrs 3eqtr4d expr ralimdvva ex
      3expb com23 com12 3ad2ant1 jcad elghomOLD 3adant3 3adant1 anbi12d 3adant2
      imp wb 3imtr4d ) CJKZDJKZEJKZUAZACDLMKZBDELMKZNZBAVDZCELMKZWKCUCZDUCZAUBZ
      FOZAPZGOZAPZDMZWTXBCMZAPZQZGWQRFWQRZNZWREUCZBUBZHOZBPZIOZBPZEMZXLXNDMBPZQ
      ZIWRRHWRRZNZNZWQXJWOUBZWTWOPZXBWOPZEMZXEWOPZQZGWQRFWQRZNZWNWPWKYAYBYHYAYB
      SWKWSXKYBXHXSXKWSYBWQWRXJBAUDUETUFWHWIYAYHSWJYAWHYHWSXTXHWHYHSZWSXTNXHYJW
      SXKXSXHYJSWSXKNZXSNZWHXHYHYLWHXHYHSZYKWHXSYMYKWHNZXSNZXGYGFGWQWQYOWTWQKZX
      BWQKZNZXGYGYOYRXGNNXABPZXCBPZEMZXFBPZYEYFYOYRXGUUAUUBQYOYRNXGUUAXDBPZUUBY
      KXSYRUUAUUCQZWHWSXSYRUUDXKWSYRXSUUDWSYRNXAWRKZXCWRKZNXSUUDWSYPUUEYQUUFWQW
      RWTAUGWQWRXBAUGUHXRUUDYSXOEMZXAXNDMZBPZQHIXAXCWRWRXLXAQZXPUUGXQUUIUUJXMYS
      XOEXLXABUIUJXLXAXNBDUKULXNXCQZUUGUUAUUIUUCUUKXOYTYSEXNXCBUIUMUUKUUHXDBXNX
      CXADUNUOULUPUQURUSUSXDXFBUIUTVAYNYRYEUUAQZXSXGYKYRUULWHYKYRNYCYSYDYTEWSYP
      YCYSQXKYQWQWRWTBAVBTWSYQYDYTQXKYPWQWRXBBAVBVCVEVFTYNYRYFUUBQZXSXGYKWHYRUU
      MWHYRNYKXEWQKZUUMWHYPYQUUNWTXBCWQWQVGZVHVOWSUUNUUMXKWQWRXEBAVBVFVIVJTVKVL
      VMURVNVPVAWEURVQVRVSWKWLXIWMXTWHWIWLXIWFWJFGACDWRWQUUOWRVGZVTWAWIWJWMXTWF
      WHHIBDEXJWRUUPXJVGZVTWBWCWHWJWPYIWFWIFGWOCEXJWQUUOUUQVTWDWGWE $.
  $}

  ${
    ghomdiv.1 $e |- X = ran G $.
    ghomdiv.2 $e |- D = ( /g ` G ) $.
    ghomdiv.3 $e |- C = ( /g ` H ) $.
    $( Obsolete theorem, use ~ ghmsub instead.  Group homomorphisms preserve
       division.  (Contributed by Jeff Madsen, 16-Jun-2011.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    ghomdiv $p |- ( ( ( G e. GrpOp /\ H e. GrpOp /\ F e. ( G GrpOpHom H ) ) /\
                                ( A e. X /\ B e. X ) ) ->
                      ( F ` ( A D B ) ) = ( ( F ` A ) C ( F ` B ) ) ) $=
      ( cgr wcel co wa cfv wceq ffvelcdmda grponpcan 3ad2antl1 cghomOLD w3a crn
      simpl2 eqid ghomf adantrr adantrl syl3anc fveq2d grpodivcl jca ghomlinOLD
      3expb simprr eqcomd syldan 3eqtr2rd wb grporcan syl13anc mpbid ) FLMZGLMZ
      EFGUANMZUBZAHMZBHMZOZOZABDNZEPZBEPZGNZAEPZVMCNZVMGNZQZVLVPQZVJVQVOVKBFNZE
      PZVNVJVDVOGUCZMZVMWBMZVQVOQVCVDVEVIUDZVFVGWCVHVFHWBAEEFGWBHIWBUEZUFZRUGZV
      FVHWDVGVFHWBBEWGRUHZVOVMCGWBWFKSUIVJVTAEVCVDVIVTAQZVEVCVGVHWJABDFHIJSUNTU
      JVFVIVKHMZVHOZWAVNQVCVDVIWLVEVCVIOWKVHVCVGVHWKABDFHIJUKUNZVCVGVHUOULTVFWL
      OVNWAVKBEFGHIUMUPUQURVJVDVLWBMZVPWBMZWDVRVSUSWEVFVIWKWNVCVDVIWKVEWMTVFHWB
      VKEWGRUQVJVDWCWDWOWEWHWIVOVMCGWBWFKUKUIWIVLVPVMGWBWFUTVAVB $.
  $}

  ${
    $d G x y $.  $d H x y $.  $d F x y $.  $d U x y $.  $d W x y $.
    $d X x y $.
    grpkerinj.1 $e |- X = ran G $.
    grpkerinj.2 $e |- W = ( GId ` G ) $.
    grpkerinj.3 $e |- Y = ran H $.
    grpkerinj.4 $e |- U = ( GId ` H ) $.
    $( Obsolete theorem, use ~ kerf1ghm instead.  A group homomorphism is
       injective if and only if its kernel is zero.  (Contributed by Jeff
       Madsen, 16-Jun-2011.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    grpokerinj $p |- ( ( G e. GrpOp /\ H e. GrpOp /\ F e. ( G GrpOpHom H ) ) ->
                      ( F : X -1-1-> Y <-> ( `' F " { U } ) = { W } ) ) $=
      ( vx vy wcel co csn cima wceq wa cfv cgr cghomOLD w3a wf1 ghomidOLD sneqd
      ccnv wfn ghomf grpoidcl 3ad2ant1 fnsnfv syl2anc eqtr3d imaeq2d adantl wss
      ffnd snssd f1imacnv sylan2 eqtrd expcom wf cv wi adantr cgs wb ffvelcdmda
      wral simpl2 adantrr adantrl eqid grpoeqdivid syl3anc adantlr eqeq1d fvexi
      ghomdiv cgi snid eleq1 mpbiri wfun cdm ffund grpodivcl 3ad2antl1 eleqtrrd
      3expb fdmd fvimacnv eleq2 sylan9bb an32s elsni biimprd sylbird ralrimivva
      syl5 sylbid dff13 sylanbrc ex impbid ) CUANZDUANZBCDUBONZUCZFGBUDZBUGZAPZ
      QZEPZRZXLXKXQXLXKSXOXMBXPQZQZXPXKXOXSRXLXKXNXRXMXKEBTZPZXNXRXKXTAAEBCDIKU
      EUFXKBFUHEFNZYAXRRXKFGBBCDGFHJUIZURXHXIYBXJECFHIUJZUKFEBULUMUNUOUPXKXLXPF
      UQZXSXPRXHXIYEXJXHEFYDUSUKFGXPBUTVAVBVCXKXQXLXKXQSZFGBVDZLVEZBTZMVEZBTZRZ
      YHYJRZVFZMFVKLFVKXLXKYGXQYCVGYFYNLMFFYFYHFNZYJFNZSZSZYLYIYKDVHTZOZARZYMXK
      YQYLUUAVIZXQXKYQSZXIYIGNZYKGNZUUBXHXIXJYQVLXKYOUUDYPXKFGYHBYCVJVMXKYPUUEY
      OXKFGYJBYCVJVNYIYKYSADGJKYSVOZVPVQVRYRUUAYHYJCVHTZOZBTZARZYMYRUUIYTAXKYQU
      UIYTRXQYHYJYSUUGBCDFHUUGVOZUUFWAVRVSUUJUUIXNNZYRYMUUJUULAXNNAADWBKVTWCUUI
      AXNWDWEYRUULUUHXPNZYMXKYQXQUULUUMVIUUCUULUUHXONZXQUUMUUCBWFZUUHBWGZNUULUU
      NVIXKUUOYQXKFGBYCWHVGUUCUUHFUUPXHXIYQUUHFNZXJXHYOYPUUQYHYJUUGCFHUUKWIWLWJ
      XKUUPFRYQXKFGBYCWMVGWKUUHXNBWNUMXOXPUUHWOWPWQXKYQUUMYMVFXQUUMUUHERZUUCYMU
      UHEWRXHXIYQUURYMVFZXJXHYOYPUUSXHYOYPUCYMUURYHYJUUGECFHIUUKVPWSWLWJXBVRXCX
      BWTXCXALMFGBXDXEXFXG $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Rings
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c RingOps $.

  $( Extend class notation with the class of all unital rings. $)
  crngo $a class RingOps $.

  ${
    $d g h x y z $.
    $( Obsolete defintion, use ~ dfring3 instead.  Define the class of all
       unital rings.  (Contributed by Jeff Hankins, 21-Nov-2006.)
       (New usage is discouraged.) $)
    df-rngo $a |- RingOps = { <. g , h >. | ( ( g e. AbelOp /\
                               h : ( ran g X. ran g ) --> ran g ) /\
            ( A. x e. ran g A. y e. ran g A. z e. ran g
              ( ( ( x h y ) h z ) = ( x h ( y h z ) ) /\
                ( x h ( y g z ) ) = ( ( x h y ) g ( x h z ) ) /\
                ( ( x g y ) h z ) = ( ( x h z ) g ( y h z ) ) ) /\
        E. x e. ran g A. y e. ran g ( ( x h y ) = y /\ ( y h x ) = y ) ) ) } $.
  $}

  ${
    $d g h x y z $.
    $( Obsolete theorem.  The class of all unital rings is a relation.
       (Contributed by FL, 31-Aug-2009.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    relrngo $p |- Rel RingOps $=
      ( vg vh vx vy vz cv cablo wcel crn cxp wf wa wceq wral wrex crngo df-rngo
      co w3a relopabiv ) AFZGHUAIZUBJUBBFZKLCFZDFZUCRZEFZUCRUDUEUGUCRZUCRMUDUEU
      GUARUCRUFUDUGUCRZUARMUDUEUARUGUCRUIUHUARMSEUBNDUBNCUBNUFUEMUEUDUCRUEMLDUB
      NCUBOLLABPCDEABQT $.
  $}

  ${
    $d g h x y z G $.  $d g h x y z H $.  $d g h x y z X $.
    isring.1 $e |- X = ran G $.
    $( Obsolete theorem, use ~ dfring2 instead.  The predicate "is a (unital)
       ring."  Definition of "ring with unit" in [Schechter] p. 187.
       (Contributed by Jeff Hankins, 21-Nov-2006.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    isrngo $p |- ( H e. A -> ( <. G , H >. e. RingOps <->
      ( ( G e. AbelOp /\ H : ( X X. X ) --> X ) /\
        ( A. x e. X A. y e. X A. z e. X
          ( ( ( x H y ) H z ) = ( x H ( y H z ) ) /\
            ( x H ( y G z ) ) = ( ( x H y ) G ( x H z ) ) /\
            ( ( x G y ) H z ) = ( ( x H z ) G ( y H z ) ) ) /\
          E. x e. X A. y e. X ( ( x H y ) = y /\ ( y H x ) = y ) ) ) ) ) $=
      ( vg vh wcel crngo cablo wa cv co wceq wral oveqd oveq123d cvv cop cxp wf
      w3a wrex wi wbr df-br relrngo brrelex1i sylbir a1i elex ad2antrr wb copab
      crn df-rngo eleq2i simpl eleq1d simpr rneqd eqtr4di sqxpeqd feq123d eqidd
      anbi12d eqeq12d 3anbi123d raleqbidv eqeq1d rexeqbidv opelopabga pm5.21ndd
      bitrid expcom ) FDKZEUAKZEFUBZLKZEMKZGGUCZGFUDZNZAOZBOZFPZCOZFPZWGWHWJFPZ
      FPZQZWGWHWJEPZFPZWIWGWJFPZEPZQZWGWHEPZWJFPZWQWLEPZQZUEZCGRZBGRZAGRZWIWHQZ
      WHWGFPZWHQZNZBGRZAGUFZNZNZWBVTUGVSWBEFLUHVTEFLUIEFLUJUKULUMXOVTUGVSWCVTWE
      XNEMUNUOUMVTVSWBXOUPWBWAIOZMKZXPURZXRUCZXRJOZUDZNZWGWHXTPZWJXTPZWGWHWJXTP
      ZXTPZQZWGWHWJXPPZXTPZYCWGWJXTPZXPPZQZWGWHXPPZWJXTPZYJYEXPPZQZUEZCXRRZBXRR
      ZAXRRZYCWHQZWHWGXTPZWHQZNZBXRRZAXRUFZNZNZIJUQZKVTVSNXOLUUIWAABCIJUSUTUUHX
      OIJEFUADXPEQZXTFQZNZYBWFUUGXNUULXQWCYAWEUULXPEMUUJUUKVAZVBUULXSWDXRGXTFUU
      JUUKVCZUULXRGUULXREURGUULXPEUUMVDHVEZVFUUOVGVIUULYTXGUUFXMUULYSXFAXRGUUOU
      ULYRXEBXRGUUOUULYQXDCXRGUUOUULYGWNYLWSYPXCUULYDWKYFWMUULYCWIWJWJXTFUUNUUL
      XTFWGWHUUNSZUULWJVHZTUULWGWGYEWLXTFUUNUULWGVHZUULXTFWHWJUUNSZTVJUULYIWPYK
      WRUULWGWGYHWOXTFUUNUURUULXPEWHWJUUMSTUULYCWIYJWQXPEUUMUUPUULXTFWGWJUUNSZT
      VJUULYNXAYOXBUULYMWTWJWJXTFUUNUULXPEWGWHUUMSUUQTUULYJWQYEWLXPEUUMUUTUUSTV
      JVKVLVLVLUULUUEXLAXRGUUOUULUUDXKBXRGUUOUULUUAXHUUCXJUULYCWIWHUUPVMUULUUBX
      IWHUULXTFWHWGUUNSVMVIVLVNVIVIVOVQVRVP $.
  $}

  ${
    $d ph x y z $.  $d G x y z $.  $d H x y z $.  $d X x y z $.  $d U x y $.
    isringod.1 $e |- ( ph -> G e. AbelOp ) $.
    isringod.2 $e |- ( ph -> X = ran G ) $.
    isringod.3 $e |- ( ph -> H : ( X X. X ) --> X ) $.
    isringod.4 $e |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) )
                                  -> ( ( x H y ) H z ) = ( x H ( y H z ) ) ) $.
    isringod.5 $e |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) )
                          -> ( x H ( y G z ) ) = ( ( x H y ) G ( x H z ) ) ) $.
    isringod.6 $e |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) )
                          -> ( ( x G y ) H z ) = ( ( x H z ) G ( y H z ) ) ) $.
    isringod.7 $e |- ( ph -> U e. X ) $.
    isringod.8 $e |- ( ( ph /\ y e. X ) -> ( U H y ) = y ) $.
    isringod.9 $e |- ( ( ph /\ y e. X ) -> ( y H U ) = y ) $.
    $( Obsolete theorem, use ~ isringd instead.  Conditions that determine a
       ring.  (Changed label from ~ isringd to ~ isrngod -NM 2-Aug-2013.)
       (Contributed by Jeff Madsen, 19-Jun-2010.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    isrngod $p |- ( ph -> <. G , H >. e. RingOps ) $=
      ( wcel co wral cop crngo cablo crn cxp wf wa wceq w3a wrex sqxpeqd feq23d
      cv mpbid 3jca ralrimivvva raleqbidv jca ralrimiva oveq1 eqeq1d ovanraleqv
      raleqdv rspcev syl2anc rexeqbidv jca31 cvv wb rnexg syl xpexd fexd isrngo
      eqid mpbird ) AFGUAUBRZFUCRZFUDZVSUEZVSGUFZUGBUMZCUMZGSZDUMZGSWBWCWEGSZGS
      UHZWBWCWEFSGSWDWBWEGSZFSUHZWBWCFSWEGSWHWFFSUHZUIZDVSTZCVSTZBVSTZWDWCUHZWC
      WBGSWCUHUGZCVSTZBVSUJZUGZUGZAVRWAWSIAHHUEZHGUFWAKAXAHVTVSGAHVSJUKJULUNZAW
      NWRAWKDHTZCHTZBHTWNAWKBCDHHHAWBHRWCHRZWEHRUIUGWGWIWJLMNUOUPAXDWMBHVSJAXCW
      LCHVSJAWKDHVSJVCUQUQUNAWPCHTZBHUJZWRAEHREWCGSZWCUHZWCEGSWCUHZUGZCHTZXGOAX
      KCHAXEUGXIXJPQURUSXFXLBEHWOXICWCWBWCGHEWBEUHWDXHWCWBEWCGUTVAVBVDVEAXFWQBH
      VSJAWPCHVSJVCVFUNURVGAGVHRVQWTVIAVTVSVHGXBAVSVSVHVHAVRVSVHRIFUCVJVKZXMVLV
      MBCDVHFGVSVSVOVNVKVP $.
  $}

  ${
    $d u x y z G $.  $d u x y z H $.  $d u x y z X $.  $d u x y z A $.
    $d y z B $.  $d z C $.  $d u x R $.
    ringi.1 $e |- G = ( 1st ` R ) $.
    ringi.2 $e |- H = ( 2nd ` R ) $.
    ringi.3 $e |- X = ran G $.
    $( Obsolete theorem, use ~ dfring3 instead.  The properties of a unital
       ring.  (Contributed by Steve Rodriguez, 8-Sep-2007.)  (Proof shortened
       by Mario Carneiro, 21-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngoi $p |- ( R e. RingOps -> ( ( G e. AbelOp /\ H : ( X X. X ) --> X ) /\
      ( A. x e. X A. y e. X A. z e. X
        ( ( ( x H y ) H z ) = ( x H ( y H z ) ) /\
          ( x H ( y G z ) ) = ( ( x H y ) G ( x H z ) ) /\
          ( ( x G y ) H z ) = ( ( x H z ) G ( y H z ) ) ) /\
        E. x e. X A. y e. X ( ( x H y ) = y /\ ( y H x ) = y ) ) ) ) $=
      ( crngo wcel cop wa cv co wceq wral cfv c2nd cxp wf w3a wrex c1st opeq12i
      cablo wrel relrngo 1st2nd eqtr4id id eqeltrd cvv fvexi isrngo ax-mp sylib
      mpan wb ) DKLZEFMZKLZEUGLGGUAGFUBNAOZBOZFPZCOZFPVDVEVGFPZFPQVDVEVGEPFPVFV
      DVGFPZEPQVDVEEPVGFPVIVHEPQUCCGRBGRAGRVFVEQVEVDFPVEQNBGRAGUDNNZVAVBDKVAVBD
      UESZDTSZMZDEVKFVLHIUFKUHVADVMQUIDKUJUSUKVAULUMFUNLVCVJUTFDTIUOABCUNEFGJUP
      UQUR $.

    $( Obsolete theorem.  Functionality of the multiplication operation of a
       ring.  (Contributed by Steve Rodriguez, 9-Sep-2007.)  (Revised by Mario
       Carneiro, 21-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngosm $p |- ( R e. RingOps -> H : ( X X. X ) --> X ) $=
      ( vx vy vz crngo wcel cablo cxp wf wa cv co wceq wral rngoi simpld simprd
      w3a wrex ) AKLZBMLZDDNDCOZUFUGUHPHQZIQZCRZJQZCRUIUJULCRZCRSUIUJULBRCRUKUI
      ULCRZBRSUIUJBRULCRUNUMBRSUDJDTIDTHDTUKUJSUJUICRUJSPIDTHDUEPHIJABCDEFGUAUB
      UC $.

    $( Obsolete theorem, use ~ ringcl instead.  Closure of the multiplication
       operation of a ring.  (Contributed by Steve Rodriguez, 9-Sep-2007.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngocl $p |- ( ( R e. RingOps /\ A e. X /\ B e. X ) -> ( A H B ) e. X ) $=
      ( crngo wcel cxp wf co rngosm fovcdm syl3an1 ) CJKFFLFEMAFKBFKABENFKCDEFG
      HIOABFFFEPQ $.

    $( Obsolete theorem, use ~ ringid instead.  The multiplication operation of
       a unital ring has (one or more) identity elements.  (Contributed by
       Steve Rodriguez, 9-Sep-2007.)  (Revised by Mario Carneiro, 22-Dec-2013.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngoid $p |- ( ( R e. RingOps /\ A e. X ) ->
                 E. u e. X ( ( u H A ) = A /\ ( A H u ) = A ) ) $=
      ( vx vy crngo wcel cv co wceq wa wrex wral eqeq12d cablo cxp wf w3a rngoi
      simprrd r19.12 syl oveq2 id oveq1 anbi12d rexbidv rspccva sylan ) CLMZANZ
      JNZEOZURPZURUQEOZURPZQZAFRZJFSZBFMUQBEOZBPZBUQEOZBPZQZAFRZUPVCJFSAFRZVEUP
      DUAMFFUBFEUCQUSKNZEOUQURVMEOZEOPUQURVMDOEOUSUQVMEOZDOPUQURDOVMEOVOVNDOPUD
      KFSJFSAFSVLAJKCDEFGHIUEUFVCAJFFUGUHVDVKJBFURBPZVCVJAFVPUTVGVBVIVPUSVFURBU
      RBUQEUIVPUJZTVPVAVHURBURBUQEUKVQTULUMUNUO $.

    $( Obsolete theorem, use ~ ringideu instead.  The unity element of a ring
       is unique.  (Contributed by NM, 4-Apr-2009.)  (Revised by Mario
       Carneiro, 21-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngoideu $p |- ( R e. RingOps ->
                 E! u e. X A. x e. X ( ( u H x ) = x /\ ( x H u ) = x ) ) $=
      ( vy wcel cv co wceq wa wral weq ralimi id eqeq12d crngo wrex wi wreu cxp
      cablo wf rngoi simprrd simpl oveq2 rspcv syl5 simpr oveq1 im2anan9r eqtr2
      w3a equcomd syl6 rgen2 eqeq1d ovanraleqv reu4 sylanblrc ) CUAKZBLZALZEMZV
      HNZVHVGEMVHNZOZAFPZBFUBZVMJLZVHEMZVHNZVHVOEMZVHNZOZAFPZOZBJQZUCZJFPBFPVMB
      FUDVFDUFKFFUEFEUGOVIVOEMVGVREMNVGVHVODMEMVIVGVOEMZDMNVGVHDMVOEMWEVRDMNURJ
      FPAFPBFPVNBAJCDEFGHIUHUIWDBJFFVGFKZVOFKZOWBWEVONZWEVGNZOZWCWGVMWHWFWAWIVM
      VJAFPWGWHVLVJAFVJVKUJRVJWHAVOFAJQZVIWEVHVOVHVOVGEUKWKSTULUMWAVSAFPWFWIVTV
      SAFVQVSUNRVSWIAVGFABQZVRWEVHVGVHVGVOEUOWLSTULUMUPWJJBWEVOVGUQUSUTVAVMWABJ
      FVJVQAVHVGVHEFVOWCVIVPVHVGVOVHEUOVBVCVDVE $.

    $( Obsolete theorem, use ~ ringdi instead.  Distributive law for the
       multiplication operation of a ring (left-distributivity).  (Contributed
       by Steve Rodriguez, 9-Sep-2007.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngodi $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                     ( A H ( B G C ) ) = ( ( A H B ) G ( A H C ) ) ) $=
      ( vx vy vz wcel cv co wceq wral wa oveq1 crngo w3a cablo cxp rngoi simprd
      wf simpld simp2 ralimi 2ralimi oveq12d eqeq12d oveq2d oveq2 oveq1d rspc3v
      wrex syl5 mpan9 ) DUANZKOZLOZFPZMOZFPVBVCVEFPZFPQZVBVCVEEPZFPZVDVBVEFPZEP
      ZQZVBVCEPVEFPVJVFEPQZUBZMGRZLGRKGRZAGNBGNCGNUBZABCEPZFPZABFPZACFPZEPZQZVA
      VPVDVCQVCVBFPVCQSLGRKGURZVAEUCNGGUDGFUGSVPWDSKLMDEFGHIJUEUFUHVPVLMGRZLGRK
      GRVQWCVOWEKLGGVNVLMGVGVLVMUIUJUKVLWCAVHFPZAVCFPZAVEFPZEPZQABVEEPZFPZVTWHE
      PZQKLMABCGGGVBAQZVIWFVKWIVBAVHFTWMVDWGVJWHEVBAVCFTVBAVEFTULUMVCBQZWFWKWIW
      LWNVHWJAFVCBVEETUNWNWGVTWHEVCBAFUOUPUMVECQZWKVSWLWBWOWJVRAFVECBEUOUNWOWHW
      AVTEVECAFUOUNUMUQUSUT $.

    $( Obsolete theorem, use ~ ringdir instead.  Distributive law for the
       multiplication operation of a ring (right-distributivity).  (Contributed
       by Steve Rodriguez, 9-Sep-2007.)  (Revised by Mario Carneiro,
       21-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngodir $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                      ( ( A G B ) H C ) = ( ( A H C ) G ( B H C ) ) ) $=
      ( vx vy vz wcel cv co wceq wral wa oveq2 crngo w3a cablo cxp rngoi simprd
      wf simpld simp3 ralimi 2ralimi oveq1 oveq1d eqeq12d oveq2d oveq12d rspc3v
      wrex syl5 mpan9 ) DUANZKOZLOZFPZMOZFPVBVCVEFPZFPQZVBVCVEEPFPVDVBVEFPZEPQZ
      VBVCEPZVEFPZVHVFEPZQZUBZMGRZLGRKGRZAGNBGNCGNUBZABEPZCFPZACFPZBCFPZEPZQZVA
      VPVDVCQVCVBFPVCQSLGRKGURZVAEUCNGGUDGFUGSVPWDSKLMDEFGHIJUEUFUHVPVMMGRZLGRK
      GRVQWCVOWEKLGGVNVMMGVGVIVMUIUJUKVMWCAVCEPZVEFPZAVEFPZVFEPZQVRVEFPZWHBVEFP
      ZEPZQKLMABCGGGVBAQZVKWGVLWIWMVJWFVEFVBAVCEULUMWMVHWHVFEVBAVEFULUMUNVCBQZW
      GWJWIWLWNWFVRVEFVCBAETUMWNVFWKWHEVCBVEFULUOUNVECQZWJVSWLWBVECVRFTWOWHVTWK
      WAEVECAFTVECBFTUPUNUQUSUT $.

    $( Obsolete theorem, use ~ ringass instead.  Associative law for the
       multiplication operation of a ring.  (Contributed by Steve Rodriguez,
       9-Sep-2007.)  (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngoass $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                      ( ( A H B ) H C ) = ( A H ( B H C ) ) ) $=
      ( vx vy vz wcel cv co wceq wral wa oveq1 crngo w3a cablo cxp rngoi simprd
      wrex wf simpld simp1 ralimi 2ralimi syl oveq1d eqeq12d oveq2 oveq2d mpan9
      rspc3v ) DUANZKOZLOZFPZMOZFPZVAVBVDFPZFPZQZMGRZLGRKGRZAGNBGNCGNUBABFPZCFP
      ZABCFPZFPZQZUTVHVAVBVDEPFPVCVAVDFPZEPQZVAVBEPVDFPVPVFEPQZUBZMGRZLGRKGRZVJ
      UTWAVCVBQVBVAFPVBQSLGRKGUGZUTEUCNGGUDGFUHSWAWBSKLMDEFGHIJUEUFUIVTVIKLGGVS
      VHMGVHVQVRUJUKULUMVHVOAVBFPZVDFPZAVFFPZQVKVDFPZABVDFPZFPZQKLMABCGGGVAAQZV
      EWDVGWEWIVCWCVDFVAAVBFTUNVAAVFFTUOVBBQZWDWFWEWHWJWCVKVDFVBBAFUPUNWJVFWGAF
      VBBVDFTUQUOVDCQZWFVLWHVNVDCVKFUPWKWGVMAFVDCBFUPUQUOUSUR $.

    $( Obsolete theorem, use ~ ringadd2 instead.  A ring element plus itself is
       two times the element.  (Contributed by Steve Rodriguez, 9-Sep-2007.)
       (Revised by Mario Carneiro, 22-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngo2 $p |- ( ( R e. RingOps /\ A e. X ) ->
                  E. x e. X ( A G A ) = ( ( x G x ) H A ) ) $=
      ( crngo wcel wa cv co wceq wrex rngoid oveq12 anidms eqcomd simpll simplr
      simpr rngodir syl13anc eqeq2d imbitrrid adantrd reximdva mpd ) CJKZBFKZLZ
      AMZBENZBOZBUNENBOZLZAFPBBDNZUNUNDNBENZOZAFPABCDEFGHIQUMURVAAFUMUNFKZLZUPV
      AUQUPVAVCUSUOUODNZOUPVDUSUPVDUSOUOBUOBDRSTVCUTVDUSVCUKVBVBULUTVDOUKULVBUA
      UMVBUCZVEUKULVBUBUNUNBCDEFGHIUDUEUFUGUHUIUJ $.
  $}

  ${
    $d G x y z $.  $d R x y z $.
    ringabl.1 $e |- G = ( 1st ` R ) $.
    $( Obsolete theorem, use ~ ringabl instead.  A ring's addition operation is
       an Abelian group operation.  (Contributed by Steve Rodriguez,
       9-Sep-2007.)  (Revised by Mario Carneiro, 21-Dec-2013.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngoablo $p |- ( R e. RingOps -> G e. AbelOp ) $=
      ( vx vy vz crngo wcel cablo crn cxp c2nd cfv wf cv co wceq wral wa eqid
      w3a wrex rngoi simplld ) AGHBIHBJZUEKUEALMZNDOZEOZUFPZFOZUFPUGUHUJUFPZUFP
      QUGUHUJBPUFPUIUGUJUFPZBPQUGUHBPUJUFPULUKBPQUAFUEREUERDUERUIUHQUHUGUFPUHQS
      EUERDUEUBSDEFABUFUECUFTUETUCUD $.
  $}

  $( Obsolete theorem, use ~ ringabl instead.  In a unital ring the addition is
     an abelian group.  (Contributed by FL, 31-Aug-2009.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  rngoablo2 $p |- ( <. G , H >. e. RingOps -> G e. AbelOp ) $=
    ( cop crngo wcel c1st cfv cablo wbr wceq df-br wa relrngo brrelex12i op1stg
    cvv syl sylbir eqid rngoablo eqeltrrd ) ABCZDEZUBFGZAHUCABDIZUDAJZABDKUEAPE
    BPELUFABDMNABPPOQRUBUDUDSTUA $.

  ${
    ringgrp.1 $e |- G = ( 1st ` R ) $.
    $( Obsolete theorem, use ~ ringgrp instead.  A ring's addition operation is
       a group operation.  (Contributed by Steve Rodriguez, 9-Sep-2007.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngogrpo $p |- ( R e. RingOps -> G e. GrpOp ) $=
      ( crngo wcel cablo cgr rngoablo ablogrpo syl ) ADEBFEBGEABCHBIJ $.
  $}

  ${
    rngone0.1 $e |- G = ( 1st ` R ) $.
    rngone0.2 $e |- X = ran G $.
    $( Obsolete theorem, use ~ ringbn0 instead.  The base set of a ring is not
       empty.  (Contributed by FL, 24-Jan-2010.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngone0 $p |- ( R e. RingOps -> X =/= (/) ) $=
      ( crngo wcel cgr c0 wne rngogrpo grpon0 syl ) AFGBHGCIJABDKBCELM $.
  $}

  ${
    ringgcl.1 $e |- G = ( 1st ` R ) $.
    ringgcl.2 $e |- X = ran G $.
    $( Obsolete theorem, use ~ ringacl instead.  Closure law for the addition
       (group) operation of a ring.  (Contributed by Steve Rodriguez,
       9-Sep-2007.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngogcl $p |- ( ( R e. RingOps /\ A e. X /\ B e. X ) -> ( A G B ) e. X ) $=
      ( crngo wcel cgr co rngogrpo grpocl syl3an1 ) CHIDJIAEIBEIABDKEICDFLABDEG
      MN $.

    $( Obsolete theorem, use ~ ringcom instead.  The addition operation of a
       ring is commutative.  (Contributed by Steve Rodriguez, 9-Sep-2007.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngocom $p |- ( ( R e. RingOps /\ A e. X /\ B e. X ) ->
                      ( A G B ) = ( B G A ) ) $=
      ( crngo wcel cablo co wceq rngoablo ablocom syl3an1 ) CHIDJIAEIBEIABDKBAD
      KLCDFMABDEGNO $.

    $( Obsolete theorem, use ~ ringgrp and ~ grpass instead.  The addition
       operation of a ring is associative.  (Contributed by Steve Rodriguez,
       9-Sep-2007.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngoaass $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                        ( ( A G B ) G C ) = ( A G ( B G C ) ) ) $=
      ( crngo wcel cgr w3a co wceq rngogrpo grpoass sylan ) DIJEKJAFJBFJCFJLABE
      MCEMABCEMEMNDEGOABCEFHPQ $.

    $( Obsolete theorem, use ~ ringabl and ~ abl32 instead.  The addition
       operation of a ring is commutative.  (Contributed by Steve Rodriguez,
       9-Sep-2007.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngoa32 $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                      ( ( A G B ) G C ) = ( ( A G C ) G B ) ) $=
      ( crngo wcel cablo w3a co wceq rngoablo ablo32 sylan ) DIJEKJAFJBFJCFJLAB
      EMCEMACEMBEMNDEGOABCEFHPQ $.

    $( Obsolete theorem, use ~ ringabl and ~ ablcmn and ~ cmn4 instead.
       Rearrangement of 4 terms in a sum of ring elements.  (Contributed by
       Steve Rodriguez, 9-Sep-2007.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngoa4 $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X ) /\
                   ( C e. X /\ D e. X ) ) ->
                     ( ( A G B ) G ( C G D ) ) = ( ( A G C ) G ( B G D ) ) ) $=
      ( crngo wcel cablo wa co wceq rngoablo ablo4 syl3an1 ) EJKFLKAGKBGKMCGKDG
      KMABFNCDFNFNACFNBDFNFNOEFHPABCDFGIQR $.

    $( Obsolete theorem, use ~ ringgrp and ~ grprcan instead.  Right
       cancellation law for the addition operation of a ring.  (Contributed by
       Steve Rodriguez, 9-Sep-2007.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngorcan $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                       ( ( A G C ) = ( B G C ) <-> A = B ) ) $=
      ( crngo wcel cgr w3a co wceq wb rngogrpo grporcan sylan ) DIJEKJAFJBFJCFJ
      LACEMBCEMNABNODEGPABCEFHQR $.

    $( Obsolete theorem, use ~ ringgrp and ~ grplcan instead.  Left
       cancellation law for the addition operation of a ring.  (Contributed by
       Steve Rodriguez, 9-Sep-2007.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngolcan $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
                       ( ( C G A ) = ( C G B ) <-> A = B ) ) $=
      ( crngo wcel cgr w3a co wceq wb rngogrpo grpolcan sylan ) DIJEKJAFJBFJCFJ
      LCAEMCBEMNABNODEGPABCEFHQR $.
  $}

  ${
    ring0cl.1 $e |- G = ( 1st ` R ) $.
    ring0cl.2 $e |- X = ran G $.
    ring0cl.3 $e |- Z = ( GId ` G ) $.
    $( Obsolete theorem, use ~ ring0cl instead.  A ring has an additive
       identity element.  (Contributed by Steve Rodriguez, 9-Sep-2007.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngo0cl $p |- ( R e. RingOps -> Z e. X ) $=
      ( crngo wcel cgr rngogrpo grpoidcl syl ) AHIBJIDCIABEKDBCFGLM $.

    $( Obsolete theorem, use ~ ringgrp and ~ grprid instead.  The additive
       identity of a ring is a right identity element.  (Contributed by Steve
       Rodriguez, 9-Sep-2007.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngo0rid $p |- ( ( R e. RingOps /\ A e. X ) -> ( A G Z ) = A ) $=
      ( crngo wcel cgr co wceq rngogrpo grporid sylan ) BIJCKJADJAECLAMBCFNAECD
      GHOP $.

    $( Obsolete theorem, use ~ ringgrp and ~ grplid instead.  The additive
       identity of a ring is a left identity element.  (Contributed by Steve
       Rodriguez, 9-Sep-2007.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngo0lid $p |- ( ( R e. RingOps /\ A e. X ) -> ( Z G A ) = A ) $=
      ( crngo wcel cgr co wceq rngogrpo grpolid sylan ) BIJCKJADJEACLAMBCFNAECD
      GHOP $.
  $}

  ${
    ringlz.1 $e |- Z = ( GId ` G ) $.
    ringlz.2 $e |- X = ran G $.
    ringlz.3 $e |- G = ( 1st ` R ) $.
    ringlz.4 $e |- H = ( 2nd ` R ) $.
    $( Obsolete theorem, use ~ ringlz instead.  The zero of a unital ring is a
       left-absorbing element.  (Contributed by FL, 31-Aug-2009.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngolz $p |- ( ( R e. RingOps /\ A e. X ) -> ( Z H A ) = Z ) $=
      ( crngo wcel wa co wceq cgr rngogrpo grpoidcl grpolid adantr syl2anc2 w3a
      oveq1d rngo0cl simpr rngodir syldan rngocl syl3anc grporid eqcomd syl2anc
      3jca simpl 3eqtr3d wb grpolcan syl13anc mpbid ) BKLZAELZMZFADNZVCCNZVCFCN
      ZOZVCFOZVBFFCNZADNZVCVDVEVBVHFADUTVHFOZVAUTCPLZFELZVJBCIQZFCEHGRFFCEHGSUA
      TUCUTVAVLVLVAUBVIVDOVBVLVLVAUTVLVABCEFIHGUDTZVNUTVAUEZUMFFABCDEIJHUFUGVBV
      KVCELZVCVEOUTVKVAVMTZVBUTVLVAVPUTVAUNVNVOFABCDEIJHUHUIZVKVPMVEVCVCFCEHGUJ
      UKULUOVBVKVPVLVPVFVGUPVQVRVNVRVCFVCCEHUQURUS $.

    $( Obsolete theorem, use ~ ringrz instead.  The zero of a unital ring is a
       right-absorbing element.  (Contributed by FL, 31-Aug-2009.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngorz $p |- ( ( R e. RingOps /\ A e. X ) -> ( A H Z ) = Z ) $=
      ( crngo wcel wa co wceq cgr rngogrpo grpoidcl grpolid adantr syl2anc2 w3a
      oveq2d simpr rngo0cl 3jca rngodi syldan rngocl mpd3an3 syl2anc 3eqtr3d wb
      eqcomd grporcan syl13anc mpbid ) BKLZAELZMZAFDNZVACNZFVACNZOZVAFOZUTAFFCN
      ZDNZVAVBVCUTVFFADURVFFOZUSURCPLZFELZVHBCIQZFCEHGRFFCEHGSUATUCURUSUSVJVJUB
      VGVBOUTUSVJVJURUSUDURVJUSBCEFIHGUETZVLUFAFFBCDEIJHUGUHUTVIVAELZVAVCOURVIU
      SVKTZURUSVJVMVLAFBCDEIJHUIUJZVIVMMVCVAVAFCEHGSUNUKULUTVIVMVJVMVDVEUMVNVOV
      LVOVAFVACEHUOUPUQ $.
  $}

  ${
    on1el3.1 $e |- G = ( 1st ` R ) $.
    on1el3.2 $e |- X = ran G $.
    $( Obsolete as of 25-Jan-2020.  Use ~ ring1zr or ~ srg1zr instead.  The
       only unital ring with a base set consisting in one element is the zero
       ring.  (Contributed by FL, 13-Feb-2010.)  (Proof shortened by Mario
       Carneiro, 30-Apr-2015.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngosn3 $p |- ( ( R e. RingOps /\ A e. B ) -> ( X = { A } <-> R =
       <. { <. <. A , A >. , A >. } , { <. <. A , A >. , A >. } >. ) ) $=
      ( crngo wcel wa csn wceq cfv cop cxp wf adantr syl5ibcom cvv wb c2nd c1st
      cgr wfo rngogrpo grpofo fof 3syl id sqxpeqd feq23d cdm fdmd eqcomd eqeq2d
      fdm xpid11 imbitrdi impbid simpr xpsng sylancom feq2d opex sylancr 3bitrd
      fsng eqeq1i bitrdi anbi1d eqid rngosm bitrd sylibd pm4.71d relrngo df-rel
      wrel wss mpbi sseli eqop syl 3bitr4d ) CHIZABIZJZEAKZLZCUAMZAANZANKZLZJCU
      BMZWLLZWMJZWICWLWLNLZWGWIWOWMWGWIDWLLZWOWGWIWHWHOZWHDPZWKKZWHDPZWRWGWIWTW
      GEEOZEDPZWIWTWEXDWFWEDUCIXCEDUDXDCDFUEDEGUFXCEDUGUHQZWIXCEWSWHDWIEWHWIUIZ
      UJZXFUKRWGWTXCWSLZWIWGXCDULZLWTXHWGXIXCWGXCEDXEUMUNWTXIWSXCWSWHDUPUOREWHU
      QURUSWGWSXAWHDWEWFWFWSXALWEWFUTZAABBVAVBZVCWGWKSIZWFXBWRTAAVDZXJWKASBDVGV
      EVFDWNWLFVHVIVJWGWIWMWGWIWSWHWJPZWMWGXCEWJPZWIXNWEXOWFCDWJEFWJVKGVLQWIXCE
      WSWHWJXGXFUKRWGXNXAWHWJPZWMWGWSXAWHWJXKVCWGXLWFXPWMTXMXJWKASBWJVGVEVMVNVO
      WGCSSOZIZWQWPTWEXRWFHXQCHVRHXQVSVPHVQVTWAQCWLWLSSWBWCWD $.

    $( Obsolete as of 25-Jan-2020.  Use ~ rngen1zr instead.  The only unital
       ring with one element is the zero ring.  (Contributed by FL,
       14-Feb-2010.)  (Revised by Mario Carneiro, 30-Apr-2015.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngosn4 $p |- ( ( R e. RingOps /\ A e. X ) -> ( X ~~ 1o <-> R =
     <. { <. <. A , A >. , A >. } , { <. <. A , A >. , A >. } >. ) ) $=
      ( crngo wcel wa c1o cen wbr csn wceq cop en1eqsnbi adantl rngosn3 bitrd
      wb ) BGHZADHZIDJKLZDAMNZBAAOAOMZUEONUBUCUDTUAADPQADBCDEFRS $.

    ${
      on1el3.3 $e |- Z = ( GId ` G ) $.
      $( Obsolete as of 25-Jan-2020.  Use ~ ringen1zr0 or ~ srgen1zr0 instead.
         The only unital ring with one element is the zero ring.  (Contributed
         by FL, 15-Feb-2010.)  (New usage is discouraged.)
         (Proof modification is discouraged.) $)
      rngosn6 $p |- ( R e. RingOps -> ( X ~~ 1o <-> R =
        <. { <. <. Z , Z >. , Z >. } , { <. <. Z , Z >. , Z >. } >. ) ) $=
        ( crngo wcel c1o cen wbr cop csn wceq wb rngo0cl rngosn4 mpdan ) AHIDCI
        CJKLADDMDMNZTMOPABCDEFGQDABCEFRS $.
    $}
  $}

  ${
    ringnegcl.1 $e |- G = ( 1st ` R ) $.
    ringnegcl.2 $e |- X = ran G $.
    ringnegcl.3 $e |- N = ( inv ` G ) $.
    $( Obsolete theorem, use ~ ringgrp and ~ grpinvcl instead.  A ring is
       closed under negation.  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngonegcl $p |- ( ( R e. RingOps /\ A e. X ) -> ( N ` A ) e. X ) $=
      ( crngo wcel cgr cfv rngogrpo grpoinvcl sylan ) BIJCKJAEJADLEJBCFMACDEGHN
      O $.

    ${
      ringaddneg.4 $e |- Z = ( GId ` G ) $.
      $( Obsolete theorem, use ~ ringgrp and ~ grplinv instead.  Adding the
         negative in a ring gives zero.  (Contributed by Jeff Madsen,
         10-Jun-2010.)  (New usage is discouraged.)
         (Proof modification is discouraged.) $)
      rngoaddneg1 $p |- ( ( R e. RingOps /\ A e. X )
            -> ( A G ( N ` A ) ) = Z ) $=
        ( crngo wcel cgr cfv co wceq rngogrpo grporinv sylan ) BKLCMLAELAADNCOF
        PBCGQAFCDEHJIRS $.

      $( Obsolete theorem, use ~ ringgrp and ~ grprinv instead.  Adding the
         negative in a ring gives zero.  (Contributed by Jeff Madsen,
         10-Jun-2010.)  (New usage is discouraged.)
         (Proof modification is discouraged.) $)
      rngoaddneg2 $p |- ( ( R e. RingOps /\ A e. X )
             -> ( ( N ` A ) G A ) = Z ) $=
        ( crngo wcel cgr cfv co wceq rngogrpo grpolinv sylan ) BKLCMLAELADNACOF
        PBCGQAFCDEHJIRS $.
    $}

    ringsub.4 $e |- D = ( /g ` G ) $.
    $( Obsolete theorem, use ~ ringgrp and ~ grpsubval instead.  Subtraction in
       a ring, in terms of addition and negation.  (Contributed by Jeff Madsen,
       19-Jun-2010.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngosub $p |- ( ( R e. RingOps /\ A e. X /\ B e. X )
                                        -> ( A D B ) = ( A G ( N ` B ) ) ) $=
      ( crngo wcel cgr co cfv wceq rngogrpo grpodivval syl3an1 ) DLMENMAGMBGMAB
      COABFPEOQDEHRABCEFGIJKST $.
  $}

  ${
    $d G u x y $.  $d X u x y $.
    $( Obsolete theorem.  The range of an internal operation with a left and
       right identity element equals its base set.  (Contributed by FL,
       24-Jan-2010.)  (Revised by Mario Carneiro, 22-Dec-2013.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngmgmbs4 $p |- ( ( G : ( X X. X ) --> X /\
      E. u e. X A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) )
         -> ran G = X ) $=
      ( vy cxp wf cv co wceq wa wral wrex wfo crn r19.12 wcel simpl eqcomd syl
      oveq2 rspceeqv ex syl5 reximdv ralimia anim2i foov sylibr forn ) DDFZDCGZ
      BHZAHZCIZUNJZUNUMCIUNJZKZADLBDMZKZUKDCNZCODJUTULUNUMEHZCIZJEDMZBDMZADLZKV
      AUSVFULUSURBDMZADLVFURBADDPVGVEADUNDQZURVDBDURUNUOJZVHVDURUOUNUPUQRSVHVIV
      DEUNDVCUOUNVBUNUMCUAUBUCUDUEUFTUGBEADDDCUHUIUKDCUJT $.
  $}

  ${
    rnplrnml0.1 $e |- H = ( 2nd ` R ) $.
    rnplrnml0.2 $e |- G = ( 1st ` R ) $.
    $( Obsolete theorem.  In a unital ring the domain of the first variable of
       the addition equals the domain of the first variable of the
       multiplication.  (Contributed by FL, 24-Jan-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngodm1dm2 $p |- ( R e. RingOps -> dom dom G = dom dom H ) $=
      ( crngo wcel crn cxp wfo cdm wceq cgr rngogrpo eqid grpofo syl rngosm fof
      wf fdmd wi fdm wa eqtr dmeqd expcom eqcoms syl5com sylc ) AFGZBHZULIZULBJ
      ZUMULCTZBKZKCKZKLZUKBMGUNABENBULULOZPQABCULEDUSRUNUPUMLZUOURUNUMULBUMULBS
      UAUOUQUMLUTURUBZUMULCUCVAUMUQUTUMUQLZURUTVBUDUPUQUPUMUQUEUFUGUHQUIUJ $.

    $( Obsolete theorem.  In a unital ring the range of the addition equals the
       domain of the first variable of the multiplication.  (Contributed by FL,
       24-Jan-2010.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngorn1 $p |- ( R e. RingOps -> ran G = dom dom H ) $=
      ( crngo wcel crn cdm cgr wceq rngogrpo grporndm syl rngodm1dm2 eqtrd ) AF
      GZBHZBIIZCIIQBJGRSKABELBMNABCDEOP $.

    ${
      $d G x y z $.  $d H x y z $.  $d R x $.
      $( Obsolete theorem.  In a unital ring the range of the addition equals
         the range of the multiplication.  (Contributed by FL, 24-Jan-2010.)
         (New usage is discouraged.)  (Proof modification is discouraged.) $)
      rngorn1eq $p |- ( R e. RingOps -> ran G = ran H ) $=
        ( vx vy vz crngo wcel crn cxp wf cv co wceq wa wral wrex eqid cablo w3a
        rngosm rngoi simprrd rngmgmbs4 syl2anc eqcomd ) AIJZCKZBKZUIUKUKLUKCMZF
        NZGNZCOZUNPUNUMCOUNPQGUKRFUKSZUJUKPABCUKEDUKTZUCUIBUAJULQUOHNZCOUMUNURC
        OZCOPUMUNURBOCOUOUMURCOZBOPUMUNBOURCOUTUSBOPUBHUKRGUKRFUKRUPFGHABCUKEDU
        QUDUEGFCUKUFUGUH $.
    $}
  $}

  ${
    $d H x y z $.  $d R x y z $.
    unmnd.1 $e |- H = ( 2nd ` R ) $.
    $( Obsolete theorem, use ~ ringgrp instead.  In a unital ring the
       multiplication is a monoid.  (Contributed by FL, 24-Jan-2010.)  (Revised
       by Mario Carneiro, 22-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngomndo $p |- ( R e. RingOps -> H e. MndOp ) $=
      ( vx vy vz wcel cdm cxp wf cv co wceq wral wa wrex w3a eqid wb cvv rngosm
      crngo cmndo c1st cfv crn rngoass ralrimivvva cablo simprrd rngorn1 xpid11
      rngoi biimpri feq23 mpancom raleqbi1dv rexeqbi1dv 3anbi123d syl mpbir3and
      raleq eqcoms c2nd fvex eleq1 mpbiri ismndo1 mp2b sylibr ) AUBGZBHHZVLIZVL
      BJZDKZEKZBLZFKZBLVOVPVRBLZBLMZFVLNZEVLNZDVLNZVQVPMVPVOBLVPMOZEVLNZDVLPZQZ
      BUCGZVKWGAUDUEZUFZWJIZWJBJZVTFWJNZEWJNZDWJNZWDEWJNZDWJPZAWIBWJWIRZCWJRZUA
      VKVTDEFWJWJWJVOVPVRAWIBWJWRCWSUGUHVKWIUIGWLOVTVOVPVRWILBLVQVOVRBLZWILMVOV
      PWILVRBLWTVSWILMQFWJNEWJNDWJNWQDEFAWIBWJWRCWSUMUJVKWJVLMWGWLWOWQQSZAWIBCW
      RUKXAVLWJVLWJMZVNWLWCWOWFWQVMWKMZXBVNWLSXCXBVLWJULUNVMVLWKWJBUOUPWBWNDVLW
      JWAWMEVLWJVTFVLWJVBUQUQWEWPDVLWJWDEVLWJVBURUSVCUTVABAVDUEZMZBTGZWHWGSCXEX
      FXDTGAVDVEBXDTVFVGDEFTBVLVLRVHVIVJ $.
  $}

  ${
    uridm.1 $e |- H = ( 2nd ` R ) $.
    uridm.2 $e |- X = ran ( 1st ` R ) $.
    ${
      uridm.3 $e |- U = ( GId ` H ) $.
      $( Obsolete theorem, use ~ ringidmlem instead.  The unity element of a
         ring is an identity element for the multiplication.  (Contributed by
         FL, 18-Feb-2010.)  (New usage is discouraged.)
         (Proof modification is discouraged.) $)
      rngoidmlem $p |- ( ( R e. RingOps /\ A e. X ) ->
        ( ( U H A ) = A /\ ( A H U ) = A ) ) $=
        ( crngo wcel co wceq wa wi crn cmndo cmagm cexid eqid ex mndomgmid 3syl
        cin rngomndo cmpidelt c1st cfv wb rngorn1eq eqtr eleq2d imbi1d syl mpan
        simpl mpcom mpbird imp ) BIJZAEJZCADKALACDKALMZUSUTVANZADOZJZVANZUSDPJD
        QRUCJZVEBDFUDDUAVFVDVAACDVCVCSHUETUBBUFUGZOZVCLZUSVBVEUHZBVGDFVGSUIEVHL
        ZVIUSVJNZGVKVIMEVCLZVLEVHVCUJVMUSVJVMUSMZUTVDVAVNEVCAVMUSUOUKULTUMUNUPU
        QUR $.

      $( Obsolete theorem, use ~ ringlidm instead.  The unity element of a ring
         is an identity element for the multiplication.  (Contributed by FL,
         18-Apr-2010.)  (New usage is discouraged.)
         (Proof modification is discouraged.) $)
      rngolidm $p |- ( ( R e. RingOps /\ A e. X ) -> ( U H A ) = A ) $=
        ( crngo wcel wa co wceq rngoidmlem simpld ) BIJAEJKCADLAMACDLAMABCDEFGH
        NO $.
    $}

    ${
      uridm2.2 $e |- U = ( GId ` H ) $.
      $( Obsolete theorem, use ~ ringridm instead.  The unity element of a ring
         is an identity element for the multiplication.  (Contributed by FL,
         18-Apr-2010.)  (New usage is discouraged.)
         (Proof modification is discouraged.) $)
      rngoridm $p |- ( ( R e. RingOps /\ A e. X ) -> ( A H U ) = A ) $=
        ( crngo wcel wa co wceq rngoidmlem simprd ) BIJAEJKCADLAMACDLAMABCDEFGH
        NO $.
    $}
  $}

  ${
    ring1cl.1 $e |- X = ran ( 1st ` R ) $.
    ring1cl.2 $e |- H = ( 2nd ` R ) $.
    ring1cl.3 $e |- U = ( GId ` H ) $.
    $( Obsolete theorem, use ~ ringidcl instead.  The unity element of a ring
       belongs to the base set.  (Contributed by FL, 12-Feb-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngo1cl $p |- ( R e. RingOps -> U e. X ) $=
      ( crngo wcel c2nd cfv crn cmagm cexid wa cmndo syl eqid cgi wceq rngomndo
      eleq1i mndoismgmOLD mndoisexid sylbi elin sylibr fveq2i eqtri iorlid c1st
      cin jca wb rngorn1eq eqtr eleq2d sylancr mpbird ) AHIZBDIZBAJKZLZIZUTVBMN
      ULIZVDUTVBMIZVBNIZOZVEUTCPIZVHACFUAVIVBPIZVHCVBPFUBVJVFVGVBUCVBUDUMUEQVBM
      NUFUGBVBVCVCRBCSKVBSKGCVBSFUHUIUJQUTDAUKKZLZTZVLVCTZVAVDUNEAVKVBVBRVKRUOV
      MVNODVCBDVLVCUPUQURUS $.
  $}

  ${
    $d R x $.  $d U x $.  $d X x $.  $d Z x $.
    uznzr.1 $e |- G = ( 1st ` R ) $.
    uznzr.2 $e |- H = ( 2nd ` R ) $.
    uznzr.3 $e |- Z = ( GId ` G ) $.
    uznzr.4 $e |- U = ( GId ` H ) $.
    uznzr.5 $e |- X = ran G $.
    $( Obsolete as of 23-Jan-2020.  Use ~ 0ring01eqbi instead.  In a unital
       ring the zero equals the ring unity iff the ring is the zero ring.
       (Contributed by FL, 14-Feb-2010.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngoueqz $p |- ( R e. RingOps -> ( X ~~ 1o <-> U = Z ) ) $=
      ( vx wcel c1o wceq wi wa syl ex wral cen wbr rngo0cl csn en1eqsn crn c1st
      crngo rneqi rngo1cl eleq2 biimpd elsni syl6com eqcomi syl5com com23 mpcom
      cfv eleq2s c0 wne rngone0 cv co oveq2 ralrimivw rngorz ralrimiva rngoridm
      eqtri r19.26 eqtr eqcoms imp31 ralimi ensn1g breq1 imbitrrid com3l sylbir
      eqsn biimtrrdi com24 mpd com13 impbid ) AUHMZENUAUBZBFOZFEMZWHWIWJPACEFGK
      IUCZWKWIWHWJWKWIWHWJPWKWIQEFUDZOZWHWJFEUEWHBCUFZMWNWJPZABDWOCAUGUSZGUIZHJ
      UJWPBEWOWNBEMZBWMMZWJWNWSWTEWMBUKULBFUMUNEWOKUOUTRUPSUQUREVAVBZWHWJWIPACE
      GKVCWJWHXAWIWJLVDZBDVEZXBFDVEZOZLETZWHXAWIPZWJXELEBFXBDVFVGWHXDFOZLETZXFX
      GPZWHXHLEXBACDEFIKGHVHVIXCXBOZLETZWHXIXJPWHXKLEXBABDEHEWOWQUFKWRVKJVJVIXL
      XFXIWHXGXLXFXIWHXGPZPZXLXFQXKXEQZLETZXNXKXELEVLXPXIXMXPXIQXOXHQZLETZXMXOX
      HLEVLXRXBFOZLETZXMXQXSLEXKXEXHXSXEXHXSPZPXBXCXBXCOZXEYAYBXEQXBXDOZYAXBXCX
      DVMYCXHXSXBXDFVMSRSVNVOVPXAXTWHWIXAXTWNWHWIPLEFWBWHWIWNWMNUAUBZWHWKYDWLFE
      VQREWMNUAVRVSWCVTRWASWASWDURWEUPWFURWG $.
  $}

  ${
    ringneg.1 $e |- G = ( 1st ` R ) $.
    ringneg.2 $e |- H = ( 2nd ` R ) $.
    ringneg.3 $e |- X = ran G $.
    ringneg.4 $e |- N = ( inv ` G ) $.
    ringneg.5 $e |- U = ( GId ` H ) $.
    $( Obsolete theorem, use ~ ringnegl instead.  Negation in a ring is the
       same as left multiplication by ` -u 1 ` .  (Contributed by Jeff Madsen,
       10-Jun-2010.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngonegmn1l $p |- ( ( R e. RingOps /\ A e. X ) ->
                                            ( N ` A ) = ( ( N ` U ) H A ) ) $=
      ( wcel wa cfv co wceq crn mpdan an32s crngo rneqi eqtri rngo1cl rngonegcl
      cgi c1st rngodir 3exp2 imp42 mpidan eqid rngoaddneg1 adantr oveq1d rngolz
      jca eqtrd rngolidm 3eqtr3rd wb rngocl rngogrpo grpoinvid1 syl3an1 mpd3an3
      3expa cgr mpbird ) BUAMZAGMZNZAFOCFOZAEPZQZAVNDPZDUFOZQZVLCVMDPZAEPZCAEPZ
      VNDPZVQVPVJVKCGMZVMGMZNZVTWBQZVJWCWDBCEGGDRBUGOZRJDWGHUBUCZILUDZVJWCWDWIC
      BDFGHJKUESZUQVJWEVKWFVJWCWDVKWFVJWCWDVKWFCVMABDEGHIJUHUIUJTUKVLVTVQAEPVQV
      LVSVQAEVJVSVQQZVKVJWCWKWICBDFGVQHJKVQULZUMSUNUOABDEGVQWLJHIUPURVLWAAVNDAB
      CEGIWHLUSUOUTVJVKVNGMZVOVRVAZVJVKWDWMWJVJWDVKWMVJWDVKWMVMABDEGHIJVBVGTUKV
      JDVHMVKWMWNBDHVCAVNVQDFGJWLKVDVEVFVI $.

    $( Obsolete theorem, use ~ ringnegr instead.  Negation in a ring is the
       same as right multiplication by ` -u 1 ` .  (Contributed by Jeff Madsen,
       19-Jun-2010.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngonegmn1r $p |- ( ( R e. RingOps /\ A e. X ) ->
                                            ( N ` A ) = ( A H ( N ` U ) ) ) $=
      ( wcel wa cfv co wceq crn mpdan adantr crngo cgi c1st rneqi eqtri rngo1cl
      rngonegcl jca rngodi 3exp2 imp43 rngoaddneg2 oveq2d rngorz eqtrd rngoridm
      eqid 3eqtr3rd wb rngocl mpd3an3 cgr rngogrpo grpoinvid2 syl3an1 mpbird )
      BUAMZAGMZNZAFOACFOZEPZQZVKADPZDUBOZQZVIAVJCDPZEPZVKACEPZDPZVNVMVIVJGMZCGM
      ZNVQVSQZVIVTWAVGVTVHVGWAVTBCEGGDRBUCOZRJDWCHUDUEZILUFZCBDFGHJKUGSTZVGWAVH
      WETUHVGVHVTWAWBVGVHVTWAWBAVJCBDEGHIJUIUJUKSVIVQAVNEPVNVIVPVNAEVGVPVNQZVHV
      GWAWGWECBDFGVNHJKVNUQZULSTUMABDEGVNWHJHIUNUOVIVRAVKDABCEGIWDLUPUMURVGVHVK
      GMZVLVOUSZVGVHVTWIWFAVJBDEGHIJUTVAVGDVBMVHWIWJBDHVCAVKVNDFGJWHKVDVEVAVF
      $.
  $}

  ${
    ringnegmul.1 $e |- G = ( 1st ` R ) $.
    ringnegmul.2 $e |- H = ( 2nd ` R ) $.
    ringnegmul.3 $e |- X = ran G $.
    ringnegmul.4 $e |- N = ( inv ` G ) $.
    $( Obsolete theorem, use ~ ringmneg1 instead.  Negation of a product in a
       ring.  (Contributed by Jeff Madsen, 19-Jun-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngoneglmul $p |- ( ( R e. RingOps /\ A e. X /\ B e. X )
                                -> ( N ` ( A H B ) ) = ( ( N ` A ) H B ) ) $=
      ( crngo wcel w3a cfv co wceq wi crn rngonegmn1l cgi c1st rneqi eqtri eqid
      rngo1cl rngonegcl mpdan rngoass 3exp2 3imp 3adant3 oveq1d wa rngocl 3expb
      mpd syldan 3impb 3eqtr4rd ) CLMZAGMZBGMZNZEUAOZFOZAEPZBEPZVFABEPZEPZAFOZB
      EPVIFOZVAVBVCVHVJQZVAVFGMZVBVCVMRRVAVEGMVNCVEEGGDSCUBOZSJDVOHUCUDIVEUEZUF
      VECDFGHJKUGUHVAVNVBVCVMVFABCDEGHIJUIUJUQUKVDVKVGBEVAVBVKVGQVCACVEDEFGHIJK
      VPTULUMVAVBVCVLVJQZVAVBVCUNVIGMZVQVAVBVCVRABCDEGHIJUOUPVICVEDEFGHIJKVPTUR
      USUT $.

    $( Obsolete theorem, use ~ ringmneg2 instead.  Negation of a product in a
       ring.  (Contributed by Jeff Madsen, 19-Jun-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    rngonegrmul $p |- ( ( R e. RingOps /\ A e. X /\ B e. X )
                                -> ( N ` ( A H B ) ) = ( A H ( N ` B ) ) ) $=
      ( crngo wcel w3a co cfv wceq wi crn rngonegmn1r cgi c1st rneqi eqtri eqid
      rngo1cl rngonegcl mpdan rngoass 3exp2 com24 com34 mpd rngocl 3expb syldan
      3imp wa 3impb 3adant2 oveq2d 3eqtr4d ) CLMZAGMZBGMZNZABEOZEUAPZFPZEOZABVI
      EOZEOZVGFPZABFPZEOVCVDVEVJVLQZVCVIGMZVDVEVORRVCVHGMVPCVHEGGDSCUBPZSJDVQHU
      CUDIVHUEZUFVHCDFGHJKUGUHVCVPVEVDVOVCVDVEVPVOVCVDVEVPVOABVICDEGHIJUIUJUKUL
      UMUQVCVDVEVMVJQZVCVDVEURVGGMZVSVCVDVEVTABCDEGHIJUNUOVGCVHDEFGHIJKVRTUPUSV
      FVNVKAEVCVEVNVKQVDBCVHDEFGHIJKVRTUTVAVB $.
  $}

  ${
    ringsubdi.1 $e |- G = ( 1st ` R ) $.
    ringsubdi.2 $e |- H = ( 2nd ` R ) $.
    ringsubdi.3 $e |- X = ran G $.
    ringsubdi.4 $e |- D = ( /g ` G ) $.
    $( Obsolete theorem, use ~ ringsubdi instead.  Ring multiplication
       distributes over subtraction.  (Contributed by Jeff Madsen,
       19-Jun-2010.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngosubdi $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) )
                          -> ( A H ( B D C ) ) = ( ( A H B ) D ( A H C ) ) ) $=
      ( wcel w3a wa co cfv wceq rngosub eqtr4d cgn eqid 3adant3r1 oveq2d rngocl
      crngo 3adant3r3 3adant3r2 jca 3expb syldan idd rngonegcl ex 3anim123d imp
      rngodi rngonegrmul ) EUFMZAHMZBHMZCHMZNZOZABCDPZGPABCFUAQZQZFPZGPZABGPZAC
      GPZDPZVDVEVHAGUSVAVBVEVHRUTBCDEFVFHIKVFUBZLSUCUDVDVLVJVKVFQZFPZVIUSVCVJHM
      ZVKHMZOVLVORZVDVPVQUSUTVAVPVBABEFGHIJKUEUGUSUTVBVQVAACEFGHIJKUEUHUIUSVPVQ
      VRVJVKDEFVFHIKVMLSUJUKVDVIVJAVGGPZFPZVOUSVCUTVAVGHMZNZVIVTRUSVCWBUSUTUTVA
      VAVBWAUSUTULUSVAULUSVBWACEFVFHIKVMUMUNUOUPABVGEFGHIJKUQUKVDVNVSVJFUSUTVBV
      NVSRVAACEFGVFHIJKVMURUHUDTTT $.

    $( Obsolete theorem, use ~ ringsubdir instead.  Ring multiplication
       distributes over subtraction.  (Contributed by Jeff Madsen,
       19-Jun-2010.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rngosubdir $p |- ( ( R e. RingOps /\ ( A e. X /\ B e. X /\ C e. X ) )
                          -> ( ( A D B ) H C ) = ( ( A H C ) D ( B H C ) ) ) $=
      ( wcel w3a wa co cfv wceq rngosub eqtr4d cgn eqid 3adant3r3 oveq1d rngocl
      crngo 3adant3r2 3adant3r1 jca 3expb syldan idd rngonegcl ex 3anim123d imp
      rngodir rngoneglmul oveq2d ) EUFMZAHMZBHMZCHMZNZOZABDPZCGPABFUAQZQZFPZCGP
      ZACGPZBCGPZDPZVEVFVICGUTVAVBVFVIRVCABDEFVGHIKVGUBZLSUCUDVEVMVKVLVGQZFPZVJ
      UTVDVKHMZVLHMZOVMVPRZVEVQVRUTVAVCVQVBACEFGHIJKUEUGUTVBVCVRVABCEFGHIJKUEUH
      UIUTVQVRVSVKVLDEFVGHIKVNLSUJUKVEVJVKVHCGPZFPZVPUTVDVAVHHMZVCNZVJWARUTVDWC
      UTVAVAVBWBVCVCUTVAULUTVBWBBEFVGHIKVNUMUNUTVCULUOUPAVHCEFGHIJKUQUKVEVOVTVK
      FUTVBVCVOVTRVABCEFGVGHIJKVNURUHUSTTT $.
  $}

  ${
    zerdivempx.1 $e |- G = ( 1st ` R ) $.
    zerdivempx.2 $e |- H = ( 2nd ` R ) $.
    zerdivempx.3 $e |- Z = ( GId ` G ) $.
    zerdivempx.4 $e |- X = ran G $.
    zerdivempx.5 $e |- U = ( GId ` H ) $.
    $d A a $.  $d B a $.  $d H a $.  $d R a $.  $d X a $.  $d Z a $.
    $( Obsolete theorem, use ~ ringinvnzdiv instead.  In a unital ring a left
       invertible element is not a zero divisor.  See also ~ ringinvnzdiv .
       (Contributed by Jeff Madsen, 18-Apr-2010.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    zerdivemp1x $p |- ( ( R e. RingOps /\ A e. X /\ E. a e. X ( a H A ) = U )
       -> ( B e. X -> ( ( A H B ) = Z -> B = Z ) ) ) $=
      ( wcel co wceq wi w3a 3exp crngo cv oveq2 wa simpl1 simpr1 simpr3 rngoass
      wrex simpl3 syl13anc eqtr ex rngorz 3adant3 crn c1st rneqi eqtri rngolidm
      cfv 3adant2 simp1 simp2 simp3 3eqtr3d com14 com13 sylc com15 com24 eqcoms
      a1d syl com25 oveq1 syl11 3imp syl6 3imp1 mpd 3exp1 syl5com rexlimiv ) CU
      AOZAGOZIUBZAFPZDQZIGUIZBGOZABFPZHQZBHQZRRZWJWFWEWOWIWFWEWORZRIGWGGOZWIWFW
      PWMWEWKWQWIWFSZWNWMWGWLFPZWGHFPZQZWEWKWRWNRRWLHWGFUCWEXAWKWRWNWEXAWKSZWRU
      DZWHBFPZWSQZWNXCWEWQWFWKXEWEXAWKWRUEXBWQWIWFUFXBWQWIWFUGWEXAWKWRUJWGABCEF
      GJKMUHUKWEXAWKWRXEWNRXEXAWKWRWEWNXEXAXDWTQZWKWRWEWNRZRRXEXAXFXDWSWTULUMWR
      WKXFXGWQWIWFWKXFXGRRZXDDBFPZQZWQWFXHRWIXJXFWFWKWQXGXFWFWKWQXGRRRZRXIXDXIX
      DQZXFXKXLXFUDXIWTQZXKXIXDWTULXMWQWKWFXGWEWQWKWFXMWNWEWQWKWFXMWNRZRZWEWQWK
      SWTHQZXIBQZXOWEWQXPWKWGCEFGHLMJKUNUOWEWKXQWQBCDFGKGEUPCUQVAZUPMEXRJURUSNU
      TVBWFXQXPXNXMXQXPWFWNXMXQXPWFWNRXMXQXPSZWNWFXSXIWTBHXMXQXPVCXMXQXPVDXMXQX
      PVEVFVMTVGVHVITVJVKVNUMVLVOWHDBFVPVQVRVHVSVJVTWAWBWCVGTWDVHVR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Division Rings
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c DivRingOps $.

  $( Extend class notation with the class of all division rings. $)
  cdrng $a class DivRingOps $.

  ${
    $d g h $.
    $( Obsolete defintion, use ~ df-drng instead.  Define the class of all
       division rings (sometimes called skew fields).  A division ring is a
       unital ring where every element except the additive identity has a
       multiplicative inverse.  (Contributed by NM, 4-Apr-2009.)
       (New usage is discouraged.) $)
    df-drngo $a |- DivRingOps = { <. g , h >. | ( <. g , h >. e. RingOps
       /\ ( h |` (
 ( ran g \ { ( GId ` g ) } ) X. ( ran g \ { ( GId ` g ) } ) ) ) e. GrpOp ) } $.
  $}

  ${
    $d G g h $.  $d H g h $.  $d x y $.
    $( Obsolete theorem, use ~ isdrng2 instead.  The predicate "is a division
       ring".  (Contributed by FL, 6-Sep-2009.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    isdivrngo $p |- ( H e. A -> ( <. G , H >. e. DivRingOps
     <-> ( <. G , H >. e. RingOps /\ ( H |` (
       ( ran G \ { ( GId ` G ) } ) X. ( ran G \ { ( GId ` G ) } ) ) )
         e. GrpOp ) ) ) $=
      ( vx vy vg vh wcel cop cdrng crngo crn cgi cfv csn cres cgr wa cv eleq1d
      cxp cvv wbr df-br df-drngo relopabiv brrelex1i sylbir anim1i ancoms cablo
      cdif rngoablo2 elex syl ad2antrl simpl copab eleq2i wceq opeq1 rneq fveq2
      jca sneqd difeq12d sqxpeqd reseq2d opeq2 reseq1 opelopabg bitrid pm5.21nd
      anbi12d ) CAHZBCIZJHZVPKHZCBLZBMNZOZULZWBUAZPZQHZRZBUBHZVORZVQVOWHVQWGVOV
      QBCJUCWGBCJUDBCJDSZESZIKHWJWILWIMNOULZWKUAPQHRDEJDEUEUFUGUHUIUJVOWFRWGVOV
      RWGVOWEVRBUKHWGBCUMBUKUNUOUPVOWFUQVDVQVPFSZGSZIZKHZWMWLLZWLMNZOZULZWSUAZP
      ZQHZRZFGURZHWHWFJXDVPFGUEUSXCBWMIZKHZWMWCPZQHZRWFFGBCUBAWLBUTZWOXFXBXHXIW
      NXEKWLBWMVATXIXAXGQXIWTWCWMXIWSWBXIWPVSWRWAWLBVBXIWQVTWLBMVCVEVFVGVHTVNWM
      CUTZXFVRXHWEXJXEVPKWMCBVITXJXGWDQWMCWCVJTVNVKVLVM $.
  $}

  ${
    $d g h H $.  $d g h R $.  $d g h X $.  $d g h Z $.
    drngi.1 $e |- G = ( 1st ` R ) $.
    drngi.2 $e |- H = ( 2nd ` R ) $.
    drngi.3 $e |- X = ran G $.
    drngi.4 $e |- Z = ( GId ` G ) $.
    $( Obsolete theorem, use ~ drngprops instead.  The properties of a division
       ring.  (Contributed by NM, 4-Apr-2009.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    drngoi $p |- ( R e. DivRingOps -> ( R e. RingOps /\
        ( H |` ( ( X \ { Z } ) X. ( X \ { Z } ) ) ) e. GrpOp ) ) $=
      ( vg vh cdrng wcel crngo cres cgr wa cfv cop eleq1d csn cdif c1st c2nd cv
      cxp crn copab wceq opeq1 id eqtr4di rneqd fveq2d difeq12d sqxpeqd reseq2d
      sneqd anbi12d opeq2 anbi1d eqtr4id reseq1d anbi2d bitr4d elopabi df-drngo
      cgi eleq2s wrel relopabiv 1st2nd mpan mpbird ) ALMZANMZCDEUAZUBZVRUFZOZPM
      ZQAUCRZAUDRZSZNMZWAQZWFAJUEZKUEZSZNMZWHWGUGZWGVHRZUAZUBZWNUFZOZPMZQZJKUHL
      WRWBWHSZNMZWHVSOZPMZQZWFJKAWGWBUIZWJWTWQXBXDWIWSNWGWBWHUJTXDWPXAPXDWOVSWH
      XDWNVRXDWKDWMVQXDWKBUGDXDWGBXDWGWBBXDUKFULZUMHULXDWLEXDWLBVHREXDWGBVHXEUN
      IULURUOUPUQTUSWHWCUIZXCWEXBQWFXFWTWEXBXFWSWDNWHWCWBUTTVAXFWAXBWEXFVTXAPXF
      CWHVSXFCWCWHGXFUKVBVCTVDVEVFJKVGZVIVOVPWEWAVOAWDNLVJVOAWDUIWRJKLXGVKALVLV
      MTVAVN $.
  $}

  ${
    ablsn.1 $e |- A e. _V $.
    $( Obsolete as of 23-Jan-2020.  Use ~ mnd1id instead.  The identity element
       of the trivial group.  (Contributed by FL, 21-Jun-2010.)  (Proof
       shortened by Mario Carneiro, 15-Dec-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    gidsn $p |- ( GId ` { <. <. A , A >. , A >. } ) = A $=
      ( cop csn cgr wcel cgi cfv wceq grposnOLD crn opex rnsnop eqcomi grpoidcl
      eqid elsni mp2b ) AACZACDZEFTGHZADZFUAAIABJUATUBTKUBSAAALMNUAPOUAAQR $.
  $}

  ${
    zrdivrng.1 $e |- A e. _V $.
    $( Obsolete theorem, use ~ zrdrng instead.  The zero ring is not a division
       ring.  (Contributed by FL, 24-Jan-2010.)  (Proof shortened by Mario
       Carneiro, 15-Dec-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    zrdivrng $p |-
         -. <. { <. <. A , A >. , A >. } , { <. <. A , A >. , A >. } >. e.
         DivRingOps $=
      ( cop csn cdrng wcel c0 cgr 0ngrp crn cgi cfv cdif cres opex rnsnop gidsn
      cxp eqtri cvv sneqi difeq12i difid xpeq2i reseq2i res0 crngo wa isdivrngo
      xp0 wb snex ax-mp simprbi eqeltrrid mto ) AACZACZDZUSCZEFZGHFIVAGUSUSJZUS
      KLZDZMZVERZNZHVGUSGNGVFGUSVFVEGRGVEGVEVEADZVHMGVBVHVDVHUQAAAOPVCAABQUAUBV
      HUCSUDVEUJSUEUSUFSVAUTUGFZVGHFZUSTFVAVIVJUHUKURULTUSUSUIUMUNUOUP $.
  $}

  ${
    dvrunz.1 $e |- G = ( 1st ` R ) $.
    dvrunz.2 $e |- H = ( 2nd ` R ) $.
    dvrunz.3 $e |- X = ran G $.
    dvrunz.4 $e |- Z = ( GId ` G ) $.
    dvrunz.5 $e |- U = ( GId ` H ) $.
    $( Obsolete theorem, use ~ drngunz instead.  In a division ring the ring
       unit is different from the zero.  (Contributed by FL, 14-Feb-2010.)
       (Revised by Mario Carneiro, 15-Dec-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dvrunz $p |- ( R e. DivRingOps -> U =/= Z ) $=
      ( cdrng wcel cop csn wn wne wceq wb syl cgi fvexi zrdivrng c1o crngo cdif
      cen wbr cxp cres cgr drngoi simpld rngoueqz rngosn6 eleq1 biimpd biimtrdi
      wi pm2.43a sylbird necon3bd mpi ) ALMZFFNFNOZVENZLMZPBFQFFCUAJUBUCVDVGBFV
      DBFRZEUDUGUHZVGVDAUEMZVIVHSVDVJDEFOUFZVKUIUJUKMACDEFGHIJULUMZABCDEFGHJKIU
      NTVIVDVGVDVIAVFRZVDVGUSVDVJVIVMSVLACEFGIJUOTVMVDVGAVFLUPUQURUTVAVBVC $.
  $}

  ${
    $d ph u x y z $.  $d G u n x y z $.  $d X u n x y z $.  $d U u n x y z $.
    isgrpda.1 $e |- ( ph -> X e. _V ) $.
    isgrpda.2 $e |- ( ph -> G : ( X X. X ) --> X ) $.
    isgrpda.3 $e |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) )
                            -> ( ( x G y ) G z ) = ( x G ( y G z ) ) ) $.
    isgrpda.4 $e |- ( ph -> U e. X ) $.
    isgrpda.5 $e |- ( ( ph /\ x e. X ) -> ( U G x ) = x ) $.
    isgrpda.6 $e |- ( ( ph /\ x e. X ) -> E. n e. X ( n G x ) = U ) $.
    $( Obsolete theorem, use ~ isgrpde instead.  Properties that determine a
       group operation.  (Contributed by Jeff Madsen, 1-Dec-2009.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    isgrpda $p |- ( ph -> G e. GrpOp ) $=
      ( vu cv co wceq wral wrex cgr wcel crn cxp wf wa ralrimivvva oveq1 eqeq1d
      w3a sylibr jca ralrimiva eqeq2 rexbidv anbi12d ralbidv rspcev syl2anc wfo
      cbvrexvw adantr simpr eqcomd rspceov syl3anc foov sylanbrc sqxpeqd feq23d
      syl raleqdv raleqbidv rexeqdv anbi2d rexeqbidv 3anbi123d mpbir3and cvv wb
      forn xpexd fexd eqid isgrpo mpbird ) AGUAUBZGUCZWHUDZWHGUEZBPZCPZGQDPZGQW
      KWLWMGQZGQRZDWHSZCWHSZBWHSZOPZWKGQZWKRZWLWKGQZWSRZCWHTZUFZBWHSZOWHTZUJZAX
      HHHUDZHGUEZWODHSZCHSZBHSZXAXCCHTZUFZBHSZOHTZJAWOBCDHHHKUGAEHUBZEWKGQZWKRZ
      XBERZCHTZUFZBHSZXQLAYCBHAWKHUBZUFZXTYBMYFFPZWKGQZERZFHTYBNYAYICFHWLYGRXBY
      HEWLYGWKGUHUIVAUKULUMXPYDOEHWSERZXOYCBHYJXAXTXNYBYJWTXSWKWSEWKGUHUIYJXCYA
      CHWSEXBUNUOUPUQURUSAWJXJWRXMXGXQAWIWHXIHGAWHHAXIHGUTZWHHRAXJWKWNRDHTCHTZB
      HSYKJAYLBHYFXRYEWKXSRYLAXRYELVBAYEVCYFXSWKMVDCDHHEWKWKGVEVFUMCDBHHHGVGVHX
      IHGWAVKZVIYMVJAWQXLBWHHYMAWPXKCWHHYMAWODWHHYMVLVMVMAXFXPOWHHYMAXEXOBWHHYM
      AXDXNXAAXCCWHHYMVNVOVMVPVQVRAGVSUBWGXHVTAXIHVSGJAHHVSVSIIWBWCBCDOVSGWHWHW
      DWEVKWF $.
  $}

  ${
    $d g h $.
    isdivrng1.1 $e |- G = ( 1st ` R ) $.
    isdivrng1.2 $e |- H = ( 2nd ` R ) $.
    isdivrng1.3 $e |- Z = ( GId ` G ) $.
    isdivrng1.4 $e |- X = ran G $.
    $( Obsolete theorem, use ~ isdrng2 instead.  The predicate "is a division
       ring".  (Contributed by Jeff Madsen, 8-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    isdrngo1 $p |- ( R e. DivRingOps <-> ( R e. RingOps /\
             ( H |` ( ( X \ { Z } ) X. ( X \ { Z } ) ) ) e. GrpOp ) ) $=
      ( vg vh cdrng wcel cfv cop crngo csn cdif cgr wa c1st c2nd wceq cres wrel
      cxp cv crn cgi df-drngo relopabiv 1st2nd relrngo adantr wb opeq12i eqeq2i
      mpan cvv fvexi isdivrngo ax-mp sneqi xpeq12i reseq2i eleq1i anbi2i bitr4i
      difeq12i eleq1 anbi1d bibi12d mpbiri sylbir pm5.21nii ) ALMZAAUANZAUBNZOZ
      UCZAPMZCDEQZRZWCUFZUDZSMZTZLUEVPVTJUGZKUGZOPMWIWHUHWHUINQRZWJUFUDSMTJKLJK
      UJUKALULURWAVTWFPUEWAVTUMAPULURUNVTABCOZUCZVPWGUOZWKVSABVQCVRFGUPUQWLWMWK
      LMZWKPMZWFTZUOWNWOCBUHZBUINZQZRZWTUFZUDZSMZTZWPCUSMWNXDUOCAUBGUTUSBCVAVBW
      FXCWOWEXBSWDXACWCWTWCWTDWQWBWSIEWRHVCVIZXEVDVEVFVGVHWLVPWNWGWPAWKLVJWLWAW
      OWFAWKPVJVKVLVMVNVO $.

    $( Obsolete theorem, use ~ drngmcl instead.  The product of two nonzero
       elements of a division ring is nonzero.  (Contributed by Jeff Madsen,
       9-Jun-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    divrngcl $p |- ( ( R e. DivRingOps /\ A e. ( X \ { Z } )
                    /\ B e. ( X \ { Z } ) ) -> ( A H B ) e. ( X \ { Z } ) ) $=
      ( wcel cxp wa co wceq adantl cdm wss eleq2d cdrng crngo csn cdif cres cgr
      isdrngo1 ovres crn wi eqid grpocl 3expib grporndm difss xpss12 mp2an fdmd
      rngosm sseqtrrid ssdmres sylib adantr dmeqd dmxpid eqtrdi anbi12d 3imtr3d
      eqtrd imp eqeltrrd 3impb syl3an1b ) CUALCUBLZEFGUCZUDZVPMZUEZUFLZNZAVPLZB
      VPLZABEOZVPLZCDEFGHIJKUGVTWAWBWDVTWAWBNZNABVROZWCVPWEWFWCPVTABVPVPEUHQVTW
      EWFVPLZVTAVRUIZLZBWHLZNZWFWHLZWEWGVSWKWLUJVNVSWIWJWLABVRWHWHUKULUMQVTWIWA
      WJWBVTWHVPAVTWHVRRZRZVPVSWHWNPVNVRUNQVTWNVQRVPVTWMVQVNWMVQPZVSVNVQERZSWOV
      NFFMZVQWPVPFSZWRVQWQSFVOUOZWSVPFVPFUPUQVNWQFECDEFHIKUSURUTVQEVAVBVCVDVPVE
      VFVIZTVTWHVPBWTTVGVTWHVPWFWTTVHVJVKVLVM $.

    $d H x y u v w z $.  $d X x y u v w z $.  $d Z x y u v w z $.
    $d R x y u v w z $.  $d U x y u v w z $.
    isdivrng2.5 $e |- U = ( GId ` H ) $.
    $( Obsolete theorem, use ~ isdrng3 instead.  A division ring is a ring in
       which ` 1 =/= 0 ` and every nonzero element is invertible.  (Contributed
       by Jeff Madsen, 8-Jun-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    isdrngo2 $p |- ( R e. DivRingOps <-> ( R e. RingOps /\ ( U =/= Z /\
             A. x e. ( X \ { Z } ) E. y e. ( X \ { Z } ) ( y H x ) = U ) ) ) $=
      ( vz wcel wa co wceq wrex adantr vu vv vw cdrng csn cdif cxp cres cgr wne
      crngo cv wral isdrngo1 dvrunz sylbir crn cdm grporndm adantl difss xpss12
      wss mp2an rngosm sseqtrrid ssdmres sylib dmeqd dmxpid eqtrdi eqtrd eleq2d
      fdmd biimpar cgn cfv grpoinvcl adantll cgi grpolinv cmagm cexid cin cmndo
      eqid rngomndo mndomgmid syl sseqtri rngorn1eq sseqtrid c1st rneqi rngo1cl
      eqtri eldifsn sylanbrc grpomndo mndoismgmOLD syl31anc oveq1 eqeq1d rspcev
      exidresid syl2anc syldan rexeqdv wb ovres ancoms rexbidva bitrd ralrimiva
      mpbid jca cvv rnex eqeltri difexg mp1i wfn wf ffnd fnssres sylancl eldifi
      fvexi anim12i 3expb sylan2 adantlr weq wi sylan2b adantlrl ovresd 3eqtr4d
      w3a sylan rngocl oveq2 rexbidv rspcv imdistanri ax-mp zerdivemp1x syl3an3
      ssrexv syl3an2 imp necon3d impr an32s ancom2s eqeltrd ralrimivva 3adantr3
      an42s ffnov simpr3 3adant3 oveq1d 3adant1 oveq2d simpr1 3adant3r1 rngoass
      fovcdm 3anim123i anim1i sylibr adantrr rngolidm adantlrr cbvrexvw isgrpda
      rspcva impbida pm5.32i bitri ) CUDOZCUKOZFGHUEZUFZUWEUGZUHZUIOZPZUWCDHUJZ
      BULZAULZFQZDRZBUWESZAUWEUMZPZPZCEFGHIJKLUNZUWCUWHUWQUWCUWHUWQUWIUWJUWPUWI
      UWBUWJUWSCDEFGHIJLKMUOUPZUWIUWOAUWEUWIUWLUWEOZPZUWKUWLUWGQZDRZBUWGUQZSZUW
      OUWIUXAUWLUXEOZUXFUWIUXGUXAUWIUXEUWEUWLUWIUXEUWGURZURZUWEUWHUXEUXIRUWCUWG
      USUTUWIUXIUWFURUWEUWIUXHUWFUWIUWFFURZVCZUXHUWFRUWCUXKUWHUWCGGUGZUWFUXJUWE
      GVCZUXMUWFUXLVCZGUWDVAZUXOUWEGUWEGVBVDZUWCUXLGFCEFGIJLVEZVNVFTUWFFVGVHVIU
      WEVJVKVLZVMVOUWIUXGPZUWLUWGVPVQZVQZUXEOZUYAUWLUWGQZDRZUXFUWHUXGUYBUWCUWLU
      WGUXTUXEUXEWFZUXTWFZVRVSUXSUYCUWGVTVQZDUWHUXGUYCUYGRUWCUWLUYGUWGUXTUXEUYE
      UYGWFUYFWAVSUWIUYGDRZUXGUWIFWBWCWDOZUWEFUQZVCZDUWEOZUWGWBOZUYHUWCUYIUWHUW
      CFWEOUYICFJWGFWHWITUWCUYKUWHUWCEUQZUWEUYJUWEGUYNUXOLWJCEFJIWKWLTUWIDGOZUW
      JUYLUWCUYOUWHCDFGGUYNCWMVQZUQLEUYPIWNWPZJMWOZTUWTDGHWQZWRUWHUYMUWCUWHUWGW
      EOUYMUWGWSUWGWTWIUTDFUWGUYJUWEUYJWFMUWGWFXEXATVLUXDUYDBUYAUXEUWKUYARUXCUY
      CDUWKUYAUWLUWGXBXCXDXFXGUXBUXFUXDBUWESZUWOUXBUXDBUXEUWEUWIUXEUWERUXAUXRTX
      HUXAUYTUWOXIUWIUXAUXDUWNBUWEUXAUWKUWEOZPUXCUWMDVUAUXAUXCUWMRUWKUWLUWEUWEF
      XJXKXCXLUTXMXOXNXPUWRUAUBUCDNUWGUWEGXQOUWEXQOUWRGUYNXQLEECWMIYHXRXSGUWDXQ
      XTYAUWRUWGUWFYBZUAULZUBULZUWGQZUWEOZUBUWEUMUAUWEUMUWFUWEUWGYCZUWRFUXLYBZU
      XNVUBUWCVUHUWQUWCUXLGFUXQYDTUXPUXLUWFFYEYFUWRVUFUAUBUWEUWEUWRVUCUWEOZVUDU
      WEOZPZPZVUEVUCVUDFQZUWEVUKVUEVUMRZUWRVUCVUDUWEUWEFXJZUTVULVUMGOZVUMHUJZVU
      MUWEOZUWCVUKVUPUWQVUKUWCVUCGOZVUDGOZPVUPVUIVUSVUJVUTVUCGUWDYGZVUDGUWDYGZY
      IUWCVUSVUTVUPVUCVUDCEFGIJLUUAYJYKYLUWCUWPVUKVUQUWJUWCVUJUWPVUIVUQUWPVUIPU
      WCVUJPZUWKVUCFQZDRZBUWESZVUIPVUQVUIUWPVVFUWOVVFAVUCUWEAUAYMZUWNVVEBUWEVVG
      UWMVVDDUWLVUCUWKFUUBXCUUCZUUDUUEVVCVUIVVFVUQUWCVUIVVFPZVUJVUQVUJUWCVVIPZV
      UTVUDHUJZPVUQVUDGHWQVVJVUTVVKVUQVVJVUTPVUMHVUDHVVJVUTVUMHRVUDHRYNZUWCVUIV
      VFVUTVVLYNZVUIUWCVUSVVFVVMVVAVVFUWCVUSVVEBGSZVVMUXMVVFVVNYNUXOVVEBUWEGUUI
      UUFVUCVUDCDEFGHBIJKLMUUGUUHUUJYJUUKUULUUMYOUUNUUOYKUUSYPVUMGHWQWRZUUPUUQU
      AUBUWEUWEUWEUWGUUTWRZUWRVUIVUJUCULZUWEOZYSZPZVUMVVQUWGQVUMVVQFQZVUEVVQUWG
      QVUCVUDVVQUWGQZUWGQZVVTVUMVVQFUWEUWRVUIVUJVURVVRVVOUURUWRVUIVUJVVRUVAYQVV
      TVUEVUMVVQUWGVVSVUNUWRVUIVUJVUNVVRVUOUVBUTUVCVVTVUCVWBFQVUCVUDVVQFQZFQZVW
      CVWAVVTVWBVWDVUCFVVSVWBVWDRZUWRVUJVVRVWFVUIVUDVVQUWEUWEFXJUVDUTUVEVVTVUCV
      WBFUWEUWRVUIVUJVVRUVFUWRVUGVVSVWBUWEOZVVPVUGVUJVVRVWGVUIVUDVVQUWEUWEUWEUW
      GUVIUVGYTYQUWCVVSVWAVWERZUWQVVSUWCVUSVUTVVQGOZYSVWHVUIVUSVUJVUTVVRVWIVVAV
      VBVVQGUWDYGUVJVUCVUDVVQCEFGIJLUVHYKYLYRYRUWCUWJUYLUWPUWCUWJPZUYOUWJPUYLUW
      CUYOUWJUYRUVKUYSUVLZUVMUWCUWJVUIDVUCUWGQZVUCRUWPVWJVUIPVWLDVUCFQZVUCVWJUY
      LVUIVWLVWMRVWKDVUCUWEUWEFXJYTUWCVUIVWMVUCRZUWJVUIUWCVUSVWNVVAVUCCDFGJUYQM
      UVNYKYLVLUVOUWCUWPVUINULZVUCUWGQZDRZNUWESZUWJUWPVUIVWRUWCVUIUWPVWRVUIUWPV
      VFVWRUWOVVFAVUCUWEVVHUVRVVFVUIVWOVUCFQZDRZNUWESZVWRVVEVWTBNUWEBNYMVVDVWSD
      UWKVWOVUCFXBXCUVPVUIVWRVXAVUIVWQVWTNUWEVWOUWEOZVUIVWQVWTXIVXBVUIPVWPVWSDV
      WOVUCUWEUWEFXJXCXKXLVOYOXGXKVSYPUVQUVSUVTUWA $.

    $( Obsolete theorem, use ~ isdrng5 instead.  A division ring is a ring in
       which ` 1 =/= 0 ` and every nonzero element is invertible.  (Contributed
       by Jeff Madsen, 10-Jun-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    isdrngo3 $p |- ( R e. DivRingOps <-> ( R e. RingOps /\ ( U =/= Z /\
                        A. x e. ( X \ { Z } ) E. y e. X ( y H x ) = U ) ) ) $=
      ( wcel wne cv co wceq wrex wa cdrng crngo csn cdif isdrngo2 wb eldifi wss
      wral wi difss ssrexv ax-mp neeq1 biimparc rngolz oveq1 syl5ibrcom necon3d
      eqeq1d imp sylan2 an4s anassrs pm3.2 syl5com eldifsn imbitrrdi imdistanda
      ancom 3imtr4g reximdv2 impbid2 ralbidva pm5.32da pm5.32i bitri ) CUANCUBN
      ZDHOZBPZAPZFQZDRZBGHUCZUDZSZAWEUIZTZTVRVSWCBGSZAWEUIZTZTABCDEFGHIJKLMUEVR
      WHWKVRVSWGWJVRVSTZWFWIAWEWAWENWLWAGNZWFWIUFWAGWDUGWLWMTZWFWIWEGUHWFWIUJGW
      DUKWCBWEGULUMWNWCWCBGWEWNWCVTGNZTWCVTWENZTWOWCTWPWCTWNWCWOWPWNWCTZWOWOVTH
      OZTZWPWQWRWOWSWLWMWCWRVRWMVSWCWRVSWCTVRWMTZWBHOZWRWCXAVSWBDHUNUOWTXAWRWTV
      THWBHWTWBHRVTHRZHWAFQZHRWACEFGHKLIJUPXBWBXCHVTHWAFUQUTURUSVAVBVCVDWOWRVEV
      FVTGHVGVHVIWOWCVJWPWCVJVKVLVMVBVNVOVPVQ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Ring homomorphisms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c RingOpsHom $.
  $c RingOpsIso $.
  $c ~=R $.

  $( Extend class notation with the class of ring homomorphisms. $)
  crngohom $a class RingOpsHom $.

  $( Extend class notation with the class of ring isomorphisms. $)
  crngoiso $a class RingOpsIso $.

  $( Extend class notation with the ring isomorphism relation. $)
  crisc $a class ~=R $.

  ${
    $d r s f x y $.
    $( Obsolete defintion, use ~ df-rhm instead.  Define the function which
       gives the set of ring homomorphisms between two given rings.
       (New usage is discouraged.)  (Contributed by Jeff Madsen,
       19-Jun-2010.) $)
    df-rngohom $a |- RingOpsHom = ( r e. RingOps , s e. RingOps |->
      { f e. ( ran ( 1st ` s ) ^m ran ( 1st ` r ) ) |
        ( ( f ` ( GId ` ( 2nd ` r ) ) ) = ( GId ` ( 2nd ` s ) ) /\
          A. x e. ran ( 1st ` r ) A. y e. ran ( 1st ` r )
 ( ( f ` ( x ( 1st ` r ) y ) ) = ( ( f ` x ) ( 1st ` s ) ( f ` y ) ) /\
   ( f ` ( x ( 2nd ` r ) y ) ) = ( ( f ` x ) ( 2nd ` s ) ( f ` y ) ) ) ) } ) $.
  $}

  ${
    $d f x y F $.  $d f r s G $.  $d f r s H $.  $d f r s J $.  $d f r s y Y $.
    $d f r s K $.  $d f r s x y R $.  $d f r s x y S $.  $d f r s x y X $.
    $d f r s U $.  $d f r s V $.
    rnghomval.1 $e |- G = ( 1st ` R ) $.
    rnghomval.2 $e |- H = ( 2nd ` R ) $.
    rnghomval.3 $e |- X = ran G $.
    rnghomval.4 $e |- U = ( GId ` H ) $.
    rnghomval.5 $e |- J = ( 1st ` S ) $.
    rnghomval.6 $e |- K = ( 2nd ` S ) $.
    rnghomval.7 $e |- Y = ran J $.
    rnghomval.8 $e |- V = ( GId ` K ) $.
    $( Obsolete theorem, use ~ rhmval0 instead.  The set of ring homomorphisms.
       (Contributed by Jeff Madsen, 19-Jun-2010.)  (Revised by Mario Carneiro,
       22-Sep-2015.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    rngohomval $p |- ( ( R e. RingOps /\ S e. RingOps ) -> ( R RingOpsHom S ) =
            { f e. ( Y ^m X ) | ( ( f ` U ) = V /\ A. x e. X A. y e. X
              ( ( f ` ( x G y ) ) = ( ( f ` x ) J ( f ` y ) ) /\
            ( f ` ( x H y ) ) = ( ( f ` x ) K ( f ` y ) ) ) ) } ) $=
      ( vr vs crngo cv c2nd cfv cgi wceq c1st co wa crn wral cmap crab crngohom
      simpr fveq2d eqtr4di rneqd simpl oveq12d eqeq12d oveqd anbi12d df-rngohom
      raleqbidv rabeqbidv ovex rabex ovmpoa ) UBUCCDUDUDUBUEZUFUGZUHUGZFUEZUGZU
      CUEZUFUGZUHUGZUIZAUEZBUEZVMUJUGZUKZVPUGZWBVPUGZWCVPUGZVRUJUGZUKZUIZWBWCVN
      UKZVPUGZWGWHVSUKZUIZULZBWDUMZUNZAWQUNZULZFWIUMZWQUOUKZUPEVPUGZKUIZWBWCGUK
      ZVPUGZWGWHIUKZUIZWBWCHUKZVPUGZWGWHJUKZUIZULZBLUNZALUNZULZFMLUOUKZUPUQVMCU
      IZVRDUIZULZWTXPFXBXQXTXAMWQLUOXTXAIUMMXTWIIXTWIDUJUGIXTVRDUJXRXSURZUSRUTZ
      VATUTXTWQGUMLXTWDGXTWDCUJUGGXTVMCUJXRXSVBZUSNUTZVAPUTZVCXTWAXDWSXOXTVQXCV
      TKXTVOEVPXTVOHUHUGEXTVNHUHXTVNCUFUGHXTVMCUFYCUSOUTZUSQUTUSXTVTJUHUGKXTVSJ
      UHXTVSDUFUGJXTVRDUFYAUSSUTZUSUAUTVDXTWRXNAWQLYEXTWPXMBWQLYEXTWKXHWOXLXTWF
      XFWJXGXTWEXEVPXTWDGWBWCYDVEUSXTWIIWGWHYBVEVDXTWMXJWNXKXTWLXIVPXTVNHWBWCYF
      VEUSXTVSJWGWHYGVEVDVFVHVHVFVIABFUCUBVGXPFXQMLUOVJVKVL $.

    $( Obsolete theorem, use ~ isrhm0 instead.  The predicate "is a ring
       homomorphism from ` R ` to ` S ` ".  (Contributed by Jeff Madsen,
       19-Jun-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    isrngohom $p |- ( ( R e. RingOps /\ S e. RingOps )
       -> ( F e. ( R RingOpsHom S ) <->
                ( F : X --> Y /\ ( F ` U ) = V /\ A. x e. X A. y e. X
              ( ( F ` ( x G y ) ) = ( ( F ` x ) J ( F ` y ) ) /\
            ( F ` ( x H y ) ) = ( ( F ` x ) K ( F ` y ) ) ) ) ) ) $=
      ( vf crngo wcel wa crngohom co cv cfv wceq wral cmap wf rngohomval eleq2d
      crab w3a crn c1st fvexi eqeltri elmap anbi1i fveq1 eqeq1d oveq12d eqeq12d
      cvv rnex anbi12d 2ralbidv elrab 3anass 3bitr4i bitrdi ) CUCUDDUCUDUEZFCDU
      FUGZUDFEUBUHZUIZKUJZAUHZBUHZGUGZVRUIZWAVRUIZWBVRUIZIUGZUJZWAWBHUGZVRUIZWE
      WFJUGZUJZUEZBLUKALUKZUEZUBMLULUGZUPZUDZLMFUMZEFUIZKUJZWCFUIZWAFUIZWBFUIZI
      UGZUJZWIFUIZXCXDJUGZUJZUEZBLUKALUKZUQZVPVQWQFABCDEUBGHIJKLMNOPQRSTUAUNUOF
      WPUDZXAXKUEZUEWSXNUEWRXLXMWSXNMLFMIURVHTIIDUSRUTVIVALGURVHPGGCUSNUTVIVAVB
      VCWOXNUBFWPVRFUJZVTXAWNXKXOVSWTKEVRFVDVEXOWMXJABLLXOWHXFWLXIXOWDXBWGXEWCV
      RFVDXOWEXCWFXDIWAVRFVDZWBVRFVDZVFVGXOWJXGWKXHWIVRFVDXOWEXCWFXDJXPXQVFVGVJ
      VKVJVLWSXAXKVMVNVO $.
  $}

  ${
    $d R x y $.  $d S x y $.  $d X x y $.  $d Y y $.  $d F x y $.
    rnghomf.1 $e |- G = ( 1st ` R ) $.
    rnghomf.2 $e |- X = ran G $.
    rnghomf.3 $e |- J = ( 1st ` S ) $.
    rnghomf.4 $e |- Y = ran J $.
    $( Obsolete theorem, use ~ rhmf instead.  A ring homomorphism is a
       function.  (Contributed by Jeff Madsen, 19-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rngohomf $p |- ( ( R e. RingOps /\ S e. RingOps
                       /\ F e. ( R RingOpsHom S ) ) -> F : X --> Y ) $=
      ( vx vy crngo wcel co wa cfv wceq eqid crngohom wf c2nd cv wral isrngohom
      cgi w3a biimpa simp1d 3impa ) ANOZBNOZCABUAPOZFGCUBZULUMQZUNQUOAUCRZUGRZC
      RBUCRZUGRZSZLUDZMUDZDPCRVBCRZVCCRZEPSVBVCUQPCRVDVEUSPSQMFUELFUEZUPUNUOVAV
      FUHLMABURCDUQEUSUTFGHUQTIURTJUSTKUTTUFUIUJUK $.

    $( Obsolete theorem, use ~ rhmcl instead.  Closure law for a ring
       homomorphism.  (Contributed by Jeff Madsen, 3-Jan-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rngohomcl $p |- ( ( ( R e. RingOps /\ S e. RingOps
                          /\ F e. ( R RingOpsHom S ) ) /\ A e. X )
                      -> ( F ` A ) e. Y ) $=
      ( crngo wcel crngohom co w3a rngohomf ffvelcdmda ) BMNCMNDBCOPNQGHADBCDEF
      GHIJKLRS $.
  $}

  ${
    $d R x y $.  $d S x y $.  $d F x y $.
    rnghom1.1 $e |- H = ( 2nd ` R ) $.
    rnghom1.2 $e |- U = ( GId ` H ) $.
    rnghom1.3 $e |- K = ( 2nd ` S ) $.
    rnghom1.4 $e |- V = ( GId ` K ) $.
    $( Obsolete theorem, use ~ rhm1 instead.  A ring homomorphism preserves
       ` 1 ` .  (Contributed by Jeff Madsen, 24-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rngohom1 $p |- ( ( R e. RingOps /\ S e. RingOps
                       /\ F e. ( R RingOpsHom S ) ) -> ( F ` U ) = V ) $=
      ( vx vy crngo wcel co cfv wceq wa eqid crngohom c1st wf cv wral isrngohom
      crn w3a biimpa simp2d 3impa ) ANOZBNOZDABUAPOZCDQGRZULUMSZUNSAUBQZUGZBUBQ
      ZUGZDUCZUOLUDZMUDZUQPDQVBDQZVCDQZUSPRVBVCEPDQVDVEFPRSMURUELURUEZUPUNVAUOV
      FUHLMABCDUQEUSFGURUTUQTHURTIUSTJUTTKUFUIUJUK $.
  $}

  ${
    $d R x y $.  $d S x y $.  $d F x y $.  $d G x y $.  $d J x y $.
    $d X x y $.  $d A x y $.  $d B y $.
    rnghomadd.1 $e |- G = ( 1st ` R ) $.
    rnghomadd.2 $e |- X = ran G $.
    rnghomadd.3 $e |- J = ( 1st ` S ) $.
    $( Obsolete theorem, use ~ rhmadd instead.  Ring homomorphisms preserve
       addition.  (Contributed by Jeff Madsen, 3-Jan-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rngohomadd $p |- ( ( ( R e. RingOps /\ S e. RingOps
        /\ F e. ( R RingOpsHom S ) ) /\ ( A e. X /\ B e. X ) )
                    -> ( F ` ( A G B ) ) = ( ( F ` A ) J ( F ` B ) ) ) $=
      ( vx vy wcel co cfv wceq wral wa eqid crngo crngohom w3a cv crn isrngohom
      wf cgi biimpa simp3d 3impa simpl 2ralimi syl fvoveq1 fveq2 oveq1d eqeq12d
      c2nd oveq2 fveq2d oveq2d rspc2v mpan9 ) CUANZDUANZECDUBONZUCZLUDZMUDZFOEP
      ZVIEPZVJEPZGOZQZMHRLHRZAHNBHNSABFOZEPZAEPZBEPZGOZQZVHVOVIVJCUSPZOEPVLVMDU
      SPZOQZSZMHRLHRZVPVEVFVGWGVEVFSZVGSHGUEZEUGZWCUHPZEPWDUHPZQZWGWHVGWJWMWGUC
      LMCDWKEFWCGWDWLHWIIWCTJWKTKWDTWITWLTUFUIUJUKWFVOLMHHVOWEULUMUNVOWBAVJFOZE
      PZVSVMGOZQLMABHHVIAQZVKWOVNWPVIAVJEFUOWQVLVSVMGVIAEUPUQURVJBQZWOVRWPWAWRW
      NVQEVJBAFUTVAWRVMVTVSGVJBEUPVBURVCVD $.
  $}

  ${
    $d R x y $.  $d S x y $.  $d F x y $.  $d H x y $.  $d K x y $.
    $d X x y $.  $d A x y $.  $d B y $.
    rnghommul.1 $e |- G = ( 1st ` R ) $.
    rnghommul.2 $e |- X = ran G $.
    rnghommul.3 $e |- H = ( 2nd ` R ) $.
    rnghommul.4 $e |- K = ( 2nd ` S ) $.
    $( Obsolete theorem, use ~ rhmmul instead.  Ring homomorphisms preserve
       multiplication.  (Contributed by Jeff Madsen, 3-Jan-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rngohommul $p |- ( ( ( R e. RingOps /\ S e. RingOps
      /\ F e. ( R RingOpsHom S ) ) /\ ( A e. X /\ B e. X ) )
                   -> ( F ` ( A H B ) ) = ( ( F ` A ) K ( F ` B ) ) ) $=
      ( vx vy wcel co cfv wceq wral crngo crngohom w3a cv wa c1st crn isrngohom
      wf cgi biimpa simp3d 3impa simpr 2ralimi syl fvoveq1 fveq2 oveq1d eqeq12d
      eqid oveq2 fveq2d oveq2d rspc2v mpan9 ) CUAPZDUAPZECDUBQPZUCZNUDZOUDZGQER
      ZVKERZVLERZHQZSZOITNITZAIPBIPUEABGQZERZAERZBERZHQZSZVJVKVLFQERVNVODUFRZQS
      ZVQUEZOITNITZVRVGVHVIWHVGVHUEZVIUEIWEUGZEUIZGUJRZERHUJRZSZWHWIVIWKWNWHUCN
      OCDWLEFGWEHWMIWJJLKWLVAWEVAMWJVAWMVAUHUKULUMWGVQNOIIWFVQUNUOUPVQWDAVLGQZE
      RZWAVOHQZSNOABIIVKASZVMWPVPWQVKAVLEGUQWRVNWAVOHVKAEURUSUTVLBSZWPVTWQWCWSW
      OVSEVLBAGVBVCWSVOWBWAHVLBEURVDUTVEVF $.
  $}

  ${
    $d R x y $.  $d S x y $.  $d G x y $.  $d J x y $.  $d F x y $.
    rnggrphom.1 $e |- G = ( 1st ` R ) $.
    rnggrphom.2 $e |- J = ( 1st ` S ) $.
    $( Obsolete theorem, use ~ rhmghm instead.  A ring homomorphism is a group
       homomorphism.  (Contributed by Jeff Madsen, 2-Jan-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rngogrphom $p |- ( ( R e. RingOps /\ S e. RingOps
                     /\ F e. ( R RingOpsHom S ) ) -> F e. ( G GrpOpHom J ) ) $=
      ( vx vy crngo wcel co crn cv cfv wral eqid wa cgr rngogrpo w3a rngohomadd
      crngohom cghomOLD wf wceq rngohomf eqcomd ralrimivva wb elghomOLD 3adant3
      syl2an mpbir2and ) AJKZBJKZCABUCLKZUAZCDEUDLKZDMZEMZCUEZHNZCOINZCOELZVCVD
      DLCOZUFZIUTPHUTPZABCDEUTVAFUTQZGVAQZUGURVGHIUTUTURVCUTKVDUTKRRVFVEVCVDABC
      DEUTFVIGUBUHUIUOUPUSVBVHRUJZUQUODSKESKVKUPADFTBEGTHICDEVAUTVIVJUKUMULUN
      $.
  $}

  ${
    rnghom0.1 $e |- G = ( 1st ` R ) $.
    rnghom0.2 $e |- Z = ( GId ` G ) $.
    rnghom0.3 $e |- J = ( 1st ` S ) $.
    rnghom0.4 $e |- W = ( GId ` J ) $.
    $( Obsolete theorem, use ~ rhm0 instead.  A ring homomorphism preserves
       ` 0 ` .  (Contributed by Jeff Madsen, 2-Jan-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rngohom0 $p |- ( ( R e. RingOps /\ S e. RingOps
                       /\ F e. ( R RingOpsHom S ) ) -> ( F ` Z ) = W ) $=
      ( crngo wcel crngohom co w3a cgr cghomOLD cfv rngogrpo 3ad2ant1 ghomidOLD
      wceq 3ad2ant2 rngogrphom syl3anc ) ALMZBLMZCABNOMZPDQMZEQMZCDEROMGCSFUCUG
      UHUJUIADHTUAUHUGUKUIBEJTUDABCDEHJUEFGCDEIKUBUF $.
  $}

  ${
    rnghomsub.1 $e |- G = ( 1st ` R ) $.
    rnghomsub.2 $e |- X = ran G $.
    rnghomsub.3 $e |- H = ( /g ` G ) $.
    rnghomsub.4 $e |- J = ( 1st ` S ) $.
    rnghomsub.5 $e |- K = ( /g ` J ) $.
    $( Obsolete theorem, use ~ rhmsub instead.  Ring homomorphisms preserve
       subtraction.  (Contributed by Jeff Madsen, 15-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rngohomsub $p |- ( ( ( R e. RingOps /\ S e. RingOps
       /\ F e. ( R RingOpsHom S ) ) /\ ( A e. X /\ B e. X ) )
                   -> ( F ` ( A H B ) ) = ( ( F ` A ) K ( F ` B ) ) ) $=
      ( crngo wcel co w3a cfv crngohom cghomOLD wceq rngogrpo 3ad2ant1 3ad2ant2
      cgr wa rngogrphom 3jca ghomdiv sylan ) CPQZDPQZECDUARQZSZFUGQZHUGQZEFHUBR
      QZSAJQBJQUHABGRETAETBETIRUCUPUQURUSUMUNUQUOCFKUDUEUNUMURUODHNUDUFCDEFHKNU
      IUJABIGEFHJLMOUKUL $.
  $}

  ${
    $d R x y $.  $d S x y $.  $d T x y $.  $d F x y $.  $d G x y $.
    $( Obsolete theorem, use ~ rhmco instead.  The composition of two ring
       homomorphisms is a ring homomorphism.  (Contributed by Jeff Madsen,
       16-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    rngohomco $p |- ( ( ( R e. RingOps /\ S e. RingOps /\ T e. RingOps )
                    /\ ( F e. ( R RingOpsHom S ) /\ G e. ( S RingOpsHom T ) ) )
                                      -> ( G o. F ) e. ( R RingOpsHom T ) ) $=
      ( vx vy wcel w3a co wa cfv wceq eqid 3expa 3adantl3 fvco3 wi ex imp crngo
      crngohom ccom c1st crn wf c2nd cgi wral rngohomf 3adantl1 adantrl adantrr
      cv fco syl2anc rngo1cl 3ad2ant1 adantr rngohom1 eqtrd rngohomadd adantlrr
      fveq2d rngohomcl anim12dan adantlrl rngogcl 3expb 3ad2antl1 adantlr sylan
      syldan oveq12 3eqtr4d rngohommul rngocl ralrimivva wb isrngohom mpbir3and
      syl jca 3adant2 ) AUAHZBUAHZCUAHZIZDABUBJHZEBCUBJHZKZKZEDUCZACUBJHZAUDLZU
      EZCUDLZUEZWMUFZAUGLZUHLZWMLZCUGLZUHLZMZFUNZGUNZWOJZWMLZXFWMLZXGWMLZWQJZMZ
      XFXGWTJZWMLZXJXKXCJZMZKZGWPUIFWPUIZWLBUDLZUEZWREUFZWPYADUFZWSWHWJYBWIWFWG
      WJYBWEWFWGWJYBBCEXTWQYAWRXTNZYANZWQNZWRNZUJOUKULWHWIYCWJWEWFWIYCWGWEWFWIY
      CABDWOXTWPYAWONZWPNZYDYEUJOPUMZWPYAWREDUOUPWLXBXADLZELZXDWLYCXAWPHZXBYLMY
      JWHYMWKWEWFYMWGAXAWTWPYIWTNZXANZUQURUSWPYAXAEDQUPWLYLBUGLZUHLZELZXDWLYKYQ
      EWHWIYKYQMZWJWEWFWIYSWGWEWFWIYSABXADWTYPYQYNYOYPNZYQNZUTOPUMVDWHWJYRXDMZW
      IWFWGWJUUBWEWFWGWJUUBBCYQEYPXCXDYTUUAXCNZXDNZUTOUKULVAVAWLXRFGWPWPWLXFWPH
      ZXGWPHZKZKZXMXQUUHXHDLZELZXFDLZELZXGDLZELZWQJZXIXLUUHUUJUUKUUMXTJZELZUUOU
      UHUUIUUPEWHWIUUGUUIUUPMZWJWHWIKZUUGUURWEWFWIUUGUURRZWGWEWFWIUUTWEWFWIIZUU
      GUURXFXGABDWOXTWPYHYIYDVBSOPTVCVDWLUUGUUKYAHZUUMYAHZKZUUQUUOMZWHWIUUGUVDW
      JUUSUUGUVDWEWFWIUUGUVDRZWGWEWFWIUVFUVAUUGUVDUVAUUEUVBUUFUVCXFABDWOXTWPYAY
      HYIYDYEVEXGABDWOXTWPYAYHYIYDYEVEVFSOPTVCZWHWJUVDUVEWIWHWJKZUVDUVEWFWGWJUV
      DUVERZWEWFWGWJUVIWFWGWJIZUVDUVEUUKUUMBCEXTWQYAYDYEYFVBSOUKTVGVMVAWLUUGXHW
      PHZXIUUJMZWHUUGUVKWKWEWFUUGUVKWGWEUUEUUFUVKXFXGAWOWPYHYIVHVIVJVKWLYCUVKUV
      LYJWPYAXHEDQVLVMUUHXJUULMZXKUUNMZKZXLUUOMWLUUEUVMUUFUVNWLYCUUEUVMYJWPYAXF
      EDQVLWLYCUUFUVNYJWPYAXGEDQVLVFZXJUULXKUUNWQVNWBVOUUHXNDLZELZUULUUNXCJZXOX
      PUUHUVRUUKUUMYPJZELZUVSUUHUVQUVTEWHWIUUGUVQUVTMZWJUUSUUGUWBWEWFWIUUGUWBRZ
      WGWEWFWIUWCUVAUUGUWBXFXGABDWOWTYPWPYHYIYNYTVPSOPTVCVDWLUUGUVDUWAUVSMZUVGW
      HWJUVDUWDWIUVHUVDUWDWFWGWJUVDUWDRZWEWFWGWJUWEUVJUVDUWDUUKUUMBCEXTYPXCYAYD
      YEYTUUCVPSOUKTVGVMVAWLUUGXNWPHZXOUVRMZWHUUGUWFWKWEWFUUGUWFWGWEUUEUUFUWFXF
      XGAWOWTWPYHYNYIVQVIVJVKWLYCUWFUWGYJWPYAXNEDQVLVMUUHUVOXPUVSMUVPXJUULXKUUN
      XCVNWBVOWCVRWHWNWSXEXSIVSZWKWEWGUWHWFFGACXAWMWOWTWQXCXDWPWRYHYNYIYOYFUUCY
      GUUDVTWDUSWA $.
  $}

  ${
    rngkerinj.1 $e |- G = ( 1st ` R ) $.
    rngkerinj.2 $e |- X = ran G $.
    rngkerinj.3 $e |- W = ( GId ` G ) $.
    rngkerinj.4 $e |- J = ( 1st ` S ) $.
    rngkerinj.5 $e |- Y = ran J $.
    rngkerinj.6 $e |- Z = ( GId ` J ) $.
    $( Obsolete theorem, use ~ rhmkerinj instead.  A ring homomorphism is
       injective if and only if its kernel is zero.  (Contributed by Jeff
       Madsen, 16-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    rngokerinj $p |- ( ( R e. RingOps /\ S e. RingOps
                         /\ F e. ( R RingOpsHom S ) )
        -> ( F : X -1-1-> Y <-> ( `' F " { Z } ) = { W } ) ) $=
      ( wcel cfv crn eqtri cgi crngo crngohom co w3a c1st cgr cghomOLD wf1 ccnv
      csn cima wceq eqid rngogrpo 3ad2ant1 3ad2ant2 rngogrphom rneqi grpokerinj
      wb fveq2i syl3anc ) AUAPZBUAPZCABUBUCPZUDAUEQZUFPZBUEQZUFPZCVFVHUGUCPGHCU
      HCUIIUJUKFUJULUTVCVDVGVEAVFVFUMZUNUOVDVCVIVEBVHVHUMZUNUPABCVFVHVJVKUQICVF
      VHFGHGDRVFRKDVFJURSFDTQVFTQLDVFTJVASHERVHRNEVHMURSIETQVHTQOEVHTMVASUSVB
      $.
  $}

  ${
    $d r s f $.
    $( Obsolete defintion, use ~ df-rim instead.  Define the function which
       gives the set of ring isomorphisms between two given rings.
       (Contributed by Jeff Madsen, 16-Jun-2011.)
       (New usage is discouraged.) $)
    df-rngoiso $a |- RingOpsIso = ( r e. RingOps , s e. RingOps |->
      { f e. ( r RingOpsHom s ) |
        f : ran ( 1st ` r ) -1-1-onto-> ran ( 1st ` s ) } ) $.
  $}

  ${
    $d f F $.  $d f r s R $.  $d f r s S $.  $d f r s X $.  $d f r s Y $.
    rngisoval.1 $e |- G = ( 1st ` R ) $.
    rngisoval.2 $e |- X = ran G $.
    rngisoval.3 $e |- J = ( 1st ` S ) $.
    rngisoval.4 $e |- Y = ran J $.
    $( Obsolete theorem, use ~ rimval instead.  The set of ring isomorphisms.
       (Contributed by Jeff Madsen, 16-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rngoisoval $p |- ( ( R e. RingOps /\ S e. RingOps ) -> ( R RingOpsIso S ) =
                         { f e. ( R RingOpsHom S ) | f : X -1-1-onto-> Y } ) $=
      ( vr vs cv c1st cfv crn wf1o crngohom eqtr4di crngo co crab crngoiso wceq
      wa oveq12 fveq2 rneqd f1oeq2d f1oeq3d sylan9bb rabeqbidv df-rngoiso rabex
      ovex ovmpoa ) LMABUAUALNZOPZQZMNZOPZQZCNZRZCURVASUBZUCFGVDRZCABSUBZUCUDUR
      AUEZVABUEZUFVEVGCVFVHURAVABSUGVIVEFVCVDRVJVGVIUTFVCVDVIUTDQFVIUSDVIUSAOPD
      URAOUHHTUIITUJVJVCGFVDVJVCEQGVJVBEVJVBBOPEVABOUHJTUIKTUKULUMCMLUNVGCVHABS
      UPUOUQ $.

    $( Obsolete theorem, use ~ isrim instead.  The predicate "is a ring
       isomorphism between ` R ` and ` S ` ".  (Contributed by Jeff Madsen,
       16-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    isrngoiso $p |- ( ( R e. RingOps /\ S e. RingOps )
             -> ( F e. ( R RingOpsIso S )
                  <-> ( F e. ( R RingOpsHom S ) /\ F : X -1-1-onto-> Y ) ) ) $=
      ( vf crngo wcel wa crngoiso co cv wf1o crngohom crab eleq2d f1oeq1 bitrdi
      rngoisoval elrab ) AMNBMNOZCABPQZNCFGLRZSZLABTQZUAZNCUKNFGCSZOUGUHULCABLD
      EFGHIJKUEUBUJUMLCUKFGUICUCUFUD $.

    $( Obsolete theorem, use ~ rimf1o instead.  A ring isomorphism is a
       bijection.  (Contributed by Jeff Madsen, 16-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rngoiso1o $p |- ( ( R e. RingOps /\ S e. RingOps
                       /\ F e. ( R RingOpsIso S ) ) -> F : X -1-1-onto-> Y ) $=
      ( crngo wcel crngoiso co wf1o wa crngohom isrngoiso simplbda 3impa ) ALMZ
      BLMZCABNOMZFGCPZUBUCQUDCABROMUEABCDEFGHIJKSTUA $.
  $}

  $( Obsolete theorem, use ~ rimrhm instead.  A ring isomorphism is a ring
     homomorphism.  (Contributed by Jeff Madsen, 16-Jun-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rngoisohom $p |- ( ( R e. RingOps /\ S e. RingOps
                       /\ F e. ( R RingOpsIso S ) )
                                          -> F e. ( R RingOpsHom S ) ) $=
    ( crngo wcel crngoiso co crngohom c1st cfv crn wf1o eqid isrngoiso simprbda
    wa 3impa ) ADEZBDEZCABFGEZCABHGEZRSPTUAAIJZKZBIJZKZCLABCUBUDUCUEUBMUCMUDMUE
    MNOQ $.

  ${
    $d R x y $.  $d S x y $.  $d F x y $.
    $( Obsolete theorem, use ~ rimcnv instead.  The inverse of a ring
       isomorphism is a ring isomorphism.  (Contributed by Jeff Madsen,
       16-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    rngoisocnv $p |- ( ( R e. RingOps /\ S e. RingOps
                         /\ F e. ( R RingOpsIso S ) )
                                          -> `' F e. ( S RingOpsIso R ) ) $=
      ( vx vy wcel co wa cfv wceq eqid sylan2 ancoms f1ocnvfv2 adantll f1ocnvdm
      wi 3expb sylan an32s crngo crngoiso ccnv crngohom c1st crn wf1o wf cgi cv
      c2nd wral f1ocnv syl ad2antll rngohom1 adantrr rngo1cl f1ocnvfv ad2ant2rl
      f1of 3expa mpd anim12dan oveq12 w3a rngohomadd exp32 imp rngogcl adantlll
      impr adantlrl 3eqtr4rd wb f1of1 ad2antlr anassrs adantllr f1fveq syl12anc
      wf1 rngohommul rngocl jca ralrimivva isrngohom adantr mpbir3and isrngoiso
      mpbid ex 3imtr4d 3impia ) AUAFZBUAFZCABUBGFZCUCZBAUBGFZWOWPHZCABUDGFZAUEI
      ZUFZBUEIZUFZCUGZHZWRBAUDGFZXEXCWRUGZHZWQWSWTXGXJWTXGHZXHXIXKXHXEXCWRUHZBU
      KIZUIIZWRIAUKIZUIIZJZDUJZEUJZXDGZWRIZXRWRIZXSWRIZXBGZJZXRXSXMGZWRIZYBYCXO
      GZJZHZEXEULDXEULZXFXLWTXAXFXIXLXCXECUMZXEXCWRVAUNUOXKXPCIXNJZXQWTXAYMXFWO
      WPXAYMABXPCXOXMXNXOKZXPKZXMKZXNKZUPVBUQWOXFYMXQQZWPXAXFWOYRWOXFXPXCFYRAXP
      XOXCXCKZYNYOURXCXEXPXNCUSLMUTVCXKYJDEXEXEXKXRXEFZXSXEFZHZHZYEYIUUCYACIZYD
      CIZJZYEUUCYBCIZYCCIZXDGZXTUUEUUDXGUUBUUIXTJZWTXFUUBUUJXAXFUUBHZUUGXRJZUUH
      XSJZHZUUJXFYTUULUUAUUMXCXEXRCNXCXEXSCNVDZUUGXRUUHXSXDVEUNOOXKUUBUUEUUIJZW
      TXAXFUUBUUPQZWOWPXAXFUUQQWOWPXAVFZXFUUBUUPUUKUURYBXCFZYCXCFZHZUUPXFYTUUSU
      UAUUTXCXEXRCPXCXEXSCPVDZYBYCABCXBXDXCXBKZYSXDKZVGLVHVBVLVIWTXFUUBUUDXTJZX
      AWPXFUUBUVEWOWPUUBXFUVEWPUUBHZXTXEFZXFUVEWPYTUUAUVGXRXSBXDXEUVDXEKZVJRZXF
      UVGUVEXCXEXTCNMSTVKVMVNWTXFUUBUUFYEVOZXAWTXFHUUBHZXCXECWBZYAXCFZYDXCFZUVJ
      XFUVLWTUUBXCXECVPVQZWPXFUUBUVMWOWPUUBXFUVMUVFUVGXFUVMUVIXFUVGUVMXCXEXTCPM
      STVKWOXFUUBUVNWPWOXFUUBUVNUUKWOUVAUVNUVBWOUUSUUTUVNYBYCAXBXCUVCYSVJRLVRVS
      XCXEYAYDCVTWAVMWKUUCYGCIZYHCIZJZYIUUCUUGUUHXMGZYFUVQUVPXGUUBUVSYFJZWTXFUU
      BUVTXAUUKUUNUVTUUOUUGXRUUHXSXMVEUNOOXKUUBUVQUVSJZWTXAXFUUBUWAQZWOWPXAXFUW
      BQUURXFUUBUWAUUKUURUVAUWAUVBYBYCABCXBXOXMXCUVCYSYNYPWCLVHVBVLVIWTXFUUBUVP
      YFJZXAWPXFUUBUWCWOWPUUBXFUWCUVFYFXEFZXFUWCWPYTUUAUWDXRXSBXDXMXEUVDYPUVHWD
      RZXFUWDUWCXCXEYFCNMSTVKVMVNWTXFUUBUVRYIVOZXAUVKUVLYGXCFZYHXCFZUWFUVOWPXFU
      UBUWGWOWPUUBXFUWGUVFUWDXFUWGUWEXFUWDUWGXCXEYFCPMSTVKWOXFUUBUWHWPWOXFUUBUW
      HUUKWOUVAUWHUVBWOUUSUUTUWHYBYCAXBXOXCUVCYNYSWDRLVRVSXCXEYGYHCVTWAVMWKWEWF
      WTXHXLXQYKVFVOZXGWPWOUWIDEBAXNWRXDXMXBXOXPXEXCUVDYPUVHYQUVCYNYSYOWGMWHWIX
      FXIWTXAYLUOWEWLABCXBXDXCXEUVCYSUVDUVHWJWPWOWSXJVOBAWRXDXBXEXCUVDUVHUVCYSW
      JMWMWN $.
  $}

  $( Obsolete theorem, use ~ rimco instead.  The composition of two ring
     isomorphisms is a ring isomorphism.  (Contributed by Jeff Madsen,
     16-Jun-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  rngoisoco $p |- ( ( ( R e. RingOps /\ S e. RingOps /\ T e. RingOps ) /\
                    ( F e. ( R RingOpsIso S ) /\ G e. ( S RingOpsIso T ) ) )
                                  -> ( G o. F ) e. ( R RingOpsIso T ) ) $=
    ( crngo wcel crngoiso co wa crngohom c1st cfv crn rngoisohom 3expa 3adantl3
    wf1o 3adantl1 eqid w3a anim12dan rngohomco syldan rngoiso1o adantrl adantrr
    ccom f1oco syl2anc wb isrngoiso 3adant2 adantr mpbir2and ) AFGZBFGZCFGZUAZD
    ABHIGZEBCHIGZJZJZEDUHZACHIGZVDACKIGZALMZNZCLMZNZVDRZUSVBDABKIGZEBCKIGZJVFUS
    UTVLVAVMUPUQUTVLURUPUQUTVLABDOPQUQURVAVMUPUQURVAVMBCEOPSUBABCDEUCUDVCBLMZNZ
    VJERZVHVODRZVKUSVAVPUTUQURVAVPUPUQURVAVPBCEVNVIVOVJVNTZVOTZVITZVJTZUEPSUFUS
    UTVQVAUPUQUTVQURUPUQUTVQABDVGVNVHVOVGTZVHTZVRVSUEPQUGVHVOVJEDUIUJUSVEVFVKJU
    KZVBUPURWDUQACVDVGVIVHVJWBWCVTWAULUMUNUO $.

  ${
    $d r s f $.
    $( Obsolete defintion, use ~ dfric2 instead.  Define the ring isomorphism
       relation.  (Contributed by Jeff Madsen, 16-Jun-2011.)
       (New usage is discouraged.) $)
    df-risc $a |- ~=R = { <. r , s >. | ( ( r e. RingOps /\ s e. RingOps )
                                  /\ E. f f e. ( r RingOpsIso s ) ) } $.
  $}

  ${
    $d R r s f $.  $d S r s f $.
    $( Obsolete theorem, use ~ isbrric2 instead.  The ring isomorphism
       relation.  (Contributed by Jeff Madsen, 16-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    isriscg $p |- ( ( R e. A /\ S e. B ) -> ( R ~=R S <->
                        ( ( R e. RingOps /\ S e. RingOps )
                          /\ E. f f e. ( R RingOpsIso S ) ) ) ) $=
      ( vr vs cv crngo wcel wa crngoiso co wex crisc wceq eleq2d exbidv anbi12d
      eleq1 anbi1d oveq1 anbi2d oveq2 df-risc brabg ) FHZIJZGHZIJZKZEHZUGUILMZJ
      ZENZKCIJZUJKZULCUILMZJZENZKUPDIJZKZULCDLMZJZENZKFGCDABOUGCPZUKUQUOUTVFUHU
      PUJUGCITUAVFUNUSEVFUMURULUGCUILUBQRSUIDPZUQVBUTVEVGUJVAUPUIDITUCVGUSVDEVG
      URVCULUIDCLUDQRSEGFUEUF $.
  $}

  ${
    $d R f $.  $d S f $.
    isrisc.1 $e |- R e. _V $.
    isrisc.2 $e |- S e. _V $.
    $( Obsolete theorem, use ~ isbrric2 instead.  The ring isomorphism
       relation.  (Contributed by Jeff Madsen, 16-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    isrisc $p |- ( R ~=R S <-> ( ( R e. RingOps /\ S e. RingOps )
                              /\ E. f f e. ( R RingOpsIso S ) ) ) $=
      ( cvv wcel crisc wbr crngo wa cv crngoiso co wex wb isriscg mp2an ) AFGBF
      GABHIAJGBJGKCLABMNGCOKPDEFFABCQR $.
  $}

  ${
    $d R f $.  $d S f $.
    $( Obsolete theorem, use ~ brric2 instead.  The ring isomorphism relation.
       (Contributed by Jeff Madsen, 16-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    risc $p |- ( ( R e. RingOps /\ S e. RingOps ) ->
                      ( R ~=R S <-> E. f f e. ( R RingOpsIso S ) ) ) $=
      ( crngo wcel wa crisc wbr cv crngoiso co wex isriscg bianabs ) ADEBDEFABG
      HCIABJKECLDDABCMN $.
  $}

  ${
    $d R f $.  $d S f $.  $d F f $.
    $( Obsolete theorem, use ~ brrici instead.  Determine that two rings are
       isomorphic.  (Contributed by Jeff Madsen, 16-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    risci $p |- ( ( R e. RingOps /\ S e. RingOps /\
                                F e. ( R RingOpsIso S ) ) -> R ~=R S ) $=
      ( vf crngo wcel crngoiso co crisc wbr wa wex elex2 risc imbitrrid 3impia
      cv ) AEFZBEFZCABGHZFZABIJZUAUBRSKDQTFDLDCTMABDNOP $.
  $}

  ${
    $d f g r s t $.
    $( Obsolete theorem, use ~ ricer instead.  Ring isomorphism is an
       equivalence relation.  (Contributed by Jeff Madsen, 16-Jun-2011.)
       (Revised by Mario Carneiro, 12-Aug-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    riscer $p |- ~=R Er dom ~=R $=
      ( vr vs vt vf vg crisc cv wbr wi wa wal crngo wcel crngoiso co wex isrisc
      vex 3expia risci cdm wer wrel wceq df-risc relopabiv eqid ccnv rngoisocnv
      ancoms syld exlimdv imp sylbi exdistrv ccom rngoisoco ex 3adant2 exlimdvv
      biimtrrid 3expb adantlr an4s syl2anb pm3.2i ax-gen gen2 dfer2 mpbir3an
      w3a ) FUAZFUBFUCVLVLUDAGZBGZFHZVNVMFHZIZVOVNCGZFHZJVMVRFHZIZJZCKZBKAKVMLM
      ZVNLMZJZDGZVMVNNOMZDPZJZABFDBAUEUFVLUGWCABWBCVQWAVOWJVPVMVNDARBRZQZWFWIVP
      WFWHVPDWFWHWGUHZVNVMNOMZVPWDWEWHWNVMVNWGUISWEWDWNVPIWEWDWNVPVNVMWMTSUJUKU
      LUMUNVOWJWEVRLMZJZEGZVNVRNOMZEPZJVTVSWLVNVREWKCRQWFWPWIWSVTWFWPJWIWSJZVTW
      DWPWTVTIZWEWDWEWOXAWTWHWRJZEPDPWDWEWOVKZVTWHWRDEUOXCXBVTDEXCXBWQWGUPZVMVR
      NOMZVTXCXBXEVMVNVRWGWQUQURWDWOXEVTIWEWDWOXEVTVMVRXDTSUSUKUTVAVBVCUMVDVEVF
      VGVHABCVLFVIVJ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Commutative rings
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Com2 $.

  $( Extend class notation with a class that adds commutativity to various
     flavors of rings. $)
  ccm2 $a class Com2 $.

  ${
    $d g h a b $.
    $( Obsolete definition, used in other obsolete definitions only.  A device
       to add commutativity to various sorts of rings.  I use ` ran g ` because
       I suppose ` g ` has a neutral element and therefore is onto.
       (Contributed by FL, 6-Sep-2009.)  (New usage is discouraged.) $)
    df-com2 $a |- Com2 = { <. g , h >. | A. a e. ran g A. b e. ran g
     ( a h b ) = ( b h a ) } $.
  $}

  $c Fld $.

  $( Extend class notation with the class of all fields. $)
  cfld $a class Fld $.

  $( Add alternate definition. Add Kennington's one (=/= the zero ring),
       and Mizar's one: ` ( GId `` G ) =/= ( GId `` H ) ` $)
  $( Obsolete defintion, use ~ df-field instead.  Definition of a field.  A
     field is a commutative division ring.  (Contributed by FL, 6-Sep-2009.)
     (Revised by Jeff Madsen, 10-Jun-2010.)  (New usage is discouraged.) $)
  df-fld $a |- Fld = ( DivRingOps i^i Com2 ) $.

  $c CRingOps $.

  $( Extend class notation with the class of commutative rings. $)
  ccring $a class CRingOps $.

  $( Obsolete defintion, use ~ df-cring instead.  Define the class of
     commutative rings.  (Contributed by Jeff Madsen, 8-Jun-2010.)
     (New usage is discouraged.) $)
  df-crngo $a |- CRingOps = ( RingOps i^i Com2 ) $.

  ${
    $d G a b x y $.  $d H a b x y $.
    $( Obsolete theorem, used (as lemma) in other obsolete theorems only.  A
       device to add commutativity to various sorts of rings.  (Contributed by
       FL, 6-Sep-2009.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    iscom2 $p |- ( ( G e. A /\ H e. B ) -> ( <. G , H >. e. Com2 <->
     A. a e. ran G A. b e. ran G ( a H b ) = ( b H a ) ) ) $=
      ( vy vx wcel wa cop ccm2 cv co wceq crn wral copab df-com2 oveq raleqbidv
      a1i eleq2d rneq raleqdv eqeq12d 2ralbidv opelopabg bitrd ) CAIDBIJZCDKZLI
      UKEMZFMZGMZNZUMULUNNZOZFHMZPZQZEUSQZHGRZIULUMDNZUMULDNZOZFCPZQEVFQZUJLVBU
      KLVBOUJHGEFSUBUCVAUQFVFQZEVFQVGHGCDABURCOZUTVHEUSVFURCUDZVIUQFUSVFVJUEUAU
      NDOZUQVEEFVFVFVKUOVCUPVDULUMUNDTUMULUNDTUFUGUHUI $.
  $}

  $( Obsolete theorem, use ~ iscrng instead.  The predicate "is a commutative
     ring".  (Contributed by Jeff Madsen, 8-Jun-2010.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  iscrngo $p |- ( R e. CRingOps <-> ( R e. RingOps /\ R e. Com2 ) ) $=
    ( crngo ccm2 ccring df-crngo elin2 ) ABCDEF $.

  ${
    $d R x y $.  $d X x y $.
    iscring2.1 $e |- G = ( 1st ` R ) $.
    iscring2.2 $e |- H = ( 2nd ` R ) $.
    iscring2.3 $e |- X = ran G $.
    $( Obsolete theorem, use ~ iscrng2 instead.  The predicate "is a
       commutative ring".  (Contributed by Jeff Madsen, 8-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    iscrngo2 $p |- ( R e. CRingOps <-> ( R e. RingOps /\
                          A. x e. X A. y e. X ( x H y ) = ( y H x ) ) ) $=
      ( wcel crngo ccm2 wa cv co wceq wral c1st cfv cvv ccring iscrngo c2nd cop
      wb wrel relrngo 1st2nd mpan eleq1 crn rneqi eqtri raleqi eqeq12i raleqbii
      oveqi ralbii fvex iscom2 mp2an 3bitr4ri bitrdi syl pm5.32i bitri ) CUAJCK
      JZCLJZMVGANZBNZEOZVJVIEOZPZBFQZAFQZMCUBVGVHVOVGCCRSZCUCSZUDZPZVHVOUEKUFVG
      VSUGCKUHUIVSVHVRLJZVOCVRLUJVIVJVQOZVJVIVQOZPZBVPUKZQZAFQWEAWDQZVOVTWEAFWD
      FDUKWDIDVPGULUMZUNVNWEAFVMWCBFWDWGVKWAVLWBEVQVIVJHUQEVQVJVIHUQUOUPURVPTJV
      QTJVTWFUECRUSCUCUSTTVPVQABUTVAVBVCVDVEVF $.
  $}

  ${
    $d ph w x y z $.  $d G w x y z $.  $d H w x y z $.  $d X w x y z $.
    $d U x y $.
    iscringd.1 $e |- ( ph -> G e. AbelOp ) $.
    iscringd.2 $e |- ( ph -> X = ran G ) $.
    iscringd.3 $e |- ( ph -> H : ( X X. X ) --> X ) $.
    iscringd.4 $e |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) )
                                  -> ( ( x H y ) H z ) = ( x H ( y H z ) ) ) $.
    iscringd.5 $e |- ( ( ph /\ ( x e. X /\ y e. X /\ z e. X ) )
                          -> ( x H ( y G z ) ) = ( ( x H y ) G ( x H z ) ) ) $.
    iscringd.6 $e |- ( ph -> U e. X ) $.
    iscringd.7 $e |- ( ( ph /\ y e. X ) -> ( y H U ) = y ) $.
    iscringd.8 $e |- ( ( ph /\ ( x e. X /\ y e. X ) )
                                              -> ( x H y ) = ( y H x ) ) $.
    $( Obsolete theorem, use ~ iscrngd instead.  Conditions that determine a
       commutative ring.  (Contributed by Jeff Madsen, 20-Jun-2011.)  (Revised
       by Mario Carneiro, 23-Dec-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    iscringd $p |- ( ph -> <. G , H >. e. CRingOps ) $=
      ( wcel co wceq wa vw cop crngo ccm2 ccring cv w3a id 3com13 eleq1 3anbi1d
      wi anbi2d oveq2 oveq12d eqeq12d imbi12d 3anbi3d oveq1 oveq1d cablo adantr
      crn simpr3 eleqtrd simpr2 eqid ablocom syl3anc simpr1 cgr ablogrpo grpocl
      syl eleqtrrd jca ovex chvarvv syldan 3adantr3 3adantr2 cxp fovcdmd 3eqtrd
      vtocl wf 3eqtr2d sylan2 imbi2d an12s ex vtoclga mpcom isrngod wral eleq2d
      eqtrd anbi12d biimpar ralrimivva cvv wb rnexg eqeltrd fexd iscom2 syl2anc
      xpexd mpbird iscrngo sylanbrc ) AFGUBZUCQXLUDQZXLUEQABCDEFGHIJKLMBUFZHQZC
      UFZHQZDUFZHQZUGZAXSXQXOUGZXNXPFRZXRGRZXNXRGRZXPXRGRZFRZSZXSXQXOYAYAUHUIAU
      AUFZHQZXQXOUGZTZYBYHGRZXNYHGRZXPYHGRZFRZSZULZAYATZYGULUADYHXRSZYKYRYPYGYS
      YJYAAYSYIXSXQXOYHXRHUJUKUMYSYLYCYOYFYHXRYBGUNYSYMYDYNYEFYHXRXNGUNYHXRXPGU
      NUOUPUQAYIXQXSUGZTZXRXPFRZYHGRZXRYHGRZYNFRZSZULZYQDBXRXNSZUUAYKUUFYPUUHYT
      YJAUUHXSXOYIXQXRXNHUJURUMUUHUUCYLUUEYOUUHUUBYBYHGXRXNXPFUSUTUUHUUDYMYNFXR
      XNYHGUSUTUPUQAXTTZUUBXNGRZXRXNGRZXPXNGRZFRZSZULUUGBUAXNYHSZUUIUUAUUNUUFUU
      OXTYTAUUOXOYIXQXSXNYHHUJUKUMUUOUUJUUCUUMUUEXNYHUUBGUNUUOUUKUUDUULYNFXNYHX
      RGUNXNYHXPGUNUOUPUQUUIUUJXPXRFRZXNGRZXNUUPGRZUUMUUIUUBUUPXNGUUIFVAQZXRFVC
      ZQZXPUUTQZUUBUUPSAUUSXTIVBZUUIXRHUUTAXOXQXSVDZAHUUTSXTJVBZVEZUUIXPHUUTAXO
      XQXSVFZUVEVEZXRXPFUUTUUTVGZVHVIUTAXTXOUUPHQZTZUURUUQSZUUIXOUVJAXOXQXSVJZU
      UIUUPUUTHUUIFVKQZUVBUVAUUPUUTQUUIUUSUVNUVCFVLVNUVHUVFXPXRFUUTUVIVMVIUVEVO
      VPAXOYITZTZYMYHXNGRZSZULZAUVKTZUVLULUAUUPXPXRFVQYHUUPSZUVPUVTUVRUVLUWAUVO
      UVKAUWAYIUVJXOYHUUPHUJUMUMUWAYMUURUVQUUQYHUUPXNGUNYHUUPXNGUSUPUQAXOXQTZTZ
      XNXPGRZUULSZULZUVSCUAXPYHSZUWCUVPUWEUVRUWGUWBUVOAUWGXQYIXOXPYHHUJUMUMUWGU
      WDYMUULUVQXPYHXNGUNXPYHXNGUSUPUQPVRWEVSUUIUURUWDYDFRUULUUKFRZUUMMUUIUWDUU
      LYDUUKFAXOXQUWEXSPVTAXOXSYDUUKSZXQUWFAXOXSTZTZUWIULCDXPXRSZUWCUWKUWEUWIUW
      LUWBUWJAUWLXQXSXOXPXRHUJUMUMUWLUWDYDUULUUKXPXRXNGUNXPXRXNGUSUPUQPVRWAUOUU
      IUUSUULUUTQUUKUUTQUWHUUMSUVCUUIUULHUUTUUIXPXNHHHGAHHWBZHGWFXTKVBZUVGUVMWC
      UVEVEUUIUUKHUUTUUIXRXNHHHGUWNUVDUVMWCUVEVEUULUUKFUUTUVIVHVIWDWGVRVRVRWHNA
      XQTZEXPGRZXPEGRZXPEHQZUWOUWPUWQSZAUWRXQNVBUWOUWEULUWOUWSULBEHXNESZUWEUWSU
      WOUWTUWDUWPUULUWQXNEXPGUSXNEXPGUNUPWIXOUWOUWEAXOXQUWEPWJWKWLWMOWQOWNAXMUW
      ECUUTWOBUUTWOZAUWEBCUUTUUTAXNUUTQZUVBTZUWBUWEAUWBUXCAXOUXBXQUVBAHUUTXNJWP
      AHUUTXPJWPWRWSPVSWTAUUSGXAQXMUXAXBIAUWMHXAGKAHHXAXAAHUUTXAJAUUSUUTXAQIFVA
      XCVNXDZUXDXHXEVAXAFGBCXFXGXIXLXJXK $.
  $}

  $( Obsolete theorem, use ~ flddrngd instead.  A field is a division ring.
     (Contributed by Jeff Madsen, 10-Jun-2010.)  (Revised by Mario Carneiro,
     15-Dec-2013.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  flddivrng $p |- ( K e. Fld -> K e. DivRingOps ) $=
    ( cfld cdrng ccm2 cin df-fld inss1 eqsstri sseli ) BCABCDECFCDGHI $.

  $( Obsolete theorem, use ~ crngringd instead.  A commutative ring is a ring.
     (Contributed by Jeff Madsen, 10-Jun-2010.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  crngorngo $p |- ( R e. CRingOps -> R e. RingOps ) $=
    ( ccring wcel crngo ccm2 iscrngo simplbi ) ABCADCAECAFG $.

  ${
    $d X x y $.  $d A x y $.  $d B y $.  $d H x y $.  $d R x y $.
    crngocom.1 $e |- G = ( 1st ` R ) $.
    crngocom.2 $e |- H = ( 2nd ` R ) $.
    crngocom.3 $e |- X = ran G $.
    $( Obsolete theorem, use ~ crngcom instead.  The multiplication operation
       of a commutative ring is commutative.  (Contributed by Jeff Madsen,
       8-Jun-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    crngocom $p |- ( ( R e. CRingOps /\ A e. X /\ B e. X )
                                        -> ( A H B ) = ( B H A ) ) $=
      ( vx vy ccring wcel co wceq cv wral oveq1 oveq2 eqeq12d wa crngo iscrngo2
      simprbi rspc2v mpan9 3impb ) CLMZAFMZBFMZABENZBAENZOZUHJPZKPZENZUOUNENZOZ
      KFQJFQZUIUJUAUMUHCUBMUSJKCDEFGHIUCUDURUMAUOENZUOAENZOJKABFFUNAOUPUTUQVAUN
      AUOERUNAUOESTUOBOUTUKVAULUOBAESUOBAERTUEUFUG $.
  $}

  ${
    crngm.1 $e |- G = ( 1st ` R ) $.
    crngm.2 $e |- H = ( 2nd ` R ) $.
    crngm.3 $e |- X = ran G $.
    $( Obsolete theorem, use ~ crng32d instead.  Commutative/associative law
       for commutative rings.  (Contributed by Jeff Madsen, 19-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    crngm23 $p |- ( ( R e. CRingOps /\ ( A e. X /\ B e. X /\ C e. X ) )
                                -> ( ( A H B ) H C ) = ( ( A H C ) H B ) ) $=
      ( ccring wcel w3a wa co wceq crngocom 3adant3r1 rngoass sylan crngo 3exp2
      oveq2d crngorngo com34 3imp2 3eqtr4d ) DKLZAGLZBGLZCGLZMZNZABCFOZFOZACBFO
      ZFOZABFOCFOZACFOBFOZUMUNUPAFUHUJUKUNUPPUIBCDEFGHIJQRUCUHDUALZULURUOPDUDZA
      BCDEFGHIJSTUHUTULUSUQPZVAUTUIUJUKVBUTUIUKUJVBUTUIUKUJVBACBDEFGHIJSUBUEUFT
      UG $.

    $( Obsolete theorem, use ~ crng4 instead.  Commutative/associative law for
       commutative rings.  (Contributed by Jeff Madsen, 19-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    crngm4 $p |- ( ( R e. CRingOps /\ ( A e. X /\ B e. X )
                                  /\ ( C e. X /\ D e. X ) ) ->
                  ( ( A H B ) H ( C H D ) ) = ( ( A H C ) H ( B H D ) ) ) $=
      ( wcel wa co wceq w3a adantrrr rngocl 3expb 3jca ccring crngm23 crngorngo
      df-3an sylan2br oveq1d crngo adantrr simprrl simprrr rngoass syldan sylan
      adantrlr simprlr 3eqtr3d 3impb ) EUALZAHLZBHLZMZCHLZDHLZMZABGNZCDGNGNZACG
      NZBDGNGNZOURVAVDMZMZVECGNZDGNZVGBGNZDGNZVFVHVJVKVMDGURVAVBVKVMOZVCVAVBMUR
      USUTVBPVOUSUTVBUDABCEFGHIJKUBUEQUFUREUGLZVIVLVFOZEUCZVPVIVEHLZVBVCPVQVPVI
      MZVSVBVCVPVAVSVDVPUSUTVSABEFGHIJKRSUHVPVAVBVCUIVPVAVBVCUJZTVECDEFGHIJKUKU
      LUMURVPVIVNVHOZVRVPVIVGHLZUTVCPWBVTWCUTVCVPVAVBWCVCVPUSVBWCUTVPUSVBWCACEF
      GHIJKRSUNQVPUSUTVDUOWATVGBDEFGHIJKUKULUMUPUQ $.
  $}

  $( Obsolete theorem, use ~ fldcrngd instead.  A field is a commutative ring.
     (Contributed by Jeff Madsen, 8-Jun-2010.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  fldcrngo $p |- ( K e. Fld -> K e. CRingOps ) $=
    ( cdrng wcel ccm2 crngo cfld ccring c2nd cfv c1st crn cgi csn cdif cxp cres
    wa cgr eqid drngoi simpld anim1i df-fld elin2 iscrngo 3imtr4i ) ABCZADCZQAE
    CZUHQAFCAGCUGUIUHUGUIAHIZAJIZKZUKLIZMNZUNOPRCAUKUJULUMUKSUJSULSUMSTUAUBABDF
    UCUDAUEUF $.

  $( Obsolete theorem, use ~ isfld instead.  The predicate "is a field".
     (Contributed by Jeff Madsen, 10-Jun-2010.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  isfld2 $p |- ( K e. Fld <-> ( K e. DivRingOps /\ K e. CRingOps ) ) $=
    ( cfld wcel cdrng ccring wa flddivrng fldcrngo jca ccm2 iscrngo simprbi cin
    crngo elin biimpri df-fld eleqtrrdi sylan2 impbii ) ABCZADCZAECZFUAUBUCAGAH
    IUCUBAJCZUAUCANCUDAKLUBUDFZADJMZBAUFCUEADJOPQRST $.

  ${
    $d R w x y z $.  $d S w x y z $.  $d X w x y z $.  $d Y w x y z $.
    $d F w x y z $.
    crngohomfo.1 $e |- G = ( 1st ` R ) $.
    crngohomfo.2 $e |- X = ran G $.
    crngohomfo.3 $e |- J = ( 1st ` S ) $.
    crngohomfo.4 $e |- Y = ran J $.
    $( Obsolete theorem, use ~ crngrhmfo instead.  The image of a homomorphism
       from a commutative ring is commutative.  (Contributed by Jeff Madsen,
       4-Jan-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    crngohomfo $p |- ( ( ( R e. CRingOps /\ S e. RingOps )
                         /\ ( F e. ( R RingOpsHom S )
                              /\ F : X -onto-> Y ) ) -> S e. CRingOps ) $=
      ( vy vz vw vx wcel wa co cfv wceq ccring crngohom wfo cv c2nd wral simplr
      crngo wrex wi foelrn anim12d reeanv imbitrrdi ad2antll w3a crngocom 3expb
      eqid 3ad2antl1 fveq2d crngorngo rngohommul syl3anl1 ancom2s oveq12 ancoms
      3eqtr3d eqeq12d syl5ibrcom 3expa adantrr rexlimdvv syld iscrngo2 sylanbrc
      ex ralrimivv ) AUAPZBUHPZQZCABUBRPZFGCUCZQZQZVTLUDZMUDZBUESZRZWGWFWHRZTZM
      GUFLGUFBUAPVSVTWDUGWEWKLMGGWEWFGPZWGGPZQZWFNUDZCSZTZWGOUDZCSZTZQZOFUINFUI
      ZWKWCWNXBUJWAWBWCWNWQNFUIZWTOFUIZQXBWCWLXCWMXDWCWLXCNFGWFCUKVQWCWMXDOFGWG
      CUKVQULWQWTNOFFUMUNUOWEXAWKNOFFWAWBWOFPZWRFPZQZXAWKUJZUJZWCVSVTWBXIVSVTWB
      UPZXGXHXJXGQZWKXAWPWSWHRZWSWPWHRZTXKWOWRAUESZRZCSZWRWOXNRZCSZXLXMXKXOXQCV
      SVTXGXOXQTZWBVSXEXFXSWOWRADXNFHXNUSZIUQURUTVAVSAUHPZVTWBXGXPXLTAVBZWOWRAB
      CDXNWHFHIXTWHUSZVCVDVSYAVTWBXGXRXMTZYBYAVTWBUPXFXEYDWRWOABCDXNWHFHIXTYCVC
      VEVDVHXAWIXLWJXMWFWPWGWSWHVFWTWQWJXMTWGWSWFWPWHVFVGVIVJVQVKVLVMVNVRLMBEWH
      GJYCKVOVP $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Ideals
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Idl $.
  $c PrIdl $.
  $c MaxIdl $.

  $( Extend class notation with the class of ideals. $)
  cidl $a class Idl $.

  $( Extend class notation with the class of prime ideals. $)
  cpridl $a class PrIdl $.

  $( Extend class notation with the class of maximal ideals. $)
  cmaxidl $a class MaxIdl $.

  ${
    $d r i x y z $.
    $( Obsolete defintion, use ~ df-2idl (or ~ df-lidl ) instead.  Define the
       class of (two-sided) ideals of a ring ` R ` .  A subset of ` R ` is an
       ideal if it contains ` 0 ` , is closed under addition, and is closed
       under multiplication on either side by any element of ` R ` .
       (Contributed by Jeff Madsen, 10-Jun-2010.)
       (New usage is discouraged.) $)
    df-idl $a |- Idl = ( r e. RingOps |->
                { i e. ~P ran ( 1st ` r ) | ( ( GId ` ( 1st ` r ) ) e. i /\
                      A. x e. i ( A. y e. i ( x ( 1st ` r ) y ) e. i /\
                    A. z e. ran ( 1st ` r ) ( ( z ( 2nd ` r ) x ) e. i /\
                            ( x ( 2nd ` r ) z ) e. i ) ) ) } ) $.
  $}

  ${
    $d r i a b x y $.
    $( Obsolete defintion, use ~ df-prmidl instead.  Define the class of prime
       ideals of a ring ` R ` .  A proper ideal ` I ` of ` R ` is prime if
       whenever ` A B C_ I ` for ideals ` A ` and ` B ` , either ` A C_ I ` or
       ` B C_ I ` .  The more familiar definition using elements rather than
       ideals is equivalent provided ` R ` is commutative; see ~ ispridl2 and
       ~ ispridlc .  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (New usage is discouraged.) $)
    df-pridl $a |- PrIdl = ( r e. RingOps |->
        { i e. ( Idl ` r ) | ( i =/= ran ( 1st ` r ) /\ A. a e. ( Idl ` r )
          A. b e. ( Idl ` r ) ( A. x e. a A. y e. b ( x ( 2nd ` r ) y ) e. i ->
                                      ( a C_ i \/ b C_ i ) ) ) } ) $.
  $}

  ${
    $d r i j $.
    $( Obsolete defintion, use ~ df-mxidl instead.  Define the class of maximal
       ideals of a ring ` R ` .  A proper ideal is called maximal if it is
       maximal with respect to inclusion among proper ideals.  (Contributed by
       Jeff Madsen, 5-Jan-2011.)  (New usage is discouraged.) $)
    df-maxidl $a |- MaxIdl = ( r e. RingOps |->
            { i e. ( Idl ` r ) | ( i =/= ran ( 1st ` r ) /\ A. j e. ( Idl ` r )
                      ( i C_ j -> ( j = i \/ j = ran ( 1st ` r ) ) ) ) } ) $.
  $}

  ${
    $d R r x y z i $.  $d X r z i $.  $d I x y z i $.  $d Z r i $.  $d G r i $.
    $d H r i $.
    idlval.1 $e |- G = ( 1st ` R ) $.
    idlval.2 $e |- H = ( 2nd ` R ) $.
    idlval.3 $e |- X = ran G $.
    idlval.4 $e |- Z = ( GId ` G ) $.
    $( Obsolete theorem, use ~ 2idlval instead.  The class of ideals of a ring.
       (Contributed by Jeff Madsen, 10-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    idlval $p |- ( R e. RingOps -> ( Idl ` R ) = { i e. ~P X | ( Z e. i /\
                                A. x e. i ( A. y e. i ( x G y ) e. i /\
                      A. z e. X ( ( z H x ) e. i /\ ( x H z ) e. i ) ) ) } ) $=
      ( cv c1st cfv wcel co wral wa cgi c2nd crn cpw crab crngo cidl wceq fveq2
      vr eqtr4di rneqd fveq2d eleq1d ralbidv anbi12d raleqbidv rabeqbidv df-idl
      pweqd oveqd cvv fvexi rnex eqeltri pwex rabex fvmpt ) UJDUJNZOPZUAPZENZQZ
      ANZBNZVJRZVLQZBVLSZCNZVNVIUBPZRZVLQZVNVSVTRZVLQZTZCVJUCZSZTZAVLSZTZEWFUDZ
      UEIVLQZVNVOFRZVLQZBVLSZVSVNGRZVLQZVNVSGRZVLQZTZCHSZTZAVLSZTZEHUDZUEUFUGVI
      DUHZWJXDEWKXEXFWFHXFWFFUCZHXFVJFXFVJDOPFVIDOUIJUKZULLUKZUTXFVMWLWIXCXFVKI
      VLXFVKFUAPIXFVJFUAXHUMMUKUNXFWHXBAVLXFVRWOWGXAXFVQWNBVLXFVPWMVLXFVJFVNVOX
      HVAUNUOXFWEWTCWFHXIXFWBWQWDWSXFWAWPVLXFVTGVSVNXFVTDUBPGVIDUBUIKUKZVAUNXFW
      CWRVLXFVTGVNVSXJVAUNUPUQUPUOUPURABCEUJUSXDEXEHHXGVBLFFDOJVCVDVEVFVGVH $.

    $( Obsolete theorem, use ~ df2idl2 instead.  The predicate "is an ideal of
       the ring ` R ` ".  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    isidl $p |- ( R e. RingOps -> ( I e. ( Idl ` R ) <-> ( I C_ X /\ Z e. I /\
                                A. x e. I ( A. y e. I ( x G y ) e. I /\
                      A. z e. X ( ( z H x ) e. I /\ ( x H z ) e. I ) ) ) ) ) $=
      ( vi wcel cv co wral wa eleq2 cidl cfv cpw crab wss w3a idlval eleq2d crn
      crngo cvv c1st fvexi rnex eqeltri elpw2 anbi1i raleqbi1dv anbi12d ralbidv
      wceq elrab 3anass 3bitr4i bitrdi ) DUJOZGDUAUBZOGINPZOZAPZBPEQZVHOZBVHRZC
      PZVJFQZVHOZVJVNFQZVHOZSZCHRZSZAVHRZSZNHUCZUDZOZGHUEZIGOZVKGOZBGRZVOGOZVQG
      OZSZCHRZSZAGRZUFZVFVGWEGABCDNEFHIJKLMUGUHGWDOZWHWPSZSWGWSSWFWQWRWGWSGHHEU
      IUKLEEDULJUMUNUOUPUQWCWSNGWDVHGVAZVIWHWBWPVHGITWAWOAVHGWTVMWJVTWNVLWIBVHG
      VHGVKTURWTVSWMCHWTVPWKVRWLVHGVOTVHGVQTUSUTUSURUSVBWGWHWPVCVDVE $.

    $d X x $.
    $( Obsolete theorem, use ~ df2idl2crng instead.  The predicate "is an ideal
       of the commutative ring ` R ` ".  (Contributed by Jeff Madsen,
       10-Jun-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    isidlc $p |- ( R e. CRingOps -> ( I e. ( Idl ` R ) <-> ( I C_ X /\ Z e. I
        /\
                                A. x e. I ( A. y e. I ( x G y ) e. I /\
                                    A. z e. X ( z H x ) e. I ) ) ) ) $=
      ( wcel cv co wral wa w3a wb ccring cidl cfv wss crngo crngorngo isidl syl
      ssel2 crngocom eleq1d biimprd 3expa pm4.71d bicomd ralbidva anbi2d sylan2
      wi anassrs adantrr pm5.32da df-3an 3bitr4g bitrd ) DUANZGDUBUCNZGHUDZIGNZ
      AOZBOEPGNBGQZCOZVJFPZGNZVJVLFPZGNZRZCHQZRZAGQZSZVHVIVKVNCHQZRZAGQZSZVFDUE
      NVGWATDUFABCDEFGHIJKLMUGUHVFVHVIRZVTRWFWDRWAWEVFWFVTWDVFVHVTWDTVIVFVHRVSW
      CAGVFVHVJGNZVSWCTZVHWGRVFVJHNZWHGHVJUIVFWIRZVRWBVKWJVQVNCHWJVLHNZRZVNVQWL
      VNVPVFWIWKVNVPUSVFWIWKSZVPVNWMVOVMGVJVLDEFHJKLUJUKULUMUNUOUPUQURUTUPVAVBV
      HVIVTVCVHVIWDVCVDVE $.
  $}

  ${
    $d R x y z $.  $d I x y z $.  $d X z $.
    idlss.1 $e |- G = ( 1st ` R ) $.
    idlss.2 $e |- X = ran G $.
    $( Obsolete theorem, use ~ 2idlss instead.  An ideal of ` R ` is a subset
       of ` R ` .  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    idlss $p |- ( ( R e. RingOps /\ I e. ( Idl ` R ) ) -> I C_ X ) $=
      ( vx vy vz crngo wcel cidl cfv wa wss cgi cv co wral eqid c2nd w3a biimpa
      isidl simp1d ) AJKZCALMKZNCDOZBPMZCKZGQZHQBRCKHCSIQZUKAUAMZRCKUKULUMRCKNI
      DSNGCSZUFUGUHUJUNUBGHIABUMCDUIEUMTFUITUDUCUE $.

    $( Obsolete theorem, use ~ 2idllidld and ~ lidlbasel instead.  An element
       of an ideal is an element of the ring.  (Contributed by Jeff Madsen,
       19-Jun-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    idlcl $p |- ( ( ( R e. RingOps /\ I e. ( Idl ` R ) )
                                      /\ A e. I ) -> A e. X ) $=
      ( crngo wcel cidl cfv wa idlss sselda ) BHIDBJKILDEABCDEFGMN $.
  $}

  ${
    $d R x y z $.  $d I x y z $.  $d G z $.
    idl0cl.1 $e |- G = ( 1st ` R ) $.
    idl0cl.2 $e |- Z = ( GId ` G ) $.
    $( Obsolete theorem, use ~ ringrng and ~ rng2idl0 instead.  An ideal
       contains ` 0 ` .  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    idl0cl $p |- ( ( R e. RingOps /\ I e. ( Idl ` R ) ) -> Z e. I ) $=
      ( vx vy vz crngo wcel cidl cfv wa crn wss cv co wral eqid c2nd w3a biimpa
      isidl simp2d ) AJKZCALMKZNCBOZPZDCKZGQZHQBRCKHCSIQZUKAUAMZRCKUKULUMRCKNIU
      HSNGCSZUFUGUIUJUNUBGHIABUMCUHDEUMTUHTFUDUCUE $.
  $}

  ${
    $d R x y z $.  $d I x y z $.  $d G x y z $.  $d A x y $.  $d B y $.
    idladdcl.1 $e |- G = ( 1st ` R ) $.
    $( Obsolete theorem, use ~ 2idllidld and ~ lidlacl instead.  An ideal is
       closed under addition.  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    idladdcl $p |- ( ( ( R e. RingOps /\ I e. ( Idl ` R ) )
                              /\ ( A e. I /\ B e. I ) ) -> ( A G B ) e. I ) $=
      ( vx vy vz crngo wcel cidl cfv wa cv co wral eqid wceq eleq1d crn wss cgi
      c2nd w3a isidl biimpa simp3d simpl ralimi syl oveq1 oveq2 rspc2v mpan9 )
      CJKZECLMKZNZGOZHOZDPZEKZHEQZGEQZAEKBEKNABDPZEKZURVCIOZUSCUDMZPEKUSVGVHPEK
      NIDUAZQZNZGEQZVDUREVIUBZDUCMZEKZVLUPUQVMVOVLUEGHICDVHEVIVNFVHRVIRVNRUFUGU
      HVKVCGEVCVJUIUJUKVBVFAUTDPZEKGHABEEUSASVAVPEUSAUTDULTUTBSVPVEEUTBADUMTUNU
      O $.
  $}

  ${
    $d R x y z $.  $d I x y z $.  $d X x z $.  $d H x z $.  $d A x z $.
    $d B z $.
    idllmulcl.1 $e |- G = ( 1st ` R ) $.
    idllmulcl.2 $e |- H = ( 2nd ` R ) $.
    idllmulcl.3 $e |- X = ran G $.
    $( Obsolete theorem, use ~ 2idllidld and ~ lidlmcl instead.  An ideal is
       closed under multiplication on the left.  (Contributed by Jeff Madsen,
       10-Jun-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    idllmulcl $p |- ( ( ( R e. RingOps /\ I e. ( Idl ` R ) )
                              /\ ( A e. I /\ B e. X ) ) -> ( B H A ) e. I ) $=
      ( vz vx vy wcel cfv wa cv co wral ralimi crngo cidl wss eqid isidl biimpa
      cgi w3a simp3d simpl adantl syl wceq oveq2 eleq1d oveq1 rspc2v mpan9 ) CU
      ANZFCUBONZPZKQZLQZERZFNZKGSZLFSZAFNBGNPBAERZFNZVAVCMQDRFNMFSZVEVCVBERFNZP
      ZKGSZPZLFSZVGVAFGUCZDUGOZFNZVOUSUTVPVRVOUHLMKCDEFGVQHIJVQUDUEUFUIVNVFLFVM
      VFVJVLVEKGVEVKUJTUKTULVEVIVBAERZFNLKABFGVCAUMVDVSFVCAVBEUNUOVBBUMVSVHFVBB
      AEUPUOUQUR $.

    $( Obsolete theorem, use ~ 2idlridld and ~ lidlmcl instead.  An ideal is
       closed under multiplication on the right.  (Contributed by Jeff Madsen,
       10-Jun-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    idlrmulcl $p |- ( ( ( R e. RingOps /\ I e. ( Idl ` R ) )
                              /\ ( A e. I /\ B e. X ) ) -> ( A H B ) e. I ) $=
      ( vx vz vy wcel cfv wa cv co wral ralimi crngo cidl wss eqid isidl biimpa
      cgi w3a simp3d simpr adantl syl wceq oveq1 eleq1d oveq2 rspc2v mpan9 ) CU
      ANZFCUBONZPZKQZLQZERZFNZLGSZKFSZAFNBGNPABERZFNZVAVBMQDRFNMFSZVCVBERFNZVEP
      ZLGSZPZKFSZVGVAFGUCZDUGOZFNZVOUSUTVPVRVOUHKMLCDEFGVQHIJVQUDUEUFUIVNVFKFVM
      VFVJVLVELGVKVEUJTUKTULVEVIAVCERZFNKLABFGVBAUMVDVSFVBAVCEUNUOVCBUMVSVHFVCB
      AEUPUOUQUR $.
  $}

  ${
    idlnegcl.1 $e |- G = ( 1st ` R ) $.
    idlnegcl.2 $e |- N = ( inv ` G ) $.
    $( Obsolete theorem, use ~ 2idllidld and ~ lidlnegcl instead.  An ideal is
       closed under negation.  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    idlnegcl $p |- ( ( ( R e. RingOps /\ I e. ( Idl ` R ) )
                                          /\ A e. I ) -> ( N ` A ) e. I ) $=
      ( crngo wcel cidl cfv wa c2nd cgi co crn wss eqid anassrs mpdan wceq c1st
      idlss ssel2 rngonegmn1l sylan2 syldanl rneqi rngonegcl ad2antrr idllmulcl
      rngo1cl eqeltrd ) BHIZDBJKIZLZADIZLZAEKZBMKZNKZEKZAUTOZDUNUODCPZQZUQUSVCU
      AZBCDVDFVDRZUCUNVEUQVFVEUQLUNAVDIVFDVDAUDABVACUTEVDFUTRZVGGVARZUEUFSUGURV
      BVDIZVCDIZUNVJUOUQUNVAVDIVJBVAUTVDCBUBKFUHVHVIULVABCEVDFVGGUITUJUPUQVJVKA
      VBBCUTDVDFVHVGUKSTUM $.
  $}

  ${
    idlsubcl.1 $e |- G = ( 1st ` R ) $.
    idlsubcl.2 $e |- D = ( /g ` G ) $.
    $( Obsolete theorem, use ~ 2idllidld and ~ lidlsubcl instead.  An ideal is
       closed under subtraction.  (Contributed by Jeff Madsen, 19-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    idlsubcl $p |- ( ( ( R e. RingOps /\ I e. ( Idl ` R ) )
                              /\ ( A e. I /\ B e. I ) ) -> ( A D B ) e. I ) $=
      ( crngo wcel cidl cfv wa co cgn crn wceq eqid idlcl syldan rngosub simprl
      anim12dan 3expb adantlr idlnegcl adantrl jca idladdcl eqeltrd ) DIJZFDKLJ
      ZMZAFJZBFJZMZMZABCNZABEOLZLZENZFUMUPAEPZJZBVBJZMZURVAQZUMUNVCUOVDADEFVBGV
      BRZSBDEFVBGVGSUCUKVEVFULUKVCVDVFABCDEUSVBGVGUSRZHUAUDUETUMUPUNUTFJZMVAFJU
      QUNVIUMUNUOUBUMUOVIUNBDEFUSGVHUFUGUHAUTDEFGUITUJ $.
  $}

  ${
    $d R x y z $.  $d X x y z $.
    rngidl.1 $e |- G = ( 1st ` R ) $.
    rngidl.2 $e |- X = ran G $.
    $( Obsolete theorem, use ~ 2idl1 instead.  A ring ` R ` is an ` R ` ideal.
       (Contributed by Jeff Madsen, 10-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rngoidl $p |- ( R e. RingOps -> X e. ( Idl ` R ) ) $=
      ( vx vy vz crngo wcel cfv cv co wral wa eqid 3expa ralrimiva rngocl jca
      cidl wss cgi c2nd ssidd rngo0cl rngogcl w3a 3com23 isidl mpbir3and ) AIJZ
      CAUAKJCCUBBUCKZCJFLZGLZBMCJZGCNZHLZUNAUDKZMCJZUNURUSMCJZOZHCNZOZFCNULCUEA
      BCUMDEUMPZUFULVDFCULUNCJZOZUQVCVGUPGCULVFUOCJUPUNUOABCDEUGQRVGVBHCULVFURC
      JZVBULVFVHUHUTVAULVHVFUTURUNABUSCDUSPZESUIUNURABUSCDVIESTQRTRFGHABUSCCUMD
      VIEVEUJUK $.
  $}

  ${
    $d R x y z $.  $d Z x y z $.  $d G z $.
    0idl.1 $e |- G = ( 1st ` R ) $.
    0idl.2 $e |- Z = ( GId ` G ) $.
    $( Obsolete theorem, use ~ 2idl0 instead.  The set containing only ` 0 ` is
       an ideal.  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    0idl $p |- ( R e. RingOps -> { Z } e. ( Idl ` R ) ) $=
      ( vx vy vz wcel cfv cv co wral wa eqid wceq ovex elsn sylibr eleq1d crngo
      csn cidl crn wss c2nd rngo0cl snssd fvexi snid velsn rngo0rid mpdan oveq2
      cgi a1i syl5ibrcom biimtrid ralrimiv rngorz jca ralrimiva ralbidv anbi12d
      rngolz oveq1 isidl mpbir3and ) AUAIZCUBZAUCJIVJBUDZUECVJIZFKZGKZBLZVJIZGV
      JMZHKZVMAUFJZLZVJIZVMVRVSLZVJIZNZHVKMZNZFVJMVICVKABVKCDVKOZEUGZUHVLVICCBU
      OEUIUJUPVIWFFVJVMVJIVMCPZVIWFFCUKVIWFWICVNBLZVJIZGVJMZVRCVSLZVJIZCVRVSLZV
      JIZNZHVKMZNVIWLWRVIWKGVJVNVJIVNCPZVIWKGCUKVIWKWSCCBLZVJIZVIWTCPZXAVICVKIX
      BWHCABVKCDWGEULUMWTCCCBQRSWSWJWTVJVNCCBUNTUQURUSVIWQHVKVIVRVKINZWNWPXCWMC
      PWNVRABVSVKCEWGDVSOZUTWMCVRCVSQRSXCWOCPWPVRABVSVKCEWGDXDVEWOCCVRVSQRSVAVB
      VAWIVQWLWEWRWIVPWKGVJWIVOWJVJVMCVNBVFTVCWIWDWQHVKWIWAWNWCWPWIVTWMVJVMCVRV
      SUNTWIWBWOVJVMCVRVSVFTVDVCVDUQURUSFGHABVSVJVKCDXDWGEVGVH $.
  $}

  ${
    $d R x $.  $d X x $.  $d I x $.  $d U x $.
    1idl.1 $e |- G = ( 1st ` R ) $.
    1idl.2 $e |- H = ( 2nd ` R ) $.
    1idl.3 $e |- X = ran G $.
    1idl.4 $e |- U = ( GId ` H ) $.
    $( Obsolete theorem, use ~ 2idl1el instead.  Two ways of expressing the
       unit ideal.  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    1idl $p |- ( ( R e. RingOps /\ I e. ( Idl ` R ) )
           -> ( U e. I <-> I = X ) ) $=
      ( vx crngo wcel cidl cfv wa wceq wss adantr crn idlss cv c1st rneqi eqtri
      rngolidm ad2ant2rl idlrmulcl eqeltrrd expr ssrdv eqssd rngo1cl syl5ibrcom
      co ex eleq2 impbid ) ALMZEANOMZPZBEMZEFQZVAVBVCVAVBPZEFVAEFRVBACEFGIUASVD
      KFEVAVBKUBZFMZVEEMVAVBVFPPBVEDUOZVEEUSVFVGVEQUTVBVEABDFHFCTAUCOZTICVHGUDU
      EZJUFUGBVEACDEFGHIUHUIUJUKULUPVAVBVCBFMZUSVJUTABDFVIHJUMSEFBUQUNUR $.
  $}

  ${
    0ring.1 $e |- G = ( 1st ` R ) $.
    0ring.2 $e |- H = ( 2nd ` R ) $.
    0ring.3 $e |- X = ran G $.
    0ring.4 $e |- Z = ( GId ` G ) $.
    0ring.5 $e |- U = ( GId ` H ) $.
    $( Obsolete theorem, use ~ 0ring01eqbi2 instead.  In a ring, ` 0 = 1 ` iff
       the ring contains only ` 0 ` .  (Contributed by Jeff Madsen,
       6-Jan-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    0rngo $p |- ( R e. RingOps -> ( Z = U <-> X = { Z } ) ) $=
      ( crngo wcel wceq csn cgi fvexi snid cfv crn eleq1 mpbii cidl wb imbitrid
      0idl mpdan eqcom imbitrdi rneqi eqtri rngo1cl eleq2 elsni eqcomd biimtrdi
      1idl c1st syl5com impbid ) ALMZFBNZEFOZNZVAVBVCENZVDVBBVCMZVAVEVBFVCMVFFF
      CPJQRFBVCUAUBVAVCAUCSMVFVEUDACFGJUFABCDVCEGHIKUQUGUEVCEUHUIVABEMZVDVBABDE
      ECTAURSZTICVHGUJUKHKULVDVGVFVBEVCBUMVFBFBFUNUOUPUSUT $.
  $}

  ${
    $d R i x y z $.  $d H i x y z $.  $d X i x y z $.  $d Z i x y z $.
    divrngidl.1 $e |- G = ( 1st ` R ) $.
    divrngidl.2 $e |- H = ( 2nd ` R ) $.
    divrngidl.3 $e |- X = ran G $.
    divrngidl.4 $e |- Z = ( GId ` G ) $.
    $( Obsolete theorem, use ~ drngnidl instead.  The only ideals in a division
       ring are the zero ideal and the unit ideal.  (Contributed by Jeff
       Madsen, 10-Jun-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    divrngidl $p |- ( R e. DivRingOps -> ( Idl ` R ) = { { Z } , X } ) $=
      ( vy vx vi vz wcel wne cv wceq wa wi adantr cdrng crngo cgi cfv cdif wrex
      co csn wral cidl cpr eqid isdrngo2 wo idl0cl wex wss fvexi necom pssdifn0
      snss c0 sylib syl2anb idlss ssdif sselda sylan oveq2 eqeq1d rspcva eldifi
      rexbidv anim12i idllmulcl 1idl biimpd eleq1 imbi1d syl5ibrcom mpid sylan2
      n0 anassrs rexlimdva imp syldan an32s exlimdv syl5 mpand neor sylibr 0idl
      ex rngoidl jaod impbid vex elpr bitr4di eqrdv adantrl sylbi ) AUANAUBNZCU
      CUDZEOZJPZKPZCUGZXFQZJDEUHZUEZUFZKXMUIZRRAUJUDZXLDUKZQZKJAXFBCDEFGIHXFULZ
      UMXEXOXRXGXEXORZLXPXQXTLPZXPNZYAXLQZYADQZUNZYAXQNXTYBYEXTYBYEXTYBRYAXLOZY
      DSZYEXEYBXOYGXEYBRZXORZEYANZYFYDYHYJXOABYAEFIUOTYJYFRMPZYAXLUEZNZMUPZYIYD
      YJXLYAUQZXLYAOZYNYFEYAEBUCIURVAYAXLUSYOYPRYLVBOYNXLYAUTMYLWCVCVDYIYMYDMYI
      YMYDYHYMXOYDYHYMRZXOXHYKCUGZXFQZJXMUFZYDYQYKXMNZXOYTYHYADUQZYMUUAABYADFHV
      EUUBYLXMYKYADXLVFVGVHXNYTKYKXMXIYKQZXKYSJXMUUCXJYRXFXIYKXHCVIVJVMVKVHYQYT
      YDYQYSYDJXMYHYMXHXMNZYSYDSZYMUUDRYHYKYANZXHDNZRZUUEYMUUFUUDUUGYKYAXLVLXHD
      XLVLVNYHUUHRZYSYRYANZYDYKXHABCYADFGHVOUUIUUJYDSYSXFYANZYDSZYHUULUUHYHUUKY
      DAXFBCYADFGHXSVPVQTYSUUJUUKYDYRXFYAVRVSVTWAWBWDWEWFWGWHWOWIWJWKWHYDYAXLWL
      WMWOXEYEYBSXOXEYCYBYDXEYBYCXLXPNABEFIWNYAXLXPVRVTXEYBYDDXPNABDFHWPYADXPVR
      VTWQTWRYAXLDLWSWTXAXBXCXD $.
  $}

  ${
    $d R i x y z $.  $d C i x y z $.
    $( Obsolete theorem, use ~ intlidl instead.  The intersection of a nonempty
       collection of ideals is an ideal.  (Contributed by Jeff Madsen,
       10-Jun-2010.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    intidl $p |- ( ( R e. RingOps /\ C =/= (/) /\ C C_ ( Idl ` R ) )
                                                  -> |^| C e. ( Idl ` R ) ) $=
      ( vx vy vz vi wcel cfv cv co wral wa eqid sylan2 anassrs ralrimiva sylibr
      wss elint2 ex crngo wne cidl w3a cint c1st crn cgi c2nd intssuni 3ad2ant2
      cuni ssel2 idlss 3adant2 unissb sstrd idl0cl vex r19.26 idladdcl ralimdva
      c0 fvex ovex imbitrrdi biimtrrid expdimp biimtrid ralrimiv anass1rs an32s
      wi idllmulcl an4s imp idlrmulcl jca wb isidl 3ad2ant1 mpbir3and ) BUAGZAV
      CUBZABUCHZRZUDZAUEZWEGZWHBUFHZUGZRZWJUHHZWHGZCIZDIZWJJZWHGZDWHKZEIZWOBUIH
      ZJZWHGZWOWTXAJZWHGZLZEWKKZLZCWHKZWGWHAULZWKWDWCWHXJRWFAUJUKWGFIZWKRZFAKZX
      JWKRWCWFXMWDWCWFLZXLFAWCWFXKAGZXLWFXOLZWCXKWEGZXLAWEXKUMZBWJXKWKWJMZWKMZU
      NNOPUOFAWKUPQUQWCWFWNWDXNWMXKGZFAKWNXNYAFAWCWFXOYAXPWCXQYAXRBWJXKWMXSWMMZ
      URNOPFWMAWJUHVDSQUOWCWFXIWDXNXHCWHWOWHGWOXKGZFAKZXNXHFWOACUSSXNYDXHXNYDLZ
      WSXGYEWRDWHWPWHGWPXKGZFAKZYEWRFWPADUSSXNYDYGWRYDYGLYCYFLZFAKZXNWRYCYFFAUT
      XNYIWQXKGZFAKWRXNYHYJFAWCWFXOYHYJVMZXPWCXQYKXRWCXQLZYHYJWOWPBWJXKXSVATNOV
      BFWQAWOWPWJVESVFVGVHVIVJYEXFEWKXNWTWKGZYDXFXNYMLZYDLZXCXEYOXBXKGZFAKZXCYN
      YDYQYNYCYPFAXNYMXOYCYPVMZWCYMWFXOYRXPWCYMLZXQYRXRWCXQYMYRYLYMLZYCYPYLYCYM
      YPWOWTBWJXAXKWKXSXAMZXTVNVKTVLNVOOVBVPFXBAWTWOXAVESQYOXDXKGZFAKZXEYNYDUUC
      YNYCUUBFAXNYMXOYCUUBVMZWCYMWFXOUUDXPYSXQUUDXRWCXQYMUUDYTYCUUBYLYCYMUUBWOW
      TBWJXAXKWKXSUUAXTVQVKTVLNVOOVBVPFXDAWOWTXAVESQVRVLPVRTVIVJUOWCWDWIWLWNXIU
      DVSWFCDEBWJXAWHWKWMXSUUAXTYBVTWAWB $.
  $}

  $( Obsolete theorem, use ~ inlidl instead.  The intersection of two ideals is
     an ideal.  (Contributed by Jeff Madsen, 16-Jun-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  inidl $p |- ( ( R e. RingOps /\ I e. ( Idl ` R ) /\ J e. ( Idl ` R ) )
                                        -> ( I i^i J ) e. ( Idl ` R ) ) $=
    ( crngo wcel cidl cfv w3a cpr cint cin wceq intprg 3adant1 wa wne wss prnzg
    c0 adantr prssi jca intidl 3expb sylan2 3impb eqeltrrd ) ADEZBAFGZEZCUIEZHB
    CIZJZBCKZUIUJUKUMUNLUHBCUIUIMNUHUJUKUMUIEZUJUKOZUHULSPZULUIQZOUOUPUQURUJUQU
    KBCUIRTBCUIUAUBUHUQURUOULAUCUDUEUFUG $.

  ${
    $d R i k x y z $.  $d C i j k x y z $.
    $( Obsolete theorem, use ~ unichnlidl instead.  The union of a nonempty
       chain of ideals is an ideal.  (Contributed by Jeff Madsen, 5-Jan-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    unichnidl $p |- ( ( R e. RingOps /\ ( C =/= (/) /\ C C_ ( Idl ` R ) /\
                              A. i e. C A. j e. C ( i C_ j \/ j C_ i ) ) )
                                          -> U. C e. ( Idl ` R ) ) $=
      ( vx vy vz vk wcel cfv wss cv wral wa eqid imp sylan2 wel wi an32s c0 wne
      crngo cidl wo w3a cuni c1st crn cgi co c2nd dfss3 idlss ex ralimdv unissb
      sylibr 3ad2antr2 wrex idl0cl r19.2z an12s eluni2 3adantr3 weq sseq1 sseq2
      sylan2b orbi12d ralbidv adantr ad2antlr ad2antrl adantll idladdcl ancom2s
      rspcv ssel2 ancoms expr an42s anasss simprl elunii syl2anc anassrs jaodan
      ad2antrr syldan rexlimdvaa biimtrid ralrimiv 3adantr1 exp43 com23 sylanl2
      idllmulcl imp41 simplrr idlrmulcl jca ralrimiva wb isidl mpbir3and ) BUCI
      ZAUAUBZABUDJZKZCLZDLZKZXLXKKZUEZDAMZCAMZUFZNZAUGZXIIZXTBUHJZUIZKZYBUJJZXT
      IZELZFLZYBUKZXTIZFXTMZGLZYGBULJZUKZXTIZYGYLYMUKZXTIZNZGYCMZNZEXTMZXGXHXJY
      DXQXGXJNZXKYCKZCAMZYDXJXGXKXIIZCAMZUUDCAXIUMZXGUUFUUDXGUUEUUCCAXGUUEUUCBY
      BXKYCYBOZYCOZUNUOUPPVICAYCUQURUSXGXHXJYFXQXGXHXJNNYEXKIZCAUTZYFXHXGXJUUKU
      UBXHUUJCAMZUUKXJXGUUFUULUUGXGUUFUULXGUUEUUJCAXGUUEUUJBYBXKYEUUHYEOZVAUOUP
      PVIUUJCAVBQVCCYEAVDURVEXSYTEXTYGXTIEHRZHAUTXSYTHYGAVDXSUUNYTHAXSHLZAIZUUN
      NZNYKYSXGUUQXRYKXGUUQNZXJXQYKXHUURXJXQYKUURXJNZXQUUOXLKZXLUUOKZUEZDAMZYKU
      USXQUVCUUQXQUVCSZXGXJUUPUVDUUNXPUVCCUUOACHVFZXOUVBDAUVEXMUUTXNUVAXKUUOXLV
      GXKUUOXLVHVJVKVRVLVMPUUSUVCNZYJFXTYHXTIFCRZCAUTUVFYJCYHAVDUVFUVGYJCAUUSXK
      AIZUVGNZUVCYJUUSUVINZUVCUUOXKKZXKUUOKZUEZYJUVJUVCUVMUVHUVCUVMSUUSUVGUVBUV
      MDXKADCVFUUTUVKUVAUVLXLXKUUOVHXLXKUUOVGVJVRVNPUVJUVKYJUVLUVJUVKYJUURXJUVI
      UVKYJSZXGXJUVINZUUQUVNXGUVONZUUQUVKYJUUQUVKNUVPECRZYJUUNUVKUVQUUPUVKUUNUV
      QUUOXKYGVSVTVOUVPUVQNYIXKIZUVHYJUVPUVQUVRXGXJUVIUVQUVRSZXGUVGXJUVHUVSXJUV
      HNXGUVGNUUEUVSAXIXKVSXGUUEUVGUVSXGUUENZUVGUVQUVRUVTUVQUVGUVRYGYHBYBXKUUHV
      PVQWATQWBWCPUVOUVHXGUVQXJUVHUVGWDVMYIXKAWEWFQWATWGPUUSUVIUVLYJUVIUVLNUUSF
      HRZYJUVGUVLUWAUVHUVLUVGUWAXKUUOYHVSVTVOUUSUWANYIUUOIZUUPYJUUSUWAUWBXGXJUU
      QUWAUWBSZXGUUNXJUUPUWCXJUUPNZXGUUNNZUUOXIIZUWCAXIUUOVSZXGUWFUUNUWCXGUWFNU
      UNUWAUWBYGYHBYBUUOUUHVPWATQWBTPUURUUPXJUWAXGUUPUUNWDWIYIUUOAWEWFQWGWHWJTW
      KWLWMWJWCWNTXGUUQXRYSUURXHXJYSXQXGXJUUQYSXGUUNXJUUPYSUWEUWDNZYRGYCUWHYLYC
      IZNZYOYQUWJYNUUOIZUUPYOUWDUWEUWFUWIUWKUWGXGUUNUWFUWIUWKXGUWFUUNUWIUWKSXGU
      WFUUNUWIUWKYGYLBYBYMUUOYCUUHYMOZUUIWRWOWPWSWQUWEXJUUPUWIWTZYNUUOAWEWFUWJY
      PUUOIZUUPYQUWDUWEUWFUWIUWNUWGXGUUNUWFUWIUWNXGUWFUUNUWIUWNSXGUWFUUNUWIUWNY
      GYLBYBYMUUOYCUUHUWLUUIXAWOWPWSWQUWMYPUUOAWEWFXBXCWBTUSTXBWKWLWMXGYAYDYFUU
      AUFXDXREFGBYBYMXTYCYEUUHUWLUUIUUMXEVLXF $.
  $}

  ${
    $d R x y z $.  $d S x y z $.  $d F x y z $.  $d Z x y z $.
    keridl.1 $e |- G = ( 1st ` S ) $.
    keridl.2 $e |- Z = ( GId ` G ) $.
    $( Obsolete theorem, use ~ ker2idl instead.  The kernel of a ring
       homomorphism is an ideal.  (Contributed by Jeff Madsen, 3-Jan-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    keridl $p |- ( ( R e. RingOps /\ S e. RingOps /\ F e. ( R RingOpsHom S ) )
                                      -> ( `' F " { Z } ) e. ( Idl ` R ) ) $=
      ( vx vy wcel co cfv wa eqid wceq fvex elsn wb elpreima 3syl vz crngo ccnv
      crngohom w3a csn cima cidl c1st crn wss wral c2nd cnvimass rngohomf fssdm
      cgi cv rngo0cl 3ad2ant1 sylibr wf wfn ffn mpbir2and an4 rngohomadd adantr
      rngohom0 oveq12 adantl rngogrpo grpoidcl grpolid syl2anc2 3ad2ant2 3eqtrd
      cgr ad2antrr ex anbi12i 3imtr4g imdistanda rngogcl 3expib anim1d biimtrid
      syld anbi12d 3imtr4d impl ralrimiva anbi2i rngocl 3expb anass1rs adantlrr
      wi 3ad2antl1 rngohommul oveq2 ad2antlr rngohomcl rngorz 3ad2antl2 adantlr
      syldan anassrs oveq1 rngolz jca sylbid imp isidl mpbir3and ) AUBJZBUBJZCA
      BUDKJZUEZCUCEUFZUGZAUHLJZYAAUILZUJZUKZYCUQLZYAJZHURZIURZYCKZYAJZIYAULZUAU
      RZYHAUMLZKZYAJZYHYMYNKZYAJZMZUAYDULZMZHYAULZXSYDDUJZYACCXTUNABCYCDYDUUCYC
      NZYDNZFUUCNZUOZUPXSYGYFYDJZYFCLZXTJZXPXQUUHXRAYCYDYFUUDUUEYFNZUSUTXSUUIEO
      UUJABCYCDEYFUUDUUKFGVIUUIEYFCPQVAXSYDUUCCVBZCYDVCZYGUUHUUJMRUUGYDUUCCVDZY
      DYFXTCSTVEXSUUAHYAXSYHYAJZMZYLYTUUPYKIYAXSUUOYIYAJZYKXSYHYDJZYHCLZXTJZMZY
      IYDJZYICLZXTJZMZMZYJYDJZYJCLZXTJZMZUUOUUQMYKUVFUURUVBMZUUTUVDMZMZXSUVJUUR
      UUTUVBUVDVFXSUVMUVKUVIMUVJXSUVKUVLUVIXSUVKMZUUSEOZUVCEOZMZUVHEOZUVLUVIUVN
      UVQUVRUVNUVQMUVHUUSUVCDKZEEDKZEUVNUVHUVSOUVQYHYIABCYCDYDUUDUUEFVGVHUVQUVS
      UVTOUVNUUSEUVCEDVJVKXSUVTEOZUVKUVQXQXPUWAXRXQDVRJEUUCJUWABDFVLEDUUCUUFGVM
      EEDUUCUUFGVNVOVPVSVQVTUUTUVOUVDUVPUUSEYHCPQZUVCEYICPQWAUVHEYJCPQWBWCXSUVK
      UVGUVIXPXQUVKUVGWRXRXPUURUVBUVGYHYIAYCYDUUDUUEWDWEUTWFWHWGXSUUOUVAUUQUVEX
      SUULUUMUUOUVARUUGUUNYDYHXTCSTZXSUULUUMUUQUVERUUGUUNYDYIXTCSTWIXSUULUUMYKU
      VJRUUGUUNYDYJXTCSTWJWKWLXSUUOYTXSUUOUVAYTUWCUVAUURUVOMZXSYTUUTUVOUURUWBWM
      XSUWDYTXSUWDMZYSUAYDUWEYMYDJZMZYPYRUWGYPYOYDJZYOCLZXTJZXSUURUWFUWHUVOXSUW
      FUURUWHXPXQUWFUURMUWHXRXPUWFUURUWHYMYHAYCYNYDUUDYNNZUUEWNWOWSWPWQUWGUWIEO
      UWJUWGUWIYMCLZUUSBUMLZKZUWLEUWMKZEXSUURUWFUWIUWNOZUVOXSUWFUURUWPYMYHABCYC
      YNUWMYDUUDUUEUWKUWMNZWTWPWQUWDUWNUWOOZXSUWFUVOUWRUURUUSEUWLUWMXAVKXBXSUWF
      UWOEOZUWDXSUWFUWLUUCJZUWSYMABCYCDYDUUCUUDUUEFUUFXCZXQXPUWTUWSXRUWLBDUWMUU
      CEGUUFFUWQXDXEXGXFVQUWIEYOCPQVAXSYPUWHUWJMRZUWDUWFXSUULUUMUXBUUGUUNYDYOXT
      CSTVSVEUWGYRYQYDJZYQCLZXTJZXSUURUWFUXCUVOXSUURUWFUXCXPXQUURUWFMUXCXRXPUUR
      UWFUXCYHYMAYCYNYDUUDUWKUUEWNWOWSXHWQUWGUXDEOUXEUWGUXDUUSUWLUWMKZEUWLUWMKZ
      EXSUURUWFUXDUXFOZUVOXSUURUWFUXHYHYMABCYCYNUWMYDUUDUUEUWKUWQWTXHWQUWDUXFUX
      GOZXSUWFUVOUXIUURUUSEUWLUWMXIVKXBXSUWFUXGEOZUWDXSUWFUWTUXJUXAXQXPUWTUXJXR
      UWLBDUWMUUCEGUUFFUWQXJXEXGXFVQUXDEYQCPQVAXSYRUXCUXEMRZUWDUWFXSUULUUMUXKUU
      GUUNYDYQXTCSTVSVEXKWLVTWGXLXMXKWLXPXQYBYEYGUUBUERXRHIUAAYCYNYAYDYFUUDUWKU
      UEUUKXNUTXO $.
  $}

  ${
    $d R r i x y a b $.  $d X i r $.  $d H i r $.
    pridlval.1 $e |- G = ( 1st ` R ) $.
    pridlval.2 $e |- H = ( 2nd ` R ) $.
    pridlval.3 $e |- X = ran G $.
    $( Obsolete theorem, use ~ prmidlval instead.  The class of prime ideals of
       a ring ` R ` .  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    pridlval $p |- ( R e. RingOps -> ( PrIdl ` R ) = { i e. ( Idl ` R ) |
                ( i =/= X /\ A. a e. ( Idl ` R ) A. b e. ( Idl ` R ) (
          A. x e. a A. y e. b ( x H y ) e. i -> ( a C_ i \/ b C_ i ) ) ) } ) $=
      ( vr cv c1st cfv c2nd wral cidl fveq2 crn wne co wcel wo wi wa crab crngo
      wss cpridl wceq eqtr4di rneqd neeq2d oveqd eleq1d 2ralbidv imbi1d anbi12d
      raleqbidv rabeqbidv df-pridl fvex rabex fvmpt ) MCDNZMNZOPZUAZUBZANZBNZVH
      QPZUCZVGUDZBINZRAHNZRZVRVGUJVQVGUJUEZUFZIVHSPZRZHWBRZUGZDWBUHVGGUBZVLVMFU
      CZVGUDZBVQRAVRRZVTUFZICSPZRZHWKRZUGZDWKUHUIUKVHCULZWEWNDWBWKVHCSTZWOVKWFW
      DWMWOVJGVGWOVJEUAGWOVIEWOVICOPEVHCOTJUMUNLUMUOWOWCWLHWBWKWPWOWAWJIWBWKWPW
      OVSWIVTWOVPWHABVRVQWOVOWGVGWOVNFVLVMWOVNCQPFVHCQTKUMUPUQURUSVAVAUTVBABDMH
      IVCWNDWKCSVDVEVF $.

    $d P i x y a b $.
    $( Obsolete theorem, use ~ isprmidl instead.  The predicate "is a prime
       ideal".  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ispridl $p |- ( R e. RingOps -> ( P e. ( PrIdl ` R ) <-> ( P e. ( Idl ` R )
                /\ P =/= X /\ A. a e. ( Idl ` R ) A. b e. ( Idl ` R )
        ( A. x e. a A. y e. b ( x H y ) e. P -> ( a C_ P \/ b C_ P ) ) ) ) ) $=
      ( vi wcel cfv cv wne wral wss wa crngo cpridl co wo wi cidl crab pridlval
      w3a eleq2d wceq neeq1 eleq2 2ralbidv sseq2 orbi12d imbi12d anbi12d 3anass
      elrab bitr4i bitrdi ) DUANZCDUBOZNCMPZGQZAPBPFUCZVENZBIPZRAHPZRZVJVESZVIV
      ESZUDZUEZIDUFOZRHVPRZTZMVPUGZNZCVPNZCGQZVGCNZBVIRAVJRZVJCSZVICSZUDZUEZIVP
      RHVPRZUIZVCVDVSCABDMEFGHIJKLUHUJVTWAWBWITZTWJVRWKMCVPVECUKZVFWBVQWIVECGUL
      WLVOWHHIVPVPWLVKWDVNWGWLVHWCABVJVIVECVGUMUNWLVLWEVMWFVECVJUOVECVIUOUPUQUN
      URUTWAWBWIUSVAVB $.
  $}

  ${
    $d R x y a b $.  $d P x y a b $.
    $( Obsolete theorem, use ~ prmidlidl instead.  A prime ideal is an ideal.
       (Contributed by Jeff Madsen, 19-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    pridlidl $p |- ( ( R e. RingOps /\ P e. ( PrIdl ` R ) )
                                            -> P e. ( Idl ` R ) ) $=
      ( vx vy vb va crngo wcel cpridl cfv cidl c1st crn wne cv c2nd wral wss wa
      eqid co wo wi w3a ispridl 3anass bitrdi simprbda ) BGHZABIJHZABKJZHZABLJZ
      MZNZCODOBPJZUAAHDEOZQCFOZQURARUQARUBUCEUKQFUKQZSZUIUJULUOUSUDULUTSCDABUMU
      PUNFEUMTUPTUNTUEULUOUSUFUGUH $.
  $}

  ${
    $d R x y a b $.  $d P x y a b $.
    pridlnr.1 $e |- G = ( 1st ` R ) $.
    prdilnr.2 $e |- X = ran G $.
    $( Obsolete theorem, use ~ prmidlnr instead.  A prime ideal is a proper
       ideal.  (Contributed by Jeff Madsen, 19-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    pridlnr $p |- ( ( R e. RingOps /\ P e. ( PrIdl ` R ) ) -> P =/= X ) $=
      ( vx vy vb va crngo wcel cpridl cfv wne cidl cv wral wss wa c2nd co wo wi
      w3a eqid ispridl 3anan12 bitrdi simprbda ) BKLZABMNLZADOZABPNZLZGQHQBUANZ
      UBALHIQZRGJQZRURASUQASUCUDIUNRJUNRZTZUKULUOUMUSUEUMUTTGHABCUPDJIEUPUFFUGU
      OUMUSUHUIUJ $.
  $}

  ${
    $d R x y a b $.  $d P x y a b $.  $d A x a b $.  $d B x y a b $.
    $d H a b $.
    pridl.1 $e |- H = ( 2nd ` R ) $.
    $( Obsolete theorem, use ~ isprmidlc instead.  The main property of a prime
       ideal.  (Contributed by Jeff Madsen, 19-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    pridl $p |- ( ( ( R e. RingOps /\ P e. ( PrIdl ` R ) ) /\
                        ( A e. ( Idl ` R ) /\ B e. ( Idl ` R ) /\
            A. x e. A A. y e. B ( x H y ) e. P ) ) -> ( A C_ P \/ B C_ P ) ) $=
      ( vb va wcel cfv wa cv wral wss wo wi eqid wceq crngo cpridl cidl co c1st
      crn wne ispridl df-3an bitrdi simplbda raleq sseq1 orbi1d imbi12d ralbidv
      w3a orbi2d rspc2v syl5com expd 3imp2 ) FUAKZEFUBLKZMZCFUCLZKZDVFKZANBNGUD
      EKZBDOZACOZCEPZDEPZQZVEVGVHVKVNRZVEVIBINZOZAJNZOZVREPZVPEPZQZRZIVFOJVFOZV
      GVHMVOVCVDEVFKZEFUELZUFZUGZMZWDVCVDWEWHWDUQWIWDMABEFWFGWGJIWFSHWGSUHWEWHW
      DUIUJUKWCVOVQACOZVLWAQZRJICDVFVFVRCTZVSWJWBWKVQAVRCULWLVTVLWAVRCEUMUNUOVP
      DTZWJVKWKVNWMVQVJACVIBVPDULUPWMWAVMVLVPDEUMURUOUSUTVAVB $.
  $}

  ${
    $d R a b r s $.  $d P a b r s $.  $d X a b r s $.  $d H r s $.
    ispridl2.1 $e |- G = ( 1st ` R ) $.
    ispridl2.2 $e |- H = ( 2nd ` R ) $.
    ispridl2.3 $e |- X = ran G $.
    $( Obsolete theorem, use ~ prmidl2 instead.  A condition that shows an
       ideal is prime.  For commutative rings, this is often taken to be the
       definition.  See ~ ispridlc for the equivalence in the commutative case.
       (Contributed by Jeff Madsen, 19-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ispridl2 $p |- ( ( R e. RingOps /\ ( P e. ( Idl ` R ) /\ P =/= X /\
          A. a e. X A. b e. X ( ( a H b ) e. P -> ( a e. P \/ b e. P ) ) ) )
                              -> P e. ( PrIdl ` R ) ) $=
      ( vs vr wcel cv wo wi wral wss wa syl crngo cidl cfv wne w3a cpridl idlss
      ssralv adantrr ralimdv adantrl syld adantlr r19.26-2 pm3.35 2ralimi dfss3
      co 2ralor orbi12i sylbb2 sylbir expcom syl6 ralrimdvva ex adantrd 3imtr4g
      imdistand df-3an ispridl sylibrd imp ) BUAMZABUBUCZMZAEUDZFNZGNZDURAMZVRA
      MZVSAMZOZPZGEQZFEQZUEZABUFUCMZVNWGVPVQVTGKNZQFLNZQZWJARZWIARZOZPZKVOQLVOQ
      ZUEZWHVNVPVQSZWFSWRWPSWGWQVNWRWFWPVNVPWFWPPZVQVNVPWSVNVPSZWFWOLKVOVOWTWJV
      OMZWIVOMZSZSWFWDGWIQZFWJQZWOVNXCWFXEPVPVNXCSWFWEFWJQZXEVNXAWFXFPZXBVNXASW
      JERXGBCWJEHJUGWEFWJEUHTUIVNXBXFXEPZXAVNXBSWIERZXHBCWIEHJUGXIWEXDFWJWDGWIE
      UHUJTUKULUMWKXEWNWKXESVTWDSZGWIQFWJQZWNVTWDFGWJWIUNXKWCGWIQFWJQZWNXJWCFGW
      JWIVTWCUOUPXLWAFWJQZWBGWIQZOWNWAWBFGWJWIUSWLXMWMXNFWJAUQGWIAUQUTVATVBVCVD
      VEVFVGVIVPVQWFVJVPVQWPVJVHFGABCDELKHIJVKVLVM $.
  $}

  ${
    $d R i j r $.  $d X r $.
    maxidlval.1 $e |- G = ( 1st ` R ) $.
    maxidlval.2 $e |- X = ran G $.
    $( Obsolete theorem, use ~ mxidlval instead.  The set of maximal ideals of
       a ring.  (Contributed by Jeff Madsen, 5-Jan-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    maxidlval $p |- ( R e. RingOps -> ( MaxIdl ` R ) =
                              { i e. ( Idl ` R ) | ( i =/= X /\
                A. j e. ( Idl ` R ) ( i C_ j -> ( j = i \/ j = X ) ) ) } ) $=
      ( vr cv c1st cfv crn wne wceq wo wi cidl wral wa crab crngo cmaxidl fveq2
      wss eqtr4di rneqd neeq2d eqeq2d orbi2d imbi2d raleqbidv anbi12d rabeqbidv
      df-maxidl fvex rabex fvmpt ) HABIZHIZJKZLZMZURCIZUDZVCURNZVCVANZOZPZCUSQK
      ZRZSZBVITUREMZVDVEVCENZOZPZCAQKZRZSZBVPTUAUBUSANZVKVRBVIVPUSAQUCZVSVBVLVJ
      VQVSVAEURVSVADLEVSUTDVSUTAJKDUSAJUCFUEUFGUEZUGVSVHVOCVIVPVTVSVGVNVDVSVFVM
      VEVSVAEVCWAUHUIUJUKULUMBCHUNVRBVPAQUOUPUQ $.
  $}

  ${
    $d R i j $.  $d M i j $.  $d X i $.
    ismaxidl.1 $e |- G = ( 1st ` R ) $.
    ismaxidl.2 $e |- X = ran G $.
    $( Obsolete theorem, use ~ ismxidl instead.  The predicate "is a maximal
       ideal".  (Contributed by Jeff Madsen, 5-Jan-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ismaxidl $p |- ( R e. RingOps -> ( M e. ( MaxIdl ` R ) <->
                              ( M e. ( Idl ` R ) /\ M =/= X /\
                A. j e. ( Idl ` R ) ( M C_ j -> ( j = M \/ j = X ) ) ) ) ) $=
      ( vi crngo wcel cmaxidl cfv cv wne wss wceq wo wi wral wa cidl w3a eleq2d
      crab neeq1 sseq1 eqeq2 orbi1d imbi12d ralbidv anbi12d elrab 3anass bitr4i
      maxidlval bitrdi ) AIJZDAKLZJDHMZENZUSBMZOZVAUSPZVAEPZQZRZBAUALZSZTZHVGUD
      ZJZDVGJZDENZDVAOZVADPZVDQZRZBVGSZUBZUQURVJDAHBCEFGUOUCVKVLVMVRTZTVSVIVTHD
      VGUSDPZUTVMVHVRUSDEUEWAVFVQBVGWAVBVNVEVPUSDVAUFWAVCVOVDUSDVAUGUHUIUJUKULV
      LVMVRUMUNUP $.
  $}

  ${
    $d R j $.  $d M j $.
    $( Obsolete theorem, use ~ mxidlidl instead.  A maximal ideal is an ideal.
       (Contributed by Jeff Madsen, 5-Jan-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    maxidlidl $p |- ( ( R e. RingOps /\ M e. ( MaxIdl ` R ) )
                                                -> M e. ( Idl ` R ) ) $=
      ( vj crngo wcel cmaxidl cfv cidl c1st crn wne cv wss wceq wo wi wral eqid
      wa w3a ismaxidl 3anass bitrdi simprbda ) ADEZBAFGEZBAHGZEZBAIGZJZKZBCLZMU
      LBNULUJNOPCUGQZSZUEUFUHUKUMTUHUNSACUIBUJUIRUJRUAUHUKUMUBUCUD $.

    $d R j $.  $d M j $.
    maxidlnr.1 $e |- G = ( 1st ` R ) $.
    maxidlnr.2 $e |- X = ran G $.
    $( Obsolete theorem, use ~ mxidlnr instead.  A maximal ideal is proper.
       (Contributed by Jeff Madsen, 16-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    maxidlnr $p |- ( ( R e. RingOps /\ M e. ( MaxIdl ` R ) ) -> M =/= X ) $=
      ( vj crngo wcel cmaxidl cfv wa cidl wne cv wss wceq wo wi wral w3a biimpa
      ismaxidl simp2d ) AHIZCAJKIZLCAMKZIZCDNZCGOZPUJCQUJDQRSGUGTZUEUFUHUIUKUAA
      GBCDEFUCUBUD $.

    $d I j $.  $d X j $.
    $( Obsolete theorem, use ~ mxidlmax instead.  A maximal ideal is a maximal
       proper ideal.  (Contributed by Jeff Madsen, 16-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    maxidlmax $p |- ( ( ( R e. RingOps /\ M e. ( MaxIdl ` R ) ) /\
                ( I e. ( Idl ` R ) /\ M C_ I ) ) -> ( I = M \/ I = X ) ) $=
      ( vj crngo wcel cmaxidl cfv wa cidl wss wceq wo wi cv eqeq1 wral ismaxidl
      wne w3a biimpa simp3d sseq2 orbi12d imbi12d rspcva sylan2 ancoms impr ) A
      IJZDAKLJZMZCANLZJZDCOZCDPZCEPZQZURUPUSVBRZUPURDHSZOZVDDPZVDEPZQZRZHUQUAZV
      CUPDUQJZDEUCZVJUNUOVKVLVJUDAHBDEFGUBUEUFVIVCHCUQVDCPZVEUSVHVBVDCDUGVMVFUT
      VGVAVDCDTVDCETUHUIUJUKULUM $.
  $}

  ${
    maxidln1.1 $e |- H = ( 2nd ` R ) $.
    maxidln1.2 $e |- U = ( GId ` H ) $.
    $( Obsolete theorem, use ~ mxidln1 instead.  One is not contained in any
       maximal ideal.  (Contributed by Jeff Madsen, 17-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    maxidln1 $p |- ( ( R e. RingOps /\ M e. ( MaxIdl ` R ) ) -> -. U e. M ) $=
      ( crngo wcel cmaxidl cfv wa wn c1st crn wne eqid maxidlnr cidl maxidlidl
      wb 1idl necon3bbid syldan mpbird ) AGHZDAIJHZKBDHZLZDAMJZNZOZAUIDUJUIPZUJ
      PZQUEUFDARJHZUHUKTADSUEUNKUGDUJABUICDUJULEUMFUAUBUCUD $.
  $}

  ${
    maxidln0.1 $e |- G = ( 1st ` R ) $.
    maxidln0.2 $e |- H = ( 2nd ` R ) $.
    maxidln0.3 $e |- Z = ( GId ` G ) $.
    maxidln0.4 $e |- U = ( GId ` H ) $.
    $( Obsolete theorem, use ~ mxidlnzr instead.  A ring with a maximal ideal
       is not the zero ring.  (Contributed by Jeff Madsen, 17-Jun-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    maxidln0 $p |- ( ( R e. RingOps /\ M e. ( MaxIdl ` R ) ) -> U =/= Z ) $=
      ( crngo wcel cmaxidl cfv wa wn wceq cidl maxidlidl idl0cl syldan maxidln1
      nelneq syl2anc neqned necomd ) AKLZEAMNLZOZFBUIFBUIFELZBELPFBQPUGUHEARNLU
      JAESACEFGITUAABDEHJUBFBEUCUDUEUF $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Prime rings and integral domains
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c PrRing $.
  $c Dmn $.

  $( Extend class notation with the class of prime rings. $)
  cprrng $a class PrRing $.

  $( Extend class notation with the class of domains. $)
  cdmn $a class Dmn $.

  $( Obsolete definition, use ~ df-prmring instead.  Define the class of prime
     rings.  A ring is prime if the zero ideal is a prime ideal.  (Contributed
     by Jeff Madsen, 10-Jun-2010.)  (New usage is discouraged.) $)
  df-prrngo $a |- PrRing = { r e. RingOps |
                              { ( GId ` ( 1st ` r ) ) } e. ( PrIdl ` r ) } $.

  $( Obsolete definition, use ~ df-idom resp. ~ dfidom2 instead.  Define the
     class of (integral) domains.  A domain is a commutative prime ring.
     (Contributed by Jeff Madsen, 10-Jun-2010.)  (New usage is discouraged.) $)
  df-dmn $a |- Dmn = ( PrRing i^i Com2 ) $.

  ${
    $d R r $.  $d Z r $.
    isprrng.1 $e |- G = ( 1st ` R ) $.
    isprrng.2 $e |- Z = ( GId ` G ) $.
    $( Obsolete theorem, use ~ isprmrng instead.  The predicate "is a prime
       ring".  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    isprrngo $p |- ( R e. PrRing <-> ( R e. RingOps
                                        /\ { Z } e. ( PrIdl ` R ) ) ) $=
      ( vr cv c1st cfv cgi csn cpridl wcel crngo cprrng wceq fveq2 fveq2d sneqd
      eqtr4di eleq12d df-prrngo elrab2 ) FGZHIZJIZKZUDLIZMCKZALIZMFANOUDAPZUGUI
      UHUJUKUFCUKUFBJICUKUEBJUKUEAHIBUDAHQDTRETSUDALQUAFUBUC $.
  $}

  $( Obsolete theorem, use ~ prmrngring instead.  A prime ring is a ring.
     (Contributed by Jeff Madsen, 10-Jun-2010.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  prrngorngo $p |- ( R e. PrRing -> R e. RingOps ) $=
    ( cprrng wcel crngo c1st cfv cgi csn cpridl eqid isprrngo simplbi ) ABCADCA
    EFZGFZHAIFCAMNMJNJKL $.

  ${
    $d R i j x y $.  $d H x y $.  $d X i j x y $.  $d Z i j x y $.
    $d U i j x y $.
    smprngpr.1 $e |- G = ( 1st ` R ) $.
    smprngpr.2 $e |- H = ( 2nd ` R ) $.
    smprngpr.3 $e |- X = ran G $.
    smprngpr.4 $e |- Z = ( GId ` G ) $.
    smprngpr.5 $e |- U = ( GId ` H ) $.
    $( Obsolete theorem, use ~ smprngprmrng instead.  A simple ring (one whose
       only ideals are ` 0 ` and ` R ` ) is a prime ring.  (Contributed by Jeff
       Madsen, 6-Jan-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    smprngopr $p |- ( ( R e. RingOps /\ U =/= Z
          /\ ( Idl ` R ) = { { Z } , X } ) -> R e. PrRing ) $=
      ( vx vy vj vi wcel wceq wral wi wa wne cidl cfv csn cpr w3a cpridl cprrng
      crngo simp1 cv co wss 0idl 3ad2ant1 0rngo eqcom 3bitr4g necon3bid 3adant3
      wo biimpa cun df-pr eqeq2i eleq2 anbi12d elun velsn orbi12i bitri anbi12i
      wb bitrdi sylbi 3ad2ant3 eqimss orcd adantr a1d a1i olcd adantl wrex c1st
      wn crn rneqi eqtri rngo1cl rngolidm mpdan eleq1d fvexi necon3bbid biimpar
      cgi elsn oveq1 notbid oveq2 rspc2ev syl3anc rexnal2 sylib pm2.21d ralbidv
      raleq sylan9bb imbi1d syl5ibrcom ccased sylbid ralrimivv ispridl isprrngo
      mpbir3and sylanbrc ) AUIPZBFUAZAUBUCZFUDZEUEZQZUFZXSYBAUGUCPZAUHPXSXTYDUJ
      YEYFYBYAPZYBEUAZLUKZMUKZDULZYBPZMNUKZRZLOUKZRZYOYBUMZYMYBUMZVAZSZNYAROYAR
      ZXSXTYGYDACFGJUNUOXSXTYHYDXSXTYHXSBFYBEXSFBQEYBQBFQZYBEQABCDEFGHIJKUPBFUQ
      YBEUQURUSVBUTYEYTONYAYAYEYOYAPZYMYAPZTZYOYBQZYOEQZVAZYMYBQZYMEQZVAZTZYTYD
      XSUUEUULVMZXTYDYAYBUDZEUDZVCZQZUUMYCUUPYAYBEVDVEUUQUUEYOUUPPZYMUUPPZTUULU
      UQUUCUURUUDUUSYAUUPYOVFYAUUPYMVFVGUURUUHUUSUUKUURYOUUNPZYOUUOPZVAUUHYOUUN
      UUOVHUUTUUFUVAUUGOYBVIOEVIVJVKUUSYMUUNPZYMUUOPZVAUUKYMUUNUUOVHUVBUUIUVCUU
      JNYBVINEVIVJVKVLVNVOVPXSXTUULYTSYDXSXTTZUUFUUIUUGUUJYTUUFUUITZYTSUVDUVEYS
      YPUUFYSUUIUUFYQYRYOYBVQVRZVSVTWAUUGUUITZYTSUVDUVGYSYPUUIYSUUGUUIYRYQYMYBV
      QWBWCVTWAUUFUUJTZYTSUVDUVHYSYPUUFYSUUJUVFVSVTWAUVDYTUUGUUJTZYLMERZLERZYSS
      UVDUVKYSUVDYLWFZMEWDLEWDZUVKWFUVDBEPZUVNBBDULZYBPZWFZUVMXSUVNXTABDEECWGAW
      EUCZWGICUVRGWHWIZHKWJZVSZUWAXSUVQXTXSUVPBFXSUVPBYBPUUBXSUVOBYBXSUVNUVOBQU
      VTBABDEHUVSKWKWLWMBFBDWQKWNWRVNWOWPUVLUVQBYJDULZYBPZWFLMBBEEYIBQZYLUWCUWD
      YKUWBYBYIBYJDWSWMWTYJBQZUWCUVPUWEUWBUVOYBYJBBDXAWMWTXBXCYLLMEEXDXEXFUVIYP
      UVKYSUUGYPYNLERUUJUVKYNLYOEXHUUJYNUVJLEYLMYMEXHXGXIXJXKXLUTXMXNXSXTYFYGYH
      UUAUFVMYDLMYBACDEONGHIXOUOXQACFGJXPXR $.
  $}

  $( Obsolete theorem, use ~ drngprmrng instead.  A division ring is a prime
     ring.  (Contributed by Jeff Madsen, 6-Jan-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  divrngpr $p |- ( R e. DivRingOps -> R e. PrRing ) $=
    ( cdrng wcel crngo c2nd cfv cgi c1st wne cidl csn crn wceq cprrng cdif cres
    cpr cxp cgr eqid isdrngo1 simplbi dvrunz divrngidl smprngopr syl3anc ) ABCZ
    ADCZAEFZGFZAHFZGFZIAJFULKZUKLZQMANCUGUHUIUNUMOZUORPSCAUKUIUNULUKTZUITZULTZU
    NTZUAUBAUJUKUIUNULUPUQUSURUJTZUCAUKUIUNULUPUQUSURUDAUJUKUIUNULUPUQUSURUTUEU
    F $.

  $( Obsolete theorem, use ~ isidom2 instead.  The predicate "is a domain".
     (Contributed by Jeff Madsen, 10-Jun-2010.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  isdmn $p |- ( R e. Dmn <-> ( R e. PrRing /\ R e. Com2 ) ) $=
    ( cprrng ccm2 cdmn df-dmn elin2 ) ABCDEF $.

  $( Obsolete theorem, use ~ isidom2 instead.  The predicate "is a domain".
     (Contributed by Jeff Madsen, 10-Jun-2010.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  isdmn2 $p |- ( R e. Dmn <-> ( R e. PrRing /\ R e. CRingOps ) ) $=
    ( cdmn wcel cprrng ccm2 wa ccring isdmn crngo wb prrngorngo iscrngo pm5.32i
    baibr syl bitri ) ABCADCZAECZFQAGCZFAHQRSQAICZRSJAKSTRALNOMP $.

  $( Obsolete theorem, use ~ idomcringd instead.  A domain is a commutative
     ring.  (Contributed by Jeff Madsen, 6-Jan-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  dmncrng $p |- ( R e. Dmn -> R e. CRingOps ) $=
    ( cdmn wcel cprrng ccring isdmn2 simprbi ) ABCADCAECAFG $.

  $( Obsolete theorem, use ~ idomringd instead.  A domain is a ring.
     (Contributed by Jeff Madsen, 6-Jan-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  dmnrngo $p |- ( R e. Dmn -> R e. RingOps ) $=
    ( cdmn wcel ccring crngo dmncrng crngorngo syl ) ABCADCAECAFAGH $.

  $( Obsolete theorem, use ~ fldidom instead.  A field is a domain.
     (Contributed by Jeff Madsen, 10-Jun-2010.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  flddmn $p |- ( K e. Fld -> K e. Dmn ) $=
    ( cdrng wcel ccring cprrng cfld cdmn divrngpr anim1i isfld2 isdmn2 3imtr4i
    wa ) ABCZADCZMAECZOMAFCAGCNPOAHIAJAKL $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Ideal generators
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c IdlGen $.

  $( Extend class notation with the ideal generation function. $)
  cigen $a class IdlGen $.

  ${
    $d r s j $.
    $( Obsolete definition, use ~ df-rsp instead.  Define the ideal generated
       by a subset of a ring.  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (New usage is discouraged.) $)
    df-igen $a |- IdlGen = ( r e. RingOps , s e. ~P ran ( 1st ` r ) |->
                      |^| { j e. ( Idl ` r ) | s C_ j } ) $.
  $}

  ${
    $d R r s j $.  $d S r s j $.  $d X r s j $.
    igenval.1 $e |- G = ( 1st ` R ) $.
    igenval.2 $e |- X = ran G $.
    $( Obsolete theorem, use ~ rspvalint instead.  The ideal generated by a
       subset of a ring.  (Contributed by Jeff Madsen, 10-Jun-2010.)  (Proof
       shortened by Mario Carneiro, 20-Dec-2013.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    igenval $p |- ( ( R e. RingOps /\ S C_ X ) -> ( R IdlGen S ) =
                                        |^| { j e. ( Idl ` R ) | S C_ j } ) $=
      ( vr vs crngo wcel wss cv cidl cfv crab cint cvv wceq c1st cigen co wa c0
      wne wrex rngoidl sseq2 rspcev sylan rabn0 sylibr intex sylib cpw crn rnex
      fvexi eqeltri elpw2 simpl fveq2d wb sseq1 adantl rabeqbidv inteqd eqtr4di
      fveq2 rneqd pweqd df-igen ovmpox syl3an2br mpd3an3 ) AJKZBELZBCMZLZCANOZP
      ZQZRKZABUAUBWBSZVPVQUCZWAUDUEZWCWEVSCVTUFZWFVPEVTKVQWGADEFGUGVSVQCEVTVREB
      UHUIUJVSCVTUKULWAUMUNVQVPBEUOZKWCWDBEEDUPZRGDDATFURUQUSUTHIABJHMZTOZUPZUO
      IMZVRLZCWJNOZPZQWBUARWHWJASZWMBSZUCZWPWAWSWNVSCWOVTWSWJANWQWRVAVBWRWNVSVC
      WQWMBVRVDVEVFVGWQWLEWQWLWIEWQWKDWQWKATODWJATVIFVHVJGVHVKCIHVLVMVNVO $.

    $( Obsolete theorem, use ~ rspssid instead.  A set is a subset of the ideal
       it generates.  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    igenss $p |- ( ( R e. RingOps /\ S C_ X ) -> S C_ ( R IdlGen S ) ) $=
      ( vj crngo wcel wss wa cv cidl cfv crab cint cigen co ssintub igenval
      sseqtrrid ) AHIBDJKBGLJGAMNZOPBABQRGBUBSABGCDEFTUA $.

    $( Obsolete theorem, use ~ rspcl instead.  The ideal generated by a set is
       an ideal.  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    igenidl $p |- ( ( R e. RingOps /\ S C_ X ) ->
                              ( R IdlGen S ) e. ( Idl ` R ) ) $=
      ( vj crngo wcel wss wa cigen co cv cidl cfv crab cint igenval c0 wne wrex
      rngoidl sseq2 rspcev sylan sylibr ssrab2 intidl mp3an3 syldan eqeltrd
      rabn0 ) AHIZBDJZKZABLMBGNZJZGAOPZQZRZUSABGCDEFSUNUOUTTUAZVAUSIZUPURGUSUBZ
      VBUNDUSIUOVDACDEFUCURUOGDUSUQDBUDUEUFURGUSUMUGUNVBUTUSJVCURGUSUHUTAUIUJUK
      UL $.
  $}

  ${
    $d R j $.  $d S j $.  $d I j $.
    $( Obsolete theorem, use ~ rspssp instead.  The ideal generated by a set is
       the minimal ideal containing that set.  (Contributed by Jeff Madsen,
       10-Jun-2010.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    igenmin $p |- ( ( R e. RingOps /\ I e. ( Idl ` R ) /\ S C_ I )
                                              -> ( R IdlGen S ) C_ I ) $=
      ( vj crngo wcel cidl cfv wss w3a cigen co cv crab cint wceq c1st crn eqid
      idlss wa sstr ancoms igenval anassrs syldanl 3impa sseq2 intminss 3adant1
      sylan2 eqsstrd ) AEFZCAGHZFZBCIZJABKLZBDMZIZDUNNOZCUMUOUPUQUTPZUMUOCAQHZR
      ZIZUPVAAVBCVCVBSZVCSZTUMVDUPVAVDUPUAUMBVCIZVAUPVDVGBCVCUBUCABDVBVCVEVFUDU
      KUEUFUGUOUPUTCIUMUSUPDCUNURCBUHUIUJUL $.

    $( Obsolete theorem, use ~ rsp2idlid instead.  The ideal generated by an
       ideal is that ideal.  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    igenidl2 $p |- ( ( R e. RingOps /\ I e. ( Idl ` R ) )
                                          -> ( R IdlGen I ) = I ) $=
      ( vj crngo wcel cidl cfv wa cigen co cv wss crab cint c1st crn wceq idlss
      eqid igenval syldan intmin adantl eqtrd ) ADEZBAFGZEZHABIJZBCKLCUFMNZBUEU
      GBAOGZPZLUHUIQAUJBUKUJSZUKSZRABCUJUKULUMTUAUGUIBQUECBUFUBUCUD $.
  $}

  ${
    $d R i j $.  $d S i j $.  $d I j $.  $d X i $.
    igenval2.1 $e |- G = ( 1st ` R ) $.
    igenval2.2 $e |- X = ran G $.
    $( Obsolete theorem, use ~ rspprop instead.  The ideal generated by a
       subset of a ring.  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    igenval2 $p |- ( ( R e. RingOps /\ S C_ X ) -> ( ( R IdlGen S ) = I <->
                                  ( I e. ( Idl ` R ) /\ S C_ I /\
                          A. j e. ( Idl ` R ) ( S C_ j -> I C_ j ) ) ) ) $=
      ( vi wcel wss wa wceq cv wi wral w3a igenmin adantr sseq2 crngo cigen cfv
      co cidl igenidl igenss 3expia ralrimiva 3jca eleq1 sseq1 imbi2d 3anbi123d
      ralbidv syl5ibcom 3adant3r3 crab cint ssint ralrab sylbbr 3ad2ant3 adantl
      adantlr igenval sseqtrrd eqssd ex impbid ) AUAJZBFKZLZABUBUDZEMZEAUEUCZJZ
      BEKZBCNZKZEVSKZOZCVPPZQZVMVNVPJZBVNKZVTVNVSKZOZCVPPZQVOWDVMWEWFWIABDFGHUF
      ABDFGHUGVKWIVLVKWHCVPVKVSVPJVTWGABVSRUHUISUJVOWEVQWFVRWIWCVNEVPUKVNEBTVOW
      HWBCVPVOWGWAVTVNEVSULUMUOUNUPVMWDVOVMWDLZVNEVKWDVNEKZVLVKVQVRWKWCABERUQVE
      WJEBINZKZIVPURZUSZVNWDEWOKZVMWCVQWPVRWPWACWNPWCCEWNUTWMVTWACIVPWLVSBTVAVB
      VCVDVMVNWOMWDABIDFGHVFSVGVHVIVJ $.
  $}

  ${
    $d R j x y u v w r s $.  $d X j x y u v w r s $.  $d G x y r s $.
    $d H j x y u v w r s $.  $d A j x y u v w r s $.
    prnc.1 $e |- G = ( 1st ` R ) $.
    prnc.2 $e |- H = ( 2nd ` R ) $.
    prnc.3 $e |- X = ran G $.
    $( Obsolete theorem, use ~ rspsn0 instead (holds for arbitrary rings).  A
       principal ideal (an ideal generated by one element) in a commutative
       ring.  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    prnc $p |- ( ( R e. CRingOps /\ A e. X ) -> ( R IdlGen { A } ) =
                                  { x e. X | E. y e. X x = ( y H A ) } ) $=
      ( vv vw wcel wa co cv wceq wrex wral oveq1 vj vu vr ccring csn cigen crab
      vs cidl cfv wss wi w3a cgi crngo crngorngo ssrab2 a1i eqid rngo0cl adantr
      rngolz eqcomd rspceeqv syl2anc eqeq1 rexbidv elrab sylanbrc eqeq2d bitrdi
      cbvrexvw rngodir 3exp2 imp42 3expib imdistani rngocl 3expa mpan2 ad2antlr
      rngogcl sylan eqeltrrd an32s anassrs eleq1d syl5ibrcom rexlimdva biimtrid
      oveq2 adantld ralrimiv rngoass anass1rs ralrimiva ralbidv anbi12d 3jca wb
      jca isidlc mpbird simpr crn c1st rneqi eqtri rngo1cl rngolidm snssd snssg
      biimpar idllmulcl eleq1 rabss sylibr syl5 expdimp snssi igenval2 syl2an
      ex ) DUDMZCGMZNZDCUEZUFOAPZBPZCFOZQZBGRZAGUGZQZYMDUIUJZMZYGYMUKZYGUAPZUKZ
      YMYRUKZULZUAYOSZUMZYFYPYQUUBYFYPYMGUKZEUNUJZYMMZUBPZKPZEOZYMMZKYMSZLPZUUG
      FOZYMMZLGSZNZUBYMSZUMZYDDUOMZYEUURDUPZUUSYENZUUDUUFUUQUUDUVAYLAGUQURUVAUU
      EGMZUUEYJQZBGRZUUFUUSUVBYEDEGUUEHJUUEUSZUTVAZUVAUVBUUEUUECFOZQUVDUVFUVAUV
      GUUECDEFGUUEUVEJHIVBVCBUUEGYJUVGUUEYIUUECFTVDVEYLUVDAUUEGYHUUEQYKUVCBGYHU
      UEYJVFVGVHVIUVAUUPUBYMUUGYMMUUGGMZUUGUCPZCFOZQZUCGRZNUVAUUPYLUVLAUUGGYHUU
      GQZYLUUGYJQZBGRUVLUVMYKUVNBGYHUUGYJVFVGUVNUVKBUCGYIUVIQYJUVJUUGYIUVICFTVJ
      VLVKVHUVAUVLUUPUVHUVAUVKUUPUCGUVAUVIGMZNZUUPUVKUVJUUHEOZYMMZKYMSZUULUVJFO
      ZYMMZLGSZNUVPUVSUWBUVPUVRKYMUUHYMMUUHGMZUUHUHPZCFOZQZUHGRZNUVPUVRYLUWGAUU
      HGYHUUHQZYLUUHYJQZBGRUWGUWHYKUWIBGYHUUHYJVFVGUWIUWFBUHGYIUWDQYJUWEUUHYIUW
      DCFTVJVLVKVHUVPUWGUVRUWCUVPUWFUVRUHGUVPUWDGMZNUVRUWFUVJUWEEOZYMMZUVAUVOUW
      JUWLUUSUVOUWJNZYEUWLUUSUWMNZYENUVIUWDEOZCFOZUWKYMUUSUVOUWJYEUWPUWKQZUUSUV
      OUWJYEUWQUVIUWDCDEFGHIJVMVNVOUWNUUSUWOGMZNZYEUWPYMMZUUSUWMUWRUUSUVOUWJUWR
      UVIUWDDEGHJWBVPVQUWSYENUWPGMZUWPYJQZBGRZUWTUUSUWRYEUXAUWOCDEFGHIJVRVSUWRU
      XCUUSYEUWRUWPUWPQUXCUWPUSBUWOGYJUWPUWPYIUWOCFTVDVTWAYLUXCAUWPGYHUWPQYKUXB
      BGYHUWPYJVFVGVHVIWCWDWEWFUWFUVQUWKYMUUHUWEUVJEWKWGWHWIWLWJWMUVPUWALGUVAUU
      LGMZUVOUWAUVAUXDUVONZNUULUVIFOZCFOZUVTYMUUSUXEYEUXGUVTQZUUSUXDUVOYEUXHUUS
      UXDUVOYEUXHUULUVICDEFGHIJWNVNVOWEUUSUXEYEUXGYMMZUUSUXENUUSUXFGMZNZYEUXIUU
      SUXEUXJUUSUXDUVOUXJUULUVIDEFGHIJVRVPVQUXKYENUXGGMZUXGYJQZBGRZUXIUUSUXJYEU
      XLUXFCDEFGHIJVRVSUXJUXNUUSYEUXJUXGUXGQUXNUXGUSBUXFGYJUXGUXGYIUXFCFTVDVTWA
      YLUXNAUXGGYHUXGQYKUXMBGYHUXGYJVFVGVHVIWCWEWDWOWPXAUVKUUKUVSUUOUWBUVKUUJUV
      RKYMUVKUUIUVQYMUUGUVJUUHETWGWQUVKUUNUWALGUVKUUMUVTYMUUGUVJUULFWKWGWQWRWHW
      IWLWJWMWSWCYDYPUURWTYEUBKLDEFYMGUUEHIJUVEXBVAXCYFCYMYFYECYJQZBGRZCYMMYDYE
      XDYDUUSYEUXPUUTUVAFUNUJZGMZCUXQCFOZQUXPUUSUXRYEDUXQFGGEXEDXFUJZXEJEUXTHXG
      XHZIUXQUSZXIVAUVAUXSCCDUXQFGIUYAUYBXJVCBUXQGYJUXSCYIUXQCFTVDVEWCYLUXPACGY
      HCQYKUXOBGYHCYJVFVGVHVIXKYDUUSYEUUBUUTUVAUUAUAYOUUSYRYOMZYEUUAUUSUYCNZYEY
      SYTYEYSNCYRMZUYDYTYEUYEYSCYRGXLXMUYDUYEYTUYDUYENZYLYHYRMZULZAGSYTUYFUYHAG
      UYFUYHYHGMUYFYKUYGBGUYFYIGMZNUYGYKYJYRMZUYDUYEUYIUYJCYIDEFYRGHIJXNWFYHYJY
      RXOWHWIVAWPYLAGYRXPXQYCXRXSWEWPWCWSYDUUSYGGUKYNUUCWTYEUUTCGXTDYGUAEYMGHJY
      AYBXC $.
  $}

  ${
    $d K x y z $.  $d X x y z $.  $d G y z $.  $d H x y z $.  $d U x y z $.
    $d Z x y $.
    isfldidl.1 $e |- G = ( 1st ` K ) $.
    isfldidl.2 $e |- H = ( 2nd ` K ) $.
    isfldidl.3 $e |- X = ran G $.
    isfldidl.4 $e |- Z = ( GId ` G ) $.
    isfldidl.5 $e |- U = ( GId ` H ) $.
    $( Obsolete theorem, use ~ isfieldidl instead.  Determine if a ring is a
       field based on its ideals.  (Contributed by Jeff Madsen, 10-Jun-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    isfldidl $p |- ( K e. Fld <-> ( K e. CRingOps /\
                                U =/= Z /\ ( Idl ` K ) = { { Z } , X } ) ) $=
      ( vy vx vz wcel wceq syl cv wrex wa cfld ccring wne cidl cfv csn fldcrngo
      cpr w3a cdrng flddivrng dvrunz divrngidl 3jca crngo co cdif wral 3ad2ant1
      crngorngo simp2 crab crn c1st rneqi eqtri rngo1cl ad2antrr cigen wn eldif
      wss snssi igenss sylan2 vex biimpri eleq2 syl5ibcom con3dimp sylan anasss
      snss sylan2b adantlr wo eldifi snssd igenidl imp an32s ovex sylib ord mpd
      elpr sylanl1 prnc eqtr3d eleqtrd eqeq1 rexbidv elrab simprd rexbii sylibr
      eqcom ralrimiva 3adant2 jca32 isdrngo3 simp1 isfld2 sylanbrc impbii ) DUA
      OZDUBOZAFUCZDUDUEZFUFZEUHZPZUIZXPXQXRYBDUGXPDUJOZXRDUKZDABCEFGHIJKULQXPYD
      YBYEDBCEFGHIJUMQUNYCYDXQXPYCDUOOZXRLRMRZCUPZAPZLESZMEXTUQZURZTTYDYCYFXRYL
      XQXRYFYBDUTZUSXQXRYBVAXQYBYLXRXQYBTZYJMYKYNYGYKOZTZAYHPZLESZYJYPAEOZYRYPA
      NRZYHPZLESZNEVBZOYSYRTYPAEUUCXQYSYBYOXQYFYSYMDACEEBVCDVDUEZVCIBUUDGVEVFHK
      VGQVHYPDYGUFZVIUPZEUUCXQYFYBYOUUFEPZYMYFYBTYOTZUUFXTPZVJZUUGYFYOUUJYBYOYF
      YGEOZYGXTOZVJZTUUJYGEXTVKYFUUKUUMUUJYFUUKTUUEUUFVLZUUMUUJUUKYFUUEEVLZUUNY
      GEVMDUUEBEGIVNVOUUNUUIUULUUNYGUUFOZUUIUULUUPUUNYGUUFMVPWCVQUUFXTYGVRVSVTW
      AWBWDWEUUHUUIUUGUUHUUFYAOZUUIUUGWFYFYOYBUUQYFYOTZYBUUQUURUUFXSOZYBUUQYOYF
      UUOUUSYOYGEYGEXTWGZWHDUUEBEGIWIVOXSYAUUFVRVSWJWKUUFXTEDUUEVIWLWPWMWNWOWQX
      QYOUUFUUCPZYBYOXQUUKUVAUUTNLYGDBCEGHIWRVOWEWSWTUUBYRNAEYTAPUUAYQLEYTAYHXA
      XBXCWMXDYIYQLEYHAXGXEXFXHXIXJMLDABCEFGHJIKXKXFXQXRYBXLDXMXNXO $.
  $}

  ${
    isfldidl2.1 $e |- G = ( 1st ` K ) $.
    isfldidl2.2 $e |- H = ( 2nd ` K ) $.
    isfldidl2.3 $e |- X = ran G $.
    isfldidl2.4 $e |- Z = ( GId ` G ) $.
    $( Obsolete theorem, use ~ isfieldidl2 instead.  Determine if a ring is a
       field based on its ideals.  (Contributed by Jeff Madsen, 6-Jan-2011.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    isfldidl2 $p |- ( K e. Fld <-> ( K e. CRingOps /\
                              X =/= { Z } /\ ( Idl ` K ) = { { Z } , X } ) ) $=
      ( cfld wcel ccring cgi cfv wne cidl wceq w3a wa 3anass csn cpr eqid crngo
      isfldidl wb crngorngo eqcom 0rngo bitrid necon3bid anbi1d pm5.32i 3bitr4i
      syl bitri ) CJKCLKZBMNZEOZCPNEUAZDUBQZRZUQDUTOZVARZURABCDEFGHIURUCZUEUQUS
      VASZSUQVCVASZSVBVDUQVFVGUQUSVCVAUQUREDUTUQCUDKZUREQZDUTQZUFCUGVIEURQVHVJU
      REUHCURABDEFGHIVEUIUJUOUKULUMUQUSVATUQVCVATUNUP $.
  $}

  ${
    $d R a b x y r s $.  $d P a b x y r s $.  $d X a b x y r s $.
    $d G x y r s $.  $d H a b x y r s $.
    ispridlc.1 $e |- G = ( 1st ` R ) $.
    ispridlc.2 $e |- H = ( 2nd ` R ) $.
    ispridlc.3 $e |- X = ran G $.
    $( Obsolete theorem, use ~ isprmidlc instead.  The predicate "is a prime
       ideal".  Alternate definition for commutative rings.  (Contributed by
       Jeff Madsen, 19-Jun-2010.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    ispridlc $p |- ( R e. CRingOps -> ( P e. ( PrIdl ` R )
                      <-> ( P e. ( Idl ` R ) /\ P =/= X /\ A. a e. X A. b e. X
                            ( ( a H b ) e. P -> ( a e. P \/ b e. P ) ) ) ) ) $=
      ( vx vy vs vr wcel co wi wral wss wa ccring cpridl cfv cidl wne cv wo w3a
      crngo wb crngorngo ispridl syl cigen snssi igenidl syl2an adantrr adantrl
      csn wceq raleq sseq1 orbi1d imbi12d ralbidv orbi2d rspc2v syl2anc adantlr
      wrex crab cab df-rab eqtrdi eqabrd anbi12d adantr reeanv anbi2i an4 bitri
      prnc crngm4 3com23 3expa adantllr syl3an1 3expb idllmulcl sylanl1 anassrs
      rngocl syldan eqeltrrd oveq12 eleq1d syl5ibrcom rexlimdvva adantld sylbid
      biimtrrid ralrimivv ex igenss snss sylibr ssel syl5com orim12d ralrimdvva
      vex imim12d syld adantrd imdistand df-3an 3imtr4g ispridl2 impbid ) BUAOZ
      ABUBUCOZABUDUCZOZAEUEZFUFZGUFZDPZAOZYFAOZYGAOZUGZQZGERFERZUHZYAYBYDYEKUFZ
      LUFZDPZAOZLMUFZRZKNUFZRZUUBASZYTASZUGZQZMYCRNYCRZUHZYOYABUIOZYBUUIUJBUKZK
      LABCDENMHIJULUMYAYDYETZUUHTUULYNTUUIYOYAUULUUHYNYAYDUUHYNQZYEYAYDUUMYAYDT
      ZUUHYMFGEEUUNYFEOZYGEOZTZTZUUHYSLBYGUTZUNPZRZKBYFUTZUNPZRZUVCASZUUTASZUGZ
      QZYMYAUUQUUHUVHQZYDYAUUQTZUVCYCOZUUTYCOZUVIYAUUOUVKUUPYAUUJUVBESZUVKUUOUU
      KYFEUOZBUVBCEHJUPUQURYAUUPUVLUUOYAUUJUUSESZUVLUUPUUKYGEUOZBUUSCEHJUPUQUSU
      UGUVHUUAKUVCRZUVEUUEUGZQNMUVCUUTYCYCUUBUVCVAZUUCUVQUUFUVRUUAKUUBUVCVBUVSU
      UDUVEUUEUUBUVCAVCVDVEYTUUTVAZUVQUVDUVRUVGUVTUUAUVAKUVCYSLYTUUTVBVFUVTUUEU
      VFUVEYTUUTAVCVGVEVHVIVJUURYIUVDUVGYLUURYIUVDUURYITZYSKLUVCUUTUWAYPUVCOZYQ
      UUTOZTZYPEOZYPUUBYFDPZVAZNEVKZTZYQEOZYQYTYGDPZVAZMEVKZTZTZYSUURUWDUWOUJZY
      IYAUUQUWPYDUVJUWBUWIUWCUWNYAUUOUWBUWIUJUUPYAUUOTZUWIKUVCUWQUVCUWHKEVLUWIK
      VMKNYFBCDEHIJWCUWHKEVNVOVPURYAUUPUWCUWNUJUUOYAUUPTZUWNLUUTUWRUUTUWMLEVLUW
      NLVMLMYGBCDEHIJWCUWMLEVNVOVPUSVQVJVRUWOUWEUWJTZUWGUWLTZMEVKNEVKZTZUWAYSUX
      BUWSUWHUWMTZTUWOUXAUXCUWSUWGUWLNMEEVSVTUWEUWJUWHUWMWAWBUWAUXAYSUWSUWAUWTY
      SNMEEUWAUUBEOZYTEOZTZTZYSUWTUWFUWKDPZAOUXGUUBYTDPZYHDPZUXHAUURUXFUXJUXHVA
      ZYIYAUUQUXFUXKYDYAUUQUXFUXKYAUXFUUQUXKUUBYTYFYGBCDEHIJWDWEWFWGVJUUNYIUXFU
      XJAOZUUQUUNYITUXFUXIEOZUXLUUNUXFUXMYIYAUXFUXMYDYAUXDUXEUXMYAUUJUXDUXEUXMU
      UKUUBYTBCDEHIJWMWHWIVJVJUUNYIUXMUXLYAUUJYDYIUXMTUXLUUKYHUXIBCDAEHIJWJWKWL
      WNWGWOUWTYRUXHAYPUWFYQUWKDWPWQWRWSWTXBXAXCXDYAUUQUVGYLQYDUVJUVEYJUVFYKUVJ
      YFUVCOZUVEYJYAUUOUXNUUPUWQUVBUVCSZUXNYAUUJUVMUXOUUOUUKUVNBUVBCEHJXEUQYFUV
      CFXLXFXGURUVCAYFXHXIUVJYGUUTOZUVFYKYAUUPUXPUUOUWRUUSUUTSZUXPYAUUJUVOUXQUU
      PUUKUVPBUUSCEHJXEUQYGUUTGXLXFXGUSUUTAYGXHXIXJVJXMXNXKXDXOXPYDYEUUHXQYDYEY
      NXQXRXAYAUUJYOYBQUUKUUJYOYBABCDEFGHIJXSXDUMXT $.

    $d A a b $.  $d B b $.
    $( Obsolete theorem, use ~ prmidlc instead.  Property of a prime ideal in a
       commutative ring.  (Contributed by Jeff Madsen, 17-Jun-2011.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    pridlc $p |- ( ( ( R e. CRingOps /\ P e. ( PrIdl ` R ) ) /\
          ( A e. X /\ B e. X /\ ( A H B ) e. P ) ) -> ( A e. P \/ B e. P ) ) $=
      ( va vb wcel cfv wa cv co wo wi wral ccring cpridl w3a cidl biimpa simp3d
      ispridlc wceq oveq1 eleq1d eleq1 orbi1d imbi12d oveq2 orbi2d rspc2v com12
      wne expd 3imp2 sylan ) DUAMZCDUBNMZOZKPZLPZFQZCMZVECMZVFCMZRZSZLGTKGTZAGM
      ZBGMZABFQZCMZUCACMZBCMZRZVDCDUDNMZCGURZVMVBVCWAWBVMUCCDEFGKLHIJUGUEUFVMVN
      VOVQVTVMVNVOVQVTSZVNVOOVMWCVLWCAVFFQZCMZVRVJRZSKLABGGVEAUHZVHWEVKWFWGVGWD
      CVEAVFFUIUJWGVIVRVJVEACUKULUMVFBUHZWEVQWFVTWHWDVPCVFBAFUNUJWHVJVSVRVFBCUK
      UOUMUPUQUSUTVA $.

    $( Obsolete theorem, use ~ prmidlc2 instead.  Property of a prime ideal in
       a commutative ring.  (Contributed by Jeff Madsen, 17-Jun-2011.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    pridlc2 $p |- ( ( ( R e. CRingOps /\ P e. ( PrIdl ` R ) ) /\
            ( A e. ( X \ P ) /\ B e. X /\ ( A H B ) e. P ) ) -> B e. P ) $=
      ( ccring wcel cpridl cfv wa cdif co w3a wn eldifn adantl wi eldifi pridlc
      3ad2ant1 ord syl3anr1 mpd ) DKLCDMNLOZAGCPLZBGLZABFQCLZRZOACLZSZBCLZUMUOU
      IUJUKUOULAGCTUEUAUJAGLZUIUKULUOUPUBAGCUCUIUQUKULROUNUPABCDEFGHIJUDUFUGUH
      $.

    $( Obsolete theorem, use ~ cmprmidlmcl instead.  Property of a prime ideal
       in a commutative ring.  (Contributed by Jeff Madsen, 17-Jun-2011.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    pridlc3 $p |- ( ( ( R e. CRingOps /\ P e. ( PrIdl ` R ) ) /\
          ( A e. ( X \ P ) /\ B e. ( X \ P ) ) ) -> ( A H B ) e. ( X \ P ) ) $=
      ( ccring wcel cpridl cfv wa cdif co eldifi wn wi crngorngo anim12i rngocl
      crngo 3expb syl2an adantlr ad2antll pridlc2 3exp2 imp32 con3d sylanr2 mpd
      eldifn eldifd ) DKLZCDMNLZOZAGCPZLZBUTLZOZOZABFQZGCUQVCVEGLZURUQDUDLZAGLZ
      BGLZOVFVCDUAVAVHVBVIAGCRBGCRZUBVGVHVIVFABDEFGHIJUCUEUFUGVDBCLZSZVECLZSZVB
      VLUSVABGCUOUHVBUSVAVIVLVNTVJUSVAVIOOVMVKUSVAVIVMVKTUSVAVIVMVKABCDEFGHIJUI
      UJUKULUMUNUP $.
  $}

  ${
    $d R a b $.  $d Z a b $.  $d H a b $.  $d X a b $.
    isdmn3.1 $e |- G = ( 1st ` R ) $.
    isdmn3.2 $e |- H = ( 2nd ` R ) $.
    isdmn3.3 $e |- X = ran G $.
    isdmn3.4 $e |- Z = ( GId ` G ) $.
    isdmn3.5 $e |- U = ( GId ` H ) $.
    $( Obsolete theorem, use ~ isidom3 instead.  The predicate "is a domain",
       alternate expression.  (Contributed by Jeff Madsen, 19-Jun-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    isdmn3 $p |- ( R e. Dmn <-> ( R e. CRingOps /\ U =/= Z /\ A. a e. X A. b e.
        X
                                ( ( a H b ) = Z -> ( a = Z \/ b = Z ) ) ) ) $=
      ( wcel wa wceq wi wral cfv syl cdmn cprrng ccring wne cv co wo w3a isdmn2
      crngo csn cpridl isprrngo cidl ispridlc crngorngo biantrurd 3anass wb crn
      0idl c1st rneqi eqtri rngo1cl eleq2 biimtrrdi syl5com c1o cen wbr rngo0cl
      elsni rngoueqz en1eqsn eqcomd ex sylbird impbid necon3bid ovex elsn velsn
      orbi12i imbi12i a1i 2ralbidv anbi12d bitr3d 3bitr3d pm5.32i ancom 3bitr4i
      bitrid bitri ) AUANAUBNZAUCNZOZWQBFUDZGUEZHUEZDUFZFPZWTFPZXAFPZUGZQZHERGE
      RZUHZAUIWQWPOWQWSXHOZOWRXIWQWPXJWPAUJNZFUKZAULSNZOZWQXJACFILUMWQXMXLAUNSN
      ZXLEUDZXBXLNZWTXLNZXAXLNZUGZQZHERGERZUHZXNXJXLACDEGHIJKUOWQXKXMAUPZUQYCXO
      XPYBOZOZWQXJXOXPYBURWQYEYFXJWQXOYEWQXKXOYDACFILVATUQWQXPWSYBXHWQXLEBFWQXK
      XLEPZBFPZUSYDXKYGYHXKBENZYGYHABDEECUTAVBSZUTKCYJIVCVDJMVEYGYIBXLNYHXLEBVF
      BFVMVGVHXKYHEVIVJVKZYGABCDEFIJLMKVNXKFENZYKYGQACEFIKLVLYLYKYGYLYKOEXLFEVO
      VPVQTVRVSTVTWQYAXGGHEEYAXGUSWQXQXCXTXFXBFWTXADWAWBXRXDXSXEGFWCHFWCWDWEWFW
      GWHWIWNWJWNWKWPWQWLWQWSXHURWMWO $.
  $}

  ${
    $d R a b $.  $d H a b $.  $d X a b $.  $d Z a b $.  $d A a b $.  $d B b $.
    dmnnzd.1 $e |- G = ( 1st ` R ) $.
    dmnnzd.2 $e |- H = ( 2nd ` R ) $.
    dmnnzd.3 $e |- X = ran G $.
    dmnnzd.4 $e |- Z = ( GId ` G ) $.
    $( Obsolete theorem, use ~ idomnzd instead.  A domain has no zero-divisors
       (besides zero).  (Contributed by Jeff Madsen, 19-Jun-2010.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    dmnnzd $p |- ( ( R e. Dmn /\ ( A e. X /\ B e. X /\ ( A H B ) = Z ) )
                                                  -> ( A = Z \/ B = Z ) ) $=
      ( va vb wcel co wceq wo wi cv wral cdmn wa ccring cgi cfv wne eqid isdmn3
      simp3bi oveq1 eqeq1d eqeq1 orbi1d imbi12d oveq2 orbi2d syl5com expd 3imp2
      rspc2v ) CUANZAFNZBFNZABEOZGPZAGPZBGPZQZVAVBVCVEVHRZVALSZMSZEOZGPZVJGPZVK
      GPZQZRZMFTLFTZVBVCUBVIVACUCNEUDUEZGUFVRCVSDEFGLMHIJKVSUGUHUIVQVIAVKEOZGPZ
      VFVOQZRLMABFFVJAPZVMWAVPWBWCVLVTGVJAVKEUJUKWCVNVFVOVJAGULUMUNVKBPZWAVEWBV
      HWDVTVDGVKBAEUOUKWDVOVGVFVKBGULUPUNUTUQURUS $.
  $}

  ${
    dmncan.1 $e |- G = ( 1st ` R ) $.
    dmncan.2 $e |- H = ( 2nd ` R ) $.
    dmncan.3 $e |- X = ran G $.
    dmncan.4 $e |- Z = ( GId ` G ) $.
    $( Obsolete theorem, use ~ idomcanl instead.  Cancellation law for domains.
       (Contributed by Jeff Madsen, 6-Jan-2011.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    dmncan1 $p |- ( ( ( R e. Dmn /\ ( A e. X /\ B e. X /\ C e. X ) )
                      /\ A =/= Z ) -> ( ( A H B ) = ( A H C ) -> B = C ) ) $=
      ( wcel wa co wceq sylan adantr wi 3expb cdmn w3a wne cgs cfv dmnrngo eqid
      crngo rngosubdi eqeq1d wo cgr rngogrpo syl grpodivcl adantlr dmnnzd 3exp2
      imp31 syldan exp43 3imp2 neor imbitrdi com23 imp sylbird rngocl 3adant3r3
      wb 3adant3r2 grpoeqdivid syl3anc 3adantr1 3imtr4d ) DUAMZAGMZBGMZCGMZUBZN
      ZAHUCZNZABFOZACFOZEUDUEZOZHPZBCWFOZHPZWDWEPZBCPZWCWHAWIFOZHPZWJWCWMWGHWAW
      MWGPZWBVPDUHMZVTWODUFZABCWFDEFGIJKWFUGZUIQRUJWAWBWNWJSWAWNWBWJWAWNAHPWJUK
      ZWBWJSVPVQVRVSWNWSSZVPVQVRVSWTVPVQNVRVSNZWIGMZWTVPXAXBVQVPEULMZXAXBVPWPXC
      WQDEIUMUNZXCVRVSXBBCWFEGKWRUOTQUPVPVQXBWTVPVQXBWNWSAWIDEFGHIJKLUQURUSUTVA
      VBWJAHVCVDVEVFVGWAWKWHVJZWBWAXCWDGMZWEGMZXEVPXCVTXDRVPWPVTXFWQWPVQVRXFVSA
      BDEFGIJKVHVIQVPWPVTXGWQWPVQVSXGVRACDEFGIJKVHVKQWDWEWFHEGKLWRVLVMRWAWLWJVJ
      ZWBVPVRVSXHVQVPXCXAXHXDXCVRVSXHBCWFHEGKLWRVLTQVNRVO $.

    $( Obsolete theorem, use ~ idomcanr instead.  Cancellation law for domains.
       (Contributed by Jeff Madsen, 6-Jan-2011.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    dmncan2 $p |- ( ( ( R e. Dmn /\ ( A e. X /\ B e. X /\ C e. X ) )
                      /\ C =/= Z ) -> ( ( A H C ) = ( B H C ) -> A = B ) ) $=
      ( cdmn wcel w3a wa wne co wceq crngocom wb ccring dmncrng 3adant3r2 sylan
      3adant3r1 eqeq12d adantr wi 3anrot biimpri dmncan1 sylanl2 sylbid ) DMNZA
      GNZBGNZCGNZOZPZCHQZPACFRZBCFRZSZCAFRZCBFRZSZABSZUTVDVGUAZVAUODUBNZUSVIDUC
      VJUSPVBVEVCVFVJUPURVBVESUQACDEFGIJKTUDVJUQURVCVFSUPBCDEFGIJKTUFUGUEUHUSUO
      URUPUQOZVAVGVHUIVKUSURUPUQUJUKCABDEFGHIJKLULUMUN $.
  $}

$( (End of Jeff Madsen's mathbox.) $)
