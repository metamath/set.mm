$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Integration
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Lebesgue integral - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d k x ph $.  $d k A $.  $d k B $.  $d k C $.  $d k D $.
    itgeq12dv.2 $e |- ( ph -> A = B ) $.
    itgeq12dv.1 $e |- ( ( ph /\ x e. A ) -> C = D ) $.
    $( Equality theorem for an integral.  (Contributed by Thierry Arnoux,
       14-Feb-2017.) $)
    itgeq12dv $p |- ( ph -> S. A C _d x = S. B D _d x ) $=
      ( vk cc0 co cv cr cdiv cre cfv cle wa citg2 cmul c3 cfz cexp wcel wbr cif
      ci cmpt citg fvoveq1d breq2d pm5.32da eleq2d anbi1d bitrd wceq adantrr wn
      csu eqidd ifbieq12d2 mpteq2dv fveq2d oveq2d sumeq2sdv eqid dfitg 3eqtr4g
      ) AJUAUBKZUGILUCKZBMBLZCUDZJEVJNKOPZQUEZRZVMJUFZUHZSPZTKZIUSVIVJBMVKDUDZJ
      FVJNKOPZQUEZRZWAJUFZUHZSPZTKZIUSBCEUIBDFUIAVIVSWGIAVRWFVJTAVQWESABMVPWDAV
      OWCVMJWAJAVOVLWBRWCAVLVNWBAVLRZVMWAJQWHEFVJONHUJZUKULAVLVTWBACDVKGUMUNUOA
      VLVMWAUPVNWIUQAVOURRJUTVAVBVCVDVEBCEVMIVMVFVGBDFWAIWAVFVGVH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Bochner integral
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c sitg $. $( Measure integral on simple functions $)
  $c sitm $. $( Integral metric $)
  $c itgm $. $( Measure integral $)

  $( Extend class notation with the (measure) Bochner integral. $)
  citgm $a class itgm $.

  $( Extend class notation with the integral metric for simple functions. $)
  csitm $a class sitm $.

  $( Extend class notation with the integral of simple functions. $)
  csitg $a class sitg $.

  ${
    $d f g m w x $.
    $( Define the integral of simple functions from a measurable space
       ` dom m ` to a generic space ` w ` equipped with the right scalar
       product. ` w ` will later be required to be a Banach space.

       These simple functions are required to take finitely many different
       values: this is expressed by ` ran g e. Fin ` in the definition.

       Moreover, for each ` x ` , the pre-image ` ( ``' g " { x } ) ` is
       requested to be measurable, of finite measure.

       In this definition, ` ( sigaGen `` ( TopOpen `` w ) ) ` is the Borel
       sigma-algebra on ` w ` , and the functions ` g ` range over the
       measurable functions over that Borel algebra.

       Definition 2.4.1 of [Bogachev] p. 118.  (Contributed by Thierry Arnoux,
       21-Oct-2017.) $)
    df-sitg $a |- sitg = ( w e. _V , m e. U. ran measures |-> ( f e.
      { g e. ( dom m MblFnM ( sigaGen ` ( TopOpen ` w ) ) ) | ( ran g e. Fin /\
          A. x e. ( ran g \ { ( 0g ` w ) } ) ( m ` ( `' g " { x } ) )
      e. ( 0 [,) +oo ) ) } |-> ( w gsum ( x e. ( ran f \ { ( 0g ` w ) } ) |-> (
          ( ( RRHom ` ( Scalar ` w ) ) ` ( m ` ( `' f " { x } ) ) )
      ( .s ` w ) x ) ) ) ) ) $.
  $}

  ${
    $d f g m w $.
    $( Define the integral metric for simple functions, as the integral of the
       distances between the function values.  Since distances take nonnegative
       values in ` RR* ` , the range structure for this integral is
       ` ( RR*s |``s ( 0 [,] +oo ) ) ` .  See definition 2.3.1 of [Bogachev]
       p. 116.  (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    df-sitm $a |- sitm = ( w e. _V , m e. U. ran measures |->
        ( f e. dom ( w sitg m ) , g e. dom ( w sitg m ) |->
     ( ( ( RR*s |`s ( 0 [,] +oo ) ) sitg m ) ` ( f oF ( dist ` w ) g ) ) ) ) $.
  $}

  ${
    $d f m w B $.  $d f g x F $.  $d f m w H $.  $d f g m w x M $.
    $d f g m w S $.  $d f g m w x W $.  $d f g m w x .0. $.  $d f m w .x. $.
    sitgval.b $e |- B = ( Base ` W ) $.
    sitgval.j $e |- J = ( TopOpen ` W ) $.
    sitgval.s $e |- S = ( sigaGen ` J ) $.
    sitgval.0 $e |- .0. = ( 0g ` W ) $.
    sitgval.x $e |- .x. = ( .s ` W ) $.
    sitgval.h $e |- H = ( RRHom ` ( Scalar ` W ) ) $.
    sitgval.1 $e |- ( ph -> W e. V ) $.
    sitgval.2 $e |- ( ph -> M e. U. ran measures ) $.
    $( Value of the simple function integral builder for a given space ` W `
       and measure ` M ` .  (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
    sitgval $p |- ( ph -> ( W sitg M ) = ( f e. { g e. ( dom M MblFnM S ) |
     ( ran g e. Fin /\ A. x e. ( ran g \ { .0. } ) ( M ` ( `' g " { x } ) )
        e. ( 0 [,) +oo ) ) } |-> ( W gsum ( x e. ( ran f \ { .0. } ) |-> (
        ( H ` ( M ` ( `' f " { x } ) ) ) .x. x ) ) ) ) ) $=
      ( vw vm cvv wcel cmeas crn cuni csitg cfn ccnv csn cima cfv cc0 cpnf cico
      co cv cdif wral wa cdm cmbfm crab cmpt cgsu wceq elexd c0g ctopn csigagen
      csca cvsca 2fveq3 fveq2i eqtri eqtr4di oveq2d fveq2 sneqd difeq2d raleqdv
      crrh anbi2d rabeqbidv fveq1d eqidd oveq123d mpteq12dv oveq12d dmeq oveq1d
      fveq1 eleq1d ralbidv simpl fveq2d mpteq2dva df-sitg ovex mptrabex syl2anc
      id ovmpo ) ALUDUEJUFUGUHZUELJUIURFGUSZUGZUJUEZXGUKBUSZULZUMZJUNZUOUPUQURZ
      UEZBXHMULZUTZVAZVBZGJVCZDVDURZVEZLBFUSZUGZXPUTZYCUKXKUMZJUNZHUNZXJEURZVFZ
      VGURZVFZVHALKTVIUAUBUCLJUDXFFXIXLUCUSZUNZXNUEZBXHUBUSZVJUNZULZUTZVAZVBZGY
      MVCZYPVKUNVLUNZVDURZVEZYPBYDYRUTZYFYMUNZYPVMUNWDUNZUNZXJYPVNUNZURZVFZVGUR
      ZVFYLUIFXIYOBXQVAZVBZGUUBDVDURZVEZLBYEUUGHUNZXJEURZVFZVGURZVFYPLVHZFUUEUU
      MUUQUVAUVBUUAUUOGUUDUUPUVBUUCDUUBVDUVBUUCLVKUNZVLUNZDYPLVLVKVODIVLUNUVDPI
      UVCVLOVPVQVRVSUVBYTUUNXIUVBYOBYSXQUVBYRXPXHUVBYQMUVBYQLVJUNMYPLVJVTQVRWAZ
      WBWCWEWFUVBYPLUULUUTVGUVBXDUVBBUUFUUKYEUUSUVBYRXPYDUVEWBUVBUUIUURXJXJUUJE
      UVBUUJLVNUNEYPLVNVTRVRUVBUUGUUHHUVBUUHLVMUNWDUNHYPLWDVMVOSVRWGUVBXJWHWIWJ
      WKWJYMJVHZFUUQUVAYBYKUVFUUOXSGUUPYAUVFUUBXTDVDYMJWLWMUVFUUNXRXIUVFYOXOBXQ
      UVFYNXMXNXLYMJWNWOWPWEWFUVFUUTYJLVGUVFBYEUUSYIUVFXJYEUEZVBZUURYHXJEUVHUUG
      YGHUVHYFYMJUVFUVGWQWGWRWMWSVSWJBUBFGUCWTXSFGYAYKXTDVDXAXBXEXC $.

    $( The predicate " ` F ` is a simple function" relative to the Bochner
       integral.  (Contributed by Thierry Arnoux, 19-Feb-2018.) $)
    issibf $p |- ( ph -> ( F e. dom ( W sitg M ) <-> ( F e. ( dom M MblFnM S )
        /\ ran F e. Fin /\ A. x e. ( ran F \ { .0. } ) ( M ` ( `' F " { x } ) )
        e. ( 0 [,) +oo ) ) ) ) $=
      ( vg vf csitg cdm wcel cmbfm crn cfn ccnv csn cima cfv cc0 cpnf cico cdif
      co cv wral wa w3a crab cmpt cgsu cvv sitgval dmeqd eqid dmmpt eqtrdi wceq
      eleq2d difeq1d cnveq imaeq1d fveq2d oveq1d mpteq12dv oveq2d eleq1d bitrdi
      rneq elrab ovex biantru bitr4di raleqbidv anbi12d 3anass ) AFKIUCUQZUDZUE
      ZFIUDDUFUQZUEZFUGZUHUEZFUIZBURZUJZUKZIULZUMUNUOUQZUEZBWOLUJZUPZUSZUTZUTZW
      NWPXFVAAWLFUAURZUGZUHUEZXIUIZWSUKZIULZXBUEZBXJXDUPZUSZUTZUAWMVBZUEZXHAWLX
      TKBXEXAGULZWREUQZVCZVDUQZVEUEZUTZXTAWLFKBUBURZUGZXDUPZYGUIZWSUKZIULZGULZW
      REUQZVCZVDUQZVEUEZUBXSVBZUEYFAWKYRFAWKUBXSYPVCZUDYRAWJYSABCDEUBUAGHIJKLMN
      OPQRSTVFVGUBXSYPYSYSVHVIVJVLYQYEUBFXSYGFVKZYPYDVEYTYOYCKVDYTBYIYNXEYBYTYH
      WOXDYGFWBVMYTYMYAWREYTYLXAGYTYKWTIYTYJWQWSYGFVNVOVPVPVQVRVSVTWCWAYEXTKYCV
      DWDWEWFXRXGUAFWMXIFVKZXKWPXQXFUUAXJWOUHXIFWBZVTUUAXOXCBXPXEUUAXJWOXDUUBVM
      UUAXNXAXBUUAXMWTIUUAXLWQWSXIFVNVOVPVTWGWHWCWAWNWPXFWIWF $.

    ${
      $d x S $.  $d x ph $.
      sibf0.1 $e |- ( ph -> W e. TopSp ) $.
      sibf0.2 $e |- ( ph -> W e. Mnd ) $.
      $( The constant zero function is a simple function.  (Contributed by
         Thierry Arnoux, 4-Mar-2018.) $)
      sibf0 $p |- ( ph -> ( U. dom M X. { .0. } ) e. dom ( W sitg M ) ) $=
        ( vx cdm cuni csn cxp csitg co wcel cmbfm crn cfn ccnv cv cima cfv cpnf
        cc0 cico cdif wral cmeas csiga dmmeas syl csigagen cvv ctopn a1i sgsiga
        fvexi eqeltrid cmpt wceq fconstmpt cmnd mndidcl ctps tpsuni unieqi mp1i
        unisg eqtrid eqtr4d eleqtrd mbfmcst xpeq1 0xp eqtrdi rneqd rn0 eqeltrdi
        c0 0fi rnxp snfi pm2.61ine noel difeq1d 0dif difid eleq2i mtbir pm2.21i
        wne adantl ralrimiva issibf mpbir3and ) AGUBZUCZJUDZUEZIGUFUGUBUHXLXICU
        IUGUHXLUJZUKUHZXLULUAUMZUDUNGUOUQUPURUGUHZUAXMXKUSZUTAUAJXICXLAGVAUJUCU
        HXIVBUJUCZUHRGVCVDACFVEUOZXRMAFVFFVFUHZAFIVGLVJZVHVIVKXLUAXJJVLVMAUAXJJ
        VNVHAJBCUCZAIVOUHJBUHTBIJKNVPVDABFUCZYBAIVQUHBYCVMSBFIKLVRVDAYBXSUCZYCC
        XSMVSXTYDYCVMAYAFVFWAVTWBWCWDWEXNAXNXJWLXJWLVMZXMWLUKYEXMWLUJWLYEXLWLYE
        XLWLXKUEWLXJWLXKWFXKWGWHWIWJWHZWMWKXJWLXDZXMXKUKXJXKWNZJWOWKWPVHAXPUAXQ
        XOXQUHZXPAYIXPYIXOWLUHXOWQXQWLXOXQWLVMXJWLYEXQWLXKUSWLYEXMWLXKYFWRXKWSW
        HYGXQXKXKUSWLYGXMXKXKYHWRXKWTWHWPXAXBXCXEXFAUABCDXLEFGHIJKLMNOPQRXGXH
        $.
    $}

    ${
      $d x A $.  $d f g B $.  $d f g x F $.  $d f H $.  $d f g M $.
      $d f g S $.  $d f W $.  $d f .x. $.  $d f g .0. $.  $d f x ph $.
      sibfmbl.1 $e |- ( ph -> F e. dom ( W sitg M ) ) $.
      $( A simple function is measurable.  (Contributed by Thierry Arnoux,
         19-Feb-2018.) $)
      sibfmbl $p |- ( ph -> F e. ( dom M MblFnM S ) ) $=
        ( vx cdm cmbfm co wcel crn cfn ccnv cv csn cima cfv cpnf cico cdif wral
        cc0 csitg w3a issibf mpbid simp1d ) AEHUBCUCUDUEZEUFZUGUEZEUHUAUIUJUKHU
        LUQUMUNUDUEUAVDKUJUOUPZAEJHURUDUBUEVCVEVFUSTAUABCDEFGHIJKLMNOPQRSUTVAVB
        $.

      $( A simple function is a function.  (Contributed by Thierry Arnoux,
         19-Feb-2018.) $)
      sibff $p |- ( ph -> F : U. dom M --> U. J ) $=
        ( cdm cuni cmeas crn wcel csiga dmmeas syl csigagen cfv cvv ctopn fvexd
        wf eqeltrid sgsiga sibfmbl mbfmf unieqi wceq unisg eqtrid feq3d mpbid )
        AHUAZUBZCUBZEUNVFGUBZEUNAVECEAHUCUDUBUEVEUFUDUBZUESHUGUHACGUIUJZVINAGUK
        AGJULUJUKMAJULUMUOZUPUOABCDEFGHIJKLMNOPQRSTUQURAVGVHEVFAVGVJUBZVHCVJNUS
        AGUKUEVLVHUTVKGUKVAUHVBVCVD $.

      $( A simple function has finite range.  (Contributed by Thierry Arnoux,
         19-Feb-2018.) $)
      sibfrn $p |- ( ph -> ran F e. Fin ) $=
        ( vx cdm cmbfm co wcel crn cfn ccnv cv csn cima cfv cpnf cico cdif wral
        cc0 csitg w3a issibf mpbid simp2d ) AEHUBCUCUDUEZEUFZUGUEZEUHUAUIUJUKHU
        LUQUMUNUDUEUAVDKUJUOUPZAEJHURUDUBUEVCVEVFUSTAUABCDEFGHIJKLMNOPQRSUTVAVB
        $.

      $( Any preimage of a singleton by a simple function is measurable.
         (Contributed by Thierry Arnoux, 19-Feb-2018.) $)
      sibfima $p |- ( ( ph /\ A e. ( ran F \ { .0. } ) )
                          -> ( M ` ( `' F " { A } ) ) e. ( 0 [,) +oo ) ) $=
        ( vx ccnv cv csn cima cfv cc0 cpnf cico co wcel crn cdif wral cdm cmbfm
        cfn csitg w3a issibf mpbid simp3d wceq sneq imaeq2d fveq2d eleq1d rspcv
        mpan9 ) AFUCZUBUDZUEZUFZIUGZUHUIUJUKZULZUBFUMZLUEUNZUOZBVSULVKBUEZUFZIU
        GZVPULZAFIUPDUQUKULZVRURULZVTAFKIUSUKUPULWEWFVTUTUAAUBCDEFGHIJKLMNOPQRS
        TVAVBVCVQWDUBBVSVLBVDZVOWCVPWGVNWBIWGVMWAVKVLBVEVFVGVHVIVJ $.

      ${
        sibfinima.g $e |- ( ph -> G e. dom ( W sitg M ) ) $.
        sibfinima.w $e |- ( ph -> W e. TopSp ) $.
        sibfinima.j $e |- ( ph -> J e. Fre ) $.
        $( The measure of the intersection of any two preimages by simple
           functions is a real number.  (Contributed by Thierry Arnoux,
           21-Mar-2018.) $)
        sibfinima $p |- ( ( ( ph /\ X e. ran F /\ Y e. ran G )
          /\ ( X =/= .0. \/ Y =/= .0. ) ) ->
        ( M ` ( ( `' F " { X } ) i^i ( `' G " { Y } ) ) ) e. ( 0 [,) +oo ) ) $=
          ( crn wcel w3a wne wo ccnv csn cima cin cfv cc0 cle wbr cpnf clt cico
          wa cr cxr cicc cdm cmeas cuni measbasedom sylib 3ad2ant1 csiga dmmeas
          co syl csigagen ct1 sgsiga eqeltrid sibfmbl ccld wss ctps ctop tpstop
          cmbfm cldssbrsiga 3syl sseqtrrdi sibff frnd simp2 sseldd eqid t1sncld
          syl2anc mbfmcnvima inelsiga syl3anc measvxrge0 elxrge0 simplbi adantr
          simp3 0re a1i simprbi pnfxr measssd cdif simpl1 anim1i eldifsn sylibr
          inss1 sibfima wb elico2 mp2an simp3bi xrlelttrd inss2 jaodan syl22anc
          xrre3 syl3anbrc ) ALEUGZUHZMFUGZUHZUIZLNUJZMNUJZUKZVCZEULLUMZUNZFULMU
          MZUNZUOZIUPZVDUHZUQUUBURUSZUUBUTVAUSZUUBUQUTVBVOZUHZYPUUBVEUHZUQVDUHZ
          UUDUUEUUCYLUUHYOYLUUBUQUTVFVOZUHZUUHYLIIVGZVHUPUHZUUAUULUHZUUKAYIUUMY
          KAIVHUGVIUHZUUMUBIVJVKVLZYLUULVMUGVIZUHZYRUULUHZYTUULUHZUUNAYIUURYKAU
          UOUURUBIVNVPVLZYLYQUULCEUVAAYICUUQUHYKACHVQUPZUUQQAHVRUFVSVTVLZAYIEUU
          LCWGVOZUHYKABCDEGHIJKNOPQRSTUAUBUCWAVLYLHWBUPZCYQAYIUVECWCYKAUVEUVBCA
          KWDUHHWEUHUVEUVBWCUEHKPWFHWHWIQWJVLZYLHVRUHZLHVIZUHYQUVEUHAYIUVGYKUFV
          LZYLYHUVHLAYIYHUVHWCYKAUULVIZUVHEABCDEGHIJKNOPQRSTUAUBUCWKWLVLAYIYKWM
          ZWNLHUVHUVHWOZWPWQWNWRZYLYSUULCFUVAUVCAYIFUVDUHYKABCDFGHIJKNOPQRSTUAU
          BUDWAVLYLUVECYSUVFYLUVGMUVHUHYSUVEUHUVIYLYJUVHMAYIYJUVHWCYKAUVJUVHFAB
          CDFGHIJKNOPQRSTUAUBUDWKWLVLAYIYKXEZWNMHUVHUVLWPWQWNWRZYRYTUULWSWTZUUA
          UULIXAWQZUUKUUHUUDUUBXBZXCVPZXDUUIYPXFXGYLUUDYOYLUUKUUDUVQUUKUUHUUDUV
          RXHVPXDZYLYMUUEYNYLYMVCZUUBYRIUPZUTYLUUHYMUVSXDUWAUWBUUJUHZUWBVEUHZUW
          AUUMUUSUWCYLUUMYMUUPXDZYLUUSYMUVMXDZYRUULIXAWQUWCUWDUQUWBURUSZUWBXBXC
          VPUTVEUHZUWAXIXGUWAUUAYRUULIUWEYLUUNYMUVPXDUWFUUAYRWCUWAYRYTXPXGXJUWA
          UWBUUFUHZUWBUTVAUSZUWAALYHNUMZXKUHZUWIAYIYKYMXLUWAYIYMVCUWLYLYIYMUVKX
          MLYHNXNXOALBCDEGHIJKNOPQRSTUAUBUCXQWQUWIUWBVDUHZUWGUWJUUIUWHUWIUWMUWG
          UWJUIXRXFXIUQUTUWBXSXTYAVPYBYLYNVCZUUBYTIUPZUTYLUUHYNUVSXDUWNUWOUUJUH
          ZUWOVEUHZUWNUUMUUTUWPYLUUMYNUUPXDZYLUUTYNUVOXDZYTUULIXAWQUWPUWQUQUWOU
          RUSZUWOXBXCVPUWHUWNXIXGUWNUUAYTUULIUWRYLUUNYNUVPXDUWSUUAYTWCUWNYRYTYC
          XGXJUWNUWOUUFUHZUWOUTVAUSZUWNAMYJUWKXKUHZUXAAYIYKYNXLUWNYKYNVCUXCYLYK
          YNUVNXMMYJNXNXOAMBCDFGHIJKNOPQRSTUAUBUDXQWQUXAUWOVDUHZUWTUXBUUIUWHUXA
          UXDUWTUXBUIXRXFXIUQUTUWOXSXTYAVPYBYDZUUBUQYFYEUVTUXEUUIUWHUUGUUCUUDUU
          EUIXRXFXIUQUTUUBXSXTYG $.
      $}

      ${
        $d x y B $.  $d x z C $.  $d b p x z F $.  $d b p x y z G $.
        $d x z J $.  $d b p x y z K $.  $d b p x z M $.  $d x W $.
        $d x y .0. $.  $d b p x y z .+ $.  $d p x y ph $.  $d b z ph $.
        sibfof.c $e |- C = ( Base ` K ) $.
        sibfof.0 $e |- ( ph -> W e. TopSp ) $.
        sibfof.1 $e |- ( ph -> .+ : ( B X. B ) --> C ) $.
        sibfof.2 $e |- ( ph -> G e. dom ( W sitg M ) ) $.
        sibfof.3 $e |- ( ph -> K e. TopSp ) $.
        sibfof.4 $e |- ( ph -> J e. Fre ) $.
        sibfof.5 $e |- ( ph -> ( .0. .+ .0. ) = ( 0g ` K ) ) $.
        $( Applying function operations on simple functions results in simple
           functions with regard to the destination space, provided the
           operation fulfills a simple condition.  (Contributed by Thierry
           Arnoux, 12-Mar-2018.) $)
        sibfof $p |- ( ph -> ( F oF .+ G ) e. dom ( K sitg M ) ) $=
          ( vz vb vx vp vy co cdm wcel ctopn cfv csigagen cmbfm crn cfn ccnv cv
          csn cima cc0 cdif wral cuni wf cvv ctps wceq tpsuni mpbid sibff cmeas
          cxp syl 3syl eqid eqtr4di feq3d a1i sgsiga mpbird wa cin imaeq2i wfun
          cun adantr ciun com cdom wbr wss inss2 simpll cnvimass sselda sibfmbl
          ct1 xp1st adantl eleqtrd t1sncld syl2anc eleqtrrdi mbfmcnvima syl3anc
          sseldd xp2nd ralrimiva sibfrn ssdomg csdm isfinite sdomdom domtr nfcv
          mpisyl sigaclcuni eqeltrd mpsyl ffund ssfi sylib c0 cle wdisj sylancl
          cr wne wo wi cof csitg cpnf cico c0g cmap feq2d fovcdmda dmexg uniexg
          sqxpeqd inidm off fvex unisg ax-mp csiga uniexd inundif ffun unpreima
          elmapd eqtr3id dmmeas imaiun eqtr3i c1st c2nd ffnd ofpreima2 ad2antrr
          iunid inss1 fssdm sstrid eqeltrid ccld ctop cldssbrsiga inelsiga xpfi
          tpstop biimpi imafi ofrn2 eqeltrrid difpreima cnvimarndm difeq2i mpbi
          ssralv ssdif0 eqtri eqtrdi unelsiga ismbfm mpbir2and csu cesum fveq2d
          0elsiga measbasedom eldifi sylan2 imaeq2d disjpreima disjxpin disjss1
          sneq sndisj measvuni syl112anc simpr sselid oveq12 sylan9eqr necon3ad
          wn ex neorian imbitrrdi ralrimivva wfn wb fniniseg cop 1st2nd2 eqtr3d
          df-ov simplr eldifbd velsn eqnetrrd sylanl2 oveq1 neeq1d neeq1 orbi1d
          necon3bbii imbi12d oveq2 orbi2d rspc2v sibfinima syl31anc esumpfinval
          mp2d 3eqtrd rge0ssre fsumrecl measge0 fsumge0 breqtrrd sylanbrc cvsca
          elrege0 csca crrh issibf mpbir3and ) AGHDUUAUQZKLUUBUQURUSVVALURZKUTV
          AZVBVAZVCUQUSZVVAVDZVEUSZVVAVFZULVGZVHZVIZLVAZVJUUCUUDUQZUSZULVVFKUUE
          VAZVHZVKZVLAVVEVVAVVDVMZVVBVMZUUFUQUSZVVHUMVGZVIZVVBUSZUMVVDVLAVVTVVS
          VVRVVAVNZAVVSCVVAVNZVWDAULUNVVSVVSVVSDJVMZVWFCGHVOVOAVVIUNVGZCVWFVWFD
          ABBWBZCDVNVWFVWFWBZCDVNUGAVWHVWICDABVWFANVPUSZBVWFVQZUFBJNPQVRWCZUUKU
          UGVSZUUHABEFGIJLMNOPQRSTUAUBUCUDVTZABEFHIJLMNOPQRSTUAUBUCUHVTZALWAVDV
          MZUSZVVBVOUSVVSVOUSUCLVWPUUIVVBVOUUJWDZVWRVVSUULUUMZACVVRVVAVVSACVVCV
          MZVVRAKVPUSCVWTVQUICVVCKUEVVCWEZVRWCVVCVOUSZVVRVWTVQKUTUUNZVVCVOUUOUU
          PWFWGVSAVVRVVSVVAVOVOAVVDUUQVDVMZAVVCVOVXBAVXCWHWIZUURVWRUVBWJAVWCUMV
          VDAVWAVVDUSZWKZVWBVVHVWAVVFWLZVIZVVHVWAVVFVKZVIZWOZVVBVXGVWBVVHVXHVXJ
          WOZVIZVXLVXMVWAVVHVWAVVFUUSWMAVXNVXLVQZVXFAVWEVVAWNZVXOVWSVVSCVVAUUTZ
          VXHVXJVVAUVAWDWPUVCVXGVVBVXDUSZVXIVVBUSVXKVVBUSZVXLVVBUSAVXRVXFAVWQVX
          RUCLUVDZWCZWPZVXGVXIULVXHVVKWQZVVBVVHULVXHVVJWQZVIVYCVXIULVVHVXHVVJUV
          EVYDVXHVVHULVXHUVLWMUVFVXGVXRVVKVVBUSZULVXHVLZVXHWRWSWTZVYCVVBUSVYBAV
          YFVXFVXHVVFXAZAVYEULVVFVLVYFVWAVVFXBZAVYEULVVFAVVIVVFUSZWKZVVKUODVFVV
          JVIZGVDZHVDZWBZWLZGVFZUOVGZUVGVAZVHZVIZHVFZVYRUVHVAZVHZVIZWLZWQZVVBAV
          VKWUGVQZVYJAVVSBBVVJDGHVOUOAVVSBGVNVVSVWFGVNVWNABVWFGVVSVWLWGWJAVVSBH
          VNVVSVWFHVNVWOABVWFHVVSVWLWGWJVWRAVWHCDUGUVIZUVJZWPVYKVXRWUFVVBUSZUOV
          YPVLZVYPWRWSWTZWUGVVBUSAVXRVYJVYAWPVYKWUKUOVYPVYKVYRVYPUSZWKZVXRWUAVV
          BUSZWUEVVBUSZWUKAVXRVYJWUNVYAUVKWUOAVYRVWHUSZWUPAVYJWUNXCZVYKVYPVWHVY
          RVYKVYPVYLVWHVYLVYOUVMZAVYLVWHXAVYJAVWHCVYLDDVVJXDUGUVNWPUVOXEZAWURWK
          ZVYTVVBEGAVXRWURVYAWPZAEVXDUSWURAEJVBVAZVXDRAJXGUJWIUVPWPZAGVVBEVCUQZ
          USWURABEFGIJLMNOPQRSTUAUBUCUDXFWPWVBVYTWVDEWVBJUVQVAZWVDVYTAWVGWVDXAZ
          WURAVWJJUVRUSWVHUFJNQUWBJUVSWDWPZWVBJXGUSZVYSVWFUSVYTWVGUSAWVJWURUJWP
          ZWVBVYSBVWFWURVYSBUSZAVYRBBXHZXIAVWKWURVWLWPZXJVYSJVWFVWFWEZXKXLXPRXM
          XNXLWUOAWURWUQWUSWVAWVBWUDVVBEHWVCWVEAHWVFUSWURABEFHIJLMNOPQRSTUAUBUC
          UHXFWPWVBWUDWVDEWVBWVGWVDWUDWVIWVBWVJWUCVWFUSWUDWVGUSWVKWVBWUCBVWFWUR
          WUCBUSZAVYRBBXQZXIWVNXJWUCJVWFWVOXKXLXPRXMXNXLWUAWUEVVBUVTXOZXRZAWUMV
          YJAVYPVYOWSWTZVYOWRWSWTZWUMAVYOVEUSZVYPVYOXAZWVTAVYMVEUSVYNVEUSWWBABE
          FGIJLMNOPQRSTUAUBUCUDXSABEFHIJLMNOPQRSTUAUBUCUHXSVYMVYNUWAXLZVYLVYOXB
          ZVYPVYOVEXTYFAWWBVYOWRYAWTZWWAWWDWWBWWFVYOYBUWCVYOWRYCWDVYPVYOWRYDXLZ
          WPVYPWUFVVBUOUOVYPYEYGXOYHXRVYEULVXHVVFUWKYIWPAVYGVXFAVXHVVFWSWTZVVFW
          RWSWTZVYGAVVGVYHWWHADVYOVIZVEUSZVVFWWJXAVVGADWNWWBWWKAVWHCDUGYJWWDDVY
          OUWDXLAVVSVWFCDGHVOVWNVWOVWMVWRUWEWWJVVFYKXLZVYIVXHVVFVEXTYFAVVFWRYAW
          TZWWIAVVGWWMWWLVVFYBYLVVFWRYCWCVXHVVFWRYDXLWPVXHVVKVVBULULVXHYEYGXOUW
          FAVXSVXFAVXKYMVVBAVXKVWBVVHVVFVIZVKZYMAVWEVXPVXKWWOVQVWSVXQVWAVVFVVAU
          WGWDWWOVWBVVAURZVKZYMWWNWWPVWBVVAUWHUWIVWBWWPXAWWQYMVQVVAVWAXDVWBWWPU
          WLUWJUWMUWNAVWQVXRYMVVBUSUCVXTVVBUXAWDYHWPVXIVXKVVBUWOXOYHXRAUMVVBVVD
          VVAVYAVXEUWPUWQWWLAVVNULVVQAVVIVVQUSZWKZVVLYQUSVJVVLYNWTVVNWWSVVLVYPW
          UFLVAZUOUWRZYQWWSVVLWUGLVAZVYPWWTUOUWSZWXAWWSVVKWUGLAWUHWWRWUJWPUWTWW
          SLVVBWAVAUSZWULWUMUOVYPWUFYOZWXBWXCVQAWXDWWRAVWQWXDUCLUXBYLWPZWWRAVYJ
          WULVVIVVFVVPUXCZWVSUXDAWUMWWRWWGWPAWXEWWRWWCAUOVYOWUFYOWXEWWEAUNUPVYM
          VYNVYQVWGVHZVIZWUBUPVGZVHZVIZWUAWUEUOVWGVYSVQZWXHVYTVYQVWGVYSUXIUXEWX
          JWUCVQZWXKWUDWUBWXJWUCUXIUXEAGWNUNVYMWXHYOUNVYMWXIYOAVVSVWFGVWNYJUNVY
          MUXJUNVYMWXHGUXFYPAHWNUPVYNWXKYOUPVYNWXLYOAVVSVWFHVWOYJUPVYNUXJUPVYNW
          XKHUXFYPUXGUOVYPVYOWUFUXHYIWPUOVYPWUFVVBLUXKUXLWWSVYPWWTUOAVYPVEUSZWW
          RAWWBWWCWXOWWDWWEVYOVYPYKYPWPZWWSWUNWKZAVYSVYMUSZWUCVYNUSZVYSOYRZWUCO
          YRZYSZWWTVVMUSAWWRWUNXCZWXQVYRVYOUSZWXRWXQVYPVYOVYRWWEWWSWUNUXMUXNZVY
          RVYMVYNXHWCWXQWYDWXSWYEVYRVYMVYNXQWCWXQVWGWXJDUQZVVOYRZVWGOYRZWXJOYRZ
          YSZYTZUPBVLUNBVLZVYSWUCDUQZVVOYRZWYBWXQAWYLWYCAWYKUNUPBBAWYKVWGBUSWXJ
          BUSWKAWYGVWGOVQWXJOVQWKZUXRWYJAWYOWYFVVOAWYOWYFVVOVQWYOAWYFOODUQVVOVW
          GOWXJODUXOUKUXPUXSUXQVWGOWXJOUXTUYAWPUYBWCWXQVVIWYMVVOWXQWURVYRDVAZVV
          IVQZWKZVVIWYMVQWXQVYRVYLUSZWYRWWSVYPVYLVYRVYPVYLXAWWSWUTWHXEWXQADVWHU
          YCWYSWYRUYDWYCWUIVWHVVIVYRDUYEWDVSWYRWYPVVIWYMWURWYQUXMWURWYPWYMVQWYQ
          WURWYPVYSWUCUYFZDVAWYMWURVYRWYTDVYRBBUYGUWTVYSWUCDUYIWFWPUYHWCWXQVVIV
          VPUSZUXRVVIVVOYRWXQVVIVVFVVPAWWRWUNUYJUYKXUAVVIVVOULVVOUYLUYSYLUYMWXQ
          WVLWVPWYLWYNWYBYTZYTWXQWURWVLWWRAVYJWUNWURWXGWVAUYNZWVMWCWXQWURWVPXUC
          WVQWCWYKXUBVYSWXJDUQZVVOYRZWXTWYIYSZYTUNUPVYSWUCBBWXMWYGXUEWYJXUFWXMW
          YFXUDVVOVWGVYSWXJDUYOUYPWXMWYHWXTWYIVWGVYSOUYQUYRUYTWXNXUEWYNXUFWYBWX
          NXUDWYMVVOWXJWUCVYSDVUAUYPWXNWYIWYAWXTWXJWUCOUYQVUBUYTVUCXLVUGABEFGHI
          JLMNVYSWUCOPQRSTUAUBUCUDUHUFUJVUDVUEZVUFVUHZWWSVYPWWTUOWXPWXQVVMYQWWT
          VUIXUGUXNZVUJYHWWSVJWXAVVLYNWWSVYPWWTUOWXPXUIWXQWXDWUKVJWWTYNWTWWSWXD
          WUNWXFWPWWRAVYJWUNWUKWXGWVRUYNWUFVVBLVUKXLVULXUHVUMVVLVUPVUNXRAULCVVD
          KVUOVAZVVAKVUQVAVURVAZVVCLVPKVVOUEVXAVVDWEVVOWEXUJWEXUKWEUIUCVUSVUT
          $.
      $}

      $( Value of the Bochner integral for a simple function ` F ` .
         (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
      sitgfval $p |- ( ph -> ( ( W sitg M ) ` F ) = ( W gsum ( x e. ( ran F \
        { .0. } ) |-> ( ( H ` ( M ` ( `' F " { x } ) ) ) .x. x ) ) ) ) $=
        ( vf vg cv crn csn cdif ccnv cima cfv cmpt cgsu cfn wcel cpnf cico wral
        co cc0 cdm cmbfm crab csitg cvv sitgval wceq simpr rneqd difeq1d cnveqd
        imaeq1d fveq2d oveq1d mpteq12dv oveq2d sibfmbl sibfrn sibfima ralrimiva
        wa jca32 rneq eleq1d cnveq raleqbidv anbi12d elrab sylibr ovexd fvmptd
        ) AUBFKBUBUDZUEZLUFZUGZWKUHZBUDZUFZUIZIUJZGUJZWPEURZUKZULURKBFUEZWMUGZF
        UHZWQUIZIUJZGUJZWPEURZUKZULURUCUDZUEZUMUNZXKUHZWQUIZIUJZUSUOUPURZUNZBXL
        WMUGZUQZVTZUCIUTDVAURZVBZKIVCURVDABCDEUBUCGHIJKLMNOPQRSTVEAWKFVFZVTZXBX
        JKULYEBWNXAXDXIYEWLXCWMYEWKFAYDVGZVHVIYEWTXHWPEYEWSXGGYEWRXFIYEWOXEWQYE
        WKFYFVJVKVLVLVMVNVOAFYBUNZXCUMUNZXGXQUNZBXDUQZVTZVTFYCUNAYGYHYJACDEFGHI
        JKLMNOPQRSTUAVPACDEFGHIJKLMNOPQRSTUAVQAYIBXDAWPCDEFGHIJKLMNOPQRSTUAVRVS
        WAYAYKUCFYBXKFVFZXMYHXTYJYLXLXCUMXKFWBZWCYLXRYIBXSXDYLXLXCWMYMVIYLXPXGX
        QYLXOXFIYLXNXEWQXKFWDVKVLWCWEWFWGWHAKXJULWIWJ $.

      ${
        $d m x .0. $.  $d m .x. $.  $d m x B $.  $d m x F $.  $d m G $.
        $d m H $.  $d m x M $.  $d m S $.  $d m x W $.  $d m x ph $.
        sitgclg.g $e |- G = ( Scalar ` W ) $.
        sitgclg.d $e |- D = ( ( dist ` G )
                                |` ( ( Base ` G ) X. ( Base ` G ) ) ) $.
        sitgclg.1 $e |- ( ph -> W e. TopSp ) $.
        sitgclg.2 $e |- ( ph -> W e. CMnd ) $.
        sitgclg.3 $e |- ( ph -> ( Scalar ` W ) e. RRExt ) $.
        sitgclg.4 $e |- ( ( ph /\ m e. ( H " ( 0 [,) +oo ) ) /\ x e. B )
                            -> ( m .x. x ) e. B ) $.
        $( TODO : eliminate G and D $)
        $( Closure of the Bochner integral on simple functions, generic
           version.  See ~ sitgclbn for the version for Banach spaces.
           (Contributed by Thierry Arnoux, 24-Feb-2018.)  (Proof shortened by
           AV, 12-Dec-2019.) $)
        sitgclg $p |- ( ph -> ( ( W sitg M ) ` F ) e. B ) $=
          ( csitg co cfv crn csn cdif ccnv cima cmpt cgsu sitgfval cvv cdm wcel
          cv rnexg difexg 3syl wa cc0 cpnf cico simpl sibfima wfun wss csca cbs
          wi cr crrh wf cioo ctg ctopn czlm cds cxp cres xpeq12i reseq12i eqtri
          fveq2i eqid cdr crrext eqeltrid rrextdrg eqeltrrid cnrg rrextnrg cnlm
          syl rrextnlm cchr wceq rrextchr eqtr3id ccusp rrextcusp cuss rrextust
          cmetu rrhf feq1i ffund rge0ssre fdmd sseqtrrid funfvima2 syl2anc sylc
          sylibr cuni cmeas csiga dmmeas csigagen fvexi a1i sgsiga sibfmbl frnd
          mbfmf unieqi w3a cfn sylancl sstri eqeltrd unisg eqtrid tpsuni eqtr4d
          mp1i sseqtrd ssdifd sselda eldifad simp2 eleq1 3anbi2d eleq1d imbi12d
          ctps oveq1 vtoclg mpcom syl3anc fmpttd csupp mptexg suppimacnv sibfrn
          c0g cnvimass dmmptss difss ssfi gsumcl2 ) AHNLUKULZUMNBHUNZOUOZUPZHUQ
          BVEZUOURLUMZJUMZUVOFULZUSZUTULCABCEFHJKLMNOPQRSTUAUBUCUDVAAUVNCUVSNVB
          OPSUHAHUVKVCZVDUVLVBVDUVNVBVDZUDHUVTVFUVLUVMVBVGVHZABUVNUVRCAUVOUVNVD
          ZVIZAUVQJVJVKVLULZURZVDZUVOCVDZUVRCVDZAUWCVMZUWDAUVPUWEVDZUWGUWJAUVOC
          EFHJKLMNOPQRSTUAUBUCUDVNAJVOUWEJVCZVPUWKUWGVSAVTNVQUMZVRUMZJAVTUWNUWM
          WAUMZWBVTUWNJWBAUWNDUWMWCUNWDUMZIWEUMIWFUMZDIWGUMZIVRUMZUWSWHZWIUWMWG
          UMZUWNUWNWHZWIUFUWRUXAUWTUXBIUWMWGUEWMUWSUWNUWSUWNIUWMVRUEWMZUXCWJWKW
          LUWPWNUWNWNIUWMWEUEWMIUWMWFUEWMAUWMIWOUEAIWPVDZIWOVDAIUWMWPUEUIWQZIWR
          XCWSAUWMIWTUEAUXDIWTVDUXEIXAXCWSAUXDUWQXBVDUXEIUWQUWQWNXDXCAUWMXEUMIX
          EUMZVJIUWMXEUEWMAUXDUXFVJXFUXEIXGXCXHAUWMIXIUEAUXDIXIVDUXEIXJXCWSAUWM
          XKUMIXKUMZDXMUMZIUWMXKUEWMAUXDUXGUXHXFUXEUWSDIUWSWNUFXLXCXHXNVTUWNJUW
          OUAXOYCZXPAVTUWEUWLXQAVTUWNJUXIXRXSUWEUVPJXTYAYBUWDUVOCUVMAUVNCUVMUPU
          VOAUVLCUVMAUVLEYDZCALVCZYDUXJHAUXKEHALYEUNYDVDUXKYFUNYDZVDUCLYGXCAEKY
          HUMZUXLRAKVBKVBVDZAKNWEQYIZYJYKWQACEFHJKLMNOPQRSTUAUBUCUDYLYNYMAUXJKY
          DZCAUXJUXMYDZUXPEUXMRYOUXNUXQUXPXFAUXOKVBUUAUUEUUBANUUOVDCUXPXFUGCKNP
          QUUCXCUUDUUFUUGUUHUUIUWGAUWGUWHYPZUWIAUWGUWHUUJAGVEZUWFVDZUWHYPZUXSUV
          OFULZCVDZVSUXRUWIVSGUVQUWFUXSUVQXFZUYAUXRUYCUWIUYDUXTUWGAUWHUXSUVQUWF
          UUKUULUYDUYBUVRCUXSUVQUVOFUUPUUMUUNUJUUQUURUUSUUTAUVSOUVAULZUVSUQVBUV
          MUPZURZYQAUVSVBVDZOVBVDUYEUYGXFAUWAUYHUWBBUVNUVRVBUVBXCONUVESYIUVSVBV
          BOUVCYRAUVLYQVDUYGUVLVPUYGYQVDACEFHJKLMNOPQRSTUAUBUCUDUVDUYGUVNUVLUYG
          UVSVCUVNUVSUYFUVFBUVNUVRUVSUVSWNUVGYSUVLUVMUVHYSUVLUYGUVIYRYTUVJYT $.
      $}

      ${
        $d m x B $.  $d m x W $.  $d m F $.  $d m x ph $.  $d m .x. $.
        sitgclbn.1 $e |- ( ph -> W e. Ban ) $.
        sitgclbn.2 $e |- ( ph -> ( Scalar ` W ) e. RRExt ) $.
        $( Closure of the Bochner integral on a simple function.  This version
           is specific to Banach spaces, with additional conditions on its
           scalar field.  (Contributed by Thierry Arnoux, 24-Feb-2018.) $)
        sitgclbn $p |- ( ph -> ( ( W sitg M ) ` F ) e. B ) $=
          ( vx vm csca cfv cds cbs cxp cres eqid cbn wcel ccms ctps bncms cmsms
          cms mstps 4syl clmod ccmn bnlmod lmodcmn 3syl cv cc0 cpnf cico co w3a
          cima syl 3ad2ant1 crn imassrn crrh rneqi crrext cr wss rrhfe eqsstrid
          wf frn sstrid sselda 3adant3 simp3 lmodvscl syl3anc sitgclg ) AUCBJUE
          UFZUGUFWMUHUFZWNUIUJZCDUDEWMFGHIJKLMNOPQRSTWMUKZWOUKAJULUMZJUNUMJURUM
          JUOUMUAJUPJUQJUSUTAWQJVAUMZJVBUMUAJVCZJVDVEUBAUDVFZFVGVHVIVJZVLZUMZUC
          VFZBUMZVKWRWTWNUMZXEWTXDDVJBUMAXCWRXEAWQWRUAWSVMVNAXCXFXEAXBWNWTAXBFV
          OZWNFXAVPAXGWMVQUFZVOZWNFXHQVRAWMVSUMVTWNXHWDXIWNWAUBWNWMWNUKZWBVTWNX
          HWEVEWCWFWGWHAXCXEWIWTDWMWNBJXDLWPPXJWJWKWL $.
      $}

      ${
        sitgclcn.1 $e |- ( ph -> W e. Ban ) $.
        sitgclcn.2 $e |- ( ph -> ( Scalar ` W ) = CCfld ) $.
        $( Closure of the Bochner integral on a simple function.  This version
           is specific to Banach spaces on the complex numbers.  (Contributed
           by Thierry Arnoux, 24-Feb-2018.) $)
        sitgclcn $p |- ( ph -> ( ( W sitg M ) ` F ) e. B ) $=
          ( csca cfv ccnfld crrext cnrrext eqeltrdi sitgclbn ) ABCDEFGHIJKLMNOP
          QRSTUAAJUCUDUEUFUBUGUHUI $.
      $}

      ${
        sitgclre.1 $e |- ( ph -> W e. Ban ) $.
        sitgclre.3 $e |- ( ph -> ( Scalar ` W ) = RRfld ) $.
        $( Closure of the Bochner integral on a simple function.  This version
           is specific to Banach spaces on the real numbers.  (Contributed by
           Thierry Arnoux, 24-Feb-2018.) $)
        sitgclre $p |- ( ph -> ( ( W sitg M ) ` F ) e. B ) $=
          ( csca cfv crefld crrext rerrext eqeltrdi sitgclbn ) ABCDEFGHIJKLMNOP
          QRSTUAAJUCUDUEUFUBUGUHUI $.
      $}
    $}

    ${
      $d x ph $.
      sitg0.1 $e |- ( ph -> W e. TopSp ) $.
      sitg0.2 $e |- ( ph -> W e. Mnd ) $.
      $( The integral of the constant zero function is zero.  (Contributed by
         Thierry Arnoux, 13-Mar-2018.) $)
      sitg0 $p |- ( ph -> ( ( W sitg M ) ` ( U. dom M X. { .0. } ) ) = .0. ) $=
        ( vx cdm cuni csn cxp csitg co cfv cdif ccnv cv cima cmpt cgsu sitgfval
        crn sibf0 c0 wceq wss rnxpss ssdif0 mpbi mpteq1 ax-mp mpt0 eqtri oveq2i
        gsum0 eqtrdi ) AGUBUCZJUDZUEZIGUFUGUHIUAVMUPZVLUIZVMUJUAUKZUDULGUHEUHVP
        DUGZUMZUNUGZJAUABCDVMEFGHIJKLMNOPQRABCDEFGHIJKLMNOPQRSTUQUOVSIURUNUGJVR
        URIUNVRUAURVQUMZURVOURUSZVRVTUSVNVLUTWAVKVLVAVNVLVBVCUAVOURVQVDVEUAVQVF
        VGVHIJNVIVGVJ $.
    $}

    ${
      $d f ph $.
      sitgf.1 $e |- ( ( ph /\ f e. dom ( W sitg M ) )
                    -> ( ( W sitg M ) ` f ) e. B ) $.
      $( The integral for simple functions is itself a function.  (Contributed
         by Thierry Arnoux, 13-Feb-2018.) $)
      sitgf $p |- ( ph -> ( W sitg M ) : dom ( W sitg M ) --> B ) $=
        ( vg vx csitg co cdm wfn crn wss wf wfun cfn wcel ccnv csn cima cfv cc0
        cv cpnf cico cdif wral cmbfm crab cmpt cgsu funmpt funeqd mpbiri funfnd
        wa sitgval ralrimiva fnfvrnss syl2anc df-f sylanbrc ) AJHUCUDZVRUEZUFZV
        RUGBUHZVSBVRUIAVRAVRUJEUAURZUGZUKULWBUMUBURZUNZUOHUPUQUSUTUDULUBWCKUNZV
        AVBVKUAHUECVCUDVDZJUBEURZUGWFVAWHUMWEUOHUPFUPWDDUDVEVFUDZVEZUJEWGWIVGAV
        RWJAUBBCDEUAFGHIJKLMNOPQRSVLVHVIVJZAVTWHVRUPBULZEVSVBWAWKAWLEVSTVMEVSBV
        RVNVOVSBVRVPVQ $.
    $}

    ${
      sitgadd.1 $e |- ( ph -> W e. TopSp ) $.
      sitgadd.2 $e |- ( ph -> ( W |`v ( H " ( 0 [,) +oo ) ) ) e. SLMod ) $.
      sitgadd.3 $e |- ( ph -> J e. Fre ) $.
      sitgadd.4 $e |- ( ph -> F e. dom ( W sitg M ) ) $.
      sitgadd.5 $e |- ( ph -> G e. dom ( W sitg M ) ) $.
      ${
        sitgadd.6 $e |- ( ph -> ( Scalar ` W ) e. RRExt ) $.
        sitgadd.7 $e |- .+ = ( +g ` W ) $.
        $( Lemma for * sitgadd .  (Contributed by Thierry Arnoux,
           10-Mar-2019.) $)
        sitgaddlemb $p |- ( ( ph
            /\ p e. ( ( ran F X. ran G ) \ { <. .0. , .0. >. } ) )
          -> ( ( H ` ( M ` ( ( `' F " { ( 1st ` p ) } )
              i^i ( `' G " { ( 2nd ` p ) } ) ) ) ) .x. ( 2nd ` p ) ) e. B ) $=
          ( cv crn cxp cop csn cdif wcel wa cc0 cpnf cico cima cresv cslmd ccnv
          co c1st cfv c2nd cin csca cress cbs adantr cr wfn wss simpl wf crrext
          crrh eqid rrhfe syl feq1i sylibr ffnd rge0ssre a1i wne wo simpr xp1st
          eldifad xp2nd wceq wn eldifbd velsn notbii sylib eqopi ex imp syl2anc
          con3d ianor orbi12i bitr4i sibfinima syl31anc fnfvima syl3anc imassrn
          df-ne frnd sstrid ressbas2 eleqtrd cdm cuni sibff ctps wb tpsuni feq3
          3syl mpbird sseldd cvv fvexi imaexg resvbas resvsca resvvsca slmdvscl
          mp2b cvsca ) ANUJZFUKZGUKZULZMMUMZUNZUOUPZUQZLHURUSUTVEZVAZVBVEZVCUPZ
          FVDYRVFVGZUNVAGVDYRVHVGZUNVAVIJVGZHVGZLVJVGZUUGVKVEZVLVGZUPUUKBUPUUMU
          UKEVEBUPAUUIUUDUDVMUUEUUMUUGUUPUUEHVNVOZUUFVNVPZUULUUFUPZUUMUUGUPUUEA
          UUQAUUDVQZAVNUUNVLVGZHAVNUVAUUNVTVGZVRZVNUVAHVRAUUNVSUPUVCUHUVAUUNUVA
          WAZWBWCVNUVAHUVBTWDWEZWFWCUURUUEWGWHUUEAUUJYSUPZUUKYTUPZUUJMWIZUUKMWI
          ZWJZUUSUUTUUEYRUUAUPZUVFUUEYRUUAUUCAUUDWKZWMZYRYSYTWLWCUUEUVKUVGUVMYR
          YSYTWNWCZUUEUUJMWOZUUKMWOZUQZWPZUVJUUEUVKYRUUBWOZWPZUVRUVMUUEYRUUCUPZ
          WPUVTUUEYRUUAUUCUVLWQUWAUVSNUUBWRWSWTUVKUVTUVRUVKUVQUVSUVKUVQUVSYRMMY
          SYTXAXBXEXCXDUVRUVOWPZUVPWPZWJUVJUVOUVPXFUVHUWBUVIUWCUUJMXNUUKMXNXGXH
          WTABDEFGHIJKLUUJUUKMOPQRSTUAUBUFUGUCUEXIXJVNUUFHUULXKXLUUEAUUGUUPWOZU
          UTAUUGUVAVPUWDAUUGHUKUVAHUUFXMAVNUVAHUVEXOXPUUGUVAUUOUUNUUOWAUVDXQWCW
          CXRUUEYTBUUKAYTBVPUUDAJXSXTZBGAUWEBGVRZUWEIXTZGVRZABDEGHIJKLMOPQRSTUA
          UBUGYAALYBUPBUWGWOUWFUWHYCUCBILOPYDBUWGUWEGYEYFYGXOVMUVNYHUUMEUUOUUPB
          UUHUUKHYIUPZUUGYIUPZBUUHVLVGWOHUUNVTTYJZHUUFYIYKZUUGBLUUHYIUUHWAZOYLY
          PUWIUWJUUOUUHVJVGWOUWKUWLUUGUVAUUHUUNYILUWMUUNWAUVDYMYPUWIUWJEUUHYQVG
          WOUWKUWLUUGELUUHYIUWMSYNYPUUPWAYOXL $.

$(
        @( Lemma for ~ sitgadd . @)
        sitgaddlem2 @p |- ( ph -> ( ( W  sitg M ) ` G )
           = ( W gsum ( p e. ( ( ran F X. ran G ) \ { <. .0. , .0. >. } )
           |-> ( ( H ` ( M ` ( ( `' F " { ( 1st ` p ) } )
           i^i ( `' G " { ( 2nd ` p ) } ) ) ) ) .x. ( 2nd ` p ) ) ) ) ) @=
          ? @.

        sitgaddlem1 @p |- ( ph -> ( ( W  sitg M ) ` F )
           = ( W gsum ( p e. ( ( ran F X. ran G ) \ { <. .0. , .0. >. } )
           |-> ( ( H ` ( M ` ( ( `' F " { ( 1st ` p ) } )
           i^i ( `' G " { ( 2nd ` p ) } ) ) ) ) .x. ( 1st ` p ) ) ) ) ) @=
          ? @.

        @( For simple functions, the integral of a sum is the sum of the
           integral. @)
        sitgadd @p |- ( ph -> ( ( W  sitg M ) ` ( F oF .+ G ) )
           = ( ( ( W  sitg M ) ` F ) .+ ( ( W  sitg M ) ` G ) ) ) @=
          ? @.
$)
      $}

$(
      sitgle.1 @e |- .<_ = ( le ` W ) @.
      sitgle.2 @e |- ( ph -> W e. oMnd ) @.
      sitgle.4 @e |- ( ph -> F oR .<_ G ) @.
      @( The simple function integral is monotonic.
         @)
      sitgle @p |- ( ph -> ( ( W sitg M ) ` F ) .<_ ( ( W sitg M ) ` G ) ) @=
        ? @.
$)
    $}
  $}

  ${
    $d m w D $.  $d f g m w M $.  $d f g m w W $.
    sitmval.d $e |- D = ( dist ` W ) $.
    sitmval.1 $e |- ( ph -> W e. V ) $.
    sitmval.2 $e |- ( ph -> M e. U. ran measures ) $.
    $( Value of the simple function integral metric for a given space ` W ` and
       measure ` M ` .  (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
    sitmval $p |- ( ph -> ( W sitm M ) =
      ( f e. dom ( W sitg M ) , g e. dom ( W sitg M ) |->
        ( ( ( RR*s |`s ( 0 [,] +oo ) ) sitg M ) ` ( f oF D g ) ) ) ) $=
      ( vw vm wcel co csitg cdm cv cof cfv wceq cmeas cuni csitm cxrs cpnf cicc
      cvv crn cc0 cress cmpo elex syl oveq1 dmeqd fveq2 ofeqd fveq2d mpoeq123dv
      cds oveqd oveq2 eqcomi ofeq mp1i fveq12d df-sitm ovex mpoex ovmpo syl2anc
      dmex ) AGUGMZEUAUHUBZMGEUCNCDGEONZPZVPCQZDQZBRZNZUDUIUEUFNUJNZEONZSZUKZTA
      GFMVMIGFULUMJKLGEUGVNCDKQZLQZONZPZWHVQVRWEUTSZRZNZWAWFONZSZUKWDUCCDGWFONZ
      PZWOVQVRGUTSZRZNZWLSZUKWEGTZCDWHWHWMWOWOWSWTWGWNWEGWFOUNUOZXAWTWKWRWLWTWJ
      WQVQVRWTWIWPWEGUTUPUQVAURUSWFETZCDWOWOWSVPVPWCXBWNVOWFEGOVBUOZXCXBWRVTWLW
      BWFEWAOVBXBWQVSVQVRWPBTWQVSTXBBWPHVCWPBVDVEVAVFUSKCDLVGCDVPVPWCVOGEOVHVLZ
      XDVIVJVK $.

    $d f g D $.  $d f g F $.  $d f g G $.  $d f g M $.  $d f g W $.
    $d f g ph $.
    sitmfval.1 $e |- ( ph -> F e. dom ( W sitg M ) ) $.
    sitmfval.2 $e |- ( ph -> G e. dom ( W sitg M ) ) $.
    $( Value of the integral distance between two simple functions.
       (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
    sitmfval $p |- ( ph -> ( F ( W sitm M ) G ) =
      ( ( ( RR*s |`s ( 0 [,] +oo ) ) sitg M ) ` ( F oF D G ) ) ) $=
      ( vf vg csitg co cv cfv wceq wa cdm cof cxrs cc0 cpnf cress csitm sitmval
      cicc cvv simprl simprr oveq12d fveq2d fvexd ovmpod ) AMNCDGEOPUAZUQMQZNQZ
      BUBZPZUCUDUEUIPUFPEOPZRCDUTPZVBRGEUGPUJABMNEFGHIJUHAURCSZUSDSZTTZVAVCVBVF
      URCUSDUTAVDVEUKAVDVEULUMUNKLAVCVBUOUP $.
  $}

  ${
    $d m x F $.  $d m x G $.  $d m x M $.  $d m x W $.  $d m x ph $.
    sitmcl.0 $e |- ( ph -> W e. Mnd ) $.
    sitmcl.1 $e |- ( ph -> W e. *MetSp ) $.
    sitmcl.2 $e |- ( ph -> M e. U. ran measures ) $.
    sitmcl.3 $e |- ( ph -> F e. dom ( W sitg M ) ) $.
    sitmcl.4 $e |- ( ph -> G e. dom ( W sitg M ) ) $.
    $( Closure of the integral distance between two simple functions, for an
       extended metric space.  (Contributed by Thierry Arnoux, 13-Feb-2018.) $)
    sitmcl $p |- ( ph -> ( F ( W sitm M ) G ) e. ( 0 [,] +oo ) ) $=
      ( co cfv cc0 cpnf eqid crefld cr cvv wcel syl vx csitm cds cof cxrs cress
      cicc csitg cxms sitmfval cxp cres cle cordt crest csigagen cxmu xrge0base
      vm crrh ctopn xrge0topn eqcomi xrge00 cvsca wceq ovex ax-xrsvsca ressvsca
      ax-mp csca ax-xrssca resssca fveq2i ovexd cbs cdm cuni wf sibff wb xmstps
      c0g ctps tpsuni 3syl mpbird cmeas crn dmexg uniexg ofresid cpsmet xmsxmet
      cxmet xmetpsmet psmetxrge0 xrge0tps a1i cha cmopn xmstopn methaus eqeltrd
      feq3 ct1 haust1 cmnd mndidcl syl2anc eqtrdi sibfof rebase xpeq12i reseq2i
      xmet0 ccmn xrge0cmn crrext rerrext eqeltrri cv cico w3a cid rrhre imaeq1i
      cima wss cxr 0re pnfxr icossre mp2an resiima eqtri icossicc eqsstri sseli
      3ad2ant2 simp3 ge0xmulcl sitgclg ) ABCEDUBKKBCEUCLZUDKZUEMNUGKZUFKZDUHKZL
      UUFAUUDBCDUIEUUDOGHIJUJAUAUUFPUCLZQQUKZULUMUNLUUFUOKZUPLZUQUSUUEPPUTLZUUK
      DRUUGMURUUGVALUUKVBVCUULOVDUUFRSZUQUUGVELVFMNUGVGZUUFUQUEUUGRUUGOZVHVIVJP
      UUGVKLZUTUUNPUUQVFUUOUUFPUEUUGRUUPVLVMVJZVNAUEUUFUFVOHAUUEBCUUDEVPLZUUSUK
      ZULZUDKUUHVQADVQZVRZUUSUUDBCRAUVCUUSBVSZUVCEVALZVRZBVSZAUUSUVEUPLZEVELZBE
      VKLUTLZUVEDUIEEWCLZUUSOZUVEOZUVHOZUVKOZUVIOZUVJOZGHIVTAUUSUVFVFZUVDUVGWAA
      EUISZEWDSZUVRGEWBZUUSUVEEUVLUVMWEWFZUUSUVFUVCBXETWGAUVCUUSCVSZUVCUVFCVSZA
      UUSUVHUVICUVJUVEDUIEUVKUVLUVMUVNUVOUVPUVQGHJVTAUVRUWCUWDWAUWBUUSUVFUVCCXE
      TWGADWHWIVRZSUVBRSUVCRSHDUWEWJUVBRWKWFWLAUUSUUFUVAUVHUVIBCUVJUVEUUGDUIEUV
      KUVLUVMUVNUVOUVPUVQGHIURAUVSUVTGUWATAUVAUUSWMLSZUUTUUFUVAVSAUVSUVAUUSWOLS
      ZUWFGUVAEUUSUVLUVAOZWNZUVAUUSWPWFUVAUUSWQTJUUGWDSAWRWSZAUVEWTSUVEXFSAUVEU
      VAXALZWTAUVSUVEUWKVFGUVAUVEEUUSUVMUVLUWHXBTAUVSUWGUWKWTSGUWIUVAUWKUUSUWKO
      XCWFXDUVEXGTAUVKUVKUVAKZMUUGWCLAUWGUVKUUSSZUWLMVFAUVSUWGGUWITAEXHSUWMFUUS
      EUVKUVLUVOXITUVKUVAUUSXPXJVDXKXLXDUURUUJPVPLZUWNUKUUIQUWNQUWNXMXMXNXOUWJU
      UGXQSAXRWSUUQXSSAPUUQXSUURXTYAWSAUSYBZUUMMNYCKZYHZSZUAYBZUUFSZYDUWOUUFSZU
      WTUWOUWSUQKUUFSUWRAUXAUWTUWQUUFUWOUWQUWPUUFUWQYEQULZUWPYHZUWPUUMUXBUWPYFY
      GUWPQYIZUXCUWPVFMQSNYJSUXDYKYLMNYMYNQUWPYOVJYPMNYQYRYSYTAUWRUWTUUAUWOUWSU
      UBXJUUCXD $.
  $}

  ${
    $d f g M $.  $d f g W $.  $d f g ph $.
    sitmf.0 $e |- ( ph -> W e. Mnd ) $.
    sitmf.1 $e |- ( ph -> W e. *MetSp ) $.
    sitmf.2 $e |- ( ph -> M e. U. ran measures ) $.
    $( The integral metric as a function.  (Contributed by Thierry Arnoux,
       13-Mar-2018.) $)
    sitmf $p |- ( ph -> ( W sitm M ) :
      ( dom ( W sitg M ) X. dom ( W sitg M ) ) --> ( 0 [,] +oo ) ) $=
      ( vf vg csitg co cdm wf cv cfv wcel wral wa cxms eqid adantr cxp cc0 cpnf
      cicc csitm cds cof cxrs cress cmpo cmeas cuni simprl simprr sitmfval cmnd
      crn sitmcl eqeltrrd ralrimivva fmpo sylib sitmval feq1d mpbird ) ACBIJKZV
      FUAZUBUCUDJZCBUEJZLVGVHGHVFVFGMZHMZCUFNZUGJUHVHUIJBIJNZUJZLZAVMVHOZHVFPGV
      FPVOAVPGHVFVFAVJVFOZVKVFOZQZQZVJVKVIJVMVHVTVLVJVKBRCVLSZACROVSETZABUKUQUL
      OVSFTZAVQVRUMZAVQVRUNZUOVTVJVKBCACUPOVSDTWBWCWDWEURUSUTGHVFVFVMVHVNVNSVAV
      BAVGVHVIVNAVLGHBRCWAEFVCVDVE $.
$(
    @d f g h x y M @.  @d f g h x y W @.  @d f g h x y ph @.
    @( The integral metric is a pseudo metric on the simple functions.
       (Contributed by Thierry Arnoux, 14-Mar-2018.) @)
    sitmpsmet @p |- ( ph -> ( W sitm M ) e. ( PsMet ` dom ( W sitg M ) ) ) @=
      ( vx vy co cxr wf cc0 wceq cxad wa cfv wcel eqid cvv syl vf vg vh cdm cxp
      csitg csitm cv cle wbr wral cpsmet cpnf wss sitmf iccssxr fss sylancl cds
      cicc cof cxrs cress cxms cmeas crn cuni simpr sitmfval csn cmpt ctopn wfn
      adantr cbs csigagen cvsca csca crrh c0g sibff ffn dmexg uniexg 3syl inidm
      eqidd offval cres ffvelcdmda xmstps tpsuni ad2antrr eleqtrrd ovres
      syl2anc ctps cxmet xmsxmet xmet0 eqtrd xrge0base xrge00 xrge0tps a1i cmnd
      xrge0cmn
      ccmn ax-mp cslmd ct1 cha haust1 mp1i biimpar simprl ofresid cmpo fovcdmda
      feq3 fnov simprr sylibr ralrimivva rnmposs df-f eqeltrd sibfof cxmu ovex
      jca off mp2an eqtri 0xr wb adantlr ralrimiva offn ofval mpteq2dva eqtr4di
      eqtr3d fconstmpt fveq2d cordt crest xrge0topn eqcomi xrge0slmod xrge0haus
      cmnmnd sitg0 eqeltrid xmetf sylib xmetge0 syl3anc elxrge0 eqsstrd xmstopn
      rneq methaus mndidcl eqtrdi adantl eqeltrrd ax-xrsvsca ressvsca ge0xaddcl
      cmopn rgen2a xaddf mpbi reseq1i resmpo fnmpo 0le0 pnfge elicc1 mpbir3an
      w3a pnfxr xaddrid xrge0le comnd xrge0omnd xmstri2 syl13anc ofrfval mpbird
      cofr sitgle xrge0plusg sitgadd breqtrd oveq12d 3brtr4d ispsmet mp2b ) ACB
      UFIZUDZUXBUEZJCBUGIZKZUAUHZUXFUXDIZLMZUXFUBUHZUXDIZUCUHZUXFUXDIZUXKUXIUXD
      IZNIZUIUJZUCUXBUKUBUXBUKZOZUAUXBUKZOZUXDUXBULPQZAUXEUXRAUXCLUMUTIZUXDKUYA
      JUNZUXEABCDEFUOLUMUPZUXCUYAJUXDUQURAUXQUAUXBAUXFUXBQZOZUXHUXPUYEUXGUXFUXF
      CUSPZVAZIZVBUYAVCIZBUFIZPZLUYEUYFUXFUXFBVDCUYFRZACVDQZUYDEVNZABVEVFVGZQZU
      YDFVNZAUYDVHZUYRVIUYEUYKBUDZVGZLVJUEZUYJPZLUYEUYHVUAUYJUYEUYHGUYTGUHZUXFP
      ZVUDUYFIZVKZVUAUYEGUYTUYTVUDVUDUYFUYTUXFUXFSSUYEUYTCVLPZVGZUXFKZUXFUYTVMZ
      UYECVOPZVUGVPPZCVQPZUXFCVRPVSPZVUGBVDCCVTPZVUKRZVUGRZVULRZVUORZVUMRZVUNRZ
      UYNUYQUYRWAZUYTVUHUXFWBTZVVCUYEUYPUYSSQZUYTSQZUYQBUYOWCZUYSSWDZWEZVVHUYTW
      FZUYEVUCUYTQZOZVUDWGZVVLWHUYEVUFGUYTLVKVUAUYEGUYTVUELVVKVUDVUDUYFVUKVUKUE
      ZWIZIZVUELVVKVUDVUKQZVVPVVOVUEMVVKVUDVUHVUKUYEUYTVUHVUCUXFVVBWJAVUKVUHMZU
      YDVVJAUYMCWQQZVVQECWKZVUKVUGCVUPVUQWLZWEWMWNZVWAVUDVUDVUKVUKUYFWOWPVVKVVN
      VUKWRPQZVVPVVOLMAVWBUYDVVJAUYMVWBEVVNCVUKVUPVVNRZWSZTZWMVWAVUDVVNVUKWTWPU
      UCUUAGUYTLUUDUUBXAUUEAVUBLMUYDAUYAUIUUFPUYAUUGIZVPPZUYIVQPZUYIVRPVSPZVWFB
      WQUYILXBUYIVLPZVWFUUHUUIZVWGRZXCVWHRZVWIRZUYIWQQZAXDXEZFVWPUYIXFQZAUYIXHQ
      ZVWQXGUYIUULXIXEUUMVNXAXAUYEUXOUBUCUXBUXBUYEUXIUXBQZUXKUXBQZOZOZUXFUXIUYG
      IZUYJPZUXKUXFUYGIZUYJPZUXKUXIUYGIZUYJPZNIZUXJUXNUIVXBVXDVXEVXGNVAIZUYJPVX
      IUIVXBUYAVWGVWHVXCVXJVWIVWFUIBXJUYILXBVWKVWLXCVWMVWNUYIXJQVXBUUJXEZUYEUYP
      VXAUYQVNZVWOVXBXDXEZVXKVXBVWFVWJXKVWKVWJXLQVWJXKQVXBUUKVWJXMXNZUUNVXBVXCU
      XFUXIVVNVAZIUYJUDZVXBUYTVUKUYFUXFUXISVXBVVQVUIUYTVUKUXFKZVXBVVRVVQVXBUYMV
      VRUYEUYMVXAUYNVNZVVSTZVVTTZVXBVUKVULVUMUXFVUNVUGBVDCVUOVUPVUQVURVUSVUTVVA
      VXRVXLUYEUYDVXAUYRVNZWAVVQVXQVUIVUKVUHUYTUXFXTXOWPZVXBVVQUYTVUHUXIKZUYTVU
      KUXIKZVXTVXBVUKVULVUMUXIVUNVUGBVDCVUOVUPVUQVURVUSVUTVVAVXRVXLUYEVWSVWTXPZ
      WAZVVQVYDVYCVUKVUHUYTUXIXTXOWPZVXBUYPVVDVVEVXLVVFVVGWEZXQVXBVUKUYAVVNVULV
      UMUXFUXIVUNVUGUYIBVDCVUOVUPVUQVURVUSVUTVVAVXRVXLVYAXBVXSAVVMUYAVVNKZUYDVX
      AAVVNVVMVMZVVNVFZUYAUNZOVYIAVYJVYLAVVMJVVNKZVYJAVWBVYMVWEVVNVUKUUOTZVVMJV
      VNWBTZAVYKGHVUKVUKVUCHUHZVVNIZXRZVFZUYAAVVNVYRMZVYKVYSMAVYJVYTVYOGHVUKVUK
      VVNYAUUPVVNVYRUVBTAVYQUYAQZHVUKUKGVUKUKVYSUYAUNAWUAGHVUKVUKAVUCVUKQZVYPVU
      KQZOZOZVYQJQZLVYQUIUJZOWUAWUEWUFWUGAVUCVYPJVUKVUKVVNVYNXSWUEVWBWUBWUCWUGA
      VWBWUDVWEVNAWUBWUCXPAWUBWUCYBVUCVYPVVNVUKUUQUURYKVYQUUSYCYDGHVUKVUKVYQUYA
      VYRVYRRYETUUTYKVVMUYAVVNYFYCWMZVYEVXMVXBVUGXLQZVUGXKQAWUIUYDVXAAVUGVVNUVK
      PZXLAUYMVUGWUJMEVVNVUGCVUKVUQVUPVWCUVATAVWBWUJXLQVWEVVNWUJVUKWUJRUVCTYGWM
      VUGXMTZVXBVUOVUOVVNIZLUYIVTPZVXBVWBVUOVUKQZWULLMVXBUYMVWBVXRVWDTVXBCXFQZW
      UNAWUOUYDVXADWMVUKCVUOVUPVUSUVDTVUOVVNVUKWTWPXCUVEZYHYGVXBVXJVXEVXGNUYAUY
      AUEZWIZVAIVXPVXBUYTUYANVXEVXGSVXBGHUYTUYTUYTUYFVUKVUKUYAUXKUXFSSVXBWUDOVY
      QVUCVYPUYFIZUYAWUDVYQWUSMVXBVUCVYPVUKVUKUYFWOUVFVXBVUCVYPUYAVUKVUKVVNWUHX
      SUVGZVXBVVQUYTVUHUXKKZUYTVUKUXKKZVXTVXBVUKVULVUMUXKVUNVUGBVDCVUOVUPVUQVUR
      VUSVUTVVAVXRVXLUYEVWSVWTYBZWAZVVQWVBWVAVUKVUHUYTUXKXTXOWPZVYBVYHVYHVVIYLV
      XBGHUYTUYTUYTUYFVUKVUKUYAUXKUXISSWUTWVEVYGVYHVYHVVIYLVYHXQVXBUYAUYAWURVWJ
      VPPZYIVXEVXGVWIVWJUYIBXHUYILXBVWJRZWVFRZXCUYASQYIVWHMLUMUTYJUYAYIVBUYISUY
      IRUVHUVIXIZVWNVWRVXBXGXEVXLVXBVXEUXKUXFVXOIVXPVXBUYTVUKUYFUXKUXFSWVEVYBVY
      HXQVXBVUKUYAVVNVULVUMUXKUXFVUNVUGUYIBVDCVUOVUPVUQVURVUSVUTVVAVXRVXLWVCXBV
      XSWUHVYAVXMWUKWUPYHYGZXBVXMVXBWURWUQVMZWURVFUYAUNZOWUQUYAWURKVXBWVKWVLVUC
      VYPNIZUYAQZHUYAUKGUYAUKZWVKVXBWVNGHUYAVUCVYPUVJUVLZGHUYAUYAWVMWURUYAWURGH
      JJWVMXRZWUQWIZGHUYAUYAWVMXRZNWVQWUQNJJUEZVMZNWVQMWVTJNKWWAUVMWVTJNWBXIGHJ
      JNYAUVNUVOUYBUYBWVRWVSMUYCUYCGHJJUYAUYAWVMUVPYMYNZUVQXNWVOWVLVXBWVPGHUYAU
      YAWVMUYAWURWWBYEXNYKWUQUYAWURYFYCVXBVXGUXKUXIVXOIVXPVXBUYTVUKUYFUXKUXISWV
      EVYGVYHXQVXBVUKUYAVVNVULVUMUXKUXIVUNVUGUYIBVDCVUOVUPVUQVURVUSVUTVVAVXRVXL
      WVCXBVXSWUHVYEVXMWUKWUPYHYGZVXMVXNLLWURIZWUMMVXBWWDLWUMWWDLLNIZLLUYAQZWWF
      WWDWWEMWWFLJQZLLUIUJZLUMUIUJZYOUVRWWGWWIYOLUVSXIWWGUMJQWWFWWGWWHWWIUWBYPY
      OUWCLUMLUVTYMUWAZWWJLLUYAUYANWOYMWWGWWELMYOLUWDXIYNXCYNXEYHYGUWEUYIUWFQVX
      BUWGXEVXBVXCVXJUIUWLUJVUDVUCUXIPZUYFIZVUCUXKPZVUDUYFIZWWMWWKUYFIZNIZUIUJZ
      GUYTUKVXBWWQGUYTVXBVVJOZUYMWWMVUKQVVPWWKVUKQWWQVXBUYMVVJVXRVNVXBUYTVUKVUC
      UXKWVEWJUYEVVJVVPVXAVWAYQVXBUYTVUKVUCUXIVYGWJVUDWWKWWMUYFCVUKVUPUYLUWHUWI
      YRVXBGUYTUYTWWLWWPUIUYTVXCVXJSSVXBUYTUYTUYFUYTUXFUXISSUYEVUJVXAVVCVNZVXBV
      YCUXIUYTVMVYFUYTVUHUXIWBTZVYHVYHVVIYSVXBUYTUYTNUYTVXEVXGSSVXBUYTUYTUYFUYT
      UXKUXFSSVXBWVAUXKUYTVMWVDUYTVUHUXKWBTZWWSVYHVYHVVIYSZVXBUYTUYTUYFUYTUXKUX
      ISSWXAWWTVYHVYHVVIYSZVYHVYHVVIYSVYHVYHVVIVXBUYTUYTVUDWWKUYFUYTUXFUXISSVUC
      WWSWWTVYHVYHVVIUYEVVJVUDVUDMVXAVVLYQZWWRWWKWGZYTVXBUYTUYTWWNWWONUYTVXEVXG
      SSVUCWXBWXCVYHVYHVVIVXBUYTUYTWWMVUDUYFUYTUXKUXFSSVUCWXAWWSVYHVYHVVIWWRWWM
      WGZWXDYTVXBUYTUYTWWMWWKUYFUYTUXKUXISSVUCWXAWWTVYHVYHVVIWXFWXEYTYTUWJUWKUW
      MVXBUYANWVFYIVXEVXGVWIVWJBXJUYILXBWVGWVHXCWVIVWNVXKVXLVXMVXKVXNWVJWWCUWNU
      WOUWPVXBUYFUXFUXIBVDCUYLVXRVXLVYAVYEVIVXBUXLVXFUXMVXHNVXBUYFUXKUXFBVDCUYL
      VXRVXLWVCVYAVIVXBUYFUXKUXIBVDCUYLVXRVXLWVCVYEVIUWQUWRYDYKYRYKUXASQUXBSQUX
      TUXSYPCBUFYJUXASWCUAUBUCUXDSUXBUWSUWTYC @.
$)
  $}

$(
  @{
    @( The metric identification for simple functions. @)
    sitmmetid @p |- ( ( W e. V /\ M e. U. ran measures ) ->
      ( ~Met ` ( W sitm M ) ) = ( ( _I |` B ) ~ae M ) ) @=
      ? @.
  @}

  @{
    sitmmet.1 @e |- B = ( Base ` W ) @.
    @( The integral metric is a metric for the equivalence classes of simple
       functions equal almost everywhere. @)
    sitmmet @p |- ( ( W e. V /\ M e. U. ran measures ) -> ( W sitm M ) e.
     ( *Met ` ( dom ( W sitg M ) /. ( ( _I |` B ) ~ae M ) ) ) ) @=
      ? @.
  @}
$)

  ${
    $d w m $.
    $( Define the Bochner integral as the extension by continuity of the
       Bochnel integral for simple functions.

       Bogachev first defines 'fundamental in the mean' sequences, in
       definition 2.3.1 of [Bogachev] p. 116, and notes that those are actually
       Cauchy sequences for the pseudometric ` ( w sitm m ) ` .

       He then defines the Bochner integral in chapter 2.4.4 in [Bogachev]
       p. 118.  The definition of the Lebesgue integral, ~ df-itg .

       (Contributed by Thierry Arnoux, 13-Feb-2018.) $)
    df-itgm $a |- itgm = ( w e. _V , m e. U. ran measures |->
      ( ( ( metUnif ` ( w sitm m ) ) CnExt ( UnifSt ` w ) ) ` ( w sitg m ) ) )
      $.
  $}

$(
  @{
    @d w m f e n i @.
    @( TODO with the previous definition, fundamental sequences shall be the
       Cauchy sequences for ` ( W sitm M ) ` : ` U. ( Cau `` ( W sitm M ) ) `

       Define the 'fundamental in the mean' sequences, in the sense of the
       definition 2.3.1 of [Bogachev] p. 116.  (Contributed by Thierry Arnoux,
       21-Oct-2017.) @)
    df-fndm @a |- Fundm = ( w e. _V , m e. U. ran measures |-> { f e. ( dom (
      w sitg m ) ^m NN ) | A. e e. RR+ E. n e. ZZ A. i e. ( ZZ>= ` n )
      ( ( RR*s sitg m ) ` ( ( f ` n ) ( dist ` w ) ( f ` i ) ) ) <_ e } ) @.
  @}

  @{
    @d f g h m n w x @.
    @( Old definition @)
    @( Define the Bochner integral, following definition 2.4.4 in [Bogachev]
       p. 118.  The definition of the Lebesgue integral, ~ df-itg .
       (Contributed by Thierry Arnoux, 21-Oct-2017.) @)
    df-itgm @a |- itgm = ( w e. _V , m e. U. ran measures |-> ( f e. ( ( Base `
      w ) ^m U. dom m ) |-> U. ran ( g e. { h e. ( w Fundm m ) | A. x e. U. dom
      m ( n e. NN |-> ( ( h ` n ) ` x ) ) ( ~~>t ` ( TopSet ` w ) ) ( f ` x ) }
      |-> ( ( ~~>t ` ( TopSet ` w ) ) ` ( ( w sitg m ) ` ( g ` n ) ) ) ) ) ) @.
  @}
$)

