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
      ci cmpt csu citg oveq1d fveq2d breq2d pm5.32da eleq2d anbi1d wceq adantrr
      bitrd wn eqidd ifbieq12d2 mpteq2dv oveq2d sumeq2sdv eqid dfitg 3eqtr4g )
      AJUAUBKZUGILUCKZBMBLZCUDZJEVJNKZOPZQUEZRZVNJUFZUHZSPZTKZIUIVIVJBMVKDUDZJF
      VJNKZOPZQUEZRZWCJUFZUHZSPZTKZIUIBCEUJBDFUJAVIVTWIIAVSWHVJTAVRWGSABMVQWFAV
      PWEVNJWCJAVPVLWDRWEAVLVOWDAVLRZVNWCJQWJVMWBOWJEFVJNHUKULZUMUNAVLWAWDACDVK
      GUOUPUSAVLVNWCUQVOWKURAVPUTRJVAVBVCULVDVEBCEVNIVNVFVGBDFWCIWCVFVGVH $.
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
    $d f g m w x $.
    $( Define the integral metric for simple functions, as the integral of the
       distances between the function values.  Since distances take
       non-negative values in ` RR* ` , the range structure for this integral
       is ` ( RR*s |``s ( 0 [,] +oo ) ) ` .  See definition 2.3.1 of [Bogachev]
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
      co cv cdif wral cdm cmbfm crab cmpt cgsu wceq elex syl c0g ctopn csigagen
      wa csca crrh cvsca fveq2 fveq2d fveq2i eqtri syl6eqr oveq2d sneqd difeq2d
      raleqdv anbi2d rabeqbidv id fveq1d oveq123d mpteq12dv oveq12d dmeq oveq1d
      eqidd fveq1 eleq1d ralbidv simpl df-sitg ovex rabex mptex ovmpt2 syl2anc
      mpteq2dva ) ALUDUEZJUFUGUHZUELJUIURFGUSZUGZUJUEZXIUKBUSZULZUMZJUNZUOUPUQU
      RZUEZBXJMULZUTZVAZVMZGJVBZDVCURZVDZLBFUSZUGZXRUTZYEUKXMUMZJUNZHUNZXLEURZV
      EZVFURZVEZVGALKUEXGTLKVHVIUAUBUCLJUDXHFXKXNUCUSZUNZXPUEZBXJUBUSZVJUNZULZU
      TZVAZVMZGYOVBZYRVKUNZVLUNZVCURZVDZYRBYFYTUTZYHYOUNZYRVNUNZVOUNZUNZXLYRVPU
      NZURZVEZVFURZVEYNUIFXKYQBXSVAZVMZGUUDDVCURZVDZLBYGUUJHUNZXLEURZVEZVFURZVE
      YRLVGZFUUHUUQUVAUVEUVFUUCUUSGUUGUUTUVFUUFDUUDVCUVFUUFLVKUNZVLUNZDUVFUUEUV
      GVLYRLVKVQVRDIVLUNUVHPIUVGVLOVSVTWAWBUVFUUBUURXKUVFYQBUUAXSUVFYTXRXJUVFYS
      MUVFYSLVJUNMYRLVJVQQWAWCZWDWEWFWGUVFYRLUUPUVDVFUVFWHUVFBUUIUUOYGUVCUVFYTX
      RYFUVIWDUVFUUMUVBXLXLUUNEUVFUUNLVPUNEYRLVPVQRWAUVFUUJUULHUVFUULLVNUNZVOUN
      HUVFUUKUVJVOYRLVNVQVRSWAWIUVFXLWOWJWKWLWKYOJVGZFUVAUVEYDYMUVKUUSYAGUUTYCU
      VKUUDYBDVCYOJWMWNUVKUURXTXKUVKYQXQBXSUVKYPXOXPXNYOJWPWQWRWFWGUVKUVDYLLVFU
      VKBYGUVCYKUVKXLYGUEZVMZUVBYJXLEUVMUUJYIHUVMYHYOJUVKUVLWSWIVRWNXFWBWKBUBFG
      UCWTFYDYMYAGYCYBDVCXAXBXCXDXE $.

    $( The predicate " ` F ` is a simple function" relative to the Bochner
       integral.  (Contributed by Thierry Arnoux, 19-Feb-2018.) $)
    issibf $p |- ( ph -> ( F e. dom ( W sitg M ) <-> ( F e. ( dom M MblFnM S )
        /\ ran F e. Fin /\ A. x e. ( ran F \ { .0. } ) ( M ` ( `' F " { x } ) )
        e. ( 0 [,) +oo ) ) ) ) $=
      ( vg vf csitg cdm wcel cmbfm crn cfn ccnv csn cima cfv cc0 cpnf cico cdif
      co cv wral wa w3a crab cmpt cgsu cvv sitgval dmeqd eqid dmmpt syl6eq wceq
      eleq2d difeq1d cnveq imaeq1d fveq2d oveq1d mpteq12dv oveq2d eleq1d syl6bb
      rneq elrab ovex biantru syl6bbr raleqbidv anbi12d 3anass ) AFKIUCUQZUDZUE
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
        cc0 cico cdif wral w3a cmeas csiga dmmeas syl csigagen cvv fvex eqeltri
        a1i sgsiga syl5eqel cmpt wceq fconstmpt cgrp grpidcl ctps tpsuni unieqi
        ctopn unisg syl5eq eqtr4d eleqtrd mbfmcst c0 xpeq1 0xp syl6eq rneqd rn0
        mp1i 0fin syl6eqel wne rnxp snfi pm2.61ine noel 0dif difid eleq2i mtbir
        difeq1d pm2.21i adantl ralrimiva 3jca issibf mpbird ) AGUBZUCZJUDZUEZIG
        UFUGUBUHXOXLCUIUGUHZXOUJZUKUHZXOULUAUMZUDUNGUOUQUPURUGUHZUAXQXNUSZUTZVA
        AXPXRYBAUAJXLCXOAGVBUJUCUHXLVCUJUCZUHRGVDVEACFVFUOZYCMAFVGFVGUHZAFIWAUO
        VGLIWAVHVIZVJVKVLXOUAXMJVMVNAUAXMJVOVJAJBCUCZAIVPUHJBUHTBIJKNVQVEABFUCZ
        YGAIVRUHBYHVNSBFIKLVSVEAYGYDUCZYHCYDMVTYEYIYHVNAYFFVGWBWMWCWDWEWFXRAXRX
        MWGXMWGVNZXQWGUKYJXQWGUJWGYJXOWGYJXOWGXNUEWGXMWGXNWHXNWIWJWKWLWJZWNWOXM
        WGWPZXQXNUKXMXNWQZJWRWOWSVJAXTUAYAXSYAUHZXTAYNXTYNXSWGUHXSWTYAWGXSYAWGV
        NXMWGYJYAWGXNUSWGYJXQWGXNYKXEXNXAWJYLYAXNXNUSWGYLXQXNXNYMXEXNXBWJWSXCXD
        XFXGXHXIAUABCDXOEFGHIJKLMNOPQRXJXK $.
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
        ( cdm cuni wf cmeas crn wcel csiga dmmeas syl csigagen cfv cvv fvex a1i
        ctopn syl5eqel sgsiga sibfmbl mbfmf wceq unieqi unisg syl5eq feq3 mpbid
        wb ) AHUAZUBZCUBZEUCZVHGUBZEUCZAVGCEAHUDUEUBUFVGUGUEUBZUFSHUHUIACGUJUKZ
        VMNAGULAGJUOUKZULMVOULUFAJUOUMUNUPZUQUPABCDEFGHIJKLMNOPQRSTURUSAVIVKUTV
        JVLVFAVIVNUBZVKCVNNVAAGULUFVQVKUTVPGULVBUIVCVIVKVHEVDUIVE $.

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
             /\ ( X =/= .0. \/ Y =/= .0. ) )
           -> ( M ` ( ( `' F " { X } ) i^i ( `' G " { Y } ) ) )  e. RR ) $=
          ( crn wcel w3a wne wo wa ccnv csn cima cin cfv cxr cc0 cr cle wbr clt
          cpnf cicc co cdm cmeas cuni measbasedom sylib 3ad2ant1 csiga csigagen
          dmmeas syl ct1 sgsiga syl5eqel sibfmbl ccld wss ctps ctop cldssbrsiga
          cmbfm tpstop 3syl syl6sseqr wf sibff frn simp2 sseldd t1sncld syl2anc
          eqid mbfmcnvima simp3 inelsiga syl3anc measvxrge0 elxrge0 simplbi 0re
          adantr a1i simprbi pnfxr inss1 measssd cico cdif simpl1 anim1i sylibr
          eldifsn sibfima wb elico2 mp2an xrlelttrd inss2 jaodan xrre3 syl22anc
          simp3bi ) ALEUGZUHZMFUGZUHZUIZLNUJZMNUJZUKZULZEUMLUNZUOZFUMMUNZUOZUPZ
          IUQZURUHZUSUTUHZUSUUBVAVBZUUBVDVCVBZUUBUTUHYLUUCYOYLUUBUSVDVEVFZUHZUU
          CYLIIVGZVHUQUHZUUAUUIUHZUUHAYIUUJYKAIVHUGVIUHZUUJUBIVJVKVLZYLUUIVMUGV
          IZUHZYRUUIUHZYTUUIUHZUUKAYIUUOYKAUULUUOUBIVOVPVLZYLYQUUICEUURAYICUUNU
          HYKACHVNUQZUUNQAHVQUFVRVSVLZAYIEUUICWFVFZUHYKABCDEGHIJKNOPQRSTUAUBUCV
          TVLYLHWAUQZCYQAYIUVBCWBYKAUVBUUSCAKWCUHHWDUHUVBUUSWBUEHKPWGHWEWHQWIVL
          ZYLHVQUHZLHVIZUHYQUVBUHAYIUVDYKUFVLZYLYHUVELAYIYHUVEWBZYKAUUIVIZUVEEW
          JUVGABCDEGHIJKNOPQRSTUAUBUCWKUVHUVEEWLVPVLAYIYKWMZWNLHUVEUVEWQZWOWPWN
          WRZYLYSUUICFUURUUTAYIFUVAUHYKABCDFGHIJKNOPQRSTUAUBUDVTVLYLUVBCYSUVCYL
          UVDMUVEUHYSUVBUHUVFYLYJUVEMAYIYJUVEWBZYKAUVHUVEFWJUVLABCDFGHIJKNOPQRS
          TUAUBUDWKUVHUVEFWLVPVLAYIYKWSZWNMHUVEUVJWOWPWNWRZYRYTUUIWTXAZUUAUUIIX
          BWPZUUHUUCUUEUUBXCZXDVPZXFUUDYPXEXGYLUUEYOYLUUHUUEUVPUUHUUCUUEUVQXHVP
          XFYLYMUUFYNYLYMULZUUBYRIUQZVDYLUUCYMUVRXFUVSUVTUUGUHZUVTURUHZUVSUUJUU
          PUWAYLUUJYMUUMXFZYLUUPYMUVKXFZYRUUIIXBWPUWAUWBUSUVTVAVBZUVTXCXDVPVDUR
          UHZUVSXIXGUVSUUAYRUUIIUWCYLUUKYMUVOXFUWDUUAYRWBUVSYRYTXJXGXKUVSUVTUSV
          DXLVFZUHZUVTVDVCVBZUVSALYHNUNZXMUHZUWHAYIYKYMXNUVSYIYMULUWKYLYIYMUVIX
          OLYHNXQXPALBCDEGHIJKNOPQRSTUAUBUCXRWPUWHUVTUTUHZUWEUWIUUDUWFUWHUWLUWE
          UWIUIXSXEXIUSVDUVTXTYAYGVPYBYLYNULZUUBYTIUQZVDYLUUCYNUVRXFUWMUWNUUGUH
          ZUWNURUHZUWMUUJUUQUWOYLUUJYNUUMXFZYLUUQYNUVNXFZYTUUIIXBWPUWOUWPUSUWNV
          AVBZUWNXCXDVPUWFUWMXIXGUWMUUAYTUUIIUWQYLUUKYNUVOXFUWRUUAYTWBUWMYRYTYC
          XGXKUWMUWNUWGUHZUWNVDVCVBZUWMAMYJUWJXMUHZUWTAYIYKYNXNUWMYKYNULUXBYLYK
          YNUVMXOMYJNXQXPAMBCDFGHIJKNOPQRSTUAUBUDXRWPUWTUWNUTUHZUWSUXAUUDUWFUWT
          UXCUWSUXAUIXSXEXIUSVDUWNXTYAYGVPYBYDUUBUSYEYF $.
      $}

      ${
        $d f g m w x y B $.  $d x z C $.  $d b f g p x z F $.
        $d b p x y z G $.  $d f m w H $.  $d x z J $.  $d b p x y z K $.
        $d b f g m p w x z M $.  $d f g m w S $.  $d f g m w x W $.
        $d f g m w x y .0. $.  $d b p x y z .+ $.  $d f m w .x. $.
        $d f p x y ph $.  $d b z ph $.
        sibfof.c $e |- C = ( Base ` K ) $.
        sibfof.0 $e |- ( ph -> W e. TopSp ) $.
        sibfof.1 $e |- ( ph -> .+ : ( B X. B ) --> C ) $.
        sibfof.2 $e |- ( ph -> G e. dom ( W sitg M ) ) $.
        sibfof.3 $e |- ( ph -> K e. TopSp ) $.
        sibfof.4 $e |- ( ph -> J e. Fre ) $.
        sibfof.5 $e |- ( ph -> ( .0. .+ .0. ) = ( 0g ` K ) ) $.
        $( Applying function operations on simple functions results in simple
           functions with regard to the the destination space, provided the
           operation fulfills a simple condition.  (Contributed by Thierry
           Arnoux, 12-Mar-2018.) $)
        sibfof $p |- ( ph -> ( F oF .+ G ) e. dom ( K sitg M ) ) $=
          ( vz vb vx vp vy co cdm wcel ctopn cfv csigagen cmbfm crn cfn ccnv cv
          csn cima cc0 cdif wral cuni wa wf cvv cxp ctps tpsuni syl mpbid sibff
          wceq cmeas uniexg 3syl wb eqid fvex eqtri syl6eqr a1i sgsiga syl5eqel
          feq3 syl2anc mpbird cin cun imaeq2i wfun ffun adantr ciun com wbr wss
          inss2 cnvimass sselda sibfmbl adantl eleqtrd t1sncld sseldd syl6eleqr
          cdom xp1st mbfmcnvima syl3anc ralrimiva wi sibfrn ssdomg mpi isfinite
          xp2nd csdm eqeltrd sylib c0 cr cle wdisj sylancl simpr wne wo sylanl2
          wn cof csitg cpnf cico c0g w3a cmap xpeq12d feq2d fovrnda dmexg inidm
          unieqi unisg ax-mp csiga elmapg inundif unpreima syl5eqr dmmeas iunid
          off imaiun eqtr3i c1st c2nd wfn ffn ofpreima2 ad2antrr inss1 syl5sseq
          simpll fdm syl5ss eqeltri ccld tpstop cldssbrsiga ct1 inelsiga biimpi
          ctop xpfi sdomdom domtr nfcv sigaclcuni ssralv mpsyl imafi ofrn2 ssfi
          syl5eqelr difpreima cnvimarndm difeq2i ssdif0 syl6eq 0elsiga unelsiga
          jca ismbfm csu cesum fveq2d measbasedom difss sseli sylan2 disjpreima
          mpbi sndisj sneq imaeq2d simpl disjxpin disjss1 measvuni sseldi eqtrd
          oveq12 ex necon3ad oran nne anbi12i bitri syl6ibr ralrimivva fniniseg
          notbii cop 1st2nd2 df-ov eqtr3d simplr elsn necon3bbii eqnetrrd oveq1
          eldifbd neeq1d neeq1 orbi1d imbi12d oveq2 orbi2d rspc2v mp2d syl31anc
          measge0 elrege0 sylanbrc esumpfinval 3eqtrd fsumrecl fsumge0 breqtrrd
          sibfinima 3jca cvsca csca crrh issibf ) AGHDUUAUQZKLUUBUQURUSVVGLURZK
          UTVAZVBVAZVCUQUSZVVGVDZVEUSZVVGVFZULVGZVHZVIZLVAZVJUUCUUDUQZUSZULVVLK
          UUEVAZVHZVKZVLZUUFAVVKVVMVWDAVVKVVGVVJVMZVVHVMZUUGUQUSZVVNUMVGZVIZVVH
          USZUMVVJVLZVNAVWGVWKAVWGVWFVWEVVGVOZAVWFCVVGVOZVWLAULUNVWFVWFVWFDJVMZ
          VWNCGHVPVPAVVOUNVGZCVWNVWNDABBVQZCDVOZVWNVWNVQZCDVOUGAVWPVWRCDABVWNBV
          WNANVRUSZBVWNWCZUFBJNPQVSVTZVXAUUHUUIWAZUUJABEFGIJLMNOPQRSTUAUBUCUDWB
          ZABEFHIJLMNOPQRSTUAUBUCUHWBZALWDVDVMZUSZVVHVPUSVWFVPUSZUCLVXEUUKVVHVP
          WEWFZVXHVWFUULUVCZACVWEWCVWMVWLWGACVVIVMZVWEAKVRUSCVXJWCUICVVIKUEVVIW
          HZVSVTVWEVWEVXJVVJVVJVVJWHZUUMVVIVPUSZVWEVXJWCKUTWIZVVIVPUUNUUOWJWKCV
          WEVWFVVGWOVTWAAVWEVPUSZVXGVWGVWLWGAVVJUUPVDVMZUSVXOAVVJVVJVXPVXLAVVIV
          PVXMAVXNWLWMWNZVVJVXPWEVTVXHVWEVWFVVGVPVPUUQWPWQAVWJUMVVJAVWHVVJUSZVN
          ZVWIVVNVWHVVLWRZVIZVVNVWHVVLVKZVIZWSZVVHVXSVWIVVNVXTVYBWSZVIZVYDVYEVW
          HVVNVWHVVLUURWTAVYFVYDWCZVXRAVWMVVGXAZVYGVXIVWFCVVGXBZVXTVYBVVGUUSWFX
          CUUTVXSVVHVXPUSZVYAVVHUSVYCVVHUSZVYDVVHUSAVYJVXRAVXFVYJUCLUVAVTZXCZVX
          SVYAULVXTVVQXDZVVHVVNULVXTVVPXDZVIVYNVYAULVVNVXTVVPUVDVYOVXTVVNULVXTU
          VBWTUVEVXSVYJVVQVVHUSZULVXTVLZVXTXEXQXFZVYNVVHUSVYMAVYQVXRVXTVVLXGZAV
          YPULVVLVLVYQVWHVVLXHZAVYPULVVLAVVOVVLUSZVNZVVQUODVFVVPVIZGVDZHVDZVQZW
          RZGVFZUOVGZUVFVAZVHZVIZHVFZWUIUVGVAZVHZVIZWRZXDZVVHAVVQWURWCZWUAAVWFB
          BVVPDGHVPUOAVWFBGVOZVWFVWNGVOZVXCAVWTWUTWVAWGVXABVWNVWFGWOVTWQAVWFBHV
          OZVWFVWNHVOZVXDAVWTWVBWVCWGVXABVWNVWFHWOVTWQVXHAVWQDVWPUVHZUGVWPCDUVI
          VTZUVJZXCWUBVYJWUQVVHUSZUOWUGVLZWUGXEXQXFZWURVVHUSAVYJWUAVYLXCWUBWVGU
          OWUGWUBWUIWUGUSZVNZVYJWULVVHUSZWUPVVHUSZWVGAVYJWUAWVJVYLUVKWVKAWUIVWP
          USZWVLAWUAWVJUVNZWUBWUGVWPWUIWUBWUGWUCVWPWUCWUFUVLZAWUCVWPXGWUAADURZW
          UCVWPDVVPXIAVWQWVQVWPWCUGVWPCDUVOVTUVMXCUVPXJZAWVNVNZWUKVVHEGAVYJWVNV
          YLXCZAEVXPUSWVNAEJVBVAZVXPRAJVPJVPUSAJNUTVAVPQNUTWIUVQWLWMWNXCZAGVVHE
          VCUQZUSWVNABEFGIJLMNOPQRSTUAUBUCUDXKXCWVSWUKWWAEWVSJUVRVAZWWAWUKAWWDW
          WAXGZWVNAVWSJUWDUSWWEUFJNQUVSJUVTWFXCZWVSJUWAUSZWUJVWNUSWUKWWDUSAWWGW
          VNUJXCZWVSWUJBVWNWVNWUJBUSZAWUIBBXRZXLAVWTWVNVXAXCZXMWUJJVWNVWNWHZXNW
          PXORXPXSWPWVKAWVNWVMWVOWVRWVSWUOVVHEHWVTWWBAHWWCUSWVNABEFHIJLMNOPQRST
          UAUBUCUHXKXCWVSWUOWWAEWVSWWDWWAWUOWWFWVSWWGWUNVWNUSWUOWWDUSWWHWVSWUNB
          VWNWVNWUNBUSZAWUIBBYGZXLWWKXMWUNJVWNWWLXNWPXORXPXSWPWULWUPVVHUWBXTZYA
          ZAWVIWUAAWUGWUFXQXFZWUFXEXQXFZWVIAWUGWUFXGZWWQWUCWUFXHZAWUFVEUSZWWSWW
          QYBAWUDVEUSWUEVEUSWXAABEFGIJLMNOPQRSTUAUBUCUDYCABEFHIJLMNOPQRSTUAUBUC
          UHYCWUDWUEUWEWPZWUGWUFVEYDVTYEAWXAWUFXEYHXFZWWRWXBWXAWXCWUFYFUWCWUFXE
          UWFWFWUGWUFXEUWGWPZXCWUGWUQVVHUOUOWUGUWHUWIXTYIYAVYPULVXTVVLUWJUWKXCA
          VYRVXRAVXTVVLXQXFZVVLXEXQXFZVYRAVYSWXEVYTAVVMVYSWXEYBADWUFVIZVEUSZVVL
          WXGXGVVMADXAZWXAWXHAVWQWXIUGVWPCDXBVTWXBDWUFUWLWPAVWFVWNCDGHVPVXCVXDV
          XBVXHUWMWXGVVLUWNWPZVXTVVLVEYDVTYEAVVLXEYHXFZWXFAVVMWXKWXJVVLYFYJVVLX
          EUWFVTVXTVVLXEUWGWPXCVXTVVQVVHULULVXTUWHUWIXTUWOAVYKVXRAVYCYKVVHAVYCV
          WIVVNVVLVIZVKZYKAVWMVYHVYCWXMWCVXIVYIVWHVVLVVGUWPWFWXMVWIVVGURZVKZYKW
          XLWXNVWIVVGUWQUWRVWIWXNXGWXOYKWCVVGVWHXIVWIWXNUWSUXMWJUWTAVYJYKVVHUSV
          YLVVHUXAVTYIXCVYAVYCVVHUXBXTYIYAUXCAUMVVHVVJVVGVYLVXQUXDWQWXJAVVTULVW
          CAVVOVWCUSZVNZVVRYLUSVJVVRYMXFVVTWXQVVRWUGWUQLVAZUOUXEZYLWXQVVRWURLVA
          ZWUGWXRUOUXFZWXSWXQVVQWURLAWUSWXPWVFXCUXGWXQLVVHWDVAUSZWVHWVIUOWUGWUQ
          YNZVNWXTWYAWCAWYBWXPAVXFWYBUCLUXHYJXCZWXPAWUAWVHVWCVVLVVOVVLVWBUXIUXJ
          ZWWPUXKWXQWVIWYCAWVIWXPWXDXCAWYCWXPWWSAUOWUFWUQYNZWYCWWTAUNWUDWUHVWOV
          HZVIZYNZUPWUEWUMUPVGZVHZVIZYNZWYFAGXAZUNWUDWYGYNWYIAWVAWYNVXCVWFVWNGX
          BVTUNWUDUXNUNWUDWYGGUXLYOAHXAZUPWUEWYKYNWYMAWVCWYOVXDVWFVWNHXBVTUPWUE
          UXNUPWUEWYKHUXLYOWYIWYMVNUNUPWUDWUEWYHWYLWULWUPUOVWOWUJWCZWYGWUKWUHVW
          OWUJUXOUXPWYJWUNWCZWYKWUOWUMWYJWUNUXOUXPWYIWYMUXQWYIWYMYPUXRWPUOWUGWU
          FWUQUXSUWKXCUXCUOWUGWUQVVHLUXTXTWXQWUGWXRUOAWUGVEUSZWXPAWXAWWSWYRWXBW
          WTWUFWUGUWNYOXCZWXQWVJVNZWXRYLUSZVJWXRYMXFZWXRVVSUSWYTAWUJWUDUSZWUNWU
          EUSZWUJOYQZWUNOYQZYRZXUAWXPAWUAWVJAWYEWVOYSZWYTWUIWUFUSZXUCWYTWUGWUFW
          UIWWTWXQWVJYPUYAZWUIWUDWUEXRVTWYTXUIXUDXUJWUIWUDWUEYGVTWYTVWOWYJDUQZV
          WAYQZVWOOYQZWYJOYQZYRZYBZUPBVLUNBVLZWUJWUNDUQZVWAYQZXUGWYTAXUQXUHAXUP
          UNUPBBAXUPVWOBUSWYJBUSVNAXULVWOOWCZWYJOWCZVNZYTZXUOAXVBXUKVWAAXVBXUKV
          WAWCAXVBVNXUKOODUQZVWAXVBXUKXVDWCAVWOOWYJODUYCXLAXVDVWAWCXVBUKXCUYBUY
          DUYEXUOXUMYTZXUNYTZVNZYTXVCXUMXUNUYFXVGXVBXVEXUTXVFXVAVWOOUYGWYJOUYGU
          YHUYMUYIUYJXCUYKVTWYTVVOXURVWAWYTWVNWUIDVAZVVOWCZVNZVVOXURWCWYTWUIWUC
          USZXVJWXQWUGWUCWUIWUGWUCXGWXQWVPWLXJWYTWVDXVKXVJWGWYTAWVDXUHWVEVTVWPV
          VOWUIDUYLVTWAXVJXVHVVOXURWVNXVIYPWVNXVHXURWCXVIWVNXVHWUJWUNUYNZDVAXUR
          WVNWUIXVLDWUIBBUYOUXGWUJWUNDUYPWKXCUYQVTWYTVVOVWBUSZYTVVOVWAYQWYTVVOV
          VLVWBAWXPWVJUYRVUCXVMVVOVWAULVWAUYSUYTYJVUAWYTWWIWWMXUQXUSXUGYBZYBWYT
          WVNWWIWXPAWUAWVJWVNWYEWVRYSZWWJVTWYTWVNWWMXVOWWNVTXUPXVNWUJWYJDUQZVWA
          YQZXUEXUNYRZYBUNUPWUJWUNBBWYPXULXVQXUOXVRWYPXUKXVPVWAVWOWUJWYJDVUBVUD
          WYPXUMXUEXUNVWOWUJOVUEVUFVUGWYQXVQXUSXVRXUGWYQXVPXURVWAWYJWUNWUJDVUHV
          UDWYQXUNXUFXUEWYJWUNOVUEVUIVUGVUJWPVUKABEFGHIJLMNWUJWUNOPQRSTUAUBUCUD
          UHUFUJVVAVULZWYTWYBWVGXUBWXQWYBWVJWYDXCWXPAWUAWVJWVGWYEWWOYSWUQVVHLVU
          MWPZWXRVUNVUOVUPVUQZWXQWUGWXRUOWYSXVSVURYIWXQVJWXSVVRYMWXQWUGWXRUOWYS
          XVSXVTVUSXWAVUTVVRVUNVUOYAVVBAULCVVJKVVCVAZVVGKVVDVAVVEVAZVVILVRKVWAU
          EVXKVXLVWAWHXWBWHXWCWHUIUCVVFWQ $.
      $}

      $( Value of the Bochner integral for a simple function ` F ` .
         (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
      sitgfval $p |- ( ph -> ( ( W sitg M ) ` F ) = ( W gsum ( x e. ( ran F \
        { .0. } ) |-> ( ( H ` ( M ` ( `' F " { x } ) ) ) .x. x ) ) ) ) $=
        ( vf vg cv crn csn cdif ccnv cima cfv cmpt cgsu cfn wcel cpnf cico wral
        co cc0 cdm cmbfm crab csitg cvv sitgval wceq simpr rneqd difeq1d cnveqd
        imaeq1d fveq2d oveq1d mpteq12dv oveq2d sibfmbl sibfrn sibfima ralrimiva
        jca32 rneq eleq1d cnveq raleqbidv anbi12d elrab sylibr ovex a1i fvmptd
        wa ) AUBFKBUBUDZUEZLUFZUGZWLUHZBUDZUFZUIZIUJZGUJZWQEURZUKZULURKBFUEZWNU
        GZFUHZWRUIZIUJZGUJZWQEURZUKZULURZUCUDZUEZUMUNZXMUHZWRUIZIUJZUSUOUPURZUN
        ZBXNWNUGZUQZWKZUCIUTDVAURZVBZKIVCURVDABCDEUBUCGHIJKLMNOPQRSTVEAWLFVFZWK
        ZXCXKKULYGBWOXBXEXJYGWMXDWNYGWLFAYFVGZVHVIYGXAXIWQEYGWTXHGYGWSXGIYGWPXF
        WRYGWLFYHVJVKVLVLVMVNVOAFYDUNZXDUMUNZXHXSUNZBXEUQZWKZWKFYEUNAYIYJYLACDE
        FGHIJKLMNOPQRSTUAVPACDEFGHIJKLMNOPQRSTUAVQAYKBXEAWQCDEFGHIJKLMNOPQRSTUA
        VRVSVTYCYMUCFYDXMFVFZXOYJYBYLYNXNXDUMXMFWAZWBYNXTYKBYAXEYNXNXDWNYOVIYNX
        RXHXSYNXQXGIYNXPXFWRXMFWCVKVLWBWDWEWFWGXLVDUNAKXKULWHWIWJ $.

      ${
        $d f g m w x .0. $.  $d f m w .x. $.  $d f g m w x B $.
        $d f g m x F $.  $d m G $.  $d f m w H $.  $d f g m w x y z M $.
        $d f g m w S $.  $d f g m w x W $.  $d f m x ph $.
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
           (Contributed by Thierry Arnoux, 24-Feb-2018.) $)
        sitgclg $p |- ( ph -> ( ( W sitg M ) ` F ) e. B ) $=
          ( vy vz csitg co cfv crn csn cdif ccnv cv cima cmpt cgsu sitgfval cvv
          cdm wcel rnexg difexg 3syl wa cc0 cpnf cico simpl sibfima wfun wss wi
          cr csca cbs wf crrh cioo ctg ctopn czlm cds cxp cres xpeq12i reseq12i
          fveq2i eqtri eqid cdr crrext syl5eqel rrextdrg syl syl5eqelr rrextnrg
          cnrg cnlm rrextnlm cchr wceq rrextchr syl5eqr rrextcusp cuss rrextust
          ccusp cmetu rrhf feq1i sylibr ffun cxr 0re pnfxr icossre a1i sseqtr4d
          mp2an fdm funfvima2 syl2anc imp cuni cmeas csiga cicc c0 com cdom w3a
          cfn sstri wbr wdisj cesum cpw isrnmeas simpld csigagen eqeltri sgsiga
          wral fvex sibfmbl mbfmf frn unieqi unisg syl5eq tpsuni eqtr4d sseqtrd
          ssdifd sselda eldifad simp2 eleq1 3anbi2d oveq1 eleq1d imbi12d vtoclg
          mp1i mpcom syl3anc fmptd sibfrn cnvimass dmmptss difss gsumcl eqeltrd
          ctps ssfi ) AHNLUMUNZUONBHUPZOUQZURZHUSBUTZUQVALUOZJUOZUWGFUNZVBZVCUN
          CABCEFHJKLMNOPQRSTUAUBUCUDVDAUWFCUWKNVEOPSUHAHUWCVFZVGUWDVEVGUWFVEVGU
          DHUWLVHUWDUWEVEVIVJABUWFUWJCUWKAUWGUWFVGZVKZAUWIJVLVMVNUNZVAZVGZUWGCV
          GZUWJCVGZAUWMVOZUWNAUWHUWOVGZUWQUWTAUWGCEFHJKLMNOPQRSTUAUBUCUDVPAUXAU
          WQAJVQZUWOJVFZVRUXAUWQVSAVTNWAUOZWBUOZJWCZUXBAVTUXEUXDWDUOZWCUXFAUXED
          UXDWEUPWFUOZIWGUOIWHUOZDIWIUOZIWBUOZUXKWJZWKUXDWIUOZUXEUXEWJZWKUFUXJU
          XMUXLUXNIUXDWIUEWNUXKUXEUXKUXEIUXDWBUEWNZUXOWLWMWOUXHWPUXEWPIUXDWGUEW
          NIUXDWHUEWNAUXDIWQUEAIWRVGZIWQVGAIUXDWRUEUIWSZIWTXAXBAUXDIXDUEAUXPIXD
          VGUXQIXCXAXBAUXPUXIXEVGUXQIUXIUXIWPXFXAAUXDXGUOIXGUOZVLIUXDXGUEWNAUXP
          UXRVLXHUXQIXIXAXJAUXDIXNUEAUXPIXNVGUXQIXKXAXBAUXDXLUOIXLUOZDXOUOZIUXD
          XLUEWNAUXPUXSUXTXHUXQUXKDIUXKWPUFXMXAXJXPVTUXEJUXGUAXQXRZVTUXEJXSXAAU
          WOVTUXCUWOVTVRZAVLVTVGVMXTVGUYBYAYBVLVMYCYFYDAUXFUXCVTXHUYAVTUXEJYGXA
          YEUWOUWHJYHYIYJYIUWNUWGCUWEAUWFCUWEURUWGAUWDCUWEAUWDEYKZCALVFZYKZUYCH
          WCUWDUYCVRAUYDEHALYLUPYKVGZUYDYMUPYKZVGZUCUYFUYHUYDVLVMYNUNLWCYOLUOVL
          XHUKUTZYPYQUUAULUYIULUTZUUBVKUYIYKLUOUYIUYJLUOULUUCXHVSUKUYDUUDUUJYRU
          KULLUUEUUFXAAEKUUGUOZUYGRAKVEKVEVGZAKNWGUOVEQNWGUUKUUHZYDUUIWSACEFHJK
          LMNOPQRSTUAUBUCUDUULUUMUYEUYCHUUNXAAUYCKYKZCAUYCUYKYKZUYNEUYKRUUOUYLU
          YOUYNXHAUYMKVEUUPUVKUUQANUWAVGCUYNXHUGCKNPQUURXAUUSUUTUVAUVBUVCUWQAUW
          QUWRYRZUWSAUWQUWRUVDAGUTZUWPVGZUWRYRZUYQUWGFUNZCVGZVSUYPUWSVSGUWIUWPU
          YQUWIXHZUYSUYPVUAUWSVUBUYRUWQAUWRUYQUWIUWPUVEUVFVUBUYTUWJCUYQUWIUWGFU
          VGUVHUVIUJUVJUVLUVMUWKWPZUVNAUWDYSVGUWKUSVEUWEURZVAZUWDVRZVUEYSVGACEF
          HJKLMNOPQRSTUAUBUCUDUVOVUFAVUEUWFUWDVUEUWKVFUWFUWKVUDUVPBUWFUWJUWKVUC
          UVQYTUWDUWEUVRYTYDUWDVUEUWBYIUVSUVT $.
      $}

      ${
        $d m x B $.  $d m x W $.  $d m F $.  $d m G $.  $d m x ph $.
        $d m .x. $.
        sitgclbn.1 $e |- ( ph -> W e. Ban ) $.
        sitgclbn.2 $e |- ( ph -> ( Scalar ` W ) e. RRExt ) $.
        $( Closure of the Bochner integral on a simple function.  This version
           is specific to Banach spaces, with additional conditions on its
           scalar field.  (Contributed by Thierry Arnoux, 24-Feb-2018.) $)
        sitgclbn $p |- ( ph -> ( ( W sitg M ) ` F ) e. B ) $=
          ( vx vm csca cfv cds cbs cxp cres eqid ccms wcel cmt ctps bncms cmsms
          cbn syl mstps 3syl clmod ccmn bnlmod lmodcmn cv cc0 cpnf cico co cima
          w3a 3ad2ant1 crn imassrn crrh crrext cr wf wss rrhfe frn fveq2i rneqi
          eqtr4i 3sstr4g syl5ss sseld 3adant3 simp3 lmodvscl syl3anc sitgclg
          imp ) AUCBJUEUFZUGUFWOUHUFZWPUIUJZCDUDEWOFGHIJKLMNOPQRSTWOUKZWQUKAJUL
          UMZJUNUMJUOUMAJURUMZWSUAJUPUSJUQJUTVAAWTJVBUMZJVCUMUAJVDZJVEVAUBAUDVF
          ZFVGVHVIVJZVKZUMZUCVFZBUMZVLXAXCWPUMZXHXCXGDVJBUMAXFXAXHAWTXAUAXBUSVM
          AXFXIXHAXFXIAXEWPXCAXEFVNZWPFXDVOAWOVPUFZVNZWPXJWPAWOVQUMVRWPXKVSXLWP
          VTUBWPWOWPUKZWAVRWPXKWBVAFXKFXKXKQWOWOVPWRWCWEWDXMWFWGWHWNWIAXFXHWJXC
          DWOWPBJXGLWRPXMWKWLWM $.
      $}

      ${
        sitgclcn.1 $e |- ( ph -> W e. Ban ) $.
        sitgclcn.2 $e |- ( ph -> ( Scalar ` W ) = CCfld ) $.
        $( Closure of the Bochner integral on a simple function.  This version
           is specific to Banach spaces on the complex numbers.  (Contributed
           by Thierry Arnoux, 24-Feb-2018.) $)
        sitgclcn $p |- ( ph -> ( ( W sitg M ) ` F ) e. B ) $=
          ( csca cfv ccnfld crrext cnrrext syl6eqel sitgclbn ) ABCDEFGHIJKLMNOP
          QRSTUAAJUCUDUEUFUBUGUHUI $.
      $}

      ${
        sitgclre.1 $e |- ( ph -> W e. Ban ) $.
        sitgclre.3 $e |- ( ph -> ( Scalar ` W ) = ( CCfld |`s RR ) ) $.
        $( Closure of the Bochner integral on a simple function.  This version
           is specific to Banach spaces on the real numbers.  (Contributed by
           Thierry Arnoux, 24-Feb-2018.) $)
        sitgclre $p |- ( ph -> ( ( W sitg M ) ` F ) e. B ) $=
          ( csca cfv ccnfld cr cress co crrext rerrext syl6eqel sitgclbn ) ABCD
          EFGHIJKLMNOPQRSTUAAJUCUDUEUFUGUHUIUBUJUKUL $.
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
        gsum0 syl6eq ) AGUBUCZJUDZUEZIGUFUGUHIUAVMUPZVLUIZVMUJUAUKZUDULGUHEUHVP
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
        ( vg vx csitg co cdm wfn crn wss wa wfun cfn wcel ccnv csn cima cfv cc0
        wf cpnf cico cdif wral cmbfm crab cmpt cgsu funmpt sitgval funeqd funfn
        cv mpbiri sylib ralrimiva r19.21bi fnfvrnss syl2anc jca df-f sylibr ) A
        JHUCUDZWAUEZUFZWAUGBUHZUIWBBWAURAWCWDAWAUJZWCAWEEUAVKZUGZUKULWFUMUBVKZU
        NZUOHUPUQUSUTUDULUBWGKUNZVAVBUIUAHUECVCUDVDZJUBEVKZUGWJVAWLUMWIUOHUPFUP
        WHDUDVEVFUDZVEZUJEWKWMVGAWAWNAUBBCDEUAFGHIJKLMNOPQRSVHVIVLWAVJVMZAWCWLW
        AUPBULZEWBVBWDWOAWPEWBAWPEWBAWPEWBTVNVOVNEWBBWAVPVQVRWBBWAVSVT $.
    $}

$(
    @{
      sitgadd.1 @e |- ( ph -> W e. TopSp ) @.
      sitgadd.2 @e |- ( ph -> ( W |`v ( H " ( 0 [,) +oo ) ) ) e. SLMod ) @.
      sitgadd.3 @e |- ( ph -> J e. Fre ) @.
      sitgadd.4 @e |- ( ph -> F e. dom ( W sitg M ) ) @.
      sitgadd.5 @e |- ( ph -> G e. dom ( W sitg M ) ) @.
      @{
        sitgadd.7 @e |- .+ = ( +g ` W ) @.
        @( Lemma for ~ sitgadd . @)
        sitgaddlem @p |- ( ph -> ( ( W  sitg M ) ` F ) 
           = ( W gsum ( p e. ( ( ran F X. ran G ) \ { <. .0. , .0. >. } )
           |-> ( ( H ` ( M ` ( ( `' F " { ( 1st ` p ) } ) 
           i^i ( `' G " { ( 2nd ` p ) } ) ) ) ) .x. ( 1st ` p ) ) ) ) ) @=
          ? @.

        @( For simple functions, the integral of a sum is the sum of the
           integral. @)
        sitgadd @p |- ( ph -> ( ( W  sitg M ) ` ( F oF .+ G ) ) 
           = ( ( ( W  sitg M ) ` F ) .+ ( ( W  sitg M ) ` G ) ) ) @=
          ? @.
      @}

      sitgle.1 @e |- .<_ = ( le ` W ) @.
      sitgle.2 @e |- ( ph -> W e. oMnd ) @.
      sitgle.4 @e |- ( ph -> F oR .<_ G ) @.
      @( The simple function integral is monotonic.
         @)
      sitgle @p |- ( ph -> ( ( W sitg M ) ` F ) .<_ ( ( W sitg M ) ` G ) ) @=
        ? @.
    @}
$)
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
      cvv crn cc0 cress cmpt2 elex syl oveq1 dmeqd fveq2 ofeq oveqd mpt2eq123dv
      cds fveq2d oveq2 eqcomi ax-mp a1i fveq12d df-sitm ovex dmex mpt2ex ovmpt2
      syl2anc ) AGUGMZEUAUHUBZMGEUCNCDGEONZPZVPCQZDQZBRZNZUDUIUEUFNUJNZEONZSZUK
      ZTAGFMVMIGFULUMJKLGEUGVNCDKQZLQZONZPZWHVQVRWEUTSZRZNZWAWFONZSZUKWDUCCDGWF
      ONZPZWOVQVRGUTSZRZNZWLSZUKWEGTZCDWHWHWMWOWOWSWTWGWNWEGWFOUNUOZXAWTWKWRWLW
      TWJWQVQVRWTWIWPTWJWQTWEGUTUPWIWPUQUMURVAUSWFETZCDWOWOWSVPVPWCXBWNVOWFEGOV
      BUOZXCXBWRVTWLWBWFEWAOVBXBWQVSVQVRWQVSTZXBWPBTXDBWPHVCWPBUQVDVEURVFUSKCDL
      VGCDVPVPWCVOGEOVHVIZXEVJVKVL $.

    $d f g m w D $.  $d f g F $.  $d f g G $.  $d f g m w M $.  $d f g m w W $.
    $d f g ph $.
    sitmfval.1 $e |- ( ph -> F e. dom ( W sitg M ) ) $.
    sitmfval.2 $e |- ( ph -> G e. dom ( W sitg M ) ) $.
    $( Value of the integral distance between two simple functions.
       (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
    sitmfval $p |- ( ph -> ( F ( W sitm M ) G ) =
      ( ( ( RR*s |`s ( 0 [,] +oo ) ) sitg M ) ` ( F oF D G ) ) ) $=
      ( vf vg csitg co cv cfv cvv wceq cdm cof cxrs cc0 cpnf cicc cress sitmval
      csitm wa simprl simprr oveq12d fveq2d wcel fvex a1i ovmpt2d ) AMNCDGEOPUA
      ZUSMQZNQZBUBZPZUCUDUEUFPUGPEOPZRCDVBPZVDRZGEUIPSABMNEFGHIJUHAUTCTZVADTZUJ
      UJZVCVEVDVIUTCVADVBAVGVHUKAVGVHULUMUNKLVFSUOAVEVDUPUQUR $.
  $}

$(
  @{
    @d m x F @.  @d m x G @.  @d m x M @.  @d m x W @.  @d m x ph @.
    sitmcl.0 @e |- ( ph -> W e. Mnd ) @.
    sitmcl.1 @e |- ( ph -> W e. *MetSp ) @.
    sitmcl.2 @e |- ( ph -> M e. U. ran measures ) @.
    sitmcl.3 @e |- ( ph -> F e. dom ( W sitg M ) ) @.
    sitmcl.4 @e |- ( ph -> G e. dom ( W sitg M ) ) @.
    @( Closure of the integral distance between two simple functions, for an
       extended metric space.  (Contributed by Thierry Arnoux, 13-Feb-2018.) @)
    sitmcl @p |- ( ph -> ( F ( W sitm M ) G ) e. ( 0 [,] +oo ) ) @=
      ( co cfv cc0 eqid cr cvv wcel wceq a1i syl vx vm csitm cds cxrs cpnf cicc
      cof cress csitg cxme sitmfval cxp cres cle cordt crest csigagen cxmu crrh
      ccnfld xrge0base ctopn eqcomi xrge00 cvsca ovex ax-xrsvsca ressvsca ax-mp
      xrge0topn csca ax-xrssca resssca fveq2i cbs cdm cuni wf c0g sibff wb ctps
      xmstps tpsuni 3syl feq3 mpbird cmeas crn dmexg uniexg ofresid cpsmet cxmt
      xmsxmet xmetpsmet psmetxrge0 cha ct1 cmopn xmstopn methaus eqeltrd haust1
      xrge0tps cmnd mndidcl xmet0 syl2anc syl6eq sibfof rebase xpeq12i xrge0cmn
      reseq2i ccmn cdr ccrg cfield wa refld isfld mpbi simpli cnrg csubrg cnnrg
      resubdrg subrgnrg mp2an cchr cofld reofld ofldchr ccusp recusp cuss cima
      cv cmetu reust cico w3a cid rrhre imaeq1i wss cxr 0re pnfxr icossre eqtri
      resiima icossicc eqsstri sseli 3ad2ant2 simp3 ge0xmulcl sitgclg ) ABCEDUC
      KKBCEUDLZUHKZUEMUFUGKZUIKZDUJKZLUVDAUVBBCDUKEUVBNGHIJULAUAUVDVAOUIKZUDLZO
      OUMZUNZUOUPLUVDUQKZURLZUSUBUVCUVGUVGUTLZUVKDPUVEMVBUVEVCLUVKVKVDUVLNVEUVD
      PQZUSUVEVFLRMUFUGVGZUVDUSUEUVEPUVENZVHVIVJUVGUVEVLLZUTUVNUVGUVQRUVOUVDUVG
      UEUVEPUVPVMVNVJZVOUVEPQAUEUVDUIVGSHAUVCBCUVBEVPLZUVSUMZUNZUHKUVFVQADVQZVR
      ZUVSUVBBCPAUWCUVSBVSZUWCEVCLZVRZBVSZAUVSUWEURLZEVFLZBEVLLUTLZUWEDUKEEVTLZ
      UVSNZUWENZUWHNZUWKNZUWINZUWJNZGHIWAAUVSUWFRZUWDUWGWBAEUKQZEWCQZUWRGEWDZUV
      SUWEEUWLUWMWEWFZUVSUWFUWCBWGTWHAUWCUVSCVSZUWCUWFCVSZAUVSUWHUWICUWJUWEDUKE
      UWKUWLUWMUWNUWOUWPUWQGHJWAAUWRUXCUXDWBUXBUVSUWFUWCCWGTWHADWIWJVRZQUWBPQUW
      CPQHDUXEWKUWBPWLWFWMAUVSUVDUWAUWHUWIBCUWJUWEUVEDUKEUWKUWLUWMUWNUWOUWPUWQG
      HIVBAUWSUWTGUXATAUWAUVSWNLQZUVTUVDUWAVSAUWSUWAUVSWOLQZUXFGUWAEUVSUWLUWANZ
      WPZUWAUVSWQWFUWAUVSWRTJUVEWCQAXFSZAUWEWSQUWEWTQAUWEUWAXALZWSAUWSUWEUXKRGU
      WAUWEEUVSUWMUWLUXHXBTAUWSUXGUXKWSQGUXIUWAUXKUVSUXKNXCWFXDUWEXETAUWKUWKUWA
      KZMUVEVTLAUXGUWKUVSQZUXLMRAUWSUXGGUXITAEXGQUXMFUVSEUWKUWLUWOXHTUWKUWAUVSX
      IXJVEXKXLXDUVRUVIUVGVPLZUXNUMUVHOUXNOUXNUVGUVGNZXMZUXPXNXPUXJUVEXQQAXOSUV
      GXRQZAUXQUVGXSQZUVGXTQUXQUXRYAUVGUXOYBUVGYCYDYESUVGYFQZAVAYFQOVAYGLQZUXSY
      HUXTUXQYIYEOVAUVGUXOYJYKSUVGYLLMRZAUVGYMQUYAUVGUXOYNUVGYOVJSUVGYPQAUVGUXO
      YQSUVGYRLUVJUUALRAUVGUXOUUBSAUBYTZUVMMUFUUCKZYSZQZUAYTZUVDQZUUDUYBUVDQZUY
      GUYBUYFUSKUVDQUYEAUYHUYGUYDUVDUYBUYDUYCUVDUYDUUEOUNZUYCYSZUYCUVMUYIUYCUUF
      UUGUYCOUUHZUYJUYCRMOQUFUUIQUYKUUJUUKMUFUULYKOUYCUUNVJUUMMUFUUOUUPUUQUURAU
      YEUYGUUSUYBUYFUUTXJUVAXD @.
  @}

  @{
    @d f g M @.  @d f g W @.  @d f g ph @.
    sitmf.0 @e |- ( ph -> W e. Mnd ) @.
    sitmf.1 @e |- ( ph -> W e. *MetSp ) @.
    sitmf.2 @e |- ( ph -> M e. U. ran measures ) @.
    @( The integral metric as a function.  (Contributed by Thierry Arnoux,
       13-Mar-2018.) @)
    sitmf @p |- ( ph -> ( W sitm M ) :
      ( dom ( W sitg M ) X. dom ( W sitg M ) ) --> ( 0 [,] +oo ) ) @=
      ( vf vg csitg co cdm wf cv cfv wcel wral wa cxme eqid adantr cxp cc0 cpnf
      cicc csitm cds cof cxrs cress cmpt2 cmeas crn cuni simprl simprr sitmfval
      cmnd sitmcl eqeltrrd ralrimivva fmpt2 sylib sitmval feq1d mpbird ) ACBIJK
      ZVFUAZUBUCUDJZCBUEJZLVGVHGHVFVFGMZHMZCUFNZUGJUHVHUIJBIJNZUJZLZAVMVHOZHVFP
      GVFPVOAVPGHVFVFAVJVFOZVKVFOZQZQZVJVKVIJVMVHVTVLVJVKBRCVLSZACROVSETZABUKUL
      UMOVSFTZAVQVRUNZAVQVRUOZUPVTVJVKBCACUQOVSDTWBWCWDWEURUSUTGHVFVFVMVHVNVNSV
      AVBAVGVHVIVNAVLGHBRCWAEFVCVDVE @.

    @d f g h x y M @.  @d f g h x y W @.  @d f g h x y ph @.
    @( The integral metric is a pseudo metric on the simple functions.
       (Contributed by Thierry Arnoux, 14-Mar-2018.) @)
    sitmpsmet @p |- ( ph -> ( W sitm M ) e. ( PsMet ` dom ( W sitg M ) ) ) @=
      ( vx vy co cxr wf cc0 wceq cxad wa cfv wcel eqid cvv syl vf vg vh cdm cxp
      csitg csitm cv cle wbr wral cpsmet cpnf wss sitmf iccssxr fss sylancl cds
      cicc cof cxrs cress cxme cmeas crn cuni simpr sitmfval csn cmpt ctopn wfn
      adantr cbs csigagen cvsca csca crrh c0g sibff ffn dmexg uniexg 3syl inidm
      eqidd offval cres ffvelrnda xmstps tpsuni ad2antrr eleqtrrd ovres syl2anc
      ctps cxmt xmsxmet xmet0 eqtrd xrge0base xrge00 xrge0tps a1i cmnd xrge0cmn
      ccmn ax-mp cslmd ct1 cha haust1 mp1i biimpar simprl ofresid cmpt2 fovrnda
      feq3 fnov simprr sylibr ralrimivva rnmpt2ss df-f eqeltrd sibfof cxmu ovex
      jca off mp2an eqtri 0xr wb adantlr ralrimiva offn ofval mpteq2dva syl6eqr
      eqtr3d fconstmpt fveq2d cordt crest xrge0topn eqcomi xrge0slmod xrge0haus
      cmnmnd sitg0 syl5eqel xmetf sylib xmetge0 syl3anc elxrge0 eqsstrd xmstopn
      rneq methaus mndidcl syl6eq adantl eqeltrrd ax-xrsvsca ressvsca ge0xaddcl
      cmopn rgen2a xaddf mpbi reseq1i resmpt2 fnmpt2 0le0 pnfge elicc1 mpbir3an
      w3a pnfxr xaddid1 xrge0le comnd xrge0omnd xmstri2 syl13anc ofrfval mpbird
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
  @}
$)

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
    @( TODO with the previous definiton, fundamental sequences shall be the
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

