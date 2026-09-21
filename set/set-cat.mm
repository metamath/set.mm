$(
###############################################################################
  BASIC CATEGORY THEORY
###############################################################################
$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Categories
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Categories
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Cat $. $( The class of all categories. $)
  $c Id $. $( The identity arrow in a category. $)
  $c Homf $. $( The functionalized hom-set operation. $)
  $c comf $. $( The functionalized composition operation. $)

  $( Extend class notation with the class of categories. $)
  ccat $a class Cat $.

  $( Extend class notation with the identity arrow of a category. $)
  ccid $a class Id $.

  $( Extend class notation to include functionalized Hom-set extractor. $)
  chomf $a class Homf $.

  $( Extend class notation to include functionalized composition operation. $)
  ccomf $a class comf $.

  ${
    $d b c f g h k o w x y z .x. $.  $d b c f g h k o w x y z B $.
    $d b c f g h k o w x y z C $.  $d b c f g h k o w x y z H $.
    $( A category is an abstraction of a structure (a group, a topology, an
       order...)  Category theory consists in finding new formulation of the
       concepts associated with those structures (product, substructure...)
       using morphisms instead of the belonging relation.  That trick has the
       interesting property that heterogeneous structures like topologies or
       groups for instance become comparable.  Definition in [Lang] p. 53,
       without the axiom CAT 1, i.e., pairwise disjointness of hom-sets
       ( ~ cat1 ).  See ~ setc2obas and ~ setc2ohom for a counterexample.  In
       contrast to definition 3.1 of [Adamek] p. 21, where "A category is a
       quadruple A = (O, hom, id, o)", a category is defined as an extensible
       structure consisting of three slots: the objects "O"
       ( ` ( Base `` c ) ` ), the morphisms "hom" ( ` ( Hom `` c ) ` ) and the
       composition law "o" ( ` ( comp `` c ) ` ).  The identities "id" are
       defined by their properties related to morphisms and their composition,
       see condition 3.1(b) in [Adamek] p. 21 and ~ df-cid .  (Note: in
       category theory morphisms are also called arrows.)  (Contributed by FL,
       24-Oct-2007.)  (Revised by Mario Carneiro, 2-Jan-2017.) $)
    df-cat $a |- Cat = { c | [. ( Base ` c ) / b ]. [. ( Hom ` c ) / h ].
      [. ( comp ` c ) / o ]. A. x e. b
      ( E. g e. ( x h x ) A. y e. b
        ( A. f e. ( y h x ) ( g ( <. y , x >. o x ) f ) = f /\
          A. f e. ( x h y ) ( f ( <. x , x >. o y ) g ) = f ) /\
        A. y e. b A. z e. b A. f e. ( x h y ) A. g e. ( y h z )
      ( ( g ( <. x , y >. o z ) f ) e. ( x h z ) /\ A. w e. b A. k e. ( z h w )
         ( ( k ( <. y , z >. o w ) g ) ( <. x , y >. o w ) f ) =
         ( k ( <. x , z >. o w ) ( g ( <. x , y >. o z ) f ) ) ) ) } $.

    $( Define the category identity arrow.  Since it is uniquely defined when
       it exists, we do not need to add it to the data of the category, and
       instead extract it by uniqueness.  (Contributed by Mario Carneiro,
       3-Jan-2017.) $)
    df-cid $a |- Id = ( c e. Cat |->
      [_ ( Base ` c ) / b ]_ [_ ( Hom ` c ) / h ]_ [_ ( comp ` c ) / o ]_
      ( x e. b |-> ( iota_ g e. ( x h x ) A. y e. b
        ( A. f e. ( y h x ) ( g ( <. y , x >. o x ) f ) = f /\
          A. f e. ( x h y ) ( f ( <. x , x >. o y ) g ) = f ) ) ) ) $.

    $( Define the functionalized Hom-set operator, which is exactly like
       ` Hom ` but is guaranteed to be a function on the base.  (Contributed by
       Mario Carneiro, 4-Jan-2017.) $)
    df-homf $a |- Homf = ( c e. _V |->
      ( x e. ( Base ` c ) , y e. ( Base ` c ) |-> ( x ( Hom ` c ) y ) ) ) $.

    $( Define the functionalized composition operator, which is exactly like
       ` comp ` but is guaranteed to be a function of the proper type.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    df-comf $a |- comf = ( c e. _V |->
      ( x e. ( ( Base ` c ) X. ( Base ` c ) ) , y e. ( Base ` c ) |->
      ( g e. ( ( 2nd ` x ) ( Hom ` c ) y ) , f e. ( ( Hom ` c ) ` x ) |->
        ( g ( x ( comp ` c ) y ) f ) ) ) ) $.

    iscat.b $e |- B = ( Base ` C ) $.
    iscat.h $e |- H = ( Hom ` C ) $.
    iscat.o $e |- .x. = ( comp ` C ) $.
    $( The predicate "is a category".  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    iscat $p |- ( C e. V -> ( C e. Cat <-> A. x e. B
      ( E. g e. ( x H x ) A. y e. B
          ( A. f e. ( y H x ) ( g ( <. y , x >. .x. x ) f ) = f /\
            A. f e. ( x H y ) ( f ( <. x , x >. .x. y ) g ) = f ) /\
        A. y e. B A. z e. B A. f e. ( x H y ) A. g e. ( y H z )
        ( ( g ( <. x , y >. .x. z ) f ) e. ( x H z ) /\
          A. w e. B A. k e. ( z H w )
         ( ( k ( <. y , z >. .x. w ) g ) ( <. x , y >. .x. w ) f ) =
         ( k ( <. x , z >. .x. w ) ( g ( <. x , y >. .x. z ) f ) ) ) ) ) ) $=
      ( cv co wceq wral oveqd vo vh vb cop wrex wcel cco cfv wsbc chom cbs ccat
      vc wa fvexd fveq2 eqtr4di simpl fveq2d simpll simpllr simplr simpr eqeq1d
      raleqbidv anbi12d rexeqbidv eleq12d eqidd oveq123d eqeq12d sbcied2 df-cat
      cvv elab2g ) IPZHPZBPZAPZUDZVSUAPZQZQZVQRZHVRVSUBPZQZSZVQVPVSVSUDZVRWAQZQ
      ZVQRZHVSVRWEQZSZUNZBUCPZSZIVSVSWEQZUEZVPVQVSVRUDZCPZWAQZQZVSWTWEQZUFZJPZV
      PVRWTUDZDPZWAQZQZVQWSXGWAQZQZXEXBVSWTUDZXGWAQZQZRZJWTXGWEQZSZDWOSZUNZIVRW
      TWEQZSZHWLSZCWOSZBWOSZUNZAWOSZUAUMPZUGUHZUIZUBYGUJUHZUIZUCYGUKUHZUIVPVQVT
      VSGQZQZVQRZHVRVSKQZSZVQVPWHVRGQZQZVQRZHVSVRKQZSZUNZBESZIVSVSKQZUEZVPVQWSW
      TGQZQZVSWTKQZUFZXEVPXFXGGQZQZVQWSXGGQZQZXEUUHXLXGGQZQZRZJWTXGKQZSZDESZUNZ
      IVRWTKQZSZHUUASZCESZBESZUNZAESZUMFULLYGFRZYKUVHUCYLEVNUVIYGUKUOUVIYLFUKUH
      EYGFUKUPMUQUVIWOERZUNZYIUVHUBYJKVNUVKYGUJUOUVKYJFUJUHKUVKYGFUJUVIUVJURUSN
      UQUVKWEKRZUNZYFUVHUAYHGVNUVMYGUGUOUVMYHFUGUHGUVMYGFUGUVIUVJUVLUTUSOUQUVMW
      AGRZUNZYEUVGAWOEUVIUVJUVLUVNVAZUVOWRUUFYDUVFUVOWPUUDIWQUUEUVOWEKVSVSUVKUV
      LUVNVBZTUVOWNUUCBWOEUVPUVOWGYQWMUUBUVOWDYOHWFYPUVOWEKVRVSUVQTUVOWCYNVQUVO
      WBYMVPVQUVOWAGVTVSUVMUVNVCZTTVDVEUVOWKYTHWLUUAUVOWEKVSVRUVQTZUVOWJYSVQUVO
      WIYRVQVPUVOWAGWHVRUVRTTVDVEVFVEVGUVOYCUVEBWOEUVPUVOYBUVDCWOEUVPUVOYAUVCHW
      LUUAUVSUVOXSUVAIXTUVBUVOWEKVRWTUVQTUVOXDUUJXRUUTUVOXBUUHXCUUIUVOXAUUGVPVQ
      UVOWAGWSWTUVRTTZUVOWEKVSWTUVQTVHUVOXQUUSDWOEUVPUVOXOUUQJXPUURUVOWEKWTXGUV
      QTUVOXKUUNXNUUPUVOXIUULVQVQXJUUMUVOWAGWSXGUVRTUVOXHUUKXEVPUVOWAGXFXGUVRTT
      UVOVQVIVJUVOXEXEXBUUHXMUUOUVOWAGXLXGUVRTUVOXEVIUVTVJVKVEVEVFVEVEVEVEVFVEV
      LVLVLABCDHIUBJUAUCUMVMVO $.
  $}

  ${
    $d f g y .1. $.  $d f g k w x y z B $.  $d f g k w x y z ph $.  $d g .x. $.
    $d f g k w x y z C $.  $d f g k w H $.
    iscatd.b $e |- ( ph -> B = ( Base ` C ) ) $.
    iscatd.h $e |- ( ph -> H = ( Hom ` C ) ) $.
    iscatd.o $e |- ( ph -> .x. = ( comp ` C ) ) $.
    iscatd.c $e |- ( ph -> C e. V ) $.
    iscatd.1 $e |- ( ( ph /\ x e. B ) -> .1. e. ( x H x ) ) $.
    iscatd.2 $e |- ( ( ph /\ ( x e. B /\ y e. B /\ f e. ( y H x ) ) ) ->
      ( .1. ( <. y , x >. .x. x ) f ) = f ) $.
    iscatd.3 $e |- ( ( ph /\ ( x e. B /\ y e. B /\ f e. ( x H y ) ) ) ->
      ( f ( <. x , x >. .x. y ) .1. ) = f ) $.
    iscatd.4 $e |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) /\
      ( f e. ( x H y ) /\ g e. ( y H z ) ) ) ->
        ( g ( <. x , y >. .x. z ) f ) e. ( x H z ) ) $.
    iscatd.5 $e |- ( ( ph /\ ( ( x e. B /\ y e. B ) /\ ( z e. B /\ w e. B ) )
      /\ ( f e. ( x H y ) /\ g e. ( y H z ) /\ k e. ( z H w ) ) ) ->
       ( ( k ( <. y , z >. .x. w ) g ) ( <. x , y >. .x. w ) f ) =
         ( k ( <. x , z >. .x. w ) ( g ( <. x , y >. .x. z ) f ) ) ) $.
    $( Properties that determine a category.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    iscatd $p |- ( ph -> C e. Cat ) $=
      ( ccat wcel cv cop cco cfv co wceq chom wral wa wrex 3exp2 imp31 ralrimiv
      cbs wi ralrimiva oveq1 eqeq1d ralbidv oveq2 anbi12d rspcev syl2anc 3expia
      jca imp43 3expa imp32 expr expd imp42 ralrimdva jcad ralrimivv ralrimivva
      ex oveqd raleqbidv rexeqbidv eleq12d eqidd oveq123d eqeq12d mpbid wb eqid
      w3a iscat syl mpbird ) AGUDUEZKUFZJUFZCUFZBUFZUGZWTGUHUIZUJZUJZWRUKZJWSWT
      GULUIZUJZUMZWRWQWTWTUGZWSXBUJZUJZWRUKZJWTWSXFUJZUMZUNZCGUSUIZUMZKWTWTXFUJ
      ZUOZWQWRWTWSUGZDUFZXBUJZUJZWTYAXFUJZUEZLUFZWQWSYAUGZEUFZXBUJZUJZWRXTYHXBU
      JZUJZYFYCWTYAUGZYHXBUJZUJZUKZLYAYHXFUJZUMZEXPUMZUNZKWSYAXFUJZUMZJXMUMZDXP
      UMZCXPUMZUNZBXPUMZAWQWRXAWTHUJZUJZWRUKZJWSWTMUJZUMZWRWQXIWSHUJZUJZWRUKZJW
      TWSMUJZUMZUNZCFUMZKWTWTMUJZUOZWQWRXTYAHUJZUJZWTYAMUJZUEZYFWQYGYHHUJZUJZWR
      XTYHHUJZUJZYFUVCYMYHHUJZUJZUKZLYAYHMUJZUMZEFUMZUNZKWSYAMUJZUMZJUUPUMZDFUM
      ZCFUMZUNZBFUMUUGAUWBBFAWTFUEZUNZUVAUWAUWDIUUTUEIWRUUHUJZWRUKZJUUKUMZWRIUU
      MUJZWRUKZJUUPUMZUNZCFUMZUVASUWDUWKCFUWDWSFUEZUNZUWGUWJUWNUWFJUUKAUWCUWMWR
      UUKUEZUWFUTAUWCUWMUWOUWFTUPUQURUWNUWIJUUPAUWCUWMWRUUPUEZUWIUTAUWCUWMUWPUW
      IUAUPUQURVJVAUUSUWLKIUUTWQIUKZUURUWKCFUWQUULUWGUUQUWJUWQUUJUWFJUUKUWQUUIU
      WEWRWQIWRUUHVBVCVDUWQUUOUWIJUUPUWQUUNUWHWRWQIWRUUMVEVCVDVFVDVGVHUWDUVSCDF
      FUWDUWMYAFUEZUNUNZUVPJKUUPUVQUWSUWPWQUVQUEZUNZUVEUVOAUWCUWMUWRUXAUVEUTZAU
      WCUWMUWRUXBAUWCUWMUWRWLUXAUVEUBVIUPVKUWSUXAUVNEFUWDUWMUWRYHFUEZUXAUVNUTZA
      UWCUWMUWRUXCUXDUTUTAUWCUWMUNZUNUWRUXCUXDAUXEUWRUXCUNZUXDAUXEUXFUNZUNZUXAU
      VNUXHUXAUNUVLLUVMUXHUWPUWTYFUVMUEZUVLUTUXHUWPUWTUXIUVLAUXGUWPUWTUXIWLUVLU
      CVLUPVMURWAVNVOVNVPVQVRVSVTVJVAAUWBUUFBFXPOAUVAXSUWAUUEAUUSXQKUUTXRAMXFWT
      WTPWBAUURXOCFXPOAUULXHUUQXNAUUJXEJUUKXGAMXFWSWTPWBAUUIXDWRAUUHXCWQWRAHXBX
      AWTQWBWBVCWCAUUOXLJUUPXMAMXFWTWSPWBZAUUNXKWRAUUMXJWRWQAHXBXIWSQWBWBVCWCVF
      WCWDAUVTUUDCFXPOAUVSUUCDFXPOAUVRUUBJUUPXMUXJAUVPYTKUVQUUAAMXFWSYAPWBAUVEY
      EUVOYSAUVCYCUVDYDAUVBYBWQWRAHXBXTYAQWBWBZAMXFWTYAPWBWEAUVNYREFXPOAUVLYPLU
      VMYQAMXFYAYHPWBAUVIYLUVKYOAUVGYJWRWRUVHYKAHXBXTYHQWBAUVFYIYFWQAHXBYGYHQWB
      WBAWRWFWGAYFYFUVCYCUVJYNAHXBYMYHQWBAYFWFUXKWGWHWCWCVFWCWCWCWCVFWCWIAGNUEW
      PUUGWJRBCDEXPGXBJKLXFNXPWKXFWKXBWKWMWNWO $.
  $}

  ${
    $d f g k w x y z B $.  $d f g k w x y z C $.  $d g ph $.  $d f g h x y X $.
    $d f g h k w x y z H $.  $d f g h k w x y z .x. $.
    catidex.b $e |- B = ( Base ` C ) $.
    catidex.h $e |- H = ( Hom ` C ) $.
    catidex.o $e |- .x. = ( comp ` C ) $.
    catidex.c $e |- ( ph -> C e. Cat ) $.
    catidex.x $e |- ( ph -> X e. B ) $.
    $( Each object in a category has an associated identity arrow.
       (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    catidex $p |- ( ph -> E. g e. ( X H X ) A. y e. B
          ( A. f e. ( y H X ) ( g ( <. y , X >. .x. X ) f ) = f /\
            A. f e. ( X H y ) ( f ( <. X , X >. .x. y ) g ) = f ) ) $=
      ( vx cv cop co wceq wral vz vk vw wa wrex id oveq2 opeq2 eqeq1d raleqbidv
      oveq12d oveqd oveq1 opeq12d anbi12d ralbidv rexeqbidv ccat wcel iscat ibi
      oveq1d simpl ralimi 3syl rspcdva ) AGPZFPZBPZOPZQZVJERZRZVHSZFVIVJHRZTZVH
      VGVJVJQZVIERZRZVHSZFVJVIHRZTZUDZBCTZGVJVJHRZUEZVGVHVIIQZIERZRZVHSZFVIIHRZ
      TZVHVGIIQZVIERZRZVHSZFIVIHRZTZUDZBCTZGIIHRZUEOCIVJISZWDWTGWEXAXBVJIVJIHXB
      UFZXCUKXBWCWSBCXBVPWLWBWRXBVNWJFVOWKVJIVIHUGXBVMWIVHXBVLWHVGVHXBVKWGVJIEV
      JIVIUHXCUKULUIUJXBVTWPFWAWQVJIVIHUMXBVSWOVHXBVRWNVHVGXBVQWMVIEXBVJIVJIXCX
      CUNVBULUIUJUOUPUQADURUSZWFVGVHVJVIQZUAPZERRZVJXFHRUSUBPZVGVIXFQUCPZERRVHX
      EXIERRXHXGVJXFQXIERRSUBXFXIHRTUCCTUDGVIXFHRTFWATUACTBCTZUDZOCTZWFOCTMXDXL
      OBUAUCCDEFGUBHURJKLUTVAXKWFOCWFXJVCVDVENVF $.

    $( Each object in a category has a unique identity arrow.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    catideu $p |- ( ph -> E! g e. ( X H X ) A. y e. B
          ( A. f e. ( y H X ) ( g ( <. y , X >. .x. X ) f ) = f /\
            A. f e. ( X H y ) ( f ( <. X , X >. .x. y ) g ) = f ) ) $=
      ( vh cv co wceq wral wa wrex wrmo wreu catidex wi wcel oveq1 opeq1 oveq1d
      cop oveqd eqeq1d raleqbidv oveq2 anbi12d syl ralrimivw weq an3 id eqeq12d
      rspcv im2anan9r eqtr2 equcomd syl56 rgen2 a1i rmo4 sylibr rmoim sylc reu5
      ralbidv sylanbrc ) AGPZFPZBPZIUJZIEQZQZVQRZFVRIHQZSZVQVPIIUJZVREQZQZVQRZF
      IVRHQZSZTZBCSZGIIHQZUAWLGWMUBZWLGWMUCABCDEFGHIJKLMNUDAWLVPVQWEIEQZQZVQRZF
      WMSZVQVPWOQZVQRZFWMSZTZUEZGWMSXBGWMUBZWNAXCGWMAICUFXCNWKXBBICVRIRZWDWRWJX
      AXEWBWQFWCWMVRIIHUGXEWAWPVQXEVTWOVPVQXEVSWEIEVRIIUHUIUKULUMXEWHWTFWIWMVRI
      IHUNXEWGWSVQXEWFWOVQVPVRIWEEUNUKULUMUOVBUPUQAXBOPZVQWOQZVQRZFWMSZVQXFWOQZ
      VQRZFWMSZTZTZGOURZUEZOWMSGWMSZXDXQAXPGOWMWMXNWRXLTVPWMUFZXFWMUFZTVPXFWOQZ
      XFRZXTVPRZTZXOWRXAXIXLUSXSWRYAXRXLYBWQYAFXFWMFOURZWPXTVQXFVQXFVPWOUNYDUTV
      AVBXKYBFVPWMFGURZXJXTVQVPVQVPXFWOUGYEUTVAVBVCYCOGXTXFVPVDVEVFVGVHXBXMGOWM
      XOWRXIXAXLXOWQXHFWMXOWPXGVQVPXFVQWOUGULVNXOWTXKFWMXOWSXJVQVPXFVQWOUNULVNU
      OVIVJWLXBGWMVKVLWLGWMVMVO $.
  $}

  ${
    $d b c f g h o x y B $.  $d b c f g h o x y C $.  $d b c f g h o x y .x. $.
    $d b c f g h o x y H $.  $d f g x y ph $.  $d f g x y X $.
    cidfval.b $e |- B = ( Base ` C ) $.
    cidfval.h $e |- H = ( Hom ` C ) $.
    cidfval.o $e |- .x. = ( comp ` C ) $.
    cidfval.c $e |- ( ph -> C e. Cat ) $.
    cidfval.i $e |- .1. = ( Id ` C ) $.
    $( Each object in a category has an associated identity arrow.
       (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    cidfval $p |- ( ph -> .1. = ( x e. B |-> ( iota_ g e. ( x H x ) A. y e. B
      ( A. f e. ( y H x ) ( g ( <. y , x >. .x. x ) f ) = f /\
        A. f e. ( x H y ) ( f ( <. x , x >. .x. y ) g ) = f ) ) ) ) $=
      ( cfv cv co wceq oveqd vc vb vh vo ccid cop wral crio cmpt ccat wcel chom
      wa cbs cco csb cvv fvexd fveq2 eqtr4di simpl fveq2d simpll simpllr simplr
      simpr eqeq1d raleqbidv anbi12d riotaeqbidv mpteq12dv csbied2 mptfvmpt syl
      df-cid eqtrid ) AGEUEPZBDIQZHQZCQZBQZUFZWAFRZRZVSSZHVTWAJRZUGZVSVRWAWAUFZ
      VTFRZRZVSSZHWAVTJRZUGZUMZCDUGZIWAWAJRZUHZUIZOAEUJUKVQWRSNBUAWQUNUEUBUAQZU
      NPZUCWSULPZUDWSUOPZBUBQZVRVSWBWAUDQZRZRZVSSZHVTWAUCQZRZUGZVSVRWHVTXDRZRZV
      SSZHWAVTXHRZUGZUMZCXCUGZIWAWAXHRZUHZUIZUPZUPZUPDUJEEWSESZUBWTDYBWRUQYCWSU
      NURYCWTEUNPDWSEUNUSKUTYCXCDSZUMZUCXAJYAWRUQYEWSULURYEXAEULPJYEWSEULYCYDVA
      VBLUTYEXHJSZUMZUDXBFXTWRUQYGWSUOURYGXBEUOPFYGWSEUOYCYDYFVCVBMUTYGXDFSZUMZ
      BXCXSDWQYCYDYFYHVDZYIXQWOIXRWPYIXHJWAWAYEYFYHVEZTYIXPWNCXCDYJYIXJWGXOWMYI
      XGWEHXIWFYIXHJVTWAYKTYIXFWDVSYIXEWCVRVSYIXDFWBWAYGYHVFZTTVGVHYIXMWKHXNWLY
      IXHJWAVTYKTYIXLWJVSYIXKWIVSVRYIXDFWHVTYLTTVGVHVIVHVJVKVLVLVLBCHIUCUDUBUAV
      OKVMVNVP $.

    cidval.x $e |- ( ph -> X e. B ) $.
    $( Each object in a category has an associated identity arrow.
       (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    cidval $p |- ( ph -> ( .1. ` X ) = ( iota_ g e. ( X H X ) A. y e. B
      ( A. f e. ( y H X ) ( g ( <. y , X >. .x. X ) f ) = f /\
        A. f e. ( X H y ) ( f ( <. X , X >. .x. y ) g ) = f ) ) ) $=
      ( cv co wceq wral vx cop wa cvv cidfval simpr oveq12d oveq2d opeq2d oveqd
      crio eqeq1d raleqbidv oveq1d opeq12d anbi12d ralbidv riotaeqbidv wcel a1i
      riotaex fvmptd ) AUAJHQZGQZBQZUAQZUBZVFERZRZVDSZGVEVFIRZTZVDVCVFVFUBZVEER
      ZRZVDSZGVFVEIRZTZUCZBCTZHVFVFIRZUKVCVDVEJUBZJERZRZVDSZGVEJIRZTZVDVCJJUBZV
      EERZRZVDSZGJVEIRZTZUCZBCTZHJJIRZUKZCFUDAUABCDEFGHIKLMNOUEAVFJSZUCZVTWOHWA
      WPWSVFJVFJIAWRUFZWTUGWSVSWNBCWSVLWGVRWMWSVJWEGVKWFWSVFJVEIWTUHWSVIWDVDWSV
      HWCVCVDWSVGWBVFJEWSVFJVEWTUIWTUGUJULUMWSVPWKGVQWLWSVFJVEIWTUNWSVOWJVDWSVN
      WIVDVCWSVMWHVEEWSVFJVFJWTWTUOUNUJULUMUPUQURPWQUDUSAWOHWPVAUTVB $.
  $}

  ${
    $d b c f g h o x y B $.  $d b c f g h o x y C $.
    $( The identity arrow construction is a function on categories.
       (Contributed by Mario Carneiro, 17-Jan-2017.) $)
    cidffn $p |- Id Fn Cat $=
      ( vc vb vh vo vx vg vf vy ccat cv cbs cfv chom cco cop co wceq wral csbex
      csb wa crio cmpt ccid vex mptex df-cid fnmpti ) AIBAJZKLZCUIMLZDUINLZEBJZ
      FJZGJZHJZEJZOUQDJZPPUOQGUPUQCJZPRUOUNUQUQOUPURPPUOQGUQUPUSPRUAHUMRFUQUQUS
      PUBZUCZTZTZTUDBUJVCCUKVBDULVAEUMUTBUEUFSSSEHGFCDBAUGUH $.

    cidfn.b $e |- B = ( Base ` C ) $.
    cidfn.i $e |- .1. = ( Id ` C ) $.
    $( The identity arrow operator is a function from objects to arrows.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    cidfn $p |- ( C e. Cat -> .1. Fn B ) $=
      ( vx vg vf vy ccat wcel wfn cv cop cco cfv co wceq wral eqid chom wa crio
      cmpt riotaex fnmpti id cidfval fneq1d mpbiri ) BJKZCALFAGMZHMZIMZFMZNUOBO
      PZQQUMRHUNUOBUAPZQSUMULUOUONUNUPQQUMRHUOUNUQQSUBIASZGUOUOUQQZUCZUDZALFAUT
      VAURGUSUEVATUFUKACVAUKFIABUPCHGUQDUQTUPTUKUGEUHUIUJ $.
  $}

  ${
    $d f g y .1. $.  $d x B $.  $d f g x y C $.  $d f g x y ph $.
    catidd.b $e |- ( ph -> B = ( Base ` C ) ) $.
    catidd.h $e |- ( ph -> H = ( Hom ` C ) ) $.
    catidd.o $e |- ( ph -> .x. = ( comp ` C ) ) $.
    catidd.c $e |- ( ph -> C e. Cat ) $.
    catidd.1 $e |- ( ( ph /\ x e. B ) -> .1. e. ( x H x ) ) $.
    catidd.2 $e |- ( ( ph /\ ( x e. B /\ y e. B /\ f e. ( y H x ) ) ) ->
      ( .1. ( <. y , x >. .x. x ) f ) = f ) $.
    catidd.3 $e |- ( ( ph /\ ( x e. B /\ y e. B /\ f e. ( x H y ) ) ) ->
      ( f ( <. x , x >. .x. y ) .1. ) = f ) $.
    $( Deduce the identity arrow in a category.  (Contributed by Mario
       Carneiro, 3-Jan-2017.) $)
    catidd $p |- ( ph -> ( Id ` C ) = ( x e. B |-> .1. ) ) $=
      ( co wceq wcel oveqd vg cbs cfv cv cop cco chom wral wa crio cmpt ccid ex
      w3a eleq2d 3anbi123d eqeq1d 3imtr3d 3expd imp41 ralrimiva jca wreu wb imp
      eqid ccat adantr simpr catideu oveq1 ralbidv oveq2 anbi12d riota2 syl2anc
      mpbid mpteq2dva cidfval mpteq1d 3eqtr4d ) ABEUBUCZUAUDZHUDZCUDZBUDZUEZWFE
      UFUCZQZQZWDRZHWEWFEUGUCZQZUHZWDWCWFWFUEZWEWHQZQZWDRZHWFWEWLQZUHZUIZCWBUHZ
      UAWFWFWLQZUJZUKBWBGUKEULUCZBDGUKABWBXDGAWFWBSZUIZGWDWIQZWDRZHWMUHZWDGWPQZ
      WDRZHWSUHZUIZCWBUHZXDGRZXGXNCWBXGWEWBSZUIZXJXMXRXIHWMAXFXQWDWMSZXIAXFXQXS
      XIAWFDSZWEDSZWDWEWFIQZSZUNZGWDWGWFFQZQZWDRZXFXQXSUNXIAYDYGOUMAXTXFYAXQYCX
      SADWBWFJUOZADWBWEJUOZAYBWMWDAIWLWEWFKTUOUPAYFXHWDAYEWIGWDAFWHWGWFLTTUQURU
      SUTVAXRXLHWSAXFXQWDWSSZXLAXFXQYJXLAXTYAWDWFWEIQZSZUNZWDGWOWEFQZQZWDRZXFXQ
      YJUNXLAYMYPPUMAXTXFYAXQYLYJYHYIAYKWSWDAIWLWFWEKTUOUPAYOXKWDAYNWPWDGAFWHWO
      WELTTUQURUSUTVAVBVAXGGXCSZXBUAXCVCXOXPVDAXFYQAXTGWFWFIQZSZXFYQAXTYSNUMYHA
      YRXCGAIWLWFWFKTUOURVEXGCWBEWHHUAWLWFWBVFZWLVFZWHVFZAEVGSXFMVHAXFVIVJXBXOU
      AXCGWCGRZXAXNCWBUUCWNXJWTXMUUCWKXIHWMUUCWJXHWDWCGWDWIVKUQVLUUCWRXLHWSUUCW
      QXKWDWCGWDWPVMUQVLVNVLVOVPVQVRABCWBEWHXEHUAWLYTUUAUUBMXEVFVSABDWBGJVTWA
      $.
  $}

  ${
    $d a f g k r w x z .1. $.  $d a f g k r w x y z B $.  $d a g k r w y z C $.
    $d f g k r w x y z H $.  $d a f g k r w x y z ph $.
    $d f g k w x y z .x. $.
    iscatd2.b $e |- ( ph -> B = ( Base ` C ) ) $.
    iscatd2.h $e |- ( ph -> H = ( Hom ` C ) ) $.
    iscatd2.o $e |- ( ph -> .x. = ( comp ` C ) ) $.
    iscatd2.c $e |- ( ph -> C e. V ) $.
    iscatd2.ps $e |- ( ps <-> ( ( x e. B /\ y e. B ) /\ ( z e. B /\ w e. B )
      /\ ( f e. ( x H y ) /\ g e. ( y H z ) /\ k e. ( z H w ) ) ) ) $.
    iscatd2.1 $e |- ( ( ph /\ y e. B ) -> .1. e. ( y H y ) ) $.
    iscatd2.2 $e |- ( ( ph /\ ps ) -> ( .1. ( <. x , y >. .x. y ) f ) = f ) $.
    iscatd2.3 $e |- ( ( ph /\ ps ) -> ( g ( <. y , y >. .x. z ) .1. ) = g ) $.
    iscatd2.4 $e |- ( ( ph /\ ps ) ->
       ( g ( <. x , y >. .x. z ) f ) e. ( x H z ) ) $.
    iscatd2.5 $e |- ( ( ph /\ ps ) ->
       ( ( k ( <. y , z >. .x. w ) g ) ( <. x , y >. .x. w ) f ) =
         ( k ( <. x , z >. .x. w ) ( g ( <. x , y >. .x. z ) f ) ) ) $.
    $( Version of ~ iscatd with a uniform assumption list, for increased proof
       sharing capabilities.  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    iscatd2 $p |- ( ph -> ( C e. Cat /\ ( Id ` C ) = ( y e. B |-> .1. ) ) ) $=
      ( va vr ccat wcel ccid cfv cmpt wceq cv co w3a wex cop wne ne0d 3ad2antr1
      wa c0 n0 sylib exdistrv simpll simplr2 simplr1 simplr3 simprl simprr 3jca
      jca wi wsb simplll eleq1d anbi1d simpllr simplr anidm bitrdi simpr oveq1d
      anbi12d eleq12d oveq2d eleq2d oveq12d bitrid anbi2d opeq1d eqidd oveq123d
      3anbi123d eqeq12d imbi12d sbiedvw sbt chvarvv syl13anc exlimdvv biimtrrid
      mp2and neeq1d wral ralrimiva adantr simpr2 rspcdva 3ad2ant1 simp23 eleq1w
      ex id 3anbi1d oveq1 opeq1 oveqd df-3an bitri bitr4di opeq2d exp45 exlimdv
      3imp mpd 3anbi23d simpl 3anbi12d 3anbi13d 3anass iscatd catidd ) AHUHUIHU
      JUKDGJULUMADUFEFGHIJUGLMNOPQRSUAADUNZGUIZUFUNZGUIZUGUNZYRYPNUOZUIZUPZVBZL
      UNZYPYPNUOZUIZLUQZMUNZUUFUIZMUQZJYTYRYPURZYPIUOZUOZYTUMZUUDUUFVCUSZUUHAYS
      YQUUPUUBAYQVBUUFJUAUTZVAZLUUFVDVEUUDUUPUUKUURMUUFVDVEUUHUUKVBUUGUUJVBZMUQ
      LUQUUDUUOUUGUUJLMVFUUDUUSUUOLMUUDUUSUUOUUDUUSVBZAYSYQVBZYQUUBUUGUUJUPZUUO
      AUUCUUSVGUUTYSYQYQYSUUBAUUSVHYQYSUUBAUUSVIZVNUVCUUTUUBUUGUUJYQYSUUBAUUSVJ
      UUDUUGUUJVKUUDUUGUUJVLVMABVBZJKUNZCUNZYPURZYPIUOZUOZUVEUMZVOZKUGVPZFDVPZE
      DVPAUVAYQUVBUPZVBZUUOVOZCUFUVFYRUMZUVMUVPEDUVQEUNZYPUMZVBZUVLUVPFDUVTFUNZ
      YPUMZVBZUVKUVPKUGUWCUVEYTUMZVBZUVDUVOUVJUUOUWEBUVNABUVFGUIZYQVBZUVRGUIZUW
      AGUIZVBZUVEUVFYPNUOZUIZUUEYPUVRNUOZUIZUUIUVRUWANUOZUIZUPZUPZUWEUVNTUWEUWG
      UVAUWJYQUWQUVBUWEUWFYSYQUWEUVFYRGUVQUVSUWBUWDVQZVRVSUWEUWJYQYQVBZYQUWEUWH
      YQUWIYQUWEUVRYPGUVQUVSUWBUWDVTZVRUWEUWAYPGUVTUWBUWDWAZVRWFYQWBZWCUWEUWLUU
      BUWNUUGUWPUUJUWEUVEYTUWKUUAUWCUWDWDZUWEUVFYRYPNUWSWEWGUWEUWMUUFUUEUWEUVRY
      PYPNUXAWHWIUWEUWOUUFUUIUWEUVRYPUWAYPNUXAUXBWJWIWPWPWKWLUWEUVIUUNUVEYTUWEJ
      JUVEYTUVHUUMUWEUVGUULYPIUWEUVFYRYPUWSWMWEUWEJWNUXDWOUXDWQWRWSWSWSUVMEDUVL
      FDUVKKUGUBWTWTWTXAXBXOXCXDXEZAYQYSYTYPYRNUOZUIZUPZVBZUVEUUFUIZKUQZUUIYRYR
      NUOZUIZMUQZYTJYPYPURZYRIUOZUOZYTUMZUXIUUPUXKAYSYQUUPUXGUUQVAKUUFVDVEUXIUX
      LVCUSZUXNUXIUUPUXSDGYRYPYRUMZUUFUXLVCUXTYPYRYPYRNUXTXPZUYAWJXFAUUPDGXGZUX
      HAUUPDGUUQXHZXIAYQYSUXGXJXKMUXLVDVEUXKUXNVBUXJUXMVBZMUQKUQUXIUXRUXJUXMKMV
      FUXIUYDUXRKMUXIUYDUXRUXIUYDVBZAYQYSUXJUXGUXMUPZUXRAUXHUYDVGYQYSUXGAUYDVIY
      QYSUXGAUYDVHUYEUXJUXGUXMUXIUXJUXMVKYQYSUXGAUYDVJUXIUXJUXMVLVMUVDUUEJUXOUV
      RIUOZUOZUUEUMZVOZLUGVPZFUFVPZEUFVPAYQYSUYFUPZVBZUXRVOZCDUVFYPUMZUYLUYOEUF
      UYPUVRYRUMZVBZUYKUYOFUFUYRUWAYRUMZVBZUYJUYOLUGUYTUUEYTUMZVBZUVDUYNUYIUXRV
      UBBUYMABUWRVUBUYMTVUBUWGYQUWJYSUWQUYFVUBUWGUWTYQVUBUWFYQYQVUBUVFYPGUYPUYQ
      UYSVUAVQZVRVSUXCWCVUBUWJYSYSVBYSVUBUWHYSUWIYSVUBUVRYRGUYPUYQUYSVUAVTZVRVU
      BUWAYRGUYRUYSVUAWAZVRWFYSWBWCVUBUWLUXJUWNUXGUWPUXMVUBUWKUUFUVEVUBUVFYPYPN
      VUCWEWIVUBUUEYTUWMUXFUYTVUAWDZVUBUVRYRYPNVUDWHWGVUBUWOUXLUUIVUBUVRYRUWAYR
      NVUDVUEWJWIWPWPWKWLVUBUYHUXQUUEYTVUBUUEYTJJUYGUXPVUBUVRYRUXOIVUDWHVUFVUBJ
      WNWOVUFWQWRWSWSWSUYLEUFUYKFUFUYJLUGUCWTWTWTXAXBXOXCXDXEZAYQYSUWHUPZUXGUUE
      YRUVRNUOZUIZVBZUPZUUIUVRUVRNUOZUIZMUQZUUEYTYPYRURZUVRIUOZUOZUWMUIZVULVUMV
      CUSZVUOVULUUPVUTDGUVRYPUVRUMZUUFVUMVCVVAYPUVRYPUVRNVVAXPZVVBWJXFAVUHUYBVU
      KUYCXLAYQYSUWHVUKXMXKMVUMVDVEVULVUNVUSMAVUHVUKVUNVUSVOAVUHVUKVUNVUSAUWFYS
      UWHUPZYTUVFYRNUOZUIZVUJVBZVUNVBZVBZVBZUUEYTUVFYRURZUVRIUOZUOZUVFUVRNUOZUI
      ZVOZAVUHVUKVUNVBZVBZVBZVUSVOCDUYPVVIVVRVVNVUSUYPVVHVVQAUYPVVCVUHVVGVVPUYP
      UWFYQYSUWHCDGXNZXQUYPVVFVUKVUNUYPVVEUXGVUJUYPVVDUXFYTUVFYPYRNXRWIZVSVSWFW
      LUYPVVLVURVVMUWMUYPVVKVUQUUEYTUYPVVJVUPUVRIUVFYPYRXSZWEXTZUVFYPUVRNXRWGWR
      UVDUUEUVEUVGUVRIUOZUOZVVMUIZVOZKUGVPZFEVPVVODUFUXTVWGVVOFEUXTUWAUVRUMZVBZ
      VWFVVOKUGVWIUWDVBZUVDVVIVWEVVNVWJBVVHABUWGUWJVBZUWQVBZVWJVVHBUWRVWLTUWGUW
      JUWQYAYBVWJVWKVVCUWQVVGVWJVWKUWFYSVBZUWHVBVVCVWJUWGVWMUWJUWHVWJYQYSUWFVWJ
      YPYRGUXTVWHUWDVGZVRWLVWJUWJUWHUWHVBUWHVWJUWIUWHUWHVWJUWAUVRGUXTVWHUWDWAZV
      RWLUWHWBWCWFUWFYSUWHYAYCVWJUWQVVEVUJVUNUPVVGVWJUWLVVEUWNVUJUWPVUNVWJUVEYT
      UWKVVDVWIUWDWDZVWJYPYRUVFNVWNWHWGVWJUWMVUIUUEVWJYPYRUVRNVWNWEWIVWJUWOVUMU
      UIVWJUWAUVRUVRNVWOWHWIWPVVEVUJVUNYAWCWFWKWLVWJVWDVVLVVMVWJUUEUUEUVEYTVWCV
      VKVWJUVGVVJUVRIVWJYPYRUVFVWNYDWEVWJUUEWNVWPWOVRWRWSWSVWGFEVWFKUGUDWTWTXAX
      AYEYGYFYHAVWMUWJVBZVVEVUJUWPUPZUPZUUIUUEYRUVRURZUWAIUOZUOZYTVVJUWAIUOZUOZ
      UUIVVLUVFUVRURZUWAIUOZUOZUMZVOZAYQYSVBZUWJVBZUXGVUJUWPUPZUPZVXBYTVUPUWAIU
      OZUOZUUIVURYPUVRURZUWAIUOZUOZUMZVOCDUYPVWSVXMVXHVXSUYPVWQVXKVWRVXLAUYPVWM
      VXJUWJUYPUWFYQYSVVSVSVSUYPVVEUXGVUJUWPVVTXQYIUYPVXDVXOVXGVXRUYPVXCVXNVXBY
      TUYPVVJVUPUWAIVWAWEXTUYPUUIUUIVVLVURVXFVXQUYPVXEVXPUWAIUVFYPUVRXSWEUYPUUI
      WNVWBWOWQWRUVDUUIUUEVXQUOZUVEUVGUWAIUOZUOZUUIVWDVXFUOZUMZVOZKUGVPVXIDUFUX
      TVYEVXIKUGUXTUWDVBZUVDVWSVYDVXHVYFUVDAVWQVWRVBZVBVWSVYFBVYGAVYFBVWMUWJVWR
      UPZVYGBUWRVYFVYHTVYFUWGVWMUWQVWRUWJVYFYQYSUWFVYFYPYRGUXTUWDYJZVRWLVYFUWLV
      VEUWNVUJUWPVYFUVEYTUWKVVDUXTUWDWDZVYFYPYRUVFNVYIWHWGVYFUWMVUIUUEVYFYPYRUV
      RNVYIWEWIYKYLWKVWMUWJVWRYAWCWLAVWQVWRYMYCVYFVYBVXDVYCVXGVYFVXTVXBUVEYTVYA
      VXCVYFUVGVVJUWAIVYFYPYRUVFVYIYDZWEVYFVXQVXAUUIUUEVYFVXPVWTUWAIVYFYPYRUVRV
      YIWMWEXTVYJWOVYFVWDVVLUUIVXFVYFUUEUUEUVEYTVWCVVKVYFUVGVVJUVRIVYKWEVYFUUEW
      NVYJWOWHWQWRWSVYEKUGUEWTXAXAYNZADUFGHIJUGNPQRVYLUAUXEVUGYOVN $.
  $}

  ${
    $d f g x y .1. $.  $d f g x y B $.  $d f g x y ph $.  $d f g x y .x. $.
    $d f g x y C $.  $d f g x y H $.  $d f g x y X $.  $d f g x y Y $.
    $d f F $.
    catidcl.b $e |- B = ( Base ` C ) $.
    catidcl.h $e |- H = ( Hom ` C ) $.
    catidcl.i $e |- .1. = ( Id ` C ) $.
    catidcl.c $e |- ( ph -> C e. Cat ) $.
    catidcl.x $e |- ( ph -> X e. B ) $.
    $( Each object in a category has an associated identity arrow.
       (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    catidcl $p |- ( ph -> ( .1. ` X ) e. ( X H X ) ) $=
      ( vg vf vy cfv cv cop co wceq wral cco crio eqid cidval wreu wcel catideu
      wa riotacl syl eqeltrd ) AFDOLPZMPZNPZFQFCUAOZRRUMSMUNFERTUMULFFQUNUORRUM
      SMFUNERTUHNBTZLFFERZUBZUQANBCUODMLEFGHUOUCZJIKUDAUPLUQUEURUQUFANBCUOMLEFG
      HUSJKUGUPLUQUIUJUK $.

    catlid.o $e |- .x. = ( comp ` C ) $.
    catlid.y $e |- ( ph -> Y e. B ) $.
    catlid.f $e |- ( ph -> F e. ( X H Y ) ) $.
    $( Left identity property of an identity arrow.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    catlid $p |- ( ph -> ( ( .1. ` Y ) ( <. X , Y >. .x. Y ) F ) = F ) $=
      ( vf vg co vx cfv cv cop wceq oveq2 eqeq12d wral oveq1 opeq1 oveq1d oveqd
      id eqeq1d raleqbidv crab wcel wa wi simpl ralimi ss2rabi crio cidval wreu
      a1i catideu riotacl2 syl eqeltrd sselid 2ralbidv elrab simprbi rspcdva )
      AIEUBZRUCZHIUDZIDTZTZVQUEZVPFVSTZFUERHIGTZFVQFUEZVTWBVQFVQFVPVSUFWDUMUGAV
      PVQUAUCZIUDZIDTZTZVQUEZRWEIGTZUHZWARWCUHUABHWEHUEZWIWARWJWCWEHIGUIWLWHVTV
      QWLWGVSVPVQWLWFVRIDWEHIUJUKULUNUOAVPSUCZVQWGTZVQUEZRWJUHZUABUHZSIIGTZUPZU
      QZWKUABUHZAWPVQWMIIUDWEDTTVQUERIWEGTUHZURZUABUHZSWRUPZWSVPXDWQSWRXDWQUSWM
      WRUQXCWPUABWPXBUTVAVFVBAVPXDSWRVCZXEAUABCDERSGIJKOMLPVDAXDSWRVEXFXEUQAUAB
      CDRSGIJKOMPVGXDSWRVHVIVJVKWTVPWRUQXAWQXASVPWRWMVPUEZWOWIUARBWJXGWNWHVQWMV
      PVQWGUIUNVLVMVNVINVOQVO $.

    $( Right identity property of an identity arrow.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    catrid $p |- ( ph -> ( F ( <. X , X >. .x. Y ) ( .1. ` X ) ) = F ) $=
      ( vf vg co vy cv cfv cop wceq oveq1 id eqeq12d wral oveq2 oveqd raleqbidv
      eqeq1d crab wcel wa wi simpr ralimi a1i ss2rabi crio cidval wreu riotacl2
      catideu syl eqeltrd sselid 2ralbidv elrab simprbi rspcdva ) ARUBZHEUCZHHU
      DZIDTZTZVNUEZFVOVQTZFUERHIGTZFVNFUEZVRVTVNFVNFVOVQUFWBUGUHAVNVOVPUAUBZDTZ
      TZVNUEZRHWCGTZUIZVSRWAUIUABIWCIUEZWFVSRWGWAWCIHGUJWIWEVRVNWIWDVQVNVOWCIVP
      DUJUKUMULAVOVNSUBZWDTZVNUEZRWGUIZUABUIZSHHGTZUNZUOZWHUABUIZAWJVNWCHUDHDTT
      VNUERWCHGTUIZWMUPZUABUIZSWOUNZWPVOXAWNSWOXAWNUQWJWOUOWTWMUABWSWMURUSUTVAA
      VOXASWOVBZXBAUABCDERSGHJKOMLNVCAXASWOVDXCXBUOAUABCDRSGHJKOMNVFXASWOVEVGVH
      VIWQVOWOUOWRWNWRSVOWOWJVOUEZWLWFUARBWGXDWKWEVNWJVOVNWDUJUMVJVKVLVGPVMQVM
      $.
  $}

  ${
    $d f g k v w x y z B $.  $d f g k v w x y z C $.  $d f g k v w x y z .x. $.
    $d f g k w x y z F $.  $d f g k v w x y z H $.  $d f g k w x y z ph $.
    $d f g k w x y z G $.  $d f g k w x y z K $.  $d f g k w x y z W $.
    $d f g k w x y z X $.  $d f g k w x y z Y $.  $d f g k w x y z Z $.
    catcocl.b $e |- B = ( Base ` C ) $.
    catcocl.h $e |- H = ( Hom ` C ) $.
    catcocl.o $e |- .x. = ( comp ` C ) $.
    catcocl.c $e |- ( ph -> C e. Cat ) $.
    catcocl.x $e |- ( ph -> X e. B ) $.
    catcocl.y $e |- ( ph -> Y e. B ) $.
    catcocl.z $e |- ( ph -> Z e. B ) $.
    ${
      catcocl.f $e |- ( ph -> F e. ( X H Y ) ) $.
      catcocl.g $e |- ( ph -> G e. ( Y H Z ) ) $.
      $( Closure of a composition arrow.  (Contributed by Mario Carneiro,
         2-Jan-2017.) $)
      catcocl $p |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) e. ( X H Z ) ) $=
        ( co vg vf vx vy vz vv vw cv cop wcel wral ccat wceq wa iscat ibi simpl
        wrex 2ralimi adantl ralimi 3syl adantr ad3antrrr simpllr simplr oveq12d
        ad2antrr eleqtrrd simpr simp-5r simp-4r opeq12d oveq123d eleq12d rspcdv
        rspcimdv mpd ) AUAUHZUBUHZUCUHZUDUHZUIZUEUHZDTZTZWAWDGTZUJZUAWBWDGTZUKZ
        UBWAWBGTZUKZUEBUKZUDBUKZUCBUKZFEHIUIZJDTZTZHJGTZUJZACULUJZVSVTWBWAUIWAD
        TTVTUMUBWBWAGTUKVTVSWAWAUIWBDTTVTUMUBWKUKUNUDBUKUAWAWAGTURZWHUFUHZVSWBW
        DUIUGUHZDTTVTWCXDDTTXCWFWAWDUIXDDTTUMUFWDXDGTUKUGBUKZUNZUAWIUKUBWKUKZUE
        BUKUDBUKZUNZUCBUKZWONXAXJUCUDUEUGBCDUBUAUFGULKLMUOUPXIWNUCBXHWNXBXGWLUD
        UEBBXFWHUBUAWKWIWHXEUQUSUSUTVAVBAWNWTUCHBOAWAHUMZUNZWMWTUDIBAIBUJXKPVCX
        LWBIUMZUNZWLWTUEJBAJBUJXKXMQVHXNWDJUMZUNZWJWTUBEWKXPEHIGTZWKAEXQUJXKXMX
        ORVDXPWAHWBIGAXKXMXOVEXLXMXOVFZVGVIXPVTEUMZUNZWHWTUAFWIXPFWIUJXSXPFIJGT
        ZWIAFYAUJXKXMXOSVDXPWBIWDJGXRXNXOVJVGVIVCXTVSFUMZUNZWFWRWGWSYCVSFVTEWEW
        QYCWCWPWDJDYCWAHWBIAXKXMXOXSYBVKZXLXMXOXSYBVLVMXNXOXSYBVEZVGXTYBVJXPXSY
        BVFVNYCWAHWDJGYDYEVGVOVPVQVQVQVQVR $.

      catass.w $e |- ( ph -> W e. B ) $.
      catass.g $e |- ( ph -> K e. ( Z H W ) ) $.
      $( Associativity of composition in a category.  (Contributed by Mario
         Carneiro, 2-Jan-2017.) $)
      catass $p |- ( ph ->
       ( ( K ( <. Y , Z >. .x. W ) G ) ( <. X , Y >. .x. W ) F ) =
         ( K ( <. X , Z >. .x. W ) ( G ( <. X , Y >. .x. Z ) F ) ) ) $=
        ( vg vf vy vx vz vk vw cv cop co wceq wral wrex wcel ccat iscat ibi syl
        adantr ad2antrr simpllr simplr oveq12d eleqtrrd ad4antr ad5antr ad6antr
        ad3antrrr simp-4r simpr simp-7r simp-6r opeq12d simp-5r oveq123d rspcdv
        wa eqeq12d rspcimdv adantld mpd ) AUDUKZUEUKZUFUKZUGUKZULWHDUMUMWFUNUEW
        GWHGUMUOWFWEWHWHULWGDUMUMWFUNUEWHWGGUMZUOVTUFBUOUDWHWHGUMUPZWEWFWHWGULZ
        UHUKZDUMZUMZWHWLGUMUQZUIUKZWEWGWLULZUJUKZDUMZUMZWFWKWRDUMZUMZWPWNWHWLUL
        ZWRDUMZUMZUNZUIWLWRGUMZUOZUJBUOZVTZUDWGWLGUMZUOZUEWIUOZUHBUOZUFBUOZVTZU
        GBUOZHFKLULZIDUMZUMZEJKULZIDUMZUMZHFEYALDUMZUMZJLULZIDUMZUMZUNZACURUQZX
        QPYJXQUGUFUHUJBCDUEUDUIGURMNOUSUTVAAXPYIUGJBQAWHJUNZVTZXOYIWJYLXNYIUFKB
        AKBUQYKRVBYLWGKUNZVTZXMYIUHLBALBUQYKYMSVCYNWLLUNZVTZXLYIUEEWIYPEJKGUMZW
        IAEYQUQYKYMYOTVKYPWHJWGKGAYKYMYOVDYLYMYOVEVFVGYPWFEUNZVTZXJYIUDFXKYSFKL
        GUMZXKAFYTUQYKYMYOYRUAVHYSWGKWLLGYLYMYOYRVDYNYOYRVEVFVGYSWEFUNZVTZXIYIW
        OUUBXHYIUJIBAIBUQYKYMYOYRUUAUBVIUUBWRIUNZVTZXFYIUIHXGUUDHLIGUMZXGAHUUEU
        QYKYMYOYRUUAUUCUCVJUUDWLLWRIGYNYOYRUUAUUCVLUUBUUCVMVFVGUUDWPHUNZVTZXBYC
        XEYHUUGWTXTWFEXAYBUUGWKYAWRIDUUGWHJWGKAYKYMYOYRUUAUUCUUFVNZYLYMYOYRUUAU
        UCUUFVOZVPZUUBUUCUUFVEZVFUUGWPHWEFWSXSUUGWQXRWRIDUUGWGKWLLUUIYNYOYRUUAU
        UCUUFVQZVPUUKVFUUDUUFVMZYSUUAUUCUUFVDZVRYPYRUUAUUCUUFVLZVRUUGWPHWNYEXDY
        GUUGXCYFWRIDUUGWHJWLLUUHUULVPUUKVFUUMUUGWEFWFEWMYDUUGWKYAWLLDUUJUULVFUU
        NUUOVRVRWAVSWBWCWBWBWBWBWCWBWD $.
    $}

    catcone0.f $e |- ( ph -> ( X H Y ) =/= (/) ) $.
    catcone0.g $e |- ( ph -> ( Y H Z ) =/= (/) ) $.
    $( Composition of non-empty hom-sets is non-empty.  (Contributed by Zhi
       Wang, 18-Sep-2024.) $)
    catcone0 $p |- ( ph -> ( X H Z ) =/= (/) ) $=
      ( vf vg wex cv co wcel wa cop c0 n0 anbi12i exdistrv sylbb2 syl2anc ancli
      wne 19.42vv biimpri ccat adantr simprl simprr catcocl ne0i exlimivv 4syl
      2eximi ) AARUAZFGEUBZUCZSUAZGHEUBZUCZUDZSTRTZUDZAVKUDZSTRTZVHVEFGUEHDUBUB
      ZFHEUBZUCZSTRTVQUFUMZAVLAVFUFUMZVIUFUMZVLPQVTWAUDVGRTZVJSTZUDVLVTWBWAWCRV
      FUGSVIUGUHVGVJRSUIUJUKULVOVMAVKRSUNUOVNVRRSVNBCDVEVHEFGHIJKACUPUCVKLUQAFB
      UCVKMUQAGBUCVKNUQAHBUCVKOUQAVGVJURAVGVJUSUTVDVRVSRSVQVPVAVBVC $.
  $}

  ${
    $d f g h w x y z C $.  $d f g h w x y z V $.
    $( Any structure with an empty set of objects is a category.  (Contributed
       by Mario Carneiro, 3-Jan-2017.) $)
    0catg $p |- ( ( C e. V /\ (/) = ( Base ` C ) ) -> C e. Cat ) $=
      ( vx vy vz vw vf vg vh wcel c0 cfv wceq wa cv co pm2.21i w3a cop syl chom
      cbs cco simpr eqidd simpl noel adantl simpr1 simp21 simp2ll iscatd ) ABJZ
      KAUBLMZNZCDEFKAAUCLZKGHIAUALZBUMUNUDUOUQUEUOUPUEUMUNUFCOZKJZKURURUQPJZUOU
      SUTURUGZQUHUOUSDOZKJZGOZVBURUQPJZRNUSKVDVBURSURUPPPVDMZUOUSVCVEUIUSVFVAQT
      UOUSVCVDURVBUQPJZRNUSVDKURURSVBUPPPVDMZUOUSVCVGUIUSVHVAQTUOUSVCEOZKJZRVGH
      OZVBVIUQPJZNZRUSVKVDURVBSZVIUPPPZURVIUQPJZUOUSVCVJVMUJUSVPVAQTUOUSVCNVJFO
      ZKJNZNVGVLIOZVIVQUQPJRZRUSVSVKVBVISVQUPPPVDVNVQUPPPVSVOURVISVQUPPPMZUSVCV
      RUOVTUKUSWAVAQTUL $.
  $}

  $( The empty set is a category, the _empty category_, see example 3.3(4.c) in
     [Adamek] p. 24.  (Contributed by Mario Carneiro, 3-Jan-2017.) $)
  0cat $p |- (/) e. Cat $=
    ( c0 cvv wcel cbs cfv wceq ccat 0ex base0 0catg mp2an ) ABCAADEFAGCHIABJK
    $.

  ${
    $d c x y B $.  $d c x y C $.  $d c x y H $.  $d x y ph $.  $d x y X $.
    $d x y Y $.
    homffval.f $e |- F = ( Homf ` C ) $.
    homffval.b $e |- B = ( Base ` C ) $.
    homffval.h $e |- H = ( Hom ` C ) $.
    $( Value of the functionalized Hom-set operation.  (Contributed by Mario
       Carneiro, 4-Jan-2017.)  (Proof shortened by AV, 1-Mar-2024.) $)
    homffval $p |- F = ( x e. B , y e. B |-> ( x H y ) ) $=
      ( vc chomf cfv cv co cmpo cvv wceq cbs chom c0 wcel fveq2 eqtr4di df-homf
      oveqd mpoeq123dv fvexi mpoex fvmpt wn fvprc eqtrid olcd 0mpo0 syl pm2.61i
      wo eqtr4d eqtri ) EDKLZABCCAMZBMZFNZOZGDPUAZUTVDQJDABJMZRLZVGVAVBVFSLZNZO
      VDPKVFDQZABVGVGVICCVCVJVGDRLZCVFDRUBHUCZVLVJVHFVAVBVJVHDSLFVFDSUBIUCUEUFA
      BJUDABCCVCCDRHUGZVMUHUIVEUJZUTTVDDKUKVNCTQZVOUQVDTQVNVOVOVNCVKTHDRUKULUMA
      BCCVCUNUOURUPUS $.

    $( If the Hom-set operation is a function it is equal to the corresponding
       functionalized Hom-set operation.  (Contributed by AV, 1-Mar-2020.) $)
    fnhomeqhomf $p |- ( H Fn ( B X. B ) -> F = H ) $=
      ( vx vy cxp wfn cv co cmpo wceq fnov homffval eqeq2 mpbiri sylbi ) DAAJKD
      HIAAHLILDMNZOZCDOZHIAADPUBUCCUAOHIABCDEFGQDUACRST $.

    homfval.x $e |- ( ph -> X e. B ) $.
    homfval.y $e |- ( ph -> Y e. B ) $.
    $( Value of the functionalized Hom-set operation.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    homfval $p |- ( ph -> ( X F Y ) = ( X H Y ) ) $=
      ( vx vy cv co cvv cmpo wceq homffval a1i wa oveq12 adantl ovexd ovmpod )
      AMNFGBBMOZNOZEPZFGEPZDQDMNBBUIRSAMNBCDEHIJTUAUGFSUHGSUBUIUJSAUGFUHGEUCUDK
      LAFGEUEUF $.
  $}

  ${
    $d x y B $.  $d x y C $.
    homffn.f $e |- F = ( Homf ` C ) $.
    homffn.b $e |- B = ( Base ` C ) $.
    $( The functionalized Hom-set operation is a function.  (Contributed by
       Mario Carneiro, 4-Jan-2017.) $)
    homffn $p |- F Fn ( B X. B ) $=
      ( vx vy cv chom cfv co eqid homffval ovex fnmpoi ) FGAAFHZGHZBIJZKCFGABCR
      DERLMPQRNO $.
  $}

  ${
    $d x y B $.  $d x y C $.  $d x y D $.  $d x y H $.  $d x y ph $.
    $d x y J $.
    homfeq.h $e |- H = ( Hom ` C ) $.
    homfeq.j $e |- J = ( Hom ` D ) $.
    homfeq.1 $e |- ( ph -> B = ( Base ` C ) ) $.
    homfeq.2 $e |- ( ph -> B = ( Base ` D ) ) $.
    $( Condition for two categories with the same base to have the same
       hom-sets.  (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    homfeq $p |- ( ph -> ( ( Homf ` C ) = ( Homf ` D ) <->
      A. x e. B A. y e. B ( x H y ) = ( x J y ) ) ) $=
      ( chomf cfv wceq cv co cmpo wral eqid homffval mpoeq123dv eqtr4id eqeq12d
      cbs eqidd cvv wcel wb ovex rgen2w mpo2eqb ax-mp bitrdi ) AEMNZFMNZOBCDDBP
      ZCPZGQZRZBCDDUQURHQZRZOZUSVAOCDSBDSZAUOUTUPVBAUOBCEUENZVEUSRUTBCVEEUOGUOT
      VETIUAABCDDUSVEVEUSKKAUSUFUBUCAUPBCFUENZVFVARVBBCVFFUPHUPTVFTJUAABCDDVAVF
      VFVALLAVAUFUBUCUDUSUGUHZCDSBDSVCVDUIVGBCDDUQURGUJUKBCDDUSVAUGULUMUN $.
  $}

  ${
    $d x y C $.  $d x y D $.  $d x y ph $.
    homfeqd.1 $e |- ( ph -> ( Base ` C ) = ( Base ` D ) ) $.
    homfeqd.2 $e |- ( ph -> ( Hom ` C ) = ( Hom ` D ) ) $.
    $( If two structures have the same ` Hom ` slot, they have the same
       Hom-sets.  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    homfeqd $p |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $=
      ( vx vy chomf cfv wceq cv chom cbs wral oveqd ralrimivw eqid eqidd homfeq
      co mpbird ) ABHICHIJFKZGKZBLIZTUBUCCLIZTJZGBMIZNZFUGNAUHFUGAUFGUGAUDUEUBU
      CEOPPAFGUGBCUDUEUDQUEQAUGRDSUA $.
  $}

  ${
    homfeqbas.1 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    $( Deduce equality of base sets from equality of Hom-sets.  (Contributed by
       Mario Carneiro, 4-Jan-2017.) $)
    homfeqbas $p |- ( ph -> ( Base ` C ) = ( Base ` D ) ) $=
      ( cbs cfv cxp cdm chomf dmeqd eqid homffn fndmi 3eqtr3g dmxpid ) ABEFZPGZ
      HCEFZRGZHPRAQSABIFZHCIFZHQSATUADJQTPBTTKPKLMSUARCUAUAKRKLMNJPORON $.
  $}

  ${
    homfeqval.b $e |- B = ( Base ` C ) $.
    homfeqval.h $e |- H = ( Hom ` C ) $.
    homfeqval.j $e |- J = ( Hom ` D ) $.
    homfeqval.1 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    homfeqval.x $e |- ( ph -> X e. B ) $.
    homfeqval.y $e |- ( ph -> Y e. B ) $.
    $( Value of the functionalized Hom-set operation.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    homfeqval $p |- ( ph -> ( X H Y ) = ( X J Y ) ) $=
      ( chomf cfv co eqid homfval cbs oveqd homfeqbas eqtrid eleqtrd 3eqtr3d )
      AGHCOPZQGHDOPZQGHEQGHFQAUFUGGHLUAABCUFEGHUFRIJMNSADTPZDUGFGHUGRUHRKAGBUHM
      ABCTPUHIACDLUBUCZUDAHBUHNUIUDSUE $.
  $}

  ${
    $d c x y z B $.  $d c f g x y z C $.  $d f g x z ph $.  $d c f g x z .x. $.
    $d f g F $.  $d f g G $.  $d f g x z X $.  $d f g x z Y $.  $d f g x z Z $.
    $d c f g x z H $.
    comfffval.o $e |- O = ( comf ` C ) $.
    comfffval.b $e |- B = ( Base ` C ) $.
    comfffval.h $e |- H = ( Hom ` C ) $.
    comfffval.x $e |- .x. = ( comp ` C ) $.
    $( Value of the functionalized composition operation.  (Contributed by
       Mario Carneiro, 4-Jan-2017.)  (Proof shortened by AV, 1-Mar-2024.) $)
    comfffval $p |- O = ( x e. ( B X. B ) , y e. B |->
     ( g e. ( ( 2nd ` x ) H y ) , f e. ( H ` x ) |-> ( g ( x .x. y ) f ) ) ) $=
      ( cfv cv co cmpo wceq cbs c0 vc ccomf cxp c2nd cvv wcel cco fveq2 eqtr4di
      chom sqxpeqd oveqd fveq1d mpoeq123dv df-comf fvexi xpex mpoex fvmpt fvprc
      wn wo eqtrid olcd 0mpo0 syl eqtr4d pm2.61i eqtri ) IDUBNZABCCUCZCGFAOZUDN
      ZBOZHPZVLHNZGOZFOZVLVNEPZPZQZQZJDUEUFZVJWBRUADABUAOZSNZWEUCZWEGFVMVNWDUJN
      ZPZVLWGNZVQVRVLVNWDUGNZPZPZQZQWBUEUBWDDRZABWFWEWMVKCWAWNWECWNWEDSNZCWDDSU
      HKUIZUKWPWNGFWHWIWLVOVPVTWNWGHVMVNWNWGDUJNHWDDUJUHLUIZULWNVLWGHWQUMWNWKVS
      VQVRWNWJEVLVNWNWJDUGNEWDDUGUHMUIULULUNUNABFGUAUOABVKCWACCCDSKUPZWRUQWRURU
      SWCVAZVJTWBDUBUTWSVKTRZCTRZVBWBTRWSXAWTWSCWOTKDSUTVCVDABVKCWAVEVFVGVHVI
      $.

    comffval.x $e |- ( ph -> X e. B ) $.
    comffval.y $e |- ( ph -> Y e. B ) $.
    comffval.z $e |- ( ph -> Z e. B ) $.
    $( Value of the functionalized composition operation.  (Contributed by
       Mario Carneiro, 4-Jan-2017.) $)
    comffval $p |- ( ph -> ( <. X , Y >. O Z ) =
     ( g e. ( Y H Z ) , f e. ( X H Y ) |-> ( g ( <. X , Y >. .x. Z ) f ) ) ) $=
      ( vx co vz cop cxp cv c2nd cfv cmpo cvv wceq comfffval a1i wa simprl wcel
      fveq2d op2ndg syl2anc adantr eqtrd oveq12d df-ov eqtr4di oveqd mpoeq123dv
      simprr opelxpd ovex mpoex ovmpod ) ASUAIJUBZKBBUCZBFESUDZUEUFZUAUDZGTZVLG
      UFZFUDZEUDZVLVNDTZTZUGZFEJKGTZIJGTZVQVRVJKDTZTZUGZHUHHSUAVKBWAUGUIASUABCD
      EFGHLMNOUJUKAVLVJUIZVNKUIZULZULZFEVOVPVTWBWCWEWJVMJVNKGWJVMVJUEUFZJWJVLVJ
      UEAWGWHUMZUOAWKJUIZWIAIBUNJBUNWMPQIJBBUPUQURUSAWGWHVEZUTWJVPVJGUFWCWJVLVJ
      GWLUOIJGVAVBWJVSWDVQVRWJVLVJVNKDWLWNUTVCVDAIJBBPQVFRWFUHUNAFEWBWCWEJKGVGI
      JGVGVHUKVI $.

    comfval.f $e |- ( ph -> F e. ( X H Y ) ) $.
    comfval.g $e |- ( ph -> G e. ( Y H Z ) ) $.
    $( Value of the functionalized composition operation.  (Contributed by
       Mario Carneiro, 4-Jan-2017.) $)
    comfval $p |- ( ph ->
      ( G ( <. X , Y >. O Z ) F ) = ( G ( <. X , Y >. .x. Z ) F ) ) $=
      ( vg vf co cv cop cvv comffval wceq wa oveq12 adantl ovexd ovmpod ) AUAUB
      FEJKGUCIJGUCUAUDZUBUDZIJUEZKDUCZUCZFEUQUCZUPKHUCUFABCDUBUAGHIJKLMNOPQRUGU
      NFUHUOEUHUIURUSUHAUNFUOEUQUJUKTSAFEUQULUM $.
  $}

  ${
    $d f g x y B $.  $d f g x y C $.  $d f g x .x. $.  $d f g X $.  $d f g Y $.
    $d f g ph $.  $d f g Z $.
    comfffval2.o $e |- O = ( comf ` C ) $.
    comfffval2.b $e |- B = ( Base ` C ) $.
    comfffval2.h $e |- H = ( Homf ` C ) $.
    comfffval2.x $e |- .x. = ( comp ` C ) $.
    $( Value of the functionalized composition operation.  (Contributed by
       Mario Carneiro, 4-Jan-2017.) $)
    comfffval2 $p |- O = ( x e. ( B X. B ) , y e. B |->
     ( g e. ( ( 2nd ` x ) H y ) , f e. ( H ` x ) |-> ( g ( x .x. y ) f ) ) ) $=
      ( cv cfv co cmpo wcel adantr homfval c2nd chom eqid comfffval xp2nd simpr
      cxp wa c1st cop xp1st df-ov 3eqtr3g wceq 1st2nd2 3eqtr4d eqidd mpoeq123dv
      fveq2d mpoeq3ia eqtr4i ) IABCCUGZCGFANZUAOZBNZDUBOZPZVCVFOZGNFNVCVEEPPZQZ
      QABVBCGFVDVEHPZVCHOZVIQZQABCDEFGVFIJKVFUCZMUDABVBCVMVJVCVBRZVECRZUHZGFVKV
      LVIVGVHVIVQCDHVFVDVELKVNVOVDCRVPVCCCUESZVOVPUFTVQVCUIOZVDUJZHOZVTVFOZVLVH
      VQVSVDHPVSVDVFPWAWBVQCDHVFVSVDLKVNVOVSCRVPVCCCUKSVRTVSVDHULVSVDVFULUMVQVC
      VTHVOVCVTUNVPVCCCUOSZUSVQVCVTVFWCUSUPVQVIUQURUTVA $.

    comffval2.x $e |- ( ph -> X e. B ) $.
    comffval2.y $e |- ( ph -> Y e. B ) $.
    comffval2.z $e |- ( ph -> Z e. B ) $.
    $( Value of the functionalized composition operation.  (Contributed by
       Mario Carneiro, 4-Jan-2017.) $)
    comffval2 $p |- ( ph -> ( <. X , Y >. O Z ) =
     ( g e. ( Y H Z ) , f e. ( X H Y ) |-> ( g ( <. X , Y >. .x. Z ) f ) ) ) $=
      ( co cv cop chom cfv cmpo eqid comffval homfval eqidd mpoeq123dv eqtr4d )
      AIJUAZKHSFEJKCUBUCZSZIJULSZFTETUKKDSSZUDFEJKGSZIJGSZUOUDABCDEFULHIJKLMULU
      EZOPQRUFAFEUPUQUOUMUNUOABCGULJKNMURQRUGABCGULIJNMURPQUGAUOUHUIUJ $.

    comfval2.f $e |- ( ph -> F e. ( X H Y ) ) $.
    comfval2.g $e |- ( ph -> G e. ( Y H Z ) ) $.
    $( Value of the functionalized composition operation.  (Contributed by
       Mario Carneiro, 4-Jan-2017.) $)
    comfval2 $p |- ( ph ->
      ( G ( <. X , Y >. O Z ) F ) = ( G ( <. X , Y >. .x. Z ) F ) ) $=
      ( chom cfv eqid co homfval eleqtrd comfval ) ABCDEFCUAUBZHIJKLMUHUCZOPQRA
      EIJGUDIJUHUDSABCGUHIJNMUIPQUEUFAFJKGUDJKUHUDTABCGUHJKNMUIQRUEUFUG $.
  $}

  ${
    $d x y B $.  $d f g x y C $.  $d f g H $.  $d f g ph $.  $d f g X $.
    $d f g Y $.  $d f g Z $.
    comfffn.o $e |- O = ( comf ` C ) $.
    comfffn.b $e |- B = ( Base ` C ) $.
    $( The functionalized composition operation is a function.  (Contributed by
       Mario Carneiro, 4-Jan-2017.) $)
    comfffn $p |- O Fn ( ( B X. B ) X. B ) $=
      ( vx vy vg vf cxp cv c2nd cfv chom co cco cmpo eqid comfffval ovex fnmpoi
      fvex mpoex ) FGAAJAHIFKZLMZGKZBNMZOZUDUGMZHKIKUDUFBPMZOOZQCFGABUJIHUGCDEU
      GRUJRSHIUHUIUKUEUFUGTUDUGUBUCUA $.

    comffn.h $e |- H = ( Hom ` C ) $.
    comffn.x $e |- ( ph -> X e. B ) $.
    comffn.y $e |- ( ph -> Y e. B ) $.
    comffn.z $e |- ( ph -> Z e. B ) $.
    $( The functionalized composition operation is a function.  (Contributed by
       Mario Carneiro, 4-Jan-2017.) $)
    comffn $p |- ( ph -> ( <. X , Y >. O Z ) Fn ( ( Y H Z ) X. ( X H Y ) ) ) $=
      ( vg vf co wfn cv eqid cop cxp cco cfv cmpo fnmpoi comffval fneq1d mpbiri
      ovex ) AFGUAZHEQZGHDQZFGDQZUBZROPUMUNOSZPSZUKHCUCUDZQZQZUEZUOROPUMUNUTVAV
      ATUPUQUSUJUFAUOULVAABCURPODEFGHIJKURTLMNUGUHUI $.
  $}

  ${
    $d f g u x y z B $.  $d f g u z C $.  $d f g u z ph $.  $d f g u x y .x. $.
    $d f g u z D $.  $d f g u x y H $.  $d f g u x y .xb $.
    comfeq.1 $e |- .x. = ( comp ` C ) $.
    comfeq.2 $e |- .xb = ( comp ` D ) $.
    comfeq.h $e |- H = ( Hom ` C ) $.
    comfeq.3 $e |- ( ph -> B = ( Base ` C ) ) $.
    comfeq.4 $e |- ( ph -> B = ( Base ` D ) ) $.
    comfeq.5 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    $( Condition for two categories with the same hom-sets to have the same
       composition.  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    comfeq $p |- ( ph -> ( ( comf ` C ) = ( comf ` D ) <->
      A. x e. B A. y e. B A. z e. B A. f e. ( x H y ) A. g e. ( y H z )
      ( g ( <. x , y >. .x. z ) f ) = ( g ( <. x , y >. .xb z ) f ) ) ) $=
      ( vu wral cxp cv c2nd cfv co cmpo wceq ccomf cop sqxpeqd eqidd mpoeq123dv
      cbs eqid comfffval eqtr4di chom w3a chomf 3ad2ant1 xp2nd 3ad2ant2 eleqtrd
      wcel simp3 homfeqval xp1st df-ov 3eqtr3g 1st2nd2 fveq2d 3eqtr4d mpoeq3dva
      c1st eqtrd eqeq12d cvv wb ovex fvex mpoex rgen2w mpo2eqb ax-mp vex op2ndd
      oveq1d fveq2 oveq1 oveqd raleqbidv ralcom 3bitr4g ralbidv ralxp bitr3di
      bitri ) ASDEEUAZEKJSUBZUCUDZDUBZLUEZWSLUDZKUBZJUBZWSXAIUEZUEZUFZUFZSDWREK
      JXBXCXDXEWSXAHUEZUEZUFZUFZUGZFUHUDZGUHUDZUGXDXEBUBZCUBZUIZXAIUEZUEZXDXEXS
      XAHUEZUEZUGZKXRXALUEZTJXQXRLUEZTZDETZCETBETZAXIXOXMXPAXISDFUMUDZYJUAZYJXH
      UFXOASDWREXHYKYJXHAEYJPUJPAXHUKULSDYJFIJKLXOXOUNYJUNZOMUOUPAXMSDGUMUDZYMU
      AZYMKJWTXAGUQUDZUEZWSYOUDZXKUFZUFZXPAXMSDWREYRUFYSASDWREXLYRAWSWRVDZXAEVD
      ZURZKJXBXCXKYPYQXKUUBYJFGLYOWTXAYLOYOUNZAYTFUSUDGUSUDUGUUARUTZUUBWTEYJYTA
      WTEVDUUAWSEEVAVBAYTEYJUGUUAPUTZVCZUUBXAEYJAYTUUAVEUUEVCVFUUBWSVNUDZWTUIZL
      UDZUUHYOUDZXCYQUUBUUGWTLUEUUGWTYOUEUUIUUJUUBYJFGLYOUUGWTYLOUUCUUDUUBUUGEY
      JYTAUUGEVDUUAWSEEVGVBUUEVCUUFVFUUGWTLVHUUGWTYOVHVIUUBWSUUHLYTAWSUUHUGUUAW
      SEEVJVBZVKUUBWSUUHYOUUKVKVLUUBXKUKULVMASDWREYRYNYMYRAEYMQUJQAYRUKULVOSDYM
      GHJKYOXPXPUNYMUNUUCNUOUPVPXNXHXLUGZDETZSWRTZYIXHVQVDZDETSWRTXNUUNVRUUOSDW
      REKJXBXCXGWTXALVSWSLVTWAWBSDWREXHXLVQWCWDUUMYHSBCEEWSXSUGZUULYGDEUUPXGXKU
      GZJXCTZKXBTZYDJYFTZKYETUULYGUUPUURUUTKXBYEUUPWTXRXALXQXRWSBWECWEWFWGUUPUU
      QYDJXCYFUUPXCXSLUDYFWSXSLWHXQXRLVHUPUUPXGYAXKYCUUPXFXTXDXEWSXSXAIWIWJUUPX
      JYBXDXEWSXSXAHWIWJVPWKWKXGVQVDZJXCTKXBTUULUUSVRUVAKJXBXCXDXEXFVSWBKJXBXCX
      GXKVQWCWDYDJKYFYEWLWMWNWOWQWP $.
  $}

  ${
    $d f g x y z C $.  $d f g x y z D $.  $d f g x y z ph $.
    comfeqd.1 $e |- ( ph -> ( comp ` C ) = ( comp ` D ) ) $.
    comfeqd.2 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    $( Condition for two categories with the same hom-sets to have the same
       composition.  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    comfeqd $p |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $=
      ( vg vf vx vy vz ccomf cfv wceq cv cco co wral oveqd ralrimivw eqid eqidd
      cop chom cbs homfeqbas comfeq mpbird ) ABKLCKLMFNZGNZHNZINZUBZJNZBOLZPZPU
      HUIULUMCOLZPZPMZFUKUMBUCLZPZQZGUJUKUSPZQZJBUDLZQZIVDQZHVDQAVFHVDAVEIVDAVC
      JVDAVAGVBAURFUTAUOUQUHUIAUNUPULUMDRRSSSSSAHIJVDBCUPUNGFUSUNTUPTUSTAVDUAAB
      CEUEEUFUG $.
  $}

  ${
    comfeqval.b $e |- B = ( Base ` C ) $.
    comfeqval.h $e |- H = ( Hom ` C ) $.
    comfeqval.1 $e |- .x. = ( comp ` C ) $.
    comfeqval.2 $e |- .xb = ( comp ` D ) $.
    comfeqval.3 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    comfeqval.4 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    comfeqval.x $e |- ( ph -> X e. B ) $.
    comfeqval.y $e |- ( ph -> Y e. B ) $.
    comfeqval.z $e |- ( ph -> Z e. B ) $.
    comfeqval.f $e |- ( ph -> F e. ( X H Y ) ) $.
    comfeqval.g $e |- ( ph -> G e. ( Y H Z ) ) $.
    $( Equality of two compositions.  (Contributed by Mario Carneiro,
       4-Jan-2017.) $)
    comfeqval $p |- ( ph ->
      ( G ( <. X , Y >. .x. Z ) F ) = ( G ( <. X , Y >. .xb Z ) F ) ) $=
      ( cop ccomf cfv co oveqd eqid comfval cbs chom homfeqbas eqtrid homfeqval
      eleqtrd 3eqtr3d ) AHGJKUDZLCUEUFZUGZUGHGURLDUEUFZUGZUGHGURLFUGUGHGURLEUGU
      GAUTVBHGAUSVAURLRUHUHABCFGHIUSJKLUSUIMNOSTUAUBUCUJADUKUFZDEGHDULUFZVAJKLV
      AUIVCUIVDUIZPAJBVCSABCUKUFVCMACDQUMUNZUPAKBVCTVFUPALBVCUAVFUPAGJKIUGJKVDU
      GUBABCDIVDJKMNVEQSTUOUPAHKLIUGKLVDUGUCABCDIVDKLMNVEQTUAUOUPUJUQ $.
  $}

  ${
    $d f g h w x y z C $.  $d f g h w x y z D $.  $d f g h w x y z ph $.
    catpropd.1 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    catpropd.2 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    catpropd.3 $e |- ( ph -> C e. V ) $.
    catpropd.4 $e |- ( ph -> D e. W ) $.
    $( Two structures with the same base, hom-sets and composition operation
       are either both categories or neither.  (Contributed by Mario Carneiro,
       5-Jan-2017.) $)
    catpropd $p |- ( ph -> ( C e. Cat <-> D e. Cat ) ) $=
      ( vg vf vy vz vh vw co wceq wral wa wcel vx cv cop cco cfv chom wrex ccat
      cbs wi simpl 2ralimi adantl ralimi a1i wb nfra1 nfv oveq1 eleq1d cbvralvw
      oveq2 ralbidv bitrid cbvralw oveqd eleq12d raleqbidv oveq1d ralcom bitrdi
      opeq2 opeq1 biimpi ancri r19.26 eqid chomf adantr ad4antr ad5antr simpllr
      ccomf ad2antrr simp-4r simplr simpr comfeqval eqeq12d ralimdva ralbi syl6
      ex impancom impr syl anbi2d biimtrrid expdimp an32s expimpd imp an4s expr
      syl56 pm5.21ndd homfeqbas homfeqval raleqbidva anbi12d rexeqbidva ad7antr
      eqeq1d oveq2d bitrd iscat 3bitr4d ) AJUBZKUBZLUBZUAUBZUCZYABUDUEZPPZXSQZK
      XTYABUFUEZPZRZXSXRYAYAUCZXTYCPPZXSQZKYAXTYFPZRZSZLBUIUEZRZJYAYAYFPZUGZXRX
      SYAXTUCZMUBZYCPZPZYAYTYFPZTZNUBZXRXTYTUCZOUBZYCPZPZXSYSUUGYCPZPZUUEUUBYAY
      TUCZUUGYCPZPZQZNYTUUGYFPZRZOYORZSZJXTYTYFPZRZKYLRZMYORZLYORZSZUAYORZXRXSY
      BYACUDUEZPPZXSQZKXTYACUFUEZPZRZXSXRYIXTUVGPPZXSQZKYAXTUVJPZRZSZLCUIUEZRZJ
      YAYAUVJPZUGZXRXSYSYTUVGPPZYAYTUVJPZTZUUEXRUUFUUGUVGPPZXSYSUUGUVGPZPZUUEUW
      BUULUUGUVGPZPZQZNYTUUGUVJPZRZOUVRRZSZJXTYTUVJPZRZKUVORZMUVRRZLUVRRZSZUAUV
      RRZBUHTZCUHTZAUVFYRUUDUUIXSUWFPZUUEUUBUWHPZQZNUUPRZOYORZSZJUUTRZKYLRZMYOR
      ZLYORZSZUAYORZUXAAUUDJUUTRZKYLRZMYORZLYORZUAYORZUVFUXOUVFUXTUJAUVEUXSUAYO
      UVDUXSYRUVBUXQLMYOYOUUSUUDKJYLUUTUUDUURUKULULUMUNUOUXOUXTUJAUXNUXSUAYOUXM
      UXSYRUXKUXQLMYOYOUXIUUDKJYLUUTUUDUXHUKULULUMUNUOUXTUUIXTUUGYFPZTZNUUPRZOY
      ORZJUUTRZMYORZLYORZUXTSAUVEUXNUPZUAYORZUVFUXOUPUXTUYGUXTUYGUXSUYFUALYOUXR
      LYOUQUYFUAURUXSUUEXRUUMPZYAUUGYFPZTZNUUPRZJUUCRZOYORZMYORYAXTQZUYFUXRUYOL
      MYOUXQMYOUQUYOLURUXRUUEXRUUJPZUYKTZNUYARZJYLRZOYORXTYTQZUYOUXQUYTMOYOUXQU
      UEXRUUAPZUUCTZNUUTRZJYLRYTUUGQZUYTUXPVUDKJYLUUDJUUTUQVUDKURUXPUUEXSUUAPZU
      UCTZNUUTRXSXRQZVUDUUDVUGJNUUTXRUUEQUUBVUFUUCXRUUEXSUUAUSUTVAVUHVUGVUCNUUT
      VUHVUFVUBUUCXSXRUUEUUAVBUTVCVDVEVUEVUDUYSJYLVUEVUCUYRNUUTUYAYTUUGXTYFVBVU
      EVUBUYQUUCUYKVUEUUAUUJUUEXRYTUUGYSYCVBVFYTUUGYAYFVBVGVHVCVDVAVUAUYTUYNOYO
      VUAUYSUYMJYLUUCXTYTYAYFVBVUAUYRUYLNUYAUUPXTYTUUGYFUSVUAUYQUYJUYKVUAUUJUUM
      UUEXRVUAYSUULUUGYCXTYTYAVLVIVFUTVHVHVCVDVEUYPUYOUYEMYOUYPUYOUYCJUUTRZOYOR
      UYEUYPUYNVUIOYOUYPUYMUYCJUUCUUTYAXTYTYFUSUYPUYLUYBNUUPUYPUYJUUIUYKUYAUYPU
      UMUUHUUEXRUYPUULUUFUUGYCYAXTYTVMVIVFYAXTUUGYFUSVGVCVHVCUYCOJYOUUTVJVKVCVD
      VEVNVOAUYGUXTUYIAUYGSZUXSUYHUAYOVUJYAYOTZUXSUYHVUJVUKUXSSSUVDUXMYRAVUKUYG
      UXSUVDUXMUPZAVUKSZUYGUXSSZVULVUNUYFUXRSZLYORZVUMVULUYFUXRLYOVPVUMVUPUVCUX
      LUPZLYORVULVUMVUOVUQLYOVUOUYEUXQSZMYORZVUMXTYOTZSZVUQUYEUXQMYOVPVVAVUSUVB
      UXKUPZMYORVUQVVAVURVVBMYOVVAYTYOTZSZUYEUXQVVBVVDUYESZUXQUVAUXJUPZKYLRVVBV
      VEUXPVVFKYLVVDXSYLTZUYEUXPVVFUJVVDVVGSZUYESUXPUUSUXIUPZJUUTRZVVFVVHUYEUXP
      VVJUYEUXPSUYDUUDSZJUUTRVVHVVJUYDUUDJUUTVPVVHVVKVVIJUUTVVHXRUUTTZSZVVKVVIV
      VMVVKSZUURUXHUUDVVNUUQUXGUPZOYORZUURUXHUPVVMUYDUUDVVPVVMUUDUYDVVPVVMUUDSZ
      UYCVVOOYOVVQUUGYOTZSZUYCUUOUXFUPZNUUPRVVOVVSUYBVVTNUUPVVSUUEUUPTZSZUYBVVT
      VWBUYBSZUUKUXDUUNUXEVWCYOBCUVGYCXSUUIYFYAXTUUGYOVQZYFVQZYCVQZUVGVQZVVMBVR
      UECVRUEQZUUDVVRVWAUYBVUMVWHVUTVVCVVGVVLAVWHVUKFVSZVTZVTZVVMBWCUECWCUEQZUU
      DVVRVWAUYBAVWLVUKVUTVVCVVGVVLGWAZVTZVVMVUKUUDVVRVWAUYBVVDVUKVVGVVLAVUKVUT
      VVCWBZWDZVTZVVMVUTUUDVVRVWAUYBVUMVUTVVCVVGVVLWEZVTVVQVVRVWAUYBWBZVVMVVGUU
      DVVRVWAUYBVVDVVGVVLWFZVTVWBUYBWGWHVWCYOBCUVGYCUUBUUEYFYAYTUUGVWDVWEVWFVWG
      VWKVWNVWQVVMVVCUUDVVRVWAUYBVVAVVCVVGVVLWBZVTVWSVVMUUDVVRVWAUYBWEVVSVWAUYB
      WFWHWIWMWJUUOUXFNUUPWKWLWJWNWOUUQUXGOYOWKWPWQWMWJWRWSUUSUXIJUUTWKWLWTWJUV
      AUXJKYLWKWLXAWJUVBUXKMYOWKWLWRWJUVCUXLLYOWKWLWRXBXCWQXDWJXAUVEUXNUAYOWKXE
      XFAUXNUWTUAYOUVRABCFXGZVUMYRUWAUXMUWSVUMYPUVSJYQUVTVUMYOBCYFUVJYAYAVWDVWE
      UVJVQZVWIAVUKWGZVXDXHVUMXRYQTZSZYNUVQLYOUVRAYOUVRQZVUKVXEVXBWDVXFVUTSZYHU
      VLYMUVPVXHYEUVIKYGUVKVXHYOBCYFUVJXTYAVWDVWEVXCVUMVWHVXEVUTVWIWDZVXFVUTWGZ
      AVUKVXEVUTWBZXHVXHXSYGTZSZYDUVHXSVXMYOBCUVGYCXSXRYFXTYAYAVWDVWEVWFVWGAVWH
      VUKVXEVUTVXLFVTAVWLVUKVXEVUTVXLGVTVXFVUTVXLWFAVUKVXEVUTVXLWEZVXNVXHVXLWGV
      UMVXEVUTVXLWBWHXMXIVXHYKUVNKYLUVOVXHYOBCYFUVJYAXTVWDVWEVXCVXIVXKVXJXHVXHV
      VGSZYJUVMXSVXOYOBCUVGYCXRXSYFYAYAXTVWDVWEVWFVWGAVWHVUKVXEVUTVVGFVTAVWLVUK
      VXEVUTVVGGVTAVUKVXEVUTVVGWEZVXPVXFVUTVVGWFVUMVXEVUTVVGWBVXHVVGWGWHXMXIXJX
      IXKVUMUXLUWRLYOUVRAVXGVUKVXBVSZVVAUXKUWQMYOUVRVUMVXGVUTVXQVSVVDUXJUWPKYLU
      VOVVDYOBCYFUVJYAXTVWDVWEVXCVUMVWHVUTVVCVWIWDZVWOVUMVUTVVCWFZXHVVHUXIUWNJU
      UTUWOVVDUUTUWOQVVGVVDYOBCYFUVJXTYTVWDVWEVXCVXRVXSVVAVVCWGZXHVSVVMUUDUWDUX
      HUWMVVMUUBUWBUUCUWCVVMYOBCUVGYCXSXRYFYAXTYTVWDVWEVWFVWGVWJVWMVWPVWRVXAVWT
      VVHVVLWGWHVVDUUCUWCQVVGVVLVVDYOBCYFUVJYAYTVWDVWEVXCVXRVWOVXTXHWDVGVVMUXGU
      WLOYOUVRVUMVXGVUTVVCVVGVVLVXQVTVVMVVRSZUXFUWJNUUPUWKVYAYOBCYFUVJYTUUGVWDV
      WEVXCVVMVWHVVRVWJVSVVAVVCVVGVVLVVRWEVVMVVRWGXHVYAVWASZUXDUWGUXEUWIVYBUUIU
      WEXSUWFVYBYOBCUVGYCXRUUEYFXTYTUUGVWDVWEVWFVWGVVDVWHVVGVVLVVRVWAVXRVTZAVWL
      VUKVUTVVCVVGVVLVVRVWAGXLZVVDVUTVVGVVLVVRVWAVXSVTZVVDVVCVVGVVLVVRVWAVXTVTZ
      VVMVVRVWAWFVVHVVLVVRVWAWBZVYAVWAWGWHVIVYBUUBUWBUUEUWHVYBYOBCUVGYCXSXRYFYA
      XTYTVWDVWEVWFVWGVYCVYDVVDVUKVVGVVLVVRVWAVWOVTVYEVYFVVDVVGVVLVVRVWAWEVYGWH
      XNWIXIXIXJXIXIXIXIXJXIXOABDTUXBUVFUPHUALMOYOBYCKJNYFDVWDVWEVWFXPWPACETUXC
      UXAUPIUALMOUVRCUVGKJNUVJEUVRVQVXCVWGXPWPXQ $.

    $( Two structures with the same base, hom-sets and composition operation
       have the same identity function.  (Contributed by Mario Carneiro,
       17-Jan-2017.) $)
    cidpropd $p |- ( ph -> ( Id ` C ) = ( Id ` D ) ) $=
      ( vx vg vf vy wcel cfv wceq wa co wral eqid ccat ccid cbs cv cop cco chom
      crio homfeqbas adantr chomf ad4antr simpr simpllr homfeqval ad5antr ccomf
      cmpt simplr simp-4r comfeqval eqeq1d raleqbidva anbi12d ralbidva ad2antrr
      riotabidva raleqdv riotaeqbidv mpteq12dva cidfval catpropd biimpa 3eqtr4d
      eqtrd wn c0 cdm cidffn fndmi eleq2i sylnibr ndmfv notbid eqtr4d pm2.61dan
      syl bitr4di ) ABUANZBUBOZCUBOZPAWIQZJBUCOZKUDZLUDZMUDZJUDZUEZWQBUFOZRRZWO
      PZLWPWQBUGOZRZSZWOWNWQWQUEZWPWSRRZWOPZLWQWPXBRZSZQZMWMSZKWQWQXBRZUHZURJCU
      COZWNWOWRWQCUFOZRRZWOPZLWPWQCUGOZRZSZWOWNXEWPXORRZWOPZLWQWPXRRZSZQZMXNSZK
      WQWQXRRZUHZURWJWKWLJWMXMXNYHAWMXNPZWIABCFUIZUJWLWQWMNZQZXMYEMWMSZKXLUHYHY
      LXKYMKXLYLWNXLNZQZXJYEMWMYOWPWMNZQZXDXTXIYDYQXAXQLXCXSYQWMBCXBXRWPWQWMTZX
      BTZXRTZABUKOCUKOPZWIYKYNYPFULZYOYPUMZWLYKYNYPUNZUOYQWOXCNZQZWTXPWOUUFWMBC
      XOWSWOWNXBWPWQWQYRYSWSTZXOTZAUUAWIYKYNYPUUEFUPABUQOCUQOPZWIYKYNYPUUEGUPYO
      YPUUEUSWLYKYNYPUUEUTZUUJYQUUEUMYLYNYPUUEUNVAVBVCYQXGYBLXHYCYQWMBCXBXRWQWP
      YRYSYTUUBUUDUUCUOYQWOXHNZQZXFYAWOUULWMBCXOWSWNWOXBWQWQWPYRYSUUGUUHYQUUAUU
      KUUBUJAUUIWIYKYNYPUUKGUPYQYKUUKUUDUJZUUMYOYPUUKUSYLYNYPUUKUNYQUUKUMVAVBVC
      VDVEVGYLYMYFKXLYGYLWMBCXBXRWQWQYRYSYTAUUAWIYKFVFWLYKUMZUUNUOYLYEMWMXNAYIW
      IYKYJVFVHVIVOVJWLJMWMBWSWJLKXBYRYSUUGAWIUMWJTVKWLJMXNCXOWKLKXRXNTYTUUHAWI
      CUANZABCDEFGHIVLZVMWKTVKVNAWIVPZQZWJVQWKUURBUBVRZNZVPWJVQPUURWIUUTAUUQUMU
      USUABUAUBVSVTZWAWBBUBWCWGUURCUUSNZVPZWKVQPAUUQUVCAWIUVBAWIUUOUVBUUPUUSUAC
      UVAWAWHWDVMCUBWCWGWEWF $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Opposite category
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Introduce new constant symbols. $)
  $c oppCat $. $( Opposite category $)

  $( The opposite category operation. $)
  coppc $a class oppCat $.

  ${
    $d f u z $.
    $( Define an opposite category, which is the same as the original category
       but with the direction of arrows the other way around.  Definition 3.5
       of [Adamek] p. 25.  (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    df-oppc $a |- oppCat = ( f e. _V |-> ( ( f sSet
      <. ( Hom ` ndx ) , tpos ( Hom ` f ) >. ) sSet <. ( comp ` ndx ) ,
        ( u e. ( ( Base ` f ) X. ( Base ` f ) ) , z e. ( Base ` f ) |->
          tpos ( <. z , ( 2nd ` u ) >. ( comp ` f ) ( 1st ` u ) ) ) >. ) ) $.
  $}

  ${
    $d c B $.  $d c u z C $.  $d c H $.  $d c .x. $.
    oppcval.b $e |- B = ( Base ` C ) $.
    oppcval.h $e |- H = ( Hom ` C ) $.
    oppcval.x $e |- .x. = ( comp ` C ) $.
    oppcval.o $e |- O = ( oppCat ` C ) $.
    $( Value of the opposite category.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    oppcval $p |- ( C e. V -> O = ( ( C sSet <. ( Hom ` ndx ) , tpos H >. )
      sSet <. ( comp ` ndx ) , ( u e. ( B X. B ) , z e. B |->
        tpos ( <. z , ( 2nd ` u ) >. .x. ( 1st ` u ) ) ) >. ) ) $=
      ( vc cfv chom ctpos cop csts co cco wcel coppc cnx cxp c2nd c1st cmpo cvv
      cv wceq elex cbs id fveq2 eqtr4di tposeqd opeq2d oveq12d oveqd mpoeq123dv
      sqxpeqd df-oppc ovex fvmpt syl eqtrid ) DHUAZGDUBNZDUCONZFPZQZRSZUCTNZBAC
      CUDZCAUIBUIZUENQZVOUFNZESZPZUGZQZRSZLVGDUHUAVHWBUJDHUKMDMUIZVIWCONZPZQZRS
      ZVMBAWCULNZWHUDZWHVPVQWCTNZSZPZUGZQZRSWBUHUBWCDUJZWGVLWNWARWOWCDWFVKRWOUM
      WOWEVJVIWOWDFWOWDDONFWCDOUNJUOUPUQURWOWMVTVMWOBAWIWHWLVNCVSWOWHCWOWHDULNC
      WCDULUNIUOZVAWPWOWKVRWOWJEVPVQWOWJDTNEWCDTUNKUOUSUPUTUQURABMVBVLWARVCVDVE
      VF $.
  $}

  ${
    $d u z C $.
    oppchom.h $e |- H = ( Hom ` C ) $.
    oppchom.o $e |- O = ( oppCat ` C ) $.
    $( Hom-sets of the opposite category.  (Contributed by Mario Carneiro,
       2-Jan-2017.)  (Proof shortened by AV, 14-Oct-2024.) $)
    oppchomfval $p |- tpos H = ( Hom ` O ) $=
      ( vu vz cvv wcel ctpos chom cfv wceq cnx cop csts co homid wne c0 cco cbs
      cxp cv c2nd c1st cmpo slotsbhcdif simp3i setsnid fvexi tposex setsid eqid
      mpan2 oppcval fveq2d 3eqtr4a wn tpos0 fvprc tposeqd coppc eqtr4di pm2.61i
      eqtrid str0 ) AHIZBJZCKLZMVHANKLZVIOPQZKLZVLNUALZFGAUBLZVOUCVOGUDFUDZUELO
      VPUFLAUALZQJUGZOPQZKLVIVJVRVNKVLRNUBLZVKSVTVNSVKVNSUHUIUJVHVIHIVIVMMBBAKD
      UKULHVIKHARUMUOVHCVSKGFVOAVQBCHVOUNDVQUNEUPUQURVHUSZTJTVIVJUTWABTWABAKLTD
      AKVAVFVBWAVJTKLTWACTKWACAVCLTEAVCVAVFUQKVKRVGVDURVE $.

    $( Hom-sets of the opposite category.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    oppchom $p |- ( X ( Hom ` O ) Y ) = ( Y H X ) $=
      ( ctpos co chom cfv oppchomfval oveqi ovtpos eqtr3i ) DEBHZIDECJKZIEDBIPQ
      DEABCFGLMDEBNO $.
  $}

  ${
    $d u z B $.  $d u z C $.  $d u z ph $.  $d u z .x. $.  $d u z X $.
    $d u z Y $.  $d u z Z $.
    oppcco.b $e |- B = ( Base ` C ) $.
    oppcco.c $e |- .x. = ( comp ` C ) $.
    oppcco.o $e |- O = ( oppCat ` C ) $.
    oppcco.x $e |- ( ph -> X e. B ) $.
    oppcco.y $e |- ( ph -> Y e. B ) $.
    oppcco.z $e |- ( ph -> Z e. B ) $.
    $( Composition in the opposite category.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    oppccofval $p |- ( ph ->
      ( <. X , Y >. ( comp ` O ) Z ) = tpos ( <. Z , Y >. .x. X ) ) $=
      ( vu vz cfv cvv wcel wceq cop cxp cv c2nd c1st co ctpos cco cnx chom csts
      cmpo elfvex eleq2s eqid oppcval 3syl fveq2d ovex fvexi mpoex ccoid setsid
      cbs xpex mp2an eqtr4di simprr simprl adantr op2ndg syl2an2r eqtrd opeq12d
      wa op1stg oveq12d tposeqd opelxpd tposex a1i ovmpod ) AOPFGUAZHBBUBZBPUCZ
      OUCZUDQZUAZWFUEQZDUFZUGZHGUAZFDUFZUGZEUHQZRAWOCUIUJQCUJQZUGUAZUKUFZUIUHQO
      PWDBWKULZUAUKUFZUHQZWSAEWTUHAFBSZCRSZEWTTLXCFCVDQBFCVDUMIUNPOBCDWPERIWPUO
      JKUPUQURWRRSWSRSWSXATCWQUKUSOPWDBWKBBBCVDIUTZXDVEXDVARWSUHRWRVBVCVFVGAWFW
      CTZWEHTZVOZVOZWJWMXHWHWLWIFDXHWEHWGGAXEXFVHXHWGWCUDQZGXHWFWCUDAXEXFVIZURA
      XBXGGBSZXIGTLAXKXGMVJZFGBBVKVLVMVNXHWIWCUEQZFXHWFWCUEXJURAXBXGXKXMFTLXLFG
      BBVPVLVMVQVRAFGBBLMVSNWNRSAWMWLFDUSVTWAWB $.

    $( Composition in the opposite category.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    oppcco $p |- ( ph ->
    ( G ( <. X , Y >. ( comp ` O ) Z ) F ) = ( F ( <. Z , Y >. .x. X ) G ) ) $=
      ( cop cco cfv co ctpos oppccofval oveqd ovtpos eqtrdi ) AFEHIQJGRSTZTFEJI
      QHDTZUAZTEFUGTAUFUHFEABCDGHIJKLMNOPUBUCFEUGUDUE $.
  $}

  ${
    $d f g h u w x y z C $.  $d f g h w x y z O $.
    oppcbas.1 $e |- O = ( oppCat ` C ) $.
    ${
      oppcbas.2 $e |- B = ( Base ` C ) $.
      $( Base set of an opposite category.  (Contributed by Mario Carneiro,
         2-Jan-2017.)  (Proof shortened by AV, 18-Oct-2024.) $)
      oppcbas $p |- B = ( Base ` O ) $=
        ( vu vz cbs cfv cvv cnx chom ctpos cop csts co cco cv wne eqid wcel cxp
        wceq c2nd baseid slotsbhcdif simp1i setsnid simp2i eqtri oppcval fveq2d
        c1st cmpo eqtr4id coppc c0 base0 eqcomi fveqprc pm2.61i ) ABHIZCHIZEBJU
        AZVBVCUCVDVBBKLIZBLIZMZNOPZKQIZFGVBVBUBVBGRFRZUDINVJUMIBQIZPMUNZNOPZHIZ
        VCVBVHHIVNVGVEHBUEKHIZVESZVOVISZVEVISZUFUGUHVLVIHVHUEVPVQVRUFUIUHUJVDCV
        MHGFVBBVKVFCJVBTVFTVKTDUKULUOHUPBCUQUQHIURUSDUTVAUJ $.
    $}

    $( Lemma for ~ oppccat .  (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    oppccatid $p |- ( C e. Cat -> ( O e. Cat /\ ( Id ` O ) = ( Id ` C ) ) ) $=
      ( vy vx vz vw vf vg wcel cfv wceq wa cv eqid oppchom cop oppcco eleqtrdi
      co ccat ccid cbs cmpt chom w3a cco cvv oppcbas a1i eqidd coppc fvexi biid
      vh simpl catidcl eleqtrrdi simpr1l simpr1r simpr31 catrid simpr2l simpr32
      simpr eqtrd catlid catcocl eqeltrd simpr2r simpr33 catass 3eqtr4rd oveq1d
      oveq2d 3eqtr4d iscatd2 wfn cidfn dffn5 sylib eqeq2d anbi2d mpbird ) AUAJZ
      BUAJZBUBKZAUBKZLZMWFWGDAUCKZDNZWHKZUDZLZMWEENZWJJZWKWJJZMZFNZWJJZGNZWJJZM
      ZHNZWOWKBUEKZTZJZINZWKWSXETZJZUONZWSXAXETZJZUFZUFZEDFGWJBBUGKZWLHIUOXEUHW
      JBUCKLWEWJABCWJOZUIUJWEXEUKWEXPUKBUHJWEBAULCUMUJXOUNWEWQMZWLWKWKAUEKZTWKW
      KXETXRWJAWHXSWKXQXSOZWHOZWEWQUPWEWQVEUQAXSBWKWKXTCPURWEXOMZWLXDWOWKQZWKXP
      TTXDWLWKWKQZWOAUGKZTTXDYBWJAYEXDWLBWOWKWKXQYEOZCWPWQXCXNWEUSZWPWQXCXNWEUT
      ZYHRYBWJAYEWHXDXSWKWOXQXTYAWEXOUPZYHYFYGYBXDXFWKWOXSTXGXJXMWRXCWEVAAXSBWO
      WKXTCPSZVBVFYBXHWLYDWSXPTTWLXHWSWKQZWKYETTXHYBWJAYEWLXHBWKWKWSXQYFCYHYHWT
      XBWRXNWEVCZRYBWJAYEWHXHXSWSWKXQXTYAYIYLYFYHYBXHXIWSWKXSTXGXJXMWRXCWEVDAXS
      BWKWSXTCPSZVGVFYBXHXDYCWSXPTTZWSWOXSTZWOWSXETYBYNXDXHYKWOYETTZYOYBWJAYEXD
      XHBWOWKWSXQYFCYGYHYLRZYBWJAYEXHXDXSWSWKWOXQXTYFYIYLYHYGYMYJVHVIAXSBWOWSXT
      CPURYBXHXKXAWSQZWKYETTZXDYCXAXPTZTZXKYPWOWSQXAXPTZTZXKXHWKWSQXAXPTTZXDYTT
      XKYNUUBTYBYPXKYRWOYETTXDYSXAWKQWOYETTUUCUUAYBWJAYEXKXHXSXDWOXAWSWKXQXTYFY
      IWTXBWRXNWEVJZYLYHYBXKXLXAWSXSTXGXJXMWRXCWEVKAXSBWSXAXTCPSYMYGYJVLYBWJAYE
      YPXKBWOWSXAXQYFCYGYLUUERYBWJAYEXDYSBWOWKXAXQYFCYGYHUUERVMYBUUDYSXDYTYBWJA
      YEXHXKBWKWSXAXQYFCYHYLUUERVNYBYNYPXKUUBYQVOVPVQWEWIWNWFWEWHWMWGWEWHWJVRWH
      WMLWJAWHXQYAVSDWJWHVTWAWBWCWD $.

    ${
      oppchomf.h $e |- H = ( Homf ` C ) $.
      $( Hom-sets of the opposite category.  (Contributed by Mario Carneiro,
         17-Jan-2017.) $)
      oppchomf $p |- tpos H = ( Homf ` O ) $=
        ( vy vx cbs cfv cv chom co cmpo chomf ctpos wceq wcel wa eqid homffval
        oppchom a1i mpoeq3ia oppcbas tposmpo 3eqtr4ri ) FGAHIZUGFJZGJZCKIZLZMFG
        UGUGUIUHAKIZLZMCNIZBOFGUGUGUKUMUKUMPUHUGQUIUGQRAULCUHUIULSZDUAUBUCFGUGC
        UNUJUNSUGACDUGSZUDUJSTGFUGUGUMBGFUGABULEUPUOTUEUF $.
    $}

    ${
      oppcid.2 $e |- B = ( Id ` C ) $.
      $( Identity function of an opposite category.  (Contributed by Mario
         Carneiro, 2-Jan-2017.) $)
      oppcid $p |- ( C e. Cat -> ( Id ` O ) = B ) $=
        ( ccat wcel ccid cfv wceq oppccatid simprd eqtr4di ) BFGZCHIZBHIZANCFGO
        PJBCDKLEM $.
    $}

    $( An opposite category is a category.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    oppccat $p |- ( C e. Cat -> O e. Cat ) $=
      ( ccat wcel ccid cfv wceq oppccatid simpld ) ADEBDEBFGAFGHABCIJ $.

    ${
      2oppcco.2 $e |- B = ( Base ` C ) $.
      $( The double opposite category has the same objects as the original
         category.  Intended for use with property lemmas such as ~ monpropd .
         (Contributed by Mario Carneiro, 3-Jan-2017.) $)
      2oppcbas $p |- B = ( Base ` ( oppCat ` O ) ) $=
        ( coppc cfv eqid oppcbas ) ACCFGZJHABCDEII $.
    $}

    $( The double opposite category has the same morphisms as the original
       category.  Intended for use with property lemmas such as ~ monpropd .
       (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    2oppchomf $p |- ( Homf ` C ) = ( Homf ` ( oppCat ` O ) ) $=
      ( chomf cfv ctpos coppc wrel cdm wceq cbs cxp wfn eqid homffn fnrel ax-mp
      relxp fndmi oppchomf releqi mpbir tpostpos2 mp2an eqtr3i ) ADEZFZFZUFBGEZ
      DEUFHZUFIZHZUHUFJUFAKEZUMLZMUJUMAUFUFNZUMNOZUNUFPQULUNHUMUMRUKUNUNUFUPSUA
      UBUFUCUDBUGUIUINAUFBCUOTTUE $.

    $( The double opposite category has the same composition as the original
       category.  Intended for use with property lemmas such as ~ monpropd .
       (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    2oppccomf $p |- ( comf ` C ) = ( comf ` ( oppCat ` O ) ) $=
      ( vg vf vx vy vz ccomf cfv wceq wtru cv cop cco co wral cbs wcel eqid w3a
      coppc wa oppcbas simpr1 simpr2 simpr3 oppcco eqtr2d ralrimivw ralrimivvva
      chom eqidd 2oppcbas a1i chomf 2oppchomf comfeq mpbird mptru ) AIJBUBJZIJK
      ZLVBDMZEMZFMZGMZNZHMZAOJZPPZVCVDVGVHVAOJZPPZKZDVFVHAULJZPZQZEVEVFVNPZQZHA
      RJZQGVSQFVSQLVRFGHVSVSVSLVEVSSZVFVSSZVHVSSZUAUCZVPEVQWCVMDVOWCVLVDVCVHVFN
      VEBOJZPPVJWCVSBWDVDVCVAVEVFVHVSABCVSTZUDWDTVATLVTWAWBUEZLVTWAWBUFZLVTWAWB
      UGZUHWCVSAVIVCVDBVHVFVEWEVITZCWHWGWFUHUIUJUJUKLFGHVSAVAVKVIEDVNWIVKTVNTLV
      SUMVSVARJKLVSABCWEUNUOAUPJVAUPJKLABCUQUOURUSUT $.
  $}

  ${
    $d f g x y z C $.  $d f g x y z D $.  $d f g x y z ph $.
    oppchomfpropd.1 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    $( If two categories have the same hom-sets, so do their opposites.
       (Contributed by Mario Carneiro, 26-Jan-2017.) $)
    oppchomfpropd $p |- ( ph ->
      ( Homf ` ( oppCat ` C ) ) = ( Homf ` ( oppCat ` D ) ) ) $=
      ( chomf cfv ctpos coppc tposeqd eqid oppchomf 3eqtr3g ) ABEFZGCEFZGBHFZEF
      CHFZEFAMNDIBMOOJMJKCNPPJNJKL $.

    oppccomfpropd.1 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    $( If two categories have the same hom-sets and composition, so do their
       opposites.  (Contributed by Mario Carneiro, 26-Jan-2017.) $)
    oppccomfpropd $p |- ( ph ->
      ( comf ` ( oppCat ` C ) ) = ( comf ` ( oppCat ` D ) ) ) $=
      ( vg vf vx vy vz cfv ccomf wceq cv cco co wral cbs wcel eqid cop chom w3a
      coppc wa chomf ad2antrr simplr3 simplr2 simplr1 simprr eleqtrdi comfeqval
      oppchom simprl oppcco homfeqbas eleqtrd 3eqtr4d ralrimivva oppcbas eqtrdi
      ralrimivvva a1i oppchomfpropd comfeq mpbird ) ABUDKZLKCUDKZLKMFNZGNZHNZIN
      ZUAZJNZVHOKZPPZVJVKVNVOVIOKZPPZMZFVMVOVHUBKZPZQGVLVMWAPZQZJBRKZQIWEQHWEQA
      WDHIJWEWEWEAVLWESZVMWESZVOWESZUCZUEZVTGFWCWBWJVKWCSZVJWBSZUEZUEZVKVJVOVMU
      AZVLBOKZPPVKVJWOVLCOKZPPVQVSWNWEBCWQWPVJVKBUBKZVOVMVLWETZWRTZWPTZWQTZABUF
      KCUFKMWIWMDUGABLKCLKMWIWMEUGWFWGWHAWMUHZWFWGWHAWMUIZWFWGWHAWMUJZWNVJWBVOV
      MWRPWJWKWLUKBWRVHVMVOWTVHTZUNULWNVKWCVMVLWRPWJWKWLUOBWRVHVLVMWTXFUNULUMWN
      WEBWPVKVJVHVLVMVOWSXAXFXEXDXCUPWNCRKZCWQVKVJVIVLVMVOXGTZXBVITZWNVLWEXGXEA
      WEXGMWIWMABCDUQZUGZURWNVMWEXGXDXKURWNVOWEXGXCXKURUPUSUTVCAHIJWEVHVIVRVPGF
      WAVPTVRTWATWEVHRKMAWEBVHXFWSVAVDAWEXGVIRKXJXGCVIXIXHVAVBABCDVEVFVG $.
  $}

  ${
    $d f u z $.
    $( ` oppCat ` restricted to ` Cat ` is a function from ` Cat ` to ` Cat ` .
       (Contributed by Zhi Wang, 29-Aug-2024.) $)
    oppccatf $p |- ( oppCat |` Cat ) : Cat --> Cat $=
      ( vc vf vu vz ccat coppc cres wf cdm wcel cfv cvv cnx chom ctpos cop csts
      cv co cco wa wfun wral wb cbs cxp c2nd c1st df-oppc funmpt2 ffvresb ax-mp
      cmpo elex ovex dmmpti eleqtrrdi eqid oppccat jca mprgbir ) EEFEGHZARZFIZJ
      ZVCFKZEJZUAZAEFUBVBVHAEUCUDBLBRZMNKVINKOPQSZMTKCDVIUEKZVKUFVKDRCRZUGKPVLU
      HKVITKSOUMPZQSZFDCBUIZUJAEEFUKULVCEJZVEVGVPVCLVDVCEUNBLVNFVJVMQUOVOUPUQVC
      VFVFURUSUTVA $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Monomorphisms and epimorphisms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Mono $. $( The class of all monomorphisms. $)
  $c Epi $. $( The class of all epimorphisms. $)

  $( Extend class notation with the class of all monomorphisms. $)
  cmon $a class Mono $.

  $( Extend class notation with the class of all epimorphisms. $)
  cepi $a class Epi $.

  ${
    $d b c f g h x y z $.
    $( Function returning the monomorphisms of the category ` c ` .  JFM CAT_1
       def. 10.  (Contributed by FL, 5-Dec-2007.)  (Revised by Mario Carneiro,
       2-Jan-2017.) $)
    df-mon $a |- Mono = ( c e. Cat |->
      [_ ( Base ` c ) / b ]_ [_ ( Hom ` c ) / h ]_
      ( x e. b , y e. b |-> { f e. ( x h y ) | A. z e. b Fun `'
        ( g e. ( z h x ) |-> ( f ( <. z , x >. ( comp ` c ) y ) g ) ) } ) ) $.

    $( Function returning the epimorphisms of the category ` c ` .  JFM CAT_1
       def. 11.  (Contributed by FL, 8-Aug-2008.)  (Revised by Mario Carneiro,
       2-Jan-2017.) $)
    df-epi $a |- Epi = ( c e. Cat |-> tpos ( Mono ` ( oppCat ` c ) ) ) $.
  $}

  ${
    $d b c f g h x y z B $.  $d g h z G $.  $d g h z K $.  $d f g h x y z ph $.
    $d b c f g h x y z C $.  $d b c f g h x y z H $.  $d b c f g h x y z .x. $.
    $d f g h z F $.  $d f g h x y z X $.  $d f g h x y z Y $.  $d g h z Z $.
    $d f M $.
    ismon.b $e |- B = ( Base ` C ) $.
    ismon.h $e |- H = ( Hom ` C ) $.
    ismon.o $e |- .x. = ( comp ` C ) $.
    ismon.s $e |- M = ( Mono ` C ) $.
    ismon.c $e |- ( ph -> C e. Cat ) $.
    $( Definition of a monomorphism in a category.  (Contributed by Mario
       Carneiro, 3-Jan-2017.) $)
    monfval $p |- ( ph -> M = ( x e. B , y e. B |-> { f e. ( x H y ) |
 A. z e. B Fun `' ( g e. ( z H x ) |-> ( f ( <. z , x >. .x. y ) g ) ) } ) ) $=
      ( cfv cv co cbs vc vb vh cmon cop cmpt ccnv wfun wral crab cmpo ccat wcel
      wceq chom cco csb cvv fvexd fveq2 eqtr4di simpl fveq2d simplr simpr oveqd
      simpll mpteq12dv cnveqd funeqd raleqbidv rabeqbidv mpoeq123dv fvexi mpoex
      wa csbied2 df-mon fvmpt syl eqtrid ) AKFUDQZBCEEIDRZBRZJSZHRZIRZWCWDUEZCR
      ZGSZSZUFZUGZUHZDEUIZHWDWIJSZUJZUKZOAFULUMWBWRUNPUAFUBUARZTQZUCWSUOQZBCUBR
      ZXBIWCWDUCRZSZWFWGWHWIWSUPQZSZSZUFZUGZUHZDXBUIZHWDWIXCSZUJZUKZUQZUQWRULUD
      WSFUNZUBWTEXOWRURXPWSTUSXPWTFTQEWSFTUTLVAXPXBEUNZVPZUCXAJXNWRURXRWSUOUSXR
      XAFUOQJXRWSFUOXPXQVBVCMVAXRXCJUNZVPZBCXBXBXMEEWQXPXQXSVDZYAXTXKWOHXLWPXTX
      CJWDWIXRXSVEZVFXTXJWNDXBEYAXTXIWMXTXHWLXTIXDXGWEWKXTXCJWCWDYBVFXTXFWJWFWG
      XTXEGWHWIXTXEFUPQGXTWSFUPXPXQXSVGVCNVAVFVFVHVIVJVKVLVMVQVQBCDHIUCUBUAVRBC
      EEWQEFTLVNZYCVOVSVTWA $.

    ismon.x $e |- ( ph -> X e. B ) $.
    ismon.y $e |- ( ph -> Y e. B ) $.
    $( Definition of a monomorphism in a category.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    ismon $p |- ( ph -> ( F e. ( X M Y ) <-> ( F e. ( X H Y ) /\ A. z e. B
      Fun `' ( g e. ( z H X ) |-> ( F ( <. z , X >. .x. Y ) g ) ) ) ) ) $=
      ( vf co vx vy wcel cv cop cmpt ccnv wfun wral crab wa monfval wceq simprl
      cvv simprr oveq12d oveq2d opeq2d oveqd mpteq12dv cnveqd ralbidv rabeqbidv
      funeqd ovex rabex a1i ovmpod eleq2d oveq1 mpteq2dv elrab bitrdi ) AGJKITZ
      UCGFBUDZJHTZSUDZFUDZVPJUEZKETZTZUFZUGZUHZBCUIZSJKHTZUJZUCGWGUCFVQGVSWATZU
      FZUGZUHZBCUIZUKAVOWHGAUAUBJKCCFVPUAUDZHTZVRVSVPWNUEZUBUDZETZTZUFZUGZUHZBC
      UIZSWNWQHTZUJWHIUOAUAUBBCDESFHILMNOPULAWNJUMZWQKUMZUKUKZXCWFSXDWGXGWNJWQK
      HAXEXFUNZAXEXFUPZUQXGXBWEBCXGXAWDXGWTWCXGFWOWSVQWBXGWNJVPHXHURXGWRWAVRVSX
      GWPVTWQKEXGWNJVPXHUSXIUQUTVAVBVEVCVDQRWHUOUCAWFSWGJKHVFVGVHVIVJWFWMSGWGVR
      GUMZWEWLBCXJWDWKXJWCWJXJFVQWBWIVRGVSWAVKVLVBVEVCVMVN $.

    $( Write out the monomorphism property directly.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    ismon2 $p |- ( ph -> ( F e. ( X M Y ) <-> ( F e. ( X H Y ) /\ A. z e. B
      A. g e. ( z H X ) A. h e. ( z H X )
        ( ( F ( <. z , X >. .x. Y ) g ) =
          ( F ( <. z , X >. .x. Y ) h ) -> g = h ) ) ) ) $=
      ( wcel co cv cmpt ccnv wfun wral wa wceq wi ismon wb ccat ad2antrr simprl
      cop simprr simplr catcocl anassrs ralrimiva wf eqid fmpt df-f1 baib sylbi
      wf1 oveq2 f1mpt bitr3d syl ralbidva pm5.32da bitrd ) AHKLJUATHKLIUATZFBUB
      ZKIUAZHFUBZVPKUOLEUAZUAZUCZUDUEZBCUFZUGVOVTHGUBZVSUAZUHVRWDUHUIGVQUFFVQUF
      ZBCUFZUGABCDEFHIJKLMNOPQRSUJAVOWCWGAVOUGZWBWFBCWHVPCTZUGZVTVPLIUAZTZFVQUF
      ZWBWFUKWJWLFVQWHWIVRVQTZWLWHWIWNUGZUGCDEVRHIVPKLMNOADULTVOWOQUMWHWIWNUNAK
      CTVOWORUMALCTVOWOSUMWHWIWNUPAVOWOUQURUSUTWMVQWKWAVGZWBWFWMVQWKWAVAZWPWBUK
      FVQWKVTWAWAVBZVCWPWQWBVQWKWAVDVEVFWPWMWFFGVQWKVTWEWAWRVRWDHVSVHVIVEVJVKVL
      VMVN $.

    $( A monomorphism is a morphism.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    monhom $p |- ( ph -> ( X M Y ) C_ ( X H Y ) ) $=
      ( vf vg vz co cv wcel cop cmpt ccnv wfun wral ismon simpl biimtrdi ssrdv
      wa ) APGHFSZGHESZAPTZULUAUNUMUAZQRTZGESUNQTUPGUBHDSSUCUDUERBUFZUKUOARBCDQ
      UNEFGHIJKLMNOUGUOUQUHUIUJ $.

    moni.z $e |- ( ph -> Z e. B ) $.
    moni.f $e |- ( ph -> F e. ( X M Y ) ) $.
    moni.g $e |- ( ph -> G e. ( Z H X ) ) $.
    moni.k $e |- ( ph -> K e. ( Z H X ) ) $.
    $( Property of a monomorphism.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    moni $p |- ( ph -> ( ( F ( <. Z , X >. .x. Y ) G ) =
                         ( F ( <. Z , X >. .x. Y ) K ) <-> G = K ) ) $=
      ( vg vz vh cop co wceq cv wi wral ismon2 mpbid simprd adantr simpr oveq1d
      wcel eleqtrrd simpllr opeq1d eqidd simplr oveq123d eqeq12d imbi12d rspcdv
      wa rspcimdv mpd oveq2 impbid1 ) AEFLJUGZKDUHZUHZEHVOUHZUIZFHUIZAEUDUJZUEU
      JZJUGZKDUHZUHZEUFUJZWCUHZUIZVTWEUIZUKZUFWAJGUHZULZUDWJULZUEBULZVRVSUKZAEJ
      KGUHUSZWMAEJKIUHUSWOWMVIUAAUEBCDUDUFEGIJKMNOPQRSUMUNUOAWLWNUELBTAWALUIZVI
      ZWKWNUDFWJWQFLJGUHZWJAFWRUSWPUBUPWQWALJGAWPUQURZUTWQVTFUIZVIZWIWNUFHWJWQH
      WJUSWTWQHWRWJAHWRUSWPUCUPWSUTUPXAWEHUIZVIZWGVRWHVSXCWDVPWFVQXCEEVTFWCVOXC
      WBVNKDXCWALJAWPWTXBVAVBURZXCEVCZWQWTXBVDZVEXCEEWEHWCVOXDXEXAXBUQZVEVFXCVT
      FWEHXFXGVFVGVHVJVJVKFHEVOVLVM $.
  $}

  ${
    $d a b c f g C $.  $d a b c f g D $.  $d a b c f g ph $.
    monpropd.3 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    monpropd.4 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    monpropd.c $e |- ( ph -> C e. Cat ) $.
    monpropd.d $e |- ( ph -> D e. Cat ) $.
    $( If two categories have the same set of objects, morphisms, and
       compositions, then they have the same monomorphisms.  (Contributed by
       Mario Carneiro, 3-Jan-2017.) $)
    monpropd $p |- ( ph -> ( Mono ` C ) = ( Mono ` D ) ) $=
      ( va vb vg vc vf cfv cv co wral wcel wceq wa eqid cbs chom cmpt ccnv wfun
      cop cco crab cmpo cmon chomf simpr simp-4r homfeqval ad5antr ccomf simplr
      ad2antrr simp-5r simpllr comfeqval mpteq12dva ralbidva rabbidva homfeqbas
      cnveqd funeqd raleqdv rabeqbidv mpoeq3dva mpoeq12 syl2anc monfval 3eqtr4d
      eqtrd 3impa ) AHIBUAMZVQJKNZHNZBUBMZOZLNZJNZVRVSUFZINZBUGMZOOZUCZUDZUEZKV
      QPZLVSWEVTOZUHZUIZHICUAMZWOJVRVSCUBMZOZWBWCWDWECUGMZOOZUCZUDZUEZKWOPZLVSW
      EWPOZUHZUIZBUJMZCUJMZAWNHIVQVQXEUIZXFAHIVQVQWMXEAVSVQQZWEVQQZWMXERAXJSZXK
      SZWMXBKVQPZLWLUHXEXMWKXNLWLXMWBWLQZSZWJXBKVQXPVRVQQZSZWIXAXRWHWTXRJWAWGWQ
      WSXRVQBCVTWPVRVSVQTZVTTZWPTZXMBUKMCUKMRZXOXQAYBXJXKDURZURXPXQULAXJXKXOXQU
      MUNXRWCWAQZSVQBCWRWFWCWBVTVRVSWEXSXTWFTZWRTZAYBXJXKXOXQYDDUOABUPMCUPMRXJX
      KXOXQYDEUOXPXQYDUQAXJXKXOXQYDUSXLXKXOXQYDUMXRYDULXMXOXQYDUTVAVBVFVGVCVDXM
      XNXCLWLXDXMVQBCVTWPVSWEXSXTYAYCAXJXKUQXLXKULUNXMXBKVQWOAVQWORZXJXKABCDVEZ
      URVHVIVOVPVJAYGYGXIXFRYHYHHIVQVQWOWOXEVKVLVOAHIKVQBWFLJVTXGXSXTYEXGTFVMAH
      IKWOCWRLJWPXHWOTYAYFXHTGVMVN $.
  $}

  ${
    $d c C $.  $d c M $.
    oppcmon.o $e |- O = ( oppCat ` C ) $.
    oppcmon.c $e |- ( ph -> C e. Cat ) $.
    ${
      oppcmon.m $e |- M = ( Mono ` O ) $.
      oppcmon.e $e |- E = ( Epi ` C ) $.
      $( A monomorphism in the opposite category is an epimorphism.
         (Contributed by Mario Carneiro, 3-Jan-2017.) $)
      oppcmon $p |- ( ph -> ( X M Y ) = ( Y E X ) ) $=
        ( vc co ctpos cepi cfv ccat wceq coppc cmon wcel eqtr4di fveq2d tposeqd
        cv fveq2 df-epi fvexi tposex fvmpt syl eqtrid oveqd ovtpos eqtr2di ) AG
        FCMGFDNZMFGDMACUPGFACBOPZUPKABQUAUQUPRILBLUEZSPZTPZNUPQOURBRZUTDVAUTETP
        DVAUSETVAUSBSPEURBSUFHUBUCJUBUDLUGDDETJUHUIUJUKULUMGFDUNUO $.
    $}

    ${
      oppcepi.e $e |- E = ( Epi ` O ) $.
      oppcepi.m $e |- M = ( Mono ` C ) $.
      $( An epimorphism in the opposite category is a monomorphism.
         (Contributed by Mario Carneiro, 3-Jan-2017.) $)
      oppcepi $p |- ( ph -> ( X E Y ) = ( Y M X ) ) $=
        ( co cfv cmon chomf wceq a1i ccomf ccat wcel 2oppchomf oppccat syl eqid
        coppc 2oppccomf monpropd eqtrid oveqd oppcmon eqtr2d ) AGFDLGFEUEMZNMZL
        FGCLADUMGFADBNMUMKABULBOMULOMPABEHUAQBRMULRMPABEHUFQIAESTZULSTABSTUNIBE
        HUBUCZEULULUDZUBUCUGUHUIAECUMULGFUPUOUMUDJUJUK $.
    $}
  $}

  ${
    $d g z B $.  $d g z C $.  $d f g h z H $.  $d g h z .x. $.  $d f g h z X $.
    $d f E $.  $d g h z F $.  $d f g z ph $.  $d f g h z Y $.
    isepi.b $e |- B = ( Base ` C ) $.
    isepi.h $e |- H = ( Hom ` C ) $.
    isepi.o $e |- .x. = ( comp ` C ) $.
    isepi.e $e |- E = ( Epi ` C ) $.
    isepi.c $e |- ( ph -> C e. Cat ) $.
    isepi.x $e |- ( ph -> X e. B ) $.
    isepi.y $e |- ( ph -> Y e. B ) $.
    $( Definition of an epimorphism in a category.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    isepi $p |- ( ph -> ( F e. ( X E Y ) <-> ( F e. ( X H Y ) /\ A. z e. B
      Fun `' ( g e. ( Y H z ) |-> ( g ( <. X , Y >. .x. z ) F ) ) ) ) ) $=
      ( co wcel coppc cfv cmon chom cv cop cco cmpt ccnv wfun wral eqid oppcbas
      wa ccat oppccat syl ismon oppcmon eleq2d wceq oppchom simpr adantr oppcco
      a1i mpteq12dv cnveqd funeqd ralbidva anbi12d 3bitr3d ) AHKJDUAUBZUCUBZSZT
      HKJVMUDUBZSZTZFBUEZKVPSZHFUEZVSKUFJVMUGUBZSSZUHZUIZUJZBCUKZUNHJKGSZTHJKIS
      ZTZFKVSISZWAHJKUFVSESSZUHZUIZUJZBCUKZUNABCVMWBFHVPVNKJCDVMVMULZLUMVPULWBU
      LVNULZADUOTVMUOTPDVMWQUPUQRQURAVOWHHADGVNVMKJWQPWROUSUTAVRWJWGWPAVQWIHVQW
      IVAADIVMKJMWQVBVFUTAWFWOBCAVSCTZUNZWEWNWTWDWMWTFVTWCWKWLVTWKVAWTDIVMVSKMW
      QVBVFWTCDEWAHVMVSKJLNWQAWSVCAKCTWSRVDAJCTWSQVDVEVGVHVIVJVKVL $.

    $( Write out the epimorphism property directly.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    isepi2 $p |- ( ph -> ( F e. ( X E Y ) <-> ( F e. ( X H Y ) /\ A. z e. B
      A. g e. ( Y H z ) A. h e. ( Y H z )
        ( ( g ( <. X , Y >. .x. z ) F ) =
          ( h ( <. X , Y >. .x. z ) F ) -> g = h ) ) ) ) $=
      ( wcel co cv cmpt ccnv wfun wral wa wceq wi isepi wb ccat ad2antrr simprl
      cop simplr simprr catcocl anassrs ralrimiva wf eqid fmpt df-f1 baib sylbi
      wf1 oveq1 f1mpt bitr3d syl ralbidva pm5.32da bitrd ) AIKLHUATIKLJUATZFLBU
      BZJUAZFUBZIKLUOVPEUAZUAZUCZUDUEZBCUFZUGVOVTGUBZIVSUAZUHVRWDUHUIGVQUFFVQUF
      ZBCUFZUGABCDEFHIJKLMNOPQRSUJAVOWCWGAVOUGZWBWFBCWHVPCTZUGZVTKVPJUAZTZFVQUF
      ZWBWFUKWJWLFVQWHWIVRVQTZWLWHWIWNUGZUGCDEIVRJKLVPMNOADULTVOWOQUMAKCTVOWORU
      MALCTVOWOSUMWHWIWNUNAVOWOUPWHWIWNUQURUSUTWMVQWKWAVGZWBWFWMVQWKWAVAZWPWBUK
      FVQWKVTWAWAVBZVCWPWQWBVQWKWAVDVEVFWPWMWFFGVQWKVTWEWAWRVRWDIVSVHVIVEVJVKVL
      VMVN $.

    $( An epimorphism is a morphism.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    epihom $p |- ( ph -> ( X E Y ) C_ ( X H Y ) ) $=
      ( vf vg vz co cv wcel cop cmpt ccnv wfun wral isepi simpl biimtrdi ssrdv
      wa ) APGHESZGHFSZAPTZULUAUNUMUAZQHRTZFSQTUNGHUBUPDSSUCUDUERBUFZUKUOARBCDQ
      EUNFGHIJKLMNOUGUOUQUHUIUJ $.

    epii.z $e |- ( ph -> Z e. B ) $.
    epii.f $e |- ( ph -> F e. ( X E Y ) ) $.
    epii.g $e |- ( ph -> G e. ( Y H Z ) ) $.
    epii.k $e |- ( ph -> K e. ( Y H Z ) ) $.
    $( Property of an epimorphism.  (Contributed by Mario Carneiro,
       3-Jan-2017.) $)
    epii $p |- ( ph -> ( ( G ( <. X , Y >. .x. Z ) F ) =
                         ( K ( <. X , Y >. .x. Z ) F ) <-> G = K ) ) $=
      ( cop coppc cfv cco co wceq eqid oppcco eqeq12d chom cmon oppcbas oppccat
      ccat wcel syl oppcmon eleqtrrd oppchom eleqtrrdi moni bitr3d ) AFGLKUDJCU
      EUFZUGUFZUHZUHZFIVHUHZUIGFJKUDLDUHZUHZIFVKUHZUIGIUIAVIVLVJVMABCDGFVFLKJMO
      VFUJZTSRUKABCDIFVFLKJMOVNTSRUKULABVFVGFGVFUMUFZIVFUNUFZKJLBCVFVNMUOVOUJVG
      UJVPUJZACUQURVFUQURQCVFVNUPUSSRTAFJKEUHKJVPUHUAACEVPVFKJVNQVQPUTVAAGKLHUH
      ZLKVOUHZUBCHVFLKNVNVBZVCAIVRVSUCVTVCVDVE $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Sections, inverses, isomorphisms
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Sect $. $( Sections of a morphism. $)
  $c Inv $. $( The inverse of a morphism. $)
  $c Iso $. $( The class of all isomorphisms. $)

  $( Extend class notation with the sections of a morphism. $)
  csect $a class Sect $.

  $( Extend class notation with the inverses of a morphism. $)
  cinv $a class Inv $.

  $( Extend class notation with the class of all isomorphisms. $)
  ciso $a class Iso $.

  ${
    $d c f g h x y $.
    $( Function returning the section relation in a category.  Given arrows
       ` f : X --> Y ` and ` g : Y --> X ` , we say ` f Sect g ` , that is,
       ` f ` is a section of ` g ` , if ` g o. f = 1 `` X ` .  If there there
       is an arrow ` g ` with ` f Sect g ` , the arrow ` f ` is called a
       _section_, see definition 7.19 of [Adamek] p. 106.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    df-sect $a |- Sect = ( c e. Cat |->
     ( x e. ( Base ` c ) , y e. ( Base ` c ) |-> { <. f , g >. |
       [. ( Hom ` c ) / h ]. ( ( f e. ( x h y ) /\ g e. ( y h x ) ) /\
         ( g ( <. x , y >. ( comp ` c ) x ) f ) = ( ( Id ` c ) ` x ) ) } ) ) $.

    $( The inverse relation in a category.  Given arrows ` f : X --> Y ` and
       ` g : Y --> X ` , we say ` g Inv f ` , that is, ` g ` is an inverse of
       ` f ` , if ` g ` is a section of ` f ` and ` f ` is a section of ` g ` .
       Definition 3.8 of [Adamek] p. 28.  (Contributed by FL, 22-Dec-2008.)
       (Revised by Mario Carneiro, 2-Jan-2017.) $)
    df-inv $a |- Inv = ( c e. Cat |-> ( x e. ( Base ` c ) , y e. ( Base ` c )
      |-> ( ( x ( Sect ` c ) y ) i^i `' ( y ( Sect ` c ) x ) ) ) ) $.

    $( Function returning the isomorphisms of the category ` c ` .  Definition
       3.8 of [Adamek] p. 28, and definition in [Lang] p. 54.  (Contributed by
       FL, 9-Jun-2014.)  (Revised by Mario Carneiro, 2-Jan-2017.) $)
    df-iso $a |- Iso = ( c e. Cat |->
      ( ( x e. _V |-> dom x ) o. ( Inv ` c ) ) ) $.
  $}

  ${
    $d c f g h x y .1. $.  $d c x y B $.  $d c f g h x y C $.  $d f g x y ph $.
    $d f g F $.  $d c f g h x y H $.  $d c f g h x y .x. $.  $d f g x y X $.
    $d f g G $.  $d f g x y Y $.
    issect.b $e |- B = ( Base ` C ) $.
    issect.h $e |- H = ( Hom ` C ) $.
    issect.o $e |- .x. = ( comp ` C ) $.
    issect.i $e |- .1. = ( Id ` C ) $.
    issect.s $e |- S = ( Sect ` C ) $.
    issect.c $e |- ( ph -> C e. Cat ) $.
    $( Value of the section operation.  (Contributed by Mario Carneiro,
       2-Jan-2017.)  Removed redundant hypotheses.  (Revised by Zhi Wang,
       27-Oct-2025.) $)
    sectffval $p |- ( ph -> S = ( x e. B , y e. B |-> { <. f , g >. |
      ( ( f e. ( x H y ) /\ g e. ( y H x ) ) /\
        ( g ( <. x , y >. .x. x ) f ) = ( .1. ` x ) ) } ) ) $=
      ( cfv cv co vc vh csect wcel wa cop wceq cmpo ccat cbs cco ccid chom wsbc
      copab fveq2 eqtr4di fvexd simpr oveqd eleq2d anbi12d simpl fveq2d eqeq12d
      cvv fveq1d sbcied2 opabbidv mpoeq123dv df-sect fvexi mpoex fvmpt eqtrid
      syl ) AFEUCRZBCDDISZBSZCSZKTZUDZJSZVTVSKTZUDZUEZWCVRVSVTUFZVSGTZTZVSHRZUG
      ZUEZIJUOZUHZPAEUIUDVQWNUGQUAEBCUASZUJRZWPVRVSVTUBSZTZUDZWCVTVSWQTZUDZUEZW
      CVRWGVSWOUKRZTZTZVSWOULRZRZUGZUEZUBWOUMRZUNZIJUOZUHWNUIUCWOEUGZBCWPWPXLDD
      WMXMWPEUJRDWOEUJUPLUQZXNXMXKWLIJXMXIWLUBXJKVFXMWOUMURXMXJEUMRKWOEUMUPMUQX
      MWQKUGZUEZXBWFXHWKXPWSWBXAWEXPWRWAVRXPWQKVSVTXMXOUSZUTVAXPWTWDWCXPWQKVTVS
      XQUTVAVBXPXEWIXGWJXPXDWHWCVRXPXCGWGVSXPXCEUKRGXPWOEUKXMXOVCZVDNUQUTUTXPVS
      XFHXPXFEULRHXPWOEULXRVDOUQVGVEVBVHVIVJBCIJUBUAVKBCDDWMDEUJLVLZXSVMVNVPVO
      $.

    issect.x $e |- ( ph -> X e. B ) $.
    issect.y $e |- ( ph -> Y e. B ) $.
    $( Value of the section relation.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    sectfval $p |- ( ph -> ( X S Y ) = { <. f , g >. |
        ( ( f e. ( X H Y ) /\ g e. ( Y H X ) ) /\
          ( g ( <. X , Y >. .x. X ) f ) = ( .1. ` X ) ) } ) $=
      ( co vx vy cv wcel cop cfv wceq copab cvv sectffval simprl simprr oveq12d
      wa eleq2d anbi12d opeq12d oveqd fveq2d eqeq12d opabbidv cxp ovex opabssxp
      xpex ssexi a1i ovmpod ) AUAUBJKBBGUCZUAUCZUBUCZITZUDZHUCZVKVJITZUDZUNZVNV
      IVJVKUEZVJETZTZVJFUFZUGZUNZGHUHVIJKITZUDZVNKJITZUDZUNZVNVIJKUEZJETZTZJFUF
      ZUGZUNZGHUHZDUIAUAUBBCDEFGHILMNOPQUJAVJJUGZVKKUGZUNUNZWCWNGHWRVQWHWBWMWRV
      MWEVPWGWRVLWDVIWRVJJVKKIAWPWQUKZAWPWQULZUMUOWRVOWFVNWRVKKVJJIWTWSUMUOUPWR
      VTWKWAWLWRVSWJVNVIWRVRWIVJJEWRVJJVKKWSWTUQWSUMURWRVJJFWSUSUTUPVARSWOUIUDA
      WOWDWFVBWDWFJKIVCKJIVCVEWMGHWDWFVDVFVGVH $.

    $( The section relation is a relation between morphisms from ` X ` to ` Y `
       and morphisms from ` Y ` to ` X ` .  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    sectss $p |- ( ph -> ( X S Y ) C_ ( ( X H Y ) X. ( Y H X ) ) ) $=
      ( vf vg co cv wcel wa cop cfv wceq copab cxp sectfval opabssxp eqsstrdi )
      AHIDTRUAZHIGTZUBSUAZIHGTZUBUCUNULHIUDHETTHFUEUFZUCRSUGUMUOUHABCDEFRSGHIJK
      LMNOPQUIUPRSUMUOUJUK $.

    $( The property " ` F ` is a section of ` G ` ".  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    issect $p |- ( ph -> ( F ( X S Y ) G <-> ( F e. ( X H Y ) /\
        G e. ( Y H X ) /\ ( G ( <. X , Y >. .x. X ) F ) = ( .1. ` X ) ) ) ) $=
      ( co vf vg wbr cv wcel wa cop cfv wceq copab sectfval breqd oveq12 ancoms
      w3a eqeq1d eqid brab2a df-3an bitr4i bitrdi ) AGHJKDTZUCGHUAUDZJKITZUEUBU
      DZKJITZUEUFVEVCJKUGJETZTZJFUHZUIZUFUAUBUJZUCZGVDUEZHVFUEZHGVGTZVIUIZUOZAV
      BVKGHABCDEFUAUBIJKLMNOPQRSUKULVLVMVNUFVPUFVQVJVPUAUBGHVDVFVKVCGUIZVEHUIZU
      FVHVOVIVSVRVHVOUIVEHVCGVGUMUNUPVKUQURVMVNVPUSUTVA $.

    issect.f $e |- ( ph -> F e. ( X H Y ) ) $.
    issect.g $e |- ( ph -> G e. ( Y H X ) ) $.
    $( Property of being a section.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    issect2 $p |- ( ph ->
      ( F ( X S Y ) G <-> ( G ( <. X , Y >. .x. X ) F ) = ( .1. ` X ) ) ) $=
      ( co wbr wcel wa cop cfv wceq jca w3a issect df-3an bitrdi mpbirand ) AGH
      JKDUBUCZGJKIUBUDZHKJIUBUDZUEZHGJKUFJEUBUBJFUGUHZAUPUQTUAUIAUOUPUQUSUJURUS
      UEABCDEFGHIJKLMNOPQRSUKUPUQUSULUMUN $.
  $}

  ${
    sectcan.b $e |- B = ( Base ` C ) $.
    sectcan.s $e |- S = ( Sect ` C ) $.
    sectcan.c $e |- ( ph -> C e. Cat ) $.
    sectcan.x $e |- ( ph -> X e. B ) $.
    sectcan.y $e |- ( ph -> Y e. B ) $.
    sectcan.1 $e |- ( ph -> G ( X S Y ) F ) $.
    sectcan.2 $e |- ( ph -> F ( Y S X ) H ) $.
    $( If ` G ` is a section of ` F ` and ` F ` is a section of ` H ` , then
       ` G = H ` .  Proposition 3.10 of [Adamek] p. 28.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    sectcan $p |- ( ph -> G = H ) $=
      ( cfv cop co eqid ccid cco chom wcel wceq wbr issect simp1d simp2d catass
      w3a mpbid simp3d oveq1d oveq2d 3eqtr3d catlid catrid ) AICUAQZQZFHIRZICUB
      QZSZSZGHUSQZHHRIVBSZSZFGAGEIHRIVBSSZFVCSGEFVAHVBSSZVFSVDVGABCVBFECUCQZGIH
      IHJVJTZVBTZLMNMAFHIVJSZUDZEIHVJSUDZVIVEUEZAFEHIDSUFVNVOVPUKOABCDVBUSFEVJH
      IJVKVLUSTZKLMNUGULZUHZAVOGVMUDZVHUTUEZAEGIHDSUFVOVTWAUKPABCDVBUSEGVJIHJVK
      VLVQKLNMUGULZUHNAVOVTWAWBUIZUJAVHUTFVCAVOVTWAWBUMUNAVIVEGVFAVNVOVPVRUMUOU
      PABCVBUSFVJHIJVKVQLMVLNVSUQABCVBUSGVJHIJVKVQLMVLNWCURUP $.
  $}

  ${
    sectco.b $e |- B = ( Base ` C ) $.
    sectco.o $e |- .x. = ( comp ` C ) $.
    sectco.s $e |- S = ( Sect ` C ) $.
    sectco.c $e |- ( ph -> C e. Cat ) $.
    sectco.x $e |- ( ph -> X e. B ) $.
    sectco.y $e |- ( ph -> Y e. B ) $.
    sectco.z $e |- ( ph -> Z e. B ) $.
    sectco.1 $e |- ( ph -> F ( X S Y ) G ) $.
    sectco.2 $e |- ( ph -> H ( Y S Z ) K ) $.
    $( Composition of two sections.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    sectco $p |- ( ph ->
     ( H ( <. X , Y >. .x. Z ) F ) ( X S Z ) ( G ( <. Z , Y >. .x. X ) K ) ) $=
      ( cop co wbr ccid cfv wceq chom eqid wcel w3a issect mpbid simp1d catcocl
      simp2d catass simp3d oveq1d catlid 3eqtr3d oveq2d 3eqtrd issect2 mpbird )
      AHFJKUBZLEUCUCZGILKUBJEUCUCZJLDUCUDVHVGJLUBZJEUCUCZJCUEUFZUFZUGAVJGIVGVIK
      EUCUCZVFJEUCZUCGFVNUCZVLABCEVGICUHUFZGJJLKMVPUIZNPQSRABCEFHVPJKLMVQNPQRSA
      FJKVPUCUJZGKJVPUCUJZVOVLUGZAFGJKDUCUDVRVSVTUKTABCDEVKFGVPJKMVQNVKUIZOPQRU
      LUMZUNZAHKLVPUCUJZILKVPUCUJZIHKLUBKEUCUCZKVKUFZUGZAHIKLDUCUDWDWEWHUKUAABC
      DEVKHIVPKLMVQNWAOPRSULUMZUNZUOZAWDWEWHWIUPZQAVRVSVTWBUPZUQAVMFGVNAWFFVFKE
      UCZUCWGFWNUCVMFAWFWGFWNAWDWEWHWIURUSABCEFHVPIKJKLMVQNPQRSWCWJRWLUQABCEVKF
      VPJKMVQWAPQNRWCUTVAVBAVRVSVTWBURVCABCDEVKVGVHVPJLMVQNWAOPQSWKABCEIGVPLKJM
      VQNPSRQWLWMUOVDVE $.
  $}

  ${
    $d C c x $.
    $( Function value of the function returning the isomorphisms of a category.
       (Contributed by AV, 5-Apr-2017.) $)
    isofval $p |- ( C e. Cat -> ( Iso ` C ) = ( ( x e. _V |-> dom x )
                                                o. ( Inv ` C ) ) ) $=
      ( vc ccat wcel cvv cv cdm cmpt cinv ccom ciso df-iso wceq fveq2 coeq2d id
      cfv wfun funmpt fvexd cofunexg sylancr fvmptd3 ) BDEZCBAFAGHZIZCGZJRZKUGB
      JRZKZDLFACMUHBNUIUJUGUHBJOPUEQUEUGSUJFEUKFEAFUFTUEBJUAUGUJFUBUCUD $.
  $}

  ${
    $d c x y B $.  $d f g h x y ph $.  $d f g h x y z X $.  $d f g h x y z Y $.
    $d c x y C $.  $d c f g h z N $.  $d c x y S $.
    invfval.b $e |- B = ( Base ` C ) $.
    invfval.n $e |- N = ( Inv ` C ) $.
    invfval.c $e |- ( ph -> C e. Cat ) $.
    ${
      ${
        invffval.s $e |- S = ( Sect ` C ) $.
        $( Value of the inverse relation.  (Contributed by Mario Carneiro,
           2-Jan-2017.)  Removed redundant hypotheses.  (Revised by Zhi Wang,
           27-Oct-2025.) $)
        invffval $p |- ( ph -> N =
        ( x e. B , y e. B |-> ( ( x S y ) i^i `' ( y S x ) ) ) ) $=
          ( vc cinv cfv cv co ccnv cin cbs csect cmpo ccat fveq2 eqtr4di cnveqd
          wcel wceq oveqd ineq12d mpoeq123dv df-inv fvexi mpoex fvmpt eqtrid
          syl ) AGEMNZBCDDBOZCOZFPZUSURFPZQZRZUAZIAEUBUFUQVDUGJLEBCLOZSNZVFURUS
          VETNZPZUSURVGPZQZRZUAVDUBMVEEUGZBCVFVFVKDDVCVLVFESNDVEESUCHUDZVMVLVHU
          TVJVBVLVGFURUSVLVGETNFVEETUCKUDZUHVLVIVAVLVGFUSURVNUHUEUIUJBCLUKBCDDV
          CDESHULZVOUMUNUPUO $.
      $}

      invfval.x $e |- ( ph -> X e. B ) $.
      invfval.y $e |- ( ph -> Y e. B ) $.
      invfval.s $e |- S = ( Sect ` C ) $.
      $( Value of the inverse relation.  (Contributed by Mario Carneiro,
         2-Jan-2017.) $)
      invfval $p |- ( ph -> ( X N Y ) = ( ( X S Y ) i^i `' ( Y S X ) ) ) $=
        ( vx vy cv co ccnv cin cvv wceq wa simprl simprr oveq12d cnveqd ineq12d
        invffval wcel ovex inex1 a1i ovmpod ) ANOFGBBNPZOPZDQZUOUNDQZRZSFGDQZGF
        DQZRZSZETANOBCDEHIJMUHAUNFUAZUOGUAZUBUBZUPUSURVAVEUNFUOGDAVCVDUCZAVCVDU
        DZUEVEUQUTVEUOGUNFDVGVFUEUFUGKLVBTUIAUSVAFGDUJUKULUM $.

      $( Value of the inverse relation.  (Contributed by Mario Carneiro,
         2-Jan-2017.) $)
      isinv $p |- ( ph ->
        ( F ( X N Y ) G <-> ( F ( X S Y ) G /\ G ( Y S X ) F ) ) ) $=
        ( co wbr wa cfv eqid ccnv cin invfval breqd brin bitrdi wrel wb cxp wss
        chom cco ccid sectss relxp relss mpisyl relbrcnvg syl anbi2d bitrd ) AE
        FHIGPZQZEFHIDPZQZEFIHDPZUAZQZRZVEFEVFQZRAVCEFVDVGUBZQVIAVBVKEFABCDGHIJK
        LMNOUCUDEFVDVGUEUFAVHVJVEAVFUGZVHVJUHAVFIHCUKSZPZHIVMPZUIZUJVPUGVLABCDC
        ULSZCUMSZVMIHJVMTVQTVRTOLNMUNVNVOUOVFVPUPUQEFVFURUSUTVA $.
    $}

    invss.x $e |- ( ph -> X e. B ) $.
    invss.y $e |- ( ph -> Y e. B ) $.
    ${
      invss.h $e |- H = ( Hom ` C ) $.
      $( The inverse relation is a relation between morphisms ` F : X --> Y `
         and their inverses ` G : Y --> X ` .  (Contributed by Mario Carneiro,
         2-Jan-2017.) $)
      invss $p |- ( ph -> ( X N Y ) C_ ( ( X H Y ) X. ( Y H X ) ) ) $=
        ( co csect cfv cxp ccnv cin eqid invfval inss1 eqsstrdi cco ccid sectss
        sstrd ) AFGENZFGCOPZNZFGDNGFDNQAUHUJGFUINRZSUJABCUIEFGHIJKLUITZUAUJUKUB
        UCABCUICUDPZCUEPZDFGHMUMTUNTULJKLUFUG $.
    $}

    $( The inverse relation is symmetric.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    invsym $p |- ( ph -> ( F ( X N Y ) G <-> G ( Y N X ) F ) ) $=
      ( co wbr csect cfv wa eqid isinv biancomd bitr4d ) ADEGHFNOZEDHGCPQZNOZDE
      GHUDNOZREDHGFNOAUCUEUFABCUDDEFGHIJKLMUDSZTUAABCUDEDFHGIJKMLUGTUB $.

    $( The inverse relation is symmetric.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    invsym2 $p |- ( ph -> `' ( X N Y ) = ( Y N X ) ) $=
      ( vg vf co wrel cv wbr wcel vex df-br ccnv wa wceq chom cfv cxp wss invss
      relxp relss mpisyl relcnv jctil cop invsym brcnv bitr3i 3bitr3g eqrelrdv2
      eqid mpancom ) EFDNZUAZOZFEDNZOZUBAVCVEUCAVFVDAVEFECUDUEZNZEFVGNZUFZUGVJO
      VFABCVGDFEGHIKJVGUTUHVHVIUIVEVJUJUKVBULUMALMVCVEAMPZLPZVBQZVLVKVEQVLVKUNZ
      VCRZVNVERABCVKVLDEFGHIJKUOVMVLVKVCQVOVLVKVBLSMSUPVLVKVCTUQVLVKVETURUSVA
      $.

    $( The inverse relation is a function, which is to say that every morphism
       has at most one inverse.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    invfun $p |- ( ph -> Fun ( X N Y ) ) $=
      ( vf vg vh co cv wbr wal wcel adantr wrel wa weq wi wfun chom cfv cxp wss
      eqid invss relxp relss csect ccat isinv simplbda adantrr simprbda adantrl
      mpisyl sectcan ex alrimiv alrimivv dffun2 sylanbrc ) AEFDOZUAZLPZMPZVHQZV
      JNPZVHQZUBZMNUCZUDZNRZMRLRVHUEAVHEFCUFUGZOZFEVSOZUHZUIWBUAVIABCVSDEFGHIJK
      VSUJUKVTWAULVHWBUMVAAVRLMAVQNAVOVPAVOUBBCCUNUGZVJVKVMFEGWCUJZACUOSVOITAFB
      SVOKTAEBSVOJTAVLVKVJFEWCOZQZVNAVLVJVKEFWCOZQWFABCWCVJVKDEFGHIJKWDUPUQURAV
      NVJVMWGQZVLAVNWHVMVJWEQABCWCVJVMDEFGHIJKWDUPUSUTVBVCVDVELMNVHVFVG $.

    $d z C $.
    isoval.n $e |- I = ( Iso ` C ) $.
    $( The isomorphisms are the domain of the inverse relation.  (Contributed
       by Mario Carneiro, 2-Jan-2017.)  (Proof shortened by AV,
       21-May-2020.) $)
    isoval $p |- ( ph -> ( X I Y ) = dom ( X N Y ) ) $=
      ( vz vx vy co cvv cv cfv cdm cmpt ccom ciso cinv ccat wcel isofval coeq2i
      wceq syl 3eqtr4g oveqd cop cxp wfn csect ccnv cmpo eqid ovex inex1 fnmpoi
      invffval fneq1d mpbiri opelxpd fvco2 syl2anc df-ov dmeq dmex fvmpt fveq2i
      cin ax-mp eqtr3i eqtrd ) AFGDQFGNRNSZUAZUBZEUCZQZFGEQZUAZADWBFGACUDTZWACU
      ETZUCZDWBACUFUGWFWHUJJNCUHUKMEWGWAIUIULUMAFGUNZWBTZWIETZWATZWCWEAEBBUOZUP
      ZWIWMUGWJWLUJAWNOPBBOSZPSZCUQTZQZWPWOWQQURZVOZUSZWMUPOPBBWTXAXAUTWRWSWOWP
      WQVAVBVCAWMEXAAOPBCWQEHIJWQUTVDVEVFAFGBBKLVGWMWAEWIVHVIFGWBVJWDWATZWEWLWD
      RUGXBWEUJFGEVAZNWDVTWERWAVSWDVKWAUTWDXCVLVMVPWDWKWAFGEVJVNVQULVR $.

    ${
      inviso1.1 $e |- ( ph -> F ( X N Y ) G ) $.
      $( If ` G ` is an inverse to ` F ` , then ` F ` is an isomorphism.
         (Contributed by Mario Carneiro, 3-Jan-2017.) $)
      inviso1 $p |- ( ph -> F e. ( X I Y ) ) $=
        ( co cdm wrel wbr wcel wfun invfun funrel syl releldm syl2anc eleqtrrd
        isoval ) ADHIGQZRZHIFQAUJSZDEUJTDUKUAAUJUBULABCGHIJKLMNUCUJUDUEPDEUJUFU
        GABCFGHIJKLMNOUIUH $.

      $( If ` G ` is an inverse to ` F ` , then ` G ` is an isomorphism.
         (Contributed by Mario Carneiro, 3-Jan-2017.) $)
      inviso2 $p |- ( ph -> G e. ( Y I X ) ) $=
        ( co wbr invsym mpbid inviso1 ) ABCEDFGIHJKLNMOADEHIGQREDIHGQRPABCDEGHI
        JKLMNSTUA $.
    $}

    $( The inverse relation is a function from isomorphisms to isomorphisms.
       (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    invf $p |- ( ph -> ( X N Y ) : ( X I Y ) --> ( Y I X ) ) $=
      ( co wfn crn wss wf cdm isoval invfun funfnd fneq2d wceq ccnv df-rn dmeqd
      mpbird invsym2 eqtr4d eqtrid eqimss syl df-f sylanbrc ) AFGENZFGDNZOZUPPZ
      GFDNZQZUQUTUPRAURUPUPSZOAUPABCEFGHIJKLUAUBAUQVBUPABCDEFGHIJKLMTUCUHAUSUTU
      DVAAUSUPUEZSZUTUPUFAVDGFENZSUTAVCVEABCEFGHIJKLUIUGABCDEGFHIJLKMTUJUKUSUTU
      LUMUQUTUPUNUO $.

    $( The inverse relation is a bijection from isomorphisms to isomorphisms.
       This means that every isomorphism ` F e. ( X I Y ) ` has a unique
       inverse, denoted by ` ( ( Inv `` C ) `` F ) ` .  Remark 3.12 of [Adamek]
       p. 28.  (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    invf1o $p |- ( ph -> ( X N Y ) : ( X I Y ) -1-1-onto-> ( Y I X ) ) $=
      ( co wfn ccnv wf1o invf ffnd invsym2 fneq1d mpbird dff1o4 sylanbrc ) AFGE
      NZFGDNZOUEPZGFDNZOZUFUHUEQAUFUHUEABCDEFGHIJKLMRSAUIGFENZUHOAUHUFUJABCDEGF
      HIJLKMRSAUHUGUJABCEFGHIJKLTUAUBUFUHUEUCUD $.

    invinv.f $e |- ( ph -> F e. ( X I Y ) ) $.
    $( The inverse of the inverse of an isomorphism is itself.  Proposition
       3.14(1) of [Adamek] p. 29.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    invinv $p |- ( ph -> ( ( Y N X ) ` ( ( X N Y ) ` F ) ) = F ) $=
      ( co cfv ccnv invsym2 fveq1d wf1o wcel invf1o f1ocnvfv1 syl2anc eqtr3d
      wceq ) ADGHFPZQZUHRZQZUIHGFPZQDAUIUJULABCFGHIJKLMSTAGHEPZHGEPZUHUADUMUBUK
      DUGABCEFGHIJKLMNUCOUMUNDUHUDUEUF $.

    invco.o $e |- .x. = ( comp ` C ) $.
    invco.z $e |- ( ph -> Z e. B ) $.
    invco.f $e |- ( ph -> G e. ( Y I Z ) ) $.
    $( The composition of two isomorphisms is an isomorphism, and the inverse
       is the composition of the individual inverses.  Proposition 3.14(2) of
       [Adamek] p. 29.  (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    invco $p |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) ( X N Z )
      ( ( ( X N Y ) ` F ) ( <. Z , Y >. .x. X ) ( ( Y N Z ) ` G ) ) ) $=
      ( cop co cfv wbr csect eqid wa cdm wcel isoval eleqtrd wb invfun funfvbrb
      wfun syl mpbid isinv simpld sectco simprd mpbir2and ) AFEIJUBKDUCUCZEIJHU
      CZUDZFJKHUCZUDZKJUBIDUCUCZIKHUCUEVDVIIKCUFUDZUCUEVIVDKIVJUCUEABCVJDEVFFVH
      IJKLSVJUGZNOPTAEVFIJVJUCUEZVFEJIVJUCUEZAEVFVEUEZVLVMUHAEVEUIZUJZVNAEIJGUC
      VORABCGHIJLMNOPQUKULAVEUPVPVNUMABCHIJLMNOPUNEVEUOUQURABCVJEVFHIJLMNOPVKUS
      URZUTAFVHJKVJUCUEZVHFKJVJUCUEZAFVHVGUEZVRVSUHAFVGUIZUJZVTAFJKGUCWAUAABCGH
      JKLMNPTQUKULAVGUPWBVTUMABCHJKLMNPTUNFVGUOUQURABCVJFVHHJKLMNPTVKUSURZUTVAA
      BCVJDVHFVFEKJILSVKNTPOAVRVSWCVBAVLVMVQVBVAABCVJVDVIHIKLMNOTVKUSVC $.
  $}

  ${
    $d C f g $.  $d F f g $.  $d H f g $.  $d I g $.  $d X f g $.  $d Y f g $.
    $d .o. g $.  $d .* g $.  $d .1. f g $.  $d ph f g $.
    dfiso2.b $e |- B = ( Base ` C ) $.
    dfiso2.h $e |- H = ( Hom ` C ) $.
    dfiso2.c $e |- ( ph -> C e. Cat ) $.
    dfiso2.i $e |- I = ( Iso ` C ) $.
    dfiso2.x $e |- ( ph -> X e. B ) $.
    dfiso2.y $e |- ( ph -> Y e. B ) $.
    dfiso2.f $e |- ( ph -> F e. ( X H Y ) ) $.
    dfiso2.1 $e |- .1. = ( Id ` C ) $.
    dfiso2.o $e |- .o. = ( <. X , Y >. ( comp ` C ) X ) $.
    dfiso2.p $e |- .* = ( <. Y , X >. ( comp ` C ) Y ) $.
    $( Alternate definition of an isomorphism of a category, according to
       definition 3.8 in [Adamek] p. 28.  (Contributed by AV, 10-Apr-2020.) $)
    dfiso2 $p |- ( ph -> ( F e. ( X I Y ) <-> E. g e. ( Y H X )
               ( ( g .o. F ) = ( .1. ` X ) /\ ( F .* g ) = ( .1. ` Y ) ) ) ) $=
      ( vf co wcel cinv cfv cdm csect ccnv cin cv wceq wrex eqid isoval invfval
      eleq2d dmeqd cop cco wex cab copab sectfval cnveqd cnvopab eqtrdi ineq12d
      wa inopab an4 an42 anidm bitri anbi1i opabbii eqtri dmopab wb eleq1 oveq2
      anbi1d eqeq1d oveq1 anbi12d exbidv syl biantrurd bicomd a1i eqcomd df-rex
      elabg oveqd bitr4di 3bitrd ) AFJKHUDZUEFJKCUFUGZUDZUHZUEFJKCUIUGZUDZKJXBU
      DZUJZUKZUHZUEZEULZFLUDZJDUGZUMZFXIIUDZKDUGZUMZVJZEKJGUDZUNZAWRXAFABCHWSJK
      MWSUOZOQRPUPURAXAXGFAWTXFABCXBWSJKMXSOQRXBUOZUQUSURAXHFUCULZJKGUDZUEZXIXQ
      UEZVJZXIYAJKUTJCVAUGZUDZUDZXKUMZYAXIKJUTKYFUDZUDZXNUMZVJZVJZEVBZUCVCZUEZF
      YBUEZYDVJZXIFYGUDZXKUMZFXIYJUDZXNUMZVJZVJZEVBZXRAXGYPFAXGYNUCEVDZUHYPAXFU
      UGAXFYEYIVJZUCEVDZYDYCVJZYLVJZUCEVDZUKZUUGAXCUUIXEUULABCXBYFDUCEGJKMNYFUO
      ZTXTOQRVEAXEUUKEUCVDZUJUULAXDUUOABCXBYFDEUCGKJMNUUNTXTORQVEVFUUKEUCVGVHVI
      UUMUUHUUKVJZUCEVDUUGUUHUUKUCEVKUUPYNUCEUUPYEUUJVJZYMVJYNYEYIUUJYLVLUUQYEY
      MUUQYEYEVJYEYCYDYDYCVMYEVNVOVPVOVQVRVHUSYNUCEVSVHURAYRYQUUFVTSYOUUFUCFYBY
      AFUMZYNUUEEUURYEYSYMUUDUURYCYRYDYAFYBWAWCUURYIUUAYLUUCUURYHYTXKYAFXIYGWBW
      DUURYKUUBXNYAFXIYJWEWDWFWFWGWNWHAUUFYDXPVJZEVBXRAUUEUUSEAYSYDUUDXPAYDYSAY
      RYDSWIWJAUUAXLUUCXOAYTXJXKAYGLXIFALYGLYGUMAUAWKWLWOWDAUUBXMXNAYJIFXIAIYJI
      YJUMAUBWKWLWOWDWFWFWGXPEXQWMWPWQWQ $.
  $}

  ${
    $d C g $.  $d F g $.  $d H g $.  $d I g $.  $d X g $.  $d Y g $.
    $d ph g $.
    dfiso3.b $e |- B = ( Base ` C ) $.
    dfiso3.h $e |- H = ( Hom ` C ) $.
    dfiso3.i $e |- I = ( Iso ` C ) $.
    dfiso3.s $e |- S = ( Sect ` C ) $.
    dfiso3.c $e |- ( ph -> C e. Cat ) $.
    dfiso3.x $e |- ( ph -> X e. B ) $.
    dfiso3.y $e |- ( ph -> Y e. B ) $.
    dfiso3.f $e |- ( ph -> F e. ( X H Y ) ) $.
    $( Alternate definition of an isomorphism of a category as a section in
       both directions.  (Contributed by AV, 11-Apr-2020.) $)
    dfiso3 $p |- ( ph -> ( F e. ( X I Y ) <-> E. g e. ( Y H X )
                                      ( g ( Y S X ) F /\ F ( X S Y ) g ) ) ) $=
      ( co wcel cv cop cco cfv ccid wceq wrex wbr eqid dfiso2 ccat adantr simpr
      wa issect2 anbi12d ancom bitr2di rexbidva bitrd ) AFIJHSTEUAZFIJUBICUCUDZ
      SZSICUEUDZUDUFZFVAJIUBJVBSZSJVDUDUFZUNZEJIGSZUGVAFJIDSUHZFVAIJDSUHZUNZEVI
      UGABCVDEFGHVFIJVCKLOMPQRVDUIZVCUIVFUIUJAVHVLEVIAVAVITZUNZVLVGVEUNVHVOVJVG
      VKVEVOBCDVBVDVAFGJIKLVBUIZVMNACUKTVNOULZAJBTVNQULZAIBTVNPULZAVNUMZAFIJGST
      VNRULZUOVOBCDVBVDFVAGIJKLVPVMNVQVSVRWAVTUOUPVGVEUQURUSUT $.
  $}

  ${
    inveq.b $e |- B = ( Base ` C ) $.
    inveq.n $e |- N = ( Inv ` C ) $.
    inveq.c $e |- ( ph -> C e. Cat ) $.
    inveq.x $e |- ( ph -> X e. B ) $.
    inveq.y $e |- ( ph -> Y e. B ) $.
    $( If there are two inverses of a morphism, these inverses are equal.
       Corollary 3.11 of [Adamek] p. 28.  (Contributed by AV, 10-Apr-2020.)
       (Revised by AV, 3-Jul-2022.) $)
    inveq $p |- ( ph -> ( ( F ( X N Y ) G /\ F ( X N Y ) K ) -> G = K ) ) $=
      ( co wbr wa wcel adantr isinv wceq csect cfv eqid wi simpr biimtrdi com12
      ccat impcom simpl adantld imp sectcan ex ) ADEHIGOZPZDFUPPZQZEFUAAUSQBCCU
      BUCZDEFIHJUTUDZACUIRUSLSAIBRUSNSAHBRUSMSUSAEDIHUTOZPZUQAVCUEURAUQVCAUQDEH
      IUTOZPZVCQVCABCUTDEGHIJKLMNVATVEVCUFUGUHSUJAUSDFVDPZAURVFUQAURVFFDVBPZQVF
      ABCUTDFGHIJKLMNVATVFVGUKUGULUMUNUO $.
  $}

  ${
    $d C c x y $.
    $( The function value of the function returning the isomorphisms of a
       category is a function over the Cartesian square of the base set of the
       category.  (Contributed by AV, 5-Apr-2020.) $)
    isofn $p |- ( C e. Cat
                  -> ( Iso ` C ) Fn ( ( Base ` C ) X. ( Base ` C ) ) ) $=
      ( vx vy vc ccat wcel cfv cbs wfn cvv cv cinv wral eqid syl csect ccnv cin
      co wa ciso cxp cdm cmpt ccom dmexg adantl ralrimiva fnmpt cmpo ovex inex1
      crn wss a1i ralrimivva fnmpo df-inv fveq2 oveqd cnveqd ineq12d mpoeq123dv
      wceq fvex pm3.2i mpoexga mp1i fvmptd3 fneq1d mpbird fnco syl3anc isofval
      id ssv ) AEFZAUAGZAHGZVSUBZIBJBKZUCZUDZALGZUEZVTIZVQWCJIZWDVTIZWDUMZJUNZW
      FVQWBJFZBJMWGVQWKBJWAJFWKVQWAJUFUGUHBJWBWCJWCNUIOVQWHBCVSVSWACKZAPGZSZWLW
      AWMSZQZRZUJZVTIZVQWQJFZCVSMBVSMWSVQWTBCVSVSWTVQWAVSFWLVSFTTWNWPWAWLWMUKUL
      UOUPBCVSVSWQWRJWRNUQOVQVTWDWRVQDABCDKZHGZXBWAWLXAPGZSZWLWAXCSZQZRZUJWRELJ
      BCDURXAAVDZBCXBXBXGVSVSWQXAAHUSZXIXHXDWNXFWPXHXCWMWAWLXAAPUSZUTXHXEWOXHXC
      WMWLWAXJUTVAVBVCVQVOVSJFZXKTWRJFVQXKXKAHVEZXLVFBCVSVSWQJJVGVHVIVJVKWJVQWI
      VPUOJVTWCWDVLVMVQVTVRWEBAVNVJVK $.
  $}

  ${
    isohom.b $e |- B = ( Base ` C ) $.
    isohom.h $e |- H = ( Hom ` C ) $.
    isohom.i $e |- I = ( Iso ` C ) $.
    isohom.c $e |- ( ph -> C e. Cat ) $.
    isohom.x $e |- ( ph -> X e. B ) $.
    isohom.y $e |- ( ph -> Y e. B ) $.
    $( An isomorphism is a homomorphism.  (Contributed by Mario Carneiro,
       27-Jan-2017.) $)
    isohom $p |- ( ph -> ( X I Y ) C_ ( X H Y ) ) $=
      ( co cxp cdm cinv cfv eqid wss isoval invss dmss eqsstrd dmxpss sstrdi
      syl ) AFGENZFGDNZGFDNZOZPZUIAUHFGCQRZNZPZULABCEUMFGHUMSZKLMJUAAUNUKTUOULT
      ABCDUMFGHUPKLMIUBUNUKUCUGUDUIUJUEUF $.
  $}

  ${
    isoco.b $e |- B = ( Base ` C ) $.
    isoco.o $e |- .x. = ( comp ` C ) $.
    isoco.n $e |- I = ( Iso ` C ) $.
    isoco.c $e |- ( ph -> C e. Cat ) $.
    isoco.x $e |- ( ph -> X e. B ) $.
    isoco.y $e |- ( ph -> Y e. B ) $.
    isoco.z $e |- ( ph -> Z e. B ) $.
    isoco.f $e |- ( ph -> F e. ( X I Y ) ) $.
    isoco.g $e |- ( ph -> G e. ( Y I Z ) ) $.
    $( The composition of two isomorphisms is an isomorphism.  Proposition
       3.14(2) of [Adamek] p. 29.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    isoco $p |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) e. ( X I Z ) ) $=
      ( co cop cinv cfv eqid invco inviso1 ) ABCFEHIUAJDTTEHICUBUCZTUCFIJUGTUCJ
      IUAHDTTGUGHJKUGUDZNOQMABCDEFGUGHIJKUHNOPMRLQSUEUF $.
  $}

  ${
    $d f g ph $.  $d f g S $.  $d f g T $.  $d f g X $.  $d f g Y $.
    oppcsect.b $e |- B = ( Base ` C ) $.
    oppcsect.o $e |- O = ( oppCat ` C ) $.
    oppcsect.c $e |- ( ph -> C e. Cat ) $.
    oppcsect.x $e |- ( ph -> X e. B ) $.
    oppcsect.y $e |- ( ph -> Y e. B ) $.
    ${
      oppcsect.s $e |- S = ( Sect ` C ) $.
      oppcsect.t $e |- T = ( Sect ` O ) $.
      $( A section in the opposite category.  (Contributed by Mario Carneiro,
         3-Jan-2017.) $)
      oppcsect $p |- ( ph -> ( F ( X T Y ) G <-> G ( X S Y ) F ) ) $=
        ( cfv co wcel chom cop cco ccid wceq w3a wbr wa eqid adantr oppcco ccat
        oppcid syl fveq1d eqeq12d pm5.32da df-3an oppchom eleq2i anbi12ci bitri
        anbi1i 3bitr4g oppcbas oppccat issect 3bitr4d ) AFIJHUARZSZTZGJIVISZTZG
        FIJUBZIHUCRZSSZIHUDRZRZUEZUFZGIJCUARZSZTZFJIWASZTZFGVNICUCRZSSZICUDRZRZ
        UEZUFZFGIJESUGGFIJDSUGAWCWEUHZVSUHZWLWJUHVTWKAWLVSWJAWLUHZVPWGVRWIWNBCW
        FFGHIJIKWFUIZLAIBTWLNUJZAJBTWLOUJWPUKWNIVQWHWNCULTZVQWHUEAWQWLMUJWHCHLW
        HUIZUMUNUOUPUQVTVKVMUHZVSUHWMVKVMVSURWSWLVSVKWEVMWCVJWDFCWAHIJWAUIZLUSU
        TVLWBGCWAHJIWTLUSUTVAVCVBWCWEWJURVDABHEVOVQFGVIIJBCHLKVEVIUIVOUIVQUIQAW
        QHULTMCHLVFUNNOVGABCDWFWHGFWAIJKWTWOWRPMNOVGVH $.

      $( A section in the opposite category.  (Contributed by Mario Carneiro,
         3-Jan-2017.) $)
      oppcsect2 $p |- ( ph -> ( X T Y ) = `' ( X S Y ) ) $=
        ( vf vg co cfv wrel ccnv chom cxp wss cco ccid oppcbas eqid oppccat syl
        ccat wcel sectss relxp relss mpisyl relcnv a1i wbr oppcsect vex bitr4di
        cv brcnv eqbrrdv ) APQGHERZGHDRZUAZAVFGHFUBSZRZHGVIRZUCZUDVLTVFTABFEFUE
        SZFUFSZVIGHBCFJIUGVIUHVMUHVNUHOACUKULFUKULKCFJUIUJLMUMVJVKUNVFVLUOUPVHT
        AVGUQURAPVCZQVCZVFUSVPVOVGUSVOVPVHUSABCDEVOVPFGHIJKLMNOUTVOVPVGPVAQVAVD
        VBVE $.
    $}

    ${
      oppcinv.s $e |- I = ( Inv ` C ) $.
      oppcinv.t $e |- J = ( Inv ` O ) $.
      $( An inverse in the opposite category.  (Contributed by Mario Carneiro,
         3-Jan-2017.) $)
      oppcinv $p |- ( ph -> ( X J Y ) = ( Y I X ) ) $=
        ( cfv co ccnv cin eqid csect incom oppcsect2 wrel wceq chom cxp wss cco
        cnveqd ccid sectss relxp relss mpisyl dfrel2 sylib eqtrd ineq12d eqtrid
        oppcbas ccat wcel oppccat syl invfval 3eqtr4d ) AGHFUAPZQZHGVHQZRZSZHGC
        UAPZQZGHVMQRZSZGHEQHGDQAVLVKVISVPVIVKUBAVKVNVIVOAVKVNRZRZVNAVJVQABCVMVH
        FHGIJKMLVMTZVHTZUCUJAVNUDZVRVNUEAVNHGCUFPZQZGHWBQZUGZUHWEUDWAABCVMCUIPZ
        CUKPZWBHGIWBTWFTWGTVSKMLULWCWDUMVNWEUNUOVNUPUQURABCVMVHFGHIJKLMVSVTUCUS
        UTABFVHEGHBCFJIVAOACVBVCFVBVCKCFJVDVELMVTVFABCVMDHGINKMLVSVFVG $.
    $}

    ${
      oppciso.s $e |- I = ( Iso ` C ) $.
      oppciso.t $e |- J = ( Iso ` O ) $.
      $( An isomorphism in the opposite category.  See also remark 3.9 in
         [Adamek] p. 28.  (Contributed by Mario Carneiro, 3-Jan-2017.) $)
      oppciso $p |- ( ph -> ( X J Y ) = ( Y I X ) ) $=
        ( cinv cfv co cdm eqid oppcinv oppcbas ccat wcel oppccat isoval 3eqtr4d
        dmeqd syl ) AGHFPQZRZSHGCPQZRZSGHERHGDRAUKUMABCULUJFGHIJKLMULTZUJTZUAUH
        ABFEUJGHBCFJIUBUOACUCUDFUCUDKCFJUEUILMOUFABCDULHGIUNKMLNUFUG $.
    $}
  $}

  ${
    $d g h x B $.  $d g h x C $.  $d g h x F $.  $d g h x ph $.  $d g h x X $.
    $d g h x Y $.
    sectmon.b $e |- B = ( Base ` C ) $.
    sectmon.m $e |- M = ( Mono ` C ) $.
    sectmon.s $e |- S = ( Sect ` C ) $.
    sectmon.c $e |- ( ph -> C e. Cat ) $.
    sectmon.x $e |- ( ph -> X e. B ) $.
    sectmon.y $e |- ( ph -> Y e. B ) $.
    ${
      sectmon.1 $e |- ( ph -> F ( X S Y ) G ) $.
      $( If ` F ` is a section of ` G ` , then ` F ` is a monomorphism.
         Proposition 7.35 of [Adamek] p. 110.  A monomorphism that arises from
         a section is also known as a _split monomorphism_.  (Contributed by
         Mario Carneiro, 3-Jan-2017.) $)
      sectmon $p |- ( ph -> F e. ( X M Y ) ) $=
        ( vg co wcel ad2antrr vx vh chom cfv cv cop cco wceq wral ccid wbr eqid
        wi issect mpbid simp1d wa oveq2 simp3d oveq1d ccat simplr simprl simp2d
        w3a catass catlid 3eqtr3d simprr eqeq12d ralrimivva ralrimiva mpbir2and
        imbitrid ismon2 ) AEHIGRSEHICUCUDZRSZEQUEZUAUEZHUFZICUGUDZRZRZEUBUEZWBR
        ZUHZVRWDUHZUMZUBVSHVPRZUIQWIUIZUABUIAVQFIHVPRSZFEHIUFHWARRZHCUJUDZUDZUH
        ZAEFHIDRUKVQWKWOVEPABCDWAWMEFVPHIJVPULZWAULZWMULZLMNOUNUOZUPZAWJUABAVSB
        SZUQZWHQUBWIWIWFFWCVSIUFHWARZRZFWEXCRZUHXBVRWISZWDWISZUQZUQZWGWCWEFXCUR
        XIXDVRXEWDXIWLVRVTHWARZRWNVRXJRXDVRXIWLWNVRXJAWOXAXHAVQWKWOWSUSTZUTXIBC
        WAVREVPFHVSHIJWPWQACVASXAXHMTZAXAXHVBZAHBSXAXHNTZAIBSXAXHOTZXBXFXGVCZAV
        QXAXHWTTZXNAWKXAXHAVQWKWOWSVDTZVFXIBCWAWMVRVPVSHJWPWRXLXMWQXNXPVGVHXIWL
        WDXJRWNWDXJRXEWDXIWLWNWDXJXKUTXIBCWAWDEVPFHVSHIJWPWQXLXMXNXOXBXFXGVIZXQ
        XNXRVFXIBCWAWMWDVPVSHJWPWRXLXMWQXNXSVGVHVJVNVKVLAUABCWAQUBEVPGHIJWPWQKM
        NOVOVM $.
    $}

    monsect.n $e |- N = ( Inv ` C ) $.
    monsect.1 $e |- ( ph -> F e. ( X M Y ) ) $.
    monsect.2 $e |- ( ph -> G ( Y S X ) F ) $.
    $( If ` F ` is a monomorphism and ` G ` is a section of ` F ` , then ` G `
       is an inverse of ` F ` and they are both isomorphisms.  This is also
       stated as "a monomorphism which is also a split epimorphism is an
       isomorphism".  (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    monsect $p |- ( ph -> F ( X N Y ) G ) $=
      ( co wbr cop cco cfv ccid wceq chom wcel eqid issect simp3d oveq1d simp2d
      w3a mpbid simp1d catass catlid catrid eqtr4d 3eqtr3d catcocl catidcl moni
      issect2 mpbird isinv mpbir2and ) AEFIJHTUAEFIJDTUAZFEJIDTUAZAVIFEIJUBZICU
      CUDZTTZICUEUDZUDZUFZAEVMIIUBJVLTZTZEVOVQTZUFVPAEFJIUBJVLTTZEVKJVLTZTJVNUD
      ZEWATZVRVSAVTWBEWAAFJICUGUDZTUHZEIJWDTUHZVTWBUFZAVJWEWFWGUNSABCDVLVNFEWDJ
      IKWDUIZVLUIZVNUIZMNPOUJUOZUKULABCVLEFWDEJIJIKWHWINOPOAWEWFWGWKUMZAWEWFWGW
      KUPZPWLUQAWCEVSABCVLVNEWDIJKWHWJNOWIPWLURABCVLVNEWDIJKWHWJNOWIPWLUSUTVAAB
      CVLEVMWDVOGIJIKWHWILNOPORABCVLEFWDIJIKWHWINOPOWLWMVBABCVNWDIKWHWJNOVCVDUO
      ABCDVLVNEFWDIJKWHWIWJMNOPWLWMVEVFSABCDEFHIJKQNOPMVGVH $.
  $}

  ${
    sectepi.b $e |- B = ( Base ` C ) $.
    sectepi.e $e |- E = ( Epi ` C ) $.
    sectepi.s $e |- S = ( Sect ` C ) $.
    sectepi.c $e |- ( ph -> C e. Cat ) $.
    sectepi.x $e |- ( ph -> X e. B ) $.
    sectepi.y $e |- ( ph -> Y e. B ) $.
    ${
      sectepi.1 $e |- ( ph -> F ( X S Y ) G ) $.
      $( If ` F ` is a section of ` G ` , then ` G ` is an epimorphism.
         Proposition 7.42 of [Adamek] p. 112.  An epimorphism that arises from
         a section is also known as a _split epimorphism_.  (Contributed by
         Mario Carneiro, 3-Jan-2017.) $)
      sectepi $p |- ( ph -> G e. ( Y E X ) ) $=
        ( cfv co eqid ccat coppc cmon csect oppcbas wcel oppccat syl wbr mpbird
        oppcsect sectmon oppcmon eleqtrd ) AGHICUAQZUBQZRIHERABUNUNUCQZGFUOHIBC
        UNUNSZJUDUOSZUPSZACTUEUNTUEMCUNUQUFUGNOAGFHIUPRUHFGHIDRUHPABCDUPGFUNHIJ
        UQMNOLUSUJUIUKACEUOUNHIUQMURKULUM $.
    $}

    episect.n $e |- N = ( Inv ` C ) $.
    episect.1 $e |- ( ph -> F e. ( X E Y ) ) $.
    episect.2 $e |- ( ph -> F ( X S Y ) G ) $.
    $( If ` F ` is an epimorphism and ` F ` is a section of ` G ` , then ` G `
       is an inverse of ` F ` and they are both isomorphisms.  This is also
       stated as "an epimorphism which is also a split monomorphism is an
       isomorphism".  (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    episect $p |- ( ph -> F ( X N Y ) G ) $=
      ( co coppc cfv cinv eqid oppcinv csect cmon oppcbas ccat wcel oppccat syl
      oppcmon eleqtrrd wbr oppcsect mpbird monsect breqdi ) AJICUAUBZUCUBZTIJHT
      FGABCHVAUTJIKUTUDZNPOQVAUDZUEABUTUTUFUBZFGUTUGUBZVAJIBCUTVBKUHVEUDZVDUDZA
      CUIUJUTUIUJNCUTVBUKULPOVCAFIJETJIVETRACEVEUTJIVBNVFLUMUNAGFIJVDTUOFGIJDTU
      OSABCDVDGFUTIJKVBNOPMVGUPUQURUS $.
  $}

  ${
    invid.b $e |- B = ( Base ` C ) $.
    invid.i $e |- I = ( Id ` C ) $.
    invid.c $e |- ( ph -> C e. Cat ) $.
    invid.x $e |- ( ph -> X e. B ) $.
    $( The identity is a section of itself.  (Contributed by AV,
       8-Apr-2020.) $)
    sectid $p |- ( ph -> ( I ` X ) ( X ( Sect ` C ) X ) ( I ` X ) ) $=
      ( cfv csect co wbr cop cco wceq chom eqid catidcl catlid issect2 mpbird )
      AEDJZUCEECKJZLMUCUCEENECOJZLLUCPABCUEDUCCQJZEEFUFRZGHIUERZIABCDUFEFUGGHIS
      ZTABCUDUEDUCUCUFEEFUGUHGUDRHIIUIUIUAUB $.

    $( The inverse of the identity is the identity.  (Contributed by AV,
       8-Apr-2020.) $)
    invid $p |- ( ph -> ( I ` X ) ( X ( Inv ` C ) X ) ( I ` X ) ) $=
      ( cfv cinv co wbr csect sectid eqid isinv mpbir2and ) AEDJZSEECKJZLMSSEEC
      NJZLMZUBABCDEFGHIOZUCABCUASSTEEFTPHIIUAPQR $.

    $( The identity is an isomorphism.  Example 3.13 of [Adamek] p. 28.
       (Contributed by AV, 8-Apr-2020.) $)
    idiso $p |- ( ph -> ( I ` X ) e. ( X ( Iso ` C ) X ) ) $=
      ( cfv ciso cinv eqid invid inviso1 ) ABCEDJZPCKJZCLJZEEFRMHIIQMABCDEFGHIN
      O $.

    $( The inverse of the identity is the identity.  Example 3.13 of [Adamek]
       p. 28.  (Contributed by AV, 9-Apr-2020.) $)
    idinv $p |- ( ph -> ( ( X ( Inv ` C ) X ) ` ( I ` X ) ) = ( I ` X ) ) $=
      ( cinv cfv co wfun wbr wceq eqid invfun invid funbrfv sylc ) AEECJKZLZMED
      KZUCUBNUCUBKUCOABCUAEEFUAPHIIQABCDEFGHIRUCUCUBST $.
  $}

  ${
    invisoinv.b $e |- B = ( Base ` C ) $.
    invisoinv.i $e |- I = ( Iso ` C ) $.
    invisoinv.n $e |- N = ( Inv ` C ) $.
    invisoinv.c $e |- ( ph -> C e. Cat ) $.
    invisoinv.x $e |- ( ph -> X e. B ) $.
    invisoinv.y $e |- ( ph -> Y e. B ) $.
    invisoinv.f $e |- ( ph -> F e. ( X I Y ) ) $.
    $( The inverse of an isomorphism ` F ` (which is unique because of ~ invf
       and is therefore denoted by ` ( ( X N Y ) `` F ) ` , see also remark
       3.12 in [Adamek] p. 28) is invers to the isomorphism.  (Contributed by
       AV, 9-Apr-2020.) $)
    invisoinvl $p |- ( ph -> ( ( X N Y ) ` F ) ( Y N X ) F ) $=
      ( co cfv wbr cop eqid ccid cco ciso idiso a1i oveqd eleqtrrd invco isohom
      wceq chom sseldd catlid cinv fveq1d idinv oveq2d ffvelcdmd catrid 3brtr3d
      eqtrd invf invsym mpbird ) ADGHFPZQZDHGFPRDVFVERAHCUAQZQZDGHSHCUBQZPPVFVH
      HHFPZQZHHSGVIPZPZDVFVEABCVIDVHEFGHHIKLMNJOVITZNAVHHHCUCQZPHHEPABCVGHIVGTZ
      LNUDAEVOHHEVOUJAJUEUFUGUHABCVIVGDCUKQZGHIVQTZVPLMVNNAGHEPZGHVQPDABCVQEGHI
      VRJLMNUIOULUMAVMVFVHVLPVFAVKVHVFVLAVKVHHHCUNQZPZQVHAVHVJWAAFVTHHFVTUJAKUE
      UFUOABCVGHIVPLNUPVAUQABCVIVGVFVQHGIVRVPLNVNMAHGEPZHGVQPVFABCVQEHGIVRJLNMU
      IAVSWBDVEABCEFGHIKLMNJVBOURULUSVAUTABCVFDFHGIKLNMVCVD $.

    $( The inverse of an isomorphism is invers to the isomorphism.
       (Contributed by AV, 9-Apr-2020.) $)
    invisoinvr $p |- ( ph -> F ( X N Y ) ( ( X N Y ) ` F ) ) $=
      ( co cfv wbr invisoinvl invsym mpbird ) ADDGHFPZQZUBRUCDHGFPRABCDEFGHIJKL
      MNOSABCDUCFGHIKLMNTUA $.

    invcoisoid.1 $e |- .1. = ( Id ` C ) $.
    ${
      invcoisoid.o $e |- .o. = ( <. X , Y >. ( comp ` C ) X ) $.
      $( The inverse of an isomorphism composed with the isomorphism is the
         identity.  (Contributed by AV, 5-Apr-2020.) $)
      invcoisoid $p |- ( ph -> ( ( ( X N Y ) ` F ) .o. F ) = ( .1. ` X ) ) $=
        ( co cfv csect wbr wceq invisoinvr wa eqid isinv simpl biimtrdi mpd cop
        cco chom isohom sseldd invf ffvelcdmd issect2 eqcomd oveqd eqeq1d bitrd
        a1i mpbid ) AEEHIGTZUAZHICUBUAZTUCZVGEJTZHDUAZUDZAEVGVFUCZVIABCEFGHIKLM
        NOPQUEAVMVIVGEIHVHTUCZUFVIABCVHEVGGHIKMNOPVHUGZUHVIVNUIUJUKAVIVGEHIULHC
        UMUAZTZTZVKUDVLABCVHVPDEVGCUNUAZHIKVSUGZVPUGRVONOPAHIFTZHIVSTEABCVSFHIK
        VTLNOPUOQUPAIHFTZIHVSTVGABCVSFIHKVTLNPOUOAWAWBEVFABCFGHIKMNOPLUQQURUPUS
        AVRVJVKAVQJVGEAJVQJVQUDASVDUTVAVBVCVE $.
    $}

    isocoinvid.o $e |- .o. = ( <. Y , X >. ( comp ` C ) Y ) $.
    $( The inverse of an isomorphism composed with the isomorphism is the
       identity.  (Contributed by AV, 10-Apr-2020.) $)
    isocoinvid $p |- ( ph -> ( F .o. ( ( X N Y ) ` F ) ) = ( .1. ` Y ) ) $=
      ( co cfv csect wbr wceq invisoinvl eqid isinv simpl biimtrdi mpd cop chom
      wa cco isohom invf ffvelcdmd sseldd issect2 a1i eqcomd oveqd eqeq1d bitrd
      mpbid ) AEHIGTZUAZEIHCUBUAZTUCZEVGJTZIDUAZUDZAVGEIHGTUCZVIABCEFGHIKLMNOPQ
      UEAVMVIEVGHIVHTUCZUMVIABCVHVGEGIHKMNPOVHUFZUGVIVNUHUIUJAVIEVGIHUKICUNUAZT
      ZTZVKUDVLABCVHVPDVGECULUAZIHKVSUFZVPUFRVONPOAIHFTZIHVSTVGABCVSFIHKVTLNPOU
      OAHIFTZWAEVFABCFGHIKMNOPLUPQUQURAWBHIVSTEABCVSFHIKVTLNOPUOQURUSAVRVJVKAVQ
      JEVGAJVQJVQUDASUTVAVBVCVDVE $.
  $}

  ${
    rcaninv.b $e |- B = ( Base ` C ) $.
    rcaninv.n $e |- N = ( Inv ` C ) $.
    rcaninv.c $e |- ( ph -> C e. Cat ) $.
    rcaninv.x $e |- ( ph -> X e. B ) $.
    rcaninv.y $e |- ( ph -> Y e. B ) $.
    rcaninv.z $e |- ( ph -> Z e. B ) $.
    rcaninv.f $e |- ( ph -> F e. ( Y ( Iso ` C ) X ) ) $.
    rcaninv.g $e |- ( ph -> G e. ( Y ( Hom ` C ) Z ) ) $.
    rcaninv.h $e |- ( ph -> H e. ( Y ( Hom ` C ) Z ) ) $.
    rcaninv.1 $e |- R = ( ( Y N X ) ` F ) $.
    rcaninv.o $e |- .o. = ( <. X , Y >. ( comp ` C ) Z ) $.
    $( Right cancellation of an inverse of an isomorphism.  (Contributed by AV,
       5-Apr-2020.) $)
    rcaninv $p |- ( ph -> ( ( G .o. R ) = ( H .o. R ) -> G = H ) ) $=
      ( co wceq wa cfv cop cco ccid chom eqid ciso isohom sseldd invf ffvelcdmd
      catass invcoisoid eqcomd oveq2d catrid 3eqtr2rd adantr a1i eqidd oveq123d
      eqcomi simpr eqtrd oveq1d oveqi oveq1i eqeltrid oveq2i 3eqtrd ex ) AFDKUD
      ZGDKUDZUEZFGUEAVTUFZFFEJIHUDZUGZIJUHLCUIUGZUDZUDZEJIUHZLWDUDZUDZVSEWHUDZG
      AFWIUEVTAWIFWCEWGJWDUDZUDZJJUHLWDUDZUDFJCUJUGZUGZWMUDFABCWDEWCCUKUGZFLJIJ
      MWPULZWDULZOQPQAJICUMUGZUDZJIWPUDEABCWPWSJIMWQWSULZOQPUNSUOZAIJWSUDZIJWPU
      DZWCABCWPWSIJMWQXAOPQUNAWTXCEWBABCWSHJIMNOQPXAUPSUQUOZRTURAWOWLFWMAWLWOAB
      CWNEWSHJIWKMXANOQPSWNULZWKULUSZUTVAABCWDWNFWPJLMWQXFOQWRRTVBVCVDWAWFVSEWH
      WAWFVRVSAWFVRUEVTAFFWCDWEKWEKUEAKWEUCVHVEAFVFWCDUEADWCUBVHVEVGVDAVTVIVJVK
      AWJGUEVTAWJGDWEUDZEWHUDZGWOWMUDZGWJXIUEAVSXHEWHKWEGDUCVLVMVEAXIGDEWKUDZWM
      UDZGWLWMUDZXJABCWDEDWPGLJIJMWQWROQPQXBADWCXDUBXEVNRUAURXLXMUEAXKWLGWMDWCE
      WKUBVMVOVEAWLWOGWMXGVAVPABCWDWNGWPJLMWQXFOQWRRUAVBVPVDVPVQ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Isomorphic objects
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  In this subsection, the "is isomorphic to" relation between objects of a
  category ` ~=c ` is defined (see ~ df-cic ).  It is shown that this relation
  is an equivalence relation, see ~ cicer .

$)

  $c ~=c $.

  $( Extend class notation to include the category isomorphism relation. $)
  ccic $a class ~=c $.

  $( Function returning the set of isomorphic objects for each category ` c ` .
     Definition 3.15 of [Adamek] p. 29.  Analogous to the definition of the
     group isomorphism relation ` ~=g ` , see ~ df-gic .  (Contributed by AV,
     4-Apr-2020.) $)
  df-cic $a |- ~=c = ( c e. Cat |-> ( ( Iso ` c ) supp (/) ) ) $.

  ${
    $d C c $.
    $( The set of isomorphic objects of the category ` c ` .  (Contributed by
       AV, 4-Apr-2020.) $)
    cicfval $p |- ( C e. Cat -> ( ~=c ` C ) = ( ( Iso ` C ) supp (/) ) ) $=
      ( vc ccat wcel cv ciso cfv c0 csupp co ccic cvv df-cic fveq2 oveq1d ovexd
      wceq id fvmptd3 ) ACDZBABEZFGZHIJAFGZHIJCKLBMUAAQUBUCHIUAAFNOTRTUCHIPS $.
  $}

  ${
    cic.i $e |- I = ( Iso ` C ) $.
    cic.b $e |- B = ( Base ` C ) $.
    cic.c $e |- ( ph -> C e. Cat ) $.
    cic.x $e |- ( ph -> X e. B ) $.
    cic.y $e |- ( ph -> Y e. B ) $.
    $( The relation "is isomorphic to" for categories.  (Contributed by AV,
       5-Apr-2020.) $)
    brcic $p |- ( ph -> ( X ( ~=c ` C ) Y <-> ( X I Y ) =/= (/) ) ) $=
      ( cfv wbr c0 co wcel wne wceq a1i cvv ccic ciso csupp cop ccat cicfval wb
      syl breqd df-br fveq1d neeq1d df-ov eqcomi cbs cxp fvexd eleqtrdi opelxpd
      wfn xpexd isofn fvn0elsuppb syl3anc 3bitr3rd 3bitrd ) AEFCUALZMEFCUBLZNUC
      OZMZEFUDZVIPZEFDOZNQZAVGVIEFACUEPZVGVIRICUFUHUIVJVLUGAEFVIUJSAVKDLZNQVKVH
      LZNQZVNVLAVPVQNAVKDVHDVHRAGSUKULAVPVMNVPVMRAVMVPEFDUMUNSULACUOLZVSUPZTPVK
      VTPVHVTUTZVRVLUGAVSVSTTACUOUQZWBVAAEFVSVSAEBVSJHURAFBVSKHURUSAVOWAICVBUHV
      TVHTVKVCVDVEVF $.

    $d I f $.  $d X f $.  $d Y f $.
    $( Objects ` X ` and ` Y ` in a category are isomorphic provided that there
       is an isomorphism ` f : X --> Y ` , see definition 3.15 of [Adamek]
       p. 29.  (Contributed by AV, 4-Apr-2020.) $)
    cic $p |- ( ph -> ( X ( ~=c ` C ) Y <-> E. f f e. ( X I Y ) ) ) $=
      ( ccic cfv wbr co c0 wne cv wcel wex brcic n0 bitrdi ) AFGCMNOFGEPZQRDSUE
      TDUAABCEFGHIJKLUBDUEUCUD $.

    $d F f $.
    cic.f $e |- ( ph -> F e. ( X I Y ) ) $.
    $( Prove that two objects are isomorphic by an explicit isomorphism.
       (Contributed by AV, 4-Apr-2020.) $)
    brcici $p |- ( ph -> X ( ~=c ` C ) Y ) $=
      ( vf ccic cfv wbr cv co wcel wex eleq1 spcegv sylc cic mpbird ) AFGCOPQNR
      ZFGESZTZNUAZADUHTZUKUJMMUIUKNDUHUGDUHUBUCUDABCNEFGHIJKLUEUF $.
  $}

  $( Isomorphism is reflexive.  (Contributed by AV, 5-Apr-2020.) $)
  cicref $p |- ( ( C e. Cat /\ O e. ( Base ` C ) ) -> O ( ~=c ` C ) O ) $=
    ( ccat wcel cbs cfv wa ccid ciso eqid simpl simpr idiso brcici ) ACDZBAEFZD
    ZGZPABAHFZFAIFZBBTJPJZOQKZOQLZUCRPASBUASJUBUCMN $.

  $( Isomorphism implies the left side is an object.  (Contributed by AV,
     5-Apr-2020.) $)
  ciclcl $p |- ( ( C e. Cat /\ R ( ~=c ` C ) S ) -> R e. ( Base ` C ) ) $=
    ( ccat wcel ccic cfv wbr cbs ciso c0 csupp co cicfval breqd cop cxp wne cvv
    wa wfn wb isofn fvexd 0ex a1i df-br elsuppfng bitrid syl3anc opelxp1 adantr
    w3a biimtrdi sylbid imp ) ADEZBCAFGZHZBAIGZEZUQUSBCAJGZKLMZHZVAUQURVCBCANOU
    QVDBCPZUTUTQZEZVEVBGKRZTZVAUQVBVFUAZVBSEZKSEZVDVIUBAUCUQAJUDVLUQUEUFVDVEVCE
    VJVKVLUMVIBCVCUGVEVBSSVFKUHUIUJVGVAVHBCUTUTUKULUNUOUP $.

  $( Isomorphism implies the right side is an object.  (Contributed by AV,
     5-Apr-2020.) $)
  cicrcl $p |- ( ( C e. Cat /\ R ( ~=c ` C ) S ) -> S e. ( Base ` C ) ) $=
    ( ccat wcel ccic cfv wbr cbs ciso c0 csupp co cicfval breqd cop cxp wne cvv
    wa wfn wb isofn fvexd 0ex a1i df-br elsuppfng bitrid syl3anc opelxp2 adantr
    w3a biimtrdi sylbid imp ) ADEZBCAFGZHZCAIGZEZUQUSBCAJGZKLMZHZVAUQURVCBCANOU
    QVDBCPZUTUTQZEZVEVBGKRZTZVAUQVBVFUAZVBSEZKSEZVDVIUBAUCUQAJUDVLUQUEUFVDVEVCE
    VJVKVLUMVIBCVCUGVEVBSSVFKUHUIUJVGVAVHBCUTUTUKULUNUOUP $.

  ${
    $d C f g $.  $d R f g $.  $d S f g $.
    $( Isomorphism is symmetric.  (Contributed by AV, 5-Apr-2020.) $)
    cicsym $p |- ( ( C e. Cat /\ R ( ~=c ` C ) S ) -> S ( ~=c ` C ) R ) $=
      ( vf vg wcel cfv wbr wa cv co wex simpl simpr adantl isoval adantr sylbid
      eqid cdm ccat ccic cbs cicrcl ciclcl ciso cic cinv crn ccnv invsym2 dmeqd
      eqcomd df-rn eqtr4di eqtrd eleq2d cvv wb vex elrng mp1i bitrd df-br exbii
      cop wi opeldm brcici ex syl5com exlimiv biimtrid exlimdv impancom mp2and
      com12 ) AUAFZBCAUBGZHZICAUCGZFZBWAFZCBVSHZABCUDABCUEVRWBWCIZVTWDVRWEIZVTD
      JZBCAUFGZKZFZDLWDWFWAADWHBCWHSZWASZVRWEMZWEWCVRWBWCNOZWEWBVRWBWCMOZUGWFWJ
      WDDWFWJEJZWGCBAUHGZKZHZELZWDWFWJWGWRUIZFZWTWFWIXAWGWFWIBCWQKZTZXAWFWAAWHW
      QBCWLWQSZWMWNWOWKPWFXDWRUJZTXAWFXCXFWFXFXCWFWAAWQCBWLXEWMWOWNUKUMULWRUNUO
      UPUQWGURFXBWTUSWFDUTZEWGWRURVAVBVCWTWPWGVFWRFZELZWFWDWSXHEWPWGWRVDVEXIWFW
      DXHWFWDVGEXHWPWRTZFZWFWDWPWGWREUTXGVHWFXKWPCBWHKZFZWDWFXJXLWPWFXLXJWFWAAW
      HWQCBWLXEWMWOWNWKPUMUQWFXMWDWFXMIWAAWPWHCBWKWLWFVRXMWMQWFWBXMWOQWFWCXMWNQ
      WFXMNVIVJRVKVLVQVMRVNRVOVP $.

    $d T f g $.
    $( Isomorphism is transitive.  (Contributed by AV, 5-Apr-2020.) $)
    cictr $p |- ( ( C e. Cat /\ R ( ~=c ` C ) S /\ S ( ~=c ` C ) T )
                  -> R ( ~=c ` C ) T ) $=
      ( vf vg wcel cfv wbr wa cicrcl ex 3impib wi cv co wex eqid simpll adantl
      ccat ccic w3a cbs ciclcl jca anim12d ciso simpl simplr cic simprr anbi12d
      cop cco isoco brcici exlimiv com12 imp sylbid com23 mpd ) AUAGZBCAUBHZIZC
      DVEIZUCBAUDHZGZCVHGZJZDVHGZJZBDVEIZVDVFVGVMVDVFVKVGVLVDVFVKVDVFJVIVJABCUE
      ABCKUFLVDVGVLACDKLUGMVDVFVGVMVNNVDVMVFVGJZVNVDVMVOVNNVDVMJZVOEOZBCAUHHZPG
      ZEQZFOZCDVRPGZFQZJZVNVPVFVTVGWCVPVHAEVRBCVRRZVHRZVDVMUIZVMVIVDVIVJVLSTZVM
      VJVDVIVJVLUJTZUKVPVHAFVRCDWEWFWGWIVDVKVLULZUKUMWDVPVNVTWCVPVNNZVSWCWKNEWC
      VSWKWBVSWKNFWBVSWKWBVSJZVPVNWLVPJZVHAWAVQBCUNDAUOHZPPVRBDWEWFVPVDWLWGTZVP
      VIWLWHTZVPVLWLWJTZWMVHAWNVQWAVRBCDWFWNRWEWOWPVPVJWLWITWQWBVSVPUJWBVSVPSUP
      UQLLURUSURUTUSVALVBMVC $.

    $d C x y z $.  $d f x y $.
    $( Isomorphism is an equivalence relation on objects of a category.  Remark
       3.16 in [Adamek] p. 29.  (Contributed by AV, 5-Apr-2020.) $)
    cicer $p |- ( C e. Cat -> ( ~=c ` C ) Er ( Base ` C ) ) $=
      ( vx vy vz vf ccat wcel cbs cfv ccic wrel c0 cv wne a1i releqd mpbird cvv
      wceq wbr ciso csupp co cxp crab cop w3a copab relopabv fveq2 neeq1d rabxp
      wfn isofn fvex sqxpexg mp1i suppvalfn syl3anc cicfval cicsym cictr cicref
      0ex 3expb ciclcl impbida iserd ) AFGZBCDAHIZAJIZVIVKKAUAIZLUBUCZKZVIVNEMZ
      VLIZLNZEVJVJUDZUEZKZVIVTBMZVJGZCMZVJGWAWCUFZVLIZLNZUGZBCUHZKZWIVIWGBCUIOV
      IVSWHVSWHSVIVQWFEBCVJVJVOWDSVPWELVOWDVLUJUKULOPQVIVMVSVIVLVRUMVRRGZLRGZVM
      VSSAUNVJRGWJVIAHUOVJRUPUQWKVIVDOEVLRRVRLURUSPQVIVKVMAUTPQAWAWCVAVIWAWCVKT
      WCDMZVKTWAWLVKTAWAWCWLVBVEVIWBWAWAVKTAWAVCAWAWAVFVGVH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Subcategories
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c C_cat $.
  $c |`cat $.
  $c Subcat $.

  $( Extend class notation to include the subset relation for subcategories. $)
  cssc $a class C_cat $.

  $( Extend class notation to include category restriction (which is like
     structure restriction but also allows limiting the collection of
     morphisms). $)
  cresc $a class |`cat $.

  $( Extend class notation to include the collection of subcategories of a
     category. $)
  csubc $a class Subcat $.

  ${
    $d c f g h j s t x y z $.  $d h j s t x H $.  $d h j s t x J $.
    $( Define the subset relation for subcategories.  Despite the name, this is
       not really a "category-aware" definition, which is to say it makes no
       explicit references to homsets or composition; instead this is a
       subset-like relation on the functions that are used as subcategory
       specifications in ~ df-subc , which makes it play an analogous role to
       the subset relation applied to the subgroups of a group.  (Contributed
       by Mario Carneiro, 6-Jan-2017.) $)
    df-ssc $a |- C_cat = { <. h , j >. | E. t ( j Fn ( t X. t ) /\
      E. s e. ~P t h e. X_ x e. ( s X. s ) ~P ( j ` x ) ) } $.

    $( Define the restriction of a category to a given set of arrows.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    df-resc $a |- |`cat = ( c e. _V , h e. _V |->
      ( ( c |`s dom dom h ) sSet <. ( Hom ` ndx ) , h >. ) ) $.

    $( ` ( Subcat `` C ) ` is the set of all the subcategory specifications of
       the category ` C ` .  Like ~ df-subg , this is not actually a collection
       of categories (as in definition 4.1(a) of [Adamek] p. 48), but only sets
       which when given operations from the base category (using ~ df-resc )
       form a category.  All the objects and all the morphisms of the
       subcategory belong to the supercategory.  The identity of an object, the
       domain and the codomain of a morphism are the same in the subcategory
       and the supercategory.  The composition of the subcategory is a
       restriction of the composition of the supercategory.  (Contributed by
       FL, 17-Sep-2009.)  (Revised by Mario Carneiro, 4-Jan-2017.) $)
    df-subc $a |- Subcat = ( c e. Cat |-> { h | ( h C_cat ( Homf ` c ) /\
      [. dom dom h / s ]. A. x e. s ( ( ( Id ` c ) ` x ) e. ( x h x ) /\
        A. y e. s A. z e. s A. f e. ( x h y ) A. g e. ( y h z )
          ( g ( <. x , y >. ( comp ` c ) z ) f ) e. ( x h z ) ) ) } ) $.

    $( The subcategory subset relation is a relation.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    sscrel $p |- Rel C_cat $=
      ( vj vt vh vx vs cxp wfn cfv cpw cixp wcel wrex wex cssc df-ssc relopabiv
      cv wa ) AQZBQZTFGCQDEQZUAFDQSHIJKETILRBMCANDBCAEOP $.

    $( The subcategory subset relation is a relation.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    brssc $p |- ( H C_cat J <-> E. t ( J Fn ( t X. t ) /\
        E. s e. ~P t H e. X_ x e. ( s X. s ) ~P ( J ` x ) ) ) $=
      ( vj vh cssc cvv wcel wa cv cxp wfn cfv cpw cixp wrex wex wceq wbr sscrel
      brrelex12i vex xpex fnex mpan2 elex rexlimivw anim12ci simpr fneq1d simpl
      exlimiv fveq1d ixpeq2dv eleq12d rexbidv anbi12d exbidv df-ssc pm5.21nii
      pweqd brabga ) CDHUACIJZDIJZKZDBLZVHMZNZCAELZVKMZALZDOZPZQZJZEVHPZRZKZBSZ
      CDHUBUCVTVGBVJVFVSVEVJVIIJVFVHVHBUDZWBUEVIIDUFUGVQVEEVRCVPUHUIUJUNFLZVINZ
      GLZAVLVMWCOZPZQZJZEVRRZKZBSWAGFCDHIIWECTZWCDTZKZWKVTBWNWDVJWJVSWNVIWCDWLW
      MUKZULWNWIVQEVRWNWECWHVPWLWMUMWNAVLWGVOWNWFVNWNVMWCDWOUOVCUPUQURUSUTABGFE
      VAVDVB $.

    $( An analogue of ~ pwex for the subcategory subset relation:  The
       collection of subcategory subsets of a given set ` J ` is a set.
       (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    sscpwex $p |- { h | h C_cat J } e. _V $=
      ( vt vx vs cv cssc wbr cab crn cuni cpw cpm cxp cixp wcel wa cvv wss vex
      cdm co ovex wfn cfv wrex wex brssc wf simpl xpex fnex sylancl rnexg pwexg
      uniexg 4syl wceq adantr eqeltrdi ss2ixp fvssunirn sspwi a1i simprr sselid
      fndm mprg elixpconst sylib elpwi ad2antrl xpss12 sseqtrrd elpm2r syl22anc
      syl2anc rexlimdvaa imp exlimiv sylbi abssi ssexi ) AFZBGHZAIBJZKZLZBUAZMU
      BZWHWIMUCWEAWJWEBCFZWKNZUDZWDDEFZWNNZDFZBUEZLZOZPZEWKLZUFZQZCUGWDWJPZDCWD
      BEUHXCXDCWMXBXDWMWTXDEXAWMWNXAPZWTQZQZWHRPZWIRPWOWHWDUIZWOWISXDXGBRPZWFRP
      WGRPXHXGWMWLRPXJWMXFUJWKWKCTZXKUKZWLRBULUMBRUNWFRUPWGRUOUQXGWIWLRWMWIWLUR
      XFWLBVGUSZXLUTXGWDDWOWHOZPXIXGWSXNWDWRWHSZWSXNSDWODWOWRWHVAXOWPWOPWQWGBWP
      VBVCVDVHWMXEWTVEVFDWOWHWDATVIVJXGWOWLWIXGWNWKSZXPWOWLSXEXPWMWTWNWKVKVLZXQ
      WNWKWNWKVMVQXMVNWHWIWOWDRRVOVPVRVSVTWAWBWC $.

    $( Reverse closure for the subcategory predicate.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    subcrcl $p |- ( H e. ( Subcat ` C ) -> C e. Cat ) $=
      ( vc vh vx vg vf vy vz vs ccat cv chomf cfv cssc co wcel wral wa cdm ccid
      wbr cop cco wsbc cab csubc df-subc mptrcl ) CKDLZCLZMNOUBELZUKUANNULULUJP
      QFLGLULHLZUCILZUKUDNPPULUNUJPQFUMUNUJPRGULUMUJPRIJLZRHUORSEUORJUJTTUESDUF
      UGBAEHIGFDJCUHUI $.
  $}

  ${
    $d s t x y H $.  $d s t x y J $.  $d s t ph $.  $d s t S $.  $d t T $.
    sscfn1.1 $e |- ( ph -> H C_cat J ) $.
    ${
      sscfn1.2 $e |- ( ph -> S = dom dom H ) $.
      $( The subcategory subset relation is defined on functions with square
         domain.  (Contributed by Mario Carneiro, 6-Jan-2017.) $)
      sscfn1 $p |- ( ph -> H Fn ( S X. S ) ) $=
        ( vt vx vs cv cxp wfn cfv cpw cixp wcel wrex wa cdm wceq wex cssc brssc
        sylib ixpfn simpr adantr fndm adantl dmeqd dmxpid eqtrdi eqtr2d sqxpeqd
        wbr fneq2d mpbid ex syl5 rexlimdvw adantld exlimdv mpd ) ADGJZVDKLZCHIJ
        ZVFKZHJDMNZOPZIVDNZQZRZGUAZCBBKZLZACDUBUOVMEHGCDIUCUDAVLVOGAVKVOVEAVIVO
        IVJVICVGLZAVOHVGVHCUEAVPVOAVPRZVPVOAVPUFVQVGVNCVQVFBVQBCSZSZVFABVSTVPFU
        GVQVSVGSVFVQVRVGVPVRVGTAVGCUHUIUJVFUKULUMUNUPUQURUSUTVAVBVC $.
    $}

    ${
      sscfn2.2 $e |- ( ph -> T = dom dom J ) $.
      $( The subcategory subset relation is defined on functions with square
         domain.  (Contributed by Mario Carneiro, 6-Jan-2017.) $)
      sscfn2 $p |- ( ph -> J Fn ( T X. T ) ) $=
        ( vt vx vy cv cxp wfn cfv cpw cixp wcel wrex wa cdm wceq wex cssc brssc
        wbr sylib simpr adantr adantl dmeqd dmxpid eqtrdi eqtr2d sqxpeqd fneq2d
        fndm mpbid ex adantrd exlimdv mpd ) ADGJZVAKZLZCHIJZVDKHJDMNOPIVANQZRZG
        UAZDBBKZLZACDUBUDVGEHGCDIUCUEAVFVIGAVCVIVEAVCVIAVCRZVCVIAVCUFVJVBVHDVJV
        ABVJBDSZSZVAABVLTVCFUGVJVLVBSVAVJVKVBVCVKVBTAVBDUOUHUIVAUJUKULUMUNUPUQU
        RUSUT $.
    $}
  $}

  ${
    $d s t x y z H $.  $d s t x y z J $.  $d s t ph $.  $d s x y z S $.
    $d s t T $.
    isssc.1 $e |- ( ph -> H Fn ( S X. S ) ) $.
    $( Lemma for ~ ssc1 and similar theorems.  (Contributed by Mario Carneiro,
       6-Jan-2017.) $)
    ssclem $p |- ( ph -> ( H e. _V <-> S e. _V ) ) $=
      ( cvv wcel wa cxp cdm dmxpid fndmd adantr dmexg adantl eqeltrrd eqeltrrid
      wceq dmexd wfn sqxpexg fnex syl2an impbida ) ACEFZBEFZAUDGZBBBHZIEBJUFUGE
      UFCIZUGEAUHUGQUDAUGCDKLUDUHEFACEMNORPACUGSUGEFUDUEDBETUGECUAUBUC $.

    isssc.2 $e |- ( ph -> J Fn ( T X. T ) ) $.
    ${
      isssc.3 $e |- ( ph -> T e. V ) $.
      $( Value of the subcategory subset relation when the arguments are known
         functions.  (Contributed by Mario Carneiro, 6-Jan-2017.) $)
      isssc $p |- ( ph -> ( H C_cat J <-> ( S C_ T /\
        A. x e. S A. y e. S ( x H y ) C_ ( x J y ) ) ) ) $=
        ( vz vs vt cv wcel wceq wa wex cdm cssc wbr cxp cfv cpw cixp wss co wfn
        wrex wral brssc fndm adantl adantr fndmd eqtr3d dmeqd dmxpid 3eqtr3g ex
        id sqxpeqd fneq2d syl5ibrcom impbid anbi1d exbidv pweq rexeqdv ceqsexgv
        bitrid wb syl bitrd df-rex cvv w3a 3anass elixp2 vex xpex fnex pm4.71ri
        mpan2 3bitr4i anbi2d an12 bitrdi exsimpl isset sylibr a1i ssexg adantrd
        wi expcom elpw sseq1 raleqdv cop fvex fveq2 df-ov eqtr4di sseq12d ralxp
        anbi12d pm5.21ndd 3bitrd ) AFGUAUBZFLMOZXLUCZLOZGUDZUEZUFPZMEUEZUJZXLDQ
        ZXLXRPZXNFUDZXPPZLXMUKZRZRZMSZDEUGZBOZCOZFUHZYIYJGUHZUGZCDUKBDUKZRZAXKN
        OZEQZXQMYPUEZUJZRZNSZXSXKGYPYPUCZUIZYSRZNSAUUALNFGMULAUUDYTNAUUCYQYSAUU
        CYQAUUCYQAUUCRZUUBTEEUCZTYPEUUEUUBUUFUUEGTZUUBUUFUUCUUGUUBQAUUBGUMUNUUE
        UUFGAGUUFUIZUUCJUOUPUQURYPUSEUSUTVAAUUCYQUUHJYQUUBUUFGYQYPEYQVBVCVDVEVF
        VGVHVLAEHPZUUAXSVMKYSXSNEHYQXQMYRXRYPEVIVJVKVNVOXSYAXQRZMSAYGXQMXRVPAUU
        JYFMAUUJYAXTYDRZRYFAXQUUKYAXQFXMUIZYDRZAUUKFVQPZUULYDVRUUNUUMRXQUUMUUNU
        ULYDVSLXMXPFVTUUMUUNUULUUNYDUULXMVQPUUNXLXLMWAZUUOWBXMVQFWCWEUOWDWFAUUL
        XTYDAUULXTAUULXTAUULRZXMTDDUCZTXLDUUPXMUUQUUPFTZXMUUQUULUURXMQAXMFUMUNU
        UPUUQFAFUUQUIZUULIUOUPUQURXLUSDUSUTVAAUULXTUUSIXTXMUUQFXTXLDXTVBVCZVDVE
        VFVGVLWGYAXTYDWHWIVHVLADVQPZYGYOYGUVAWPAYGXTMSUVAXTYEMWJMDWKWLWMAYHUVAY
        NAUUIYHUVAWPKYHUUIUVADEHWNWQVNWOUVAYGYOVMWPAYEYOMDVQXTYAYHYDYNYAXLEUGXT
        YHXLEUUOWRXLDEWSVLXTYDYCLUUQUKYNXTYCLXMUUQUUTWTYCYMLBCDDYCYBXOUGXNYIYJX
        AZQZYMYBXOXNFXBWRUVCYBYKXOYLUVCYBUVBFUDYKXNUVBFXCYIYJFXDXEUVCXOUVBGUDYL
        XNUVBGXCYIYJGXDXEXFVLXGWIXHVKWMXIXJ $.
    $}

    ssc1.3 $e |- ( ph -> H C_cat J ) $.
    $( Infer subset relation on objects from the subcategory subset relation.
       (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    ssc1 $p |- ( ph -> S C_ T ) $=
      ( vx vy wss cv co wral cssc wbr wa cvv wcel mpbid sscrel brrelex2i ssclem
      syl isssc simpld ) ABCKZILZJLZDMUHUIEMKJBNIBNZADEOPZUGUJQHAIJBCDERFGAERSZ
      CRSAUKULHDEOUAUBUDACEGUCTUETUF $.
  $}

  ${
    $d x y H $.  $d x y J $.  $d x y S $.  $d x y X $.  $d y Y $.
    ssc2.1 $e |- ( ph -> H Fn ( S X. S ) ) $.
    ssc2.2 $e |- ( ph -> H C_cat J ) $.
    ssc2.3 $e |- ( ph -> X e. S ) $.
    ssc2.4 $e |- ( ph -> Y e. S ) $.
    $( Infer subset relation on morphisms from the subcategory subset relation.
       (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    ssc2 $p |- ( ph -> ( X H Y ) C_ ( X J Y ) ) $=
      ( vx vy wcel cv co wss wral cdm cssc cvv wa eqidd sscfn2 sscrel brrelex2i
      dmexg 4syl isssc mpbid simprd wceq oveq1 sseq12d oveq2 rspc2va syl21anc
      wbr ) AEBMFBMKNZLNZCOZURUSDOZPZLBQKBQZEFCOZEFDOZPZIJABDRZRZPZVCACDSUQZVIV
      CUAHAKLBVHCDTGAVHCDHAVHUBUCAVJDTMVGTMVHTMHCDSUDUEDTUFVGTUFUGUHUIUJVBVFEUS
      COZEUSDOZPKLEFBBUREUKUTVKVAVLUREUSCULUREUSDULUMUSFUKVKVDVLVEUSFECUNUSFEDU
      NUMUOUP $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y H $.  $d x y S $.
    $d x y T $.
    $( Any function restricted to a square domain is a subcategory subset of
       the original.  (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    sscres $p |- ( ( H Fn ( S X. S ) /\ S e. V ) ->
      ( H |` ( T X. T ) ) C_cat H ) $=
      ( vx vy cxp wfn wcel wa cres cin wss cv co wral inss1 wceq simpl elin2d
      cssc wbr simpr ovresd eqimss pm3.2i fnssres sylancl resres fnresdm adantr
      syl rgen2 reseq1d eqtr3id inxp a1i fneq12d mpbid isssc mpbiri ) CAAGZHZAD
      IZJZCBBGZKZCUAUBABLZAMZENZFNZVGOZVJVKCOZMZFVHPEVHPZJVIVOABQVNEFVHVHVJVHIZ
      VKVHIZJZVLVMRVNVRVJVKCBVRABVJVPVQSTVRABVKVPVQUCTUDVLVMUEULUMUFVEEFVHAVGCD
      VECVBVFLZKZVSHZVGVHVHGZHVEVCVSVBMWAVCVDSZVBVFQVBVSCUGUHVEVSWBVTVGVEVTCVBK
      ZVFKVGCVBVFUIVEWDCVFVCWDCRVDVBCUJUKUNUOVSWBRVEAABBUPUQURUSWCVCVDUCUTVA $.

    $( The subcategory subset relation is reflexive.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    sscid $p |- ( ( H Fn ( S X. S ) /\ S e. V ) -> H C_cat H ) $=
      ( cxp wfn wcel wa cres cssc wceq fnresdm adantr sscres eqbrtrrd ) BAADZEZ
      ACFZGBOHZBBIPRBJQOBKLAABCMN $.

    $( The subcategory subset relation is transitive.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    ssctr $p |- ( ( A C_cat B /\ B C_cat C ) -> A C_cat C ) $=
      ( vx vy cssc wbr wa cdm wss cv co wral eqidd sscfn2 ssc1 sstrd adantr cvv
      wcel simpl sscfn1 simpr cxp wfn simprl simprr sseldd ralrimivva brrelex2i
      ssc2 sscrel adantl dmexg 3syl isssc mpbir2and ) ABFGZBCFGZHZACFGAIIZCIZIZ
      JDKZEKZALZVDVECLZJZEVAMDVAMUTVABIIZVCUTVAVIABUTVAABURUSUAZUTVANUBZUTVIABV
      JUTVINOZVJPZUTVIVCBCVLUTVCBCURUSUCZUTVCNOZVNPQUTVHDEVAVAUTVDVATZVEVATZHZH
      ZVFVDVEBLVGVSVAABVDVEUTAVAVAUDUEVRVKRUTURVRVJRUTVPVQUFZUTVPVQUGZUKVSVIBCV
      DVEUTBVIVIUDUEVRVLRUTUSVRVNRVSVAVIVDUTVAVIJVRVMRZVTUHVSVAVIVEWBWAUHUKQUIU
      TDEVAVCACSVKVOUTCSTZVBSTVCSTUSWCURBCFULUJUMCSUNVBSUNUOUPUQ $.

    $( The subcategory subset relation is antisymmetric.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    ssceq $p |- ( ( A C_cat B /\ B C_cat A ) -> A = B ) $=
      ( vx vy cssc wbr wa wceq cdm cxp cv wral eqidd sscfn1 ssc1 eqssd wcel wfn
      co adantr simpl simpr sqxpeqd simprl simprr ssc2 wss sseldd ralrimivva wb
      eqfnov syl2anc mpbir2and ) ABEFZBAEFZGZABHZAIIZURJZBIIZUTJZHZCKZDKZASZVCV
      DBSZHZDURLCURLZUPURUTUPURUTUPURUTABUPURABUNUOUAZUPURMNZUPUTBAUNUOUBZUPUTM
      NZVIOZUPUTURBAVLVJVKOPUCUPVGCDURURUPVCURQZVDURQZGZGZVEVFVQURABVCVDUPAUSRZ
      VPVJTUPUNVPVITUPVNVOUDZUPVNVOUEZUFVQUTBAVCVDUPBVARZVPVLTUPUOVPVKTVQURUTVC
      UPURUTUGVPVMTZVSUHVQURUTVDWBVTUHUFPUIUPVRWAUQVBVHGUJVJVLCDURURUTUTABUKULU
      M $.
  $}

  ${
    $d c h C $.  $d c h H $.
    rescval.1 $e |- D = ( C |`cat H ) $.
    $( Value of the category restriction.  (Contributed by Mario Carneiro,
       4-Jan-2017.) $)
    rescval $p |- ( ( C e. V /\ H e. W ) -> D =
      ( ( C |`s dom dom H ) sSet <. ( Hom ` ndx ) , H >. ) ) $=
      ( vc vh wcel wa cresc co cdm cress cop csts cvv wceq elex cv cnx chom cfv
      simpl simpr dmeqd oveq12d opeq2d df-resc ovex ovmpoa syl2an eqtrid ) ADIZ
      CEIZJBACKLZACMZMZNLZUAUBUCZCOZPLZFUNAQICQIUPVBRUOADSCESGHACQQGTZHTZMZMZNL
      ZUTVDOZPLVBKVCARZVDCRZJZVGUSVHVAPVKVCAVFURNVIVJUDVKVEUQVKVDCVIVJUEZUFUFUG
      VKVDCUTVLUHUGHGUIUSVAPUJUKULUM $.

    rescval2.1 $e |- ( ph -> C e. V ) $.
    rescval2.2 $e |- ( ph -> S e. W ) $.
    rescval2.3 $e |- ( ph -> H Fn ( S X. S ) ) $.
    $( Value of the category restriction.  (Contributed by Mario Carneiro,
       4-Jan-2017.) $)
    rescval2 $p |- ( ph ->
      D = ( ( C |`s S ) sSet <. ( Hom ` ndx ) , H >. ) ) $=
      ( cdm cress co cnx chom csts wcel cvv syl2anc cfv cop wceq cxp xpexd fnex
      wfn rescval fndmd dmeqd dmxpid eqtrdi oveq2d oveq1d eqtrd ) ACBELZLZMNZOP
      UAEUBZQNZBDMNZUSQNABFRESRZCUTUCIAEDDUDZUGVCSRVBKADDGGJJUEVCSEUFTBCEFSHUHT
      AURVAUSQAUQDBMAUQVCLDAUPVCAVCEKUIUJDUKULUMUNUO $.
  $}

  ${
    $d x y D $.
    rescbas.d $e |- D = ( C |`cat H ) $.
    rescbas.b $e |- B = ( Base ` C ) $.
    rescbas.c $e |- ( ph -> C e. V ) $.
    rescbas.h $e |- ( ph -> H Fn ( S X. S ) ) $.
    rescbas.s $e |- ( ph -> S C_ B ) $.
    $( Base set of the category restriction.  (Contributed by Mario Carneiro,
       4-Jan-2017.)  (Proof shortened by AV, 18-Oct-2024.) $)
    rescbas $p |- ( ph -> S = ( Base ` D ) ) $=
      ( cress co cbs cfv cnx wne syl cvv chom cop baseid cco slotsbhcdif simp1i
      csts setsnid wceq eqid ressbas2 wcel fvexi ssex rescval2 fveq2d 3eqtr4a
      wss ) ACEMNZOPZUSQUAPZFUBUGNZOPEDOPFVAOUSUCQOPZVARVCQUDPZRVAVDRUEUFUHAEBU
      RZEUTUILEBUSCUSUJIUKSADVBOACDEFGTHJAVEETULLEBBCOIUMUNSKUOUPUQ $.

    $( Hom-sets of the category restriction.  (Contributed by Mario Carneiro,
       4-Jan-2017.) $)
    reschom $p |- ( ph -> H = ( Hom ` D ) ) $=
      ( cress co cnx chom cfv cop cvv wcel csts wceq ovex cxp wfn wss cbs fvexi
      ssex syl xpexd fnex syl2anc homid setsid sylancr rescval2 fveq2d eqtr4d )
      AFCEMNZOPQFRUANZPQZDPQAUTSTFSTZFVBUBCEMUCAFEEUDZUEVDSTVCKAEESSAEBUFESTLEB
      BCUGIUHUIUJZVEUKVDSFULUMSFPSUTUNUOUPADVAPACDEFGSHJVEKUQURUS $.

    $( Hom-sets of the category restriction.  (Contributed by Mario Carneiro,
       4-Jan-2017.) $)
    reschomf $p |- ( ph -> H = ( Homf ` D ) ) $=
      ( vx vy cbs cfv cv cxp wfn eqid chom co cmpo reschom wceq rescbas sqxpeqd
      chomf fneq12d mpbid fnov sylib eqtrd homffval eqtr4di ) AFMNDOPZUPMQNQDUA
      PZUBUCZDUHPZAFUQURABCDEFGHIJKLUDZAUQUPUPRZSZUQURUEAFEERZSVBKAVCVAFUQUTAEU
      PABCDEFGHIJKLUFUGUIUJMNUPUPUQUKULUMMNUPDUSUQUSTUPTUQTUNUO $.

    rescco.o $e |- .x. = ( comp ` C ) $.
    $( Composition in the category restriction.  (Contributed by Mario
       Carneiro, 4-Jan-2017.)  (Proof shortened by AV, 13-Oct-2024.) $)
    rescco $p |- ( ph -> .x. = ( comp ` D ) ) $=
      ( co cco cfv cnx wne cvv cress chom cop csts ccoid cbs slotsbhcdif necomd
      w3a simp3 ax-mp setsnid wcel wceq wss fvexi ssex syl eqid ressco rescval2
      fveq2d 3eqtr4a ) ACEUAOZPQZVDRUBQZGUCUDOZPQFDPQGVFPVDUERUFQZVFSZVHRPQZSZV
      FVJSZUIZVJVFSUGVMVFVJVIVKVLUJUHUKULAETUMZFVEUNAEBUOVNMEBBCUFJUPUQURZECVDF
      TVDUSNUTURADVGPACDEGHTIKVOLVAVBVC $.
  $}

  ${
    rescabs.c $e |- ( ph -> C e. V ) $.
    rescabs.h $e |- ( ph -> H Fn ( S X. S ) ) $.
    rescabs.j $e |- ( ph -> J Fn ( T X. T ) ) $.
    rescabs.s $e |- ( ph -> S e. W ) $.
    rescabs.t $e |- ( ph -> T C_ S ) $.
    $( Restriction absorption law.  (Contributed by Mario Carneiro,
       6-Jan-2017.)  (Proof shortened by AV, 9-Nov-2024.) $)
    rescabs $p |- ( ph -> ( ( C |`cat H ) |`cat J ) = ( C |`cat J ) ) $=
      ( cress co csts cvv eqid wceq wcel cnx cfv cop cresc ovexd ssexd rescval2
      cbs wss wa simpr adantr baseid wne cco slotsbhcdif simp1i setsnid ressid2
      chom syl3anc oveq1d ovex cxp xpexd setsabs sylancr cin ressbas syl sseq1d
      fnexd biimpar inss2 ssind ssrind eqssd oveq2d ressinbas 3eqtr4d 3eqtrd wn
      ressval2 necomi fvex inex2 setscom syl22anc ressabs syl2an2r eqtr3d eqtrd
      a1i pm2.61dan ) ABCNOZUAUTUBZEUCZPOZFUDOZBDNOZWPFUCZPOZBEUDOZFUDOBFUDOZAW
      SWRDNOZXAPOZXBAWRWSDFQQWSRAWOWQPUEADCHLMUFZKUGAWOUHUBZDUIZXFXBSAXIUJZXFWR
      XAPOZWOXAPOZXBXJXEWRXAPXJXIWRQTZDQTZXEWRSAXIUKXJWOWQPUEAXNXIXGULZDXHXEWRQ
      QXERZEWPUHWOUMUAUHUBZWPUNXQUAUOUBZUNWPXRUNUPUQZURZUSVAVBXJWOQTZFQTZXKXLSB
      CNVCAYBXIADDVDFQKADDQQXGXGVEVLZULWPEFWOQQVFVGXJWOWTXAPXJBCBUHUBZVHZNOZBDY
      DVHZNOZWOWTXJYEYGBNXJYEYGXJYEDYDAYEDUIXIAYEXHDACHTZYEXHSLCYDWOHBWORYDRZVI
      VJVKVMYEYDUIXJCYDVNWMVOXJDCYDADCUIZXIMULVPVQVRXJYIWOYFSAYIXILULCYDBHYJVSV
      JXJXNWTYHSXODYDBQYJVSVJVTVBWAAXIWBZUJZXFWTWQPOZXAPOZXBYMXEYNXAPYMXEWRXQDX
      HVHZUCZPOZWOYQPOZWQPOZYNYMYLXMXNXEYRSAYLUKZYMWOWQPUEAXNYLXGULZDXHXEWRQQXP
      XTWCVAYMYAWPXQUNZEQTZYPQTZYRYTSYMBCNUEZUUCYMXQWPXSWDWMAUUDYLACCVDEQJACCHH
      LLVEVLULUUEYMXHDWOUHWEWFWMWPXQEYPWOQQQUAUTWEUAUHWEWGWHYMYSWTWQPYMWODNOZYS
      WTYMYLYAXNUUGYSSUUAUUFUUBDXHUUGWOQQUUGRXHRWCVAAYIYLYKUUGWTSLAYKYLMULCDBHW
      IWJWKVBWAVBYMWTQTYBYOXBSBDNVCAYBYLYCULWPEFWTQQVFVGWLWNWLAXCWRFUDABXCCEGHX
      CRILJUGVBABXDDFGQXDRIXGKUGVT $.
  $}

  ${
    rescabs2.c $e |- ( ph -> C e. V ) $.
    rescabs2.j $e |- ( ph -> J Fn ( T X. T ) ) $.
    rescabs2.s $e |- ( ph -> S e. W ) $.
    rescabs2.t $e |- ( ph -> T C_ S ) $.
    $( Restriction absorption law.  (Contributed by Mario Carneiro,
       6-Jan-2017.) $)
    rescabs2 $p |- ( ph -> ( ( C |`s S ) |`cat J ) = ( C |`cat J ) ) $=
      ( cress co cnx chom csts cresc cvv eqid rescval2 cfv cop wcel wss ressabs
      wceq syl2anc oveq1d ovexd ssexd 3eqtr4d ) ABCLMZDLMZNOUAEUBZPMBDLMZUNPMUL
      EQMZBEQMZAUMUOUNPACGUCDCUDUMUOUFJKCDBGUEUGUHAULUPDERRUPSABCLUIADCGJKUJZIT
      ABUQDEFRUQSHURITUK $.
  $}

  ${
    $d c f g j s x y z C $.  $d c f g j s x y z J $.  $d c f g j s x y z S $.
    $d c j s .1. $.  $d c j H $.  $d c j s .x. $.
    issubc.h $e |- H = ( Homf ` C ) $.
    issubc.i $e |- .1. = ( Id ` C ) $.
    issubc.o $e |- .x. = ( comp ` C ) $.
    issubc.c $e |- ( ph -> C e. Cat ) $.
    ${
      issubc.s $e |- ( ph -> S = dom dom J ) $.
      $( Elementhood in the set of subcategories.  (Contributed by Mario
         Carneiro, 4-Jan-2017.) $)
      issubc $p |- ( ph -> ( J e. ( Subcat ` C ) <-> ( J C_cat H /\
         A. x e. S ( ( .1. ` x ) e. ( x J x ) /\ A. y e. S A. z e. S
          A. f e. ( x J y ) A. g e. ( y J z )
            ( g ( <. x , y >. .x. z ) f ) e. ( x J z ) ) ) ) ) $=
        ( vj wcel co vc vs ccat cdm wceq csubc cfv cssc wbr cv wral wa wb chomf
        cop ccid cco wsbc cab csb cvv simpl sscpwex ss2abi ssexi df-subc fvmpts
        csbex a1i syl2anc eleq2d sbcel2 wi sscrel brrelex1i adantr df-sbc simpr
        elex fveq2d eqtr4di breq12d vex dmex dmeqd simpllr eqtr4d fveq1d simplr
        oveqd eleq12d raleqbidv anbi12d sbcied2 adantlr sbcied bitr3id 3bitr2d
        ex pm5.21ndd ) AEUCSZFLUDZUDZUEZLEUFUGZSZLKUHUIZBUJZHUGZXHXHLTZSZJUJZIU
        JZXHCUJZUOZDUJZGTZTZXHXPLTZSZJXNXPLTZUKZIXHXNLTZUKZDFUKZCFUKZULZBFUKZUL
        ZUMPQXAXDULZXFLUAERUJZUAUJZUNUGZUHUIZXHYLUPUGZUGZXHXHYKTZSZXLXMXOXPYLUQ
        UGZTZTZXHXPYKTZSZJXNXPYKTZUKZIXHXNYKTZUKZDUBUJZUKZCUUHUKZULZBUUHUKZUBYK
        UDZUDZURZULZRUSZUTZSZLUUQSZUAEURZYIYJXEUURLYJXAUURVASZXEUURUEXAXDVBZUVB
        YJUAEUUQUUQYNRUSRYMVCUUPYNRYNUUOVBVDVEVHVIUAEUUQUCUFVABCDIJRUBUAVFVGVJV
        KUVAUUSUMYJUAELUUQVLVIYJUUTYIUAEUCUVCYJYLEUEZULZLVASZUUTYIUUTUVFVMUVELU
        UQVSVIYIUVFVMUVEXGUVFYHLKUHVNVOVPVIUVEUVFUUTYIUMUUTUUPRLURUVEUVFULZYIUU
        PRLVQUVGUUPYIRLVAUVEUVFVRUVEYKLUEZUUPYIUMUVFUVEUVHULZYNXGUUOYHUVIYKLYMK
        UHUVEUVHVRZUVEYMKUEUVHUVEYMEUNUGKUVEYLEUNYJUVDVRVTMWAVPWBUVIUULYHUBUUNF
        VAUUNVASUVIUUMYKRWCWDWDVIUVIUUNXCFUVIUUMXBUVIYKLUVJWEWEXAXDUVDUVHWFWGUV
        IUUHFUEZULZUUKYGBUUHFUVIUVKVRZUVLYRXKUUJYFUVLYPXIYQXJUVLXHYOHUVLYOEUPUG
        HUVLYLEUPYJUVDUVHUVKWFZVTNWAWHUVLYKLXHXHUVEUVHUVKWIZWJWKUVLUUIYECUUHFUV
        MUVLUUGYDDUUHFUVMUVLUUEYBIUUFYCUVLYKLXHXNUVOWJUVLUUCXTJUUDYAUVLYKLXNXPU
        VOWJUVLUUAXRUUBXSUVLYTXQXLXMUVLYSGXOXPUVLYSEUQUGGUVLYLEUQUVNVTOWAWJWJUV
        LYKLXHXPUVOWJWKWLWLWLWLWMWLWNWMWOWPWQWSWTWPWRVJ $.
    $}

    issubc2.a $e |- ( ph -> J Fn ( S X. S ) ) $.
    $( Elementhood in the set of subcategories.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    issubc2 $p |- ( ph -> ( J e. ( Subcat ` C ) <-> ( J C_cat H /\ A. x e. S
      ( ( .1. ` x ) e. ( x J x ) /\ A. y e. S A. z e. S A. f e. ( x J y )
        A. g e. ( y J z ) ( g ( <. x , y >. .x. z ) f ) e. ( x J z ) ) ) ) ) $=
      ( cdm cxp fndmd dmeqd dmxpid eqtr2di issubc ) ABCDEFGHIJKLMNOPALRZRFFSZRF
      AUEUFAUFLQTUAFUBUCUD $.
  $}

  ${
    $d f g x y z C $.
    $( For any category ` C ` , the empty set is a subcategory subset of
       ` C ` .  (Contributed by AV, 23-Apr-2020.) $)
    0ssc $p |- ( C e. Cat -> (/) C_cat ( Homf ` C ) ) $=
      ( vx vy ccat wcel c0 chomf cfv cssc wbr cbs wss wral 0ss a1i cxp wfn eqid
      cv co ral0 cvv wf ffn ax-mp xp0 fneq2i mpbir homffn fvexd isssc mpbir2and
      f0 ) ADEZFAGHZIJFAKHZLZBSZCSZFTURUSUOTLCFMZBFMZUQUNUPNOVAUNUTBUAOUNBCFUPF
      UOUBFFFPZQZUNVCFFQZFFFUCVDFUMFFFUDUEVBFFFUFUGUHOUOUPUPPQUNUPAUOUORUPRUIOU
      NAKUJUKUL $.

    $( For any category ` C ` , the empty set is a (full) subcategory of
       ` C ` , see example 4.3(1.a) in [Adamek] p. 48.  (Contributed by AV,
       23-Apr-2020.) $)
    0subcat $p |- ( C e. Cat -> (/) e. ( Subcat ` C ) ) $=
      ( vx vg vf vy vz ccat wcel c0 csubc cfv chomf cssc wbr cv co wral a1i wfn
      eqid ccid cop cco wa 0ssc id cxp wf f0 ffn ax-mp 0xp fneq2i mpbir issubc2
      ral0 mpbir2and ) AGHZIAJKHIALKZMNBOZAUAKZKUTUTIPHCODOUTEOZUBFOZAUCKZPPUTV
      CIPHCVBVCIPQDUTVBIPQFIQEIQUDZBIQZAUEVFURVEBUPRURBEFAIVDVADCUSIUSTVATVDTUR
      UFIIIUGZSZURVHIISZIIIUHVIIUIIIIUJUKVGIIIULUMUNRUOUQ $.

    $( For any category ` C ` , ` C ` itself is a (full) subcategory of ` C ` ,
       see example 4.3(1.b) in [Adamek] p. 48.  (Contributed by AV,
       23-Apr-2020.) $)
    catsubcat $p |- ( C e. Cat -> ( Homf ` C ) e. ( Subcat ` C ) ) $=
      ( vx vg vf vy vz wcel cfv cv co wral cbs wa wss ralrimivva eqid mpbir2and
      ssidd homfval adantr ccat chomf csubc cssc wbr cop cco cvv cxp wfn homffn
      ccid a1i fvexd isssc chom simpl catidcl eleqtrrd adantl wi eleq2d biimpcd
      simpr impcom biimpd adantld imp catcocl wceq jca ralrimiva id issubc2 ) A
      UAGZAUBHZAUCHGVPVPUDUEZBIZAULHZHZVRVRVPJZGZCIZDIZVREIZUFFIZAUGHZJJZVRWFVP
      JZGZCWEWFVPJZKDVRWEVPJZKZFALHZKEWNKZMZBWNKVOVQWNWNNWLWLNZEWNKBWNKVOWNRVOW
      QBEWNWNVOVRWNGZWEWNGZMMWLROVOBEWNWNVPVPUHVPWNWNUIUJVOWNAVPVPPZWNPZUKUMZXB
      VOALUNUOQVOWPBWNVOWRMZWBWOXCVTVRVRAUPHZJWAXCWNAVSXDVRXAXDPZVSPZVOWRUQZVOW
      RVDZURXCWNAVPXDVRVRWTXAXEXHXHSUSXCWMEFWNWNXCWSWFWNGZMZMZWJDCWLWKXKWDWLGZW
      CWKGZMZMZWHVRWFXDJZWIXOWNAWGWDWCXDVRWEWFXAXEWGPZXKVOXNXCVOXJXGTTXKWRXNXCW
      RXJXHTZTXKWSXNXJWSXCWSXIUQUTZTXKXIXNXJXIXCWSXIVDUTZTXNXKWDVRWEXDJZGZXLXKY
      BVAXMXKXLYBXKWLYAWDXKWNAVPXDVRWEWTXAXEXRXSSVBVCTVEXKXNWCWEWFXDJZGZXKXMYDX
      LXKXMYDXKWKYCWCXKWNAVPXDWEWFWTXAXEXSXTSVBVFVGVHVIXKWIXPVJXNXKWNAVPXDVRWFW
      TXAXEXRXTSTUSOOVKVLVOBEFAWNWGVSDCVPVPWTXFXQVOVMXBVNQ $.
  $}

  ${
    $d f g x y z C $.  $d f g x y z J $.  $d f g x y z ph $.
    subcixp.1 $e |- ( ph -> J e. ( Subcat ` C ) ) $.
    ${
      subcssc.h $e |- H = ( Homf ` C ) $.
      $( An element in the set of subcategories is a subset of the category.
         (Contributed by Mario Carneiro, 6-Jan-2017.) $)
      subcssc $p |- ( ph -> J C_cat H ) $=
        ( vx vg vf vy vz cssc cv cfv co wcel wral cdm wa eqid wbr cop cco csubc
        ccid ccat subcrcl syl eqidd issubc mpbid simpld ) ADCLUAZGMZBUENZNUNUND
        OPHMIMUNJMZUBKMZBUCNZOOUNUQDOPHUPUQDOQIUNUPDOQKDRRZQJUSQSGUSQZADBUDNPZU
        MUTSEAGJKBUSURUOIHCDFUOTURTAVABUFPEBDUGUHAUSUIUJUKUL $.
    $}

    subcfn.2 $e |- ( ph -> S = dom dom J ) $.
    $( An element in the set of subcategories is a binary function.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    subcfn $p |- ( ph -> J Fn ( S X. S ) ) $=
      ( chomf cfv eqid subcssc sscfn1 ) ACDBGHZABLDELIJFK $.
  $}

  ${
    subcss1.1 $e |- ( ph -> J e. ( Subcat ` C ) ) $.
    subcss1.2 $e |- ( ph -> J Fn ( S X. S ) ) $.
    ${
      subcss1.b $e |- B = ( Base ` C ) $.
      $( The objects of a subcategory are a subset of the objects of the
         original.  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
      subcss1 $p |- ( ph -> S C_ B ) $=
        ( chomf cfv cxp wfn eqid homffn a1i subcssc ssc1 ) ADBECIJZGRBBKLABCRRM
        ZHNOACREFSPQ $.
    $}

    ${
      subcss2.h $e |- H = ( Hom ` C ) $.
      subcss2.x $e |- ( ph -> X e. S ) $.
      subcss2.y $e |- ( ph -> Y e. S ) $.
      $( The morphisms of a subcategory are a subset of the morphisms of the
         original.  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
      subcss2 $p |- ( ph -> ( X J Y ) C_ ( X H Y ) ) $=
        ( co chomf cfv eqid subcssc ssc2 cbs sseldd subcss1 homfval sseqtrd ) A
        FGEMFGBNOZMFGDMACEUDFGIABUDEHUDPZQKLRABSOZBUDDFGUEUFPZJACUFFAUFBCEHIUGU
        AZKTACUFGUHLTUBUC $.
    $}
  $}

  ${
    $d f g x y z C $.  $d f g x y z F $.  $d f g x y z G $.  $d f g x y z ph $.
    $d f g x y z J $.  $d f g x y z S $.  $d f g x y z X $.  $d f g x y z Y $.
    $d x .1. $.  $d f g x y z .x. $.  $d f g x y z Z $.
    subcidcl.j $e |- ( ph -> J e. ( Subcat ` C ) ) $.
    subcidcl.2 $e |- ( ph -> J Fn ( S X. S ) ) $.
    subcidcl.x $e |- ( ph -> X e. S ) $.
    ${
      subcidcl.1 $e |- .1. = ( Id ` C ) $.
      $( The identity of the original category is contained in each
         subcategory.  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
      subcidcl $p |- ( ph -> ( .1. ` X ) e. ( X J X ) ) $=
        ( vx vg vf vy vz cv cfv co wcel wral wceq fveq2 id oveq12d eleq12d cssc
        chomf wbr cop cco wa csubc eqid ccat subcrcl issubc2 mpbid simpl ralimi
        syl simpl2im rspcdva ) AKPZDQZVCVCERZSZFDQZFFERZSKCFVCFUAZVDVGVEVHVCFDU
        BVIVCFVCFEVIUCZVJUDUEAEBUGQZUFUHZVFLPMPVCNPZUIOPZBUJQZRRVCVNERSLVMVNERT
        MVCVMERTOCTNCTZUKZKCTZVFKCTAEBULQSZVLVRUKGAKNOBCVODMLVKEVKUMJVOUMAVSBUN
        SGBEUOUTHUPUQVQVFKCVFVPURUSVAIVB $.
    $}

    subccocl.o $e |- .x. = ( comp ` C ) $.
    subccocl.y $e |- ( ph -> Y e. S ) $.
    subccocl.z $e |- ( ph -> Z e. S ) $.
    subccocl.f $e |- ( ph -> F e. ( X J Y ) ) $.
    subccocl.g $e |- ( ph -> G e. ( Y J Z ) ) $.
    $( A subcategory is closed under composition.  (Contributed by Mario
       Carneiro, 4-Jan-2017.) $)
    subccocl $p |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) e. ( X J Z ) ) $=
      ( co wcel vx vg vf vy vz cv ccid cfv cop wral wa chomf cssc wbr eqid ccat
      csubc subcrcl issubc2 mpbid simprd wceq adantr ad2antrr ad3antrrr simpllr
      syl simplr oveq12d eleqtrrd ad4antr simp-5r simp-4r opeq12d simpr eleq12d
      oveq123d rspcdv rspcimdv adantld mpd ) AUAUFZBUGUHZUHWBWBGSTZUBUFZUCUFZWB
      UDUFZUIZUEUFZDSZSZWBWIGSZTZUBWGWIGSZUJZUCWBWGGSZUJZUECUJZUDCUJZUKZUACUJZF
      EHIUIZJDSZSZHJGSZTZAGBULUHZUMUNZXAAGBUQUHTZXHXAUKKAUAUDUEBCDWCUCUBXGGXGUO
      WCUONAXIBUPTKBGURVGLUSUTVAAWTXFUAHCMAWBHVBZUKZWSXFWDXKWRXFUDICAICTXJOVCXK
      WGIVBZUKZWQXFUEJCAJCTXJXLPVDXMWIJVBZUKZWOXFUCEWPXOEHIGSZWPAEXPTXJXLXNQVEX
      OWBHWGIGAXJXLXNVFXKXLXNVHVIVJXOWFEVBZUKZWMXFUBFWNXRFIJGSZWNAFXSTXJXLXNXQR
      VKXRWGIWIJGXKXLXNXQVFXMXNXQVHVIVJXRWEFVBZUKZWKXDWLXEYAWEFWFEWJXCYAWHXBWIJ
      DYAWBHWGIAXJXLXNXQXTVLZXKXLXNXQXTVMVNXMXNXQXTVFZVIXRXTVOXOXQXTVHVQYAWBHWI
      JGYBYCVIVPVRVSVSVSVTVSWA $.
  $}

  ${
    $d f g h w x y z C $.  $d g h x y z D $.  $d f g h w x y z ph $.  $d x X $.
    $d f g h w x y z .1. $.  $d f g h w x y z J $.  $d f g h w x y z S $.
    subccat.1 $e |- D = ( C |`cat J ) $.
    subccat.j $e |- ( ph -> J e. ( Subcat ` C ) ) $.
    ${
      subccatid.1 $e |- ( ph -> J Fn ( S X. S ) ) $.
      subccatid.2 $e |- .1. = ( Id ` C ) $.
      $( A subcategory is a category.  (Contributed by Mario Carneiro,
         4-Jan-2017.) $)
      subccatid $p |- ( ph ->
        ( D e. Cat /\ ( Id ` D ) = ( x e. S |-> ( .1. ` x ) ) ) ) $=
        ( cv wcel wa co cfv ccat eqid adantr sseldd vw vy vz vf w3a cco cvv cbs
        vg vh csubc subcrcl syl subcss1 rescbas reschom rescco cresc ovexi biid
        a1i cxp wfn simpr subcidcl chom simpr1l simpr1r subcss2 simpr31 simpr2l
        wss catlid simpr32 catrid subccocl simpr2r simpr33 catass iscatd2 ) AUA
        LZEMZBLZEMZNZUBLZEMZUCLZEMZNZUDLZWAWCGOZMZUILZWCWFGOZMZUJLZWFWHGOZMZUEZ
        UEZUABUBUCEDCUFPZWCFPUDUIUJGUGACUHPZCDEGQHXCRZAGCUKPMZCQMZICGULUMZJAXCC
        EGIJXDUNZUOAXCCDEGQHXDXGJXHUPAXCCDEXBGQHXDXGJXHXBRZUQDUGMADCGURHUSVAXAU
        TAWDNCEFGWCAXEWDISAGEEVBVCZWDJSAWDVDKVEAXANZXCCXBFWKCVFPZWAWCXDXLRZKAXF
        XAXGSZXKEXCWAAEXCVLXAXHSZWBWDWJWTAVGZTZXIXKEXCWCXOWBWDWJWTAVHZTZXKWLWAW
        CXLOWKXKCEXLGWAWCAXEXAISZAXJXAJSZXMXPXRVIWMWPWSWEWJAVJZTZVMXKXCCXBFWNXL
        WCWFXDXMKXNXSXIXKEXCWFXOWGWIWEWTAVKZTZXKWOWCWFXLOWNXKCEXLGWCWFXTYAXMXRY
        DVIWMWPWSWEWJAVNZTZVOXKCEXBWKWNGWAWCWFXTYAXPXIXRYDYBYFVPXKXCCXBWKWNXLWQ
        WHWAWCWFXDXMXIXNXQXSYEYCYGXKEXCWHXOWGWIWEWTAVQZTXKWRWFWHXLOWQXKCEXLGWFW
        HXTYAXMYDYHVIWMWPWSWEWJAVRTVSVT $.

      subcid.x $e |- ( ph -> X e. S ) $.
      $( The identity in a subcategory is the same as the original category.
         (Contributed by Mario Carneiro, 4-Jan-2017.) $)
      subcid $p |- ( ph -> ( .1. ` X ) = ( ( Id ` D ) ` X ) ) $=
        ( vx ccid cfv cv cvv ccat wcel wceq subccatid simprd simpr fveq2d fvexd
        cmpt wa fvmptd eqcomd ) AGCNOZOGEOZAMGMPZEOZUKDUJQACRSUJMDUMUFTAMBCDEFH
        IJKUAUBAULGTZUGULGEAUNUCUDLAGEUEUHUI $.
    $}

    $( A subcategory is a category.  (Contributed by Mario Carneiro,
       4-Jan-2017.) $)
    subccat $p |- ( ph -> D e. Cat ) $=
      ( vx ccat wcel ccid cfv cdm cmpt wceq eqidd subcfn eqid subccatid simpld
      cv ) ACHICJKGDLLZGTBJKZKMNAGBCUAUBDEFABUADFAUAOPUBQRS $.
  $}

  ${
    $d f g x y z C $.  $d f g x y z D $.  $d f g x y z H $.  $d f g x y z ph $.
    $d f g x y z J $.  $d f g x y z S $.
    issubc3.h $e |- H = ( Homf ` C ) $.
    issubc3.i $e |- .1. = ( Id ` C ) $.
    issubc3.1 $e |- D = ( C |`cat J ) $.
    issubc3.c $e |- ( ph -> C e. Cat ) $.
    issubc3.a $e |- ( ph -> J Fn ( S X. S ) ) $.
    $( Alternate definition of a subcategory, as a subset of the category which
       is itself a category.  The assumption that the identity be closed is
       necessary just as in the case of a monoid, ~ issubm2 , for the same
       reasons, since categories are a generalization of monoids.  (Contributed
       by Mario Carneiro, 6-Jan-2017.) $)
    issubc3 $p |- ( ph -> ( J e. ( Subcat ` C ) <-> ( J C_cat H /\
      A. x e. S ( .1. ` x ) e. ( x J x ) /\ D e. Cat ) ) ) $=
      ( cfv wcel cv co wral ccat wa vg vf vy vz csubc cssc wbr w3a simpr adantr
      subcssc cxp wfn ad2antrr subcidcl ralrimiva subccat cop cco simpr1 simpr2
      3jca chom cbs eqid simplrr simprl1 homffn simplrl rescbas eleqtrd simprl2
      ssc1 simprl3 simprrl reschom oveqd simprrr catcocl rescco 3eltr4d anassrs
      ralrimivva ralrimivvva 3adantr2 r19.26 sylanbrc issubc2 mpbir2and impbida
      a1i ) AHCUENOZHGUFUGZBPZFNWNWNHQOZBERZDSOZUHZAWLTZWMWPWQWSCGHAWLUIZIUKWSW
      OBEWSWNEOZTCEFHWNWSWLXAWTUJAHEEULUMZWLXAMUNWSXAUIJUOUPWSCDHKWTUQVBAWRTZWL
      WMWOUAPZUBPZWNUCPZURZUDPZCUSNZQZQZWNXHHQZOZUAXFXHHQZRUBWNXFHQZRZUDERUCERZ
      TBERZAWMWPWQUTXCWPXQBERZXRAWMWPWQVAAWMWQXSWPAWMWQTZTZXPBUCUDEEEYAXAXFEOZX
      HEOZUHZTXMUBUAXOXNYAYDXEXOOZXDXNOZTZXMYAYDYGTZTZXDXEXGXHDUSNZQZQWNXHDVCNZ
      QXKXLYIDVDNZDYJXEXDYLWNXFXHYMVEYLVEYJVEAWMWQYHVFYIWNEYMXAYBYCYGYAVGYICVDN
      ZCDEHSKYNVEZACSOZXTYHLUNZAXBXTYHMUNZYIEYNHGYRGYNYNULUMYIYNCGIYOVHWKAWMWQY
      HVIVMZVJZVKYIXFEYMXAYBYCYGYAVLYTVKYIXHEYMXAYBYCYGYAVNYTVKYIXEXOWNXFYLQYAY
      DYEYFVOYIHYLWNXFYIYNCDEHSKYOYQYRYSVPZVQVKYIXDXNXFXHYLQYAYDYEYFVRYIHYLXFXH
      UUAVQVKVSYIXJYKXDXEYIXIYJXGXHYIYNCDEXIHSKYOYQYRYSXIVEZVTVQVQYIHYLWNXHUUAV
      QWAWBWCWDWEWOXQBEWFWGXCBUCUDCEXIFUBUAGHIJUUBAYPWRLUJAXBWRMUJWHWIWJ $.
  $}

  ${
    $d f g x y z C $.  $d f g x y z H $.  $d f g x y z ph $.  $d f g x y z S $.
    $d x y D $.  $d x y E $.
    fullsubc.b $e |- B = ( Base ` C ) $.
    fullsubc.h $e |- H = ( Homf ` C ) $.
    fullsubc.c $e |- ( ph -> C e. Cat ) $.
    fullsubc.s $e |- ( ph -> S C_ B ) $.
    $( The full subcategory generated by a subset of objects is the category
       with these objects and the same morphisms as the original.  The result
       is always a subcategory (and it is full, meaning that all morphisms of
       the original category between objects in the subcategory is also in the
       subcategory), see definition 4.1(2) of [Adamek] p. 48.  (Contributed by
       Mario Carneiro, 4-Jan-2017.) $)
    fullsubc $p |- ( ph -> ( H |` ( S X. S ) ) e. ( Subcat ` C ) ) $=
      ( vx vg vf vy cfv wcel cv co wral wa adantr vz cxp cres cssc wbr ccid cop
      csubc cco wfn cvv homffn cbs fvexi sscres mp2an a1i chom eqid ccat sselda
      catidcl simpr ovresd homfval eleqtrrd ad3antrrr wss simprl simprr catcocl
      eqtrd simplr ralrimivva raleqdv raleqbidv mpbird ralrimiva xpss12 syl2anc
      wceq jca fnssres sylancr issubc2 mpbir2and ) AEDDUBZUCZCUHNOWHEUDUEZJPZCU
      FNZNZWJWJWHQZOZKPZLPZWJMPZUGUAPZCUINZQQZWJWRWHQZOZKWQWRWHQZRZLWJWQWHQZRZU
      ADRZMDRZSZJDRWIAEBBUBZUJZBUKOWIBCEGFULZBCUMFUNBDEUKUOUPUQAXIJDAWJDOZSZWNX
      HXNWLWJWJCURNZQZWMXNBCWKXOWJFXOUSZWKUSZACUTOZXMHTZADBWJIVAZVBXNWMWJWJEQXP
      XNWJWJEDAXMVCZYBVDXNBCEXOWJWJGFXQYAYAVEVLVFXNXGMDXNWQDOZSZXFUADYDWRDOZSZX
      FXBKWQWRXOQZRZLWJWQXOQZRYFXBLKYIYGYFWPYIOZWOYGOZSZSZWTWJWRXOQZXAYMBCWSWPW
      OXOWJWQWRFXQWSUSZXNXSYCYEYLXTVGXNWJBOZYCYEYLYAVGZYFWQBOZYLYDYRYEXNDBWQADB
      VHZXMITZVAZTZTYFWRBOYLYDDBWRXNYSYCYTTVAZTZYFYJYKVIYFYJYKVJVKYMXAWJWREQYNY
      MWJWREDXNXMYCYEYLYBVGYDYEYLVMVDYMBCEXOWJWRGFXQYQUUDVEVLVFVNYFXDYHLXEYIYDX
      EYIWAYEYDXEWJWQEQYIYDWJWQEDAXMYCVMXNYCVCVDYDBCEXOWJWQGFXQXNYPYCYATUUAVEVL
      TYFXBKXCYGYFXCWQWREQYGYFWQWREDXNYCYEVMYDYEVCVDYFBCEXOWQWRGFXQUUBUUCVEVLVO
      VPVQVRVRWBVRAJMUACDWSWKLKEWHGXRYOHAXKWGXJVHZWHWGUJXLAYSYSUUEIIDBDBVSVTXJW
      GEWCWDWEWF $.

    fullsubc.d $e |- D = ( C |`s S ) $.
    fullsubc.e $e |- E = ( C |`cat ( H |` ( S X. S ) ) ) $.
    $( The category formed by structure restriction is the same as the category
       restriction.  (Contributed by Mario Carneiro, 5-Jan-2017.) $)
    fullresc $p |- ( ph -> ( ( Homf ` D ) = ( Homf ` E ) /\
                             ( comf ` D ) = ( comf ` E ) ) ) $=
      ( vx vy cfv wceq co eqid cvv chomf ccomf chom wral wcel wss adantr simprl
      cv wa sseldd simprr homfval cxp cres ovresd homffn xpss12 syl2anc fnssres
      ccat wfn sylancr reschom oveqdr eqtr3d cbs ressbas2 fvex eqeltrdi resshom
      syl 3eqtr3rd ralrimivva rescbas homfeq mpbird cco ressco rescco comfeqd
      jca ) ADUAPFUAPQZDUBPFUBPQAWCNUIZOUIZDUCPZRZWDWEFUCPZRZQZOEUDNEUDAWJNOEEA
      WDEUEZWEEUEZUJZUJZWDWEGRZWDWECUCPZRWIWGWNBCGWPWDWEIHWPSZWNEBWDAEBUFZWMKUG
      ZAWKWLUHZUKWNEBWEWSAWKWLULZUKUMWNWDWEGEEUNZUOZRWOWIWNWDWEGEWTXAUPAWMNOXCW
      HABCFEXCVAMHJAGBBUNZVBXBXDUFZXCXBVBBCGIHUQAWRWRXEKKEBEBURUSXDXBGUTVCZKVDV
      EVFAWMNOWPWFAETUEZWPWFQAEDVGPZTAWREXHQKEBDCLHVHVLZDVGVIVJZECDWPTLWQVKVLVE
      VMVNANOEDFWFWHWFSWHSXIABCFEXCVAMHJXFKVOVPVQZADFACVRPZDVRPZFVRPAXGXLXMQXJE
      CDXLTLXLSZVSVLABCFEXLXCVAMHJXFKXNVTVFXKWAWB $.
  $}

  $( A category restricted to a smaller set of objects is a category.
     (Contributed by Mario Carneiro, 6-Jan-2017.) $)
  resscat $p |- ( ( C e. Cat /\ S e. V ) -> ( C |`s S ) e. Cat ) $=
    ( ccat wcel wa cress cbs cfv cin wceq eqid ressinbas adantl chomf cxp cresc
    co cres ccomf simpl wss inss2 fullsubc subccat fullresc simpld simprd ovexd
    a1i cvv catpropd mpbird eqeltrd ) ADEZBCEZFZABGRZABAHIZJZGRZDUPURVAKUOBUSAC
    USLZMNUQVADEAAOIZUTUTPSZQRZDEUQAVEVDVELZUQUSAUTVCVBVCLZUOUPUAZUTUSUBUQBUSUC
    UJZUDUEZUQVAVEUKDUQVAOIVEOIKZVATIVETIKZUQUSAVAUTVEVCVBVGVHVIVALVFUFZUGUQVKV
    LVMUHUQAUTGUIVJULUMUN $.

  ${
    $d x C $.  $d x D $.  $d x H $.  $d x J $.
    subsubc.d $e |- D = ( C |`cat H ) $.
    $( A subcategory of a subcategory is a subcategory.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    subsubc $p |- ( H e. ( Subcat ` C ) -> ( J e. ( Subcat ` D ) <->
      ( J e. ( Subcat ` C ) /\ J C_cat H ) ) ) $=
      ( vx csubc cfv wcel cssc wbr wa chomf eqid cdm ccat co cresc adantr cvv
      id subcssc cbs subcrcl eqidd subcfn reschomf breq2d imbitrrid pm4.71rd cv
      subcss1 ccid wral w3a simpr simpl syl2anc biimpa 2thd cxp wfn sscfn1 ssc1
      ssctr sselda subcid eleq1d ralbidva dmexg dmexd rescabs eqtr2id 3anbi123d
      oveq1i issubc3 subccat 3bitr4rd pm5.32da bitrd biancomd ) CAGHZIZDBGHIZDW
      BIZDCJKZWCWDWFWDLWFWELWCWDWFWDWFWCDBMHZJKZWDBWGDWDUAWGNZUBWCCWGDJWCAUCHZA
      BCOZOZCPEWJNZACUDZWCAWLCWCUAZWCWLUEUFZWCWJAWLCWOWPWMULUGUHZUIUJWCWFWDWEWC
      WFLZDAMHZJKZFUKZAUMHZHZXAXADQZIZFDOOZUNZADRQZPIZUOWHXABUMHZHZXDIZFXFUNZBD
      RQZPIZUOWEWDWRWTWHXGXMXIXOWRWTWHWRWFCWSJKWTWCWFUPZWRAWSCWCWFUQZWSNZUBDCWS
      VEURWCWFWHWQUSUTWRXEXLFXFWRXAXFIZLZXCXKXDXTABWLXBCXAEWRWCXSXQSWRCWLWLVAVB
      ZXSWCYAWFWPSZSXBNZWRXFWLXAWRXFWLDCWRXFDCXPWRXFUEVCZYBXPVDZVFVGVHVIWRXHXNP
      WRXNACRQZDRQXHBYFDREVOWRAWLXFCDPTWCAPIWFWNSZYBYDWCWLTIWFWCWKTCWBVJVKSYEVL
      VMVHVNWRFAXHXFXBWSDXRYCXHNYGYDVPWRFBXNXFXJWGDWIXJNXNNWCBPIWFWCABCEWOVQSYD
      VPVRVSVTWA $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Functors
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Func $.  $( The class of all functors. $)
  $c idFunc $.  $( Identity functor. $)
  $c o.func $.  $( Functor composition. $)
  $c |`f $.  $( Functor restriction. $)

  $( Extend class notation with the class of all functors. $)
  cfunc $a class Func $.

  $( Extend class notation with identity functor. $)
  cidfu $a class idFunc $.

  $( Extend class notation with functor composition. $)
  ccofu $a class o.func $.

  $( Extend class notation to include restriction of a functor to a
     subcategory. $)
  cresf $a class |`f $.

  ${
    $d b f g h m n t u x y z $.
    $( Function returning all the functors from a category ` t ` to a category
       ` u ` .  Definition 3.17 of [Adamek] p. 29, and definition in [Lang]
       p. 62 ("covariant functor").  Intuitively a functor associates any
       morphism of ` t ` to a morphism of ` u ` , any object of ` t ` to an
       object of ` u ` , and respects the identity, the composition, the domain
       and the codomain.  Here to capture the idea that a functor associates
       any object of ` t ` to an object of ` u ` we write it associates any
       identity of ` t ` to an identity of ` u ` which simplifies the
       definition.  According to remark 3.19 in [Adamek] p. 30, "a functor F :
       A -> B is technically a family of functions; one from Ob(A) to Ob(B)
       [here: f, called "the object part" in the following], and for each pair
       (A,A') of A-objects, one from hom(A,A') to hom(FA, FA') [here: g, called
       "the morphism part" in the following]".  (Contributed by FL,
       10-Feb-2008.)  (Revised by Mario Carneiro, 2-Jan-2017.) $)
    df-func $a |- Func = ( t e. Cat , u e. Cat |-> { <. f , g >. |
     [. ( Base ` t ) / b ]. ( f : b --> ( Base ` u ) /\ g e. X_ z e. ( b X. b )
      ( ( ( f ` ( 1st ` z ) ) ( Hom ` u )
          ( f ` ( 2nd ` z ) ) ) ^m ( ( Hom ` t ) ` z ) ) /\ A. x e. b
      ( ( ( x g x ) ` ( ( Id ` t ) ` x ) ) = ( ( Id ` u ) ` ( f ` x ) ) /\
    A. y e. b A. z e. b A. m e. ( x ( Hom ` t ) y ) A. n e. ( y ( Hom ` t ) z )
      ( ( x g z ) ` ( n ( <. x , y >. ( comp ` t ) z ) m ) ) =
      ( ( ( y g z ) ` n ) ( <. ( f ` x ) , ( f ` y ) >.
          ( comp ` u ) ( f ` z ) ) ( ( x g y ) ` m ) ) ) ) } ) $.

    $( Define the identity functor.  (Contributed by Mario Carneiro,
       3-Jan-2017.) $)
    df-idfu $a |- idFunc = ( t e. Cat |-> [_ ( Base ` t ) / b ]_ <.
    ( _I |` b ) , ( z e. ( b X. b ) |-> ( _I |` ( ( Hom ` t ) ` z ) ) ) >. ) $.

    $( Define the composition of two functors.  (Contributed by Mario Carneiro,
       3-Jan-2017.) $)
    df-cofu $a |- o.func = ( g e. _V , f e. _V |->
      <. ( ( 1st ` g ) o. ( 1st ` f ) ) , ( x e. dom dom ( 2nd ` f ) ,
      y e. dom dom ( 2nd ` f ) |-> ( ( ( ( 1st ` f ) ` x ) ( 2nd ` g )
        ( ( 1st ` f ) ` y ) ) o. ( x ( 2nd ` f ) y ) ) ) >. ) $.

    $( Define the restriction of a functor to a subcategory (analogue of
       ~ df-res ).  (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    df-resf $a |- |`f = ( f e. _V , h e. _V |->
      <. ( ( 1st ` f ) |` dom dom h ) , ( x e. dom h |->
        ( ( ( 2nd ` f ) ` x ) |` ( h ` x ) ) ) >. ) $.

    $( The set of functors is a relation.  (Contributed by Mario Carneiro,
       2-Jan-2017.) $)
    relfunc $p |- Rel ( D Func E ) $=
      ( vb vu vf vg vz vt vx vn vm vy cv cbs cfv chom co ccid wceq wral wf c1st
      cxp c2nd cmap cixp wcel cop cco wa w3a wsbc ccat cfunc df-func relmpoopab
      ) CMZDMZNOEMZUAFMZGUQUQUCGMZUBOUSOVAUDOUSOURPOQVAHMZPOZOUEQUFUGIMZVBROOVD
      VDUTQOVDUSOZURROOSJMZKMZVDLMZUHVAVBUIOQQVDVAUTQOVFVHVAUTQOVGVDVHUTQOVEVHU
      SOUHVAUSOURUIOQQSJVHVAVCQTKVDVHVCQTGUQTLUQTUJIUQTUKCVBNOULHDEFUMUMABUNILG
      DHEFKJCUOUP $.

    $( Reverse closure for a functor.  (Contributed by Mario Carneiro,
       6-Jan-2017.) $)
    funcrcl $p |- ( F e. ( D Func E ) -> ( D e. Cat /\ E e. Cat ) ) $=
      ( vt vu vb vf vg vz vx vn vm vy ccat cv cbs cfv chom co wral wf c1st c2nd
      cxp cmap cixp wcel ccid wceq cop cco w3a wsbc copab cfunc df-func elmpocl
      wa ) DENNFOZEOZPQGOZUAHOZIUSUSUDIOZUBQVAQVCUCQVAQUTRQSVCDOZRQZQUESUFUGJOZ
      VDUHQQVFVFVBSQVFVAQZUTUHQQUIKOZLOZVFMOZUJVCVDUKQSSVFVCVBSQVHVJVCVBSQVIVFV
      JVBSQVGVJVAQUJVCVAQUTUKQSSUIKVJVCVESTLVFVJVESTIUSTMUSTURJUSTULFVDPQUMGHUN
      ABUOCJMIEDGHLKFUPUQ $.
  $}

  ${
    $d b d e f g m n x y z B $.  $d b d e f g C $.  $d b d e f g m n x y z D $.
    $d b d e f g m n x y z E $.  $d b d e f g m n x y z H $.  $d b d e f g I $.
    $d f g m n x y z F $.  $d f g m n x y z G $.  $d b d e f g x y z J $.
    $d b d e f g .1. $.  $d m n x y z ph $.  $d b d e f g .x. $.
    $d b d e f g O $.
    isfunc.b $e |- B = ( Base ` D ) $.
    isfunc.c $e |- C = ( Base ` E ) $.
    isfunc.h $e |- H = ( Hom ` D ) $.
    isfunc.j $e |- J = ( Hom ` E ) $.
    isfunc.1 $e |- .1. = ( Id ` D ) $.
    isfunc.i $e |- I = ( Id ` E ) $.
    isfunc.x $e |- .x. = ( comp ` D ) $.
    isfunc.o $e |- O = ( comp ` E ) $.
    isfunc.d $e |- ( ph -> D e. Cat ) $.
    isfunc.e $e |- ( ph -> E e. Cat ) $.
    $( Value of the set of functors between two categories.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    isfunc $p |- ( ph -> ( F ( D Func E ) G <-> ( F : B --> C /\
      G e. X_ z e. ( B X. B ) ( ( ( F ` ( 1st ` z ) ) J
                ( F ` ( 2nd ` z ) ) ) ^m ( H ` z ) ) /\ A. x e. B
      ( ( ( x G x ) ` ( .1. ` x ) ) = ( I ` ( F ` x ) ) /\
    A. y e. B A. z e. B A. m e. ( x H y ) A. n e. ( y H z )
      ( ( x G z ) ` ( n ( <. x , y >. .x. z ) m ) ) =
      ( ( ( y G z ) ` n ) ( <. ( F ` x ) , ( F ` y ) >.
          O ( F ` z ) ) ( ( x G y ) ` m ) ) ) ) ) ) $=
      ( vf vg vd ve vb cfunc co wbr cv cmap wcel cxp c1st cfv c2nd cixp wa wceq
      cop wral copab wf w3a ccat cbs chom ccid cco wsbc cvv fvexd simpl eqtr4di
      fveq2d simpr simplr feq23d bitr4di sqxpeqd ixpeq1d simpll fveq1d ixpeq2dv
      fvexi elmap oveqd oveq12d eqtrd eleq2d eqeq12d raleqbidv 3anbi123d df-3an
      anbi12d bitrdi sbcied2 opabbidv df-func csn ciun vsnex rgenw ixpexg ax-mp
      ovex xpex iunex anim2i 2eximi elopab eliunxp 3imtr4i ssriv ovmpoa syl2anc
      wex ssexi breqd brabv elex anim12i 3adant3 eleq1d oveq1d eleq12d oveq123d
      opeq12d 2ralbidv ralbidv bitr3id eqid brabga pm5.21nii 3anbi1i bitri ) AM
      NGLUNUOZUPMNUIUQZFEURUOZUSZUJUQZDEEUTZDUQZVAVBZUUEVBZUUJVCVBZUUEVBZQUOZUU
      JOVBZURUOZVDZUSZVEZBUQZIVBZUVAUVAUUHUOZVBZUVAUUEVBZPVBZVFZKUQZJUQZUVACUQZ
      VGZUUJHUOZUOZUVAUUJUUHUOZVBZUVHUVJUUJUUHUOZVBZUVIUVAUVJUUHUOZVBZUVEUVJUUE
      VBZVGZUUJUUEVBZRUOZUOZVFZKUVJUUJOUOZVHZJUVAUVJOUOZVHZDEVHZCEVHZVEZBEVHZVE
      ZUIUJVIZUPZEFMVJZNDUUIUUKMVBZUUMMVBZQUOZUUPURUOZVDZUSZUVBUVAUVANUOZVBZUVA
      MVBZPVBZVFZUVMUVAUUJNUOZVBZUVHUVJUUJNUOZVBZUVIUVAUVJNUOZVBZUXFUVJMVBZVGZU
      UJMVBZRUOZUOZVFZKUWFVHJUWHVHZDEVHCEVHZVEZBEVHZVKZAUUDUWOMNAGVLUSLVLUSUUDU
      WOVFUGUHUKULGLVLVLUMUQZULUQZVMVBZUUEVJZUUHDUYFUYFUTZUULUUNUYGVNVBZUOZUUJU
      KUQZVNVBZVBZURUOZVDZUSZUVAUYMVOVBZVBZUVCVBZUVEUYGVOVBZVBZVFZUVHUVIUVKUUJU
      YMVPVBZUOZUOZUVNVBZUVQUVSUWAUWBUYGVPVBZUOZUOZVFZKUVJUUJUYNUOZVHZJUVAUVJUY
      NUOZVHZDUYFVHZCUYFVHZVEZBUYFVHZVKZUMUYMVMVBZVQZUIUJVIUWOUNUYMGVFZUYGLVFZV
      EZVVCUWNUIUJVVFVVAUWNUMVVBEVRVVFUYMVMVSVVFVVBGVMVBEVVFUYMGVMVVDVVEVTWBSWA
      VVFUYFEVFZVEZVVAUUGUUSUWMVKZUWNVVHUYIUUGUYRUUSVUTUWMVVHUYIEFUUEVJUUGVVHUY
      FUYHEFUUEVVFVVGWCZVVHUYHLVMVBFVVHUYGLVMVVDVVEVVGWDZWBTWAWEFEUUEFLVMTWLZEG
      VMSWLZWMWFVVHUYQUURUUHVVHUYQDUUIUYPVDUURVVHDUYJUUIUYPVVHUYFEVVJWGWHVVHDUU
      IUYPUUQVVHUYLUUOUYOUUPURVVHUYKQUULUUNVVHUYKLVNVBQVVHUYGLVNVVKWBUBWAWNVVHU
      UJUYNOVVHUYNGVNVBOVVHUYMGVNVVDVVEVVGWIZWBUAWAZWJWOWKWPWQVVHVUSUWLBUYFEVVJ
      VVHVUDUVGVURUWKVVHVUAUVDVUCUVFVVHUYTUVBUVCVVHUVAUYSIVVHUYSGVOVBIVVHUYMGVO
      VVNWBUCWAWJWBVVHUVEVUBPVVHVUBLVOVBPVVHUYGLVOVVKWBUDWAWJWRVVHVUQUWJCUYFEVV
      JVVHVUPUWIDUYFEVVJVVHVUNUWGJVUOUWHVVHUYNOUVAUVJVVOWNVVHVULUWEKVUMUWFVVHUY
      NOUVJUUJVVOWNVVHVUHUVOVUKUWDVVHVUGUVMUVNVVHVUFUVLUVHUVIVVHVUEHUVKUUJVVHVU
      EGVPVBHVVHUYMGVPVVNWBUEWAWNWNWBVVHVUJUWCUVQUVSVVHVUIRUWAUWBVVHVUILVPVBRVV
      HUYGLVPVVKWBUFWAWNWNWRWSWSWSWSXBWSWTUUGUUSUWMXAZXCXDXEBCDULUKUIUJJKUMXFUW
      OUIUUFUUEXGZUURUTZXHZUIUUFVVRFEURXMVVQUURUIXIUUQVRUSZDUUIVHUURVRUSVVTDUUI
      UUOUUPURXMXJDUUIUUQVRXKXLXNXOUKUWOVVSUYMUUEUUHVGVFZUWNVEZUJYDUIYDVWAUUTVE
      ZUJYDUIYDUYMUWOUSUYMVVSUSVWBVWCUIUJUWNUUTVWAUUTUWMVTXPXQUWNUIUJUYMXRUIUJU
      UFUURUYMXSXTYAYEYBYCYFUWPMUUFUSZUXCUYDVKZUYEUWPMVRUSZNVRUSZVEZVWEUWNUIUJM
      NYGVWDUXCVWHUYDVWDVWFUXCVWGMUUFYHNUXBYHYIYJUWNVWEUIUJMNUWOVRVRUWNVVIUUEMV
      FZUUHNVFZVEZVWEVVPVWKUUGVWDUUSUXCUWMUYDVWKUUEMUUFVWIVWJVTZYKVWKUUHNUURUXB
      VWIVWJWCZVWKDUUIUUQUXAVWKUUOUWTUUPURVWKUULUWRUUNUWSQVWKUUKUUEMVWLWJVWKUUM
      UUEMVWLWJWOYLWKYMVWKUWLUYCBEVWKUVGUXHUWKUYBVWKUVDUXEUVFUXGVWKUVBUVCUXDVWK
      UUHNUVAUVAVWMWNWJVWKUVEUXFPVWKUVAUUEMVWLWJZWBWRVWKUWIUYACDEEVWKUWEUXTJKUW
      HUWFVWKUVOUXJUWDUXSVWKUVMUVNUXIVWKUUHNUVAUUJVWMWNWJVWKUVQUXLUVSUXNUWCUXRV
      WKUWAUXPUWBUXQRVWKUVEUXFUVTUXOVWNVWKUVJUUEMVWLWJYOVWKUUJUUEMVWLWJWOVWKUVH
      UVPUXKVWKUUHNUVJUUJVWMWNWJVWKUVIUVRUXMVWKUUHNUVAUVJVWMWNWJYNWRYPYPXBYQWTY
      RUWOYSYTUUAVWDUWQUXCUYDFEMVVLVVMWMUUBUUCXC $.

    isfuncd.1 $e |- ( ph -> F : B --> C ) $.
    isfuncd.2 $e |- ( ph -> G Fn ( B X. B ) ) $.
    isfuncd.3 $e |- ( ( ph /\ ( x e. B /\ y e. B ) ) ->
      ( x G y ) : ( x H y ) --> ( ( F ` x ) J ( F ` y ) ) ) $.
    isfuncd.4 $e |- ( ( ph /\ x e. B ) ->
      ( ( x G x ) ` ( .1. ` x ) ) = ( I ` ( F ` x ) ) ) $.
    isfuncd.5 $e |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) /\
      ( m e. ( x H y ) /\ n e. ( y H z ) ) ) ->
        ( ( x G z ) ` ( n ( <. x , y >. .x. z ) m ) ) =
        ( ( ( y G z ) ` n ) ( <. ( F ` x ) , ( F ` y ) >.
            O ( F ` z ) ) ( ( x G y ) ` m ) ) ) $.
    $( Deduce that an operation is a functor of categories.  (Contributed by
       Mario Carneiro, 4-Jan-2017.) $)
    isfuncd $p |- ( ph -> F ( D Func E ) G ) $=
      ( cfunc co wbr wf cxp cv c1st cfv c2nd cmap cixp wcel wceq cop wa cvv wfn
      wral cbs fvexi xpex fnex sylancl ovex elmap sylibr ralrimivva fveq2 df-ov
      eqtr4di vex op1std fveq2d op2ndd oveq12d ralxp elixp2 syl3anbrc wi 3expia
      eleq12d w3a 3exp2 imp43 ralrimivv jca ralrimiva isfunc mpbir3and ) AMNGLU
      NUOUPEFMUQNDEEURZDUSZUTVAZMVAZXDVBVAZMVAZQUOZXDOVAZVCUOZVDVEZBUSZIVAXMXMN
      UOVAXMMVAZPVAVFZKUSZJUSZXMCUSZVGZXDHUOUOXMXDNUOVAXPXRXDNUOVAXQXMXRNUOZVAX
      NXRMVAZVGXDMVARUOUOVFZKXRXDOUOZVKJXMXROUOZVKZDEVKCEVKZVHZBEVKUIANVIVEZNXC
      VJZXDNVAZXKVEZDXCVKZXLAYIXCVIVEYHUJEEEGVLSVMZYMVNXCVINVOVPUJAXTXNYAQUOZYD
      VCUOZVEZCEVKBEVKYLAYPBCEEAXMEVEZXREVEZVHVHYDYNXTUQYPUKYNYDXTXNYAQVQXMXROV
      QVRVSVTYKYPDBCEEXDXSVFZYJXTXKYOYSYJXSNVAXTXDXSNWAXMXRNWBWCYSXIYNXJYDVCYSX
      FXNXHYAQYSXEXMMXMXRXDBWDZCWDZWEWFYSXGXRMXMXRXDYTUUAWGWFWHYSXJXSOVAYDXDXSO
      WAXMXROWBWCWHWNWIVSDXCXKNWJWKAYGBEAYQVHZXOYFULUUBYECDEEUUBYRXDEVEZVHVHYBJ
      KYDYCAYQYRUUCXQYDVEXPYCVEVHZYBWLZAYQYRUUCUUEAYQYRUUCWOUUDYBUMWMWPWQWRVTWS
      WTABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHXAXB $.
  $}

  ${
    $d m n x y z B $.  $d m n x y z D $.  $d m n x y z E $.  $d m n x y z ph $.
    $d m n x y z F $.  $d m n x y z G $.
    funcf1.b $e |- B = ( Base ` D ) $.
    funcf1.c $e |- C = ( Base ` E ) $.
    funcf1.f $e |- ( ph -> F ( D Func E ) G ) $.
    $( The object part of a functor is a function on objects.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    funcf1 $p |- ( ph -> F : B --> C ) $=
      ( vz vx vn vm cv cfv co wcel wral eqid vy wf cxp c1st c2nd chom cmap cixp
      ccid wceq cop cco wa cfunc wbr w3a ccat df-br sylib funcrcl simpld simprd
      syl isfunc mpbid simp1d ) ABCFUBZGKBBUCKOZUDPFPVHUEPFPEUFPZQVHDUFPZPUGQUH
      RZLOZDUIPZPVLVLGQPVLFPZEUIPZPUJMOZNOZVLUAOZUKVHDULPZQQVLVHGQPVPVRVHGQPVQV
      LVRGQPVNVRFPUKVHFPEULPZQQUJMVRVHVJQSNVLVRVJQSKBSUABSUMLBSZAFGDEUNQZUOZVGV
      KWAUPJALUAKBCDVSVMNMEFGVJVOVIVTHIVJTVITVMTVOTVSTVTTADUQRZEUQRZAFGUKZWBRZW
      DWEUMAWCWGJFGWBURUSDEWFUTVCZVAAWDWEWHVBVDVEVF $.
  $}

  ${
    $d m n x y z B $.  $d m n x y z D $.  $d m n x y z E $.  $d m n x y z ph $.
    $d m n x y z F $.  $d m n x y z G $.  $d x y z J $.  $d z X $.  $d z Y $.
    $d m n x y z H $.
    funcixp.b $e |- B = ( Base ` D ) $.
    funcixp.h $e |- H = ( Hom ` D ) $.
    funcixp.j $e |- J = ( Hom ` E ) $.
    funcixp.f $e |- ( ph -> F ( D Func E ) G ) $.
    $( The morphism part of a functor is a function on homsets.  (Contributed
       by Mario Carneiro, 2-Jan-2017.) $)
    funcixp $p |- ( ph -> G e. X_ z e. ( B X. B )
      ( ( ( F ` ( 1st ` z ) ) J ( F ` ( 2nd ` z ) ) ) ^m ( H ` z ) ) ) $=
      ( vx cfv cv co wcel wral eqid vn vm cbs cxp c1st c2nd cmap cixp ccid wceq
      vy wf cop cco wa cfunc wbr w3a ccat df-br sylib funcrcl syl simpld simprd
      isfunc mpbid simp2d ) ACEUCOZFULZGBCCUDBPZUEOFOVKUFOFOIQVKHOUGQUHRZNPZDUI
      OZOVMVMGQOVMFOZEUIOZOUJUAPZUBPZVMUKPZUMVKDUNOZQQVMVKGQOVQVSVKGQOVRVMVSGQO
      VOVSFOUMVKFOEUNOZQQUJUAVSVKHQSUBVMVSHQSBCSUKCSUONCSZAFGDEUPQZUQZVJVLWBURM
      ANUKBCVIDVTVNUBUAEFGHVPIWAJVITKLVNTVPTVTTWATADUSRZEUSRZAFGUMZWCRZWEWFUOAW
      DWHMFGWCUTVADEWGVBVCZVDAWEWFWIVEVFVGVH $.

    funcf2.x $e |- ( ph -> X e. B ) $.
    funcf2.y $e |- ( ph -> Y e. B ) $.
    $( The morphism part of a functor is a function on homsets.  (Contributed
       by Mario Carneiro, 2-Jan-2017.) $)
    funcf2 $p |- ( ph ->
      ( X G Y ) : ( X H Y ) --> ( ( F ` X ) J ( F ` Y ) ) ) $=
      ( co cfv cmap wcel vz wf cop c1st c2nd df-ov cv cixp funcixp opelxpd wceq
      cxp 2fveq3 oveq12d fveq2 eqtr4di syl2anc eqeltrid wa op1stg fveq2d op2ndg
      fvixp oveq1d eleqtrd elmapi syl ) AIJFQZIERZJERZHQZIJGQZSQZTVLVKVHUBAVHIJ
      UCZUDRZERZVNUERZERZHQZVLSQZVMAVHVNFRZVTIJFUFAFUABBULZUAUGZUDRERZWCUERERZH
      QZWCGRZSQZUHTVNWBTWAVTTAUABCDEFGHKLMNUIAIJBBOPUJUAWBWHVNVTFWCVNUKZWFVSWGV
      LSWIWDVPWEVRHWCVNEUDUMWCVNEUEUMUNWIWGVNGRVLWCVNGUOIJGUFUPUNVCUQURAVSVKVLS
      AIBTZJBTZVSVKUKOPWJWKUSZVPVIVRVJHWLVOIEIJBBUTVAWLVQJEIJBBVBVAUNUQVDVEVHVK
      VLVFVG $.
  $}

  ${
    $d x B $.  $d x D $.  $d x E $.  $d x F $.  $d x G $.  $d x ph $.
    funcfn2.b $e |- B = ( Base ` D ) $.
    funcfn2.f $e |- ( ph -> F ( D Func E ) G ) $.
    $( The morphism part of a functor is a function.  (Contributed by Mario
       Carneiro, 3-Jan-2017.) $)
    funcfn2 $p |- ( ph -> G Fn ( B X. B ) ) $=
      ( vx cxp cv c1st cfv c2nd chom co cmap cixp wcel eqid wfn funcixp ixpfn
      syl ) AFIBBJZIKZLMEMUFNMEMDOMZPUFCOMZMQPZRSFUEUAAIBCDEFUHUGGUHTUGTHUBIUEU
      IFUCUD $.
  $}

  ${
    $d m n x y z B $.  $d m n x y z D $.  $d m n x y z E $.  $d m n x y z ph $.
    $d x .1. $.  $d m n x y z F $.  $d m n x y z G $.  $d x I $.  $d x X $.
    funcid.b $e |- B = ( Base ` D ) $.
    funcid.1 $e |- .1. = ( Id ` D ) $.
    funcid.i $e |- I = ( Id ` E ) $.
    funcid.f $e |- ( ph -> F ( D Func E ) G ) $.
    funcid.x $e |- ( ph -> X e. B ) $.
    $( A functor maps each identity to the corresponding identity in the target
       category.  (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    funcid $p |- ( ph -> ( ( X G X ) ` ( .1. ` X ) ) = ( I ` ( F ` X ) ) ) $=
      ( vx cv cfv co wral eqid vn vm vy vz wceq id oveq12d fveq2 fveq12d 2fveq3
      eqeq12d cop cco chom wa cbs wf cxp c1st c2nd cmap cixp wcel cfunc wbr w3a
      ccat df-br sylib funcrcl simpld simprd isfunc mpbid simp3d ralimi rspcdva
      syl simpl ) AOPZDQZVTVTGRZQZVTFQZHQZUEZIDQZIIGRZQZIFQHQZUEOBIVTIUEZWCWIWE
      WJWKWAWGWBWHWKVTIVTIGWKUFZWLUGVTIDUHUIVTIHFUJUKAWFUAPZUBPZVTUCPZULUDPZCUM
      QZRRVTWPGRQWMWOWPGRQWNVTWOGRQWDWOFQULWPFQEUMQZRRUEUAWOWPCUNQZRSUBVTWOWSRS
      UDBSUCBSZUOZOBSZWFOBSABEUPQZFUQZGUDBBURWPUSQFQWPUTQFQEUNQZRWPWSQVARVBVCZX
      BAFGCEVDRZVEZXDXFXBVFMAOUCUDBXCCWQDUBUAEFGWSHXEWRJXCTWSTXETKLWQTWRTACVGVC
      ZEVGVCZAFGULZXGVCZXIXJUOAXHXLMFGXGVHVICEXKVJVRZVKAXIXJXMVLVMVNVOXAWFOBWFW
      TVSVPVRNVQ $.
  $}

  ${
    $d m n x y z B $.  $d m n x y z D $.  $d m n x y z E $.  $d m n x y z ph $.
    $d m n x y z F $.  $d m n x y z G $.  $d m n x y z H $.  $d m n x y z M $.
    $d m n x y z N $.  $d m n x y z O $.  $d m n x y z X $.  $d m n x y z Y $.
    $d m n x y z .x. $.  $d m n x y z Z $.
    funcco.b $e |- B = ( Base ` D ) $.
    funcco.h $e |- H = ( Hom ` D ) $.
    funcco.o $e |- .x. = ( comp ` D ) $.
    funcco.O $e |- O = ( comp ` E ) $.
    funcco.f $e |- ( ph -> F ( D Func E ) G ) $.
    funcco.x $e |- ( ph -> X e. B ) $.
    funcco.y $e |- ( ph -> Y e. B ) $.
    funcco.z $e |- ( ph -> Z e. B ) $.
    funcco.m $e |- ( ph -> M e. ( X H Y ) ) $.
    funcco.n $e |- ( ph -> N e. ( Y H Z ) ) $.
    $( A functor maps composition in the source category to composition in the
       target.  (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    funcco $p |- ( ph -> ( ( X G Z ) ` ( N ( <. X , Y >. .x. Z ) M ) ) =
      ( ( ( Y G Z ) ` N ) ( <. ( F ` X ) , ( F ` Y ) >.
          O ( F ` Z ) ) ( ( X G Y ) ` M ) ) ) $=
      ( vx vn vm vy vz cv ccid cfv co wceq cop wral cbs cxp c1st c2nd chom cmap
      wa wf cixp wcel cfunc wbr w3a eqid ccat df-br sylib funcrcl simpld simprd
      syl isfunc mpbid simp3d adantr ad2antrr ad3antrrr simpllr simplr eleqtrrd
      oveq12d ad4antr simp-5r simp-4r opeq12d oveq123d fveq12d eqeq12d rspcimdv
      simpr fveq2d rspcdv adantld mpd ) AUEUJZCUKULZULXAXAGUMULXAFULZEUKULZULUN
      ZUFUJZUGUJZXAUHUJZUOZUIUJZDUMZUMZXAXJGUMZULZXFXHXJGUMZULZXGXAXHGUMZULZXCX
      HFULZUOZXJFULZKUMZUMZUNZUFXHXJHUMZUPZUGXAXHHUMZUPZUIBUPZUHBUPZVCZUEBUPZJI
      LMUOZNDUMZUMZLNGUMZULZJMNGUMZULZILMGUMZULZLFULZMFULZUOZNFULZKUMZUMZUNZABE
      UQULZFVDZGUIBBURXJUSULFULXJUTULFULEVAULZUMXJHULVBUMVEVFZYLAFGCEVGUMZVHZUU
      JUULYLVISAUEUHUIBUUICDXBUGUFEFGHXDUUKKOUUIVJPUUKVJXBVJXDVJQRACVKVFZEVKVFZ
      AFGUOZUUMVFZUUOUUPVCAUUNUURSFGUUMVLVMCEUUQVNVQZVOAUUOUUPUUSVPVRVSVTAYKUUH
      UELBTAXALUNZVCZYJUUHXEUVAYIUUHUHMBAMBVFUUTUAWAUVAXHMUNZVCZYHUUHUINBANBVFU
      UTUVBUBWBUVCXJNUNZVCZYFUUHUGIYGUVEILMHUMZYGAIUVFVFUUTUVBUVDUCWCUVEXALXHMH
      AUUTUVBUVDWDUVAUVBUVDWEWGWFUVEXGIUNZVCZYDUUHUFJYEUVHJMNHUMZYEAJUVIVFUUTUV
      BUVDUVGUDWHUVHXHMXJNHUVAUVBUVDUVGWDUVCUVDUVGWEWGWFUVHXFJUNZVCZXNYQYCUUGUV
      KXLYOXMYPUVKXALXJNGAUUTUVBUVDUVGUVJWIZUVCUVDUVGUVJWDZWGUVKXFJXGIXKYNUVKXI
      YMXJNDUVKXALXHMUVLUVAUVBUVDUVGUVJWJZWKUVMWGUVHUVJWPZUVEUVGUVJWEZWLWMUVKXP
      YSXRUUAYBUUFUVKXTUUDYAUUEKUVKXCUUBXSUUCUVKXALFUVLWQUVKXHMFUVNWQWKUVKXJNFU
      VMWQWGUVKXFJXOYRUVKXHMXJNGUVNUVMWGUVOWMUVKXGIXQYTUVKXALXHMGUVLUVNWGUVPWMW
      LWNWRWOWOWOWSWOWT $.
  $}

  ${
    funcsect.b $e |- B = ( Base ` D ) $.
    funcsect.s $e |- S = ( Sect ` D ) $.
    funcsect.t $e |- T = ( Sect ` E ) $.
    funcsect.f $e |- ( ph -> F ( D Func E ) G ) $.
    funcsect.x $e |- ( ph -> X e. B ) $.
    funcsect.y $e |- ( ph -> Y e. B ) $.
    funcsect.m $e |- ( ph -> M ( X S Y ) N ) $.
    $( The image of a section under a functor is a section.  (Contributed by
       Mario Carneiro, 2-Jan-2017.) $)
    funcsect $p |- ( ph ->
      ( ( X G Y ) ` M ) ( ( F ` X ) T ( F ` Y ) ) ( ( Y G X ) ` N ) ) $=
      ( cfv co wbr cop cco ccid wceq chom wcel eqid ccat cfunc wa df-br funcrcl
      w3a sylib simpld issect simp3d fveq2d simp1d simp2d funcco funcid 3eqtr3d
      syl mpbid cbs simprd funcf1 ffvelcdmd funcf2 issect2 mpbird ) AIKLHUAZTZJ
      LKHUAZTZKGTZLGTZEUAUBVRVPVSVTUCVSFUDTZUAUAZVSFUETZTZUFAJIKLUCKCUDTZUAUAZK
      KHUAZTKCUETZTZWGTWBWDAWFWIWGAIKLCUGTZUAZUHZJLKWJUAZUHZWFWIUFZAIJKLDUAUBWL
      WNWOUOSABCDWEWHIJWJKLMWJUIZWEUIZWHUIZNACUJUHZFUJUHZAGHUCZCFUKUAZUHZWSWTUL
      AGHXBUBXCPGHXBUMUPCFXAUNVFZUQQRURVGZUSUTABCWEFGHWJIJWAKLKMWPWQWAUIZPQRQAW
      LWNWOXEVAZAWLWNWOXEVBZVCABCWHFGHWCKMWRWCUIZPQVDVEAFVHTZFEWAWCVPVRFUGTZVSV
      TXJUIZXKUIZXFXIOAWSWTXDVIABXJKGABXJCFGHMXLPVJZQVKABXJLGXNRVKAWKVSVTXKUAIV
      OABCFGHWJXKKLMWPXMPQRVLXGVKAWMVTVSXKUAJVQABCFGHWJXKLKMWPXMPRQVLXHVKVMVN
      $.
  $}

  ${
    funcinv.b $e |- B = ( Base ` D ) $.
    funcinv.s $e |- I = ( Inv ` D ) $.
    funcinv.t $e |- J = ( Inv ` E ) $.
    funcinv.f $e |- ( ph -> F ( D Func E ) G ) $.
    funcinv.x $e |- ( ph -> X e. B ) $.
    funcinv.y $e |- ( ph -> Y e. B ) $.
    funcinv.m $e |- ( ph -> M ( X I Y ) N ) $.
    $( The image of an inverse under a functor is an inverse.  (Contributed by
       Mario Carneiro, 3-Jan-2017.) $)
    funcinv $p |- ( ph ->
      ( ( X G Y ) ` M ) ( ( F ` X ) J ( F ` Y ) ) ( ( Y G X ) ` N ) ) $=
      ( co cfv wbr csect eqid wa ccat wcel cop cfunc df-br sylib funcrcl simpld
      syl isinv mpbid funcsect simprd cbs funcf1 ffvelcdmd mpbir2and ) AIKLFTUA
      ZJLKFTUAZKEUAZLEUAZHTUBVCVDVEVFDUCUAZTUBVDVCVFVEVGTUBABCCUCUAZVGDEFIJKLMV
      HUDZVGUDZPQRAIJKLVHTUBZJILKVHTUBZAIJKLGTUBVKVLUESABCVHIJGKLMNACUFUGZDUFUG
      ZAEFUHZCDUITZUGZVMVNUEAEFVPUBVQPEFVPUJUKCDVOULUNZUMQRVIUOUPZUMUQABCVHVGDE
      FJILKMVIVJPRQAVKVLVSURUQADUSUAZDVGVCVDHVEVFVTUDZOAVMVNVRURABVTKEABVTCDEFM
      WAPUTZQVAABVTLEWBRVAVJUOVB $.
  $}

  ${
    funciso.b $e |- B = ( Base ` D ) $.
    funciso.s $e |- I = ( Iso ` D ) $.
    funciso.t $e |- J = ( Iso ` E ) $.
    funciso.f $e |- ( ph -> F ( D Func E ) G ) $.
    funciso.x $e |- ( ph -> X e. B ) $.
    funciso.y $e |- ( ph -> Y e. B ) $.
    funciso.m $e |- ( ph -> M e. ( X I Y ) ) $.
    $( The image of an isomorphism under a functor is an isomorphism.
       Proposition 3.21 of [Adamek] p. 32.  (Contributed by Mario Carneiro,
       3-Jan-2017.) $)
    funciso $p |- ( ph -> ( ( X G Y ) ` M ) e. ( ( F ` X ) J ( F ` Y ) ) ) $=
      ( cfv co cbs cinv eqid ccat wcel cop cfunc wa wbr df-br sylib funcrcl syl
      simprd funcf1 ffvelcdmd simpld invisoinvr funcinv inviso1 ) ADUASZDIJKFTS
      IJKCUBSZTSZKJFTSHDUBSZJESKESVAUCZVDUCZACUDUEZDUDUEZAEFUFZCDUGTZUEZVGVHUHA
      EFVJUIVKOEFVJUJUKCDVIULUMZUNABVAJEABVACDEFLVEOUOZPUPABVAKEVMQUPNABCDEFVBV
      DIVCJKLVBUCZVFOPQABCIGVBJKLMVNAVGVHVLUQPQRURUSUT $.
  $}

  ${
    $d f g x y z C $.  $d f g x y z F $.  $d f g x y z G $.  $d f g x y z ph $.
    $d f g x y z O $.  $d f g x y z P $.
    funcoppc.o $e |- O = ( oppCat ` C ) $.
    funcoppc.p $e |- P = ( oppCat ` D ) $.
    funcoppc.f $e |- ( ph -> F ( C Func D ) G ) $.
    $( A functor on categories yields a functor on the opposite categories (in
       the same direction), see definition 3.41 of [Adamek] p. 39.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    funcoppc $p |- ( ph -> F ( O Func P ) tpos G ) $=
      ( cfv cco ccid chom eqid wcel cop co wa cv vx vy vz vf ctpos oppcbas ccat
      vg cbs cfunc wbr df-br funcrcl syl simpld oppccat simpl2im funcf1 cxp wfn
      sylib funcfn2 tposfn wf adantr simprr simprl funcf2 ovtpos oppchom feq23i
      feq1i bitri sylibr funcid wceq a1i oppcid fveq1d fveq12d 3eqtr4d 3ad2ant1
      simpr simp23 simp22 simp21 simp3r eleqtrdi simp3l funcco oppcco ffvelcdmd
      w3a fveq2d fveq1i oveq12i 3eqtr4g isfuncd ) AUAUBUCBUIKZCUIKZGGLKZGMKZUDU
      HDEFUEZGNKZDMKZDNKZDLKZWSBGHWSOZUFWTCDIWTOZUFXDOXFOXBOXEOXAOXGOABUGPZGUGP
      AXJCUGPZAEFQZBCUJRZPZXJXKSAEFXMUKZXNJEFXMULVABCXLUMUNZUOZBGHUPUNAXJXKDUGP
      XPCDIUPUQAWSWTBCEFXHXIJURZAFWSWSUSZUTXCXSUTAWSBCEFXHJVBWSWSFVCUNAUATZWSPZ
      UBTZWSPZSZSZYBXTBNKZRZYBEKZXTEKZCNKZRZYBXTFRZVDZXTYBXDRZYIYHXFRZXTYBXCRZV
      DZYEWSBCEFYFYJYBXTXHYFOZYJOZAXOYDJVEAYAYCVFAYAYCVGVHYQYNYOYLVDYMYNYOYPYLX
      TYBFVIZVLYNYOYGYKYLBYFGXTYBYRHVJZCYJDYIYHYSIVJVKVMVNAYASZXTBMKZKZXTXTFRZK
      YICMKZKXTXBKZXTXTXCRZKYIXEKUUBWSBUUCCEFUUFXTXHUUCOZUUFOZAXOYAJVEAYAWCVOUU
      BUUGUUDUUHUUEUUHUUEVPUUBXTXTFVIVQUUBXTXBUUCAXBUUCVPZYAAXJUUKXQUUCBGHUUIVR
      UNVEVSVTUUBYIXEUUFAXEUUFVPZYAAXJXKUULXPUUFCDIUUJVRUQVEVSWAAYAYCUCTZWSPZWM
      ZUDTZYNPZUHTZYBUUMXDRZPZSZWMZUURUUPXTYBQUUMXARRZUUMXTFRZKZUURUUMYBFRZKZUU
      PYLKZYIYHQUUMEKZXGRZRZUVCXTUUMXCRZKUURYBUUMXCRZKZUUPYPKZUVJRUVBUUPUURUUMY
      BQXTBLKZRRZUVDKUVHUVGUVIYHQYICLKZRRUVEUVKUVBWSBUVPCEFYFUURUUPUVRUUMYBXTXH
      YRUVPOZUVROZAUUOXOUVAJWBAYAYCUUNUVAWDZAYAYCUUNUVAWEZAYAYCUUNUVAWFZUVBUURU
      USUUMYBYFRAUUOUUQUUTWGBYFGYBUUMYRHVJWHUVBUUPYNYGAUUOUUQUUTWIUUAWHWJUVBUVC
      UVQUVDUVBWSBUVPUUPUURGXTYBUUMXHUVSHUWCUWBUWAWKWNUVBWTCUVRUVHUVGDYIYHUVIXI
      UVTIUVBWSWTXTEAUUOWSWTEVDUVAXRWBZUWCWLUVBWSWTYBEUWDUWBWLUVBWSWTUUMEUWDUWA
      WLWKWAUVCUVLUVDXTUUMFVIWOUVNUVGUVOUVHUVJUURUVMUVFYBUUMFVIWOUUPYPYLYTWOWPW
      QWR $.
  $}

  ${
    $d b c z B $.  $d b c z C $.  $d b c z H $.  $d z ph $.  $d z X $.
    $d z Y $.
    idfuval.i $e |- I = ( idFunc ` C ) $.
    idfuval.b $e |- B = ( Base ` C ) $.
    idfuval.c $e |- ( ph -> C e. Cat ) $.
    ${
      idfuval.h $e |- H = ( Hom ` C ) $.
      $( Value of the identity functor.  (Contributed by Mario Carneiro,
         3-Jan-2017.) $)
      idfuval $p |- ( ph -> I =
        <. ( _I |` B ) , ( z e. ( B X. B ) |-> ( _I |` ( H ` z ) ) ) >. ) $=
        ( vc vb cidfu cfv cid cres cv wceq cbs chom cxp cmpt cop ccat csb fvexd
        wcel cvv fveq2 eqtr4di wa simpr reseq2d sqxpeqd fveq2d fveq1d mpteq12dv
        simpl opeq12d csbied2 df-idfu opex fvmpt syl eqtrid ) AFDMNZOCPZBCCUAZO
        BQZENZPZUBZUCZGADUDUGVFVMRIKDLKQZSNZOLQZPZBVPVPUAZOVIVNTNZNZPZUBZUCZUEV
        MUDMVNDRZLVOCWCVMUHWDVNSUFWDVODSNCVNDSUIHUJWDVPCRZUKZVQVGWBVLWFVPCOWDWE
        ULZUMWFBVRWAVHVKWFVPCWGUNWFVTVJOWFVIVSEWFVSDTNEWFVNDTWDWEURUOJUJUPUMUQU
        SUTBKLVAVGVLVBVCVDVE $.

      idfu2nd.x $e |- ( ph -> X e. B ) $.
      idfu2nd.y $e |- ( ph -> Y e. B ) $.
      $( Value of the morphism part of the identity functor.  (Contributed by
         Mario Carneiro, 3-Jan-2017.) $)
      idfu2nd $p |- ( ph -> ( X ( 2nd ` I ) Y ) = ( _I |` ( X H Y ) ) ) $=
        ( vz c2nd cfv cid cres cvv wcel co cop df-ov cv cxp cmpt idfuval fveq2d
        cbs fvexi resiexg ax-mp xpex mptex op2nd eqtrdi wceq wa eqtr4di reseq2d
        simpr opelxpd ovex mp1i fvmptd eqtrid ) AFGEOPZUAFGUBZVGPQFGDUAZRZFGVGU
        CANVHQNUDZDPZRZVJBBUEZVGSAVGQBRZNVNVMUFZUBZOPVPAEVQOANBCDEHIJKUGUHVOVPB
        STVOSTBCUIIUJZBSUKULNVNVMBBVRVRUMUNUOUPAVKVHUQZURZVLVIQVTVLVHDPVIVTVKVH
        DAVSVAUHFGDUCUSUTAFGBBLMVBVISTVJSTAFGDVCVISUKVDVEVF $.

      idfu2.f $e |- ( ph -> F e. ( X H Y ) ) $.
      $( Value of the morphism part of the identity functor.  (Contributed by
         Mario Carneiro, 28-Jan-2017.) $)
      idfu2 $p |- ( ph -> ( ( X ( 2nd ` I ) Y ) ` F ) = F ) $=
        ( c2nd cfv co cid cres idfu2nd fveq1d wcel wceq fvresi syl eqtrd ) ADGH
        FPQRZQDSGHERZTZQZDADUHUJABCEFGHIJKLMNUAUBADUIUCUKDUDOUIDUEUFUG $.
    $}

    $( Value of the object part of the identity functor.  (Contributed by Mario
       Carneiro, 3-Jan-2017.) $)
    idfu1st $p |- ( ph -> ( 1st ` I ) = ( _I |` B ) ) $=
      ( vz c1st cfv cid cres cxp cv chom cmpt cop eqid cvv wcel idfuval resiexg
      fveq2d cbs fvexi ax-mp xpex mptex op1st eqtrdi ) ADIJKBLZHBBMZKHNCOJZJLZP
      ZQZIJUKADUPIAHBCUMDEFGUMRUAUCUKUOBSTUKSTBCUDFUEZBSUBUFHULUNBBUQUQUGUHUIUJ
      $.

    idfu1.x $e |- ( ph -> X e. B ) $.
    $( Value of the object part of the identity functor.  (Contributed by Mario
       Carneiro, 3-Jan-2017.) $)
    idfu1 $p |- ( ph -> ( ( 1st ` I ) ` X ) = X ) $=
      ( c1st cfv cid cres idfu1st fveq1d wcel wceq fvresi syl eqtrd ) AEDJKZKEL
      BMZKZEAEUAUBABCDFGHNOAEBPUCEQIBERST $.
  $}

  ${
    $d f g x y z C $.  $d f g x y z I $.
    idfucl.i $e |- I = ( idFunc ` C ) $.
    $( The identity functor is a functor.  Example 3.20(1) of [Adamek] p. 30.
       (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    idfucl $p |- ( C e. Cat -> I e. ( C Func C ) ) $=
      ( vz vx vg vf vy wcel cid cfv cop co cv cvv wceq wral wa fvresi syl cfunc
      ccat cbs cres c2nd cxp chom cmpt eqid id idfuval fveq2d fvex resiexg xpex
      ax-mp mptex eqtrdi opeq2d eqtr4d wbr wf c1st cmap cixp ccid cco wf1o f1oi
      op2nd f1of elmap mpbir xp1st adantl xp2nd oveq12d df-ov 1st2nd2 eleqtrrid
      mp1i oveq1d ralrimiva mptelixpg sylibr eqeltrd simpl simpr catidcl fveq1d
      wb idfu2nd 3eqtr4d ad2antrr simplrl simplrr simprl simprr catcocl opeq12d
      idfu2 oveq123d ralrimivva jca isfunc mpbir3and df-br sylib ) AUBIZBJAUCKZ
      UDZBUEKZLZAAUAMZXIBXKDXJXJUFZJDNZAUGKZKZUDZUHZLZXMXIDXJAXQBCXJUIZXIUJZXQU
      IZUKZXIXLXTXKXIXLYAUEKXTXIBYAUEYEULXKXTXJOIXKOIAUCUMZXJOUNUPDXOXSXJXJYFYF
      UOZUQVJURZUSUTXIXKXLXNVAZXMXNIXIYIXJXJXKVBZXLDXOXPVCKZXKKZXPUEKZXKKZXQMZX
      RVDMZVEZIENZAVFKZKZYRYRXLMZKZYRXKKZYSKZPZFNZGNZYRHNZLZXPAVGKZMZMZYRXPXLMZ
      KZUUFUUHXPXLMKZUUGYRUUHXLMKZUUCUUHXKKZLZXPXKKZUUJMZMZPZFUUHXPXQMZQGYRUUHX
      QMZQZDXJQHXJQZRZEXJQXJXJXKVHYJXIXJVIXJXJXKVKWAXIXLXTYQYHXIXSYPIZDXOQZXTYQ
      IZXIUVHDXOXIXPXOIZRZXSXRXRVDMZYPXSUVMIXRXRXSVBZXRXRXSVHUVNXRVIXRXRXSVKUPX
      RXRXSXPXQUMZUVOVLVMUVLYOXRXRVDUVLYOYKYMLZXQKZXRUVLYOYKYMXQMUVQUVLYLYKYNYM
      XQUVLYKXJIZYLYKPUVKUVRXIXPXJXJVNVOXJYKSTUVLYMXJIZYNYMPUVKUVSXIXPXJXJVPVOX
      JYMSTVQYKYMXQVRURUVLXPUVPXQUVKXPUVPPXIXPXJXJVSVOULUTWBVTWCXOOIUVJUVIWKYGD
      XOXSYPOWDUPWEWFXIUVGEXJXIYRXJIZRZUUEUVFUWAYTJYRYRXQMZUDZKZYTUUBUUDUWAYTUW
      BIUWDYTPUWAXJAYSXQYRYBYDYSUIZXIUVTWGZXIUVTWHZWIUWBYTSTUWAYTUUAUWCUWAXJAXQ
      BYRYRCYBUWFYDUWGUWGWLWJUWAUUCYRYSUVTUUCYRPZXIXJYRSZVOULWMUWAUVEHDXJXJUWAU
      UHXJIZXPXJIZRZRZUVBGFUVDUVCUWMUUGUVDIZUUFUVCIZRZRZUULJYRXPXQMZUDZKZUULUUN
      UVAUWQUULUWRIUWTUULPUWQXJAUUJUUGUUFXQYRUUHXPYBYDUUJUIZUWAXIUWLUWPUWFWNZUW
      AUVTUWLUWPUWGWNZUWAUWJUWKUWPWOZUWAUWJUWKUWPWPZUWMUWNUWOWQZUWMUWNUWOWRZWSU
      WRUULSTUWQUULUUMUWSUWQXJAXQBYRXPCYBUXBYDUXCUXEWLWJUWQUUOUUFUUPUUGUUTUUKUW
      QUURUUIUUSXPUUJUWQUUCYRUUQUUHUWQUVTUWHUXCUWITUWQUWJUUQUUHPUXDXJUUHSTWTUWQ
      UWKUUSXPPUXEXJXPSTVQUWQXJAUUFXQBUUHXPCYBUXBYDUXDUXEUXGXAUWQXJAUUGXQBYRUUH
      CYBUXBYDUXCUXDUXFXAXBWMXCXCXDWCXIEHDXJXJAUUJYSGFAXKXLXQYSXQUUJYBYBYDYDUWE
      UWEUXAUXAYCYCXEXFXKXLXNXGXHWF $.
  $}

  ${
    $d f g x y B $.  $d f g x y F $.  $d f g x y G $.  $d f g x y ph $.
    $d x y X $.  $d x y Y $.
    cofuval.b $e |- B = ( Base ` C ) $.
    cofuval.f $e |- ( ph -> F e. ( C Func D ) ) $.
    cofuval.g $e |- ( ph -> G e. ( D Func E ) ) $.
    $( Value of the composition of two functors.  (Contributed by Mario
       Carneiro, 3-Jan-2017.) $)
    cofuval $p |- ( ph -> ( G o.func F ) =
      <. ( ( 1st ` G ) o. ( 1st ` F ) ) ,
         ( x e. B , y e. B |-> ( ( ( ( 1st ` F ) ` x ) ( 2nd ` G )
           ( ( 1st ` F ) ` y ) ) o. ( x ( 2nd ` F ) y ) ) ) >. ) $=
      ( vg vf cvv cv c1st cfv c2nd co ccom cdm cmpo cop wceq df-cofu a1i simprl
      ccofu wa fveq2d simprr coeq12d cxp dmeqd cfunc wrel wcel relfunc 1st2ndbr
      wbr sylancr funcfn2 fndmd adantr dmxpid eqtrdi fveq1d oveq123d mpoeq123dv
      eqtrd oveqd opeq12d elexd opex ovmpod ) AMNIHOOMPZQRZNPZQRZUAZBCVSSRZUBZU
      BZWDBPZVTRZCPZVTRZVQSRZTZWEWGWBTZUAZUCZUDZIQRZHQRZUAZBCDDWEWPRZWGWPRZISRZ
      TZWEWGHSRZTZUAZUCZUDZUIOUIMNOOWNUCUEABCNMUFUGAVQIUEZVSHUEZUJZUJZWAWQWMXEX
      JVRWOVTWPXJVQIQAXGXHUHZUKXJVSHQAXGXHULZUKZUMXJBCWDWDWLDDXDXJWDDDUNZUBDXJW
      CXNXJWCXBUBZXNXJWBXBXJVSHSXLUKZUOAXOXNUEXIAXNXBADEFWPXBJAEFUPTZUQHXQURWPX
      BXQVAEFUSKHXQUTVBVCVDVEVKUODVFVGZXRXJWJXAWKXCXJWFWRWHWSWIWTXJVQISXKUKXJWE
      VTWPXMVHXJWGVTWPXMVHVIXJWBXBWEWGXPVLUMVJVMAIFGUPTLVNAHXQKVNXFOURAWQXEVOUG
      VP $.

    $( Value of the object part of the functor composition.  (Contributed by
       Mario Carneiro, 3-Jan-2017.) $)
    cofu1st $p |- ( ph ->
      ( 1st ` ( G o.func F ) ) = ( ( 1st ` G ) o. ( 1st ` F ) ) ) $=
      ( vx vy ccofu co c1st cfv ccom cv c2nd fvex cmpo cop cofuval fveq2d fvexi
      coex cbs mpoex op1st eqtrdi ) AGFMNZOPGOPZFOPZQZKLBBKRZUMPLRZUMPGSPNUOUPF
      SPNQZUAZUBZOPUNAUKUSOAKLBCDEFGHIJUCUDUNURULUMGOTFOTUFKLBBUQBCUGHUEZUTUHUI
      UJ $.

    cofu2nd.x $e |- ( ph -> X e. B ) $.
    $( Value of the object part of the functor composition.  (Contributed by
       Mario Carneiro, 28-Jan-2017.) $)
    cofu1 $p |- ( ph -> ( ( 1st ` ( G o.func F ) ) ` X ) =
      ( ( 1st ` G ) ` ( ( 1st ` F ) ` X ) ) ) $=
      ( ccofu co c1st cfv ccom cofu1st fveq1d wcel wf wceq c2nd eqid cfunc wrel
      cbs wbr relfunc 1st2ndbr sylancr funcf1 fvco3 syl2anc eqtrd ) AHGFMNOPZPH
      GOPZFOPZQZPZHURPUQPZAHUPUSABCDEFGIJKRSABDUGPZURUAHBTUTVAUBABVBCDURFUCPZIV
      BUDACDUENZUFFVDTURVCVDUHCDUIJFVDUJUKULLBVBHUQURUMUNUO $.

    cofu2nd.y $e |- ( ph -> Y e. B ) $.
    $( Value of the morphism part of the functor composition.  (Contributed by
       Mario Carneiro, 3-Jan-2017.) $)
    cofu2nd $p |- ( ph ->
      ( X ( 2nd ` ( G o.func F ) ) Y ) = ( ( ( ( 1st ` F ) ` X ) ( 2nd ` G )
           ( ( 1st ` F ) ` Y ) ) o. ( X ( 2nd ` F ) Y ) ) ) $=
      ( vx vy c1st cfv c2nd co ccom ccofu cvv cmpo cop cofuval fveq2d fvex coex
      cbs fvexi mpoex op2nd eqtrdi wceq simprl simprr oveq12d coeq12d wcel ovex
      cv wa a1i ovmpod ) AOPHIBBOVBZFQRZRZPVBZVGRZGSRZTZVFVIFSRZTZUAZHVGRZIVGRZ
      VKTZHIVMTZUAZGFUBTZSRZUCAWBGQRZVGUAZOPBBVOUDZUEZSRWEAWAWFSAOPBCDEFGJKLUFU
      GWDWEWCVGGQUHFQUHUIOPBBVOBCUJJUKZWGULUMUNAVFHUOZVIIUOZVCVCZVLVRVNVSWJVHVP
      VJVQVKWJVFHVGAWHWIUPZUGWJVIIVGAWHWIUQZUGURWJVFHVIIVMWKWLURUSMNVTUCUTAVRVS
      VPVQVKVAHIVMVAUIVDVE $.

    cofu2.h $e |- H = ( Hom ` C ) $.
    cofu2.y $e |- ( ph -> R e. ( X H Y ) ) $.
    $( Value of the morphism part of the functor composition.  (Contributed by
       Mario Carneiro, 28-Jan-2017.) $)
    cofu2 $p |- ( ph -> ( ( X ( 2nd ` ( G o.func F ) ) Y ) ` R ) =
      ( ( ( ( 1st ` F ) ` X ) ( 2nd ` G ) ( ( 1st ` F ) ` Y ) ) `
        ( ( X ( 2nd ` F ) Y ) ` R ) ) ) $=
      ( co cfv ccofu c2nd c1st ccom cofu2nd fveq1d chom wf wcel wceq eqid cfunc
      wrel wbr relfunc 1st2ndbr sylancr funcf2 fvco3 syl2anc eqtrd ) AEJKHGUASU
      BTSZTEJGUCTZTZKVCTZHUBTSZJKGUBTZSZUDZTZEVHTVFTZAEVBVIABCDFGHJKLMNOPUEUFAJ
      KISZVDVEDUGTZSZVHUHEVLUIVJVKUJABCDVCVGIVMJKLQVMUKACDULSZUMGVOUIVCVGVOUNCD
      UOMGVOUPUQOPURRVLVNEVFVHUSUTVA $.
  $}

  ${
    $d x y B $.  $d x y F $.  $d x y G $.  $d x y H $.  $d x y ph $.
    $d x y K $.
    cofuval2.b $e |- B = ( Base ` C ) $.
    cofuval2.f $e |- ( ph -> F ( C Func D ) G ) $.
    cofuval2.x $e |- ( ph -> H ( D Func E ) K ) $.
    $( Value of the composition of two functors.  (Contributed by Mario
       Carneiro, 3-Jan-2017.) $)
    cofuval2 $p |- ( ph -> ( <. H , K >. o.func <. F , G >. ) = <. ( H o. F ) ,
     ( x e. B , y e. B |-> ( ( ( F ` x ) K ( F ` y ) ) o. ( x G y ) ) ) >. ) $=
      ( cop co cfv ccom wcel cvv ccofu c1st c2nd cmpo cfunc df-br sylib cofuval
      cv wbr wa wceq wrel relfunc brrelex12 sylancr op1stg syl coeq12d 3ad2ant1
      w3a op2ndg fveq1d oveq123d oveqd mpoeq3dva opeq12d eqtrd ) AJKOZHIOZUAPVI
      UBQZVJUBQZRZBCDDBUIZVLQZCUIZVLQZVIUCQZPZVNVPVJUCQZPZRZUDZOJHRZBCDDVNHQZVP
      HQZKPZVNVPIPZRZUDZOABCDEFGVJVILAHIEFUEPZUJZVJWKSMHIWKUFUGAJKFGUEPZUJZVIWM
      SNJKWMUFUGUHAVMWDWCWJAVKJVLHAJTSKTSUKZVKJULAWMUMWNWOFGUNNJKWMUOUPZJKTTUQU
      RAHTSITSUKZVLHULZAWKUMWLWQEFUNMHIWKUOUPZHITTUQURZUSABCDDWBWIAVNDSZVPDSZVA
      ZVSWGWAWHXCVOWEVQWFVRKAXAVRKULZXBAWOXDWPJKTTVBURUTXCVNVLHAXAWRXBWTUTZVCXC
      VPVLHXEVCVDXCVTIVNVPAXAVTIULZXBAWQXFWSHITTVBURUTVEUSVFVGVH $.
  $}

  ${
    $d f g x y z C $.  $d f g x y z E $.  $d f g x y z F $.  $d f g x y z ph $.
    $d f g x y z G $.
    cofucl.f $e |- ( ph -> F e. ( C Func D ) ) $.
    cofucl.g $e |- ( ph -> G e. ( D Func E ) ) $.
    $( The composition of two functors is a functor.  Proposition 3.23 of
       [Adamek] p. 33.  (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    cofucl $p |- ( ph -> ( G o.func F ) e. ( C Func E ) ) $=
      ( vx vy vz co cfv c2nd eqid wcel wf wral wa adantr vg vf ccofu c1st cfunc
      cop ccom cbs cv cmpo cofuval cofu1st fveq2d fvex coex mpoex op2nd opeq12d
      eqtrdi wbr cxp chom cmap cixp ccid wceq cco wrel relfunc 1st2ndbr sylancr
      eqtr4d funcf1 fco syl2anc feq1d mpbird wfn fnmpoi fneq1d mpbiri ffvelcdmd
      simprl simprr funcf2 elmap sylibr cofu2nd cofu1 oveq12d oveq1d ralrimivva
      ovex 3eltr4d fveq2 df-ov eqtr4di vex op1std op2ndd eleq12d ralxp sylanbrc
      elixp simpr funcid ffvelcdmda eqtrd ccat funcrcl syl simpld catidcl cofu2
      3eqtr4d simplr simprlr simprll simprrl simprrr fvco3 funcco 3eqtrd fveq1d
      catcocl anassrs jca ralrimiva simprd isfunc mpbir3and df-br sylib eqeltrd
      oveq123d ) AFEUCLZYPUDMZYPNMZUFZBDUELZAYPFUDMZEUDMZUGZIJBUHMZUUDIUIZUUBMZ
      JUIZUUBMZFNMZLZUUEUUGENMZLZUGZUJZUFZYSAIJUUDBCDEFUUDOZGHUKZAYQUUCYRUUNAUU
      DBCDEFUUPGHULZAYRUUONMUUNAYPUUONUUQUMUUCUUNUUAUUBFUDUNEUDUNUOIJUUDUUDUUMB
      UHUNZUUSUPUQUSZURVLAYQYRYTUTZYSYTPAUVAUUDDUHMZYQQZYRKUUDUUDVAZKUIZUDMZYQM
      ZUVENMZYQMZDVBMZLZUVEBVBMZMZVCLZVDPZUUEBVEMZMZUUEUUEYRLMZUUEYQMZDVEMZMZVF
      ZUAUIZUBUIZUUEUUGUFZUVEBVGMZLLZUUEUVEYRLZMZUWCUUGUVEYRLMZUWDUUEUUGYRLZMZU
      VSUUGYQMZUFZUVEYQMZDVGMZLZLZVFZUAUUGUVEUVLLZRUBUUEUUGUVLLZRZKUUDRJUUDRZSZ
      IUUDRAUVCUUDUVBUUCQZACUHMZUVBUUAQUUDUXFUUBQZUXEAUXFUVBCDUUAUUIUXFOZUVBOZA
      CDUELZVHFUXJPZUUAUUIUXJUTZCDVIHFUXJVJVKZVMAUUDUXFBCUUBUUKUUPUXHABCUELZVHE
      UXNPZUUBUUKUXNUTZBCVIGEUXNVJVKZVMZUUDUXFUVBUUAUUBVNVOAUUDUVBYQUUCUURVPVQA
      YRUVDVRZUVEYRMZUVNPZKUVDRZUVOAUXSUUNUVDVRIJUUDUUDUUMUUNUUNOUUJUULUUFUUHUU
      IWMUUEUUGUUKWMUOVSAUVDYRUUNUUTVTWAAUWKUVSUWMUVJLZUXAVCLZPZJUUDRIUUDRUYBAU
      YEIJUUDUUDAUUEUUDPZUUGUUDPZSZSZUUMUUFUUAMZUUHUUAMZUVJLZUXAVCLZUWKUYDUYIUX
      AUYLUUMQZUUMUYMPUYIUUFUUHCVBMZLZUYLUUJQUXAUYPUULQUYNUYIUXFCDUUAUUIUYOUVJU
      UFUUHUXHUYOOZUVJOZAUXLUYHUXMTUYIUUDUXFUUEUUBAUXGUYHUXRTZAUYFUYGWCZWBUYIUU
      DUXFUUGUUBUYSAUYFUYGWDZWBWEUYIUUDBCUUBUUKUVLUYOUUEUUGUUPUVLOZUYQAUXPUYHUX
      QTUYTVUAWEUXAUYPUYLUUJUULVNVOUYLUXAUUMUYJUYKUVJWMUUEUUGUVLWMWFWGUYIUUDBCD
      EFUUEUUGUUPAUXOUYHGTZAUXKUYHHTZUYTVUAWHUYIUYCUYLUXAVCUYIUVSUYJUWMUYKUVJUY
      IUUDBCDEFUUEUUPVUCVUDUYTWIUYIUUDBCDEFUUGUUPVUCVUDVUAWIWJWKWNWLUYAUYEKIJUU
      DUUDUVEUWEVFZUXTUWKUVNUYDVUEUXTUWEYRMUWKUVEUWEYRWOUUEUUGYRWPWQVUEUVKUYCUV
      MUXAVCVUEUVGUVSUVIUWMUVJVUEUVFUUEYQUUEUUGUVEIWRZJWRZWSUMVUEUVHUUGYQUUEUUG
      UVEVUFVUGWTUMWJVUEUVMUWEUVLMUXAUVEUWEUVLWOUUEUUGUVLWPWQWJXAXBWGKUVDUVNYRY
      PNUNXDXCAUXDIUUDAUYFSZUWBUXCVUHUVQUUEUUEUUKLMZUUFUUFUUILZMZUYJUVTMZUVRUWA
      VUHVUKUUFCVEMZMZVUJMVULVUHVUIVUNVUJVUHUUDBUVPCUUBUUKVUMUUEUUPUVPOZVUMOZAU
      XPUYFUXQTZAUYFXEZXFUMVUHUXFCVUMDUUAUUIUVTUUFUXHVUPUVTOZAUXLUYFUXMTZAUUDUX
      FUUEUUBUXRXGZXFXHVUHUUDBCUVQDEFUVLUUEUUEUUPAUXOUYFGTZAUXKUYFHTZVURVURVUBV
      UHUUDBUVPUVLUUEUUPVUBVUOABXIPZUYFAVVDCXIPZAUXOVVDVVESGBCEXJXKXLZTZVURXMXN
      VUHUVSUYJUVTVUHUUDBCDEFUUEUUPVVBVVCVURWIZUMXOVUHUXBJKUUDUUDVUHUYGUVEUUDPZ
      SZSUWSUBUAUXAUWTVUHVVJUWDUXAPZUWCUWTPZSZUWSVUHVVJVVMSZSZUWGUUFUVEUUBMZUUI
      LZUUEUVEUUKLZUGZMZUWCUUGUVEUUKLZMZUUHVVPUUILMZUWDUULMZUUJMZUYJUYKUFZVVPUU
      AMZUWPLZLZUWIUWRVVOVVTUWGVVRMZVVQMZVWBVWDUUFUUHUFVVPCVGMZLLZVVQMVWIVVOUUE
      UVEUVLLZUUFVVPUYOLZVVRQUWGVWNPVVTVWKVFVVOUUDBCUUBUUKUVLUYOUUEUVEUUPVUBUYQ
      VUHUXPVVNVUQTZAUYFVVNXPZVUHUYGVVIVVMXQZWEVVOUUDBUWFUWDUWCUVLUUEUUGUVEUUPV
      UBUWFOZVUHVVDVVNVVGTVWQVUHUYGVVIVVMXRZVWRVUHVVJVVKVVLXSZVUHVVJVVKVVLXTZYE
      VWNVWOUWGVVQVVRYAVOVVOVWJVWMVVQVVOUUDBUWFCUUBUUKUVLUWDUWCVWLUUEUUGUVEUUPV
      UBVWSVWLOZVWPVWQVWTVWRVXAVXBYBUMVVOUXFCVWLDUUAUUIUYOVWDVWBUWPUUFUUHVVPUXH
      UYQVXCUWPOZVUHUXLVVNVUTTVUHUUFUXFPVVNVVATVVOUUDUXFUUGUUBVUHUXGVVNAUXGUYFU
      XRTTZVWTWBVVOUUDUXFUVEUUBVXEVWRWBVVOUXAUYPUWDUULVVOUUDBCUUBUUKUVLUYOUUEUU
      GUUPVUBUYQVWPVWQVWTWEVXAWBVVOUWTUUHVVPUYOLUWCVWAVVOUUDBCUUBUUKUVLUYOUUGUV
      EUUPVUBUYQVWPVWTVWRWEVXBWBYBYCVVOUWGUWHVVSVVOUUDBCDEFUUEUVEUUPVUHUXOVVNVV
      BTZVUHUXKVVNVVCTZVWQVWRWHYDVVOUWJVWCUWLVWEUWQVWHVVOUWNVWFUWOVWGUWPVVOUVSU
      YJUWMUYKVUHUVSUYJVFVVNVVHTVVOUUDBCDEFUUGUUPVXFVXGVWTWIURVVOUUDBCDEFUVEUUP
      VXFVXGVWRWIWJVVOUUDBCUWCDEFUVLUUGUVEUUPVXFVXGVWTVWRVUBVXBXNVVOUUDBCUWDDEF
      UVLUUEUUGUUPVXFVXGVWQVWTVUBVXAXNYOXOYFWLWLYGYHAIJKUUDUVBBUWFUVPUBUADYQYRU
      VLUVTUVJUWPUUPUXIVUBUYRVUOVUSVWSVXDVVFAVVEDXIPZAUXKVVEVXHSHCDFXJXKYIYJYKY
      QYRYTYLYMYN $.
  $}

  ${
    $d x y C $.  $d x y G $.  $d x y H $.  $d x y K $.  $d x y ph $.
    cofuass.g $e |- ( ph -> G e. ( C Func D ) ) $.
    cofuass.h $e |- ( ph -> H e. ( D Func E ) ) $.
    cofuass.k $e |- ( ph -> K e. ( E Func F ) ) $.
    $( Functor composition is associative.  (Contributed by Mario Carneiro,
       3-Jan-2017.) $)
    cofuass $p |- ( ph ->
      ( ( K o.func H ) o.func G ) = ( K o.func ( H o.func G ) ) ) $=
      ( vx vy ccofu co c1st cfv ccom c2nd wcel cbs cv cmpo coass cofu1st coeq1d
      cop coeq2d 3eqtr4a w3a cfunc 3ad2ant1 wbr relfunc 1st2ndbr sylancr funcf1
      eqid wrel simp2 ffvelcdmd simp3 cofu2nd oveq12d coeq12d mpoeq3dva opeq12d
      cofu1 cofucl cofuval 3eqtr4d ) AHGNOZPQZFPQZRZLMBUAQZVPLUBZVNQZMUBZVNQZVL
      SQOZVQVSFSQZOZRZUCZUGHPQZGFNOZPQZRZLMVPVPVQWHQZVSWHQZHSQZOZVQVSWGSQOZRZUC
      ZUGVLFNOHWGNOAVOWIWEWPAWFGPQZRZVNRWFWQVNRZRVOWIWFWQVNUDAVMWRVNACUAQZCDEGH
      WTURZJKUEUFAWHWSWFAVPBCDFGVPURZIJUEUHUIALMVPVPWDWOAVQVPTZVSVPTZUJZVRWQQZV
      TWQQZWLOZVRVTGSQOZRZWCRXHXIWCRZRWDWOXHXIWCUDXEWAXJWCXEWTCDEGHVRVTXAAXCGCD
      UKOTXDJULZAXCHDEUKOTXDKULXEVPWTVQVNXEVPWTBCVNWBXBXAAXCVNWBBCUKOZUMZXDAXMU
      SFXMTZXNBCUNIFXMUOUPULUQZAXCXDUTZVAXEVPWTVSVNXPAXCXDVBZVAVCUFXEWMXHWNXKXE
      WJXFWKXGWLXEVPBCDFGVQXBAXCXOXDIULZXLXQVHXEVPBCDFGVSXBXSXLXRVHVDXEVPBCDFGV
      QVSXBXSXLXQXRVCVEUIVFVGALMVPBCEFVLXBIACDEGHJKVIVJALMVPBDEWGHXBABCDFGIJVIK
      VJVK $.
  $}

  ${
    $d x y C $.  $d x D $.  $d x y F $.  $d x y I $.  $d x y ph $.
    cofulid.g $e |- ( ph -> F e. ( C Func D ) ) $.
    ${
      cofulid.1 $e |- I = ( idFunc ` D ) $.
      $( The identity functor is a left identity for composition.  (Contributed
         by Mario Carneiro, 3-Jan-2017.) $)
      cofulid $p |- ( ph -> ( I o.func F ) = F ) $=
        ( vx vy c1st cfv ccom cbs cv c2nd co eqid wcel syl wceq cmpo ccofu cres
        cop cid ccat cfunc wa funcrcl simprd idfu1st coeq1d wf wrel wbr relfunc
        1st2ndbr sylancr funcf1 fcoi2 eqtrd w3a chom ffvelcdmda 3adant3 3adant2
        3ad2ant1 idfu2nd simp2 simp3 funcf2 mpoeq3dva cxp wfn fnov sylib eqtr4d
        funcfn2 opeq12d idfucl cofuval 1st2nd 3eqtr4d ) AEJKZDJKZLZHIBMKZWGHNZW
        EKZINZWEKZEOKPZWHWJDOKZPZLZUAZUDWEWMUDZEDUBPDAWFWEWPWMAWFUECMKZUCZWELZW
        EAWDWSWEAWRCEGWRQZABUFRZCUFRZADBCUGPZRZXBXCUHFBCDUISUJZUKULAWGWRWEUMWTW
        ETAWGWRBCWEWMWGQZXAAXDUNZXEWEWMXDUOZBCUPZFDXDUQURZUSZWGWRWEUTSVAAWPHIWG
        WGWNUAZWMAHIWGWGWOWNAWHWGRZWJWGRZVBZWOUEWIWKCVCKZPZUCZWNLZWNXPWLXSWNXPW
        RCXQEWIWKGXAAXNXCXOXFVGXQQZAXNWIWRRXOAWGWRWHWEXLVDVEAXOWKWRRXNAWGWRWJWE
        XLVDVFVHULXPWHWJBVCKZPZXRWNUMXTWNTXPWGBCWEWMYBXQWHWJXGYBQYAAXNXIXOXKVGA
        XNXOVIAXNXOVJVKYCXRWNUTSVAVLAWMWGWGVMVNWMXMTAWGBCWEWMXGXKVRHIWGWGWMVOVP
        VQVSAHIWGBCCDEXGFAXCECCUGPRXFCEGVTSWAAXHXEDWQTXJFDXDWBURWC $.
    $}

    ${
      cofurid.1 $e |- I = ( idFunc ` C ) $.
      $( The identity functor is a right identity for composition.
         (Contributed by Mario Carneiro, 3-Jan-2017.) $)
      cofurid $p |- ( ph -> ( F o.func I ) = F ) $=
        ( vx vy c1st cfv ccom cbs co eqid wcel syl wceq eqtrd 3ad2ant1 c2nd cop
        cv cmpo ccofu cid cres ccat cfunc wa funcrcl simpld idfu1st coeq2d wrel
        wf wbr relfunc 1st2ndbr sylancr funcf1 fcoi1 w3a fveq1d fvresi 3ad2ant2
        chom 3ad2ant3 oveq12d simp2 simp3 idfu2nd coeq12d mpoeq3dva cxp funcfn2
        funcf2 wfn fnov sylib eqtr4d opeq12d idfucl cofuval 1st2nd 3eqtr4d ) AD
        JKZEJKZLZHIBMKZWJHUCZWHKZIUCZWHKZDUAKZNZWKWMEUAKNZLZUDZUBWGWOUBZDEUENDA
        WIWGWSWOAWIWGUFWJUGZLZWGAWHXAWGAWJBEGWJOZABUHPZCUHPZADBCUINZPZXDXEUJFBC
        DUKQULZUMZUNAWJCMKZWGUPXBWGRAWJXJBCWGWOXCXJOAXFUOZXGWGWOXFUQZBCURZFDXFU
        SUTZVAWJXJWGVBQSAWSHIWJWJWKWMWONZUDZWOAHIWJWJWRXOAWKWJPZWMWJPZVCZWRXOUF
        WKWMBVGKZNZUGZLZXOXSWPXOWQYBXSWLWKWNWMWOXSWLWKXAKZWKXSWKWHXAAXQWHXARXRX
        ITZVDXQAYDWKRXRWJWKVEVFSXSWNWMXAKZWMXSWMWHXAYEVDXRAYFWMRXQWJWMVEVHSVIXS
        WJBXTEWKWMGXCAXQXDXRXHTXTOZAXQXRVJZAXQXRVKZVLVMXSYAWKWGKWMWGKCVGKZNZXOU
        PYCXORXSWJBCWGWOXTYJWKWMXCYGYJOAXQXLXRXNTYHYIVQYAYKXOVBQSVNAWOWJWJVOVRW
        OXPRAWJBCWGWOXCXNVPHIWJWJWOVSVTWAWBAHIWJBBCEDXCAXDEBBUINPXHBEGWCQFWDAXK
        XGDWTRXMFDXFWEUTWF $.
    $}
  $}

  ${
    $d f h x z F $.  $d x y z G $.  $d f h x y z H $.  $d f h x z ph $.
    $d x y z S $.
    resfval.c $e |- ( ph -> F e. V ) $.
    resfval.d $e |- ( ph -> H e. W ) $.
    $( Value of the functor restriction operator.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    resfval $p |- ( ph -> ( F |`f H ) =
      <. ( ( 1st ` F ) |` dom dom H ) , ( x e. dom H |->
        ( ( ( 2nd ` F ) ` x ) |` ( H ` x ) ) ) >. ) $=
      ( vf vh cvv cv c1st cfv cdm cres c2nd cmpt cop wceq cresf cmpo df-resf wa
      a1i simprl fveq2d simprr dmeqd reseq12d mpteq12dv opeq12d elexd wcel opex
      fveq1d ovmpod ) AIJCDKKILZMNZJLZOZOZPZBVABLZURQNZNZVDUTNZPZRZSZCMNZDOZOZP
      ZBVLVDCQNZNZVDDNZPZRZSZUAKUAIJKKVJUBTABIJUCUEAURCTZUTDTZUDUDZVCVNVIVSWCUS
      VKVBVMWCURCMAWAWBUFZUGWCVAVLWCUTDAWAWBUHZUIZUIUJWCBVAVHVLVRWFWCVFVPVGVQWC
      VDVEVOWCURCQWDUGUPWCVDUTDWEUPUJUKULACEGUMADFHUMVTKUNAVNVSUOUEUQ $.

    resfval2.g $e |- ( ph -> G e. X ) $.
    resfval2.d $e |- ( ph -> H Fn ( S X. S ) ) $.
    $( Value of the functor restriction operator.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    resfval2 $p |- ( ph -> ( <. F , G >. |`f H ) = <. ( F |` S ) ,
      ( x e. S , y e. S |-> ( ( x G y ) |` ( x H y ) ) ) >. ) $=
      ( vz cop co cfv cdm cres c1st cv c2nd cmpt cmpo cvv wcel opex a1i resfval
      cresf op1stg syl2anc cxp fndmd dmeqd dmxpid eqtrdi reseq12d op2ndg fveq1d
      wceq reseq1d mpteq12dv fveq2 df-ov eqtr4di mpompt opeq12d eqtrd ) AEFPZGU
      KQVKUARZGSZSZTZOVMOUBZVKUCRZRZVPGRZTZUDZPEDTZBCDDBUBZCUBZFQZWCWDGQZTZUEZP
      AOVKGUFIVKUFUGAEFUHUILUJAVOWBWAWHAVLEVNDAEHUGZFJUGZVLEVBKMEFHJULUMAVNDDUN
      ZSDAVMWKAWKGNUOZUPDUQURUSAWAOWKVPFRZVSTZUDWHAOVMVTWKWNWLAVRWMVSAVPVQFAWIW
      JVQFVBKMEFHJUTUMVAVCVDBCODDWNWGVPWCWDPZVBZWMWEVSWFWPWMWOFRWEVPWOFVEWCWDFV
      FVGWPVSWOGRWFVPWOGVEWCWDGVFVGUSVHURVIVJ $.
  $}

  ${
    $d z F $.  $d z H $.  $d z ph $.  $d z X $.  $d z Y $.
    resf1st.f $e |- ( ph -> F e. V ) $.
    resf1st.h $e |- ( ph -> H e. W ) $.
    resf1st.s $e |- ( ph -> H Fn ( S X. S ) ) $.
    $( Value of the functor restriction operator on objects.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)
    resf1st $p |- ( ph -> ( 1st ` ( F |`f H ) ) = ( ( 1st ` F ) |` S ) ) $=
      ( vz cresf co c1st cfv cdm cres cv c2nd cvv wcel cmpt resfval fveq2d wceq
      cop fvex resex dmexg mptexg 3syl op1stg sylancr fndmd dmeqd dmxpid eqtrdi
      cxp reseq2d 3eqtrd ) ACDKLZMNCMNZDOZOZPZJVBJQZCRNNVEDNPZUAZUEZMNZVDVABPAU
      TVHMAJCDEFGHUBUCAVDSTVGSTZVIVDUDVAVCCMUFUGADFTVBSTVJHDFUHJVBVFSUIUJVDVGSS
      UKULAVCBVAAVCBBUQZOBAVBVKAVKDIUMUNBUOUPURUS $.

    resf2nd.x $e |- ( ph -> X e. S ) $.
    resf2nd.y $e |- ( ph -> Y e. S ) $.
    $( Value of the functor restriction operator on morphisms.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)
    resf2nd $p |- ( ph ->
      ( X ( 2nd ` ( F |`f H ) ) Y ) = ( ( X ( 2nd ` F ) Y ) |` ( X H Y ) ) ) $=
      ( vz co c2nd cfv cres cvv wcel cresf cop df-ov cv cdm c1st resfval fveq2d
      cmpt wceq fvex resex dmexg mptexg 3syl op2ndg sylancr eqtrd simpr eqtr4di
      wa reseq12d cxp opelxpd fndmd eleqtrrd ovex a1i fvmptd eqtrid ) AGHCDUAOZ
      PQZOGHUBZVLQGHCPQZOZGHDOZRZGHVLUCANVMNUDZVNQZVRDQZRZVQDUEZVLSAVLCUFQZWBUE
      ZRZNWBWAUIZUBZPQZWFAVKWGPANCDEFIJUGUHAWESTWFSTZWHWFUJWCWDCUFUKULADFTWBSTW
      IJDFUMNWBWASUNUOWEWFSSUPUQURAVRVMUJZVAZVSVOVTVPWKVSVMVNQVOWKVRVMVNAWJUSZU
      HGHVNUCUTWKVTVMDQVPWKVRVMDWLUHGHDUCUTVBAVMBBVCZWBAGHBBLMVDAWMDKVEVFVQSTAV
      OVPGHVNVGULVHVIVJ $.
  $}

  ${
    $d f g x y z C $.  $d f g x y z D $.  $d f g x y z F $.  $d f g x y z ph $.
    $d f g x y z H $.
    funcres.f $e |- ( ph -> F e. ( C Func D ) ) $.
    funcres.h $e |- ( ph -> H e. ( Subcat ` C ) ) $.
    $( A functor restricted to a subcategory is a functor.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)
    funcres $p |- ( ph -> ( F |`f H ) e. ( ( C |`cat H ) Func D ) ) $=
      ( vz cfv cres cvv wcel eqtrd eqid adantr eleqtrrd sseldd fvresd 3ad2ant1
      co vx vy vf vg cresf c1st cdm c2nd cop cresc cfunc cv cmpt resfval fveq2d
      csubc wceq fvex resex dmexg mptexg 3syl op2ndg sylancr opeq2d wbr cbs cco
      eqtr4d ccid chom subccat ccat wa funcrcl syl simprd wrel relfunc 1st2ndbr
      wf funcf1 eqidd subcfn subcss1 fssresd simpld rescbas feq2d mpbid wfn cxp
      fnmpti eqcomd fndm sqxpeqd fneq12d mpbii wss simprl simprr funcf2 subcss2
      resf2nd feq1d mpbird reschom oveq12d feq23d eleq2d biimpar subcid fveq12d
      oveqd eqsstrrd sselda funcid subcidcl 3eqtr4d simp21 simp22 simp23 simp3l
      simp3r subccocl funcco rescco opeq12d fveq1d oveq123d isfuncd df-br sylib
      w3a eqeltrd ) ADEUETZDUFIZEUGZUGZJZYPUHIZUIZBEUJTZCUKTZAYPYTHYRHULZDUHIZI
      ZUUEEIZJZUMZUIZUUBAHDEBCUKTZBUPIZFGUNZAUUAUUJYTAUUAUUKUHIZUUJAYPUUKUHUUNU
      OAYTKLUUJKLZUUOUUJUQYQYSDUFURUSAEUUMLZYRKLUUPGEUUMUTHYRUUIKVAVBYTUUJKKVCV
      DMZVEVIAYTUUAUUDVFUUBUUDLAUAUBHUUCVGIZCVGIZUUCUUCVHIZUUCVJIZUCUDCYTUUAUUC
      VKIZCVJIZCVKIZCVHIZUUSNUUTNZUVCNUVENZUVBNUVDNZUVANUVFNZABUUCEUUCNZGVLABVM
      LZCVMLZADUULLZUVLUVMVNFBCDVOVPZVQAYSUUTYTWAUUSUUTYTWAABVGIZUUTYSYQAUVPUUT
      BCYQUUFUVPNZUVGAUULVRUVNYQUUFUULVFZBCVSFDUULVTVDZWBAUVPBYSEGABYSEGAYSWCWD
      ZUVQWEZWFAYSUUSUUTYTAUVPBUUCYSEVMUVKUVQAUVLUVMUVOWGZUVTUWAWHZWIWJAUUJYRWK
      UUAUUSUUSWLZWKHYRUUIUUJUUGUUHUUEUUFURUSUUJNWMAYRUWDUUJUUAAUUAUUJUURWNAYRY
      SYSWLZUWDAEUWEWKZYRUWEUQUVTUWEEWOVPAYSUUSUWCWPMWQWRAUAULZUUSLZUBULZUUSLZV
      NZVNZUWGUWIETZUWGYQIZUWIYQIZUVETZUWGUWIUUATZWAZUWGUWIUVCTZUWGYTIZUWIYTIZU
      VETZUWQWAUWLUWRUWMUWPUWGUWIUUFTZUWMJZWAUWLUWGUWIBVKIZTZUWPUWMUXCUWLUVPBCY
      QUUFUXEUVEUWGUWIUVQUXENZUVHAUVRUWKUVSOUWLYSUVPUWGAYSUVPWSZUWKUWAOZUWLUWGU
      USYSAUWHUWJWTAYSUUSUQZUWKUWCOZPZQUWLYSUVPUWIUXIUWLUWIUUSYSAUWHUWJXAUXKPZQ
      XBUWLBYSUXEEUWGUWIAUUQUWKGOZAUWFUWKUVTOZUXGUXLUXMXCWFUWLUWMUWPUWQUXDUWLYS
      DEUULUUMUWGUWIAUVNUWKFOUXNUXOUXLUXMXDXEXFUWLUWMUWPUWSUXBUWQUWLEUVCUWGUWIA
      EUVCUQZUWKAUVPBUUCYSEVMUVKUVQUWBUVTUWAXGZOXNUWLUXBUWPUWLUWTUWNUXAUWOUVEUW
      LUWGYSYQUXLRUWLUWIYSYQUXMRXHWNXIWJAUWHVNZUWGUVBIZUWGUWGUUATZIUWGBVJIZIZUW
      GUWGUUFTZUWGUWGETZJZIZUWTUVDIZUXRUXSUYBUXTUYEUXRYSDEUULUUMUWGUWGAUVNUWHFO
      AUUQUWHGOZAUWFUWHUVTOZAUWGYSLUWHAYSUUSUWGUWCXJXKZUYJXDUXRUYBUXSUXRBUUCYSU
      YAEUWGUVKUYHUYIUYANZUYJXLWNXMUXRUYBUYCIUWNUVDIUYFUYGUXRUVPBUYACYQUUFUVDUW
      GUVQUYKUVIAUVRUWHUVSOAUUSUVPUWGAUUSYSUVPUWCUWAXOXPXQUXRUYBUYDUYCUXRBYSUYA
      EUWGUYHUYIUYJUYKXRRUXRUWTUWNUVDUXRUWGYSYQUYJRUOXSMAUWHUWJUUEUUSLZYNZUCULZ
      UWSLZUDULZUWIUUEUVCTZLZVNZYNZUYPUYNUWGUWIUIZUUEBVHIZTZTZUWGUUEUUFTZUWGUUE
      ETZJZIZUYPUWIUUEUUFTZIZUYNUXCIZUWNUWOUIZUUEYQIZUVFTZTZUYPUYNVUAUUEUVATZTZ
      UWGUUEUUATZIUYPUWIUUEUUATZIZUYNUWQIZUWTUXAUIZUUEYTIZUVFTZTUYTVUHVUDVUEIVU
      OUYTVUDVUFVUEUYTBYSVUBUYNUYPEUWGUWIUUEAUYMUUQUYSGSZAUYMUWFUYSUVTSZUYTUWGU
      USYSAUWHUWJUYLUYSXTAUYMUXJUYSUWCSZPZVUBNZUYTUWIUUSYSAUWHUWJUYLUYSYAVVGPZU
      YTUUEUUSYSAUWHUWJUYLUYSYBVVGPZUYTUYNUWSUWMAUYMUYOUYRYCUYTEUVCUWGUWIAUYMUX
      PUYSUXQSZXNPZUYTUYPUYQUWIUUEETZAUYMUYOUYRYDUYTEUVCUWIUUEVVLXNPZYERUYTUVPB
      VUBCYQUUFUXEUYNUYPUVFUWGUWIUUEUVQUXGVVIUVJAUYMUVRUYSUVSSUYTYSUVPUWGAUYMUX
      HUYSUWASZVVHQUYTYSUVPUWIVVPVVJQUYTYSUVPUUEVVPVVKQUYTUWMUXFUYNUYTBYSUXEEUW
      GUWIVVEVVFUXGVVHVVJXCVVMQUYTVVNUWIUUEUXETUYPUYTBYSUXEEUWIUUEVVEVVFUXGVVJV
      VKXCVVOQYFMUYTVUQVUDVURVUGUYTYSDEUULUUMUWGUUEAUYMUVNUYSFSZVVEVVFVVHVVKXDU
      YTVUPVUCUYPUYNUYTUVAVUBVUAUUEUYTVUBUVAAUYMVUBUVAUQUYSAUVPBUUCYSVUBEVMUVKU
      VQUWBUVTUWAVVIYGSWNXNXNXMUYTVUTVUJVVAVUKVVDVUNUYTVVBVULVVCVUMUVFUYTUWTUWN
      UXAUWOUYTUWGYSYQVVHRUYTUWIYSYQVVJRYHUYTUUEYSYQVVKRXHUYTVUTUYPVUIVVNJZIVUJ
      UYTUYPVUSVVRUYTYSDEUULUUMUWIUUEVVQVVEVVFVVJVVKXDYIUYTUYPVVNVUIVVORMUYTVVA
      UYNUXDIVUKUYTUYNUWQUXDUYTYSDEUULUUMUWGUWIVVQVVEVVFVVHVVJXDYIUYTUYNUWMUXCV
      VMRMYJXSYKYTUUAUUDYLYMYO $.
  $}

  ${
    $d f g x y z A $.  $d f g x y z C $.  $d f g x y z D $.  $d f g x y z ph $.
    $d f g x y z F $.  $d f g x y z G $.  $d f g x y z H $.  $d f g x y z R $.
    funcres2b.a $e |- A = ( Base ` C ) $.
    funcres2b.h $e |- H = ( Hom ` C ) $.
    funcres2b.r $e |- ( ph -> R e. ( Subcat ` D ) ) $.
    funcres2b.s $e |- ( ph -> R Fn ( S X. S ) ) $.
    funcres2b.1 $e |- ( ph -> F : A --> S ) $.
    funcres2b.2 $e |- ( ( ph /\ ( x e. A /\ y e. A ) ) ->
      ( x G y ) : Y --> ( ( F ` x ) R ( F ` y ) ) ) $.
    $( Condition for a functor to also be a functor into the restriction.
       (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    funcres2b $p |- ( ph ->
      ( F ( C Func D ) G <-> F ( C Func ( D |`cat R ) ) G ) ) $=
      ( co cfv vz vg vf ccat wcel cfunc wbr cresc wi cop wa df-br funcrcl sylbi
      simpld a1i wb cbs wf cxp c1st c2nd chom cmap cixp ccid wceq cco wral eqid
      cv w3a subcss1 fssd csubc subcrcl syl rescbas feq3d mpbid 2thd adantr cvv
      wfn crn wss adantlr ad2antrr simprl ffvelcdmd simprr subcss2 sstrd anbi2d
      frnd df-f 3bitr4g reschom oveqd bitrd ralrimivva fveq2 eqtr4di vex op1std
      df-ov fveq2d op2ndd oveq12d eleq12d ovex elmap bitrdi bibi12d ralxp ralbi
      sylibr 3anbi3d elixp2 ffvelcdmda subcid eqeq2d 2ralbidv anbi12d 3anbi123d
      rescco ralbidva simpr isfunc subccat 3bitr4d ex pm5.21ndd ) AEUDUEZIJEFUF
      SZUGZIJEFGUHSZUFSZUGZYPYNUIAYPYNFUDUEZYPIJUJZYOUEYNYTUKIJYOULEFUUAUMUNUOU
      PYSYNUIAYSYNYQUDUEZYSUUAYRUEYNUUBUKIJYRULEYQUUAUMUNUOUPAYNYPYSUQAYNUKZDFU
      RTZIUSZJUADDUTZUAVKZVATZITZUUGVBTZITZFVCTZSZUUGKTZVDSZVEUEZBVKZEVFTZTUUQU
      UQJSTZUUQITZFVFTZTZVGZUBVKZUCVKZUUQCVKZUJZUUGEVHTZSSUUQUUGJSTZUVDUVFUUGJS
      TZUVEUUQUVFJSZTZUUTUVFITZUJZUUGITZFVHTZSZSZVGZUBUVFUUGKSZVIUCUUQUVFKSZVIZ
      UADVICDVIZUKZBDVIZVLDYQURTZIUSZJUAUUFUUIUUKYQVCTZSZUUNVDSZVEUEZUUSUUTYQVF
      TZTZVGZUVIUVJUVLUVNUVOYQVHTZSZSZVGZUBUVTVIUCUWAVIZUADVICDVIZUKZBDVIZVLYPY
      SUUCUUEUWGUUPUWKUWEUXBAUUEUWGUQYNAUUEUWGADHUUDIQAUUDFHGOPUUDVJZVMZVNADHIU
      SZUWGQAHUWFIDAUUDFYQHGUDYQVJZUXCAGFVOTUEZYTOFGVPVQZPUXDVRVSVTWAWBUUCJWCUE
      ZJUUFWDZUUGJTZUUOUEZUAUUFVIZVLUXIUXJUXKUWJUEZUAUUFVIZVLUUPUWKUUCUXMUXOUXI
      UXJUUCUXLUXNUQZUAUUFVIZUXMUXOUQUUCUWAUUTUVMUULSZUVKUSZUWAUUTUVMUWHSZUVKUS
      ZUQZCDVIBDVIUXQUUCUYBBCDDUUCUUQDUEZUVFDUEZUKZUKZUXSUWAUUTUVMGSZUVKUSZUYAU
      YFUVKUWAWDZUVKWEZUXRWFZUKUYIUYJUYGWFZUKUXSUYHUYFUYKUYLUYIUYFUYKUYLUYFUYJU
      YGUXRUYFLUYGUVKAUYELUYGUVKUSYNRWGWOZUYFFHUULGUUTUVMAUXGYNUYEOWHAGHHUTWDZY
      NUYEPWHUULVJZUYFDHUUQIAUXEYNUYEQWHZUUCUYCUYDWIWJUYFDHUVFIUYPUUCUYCUYDWKWJ
      WLWMUYMWAWNUWAUXRUVKWPUWAUYGUVKWPWQUYFUYGUXTUVKUWAUYFGUWHUUTUVMAGUWHVGYNU
      YEAUUDFYQHGUDUXFUXCUXHPUXDWRWHWSVSWTXAUXPUYBUABCDDUUGUVGVGZUXLUXSUXNUYAUY
      QUXLUVKUXRUWAVDSZUEUXSUYQUXKUVKUUOUYRUYQUXKUVGJTUVKUUGUVGJXBUUQUVFJXFXCZU
      YQUUMUXRUUNUWAVDUYQUUIUUTUUKUVMUULUYQUUHUUQIUUQUVFUUGBXDZCXDZXEXGZUYQUUJU
      VFIUUQUVFUUGUYTVUAXHXGZXIUYQUUNUVGKTUWAUUGUVGKXBUUQUVFKXFXCZXIXJUXRUWAUVK
      UUTUVMUULXKUUQUVFKXKZXLXMUYQUXNUVKUXTUWAVDSZUEUYAUYQUXKUVKUWJVUFUYSUYQUWI
      UXTUUNUWAVDUYQUUIUUTUUKUVMUWHVUBVUCXIVUDXIXJUXTUWAUVKUUTUVMUWHXKVUEXLXMXN
      XOXQUXLUXNUAUUFXPVQXRUAUUFUUOJXSUAUUFUWJJXSWQUUCUWDUXABDUUCUYCUKZUVCUWNUW
      CUWTVUGUVBUWMUUSVUGFYQHUVAGUUTUXFAUXGYNUYCOWHAUYNYNUYCPWHUVAVJZUUCDHUUQIA
      UXEYNQWBXTYAYBVUGUWBUWSCUADDVUGUVSUWRUCUBUWAUVTVUGUVRUWQUVIVUGUVQUWPUVJUV
      LVUGUVPUWOUVNUVOAUVPUWOVGYNUYCAUUDFYQHUVPGUDUXFUXCUXHPUXDUVPVJZYFWHWSWSYB
      YCYCYDYGYEUUCBCUADUUDEUVHUURUCUBFIJKUVAUULUVPMUXCNUYOUURVJZVUHUVHVJZVUIAY
      NYHZAYTYNUXHWBYIUUCBCUADUWFEUVHUURUCUBYQIJKUWLUWHUWOMUWFVJNUWHVJVUJUWLVJV
      UKUWOVJVULAUUBYNAFYQGUXFOYJWBYIYKYLYM $.
  $}

  ${
    $d f g x y C $.  $d f g x y D $.  $d f g x y R $.
    $( A functor into a restricted category is also a functor into the whole
       category.  (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    funcres2 $p |- ( R e. ( Subcat ` D ) ->
      ( C Func ( D |`cat R ) ) C_ ( C Func D ) ) $=
      ( vf vg vx vy cfv wcel co cfunc cv wbr wa cbs cdm eqid wf ccat mpbird a1i
      csubc cresc wrel relfunc cop simpr chom simpl eqidd subcfn funcf1 subcrcl
      adantr subcss1 rescbas simplr simprl simprr funcf2 wceq reschom funcres2b
      feq3d oveqd ex df-br 3imtr3g relssdv ) CBUBHIZDEABCUCJZKJZABKJZVLUDVJAVKU
      EUAVJDLZELZVLMZVNVOVMMZVNVOUFZVLIVRVMIVJVPVQVJVPNZVQVPVJVPUGZVSFGAOHZABCC
      PPZVNVOAUHHZFLZGLZWCJZWAQZWCQZVJVPUIZVSBWBCWIVSWBUJUKZVSWAWBVNRWAVKOHZVNR
      VSWAWKAVKVNVOWGWKQVTULVSWBWKVNWAVSBOHZBVKWBCSVKQZWLQZVJBSIVPBCUMUNZWJVSWL
      BWBCWIWJWNUOZUPVDTVSWDWAIZWEWAIZNZNZWFWDVNHZWEVNHZCJZWDWEVOJZRWFXAXBVKUHH
      ZJZXDRWTWAAVKVNVOWCXEWDWEWGWHXEQVJVPWSUQVSWQWRURVSWQWRUSUTWTXCXFXDWFWTCXE
      XAXBVSCXEVAWSVSWLBVKWBCSWMWNWOWJWPVBUNVEVDTVCTVFVNVOVLVGVNVOVMVGVHVI $.
  $}

  ${
    $d B x y z $.  $d C x y z $.  $d J x y z $.  $d S x y z $.
    idfusubc.s $e |- S = ( C |`cat J ) $.
    idfusubc.i $e |- I = ( idFunc ` S ) $.
    idfusubc.b $e |- B = ( Base ` S ) $.
    $( The identity functor for a subcategory is an "inclusion functor" from
       the subcategory into its supercategory.  (Contributed by AV,
       29-Mar-2020.) $)
    idfusubc0 $p |- ( J e. ( Subcat ` C ) -> I = <. ( _I |` B ) ,
                  ( x e. B , y e. B |-> ( _I |` ( x ( Hom ` S ) y ) ) ) >. ) $=
      ( vz csubc cfv wcel cid cres cxp cv cop wceq chom cmpt co cmpo id subccat
      eqid idfuval fveq2 df-ov eqtr4di reseq2d mpompt a1i opeq2d eqtrd ) GDLMNZ
      FOCPZKCCQOKRZEUAMZMZPZUBZSURABCCOARZBRZUTUCZPZUDZSUQKCEUTFIJUQDEGHUQUEUFU
      TUGUHUQVCVHURVCVHTUQABKCCVBVGUSVDVESZTZVAVFOVJVAVIUTMVFUSVIUTUIVDVEUTUJUK
      ULUMUNUOUP $.

    $( The identity functor for a subcategory is an "inclusion functor" from
       the subcategory into its supercategory.  (Contributed by AV,
       29-Mar-2020.) $)
    idfusubc $p |- ( J e. ( Subcat ` C ) -> I = <. ( _I |` B ) ,
                            ( x e. B , y e. B |-> ( _I |` ( x J y ) ) ) >. ) $=
      ( csubc cfv wcel cid cres cv co cmpo cop cdm chom idfusubc0 cbs ccat eqid
      subcrcl eqidd subcfn subcss1 reschom eqcomd oveqd reseq2d mpoeq3dv opeq2d
      id eqtrd ) GDKLMZFNCOZABCCNAPZBPZEUALZQZOZRZSUSABCCNUTVAGQZOZRZSABCDEFGHI
      JUBURVEVHUSURABCCVDVGURVCVFNURVBGUTVAURGVBURDUCLZDEGTTZGUDHVIUEZDGUFURDVJ
      GURUPZURVJUGUHZURVIDVJGVLVMVKUIUJUKULUMUNUOUQ $.
  $}

  ${
    $d f g z C $.  $d f g z D $.  $d f g z ph $.
    wunfunc.1 $e |- ( ph -> U e. WUni ) $.
    wunfunc.2 $e |- ( ph -> C e. U ) $.
    wunfunc.3 $e |- ( ph -> D e. U ) $.
    $( A weak universe is closed under the functor set operation.  (Contributed
       by Mario Carneiro, 12-Jan-2017.)  (Proof shortened by AV,
       13-Oct-2024.) $)
    wunfunc $p |- ( ph -> ( C Func D ) e. U ) $=
      ( vz cbs cfv cmap co chom cxp wunstr wunxp cv eqid fvex wss vf vg crn cpw
      cuni cfunc cnx baseid wunmap homid wunrn wununi wrel relfunc a1i cop wcel
      wunpw df-br wa wf simpr funcf1 elmap sylibr c1st c2nd cixp wral fvssunirn
      wbr ovssunirn xpss12 mp2an sspwi sstri rgenw ss2ixp ax-mp xpex rnex uniex
      mapsspw pwex ixpconst sseqtri funcixp sselid opelxpd ex biimtrrid relssdv
      wunss ) ACIJZBIJZKLZBMJZUCZUEZCMJZUCZUEZNZUDZWOWONZKLZNZBCUFLZDEAWPXFDEAW
      NWODEACDIUGIJZUHEGOABDIXIUHEFOZUIAXDXEDEAXCDEAWSXBDEAWRDEAWQDEABDMUGMJZUJ
      EFOUKULAXADEAWTDEACDMXKUJEGOUKULPURAWOWODEXJXJPUIPAUAUBXHXGXHUMABCUNUOUAQ
      ZUBQZUPZXHUQXLXMXHVKZAXNXGUQZXLXMXHUSAXOXPAXOUTZXLXMWPXFXQWOWNXLVAXLWPUQX
      QWOWNBCXLXMWORZWNRAXOVBZVCWNWOXLCISBISZVDVEXQHXEHQZVFJXLJZYAVGJXLJZWTLZYA
      WQJZKLZVHZXFXMYGHXEXDVHZXFYFXDTZHXEVIYGYHTYIHXEYFYEYDNZUDXDYDYEWCYJXCYEWS
      TYDXBTYJXCTWQYAVJWTYBYCVLYEWSYDXBVMVNVOVPVQHXEYFXDVRVSHXEXDWOWOXTXTVTXCWS
      XBWRWQBMSWAWBXAWTCMSWAWBVTWDWEWFXQHWOBCXLXMWQWTXRWQRWTRXSWGWHWIWJWKWLWM
      $.
  $}

  ${
    $d f g m n w x y z A $.  $d f g m n w x y z C $.  $d f g m n x y z ph $.
    $d f g m n x y z B $.  $d f g m n x y z D $.
    funcpropd.1 $e |- ( ph -> ( Homf ` A ) = ( Homf ` B ) ) $.
    funcpropd.2 $e |- ( ph -> ( comf ` A ) = ( comf ` B ) ) $.
    funcpropd.3 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    funcpropd.4 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    funcpropd.a $e |- ( ph -> A e. V ) $.
    funcpropd.b $e |- ( ph -> B e. V ) $.
    funcpropd.c $e |- ( ph -> C e. V ) $.
    funcpropd.d $e |- ( ph -> D e. V ) $.
    $( If two categories have the same set of objects, morphisms, and
       compositions, then they have the same functors.  (Contributed by Mario
       Carneiro, 17-Jan-2017.) $)
    funcpropd $p |- ( ph -> ( A Func C ) = ( B Func D ) ) $=
      ( vz co wcel wa cfv eqid vf vg vx vn vm vy vw cfunc relfunc cbs cv wf cxp
      ccat c1st c2nd chom cmap cixp ccid wceq cop cco wral w3a catpropd anbi12d
      wbr wb 2fveq3 oveq12d fveq2 cbvixpv eleq2i anbi2i chomf ad2antrr cidpropd
      ccomf fveq1d fveq2d eqeq12d ad6antr simp-5r simp-4r simpllr simplr simprl
      simpr comfeqval ad5antr ffvelcdmd df-ov simprr ad3antrrr opelxpi ad5ant23
      adantr vex op1std op2ndd eqtr4di fvixp syl2anc eqeltrid elmapi ffvelcdmda
      adantll ralbidva homfeqval raleqdv raleqbidv bitrd sylan2b pm5.32da xp1st
      syl adantl xp2nd 3eqtr3g 1st2nd2 3eqtr4d ixpeq2dva sqxpeqd ixpeq1d eleq2d
      homfeqbas eqtrd feq23d anbi1d anbi2d raleqbidva 3bitr4g df-br sylbi simpl
      df-3an funcrcl isfunc biadanii eqbrrdiv ) AUAUBBDUHPZCEUHPZBDUICEUIABUNQZ
      DUNQZRZBUJSZDUJSZUAUKZULZUBUKZOUUGUUGUMZOUKZUOSZUUISZUUMUPSZUUISZDUQSZPZU
      UMBUQSZSZURPZUSZQZUCUKZBUTSZSZUVEUVEUUKPZSZUVEUUISZDUTSZSZVAZUDUKZUEUKZUV
      EUFUKZVBZUUMBVCSZPPZUVEUUMUUKPZSZUVNUVPUUMUUKPZSZUVOUVEUVPUUKPZSZUVJUVPUU
      ISZVBZUUMUUISZDVCSZPPZVAZUDUVPUUMUUTPZVDZUEUVEUVPUUTPZVDZOUUGVDZUFUUGVDZR
      ZUCUUGVDZVEZRCUNQZEUNQZRZCUJSZEUJSZUUIULZUUKOUXDUXDUMZUUOUUQEUQSZPZUUMCUQ
      SZSZURPZUSZQZUVECUTSZSZUVHSZUVJEUTSZSZVAZUVNUVOUVQUUMCVCSZPPZUVTSZUWCUWEU
      WGUWHEVCSZPPZVAZUDUVPUUMUXJPZVDZUEUVEUVPUXJPZVDZOUXDVDZUFUXDVDZRZUCUXDVDZ
      VEZRUUIUUKUUBVHZUUIUUKUUCVHZAUUFUXCUWTUYOAUUDUXAUUEUXBABCFFGHKLVFADEFFIJM
      NVFVGAUUJUVDRZUWSRZUXFUXNRZUYNRZUWTUYOAUYSUYRUXTUYJOUUGVDZUFUUGVDZRZUCUUG
      VDZRVUAAUYRUWSVUEUYRAUUJUUKUGUULUGUKZUOSZUUISZVUFUPSZUUISZUURPZVUFUUTSZUR
      PZUSZQZRZUWSVUEVIUVDVUOUUJUVCVUNUUKOUGUULUVBVUMUUMVUFVAZUUSVUKUVAVULURVUQ
      UUOVUHUUQVUJUURUUMVUFUUIUOVJUUMVUFUUIUPVJVKUUMVUFUUTVLVKVMVNVOAVUPRZUWRVU
      DUCUUGVURUVEUUGQZRZUVMUXTUWQVUCVUTUVIUXQUVLUXSVUTUVGUXPUVHVUTUVEUVFUXOVUT
      BCFFABVPSCVPSVAZVUPVUSGVQZABVSSCVSSVAZVUPVUSHVQABFQVUPVUSKVQACFQVUPVUSLVQ
      VRVTWAVUTUVJUVKUXRAUVKUXRVAVUPVUSADEFFIJMNVRVQVTWBVUTUWPVUBUFUUGVUTUVPUUG
      QZRZUWOUYJOUUGVVEUUMUUGQZRZUWOUYFUDUWLVDZUEUWNVDUYJVVGUWMVVHUEUWNVVGUVOUW
      NQZRZUWKUYFUDUWLVVJUVNUWLQZRZUWAUYCUWJUYEVVLUVSUYBUVTVVLUUGBCUYAUVRUVOUVN
      UUTUVEUVPUUMUUGTZUUTTZUVRTZUYATZAVVAVUPVUSVVDVVFVVIVVKGWCAVVCVUPVUSVVDVVF
      VVIVVKHWCVURVUSVVDVVFVVIVVKWDZVUTVVDVVFVVIVVKWEZVVEVVFVVIVVKWFZVVGVVIVVKW
      GZVVJVVKWIWJWAVVLUUHDEUYDUWIUWEUWCUURUVJUWFUWHUUHTZUURTZUWITZUYDTZADVPSEV
      PSVAZVUPVUSVVDVVFVVIVVKIWCADVSSEVSSVAVUPVUSVVDVVFVVIVVKJWCVVLUUGUUHUVEUUI
      VURUUJVUSVVDVVFVVIVVKAUUJVUOWHWKZVVQWLVVLUUGUUHUVPUUIVWFVVRWLVVLUUGUUHUUM
      UUIVWFVVSWLVVLUWNUVJUWFUURPZUVOUWDVVJUWNVWGUWDULZVVKVVJUWDVWGUWNURPZQVWHV
      VJUWDUVQUUKSZVWIUVEUVPUUKWMVVJVUOUVQUULQZVWJVWIQVVGVUOVVIVURVUOVUSVVDVVFA
      UUJVUOWNWOZWRVUSVVDVWKVURVVFVVIUVEUVPUUGUUGWPWQUGUULVUMUVQVWIUUKVUFUVQVAZ
      VUKVWGVULUWNURVWMVUHUVJVUJUWFUURVWMVUGUVEUUIUVEUVPVUFUCWSZUFWSZWTWAVWMVUI
      UVPUUIUVEUVPVUFVWNVWOXAWAVKVWMVULUVQUUTSUWNVUFUVQUUTVLUVEUVPUUTWMXBVKXCXD
      XEUWDVWGUWNXFXQWRVVTWLVVJUWLUWFUWHUURPZUVNUWBVVGUWLVWPUWBULZVVIVVGUWBVWPU
      WLURPZQVWQVVGUWBUVPUUMVBZUUKSZVWRUVPUUMUUKWMVVGVUOVWSUULQZVWTVWRQVWLVVDVV
      FVXAVUTUVPUUMUUGUUGWPXHUGUULVUMVWSVWRUUKVUFVWSVAZVUKVWPVULUWLURVXBVUHUWFV
      UJUWHUURVXBVUGUVPUUIUVPUUMVUFVWOOWSZWTWAVXBVUIUUMUUIUVPUUMVUFVWOVXCXAWAVK
      VXBVULVWSUUTSUWLVUFVWSUUTVLUVPUUMUUTWMXBVKXCXDXEUWBVWPUWLXFXQWRXGWJWBXIXI
      VVGVVHUYHUEUWNUYIVVGUUGBCUUTUXJUVEUVPVVMVVNUXJTZVUTVVAVVDVVFVVBVQZVURVUSV
      VDVVFWFVUTVVDVVFWGZXJVVGUYFUDUWLUYGVVGUUGBCUUTUXJUVPUUMVVMVVNVXDVXEVXFVVE
      VVFWIXJXKXLXMXIXIVGXIXNXOAUYRUYTVUEUYNAUYRUUJUXNRUYTAUUJUVDUXNAUUJRZUVCUX
      MUUKVXGUVCOUULUXLUSUXMVXGOUULUVBUXLVXGUUMUULQZRZUUSUXIUVAUXKURVXIUUHDEUUR
      UXHUUOUUQVWAVWBUXHTZAVWEUUJVXHIVQVXIUUGUUHUUNUUIAUUJVXHWGZVXHUUNUUGQVXGUU
      MUUGUUGXPXRZWLVXIUUGUUHUUPUUIVXKVXHUUPUUGQVXGUUMUUGUUGXSXRZWLXJVXIUUNUUPV
      BZUUTSZVXNUXJSZUVAUXKVXIUUNUUPUUTPUUNUUPUXJPVXOVXPVXIUUGBCUUTUXJUUNUUPVVM
      VVNVXDAVVAUUJVXHGVQVXLVXMXJUUNUUPUUTWMUUNUUPUXJWMXTVXIUUMVXNUUTVXHUUMVXNV
      AVXGUUMUUGUUGYAXRZWAVXIUUMVXNUXJVXQWAYBVKYCVXGOUULUXGUXLAUULUXGVAUUJAUUGU
      XDABCGYGZYDWRYEYHYFXOAUUJUXFUXNAUUGUUHUXDUXEUUIVXRADEIYGYIYJXMAVUDUYMUCUU
      GUXDVXRAVUSRZVUCUYLUXTVXSVUBUYKUFUUGUXDAUUGUXDVAVUSVXRWRZVXSUYJOUUGUXDVXT
      XKXLYKYLVGXMUUJUVDUWSYQUXFUXNUYNYQYMVGUYPUUFUWTUYPUUIUUKVBZUUBQUUFUUIUUKU
      UBYNBDVYAYRYOUUFUCUFOUUGUUHBUVRUVFUEUDDUUIUUKUUTUVKUURUWIVVMVWAVVNVWBUVFT
      UVKTVVOVWCUUDUUEYPUUDUUEWIYSYTUYQUXCUYOUYQVYAUUCQUXCUUIUUKUUCYNCEVYAYRYOU
      XCUCUFOUXDUXECUYAUXOUEUDEUUIUUKUXJUXRUXHUYDUXDTUXETVXDVXJUXOTUXRTVVPVWDUX
      AUXBYPUXAUXBWIYSYTYMUUA $.
  $}

  ${
    $d x y A $.  $d x y C $.  $d x y D $.  $d x y E $.  $d x y ph $.
    $d x y F $.  $d x y G $.  $d x y S $.
    funcres2c.a $e |- A = ( Base ` C ) $.
    funcres2c.e $e |- E = ( D |`s S ) $.
    funcres2c.d $e |- ( ph -> D e. Cat ) $.
    funcres2c.r $e |- ( ph -> S e. V ) $.
    funcres2c.1 $e |- ( ph -> F : A --> S ) $.
    $( Condition for a functor to also be a functor into the restriction.
       (Contributed by Mario Carneiro, 30-Jan-2017.) $)
    funcres2c $p |- ( ph -> ( F ( C Func D ) G <-> F ( C Func E ) G ) ) $=
      ( co wa chomf cfv eqid wcel vx vy cfunc wbr wo wi orc a1i olc cbs cin cxp
      wb cres cresc chom cv csubc wss inss2 fullsubc adantr homffn xpss12 mp2an
      wfn fnssres crn ffnd frnd simpr funcf1 ressbasss sstrdi jaodan ssind df-f
      wf sylanbrc simplrl simplrr funcf2 wceq resshom syl ad2antrr oveqd mpbird
      feq3d an32s simprl ffvelcdmd simprr ovresd elin2d homfval eqtrd funcres2b
      cvv eqidd ccomf cress ressinbas eqtrid fveq2d fullresc simpld simprd ccat
      cop df-br funcrcl sylbi jaoi elexd adantl ovexi ovexd funcpropd bitr4d ex
      breqd pm5.21ndd ) AGHCDUCOZUDZGHCFUCOZUDZUEZYEYGYEYHUFAYEYGUGUHYGYHUFAYGY
      EUIUHAYHYEYGUMAYHPZYEGHCDDQRZEDUJRZUKZYLULZUNZUOOZUCOZUDYGYIUAUBBCDYNYLGH
      CUPRZUAUQZUBUQZYQOZJYQSZAYNDURRTYHAYKDYLYJYKSZYJSZLYLYKUSZAEYKUTZUHZVAVBY
      NYMVFZYIYJYKYKULZVFYMUUHUSZUUGYKDYJUUCUUBVCUUDUUDUUIUUEUUEYLYKYLYKVDVEUUH
      YMYJVGVEUHYIGBVFGVHZYLUSBYLGVRZYIBEGABEGVRYHNVBZVIYIUUJEYKYIBEGUULVJAYEUU
      JYKUSYGAYEPZBYKGUUMBYKCDGHJUUBAYEVKVLVJAYGPZUUJFUJRZYKUUNBUUOGUUNBUUOCFGH
      JUUOSAYGVKVLVJEYKFDKUUBVMVNVOVPBYLGVQVSZYIYRBTZYSBTZPZPZYTYRGRZYSGRZYNOZY
      RYSHOZVRYTUVAUVBDUPRZOZUVDVRZAUUSYHUVGAUUSPZYEUVGYGUVHYEPBCDGHYQUVEYRYSJU
      UAUVESZUVHYEVKAUUQUURYEVTAUUQUURYEWAWBUVHYGPZUVGYTUVAUVBFUPRZOZUVDVRUVJBC
      FGHYQUVKYRYSJUUAUVKSUVHYGVKAUUQUURYGVTAUUQUURYGWAWBUVJUVFUVLUVDYTUVJUVEUV
      KUVAUVBAUVEUVKWCZUUSYGAEITZUVMMEDFUVEIKUVIWDWEWFWGWIWHVOWJUUTUVCUVFUVDYTU
      UTUVCUVAUVBYJOUVFUUTUVAUVBYJYLUUTBYLYRGYIUUKUUSUUPVBZYIUUQUURWKWLZUUTBYLY
      SGUVOYIUUQUURWMWLZWNUUTYKDYJUVEUVAUVBUUCUUBUVIUUTEYKUVAUVPWOUUTEYKUVBUVQW
      OWPWQWIWHWRYIYFYPGHYICCFYOWSYICQRWTYICXARWTAFQRZYOQRZWCYHAUVRDYLXBOZQRZUV
      SAFUVTQAFDEXBOZUVTKAUVNUWBUVTWCMEYKDIUUBXCWEXDZXEAUWAUVSWCZUVTXARZYOXARZW
      CZAYKDUVTYLYOYJUUBUUCLUUFUVTSYOSXFZXGWQVBAFXARZUWFWCYHAUWIUWEUWFAFUVTXAUW
      CXEAUWDUWGUWHXHWQVBYHCWSTAYHCXIYECXITZYGYEUWJDXITZYEGHXJZYDTUWJUWKPGHYDXK
      CDUWLXLXMXGYGUWJFXITZYGUWLYFTUWJUWMPGHYFXKCFUWLXLXMXGXNXOXPZUWNFWSTYIFDEX
      BKXQUHYIDYNUOXRXSYBXTYAYC $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Full & faithful functors
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Full $.  $( The class of full functors. $)
  $c Faith $.  $( The class of faithful functors. $)

  $( Extend class notation with the class of all full functors. $)
  cful $a class Full $.

  $( Extend class notation with the class of all faithful functors. $)
  cfth $a class Faith $.

  ${
    $d c d f g x y $.  $d c d C $.  $d d D $.
    $( Function returning all the full functors from a category ` C ` to a
       category ` D ` .  A full functor is a functor in which all the morphism
       maps ` G ( X , Y ) ` between objects ` X , Y e. C ` are surjections.
       Definition 3.27(3) in [Adamek] p. 34.  (Contributed by Mario Carneiro,
       26-Jan-2017.) $)
    df-full $a |- Full = ( c e. Cat , d e. Cat |->
      { <. f , g >. | ( f ( c Func d ) g /\
        A. x e. ( Base ` c ) A. y e. ( Base ` c )
        ran ( x g y ) = ( ( f ` x ) ( Hom ` d ) ( f ` y ) ) ) } ) $.

    $( Function returning all the faithful functors from a category ` C ` to a
       category ` D ` .  A faithful functor is a functor in which all the
       morphism maps ` G ( X , Y ) ` between objects ` X , Y e. C ` are
       injections.  Definition 3.27(2) in [Adamek] p. 34.  (Contributed by
       Mario Carneiro, 26-Jan-2017.) $)
    df-fth $a |- Faith = ( c e. Cat , d e. Cat |->
      { <. f , g >. | ( f ( c Func d ) g /\
        A. x e. ( Base ` c ) A. y e. ( Base ` c ) Fun `' ( x g y ) ) } ) $.

    $( A full functor is a functor.  (Contributed by Mario Carneiro,
       26-Jan-2017.) $)
    fullfunc $p |- ( C Full D ) C_ ( C Func D ) $=
      ( vc vd vf vg vx vy ccat wcel wa cful co cfunc wss wceq oveq1 sseq12d cfv
      cv oveq2 wbr crn chom cbs wral copab cvv ovex simpl ssopab2i opabss sstri
      ssexi df-full ovmpt4g mp3an3 eqsstrdi vtocl2ga wn c0 mpondm0 0ss pm2.61i
      ) AIJBIJKZABLMZABNMZOZCTZDTZLMZVIVJNMZOAVJLMZAVJNMZOVHCDABIIVIAPVKVMVLVNV
      IAVJLQVIAVJNQRVJBPVMVFVNVGVJBALUAVJBANUARVIIJZVJIJZKVKETZFTZVLUBZGTZHTZVR
      MUCVTVQSWAVQSVJUDSMPHVIUESZUFGWBUFZKZEFUGZVLVOVPWEUHJVKWEPWEVLVIVJNUIWEVS
      EFUGVLWDVSEFVSWCUJUKEFVLULUMZUNCDIIWELUHGHEFCDUOZUPUQWFURUSVEUTVFVAVGCDWE
      LABIIWGVBVGVCURVD $.

    $( A faithful functor is a functor.  (Contributed by Mario Carneiro,
       26-Jan-2017.) $)
    fthfunc $p |- ( C Faith D ) C_ ( C Func D ) $=
      ( vc vd vf vg vx vy ccat wcel wa cfth co cfunc wss cv oveq1 sseq12d oveq2
      wceq wbr ccnv wfun cbs cfv wral copab cvv ovex simpl ssopab2i sstri ssexi
      opabss df-fth ovmpt4g mp3an3 eqsstrdi vtocl2ga wn c0 mpondm0 0ss pm2.61i
      ) AIJBIJKZABLMZABNMZOZCPZDPZLMZVIVJNMZOAVJLMZAVJNMZOVHCDABIIVIATVKVMVLVNV
      IAVJLQVIAVJNQRVJBTVMVFVNVGVJBALSVJBANSRVIIJZVJIJZKVKEPFPZVLUAZGPHPVQMUBUC
      HVIUDUEZUFGVSUFZKZEFUGZVLVOVPWBUHJVKWBTWBVLVIVJNUIWBVREFUGVLWAVREFVRVTUJU
      KEFVLUNULZUMCDIIWBLUHGHEFCDUOZUPUQWCURUSVEUTVFVAVGCDWBLABIIWDVBVGVCURVD
      $.
  $}

  $( The set of full functors is a relation.  (Contributed by Mario Carneiro,
     26-Jan-2017.) $)
  relfull $p |- Rel ( C Full D ) $=
    ( cful co cfunc wss wrel fullfunc relfunc relss mp2 ) ABCDZABEDZFMGLGABHABI
    LMJK $.

  $( The set of faithful functors is a relation.  (Contributed by Mario
     Carneiro, 26-Jan-2017.) $)
  relfth $p |- Rel ( C Faith D ) $=
    ( cfth co cfunc wss wrel fthfunc relfunc relss mp2 ) ABCDZABEDZFMGLGABHABIL
    MJK $.

  ${
    $d c d f g x y B $.  $d c d f g x y C $.  $d c d f g x y D $.  $d x y ph $.
    $d f x y H $.  $d c d f g x y J $.  $d f R $.  $d f x y X $.  $d f x y Y $.
    $d f g x y F $.  $d f g x y G $.
    isfull.b $e |- B = ( Base ` C ) $.
    isfull.j $e |- J = ( Hom ` D ) $.
    $( Value of the set of full functors between two categories.  (Contributed
       by Mario Carneiro, 27-Jan-2017.) $)
    isfull $p |- ( F ( C Full D ) G <-> ( F ( C Func D ) G /\
      A. x e. B A. y e. B ran ( x G y ) = ( ( F ` x ) J ( F ` y ) ) ) ) $=
      ( vf vg co wbr cv cfv wceq wral wa wcel vc cfunc crn fullfunc ssbri copab
      vd cful ccat cop df-br funcrcl sylbi chom cbs oveq12 breqd fveq2d eqtr4di
      simpl simpr oveqd eqeq2d raleqbidv anbi12d opabbidv df-full ovex ssopab2i
      opabss sstri ssexi ovmpoa syl cvv relfunc brrelex12i breq12 rneqd oveq12d
      wb fveq1d eqeq12d 2ralbidv eqid brabga bitrd bianabs biadanii ) FGDEUHMZN
      ZFGDEUBMZNZAOZBOZGMZUCZWNFPZWOFPZHMZQZBCRACRZWJWLFGDEUDUEWMWKXBWMWKFGKOZL
      OZWLNZWNWOXDMZUCZWNXCPZWOXCPZHMZQZBCRZACRZSZKLUFZNZWMXBSZWMWJXOFGWMDUITEU
      ITSZWJXOQWMFGUJZWLTXRFGWLUKDEXSULUMUAUGDEUIUIXCXDUAOZUGOZUBMZNZXGXHXIYAUN
      PZMZQZBXTUOPZRZAYGRZSZKLUFXOUHXTDQZYAEQZSZYJXNKLYMYCXEYIXMYMYBWLXCXDXTDYA
      EUBUPUQYMYHXLAYGCYMYGDUOPCYMXTDUOYKYLUTURIUSZYMYFXKBYGCYNYMYEXJXGYMYDHXHX
      IYMYDEUNPHYMYAEUNYKYLVAURJUSVBVCVDVDVEVFABKLUAUGVGXOWLDEUBVHXOXEKLUFWLXNX
      EKLXEXMUTVIKLWLVJVKVLVMVNUQWMFVOTGVOTSXPXQWAFGWLDEVPVQXNXQKLFGXOVOVOXCFQZ
      XDGQZSZXEWMXMXBXCFXDGWLVRYQXKXAABCCYQXGWQXJWTYQXFWPYQXDGWNWOYOYPVAVBVSYQX
      HWRXIWSHYQWNXCFYOYPUTZWBYQWOXCFYRWBVTWCWDVEXOWEWFVNWGWHWI $.

    isfull.h $e |- H = ( Hom ` C ) $.
    $( Equivalent condition for a full functor.  (Contributed by Mario
       Carneiro, 27-Jan-2017.) $)
    isfull2 $p |- ( F ( C Full D ) G <-> ( F ( C Func D ) G /\
      A. x e. B A. y e. B
        ( x G y ) : ( x H y ) -onto-> ( ( F ` x ) J ( F ` y ) ) ) ) $=
      ( co wbr cv cfv wral wa wcel ralbidva cful cfunc crn wfo isfull wf wfn wb
      wceq simpll simplr simpr funcf2 ffn df-fo baib 3syl pm5.32i bitr4i ) FGDE
      UAMNFGDEUBMNZAOZBOZGMZUCVAFPVBFPIMZUIZBCQZACQZRUTVAVBHMZVDVCUDZBCQZACQZRA
      BCDEFGIJKUEUTVKVGUTVJVFACUTVACSZRZVIVEBCVMVBCSZRZVHVDVCUFVCVHUGZVIVEUHVOC
      DEFGHIVAVBJLKUTVLVNUJUTVLVNUKVMVNULUMVHVDVCUNVIVPVEVHVDVCUOUPUQTTURUS $.

    fullfo.f $e |- ( ph -> F ( C Full D ) G ) $.
    fullfo.x $e |- ( ph -> X e. B ) $.
    fullfo.y $e |- ( ph -> Y e. B ) $.
    $( The morphism map of a full functor is a surjection.  (Contributed by
       Mario Carneiro, 27-Jan-2017.) $)
    fullfo $p |- ( ph ->
      ( X G Y ) : ( X H Y ) -onto-> ( ( F ` X ) J ( F ` Y ) ) ) $=
      ( vx vy co cfv cv wfo wral cful wbr cfunc isfull2 simprbi syl wceq adantr
      wa wcel simplr simpr oveq12d fveq2d foeq123d rspcdv rspcimdv mpd ) AQUAZR
      UAZGSZVBETZVCETZHSZVBVCFSZUBZRBUCZQBUCZIJGSZIETZJETZHSZIJFSZUBZAEFCDUDSUE
      ZVKNVREFCDUFSUEVKQRBCDEFGHKLMUGUHUIAVJVQQIBOAVBIUJZULZVIVQRJBAJBUMVSPUKVT
      VCJUJZULZVDVLVGVOVHVPWBVBIVCJFAVSWAUNZVTWAUOZUPWBVBIVCJGWCWDUPWBVEVMVFVNH
      WBVBIEWCUQWBVCJEWDUQUPURUSUTVA $.

    fulli.r $e |- ( ph -> R e. ( ( F ` X ) J ( F ` Y ) ) ) $.
    $( The morphism map of a full functor is a surjection.  (Contributed by
       Mario Carneiro, 27-Jan-2017.) $)
    fulli $p |- ( ph -> E. f e. ( X H Y ) R = ( ( X G Y ) ` f ) ) $=
      ( co cfv wfo wcel cv wceq wrex fullfo foelrn syl2anc ) AKLITZKGUALGUAJTZK
      LHTZUBEUKUCEFUDULUAUEFUJUFABCDGHIJKLMNOPQRUGSFUJUKEULUHUI $.
  $}

  ${
    $d c d f g x y B $.  $d c d f g x y C $.  $d c d f g x y D $.  $d x y ph $.
    $d f g x y F $.  $d f g x y G $.  $d x y H $.  $d x y J $.  $d x y X $.
    $d x y Y $.
    isfth.b $e |- B = ( Base ` C ) $.
    $( Value of the set of faithful functors between two categories.
       (Contributed by Mario Carneiro, 27-Jan-2017.) $)
    isfth $p |- ( F ( C Faith D ) G <-> ( F ( C Func D ) G /\
      A. x e. B A. y e. B Fun `' ( x G y ) ) ) $=
      ( vf vg co wbr cfunc cv wral wa ccat wcel wceq cvv cfth ccnv wfun fthfunc
      vc ssbri copab cop df-br funcrcl sylbi cbs cfv oveq12 breqd simpl eqtr4di
      vd fveq2d raleqdv raleqbidv anbi12d opabbidv df-fth ssopab2i opabss sstri
      ovex ssexi ovmpoa syl relfunc brrelex12i breq12 simpr oveqd cnveqd funeqd
      wb 2ralbidv eqid brabga bitrd bianabs biadanii ) FGDEUAKZLZFGDEMKZLZANZBN
      ZGKZUBZUCZBCOACOZWFWHFGDEUDUFWIWGWOWIWGFGINZJNZWHLZWJWKWQKZUBZUCZBCOZACOZ
      PZIJUGZLZWIWOPZWIWFXEFGWIDQREQRPZWFXESWIFGUHZWHRXHFGWHUIDEXIUJUKUEURDEQQW
      PWQUENZURNZMKZLZXABXJULUMZOZAXNOZPZIJUGXEUAXJDSZXKESZPZXQXDIJXTXMWRXPXCXT
      XLWHWPWQXJDXKEMUNUOXTXOXBAXNCXTXNDULUMCXTXJDULXRXSUPUSHUQZXTXABXNCYAUTVAV
      BVCABIJUEURVDXEWHDEMVHXEWRIJUGWHXDWRIJWRXCUPVEIJWHVFVGVIVJVKUOWIFTRGTRPXF
      XGVSFGWHDEVLVMXDXGIJFGXETTWPFSZWQGSZPZWRWIXCWOWPFWQGWHVNYDXAWNABCCYDWTWMY
      DWSWLYDWQGWJWKYBYCVOVPVQVRVTVBXEWAWBVKWCWDWE $.

    isfth.h $e |- H = ( Hom ` C ) $.
    isfth.j $e |- J = ( Hom ` D ) $.
    $( Equivalent condition for a faithful functor.  (Contributed by Mario
       Carneiro, 27-Jan-2017.) $)
    isfth2 $p |- ( F ( C Faith D ) G <-> ( F ( C Func D ) G /\
      A. x e. B A. y e. B
        ( x G y ) : ( x H y ) -1-1-> ( ( F ` x ) J ( F ` y ) ) ) ) $=
      ( co wbr cv wral wa cfv wcel ralbidva cfth cfunc ccnv wf1 isfth wf simpll
      wfun wb simplr simpr funcf2 df-f1 baib syl pm5.32i bitr4i ) FGDEUAMNFGDEU
      BMNZAOZBOZGMZUCUHZBCPZACPZQURUSUTHMZUSFRUTFRIMZVAUDZBCPZACPZQABCDEFGJUEUR
      VIVDURVHVCACURUSCSZQZVGVBBCVKUTCSZQZVEVFVAUFZVGVBUIVMCDEFGHIUSUTJKLURVJVL
      UGURVJVLUJVKVLUKULVGVNVBVEVFVAUMUNUOTTUPUQ $.

    $( A fully faithful functor is a functor which is bijective on hom-sets.
       (Contributed by Mario Carneiro, 27-Jan-2017.) $)
    isffth2 $p |- ( F ( ( C Full D ) i^i ( C Faith D ) ) G <->
      ( F ( C Func D ) G /\ A. x e. B A. y e. B
        ( x G y ) : ( x H y ) -1-1-onto-> ( ( F ` x ) J ( F ` y ) ) ) ) $=
      ( cful co wbr wa cv cfv wral bitri cfth cfunc wfo wf1 wf1o isfull2 isfth2
      cin anbi12i brin df-f1o biancomi 2ralbii r19.26-2 anbi2i anandi 3bitr4i )
      FGDEMNZOZFGDEUANZOZPFGDEUBNOZAQZBQZHNZVCFRVDFRINZVCVDGNZUCZBCSACSZPZVBVEV
      FVGUDZBCSACSZPZPZFGURUTUHOVBVEVFVGUEZBCSACSZPZUSVJVAVMABCDEFGHIJLKUFABCDE
      FGHIJKLUGUIFGURUTUJVQVBVIVLPZPVNVPVRVBVPVHVKPZBCSACSVRVOVSABCCVOVHVKVEVFV
      GUKULUMVHVKABCCUNTUOVBVIVLUPTUQ $.

    ${
      fthf1.f $e |- ( ph -> F ( C Faith D ) G ) $.
      fthf1.x $e |- ( ph -> X e. B ) $.
      fthf1.y $e |- ( ph -> Y e. B ) $.
      $( The morphism map of a faithful functor is an injection.  (Contributed
         by Mario Carneiro, 27-Jan-2017.) $)
      fthf1 $p |- ( ph ->
        ( X G Y ) : ( X H Y ) -1-1-> ( ( F ` X ) J ( F ` Y ) ) ) $=
        ( vx vy co cfv cv wf1 wral cfth wbr cfunc isfth2 simprbi wceq wa adantr
        syl wcel simplr simpr oveq12d fveq2d f1eq123d rspcdv rspcimdv mpd ) AQU
        AZRUAZGSZVBETZVCETZHSZVBVCFSZUBZRBUCZQBUCZIJGSZIETZJETZHSZIJFSZUBZAEFCD
        UDSUEZVKNVREFCDUFSUEVKQRBCDEFGHKLMUGUHULAVJVQQIBOAVBIUIZUJZVIVQRJBAJBUM
        VSPUKVTVCJUIZUJZVDVLVGVOVHVPWBVBIVCJFAVSWAUNZVTWAUOZUPWBVBIVCJGWCWDUPWB
        VEVMVFVNHWBVBIEWCUQWBVCJEWDUQUPURUSUTVA $.

      fthi.r $e |- ( ph -> R e. ( X H Y ) ) $.
      fthi.s $e |- ( ph -> S e. ( X H Y ) ) $.
      $( The morphism map of a faithful functor is an injection.  (Contributed
         by Mario Carneiro, 27-Jan-2017.) $)
      fthi $p |- ( ph ->
        ( ( ( X G Y ) ` R ) = ( ( X G Y ) ` S ) <-> R = S ) ) $=
        ( co cfv wf1 wcel wceq wb fthf1 f1fveq syl12anc ) AKLIUAZKGUBLGUBJUAZKL
        HUAZUCEUJUDFUJUDEULUBFULUBUEEFUEUFABCDGHIJKLMNOPQRUGSTUJUKEFULUHUI $.
    $}

    ffthf1o.f $e |- ( ph -> F ( ( C Full D ) i^i ( C Faith D ) ) G ) $.
    ffthf1o.x $e |- ( ph -> X e. B ) $.
    ffthf1o.y $e |- ( ph -> Y e. B ) $.
    $( The morphism map of a fully faithful functor is a bijection.
       (Contributed by Mario Carneiro, 29-Jan-2017.) $)
    ffthf1o $p |- ( ph ->
      ( X G Y ) : ( X H Y ) -1-1-onto-> ( ( F ` X ) J ( F ` Y ) ) ) $=
      ( co cfv wf1 wbr wfo wf1o cful cfth cin wa brin sylib simprd fthf1 simpld
      fullfo df-f1o sylanbrc ) AIJGQZIERJERHQZIJFQZSUOUPUQUAUOUPUQUBABCDEFGHIJK
      LMAEFCDUCQZTZEFCDUDQZTZAEFURUTUETUSVAUFNEFURUTUGUHZUIOPUJABCDEFGHIJKMLAUS
      VAVBUKOPULUOUPUQUMUN $.
  $}

  ${
    $d f g x y A $.  $d f g x y B $.  $d f g x y C $.  $d f g x y ph $.
    $d f g x y D $.
    fullpropd.1 $e |- ( ph -> ( Homf ` A ) = ( Homf ` B ) ) $.
    fullpropd.2 $e |- ( ph -> ( comf ` A ) = ( comf ` B ) ) $.
    fullpropd.3 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    fullpropd.4 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    fullpropd.a $e |- ( ph -> A e. V ) $.
    fullpropd.b $e |- ( ph -> B e. V ) $.
    fullpropd.c $e |- ( ph -> C e. V ) $.
    fullpropd.d $e |- ( ph -> D e. V ) $.
    $( If two categories have the same set of objects, morphisms, and
       compositions, then they have the same full functors.  (Contributed by
       Mario Carneiro, 27-Jan-2017.) $)
    fullpropd $p |- ( ph -> ( A Full C ) = ( B Full D ) ) $=
      ( vx vy co cfv wa eqid vf vg cful relfull cv cfunc wbr crn chom wceq wral
      cbs homfeqbas adantr wcel chomf ad3antrrr simpllr funcf1 simplr ffvelcdmd
      simpr homfeqval eqeq2d raleqbidva pm5.32da funcpropd breqd anbi1d 3bitr4g
      bitrd isfull eqbrrdiv ) AUAUBBDUCQZCEUCQZBDUDCEUDAUAUEZUBUEZBDUFQZUGZOUEZ
      PUEZVQQUHZVTVPRZWAVPRZDUIRZQZUJZPBULRZUKZOWHUKZSZVPVQCEUFQZUGZWBWCWDEUIRZ
      QZUJZPCULRZUKZOWQUKZSZVPVQVNUGVPVQVOUGAWKVSWSSWTAVSWJWSAVSSZWIWROWHWQAWHW
      QUJZVSABCGUMUNZXAVTWHUOZSZWGWPPWHWQXAXBXDXCUNXEWAWHUOZSZWFWOWBXGDULRZDEWE
      WNWCWDXHTZWETZWNTZADUPREUPRUJVSXDXFIUQXGWHXHVTVPXGWHXHBDVPVQWHTZXIAVSXDXF
      URUSZXAXDXFUTVAXGWHXHWAVPXMXEXFVBVAVCVDVEVEVFAVSWMWSAVRWLVPVQABCDEFGHIJKL
      MNVGVHVIVKOPWHBDVPVQWEXLXJVLOPWQCEVPVQWNWQTXKVLVJVM $.

    $( If two categories have the same set of objects, morphisms, and
       compositions, then they have the same faithful functors.  (Contributed
       by Mario Carneiro, 27-Jan-2017.) $)
    fthpropd $p |- ( ph -> ( A Faith C ) = ( B Faith D ) ) $=
      ( vx vy co cv wbr wral vf vg cfth relfth cfunc ccnv wfun cbs wa funcpropd
      cfv breqd homfeqbas raleqdv raleqbidv anbi12d eqid isfth 3bitr4g eqbrrdiv
      ) AUAUBBDUCQZCEUCQZBDUDCEUDAUARZUBRZBDUEQZSZORPRVDQUFUGZPBUHUKZTZOVHTZUIV
      CVDCEUEQZSZVGPCUHUKZTZOVMTZUIVCVDVASVCVDVBSAVFVLVJVOAVEVKVCVDABCDEFGHIJKL
      MNUJULAVIVNOVHVMABCGUMZAVGPVHVMVPUNUOUPOPVHBDVCVDVHUQUROPVMCEVCVDVMUQURUS
      UT $.
  $}

  ${
    $d x y C $.  $d x y F $.  $d x y G $.  $d x y ph $.  $d x y O $.
    $d x y P $.
    fulloppc.o $e |- O = ( oppCat ` C ) $.
    fulloppc.p $e |- P = ( oppCat ` D ) $.
    ${
      fulloppc.f $e |- ( ph -> F ( C Full D ) G ) $.
      $( The opposite functor of a full functor is also full.  Proposition
         3.43(d) in [Adamek] p. 39.  (Contributed by Mario Carneiro,
         27-Jan-2017.) $)
      fulloppc $p |- ( ph -> F ( O Full P ) tpos G ) $=
        ( vx vy cfunc co wbr cv crn cfv chom eqid ctpos wceq wral cful fullfunc
        cbs ssbri syl funcoppc wcel wfo adantr simprr simprl fullfo forn ovtpos
        wa rneqi oppchom 3eqtr4g ralrimivva oppcbas isfull sylanbrc ) AEFUAZGDM
        NOKPZLPZVFNZQZVGERZVHERZDSRZNZUBZLBUFRZUCKVPUCEVFGDUDNOABCDEFGHIAEFBCUD
        NZOZEFBCMNZOJVQVSEFBCUEUGUHUIAVOKLVPVPAVGVPUJZVHVPUJZURZURZVHVGFNZQZVLV
        KCSRZNZVJVNWCVHVGBSRZNZWGWDUKWEWGUBWCVPBCEFWHWFVHVGVPTZWFTZWHTAVRWBJULA
        VTWAUMAVTWAUNUOWIWGWDUPUHVIWDVGVHFUQUSCWFDVKVLWKIUTVAVBKLVPGDEVFVMVPBGH
        WJVCVMTVDVE $.
    $}

    ${
      fthoppc.f $e |- ( ph -> F ( C Faith D ) G ) $.
      $( The opposite functor of a faithful functor is also faithful.
         Proposition 3.43(c) in [Adamek] p. 39.  (Contributed by Mario
         Carneiro, 27-Jan-2017.) $)
      fthoppc $p |- ( ph -> F ( O Faith P ) tpos G ) $=
        ( vx vy cfunc co wbr cv ccnv wfun cfv eqid ctpos cbs wral fthfunc ssbri
        cfth syl funcoppc wcel wa chom adantr simprr simprl fthf1 df-f1 simprbi
        wf1 wf ovtpos cnveqi funeqi sylibr ralrimivva oppcbas isfth sylanbrc )
        AEFUAZGDMNOKPZLPZVHNZQZRZLBUBSZUCKVNUCEVHGDUFNOABCDEFGHIAEFBCUFNZOZEFBC
        MNZOJVOVQEFBCUDUEUGUHAVMKLVNVNAVIVNUIZVJVNUIZUJZUJZVJVIFNZQZRZVMWAVJVIB
        UKSZNZVJESVIESCUKSZNZWBURZWDWAVNBCEFWEWGVJVIVNTZWETWGTAVPVTJULAVRVSUMAV
        RVSUNUOWIWFWHWBUSWDWFWHWBUPUQUGVLWCVKWBVIVJFUTVAVBVCVDKLVNGDEVHVNBGHWJV
        EVFVG $.
    $}

    ${
      ffthoppc.f $e |- ( ph -> F ( ( C Full D ) i^i ( C Faith D ) ) G ) $.
      $( The opposite functor of a fully faithful functor is also full and
         faithful.  (Contributed by Mario Carneiro, 27-Jan-2017.) $)
      ffthoppc $p |- ( ph -> F ( ( O Full P ) i^i ( O Faith P ) ) tpos G ) $=
        ( ctpos cful co wbr cfth cin wa brin sylib simpld fulloppc sylanbrc
        simprd fthoppc ) AEFKZGDLMZNEUEGDOMZNEUEUFUGPNABCDEFGHIAEFBCLMZNZEFBCOM
        ZNZAEFUHUJPNUIUKQJEFUHUJRSZTUAABCDEFGHIAUIUKULUCUDEUEUFUGRUB $.
    $}
  $}

  ${
    fthsect.b $e |- B = ( Base ` C ) $.
    fthsect.h $e |- H = ( Hom ` C ) $.
    fthsect.f $e |- ( ph -> F ( C Faith D ) G ) $.
    fthsect.x $e |- ( ph -> X e. B ) $.
    fthsect.y $e |- ( ph -> Y e. B ) $.
    fthsect.m $e |- ( ph -> M e. ( X H Y ) ) $.
    fthsect.n $e |- ( ph -> N e. ( Y H X ) ) $.
    ${
      fthsect.s $e |- S = ( Sect ` C ) $.
      fthsect.t $e |- T = ( Sect ` D ) $.
      $( A faithful functor reflects sections.  (Contributed by Mario Carneiro,
         27-Jan-2017.) $)
      fthsect $p |- ( ph -> ( M ( X S Y ) N <->
        ( ( X G Y ) ` M ) ( ( F ` X ) T ( F ` Y ) ) ( ( Y G X ) ` N ) ) ) $=
        ( cop cco cfv co ccid wceq chom eqid ccat wcel cfunc cfth fthfunc ssbri
        wbr wa df-br sylib funcrcl simpld catcocl catidcl funcco funcid eqeq12d
        syl fthi bitr3d issect2 cbs simprd funcf1 ffvelcdmd funcf2 3bitr4d ) AK
        JLMUCLCUDUEZUFUFZLCUGUEZUEZUHZKMLHUFZUEZJLMHUFZUEZLGUEZMGUEZUCWGDUDUEZU
        FUFZWGDUGUEZUEZUHZJKLMEUFUQWFWDWGWHFUFUQAVSLLHUFZUEZWAWNUEZUHWBWMABCDVS
        WAGHIDUIUEZLLNOWQUJZPQQABCVRJKILMLNOVRUJZACUKULZDUKULZAGHUCZCDUMUFZULZW
        TXAURAGHXCUQZXDAGHCDUNUFZUQXEPXFXCGHCDUOUPVHZGHXCUSUTCDXBVAVHZVBZQRQSTV
        CABCVTILNOVTUJZXIQVDVIAWOWJWPWLABCVRDGHIJKWILMLNOWSWIUJZXGQRQSTVEABCVTD
        GHWKLNXJWKUJZXGQVFVGVJABCEVRVTJKILMNOWSXJUAXIQRSTVKADVLUEZDFWIWKWFWDWQW
        GWHXMUJZWRXKXLUBAWTXAXHVMABXMLGABXMCDGHNXNXGVNZQVOABXMMGXORVOALMIUFWGWH
        WQUFJWEABCDGHIWQLMNOWRXGQRVPSVOAMLIUFWHWGWQUFKWCABCDGHIWQMLNOWRXGRQVPTV
        OVKVQ $.
    $}

    ${
      fthinv.s $e |- I = ( Inv ` C ) $.
      fthinv.t $e |- J = ( Inv ` D ) $.
      $( A faithful functor reflects inverses.  (Contributed by Mario Carneiro,
         27-Jan-2017.) $)
      fthinv $p |- ( ph -> ( M ( X I Y ) N <->
        ( ( X G Y ) ` M ) ( ( F ` X ) J ( F ` Y ) ) ( ( Y G X ) ` N ) ) ) $=
        ( csect cfv co wbr wa eqid fthsect anbi12d ccat wcel cfunc cfth fthfunc
        cop ssbri syl df-br sylib funcrcl simpld isinv simprd ffvelcdmd 3bitr4d
        cbs funcf1 ) AJKLMCUCUDZUEUFZKJMLVIUEUFZUGJLMFUEUDZKMLFUEUDZLEUDZMEUDZD
        UCUDZUEUFZVMVLVOVNVPUEUFZUGJKLMHUEUFVLVMVNVOIUEUFAVJVQVKVRABCDVIVPEFGJK
        LMNOPQRSTVIUHZVPUHZUIABCDVIVPEFGKJMLNOPRQTSVSVTUIUJABCVIJKHLMNUAACUKULZ
        DUKULZAEFUPZCDUMUEZULZWAWBUGAEFWDUFZWEAEFCDUNUEZUFWFPWGWDEFCDUOUQURZEFW
        DUSUTCDWCVAURZVBQRVSVCADVGUDZDVPVLVMIVNVOWJUHZUBAWAWBWIVDABWJLEABWJCDEF
        NWKWHVHZQVEABWJMEWLRVEVTVCVF $.
    $}
  $}

  ${
    $d f g z B $.  $d f g z C $.  $d f g z H $.  $d f g z ph $.  $d f g z R $.
    $d f D $.  $d f F $.  $d f G $.  $d f I $.  $d f g z X $.  $d f g z Y $.
    $d f J $.
    fthmon.b $e |- B = ( Base ` C ) $.
    fthmon.h $e |- H = ( Hom ` C ) $.
    fthmon.f $e |- ( ph -> F ( C Faith D ) G ) $.
    fthmon.x $e |- ( ph -> X e. B ) $.
    fthmon.y $e |- ( ph -> Y e. B ) $.
    fthmon.r $e |- ( ph -> R e. ( X H Y ) ) $.
    ${
      fthmon.m $e |- M = ( Mono ` C ) $.
      fthmon.n $e |- N = ( Mono ` D ) $.
      fthmon.1 $e |- ( ph ->
        ( ( X G Y ) ` R ) e. ( ( F ` X ) N ( F ` Y ) ) ) $.
      $( A faithful functor reflects monomorphisms.  (Contributed by Mario
         Carneiro, 27-Jan-2017.) $)
      fthmon $p |- ( ph -> R e. ( X M Y ) ) $=
        ( vf vz vg co wcel cv cop cco cfv wceq wi wral w3a chom eqid ccat cfunc
        cbs wbr cfth fthfunc ssbri syl df-br sylib funcrcl simprd adantr funcf1
        ffvelcdmd simpr1 funcf2 simpr2 simpr3 moni funcco eqeq12d simpld bitr3d
        wa catcocl fthi 3bitr3d biimpd ralrimivvva ismon2 mpbir2and ) AEKLIUEUF
        EKLHUEUFZEUBUGZUCUGZKUHLCUIUJZUEZUEZEUDUGZWMUEZUKZWJWOUKZULZUDWKKHUEZUM
        UBWTUMUCBUMRAWSUCUBUDBWTWTAWKBUFZWJWTUFZWOWTUFZUNZWAZWQWRXEEKLGUEUJZWJW
        KKGUEZUJZWKFUJZKFUJZUHLFUJZDUIUJZUEZUEZXFWOXGUJZXMUEZUKZXHXOUKWQWRXEDUS
        UJZDXLXFXHDUOUJZXOJXJXKXIXRUPZXSUPZXLUPZTADUQUFZXDACUQUFZYCAFGUHZCDURUE
        ZUFZYDYCWAAFGYFUTZYGAFGCDVAUEZUTZYHOYIYFFGCDVBVCVDZFGYFVEVFCDYEVGVDZVHV
        IXEBXRKFXEBXRCDFGMXTAYHXDYKVIZVJZAKBUFXDPVIZVKXEBXRLFYNALBUFXDQVIZVKXEB
        XRWKFYNAXAXBXCVLZVKAXFXJXKJUEUFXDUAVIXEWTXIXJXSUEZWJXGXEBCDFGHXSWKKMNYA
        YMYQYOVMZAXAXBXCVNZVKXEWTYRWOXGYSAXAXBXCVOZVKVPXEWNWKLGUEZUJZWPUUBUJZUK
        XQWQXEUUCXNUUDXPXEBCWLDFGHWJEXLWKKLMNWLUPZYBYMYQYOYPYTAWIXDRVIZVQXEBCWL
        DFGHWOEXLWKKLMNUUEYBYMYQYOYPUUAUUFVQVRXEBCDWNWPFGHXSWKLMNYAAYJXDOVIZYQY
        PXEBCWLWJEHWKKLMNUUEAYDXDAYDYCYLVSZVIZYQYOYPYTUUFWBXEBCWLWOEHWKKLMNUUEU
        UIYQYOYPUUAUUFWBWCVTXEBCDWJWOFGHXSWKKMNYAUUGYQYOYTUUAWCWDWEWFAUCBCWLUBU
        DEHIKLMNUUESUUHPQWGWH $.
    $}

    ${
      fthepi.e $e |- E = ( Epi ` C ) $.
      fthepi.p $e |- P = ( Epi ` D ) $.
      fthepi.1 $e |- ( ph ->
        ( ( X G Y ) ` R ) e. ( ( F ` X ) P ( F ` Y ) ) ) $.
      $( A faithful functor reflects epimorphisms.  (Contributed by Mario
         Carneiro, 27-Jan-2017.) $)
      fthepi $p |- ( ph -> R e. ( X E Y ) ) $=
        ( coppc cfv cmon co ctpos chom oppcbas fthoppc oppchom eleqtrrdi ovtpos
        eqid fveq1i eqeltrid ccat wcel cop cfunc wa wbr fthfunc ssbri syl df-br
        cfth sylib funcrcl simprd oppcmon eleqtrrd fthmon simpld eleqtrd ) AFLK
        CUBUCZUDUCZUEKLGUEABVODUBUCZFHIUFZVOUGUCZVPVQUDUCZLKBCVOVOUMZMUHVSUMACD
        VQHIVOWAVQUMZOUIQPAFKLJUELKVSUERCJVOLKNWAUJUKVPUMZVTUMZAFLKVRUEZUCZKHUC
        ZLHUCZEUEZWHWGVTUEAWFFKLIUEZUCWIFWEWJLKIULUNUAUOADEVTVQWHWGWBACUPUQZDUP
        UQZAHIURZCDUSUEZUQZWKWLUTAHIWNVAZWOAHICDVFUEZVAWPOWQWNHICDVBVCVDHIWNVEV
        GCDWMVHVDZVIWDTVJVKVLACGVPVOLKWAAWKWLWRVMWCSVJVN $.
    $}

    ${
      ffthiso.f $e |- ( ph -> F ( C Full D ) G ) $.
      ffthiso.s $e |- I = ( Iso ` C ) $.
      ffthiso.t $e |- J = ( Iso ` D ) $.
      $( A fully faithful functor reflects isomorphisms.  Corollary 3.32 of
         [Adamek] p. 35.  (Contributed by Mario Carneiro, 27-Jan-2017.) $)
      ffthiso $p |- ( ph -> ( R e. ( X I Y ) <->
        ( ( X G Y ) ` R ) e. ( ( F ` X ) J ( F ` Y ) ) ) ) $=
        ( vf co wcel cfv wa cfunc wbr cfth fthfunc ssbri syl simpr funciso cinv
        adantr cv wceq eqid cop df-br sylib funcrcl simpld ad3antrrr cdm simprd
        ccat cbs funcf1 ffvelcdmd isoval eleq2d biimpa wb invfun funfvbrb mpbid
        wfun ad2antrr breqtrd simplr fthinv mpbird inviso1 chom cful wss isohom
        invf ffvelcdmda sseldd fulli r19.29a impbida ) AEKLIUCUDZEKLGUCUEZKFUEZ
        LFUEZJUCZUDZAWPUFBCDFGIJEKLMTUAAFGCDUGUCZUHZWPAFGCDUIUCZUHZXCOXDXBFGCDU
        JUKULZUPAKBUDZWPPUPALBUDZWPQUPAWPUMUNAXAUFZWQWRWSDUOUEZUCZUEZUBUQZLKGUC
        UEZURZWPUBLKHUCZXIXMXPUDZUFZXOUFZBCEXMICUOUEZKLMXTUSZACVHUDZXAXQXOAYBDV
        HUDZAFGUTZXBUDZYBYCUFAXCYEXFFGXBVAVBCDYDVCULZVDVEAXGXAXQXOPVEZAXHXAXQXO
        QVEZTXSEXMKLXTUCUHWQXNXKUHXSWQXLXNXKXIWQXLXKUHZXQXOXIWQXKVFZUDZYIAXAYKA
        WTYJWQADVIUEZDJXJWRWSYLUSZXJUSZAYBYCYFVGZABYLKFABYLCDFGMYMXFVJZPVKZABYL
        LFYPQVKZUAVLVMVNXIXKVSZYKYIVOAYSXAAYLDXJWRWSYMYNYOYQYRVPUPWQXKVQULVRVTX
        RXOUMWAXSBCDFGHXTXJEXMKLMNAXEXAXQXOOVEYGYHAEKLHUCUDXAXQXORVEXIXQXOWBYAY
        NWCWDWEXIBCDXLUBFGHDWFUEZLKMYTUSZNAFGCDWGUCUHXASUPAXHXAQUPAXGXAPUPXIWSW
        RJUCZWSWRYTUCZXLAUUBUUCWHXAAYLDYTJWSWRYMUUAUAYOYRYQWIUPAWTUUBWQXKAYLDJX
        JWRWSYMYNYOYQYRUAWJWKWLWMWNWO $.
    $}
  $}

  ${
    $d x y A $.  $d x y C $.  $d x y D $.  $d x y ph $.  $d x y F $.
    $d x y G $.  $d x y H $.  $d x y R $.
    fthres2b.a $e |- A = ( Base ` C ) $.
    fthres2b.h $e |- H = ( Hom ` C ) $.
    fthres2b.r $e |- ( ph -> R e. ( Subcat ` D ) ) $.
    fthres2b.s $e |- ( ph -> R Fn ( S X. S ) ) $.
    fthres2b.1 $e |- ( ph -> F : A --> S ) $.
    fthres2b.2 $e |- ( ( ph /\ ( x e. A /\ y e. A ) ) ->
      ( x G y ) : Y --> ( ( F ` x ) R ( F ` y ) ) ) $.
    $( Condition for a faithful functor to also be a faithful functor into the
       restriction.  (Contributed by Mario Carneiro, 27-Jan-2017.) $)
    fthres2b $p |- ( ph ->
      ( F ( C Faith D ) G <-> F ( C Faith ( D |`cat R ) ) G ) ) $=
      ( co wbr cfunc cv ccnv wfun wral wa cresc funcres2b anbi1d isfth 3bitr4g
      cfth ) AIJEFUASTZBUBCUBJSUCUDCDUEBDUEZUFIJEFGUGSZUASTZUNUFIJEFULSTIJEUOUL
      STAUMUPUNABCDEFGHIJKLMNOPQRUHUIBCDEFIJMUJBCDEUOIJMUJUK $.
  $}

  ${
    $d x y A $.  $d x y C $.  $d x y D $.  $d x y E $.  $d x y F $.
    $d x y G $.
    fthres2c.a $e |- A = ( Base ` C ) $.
    fthres2c.e $e |- E = ( D |`s S ) $.
    fthres2c.d $e |- ( ph -> D e. Cat ) $.
    fthres2c.r $e |- ( ph -> S e. V ) $.
    fthres2c.1 $e |- ( ph -> F : A --> S ) $.
    $( Condition for a faithful functor to also be a faithful functor into the
       restriction.  (Contributed by Mario Carneiro, 30-Jan-2017.) $)
    fthres2c $p |- ( ph -> ( F ( C Faith D ) G <-> F ( C Faith E ) G ) ) $=
      ( vx vy cfunc co wbr cv ccnv wfun wral wa funcres2c anbi1d isfth 3bitr4g
      cfth ) AGHCDQRSZOTPTHRUAUBPBUCOBUCZUDGHCFQRSZUKUDGHCDUIRSGHCFUIRSAUJULUKA
      BCDEFGHIJKLMNUEUFOPBCDGHJUGOPBCFGHJUGUH $.
  $}

  ${
    $d f g x y C $.  $d f g x y D $.  $d f g x y R $.
    $( A faithful functor into a restricted category is also a faithful functor
       into the whole category.  (Contributed by Mario Carneiro,
       27-Jan-2017.) $)
    fthres2 $p |- ( R e. ( Subcat ` D ) ->
      ( C Faith ( D |`cat R ) ) C_ ( C Faith D ) ) $=
      ( vf vg vx vy csubc cfv wcel cresc co cfth cv wbr cfunc wral isfth df-br
      wa wrel relfth a1i cop ccnv wfun cbs funcres2 anim1d eqid 3imtr4g 3imtr3g
      ssbrd relssdv ) CBHIJZDEABCKLZMLZABMLZUQUAUOAUPUBUCUODNZENZUQOZUSUTUROZUS
      UTUDZUQJVCURJUOUSUTAUPPLZOZFNGNUTLUEUFGAUGIZQFVFQZTUSUTABPLZOZVGTVAVBUOVE
      VIVGUOVDVHUSUTABCUHUMUIFGVFAUPUSUTVFUJZRFGVFABUSUTVJRUKUSUTUQSUSUTURSULUN
      $.
  $}

  ${
    $d x y C $.  $d x y I $.
    idffth.i $e |- I = ( idFunc ` C ) $.
    $( The identity functor is a fully faithful functor.  (Contributed by Mario
       Carneiro, 27-Jan-2017.) $)
    idffth $p |- ( C e. Cat -> I e. ( ( C Full C ) i^i ( C Faith C ) ) ) $=
      ( vx vy ccat wcel c1st cfv c2nd cop co wbr cv wf1o wral df-br eqid idfu1
      wa cful cfth cin cfunc wrel wceq relfunc idfucl sylancr chom cbs eqeltrrd
      1st2nd sylibr cid cres f1oi simpl simprl simprr idfu2nd oveq12d f1oeq123d
      eqidd mpbiri ralrimivva isffth2 sylanbrc sylib eqeltrd ) AFGZBBHIZBJIZKZA
      AUALAAUBLUCZVKAAUDLZUEBVPGBVNUFAAUGABCUHZBVPUMUIZVKVLVMVOMZVNVOGVKVLVMVPM
      ZDNZENZAUJIZLZWAVLIZWBVLIZWCLZWAWBVMLZOZEAUKIZPDWJPVSVKVNVPGVTVKBVNVPVRVQ
      ULVLVMVPQUNVKWIDEWJWJVKWAWJGZWBWJGZTZTZWIWDWDUOWDUPZOWDUQWNWDWDWGWDWHWOWN
      WJAWCBWAWBCWJRZVKWMURZWCRZVKWKWLUSZVKWKWLUTZVAWNWDVDWNWEWAWFWBWCWNWJABWAC
      WPWQWSSWNWJABWBCWPWQWTSVBVCVEVFDEWJAAVLVMWCWCWPWRWRVGVHVLVMVOQVIVJ $.
  $}

  ${
    $d x y C $.  $d x y E $.  $d x y F $.  $d x y G $.  $d x y ph $.
    cofull.f $e |- ( ph -> F e. ( C Full D ) ) $.
    cofull.g $e |- ( ph -> G e. ( D Full E ) ) $.
    $( The composition of two full functors is full.  Proposition 3.30(d) in
       [Adamek] p. 35.  (Contributed by Mario Carneiro, 28-Jan-2017.) $)
    cofull $p |- ( ph -> ( G o.func F ) e. ( C Full E ) ) $=
      ( vx vy co cfv wrel wcel sylancr wbr wfo 1st2ndbr eqid adantr ccofu cfunc
      c1st c2nd cop cful wceq relfunc fullfunc sselid cofucl 1st2nd cv chom cbs
      wral wa ccom relfull funcf1 simprl ffvelcdmd simprr syl2anc cofu2nd eqidd
      fullfo foco cofu1 oveq12d foeq123d mpbird ralrimivva sylanbrc df-br sylib
      isfull2 eqeltrd ) AFEUAKZVSUCLZVSUDLZUEZBDUFKZABDUBKZMZVSWDNZVSWBUGBDUHZA
      BCDEFABCUFKZBCUBKZEBCUIGUJZACDUFKZCDUBKZFCDUIHUJZUKZVSWDULOAVTWAWCPZWBWCN
      AVTWAWDPZIUMZJUMZBUNLZKZWQVTLZWRVTLZDUNLZKZWQWRWAKZQZJBUOLZUPIXGUPWOAWEWF
      WPWGWNVSWDROAXFIJXGXGAWQXGNZWRXGNZUQZUQZXFWTWQEUCLZLZFUCLZLZWRXLLZXNLZXCK
      ZXMXPFUDLZKZWQWREUDLZKZURZQZXKXMXPCUNLZKZXRXTQWTYFYBQYDXKCUOLZCDXNXSYEXCX
      MXPYGSZXCSZYESZXKWKMFWKNZXNXSWKPCDUSAYKXJHTFWKROXKXGYGWQXLXKXGYGBCXLYAXGS
      ZYHXKWIMEWINZXLYAWIPBCUHAYMXJWJTZEWIROUTZAXHXIVAZVBXKXGYGWRXLYOAXHXIVCZVB
      VGXKXGBCXLYAWSYEWQWRYLYJWSSZXKWHMEWHNZXLYAWHPBCUSAYSXJGTEWHROYPYQVGWTYFXR
      XTYBVHVDXKWTWTXDXRXEYCXKXGBCDEFWQWRYLYNAFWLNXJWMTZYPYQVEXKWTVFXKXAXOXBXQX
      CXKXGBCDEFWQYLYNYTYPVIXKXGBCDEFWRYLYNYTYQVIVJVKVLVMIJXGBDVTWAWSXCYLYIYRVQ
      VNVTWAWCVOVPVR $.
  $}

  ${
    $d x y C $.  $d x y E $.  $d x y F $.  $d x y G $.  $d x y ph $.
    cofth.f $e |- ( ph -> F e. ( C Faith D ) ) $.
    cofth.g $e |- ( ph -> G e. ( D Faith E ) ) $.
    $( The composition of two faithful functors is faithful.  Proposition
       3.30(c) in [Adamek] p. 35.  (Contributed by Mario Carneiro,
       28-Jan-2017.) $)
    cofth $p |- ( ph -> ( G o.func F ) e. ( C Faith E ) ) $=
      ( vx vy co cfv wrel wcel sylancr wbr wf1 1st2ndbr eqid adantr ccofu cfunc
      c1st c2nd cop cfth wceq relfunc fthfunc sselid cofucl 1st2nd cv chom wral
      cbs ccom relfth funcf1 simprl ffvelcdmd simprr fthf1 f1co syl2anc cofu2nd
      wa eqidd cofu1 oveq12d f1eq123d mpbird ralrimivva isfth2 sylanbrc eqeltrd
      df-br sylib ) AFEUAKZVSUCLZVSUDLZUEZBDUFKZABDUBKZMZVSWDNZVSWBUGBDUHZABCDE
      FABCUFKZBCUBKZEBCUIGUJZACDUFKZCDUBKZFCDUIHUJZUKZVSWDULOAVTWAWCPZWBWCNAVTW
      AWDPZIUMZJUMZBUNLZKZWQVTLZWRVTLZDUNLZKZWQWRWAKZQZJBUPLZUOIXGUOWOAWEWFWPWG
      WNVSWDROAXFIJXGXGAWQXGNZWRXGNZVGZVGZXFWTWQEUCLZLZFUCLZLZWRXLLZXNLZXCKZXMX
      PFUDLZKZWQWREUDLZKZUQZQZXKXMXPCUNLZKZXRXTQWTYFYBQYDXKCUPLZCDXNXSYEXCXMXPY
      GSZYESZXCSZXKWKMFWKNZXNXSWKPCDURAYKXJHTFWKROXKXGYGWQXLXKXGYGBCXLYAXGSZYHX
      KWIMEWINZXLYAWIPBCUHAYMXJWJTZEWIROUSZAXHXIUTZVAXKXGYGWRXLYOAXHXIVBZVAVCXK
      XGBCXLYAWSYEWQWRYLWSSZYIXKWHMEWHNZXLYAWHPBCURAYSXJGTEWHROYPYQVCWTYFXRXTYB
      VDVEXKWTWTXDXRXEYCXKXGBCDEFWQWRYLYNAFWLNXJWMTZYPYQVFXKWTVHXKXAXOXBXQXCXKX
      GBCDEFWQYLYNYTYPVIXKXGBCDEFWRYLYNYTYQVIVJVKVLVMIJXGBDVTWAWSXCYLYRYJVNVOVT
      WAWCVQVRVP $.
  $}

  ${
    coffth.f $e |- ( ph -> F e. ( ( C Full D ) i^i ( C Faith D ) ) ) $.
    coffth.g $e |- ( ph -> G e. ( ( D Full E ) i^i ( D Faith E ) ) ) $.
    $( The composition of two fully faithful functors is fully faithful.
       (Contributed by Mario Carneiro, 28-Jan-2017.) $)
    coffth $p |- ( ph ->
      ( G o.func F ) e. ( ( C Full E ) i^i ( C Faith E ) ) ) $=
      ( cful co cfth ccofu elin1d cofull elin2d cofth elind ) ABDIJBDKJFELJABCD
      EFABCIJZBCKJZEGMACDIJZCDKJZFHMNABCDEFARSEGOATUAFHOPQ $.
  $}

  ${
    rescfth.d $e |- D = ( C |`cat J ) $.
    rescfth.i $e |- I = ( idFunc ` D ) $.
    $( The inclusion functor from a subcategory is a faithful functor.
       (Contributed by Mario Carneiro, 27-Jan-2017.) $)
    rescfth $p |- ( J e. ( Subcat ` C ) -> I e. ( D Faith C ) ) $=
      ( csubc cfv wcel cfth cresc oveq2i fthres2 eqsstrid cful ccat cin subccat
      co id idffth syl elin2d sseldd ) DAGHIZBBJSZBAJSZCUEUFBADKSZJSUGBUHBJELBA
      DMNUEBBOSZUFCUEBPICUIUFQIUEABDEUETRBCFUAUBUCUD $.
  $}

  ${
    $d x y C $.  $d x y D $.  $d x y I $.  $d x y S $.  $d x y V $.
    ressffth.d $e |- D = ( C |`s S ) $.
    ressffth.i $e |- I = ( idFunc ` D ) $.
    $( The inclusion functor from a full subcategory is a full and faithful
       functor, see also remark 4.4(2) in [Adamek] p. 49.  (Contributed by
       Mario Carneiro, 27-Jan-2017.) $)
    ressffth $p |- ( ( C e. Cat /\ S e. V ) ->
      I e. ( ( D Full C ) i^i ( D Faith C ) ) ) $=
      ( vx vy ccat wcel wa cfv co cfunc wceq cress chomf ccomf eqid cop relfunc
      c1st c2nd cful cfth cin resscat eqeltrid idfucl syl 1st2nd sylancr wbr cv
      wrel chom wf1o cbs wral cxp cres cresc cvv ressinbas adantl eqtrid fveq2d
      eqidd simpl wss inss2 a1i simpld eqtrd simprd ovexi ovexd funcpropd csubc
      fullresc fullsubc funcres2 eqsstrd sseldd eqeltrrd sylibr cid f1oi adantr
      df-br simprl idfu2nd resshom ad2antlr idfu1 oveq123d f1oeq123d ralrimivva
      simprr mpbiri isffth2 sylanbrc sylib eqeltrd ) AJKZCEKZLZDDUCMZDUDMZUAZBA
      UENBAUFNUGZXHBBONZUPDXMKZDXKPBBUBXHBJKZXNXHBACQNZJFACEUHUIZBDGUJUKZDXMULU
      MZXHXIXJXLUNZXKXLKXHXIXJBAONZUNZHUOZIUOZBUQMZNZYCXIMZYDXIMZAUQMZNZYCYDXJN
      ZURZIBUSMZUTHYMUTXTXHXKYAKYBXHDXKYAXSXHXMYADXHXMBAARMZCAUSMZUGZYPVAVBZVCN
      ZONZYAXHBBBYRVDXHBRMZVIXHBSMZVIXHYTAYPQNZRMZYRRMZXHBUUBRXHBXPUUBFXGXPUUBP
      XFCYOAEYOTZVEVFVGZVHXHUUCUUDPZUUBSMZYRSMZPZXHYOAUUBYPYRYNUUEYNTZXFXGVJZYP
      YOVKXHCYOVLVMZUUBTYRTWAZVNVOXHUUAUUHUUIXHBUUBSUUFVHXHUUGUUJUUNVPVOBVDKXHB
      ACQFVQVMZUUOUUOXHAYQVCVRVSXHYQAVTMKYSYAVKXHYOAYPYNUUEUUKUULUUMWBBAYQWCUKW
      DXRWEWFXIXJYAWKWGXHYLHIYMYMXHYCYMKZYDYMKZLZLZYLYFYFWHYFVBZURYFWIUUSYFYFYJ
      YFYKUUTUUSYMBYEDYCYDGYMTZXHXOUURXQWJZYETZXHUUPUUQWLZXHUUPUUQWTZWMUUSYFVIU
      USYGYCYHYDYIYEXGYIYEPXFUURCABYIEFYITZWNWOUUSYMBDYCGUVAUVBUVDWPUUSYMBDYDGU
      VAUVBUVEWPWQWRXAWSHIYMBAXIXJYEYIUVAUVCUVFXBXCXIXJXLWKXDXE $.
  $}

  ${
    $d x y A $.  $d x y C $.  $d x y D $.  $d x y E $.  $d x y ph $.
    $d x y F $.  $d x y G $.
    ffthres2c.a $e |- A = ( Base ` C ) $.
    ffthres2c.e $e |- E = ( D |`s S ) $.
    ffthres2c.d $e |- ( ph -> D e. Cat ) $.
    ffthres2c.r $e |- ( ph -> S e. V ) $.
    ffthres2c.1 $e |- ( ph -> F : A --> S ) $.
    $( Condition for a full functor to also be a full functor into the
       restriction.  (Contributed by Mario Carneiro, 30-Jan-2017.) $)
    fullres2c $p |- ( ph -> ( F ( C Full D ) G <-> F ( C Full E ) G ) ) $=
      ( vx vy co wbr cfv wral cfunc cv chom wceq wa cful funcres2c wcel resshom
      crn eqid syl oveqd eqeq2d 2ralbidv anbi12d isfull 3bitr4g ) AGHCDUAQRZOUB
      ZPUBZHQUJZUTGSZVAGSZDUCSZQZUDZPBTOBTZUEGHCFUAQRZVBVCVDFUCSZQZUDZPBTOBTZUE
      GHCDUFQRGHCFUFQRAUSVIVHVMABCDEFGHIJKLMNUGAVGVLOPBBAVFVKVBAVEVJVCVDAEIUHVE
      VJUDMEDFVEIKVEUKZUIULUMUNUOUPOPBCDGHVEJVNUQOPBCFGHVJJVJUKUQUR $.

    $( Condition for a fully faithful functor to also be a fully faithful
       functor into the restriction.  (Contributed by Mario Carneiro,
       27-Jan-2017.) $)
    ffthres2c $p |- ( ph -> ( F ( ( C Full D ) i^i ( C Faith D ) ) G <->
      F ( ( C Full E ) i^i ( C Faith E ) ) G ) ) $=
      ( cful co wbr cfth wa cin fullres2c fthres2c anbi12d brin 3bitr4g ) AGHCD
      OPZQZGHCDRPZQZSGHCFOPZQZGHCFRPZQZSGHUFUHTQGHUJULTQAUGUKUIUMABCDEFGHIJKLMN
      UAABCDEFGHIJKLMNUBUCGHUFUHUDGHUJULUDUE $.
  $}

  ${
    $d B x y $.  $d C x y $.  $d J x y $.  $d S x y $.
    inclfusubc.j $e |- ( ph -> J e. ( Subcat ` C ) ) $.
    inclfusubc.s $e |- S = ( C |`cat J ) $.
    inclfusubc.b $e |- B = ( Base ` S ) $.
    inclfusubc.f $e |- ( ph -> F = ( _I |` B ) ) $.
    inclfusubc.g $e |- ( ph -> G = ( x e. B , y e. B
                                     |-> ( _I |` ( x J y ) ) ) ) $.
    $( The "inclusion functor" from a subcategory of a category into the
       category itself.  (Contributed by AV, 30-Mar-2020.) $)
    inclfusubc $p |- ( ph -> F ( S Func C ) G ) $=
      ( co cfv wcel syl cop cid cfunc wbr cidfu cfth fthfunc csubc eqid rescfth
      sselid df-br cres cmpo opeq12d wceq idfusubc eqtr4d eleq1d bitrid mpbird
      cv ) AGHFEUAOZUBZFUCPZVAQZAFEUDOZVAVCFEUEAIEUFPQZVCVEQJEFVCIKVCUGZUHRUIVB
      GHSZVAQAVDGHVAUJAVHVCVAAVHTDUKZBCDDTBUTCUTIOUKULZSZVCAGVIHVJMNUMAVFVCVKUN
      JBCDEFVCIKVGLUORUPUQURUS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Natural transformations and the functor category
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Nat $.
  $c FuncCat $.

  $( Extend class notation to include the collection of natural
     transformations. $)
  cnat $a class Nat $.

  $( Extend class notation to include the functor category. $)
  cfuc $a class FuncCat $.

  ${
    $d a b f g h r s t u v x y $.  $d a h x y A $.  $d a f g r s t u x y B $.
    $d a f g h r s t u x y C $.  $d a f g h r s x y F $.  $d a f g r s t u J $.
    $d a f g h r s x y G $.  $d a f g h r s t u H $.  $d a f g h r s x y ph $.
    $d a f g h r s x y K $.  $d a f g h r s x y L $.  $d a f g r s t u .x. $.
    $d a f g h r s t u x y D $.
    $( Definition of a natural transformation between two functors.  A natural
       transformation ` A : F --> G ` is a collection of arrows
       ` A ( x ) : F ( x ) --> G ( x ) ` , such that
       ` A ( y ) o. F ( h ) = G ( h ) o. A ( x ) ` for each morphism
       ` h : x --> y ` .  Definition 6.1 in [Adamek] p. 83, and definition in
       [Lang] p. 65.  (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    df-nat $a |- Nat = ( t e. Cat , u e. Cat |->
      ( f e. ( t Func u ) , g e. ( t Func u ) |->
        [_ ( 1st ` f ) / r ]_ [_ ( 1st ` g ) / s ]_
          { a e. X_ x e. ( Base ` t ) ( ( r ` x ) ( Hom ` u ) ( s ` x ) ) |
        A. x e. ( Base ` t ) A. y e. ( Base ` t ) A. h e. ( x ( Hom ` t ) y )
      ( ( a ` y ) ( <. ( r ` x ) , ( r ` y ) >.
          ( comp ` u ) ( s ` y ) ) ( ( x ( 2nd ` f ) y ) ` h ) ) =
      ( ( ( x ( 2nd ` g ) y ) ` h ) ( <. ( r ` x ) , ( s ` x ) >.
          ( comp ` u ) ( s ` y ) ) ( a ` x ) ) } ) ) $.

    $( Definition of the category of functors between two fixed categories,
       with the objects being functors and the morphisms being natural
       transformations.  Definition 6.15 in [Adamek] p. 87.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)
    df-fuc $a |- FuncCat = ( t e. Cat , u e. Cat |->
      { <. ( Base ` ndx ) , ( t Func u ) >. ,
        <. ( Hom ` ndx ) , ( t Nat u ) >. ,
        <. ( comp ` ndx ) ,
          ( v e. ( ( t Func u ) X. ( t Func u ) ) , h e. ( t Func u ) |->
            [_ ( 1st ` v ) / f ]_ [_ ( 2nd ` v ) / g ]_
          ( b e. ( g ( t Nat u ) h ) , a e. ( f ( t Nat u ) g ) |->
            ( x e. ( Base ` t ) |-> ( ( b ` x )
              ( <. ( ( 1st ` f ) ` x ) , ( ( 1st ` g ) ` x ) >. ( comp ` u )
                   ( ( 1st ` h ) ` x ) ) ( a ` x ) ) ) ) ) >. } ) $.

    $( The ` FuncCat ` operation is a well-defined function on categories.
       (Contributed by Mario Carneiro, 12-Jan-2017.) $)
    fnfuc $p |- FuncCat Fn ( Cat X. Cat ) $=
      ( vt vu vv vh vf vg vb va vx ccat cnx cbs cfv cv co cop cco c1st cmpo csb
      cfunc chom cnat cxp c2nd cmpt ctp cfuc df-fuc tpex fnmpoi ) ABJJKLMANZBNZ
      UAOZPZKUBMULUMUCOZPZKQMCDUNUNUDUNECNZRMFURUEMGHFNZDNZUPOENZUSUPOIULLMINZG
      NMVBHNMVBVARMMVBUSRMMPVBUTRMMUMQMOOUFSTTSPZUGUHICBAEFDHGUIUOUQVCUJUK $.

    natfval.1 $e |- N = ( C Nat D ) $.
    natfval.b $e |- B = ( Base ` C ) $.
    natfval.h $e |- H = ( Hom ` C ) $.
    natfval.j $e |- J = ( Hom ` D ) $.
    natfval.o $e |- .x. = ( comp ` D ) $.
    $( Value of the function giving natural transformations between two
       categories.  (Contributed by Mario Carneiro, 6-Jan-2017.)  (Proof
       shortened by AV, 1-Mar-2024.) $)
    natfval $p |- N = ( f e. ( C Func D ) , g e. ( C Func D ) |->
        [_ ( 1st ` f ) / r ]_ [_ ( 1st ` g ) / s ]_
          { a e. X_ x e. B ( ( r ` x ) J ( s ` x ) ) |
        A. x e. B A. y e. B A. h e. ( x H y )
      ( ( a ` y ) ( <. ( r ` x ) , ( r ` y ) >.
          .x. ( s ` y ) ) ( ( x ( 2nd ` f ) y ) ` h ) ) =
      ( ( ( x ( 2nd ` g ) y ) ` h ) ( <. ( r ` x ) , ( s ` x ) >.
          .x. ( s ` y ) ) ( a ` x ) ) } ) $=
      ( vt vu cnat co cfunc c1st cfv c2nd cop wceq wral cixp crab csb cmpo ccat
      cv wcel wa cco chom cbs oveq12 simpl eqtr4di ixpeq1d simpr oveqd ixpeq2dv
      fveq2d eqtrd eqeq12d raleqbidv rabeqbidv csbeq2dv mpoeq123dv df-nat mpoex
      ovex ovmpoa wn c0 mpondm0 wo funcrcl con3i eq0rdv olcd syl eqtr4d pm2.61i
      0mpo0 eqtri ) LDEUCUDZGHDEUEUDZWONGUQZUFUGZMHUQZUFUGZBUQZOUQZUGZIUQZAUQZW
      TWPUHUGUDUGZXDNUQZUGZWTXFUGUIZWTMUQZUGZFUDZUDZXCXDWTWRUHUGUDUGZXDXAUGZXGX
      DXIUGZUIZXJFUDZUDZUJZIXDWTJUDZUKZBCUKZACUKZOACXGXOKUDZULZUMZUNZUNZUOZPDUP
      UREUPURUSZWNYIUJUAUBDEUPUPGHUAUQZUBUQZUEUDZYMNWQMWSXBXEXHXJYLUTUGZUDZUDZX
      MXNXPXJYNUDZUDZUJZIXDWTYKVAUGZUDZUKZBYKVBUGZUKZAUUCUKZOAUUCXGXOYLVAUGZUDZ
      ULZUMZUNZUNZUOZYIUCYKDUJZYLEUJZUSZGHYMYMUUKWOWOYHYKDYLEUEVCZUUPUUONWQUUJY
      GUUOMWSUUIYFUUOUUEYCOUUHYEUUOUUHACUUGULYEUUOAUUCCUUGUUOUUCDVBUGCUUOYKDVBU
      UMUUNVDZVJQVEZVFUUOACUUGYDUUOUUFKXGXOUUOUUFEVAUGKUUOYLEVAUUMUUNVGZVJSVEVH
      VIVKUUOUUDYBAUUCCUURUUOUUBYABUUCCUURUUOYSXSIUUAXTUUOYTJXDWTUUOYTDVAUGJUUO
      YKDVAUUQVJRVEVHUUOYPXLYRXRUUOYOXKXBXEUUOYNFXHXJUUOYNEUTUGFUUOYLEUTUUSVJTV
      EZVHVHUUOYQXQXMXNUUOYNFXPXJUUTVHVHVLVMVMVMVNVOVOVPABUBUAGHIMNOVQZGHWOWOYH
      DEUEVSZUVBVRVTYJWAZWNWBYIUAUBUULUCDEUPUPUVAWCUVCWOWBUJZUVDWDYIWBUJUVCUVDU
      VDUVCGWOWPWOURYJDEWPWEWFWGWHGHWOWOYHWLWIWJWKWM $.

    ${
      isnat.f $e |- ( ph -> F ( C Func D ) G ) $.
      isnat.g $e |- ( ph -> K ( C Func D ) L ) $.
      $( Property of being a natural transformation.  (Contributed by Mario
         Carneiro, 6-Jan-2017.) $)
      isnat $p |- ( ph -> ( A e. ( <. F , G >. N <. K , L >. ) <->
            ( A e. X_ x e. B ( ( F ` x ) J ( K ` x ) ) /\
          A. x e. B A. y e. B A. h e. ( x H y )
        ( ( A ` y ) ( <. ( F ` x ) , ( F ` y ) >.
            .x. ( K ` y ) ) ( ( x G y ) ` h ) ) =
        ( ( ( x L y ) ` h ) ( <. ( F ` x ) , ( K ` x ) >.
            .x. ( K ` y ) ) ( A ` x ) ) ) ) ) $=
        ( va vf vg vr vs cop co wcel cv cfv wceq wral cixp crab cfunc c1st c2nd
        csb cvv cmpo natfval a1i fvexd simprl fveq2d wrel wbr relfunc brrelex12
        wa sylancr op1stg syl adantr eqtrd simplrr ad2antrr simplr fveq1d simpr
        oveq12d ixpeq2dv opeq12d eqidd ad3antrrr oveqd oveq123d eqeq12d ralbidv
        op2ndg 2ralbidv rabeqbidv csbied2 df-br sylib rgenw ixpexg ax-mp ovmpod
        ovex rabex eleq2d fveq1 oveq1d oveq2d elrab bitrdi ) ADJKUIZNOUIZPUJZUK
        DCULZUDULZUMZIULZBULZXNKUJZUMZXRJUMZXNJUMZUIZXNNUMZHUJZUJZXQXRXNOUJZUMZ
        XRXOUMZYAXRNUMZUIZYDHUJZUJZUNZIXRXNLUJZUOZCEUOBEUOZUDBEYAYJMUJZUPZUQZUK
        DYSUKXNDUMZXTYEUJZYHXRDUMZYLUJZUNZIYOUOZCEUOBEUOZVMAXMYTDAUEUFXKXLFGURU
        JZUUHUGUEULZUSUMZUHUFULZUSUMZXPXQXRXNUUIUTUMZUJZUMZXRUGULZUMZXNUUPUMZUI
        ZXNUHULZUMZHUJZUJZXQXRXNUUKUTUMZUJZUMZYIUUQXRUUTUMZUIZUVAHUJZUJZUNZIYOU
        OZCEUOBEUOZUDBEUUQUVGMUJZUPZUQZVAZVAZYTPVBPUEUFUUHUUHUVRVCUNABCEFGHUEUF
        ILMPUHUGUDQRSTUAVDVEAUUIXKUNZUUKXLUNZVMZVMZUGUUJJUVQYTVBUWBUUIUSVFUWBUU
        JXKUSUMZJUWBUUIXKUSAUVSUVTVGZVHAUWCJUNZUWAAJVBUKKVBUKVMZUWEAUUHVIZJKUUH
        VJZUWFFGVKZUBJKUUHVLVNZJKVBVBVOVPVQVRUWBUUPJUNZVMZUHUULNUVPYTVBUWLUUKUS
        VFUWLUULXLUSUMZNUWLUUKXLUSAUVSUVTUWKVSZVHAUWMNUNZUWAUWKANVBUKOVBUKVMZUW
        OAUWGNOUUHVJZUWPUWIUCNOUUHVLVNZNOVBVBVOVPVTVRUWLUUTNUNZVMZUVMYQUDUVOYSU
        WTBEUVNYRUWTUUQYAUVGYJMUWTXRUUPJUWBUWKUWSWAZWBZUWTXRUUTNUWLUWSWCZWBZWDW
        EUWTUVLYPBCEEUWTUVKYNIYOUWTUVCYFUVJYMUWTXPXPUUOXTUVBYEUWTUUSYCUVAYDHUWT
        UUQYAUURYBUXBUWTXNUUPJUXAWBWFUWTXNUUTNUXCWBZWDUWTXPWGUWTXQUUNXSUWTUUMKX
        RXNUWTUUMXKUTUMZKUWTUUIXKUTUWBUVSUWKUWSUWDVTVHAUXFKUNZUWAUWKUWSAUWFUXGU
        WJJKVBVBWMVPWHVRWIWBWJUWTUVFYHYIYIUVIYLUWTUVHYKUVAYDHUWTUUQYAUVGYJUXBUX
        DWFUXEWDUWTXQUVEYGUWTUVDOXRXNUWTUVDXLUTUMZOUWTUUKXLUTUWLUVTUWSUWNVQVHAU
        XHOUNZUWAUWKUWSAUWPUXIUWRNOVBVBWMVPWHVRWIWBUWTYIWGWJWKWLWNWOWPWPAUWHXKU
        UHUKUBJKUUHWQWRAUWQXLUUHUKUCNOUUHWQWRYTVBUKAYQUDYSYRVBUKZBEUOYSVBUKUXJB
        EYAYJMXCWSBEYRVBWTXAXDVEXBXEYQUUGUDDYSXODUNZYPUUFBCEEUXKYNUUEIYOUXKYFUU
        BYMUUDUXKXPUUAXTYEXNXODXFXGUXKYIUUCYHYLXRXODXFXHWKWLWNXIXJ $.
    $}

    isnat2.f $e |- ( ph -> F e. ( C Func D ) ) $.
    isnat2.g $e |- ( ph -> G e. ( C Func D ) ) $.
    $( Property of being a natural transformation.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    isnat2 $p |- ( ph -> ( A e. ( F N G ) <->
          ( A e. X_ x e. B ( ( ( 1st ` F ) ` x ) J ( ( 1st ` G ) ` x ) ) /\
        A. x e. B A. y e. B A. h e. ( x H y )
      ( ( A ` y ) ( <. ( ( 1st ` F ) ` x ) , ( ( 1st ` F ) ` y ) >.
          .x. ( ( 1st ` G ) ` y ) ) ( ( x ( 2nd ` F ) y ) ` h ) ) =
      ( ( ( x ( 2nd ` G ) y ) ` h ) ( <. ( ( 1st ` F ) ` x ) ,
        ( ( 1st ` G ) ` x ) >. .x. ( ( 1st ` G ) ` y ) ) ( A ` x ) ) ) ) ) $=
      ( co wcel c1st cfv c2nd cv cixp wceq wral wa cfunc relfunc 1st2nd sylancr
      cop wrel oveq12d eleq2d wbr 1st2ndbr isnat bitrd ) ADJKNUBZUCDJUDUEZJUFUE
      ZUPZKUDUEZKUFUEZUPZNUBZUCDBEBUGZVEUEZVLVHUEZMUBUHUCCUGZDUEIUGZVLVOVFUBUEV
      MVOVEUEUPVOVHUEZHUBUBVPVLVOVIUBUEVLDUEVMVNUPVQHUBUBUIIVLVOLUBUJCEUJBEUJUK
      AVDVKDAJVGKVJNAFGULUBZUQZJVRUCZJVGUIFGUMZTJVRUNUOAVSKVRUCZKVJUIWAUAKVRUNU
      OURUSABCDEFGHIVEVFLMVHVINOPQRSAVSVTVEVFVRUTWATJVRVAUOAVSWBVHVIVRUTWAUAKVR
      VAUOVBVC $.
  $}

  ${
    $d f x y z A $.  $d f x y z F $.  $d f x y z G $.  $d f H $.  $d f x y R $.
    $d a f g h r s x y z C $.  $d f x y z K $.  $d f x y z ph $.  $d f x y X $.
    $d a f g h r s x y z D $.  $d f x y z L $.  $d f x y .x. $.  $d f x y Y $.
    $d x y B $.  $d x J $.
    natrcl.1 $e |- N = ( C Nat D ) $.
    $( The natural transformation set operation is a well-defined function.
       (Contributed by Mario Carneiro, 12-Jan-2017.) $)
    natffn $p |- N Fn ( ( C Func D ) X. ( C Func D ) ) $=
      ( vf vg vr vs vy va vh vx co cv c1st cfv c2nd wral eqid cvv cfunc cop cco
      wceq chom cbs cixp crab natfval wcel ovex rgenw ixpexg ax-mp rabex fnmpoi
      csb csbex ) EFABUAMZUSGENZOPZHFNZOPZINZJNZPKNZLNZVDUTQPMPVGGNZPZVDVHPUBVD
      HNZPZBUCPZMMVFVGVDVBQPMPVGVEPVIVGVJPZUBVKVLMMUDKVGVDAUEPZMRIAUFPZRLVORZJL
      VOVIVMBUEPZMZUGZUHZUQZUQCLIVOABVLEFKVNVQCHGJDVOSVNSVQSVLSUIGVAWAHVCVTVPJV
      SVRTUJZLVORVSTUJWBLVOVIVMVQUKULLVOVRTUMUNUOURURUP $.

    $( Reverse closure for a natural transformation.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    natrcl $p |- ( A e. ( F N G ) ->
      ( F e. ( C Func D ) /\ G e. ( C Func D ) ) ) $=
      ( vf vg vr vs vy va vh vx co cv cfv wral eqid c1st c2nd cop cco wceq chom
      cfunc cbs cixp crab csb natfval elmpocl ) HIBCUGPZUNJHQZUARKIQZUARLQZMQZR
      NQZOQZUQUOUBRPRUTJQZRZUQVARUCUQKQZRZCUDRZPPUSUTUQUPUBRPRUTURRVBUTVCRZUCVD
      VEPPUENUTUQBUFRZPSLBUHRZSOVHSMOVHVBVFCUFRZPUIUJUKUKDEFAOLVHBCVEHINVGVIFKJ
      MGVHTVGTVITVETULUM $.

    ${
      nat1st2nd.2 $e |- ( ph -> A e. ( F N G ) ) $.
      $( Rewrite the natural transformation predicate with separated functor
         parts.  (Contributed by Mario Carneiro, 6-Jan-2017.) $)
      nat1st2nd $p |- ( ph -> A e. ( <. ( 1st ` F ) , ( 2nd ` F ) >. N
          <. ( 1st ` G ) , ( 2nd ` G ) >. ) ) $=
        ( co c1st cfv c2nd cop cfunc wrel wcel wceq 1st2nd sylancr relfunc syl
        wa natrcl simpld simprd oveq12d eleqtrd ) ABEFGJZEKLEMLNZFKLFMLNZGJIAEU
        JFUKGACDOJZPZEULQZEUJRCDUAZAUNFULQZABUIQUNUPUCIBCDEFGHUDUBZUEEULSTAUMUP
        FUKRUOAUNUPUQUFFULSTUGUH $.
    $}

    natixp.2 $e |- ( ph -> A e. ( <. F , G >. N <. K , L >. ) ) $.
    natixp.b $e |- B = ( Base ` C ) $.
    ${
      natixp.j $e |- J = ( Hom ` D ) $.
      $( A natural transformation is a function from the objects of ` C ` to
         homomorphisms from ` F ( x ) ` to ` G ( x ) ` .  (Contributed by Mario
         Carneiro, 6-Jan-2017.) $)
      natixp $p |- ( ph -> A e. X_ x e. B ( ( F ` x ) J ( K ` x ) ) ) $=
        ( cfv co wcel cop vy vz cv cixp cco wceq chom wral wa eqid cfunc natrcl
        wbr syl simpld df-br sylibr simprd isnat mpbid ) ACBDBUCZGQZVAJQZIRUDSZ
        UAUCZCQUBUCZVAVEHRQVBVEGQTVEJQZFUEQZRRVFVAVEKRQVACQVBVCTVGVHRRUFUBVAVEE
        UGQZRUHUADUHBDUHZACGHTZJKTZLRSZVDVJUINABUACDEFVHUBGHVIIJKLMOVIUJPVHUJAV
        KEFUKRZSZGHVNUMAVOVLVNSZAVMVOVPUINCEFVKVLLMULUNZUOGHVNUPUQAVPJKVNUMAVOV
        PVQURJKVNUPUQUSUTUO $.

      natcl.1 $e |- ( ph -> X e. B ) $.
      $( A component of a natural transformation is a morphism.  (Contributed
         by Mario Carneiro, 6-Jan-2017.) $)
      natcl $p |- ( ph -> ( A ` X ) e. ( ( F ` X ) J ( K ` X ) ) ) $=
        ( vx cfv wcel cv co cixp natixp wceq fveq2 oveq12d fvixp syl2anc ) ABRC
        RUAZFSZUJISZHUBZUCTLCTLBSLFSZLISZHUBZTARBCDEFGHIJKMNOPUDQRCUMLUPBUJLUEU
        KUNULUOHUJLFUFUJLIUFUGUHUI $.
    $}

    $( A natural transformation is a function on the objects of ` C ` .
       (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    natfn $p |- ( ph -> A Fn B ) $=
      ( vx cv cfv chom co cixp wcel wfn eqid natixp ixpfn syl ) ABNCNOZFPUFHPEQ
      PZRZSTBCUAANBCDEFGUGHIJKLMUGUBUCNCUHBUDUE $.

    nati.h $e |- H = ( Hom ` C ) $.
    nati.o $e |- .x. = ( comp ` D ) $.
    nati.x $e |- ( ph -> X e. B ) $.
    nati.y $e |- ( ph -> Y e. B ) $.
    nati.r $e |- ( ph -> R e. ( X H Y ) ) $.
    $( Naturality property of a natural transformation.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    nati $p |- ( ph ->
        ( ( A ` Y ) ( <. ( F ` X ) , ( F ` Y ) >.
            .x. ( K ` Y ) ) ( ( X G Y ) ` R ) ) =
        ( ( ( X L Y ) ` R ) ( <. ( F ` X ) , ( K ` X ) >.
            .x. ( K ` Y ) ) ( A ` X ) ) ) $=
      ( vy vf vx cv cfv co cop wceq wral chom cixp wcel wa cfunc wbr natrcl syl
      eqid simpld df-br sylibr simprd isnat mpbid adantr ad2antrr simpr oveq12d
      simplr eleqtrrd simpllr fveq2d opeq12d fveq12d oveq123d eqeq12d rspcimdv
      rspcdv mpd ) AUDUGZBUHZUEUGZUFUGZWCIUIZUHZWFHUHZWCHUHZUJZWCKUHZGUIZUIZWEW
      FWCLUIZUHZWFBUHZWIWFKUHZUJZWLGUIZUIZUKZUEWFWCJUIZULZUDCULZUFCULZOBUHZFNOI
      UIZUHZNHUHZOHUHZUJZOKUHZGUIZUIZFNOLUIZUHZNBUHZXJNKUHZUJZXMGUIZUIZUKZABUFC
      WIWREUMUHZUIUNUOZXFABHIUJZKLUJZMUIUOZYEXFUPQAUFUDBCDEGUEHIJYDKLMPRSYDVATA
      YFDEUQUIZUOZHIYIURAYJYGYIUOZAYHYJYKUPQBDEYFYGMPUSUTZVBHIYIVCVDAYKKLYIURAY
      JYKYLVEKLYIVCVDVFVGVEAXEYCUFNCUAAWFNUKZUPZXDYCUDOCAOCUOYMUBVHYNWCOUKZUPZX
      BYCUEFXCYPFNOJUIZXCAFYQUOYMYOUCVIYPWFNWCOJAYMYOVLYNYOVJVKVMYPWEFUKZUPZWNX
      OXAYBYSWDXGWHXIWMXNYSWKXLWLXMGYSWIXJWJXKYSWFNHAYMYOYRVNZVOZYSWCOHYNYOYRVL
      ZVOVPYSWCOKUUBVOZVKYSWCOBUUBVOYSWEFWGXHYSWFNWCOIYTUUBVKYPYRVJZVQVRYSWPXQW
      QXRWTYAYSWSXTWLXMGYSWIXJWRXSUUAYSWFNKYTVOVPUUCVKYSWEFWOXPYSWFNWCOLYTUUBVK
      UUDVQYSWFNBYTVOVRVSWAVTVTWB $.
  $}

  ${
    $d a f g r s x y z C $.  $d a f g r s x y z D $.
    wunnat.1 $e |- ( ph -> U e. WUni ) $.
    wunnat.2 $e |- ( ph -> C e. U ) $.
    wunnat.3 $e |- ( ph -> D e. U ) $.
    $( A weak universe is closed under the natural transformation operation.
       (Contributed by Mario Carneiro, 12-Jan-2017.)  (Proof shortened by AV,
       13-Oct-2024.) $)
    wunnat $p |- ( ph -> ( C Nat D ) e. U ) $=
      ( vr vf vs vg vx co chom cfv cv wral wcel cvv eqid vy va vz cfunc cxp crn
      cuni cbs cmap cpw cnat wunfunc wunxp cnx homid wunstr wunrn wununi baseid
      wunmap wunpw wf c1st c2nd cop cco wceq cixp crab csb fvex wsbc ssrab2 wss
      ovex ovssunirn rgenw ss2ixp ax-mp rnex uniex ixpconst sseqtri sstri sbcth
      elpwi2 sbcel1g mpbid rgen2w natfval fmpo mpbi a1i wunf ) ABCUDMZWOUEZCNOZ
      UFZUGZBUHOZUIMZUJZDBCUKMZEAWOWODEABCDEFGULZXDUMAXADEAWSWTDEAWRDEAWQDEACDN
      UNNOUOEGUPUQURABDUHUNUHOUSEFUPUTVAWPXBXCVBZAHIPZVCOZJKPZVCOZUAPZUBPZOUCPZ
      LPZXJXFVDOMOXMHPZOZXJXNOVEXJJPZOZCVFOZMMXLXMXJXHVDOMOXMXKOXOXMXPOZVEXQXRM
      MVGUCXMXJBNOZMQUAWTQLWTQZUBLWTXOXSWQMZVHZVIZVJZVJZXBRZKWOQIWOQXEYGIKWOWOX
      GSRZYGXFVCVKYHYEXBRZHXGVLYGYIHXGSXISRZYIXHVCVKYJYDXBRZJXIVLYIYKJXISYDXASW
      SWTUIVOYDYCXAYAUBYCVMYCLWTWSVHZXAYBWSVNZLWTQYCYLVNYMLWTWQXOXSVPVQLWTYBWSV
      RVSLWTWSBUHVKWRWQCNVKVTWAWBWCWDWFWEJXIYDXBSWGWHVSWEHXGYEXBSWGWHVSWIIKWOWO
      YFXBXCLUAWTBCXRIKUCXTWQXCJHUBXCTWTTXTTWQTXRTWJWKWLWMWN $.
  $}

  $( A category structure is a structure.  (Contributed by Mario Carneiro,
     3-Jan-2017.) $)
  catstr $p |- { <. ( Base ` ndx ) , U >. ,
                 <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .x. >. }
                Struct <. 1 , ; 1 5 >. $=
    ( cnx cbs cfv chom cco c1 c4 cdc 1nn basendx 4nn0 1nn0 1lt10 declti decnncl
    c5 5nn 4nn homndx 4lt5 declt ccondx strle3 ) DEFDGFDHFIIJKISKBCALMIJILNOPQI
    JOUARUBIJSONTUCUDISOTRUEUF $.

  ${
    $d h t u v B $.  $d t u N $.  $d a b f g h t u v x ph $.  $d t u .xb $.
    $d a b f g h t u v x C $.  $d a b f g h t u v x D $.
    fucval.q $e |- Q = ( C FuncCat D ) $.
    fucval.b $e |- B = ( C Func D ) $.
    fucval.n $e |- N = ( C Nat D ) $.
    fucval.a $e |- A = ( Base ` C ) $.
    fucval.o $e |- .x. = ( comp ` D ) $.
    fucval.c $e |- ( ph -> C e. Cat ) $.
    fucval.d $e |- ( ph -> D e. Cat ) $.
    ${
      fucval.x $e |- ( ph -> .xb = ( v e. ( B X. B ) , h e. B |->
              [_ ( 1st ` v ) / f ]_ [_ ( 2nd ` v ) / g ]_
            ( b e. ( g N h ) , a e. ( f N g ) |->
              ( x e. A |-> ( ( b ` x )
                ( <. ( ( 1st ` f ) ` x ) , ( ( 1st ` g ) ` x ) >. .x.
                     ( ( 1st ` h ) ` x ) ) ( a ` x ) ) ) ) ) ) $.
      $( Value of the functor category.  (Contributed by Mario Carneiro,
         6-Jan-2017.) $)
      fucval $p |- ( ph -> Q = { <. ( Base ` ndx ) , B >. ,
        <. ( Hom ` ndx ) , N >. , <. ( comp ` ndx ) , .xb >. } ) $=
        ( vt vu cfuc co cnx cbs cfv cop chom cco ctp ccat cv cnat cxp c1st c2nd
        cfunc cmpt cmpo csb cvv wceq df-fuc a1i wa simprl simprr oveq12d opeq2d
        eqtr4di sqxpeqd oveqd fveq2d mpoeq123dv csbeq2dv adantr eqtr4d tpeq123d
        mpteq12dv wcel tpex ovmpod eqtrid ) AHFGUGUHUIUJUKZEULZUIUMUKZNULZUIUNU
        KZIULZUOZQAUEUFFGUPUPWIUEUQZUFUQZVBUHZULZWKWPWQURUHZULZWMCMWRWRUSZWRKCU
        QZUTUKZLXCVAUKZPOLUQZMUQZWTUHZKUQZXFWTUHZBWPUJUKZBUQZPUQUKZXLOUQUKZXLXI
        UTUKUKXLXFUTUKUKULZXLXGUTUKUKZWQUNUKZUHZUHZVCZVDZVEZVEZVDZULZUOZWOUGVFU
        GUEUFUPUPYFVDVGABCUFUEKLMOPVHVIAWPFVGZWQGVGZVJZVJZWSWJXAWLYEWNYJWREWIYJ
        WRFGVBUHEYJWPFWQGVBAYGYHVKZAYGYHVLZVMRVOZVNYJWTNWKYJWTFGURUHNYJWPFWQGUR
        YKYLVMSVOZVNYJYDIWMYJYDCMEEUSZEKXDLXEPOXFXGNUHZXIXFNUHZBDXMXNXOXPJUHZUH
        ZVCZVDZVEZVEZVDZIYJCMXBWRYCYOEUUCYJWREYMVPYMYJKXDYBUUBYJLXEYAUUAYJPOXHX
        JXTYPYQYTYJWTNXFXGYNVQYJWTNXIXFYNVQYJBXKXSDYSYJXKFUJUKDYJWPFUJYKVRTVOYJ
        XRYRXMXNYJXQJXOXPYJXQGUNUKJYJWQGUNYLVRUAVOVQVQWDVSVTVTVSAIUUDVGYIUDWAWB
        VNWCUBUCWOVFWEAWJWLWNWFVIWGWH $.
    $}

    fuccofval.x $e |- .xb = ( comp ` Q ) $.
    $( Value of the functor category.  (Contributed by Mario Carneiro,
       6-Jan-2017.) $)
    fuccofval $p |- ( ph -> .xb = ( v e. ( B X. B ) , h e. B |->
            [_ ( 1st ` v ) / f ]_ [_ ( 2nd ` v ) / g ]_
          ( b e. ( g N h ) , a e. ( f N g ) |->
            ( x e. A |-> ( ( b ` x )
              ( <. ( ( 1st ` f ) ` x ) , ( ( 1st ` g ) ` x ) >. .x.
                   ( ( 1st ` h ) ` x ) ) ( a ` x ) ) ) ) ) ) $=
      ( cco cfv cnx cbs cop chom cxp cv c1st c2nd co cmpt cmpo csb eqidd fucval
      ctp fveq2d cvv wcel wceq cfunc ovexi mpoex c1 c5 cdc catstr ccoid snsstp3
      xpex strfv ax-mp 3eqtr4g ) AHUEUFUGUHUFEUIZUGUJUFNUIZUGUEUFCMEEUKZEKCULZU
      MUFLWBUNUFPOLULZMULZNUOKULZWCNUOBDBULZPULUFWFOULUFWFWEUMUFUFWFWCUMUFUFUIW
      FWDUMUFUFJUOUOUPUQURURZUQZUIZVAZUEUFZIWHAHWJUEABCDEFGHWHJKLMNOPQRSTUAUBUC
      AWHUSUTVBUDWHVCVDWHWKVECMWAEWGEEEFGVFRVGZWLVOWLVHWHWJUEVCVIVIVJVKUIWHENVL
      VMVSVTWIVNVPVQVR $.
  $}

  ${
    $d a b f g h v x C $.  $d a b f g h v x D $.
    fucbas.q $e |- Q = ( C FuncCat D ) $.
    $( The objects of the functor category are functors from ` C ` to ` D ` .
       (Contributed by Mario Carneiro, 6-Jan-2017.)  (Revised by Mario
       Carneiro, 12-Jan-2017.) $)
    fucbas $p |- ( C Func D ) = ( Base ` Q ) $=
      ( vx vv vf vg vh ccat wcel co cbs cfv cnx cop cco eqid c0 cfuc va vb wceq
      wa cfunc chom cnat ctp cvv c1 c5 cdc simpl fuccofval fucval catstr baseid
      simpr snsstp1 ovexd strfv3 eqcomd wn base0 funcrcl con3i eq0rdv cxp fnfuc
      cv fndmi ndmov eqtrid fveq2d 3eqtr4a pm2.61i ) AJKZBJKZUDZABUELZCMNZUCVSW
      AVTVSWAVTOMNVTPZOUFNABUGLZPZOQNCQNZPZUHCMUIUJUJUKULPVSEFAMNZVTABCWEBQNZGH
      IWCUAUBDVTRZWCRZWGRZWHRZVQVRUMZVQVRURZVSEFWGVTABCWEWHGHIWCUAUBDWIWJWKWLWM
      WNWERUNUOWEVTWCUPUQWBWDWFUSVSABUEUTWARVAVBVSVCZSSMNVTWAVDWOGVTGVJZVTKVSAB
      WPVEVFVGWOCSMWOCABTLSDABJTJJVHTVIVKVLVMVNVOVP $.

    fuchom.n $e |- N = ( C Nat D ) $.
    $( The morphisms in the functor category are natural transformations.
       (Contributed by Mario Carneiro, 6-Jan-2017.)  (Proof shortened by AV,
       14-Oct-2024.) $)
    fuchom $p |- N = ( Hom ` Q ) $=
      ( vx vv vf ccat wcel chom cfv cnx cop cco eqid c0 cxp cfuc vg vh va vb wa
      wceq cbs cfunc co ctp cvv c1 c5 simpl simpr fuccofval fucval catstr homid
      cdc snsstp2 cnat ovexi a1i strfv3 eqcomd wn str0 wfn natffn funcrcl con3i
      eq0rdv xpeq2d xp0 eqtrdi fneq2d mpbii fn0 sylib fnfuc fndmi eqtrid fveq2d
      cv ndmov 3eqtr4a pm2.61i ) AJKZBJKZUEZDCLMZUFWKWLDWKWLDNUGMABUHUIZOZNLMZD
      OZNPMCPMZOZUJCLUKULULUMUTOWKGHAUGMZWMABCWQBPMZIUAUBDUCUDEWMQZFWSQZWTQZWIW
      JUNZWIWJUOZWKGHWSWMABCWQWTIUAUBDUCUDEXAFXBXCXDXEWQQUPUQWQWMDURUSWNWPWRVAD
      UKKWKDABVBFVCVDWLQVEVFWKVGZRRLMDWLLWOUSVHXFDRVIZDRUFXFDWMWMSZVIXGABDFVJXF
      XHRDXFXHWMRSRXFWMRWMXFIWMIWEZWMKWKABXIVKVLVMVNWMVOVPVQVRDVSVTXFCRLXFCABTU
      IREABJTJJSTWAWBWFWCWDWGWH $.
  $}

  ${
    $d a b f g h v x A $.  $d a b f g h v x ph $.  $d a b x R $.  $d a b x S $.
    $d a b f g h v x C $.  $d a b f g h v x D $.  $d a b f g h v x .x. $.
    $d a b f g h v x F $.  $d a b f g h v x G $.  $d a b f g h v x H $.
    $d a b f g h v N $.  $d x X $.
    fucco.q $e |- Q = ( C FuncCat D ) $.
    fucco.n $e |- N = ( C Nat D ) $.
    fucco.a $e |- A = ( Base ` C ) $.
    fucco.o $e |- .x. = ( comp ` D ) $.
    fucco.x $e |- .xb = ( comp ` Q ) $.
    fucco.f $e |- ( ph -> R e. ( F N G ) ) $.
    fucco.g $e |- ( ph -> S e. ( G N H ) ) $.
    $( Value of the composition of natural transformations.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)
    fucco $p |- ( ph -> ( S ( <. F , G >. .xb H ) R ) = ( x e. A |->
      ( ( S ` x ) ( <. ( ( 1st ` F ) ` x ) , ( ( 1st ` G ) ` x ) >. .x.
        ( ( 1st ` H ) ` x ) ) ( R ` x ) ) ) ) $=
      ( vb va vv vh vf vg co cfv c1st cop cmpt cvv cfunc cxp c2nd cmpo csb eqid
      cv ccat wcel natrcl syl simpld funcrcl simprd fuccofval wceq fvexd simprl
      wa fveq2d op1stg adantr eqtrd op2ndg ad2antrr simpr simprr oveq12d simplr
      fveq1d opeq12d oveqd mpteq2dv mpoeq123dv csbied2 opelxpi mpoex a1i ovmpod
      ovex cbs fvexi mptex ) AUBUCHGLMNUHZKLNUHZBCBUTZUBUTZUIZWSUCUTZUIZWSKUJUI
      ZUIZWSLUJUIZUIZUKZWSMUJUIZUIZJUHZUHZULZBCWSHUIZWSGUIZXKUHZULZKLUKZMIUHUMA
      UDUEXRMDEUNUHZXSUOZXSUFUDUTZUJUIZUGYAUPUIZUBUCUGUTZUEUTZNUHZUFUTZYDNUHZBC
      XAXCWSYGUJUIZUIZWSYDUJUIZUIZUKZWSYEUJUIZUIZJUHZUHZULZUQZURZURUBUCWQWRXMUQ
      ZIUMABUDCXSDEFIJUFUGUENUCUBOXSUSPQRADVAVBZEVAVBZAKXSVBZUUBUUCVLAUUDLXSVBZ
      AGWRVBUUDUUEVLZTGDEKLNPVCVDZVEDEKVFVDZVEAUUBUUCUUHVGSVHAYAXRVIZYEMVIZVLZV
      LZUFYBKYTUUAUMUULYAUJVJUULYBXRUJUIZKUULYAXRUJAUUIUUJVKZVMAUUMKVIZUUKAUUFU
      UOUUGKLXSXSVNVDVOVPUULYGKVIZVLZUGYCLYSUUAUMUUQYAUPVJUUQYCXRUPUIZLUUQYAXRU
      PUULUUIUUPUUNVOVMAUURLVIZUUKUUPAUUFUUSUUGKLXSXSVQVDVRVPUUQYDLVIZVLZUBUCYF
      YHYRWQWRXMUVAYDLYEMNUUQUUTVSZUULUUJUUPUUTAUUIUUJVTVRZWAUVAYGKYDLNUULUUPUU
      TWBZUVBWAUVABCYQXLUVAYPXKXAXCUVAYMXHYOXJJUVAYJXEYLXGUVAWSYIXDUVAYGKUJUVDV
      MWCUVAWSYKXFUVAYDLUJUVBVMWCWDUVAWSYNXIUVAYEMUJUVCVMWCWAWEWFWGWHWHAUUFXRXT
      VBUUGKLXSXSWIVDAUUEMXSVBZAHWQVBUUEUVEVLUAHDELMNPVCVDVGUUAUMVBAUBUCWQWRXML
      MNWMKLNWMWJWKWLAWTHVIZXBGVIZVLVLZBCXLXPUVHXAXNXCXOXKUVHWSWTHAUVFUVGVKWCUV
      HWSXBGAUVFUVGVTWCWAWFUATXQUMVBABCXPCDWNQWOWPWKWL $.

    fuccoval.f $e |- ( ph -> X e. A ) $.
    $( Value of the functor category.  (Contributed by Mario Carneiro,
       6-Jan-2017.) $)
    fuccoval $p |- ( ph -> ( ( S ( <. F , G >. .xb H ) R ) ` X ) =
      ( ( S ` X ) ( <. ( ( 1st ` F ) ` X ) , ( ( 1st ` G ) ` X ) >. .x.
        ( ( 1st ` H ) ` X ) ) ( R ` X ) ) ) $=
      ( vx cv cfv c1st cop co cvv fucco wceq wa fveq2d opeq12d oveq12d oveq123d
      simpr ovexd fvmptd ) AUCNUCUDZGUEZUTFUEZUTJUFUEZUEZUTKUFUEZUEZUGZUTLUFUEZ
      UEZIUHZUHNGUEZNFUEZNVCUEZNVEUEZUGZNVHUEZIUHZUHBGFJKUGLHUHUHUIAUCBCDEFGHIJ
      KLMOPQRSTUAUJAUTNUKZULZVAVKVBVLVJVQVSVGVOVIVPIVSVDVMVFVNVSUTNVCAVRUQZUMVS
      UTNVEVTUMUNVSUTNVHVTUMUOVSUTNGVTUMVSUTNFVTUMUPUBAVKVLVQURUS $.
  $}

  ${
    $d f x y C $.  $d f x y D $.  $d f x y F $.  $d f x y G $.  $d f x y .xb $.
    $d f x y H $.  $d f x y ph $.  $d f x y R $.  $d f x y S $.
    fuccocl.q $e |- Q = ( C FuncCat D ) $.
    fuccocl.n $e |- N = ( C Nat D ) $.
    fuccocl.x $e |- .xb = ( comp ` Q ) $.
    fuccocl.r $e |- ( ph -> R e. ( F N G ) ) $.
    fuccocl.s $e |- ( ph -> S e. ( G N H ) ) $.
    $( The composition of two natural transformations is a natural
       transformation.  Remark 6.14(a) in [Adamek] p. 87.  (Contributed by
       Mario Carneiro, 6-Jan-2017.) $)
    fuccocl $p |- ( ph -> ( S ( <. F , G >. .xb H ) R ) e. ( F N H ) ) $=
      ( co wcel cfv adantr vx vy cop cbs c1st chom cixp c2nd cco wceq wral cmpt
      vf cv eqid fucco ccat cfunc natrcl syl simpld funcrcl simprd wrel relfunc
      wa wbr 1st2ndbr sylancr funcf1 ffvelcdmda nat1st2nd simpr natcl ralrimiva
      catcocl cvv wb mptelixpg ax-mp sylibr eqeltrd w3a simpr1 ffvelcdmd simpr2
      fvex funcf2 simpr3 catass nati oveq2d oveq1d 3eqtr2d fuccoval ralrimivvva
      wf 3eqtrd 3eqtr4d isnat2 mpbir2and ) AFEHIUCJGQQZHJKQRXBUABUDSZUAUNZHUESZ
      SZXDJUESZSZCUFSZQZUGZRUBUNZXBSZUMUNZXDXLHUHSZQZSZXFXLXESZUCZXLXGSZCUISZQZ
      QZXNXDXLJUHSZQZSZXDXBSZXFXHUCXTYAQZQZUJZUMXDXLBUFSZQZUKUBXCUKUAXCUKAXBUAX
      CXDFSZXDESZXFXDIUESZSZUCZXHYAQQZULZXKAUAXCBCDEFGYAHIJKLMXCUOZYAUOZNOPUPAY
      RXJRZUAXCUKZYSXKRZAUUBUAXCAXDXCRZVFZCUDSZCYAYNYMXIXFYPXHUUGUOZXIUOZUUAACU
      QRZUUEABUQRZUUJAHBCURQZRZUUKUUJVFAUUMIUULRZAEHIKQRZUUMUUNVFOEBCHIKMUSUTVA
      ZBCHVBUTVCZTAXCUUGXDXEAXCUUGBCXEXOYTUUHAUULVDZUUMXEXOUULVGZBCVEZUUPHUULVH
      VIZVJZVKAXCUUGXDYOAXCUUGBCYOIUHSZYTUUHAUURUUNYOUVCUULVGZUUTAUUNJUULRZAFIJ
      KQRZUUNUVEVFPFBCIJKMUSUTZVAIUULVHVIZVJZVKAXCUUGXDXGAXCUUGBCXGYDYTUUHAUURU
      VEXGYDUULVGZUUTAUUNUVEUVGVCZJUULVHVIZVJZVKUUFEXCBCXEXOXIYOUVCKXDMAEXEXOUC
      YOUVCUCZKQRZUUEAEBCHIKMOVLZTYTUUIAUUEVMZVNUUFFXCBCYOUVCXIXGYDKXDMAFUVNXGY
      DUCKQRZUUEAFBCIJKMPVLZTYTUUIUVQVNVPVOXCVQRUUDUUCVRBUDWGUAXCYRXJVQVSVTWAWB
      AYJUAUBUMXCXCYLAUUEXLXCRZXNYLRZWCZVFZXLFSZXLESZXRXLYOSZUCXTYAQQZXQYBQZYFY
      RYHQZYCYIUWCUWHUWDUWEXQXSUWFYAQQZXFUWFUCXTYAQZQZYFYMYPXHUCXTYAQQZYNYQXTYA
      QZQZUWIUWCUUGCYAXQUWEXIUWDXTXFXRUWFUUHUUIUUAAUUJUWBUUQTZUWCXCUUGXDXEAXCUU
      GXEWQUWBUVBTZAUUEUVTUWAWDZWEZUWCXCUUGXLXEUWQAUUEUVTUWAWFZWEUWCXCUUGXLYOAX
      CUUGYOWQUWBUVITZUWTWEZUWCYLXFXRXIQXNXPUWCXCBCXEXOYKXIXDXLYTYKUOZUUIAUUSUW
      BUVATUWRUWTWHAUUEUVTUWAWIZWEUWCEXCBCXEXOXIYOUVCKXLMAUVOUWBUVPTZYTUUIUWTVN
      UWCXCUUGXLXGAXCUUGXGWQUWBUVMTZUWTWEZUWCFXCBCYOUVCXIXGYDKXLMAUVRUWBUVSTZYT
      UUIUWTVNZWJUWCUWLUWDXNXDXLUVCQZSZYNYQUWFYAQQZUWKQUWDUXKYPUWFUCXTYAQQZYNUW
      NQUWOUWCUWJUXLUWDUWKUWCEXCBCXNYAXEXOYKYOUVCKXDXLMUXEYTUXCUUAUWRUWTUXDWKWL
      UWCUUGCYAYNUXKXIUWDXTXFYPUWFUUHUUIUUAUWPUWSUWCXCUUGXDYOUXAUWRWEZUXBUWCEXC
      BCXEXOXIYOUVCKXDMUXEYTUUIUWRVNZUWCYLYPUWFXIQXNUXJUWCXCBCYOUVCYKXIXDXLYTUX
      CUUIAUVDUWBUVHTUWRUWTWHUXDWEUXGUXIWJUWCUXMUWMYNUWNUWCFXCBCXNYAYOUVCYKXGYD
      KXDXLMUXHYTUXCUUAUWRUWTUXDWKWMWNUWCUUGCYAYNYMXIYFXTXFYPXHUUHUUIUUAUWPUWSU
      XNUWCXCUUGXDXGUXFUWRWEUXOUWCFXCBCYOUVCXIXGYDKXDMUXHYTUUIUWRVNUXGUWCYLXHXT
      XIQXNYEUWCXCBCXGYDYKXIXDXLYTUXCUUIAUVJUWBUVLTUWRUWTWHUXDWEWJWRUWCXMUWGXQY
      BUWCXCBCDEFGYAHIJKXLLMYTUUANAUUOUWBOTZAUVFUWBPTZUWTWOWMUWCYGYRYFYHUWCXCBC
      DEFGYAHIJKXDLMYTUUANUXPUXQUWRWOWLWSWPAUAUBXBXCBCYAUMHJYKXIKMYTUXCUUIUUAUU
      PUVKWTXA $.
  $}

  ${
    $d f x y .1. $.  $d f x y C $.  $d f x y D $.  $d f x y ph $.
    $d f x y F $.
    fucidcl.q $e |- Q = ( C FuncCat D ) $.
    fucidcl.n $e |- N = ( C Nat D ) $.
    fucidcl.x $e |- .1. = ( Id ` D ) $.
    fucidcl.f $e |- ( ph -> F e. ( C Func D ) ) $.
    $( The identity natural transformation.  (Contributed by Mario Carneiro,
       6-Jan-2017.) $)
    fucidcl $p |- ( ph -> ( .1. o. ( 1st ` F ) ) e. ( F N F ) ) $=
      ( vx vy vf cfv co wcel wceq wral eqid c1st ccom cbs cv chom cixp c2nd cop
      cco cmpt cvv wf wfn ccat cfunc wa funcrcl syl simprd cidfn dffn2 wrel wbr
      sylib relfunc 1st2ndbr sylancr funcf1 fcompt syl2anc ffvelcdmda ralrimiva
      adantr catidcl wb mptelixpg ax-mp sylibr eqeltrd w3a simpr1 syldan simpr2
      fvex funcf2 simpr3 catlid catrid eqtr4d oveq1d oveq2d 3eqtr4d ralrimivvva
      ffvelcdmd fvco3 isnat2 mpbir2and ) AEFUAOZUBZFFGPQWSLBUCOZLUDZWROZXBCUEOZ
      PZUFZQMUDZWSOZNUDZXAXFFUGOZPZOZXBXFWROZUHXLCUIOZPZPZXKXAWSOZXBXBUHXLXMPZP
      ZRZNXAXFBUEOZPZSMWTSLWTSAWSLWTXBEOZUJZXEACUCOZUKEULZWTYDWRULZWSYCRAEYDUMZ
      YEACUNQZYGABUNQZYHAFBCUOPZQZYIYHUPKBCFUQURUSZYDCEYDTZJUTURYDEVAVDAWTYDBCW
      RXIWTTZYMAYJVBYKWRXIYJVCZBCVEKFYJVFVGZVHZLEWRWTYDUKVIVJAYBXDQZLWTSZYCXEQZ
      AYRLWTAXAWTQZUPYDCEXCXBYMXCTZJAYHUUAYLVMAWTYDXAWRYQVKZVNVLWTUKQYTYSVOBUCW
      DLWTYBXDUKVPVQVRVSAXSLMNWTWTYAAUUAXFWTQZXHYAQZVTZUPZXLEOZXKXNPZXKYBXQPZXO
      XRUUGUUIXKUUJUUGYDCXMEXKXCXBXLYMUUBJAYHUUFYLVMZAUUFUUAXBYDQAUUAUUDUUEWAZU
      UCWBZXMTZUUGWTYDXFWRAYFUUFYQVMZAUUAUUDUUEWCZWNZUUGYAXBXLXCPXHXJUUGWTBCWRX
      IXTXCXAXFYNXTTZUUBAYOUUFYPVMUULUUPWEAUUAUUDUUEWFWNZWGUUGYDCXMEXKXCXBXLYMU
      UBJUUKUUMUUNUUQUUSWHWIUUGXGUUHXKXNUUGYFUUDXGUUHRUUOUUPWTYDXFEWRWOVJWJUUGX
      PYBXKXQUUGYFUUAXPYBRUUOUULWTYDXAEWRWOVJWKWLWMALMWSWTBCXMNFFXTXCGIYNUURUUB
      UUNKKWPWQ $.
  $}

  ${
    $d x .1. $.  $d x C $.  $d x D $.  $d x F $.  $d x G $.  $d x ph $.
    $d x R $.
    fuclid.q $e |- Q = ( C FuncCat D ) $.
    fuclid.n $e |- N = ( C Nat D ) $.
    fuclid.x $e |- .xb = ( comp ` Q ) $.
    fuclid.1 $e |- .1. = ( Id ` D ) $.
    fuclid.r $e |- ( ph -> R e. ( F N G ) ) $.
    $( Left identity of natural transformations.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    fuclid $p |- ( ph ->
      ( ( .1. o. ( 1st ` G ) ) ( <. F , G >. .xb G ) R ) = R ) $=
      ( vx cfv cop co wcel cbs cv c1st ccom cco cmpt wa wf wceq c2nd eqid cfunc
      wrel wbr relfunc natrcl simprd 1st2ndbr sylancr funcf1 fvco3 sylan oveq1d
      syl chom ccat simpld adantr ffvelcdmda nat1st2nd simpr natcl catlid eqtrd
      funcrcl mpteq2dva fucidcl fucco wfn natfn dffn5 sylib 3eqtr4d ) APBUAQZPU
      BZGIUCQZUDZQZWEEQZWEHUCQZQZWEWFQZRWLCUEQZSZSZUFPWDWIUFZWGEHIRIFSSEAPWDWOW
      IAWEWDTZUGZWOWLGQZWIWNSWIWRWHWSWIWNAWDCUAQZWFUHWQWHWSUIAWDWTBCWFIUJQZWDUK
      ZWTUKZABCULSZUMZIXDTZWFXAXDUNBCUOZAHXDTZXFAEHIJSTXHXFUGOEBCHIJLUPVDZUQZIX
      DURUSUTZWDWTWEGWFVAVBVCWRWTCWMGWICVEQZWKWLXCXLUKZNACVFTZWQABVFTZXNAXHXOXN
      UGAXHXFXIVGZBCHVOVDUQVHAWDWTWEWJAWDWTBCWJHUJQZXBXCAXEXHWJXQXDUNXGXPHXDURU
      SUTVIWMUKZAWDWTWEWFXKVIWREWDBCWJXQXLWFXAJWELAEWJXQRWFXARJSTWQAEBCHIJLOVJZ
      VHXBXMAWQVKVLVMVNVPAPWDBCDEWGFWMHIIJKLXBXRMOABCDGIJKLNXJVQVRAEWDVSEWPUIAE
      WDBCWJXQWFXAJLXSXBVTPWDEWAWBWC $.

    $( Right identity of natural transformations.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    fucrid $p |- ( ph ->
      ( R ( <. F , F >. .xb G ) ( .1. o. ( 1st ` F ) ) ) = R ) $=
      ( vx cfv cop co wcel cbs cv c1st ccom cco cmpt wa wf wceq c2nd eqid cfunc
      wrel wbr relfunc natrcl simpld 1st2ndbr sylancr funcf1 fvco3 sylan oveq2d
      syl chom ccat simprd adantr ffvelcdmda nat1st2nd simpr natcl catrid eqtrd
      funcrcl mpteq2dva fucidcl fucco wfn natfn dffn5 sylib 3eqtr4d ) APBUAQZPU
      BZEQZWEGHUCQZUDZQZWEWGQZWJRWEIUCQZQZCUEQZSZSZUFPWDWFUFZEWHHHRIFSSEAPWDWOW
      FAWEWDTZUGZWOWFWJGQZWNSWFWRWIWSWFWNAWDCUAQZWGUHWQWIWSUIAWDWTBCWGHUJQZWDUK
      ZWTUKZABCULSZUMZHXDTZWGXAXDUNBCUOZAXFIXDTZAEHIJSTXFXHUGOEBCHIJLUPVDZUQZHX
      DURUSUTZWDWTWEGWGVAVBVCWRWTCWMGWFCVEQZWJWLXCXLUKZNACVFTZWQABVFTZXNAXFXOXN
      UGXJBCHVOVDVGVHAWDWTWEWGXKVIWMUKZAWDWTWEWKAWDWTBCWKIUJQZXBXCAXEXHWKXQXDUN
      XGAXFXHXIVGIXDURUSUTVIWREWDBCWGXAXLWKXQJWELAEWGXARWKXQRJSTWQAEBCHIJLOVJZV
      HXBXMAWQVKVLVMVNVPAPWDBCDWHEFWMHHIJKLXBXPMABCDGHJKLNXJVQOVRAEWDVSEWPUIAEW
      DBCWGXAWKXQJLXRXBVTPWDEWAWBWC $.
  $}

  ${
    $d x C $.  $d x D $.  $d x F $.  $d x G $.  $d x H $.  $d x K $.  $d x R $.
    $d x ph $.  $d x S $.  $d x T $.  $d x .xb $.
    fucass.q $e |- Q = ( C FuncCat D ) $.
    fucass.n $e |- N = ( C Nat D ) $.
    fucass.x $e |- .xb = ( comp ` Q ) $.
    fucass.r $e |- ( ph -> R e. ( F N G ) ) $.
    fucass.s $e |- ( ph -> S e. ( G N H ) ) $.
    fucass.t $e |- ( ph -> T e. ( H N K ) ) $.
    $( Associativity of natural transformation composition.  Remark 6.14(b) in
       [Adamek] p. 87.  (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    fucass $p |- ( ph ->
      ( ( T ( <. G , H >. .xb K ) S ) ( <. F , G >. .xb K ) R ) =
      ( T ( <. F , H >. .xb K ) ( S ( <. F , G >. .xb H ) R ) ) ) $=
      ( co vx cbs cfv cv cop c1st cco cmpt wcel chom eqid ccat cfunc natrcl syl
      wa simpld funcrcl simprd adantr c2nd wrel relfunc 1st2ndbr sylancr funcf1
      ffvelcdmda nat1st2nd simpr natcl catass fuccoval oveq1d 3eqtr4d mpteq2dva
      wbr oveq2d fuccocl fucco ) AUABUBUCZUAUDZHFJKUELGTTZUCZWAEUCZWAIUFUCZUCZW
      AJUFUCZUCZUEZWALUFUCZUCZCUGUCZTZTZUHUAVTWAHUCZWAFEIJUEZKGTTZUCZWFWAKUFUCZ
      UCZUEWKWLTZTZUHWBEWPLGTTHWQIKUELGTTAUAVTWNXBAWAVTUIZUPZWOWAFUCZWHWTUEWKWL
      TTZWDWMTWOXEWDWIWTWLTTZXATWNXBXDCUBUCZCWLWDXECUJUCZWOWKWFWHWTXHUKZXIUKZWL
      UKZACULUIZXCABULUIZXMAIBCUMTZUIZXNXMUPAXPJXOUIZAEIJMTUIZXPXQUPQEBCIJMOUNU
      OZUQZBCIURUOUSUTAVTXHWAWEAVTXHBCWEIVAUCZVTUKZXJAXOVBZXPWEYAXOVPBCVCZXTIXO
      VDVEVFVGAVTXHWAWGAVTXHBCWGJVAUCZYBXJAYCXQWGYEXOVPYDAXPXQXSUSJXOVDVEVFVGAV
      TXHWAWSAVTXHBCWSKVAUCZYBXJAYCKXOUIZWSYFXOVPYDAYGLXOUIZAHKLMTUIZYGYHUPSHBC
      KLMOUNUOZUQKXOVDVEVFVGXDEVTBCWEYAXIWGYEMWAOAEWEYAUEWGYEUEZMTUIXCAEBCIJMOQ
      VHUTYBXKAXCVIZVJXDFVTBCWGYEXIWSYFMWAOAFYKWSYFUEZMTUIXCAFBCJKMORVHUTYBXKYL
      VJAVTXHWAWJAVTXHBCWJLVAUCZYBXJAYCYHWJYNXOVPYDAYGYHYJUSLXOVDVEVFVGXDHVTBCW
      SYFXIWJYNMWAOAHYMWJYNUEMTUIXCAHBCKLMOSVHUTYBXKYLVJVKXDWCXFWDWMXDVTBCDFHGW
      LJKLMWANOYBXLPAFJKMTUIXCRUTZAYIXCSUTYLVLVMXDWRXGWOXAXDVTBCDEFGWLIJKMWANOY
      BXLPAXRXCQUTYOYLVLVQVNVOAUAVTBCDEWBGWLIJLMNOYBXLPQABCDFHGJKLMNOPRSVRVSAUA
      VTBCDWQHGWLIKLMNOYBXLPABCDEFGIJKMNOPQRVRSVSVN $.
  $}

  ${
    $d e g h r s t .1. $.  $d e f g h r s t C $.  $d e f g h r s t ph $.
    $d e f g h r s t D $.  $d e f g h r s t Q $.
    fuccat.q $e |- Q = ( C FuncCat D ) $.
    fuccat.r $e |- ( ph -> C e. Cat ) $.
    fuccat.s $e |- ( ph -> D e. Cat ) $.
    ${
      fuccatid.1 $e |- .1. = ( Id ` D ) $.
      $( The functor category is a category.  (Contributed by Mario Carneiro,
         6-Jan-2017.) $)
      fuccatid $p |- ( ph -> ( Q e. Cat /\ ( Id ` Q ) =
          ( f e. ( C Func D ) |-> ( .1. o. ( 1st ` f ) ) ) ) ) $=
        ( ve vg vh vr cv co wcel wa cfv a1i vs cfunc cnat w3a cco c1st ccom cvv
        vt cbs wceq fucbas chom eqid fuchom eqidd cfuc ovexi biid simpr fucidcl
        simpr31 fuclid simpr32 fucrid fuccocl simpr33 fucass iscatd2 ) AKOZBCUB
        PZQFOZVKQZRZLOZVKQMOZVKQRZNOZVJVLBCUCPZPQZUAOZVLVOVSPQZUIOZVOVPVSPQZUDU
        DZKFLMVKDDUESZEVLUFSUGNUAUIVSUHVKDUJSUKABCDGULTVSDUMSUKABCDVSGVSUNZUOTA
        WFUPDUHQADBCUQGURTWEUSAVMRBCDEVLVSGWGJAVMUTVAAWERZBCDVRWFEVJVLVSGWGWFUN
        ZJVTWBWDVNVQAVBZVCWHBCDWAWFEVLVOVSGWGWIJVTWBWDVNVQAVDZVEWHBCDVRWAWFVJVL
        VOVSGWGWIWJWKVFWHBCDVRWAWFWCVJVLVOVPVSGWGWIWJWKVTWBWDVNVQAVGVHVI $.
    $}

    $( The functor category is a category.  Remark 6.16 in [Adamek] p. 88.
       (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    fuccat $p |- ( ph -> Q e. Cat ) $=
      ( vf ccat wcel ccid cfv cfunc co cv c1st ccom cmpt wceq eqid fuccatid
      simpld ) ADIJDKLHBCMNCKLZHOPLQRSABCDUCHEFGUCTUAUB $.
  $}

  ${
    $d f .1. $.  $d f C $.  $d f D $.  $d f F $.  $d f ph $.  $d f Q $.
    fucid.q $e |- Q = ( C FuncCat D ) $.
    fucid.i $e |- I = ( Id ` Q ) $.
    fucid.1 $e |- .1. = ( Id ` D ) $.
    fucid.f $e |- ( ph -> F e. ( C Func D ) ) $.
    $( The identity morphism in the functor category.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    fucid $p |- ( ph -> ( I ` F ) = ( .1. o. ( 1st ` F ) ) ) $=
      ( vf c1st cfv ccom cvv ccid ccat wcel wceq cv cfunc co cmpt wa syl simpld
      funcrcl simprd fuccatid eqtrid simpr fveq2d coeq2d fvexi fvex coex fvmptd
      a1i ) ALFELUAZMNZOZEFMNZOZBCUBUCZGPAGDQNZLVEVBUDZIADRSVFVGTABCDELHABRSZCR
      SZAFVESVHVIUEKBCFUHUFZUGAVHVIVJUIJUJUIUKAUTFTZUEZVAVCEVLUTFMAVKULUMUNKVDP
      SAEVCECQJUOFMUPUQUSUR $.
  $}

  ${
    $d x y A $.  $d f x y z B $.  $d f x y z C $.  $d f x y z D $.  $d x y I $.
    $d f x y z F $.  $d f x y z G $.  $d x y J $.  $d x y N $.  $d f x y z V $.
    $d f x y z ph $.  $d x y Q $.  $d x y U $.  $d f y z X $.
    fuciso.q $e |- Q = ( C FuncCat D ) $.
    fuciso.b $e |- B = ( Base ` C ) $.
    fuciso.n $e |- N = ( C Nat D ) $.
    fuciso.f $e |- ( ph -> F e. ( C Func D ) ) $.
    fuciso.g $e |- ( ph -> G e. ( C Func D ) ) $.
    ${
      fucsect.s $e |- S = ( Sect ` Q ) $.
      fucsect.t $e |- T = ( Sect ` D ) $.
      $( Two natural transformations are in a section iff all the components
         are in a section relation.  (Contributed by Mario Carneiro,
         28-Jan-2017.) $)
      fucsect $p |- ( ph -> ( U ( F S G ) V <->
        ( U e. ( F N G ) /\ V e. ( G N F ) /\ A. x e. B
     ( U ` x ) ( ( ( 1st ` F ) ` x ) T ( ( 1st ` G ) ` x ) ) ( V ` x ) ) ) ) $=
        ( co wbr wcel cop cco cfv ccid wceq w3a cv c1st wral fucbas fuchom eqid
        cfunc ccat wa funcrcl syl simpld simprd fuccat issect cmpt cvv wb rgenw
        ovex mpteqb mp1i simprl simprr fucco ccom adantr fucid cbs wf wfn cidfn
        dffn2 sylib c2nd relfunc 1st2ndbr sylancr funcf1 fcompt syl2anc eqeq12d
        wrel eqtrd ffvelcdmda nat1st2nd simpr issect2 ralbidva 3bitr4d pm5.32da
        chom natcl df-3an 3bitr4g bitrd ) AIMJKGUAUBIJKLUAUCZMKJLUAUCZMIJKUDJFU
        EUFZUAUAZJFUGUFZUFZUHZUIZXFXGBUJZIUFZXNMUFZXNJUKUFZUFZXNKUKUFZUFZHUAUBZ
        BCULZUIZADEUPUAZFGXHXJIMLJKDEFNUMDEFLNPUNXHUOZXJUOZSADEFNADUQUCZEUQUCZA
        JYDUCZYGYHURQDEJUSUTZVAAYGYHYJVBZVCQRVDAXFXGURZXLURYLYBURXMYCAYLXLYBAYL
        URZBCXPXOXRXTUDXREUEUFZUAZUAZVEZBCXREUGUFZUFZVEZUHZYPYSUHZBCULZXLYBYPVF
        UCZBCULUUAUUCVGYMUUDBCXPXOYOVIVHBCYPYSVFVJVKYMXIYQXKYTYMBCDEFIMXHYNJKJL
        NPOYNUOZYEAXFXGVLZAXFXGVMZVNYMXKYRXQVOZYTYMDEFYRJXJNYFYRUOZAYIYLQVPVQYM
        EVRUFZVFYRVSZCUUJXQVSZUUHYTUHYMYRUUJVTZUUKYMYHUUMAYHYLYKVPZUUJEYRUUJUOZ
        UUIWAUTUUJYRWBWCAUULYLACUUJDEXQJWDUFZOUUOAYDWLZYIXQUUPYDUBDEWEZQJYDWFWG
        WHVPZBYRXQCUUJVFWIWJWMWKYMYAUUBBCYMXNCUCZURZUUJEHYNYRXOXPEXAUFZXRXTUUOU
        VBUOZUUEUUITYMYHUUTUUNVPYMCUUJXNXQUUSWNYMCUUJXNXSACUUJXSVSYLACUUJDEXSKW
        DUFZOUUOAUUQKYDUCXSUVDYDUBUURRKYDWFWGWHVPWNUVAICDEXQUUPUVBXSUVDLXNPUVAI
        DEJKLPYMXFUUTUUFVPWOOUVCYMUUTWPZXBUVAMCDEXSUVDUVBXQUUPLXNPUVAMDEKJLPYMX
        GUUTUUGVPWOOUVCUVEXBWQWRWSWTXFXGXLXCXFXGYBXCXDXE $.
    $}

    ${
      fucinv.i $e |- I = ( Inv ` Q ) $.
      fucinv.j $e |- J = ( Inv ` D ) $.
      $( Two natural transformations are inverses of each other iff all the
         components are inverse.  (Contributed by Mario Carneiro,
         28-Jan-2017.) $)
      fucinv $p |- ( ph -> ( U ( F I G ) V <->
        ( U e. ( F N G ) /\ V e. ( G N F ) /\ A. x e. B
     ( U ` x ) ( ( ( 1st ` F ) ` x ) J ( ( 1st ` G ) ` x ) ) ( V ` x ) ) ) ) $=
        ( csect cfv co wbr wa wcel cv c1st wral w3a eqid fucsect anbi12d fucbas
        cfunc ccat funcrcl syl simpld simprd fuccat isinv cbs c2nd wrel relfunc
        adantr 1st2ndbr sylancr funcf1 ffvelcdmda ralbidva r19.26 bitrdi anbi2d
        df-3an 3ancoma bitri anbi12i anandi bitr4i 3bitr4g 3bitr4d ) AGMHIFUAUB
        ZUCUDZMGIHWDUCUDZUEGHILUCUFZMIHLUCUFZBUGZGUBZWIMUBZWIHUHUBZUBZWIIUHUBZU
        BZEUAUBZUCUDZBCUIZUJZWHWGWKWJWOWMWPUCUDZBCUIZUJZUEZGMHIJUCUDWGWHWJWKWMW
        OKUCUDZBCUIZUJZAWEWSWFXBABCDEFWDWPGHILMNOPQRWDUKZWPUKZULABCDEFWDWPMIHLG
        NOPRQXGXHULUMADEUOUCZFWDGMJHIDEFNUNSADEFNADUPUFZEUPUFZAHXIUFZXJXKUEQDEH
        UQURZUSAXJXKXMUTZVAQRXGVBAWGWHUEZXEUEXOWRXAUEZUEZXFXCAXEXPXOAXEWQWTUEZB
        CUIXPAXDXRBCAWICUFZUEEVCUBZEWPWJWKKWMWOXTUKZTAXKXSXNVGACXTWIWLACXTDEWLH
        VDUBZOYAAXIVEZXLWLYBXIUDDEVFZQHXIVHVIVJVKACXTWIWNACXTDEWNIVDUBZOYAAYCIX
        IUFWNYEXIUDYDRIXIVHVIVJVKXHVBVLWQWTBCVMVNVOWGWHXEVPXCXOWRUEZXOXAUEZUEXQ
        WSYFXBYGWGWHWRVPXBWGWHXAUJYGWHWGXAVQWGWHXAVPVRVSXOWRXAVTWAWBWC $.

      invfuc.u $e |- ( ph -> U e. ( F N G ) ) $.
      invfuc.v $e |- ( ( ph /\ x e. B ) ->
        ( U ` x ) ( ( ( 1st ` F ) ` x ) J ( ( 1st ` G ) ` x ) ) X ) $.
      $( If ` V ( x ) ` is an inverse to ` U ( x ) ` for each ` x ` , and ` U `
         is a natural transformation, then ` V ` is also a natural
         transformation, and they are inverse in the functor category.
         (Contributed by Mario Carneiro, 28-Jan-2017.) $)
      invfuc $p |- ( ph -> U ( F I G ) ( x e. B |-> X ) ) $=
        ( vy vz vf cmpt co wbr wcel cv cfv c1st wral chom cixp c2nd cop wceq wa
        cco cxp cbs eqid ccat cfunc funcrcl simprd adantr wrel relfunc 1st2ndbr
        syl sylancr funcf1 ffvelcdmda invss ssbrd mpd brxp simprbi ralrimiva wb
        cvv fvexi mptelixpg ax-mp sylibr weq fveq2 oveq12d cbvixpv eleqtrdi w3a
        ccid csect simpr2 simpr fvmpt2 syl2anc breqtrrd nfcv nffvmpt1 nfbr rspc
        breq123d sylc ffvelcdmd isinv simpld issect simp3d oveq1d simpr1 funcf2
        wf mpbid simpr3 catlid eqtr2d nat1st2nd natcl simp2d catass nati oveq2d
        3eqtrd simp1d catcocl catrid 3eqtrrd ralrimivvva isnat2 mpbir2and sylib
        nfv cbvralw fucinv mpbir3and ) AGBCMUFZHIJUGUHGHILUGUIZYSIHLUGUIZUCUJZG
        UKZUUBYSUKZUUBHULUKZUKZUUBIULUKZUKZKUGZUHZUCCUMZUAAUUAYSUCCUUHUUFEUNUKZ
        UGZUOZUIUDUJZYSUKZUEUJZUUBUUOIUPUKZUGZUKZUUHUUOUUGUKZUQUUOUUEUKZEUTUKZU
        GZUGZUUQUUBUUOHUPUKZUGZUKZUUDUUHUUFUQZUVBUVCUGZUGZURZUEUUBUUODUNUKZUGZU
        MUDCUMUCCUMAYSBCBUJZUUGUKZUVOUUEUKZUULUGZUOZUUNAMUVRUIZBCUMZYSUVSUIZAUV
        TBCAUVOCUIZUSZUVOGUKZMUVQUVPUULUGZUVRVAZUHZUVTUWDUWEMUVQUVPKUGZUHUWHUBU
        WDUWIUWGUWEMUWDEVBUKZEUULKUVQUVPUWJVCZTAEVDUIZUWCADVDUIZUWLAHDEVEUGZUIZ
        UWMUWLUSQDEHVFVLVGZVHACUWJUVOUUEACUWJDEUUEUVFOUWKAUWNVIZUWOUUEUVFUWNUHZ
        DEVJZQHUWNVKVMZVNZVOACUWJUVOUUGACUWJDEUUGUUROUWKAUWQIUWNUIUUGUURUWNUHZU
        WSRIUWNVKVMZVNZVOUULVCZVPVQVRUWHUWEUWFUIUVTUWEMUWFUVRVSVTVLZWACWCUIUWBU
        WAWBCDVBOWDBCMUVRWCWEWFWGBUCCUVRUUMBUCWHZUVPUUHUVQUUFUULUVOUUBUUGWIZUVO
        UUBUUEWIZWJWKWLAUVLUCUDUECCUVNAUUBCUIZUUOCUIZUUQUVNUIZWMZUSZUVKUUPUUTUU
        CUUFUUHUQUVAUVCUGUGZUUFUVAUQUVBUVCUGZUGZUUDUVJUGUUPUXOUUDUVIUVAUVCUGUGZ
        UVDUGUVEUXNUVHUXQUUDUVJUXNUVHUUPUUOGUKZUVBUVAUQUVBUVCUGUGZUVHUUFUVBUQZU
        VBUVCUGZUGZUUPUXSUVHUYAUVAUVCUGUGZUXPUGUXQUXNUYCUVBEWNUKZUKZUVHUYBUGUVH
        UXNUXTUYFUVHUYBUXNUXSUVBUVAUULUGUIZUUPUVAUVBUULUGUIZUXTUYFURZUXNUXSUUPU
        VBUVAEWOUKZUGUHZUYGUYHUYIWMUXNUYKUUPUXSUVAUVBUYJUGUHZUXNUXSUUPUVBUVAKUG
        ZUHZUYKUYLUSUXNUXKUWEUVOYSUKZUWIUHZBCUMZUYNAUXJUXKUXLWPZAUYQUXMAUYPBCUW
        DUWEMUYOUWIUBUWDUWCUVTUYOMURAUWCWQUXFBCMUVRYSYSVCWRWSWTWAZVHZUYPUYNBUUO
        CBUXSUUPUYMBUXSXABUYMXABCMUUOXBXCBUDWHZUWEUXSUYOUUPUWIUYMUVOUUOGWIVUAUV
        QUVBUVPUVAKUVOUUOUUEWIUVOUUOUUGWIWJUVOUUOYSWIXEXDXFUXNUWJEUYJUXSUUPKUVB
        UVAUWKTAUWLUXMUWPVHZUXNCUWJUUOUUEACUWJUUEXOUXMUXAVHZUYRXGZUXNCUWJUUOUUG
        ACUWJUUGXOUXMUXDVHZUYRXGZUYJVCZXHXPXIUXNUWJEUYJUVCUYEUXSUUPUULUVBUVAUWK
        UXEUVCVCZUYEVCZVUGVUBVUDVUFXJXPZXKXLUXNUWJEUVCUYEUVHUULUUFUVBUWKUXEVUIV
        UBUXNCUWJUUBUUEVUCAUXJUXKUXLXMZXGZVUHVUDUXNUVNUUFUVBUULUGUUQUVGUXNCDEUU
        EUVFUVMUULUUBUUOOUVMVCZUXEAUWRUXMUWTVHVUKUYRXNAUXJUXKUXLXQZXGZXRXSUXNUW
        JEUVCUVHUXSUULUUPUVBUUFUVBUVAUWKUXEVUHVUBVULVUDVUFVUOUXNGCDEUUEUVFUULUU
        GUURLUUOPUXNGDEHILPAYTUXMUAVHXTZOUXEUYRYAVUDUXNUYGUYHUYIVUJYBZYCUXNUYDU
        XOUUPUXPUXNGCDEUUQUVCUUEUVFUVMUUGUURLUUBUUOPVUPOVUMVUHVUKUYRVUNYDYEYFXL
        UXNUWJEUVCUUDUXOUULUUPUVBUUHUUFUVAUWKUXEVUHVUBUXNCUWJUUBUUGVUEVUKXGZVUL
        VUFUXNUUDUUMUIZUUCUUFUUHUULUGUIZUUCUUDUVIUUHUVCUGUGZUUHUYEUKZURZUXNUUDU
        UCUUHUUFUYJUGUHZVUSVUTVVCWMUXNUUCUUDUUFUUHUYJUGUHZVVDUXNUUJVVEVVDUSUXNU
        XJUYQUUJVUKUYTUYPUUJBUUBCBUUCUUDUUIBUUCXABUUIXABCMUUBXBXCZUXGUWEUUCUYOU
        UDUWIUUIUVOUUBGWIUXGUVQUUFUVPUUHKUXIUXHWJUVOUUBYSWIXEZXDXFUXNUWJEUYJUUC
        UUDKUUFUUHUWKTVUBVULVURVUGXHXPVGUXNUWJEUYJUVCUYEUUDUUCUULUUHUUFUWKUXEVU
        HVUIVUGVUBVURVULXJXPZYGZUXNUWJEUVCUUCUUTUULUUFUUHUVAUWKUXEVUHVUBVULVURV
        UFUXNVUSVUTVVCVVHYBUXNUVNUUHUVAUULUGUUQUUSUXNCDEUUGUURUVMUULUUBUUOOVUMU
        XEAUXBUXMUXCVHVUKUYRXNVUNXGZYHVUDVUQYCUXNUXRUUTUUPUVDUXNUXRUUTVVAUUHUUH
        UQUVAUVCUGZUGUUTVVBVVKUGUUTUXNUWJEUVCUUDUUCUULUUTUVAUUHUUFUUHUWKUXEVUHV
        UBVURVULVURVVIUXNGCDEUUEUVFUULUUGUURLUUBPVUPOUXEVUKYAVUFVVJYCUXNVVAVVBU
        UTVVKUXNVUSVUTVVCVVHXKYEUXNUWJEUVCUYEUUTUULUUHUVAUWKUXEVUIVUBVURVUHVUFV
        VJYIYFYEYJYKAUCUDYSCDEUVCUEIHUVMUULLPOVUMUXEVUHRQYLYMAUYQUUKUYSUYPUUJBU
        CCUYPUCYOVVFVVGYPYNAUCCDEFGHIJKLYSNOPQRSTYQYR $.
    $}

    ${
      fuciso.i $e |- I = ( Iso ` Q ) $.
      fuciso.j $e |- J = ( Iso ` D ) $.
      $( A natural transformation is an isomorphism of functors iff all its
         components are isomorphisms.  (Contributed by Mario Carneiro,
         28-Jan-2017.) $)
      fuciso $p |- ( ph -> ( A e. ( F I G ) <-> ( A e. ( F N G ) /\
  A. x e. B ( A ` x ) e. ( ( ( 1st ` F ) ` x ) J ( ( 1st ` G ) ` x ) ) ) ) ) $=
        ( cfv vy co wcel cv c1st wral wa cfunc fucbas fuchom funcrcl syl simpld
        ccat simprd fuccat isohom sselda cbs cinv eqid ad2antrr wf c2nd relfunc
        wrel wbr 1st2ndbr sylancr funcf1 adantr ffvelcdmda w3a isoval eleq2d wb
        cdm invfun funfvbrb bitrd biimpa fucinv mpbid simp3d r19.21bi ralrimiva
        wfun inviso1 jca cmpt simprl simprr fveq2 oveq12d eleq12d rspccva sylan
        weq invisoinvr invfuc impbida ) ACHIJUBZUCZCHILUBZUCZBUDZCTZXFHUETZTZXF
        IUETZTZKUBZUCZBDUFZUGZAXCUGZXEXNAXBXDCAEFUHUBZGLJHIEFGMUIZEFGLMOUJRAEFG
        MAEUNUCZFUNUCZAHXQUCZXSXTUGPEFHUKULZUMAXSXTYBUOZUPZPQUQURXPXMBDXPXFDUCZ
        UGFUSTZFXGXFCHIGUTTZUBZTZTZKFUTTZXIXKYFVAZYKVAZAXTXCYEYCVBXPDYFXFXHADYF
        XHVCZXCADYFEFXHHVDTZNYLAXQVFZYAXHYOXQVGEFVEZPHXQVHVIVJZVKVLXPDYFXFXJADY
        FXJVCZXCADYFEFXJIVDTZNYLAYPIXQUCZXJYTXQVGYQQIXQVHVIVJZVKVLSXPXGYJXIXKYK
        UBVGZBDXPXEYIIHLUBUCZUUCBDUFZXPCYIYHVGZXEUUDUUEVMZAXCUUFAXCCYHVQZUCZUUF
        AXBUUHCAXQGJYGHIXRYGVAZYDPQRVNVOAYHWGUUIUUFVPAXQGYGHIXRUUJYDPQVRCYHVSUL
        VTWAAUUFUUGVPXCABDEFGCHIYGYKLYIMNOPQUUJYMWBVKWCWDWEWHWFWIAXOUGZXQGCUADU
        AUDZCTZUULXHTZUULXJTZYKUBTZWJJYGHIXRUUJAGUNUCXOYDVKAYAXOPVKZAUUAXOQVKZR
        UUKUADEFGCHIYGYKLUUPMNOUUQUURUUJYMAXEXNWKUUKUULDUCZUGYFFUUMKYKUUNUUOYLS
        YMAXTXOUUSYCVBUUKDYFUULXHAYNXOYRVKVLUUKDYFUULXJAYSXOUUBVKVLUUKXNUUSUUMU
        UNUUOKUBZUCZAXEXNWLXMUVABUULDBUAWRZXGUUMXLUUTXFUULCWMUVBXIUUNXKUUOKXFUU
        LXHWMXFUULXJWMWNWOWPWQWSWTWHXA $.
    $}
  $}

  ${
    $d a b f g h r s v x y z A $.  $d a b f g h r s v x y z C $.
    $d a b f g h r s v x y B $.  $d a b f g h r s v x y ph $.
    $d a b f g h r s v x y D $.
    fucpropd.1 $e |- ( ph -> ( Homf ` A ) = ( Homf ` B ) ) $.
    fucpropd.2 $e |- ( ph -> ( comf ` A ) = ( comf ` B ) ) $.
    fucpropd.3 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    fucpropd.4 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    fucpropd.a $e |- ( ph -> A e. Cat ) $.
    fucpropd.b $e |- ( ph -> B e. Cat ) $.
    fucpropd.c $e |- ( ph -> C e. Cat ) $.
    fucpropd.d $e |- ( ph -> D e. Cat ) $.
    $( If two categories have the same set of objects, morphisms, and
       compositions, then they have the same natural transformations.
       (Contributed by Mario Carneiro, 26-Jan-2017.) $)
    natpropd $p |- ( ph -> ( A Nat C ) = ( B Nat D ) ) $=
      ( vr vx co cfv wceq wcel eqid vf vg vs vy va vh vz cfunc cv c1st c2nd cop
      cco chom wral cbs cixp crab csb cmpo cnat funcpropd adantr wa cvv nfcsb1v
      ccat nfv wnfc a1i fvexd chomf ad4antr simplr wbr relfunc simpllr 1st2ndbr
      simpld sylancr eqbrtrd funcf1 ffvelcdmda simpr simprd homfeqval ixpeq2dva
      homfeqbas ad3antrrr ixpeq1d eqtrd wb fveq2 oveq12d cbvixpv eleq2i ad6antr
      wrel ad7antr ccomf ad5ant13 wf ad2antrr fvixp ad5ant24 comfeqval ad5ant23
      eqeq12d raleqbidva sylan2b rabeqbidva csbeq1a csbiedf mpoeq123dva natfval
      funcf2 adantl 3eqtr4g ) AUAUBBDUHPZXSNUAUIZUJQZUCUBUIZUJQZUDUIZUEUIZQZUFU
      IZOUIZYDXTUKQZPZQZYHNUIZQZYDYLQZULZYDUCUIZQZDUMQZPPZYGYHYDYBUKQZPZQZYHYEQ
      ZYMYHYPQZULZYQYRPPZRZUFYHYDBUNQZPZUOZUDBUPQZUOZOUUKUOZUEOUUKYMUUDDUNQZPZU
      QZURZUSZUSZUTUAUBCEUHPZUUTNYAUCYCYFYKYOYQEUMQZPPZUUBUUCUUEYQUVAPPZRZUFYHY
      DCUNQZPZUOZUDCUPQZUOZOUVHUOZUEOUVHYMUUDEUNQZPZUQZURZUSZUSZUTBDVAPZCEVAPZA
      UAUBXSXSUUSUUTUUTUVPABCDEVGFGHIJKLMVBZAXSUUTRXTXSSZUVSVCAUVTYBXSSZVDZVDZN
      YAUURUVPVEUWCNVHNUVPVIUWCNYAUVOVFVJUWCXTUJVKUWCYLYARZVDZUURUVOUVPUWEUCYCU
      UQUVOVEUWEUCVHUCUVOVIUWEUCYCUVNVFVJUWEYBUJVKUWEYPYCRZVDZUUQUVNUVOUWGUUMUV
      JUEUUPUVMUWGUUPOUUKUVLUQUVMUWGOUUKUUOUVLUWGYHUUKSZVDDUPQZDEUUNUVKYMUUDUWI
      TZUUNTZUVKTZADVLQEVLQRZUWBUWDUWFUWHHVMUWGUUKUWIYHYLUWGUUKUWIBDYLYIUUKTZUW
      JUWGYLYAYIXSUWCUWDUWFVNUWGXSWRZUVTYAYIXSVOBDVPZUWGUVTUWAAUWBUWDUWFVQZVSXT
      XSVRVTWAZWBZWCZUWGUUKUWIYHYPUWGUUKUWIBDYPYTUWNUWJUWGYPYCYTXSUWEUWFWDUWGUW
      OUWAYCYTXSVOUWPUWGUVTUWAUWQWEYBXSVRVTWAZWBZWCZWFWGUWGOUUKUVHUVLAUUKUVHRZU
      WBUWDUWFABCFWHWIZWJWKYEUUPSUWGYEUGUUKUGUIZYLQZUXFYPQZUUNPZUQZSZUUMUVJWLUU
      PUXJYEOUGUUKUUOUXIYHUXFRYMUXGUUDUXHUUNYHUXFYLWMYHUXFYPWMWNWOWPUWGUXKVDZUU
      LUVIOUUKUVHUWGUXDUXKUXEVCZUXLUWHVDZUUJUVGUDUUKUVHUXLUXDUWHUXMVCUXNYDUUKSZ
      VDZUUGUVDUFUUIUVFUXPUUKBCUUHUVEYHYDUWNUUHTZUVETZABVLQCVLQRUWBUWDUWFUXKUWH
      UXOFWQUXLUWHUXOVNZUXNUXOWDZWFUXPYGUUISZVDZYSUVBUUFUVCUYBUWIDEUVAYRYKYFUUN
      YMYNYQUWJUWKYRTZUVATZAUWMUWBUWDUWFUXKUWHUXOUYAHWSZADWTQEWTQRUWBUWDUWFUXKU
      WHUXOUYAIWSZUWGUWHYMUWISUXKUXOUYAUWTXAZUXPYNUWISUYAUXNUUKUWIYDYLUWGUUKUWI
      YLXBUXKUWHUWSXCWCVCUXPYQUWISUYAUXNUUKUWIYDYPUWGUUKUWIYPXBUXKUWHUXBXCWCVCZ
      UXPUUIYMYNUUNPYGYJUXPUUKBDYLYIUUHUUNYHYDUWNUXQUWKUWGYLYIXSVOUXKUWHUXOUWRW
      IUXSUXTXPWCUXKUXOYFYNYQUUNPZSUWGUWHUYAUGUUKUXIYDUYIYEUXFYDRUXGYNUXHYQUUNU
      XFYDYLWMUXFYDYPWMWNXDXEXFUYBUWIDEUVAYRUUCUUBUUNYMUUDYQUWJUWKUYCUYDUYEUYFU
      YGUWGUWHUUDUWISUXKUXOUYAUXCXAUYHUXKUWHUUCUUOSUWGUXOUYAUGUUKUXIYHUUOYEUXFY
      HRUXGYMUXHUUDUUNUXFYHYLWMUXFYHYPWMWNXDXGUXPUUIUUDYQUUNPYGUUAUXPUUKBDYPYTU
      UHUUNYHYDUWNUXQUWKUWGYPYTXSVOUXKUWHUXOUXAWIUXSUXTXPWCXFXHXIXIXIXJXKUWFUVN
      UVORUWEUCYCUVNXLXQWKXMUWDUVOUVPRUWCNYAUVOXLXQWKXMXNOUDUUKBDYRUAUBUFUUHUUN
      UVQUCNUEUVQTUWNUXQUWKUYCXOOUDUVHCEUVAUAUBUFUVEUVKUVRUCNUEUVRTUVHTUXRUWLUY
      DXOXR $.

    $( If two categories have the same set of objects, morphisms, and
       compositions, then they have the same functor categories.  (Contributed
       by Mario Carneiro, 26-Jan-2017.) $)
    fucpropd $p |- ( ph -> ( A FuncCat C ) = ( B FuncCat D ) ) $=
      ( vf vg cfv co wceq wcel eqid vv vh vb va cnx cbs cfunc cop chom cnat cco
      vx cxp cv c1st c2nd cmpt cmpo csb ctp cfuc ccat funcpropd opeq2d natpropd
      sqxpeqd adantr wa cvv wnfc nfcsb1v fvexd ad3antrrr oveqd oveqdr homfeqbas
      nfv a1i ad4antr chomf ad5antr ccomf wrel wbr relfunc simpllr simpld xp1st
      simp-4r syl eqeltrd sylancr funcf1 ffvelcdmda simplr xp2nd simprd simplrr
      1st2ndbr nat1st2nd simpr simplrl comfeqval mpteq12dva mpoeq123dva csbeq1a
      natcl adantl eqtrd csbiedf tpeq123d eqidd fucval 3eqtr4d ) AUEUFPZBDUGQZU
      HZUEUIPZBDUJQZUHZUEUKPZUAUBXPXPUMZXPNUAUNZUOPZOYCUPPZUCUDOUNZUBUNZXSQZNUN
      ZYFXSQZULBUFPZULUNZUCUNZPZYLUDUNZPZYLYIUOPZPZYLYFUOPZPZUHZYLYGUOPZPZDUKPZ
      QQZUQZURZUSZUSZURZUHZUTXOCEUGQZUHZXRCEUJQZUHZYAUAUBUULUULUMZUULNYDOYEUCUD
      YFYGUUNQZYIYFUUNQZULCUFPZYNYPUUAUUCEUKPZQQZUQZURZUSZUSZURZUHZUTBDVAQZCEVA
      QZAXQUUMXTUUOUUKUVGAXPUULXOABCDEVBFGHIJKLMVCZVDAXSUUNXRABCDEFGHIJKLMVEZVD
      AUUJUVFYAAUAUBYBXPUUIUUPUULUVEAXPUULUVJVFAXPUULRYCYBSZUVJVGAUVLYGXPSZVHZV
      HZNYDUUHUVEVIUVONVQNUVEVJUVONYDUVDVKVRUVOYCUOVLUVOYIYDRZVHZUUHUVDUVEUVQOY
      EUUGUVDVIUVQOVQOUVDVJUVQOYEUVCVKVRUVQYCUPVLUVQYFYERZVHZUUGUVCUVDUVSUCUDYH
      YJUUFUUQUURUVBUVSXSUUNYFYGAXSUUNRUVNUVPUVRUVKVMZVNUVSYMYHSZNOXSUUNUVTVOUV
      SUWAYOYJSZVHZVHZULYKUUEUUSUVAAYKUUSRUVNUVPUVRUWCABCFVPVSUWDYLYKSZVHZDUFPZ
      DEUUTUUDYPYNDUIPZYRYTUUCUWGTZUWHTZUUDTZUUTTZADVTPEVTPRUVNUVPUVRUWCUWEHWAA
      DWBPEWBPRUVNUVPUVRUWCUWEIWAUWDYKUWGYLYQUWDYKUWGBDYQYIUPPZYKTZUWIUWDXPWCZY
      IXPSYQUWMXPWDBDWEZUWDYIYDXPUVOUVPUVRUWCWFUWDUVLYDXPSUWDUVLUVMAUVNUVPUVRUW
      CWIZWGZYCXPXPWHWJWKYIXPWSWLWMWNUWDYKUWGYLYSUWDYKUWGBDYSYFUPPZUWNUWIUWDUWO
      YFXPSYSUWSXPWDUWPUWDYFYEXPUVQUVRUWCWOUWDUVLYEXPSUWRYCXPXPWPWJWKYFXPWSWLWM
      WNUWDYKUWGYLUUBUWDYKUWGBDUUBYGUPPZUWNUWIUWDUWOUVMUUBUWTXPWDUWPUWDUVLUVMUW
      QWQYGXPWSWLWMWNUWFYOYKBDYQUWMUWHYSUWSXSYLXSTZUWFYOBDYIYFXSUXAUVSUWAUWBUWE
      WRWTUWNUWJUWDUWEXAZXGUWFYMYKBDYSUWSUWHUUBUWTXSYLUXAUWFYMBDYFYGXSUXAUVSUWA
      UWBUWEXBWTUWNUWJUXBXGXCXDXEUVRUVCUVDRUVQOYEUVCXFXHXIXJUVPUVDUVERUVONYDUVD
      XFXHXIXJXEVDXKAULUAYKXPBDUVHUUJUUDNOUBXSUDUCUVHTXPTUXAUWNUWKJLAUUJXLXMAUL
      UAUUSUULCEUVIUVFUUTNOUBUUNUDUCUVITUULTUUNTUUSTUWLKMAUVFXLXMXN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Initial, terminal and zero objects of a category
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c InitO $. $( The initial objects of a category. $)
  $c TermO $. $( The terminal objects of a category. $)
  $c ZeroO $. $( The zero objects of a category. $)

  $( Extend class notation with the class of initial objects of a category. $)
  cinito $a class InitO $.

  $( Extend class notation with the class of terminal objects of a category. $)
  ctermo $a class TermO $.

  $( Extend class notation with the class of zero objects of a category. $)
  czeroo $a class ZeroO $.

  ${
    $d a b c h $.
    $( An object A is said to be an initial object provided that for each
       object B there is exactly one morphism from A to B. Definition 7.1 in
       [Adamek] p. 101, or definition in [Lang] p. 57 (called "a universally
       repelling object" there).  See ~ dfinito2 and ~ dfinito3 for alternate
       definitions depending on ~ df-termo .  See ~ dfinito4 for an alternate
       definition using the universal property.  (Contributed by AV,
       3-Apr-2020.) $)
    df-inito $a |- InitO = ( c e. Cat |-> { a e. ( Base ` c ) |
                      A. b e. ( Base ` c ) E! h h e. ( a ( Hom ` c ) b ) } ) $.

    $( An object A is called a terminal object provided that for each object B
       there is exactly one morphism from B to A. Definition 7.4 in [Adamek]
       p. 102, or definition in [Lang] p. 57 (called "a universally attracting
       object" there).  See ~ dftermo2 and ~ dftermo3 for alternate definitions
       depending on ~ df-inito .  See ~ dftermo4 for an alternate definition
       using the universal property.  (Contributed by AV, 3-Apr-2020.) $)
    df-termo $a |- TermO = ( c e. Cat |-> { a e. ( Base ` c ) |
                      A. b e. ( Base ` c ) E! h h e. ( b ( Hom ` c ) a ) } ) $.

    $( An object A is called a zero object provided that it is both an initial
       object and a terminal object.  Definition 7.7 of [Adamek] p. 103.
       (Contributed by AV, 3-Apr-2020.) $)
    df-zeroo $a |- ZeroO = ( c e. Cat
                             |-> ( ( InitO ` c ) i^i ( TermO ` c ) ) ) $.

    $( ` InitO ` is a function on ` Cat ` .  (Contributed by Zhi Wang,
       29-Aug-2024.) $)
    initofn $p |- InitO Fn Cat $=
      ( vc vh va vb ccat cv chom cfv co wcel weu wral crab cinito fvex df-inito
      cbs rabex fnmpti ) AEBFCFDFAFZGHIJBKDTQHZLZCUAMNUBCUATQORBCDAPS $.

    $( ` TermO ` is a function on ` Cat ` .  (Contributed by Zhi Wang,
       29-Aug-2024.) $)
    termofn $p |- TermO Fn Cat $=
      ( vc vh vb va ccat cv chom cfv co wcel weu wral crab ctermo fvex df-termo
      cbs rabex fnmpti ) AEBFCFDFAFZGHIJBKCTQHZLZDUAMNUBDUATQORBDCAPS $.

    $( ` ZeroO ` is a function on ` Cat ` .  (Contributed by Zhi Wang,
       29-Aug-2024.) $)
    zeroofn $p |- ZeroO Fn Cat $=
      ( vc ccat cv cinito cfv ctermo cin czeroo fvex inex1 df-zeroo fnmpti ) AB
      ACZDEZMFEZGHNOMDIJAKL $.

    $( Reverse closure for an initial object:  If a class has an initial
       object, the class is a category.  (Contributed by AV, 4-Apr-2020.) $)
    initorcl $p |- ( I e. ( InitO ` C ) -> C e. Cat ) $=
      ( vc vh va vb ccat chom cfv wcel weu cbs wral crab cinito df-inito mptrcl
      cv co ) CGDRERFRCRZHISJDKFTLIZMEUANOBADEFCPQ $.

    $( Reverse closure for a terminal object:  If a class has a terminal
       object, the class is a category.  (Contributed by AV, 4-Apr-2020.) $)
    termorcl $p |- ( T e. ( TermO ` C ) -> C e. Cat ) $=
      ( vc vh vb va ccat chom cfv wcel weu cbs wral crab ctermo df-termo mptrcl
      cv co ) CGDRERFRCRZHISJDKETLIZMFUANOBADFECPQ $.

    $( Reverse closure for a zero object:  If a class has a zero object, the
       class is a category.  (Contributed by AV, 4-Apr-2020.) $)
    zeroorcl $p |- ( Z e. ( ZeroO ` C ) -> C e. Cat ) $=
      ( vc ccat cv cinito cfv ctermo cin czeroo df-zeroo mptrcl ) CDCEZFGMHGIJB
      ACKL $.

    $d B a b c $.  $d C a b c h $.  $d H c $.  $d ph c $.
    initoval.c $e |- ( ph -> C e. Cat ) $.
    initoval.b $e |- B = ( Base ` C ) $.
    initoval.h $e |- H = ( Hom ` C ) $.
    $( The value of the initial object function, i.e. the set of all initial
       objects of a category.  (Contributed by AV, 3-Apr-2020.) $)
    initoval $p |- ( ph -> ( InitO ` C )
                           = { a e. B | A. b e. B E! h h e. ( a H b ) } ) $=
      ( vc cv chom cfv co wcel weu cbs wral crab ccat cinito cvv df-inito fveq2
      wceq eqtr4di oveqd eleq2d eubidv raleqbidv rabeqbidv fvexi rabex fvmptd3
      a1i ) AKCDLZFLZGLZKLZMNZOZPZDQZGUTRNZSZFVETUQURUSEOZPZDQZGBSZFBTZUAUBUCDF
      GKUDUTCUFZVFVJFVEBVLVECRNBUTCRUEIUGZVLVDVIGVEBVMVLVCVHDVLVBVGUQVLVAEURUSV
      LVACMNEUTCMUEJUGUHUIUJUKULHVKUCPAVJFBBCRIUMUNUPUO $.

    $( The value of the terminal object function, i.e. the set of all terminal
       objects of a category.  (Contributed by AV, 3-Apr-2020.) $)
    termoval $p |- ( ph -> ( TermO ` C )
                           = { a e. B | A. b e. B E! h h e. ( b H a ) } ) $=
      ( vc cv chom cfv co wcel weu cbs wral crab ccat ctermo cvv df-termo fveq2
      wceq eqtr4di oveqd eleq2d eubidv raleqbidv rabeqbidv fvexi rabex fvmptd3
      a1i ) AKCDLZGLZFLZKLZMNZOZPZDQZGUTRNZSZFVETUQURUSEOZPZDQZGBSZFBTZUAUBUCDF
      GKUDUTCUFZVFVJFVEBVLVECRNBUTCRUEIUGZVLVDVIGVEBVMVLVCVHDVLVBVGUQVLVAEURUSV
      LVACMNEUTCMUEJUGUHUIUJUKULHVKUCPAVJFBBCRIUMUNUPUO $.

    $( The value of the zero object function, i.e. the set of all zero objects
       of a category.  (Contributed by AV, 3-Apr-2020.) $)
    zerooval $p |- ( ph -> ( ZeroO ` C )
                           = ( ( InitO ` C ) i^i ( TermO ` C ) ) ) $=
      ( vc cv cinito cfv ctermo cin ccat czeroo cvv df-zeroo wceq fveq2 ineq12d
      wcel fvex inex1 a1i fvmptd3 ) AHCHIZJKZUFLKZMCJKZCLKZMZNOPHQUFCRUGUIUHUJU
      FCJSUFCLSTEUKPUAAUIUJCJUBUCUDUE $.
  $}

  ${
    $d B b i $.  $d C b h i $.  $d H i $.  $d I b h i $.
    isinito.b $e |- B = ( Base ` C ) $.
    isinito.h $e |- H = ( Hom ` C ) $.
    isinito.c $e |- ( ph -> C e. Cat ) $.
    isinito.i $e |- ( ph -> I e. B ) $.
    $( The predicate "is an initial object" of a category.  (Contributed by AV,
       3-Apr-2020.) $)
    isinito $p |- ( ph -> ( I e. ( InitO ` C )
                            <-> A. b e. B E! h h e. ( I H b ) ) ) $=
      ( vi cinito cfv wcel cv co weu wral eleq2d crab initoval wb oveq1 ralbidv
      wceq eubidv elrab3 syl bitrd ) AFCMNZOFDPZLPZGPZEQZOZDRZGBSZLBUAZOZULFUNE
      QZOZDRZGBSZAUKUSFABCDELGJHIUBTAFBOUTVDUCKURVDLFBUMFUFZUQVCGBVEUPVBDVEUOVA
      ULUMFUNEUDTUGUEUHUIUJ $.

    $( The predicate "is a terminal object" of a category.  (Contributed by AV,
       3-Apr-2020.) $)
    istermo $p |- ( ph -> ( I e. ( TermO ` C )
                            <-> A. b e. B E! h h e. ( b H I ) ) ) $=
      ( vi ctermo cfv wcel cv co weu wral eleq2d crab termoval wb oveq2 ralbidv
      wceq eubidv elrab3 syl bitrd ) AFCMNZOFDPZGPZLPZEQZOZDRZGBSZLBUAZOZULUMFE
      QZOZDRZGBSZAUKUSFABCDELGJHIUBTAFBOUTVDUCKURVDLFBUNFUFZUQVCGBVEUPVBDVEUOVA
      ULUNFUMEUDTUGUEUHUIUJ $.

    $( The predicate "is a zero object" of a category.  (Contributed by AV,
       3-Apr-2020.) $)
    iszeroo $p |- ( ph -> ( I e. ( ZeroO ` C )
                        <-> ( I e. ( InitO ` C ) /\ I e. ( TermO ` C ) ) ) ) $=
      ( czeroo cfv wcel cinito ctermo cin wa zerooval eleq2d elin bitrdi ) AECJ
      KZLECMKZCNKZOZLEUBLEUCLPAUAUDEABCDHFGQREUBUCST $.
  $}

  ${
    $d B a b $.  $d C a b h $.  $d O a b h $.
    isinitoi.b $e |- B = ( Base ` C ) $.
    isinitoi.h $e |- H = ( Hom ` C ) $.
    isinitoi.c $e |- ( ph -> C e. Cat ) $.
    $( Implication of a class being an initial object.  (Contributed by AV,
       6-Apr-2020.) $)
    isinitoi $p |- ( ( ph /\ O e. ( InitO ` C ) )
                            -> ( O e. B /\ A. b e. B E! h h e. ( O H b ) ) ) $=
      ( va cinito cfv wcel wa cv co weu wral crab initoval eleq2d biimtrdi ccat
      elrabi imp adantr simpr isinito biimpd impancom jcai ) AFCLMZNZOFBNZDPZFG
      PZEQNDRGBSZAUNUOAUNFUPKPUQEQNDRGBSZKBTZNUOAUMUTFABCDEKGJHIUAUBUSKFBUEUCUF
      AUOUNURAUOOZUNURVABCDEFGHIACUDNUOJUGAUOUHUIUJUKUL $.

    $( Implication of a class being a terminal object.  (Contributed by AV,
       18-Apr-2020.) $)
    istermoi $p |- ( ( ph /\ O e. ( TermO ` C ) )
                            -> ( O e. B /\ A. b e. B E! h h e. ( b H O ) ) ) $=
      ( va ctermo cfv wcel wa cv co weu wral crab termoval eleq2d biimtrdi ccat
      elrabi imp adantr simpr istermo biimpd impancom jcai ) AFCLMZNZOFBNZDPZGP
      ZFEQNDRGBSZAUNUOAUNFUPUQKPEQNDRGBSZKBTZNUOAUMUTFABCDEKGJHIUAUBUSKFBUEUCUF
      AUOUNURAUOOZUNURVABCDEFGHIACUDNUOJUGAUOUHUIUJUKUL $.

    $d B h o $.  $d C o $.  $d H h o $.  $d O o $.  $d ph h $.
    $( For an initial object, the identity arrow is the one and only morphism
       of the object to the object itself.  (Contributed by AV, 6-Apr-2020.) $)
    initoid $p |- ( ( ph /\ O e. ( InitO ` C ) )
                            -> ( O H O ) = { ( ( Id ` C ) ` O ) } ) $=
      ( vh vo cfv wcel wa cv co weu csn wceq wi cvv cinito wral isinitoi eleq2d
      ccid oveq2 eubidv rspcv adantl eusn eqid ccat ad2antrr simpr catidcl fvex
      wex elsn eqcom wb sneqbg bicomd elv 3bitri biimpi a1i eleq2 eqeq1 3imtr4d
      syl5 exlimiv com12 biimtrid syld expimpd mpd ) AECUAKLZMZEBLZINZEJNZDOZLZ
      IPZJBUBZMEEDOZECUEKZKZQZRZABCIDEJFGHUCVRVSWEWJVRVSMZWEVTWFLZIPZWJVSWEWMSV
      RWDWMJEBWAERZWCWLIWNWBWFVTWAEEDUFUDUGUHUIWMWFVTQZRZIUQZWKWJIWFUJWQWKWJWPW
      KWJSIWKWHWFLZWPWJWKBCWGDEFGWGUKACULLVQVSHUMVRVSUNUOWPWHWOLZWOWIRZWRWJWSWT
      SWPWSWTWSWHVTRVTWHRZWTWHVTEWGUPURWHVTUSXAWTUTIVTTLWTXAVTWHTVAVBVCVDVEVFWF
      WOWHVGWFWOWIVHVIVJVKVLVMVNVOVP $.

    $( For a terminal object, the identity arrow is the one and only morphism
       of the object to the object itself.  (Contributed by AV,
       18-Apr-2020.) $)
    termoid $p |- ( ( ph /\ O e. ( TermO ` C ) )
                            -> ( O H O ) = { ( ( Id ` C ) ` O ) } ) $=
      ( vh vo cfv wcel wa cv co weu csn wceq wi cvv ctermo wral istermoi eleq2d
      ccid oveq1 eubidv rspcv adantl eusn eqid ccat ad2antrr simpr catidcl fvex
      wex elsn eqcom wb sneqbg bicomd elv 3bitri biimpi a1i eleq2 eqeq1 3imtr4d
      syl5 exlimiv com12 biimtrid syld expimpd mpd ) AECUAKLZMZEBLZINZJNZEDOZLZ
      IPZJBUBZMEEDOZECUEKZKZQZRZABCIDEJFGHUCVRVSWEWJVRVSMZWEVTWFLZIPZWJVSWEWMSV
      RWDWMJEBWAERZWCWLIWNWBWFVTWAEEDUFUDUGUHUIWMWFVTQZRZIUQZWKWJIWFUJWQWKWJWPW
      KWJSIWKWHWFLZWPWJWKBCWGDEFGWGUKACULLVQVSHUMVRVSUNUOWPWHWOLZWOWIRZWRWJWSWT
      SWPWSWTWSWHVTRVTWHRZWTWHVTEWGUPURWHVTUSXAWTUTIVTTLWTXAVTWHTVAVBVCVDVEVFWF
      WOWHVGWFWOWIVHVIVJVKVLVMVNVOVP $.
  $}

  ${
    $d a b c h $.
    $( An initial object is a terminal object in the opposite category.  An
       alternate definition of ~ df-inito depending on ~ df-termo .
       (Contributed by Zhi Wang, 29-Aug-2024.) $)
    dfinito2 $p  |- InitO = ( c e. Cat |-> ( TermO ` ( oppCat ` c ) ) ) $=
      ( vh va vb cinito ccat cv chom cfv co wcel weu cbs wral crab coppc ctermo
      cmpt df-inito eqid oppccat oppcbas termoval oppchom eleq2i eubii mpteq2ia
      ralbii rabbii eqtrdi eqtr4i ) EAFBGZCGZDGZAGZHIZJZKZBLZDUOMIZNZCUTOZRAFUO
      PIZQIZRBCDASAFVDVBUOFKZVDULUNUMVCHIZJZKZBLZDUTNZCUTOVBVEUTVCBVFCDUOVCVCTZ
      UAUTUOVCVKUTTUBVFTUCVJVACUTVIUSDUTVHURBVGUQULUOUPVCUNUMUPTVKUDUEUFUHUIUJU
      GUK $.

    $( A terminal object is an initial object in the opposite category.  An
       alternate definition of ~ df-termo depending on ~ df-inito .
       (Contributed by Zhi Wang, 29-Aug-2024.) $)
    dftermo2 $p |- TermO = ( c e. Cat |-> ( InitO ` ( oppCat ` c ) ) ) $=
      ( vh vb va ctermo ccat cv chom cfv co wcel weu cbs wral crab coppc cinito
      cmpt df-termo eqid oppccat oppcbas initoval oppchom eleq2i eubii mpteq2ia
      ralbii rabbii eqtrdi eqtr4i ) EAFBGZCGZDGZAGZHIZJZKZBLZCUOMIZNZDUTOZRAFUO
      PIZQIZRBDCASAFVDVBUOFKZVDULUNUMVCHIZJZKZBLZCUTNZDUTOVBVEUTVCBVFDCUOVCVCTZ
      UAUTUOVCVKUTTUBVFTUCVJVADUTVIUSCUTVHURBVGUQULUOUPVCUNUMUPTVKUDUEUFUHUIUJU
      GUK $.

    $( An alternate definition of ~ df-inito depending on ~ df-termo , without
       dummy variables.  (Contributed by Zhi Wang, 29-Aug-2024.) $)
    dfinito3 $p  |- InitO = ( TermO o. ( oppCat |` Cat ) ) $=
      ( vc ccat cv coppc cres cfv ctermo cmpt ccom cinito fvres fveq2d mpteq2ia
      wcel cvv wf wceq wfn termofn dffn2 mpbi oppccatf fcompt dfinito2 3eqtr4ri
      mp2an ) ABACZDBEZFZGFZHZABUGDFZGFZHGUHIZJABUJUMUGBNUIULGUGBDKLMBOGPZBBUHP
      UNUKQGBRUOSBGTUAUBAGUHBBOUCUFAUDUE $.

    $( An alternate definition of ~ df-termo depending on ~ df-inito , without
       dummy variables.  (Contributed by Zhi Wang, 29-Aug-2024.) $)
    dftermo3 $p  |- TermO = ( InitO o. ( oppCat |` Cat ) ) $=
      ( vc ccat cv coppc cres cfv cinito cmpt ccom ctermo fvres fveq2d mpteq2ia
      wcel cvv wf wceq wfn initofn dffn2 mpbi oppccatf fcompt dftermo2 3eqtr4ri
      mp2an ) ABACZDBEZFZGFZHZABUGDFZGFZHGUHIZJABUJUMUGBNUIULGUGBDKLMBOGPZBBUHP
      UNUKQGBRUOSBGTUAUBAGUHBBOUCUFAUDUE $.
  $}

  ${
    $d C b h $.  $d O b h $.
    $( An initial object is an object.  (Contributed by AV, 14-Apr-2020.) $)
    initoo $p |- ( C e. Cat -> ( O e. ( InitO ` C ) -> O e. ( Base ` C ) ) ) $=
      ( vh vb ccat wcel cinito cfv cbs wa cv chom weu wral eqid isinitoi simpld
      co id ex ) AEFZBAGHFZBAIHZFZUAUBJUDCKBDKALHZRFCMDUCNUAUCACUEBDUCOUEOUASPQ
      T $.

    $( A terminal object is an object.  (Contributed by AV, 18-Apr-2020.) $)
    termoo $p |- ( C e. Cat -> ( O e. ( TermO ` C ) -> O e. ( Base ` C ) ) ) $=
      ( vh vb ccat wcel ctermo cfv cbs wa cv chom weu wral eqid istermoi simpld
      co id ex ) AEFZBAGHFZBAIHZFZUAUBJUDCKDKBALHZRFCMDUCNUAUCACUEBDUCOUEOUASPQ
      T $.
  $}

  $( Implication of a class being a zero object.  (Contributed by AV,
     18-Apr-2020.) $)
  iszeroi $p |- ( ( C e. Cat /\ O e. ( ZeroO ` C ) ) -> ( O e. ( Base ` C )
                         /\ ( O e. ( InitO ` C ) /\ O e. ( TermO ` C ) ) ) ) $=
    ( ccat wcel czeroo cfv cbs cinito ctermo cin chom eqid zerooval eleq2d elin
    wa id initoo adantrd biimtrid sylbid imp simpl iszeroo biimpd impancom jcai
    simpr ) ACDZBAEFZDZPBAGFZDZBAHFZDZBAIFZDZPZUIUKUMUIUKBUNUPJZDZUMUIUJUSBUIUL
    AAKFZUIQULLZVALZMNUTURUIUMBUNUPOUIUOUMUQABRSTUAUBUIUMUKURUIUMPZUKURVDULAVAB
    VBVCUIUMUCUIUMUHUDUEUFUG $.

  ${
    $d A a g $.  $d A b f $.  $d B a g $.  $d B b f $.  $d C b f $.
    $d C a g $.  $d ph g f $.  $d a f $.
    initoeu1.c $e |- ( ph -> C e. Cat ) $.
    initoeu1.a $e |- ( ph -> A e. ( InitO ` C ) ) $.
    ${
      initoeu1.b $e |- ( ph -> B e. ( InitO ` C ) ) $.
      $( Morphisms between two initial objects are inverses.  (Contributed by
         AV, 14-Apr-2020.) $)
      2initoinv $p |- ( ( ph /\ G e. ( B ( Hom ` C ) A )
                             /\ F e. ( A ( Hom ` C ) B ) )
                        -> F ( A ( Inv ` C ) B ) G ) $=
        ( cfv co wcel wbr cop wceq eqid 3ad2ant1 initoo sylc catcocl chom csect
        w3a cinv cco ccid cbs cinito simp3 simp2 csn initoid mpdan eleq2d elsni
        ccat biimtrdi mpd issect2 mpbird wa wb isinv mpbir2and ) AFCBDUAJZKLZEB
        CVEKLZUCZEFBCDUDJZKMZEFBCDUBJZKMZFECBVKKMZVHVLFEBCNBDUEJZKKZBDUFJZJZOZV
        HVOBBVEKZLZVRVHDUGJZDVNEFVEBCBWAPZVEPZVNPZAVFDUPLZVGGQZAVFBWALZVGAWEBDU
        HJZLZWGGHDBRSZQZAVFCWALZVGAWECWHLZWLGIDCRSZQZWKAVFVGUIZAVFVGUJZTVHVTVOV
        QUKZLVRVHVSWRVOAVFVSWROZVGAWIWSHAWADVEBWBWCGULUMQUNVOVQUOUQURVHWADVKVNV
        PEFVEBCWBWCWDVPPZVKPZWFWKWOWPWQUSUTVHVMEFCBNCVNKKZCVPJZOZVHXBCCVEKZLZXD
        VHWADVNFEVECBCWBWCWDWFWOWKWOWQWPTVHXFXBXCUKZLXDVHXEXGXBAVFXEXGOZVGAWMXH
        IAWADVECWBWCGULUMQUNXBXCUOUQURVHWADVKVNVPFEVECBWBWCWDWTXAWFWOWKWQWPUSUT
        AVFVJVLVMVAVBVGAWADVKEFVIBCWBVIPGWJWNXAVCQVD $.

      $( Initial objects are essentially unique (strong form), i.e. there is a
         _unique_ isomorphism between two initial objects, see statement in
         [Lang] p. 58 ("... if P, P' are two universal objects [[...] then
         there exists a unique isomorphism between them.".  (Proposed by BJ,
         14-Apr-2020.)  (Contributed by AV, 14-Apr-2020.) $)
      initoeu1 $p |- ( ph -> E! f f e. ( A ( Iso ` C ) B ) ) $=
        ( vb vg va cfv wcel cv co weu wa eqid wi wex cbs chom wral cinito mpdan
        ciso isinitoi oveq2 eleq2d eubidv rspcv wss adantr simprr simprl isohom
        wceq ccat euex a1i rspcva ex ad2antll cinv ad2antrr 2initoinv ad4ant134
        syl wbr inviso1 eximdv expcom exlimiv com3l impd syl2and euelss syl3anc
        imp exp42 com24 com14 expd syldc com15 mpd ) ABDUALZMZENZBINZDUBLZOZMZE
        PZIWGUCZQZWIBCDUFLZOZMZEPZABDUDLZMWPGAWGDEWKBIWGRZWKRZFUGUEAWHWOWTACWGM
        ZJNZCKNZWKOZMZJPZKWGUCZQZWHWOWTSSZACXAMXKHAWGDJWKCKXBXCFUGUEAXDXJXLWOXD
        XJWHAWTXDWOWIBCWKOZMZEPZXJWHAWTSSZSWNXOICWGWJCUQZWMXNEXQWLXMWIWJCBWKUHU
        IUJUKXDXOXJXPAXOXJQZWHXDWTAXDWHXRWTAXDWHXRWTAXDWHQZQZXRQWRXMULZWSETZXOW
        TXTYAXRXTWGDWKWQBCXBXCWQRZADURMZXSFUMZAXDWHUNZAXDWHUOZUPUMXTXRYBXTXOXNE
        TZXJXECBWKOZMZJTZYBXOYHSXTXNEUSUTWHXJYKSAXDWHXJYKWHXJQYJJPZYKXIYLKBWGXF
        BUQZXHYJJYMXGYIXEXFBCWKUHUIUJVAYJJUSVHVBVCXTYHYKYBYKXTYHYBYJXTYHYBSZSJX
        TYJYNXTYJQZXNWSEYOXNWSYOXNQWGDWIXEWQDVDLZBCXBYPRXTYDYJXNYEVEXTWHYJXNYFV
        EXTXDYJXNYGVEYCAYJXNWIXEBCYPOVIXSABCDWIXEFGHVFVGVJVBVKVLVMVNVOVPVSXTXOX
        JUOEWRXMVQVRVTWAWBWCWDWEVOWFVOWF $.

      $( Initial objects are essentially unique (weak form), i.e. if A and B
         are initial objects, then A and B are isomorphic.  Proposition 7.3 (1)
         of [Adamek] p. 102.  (Contributed by AV, 6-Apr-2020.) $)
      initoeu1w $p |- ( ph -> A ( ~=c ` C ) B ) $=
        ( vf ccic cfv wbr cv ciso co wcel wex weu eqid initoo sylc initoeu1 syl
        euex cbs ccat cinito cic mpbird ) ABCDIJKHLBCDMJZNOZHPZAUJHQUKABCDHEFGU
        AUJHUCUBADUDJZDHUIBCUIRULREADUEOZBDUFJZOBULOEFDBSTAUMCUNOCULOEGDCSTUGUH
        $.
    $}

    ${
      initoeu2lem.x $e |- X = ( Base ` C ) $.
      initoeu2lem.h $e |- H = ( Hom ` C ) $.
      initoeu2lem.i $e |- I = ( Iso ` C ) $.
      initoeu2lem.o $e |- .o. = ( comp ` C ) $.
      $( Lemma 0 for ~ initoeu2 .  (Contributed by AV, 9-Apr-2020.) $)
      initoeu2lem0 $p |- ( ( ( ph /\ ( A e. X /\ B e. X /\ D e. X ) )
                 /\ ( K e. ( B I A ) /\ F e. ( A H D ) /\ G e. ( B H D ) )
                 /\ ( ( F ( <. B , A >. .o. D ) K ) ( <. A , B >. .o. D )
                      ( ( B ( Inv ` C ) A ) ` K ) )
                    = ( G ( <. A , B >. .o. D ) ( ( B ( Inv ` C ) A ) ` K ) ) )
                           -> G = ( F ( <. B , A >. .o. D ) K ) ) $=
        ( wcel co w3a wa cop cinv cfv wceq 3simpa simp3 eqcomd eqid ccat adantr
        simpr1 simpr2 simplr3 ciso oveqi eleq2i biimpi 3ad2ant1 adantl 3ad2ant3
        chom wi isohom sseld com12 impcom 3ad2ant2 catcocl cco rcaninv sylc ) A
        BKSZCKSZEKSZUAZUBZJCBITZSZFBEHTZSZGCEHTZSZUAZFJCBUCELTTZJCBDUDUEZTUEZBC
        UCZELTZTZGWHWJTZUFZUAZVRWEUBZWLWKUFGWFUFVRWEWMUGWNWKWLVRWEWMUHUIWOKDWHJ
        GWFWGBCWJEOWGUJVRDUKSZWEAWPVQMULZULZVRVNWEAVNVOVPUMZULZVRVOWEAVNVOVPUNZ
        ULZVNVOVPAWEUOZWEJCBDUPUEZTZSZVRVTWBXFWDVTXFVSXEJIXDCBQUQURUSUTVAWEGCED
        VCUEZTZSZVRWDVTXIWBWDXIWCXHGHXGCEPUQURUSVBVAWOKDLJFXGCBEOXGUJZRWRXBWTXC
        WEVRJCBXGTZSZVTWBVRXLVDWDVRVTXLVRVSXKJVRKDXGICBOXJQWQXAWSVEVFVGUTVHWEFB
        EXGTZSZVRWBVTXNWDWBXNWAXMFHXGBEPUQURUSVIVAVJWHUJLDVKUEWIERUQVLVM $.

      $d D f $.  $d F f $.  $d G f $.  $d I f $.  $d K f $.  $d H f $.
      $d X f $.  $d .o. f $.
      $( Lemma 1 for ~ initoeu2 .  (Contributed by AV, 9-Apr-2020.) $)
      initoeu2lem1 $p |- ( ( ph /\ ( A e. X /\ B e. X /\ D e. X )
          /\ ( K e. ( B I A ) /\ ( F ( <. B , A >. .o. D ) K ) e. ( B H D ) ) )
               -> ( ( E! f f e. ( A H D ) /\ F e. ( A H D ) /\ G e. ( B H D ) )
                    -> G = ( F ( <. B , A >. .o. D ) K ) ) ) $=
        ( wi cv co wcel weu w3a cop wa wceq csn wex eusn cinv cfv eqid ad2antrr
        ccat simpr2 adantr simpr1 invf simpr ffvelcdmd wss isohom sselda simpr3
        ad4antr simplr catcocl exp31 imp eleq2 adantl cvv ovex elsng mp1i bitrd
        eqeq2 eqcoms simp-4l simp-4r simprr simprl initoeu2lem0 syl131anc exp43
        wb sylbid ex com23 com24 syld com25 mpd mpdan com15 impcom com13 3impia
        expimpd com12 exlimiv sylbi 3impib ) FUAZBEIUBZUCFUDZGXGUCZHCEIUBZUCZUE
        ABLUCZCLUCZELUCZUEZKCBJUBZUCZGKCBUFEMUBUBZXJUCZUGZUEZHXRUHZXHXIXKYAYBTZ
        XHXGXFUIZUHZFUJXIXKUGZYCTZFXGUKYEYGFYEYFYCYAYEYFUGZYBAXOXTYHYBTZAXOUGZX
        QXSYIYJXQUGZKCBDULUMZUBZUMZBCJUBZUCZXSYITYKXPYOKYMYKLDJYLCBPYLUNADUPUCZ
        XOXQNUOYJXMXQAXLXMXNUQZURYJXLXQAXLXMXNUSZURRUTYJXQVAVBYHXSYKYPUGZYBYFYE
        XSYTYBTTZXIXKYEUUATYTXKYEXSXIYBYTYNBCIUBZUCZXKYEXSXIYBTZTTZTYKYOUUBYNYJ
        YOUUBVCXQYJLDIJBCPQRAYQXONURZYSYRVDURVEYTUUCUGZXKUUEUUGXKUGZHYNBCUFEMUB
        ZUBZXGUCZUUEUUHLDMYNHIBCEPQSYJYQXQYPUUCXKUUFVGYJXLXQYPUUCXKYSVGYJXMXQYP
        UUCXKYRVGYJXNXQYPUUCXKAXLXMXNVFZVGYTUUCXKVHUUGXKVAVIUUGXKUUKUUETUUGXSUU
        KYEXKUUDUUGXSXRYNUUIUBZXGUCZUUKYEXKUUDTZTTZYTUUCXSUUNTZYJUUCUUQTXQYPYJU
        UCXSUUNYJUUCUGZXSUGLDMYNXRIBCEPQSYJYQUUCXSUUFUOYJXLUUCXSYSUOYJXMUUCXSYR
        UOYJXNUUCXSUULUOYJUUCXSVHUURXSVAVIVJUOVKYTUUNUUPTUUCYTYEUUKUUNUUOYTYEUU
        KUUNUUOTTYTYEUGZUUNUUKUUOUUSUUNUUMXFUHZUUKUUOTUUSUUNUUMYDUCZUUTYEUUNUVA
        WHYTXGYDUUMVLVMUUMVNUCUVAUUTWHUUSXRYNUUIVOUUMXFVNVPVQVRUUSUUKUUTUUOUUSU
        UKUUJXFUHZUUTUUOTZYEUUKUVBWHYTYEUUKUUJYDUCZUVBXGYDUUJVLUUJVNUCUVDUVBWHY
        EHYNUUIVOUUJXFVNVPVQVRVMYTUVBUVCTYEYTUVBUVCYTUVBUGUUTUUMUUJUHZUUOUVBUUT
        UVEWHZYTUVFXFUUJXFUUJUUMVSVTVMYTUVEUUOTUVBYTUVEXKXIYBYTUVEUGZXKXIUGZUGY
        JXQXIXKUVEYBYJXQYPUVEUVHWAYJXQYPUVEUVHWBUVGXKXIWCUVGXKXIWDYTUVEUVHVHABC
        DEGHIJKLMNOPQRSWEWFWGURWIWJURWIWKWIWKWJWLURWMWNVKWOWJWPWQVKWRWSWPXAWTXB
        WJXCXDXEXB $.

      $d A f h $.  $d B h $.  $d D g h $.  $d F g h $.  $d H g h $.
      $d I g h $.  $d K g h $.  $d X g h $.  $d .o. g h $.  $d ph g h $.
      $( Lemma 2 for ~ initoeu2 .  (Contributed by AV, 10-Apr-2020.) $)
      initoeu2lem2 $p |- ( ( ph /\ ( A e. X /\ B e. X /\ D e. X )
                         /\ ( K e. ( B I A ) /\ F e. ( A H D )
                              /\ ( F ( <. B , A >. .o. D ) K ) e. ( B H D ) ) )
                         -> ( E! f f e. ( A H D ) -> E! g g e. ( B H D ) ) ) $=
        ( wcel vh w3a co cop cv weu wa wex wceq wal cvv ovex eleq1 spcegv com12
        wi mp1i 3ad2ant3 a1d adantr simpll1 simpll2 3simpb simplr simpl32 simpr
        3imp initoeu2lem1 imp syl33anc adantrr adantrl eqtr4d alrimivv sylanbrc
        ex eu4 ) ABLTCLTELTUBZKCBJUCTZHBEIUCZTZHKCBUDEMUCZUCZCEIUCZTZUBZUBZFUEV
        TTFUFZGUEZWDTZGUFZWGWHUGZWJGUHZWJUAUEZWDTZUGZWIWNUIZUPZUAUJGUJWKWGWMWHA
        VRWFWMAWFWMUPVRWFAWMWEVSAWMUPWAAWEWMWCUKTWEWMUPAHKWBULWJWEGWCUKWIWCWDUM
        UNUQUOURUOUSVGUTWLWRGUAWLWPWQWLWPUGWIWCWNWLWJWIWCUIZWOWLWJUGAVRVSWEUGZW
        HWAWJWSAVRWFWHWJVAAVRWFWHWJVBWLWTWJWGWTWHWFAWTVRVSWAWEVCURUTZUTWGWHWJVD
        WLWAWJVSWAWEAVRWHVEZUTWLWJVFAVRWTUBZWHWAWJUBWSABCDEFHWIIJKLMNOPQRSVHVIV
        JVKWLWOWNWCUIZWJWLWOUGAVRWTWHWAWOXDAVRWFWHWOVAAVRWFWHWOVBWLWTWOXAUTWGWH
        WOVDWLWAWOXBUTWLWOVFXCWHWAWOUBXDABCDEFHWNIJKLMNOPQRSVHVIVJVLVMVPVNWJWOG
        UAWIWNWDUMVQVOVP $.
    $}

    $d A f g h k $.  $d B f g h k $.  $d C h k $.  $d ph b f g h k $.
    $d a b $.
    initoeu2.i $e |- ( ph -> A ( ~=c ` C ) B ) $.
    $( Initial objects are essentially unique, if A is an initial object, then
       so is every object that is isomorphic to A. Proposition 7.3 (2) in
       [Adamek] p. 102.  (Contributed by AV, 10-Apr-2020.) $)
    initoeu2 $p |- ( ph -> B e. ( InitO ` C ) ) $=
      ( vb vf va vh cfv wcel wa cv co wi adantr ad2antrr ex ccic wbr cinito cbs
      vg vk ccat ciclcl cicrcl chom weu wral cicsym ciso wex eqid simprr simprl
      sylan cic isinitoi mpdan weq oveq2 eleq2d eubidv rspcva nfv eleq1w cbveuw
      euex simpr ad2antrl simprll isohom sselda cop cco catcocl simp-4l biimpri
      df-3an ad4antlr initoeu2lem2 syl113anc mpand com23 com15 expd com24 com12
      w3a exlimiv syl sylbi pm2.43i mpd adantld exlimdv sylbid ralrimiv isinito
      imp an32s mpbird mp2and ) ABCDUALZUBZCDUCLZMZGAXHNZBDUDLZMZCXLMZXJADUGMZX
      HXMEDBCUHUSAXOXHXNEDBCUIUSXKXMXNNZXJXKXPNZXJUEOCHOZDUJLZPZMUEUKZHXLULXQYA
      HXLAXPXHXRXLMZYAQZAXPNZXHNCBXGUBZYCYDXOXHYEAXOXPERZDBCUMUSYDYEYCQXHYDYEUF
      OZCBDUNLZPZMZUFUOYCYDXLDUFYHCBYHUPZXLUPZYFAXMXNUQAXMXNURUTYDYJYCUFAXPYJYC
      QZAXMIOZBJOZXSPZMZIUKZJXLULZNZXPYMQZABXIMYTFAXLDIXSBJYLXSUPZEVAVBAYSUUAXM
      YBYSXPYJAYAYBYSXPYJAYAQQZQZYBYSNYNBXRXSPZMZIUKZUUDYRUUGJXRXLJHVCZYQUUFIUU
      HYPUUEYNYOXRBXSVDVEVFVGYBUUGUUDQYSUUGYBUUDUUGYBUUDQZUUGKOZUUEMZKUKZUUGUUI
      QZUUFUUKIKUUFKVHUUKIVHIKUUEVIVJUULUUKKUOUUMUUKKVKUUKUUMKUUGUUKUUIUUGXPYBU
      UKUUCUUGXPYBUUKUUCQAXPYBNZUUKYJUUGYAAUUNUUKYJUUGYAQZQQAUUNNZYJUUKUUOUUPYJ
      UUKUUOQUUPYJNZYGCBXSPZMZUUKUUOUUPYIUURYGUUPXLDXSYHCBYLUUBYKAXOUUNERZXPXNA
      YBXMXNVLVMZAXMXNYBVNZVOVPUUQUUSUUKNZUUOUUQUVCNZUUJYGCBVQXRDVRLZPPXTMZUUOU
      VDXLDUVEYGUUJXSCBXRYLUUBUVEUPZUUPXOYJUVCUUTSUUPXNYJUVCUVASUUPXMYJUVCUVBSU
      UPYBYJUVCAXPYBUQSUUQUUSUUKURUUQUUSUUKUQZVSUVDUVFNAXMXNYBWLZYJUUKUVFUUOAUU
      NYJUVCUVFVTUUNUVIAYJUVCUVFUVIUUNXMXNYBWBWAWCUUQYJUVCUVFUUPYJVLSUVDUUKUVFU
      VHRUVDUVFVLABCDXRIUEUUJXSYHYGXLUVEEFYLUUBYKUVGWDWEVBTWFTWGTWHWIWJWKWMWNWO
      WPWKRWQTWHWRWQXCWSWTRWQXDXAXQXLDUEXSCHYLUUBAXOXHXPESXKXMXNUQXBXETXFVB $.
  $}

  ${
    $d A a g $.  $d A b f $.  $d B a g $.  $d B b f $.  $d C b f $.
    $d C a g $.  $d ph g f $.  $d a f $.  $d b g $.
    termoeu1.c $e |- ( ph -> C e. Cat ) $.
    termoeu1.a $e |- ( ph -> A e. ( TermO ` C ) ) $.
    ${
      termoeu1.b $e |- ( ph -> B e. ( TermO ` C ) ) $.
      $( Morphisms between two terminal objects are inverses.  (Contributed by
         AV, 18-Apr-2020.) $)
      2termoinv $p |- ( ( ph /\ G e. ( B ( Hom ` C ) A )
                             /\ F e. ( A ( Hom ` C ) B ) )
                        -> F ( A ( Inv ` C ) B ) G ) $=
        ( cfv co wcel wbr cop wceq eqid 3ad2ant1 termoo sylc catcocl chom csect
        w3a cinv cco ccid cbs ctermo simp3 simp2 csn termoid mpdan eleq2d elsni
        ccat biimtrdi mpd issect2 mpbird wa wb isinv mpbir2and ) AFCBDUAJZKLZEB
        CVEKLZUCZEFBCDUDJZKMZEFBCDUBJZKMZFECBVKKMZVHVLFEBCNBDUEJZKKZBDUFJZJZOZV
        HVOBBVEKZLZVRVHDUGJZDVNEFVEBCBWAPZVEPZVNPZAVFDUPLZVGGQZAVFBWALZVGAWEBDU
        HJZLZWGGHDBRSZQZAVFCWALZVGAWECWHLZWLGIDCRSZQZWKAVFVGUIZAVFVGUJZTVHVTVOV
        QUKZLVRVHVSWRVOAVFVSWROZVGAWIWSHAWADVEBWBWCGULUMQUNVOVQUOUQURVHWADVKVNV
        PEFVEBCWBWCWDVPPZVKPZWFWKWOWPWQUSUTVHVMEFCBNCVNKKZCVPJZOZVHXBCCVEKZLZXD
        VHWADVNFEVECBCWBWCWDWFWOWKWOWQWPTVHXFXBXCUKZLXDVHXEXGXBAVFXEXGOZVGAWMXH
        IAWADVECWBWCGULUMQUNXBXCUOUQURVHWADVKVNVPFEVECBWBWCWDWTXAWFWOWKWQWPUSUT
        AVFVJVLVMVAVBVGAWADVKEFVIBCWBVIPGWJWNXAVCQVD $.

      $( Terminal objects are essentially unique (strong form), i.e. there is a
         _unique_ isomorphism between two terminal objects, see statement in
         [Lang] p. 58 ("... if P, P' are two universal objects [[...] then
         there exists a unique isomorphism between them.".  (Proposed by BJ,
         14-Apr-2020.)  (Contributed by AV, 18-Apr-2020.) $)
      termoeu1 $p |- ( ph -> E! f f e. ( A ( Iso ` C ) B ) ) $=
        ( va vg vb cfv wcel cv co weu wa eqid wi wex cbs chom wral ctermo mpdan
        ciso istermoi oveq1 eleq2d eubidv rspcv wss adantr simprl simprr isohom
        wceq ccat euex a1i rspcva ex ad2antll cinv ad2antrr 2termoinv ad4ant134
        syl wbr inviso1 eximdv expcom exlimiv com3l impd syl2and euelss syl3anc
        imp exp42 com24 com14 expd syldc com15 mpd ) ACDUALZMZENZINZCDUBLZOZMZE
        PZIWGUCZQZWIBCDUFLZOZMZEPZACDUDLZMWPHAWGDEWKCIWGRZWKRZFUGUEAWHWOWTABWGM
        ZJNZKNZBWKOZMZJPZKWGUCZQZWHWOWTSSZABXAMXKGAWGDJWKBKXBXCFUGUEAXDXJXLWOXD
        XJWHAWTXDWOWIBCWKOZMZEPZXJWHAWTSSZSWNXOIBWGWJBUQZWMXNEXQWLXMWIWJBCWKUHU
        IUJUKXDXOXJXPAXOXJQZWHXDWTAXDWHXRWTAXDWHXRWTAXDWHQZQZXRQWRXMULZWSETZXOW
        TXTYAXRXTWGDWKWQBCXBXCWQRZADURMZXSFUMZAXDWHUNZAXDWHUOZUPUMXTXRYBXTXOXNE
        TZXJXECBWKOZMZJTZYBXOYHSXTXNEUSUTWHXJYKSAXDWHXJYKWHXJQYJJPZYKXIYLKCWGXF
        CUQZXHYJJYMXGYIXEXFCBWKUHUIUJVAYJJUSVHVBVCXTYHYKYBYKXTYHYBYJXTYHYBSZSJX
        TYJYNXTYJQZXNWSEYOXNWSYOXNQWGDWIXEWQDVDLZBCXBYPRXTYDYJXNYEVEXTXDYJXNYFV
        EXTWHYJXNYGVEYCAYJXNWIXEBCYPOVIXSABCDWIXEFGHVFVGVJVBVKVLVMVNVOVPVSXTXOX
        JUNEWRXMVQVRVTWAWBWCWDWEVOWFVOWF $.

      $( Terminal objects are essentially unique (weak form), i.e. if A and B
         are terminal objects, then A and B are isomorphic.  Proposition 7.6 of
         [Adamek] p. 103.  (Contributed by AV, 18-Apr-2020.) $)
      termoeu1w $p |- ( ph -> A ( ~=c ` C ) B ) $=
        ( vf ccic cfv wbr cv ciso co wcel wex weu eqid termoo sylc termoeu1 syl
        euex cbs ccat ctermo cic mpbird ) ABCDIJKHLBCDMJZNOZHPZAUJHQUKABCDHEFGU
        AUJHUCUBADUDJZDHUIBCUIRULREADUEOZBDUFJZOBULOEFDBSTAUMCUNOCULOEGDCSTUGUH
        $.
    $}
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Arrows (disjointified hom-sets)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c domA $.
  $c codA $.
  $c Arrow $.
  $c HomA $.

  $( Extend class notation to include the domain extractor for an arrow. $)
  cdoma $a class domA $.

  $( Extend class notation to include the codomain extractor for an arrow. $)
  ccoda $a class codA $.

  $( Extend class notation to include the collection of all arrows of a
     category. $)
  carw $a class Arrow $.

  $( Extend class notation to include the set of all arrows with a specific
     domain and codomain. $)
  choma $a class HomA $.

  ${
    $d c x z B $.  $d c x z C $.  $d c z J $.  $d x z ph $.  $d z X $.
    $d z Y $.
    $( Definition of the domain extractor for an arrow.  (Contributed by FL,
       24-Oct-2007.)  (Revised by Mario Carneiro, 11-Jan-2017.) $)
    df-doma $a |- domA = ( 1st o. 1st ) $.

    $( Definition of the codomain extractor for an arrow.  (Contributed by FL,
       26-Oct-2007.)  (Revised by Mario Carneiro, 11-Jan-2017.) $)
    df-coda $a |- codA = ( 2nd o. 1st ) $.

    $( Definition of the hom-set extractor for arrows, which tags the morphisms
       of the underlying hom-set with domain and codomain, which can then be
       extracted using ~ df-doma and ~ df-coda .  (Contributed by FL,
       6-May-2007.)  (Revised by Mario Carneiro, 11-Jan-2017.) $)
    df-homa $a |- HomA = ( c e. Cat |-> ( x e. ( ( Base ` c ) X. ( Base ` c ) )
      |-> ( { x } X. ( ( Hom ` c ) ` x ) ) ) ) $.

    $( Definition of the set of arrows of a category.  We will use the term
       "arrow" to denote a morphism tagged with its domain and codomain, as
       opposed to ` Hom ` , which allows hom-sets for distinct objects to
       overlap.  (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    df-arw $a |- Arrow = ( c e. Cat |-> U. ran ( HomA ` c ) ) $.

    homarcl.h $e |- H = ( HomA ` C ) $.
    $( Reverse closure for an arrow.  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)
    homarcl $p |- ( F e. ( X H Y ) -> C e. Cat ) $=
      ( vc vx co wcel c0 wceq ccat n0i wn choma cfv cv cbs cxp csn chom df-homa
      cmpt fvmptndm eqtrid oveqd 0ov eqtrdi nsyl2 ) BDECIZJUKKLAMJZUKBNULOZUKDE
      KIKUMCKDEUMCAPQKFGMHGRZSQZUOTHRZUAUPUNUBQQTUDPAHGUCUEUFUGDEUHUIUJ $.

    homafval.b $e |- B = ( Base ` C ) $.
    homafval.c $e |- ( ph -> C e. Cat ) $.
    ${
      homafval.j $e |- J = ( Hom ` C ) $.
      $( Value of the disjointified hom-set function.  (Contributed by Mario
         Carneiro, 11-Jan-2017.) $)
      homafval $p |- ( ph -> H =
        ( x e. ( B X. B ) |-> ( { x } X. ( J ` x ) ) ) ) $=
        ( vc choma cfv cxp cv cmpt ccat wceq cbs chom csn fveq2 eqtr4di sqxpeqd
        wcel fveq1d xpeq2d mpteq12dv df-homa fvexi xpex mptex fvmpt syl eqtrid
        ) AEDLMZBCCNZBOZUAZURFMZNZPZGADQUEUPVBRIKDBKOZSMZVDNZUSURVCTMZMZNZPVBQL
        VCDRZBVEVHUQVAVIVDCVIVDDSMCVCDSUBHUCUDVIVGUTUSVIURVFFVIVFDTMFVCDTUBJUCU
        FUGUHBKUIBUQVACCCDSHUJZVJUKULUMUNUO $.
    $}

    $( Functionality of the disjointified hom-set function.  (Contributed by
       Mario Carneiro, 11-Jan-2017.) $)
    homaf $p |- ( ph -> H : ( B X. B ) --> ~P ( ( B X. B ) X. _V ) ) $=
      ( vx cxp cv csn chom cfv cvv cpw eqid homafval wcel wa wss adantl sylancl
      snssi ssv xpss12 vsnex fvex xpex elpw sylibr fmpt3d ) AHBBIZHJZKZUMCLMZMZ
      IZULNIZOZDAHBCDUOEFGUOPQAUMULRZSZUQURTZUQUSRVAUNULTZUPNTVBUTVCAUMULUCUAUP
      UDUNULUPNUEUBUQURUNUPHUFUMUOUGUHUIUJUK $.

    homaval.j $e |- J = ( Hom ` C ) $.
    homaval.x $e |- ( ph -> X e. B ) $.
    homaval.y $e |- ( ph -> Y e. B ) $.
    $( Value of the disjointified hom-set function.  (Contributed by Mario
       Carneiro, 11-Jan-2017.) $)
    homaval $p |- ( ph -> ( X H Y ) = ( { <. X , Y >. } X. ( X J Y ) ) ) $=
      ( vz co cfv csn cxp df-ov cvv cop cv homafval wceq wa simpr sneqd eqtr4di
      fveq2d xpeq12d opelxpd wcel snex ovex xpex a1i fvmptd eqtrid ) AFGDOFGUAZ
      DPUSQZFGEOZRZFGDSANUSNUBZQZVCEPZRVBBBRDTANBCDEHIJKUCAVCUSUDZUEZVDUTVEVAVG
      VCUSAVFUFZUGVGVEUSEPVAVGVCUSEVHUIFGESUHUJAFGBBLMUKVBTULAUTVAUSUMFGEUNUOUP
      UQUR $.

    $( Value of the disjointified hom-set function.  (Contributed by Mario
       Carneiro, 11-Jan-2017.) $)
    elhoma $p |- ( ph -> ( Z ( X H Y ) F <->
      ( Z = <. X , Y >. /\ F e. ( X J Y ) ) ) ) $=
      ( co wbr cop wcel wa csn wceq homaval breqd brxp opex elsn2 anbi1i bitrdi
      cxp bitri ) AIDGHEPZQIDGHRZUAZGHFPZUJZQZIUMUBZDUOSZTZAULUPIDABCEFGHJKLMNO
      UCUDUQIUNSZUSTUTIDUNUOUEVAURUSIUMGHUFUGUHUKUI $.

    elhomai.f $e |- ( ph -> F e. ( X J Y ) ) $.
    $( Produce an arrow from a morphism.  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)
    elhomai $p |- ( ph -> <. X , Y >. ( X H Y ) F ) $=
      ( cop co wbr wceq wcel eqidd elhoma mpbir2and ) AGHPZDGHEQRUDUDSDGHFQTAUD
      UAOABCDEFGHUDIJKLMNUBUC $.

    $( Produce an arrow from a morphism.  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)
    elhomai2 $p |- ( ph -> <. X , Y , F >. e. ( X H Y ) ) $=
      ( cotp cop co df-ot wbr wcel elhomai df-br sylib eqeltrid ) AGHDPGHQZDQZG
      HERZGHDSAUFDUHTUGUHUAABCDEFGHIJKLMNOUBUFDUHUCUDUE $.
  $}

  ${
    $d f H $.  $d f X $.  $d f Y $.
    homahom.h $e |- H = ( HomA ` C ) $.
    ${
      homarcl2.b $e |- B = ( Base ` C ) $.
      $( Reverse closure for the domain and codomain of an arrow.  (Contributed
         by Mario Carneiro, 11-Jan-2017.) $)
      homarcl2 $p |- ( F e. ( X H Y ) -> ( X e. B /\ Y e. B ) ) $=
        ( co wcel cop cxp wa cdm cfv elfvdm df-ov eleq2s cvv cpw homarcl opelxp
        homaf fdmd eleqtrd sylib ) CEFDIZJZEFKZAALZJEAJFAJMUHUIDNZUJUIUKJCUIDOU
        GCUIDPEFDQRUHUJUJSLTDUHABDGHBCDEFGUAUCUDUEEFAAUBUF $.
    $}

    $( An arrow is an ordered pair.  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)
    homarel $p |- Rel ( X H Y ) $=
      ( vf co wrel cvv cxp wss cv wcel cbs cfv xpss cpw eqid homarcl homaf
      homarcl2 simpld simprd fovcdmd elelpwi mpdan sselid ssriv df-rel mpbir )
      CDBGZHUKIIJZKFUKULFLZUKMZANOZUOJZIJZULUMUPIPUNUKUQQZMUMUQMUNCDURUOUOBUNUO
      ABEUORZAUMBCDESTUNCUOMZDUOMZUOAUMBCDEUSUAZUBUNUTVAVBUCUDUMUKUQUEUFUGUHUKU
      IUJ $.

    $( The first component of an arrow is the ordered pair of domain and
       codomain.  (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    homa1 $p |- ( Z ( X H Y ) F -> Z = <. X , Y >. ) $=
      ( co wbr cop wceq chom cfv wcel wa wb df-br cbs eqid simpld simprd elhoma
      homarcl homarcl2 sylbi ibi ) FBDECHZIZFDEJKZBDEALMZHNZUHUIUKOZUHFBJZUGNZU
      HULPFBUGQUNARMZABCUJDEFGUOSZAUMCDEGUCUJSUNDUONZEUONZUOAUMCDEGUPUDZTUNUQUR
      USUAUBUEUFT $.

    ${
      homahom.j $e |- J = ( Hom ` C ) $.
      $( The second component of an arrow is the corresponding morphism
         (without the domain/codomain tag).  (Contributed by Mario Carneiro,
         11-Jan-2017.) $)
      homahom2 $p |- ( Z ( X H Y ) F -> F e. ( X J Y ) ) $=
        ( co wbr cop wceq wcel wa wb df-br cbs cfv simprd eqid homarcl homarcl2
        simpld elhoma sylbi ibi ) GBEFCJZKZGEFLMZBEFDJNZUIUJUKOZUIGBLZUHNZUIULP
        GBUHQUNARSZABCDEFGHUOUAZAUMCEFHUBIUNEUONZFUONZUOAUMCEFHUPUCZUDUNUQURUST
        UEUFUGT $.

      $( The second component of an arrow is the corresponding morphism
         (without the domain/codomain tag).  (Contributed by Mario Carneiro,
         11-Jan-2017.) $)
      homahom $p |- ( F e. ( X H Y ) -> ( 2nd ` F ) e. ( X J Y ) ) $=
        ( co wcel c1st cfv c2nd wbr wrel homarel 1st2ndbr mpan homahom2 syl ) B
        EFCIZJZBKLZBMLZUANZUDEFDIJUAOUBUEACEFGPBUAQRAUDCDEFUCGHST $.
    $}

    $( The domain of an arrow with known domain and codomain.  (Contributed by
       Mario Carneiro, 11-Jan-2017.) $)
    homadm $p |- ( F e. ( X H Y ) -> ( domA ` F ) = X ) $=
      ( co wcel cdoma cfv c1st cop ccom df-doma fveq1i cvv wf wceq wfo syl elex
      fo1st fof ax-mp fvco3 sylancr eqtrid c2nd wbr wrel homarel 1st2ndbr homa1
      mpan fveq2d cbs wa eqid homarcl2 op1stg 3eqtrd ) BDECGZHZBIJZBKJZKJZDELZK
      JZDVCVDBKKMZJZVFBIVINOVCPPKQZBPHVJVFRPPKSVKUBPPKUCUDBVBUAPPBKKUEUFUGVCVEV
      GKVCVEBUHJZVBUIZVEVGRVBUJVCVMACDEFUKBVBULUNAVLCDEVEFUMTUOVCDAUPJZHEVNHUQV
      HDRVNABCDEFVNURUSDEVNVNUTTVA $.

    $( The codomain of an arrow with known domain and codomain.  (Contributed
       by Mario Carneiro, 11-Jan-2017.) $)
    homacd $p |- ( F e. ( X H Y ) -> ( codA ` F ) = Y ) $=
      ( co wcel ccoda cfv c1st c2nd cop ccom df-coda fveq1i cvv wf wceq syl wfo
      fo1st fof ax-mp elex fvco3 sylancr eqtrid wbr wrel homarel 1st2ndbr homa1
      mpan fveq2d cbs wa eqid homarcl2 op2ndg 3eqtrd ) BDECGZHZBIJZBKJZLJZDEMZL
      JZEVCVDBLKNZJZVFBIVIOPVCQQKRZBQHVJVFSQQKUAVKUBQQKUCUDBVBUEQQBLKUFUGUHVCVE
      VGLVCVEBLJZVBUIZVEVGSVBUJVCVMACDEFUKBVBULUNAVLCDEVEFUMTUOVCDAUPJZHEVNHUQV
      HESVNABCDEFVNURUSDEVNVNUTTVA $.

    $( Decompose an arrow into domain, codomain, and morphism.  (Contributed by
       Mario Carneiro, 11-Jan-2017.) $)
    homadmcd $p |- ( F e. ( X H Y ) -> F = <. X , Y , ( 2nd ` F ) >. ) $=
      ( wcel cop c2nd cfv cotp c1st wrel wceq homarel 1st2nd mpan wbr 1st2ndbr
      co homa1 syl opeq1d eqtrd df-ot eqtr4di ) BDECTZGZBDEHZBIJZHZDEUJKUHBBLJZ
      UJHZUKUGMZUHBUMNACDEFOZBUGPQUHULUIUJUHULUJUGRZULUINUNUHUPUOBUGSQAUJCDEULF
      UAUBUCUDDEUJUEUF $.
  $}

  ${
    $d c x $.  $d c C $.  $d c H $.
    arwval.a $e |- A = ( Arrow ` C ) $.
    arwval.h $e |- H = ( HomA ` C ) $.
    $( The set of arrows is the union of all the disjointified hom-sets.
       (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    arwval $p |- A = U. ran H $=
      ( vc vx carw cfv crn cuni ccat wceq cv choma rneqd unieqd c0 fvmptndm cxp
      wcel fveq2 eqtr4di df-arw fvexi rnex uniex fvmpt wn cbs chom cmpt df-homa
      csn eqtrid rn0 eqtrdi uni0 eqtr4d pm2.61i eqtri ) ABHIZCJZKZDBLUAZVBVDMFB
      FNZOIZJZKZVDLHVFBMZVHVCVJVGCVJVGBOIZCVFBOUBEUCPQFUDZVCCCBOEUEUFUGUHVEUIZV
      BRVDFLVIHBVLSVMVDRKRVMVCRVMVCRJRVMCRVMCVKREFLGVFUJIZVNTGNZUNVOVFUKIITULOB
      GFUMSUOPUPUQQURUQUSUTVA $.
  $}

  ${
    $d x A $.  $d x B $.  $d x y z C $.  $d x y z F $.  $d x y z H $.
    arwrcl.a $e |- A = ( Arrow ` C ) $.
    $( The first component of an arrow is the ordered pair of domain and
       codomain.  (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    arwrcl $p |- ( F e. A -> C e. Cat ) $=
      ( vc wcel carw cdm ccat cv choma cfv crn cuni df-arw elfvdm eleq2s sselid
      dmmptss ) CAFGHZIBEIEJKLMNGEOSBTFCBGLACBGPDQR $.

    ${
      arwhoma.h $e |- H = ( HomA ` C ) $.
      $( An arrow is contained in the hom-set corresponding to its domain and
         codomain.  (Contributed by Mario Carneiro, 11-Jan-2017.) $)
      arwhoma $p |- ( F e. A -> F e. ( ( domA ` F ) H ( codA ` F ) ) ) $=
        ( vx vy vz wcel cv co cbs cfv wrex cdoma ccoda cxp crn rexlimivw arwval
        cuni eleq2i biimpi cvv cpw wf wfn wb eqid arwrcl homaf ffn fnunirn 3syl
        mpbid cop wceq fveq2 df-ov eqtr4di eleq2d rexxp sylib id homadm oveq12d
        homacd eleqtrrd syl ) CAJZCGKZHKZDLZJZHBMNZOZGVPOZCCPNZCQNZDLZJZVKCIKZD
        NZJZIVPVPRZOZVRVKCDSUBZJZWGVKWIAWHCABDEFUAUCUDVKWFWFUERUFZDUGDWFUHWIWGU
        IVKVPBDFVPUJABCEUKULWFWJDUMICDWFUNUOUPWEVOIGHVPVPWCVLVMUQZURZWDVNCWLWDW
        KDNVNWCWKDUSVLVMDUTVAVBVCVDVQWBGVPVOWBHVPVOCVNWAVOVEVOVSVLVTVMDBCDVLVMF
        VFBCDVLVMFVHVGVITTVJ $.

      $( A hom-set is a subset of the collection of all arrows.  (Contributed
         by Mario Carneiro, 11-Jan-2017.) $)
      homarw $p |- ( X H Y ) C_ A $=
        ( co crn cuni ovssunirn arwval sseqtrri ) DECHCIJACDEKABCFGLM $.
    $}

    ${
      arwdm.b $e |- B = ( Base ` C ) $.
      $( The domain of an arrow is an object.  (Contributed by Mario Carneiro,
         11-Jan-2017.) $)
      arwdm $p |- ( F e. A -> ( domA ` F ) e. B ) $=
        ( wcel cdoma cfv ccoda choma co wa eqid arwhoma homarcl2 syl simpld ) D
        AGZDHIZBGZDJIZBGZSDTUBCKIZLGUAUCMACDUDEUDNZOBCDUDTUBUEFPQR $.

      $( The codomain of an arrow is an object.  (Contributed by Mario
         Carneiro, 11-Jan-2017.) $)
      arwcd $p |- ( F e. A -> ( codA ` F ) e. B ) $=
        ( wcel cdoma cfv ccoda choma co wa eqid arwhoma homarcl2 syl simprd ) D
        AGZDHIZBGZDJIZBGZSDTUBCKIZLGUAUCMACDUDEUDNZOBCDUDTUBUEFPQR $.

      $( The domain function is a function from arrows to objects.
         (Contributed by Mario Carneiro, 11-Jan-2017.) $)
      dmaf $p |- ( domA |` A ) : A --> B $=
        ( vx cdoma cres wf wfn cv cfv wcel wral cvv wss c1st fo1st ax-mp mp2an
        ccom wfo fof fnfco df-doma fneq1i mpbir ssv fnssres fvres arwdm eqeltrd
        fofn rgen ffnfv mpbir2an ) ABGAHZIUQAJZFKZUQLZBMZFANGOJZAOPURVBQQUAZOJZ
        QOJZOOQIZVDOOQUBZVEROOQUMSVGVFROOQUCSOOQQUDTOGVCUEUFUGAUHOAGUITVAFAUSAM
        UTUSGLBUSAGUJABCUSDEUKULUNFABUQUOUP $.

      $( The codomain function is a function from arrows to objects.
         (Contributed by Mario Carneiro, 11-Jan-2017.) $)
      cdaf $p |- ( codA |` A ) : A --> B $=
        ( vx ccoda cres wf wfn cv cfv wcel wral cvv c2nd c1st wfo ax-mp mp2an
        wss ccom fo2nd fo1st fof fnfco df-coda fneq1i mpbir fnssres fvres arwcd
        fofn ssv eqeltrd rgen ffnfv mpbir2an ) ABGAHZIUSAJZFKZUSLZBMZFANGOJZAOU
        AUTVDPQUBZOJZPOJZOOQIZVFOOPRVGUCOOPUMSOOQRVHUDOOQUESOOPQUFTOGVEUGUHUIAU
        NOAGUJTVCFAVAAMVBVAGLBVAAGUKABCVADEULUOUPFABUSUQUR $.
    $}

    ${
      arwhom.j $e |- J = ( Hom ` C ) $.
      $( The second component of an arrow is the corresponding morphism
         (without the domain/codomain tag).  (Contributed by Mario Carneiro,
         11-Jan-2017.) $)
      arwhom $p |- ( F e. A ->
        ( 2nd ` F ) e. ( ( domA ` F ) J ( codA ` F ) ) ) $=
        ( wcel cdoma cfv ccoda choma co c2nd eqid arwhoma homahom syl ) CAGCCHI
        ZCJIZBKIZLGCMIRSDLGABCTETNZOBCTDRSUAFPQ $.
    $}

    $( Decompose an arrow into domain, codomain, and morphism.  (Contributed by
       Mario Carneiro, 11-Jan-2017.) $)
    arwdmcd $p |- ( F e. A -> F =
      <. ( domA ` F ) , ( codA ` F ) , ( 2nd ` F ) >. ) $=
      ( wcel cdoma cfv ccoda choma co c2nd cotp wceq eqid arwhoma homadmcd syl
      ) CAECCFGZCHGZBIGZJECRSCKGLMABCTDTNZOBCTRSUAPQ $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Identity and composition for arrows
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c IdA $.
  $c compA $.

  $( Extend class notation to include identity for arrows. $)
  cida $a class IdA $.

  $( Extend class notation to include composition for arrows. $)
  ccoa $a class compA $.

  ${
    $d c f g h x $.
    $( Definition of the identity arrow, which is just the identity morphism
       tagged with its domain and codomain.  (Contributed by FL, 26-Oct-2007.)
       (Revised by Mario Carneiro, 11-Jan-2017.) $)
    df-ida $a |- IdA = ( c e. Cat |-> ( x e. ( Base ` c ) |->
      <. x , x , ( ( Id ` c ) ` x ) >. ) ) $.

    $( Definition of the composition of arrows.  Since arrows are tagged with
       domain and codomain, this does not need to be a quinary operation like
       the regular composition in a category ` comp ` .  Instead, it is a
       partial binary operation on arrows, which is defined when the domain of
       the first arrow matches the codomain of the second.  (Contributed by
       Mario Carneiro, 11-Jan-2017.) $)
    df-coa $a |- compA = ( c e. Cat |-> ( g e. ( Arrow ` c ) , f e.
      { h e. ( Arrow ` c ) | ( codA ` h ) = ( domA ` g ) } |->
      <. ( domA ` f ) , ( codA ` g ) , ( ( 2nd ` g ) ( <. ( domA ` f ) ,
        ( domA ` g ) >. ( comp ` c ) ( codA ` g ) ) ( 2nd ` f ) ) >. ) ) $.
  $}

  ${
    $d c x .1. $.  $d x A $.  $d c x B $.  $d c x C $.  $d x I $.  $d x ph $.
    $d x X $.
    idafval.i $e |- I = ( IdA ` C ) $.
    idafval.b $e |- B = ( Base ` C ) $.
    idafval.c $e |- ( ph -> C e. Cat ) $.
    ${
      idafval.1 $e |- .1. = ( Id ` C ) $.
      $( Value of the identity arrow function.  (Contributed by Mario Carneiro,
         11-Jan-2017.) $)
      idafval $p |- ( ph -> I = ( x e. B |-> <. x , x , ( .1. ` x ) >. ) ) $=
        ( vc cida cfv cv cotp cmpt ccat wceq cbs ccid wcel fveq2 eqtr4di fveq1d
        oteq3d mpteq12dv df-ida mptfvmpt syl eqtrid ) AFDLMZBCBNZULULEMZOZPZGAD
        QUAUKUORIBKUNSLBKNZSMZULULULUPTMZMZOZPCQDDUPDRZBUQUTCUNVAUQDSMCUPDSUBHU
        CVAUSUMULULVAULUREVAURDTMEUPDTUBJUCUDUEUFBKUGHUHUIUJ $.

      idaval.x $e |- ( ph -> X e. B ) $.
      $( Value of the identity arrow function.  (Contributed by Mario Carneiro,
         11-Jan-2017.) $)
      idaval $p |- ( ph -> ( I ` X ) = <. X , X , ( .1. ` X ) >. ) $=
        ( vx cv cfv cotp cvv idafval wceq wa simpr fveq2d oteq123d wcel fvmptd
        otex a1i ) ALFLMZUGUGDNZOFFFDNZOZBEPALBCDEGHIJQAUGFRZSZUGFUGFUHUIAUKTZU
        MULUGFDUMUAUBKUJPUCAFFUIUEUFUD $.

      $( Morphism part of the identity arrow.  (Contributed by Mario Carneiro,
         11-Jan-2017.) $)
      ida2 $p |- ( ph -> ( 2nd ` ( I ` X ) ) = ( .1. ` X ) ) $=
        ( cfv c2nd cotp idaval fveq2d cvv wcel wceq fvex ot3rdg ax-mp eqtrdi )
        AFELZMLFFFDLZNZMLZUEAUDUFMABCDEFGHIJKOPUEQRUGUESFDTFFUEQUAUBUC $.
    $}

    ${
      idahom.x $e |- ( ph -> X e. B ) $.
      ${
        idahom.h $e |- H = ( HomA ` C ) $.
        $( Domain and codomain of the identity arrow.  (Contributed by Mario
           Carneiro, 11-Jan-2017.) $)
        idahom $p |- ( ph -> ( I ` X ) e. ( X H X ) ) $=
          ( cfv ccid cotp co eqid idaval chom catidcl elhomai2 eqeltrd ) AFELFF
          FCMLZLZNFFDOABCUBEFGHIUBPZJQABCUCDCRLZFFKHIUEPZJJABCUBUEFHUFUDIJSTUA
          $.
      $}

      $( Domain of the identity arrow.  (Contributed by Mario Carneiro,
         11-Jan-2017.) $)
      idadm $p |- ( ph -> ( domA ` ( I ` X ) ) = X ) $=
        ( cfv choma co wcel cdoma wceq eqid idahom homadm syl ) AEDJZEECKJZLMTN
        JEOABCUADEFGHIUAPZQCTUAEEUBRS $.

      $( Codomain of the identity arrow.  (Contributed by Mario Carneiro,
         11-Jan-2017.) $)
      idacd $p |- ( ph -> ( codA ` ( I ` X ) ) = X ) $=
        ( cfv choma co wcel ccoda wceq eqid idahom homacd syl ) AEDJZEECKJZLMTN
        JEOABCUADEFGHIUAPZQCTUAEEUBRS $.
    $}

    idaf.a $e |- A = ( Arrow ` C ) $.
    $( The identity arrow function is a function from objects to arrows.
       (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    idaf $p |- ( ph -> I : B --> A ) $=
      ( vx cv ccid cfv cotp cvv wcel wa otex a1i eqid idafval choma homarw ccat
      co adantr simpr idahom sselid fmpt2d ) AJJCJKZUKUKDLMZMZNZBEOUNOPAUKCPZQZ
      UKUKUMRSAJCDULEFGHULTUAUPUKUKDUBMZUEBUKEMBDUQUKUKIUQTZUCUPCDUQEUKFGADUDPU
      OHUFAUOUGURUHUIUJ $.
  $}

  ${
    $d c f g h A $.  $d c f g h C $.  $d g h F $.  $d g h G $.  $d c .xb $.
    coafval.o $e |- .x. = ( compA ` C ) $.
    coafval.a $e |- A = ( Arrow ` C ) $.
    ${
      coafval.x $e |- .xb = ( comp ` C ) $.
      $( The value of the composition of arrows.  (Contributed by Mario
         Carneiro, 11-Jan-2017.) $)
      coafval $p |- .x. = ( g e. A , f e.
        { h e. A | ( codA ` h ) = ( domA ` g ) } |->
        <. ( domA ` f ) , ( codA ` g ) , ( ( 2nd ` g ) ( <. ( domA ` f ) ,
          ( domA ` g ) >. .xb ( codA ` g ) ) ( 2nd ` f ) ) >. ) $=
        ( vc ccoa cfv cv wceq co cmpo ccat carw c0 ccoda crab c2nd cop cotp cco
        cdoma fveq2 eqtr4di rabeqdv oveqd oteq3d df-coa fvexi rabex mpoex fvmpt
        wcel mpoeq123dv fvmptndm arwrcl con3i eq0rdv mpo0 eqtrdi eqtr4d pm2.61i
        wn eqidd eqtri ) DBLMZFEAGNUAMFNZUGMZOZGAUBZENZUGMZVLUAMZVLUCMZVPUCMZVQ
        VMUDZVRCPZPZUEZQZHBRURZVKWEOKBFEKNZSMZVNGWHUBZVQVRVSVTWAVRWGUFMZPZPZUEZ
        QZWERLWGBOZFEWHWIWMAVOWDWOWHBSMAWGBSUHIUIZWOVNGWHAWPUJWOWLWCVQVRWOWKWBV
        SVTWOWJCWAVRWOWJBUFMCWGBUFUHJUIUKUKULUSEFGKUMZFEAVOWDABSIUNZVNGAWRUOUPU
        QWFVHZVKTWEKRWNLBWQUTWSWEFETVOWDQTWSFEAVOWDTVOWDWSEAVPAURWFABVPIVAVBVCW
        SVOVIWSWDVIUSFEVOWDVDVEVFVGVJ $.
    $}

    $( A pair ` <. G , F >. ` is in the domain of the arrow composition, if the
       domain of ` G ` equals the codomain of ` F ` .  (In this case we say
       ` G ` and ` F ` are composable.)  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)
    eldmcoa $p |- ( G dom .x. F <->
      ( F e. A /\ G e. A /\ ( codA ` F ) = ( domA ` G ) ) ) $=
      ( vg vh vf cop wcel cv ccoda cfv cdoma wceq crab cvv wa cdm wbr csn df-br
      cxp ciun w3a c2nd cco co cotp wral wf otex rgen2w eqid coafval fmpox mpbi
      eleq2i fveq2 eqeq2d rabbidv opeliunxp2 fveqeq2 elrab anbi2i 3anass bitr4i
      fdmi an12 3bitri ) EDCUAZUBEDKZVMLVNHAHMZUCIMZNOZVOPOZQZIARZUEUFZLZDALZEA
      LZDNOEPOZQZUGZEDVMUDVMWAVNWASCJMZPOZVONOZVOUHOWHUHOWIVRKWJBUIOZUJUJZUKZSL
      ZJVTULHAULWASCUMWNHJAVTWIWJWLUNUOHJAVTWMSCABWKCJHIFGWKUPUQURUSVJUTWBWDDVQ
      WEQZIARZLZTWDWCWFTZTZWGHAVTEDWPVOEQZVSWOIAWTVRWEVQVOEPVAVBVCVDWQWRWDWOWFI
      DAVPDWENVEVFVGWSWCWDWFTTWGWDWCWFVKWCWDWFVHVIVLVL $.

    $( The domain of composition is a collection of pairs of arrows.
       (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    dmcoass $p |- dom .x. C_ ( A X. A ) $=
      ( vg vh vf cdm cv csn ccoda cfv cdoma wceq crab cxp c2nd co wss ciun cotp
      cop eqid coafval dmmpossx iunss snssi ssrab2 xpss12 sylancl mprgbir sstri
      cco wcel ) CIFAFJZKZGJLMUPNMZOZGAPZQZUAZAAQZFHAUTHJZNMZUPLMZUPRMVDRMVEURU
      CVFBUNMZSSUBCABVGCHFGDEVGUDUEUFVBVCTVAVCTZFAFAVAVCUGUPAUOUQATUTATVHUPAUHU
      SGAUIUQAUTAUJUKULUM $.
  $}

  ${
    $d f g G $.  $d f g ph $.  $d f g X $.  $d f g Y $.  $d f g h C $.
    $d f g h F $.  $d f g .xb $.  $d f g Z $.
    homdmcoa.o $e |- .x. = ( compA ` C ) $.
    homdmcoa.h $e |- H = ( HomA ` C ) $.
    homdmcoa.f $e |- ( ph -> F e. ( X H Y ) ) $.
    homdmcoa.g $e |- ( ph -> G e. ( Y H Z ) ) $.
    $( If ` F : X --> Y ` and ` G : Y --> Z ` , then ` G ` and ` F ` are
       composable.  (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    homdmcoa $p |- ( ph -> G dom .x. F ) $=
      ( cfv wcel wceq co homarw sselid syl carw ccoda cdoma cdm wbr eqid homacd
      homadm eqtr4d eldmcoa syl3anbrc ) ADBUANZOEULODUBNZEUCNZPEDCUDUEAGHFQZULD
      ULBFGHULUFZKRLSAHIFQZULEULBFHIUPKRMSAUMHUNADUOOUMHPLBDFGHKUGTAEUQOUNHPMBE
      FHIKUHTUIULBCDEJUPUJUK $.

    ${
      coaval.x $e |- .xb = ( comp ` C ) $.
      $( Value of composition for composable arrows.  (Contributed by Mario
         Carneiro, 11-Jan-2017.) $)
      coaval $p |- ( ph -> ( G .x. F ) =
        <. X , Z , ( ( 2nd ` G ) ( <. X , Y >. .xb Z ) ( 2nd ` F ) ) >. ) $=
        ( cfv ccoda cdoma wceq co vg vf vh carw cv crab c2nd cop cotp cmpo eqid
        coafval homarw sselid wa fveqeq2 wcel adantr homacd simpr fveq2d homadm
        cvv syl eqtrd eqtr4d elrabd a1i simprr adantrr opeq12d oveq12d oveq123d
        otex simprl oteq123d ovmpodv2 mpi ) ADUAUBBUDPZUCUEZQPUAUEZRPZSZUCVSUFZ
        UBUEZRPZWAQPZWAUGPZWEUGPZWFWBUHZWGCTZTZUIZUJSFEDTHJFUGPZEUGPZHIUHZJCTZT
        ZUIZSVSBCDUBUAUCKVSUKZOULAUAUBFEVSWDWMWSDVCAIJGTZVSFVSBGIJWTLUMNUNAWAFS
        ZUOZWCEQPZWBSUCEVSVTEWBQUPXCHIGTZVSEVSBGHIWTLUMAEXEUQZXBMURZUNXCXDIWBXC
        XFXDISXGBEGHILUSVDXCWBFRPZIXCWAFRAXBUTZVAXCFXAUQZXHISAXJXBNURZBFGIJLVBV
        DVEZVFVGWMVCUQAXBWEESZUOUOZWFWGWLVNVHXNWFHWGJWLWRXNWFERPZHXNWEERAXBXMVI
        ZVAAXBXOHSZXMXCXFXQXGBEGHILVBVDVJVEZAXBWGJSXMXCWGFQPZJXCWAFQXIVAXCXJXSJ
        SXKBFGIJLUSVDVEVJZXNWHWNWIWOWKWQXNWJWPWGJCXNWFHWBIXRAXBWBISXMXLVJVKXTVL
        XNWAFUGAXBXMVOVAXNWEEUGXPVAVMVPVQVR $.

      $( The morphism part of arrow composition.  (Contributed by Mario
         Carneiro, 11-Jan-2017.) $)
      coa2 $p |- ( ph -> ( 2nd ` ( G .x. F ) ) =
        ( ( 2nd ` G ) ( <. X , Y >. .xb Z ) ( 2nd ` F ) ) ) $=
        ( co c2nd cfv cop cvv cotp coaval fveq2d wcel wceq ot3rdg ax-mp eqtrdi
        ovex ) AFEDPZQRHJFQRZEQRZHISJCPZPZUAZQRZUNAUJUOQABCDEFGHIJKLMNOUBUCUNTU
        DUPUNUEUKULUMUIHJUNTUFUGUH $.
    $}

    $( The composition of two composable arrows is an arrow.  (Contributed by
       Mario Carneiro, 11-Jan-2017.) $)
    coahom $p |- ( ph -> ( G .x. F ) e. ( X H Z ) ) $=
      ( co c2nd cfv eqid wcel syl wa cop cco cotp coaval cbs chom ccat homarcl2
      homarcl simpld simprd homahom catcocl elhomai2 eqeltrd ) AEDCNGIEOPZDOPZG
      HUAIBUBPZNNZUCGIFNABURCDEFGHIJKLMURQZUDABUEPZBUSFBUFPZGIKVAQZADGHFNRZBUGR
      LBDFGHKUISZVBQZAGVARZHVARZAVDVGVHTLVABDFGHKVCUHSZUJZAVHIVARZAEHIFNRZVHVKT
      MVABEFHIKVCUHSUKZAVABURUQUPVBGHIVCVFUTVEVJAVGVHVIUKVMAVDUQGHVBNRLBDFVBGHK
      VFULSAVLUPHIVBNRMBEFVBHIKVFULSUMUNUO $.
  $}

  ${
    $d f g h z A $.  $d f g h C $.  $d z .x. $.
    coapm.o $e |- .x. = ( compA ` C ) $.
    coapm.a $e |- A = ( Arrow ` C ) $.
    $( Composition of arrows is a partial binary operation on arrows.
       (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    coapm $p |- .x. e. ( A ^pm ( A X. A ) ) $=
      ( vz vg vf vh co wcel cv cfv ccoda cdoma wceq c2nd cop eqid syl wral wfun
      cxp cpm cdm wf wss wfn crab cco cotp coafval mpofun funfn mpbi c1st sseli
      dmcoass 1st2nd2 fveq2d df-ov eqtr4di choma homarw wbr w3a eqeltrrd sylibr
      id df-br eldmcoa sylib simp1d arwhoma simp3d oveq2d eleqtrd simp2d coahom
      sselid eqeltrd rgen ffnfv mpbir2an carw fvexi xpex elpm2 ) CAAAUCZUDJKCUE
      ZACUFZWJWIUGWKCWJUHZFLZCMZAKZFWJUACUBWLGHAILNMGLZOMZPIAUIHLZOMZWPNMZWPQMW
      RQMWSWQRWTBUJMZJJUKCABXACHGIDEXASULUMCUNUOWOFWJWMWJKZWNWMUPMZWMQMZCJZAXBW
      NXCXDRZCMXEXBWMXFCXBWMWIKWMXFPWJWIWMABCDEURZUQWMAAUSTZUTXCXDCVAVBXBXDOMZX
      CNMZBVCMZJAXEABXKXIXJEXKSZVDXBBCXDXCXKXIXCOMZXJDXLXBXDXIXDNMZXKJZXIXMXKJX
      BXDAKZXDXOKXBXPXCAKZXNXMPZXBXCXDWJVEZXPXQXRVFXBXFWJKXSXBWMXFWJXHXBVIVGXCX
      DWJVJVHABCXDXCDEVKVLZVMABXDXKEXLVNTXBXNXMXIXKXBXPXQXRXTVOVPVQXBXQXCXMXJXK
      JKXBXPXQXRXTVRABXCXKEXLVNTVSVTWAWBFWJACWCWDXGAWICABWEEWFZAAYAYAWGWHWD $.
  $}

  ${
    arwlid.h $e |- H = ( HomA ` C ) $.
    arwlid.o $e |- .x. = ( compA ` C ) $.
    arwlid.a $e |- .1. = ( IdA ` C ) $.
    arwlid.f $e |- ( ph -> F e. ( X H Y ) ) $.
    $( Left identity of a category using arrow notation.  (Contributed by Mario
       Carneiro, 11-Jan-2017.) $)
    arwlid $p |- ( ph -> ( ( .1. ` Y ) .x. F ) = F ) $=
      ( cfv c2nd cop co cotp eqid wcel syl cco ccid cbs homarcl homarcl2 simprd
      ccat wa ida2 oveq1d chom simpld homahom catlid eqtrd oteq3d idahom coaval
      wceq homadmcd 3eqtr4d ) AGHHDMZNMZENMZGHOHBUAMZPZPZQGHVDQZVBECPEAVGVDGHAV
      GHBUBMZMZVDVFPVDAVCVJVDVFABUCMZBVIDHKVKRZAEGHFPSZBUGSLBEFGHIUDTZVIRZAGVKS
      ZHVKSZAVMVPVQUHLVKBEFGHIVLUETZUFZUIUJAVKBVEVIVDBUKMZGHVLVTRZVOVNAVPVQVRUL
      VERZVSAVMVDGHVTPSLBEFVTGHIWAUMTUNUOUPABVECEVBFGHHJILAVKBFDHKVLVNVSIUQWBUR
      AVMEVHUSLBEFGHIUTTVA $.

    $( Right identity of a category using arrow notation.  (Contributed by
       Mario Carneiro, 11-Jan-2017.) $)
    arwrid $p |- ( ph -> ( F .x. ( .1. ` X ) ) = F ) $=
      ( c2nd cfv cop co cotp eqid wcel syl cco ccid cbs homarcl homarcl2 simpld
      ccat wa ida2 oveq2d chom simprd homahom catrid eqtrd oteq3d idahom coaval
      wceq homadmcd 3eqtr4d ) AGHEMNZGDNZMNZGGOHBUANZPZPZQGHVBQZEVCCPEAVGVBGHAV
      GVBGBUBNZNZVFPVBAVDVJVBVFABUCNZBVIDGKVKRZAEGHFPSZBUGSLBEFGHIUDTZVIRZAGVKS
      ZHVKSZAVMVPVQUHLVKBEFGHIVLUETZUFZUIUJAVKBVEVIVBBUKNZGHVLVTRZVOVNVSVERZAVP
      VQVRULAVMVBGHVTPSLBEFVTGHIWAUMTUNUOUPABVECVCEFGGHJIAVKBFDGKVLVNVSIUQLWBUR
      AVMEVHUSLBEFGHIUTTVA $.

    arwass.g $e |- ( ph -> G e. ( Y H Z ) ) $.
    arwass.k $e |- ( ph -> K e. ( Z H W ) ) $.
    $( Associativity of composition in a category using arrow notation.
       (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    arwass $p |- ( ph -> ( ( K .x. G ) .x. F ) = ( K .x. ( G .x. F ) ) ) $=
      ( co wcel c2nd cfv cop cco cotp cbs chom eqid homarcl syl homarcl2 simpld
      ccat wa simprd homahom catass oveq1d oveq2d 3eqtr4d oteq3d coahom coaval
      coa2 ) AJIHFCSZUAUBZEUAUBZJKUCZIBUDUBZSZSZUEJIHUAUBZFECSZUAUBZJLUCIVISZSZ
      UEVEECSHVMCSAVKVPJIAVLFUAUBZKLUCIVISSZVGVJSVLVQVGVHLVISSZVOSVKVPABUFUBZBV
      IVGVQBUGUBZVLIJKLVTUHZWAUHZVIUHZAEJKGSTZBUMTPBEGJKMUIUJAJVTTZKVTTZAWEWFWG
      UNPVTBEGJKMWBUKUJZULAWFWGWHUOALVTTZIVTTZAHLIGSTZWIWJUNRVTBHGLIMWBUKUJZULA
      WEVGJKWASTPBEGWAJKMWCUPUJAFKLGSTVQKLWASTQBFGWAKLMWCUPUJAWIWJWLUOAWKVLLIWA
      STRBHGWALIMWCUPUJUQAVFVRVGVJABVICFHGKLINMQRWDVDURAVNVSVLVOABVICEFGJKLNMPQ
      WDVDUSUTVAABVICEVEGJKINMPABCFHGKLINMQRVBWDVCABVICVMHGJLINMABCEFGJKLNMPQVB
      RWDVCUT $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Examples of categories
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The category of sets
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c SetCat $.

  $( Extend class notation to include the category Set. $)
  csetc $a class SetCat $.

  ${
    $d f g u v x y z $.
    $( Definition of the category Set, relativized to a subset ` u ` .  Example
       3.3(1) of [Adamek] p. 22.  This is the category of all sets in ` u ` and
       functions between these sets.  Generally, we will take ` u ` to be a
       weak universe or Grothendieck universe, because these sets have closure
       properties as good as the real thing.  (Contributed by FL, 8-Nov-2013.)
       (Revised by Mario Carneiro, 3-Jan-2017.) $)
    df-setc $a |- SetCat = ( u e. _V |-> { <. ( Base ` ndx ) , u >. ,
     <. ( Hom ` ndx ) , ( x e. u , y e. u |-> ( y ^m x ) ) >. ,
     <. ( comp ` ndx ) , ( v e. ( u X. u ) , z e. u |->
      ( g e. ( z ^m ( 2nd ` v ) ) , f e. ( ( 2nd ` v ) ^m ( 1st ` v ) ) |->
        ( g o. f ) ) ) >. } ) $.
  $}

  ${
    $d f g u v x y z $.  $d u v x y z ph $.  $d u v x y z U $.  $d u .x. $.
    $d u H $.
    setcval.c $e |- C = ( SetCat ` U ) $.
    setcval.u $e |- ( ph -> U e. V ) $.
    setcval.h $e |- ( ph -> H = ( x e. U , y e. U |-> ( y ^m x ) ) ) $.
    setcval.o $e |- ( ph -> .x. = ( v e. ( U X. U ) , z e. U |->
      ( g e. ( z ^m ( 2nd ` v ) ) , f e. ( ( 2nd ` v ) ^m ( 1st ` v ) ) |->
        ( g o. f ) ) ) ) $.
    $( Value of the category of sets (in a universe).  (Contributed by Mario
       Carneiro, 3-Jan-2017.) $)
    setcval $p |- ( ph -> C = { <. ( Base ` ndx ) , U >. ,
      <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .x. >. } ) $=
      ( cfv cop cv cmpo vu csetc cnx cbs chom cco ctp cmap co cxp c2nd c1st cvv
      ccom df-setc wceq wa simpr opeq2d eqidd mpoeq123dv adantr eqtr4d tpeq123d
      sqxpeqd elexd wcel tpex a1i fvmptd2 eqtrid ) AFHUBQUCUDQZHRZUCUEQZKRZUCUF
      QZGRZUGZMAUAHVLUASZRZVNBCVSVSCSBSUHUIZTZRZVPEDVSVSUJZVSJIDSESZUKQZUHUIWFW
      EULQUHUIJSISUNTZTZRZUGVRUMUBUMBCDEUAIJUOAVSHUPZUQZVTVMWCVOWIVQWKVSHVLAWJU
      RZUSWKWBKVNWKWBBCHHWATZKWKBCVSVSWAHHWAWLWLWKWAUTVAAKWMUPWJOVBVCUSWKWHGVPW
      KWHEDHHUJZHWGTZGWKEDWDVSWGWNHWGWKVSHWLVEWLWKWGUTVAAGWOUPWJPVBVCUSVDAHLNVF
      VRUMVGAVMVOVQVHVIVJVK $.
  $}

  ${
    $d f g F $.  $d f g v x y z ph $.  $d f g v x y z X $.  $d f g v x y z Y $.
    $d f g G $.  $d v x y z U $.  $d f g v z Z $.
    setcbas.c $e |- C = ( SetCat ` U ) $.
    setcbas.u $e |- ( ph -> U e. V ) $.
    $( Set of objects of the category of sets (in a universe).  (Contributed by
       Mario Carneiro, 3-Jan-2017.) $)
    setcbas $p |- ( ph -> U = ( Base ` C ) ) $=
      ( vx vy vv vz vg vf cnx cbs cfv cop cv cmap co cmpo chom cco cxp c2nd ctp
      c1st ccom wcel wceq c1 cdc catstr baseid snsstp1 strfv syl setcval fveq2d
      c5 eqidd eqtr4d ) ACMNOCPZMUAOGHCCHQGQRSTZPZMUBOIJCCUCCKLJQIQZUDOZRSVFVEU
      FORSKQLQUGTTZPZUEZNOZBNOACDUHCVJUIFCVINDUJUJUSUKPVGCVCULUMVBVDVHUNUOUPABV
      INAGHJIBVGCLKVCDEFAVCUTAVGUTUQURVA $.

    ${
      setchomfval.h $e |- H = ( Hom ` C ) $.
      $( Set of arrows of the category of sets (in a universe).  (Contributed
         by Mario Carneiro, 3-Jan-2017.) $)
      setchomfval $p |- ( ph -> H = ( x e. U , y e. U |-> ( y ^m x ) ) ) $=
        ( vv vz vg vf cv cmap co cmpo cfv cop cnx cbs chom cco cxp c2nd ctp cvv
        c1st ccom c1 c5 eqidd setcval catstr homid snsstp2 wcel mpoexga syl2anc
        cdc strfv3 ) AFBCEECOBOPQZRZUAUBSETZUAUCSVDTZUAUDSKLEEUEEMNLOKOZUFSZPQV
        HVGUISPQMONOUJRRZTZUGDUCUHUKUKULVATABCLKDVIENMVDGHIAVDUMAVIUMUNVIEVDUOU
        PVEVFVJUQAEGURZVKVDUHURIIBCEEVCGGUSUTJVB $.

      setchom.x $e |- ( ph -> X e. U ) $.
      setchom.y $e |- ( ph -> Y e. U ) $.
      $( Set of arrows of the category of sets (in a universe).  (Contributed
         by Mario Carneiro, 3-Jan-2017.) $)
      setchom $p |- ( ph -> ( X H Y ) = ( Y ^m X ) ) $=
        ( vx vy cv cmap co cvv wceq wa setchomfval simprr simprl oveq12d ovmpod
        ovexd ) AMNFGCCNOZMOZPQGFPQDRAMNBCDEHIJUAAUHFSZUGGSZTTUGGUHFPAUIUJUBAUI
        UJUCUDKLAGFPUFUE $.

      $( A morphism of sets is a function.  (Contributed by Mario Carneiro,
         3-Jan-2017.) $)
      elsetchom $p |- ( ph -> ( F e. ( X H Y ) <-> F : X --> Y ) ) $=
        ( co wcel cmap wf setchom eleq2d elmapd bitrd ) ADGHENZODHGPNZOGHDQAUBU
        CDABCEFGHIJKLMRSAHGDCCMLTUA $.
    $}

    ${
      setcco.o $e |- .x. = ( comp ` C ) $.
      $( Composition in the category of sets.  (Contributed by Mario Carneiro,
         3-Jan-2017.) $)
      setccofval $p |- ( ph -> .x. = ( v e. ( U X. U ) , z e. U |->
      ( g e. ( z ^m ( 2nd ` v ) ) , f e. ( ( 2nd ` v ) ^m ( 1st ` v ) ) |->
        ( g o. f ) ) ) ) $=
        ( vx vy cv cfv cnx cop cvv wcel cxp c2nd cmap co c1st ccom cmpo cbs cco
        chom ctp c1 c5 cdc setchomfval eqidd setcval catstr ccoid snsstp3 xpexd
        eqid mpoexga syl2anc strfv3 ) AECBFFUAZFHGBOCOZUBPZUCUDVHVGUEPUCUDHOGOU
        FUGZUGZQUHPFRZQUJPDUJPZRZQUIPVJRZUKDUISULULUMUNRAMNBCDVJFGHVLIJKAMNDFVL
        IJKVLVBUOAVJUPUQVJFVLURUSVKVMVNUTAVFSTFITVJSTAFFIIKKVAKCBVFFVISIVCVDLVE
        $.

      setcco.x $e |- ( ph -> X e. U ) $.
      setcco.y $e |- ( ph -> Y e. U ) $.
      setcco.z $e |- ( ph -> Z e. U ) $.
      setcco.f $e |- ( ph -> F : X --> Y ) $.
      setcco.g $e |- ( ph -> G : Y --> Z ) $.
      $( Composition in the category of sets.  (Contributed by Mario Carneiro,
         3-Jan-2017.) $)
      setcco $p |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) = ( G o. F ) ) $=
        ( vg cmap vf vv vz co cv ccom cop cvv cxp c2nd cfv c1st cmpo setccofval
        wceq wa simprr simprl fveq2d op2ndg syl2anc adantr eqtrd oveq12d op1stg
        wcel eqidd mpoeq123dv opelxpd mpoex a1i ovmpod coeq12d wf elmapd mpbird
        ovex coexg ) ASUAFEJITUDZIHTUDZSUEZUAUEZUFZFEUFZHIUGZJCUDUHAUBUCWEJDDUI
        DSUAUCUEZUBUEZUJUKZTUDZWHWGULUKZTUDZWCUMSUAVSVTWCUMZCUHAUCUBBCDUASGKLMU
        NAWGWEUOZWFJUOZUPZUPZSUAWIWKWCVSVTWCWPWFJWHITAWMWNUQWPWHWEUJUKZIWPWGWEU
        JAWMWNURZUSAWQIUOZWOAHDVFZIDVFZWSNOHIDDUTVAVBVCZVDWPWHIWJHTXBWPWJWEULUK
        ZHWPWGWEULWRUSAXCHUOZWOAWTXAXDNOHIDDVEVAVBVCVDWPWCVGVHAHIDDNOVIPWLUHVFA
        SUAVSVTWCJITVQIHTVQVJVKVLAWAFUOZWBEUOZUPUPWAFWBEAXEXFURAXEXFUQVMAFVSVFZ
        IJFVNRAJIFDDPOVOVPZAEVTVFZHIEVNQAIHEDDONVOVPZAXGXIWDUHVFXHXJFEVSVTVRVAV
        L $.
    $}
  $}

  ${
    $d f g h w x y z C $.  $d f g h w x y z U $.  $d f g h w x y z V $.
    $d x ph $.  $d x X $.
    setccat.c $e |- C = ( SetCat ` U ) $.
    $( Lemma for ~ setccat .  (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    setccatid $p |- ( U e. V ->
      ( C e. Cat /\ ( Id ` C ) = ( x e. U |-> ( _I |` x ) ) ) ) $=
      ( vw vy vz vf vg wcel cv wa co wf elsetchom cop ccom mpbid setcco vh chom
      cfv w3a cco cid cres cvv id setcbas eqidd csetc fvexi biid wf1o f1oi f1of
      a1i mp1i simpl eqid simpr mpbird simpr1l simpr1r simpr31 wceq fcoi2 eqtrd
      syl simpr2l simpr32 fcoi1 fco syl2anc eqeltrd coass simpr2r oveq1d oveq2d
      simpr33 3eqtr4a 3eqtr4d iscatd2 ) CDKZFLZCKZALZCKZMZGLZCKZHLZCKZMZILZWFWH
      BUBUCZNKZJLZWHWKWQNKZUALZWKWMWQNKZUDZUDZFAGHCBBUEUCZUFWHUGZIJUAWQUHWEBCDE
      WEUIUJWEWQUKWEXEUKBUHKWEBCULEUMURXDUNWEWIMZXFWHWHWQNKWHWHXFOZWHWHXFUOZXHX
      GWHUPZWHWHXFUQZUSXGBCXFWQDWHWHEWEWIUTWQVAZWEWIVBZXMPVCWEXDMZXFWPWFWHQZWHX
      ENNXFWPRZWPXNBXECWPXFDWFWHWHEWEXDUTZXEVAZWGWIWOXCWEVDZWGWIWOXCWEVEZXTXNWR
      WFWHWPOZWRWTXBWJWOWEVFXNBCWPWQDWFWHEXQXLXSXTPSZXIXHXNXJXKUSZTXNYAXPWPVGYB
      WFWHWPVHVJVIXNWSXFWHWHQWKXENNWSXFRZWSXNBXECXFWSDWHWHWKEXQXRXTXTWLWNWJXCWE
      VKZYCXNWTWHWKWSOZWRWTXBWJWOWEVLXNBCWSWQDWHWKEXQXLXTYEPSZTXNYFYDWSVGYGWHWK
      WSVMVJVIXNWSWPXOWKXENNZWSWPRZWFWKWQNZXNBXECWPWSDWFWHWKEXQXRXSXTYEYBYGTZXN
      YIYJKWFWKYIOZXNYFYAYLYGYBWFWHWKWSWPVNVOZXNBCYIWQDWFWKEXQXLXSYEPVCVPXNXAWS
      RZWPXOWMXENZNZXAYIWFWKQWMXENZNZXAWSWHWKQWMXENNZWPYONXAYHYQNXNYNWPRXAYIRYP
      YRXAWSWPVQXNBXECWPYNDWFWHWMEXQXRXSXTWLWNWJXCWEVRZYBXNWKWMXAOZYFWHWMYNOXNX
      BUUAWRWTXBWJWOWEWAXNBCXAWQDWKWMEXQXLYEYTPSZYGWHWKWMXAWSVNVOTXNBXECYIXADWF
      WKWMEXQXRXSYEYTYMUUBTWBXNYSYNWPYOXNBXECWSXADWHWKWMEXQXRXTYEYTYGUUBTVSXNYH
      YIXAYQYKVTWCWD $.

    $( The category of sets is a category.  (Contributed by Mario Carneiro,
       3-Jan-2017.) $)
    setccat $p |- ( U e. V -> C e. Cat ) $=
      ( vx wcel ccat ccid cfv cid cv cres cmpt wceq setccatid simpld ) BCFAGFAH
      IEBJEKLMNEABCDOP $.

    setcid.o $e |- .1. = ( Id ` C ) $.
    setcid.u $e |- ( ph -> U e. V ) $.
    setcid.x $e |- ( ph -> X e. U ) $.
    $( The identity arrow in the category of sets is the identity function.
       (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    setcid $p |- ( ph -> ( .1. ` X ) = ( _I |` X ) ) $=
      ( vx cid cv cres cvv ccid cfv wcel wceq wa cmpt ccat setccatid syl simprd
      eqtrid simpr reseq2d resiexd fvmptd ) AKFLKMZNZLFNCDOADBPQZKCULUAZHABUBRZ
      UMUNSZACERUOUPTIKBCEGUCUDUEUFAUKFSZTUKFLAUQUGUHJAFCJUIUJ $.
  $}

  ${
    $d x E $.  $d a g h x y z F $.  $d x y M $.  $d g h U $.  $d g h x y z X $.
    $d g h z C $.  $d g h x y z ph $.  $d a g h x y z Y $.
    setcmon.c $e |- C = ( SetCat ` U ) $.
    setcmon.u $e |- ( ph -> U e. V ) $.
    setcmon.x $e |- ( ph -> X e. U ) $.
    setcmon.y $e |- ( ph -> Y e. U ) $.
    ${
      setcmon.h $e |- M = ( Mono ` C ) $.
      $( A monomorphism of sets is an injection.  (Contributed by Mario
         Carneiro, 3-Jan-2017.) $)
      setcmon $p |- ( ph -> ( F e. ( X M Y ) <-> F : X -1-1-> Y ) ) $=
        ( vx co wcel wa cfv wceq ad2antrr vy vg vz vh wf1 wf cv wi wral cbs cco
        chom eqid setccat setcbas eleqtrd monhom sselda elsetchom biimpa syldan
        ccat syl csn cxp cop ccom simprr sneqd xpeq2d wfn ffnd simprll fcoconst
        adantr syl2anc simprlr 3eqtr4d fconst6g setcco simplr mpbird moni mpbid
        fveq1d vex fvconst2 3eqtr3d expr ralrimivva sylanbrc f1f biimpar sylan2
        eleq2d simprl simprrl ad2antlr simprrr eqeq12d wb cocan1 syl3anc biimpd
        dff13 sylbid anassrs ex sylbird ralrimiv ismon2 mpbir2and impbida ) ADG
        HEOZPZGHDUEZAXOQZGHDUFZNUGZDRZUAUGZDRZSZXSYASZUHZUAGUINGUIXPAXODGHBULRZ
        OZPZXRAXNYGDABUJRZBBUKRZYFEGHYIUMZYFUMZYJUMZMACFPZBVBPZJBCFIUNVCZAGCYIK
        ABCFIJUOZUPZAHCYILYQUPZUQURAYHXRABCDYFFGHIJYLKLUSZUTVAZXQYENUAGGXQXSGPZ
        YAGPZQZYCYDXQUUDYCQZQZXSGXSVDVEZRZXSGYAVDVEZRZXSYAUUFXSUUGUUIUUFDUUGGGV
        FHYJOZOZDUUIUUKOZSUUGUUISUUFDUUGVGZDUUIVGZUULUUMUUFGXTVDZVEZGYBVDZVEZUU
        NUUOUUFUUPUURGUUFXTYBXQUUDYCVHVIVJUUFDGVKZUUBUUNUUQSUUFGHDXQXRUUEUUAVOZ
        VLZXQUUBUUCYCVMZDGGXSVNVPUUFUUTUUCUUOUUSSUVBXQUUBUUCYCVQZDGGYAVNVPVRUUF
        BYJCUUGDFGGHIAYNXOUUEJTZYMAGCPZXOUUEKTZUVGAHCPZXOUUELTZUUFUUBGGUUGUFZUV
        CGXSGVSVCZUVAVTUUFBYJCUUIDFGGHIUVEYMUVGUVGUVIUUFUUCGGUUIUFZUVDGYAGVSVCZ
        UVAVTVRUUFYIBYJDUUGYFUUIEGHGYKYLYMMAYOXOUUEYPTAGYIPXOUUEYRTZAHYIPXOUUEY
        STUVNAXOUUEWAUUFUUGGGYFOZPUVJUVKUUFBCUUGYFFGGIUVEYLUVGUVGUSWBUUFUUIUVOP
        UVLUVMUUFBCUUIYFFGGIUVEYLUVGUVGUSWBWCWDWEUUFUUBUUHXSSUVCGXSXSNWFWGVCUUF
        UUBUUJYASUVCGYAXSUAWFWGVCWHWIWJNUAGHDXEWKAXPQZXOYHDUBUGZUCUGZGVFHYJOZOZ
        DUDUGZUVSOZSZUVQUWASZUHZUDUVRGYFOZUIUBUWFUIZUCYIUIZXPAXRYHGHDWLZAYHXRYT
        WMWNUVPUWGUCYIUVPUVRYIPUVRCPZUWGUVPCYIUVRACYISXPYQVOWOUVPUWJUWGUVPUWJQU
        WEUBUDUWFUWFUVPUWJUVQUWFPZUWAUWFPZQZUWEUVPUWJUWMQZQZUWCDUVQVGZDUWAVGZSZ
        UWDUWOUVTUWPUWBUWQUWOBYJCUVQDFUVRGHIAYNXPUWNJTZYMUVPUWJUWMWPZAUVFXPUWNK
        TZAUVHXPUWNLTZUWOUWKUVRGUVQUFZUVPUWJUWKUWLWQUWOBCUVQYFFUVRGIUWSYLUWTUXA
        USWDZXPXRAUWNUWIWRZVTUWOBYJCUWADFUVRGHIUWSYMUWTUXAUXBUWOUWLUVRGUWAUFZUV
        PUWJUWKUWLWSUWOBCUWAYFFUVRGIUWSYLUWTUXAUSWDZUXEVTWTUWOUWRUWDUWOXPUXCUXF
        UWRUWDXAAXPUWNWAUXDUXGUVRGHDUVQUWAXBXCXDXFXGWJXHXIXJAXOYHUWHQXAXPAUCYIB
        YJUBUDDYFEGHYKYLYMMYPYRYSXKVOXLXM $.
    $}

    ${
      setcepi.h $e |- E = ( Epi ` C ) $.
      setcepi.2 $e |- ( ph -> 2o e. U ) $.
      $( An epimorphism of sets is a surjection.  (Contributed by Mario
         Carneiro, 3-Jan-2017.) $)
      setcepi $p |- ( ph -> ( F e. ( X E Y ) <-> F : X -onto-> Y ) ) $=
        ( va wcel wceq c1o c0 c2o vx vg vz vh co wfo wa wf crn chom cfv cbs cco
        eqid ccat setccat setcbas eleqtrd epihom sselda elsetchom biimpa syldan
        syl frnd wral wss cif cmpt csn cxp cop ccom ffnd fnfvelrn sylan iftrued
        wfn mpteq2dva ffvelcdmda feqmptd eqidd eleq1 ifbid fmptco fconstmpt a1i
        3eqtr4d adantr cpr 1oelpr df2o3 eleqtrri 0ex prid1 ifcli fmpti fconst6g
        cv setcco mp1i simpr mpbird mpbid eqtrdi wb rgenw mpteqb ax-mp sylib wn
        epii nesymi iffalse eqeq1d mtbiri con4i ralimi dfss3 sylibr eqssd dffo2
        1n0 sylanbrc fof adantl biimpar eleq2d ad2antrr simprrl simprrr eqeq12d
        wi simprl simplr cocan2 syl3anc biimpd sylbid anassrs ralrimivva isepi2
        ex sylbird ralrimiv mpbir2and impbida ) AEGHDUEZPZGHEUFZAUUIUGZGHEUHZEU
        IZHQUUJAUUIEGHBUJUKZUEZPZUULAUUHUUOEABULUKZBBUMUKZDUUNGHUUQUNZUUNUNZUUR
        UNZMACFPZBUOPZJBCFIUPVDZAGCUUQKABCFIJUQZURZAHCUUQLUVEURZUSUTAUUPUULABCE
        UUNFGHIJUUTKLVAZVBVCZUUKUUMHUUKGHEUVIVEUUKOWSZUUMPZOHVFZHUUMVGUUKUVKRSV
        HZRQZOHVFZUVLUUKOHUVMVIZOHRVIZQZUVOUUKUVPHRVJVKZUVQUUKUVPEGHVLZTUURUEZU
        EZUVSEUWAUEZQUVPUVSQUUKUVPEVMZUVSEVMZUWBUWCUUKUAGUAWSZEUKZUUMPZRSVHZVIU
        AGRVIUWDUWEUUKUAGUWIRUUKUWFGPZUGUWHRSUUKEGVRUWJUWHUUKGHEUVIVNGUWFEVOVPV
        QVSUUKUAOGHUWGUVMUWIEUVPUUKGHUWFEUVIVTZUUKUAGHEUVIWAZUUKUVPWBUVJUWGQZUV
        KUWHRSUVJUWGUUMWCWDWEUUKUAOGHUWGRREUVSUWKUWLUVSUVQQUUKOHRWFZWGUWMRWBWEW
        HUUKBUURCEUVPFGHTIAUVBUUIJWIZUVAAGCPZUUIKWIZAHCPZUUILWIZATCPUUINWIZUVIH
        TUVPUHZUUKOHTUVMUVPUVPUNUVMTPZUVJHPUVKRSTRSRWJZTWKWLWMZSUXCTSRWNWOWLWMW
        PZWGWQWGZWTUUKBUURCEUVSFGHTIUWOUVAUWQUWSUWTUVIRTPHTUVSUHZUUKUXDHRTWRXAZ
        WTWHUUKUUQBUURDEUVPUUNUVSGHTUUSUUTUVAMAUVCUUIUVDWIAGUUQPUUIUVFWIAHUUQPU
        UIUVGWIATUUQPUUIATCUUQNUVEURWIAUUIXBUUKUVPHTUUNUEZPUXAUXFUUKBCUVPUUNFHT
        IUWOUUTUWSUWTVAXCUUKUVSUXIPUXGUXHUUKBCUVSUUNFHTIUWOUUTUWSUWTVAXCXLXDUWN
        XEUXBOHVFUVRUVOXFUXBOHUXEXGOHUVMRTXHXIXJUVNUVKOHUVKUVNUVKXKZUVNSRQRSYCX
        MUXJUVMSRUVKRSXNXOXPXQXRVDOHUUMXSXTYAGHEYBYDAUUJUGZUUIUUPUBWSZEUVTUCWSZ
        UURUEZUEZUDWSZEUXNUEZQZUXLUXPQZYMZUDHUXMUUNUEZVFUBUYAVFZUCUUQVFZAUUJUUL
        UUPUUJUULAGHEYEYFZAUUPUULUVHYGVCUXKUYBUCUUQUXKUXMUUQPUXMCPZUYBUXKCUUQUX
        MACUUQQUUJUVEWIYHUXKUYEUYBUXKUYEUGUXTUBUDUYAUYAUXKUYEUXLUYAPZUXPUYAPZUG
        ZUXTUXKUYEUYHUGZUGZUXRUXLEVMZUXPEVMZQZUXSUYJUXOUYKUXQUYLUYJBUURCEUXLFGH
        UXMIAUVBUUJUYIJYIZUVAAUWPUUJUYIKYIZAUWRUUJUYILYIZUXKUYEUYHYNZUXKUULUYIU
        YDWIZUYJUYFHUXMUXLUHUXKUYEUYFUYGYJUYJBCUXLUUNFHUXMIUYNUUTUYPUYQVAXDZWTU
        YJBUURCEUXPFGHUXMIUYNUVAUYOUYPUYQUYRUYJUYGHUXMUXPUHUXKUYEUYFUYGYKUYJBCU
        XPUUNFHUXMIUYNUUTUYPUYQVAXDZWTYLUYJUYMUXSUYJUUJUXLHVRUXPHVRUYMUXSXFAUUJ
        UYIYOUYJHUXMUXLUYSVNUYJHUXMUXPUYTVNGHEUXLUXPYPYQYRYSYTUUAUUCUUDUUEAUUIU
        UPUYCUGXFUUJAUCUUQBUURUBUDDEUUNGHUUSUUTUVAMUVDUVFUVGUUBWIUUFUUG $.
    $}

    ${
      setcsect.n $e |- S = ( Sect ` C ) $.
      $( A section in the category of sets, written out.  (Contributed by Mario
         Carneiro, 3-Jan-2017.) $)
      setcsect $p |- ( ph -> ( F ( X S Y ) G <->
        ( F : X --> Y /\ G : Y --> X /\ ( G o. F ) = ( _I |` X ) ) ) ) $=
        ( co cfv wcel eqid wa adantr wbr chom cop cco ccid wceq w3a wf ccom cid
        cres cbs setccat setcbas eleqtrd issect elsetchom anbi12d anbi1d simprl
        ccat syl simprr setcco setcid eqeq12d pm5.32da bitrd df-3an 3bitr4g ) A
        EFHICOUAEHIBUBPZOQZFIHVKOQZFEHIUCHBUDPZOOZHBUEPZPZUFZUGZHIEUHZIHFUHZFEU
        IZUJHUKZUFZUGZABULPZBCVNVPEFVKHIWFRVKRZVNRZVPRZNADGQZBVAQKBDGJUMVBAHDWF
        LABDGJKUNZUOAIDWFMWKUOUPAVLVMSZVRSZVTWASZWDSZVSWEAWMWNVRSWOAWLWNVRAVLVT
        VMWAABDEVKGHIJKWGLMUQABDFVKGIHJKWGMLUQURUSAWNVRWDAWNSZVOWBVQWCWPBVNDEFG
        HIHJAWJWNKTWHAHDQWNLTZAIDQWNMTWQAVTWAUTAVTWAVCVDAVQWCUFWNABDVPGHJWIKLVE
        TVFVGVHVLVMVRVIVTWAWDVIVJVH $.
    $}

    ${
      setcinv.n $e |- N = ( Inv ` C ) $.
      $( An inverse in the category of sets is the converse operation.
         (Contributed by Mario Carneiro, 3-Jan-2017.) $)
      setcinv $p |- ( ph ->
        ( F ( X N Y ) G <-> ( F : X -1-1-onto-> Y /\ G = `' F ) ) ) $=
        ( co wbr wa ccom wceq ad2antrl csect cfv wf cid cres wf1o ccnv cbs eqid
        wcel ccat setccat syl setcbas eleqtrd isinv w3a setcsect df-3an 3ancoma
        bitrdi bitri anbi12d anandi bitr4di fcof1o anbi2i ancom2s adantl f1ocnv
        eqcom sylib f1oeq1 ad2antll mpbird simprr coeq1d f1ococnv1 eqtrd coeq2d
        f1of wb f1ococnv2 jca jca31 impbida 3bitrd ) ADEHIFOPDEHIBUAUBZOPZEDIHW
        HOPZQZHIDUCZIHEUCZQZEDRZUDHUEZSZDERZUDIUEZSZQZQZHIDUFZEDUGZSZQZABUHUBZB
        WHDEFHIXGUINACGUJBUKUJKBCGJULUMAHCXGLABCGJKUNZUOAICXGMXHUOWHUIZUPAWKWNW
        QQZWNWTQZQXBAWIXJWJXKAWIWLWMWQUQXJABWHCDEGHIJKLMXIURWLWMWQUSVAAWJWMWLWT
        UQZXKABWHCEDGIHJKMLXIURXLWLWMWTUQXKWMWLWTUTWLWMWTUSVBVAVCWNWQWTVDVEAXBX
        FXBXFAWNWTWQXFWNWTWQQQXCXDESZQXFHIDEVFXMXEXCXDEVKVGVLVHVIAXFQZWLWMXAXCW
        LAXEHIDWATXNIHEUFZWMXNXOIHXDUFZXCXPAXEHIDVJTXEXOXPWBAXCIHEXDVMVNVOIHEWA
        UMXNWQWTXNWOXDDRZWPXNEXDDAXCXEVPZVQXCXQWPSAXEHIDVRTVSXNWRDXDRZWSXNEXDDX
        RVTXCXSWSSAXEHIDWCTVSWDWEWFWG $.
    $}

    ${
      setciso.n $e |- I = ( Iso ` C ) $.
      $( An isomorphism in the category of sets is a bijection.  (Contributed
         by Mario Carneiro, 3-Jan-2017.) $)
      setciso $p |- ( ph -> ( F e. ( X I Y ) <-> F : X -1-1-onto-> Y ) ) $=
        ( co wcel cfv eqid syl eleqtrd wbr cinv cdm wf1o setccat setcbas isoval
        ccat eleq2d wfun wb invfun funfvbrb ccnv wceq wa setcinv simpl biimtrdi
        cbs sylbid wrel wi funrel releldm ex sylbird mpan2i impbid bitrd ) ADGH
        ENZODGHBUAPZNZUBZOZGHDUCZAVJVMDABUSPZBEVKGHVPQZVKQZACFOBUGOJBCFIUDRZAGC
        VPKABCFIJUEZSZAHCVPLVTSZMUFUHAVNVOAVNDDVLPZVLTZVOAVLUIZVNWDUJAVPBVKGHVQ
        VRVSWAWBUKZDVLULRAWDVOWCDUMZUNZUOVOABCDWCVKFGHIJKLVRUPVOWHUQURUTAVOWGWG
        UNZVNWGQAVOWIUODWGVLTZVNABCDWGVKFGHIJKLVRUPAVLVAZWJVNVBAWEWKWFVLVCRWKWJ
        VNDWGVLVDVERVFVGVHVI $.
    $}
  $}

  ${
    $d f g x y z C $.  $d f g x y z D $.  $d f g x y z ph $.  $d f g x y z V $.
    $d f E $.
    resssetc.c $e |- C = ( SetCat ` U ) $.
    resssetc.d $e |- D = ( SetCat ` V ) $.
    resssetc.1 $e |- ( ph -> U e. W ) $.
    resssetc.2 $e |- ( ph -> V C_ U ) $.
    $( The restriction of the category of sets to a subset is the category of
       sets in the subset.  Thus, the ` SetCat `` U ` categories for different
       ` U ` are full subcategories of each other.  (Contributed by Mario
       Carneiro, 6-Jan-2017.) $)
    resssetc $p |- ( ph -> ( ( Homf ` ( C |`s V ) ) = ( Homf ` D ) /\
                             ( comf ` ( C |`s V ) ) = ( comf ` D ) ) ) $=
      ( vx vy co cfv wceq cv wral wcel cvv eqid vg vf vz cress chomf ccomf chom
      wa cmap ssexd adantr simprl simprr setchom sseldd resshom oveqdr 3eqtr2rd
      wss syl ralrimivva cbs setcbas sseqtrd ressbas2 homfeq mpbird cop cco w3a
      ccom ad2antrr simplr1 simplr2 simplr3 elsetchom mpbid setcco ressco oveqd
      wf 3eqtr2d ralrimivvva eqcomd comfeq jca ) ABEUDMZUENZCUENZOZWGUFNZCUFNZO
      AWJKPZLPZWGUGNZMZWMWNCUGNZMZOZLEQKEQAWSKLEEAWMERZWNERZUHZUHZWRWNWMUIMWMWN
      BUGNZMWPXCCEWQSWMWNHAESRZXBAEDFIJUJZUKWQTZAWTXAULZAWTXAUMZUNXCBDXDFWMWNGA
      DFRZXBIUKXDTZXCEDWMAEDUSZXBJUKZXHUOXCEDWNXMXIUOUNAXBKLXDWOAXEXDWOOXFEBWGX
      DSWGTZXKUPUTUQURVAAKLEWGCWOWQWOTXGAEBVBNZUSEWGVBNOAEDXOJABDFGIVCVDEXOWGBX
      NXOTVEUTZACESHXFVCZVFVGZAWLWKAWLWKOUAPZUBPZWMWNVHZUCPZCVINZMMZXSXTYAYBWGV
      INZMZMZOZUAWNYBWQMZQUBWRQZUCEQLEQKEQAYJKLUCEEEAWTXAYBERZVJZUHZYHUBUAWRYIY
      MXTWRRZXSYIRZUHZUHZYDXSXTVKXSXTYAYBBVINZMZMYGYQCYCEXTXSSWMWNYBHAXEYLYPXFV
      LZYCTZWTXAYKAYPVMZWTXAYKAYPVNZWTXAYKAYPVOZYQYNWMWNXTWAYMYNYOULYQCEXTWQSWM
      WNHYTXGUUBUUCVPVQZYQYOWNYBXSWAYMYNYOUMYQCEXSWQSWNYBHYTXGUUCUUDVPVQZVRYQBY
      RDXTXSFWMWNYBGAXJYLYPIVLYRTZYQEDWMAXLYLYPJVLZUUBUOYQEDWNUUHUUCUOYQEDYBUUH
      UUDUOUUEUUFVRYQYSYFXSXTYQYRYEYAYBAYRYEOZYLYPAXEUUIXFEBWGYRSXNUUGVSUTVLVTV
      TWBVAWCAKLUCECWGYEYCUBUAWQUUAYETXGXQXPAWHWIXRWDWEVGWDWF $.

    $( A functor into a smaller category of sets is a functor into the larger
       category.  (Contributed by Mario Carneiro, 28-Jan-2017.) $)
    funcsetcres2 $p |- ( ph -> ( E Func D ) C_ ( E Func C ) ) $=
      ( cfunc co wcel chomf cfv ccat ccomf wceq eqid vf cv cxp cres cresc eqidd
      cress cbs setccat syl adantr wss setcbas sseqtrd fullresc simpld resssetc
      wa eqtr3d simprd funcrcl adantl fullsubc subccat funcpropd csubc funcres2
      eqsstrrd simpr sseldd ex ssrdv ) AUAECLMZEBLMZAUAUBZVMNZVOVNNAVPURZVMVNVO
      VQVMEBBOPZFFUCUDZUEMZLMZVNVQEEVTCQVQEOPUFVQERPUFVQBFUGMZOPZVTOPZCOPZVQWCW
      DSZWBRPZVTRPZSZVQBUHPZBWBFVTVRWJTZVRTZABQNZVPADGNWMJBDGHUIUJUKZAFWJULVPAF
      DWJKABDGHJUMUNUKZWBTVTTZUOZUPVQWCWESZWGCRPZSZAWRWTURVPABCDFGHIJKUQUKZUPUS
      VQWGWHWSVQWFWIWQUTVQWRWTXAUTUSVQEQNZCQNZVPXBXCURAECVOVAVBZUPZXEVQBVTVSWPV
      QWJBFVRWKWLWNWOVCZVDVQXBXCXDUTVEVQVSBVFPNWAVNULXFEBVSVGUJVHAVPVIVJVKVL $.
  $}

  ${
    setc2ohom.c $e |- C = ( SetCat ` 2o ) $.
    ${
      setc2obas.b $e |- B = ( Base ` C ) $.
      $( ` (/) ` and ` 1o ` are distinct objects in ` ( SetCat `` 2o ) ` .
         This combined with ~ setc2ohom demonstrates that the category does not
         have pairwise disjoint hom-sets.  See also ~ df-cat and ~ cat1 .
         (Contributed by Zhi Wang, 24-Sep-2024.) $)
      setc2obas $p |- ( (/) e. B /\ 1o e. B /\ 1o =/= (/) ) $=
        ( c0 wcel c1o wne cpr 0ex prid1 cbs cfv c2o wceq wtru cvv 2oex eleqtrri
        a1i setcbas mptru df2o3 3eqtr2i 1oelpr 1n0 3pm3.2i ) EAFGAFGEHEEGIZAEGJ
        KABLMZNUHDNUIOPBNQCNQFPRTUAUBUCUDZSGUHAUEUJSUFUG $.
    $}

    setc2ohom.h $e |- H = ( Hom ` C ) $.
    $( ` ( SetCat `` 2o ) ` is a category (provable from ~ setccat and ~ 2oex )
       that does not have pairwise disjoint hom-sets, proved by this theorem
       combined with ~ setc2obas .  Notably, the empty set ` (/) ` is
       simultaneously an object ( ~ setc2obas ), an identity morphism from
       ` (/) ` to ` (/) ` ( ~ setcid or ~ thincid ), and a non-identity
       morphism from ` (/) ` to ` 1o ` .  See ~ cat1lem and ~ cat1 for a more
       general statement.  This category is also thin ( ~ setc2othin ), and
       therefore is "equivalent" to a preorder (actually a partial order).  See
       ~ prsthinc for more details on the "equivalence".  (Contributed by Zhi
       Wang, 24-Sep-2024.) $)
    setc2ohom $p |- (/) e. ( ( (/) H (/) ) i^i ( (/) H 1o ) ) $=
      ( c0 co c1o wcel wf f0 wb wtru c2o cvv a1i df2o3 eleqtrri elsetchom mptru
      mpbir 2oex cpr 0ex prid1 1oelpr elini ) EEEBFZEGBFZEUGHZEEEIZEJUIUJKLAMEB
      NEECMNHLUAOZDEMHLEEGUBZMEGUCUDPQOZUMRSTEUHHZEGEIZGJUNUOKLAMEBNEGCUKDUMGMH
      LGULMUEPQORSTUF $.
  $}

  ${
    $d B w x y z $.  $d H w x y z $.  $d Y w $.
    cat1lem.1 $e |- C = ( SetCat ` U ) $.
    cat1lem.2 $e |- ( ph -> U e. V ) $.
    cat1lem.3 $e |- B = ( Base ` C ) $.
    cat1lem.4 $e |- H = ( Hom ` C ) $.
    cat1lem.5 $e |- ( ph -> (/) e. U ) $.
    cat1lem.6 $e |- ( ph -> Y e. U ) $.
    cat1lem.7 $e |- ( ph -> (/) =/= Y ) $.
    $( The category of sets in a "universe" containing the empty set and
       another set does not have pairwise disjoint hom-sets as required in
       Axiom CAT 1 in [Lang] p. 53.  Lemma for ~ cat1 .  (Contributed by Zhi
       Wang, 15-Sep-2024.) $)
    cat1lem $p |- ( ph -> E. x e. B E. y e. B E. z e. B E. w e. B
        ( ( ( x H y ) i^i ( z H w ) ) =/= (/) /\ -. ( x = z /\ y = w ) ) ) $=
      ( c0 wa wcel co cv cin wne wceq wn weq cbs cfv setcbas eqtr4di eleqtrd wf
      wrex f0 elsetchom mpbiri inelcm syl2anc neneqd intnand oveq1 ineq2d eqeq2
      neeq1d anbi1d notbid anbi12d oveq2 anbi2d syl112anc ineq1d eqeq1 2rexbidv
      rspc2ev syl3anc ) ASFUAZVRSSIUBZDUCZEUCZIUBZUDZSUEZSVTUFZSWAUFZTZUGZTZEFU
      ODFUOZBUCZCUCZIUBZWBUDZSUEZBDUHZCEUHZTZUGZTZEFUODFUOZCFUOBFUOASHFPAHGUIUJ
      FAGHJLMUKNULZUMZXCAVRKFUAVSSKIUBZUDZSUEZSSUFZSKUFZTZUGZWJXCAKHFQXBUMASVSU
      AZSXDUAZXFAXKSSSUNSUPAGHSIJSSLMOPPUQURAXLSKSUNKUPAGHSIJSKLMOPQUQURSVSXDUS
      UTAXHXGASKRVAVBWIXFXJTVSSWAIUBZUDZSUEZXGWFTZUGZTDESKFFVTSUFZWDXOWHXQXRWCX
      NSXRWBXMVSVTSWAIVCVDVFXRWGXPXRWEXGWFVTSSVEVGVHVIWAKUFZXOXFXQXJXSXNXESXSXM
      XDVSWAKSIVJVDVFXSXPXIXSWFXHXGWAKSVEVKVHVIVPVLXAWJSWLIUBZWBUDZSUEZWEWQTZUG
      ZTZEFUODFUOBCSSFFWKSUFZWTYEDEFFYFWOYBWSYDYFWNYASYFWMXTWBWKSWLIVCVMVFYFWRY
      CYFWPWEWQWKSVTVNVGVHVIVOWLSUFZYEWIDEFFYGYBWDYDWHYGYAWCSYGXTVSWBWLSSIVJVMV
      FYGYCWGYGWQWFWEWLSWAVNVKVHVIVOVPVQ $.
  $}

  ${
    $d b c h w x y z $.
    $( The definition of category ~ df-cat does not impose pairwise disjoint
       hom-sets as required in Axiom CAT 1 in [Lang] p. 53.  See ~ setc2obas
       and ~ setc2ohom for a counterexample.  For a version with pairwise
       disjoint hom-sets, see ~ df-homa and its subsection.  (Contributed by
       Zhi Wang, 15-Sep-2024.) $)
    cat1 $p |- E. c e. Cat [. ( Base ` c ) / b ]. [. ( Hom ` c ) / h ].
               -. A. x e. b A. y e. b A. z e. b A. w e. b
               ( ( ( x h y ) i^i ( z h w ) ) =/= (/) -> ( x = z /\ y = w ) ) $=
      ( c2o cfv wcel cv chom co c0 wceq wa wn wrex wtru a1i ccat cin wne cbs wi
      csetc wral wsbc con0 2on eqid setccat ax-mp csn prid1 df2o2 eleqtrri p0ex
      cpr 0ex prid2 0nep0 cat1lem mptru cvv fvexd adantr wb oveq ineq12d neeq1d
      fveq2 anbi1d 2rexbidv adantl pm4.61 2rexbii bitr3i bitri rexeq rexeqbi1dv
      rexnal2 rexbidv 3bitrd ad2antlr 3bitr3d sbcied2 rspcev mp2an ) HUFIZUAJZA
      KZBKZWJLIZMZCKZDKZWNMZUBZNUCZWLWPOWMWQOPZQZPZDWJUDIZRZCXDRZBXDRZAXDRZWLWM
      EKZMZWPWQXIMZUBZNUCZXAUEZDFKZUGCXOUGZBXOUGAXOUGQZEGKZLIZUHZFXRUDIZUHZGUAR
      HUIJZWKUJWJHUIWJUKZULUMXHSABCDXDWJHWNUINUNZYDYCSUJTXDUKWNUKNHJSNNYEUSZHNY
      EUTUOUPUQTYEHJSYEYFHNYEURVAUPUQTNYEUCSVBTVCVDYBXHGWJUAXRWJOZXTXHFYAXDVEYG
      XRUDVFXRWJUDVLYGXOXDOZPZXQXHEXSWNVEYIXRLVFYGXSWNOYHXRWJLVLVGYIXIWNOZPZXMX
      BPZDXORCXORZBXORAXORZXCDXORZCXORZBXORZAXORZXQXHYJYNYRVHYIYJYMYPABXOXOYJYL
      XCCDXOXOYJXMWTXBYJXLWSNYJXJWOXKWRWLWMXIWNVIWPWQXIWNVIVJVKVMVNVNVOYNXQVHYK
      YNXPQZBXORAXORXQYMYSABXOXOYMXNQZDXORCXORYSYTYLCDXOXOXMXAVPVQXNCDXOXOWBVRV
      QXPABXOXOWBVSTYHYRXHVHYGYJYHYRXECXORZBXORZAXORXFBXORZAXORXHYHYQUUBAXOYHYO
      XEBCXOXOXCDXOXDVTVNWCYHUUAXFABXOXOXECXOXDVTVNUUCXGAXOXDXFBXOXDVTWAWDWEWFW
      GWGWHWI $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The category of categories
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c CatCat $.

  $( Extend class notation to include the category Cat. $)
  ccatc $a class CatCat $.

  ${
    $d b f g u v x y z $.
    $( Definition of the category Cat, which consists of all categories in the
       universe ` u ` (i.e., " ` u ` -small categories", see Definition 3.44.
       of [Adamek] p. 39), with functors as the morphisms ( ~ catchom ,
       ~ elcatchom ).  Definition 3.47 of [Adamek] p. 40.  We do not introduce
       a specific definition for " ` u ` -large categories", which can be
       expressed as ` ( Cat \ u ) ` .  (Contributed by Mario Carneiro,
       3-Jan-2017.) $)
    df-catc $a |- CatCat = ( u e. _V |-> [_ ( u i^i Cat ) / b ]_
      { <. ( Base ` ndx ) , b >. ,
        <. ( Hom ` ndx ) , ( x e. b , y e. b |-> ( x Func y ) ) >. ,
        <. ( comp ` ndx ) , ( v e. ( b X. b ) , z e. b |->
          ( g e. ( ( 2nd ` v ) Func z ) , f e. ( Func ` v ) |->
            ( g o.func f ) ) ) >. } ) $.
  $}

  ${
    $d b u v x y z B $.  $d b u H $.  $d b u v x y z ph $.  $d b u v x y z U $.
    $d b f g u v x y z $.  $d b u .x. $.
    catcval.c $e |- C = ( CatCat ` U ) $.
    catcval.u $e |- ( ph -> U e. V ) $.
    catcval.b $e |- ( ph -> B = ( U i^i Cat ) ) $.
    catcval.h $e |- ( ph -> H = ( x e. B , y e. B |-> ( x Func y ) ) ) $.
    catcval.o $e |- ( ph -> .x. = ( v e. ( B X. B ) , z e. B |->
      ( g e. ( ( 2nd ` v ) Func z ) , f e. ( Func ` v ) |->
            ( g o.func f ) ) ) ) $.
    $( Value of the category of categories (in a universe).  (Contributed by
       Mario Carneiro, 3-Jan-2017.) $)
    catcval $p |- ( ph -> C = { <. ( Base ` ndx ) , B >. ,
      <. ( Hom ` ndx ) , H >. , <. ( comp ` ndx ) , .x. >. } ) $=
      ( cfv cv vu vb ccatc cnx cbs cop chom cco ctp ccat cin cfunc co cmpo c2nd
      cxp ccofu csb cvv df-catc wceq wa wcel vex inex1 a1i ineq1d adantr eqtr4d
      simpr opeq2d eqidd mpoeq123dv ad2antrr sqxpeqd csbied2 elexd tpex fvmptd2
      tpeq123d eqtrid ) AGIUCSUDUESZFUFZUDUGSZLUFZUDUHSZHUFZUIZNAUAIUBUATZUJUKZ
      WBUBTZUFZWDBCWKWKBTCTULUMZUNZUFZWFEDWKWKUPZWKKJETZUOSDTULUMWQULSKTJTUQUMU
      NZUNZUFZUIZURWHUSUCUSBCDEUAJKUBUTAWIIVAZVBZUBWJFXAWHUSWJUSVCXCWIUJUAVDVEV
      FXCWJIUJUKZFXCWIIUJAXBVJVGAFXDVAXBPVHVIXCWKFVAZVBZWLWCWOWEWTWGXFWKFWBXCXE
      VJZVKXFWNLWDXFWNBCFFWMUNZLXFBCWKWKWMFFWMXGXGXFWMVLVMALXHVAXBXEQVNVIVKXFWS
      HWFXFWSEDFFUPZFWRUNZHXFEDWPWKWRXIFWRXFWKFXGVOXGXFWRVLVMAHXJVAXBXERVNVIVKV
      TVPAIMOVQWHUSVCAWCWEWGVRVFVSWA $.
  $}

  ${
    $d v x y z B $.  $d f g v x y z ph $.  $d v x y z U $.  $d f g v x y z X $.
    $d f g F $.  $d f g G $.  $d f g v x y z Y $.  $d f g v z Z $.
    catcbas.c $e |- C = ( CatCat ` U ) $.
    catcbas.b $e |- B = ( Base ` C ) $.
    catcbas.u $e |- ( ph -> U e. V ) $.
    $( Set of objects of the category of categories.  (Contributed by Mario
       Carneiro, 3-Jan-2017.) $)
    catcbas $p |- ( ph -> B = ( U i^i Cat ) ) $=
      ( vx vy vv vz vg vf cnx cfv cop cv cfunc co ccat cin chom cmpo c2nd ccofu
      cbs cco cxp ctp cvv c1 c5 eqidd catcval catstr baseid snsstp1 wcel inex1g
      cdc syl strfv3 ) ABDUAUBZOUGPVDQZOUCPIJVDVDIRJRSTUDZQZOUHPKLVDVDUIVDMNKRZ
      UEPLRSTVHSPMRNRUFTUDUDZQZUJCUGUKULULUMVAQAIJLKVDCVIDNMVFEFHAVDUNAVFUNAVIU
      NUOVIVDVFUPUQVEVGVJURADEUSVDUKUSHDUAEUTVBGVC $.

    ${
      catchomfval.h $e |- H = ( Hom ` C ) $.
      $( Set of arrows of the category of categories (in a universe).
         (Contributed by Mario Carneiro, 3-Jan-2017.) $)
      catchomfval $p |- ( ph -> H = ( x e. B , y e. B |-> ( x Func y ) ) ) $=
        ( vv vz vg vf cfv cop chom cv cnx cbs cfunc cmpo cco cxp c2nd ccofu ctp
        co catcbas eqidd catcval fveq2d eqtrid cvv wcel wceq fvexi mpoex c1 cdc
        c5 catstr homid snsstp2 strfv mp1i eqtr4d ) AGUAUBQDRZUASQBCDDBTCTUCUJZ
        UDZRZUAUEQMNDDUFDOPMTZUGQNTUCUJVNUCQOTPTUHUJUDUDZRZUIZSQZVLAGESQVRLAEVQ
        SABCNMDEVOFPOVLHIKADEFHIJKUKAVLULAVOULUMUNUOVLUPUQVLVRURABCDDVKDEUBJUSZ
        VSUTVLVQSUPVAVAVCVBRVODVLVDVEVJVMVPVFVGVHVI $.

      catchom.x $e |- ( ph -> X e. B ) $.
      catchom.y $e |- ( ph -> Y e. B ) $.
      $( Set of arrows of the category of categories (in a universe).
         (Contributed by Mario Carneiro, 3-Jan-2017.) $)
      catchom $p |- ( ph -> ( X H Y ) = ( X Func Y ) ) $=
        ( vx vy cv cfunc co wceq cvv catchomfval wa oveq12 adantl ovexd ovmpod
        ) AOPGHBBOQZPQZRSZGHRSZEUAAOPBCDEFIJKLUBUHGTUIHTUCUJUKTAUHGUIHRUDUEMNAG
        HRUFUG $.
    $}

    ${
      catcco.o $e |- .x. = ( comp ` C ) $.
      $( Composition in the category of categories.  (Contributed by Mario
         Carneiro, 3-Jan-2017.) $)
      catccofval $p |- ( ph -> .x. = ( v e. ( B X. B ) , z e. B |->
      ( g e. ( ( 2nd ` v ) Func z ) , f e. ( Func ` v ) |->
            ( g o.func f ) ) ) ) $=
        ( vx cco cfv cnx cop cv vy cbs chom cxp c2nd cfunc co ccofu ctp catcbas
        cmpo eqid catchomfval eqidd catcval fveq2d cvv wcel wceq fvexi mpoex c1
        xpex c5 cdc catstr ccoid snsstp3 strfv ax-mp 3eqtr4g ) AEPQRUBQDSZRUCQE
        UCQZSZRPQCBDDUDZDIHCTZUEQBTUFUGVPUFQITHTUHUGUKZUKZSZUIZPQZFVRAEVTPAOUAB
        CDEVRGHIVMJKMADEGJKLMUJAOUADEGVMJKLMVMULUMAVRUNUOUPNVRUQURVRWAUSCBVODVQ
        DDDEUBLUTZWBVCWBVAVRVTPUQVBVBVDVESVRDVMVFVGVLVNVSVHVIVJVK $.

      catcco.x $e |- ( ph -> X e. B ) $.
      catcco.y $e |- ( ph -> Y e. B ) $.
      catcco.z $e |- ( ph -> Z e. B ) $.
      catcco.f $e |- ( ph -> F e. ( X Func Y ) ) $.
      catcco.g $e |- ( ph -> G e. ( Y Func Z ) ) $.
      $( Composition in the category of categories.  (Contributed by Mario
         Carneiro, 3-Jan-2017.) $)
      catcco $p |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) = ( G o.func F ) ) $=
        ( vg vf vv vz cfunc co cv ccofu cop cvv cxp c2nd cfv cmpo catccofval wa
        wceq simprl fveq2d wcel op2ndg syl2anc adantr eqtrd oveq12d df-ov eqidd
        simprr eqtr4di mpoeq123dv opelxpd ovex mpoex ovmpod oveq12 adantl ovexd
        a1i ) AUAUBGFJKUEUFZIJUEUFZUAUGZUBUGZUHUFZGFUHUFZIJUIZKDUFUJAUCUDWEKBBU
        KBUAUBUCUGZULUMZUDUGZUEUFZWFUEUMZWCUNUAUBVSVTWCUNZDUJAUDUCBCDEUBUAHLMNO
        UOAWFWEUQZWHKUQZUPZUPZUAUBWIWJWCVSVTWCWOWGJWHKUEWOWGWEULUMZJWOWFWEULAWL
        WMURZUSAWPJUQZWNAIBUTJBUTWRPQIJBBVAVBVCVDAWLWMVHVEWOWJWEUEUMVTWOWFWEUEW
        QUSIJUEVFVIWOWCVGVJAIJBBPQVKRWKUJUTAUAUBVSVTWCJKUEVLIJUEVLVMVRVNWAGUQWB
        FUQUPWCWDUQAWAGWBFUHVOVPTSAGFUHVQVN $.
    $}
  $}

  ${
    $d f g h w x y z B $.  $d f g h w x y z C $.  $d f g h w x y z U $.
    $d x ph $.  $d f g h w x y z V $.  $d x X $.
    catccatid.c $e |- C = ( CatCat ` U ) $.
    catccatid.b $e |- B = ( Base ` C ) $.
    $( Lemma for ~ catccat .  (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    catccatid $p |- ( U e. V ->
      ( C e. Cat /\ ( Id ` C ) = ( x e. B |-> ( idFunc ` x ) ) ) ) $=
      ( wcel cv wa cfv co cfunc ccat eqid catchom cop ccofu eleqtrd catcco chom
      vw vy vz vf vg vh w3a cco cidfu cvv cbs wceq a1i eqidd ccatc fvexi cin id
      biid catcbas inss2 eqsstrdi sselda idfucl syl simpl simpr simpr1l simpr1r
      simpr31 syldan cofulid eqtrd simpr2l simpr32 cofurid cofucl oveq1d oveq2d
      eleqtrrd 3eltr4d simpr33 simpr2r cofuass 3eqtr4d iscatd2 ) DEHZUBIZBHZAIZ
      BHZJZUCIZBHZUDIZBHZJZUEIZWIWKCUAKZLZHZUFIZWKWNWTLZHZUGIZWNWPWTLZHZUHZUHZU
      BAUCUDBCCUIKZWKUJKZUEUFUGWTUKBCULKUMWHGUNWHWTUOWHXKUOCUKHWHCDUPFUQUNXJUTW
      HWLJZXLWKWKMLZWKWKWTLXMWKNHXLXNHZWHBNWKWHBDNURNWHBCDEFGWHUSVADNVBVCVDWKXL
      XLOZVEVFZXMBCDWTEWKWKFGWHWLVGWTOZWHWLVHZXSPWAWHXJJZXLWSWIWKQZWKXKLLXLWSRL
      WSXTBCXKDWSXLEWIWKWKFGWHXJVGZXKOZWJWLWRXIWHVIZWJWLWRXIWHVJZYEXTWSXAWIWKML
      XBXEXHWMWRWHVKXTBCDWTEWIWKFGYBXRYDYEPSZWHXJWLXOYEXQVLZTXTWIWKWSXLYFXPVMVN
      XTXCXLWKWKQWNXKLLXCXLRLXCXTBCXKDXLXCEWKWKWNFGYBYCYEYEWOWQWMXIWHVOZYGXTXCX
      DWKWNMLXBXEXHWMWRWHVPXTBCDWTEWKWNFGYBXRYEYHPSZTXTWKWNXCXLYIXPVQVNXTXCWSRL
      ZWIWNMLXCWSYAWNXKLLZWIWNWTLXTWIWKWNWSXCYFYIVRZXTBCXKDWSXCEWIWKWNFGYBYCYDY
      EYHYFYITZXTBCDWTEWIWNFGYBXRYDYHPWBXTXFXCRLZWSYAWPXKLZLZXFYJWIWNQWPXKLZLZX
      FXCWKWNQWPXKLLZWSYOLXFYKYQLXTYNWSRLXFYJRLYPYRXTWIWKWNWPWSXCXFYFYIXTXFXGWN
      WPMLXBXEXHWMWRWHWCXTBCDWTEWNWPFGYBXRYHWOWQWMXIWHWDZPSZWEXTBCXKDWSYNEWIWKW
      PFGYBYCYDYEYTYFXTWKWNWPXCXFYIUUAVRTXTBCXKDYJXFEWIWNWPFGYBYCYDYHYTYLUUATWF
      XTYSYNWSYOXTBCXKDXCXFEWKWNWPFGYBYCYEYHYTYIUUATVSXTYKYJXFYQYMVTWFWG $.

    catcid.o $e |- .1. = ( Id ` C ) $.
    catcid.i $e |- I = ( idFunc ` X ) $.
    catcid.u $e |- ( ph -> U e. V ) $.
    catcid.x $e |- ( ph -> X e. B ) $.
    $( The identity arrow in the category of categories is the identity
       functor.  (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    catcid $p |- ( ph -> ( .1. ` X ) = I ) $=
      ( vx cfv cidfu wcel wceq wa cv cvv ccid cmpt ccat catccatid simprd eqtrid
      syl simpr fveq2d fvexd fvmptd eqtr4di ) AHEPHQPZFAOHOUAZQPZUOBEUBAECUCPZO
      BUQUDZKACUERZURUSSZADGRUTVATMOBCDGIJUFUIUGUHAUPHSZTUPHQAVBUJUKNAHQULUMLUN
      $.
  $}

  ${
    $d x C $.  $d x U $.  $d x V $.
    catccat.c $e |- C = ( CatCat ` U ) $.
    $( The category of categories is a category, see remark 3.48 in [Adamek]
       p. 40.  (Clearly it cannot be an element of itself, hence it is " ` U `
       -large".)  (Contributed by Mario Carneiro, 3-Jan-2017.) $)
    catccat $p |- ( U e. V -> C e. Cat ) $=
      ( vx wcel ccat ccid cfv cbs cv cidfu cmpt wceq eqid catccatid simpld ) BC
      FAGFAHIEAJIZEKLIMNERABCDROPQ $.
  $}

  ${
    $d f g x y z C $.  $d f g x y z D $.  $d f g x y z ph $.  $d f g x y z V $.
    resscatc.c $e |- C = ( CatCat ` U ) $.
    resscatc.d $e |- D = ( CatCat ` V ) $.
    resscatc.1 $e |- ( ph -> U e. W ) $.
    resscatc.2 $e |- ( ph -> V C_ U ) $.
    $( The restriction of the category of categories to a subset is the
       category of categories in the subset.  Thus, the ` CatCat `` U `
       categories for different ` U ` are full subcategories of each other.
       (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    resscatc $p |- ( ph -> ( ( Homf ` ( C |`s V ) ) = ( Homf ` D ) /\
                             ( comf ` ( C |`s V ) ) = ( comf ` D ) ) ) $=
      ( vx vy co cfv wceq cin wral wcel cvv eqid vg vf vz cress chomf chom ccat
      ccomf cv wa cfunc cbs ssexd adantr simprl catcbas eleqtrrd simprr catchom
      wss inass ineq2d eqtr4id dfss2 sylib ineq1d ressbas syl 3eqtr3d ressbasss
      eqsstrdi sseldd oveqdr 3eqtr2rd ralrimivva eqcomd homfeq mpbird cop ccofu
      resshom cco ad2antrr simplr1 simplr2 simplr3 eleqtrd catcco oveqd 3eqtr2d
      w3a ressco ralrimivvva comfeq jca ) ABEUDMZUENZCUENZOZWPUHNZCUHNZOAWSKUIZ
      LUIZWPUFNZMZXBXCCUFNZMZOZLEUGPZQKXIQAXHKLXIXIAXBXIRZXCXIRZUJZUJZXGXBXCUKM
      ZXBXCBUFNZMXEXMCULNZCEXFSXBXCHXPTZAESRZXLAEDFIJUMZUNXFTZXMXBXIXPAXJXKUOZA
      XPXIOZXLAXPCESHXQXSUPZUNZUQXMXCXIXPAXJXKURZYDUQUSXMBULNZBDXOFXBXCGYFTZADF
      RZXLIUNXOTZXMXIYFXBAXIYFUTZXLAXIWPULNZYFAEDPZUGPZEYFPZXIYKAYMEDUGPZPYNEDU
      GVAAYFYOEAYFBDFGYGIUPVBVCAYLEUGAEDUTYLEOJEDVDVEVFAXRYNYKOXSEYFWPSBWPTZYGV
      GVHVIZEYFWPBYPYGVJVKZUNZYAVLXMXIYFXCYSYEVLUSAXLKLXOXDAXRXOXDOXSEBWPXOSYPY
      IWAVHVMVNVOAKLXIWPCXDXFXDTXTYQAXPXIYCVPZVQVRZAXAWTAXAWTOUAUIZUBUIZXBXCVSZ
      UCUIZCWBNZMMZUUBUUCUUDUUEWPWBNZMZMZOZUAXCUUEXFMZQUBXGQZUCXIQLXIQKXIQAUUMK
      LUCXIXIXIAXJXKUUEXIRZWKZUJZUUKUBUAXGUULUUPUUCXGRZUUBUULRZUJZUJZUUGUUBUUCV
      TMUUBUUCUUDUUEBWBNZMZMUUJUUTXPCUUFEUUCUUBSXBXCUUEHXQAXRUUOUUSXSWCZUUFTZUU
      TXBXIXPXJXKUUNAUUSWDZAYBUUOUUSYCWCZUQZUUTXCXIXPXJXKUUNAUUSWEZUVFUQZUUTUUE
      XIXPXJXKUUNAUUSWFZUVFUQZUUTUUCXGXNUUPUUQUURUOUUTXPCEXFSXBXCHXQUVCXTUVGUVI
      USWGZUUTUUBUULXCUUEUKMUUPUUQUURURUUTXPCEXFSXCUUEHXQUVCXTUVIUVKUSWGZWHUUTY
      FBUVADUUCUUBFXBXCUUEGYGAYHUUOUUSIWCUVATZUUTXIYFXBAYJUUOUUSYRWCZUVEVLUUTXI
      YFXCUVOUVHVLUUTXIYFUUEUVOUVJVLUVLUVMWHUUTUVBUUIUUBUUCUUTUVAUUHUUDUUEAUVAU
      UHOZUUOUUSAXRUVPXSEBWPUVASYPUVNWLVHWCWIWIWJVOWMAKLUCXICWPUUHUUFUBUAXFUVDU
      UHTXTYTYQAWQWRUUAVPWNVRVPWO $.
  $}

  ${
    $d x y C $.  $d f g u v x y z F $.  $d u v x y G $.  $d f g u v x y z ph $.
    $d f g u v z H $.  $d x y I $.  $d u v x y z R $.  $d f g u v x y z S $.
    $d f g u v x y z X $.  $d f g u v x y z Y $.
    catciso.c $e |- C = ( CatCat ` U ) $.
    catciso.b $e |- B = ( Base ` C ) $.
    catciso.r $e |- R = ( Base ` X ) $.
    catciso.s $e |- S = ( Base ` Y ) $.
    catciso.u $e |- ( ph -> U e. V ) $.
    catciso.x $e |- ( ph -> X e. B ) $.
    catciso.y $e |- ( ph -> Y e. B ) $.
    ${
      catcisolem.i $e |- I = ( Inv ` C ) $.
      catcisolem.g $e |- H = ( x e. S , y e. S |->
        `' ( ( `' F ` x ) G ( `' F ` y ) ) ) $.
      catcisolem.1 $e |- ( ph -> F ( ( X Full Y ) i^i ( X Faith Y ) ) G ) $.
      catcisolem.2 $e |- ( ph -> F : R -1-1-onto-> S ) $.
      $( Lemma for ~ catciso .  (Contributed by Mario Carneiro,
         29-Jan-2017.) $)
      catcisolem $p |- ( ph -> <. F , G >. ( X I Y ) <. `' F , H >. ) $=
        ( vu vv vz vf vg cop ccnv co wbr csect cfv cco ccid wceq ccofu cidfu cv
        ccom cmpo cid cres cxp chom cmpt wf1o f1ococnv1 syl wcel 3ad2ant1 simp2
        wf f1of ffvelcdmd simp3 wa simpl fveq2d simpr oveq12d cnveqd ovex cnvex
        w3a ovmpoa syl2anc f1ocnvfv1 eqtrd eqid cful cfth cin ffthf1o mpoeq3dva
        coeq1d fveq2 df-ov eqtr4di reseq2d opeq12d cfunc inss1 sstri ssbri ccat
        mpompt fullfunc inss2 eqsstrdi sseldd f1ocnv 3syl adantr ffvelcdmda weq
        catcbas f1ocnvfv2 mpbird fveq1d f1ocnvfv f1oeq3d mpbid 3eqtr4d cofuval2
        wi idfuval df-br sylib catcco catcid catchom eleqtrrd issect2 f1ococnv2
        mpd wfn fnmpoi adantrr adantrl adantl simprl simprr eqcomd feq12d sylan
        a1i funcid catidcl simp21 simp22 simp23 simp3l oveq123d catcocl isfuncd
        simp3r funcco catccat 3adant1 coeq2d 3adant3 3adant2 3impb mpbir2and
        isinv ) AIJULZIUMZKULZNOLUNUOUVKUVMNOEUPUQZUNUOZUVMUVKONUVNUNUOZAUVOUVM
        UVKNOULNEURUQZUNUNZNEUSUQZUQZUTAUVMUVKVAUNZNVBUQZUVRUVTAUVLIVDZUGUHFFUG
        VCZIUQZUHVCZIUQZKUNZUWDUWFJUNZVDZVEZULVFFVGZUIFFVHVFUIVCZNVIUQZUQZVGZVJ
        ZULUWAUWBAUWCUWLUWKUWQAFGIVKZUWCUWLUTUFFGIVLVMAUWKUGUHFFVFUWDUWFUWNUNZV
        GZVEUWQAUGUHFFUWJUWTAUWDFVNZUWFFVNZWIZUWJUWIUMZUWIVDZUWTUXCUWHUXDUWIUXC
        UWHUWEUVLUQZUWGUVLUQZJUNZUMZUXDUXCUWEGVNUWGGVNUWHUXIUTUXCFGUWDIUXCUWRFG
        IVQAUXAUWRUXBUFVOZFGIVRVMZAUXAUXBVPZVSUXCFGUWFIUXKAUXAUXBVTZVSBCUWEUWGG
        GBVCZUVLUQZCVCZUVLUQZJUNZUMZUXIKUXNUWEUTZUXPUWGUTZWAZUXRUXHUYBUXOUXFUXQ
        UXGJUYBUXNUWEUVLUXTUYAWBWCUYBUXPUWGUVLUXTUYAWDWCWEWFUDUXHUXFUXGJWGWHWJW
        KUXCUXHUWIUXCUXFUWDUXGUWFJUXCUWRUXAUXFUWDUTUXJUXLFGUWDIWLWKUXCUWRUXBUXG
        UWFUTUXJUXMFGUWFIWLWKWEWFWMWTUXCUWSUWEUWGOVIUQZUNZUWIVKUXEUWTUTUXCFNOIJ
        UWNUYCUWDUWFRUWNWNZUYCWNZAUXAIJNOWOUNZNOWPUNZWQZUOZUXBUEVOUXLUXMWRUWSUY
        DUWIVLVMWMWSUGUHUIFFUWPUWTUWMUWDUWFULZUTZUWOUWSVFUYLUWOUYKUWNUQUWSUWMUY
        KUWNXAUWDUWFUWNXBXCXDXKXCXEAUGUHFNONIJUVLKRAUYJIJNOXFUNZUOZUEUYIUYMIJUY
        IUYGUYMUYGUYHXGNOXLXHXIVMZAUGUHUIGFOOURUQZOUSUQZUJUKNUVLKUYCNUSUQZUWNNU
        RUQZSRUYFUYEUYQWNZUYRWNZUYPWNZUYSWNZADXJOADHXJWQXJADEHMPQTYAHXJXMXNZUBX
        OZADXJNVUDUAXOZAUWRGFUVLVKGFUVLVQZUFFGIXPGFUVLVRXQZKGGVHZUUAABCGGUXSKUD
        UXRUXOUXQJWGWHUUBUUKAUWDGVNZUWFGVNZWAZWAZUWDUWFUYCUNZUWDUVLUQZUWFUVLUQZ
        UWNUNZUWDUWFKUNZVQVUOIUQZVUPIUQZUYCUNZVUQVUOVUPJUNZUMZVQZVUMVUQVVAVVBVK
        ZVVAVUQVVCVKVVDVUMFNOIJUWNUYCVUOVUPRUYEUYFAUYJVULUEXRAVUJVUOFVNZVUKAGFU
        WDUVLVUHXSZUUCAVUKVUPFVNZVUJAGFUWFUVLVUHXSZUUDWRVUQVVAVVBXPVVAVUQVVCVRX
        QVUMVUNVVAVUQVURVVCVULVURVVCUTZABCUWDUWFGGUXSVVCKBUGXTZCUHXTZWAZUXRVVBV
        VMUXOVUOUXQVUPJVVMUXNUWDUVLVVKVVLWBWCVVMUXPUWFUVLVVKVVLWDWCWEWFUDVVBVUO
        VUPJWGWHWJZUUEVUMVVAVUNVUMVUSUWDVUTUWFUYCVUMUWRVUJVUSUWDUTZAUWRVULUFXRZ
        AVUJVUKUUFFGUWDIYBZWKVUMUWRVUKVUTUWFUTZVVPAVUJVUKUUGFGUWFIYBZWKWEZUUHUU
        IYCAVUJWAZUWDUYQUQZUWDUWDKUNZUQVWBVUOVUOJUNZUMZUQZVUOUYRUQZVWAVWBVWCVWE
        VWAVUJVUJVWCVWEUTAVUJWDZVWHBCUWDUWDGGUXSVWEKVVKCUGXTZWAZUXRVWDVWJUXOVUO
        UXQVUOJVWJUXNUWDUVLVVKVWIWBWCVWJUXPUWDUVLVVKVWIWDWCWEWFUDVWDVUOVUOJWGWH
        WJWKYDVWAVWGVWDUQZVWBUTZVWFVWGUTZVWAVWKVUSUYQUQVWBVWAFNUYROIJUYQVUORVUA
        UYTAUYNVUJUYOXRVVGUULVWAVUSUWDUYQAUWRVUJVVOUFVVQUUJWCWMVWAVUOVUOUWNUNZV
        USVUSUYCUNZVWDVKVWGVWNVNVWLVWMYJVWAFNOIJUWNUYCVUOVUORUYEUYFAUYJVUJUEXRV
        VGVVGWRVWAFNUYRUWNVUORUYEVUAANXJVNZVUJVUFXRVVGUUMVWNVWOVWGVWBVWDYEWKYTW
        MAVUJVUKUWMGVNZWIZUJVCZVUNVNZUKVCZUWFUWMUYCUNZVNZWAZWIZVXAVWSUYKUWMUYPU
        NZUNZVUOUWMUVLUQZJUNZUMZUQZVXAVUPVXHJUNZUMZUQZVWSVVCUQZVUOVUPULVXHUYSUN
        ZUNZVXGUWDUWMKUNZUQVXAUWFUWMKUNZUQZVWSVURUQZVXPUNVXEVXQVXIUQZVXGUTZVXKV
        XQUTZVXEVYBVXNVXLUQZVXOVVBUQZVUSVUTULZVXHIUQZUYPUNZUNVXGVXEFNUYSOIJUWNV
        XOVXNUYPVUOVUPVXHRUYEVUCVUBAVWRUYNVXDUYOVOVXEGFUWDUVLAVWRVUGVXDVUHVOZAV
        UJVUKVWQVXDUUNZVSZVXEGFUWFUVLVYJAVUJVUKVWQVXDUUOZVSZVXEGFUWMUVLVYJAVUJV
        UKVWQVXDUUPZVSZVXEVUNVUQVWSVVCVXEVUQVUNVVBVKZVUNVUQVVCVKVUNVUQVVCVQVXEV
        VEVYQVXEFNOIJUWNUYCVUOVUPRUYEUYFAVWRUYJVXDUEVOZVYLVYNWRVXEVVAVUNVUQVVBV
        XEVUSUWDVUTUWFUYCVXEUWRVUJVVOAVWRUWRVXDUFVOZVYKVVQWKZVXEUWRVUKVVRVYSVYM
        VVSWKZWEYFYGZVUQVUNVVBXPVUNVUQVVCVRXQAVWRVWTVXCUUQZVSZVXEVXBVUPVXHUWNUN
        ZVXAVXMVXEWUEVXBVXLVKZVXBWUEVXMVKVXBWUEVXMVQVXEWUEVUTVYHUYCUNZVXLVKWUFV
        XEFNOIJUWNUYCVUPVXHRUYEUYFVYRVYNVYPWRVXEWUGVXBWUEVXLVXEVUTUWFVYHUWMUYCW
        UAVXEUWRVWQVYHUWMUTVYSVYOFGUWMIYBWKZWEYFYGZWUEVXBVXLXPVXBWUEVXMVRXQAVWR
        VWTVXCUVAZVSZUVBVXEVYEVXAVYFVWSVYIVXFVXEVYGUYKVYHUWMUYPVXEVUSUWDVUTUWFV
        YTWUAXEWUHWEVXEWUFVXCVYEVXAUTWUIWUJWUEVXBVXAVXLYBWKVXEVYQVWTVYFVWSUTWUB
        WUCVUQVUNVWSVVBYBWKUURWMVXEVUOVXHUWNUNZUWDUWMUYCUNZVXIVKZVXQWULVNVYCVYD
        YJVXEWULVUSVYHUYCUNZVXIVKWUNVXEFNOIJUWNUYCVUOVXHRUYEUYFVYRVYLVYPWRVXEWU
        OWUMWULVXIVXEVUSUWDVYHUWMUYCVYTWUHWEYFYGVXEFNUYSVXOVXNUWNVUOVUPVXHRUYEV
        UCAVWRVWPVXDVUFVOVYLVYNVYPWUDWUKUUSWULWUMVXQVXGVXIYEWKYTVXEVXGVXRVXJVXE
        VUJVWQVXRVXJUTVYKVYOBCUWDUWMGGUXSVXJKVVKCUIXTZWAZUXRVXIWUQUXOVUOUXQVXHJ
        WUQUXNUWDUVLVVKWUPWBWCWUQUXPUWMUVLVVKWUPWDWCWEWFUDVXIVUOVXHJWGWHWJWKYDV
        XEVXTVXNVYAVXOVXPVXEVXAVXSVXMVXEVUKVWQVXSVXMUTVYMVYOBCUWFUWMGGUXSVXMKBU
        HXTZWUPWAZUXRVXLWUSUXOVUPUXQVXHJWUSUXNUWFUVLWURWUPWBWCWUSUXPUWMUVLWURWU
        PWDWCWEWFUDVXLVUPVXHJWGWHWJWKYDVXEVWSVURVVCVXEVUJVUKVVJVYKVYMVVNWKYDWEY
        HUUTZYIAUIFNUWNUWBUWBWNZRVUFUYEYKYHADEUVQHUVKUVMMNONPQTUVQWNZUAUBUAAUYN
        UVKUYMVNUYOIJUYMYLYMZAUVLKONXFUNZUOUVMWVDVNWUTUVLKWVDYLYMZYNADEHUVSUWBM
        NPQUVSWNZWVATUAYOYHADEUVNUVQUVSUVKUVMEVIUQZNOQWVGWNZWVBWVFUVNWNZAHMVNEX
        JVNTEHMPUVCVMZUAUBAUVKUYMNOWVGUNWVCADEHWVGMNOPQTWVHUAUBYPYQZAUVMWVDONWV
        GUNWVEADEHWVGMONPQTWVHUBUAYPYQZYRYCAUVPUVKUVMONULOUVQUNUNZOUVSUQZUTAUVK
        UVMVAUNZOVBUQZWVMWVNAIUVLVDZUGUHGGVVBVURVDZVEZULVFGVGZUIVUIVFUWMUYCUQZV
        GZVJZULWVOWVPAWVQWVTWVSWWCAUWRWVQWVTUTUFFGIYSVMAWVSUGUHGGVFVUNVGZVEWWCA
        UGUHGGWVRWWDAVUJVUKWIZWVRVVBVVCVDZWWDWWEVURVVCVVBVUJVUKVVJAVVNUVDUVEWWE
        VYQWWFWWDUTWWEVVEVYQWWEFNOIJUWNUYCVUOVUPRUYEUYFAVUJUYJVUKUEVOAVUJVVFVUK
        VVGUVFAVUKVVHVUJVVIUVGWRWWEVVAVUNVUQVVBAVUJVUKVVAVUNUTVVTUVHYFYGVUQVUNV
        VBYSVMWMWSUGUHUIGGWWBWWDUYLWWAVUNVFUYLWWAUYKUYCUQVUNUWMUYKUYCXAUWDUWFUY
        CXBXCXDXKXCXEAUGUHGONOUVLKIJSWUTUYOYIAUIGOUYCWVPWVPWNZSVUEUYFYKYHADEUVQ
        HUVMUVKMONOPQTWVBUBUAUBWVEWVCYNADEHUVSWVPMOPQWVFWWGTUBYOYHADEUVNUVQUVSU
        VMUVKWVGONQWVHWVBWVFWVIWVJUBUAWVLWVKYRYCADEUVNUVKUVMLNOQUCWVJUAUBWVIUVJ
        UVI $.
    $}

    catciso.i $e |- I = ( Iso ` C ) $.
    $( A functor is an isomorphism of categories if and only if it is full and
       faithful, and is a bijection on the objects.  Remark 3.28(2) in [Adamek]
       p. 34.  Note that "catciso.u" is redundant thanks to ~ elbasfv .
       (Contributed by Mario Carneiro, 29-Jan-2017.) $)
    catciso $p |- ( ph -> ( F e. ( X I Y ) <->
      ( F e. ( ( X Full Y ) i^i ( X Faith Y ) ) /\
        ( 1st ` F ) : R -1-1-onto-> S ) ) ) $=
      ( cfv vx vy co wcel cful cfth cin c1st wf1o wa c2nd cop wrel wceq relfunc
      cfunc chom cinv cco ccid csect wbr w3a cdm eqid catccat syl isoval eleq2d
      ccat biimpa wfun adantr invfun funfvbrb mpbid isinv simpld issect catchom
      wb simp1d eleqtrd 1st2nd sylancr cv wral 1st2ndbr simprl simprr funcf2 wf
      simp2d funcf1 ffvelcdmd ccofu simp3d catcco catcid 3eqtr3d fveq2d catcbas
      cidfu fveq1d cofu1 inss2 eqsstrdi sseldd ad2antrr idfu1 oveq12d feq3d cid
      ccom oveqd cofu2nd idfu2nd simprd coeq1d eqtrd fcof1od ralrimivva isffth2
      cres wss sylanbrc df-br sylib eqeltrd cofu1st idfu1st jca ccnv cmpo inss1
      fullfunc sstri sselid eqeltrrd sylibr catcisolem eqbrtrd inviso1 impbida
      ) AGJKHUCZUDZGJKUEUCZJKUFUCZUGZUDZDEGUHTZUIZUJZAUUFUJZUUJUULUUNGUUKGUKTZU
      LZUUIUUNJKUPUCZUMZGUUQUDZGUUPUNZJKUOZUUNGJKCUQTZUCZUUQUUNGUVCUDZGJKCURTZU
      CZTZKJUVBUCZUDZUVGGJKULJCUSTZUCUCZJCUTTZTZUNZUUNGUVGJKCVATZUCVBZUVDUVIUVN
      VCUUNUVPUVGGKJUVOUCVBZUUNGUVGUVFVBZUVPUVQUJUUNGUVFVDZUDZUVRAUUFUVTAUUEUVS
      GABCHUVEJKMUVEVEZAFIUDZCVJUDZPCFILVFVGZQRSVHVIVKUUNUVFVLUVTUVRWAUUNBCUVEJ
      KMUWAAUWCUUFUWDVMZAJBUDZUUFQVMZAKBUDZUUFRVMZVNGUVFVOVGVPUUNBCUVOGUVGUVEJK
      MUWAUWEUWGUWIUVOVEZVQVPZVRUUNBCUVOUVJUVLGUVGUVBJKMUVBVEZUVJVEZUVLVEZUWJUW
      EUWGUWIVSVPZWBAUVCUUQUNUUFABCFUVBIJKLMPUWLQRVTVMWCZGUUQWDZWEUUNUUKUUOUUIV
      BZUUPUUIUDZUUNUUKUUOUUQVBZUAWFZUBWFZJUQTZUCZUXAUUKTZUXBUUKTZKUQTZUCZUXAUX
      BUUOUCZUIZUBDWGUADWGUWRUUNUURUUSUWTUVAUWPGUUQWHWEZUUNUXJUAUBDDUUNUXADUDZU
      XBDUDZUJZUJZUXDUXHUXIUXEUXFUVGUKTZUCZUXODJKUUKUUOUXCUXGUXAUXBNUXCVEZUXGVE
      ZUUNUWTUXNUXKVMZUUNUXLUXMWIZUUNUXLUXMWJZWKUXOUXHUXEUVGUHTZTZUXFUYCTZUXCUC
      ZUXQWLUXHUXDUXQWLUXOEKJUYCUXPUXGUXCUXEUXFOUXSUXRUUNUYCUXPKJUPUCZVBZUXNUUN
      UYGUMUVGUYGUDZUYHKJUOUUNUVGUVHUYGUUNUVDUVIUVNUWOWMAUVHUYGUNUUFABCFUVBIKJL
      MPUWLRQVTVMWCZUVGUYGWHWEZVMUXODEUXAUUKUXODEJKUUKUUONOUXTWNZUYAWOZUXODEUXB
      UUKUYLUYBWOZWKUXOUYFUXDUXQUXHUXOUYDUXAUYEUXBUXCUXOUXAUVGGWPUCZUHTZTUXAJXC
      TZUHTZTUYDUXAUXOUXAUYPUYRUXOUYOUYQUHUUNUYOUYQUNUXNUUNUVKUVMUYOUYQUUNUVDUV
      IUVNUWOWQUUNBCUVJFGUVGIJKJLMAUWBUUFPVMZUWMUWGUWIUWGUWPUYJWRAUVMUYQUNUUFAB
      CFUVLUYQIJLMUWNUYQVEZPQWSVMWTZVMZXAZXDUXODJKJGUVGUXANUUNUUSUXNUWPVMZUUNUY
      IUXNUYJVMZUYAXEUXODJUYQUXAUYTNAJVJUDZUUFUXNABVJJABFVJUGVJABCFILMPXBFVJXFX
      GZQXHZXIZUYAXJWTZUXOUXBUYPTUXBUYRTUYEUXBUXOUXBUYPUYRVUCXDUXODJKJGUVGUXBNV
      UDVUEUYBXEUXODJUYQUXBUYTNVUIUYBXJWTZXKXLVPUXOUXAUXBUYOUKTZUCUXAUXBUYQUKTZ
      UCUXQUXIXNXMUXDYDUXOVULVUMUXAUXBUXOUYOUYQUKVUBXAXOUXODJKJGUVGUXAUXBNVUDVU
      EUYAUYBXPUXODJUXCUYQUXAUXBUYTNVUIUXRUYAUYBXQWTUXOUXEUXFGUVGWPUCZUKTZUCZUX
      EUXFKXCTZUKTZUCUXIUXQXNZXMUXHYDUXOVUOVURUXEUXFUXOVUNVUQUKUUNVUNVUQUNUXNUU
      NGUVGKJULKUVJUCUCZKUVLTZVUNVUQUUNUVIUVDVUTVVAUNZUUNUVQUVIUVDVVBVCUUNUVPUV
      QUWKXRUUNBCUVOUVJUVLUVGGUVBKJMUWLUWMUWNUWJUWEUWIUWGVSVPWQUUNBCUVJFUVGGIKJ
      KLMUYSUWMUWIUWGUWIUYJUWPWRAVVAVUQUNUUFABCFUVLVUQIKLMUWNVUQVEZPRWSVMWTZVMX
      AXOUXOVUPUYDUYEUUOUCZUXQXNVUSUXOEKJKUVGGUXEUXFOVUEVUDUYMUYNXPUXOVVEUXIUXQ
      UXOUYDUXAUYEUXBUUOVUJVUKXKXSXTUXOEKUXGVUQUXEUXFVVCOUXOBVJKABVJYEUUFUXNVUG
      XIAUWHUUFUXNRXIXHUXSUYMUYNXQWTYAYBUAUBDJKUUKUUOUXCUXGNUXRUXSYCYFUUKUUOUUI
      YGZYHYIUUNDEUUKUYCUUNDEJKUUKUUONOUXKWNUUNEDKJUYCUXPONUYKWNUUNUYPUYRUYCUUK
      XNXMDYDUUNUYOUYQUHVUAXAUUNDJKJGUVGNUWPUYJYJUUNDJUYQUYTNAVUFUUFVUHVMYKWTUU
      NVUNUHTVUQUHTUUKUYCXNXMEYDUUNVUNVUQUHVVDXAUUNEKJKUVGGOUYJUWPYJUUNEKVUQVVC
      OAKVJUDUUFABVJKVUGRXHVMYKWTYAYLAUUMUJZBCGUUKYMZUAUBEEUXAVVHTUXBVVHTUUOUCY
      MYNZULZHUVEJKMUWAAUWCUUMUWDVMAUWFUUMQVMZAUWHUUMRVMZSVVGGUUPVVJUVFVVGUURUU
      SUUTUVAVVGUUIUUQGUUIUUGUUQUUGUUHYOJKYPYQAUUJUULWIZYRUWQWEZVVGUAUBBCDEFUUK
      UUOVVIUVEIJKLMNOAUWBUUMPVMVVKVVLUWAVVIVEVVGUWSUWRVVGGUUPUUIVVNVVMYSVVFYTA
      UUJUULWJUUAUUBUUCUUD $.
  $}

  ${
    catcbascl.c $e |- C = ( CatCat ` U ) $.
    catcbascl.b $e |- B = ( Base ` C ) $.
    catcbascl.u $e |- ( ph -> U e. WUni ) $.
    catcbascl.x $e |- ( ph -> X e. B ) $.
    $( An element of the base set of the category of categories for a weak
       universe belongs to the weak universe.  Formerly part of the proof for
       ~ catcoppccl .  (Contributed by AV, 14-Oct-2024.) $)
    catcbascl $p |- ( ph -> X e. U ) $=
      ( ccat cin cwun catcbas eleqtrd elin1d ) ADJEAEBDJKIABCDLFGHMNO $.

    ${
      catcslotelcl.e $e |- E = Slot ( E ` ndx ) $.
      $( A slot entry of an element of the base set of the category of
         categories for a weak universe belongs to the weak universe.  Formerly
         part of the proof for ~ catcoppccl .  (Contributed by AV,
         14-Oct-2024.) $)
      catcslotelcl $p |- ( ph -> ( E ` X ) e. U ) $=
        ( cnx cfv catcbascl wunstr ) AFDELEMKIABCDFGHIJNO $.
    $}

    $( The base set of an element of the base set of the category of categories
       for a weak universe belongs to the weak universe.  Formerly part of the
       proof for ~ catcoppccl .  (Contributed by AV, 14-Oct-2024.) $)
    catcbaselcl $p |- ( ph -> ( Base ` X ) e. U ) $=
      ( cbs baseid catcslotelcl ) ABCDJEFGHIKL $.

    $( The Hom-set of an element of the base set of the category of categories
       for a weak universe belongs to the weak universe.  Formerly part of the
       proof for ~ catcoppccl .  (Contributed by AV, 14-Oct-2024.) $)
    catchomcl $p |- ( ph -> ( Hom ` X ) e. U ) $=
      ( chom homid catcslotelcl ) ABCDJEFGHIKL $.

    $( The composition operation of an element of the base set of the category
       of categories for a weak universe belongs to the weak universe.
       Formerly part of the proof for ~ catcoppccl .  (Contributed by AV,
       14-Oct-2024.) $)
    catcccocl $p |- ( ph -> ( comp ` X ) e. U ) $=
      ( cco ccoid catcslotelcl ) ABCDJEFGHIKL $.
  $}

  ${
    $d x y ph $.  $d x y X $.
    catcoppccl.c $e |- C = ( CatCat ` U ) $.
    catcoppccl.b $e |- B = ( Base ` C ) $.
    catcoppccl.o $e |- O = ( oppCat ` X ) $.
    catcoppccl.1 $e |- ( ph -> U e. WUni ) $.
    catcoppccl.2 $e |- ( ph -> _om e. U ) $.
    catcoppccl.3 $e |- ( ph -> X e. B ) $.
    $( The category of categories for a weak universe is closed under taking
       opposites.  (Contributed by Mario Carneiro, 12-Jan-2017.)  (Proof
       shortened by AV, 13-Oct-2024.) $)
    catcoppccl $p |- ( ph -> O e. B ) $=
      ( vx vy ccat cnx cfv cxp wcel wss cin chom ctpos cop csts co cco cbs c2nd
      c1st cmpo wceq eqid oppcval syl catcbascl wunndx wunstr catchomcl wuntpos
      cv homid wunop wunsets ccoid crn cuni cdm ccnv c0 csn cun cpw catcbaselcl
      wunxp catcccocl wunrn wununi wundm wuncnv wun0 wunsn wunun wunpw tposssxp
      wral wf ovssunirn dmss ax-mp cnvss unss1 mp2b rnssi xpss12 mp2an sstri wb
      elpw2g mpbiri ralrimivw fmpo sylib eqeltrd catcbas eleqtrd elin2d oppccat
      wunf cwun elind eleqtrrd ) AEDOUAZBADOEAEFPUBQZFUBQZUCZUDZUEUFZPUGQZMNFUH
      QZXTRZXTNVAMVAZUIQUDZYBUJQZFUGQZUFZUCZUKZUDZUEUFZDAFBSEYJULLNMXTFYEXOEBXT
      UMXOUMYEUMIUNUOAYIXRDJAXQFDJABCDFGHJLUPAXNXPDJAPDUBXNVBJADJKUQZURAXODJABC
      DFGHJLUSUTVCVDAXSYHDJAPDUGXSVEJYKURAYAXTRZYEVFZVGZVHZVIZVJVKZVLZYNVFZRZVM
      ZDYHJAYAXTDJAXTXTDJABCDFGHJLVNZUUBVOUUBVOAYTDJAYRYSDJAYPYQDJAYODJAYNDJAYM
      DJAYEDJABCDFGHJLVPVQVRZVSVTAVJDJADJWAWBWCAYNDJUUCVQVOZWDAYGUUASZNXTWFZMYA
      WFYLUUAYHWGAUUFMYAAUUENXTAUUEYGYTTZYGYFVHZVIZYQVLZYFVFZRZYTYFWEUUJYRTZUUK
      YSTUULYTTUUHYOTZUUIYPTUUMYFYNTUUNYEYCYDWHZYFYNWIWJUUHYOWKUUIYPYQWLWMYFYNU
      UOWNUUJYRUUKYSWOWPWQAYTDSUUEUUGWRUUDYGYTDWSUOWTXAXAMNYAXTYGUUAYHYHUMXBXCX
      IVCVDXDAFOSEOSADOFAFBXMLABCDXJGHJXEZXFXGFEIXHUOXKUUPXL $.
  $}

  ${
    $d a b f g h v x ph $.  $d a b f g h v x X $.  $d a b f g h v x Y $.
    catcfuccl.c $e |- C = ( CatCat ` U ) $.
    catcfuccl.b $e |- B = ( Base ` C ) $.
    catcfuccl.o $e |- Q = ( X FuncCat Y ) $.
    catcfuccl.u $e |- ( ph -> U e. WUni ) $.
    catcfuccl.1 $e |- ( ph -> _om e. U ) $.
    catcfuccl.x $e |- ( ph -> X e. B ) $.
    catcfuccl.y $e |- ( ph -> Y e. B ) $.
    $( The category of categories for a weak universe is closed under the
       functor category operation.  (Contributed by Mario Carneiro,
       12-Jan-2017.)  (Proof shortened by AV, 14-Oct-2024.) $)
    catcfuccl $p |- ( ph -> Q e. B ) $=
      ( cfv co cv eqid wcel cvv vv vh vf vg vb va vx ccat cin cnx cbs cfunc cop
      chom cnat cco cxp c1st c2nd cmpt cmpo csb ctp cwun catcbas eleqtrd elin2d
      eqidd fucval baseid wunndx wunstr catcbascl wunfunc wunop homid ccoid crn
      wunnat cuni cpw cpm wunxp catcccocl wunrn wununi wunpw catcbaselcl wunmap
      cmap wunpm wf wral fvex wsbc wss ovex rnex uniex xpex ovssunirn rnss mp2b
      uniss sstri elpw mpbir a1i fmpti pwex elmap rgen2w fmpo mpbi xpss12 mp2an
      elpm2r mp4an sbcth sbcel1g mpbid ax-mp wunf wuntp eqeltrd fuccat eleqtrrd
      elind ) ADEUHUIZBAEUHDADUJUKOZFGULPZUMZUJUNOZFGUOPZUMZUJUPOZUAUBYKYKUQZYK
      UCUAQZUROZUDYRUSOZUEUFUDQZUBQZYNPZUCQZUUAYNPZUGFUKOZUGQZUEQOZUUGUFQOZUUGU
      UDUROOUUGUUAUROOUMZUUGUUBUROOZGUPOZPZPZUTZVAZVBZVBZVAZUMZVCEAUGUAUUFYKFGD
      UUSUULUCUDUBYNUFUEJYKRYNRUUFRUULRAEUHFAFBYIMABCEVDHIKVEZVFVGZAEUHGAGBYINU
      VAVFVGZAUUSVHVIAYLYOUUTEKAYJYKEKAUJEUKYJVJKAEKLVKZVLAFGEKABCEFHIKMVMZABCE
      GHIKNVMZVNZVOAYMYNEKAUJEUNYMVPKUVDVLAFGEKUVEUVFVSZVOAYPUUSEKAUJEUPYPVQKUV
      DVLAYQYKUQZUULVRZVTZVRZVTZWAZUUFWJPZYNVRZVTZUVQUQZWBPZEUUSKAYQYKEKAYKYKEK
      UVGUVGWCUVGWCAUVOUVREKAUVNUUFEKAUVMEKAUVLEKAUVKEKAUVJEKAUULEKABCEGHIKNWDW
      EWFWEWFWGABCEFHIKMWHWIAUVQUVQEKAUVPEKAYNEKUVHWEWFZUVTWCWKUVIUVSUUSWLZAUUR
      UVSSZUBYKWMUAYQWMUWAUWBUAUBYQYKYSTSZUWBYRURWNUWCUUQUVSSZUCYSWOUWBUWDUCYST
      YTTSZUWDYRUSWNUWEUUPUVSSZUDYTWOUWDUWFUDYTTUVOTSUVRTSUUCUUEUQZUVOUUPWLZUWG
      UVRWPZUWFUVNUUFWJWQUVQUVQUVPYNFGUOWQWRWSZUWJWTUUOUVOSZUFUUEWMUEUUCWMUWHUW
      KUEUFUUCUUEUWKUUFUVNUUOWLUGUUFUVNUUNUUOUUORUUNUVNSZUUGUUFSUWLUUNUVMWPUUNU
      UMVRZVTZUVMUUMUUHUUIXAUUMUVKWPUWMUVLWPUWNUVMWPUULUUJUUKXAUUMUVKXBUWMUVLXD
      XCXEUUNUVMUUHUUIUUMWQXFXGXHXIUVNUUFUUOUVMUVLUVKUVJUULGUPWNWRWSWRWSXJFUKWN
      XKXGXLUEUFUUCUUEUUOUVOUUPUUPRXMXNUUCUVQWPUUEUVQWPUWIYNUUAUUBXAYNUUDUUAXAU
      UCUVQUUEUVQXOXPUVOUVRUWGUUPTTXQXRXSUDYTUUPUVSTXTYAYBXSUCYSUUQUVSTXTYAYBXL
      UAUBYQYKUURUVSUUSUUSRXMXNXHYCVOYDYEAFGDJUVBUVCYFYHUVAYG $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  The category of extensible structures
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
The "category of extensible structures" ` ExtStrCat ` is the category of all
sets in a universe regarded as extensible structures and the functions between
their base sets, see ~ df-estrc .

Since we consider only "small categories" (i.e. categories whose objects and
morphisms are actually sets and not proper classes), the objects of the
category (i.e. the base set of the category regarded as extensible structure)
are all sets in a universe ` u `, which can be an arbitrary set, see
~ estrcbas .  Generally, we will take ` u ` to be a weak universe or
Grothendieck universe, because these sets have closure properties as good as
the real thing.  If a set is not a real extensible structure, it is regarded as
extensible structure with an empty base set.  Because of ~ bascnvimaeqv we do
not need to restrict the universe to sets which "have a base".  The morphisms
(or arrows) between two objects, i.e. sets from the universe, are the mappings
between their base sets, see ~ estrchomfval , whereas the composition
is the ordinary composition of functions, see ~ estrccofval and ~ estrcco .

It is shown that the category of extensible structures ` ExtStrCat ` is
actually a category, see ~ estrccat with the identity function as identity
arrow, see ~ estrcid .

In the following, some background information about the category of extensible
structures is given, taken from the discussion in Github issue #1507
(see ~ https://github.com/metamath/set.mm/issues/1507 ):

At the beginning, the categories of non-unital rings ` RngCat ` and unital
rings ` RingCat ` were defined separately (as unordered triples of ordered
pairs, see ~ dfrngc2 and ~ dfringc2 , but with special compositions).  With
this definitions, however, Theorem ~ rngcresringcat could not be proven,
because the compositions were not compatible.  Unfortunately, no precise
definition of the composition within the category of rings could be found in
the literature.  In section 3.3 EXAMPLES, paragraph (2) of [Adamek] p. 22,
however, a definition is given for "Grp", the category of groups:  "The
following constructs; i.e., categories of structured sets and
structure-preserving functions between them (o will always be the _composition
of functions_ and id_A will always be the identity function on A): ... (b) Grp
with objects all groups and morphisms all homomorphisms between them."
Therefore, the compositions should have been harmonized by using the
composition of the category of sets ` SetCat `, see ~ df-setc , which is the
ordinary composition of functions.  Analogously, categories of Rngs (and Rings)
could have been shown to be restrictions resp. subcategories of the category of
sets.

BJ and MC observed, however, that "... ` |``cat ` [cannot be used] to restrict
the category Set to Ring, because the homs are different.  Although Ring is a
concrete category, a hom between rings R and S is a function
(Base``R) --> (Base``S) with certain properties, unlike in Set where it is a
function R --> S.".  Therefore, MC suggested that "we could have an alternative
version of the Set category consisting of extensible structures (in U) together
with (A Hom B) := (Base``A) --> (Base``B).  This category is not isomorphic to
Set because different extensible structures can have the same base set, but it
is equivalent to Set; the relevant functors are (U``A) = (Base``A), the
forgetful functor, and (F``A) = { <. (Base``ndx), A >. }".  This led to the
current definition of ` ExtStrCat `, see ~ df-estrc .  The claimed equivalence
is proven by ~ equivestrcsetc .  Having a definition of a category of
extensible structures, the categories of non-unital and unital rings can be
defined as appropriate restrictions of the category of extensible structures,
see ~ df-rngc and ~ df-ringc .

In the same way, more subcategories could be provided, resulting in the
following "inclusion chain" by proving theorems like ~ rngcresringcat ,
although the morphisms of the shown categories are different ( "->" means "is
subcategory of"):

` RingCat ` -> ` RngCat ` -> GrpCat -> MndCat -> MgmCat -> ` ExtStrCat `

According to MC, "If we generalize from subcategories to embeddings, then we
can even fit ` SetCat ` into the chain, equivalent to ` ExtStrCat ` at the
end."  As mentioned before, the equivalence of ` SetCat ` and ` ExtStrCat ` is
proven by ~ equivestrcsetc .  Furthermore, it can be shown that ` SetCat ` is
_embedded_ into ` ExtStrCat `, see ~ embedsetcestrc .

Remark: ~ equivestrcsetc as well as ~ embedsetcestrc require that the index of
the base set extractor is contained within the considered universe.  This is
ensured by assuming that the natural numbers are contained within the
considered universe: ` _om e. U ` (see ~ wunndx ), but it would be currently
sufficient to assume that ` 1 e. U `, because the index value of the base set
extractor is hard-coded as ` 1 `, see ~ basendx .

Some people, however, feel uncomfortable to say that a ring "is a" group
(without mentioning the restriction to the addition, which is usually found in
the literature, e.g., the definition of a ring in [Herstein] p. 126: "... Note
that so far all we have said is that R is an abelian group under +.".  The main
argument against a ring being a group is the number of components/slots:
usually, a group consists of (exactly!) two components (a base set and an
operation), whereas a ring consists of (exactly!) three components (a base set
and two operations). According to this "definition", a ring cannot be a group.

This is also an (unfortunately informal) argument for the category of rings not
being a subcategory of the category of abelian groups in "Categories and
Functors", Bodo Pareigis, Academic Press, New York, London, 1970: "A category A
is called a subcategory of a category B if Ob(A) ` C_ ` Ob(B) and
Mor_A(X,Y) ` C_ ` Mor_B(X,Y) for all X,Y e. Ob(A), if the composition of
morphisms in A coincides with the composition of the same morphisms in B and if
the identity of an object in A is also the identity of the same object viewed
as an object in B. Then there is a forgetful functor from A to B.  We note that
Ri [the category of rings] _is not a subcategory_ of Ab [the category of
abelian groups]. In fact, Ob(Ri) ` C_ ` Ob(Ab) is not true, although every ring
can also be regarded as an abelian group.  The corresponding abelian groups of
two rings may coincide even if the rings do not coincide. The multiplication
may be defined differently.".

As long as we define Rings, Groups, etc. in a way that ` A e. Ring -> `
` A e. Grp ` is valid (see ~ ringgrp ) the corresponding categories are in a
subcategory relation. If we do not want Rings to be Groups (then the category
of rings would not be a subcategory of the category of groups, as observed by
Pareigis), we would have to change the definitions of Magmas, Monoids, Groups,
Rings etc. to restrict them to have exactly the required number of slots, so
that the following holds

` g e. Grp -> g Struct <. ( Base `` ndx ) , ( +g `` ndx ) >. `

` r e. Ring -> r Struct <. ( Base `` ndx ) , ( +g `` ndx ) , ( .r `` ndx ) >. `
$)

  ${
    $d F x y $.
    $( The inverse images of the universal class ` _V ` under functions on the
       universal class ` _V ` are the universal class ` _V ` itself.  (Proposed
       by Mario Carneiro, 7-Mar-2020.)  (Contributed by AV, 7-Mar-2020.) $)
    fncnvimaeqv $p |- ( F Fn _V -> ( `' F " _V ) = _V ) $=
      ( vy vx cvv wfn ccnv cima cv cfv wcel fncnvima2 wa weq fveq2 eleq1d elrab
      crab fvexd biantrud bitr4id eqrdv eqtrd ) ADEZAFDGBHZAIZDJZBDQZDBDDAKUCCU
      GDUCCHZUGJUHDJZUHAIZDJZLUIUFUKBUHDBCMUEUJDUDUHANOPUCUKUIUCUHARSTUAUB $.
  $}

  $( The inverse image of the universal class ` _V ` under the base function is
     the universal class ` _V ` itself.  (Proposed by Mario Carneiro,
     7-Mar-2020.)  (Contributed by AV, 7-Mar-2020.) $)
  bascnvimaeqv $p |- ( `' Base " _V ) = _V $=
    ( cbs cvv wfn ccnv cima wceq basfn fncnvimaeqv ax-mp ) ABCADBEBFGAHI $.

  $c ExtStrCat $.

  $( Extend class notation to include the category ExtStr. $)
  cestrc $a class ExtStrCat $.

  ${
    $d f g u v x y z $.
    $( Definition of the category ExtStr of extensible structures.  This is the
       category whose objects are all sets in a universe ` u ` regarded as
       extensible structures and whose morphisms are the functions between
       their base sets.  If a set is not a real extensible structure, it is
       regarded as extensible structure with an empty base set.  Because of
       ~ bascnvimaeqv we do not need to restrict the universe to sets which
       "have a base".  Generally, we will take ` u ` to be a weak universe or
       Grothendieck universe, because these sets have closure properties as
       good as the real thing.  (Proposed by Mario Carneiro, 5-Mar-2020.)
       (Contributed by AV, 7-Mar-2020.) $)
    df-estrc $a |- ExtStrCat = ( u e. _V |->
         { <. ( Base ` ndx ) , u >. ,
           <. ( Hom ` ndx ) ,
              ( x e. u , y e. u |-> ( ( Base ` y ) ^m ( Base ` x ) ) ) >. ,
           <. ( comp ` ndx ) , ( v e. ( u X. u ) , z e. u
                |-> ( g e. ( ( Base ` z ) ^m ( Base ` ( 2nd ` v ) ) ) ,
                      f e. ( ( Base ` ( 2nd ` v ) ) ^m ( Base ` ( 1st ` v ) ) )
                      |-> ( g o. f ) ) ) >. } ) $.

    $d u v x y z ph $.  $d u v x y z U $.  $d u .x. $.  $d u H $.
    estrcval.c $e |- C = ( ExtStrCat ` U ) $.
    estrcval.u $e |- ( ph -> U e. V ) $.
    estrcval.h $e |- ( ph -> H = ( x e. U , y e. U
                                   |-> ( ( Base ` y ) ^m ( Base ` x ) ) ) ) $.
    estrcval.o $e |- ( ph -> .x. = ( v e. ( U X. U ) , z e. U |->
                    ( g e. ( ( Base ` z ) ^m ( Base ` ( 2nd ` v ) ) ) ,
                      f e. ( ( Base ` ( 2nd ` v ) ) ^m ( Base ` ( 1st ` v ) ) )
                      |-> ( g o. f ) ) ) ) $.
    $( Value of the category of extensible structures (in a universe).
       (Contributed by AV, 7-Mar-2020.) $)
    estrcval $p |- ( ph -> C = { <. ( Base ` ndx ) , U >. ,
                                 <. ( Hom ` ndx ) , H >. ,
                                 <. ( comp ` ndx ) , .x. >. } ) $=
      ( cfv cbs cop cv cestrc cnx chom cco ctp cmap cmpo cxp c2nd c1st ccom cvv
      vu co df-estrc wceq simpr opeq2d eqidd mpoeq123dv adantr sqxpeqd tpeq123d
      wa eqtr4d elexd wcel tpex a1i fvmptd2 eqtrid ) AFHUAQUBRQZHSZUBUCQZKSZUBU
      DQZGSZUEZMAUMHVLUMTZSZVNBCVSVSCTRQBTRQUFUNZUGZSZVPEDVSVSUHZVSJIDTRQETZUIQ
      RQZUFUNWFWEUJQRQUFUNJTITUKUGZUGZSZUEVRULUAULBCDEUMIJUOAVSHUPZVDZVTVMWCVOW
      IVQWKVSHVLAWJUQZURWKWBKVNWKWBBCHHWAUGZKWKBCVSVSWAHHWAWLWLWKWAUSUTAKWMUPWJ
      OVAVEURWKWHGVPWKWHEDHHUHZHWGUGZGWKEDWDVSWGWNHWGWKVSHWLVBWLWKWGUSUTAGWOUPW
      JPVAVEURVCAHLNVFVRULVGAVMVOVQVHVIVJVK $.
  $}

  ${
    $d f g v x y z $.  $d v x y z ph $.  $d v x y z U $.
    estrcbas.c $e |- C = ( ExtStrCat ` U ) $.
    estrcbas.u $e |- ( ph -> U e. V ) $.
    $( Set of objects of the category of extensible structures (in a universe).
       (Contributed by AV, 7-Mar-2020.) $)
    estrcbas $p |- ( ph -> U = ( Base ` C ) ) $=
      ( vx vy vv vz vg vf cnx cbs cfv cop cv cmap co cmpo chom cco cxp c2nd ctp
      c1st ccom wcel wceq c1 cdc catstr baseid snsstp1 strfv syl eqidd estrcval
      c5 fveq2d eqtr4d ) ACMNOCPZMUAOGHCCHQNOGQNORSTZPZMUBOIJCCUCCKLJQNOIQZUDON
      OZRSVFVEUFONORSKQLQUGTTZPZUEZNOZBNOACDUHCVJUIFCVINDUJUJUSUKPVGCVCULUMVBVD
      VHUNUOUPABVINAGHJIBVGCLKVCDEFAVCUQAVGUQURUTVA $.

    ${
      estrchomfval.h $e |- H = ( Hom ` C ) $.
      $( Set of morphisms ("arrows") of the category of extensible structures
         (in a universe).  (Contributed by AV, 7-Mar-2020.) $)
      estrchomfval $p |- ( ph -> H = ( x e. U , y e. U
                                    |-> ( ( Base ` y ) ^m ( Base ` x ) ) ) ) $=
        ( vv vz vg vf cv cbs cfv cmap co cop cmpo cnx chom cco cxp c2nd ctp cvv
        c1st ccom c1 c5 cdc eqidd estrcval catstr homid snsstp2 mpoexga syl2anc
        wcel strfv3 ) AFBCEECOPQBOPQRSZUAZUBPQETZUBUCQVDTZUBUDQKLEEUEEMNLOPQKOZ
        UFQPQZRSVHVGUIQPQRSMONOUJUAUAZTZUGDUCUHUKUKULUMTABCLKDVIENMVDGHIAVDUNAV
        IUNUOVIEVDUPUQVEVFVJURAEGVAZVKVDUHVAIIBCEEVCGGUSUTJVB $.

      $d x y A $.  $d x y B $.  $d x y X $.  $d x y Y $.
      estrchom.x $e |- ( ph -> X e. U ) $.
      estrchom.y $e |- ( ph -> Y e. U ) $.
      estrchom.a $e |- A = ( Base ` X ) $.
      estrchom.b $e |- B = ( Base ` Y ) $.
      $( The morphisms between extensible structures are mappings between their
         base sets.  (Contributed by AV, 7-Mar-2020.) $)
      estrchom $p |- ( ph -> ( X H Y ) = ( B ^m A ) ) $=
        ( vx cbs cfv cmap vy cv co cvv estrchomfval wa fveq2 oveqan12rd oveq12i
        wceq eqtr4di adantl ovexd ovmpod ) AQUAHIEEUAUBZRSZQUBZRSZTUCZCBTUCZFUD
        AQUADEFGJKLUEUQHUJZUOIUJZUFZUSUTUJAVCUSIRSZHRSZTUCUTVBVAUPVDURVETUOIRUG
        UQHRUGUHCVDBVETPOUIUKULMNACBTUMUN $.

      $( A morphism between extensible structures is a function between their
         base sets.  (Contributed by AV, 7-Mar-2020.) $)
      elestrchom $p |- ( ph -> ( F e. ( X H Y ) <-> F : A --> B ) ) $=
        ( co wcel cvv cmap wf estrchom eleq2d cbs fvexi a1i elmapd bitrd ) AFIJ
        GRZSFCBUARZSBCFUBAUJUKFABCDEGHIJKLMNOPQUCUDACBFTTCTSACJUEQUFUGBTSABIUEP
        UFUGUHUI $.
    $}

    ${
      estrcco.o $e |- .x. = ( comp ` C ) $.
      $( Composition in the category of extensible structures.  (Contributed by
         AV, 7-Mar-2020.) $)
      estrccofval $p |- ( ph -> .x. = ( v e. ( U X. U ) , z e. U
          |-> ( g e. ( ( Base ` z ) ^m ( Base ` ( 2nd ` v ) ) ) ,
                f e. ( ( Base ` ( 2nd ` v ) ) ^m ( Base ` ( 1st ` v ) ) )
                |-> ( g o. f ) ) ) ) $=
        ( vx cv cbs cfv cnx cop cvv wcel vy cxp c2nd cmap co c1st ccom cmpo cco
        chom ctp c1 c5 cdc eqid estrchomfval eqidd estrcval ccoid snsstp3 xpexd
        catstr mpoexga syl2anc strfv3 ) AECBFFUBZFHGBNOPCNZUCPOPZUDUEVHVGUFPOPU
        DUEHNGNUGUHZUHZQOPFRZQUJPDUJPZRZQUIPVJRZUKDUISULULUMUNRAMUABCDVJFGHVLIJ
        KAMUADFVLIJKVLUOUPAVJUQURVJFVLVBUSVKVMVNUTAVFSTFITVJSTAFFIIKKVAKCBVFFVI
        SIVCVDLVE $.

      $d f g F $.  $d f g G $.  $d f g v z X $.  $d f g v z Y $.
      $d f g v z Z $.  $d f g ph $.
      estrcco.x $e |- ( ph -> X e. U ) $.
      estrcco.y $e |- ( ph -> Y e. U ) $.
      estrcco.z $e |- ( ph -> Z e. U ) $.
      estrcco.a $e |- A = ( Base ` X ) $.
      estrcco.b $e |- B = ( Base ` Y ) $.
      estrcco.d $e |- D = ( Base ` Z ) $.
      estrcco.f $e |- ( ph -> F : A --> B ) $.
      estrcco.g $e |- ( ph -> G : B --> D ) $.
      $( Composition in the category of extensible structures.  (Contributed by
         AV, 7-Mar-2020.) $)
      estrcco $p |- ( ph -> ( G ( <. X , Y >. .x. Z ) F ) = ( G o. F ) ) $=
        ( vg vf vv vz cbs cfv cmap co cv ccom cop cvv cxp c2nd c1st estrccofval
        cmpo wceq fveq2 adantl simprl fveq2d wcel op2ndg syl2anc adantr oveq12d
        eqtrd op1stg eqidd mpoeq123dv opelxpd ovex mpoex a1i ovmpod simpl simpr
        wa coeq12d wf eqcomd feq23d mpbird fvexd elmapd coexg ) AUEUFIHMUIUJZLU
        IUJZUKULZWMKUIUJZUKULZUEUMZUFUMZUNZIHUNZKLUOZMFULUPAUGUHXAMGGUQGUEUFUHU
        MZUIUJZUGUMZURUJZUIUJZUKULZXFXDUSUJZUIUJZUKULZWSVAUEUFWNWPWSVAZFUPAUHUG
        DFGUFUEJNOPUTAXDXAVBZXBMVBZWCZWCZUEUFXGXJWSWNWPWSXOXCWLXFWMUKXNXCWLVBZA
        XMXPXLXBMUIVCVDVDXOXELUIXOXEXAURUJZLXOXDXAURAXLXMVEZVFAXQLVBZXNAKGVGZLG
        VGZXSQRKLGGVHVIVJVLVFZVKXOXFWMXIWOUKYBXOXIXAUSUJZUIUJZWOXOXHYCUIXOXDXAU
        SXRVFVFAYDWOVBXNAYCKUIAXTYAYCKVBQRKLGGVMVIVFVJVLVKXOWSVNVOAKLGGQRVPSXKU
        PVGAUEUFWNWPWSWLWMUKVQWMWOUKVQVRVSVTWQIVBZWRHVBZWCZWSWTVBAYGWQIWRHYEYFW
        AYEYFWBWDVDAIWNVGZWMWLIWEZAYICEIWEUDAWMWLCEIACWMCWMVBAUAVSWFZAEWLEWLVBA
        UBVSWFWGWHAWLWMIUPUPAMUIWIALUIWIZWJWHZAHWPVGZWOWMHWEZAYNBCHWEUCAWOWMBCH
        ABWOBWOVBATVSWFYJWGWHAWMWOHUPUPYKAKUIWIWJWHZAYHYMWTUPVGYLYOIHWNWPWKVIVT
        $.
    $}
  $}

  ${
    estrcbasbas.c $e |- C = ( ExtStrCat ` U ) $.
    estrcbasbas.b $e |- B = ( Base ` C ) $.
    estrcbasbas.u $e |- ( ph -> U e. WUni ) $.
    $( An element of the base set of the base set of the category of extensible
       structures (i.e. the base set of an extensible structure) belongs to the
       considered weak universe.  (Contributed by AV, 22-Mar-2020.) $)
    estrcbasbas $p |- ( ( ph /\ E e. B ) -> ( Base ` E ) e. U ) $=
      ( wcel cbs cfv cwun estrcbas eqtr4id eleq2d wi wa cnx baseid simpl wunstr
      simpr ex syl sylbid imp ) AEBIZEJKDIZAUGEDIZUHABDEABCJKDGACDLFHMNOADLIZUI
      UHPHUJUIUHUJUIQEDJRJKSUJUITUJUIUBUAUCUDUEUF $.
  $}

  ${
    $d f g h w x y z C $.  $d f g h w x y z U $.  $d f g h w x y z V $.
    estrccat.c $e |- C = ( ExtStrCat ` U ) $.
    $( Lemma for ~ estrccat .  (Contributed by AV, 8-Mar-2020.) $)
    estrccatid $p |- ( U e. V -> ( C e. Cat
                   /\ ( Id ` C ) = ( x e. U |-> ( _I |` ( Base ` x ) ) ) ) ) $=
      ( vw vy wcel cv wa cfv co cbs wf eqid elestrchom cop ccom mpbid estrcco
      vz vf vg vh chom w3a cco cid cres cvv id estrcbas eqidd cestrc fvexi biid
      wf1o f1oi f1of mp1i simpl simpr mpbird simpr1l simpr1r simpr31 wceq fcoi2
      a1i syl eqtrd simpr2l simpr32 fcoi1 syl2anc eqeltrd coass simpr2r simpr33
      fco 3eqtr4a oveq1d oveq2d 3eqtr4d iscatd2 ) CDHZFIZCHZAIZCHZJZGIZCHZUAIZC
      HZJZUBIZWGWIBUEKZLHZUCIZWIWLWRLHZUDIZWLWNWRLHZUFZUFZFAGUACBBUGKZUHWIMKZUI
      ZUBUCUDWRUJWFBCDEWFUKULWFWRUMWFXFUMBUJHWFBCUNEUOVIXEUPWFWJJZXHWIWIWRLHXGX
      GXHNZXGXGXHUQZXJXIXGURZXGXGXHUSZUTXIXGXGBCXHWRDWIWIEWFWJVAWROZWFWJVBZXOXG
      OZXPPVCWFXEJZXHWQWGWIQZWIXFLLXHWQRZWQXQWGMKZXGBXGXFCWQXHDWGWIWIEWFXEVAZXF
      OZWHWJWPXDWFVDZWHWJWPXDWFVEZYDXTOZXPXPXQWSXTXGWQNZWSXAXCWKWPWFVFXQXTXGBCW
      QWRDWGWIEYAXNYCYDYEXPPSZXKXJXQXLXMUTZTXQYFXSWQVGYGXTXGWQVHVJVKXQWTXHWIWIQ
      WLXFLLWTXHRZWTXQXGXGBWLMKZXFCXHWTDWIWIWLEYAYBYDYDWMWOWKXDWFVLZXPXPYJOZYHX
      QXAXGYJWTNZWSXAXCWKWPWFVMXQXGYJBCWTWRDWIWLEYAXNYDYKXPYLPSZTXQYMYIWTVGYNXG
      YJWTVNVJVKXQWTWQXRWLXFLLZWTWQRZWGWLWRLZXQXTXGBYJXFCWQWTDWGWIWLEYAYBYCYDYK
      YEXPYLYGYNTZXQYPYQHXTYJYPNZXQYMYFYSYNYGXTXGYJWTWQVTVOZXQXTYJBCYPWRDWGWLEY
      AXNYCYKYEYLPVCVPXQXBWTRZWQXRWNXFLZLZXBYPWGWLQWNXFLZLZXBWTWIWLQWNXFLLZWQUU
      BLXBYOUUDLXQUUAWQRXBYPRUUCUUEXBWTWQVQXQXTXGBWNMKZXFCWQUUADWGWIWNEYAYBYCYD
      WMWOWKXDWFVRZYEXPUUGOZYGXQYJUUGXBNZYMXGUUGUUANXQXCUUJWSXAXCWKWPWFVSXQYJUU
      GBCXBWRDWLWNEYAXNYKUUHYLUUIPSZYNXGYJUUGXBWTVTVOTXQXTYJBUUGXFCYPXBDWGWLWNE
      YAYBYCYKUUHYEYLUUIYTUUKTWAXQUUFUUAWQUUBXQXGYJBUUGXFCWTXBDWIWLWNEYAYBYDYKU
      UHXPYLUUIYNUUKTWBXQYOYPXBUUDYRWCWDWE $.

    $( The category of extensible structures is a category.  (Contributed by
       AV, 8-Mar-2020.) $)
    estrccat $p |- ( U e. V -> C e. Cat ) $=
      ( vx wcel ccat ccid cfv cid cv cbs cres cmpt wceq estrccatid simpld ) BCF
      AGFAHIEBJEKLIMNOEABCDPQ $.

    $d x X $.  $d x ph $.
    estrcid.o $e |- .1. = ( Id ` C ) $.
    estrcid.u $e |- ( ph -> U e. V ) $.
    estrcid.x $e |- ( ph -> X e. U ) $.
    $( The identity arrow in the category of extensible structures is the
       identity function of base sets.  (Contributed by AV, 8-Mar-2020.) $)
    estrcid $p |- ( ph -> ( .1. ` X ) = ( _I |` ( Base ` X ) ) ) $=
      ( vx cid cv cbs cfv cres cvv ccid wcel wceq cmpt wa estrccatid syl simprd
      ccat eqtrid fveq2 reseq2d adantl fvexd resiexd fvmptd ) AKFLKMZNOZPZLFNOZ
      PZCDQADBROZKCUPUAZHABUFSZUSUTTZACESVAVBUBIKBCEGUCUDUEUGUNFTZUPURTAVCUOUQL
      UNFNUHUIUJJAUQQAFNUKULUM $.
  $}

  ${
    $d U x y $.  $d ph x y $.
    estrchomfn.c $e |- C = ( ExtStrCat ` U ) $.
    estrchomfn.u $e |- ( ph -> U e. V ) $.
    estrchomfn.h $e |- H = ( Hom ` C ) $.
    $( The Hom-set operation in the category of extensible structures (in a
       universe) is a function.  (Contributed by AV, 8-Mar-2020.) $)
    estrchomfn $p |- ( ph -> H Fn ( U X. U ) ) $=
      ( vx vy cxp wfn cv cbs cfv cmap co cmpo eqid ovex fnmpoi fneq1d mpbiri
      estrchomfval ) ADCCKZLIJCCJMNOZIMNOZPQZRZUELIJCCUHUIUISUFUGPTUAAUEDUIAIJB
      CDEFGHUDUBUC $.

    $( The functionalized Hom-set operation equals the Hom-set operation in the
       category of extensible structures (in a universe).  (Contributed by AV,
       8-Mar-2020.) $)
    estrchomfeqhom $p |- ( ph -> ( Homf ` C ) = H ) $=
      ( cbs cfv cxp chomf wceq estrchomfn estrcbas eqcomd sqxpeqd fneq2d eqid
      wfn mpbird fnhomeqhomf syl ) ADBIJZUDKZTZBLJZDMAUFDCCKZTABCDEFGHNAUEUHDAU
      DCACUDABCEFGOPQRUAUDBUGDUGSUDSHUBUC $.
  $}

  ${
    estrres.c $e |- ( ph -> C = { <. ( Base ` ndx ) , B >. ,
                                 <. ( Hom ` ndx ) , H >. ,
                                 <. ( comp ` ndx ) , .x. >. } ) $.
    estrres.b $e |- ( ph -> B e. V ) $.
    $( Lemma 1 for ~ estrres .  (Contributed by AV, 14-Mar-2020.)  (Proof
       shortened by AV, 28-Oct-2024.) $)
    estrreslem1 $p |- ( ph -> B = ( Base ` C ) ) $=
      ( cbs cfv cnx cop chom cco ctp fveq2d cvv baseid wcel wne tpex strfvnd wa
      a1i wceq fvexd w3a slotsbhcdif 3simpa mp1i fvtp1g syl21anc 3eqtrrd ) ACIJ
      KIJZBLZKMJZELZKNJZDLZOZIJUNUTJZBACUTIGPAUTIUNQRUTQSAUOUQUSUAUDUBAUNQSBFSU
      NUPTZUNURTZUCZVABUEAKIUFHVBVCUPURTZUGVDAUHVBVCVEUIUJUNUPURBEDQFUKULUM $.

    estrres.h $e |- ( ph -> H e. X ) $.
    estrres.x $e |- ( ph -> .x. e. Y ) $.
    $( Lemma 2 for ~ estrres .  (Contributed by AV, 14-Mar-2020.) $)
    estrreslem2 $p |- ( ph -> ( Base ` ndx ) e. dom C ) $=
      ( cnx cfv cdm wcel wceq cop cun a1i cbs chom cco ctp w3o eqidd 3mix1d cvv
      wb fvex eltpg mp1i mpbird cpr csn df-tp dmeqd dmpropg syl2anc dmsnopg syl
      dmun uneq12d 3eqtrd 3eqtr4d eleqtrrd ) AMUANZVGMUBNZMUCNZUDZCOZAVGVJPZVGV
      GQZVGVHQZVGVIQZUEZAVMVNVOAVGUFUGVGUHPVLVPUIAMUAUJVGVGVHVIUHUKULUMAVGBRZVH
      ERZVIDRZUDZOZVGVHUNZVIUOZSZVKVJAWAVQVRUNZVSUOZSZOZWEOZWFOZSZWDAVTWGVTWGQA
      VQVRVSUPTUQWHWKQAWEWFVBTAWIWBWJWCABFPEGPWIWBQJKVGBVHEFGURUSADHPWJWCQLVIDH
      UTVAVCVDACVTIUQVJWDQAVGVHVIUPTVEVF $.

    estrres.g $e |- ( ph -> G e. W ) $.
    estrres.u $e |- ( ph -> A C_ B ) $.
    $( Any restriction of a category (as an extensible structure which is an
       unordered triple of ordered pairs) is an unordered triple of ordered
       pairs.  (Contributed by AV, 15-Mar-2020.)  (Revised by AV,
       3-Jul-2022.) $)
    estrres $p |- ( ph -> ( ( C |`s A ) sSet <. ( Hom ` ndx ) , G >. )
                             = { <. ( Base ` ndx ) , A >. ,
                                 <. ( Hom ` ndx ) , G >. ,
                                 <. ( comp ` ndx ) , .x. >. } ) $=
      ( cnx cvv wcel cress chom cfv cop csts csn cdif cres cun cbs cco ctp wceq
      ovex setsval sylancr eqid tpex eqeltrdi wfun w3a fvex 3pm3.2i slotsbhcdif
      co wne a1i funtpg syl131anc funeqd mpbird estrreslem2 estrreslem1 sseqtrd
      ressval3d reseq1d uneq1d cpr ssexd syl2anc fvexd elexd simp1 necomd simp2
      mp1i tpres df-tp eqtr4di simp3 eqtrd tprot eqtr3i eqtrdi 3eqtrd ) ADBUAVE
      ZRUBUCZFUDZUEVEZWPSWQUFUGZUHZWRUFZUIZDRUJUCZBUDZUEVEZWTUHZXBUIZXEWRRUKUCZ
      EUDZULZAWPSTFITWSXCUMDBUAUNPWQFWPSIUOUPAXAXGXBAWPXFWTABDUJUCZWPDXDSWPUQXL
      UQXDUQADXDCUDZWQGUDZXJULZSLXMXNXJURUSZADUTXOUTZAXDSTZWQSTZXISTZVAZCHTGJTE
      KTXDWQVFZXDXIVFZWQXIVFZVAZXQYAAXRXSXTRUJVBRUBVBRUKVBVCVGMNOYEAVDVGCGESHJK
      SSXDWQXIVHVIADXOLVJVKACDEGHJKLMNOVLABCXLQACDEGHLMVMVNVOVPVQAXHXJXEVRZXBUI
      ZXKAXGYFXBAXGDSXDUFUGUHZXEUFZUIZWTUHYFAXFYJWTADSTBSTXFYJUMXPABCHMQVSZXDBD
      SSUOVTVPAWQXIXDGYJEBSAYJXNXJVRZYIUIXNXJXEULAYHYLYIAXDWQXICDGESLARUBWAARUK
      WAZAGJNWBAEKOWBZYEWQXDVFAVDYEXDWQYBYCYDWCZWDWFYEXIXDVFAVDYEXDXIYBYCYDWEWD
      WFWGVQXNXJXEWHWIYMARUJWAYNYKYEXIWQVFAVDYEWQXIYBYCYDWJWDWFYEYBAVDYOWFWGWKV
      QXJXEWRULYGXKXJXEWRWHXJXEWRWLWMWNWO $.
  $}

  ${
    $d B x $.  $d X x $.  $d ph x $.
    funcestrcsetc.e $e |- E = ( ExtStrCat ` U ) $.
    funcestrcsetc.s $e |- S = ( SetCat ` U ) $.
    funcestrcsetc.b $e |- B = ( Base ` E ) $.
    funcestrcsetc.c $e |- C = ( Base ` S ) $.
    funcestrcsetc.u $e |- ( ph -> U e. WUni ) $.
    funcestrcsetc.f $e |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) ) $.
    $( Lemma 1 for ~ funcestrcsetc .  (Contributed by AV, 22-Mar-2020.) $)
    funcestrcsetclem1 $p |- ( ( ph /\ X e. B ) -> ( F ` X ) = ( Base ` X ) ) $=
      ( wcel wa cbs cfv wceq cv cvv cmpt adantr fveq2 adantl simpr fvexd fvmptd
      ) AICPZQZBIBUAZRSZIRSZCHUBAHBCUMUCTUJOUDULITUMUNTUKULIRUEUFAUJUGUKIRUHUI
      $.

    $( Lemma 2 for ~ funcestrcsetc .  (Contributed by AV, 22-Mar-2020.) $)
    funcestrcsetclem2 $p |- ( ( ph /\ X e. B ) -> ( F ` X ) e. U ) $=
      ( wcel wa cfv cbs funcestrcsetclem1 estrcbasbas eqeltrd ) AICPQIHRISRFABC
      DEFGHIJKLMNOTACGFIJLNUAUB $.

    $d C x $.
    $( Lemma 3 for ~ funcestrcsetc .  (Contributed by AV, 22-Mar-2020.) $)
    funcestrcsetclem3 $p |- ( ph -> F : B --> C ) $=
      ( cv cbs cfv wcel wa estrcbasbas wceq cwun setcbas eqcomd adantr eleqtrrd
      eleqtrrdi fmpt3d ) ABCBOZPQZDHNAUICRZSZUJEPQZDULUJFUMACGFUIIKMTAUMFUAUKAF
      UMAEFUBJMUCUDUEUFLUGUH $.

    $d B x y $.
    funcestrcsetc.g $e |- ( ph -> G = ( x e. B , y e. B
                          |-> ( _I |` ( ( Base ` y ) ^m ( Base ` x ) ) ) ) ) $.
    $( Lemma 4 for ~ funcestrcsetc .  (Contributed by AV, 22-Mar-2020.) $)
    funcestrcsetclem4 $p |- ( ph -> G Fn ( B X. B ) ) $=
      ( wfn cv cvv cxp cid cbs cfv cmap cres cmpo eqid wcel ovex resiexg fnmpoi
      co ax-mp fneq1d mpbiri ) AJDDUAZRBCDDUBCSUCUDZBSUCUDZUEUMZUFZUGZUQRBCDDVA
      VBVBUHUTTUIVATUIURUSUEUJUTTUKUNULAUQJVBQUOUP $.

    $d X y $.  $d ph y $.
    ${
      $d M x y $.  $d N x y $.  $d Y x y $.
      funcestrcsetc.m $e |- M = ( Base ` X ) $.
      funcestrcsetc.n $e |- N = ( Base ` Y ) $.
      $( Lemma 5 for ~ funcestrcsetc .  (Contributed by AV, 23-Mar-2020.) $)
      funcestrcsetclem5 $p |- ( ( ph /\ ( X e. B /\ Y e. B ) )
                                -> ( X G Y ) = ( _I |` ( N ^m M ) ) ) $=
        ( wcel wa cid cv cbs cfv cmap co cres cmpo wceq adantr fveq2 oveqan12rd
        cvv oveq12i eqtr4di reseq2d adantl simprl simprr ovexd resiexd ovmpod )
        AMDUDZNDUDZUEZUEZBCMNDDUFCUGZUHUIZBUGZUHUIZUJUKZULZUFLKUJUKZULZJURAJBCD
        DVQUMUNVJUAUOVNMUNZVLNUNZUEZVQVSUNVKWBVPVRUFWBVPNUHUIZMUHUIZUJUKVRWAVTV
        MWCVOWDUJVLNUHUPVNMUHUPUQLWCKWDUJUCUBUSUTVAVBAVHVIVCAVHVIVDVKVRURVKLKUJ
        VEVFVG $.

      $( Lemma 6 for ~ funcestrcsetc .  (Contributed by AV, 23-Mar-2020.) $)
      funcestrcsetclem6 $p |- ( ( ph /\ ( X e. B /\ Y e. B )
                             /\ H e. ( N ^m M ) ) -> ( ( X G Y ) ` H ) = H ) $=
        ( wcel wa cmap co w3a cfv cid cres wceq funcestrcsetclem5 fveq1d fvresi
        3adant3 3ad2ant3 eqtrd ) ANDUEODUEUFZKMLUGUHZUEZUIZKNOJUHZUJKUKVAULZUJZ
        KVCKVDVEAUTVDVEUMVBABCDEFGHIJLMNOPQRSTUAUBUCUDUNUQUOVBAVFKUMUTVAKUPURUS
        $.
    $}

    $( Lemma 7 for ~ funcestrcsetc .  (Contributed by AV, 23-Mar-2020.) $)
    funcestrcsetclem7 $p |- ( ( ph /\ X e. B )
        -> ( ( X G X ) ` ( ( Id ` E ) ` X ) ) = ( ( Id ` S ) ` ( F ` X ) ) ) $=
      ( wcel cfv wa ccid cid cbs cres cmap wceq eqid funcestrcsetclem5 anabsan2
      co cwun adantr estrcbas eqtr4id eleq2d biimpa estrcid fveq12d fvex pm3.2i
      cvv wf wf1o f1oi f1of ax-mp elmapg mpbiri fvresi funcestrcsetclem1 fveq2d
      a1i 3syl estrcbasbas setcid eqtr2d 3eqtrd ) AKDSZUAZKHUBTZTZKKJUKZTUCKUDT
      ZUEZUCWDWDUFUKZUEZTZWEKITZFUBTZTZVTWBWEWCWGAVSWCWGUGABCDEFGHIJWDWDKKLMNOP
      QRWDUHZWLUIUJVTHGWAULKLWAUHAGULSVSPUMZAVSKGSADGKADHUDTGNAHGULLPUNUOUPUQUR
      USVTWDVBSZWNUAZWEWFSZWHWEUGWOVTWNWNKUDUTZWQVAVMWOWPWDWDWEVCZWDWDWEVDWRWDV
      EWDWDWEVFVGWDWDWEVBVBVHVIWFWEVJVNVTWKWDWJTWEVTWIWDWJABDEFGHIKLMNOPQVKVLVT
      FGWJULWDMWJUHWMADHGKLNPVOVPVQVR $.

    $d B f $.  $d F f $.  $d X f $.  $d Y f $.  $d Y x y $.  $d ph f $.
    $( Lemma 8 for ~ funcestrcsetc .  (Contributed by AV, 15-Feb-2020.) $)
    funcestrcsetclem8 $p |- ( ( ph /\ ( X e. B /\ Y e. B ) )
                    -> ( X G Y ) : ( X ( Hom ` E ) Y )
                                   --> ( ( F ` X ) ( Hom ` S ) ( F ` Y ) ) ) $=
      ( wcel vf wa chom cfv co cbs cmap cid cres wf1o f1oi f1of mp1i elmapi cvv
      wf cv wb fvex pm3.2i elmapg bicomd wceq funcestrcsetclem1 adantrl adantrr
      biimpa oveq12d eleqtrrd ex syl5 ssrdv fssd eqid funcestrcsetclem5 cwun wi
      adantr estrcbas eqtr4id eleq2d biimpcd impcom biimpd adantld imp estrchom
      funcestrcsetclem2 setchom feq123d mpbird ) AKDTZLDTZUBZUBZKLHUCUDZUEZKIUD
      ZLIUDZFUCUDZUEZKLJUEZUPLUFUDZKUFUDZUGUEZWSWRUGUEZUHXEUIZUPWOXEXEXFXGXEXEX
      GUJXEXEXGUPWOXEUKXEXEXGULUMWOUAXEXFUAUQZXETZXDXCXHUPZWOXHXFTZXHXCXDUNWOXJ
      XKWOXJUBXHXEXFWOXJXIXCUOTZXDUOTZUBZXJXIURWOXLXMLUFUSKUFUSUTXNXIXJXCXDXHUO
      UOVAVBUMVGWOXFXEVCXJWOWSXCWRXDUGAWMWSXCVCWLABDEFGHILMNOPQRVDVEAWLWRXDVCWM
      ABDEFGHIKMNOPQRVDVFVHVRVIVJVKVLVMWOWQXEXAXFXBXGABCDEFGHIJXDXCKLMNOPQRSXDV
      NZXCVNZVOWOXDXCHGWPVPKLMAGVPTWNQVRZWPVNWNAKGTZWLAXRVQWMAWLXRADGKADHUFUDGO
      AHGVPMQVSVTZWAWBVRWCAWNLGTZAWMXTWLAWMXTADGLXSWAWDWEWFXOXPWGWOFGWTVPWRWSNX
      QWTVNAWLWRGTWMABDEFGHIKMNOPQRWHVFAWMWSGTWLABDEFGHILMNOPQRWHVEWIWJWK $.

    $d Z x y $.
    $( Lemma 9 for ~ funcestrcsetc .  (Contributed by AV, 23-Mar-2020.) $)
    funcestrcsetclem9 $p |- ( ( ph /\ ( X e. B /\ Y e. B /\ Z e. B )
                  /\ ( H e. ( X ( Hom ` E ) Y ) /\ K e. ( Y ( Hom ` E ) Z ) ) )
                  -> ( ( X G Z ) ` ( K ( <. X , Y >. ( comp ` E ) Z ) H ) )
                     = ( ( ( Y G Z ) ` K )
                         ( <. ( F ` X ) , ( F ` Y ) >. ( comp ` S ) ( F ` Z ) )
                         ( ( X G Y ) ` H ) ) ) $=
      ( wcel w3a chom cfv co wa cop cco wceq cbs cmap cwun adantr eqid estrcbas
      eqtr4id eleq2d biimpcd 3ad2ant1 impcom 3ad2ant2 estrchom 3ad2ant3 anbi12d
      wi ccom cid cres elmapi fco syl2an fvex elmap sylibr ancoms adantl fvresi
      wf funcestrcsetclem5 3adantr2 ad2antrl ad2antll estrcco funcestrcsetclem2
      syl fveq12d 3ad2antr1 3ad2antr2 3ad2antr3 funcestrcsetclem1 feq23d mpbird
      simpll 3simpa simprl funcestrcsetclem6 syl3anc feq1d 3simpc simprr setcco
      wb ad2antlr coeq12d eqtrd 3eqtr4d ex sylbid 3impia ) AMDUCZNDUCZODUCZUDZK
      MNHUEUFZUGZUCZLNOXPUGZUCZUHZLKMNUIOHUJUFZUGUGZMOJUGZUFZLNOJUGUFZKMNJUGUFZ
      MIUFZNIUFZUIOIUFZFUJUFZUGUGZUKZAXOUHZYAKNULUFZMULUFZUMUGZUCZLOULUFZYOUMUG
      ZUCZUHZYMYNXRYRXTUUAYNXQYQKYNYPYOHGXPUNMNPAGUNUCZXOTUOZXPUPZXOAMGUCZXLXMA
      UUFVGXNAXLUUFADGMADHULUFGRAHGUNPTUQURZUSUTVAVBZXOANGUCZXMXLAUUIVGXNAXMUUI
      ADGNUUGUSUTVCVBZYPUPZYOUPZVDUSYNXSYTLYNYOYSHGXPUNNOPUUDUUEUUJXOAOGUCZXNXL
      AUUMVGXMAXNUUMADGOUUGUSUTVEVBZUULYSUPZVDUSVFYNUUBYMYNUUBUHZLKVHZVIYSYPUMU
      GZVJZUFZUUQYEYLUUPUUQUURUCZUUTUUQUKUUBUVAYNUUAYRUVAUUAYRUHYPYSUUQVTZUVAUU
      AYOYSLVTZYPYOKVTZUVBYRLYSYOVKZKYOYPVKZYPYOYSLKVLVMYSYPUUQOULVNMULVNVOVPVQ
      VRUURUUQVSWGUUPYCUUQYDUUSYNYDUUSUKZUUBAXLXNUVGXMABCDEFGHIJYPYSMOPQRSTUAUB
      UUKUUOWAWBUOUUPYPYOHYSYBGKLUNMNOPYNUUCUUBUUDUOZYBUPYNUUFUUBUUHUOYNUUIUUBU
      UJUOYNUUMUUBUUNUOUUKUULUUOYRUVDYNUUAUVFWCZUUAUVCYNYRUVEWDZWEWHUUPYLYFYGVH
      UUQUUPFYKGYGYFUNYHYIYJQUVHYKUPYNYHGUCZUUBAXMXLUVKXNABDEFGHIMPQRSTUAWFWIUO
      YNYIGUCZUUBAXLXMUVLXNABDEFGHINPQRSTUAWFWJUOYNYJGUCZUUBAXLXNUVMXMABDEFGHIO
      PQRSTUAWFWKUOUUPYHYIYGVTYHYIKVTZUUPUVNUVDUVIYNUVNUVDXDUUBYNYHYIYPYOKAXMXL
      YHYPUKXNABDEFGHIMPQRSTUAWLWIAXLXMYIYOUKXNABDEFGHINPQRSTUAWLWJZWMUOWNUUPYH
      YIYGKUUPAXLXMUHZYRYGKUKAXOUUBWOZXOUVPAUUBXLXMXNWPXEYNYRUUAWQABCDEFGHIJKYP
      YOMNPQRSTUAUBUUKUULWRWSZWTWNUUPYIYJYFVTYIYJLVTZUUPUVSUVCUVJYNUVSUVCXDUUBY
      NYIYJYOYSLUVOAXLXNYJYSUKXMABDEFGHIOPQRSTUAWLWKWMUOWNUUPYIYJYFLUUPAXMXNUHZ
      UUAYFLUKUVQXOUVTAUUBXLXMXNXAXEYNYRUUAXBABCDEFGHIJLYOYSNOPQRSTUAUBUULUUOWR
      WSZWTWNXCUUPYFLYGKUWAUVRXFXGXHXIXJXK $.

    $d a b c x y $.  $d B a b c h k $.  $d F a b c h k $.  $d G a b c h k $.
    $d E a b c h k $.  $d S a b c h k $.  $d ph a b c h k $.
    $( The "natural forgetful functor" from the category of extensible
       structures into the category of sets which sends each extensible
       structure to its base set, preserving the morphisms as mappings between
       the corresponding base sets.  (Contributed by AV, 23-Mar-2020.) $)
    funcestrcsetc $p |- ( ph -> F ( E Func S ) G ) $=
      ( cfv eqid cv va vb vc vh vk cco ccid chom cwun wcel estrccat syl setccat
      funcestrcsetclem3 funcestrcsetclem4 funcestrcsetclem8 funcestrcsetclem7
      ccat funcestrcsetclem9 isfuncd ) AUAUBUCDEHHUFRZHUGRZUDUEFIJHUHRZFUGRZFUH
      RZFUFRZMNVCSVESVBSVDSVASVFSAGUIUJZHURUJOHGUIKUKULAVGFURUJOFGUILUMULABDEFG
      HIKLMNOPUNABCDEFGHIJKLMNOPQUOABCDEFGHIJUATZUBTZKLMNOPQUPABCDEFGHIJVHKLMNO
      PQUQABCDEFGHIJUDTUETVHVIUCTKLMNOPQUSUT $.

    $( The "natural forgetful functor" from the category of extensible
       structures into the category of sets which sends each extensible
       structure to its base set is faithful.  (Contributed by AV,
       2-Apr-2020.) $)
    fthestrcsetc $p |- ( ph -> F ( E Faith S ) G ) $=
      ( co cfv wcel va vb vh vk cfunc wbr cv chom wral cfth funcestrcsetc wa wf
      wf1 wceq weq funcestrcsetclem8 cbs cmap cwun adantr eqid estrcbas eqtr4id
      wi eleq2d biimpcd impcom adantl estrchom funcestrcsetclem6 3expia eqeq12d
      sylbid com12 biimpd ralrimivva dff13 sylanbrc isfth2 ) AIJHFUERUFUAUGZUBU
      GZHUHSZRZWAISWBISFUHSZRZWAWBJRZUNZUBDUIUADUIIJHFUJRUFABCDEFGHIJKLMNOPQUKA
      WHUAUBDDAWADTZWBDTZULZULZWDWFWGUMUCUGZWGSZUDUGZWGSZUOZUCUDUPZVEZUDWDUIUCW
      DUIWHABCDEFGHIJWAWBKLMNOPQUQWLWSUCUDWDWDWLWMWDTZWOWDTZULZULZWQWRXCWNWMWPW
      OXBWLWNWMUOZWTWLXDVEXAWLWTXDWLWTWMWBURSZWAURSZUSRZTZXDWLWDXGWMWLXFXEHGWCU
      TWAWBKAGUTTWKOVAWCVBZWKAWAGTZWIAXJVEWJAWIXJADGWAADHURSGMAHGUTKOVCVDZVFVGV
      AVHWKAWBGTZWJAXLVEWIAWJXLADGWBXKVFVGVIVHXFVBZXEVBZVJZVFAWKXHXDABCDEFGHIJW
      MXFXEWAWBKLMNOPQXMXNVKVLVNVOVAVHXBWLWPWOUOZXAWLXPVEWTWLXAXPWLXAWOXGTZXPWL
      WDXGWOXOVFAWKXQXPABCDEFGHIJWOXFXEWAWBKLMNOPQXMXNVKVLVNVOVIVHVMVPVQUCUDWDW
      FWGVRVSVQUAUBDHFIJWCWEMXIWEVBVTVS $.

    $d F h k $.  $d S h k $.
    $( The "natural forgetful functor" from the category of extensible
       structures into the category of sets which sends each extensible
       structure to its base set is full.  (Contributed by AV, 2-Apr-2020.) $)
    fullestrcsetc $p |- ( ph -> F ( E Full S ) G ) $=
      ( vh vk wcel va vb cfunc co wbr cv chom cfv wral cful funcestrcsetc wa wf
      wfo wceq wrex funcestrcsetclem8 cbs cwun adantr funcestrcsetclem2 adantrr
      eqid adantrl elsetchom funcestrcsetclem1 feq23d bitrd cmap weq cvv pm3.2i
      wb fvex elmapg mp1i biimpar adantl eqidd rspcedvd funcestrcsetclem6 3expa
      equequ2 eqeq2d rexbidva mpbird wi estrcbas eqtr4id eleq2d impcom estrchom
      biimpcd rexeqdv ex sylbid ralrimiv dffo3 sylanbrc ralrimivva isfull2 ) AI
      JHFUCUDUEUAUFZUBUFZHUGUHZUDZXBIUHZXCIUHZFUGUHZUDZXBXCJUDZUNZUBDUIUADUIIJH
      FUJUDUEABCDEFGHIJKLMNOPQUKAXKUAUBDDAXBDTZXCDTZULZULZXEXIXJUMRUFZSUFZXJUHZ
      UOZSXEUPZRXIUIXKABCDEFGHIJXBXCKLMNOPQUQXOXTRXIXOXPXITZXBURUHZXCURUHZXPUMZ
      XTXOYAXFXGXPUMYDXOFGXPXHUSXFXGLAGUSTXNOUTZXHVCZAXLXFGTXMABDEFGHIXBKLMNOPV
      AVBAXMXGGTXLABDEFGHIXCKLMNOPVAVDVEXOXFXGYBYCXPAXLXFYBUOXMABDEFGHIXBKLMNOP
      VFVBAXMXGYCUOXLABDEFGHIXCKLMNOPVFVDVGVHXOYDXTXOYDULZXTXSSYCYBVIUDZUPZYGYI
      RSVJZSYHUPZYGYJRRVJZSXPYHXOXPYHTZYDYCVKTZYBVKTZULYMYDVMXOYNYOXCURVNXBURVN
      VLYCYBXPVKVKVOVPVQSRVJYJYLVMYGSRRWCVRYGXPVSVTXOYIYKVMYDXOXSYJSYHXOXQYHTZU
      LXRXQXPAXNYPXRXQUOABCDEFGHIJXQYBYCXBXCKLMNOPQYBVCZYCVCZWAWBWDWEUTWFXOXTYI
      VMYDXOXSSXEYHXOYBYCHGXDUSXBXCKYEXDVCZXNAXBGTZXLAYTWGXMAXLYTADGXBADHURUHGM
      AHGUSKOWHWIZWJWMUTWKXNAXCGTZXMAUUBWGXLAXMUUBADGXCUUAWJWMVRWKYQYRWLWNUTWFW
      OWPWQSRXEXIXJWRWSWTUAUBDHFIJXDXHMYFYSXAWS $.

    $d C a $.  $d F a b i $.
    equivestrcsetc.i $e |- ( ph -> ( Base ` ndx ) e. U ) $.
    $( The "natural forgetful functor" from the category of extensible
       structures into the category of sets which sends each extensible
       structure to its base set is an equivalence.  According to definition
       3.33 (1) of [Adamek] p. 36, "A functor F :  A -> B is called an
       _equivalence_ provided that it is full, faithful, and isomorphism-dense
       in the sense that for any B-object B' there exists some A-object A' such
       that F(A') is isomorphic to B'.".  Therefore, the category of sets and
       the category of extensible structures are equivalent, according to
       definition 3.33 (2) of [Adamek] p. 36, "Categories A and B are called
       _equivalent_ provided that there is an equivalence from A to B.".
       (Contributed by AV, 2-Apr-2020.) $)
    equivestrcsetc $p |- ( ph -> ( F ( E Faith S ) G /\ F ( E Full S ) G
                /\ A. b e. C E. a e. B E. i i : b -1-1-onto-> ( F ` a ) ) ) $=
      ( cfth co wbr cful cfv wf1o wex wrex wral fthestrcsetc fullestrcsetc wcel
      cv wa cnx cbs cop csn cwun setcbas eqtr4id eleq2d eqid 1strwunbndx sylbid
      ex imp wceq estrcbas adantr eleqtrrd fveq2 f1oeq3d exbidv adantl cid cres
      wb f1oi funcestrcsetclem1 syldan 1strbas eqtr4d mpbiri cvv resiexg f1oeq1
      elv spcev syl rspcedvd ralrimiva 3jca ) AJKIFUBUCUDJKIFUEUCUDMUNZLUNZJUFZ
      HUNZUGZHUHZLDUIZMEUJABCDEFGIJKNOPQRSTUKABCDEFGIJKNOPQRSTULAXAMEAWOEUMZUOZ
      WTWOUPUQUFWOURUSZJUFZWRUGZHUHZLXDDXCXDGDAXBXDGUMZAXBWOGUMZXHAEGWOAEFUQUFG
      QAFGUTORVAVBVCAXIXHAWOGXDXDVDZRUAVEVGVFVHXCDIUQUFZGPAGXKVIXBAIGUTNRVJVKVB
      VLZWPXDVIZWTXGVSXCXMWSXFHXMWQXEWOWRWPXDJVMVNVOVPXCWOXEVQWOVRZUGZXGXCXOWOW
      OXNUGWOVTXCXEWOWOXNXCXEXDUQUFZWOAXBXDDUMXEXPVIXLABDEFGIJXDNOPQRSWAWBXBWOX
      PVIAWOXDEXJWCVPWDVNWEXFXOHXNXNWFUMMWOWFWGWIWOXEWRXNWHWJWKWLWMWN $.
  $}

  ${
    setc1strwun.s $e |- S = ( SetCat ` U ) $.
    setc1strwun.c $e |- C = ( Base ` S ) $.
    setc1strwun.u $e |- ( ph -> U e. WUni ) $.
    setc1strwun.o $e |- ( ph -> _om e. U ) $.
    $( A constructed one-slot structure with the objects of the category of
       sets as base set in a weak universe.  (Contributed by AV,
       27-Mar-2020.) $)
    setc1strwun $p |- ( ( ph /\ X e. C )
                              -> { <. ( Base ` ndx ) , X >. } e. U ) $=
      ( wcel cnx cbs cfv cop csn cwun setcbas eqtr4id eleq2d biimpa eqid syldan
      1strwun ) AEBJZEDJZKLMENOZDJAUDUEABDEABCLMDGACDPFHQRSTAEDUFUFUAHIUCUB $.
  $}

  ${
    $d C x $.  $d X x $.  $d ph x $.
    funcsetcestrc.s $e |- S = ( SetCat ` U ) $.
    funcsetcestrc.c $e |- C = ( Base ` S ) $.
    funcsetcestrc.f $e |- ( ph
                        -> F = ( x e. C |-> { <. ( Base ` ndx ) , x >. } ) ) $.
    $( Lemma 1 for ~ funcsetcestrc .  (Contributed by AV, 27-Mar-2020.) $)
    funcsetcestrclem1 $p |- ( ( ph /\ X e. C )
                              -> ( F ` X ) = { <. ( Base ` ndx ) , X >. } ) $=
      ( wcel wa cnx cbs cfv cv cop csn cvv wceq adantr opeq2 sneqd adantl simpr
      cmpt snex a1i fvmptd ) AGCKZLZBGMNOZBPZQZRZULGQZRZCFSAFBCUOUFTUJJUAUMGTZU
      OUQTUKURUNUPUMGULUBUCUDAUJUEUQSKUKUPUGUHUI $.

    funcsetcestrc.u $e |- ( ph -> U e. WUni ) $.
    funcsetcestrc.o $e |- ( ph -> _om e. U ) $.
    $( Lemma 2 for ~ funcsetcestrc .  (Contributed by AV, 27-Mar-2020.) $)
    funcsetcestrclem2 $p |- ( ( ph /\ X e. C ) -> ( F ` X ) e. U ) $=
      ( wcel wa cfv cnx cbs cop csn funcsetcestrclem1 setc1strwun eqeltrd ) AGC
      MNGFOPQOGRSEABCDEFGHIJTACDEGHIKLUAUB $.

    ${
      $d B x $.  $d C x $.
      funcsetcestrclem3.e $e |- E = ( ExtStrCat ` U ) $.
      funcsetcestrclem3.b $e |- B = ( Base ` E ) $.
      $( Lemma 3 for ~ funcsetcestrc .  (Contributed by AV, 27-Mar-2020.) $)
      funcsetcestrclem3 $p |- ( ph -> F : C --> B ) $=
        ( cnx cbs cfv cv cop csn wcel setc1strwun wceq estrcbas eqcomd eleqtrrd
        wa cwun adantr eleqtrrdi fmpt3d ) ABDPQRBSZTUAZCHKAUMDUBZUHZUNGQRZCUPUN
        FUQADEFUMIJLMUCAUQFUDUOAFUQAGFUINLUEUFUJUGOUKUL $.

      $d C y z $.  $d F y z $.  $d ph x y z $.
      $( Lemma for ~ embedsetcestrc .  (Contributed by AV, 31-Mar-2020.) $)
      embedsetcestrclem $p |- ( ph -> F : C -1-1-> B ) $=
        ( vy vz wceq wcel cvv wf cv cfv weq wi wf1 funcsetcestrclem3 wa cnx cbs
        wral cop csn funcsetcestrclem1 adantrr adantrl eqeq12d opex sneqbg mp1i
        wb fvexd simpl opthg syl2an simpr biimtrdi sylbid ralrimivva sylanbrc
        dff13 ) ADCHUAPUBZHUCZQUBZHUCZRZPQUDZUEZQDUKPDUKDCHUFABCDEFGHIJKLMNOUGA
        VRPQDDAVLDSZVNDSZUHZUHZVPUIUJUCZVLULZUMZWCVNULZUMZRZVQWBVMWEVOWGAVSVMWE
        RVTABDEFHVLIJKUNUOAVTVOWGRVSABDEFHVNIJKUNUPUQWBWHWDWFRZVQWDTSWHWIVAWBWC
        VLURWDWFTUSUTWBWIWCWCRZVQUHZVQAWCTSVSWIWKVAWAAUIUJVBVSVTVCWCVLWCVNTDVDV
        EWJVQVFVGVHVHVIPQDCHVKVJ $.
    $}

    $d C x y $.
    funcsetcestrc.g $e |- ( ph -> G = ( x e. C , y e. C
                                        |-> ( _I |` ( y ^m x ) ) ) ) $.
    $( Lemma 4 for ~ funcsetcestrc .  (Contributed by AV, 27-Mar-2020.) $)
    funcsetcestrclem4 $p |- ( ph -> G Fn ( C X. C ) ) $=
      ( cxp wfn cv cmap cvv wcel cid co cres cmpo eqid ovex ax-mp fnmpoi fneq1d
      resiexg mpbiri ) AHDDOZPBCDDUACQZBQZRUBZUCZUDZULPBCDDUPUQUQUEUOSTUPSTUMUN
      RUFUOSUJUGUHAULHUQNUIUK $.

    $d X y $.  $d Y x y $.  $d ph y $.
    $( Lemma 5 for ~ funcsetcestrc .  (Contributed by AV, 27-Mar-2020.) $)
    funcsetcestrclem5 $p |- ( ( ph /\ ( X e. C /\ Y e. C ) )
                              -> ( X G Y ) = ( _I |` ( Y ^m X ) ) ) $=
      ( wa cid cmap wceq wcel cres cvv cmpo adantr oveq12 ancoms reseq2d adantl
      cv co simprl simprr ovexd resiexd ovmpod ) AIDUAZJDUAZQZQZBCIJDDRCUJZBUJZ
      SUKZUBZRJISUKZUBZHUCAHBCDDVDUDTUSPUEVBITZVAJTZQZVDVFTUTVIVCVERVHVGVCVETVA
      JVBISUFUGUHUIAUQURULAUQURUMUTVEUCUTJISUNUOUP $.

    $( Lemma 6 for ~ funcsetcestrc .  (Contributed by AV, 27-Mar-2020.) $)
    funcsetcestrclem6 $p |- ( ( ph /\ ( X e. C /\ Y e. C )
                             /\ H e. ( Y ^m X ) ) -> ( ( X G Y ) ` H ) = H ) $=
      ( wcel co cfv wa cmap w3a cid cres wceq funcsetcestrclem5 fveq1d 3ad2ant3
      3adant3 fvresi eqtrd ) AJDRKDRUAZIKJUBSZRZUCZIJKHSZTIUDUNUEZTZIUPIUQURAUM
      UQURUFUOABCDEFGHJKLMNOPQUGUJUHUOAUSIUFUMUNIUKUIUL $.

    funcsetcestrc.e $e |- E = ( ExtStrCat ` U ) $.
    $( Lemma 7 for ~ funcsetcestrc .  (Contributed by AV, 27-Mar-2020.) $)
    funcsetcestrclem7 $p |- ( ( ph /\ X e. C )
        -> ( ( X G X ) ` ( ( Id ` S ) ` X ) ) = ( ( Id ` E ) ` ( F ` X ) ) ) $=
      ( wcel cfv cid wa ccid co cres cnx cbs cop csn funcsetcestrclem5 anabsan2
      cmap wceq cwun eqid adantr setcbas eqtr4id eleq2d biimpa setcid wf1o f1oi
      fveq12d wf ax-mp simpr elmapd mpbiri fvresi syl 1strbas funcsetcestrclem1
      f1of reseq2d eqtrd fveq2d setc1strwun estrcid eqtr2d 3eqtrd ) AJDRZUAZJEU
      BSZSZJJIUCZSTJUDZTJJUKUCZUDZSZTUEUFSJUGUHZUFSZUDZJHSZGUBSZSZWBWDWFWEWHAWA
      WEWHULABCDEFHIJJKLMNOPUIUJWBEFWCUMJKWCUNAFUMRWANUOZAWAJFRADFJADEUFSFLAEFU
      MKNUPUQURUSUTVCWBWIWFWLWBWFWGRZWIWFULWBWQJJWFVDZJJWFVAWRJVBJJWFVMVEWBJJWF
      DDAWAVFZWSVGVHWGWFVIVJWBJWKTWBWAJWKULWSJWJDWJUNVKVJVNVOWBWOWJWNSWLWBWMWJW
      NABDEFHJKLMVLVPWBGFWNUMWJQWNUNWPADEFJKLNOVQVRVSVT $.

    $d C f $.  $d F f $.  $d X f $.  $d Y f $.  $d ph f $.
    $( Lemma 8 for ~ funcsetcestrc .  (Contributed by AV, 28-Mar-2020.) $)
    funcsetcestrclem8 $p |- ( ( ph /\ ( X e. C /\ Y e. C ) )
                    -> ( X G Y ) : ( X ( Hom ` S ) Y )
                                   --> ( ( F ` X ) ( Hom ` E ) ( F ` Y ) ) ) $=
      ( wcel cfv vf wa chom co wf cmap cbs cid cres wf1o f1oi f1of cv elmapi wb
      mp1i simpr ancomd elmapg syl biimpar cnx cop csn funcsetcestrclem1 fveq2d
      wceq 1strbas eqcomd adantl adantrl eqtr4d adantrr oveq12d adantr eleqtrrd
      eqid eqtrd syl5 fssd funcsetcestrclem5 cwun setcbas eqtr4id eleq2d biimpd
      ex adantrd imp adantld setchom funcsetcestrclem2 estrchom feq123d mpbird
      ssrdv ) AJDSZKDSZUBZUBZJKEUCTZUDZJHTZKHTZGUCTZUDZJKIUDZUEKJUFUDZXDUGTZXCU
      GTZUFUDZUHXHUIZUEWTXHXHXKXLXHXHXLUJXHXHXLUEWTXHUKXHXHXLULUPWTUAXHXKUAUMZX
      HSZJKXMUEZWTXMXKSZXMKJUNWTXOXPWTXOUBXMXHXKWTXNXOWTWRWQUBXNXOUOWTWQWRAWSUQ
      URKJXMDDUSUTVAWTXKXHVGXOWTXIKXJJUFAWRXIKVGWQAWRUBZXIVBUGTZKVCVDZUGTZKXQXD
      XSUGABDEFHKLMNVEVFWRXTKVGAWRKXTKXSDXSVQVHVIVJVRVKAWQXJJVGWRAWQUBZXJXRJVCV
      DZUGTZJYAXCYBUGABDEFHJLMNVEVFWQJYCVGAJYBDYBVQVHVJVLVMVNVOVPWGVSWPVTWTXBXH
      XFXKXGXLABCDEFHIJKLMNOPQWAWTEFXAWBJKLAFWBSWSOVOZXAVQAWSJFSZAWQYEWRAWQYEAD
      FJADEUGTFMAEFWBLOWCWDZWEWFWHWIAWSKFSZAWRYGWQAWRYGADFKYFWEWFWJWIWKWTXJXIGF
      XEWBXCXDRYDXEVQAWQXCFSWRABDEFHJLMNOPWLVMAWRXDFSWQABDEFHKLMNOPWLVKXJVQXIVQ
      WMWNWO $.

    $d Z x y $.
    $( Lemma 9 for ~ funcsetcestrc .  (Contributed by AV, 28-Mar-2020.) $)
    funcsetcestrclem9 $p |- ( ( ph /\ ( X e. C /\ Y e. C /\ Z e. C )
                  /\ ( H e. ( X ( Hom ` S ) Y ) /\ K e. ( Y ( Hom ` S ) Z ) ) )
                  -> ( ( X G Z ) ` ( K ( <. X , Y >. ( comp ` S ) Z ) H ) )
                     = ( ( ( Y G Z ) ` K )
                         ( <. ( F ` X ) , ( F ` Y ) >. ( comp ` E ) ( F ` Z ) )
                         ( ( X G Y ) ` H ) ) ) $=
      ( wcel w3a chom cfv co cop cco wceq cmap cwun adantr eqid setcbas eqtr4id
      cbs eleq2d biimpcd 3ad2ant1 impcom 3ad2ant2 setchom 3ad2ant3 anbi12d ccom
      wa wi cid cres wf elmapi syl2anr adantl wb elmapg ancoms 3adant2 ad2antlr
      fco mpbird fvresi syl funcsetcestrclem5 3adantr2 ad2antrl ad2antll setcco
      fveq12d funcsetcestrclem2 3ad2antr1 3ad2antr2 3ad2antr3 funcsetcestrclem6
      simpll 3simpa simprl syl3anc cnx funcsetcestrclem1 fveq2d 1strbas feq123d
      csn eqcomd eqtrd 3simpc simprr estrcco coeq12d 3eqtr4d ex sylbid 3impia )
      ALDUBZMDUBZNDUBZUCZJLMEUDUEZUFZUBZKMNXRUFZUBZVFZKJLMUGNEUHUEZUFUFZLNIUFZU
      EZKMNIUFUEZJLMIUFUEZLHUEZMHUEZUGNHUEZGUHUEZUFUFZUIZAXQVFZYCJMLUJUFZUBZKNM
      UJUFZUBZVFZYOYPXTYRYBYTYPXSYQJYPEFXRUKLMOAFUKUBZXQRULZXRUMZXQALFUBZXNXOAU
      UEVGXPAXNUUEADFLADEUPUEFPAEFUKORUNUOZUQURUSUTZXQAMFUBZXOXNAUUHVGXPAXOUUHA
      DFMUUFUQURVAUTZVBUQYPYAYSKYPEFXRUKMNOUUCUUDUUIXQANFUBZXPXNAUUJVGXOAXPUUJA
      DFNUUFUQURVCUTZVBUQVDYPUUAYOYPUUAVFZKJVEZVHNLUJUFZVIZUEZUUMYGYNUULUUMUUNU
      BZUUPUUMUIUULUUQLNUUMVJZUUAUURYPYTMNKVJZLMJVJZUURYRKNMVKZJMLVKZLMNKJVSVLV
      MXQUUQUURVNZAUUAXNXPUVCXOXPXNUVCNLUUMDDVOVPVQVRVTUUNUUMWAWBUULYEUUMYFUUOY
      PYFUUOUIZUUAAXNXPUVDXOABCDEFHILNOPQRSTWCWDULUULEYDFJKUKLMNOYPUUBUUAUUCULZ
      YDUMYPUUEUUAUUGULYPUUHUUAUUIULYPUUJUUAUUKULYRUUTYPYTUVBWEZYTUUSYPYRUVAWFZ
      WGWHUULYNYHYIVEUUMUULYJUPUEZYKUPUEZGYLUPUEZYMFYIYHUKYJYKYLUAUVEYMUMYPYJFU
      BZUUAAXOXNUVKXPABDEFHLOPQRSWIWJULYPYKFUBZUUAAXNXOUVLXPABDEFHMOPQRSWIWKULY
      PYLFUBZUUAAXNXPUVMXOABDEFHNOPQRSWIWLULUVHUMUVIUMUVJUMUULUVHUVIYIVJUUTUVFU
      ULUVHLUVIMYIJUULAXNXOVFZYRYIJUIAXQUUAWNZXQUVNAUUAXNXOXPWOVRYPYRYTWPABCDEF
      HIJLMOPQRSTWMWQZYPUVHLUIUUAYPUVHWRUPUEZLUGXCZUPUEZLYPYJUVRUPAXOXNYJUVRUIX
      PABDEFHLOPQWSWJWTXQUVSLUIZAXNXOUVTXPXNLUVSLUVRDUVRUMXAXDUSVMXEULYPUVIMUIU
      UAYPUVIUVQMUGXCZUPUEZMYPYKUWAUPAXNXOYKUWAUIXPABDEFHMOPQWSWKWTXQUWBMUIZAXO
      XNUWCXPXOMUWBMUWADUWAUMXAXDVAVMXEULZXBVTUULUVIUVJYHVJUUSUVGUULUVIMUVJNYHK
      UULAXOXPVFZYTYHKUIUVOXQUWEAUUAXNXOXPXFVRYPYRYTXGABCDEFHIKMNOPQRSTWMWQZUWD
      YPUVJNUIUUAYPUVJUVQNUGXCZUPUEZNYPYLUWGUPAXNXPYLUWGUIXOABDEFHNOPQWSWLWTXQU
      WHNUIZAXPXNUWIXOXPNUWHNUWGDUWGUMXAXDVCVMXEULXBVTXHUULYHKYIJUWFUVPXIXEXJXK
      XLXM $.

    $d a b c x y $.  $d C a b c h k $.  $d E a b c h k x $.  $d F a b c h k $.
    $d G a b c h k $.  $d S a b c h k $.  $d ph a b c h k $.
    $( The "embedding functor" from the category of sets into the category of
       extensible structures which sends each set to an extensible structure
       consisting of the base set slot only, preserving the morphisms as
       mappings between the corresponding base sets.  (Contributed by AV,
       28-Mar-2020.) $)
    funcsetcestrc $p |- ( ph -> F ( S Func E ) G ) $=
      ( cfv eqid cwun cv va vb vc vh vk cbs cco ccid chom wcel ccat setccat syl
      funcsetcestrclem3 funcsetcestrclem4 funcsetcestrclem8 funcsetcestrclem7
      estrccat funcsetcestrclem9 isfuncd ) AUAUBUCDGUFQZEEUGQZEUHQZUDUEGHIEUIQZ
      GUHQZGUIQZGUGQZKVARZVDRVFRVCRVERVBRVGRAFSUJZEUKUJMEFSJULUMAVIGUKUJMGFSPUR
      UMABVADEFGHJKLMNPVHUNABCDEFHIJKLMNOUOABCDEFGHIUATZUBTZJKLMNOPUPABCDEFGHIV
      JJKLMNOPUQABCDEFGHIUDTUETVJVKUCTJKLMNOPUSUT $.

    $( The "embedding functor" from the category of sets into the category of
       extensible structures which sends each set to an extensible structure
       consisting of the base set slot only is faithful.  (Contributed by AV,
       31-Mar-2020.) $)
    fthsetcestrc $p |- ( ph -> F ( S Faith E ) G ) $=
      ( vh co cfv wcel va vb vk cfunc wbr cv chom wral cfth funcsetcestrc wa wf
      wf1 wceq weq wi funcsetcestrclem8 cmap cwun adantr setcbas eqtr4id eleq2d
      cbs biimpcd impcom adantl setchom funcsetcestrclem6 3expia sylbid eqeq12d
      eqid com12 biimpd ralrimivva dff13 sylanbrc isfth2 ) AHIEGUDRUEUAUFZUBUFZ
      EUGSZRZVTHSWAHSGUGSZRZVTWAIRZUMZUBDUHUADUHHIEGUIRUEABCDEFGHIJKLMNOPUJAWGU
      AUBDDAVTDTZWADTZUKZUKZWCWEWFULQUFZWFSZUCUFZWFSZUNZQUCUOZUPZUCWCUHQWCUHWGA
      BCDEFGHIVTWAJKLMNOPUQWKWRQUCWCWCWKWLWCTZWNWCTZUKZUKZWPWQXBWMWLWOWNXAWKWMW
      LUNZWSWKXCUPWTWKWSXCWKWSWLWAVTURRZTZXCWKWCXDWLWKEFWBUSVTWAJAFUSTWJMUTWBVM
      ZWJAVTFTZWHAXGUPWIAWHXGADFVTADEVDSFKAEFUSJMVAVBZVCVEUTVFWJAWAFTZWIAXIUPWH
      AWIXIADFWAXHVCVEVGVFVHZVCAWJXEXCABCDEFHIWLVTWAJKLMNOVIVJVKVNUTVFXAWKWOWNU
      NZWTWKXKUPWSWKWTXKWKWTWNXDTZXKWKWCXDWNXJVCAWJXLXKABCDEFHIWNVTWAJKLMNOVIVJ
      VKVNVGVFVLVOVPQUCWCWEWFVQVRVPUAUBDEGHIWBWDKXFWDVMVSVR $.

    $( The "embedding functor" from the category of sets into the category of
       extensible structures which sends each set to an extensible structure
       consisting of the base set slot only is full.  (Contributed by AV,
       1-Apr-2020.) $)
    fullsetcestrc $p |- ( ph -> F ( S Full E ) G ) $=
      ( vh vk cfv wcel va vb cfunc co wbr cv chom wral cful funcsetcestrc wa wf
      wfo wceq wrex funcsetcestrclem8 cbs cwun adantr funcsetcestrclem2 adantrr
      eqid adantrl elestrchom cnx cop funcsetcestrclem1 fveq2d 1strbas ad2antrl
      csn eqtr4d ad2antll feq23d weq wb simpr ancomd elmapg syl biimpar equequ2
      cmap adantl eqidd rspcedvd funcsetcestrclem6 3expa eqeq2d rexbidva mpbird
      wi setcbas eqtr4id eleq2d biimpcd impcom setchom ex sylbid ralrimiv dffo3
      rexeqdv sylanbrc ralrimivva isfull2 ) AHIEGUCUDUEUAUFZUBUFZEUGSZUDZXGHSZX
      HHSZGUGSZUDZXGXHIUDZUMZUBDUHUADUHHIEGUIUDUEABCDEFGHIJKLMNOPUJAXPUAUBDDAXG
      DTZXHDTZUKZUKZXJXNXOULQUFZRUFZXOSZUNZRXJUOZQXNUHXPABCDEFGHIXGXHJKLMNOPUPX
      TYEQXNXTYAXNTXKUQSZXLUQSZYAULZYEXTYFYGGFYAXMURXKXLPAFURTXSMUSZXMVBZAXQXKF
      TXRABDEFHXGJKLMNUTVAAXRXLFTXQABDEFHXHJKLMNUTVCYFVBYGVBVDXTYHXGXHYAULZYEXT
      YFYGXGXHYAXTYFVEUQSZXGVFVKZUQSZXGXTXKYMUQAXQXKYMUNXRABDEFHXGJKLVGVAVHXQXG
      YNUNAXRXGYMDYMVBVIVJVLXTYGYLXHVFVKZUQSZXHXTXLYOUQAXRXLYOUNXQABDEFHXHJKLVG
      VCVHXRXHYPUNAXQXHYODYOVBVIVMVLVNXTYKYEXTYKUKZYEYDRXHXGWCUDZUOZYQYSQRVOZRY
      RUOZYQYTQQVOZRYAYRXTYAYRTZYKXTXRXQUKUUCYKVPXTXQXRAXSVQVRXHXGYADDVSVTWARQV
      OYTUUBVPYQRQQWBWDYQYAWEWFXTYSUUAVPYKXTYDYTRYRXTYBYRTZUKYCYBYAAXSUUDYCYBUN
      ABCDEFHIYBXGXHJKLMNOWGWHWIWJUSWKXTYEYSVPYKXTYDRXJYRXTEFXIURXGXHJYIXIVBZXS
      AXGFTZXQAUUFWLXRAXQUUFADFXGADEUQSFKAEFURJMWMWNZWOWPUSWQXSAXHFTZXRAUUHWLXQ
      AXRUUHADFXHUUGWOWPWDWQWRXCUSWKWSWTWTXARQXJXNXOXBXDXEUAUBDEGHIXIXMKYJUUEXF
      XD $.

    $d B x $.
    embedsetcestrc.b $e |- B = ( Base ` E ) $.
    $( The "embedding functor" from the category of sets into the category of
       extensible structures which sends each set to an extensible structure
       consisting of the base set slot only is an embedding.  According to
       definition 3.27 (1) of [Adamek] p. 34, a functor "F is called an
       _embedding_ provided that F is injective on morphisms", or according to
       remark 3.28 (1) in [Adamek] p. 34, "a functor is an embedding if and
       only if it is faithful and injective on objects".  (Contributed by AV,
       31-Mar-2020.) $)
    embedsetcestrc $p |- ( ph -> ( F ( S Faith E ) G /\ F : C -1-1-> B ) ) $=
      ( cfth co wbr wf1 fthsetcestrc embedsetcestrclem jca ) AIJFHSTUAEDIUBABCE
      FGHIJKLMNOPQUCABDEFGHIKLMNOQRUDUE $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Categorical constructions
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Product of categories
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Xc. $.
  $c 1stF $.
  $c 2ndF $.
  $c pairF $.

  $( Extend class notation with the product of two categories. $)
  cxpc $a class Xc. $.

  $( Extend class notation with the first projection functor. $)
  c1stf $a class 1stF $.

  $( Extend class notation with the second projection functor. $)
  c2ndf $a class 2ndF $.

  $( Extend class notation with the functor pairing operation. $)
  cprf $a class pairF $.

  ${
    $d b f g h r s u v x y $.
    $( Define the binary product of categories, which has objects for each pair
       of objects of the factors, and morphisms for each pair of morphisms of
       the factors.  Composition is componentwise.  (Contributed by Mario
       Carneiro, 10-Jan-2017.) $)
    df-xpc $a |- Xc. = ( r e. _V , s e. _V |->
    [_ ( ( Base ` r ) X. ( Base ` s ) ) / b ]_
    [_ ( u e. b , v e. b |-> ( ( ( 1st ` u ) ( Hom ` r ) ( 1st ` v ) ) X.
        ( ( 2nd ` u ) ( Hom ` s ) ( 2nd ` v ) ) ) ) / h ]_
    { <. ( Base ` ndx ) , b >. ,
      <. ( Hom ` ndx ) , h >. ,
      <. ( comp ` ndx ) , ( x e. ( b X. b ) , y e. b |->
        ( g e. ( ( 2nd ` x ) h y ) , f e. ( h ` x ) |->
        <. ( ( 1st ` g ) ( <. ( 1st ` ( 1st ` x ) ) ,
          ( 1st ` ( 2nd ` x ) ) >. ( comp ` r ) ( 1st ` y ) ) ( 1st ` f ) ) ,
           ( ( 2nd ` g ) ( <. ( 2nd ` ( 1st ` x ) ) ,
          ( 2nd ` ( 2nd ` x ) ) >. ( comp ` s ) ( 2nd ` y ) ) ( 2nd ` f ) ) >.
          ) ) >. } ) $.

    $( Define the first projection functor out of the product of categories.
       (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    df-1stf $a |- 1stF = ( r e. Cat , s e. Cat |->
    [_ ( ( Base ` r ) X. ( Base ` s ) ) / b ]_
      <. ( 1st |` b ) , ( x e. b , y e. b |->
        ( 1st |` ( x ( Hom ` ( r Xc. s ) ) y ) ) ) >. ) $.

    $( Define the second projection functor out of the product of categories.
       (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    df-2ndf $a |- 2ndF = ( r e. Cat , s e. Cat |->
    [_ ( ( Base ` r ) X. ( Base ` s ) ) / b ]_
      <. ( 2nd |` b ) , ( x e. b , y e. b |->
        ( 2nd |` ( x ( Hom ` ( r Xc. s ) ) y ) ) ) >. ) $.

    $( Define the pairing operation for functors (which takes two functors
       ` F : C --> D ` and ` G : C --> E ` and produces
       ` ( F pairF G ) : C --> ( D Xc. E ) ` ).  (Contributed by Mario
       Carneiro, 11-Jan-2017.) $)
    df-prf $a |- pairF = ( f e. _V , g e. _V |-> [_ dom ( 1st ` f ) / b ]_
      <. ( x e. b |-> <. ( ( 1st ` f ) ` x ) , ( ( 1st ` g ) ` x ) >. ) ,
         ( x e. b , y e. b |-> ( h e. dom ( x ( 2nd ` f ) y ) |->
    <. ( ( x ( 2nd ` f ) y ) ` h ) , ( ( x ( 2nd ` g ) y ) ` h ) >. ) ) >. ) $.

    $( The binary product of categories is a two-argument function.
       (Contributed by Mario Carneiro, 10-Jan-2017.) $)
    fnxpc $p |- Xc. Fn ( _V X. _V ) $=
      ( vr vs vb vh vu vv vx vy vg vf cv cbs cfv cxp c1st chom co c2nd cmpo cop
      cvv cnx cco ctp csb cxpc df-xpc tpex csbex fnmpoi ) ABUAUACAKZLMBKZLMNZDE
      FCKZUNEKZOMFKZOMUKPMQUORMUPRMULPMQNSZUBLMUNTZUBPMDKZTZUBUCMGHUNUNNUNIJGKZ
      RMZHKZUSQVAUSMIKZOMJKZOMVAOMZOMVBOMTVCOMUKUCMQQVDRMVERMVFRMVBRMTVCRMULUCM
      QQTSSTZUDZUEZUEUFGHFEJIDBACUGCUMVIDUQVHURUTVGUHUIUIUJ $.
  $}

  ${
    $d b f g h r s u v x y B $.  $d b h r s O $.  $d b f g h r s u v x y ph $.
    $d b f g h r s u v x y C $.  $d b f g h r s u v x y D $.
    $d b f g h r s x y K $.
    xpcval.t $e |- T = ( C Xc. D ) $.
    xpcval.x $e |- X = ( Base ` C ) $.
    xpcval.y $e |- Y = ( Base ` D ) $.
    xpcval.h $e |- H = ( Hom ` C ) $.
    xpcval.j $e |- J = ( Hom ` D ) $.
    xpcval.o1 $e |- .x. = ( comp ` C ) $.
    xpcval.o2 $e |- .xb = ( comp ` D ) $.
    xpcval.c $e |- ( ph -> C e. V ) $.
    xpcval.d $e |- ( ph -> D e. W ) $.
    xpcval.b $e |- ( ph -> B = ( X X. Y ) ) $.
    xpcval.k $e |- ( ph -> K = ( u e. B , v e. B |->
      ( ( ( 1st ` u ) H ( 1st ` v ) ) X. ( ( 2nd ` u ) J ( 2nd ` v ) ) ) ) ) $.
    xpcval.o $e |- ( ph -> O =
      ( x e. ( B X. B ) , y e. B |->
        ( g e. ( ( 2nd ` x ) K y ) , f e. ( K ` x ) |->
        <. ( ( 1st ` g ) ( <. ( 1st ` ( 1st ` x ) ) ,
          ( 1st ` ( 2nd ` x ) ) >. .x. ( 1st ` y ) ) ( 1st ` f ) ) ,
           ( ( 2nd ` g ) ( <. ( 2nd ` ( 1st ` x ) ) ,
          ( 2nd ` ( 2nd ` x ) ) >. .xb ( 2nd ` y ) ) ( 2nd ` f ) ) >. ) ) ) $.
    $( Value of the binary product of categories.  (Contributed by Mario
       Carneiro, 10-Jan-2017.) $)
    xpcval $p |- ( ph -> T = { <. ( Base ` ndx ) , B >. ,
        <. ( Hom ` ndx ) , K >. , <. ( comp ` ndx ) , O >. } ) $=
      ( vr vs vb vh cxpc co cnx cbs cfv cop chom cco ctp cvv cxp c1st c2nd cmpo
      cv csb wceq df-xpc wa wcel fvex xpex simprl fveq2d eqtr4di simprr xpeq12d
      a1i adantr eqtr4d vex mpoex simpr simplrl oveqd simplrr mpoeq123dv simplr
      ad2antrr opeq2d fveq1d opeq12d ad3antrrr csbied2 elexd tpex ovmpod eqtrid
      tpeq123d ) AJGHURUSUTVAVBZFVCZUTVDVBZPVCZUTVEVBZQVCZVFZUBAUNUOGHVGVGUPUNV
      LZVAVBZUOVLZVAVBZVHZUQEDUPVLZXSEVLZVIVBZDVLZVIVBZXNVDVBZUSZXTVJVBZYBVJVBZ
      XPVDVBZUSZVHZVKZXGXSVCZXIUQVLZVCZXKBCXSXSVHZXSMLBVLZVJVBZCVLZYMUSZYPYMVBZ
      MVLZVIVBZLVLZVIVBZYPVIVBZVIVBYQVIVBVCZYRVIVBZXNVEVBZUSZUSZUUAVJVBZUUCVJVB
      ZUUEVJVBYQVJVBVCZYRVJVBZXPVEVBZUSZUSZVCZVKZVKZVCZVFZVMZVMZXMURVGURUNUOVGV
      GUVDVKVNABCDELMUQUOUNUPVOWEAXNGVNZXPHVNZVPZVPZUPXRFUVCXMVGXRVGVQUVHXOXQXN
      VAVRXPVAVRVSWEUVHXRTUAVHZFUVHXOTXQUAUVHXOGVAVBTUVHXNGVAAUVEUVFVTWAUCWBUVH
      XQHVAVBUAUVHXPHVAAUVEUVFWCWAUDWBWDAFUVIVNUVGUKWFWGUVHXSFVNZVPZUQYKPUVBXMV
      GYKVGVQUVKEDXSXSYJUPWHZUVLWIWEUVKYKEDFFYAYCNUSZYFYGOUSZVHZVKZPUVKEDXSXSYJ
      FFUVOUVHUVJWJZUVQUVKYEUVMYIUVNUVKYDNYAYCUVKYDGVDVBNUVKXNGVDAUVEUVFUVJWKZW
      AUEWBWLUVKYHOYFYGUVKYHHVDVBOUVKXPHVDAUVEUVFUVJWMZWAUFWBWLWDWNAPUVPVNUVGUV
      JULWPWGUVKYMPVNZVPZYLXHYNXJUVAXLUWAXSFXGUVHUVJUVTWOZWQUWAYMPXIUVKUVTWJZWQ
      UWAUUTQXKUWAUUTBCFFVHZFMLYQYRPUSZYPPVBZUUBUUDUUFUUGKUSZUSZUUKUULUUMUUNIUS
      ZUSZVCZVKZVKZQUWABCYOXSUUSUWDFUWLUWAXSFXSFUWBUWBWDUWBUWAMLYSYTUURUWEUWFUW
      KUWAYMPYQYRUWCWLUWAYPYMPUWCWRUWAUUJUWHUUQUWJUWAUUIUWGUUBUUDUWAUUHKUUFUUGU
      WAUUHGVEVBKUWAXNGVEUVKUVEUVTUVRWFWAUGWBWLWLUWAUUPUWIUUKUULUWAUUOIUUMUUNUW
      AUUOHVEVBIUWAXPHVEUVKUVFUVTUVSWFWAUHWBWLWLWSWNWNAQUWMVNUVGUVJUVTUMWTWGWQX
      FXAXAAGRUIXBAHSUJXBXMVGVQAXHXJXLXCWEXDXE $.
  $}

  ${
    $d f g u v x y C $.  $d f g u v x y D $.  $d f g u v x y X $.
    $d f g u v x y Y $.
    xpcbas.t $e |- T = ( C Xc. D ) $.
    xpcbas.x $e |- X = ( Base ` C ) $.
    xpcbas.y $e |- Y = ( Base ` D ) $.
    $( Set of objects of the binary product of categories.  (Contributed by
       Mario Carneiro, 10-Jan-2017.) $)
    xpcbas $p |- ( X X. Y ) = ( Base ` T ) $=
      ( cvv cxp cbs cfv wceq cv c2nd c1st co eqid c0 cxpc vx vy vg vf wcel chom
      vu vv wa cmpo cop cco simpl simpr eqidd xpcval fvexi xpex a1i estrreslem1
      wn base0 wo fvprc eqtrid orim12i ianor xpeq0 3imtr4i wfn fnxpc fndm ax-mp
      cdm ndmov fveq2d 3eqtr4a pm2.61i ) AIUEZBIUEZUIZDEJZCKLZMWAWBCUAUBWBWBJWB
      UCUDUANZOLZUBNZUGUHWBWBUGNZPLUHNZPLAUFLZQWGOLWHOLBUFLZQJUJZQWDWKLUCNZPLUD
      NZPLWDPLZPLWEPLUKWFPLAULLZQQWLOLWMOLWNOLWEOLUKWFOLBULLZQQUKUJUJZWKIWAUAUB
      UHUGWBABWPCWOUDUCWIWJWKWQIIDEFGHWIRWJRWORWPRVSVTUMVSVTUNWAWBUOWAWKUOWAWQU
      OUPWBIUEWADEDAKGUQEBKHUQURUSUTWAVAZSSKLWBWCVBVSVAZVTVAZVCDSMZESMZVCWRWBSM
      WSXAWTXBWSDAKLSGAKVDVEWTEBKLSHBKVDVEVFVSVTVGDEVHVIWRCSKWRCABTQSFABITTIIJZ
      VJTVNXCMVKXCTVLVMVOVEVPVQVR $.
  $}

  ${
    $d f g u v x y B $.  $d f g u v x y C $.  $d f g u v x y D $.  $d u v X $.
    $d f g u v x y H $.  $d f g u v x y J $.  $d u v Y $.
    xpchomfval.t $e |- T = ( C Xc. D ) $.
    xpchomfval.y $e |- B = ( Base ` T ) $.
    xpchomfval.h $e |- H = ( Hom ` C ) $.
    xpchomfval.j $e |- J = ( Hom ` D ) $.
    xpchomfval.k $e |- K = ( Hom ` T ) $.
    $( Set of morphisms of the binary product of categories.  (Contributed by
       Mario Carneiro, 11-Jan-2017.)  (Proof shortened by AV, 1-Mar-2024.) $)
    xpchomfval $p |- K = ( u e. B , v e. B |->
      ( ( ( 1st ` u ) H ( 1st ` v ) ) X. ( ( 2nd ` u ) J ( 2nd ` v ) ) ) ) $=
      ( cvv c1st cfv co c2nd c0 vx vy vg vf wcel cxp cmpo wceq cnx cbs cop chom
      wa cv cco ctp c1 c5 cdc simpl simpr xpcbas eqtr4i a1i eqidd xpcval catstr
      eqid homid snsstp2 fvexi mpoex strfv3 cxpc wfn cdm fnxpc fndm ax-mp ndmov
      wn eqtrid fveq2d str0 3eqtr4g wo base0 olcd 0mpo0 syl eqtr4d pm2.61i ) DO
      UEZEOUEZUMZIBACCBUNZPQAUNZPQGRWPSQWQSQHRUFZUGZUHWOIWSUIUJQCUKZUIULQZWSUKZ
      UIUOQUAUBCCUFCUCUDUAUNZSQZUBUNZWSRXCWSQUCUNZPQUDUNZPQXCPQZPQXDPQUKXEPQDUO
      QZRRXFSQXGSQXHSQXDSQUKXESQEUOQZRRUKUGUGZUKZUPFULOUQUQURUSUKWOUAUBABCDEXJF
      XIUDUCGHWSXKOODUJQZEUJQZJXMVHZXNVHZLMXIVHXJVHWMWNUTWMWNVACXMXNUFZUHWOCFUJ
      QZXQKDEFXMXNJXOXPVBVCVDWOWSVEWOXKVEVFXKCWSVGVIWTXBXLVJWSOUEWOBACCWRCFUJKV
      KZXSVLVDNVMWOWAZITWSXTFULQTULQITXTFTULXTFDEVNRTJDEOVNVNOOUFZVOVNVPYAUHVQY
      AVNVRVSVTWBZWCNULXAVIWDWEXTCTUHZYCWFWSTUHXTYCYCXTXRTUJQCTXTFTUJYBWCKWGWEW
      HBACCWRWIWJWKWL $.

    xpchom.x $e |- ( ph -> X e. B ) $.
    xpchom.y $e |- ( ph -> Y e. B ) $.
    $( Set of morphisms of the binary product of categories.  (Contributed by
       Mario Carneiro, 11-Jan-2017.) $)
    xpchom $p |- ( ph -> ( X K Y ) =
      ( ( ( 1st ` X ) H ( 1st ` Y ) ) X. ( ( 2nd ` X ) J ( 2nd ` Y ) ) ) ) $=
      ( c1st cfv c2nd vu vv wcel co cxp wceq cv wa simpl fveq2d oveq12d xpeq12d
      simpr xpchomfval ovex xpex ovmpoa syl2anc ) AIBUCJBUCIJHUDIRSZJRSZFUDZITS
      ZJTSZGUDZUEZUFPQUAUBIJBBUAUGZRSZUBUGZRSZFUDZVFTSZVHTSZGUDZUEVEHVFIUFZVHJU
      FZUHZVJVAVMVDVPVGUSVIUTFVPVFIRVNVOUIZUJVPVHJRVNVOUMZUJUKVPVKVBVLVCGVPVFIT
      VQUJVPVHJTVRUJUKULUBUABCDEFGHKLMNOUNVAVDUSUTFUOVBVCGUOUPUQUR $.
  $}

  ${
    $d u v C $.  $d u v D $.  $d u v T $.
    relxpchom.t $e |- T = ( C Xc. D ) $.
    relxpchom.k $e |- K = ( Hom ` T ) $.
    $( A hom-set in the binary product of categories is a relation.
       (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    relxpchom $p |- Rel ( X K Y ) $=
      ( vu vv co cvv cxp wss cv c1st cfv chom c2nd eqid wrel cbs rgen2w ovmptss
      wral xpss xpchomfval ax-mp df-rel mpbir ) EFDKZUAUKLLMZNZIOZPQJOZPQARQZKZ
      UNSQUOSQBRQZKZMZULNZJCUBQZUEIVBUEUMVAIJVBVBUQUSUFUCIJVBVBUTEDFULJIVBABCUP
      URDGVBTUPTURTHUGUDUHUKUIUJ $.
  $}

  ${
    $d f g u v x y B $.  $d f g u v x y C $.  $d f g x y F $.  $d f g x y ph $.
    $d f g u v x y D $.  $d f g x y G $.  $d f g x y .x. $.  $d f g x y .xb $.
    $d f g x y K $.  $d f g x y X $.  $d f g x y Y $.  $d f g x y Z $.
    $d x y O $.
    xpccofval.t $e |- T = ( C Xc. D ) $.
    xpccofval.b $e |- B = ( Base ` T ) $.
    xpccofval.k $e |- K = ( Hom ` T ) $.
    xpccofval.o1 $e |- .x. = ( comp ` C ) $.
    xpccofval.o2 $e |- .xb = ( comp ` D ) $.
    xpccofval.o $e |- O = ( comp ` T ) $.
    $( Value of composition in the binary product of categories.  (Contributed
       by Mario Carneiro, 11-Jan-2017.)  (Proof shortened by AV,
       2-Mar-2024.) $)
    xpccofval $p |- O = ( x e. ( B X. B ) , y e. B |->
        ( g e. ( ( 2nd ` x ) K y ) , f e. ( K ` x ) |->
        <. ( ( 1st ` g ) ( <. ( 1st ` ( 1st ` x ) ) ,
          ( 1st ` ( 2nd ` x ) ) >. .x. ( 1st ` y ) ) ( 1st ` f ) ) ,
           ( ( 2nd ` g ) ( <. ( 2nd ` ( 1st ` x ) ) ,
          ( 2nd ` ( 2nd ` x ) ) >. .xb ( 2nd ` y ) ) ( 2nd ` f ) ) >. ) ) $=
      ( cfv c0 vv vu cvv wcel wa cxp cv c2nd co c1st cop cmpo wceq cnx cbs chom
      cco ctp c1 cdc eqid simpl simpr xpcbas eqtr4i a1i xpchomfval eqidd xpcval
      c5 catstr ccoid snsstp3 fvexi xpex mpoex strfv3 wn cxpc fnxpc fndmi ndmov
      eqtrid fveq2d str0 3eqtr4g wo base0 olcd 0mpo0 syl eqtr4d pm2.61i ) DUCUD
      ZEUCUDZUEZLABCCUFZCJIAUGZUHSZBUGZKUIWRKSJUGZUJSIUGZUJSWRUJSZUJSWSUJSUKWTU
      JSHUIUIXAUHSXBUHSXCUHSWSUHSUKWTUHSFUIUIUKULZULZUMWPLXEUNUOSCUKZUNUPSKUKZU
      NUQSZXEUKZURGUQUCUSUSVJUTUKWPABUAUBCDEFGHIJDUPSZEUPSZKXEUCUCDUOSZEUOSZMXL
      VAZXMVAZXJVAZXKVAZPQWNWOVBWNWOVCCXLXMUFZUMWPCGUOSZXRNDEGXLXMMXNXOVDVEVFKU
      BUACCUBUGZUJSUAUGZUJSXJUIXTUHSYAUHSXKUIUFULUMWPUAUBCDEGXJXKKMNXPXQOVGVFWP
      XEVHVIXECKVKVLXFXGXIVMXEUCUDWPABWQCXDCCCGUONVNZYBVOYBVPVFRVQWPVRZLTXEYCGU
      QSTUQSLTYCGTUQYCGDEVSUITMDEUCVSUCUCUFVSVTWAWBWCZWDRUQXHVLWEWFYCWQTUMZCTUM
      ZWGXETUMYCYFYEYCXSTUOSCTYCGTUOYDWDNWHWFWIABWQCXDWJWKWLWM $.

    xpcco.x $e |- ( ph -> X e. B ) $.
    xpcco.y $e |- ( ph -> Y e. B ) $.
    xpcco.z $e |- ( ph -> Z e. B ) $.
    xpcco.f $e |- ( ph -> F e. ( X K Y ) ) $.
    xpcco.g $e |- ( ph -> G e. ( Y K Z ) ) $.
    $( Value of composition in the binary product of categories.  (Contributed
       by Mario Carneiro, 11-Jan-2017.) $)
    xpcco $p |- ( ph -> ( G ( <. X , Y >. O Z ) F ) =
        <. ( ( 1st ` G ) ( <. ( 1st ` X ) ,
          ( 1st ` Y ) >. .x. ( 1st ` Z ) ) ( 1st ` F ) ) ,
           ( ( 2nd ` G ) ( <. ( 2nd ` X ) ,
          ( 2nd ` Y ) >. .xb ( 2nd ` Z ) ) ( 2nd ` F ) ) >. ) $=
      ( vx vy vg vf cxp cv c2nd cfv co c1st cop cmpo wceq xpccofval cvv opelxpd
      wcel adantr ovex fvex mpoex a1i simprl fveq2d op2ndg syl2anc eqtrd simprr
      wa oveq12d eleqtrrd eqtr4di opex op1stg opeq12d simplrr oveq123d ovmpodv2
      df-ov ovmpodv mpi ) AKUFUGBBUJZBUHUIUFUKZULUMZUGUKZJUNZWHJUMZUHUKZUOUMZUI
      UKZUOUMZWHUOUMZUOUMZWIUOUMZUPZWJUOUMZGUNZUNZWMULUMZWOULUMZWQULUMZWIULUMZU
      PZWJULUMZEUNZUNZUPZUQZUQURIHLMUPZNKUNZUNIUOUMZHUOUMZLUOUMZMUOUMZUPZNUOUMZ
      GUNZUNZIULUMZHULUMZLULUMZMULUMZUPZNULUMZEUNZUNZUPZURZUFUGBCDEFGUIUHJKOPQR
      STUSAYMUFUGXNNWGBXMKUTALMBBUAUBVAANBVBWHXNURZUCVCXMUTVBAYNWJNURZVNZVNZUHU
      IWKWLXLWIWJJVDWHJVEVFVGYQUHUIIHWKWLXLYLXOUTYQIMNJUNZWKAIYRVBYPUEVCYQWIMWJ
      NJYQWIXNULUMZMYQWHXNULAYNYOVHZVIAYSMURZYPALBVBZMBVBZUUAUAUBLMBBVJVKVCVLZA
      YNYOVMVOVPYQHWLVBWMIURZYQHLMJUNZWLAHUUFVBYPUDVCYQWLXNJUMUUFYQWHXNJYTVILMJ
      WDVQVPVCXLUTVBYQUUEWOHURZVNZVNZXCXKVRVGUUIXCYCXKYKUUIWNXPWPXQXBYBUUIWTXTX
      AYAGUUIWRXRWSXSUUIWQLUOYQWQLURUUHYQWQXNUOUMZLYQWHXNUOYTVIAUUJLURZYPAUUBUU
      CUUKUAUBLMBBVSVKVCVLVCZVIUUIWIMUOYQWIMURUUHUUDVCZVIVTUUIWJNUOAYNYOUUHWAZV
      IVOUUIWMIUOYQUUEUUGVHZVIUUIWOHUOYQUUEUUGVMZVIWBUUIXDYDXEYEXJYJUUIXHYHXIYI
      EUUIXFYFXGYGUUIWQLULUULVIUUIWIMULUUMVIVTUUIWJNULUUNVIVOUUIWMIULUUOVIUUIWO
      HULUUPVIWBVTWCWEWF $.
  $}

  ${
    xpcco1st.t $e |- T = ( C Xc. D ) $.
    xpcco1st.b $e |- B = ( Base ` T ) $.
    xpcco1st.k $e |- K = ( Hom ` T ) $.
    xpcco1st.o $e |- O = ( comp ` T ) $.
    xpcco1st.x $e |- ( ph -> X e. B ) $.
    xpcco1st.y $e |- ( ph -> Y e. B ) $.
    xpcco1st.z $e |- ( ph -> Z e. B ) $.
    xpcco1st.f $e |- ( ph -> F e. ( X K Y ) ) $.
    xpcco1st.g $e |- ( ph -> G e. ( Y K Z ) ) $.
    ${
      xpcco1st.1 $e |- .x. = ( comp ` C ) $.
      $( Value of composition in the binary product of categories.
         (Contributed by Mario Carneiro, 11-Jan-2017.) $)
      xpcco1st $p |- ( ph -> ( 1st ` ( G ( <. X , Y >. O Z ) F ) ) =
        ( ( 1st ` G ) ( <. ( 1st ` X ) ,
          ( 1st ` Y ) >. .x. ( 1st ` Z ) ) ( 1st ` F ) ) ) $=
        ( cop co c1st cfv c2nd cco wceq eqid xpcco ovex op1std syl ) AHGKLUDMJU
        EUEZHUFUGZGUFUGZKUFUGLUFUGUDMUFUGFUEZUEZHUHUGZGUHUGZKUHUGLUHUGUDMUHUGDU
        IUGZUEZUEZUDUJUPUFUGUTUJABCDVCEFGHIJKLMNOPUCVCUKQRSTUAUBULUTVEUPUQURUSU
        MVAVBVDUMUNUO $.
    $}

    ${
      xpcco2nd.1 $e |- .x. = ( comp ` D ) $.
      $( Value of composition in the binary product of categories.
         (Contributed by Mario Carneiro, 11-Jan-2017.) $)
      xpcco2nd $p |- ( ph -> ( 2nd ` ( G ( <. X , Y >. O Z ) F ) ) =
        ( ( 2nd ` G ) ( <. ( 2nd ` X ) ,
          ( 2nd ` Y ) >. .x. ( 2nd ` Z ) ) ( 2nd ` F ) ) ) $=
        ( cop co c1st cfv cco c2nd wceq eqid xpcco ovex op2ndd syl ) AHGKLUDMJU
        EUEZHUFUGZGUFUGZKUFUGLUFUGUDMUFUGCUHUGZUEZUEZHUIUGZGUIUGZKUIUGLUIUGUDMU
        IUGFUEZUEZUDUJUPUIUGVEUJABCDFEUSGHIJKLMNOPUSUKUCQRSTUAUBULVAVEUPUQURUTU
        MVBVCVDUMUNUO $.
    $}
  $}

  ${
    xpcco2.t $e |- T = ( C Xc. D ) $.
    xpcco2.x $e |- X = ( Base ` C ) $.
    xpcco2.y $e |- Y = ( Base ` D ) $.
    xpcco2.h $e |- H = ( Hom ` C ) $.
    xpcco2.j $e |- J = ( Hom ` D ) $.
    xpcco2.m $e |- ( ph -> M e. X ) $.
    xpcco2.n $e |- ( ph -> N e. Y ) $.
    xpcco2.p $e |- ( ph -> P e. X ) $.
    xpcco2.q $e |- ( ph -> Q e. Y ) $.
    ${
      xpchom2.k $e |- K = ( Hom ` T ) $.
      $( Value of the set of morphisms in the binary product of categories.
         (Contributed by Mario Carneiro, 11-Jan-2017.) $)
      xpchom2 $p |- ( ph ->
        ( <. M , N >. K <. P , Q >. ) = ( ( M H P ) X. ( N J Q ) ) ) $=
        ( cop c1st cfv c2nd cxp xpcbas opelxpd xpchom wcel wceq syl2anc oveq12d
        co op1stg op2ndg xpeq12d eqtrd ) AJKUDZDEUDZIUPVAUEUFZVBUEUFZGUPZVAUGUF
        ZVBUGUFZHUPZUHJDGUPZKEHUPZUHALMUHBCFGHIVAVBNBCFLMNOPUIQRUCAJKLMSTUJADEL
        MUAUBUJUKAVEVIVHVJAVCJVDDGAJLULZKMULZVCJUMSTJKLMUQUNADLULZEMULZVDDUMUAU
        BDELMUQUNUOAVFKVGEHAVKVLVFKUMSTJKLMURUNAVMVNVGEUMUAUBDELMURUNUOUSUT $.
    $}

    xpcco2.o1 $e |- .x. = ( comp ` C ) $.
    xpcco2.o2 $e |- .xb = ( comp ` D ) $.
    xpcco2.o $e |- O = ( comp ` T ) $.
    xpcco2.r $e |- ( ph -> R e. X ) $.
    xpcco2.s $e |- ( ph -> S e. Y ) $.
    xpcco2.f $e |- ( ph -> F e. ( M H P ) ) $.
    xpcco2.g $e |- ( ph -> G e. ( N J Q ) ) $.
    xpcco2.k $e |- ( ph -> K e. ( P H R ) ) $.
    xpcco2.l $e |- ( ph -> L e. ( Q J S ) ) $.
    $( Value of composition in the binary product of categories.  (Contributed
       by Mario Carneiro, 11-Jan-2017.) $)
    xpcco2 $p |- ( ph -> ( <. K , L >. ( <. <. M , N >. ,
      <. P , Q >. >. O <. R , S >. ) <. F , G >. ) =
        <. ( K ( <. M , P >. .x. R ) F ) ,
           ( L ( <. N , Q >. .xb S ) G ) >. ) $=
      ( cop co c1st cfv c2nd cxp chom xpcbas eqid opelxpd xpchom2 eleqtrrd wcel
      xpcco wceq op1stg syl2anc opeq12d oveq12d oveq123d op2ndg eqtrd ) AOPUTZK
      LUTZQRUTZDEUTZUTFGUTZSVAVAWBVBVCZWCVBVCZWDVBVCZWEVBVCZUTZWFVBVCZJVAZVAZWB
      VDVCZWCVDVCZWDVDVCZWEVDVCZUTZWFVDVCZHVAZVAZUTOKQDUTZFJVAZVAZPLREUTZGHVAZV
      AZUTATUAVEBCHIJWCWBIVFVCZSWDWEWFUBBCITUAUBUCUDVGXIVHZUKULUMAQRTUAUGUHVIAD
      ETUAUIUJVIAFGTUAUNUOVIAWCQDMVAZRENVAZVEWDWEXIVAAKLXKXLUPUQVIABCDEIMNXIQRT
      UAUBUCUDUEUFUGUHUIUJXJVJVKAWBDFMVAZEGNVAZVEWEWFXIVAAOPXMXNURUSVIABCFGIMNX
      IDETUAUBUCUDUEUFUIUJUNUOXJVJVKVMAWNXEXBXHAWGOWHKWMXDAWKXCWLFJAWIQWJDAQTVL
      ZRUAVLZWIQVNUGUHQRTUAVOVPADTVLZEUAVLZWJDVNUIUJDETUAVOVPVQAFTVLZGUAVLZWLFV
      NUNUOFGTUAVOVPVRAOXMVLZPXNVLZWGOVNURUSOPXMXNVOVPAKXKVLZLXLVLZWHKVNUPUQKLX
      KXLVOVPVSAWOPWPLXAXGAWSXFWTGHAWQRWREAXOXPWQRVNUGUHQRTUAVTVPAXQXRWREVNUIUJ
      DETUAVTVPVQAXSXTWTGVNUNUOFGTUAVTVPVRAYAYBWOPVNURUSOPXMXNVTVPAYCYDWPLVNUPU
      QKLXKXLVTVPVSVQWA $.
  $}

  ${
    $d f g h s t u v x y I $.  $d f g h s t u v x y J $.  $d f g h s t u v T $.
    $d x y C $.  $d f g h s t u v x y ph $.  $d f g h s t u v x y X $.
    $d x y D $.  $d x y R $.  $d x y S $.  $d f g h s t u v x y Y $.
    xpccat.t $e |- T = ( C Xc. D ) $.
    xpccat.c $e |- ( ph -> C e. Cat ) $.
    xpccat.d $e |- ( ph -> D e. Cat ) $.
    ${
      xpccat.x $e |- X = ( Base ` C ) $.
      xpccat.y $e |- Y = ( Base ` D ) $.
      xpccat.i $e |- I = ( Id ` C ) $.
      xpccat.j $e |- J = ( Id ` D ) $.
      $( The product of two categories is a category.  (Contributed by Mario
         Carneiro, 11-Jan-2017.) $)
      xpccatid $p |- ( ph -> ( T e. Cat /\ ( Id ` T ) = ( x e. X , y e. Y |->
        <. ( I ` x ) , ( J ` y ) >. ) ) ) $=
        ( wcel cfv co vt vs vu vv vf vg vh ccat ccid cxp cv c1st c2nd cmpt wceq
        cop wa cmpo chom w3a cco cvv cbs xpcbas a1i eqidd cxpc biid eqid adantr
        ovexi xp1st adantl catidcl xp2nd opelxpd simpr xpchom fvex op1st oveq1i
        eleqtrrd simpr1l syl simpr1r simpr31 eleqtrd catlid eqtrid op2nd syldan
        opeq12d 1st2nd2 3eqtr4d simpr2l simpr32 catcocl 3eltr4d simpr2r simpr33
        xpcco oveq2i catrid catass fveq2d ovex eqtrdi oveq1d oveq2d iscatd2 vex
        op1std op2ndd mpompt eqeq2i anbi2i sylib ) AFUHRZFUISZUAIJUJZUAUKZULSZG
        SZYAUMSZHSZUPZUNZUOZUQXRXSBCIJBUKZGSZCUKZHSZUPZURZUOZUQAUBUKZXTRZYAXTRZ
        UQZUCUKZXTRZUDUKZXTRZUQZUEUKZYPYAFUSSZTZRZUFUKZYAYTUUFTZRZUGUKZYTUUBUUF
        TZRZUTZUTZUBUAUCUDXTFFVASZYFUEUFUGUUFVBXTFVCSUOADEFIJKNOVDZVEAUUFVFAUUQ
        VFFVBRAFDEVGKVKVEUUPVHAYRUQZYFYBYBDUSSZTZYDYDEUSSZTZUJYAYAUUFTZUUSYCYEU
        VAUVCUUSIDGUUTYBNUUTVIZPADUHRZYRLVJYRYBIRZAYAIJVLZVMVNUUSJEHUVBYDOUVBVI
        ZQAEUHRZYRMVJYRYDJRZAYAIJVOZVMVNVPUUSXTDEFUUTUVBUUFYAYAKUURUVEUVIUUFVIZ
        AYRVQZUVNVRWBZAUUPUQZYFULSZUUEULSZYPULSZYBUPZYBDVASZTZTZYFUMSZUUEUMSZYP
        UMSZYDUPZYDEVASZTZTZUPUVRUWEUPZYFUUEYPYAUPZYAUUQTTUUEUVPUWCUVRUWJUWEUVP
        UWCYCUVRUWBTUVRUVQYCUVRUWBYCYEYBGVSZYDHVSZVTZWAUVPIDUWAGUVRUUTUVSYBNUVE
        PAUVFUUPLVJZUVPYQUVSIRYQYRUUDUUOAWCZYPIJVLWDZUWAVIZUVPYRUVGYQYRUUDUUOAW
        EZUVHWDZUVPUUEUVSYBUUTTZUWFYDUVBTZUJZRZUVRUXBRUVPUUEUUGUXDUUHUUKUUNYSUU
        DAWFZUVPXTDEFUUTUVBUUFYPYAKUURUVEUVIUVMUWQUWTVRWGZUUEUXBUXCVLWDZWHWIUVP
        UWJYEUWEUWITUWEUWDYEUWEUWIYCYEUWMUWNWJZWAUVPJEUWHHUWEUVBUWFYDOUVIQAUVJU
        UPMVJZUVPYQUWFJRUWQYPIJVOWDZUWHVIZUVPYRUVKUWTUVLWDZUVPUXEUWEUXCRUXGUUEU
        XBUXCVOWDZWHWIWLUVPXTDEUWHFUWAUUEYFUUFUUQYPYAYAKUURUVMUWSUXLUUQVIZUWQUW
        TUWTUXFAUUPYRYFUVDRUWTUVOWKZXAUVPUXEUUEUWKUOUXGUUEUXBUXCWMWDWNUVPUUIULS
        ZUVQYBYBUPYTULSZUWATZTZUUIUMSZUWDYDYDUPYTUMSZUWHTZTZUPUXQUYAUPZUUIYFYAY
        AUPYTUUQTTUUIUVPUXTUXQUYDUYAUVPUXTUXQYCUXSTUXQUVQYCUXQUXSUWOXBUVPIDUWAG
        UXQUUTYBUXRNUVEPUWPUXAUWSUVPUUAUXRIRUUAUUCYSUUOAWOZYTIJVLWDZUVPUUIYBUXR
        UUTTZYDUYBUVBTZUJZRZUXQUYHRUVPUUIUUJUYJUUHUUKUUNYSUUDAWPZUVPXTDEFUUTUVB
        UUFYAYTKUURUVEUVIUVMUWTUYFVRWGZUUIUYHUYIVLWDZXCWIUVPUYDUYAYEUYCTUYAUWDY
        EUYAUYCUXIXBUVPJEUWHHUYAUVBYDUYBOUVIQUXJUXMUXLUVPUUAUYBJRUYFYTIJVOWDZUV
        PUYKUYAUYIRUYMUUIUYHUYIVOWDZXCWIWLUVPXTDEUWHFUWAYFUUIUUFUUQYAYAYTKUURUV
        MUWSUXLUXOUWTUWTUYFUXPUYLXAUVPUYKUUIUYEUOUYMUUIUYHUYIWMWDWNUVPUXQUVRUVT
        UXRUWATZTZUYAUWEUWGUYBUWHTZTZUPZUVSUXRUUTTZUWFUYBUVBTZUJUUIUUEUWLYTUUQT
        TZYPYTUUFTUVPUYRUYTVUBVUCUVPIDUWAUVRUXQUUTUVSYBUXRNUVEUWSUWPUWRUXAUYGUX
        HUYNWQUVPJEUWHUWEUYAUVBUWFYDUYBOUVIUXLUXJUXKUXMUYOUXNUYPWQVPUVPXTDEUWHF
        UWAUUEUUIUUFUUQYPYAYTKUURUVMUWSUXLUXOUWQUWTUYFUXFUYLXAZUVPXTDEFUUTUVBUU
        FYPYTKUURUVEUVIUVMUWQUYFVRWRZUVPUULUUIYAYTUPUUBUUQTTZULSZUVRUVTUUBULSZU
        WATZTZVUGUMSZUWEUWGUUBUMSZUWHTZTZUPUULULSZVUDULSZUVSUXRUPVUIUWATZTZUULU
        MSZVUDUMSZUWFUYBUPVUMUWHTZTZUPVUGUUEUWLUUBUUQTTUULVUDYPYTUPUUBUUQTTUVPV
        UKVUSVUOVVCUVPVUPUXQYBUXRUPVUIUWATZTZUVRVUJTVUPUYRVURTVUKVUSUVPIDUWAUVR
        UXQUUTVUPVUIUVSYBUXRNUVEUWSUWPUWRUXAUYGUXHUYNUVPUUCVUIIRUUAUUCYSUUOAWSZ
        UUBIJVLWDZUVPUULUXRVUIUUTTZUYBVUMUVBTZUJZRZVUPVVHRUVPUULUUMVVJUUHUUKUUN
        YSUUDAWTZUVPXTDEFUUTUVBUUFYTUUBKUURUVEUVIUVMUYFVVFVRWGZUULVVHVVIVLWDZXD
        UVPVUHVVEUVRVUJUVPVUHVVEVUTUYAYDUYBUPVUMUWHTZTZUPZULSVVEUVPVUGVVQULUVPX
        TDEUWHFUWAUUIUULUUFUUQYAYTUUBKUURUVMUWSUXLUXOUWTUYFVVFUYLVVLXAZXEVVEVVP
        VUPUXQVVDXFZVUTUYAVVOXFZVTXGXHUVPVUQUYRVUPVURUVPVUQVUAULSUYRUVPVUDVUAUL
        VUEXEUYRUYTUXQUVRUYQXFZUYAUWEUYSXFZVTXGXIWNUVPVVPUWEVUNTVUTUYTVVBTVUOVV
        CUVPJEUWHUWEUYAUVBVUTVUMUWFYDUYBOUVIUXLUXJUXKUXMUYOUXNUYPUVPUUCVUMJRVVF
        UUBIJVOWDZUVPVVKVUTVVIRVVMUULVVHVVIVOWDZXDUVPVULVVPUWEVUNUVPVULVVQUMSVV
        PUVPVUGVVQUMVVRXEVVEVVPVVSVVTWJXGXHUVPVVAUYTVUTVVBUVPVVAVUAUMSUYTUVPVUD
        VUAUMVUEXEUYRUYTVWAVWBWJXGXIWNWLUVPXTDEUWHFUWAUUEVUGUUFUUQYPYAUUBKUURUV
        MUWSUXLUXOUWQUWTVVFUXFUVPVVQYBVUIUUTTZYDVUMUVBTZUJVUGYAUUBUUFTUVPVVEVVP
        VWEVWFUVPIDUWAUXQVUPUUTYBUXRVUINUVEUWSUWPUXAUYGVVGUYNVVNWQUVPJEUWHUYAVU
        TUVBYDUYBVUMOUVIUXLUXJUXMUYOVWCUYPVWDWQVPVVRUVPXTDEFUUTUVBUUFYAUUBKUURU
        VEUVIUVMUWTVVFVRWRXAUVPXTDEUWHFUWAVUDUULUUFUUQYPYTUUBKUURUVMUWSUXLUXOUW
        QUYFVVFVUFVVLXAWNXJYHYOXRYGYNXSBCUAIJYFYMYAYIYKUPUOZYCYJYEYLVWGYBYIGYIY
        KYABXKZCXKZXLXEVWGYDYKHYIYKYAVWHVWIXMXEWLXNXOXPXQ $.

      xpcid.1 $e |- .1. = ( Id ` T ) $.
      xpcid.r $e |- ( ph -> R e. X ) $.
      xpcid.s $e |- ( ph -> S e. Y ) $.
      $( The identity morphism in the product of categories.  (Contributed by
         Mario Carneiro, 11-Jan-2017.) $)
      xpcid $p |- ( ph ->
        ( .1. ` <. R , S >. ) = <. ( I ` R ) , ( J ` S ) >. ) $=
        ( vx vy cop cfv co df-ov cvv ccid cmpo ccat wcel xpccatid simprd eqtrid
        cv wceq wa simprl fveq2d simprr opeq12d opex a1i ovmpod eqtr3id ) ADEUD
        GUEDEGUFDHUEZEIUEZUDZDEGUGAUBUCDEJKUBUPZHUEZUCUPZIUEZUDZVIGUHAGFUIUEZUB
        UCJKVNUJZSAFUKULVOVPUQAUBUCBCFHIJKLMNOPQRUMUNUOAVJDUQZVLEUQZURURZVKVGVM
        VHVSVJDHAVQVRUSUTVSVLEIAVQVRVAUTVBTUAVIUHULAVGVHVCVDVEVF $.
    $}

    $( The product of two categories is a category.  (Contributed by Mario
       Carneiro, 11-Jan-2017.) $)
    xpccat $p |- ( ph -> T e. Cat ) $=
      ( vx vy ccat wcel ccid cfv cbs cv cop cmpo wceq eqid xpccatid simpld ) AD
      JKDLMHIBNMZCNMZHOBLMZMIOCLMZMPQRAHIBCDUDUEUBUCEFGUBSUCSUDSUESTUA $.
  $}

  ${
    $d b c d x y B $.  $d b c d x y C $.  $d b c d x y D $.  $d b c d x y H $.
    $d x y ph $.  $d x y R $.  $d x y S $.
    1stfval.t $e |- T = ( C Xc. D ) $.
    1stfval.b $e |- B = ( Base ` T ) $.
    1stfval.h $e |- H = ( Hom ` T ) $.
    1stfval.c $e |- ( ph -> C e. Cat ) $.
    1stfval.d $e |- ( ph -> D e. Cat ) $.
    ${
      1stfval.p $e |- P = ( C 1stF D ) $.
      $( Value of the first projection functor.  (Contributed by Mario
         Carneiro, 11-Jan-2017.) $)
      1stfval $p |- ( ph -> P = <. ( 1st |` B ) ,
        ( x e. B , y e. B |-> ( 1st |` ( x H y ) ) ) >. ) $=
        ( co c1st cv cbs cfv vc vd c1stf cres cmpo cop ccat wcel wceq cxpc chom
        vb cxp csb wa cvv fvex xpex a1i simpl fveq2d xpeq12d eqid xpcbas eqtr4i
        eqtrdi reseq2d simpll simplr oveq12d eqtr4di mpoeq123dv opeq12d csbied2
        simpr oveqd df-1stf opex ovmpoa syl2anc eqtrid ) AGEFUCPZQDUDZBCDDQBRZC
        RZIPZUDZUEZUFZOAEUGUHFUGUHWBWIUIMNUAUBEFUGUGULUARZSTZUBRZSTZUMZQULRZUDZ
        BCWOWOQWDWEWJWLUJPZUKTZPZUDZUEZUFZUNWIUCWJEUIZWLFUIZUOZULWNDXBWIUPWNUPU
        HXEWKWMWJSUQWLSUQURUSXEWNESTZFSTZUMZDXEWKXFWMXGXEWJESXCXDUTVAXEWLFSXCXD
        VOVAVBXHHSTDEFHXFXGJXFVCXGVCVDKVEVFXEWODUIZUOZWPWCXAWHXJWODQXEXIVOZVGXJ
        BCWOWOWTDDWGXKXKXJWSWFQXJWRIWDWEXJWRHUKTIXJWQHUKXJWQEFUJPHXJWJEWLFUJXCX
        DXIVHXCXDXIVIVJJVKVALVKVPVGVLVMVNBCUBUAULVQWCWHVRVSVTWA $.

      1stf1.p $e |- ( ph -> R e. B ) $.
      $( Value of the first projection on an object.  (Contributed by Mario
         Carneiro, 11-Jan-2017.) $)
      1stf1 $p |- ( ph -> ( ( 1st ` P ) ` R ) = ( 1st ` R ) ) $=
        ( vx vy c1st cfv cvv cres cv co cmpo wceq 1stfval wfun wcel fo1st fofun
        cop wfo ax-mp cbs fvexi resfunexg mp2an mpoex op1std syl fveq1d fvresd
        eqtrd ) AFERSZSFRBUAZSFRSAFVDVEAEVEPQBBRPUBQUBHUCUAZUDZUKUEVDVEUEAPQBCD
        EGHIJKLMNUFVEVGERUGZBTUHVETUHTTRULVHUITTRUJUMBGUNJUOZRBTUPUQPQBBVFVIVIU
        RUSUTVAAFBROVBVC $.

      1stf2.p $e |- ( ph -> S e. B ) $.
      $( Value of the first projection on a morphism.  (Contributed by Mario
         Carneiro, 11-Jan-2017.) $)
      1stf2 $p |- ( ph -> ( R ( 2nd ` P ) S ) = ( 1st |` ( R H S ) ) ) $=
        ( vx c1st cvv vy cv cres c2nd cfv cmpo cop wceq 1stfval wfun wcel fo1st
        co wfo fofun ax-mp cbs fvexi resfunexg mp2an mpoex op2ndd syl wa simprl
        simprr oveq12d reseq2d ovex a1i ovmpod ) ARUAFGBBSRUBZUAUBZIUMZUCZSFGIU
        MZUCZEUDUEZTAESBUCZRUABBVOUFZUGUHVRVTUHARUABCDEHIJKLMNOUIVSVTESUJZBTUKV
        STUKTTSUNWAULTTSUOUPZBHUQKURZSBTUSUTRUABBVOWCWCVAVBVCAVLFUHZVMGUHZVDVDZ
        VNVPSWFVLFVMGIAWDWEVEAWDWEVFVGVHPQVQTUKZAWAVPTUKWGWBFGIVISVPTUSUTVJVK
        $.
    $}

    ${
      2ndfval.p $e |- Q = ( C 2ndF D ) $.
      $( Value of the first projection functor.  (Contributed by Mario
         Carneiro, 11-Jan-2017.) $)
      2ndfval $p |- ( ph -> Q = <. ( 2nd |` B ) ,
        ( x e. B , y e. B |-> ( 2nd |` ( x H y ) ) ) >. ) $=
        ( co c2nd cv cbs cfv vc vd c2ndf cres cmpo cop ccat wcel wceq cxpc chom
        vb cxp csb wa cvv fvex xpex a1i simpl fveq2d xpeq12d eqid xpcbas eqtr4i
        eqtrdi reseq2d simpll simplr oveq12d eqtr4di mpoeq123dv opeq12d csbied2
        simpr oveqd df-2ndf opex ovmpoa syl2anc eqtrid ) AGEFUCPZQDUDZBCDDQBRZC
        RZIPZUDZUEZUFZOAEUGUHFUGUHWBWIUIMNUAUBEFUGUGULUARZSTZUBRZSTZUMZQULRZUDZ
        BCWOWOQWDWEWJWLUJPZUKTZPZUDZUEZUFZUNWIUCWJEUIZWLFUIZUOZULWNDXBWIUPWNUPU
        HXEWKWMWJSUQWLSUQURUSXEWNESTZFSTZUMZDXEWKXFWMXGXEWJESXCXDUTVAXEWLFSXCXD
        VOVAVBXHHSTDEFHXFXGJXFVCXGVCVDKVEVFXEWODUIZUOZWPWCXAWHXJWODQXEXIVOZVGXJ
        BCWOWOWTDDWGXKXKXJWSWFQXJWRIWDWEXJWRHUKTIXJWQHUKXJWQEFUJPHXJWJEWLFUJXCX
        DXIVHXCXDXIVIVJJVKVALVKVPVGVLVMVNBCUBUAULVQWCWHVRVSVTWA $.

      2ndf1.p $e |- ( ph -> R e. B ) $.
      $( Value of the first projection on an object.  (Contributed by Mario
         Carneiro, 11-Jan-2017.) $)
      2ndf1 $p |- ( ph -> ( ( 1st ` Q ) ` R ) = ( 2nd ` R ) ) $=
        ( vx vy cfv c2nd cvv c1st cres cv cmpo cop wceq 2ndfval wfun wcel fo2nd
        co wfo fofun ax-mp cbs fvexi resfunexg mp2an mpoex op1std fveq1d fvresd
        syl eqtrd ) AFEUARZRFSBUBZRFSRAFVEVFAEVFPQBBSPUCQUCHUKUBZUDZUEUFVEVFUFA
        PQBCDEGHIJKLMNUGVFVHESUHZBTUIVFTUITTSULVIUJTTSUMUNBGUOJUPZSBTUQURPQBBVG
        VJVJUSUTVCVAAFBSOVBVD $.

      2ndf2.p $e |- ( ph -> S e. B ) $.
      $( Value of the first projection on a morphism.  (Contributed by Mario
         Carneiro, 11-Jan-2017.) $)
      2ndf2 $p |- ( ph -> ( R ( 2nd ` Q ) S ) = ( 2nd |` ( R H S ) ) ) $=
        ( vx c2nd cvv vy cv co cres cfv cmpo wceq 2ndfval wfun wcel fo2nd fofun
        cop wfo ax-mp cbs fvexi resfunexg mp2an mpoex op2ndd syl simprl oveq12d
        wa simprr reseq2d ovex a1i ovmpod ) ARUAFGBBSRUBZUAUBZIUCZUDZSFGIUCZUDZ
        ESUEZTAESBUDZRUABBVNUFZUMUGVQVSUGARUABCDEHIJKLMNOUHVRVSESUIZBTUJVRTUJTT
        SUNVTUKTTSULUOZBHUPKUQZSBTURUSRUABBVNWBWBUTVAVBAVKFUGZVLGUGZVEVEZVMVOSW
        EVKFVLGIAWCWDVCAWCWDVFVDVGPQVPTUJZAVTVOTUJWFWAFGIVHSVOTURUSVIVJ $.
    $}
  $}

  ${
    $d f g x y z C $.  $d f g x y z D $.  $d f g x y z P $.  $d f g x y z ph $.
    $d f g x y z Q $.  $d f g x y z T $.
    1stfcl.t $e |- T = ( C Xc. D ) $.
    1stfcl.c $e |- ( ph -> C e. Cat ) $.
    1stfcl.d $e |- ( ph -> D e. Cat ) $.
    ${
      1stfcl.p $e |- P = ( C 1stF D ) $.
      $( The first projection functor is a functor onto the left argument.
         (Contributed by Mario Carneiro, 11-Jan-2017.) $)
      1stfcl $p |- ( ph -> P e. ( T Func C ) ) $=
        ( vx vy c1st cfv cop co eqid wceq cvv wcel fvresd vz vf vg cbs cxp cres
        c2nd cfunc cv chom cmpo xpcbas 1stfval wfun fo1st fofun ax-mp fvex xpex
        wfo resfunexg mp2an mpoex op2ndd syl opeq2d eqtr4d wbr cco ccid f1stres
        xpccat wf a1i wfn ovex fnmpoi fneq1d mpbiri wa ccat adantr simprl 1stf2
        simprr xpchom reseq2d eqtrd feq1d fvres ad2antrl ad2antll feq23d mpbird
        oveq12d simpr catidcl 1st2nd2 adantl fveq2d xp1st op1std fveq1d 3eqtr4d
        xp2nd xpcid 3ad2ant1 simp21 simp22 simp23 simp3l simp3r catcocl opeq12d
        w3a xpcco1st oveq123d isfuncd df-br sylib eqeltrd ) ADLBUDMZCUDMZUEZUFZ
        DUGMZNZEBUHOZADYEJKYDYDLJUIZKUIZEUJMZOZUFZUKZNZYGAJKYDBCDEYKFBCEYBYCFYB
        PZYCPZULZYKPZGHIUMZAYFYNYEADYOQYFYNQYTYEYNDLUNZYDRSYERSRRLUTUUAUORRLUPU
        QZYBYCBUDURCUDURUSZLYDRVAVBJKYDYDYMUUCUUCVCVDVEZVFVGAYEYFYHVHYGYHSAJKUA
        YDYBEEVIMZEVJMZUBUCBYEYFYKBVJMZBUJMZBVIMZYRYPYSUUHPZUUFPZUUGPZUUEPZUUIP
        ZABCEFGHVLZGYDYBYEVMAYBYCVKVNAYFYDYDUEZVOYNUUPVOJKYDYDYMYNYNPUUAYLRSYMR
        SUUBYIYJYKVPLYLRVAVBVQAUUPYFYNUUDVRVSAYIYDSZYJYDSZVTZVTZYLYIYEMZYJYEMZU
        UHOZYIYJYFOZVMYILMZYJLMZUUHOZYIUGMZYJUGMCUJMZOZUEZUVGUVDVMZUUTUVLUVKUVG
        LUVKUFZVMUVGUVJVKUUTUVKUVGUVDUVMUUTUVDYMUVMUUTYDBCDYIYJEYKFYRYSABWASZUU
        SGWBACWASZUUSHWBIAUUQUURWCZAUUQUURWEZWDUUTYLUVKLUUTYDBCEUUHUVIYKYIYJFYR
        UUJUVIPYSUVPUVQWFZWGWHWIVSUUTYLUVCUVKUVGUVDUVRUUTUVAUVEUVBUVFUUHUUQUVAU
        VEQZAUURYIYDLWJZWKUURUVBUVFQAUUQYJYDLWJWLWOWMWNAUUQVTZYIUUFMZLYIYIYKOZU
        FZMZUVEUUGMZUWBYIYIYFOZMUVAUUGMUWAUWEUWBLMZUWFUWAUWBUWCLUWAYDEUUFYKYIYR
        YSUUKAEWASZUUQUUOWBAUUQWPZWQTUWAUWBUWFUVHCVJMZMZNZQUWHUWFQUWAUWBUVEUVHN
        ZUUFMUWMUWAYIUWNUUFUUQYIUWNQAYIYBYCWRWSWTUWABCUVEUVHEUUFUUGUWKYBYCFAUVN
        UUQGWBZAUVOUUQHWBZYPYQUULUWKPUUKUUQUVEYBSAYIYBYCXAWSUUQUVHYCSAYIYBYCXEW
        SXFWHUWFUWLUWBUVEUUGURUVHUWKURXBVEWHUWAUWBUWGUWDUWAYDBCDYIYIEYKFYRYSUWO
        UWPIUWJUWJWDXCUWAUVAUVEUUGUUQUVSAUVTWSWTXDAUUQUURUAUIZYDSZXOZUBUIZYLSZU
        CUIZYJUWQYKOZSZVTZXOZUXBUWTYIYJNUWQUUEOOZLYIUWQYKOZUFZMZUXBLMZUWTLMZUVE
        UVFNZUWQLMZUUIOZOZUXGYIUWQYFOZMUXBYJUWQYFOZMZUWTUVDMZUVAUVBNZUWQYEMZUUI
        OZOUXFUXJUXGLMUXPUXFUXGUXHLUXFYDEUUEUWTUXBYKYIYJUWQYRYSUUMAUWSUWIUXEUUO
        XGAUUQUURUWRUXEXHZAUUQUURUWRUXEXIZAUUQUURUWRUXEXJZAUWSUXAUXDXKZAUWSUXAU
        XDXLZXMTUXFYDBCEUUIUWTUXBYKUUEYIYJUWQFYRYSUUMUYDUYEUYFUYGUYHUUNXPWHUXFU
        XGUXQUXIUXFYDBCDYIUWQEYKFYRYSAUWSUVNUXEGXGZAUWSUVOUXEHXGZIUYDUYFWDXCUXF
        UXSUXKUXTUXLUYCUXOUXFUYAUXMUYBUXNUUIUXFUVAUVEUVBUVFUXFYIYDLUYDTUXFYJYDL
        UYETXNUXFUWQYDLUYFTWOUXFUXSUXBLUXCUFZMUXKUXFUXBUXRUYKUXFYDBCDYJUWQEYKFY
        RYSUYIUYJIUYEUYFWDXCUXFUXBUXCLUYHTWHUXFUXTUWTYMMUXLUXFUWTUVDYMUXFYDBCDY
        IYJEYKFYRYSUYIUYJIUYDUYEWDXCUXFUWTYLLUYGTWHXQXDXRYEYFYHXSXTYA $.
    $}

    ${
      2ndfcl.p $e |- Q = ( C 2ndF D ) $.
      $( The second projection functor is a functor onto the right argument.
         (Contributed by Mario Carneiro, 11-Jan-2017.) $)
      2ndfcl $p |- ( ph -> Q e. ( T Func D ) ) $=
        ( vx vy c2nd cfv cop co eqid wceq cvv wcel fvresd vz vf vg cbs cxp cres
        cfunc cv chom cmpo xpcbas 2ndfval wfun fo2nd fofun ax-mp fvex resfunexg
        wfo xpex mp2an mpoex op2ndd syl opeq2d eqtr4d wbr cco xpccat wf f2ndres
        ccid a1i wfn ovex fnmpoi fneq1d mpbiri wa c1st ccat adantr simprl 2ndf2
        simprr xpchom reseq2d eqtrd feq1d fvres ad2antrl ad2antll feq23d mpbird
        oveq12d simpr catidcl 1st2nd2 adantl fveq2d xp1st xp2nd fveq1d 3ad2ant1
        3eqtr4d w3a simp21 simp22 simp23 simp3l simp3r catcocl xpcco2nd opeq12d
        xpcid oveq123d isfuncd df-br sylib eqeltrd ) ADLBUDMZCUDMZUEZUFZDLMZNZE
        CUGOZADYDJKYCYCLJUHZKUHZEUIMZOZUFZUJZNZYFAJKYCBCDEYJFBCEYAYBFYAPZYBPZUK
        ZYJPZGHIULZAYEYMYDADYNQYEYMQYSYDYMDLUMZYCRSYDRSRRLUSYTUNRRLUOUPZYAYBBUD
        UQCUDUQUTZLYCRURVAJKYCYCYLUUBUUBVBVCVDZVEVFAYDYEYGVGYFYGSAJKUAYCYBEEVHM
        ZEVLMZUBUCCYDYEYJCVLMZCUIMZCVHMZYQYPYRUUGPZUUEPZUUFPZUUDPZUUHPZABCEFGHV
        IZHYCYBYDVJAYAYBVKVMAYEYCYCUEZVNYMUUOVNJKYCYCYLYMYMPYTYKRSYLRSUUAYHYIYJ
        VOLYKRURVAVPAUUOYEYMUUCVQVRAYHYCSZYIYCSZVSZVSZYKYHYDMZYIYDMZUUGOZYHYIYE
        OZVJYHVTMZYIVTMBUIMZOZYHLMZYILMZUUGOZUEZUVIUVCVJZUUSUVKUVJUVILUVJUFZVJU
        VFUVIVKUUSUVJUVIUVCUVLUUSUVCYLUVLUUSYCBCDYHYIEYJFYQYRABWASZUURGWBACWASZ
        UURHWBIAUUPUUQWCZAUUPUUQWEZWDUUSYKUVJLUUSYCBCEUVEUUGYJYHYIFYQUVEPUUIYRU
        VOUVPWFZWGWHWIVRUUSYKUVBUVJUVIUVCUVQUUSUUTUVGUVAUVHUUGUUPUUTUVGQZAUUQYH
        YCLWJZWKUUQUVAUVHQAUUPYIYCLWJWLWOWMWNAUUPVSZYHUUEMZLYHYHYJOZUFZMZUVGUUF
        MZUWAYHYHYEOZMUUTUUFMUVTUWDUWALMZUWEUVTUWAUWBLUVTYCEUUEYJYHYQYRUUJAEWAS
        ZUUPUUNWBAUUPWPZWQTUVTUWAUVDBVLMZMZUWENZQUWGUWEQUVTUWAUVDUVGNZUUEMUWLUV
        TYHUWMUUEUUPYHUWMQAYHYAYBWRWSWTUVTBCUVDUVGEUUEUWJUUFYAYBFAUVMUUPGWBZAUV
        NUUPHWBZYOYPUWJPUUKUUJUUPUVDYASAYHYAYBXAWSUUPUVGYBSAYHYAYBXBWSXOWHUWKUW
        EUWAUVDUWJUQUVGUUFUQVCVDWHUVTUWAUWFUWCUVTYCBCDYHYHEYJFYQYRUWNUWOIUWIUWI
        WDXCUVTUUTUVGUUFUUPUVRAUVSWSWTXEAUUPUUQUAUHZYCSZXFZUBUHZYKSZUCUHZYIUWPY
        JOZSZVSZXFZUXAUWSYHYINUWPUUDOOZLYHUWPYJOZUFZMZUXALMZUWSLMZUVGUVHNZUWPLM
        ZUUHOZOZUXFYHUWPYEOZMUXAYIUWPYEOZMZUWSUVCMZUUTUVANZUWPYDMZUUHOZOUXEUXIU
        XFLMUXOUXEUXFUXGLUXEYCEUUDUWSUXAYJYHYIUWPYQYRUULAUWRUWHUXDUUNXDAUUPUUQU
        WQUXDXGZAUUPUUQUWQUXDXHZAUUPUUQUWQUXDXIZAUWRUWTUXCXJZAUWRUWTUXCXKZXLTUX
        EYCBCEUUHUWSUXAYJUUDYHYIUWPFYQYRUULUYCUYDUYEUYFUYGUUMXMWHUXEUXFUXPUXHUX
        EYCBCDYHUWPEYJFYQYRAUWRUVMUXDGXDZAUWRUVNUXDHXDZIUYCUYEWDXCUXEUXRUXJUXSU
        XKUYBUXNUXEUXTUXLUYAUXMUUHUXEUUTUVGUVAUVHUXEYHYCLUYCTUXEYIYCLUYDTXNUXEU
        WPYCLUYETWOUXEUXRUXALUXBUFZMUXJUXEUXAUXQUYJUXEYCBCDYIUWPEYJFYQYRUYHUYII
        UYDUYEWDXCUXEUXAUXBLUYGTWHUXEUXSUWSYLMUXKUXEUWSUVCYLUXEYCBCDYHYIEYJFYQY
        RUYHUYIIUYCUYDWDXCUXEUWSYKLUYFTWHXPXEXQYDYEYGXRXSXT $.
    $}
  $}

  ${
    $d b f g h x y B $.  $d x y C $.  $d b f g h x y F $.  $d b f g h x y ph $.
    $d x y D $.  $d b f g h x y G $.  $d h K $.  $d h x y X $.  $d h x y Y $.
    $d b f g h x y H $.
    prfval.k $e |- P = ( F pairF G ) $.
    prfval.b $e |- B = ( Base ` C ) $.
    prfval.h $e |- H = ( Hom ` C ) $.
    prfval.c $e |- ( ph -> F e. ( C Func D ) ) $.
    prfval.d $e |- ( ph -> G e. ( C Func E ) ) $.
    $( Value of the pairing functor.  (Contributed by Mario Carneiro,
       12-Jan-2017.) $)
    prfval $p |- ( ph -> P = <. ( x e. B |->
      <. ( ( 1st ` F ) ` x ) , ( ( 1st ` G ) ` x ) >. ) ,
       ( x e. B , y e. B |-> ( h e. ( x H y ) |->
    <. ( ( x ( 2nd ` F ) y ) ` h ) , ( ( x ( 2nd ` G ) y ) ` h ) >. ) ) >. ) $=
      ( co c1st cfv vf vg vb cprf cv cop cmpt c2nd cmpo cvv cdm csb wceq df-prf
      a1i wa wcel fvex dmex simprl fveq2d dmeqd cbs eqid cfunc wrel wbr relfunc
      1st2ndbr sylancr funcf1 adantr eqtrd simpr simplrl fveq1d simplrr opeq12d
      fdmd mpteq12dv eqidd mpoeq123dv ad2antrr oveqd chom ad4antr simplr funcf2
      3impa mpoeq3dva csbied2 elexd opex ovmpod eqtrid ) AGJKUDRBDBUEZJSTZTZWPK
      STZTZUFZUGZBCDDHWPCUEZLRZHUEZWPXCJUHTZRZTZXEWPXCKUHTZRZTZUFZUGZUIZUFZMAUA
      UBJKUJUJUCUAUEZSTZUKZBUCUEZWPXQTZWPUBUEZSTZTZUFZUGZBCXSXSHWPXCXPUHTZRZUKZ
      XEYGTZXEWPXCYAUHTZRZTZUFZUGZUIZUFZULZXOUDUJUDUAUBUJUJYQUIUMABCUAUBHUCUNUO
      AXPJUMZYAKUMZUPZUPZUCXRDYPXOUJXRUJUQUUAXQXPSURUSUOUUAXRWQUKZDUUAXQWQUUAXP
      JSAYRYSUTVAVBAUUBDUMYTADFVCTZWQADUUCEFWQXFNUUCVDAEFVERZVFJUUDUQWQXFUUDVGZ
      EFVHPJUUDVIVJZVKVSVLVMUUAXSDUMZUPZYEXBYOXNUUHBXSYDDXAUUAUUGVNZUUHXTWRYCWT
      UUHWPXQWQUUHXPJSAYRYSUUGVOZVAVPUUHWPYBWSUUHYAKSAYRYSUUGVQZVAVPVRVTUUHYOBC
      DDYNUIXNUUHBCXSXSYNDDYNUUIUUIUUHYNWAWBUUHBCDDYNXMUUHWPDUQZXCDUQZYNXMUMUUH
      UULUPZUUMUPZHYHYMXDXLUUOYHXGUKXDUUOYGXGUUOYFXFWPXCUUOXPJUHUUHYRUULUUMUUJW
      CVAWDZVBUUOXDWRXCWQTFWETZRXGUUODEFWQXFLUUQWPXCNOUUQVDAUUEYTUUGUULUUMUUFWF
      UUHUULUUMWGUUNUUMVNWHVSVMUUOYIXHYLXKUUOXEYGXGUUPVPUUOXEYKXJUUOYJXIWPXCUUO
      YAKUHUUHYSUULUUMUUKWCVAWDVPVRVTWIWJVMVRWKAJUUDPWLAKEIVERQWLXOUJUQAXBXNWMU
      OWNWO $.

    prf1.x $e |- ( ph -> X e. B ) $.
    $( Value of the pairing functor on objects.  (Contributed by Mario
       Carneiro, 12-Jan-2017.) $)
    prf1 $p |- ( ph -> ( ( 1st ` P ) ` X ) =
      <. ( ( 1st ` F ) ` X ) , ( ( 1st ` G ) ` X ) >. ) $=
      ( vx vy cfv cop vh cv c1st cvv cmpt c2nd cmpo wceq prfval cbs fvexi mptex
      co mpoex op1std syl wa simpr fveq2d opeq12d wcel opex a1i fvmptd ) AQJQUB
      ZGUCSZSZVEHUCSZSZTZJVFSZJVHSZTZBEUCSZUDAEQBVJUEZQRBBUAVERUBZIUMUAUBZVEVPG
      UFSUMSVQVEVPHUFSUMSTUEZUGZTUHVNVOUHAQRBCDEUAFGHIKLMNOUIVOVSEQBVJBCUJLUKZU
      LQRBBVRVTVTUNUOUPAVEJUHZUQZVGVKVIVLWBVEJVFAWAURZUSWBVEJVHWCUSUTPVMUDVAAVK
      VLVBVCVD $.

    prf2.y $e |- ( ph -> Y e. B ) $.
    $( Value of the pairing functor on morphisms.  (Contributed by Mario
       Carneiro, 12-Jan-2017.) $)
    prf2fval $p |- ( ph -> ( X ( 2nd ` P ) Y ) = ( h e. ( X H Y ) |->
    <. ( ( X ( 2nd ` F ) Y ) ` h ) , ( ( X ( 2nd ` G ) Y ) ` h ) >. ) ) $=
      ( cfv vx vy cv co c2nd cop cmpt cvv c1st cmpo wceq prfval cbs fvexi mptex
      mpoex op2ndd syl simprl simprr oveq12d fveq1d opeq12d mpteq12dv wcel ovex
      wa a1i ovmpod ) AUAUBKLBBFUAUCZUBUCZJUDZFUCZVJVKHUETZUDZTZVMVJVKIUETZUDZT
      ZUFZUGZFKLJUDZVMKLVNUDZTZVMKLVQUDZTZUFZUGZEUETZUHAEUABVJHUITTVJIUITTUFZUG
      ZUAUBBBWAUJZUFUKWIWLUKAUAUBBCDEFGHIJMNOPQULWKWLEUABWJBCUMNUNZUOUAUBBBWAWM
      WMUPUQURAVJKUKZVKLUKZVGVGZFVLVTWBWGWPVJKVKLJAWNWOUSZAWNWOUTZVAWPVPWDVSWFW
      PVMVOWCWPVJKVKLVNWQWRVAVBWPVMVRWEWPVJKVKLVQWQWRVAVBVCVDRSWHUHVEAFWBWGKLJV
      FUOVHVI $.

    prf2.k $e |- ( ph -> K e. ( X H Y ) ) $.
    $( Value of the pairing functor on morphisms.  (Contributed by Mario
       Carneiro, 12-Jan-2017.) $)
    prf2 $p |- ( ph -> ( ( X ( 2nd ` P ) Y ) ` K ) =
      <. ( ( X ( 2nd ` F ) Y ) ` K ) , ( ( X ( 2nd ` G ) Y ) ` K ) >. ) $=
      ( vh cv c2nd cfv co cop cvv prf2fval wceq wa fveq2d opeq12d wcel opex a1i
      simpr fvmptd ) AUAJUAUBZKLGUCUDUEZUDZURKLHUCUDUEZUDZUFJUSUDZJVAUDZUFZKLIU
      EKLEUCUDUEUGABCDEUAFGHIKLMNOPQRSUHAURJUIZUJZUTVCVBVDVGURJUSAVFUPZUKVGURJV
      AVHUKULTVEUGUMAVCVDUNUOUQ $.
  $}

  ${
    $d f g h x y z C $.  $d x y D $.  $d f g h x y z P $.  $d f g h x y z ph $.
    $d x E $.  $d h x y F $.  $d h x y G $.  $d f g h x y z T $.
    prfcl.p $e |- P = ( F pairF G ) $.
    prfcl.t $e |- T = ( D Xc. E ) $.
    prfcl.c $e |- ( ph -> F e. ( C Func D ) ) $.
    prfcl.d $e |- ( ph -> G e. ( C Func E ) ) $.
    $( The pairing of functors ` F : C --> D ` and ` G : C --> D ` is a functor
       ` <. F , G >. : C --> ( D X. E ) ` .  (Contributed by Mario Carneiro,
       12-Jan-2017.) $)
    prfcl $p |- ( ph -> P e. ( C Func T ) ) $=
      ( vx cfv cop co eqid wcel adantr ffvelcdmd vy vh vz vf vg c1st c2nd cfunc
      cbs cmpt chom cmpo prfval wceq fvex mptex mpoex op1std syl op2ndd opeq12d
      cv eqtr4d wbr cxp cco ccid xpcbas wa funcrcl simpld simprd xpccat relfunc
      ccat wrel 1st2ndbr sylancr funcf1 ffvelcdmda opelxpd fmpt3d fnmpoi fneq1d
      wfn mpbiri oveqd cvv ovmpt4g mp3an3 sylan9eq simprl simprr funcf2 oveq12d
      ovex prf1 adantrr adantrl xpchom2 eqtrd eleqtrrd simpr funcid prf2 fveq2d
      catidcl xpcid 3eqtr4d 3ad2ant1 simp21 simp22 simp23 simp3l simp3r catcocl
      w3a funcco oveq123d wf xpcco2 isfuncd df-br sylib eqeltrd ) ADDUFNZDUGNZO
      ZBEUHPZADMBUINZMVBZGUFNZNZYKHUFNZNZOZUJZMUAYJYJUBYKUAVBZBUKNZPZUBVBZYKYRG
      UGNZPZNZUUAYKYRHUGNZPZNZOZUJZULZOZYHAMUAYJBCDUBFGHYSIYJQZYSQZKLUMZAYFYQYG
      UUJADUUKUNZYFYQUNUUNYQUUJDMYJYPBUIUOZUPZMUAYJYJUUIUUPUUPUQZURUSZAUUOYGUUJ
      UNUUNYQUUJDUUQUURUTUSZVAVCAYFYGYIVDYHYIRAMUAUCYJCUINZFUINZVEZBBVFNZBVGNZU
      DUEEYFYGYSEVGNZEUKNZEVFNZUULCFEUVAUVBJUVAQZUVBQZVHUUMUVGQZUVEQZUVFQZUVDQZ
      UVHQZABVORZCVORZAGBCUHPZRZUVPUVQVIKBCGVJUSZVKZACFEJAUVPUVQUVTVLZAUVPFVORZ
      AHBFUHPZRZUVPUWCVILBFHVJUSVLZVMAMYJYPUVCYFUUSAYKYJRZVIZYMYOUVAUVBAYJUVAYK
      YLAYJUVABCYLUUBUULUVIAUVRVPUVSYLUUBUVRVDZBCVNKGUVRVQVRZVSZVTZAYJUVBYKYNAY
      JUVBBFYNUUEUULUVJAUWDVPZUWEYNUUEUWDVDZBFVNZLHUWDVQZVRZVSZVTZWAWBAYGYJYJVE
      ZWEUUJUWTWEMUAYJYJUUIUUJUUJQZUBYTUUHYKYRYSWPUPZWCAUWTYGUUJUUTWDWFAUWGYRYJ
      RZVIZVIZUBYTUUHYKYFNZYRYFNZUVGPZYKYRYGPZAUXDUXIYKYRUUJPZUUIAYGUUJYKYRUUTW
      GUWGUXCUUIWHRUXJUUIUNUXBMUAYJYJUUIUUJWHUXAWIWJWKUXEUUAYTRZVIZUUHYMYRYLNZC
      UKNZPZYOYRYNNZFUKNZPZVEZUXHUXLUUDUUGUXOUXRUXEYTUXOUUAUUCUXEYJBCYLUUBYSUXN
      YKYRUULUUMUXNQZAUWIUXDUWJSAUWGUXCWLZAUWGUXCWMZWNVTUXEYTUXRUUAUUFUXEYJBFYN
      UUEYSUXQYKYRUULUUMUXQQZAUWNUXDUWQSUYAUYBWNVTWAUXEUXHUXSUNUXKUXEUXHYPUXMUX
      POZUVGPUXSUXEUXFYPUXGUYDUVGUXEYJBCDFGHYSYKIUULUUMAUVSUXDKSZAUWEUXDLSZUYAW
      QUXEYJBCDFGHYSYRIUULUUMUYEUYFUYBWQWOUXECFUXMUXPEUXNUXQUVGYMYOUVAUVBJUVIUV
      JUXTUYCAUWGYMUVARUXCUWLWRAUWGYOUVBRUXCUWSWRAUXCUXMUVARUWGAYJUVAYRYLUWKVTW
      SAUXCUXPUVBRUWGAYJUVBYRYNUWRVTWSUVKWTXASXBWBUWHYKUVENZYKYKUUBPNZUYGYKYKUU
      EPNZOYMCVGNZNZYOFVGNZNZOZUYGYKYKYGPNUXFUVFNZUWHUYHUYKUYIUYMUWHYJBUVECYLUU
      BUYJYKUULUVLUYJQZAUWIUWGUWJSAUWGXCZXDUWHYJBUVEFYNUUEUYLYKUULUVLUYLQZAUWNU
      WGUWQSUYQXDVAUWHYJBCDFGHYSUYGYKYKIUULUUMAUVSUWGKSZAUWEUWGLSZUYQUYQUWHYJBU
      VEYSYKUULUUMUVLAUVPUWGUWASUYQXGXEUWHUYOYPUVFNUYNUWHUXFYPUVFUWHYJBCDFGHYSY
      KIUULUUMUYSUYTUYQWQXFUWHCFYMYOEUVFUYJUYLUVAUVBJAUVQUWGUWBSAUWCUWGUWFSUVIU
      VJUYPUYRUVMUWLUWSXHXAXIAUWGUXCUCVBZYJRZXQZUDVBZYTRZUEVBZYRVUAYSPZRZVIZXQZ
      VUFVUDYKYROVUAUVDPPZYKVUAUUBPNZVUKYKVUAUUEPNZOVUFYRVUAUUBPZNZVUDUUCNZYMUX
      MOVUAYLNZCVFNZPPZVUFYRVUAUUEPZNZVUDUUFNZYOUXPOVUAYNNZFVFNZPPZOZVUKYKVUAYG
      PNVUFYRVUAYGPNZVUDUXINZUXFUXGOZVUAYFNZUVHPZPZVUJVULVUSVUMVVEVUJYJBUVDCYLU
      UBYSVUDVUFVURYKYRVUAUULUUMUVNVURQZAVUCUWIVUIUWJXJZAUWGUXCVUBVUIXKZAUWGUXC
      VUBVUIXLZAUWGUXCVUBVUIXMZAVUCVUEVUHXNZAVUCVUEVUHXOZXRVUJYJBUVDFYNUUEYSVUD
      VUFVVDYKYRVUAUULUUMUVNVVDQZVUJUWMUWEUWNUWOAVUCUWEVUILXJZUWPVRZVVOVVPVVQVV
      RVVSXRVAVUJYJBCDFGHYSVUKYKVUAIUULUUMAVUCUVSVUIKXJZVWAVVOVVQVUJYJBUVDVUDVU
      FYSYKYRVUAUULUUMUVNAVUCUVPVUIUWAXJVVOVVPVVQVVRVVSXPXEVUJVVLVUOVVAOZVUPVVB
      OZYPUYDOZVUQVVCOZUVHPZPVVFVUJVVGVWDVVHVWEVVKVWHVUJVVIVWFVVJVWGUVHVUJUXFYP
      UXGUYDVUJYJBCDFGHYSYKIUULUUMVWCVWAVVOWQVUJYJBCDFGHYSYRIUULUUMVWCVWAVVPWQV
      AVUJYJBCDFGHYSVUAIUULUUMVWCVWAVVQWQWOVUJYJBCDFGHYSVUFYRVUAIUULUUMVWCVWAVV
      PVVQVVSXEVUJYJBCDFGHYSVUDYKYRIUULUUMVWCVWAVVOVVPVVRXEXSVUJCFUXMUXPVUQVVCV
      VDEVURVUPVVBUXNUXQVUOVVAYMYOUVHUVAUVBJUVIUVJUXTUYCVUJYJUVAYKYLAVUCYJUVAYL
      XTVUIUWKXJZVVOTVUJYJUVBYKYNAVUCYJUVBYNXTVUIUWRXJZVVOTVUJYJUVAYRYLVWIVVPTV
      UJYJUVBYRYNVWJVVPTVVMVVTUVOVUJYJUVAVUAYLVWIVVQTVUJYJUVBVUAYNVWJVVQTVUJYTU
      XOVUDUUCVUJYJBCYLUUBYSUXNYKYRUULUUMUXTVVNVVOVVPWNVVRTVUJYTUXRVUDUUFVUJYJB
      FYNUUEYSUXQYKYRUULUUMUYCVWBVVOVVPWNVVRTVUJVUGUXMVUQUXNPVUFVUNVUJYJBCYLUUB
      YSUXNYRVUAUULUUMUXTVVNVVPVVQWNVVSTVUJVUGUXPVVCUXQPVUFVUTVUJYJBFYNUUEYSUXQ
      YRVUAUULUUMUYCVWBVVPVVQWNVVSTYAXAXIYBYFYGYIYCYDYE $.
  $}

  ${
    $d f h x y C $.  $d f h u x y F $.  $d f h u x y G $.  $d f h x y ph $.
    $d f u x y D $.  $d f u x y E $.  $d f x y P $.
    prf1st.p $e |- P = ( F pairF G ) $.
    prf1st.c $e |- ( ph -> F e. ( C Func D ) ) $.
    prf1st.d $e |- ( ph -> G e. ( C Func E ) ) $.
    $( Cancellation of pairing with first projection.  (Contributed by Mario
       Carneiro, 12-Jan-2017.) $)
    prf1st $p |- ( ph -> ( ( D 1stF E ) o.func P ) = F ) $=
      ( vx vy vf co c1st cfv cop wcel eqid adantr vu vh c1stf ccom cv c2nd cmpo
      cbs ccofu cmpt wa cxp cxpc chom xpcbas ccat cfunc funcrcl syl simprd wrel
      wbr relfunc 1st2ndbr sylancr funcf1 ffvelcdmda opelxpd 1stf1 op1st eqtrdi
      fvex mpteq2dva wceq prfval mptex mpoex op1std 1stfcl feqmptd fveq2 fmptco
      3eqtr4d ad2antrr prfcl adantrr adantrl fveq1d simprl simprr funcf2 fvresd
      cres 1stf2 simpr prf2 fveq2d 3eqtrd wf fcompt syl2anc 3impb mpoeq3dva wfn
      funcfn2 fnov sylib eqtr4d opeq12d cofuval 1st2nd ) ACEUCNZOPZDOPZUDZKLBUH
      PZXPKUEZXNPZLUEZXNPZXLUFPZNZXQXSDUFPZNZUDZUGZQFOPZFUFPZQZXLDUINFAXOYGYFYH
      AKXPXQYGPZXQGOPZPZQZXMPZUJKXPYJUJXOYGAKXPYNYJAXQXPRZUKZYNYMOPYJYPCUHPZEUH
      PZULZCEXLYMCEUMNZYTUNPZYTSZCEYTYQYRUUBYQSZYRSZUOZUUASZACUPRZYOABUPRZUUGAF
      BCUQNZRZUUHUUGUKIBCFURUSUTZTAEUPRZYOAUUHUULAGBEUQNZRZUUHUULUKJBEGURUSUTZT
      XLSZYPYJYLYQYRAXPYQXQYGAXPYQBCYGYHXPSZUUCAUUIVAZUUJYGYHUUIVBZBCVCZIFUUIVD
      VEZVFZVGAXPYRXQYKAXPYRBEYKGUFPZUUQUUDAUUMVAUUNYKUVCUUMVBBEVCJGUUMVDVEVFVG
      VHZVIYJYLXQYGVLXQYKVLVJVKVMAKUAXPYSYMUAUEZXMPYNXNXMUVDADKXPYMUJZKLXPXPUBX
      QXSBUNPZNZUBUEZXQXSYHNZPUVIXQXSUVCNZPQUJZUGZQVNXNUVFVNAKLXPBCDUBEFGUVGHUU
      QUVGSZIJVOUVFUVMDKXPYMBUHVLZVPKLXPXPUVLUVOUVOVQVRUSAUAYSYQXMAYSYQYTCXMYAU
      UEUUCAYTCUQNZVAXLUVPRXMYAUVPVBZYTCVCACEXLYTUUBUUKUUOUUPVSZXLUVPVDVEZVFVTU
      VEYMXMWAWBAKXPYQYGUVBVTWCAYFKLXPXPUVJUGZYHAKLXPXPYEUVJAYOXSXPRZYEUVJVNAYO
      UWAUKZUKZMUVHMUEZYDPZYBPZUJZMUVHUWDUVJPZUJYEUVJUWCMUVHUWFUWHUWCUWDUVHRZUK
      ZUWFUWEOXRXTUUANZWMZPUWEOPZUWHUWJUWEYBUWLUWJYSCEXLXRXTYTUUAUUBUUEUUFAUUGU
      WBUWIUUKWDAUULUWBUWIUUOWDUUPUWCXRYSRZUWIAYOUWNUWAAXPYSXQXNAXPYSBYTXNYCUUQ
      UUEABYTUQNZVADUWORXNYCUWOVBZBYTVCABCDYTEFGHUUBIJWEZDUWOVDVEZVFZVGWFZTUWCX
      TYSRZUWIAUWAUXAYOAXPYSXSXNUWSVGWGZTWNWHUWJUWEUWKOUWCUVHUWKUWDYDUWCXPBYTXN
      YCUVGUUAXQXSUUQUVNUUFAUWPUWBUWRTAYOUWAWIZAYOUWAWJZWKZVGWLUWJUWMUWHUWDUVKP
      ZQZOPUWHUWJUWEUXGOUWJXPBCDEFGUVGUWDXQXSHUUQUVNAUUJUWBUWIIWDAUUNUWBUWIJWDU
      WCYOUWIUXCTUWCUWAUWIUXDTUWCUWIWOWPWQUWHUXFUWDUVJVLUWDUVKVLVJVKWRVMUWCUWKX
      RXMPXTXMPCUNPZNZYBWSUVHUWKYDWSYEUWGVNUWCYSYTCXMYAUUAUXHXRXTUUEUUFUXHSZAUV
      QUWBUVSTUWTUXBWKUXEMYBYDUVHUWKUXIWTXAUWCMUVHYJXSYGPUXHNUVJUWCXPBCYGYHUVGU
      XHXQXSUUQUVNUXJAUUSUWBUVATUXCUXDWKVTWCXBXCAYHXPXPULXDYHUVTVNAXPBCYGYHUUQU
      VAXEKLXPXPYHXFXGXHXIAKLXPBYTCDXLUUQUWQUVRXJAUURUUJFYIVNUUTIFUUIXKVEWC $.

    $( Cancellation of pairing with second projection.  (Contributed by Mario
       Carneiro, 12-Jan-2017.) $)
    prf2nd $p |- ( ph -> ( ( D 2ndF E ) o.func P ) = G ) $=
      ( vx vy vf co cfv c2nd cop wcel eqid adantr vu vh c2ndf c1st ccom cv cmpo
      cbs ccofu cmpt wa cxp cxpc chom xpcbas ccat cfunc funcrcl syl simprd wrel
      wbr relfunc 1st2ndbr sylancr funcf1 ffvelcdmda opelxpd 2ndf1 op2nd eqtrdi
      fvex mpteq2dva wceq prfval mptex mpoex op1std 2ndfcl feqmptd fveq2 fmptco
      3eqtr4d ad2antrr prfcl adantrr adantrl fveq1d simprl simprr funcf2 fvresd
      cres 2ndf2 simpr prf2 fveq2d 3eqtrd wf fcompt syl2anc 3impb mpoeq3dva wfn
      funcfn2 fnov sylib eqtr4d opeq12d cofuval 1st2nd ) ACEUCNZUDOZDUDOZUEZKLB
      UHOZXPKUFZXNOZLUFZXNOZXLPOZNZXQXSDPOZNZUEZUGZQGUDOZGPOZQZXLDUINGAXOYGYFYH
      AKXPXQFUDOZOZXQYGOZQZXMOZUJKXPYLUJXOYGAKXPYNYLAXQXPRZUKZYNYMPOYLYPCUHOZEU
      HOZULZCEXLYMCEUMNZYTUNOZYTSZCEYTYQYRUUBYQSZYRSZUOZUUASZACUPRZYOABUPRZUUGA
      FBCUQNZRZUUHUUGUKIBCFURUSUTZTAEUPRZYOAUUHUULAGBEUQNZRZUUHUULUKJBEGURUSUTZ
      TXLSZYPYKYLYQYRAXPYQXQYJAXPYQBCYJFPOZXPSZUUCAUUIVAUUJYJUUQUUIVBBCVCIFUUIV
      DVEVFVGAXPYRXQYGAXPYRBEYGYHUURUUDAUUMVAZUUNYGYHUUMVBZBEVCZJGUUMVDVEZVFZVG
      VHZVIYKYLXQYJVLXQYGVLVJVKVMAKUAXPYSYMUAUFZXMOYNXNXMUVDADKXPYMUJZKLXPXPUBX
      QXSBUNOZNZUBUFZXQXSUUQNZOUVIXQXSYHNZOQUJZUGZQVNXNUVFVNAKLXPBCDUBEFGUVGHUU
      RUVGSZIJVOUVFUVMDKXPYMBUHVLZVPKLXPXPUVLUVOUVOVQVRUSAUAYSYRXMAYSYRYTEXMYAU
      UEUUDAYTEUQNZVAXLUVPRXMYAUVPVBZYTEVCACEXLYTUUBUUKUUOUUPVSZXLUVPVDVEZVFVTU
      VEYMXMWAWBAKXPYRYGUVCVTWCAYFKLXPXPUVKUGZYHAKLXPXPYEUVKAYOXSXPRZYEUVKVNAYO
      UWAUKZUKZMUVHMUFZYDOZYBOZUJZMUVHUWDUVKOZUJYEUVKUWCMUVHUWFUWHUWCUWDUVHRZUK
      ZUWFUWEPXRXTUUANZWMZOUWEPOZUWHUWJUWEYBUWLUWJYSCEXLXRXTYTUUAUUBUUEUUFAUUGU
      WBUWIUUKWDAUULUWBUWIUUOWDUUPUWCXRYSRZUWIAYOUWNUWAAXPYSXQXNAXPYSBYTXNYCUUR
      UUEABYTUQNZVADUWORXNYCUWOVBZBYTVCABCDYTEFGHUUBIJWEZDUWOVDVEZVFZVGWFZTUWCX
      TYSRZUWIAUWAUXAYOAXPYSXSXNUWSVGWGZTWNWHUWJUWEUWKPUWCUVHUWKUWDYDUWCXPBYTXN
      YCUVGUUAXQXSUURUVNUUFAUWPUWBUWRTAYOUWAWIZAYOUWAWJZWKZVGWLUWJUWMUWDUVJOZUW
      HQZPOUWHUWJUWEUXGPUWJXPBCDEFGUVGUWDXQXSHUURUVNAUUJUWBUWIIWDAUUNUWBUWIJWDU
      WCYOUWIUXCTUWCUWAUWIUXDTUWCUWIWOWPWQUXFUWHUWDUVJVLUWDUVKVLVJVKWRVMUWCUWKX
      RXMOXTXMOEUNOZNZYBWSUVHUWKYDWSYEUWGVNUWCYSYTEXMYAUUAUXHXRXTUUEUUFUXHSZAUV
      QUWBUVSTUWTUXBWKUXEMYBYDUVHUWKUXIWTXAUWCMUVHYLXSYGOUXHNUVKUWCXPBEYGYHUVGU
      XHXQXSUURUVNUXJAUUTUWBUVBTUXCUXDWKVTWCXBXCAYHXPXPULXDYHUVTVNAXPBEYGYHUURU
      VBXEKLXPXPYHXFXGXHXIAKLXPBYTEDXLUURUWQUVRXJAUUSUUNGYIVNUVAJGUUMXKVEWC $.
  $}

  ${
    $d f x y C $.  $d f x y D $.  $d f x y E $.  $d f x y F $.  $d f x y ph $.
    1st2ndprf.t $e |- T = ( D Xc. E ) $.
    1st2ndprf.f $e |- ( ph -> F e. ( C Func T ) ) $.
    1st2ndprf.d $e |- ( ph -> D e. Cat ) $.
    1st2ndprf.e $e |- ( ph -> E e. Cat ) $.
    $( Break a functor into a product category into first and second
       projections.  (Contributed by Mario Carneiro, 12-Jan-2017.) $)
    1st2ndprf $p |- ( ph -> F =
      ( ( ( D 1stF E ) o.func F ) pairF ( ( D 2ndF E ) o.func F ) ) ) $=
      ( vx vy c1st cfv c2nd co eqid wcel wceq adantr vf cop cv c1stf ccofu cmpt
      cbs c2ndf chom cmpo cprf cxp xpcbas cfunc wrel wbr relfunc sylancr funcf1
      1st2ndbr feqmptd wa ffvelcdmda 1st2nd2 syl 1stfcl simpr cofu1 1stf1 eqtrd
      ccat 2ndfcl 2ndf1 opeq12d eqtr4d mpteq2dva wfn funcfn2 fnov simprl simprr
      sylib funcf2 relxpchom 1st2nd ad2antrr cofu2 adantrr adantrl 1stf2 fveq1d
      cres fvresd 3eqtrd 2ndf2 3impb mpoeq3dva cofucl prfval 3eqtr4d ) AFMNZFON
      ZUBZKBUGNZKUCZCEUDPZFUEPZMNNZXECEUHPZFUEPZMNNZUBZUFZKLXDXDUAXELUCZBUINZPZ
      UAUCZXEXNXGONPNZXQXEXNXJONPNZUBZUFZUJZUBFXGXJUKPZAXAXMXBYBAXAKXDXEXANZUFX
      MAKXDCUGNZEUGNZULZXAAXDYGBDXAXBXDQZCEDYEYFGYEQYFQUMZABDUNPZUOZFYJRZXAXBYJ
      UPZBDUQZHFYJUTURZUSZVAAKXDYDXLAXEXDRZVBZYDYDMNZYDONZUBZXLYRYDYGRZYDUUASAX
      DYGXEXAYPVCZYDYEYFVDVEYRXHYSXKYTYRXHYDXFMNNYSYRXDBDCFXFXEYHAYLYQHTZAXFDCU
      NPRZYQACEXFDGIJXFQZVFZTAYQVGZVHYRYGCEXFYDDDUINZGYIUUIQZACVKRZYQITZAEVKRZY
      QJTZUUFUUCVIVJYRXKYDXIMNNYTYRXDBDEFXIXEYHUUDAXIDEUNPRZYQACEXIDGIJXIQZVLZT
      UUHVHYRYGCEXIYDDUUIGYIUUJUULUUNUUPUUCVMVJVNVOVPVJAXBKLXDXDXEXNXBPZUJZYBAX
      BXDXDULVQXBUUSSAXDBDXAXBYHYOVRKLXDXDXBVSWBAKLXDXDUURYAAYQXNXDRZUURYASAYQU
      UTVBZVBZUURUAXPXQUURNZUFYAUVBUAXPYDXNXANZUUIPZUURUVBXDBDXAXBXOUUIXEXNYHXO
      QZUUJAYMUVAYOTAYQUUTVTZAYQUUTWAZWCZVAUVBUAXPUVCXTUVBXQXPRZVBZUVCUVCMNZUVC
      ONZUBZXTUVKUVEUOUVCUVERUVCUVNSCEDUUIYDUVDGUUJWDUVBXPUVEXQUURUVIVCZUVCUVEW
      EURUVKXRUVLXSUVMUVKXRUVCYDUVDXFONPZNUVCMUVEWLZNUVLUVKXDBDXQCFXFXOXEXNYHAY
      LUVAUVJHWFZAUUEUVAUVJUUGWFUVBYQUVJUVGTZUVBUUTUVJUVHTZUVFUVBUVJVGZWGUVKUVC
      UVPUVQUVBUVPUVQSUVJUVBYGCEXFYDUVDDUUIGYIUUJAUUKUVAITZAUUMUVAJTZUUFAYQUUBU
      UTUUCWHZAUUTUVDYGRYQAXDYGXNXAYPVCWIZWJTWKUVKUVCUVEMUVOWMWNUVKXSUVCYDUVDXI
      ONPZNUVCOUVEWLZNUVMUVKXDBDXQEFXIXOXEXNYHUVRAUUOUVAUVJUUQWFUVSUVTUVFUWAWGU
      VKUVCUWFUWGUVBUWFUWGSUVJUVBYGCEXIYDUVDDUUIGYIUUJUWBUWCUUPUWDUWEWOTWKUVKUV
      CUVEOUVOWMWNVNVOVPVJWPWQVJVNAYKYLFXCSYNHFYJWEURAKLXDBCYCUAEXGXJXOYCQYHUVF
      ABDCFXFHUUGWRABDEFXIHUUQWRWSWT $.
  $}

  ${
    $d f g u v x y ph $.  $d f g u v x y X $.  $d f g u v x y Y $.
    $d f g x y T $.
    catcxpccl.c $e |- C = ( CatCat ` U ) $.
    catcxpccl.b $e |- B = ( Base ` C ) $.
    catcxpccl.o $e |- T = ( X Xc. Y ) $.
    catcxpccl.u $e |- ( ph -> U e. WUni ) $.
    catcxpccl.1 $e |- ( ph -> _om e. U ) $.
    catcxpccl.x $e |- ( ph -> X e. B ) $.
    catcxpccl.y $e |- ( ph -> Y e. B ) $.
    $( The category of categories for a weak universe is closed under the
       product category operation.  (Contributed by Mario Carneiro,
       12-Jan-2017.)  (Proof shortened by AV, 14-Oct-2024.) $)
    catcxpccl $p |- ( ph -> T e. B ) $=
      ( cfv cxp eqid crn cuni wss vx vy vg vf vv vu ccat cin cnx cbs cop cco cv
      chom c2nd co c1st cmpo ctp eqidd wceq xpcbas xpchomfval a1i xpcval baseid
      wunndx wunstr catcbaselcl wunxp wunop homid cpw catchomcl wunrn wununi wf
      wunpw wcel wral ovssunirn xpss12 mp2an ovex xpex elpw mpbir fmpo eqeltrid
      rgen2w mpbi wunf ccoid cpm catcccocl wunpm cvv fvex rnex uniex pwex uniss
      rnss mp2b sstri opelxpi fvssunirn elpm2r mp4an wuntp eqeltrd cwun catcbas
      eleqtrd elin2d xpccat elind eleqtrrd ) ADEUGUHZBAEUGDADUIUJOZFUJOZGUJOZPZ
      UKZUIUNOZDUNOZUKZUIULOZUAUBYCYCPZYCUCUDUAUMZUOOZUBUMZYFUPZYJYFOZUCUMZUQOZ
      UDUMZUQOZYJUQOZUQOYKUQOUKZYLUQOZFULOZUPZUPZYOUOOZYQUOOZYSUOOYKUOOUKZYLUOO
      ZGULOZUPZUPZUKZURZURZUKZUSEAUAUBUEUFYCFGUUIDUUBUDUCFUNOZGUNOZYFUUNBBYAYBJ
      YAQZYBQZUUPQZUUQQZUUBQUUIQMNAYCUTYFUFUEYCYCUFUMZUQOZUEUMZUQOZUUPUPZUVBUOO
      ZUVDUOOZUUQUPZPZURZVAAUEUFYCFGDUUPUUQYFJFGDYAYBJUURUUSVBUUTUVAYFQVCZVDAUU
      NUTVEAYDYGUUOEKAXTYCEKAUIEUJXTVFKAEKLVGZVHAYAYBEKABCEFHIKMVIABCEGHIKNVIVJ
      ZVKAYEYFEKAUIEUNYEVLKUVMVHAYFUVKEUVLAYIUUPRZSZUUQRZSZPZVMZEUVKKAYCYCEKUVN
      UVNVJZAUVSEKAUVPUVREKAUVOEKAUUPEKABCEFHIKMVNVOVPAUVQEKAUUQEKABCEGHIKNVNVO
      VPVJVRYIUVTUVKVQZAUVJUVTVSZUEYCVTUFYCVTUWBUWCUFUEYCYCUWCUVJUVSTZUVFUVPTUV
      IUVRTUWDUUPUVCUVEWAUUQUVGUVHWAUVFUVPUVIUVRWBWCUVJUVSUVFUVIUVCUVEUUPWDUVGU
      VHUUQWDWEWFWGWJUFUEYCYCUVJUVTUVKUVKQWHWKVDWLWIZVKAYHUUNEKAUIEULYHWMKUVMVH
      AYIYCPZUUBRZSZRZSZVMZUUIRZSZRZSZVMZPZYFRZSZUWSPZWNUPZEUUNKAYIYCEKUWAUVNVJ
      AUWQUWTEKAUWKUWPEKAUWJEKAUWIEKAUWHEKAUWGEKAUUBEKABCEFHIKMWOVOVPVOVPVRAUWO
      EKAUWNEKAUWMEKAUWLEKAUUIEKABCEGHIKNWOVOVPVOVPVRVJAUWSUWSEKAUWREKAYFEKUWEV
      OVPZUXBVJWPUWFUXAUUNVQZAUUMUXAVSZUBYCVTUAYIVTUXCUXDUAUBYIYCUWQWQVSUWTWQVS
      YMYNPZUWQUUMVQZUXEUWTTZUXDUWKUWPUWJUWIUWHUWGUUBFULWRWSWTWSWTXAUWOUWNUWMUW
      LUUIGULWRWSWTWSWTXAWEUWSUWSUWRYFDUNWRWSWTZUXHWEUULUWQVSZUDYNVTUCYMVTUXFUX
      IUCUDYMYNUUDUWKVSZUUKUWPVSZUXIUXJUUDUWJTUUDUUCRZSZUWJUUCYPYRWAUUCUWHTUXLU
      WITUXMUWJTUUBYTUUAWAUUCUWHXCUXLUWIXBXDXEUUDUWJYPYRUUCWDWFWGUXKUUKUWOTUUKU
      UJRZSZUWOUUJUUEUUFWAUUJUWMTUXNUWNTUXOUWOTUUIUUGUUHWAUUJUWMXCUXNUWNXBXDXEU
      UKUWOUUEUUFUUJWDWFWGUUDUUKUWKUWPXFWCWJUCUDYMYNUULUWQUUMUUMQWHWKYMUWSTYNUW
      STUXGYFYKYLWAYFYJXGYMUWSYNUWSWBWCUWQUWTUXEUUMWQWQXHXIWJUAUBYIYCUUMUXAUUNU
      UNQWHWKVDWLVKXJXKAFGDJAEUGFAFBXSMABCEXLHIKXMZXNXOAEUGGAGBXSNUXPXNXOXPXQUX
      PXR $.
  $}

  ${
    $d f g u v x y A $.  $d f g u v x y B $.  $d f g u v x y ph $.
    $d f g u v x y C $.  $d f g u v x y D $.
    xpcpropd.1 $e |- ( ph -> ( Homf ` A ) = ( Homf ` B ) ) $.
    xpcpropd.2 $e |- ( ph -> ( comf ` A ) = ( comf ` B ) ) $.
    xpcpropd.3 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    xpcpropd.4 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    xpcpropd.a $e |- ( ph -> A e. V ) $.
    xpcpropd.b $e |- ( ph -> B e. V ) $.
    xpcpropd.c $e |- ( ph -> C e. V ) $.
    xpcpropd.d $e |- ( ph -> D e. V ) $.
    $( If two categories have the same set of objects, morphisms, and
       compositions, then they have the same product category.  (Contributed by
       Mario Carneiro, 17-Jan-2017.) $)
    xpcpropd $p |- ( ph -> ( A Xc. C ) = ( B Xc. D ) ) $=
      ( co cfv cop eqid wcel syl vx vy vg vf vv vu cxpc cnx cbs cxp chom cco cv
      c2nd c1st cmpo ctp eqidd wceq xpcbas xpchomfval a1i homfeqbas xpeq12d w3a
      xpcval chomf 3ad2ant1 xp1st 3ad2ant2 3ad2ant3 homfeqval mpoeq3dva ad4antr
      xp2nd eqtrid wa ccomf simp-4r simpllr simpr 1st2nd2 fveq2d eqtr4di xpchom
      df-ov eqtrd eleqtrd simplr comfeqval opeq12d 3impa eqtr4d ) ABDUGOZUHUIPB
      UIPZDUIPZUJZQUHUKPWNUKPZQUHULPUAUBWQWQUJZWQUCUDUAUMZUNPZUBUMZWROZWTWRPZUC
      UMZUOPZUDUMZUOPZWTUOPZUOPZXAUOPZQZXBUOPZBULPZOOZXEUNPZXGUNPZXIUNPZXAUNPZQ
      ZXBUNPZDULPZOOZQZUPZUPZQUQCEUGOZAUAUBUEUFWQBDYBWNXNUDUCBUKPZDUKPZWRYFFFWO
      WPWNRZWORZWPRZYHRZYIRZXNRZYBRZKMAWQURWRUFUEWQWQUFUMZUOPZUEUMZUOPZYHOZYQUN
      PZYSUNPZYIOZUJZUPZUSAUEUFWQBDWNYHYIWRYJBDWNWOWPYJYKYLUTZYMYNWRRZVAZVBAYFU
      RVFAUAUBUEUFWQCEEULPZYGCULPZUDUCCUKPZEUKPZWRYFFFCUIPZEUIPZYGRUUNRUUORUULR
      ZUUMRZUUKRZUUJRZLNAWOUUNWPUUOABCGVCADEIVCVDAWRUUFUFUEWQWQYRYTUULOZUUBUUCU
      UMOZUJZUPUUIAUFUEWQWQUUEUVBAYQWQSZYSWQSZVEZUUAUUTUUDUVAUVEWOBCYHUULYRYTYK
      YMUUPAUVCBVGPCVGPUSZUVDGVHUVCAYRWOSUVDYQWOWPVIVJUVDAYTWOSUVCYSWOWPVIVKVLU
      VEWPDEYIUUMUUBUUCYLYNUUQAUVCDVGPEVGPUSZUVDIVHUVCAUUBWPSUVDYQWOWPVOVJUVDAU
      UCWPSUVCYSWOWPVOVKVLVDVMVPAUAUBWSWQYEUCUDXCXDXFXHXLXMUUKOOZXPXQXTYAUUJOOZ
      QZUPZAWTWSSZXBWQSZYEUVKUSAUVLVQZUVMVQZUCUDXCXDYDUVJUVOXEXCSZXGXDSZYDUVJUS
      UVOUVPVQZUVQVQZXOUVHYCUVIUVSWOBCUUKXNXHXFYHXJXKXMYKYMYOUURAUVFUVLUVMUVPUV
      QGVNABVRPCVRPUSUVLUVMUVPUVQHVNUVSXIWQSZXJWOSUVSUVLUVTAUVLUVMUVPUVQVSZWTWQ
      WQVITZXIWOWPVITUVSXAWQSZXKWOSUVSUVLUWCUWAWTWQWQVOTZXAWOWPVITUVSUVMXMWOSUV
      NUVMUVPUVQVTZXBWOWPVITUVSXGXJXKYHOZXRXSYIOZUJZSZXHUWFSUVSXGXDUWHUVRUVQWAU
      VSXDXIXAWROZUWHUVSXDXIXAQZWRPUWJUVSWTUWKWRUVSUVLWTUWKUSUWAWTWQWQWBTWCXIXA
      WRWFWDUVSWQBDWNYHYIWRXIXAYJUUGYMYNUUHUWBUWDWEWGWHZXGUWFUWGVITUVSXEXKXMYHO
      ZXSYAYIOZUJZSZXFUWMSUVSXEXCUWOUVOUVPUVQWIUVSWQBDWNYHYIWRXAXBYJUUGYMYNUUHU
      WDUWEWEWHZXEUWMUWNVITWJUVSWPDEUUJYBXQXPYIXRXSYAYLYNYPUUSAUVGUVLUVMUVPUVQI
      VNADVRPEVRPUSUVLUVMUVPUVQJVNUVSUVTXRWPSUWBXIWOWPVOTUVSUWCXSWPSUWDXAWOWPVO
      TUVSUVMYAWPSUWEXBWOWPVOTUVSUWIXQUWGSUWLXGUWFUWGVOTUVSUWPXPUWNSUWQXEUWMUWN
      VOTWJWKWLVMWLVMVFWM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Functor evaluation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c evalF $.
  $c curryF $.
  $c uncurryF $.
  $c DiagFunc $.

  $( Extend class notation with the evaluation functor. $)
  cevlf $a class evalF $.

  $( Extend class notation with the currying of a functor. $)
  ccurf $a class curryF $.

  $( Extend class notation with the uncurrying of a functor. $)
  cuncf $a class uncurryF $.

  $( Extend class notation to include the diagonal functor. $)
  cdiag $a class DiagFunc $.

  ${
    $d a c d f g m n x y C $.  $d a c d f g m n x y D $.  $d c d g m n x y H $.
    $d a c d e f g m n x y z $.  $d a g m n x y F $.  $d a c d g m n x y N $.
    $d a g m n x y G $.  $d a c d f g m n x y ph $.  $d a c d g m n x y .x. $.
    $d a g A $.  $d c d x y B $.  $d a g m n x y X $.  $d a g m n x y Y $.
    $d a g K $.
    $( Define the evaluation functor, which is the extension of the evaluation
       map ` f , x |-> ( f `` x ) ` of functors, to a functor
       ` ( C --> D ) X. C --> D ` .  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)
    df-evlf $a |- evalF = ( c e. Cat , d e. Cat |->
      <. ( f e. ( c Func d ) , x e. ( Base ` c ) |-> ( ( 1st ` f ) ` x ) ) ,
         ( x e. ( ( c Func d ) X. ( Base ` c ) ) ,
           y e. ( ( c Func d ) X. ( Base ` c ) ) |->
           [_ ( 1st ` x ) / m ]_ [_ ( 1st ` y ) / n ]_
           ( a e. ( m ( c Nat d ) n ) ,
             g e. ( ( 2nd ` x ) ( Hom ` c ) ( 2nd ` y ) ) |->
       ( ( a ` ( 2nd ` y ) )
          ( <. ( ( 1st ` m ) ` ( 2nd ` x ) ) ,
               ( ( 1st ` m ) ` ( 2nd ` y ) ) >. ( comp ` d )
               ( ( 1st ` n ) ` ( 2nd ` y ) ) )
         ( ( ( 2nd ` x ) ( 2nd ` m ) ( 2nd ` y ) ) ` g ) ) ) ) >. ) $.

    $( Define the curry functor, which maps a functor ` F : C X. D --> E ` to
       ` curryF ( F ) : C --> ( D --> E ) ` .  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)
    df-curf $a |- curryF = ( e e. _V , f e. _V |-> [_ ( 1st ` e ) / c ]_
      [_ ( 2nd ` e ) / d ]_ <. ( x e. ( Base ` c ) |->
        <. ( y e. ( Base ` d ) |-> ( x ( 1st ` f ) y ) ) ,
           ( y e. ( Base ` d ) , z e. ( Base ` d ) |->
             ( g e. ( y ( Hom ` d ) z ) |-> ( ( ( Id ` c ) ` x )
               ( <. x , y >. ( 2nd ` f ) <. x , z >. ) g ) ) ) >. ) ,
        ( x e. ( Base ` c ) , y e. ( Base ` c ) |->
          ( g e. ( x ( Hom ` c ) y ) |-> ( z e. ( Base ` d ) |->
            ( g ( <. x , z >. ( 2nd ` f ) <. y , z >. )
              ( ( Id ` d ) ` z ) ) ) ) ) >. ) $.

    $( Define the uncurry functor, which can be defined equationally using
       ` evalF ` .  Strictly speaking, the third category argument is not
       needed, since the resulting functor is extensionally equal regardless,
       but it is used in the equational definition and is too much work to
       remove.  (Contributed by Mario Carneiro, 13-Jan-2017.) $)
    df-uncf $a |- uncurryF = ( c e. _V , f e. _V |->
      ( ( ( c ` 1 ) evalF ( c ` 2 ) ) o.func
        ( ( f o.func ( ( c ` 0 ) 1stF ( c ` 1 ) ) )
          pairF ( ( c ` 0 ) 2ndF ( c ` 1 ) ) ) ) ) $.

    $( Define the diagonal functor, which is the functor ` C --> ( D Func C ) `
       whose object part is ` x e. C |-> ( y e. D |-> x ) ` .  The value of the
       functor at an object ` x ` is the constant functor which maps all
       objects in ` D ` to ` x ` and all morphisms to ` 1 ( x ) ` .  The
       morphism part is a natural transformation between these functors, which
       takes ` f : x --> y ` to the natural transformation with every component
       equal to ` f ` .  (Contributed by Mario Carneiro, 6-Jan-2017.) $)
    df-diag $a |- DiagFunc = ( c e. Cat , d e. Cat |->
      ( <. c , d >. curryF ( c 1stF d ) ) ) $.

    evlfval.e $e |- E = ( C evalF D ) $.
    evlfval.c $e |- ( ph -> C e. Cat ) $.
    evlfval.d $e |- ( ph -> D e. Cat ) $.
    evlfval.b $e |- B = ( Base ` C ) $.
    evlfval.h $e |- H = ( Hom ` C ) $.
    evlfval.o $e |- .x. = ( comp ` D ) $.
    evlfval.n $e |- N = ( C Nat D ) $.
    $( Value of the evaluation functor.  (Contributed by Mario Carneiro,
       12-Jan-2017.) $)
    evlfval $p |- ( ph -> E =
      <. ( f e. ( C Func D ) , x e. B |-> ( ( 1st ` f ) ` x ) ) ,
         ( x e. ( ( C Func D ) X. B ) , y e. ( ( C Func D ) X. B ) |->
           [_ ( 1st ` x ) / m ]_ [_ ( 1st ` y ) / n ]_
           ( a e. ( m N n ) , g e. ( ( 2nd ` x ) H ( 2nd ` y ) ) |->
       ( ( a ` ( 2nd ` y ) )
          ( <. ( ( 1st ` m ) ` ( 2nd ` x ) ) ,
               ( ( 1st ` m ) ` ( 2nd ` y ) ) >. .x.
               ( ( 1st ` n ) ` ( 2nd ` y ) ) )
         ( ( ( 2nd ` x ) ( 2nd ` m ) ( 2nd ` y ) ) ` g ) ) ) ) >. ) $=
      ( vc vd cevlf cfunc c1st cfv cmpo cxp c2nd cop csb ccat cbs cnat chom cco
      co cv cvv wceq df-evlf wa simprl simprr oveq12d fveq2d eqtr4di mpoeq123dv
      a1i eqidd xpeq12d oveqd csbeq2dv opeq12d wcel opex ovmpod eqtrid ) ALEFUE
      USHBEFUFUSZDBUTZHUTUGUHUHZUIZBCWADUJZWEJWBUGUHZKCUTZUGUHZOIJUTZKUTZNUSZWB
      UKUHZWGUKUHZMUSZWMOUTUHZIUTWLWMWIUKUHUSUHZWLWIUGUHZUHWMWQUHULZWMWJUGUHUHZ
      GUSZUSZUIZUMZUMZUIZULZPAUCUDEFUNUNHBUCUTZUDUTZUFUSZXGUOUHZWCUIZBCXIXJUJZX
      LJWFKWHOIWIWJXGXHUPUSZUSZWLWMXGUQUHZUSZWOWPWRWSXHURUHZUSZUSZUIZUMZUMZUIZU
      LZXFUEVAUEUCUDUNUNYDUIVBABCHIJKOUCUDVCVKAXGEVBZXHFVBZVDVDZXKWDYCXEYGHBXIX
      JWCWADWCYGXGEXHFUFAYEYFVEZAYEYFVFZVGZYGXJEUOUHDYGXGEUOYHVHSVIZYGWCVLVJYGB
      CXLXLYBWEWEXDYGXIWAXJDYJYKVMZYLYGJWFYAXCYGKWHXTXBYGOIXNXPXSWKWNXAYGXMNWIW
      JYGXMEFUPUSNYGXGEXHFUPYHYIVGUBVIVNYGXOMWLWMYGXOEUQUHMYGXGEUQYHVHTVIVNYGXR
      WTWOWPYGXQGWRWSYGXQFURUHGYGXHFURYIVHUAVIVNVNVJVOVOVJVPQRXFVAVQAWDXEVRVKVS
      VT $.

    evlf2.f $e |- ( ph -> F e. ( C Func D ) ) $.
    evlf2.g $e |- ( ph -> G e. ( C Func D ) ) $.
    evlf2.x $e |- ( ph -> X e. B ) $.
    evlf2.y $e |- ( ph -> Y e. B ) $.
    evlf2.l $e |- L = ( <. F , X >. ( 2nd ` E ) <. G , Y >. ) $.
    $( Value of the evaluation functor at a morphism.  (Contributed by Mario
       Carneiro, 12-Jan-2017.) $)
    evlf2 $p |- ( ph -> L = ( a e. ( F N G ) , g e. ( X H Y ) |->
      ( ( a ` Y ) ( <. ( ( 1st ` F ) ` X ) , ( ( 1st ` F ) ` Y ) >. .x.
        ( ( 1st ` G ) ` Y ) ) ( ( X ( 2nd ` F ) Y ) ` g ) ) ) ) $=
      ( vx vy vm vn vf cop c2nd cfv co c1st cmpo cfunc cxp csb cvv wceq evlfval
      cv ovex cbs fvexi mpoex xpex op2ndd wa fvexd simprl fveq2d op1stg syl2anc
      wcel adantr eqtrd simplrr ad2antrr simplr simpr oveq12d ad3antrrr fveq12d
      syl op2ndg opeq12d oveq123d fveq1d mpoeq123dv csbied2 opelxpd a1i ovmpod
      eqtrid ) AKHMUMZINUMZGUNUOZUPOFHILUPZMNJUPZNOVEZUOZFVEZMNHUNUOZUPZUOZMHUQ
      UOZUOZNXJUOZUMZNIUQUOZUOZEUPZUPZURZUGAUHUIWSWTCDUSUPZBUTZXTUJUHVEZUQUOZUK
      UIVEZUQUOZOFUJVEZUKVEZLUPZYAUNUOZYCUNUOZJUPZYIXDUOZXFYHYIYEUNUOZUPZUOZYHY
      EUQUOZUOZYIYOUOZUMZYIYFUQUOZUOZEUPZUPZURZVAZVAZXRXAVBAGULUHXSBYAULVEUQUOU
      OZURZUHUIXTXTUUEURZUMVCXAUUHVCAUHUIBCDEULFUJUKGJLOPQRSTUAUBVDUUGUUHGULUHX
      SBUUFCDUSVFZBCVGSVHZVIUHUIXTXTUUEXSBUUIUUJVJZUUKVIVKWHAYAWSVCZYCWTVCZVLZV
      LZUJYBHUUDXRVBUUOYAUQVMUUOYBWSUQUOZHUUOYAWSUQAUULUUMVNZVOAUUPHVCZUUNAHXSV
      RZMBVRZUURUCUEHMXSBVPVQVSVTUUOYEHVCZVLZUKYDIUUCXRVBUVBYCUQVMUVBYDWTUQUOZI
      UVBYCWTUQAUULUUMUVAWAZVOAUVCIVCZUUNUVAAIXSVRZNBVRZUVEUDUFINXSBVPVQWBVTUVB
      YFIVCZVLZOFYGYJUUBXBXCXQUVIYEHYFILUUOUVAUVHWCZUVBUVHWDZWEUVIYHMYINJUVIYHW
      SUNUOZMUVIYAWSUNUUOUULUVAUVHUUQWBVOAUVLMVCZUUNUVAUVHAUUSUUTUVMUCUEHMXSBWI
      VQWFVTZUVIYIWTUNUOZNUVIYCWTUNUVBUUMUVHUVDVSVOAUVONVCZUUNUVAUVHAUVFUVGUVPU
      DUFINXSBWIVQWFVTZWEUVIYKXEYNXIUUAXPUVIYRXMYTXOEUVIYPXKYQXLUVIYHMYOXJUVIYE
      HUQUVJVOZUVNWGUVIYINYOXJUVRUVQWGWJUVIYINYSXNUVIYFIUQUVKVOUVQWGWEUVIYINXDU
      VQVOUVIXFYMXHUVIYHMYINYLXGUVIYEHUNUVJVOUVNUVQWKWLWKWMWNWNAHMXSBUCUEWOAINX
      SBUDUFWOXRVBVRAOFXBXCXQHILVFMNJVFVIWPWQWR $.

    evlf2val.a $e |- ( ph -> A e. ( F N G ) ) $.
    evlf2val.k $e |- ( ph -> K e. ( X H Y ) ) $.
    $( Value of the evaluation natural transformation at an object.
       (Contributed by Mario Carneiro, 12-Jan-2017.) $)
    evlf2val $p |- ( ph -> ( A L K ) =
      ( ( A ` Y ) ( <. ( ( 1st ` F ) ` X ) , ( ( 1st ` F ) ` Y ) >. .x.
        ( ( 1st ` G ) ` Y ) ) ( ( X ( 2nd ` F ) Y ) ` K ) ) ) $=
      ( va vg co cv cfv c2nd c1st cop evlf2 wceq wa simprl fveq1d simprr fveq2d
      cvv oveq12d ovexd ovmpod ) AUJUKBKHIMULNOJULOUJUMZUNZUKUMZNOHUOUNULZUNZNH
      UPUNZUNOVNUNUQOIUPUNUNFULZULOBUNZKVLUNZVOULLVEACDEFUKGHIJLMNOUJPQRSTUAUBU
      CUDUEUFUGURAVIBUSZVKKUSZUTUTZVJVPVMVQVOVTOVIBAVRVSVAVBVTVKKVLAVRVSVCVDVFU
      HUIAVPVQVOVGVH $.
  $}

  ${
    $d x y B $.  $d a f g m n x y C $.  $d f x F $.  $d a f g m n x y ph $.
    $d a f g m n x y D $.  $d f x X $.
    evlf1.e $e |- E = ( C evalF D ) $.
    evlf1.c $e |- ( ph -> C e. Cat ) $.
    evlf1.d $e |- ( ph -> D e. Cat ) $.
    evlf1.b $e |- B = ( Base ` C ) $.
    evlf1.f $e |- ( ph -> F e. ( C Func D ) ) $.
    evlf1.x $e |- ( ph -> X e. B ) $.
    $( Value of the evaluation functor at an object.  (Contributed by Mario
       Carneiro, 12-Jan-2017.) $)
    evlf1 $p |- ( ph -> ( F ( 1st ` E ) X ) = ( ( 1st ` F ) ` X ) ) $=
      ( vf vx vy co cv c1st cfv vm vn va vg cvv cmpo cxp cnat c2nd chom cop cco
      cfunc csb wceq eqid evlfval ovex cbs fvexi mpoex op1std syl simprl fveq2d
      xpex wa simprr fveq12d fvexd ovmpod ) ANOFGCDUMQZBORZNRZSTZTZGFSTZTESTZUE
      AENOVLBVPUFZOPVLBUGZVTUAVMSTUBPRZSTUCUDUARZUBRZCDUHQZQVMUITZWAUITZCUJTZQW
      FUCRTUDRWEWFWBUITQTWEWBSTZTWFWHTUKWFWCSTTDULTZQQUFUNUNZUFZUKUOVRVSUOAOPBC
      DWINUDUAUBEWGWDUCHIJKWGUPWIUPWDUPUQVSWKENOVLBVPCDUMURZBCUSKUTZVAOPVTVTWJV
      LBWLWMVFZWNVAVBVCAVNFUOZVMGUOZVGVGZVMGVOVQWQVNFSAWOWPVDVEAWOWPVHVILMAGVQV
      JVK $.
  $}

  ${
    $d a f g h m n u v x y z C $.  $d f g u v x y z E $.  $d f g u v x y z Q $.
    $d a f g h m n u v x y z D $.  $d a f g h m n u v x y z ph $.
    evlfcl.e $e |- E = ( C evalF D ) $.
    evlfcl.q $e |- Q = ( C FuncCat D ) $.
    evlfcl.c $e |- ( ph -> C e. Cat ) $.
    evlfcl.d $e |- ( ph -> D e. Cat ) $.
    ${
      evlfcl.n $e |- N = ( C Nat D ) $.
      evlfcl.f $e |- ( ph -> ( F e. ( C Func D ) /\ X e. ( Base ` C ) ) ) $.
      evlfcl.g $e |- ( ph -> ( G e. ( C Func D ) /\ Y e. ( Base ` C ) ) ) $.
      evlfcl.h $e |- ( ph -> ( H e. ( C Func D ) /\ Z e. ( Base ` C ) ) ) $.
      evlfcl.a $e |- ( ph ->
        ( A e. ( F N G ) /\ K e. ( X ( Hom ` C ) Y ) ) ) $.
      evlfcl.b $e |- ( ph ->
        ( B e. ( G N H ) /\ L e. ( Y ( Hom ` C ) Z ) ) ) $.
      $( Lemma for ~ evlfcl .  (Contributed by Mario Carneiro, 12-Jan-2017.) $)
      evlfcllem $p |- ( ph ->
      ( ( <. F , X >. ( 2nd ` E ) <. H , Z >. ) `
        ( <. B , L >. ( <. <. F , X >. , <. G , Y >. >.
          ( comp ` ( Q Xc. C ) ) <. H , Z >. ) <. A , K >. ) ) =
      ( ( ( <. G , Y >. ( 2nd ` E ) <. H , Z >. ) ` <. B , L >. )
        ( <. ( ( 1st ` E ) ` <. F , X >. ) , ( ( 1st ` E ) ` <. G , Y >. ) >.
          ( comp ` D ) ( ( 1st ` E ) ` <. H , Z >. ) )
        ( ( <. F , X >. ( 2nd ` E ) <. G , Y >. ) ` <. A , K >. ) ) ) $=
        ( cop cco cfv co c2nd c1st cxpc cbs chom eqid cfunc wcel simpld fuccocl
        simprd catcocl evlf2val fuccoval oveq1d wrel wbr relfunc sylancr funcco
        1st2ndbr oveq2d nat1st2nd funcf1 ffvelcdmd funcf2 natcl 3eqtr4d 3eqtr3d
        catass eqtrd 3eqtrd fucbas fuchom xpcco2 fveq2d eqtr4di eqtr3id opeq12d
        nati df-ov evlf1 oveq12d oveq123d ) ACBHIUGJFUHUIZUJUJZLKNOUGPDUHUIZUJU
        JZHNUGZJPUGZGUKUIZUJZUJZPCUIZLOPIUKUIZUJZUIZOIULUIZUIZPXHUIZUGPJULUIZUI
        ZEUHUIZUJUJZOBUIZKNOHUKUIZUJZUIZNHULUIZUIZOXSUIZUGZXIXMUJUJZXTXIUGZXLXM
        UJZUJZCLUGZBKUGZWSIOUGZUGWTFDUMUJZUHUIZUJUJZXBUIZYGYIWTXAUJZUIZYHWSYIXA
        UJZUIZWSGULUIZUIZYIYRUIZUGZWTYRUIZXMUJZUJAXCPWPUIZWRNPXPUJUIZXTPXSUIZUG
        XLXMUJZUJXDPBUIZUUFXJUGXLXMUJUJZUUEUUGUJZYFAWPDUNUIZDEXMGHJDUOUIZWRXBMN
        PQSTUUKUPZUULUPZXMUPZUAAHDEUQUJZURZNUUKURZUBUSZAJUUPURZPUUKURZUDUSZAUUQ
        UURUBVAZAUUTUVAUDVAZXBUPADEFBCWOHIJMRUAWOUPZABHIMUJURZKNOUULUJZURZUEUSZ
        ACIJMUJURZLOPUULUJZURZUFUSZUTAUUKDWQKLUULNOPUUMUUNWQUPZSUVCAIUUPURZOUUK
        URZUCVAZUVDAUVFUVHUEVAZAUVJUVLUFVAZVBVCAUUDUUIUUEUUGAUUKDEFBCWOXMHIJMPR
        UAUUMUUOUVEUVIUVMUVDVDVEAUUJUUILOPXPUJZUIZXRYBUUFXMUJUJZUUGUJZYFAUUEUWB
        UUIUUGAUUKDWQEXSXPUULKLXMNOPUUMUUNUVNUUOAUUPVFZUUQXSXPUUPVGDEVHZUUSHUUP
        VKVIZUVCUVQUVDUVRUVSVJVLAUUIUWAYAUUFUGZXLXMUJUJZXRYBXLXMUJZUJXNXOYAXIUG
        ZXLXMUJUJZXRUWIUJUWCYFAUWHUWKXRUWIAXDUUHUWAUWGXJXMUJUJZYAXJUGXLXMUJZUJX
        DXGXOUWJXJXMUJUJZUWMUJUWHUWKAUWLUWNXDUWMABUUKDELXMXSXPUULXHXEMOPUAABDEH
        IMUAUVIVMZUUMUUNUUOUVQUVDUVSWJVLAEUNUIZEXMUWAUUHEUOUIZXDXLYAUUFXJUWPUPZ
        UWQUPZUUOTAUUKUWPOXSAUUKUWPDEXSXPUUMUWRUWFVNZUVQVOZAUUKUWPPXSUWTUVDVOZA
        UUKUWPPXHAUUKUWPDEXHXEUUMUWRAUWDUVOXHXEUUPVGUWEAUVOUVPUCUSZIUUPVKVIZVNZ
        UVDVOZAUVKYAUUFUWQUJLUVTAUUKDEXSXPUULUWQOPUUMUUNUWSUWFUVQUVDVPUVSVOZABU
        UKDEXSXPUWQXHXEMPUAUWOUUMUWSUVDVQZAUUKUWPPXKAUUKUWPDEXKJUKUIZUUMUWRAUWD
        UUTXKUXIUUPVGUWEUVBJUUPVKVIVNUVDVOZACUUKDEXHXEUWQXKUXIMPUAACDEIJMUAUVMV
        MUUMUWSUVDVQZVTAUWPEXMXOXGUWQXDXLYAXIXJUWRUWSUUOTUXAAUUKUWPOXHUXEUVQVOZ
        UXFABUUKDEXSXPUWQXHXEMOUAUWOUUMUWSUVQVQZAUVKXIXJUWQUJLXFAUUKDEXHXEUULUW
        QOPUUMUUNUWSUXDUVQUVDVPUVSVOZUXJUXKVTVRVEAUWPEXMXRUWAUWQUUIXLXTYAUUFUWR
        UWSUUOTAUUKUWPNXSUWTUVCVOZUXAUXBAUVGXTYAUWQUJKXQAUUKDEXSXPUULUWQNOUUMUU
        NUWSUWFUVCUVQVPUVRVOZUXGUXJAUWPEXMUUHXDUWQUUFXJXLUWRUWSUUOTUXBUXFUXJUXH
        UXKVBVTAUWPEXMXRXOUWQXNXLXTYAXIUWRUWSUUOTUXOUXAUXLUXPUXMUXJAUWPEXMXGXDU
        WQXIXJXLUWRUWSUUOTUXLUXFUXJUXNUXKVBVTVSWAWBAYMWPWRUGZXBUIXCAYLUXQXBAFDI
        OJPWQYJWOBKMUULCLHNYKUUPUUKYJUPDEFRWCUUMDEFMRUAWDUUNUUSUVCUXCUVQUVEUVNY
        KUPUVBUVDUVIUVRUVMUVSWEWFWPWRXBWKWGAYOXNYQYCUUCYEAUUAYDUUBXLXMAYSXTYTXI
        AYSHNYRUJXTHNYRWKAUUKDEGHNQSTUUMUUSUVCWLWHAYTIOYRUJXIIOYRWKAUUKDEGIOQST
        UUMUXCUVQWLWHWIAUUBJPYRUJXLJPYRWKAUUKDEGJPQSTUUMUVBUVDWLWHWMAYOCLYNUJXN
        CLYNWKACUUKDEXMGIJUULLYNMOPQSTUUMUUNUUOUAUXCUVBUVQUVDYNUPUVMUVSVCWHAYQB
        KYPUJYCBKYPWKABUUKDEXMGHIUULKYPMNOQSTUUMUUNUUOUAUUSUXCUVCUVQYPUPUVIUVRV
        CWHWNVR $.
    $}

    $( The evaluation functor is a bifunctor (a two-argument functor) with the
       first parameter taking values in the set of functors ` C --> D ` , and
       the second parameter in ` D ` .  (Contributed by Mario Carneiro,
       12-Jan-2017.) $)
    evlfcl $p |- ( ph -> E e. ( ( Q Xc. C ) Func D ) ) $=
      ( vf vx cfv cop co wcel wceq cv eqid wral wa vy vm vn va vg vz vu vv c1st
      vh c2nd cxpc cfunc cvv cxp cbs cmpo cnat chom cco evlfval ovex fvex mpoex
      csb xpex opelvv eqeltrdi 1st2nd2 syl wbr ccid fucbas xpcbas fuccat xpccat
      wf wrel relfunc simpr 1st2ndbr sylancr funcf1 ffvelcdmda ralrimiva op1std
      fmpo sylib feq1d mpbird wfn csbex fnmpoi op2ndd fneq1d mpbiri ccat adantr
      ad2antrr simplrl simplrr ffvelcdmd simprl simprr funcf2 nat1st2nd catcocl
      natcl evlf2 fuchom xpchom2 evlf1 oveq12d feq23d oveq2 fveq2 df-ov eqtr4di
      oveq2d feq123d ralxp oveq1 oveq1d 2ralbidv bitrid sylibr r19.21bi catidcl
      ralrimivva fveq2d 3eqtr4d fveq12d 3ad2ant1 eqeltrrd opelxp xpchom eleqtrd
      w3a opeq12d oveq123d anasss xpcid evlf2val catlid ccom fucid fveq1d fvco3
      syl2anc eqtrd funcid 3eqtrd id eqeq12d simp21 simp22 simp23 simp3l simp3r
      evlfcllem isfuncd df-br eqeltrd ) AEEUILZEUKLZMZDBULNZCUMNZAEUNUNUOZOEUVF
      PAEJKBCUMNZBUPLZKQZJQZUILZLZUQZKUAUVJUVKUOZUVQUBUVLUILZUCUAQZUILZUDUEUBQZ
      UCQZBCURNZNZUVLUKLZUVSUKLZBUSLZNZUWFUDQZLUEQZUWEUWFUWAUKLNLUWEUWAUILZLUWF
      UWKLMUWFUWBUILLCUTLZNNZUQZVEZVEZUQZMZUVIAKUAUVKBCUWLJUEUBUCEUWGUWCUDFHIUV
      KRZUWGRZUWLRZUWCRZVAZUVPUWQJKUVJUVKUVOBCUMVBZBUPVCZVDZKUAUVQUVQUWPUVJUVKU
      XDUXEVFZUXGVDZVGVHEUNUNVIVJAUVDUVEUVHVKUVFUVHOAKUAUFUVQCUPLZUVGUVGUTLZUVG
      VLLZJUECUVDUVEUVGUSLZCVLLZCUSLZUWLDBUVGUVJUVKUVGRZBCDGVMZUWSVNZUXIRZUXLRZ
      UXNRZUXKRZUXMRZUXJRUXAADBUVGUXOABCDGHIVOZHVPIAUVQUXIUVDVQUVQUXIUVPVQZAUVO
      UXIOZKUVKSZJUVJSUYDAUYFJUVJAUVMUVJOZTZUYEKUVKUYHUVKUXIUVLUVNUYHUVKUXIBCUV
      NUVMUKLZUWSUXRUYHUVJVRZUYGUVNUYIUVJVKZBCVSZAUYGVTUVMUVJWAZWBWCWDWEWEJKUVJ
      UVKUVOUXIUVPUVPRWGWHAUVQUXIUVDUVPAEUWRPZUVDUVPPUXCUVPUWQEUXFUXHWFVJWIWJAU
      VEUVQUVQUOZWKUWQUYOWKKUAUVQUVQUWPUWQUWQRUBUVRUWOUCUVTUWNUDUEUWDUWHUWMUWAU
      WBUWCVBUWEUWFUWGVBVDWLWLWMAUYOUVEUWQAUYNUVEUWQPUXCUVPUWQEUXFUXHWNVJWOWPAU
      VLUVQOZUVSUVQOZUVLUVSUXLNZUVLUVDLZUVSUVDLZUXNNZUVLUVSUVENZVQZAUYPTVUCUAUV
      QAVUCUAUVQSZKUVQAUVMUGQZMZUWJUHQZMZUXLNZUVMVUEUVDNZUWJVUGUVDNZUXNNZVUFVUH
      UVENZVQZUHUVKSUEUVJSZUGUVKSJUVJSVUDKUVQSAVUOJUGUVJUVKAUYGVUEUVKOZTZTZVUNU
      EUHUVJUVKVURUWJUVJOZVUGUVKOZTZTZVUNUVMUWJUWCNZVUEVUGUWGNZUOZVUEUVNLZVUGUW
      JUILZLZUXNNZVUMVQZVVBVVJVVEVVIUDUJVVCVVDVUGUWILZUJQZVUEVUGUYINZLZVVFVUGUV
      NLZMVVHUWLNNZUQZVQZVVBVVPVVIOZUJVVDSUDVVCSVVRVVBVVSUDUJVVCVVDVVBUWIVVCOZV
      VLVVDOZTZTZUXICUWLVVNVVKUXNVVFVVOVVHUXRUXTUXAVVBCWQOZVWBAVWDVUQVVAIWSZWRV
      WCUVKUXIVUEUVNVVBUVKUXIUVNVQZVWBVVBUVKUXIBCUVNUYIUWSUXRVVBUYJUYGUYKUYLAUY
      GVUPVVAWTZUYMWBZWCWRZVVBVUPVWBAUYGVUPVVAXAZWRXBVWCUVKUXIVUGUVNVWIVURVUSVU
      TVWBXAZXBVWCUVKUXIVUGVVGVVBUVKUXIVVGVQVWBVVBUVKUXIBCVVGUWJUKLZUWSUXRVVBUY
      JVUSVVGVWLUVJVKUYLVURVUSVUTXCZUWJUVJWAWBWCWRVWKXBVWCVVDVVFVVOUXNNZVVLVVMV
      VBVVDVWNVVMVQVWBVVBUVKBCUVNUYIUWGUXNVUEVUGUWSUWTUXTVWHVWJVURVUSVUTXDZXEWR
      VVBVVTVWAXDXBVWCUWIUVKBCUVNUYIUXNVVGVWLUWCVUGUXBVWCUWIBCUVMUWJUWCUXBVVBVV
      TVWAXCXFUWSUXTVWKXHXGYIUDUJVVCVVDVVPVVIVVQVVQRWGWHVVBVVEVVIVUMVVQVVBUVKBC
      UWLUJEUVMUWJUWGVUMUWCVUEVUGUDFABWQOZVUQVVAHWSZVWEUWSUWTUXAUXBVWGVWMVWJVWO
      VUMRXIWIWJVVBVUIVULVVEVVIVUMVVBDBUWJVUGUVGUWCUWGUXLUVMVUEUVJUVKUXOUXPUWSB
      CDUWCGUXBXJZUWTVWGVWJVWMVWOUXSXKVVBVUJVVFVUKVVHUXNVVBUVKBCEUVMVUEFVWQVWEU
      WSVWGVWJXLVVBUVKBCEUWJVUGFVWQVWEUWSVWMVWOXLXMXNWJYIYIVUDVUOKJUGUVJUVKVUDU
      VLVUHUXLNZUYSVUKUXNNZUVLVUHUVENZVQZUHUVKSUEUVJSUVLVUFPZVUOVUCVXBUAUEUHUVJ
      UVKUVSVUHPZUYRVWSVUAVWTVUBVXAUVSVUHUVLUVEXOUVSVUHUVLUXLXOVXDUYTVUKUYSUXNV
      XDUYTVUHUVDLVUKUVSVUHUVDXPUWJVUGUVDXQXRXSXTYAVXCVXBVUNUEUHUVJUVKVXCVWSVUI
      VWTVULVXAVUMUVLVUFVUHUVEYBUVLVUFVUHUXLYBVXCUYSVUJVUKUXNVXCUYSVUFUVDLVUJUV
      LVUFUVDXPUVMVUEUVDXQXRZYCXTYDYEYAYFYGYGUUAAUVLUXKLZUVLUVLUVENZLZUYSUXMLZP
      ZKUVQAVUFUXKLZVUFVUFUVENZLZVUJUXMLZPZUGUVKSJUVJSVXJKUVQSAVXOJUGUVJUVKVURV
      XMUVMDVLLZLZVUEBVLLZLZVXLNZVUEVXQLZVXSVUEVUEUYINLZVVFVVFMVVFUWLNZNZVXNVUR
      VXMVXQVXSMZVXLLVXTVURVXKVYEVXLVURDBUVMVUEUVGUXKVXPVXRUVJUVKUXOADWQOVUQUYC
      WRZAVWPVUQHWRZUXPUWSVXPRZVXRRZUYAAUYGVUPXCZAUYGVUPXDZUUBYJVXQVXSVXLXQXRVU
      RVXQUVKBCUWLEUVMUVMUWGVXSVXLUWCVUEVUEFVYGAVWDVUQIWRZUWSUWTUXAUXBVYJVYJVYK
      VYKVXLRVURUVJDVXPUWCUVMUXPVWRVYHVYFVYJYHVURUVKBVXRUWGVUEUWSUWTVYIVYGVYKYH
      UUCVURVVFUXMLZVYMVYCNVYMVYDVXNVURUXICUWLUXMVYMUXNVVFVVFUXRUXTUYBVYLVURUVK
      UXIVUEUVNVURUVKUXIBCUVNUYIUWSUXRVURUYJUYGUYKUYLVYJUYMWBZWCZVYKXBZUXAVYPVU
      RUXICUXMUXNVVFUXRUXTUYBVYLVYPYHUUDVURVYAVYMVYBVYMVYCVURVYAVUEUXMUVNUUEZLZ
      VYMVURVUEVXQVYQVURBCDUXMUVMVXPGVYHUYBVYJUUFUUGVURVWFVUPVYRVYMPVYOVYKUVKUX
      IVUEUXMUVNUUHUUIUUJVURUVKBVXRCUVNUYIUXMVUEUWSVYIUYBVYNVYKUUKXMVURVUJVVFUX
      MVURUVKBCEUVMVUEFVYGVYLUWSVYJVYKXLYJYKUULYIVXJVXOKJUGUVJUVKVXCVXHVXMVXIVX
      NVXCVXFVXKVXGVXLVXCUVLVUFUVLVUFUVEVXCUUMZVYSXMUVLVUFUXKXPYLVXCUYSVUJUXMVX
      EYJUUNYAYFYGAUYPUYQUFQZUVQOZYRZUVMUYROZUWJUVSVYTUXLNZOZTZYRZVVGVWLMZUVNUY
      IMZUVRUWEMZUVTUWFMZMZVYTUILZVYTUKLZMZUXJNZNZWUJWUOUVENZLWUHWUKWUOUVENZLZW
      UIWUJWUKUVENZLZWUJUVDLZWUKUVDLZMZWUOUVDLZUWLNZNUWJUVMUVLUVSMZVYTUXJNZNZUV
      LVYTUVENZLUWJUVSVYTUVENZLZUVMVUBLZUYSUYTMZVYTUVDLZUWLNZNWUGUVNVVGBCDEUVRU
      VTWUMUYIVWLUWCUWEUWFWUNFGAWUBVWPWUFHYMAWUBVWDWUFIYMUXBWUGWUJUVQOUVRUVJOUW
      EUVKOTWUGUVLWUJUVQWUGUYPUVLWUJPAUYPUYQWUAWUFUUOZUVLUVJUVKVIVJZWVRYNUVRUWE
      UVJUVKYOWHWUGWUKUVQOUVTUVJOUWFUVKOTWUGUVSWUKUVQWUGUYQUVSWUKPAUYPUYQWUAWUF
      UUPZUVSUVJUVKVIVJZWVTYNUVTUWFUVJUVKYOWHWUGWUOUVQOWUMUVJOWUNUVKOTWUGVYTWUO
      UVQWUGWUAVYTWUOPAUYPUYQWUAWUFUUQZVYTUVJUVKVIVJZWWBYNWUMWUNUVJUVKYOWHWUGWU
      IUVRUVTUWCNZUWHUOZOUVNWWDOUYIUWHOTWUGUVMWUIWWEWUGUVMWWEOUVMWUIPWUGUVMUYRW
      WEAWUBWUCWUEUURWUGUVQDBUVGUWCUWGUXLUVLUVSUXOUXQVWRUWTUXSWVRWVTYPYQZUVMWWD
      UWHVIVJZWWFYNUVNUYIWWDUWHYOWHWUGWUHUVTWUMUWCNZUWFWUNUWGNZUOZOVVGWWHOVWLWW
      IOTWUGUWJWUHWWJWUGUWJWWJOUWJWUHPWUGUWJWUDWWJAWUBWUCWUEUUSWUGUVQDBUVGUWCUW
      GUXLUVSVYTUXOUXQVWRUWTUXSWVTWWBYPYQZUWJWWHWWIVIVJZWWKYNVVGVWLWWHWWIYOWHUU
      TWUGWVJWUQWVKWURWUGUVLWUJVYTWUOUVEWVSWWCXMWUGUWJWUHUVMWUIWVIWUPWUGWVHWULV
      YTWUOUXJWUGUVLWUJUVSWUKWVSWWAYSWWCXMWWLWWGYTYLWUGWVMWUTWVNWVBWVQWVGWUGWVO
      WVEWVPWVFUWLWUGUYSWVCUYTWVDWUGUVLWUJUVDWVSYJWUGUVSWUKUVDWWAYJYSWUGVYTWUOU
      VDWWCYJXMWUGUWJWUHWVLWUSWUGUVSWUKVYTWUOUVEWWAWWCXMWWLYLWUGUVMWUIVUBWVAWUG
      UVLWUJUVSWUKUVEWVSWWAXMWWGYLYTYKUVAUVDUVEUVHUVBWHUVC $.
  $}

  ${
    $d c d e f g x y z .1. $.  $d c d e f x y A $.  $d c d e f g h w x y z B $.
    $d c d e f g x y z C $.  $d c d e f g h w x y z D $.  $d c d e f g y z H $.
    $d c d e f I $.  $d c d e f g h w x y z ph $.  $d g y z Y $.  $d g y z Z $.
    $d g h w y z E $.  $d c d e f g x J $.  $d g h w y z K $.  $d g x y z X $.
    $d c d e f g x y z F $.
    curfval.g $e |- G = ( <. C , D >. curryF F ) $.
    curfval.a $e |- A = ( Base ` C ) $.
    curfval.c $e |- ( ph -> C e. Cat ) $.
    curfval.d $e |- ( ph -> D e. Cat ) $.
    curfval.f $e |- ( ph -> F e. ( ( C Xc. D ) Func E ) ) $.
    curfval.b $e |- B = ( Base ` D ) $.
    ${
      curfval.j $e |- J = ( Hom ` D ) $.
      curfval.1 $e |- .1. = ( Id ` C ) $.
      ${
        curfval.h $e |- H = ( Hom ` C ) $.
        curfval.i $e |- I = ( Id ` D ) $.
        $( Value of the curry functor.  (Contributed by Mario Carneiro,
           12-Jan-2017.) $)
        curfval $p |- ( ph -> G = <. ( x e. A |->
     <. ( y e. B |-> ( x ( 1st ` F ) y ) ) ,
        ( y e. B , z e. B |-> ( g e. ( y J z ) |->
          ( ( .1. ` x ) ( <. x , y >. ( 2nd ` F ) <. x , z >. ) g ) ) ) >. ) ,
        ( x e. A , y e. A |-> ( g e. ( x H y ) |-> ( z e. B |->
          ( g ( <. x , z >. ( 2nd ` F ) <. y , z >. ) ( I ` z ) ) ) ) ) >. ) $=
          ( ve vf vc vd cop ccurf c1st cfv cmpt c2nd cmpo cvv cbs chom ccid csb
          co cv wceq df-curf a1i wa fvexd simprl fveq2d ccat wcel op1stg adantr
          syl2anc eqtrd op2ndg ad2antrr simplr eqtr4di simpr simprr oveqd eqidd
          mpteq12dv fveq1d oveq123d mpoeq123dv opeq12d csbied2 opex cfunc elexd
          cxpc ovmpod eqtrid ) AMGHUKZLULVCBECFBVDZCVDZLUMUNZVCZUOZCDFFJWTDVDZP
          VCZWSIUNZJVDZWSWTUKZWSXDUKZLUPUNZVCZVCZUOZUQZUKZUOZBCEEJWSWTNVCZDFXGX
          DOUNZXIWTXDUKZXJVCZVCZUOZUOZUQZUKZQAUGUHWRLURURUIUGVDZUMUNZUJYFUPUNZB
          UIVDZUSUNZCUJVDZUSUNZWSWTUHVDZUMUNZVCZUOZCDYLYLJWTXDYKUTUNZVCZWSYIVAU
          NZUNZXGXHXIYMUPUNZVCZVCZUOZUQZUKZUOZBCYJYJJWSWTYIUTUNZVCZDYLXGXDYKVAU
          NZUNZXIXSUUAVCZVCZUOZUOZUQZUKZVBZVBZYEULURULUGUHURURUUSUQVEABCDUGUHJU
          IUJVFVGAYFWRVEZYMLVEZVHZVHZUIYGGUURYEURUVCYFUMVIUVCYGWRUMUNZGUVCYFWRU
          MAUUTUVAVJZVKAUVDGVEZUVBAGVLVMZHVLVMZUVFSTGHVLVLVNVPVOVQUVCYIGVEZVHZU
          JYHHUUQYEURUVJYFUPVIUVJYHWRUPUNZHUVJYFWRUPUVCUUTUVIUVEVOVKAUVKHVEZUVB
          UVIAUVGUVHUVLSTGHVLVLVRVPVSVQUVJYKHVEZVHZUUGXPUUPYDUVNBYJUUFEXOUVNYJG
          USUNEUVNYIGUSUVCUVIUVMVTZVKRWAZUVNYPXCUUEXNUVNCYLYOFXBUVNYLHUSUNFUVNY
          KHUSUVJUVMWBZVKUBWAZUVNYNXAWSWTUVNYMLUMUVCUVAUVIUVMAUUTUVAWCVSZVKWDWF
          UVNCDYLYLUUDFFXMUVRUVRUVNJYRUUCXEXLUVNYQPWTXDUVNYQHUTUNPUVNYKHUTUVQVK
          UCWAWDUVNYTXFXGXGUUBXKUVNUUAXJXHXIUVNYMLUPUVSVKZWDUVNWSYSIUVNYSGVAUNI
          UVNYIGVAUVOVKUDWAWGUVNXGWEZWHWFWIWJWFUVNBCYJYJUUOEEYCUVPUVPUVNJUUIUUN
          XQYBUVNUUHNWSWTUVNUUHGUTUNNUVNYIGUTUVOVKUEWAWDUVNDYLUUMFYAUVRUVNXGXGU
          UKXRUULXTUVNUUAXJXIXSUVTWDUWAUVNXDUUJOUVNUUJHVAUNOUVNYKHVAUVQVKUFWAWG
          WHWFWFWIWJWKWKWRURVMAGHWLVGALGHWOVCKWMVCUAWNYEURVMAXPYDWLVGWPWQ $.
      $}

      $( Value of the object part of the curry functor.  (Contributed by Mario
         Carneiro, 12-Jan-2017.) $)
      curf1fval $p |- ( ph -> ( 1st ` G ) = ( x e. A |->
   <. ( y e. B |-> ( x ( 1st ` F ) y ) ) ,
      ( y e. B , z e. B |-> ( g e. ( y J z ) |->
        ( ( .1. ` x ) ( <. x , y >. ( 2nd ` F ) <. x , z >. ) g ) ) ) >. ) ) $=
        ( cv c1st cfv co cmpt c2nd cmpo chom ccid wceq eqid curfval fvexi mptex
        cop cbs mpoex op1std syl ) AMBECFBUCZCUCZLUDUEUFUGCDFFJVCDUCZNUFVBIUEJU
        CZVBVCUQVBVDUQZLUHUEZUFUFUGUIUQZUGZBCEEJVBVCGUJUEZUFDFVEVDHUKUEZUEVFVCV
        DUQVGUFUFUGUGZUIZUQULMUDUEVIULABCDEFGHIJKLMVJVKNOPQRSTUAUBVJUMVKUMUNVIV
        MMBEVHEGURPUOZUPBCEEVLVNVNUSUTVA $.
    $}

    curf1.x $e |- ( ph -> X e. A ) $.
    curf1.k $e |- K = ( ( 1st ` G ) ` X ) $.
    ${
      curf1.j $e |- J = ( Hom ` D ) $.
      curf1.1 $e |- .1. = ( Id ` C ) $.
      $( Value of the object part of the curry functor.  (Contributed by Mario
         Carneiro, 12-Jan-2017.) $)
      curf1 $p |- ( ph -> K = <. ( y e. B |-> ( X ( 1st ` F ) y ) ) ,
       ( y e. B , z e. B |-> ( g e. ( y J z ) |->
         ( ( .1. ` X ) ( <. X , y >. ( 2nd ` F ) <. X , z >. ) g ) ) ) >. ) $=
        ( vx c1st cfv cv co cmpt cop c2nd cmpo curf1fval wceq wa simpr mpteq2dv
        cvv oveq1d wcel w3a simp1r opeq1d oveq12d fveq2d eqidd oveq123d opeq12d
        mpoeq3dva opex a1i fvmptd eqtrid ) ANOLUGUHZUHBEOBUIZKUGUHZUJZUKZBCEEIV
        QCUIZMUJZOHUHZIUIZOVQULZOWAULZKUMUHZUJZUJZUKZUNZULZUCAUFOBEUFUIZVQVRUJZ
        UKZBCEEIWBWMHUHZWDWMVQULZWMWAULZWGUJZUJZUKZUNZULWLDVPUTAUFBCDEFGHIJKLMP
        QRSTUAUDUEUOAWMOUPZUQZWOVTXBWKXDBEWNVSXDWMOVQVRAXCURVAUSXDBCEEXAWJXDVQE
        VBZWAEVBZVCZIWBWTWIXGWPWCWDWDWSWHXGWQWEWRWFWGXGWMOVQAXCXEXFVDZVEXGWMOWA
        XHVEVFXGWMOHXHVGXGWDVHVIUSVKVJUBWLUTVBAVTWKVLVMVNVO $.
    $}

    ${
      curf11.y $e |- ( ph -> Y e. B ) $.
      $( Value of the double evaluated curry functor.  (Contributed by Mario
         Carneiro, 12-Jan-2017.) $)
      curf11 $p |- ( ph -> ( ( 1st ` K ) ` Y ) = ( X ( 1st ` F ) Y ) ) $=
        ( vy vz vg cv c1st cfv cvv cmpt chom ccid cop c2nd cmpo wceq eqid curf1
        co cbs fvexi mptex mpoex op1std syl wa simpr oveq2d ovexd fvmptd ) AUAK
        JUAUDZGUEUFZUQZJKVJUQCIUEUFZUGAIUACVKUHZUAUBCCUCVIUBUDZEUIUFZUQJDUJUFZU
        FUCUDJVIUKJVNUKGULUFUQUQUHZUMZUKUNVLVMUNAUAUBBCDEVPUCFGHVOIJLMNOPQRSVOU
        OVPUOUPVMVRIUACVKCEURQUSZUTUAUBCCVQVSVSVAVBVCAVIKUNZVDVIKJVJAVTVEVFTAJK
        VJVGVH $.

      curf12.j $e |- J = ( Hom ` D ) $.
      curf12.1 $e |- .1. = ( Id ` C ) $.
      curf12.y $e |- ( ph -> Z e. B ) $.
      curf12.g $e |- ( ph -> H e. ( Y J Z ) ) $.
      $( The partially evaluated curry functor at a morphism.  (Contributed by
         Mario Carneiro, 12-Jan-2017.) $)
      curf12 $p |- ( ph -> ( ( Y ( 2nd ` K ) Z ) ` H ) =
        ( ( .1. ` X ) ( <. X , Y >. ( 2nd ` F ) <. X , Z >. ) H ) ) $=
        ( vy vz vg c2nd cfv cv co cop cmpt cmpo wceq c1st curf1 cbs fvexi mptex
        mpoex op2ndd syl cvv wcel adantr wa ovex simprl simprr oveq12d eleqtrrd
        a1i ovexd simplrl opeq2d simplrr eqidd simpr oveq123d fvmptdv2 ovmpodv
        mpd ) ALULUMZUIUJCCUKUIUNZUJUNZKUOZMFUMZUKUNZMWIUPZMWJUPZHULUMZUOZUOZUQ
        ZURZUSZJNOWHUOZUMWLJMNUPZMOUPZWPUOZUOZUSZALUICMWIHUTUMUOZUQZWTUPUSXAAUI
        UJBCDEFUKGHIKLMPQRSTUAUBUCUEUFVAXIWTLUICXHCEVBUAVCZVDUIUJCCWSXJXJVEVFVG
        AXGUIUJNOCCWSWHVHUDAOCVIWINUSZUGVJWSVHVIAXKWJOUSZVKZVKZUKWKWRWIWJKVLVDV
        QXNUKJWRXFWKXBVHXNJNOKUOZWKAJXOVIXMUHVJXNWINWJOKAXKXLVMAXKXLVNVOVPXNWMJ
        USZVKZWLWMWQVRXQWLWLWMJWQXEXQWNXCWOXDWPXQWINMAXKXLXPVSVTXQWJOMAXKXLXPWA
        VTVOXQWLWBXNXPWCWDWEWFWG $.
    $}

    $( The partially evaluated curry functor is a functor.  (Contributed by
       Mario Carneiro, 13-Jan-2017.) $)
    curf1cl $p |- ( ph -> K e. ( D Func E ) ) $=
      ( cfv co vy vz vg vw vh c1st c2nd cfunc cv cmpt chom ccid cmpo eqid curf1
      cop wceq cbs fvexi mptex mpoex op1std syl op2ndd opeq12d eqtr4d wcel cxpc
      wbr cco ccat wa funcrcl simprd cxp wf xpcbas wrel relfunc 1st2ndbr funcf1
      sylancr adantr simpr fovcdmd fmpt3d wfn ovex fnmpoi fneq1d mpbiri ovmpt4g
      cvv mp3an3 sylan9eq ad2antrr simplrl opelxpd simplrr funcf2 xpchom curf11
      oveqd df-ov eqtr2di oveq12d feq23d catidcl op1stg syl2anc eleqtrrd op2ndg
      mpbid xpcid fveq2d eqtr4di opelxpi sylan funcid eqtr3d curf12 3eqtr4d w3a
      eqtrdi 3ad2ant1 simp21 simp22 simp23 simp3l simp3r xpcco2 xpchom2 catcocl
      catlid opeq1d eqtrd funcco oveq123d isfuncd df-br sylib eqeltrd ) AIIUFSZ
      IUGSZUPZEFUHTZAIUACJUAUIZGUFSZTZUJZUAUBCCUCUUGUBUIZEUKSZTZJDULSZSZUCUIZJU
      UGUPZJUUKUPZGUGSZTZTZUJZUMZUPZUUEAUAUBBCDEUUNUCFGHUULIJKLMNOPQRUULUNZUUNU
      NZUOZAUUCUUJUUDUVCAIUVDUQZUUCUUJUQUVGUUJUVCIUACUUICEURPUSZUTZUAUBCCUVBUVI
      UVIVAZVBVCZAUVHUUDUVCUQUVGUUJUVCIUVJUVKVDVCZVEVFAUUCUUDUUFVIUUEUUFVGAUAUB
      UDCFURSZEEVJSZEULSZUCUEFUUCUUDUULFULSZFUKSZFVJSZPUVNUNZUVEUVRUNZUVPUNZUVQ
      UNZUVOUNZUVSUNZNADEVHTZVKVGZFVKVGZAGUWFFUHTZVGZUWGUWHVLOUWFFGVMVCVNAUACUU
      IUVNUUCUVLAUUGCVGZVLZJUUGUVNBCUUHABCVOZUVNUUHVPUWKAUWMUVNUWFFUUHUUSDEUWFB
      CUWFUNZLPVQZUVTAUWIVRUWJUUHUUSUWIVIZUWFFVSOGUWIVTWBZWAWCAJBVGZUWKQWCZAUWK
      WDZWEWFAUUDCCVOZWGUVCUXAWGUAUBCCUVBUVCUVCUNZUCUUMUVAUUGUUKUULWHUTZWIAUXAU
      UDUVCUVMWJWKAUWKUUKCVGZVLZVLZUCUUMUVAUUGUUCSZUUKUUCSZUVRTZUUGUUKUUDTZAUXE
      UXJUUGUUKUVCTZUVBAUUDUVCUUGUUKUVMXCUWKUXDUVBWMVGUXKUVBUQUXCUAUBCCUVBUVCWM
      UXBWLWNWOUXFUUPUUMVGZVLZUUOUUPUXIUUQUFSZUURUFSZDUKSZTZUUQUGSZUURUGSZUULTZ
      UUTUXMUUQUURUWFUKSZTZUUQUUHSZUURUUHSZUVRTZUUTVPUXQUXTVOZUXIUUTVPUXMUWMUWF
      FUUHUUSUYAUVRUUQUURUWOUYAUNZUWAAUWPUXEUXLUWQWPUXMJUUGBCAUWRUXEUXLQWPZAUWK
      UXDUXLWQZWRZUXMJUUKBCUYHAUWKUXDUXLWSZWRZWTUXMUYBUYEUYFUXIUUTUXMUWMDEUWFUX
      PUULUYAUUQUURUWNUWOUXPUNZUVEUYGUYJUYLXAUXMUYCUXGUYDUXHUVRUXMUXGUUIUYCUXMB
      CDEFGHIJUUGKLADVKVGZUXEUXLMWPZAEVKVGZUXEUXLNWPZAUWJUXEUXLOWPZPUYHRUYIXBJU
      UGUUHXDZXEUXMUXHJUUKUUHTZUYDUXMBCDEFGHIJUUKKLUYOUYQUYRPUYHRUYKXBJUUKUUHXD
      ZXEXFXGXMUXMUUOJJUXPTZUXQUXMBDUUNUXPJLUYMUVFUYOUYHXHUXMUXNJUXOJUXPUXMUWRU
      WKUXNJUQUYHUYIJUUGBCXIXJUXMUWRUXDUXOJUQUYHUYKJUUKBCXIXJXFXKUXMUUPUUMUXTUX
      FUXLWDUXMUXRUUGUXSUUKUULUXMUWRUWKUXRUUGUQUYHUYIJUUGBCXLXJUXMUWRUXDUXSUUKU
      QUYHUYKJUUKBCXLXJXFXKWEWFUWLUUOUUGUVPSZUUQUUQUUSTZTZUYCUVQSZVUCUUGUUGUUDT
      SUXGUVQSUWLUUQUWFULSZSZVUDSZVUEVUFUWLVUIUUOVUCUPZVUDSVUEUWLVUHVUJVUDUWLDE
      JUUGUWFVUGUUNUVPBCUWNAUYNUWKMWCZAUYPUWKNWCZLPUVFUWBVUGUNZUWSUWTXNXOUUOVUC
      VUDXDXPUWLUWMUWFVUGFUUHUUSUVQUUQUWOVUMUWCAUWPUWKUWQWCAUWRUWKUUQUWMVGQJUUG
      BCXQXRXSXTUWLBCDEUUNFGHVUCUULIJUUGUUGKLVUKVULAUWJUWKOWCZPUWSRUWTUVEUVFUWT
      UWLCEUVPUULUUGPUVEUWBVULUWTXHYAUWLUXGUYCUVQUWLUXGUUIUYCUWLBCDEFGHIJUUGKLV
      UKVULVUNPUWSRUWTXBUYSYDXOYBAUWKUXDUDUIZCVGZYCZUXLUEUIZUUKVUOUULTZVGZVLZYC
      ZUUOVURUUPUUGUUKUPVUOUVOTTZUUQJVUOUPZUUSTZTZUUOVURUPZUURVVDUUSTZSZUUOUUPU
      PZUUTSZUYCUYDUPZVVDUUHSZUVSTZTZVVCUUGVUOUUDTSVURUUKVUOUUDTSZUUPUXJSZUXGUX
      HUPZVUOUUCSZUVSTZTVVBVVGVVJUUQUURUPVVDUWFVJSZTTZVVESZVVFVVOVVBVWCUUOVVCUP
      ZVVESVVFVVBVWBVWDVVEVVBVWBUUOUUOJJUPJDVJSZTTZVVCUPVWDVVBDEJUUKJVUOUVOUWFV
      WEUUOUUPUXPUULUUOVURJUUGVWABCUWNLPUYMUVEAVUQUWRVVAQYEZAUWKUXDVUPVVAYFZVWG
      AUWKUXDVUPVVAYGZVWEUNZUWDVWAUNZVWGAUWKUXDVUPVVAYHZVVBBDUUNUXPJLUYMUVFAVUQ
      UYNVVAMYEZVWGXHZAVUQUXLVUTYIZVWNAVUQUXLVUTYJZYKVVBVWFUUOVVCVVBBDVWEUUNUUO
      UXPJJLUYMUVFVWMVWGVWJVWGVWNYNYOYPXOUUOVVCVVEXDXPVVBUWMUWFVWAFUUHUUSUYAVVJ
      VVGUVSUUQUURVVDUWOUYGVWKUWEAVUQUWPVVAUWQYEVVBJUUGBCVWGVWHWRVVBJUUKBCVWGVW
      IWRVVBJVUOBCVWGVWLWRVVBVVJVUBUUMVOUYBVVBUUOUUPVUBUUMVWNVWOWRVVBDEJUUKUWFU
      XPUULUYAJUUGBCUWNLPUYMUVEVWGVWHVWGVWIUYGYLXKVVBVVGVUBVUSVOUURVVDUYATVVBUU
      OVURVUBVUSVWNVWPWRVVBDEJVUOUWFUXPUULUYAJUUKBCUWNLPUYMUVEVWGVWIVWGVWLUYGYL
      XKYQXTVVBBCDEUUNFGHVVCUULIJUUGVUOKLVWMAVUQUYPVVANYEZAVUQUWJVVAOYEZPVWGRVW
      HUVEUVFVWLVVBCEUVOUUPVURUULUUGUUKVUOPUVEUWDVWQVWHVWIVWLVWOVWPYMYAVVBVVPVV
      IVVQVVKVVTVVNVVBVVRVVLVVSVVMUVSVVBUXGUYCUXHUYDVVBUXGUUIUYCVVBBCDEFGHIJUUG
      KLVWMVWQVWRPVWGRVWHXBUYSYDVVBUXHUYTUYDVVBBCDEFGHIJUUKKLVWMVWQVWRPVWGRVWIX
      BVUAYDVEVVBVVSJVUOUUHTVVMVVBBCDEFGHIJVUOKLVWMVWQVWRPVWGRVWLXBJVUOUUHXDYDX
      FVVBVVPUUOVURVVHTVVIVVBBCDEUUNFGHVURUULIJUUKVUOKLVWMVWQVWRPVWGRVWIUVEUVFV
      WLVWPYAUUOVURVVHXDYDVVBVVQUVAVVKVVBBCDEUUNFGHUUPUULIJUUGUUKKLVWMVWQVWRPVW
      GRVWHUVEUVFVWIVWOYAUUOUUPUUTXDYDYRYBYSUUCUUDUUFYTUUAUUB $.
  $}

  ${
    $d x y A $.  $d g x y z C $.  $d g x y z F $.  $d g y z H $.  $d f w z L $.
    $d f g w y z E $.  $d f w x y z G $.  $d g x y z I $.  $d f g w x y z ph $.
    $d f g w x y z B $.  $d f g w x y z D $.  $d f g w x y z X $.  $d z Z $.
    $d g x y z K $.  $d f g w x y z Y $.
    curf2.g $e |- G = ( <. C , D >. curryF F ) $.
    curf2.a $e |- A = ( Base ` C ) $.
    curf2.c $e |- ( ph -> C e. Cat ) $.
    curf2.d $e |- ( ph -> D e. Cat ) $.
    curf2.f $e |- ( ph -> F e. ( ( C Xc. D ) Func E ) ) $.
    curf2.b $e |- B = ( Base ` D ) $.
    curf2.h $e |- H = ( Hom ` C ) $.
    curf2.i $e |- I = ( Id ` D ) $.
    curf2.x $e |- ( ph -> X e. A ) $.
    curf2.y $e |- ( ph -> Y e. A ) $.
    curf2.k $e |- ( ph -> K e. ( X H Y ) ) $.
    curf2.l $e |- L = ( ( X ( 2nd ` G ) Y ) ` K ) $.
    $( Value of the curry functor at a morphism.  (Contributed by Mario
       Carneiro, 13-Jan-2017.) $)
    curf2 $p |- ( ph -> L = ( z e. B |->
      ( K ( <. X , z >. ( 2nd ` F ) <. Y , z >. ) ( I ` z ) ) ) ) $=
      ( vx vy vg c2nd cfv co cop cmpt cmpo wceq c1st chom ccid eqid curfval cbs
      cv fvexi mptex mpoex op2ndd syl cvv wcel adantr wa ovex a1i simprl simprr
      oveq12d eleqtrrd simplrl simplrr simpr oveq123d mpteq2dv fvmptdv2 ovmpodv
      opeq1d eqidd mpd eqtrid ) AMLNOIUKULZUMZULZBDLBVDZKULZNWNUNZOWNUNZHUKULZU
      MZUMZUOZUGAWKUHUICCUJUHVDZUIVDZJUMZBDUJVDZWOXBWNUNZXCWNUNZWRUMZUMZUOZUOZU
      PZUQZWMXAUQZAIUHCUIDXBXCHURULUMUOUIBDDUJXCWNFUSULZUMXBEUTULZULXEXBXCUNXFW
      RUMUMUOUPUNZUOZXLUNUQXMAUHUIBCDEFXPUJGHIJKXOPQRSTUAXOVAXPVAUBUCVBXRXLIUHC
      XQCEVCQVEZVFUHUICCXKXSXSVGVHVIAXNUHUINOCCXKWKVJUDAOCVKXBNUQZUEVLXKVJVKAXT
      XCOUQZVMZVMZUJXDXJXBXCJVNVFVOYCUJLXJXAXDWLVJYCLNOJUMZXDALYDVKYBUFVLYCXBNX
      COJAXTYAVPAXTYAVQVRVSXJVJVKYCXELUQZVMZBDXIDFVCUAVEVFVOYFBDXIWTYFXELWOWOXH
      WSYFXFWPXGWQWRYFXBNWNAXTYAYEVTWGYFXCOWNAXTYAYEWAWGVRYCYEWBYFWOWHWCWDWEWFW
      IWJ $.

    ${
      curf2.z $e |- ( ph -> Z e. B ) $.
      $( Value of a component of the curry functor natural transformation.
         (Contributed by Mario Carneiro, 13-Jan-2017.) $)
      curf2val $p |- ( ph -> ( L ` Z ) =
        ( K ( <. X , Z >. ( 2nd ` F ) <. Y , Z >. ) ( I ` Z ) ) ) $=
        ( vz cv cfv cop c2nd co curf2 wceq wa simpr opeq2d oveq12d eqidd fveq2d
        cvv oveq123d ovexd fvmptd ) AUIOKUIUJZJUKZMVGULZNVGULZGUMUKZUNZUNKOJUKZ
        MOULZNOULZVKUNZUNCLVCAUIBCDEFGHIJKLMNPQRSTUAUBUCUDUEUFUGUOAVGOUPZUQZKKV
        HVMVLVPVRVIVNVJVOVKVRVGOMAVQURZUSVRVGONVSUSUTVRKVAVRVGOJVSVBVDUHAKVMVPV
        EVF $.
    $}

    curf2.n $e |- N = ( D Nat E ) $.
    $( The curry functor at a morphism is a natural transformation.
       (Contributed by Mario Carneiro, 13-Jan-2017.) $)
    curf2cl $p |- ( ph ->
      L e. ( ( ( 1st ` G ) ` X ) N ( ( 1st ` G ) ` Y ) ) ) $=
      ( vz vw vf c1st cfv co wcel cv chom cixp c2nd cop wceq wral cmpt curf2 wa
      cco cxpc wf cxp eqid xpcbas cfunc wbr wrel relfunc sylancr adantr opelxpi
      1st2ndbr sylan funcf2 simpr xpchom2 feq2d mpbid ccat catidcl curf11 df-ov
      fovcdmd eqtrdi oveq12d eleqtrrd ralrimiva wb fvexi mptelixpg ax-mp sylibr
      cvv cbs eqeltrd w3a ccid catrid catlid eqtr4d simpr1 simpr2 simpr3 xpcco2
      opeq12d 3ad2antr1 3eqtr4d fveq2d opelxpd funcco 3eqtr3d curf2val oveq123d
      curf12 ralrimivvva curf1cl isnat2 mpbir2and ) ALNHULUMZUMZOYFUMZMUNUOLUIC
      UIUPZYGULUMZUMZYIYHULUMZUMZFUQUMZUNZURZUOUJUPZLUMZUKUPZYIYQYGUSUMUNUMZYKY
      QYJUMZUTZYQYLUMZFVFUMZUNZUNZYSYIYQYHUSUMUNUMZYILUMZYKYMUTZUUCUUDUNZUNZVAZ
      UKYIYQEUQUMZUNZVBUJCVBUICVBALUICKYIJUMZNYIUTZOYIUTZGUSUMZUNZUNZVCZYPAUIBC
      DEFGHIJKLNOPQRSTUAUBUCUDUEUFUGVDAUUTYOUOZUICVBZUVAYPUOZAUVBUICAYICUOZVEZU
      UTUUPGULUMZUMZUUQUVGUMZYNUNZYOUVFKUUOUVJNOIUNZYIYIUUMUNZUUSUVFUUPUUQDEVGU
      NZUQUMZUNZUVJUUSVHUVKUVLVIZUVJUUSVHUVFBCVIZUVMFUVGUURUVNYNUUPUUQDEUVMBCUV
      MVJZQUAVKZUVNVJZYNVJZAUVGUURUVMFVLUNZVMZUVEAUWBVNGUWBUOZUWCUVMFVOTGUWBVSV
      PZVQANBUOZUVEUUPUVQUOZUDNYIBCVRVTZAOBUOZUVEUUQUVQUOZUEOYIBCVRVTZWAUVFUVOU
      VPUVJUUSUVFDEOYIUVMIUUMUVNNYIBCUVRQUAUBUUMVJZAUWFUVEUDVQZAUVEWBZAUWIUVEUE
      VQZUWNUVTWCWDWEAKUVKUOZUVEUFVQUVFCEJUUMYIUAUWLUCAEWFUOZUVESVQZUWNWGZWJUVF
      YKUVHYMUVIYNUVFYKNYIUVGUNZUVHUVFBCDEFGHYGNYIPQADWFUOZUVERVQZUWRAUWDUVETVQ
      ZUAUWMYGVJZUWNWHNYIUVGWIZWKUVFYMOYIUVGUNZUVIUVFBCDEFGHYHOYIPQUXBUWRUXCUAU
      WOYHVJZUWNWHOYIUVGWIZWKWLWMWNCWTUOUVDUVCWOCEXAUAWPUICUUTYOWTWQWRWSXBAUULU
      IUJUKCCUUNAUVEYQCUOZYSUUNUOZXCZVEZKYQJUMZUTZNYQUTZOYQUTZUURUNZUMZNDXDUMZU
      MZYSUTZUUPUXOUURUNZUMZUVHUXOUVGUMZUTZUXPUVGUMZUUDUNZUNZOUXSUMZYSUTZUUQUXP
      UURUNZUMZKUUOUTZUUSUMZUVHUVIUTZUYFUUDUNZUNZUUFUUKUXLUXNUYAUUPUXOUTUXPUVMV
      FUMZUNUNZUUPUXPUURUNZUMUYJUYMUUPUUQUTUXPUYRUNUNZUYTUMUYHUYQUXLUYSVUAUYTUX
      LKUXTNNUTODVFUMZUNUNZUXMYSYIYQUTYQEVFUMZUNUNZUTUYIKNOUTOVUBUNUNZYSUUOYIYI
      UTYQVUDUNUNZUTUYSVUAUXLVUCVUFVUEVUGUXLVUCKVUFUXLBDVUBUXSKINOQUBUXSVJZAUXA
      UXKRVQZAUWFUXKUDVQZVUBVJZAUWIUXKUEVQZAUWPUXKUFVQZXEUXLBDVUBUXSKINOQUBVUHV
      UIVUJVUKVULVUMXFXGUXLVUEYSVUGUXLCEVUDJYSUUMYIYQUAUWLUCAUWQUXKSVQZAUVEUXIU
      XJXHZVUDVJZAUVEUXIUXJXIZAUVEUXIUXJXJZXFUXLCEVUDJYSUUMYIYQUAUWLUCVUNVUOVUP
      VUQVURXEXGXLUXLDENYQOYQVUDUVMVUBUXTYSIUUMKUXMNYIUYRBCUVRQUAUBUWLVUJVUOVUJ
      VUQVUKVUPUYRVJZVULVUQUXLBDUXSINQUBVUHVUIVUJWGZVURVUMUXLCEJUUMYQUAUWLUCVUN
      VUQWGZXKUXLDEOYIOYQVUDUVMVUBKUUOIUUMUYIYSNYIUYRBCUVRQUAUBUWLVUJVUOVULVUOV
      UKVUPVUSVULVUQVUMAUXIUVEUUOUVLUOUXJUWSXMZUXLBDUXSIOQUBVUHVUIVULWGZVURXKXN
      XOUXLUVQUVMUYRFUVGUURUVNUYAUXNUUDUUPUXOUXPUVSUVTVUSUUDVJZAUWCUXKUWEVQZAUX
      IUVEUWGUXJUWHXMZUXLNYQBCVUJVUQXPUXLOYQBCVULVUQXPZUXLUYANNIUNZUUNVIUUPUXOU
      VNUNUXLUXTYSVVHUUNVUTVURXPUXLDENYQUVMIUUMUVNNYIBCUVRQUAUBUWLVUJVUOVUJVUQU
      VTWCWMUXLUXNUVKYQYQUUMUNZVIUXOUXPUVNUNUXLKUXMUVKVVIVUMVVAXPUXLDEOYQUVMIUU
      MUVNNYQBCUVRQUAUBUWLVUJVUQVULVUQUVTWCWMXQUXLUVQUVMUYRFUVGUURUVNUYMUYJUUDU
      UPUUQUXPUVSUVTVUSVVDVVEVVFAUXIUVEUWJUXJUWKXMVVGUXLUYMUVPUVOUXLKUUOUVKUVLV
      UMVVBXPUXLDEOYIUVMIUUMUVNNYIBCUVRQUAUBUWLVUJVUOVULVUOUVTWCWMUXLUYJOOIUNZU
      UNVIUUQUXPUVNUNUXLUYIYSVVJUUNVVCVURXPUXLDEOYQUVMIUUMUVNOYIBCUVRQUAUBUWLVU
      LVUOVULVUQUVTWCWMXQXRUXLYRUXRYTUYCUUEUYGUXLUUBUYEUUCUYFUUDUXLYKUVHUUAUYDU
      XLYKUWTUVHUXLBCDEFGHYGNYIPQVUIVUNAUWDUXKTVQZUAVUJUXDVUOWHUXEWKZUXLUUANYQU
      VGUNUYDUXLBCDEFGHYGNYQPQVUIVUNVVKUAVUJUXDVUQWHNYQUVGWIWKXLUXLUUCOYQUVGUNU
      YFUXLBCDEFGHYHOYQPQVUIVUNVVKUAVULUXGVUQWHOYQUVGWIWKZWLUXLYRKUXMUXQUNUXRUX
      LBCDEFGHIJKLNOYQPQVUIVUNVVKUAUBUCVUJVULVUMUGVUQXSKUXMUXQWIWKUXLYTUXTYSUYB
      UNUYCUXLBCDEUXSFGHYSUUMYGNYIYQPQVUIVUNVVKUAVUJUXDVUOUWLVUHVUQVURYAUXTYSUY
      BWIWKXTUXLUUGUYLUUHUYNUUJUYPUXLUUIUYOUUCUYFUUDUXLYKUVHYMUVIVVLUXLYMUXFUVI
      UXLBCDEFGHYHOYIPQVUIVUNVVKUAVULUXGVUOWHUXHWKXLVVMWLUXLUUGUYIYSUYKUNUYLUXL
      BCDEUXSFGHYSUUMYHOYIYQPQVUIVUNVVKUAVULUXGVUOUWLVUHVUQVURYAUYIYSUYKWIWKUXL
      UUHUUTUYNUXLBCDEFGHIJKLNOYIPQVUIVUNVVKUAUBUCVUJVULVUMUGVUOXSKUUOUUSWIWKXT
      XNYBAUIUJLCEFUUDUKYGYHUUMYNMUHUAUWLUWAVVDABCDEFGHYGNPQRSTUAUDUXDYCABCDEFG
      HYHOPQRSTUAUEUXGYCYDYE $.
  $}

  ${
    $d g w x y z D $.  $d g w x y z E $.  $d g w x y z F $.  $d f g x y z Q $.
    $d f g w x y z C $.  $d f g w x y z G $.  $d f g w x y z ph $.
    curfcl.g $e |- G = ( <. C , D >. curryF F ) $.
    curfcl.q $e |- Q = ( D FuncCat E ) $.
    curfcl.c $e |- ( ph -> C e. Cat ) $.
    curfcl.d $e |- ( ph -> D e. Cat ) $.
    curfcl.f $e |- ( ph -> F e. ( ( C Xc. D ) Func E ) ) $.
    $( The curry functor of a functor ` F : C X. D --> E ` is a functor
       ` curryF ( F ) : C --> ( D --> E ) ` .  (Contributed by Mario Carneiro,
       13-Jan-2017.) $)
    curfcl $p |- ( ph -> G e. ( C Func Q ) ) $=
      ( vx vy cfv cop co eqid wcel adantr vz vg vf vw c1st c2nd cfunc cmpt chom
      cbs cv ccid cmpo curfval wceq fvex mptex op1std syl op2ndd opeq12d eqtr4d
      mpoex wbr cco cnat fucbas fuchom cxpc ccat funcrcl simprd fuccat cvv opex
      a1i simpr curf1cl fmpt2d cxp wfn ovex fnmpoi fneq1d mpbiri ovmpt4g mp3an3
      oveqd sylan9eq ad2antrr simplrl simplrr curf2cl ccom xpcbas wrel 1st2ndbr
      relfunc sylancr opelxpi adantll funcid xpcid fveq2d df-ov eqtr4di eqtr2di
      wa curf11 3eqtr3d mpteq2dva cidfn dffn2 sylib funcf1 fcompt syl2anc curf2
      wf catidcl fucid 3eqtr4d w3a 3ad2ant1 simp21 eqtrdi simp22 simp23 oveq12d
      simp3r curf2val simp3l oveq123d opelxpd xpchom2 eleqtrrd funcco xpcco2
      sylan catlid opeq2d eqtrd 3eqtr2rd catcocl fucco isfuncd df-br eqeltrd )
      AGGUEOZGUFOZPZBDUGQZAGMBUJOZNCUJOZMUKZNUKZFUEOZQZUHZNUAUUNUUNUBUUPUAUKZCU
      IOZQUUOBULOZOZUBUKZUUOUUPPZUUOUUTPZFUFOZQQUHUMZPZUHZMNUUMUUMUBUUOUUPBUIOZ
      QZUAUUNUVDUUTCULOZOUVFUUPUUTPUVGQQZUHZUHZUMZPZUUKAMNUAUUMUUNBCUVBUBEFGUVK
      UVMUVAHUUMRZJKLUUNRZUVARZUVBRZUVKRZUVMRZUNZAUUIUVJUUJUVQAGUVRUOZUUIUVJUOU
      WEUVJUVQGMUUMUVIBUJUPZUQZMNUUMUUMUVPUWGUWGVCZURUSZAUWFUUJUVQUOUWEUVJUVQGU
      WHUWIUTUSZVAVBAUUIUUJUULVDUUKUULSAMNUAUUMCEUGQZBBVEOZUVBUCUBDUUIUUJUVKDUL
      OZCEVFQZDVEOZUVSCEDIVGUWCCEDUWOIUWORZVHUWBUWNRZUWMRZUWPRZJACEDIKABCVIQZVJ
      SZEVJSZAFUXAEUGQZSZUXBUXCXHLUXAEFVKUSVLZVMAMMUUMUVIUWLUUIVNUVIVNSAUUOUUMS
      ZXHZUUSUVHVOVPUWJUXHUUMUUNBCEFGUUOUUIOZUUOHUVSABVJSZUXGJTZACVJSZUXGKTZAUX
      EUXGLTZUVTAUXGVQZUXIRZVRZVSAUUJUUMUUMVTZWAUVQUXRWAMNUUMUUMUVPUVQUVQRZUBUV
      LUVOUUOUUPUVKWBUQZWCAUXRUUJUVQUWKWDWEAUXGUUPUUMSZXHZXHZUBUBUVLUVOUXIUUPUU
      IOZUWOQUUOUUPUUJQZVNUVOVNSUYCUVDUVLSZXHZUAUUNUVNCUJUPUQVPAUYBUYEUUOUUPUVQ
      QZUVPAUUJUVQUUOUUPUWKWHUXGUYAUVPVNSUYHUVPUOUXTMNUUMUUMUVPUVQVNUXSWFWGWIUY
      GUUMUUNBCEFGUVKUVMUVDUVDUYEOZUWOUUOUUPHUVSAUXJUYBUYFJWJAUXLUYBUYFKWJAUXEU
      YBUYFLWJUVTUWCUWDAUXGUYAUYFWKAUXGUYAUYFWLUYCUYFVQUYIRUWQWMVSUXHNUUNUVCUUP
      UVMOZUVEUVEUVGQZQZUHZEULOZUXIUEOZWNZUVCUUOUUOUUJQOZUXIUWNOUXHUYMNUUNUUPUY
      OOZUYNOZUHZUYPUXHNUUNUYLUYSUXHUUPUUNSZXHZUVEUXAULOZOZUYKOZUVEUUQOZUYNOUYL
      UYSVUBUUMUUNVTZUXAVUCEUUQUVGUYNUVEBCUXAUUMUUNUXARZUVSUVTWOZVUCRZUYNRZAUUQ
      UVGUXDVDZUXGVUAAUXDWPZUXEVULUXAEWRZLFUXDWQZWSWJUXGVUAUVEVUGSAUUOUUPUUMUUN
      WTXAXBVUBVUEUVCUYJPZUYKOUYLVUBVUDVUPUYKVUBBCUUOUUPUXAVUCUVBUVMUUMUUNVUHAU
      XJUXGVUAJWJZAUXLUXGVUAKWJZUVSUVTUWBUWDVUJUXHUXGVUAUXOTZUXHVUAVQZXCXDUVCUY
      JUYKXEXFVUBVUFUYRUYNVUBUYRUURVUFVUBUUMUUNBCEFGUXIUUOUUPHUVSVUQVURAUXEUXGV
      UALWJUVTVUSUXPVUTXIUUOUUPUUQXEXGXDXJXKUXHEUJOZVNUYNXSZUUNVVAUYOXSUYPUYTUO
      UXHUYNVVAWAZVVBUXHUXCVVCAUXCUXGUXFTVVAEUYNVVARZVUKXLUSVVAUYNXMXNUXHUUNVVA
      CEUYOUXIUFOZUVTVVDUXHUWLWPUXIUWLSUYOVVEUWLVDCEWRUXQUXIUWLWQWSXONUYNUYOUUN
      VVAVNXPXQVBUXHNUUMUUNBCEFGUVKUVMUVCUYQUUOUUOHUVSUXKUXMUXNUVTUWCUWDUXOUXOU
      XHUUMBUVBUVKUUOUVSUWCUWBUXKUXOXTUYQRXRUXHCEDUYNUXIUWNIUWRVUKUXQYAYBAUXGUY
      AUUTUUMSZYCZUCUKZUVLSZUVDUUPUUTUVKQZSZXHZYCZUDUUNUVDVVHUVEUUTUWMQQZUDUKZU
      VMOZUUOVVOPZUUTVVOPZUVGQZQZUHUDUUNVVOUVDUUPUUTUUJQOZOZVVOVVHUYEOZOZVVOUYO
      OZVVOUYDUEOOZPZVVOUUTUUIOZUEOOZEVEOZQZQZUHVVNUUOUUTUUJQOZVWAVWCUXIUYDPVWH
      UWPQQVVMUDUUNVVTVWLVVMVVOUUNSZXHZVWLUVDVVPPZUUPVVOPZVVRUVGQZOZVVHVVPPZVVQ
      VWQUVGQZOZVVQUUQOZVWQUUQOZPZVVRUUQOZVWJQZQVWPVWTVVQVWQPVVRUXAVEOZQQZVVSOZ
      VVTVWOVWBVWSVWDVXBVWKVXGVWOVWGVXEVWIVXFVWJVWOVWEVXCVWFVXDVWOVWEUUOVVOUUQQ
      VXCVWOUUMUUNBCEFGUXIUUOVVOHUVSVVMUXJVWNAVVGUXJVVLJYDZTZVVMUXLVWNAVVGUXLVV
      LKYDZTZVVMUXEVWNAVVGUXEVVLLYDZTZUVTVVMUXGVWNAUXGUYAVVFVVLYEZTZUXPVVMVWNVQ
      ZXIUUOVVOUUQXEYFVWOVWFUUPVVOUUQQVXDVWOUUMUUNBCEFGUYDUUPVVOHUVSVXLVXNVXPUV
      TVVMUYAVWNAUXGUYAVVFVVLYGZTZUYDRVXSXIUUPVVOUUQXEYFVAVWOVWIUUTVVOUUQQVXFVW
      OUUMUUNBCEFGVWHUUTVVOHUVSVXLVXNVXPUVTVVMVVFVWNAUXGUYAVVFVVLYHZTZVWHRVXSXI
      UUTVVOUUQXEYFYIVWOVWBUVDVVPVWRQVWSVWOUUMUUNBCEFGUVKUVMUVDVWAUUPUUTVVOHUVS
      VXLVXNVXPUVTUWCUWDVYAVYCVVMVVKVWNAVVGVVIVVKYJZTZVWARZVXSYKUVDVVPVWRXEYFVW
      OVWDVVHVVPVXAQVXBVWOUUMUUNBCEFGUVKUVMVVHVWCUUOUUPVVOHUVSVXLVXNVXPUVTUWCUW
      DVXRVYAVVMVVIVWNAVVGVVIVVKYLZTZVWCRZVXSYKVVHVVPVXAXEYFYMVWOVUGUXAVXHEUUQU
      VGUXAUIOZVWTVWPVWJVVQVWQVVRVUIVYJRZVXHRZVWJRZVWOVUMUXEVULVUNVXPVUOWSVVMUX
      GVWNVVQVUGSVXQUUOVVOUUMUUNWTYSVVMUYAVWNVWQVUGSVXTUUPVVOUUMUUNWTYSVVMVVFVW
      NVVRVUGSVYBUUTVVOUUMUUNWTYSVWOVWTUVLVVOVVOUVAQZVTVVQVWQVYJQVWOVVHVVPUVLVY
      NVYHVWOUUNCUVMUVAVVOUVTUWAUWDVXNVXSXTZYNVWOBCUUPVVOUXAUVKUVAVYJUUOVVOUUMU
      UNVUHUVSUVTUWCUWAVXRVXSVYAVXSVYKYOYPVWOVWPVVJVYNVTVWQVVRVYJQVWOUVDVVPVVJV
      YNVYEVYOYNVWOBCUUTVVOUXAUVKUVAVYJUUPVVOUUMUUNVUHUVSUVTUWCUWAVYAVXSVYCVXSV
      YKYOYPYQVWOVXJVVNVVPPZVVSOVVTVWOVXIVYPVVSVWOVXIVVNVVPVVPVVOVVOPVVOCVEOZQQ
      ZPVYPVWOBCUUPVVOUUTVVOVYQUXAUWMVVHVVPUVKUVAUVDVVPUUOVVOVXHUUMUUNVUHUVSUVT
      UWCUWAVXRVXSVYAVXSUWSVYQRZVYLVYCVXSVYHVYOVYEVYOYRVWOVYRVVPVVNVWOUUNCVYQUV
      MVVPUVAVVOVVOUVTUWAUWDVXNVXSVYSVXSVYOYTUUAUUBXDVVNVVPVVSXEXFUUCXKVVMUDUUM
      UUNBCEFGUVKUVMVVNVWMUUOUUTHUVSVXKVXMVXOUVTUWCUWDVXQVYBVVMUUMBUWMVVHUVDUVK
      UUOUUPUUTUVSUWCUWSVXKVXQVXTVYBVYGVYDUUDVWMRXRVVMUDUUNCEDVWCVWAUWPVWJUXIUY
      DVWHUWOIUWQUVTVYMUWTVVMUUMUUNBCEFGUVKUVMVVHVWCUWOUUOUUPHUVSVXKVXMVXOUVTUW
      CUWDVXQVXTVYGVYIUWQWMVVMUUMUUNBCEFGUVKUVMUVDVWAUWOUUPUUTHUVSVXKVXMVXOUVTU
      WCUWDVXTVYBVYDVYFUWQWMUUEYBUUFUUIUUJUULUUGXNUUH $.
  $}

  ${
    $d g x y z A $.  $d g x y z B $.  $d g x y z C $.  $d g x y z ph $.
    $d g x y z D $.  $d g y z E $.  $d g x y z F $.
    curfpropd.1 $e |- ( ph -> ( Homf ` A ) = ( Homf ` B ) ) $.
    curfpropd.2 $e |- ( ph -> ( comf ` A ) = ( comf ` B ) ) $.
    curfpropd.3 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    curfpropd.4 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    curfpropd.a $e |- ( ph -> A e. Cat ) $.
    curfpropd.b $e |- ( ph -> B e. Cat ) $.
    curfpropd.c $e |- ( ph -> C e. Cat ) $.
    curfpropd.d $e |- ( ph -> D e. Cat ) $.
    curfpropd.f $e |- ( ph -> F e. ( ( A Xc. C ) Func E ) ) $.
    $( If two categories have the same set of objects, morphisms, and
       compositions, then they curry the same functor to the same result.
       (Contributed by Mario Carneiro, 26-Jan-2017.) $)
    curfpropd $p |- ( ph ->
      ( <. A , C >. curryF F ) = ( <. B , D >. curryF F ) ) $=
      ( vy cfv co eqid vx vz vg cbs c1st cmpt chom ccid cop c2nd cmpo homfeqbas
      cv ccurf wcel wa wceq adantr mpteq1d chomf ad2antrr simprl homfeqval ccat
      simprr cidpropd fveq1d mpteq12dv mpoeq123dva opeq12d mpteq12dva ad3antrrr
      oveq1d oveq2d curfval cxpc cfunc xpcpropd eleqtrd 3eqtr4d ) AUABUDRZQDUDR
      ZUAUMZQUMZGUERSZUFZQUBWBWBUCWDUBUMZDUGRZSZWCBUHRZRZUCUMZWCWDUIWCWGUIZGUJR
      ZSZSZUFZUKZUIZUFZUAQWAWAUCWCWDBUGRZSZUBWBWLWGDUHRZRZWMWDWGUIWNSZSZUFZUFZU
      KZUIUACUDRZQEUDRZWEUFZQUBXKXKUCWDWGEUGRZSZWCCUHRZRZWLWOSZUFZUKZUIZUFZUAQX
      JXJUCWCWDCUGRZSZUBXKWLWGEUHRZRZXESZUFZUFZUKZUIBDUIGUNSZCEUIGUNSZAWTYAXIYI
      AUAWAWSXJXTABCHULZAWCWAUOZUPZWFXLWRXSYNQWBXKWEAWBXKUQZYMADEJULZURZUSYNQUB
      WBWBWQXKXKXRYQYNYOWDWBUOZYQURYNYRWGWBUOZUPZUPZUCWIWPXNXQUUAWBDEWHXMWDWGWB
      TZWHTZXMTZADUTREUTRUQYMYTJVAYNYRYSVBYNYRYSVEVCUUAWKXPWLWOUUAWCWJXOAWJXOUQ
      YMYTABCVDVDHILMVFVAVGVMVHVIVJVKAUAQWAWAXHXJXJYHYLAWAXJUQYMYLURAYMWDWAUOZU
      PZUPZUCXBXGYCYGUUGWABCXAYBWCWDWATZXATZYBTZABUTRCUTRUQUUFHURAYMUUEVBAYMUUE
      VEVCUUGWLXBUOZUPZUBWBXFXKYFAYOUUFUUKYPVAUULYSUPZXDYEWLXEUUMWGXCYDAXCYDUQU
      UFUUKYSADEVDVDJKNOVFVLVGVNVKVKVIVJAUAQUBWAWBBDWJUCFGYJXAXCWHYJTUUHLNPUUBU
      UCWJTUUIXCTVOAUAQUBXJXKCEXOUCFGYKYBYDXMYKTXJTMOAGBDVPSZFVQSCEVPSZFVQSPAUU
      NUUOFVQABCDEVDHIJKLMNOVRVMVSXKTUUDXOTUUJYDTVOVT $.
  $}

  ${
    $d c f g x y z C $.  $d c f g x y z D $.  $d c f g x y z ph $.
    $d c f g y z E $.  $d g x y z F $.  $d c f g x y z G $.
    uncfval.g $e |- F = ( <" C D E "> uncurryF G ) $.
    uncfval.c $e |- ( ph -> D e. Cat ) $.
    uncfval.d $e |- ( ph -> E e. Cat ) $.
    uncfval.f $e |- ( ph -> G e. ( C Func ( D FuncCat E ) ) ) $.
    $( Value of the uncurry functor, which is the reverse of the curry functor,
       taking ` G : C --> ( D --> E ) ` to ` uncurryF ( G ) : C X. D --> E ` .
       (Contributed by Mario Carneiro, 13-Jan-2017.) $)
    uncfval $p |- ( ph -> F = ( ( D evalF E ) o.func
        ( ( G o.func ( C 1stF D ) ) pairF ( C 2ndF D ) ) ) ) $=
      ( vc vf co ccofu cvv cfv wceq ccat wcel oveq12d cuncf cevlf c1stf cprf c1
      cs3 c2ndf cv c2 cc0 cmpo df-uncf a1i simprl fveq1d s3fv1 syl adantr eqtrd
      s3fv2 simprr cfuc cfunc funcrcl simpld s3fv0 cword s3cli elex elexd ovexd
      wa mp1i ovmpod eqtrid ) AEBCDUFZFUAMCDUBMZFBCUCMZNMZBCUGMZUDMZNMZGAKLVPFO
      OUEKUHZPZUIWCPZUBMZLUHZUJWCPZWDUCMZNMZWHWDUGMZUDMZNMZWBUAOUAKLOOWMUKQALKU
      LUMAWCVPQZWGFQZVLZVLZWFVQWLWANWQWDCWEDUBWQWDUEVPPZCWQUEWCVPAWNWOUNZUOAWRC
      QZWPACRSWTHBCDRUPUQURUSZWQWEUIVPPZDWQUIWCVPWSUOAXBDQZWPADRSXCIBCDRUTUQURU
      STWQWJVSWKVTUDWQWGFWIVRNAWNWOVAWQWHBWDCUCWQWHUJVPPZBWQUJWCVPWSUOAXDBQZWPA
      BRSZXEAXFCDVBMZRSZAFBXGVCMZSXFXHVLJBXGFVDUQVEBCDRVFUQURUSZXATTWQWHBWDCUGX
      JXATTTVPOVGZSVPOSABCDVHVPXKVIVMAFXIJVJAVQWANVKVNVO $.

    $( The uncurry operation takes a functor ` F : C --> ( D --> E ) ` to a
       functor ` uncurryF ( F ) : C X. D --> E ` .  (Contributed by Mario
       Carneiro, 13-Jan-2017.) $)
    uncfcl $p |- ( ph -> F e. ( ( C Xc. D ) Func E ) ) $=
      ( cevlf co c1stf ccofu cxpc cfunc eqid ccat wcel cofucl cprf uncfval cfuc
      c2ndf wa funcrcl syl simpld 1stfcl 2ndfcl prfcl evlfcl eqeltrd ) AECDKLZF
      BCMLZNLZBCUDLZUALZNLBCOLZDPLABCDEFGHIJUBAUSCDUCLZCOLZDURUNAUSUTURVACUPUQU
      RQVAQAUSBUTUOFABCUOUSUSQZABRSZUTRSZAFBUTPLSVCVDUEJBUTFUFUGUHZHUOQUIJTABCU
      QUSVBVEHUQQUJUKACDUTUNUNQUTQHIULTUM $.

    ${
      uncf1.a $e |- A = ( Base ` C ) $.
      uncf1.b $e |- B = ( Base ` D ) $.
      uncf1.x $e |- ( ph -> X e. A ) $.
      uncf1.y $e |- ( ph -> Y e. B ) $.
      $( Value of the uncurry functor on an object.  (Contributed by Mario
         Carneiro, 13-Jan-2017.) $)
      uncf1 $p |- ( ph -> ( X ( 1st ` F ) Y ) =
        ( ( 1st ` ( ( 1st ` G ) ` X ) ) ` Y ) ) $=
        ( cfv co c1st cevlf c1stf ccofu c2ndf cprf cop uncfval fveq2d oveqd cxp
        df-ov cxpc cfuc eqid xpcbas ccat wcel cfunc wa syl simpld 1stfcl cofucl
        funcrcl 2ndfcl prfcl evlfcl opelxpd cofu1 eqtrid chom prf1 1stf1 op1stg
        wceq syl2anc eqtrd c2nd 2ndf1 op2ndg opeq12d eqtr4di fucbas wbr relfunc
        wrel 1st2ndbr sylancr funcf1 ffvelcdmd evlf1 3eqtrd ) AIJGUASZTIJEFUBTZ
        HDEUCTZUDTZDEUETZUFTZUDTZUASZTZIJUGZWSUASSZWOUASZSZJIHUASZSZUASSZAWNXAI
        JAGWTUAADEFGHKLMNUHUIUJAXBXCXASXFIJXAULABCUKZDEUMTZEFUNTZEUMTZFWSWOXCDE
        XKBCXKUOZOPUPZAXKXLWSXMEWQWRWSUOZXMUOAXKDXLWPHADEWPXKXNADUQURZXLUQURZAH
        DXLUSTZURZXQXRUTNDXLHVEVAVBZLWPUOZVCZNVDZADEWRXKXNYALWRUOZVFZVGAEFXLWOW
        OUOZXLUOZLMVHAIJBCQRVIZVJVKAXFXHJXETZXIAXFXHJUGZXESYJAXDYKXEAXDXCWQUASS
        ZXCWRUASSZUGYKAXJXKXLWSEWQWRXKVLSZXCXPXOYNUOZYDYFYIVMAYLXHYMJAYLXCWPUAS
        SZXGSXHAXJXKDXLWPHXCXOYCNYIVJAYPIXGAYPXCUASZIAXJDEWPXCXKYNXNXOYOYALYBYI
        VNAIBURZJCURZYQIVPQRIJBCVOVQVRUIVRAYMXCVSSZJAXJDEWRXCXKYNXNXOYOYALYEYIV
        TAYRYSYTJVPQRIJBCWAVQVRWBVRUIXHJXEULWCACEFWOXHJYGLMPABEFUSTZIXGABUUADXL
        XGHVSSZOEFXLYHWDAXSWGXTXGUUBXSWEDXLWFNHXSWHWIWJQWKRWLVRWM $.

      uncf2.h $e |- H = ( Hom ` C ) $.
      uncf2.j $e |- J = ( Hom ` D ) $.
      uncf2.z $e |- ( ph -> Z e. A ) $.
      uncf2.w $e |- ( ph -> W e. B ) $.
      uncf2.r $e |- ( ph -> R e. ( X H Z ) ) $.
      uncf2.s $e |- ( ph -> S e. ( Y J W ) ) $.
      $( Value of the uncurry functor on a morphism.  (Contributed by Mario
         Carneiro, 13-Jan-2017.) $)
      uncf2 $p |- ( ph -> ( R ( <. X , Y >. ( 2nd ` F ) <. Z , W >. ) S ) =
        ( ( ( ( X ( 2nd ` G ) Z ) ` R ) ` W )
          ( <. ( ( 1st ` ( ( 1st ` G ) ` X ) ) ` Y ) ,
               ( ( 1st ` ( ( 1st ` G ) ` X ) ) ` W ) >. ( comp ` E )
               ( ( 1st ` ( ( 1st ` G ) ` Z ) ) ` W ) )
          ( ( Y ( 2nd ` ( ( 1st ` G ) ` X ) ) W ) ` S ) ) ) $=
        ( cop c2nd cfv co c1stf ccofu c2ndf cprf cevlf cco uncfval fveq2d oveqd
        c1st df-ov cxpc cfuc chom eqid xpcbas ccat wcel cfunc wa funcrcl simpld
        cxp syl 1stfcl cofucl 2ndfcl prfcl evlfcl opelxpd eleqtrrd cofu2 eqtrid
        xpchom2 eqtrd prf1 cofu1 1stf1 wceq op1stg syl2anc 2ndf1 op2ndg opeq12d
        oveq12d prf2 cres 1stf2 fveq1d fvresd 3eqtrd fveq12d 2ndf2 eqtr4di cnat
        fucbas wrel wbr relfunc 1st2ndbr sylancr funcf1 ffvelcdmd fuchom funcf2
        evlf2val ) AFGNOUKZPMUKZIULUMZUNZUNZFGUKZYAYBJDEUOUNZUPUNZDEUQUNZURUNZU
        LUMUNUMZYAYJVDUMZUMZYBYLUMZEHUSUNZULUMZUNZUMZFNPJULUMZUNZUMZGNJVDUMZUMZ
        OUKZPUUBUMZMUKZYPUNZUNZMUUAUMGOMUUCULUMUNUMOUUCVDUMZUMMUUIUMUKMUUEVDUMU
        MHUTUMZUNUNAYEFGYAYBYOYJUPUNZULUMZUNZUNZYRAYDUUMFGAYCUULYAYBAIUUKULADEH
        IJQRSTVAVBVCVCAUUNYFUUMUMYRFGUUMVEABCVQZDEVFUNZEHVGUNZEVFUNZYFHYJYOUUPV
        HUMZYAYBDEUUPBCUUPVIZUAUBVJZAUUPUUQYJUUREYHYIYJVIZUURVIAUUPDUUQYGJADEYG
        UUPUUTADVKVLZUUQVKVLZAJDUUQVMUNZVLZUVCUVDVNTDUUQJVOVRVPZRYGVIZVSZTVTZAD
        EYIUUPUUTUVGRYIVIZWAZWBAEHUUQYOYOVIZUUQVIZRSWCANOBCUCUDWDZAPMBCUGUHWDZU
        USVIZAYFNPKUNZOMLUNZVQYAYBUUSUNZAFGUVRUVSUIUJWDADEPMUUPKLUUSNOBCUUTUAUB
        UEUFUCUDUGUHUVQWHWEZWFWGWIAYRUUAGUKZUUGUMUUHAYKUWBYQUUGAYMUUDYNUUFYPAYM
        YAYHVDUMZUMZYAYIVDUMZUMZUKUUDAUUOUUPUUQYJEYHYIUUSYAUVBUVAUVQUVJUVLUVOWJ
        AUWDUUCUWFOAUWDYAYGVDUMZUMZUUBUMUUCAUUOUUPDUUQYGJYAUVAUVITUVOWKAUWHNUUB
        AUWHYAVDUMZNAUUODEYGYAUUPUUSUUTUVAUVQUVGRUVHUVOWLANBVLZOCVLZUWINWMUCUDN
        OBCWNWOWIZVBWIAUWFYAULUMZOAUUODEYIYAUUPUUSUUTUVAUVQUVGRUVKUVOWPAUWJUWKU
        WMOWMUCUDNOBCWQWOWIWRWIAYNYBUWCUMZYBUWEUMZUKUUFAUUOUUPUUQYJEYHYIUUSYBUV
        BUVAUVQUVJUVLUVPWJAUWNUUEUWOMAUWNYBUWGUMZUUBUMUUEAUUOUUPDUUQYGJYBUVAUVI
        TUVPWKAUWPPUUBAUWPYBVDUMZPAUUODEYGYBUUPUUSUUTUVAUVQUVGRUVHUVPWLAPBVLZMC
        VLZUWQPWMUGUHPMBCWNWOWIZVBWIAUWOYBULUMZMAUUODEYIYBUUPUUSUUTUVAUVQUVGRUV
        KUVPWPAUWRUWSUXAMWMUGUHPMBCWQWOWIWRWIWSAYKYFYAYBYHULUMUNUMZYFYAYBYIULUM
        UNZUMZUKUWBAUUOUUPUUQYJEYHYIUUSYFYAYBUVBUVAUVQUVJUVLUVOUVPUWAWTAUXBUUAU
        XDGAUXBYFYAYBYGULUMUNZUMZUWHUWPYSUNZUMUUAAUUOUUPDYFUUQYGJUUSYAYBUVAUVIT
        UVOUVPUVQUWAWFAUXFFUXGYTAUWHNUWPPYSUWLUWTWSAUXFYFVDUVTXAZUMYFVDUMZFAYFU
        XEUXHAUUODEYGYAYBUUPUUSUUTUVAUVQUVGRUVHUVOUVPXBXCAYFUVTVDUWAXDAFUVRVLZG
        UVSVLZUXIFWMUIUJFGUVRUVSWNWOXEXFWIAUXDYFULUVTXAZUMYFULUMZGAYFUXCUXLAUUO
        DEYIYAYBUUPUUSUUTUVAUVQUVGRUVKUVOUVPXGXCAYFUVTULUWAXDAUXJUXKUXMGWMUIUJF
        GUVRUVSWQWOXEWRWIXFUUAGUUGVEXHAUUACEHUUJYOUUCUUELGUUGEHXIUNZOMUVMRSUBUF
        UUJVIUXNVIZABEHVMUNZNUUBABUXPDUUQUUBYSUAEHUUQUVNXJAUVEXKUVFUUBYSUVEXLDU
        UQXMTJUVEXNXOZXPZUCXQABUXPPUUBUXRUGXQUDUHUUGVIAUVRUUCUUEUXNUNFYTABDUUQU
        UBYSKUXNNPUAUEEHUUQUXNUVNUXOXRUXQUCUGXSUIXQUJXTXE $.
    $}

    $( Cancellation of curry with uncurry.  (Contributed by Mario Carneiro,
       13-Jan-2017.) $)
    curfuncf $p |- ( ph -> ( <. C , D >. curryF F ) = G ) $=
      ( vx vy vz vg cfv co cmpt cop wcel eqid cv c1st chom ccid c2nd cmpo ccurf
      cbs wa ccat ad2antrr cfuc cfunc simplr simpr uncf1 mpteq2dva wrel relfunc
      wbr fucbas 1st2ndbr sylancr funcf1 ffvelcdmda feqmptd eqtr4d wceq simpllr
      cco ad3antrrr simplrl simprr adantr funcrcl syl simpld catidcl uncf2 ccom
      funcid fucid eqtrd fveq1d wf fvco3 syl2anc oveq1d ffvelcdmd simprl funcf2
      catlid 3eqtrd 3impb mpoeq3dva cxp wfn funcfn2 fnov opeq12d 1st2nd adantrr
      sylib oveq2d adantrl cnat fuchom natcl catrid natfn dffn5 curfval 3eqtr4d
      nat1st2nd uncfcl ) AKBUHOZLCUHOZKUAZLUAZEUBOPZQZLMXQXQNXSMUAZCUCOZPZXRBUD
      OZOZNUAZXRXSRXRYBRZEUEOZPPZQZUFZRZQZKLXPXPNXRXSBUCOZPZMXQYGYBCUDOZOZYHXSY
      BRYIPPZQZQZUFZRFUBOZFUEOZRZBCREUGPZFAYNUUCUUBUUDAYNKXPXRUUCOZQUUCAKXPYMUU
      GAXRXPSZUIZYMUUGUBOZUUGUEOZRZUUGUUIYAUUJYLUUKUUIYALXQXSUUJOZQUUJUUILXQXTU
      UMUUIXSXQSZUIXPXQBCDEFXRXSGACUJSZUUHUUNHUKADUJSZUUHUUNIUKAFBCDULPZUMPZSZU
      UHUUNJUKXPTZXQTZAUUHUUNUNUUIUUNUOUPUQUUILXQDUHOZUUJUUIXQUVBCDUUJUUKUVAUVB
      TZUUICDUMPZURZUUGUVDSZUUJUUKUVDUTZCDUSZAXPUVDXRUUCAXPUVDBUUQUUCUUDUUTCDUU
      QUUQTZVAAUURURZUUSUUCUUDUURUTZBUUQUSZJFUURVBVCZVDZVEZUUGUVDVBZVCZVDZVFVGU
      UIYLLMXQXQXSYBUUKPZUFZUUKUUILMXQXQYKUVSUUIUUNYBXQSZYKUVSVHUUIUUNUWAUIZUIZ
      YKNYDYGUVSOZQUVSUWCNYDYJUWDUWCYGYDSZUIZYJYBYFXRXRUUDPOZOZUWDUUMYBUUJOZRUW
      IDVJOZPZPUWIDUDOZOZUWDUWKPUWDUWFXPXQBCYFYGDEFYOYCYBXRXSXRGAUUOUUHUWBUWEHV
      KAUUPUUHUWBUWEIVKZAUUSUUHUWBUWEJVKUUTUVAAUUHUWBUWEVIZUUIUUNUWAUWEVLZYOTZY
      CTZUWOUWCUWAUWEUUIUUNUWAVMZVNZUWFXPBYEYOXRUUTUWQYETZABUJSZUUHUWBUWEAUXBUU
      QUJSZAUUSUXBUXCUIJBUUQFVOVPVQZVKUWOVRUWCUWEUOVSUWFUWHUWMUWDUWKUWFUWHYBUWL
      UUJVTZOZUWMUWFYBUWGUXEUWFUWGUUGUUQUDOZOUXEUWFXPBYEUUQUUCUUDUXGXRUUTUXAUXG
      TZAUVKUUHUWBUWEUVMVKUWOWAUWFCDUUQUWLUUGUXGUVIUXHUWLTZUUIUVFUWBUWEUVOUKWBW
      CWDUWFXQUVBUUJWEZUWAUXFUWMVHUUIUXJUWBUWEUVRUKZUWTXQUVBYBUWLUUJWFWGWCWHUWF
      UVBDUWJUWLUWDDUCOZUUMUWIUVCUXLTZUXIUWNUWFXQUVBXSUUJUXKUWPWIUWJTZUWFXQUVBY
      BUUJUXKUWTWIUWCYDUUMUWIUXLPZYGUVSUWCXQCDUUJUUKYCUXLXSYBUVAUWRUXMUUIUVGUWB
      UVQVNUUIUUNUWAWJUWSWKZVEWLWMUQUWCNYDUXOUVSUXPVFVGWNWOUUIUUKXQXQWPWQUUKUVT
      VHUUIXQCDUUJUUKUVAUVQWRLMXQXQUUKWSXCVGWTUUIUVEUVFUUGUULVHUVHUVOUUGUVDXAVC
      VGUQAKXPUVDUUCUVNVFVGAUUBKLXPXPXRXSUUDPZUFZUUDAKLXPXPUUAUXQAUUHXSXPSZUUAU
      XQVHAUUHUXSUIZUIZUUANYPYGUXQOZQUXQUYANYPYTUYBUYAYGYPSZUIZYTMXQYBUYBOZQZUY
      BUYDMXQYSUYEUYDUWAUIZYSUYEYRYBYBUUKPOZUWIUWIRYBXSUUCOZUBOZOZUWJPZPUYEUWMU
      YLPUYEUYGXPXQBCYGYRDEFYOYCYBXRYBXSGAUUOUXTUYCUWAHVKZAUUPUXTUYCUWAIVKZAUUS
      UXTUYCUWAJVKUUTUVAUYAUUHUYCUWAAUUHUXSWJZUKZUYDUWAUOZUWQUWRUYAUXSUYCUWAAUU
      HUXSVMZUKZUYQUYAUYCUWAUNZUYGXQCYQYCYBUVAUWRYQTZUYMUYQVRVSUYGUYHUWMUYEUYLU
      YGXQCYQDUUJUUKUWLYBUVAVUAUXIUYDUVGUWAUYDUVEUVFUVGUVHUYAUVFUYCAUUHUVFUXSUV
      OXBVNUVPVCZVNUYQWAXDUYGUVBDUWJUWLUYEUXLUWIUYKUVCUXMUXIUYNUYDXQUVBYBUUJUYD
      XQUVBCDUUJUUKUVAUVCVUBVDVEUXNUYDXQUVBYBUYJUYDXQUVBCDUYJUYIUEOZUVAUVCUYDUV
      EUYIUVDSZUYJVUCUVDUTUVHUYAVUDUYCAUXSVUDUUHAXPUVDXSUUCUVNVEXEVNUYIUVDVBVCV
      DVEUYGUYBXQCDUUJUUKUXLUYJVUCCDXFPZYBVUETZUYGUYBCDUUGUYIVUEVUFUYGYPUUGUYIV
      UEPZYGUXQUYGXPBUUQUUCUUDYOVUEXRXSUUTUWQCDUUQVUEUVIVUFXGZAUVKUXTUYCUWAUVMV
      KUYPUYSWKUYTWIXNUVAUXMUYQXHXIWMUQUYDUYBXQWQUYBUYFVHUYDUYBXQCDUUJUUKUYJVUC
      VUEVUFUYDUYBCDUUGUYIVUEVUFUYAYPVUGYGUXQUYAXPBUUQUUCUUDYOVUEXRXSUUTUWQVUHA
      UVKUXTUVMVNUYOUYRWKZVEXNUVAXJMXQUYBXKXCVGUQUYANYPVUGUXQVUIVFVGWNWOAUUDXPX
      PWPWQUUDUXRVHAXPBUUQUUCUUDUUTUVMWRKLXPXPUUDWSXCVGWTAKLMXPXQBCYENDEUUFYOYQ
      YCUUFTUUTUXDHABCDEFGHIJXOUVAUWRUXAUWQVUAXLAUVJUUSFUUEVHUVLJFUURXAVCXM $.
  $}

  ${
    $d f g u v w x y z C $.  $d f g u v w x y z D $.  $d f g u v w x y z E $.
    $d f g u v w x y z F $.  $d f g u v w x y z G $.  $d f g w x y z ph $.
    uncfcurf.g $e |- G = ( <. C , D >. curryF F ) $.
    uncfcurf.c $e |- ( ph -> C e. Cat ) $.
    uncfcurf.d $e |- ( ph -> D e. Cat ) $.
    uncfcurf.f $e |- ( ph -> F e. ( ( C Xc. D ) Func E ) ) $.
    $( Cancellation of uncurry with curry.  (Contributed by Mario Carneiro,
       13-Jan-2017.) $)
    uncfcurf $p |- ( ph -> ( <" C D E "> uncurryF G ) = F ) $=
      ( vx co cfv cop wceq cv wral wcel eqid adantr vy vu vv vz vw vf cs3 cuncf
      vg c1st c2nd cbs wa ccat cxpc cfunc funcrcl syl simprd cfuc curfcl simprl
      simprr uncf1 curf11 eqtrd ralrimivva cxp wfn wb xpcbas wbr relfunc uncfcl
      wrel 1st2ndbr sylancr funcf1 ffnd eqfnov2 mpbird chom cco ad3antrrr uncf2
      syl2anc eqtrdi opeq12d oveq12d curf2val curf12 oveq123d ad2antrr ad2antlr
      ccid opelxpi opelxpd adantl catidcl xpchom2 eleqtrrd funcco xpcco2 fveq2d
      df-ov eqtr4di catrid catlid 3eqtr2d feq2d mpbid oveq2 eqeq12d ralxp oveq1
      wf funcf2 2ralbidv bitrid sylibr funcfn2 1st2nd 3eqtr4d ) ABCDUGFUHLZUJMZ
      YDUKMZNZEUJMZEUKMZNZYDEAYEYHYFYIAYEYHOZKPZUAPZYELZYLYMYHLZOZUACULMZQKBULM
      ZQZAYPKUAYRYQAYLYRRZYMYQRZUMZUMZYNYMYLFUJMZMZUJMZMZYOUUCYRYQBCDYDFYLYMYDS
      ZACUNRZUUBITZADUNRZUUBABCUOLZUNRZUUKAEUULDUPLZRZUUMUUKUMJUULDEUQURUSZTAFB
      CDUTLZUPLRZUUBABCUUQDEFGUUQSHIJVAZTYRSZYQSZAYTUUAVBZAYTUUAVCZVDUUCYRYQBCD
      EFUUEYLYMGUUTABUNRZUUBHTUUJAUUOUUBJTUVAUVBUUESZUVCVEVFVGAYEYRYQVHZVIYHUVF
      VIYKYSVJAUVFDULMZYEAUVFUVGUULDYEYFBCUULYRYQUULSZUUTUVAVKZUVGSZAUUNVOZYDUU
      NRZYEYFUUNVLZUULDVMZABCDYDFUUHIUUPUUSVNZYDUUNVPVQZVRVSAUVFUVGYHAUVFUVGUUL
      DYHYIUVIUVJAUVKUUOYHYIUUNVLZUVNJEUUNVPVQZVRVSKUAYRYQYEYHVTWFWAAYFYIOZUBPZ
      UCPZYFLZUVTUWAYILZOZUCUVFQZUBUVFQZAYLYMNZUDPZUEPZNZYFLZUWGUWJYILZOZUEYQQU
      DYRQZUAYQQKYRQUWFAUWNKUAYRYQUUCUWMUDUEYRYQUUCUWHYRRZUWIYQRZUMZUMZUWMUFPZU
      IPZUWKLZUWSUWTUWLLZOZUIYMUWICWBMZLZQUFYLUWHBWBMZLZQZUWRUXCUFUIUXGUXEUWRUW
      SUXGRZUWTUXERZUMZUMZUXAUWIUWSYLUWHFUKMLMZMZUWTYMUWIUUEUKMLMZUUGUWIUUFMZNZ
      UWIUWHUUDMZUJMMZDWCMZLZLZUXBUXLYRYQBCUWSUWTDYDFUXFUXDUWIYLYMUWHUUHAUUIUUB
      UWQUXKIWDZAUUKUUBUWQUXKUUPWDAUURUUBUWQUXKUUSWDUUTUVAUWRYTUXKUUCYTUWQUVBTZ
      TZUWRUUAUXKUUCUUAUWQUVCTZTZUXFSZUXDSZUWRUWOUXKUUCUWOUWPVBZTZUWRUWPUXKUUCU
      WOUWPVCZTZUWRUXIUXJVBZUWRUXIUXJVCZWEUXLUYBUWSUWICWOMZMZNZYLUWINZUWJYILZMZ
      YLBWOMZMZUWTNZUWGUYSYILZMZUWGYHMZUYSYHMZNZUWJYHMZUXTLZLUYRVUDUWGUYSNUWJUU
      LWCMZLLZUWLMZUXBUXLUXNVUAUXOVUFUYAVUKUXLUXQVUIUXSVUJUXTUXLUUGVUGUXPVUHUXL
      UUGYOVUGUXLYRYQBCDEFUUEYLYMGUUTAUVDUUBUWQUXKHWDZUYCAUUOUUBUWQUXKJWDZUVAUY
      EUVEUYGVEYLYMYHXEWGUXLUXPYLUWIYHLVUHUXLYRYQBCDEFUUEYLUWIGUUTVUOUYCVUPUVAU
      YEUVEUYMVEYLUWIYHXEWGWHUXLUXSUWHUWIYHLVUJUXLYRYQBCDEFUXRUWHUWIGUUTVUOUYCV
      UPUVAUYKUXRSUYMVEUWHUWIYHXEWGWIUXLUXNUWSUYQUYTLVUAUXLYRYQBCDEFUXFUYPUWSUX
      MYLUWHUWIGUUTVUOUYCVUPUVAUYHUYPSZUYEUYKUYNUXMSUYMWJUWSUYQUYTXEWGUXLUXOVUC
      UWTVUELVUFUXLYRYQBCVUBDEFUWTUXDUUEYLYMUWIGUUTVUOUYCVUPUVAUYEUVEUYGUYIVUBS
      ZUYMUYOWKVUCUWTVUEXEWGWLUXLUVFUULVULDYHYIUULWBMZVUDUYRUXTUWGUYSUWJUVIVUSS
      ZVULSZUXTSUWRUVQUXKAUVQUUBUWQUVRWMZTUWRUWGUVFRZUXKUUBVVCAUWQYLYMYRYQWPWNZ
      TUXLYLUWIYRYQUYEUYMWQUWRUWJUVFRZUXKUWQVVEUUCUWHUWIYRYQWPWRZTUXLVUDYLYLUXF
      LZUXEVHUWGUYSVUSLUXLVUCUWTVVGUXEUXLYRBVUBUXFYLUUTUYHVURVUOUYEWSZUYOWQUXLB
      CYLUWIUULUXFUXDVUSYLYMYRYQUVHUUTUVAUYHUYIUYEUYGUYEUYMVUTWTXAUXLUYRUXGUWIU
      WIUXDLZVHUYSUWJVUSLUXLUWSUYQUXGVVIUYNUXLYQCUYPUXDUWIUVAUYIVUQUYCUYMWSZWQU
      XLBCUWHUWIUULUXFUXDVUSYLUWIYRYQUVHUUTUVAUYHUYIUYEUYMUYKUYMVUTWTXAXBUXLVUN
      UWSVUCYLYLNUWHBWCMZLLZUYQUWTYMUWINUWICWCMZLLZUWLLZUXBUXLVUNVVLVVNNZUWLMVV
      OUXLVUMVVPUWLUXLBCYLUWIUWHUWIVVMUULVVKVUCUWTUXFUXDUWSUYQYLYMVULYRYQUVHUUT
      UVAUYHUYIUYEUYGUYEUYMVVKSZVVMSZVVAUYKUYMVVHUYOUYNVVJXCXDVVLVVNUWLXEXFUXLV
      VLUWSVVNUWTUWLUXLYRBVVKVUBUWSUXFYLUWHUUTUYHVURVUOUYEVVQUYKUYNXGUXLYQCVVMU
      YPUWTUXDYMUWIUVAUYIVUQUYCUYGVVRUYMUYOXHWIVFXIVFVGUWRUWKUXGUXEVHZVIUWLVVSV
      IUWMUXHVJUWRVVSUWGYEMUWJYEMDWBMZLZUWKUWRUWGUWJVUSLZVWAUWKXPVVSVWAUWKXPUWR
      UVFUULDYEYFVUSVVTUWGUWJUVIVUTVVTSZAUVMUUBUWQUVPWMVVDVVFXQUWRVWBVVSVWAUWKU
      WRBCUWHUWIUULUXFUXDVUSYLYMYRYQUVHUUTUVAUYHUYIUYDUYFUYJUYLVUTWTZXJXKVSUWRV
      VSVUGVUJVVTLZUWLUWRVWBVWEUWLXPVVSVWEUWLXPUWRUVFUULDYHYIVUSVVTUWGUWJUVIVUT
      VWCVVBVVDVVFXQUWRVWBVVSVWEUWLVWDXJXKVSUFUIUXGUXEUWKUWLVTWFWAVGVGUWEUWNUBK
      UAYRYQUWEUVTUWJYFLZUVTUWJYILZOZUEYQQUDYRQUVTUWGOZUWNUWDVWHUCUDUEYRYQUWAUW
      JOUWBVWFUWCVWGUWAUWJUVTYFXLUWAUWJUVTYIXLXMXNVWIVWHUWMUDUEYRYQVWIVWFUWKVWG
      UWLUVTUWGUWJYFXOUVTUWGUWJYIXOXMXRXSXNXTAYFUVFUVFVHZVIYIVWJVIUVSUWFVJAUVFU
      ULDYEYFUVIUVPYAAUVFUULDYHYIUVIUVRYAUBUCUVFUVFYFYIVTWFWAWHAUVKUVLYDYGOUVNU
      VOYDUUNYBVQAUVKUUOEYJOUVNJEUUNYBVQYC $.
  $}

  ${
    $d c d C $.  $d c d D $.  $d c d ph $.
    diagval.l $e |- L = ( C DiagFunc D ) $.
    diagval.c $e |- ( ph -> C e. Cat ) $.
    diagval.d $e |- ( ph -> D e. Cat ) $.
    $( Define the diagonal functor, which is the functor ` C --> ( D Func C ) `
       whose object part is ` x e. C |-> ( y e. D |-> x ) ` .  We can define
       this equationally as the currying of the first projection functor, and
       by expressing it this way we get a quick proof of functoriality.
       (Contributed by Mario Carneiro, 6-Jan-2017.)  (Revised by Mario
       Carneiro, 15-Jan-2017.) $)
    diagval $p |- ( ph -> L = ( <. C , D >. curryF ( C 1stF D ) ) ) $=
      ( vc vd cdiag co cop c1stf ccurf ccat cv cvv wceq wa oveq12d cmpo df-diag
      a1i simprl simprr opeq12d ovexd ovmpod eqtrid ) ADBCJKBCLZBCMKZNKZEAHIBCO
      OHPZIPZLZUMUNMKZNKZULJQJHIOOUQUARAHIUBUCAUMBRZUNCRZSSZUOUJUPUKNUTUMBUNCAU
      RUSUDZAURUSUEZUFUTUMBUNCMVAVBTTFGAUJUKNUGUHUI $.

    ${
      diagcl.q $e |- Q = ( D FuncCat C ) $.
      $( The diagonal functor is a functor from the base category to the
         functor category.  Another way of saying this is that the constant
         functor ` ( y e. D |-> X ) ` is a construction that is natural in
         ` X ` (and covariant).  (Contributed by Mario Carneiro, 7-Jan-2017.)
         (Revised by Mario Carneiro, 15-Jan-2017.) $)
      diagcl $p |- ( ph -> L e. ( C Func Q ) ) $=
        ( cop c1stf co ccurf cfunc diagval eqid cxpc 1stfcl curfcl eqeltrd ) AE
        BCJBCKLZMLZBDNLABCEFGHOABCDBUAUBUBPIGHABCUABCQLZUCPGHUAPRST $.
    $}

    diag11.a $e |- A = ( Base ` C ) $.
    diag11.c $e |- ( ph -> X e. A ) $.
    diag11.k $e |- K = ( ( 1st ` L ) ` X ) $.
    $( The constant functor of ` X ` is a functor.  (Contributed by Mario
       Carneiro, 6-Jan-2017.)  (Revised by Mario Carneiro, 15-Jan-2017.) $)
    diag1cl $p |- ( ph -> K e. ( D Func C ) ) $=
      ( c1st cfv cfunc co cfuc c2nd eqid fucbas wrel wbr relfunc diagcl sylancr
      wcel 1st2ndbr funcf1 ffvelcdmd eqeltrid ) AEGFNOZODCPQZMABUMGULABUMCDCRQZ
      ULFSOZKDCUNUNTZUAACUNPQZUBFUQUGULUOUQUCCUNUDACDUNFHIJUPUEFUQUHUFUILUJUK
      $.

    diag11.b $e |- B = ( Base ` D ) $.
    diag11.y $e |- ( ph -> Y e. B ) $.
    $( Value of the constant functor at an object.  (Contributed by Mario
       Carneiro, 7-Jan-2017.)  (Revised by Mario Carneiro, 15-Jan-2017.) $)
    diag11 $p |- ( ph -> ( ( 1st ` K ) ` Y ) = X ) $=
      ( c1st cfv eqid c1stf co ccurf diagval fveq2d fveq1d eqtrid 1stfcl curf11
      cop cxpc df-ov chom xpcbas opelxpd 1stf1 wcel op1stg syl2anc eqtrd 3eqtrd
      cxp wceq ) AIFRSZSIHDEUJDEUAUBZUCUBZRSZSZRSZSHIVERSZUBZHAIVDVIAFVHRAFHGRS
      ZSVHOAHVLVGAGVFRADEGJKLUDUEUFUGUEUFABCDEDVEVFVHHIVFTMKLADEVEDEUKUBZVMTZKL
      VETZUHPNVHTQUIAVKHIUJZRSZHAVKVPVJSVQHIVJULABCVBDEVEVPVMVMUMSZVNDEVMBCVNMP
      UNVRTKLVOAHIBCNQUOUPUGAHBUQICUQVQHVCNQHIBCURUSUTVA $.

    diag12.j $e |- J = ( Hom ` D ) $.
    diag12.i $e |- .1. = ( Id ` C ) $.
    diag12.z $e |- ( ph -> Z e. B ) $.
    diag12.f $e |- ( ph -> F e. ( Y J Z ) ) $.
    $( Value of the constant functor at a morphism.  (Contributed by Mario
       Carneiro, 6-Jan-2017.)  (Revised by Mario Carneiro, 15-Jan-2017.) $)
    diag12 $p |- ( ph -> ( ( Y ( 2nd ` K ) Z ) ` F ) = ( .1. ` X ) ) $=
      ( c2nd cfv co cop c1stf ccurf c1st diagval fveq2d fveq1d eqtrid eqid cxpc
      oveqd 1stfcl curf12 chom cres df-ov xpcbas opelxpd 1stf2 catidcl eleqtrrd
      cxp xpchom2 fvresd wcel wceq op1stg syl2anc 3eqtrd ) AGLMIUFUGZUHZUGGLMKD
      EUIDEUJUHZUKUHZULUGZUGZUFUGZUHZUGKFUGZGKLUIZKMUIZVTUFUGUHZUHZWFAGVSWEAVRW
      DLMAIWCUFAIKJULUGZUGWCSAKWKWBAJWAULADEJNOPUMUNUOUPUNUSUOABCDEFDVTWAGHWCKL
      MWAUQQOPADEVTDEURUHZWLUQZOPVTUQZUTTRWCUQUAUBUCUDUEVAAWJWFGUIZULWGWHWLVBUG
      ZUHZVCZUGZWOULUGZWFAWJWOWIUGWSWFGWIVDAWOWIWRABCVJDEVTWGWHWLWPWMDEWLBCWMQT
      VEWPUQZOPWNAKLBCRUAVFAKMBCRUDVFVGUOUPAWOWQULAWOKKDVBUGZUHZLMHUHZVJWQAWFGX
      CXDABDFXBKQXBUQZUCORVHZUEVFADEKMWLXBHWPKLBCWMQTXEUBRUARUDXAVKVIVLAWFXCVMG
      XDVMWTWFVNXFUEWFGXCXDVOVPVQVQ $.
  $}

  ${
    $d x B $.  $d x C $.  $d x D $.  $d x F $.  $d x H $.  $d x X $.  $d x Y $.
    $d x ph $.
    diag2.l $e |- L = ( C DiagFunc D ) $.
    diag2.a $e |- A = ( Base ` C ) $.
    diag2.b $e |- B = ( Base ` D ) $.
    diag2.h $e |- H = ( Hom ` C ) $.
    diag2.c $e |- ( ph -> C e. Cat ) $.
    diag2.d $e |- ( ph -> D e. Cat ) $.
    diag2.x $e |- ( ph -> X e. A ) $.
    diag2.y $e |- ( ph -> Y e. A ) $.
    diag2.f $e |- ( ph -> F e. ( X H Y ) ) $.
    $( Value of the diagonal functor at a morphism.  (Contributed by Mario
       Carneiro, 7-Jan-2017.) $)
    diag2 $p |- ( ph -> ( ( X ( 2nd ` L ) Y ) ` F ) = ( B X. { F } ) ) $=
      ( cfv vx c2nd co cop c1stf ccurf cv ccid cmpt csn cxp fveq2d oveqd fveq1d
      diagval eqid cxpc 1stfcl curf2 wcel wa c1st chom cres xpcbas ccat opelxpi
      adantr sylan 1stf2 df-ov simpr catidcl opelxpd xpchom2 fvresd eqtrid wceq
      eleqtrrd op1stg syl2an2r 3eqtrd mpteq2dva fconstmpt eqtr4di ) AFIJHUBTZUC
      ZTFIJDEUDDEUEUCZUFUCZUBTZUCZTZUACFUAUGZEUHTZTZIWMUDZJWMUDZWHUBTUCZUCZUIZC
      FUJUKZAFWGWKAWFWJIJAHWIUBADEHKOPUOULUMUNAUABCDEDWHWIGWNFWLIJWIUPLOPADEWHD
      EUQUCZXBUPZOPWHUPZURMNWNUPZQRSWLUPUSAWTUACFUIXAAUACWSFAWMCUTZVAZWSFWOVBWP
      WQXBVCTZUCZVDZUCZFWOUDZVBTZFXGWRXJFWOXGBCUKZDEWHWPWQXBXHXCDEXBBCXCLMVEXHU
      PZADVFUTXFOVHAEVFUTXFPVHZXDAIBUTZXFWPXNUTQIWMBCVGVIAJBUTZXFWQXNUTRJWMBCVG
      VIVJUMXGXKXLXJTXMFWOXJVKXGXLXIVBXGXLIJGUCZWMWMEVCTZUCZUKXIXGFWOXSYAAFXSUT
      ZXFSVHXGCEWNXTWMMXTUPZXEXPAXFVLZVMZVNXGDEJWMXBGXTXHIWMBCXCLMNYCAXQXFQVHYD
      AXRXFRVHYDXOVOVSVPVQAYBXFWOYAUTXMFVRSYEFWOXSYAVTWAWBWCUACFWDWEWB $.

    diag2cl.h $e |- N = ( D Nat C ) $.
    $( The diagonal functor at a morphism is a natural transformation between
       constant functors.  (Contributed by Mario Carneiro, 7-Jan-2017.) $)
    diag2cl $p |- ( ph ->
      ( B X. { F } ) e. ( ( ( 1st ` L ) ` X ) N ( ( 1st ` L ) ` Y ) ) ) $=
      ( c2nd cfv co csn cxp c1st diag2 cfuc eqid fuchom cfunc wrel wcel relfunc
      wbr diagcl 1st2ndbr sylancr funcf2 ffvelcdmd eqeltrrd ) AFJKHUBUCZUDZUCCF
      UEUFJHUGUCZUCKVEUCIUDZABCDEFGHJKLMNOPQRSTUHAJKGUDVFFVDABDEDUIUDZVEVCGIJKM
      OEDVGIVGUJZUAUKADVGULUDZUMHVIUNVEVCVIUPDVGUOADEVGHLPQVHUQHVIURUSRSUTTVAVB
      $.
  $}

  ${
    $d f u x y z C $.  $d f u x y z D $.  $d f u x y z ph $.  $d f x y Q $.
    curf2ndf.q $e |- Q = ( D FuncCat D ) $.
    curf2ndf.c $e |- ( ph -> C e. Cat ) $.
    curf2ndf.d $e |- ( ph -> D e. Cat ) $.
    $( As shown in ~ diagval , the currying of the first projection is the
       diagonal functor.  On the other hand, the currying of the second
       projection is ` x e. C |-> ( y e. D |-> y ) ` , which is a constant
       functor of the identity functor at ` D ` .  (Contributed by Mario
       Carneiro, 15-Jan-2017.) $)
    curf2ndf $p |- ( ph -> ( <. C , D >. curryF ( C 2ndF D ) ) =
      ( ( 1st ` ( Q DiagFunc C ) ) ` ( idFunc ` D ) ) ) $=
      ( vx vy vz vf cop co cfv c2nd cmpt wcel eqid ad2antrr adantr vu c2ndf cbs
      ccurf c1st cidfu cdiag cv wa chom ccid cmpo cid cres cxp cxpc xpcbas ccat
      df-ov opelxpi adantll 2ndf1 vex op2nd eqtrdi eqtrid mptresid eqtr4di wceq
      mpteq2dva simp-4r simplr opelxpd fveq1d catidcl ad3antrrr simpllr xpchom2
      2ndf2 simpr eleqtrrd fvresd fvex eqtrd 3impa fveq2 reseq2d mpompt opeq12d
      mpoeq3dva cfunc 2ndfcl idfuval 3eqtr4d fuccat fucbas idfucl diag11 eqtr4d
      curf1 syl wrel wbr relfunc curfcl 1st2ndbr sylancr funcf1 feqmptd diag1cl
      ccom idfu1st coeq2d fucid cvv wfn cidfn dffn2 sylib fcoi1 simplrl simplrr
      sylan oveqd 3eqtr4rd curf2 diag12 cnat fuchom simprl simprr 3impb funcfn2
      wf funcf2 fnov 1st2nd ) ABCLBCUBMZUDMZUENZYSONZLZCUFNZDBUGMZUENNZUENZUUEO
      NZLZYSUUEAYTUUFUUAUUGAHBUCNZHUHZYTNZPHUUIUUJUUFNZPYTUUFAHUUIUUKUULAUUJUUI
      QZUIZUUKUUCUULUUNICUCNZUUJIUHZYRUENZMZPZIJUUOUUOKUUPJUHZCUJNZMZUUJBUKNZNZ
      KUHZUUJUUPLZUUJUUTLZYRONZMZMZPZULZLUMUUOUNZUAUUOUUOUOUMUAUHZUVANZUNZPZLUU
      KUUCUUNUUSUVMUVLUVQUUNUUSIUUOUUPPUVMUUNIUUOUURUUPUUNUUPUUOQZUIZUURUVFUUQN
      ZUUPUUJUUPUUQUSUVSUVTUVFONUUPUVSUUIUUOUOZBCYRUVFBCUPMZUWBUJNZUWBRZBCUWBUU
      IUUOUWDUUIRZUUORZUQZUWCRZABURQZUUMUVRFSZACURQZUUMUVRGSZYRRZUUMUVRUVFUWAQZ
      AUUJUUPUUIUUOUTVAZVBUUJUUPHVCIVCVDVEVFVJIUUOVGVHUUNUVLIJUUOUUOUMUVBUNZULU
      VQUUNIJUUOUUOUVKUWPUUNUVRUUTUUOQZUVKUWPVIUVSUWQUIZUVKKUVBUVEPUWPUWRKUVBUV
      JUVEUWRUVEUVBQZUIZUVJUVDUVELZOUVFUVGUWCMZUNZNZUVEUWTUVJUXAUVINUXDUVDUVEUV
      IUSUWTUXAUVIUXCUWTUWABCYRUVFUVGUWBUWCUWDUWGUWHUVSUWIUWQUWSUWJSUVSUWKUWQUW
      SUWLSUWMUVSUWNUWQUWSUWOSUWTUUJUUTUUIUUOAUUMUVRUWQUWSVKZUVSUWQUWSVLZVMVSVN
      VFUWTUXDUXAONUVEUWTUXAUXBOUWTUXAUUJUUJBUJNZMZUVBUOUXBUWTUVDUVEUXHUVBUUNUV
      DUXHQUVRUWQUWSUUNUUIBUVCUXGUUJUWEUXGRZUVCRZAUWIUUMFTZAUUMVTZVOVPUWRUWSVTV
      MUWTBCUUJUUTUWBUXGUVAUWCUUJUUPUUIUUOUWDUWEUWFUXIUVARZUXEUUNUVRUWQUWSVQUXE
      UXFUWHVRWAWBUVDUVEUUJUVCWCKVCZVDVEWDVJKUVBVGVHWEWJIJUAUUOUUOUVPUWPUVNUUPU
      UTLZVIZUVOUVBUMUXPUVOUXOUVANUVBUVNUXOUVAWFUUPUUTUVAUSVHWGWHVHWIUUNIJUUIUU
      OBCUVCKCYRYSUVAUUKUUJYSRZUWEUXKAUWKUUMGTZAYRUWBCWKMQZUUMABCYRUWBUWDFGUWMW
      LZTUWFUXLUUKRUXMUXJWTUUNUAUUOCUVAUUCUUCRZUWFUXRUXMWMWNUUNCCWKMZUUIDBUUEUU
      DUUCUUJUUDRZADURQZUUMACCDEGGWOZTUXKCCDEWPZAUUCUYBQZUUMAUWKUYGGCUUCUYAWQXA
      ZTUUERZUWEUXLWRWSVJAHUUIUYBYTAUUIUYBBDYTUUAUWEUYFABDWKMZXBZYSUYJQZYTUUAUY
      JXCZBDXDZABCDCYRYSUXQEFGUXTXEZYSUYJXFXGZXHXIAHUUIUYBUUFAUUIUYBBDUUFUUGUWE
      UYFAUYKUUEUYJQZUUFUUGUYJXCZUYNAUYBDBUUEUUDUUCUYCUYEFUYFUYHUYIXJZUUEUYJXFX
      GZXHXIWNAHIUUIUUIUUJUUPUUAMZULZHIUUIUUIUUJUUPUUGMZULZUUAUUGAHIUUIUUIVUAVU
      CAUUMUUPUUIQZVUAVUCVIAUUMVUEUIZUIZKUUJUUPUXGMZUVEVUANZPKVUHUVEVUCNZPVUAVU
      CVUGKVUHVUIVUJVUGUVEVUHQZUIZJUUOUVEUUTCUKNZNZUVGUXOUVHMZMZPZUUCDUKNZNZVUI
      VUJVULVUMUUCUENZXKVUMUVMXKZVUSVUQVULVUTUVMVUMVULUUOCUUCUYAUWFAUWKVUFVUKGS
      ZXLXMVULCCDVUMUUCVUREVURRZVUMRZAUYGVUFVUKUYHSZXNVULVUMJUUOVUNPVVAVUQVULJU
      UOXOVUMVULVUMUUOXPZUUOXOVUMYNZVULUWKVVFVVBUUOCVUMUWFVVDXQXAUUOVUMXRXSZXIV
      ULVVGVVAVUMVIVVHUUOXOVUMXTXAVULJUUOVUPVUNVULUWQUIZVUPUVEVUNOUVGUXOUWCMZUN
      ZMZVUNVVIVUOVVKUVEVUNVVIUWABCYRUVGUXOUWBUWCUWDUWGUWHVULUWIUWQAUWIVUFVUKFS
      ZTVULUWKUWQVVBTZUWMVULUUMUWQUVGUWAQAUUMVUEVUKYAZUUJUUTUUIUUOUTYCVULVUEUWQ
      UXOUWAQAUUMVUEVUKYBZUUPUUTUUIUUOUTYCVSYDVVIVVLUVEVUNLZONZVUNVVIVVLVVQVVKN
      VVRUVEVUNVVKUSVVIVVQVVJOVVIVVQVUHUUTUUTUVAMZUOVVJVVIUVEVUNVUHVVSVUGVUKUWQ
      VLVVIUUOCVUMUVAUUTUWFUXMVVDVVNVULUWQVTZVOVMVVIBCUUPUUTUWBUXGUVAUWCUUJUUTU
      UIUUOUWDUWEUWFUXIUXMVULUUMUWQVVOTVVTVULVUEUWQVVPTVVTUWHVRWAWBVFUVEVUNUXNU
      UTVUMWCVDVEWDVJYEYEVULJUUIUUOBCCYRYSUXGVUMUVEVUIUUJUUPUXQUWEVVMVVBAUXSVUF
      VUKUXTSUWFUXIVVDVVOVVPVUGVUKVTZVUIRYFVULUYBUUIDBVURUVEUXGUUEUUDUUCUUJUUPU
      YCAUYDVUFVUKUYESVVMUYFVVEUYIUWEVVOUXIVVCVVPVWAYGWNVJVUGKVUHUUKUUPYTNCCYHM
      ZMVUAVUGUUIBDYTUUAUXGVWBUUJUUPUWEUXICCDVWBEVWBRYIZAUYMVUFUYPTAUUMVUEYJZAU
      UMVUEYKZYOXIVUGKVUHUULUUPUUFNVWBMVUCVUGUUIBDUUFUUGUXGVWBUUJUUPUWEUXIVWCAU
      YRVUFUYTTVWDVWEYOXIWNYLWJAUUAUUIUUIUOZXPUUAVUBVIAUUIBDYTUUAUWEUYPYMHIUUIU
      UIUUAYPXSAUUGVWFXPUUGVUDVIAUUIBDUUFUUGUWEUYTYMHIUUIUUIUUGYPXSWNWIAUYKUYLY
      SUUBVIUYNUYOYSUYJYQXGAUYKUYQUUEUUHVIUYNUYSUUEUYJYQXGWN $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Hom functor
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c HomF $.
  $c Yon $.

  $( Extend class notation with the Hom functor. $)
  chof $a class HomF $.

  $( Extend class notation with the Yoneda embedding. $)
  cyon $a class Yon $.

  ${
    $d b c f g h x y B $.  $d f g h F $.  $d f g h G $.  $d b c f g h x y ph $.
    $d b c f g h x y C $.  $d b c f g h x y H $.  $d h K $.  $d f g h x y W $.
    $d b c f g h x y .x. $.  $d f g h x y X $.  $d f g h x y Y $.
    $d f g h x y Z $.
    $( Define the Hom functor, which is a bifunctor (a functor of two
       arguments), contravariant in the first argument and covariant in the
       second, from ` ( oppCat `` C ) X. C ` to ` SetCat ` , whose object part
       is the hom-function ` Hom ` , and with morphism part given by pre- and
       post-composition.  (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    df-hof $a |- HomF = ( c e. Cat |-> <. ( Homf ` c ) , [_ ( Base ` c ) / b ]_
       ( x e. ( b X. b ) , y e. ( b X. b ) |->
         ( f e. ( ( 1st ` y ) ( Hom ` c ) ( 1st ` x ) ) ,
           g e. ( ( 2nd ` x ) ( Hom ` c ) ( 2nd ` y ) ) |->
           ( h e. ( ( Hom ` c ) ` x ) |->
             ( ( g ( x ( comp ` c ) ( 2nd ` y ) ) h ) ( <. ( 1st ` y ) ,
               ( 1st ` x ) >. ( comp ` c ) ( 2nd ` y ) ) f ) ) ) ) >. ) $.

    $( Define the Yoneda embedding, which is the currying of the (opposite) Hom
       functor.  (Contributed by Mario Carneiro, 11-Jan-2017.) $)
    df-yon $a |- Yon = ( c e. Cat |->
      ( <. c , ( oppCat ` c ) >. curryF ( HomF ` ( oppCat ` c ) ) ) ) $.

    hofval.m $e |- M = ( HomF ` C ) $.
    hofval.c $e |- ( ph -> C e. Cat ) $.
    ${
      hofval.b $e |- B = ( Base ` C ) $.
      hofval.h $e |- H = ( Hom ` C ) $.
      hofval.o $e |- .x. = ( comp ` C ) $.
      $( Value of the Hom functor, which is a bifunctor (a functor of two
         arguments), contravariant in the first argument and covariant in the
         second, from ` ( oppCat `` C ) X. C ` to ` SetCat ` , whose object
         part is the hom-function ` Hom ` , and with morphism part given by
         pre- and post-composition.  (Contributed by Mario Carneiro,
         15-Jan-2017.) $)
      hofval $p |- ( ph -> M = <. ( Homf ` C ) ,
         ( x e. ( B X. B ) , y e. ( B X. B ) |->
           ( f e. ( ( 1st ` y ) H ( 1st ` x ) ) ,
             g e. ( ( 2nd ` x ) H ( 2nd ` y ) ) |->
             ( h e. ( H ` x ) |->
               ( ( g ( x .x. ( 2nd ` y ) ) h ) ( <. ( 1st ` y ) ,
                 ( 1st ` x ) >. .x. ( 2nd ` y ) ) f ) ) ) ) >. ) $=
        ( cfv cv co oveqd vc vb chof chomf cxp c1st c2nd cop cmpt cmpo cbs chom
        cco csb ccat cvv df-hof wceq simpr fveq2d eqtr4di sqxpeqd simplr fveq1d
        fvexd eqidd oveq123d mpteq12dv mpoeq123dv csbied2 opeq12d wcel opex a1i
        wa fvmptd2 eqtrid ) AKEUCQEUDQZBCDDUEZVSGHCRZUFQZBRZUFQZJSZWBUGQZVTUGQZ
        JSZIWBJQZHRZIRZWBWFFSZSZGRZWAWCUHZWFFSZSZUIZUJZUJZUHZLAUAEUARZUDQZUBXAU
        KQZBCUBRZXDUEZXEGHWAWCXAULQZSZWEWFXFSZIWBXFQZWIWJWBWFXAUMQZSZSZWMWNWFXJ
        SZSZUIZUJZUJZUNZUHWTUOUCUPBCGHIUBUAUQAXAEURZVOZXBVRXRWSXTXAEUDAXSUSZUTX
        TUBXCDXQWSUPXTXAUKVEXTXCEUKQDXTXAEUKYAUTNVAXTXDDURZVOZBCXEXEXPVSVSWRYCX
        DDXTYBUSVBZYDYCGHXGXHXOWDWGWQYCXFJWAWCYCXFEULQJYCXAEULAXSYBVCZUTOVAZTYC
        XFJWEWFYFTYCIXIXNWHWPYCWBXFJYFVDYCXLWLWMWMXMWOYCXJFWNWFYCXJEUMQFYCXAEUM
        YEUTPVAZTYCXKWKWIWJYCXJFWBWFYGTTYCWMVFVGVHVIVIVJVKMWTUPVLAVRWSVMVNVPVQ
        $.
    $}

    $( The object part of the Hom functor is the ` Homf ` operation, which is
       just a functionalized version of ` Hom ` .  That is, it is a two
       argument function, which maps ` X , Y ` to the set of morphisms from
       ` X ` to ` Y ` .  (Contributed by Mario Carneiro, 15-Jan-2017.) $)
    hof1fval $p |- ( ph -> ( 1st ` M ) = ( Homf ` C ) ) $=
      ( vx vy vf vg vh chomf cfv cbs cv c1st co c2nd cop cmpo eqid cxp chom cco
      cmpt wceq hofval fvex xpex mpoex op1std syl ) ACBKLZFGBMLZUMUAZUNHIGNZOLZ
      FNZOLZBUBLZPUQQLUOQLZUSPJUQUSLINJNUQUTBUCLZPPHNUPURRUTVAPPUDSZSZRUECOLULU
      EAFGUMBVAHIJUSCDEUMTUSTVATUFULVCCBKUGFGUNUNVBUMUMBMUGZVDUHZVEUIUJUK $.

    hof1.b $e |- B = ( Base ` C ) $.
    hof1.h $e |- H = ( Hom ` C ) $.
    hof1.x $e |- ( ph -> X e. B ) $.
    hof1.y $e |- ( ph -> Y e. B ) $.
    $( The object part of the Hom functor maps ` X , Y ` to the set of
       morphisms from ` X ` to ` Y ` .  (Contributed by Mario Carneiro,
       15-Jan-2017.) $)
    hof1 $p |- ( ph -> ( X ( 1st ` M ) Y ) = ( X H Y ) ) $=
      ( c1st cfv co chomf hof1fval oveqd eqid homfval eqtrd ) AFGENOZPFGCQOZPFG
      DPAUCUDFGACEHIRSABCUDDFGUDTJKLMUAUB $.

    hof2.z $e |- ( ph -> Z e. B ) $.
    hof2.w $e |- ( ph -> W e. B ) $.
    hof2.o $e |- .x. = ( comp ` C ) $.
    $( The morphism part of the Hom functor, for morphisms
       ` <. f , g >. : <. X , Y >. --> <. Z , W >. ` (which since the first
       argument is contravariant means morphisms ` f : Z --> X ` and
       ` g : Y --> W ` ), yields a function (a morphism of ` SetCat ` ) mapping
       ` h : X --> Y ` to ` g o. h o. f : Z --> W ` .  (Contributed by Mario
       Carneiro, 15-Jan-2017.) $)
    hof2fval $p |- ( ph -> ( <. X , Y >. ( 2nd ` M ) <. Z , W >. ) =
      ( f e. ( Z H X ) , g e. ( Y H W ) |-> ( h e. ( X H Y ) |->
        ( ( g ( <. X , Y >. .x. W ) h ) ( <. Z , X >. .x. W ) f ) ) ) ) $=
      ( vx vy cop cxp cv c1st cfv c2nd cmpt cmpo cvv chomf wceq hofval fvex cbs
      co fvexi xpex mpoex op2ndd syl wa simprr fveq2d wcel op1stg syl2anc eqtrd
      adantr simprl oveq12d op2ndg df-ov eqtr4di oveqd eqidd oveq123d mpteq12dv
      opeq12d mpoeq123dv opelxpd ovex a1i ovmpod ) AUCUDKLUEZMJUEZBBUFZWJEFUDUG
      ZUHUIZUCUGZUHUIZHUSZWMUJUIZWKUJUIZHUSZGWMHUIZFUGZGUGZWMWQDUSZUSZEUGZWLWNU
      EZWQDUSZUSZUKZULZEFMKHUSZLJHUSZGKLHUSZWTXAWHJDUSZUSZXDMKUEZJDUSZUSZUKZULZ
      IUJUIZUMAICUNUIZUCUDWJWJXIULZUEUOXTYBUOAUCUDBCDEFGHINOPQUBUPYAYBICUNUQUCU
      DWJWJXIBBBCURPUTZYCVAZYDVBVCVDAWMWHUOZWKWIUOZVEZVEZEFWOWRXHXJXKXRYHWLMWNK
      HYHWLWIUHUIZMYHWKWIUHAYEYFVFZVGAYIMUOZYGAMBVHZJBVHZYKTUAMJBBVIVJVLVKZYHWN
      WHUHUIZKYHWMWHUHAYEYFVMZVGAYOKUOZYGAKBVHZLBVHZYQRSKLBBVIVJVLVKZVNYHWPLWQJ
      HYHWPWHUJUIZLYHWMWHUJYPVGAUUALUOZYGAYRYSUUBRSKLBBVOVJVLVKYHWQWIUJUIZJYHWK
      WIUJYJVGAUUCJUOZYGAYLYMUUDTUAMJBBVOVJVLVKZVNYHGWSXGXLXQYHWSWHHUIXLYHWMWHH
      YPVGKLHVPVQYHXCXNXDXDXFXPYHXEXOWQJDYHWLMWNKYNYTWBUUEVNYHXBXMWTXAYHWMWHWQJ
      DYPUUEVNVRYHXDVSVTWAWCAKLBBRSWDAMJBBTUAWDXSUMVHAEFXJXKXRMKHWELJHWEVBWFWG
      $.

    hof2.f $e |- ( ph -> F e. ( Z H X ) ) $.
    hof2.g $e |- ( ph -> G e. ( Y H W ) ) $.
    $( The morphism part of the Hom functor, for morphisms
       ` <. f , g >. : <. X , Y >. --> <. Z , W >. ` (which since the first
       argument is contravariant means morphisms ` f : Z --> X ` and
       ` g : Y --> W ` ), yields a function (a morphism of ` SetCat ` ) mapping
       ` h : X --> Y ` to ` g o. h o. f : Z --> W ` .  (Contributed by Mario
       Carneiro, 15-Jan-2017.) $)
    hof2val $p |- ( ph -> ( F ( <. X , Y >. ( 2nd ` M ) <. Z , W >. ) G ) =
      ( h e. ( X H Y ) |->
        ( ( G ( <. X , Y >. .x. W ) h ) ( <. Z , X >. .x. W ) F ) ) ) $=
      ( vf vg co cv cop cmpt c2nd cfv cvv hof2fval wceq wa wcel simplrr simplrl
      oveq1d oveq12d mpteq2dva ovex mptex a1i ovmpod ) AUEUFFGMKHUGLJHUGEKLHUGZ
      UFUHZEUHZKLUIZJDUGZUGZUEUHZMKUIJDUGZUGZUJEVGGVIVKUGZFVNUGZUJZVJMJUIIUKULU
      GUMABCDUEUFEHIJKLMNOPQRSTUAUBUNAVMFUOZVHGUOZUPUPZEVGVOVQWAVIVGUQZUPZVLVPV
      MFVNWCVHGVIVKAVSVTWBURUTAVSVTWBUSVAVBUCUDVRUMUQAEVGVQKLHVCVDVEVF $.

    hof2.k $e |- ( ph -> K e. ( X H Y ) ) $.
    $( The morphism part of the Hom functor, for morphisms
       ` <. f , g >. : <. X , Y >. --> <. Z , W >. ` (which since the first
       argument is contravariant means morphisms ` f : Z --> X ` and
       ` g : Y --> W ` ), yields a function (a morphism of ` SetCat ` ) mapping
       ` h : X --> Y ` to ` g o. h o. f : Z --> W ` .  (Contributed by Mario
       Carneiro, 15-Jan-2017.) $)
    hof2 $p |- ( ph ->
      ( ( F ( <. X , Y >. ( 2nd ` M ) <. Z , W >. ) G ) ` K ) =
        ( ( G ( <. X , Y >. .x. W ) K ) ( <. Z , X >. .x. W ) F ) ) $=
      ( vh cv cop co c2nd cfv cvv hof2val wceq simpr oveq2d oveq1d ovexd fvmptd
      wa ) AUFHFUFUGZKLUHZJDUIZUIZEMKUHJDUIZUIFHVCUIZEVEUIKLGUIEFVBMJUHIUJUKUIU
      IULABCDUFEFGIJKLMNOPQRSTUAUBUCUDUMAVAHUNZUTZVDVFEVEVHVAHFVCAVGUOUPUQUEAVF
      EVEURUS $.
  $}

  ${
    $d f g B $.  $d f g x y z D $.  $d f g H $.  $d f g K $.  $d f g x y z M $.
    $d f g h x y z C $.  $d f g L $.  $d f g x y z O $.  $d f g h x y z ph $.
    $d f g P $.  $d f g Q $.  $d f g S $.  $d f g T $.  $d f g W $.
    $d f g X $.  $d f g Y $.  $d f g Z $.
    hofcl.m $e |- M = ( HomF ` C ) $.
    hofcl.o $e |- O = ( oppCat ` C ) $.
    hofcl.d $e |- D = ( SetCat ` U ) $.
    hofcl.c $e |- ( ph -> C e. Cat ) $.
    hofcl.u $e |- ( ph -> U e. V ) $.
    hofcl.h $e |- ( ph -> ran ( Homf ` C ) C_ U ) $.
    ${
      hofcllem.b $e |- B = ( Base ` C ) $.
      hofcllem.h $e |- H = ( Hom ` C ) $.
      hofcllem.x $e |- ( ph -> X e. B ) $.
      hofcllem.y $e |- ( ph -> Y e. B ) $.
      hofcllem.z $e |- ( ph -> Z e. B ) $.
      hofcllem.w $e |- ( ph -> W e. B ) $.
      hofcllem.s $e |- ( ph -> S e. B ) $.
      hofcllem.t $e |- ( ph -> T e. B ) $.
      hofcllem.m $e |- ( ph -> K e. ( Z H X ) ) $.
      hofcllem.n $e |- ( ph -> L e. ( Y H W ) ) $.
      hofcllem.p $e |- ( ph -> P e. ( S H Z ) ) $.
      hofcllem.q $e |- ( ph -> Q e. ( W H T ) ) $.
      $( Lemma for ~ hofcl .  (Contributed by Mario Carneiro, 15-Jan-2017.) $)
      hofcllem $p |- ( ph ->
        ( ( K ( <. S , Z >. ( comp ` C ) X ) P )
          ( <. X , Y >. ( 2nd ` M ) <. S , T >. )
          ( Q ( <. Y , W >. ( comp ` C ) T ) L ) ) =
        ( ( P ( <. Z , W >. ( 2nd ` M ) <. S , T >. ) Q )
          ( <. ( X H Y ) , ( Z H W ) >. ( comp ` D ) ( S H T ) )
          ( K ( <. X , Y >. ( 2nd ` M ) <. Z , W >. ) L ) ) ) $=
        ( vf vg co cop cco cfv cv cmpt c2nd wcel eqid ccat adantr simpr catcocl
        catass oveq1d eqtrd eqtr3d mpteq2dva hof2val ccom oveq12d chomf homfval
        cxp wfn crn wss homffn a1i df-f sylanbrc fovcdmd eqeltrrd fmpttd setcco
        wa wf eqidd wceq oveq2 fmptco 3eqtrd 3eqtr4d ) AURQRJUTZFLRPVAHCVBVCZUT
        UTZURVDZQRVAZHXDUTUTZKEGSVAZQXDUTUTZGQVAHXDUTUTZVEURXCFLXFXGPXDUTUTZKSQ
        VAZPXDUTUTZSPVAZHXDUTZUTZEXIHXDUTZUTZVEZXJXEXGGHVAZMVFVCZUTUTEFXOYAYBUT
        UTZKLXGXOYBUTUTZXCSPJUTZVAGHJUTZDVBVCZUTZUTZAURXCXKXSAXFXCVGZWOZXHKXMHX
        DUTZUTZEXRUTXKXSYKBCXDEKJXHHGSQUFUGXDVHZACVIVGZYJUCVJZAGBVGZYJULVJASBVG
        ZYJUJVJZAQBVGYJUHVJZAEGSJUTVGZYJUPVJAKSQJUTVGYJUNVJZAHBVGZYJUMVJZYKBCXD
        XFXEJQRHUFUGYNYPYTARBVGYJUIVJZUUDAYJVKZAXERHJUTVGYJABCXDLFJRPHUFUGYNUCU
        IUKUMUOUQVLZVJVLVMYKYMXQEXRYKYMFXLQPVAHXDUTUTZKYLUTXQYKXHUUHKYLYKBCXDXF
        LJFHQRPUFUGYNYPYTUUEAPBVGZYJUKVJZUUFALRPJUTVGYJUOVJZUUDAFPHJUTVGZYJUQVJ
        ZVMVNYKBCXDKXLJFHSQPUFUGYNYPYSYTUUJUUBYKBCXDXFLJQRPUFUGYNYPYTUUEUUJUUFU
        UKVLZUUDUUMVMVOVNVPVQABCXDURXJXEJMHQRGTUCUFUGUHUIULUMYNABCXDEKJGSQUFUGY
        NUCULUJUHUPUNVLUUGVRAYIUSYEFUSVDZXPUTZEXRUTZVEZURXCXNVEZYHUTUURUUSVSXTA
        YCUURYDUUSYHABCXDUSEFJMHSPGTUCUFUGUJUKULUMYNUPUQVRABCXDURKLJMPQRSTUCUFU
        GUHUIUJUKYNUNUOVRVTADYGIUUSUUROXCYEYFUBUDYGVHAQRCWAVCZUTXCIABCUUTJQRUUT
        VHZUFUGUHUIWBAQRIBBUUTAUUTBBWCZWDZUUTWEIWFUVBIUUTWPUVCABCUUTUVAUFWGWHUE
        UVBIUUTWIWJZUHUIWKWLASPUUTUTYEIABCUUTJSPUVAUFUGUJUKWBASPIBBUUTUVDUJUKWK
        WLAGHUUTUTYFIABCUUTJGHUVAUFUGULUMWBAGHIBBUUTUVDULUMWKWLAURXCXNYEYKBCXDK
        XLJSQPUFUGYNYPYSYTUUJUUBUUNVLZWMAUSYEUUQYFAUUOYEVGZWOZBCXDEUUPJGSHUFUGY
        NAYOUVFUCVJZAYQUVFULVJAYRUVFUJVJZAUUCUVFUMVJZAUUAUVFUPVJUVGBCXDUUOFJSPH
        UFUGYNUVHUVIAUUIUVFUKVJUVJAUVFVKAUULUVFUQVJVLVLWMWNAURUSXCYEXNUUQXSUUSU
        URUVEAUUSWQAUURWQUUOXNWRUUPXQEXRUUOXNFXPWSVNWTXAXB $.
    $}

    $( Closure of the Hom functor.  Note that the codomain is the category
       ` SetCat `` U ` for any universe ` U ` which contains each Hom-set.
       This corresponds to the assertion that ` C ` be locally small (with
       respect to ` U ` ).  (Contributed by Mario Carneiro, 15-Jan-2017.) $)
    hofcl $p |- ( ph -> M e. ( ( O Xc. C ) Func D ) ) $=
      ( vf cfv cop co eqid syl wcel vx vy vg vh vz chomf c2nd cxpc cfunc cbs cv
      cxp c1st chom cco cmpt cmpo hofval wceq fvex xpex mpoex op2ndd opeq2d wbr
      eqtr4d ccid oppcbas xpcbas ccat oppccat xpccat setccat wfn crn wss homffn
      a1i df-f sylanbrc setcbas feq3d mpbid ovex fnmpoi fneq1d mpbiri ad3antrrr
      wf wa wral simplrr xp1st adantr simplrl xp2nd 1st2nd2 oveq1d oveqd fveq2d
      eqtr4di eleq2d biimpa catcocl eqeltrd eleqtrrd ad2antrr homfval ffvelcdmd
      df-ov fmpttd 3eqtr4d eqeltrrd elsetchom oveq12d ralrimivva fmpo sylib cvv
      mpbird ovmpt4g mp3an3 sylan9eq xpchom oppchom eqtrdi adantl eqtrd catidcl
      cid cres opeq1d 3eqtrd fveq12d 3ad2ant1 eleqtrd eleqtrdi opeq12d oveq123d
      w3a simprl simprr xpeq1i feq12d catlid mpteq2dva hof2val eqtr3id mptresid
      simpr catrid reseq2d oppcid fveq1d ffvelcdmda setcid simp21 simp22 simp23
      xpcid simp3l simp3r hofcllem xpcco2 oppcco isfuncd df-br ) AEBUFOZEUGOZPZ
      FBUHQZCUIQZAEUVHUAUBBUJOZUVMULZUVNNUCUBUKZUMOZUAUKZUMOZBUNOZQZUVQUGOZUVOU
      GOZUVSQZUDUVQUVSOZUCUKZUDUKZUVQUWBBUOOZQZQZNUKZUVPUVRPUWBUWGQQZUPZUQZUQZP
      ZUVJAUAUBUVMBUWGNUCUDUVSEHKUVMRZUVSRZUWGRZURZAUVIUWNUVHAEUWOUSUVIUWNUSUWS
      UVHUWNEBUFUTUAUBUVNUVNUWMUVMUVMBUJUTZUWTVAZUXAVBVCSZVDVFAUVHUVIUVLVEUVJUV
      LTAUAUBUEUVNCUJOZUVKUVKUOOZUVKVGOZNUCCUVHUVIUVKUNOZCVGOZCUNOZCUOOZFBUVKUV
      MUVMUVKRZUVMBFIUWPVHZUWPVIZUXCRUXFRZUXHRZUXERZUXGRZUXDRZUXIRAFBUVKUXJABVJ
      TZFVJTZKBFIVKSZKVLADGTZCVJTLCDGJVMSAUVNDUVHWIZUVNUXCUVHWIAUVHUVNVNZUVHVOD
      VPZUYBUYCAUVMBUVHUVHRZUWPVQVRMUVNDUVHVSVTZADUXCUVHUVNACDGJLWAWBWCAUVIUVNU
      VNULZVNUWNUYGVNUAUBUVNUVNUWMUWNUWNRZNUCUVTUWCUWLUVPUVRUVSWDUWAUWBUVSWDVBZ
      WEAUYGUVIUWNUXBWFWGAUVQUVNTZUVOUVNTZWJZWJZUVQUVOUXFQZUVQUVHOZUVOUVHOZUXHQ
      ZUVQUVOUVIQZWIUVTUWCULZUYQUWMWIZUYMUWLUYQTZUCUWCWKNUVTWKUYTUYMVUANUCUVTUW
      CUYMUWJUVTTZUWEUWCTZWJZWJZUWLUWDUVOUVSOZUXHQZUYQVUEUWLVUGTUWDVUFUWLWIVUEU
      DUWDUWKVUFVUEUWFUWDTZWJZUWKUVPUWBUVSQZVUFVUIUVMBUWGUWJUWIUVSUVPUVRUWBUWPU
      WQUWRAUXRUYLVUDVUHKWHZVUEUVPUVMTZVUHVUEUYKVULAUYJUYKVUDWLZUVOUVMUVMWMZSZW
      NVUEUVRUVMTZVUHVUEUYJVUPAUYJUYKVUDWOZUVQUVMUVMWMZSZWNZVUEUWBUVMTZVUHVUEUY
      KVVAVUMUVOUVMUVMWPZSZWNZUYMVUBVUCVUHWOVUIUWIUWEUWFUVRUWAPZUWBUWGQZQUVRUWB
      UVSQVUIUWHVVFUWEUWFVUIUVQVVEUWBUWGVUEUVQVVEUSZVUHVUEUYJVVGVUQUVQUVMUVMWQZ
      SZWNWRWSVUIUVMBUWGUWFUWEUVSUVRUWAUWBUWPUWQUWRVUKVUTVUEUWAUVMTZVUHVUEUYJVV
      JVUQUVQUVMUVMWPZSZWNVVDVUEVUHUWFUVRUWAUVSQZTVUEUWDVVMUWFVUEUWDVVEUVSOVVMV
      UEUVQVVEUVSVVIWTUVRUWAUVSXJXAZXBXCUYMVUBVUCVUHWLXDXEXDVUEVUFVUJUSVUHVUEVU
      FUVPUWBPZUVSOVUJVUEUVOVVOUVSVUEUYKUVOVVOUSZVUMUVOUVMUVMWQZSZWTUVPUWBUVSXJ
      XAZWNXFXKVUECDUWLUXHGUWDVUFJAUYAUYLVUDLXGUXNVUEUYOUWDDVUEUVRUWAUVHQZVVMUY
      OUWDVUEUVMBUVHUVSUVRUWAUYEUWPUWQVUSVVLXHVUEUYOVVEUVHOZVVTVUEUVQVVEUVHVVIW
      TUVRUWAUVHXJZXAVVNXLZVUEUVNDUVQUVHAUYBUYLVUDUYFXGZVUQXIXMVUEUYPVUFDVUEUVP
      UWBUVHQZVUJUYPVUFVUEUVMBUVHUVSUVPUWBUYEUWPUWQVUOVVCXHVUEUYPVVOUVHOZVWEVUE
      UVOVVOUVHVVRWTUVPUWBUVHXJZXAVVSXLZVUEUVNDUVOUVHVWDVUMXIXMXNXTVUEUYOUWDUYP
      VUFUXHVWCVWHXOXFXPNUCUVTUWCUWLUYQUWMUWMRXQXRUYMUYNUYSUYQUYRUWMAUYLUYRUVQU
      VOUWNQZUWMAUVIUWNUVQUVOUXBWSUYJUYKUWMXSTVWIUWMUSUYIUAUBUVNUVNUWMUWNXSUYHY
      AYBYCUYMUYNUVRUVPFUNOZQZUWCULZUYSUYMUVNFBUVKVWJUVSUXFUVQUVOUXJUXLVWJRZUWQ
      UXMAUYJUYKUUAAUYJUYKUUBYDVWKUVTUWCBUVSFUVRUVPUWQIYEZUUCYFUUDXTAUYJWJZUVRB
      VGOZOZUWAVWPOZPZVVEVVEUVIQZOZYJUYOYKZUVQUXEOZUVQUVQUVIQZOUYOUXGOVWONVVMVW
      RUWJVVEUWAUWGQQZVWQUVRUVRPUWAUWGQZQZUPZNVVMUWJUPZVXAVXBVWONVVMVXGUWJVWOUW
      JVVMTZWJZVXGUWJVWQVXFQUWJVXKVXEUWJVWQVXFVXKUVMBUWGVWPUWJUVSUVRUWAUWPUWQVW
      PRZAUXRUYJVXJKXGZVWOVUPVXJUYJVUPAVURYGZWNZUWRVWOVVJVXJUYJVVJAVVKYGZWNZVWO
      VXJUUJZUUEWRVXKUVMBUWGVWPUWJUVSUVRUWAUWPUWQVXLVXMVXOUWRVXQVXRUUKYHUUFVWOV
      XAVWQVWRVWTQVXHVWQVWRVWTXJVWOUVMBUWGNVWQVWRUVSEUWAUVRUWAUVRHAUXRUYJKWNZUW
      PUWQVXNVXPVXNVXPUWRVWOUVMBVWPUVSUVRUWPUWQVXLVXSVXNYIVWOUVMBVWPUVSUWAUWPUW
      QVXLVXSVXPYIUUGUUHVWOVXBYJVVMYKVXIVWOUYOVVMYJVWOUYOVVTVVMVWOUYOVWAVVTVWOU
      VQVVEUVHUYJVVGAVVHYGZWTVWBXAVWOUVMBUVHUVSUVRUWAUYEUWPUWQVXNVXPXHYHUULNVVM
      UUIYFXLVWOVXCVWSVXDVWTVWOUVQVVEUVQVVEUVIVXTVXTXOVWOVXCVVEUXEOUVRFVGOZOZVW
      RPVWSVWOUVQVVEUXEVXTWTVWOFBUVRUWAUVKUXEVYAVWPUVMUVMUXJAUXSUYJUXTWNVXSUXKU
      WPVYARVXLUXOVXNVXPUUTVWOVYBVWQVWRVWOUVRVYAVWPVWOUXRVYAVWPUSVXSVWPBFIVXLUU
      MSUUNYLYMYNVWOCDUXGGUYOJUXPAUYAUYJLWNAUVNDUVQUVHUYFUUOUUPXLAUYJUYKUEUKZUV
      NTZYTZUWJUYNTZUWEUVOVYCUXFQZTZWJZYTZUWJUMOZUWEUMOZVYCUMOZUVPPUVRUWGQQZUWE
      UGOZUWJUGOZUWAUWBPVYCUGOZUWGQQZVVEVYMVYQPZUVIQZQZVYLVYOVVOVYSUVIQZQZVYKVY
      PVVEVVOUVIQZQZVVMVUJPZVYMVYQUVSQZUXIQZQUWEUWJUVQUVOPZVYCUXDQZQZUVQVYCUVIQ
      ZOZUWEUVOVYCUVIQZOZUWJUYROZUYOUYPPZVYCUVHOZUXIQZQVYJUVMBCVYLVYOVYMVYQDUVS
      VYKVYPEFGUWBUVRUWAUVPHIJAVYEUXRVYIKYOAVYEUYAVYILYOAVYEUYDVYIMYOUWPUWQVYJU
      YJVUPAUYJUYKVYDVYIUUQZVURSZVYJUYJVVJWUTVVKSZVYJUYKVULAUYJUYKVYDVYIUURZVUN
      SZVYJUYKVVAWVCVVBSZVYJVYDVYMUVMTAUYJUYKVYDVYIUUSZVYCUVMUVMWMSZVYJVYDVYQUV
      MTWVFVYCUVMUVMWPSZVYJVYKVWKUVTVYJUWJVWLTZVYKVWKTVYJUWJUYNVWLAVYEVYFVYHUVA
      VYJUVNFBUVKVWJUVSUXFUVQUVOUXJUXLVWMUWQUXMWUTWVCYDYPZUWJVWKUWCWMSZVWNYQVYJ
      WVIVYPUWCTWVJUWJVWKUWCWPSZVYJVYLUVPVYMVWJQZVYMUVPUVSQVYJUWEWVMUWBVYQUVSQZ
      ULZTZVYLWVMTVYJUWEVYGWVOAVYEVYFVYHUVBVYJUVNFBUVKVWJUVSUXFUVOVYCUXJUXLVWMU
      WQUXMWVCWVFYDYPZUWEWVMWVNWMSZBUVSFUVPVYMUWQIYEYQVYJWVPVYOWVNTWVQUWEWVMWVN
      WPSZUVCVYJWUMVYNVYRPZVYTOWUAVYJWUKWVTWULVYTVYJUVQVVEVYCVYSUVIVYJUYJVVGWUT
      VVHSZVYJVYDVYCVYSUSWVFVYCUVMUVMWQSZXOVYJWUKVYLVYOPZVYKVYPPZVVEVVOPZVYSUXD
      QZQVYLVYKUVRUVPPVYMFUOOZQQZVYRPWVTVYJUWEWWCUWJWWDWUJWWFVYJWUIWWEVYCVYSUXD
      VYJUVQVVEUVOVVOWWAVYJUYKVVPWVCVVQSZYRWWBXOVYJWVPUWEWWCUSWVQUWEWVMWVNWQSZV
      YJWVIUWJWWDUSWVJUWJVWKUWCWQSZYSVYJFBUVPUWBVYMVYQUWGUVKWWGVYKVYPVWJUVSVYLV
      YOUVRUWAUXDUVMUVMUXJUXKUWPVWMUWQWVAWVBWVDWVEWWGRUWRUXQWVGWVHWVKWVLWVRWVSU
      VDVYJWWHVYNVYRVYJUVMBUWGVYKVYLFUVRUVPVYMUWPUWRIWVAWVDWVGUVEYLYMYNVYNVYRVY
      TXJXAVYJWUOWUCWUPWUEWUSWUHVYJWUQWUFWURWUGUXIVYJUYOVVMUYPVUJVYJUYOVVTVVMVY
      JUYOVWAVVTVYJUVQVVEUVHWWAWTVWBXAVYJUVMBUVHUVSUVRUWAUYEUWPUWQWVAWVBXHYHVYJ
      UYPVWEVUJVYJUYPVWFVWEVYJUVOVVOUVHWWIWTVWGXAVYJUVMBUVHUVSUVPUWBUYEUWPUWQWV
      DWVEXHYHYRVYJWURVYMVYQUVHQZWUGVYJWURVYSUVHOWWLVYJVYCVYSUVHWWBWTVYMVYQUVHX
      JXAVYJUVMBUVHUVSVYMVYQUYEUWPUWQWVGWVHXHYHXOVYJWUOWWCWUBOWUCVYJUWEWWCWUNWU
      BVYJUVOVVOVYCVYSUVIWWIWWBXOWWJYNVYLVYOWUBXJXAVYJWUPWWDWUDOWUEVYJUWJWWDUYR
      WUDVYJUVQVVEUVOVVOUVIWWAWWIXOWWKYNVYKVYPWUDXJXAYSXLUVFUVHUVIUVLUVGXRXE $.
  $}

  ${
    oppchofcl.o $e |- O = ( oppCat ` C ) $.
    oppchofcl.m $e |- M = ( HomF ` O ) $.
    oppchofcl.d $e |- D = ( SetCat ` U ) $.
    oppchofcl.c $e |- ( ph -> C e. Cat ) $.
    oppchofcl.u $e |- ( ph -> U e. V ) $.
    oppchofcl.h $e |- ( ph -> ran ( Homf ` C ) C_ U ) $.
    $( Closure of the opposite Hom functor.  (Contributed by Mario Carneiro,
       17-Jan-2017.) $)
    oppchofcl $p |- ( ph -> M e. ( ( C Xc. O ) Func D ) ) $=
      ( cfv co cfunc eqid ccat wcel chomf coppc cxpc oppccat syl ctpos oppchomf
      crn rneqi cdm wrel wceq cbs relxp homffn fndmi releqi mpbir rntpos eqtr3i
      cxp ax-mp eqsstrid hofcl 2oppchomf a1i 2oppccomf xpcpropd oveq1d eleqtrrd
      ccomf eqidd ) AEFUANZFUBOZCPOBFUBOZCPOAFCDEVLGIVLQZJABRSFRSZKBFHUCUDZLAFT
      NZUGZBTNZUGZDVTUEZUGZVSWAWBVRBVTFHVTQZUFUHVTUIZUJZWCWAUKWFBULNZWGUTZUJWGW
      GUMWEWHWHVTWGBVTWDWGQUNUOUPUQVTURVAUSMVBVCAVNVMCPABVLFFRVTVLTNUKABFHVDVEB
      VJNVLVJNUKABFHVFVEAVRVKAFVJNVKKAVPVLRSVQFVLVOUCUDVQVQVGVHVI $.
  $}

  ${
    $d c C $.  $d c M $.  $d c O $.  $d c ph $.
    yonval.y $e |- Y = ( Yon ` C ) $.
    yonval.c $e |- ( ph -> C e. Cat ) $.
    yonval.o $e |- O = ( oppCat ` C ) $.
    ${
      yonval.m $e |- M = ( HomF ` O ) $.
      $( Value of the Yoneda embedding.  (Contributed by Mario Carneiro,
         17-Jan-2017.) $)
      yonval $p |- ( ph -> Y = ( <. C , O >. curryF M ) ) $=
        ( vc cyon cfv cop ccurf co cv coppc chof fveq2d eqtr4di ccat cvv df-yon
        wceq wa simpr opeq12d oveq12d ovexd fvmptd2 eqtrid ) AEBKLBDMZCNOZFAJBJ
        PZUNQLZMZUORLZNOUMUAKUBJUCAUNBUDZUEZUPULUQCNUSUNBUODAURUFZUSUOBQLDUSUNB
        QUTSHTZUGUSUQDRLCUSUODRVASITUHGAULCNUIUJUK $.
    $}

    yoncl.s $e |- S = ( SetCat ` U ) $.
    yoncl.q $e |- Q = ( O FuncCat S ) $.
    yoncl.u $e |- ( ph -> U e. V ) $.
    yoncl.h $e |- ( ph -> ran ( Homf ` C ) C_ U ) $.
    $( The Yoneda embedding is a functor from the category to the category
       ` Q ` of presheaves on ` C ` .  (Contributed by Mario Carneiro,
       17-Jan-2017.) $)
    yoncl $p |- ( ph -> Y e. ( C Func Q ) ) $=
      ( cop co eqid ccat wcel chof cfv ccurf cfunc yonval oppccat syl oppchofcl
      curfcl eqeltrd ) AHBFPFUAUBZUCQZBCUDQABUKFHIJKUKRZUEABFCDUKULULRMJABSTFST
      JBFKUFUGABDEUKFGKUMLJNOUHUIUJ $.
  $}

  ${
    yon11.y $e |- Y = ( Yon ` C ) $.
    yon11.b $e |- B = ( Base ` C ) $.
    yon11.c $e |- ( ph -> C e. Cat ) $.
    yon11.p $e |- ( ph -> X e. B ) $.
    ${
      yon1cl.o $e |- O = ( oppCat ` C ) $.
      yon1cl.s $e |- S = ( SetCat ` U ) $.
      yon1cl.u $e |- ( ph -> U e. V ) $.
      yon1cl.h $e |- ( ph -> ran ( Homf ` C ) C_ U ) $.
      $( The Yoneda embedding at an object of ` C ` is a presheaf on ` C ` ,
         also known as the contravariant Hom functor.  (Contributed by Mario
         Carneiro, 17-Jan-2017.) $)
      yon1cl $p |- ( ph -> ( ( 1st ` Y ) ` X ) e. ( O Func S ) ) $=
        ( cfunc co cfv c1st cfuc c2nd eqid wrel wcel wbr relfunc yoncl 1st2ndbr
        fucbas sylancr funcf1 ffvelcdmd ) ABFDRSZHIUATZABUOCFDUBSZUPIUCTZKFDUQU
        QUDZUKACUQRSZUEIUTUFUPURUTUGCUQUHACUQDEFGIJLNOUSPQUIIUTUJULUMMUN $.
    $}

    yon11.h $e |- H = ( Hom ` C ) $.
    yon11.z $e |- ( ph -> Z e. B ) $.
    $( Value of the Yoneda embedding at an object.  The partially evaluated
       Yoneda embedding is also the contravariant Hom functor.  (Contributed by
       Mario Carneiro, 17-Jan-2017.) $)
    yon11 $p |- ( ph ->
      ( ( 1st ` ( ( 1st ` Y ) ` X ) ) ` Z ) = ( Z H X ) ) $=
      ( c1st cfv co eqid fveq2d fveq1d wcel coppc chof ccurf yonval chomf csetc
      cop crn ccat oppccat syl cvv fvex rnex a1i ssidd oppchofcl oppcbas curf11
      chom hof1 oppchom eqtrdi 3eqtrd ) AGEFNOZOZNOZOGECCUAOZUGVHUBOZUCPZNOZOZN
      OZOEGVINOPZGEDPZAGVGVMAVFVLNAEVEVKAFVJNACVIVHFHJVHQZVIQZUDRSRSABBCVHCUEOZ
      UHZUFOZVIVJVLEGVJQIJACUITVHUITJCVHVPUJUKZACVTVSVIVHULVPVQVTQJVSULTAVRCUEU
      MUNUOAVSUPUQBCVHVPIURZKVLQMUSAVNEGVHUTOZPVOABVHWCVIEGVQWAWBWCQKMVACDVHEGL
      VPVBVCVD $.

    yon12.x $e |- .x. = ( comp ` C ) $.
    yon12.w $e |- ( ph -> W e. B ) $.
    ${
      yon12.f $e |- ( ph -> F e. ( W H Z ) ) $.
      yon12.g $e |- ( ph -> G e. ( Z H X ) ) $.
      $( Value of the Yoneda embedding at a morphism.  The partially evaluated
         Yoneda embedding is also the contravariant Hom functor.  (Contributed
         by Mario Carneiro, 17-Jan-2017.) $)
      yon12 $p |- ( ph -> ( ( ( Z ( 2nd ` ( ( 1st ` Y ) ` X ) ) W ) ` F ) ` G )
        = ( G ( <. W , Z >. .x. X ) F ) ) $=
        ( c1st cfv c2nd ccid cop coppc chof cco ccurf eqid yonval fveq2d fveq1d
        co oveqd chomf crn csetc chom ccat wcel oppccat syl cvv fvex rnex ssidd
        a1i oppchofcl oppcbas oppchom eleqtrrdi curf12 eqtrd hof2 oppcco oveq1d
        catidcl catcocl catlid 3eqtrd ) AFEKHIJUBUCZUCZUDUCZUOZUCZUCFICUEUCZUCZ
        EIKUFZIHUFCUGUCZUHUCZUDUCUOUOZUCEFWJHWKUIUCZUOUOZWIIIUFHWNUOZUOZFEHKUFI
        DUOUOZAFWGWMAWGEKHICWKUFWLUJUOZUBUCZUCZUDUCZUOZUCWMAEWFXCAWEXBKHAWDXAUD
        AIWCWTAJWSUBACWLWKJLNWKUKZWLUKZULUMUNUMUPUNABBCWKWHCUQUCZURZUSUCZWLWSEW
        KUTUCZXAIKHWSUKMNACVAVBWKVAVBNCWKXDVCVDZACXHXGWLWKVEXDXEXHUKNXGVEVBAXFC
        UQVFVGVIAXGVHVJBCWKXDMVKZOXAUKQXIUKZWHUKZSAEHKGUOKHXIUOTCGWKKHPXDVLVMZV
        NVOUNABWKWNWIEXIFWLHIKIXEXJXKXLOQOSWNUKAWIIIGUOIIXIUOABCWHGIMPXMNOVSCGW
        KIIPXDVLVMXNAFKIGUOIKXIUOUACGWKIKPXDVLVMVPAWQWRWIWPUOWIWRHIUFIDUOUOWRAW
        OWRWIWPABCDFEWKIKHMRXDOQSVQVRABCDWIWRWKIIHMRXDOOSVQABCDWHWRGHIMPXMNSROA
        BCDEFGHKIMPRNSQOTUAVTWAWBWB $.
    $}

    yon2.f $e |- ( ph -> F e. ( X H Z ) ) $.
    yon2.g $e |- ( ph -> G e. ( W H X ) ) $.
    $( Value of the Yoneda embedding at a morphism.  (Contributed by Mario
       Carneiro, 17-Jan-2017.) $)
    yon2 $p |- ( ph -> ( ( ( ( X ( 2nd ` Y ) Z ) ` F ) ` W ) ` G )
      = ( F ( <. W , X >. .x. Z ) G ) ) $=
      ( c2nd cfv coppc ccid cop chof cco ccurf yonval fveq2d oveqd fveq1d chomf
      co eqid crn csetc ccat wcel oppccat syl cvv fvex rnex a1i ssidd oppchofcl
      oppcbas curf2val chom oppchom eleqtrrdi catidcl hof2 catlid oveq1d oppcco
      eqtrd 3eqtrd ) AFHEIKJUBUCZUOZUCZUCZUCFEHCUDUCZUEUCZUCZIHUFZKHUFWEUGUCZUB
      UCUOUOZUCWGFWHHWEUHUCZUOUOZEKIUFHWKUOZUOZEFHIUFKDUOUOZAFWDWJAWDHEIKCWEUFW
      IUIUOZUBUCZUOZUCZUCWJAHWCWSAEWBWRAWAWQIKAJWPUBACWIWEJLNWEUPZWIUPZUJUKULUM
      UMABBCWECUNUCZUQZURUCZWIWPGWFEWSIKHWPUPMNACUSUTWEUSUTNCWEWTVAVBZACXDXCWIW
      EVCWTXAXDUPNXCVCUTAXBCUNVDVEVFAXCVGVHBCWEWTMVIZPWFUPZOQTWSUPSVJVSUMABWEWK
      EWGWEVKUCZFWIHIHKXAXEXFXHUPZOSQSWKUPZAEIKGUOKIXHUOTCGWEKIPWTVLVMABWEWFXHH
      XFXIXGXESVNAFHIGUOIHXHUOUACGWEIHPWTVLVMZVOAWNFEWMUOWOAWLFEWMABWEWKWFFXHIH
      XFXIXGXEOXJSXKVPVQABCDEFWEKIHMRWTQOSVRVSVT $.
  $}

  ${
    $d f g h x y C $.  $d f g h x y D $.  $d f g h x y ph $.
    hofpropd.1 $e |- ( ph -> ( Homf ` C ) = ( Homf ` D ) ) $.
    hofpropd.2 $e |- ( ph -> ( comf ` C ) = ( comf ` D ) ) $.
    hofpropd.c $e |- ( ph -> C e. Cat ) $.
    hofpropd.d $e |- ( ph -> D e. Cat ) $.
    $( If two categories have the same set of objects, morphisms, and
       compositions, then they have the same Hom functor.  (Contributed by
       Mario Carneiro, 26-Jan-2017.) $)
    hofpropd $p |- ( ph -> ( HomF ` C ) = ( HomF ` D ) ) $=
      ( vx vy vf vg vh cfv cv co wceq wcel adantr eqid ad2antrr chomf c1st chom
      cbs cxp c2nd cco cmpt cmpo chof homfeqbas sqxpeqd xp1st ad2antll ad2antrl
      cop wa homfeqval xp2nd df-ov 3eqtr3g 1st2nd2 fveq2d 3eqtr4d ccomf simplrl
      ad3antrrr oveq1d oveqd ccat eqtr4di eleq2d biimpa simplrr catcocl eqeltrd
      comfeqval eqtrd mpteq12dva mpoeq123dva opeq12d hofval ) ABUAMZHIBUDMZWDUE
      ZWEJKINZUBMZHNZUBMZBUCMZOZWHUFMZWFUFMZWJOZLWHWJMZKNZLNZWHWMBUGMZOZOZJNZWG
      WIUPZWMWROOZUHZUIZUIZUPCUAMZHICUDMZXHUEZXIJKWGWICUCMZOZWLWMXJOZLWHXJMZWPW
      QWHWMCUGMZOZOZXAXBWMXNOZOZUHZUIZUIZUPBUJMZCUJMZAWCXGXFYADAHIWEWEXEXIXIXTA
      WDXHABCDUKULZAWEXIPWHWEQZYDRAYEWFWEQZUQZUQZJKWKWNXDXKXLXSYHWDBCWJXJWGWIWD
      SZWJSZXJSZAWCXGPZYGDRZYFWGWDQZAYEWFWDWDUMUNZYEWIWDQZAYFWHWDWDUMUOZURYHWNX
      LPXAWKQZYHWDBCWJXJWLWMYIYJYKYMYEWLWDQZAYFWHWDWDUSUOZYFWMWDQZAYEWFWDWDUSUN
      ZURRYHYRWPWNQZUQZUQZLWOXCXMXRYHWOXMPUUDYHWIWLUPZWJMZUUFXJMZWOXMYHWIWLWJOZ
      WIWLXJOUUGUUHYHWDBCWJXJWIWLYIYJYKYMYQYTURWIWLWJUTZWIWLXJUTVAYHWHUUFWJYEWH
      UUFPZAYFWHWDWDVBUOZVCZYHWHUUFXJUULVCVDRUUEWQWOQZUQZXCWTXAXQOXRUUOWDBCXNWR
      XAWTWJWGWIWMYIYJWRSZXNSZYHYLUUDUUNYMTZABVEMCVEMPYGUUDUUNEVGZYHYNUUDUUNYOT
      YHYPUUDUUNYQTZYHUUAUUDUUNUUBTZYHYRUUCUUNVFUUOWTWPWQUUFWMWROZOZWIWMWJOUUOW
      SUVBWPWQUUOWHUUFWMWRYHUUKUUDUUNUULTZVHVIZUUOWDBWRWQWPWJWIWLWMYIYJUUPABVJQ
      YGUUDUUNFVGUUTYHYSUUDUUNYTTZUVAUUEUUNWQUUIQUUEWOUUIWQUUEWOUUGUUIYHWOUUGPU
      UDUUMRUUJVKVLVMZYHYRUUCUUNVNZVOVPVQUUOWTXPXAXQUUOUVCWPWQUUFWMXNOZOWTXPUUO
      WDBCXNWRWQWPWJWIWLWMYIYJUUPUUQUURUUSUUTUVFUVAUVGUVHVQUVEUUOXOUVIWPWQUUOWH
      UUFWMXNUVDVHVIVDVHVRVSVTVTWAAHIWDBWRJKLWJYBYBSFYIYJUUPWBAHIXHCXNJKLXJYCYC
      SGXHSYKUUQWBVD $.

    $( If two categories have the same set of objects, morphisms, and
       compositions, then they have the same Yoneda functor.  (Contributed by
       Mario Carneiro, 26-Jan-2017.) $)
    yonpropd $p |- ( ph -> ( Yon ` C ) = ( Yon ` D ) ) $=
      ( coppc cfv cop chof ccurf co cyon chomf ccat wcel eqid oppccat syl csetc
      crn oppchomfpropd oppccomfpropd cvv fvex a1i oppchofcl curfpropd hofpropd
      rnex ssidd oveq2d eqtrd yonval 3eqtr4d ) ABBHIZJUQKIZLMZCCHIZJZUTKIZLMZBN
      IZCNIZAUSVAURLMVCABCUQUTBOIZUBZUAIZURDEABCDUCZABCDEUDZFGABPQUQPQFBUQUQRZS
      TZACPQUTPQGCUTUTRZSTZABVHVGURUQUEVKURRZVHRFVGUEQAVFBOUFUKUGAVGULUHUIAURVB
      VALAUQUTVIVJVLVNUJUMUNABURUQVDVDRFVKVOUOACVBUTVEVERGVMVBRUOUP $.
  $}

  ${
    oppcyon.o $e |- O = ( oppCat ` C ) $.
    oppcyon.y $e |- Y = ( Yon ` O ) $.
    oppcyon.m $e |- M = ( HomF ` C ) $.
    oppcyon.c $e |- ( ph -> C e. Cat ) $.
    $( Value of the opposite Yoneda embedding.  (Contributed by Mario Carneiro,
       26-Jan-2017.) $)
    oppcyon $p |- ( ph -> Y = ( <. O , C >. curryF M ) ) $=
      ( cfv cop ccurf co chof chomf a1i ccomf ccat wcel eqid coppc wceq oppccat
      2oppchomf 2oppccomf syl hofpropd eqtrid oveq2d crn csetc eqidd fvex ssidd
      cvv rnex hofcl curfpropd yonval 3eqtr4rd ) ADDUAJZKZCLMVBVANJZLMDBKCLMEAC
      VCVBLACBNJVCHABVABOJZVAOJUBABDFUDPZBQJVAQJUBABDFUEPZIADRSZVARSABRSVGIBDFU
      CUFZDVAVATZUCUFZUGUHUIADDBVAVDUJZUKJZCADOJULADQJULVEVFVHVHIVJABVLVKCDUOHF
      VLTIVKUOSAVDBOUMUPPAVKUNUQURADVCVAEGVHVIVCTUSUT $.
  $}

  ${
    oyoncl.o $e |- O = ( oppCat ` C ) $.
    oyoncl.y $e |- Y = ( Yon ` O ) $.
    oyoncl.c $e |- ( ph -> C e. Cat ) $.
    oyoncl.s $e |- S = ( SetCat ` U ) $.
    oyoncl.u $e |- ( ph -> U e. V ) $.
    oyoncl.h $e |- ( ph -> ran ( Homf ` C ) C_ U ) $.
    ${
      oyoncl.q $e |- Q = ( C FuncCat S ) $.
      $( The opposite Yoneda embedding is a functor from ` oppCat `` C ` to the
         functor category ` C -> SetCat ` .  (Contributed by Mario Carneiro,
         26-Jan-2017.) $)
      oyoncl $p |- ( ph -> Y e. ( O Func Q ) ) $=
        ( cfv co ccat wcel eqid coppc cfuc cfunc oppccat syl chomf crn oppchomf
        ctpos rneqi cdm wrel wceq cbs cxp relxp homffn fndmi releqi mpbir ax-mp
        rntpos eqtr3i eqsstrid yoncl 2oppchomf ccomf 2oppccomf setccat fucpropd
        a1i eqidd eqtrid oveq2d eleqtrrd ) AHFFUAPZDUBQZUCQFCUCQAFVQDEVPGHJABRS
        FRSZKBFIUDUEZVPTZLVQTMAFUFPZUGZBUFPZUGZEWCUIZUGZWBWDWEWABWCFIWCTZUHUJWC
        UKZULZWFWDUMWIBUNPZWJUOZULWJWJUPWHWKWKWCWJBWCWGWJTUQURUSUTWCVBVAVCNVDVE
        ACVQFUCACBDUBQVQOABVPDDWCVPUFPUMABFIVFVKBVGPVPVGPUMABFIVHVKADUFPVLADVGP
        VLKAVRVPRSVSFVPVTUDUEAEGSDRSMDEGLVIUEZWLVJVMVNVO $.
    $}

    oyon1cl.b $e |- B = ( Base ` C ) $.
    oyon1cl.p $e |- ( ph -> X e. B ) $.
    $( The opposite Yoneda embedding at an object of ` C ` is a functor from
       ` C ` to Set, also known as the covariant Hom functor.  (Contributed by
       Mario Carneiro, 17-Jan-2017.) $)
    oyon1cl $p |- ( ph -> ( ( 1st ` Y ) ` X ) e. ( C Func S ) ) $=
      ( cfunc co cfv c1st cfuc c2nd oppcbas eqid fucbas wrel wbr relfunc oyoncl
      wcel 1st2ndbr sylancr funcf1 ffvelcdmd ) ABCDRSZHIUATZABUPFCDUBSZUQIUCTZB
      CFJPUDCDURURUEZUFAFURRSZUGIVAUKUQUSVAUHFURUIACURDEFGIJKLMNOUTUJIVAULUMUNQ
      UO $.
  $}

  ${
    $d a b f g x y .1. $.  $d a b g h k u w y z A $.  $d a f g h u w x y z C $.
    $d a b f g h k u v w y z E $.  $d a b f g h k u w x y z F $.  $d a b y K $.
    $d a b f g h k u v w x y z B $.  $d a b f g x y G $.  $d a b h k v w z N $.
    $d z I $.  $d a b f g h k u v w x y z O $.  $d a b f g h k u v w x y z S $.
    $d b g h k u w y z M $.  $d a b f g u v w x z Q $.  $d f g h u v w y z T $.
    $d a b f g x y P $.  $d a b f g h k u v w x y z ph $.  $d u v z R $.
    $d a b f g h k u v w x y z Y $.  $d a b f g h k u v w x y z Z $.
    $d a b f g h k u w x y z X $.
    yoneda.y $e |- Y = ( Yon ` C ) $.
    yoneda.b $e |- B = ( Base ` C ) $.
    yoneda.1 $e |- .1. = ( Id ` C ) $.
    yoneda.o $e |- O = ( oppCat ` C ) $.
    yoneda.s $e |- S = ( SetCat ` U ) $.
    yoneda.t $e |- T = ( SetCat ` V ) $.
    yoneda.q $e |- Q = ( O FuncCat S ) $.
    yoneda.h $e |- H = ( HomF ` Q ) $.
    yoneda.r $e |- R = ( ( Q Xc. O ) FuncCat T ) $.
    yoneda.e $e |- E = ( O evalF S ) $.
    yoneda.z $e |- Z = ( H o.func ( ( <. ( 1st ` Y ) , tpos ( 2nd ` Y ) >.
      o.func ( Q 2ndF O ) ) pairF ( Q 1stF O ) ) ) $.
    yoneda.c $e |- ( ph -> C e. Cat ) $.
    yoneda.w $e |- ( ph -> V e. W ) $.
    yoneda.u $e |- ( ph -> ran ( Homf ` C ) C_ U ) $.
    yoneda.v $e |- ( ph -> ( ran ( Homf ` Q ) u. U ) C_ V ) $.
    $( Lemma for ~ yoneda .  (Contributed by Mario Carneiro, 28-Jan-2017.) $)
    yonedalem1 $p |- ( ph ->
      ( Z e. ( ( Q Xc. O ) Func T ) /\ E e. ( ( Q Xc. O ) Func T ) ) ) $=
      ( cxpc co cfunc wcel c1st cfv c2nd ctpos cop c2ndf ccofu c1stf cprf coppc
      eqid ccat oppccat syl cvv chomf crn unssbd setccat fuccat 2ndfcl wbr wrel
      ssexd relfunc yoncl 1st2ndbr df-br sylib cofucl 1stfcl prfcl unssad hofcl
      sylancr funcoppc eqeltrid funcsetcres2 evlfcl sseldd jca ) APDLULUMZGUNUM
      ZUOJWRUOAPKOUPUQZOURUQZUSZUTZDLVAUMZVBUMZDLVCUMZVDUMZVBUMWRUGAWQDVEUQZDUL
      UMZGXFKAWQXGXFXHDXDXEXFVFXHVFAWQLXGXCXBADLXCWQWQVFZALFDUCACVGUOLVGUOUHCLT
      VHVIZAHVJUOFVGUOAHMNUIADVKUQVLZHMUKVMZVSZFHVJUAVNVIZVOZXJXCVFVPAWSXALXGUN
      UMZVQXBXPUOACDXGWSWTLTXGVFZACDUNUMZVROXRUOWSWTXRVQCDVTACDFHLVJOQUHTUAUCXM
      UJWAOXRWBWJWKWSXAXPWCWDWEADLXEWQXIXOXJXEVFWFWGADGMKXGNUDXQUBXOUIAXKHMUKWH
      WIWEWLAWQFUNUMWRJAGFMWQHNUBUAUIXLWMALFDJUFUCXJXNWNWOWP $.

    ${
      yonedalem21.f $e |- ( ph -> F e. ( O Func S ) ) $.
      yonedalem21.x $e |- ( ph -> X e. B ) $.
      $( Lemma for ~ yoneda .  (Contributed by Mario Carneiro, 28-Jan-2017.) $)
      yonedalem21 $p |- ( ph -> ( F ( 1st ` Z ) X ) =
        ( ( ( 1st ` Y ) ` X ) ( O Nat S ) F ) ) $=
        ( c1st cfv co c2nd ctpos c2ndf ccofu c1stf cprf cnat fveq2i oveqi df-ov
        cop eqtri cfunc cxpc coppc eqid fucbas oppcbas xpcbas ccat wcel oppccat
        cxp syl cvv chomf crn unssbd ssexd setccat fuccat 2ndfcl wbr wrel yoncl
        relfunc 1st2ndbr sylancr funcoppc df-br sylib cofucl 1stfcl prfcl hofcl
        unssad opelxpd cofu1 eqtrid chom prf1 wceq fvex tposex op1st a1i op2ndg
        2ndf1 syl2anc eqtrd fveq12d op1stg opeq12d fveq2d eqtr4di fuchom yon1cl
        1stf1 hof1 3eqtrd ) AKPRUPUQZURZKPVIZQUPUQZQUSUQZUTZVIZDMVAURZVBURZDMVC
        URZVDURZUPUQUQZLUPUQZUQZPYLUQZKUUAURZUUCKMFVEURZURAYJYKLYSVBURZUPUQZUQZ
        UUBYJKPUUGURUUHYIUUGKPRUUFUPUIVFVGKPUUGVHVJAMFVKURZBWAZDMVLURZDVMUQZDVL
        URZGYSLYKDMUUKUUIBUUKVNZMFDUEVOZBCMUBTVPVQZAUUKUULYSUUMDYQYRYSVNZUUMVNA
        UUKMUULYPYOADMYPUUKUUNAMFDUEACVRVSMVRVSUJCMUBVTWBZAHWCVSFVRVSAHNOUKADWD
        UQWEZHNUMWFWGZFHWCUCWHWBWIZUURYPVNZWJZAYLYNMUULVKURZWKYOUVDVSACDUULYLYM
        MUBUULVNZACDVKURZWLQUVFVSYLYMUVFWKCDWNACDFHMWCQSUJUBUCUEUUTULWMQUVFWOWP
        WQYLYNUVDWRWSZWTZADMYRUUKUUNUVAUURYRVNZXAZXBADGNLUULOUFUVEUDUVAUKAUUSHN
        UMXDXCAKPUUIBUNUOXEZXFXGAUUBUUCKVIZUUAUQUUDAYTUVLUUAAYTYKYQUPUQUQZYKYRU
        PUQUQZVIUVLAUUJUUKUULYSDYQYRUUKXHUQZYKUUQUUPUVOVNZUVHUVJUVKXIAUVMUUCUVN
        KAUVMYKYPUPUQUQZYOUPUQZUQUUCAUUJUUKMUULYPYOYKUUPUVCUVGUVKXFAUVQPUVRYLUV
        RYLXJAYLYNQUPXKYMQUSXKXLXMXNAUVQYKUSUQZPAUUJDMYPYKUUKUVOUUNUUPUVPUVAUUR
        UVBUVKXPAKUUIVSZPBVSZUVSPXJUNUOKPUUIBXOXQXRXSXRAUVNYKUPUQZKAUUJDMYRYKUU
        KUVOUUNUUPUVPUVAUURUVIUVKYFAUVTUWAUWBKXJUNUOKPUUIBXTXQXRYAXRYBUUCKUUAVH
        YCAUUIDUUELUUCKUFUVAUUOMFDUUEUEUUEVNYDABCFHMWCPQSTUJUOUBUCUUTULYEUNYGYH
        $.

      ${
        yonedalem3a.m $e |- M = ( f e. ( O Func S ) , x e. B |->
          ( a e. ( ( ( 1st ` Y ) ` x ) ( O Nat S ) f ) |->
            ( ( a ` x ) ` ( .1. ` x ) ) ) ) $.
        $( Lemma for ~ yoneda .  (Contributed by Mario Carneiro,
           29-Jan-2017.) $)
        yonedalem3a $p |- ( ph -> ( ( F M X ) =
          ( a e. ( ( ( 1st ` Y ) ` X ) ( O Nat S ) F ) |->
            ( ( a ` X ) ` ( .1. ` X ) ) ) /\
            ( F M X ) : ( F ( 1st ` Z ) X ) --> ( F ( 1st ` E ) X ) ) ) $=
          ( co c1st cfv cnat cv cmpt wceq wf cfunc wcel wa simpr fveq2d oveq12d
          simpl fveq12d mpteq12dv ovex mptex ovmpoa syl2anc chom c2nd nat1st2nd
          eqid oppcbas adantr natcl cvv chomf crn unssbd ssexd cbs wrel relfunc
          wbr yon1cl 1st2ndbr sylancr funcf1 ffvelcdmd eleqtrrd elsetchom mpbid
          setcbas catidcl yon11 fmpttd yonedalem21 ccat oppccat setccat feq123d
          syl evlf1 mpbird jca ) AMSOVAZUBSTVBVCZVCZMPGVDVAZVAZSJVCZSUBVEZVCZVC
          ZVFZVGZMSUAVBVCVAZMSLVBVCVAZXSVHZAMPGVIVAZVJZSCVJZYIURUSKBMSYMCUBBVEZ
          XTVCZKVEZYBVAZYPJVCZYPYEVCZVCZVFYHOYRMVGZYPSVGZVKZUBYSUUBYCYGUUEYQYAY
          RMYBUUEYPSXTUUCUUDVLZVMUUCUUDVOVNUUEYTYDUUAYFUUEYPSYEUUFVMUUEYPSJUUFV
          MVPVQUTUBYCYGYAMYBVRVSVTWAZAYLYCSMVBVCZVCZYHVHAUBYCYGUUIAYEYCVJZVKZSY
          AVBVCZVCZUUIYDYFUUKYFUUMUUIGWBVCZVAVJUUMUUIYFVHUUKYECPGUULYAWCVCZUUNU
          UHMWCVCZYBSYBWEZUUKYEPGYAMYBUUQAUUJVLWDCDPUFUDWFZUUNWEZAYOUUJUSWGWHUU
          KGIYFUUNWIUUMUUIUGAIWIVJZUUJAIQRUOAEWJVCWKIQUQWLWMZWGUUSAUUMIVJUUJAUU
          MGWNVCZIACUVBSUULACUVBPGUULUUOUURUVBWEZAYMWOZYAYMVJUULUUOYMWQPGWPZACD
          GIPWISTUCUDUNUSUFUGUVAUPWRYAYMWSWTXAUSXBAGIWIUGUVAXFZXCWGAUUIIVJUUJAU
          UIUVBIACUVBSUUHACUVBPGUUHUUPUURUVCAUVDYNUUHUUPYMWQUVEURMYMWSWTXAUSXBU
          VFXCWGXDXEAYDUUMVJUUJAYDSSDWBVCZVAUUMACDJUVGSUDUVGWEZUEUNUSXGACDUVGST
          SUCUDUNUSUVHUSXHXCWGXBXIAYJYCYKUUIXSYHUUGACDEFGHIJLMNPQRSTUAUCUDUEUFU
          GUHUIUJUKULUMUNUOUPUQURUSXJACPGLMSULADXKVJPXKVJUNDPUFXLXOAUUTGXKVJUVA
          GIWIUGXMXOUURURUSXPXNXQXR $.
      $}

      ${
        yonedalem4.n $e |- N =
          ( f e. ( O Func S ) , x e. B |-> ( u e. ( ( 1st ` f ) ` x ) |->
            ( y e. B |-> ( g e. ( y ( Hom ` C ) x ) |->
              ( ( ( x ( 2nd ` f ) y ) ` g ) ` u ) ) ) ) ) $.
        yonedalem4.p $e |- ( ph -> A e. ( ( 1st ` F ) ` X ) ) $.
        $( Lemma for ~ yoneda .  (Contributed by Mario Carneiro,
           29-Jan-2017.) $)
        yonedalem4a $p |- ( ph -> ( ( F N X ) ` A ) =
          ( y e. B |-> ( g e. ( y ( Hom ` C ) X ) |->
              ( ( ( X ( 2nd ` F ) y ) ` g ) ` A ) ) ) ) $=
          ( cv chom cfv co c2nd cmpt c1st cvv cfunc cmpo wceq a1i simprl fveq2d
          wa simprr fveq12d wcel simplrr oveq2d eqidd oveq123d fveq1d mpteq12dv
          simplrl mpteq2dva fvex mptex ovmpod simpr mpteq2dv cbs fvexi fvmptd )
          ADECFOCVEZUCGVFVGZVHZDVEZOVEZUCWSQVIVGZVHZVGZVGZVJZVJZCFOXAEXFVGZVJZV
          JZUCQVKVGZVGZQUCSVHVLANBQUCTJVMVHZFDBVEZNVEZVKVGZVGZCFOWSXPWTVHZXBXCX
          PWSXQVIVGZVHZVGZVGZVJZVJZVJZDXNXIVJZSVLSNBXOFYGVNVOAVCVPAXQQVOZXPUCVO
          ZVSVSZDXSYFXNXIYKXPUCXRXMYKXQQVKAYIYJVQVRAYIYJVTWAYKCFYEXHYKWSFWBZVSZ
          OXTYDXAXGYMXPUCWSWTAYIYJYLWCZWDYMXBYCXFYMXCYBXEYMXPUCWSWSYAXDYMXQQVIA
          YIYJYLWIVRYNYMWSWEWFWGWGWHWJWHVAVBYHVLWBADXNXIUCXMWKWLVPWMAXBEVOZVSZC
          FXHXKYPOXAXGXJYPXBEXFAYOWNVRWOWOVDXLVLWBACFXKFGWPUGWQWLVPWR $.

        ${
          yonedalem4b.p $e |- ( ph -> P e. B ) $.
          yonedalem4b.g $e |- ( ph -> G e. ( P ( Hom ` C ) X ) ) $.
          $( Lemma for ~ yoneda .  (Contributed by Mario Carneiro,
             29-Jan-2017.) $)
          yonedalem4b $p |- ( ph -> ( ( ( ( F N X ) ` A ) ` P ) ` G ) =
            ( ( ( X ( 2nd ` F ) P ) ` G ) ` A ) ) $=
            ( co cfv chom c2nd cmpt yonedalem4a fveq1d wceq eqidd cvv wcel ovex
            cv wa mptex a1i adantr simpr oveq1d eleqtrrd simplr oveq2d fvmptdv2
            fvexd fveq12d nfmpt1 nffvmpt1 nfcv nffv nfeq1 fvmptd2f mpd eqtrd )
            ASHERUEUAVIVJZVJZVJSHCFPCWAZUEGVKVJZVIZEPWAZUEXDRVLVJZVIZVJZVJZVMZV
            MZVJZVJZESUEHXHVIZVJZVJZASXCXNAHXBXMABCDEFGIJKLMNOPQRTUAUBUCUDUEUFU
            GUHUIUJUKULUMUNUOUPUQURUSUTVAVBVCVDVEVFVNVOVOAXMXMVPXOXRVPZAXMVQAXS
            CHXLFXMVRVGXLVRVSAXDHVPZWBZPXFXKXDUEXEVTWCWDYAPSXKXRXFXNVRYASHUEXEV
            IZXFASYBVSXTVHWEYAXDHUEXEAXTWFWGWHYAXGSVPZWBZEXJWLYDEXJXQYDXGSXIXPY
            DXDHUEXHAXTYCWIWJYAYCWFWMVOWKCFXLWNCXOXRCSXNCFXLHWOCSWPWQWRWSWTXA
            $.
        $}

        $( Lemma for ~ yoneda .  (Contributed by Mario Carneiro,
           29-Jan-2017.) $)
        yonedalem4c $p |- ( ph ->
          ( ( F N X ) ` A ) e. ( ( ( 1st ` Y ) ` X ) ( O Nat S ) F ) ) $=
          ( vz vw vh vk co cfv c1st cnat wcel chom cixp c2nd cop wceq wral cmpt
          cv cco yonedalem4a weq oveq1 oveq2 fveq1d mpteq12dv cbvmptv eqtrdi wa
          wf oppcbas eqid cfunc wbr wrel relfunc 1st2ndbr sylancr adantr funcf2
          simpr oppchom eleqtrrdi ffvelcdmd cvv chomf crn unssbd funcf1 setcbas
          ssexd cbs feq3d mpbird ad2antrr ffvelcdmda elsetchom mpbid ccat yon11
          fmpttd feq2d yon1cl ralrimiva fvexi mptelixpg fveq2d 3ad2antr1 setcco
          wb ccom syl2anc eqtrd wss yonedalem4b 3eqtr4d fveq2 fcompt sylibr w3a
          ax-mp eqeltrd simpr1 eleq2d biimpa simpr2 simplr3 funcco oppcco fvco3
          simpr3 3eqtr3d eleqtrdi yon12 cun catcocl syldan mpteq2dva ovex mptex
          feq123d fvmpt2 mpan2 sylan9eq rspcdva ralrimivvva isnat2 mpbir2and
          feq1d ) AEQUCSVIVJZUCUDVKVJVJZQTJVLVIZVIVMUVLVEFVEWAZUVMVKVJZVJZUVOQV
          KVJZVJZJVNVJZVIZVOZVMVFWAZUVLVJZVGWAZUVOUWCUVMVPVJZVIZVJZUVQUWCUVPVJZ
          VQUWCUVRVJZJWBVJZVIVIZUWEUVOUWCQVPVJZVIZVJZUVOUVLVJZUVQUVSVQUWJUWKVIV
          IZVRZVGUVOUWCTVNVJZVIZVSVFFVSVEFVSAUVLVEFOUVOUCGVNVJZVIZEOWAZUCUVOUWM
          VIZVJZVJZVTZVTZUWBAUVLCFOCWAZUCUXAVIZEUXCUCUXIUWMVIZVJZVJZVTZVTUXHABC
          DEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPUQURUSUTVAVBVCVDWCCV
          EFUXNUXGCVEWDZOUXJUXMUXBUXFUXIUVOUCUXAWEUXOEUXLUXEUXOUXCUXKUXDUXIUVOU
          CUWMWFWGWGWHWIWJZAUXGUWAVMZVEFVSZUXHUWBVMZAUXQVEFAUVOFVMZWKZUXQUVQUVS
          UXGWLZUYAUYBUXBUVSUXGWLUYAOUXBUXFUVSUYAUXCUXBVMZWKZUCUVRVJZUVSEUXEUYD
          UXEUYEUVSUVTVIZVMUYEUVSUXEWLUYDUCUVOUWSVIZUYFUXCUXDUYAUYGUYFUXDWLZUYC
          UYAFTJUVRUWMUWSUVTUCUVOFGTUIUGWMZUWSWNZUVTWNZAUVRUWMTJWOVIZWPZUXTAUYL
          WQZQUYLVMZUYMTJWRZVAQUYLWSWTZXAAUCFVMZUXTVBXAZAUXTXCZXBXAUYDUXCUXBUYG
          UYAUYCXCGUXATUCUVOUXAWNZUIXDZXEXFUYDJLUXEUVTXGUYEUVSUJUYALXGVMZUYCAVU
          CUXTALUAUBURAHXHVJXIZLUAUTXJXMZXAZXAUYKAUYELVMZUXTUYCAFLUCUVRAFLUVRWL
          ZFJXNVJZUVRWLAFVUITJUVRUWMUYIVUIWNZUYQXKALVUIUVRFAJLXGUJVUEXLZXOXPZVB
          XFZXQUYAUVSLVMZUYCAFLUVOUVRVULXRZXAXSXTAEUYEVMZUXTUYCVDXQXFYCUYAUVQUX
          BUVSUXGUYAFGUXAUCUDUVOUFUGAGYAVMZUXTUQXAUYSVUAUYTYBYDXPZUYAJLUXGUVTXG
          UVQUVSUJVUFUYKAFLUVOUVPAFLUVPWLZFVUIUVPWLAFVUITJUVPUWFUYIVUJAUYNUVMUY
          LVMUVPUWFUYLWPZUYPAFGJLTXGUCUDUFUGUQVBUIUJVUEUSYEZUVMUYLWSWTZXKALVUIU
          VPFVUKXOXPZXRZVUOXSXPYFFXGVMUXSUXRYLFGXNUGYGVEFUXGUWAXGYHUUCUUAUUDAUW
          RVEVFVGFFUWTAUXTUWCFVMZUWEUWTVMZUUBZWKZUWDUWHYMZUWOUWPYMZUWLUWQVVHVHU
          VQVHWAZUWHVJZUWDVJZVTZVHUVQVVKUWPVJZUWOVJZVTZVVIVVJVVHVHUVQVVMVVPVVHV
          VKUVQVMZVVKUXBVMZVVMVVPVRVVHVVRVVSVVHUVQUXBVVKVVHFGUXAUCUDUVOUFUGAVUQ
          VVGUQXAZAUYRVVGVBXAZVUAAUXTVVEVVFUUEZYBUUFUUGVVHVVSWKZEVVKUWEUWCUVOVQ
          UCGWBVJZVIVIZUCUWCUWMVIZVJZVJZEVVKUXDVJZVJZUWOVJZVVMVVPVWCVWHEUWOVWIY
          MZVJZVWKVWCEVWGVWLVWCUWEVVKUCUVOVQUWCTWBVJZVIVIZVWFVJUWOVWIUYEUVSVQUW
          JUWKVIVIVWGVWLVWCFTVWNJUVRUWMUWSVVKUWEUWKUCUVOUWCUYIUYJVWNWNUWKWNZVVH
          UYMVVSAUYMVVGUYQXAZXAVVHUYRVVSVWAXAZVVHUXTVVSVWBXAZVVHVVEVVSAUXTVVEVV
          FUUHZXAZVWCVVKUXBUYGVVHVVSXCZVUBXEZUXTVVEVVFAVVSUUIZUUJVWCVWOVWEVWFVW
          CFGVWDVVKUWETUCUVOUWCUGVWDWNZUIVWRVWSVXAUUKYIVWCJUWKLVWIUWOXGUYEUVSUW
          JUJVVHVUCVVSAVUCVVGVUEXAZXAZVWPAVUGVVGVVSVUMXQZVVHVUNVVSAVVEUXTVUNVVF
          VUOYJZXAZVVHUWJLVMVVSVVHFLUWCUVRAVUHVVGVULXAVWTXFZXAVWCVWIUYFVMUYEUVS
          VWIWLZVWCUYGUYFVVKUXDVVHUYHVVSVVHFTJUVRUWMUWSUVTUCUVOUYIUYJUYKVWQVWAV
          WBXBXAVXCXFVWCJLVWIUVTXGUYEUVSUJVXGUYKVXHVXJXSXTZVVHUVSUWJUWOWLZVVSVV
          HUWOUVSUWJUVTVIZVMVXNVVHUWTVXOUWEUWNVVHFTJUVRUWMUWSUVTUVOUWCUYIUYJUYK
          VWQVWBVWTXBAUXTVVEVVFUUMZXFVVHJLUWOUVTXGUVSUWJUJVXFUYKVXIVXKXSXTZXAYK
          UUNWGVWCVXLVUPVWMVWKVRVXMAVUPVVGVVSVDXQZUYEUVSEUWOVWIUULYNYOVWCVVMVWE
          UWDVJVWHVWCVVLVWEUWDVWCFGVWDUWEVVKUXAUWCUCUDUVOUFUGVVHVUQVVSVVTXAZVWR
          VUAVWSVXEVXAVWCUWEUWTUWCUVOUXAVIVXDGUXATUVOUWCVUAUIXDUUOZVXBUUPYIVWCB
          CDEFGUWCHIJKLMNOPQVWERSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPVXSAUAUBVMVVG
          VVSURXQZAGXHVJXILYPVVGVVSUSXQZAVUDLUUQUAYPVVGVVSUTXQZAUYOVVGVVSVAXQZV
          WRVCVXRVXAVWCFGVWDUWEVVKUXAUWCUVOUCUGVUAVXEVXSVXAVWSVWRVXTVXBUURYQYOV
          WCVVOVWJUWOVWCBCDEFGUVOHIJKLMNOPQVVKRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUO
          UPVXSVYAVYBVYCVYDVWRVCVXRVWSVXBYQYIYRUUSUUTVVHUWIUWJUWDWLZUVQUWIUWHWL
          ZVVIVVNVRVVHUVQUVSUWPWLZVYEVEFUWCVEVFWDUVQUWIUVSUWJUWPUWDUVOUWCUVLYSU
          VOUWCUVPYSUVOUWCUVRYSUVCAVYGVEFVSVVGAVYGVEFUYAVYGUYBVURUYAUVQUVSUWPUX
          GAUXTUWPUVOUXHVJZUXGAUVOUVLUXHUXPWGUXTUXGXGVMVYHUXGVROUXBUXFUVOUCUXAU
          VAUVBVEFUXGXGUXHUXHWNUVDUVEUVFUVKXPZYFXAVWTUVGZVVHUWHUVQUWIUVTVIZVMVY
          FVVHUWTVYKUWEUWGVVHFTJUVPUWFUWSUVTUVOUWCUYIUYJUYKAVUTVVGVVBXAVWBVWTXB
          VXPXFVVHJLUWHUVTXGUVQUWIUJVXFUYKAVVEUXTUVQLVMVVFVVDYJZVVHFLUWCUVPAVUS
          VVGVVCXAVWTXFZXSXTZVHUWDUWHUVQUWIUWJYTYNVVHVXNVYGVVJVVQVRVXQAVVEUXTVY
          GVVFVYIYJZVHUWOUWPUVQUVSUWJYTYNYRVVHJUWKLUWHUWDXGUVQUWIUWJUJVXFVWPVYL
          VYMVXKVYNVYJYKVVHJUWKLUWPUWOXGUVQUVSUWJUJVXFVWPVYLVXIVXKVYOVXQYKYRUVH
          AVEVFUVLFTJUWKVGUVMQUWSUVTUVNUVNWNUYIUYJUYKVWPVVAVAUVIUVJ $.
      $}

      yonedalem22.g $e |- ( ph -> G e. ( O Func S ) ) $.
      yonedalem22.p $e |- ( ph -> P e. B ) $.
      yonedalem22.a $e |- ( ph -> A e. ( F ( O Nat S ) G ) ) $.
      yonedalem22.k $e |- ( ph -> K e. ( P ( Hom ` C ) X ) ) $.
      $( Lemma for ~ yoneda .  (Contributed by Mario Carneiro, 29-Jan-2017.) $)
      yonedalem22 $p |- ( ph ->
        ( A ( <. F , X >. ( 2nd ` Z ) <. G , P >. ) K ) =
        ( ( ( P ( 2nd ` Y ) X ) ` K ) ( <. ( ( 1st ` Y ) ` X ) , F >.
          ( 2nd ` H ) <. ( ( 1st ` Y ) ` P ) , G >. ) A ) ) $=
        ( cop c2nd cfv co c1st ctpos c2ndf ccofu c1stf fveq2i oveqi df-ov eqtri
        cprf cfunc cxpc coppc chom eqid fucbas oppcbas xpcbas ccat wcel oppccat
        cxp syl cvv chomf crn unssbd ssexd setccat fuccat 2ndfcl wbr wrel yoncl
        relfunc 1st2ndbr sylancr funcoppc df-br sylib cofucl 1stfcl prfcl hofcl
        unssad opelxpd cnat oppchom eleqtrrdi fuchom eleqtrrd cofu2 eqtrid prf1
        xpchom2 cofu1 wceq fvex tposex op1st 2ndf1 op2ndg syl2anc eqtrd fveq12d
        1stf1 op1stg opeq12d oveq12d cres fveq1d fvresd 3eqtrd a1i op2nd ovtpos
        prf2 2ndf2 1stf2 eqtr4di ) ABPMTVDZNEVDZUBVEVFZVGZVGZBPVDZUUHUUIUAVHVFZ
        UAVEVFZVIZVDZFQVJVGZVKVGZFQVLVGZVQVGZVEVFVGVFZUUHUVAVHVFZVFZUUIUVCVFZOV
        EVFZVGZVFZPETUUOVGZVFZBTUUNVFZMVDZEUUNVFZNVDZUVFVGZVGZAUULUUMUUHUUIOUVA
        VKVGZVEVFZVGZVFZUVHUULBPUVSVGUVTUUKUVSBPUUJUVRUUHUUIUBUVQVEUMVMVNVNBPUV
        SVOVPAQHVRVGZCWIZFQVSVGZFVTVFZFVSVGZUUMIUVAOUWCWAVFZUUHUUIFQUWCUWACUWCW
        BZQHFUIWCZCDQUFUDWDZWEZAUWCUWDUVAUWEFUUSUUTUVAWBZUWEWBAUWCQUWDUURUUQAFQ
        UURUWCUWGAQHFUIADWFWGQWFWGUNDQUFWHWJZAJWKWGHWFWGAJRSUOAFWLVFWMZJRUQWNWO
        ZHJWKUGWPWJWQZUWLUURWBZWRZAUUNUUPQUWDVRVGZWSUUQUWRWGADFUWDUUNUUOQUFUWDW
        BZADFVRVGZWTUAUWTWGUUNUUOUWTWSDFXBADFHJQWKUAUCUNUFUGUIUWNUPXAUAUWTXCXDX
        EUUNUUPUWRXFXGZXHZAFQUUTUWCUWGUWOUWLUUTWBZXIZXJAFIROUWDSUJUWSUHUWOUOAUW
        MJRUQXLXKAMTUWACURUSXMZANEUWACUTVAXMZUWFWBZAUUMMNQHXNVGZVGZTEQWAVFZVGZW
        IUUHUUIUWFVGZABPUXIUXKVBAPETDWAVFZVGZUXKVCDUXMQTEUXMWBUFXOXPXMAFQNEUWCU
        XHUXJUWFMTUWACUWGUWHUWIQHFUXHUIUXHWBXQUXJWBURUSUTVAUXGYBXRZXSXTAUVHUVJB
        VDZUVOVFUVPAUVBUXPUVGUVOAUVDUVLUVEUVNUVFAUVDUUHUUSVHVFZVFZUUHUUTVHVFZVF
        ZVDUVLAUWBUWCUWDUVAFUUSUUTUWFUUHUWKUWJUXGUXBUXDUXEYAAUXRUVKUXTMAUXRUUHU
        URVHVFZVFZUUQVHVFZVFUVKAUWBUWCQUWDUURUUQUUHUWJUWQUXAUXEYCAUYBTUYCUUNUYC
        UUNYDAUUNUUPUAVHYEZUUOUAVEYEYFZYGUUAZAUYBUUHVEVFZTAUWBFQUURUUHUWCUWFUWG
        UWJUXGUWOUWLUWPUXEYHAMUWAWGZTCWGZUYGTYDURUSMTUWACYIYJYKZYLYKAUXTUUHVHVF
        ZMAUWBFQUUTUUHUWCUWFUWGUWJUXGUWOUWLUXCUXEYMAUYHUYIUYKMYDURUSMTUWACYNYJY
        KYOYKAUVEUUIUXQVFZUUIUXSVFZVDUVNAUWBUWCUWDUVAFUUSUUTUWFUUIUWKUWJUXGUXBU
        XDUXFYAAUYLUVMUYMNAUYLUUIUYAVFZUYCVFUVMAUWBUWCQUWDUURUUQUUIUWJUWQUXAUXF
        YCAUYNEUYCUUNUYFAUYNUUIVEVFZEAUWBFQUURUUIUWCUWFUWGUWJUXGUWOUWLUWPUXFYHA
        NUWAWGZECWGZUYOEYDUTVANEUWACYIYJYKZYLYKAUYMUUIVHVFZNAUWBFQUUTUUIUWCUWFU
        WGUWJUXGUWOUWLUXCUXFYMAUYPUYQUYSNYDUTVANEUWACYNYJYKYOYKYPAUVBUUMUUHUUIU
        USVEVFVGVFZUUMUUHUUIUUTVEVFVGZVFZVDUXPAUWBUWCUWDUVAFUUSUUTUWFUUMUUHUUIU
        WKUWJUXGUXBUXDUXEUXFUXOUUDAUYTUVJVUBBAUYTUUMUUHUUIUURVEVFVGZVFZUYBUYNUU
        QVEVFZVGZVFUVJAUWBUWCQUUMUWDUURUUQUWFUUHUUIUWJUWQUXAUXEUXFUXGUXOXSAVUDP
        VUFUVIAVUFUYNUYBUUOVGZUVIVUFUYBUYNUUPVGVUGVUEUUPUYBUYNUUNUUPUYDUYEUUBVN
        UYBUYNUUOUUCVPAUYNEUYBTUUOUYRUYJYPXTAVUDUUMVEUXLYQZVFUUMVEVFZPAUUMVUCVU
        HAUWBFQUURUUHUUIUWCUWFUWGUWJUXGUWOUWLUWPUXEUXFUUEYRAUUMUXLVEUXOYSABUXIW
        GZPUXNWGZVUIPYDVBVCBPUXIUXNYIYJYTYLYKAVUBUUMVHUXLYQZVFUUMVHVFZBAUUMVUAV
        ULAUWBFQUUTUUHUUIUWCUWFUWGUWJUXGUWOUWLUXCUXEUXFUUFYRAUUMUXLVHUXOYSAVUJV
        UKVUMBYDVBVCBPUXIUXNYNYJYTYOYKYLUVJBUVOVOUUGYK $.

      yonedalem3.m $e |- M = ( f e. ( O Func S ) , x e. B |->
        ( a e. ( ( ( 1st ` Y ) ` x ) ( O Nat S ) f ) |->
          ( ( a ` x ) ` ( .1. ` x ) ) ) ) $.
      $( Lemma for ~ yoneda .  (Contributed by Mario Carneiro, 29-Jan-2017.) $)
      yonedalem3b $p |- ( ph -> ( ( G M P )
         ( <. ( F ( 1st ` Z ) X ) , ( G ( 1st ` Z ) P ) >.
              ( comp ` T ) ( G ( 1st ` E ) P ) )
         ( A ( <. F , X >. ( 2nd ` Z ) <. G , P >. ) K ) ) =
       ( ( A ( <. F , X >. ( 2nd ` E ) <. G , P >. ) K )
          ( <. ( F ( 1st ` Z ) X ) , ( F ( 1st ` E ) X ) >.
              ( comp ` T ) ( G ( 1st ` E ) P ) ) ( F M X ) ) ) $=
        ( vb vy co cop c2nd cfv ccom c1st cnat cv cmpt wceq oveq2 oveq1d fveq1d
        cco cbvmptv wcel wa eqid chom cfunc wrel wbr relfunc cvv sylancr funcf2
        1st2ndbr ffvelcdmd adantr fuccoval wf cbs funcf1 setcbas feq3d eleqtrrd
        mpbird nat1st2nd natcl elsetchom mpbid setcco eqtrd syl2anc yon11 fvco3
        3eqtrd catidcl ccat fveq2d 3eqtr3d wral cxp simpld opelxpd df-ov eqcomi
        oveq12i a1i feq23d fovcdmd yonedalem21 feq123d fmpt yonedalem3a fmptcof
        syl sylibr simprd 3eqtr4d oppcbas fuchom chomf unssbd ssexd yoncl simpr
        crn fuccocl fucbas fco yon2 catrid oppchom eleqtrrdi nati yon12 3eqtr2d
        catlid mpteq2dva eqtrid xpcbas yonedalem1 xpchom2 xpeq2i eqtrdi oppccat
        yonedalem22 setccat fuccat hof2val fveq1 evlf2val coeq1d fcompt 2fveq3
        cxpc evlf1 ) APFSVKZCROUCVLZPFVLZUEVMVNZVKZVKZVOZCRUVTUWANVMVNZVKZVKZOU
        CSVKZVOZUVSUWDOUCUEVPVNZVKZPFUWKVKZVLPFNVPVNZVKZJWDVNZVKVKUWHUWIUWLOUCU
        WNVKZVLUWOUWPVKVKAVIUCUDVPVNZVNZOTIVQVKZVKZFLVNZFCVIVRZUWSOVLZPGWDVNZVK
        ZVKZRFUCUDVMVNZVKZVNZFUWRVNZUWSVLPUXEVKZVKZVNZVNZVSZUFUXAUCLVNZUCUFVRZV
        NZVNZRUCFOVMVNZVKZVNZVNZFCVNZVNZVSZUWEUWJAUXPUFUXAUXBFCUXRUXFVKZUXJUXLV
        KZVNZVNZVSUYGVIUFUXAUXOUYKUXCUXRVTZUXBUXNUYJUYLFUXMUYIUYLUXGUYHUXJUXLUX
        CUXRCUXFWAWBWCWCWEAUFUXAUYKUYFAUXRUXAWFZWGZUYKUXBUYEFUXRVNZVOZFUXJVNZVO
        ZVNZUXBUYQVNZUYPVNZUYFUYNUXBUYJUYRUYNUYJFUYHVNZUYQFUXKVPVNZVNZFUWSVPVNZ
        VNZVLFPVPVNZVNZIWDVNZVKZVKUYPUYQVUJVKUYRUYNDTIGUXJUYHUXEVUIUXKUWSPUWTFU
        MUWTWHZDETUJUHUUAZVUIWHZUXEWHZAUXJUXKUWSUWTVKZWFUYMAFUCEWIVNZVKZVUORUXI
        ADEGUWRUXHVUPUWTFUCUHVUPWHZTIGUWTUMVUKUUBZAEGWJVKZWKUDVUTWFUWRUXHVUTWLE
        GWMAEGIKTWNUDUGURUJUKUMAKUAUBUSAGUUCVNUUHKUAVAUUDUUEZUTUUFUDVUTWQWOZVEV
        CWPVGWRZWSUYNTIGUXRCUXEUWSOPUWTUMVUKVUNAUYMUUGZACOPUWTVKZWFUYMVFWSZUUIA
        FDWFUYMVEWSZWTUYNVUBUYPUYQVUJUYNVUBUYEUYOVUFFOVPVNZVNZVLVUHVUIVKVKUYPUY
        NDTIGUXRCUXEVUIUWSOPUWTFUMVUKVULVUMVUNVVDVVFVVGWTUYNIVUIKUYOUYEWNVUFVVI
        VUHUKAKWNWFZUYMVVAWSZVUMAVUFKWFUYMADKFVUEADKVUEXADIXBVNZVUEXAADVVLTIVUE
        UWSVMVNZVULVVLWHZATIWJVKZWKZUWSVVOWFVUEVVMVVOWLTIWMZADVVOUCUWRADVVOEGUW
        RUXHUHTIGUMUUJZVVBXCZVCWRZUWSVVOWQWOZXCAKVVLVUEDAIKWNUKVVAXDZXEXGZVEWRZ
        WSZAVVIKWFUYMADKFVVHADKVVHXADVVLVVHXAADVVLTIVVHUYAVULVVNAVVPOVVOWFVVHUY
        AVVOWLVVQVBOVVOWQWOZXCAKVVLVVHDVWBXEXGZVEWRZWSZAVUHKWFUYMAVUHVVLKADVVLF
        VUGADVVLTIVUGPVMVNZVULVVNAVVPPVVOWFVUGVWJVVOWLVVQVDPVVOWQWOXCVEWRVWBXFZ
        WSZUYNUYOVUFVVIIWIVNZVKWFVUFVVIUYOXAZUYNUXRDTIVUEVVMVWMVVHUYAUWTFVUKUYN
        UXRTIUWSOUWTVUKVVDXHZVULVWMWHZVVGXIUYNIKUYOVWMWNVUFVVIUKVVKVWPVWEVWIXJX
        KZAVVIVUHUYEXAZUYMAUYEVVIVUHVWMVKWFVWRACDTIVVHUYAVWMVUGVWJUWTFVUKACTIOP
        UWTVUKVFXHVULVWPVEXIAIKUYEVWMWNVVIVUHUKVVAVWPVWHVWKXJXKZWSZXLXMWBUYNIVU
        IKUYQUYPWNVUDVUFVUHUKVVKVUMAVUDKWFUYMAVUDVVLKADVVLFVUCADVVLTIVUCUXKVMVN
        ZVULVVNAVVPUXKVVOWFVUCVXAVVOWLVVQADVVOFUWRVVSVEWRZUXKVVOWQWOXCVEWRVWBXF
        ZWSVWEVWLAVUDVUFUYQXAZUYMAUYQVUDVUFVWMVKWFVXDAUXJDTIVUCVXAVWMVUEVVMUWTF
        VUKAUXJTIUXKUWSUWTVUKVVCXHVULVWPVEXIAIKUYQVWMWNVUDVUFUKVVAVWPVXCVWDXJXK
        WSZUYNVWRVWNVUFVUHUYPXAVWTVWQVUFVVIVUHUYEUYOUUKXNXLXQWCUYNVXDUXBVUDWFZU
        YSVUAVTVXEAVXFUYMAUXBFFVUPVKZVUDADELVUPFUHVURUIURVEXRZADEVUPFUDFUGUHURV
        EVURVEXOXFWSZVUDVUFUXBUYPUYQXPXNUYNVUAUYTUYOVNZUYEVNZUYFUYNVWNUYTVUFWFV
        UAVXKVTVWQUYNVUDVUFUXBUYQVXEVXIWRVUFVVIUYTUYEUYOXPXNUYNVXJUYDUYEUYNVXJR
        UYOVNZUXQUYCUXSVOZVNZUYDUYNUYTRUYOUYNUYTRUXBFFVLUCEWDVNZVKVKRUYNDEVXORU
        XBVUPFFUDUCUGUHAEXSWFZUYMURWSZVVGVURAUCDWFUYMVCWSZVXOWHZVVGARVUQWFUYMVG
        WSZAUXBVXGWFUYMVXHWSUULUYNDEVXOLRVUPFUCUHVURUIVXQVVGVXSVXRVXTUUMXMXTUYN
        UXQUYORUCFVVMVKZVNZVOZVNZUXQVYBVNZUYOVNZVXNVXLUYNUCVUEVNZVUFVYBXAZUXQVY
        GWFZVYDVYFVTAVYHUYMAVYBVYGVUFVWMVKZWFVYHAUCFTWIVNZVKZVYJRVYAADTIVUEVVMV
        YKVWMUCFVULVYKWHZVWPVWAVCVEWPARVUQVYLVGEVUPTUCFVURUJUUNZUUOZWRAIKVYBVWM
        WNVYGVUFUKVVAVWPADKUCVUEVWCVCWRZVWDXJXKWSZAVYIUYMAUXQUCUCVUPVKZVYGADELV
        UPUCUHVURUIURVCXRZADEVUPUCUDUCUGUHURVCVURVCXOXFWSZVYGVUFUXQUYOVYBXPXNUY
        NUXQVYCVXMUYNUYOVYBVYGVUFVLVVIVUIVKVKUYCUXSVYGUCVVHVNZVLVVIVUIVKVKVYCVX
        MUYNUXRDTIRVUIVUEVVMVYKVVHUYAUWTUCFVUKVWOVULVYMVUMVXRVVGARVYLWFUYMVYOWS
        UUPUYNIVUIKVYBUYOWNVYGVUFVVIUKVVKVUMAVYGKWFUYMVYPWSZVWEVWIVYQVWQXLUYNIV
        UIKUXSUYCWNVYGWUAVVIUKVVKVUMWUBAWUAKWFUYMADKUCVVHVWGVCWRZWSZVWIUYNUXSVY
        GWUAVWMVKWFVYGWUAUXSXAZUYNUXRDTIVUEVVMVWMVVHUYAUWTUCVUKVWOVULVWPVXRXIUY
        NIKUXSVWMWNVYGWUAUKVVKVWPWUBWUDXJXKZAWUAVVIUYCXAZUYMAUYCWUAVVIVWMVKZWFW
        UGAVYLWUHRUYBADTIVVHUYAVYKVWMUCFVULVYMVWPVWFVCVEWPVYOWRAIKUYCVWMWNWUAVV
        IUKVVAVWPWUCVWHXJXKZWSXLYAWCUYNVYERUYOUYNVYEUXQRFUCVLUCVXOVKVKRUYNDEVXO
        RUXQVUPFUCUDUCUGUHVXQVXRVURVXRVXSVVGVXTAUXQVYRWFUYMVYSWSUUQUYNDEVXOLRVU
        PFUCUHVURUIVXQVVGVXSVXRVXTUUSXMXTYAUYNWUEVYIVXNUYDVTWUFVYTVYGWUAUXQUYCU
        XSXPXNUURXTXMXQUUTUVAAVIUFUXAUXKPUWTVKZUXMUXBUYOVNZUXOUWDUVSAUXAWUJVIUX
        AUXMVSZXAZUXMWUJWFVIUXAYBAUWLUWMUWDXAZWUMAUWDUWLUWMJWIVNZVKZWFWUNACRWUP
        VVEVUQUWCAUVTUWAGTUVQVKZWIVNZVKZUVTUWKVNZUWAUWKVNZWUOVKZUWCXAVVEVUQYCZW
        UPUWCXAAVVODYCZWUQJUWKUWBWURWUOUVTUWAGTWUQVVODWUQWHZVVRVULUVBZWURWHZWUO
        WHZAWUQJWJVKZWKZUEWVIWFZUWKUWBWVIWLWUQJWMZAWVKNWVIWFZADEGHIJKLNQTUAUBUD
        UEUGUHUIUJUKULUMUNUOUPUQURUSUTVAUVCZYDUEWVIWQWOZAOUCVVODVBVCYEZAPFVVODV
        DVEYEZWPAWUSWVBWVCWUPUWCAWUSVVEVYLYCWVCAGTPFWUQUWTVYKWUROUCVVODWVEVVRVU
        LVUSVYMVBVCVDVEWVGUVDVYLVUQVVEVYNUVEUVFZWVBWUPVTAWUPWVBUWLWUTUWMWVAWUOO
        UCUWKYFPFUWKYFYHYGYIYJXKVFVGYKAJUAUWDWUOUBUWLUWMULUSWVHAUWLJXBVNZUAAOUC
        WVSVVODUWKAWVDWVSWUQJUWKUWBWVFWVSWHZWVOXCZVBVCYKAJUAUBULUSXDZXFZAUWMWVS
        UAAPFWVSVVODUWKWWAVDVEYKWWBXFZXJXKZAUWLUXAUWMWUJUWDWULAUWDUXJCUXDUXKPVL
        QVMVNVKVKWULACDEFGHIJKLNOPQRTUAUBUCUDUEUGUHUIUJUKULUMUNUOUPUQURUSUTVAVB
        VCVDVEVFVGUVHAVVOGUXEVIUXJCUWTQPUWSOUXKUNATIGUMAVXPTXSWFURETUJUVGYQZAVV
        JIXSWFVVAIKWNUKUVIYQZUVJVVRVUSVVTVBVXBVDVUNVVCVFUVKXMZADEGHIJKLNOQTUAUB
        UCUDUEUGUHUIUJUKULUMUNUOUPUQURUSUTVAVBVCYLZADEGHIJKLNPQTUAUBFUDUEUGUHUI
        UJUKULUMUNUOUPUQURUSUTVAVDVEYLYMXKVIUXAWUJUXMWULWULWHYNYRWWHAUVSUFWUJWU
        KVSVTZUWMUWOUVSXAZABDEGHIJKLMNPQSTUAUBFUDUEUFUGUHUIUJUKULUMUNUOUPUQURUS
        UTVAVDVEVHYOZYDUXRUXMVTUXBUYOUXNFUXRUXMUVLWCYPAUWJUYEUYCVOZUWIVOUYGAUWH
        WWMUWIAUWHUYEUYCWUAVVIVLVUHVUIVKVKWWMACDTIVUINOPVYKRUWGUWTUCFUPWWFWWGVU
        LVYMVUMVUKVBVDVCVEUWGWHVFVYOUVMAIVUIKUYCUYEWNWUAVVIVUHUKVVAVUMWUCVWHVWK
        WUIVWSXLXMUVNAUFVJUXAWUAUXTVJVRZUYCVNUYEVNZUYFUWIWWMAUXAWUAUFUXAUXTVSZX
        AZUXTWUAWFUFUXAYBAUWLUWQUWIXAZWWQAUWIWWPVTZWWRABDEGHIJKLMNOQSTUAUBUCUDU
        EUFUGUHUIUJUKULUMUNUOUPUQURUSUTVAVBVCVHYOZYSZAUWLUXAUWQWUAUWIWWPAWWSWWR
        WWTYDZWWIADTINOUCUPWWFWWGVULVBVCUVRYMXKUFUXAWUAUXTWWPWWPWHYNYRWXBAVWRWU
        GWWMVJWUAWWOVSVTVWSWUIVJUYEUYCWUAVVIVUHUVOXNWWNUXTUYEUYCUVPYPXMYTAJUWPU
        AUWDUVSUBUWLUWMUWOULUSUWPWHZWWCWWDAUWOWVSUAAPFWVSVVODUWNAWVDWVSWUQJUWNU
        WFWVFWVTAWVJWVMUWNUWFWVIWLWVLAWVKWVMWVNYSNWVIWQWOZXCZVDVEYKWWBXFZWWEAWW
        JWWKWWLYSXLAJUWPUAUWIUWHUBUWLUWQUWOULUSWXCWWCAUWQWVSUAAOUCWVSVVODUWNWXE
        VBVCYKWWBXFZWXFWXAAUWHUWQUWOWUOVKZWFUWQUWOUWHXAACRWXHVVEVUQUWGAWUSUVTUW
        NVNZUWAUWNVNZWUOVKZUWGXAWVCWXHUWGXAAWVDWUQJUWNUWFWURWUOUVTUWAWVFWVGWVHW
        XDWVPWVQWPAWUSWXKWVCWXHUWGWVRWXKWXHVTAWXHWXKUWQWXIUWOWXJWUOOUCUWNYFPFUW
        NYFYHYGYIYJXKVFVGYKAJUAUWHWUOUBUWQUWOULUSWVHWXGWXFXJXKXLYT $.
    $}

    yoneda.m $e |- M = ( f e. ( O Func S ) , x e. B |->
      ( a e. ( ( ( 1st ` Y ) ` x ) ( O Nat S ) f ) |->
        ( ( a ` x ) ` ( .1. ` x ) ) ) ) $.
    $( Lemma for ~ yoneda .  (Contributed by Mario Carneiro, 28-Jan-2017.) $)
    yonedalem3 $p |- ( ph -> M e. ( Z ( ( Q Xc. O ) Nat T ) E ) ) $=
      ( vz vw vg vy cxpc co cnat wcel cfunc cxp c1st cfv chom cixp c2nd cop cco
      cv wceq wral wfn cmpt ovex mptex fnmpoi a1i wa wf ccat adantr crn wss cun
      chomf simprl simprr yonedalem3a simprd eqid cbs fucbas oppcbas xpcbas wbr
      wrel relfunc yonedalem1 simpld 1st2ndbr sylancr fovcdmda setcbas eleqtrrd
      funcf1 mpbird ralrimivva fveq2 df-ov eqtr4di oveq12d eleq12d ralxp sylibr
      elsetchom cmpo cvv fvexi mpoex eqeltri elixp sylanbrc w3a xp1st syl xp2nd
      simpr1 simpr2 simpr3 fuchom 1st2nd2 fveq2d opeq12d fveq12d oveq123d
      xpchom oppchom xpeq2i eqtrdi eleqtrd yonedalem3b 3eqtr4d isnat2 mpbir2and
      ralrimivvva ) ANSLEOVAVBZHVCVBZVBVDNUQOGVEVBZCVFZUQVNZSVGVHZVHZUUOLVGVHZV
      HZHVIVHZVBZVJVDZURVNZNVHZUSVNZUUOUVCSVKVHZVBZVHZUUQUVCUUPVHZVLZUVCUURVHZH
      VMVHZVBZVBZUVEUUOUVCLVKVHZVBZVHZUUONVHZUUQUUSVLZUVKUVLVBZVBZVOZUSUUOUVCUU
      KVIVHZVBZVPURUUNVPUQUUNVPANUUNVQZUVRUVAVDZUQUUNVPZUVBUWEAKBUUMCTBVNZRVGVH
      ZVHZKVNZOGVCVBZVBZUWHJVHUWHTVNZVHVHZVRZNUPTUWMUWOUWJUWKUWLVSVTWAWBAUVEUTV
      NZNVBZUVEUWQUUPVBZUVEUWQUURVBZUUTVBZVDZUTCVPUSUUMVPUWGAUXBUSUTUUMCAUVEUUM
      VDZUWQCVDZWCZWCZUXBUWSUWTUWRWDZUXFUWRTUWQUWIVHUVEUWLVBUWQJVHUWQUWNVHVHVRV
      OUXGUXFBCDEFGHIJKLUVEMNOPQUWQRSTUAUBUCUDUEUFUGUHUIUJUKADWEVDZUXEULWFAPQVD
      ZUXEUMWFZADWJVHWGIWHZUXEUNWFAEWJVHWGIWIPWHZUXEUOWFAUXCUXDWKAUXCUXDWLUPWMW
      NUXFHPUWRUUTQUWSUWTUFUXJUUTWOZUXFUWSHWPVHZPAUVEUWQUXNUUMCUUPAUUNUXNUUKHUU
      PUVFEOUUKUUMCUUKWOZOGEUGWQCDOUDUBWRWSZUXNWOZAUUKHVEVBZXAZSUXRVDZUUPUVFUXR
      WTUUKHXBZAUXTLUXRVDZACDEFGHIJLMOPQRSUAUBUCUDUEUFUGUHUIUJUKULUMUNUOXCZXDZS
      UXRXEXFXJXGUXFHPQUFUXJXHZXIUXFUWTUXNPAUVEUWQUXNUUMCUURAUUNUXNUUKHUURUVOUX
      PUXQAUXSUYBUURUVOUXRWTUYAAUXTUYBUYCWNZLUXRXEXFXJXGUYEXIXTXKXLUWFUXBUQUSUT
      UUMCUUOUVEUWQVLZVOZUVRUWRUVAUXAUYHUVRUYGNVHUWRUUOUYGNXMUVEUWQNXNXOUYHUUQU
      WSUUSUWTUUTUYHUUQUYGUUPVHUWSUUOUYGUUPXMUVEUWQUUPXNXOUYHUUSUYGUURVHUWTUUOU
      YGUURXMUVEUWQUURXNXOXPXQXRXSUQUUNUVANNKBUUMCUWPYAYBUPKBUUMCUWPOGVEVSCDWPU
      BYCYDYEYFYGAUWBUQURUSUUNUUNUWDAUUOUUNVDZUVCUUNVDZUVEUWDVDZYHZWCZUVCVGVHZU
      VCVKVHZNVBZUVEVGVHZUVEVKVHZUUOVGVHZUUOVKVHZVLZUYNUYOVLZUVFVBZVBZUYSUYTUUP
      VBZUYNUYOUUPVBZVLZUYNUYOUURVBZUVLVBZVBUYQUYRVUAVUBUVOVBZVBZUYSUYTNVBZVUEU
      YSUYTUURVBZVLZVUHUVLVBZVBUVNUWAUYMBUYQCDUYOEFGHIJKLUYSUYNMUYRNOPQUYTRSTUA
      UBUCUDUEUFUGUHUIUJUKAUXHUYLULWFAUXIUYLUMWFAUXKUYLUNWFAUXLUYLUOWFUYMUYIUYS
      UUMVDAUYIUYJUYKYLZUUOUUMCYIYJUYMUYIUYTCVDVUPUUOUUMCYKYJUYMUYJUYNUUMVDAUYI
      UYJUYKYMZUVCUUMCYIYJUYMUYJUYOCVDVUQUVCUUMCYKYJUYMUVEUYSUYNUWLVBZUYOUYTDVI
      VHZVBZVFZVDZUYQVURVDUYMUVEUWDVVAAUYIUYJUYKYNUYMUWDVURUYTUYOOVIVHZVBZVFVVA
      UYMUUNEOUUKUWLVVCUWCUUOUVCUXOUXPOGEUWLUGUWLWOYOVVCWOUWCWOZVUPVUQUUAVVDVUT
      VURDVUSOUYTUYOVUSWOUDUUBUUCUUDUUEZUVEVURVUTYIYJUYMVVBUYRVUTVDVVFUVEVURVUT
      YKYJUPUUFUYMUVDUYPUVHVUDUVMVUIUYMUVJVUGUVKVUHUVLUYMUUQVUEUVIVUFUYMUUQVUAU
      UPVHVUEUYMUUOVUAUUPUYMUYIUUOVUAVOVUPUUOUUMCYPYJZYQUYSUYTUUPXNXOZUYMUVIVUB
      UUPVHVUFUYMUVCVUBUUPUYMUYJUVCVUBVOVUQUVCUUMCYPYJZYQUYNUYOUUPXNXOYRUYMUVKV
      UBUURVHVUHUYMUVCVUBUURVVIYQUYNUYOUURXNXOZXPUYMUVDVUBNVHUYPUYMUVCVUBNVVIYQ
      UYNUYONXNXOUYMUVHUYQUYRVLZVUCVHVUDUYMUVEVVKUVGVUCUYMUUOVUAUVCVUBUVFVVGVVI
      XPUYMVVBUVEVVKVOVVFUVEVURVUTYPYJZYSUYQUYRVUCXNXOYTUYMUVQVUKUVRVULUVTVUOUY
      MUVSVUNUVKVUHUVLUYMUUQVUEUUSVUMVVHUYMUUSVUAUURVHVUMUYMUUOVUAUURVVGYQUYSUY
      TUURXNXOYRVVJXPUYMUVQVVKVUJVHVUKUYMUVEVVKUVPVUJUYMUUOVUAUVCVUBUVOVVGVVIXP
      VVLYSUYQUYRVUJXNXOUYMUVRVUANVHVULUYMUUOVUANVVGYQUYSUYTNXNXOYTUUGUUJAUQURN
      UUNUUKHUVLUSSLUWCUUTUULUULWOUXPVVEUXMUVLWOUYDUYFUUHUUI $.

    ${
      yonedainv.i $e |- I = ( Inv ` R ) $.
      yonedainv.n $e |- N =
        ( f e. ( O Func S ) , x e. B |-> ( u e. ( ( 1st ` f ) ` x ) |->
          ( y e. B |-> ( g e. ( y ( Hom ` C ) x ) |->
            ( ( ( x ( 2nd ` f ) y ) ` g ) ` u ) ) ) ) ) $.
      $( The Yoneda Lemma with explicit inverse.  (Contributed by Mario
         Carneiro, 29-Jan-2017.) $)
      yonedainv $p |- ( ph -> M ( Z I E ) N ) $=
        ( vz vh vw vb vk cfunc co cv cfv cmpt cnat eqid wcel simpld simprd c1st
        wbr wral wa wceq wf ccom cid cres ccat adantr chomf crn wss yonedalem3a
        simplrl simplrr simpr yonedalem4c wfn chom c2nd cbs mptex fveq2d simplr
        weq fveq1d mpteq12dv mpteq2dva adantl dffn5 sylib syl cvv mpbird fcompt
        fvex syl2anc eleq2d biimpa ffvelcdmda relfunc 1st2ndbr sylancr ad2antrr
        fveq1 funcf1 setcbas feq3d ffvelcdmd 3eqtr3d 3eqtrd eqtr4di eqtrd mpbid
        wrel cop elsetchom natcl fveq2 df-ov cxp cxpc fucbas oppcbas yonedalem1
        cinv xpcbas yonedalem3 wf1o cun simprl simprr fmpttd fvexi fnmpti simpl
        ccnv fveq12d oveq2d simpll oveq123d ovmpoa fneq1d mpbiri oppccat unssbd
        eqidd ssexd setccat evlf1 yonedalem21 feq123d fvmpt catidcl yonedalem4b
        fmpt3d ccid funcid oppcid setcid fvresi syldan mptresid nat1st2nd natfn
        yon11 oppchom eleqtrrdi nati yoncl funcf2 setcco eleqtrrd fvco3d catlid
        cco yon12 eqtr3d feqmptd 3eqtr4d eqfnfvd fcof1o syl22anc eqcom fovcdmda
        anbi2i setcinv ralrimivva oveq12d breq123d ralxp sylibr r19.21bi invfuc
        fnmpoi mpbi breqtrrdi ) ARVDTIVIVJZEUUAZVDVKZSVLZVMZSUDOQVJAVDUXSGTUUBV
        JZJHRUDOQJUUFVLZUYCJVNVJZUYAUNGTUYCUXREUYCVOTIGULUUCZEFTUIUGUUDZUUGZUYE
        VOAUDUYCJVIVJZVPZOUYIVPZAEFGHIJKLOPTUAUBUCUDUFUGUHUIUJUKULUMUNUOUPUQURU
        SUTUUEZVQZAUYJUYKUYLVRZVBUYDVOZABEFGHIJKLMOPRTUAUBUCUDUEUFUGUHUIUJUKULU
        MUNUOUPUQURUSUTVAUUHAUXTRVLZUYAUXTUDVSVLZVLZUXTOVSVLZVLZUYDVJZVTZVDUXSA
        VEVKZVFVKZRVJZVUCVUDSVJZVUCVUDUYQVJZVUCVUDUYSVJZUYDVJZVTZVFEWAVEUXRWAVU
        BVDUXSWAAVUJVEVFUXREAVUCUXRVPZVUDEVPZWBZWBZVUJVUGVUHVUEUUIZVUFVUEUUQZWC
        ZWBZVUNVUOVUPVUFWCZWBZVURVUNVUGVUHVUEWDZVUHVUGVUFWDZVUEVUFWEZWFVUHWGZWC
        VUFVUEWEZWFVUGWGZWCVUTVUNVUEUEVUDUCVSVLZVLZVUCTIVNVJZVJZVUDLVLZVUDUEVKZ
        VLZVLZVMZWCZVVAVUNBEFGHIJKLMOVUCPRTUAUBVUDUCUDUEUFUGUHUIUJUKULUMUNUOUPA
        FWHVPZVUMUQWIZAUAUBVPZVUMURWIZAFWJVLWKKWLZVUMUSWIZAGWJVLWKZKUUJUAWLZVUM
        UTWIZAVUKVULUUKZAVUKVULUULZVAWMVRZVUNVVBVUDVUCVSVLZVLZVVJVGVWJVGVKZVUFV
        LZVMZWDVUNVGVWJVWLVVJVUNVWKVWJVPZWBBCDVWKEFGHIJKLMNOVUCPSTUAUBVUDUCUDUF
        UGUHUIUJUKULUMUNUOUPVUNVVQVWNVVRWIVUNVVSVWNVVTWIVUNVWAVWNVWBWIVUNVWDVWN
        VWEWIAVUKVULVWNWNAVUKVULVWNWOVCVUNVWNWPWQZUUMVUNVUHVWJVUGVVJVUFVWMVUNVU
        FVWJWRZVUFVWMWCVUNVWPDVWJCENCVKZVUDFWSVLZVJZDVKZNVKZVUDVWQVUCWTVLZVJZVL
        ZVLZVMZVMZVMZVWJWRDVWJVXGVXHCEVXFEFXAUGUUNXBVXHVOUUOVUNVWJVUFVXHVUMVUFV
        XHWCAMBVUCVUDUXREDBVKZMVKZVSVLZVLZCENVWQVXIVWRVJZVWTVXAVXIVWQVXJWTVLZVJ
        ZVLZVLZVMZVMZVMZVXHSMVEXEZBVFXEZWBZDVXLVXSVWJVXGVYCVXIVUDVXKVWIVYCVXJVU
        CVSVYAVYBUUPXCVYAVYBWPUURVYCCEVXRVXFVYCVWQEVPZWBZNVXMVXQVWSVXEVYEVXIVUD
        VWQVWRVYAVYBVYDXDZUUSVYEVWTVXPVXDVYEVXAVXOVXCVYEVXIVUDVWQVWQVXNVXBVYEVX
        JVUCWTVYAVYBVYDUUTXCVYFVYEVWQUVGUVAXFXFXGXHXGVCDVWJVXGVUDVWIXPXBUVBXIUV
        CUVDVGVWJVUFXJXKZVUNETIOVUCVUDUOATWHVPZVUMAVVQVYHUQFTUIUVEXLWIAIWHVPZVU
        MAKXMVPZVYIAKUAUBURAVWCKUAUTUVFUVHZIKXMUJUVIXLWIUYGVWFVWGUVJZVUNEFGHIJK
        LOVUCPTUAUBVUDUCUDUFUGUHUIUJUKULUMUNUOUPVVRVVTVWBVWEVWFVWGUVKZUVLXNZVUN
        VVCVHVUHVHVKZVUFVLZVUEVLZVMZVVDVUNVVAVVBVVCVYRWCVWHVYNVHVUEVUFVUHVUGVUH
        XOXQVUNVYRVHVUHVYOVMVVDVUNVHVUHVYQVYOVUNVYOVUHVPZVYOVWJVPZVYQVYOWCVUNVY
        SVYTVUNVUHVWJVYOVYLXRXSVUNVYTWBZVYQVYPVVOVLZVVKVUDVYPVLZVLZVYOWUAVYPVUE
        VVOWUAVVPVVAWUABEFGHIJKLMOVUCPRTUAUBVUDUCUDUEUFUGUHUIUJUKULUMUNUOUPVUNV
        VQVYTVVRWIZVUNVVSVYTVVTWIZVUNVWAVYTVWBWIZVUNVWDVYTVWEWIZAVUKVULVYTWNZAV
        UKVULVYTWOZVAWMVQXFWUAVYPVVJVPWUBWUDWCVUNVWJVVJVYOVUFVUNVGVWJVWLVVJVUFV
        YGVWOUVPXTUEVYPVVNWUDVVJVVOVVLVYPWCVVKVVMWUCVUDVVLVYPYEXFVVOVOZVVKWUCXP
        UVMXLWUAWUDVYOVVKVUDVUDVXBVJZVLZVLVYOWFVWJWGZVLZVYOWUABCDVYOEFVUDGHIJKL
        MNOVUCVVKPSTUAUBVUDUCUDUFUGUHUIUJUKULUMUNUOUPWUEWUFWUGWUHWUIWUJVCVUNVYT
        WPWUJWUAEFLVWRVUDUGVWRVOZUHWUEWUJUVNUVOWUAVYOWUMWUNWUAVUDTUVQVLZVLZWULV
        LVWJIUVQVLZVLWUMWUNWUAETWUQIVWIVXBWUSVUDUYGWUQVOWUSVOZWUAUXRYOZVUKVWIVX
        BUXRVTZTIYAZWUIVUCUXRYBZYCZWUJUVRWUAWURVVKWULWUAVUDWUQLWUAVVQWUQLWCWUEL
        FTUIUHUVSXLXFXCWUAIKWUSXMVWJUJWUTAVYJVUMVYTVYKYDZWUAEKVUDVWIWUAEKVWIWDZ
        EIXAVLZVWIWDZWUAEWVHTIVWIVXBUYGWVHVOZWVEYFWUAKWVHVWIEWUAIKXMUJWVFYGYHXN
        WUJYIUVTYJXFVYTWUOVYOWCVUNVWJVYOUWAXIYKYKUWBXHVHVUHUWCYLYMVUNVVEVGVUGVW
        KVUEVLZVUFVLZVMZVVFVUNVVBVVAVVEWVMWCVYNVWHVGVUFVUEVUGVUHVUGXOXQVUNWVMVG
        VUGVWKVMVVFVUNVGVUGWVLVWKVUNVWKVUGVPZWBZVDEWVLVWKWVOWVLETIVVHVSVLZVVHWT
        VLZVWIVXBVVIVVIVOZWVOWVLTIVVHVUCVVIWVRWVOBCDWVKEFGHIJKLMNOVUCPSTUAUBVUD
        UCUDUFUGUHUIUJUKULUMUNUOUPVUNVVQWVNVVRWIZVUNVVSWVNVVTWIZVUNVWAWVNVWBWIZ
        VUNVWDWVNVWEWIZAVUKVULWVNWNZAVUKVULWVNWOZVCVUNVUGVWJVWKVUEVUNVVAVUGVWJV
        UEWDVWHVUNVUHVWJVUEVUGVYLYHYNXTZWQUWDZUYGUWEWVOVWKETIWVPWVQVWIVXBVVIWVR
        WVOVWKTIVVHVUCVVIWVRVUNWVNVWKVVJVPZVUNVUGVVJVWKVYMXRXSZUWDZUYGUWEWVOUXT
        EVPZWBZVHUXTWVPVLZVYOUXTWVLVLZVLZVMVHWWLVYOUXTVWKVLZVLZVMWWMWWOWWKVHWWL
        WWNWWPWWKVYOWWLVPZVYOUXTVUDVWRVJZVPZWWNWWPWCWWKWWQWWSWWKWWLWWRVYOWWKEFV
        WRVUDUCUXTUFUGWVOVVQWWJWVSWIZWVOVULWWJWWDWIZWUPWVOWWJWPZUWFXRXSWWKWWSWB
        ZWWNWVKVYOVUDUXTVXBVJZVLZVLVVKVUDVWKVLZVLZWXEVLZWWPWXCBCDWVKEFUXTGHIJKL
        MNOVUCVYOPSTUAUBVUDUCUDUFUGUHUIUJUKULUMUNUOUPWWKVVQWWSWWTWIZWVOVVSWWJWW
        SWVTYDZWVOVWAWWJWWSWWAYDZWVOVWDWWJWWSWWBYDZWVOVUKWWJWWSWWCYDZWWKVULWWSW
        XAWIZVCWVOWVKVWJVPWWJWWSWWEYDWVOWWJWWSXDZWWKWWSWPZUVOWXCWVKWXGWXEWXCWVK
        VWKVVOVLZWXGWXCVWKVUEVVOWXCVVPVVAWXCBEFGHIJKLMOVUCPRTUAUBVUDUCUDUEUFUGU
        HUIUJUKULUMUNUOUPWXIWXJWXKWXLWXMWXNVAWMVQXFWXCWWGWXQWXGWCWVOWWGWWJWWSWW
        HYDUEVWKVVNWXGVVJVVOUEVGXEVVKVVMWXFVUDVVLVWKYEXFWUKVVKWXFXPUVMXLYMXCWXC
        VVKVYOVUDUXTWVQVJZVLZVLZWWOVLZWXHWWPWXCVVKWWOWXSWEZVLVVKWXEWXFWEZVLZWYA
        WXHWXCVVKWYBWYCWXCWWOWXSVUDWVPVLZWWLYPUXTVWIVLZIUWPVLZVJVJWXEWXFWYEVWJY
        PWYFWYGVJVJWYBWYCWXCVWKETIVYOWYGWVPWVQTWSVLZVWIVXBVVIVUDUXTWVRWVOVWKWVP
        WVQYPVWIVXBYPVVIVJZVPZWWJWWSWWIYDUYGWYHVOZWYGVOZWXNWXOWXCVYOWWRVUDUXTWY
        HVJZWXPFVWRTVUDUXTWUPUIUWGUWHZUWIWXCIWYGKWXSWWOXMWYEWWLWYFUJWWKVYJWWSWV
        OVYJWWJAVYJVUMWVNVYKYDZWIZWIZWYLWVOWYEKVPWWJWWSWVOEKVUDWVPWVOEKWVPWDEWV
        HWVPWDWVOEWVHTIWVPWVQUYGWVJWVOWVAVVHUXRVPWVPWVQUXRVTZWVCWVOEUXRVUDVVGAE
        UXRVVGWDVUMWVNAEUXRFGVVGUCWTVLZUGUYFAFGVIVJZYOUCWYTVPVVGWYSWYTVTFGYAAFG
        IKTXMUCUFUQUIUJULVYKUSUWJUCWYTYBYCYFYDWWDYIVVHUXRYBYCZYFWVOKWVHWVPEWVOI
        KXMUJWYOYGZYHXNZWWDYIZYDZWWKWWLKVPWWSWVOEKUXTWVPXUCXTZWIZWWKWYFKVPWWSWV
        OEKUXTVWIWVOWVGWVIWVOEWVHTIVWIVXBUYGWVJWVOWVAVUKWVBWVCWWCWVDYCYFWVOKWVH
        VWIEXUBYHXNZXTZWIZWXCWXSWYEWWLIWSVLZVJZVPWYEWWLWXSWDWXCWYMXULVYOWXRWXCE
        TIWVPWVQWYHXUKVUDUXTUYGWYKXUKVOZWVOWYRWWJWWSXUAYDWXNWXOUWKWYNYIWXCIKWXS
        XUKXMWYEWWLUJWYQXUMXUEXUGYQYNZWWKWWLWYFWWOWDZWWSWWKWWOWWLWYFXUKVJZVPXUO
        WWKVWKETIWVPWVQXUKVWIVXBVVIUXTWVRWVOWYJWWJWWIWIUYGXUMWXBYRWWKIKWWOXUKXM
        WWLWYFUJWYPXUMXUFXUIYQYNZWIUWLWXCIWYGKWXFWXEXMWYEVWJWYFUJWYQWYLXUEWVOVW
        JKVPWWJWWSWVOEKVUDVWIXUHWWDYIZYDZXUJWVOWYEVWJWXFWDZWWJWWSWVOWXFWYEVWJXU
        KVJVPXUTWVOVWKETIWVPWVQXUKVWIVXBVVIVUDWVRWWIUYGXUMWWDYRWVOIKWXFXUKXMWYE
        VWJUJWYOXUMXUDXURYQYNZYDWXCWXEVWJWYFXUKVJZVPVWJWYFWXEWDWXCWYMXVBVYOWXDW
        XCETIVWIVXBWYHXUKVUDUXTUYGWYKXUMWXCWVAVUKWVBWVCWXMWVDYCWXNWXOUWKWYNYIWX
        CIKWXEXUKXMVWJWYFUJWYQXUMXUSXUJYQYNUWLYJXFWXCWYEWWLVVKWWOWXSXUNWVOVVKWY
        EVPWWJWWSWVOVVKVUDVUDVWRVJZWYEWVOEFLVWRVUDUGWUPUHWVSWWDUVNZWVOEFVWRVUDU
        CVUDUFUGWVSWWDWUPWWDUWFUWMZYDUWNWVOWYDWXHWCWWJWWSWVOWYEVWJVVKWXEWXFXVAX
        VEUWNYDYJWXCWXTVYOWWOWXCWXTVVKVYOUXTVUDYPVUDFUWPVLZVJVJVYOWXCEFXVFVYOVV
        KVWRUXTVUDUCVUDUFUGWXIWXNWUPWXNXVFVOZWXOWXPWVOVVKXVCVPWWJWWSXVDYDUWQWXC
        EFXVFLVYOVWRUXTVUDUGWUPUHWXIWXOXVGWXNWXPUWOYMXCUWRYKUWBXHWWKVHWWLWYFWWM
        WWKWWMXUPVPWWLWYFWWMWDWWKWVLETIWVPWVQXUKVWIVXBVVIUXTWVRWVOWVLWYIVPWWJWW
        FWIUYGXUMWXBYRWWKIKWWMXUKXMWWLWYFUJWYPXUMXUFXUIYQYNUWSWWKVHWWLWYFWWOXUQ
        UWSUWTUXAXHVGVUGUWCYLYMVUGVUHVUEVUFUXBUXCVUSVUQVUOVUPVUFUXDUXFXKVUNJUAV
        UEVUFUYDUBVUGVUHUKVVTAVUCVUDUAUXREUYQAUXSUAUYQWDUXSJXAVLZUYQWDAUXSXVHUY
        CJUYQUDWTVLZUYHXVHVOZAUYIYOZUYJUYQXVIUYIVTUYCJYAZUYMUDUYIYBYCYFAUAXVHUY
        QUXSAJUAUBUKURYGZYHXNUXEAVUCVUDUAUXREUYSAUXSUAUYSWDUXSXVHUYSWDAUXSXVHUY
        CJUYSOWTVLZUYHXVJAXVKUYKUYSXVNUYIVTXVLUYNOUYIYBYCYFAUAXVHUYSUXSXVMYHXNU
        XEUYOUXGXNUXHVUBVUJVDVEVFUXREUXTVUCVUDYPZWCZUYPVUEUYAVUFVUAVUIXVPUYPXVO
        RVLVUEUXTXVORYSVUCVUDRYTYLXVPUYRVUGUYTVUHUYDXVPUYRXVOUYQVLVUGUXTXVOUYQY
        SVUCVUDUYQYTYLXVPUYTXVOUYSVLVUHUXTXVOUYSYSVUCVUDUYSYTYLUXIXVPUYAXVOSVLV
        UFUXTXVOSYSVUCVUDSYTYLUXJUXKUXLUXMUXNSUXSWRSUYBWCMBUXREVXTSVCDVXLVXSVXI
        VXKXPXBUXOVDUXSSXJUXPUXQ $.

      $( Lemma for ~ yonffth .  (Contributed by Mario Carneiro,
         29-Jan-2017.) $)
      yonffthlem $p |- ( ph -> Y e. ( ( C Full Q ) i^i ( C Faith Q ) ) ) $=
        ( vz vw vv vh c1st cfv c2nd cop cful co cfth cin wrel wcel wceq relfunc
        cfunc cvv chomf crn unssbd ssexd yoncl 1st2nd sylancr cv chom cnat wf1o
        wbr wral 1st2ndbr wa ciso cxp fveq2 eqtr4di oveq12d eleq12d cxpc fucbas
        ccat yonedalem1 simpld funcrcl syl simprd fuccat eqid yonedainv inviso2
        df-ov oppcbas xpcbas fuciso mpbid adantr funcf1 simprr ffvelcdmd simprl
        yon11 wss eleqtrrd eqeltrrd sseldd wfn simpr eqtr4d ffvelcdmda ad2antrr
        wf cmpt feqmptd mpteq2dva sylib 3eqtr4d opelxpd rspcdva oppccat setccat
        evlf1 eqtrd cun yonedalem21 eleqtrd setcbas fuchom unssad homffn fnovrn
        cbs homfval mp3an2i setciso cco ad3antrrr simpllr yon12 yon2 mpteq12dva
        eqcomd funcf2 nat1st2nd natcl elsetchom biimpar yonedalem4a natfn dffn5
        eleq2d f1of f1oeq1d ralrimivva isffth2 sylanbrc df-br eqeltrd ) AUCUCVH
        VIZUCVJVIZVKZFGVLVMFGVNVMVOZAFGVTVMZVPZUCUWFVQZUCUWDVRFGVSZAFGIKTWAUCUF
        UQUIUJULAKUAUBURAGWBVIZWCZKUAUTWDZWEZUSWFZUCUWFWGWHAUWBUWCUWEWMZUWDUWEV
        QAUWBUWCUWFWMZVDWIZVEWIZFWJVIZVMZUWQUWBVIZUWRUWBVIZTIWKVMZVMZUWQUWRUWCV
        MZWLZVEEWNVDEWNUWOAUWGUWHUWPUWIUWNUCUWFWOWHZAUXFVDVEEEAUWQEVQZUWREVQZWP
        ZWPZUWTUXDUXBUWQSVMZWLZUXFUXKUXLUWTUXDJWQVIZVMZVQUXMUXKUXLUXBUWQOVHVIZV
        MZUXBUWQUDVHVIZVMZUXNVMZUXOUXKVFWIZSVIZUYAUXPVIZUYAUXRVIZUXNVMZVQZUXLUX
        TVQVFTIVTVMZEWRZUXBUWQVKZUYAUYIVRZUYBUXLUYEUXTUYJUYBUYISVIUXLUYAUYISWSU
        XBUWQSXOWTUYJUYCUXQUYDUXSUXNUYJUYCUYIUXPVIUXQUYAUYIUXPWSUXBUWQUXPXOWTUY
        JUYDUYIUXRVIUXSUYAUYIUXRWSUXBUWQUXRXOWTXAXBAUYFVFUYHWNZUXJASOUDGTXCVMZJ
        WKVMZVMVQZUYKASOUDHWQVIZVMVQUYNUYKWPAUYLJVTVMZHRSUYOQUDOUYLJHUNXDVBAUYL
        JHUNAUYLXEVQZJXEVQZAUDUYPVQZUYQUYRWPAUYSOUYPVQZAEFGHIJKLOPTUAUBUCUDUFUG
        UHUIUJUKULUMUNUOUPUQURUSUTXFZXGZUYLJUDXHXIZXGAUYQUYRVUCXJXKVUBAUYSUYTVU
        AXJZUYOXLZABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPUQURUSUTV
        AVBVCXMXNAVFSUYHUYLJHOUDUYOUXNUYMUNGTUYLUYGEUYLXLTIGULXDZEFTUIUGXPZXQUY
        MXLVUDVUBVUEUXNXLZXRXSXJXTUXKUXBUWQUYGEUXKEUYGUWRUWBAEUYGUWBYOZUXJAEUYG
        FGUWBUWCUGVUFUXGYAZXTZAUXHUXIYBZYCZAUXHUXIYDZUUAUUBUXKUXQUWTUXSUXDUXNUX
        KUXQUWQUXBVHVIZVIZUWTUXKETIOUXBUWQUOATXEVQZUXJAFXEVQZVUQUQFTUIUUCXIXTAI
        XEVQZUXJAKWAVQZVUSUWMIKWAUJUUDXIXTVUGVUMVUNUUEUXKEFUWSUWRUCUWQUFUGAVURU
        XJUQXTZVULUWSXLZVUNYEZUUFUXKEFGHIJKLOUXBPTUAUBUWQUCUDUFUGUHUIUJUKULUMUN
        UOUPVVAAUAUBVQZUXJURXTZAFWBVIWCKYFZUXJUSXTZAUWKKUUGUAYFZUXJUTXTZVUMVUNU
        UHXAUUIUXKJUAUXLUXNUBUWTUXDUKVVEUXKKUAUWTAKUAYFUXJUWLXTUXKVUPUWTKVVCUXK
        VUPIUUOVIZKUXKEVVJUWQVUOUXKEVVJTIVUOUXBVJVIZVUGVVJXLZUXKUYGVPZUXBUYGVQZ
        VUOVVKUYGWMTIVSZVUMUXBUYGWOWHYAZVUNYCAKVVJVRZUXJAIKWAUJUWMUUJXTZYGYHYIU
        XKUXAUXBUWJVMZUXDUAUXKUYGGUWJUXCUXAUXBUWJXLZVUFTIGUXCULUXCXLZUUKZUXKEUY
        GUWQUWBVUKVUNYCZVUMUUPUXKUWKUAVVSAUWKUAYFUXJAUWKKUAUTUULXTUWJUYGUYGWRYJ
        UXKUXAUYGVQZVVNVVSUWKVQUYGGUWJVVTVUFUUMVWCVUMUYGUYGUXAUXBUWJUUNUUQYIYHV
        UHUURXSZUXKUWTUXDUXLUXEUXKVGUWTVGWIZUXLVIZYPVGUWTVWFUXEVIZYPUXLUXEUXKVG
        UWTVWGVWHUXKVWFUWTVQZWPZCENCWIZUWQUWSVMZVWFNWIZUWQVWKVVKVMVIVIZYPZYPCEV
        WKVWHVIZYPZVWGVWHVWJCEVWOVWPVWJVWKEVQZWPZVWONVWKUXAVHVIZVIZVWMVWPVIZYPV
        WPVWSNVWLVWNVXAVXBVWSVXAVWLVWSEFUWSUWQUCVWKUFUGVWJVURVWRUXKVURVWIVVAXTZ
        XTZVWJUXHVWRUXKUXHVWIVUNXTZXTZVVBVWJVWRYKZYEUVEVWSVWMVWLVQZWPZVWNVWFVWM
        VWKUWQVKUWRFUUSVIZVMVMVXBVXIEFVXJVWMVWFUWSVWKUWRUCUWQUFUGVWSVURVXHVXDXT
        ZUXKUXIVWIVWRVXHVULUUTZVVBVWSUXHVXHVXFXTZVXJXLZVWSVWRVXHVXGXTZVWSVXHYKZ
        UXKVWIVWRVXHUVAZUVBVXIEFVXJVWFVWMUWSVWKUWQUCUWRUFUGVXKVXMVVBVXLVXNVXOVX
        QVXPUVCYLUVDVWSNVXAVWKVUOVIZVWPVWSVWPVXAVXRIWJVIZVMVQVXAVXRVWPYOVWSVWHE
        TIVWTUXAVJVIZVXSVUOVVKUXCVWKVWAVWJVWHVWTVXTVKVUOVVKVKUXCVMVQVWRVWJVWHTI
        UXAUXBUXCVWAUXKUWTUXDVWFUXEUXKEFGUWBUWCUWSUXCUWQUWRUGVVBVWBAUWPUXJUXGXT
        VUNVULUVFZYMUVGZXTVUGVXSXLZVXGUVHVWSIKVWPVXSWAVXAVXRUJUXKVUTVWIVWRAVUTU
        XJUWMXTYNVYCVWSVXAVVJKVWJEVVJVWKVWTVWJEVVJTIVWTVXTVUGVVLVWJVVMVWDVWTVXT
        UYGWMVVOVWJEUYGUWQUWBAVUIUXJVWIVUJYNVXEYCUXAUYGWOWHYAYMUXKVVQVWIVWRVVRY
        NZYGVWSVXRVVJKVWJEVVJVWKVUOUXKEVVJVUOYOVWIVVPXTYMVYDYGUVIXSYQYLYRVWJBCD
        VWFEFGHIJKLMNOUXBPSTUAUBUWQUCUDUFUGUHUIUJUKULUMUNUOUPVXCUXKVVDVWIVVEXTU
        XKVVFVWIVVGXTUXKVVHVWIVVIXTUXKVVNVWIVUMXTVXEVCUXKVWFVUPVQVWIUXKVUPUWTVW
        FVVCUVNUVJUVKVWJVWHEYJVWHVWQVRVWJVWHETIVWTVXTVUOVVKUXCVWAVYBVUGUVLCEVWH
        UVMYSYTYRUXKVGUWTUXDUXLUXKUXMUWTUXDUXLYOVWEUWTUXDUXLUVOXIYQUXKVGUWTUXDU
        XEVYAYQYTUVPXSUVQVDVEEFGUWBUWCUWSUXCUGVVBVWBUVRUVSUWBUWCUWEUVTYSUWA $.
    $}

    yoneda.i $e |- I = ( Iso ` R ) $.
    $( The Yoneda Lemma.  There is a natural isomorphism between the functors
       ` Z ` and ` E ` , where ` Z ( F , X ) ` is the natural transformations
       from ` Yon ( X ) = Hom ( - , X ) ` to ` F ` , and
       ` E ( F , X ) = F ( X ) ` is the evaluation functor.  Here we need two
       universes to state the claim: the smaller universe ` U ` is used for
       forming the functor category
       ` Q = C ` <HTML><sup>op</sup></HTML> ` -> SetCat ( U ) ` , which itself
       does not (necessarily) live in ` U ` but instead is an element of the
       larger universe ` V ` . (If ` U ` is a Grothendieck universe, then it
       will be closed under this "presheaf" operation, and so we can set
       ` U = V ` in this case.)
       (Contributed by Mario Carneiro, 29-Jan-2017.) $)
    yoneda $p |- ( ph -> M e. ( Z I E ) ) $=
      ( vu vy vg cxpc co cfunc cv c1st cfv chom c2nd cmpt cmpo cinv fucbas eqid
      ccat wcel yonedalem1 simpld funcrcl syl simprd fuccat yonedainv inviso1
      wa ) AEPVBVCZHVDVCZFOKBPGVDVCCUSBVEZKVEZVFVGVGUTCVAUTVEZWHDVHVGVCUSVEVAVE
      WHWJWIVIVGVCVGVGVJVJVJVKZNFVLVGZTLWFHFUJVMWLVNZAWFHFUJAWFVOVPZHVOVPZATWGV
      PZWNWOWEAWPLWGVPZACDEFGHIJLMPQRSTUBUCUDUEUFUGUHUIUJUKULUMUNUOUPVQZVRZWFHT
      VSVTZVRAWNWOWTWAWBWSAWPWQWRWAURABUTUSCDEFGHIJKVALMWLOWKPQRSTUAUBUCUDUEUFU
      GUHUIUJUKULUMUNUOUPUQWMWKVNWCWD $.
  $}

  ${
    $d a f g u x y C $.  $d a f g u x y O $.  $d a f g u x y ph $.
    $d a f g u x y Q $.  $d a f g u x y S $.  $d a f g u x y Y $.
    $d f g u y U $.
    yonffth.y $e |- Y = ( Yon ` C ) $.
    yonffth.o $e |- O = ( oppCat ` C ) $.
    yonffth.s $e |- S = ( SetCat ` U ) $.
    yonffth.q $e |- Q = ( O FuncCat S ) $.
    yonffth.c $e |- ( ph -> C e. Cat ) $.
    yonffth.u $e |- ( ph -> U e. V ) $.
    yonffth.h $e |- ( ph -> ran ( Homf ` C ) C_ U ) $.
    $( The Yoneda Lemma.  The Yoneda embedding, the curried Hom functor, is
       full and faithful, and hence is a representation of the category ` C `
       as a full subcategory of the category ` Q ` of presheaves on ` C ` .
       (Contributed by Mario Carneiro, 29-Jan-2017.) $)
    yonffth $p |- ( ph -> Y e. ( ( C Full Q ) i^i ( C Faith Q ) ) ) $=
      ( vx cfv co cv eqid vy vu vf vg va cbs cxpc chomf crn cun csetc cfuc ccid
      cevlf chof cinv cfunc c1st cnat cmpt cmpo chom c2nd cvv ctpos c2ndf ccofu
      cop c1stf cprf wcel fvex rnex unexg sylancr ssidd yonffthlem ) APUAUBBUFQ
      ZBCCFUGRCUHQZUIZEUJZUKQZULRZDWBEBUMQZUCUDFDUNRZCUOQZWCUPQZUCPFDUQRZVRUEPS
      ZHURQZQUCSZFDUSRRWIWDQWIUESQQUTVAZUCPWHVRUBWIWKURQQUAVRUDUASZWIBVBQRUBSUD
      SWIWMWKVCQRQQUTUTUTVAZFWAVDHWFWJHVCQVEVHCFVFRVGRCFVIRVJRVGRZUEIVRTWDTJKWB
      TLWFTWCTWETWOTMAVTVDVKEGVKWAVDVKVSCUHVLVMNVTEVDGVNVOOAWAVPWLTWGTWNTVQ $.
  $}

  ${
    $d x y C $.  $d y F $.  $d x y ph $.  $d x y Y $.
    yoniso.y $e |- Y = ( Yon ` C ) $.
    yoniso.o $e |- O = ( oppCat ` C ) $.
    yoniso.s $e |- S = ( SetCat ` U ) $.
    yoniso.d $e |- D = ( CatCat ` V ) $.
    yoniso.b $e |- B = ( Base ` D ) $.
    yoniso.i $e |- I = ( Iso ` D ) $.
    yoniso.q $e |- Q = ( O FuncCat S ) $.
    yoniso.e $e |- E = ( Q |`s ran ( 1st ` Y ) ) $.
    yoniso.v $e |- ( ph -> V e. X ) $.
    yoniso.c $e |- ( ph -> C e. B ) $.
    yoniso.u $e |- ( ph -> U e. W ) $.
    yoniso.h $e |- ( ph -> ran ( Homf ` C ) C_ U ) $.
    yoniso.eb $e |- ( ph -> E e. B ) $.
    yoniso.1 $e |- ( ( ph /\ ( x e. ( Base ` C ) /\ y e. ( Base ` C ) ) ) ->
      ( F ` ( x ( Hom ` C ) y ) ) = y ) $.
    $( If the codomain is recoverable from a hom-set, then the Yoneda embedding
       is injective on objects, and hence is an isomorphism from ` C ` into a
       full subcategory of a presheaf category.  (Contributed by Mario
       Carneiro, 30-Jan-2017.) $)
    yoniso $p |- ( ph -> Y e. ( C I E ) ) $=
      ( co wcel cful cfth cin cbs cfv c1st wf1o c2nd cop wrel wceq relfunc ccat
      cfunc catcbas inss2 eqsstrdi sseldd yoncl 1st2nd sylancr yonffth eqeltrrd
      wbr crn cvv eqid oppccat syl setccat fuccat fvex rnex a1i wfn wf 1st2ndbr
      fucbas funcf1 ffnd dffn3 sylib ffthres2c df-br 3bitr3g eqeltrd wf1 cv weq
      mpbid wi wa fveq2 fveq1d fveq2d simpl jca eleq1w anbi2d 2fveq3 id eqeq12d
      wral imbi12d adantr simprr simprl yon11 eqtrd chvarvv imbitrid ralrimivva
      chom sylan2 dff13 sylanbrc f1f1orn wss ressbas2 f1oeq3d catciso mpbir2and
      frnd ) AQEJLULUMQEJUNULEJUOULUPZUMEUQURZJUQURZQUSURZUTZAQYTQVAURZVBZYQAEG
      VGULZVCZQUUDUMZQUUCVDEGVEZAEGHIMOQRADVFEADNVFUPVFADFNPUAUBUFVHNVFVIVJUGVK
      ZSTUDUHUIVLZQUUDVMVNZAUUCEGUNULEGUOULUPZUMZUUCYQUMZAQUUCUUKUUJAEGHIMOQRST
      UDUUHUHUIVOVPAYTUUBUUKVQYTUUBYQVQUULUUMAYREGYTVRZJYTUUBVSYRVTZUEAMHGUDAEV
      FUMZMVFUMUUHEMSWAWBAIOUMHVFUMUHHIOTWCWBWDUUNVSUMAYTQUSWEWFWGAYTYRWHYRUUNY
      TWIAYRMHVGULZYTAYRUUQEGYTUUBUUOMHGUDWKZAUUEUUFYTUUBUUDVQUUGUUIQUUDWJVNWLZ
      WMYRYTWNWOWPYTUUBUUKWQYTUUBYQWQWRXCWSAYRUUNYTUTZUUAAYRUUQYTWTZUUTAYRUUQYT
      WIBXAZYTURZCXAZYTURZVDZBCXBZXDZCYRXPBYRXPUVAUUSAUVHBCYRYRUVFUVBUVCUSURZUR
      ZKURZUVBUVEUSURZURZKURZVDAUVBYRUMZUVDYRUMZXEZXEZUVGUVFUVJUVMKUVFUVBUVIUVL
      UVCUVEUSXFXGXHUVRUVKUVBUVNUVDUVQAUVOUVOXEZUVKUVBVDZUVQUVOUVOUVOUVPXIZUWAX
      JUVRUVNUVDVDZXDAUVSXEZUVTXDCBCBXBZUVRUWCUWBUVTUWDUVQUVSAUWDUVPUVOUVOCBYRX
      KXLXLUWDUVNUVKUVDUVBUWDUVMUVJKUWDUVBUVLUVIUVDUVBUSYTXMXGXHUWDXNXOXQUVRUVN
      UVBUVDEYFURZULZKURUVDUVRUVMUWFKUVRYREUWEUVDQUVBRUUOAUUPUVQUUHXRAUVOUVPXSU
      WEVTAUVOUVPXTYAXHUKYBZYCYGUWGXOYDYEBCYRUUQYTYHYIYRUUQYTYJWBAUUNYSYRYTAUUN
      UUQYKUUNYSVDAYRUUQYTUUSYPUUNUUQJGUEUURYLWBYMXCADFYRYSNQLPEJUAUBUUOYSVTUFU
      GUJUCYNYO $.
  $}

