$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Structure builders
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Structure builder restriction operator
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x .0. $.  $d x A $.  $d x B $.  $d x R $.  $d x S $.
    ress0g.s $e |- S = ( R |`s A ) $.
    ress0g.b $e |- B = ( Base ` R ) $.
    ress0g.0 $e |- .0. = ( 0g ` R ) $.
    $( ` 0g ` is unaffected by restriction.  This is a bit more generic than
       ~ submnd0 (Contributed by Thierry Arnoux, 23-Oct-2017.) $)
    ress0g $p |- ( ( R e. Mnd /\ .0. e. A /\ A C_ B ) -> .0. = ( 0g ` S ) ) $=
      ( vx cmnd wcel wss w3a cplusg cfv cbs wceq cvv co syl2anc eqeltri sylancl
      ressbas2 3ad2ant3 simp3 fvex ssexg eqid ressplusg syl simp2 simpl1 sselda
      cv wa mndlid mndrid grpidd ) CJKZEAKZABLZMZIACNOZDEVAUSADPOQUTABDCFGUCUDV
      BARKZVCDNOQVBVABRKVDUSUTVAUEZBCPORGCPUFUAABRUGUBAVCCDRFVCUHZUIUJUSUTVAUKV
      BIUNZAKZUOZUSVGBKZEVGVCSVGQUSUTVAVHULZVBABVGVEUMZBVCCVGEGVFHUPTVIUSVJVGEV
      CSVGQVKVLBVCCVGEGVFHUQTUR $.
  $}

  ${
    $d x y .+^ $.  $d x y A $.  $d x y B $.  $d x y H $.
    ressplusf.1 $e |- B = ( Base ` G ) $.
    ressplusf.2 $e |- H = ( G |`s A ) $.
    ressplusf.3 $e |- .+^ = ( +g ` G ) $.
    ressplusf.4 $e |- .+^ Fn ( B X. B ) $.
    ressplusf.5 $e |- A C_ B $.
    $( The group operation function ` +f ` of a structure's restriction is the
       operation function's restriction to the new base.  (Contributed by
       Thierry Arnoux, 26-Mar-2017.) $)
    ressplusf $p |- ( +f ` H ) = ( .+^ |` ( A X. A ) ) $=
      ( vx vy cv cmpt2 cxp cres cfv wceq cbs cvv co cplusf wss resmpt2 wfn fnov
      mp2an mpbi reseq1i ressbas2 ax-mp cplusg wcel fvex eqeltri eqid ressplusg
      ssexi eqtri plusffval 3eqtr4ri ) KLBBKMLMCUAZNZAAOZPZKLAAVBNZCVDPEUBQZABU
      CZVHVEVFRJJKLBBAAVBUDUGCVCVDCBBOUECVCRIKLBBCUFUHUIKLACVGEVHAESQRJABEDGFUJ
      UKCDULQZEULQZHATUMVIVJRABBDSQTFDSUNUOJURAVIDETGVIUPUQUKUSVGUPUTVA $.
  $}

  ${
    $d x .0. $.  $d x A $.  $d x B $.  $d x G $.  $d x H $.
    ressnm.1 $e |- H = ( G |`s A ) $.
    ressnm.2 $e |- B = ( Base ` G ) $.
    ressnm.3 $e |- .0. = ( 0g ` G ) $.
    ressnm.4 $e |- N = ( norm ` G ) $.
    $( The norm in a restricted structure.  (Contributed by Thierry Arnoux,
       8-Oct-2017.) $)
    ressnm $p |- ( ( G e. Mnd /\ .0. e. A /\ A C_ B )
                   -> ( N |` A ) = ( norm ` H ) ) $=
      ( vx wcel cds cfv cmpt cbs wceq 3ad2ant3 cvv eqid cmnd wss w3a cv co cres
      c0g cnm ressbas2 fvex eqeltri ssex ressds eqidd ress0g oveq123d mpteq12dv
      syl nmfval reseq1i resmpt syl5eq a1i 3eqtr4d ) CUALZFALZABUBZUCZKAKUDZFCM
      NZUEZOZKDPNZVIDUGNZDMNZUEZOZEAUFZDUHNZVHKAVKVMVPVGVEAVMQVFABDCGHUIRVHVIVI
      FVNVJVOVGVEVJVOQZVFVGASLVTABBCPNSHCPUJUKULAVJCDSGVJTZUMURRVHVIUNABCDFGHIU
      OUPUQVGVEVRVLQVFVGVRKBVKOZAUFVLEWBAKVJECBFJHIWAUSUTKBAVKVAVBRVSVQQVHKVOVS
      DVMVNVSTVMTVNTVOTUSVCVD $.
  $}

  ${
    $d x y B $.  $d f x y K $.  $d f x y L $.  $d f x y ph $.
    abvpropd2.1 $e |- ( ph -> ( Base ` K ) = ( Base ` L ) ) $.
    abvpropd2.2 $e |- ( ph -> ( +g ` K ) = ( +g ` L ) ) $.
    abvpropd2.3 $e |- ( ph -> ( .r ` K ) = ( .r ` L ) ) $.
    $( Weaker version of ~ abvpropd .  (Contributed by Thierry Arnoux,
       8-Nov-2017.) $)
    abvpropd2 $p |- ( ph -> ( AbsVal ` K ) = ( AbsVal ` L ) ) $=
      ( vx vy cbs cfv eqidd cv wcel wa cplusg proplem3 cmulr abvpropd ) AGHBIJZ
      BCASKDAGLSMHLSMNZGHBOJCOJEPATGHBQJCQJFPR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     The opposite group
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    oppglt.1 $e |- O = ( oppG ` R ) $.
    ${
      oppgle.2 $e |- .<_ = ( le ` R ) $.
      $( less-than relation of an opposite group.  (Contributed by Thierry
         Arnoux, 13-Apr-2018.) $)
      oppgle $p |- .<_ = ( le ` O ) $=
        ( cple cfv c10 df-ple 10nn c2 2re 2lt10 gtneii oppglem eqtri ) BAFGCFGE
        AFHCDIJKHLMNOP $.
    $}

    ${
      oppglt.2 $e |- .< = ( lt ` R ) $.
      $( less-than relation of an opposite group.  (Contributed by Thierry
         Arnoux, 13-Apr-2018.) $)
      oppglt $p |- ( R e. V -> .< = ( lt ` O ) ) $=
        ( wcel cple cfv cid cdif cplt eqid pltfval cvv wceq fvex eqeltri oppgle
        coppg ax-mp syl6eqr ) ADGBAHIZJKZCLIZDBAUCUCMZFNCOGUEUDPCATIOEATQROUECU
        CAUCCEUFSUEMNUAUB $.
    $}
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Posets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y F $.
    $( A Toset is a Poset.  (Contributed by Thierry Arnoux, 20-Jan-2018.) $)
    tospos $p |- ( F e. Toset -> F e. Poset ) $=
      ( vx vy ctos wcel cpo cv cple cfv wbr wo cbs wral eqid istos simplbi ) AD
      EAFEBGZCGZAHIZJRQSJKCALIZMBTMBCTASTNSNOP $.

    $d x y z A $.  $d x y z F $.
    $( The restriction of a Poset is a Poset.  (Contributed by Thierry Arnoux,
       20-Jan-2018.) $)
    resspos $p |- ( ( F e. Poset /\ A e. V ) -> ( F |`s A ) e. Poset ) $=
      ( vx vy vz cpo wcel wa cress cvv cv cple cfv wbr wi wral eqid ssralv breq
      co wceq w3a cbs ovex a1i wss ressbas inss2 syl6eqssr adantl ispos simprbi
      cin adantr ralimdv syld sylc wb ressle anbi12d imbi12d 3anbi123d 2ralbidv
      imbi1d ralbidv syl mpbid sylanbrc ) BGHZACHZIZBAJUAZKHZDLZVOVMMNZOZVOELZV
      POZVRVOVPOZIZVOVRUBZPZVSVRFLZVPOZIZVOWDVPOZPZUCZFVMUDNZQZEWJQDWJQZVMGHVNV
      LBAJUEUFVLVOVOBMNZOZVOVRWMOZVRVOWMOZIZWBPZWOVRWDWMOZIZVOWDWMOZPZUCZFWJQZE
      WJQZDWJQZWLVLWJBUDNZUGZXCFXGQZEXGQZDXGQZXFVKXHVJVKWJAXGUNXGAXGVMCBVMRZXGR
      ZUHAXGUIUJUKVJXKVKVJBKHXKDEFXGBWMXMWMRZULUMUOXHXKXEDXGQXFXHXJXEDXGXHXJXDE
      XGQXEXHXIXDEXGXCFWJXGSUPXDEWJXGSUQUPXEDWJXGSUQURVLWMVPUBZXFWLUSVKXOVJABWM
      CVMXLXNUTUKXOXDWKDEWJWJXOXCWIFWJXOWNVQWRWCXBWHVOVOWMVPTXOWQWAWBXOWOVSWPVT
      VOVRWMVPTZVRVOWMVPTVAVEXOWTWFXAWGXOWOVSWSWEXPVRWDWMVPTVAVOWDWMVPTVBVCVFVD
      VGVHDEFWJVMVPWJRVPRULVI $.

    $d x y V $.
    $( The restriction of a Toset is a Toset.  (Contributed by Thierry Arnoux,
       20-Jan-2018.) $)
    resstos $p |- ( ( F e. Toset /\ A e. V ) -> ( F |`s A ) e. Toset ) $=
      ( vx vy ctos wcel cpo cv cple cfv wbr wo cbs wral eqid adantl istos breqd
      ssralv wa cress co tospos resspos sylan wss cin ressbas syl6eqssr simprbi
      inss2 adantr ralimdv syld sylc wb ressle orbi12d 2ralbidv mpbid sylanbrc
      ) BFGZACGZUAZBAUBUCZHGZDIZEIZVFJKZLZVIVHVJLZMZEVFNKZODVNOZVFFGVCBHGZVDVGB
      UDABCUEUFVEVHVIBJKZLZVIVHVQLZMZEVNOZDVNOZVOVEVNBNKZUGZVTEWCOZDWCOZWBVDWDV
      CVDVNAWCUHWCAWCVFCBVFPZWCPZUIAWCULUJQVCWFVDVCVPWFDEWCBVQWHVQPZRUKUMWDWFWE
      DVNOWBWEDVNWCTWDWEWADVNVTEVNWCTUNUOUPVDWBVOUQVCVDVTVMDEVNVNVDVRVKVSVLVDVQ
      VJVHVIABVQCVFWGWIURZSVDVQVJVIVHWJSUSUTQVADEVNVFVJVNPVJPRVB $.
  $}

  ${
    $d x y B $.  $d x y X $.  $d y Y $.  $d x y .<_ $.
    tleile.b $e |- B = ( Base ` K ) $.
    tleile.l $e |- .<_ = ( le ` K ) $.
    $( In a Toset, two elements must compare.  (Contributed by Thierry Arnoux,
       11-Feb-2018.) $)
    tleile $p |- ( ( K e. Toset /\ X e. B /\ Y e. B )
      -> ( X .<_ Y \/ Y .<_ X ) ) $=
      ( vx vy ctos wcel w3a cv wbr wo wral wceq breq1 breq2 orbi12d simp2 simp3
      cpo istos simprbi 3ad2ant1 wa rspc2v imp syl21anc ) BJKZDAKZEAKZLULUMHMZI
      MZCNZUOUNCNZOZIAPHAPZDECNZEDCNZOZUKULUMUAUKULUMUBUKULUSUMUKBUCKUSHIABCFGU
      DUEUFULUMUGUSVBURVBDUOCNZUODCNZOHIDEAAUNDQUPVCUQVDUNDUOCRUNDUOCSTUOEQVCUT
      VDVAUOEDCSUOEDCRTUHUIUJ $.

    tltnle.s $e |- .< = ( lt ` K ) $.
    $( In a Toset, less-than is equivalent to not inverse less-than-or-equal
       see ~ pltnle .  (Contributed by Thierry Arnoux, 11-Feb-2018.) $)
    tltnle $p |- ( ( K e. Toset /\ X e. B /\ Y e. B )
      -> ( X .< Y <-> -. Y .<_ X ) ) $=
      ( ctos wcel w3a wbr wn wa cpo wb tospos pltval3 syl3an1 wo tleile syl6rbb
      ibar pm5.61 syl bitrd ) CJKZEAKZFAKZLZEFBMZEFDMZFEDMZNZOZUOUHCPKUIUJULUPQ
      CRABCDEFGHISTUKUMUNUAZUPUOQACDEFGHUBUQUOUQUOOUPUQUOUDUMUNUEUCUFUG $.
  $}
  
  ${
    tlt2.b $e |- B = ( Base ` K ) $.
    tlt2.e $e |- .<_ = ( le ` K ) $.
    tlt2.l $e |- .< = ( lt ` K ) $.
    $( In a Toset, two elements must compare.  (Contributed by Thierry Arnoux,
       13-Apr-2018.) $)
    tlt2 $p |- ( ( K e. Toset /\ X e. B /\ Y e. B )
      -> ( X .<_ Y \/ Y .< X ) ) $=
      ( ctos wcel w3a wbr wo wn exmidd wb tltnle 3com23 orbi2d mpbird ) CJKZEAK
      ZFAKZLZEFDMZFEBMZNUFUFOZNUEUFPUEUGUHUFUBUDUCUGUHQABCDFEGHIRSTUA $.
  $}
  
  ${
    tlt3.b $e |- B = ( Base ` K ) $.
    tlt3.l $e |- .< = ( lt ` K ) $.
    $( In a Toset, two elements must compare strictly, or be equal.
       (Contributed by Thierry Arnoux, 13-Apr-2018.) $)
    tlt3 $p |- ( ( K e. Toset /\ X e. B /\ Y e. B )
      -> ( X = Y \/ X .< Y \/ Y .< X ) ) $=
      ( ctos wcel w3a wceq wbr wo w3o cple cfv eqid tlt2 cpo wb pleval2 syl3an1
      tospos orcom syl6bb orbi1d mpbid df-3or sylibr ) CHIZDAIZEAIZJZDEKZDEBLZM
      ZEDBLZMZUNUOUQNUMDECOPZLZUQMURABCUSDEFUSQZGRUMUTUPUQUJCSIZUKULUTUPTCUCVBU
      KULJUTUOUNMUPABCUSDEFVAGUAUOUNUDUEUBUFUGUNUOUQUHUI $.
  $}

  ${
    $d a b c d .< $.  $d a b c d A $.  $d a b c d B $.  $d a b c K $.
    $d a b c ph $.
    toslub.b $e |- B = ( Base ` K ) $.
    toslub.l $e |- .< = ( lt ` K ) $.
    toslub.1 $e |- ( ph -> K e. Toset ) $.
    toslub.2 $e |- ( ph -> A C_ B ) $.
    toslub.3 $e |- ( ph -> E. a e. B
       ( A. b e. A -. a .< b /\ A. b e. B ( b .< a -> E. d e. A b .< d ) ) ) $.
    $( In a toset, the lowest upper bound ` lub ` , defined for partial orders
       is the supremum, ` sup ( A , B , .< ) ` , defined for total orders, if
       this supremum exists (these are the set.mm definition: lowest upper
       bound and supremum are normally synonymous) Note that the two
       definitions do not have the same value when there is no such supremum.
       In that case, ` sup ( A , B , .< ) ` will take the value ` (/) ` , but
       ` ( ( lub `` K ) `` A ) ` takes the value ` ( Undef `` B ) ` ,
       therefore, we restrict this theorem only to the case where this supremum
       exists, which is expressed by the last assumption.  (Contributed by
       Thierry Arnoux, 15-Feb-2018.) $)
    toslub $p |- ( ph -> ( ( lub ` K ) ` A ) = sup ( A , B , .< ) ) $=
      ( vc wbr wral wa wcel wn wb club cfv cv cple crio csup ctos wss wceq eqid
      lubval syl2anc wrex ad2antrr simplr adantr sselda tltnle syl3anc ralbidva
      wi con2bid simpll simpr sseldd syl3an1 3expa syl21anc breq2 notbid ralnex
      cbvralv bitri syl6bb adantlr imbi12d con34b syl6bbr breq1 rexbidv anbi12d
      syl riotabidva wor cid cres tosso ibi simpld supval2 eqtr4d eqtrd ) ABEUA
      UBZUBZGUCZFUCZEUDUBZOZGBPZWONUCZWQOZGBPZWPWTWQOZVAZNCPZQZFCUEZBCDUFZAEUGR
      ZBCUHZWNXGUIKLFGNUGCBWMEWQIWQUJZWMUJUKULAXGWPWODOZSZGBPZWOWPDOZWOHUCZDOZH
      BUMZVAZGCPZQZFCUEXHAXFYAFCAWPCRZQZWSXNXEXTYCWRXMGBYCWOBRZQZXLWRYEXIYBWOCR
      ZXLWRSTAXIYBYDKUNAYBYDUOYCBCWOAXJYBLUPUQCDEWQWPWOIXKJURUSVBUTYCXEWTWPDOZW
      TXPDOZHBUMZVAZNCPXTYCXDYJNCYCWTCRZQZXDYISZYGSZVAYJYLXBYMXCYNAYKXBYMTYBAYK
      QZXBWTWODOZSZGBPZYMYOXAYQGBYOYDQZAYKYFXAYQTAYKYDVCZAYKYDUOYSBCWOYSAXJYTLW
      BYOYDVDVEYOYFQYPXAAYKYFYPXASTZAXIYKYFUUAKCDEWQWTWOIXKJURVFVGVBVHUTYRYHSZH
      BPYMYQUUBGHBWOXPUIYPYHWOXPWTDVIVJVLYHHBVKVMVNVOYLYGXCYLXIYKYBYGXCSTAXIYBY
      KKUNYCYKVDAYBYKUOCDEWQWTWPIXKJURUSVBVPYGYIVQVRUTXSYJGNCWOWTUIZXOYGXRYIWOW
      TWPDVSUUCXQYHHBWOWTXPDVSVTVPVLVRWAWCAFGHCBDAXICDWDZKXIUUDWECWFWQUHZXIUUDU
      UEQCDEWQUGIXKJWGWHWIWBMWJWKWL $.
  $}


  ${
    $d a b c d .< $.  $d a b c d A $.  $d a b c d B $.  $d a b c K $.
    $d a b c ph $.
    tosglb.b $e |- B = ( Base ` K ) $.
    tosglb.l $e |- .< = ( lt ` K ) $.
    tosglb.1 $e |- ( ph -> K e. Toset ) $.
    tosglb.2 $e |- ( ph -> A C_ B ) $.
    tosglb.3 $e |- ( ph -> E. a e. B
       ( A. b e. A -. b .< a /\ A. b e. B ( a .< b -> E. d e. A d .< b ) ) ) $.
    $( Same theorem as ~ toslub , for infinimum.  (Contributed by Thierry
       Arnoux, 17-Feb-2018.) $)
    tosglb $p |- ( ph -> ( ( glb ` K ) ` A ) = sup ( A , B , `' .< ) ) $=
      ( wbr wral wa wcel wn wb cvv vc cglb cfv cv cple crio ccnv csup ctos wceq
      wss eqid glbval syl2anc wrex ad2antrr adantr sselda simplr tltnle syl3anc
      wi con2bid ralbidva simpll syl simpr sseldd syl3an1 3com23 3expa syl21anc
      breq1 notbid cbvralv ralnex syl6bb adantlr imbi12d con34b syl6bbr rexbidv
      bitri breq2 anbi12d vex brcnvg mp2an notbii ralbii rexbii imbi12i anbi12i
      riotabidva wor cid cres tosso ibi simpld cnvso sylib sylibr supval2 eqtrd
      eqtr4d ) ABEUBUCZUCZFUDZGUDZEUEUCZNZGBOZUAUDZXJXKNZGBOZXNXIXKNZVBZUACOZPZ
      FCUFZBCDUGZUHZAEUIQZBCUKZXHYAUJKLFGUAUICBXGEXKIXKULZXGULUMUNAYAXIXJYBNZRZ
      GBOZXJXIYBNZXJHUDZYBNZHBUOZVBZGCOZPZFCUFYCAXTYPFCAXICQZPZXTXJXIDNZRZGBOZX
      IXJDNZYKXJDNZHBUOZVBZGCOZPZYPYRXMUUAXSUUFYRXLYTGBYRXJBQZPZYSXLUUIYDXJCQZY
      QYSXLRSAYDYQUUHKUPYRBCXJAYEYQLUQURAYQUUHUSCDEXKXJXIIYFJUTVAVCVDYRXSXIXNDN
      ZYKXNDNZHBUOZVBZUACOUUFYRXRUUNUACYRXNCQZPZXRUUMRZUUKRZVBUUNUUPXPUUQXQUURA
      UUOXPUUQSYQAUUOPZXPXJXNDNZRZGBOZUUQUUSXOUVAGBUUSUUHPZAUUOUUJXOUVASAUUOUUH
      VEZAUUOUUHUSUVCBCXJUVCAYEUVDLVFUUSUUHVGVHUUSUUJPUUTXOAUUOUUJUUTXORSZAUUJU
      UOUVEAYDUUJUUOUVEKCDEXKXJXNIYFJUTVIVJVKVCVLVDUVBUULRZHBOUUQUVAUVFGHBXJYKU
      JUUTUULXJYKXNDVMVNVOUULHBVPWCVQVRUUPUUKXQUUPYDYQUUOUUKXQRSAYDYQUUOKUPAYQU
      UOUSYRUUOVGCDEXKXIXNIYFJUTVAVCVSUUKUUMVTWAVDUUEUUNGUACXJXNUJZUUBUUKUUDUUM
      XJXNXIDWDUVGUUCUULHBXJXNYKDWDWBVSVOWAWEYIUUAYOUUFYHYTGBYGYSXITQZXJTQZYGYS
      SFWFZGWFZXIXJTTDWGWHWIWJYNUUEGCYJUUBYMUUDUVIUVHYJUUBSUVKUVJXJXITTDWGWHYLU
      UCHBUVIYKTQYLUUCSUVKHWFXJYKTTDWGWHWKWLWJWMZWAWNAFGHCBYBAYDCYBWOZKYDCDWOZU
      VMYDUVNWPCWQXKUKZYDUVNUVOPCDEXKUIIYFJWRWSWTCDXAXBVFAUUGFCUOYPFCUOMYPUUGFC
      UVLWKXCXDXFXE $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Complete lattices
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    clatp0cl.b $e |- B = ( Base ` W ) $.
    clatp0cl.0 $e |- .0. = ( 0. ` W ) $.
    $( The poset zero of a complete lattice belongs to its base.  (Contributed
       by Thierry Arnoux, 17-Feb-2018.) $)
    clatp0cl $p |- ( W e. CLat -> .0. e. B ) $=
      ( ccla wcel cglb cfv eqid p0val wss ssid clatglbcl mpan2 eqeltrd ) BFGZCA
      BHIZIZAARBFCDRJZEKQAALSAGAMAARBDTNOP $.
  $}

  ${
    clatp1cl.b $e |- B = ( Base ` W ) $.
    clatp1cl.1 $e |- .1. = ( 1. ` W ) $.
    $( The poset one of a complete lattice belongs to its base.  (Contributed
       by Thierry Arnoux, 17-Feb-2018.) $)
    clatp1cl $p |- ( W e. CLat -> .1. e. B ) $=
      ( ccla wcel club cfv eqid p1val wss ssid clatlubcl mpan2 eqeltrd ) CFGZBA
      CHIZIZAARBCFDRJZEKQAALSAGAMAARCDTNOP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Extended reals Structure - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Assume the scalar component of the extended real structure is the field of
     the real numbers (this has to be defined in the main body of set.mm)
     (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
  ax-xrssca $a |- ( CCfld |`s RR ) = ( Scalar ` RR*s ) $.

  $( Assume the scalar product of the extended real structure is the extended
     real number multiplication operation (this has to be defined in the main
     body of set.mm) (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
  ax-xrsvsca $a |- *e = ( .s ` RR*s ) $.

  $( The zero of the extended real numbers.  The extended real is not a group,
     as its addition is not associative.  (cf. ~ xaddass and ~ df-xrs ),
     however it has a zero.  (Contributed by Thierry Arnoux, 13-Jun-2017.) $)
  xrs0 $p |- 0 = ( 0g ` RR*s ) $=
    ( cc0 cxrs c0g cfv wceq wtru cxr cxad cbs xrsbas a1i cplusg xrsadd wcel 0xr
    vx cv co xaddid2 adantl xaddid1 grpidd trud ) ABCDEFPGHBAGBIDEFJKHBLDEFMKAG
    NFOKPQZGNZAUDHRUDEFUDSTUEUDAHRUDEFUDUATUBUC $.

  $( The "strictly less than" relation for the extended real structure.
     (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
  xrslt $p |- < = ( lt ` RR*s ) $=
    ( clt cle cid cdif cxrs cplt cfv dflt2 cvv wcel wceq xrsex xrsle eqid ax-mp
    pltfval eqtr4i ) ABCDZEFGZHEIJSRKLISEBMSNPOQ $.

  ${
    $d x B $.
    $( The inversion operation in the extended real numbers.  The extended real
       is not a group, as its addition is not associative.  (cf. ~ xaddass and
       ~ df-xrs ), however it has an inversion operation.  (Contributed by
       Thierry Arnoux, 13-Jun-2017.) $)
    xrsinvgval $p |- ( B e. RR* -> ( ( invg ` RR*s ) ` B ) = -e B ) $=
      ( vx cxr wcel cxrs cminusg cfv cxad cc0 wceq crio cxne xrsbas xrsadd xrs0
      cv co eqid grpinvval xnegcl wb xaddeq0 ancoms riota5 eqtrd ) ACDZAEFGZGBP
      ZAHQIJZBCKALZBCHEUGAIMNOUGRSUFUIBCUJATUHCDUFUIUHUJJUAUHAUBUCUDUE $.
  $}

  ${
    $d n A $.  $d m n x y B $.
    $( The "multiple" function in the extended real numbers structure.
       (Contributed by Thierry Arnoux, 14-Jun-2017.) $)
    xrsmulgzz $p |- ( ( A e. ZZ /\ B e. RR* ) ->
                                        ( A ( .g ` RR*s ) B ) = ( A *e B ) ) $=
      ( cxr wcel cxrs co cxmu wceq c1 oveq1 eqeq12d xrsbas wa cxad simpr oveq1d
      cc0 adantl cr a1i vn vm vx vy cz cmg cv cneg caddc xrs0 eqid mulg0 xmul02
      cfv eqtr4d cn0 cn simpll xrsadd mulgnnp1 syl2anc simpl eqtrd 0p1e1 syl6eq
      xaddid2 mulg1 3eqtr4rd elnn0 sylib mpjaodan adantr cle wbr nn0ssre ressxr
      wo sstri sseldi nn0ge0 ad2antlr 1re rexri 0le1 xadddi2r syl221anc xmulid2
      rexadd syl oveq2d 3eqtr3d 3eqtr4d exp31 cxne xnegeq cminusg mulgnegnn cvv
      ancoms xrsex wss ssid simp2 simp3 xaddcld mulgnnsubcl 3anidm12 xrsinvgval
      w3a nnssre sseli rexneg xmulneg1 eqtr3d zindd impcom ) BCDZAUEDABEUFUNZFZ
      ABGFZHZUAUGZBXRFZYBBGFZHQBXRFZQBGFZHUBUGZBXRFZYGBGFZHZYGUHZBXRFZYKBGFZHZY
      GIUIFZBXRFZYOBGFZHZYAXQUAUBAYBQHYCYEYDYFYBQBXRJYBQBGJKYBYGHYCYHYDYIYBYGBX
      RJYBYGBGJKYBYOHYCYPYDYQYBYOBXRJYBYOBGJKYBYKHYCYLYDYMYBYKBXRJYBYKBGJKYBAHY
      CXSYDXTYBABXRJYBABGJKXQYEQYFCXREBQLUJXRUKZULZBUMUOXQYGUPDZYJYRXQUUAMZYJMZ
      YHBNFZYIBNFZYPYQUUCYHYIBNUUBYJOPUUBYPUUDHZYJUUBYGUQDZUUFYGQHZUUBUUGMUUGXQ
      UUFUUBUUGOXQUUAUUGURCNXREYGBLYSUSUTVAUUBUUHMUUHXQUUFUUBUUHOXQUUAUUHURUUHX
      QMZQBNFZBUUDYPXQUUJBHUUHBVFRUUIYHQBNUUIYHYEQUUIYGQBXRUUHXQVBZPXQYEQHUUHYT
      RVCPUUIYPIBXRFZBUUIYOIBXRUUIYOQIUIFIUUIYGQIUIUUKPVDVEPXQUULBHUUHCXREBLYSV
      GRVCVHVAUUBUUAUUGUUHVQXQUUAOZYGVIVJVKVLUUCYGINFZBGFZYIIBGFZNFZYQUUEUUCYGC
      DZQYGVMVNZICDZQIVMVNZXQUUOUUQHUUCUPCYGUPSCVOVPVRUUBUUAYJUUMVLZVSUUAUUSXQY
      JYGVTWAUUTUUCIWBWCTUVAUUCWDTXQUUAYJURZYGIBWEWFUUCUUNYOBGUUCYGSDZISDZUUNYO
      HUUCUPSYGVOUVBVSUVEUUCWBTYGIWHVAPUUCUUPBYINUUCXQUUPBHUVCBWGWIWJWKWLWMXQUU
      GYJYNXQUUGMZYJMYHWNZYIWNZYLYMYJUVGUVHHUVFYHYIWORUVFYLUVGHYJUVFYLYHEWPUNZU
      NZUVGUUGXQYLUVJHCXREUVIYGBLYSUVIUKWQWSUVFYHCDZUVJUVGHUUGXQUVKUUGXQUVKUUGU
      CUDCNCXREYGWRBLYSUSEWRDUUGWTTCCXAUUGCXBTUUGUCUGZCDZUDUGZCDZXIUVLUVNUUGUVM
      UVOXCUUGUVMUVOXDXEXFXGWSYHXHWIVCVLUVFYMUVHHYJUVFYGWNZBGFZYMUVHUVFUVPYKBGU
      VFUVDUVPYKHUUGUVDXQUQSYGXJXKRYGXLWIPUVFUURXQUVQUVHHUVFUQCYGUQSCXJVPVRXQUU
      GOVSXQUUGVBYGBXMVAXNVLWLWMXOXP $.
  $}

  ${
    $d x y z $.
    $( The extended real numbers form a toset.  (Contributed by Thierry Arnoux,
       15-Feb-2018.) $)
    xrstos $p |- RR*s e. Toset $=
      ( vx vy vz cxrs ctos wcel cpo cv cle wbr wo cxr wral cvv wa rgen2a xrsbas
      wi xrsle mpbir2an wceq w3a xrleid ad2antrr xrletri3 biimprd adantr xrletr
      xrsex 3expa 3jca ralrimiva ispos xrletri istos ) DEFDGFZAHZBHZIJZURUQIJZK
      ZBLMALMUPDNFUQUQIJZUSUTOZUQURUAZRZUSURCHZIJOUQVFIJRZUBZCLMZBLMALMUIVIABLU
      QLFZURLFZOZVHCLVLVFLFZOVBVEVGVJVBVKVMUQUCUDVLVEVMVLVDVCUQURUEUFUGVJVKVMVG
      UQURVFUHUJUKULPABCLDIQSUMTVAABLUQURUNPABLDIQSUOT $.
  $}

  ${
    $d a b c x $.
    $( The extended real numbers form a complete lattice.  (Contributed by
       Thierry Arnoux, 15-Feb-2018.) $)
    xrsclat $p |- RR*s e. CLat $=
      ( vx va vb vc cxrs ccla wcel cpo cxr wss club cfv xrstos clt xrsbas xrslt
      cv csup eqeltrd eqid cglb wa wi wal ctos tospos ax-mp a1i xrsupss supxrcl
      id toslub ccnv xrinfmss tosglb infmxrcl jca ax-gen isclat mpbir2an ) EFGE
      HGZAQZIJZVBEKLZLZIGZVBEUALZLZIGZUBUCZAUDEUEGZVAMEUFUGVJAVCVFVIVCVEVBINRIV
      CVBINEBCDOPVKVCMUHZVCUKZBCDVBUIULVBUJSVCVHVBINUMRIVCVBINEBCDOPVLVMBCDVBUN
      UOVBUPSUQURIVDVGEAOVDTVGTUSUT $.
  $}

  ${
    $d x y z $.
    $( The poset 0 of the extended real numbers is minus infinity.
       (Contributed by Thierry Arnoux, 18-Feb-2018.) $)
    xrsp0 $p |- -oo = ( 0. ` RR*s ) $=
      ( vx vy vz cxrs cp0 cfv cxr cglb clt ccnv csup cmnf cvv wcel xrsex xrsbas
      wceq eqid p0val ax-mp wss ssid xrslt xrstos a1i id xrinfmss tosglb xrinfm
      ctos 3eqtrri ) DEFZGDHFZFZGGIJKZLDMNULUNQOGUMDMULPUMRULRSTGGUAZUNUOQGUBUP
      GGIDABCPUCDUJNUPUDUEUPUFABCGUGUHTUIUK $.

    $( The poset 1 of the extended real numbers is plus infinity.  (Contributed
       by Thierry Arnoux, 18-Feb-2018.) $)
    xrsp1 $p |- +oo = ( 1. ` RR*s ) $=
      ( vx vy vz cxrs cp1 cfv cxr club clt csup cpnf cvv wcel wceq xrsex xrsbas
      eqid p1val ax-mp wss ssid xrslt ctos xrstos a1i id xrsupss toslub 3eqtrri
      xrsup ) DEFZGDHFZFZGGIJZKDLMUKUMNOGULUKDLPULQUKQRSGGTZUMUNNGUAUOGGIDABCPU
      BDUCMUOUDUEUOUFABCGUGUHSUJUI $.
  $}

  ${
    ressmulgnn.1 $e |- H = ( G |`s A ) $.
    ressmulgnn.2 $e |- A C_ ( Base ` G ) $.
    ressmulgnn.3 $e |- .* = ( .g ` G ) $.
    ressmulgnn.4 $e |- I = ( invg ` G ) $.
    $( Values for the group multiple function in a restricted structure
       (Contributed by Thierry Arnoux, 12-Jun-2017.) $)
    ressmulgnn $p |-
                ( ( N e. NN /\ X e. A ) -> ( N ( .g ` H ) X ) = ( N .* X ) ) $=
      ( cn wcel cfv co c1 cbs wceq eqid ax-mp cmg csn cxp cseq wss ressbas2 cvv
      wa cplusg fvex ssexi ressplusg seqeq2 mulgnn simpr sseldi syldan eqtr4d )
      FLMZGAMZUHZFGCUANZOFBUINZLGUBUCZPUDZNZFGEOZACUINZVEVBCFGABQNZUEACQNRIAVIC
      BHVISZUFTVHSVBSVCVHRZVEVHVDPUDRAUGMVKAVIBQUJIUKAVCBCUGHVCSZULTVCVHVDPUMTU
      NUSUTGVIMVGVFRVAAVIGIUSUTUOUPVIVCVEEBFGVJVLJVESUNUQUR $.

    ressmulgnn0.4 $e |- ( 0g ` G ) = ( 0g ` H ) $.
    $( Values for the group multiple function in a restricted structure
       (Contributed by Thierry Arnoux, 14-Jun-2017.) $)
    ressmulgnn0 $p |-
               ( ( N e. NN0 /\ X e. A ) -> ( N ( .g ` H ) X ) = ( N .* X ) ) $=
      ( wcel wa cfv co wceq cc0 simpr eqid cn0 cn cmg simplr ressmulgnn syl2anc
      c0g cbs wss ressbas2 ax-mp mulg0 syl oveq1d sseldi eqtr4d wo elnn0 biimpi
      3eqtr4d adantr mpjaodan ) FUAMZGAMZNZFUBMZFGCUCOZPZFGEPZQZFRQZVEVFNVFVDVJ
      VEVFSVCVDVFUDABCDEFGHIJKUEUFVEVKNZVHRGEPZVIVLRGVGPZBUGOZVHVMVLVDVNVOQVCVD
      VKUDZAVGCGVOABUHOZUIACUHOQIAVQCBHVQTZUJUKLVGTULUMVLFRGVGVEVKSZUNVLGVQMVMV
      OQVLAVQGIVPUOVQEBGVOVRVOTJULUMUTVLFRGEVSUNUPVCVFVKUQZVDVCVTFURUSVAVB $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     The extended non-negative real numbers commutative monoid
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The base of the extended non-negative real numbers.  (Contributed by
     Thierry Arnoux, 30-Jan-2017.) $)
  xrge0base $p |- ( 0 [,] +oo ) = ( Base ` ( RR*s |`s ( 0 [,] +oo ) ) ) $=
    ( cc0 cpnf cicc cxr cin cxrs cress cbs cfv wss wceq iccssxr df-ss mpbi wcel
    co cvv ovex eqid xrsbas ressbas ax-mp eqtr3i ) ABCPZDEZUDFUDGPZHIZUDDJUEUDK
    ABLUDDMNUDQOUEUGKABCRUDDUFQFUFSTUAUBUC $.

  $( The zero of the extended non-negative real numbers monoid.  (Contributed
     by Thierry Arnoux, 30-Jan-2017.) $)
  xrge00 $p |- 0 = ( 0g ` ( RR*s |`s ( 0 [,] +oo ) ) ) $=
    ( cxrs cxr cmnf cdif cress co cmnd wcel cc0 cpnf cicc wss cfv wceq ax-mp wn
    wbr mpbi cin cvv csn c0g eqid xrs1mnd ccmn xrge0cmn cmnmnd cle wa clt mnflt
    cr 0re wb mnfxr 0xr xrltnle mp2an intnan elxrge0 mtbir difsn ssdif eqsstr3i
    iccssxr 0le0 mpbir2an cbs difss df-ss xrex difexg xrsbas ressbas xrs10 ovex
    eqtr3i ressress dfss incom eqtr2i oveq2i submnd0 mp4an ) ABCUAZDZEFZGHAIJKF
    ZEFZGHZWHWFLZIWHHZIWIUBMNWGWGUCZUDWIUEHWJUFWIUGOWHWHWEDZWFCWHHZPWNWHNWOCBHZ
    ICUHQZUIWQWPCIUJQZWQPZIULHWRUMIUKOWPIBHZWRWSUNUOUPCIUQURRUSCUTVACWHVBOWHBLW
    NWFLIJVEWHBWEVCOVDZWLWTIIUHQUPVFIUTVGWFWHWGWIIWFBSZWFWGVHMZWFBLXBWFNBWEVIWF
    BVJRWFTHZXBXCNBTHXDVKBWETVLOZWFBWGTAWMVMVNOVQWGWMVOWGWHEFZAWFWHSZEFZWIXDWHT
    HXFXHNXEIJKVPWFWHATTVRURXGWHAEWHWHWFSZXGWKWHXINXAWHWFVSRWHWFVTWAWBWAWCWD $.

  $( The additive law of the extended non-negative real numbers monoid is the
     addition in the extended real numbers.  (Contributed by Thierry Arnoux,
     20-Mar-2017.) $)
  xrge0plusg $p |- +e = ( +g ` ( RR*s |`s ( 0 [,] +oo ) ) ) $=
    ( cc0 cpnf cicc co cvv wcel cxad cxrs cress cplusg wceq ovex eqid ressplusg
    cfv xrsadd ax-mp ) ABCDZEFGHRIDZJOKABCLRGHSESMPNQ $.

  $( The lower-or-equal relation in the extended real numbers.  (Contributed by
     Thierry Arnoux, 14-Mar-2018.) $)
  xrge0le $p |- <_ = ( le ` ( RR*s |`s ( 0 [,] +oo ) ) ) $=
    ( cc0 cpnf cicc co cvv wcel cle cxrs cress cple wceq ovex eqid xrsle ressle
    cfv ax-mp ) ABCDZEFGHRIDZJPKABCLRHGESSMNOQ $.

  $( The group multiple function in the extended non-negative real numbers.
     (Contributed by Thierry Arnoux, 14-Jun-2017.) $)
  xrge0mulgnn0 $p |- ( ( A e. NN0 /\ B e. ( 0 [,] +oo ) ) ->
                  ( A ( .g ` ( RR*s |`s ( 0 [,] +oo ) ) ) B ) = ( A *e B ) ) $=
    ( cn0 wcel cc0 cpnf cicc co wa cxrs cress cmg cfv cxmu cminusg eqid cxr cbs
    iccssxr c0g xrsbas sseqtri xrs0 xrge00 eqtr3i ressmulgnn0 cz wceq xrsmulgzz
    nn0z sseli syl2an eqtrd ) ACDZBEFGHZDZIABJUOKHZLMHABJLMZHZABNHZUOJUQJOMZURA
    BUQPUOQJRMEFSZUAUBURPVAPEJTMUQTMUCUDUEUFUNAUGDBQDUSUTUHUPAUJUOQBVBUKABUIULU
    M $.

  $( Associativity of extended non-negative real addition.  (Contributed by
     Thierry Arnoux, 8-Jun-2017.) $)
  xrge0addass $p |- ( ( A e. ( 0 [,] +oo ) /\ B e. ( 0 [,] +oo ) /\
    C e. ( 0 [,] +oo ) ) -> ( ( A +e B ) +e C ) = ( A +e ( B +e C ) ) ) $=
    ( cc0 cpnf co wcel cxr cmnf wne cxad sseldi cle wbr wa elicc4 syl3anc mpbid
    wb simpld cicc w3a iccssxr simp1 0xr a1i pnfxr ge0nemnf syl2anc simp2 simp3
    wceq xaddass syl222anc ) ADEUAFZGZBUOGZCUOGZUBZAHGZAIJZBHGZBIJZCHGZCIJZABKF
    CKFABCKFKFULUSUOHADEUCZUPUQURUDZLZUSUTDAMNZVAVHUSVIAEMNZUSUPVIVJOZVGUSDHGZE
    HGZUTUPVKSVLUSUEUFZVMUSUGUFZVHDEAPQRTAUHUIUSUOHBVFUPUQURUJZLZUSVBDBMNZVCVQU
    SVRBEMNZUSUQVRVSOZVPUSVLVMVBUQVTSVNVOVQDEBPQRTBUHUIUSUOHCVFUPUQURUKZLZUSVDD
    CMNZVEWBUSWCCEMNZUSURWCWDOZWAUSVLVMVDURWESVNVOWBDECPQRTCUHUIABCUMUN $.

  $( An extended non-negative real cannot be minus infinity.  (Contributed by
     Thierry Arnoux, 9-Jun-2017.) $)
  xrge0neqmnf $p |- ( A e. ( 0 [,] +oo ) -> A =/= -oo ) $=
    ( cc0 cpnf cicc co wcel cmnf wn wceq cle wbr cxr w3a clt cr 0re mp2an con3i
    wb 0xr mnflt ax-mp mnfxr xrltnle mpbi simp2 pnfxr elicc1 biimpi mp2b nelneq
    mpan2 neneqad ) ABCDEZFZAGUOGUNFZHZAGIHBGJKZHZGLFZURGCJKZMZHUQGBNKZUSBOFVCP
    BUAUBUTBLFZVCUSSUCTGBUDQUEVBURUTURVAUFRUPVBUPVBVDCLFUPVBSTUGBCGUHQUIRUJAGUN
    UKULUM $.

  $( An extended real which is not a real is plus infinity.  (Contributed by
     Thierry Arnoux, 16-Oct-2017.) $)
  xrge0nre $p |- ( ( A e. ( 0 [,] +oo ) /\ -. A e. RR ) -> A = +oo ) $=
    ( cc0 cpnf cicc co wcel cr wceq cxr cmnf wne wo iccssxr xrge0neqmnf xrnemnf
    sseli wa biimpi syl2anc orcanai ) ABCDEZFZAGFZACHZUBAIFZAJKZUCUDLZUAIABCMPA
    NUEUFQUGAORST $.

  $( The sum of nonnegative and positive numbers is positive.  See ~ addgtge0
     (Contributed by Thierry Arnoux, 6-Jul-2017.) $)
  xrge0addgt0 $p |- ( ( ( A e. ( 0 [,] +oo ) /\ B e. ( 0 [,] +oo ) ) /\ 0 < A )
                                                         -> 0 < ( A +e B ) ) $=
    ( cc0 cpnf cicc co wcel wa clt wbr cxad wceq cxr 0xr xaddid1 simplr simplll
    a1i sseldi breq2d ax-mp simpr wi iccssxr simpllr xlt2add syl22anc syl5eqbrr
    mp2and oveq2 adantl syl bitr3d mpbird cle wo iccgelb syl3anc xrleloe biimpa
    pnfxr syl21anc mpjaodan ) ACDEFZGZBVDGZHZCAIJZHZCBIJZCABKFZIJZCBLZVIVJHZCCC
    KFZVKICMGZVOCLNCOUAVNVHVJVOVKIJZVGVHVJPVIVJUBVNVPVPAMGZBMGZVHVJHVQUCVPVNNRZ
    VTVNVDMACDUDZVEVFVHVJQSVNVDMBWAVEVFVHVJUESCCABUFUGUIUHVIVMHZVLVHVGVHVMPWBCA
    CKFZIJVLVHWBWCVKCIVMWCVKLVICBAKUJUKTWBWCACIWBVRWCALWBVDMAWAVEVFVHVMQSAOULTU
    MUNVIVPVSCBUOJZVJVMUPZVPVINRZVIVDMBWAVEVFVHPZSVIVPDMGZVFWDWFWHVIVARWGCDBUQU
    RVPVSHWDWECBUSUTVBVC $.

  $( Distributivity of extended non-negative real multiplication over
     addition.  (Contributed by Thierry Arnoux, 30-Jun-2017.) $)
  xrge0adddir $p |- ( ( A e. ( 0 [,] +oo ) /\ B e. ( 0 [,] +oo ) /\ C e.
    ( 0 [,] +oo ) ) -> ( ( A +e B ) *e C ) = ( ( A *e C ) +e ( B *e C ) ) ) $=
    ( cc0 cpnf co wcel cxad cxmu wceq wa cxr cr sseldi wbr pnfxr syl2anc oveq1d
    cmnf syl cicc w3a cico iccssxr simpl1 simpl2 cioo clt cle mnfxr mnflt ax-mp
    wss 0re pnfge icossioo mp4an ioomax sseqtri xadddir syl3anc simpll1 simpll2
    simpr xaddcld xrge0addgt0 syl21anc xmulpnf1 oveq2 wne ge0xmulcl xrge0neqmnf
    ad2antlr simpll3 xaddpnf2 3eqtr4d eqtrd eqtr4d xmul02 oveq1 xmulcld xaddid2
    adantl 3eqtr3d 3eqtr2rd wo 0xr a1i iccgelb xrleloe biimpa mpjaodan wb mp3an
    eliccelico 3anbi3i simp3bi ) ADEUAFZGZBWRGZCWRGZUBZCDEUCFZGZABHFZCIFZACIFZB
    CIFZHFZJZCEJZXBXDKZALGZBLGZCMGXJXLWRLADEUDZWSWTXAXDUENXLWRLBXOWSWTXAXDUFNXL
    XCMCXCSEUGFZMSLGELGZSDUHOZEEUIOZXCXPUMUJPDMGXRUNDUKULXQXSPEUOULSEDEUPUQURUS
    XBXDVDNABCUTVAXBXKKZDAUHOZXJDAJZXTYAKZXFEXHHFZXIYCXEEIFZEXFYDYCXELGDXEUHOZY
    EEJYCABYCWRLAXOWSWTXAXKYAVBZNZYCWRLBXOWSWTXAXKYAVCZNVEYCWSWTYAYFYGYIXTYAVDZ
    ABVFVGXEVHQXKXFYEJXBYACEXEIVIVMYCXHLGZXHSVJZYDEJYCWRLXHXOYCWTXAXHWRGZYIWSWT
    XAXKYAVNBCVKQZNYCYMYLYNXHVLTXHVOQVPYCXGEXHHYCXGAEIFZEXKXGYOJXBYACEAIVIVMYCX
    MYAYOEJYHYJAVHQVQRVRXTYBKZXIXHDBHFZCIFZXFYPDCIFZXHHFDXHHFZXIXHYPYSDXHHYPCLG
    YSDJYPWRLCXOWSWTXAXKYBVNNZCVSTRYPYSXGXHHYBYSXGJXTDACIVTWCRYPYKYTXHJYPBCYPWR
    LBXOWSWTXAXKYBVCNZUUAWAXHWBTWDYPYQBCIYPXNYQBJUUBBWBTRYBYRXFJXTYBYQXECIDABHV
    TRWCWEXTDLGZXMDAUIOZYAYBWFZUUCXTWGWHZXTWRLAXOWSWTXAXKUEZNXTUUCXQWSUUDUUFXQX
    TPWHUUGDEAWIVAUUCXMKUUDUUEDAWJWKVGWLXBWSWTXDXKWFZXAUUHWSWTUUCXQDEUIOZXAUUHW
    MWGPUUCUUIWGDUOULDECWOWNWPWQWL $.

  $( Distributivity of extended non-negative real multiplication over
     addition.  (Contributed by Thierry Arnoux, 6-Sep-2018.) $)
  xrge0adddi $p |- ( ( A e. ( 0 [,] +oo ) /\ B e. ( 0 [,] +oo ) /\ C e.
    ( 0 [,] +oo ) ) -> ( C *e ( A +e B ) ) = ( ( C *e A ) +e ( C *e B ) ) ) $=
    ( cc0 cpnf cicc co wcel w3a cxad cxmu xrge0adddir wceq iccssxr simp1 sseldi
    cxr simp2 xmulcom syl2anc xaddcld simp3 oveq12d 3eqtr3d ) ADEFGZHZBUEHZCUEH
    ZIZABJGZCKGZACKGZBCKGZJGCUJKGZCAKGZCBKGZJGABCLUIUJQHCQHZUKUNMUIABUIUEQADENZ
    UFUGUHOPZUIUEQBURUFUGUHRPZUAUIUEQCURUFUGUHUBPZUJCSTUIULUOUMUPJUIAQHUQULUOMU
    SVAACSTUIBQHUQUMUPMUTVABCSTUCUD $.

  $( Extended non-negative real version of ~ npcan .  (Contributed by Thierry
     Arnoux, 9-Jun-2017.) $)
  xrge0npcan $p |- ( ( A e. ( 0 [,] +oo ) /\ B e. ( 0 [,] +oo ) /\ B <_ A ) ->
     ( ( A +e -e B ) +e B ) = A ) $=
    ( cc0 cpnf co wcel cle wbr wceq cxne wa cxr simpl1 sseldi simpr syl2anc syl
    cxad cmnf wne cicc w3a iccssxr simpl3 eqbrtrrd xgepnf biimpa xnegeq oveq12d
    pnfxr xnegid syl6eq oveq1d oveq2d xaddid2 mp1i 3eqtrd eqtr4d wn xrge0neqmnf
    ax-mp simpl2 xnegcld xnegneg sylan9req xnegmnf ex con3and neneqad syl222anc
    xaddass xnegcl xaddcom mpancom eqtrd xaddid1 sylan9eqr pm2.61dan ) ACDUAEZF
    ZBVSFZBAGHZUBZBDIZABJZREZBREZAIWCWDKZWGDAWHWGCBRECDREZDWHWFCBRWHWFDDJZREZCW
    HADWEWJRWHALFZDAGHZADIZWHVSLACDUCZVTWAWBWDMNWHBDAGWCWDOZVTWAWBWDUDUEWLWMWNA
    UFUGPZWHWDWEWJIWPBDUHQUIDLFZWKCIUJDUKVAULUMWHBDCRWPUNWRWIDIWHUJDUOUPUQWQURW
    CWDUSZKZWGAWEBREZREZAWTWLASTZWELFZWESTZBLFZBSTZWGXBIWTVSLAWOVTWAWBWSMZNZWTV
    TXCXHAUTQWTBWTVSLBWOVTWAWBWSVBZNZVCWTXFWSXEXKWCWSOXFWSKWESXFWESIZWDXFXLWDXF
    XLKBSJZDXFXLBWEJXMBVDWESUHVEVFULVGVHVIPXKWTWAXGXJBUTQAWEBVKVJWTWLXFXBAIXIXK
    XFWLXBACREAXFXACARXFXABWEREZCXDXFXAXNIBVLWEBVMVNBUKVOUNAVPVQPVOVR $.

  ${
    $d k x y A $.  $d x y B $.  $d k x y ph $.
    fsumrp0cl.1 $e |- ( ph -> A e. Fin ) $.
    fsumrp0cl.2 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) ) $.
    $( Closure of a finite sum of positive integers.  (Contributed by Thierry
       Arnoux, 25-Jun-2017.) $)
    fsumrp0cl $p |- ( ph -> sum_ k e. A B e. ( 0 [,) +oo ) ) $=
      ( cc0 cpnf co cr cmnf cxr wcel clt wbr cle pnfxr ax-mp w3a 0xr vx vy cico
      cc wss cioo mnfxr 0re mnflt pnfge icossioo mp4an ioomax sseqtri ax-resscn
      sstri a1i cv wa caddc simprl sseldi simprr readdcld rexrd wb elico1 mp2an
      simp2bi syl addge0d ltpnf syl3anbrc lbico1 mp3an fsumcllem ) AUAUBBCGHUCI
      ZDVQUDUEAVQJUDVQKHUFIZJKLMHLMZKGNOZHHPOZVQVRUEUGQGJMZVTUHGUIRVSWAQHUJRKHG
      HUKULUMUNZUOUPUQAUAURZVQMZUBURZVQMZUSUSZWDWFUTIZLMZGWIPOZWIHNOZWIVQMZWHWI
      WHWDWFWHVQJWDWCAWEWGVAZVBZWHVQJWFWCAWEWGVCZVBZVDZVEWHWDWFWOWQWHWEGWDPOZWN
      WEWDLMZWSWDHNOZGLMZVSWEWTWSXASVFTQGHWDVGVHVIVJWHWGGWFPOZWPWGWFLMZXCWFHNOZ
      XBVSWGXDXCXESVFTQGHWFVGVHVIVJVKWHWIJMWLWRWIVLVJXBVSWMWJWKWLSVFTQGHWIVGVHV
      MEFGVQMZAXBVSGHNOZXFTQWBXGUHGVLRGHVNVOUQVP $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Algebra
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
    Monoids Homomorphisms
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y F $.  $d x y M $.  $d x y N $. 
    $( The image of an Abelian group by a group isomorphism is also
       Abelian.  (Contributed by Thierry Arnoux, 8-Mar-2018.) $)
    abliso $p |- ( ( M e. Abel /\ F e. ( M GrpIso N ) ) -> N e. Abel ) $=
      ( vx vy cabel wcel cgim co wa cghm gimghm syl cv cplusg cfv wceq ad2antlr
      eqid syl3anc cgrp ccmn ghmgrp2 adantl cmnd cbs wral grpmnd ccnv simpll wf
      wf1o gimf1o f1ocnv f1of 3syl simprl ffvelrnd simprr ablcom gimcnv 3eqtr4d
      ghmlin fveq2d adantr grpcl f1ocnvfv2 syl2anc 3eqtr3d iscmn sylanbrc isabl
      ralrimivva ) BFGZABCHIGZJZCUAGZCUBGZCFGVOVQVNVOABCKIGVQBCALBCAUCMUDZVPCUE
      GZDNZENZCOPZIZWBWAWCIZQZECUFPZUGDWGUGVRVPVQVTVSCUHMVPWFDEWGWGVPWAWGGZWBWG
      GZJZJZWDAUIZPZAPZWEWLPZAPZWDWEWKWMWOAWKWAWLPZWBWLPZBOPZIZWRWQWSIZWMWOWKVN
      WQBUFPZGWRXBGWTXAQVNVOWJUJWKWGXBWAWLVOWGXBWLUKZVNWJVOXBWGAULZWGXBWLULXCXB
      WGBCAXBSZWGSZUMZXBWGAUNWGXBWLUOUPRZVPWHWIUQZURWKWGXBWBWLXHVPWHWIUSZURXBWS
      BWQWRXEWSSZUTTWKWLCBKIGZWHWIWMWTQWKWLCBHIGZXLVOXMVNWJBCAVARCBWLLMZXIXJWCW
      SCBWAWLWBWGXFWCSZXKVCTWKXLWIWHWOXAQXNXJXIWCWSCBWBWLWAWGXFXOXKVCTVBVDWKXDW
      DWGGZWNWDQVOXDVNWJXGRZWKVQWHWIXPVPVQWJVSVEZXIXJWGWCCWAWBXFXOVFTXBWGWDAVGV
      HWKXDWEWGGZWPWEQXQWKVQWIWHXSXRXJXIWGWCCWBWAXFXOVFTXBWGWEAVGVHVIVMDEWGWCCX
      FXOVJVKCVLVK $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
    Ordered monoids and groups
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c oMnd $.
  $c oGrp $.

  $( Extend class notation with the class of all ordered monoids. $)
  comnd $a class oMnd $.

  $( Extend class notation with the class of all ordered groups. $)
  cogrp $a class oGrp $.

  ${
    $d a b c g l p v z $.
    $( Define class of all ordered monoids.  An ordered monoid is a monoid with
       a total ordering compatible with its operation.  (Contributed by Thierry
       Arnoux, 13-Mar-2018.) $)
    df-omnd $a |- oMnd = { g e. Mnd | [. ( Base ` g ) / v ].
      [. ( +g ` g ) / p ]. [. ( le ` g ) / l ]. ( g e. Toset /\
      A. a e. v A. b e. v A. c e. v ( a l b -> ( a p c ) l ( b p c ) ) ) } $.

    $( Define class of all ordered groups.  An ordered group is a group with a
       total ordering compatible with its operation.  (Contributed by Thierry
       Arnoux, 13-Mar-2018.) $)
    df-ogrp $a |- oGrp = ( Grp i^i oMnd ) $.
  $}

  ${
    $d a b c l m p v B $.  $d a b c l m p v M $.  $d l m p t .+ $.
    $d l m .<_ $.
    isomnd.0 $e |- B = ( Base ` M ) $.
    isomnd.1 $e |- .+ = ( +g ` M ) $.
    isomnd.2 $e |- .<_ = ( le ` M ) $.
    $( An ordered monoid is a monoid with a total ordering compatible with its
       operation.  (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
    isomnd $p |- ( M e. oMnd <-> ( M e. Mnd /\ M e. Toset /\
      A. a e. B A. b e. B A. c e. B ( a .<_ b -> ( a .+ c ) .<_ ( b .+ c ) )
      ) ) $=
      ( vl vp wcel cv wral wa cfv wsbc wceq cvv vm vv comnd cmnd ctos wbr co wi
      w3a cple cplusg cbs fvex a1i wb simpr fveq2 adantr eqtrd raleq raleqbi1dv
      syl6eqr anbi2d sbcbidv sbcied oveqd breq12d imbi2d ralbidv 2ralbidv bitrd
      biidd simpl fveq2d breqd imbi12d eleq1 anbi1d 3bitrd elrab2 3anass bitr4i
      syl df-omnd ) DUCMDUDMZDUEMZENZFNZCUFZWGGNZBUGZWHWJBUGZCUFZUHZGAOZFAOEAOZ
      PZPWEWFWPUIUANZUEMZWGWHKNZUFZWGWJLNZUGZWHWJXBUGZWTUFZUHZGUBNZOZFXGOZEXGOZ
      PZKWRUJQZRZLWRUKQZRZUBWRULQZRZWQUADUDUCWRDSZXQWSXAWKWLWTUFZUHZGAOZFAOEAOZ
      PZKXLRZWQXRXQWSXFGAOZFAOZEAOZPZKXLRZLXNRZYDXRXOYJUBXPTXPTMXRWRULUMUNXRXGX
      PSZPZXMYILXNYLXKYHKXLYLXJYGWSYLXGASXJYGUOYLXGDULQZAYLXGXPYMXRYKUPXRXPYMSY
      KWRDULUQURUSHVBXIYFEXGAXHYEFXGAXFGXGAUTVAVAWCVCVDVDVEXRYIYDLXNTXNTMXRWRUK
      UMUNXRXBXNSZPZYHYCKXLYOYGYBWSYOYEYAEFAAYOXFXTGAYOXEXSXAYOXCWKXDWLWTYOXBBW
      GWJYOXBDUKQZBYOXBXNYPXRYNUPXRXNYPSYNWRDUKUQURUSIVBZVFYOXBBWHWJYQVFVGVHVIV
      JVCVDVEVKXRYDYDWSWPPZWQXRYDVLXRYCYRKXLTXLTMXRWRUJUMUNXRWTXLSZPZYBWPWSYTYA
      WOEFAAYTXTWNGAYTXAWIXSWMYTWTCWGWHYTWTDUJQZCYTWTXLUUAXRYSUPYTWRDUJXRYSVMVN
      USJVBZVOYTWTCWKWLUUBVOVPVIVJVCVEXRWSWFWPWRDUEVQVRVSVKUBUALEFGKWDVTWEWFWPW
      AWB $.
  $}

  $( An ordered group is a group with a total ordering compatible with its
    operations.  (Contributed by Thierry Arnoux, 23-Mar-2018.) $)
  isogrp $p |- ( G e. oGrp <-> ( G e. Grp /\ G e. oMnd ) ) $=
    ( cgrp comnd cogrp df-ogrp elin2 ) ABCDEF $.

  $( An ordered group is a group.  (Contributed by Thierry Arnoux,
     9-Jul-2018.) $)
  ogrpgrp $p |- ( G e. oGrp -> G e. Grp ) $=
    ( cogrp wcel cgrp comnd isogrp simplbi ) ABCADCAECAFG $.

  ${
    $d a b c M $.
    $( An ordered monoid is a monoid.  (Contributed by Thierry Arnoux,
       13-Mar-2018.) $)
    omndmnd $p |- ( M e. oMnd -> M e. Mnd ) $=
      ( va vb vc comnd wcel cmnd ctos cv cple cfv wbr cplusg co cbs wral isomnd
      wi eqid simp1bi ) AEFAGFAHFBIZCIZAJKZLUADIZAMKZNUBUDUENUCLRDAOKZPCUFPBUFP
      UFUEUCABCDUFSUESUCSQT $.

    $( An ordered monoid is a totally ordered set.  (Contributed by Thierry
       Arnoux, 13-Mar-2018.) $)
    omndtos $p |- ( M e. oMnd -> M e. Toset ) $=
      ( va vb vc comnd wcel cmnd ctos cv cple cfv wbr cplusg co cbs wral isomnd
      wi eqid simp2bi ) AEFAGFAHFBIZCIZAJKZLUADIZAMKZNUBUDUENUCLRDAOKZPCUFPBUFP
      UFUEUCABCDUFSUESUCSQT $.

    $d a b c X $.  $d b c Y $.  $d c Z $.  $d a b c .+ $.  $d a b c .<_ $.
    $d a b c B $.
    omndadd.0 $e |- B = ( Base ` M ) $.
    omndadd.1 $e |- .<_ = ( le ` M ) $.
    omndadd.2 $e |- .+ = ( +g ` M ) $.
    $( In an ordered monoid, the ordering is compatible with group addition.
       (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
    omndadd $p |- ( ( M e. oMnd /\ ( X e. B /\ Y e. B /\ Z e. B )
      /\ X .<_ Y ) -> ( X .+ Z ) .<_ ( Y .+ Z ) ) $=
      ( va vb vc wcel wbr co wi cv wral wceq comnd w3a cmnd ctos isomnd simp3bi
      breq1 oveq1 breq1d imbi12d breq2 breq2d breq12d imbi2d rspc3v syl5 impcom
      oveq2 3impia ) DUANZEANFANGANUBZEFCOZEGBPZFGBPZCOZVAUTVBVEQZUTKRZLRZCOZVG
      MRZBPZVHVJBPZCOZQZMASLASKASZVAVFUTDUCNDUDNVOABCDKLMHJIUEUFVNVFEVHCOZEVJBP
      ZVLCOZQVBVQFVJBPZCOZQKLMEFGAAAVGETZVIVPVMVRVGEVHCUGWAVKVQVLCVGEVJBUHUIUJV
      HFTZVPVBVRVTVHFECUKWBVLVSVQCVHFVJBUHULUJVJGTZVTVEVBWCVQVCVSVDCVJGEBURVJGF
      BURUMUNUOUPUQUS $.

    $( In a right ordered monoid, the ordering is compatible with group
       addition.  (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
    omndaddr $p |- ( ( ( oppG ` M ) e. oMnd  /\ ( X e. B /\ Y e. B /\ Z e. B )
      /\ X .<_ Y ) -> ( Z .+ X ) .<_ ( Z .+ Y ) ) $= 
      ( coppg cfv comnd wcel w3a wbr cplusg co eqid oppgplus oppgbas omndadd
      oppgle 3brtr3g ) DKLZMNEANFANGANOEFCPOEGUEQLZRFGUFRGEBRGFBRCAUFCUEEFGADUE
      UESZHUADCUEUGIUCUFSZUBBUFDUEEGJUGUHTBUFDUEFGJUGUHTUD $.

    ${
      omndadd2d.m $e |- ( ph -> M e. oMnd ) $.
      omndadd2d.w $e |- ( ph -> W e. B ) $.
      omndadd2d.x $e |- ( ph -> X e. B ) $.
      omndadd2d.y $e |- ( ph -> Y e. B ) $.
      omndadd2d.z $e |- ( ph -> Z e. B ) $.
      omndadd2d.1 $e |- ( ph -> X .<_ Z ) $.
      omndadd2d.2 $e |- ( ph -> Y .<_ W ) $.

      ${
        omndadd2d.c $e |- ( ph -> M e. CMnd ) $.
        $( In a commutative left ordered monoid, the ordering is compatible
           with monoid addition.  Double addition version (Contributed by
           Thierry Arnoux, 30-Jan-2018.) $)
        omndadd2d $p |- ( ph -> ( X .+ Y ) .<_ ( Z .+ W ) ) $=
          ( cpo wcel co w3a wbr comnd ctos omndtos tospos 3syl cmnd omndmnd syl
          mndcl syl3anc 3jca omndadd syl131anc ccmn cmncom 3brtr3d wa postr imp
          wceq syl22anc ) AEUAUBZGHCUCZBUBZIHCUCZBUBZIFCUCZBUBZUDZVHVJDUEZVJVLD
          UEZVHVLDUEZAEUFUBZEUGUBVGMEUHEUIUJAVIVKVMAEUKUBZGBUBZHBUBZVIAVRVSMEUL
          UMZOPBCEGHJLUNUOAVSIBUBZWAVKWBQPBCEIHJLUNUOAVSWCFBUBZVMWBQNBCEIFJLUNU
          OUPAVRVTWCWAGIDUEVOMOQPRBCDEGIHJKLUQURAHICUCZFICUCZVJVLDAVRWAWDWCHFDU
          EWEWFDUEMPNQSBCDEHFIJKLUQURAEUSUBZWAWCWEVJVETPQBCEHIJLUTUOAWGWDWCWFVL
          VETNQBCEFIJLUTUOVAVGVNVBVOVPVBVQBEDVHVJVLJKVCVDVF $.
      $}
      
      ${
        omndadd2rd.c $e |- ( ph -> ( oppG ` M ) e. oMnd ) $.
        $( In a left- and right- ordered monoid, the ordering is compatible
           with monoid addition.  Double addition version (Contributed by
           Thierry Arnoux, 2-May-2018.) $)
        omndadd2rd $p |- ( ph -> ( X .+ Y ) .<_ ( Z .+ W ) ) $=
          ( cpo wcel co w3a wbr comnd ctos omndtos tospos 3syl cmnd omndmnd syl
          mndcl syl3anc 3jca coppg omndaddr syl131anc omndadd wa postr syl22anc
          cfv imp ) AEUAUBZGHCUCZBUBZGFCUCZBUBZIFCUCZBUBZUDZVGVIDUEZVIVKDUEZVGV
          KDUEZAEUFUBZEUGUBVFMEUHEUIUJAVHVJVLAEUKUBZGBUBZHBUBZVHAVQVRMEULUMZOPB
          CEGHJLUNUOAVRVSFBUBZVJWAONBCEGFJLUNUOAVRIBUBZWBVLWAQNBCEIFJLUNUOUPAEU
          QVDUFUBVTWBVSHFDUEVNTPNOSBCDEHFGJKLURUSAVQVSWCWBGIDUEVOMOQNRBCDEGIFJK
          LUTUSVFVMVAVNVOVAVPBEDVGVIVKJKVBVEVC $.
      $}
    $}
  $}

  ${
    $d a b c A $.  $d a b c M $. 
    $( A submonoid of an ordered monoid is also ordered.  (Contributed by
       Thierry Arnoux, 23-Mar-2018.) $)
    submomnd $p |- ( ( M e. oMnd /\ ( M |`s A ) e. Mnd ) 
      -> ( M |`s A ) e. oMnd ) $=
      ( va vb vc wcel co wa cv cfv wbr cbs wral w3a cvv adantr c0 wceq eqid syl
      comnd cress cmnd ctos cple cplusg wi simpr reldmress ovprc2 fveq2d adantl
      omndtos base0 syl6eqr wne c0g mndidcl ne0i ad2antlr neneqd condan resstos
      wn syl2anc simplll wss cin ressbas inss2 syl6eqssr simplr1 sseldd simplr2
      ad2antrr simplr3 3jca breqd biimpar omndadd syl3anc wb ressplusg breq123d
      ressle oveqd mpbid ex ralrimivvva isomnd sylibr ) BUAFZBAUBGZUCFZHZWNWMUD
      FZCIZDIZWMUEJZKZWQEIZWMUFJZGZWRXAXBGZWSKZUGZEWMLJZMDXGMCXGMZNWMUAFWOWNWPX
      HWLWNUHWOBUDFZAOFZWPWLXIWNBUMPWOXJXGQRWOXJVDZHZXGQLJZQXKXGXMRWOXKWMQLBAUB
      UIUJUKULUNUOXLXGQWNXGQUPZWLXKWNWMUQJZXGFXNXGWMXOXGSZXOSURXGXOUSTUTVAVBZAB
      OVCVEWOXFCDEXGXGXGWOWQXGFZWRXGFZXAXGFZNZHZWTXEYBWTHZWQXABUFJZGZWRXAYDGZBU
      EJZKZXEYCWLWQBLJZFZWRYIFZXAYIFZNWQWRYGKZYHWLWNYAWTVFYCYJYKYLYCXGYIWQWOXGY
      IVGZYAWTWOXJYNXQXJXGAYIVHYIAYIWMOBWMSZYISZVIAYIVJVKTVOZXRXSXTWOWTVLVMYCXG
      YIWRYQXRXSXTWOWTVNVMYCXGYIXAYQXRXSXTWOWTVPVMVQYBYMWTYBYGWSWQWRWOYGWSRZYAW
      OXJYRXQABYGOWMYOYGSZWEZTPVRVSYIYDYGBWQWRXAYPYSYDSZVTWAYBYHXEWBWTYBYEXCYFX
      DYGWSYBYDXBWQXAYBXJYDXBRWOXJYAXQPZAYDBWMOYOUUAWCTZWFYBXJYRUUBYTTYBYDXBWRX
      AUUCWFWDPWGWHWIVQXGXBWSWMCDEXPXBSWSSWJWK $.
  $}

  ${
    $d x y z $.
    $( The nonnegative extended real numbers form an ordered monoid.
       (Contributed by Thierry Arnoux, 22-Mar-2018.) $)
    xrge0omnd $p |- ( RR*s |`s ( 0 [,] +oo ) ) e. oMnd $=
      ( vx vy vz cxrs cc0 cpnf co wcel cv cle wbr cxad wi wral cvv wa w3a sseli
      cxr xrge0base cicc cress comnd cmnd ctos ccmn xrge0cmn cmnmnd cpo wo wceq
      ax-mp ovex iccssxr xrleid 3ad2ant1 xrletri3 biimprd syl2an 3adant3 xrletr
      syl syl3an 3jca rgen3 cple cfv eqid xrsle ressle mpbir2an anim12i xrletri
      ispos rgen2a istos xleadd1a ex xrge0plusg isomnd mpbir3an ) DEFUAGZUBGZUC
      HWCUDHZWCUEHZAIZBIZJKZWFCIZLGWGWILGJKZMZCWBNBWBNAWBNWCUFHWDUGWCUHULWEWCUI
      HZWHWGWFJKZUJZBWBNAWBNWLWCOHWFWFJKZWHWMPZWFWGUKZMZWHWGWIJKPWFWIJKMZQZCWBN
      BWBNAWBNDWBUBUMWTABCWBWBWBWFWBHZWGWBHZWIWBHZQWOWRWSXAXBWOXCXAWFSHZWOWBSWF
      EFUNZRZWFUOVBUPXAXBWRXCXAXDWGSHZWRXBXFWBSWGXERZXDXGPZWQWPWFWGUQURUSUTXAXD
      XBXGXCWISHZWSXFXHWBSWIXERZWFWGWIVAVCVDVEABCWBWCJTWBOHJWCVFVGUKEFUAUMWBDJO
      WCWCVHVIVJULZVNVKWNABWBXAXBPXIWNXAXDXBXGXFXHVLWFWGVMVBVOABWBWCJTXLVPVKWKA
      BCWBWBWBXAXDXBXGXCXJWKXFXHXKXDXGXJQWHWJWFWGWIVQVRVCVEWBLJWCABCTVSXLVTWA
      $.
  $}

  ${
    $d m n B $.  $d m n M $.  $d m n N $.  $d m n X $.  $d m n Y $.
    $d m n .0. $.  $d m n .<_ $.  $d m n .x. $.  $d m n ph $.
    omndmul.0 $e |- B = ( Base ` M ) $.
    omndmul.1 $e |- .<_ = ( le ` M ) $.
    ${
      omndmul2.2 $e |- .x. = ( .g ` M ) $.
      omndmul2.3 $e |- .0. = ( 0g ` M ) $.
      $( In an ordered monoid, the ordering is compatible with group power.
         This version does not require the monoid to be commutative.
         (Contributed by Thierry Arnoux, 23-Mar-2018.) $)
      omndmul2 $p |- ( ( M e. oMnd /\ ( X e. B /\ N e. NN0 ) /\ .0. .<_ X ) ->
        .0. .<_ ( N .x. X ) ) $=
        ( wcel cn0 wa wbr w3a co c1 wceq syl df-3an 3anass bitr3i anbi1i bitr4i
        vm vn comnd simplr cv cc0 caddc oveq1 breq2d cpo omndtos tospos omndmnd
        ctos mndidcl posref syl2anc ad3antrrr ad3antlr breqtrrd ad5antr simp-5r
        cmnd mulg0 mulgnn0cl syl3anc simpr32 1nn0 nn0addcld 3anassrs 3jca simpr
        a1i cplusg cfv simp-4l ad4antr simp-4r eqid syl131anc mndlid mulgnn0dir
        omndadd syl13anc cc ax-1cn simpr3 nn0cnd addcomd mulg1 3eqtr3rd 3brtr3d
        oveq1d adantr jca postr imp syl21anc nn0indd mpdan sylbi ) DUHLZFALZEML
        ZNZGFCOZPZXGXHNZXINZXKNZGEFBQZCOZXLXGXJNZXKNXOXGXJXKUAXNXRXKXNXGXHXIPXR
        XGXHXIUAXGXHXIUBUCUDUEXOXIXQXMXIXKUIXOGUFUJZFBQZCOGUKFBQZCOGUGUJZFBQZCO
        ZGYBRULQZFBQZCOZXQUFUGEXSUKSXTYAGCXSUKFBUMUNXSYBSXTYCGCXSYBFBUMUNXSYESX
        TYFGCXSYEFBUMUNXSESXTXPGCXSEFBUMUNXOGGYACXGGGCOZXHXIXKXGDUOLZGALZYHXGDU
        SLYIDUPDUQTZXGDVHLZYJDURZADGHKUTZTADCGHIVAVBVCXHYAGSXGXIXKABDFGHKJVIVDV
        EXOYBMLZNZYDNZYIYJYCALZYFALZPZYDYCYFCOZNZYGXGYIXHXIXKYOYDYKVFYQYJYRYSYQ
        YLYJXGYLXHXIXKYOYDYMVFZYNTYQYLYOXHYRUUCXOYOYDUIXGXHXIXKYOYDVGZABDYBFHJV
        JZVKYQYLYEMLZXHYSUUCXNXKYOYDUUFXGXHXIXKYOYDPZUUFXGXHXIUUGPNZYBRXKYOYDXH
        XIXGVLRMLZUUHVMVRVNVOVOUUDABDYEFHJVJVKVPYQYDUUAYPYDVQYPUUAYDYPGYCDVSVTZ
        QZFYCUUJQZYCYFCYPXGYJXHYRXKUUKUULCOXGXHXIXKYOWAYPYLYJXGYLXHXIXKYOYMWBZY
        NTXGXHXIXKYOWCZYPYLYOXHYRUUMXOYOVQZUUNUUEVKZXNXKYOUIAUUJCDGFYCHIUUJWDZW
        HWEYPYLYRUUKYCSUUMUUPAUUJDYCGHUUQKWFVBYPRYBULQZFBQZRFBQZYCUUJQZYFUULYPY
        LUUIYOXHUUSUVASUUMUUIYPVMVRUUOUUNAUUJBDRYBFHJUUQWGWIYPUURYEFBXMXIXKYOUU
        RYESXMXIXKYOPNZRYBRWJLUVBWKVRUVBYBXMXIXKYOWLWMWNVOWRYPUUTFYCUUJYPXHUUTF
        SUUNABDFHJWOTWRWPWQWSWTYIYTNUUBYGADCGYCYFHIXAXBXCXDXEXF $.
    $}

    ${    
      omndmul3.m $e |- .x. = (  .g ` M ) $.
      omndmul3.0 $e |- .0. = ( 0g ` M ) $.
      omndmul3.o $e |- ( ph -> M e. oMnd ) $.
      omndmul3.1 $e |- ( ph -> N e. NN0 ) $.
      omndmul3.2 $e |- ( ph -> P e. NN0 ) $.
      omndmul3.3 $e |- ( ph -> N <_ P ) $.
      omndmul3.4 $e |- ( ph -> X e. B ) $.
      omndmul3.5 $e |- ( ph -> .0. .<_ X ) $.
      $( In an ordered monoid, the ordering is compatible with group power.
         This version does not require the monoid to be commutative.
         (Contributed by Thierry Arnoux, 23-Mar-2018.) $)
      omndmul3 $p |- ( ph -> ( N .x. X ) .<_ ( P .x. X ) ) $=
        ( wcel co cplusg cfv cmin comnd wbr cmnd omndmnd syl mndidcl cn0 cle wa
        nn0sub biimpa syl21anc mulgnn0cl omndmul2 syl121anc eqid syl131anc wceq
        syl3anc omndadd mndlid syl2anc mulgnn0dir syl13anc nn0cnd npcand oveq1d
        caddc eqtr3d 3brtr3d ) AIGHDUAZFUBUCZUAZCGUDUAZHDUAZVOVPUAZVOCHDUAZEAFU
        ETZIBTZVSBTZVOBTZIVSEUFZVQVTEUFNAFUGTZWCAWBWGNFUHUIZBFIJMUJUIAWGVRUKTZH
        BTZWDWHAGUKTZCUKTZGCULUFZWIOPQWKWLUMWMWIGCUNUOUPZRBDFVRHJLUQVCAWGWKWJWE
        WHORBDFGHJLUQVCZAWBWJWIIHEUFWFNRWNSBDEFVRHIJKLMURUSBVPEFIVSVOJKVPUTZVDV
        AAWGWEVQVOVBWHWOBVPFVOIJWPMVEVFAVRGVLUAZHDUAZVTWAAWGWIWKWJWRVTVBWHWNORB
        VPDFVRGHJLWPVGVHAWQCHDACGACPVIAGOVIVJVKVMVN $.
    $}

    ${
      omndmul.2 $e |- .x. = ( .g ` M ) $.
      omndmul.o $e |- ( ph -> M e. oMnd ) $.
      omndmul.c $e |- ( ph -> M e. CMnd ) $.
      omndmul.x $e |- ( ph -> X e. B ) $.
      omndmul.y $e |- ( ph -> Y e. B ) $.
      omndmul.n $e |- ( ph -> N e. NN0 ) $.
      omndmul.l $e |- ( ph -> X .<_ Y ) $.
      $( In a commutative ordered monoid, the ordering is compatible with group
         power.  (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
      omndmul $p |- ( ph -> ( N .x. X ) .<_ ( N .x. Y ) ) $=
        ( wcel co wceq vm vn cn0 wbr cv cc0 c1 caddc oveq1 breq12d ctos omndtos
        cpo comnd tospos 3syl c0g cfv eqid mulg0 omndmnd mndidcl eqeltrd posref
        syl cmnd syl2anc wb wa adantr adantl eqtr4d breq1d mpbird cplusg simplr
        ad2antrr mulgnn0cl syl3anc simpr ccmn omndadd2d mulgnn0p1 3brtr4d mpdan
        nn0indd ) AFUCRFGCSZFHCSZDUDZPAUAUEZGCSZWJHCSZDUDUFGCSZUFHCSZDUDZUBUEZG
        CSZWPHCSZDUDZWPUGUHSZGCSZWTHCSZDUDWIUAUBFWJUFTWKWMWLWNDWJUFGCUIWJUFHCUI
        UJWJWPTWKWQWLWRDWJWPGCUIWJWPHCUIUJWJWTTWKXAWLXBDWJWTGCUIWJWTHCUIUJWJFTW
        KWGWLWHDWJFGCUIWJFHCUIUJAWOWNWNDUDZAEUMRZWNBRXCAEUNRZEUKRXDLEULEUOUPAWN
        EUQURZBAHBRZWNXFTZOBCEHXFIXFUSZKUTZVEAXEEVFRZXFBRLEVAZBEXFIXIVBUPVCBEDW
        NIJVDVGAGBRZXGWOXCVHNOXMXGVIZWMWNWNDXNWMXFWNXMWMXFTXGBCEGXFIXIKUTVJXGXH
        XMXJVKVLVMVGVNAWPUCRZVIZWSVIZWQGEVOURZSZWRHXRSZXAXBDXQBXRDEHWQGWRIJXRUS
        ZAXEXOWSLVQZAXGXOWSOVQZXQXKXOXMWQBRXQXEXKYBXLVEZAXOWSVPZAXMXOWSNVQZBCEW
        PGIKVRVSYFXQXKXOXGWRBRYDYEYCBCEWPHIKVRVSXPWSVTAGHDUDXOWSQVQAEWARXOWSMVQ
        WBXQXKXOXMXAXSTYDYEYFBXRCEWPGIKYAWCVSXQXKXOXGXBXTTYDYEYCBXRCEWPHIKYAWCV
        SWDWFWE $.
    $}
  $}

  ${
    ogrpsub.0 $e |- B = ( Base ` G ) $.
    ogrpsub.1 $e |- .<_ = ( le ` G ) $.
    ${
      ogrpinv.2 $e |- I = ( invg ` G ) $.
      ogrpinv.3 $e |- .0. = ( 0g ` G ) $.
      $( In an ordered group, the ordering is compatible with group inverse.
         (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
      ogrpinvOLD $p |- ( ( G e. oGrp /\ X e. B /\ .0. .<_ X )
        -> ( I ` X ) .<_ .0. ) $=
        ( cogrp wcel wbr w3a cfv cplusg co 3ad2ant1 syl2anc wceq isogrp simprbi
        comnd cgrp simplbi grpidcl syl simp2 grpinvcl simp3 eqid omndadd grplid
        syl131anc grprinv 3brtr3d ) BKLZEALZFEDMZNZFECOZBPOZQZEVAVBQZVAFDUTBUCL
        ZFALZURVAALZUSVCVDDMUQURVEUSUQBUDLZVEBUAZUBRUTVHVFUQURVHUSUQVHVEVIUERZA
        BFGJUFUGUQURUSUHZUTVHURVGVJVKABCEGIUISZUQURUSUJAVBDBFEVAGHVBUKZULUNUTVH
        VGVCVATVJVLAVBBVAFGVMJUMSUTVHURVDFTVJVKAVBBCEFGVMJIUOSUP $.

      $( In an ordered group, the ordering is compatible with group inverse.
         (Contributed by Thierry Arnoux, 3-Sep-2018.) $)
      ogrpinv0le $p |- ( ( G e. oGrp /\ X e. B ) 
        -> ( .0. .<_ X <-> ( I ` X ) .<_ .0. ) ) $=
        ( wcel wa wbr cfv co ad2antrr 3syl simplr syl2anc wceq cogrp comnd cgrp
        cplusg simprbi cmnd omndmnd mndidcl simplbi grpinvcl simpr eqid omndadd
        isogrp syl131anc grplid grprinv 3brtr3d grplinv impbida ) BUAKZEAKZLZFE
        DMZECNZFDMZVCVDLZFVEBUDNZOZEVEVHOZVEFDVGBUBKZFAKZVBVEAKZVDVIVJDMVAVKVBV
        DVABUCKZVKBUNZUEZPZVGVKBUFKZVLVQBUGZABFGJUHZQVAVBVDRZVGVNVBVMVAVNVBVDVA
        VNVKVOUIZPZWAABCEGIUJZSZVCVDUKAVHDBFEVEGHVHULZUMUOVGVNVMVIVETWCWEAVHBVE
        FGWFJUPSVGVNVBVJFTWCWAAVHBCEFGWFJIUQSURVCVFLZVEEVHOZFEVHOZFEDWGVKVMVLVB
        VFWHWIDMVAVKVBVFVPPZWGVNVBVMVAVNVBVFWBPZVAVBVFRZWDSWGVKVRVLWJVSVTQWLVCV
        FUKAVHDBVEFEGHWFUMUOWGVNVBWHFTWKWLAVHBCEFGWFJIUSSWGVNVBWIETWKWLAVHBEFGW
        FJUPSURUT $.
    $}

    ${
      ogrpsub.2 $e |- .- = ( -g ` G ) $.
      $( In an ordered group, the ordering is compatible with group subtraction
         (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
      ogrpsub $p |- ( ( G e. oGrp /\ ( X e. B /\ Y e. B /\ Z e. B )
        /\ X .<_ Y ) -> ( X .- Z ) .<_ ( Y .- Z ) ) $=
        ( wcel w3a wbr cfv co 3ad2ant1 eqid syl2anc wceq grpsubval cogrp cplusg
        cminusg comnd cgrp isogrp simprbi simp21 simp22 simplbi simp23 grpinvcl
        simp3 omndadd syl131anc 3brtr4d ) BUAKZEAKZFAKZGAKZLZEFCMZLZEGBUCNZNZBU
        BNZOZFVEVFOZEGDOZFGDOZCVCBUDKZURUSVEAKZVBVGVHCMUQVAVKVBUQBUEKZVKBUFZUGP
        UQURUSUTVBUHZUQURUSUTVBUIZVCVMUTVLUQVAVMVBUQVMVKVNUJPUQURUSUTVBUKZABVDG
        HVDQZULRUQVAVBUMAVFCBEFVEHIVFQZUNUOVCURUTVIVGSVOVQAVFBVDDEGHVSVRJTRVCUS
        UTVJVHSVPVQAVFBVDDFGHVSVRJTRUP $.
    $}
  $}

  ${
    ogrpaddlt.0 $e |- B = ( Base ` G ) $.
    ogrpaddlt.1 $e |- .< = ( lt ` G ) $.
    ogrpaddlt.2 $e |- .+ = ( +g ` G ) $.
    $( In an ordered group, strict ordering is compatible with group addition.
       (Contributed by Thierry Arnoux, 20-Jan-2018.) $)
    ogrpaddlt $p |- ( ( G e. oGrp /\ ( X e. B /\ Y e. B /\ Z e. B )
      /\ X .< Y ) -> ( X .+ Z ) .< ( Y .+ Z ) ) $=
      ( cogrp wcel w3a wbr co wne wa imp syl31anc cvv cple cfv comnd simp1 cgrp
      isogrp simprbi simp2 simp1d simp2d simp3 eqid pltle omndadd syl3anc pltne
      syl wceq wi simplbi grprcan biimpd sylan necon3d 3impia wb pltval mp3an23
      jca ovex 3ad2ant1 mpbird ) DKLZEALZFALZGALZMZEFCNZMZEGBOZFGBOZCNZVTWADUAU
      BZNZVTWAPZQZVSWDWEVSDUCLZVQEFWCNZWDVSVMWGVMVQVRUDZVMDUELZWGDUFZUGUQVMVQVR
      UHZVSVMVNVOVRWHWIVSVNVOVPWLUIZVSVNVOVPWLUJZVMVQVRUKZVMVNVOMZVRWHKAACDWCEF
      WCULZIUMRSABWCDEFGHWQJUNUOVSVMVQEFPZWEWIWLVSVMVNVOVRWRWIWMWNWOWPVRWRKAACD
      EFIUPRSVMVQWRWEVMVQQVTWAEFVMWJVQVTWAURZEFURZUSVMWJWGWKUTWJVQQWSWTABDEFGHJ
      VAVBVCVDVEUOVIVMVQWBWFVFZVRVMVTTLWATLXAEGBVJFGBVJKTTCDWCVTWAWQIVGVHVKVL
      $.

    $( In a right ordered group, strict ordering is compatible with group
       addition.  (Contributed by Thierry Arnoux, 3-Sep-2018.) $)
    ogrpaddltbi $p |- ( ( G e. oGrp /\ ( X e. B /\ Y e. B /\ Z e. B ) )
       -> ( X .< Y <-> ( X .+ Z ) .< ( Y .+ Z ) ) ) $=
      ( wcel wa wbr co ogrpaddlt cfv grpcl syl3anc syl2anc wceq cogrp w3a 3expa
      cminusg cgrp ogrpgrp syl simplr1 simplr3 simplr2 grpinvcl simpr syl131anc
      simpll eqid c0g grpass grprinv oveq2d grprid 3eqtrd breq12d mpbid impbida
      syl13anc ) DUAKZEAKZFAKZGAKZUBZLZEFCMZEGBNZFGBNZCMZVFVJVLVOABCDEFGHIJOUCV
      KVOLZVMGDUDPZPZBNZVNVRBNZCMZVLVPVFVMAKZVNAKZVRAKZVOWAVFVJVOUNZVPDUEKZVGVI
      WBVPVFWFWEDUFUGZVGVHVIVFVOUHZVGVHVIVFVOUIZABDEGHJQRVPWFVHVIWCWGVGVHVIVFVO
      UJZWIABDFGHJQRVPWFVIWDWGWIADVQGHVQUOZUKSZVKVOULABCDVMVNVRHIJOUMVPVSEVTFCV
      PVSEGVRBNZBNZEDUPPZBNZEVPWFVGVIWDVSWNTWGWHWIWLABDEGVRHJUQVEVPWMWOEBVPWFVI
      WMWOTWGWIABDVQGWOHJWOUOZWKURSZUSVPWFVGWPETWGWHABDEWOHJWQUTSVAVPVTFWMBNZFW
      OBNZFVPWFVHVIWDVTWSTWGWJWIWLABDFGVRHJUQVEVPWMWOFBWRUSVPWFVHWTFTWGWJABDFWO
      HJWQUTSVAVBVCVD $.

    ogrpaddltrd.1 $e |- ( ph -> G e. V ) $.
    ogrpaddltrd.2 $e |- ( ph -> ( oppG ` G ) e. oGrp ) $.
    ogrpaddltrd.3 $e |- ( ph -> X e. B ) $.
    ogrpaddltrd.4 $e |- ( ph -> Y e. B ) $.
    ogrpaddltrd.5 $e |- ( ph -> Z e. B ) $.
    ${
      ogrpaddltrd.6 $e |- ( ph -> X .< Y ) $.
      $( In a right ordered group, strict ordering is compatible with group
         addition.  (Contributed by Thierry Arnoux, 3-Sep-2018.) $)
      ogrpaddltrd $p |- ( ph -> ( Z .+ X ) .< ( Z .+ Y ) ) $=
      ( wbr wcel coppg cfv cplt cplusg cogrp wceq eqid oppglt syl breqd oppgbas
      co mpbid ogrpaddlt syl131anc oppgplus 3brtr3g mpbird ) AIGCULZIHCULZDSUSU
      TEUAUBZUCUBZSAGIVAUDUBZULZHIVCULZUSUTVBAVAUETGBTHBTIBTGHVBSZVDVEVBSNOPQAG
      HDSVFRADVBGHAEFTDVBUFMEDVAFVAUGZKUHUIZUJUMBVCVBVAGHIBEVAVGJUKVBUGVCUGZUNU
      OCVCEVAGILVGVIUPCVCEVAHILVGVIUPUQADVBUSUTVHUJUR $.
    $}
 
    $( In a right ordered group, strict ordering is compatible with group
       addition.  (Contributed by Thierry Arnoux, 4-Sep-2018.) $)
    ogrpaddltrbid $p |- ( ph -> ( X .< Y <-> ( Z .+ X ) .< ( Z .+ Y ) ) ) $=
      ( co wcel adantr wbr wa coppg cfv cogrp simpr ogrpaddltrd cminusg ogrpgrp
      cgrp syl w3a cplusg eqid oppgplus oppgbas grpcl syl5eqelr oppggrpb sylibr
      syl3anc grpinvcl syl2anc c0g wceq grplinv oveq1d syl13anc 3eqtr3d 3brtr3d
      grpass grplid impbida ) AGHDUAZIGCRZIHCRZDUAZAVNUBBCDEFGHIJKLAEFSZVNMTAEU
      CUDZUESZVNNTAGBSZVNOTAHBSZVNPTAIBSZVNQTAVNUFUGAVQUBZIEUHUDZUDZVOCRZWFVPCR
      ZGHDWDBCDEFVOVPWFJKLAVRVQMTAVTVQNTWDVSUJSZWAWCVOBSAWIVQAVTWINVSUIUKTZAWAV
      QOTZAWCVQQTZWIWAWCULVOGIVSUMUDZRBCWMEVSGILVSUNZWMUNZUOBWMVSGIBEVSWNJUPZWO
      UQURVAWDWIWBWCVPBSWJAWBVQPTZWLWIWBWCULVPHIWMRBCWMEVSHILWNWOUOBWMVSHIWPWOU
      QURVAWDEUJSZWCWFBSZWDWIWRWJEVSWNUSUTZWLBEWEIJWEUNZVBVCZAVQUFUGWDWFICRZGCR
      ZEVDUDZGCRZWGGWDXCXEGCWDWRWCXCXEVEWTWLBCEWEIXEJLXEUNZXAVFVCZVGWDWRWSWCWAX
      DWGVEWTXBWLWKBCEWFIGJLVKVHWDWRWAXFGVEWTWKBCEGXEJLXGVLVCVIWDXCHCRZXEHCRZWH
      HWDXCXEHCXHVGWDWRWSWCWBXIWHVEWTXBWLWQBCEWFIHJLVKVHWDWRWBXJHVEWTWQBCEHXEJL
      XGVLVCVIVJVM $.
  $}

  ${
    ogrpsublt.0 $e |- B = ( Base ` G ) $.
    ogrpsublt.1 $e |- .< = ( lt ` G ) $.
    ogrpsublt.2 $e |- .- = ( -g ` G ) $.
    $( In an ordered group, strict ordering is compatible with group addition.
       (Contributed by Thierry Arnoux, 3-Sep-2018.) $)
    ogrpsublt $p |- ( ( G e. oGrp /\ ( X e. B /\ Y e. B /\ Z e. B )
      /\ X .< Y ) -> ( X .- Z ) .< ( Y .- Z ) ) $=
      ( cogrp wcel w3a wbr co wne wa wb pltval syl3anc cple simp1 simp21 simp22
      simp23 simp3 eqid mpbid simpld ogrpsub syl131anc simprd cgrp wceq ogrpgrp
      cfv syl grpsubrcan syl13anc necon3bid mpbird jca grpsubcl ) CKLZEALZFALZG
      ALZMZEFBNZMZEGDOZFGDOZBNZVKVLCUAUPZNZVKVLPZQZVJVOVPVJVDVEVFVGEFVNNZVOVDVH
      VIUBZVDVEVFVGVIUCZVDVEVFVGVIUDZVDVEVFVGVIUEZVJVREFPZVJVIVRWCQZVDVHVIUFVJV
      DVEVFVIWDRVSVTWAKAABCVNEFVNUGZISTUHZUIACVNDEFGHWEJUJUKVJVPWCVJVRWCWFULVJV
      KVLEFVJCUMLZVEVFVGVKVLUNEFUNRVJVDWGVSCUOUQZVTWAWBACDEFGHJURUSUTVAVBVJVDVK
      ALZVLALZVMVQRVSVJWGVEVGWIWHVTWBACDEGHJVCTVJWGVFVGWJWHWAWBACDFGHJVCTKAABCV
      NVKVLWEISTVA $.
  $}
  
  ${
    ogrpinvlt.0 $e |- B = ( Base ` G ) $.
    ogrpinvlt.1 $e |- .< = ( lt ` G ) $.
    ogrpinvlt.2 $e |- I = ( invg ` G ) $.
    ${
      ogrpinv0lt.3 $e |- .0. = ( 0g ` G ) $.
      $( In an ordered group, the ordering is compatible with group inverse.
         (Contributed by Thierry Arnoux, 3-Sep-2018.) $)
      ogrpinv0lt $p |- ( ( G e. oGrp /\ X e. B ) 
        -> ( .0. .< X <-> ( I ` X ) .< .0. ) ) $=
        ( wcel wa wbr cfv co simpll syl simplr syl2anc wceq cplusg cgrp ogrpgrp
        cogrp grpidcl grpinvcl simpr ogrpaddlt syl131anc grplid grprinv 3brtr3d
        eqid 3syl grplinv impbida ) CUDKZEAKZLZFEBMZEDNZFBMZUSUTLZFVACUANZOZEVA
        VDOZVAFBVCUQFAKZURVAAKZUTVEVFBMUQURUTPZVCCUBKZVGVCUQVJVICUCZQZACFGJUEZQ
        UQURUTRZVCVJURVHVLVNACDEGIUFZSZUSUTUGAVDBCFEVAGHVDUMZUHUIVCVJVHVEVATVLV
        PAVDCVAFGVQJUJSVCVJURVFFTVLVNAVDCDEFGVQJIUKSULUSVBLZVAEVDOZFEVDOZFEBVRU
        QVHVGURVBVSVTBMUQURVBPZVRVJURVHVRUQVJWAVKQZUQURVBRZVOSVRUQVJVGWAVKVMUNW
        CUSVBUGAVDBCVAFEGHVQUHUIVRVJURVSFTWBWCAVDCDEFGVQJIUOSVRVJURVTETWBWCAVDC
        EFGVQJUJSULUP $.
    $}
    
    $( In an ordered group, the ordering is compatible with group inverse.
       (Contributed by Thierry Arnoux, 3-Sep-2018.) $)
    ogrpinvlt $p |- ( ( ( G e. oGrp /\ ( oppG ` G ) e. oGrp )
      /\ X e. B /\ Y e. B ) -> ( X .< Y <-> ( I ` Y ) .< ( I ` X ) ) ) $=
      ( cogrp wcel coppg cfv wbr co grpinvcl syl2anc eqid syl13anc wceq w3a c0g
      wa cplusg wb simp1l simp2 simp3 ogrpgrp ogrpaddltbi grprinv breq2d simp1r
      cgrp syl grpcl syl3anc grpidcl ogrpaddltrbid 3bitrd grplinv oveq1d grpass
      3syl grplid 3eqtr3d grprid breq12d bitrd ) CJKZCLMJKZUCZEAKZFAKZUAZEFBNZE
      DMZEFDMZCUDMZOZVSOZVQCUBMZVSOZBNZVRVQBNVOVPVTFVRVSOZBNZVTWBBNWDVOVJVMVNVR
      AKZVPWFUEVJVKVMVNUFZVLVMVNUGZVLVMVNUHZVOCUNKZVNWGVOVJWKWHCUIZUOZWJACDFGIP
      QZAVSBCEFVRGHVSRZUJSVOWEWBVTBVOWKVNWEWBTWMWJAVSCDFWBGWOWBRZIUKQULVOAVSBCJ
      VTWBVQGHWOWHVJVKVMVNUMVOWKVMWGVTAKWMWIWNAVSCEVRGWOUPUQVOVJWKWBAKWHWLACWBG
      WPURVDVOWKVMVQAKZWMWIACDEGIPQZUSUTVOWAVRWCVQBVOVQEVSOZVRVSOZWBVRVSOZWAVRV
      OWSWBVRVSVOWKVMWSWBTWMWIAVSCDEWBGWOWPIVAQVBVOWKWQVMWGWTWATWMWRWIWNAVSCVQE
      VRGWOVCSVOWKWGXAVRTWMWNAVSCVRWBGWOWPVEQVFVOWKWQWCVQTWMWRAVSCVQWBGWOWPVGQV
      HVI $.
  
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
    The Archimedean property for generic ordered algebraic structures
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c <<< $.
  $c Archi $.

  $( Class notation for the infinitesimal relation $)
  cinftm $a class <<< $.

  $( Class notation for the Archimedean property $)
  carchi $a class Archi $.

  ${
    $d n w x y $.
    $( Define the relation " ` x ` is infinitesimal with respect to ` y ` " for
       a structure ` w ` .  (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
    df-inftm $a |- <<< = ( w e. _V |-> { <. x , y >. | ( ( x e. ( Base ` w ) /\
      y e. ( Base ` w ) ) /\ ( ( 0g ` w ) ( lt ` w ) x /\
      A. n e. NN ( n ( .g ` w ) x ) ( lt ` w ) y ) ) } ) $.
  $}

  $( A structure said to be Archimedean if it has no infinitesimal elements.
     (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
  df-archi $a |- Archi = { w e. _V | ( <<< ` w ) = (/) } $.

  ${
    $d w x y B $.  $d n w x y W $.  $d n x y X $.  $d n x y Y $.
    $d w x y .< $.  $d w x y .x. $.  $d w x y .0. $.
    inftm.b $e |- B = ( Base ` W ) $.
    $( The infinitesimal relation for a structure ` W ` (Contributed by Thierry
       Arnoux, 30-Jan-2018.) $)
    inftmrel $p |- ( W e. V -> ( <<< ` W ) C_ ( B X. B ) ) $=
      ( vx vy vn vw wcel cfv cv wa c0g cplt wbr cmg cn cvv cbs fveq2 wral copab
      cinftm cxp wceq elex syl6eqr eleq2d anbi12d eqidd breq123d oveqd opabbidv
      co ralbidv df-inftm fvex eqeltri xpex opabssxp ssexi fvmpt syl syl6eqss )
      CBIZCUCJZEKZAIZFKZAIZLZCMJZVGCNJZOZGKZVGCPJZUNZVIVMOZGQUAZLZLZEFUBZAAUDZV
      ECRIVFWBUECBUFHCVGHKZSJZIZVIWEIZLZWDMJZVGWDNJZOZVOVGWDPJZUNZVIWJOZGQUAZLZ
      LZEFUBWBRUCWDCUEZWQWAEFWRWHVKWPVTWRWFVHWGVJWRWEAVGWRWECSJZAWDCSTDUGZUHWRW
      EAVIWTUHUIWRWKVNWOVSWRWIVLVGVGWJVMWDCMTWDCNTZWRVGUJUKWRWNVRGQWRWMVQVIVIWJ
      VMWRWLVPVOVGWDCPTULXAWRVIUJUKUOUIUIUMEFHGUPWBWCAAAWSRDCSUQURZXBUSVTEFAAUT
      ZVAVBVCXCVD $.

    inftm.0 $e |- .0. = ( 0g ` W ) $.
    inftm.x $e |- .x. = ( .g ` W ) $.
    inftm.l $e |- .< = ( lt ` W ) $.
    $( Express ` x ` is infinitesimal with respect to ` y ` for a structure
       ` W ` .  (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
    isinftm $p |- ( ( W e. V /\ X e. B /\ Y e. B ) ->
      ( X ( <<< ` W ) Y <-> ( .0. .< X /\ A. n e. NN ( n .x. X ) .< Y ) ) ) $=
      ( vx vy wcel cfv wbr wa cn vw w3a cinftm cv wral copab wceq elex 3ad2ant1
      co cvv cbs c0g cplt cmg fveq2 syl6eqr eleq2d anbi12d eqidd breq123d oveqd
      ralbidv opabbidv df-inftm cxp fvex eqeltri opabssxp ssexi fvmpt syl breqd
      xpex wb eleq1 bi2anan9 simpl breq2 oveq2d simpr breq12d eqid brabga bitrd
      3adant1 3simpc biantrurd bitr4d ) FEPZGAPZHAPZUBZGHFUCQZRZWKWLSZIGBRZDUDZ
      GCUJZHBRZDTUEZSZSZXBWMWOGHNUDZAPZOUDZAPZSZIXDBRZWRXDCUJZXFBRZDTUEZSZSZNOU
      FZRZXCWMWNXOGHWMFUKPZWNXOUGWJWKXQWLFEUHUIUAFXDUAUDZULQZPZXFXSPZSZXRUMQZXD
      XRUNQZRZWRXDXRUOQZUJZXFYDRZDTUEZSZSZNOUFXOUKUCXRFUGZYKXNNOYLYBXHYJXMYLXTX
      EYAXGYLXSAXDYLXSFULQZAXRFULUPJUQZURYLXSAXFYNURUSYLYEXIYIXLYLYCIXDXDYDBYLY
      CFUMQIXRFUMUPKUQYLYDFUNQBXRFUNUPMUQZYLXDUTVAYLYHXKDTYLYGXJXFXFYDBYLYFCWRX
      DYLYFFUOQCXRFUOUPLUQVBYOYLXFUTVAVCUSUSVDNOUADVEXOAAVFAAAYMUKJFULVGVHZYPVN
      XMNOAAVIVJVKVLVMWKWLXPXCVOWJXNXCNOGHXOAAXDGUGZXFHUGZSZXHWPXMXBYQXEWKYRXGW
      LXDGAVPXFHAVPVQYSXIWQXLXAYSYQXIWQVOYQYRVRZXDGIBVSVLYSXKWTDTYSXJWSXFHBYSXD
      GWRCYTVTYQYRWAWBVCUSUSXOWCWDWFWEWMWPXBWJWKWLWGWHWI $.
  $}

  ${
    $d x y B $.  $d x y w W $.
    isarchi.b $e |- B = ( Base ` W ) $.
    isarchi.0 $e |- .0. = ( 0g ` W ) $.
    isarchi.i $e |- .< = ( <<< ` W ) $.
    $( Express the predicate " ` W ` is Archimedean ".  (Contributed by Thierry
       Arnoux, 30-Jan-2018.) $)
    isarchi $p |- ( W e. V -> ( W e. Archi <-> A. x e. B A. y e. B -. x .< y )
      ) $=
      ( vw wcel carchi cinftm cfv c0 wceq cv wral wb wbr wn elex fveq2 df-archi
      cvv eqeq1d elrab2 baib syl cxp wss inftmrel cop ss0b ssrel2 syl5bbr breqi
      wi noel df-br bitri xchnxbir pm2.21i dfbi2 mpbiran2 2ralbii syl6bbr bitrd
      nbn ) FELZFMLZFNOZPQZARZBRZDUAZUBZBCSACSZVKFUFLZVLVNTFEUCVLVTVNKRZNOZPQVN
      KFUFMWAFQWBVMPWAFNUDUGKUEUHUIUJVKVMCCUKULZVNVSTCEFHUMWCVNVOVPUNZVMLZWDPLZ
      USZBCSACSZVSVNVMPULWCWHVMUOABCCVMPUPUQVRWGABCCVRWEWFTZWGWEWIVQWFWEWDUTZVJ
      VQVOVPVMUAWEVOVPDVMJURVOVPVMVAVBVCWIWGWFWEUSWFWEWJVDWEWFVEVFVBVGVHUJVI $.
  $}

  ${
    $d n A $.
    $( Plus infinity is an infinite for the completed real line, as any real
       number is infinitesimal compared to it.  (Contributed by Thierry Arnoux,
       1-Feb-2018.) $)
    pnfinf $p |- ( A e. RR+ -> A ( <<< ` RR*s ) +oo ) $=
      ( vn crp wcel cpnf cfv wbr cc0 clt co cn wa cr cxr adantr syl2anc eqeltrd
      cxrs syl cvv cinftm cv cmg wral rpgt0 cxmu wceq nnz adantl rpxr xrsmulgzz
      cz zred rpre cmul rexmul remulcl ltpnf ralrimiva jca wb xrsex xrsbas xrs0
      pnfxr eqid xrslt isinftm mp3an13 mpbird ) ACDZAERUAFGZHAIGZBUBZARUCFZJZEI
      GZBKUDZLZVKVMVRAUEVKVQBKVKVNKDZLZVPMDVQWAVPVNAUFJZMWAVNULDZANDZVPWBUGVTWC
      VKVNUHUIZVKWDVTAUJZOVNAUKPWAVNMDZAMDZWBMDWAVNWEUMVKWHVTAUNOWGWHLWBVNAUOJM
      VNAUPVNAUQQPQVPURSUSUTVKWDVLVSVAZWFRTDWDENDWIVBVENIVOBTRAEHVCVDVOVFVGVHVI
      SVJ $.
  $}

  ${
    $d x y $.
    $( The completed real line is not Archimedean.  (Contributed by Thierry
       Arnoux, 1-Feb-2018.) $)
    xrnarchi $p |- -. RR*s e. Archi $=
      ( vx vy cv cxrs cinftm cfv wbr cxr wrex carchi wcel wn c1 1re rexri pnfxr
      cpnf ax-mp wral cvv crp 1rp pnfinf breq1 breq2 mp3an rexnal dfrex2 rexbii
      rspc2ev wb xrsex cc0 xrsbas xrs0 eqid isarchi notbii 3bitr4i mpbi ) ACZBC
      ZDEFZGZBHIZAHIZDJKZLZMHKQHKMQVCGZVFMNOPMUAKVIUBMUCRVDVIMVBVCGABMQHHVAMVBV
      CUDVBQMVCUEUJUFVDLBHSZLZAHIVJAHSZLVFVHVJAHUGVEVKAHVDBHUHUIVGVLDTKVGVLUKUL
      ABHVCTDUMUNUOVCUPUQRURUSUT $.
  $}

  ${
    $d n x y B $.  $d n x y W $.
    isarchi2.b $e |- B = ( Base ` W ) $.
    isarchi2.0 $e |- .0. = ( 0g ` W ) $.
    isarchi2.x $e |- .x. = ( .g ` W ) $.
    isarchi2.l $e |- .<_ = ( le ` W ) $.
    isarchi2.t $e |- .< = ( lt ` W ) $.
    $( Alternative way to express the predicate " ` W ` is Archimedean ", for
       Tosets. (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
    isarchi2 $p |- ( ( W e. Toset /\ W e. Grp ) -> ( W e. Archi <->
      A. x e. B A. y e. B ( .0. .< x -> E. n e. NN y .<_ ( n .x. x ) ) ) ) $=
      ( wcel wbr wn wral cn wb ctos cgrp wa carchi cv cinftm co wrex wi isarchi
      cfv eqid adantr w3a simpl1l cz simpl1r simpr simpl2 mulgcl syl3anc simpl3
      tltnle con2bid rexbidva imbi2d isinftm notbid rexnal imbi2i bitr2i syl6bb
      nnzd imnan 3adant1r bitr4d 3expb 2ralbidva ) HUAOZHUBOZUCZHUDOZAUEZBUEZHU
      FUKZPZQZBCRACRZIWCDPZWDFUEZWCEUGZGPZFSUHZUIZBCRACRVSWBWHTVTABCWEUAHIJKWEU
      LUJUMWAWNWGABCCWAWCCOZWDCOZWNWGTWAWOWPUNZWNWIWKWDDPZQZFSUHZUIZWGWQWMWTWIW
      QWLWSFSWQWJSOZUCZVSWKCOZWPWLWSTVSVTWOWPXBUOXCVTWJUPOWOXDVSVTWOWPXBUQXCWJW
      QXBURVMWAWOWPXBUSCEHWJWCJLUTVAWAWOWPXBVBVSXDWPUNWRWLCDHGWKWDJMNVCVDVAVEVF
      VSWOWPWGXATVTVSWOWPUNZWGWIWRFSRZUCZQZXAXEWFXGCDEFUAHWCWDIJKLNVGVHXAWIXFQZ
      UIXHWTXIWIWRFSVIVJWIXFVNVKVLVOVPVQVRVP $.
  $}

  ${
    $d m n x y $.  $d n x y B $.  $d n x y W $.  $d m n .< $.  $d m n .x. $.
    $d n .0. $.
    isarchi3.b $e |- B = ( Base ` W ) $.
    isarchi3.0 $e |- .0. = ( 0g ` W ) $.
    isarchi3.i $e |- .< = ( lt ` W ) $.
    isarchi3.x $e |- .x. = ( .g ` W ) $.
    $( This is the usual definition of the Archimedean property for an ordered
       group. (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
    isarchi3 $p |- ( W e. oGrp -> ( W e. Archi <->
      A. x e. B A. y e. B ( .0. .< x -> E. n e. NN y .< ( n .x. x ) ) ) ) $=
      ( wcel wbr co cn syl wa c1 wceq vm cogrp carchi cv cple wrex wi wral ctos
      cfv cgrp comnd isogrp simprbi omndtos simplbi eqid isarchi2 syl2anc nfre1
      nfv nfan caddc simpr adantr peano2nnd cplusg simp-4l grpidcl 3syl simp-4r
      wb cz ad4antr nnzd mulgcl syl3anc simpllr ogrpaddlt syl131anc grplid nncn
      ax-1cn addcom mpan2 oveq1d cmnd grpmnd 1nn a1i mulgnndir syl13anc 3eqtrrd
      cc mulg1 3brtr3d tospos peano2zd plelttr impl mpdan oveq1 breq2d adantllr
      cpo r19.29af cbvrexv sylib pltle reximdva impbida pm5.74da ralbidva bitrd
      rspcev imp ) GUBMZGUCMZHAUDZDNZBUDZFUDZXSEOZGUEUJZNZFPUFZUGZBCUHZACUHZXTY
      AYCDNZFPUFZUGZBCUHZACUHXQGUIMZGUKMZXRYIVLXQGULMZYNXQYOYPGUMZUNGUOQZXQYOYP
      YQUPZABCDEFYDGHIJLYDUQZKURUSXQYHYMACXQXSCMZRZYGYLBCUUBYACMZRZXTYFYKUUDXTR
      ZYFYKUUEYFRZYAUAUDZXSEOZDNZUAPUFZYKUUFYEUUJFPUUEYFFUUEFVAYEFPUTVBUUEYBPMZ
      YEUUJYFUUEUUKRZYERZYBSVCOZPMYAUUNXSEOZDNZUUJUUMYBUULUUKYEUUEUUKVDZVEZVFUU
      MYCUUODNZUUPUUMHYCGVGUJZOZXSYCUUTOZYCUUODUUMXQHCMZUUAYCCMZXTUVAUVBDNUULXQ
      YEXQUUAUUCXTUUKVHZVEZUUMXQYOUVCUVFYSCGHIJVIVJUULUUAYEXQUUAUUCXTUUKVKZVEZU
      ULUVDYEUULYOYBVMMUUAUVDXQYOUUAUUCXTUUKYSVNZUULYBUUQVOZUVGCEGYBXSILVPVQZVE
      ZUUDXTUUKYEVRCUUTDGHXSYCIKUUTUQZVSVTUUMYOUVDUVAYCTUUMXQYOUVFYSQUVLCUUTGYC
      HIUVMJWAUSUUMUUOSYBVCOZXSEOZSXSEOZYCUUTOZUVBUUMUUKUUOUVOTUURUUKUUNUVNXSEU
      UKYBWNMZUUNUVNTZYBWBUVRSWNMUVSWCYBSWDWEQWFQUUMGWGMZSPMZUUKUUAUVOUVQTUUMXQ
      YOUVTUVFYSGWHVJUWAUUMWIWJUURUVHCUUTEGSYBXSILUVMWKWLUUMUVPXSYCUUTUUMUUAUVP
      XSTUVHCEGXSILWOQWFWMWPUULYEUUSUUPUULGXEMZUUCUVDUUOCMZYEUUSRUUPUGUULXQYNUW
      BUVEYRGWQVJUUBUUCXTUUKVRZUVKUULYOUUNVMMUUAUWCUVIUULYBUVJWRUVGCEGUUNXSILVP
      VQCDGYDYAYCUUOIYTKWSWLWTXAUUIUUPUAUUNPUUGUUNTUUHUUOYADUUGUUNXSEXBXCXOUSXD
      UUEYFVDXFUUIYJUAFPUUGYBTUUHYCYADUUGYBXSEXBXCXGXHUUEYKYFUUEYJYEFPUULXQUUCU
      VDYJYEUGUVEUWDUVKUBCCDGYDYAYCYTKXIVQXJXPXKXLXMXMXN $.
  $}

  ${
    $d m x y B $.  $d m x y W $.  $d m n x y X $.  $d m n y Y $.  $d m n ph $. 
    $d m n x y .0. $.  $d m n x y .<_ $.  $d m n x y .< $.  $d m n x y .x. $. 
    archirng.b $e |- B = ( Base ` W ) $.
    archirng.0 $e |- .0. = ( 0g ` W ) $.
    archirng.i $e |- .< = ( lt ` W ) $.
    archirng.l $e |- .<_ = ( le ` W ) $.
    archirng.x $e |- .x. = ( .g ` W ) $.
    archirng.1 $e |- ( ph -> W e. oGrp ) $.
    archirng.2 $e |- ( ph -> W e. Archi ) $.
    archirng.3 $e |- ( ph -> X e. B ) $.
    archirng.4 $e |- ( ph -> Y e. B ) $.
    archirng.5 $e |- ( ph -> .0. .< X ) $.
    ${
      archirng.6 $e |- ( ph -> .0. .< Y ) $.
      $( Property of Archimedean ordered groups, framing positive ` Y ` between
         multiples of ` X ` .  (Contributed by Thierry Arnoux, 12-Apr-2018.) $)
      archirng $p |- ( ph -> E. n e. NN0 ( ( n .x. X ) .< Y 
        /\ Y .<_ ( ( n + 1 ) .x. X ) ) ) $=
        ( vm vx vy cv co wbr c1 caddc wa cn0 wrex wn cc0 wceq oveq1 breq2d ctos
        wcel wb cogrp comnd cgrp isogrp simprbi omndtos 3syl simplbi syl tltnle
        grpidcl syl3anc mpbid mulg0 mtbird cn wral jca carchi isarchi2 syl21anc
        wi biimpa breq2 oveq2 rexbidv imbi12d breq1 imbi2d rspc2v nn0min adantr
        imp cz simpr nn0zd mulgcl anbi1d rexbidva mpbird ) AEUEZHDUFZICUGZIXAUH
        UIUFZHDUFZFUGZUJZEUKULIXBFUGZUMZXFUJZEUKULAIUBUEZHDUFZFUGZIUNHDUFZFUGZX
        HXFEUBXKUNUOXLXNIFXKUNHDUPUQXKXAUOXLXBIFXKXAHDUPUQXKXDUOXLXEIFXKXDHDUPU
        QAXOIJFUGZAJICUGZXPUMZUAAGURUSZJBUSZIBUSZXQXRUTAGVAUSZGVBUSZXSPYBGVCUSZ
        YCGVDZVEGVFVGZAYDXTAYBYDPYBYDYCYEVHVIZBGJKLVKVISBCGFJIKNMVJVLVMAXNJIFAH
        BUSZXNJUORBDGHJKLOVNVIUQVOAYHYAUJZJUCUEZCUGZUDUEZXKYJDUFZFUGZUBVPULZWBZ
        UDBVQUCBVQZJHCUGZXMUBVPULZAYHYARSVRAXSYDGVSUSZYQYFYGQXSYDUJYTYQUCUDBCDU
        BFGJKLONMVTWCWATYIYQUJYRYSYIYQYRYSWBZYPUUAYRYLXLFUGZUBVPULZWBUCUDHIBBYJ
        HUOZYKYRYOUUCYJHJCWDUUDYNUUBUBVPUUDYMXLYLFYJHXKDWEUQWFWGYLIUOZUUCYSYRUU
        EUUBXMUBVPYLIXLFWHWFWIWJWMWMWAWKAXGXJEUKAXAUKUSZUJZXCXIXFUUGXSXBBUSZYAX
        CXIUTAXSUUFYFWLUUGYDXAWNUSYHUUHAYDUUFYGWLUUGXAAUUFWOWPAYHUUFRWLBDGXAHKO
        WQVLAYAUUFSWLBCGFXBIKNMVJVLWRWSWT $.
    $}
    
    archirngz.1 $e |- ( ph -> ( oppG ` W ) e. oGrp ) $.
    $( Property of Archimedean left and right ordered groups.  (Contributed by
       Thierry Arnoux, 6-May-2018.) $)
    archirngz $p |- ( ph -> E. n e. ZZ ( ( n .x. X ) .< Y 
      /\ Y .<_ ( ( n + 1 ) .x. X ) ) ) $=
      ( vm wceq cv co wbr c1 caddc wa wrex cneg wcel 1nn0 nn0negzi cminusg cgrp
      cz cfv cogrp comnd isogrp simplbi syl 1z a1i mulgneg syl3anc mulg1 fveq2d
      eqid eqtrd ogrpinv0lt biimpa syl21anc eqbrtrd adantr breqtrrd cpo simprbi
      simpr ctos omndtos tospos grpidcl posref syl2anc cc0 ax-1cn subidi negeqi
      3syl cmin negsubdii neg0 3eqtr3i oveq1i mulg0 syl5eq 3brtr4d oveq1 breq1d
      jca oveq1d breq2d anbi12d rspcev sylancr cn0 c2 nn0ssz sseldi ad2antrr 2z
      znegcld zsubcld cc nn0cn zcnd negdi2d coppg mulgcl zaddcld addassd oveq2i
      peano2zd 3eqtrrd 3brtr3d w3a ogrpinvlt syl31anc eqbrtrrd ad4antr syl12anc
      addcld eqcomd wb negcld cvv biimpar archirng cplusg grplid syl6eq addcomd
      ogrpaddlt syl131anc mulgdir syl13anc grpinvcl posasymb syl32anc grpinvinv
      1p1e2 eqtr3d simplrr 3eqtr2rd addsubassd 2m1e1 syl6req negsubdid 3anassrs
      negeqd simp-4l adantrr negdi sylancl addid1d 3eqtrd wi ovex pltle wo tlt2
      imp mpjaodan carchi syldan r19.29a wss ssrexv mpsyl w3o tlt3 mpjao3dan )
      AIJUCZEUDZHDUEZICUFZIUWFUGUHUEZHDUEZFUFZUIZEUQUJZIJCUFZJICUFZAUWEUIZUGUKZ
      UQULUWQHDUEZICUFZIUWQUGUHUEZHDUEZFUFZUIZUWMUGUMUNUWPUWSUXBUWPUWRJICAUWRJC
      UFUWEAUWRHGUOURZURZJCAUWRUGHDUEZUXDURZUXEAGUPULZUGUQULZHBULZUWRUXGUCAGUSU
      LZUXHPUXKUXHGUTULZGVAZVBZVCZUXIAVDVERBDGUXDUGHKOUXDVJZVFVGAUXFHUXDAUXJUXF
      HUCZRBDGHKOVHZVCVIVKAUXKUXJJHCUFZUXEJCUFZPRTUXKUXJUIUXSUXTBCGUXDHJKMUXPLV
      LVMVNVOVPAUWEVTZVQUWPJJIUXAFAJJFUFZUWEAGVRULZJBULZUYBAGWAULZUYCAUXKUXLUYE
      PUXKUXHUXLUXMVSGWBWKZGWCZVCZAUXKUXHUYDPUXNBGJKLWDZWKZBGFJKNWEWFVPUYAAUXAJ
      UCUWEAUXAWGHDUEZJUWTWGHDUGUGWLUEZUKWGUKUWTWGUYLWGUGWHWIWJUGUGWHWHWMWNWOZW
      PAUXJUYKJUCRBDGHJKLOWQVCWRVPWSXBUWLUXCEUWQUQUWFUWQUCZUWHUWSUWKUXBUYNUWGUW
      RICUWFUWQHDWTXAUYNUWJUXAIFUYNUWIUWTHDUWFUWQUGUHWTXCXDXEXFXGAUWNUIZUBUDZHD
      UEZIUXDURZCUFZUYRUYPUGUHUEZHDUEZFUFZUIZUWMUBXHUYOUYPXHULZUIZVUCUIZVUAUYRF
      UFZUWMUYRVUACUFZVUFVUGUIZUYPUKZXIWLUEZUQULVUKHDUEZICUFZIVUKUGUHUEZHDUEZFU
      FZUWMVUIVUJXIVUIUYPVUEUYPUQULZVUCVUGVUEXHUQUYPXJUYOVUDVTZXKZXLXNXIUQULZVU
      IXMVEXOVUIVULUYTUKZHDUEZICVUEVULVVBCUFVUCVUGVUEUYPXIUHUEZUKZHDUEZVULVVBCV
      UEVVDVUKHDVUEUYPXIVUEVUDUYPXPULZVURUYPXQZVCZVUEXIVUTVUEXMVEZXRZXSZXCVUEVV
      CHDUEZUXDURZVUAUXDURZVVEVVBCVUEUXKGXTURUSULZUIZVUABULZVVLBULZVUAVVLCUFZVV
      MVVNCUFZVUEUXKVVOUYOUXKVUDAUXKUWNPVPZVPZUYOVVOVUDAVVOUWNUAVPZVPXBZVUEUXHU
      YTUQULZUXJVVQAUXHUWNVUDUXOXLZVUEUYPVUSYEZUYOUXJVUDAUXJUWNRVPZVPZBDGUYTHKO
      YAVGZVUEUXHVVCUQULZUXJVVRVWFVUEUYPXIVUSVVIYBZVWIBDGVVCHKOYAVGVUEJVUAGUUAU
      RZUEZHVUAVWMUEZVUAVVLCVUEUXKUYDUXJVVQUXSVWNVWOCUFVWBVUEUXHUYDVWFUYIVCVWIV
      WJUYOUXSVUDAUXSUWNTVPZVPBVWMCGJHVUAKMVWMVJZUUEUUFVUEUXHVVQVWNVUAUCVWFVWJB
      VWMGVUAJKVWQLUUBWFVUEVVLUGUYTUHUEZHDUEZUXFVUAVWMUEZVWOVUEVUDVVLVWSUCVURVU
      DVVCVWRHDVUDUYTUGUHUEZVVCVWRVUDVXAUYPUGUGUHUEZUHUEVVCVUDUYPUGUGVVGUGXPULZ
      VUDWHVEZVXDYCVXBXIUYPUHUUMYDUUCVUDUYTUGVUDUYPUGVVGVXDYNVXDUUDUUNXCVCVUEUX
      HUXIVWEUXJVWSVWTUCVWFUXIVUEVDVEVWGVWIBVWMDGUGUYTHKOVWQUUGUUHVUEUXFHVUAVWM
      VUEUXJUXQVWIUXRVCXCYFYGVVPVVQVVRYHVVSVVTBCGUXDVUAVVLKMUXPYIVMYJVUEUXHVWKU
      XJVVEVVMUCVWFVWLVWIBDGUXDVVCHKOUXPVFVGVUEUXHVWEUXJVVBVVNUCZVWFVWGVWIBDGUX
      DUYTHKOUXPVFVGZWSYKXLVUIVVBVVNUYRUXDURZIVUEVXEVUCVUGVXFXLVUIUYRVUAUXDVUIU
      YCUYRBULZVVQVUBVUGUYRVUAUCZAUYCUWNVUDVUCVUGUYHYLVUEVXHVUCVUGUYOVXHVUDAVXH
      UWNAUXHIBULZVXHUXOSBGUXDIKUXPUUIWFZVPZVPZXLVUEVVQVUCVUGVWJXLVUEUYSVUBVUGU
      UOVUFVUGVTUYCVXHVVQYHVUBVUGUIVXIBGFUYRVUAKNUUJVMUUKVIAVXGIUCZUWNVUDVUCVUG
      AUXHVXJVXNUXOSBGUXDIKUXPUULWFZYLUUPZVQVUIIVVBVUOFVXPVUEVVBVUOFUFVUCVUGVUE
      VUOVVBVUOFVUEVUNVVAHDVUEVVAVVCUGWLUEZUKVVDUGUHUEVUNVUEUYTVXQVUEVXQUYPXIUG
      WLUEZUHUEUYTVUEUYPXIUGVVHVVJVXCVUEWHVEZUUQVXRUGUYPUHUURYDUUSUVBVUEVVCUGVU
      EUYPXIVVHVVJYNVXSUUTVUEVVDVUKUGUHVVKXCYFXCVUEUYCVUOBULZVUOVUOFUFVUEUYEUYC
      AUYEUWNVUDUYFXLZUYGVCVUEUXHVUNUQULUXJVXTVWFVUEVUKVUEVUJXIVUEUYPVUSXNVVIXO
      YEVWIBDGVUNHKOYAVGBGFVUOKNWEWFYKXLVOUWLVUMVUPUIEVUKUQUWFVUKUCZUWHVUMUWKVU
      PVYBUWGVULICUWFVUKHDWTXAVYBUWJVUOIFVYBUWIVUNHDUWFVUKUGUHWTXCXDXEXFYMVUFVU
      HUIZVVAUQULVVBICUFZIVVAUGUHUEZHDUEZFUFZUWMVYCUYTVUEVWEVUCVUHVWGXLXNVYCVVN
      VXGVVBICVYCVVPVXHVVQVUHVVNVXGCUFZUYOVUDVUCVUHVVPUYOVUDVUCVUHYHZUIUXKVVOUY
      OUXKVYIVWAVPUYOVVOVYIVWCVPXBUVAVUEVXHVUCVUHVXMXLVUEVVQVUCVUHVWJXLVUFVUHVT
      VVPVXHVVQYHVUHVYHBCGUXDUYRVUAKMUXPYIVMYJVYCVVBVVNVUEVXEVUCVUHVXFXLYOAVXNU
      WNVUDVUCVUHVXOYLZYGVYCAIVYFCUFZVYGAUWNVUDVUCVUHUVCVYCVXGUYQUXDURZIVYFCVUF
      VXGVYLCUFZVUHVUEUYSVYMVUBVUEUYSVYMVUEVVPUYQBULZVXHUYSVYMYPVWDVUEUXHVUQUXJ
      VYNVWFVUSVWIBDGUYPHKOYAVGVXMBCGUXDUYQUYRKMUXPYIVGVMUVDVPVYJVYCVYFVYLVUEVY
      FVYLUCVUCVUHVUEVYFVUJHDUEZVYLVUEVUDVYFVYOUCVURVUDVYEVUJHDVUDVYEVUJUWQUHUE
      ZUGUHUEZVUJVUDVVAVYPUGUHVUDVVFVXCVVAVYPUCVVGWHUYPUGUVEUVFXCVUDVYQVUJUWTUH
      UEZVUJWGUHUEZVUJVUDVUJUWQUGVUDUYPVVGYQZVUDUGVXDYQVXDYCVYRVYSUCVUDUWTWGVUJ
      UHUYMYDVEVUDVUJVYTUVGUVHVKXCVCVUEUXHVUQUXJVYOVYLUCVWFVUSVWIBDGUXDUYPHKOUX
      PVFVGVKXLYOYGAVYKVYGAUXKVXJVYFYRULZVYKVYGUVIPSWUAAVYEHDUVJVEUSBYRCGFIVYFN
      MUVKVGUVNWFUWLVYDVYGUIEVVAUQUWFVVAUCZUWHVYDUWKVYGWUBUWGVVBICUWFVVAHDWTXAW
      UBUWJVYFIFWUBUWIVYEHDUWFVVAUGUHWTXCXDXEXFYMVUEVUGVUHUVLZVUCVUEUYEVVQVXHWU
      CVYAVWJVXMBCGFVUAUYRKNMUVMVGVPUVOUYOBCDUBFGHUYRJKLMNOVWAAGUVPULZUWNQVPVWH
      VXLVWPAUWNVXGJCUFZJUYRCUFZAWUEUWNAVXGIJCVXOXAYSAWUFWUEAUXKVXHWUFWUEYPPVXK
      BCGUXDUYRJKMUXPLVLWFYSUVQYTUVRXHUQUVSAUWOUIZUWLEXHUJUWMXJWUGBCDEFGHIJKLMN
      OAUXKUWOPVPAWUDUWOQVPAUXJUWORVPAVXJUWOSVPAUXSUWOTVPAUWOVTYTUWLEXHUQUVTUWA
      AUYEVXJUYDUWEUWNUWOUWBUYFSUYJBCGIJKMUWCVGUWD $.
  $}

  ${
    $d n x y B $.  $d n x y W $.  $d n x y X $.  $d n y Y $.  $d n x y .0. $. 
    $d n x y .< $.  $d n x y .x. $. 
    archiexdiv.b $e |- B = ( Base ` W ) $.
    archiexdiv.0 $e |- .0. = ( 0g ` W ) $.
    archiexdiv.i $e |- .< = ( lt ` W ) $.
    archiexdiv.x $e |- .x. = ( .g ` W ) $.
    $( In an Archimedean group, given two positive elements, there exists a
       "divisor" ` n ` . (Contributed by Thierry Arnoux, 30-Jan-2018.) $)
    archiexdiv $p |- ( ( ( W e. oGrp /\ W e. Archi ) /\ ( X e. B /\ Y e. B )
      /\ .0. .< X ) -> E. n e. NN Y .< ( n .x. X ) ) $=
      ( vx vy wcel wbr cv cn wrex wi cogrp carchi wa w3a co simp3 wral isarchi3
      biimpa 3ad2ant1 breq2 oveq2 breq2d rexbidv imbi12d imbi2d rspc2v 3ad2ant2
      wceq breq1 mpd ) EUAOZEUBOZUCZFAOGAOUCZHFBPZUDZVFGDQZFCUEZBPZDRSZVDVEVFUF
      VGHMQZBPZNQZVHVLCUEZBPZDRSZTZNAUGMAUGZVFVKTZVDVEVSVFVBVCVSMNABCDEHIJKLUHU
      IUJVEVDVSVTTVFVRVTVFVNVIBPZDRSZTMNFGAAVLFUSZVMVFVQWBVLFHBUKWCVPWADRWCVOVI
      VNBVLFVHCULUMUNUOVNGUSZWBVKVFWDWAVJDRVNGVIBUTUNUPUQURVAVA $.
  $}

  ${
    $d a b m n x y z $.  $d m n x y z B $.  $d m n x U $.  $d m n x y z W $.
    $d m n x X $.  $d m n x y z ph $.  $d m n x .x. $.  $d m n x .0. $.
    $d m n x .< $.  $d m x .<_ $.
    archiabllem.b $e |- B = ( Base ` W ) $.
    archiabllem.0 $e |- .0. = ( 0g ` W ) $.
    archiabllem.e $e |- .<_ = ( le ` W ) $.
    archiabllem.t $e |- .< = ( lt ` W ) $.
    archiabllem.m $e |- .x. = ( .g ` W ) $.
    archiabllem.g $e |- ( ph -> W e. oGrp ) $.
    archiabllem.a $e |- ( ph -> W e. Archi ) $.
    ${
      archiabllem1.u $e |- ( ph -> U e. B ) $.
      archiabllem1.p $e |- ( ph -> .0. .< U ) $.
      archiabllem1.s $e |- ( ( ph /\ x e. B /\ .0. .< x ) -> U .<_ x ) $.
      ${
        archiabllem1a.x $e |- ( ph -> X e. B ) $.
        archiabllem1a.c $e |- ( ph -> .0. .< X ) $.
        $( Lemma for ~ archiabl : In case an archimedean group ` W ` admits a
           smallest positive element ` U ` , then any positive element ` X ` of
           ` W ` can be written as ` ( n .x. U ) ` with ` n e. NN ` . Since the
           reciprocal holds for negative elements, ` W ` is then isomorphic to
           ` ZZ ` .  (Contributed by Thierry Arnoux, 12-Apr-2018.) $)
        archiabllem1a $p |- ( ph -> E. n e. NN X = ( n .x. U ) ) $=
          ( vm cv co wbr c1 caddc wa wceq cn wrex cn0 simplr cc elnn0nn simprbi
          wcel syl csg cfv cplusg ad2antrr mulg1 oveq1d cgrp cogrp comnd isogrp
          cz simplbi 1z a1i nn0zd eqid mulgdir syl13anc cpo ctos omndtos tospos
          3syl mulgcl syl3anc grpsubcl peano2zd simprr ogrpsub syl131anc nn0cnd
          cmin ax-1cn pncan2d mulgsubdir 3eqtr3d breqtrd wi wral 3expa grpsubid
          ralrimiva syl2anc simprl ogrpsublt eqbrtrrd breq2 imbi12d rspcv syl3c
          ex w3a posasymb biimpa syl32anc 3eqtr4rd grpnpcan addcom oveq1 eqeq2d
          rspcev archirng r19.29a ) AUDUEZFEUFZJDUGZJYDUHUIUFZFEUFZHUGZUJZJGUEZ
          FEUFZUKZGULUMZUDUNAYDUNUSZUJZYJUJZYGULUSZJYHUKZYNYQYOYRAYOYJUOZYOYDUP
          USZYRYDUQURUTYQJYEIVAVBZUFZYEIVCVBZUFZUHYDUIUFZFEUFZJYHYQUHFEUFZYEUUD
          UFZFYEUUDUFUUGUUEYQUUHFYEUUDYQFCUSZUUHFUKAUUJYOYJSVDZCEIFLPVEUTZVFYQI
          VGUSZUHVKUSZYDVKUSZUUJUUGUUIUKYQIVHUSZUUMAUUPYOYJQVDZUUPUUMIVIUSZIVJZ
          VLUTZUUNYQVMVNYQYDYTVOZUUKCUUDEIUHYDFLPUUDVPZVQVRYQUUCFYEUUDYQIVSUSZU
          UCCUSZUUJUUCFHUGZFUUCHUGZUUCFUKZYQUUPUVCUUQUUPUURIVTUSUVCUUPUUMUURUUS
          URIWAIWBWCUTYQUUMJCUSZYECUSZUVDUUTAUVHYOYJUBVDZYQUUMUUOUUJUVIUUTUVAUU
          KCEIYDFLPWDWEZCIUUBJYELUUBVPZWFWEZUUKYQUUCYHYEUUBUFZFHYQUUPUVHYHCUSZU
          VIYIUUCUVNHUGUUQUVJYQUUMYGVKUSZUUJUVOUUTYQYDUVAWGZUUKCEIYGFLPWDWEUVKY
          PYFYIWHCIHUUBJYHYELNUVLWIWJYQYGYDWLUFZFEUFZUUHUVNFYQUVRUHFEYQYDUHYQYD
          YTWKZUHUPUSZYQWMVNZWNVFYQUUMUVPUUOUUJUVSUVNUKUUTUVQUVAUUKCEIYGUUBYDFL
          PUVLWOVRUULWPWQYQUVDKBUEZDUGZFUWCHUGZWRZBCWSZKUUCDUGZUVFUVMAUWGYOYJAU
          WFBCAUWCCUSZUJUWDUWEAUWIUWDUWEUAWTXKXBVDYQYEYEUUBUFZKUUCDYQUUMUVIUWJK
          UKUUTUVKCIUUBYEKLMUVLXAXCYQUUPUVIUVHUVIYFUWJUUCDUGUUQUVKUVJUVKYPYFYIX
          DCDIUUBYEJYELOUVLXEWJXFUWFUWHUVFWRBUUCCUWCUUCUKUWDUWHUWEUVFUWCUUCKDXG
          UWCUUCFHXGXHXIXJUVCUVDUUJXLUVEUVFUJUVGCIHUUCFLNXMXNXOVFXPYQUUMUVHUVIU
          UEJUKUUTUVJUVKCUUDIUUBJYELUVBUVLXQWEYQUUFYGFEYQUWAUUAUUFYGUKUWBUVTUHY
          DXRXCVFWPYMYSGYGULYKYGUKYLYHJYKYGFEXSXTYAXCACDEUDHIFJKLMONPQRSUBTUCYB
          YC $.
      $}

      $( Lemma for ~ archiabl (Contributed by Thierry Arnoux, 13-Apr-2018.) $)
      archiabllem1b $p |- ( ( ph /\ y e. B ) -> E. n e. ZZ y = ( n .x. U ) ) $=
        ( vm cv wcel wa wceq co cz wrex wbr cc0 0z a1i simpr mulg0 syl ad2antrr
        eqtr4d oveq1 eqeq2d rspcev syl2anc w3a cminusg cfv cn cneg nnssz simplr
        sseldi znegcld 3ad2ant1 eqid mulgnegnn fveq2d cgrp cogrp isogrp simplbi
        comnd simp2 3eqtr2rd carchi simp1 syl3an1 grpinvcl cplusg grpidcl simp3
        grpinvinv ogrpaddlt syl131anc grprinv 3brtr3d archiabllem1a r19.29a wss
        grplid 3expa ssrexv mpsyl ctos simprbi omndtos 3syl adantr tlt3 syl3anc
        w3o mpjao3dan ) ACUCZDUDZUEZXKKUFZXKHUCZGFUGZUFZHUHUIZXKKEUJZKXKEUJZXMX
        NUEZUKUHUDZXKUKGFUGZUFZXRYBYAULUMYAXKKYCXMXNUNAYCKUFZXLXNAGDUDZYESDFJGK
        LMPUOUPUQURXQYDHUKUHXOUKUFXPYCXKXOUKGFUSUTVAVBAXLXSXRAXLXSVCZXKJVDVEZVE
        ZUBUCZGFUGZUFZXRUBVFYGYJVFUDZUEZYLUEZYJVGZUHUDXKYPGFUGZUFZXRYOYJYOVFUHY
        JVHYGYMYLVIZVJVKYOYQYKYHVEZYIYHVEZXKYOYMYFYQYTUFYSYGYFYMYLAXLYFXSSVLZUQ
        DFJYHYJGLPYHVMZVNVBYOYIYKYHYNYLUNVOYGUUAXKUFZYMYLYGJVPUDZXLUUDYGJVQUDZU
        UEAXLUUFXSQVLZUUFUUEJVTUDZJVRZVSZUPZAXLXSWAZDJYHXKLUUCWJVBUQWBXQYRHYPUH
        XOYPUFXPYQXKXOYPGFUSUTVAVBYGBDEFGUBIJYIKLMNOPUUGAXLJWCUDZXSRVLUUBAXLKGE
        UJZXSTVLYGABUCZDUDZKUUOEUJZGUUOIUJZAXLXSWDUAWEYGUUEXLYIDUDZUUKUULDJYHXK
        LUUCWFVBZYGXKYIJWGVEZUGZKYIUVAUGZKYIEYGUUFXLKDUDZUUSXSUVBUVCEUJUUGUULYG
        UUEUVDUUKDJKLMWHZUPUUTAXLXSWIDUVAEJXKKYILOUVAVMZWKWLYGUUEXLUVBKUFUUKUUL
        DUVAJYHXKKLUVFMUUCWMVBYGUUEUUSUVCYIUFUUKUUTDUVAJYIKLUVFMWRVBWNWOWPWSVFU
        HWQXMXTUEXQHVFUIZXRVHAXLXTUVGAXLXTVCZBDEFGHIJXKKLMNOPAXLUUFXTQVLAXLUUMX
        TRVLAXLYFXTSVLAXLUUNXTTVLUVHAUUPUUQUURAXLXTWDUAWEAXLXTWAAXLXTWIWOWSXQHV
        FUHWTXAXMJXBUDZXLUVDXNXSXTXIAUVIXLAUUFUUHUVIQUUFUUEUUHUUIXCJXDXEXFAXLUN
        AUVDXLAUUFUUEUVDQUUJUVEXEXFDEJXKKLOXGXHXJ $.
  
      $( Archimedean ordered groups with a minimal positive value are abelian.
         (Contributed by Thierry Arnoux, 13-Apr-2018.) $)
      archiabllem1 $p |- ( ph -> W e. Abel ) $=
        ( co vy vz vm vn cgrp wcel cv cplusg wceq wral cabel cogrp comnd isogrp
        cfv simplbi syl wa caddc simplr zcnd simpr addcomd oveq1d ad2antrr eqid
        cz mulgdir syl13anc 3eqtr3d adantlr adantr simpllr oveq12d 3eqtr4d wrex
        adantllr simplll simpr1r 3anassrs archiabllem1b syl2anc r19.29a adantrr
        ralrimivva isabl2 sylanbrc ) AHUEUFZUAUGZUBUGZHUHUOZTZWJWIWKTZUIZUBCUJU
        ACUJHUKUFAHULUFZWHOWOWHHUMUFHUNUPUQZAWNUAUBCCAWICUFZWJCUFZURZURZWIUCUGZ
        FETZUIZWNUCVGWTXAVGUFZURZXCURZWJUDUGZFETZUIZWNUDVGXFXGVGUFZURZXIURZXBXH
        WKTZXHXBWKTZWLWMXKXMXNUIZXIXEXJXOXCAXDXJXOWSAXDURZXJURZXAXGUSTZFETZXGXA
        USTZFETZXMXNXQXRXTFEXQXAXGXQXAAXDXJUTZVAXQXGXPXJVBZVAVCVDXQWHXDXJFCUFZX
        SXMUIAWHXDXJWPVEZYBYCAYDXDXJQVEZCWKEHXAXGFJNWKVFZVHVIXQWHXJXDYDYAXNUIYE
        YCYBYFCWKEHXGXAFJNYGVHVIVJVQVKVLXLWIXBWJXHWKXEXCXJXIVMZXKXIVBZVNXLWJXHW
        IXBWKYIYHVNVOXFAWRXIUDVGVPAWSXDXCVRAWSXDXCWRWQWRXDXCAVSVTABUBCDEFUDGHIJ
        KLMNOPQRSWAWBWCAWQXCUCVGVPWRABUACDEFUCGHIJKLMNOPQRSWAWDWCWEUAUBCWKHJYGW
        FWG $.
    $}

    ${
      $d m n t $. $d a b c t B $.  $d a b c t W $.  $d a b c t X $.  
      $d a b m n t Y $.  $d a b t ph $. $d a b c t m n .+ $.
      $d a b c t m n .<_ $.  $d a b c t m n .< $. $d a b c t .0. $.
      archiabllem2.1 $e |- .+ = ( +g ` W ) $. 
      archiabllem2.2 $e |- ( ph -> ( oppG ` W ) e. oGrp ) $. 
      archiabllem2.3 $e |- ( ( ph /\ a e. B /\ .0. .< a ) 
                                       -> E. b e. B ( .0. .< b /\ b .< a ) ) $. 
      ${
        archiabllem2a.4 $e |- ( ph -> X e. B ) $. 
        archiabllem2a.5 $e |- ( ph -> .0. .< X ) $. 
        $( Lemma for ~ archiabl , which requires the group to be both left- and
           right-ordered.  (Contributed by Thierry Arnoux, 13-Apr-2018.) $)
        archiabllem2a $p |- ( ph 
          -> E. c e. B ( .0. .< c /\ ( c .+ c ) .<_ X ) ) $=
          ( cv wbr wa wrex wcel simpllr simplrl simpr wceq breq2 oveq12d breq1d
          co id anbi12d rspcev syl12anc csg cfv cgrp cogrp simplll comnd isogrp
          simplbi 3syl eqid grpsubcl syl3anc grpsubid syl2anc simplrr ogrpsublt
          syl syl131anc eqbrtrrd coppg cplusg cplt grpaddsubass syl13anc oveq2d
          grpcl grprid 3eqtrd breqtrd oppglt breqd mpbid oppgbas mpbird 3brtr3g
          ogrpaddlt oppgplus grpnpcan cvv wi ovex a1i pltle mpd jca wo ad2antrr
          ctos simprbi omndtos simplr tlt2 wral 3expia ralrimiva anbi2d rexbidv
          mpjaodan imbi12d rspcv syl3c r19.29a ) AIKUEZDUFZYDHDUFZUGZILUEZDUFZY
          HYHCUQZHFUFZUGZLBUHZKBAYDBUIZUGZYGUGZYDYDCUQZHFUFZYMHYQDUFZYPYRUGYNYE
          YRYMAYNYGYRUJYOYEYFYRUKYPYRULYLYEYRUGLYDBYHYDUMZYIYEYKYRYHYDIDUNYTYJY
          QHFYTYHYDYHYDCYTURZUUAUOUPUSUTVAYPYSUGZHYDGVBVCZUQZBUIZIUUDDUFZUUDUUD
          CUQZHFUFZUGZYMUUBGVDUIZHBUIZYNUUEUUBAGVEUIZUUJAYNYGYSVFZRUULUUJGVGUIZ
          GVHZVIZVJZUUBAUUKUUMUCVRZAYNYGYSUJZBGUUCHYDMUUCVKZVLVMZUUBUUFUUHUUBYD
          YDUUCUQZIUUDDUUBUUJYNUVBIUMUUQUUSBGUUCYDIMNUUTVNVOZUUBUULYNUUKYNYFUVB
          UUDDUFUUBAUULUUMRVRZUUSUURUUSYOYEYFYSVPBDGUUCYDHYDMPUUTVQVSVTUUBUUGHD
          UFZUUHUUBUUGUUDYDCUQZHDUUBUUDUUDGWAVCZWBVCZUQZYDUUDUVHUQZUUGUVFDUUBUV
          IUVJDUFUVIUVJUVGWCVCZUFZUUBUVGVEUIZUUEYNUUEUUDYDUVKUFZUVLUUBAUVMUUMUA
          VRUVAUUSUVAUUBUUDYDDUFUVNUUBUUDYQYDUUCUQZYDDUUBUULUUKYQBUIZYNYSUUDUVO
          DUFUVDUURUUBUUJYNYNUVPUUQUUSUUSBCGYDYDMTWGZVMUUSYPYSULBDGUUCHYQYDMPUU
          TVQVSUUBUVOYDUVBCUQZYDICUQZYDUUBUUJYNYNYNUVOUVRUMUUQUUSUUSUUSBCGUUCYD
          YDYDMTUUTWDWEUUBUVBIYDCUVCWFUUBUUJYNUVSYDUMUUQUUSBCGYDIMTNWHVOWIWJUUB
          DUVKUUDYDUUBUUJDUVKUMUUQGDUVGVDUVGVKZPWKVRZWLWMBUVHUVKUVGUUDYDUUDBGUV
          GUVTMWNUVKVKUVHVKZWQVSUUBDUVKUVIUVJUWAWLWOCUVHGUVGUUDUUDTUVTUWBWRCUVH
          GUVGYDUUDTUVTUWBWRWPUUBUUJUUKYNUVFHUMUUQUURUUSBCGUUCHYDMTUUTWSVMWJUUB
          UUJUUGWTUIZUUKUVEUUHXAUUQUWCUUBUUDUUDCXBXCUURVDWTBDGFUUGHOPXDVMXEXFYL
          UUILUUDBYHUUDUMZYIUUFYKUUHYHUUDIDUNUWDYJUUGHFUWDYHUUDYHUUDCUWDURZUWEU
          OUPUSUTVOYPGXIUIZUVPUUKYRYSXGYPUULUUNUWFAUULYNYGRXHZUULUUJUUNUUOXJGXK
          VJYPUUJYNYNUVPYPUULUUJUWGUUPVRAYNYGXLZUWHUVQVMAUUKYNYGUCXHBDGFYQHMOPX
          MVMXSAUUKIJUEZDUFZYEYDUWIDUFZUGZKBUHZXAZJBXNIHDUFZYGKBUHZUCAUWNJBAUWI
          BUIUWJUWMUBXOXPUDUWNUWOUWPXAJHBUWIHUMZUWJUWOUWMUWPUWIHIDUNUWQUWLYGKBU
          WQUWKYFYEUWIHYDDUNXQXRXTYAYBYC $.
      $}

      ${
        archiabllem2b.4 $e |- ( ph -> X e. B ) $. 
        archiabllem2b.5 $e |- ( ph -> Y e. B ) $. 
        $( Lemma for ~ archiabl (Contributed by Thierry Arnoux, 1-May-2018.) $)
        archiabllem2c $p |- ( ph -> -. ( X .+ Y ) .< ( Y .+ X ) ) $=
          ( vt vn vm co wbr wa cv csg cfv wfal wcel simprr wn w3a c1 caddc cneg
          cz cminusg cogrp simpl1l syl simpl1r cgrp adantr comnd isogrp simplbi
          grpcl syl3anc syl2anc 3syl simpr2 1z a1i simp2 mulgcl simpr1 3ad2ant1
          zaddcld simprbi simpr3 simprd coppg omndadd2rd eqid ogrpsub syl131anc
          simpld c2 zcnd add4d wceq 1p1e2 oveq2i addcom oveq1d syl5eq 2cn simpr
          cc simpl addcld addcomd eqtr4d eqtr3d 2z mulgdir syl13anc eqtrd mulg2
          3eqtr3d breqtrd eqeltrrd grpsubval grpinvcl ogrpaddlt ogrpaddltrd cpo
          znegcld wi ctos omndtos tospos plttr mp2and eqbrtrd eqeltrd ogrpinvlt
          wb jca mpbid mulgneg cc0 wrex archirngz breqtrrd plelttr grpass negid
          grpsubcl oveq2d grprid 3anassrs carchi reeanv sylibr r19.29_2a tltnle
          mulg0 simp3 adantrr pm2.21dd 3adant1r grpsubid eqbrtrrd archiabllem2a
          3expa ogrpsublt r19.29a inegd ) AHICUHZIHCUHZDUIZAUVHUJZJUEUKZDUIZUVJ
          UVJCUHZUVGUVFGULUMZUHZFUIZUJZUNUEBUVIUVJBUOZUJZUVPUJUVOUNUVRUVKUVOUPU
          VRUVKUVOUQZUVOUVIUVQUVKUVSUVIUVQUVKURZUVNUVLDUIZUVSUVTUFUKZUVJEUHZHDU
          IZHUWBUSUTUHZUVJEUHZFUIZUJZUGUKZUVJEUHZIDUIZIUWIUSUTUHZUVJEUHZFUIZUJZ
          UJZUWAUFUGVBVBUVTUWBVBUOZUWIVBUOZUWPUWAUVTUWQUWRUWPURZUJZUVNUVLUWBUWI
          UTUHZUVJEUHZCUHZUXAVAZUVJEUHZCUHZUVLDUWTUVNUXCUVFGVCUMZUMZCUHZFUIZUXI
          UXFDUIZUVNUXFDUIZUWTUVNUXCUVFUVMUHZUXIFUWTUVNUWMUWFCUHZUVFUVMUHZUXMFU
          WTGVDUOZUVGBUOZUXNBUOZUVFBUOZUVGUXNFUIUVNUXOFUIUWTAUXPAUVHUVQUVKUWSVE
          ZRVFZUWTAUVHUXQUXTAUVHUVQUVKUWSVGUVIGVHUOZIBUOZHBUOZUXQUVIUXPUYBAUXPU
          VHRVIZUXPUYBGVJUOZGVKZVLZVFZAUYCUVHUDVIZAUYDUVHUCVIZBCGIHMTVMVNZVOZUW
          TUYBUWMBUOZUWFBUOZUXRUWTUXPUYBUYAUYHVFZUWTUYBUWLVBUOZUVQUYNUWTAUXPUYB
          UXTRUYHVPZUWTUWIUSUVTUWQUWRUWPVQZUSVBUOUWTVRVSZWDZUVTUVQUWSUVIUVQUVKV
          TZVIZBEGUWLUVJMQWAVNZUWTUYBUWEVBUOZUVQUYOUYRUWTUWBUSUVTUWQUWRUWPWBZUY
          TWDZVUCBEGUWEUVJMQWAVNZBCGUWMUWFMTVMVNZUWTUYBUYDUYCUXSUYPUVTUYDUWSUVI
          UVQUYDUVKUYKWCZVIZUVTUYCUWSUVIUVQUYCUVKUYJWCZVIZBCGHIMTVMZVNZUWTBCFGU
          WFIHUWMMOTUWTAUXPUYFUXTRUXPUYBUYFUYGWEZVPZVUHVUMVUKVUDUWTUWKUWNUWTUWH
          UWOUVTUWQUWRUWPWFZWGZWGUWTUWDUWGUWTUWHUWOVURWMZWGUWTAGWHUMZVDUOZVVAVJ
          UOZUXTUAVVBVVAVHUOVVCVVAVKWEVPWIBGFUVMUVGUXNUVFMOUVMWJZWKWLUWTUXNUXCU
          VFUVMUWTUWLUWEUTUHZUVJEUHZWNUVJEUHZUXBCUHZUXNUXCUWTVVFWNUXAUTUHZUVJEU
          HZVVHUWTVVEVVIUVJEUWTUWIUWBUTUHZUSUSUTUHZUTUHZVVEVVIUWTUWIUWBUSUSUWTU
          WIUYSWOZUWTUWBVUFWOZUWTUSUYTWOZVVPWPUWTUWIXEUOZUWBXEUOZVVMVVIWQVVNVVO
          VVQVVRUJZVVMUXAWNUTUHZVVIVVSVVMVVKWNUTUHVVTVVLWNVVKUTWRWSVVSVVKUXAWNU
          TUWIUWBWTXAXBVVSWNUXAWNXEUOVVSXCVSVVSUWBUWIVVQVVRXDVVQVVRXFXGXHXIVOXJ
          XAUWTUYBWNVBUOZUXAVBUOZUVQVVJVVHWQUYPVWAUWTXKVSUWTUWBUWIVUFUYSWDZVUCB
          CEGWNUXAUVJMQTXLXMXNUWTUYBUYQVUEUVQVVFUXNWQUYPVUAVUGVUCBCEGUWLUWEUVJM
          QTXLXMUWTVVGUVLUXBCUWTUVQVVGUVLWQVUCBCEGUVJMQTXOVFXAXPZXAXQUWTUXCBUOZ
          UXSUXMUXIWQUWTUXNUXCBVWDVUIXRZVUOBCGUXGUVMUXCUVFMTUXGWJZVVDXSVOXQUWTB
          CDGVDUXHUXEUXCMPTUYAUWTAVVBUXTUAVFZUWTUYBUXSUXHBUOZUYPVUOBGUXGUVFMVWG
          XTVOZUWTUYBUXDVBUOZUVQUXEBUOZUYPUWTUXAVWCYDZVUCBEGUXDUVJMQWAVNZVWFUWT
          UXHUXBUXGUMZUXEDUWTUXBUVFDUIZUXHVWODUIZUWTUXBUWCUWJCUHZUVFDUWTUYBUWQU
          WRUVQUXBVWRWQUYPVUFUYSVUCBCEGUWBUWIUVJMQTXLXMZUWTVWRHUWJCUHZDUIZVWTUV
          FDUIZVWRUVFDUIZUWTUXPUWCBUOZUYDUWJBUOZUWDVXAUYAUWTUYBUWQUVQVXDUYPVUFV
          UCBEGUWBUVJMQWAVNZVUKUWTUYBUWRUVQVXEUYPUYSVUCBEGUWIUVJMQWAVNZUWTUWDUW
          GVUTWMBCDGUWCHUWJMPTYAWLUWTBCDGVDUWJIHMPTUYAVWHVXGVUMVUKUWTUWKUWNVUSW
          MYBUWTGYCUOZVWRBUOZVWTBUOZUXSVXAVXBUJVXCYEUWTUYFGYFUOZVXHVUQGYGZGYHVP
          ZUWTUYBVXDVXEVXIUYPVXFVXGBCGUWCUWJMTVMVNZUWTUYBUYDVXEVXJUYPVUKVXGBCGH
          UWJMTVMVNVUOBDGVWRVWTUVFMPYIXMYJYKUWTUXPVVBUJUXBBUOZUXSVWPVWQYNUWTUXP
          VVBUYAVWHYOUWTUXBVWRBVWSVXNYLZVUOBDGUXGUXBUVFMPVWGYMVNYPUWTUYBVWBUVQU
          XEVWOWQUYPVWCVUCBEGUXGUXAUVJMQVWGYQVNUUAYBUWTVXHUVNBUOZUXIBUOZUXFBUOZ
          UXJUXKUJUXLYEVXMUWTUYBUXQUXSVXQUYPUYMVUOBGUVMUVGUVFMVVDUUEZVNUWTUYBVW
          EVWIVXRUYPVWFVWJBCGUXCUXHMTVMVNUWTUYBVWEVWLVXSUYPVWFVWNBCGUXCUXEMTVMV
          NBDGFUVNUXIUXFMOPUUBXMYJUWTUXFUVLUXBUXECUHZCUHZUVLUWTUYBUVLBUOZVXOVWL
          UXFVYBWQUYPUWTUYBUVQUVQVYCUYPVUCVUCBCGUVJUVJMTVMZVNZVXPVWNBCGUVLUXBUX
          EMTUUCXMUWTVYBUVLJCUHZUVLUWTVYAJUVLCUWTUXAUXDUTUHZUVJEUHZYRUVJEUHZVYA
          JUWTVYGYRUVJEUWTUXAXEUOVYGYRWQUWTUWBUWIVVOVVNXGUXAUUDVFXAUWTUYBVWBVWK
          UVQVYHVYAWQUYPVWCVWMVUCBCEGUXAUXDUVJMQTXLXMUWTUVQVYIJWQVUCBEGUVJJMNQU
          UNVFXPUUFUWTUYBVYCVYFUVLWQUYPVYEBCGUVLJMTNUUGVOXNXNXQUUHUVTUWHUFVBYSZ
          UWOUGVBYSZUJUWPUGVBYSUFVBYSUVTVYJVYKUVTBDEUFFGUVJHJMNPOQUVIUVQUXPUVKU
          YEWCZUVIUVQGUUIUOZUVKAVYMUVHSVIZWCZVUBVUJUVIUVQUVKUUOZUVIUVQVVBUVKAVV
          BUVHUAVIZWCZYTUVTBDEUGFGUVJIJMNPOQVYLVYOVUBVULVYPVYRYTYOUWHUWOUFUGVBV
          BUUJUUKUULUVTVXKVXQVYCUWAUVSYNUVTUXPUYFVXKVYLVUPVXLVPUVIUVQVXQUVKUVIU
          YBUXQUXSVXQUYIUYLUVIUYBUYDUYCUXSUYIUYKUYJVUNVNZVXTVNZWCUVTUYBUVQUVQVY
          CUVTUXPUYBVYLUYHVFVUBVUBVYDVNBDGFUVNUVLMOPUUMVNYPUVBUUPUUQUVIBCDEFGUV
          NJKLUEMNOPQUYEVYNTVYQAKUKZBUOJWUADUIJLUKZDUIWUBWUADUIUJLBYSUVHUBUURVY
          TUVIUVFUVFUVMUHZJUVNDUVIUYBUXSWUCJWQUYIVYSBGUVMUVFJMNVVDUUSVOUVIUXPUX
          SUXQUXSUVHWUCUVNDUIUYEVYSUYLVYSAUVHXDBDGUVMUVFUVGUVFMPVVDUVCWLUUTUVAU
          VDUVE $.

        $( Lemma for ~ archiabl (Contributed by Thierry Arnoux, 1-May-2018.) $)
        archiabllem2b $p |- ( ph -> ( X .+ Y ) = ( Y .+ X ) ) $=
          ( co wceq wbr archiabllem2c cminusg cfv cgrp wcel cogrp comnd simplbi
          isogrp syl eqid grpinvcl syl2anc coppg wa jca grpcl syl3anc ogrpinvlt
          grpinvadd breq12d bitrd mtbird ctos w3o simprbi omndtos 3syl ecase23d
          wb tlt3 ) AHICUEZIHCUEZUFZVSVTDUGZVTVSDUGZABCDEFGHIJKLMNOPQRSTUAUBUCU
          DUHAWCIGUIUJZUJZHWDUJZCUEZWFWECUEZDUGZABCDEFGWEWFJKLMNOPQRSTUAUBAGUKU
          LZIBULZWEBULAGUMULZWJRWLWJGUNULZGUPZUOUQZUDBGWDIMWDURZUSUTAWJHBULZWFB
          ULWOUCBGWDHMWPUSUTUHAWCVSWDUJZVTWDUJZDUGZWIAWLGVAUJUMULZVBVTBULZVSBUL
          ZWCWTVQAWLXARUAVCAWJWKWQXBWOUDUCBCGIHMTVDVEZAWJWQWKXCWOUCUDBCGHIMTVDV
          EZBDGWDVTVSMPWPVFVEAWRWGWSWHDAWJWQWKWRWGUFWOUCUDBCGWDHIMTWPVGVEAWJWKW
          QWSWHUFWOUDUCBCGWDIHMTWPVGVEVHVIVJAGVKULZXCXBWAWBWCVLAWLWMXFRWLWJWMWN
          VMGVNVOXEXDBDGVSVTMPVRVEVP $.
      $}

      $( Archimedean ordered groups with no minimal positive value are abelian.
         (Contributed by Thierry Arnoux, 1-May-2018.) $)
      archiabllem2 $p |- ( ph -> W e. Abel ) $=
        ( vx vy cgrp wcel cv wceq wral cabel cogrp comnd isogrp simplbi syl w3a
        co 3ad2ant1 carchi coppg cfv wbr wrex simp1 syl3an1 simp2 archiabllem2b
        wa simp3 3expb ralrimivva isabl2 sylanbrc ) AGUCUDZUAUEZUBUEZCUOVNVMCUO
        UFZUBBUGUABUGGUHUDAGUIUDZVLPVPVLGUJUDGUKULUMAVOUAUBBBAVMBUDZVNBUDZVOAVQ
        VRUNZBCDEFGVMVNHIJKLMNOAVQVPVRPUPAVQGUQUDVRQUPRAVQGURUSUIUDVRSUPVSAIUEZ
        BUDHVTDUTHJUEZDUTWAVTDUTVFJBVAAVQVRVBTVCAVQVRVDAVQVRVGVEVHVIUAUBBCGKRVJ
        VK $.
    $}
  $}

  ${
    $d u v x y W $. 
    $( Archimedean left- and right- ordered groups are Abelian.  (Contributed
       by Thierry Arnoux, 1-May-2018.) $)
    archiabl $p |- ( ( W e. oGrp /\ ( oppG ` W ) e. oGrp /\ W e. Archi )
      -> W e. Abel ) $=
      ( vu vx vv vy cogrp wcel cfv w3a cv wi wral wa wrex eqid simp2 wceq breq2
      wbr wn coppg carchi c0g cplt cple cbs cabel simpll1 simpll3 simplr simprl
      cmg simp1rr simp3 imbi12d rspcv imp syl21anc archiabllem1 adantllr imbi2d
      ralbidv anbi12d cbvrexv r19.29a cplusg simpl1 simpl3 simpl2 ralnex sylibr
      simpr breq1 sylib annim rexbii rexnal imbi2i ralbii notbid anbi2d rexbidv
      bitri imnan cbvralv r19.21bi syl6ib 3impia ctos wb 3ad2ant1 comnd simprbi
      cgrp isogrp omndtos syl tltnle bicomd 3com23 3expa rexbidva syl2anc mpbid
      archiabllem2 pm2.61dan ) AFGZAUAHFGZAUBGZIZAUCHZBJZAUDHZSZXKCJZXMSZXLXOAU
      EHZSZKZCAUFHZLZMZBXTNZAUGGZXJYCMZXKDJZXMSZXPYFXOXQSZKZCXTLZMZYDDXTXJYFXTG
      ZYKYDYCXJYLMZYKMZEXTXMAULHZYFXQAXKXTOZXKOZXQOZXMOZYOOZXGXHXIYLYKUHXGXHXIY
      LYKUIXJYLYKUJYMYGYJUKYNEJZXTGZXKUUAXMSZIUUBYJUUCYFUUAXQSZYNUUBUUCPYGYJYMU
      UBUUCUMYNUUBUUCUNUUBYJMUUCUUDUUBYJUUCUUDKZYIUUECUUAXTXOUUAQZXPUUCYHUUDXOU
      UAXKXMRZXOUUAYFXQRZUOUPUQUQURUSUTYEYCYKDXTNXJYCVLYBYKBDXTXLYFQZXNYGYAYJXL
      YFXKXMRZUUIXSYICXTUUIXRYHXPXLYFXOXQVMZVAVBVCVDVNVEXJYCTZMZXTAVFHZXMYOXQAX
      KDEYPYQYRYSYTXGXHXIUULVGZXGXHXIUULVHUUNOXGXHXIUULVIUUMYLYGIZUUCUUDTZMZEXT
      NZUUCUUAYFXMSZMZEXTNZUUMYLYGUUSUUMYLMYGXPYHTZMZCXTNZUUSUUMYGUVEKZDXTUUMXN
      XPXRTZMZCXTNZKZBXTLZUVFDXTLUUMYBTZBXTLZUVKUUMUULUVMXJUULVLYBBXTVJVKUVJUVL
      BXTUVJXNYATZKUVLUVIUVNXNUVIXSTZCXTNUVNUVHUVOCXTXPXRVOVPXSCXTVQWCVRXNYAWDW
      CVSVKUVJUVFBDXTUUIXNYGUVIUVEUUJUUIUVHUVDCXTUUIUVGUVCXPUUIXRYHUUKVTWAWBUOW
      EVNWFUVDUURCEXTUUFXPUUCUVCUUQUUGUUFYHUUDUUHVTVCVDWGWHUUPAWIGZYLUUSUVBWJUU
      PXGUVPUUMYLXGYGUUOWKXGAWLGZUVPXGAWNGUVQAWOWMAWPWQWQUUMYLYGPUVPYLMZUURUVAE
      XTUVRUUBMUUQUUTUUCUVPYLUUBUUQUUTWJZUVPUUBYLUVSUVPUUBYLIUUTUUQXTXMAXQUUAYF
      YPYRYSWRWSWTXAWAXBXCXDXEXF $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Semirings
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c SRing $.
  
  $( Extend class notation with the class of all semirings $)
  csrg $a class SRing $.

  ${
    $d f n p r t x y z $.
    $( Define class of all semirings.  A semiring is a set equipped with two
       everywhere-defined internal operations, whose first one is an additive
       commutative monoid structure and the second one is a multiplicative
       monoid structure, and where the addition is left- and right-distributive
       for the multiplication.  Compared to the definition of a ring, this
       definition also adds that the additive identity is an absorbing element
       of the multiplivative law, as this cannot be deduced from the 
       distributivity alone.  Definition of [Golan] p. 1.  (Contributed by
       Thierry Arnoux, 21-Mar-2018.) $)
    df-srg $a |- SRing = { f e. CMnd | ( ( mulGrp ` f ) e. Mnd /\
        [. ( Base ` f ) / r ]. [. ( +g ` f ) / p ]. [. ( .r ` f ) / t ].
        [. ( 0g ` f ) / n ]. A. x e. r ( A. y e. r A. z e. r
           ( ( x t ( y p z ) ) = ( ( x t y ) p ( x t z ) )
            /\ ( ( x p y ) t z ) = ( ( x t z ) p ( y t z ) ) ) 
            /\ ( ( n t x ) = n /\ ( x t n ) = n ) ) ) } $.
  $}

  ${
    $d b n p r t x y z .+ $.  $d b n p r t x y z .0. $.  $d r G $.
    $d b n p r t x y z .x. $.  $d b n p r t x y z B $.  $d b n p r t x y z R $.
    issrg.b $e |- B = ( Base ` R ) $.
    issrg.g $e |- G = ( mulGrp ` R ) $.
    issrg.p $e |- .+ = ( +g ` R ) $.
    issrg.t $e |- .x. = ( .r ` R ) $.
    issrg.0 $e |- .0. = ( 0g ` R ) $.
    $( The predicate "is a semiring."  (Contributed by Thierry Arnoux,
       21-Mar-2018.)  $)
    issrg $p |- ( R e. SRing <-> ( R e. CMnd /\ G e. Mnd
      /\ A. x e. B ( A. y e. B A. z e. B
       ( ( x .x. ( y .+ z ) ) = ( ( x .x. y ) .+ ( x .x. z ) )
      /\ ( ( x .+ y ) .x. z ) = ( ( x .x. z ) .+ ( y .x. z ) ) ) 
      /\ ( ( .0. .x. x ) = .0. /\ ( x .x. .0. ) = .0. ) ) ) ) $=
      ( wcel cfv co wceq wa cvv vp vt vb vn vr ccmn cmgp cmnd cv wral wsbc csrg
      w3a eleq1i bicomi cbs eqeltri cplusg a1i cmulr c0g simplll simplr simpllr
      eqidd oveqd oveq123d eqeq12d anbi12d raleqbidv simpr sbcied sbcie anbi12i
      anbi2i fveq2 eleq1d syl6eqr biidd sbceqbid df-srg elrab2 3anass 3bitr4i
      fvex ) FUFOZFUGPZUHOZAUIZBUIZCUIZUAUIZQZUBUIZQZWIWJWNQZWIWKWNQZWLQZRZWIWJ
      WLQZWKWNQZWQWJWKWNQZWLQZRZSZCUCUIZUJZBXFUJZUDUIZWIWNQZXIRZWIXIWNQZXIRZSZS
      ZAXFUJZUDIUKZUBGUKZUAEUKZUCDUKZSZSWFHUHOZWIWJWKEQZGQZWIWJGQZWIWKGQZEQZRZW
      IWJEQZWKGQZYFWJWKGQZEQZRZSZCDUJZBDUJZIWIGQZIRZWIIGQZIRZSZSZADUJZSZSFULOWF
      YBUUCUMYAUUDWFWHYBXTUUCYBWHHWGUHKUNUOXSUUCUCDDFUPPZTJFUPWEUQXFDRZXRUUCUAE
      TETOUUFEFURPZTLFURWEUQUSUUFWLERZSZXQUUCUBGTGTOUUIGFUTPZTMFUTWEUQUSUUIWNGR
      ZSZXPUUCUDITITOUULIFVAPZTNFVAWEUQUSUULXIIRZSZXOUUBAXFDUUFUUHUUKUUNVBZUUOX
      HYPXNUUAUUOXGYOBXFDUUPUUOXEYNCXFDUUPUUOWSYHXDYMUUOWOYDWRYGUUOWIWIWMYCWNGU
      UIUUKUUNVCZUUOWIVEZUUOWLEWJWKUUFUUHUUKUUNVDZVFVGUUOWPYEWQYFWLEUUSUUOWNGWI
      WJUUQVFUUOWNGWIWKUUQVFZVGVHUUOXAYJXCYLUUOWTYIWKWKWNGUUQUUOWLEWIWJUUSVFUUO
      WKVEVGUUOWQYFXBYKWLEUUSUUTUUOWNGWJWKUUQVFVGVHVIVJVJUUOXKYRXMYTUUOXJYQXIIU
      UOXIIWIWIWNGUUQUULUUNVKZUURVGUVAVHUUOXLYSXIIUUOWIWIXIIWNGUUQUURUVAVGUVAVH
      VIVIVJVLVLVLVMVNVOUEUIZUGPZUHOZXPUDUVBVAPZUKZUBUVBUTPZUKZUAUVBURPZUKZUCUV
      BUPPZUKZSYAUEFUFULUVBFRZUVDWHUVLXTUVMUVCWGUHUVBFUGVPVQUVMUVJXSUCUVKDUVMUV
      KUUEDUVBFUPVPJVRUVMUVHXRUAUVIEUVMUVIUUGEUVBFURVPLVRUVMUVFXQUBUVGGUVMUVGUU
      JGUVBFUTVPMVRUVMXPXPUDUVEIUVMUVEUUMIUVBFVAVPNVRUVMXPVSVTVTVTVTVIABCUBUEUD
      UCUAWAWBWFYBUUCWCWD $.
  $}

  ${
    $d x y z R $.       
    $( Any ring is also a semiring.  (Contributed by Thierry Arnoux,
       1-Apr-2018.)  $)
    rngsrg $p |- ( R e. Ring -> R e. SRing ) $=
      ( vx vy vz crg wcel ccmn cmgp cfv cmnd cv cplusg co cmulr wceq wa cbs w3a
      wral eqid c0g csrg rngcmn cgrp isrng biimpi simp2d simp3d rnglz rngrz jca
      ralrimiva r19.26 sylanbrc 3jca issrg sylibr ) AEFZAGFZAHIZJFZBKZCKZDKZALI
      ZMANIZMVBVCVFMVBVDVFMZVEMOVBVCVEMVDVFMVGVCVDVFMVEMOPDAQIZSCVHSZAUAIZVBVFM
      VJOZVBVJVFMVJOZPZPBVHSZRAUBFURUSVAVNAUCURAUDFZVAVIBVHSZURVOVAVPRBCDVHVEAV
      FUTVHTZUTTZVETZVFTZUEUFZUGURVPVMBVHSVNURVOVAVPWAUHURVMBVHURVBVHFPVKVLVHAV
      FVBVJVQVTVJTZUIVHAVFVBVJVQVTWBUJUKULVIVMBVHUMUNUOBCDVHVEAVFUTVJVQVRVSVTWB
      UPUQ $.

    $( A semiring is a commutative monoid.  (Contributed by Thierry Arnoux,
       21-Mar-2018.)  $)
    srgcmn $p |- ( R e. SRing -> R e. CMnd ) $=
      ( vx vy vz csrg wcel ccmn cmgp cfv cmnd cv cplusg cmulr wceq cbs wral c0g
      co wa eqid issrg simp1bi ) AEFAGFAHIZJFBKZCKZDKZALIZRAMIZRUDUEUHRUDUFUHRZ
      UGRNUDUEUGRUFUHRUIUEUFUHRUGRNSDAOIZPCUJPAQIZUDUHRUKNUDUKUHRUKNSSBUJPBCDUJ
      UGAUHUCUKUJTUCTUGTUHTUKTUAUB $.

    $( A semiring is a monoid.  (Contributed by Thierry Arnoux, 21-Mar-2018.)
       $)
    srgmnd $p |- ( R e. SRing -> R e. Mnd ) $=
      ( csrg wcel ccmn cmnd srgcmn cmnmnd syl ) ABCADCAECAFAGH $.

    srgmgp.g $e |- G = ( mulGrp ` R ) $.
    $( A semiring is a monoid under multiplication.  (Contributed by Thierry
       Arnoux, 21-Mar-2018.)  $)
    srgmgp $p |- ( R e. SRing -> G e. Mnd ) $=
      ( vx vy vz csrg wcel ccmn cmnd cv cplusg cfv co cmulr wceq cbs wral eqid
      wa c0g issrg simp2bi ) AGHAIHBJHDKZEKZFKZALMZNAOMZNUDUEUHNUDUFUHNZUGNPUDU
      EUGNUFUHNUIUEUFUHNUGNPTFAQMZREUJRAUAMZUDUHNUKPUDUKUHNUKPTTDUJRDEFUJUGAUHB
      UKUJSCUGSUHSUKSUBUC $.
  $}

  ${
    $d x y z B $.  $d x y z R $.  $d x y z .x. $.  $d x y z X $.  $d x y z Y $.
    $d x y z .+ $.  $d x y z Z $.
    srgi.b $e |- B = ( Base ` R ) $.
    srgi.p $e |- .+ = ( +g ` R ) $.
    srgi.t $e |- .x. = ( .r ` R ) $.
    $( Properties of a semiring.  (Contributed by NM, 26-Aug-2011.)
       (Revised by Mario Carneiro, 6-Jan-2015.)  (Revised by Thierry
       Arnoux, 1-Apr-2018.)  $)
    srgi $p |- ( ( R e. SRing /\ ( X e. B /\ Y e. B /\ Z e. B ) )
           -> ( ( X .x. ( Y .+ Z ) ) = ( ( X .x. Y ) .+ ( X .x. Z ) )
                /\ ( ( X .+ Y ) .x. Z ) = ( ( X .x. Z ) .+ ( Y .x. Z ) ) ) ) $=
      ( vx vy vz wcel wa co wceq cv wral rsp csrg w3a ccmn cmgp cmnd eqid issrg
      c0g simp3bi r19.21bi simpld ralrimiva adantr simpr1 simpr2 simpr3 caovdig
      cfv sylc simprd caovdirg jca ) CUANZEANFANGANUBOEFGBPDPEFDPEGDPZBPQEFBPGD
      PVDFGDPBPQVCKLMEFGABDBAVCKRZANZLRZANZMRZANZUBZOZVEVGVIBPDPVEVGDPVEVIDPZBP
      QZVEVGBPVIDPVMVGVIDPBPQZVLVNVOOZMASZVJVPVLVQLASZVHVQVLVRKASZVFVRVCVSVKVCV
      RKAVCVFOVRCUHURZVEDPVTQVEVTDPVTQOZVCVRWAOZKAVCCUCNCUDURZUENWBKASKLMABCDWC
      VTHWCUFIJVTUFUGUIUJUKULUMVCVFVHVJUNVRKATUSVCVFVHVJUOVQLATUSVCVFVHVJUPVPMA
      TUSZUKUQVCKLMEFGABDBAVLVNVOWDUTVAVB $.
  $}

  ${
    srgcl.b $e |- B = ( Base ` R ) $.
    srgcl.t $e |- .x. = ( .r ` R ) $.
    $( Closure of the multiplication operation of a semiring.  (Contributed by
       NM, 26-Aug-2011.)  (Revised by Mario Carneiro, 6-Jan-2015.)  (Revised by
       Thierry Arnoux, 1-Apr-2018.) $)
    srgcl $p |- ( ( R e. SRing /\ X e. B /\ Y e. B ) -> ( X .x. Y ) e. B ) $=
      ( csrg wcel cmgp cfv cmnd co eqid srgmgp mgpbas mgpplusg mndcl syl3an1 )
      BHIBJKZLIDAIEAIDECMAIBTTNZOACTDEABTUAFPBCTUAGQRS $.

    $( Associative law for the multiplication operation of a semiring.
       (Contributed by NM, 27-Aug-2011.)  (Revised by Mario Carneiro,
       6-Jan-2015.)  (Revised by Thierry Arnoux, 1-Apr-2018.) $)
    srgass $p |- ( ( R e. SRing /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
                      ( ( X .x. Y ) .x. Z ) = ( X .x. ( Y .x. Z ) ) ) $=
      ( csrg wcel cmgp cfv cmnd w3a co wceq eqid srgmgp mgpbas mgpplusg mndass
      sylan ) BIJBKLZMJDAJEAJFAJNDECOFCODEFCOCOPBUCUCQZRACUCDEFABUCUDGSBCUCUDHT
      UAUB $.

    $d u x B $.  $d u x R $.  $d u x .x. $.
    $( The unit element of a ring is unique.  (Contributed by NM,
       27-Aug-2011.)  (Revised by Mario Carneiro, 6-Jan-2015.)  (Revised by
       Thierry Arnoux, 1-Apr-2018.) $)
    srgideu $p |- ( R e. SRing ->
                E! u e. B A. x e. B ( ( u .x. x ) = x /\ ( x .x. u ) = x ) ) $=
      ( csrg wcel cmgp cfv cmnd cv co wceq wa wral wreu eqid srgmgp mndideu syl
      mgpbas mgpplusg ) DHIDJKZLIBMZAMZENUGOUGUFENUGOPACQBCRDUEUESZTABCEUECDUEU
      HFUCDEUEUHGUDUAUB $.
  $}

  ${
    srgdi.b $e |- B = ( Base ` R ) $.
    srgdi.p $e |- .+ = ( +g ` R ) $.
    srgdi.t $e |- .x. = ( .r ` R ) $.
    $( Distributive law for the multiplication operation of a semiring.
       (Contributed by Steve Rodriguez, 9-Sep-2007.)  (Revised by Thierry
       Arnoux, 1-Apr-2018.) $)
    srgdi $p |- ( ( R e. SRing /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
                     ( X .x. ( Y .+ Z ) ) = ( ( X .x. Y ) .+ ( X .x. Z ) ) ) $=
      ( csrg wcel w3a wa co wceq srgi simpld ) CKLEALFALGALMNEFGBODOEFDOEGDOZBO
      PEFBOGDOSFGDOBOPABCDEFGHIJQR $.

    $( Distributive law for the multiplication operation of a semiring.
       (Contributed by Steve Rodriguez, 9-Sep-2007.)  (Revised by Thierry
       Arnoux, 1-Apr-2018.) $)
    srgdir $p |- ( ( R e. SRing /\ ( X e. B /\ Y e. B /\ Z e. B ) ) ->
                     ( ( X .+ Y ) .x. Z ) = ( ( X .x. Z ) .+ ( Y .x. Z ) ) ) $=
      ( csrg wcel w3a wa co wceq srgi simprd ) CKLEALFALGALMNEFGBODOEFDOEGDOZBO
      PEFBOGDOSFGDOBOPABCDEFGHIJQR $.
  $}

  ${
    srgidcl.b $e |- B = ( Base ` R ) $.
    srgidcl.u $e |- .1. = ( 1r ` R ) $.
    $( The unit element of a semiring belongs to the base set of the semiring.
       (Contributed by NM, 27-Aug-2011.)  (Revised by Mario Carneiro,
       27-Dec-2014.)  (Revised by Thierry Arnoux, 1-Apr-2018.) $)
    srgidcl $p |- ( R e. SRing -> .1. e. B ) $=
      ( csrg wcel cmgp cfv cmnd eqid srgmgp mgpbas rngidval mndidcl syl ) BFGBH
      IZJGCAGBQQKZLAQCABQRDMBCQRENOP $.
  $}

  ${
    srg0cl.b $e |- B = ( Base ` R ) $.
    srg0cl.z $e |- .0. = ( 0g ` R ) $.
    $( The zero element of a semiring belongs to its base set.  (Contributed by
       Mario Carneiro, 12-Jan-2014.)  (Revised by Thierry Arnoux, 1-Apr-2018.)
       $)
    srg0cl $p |- ( R e. SRing -> .0. e. B ) $=
      ( csrg wcel cmnd srgmnd mndidcl syl ) BFGBHGCAGBIABCDEJK $.
  $}

  ${
    $d x y B $.  $d x y I $.  $d x y R $.  $d x y .x. $.  $d x y .1. $.
    srgidm.b $e |- B = ( Base ` R ) $.
    srgidm.t $e |- .x. = ( .r ` R ) $.
    srgidm.u $e |- .1. = ( 1r ` R ) $.
    $( Lemma for ~ srglidm and ~ srgridm .  (Contributed by NM, 15-Sep-2011.)
       (Revised by Mario Carneiro, 27-Dec-2014.)  (Revised by Thierry Arnoux,
       1-Apr-2018.) $)
    srgidmlem $p |- ( ( R e. SRing /\ X e. B )
           -> ( ( .1. .x. X ) = X /\ ( X .x. .1. ) = X ) ) $=
      ( csrg wcel cmgp cfv cmnd co wceq wa eqid srgmgp mgpbas mgpplusg rngidval
      mndlrid sylan ) BIJBKLZMJEAJDECNEOEDCNEOPBUDUDQZRACUDEDABUDUEFSBCUDUEGTBD
      UDUEHUAUBUC $.

    $( The unit element of a semiring is a left multiplicative identity.
       (Contributed by NM, 15-Sep-2011.)  (Revised by Thierry Arnoux,
       1-Apr-2018.) $)
    srglidm $p |- ( ( R e. SRing /\ X e. B ) -> ( .1. .x. X ) = X ) $=
      ( csrg wcel wa co wceq srgidmlem simpld ) BIJEAJKDECLEMEDCLEMABCDEFGHNO
      $.

    $( The unit element of a semiring is a right multiplicative identity.
       (Contributed by NM, 15-Sep-2011.)  (Revised by Thierry Arnoux,
       1-Apr-2018.) $)
    srgridm $p |- ( ( R e. SRing /\ X e. B ) -> ( X .x. .1. ) = X ) $=
      ( csrg wcel wa co wceq srgidmlem simprd ) BIJEAJKDECLEMEDCLEMABCDEFGHNO
      $.

    $( Properties showing that an element ` I ` is the unity element of a
       semiring.  (Contributed by NM, 7-Aug-2013.)  (Revised by Thierry Arnoux,
       1-Apr-2018.) $)
    issrgid $p |- ( R e. SRing
      -> ( ( I e. B /\ A. x e. B ( ( I .x. x ) = x /\ ( x .x. I ) = x ) )
        <-> .1. = I ) ) $=
      ( vy csrg wcel cmgp cfv eqid mgpbas rngidval cv co wceq wa wral wreu wrex
      mgpplusg srgideu reurex syl ismgmid ) CKLZABDFJCMNZEBCUKUKOZGPCEUKULIQCDU
      KULHUEUJJRZARZDSUNTUNUMDSUNTUAABUBZJBUCUOJBUDAJBCDGHUFUOJBUGUHUI $.
  $}

  ${
    srgacl.b $e |- B = ( Base ` R ) $.
    srgacl.p $e |- .+ = ( +g ` R ) $.
    $( Closure of the addition operation of a semiring.  (Contributed by Mario
       Carneiro, 14-Jan-2014.)  (Revised by Thierry Arnoux, 1-Apr-2018.) $)
    srgacl $p |- ( ( R e. SRing /\ X e. B /\ Y e. B ) -> ( X .+ Y ) e. B ) $=
      ( csrg wcel cmnd co srgmnd mndcl syl3an1 ) CHICJIDAIEAIDEBKAICLABCDEFGMN
      $.

    $( Commutativity of the additive group of a semiring.  (Contributed by
       Thierry Arnoux, 1-Apr-2018.) $)
    srgcom $p |- ( ( R e. SRing /\ X e. B /\ Y e. B ) ->
      ( X .+ Y ) = ( Y .+ X ) ) $=
      ( csrg wcel ccmn co wceq srgcmn cmncom syl3an1 ) CHICJIDAIEAIDEBKEDBKLCMA
      BCDEFGNO $.
  $}

  ${
    $d x y z B $.  $d x y z R $.  $d x X $.  $d x y z .x. $.  $d x y z .0. $.
    srgz.b $e |- B = ( Base ` R ) $.
    srgz.t $e |- .x. = ( .r ` R ) $.
    srgz.z $e |- .0. = ( 0g ` R ) $.
    $( The zero of a semiring is a right absorbing element.  (Contributed by
       Thierry Arnoux, 1-Apr-2018.) $)
    srgrz $p |- ( ( R e. SRing /\ X e. B ) -> ( X .x. .0. ) = .0. ) $=
      ( vx vy vz wcel cv co wceq wral wa cfv eqid simprd csrg cplusg ccmn issrg
      cmgp cmnd simp3bi r19.21bi ralrimiva oveq1 eqeq1d rspcv mpan9 ) BUALZIMZE
      CNZEOZIAPDALDECNZEOZUNUQIAUNUOALQZEUOCNEOZUQUTUOJMZKMZBUBRZNCNUOVBCNUOVCC
      NZVDNOUOVBVDNVCCNVEVBVCCNVDNOQKAPJAPZVAUQQZUNVFVGQZIAUNBUCLBUERZUFLVHIAPI
      JKAVDBCVIEFVISVDSGHUDUGUHTTUIUQUSIDAUODOUPUREUODECUJUKULUM $.

    $d x X $.  $d x Z $.  $d x ph $.  
    srgisid.1 $e |- ( ph -> R e. SRing ) $. 
    srgisid.2 $e |- ( ph -> Z e. B ) $. 
    srgisid.3 $e |- ( ( ph /\ x e. B ) -> ( Z .x. x ) = Z ) $. 
    $( In a semiring, the only absorbing element is the additive identity.
       Remark in [Golan] p. 1.  (Contributed by Thierry Arnoux, 1-May-2018.) $)
    srgisid $p |- ( ph -> Z = .0. ) $=
      ( co cv wceq wral ralrimiva csrg wcel srg0cl oveq2 eqeq1d rspcv mpd srgrz
      wi 3syl syl2anc eqtr3d ) AGFENZGFAGBOZENZGPZBCQZUKGPZAUNBCMRADSTZFCTUOUPU
      GKCDFHJUAUNUPBFCULFPUMUKGULFGEUBUCUDUHUEAUQGCTUKFPKLCDEGFHIJUFUIUJ $.
  $}

  ${
    $d x y z $. 
    $( The natural numbers (including zero) form a semiring.  (Contributed by
       Thierry Arnoux, 1-May-2018.) $)
    nn0srg $p |- ( CCfld |`s NN0 ) e. SRing $=
      ( vx vy vz ccnfld cn0 co wcel cfv cmnd caddc cmul wceq wa wral ax-mp eqid
      cc0 cvv cc nn0sscn cress csrg ccmn cmgp csubmnd crg cnrng nn0subm submcmn
      cv rngcmn mp2an nn0ex mgpress wss c1 w3a nn0mulcl rgen2 3pm3.2i wb rngmgp
      cnfldbas mgpbas cnfld1 rngidval cnfldmul mgpplusg issubm submmnd eqeltrri
      1nn0 mpbir simpl nn0cn syl simprl sseldi simprr adddid adddird ralrimivva
      jca mul02d mul01d rgen cbs ressbas2 cnfldadd ressplusg cmulr ressmulr c0g
      cplusg rngmnd 0nn0 cnfld0 ress0g mp3an issrg mpbir3an ) DEUAFZUBGXBUCGZXB
      UDHZIGAUJZBUJZCUJZJFKFXEXFKFZXEXGKFZJFLZXEXFJFXGKFXIXFXGKFJFLZMZCENBENZQX
      EKFQLZXEQKFQLZMZMZAENDUCGZEDUEHGXCDUFGZXRUGDUKOZUHEDXBXBPZUIULDUDHZEUAFZX
      DIXRERGZYCXDLXTUMEDXBYBUCRYAYBPZUNULEYBUEHGZYCIGYFESUOZUPEGZXHEGZBENAENZU
      QZYGYHYJTVLYIABEEXEXFURUSUTYBIGZYFYKVAXSYLUGDYBYEVBOABSKEYBUPSDYBYEVCVDDU
      PYBYEVEVFDKYBYEVGVHVIOVMEYCYBYCPVJOVKXQAEXEEGZXMXPYMXLBCEEYMXFEGZXGEGZMZM
      ZXJXKYQXEXFXGYQYMXESGYMYPVNXEVOZVPZYQESXFTYMYNYOVQVRZYQESXGTYMYNYOVSVRZVT
      YQXEXFXGYSYTUUAWAWCWBYMXNXOYMXEYRWDYMXEYRWEWCWCWFABCEJXBKXDQYGEXBWGHLTESX
      BDYAVCWHOXDPYDJXBWNHLUMEJDXBRYAWIWJOYDKXBWKHLUMEDXBKRYAVGWLODIGZQEGYGQXBW
      MHLXSUUBUGDWOOWPTESDXBQYAVCWQWRWSWTXA $.
  $} 

  ${
    $d x y z $. 
    $( The non-negative real numbers form a semiring.  (Contributed by Thierry
       Arnoux, 6-Sep-2018.) $)
    rge0srg $p |- ( CCfld |`s ( 0 [,) +oo ) ) e. SRing $=
      ( vx vy vz ccnfld cc0 cpnf co wcel cfv caddc cmul wceq wa ax-mp cc cr wbr
      wral c1 cvv cico cress csrg ccmn cmgp cv csubmnd crg cnrng rngcmn wss w3a
      cmnd cmnf cioo cxr clt cle mnfxr pnfxr mnflt pnfge icossioo mp4an sseqtri
      0re ioomax ax-resscn sstri 0xr ltpnf lbico1 mp3an ge0addcl 3pm3.2i rngmnd
      rgen2 cnfldbas cnfld0 cnfldadd issubm mpbir eqid submcmn mp2an 1re elico2
      wb 0le1 mpbir3an ge0mulcl rngmgp mgpbas cnfld1 rngidval cnfldmul mgpplusg
      mp2b submmnd simpll sseldi simplr simpr adddid jca ralrimiva sseli mul02d
      adddird mul01d jca32 rgen ressbas2 cnfldex mgpress cplusg ressplusg cmulr
      cbs ovex ressmulr c0g ress0g issrg ) DEFUAGZUBGZUCHYFUDHZDUEIZYEUBGZUMHZA
      UFZBUFZCUFZJGKGYKYLKGZYKYMKGZJGLZYKYLJGZYMKGYOYLYMKGJGLZMZCYERZBYERZEYKKG
      ELZYKEKGELZMMZAYERDUDHZYEDUGIHZYGDUHHZUUEUIDUJNUUFYEOUKZEYEHZYQYEHZBYERAY
      ERZULZUUHUUIUUKYEPOYEUNFUOGZPUNUPHFUPHZUNEUQQZFFURQZYEUUMUKUSUTEPHZUUOVFE
      VANUUNUUPUTFVBNUNFEFVCVDVGVEVHVIZEUPHUUNEFUQQZUUIVJUTUUQUUSVFEVKNEFVLVMZU
      UJABYEYEYKYLVNVQVODUMHZUUFUULWHUUGUVAUIDVPNZABOJYEDEVRVSVTWANWBYEDYFYFWCZ
      WDWEYEYHUGIHZYJUVDUUHSYEHZYNYEHZBYERAYERZULZUUHUVEUVGUURUVESPHZESURQZSFUQ
      QZWFWIUVIUVKWFSVKNUUQUUNUVEUVIUVJUVKULWHVFUTEFSWGWEWJUVFABYEYEYKYLWKVQVOU
      UGYHUMHUVDUVHWHUIDYHYHWCZWLABOKYEYHSODYHUVLVRWMDSYHUVLWNWODKYHUVLWPWQWAWR
      WBYEYIYHYIWCWSNUUDAYEYKYEHZUUAUUBUUCUVMYTBYEUVMYLYEHZMZYSCYEUVOYMYEHZMZYP
      YRUVQYKYLYMUVQYEOYKUURUVMUVNUVPWTXAZUVQYEOYLUURUVMUVNUVPXBXAZUVQYEOYMUURU
      VOUVPXCXAZXDUVQYKYLYMUVRUVSUVTXIXEXFXFUVMYKYEOYKUURXGZXHUVMYKUWAXJXKXLABC
      YEJYFKYIEUUHYEYFXSILUURYEOYFDUVCVRXMNDTHYETHZYIYFUEILXNEFUAXTZYEDYFYHTTUV
      CUVLXOWEUWBJYFXPILUWCYEJDYFTUVCVTXQNUWBKYFXRILUWCYEDYFKTUVCWPYANUVAUUIUUH
      EYFYBILUVBUUTUURYEODYFEUVCVRVSYCVMYDWJ $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Semiring left modules
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c SLMod $.

  $( Extend class notation with class of all semimodules. $)
  cslmd $a class SLMod $.

  ${
    $d a f g k p q r s t v w x y $.
    $( Define the class of all (left) modules over semirings, i.e. semimodules,
       which are generalizations of left modules.  A semimodule is a 
       commutative monoid (=vectors) together with a semiring (=scalars) and a
       left scalar product connecting them.  ` ( 0 [,] +oo ) ` for example is
       not a full fledged left module, but is a semimodule.  Definition of
       [Golan] p. 149.  (Contributed by Thierry Arnoux, 21-Mar-2018.) $)
    df-slmd $a |- SLMod = { g e. CMnd | [. ( Base ` g ) / v ].
      [. ( +g ` g ) / a ]. [. ( .s ` g ) / s ]. [. ( Scalar ` g ) / f ].
      [. ( Base ` f ) / k ]. [. ( +g ` f ) / p ]. [. ( .r ` f ) / t ].
      ( f e. SRing /\ A. q e. k A. r e. k A. x e. v A. w e. v
                ( ( ( r s w ) e. v
                 /\ ( r s ( w a x ) ) = ( ( r s w ) a ( r s x ) )
                 /\ ( ( q p r ) s w ) = ( ( q s w ) a ( r s w ) )
               ) /\ ( ( ( q t r ) s w ) = ( q s ( r s w ) )
                 /\ ( ( 1r ` f ) s w ) = w 
                 /\ ( ( 0g ` f ) s w ) = ( 0g ` g ) ) ) ) } $.
  $}

  ${
    $d a f g k p q r s t v w x .X. $.  $d a f g k p q r s v w x .+ $.
    $d a f g k p q r s v w x .+^ $.  $d a f g k p q r s v w x .1. $.
    $d a f g k p q r s v w x .x. $.  $d a f g k p q r s t v w x F $.
    $d a f g k p q r s v w x K $.  $d a f g k p q r s v w x V $.
    $d a f g q r s v w x W $.  $d g q r w x .0. $.  $d g q r w x O $.
    $d q r w x Q $.  $d r w x R $.  $d w x X $.  $d w Y $.
    isslmd.v $e |- V = ( Base ` W ) $.
    isslmd.a $e |- .+ = ( +g ` W ) $.
    isslmd.s $e |- .x. = ( .s ` W ) $.
    isslmd.0 $e |- .0. = ( 0g ` W ) $.
    isslmd.f $e |- F = ( Scalar ` W ) $.
    isslmd.k $e |- K = ( Base ` F ) $.
    isslmd.p $e |- .+^ = ( +g ` F ) $.
    isslmd.t $e |- .X. = ( .r ` F ) $.
    isslmd.u $e |- .1. = ( 1r ` F ) $.
    isslmd.o $e |- O = ( 0g ` F ) $.
    $( The predicate "is a semimodule".  (Contributed by NM, 4-Nov-2013.)
       (Revised by Mario Carneiro, 19-Jun-2014.)  (Revised by Thierry Arnoux,
       1-Apr-2018.) $)
    isslmd $p |- ( W e. SLMod <->
      ( W e. CMnd /\ F e. SRing /\ A. q e. K A. r e. K A. x e. V A. w e. V
                ( ( ( r .x. w ) e. V
                 /\ ( r .x. ( w .+ x ) ) = ( ( r .x. w ) .+ ( r .x. x ) )
                 /\ ( ( q .+^ r ) .x. w ) = ( ( q .x. w ) .+ ( r .x. w ) )
               ) /\ ( ( ( q .X. r ) .x. w ) = ( q .x. ( r .x. w ) )
                 /\ ( .1. .x. w ) = w 
                 /\ ( O .x. w ) = .0. ) ) ) ) $=
      ( vf vs vv va vp vt vg vk cslmd wcel ccmn csrg cv co wceq w3a wa wral cur
      cfv c0g cmulr wsbc cplusg csca cvsca fvex simp1 simp2 oveqd oveq1d eqeq1d
      cbs 3anbi3d simp3 3anbi1d anbi12d 2ralbidv raleqbidv anbi2d sbc3ie eleq1d
      simpr fveq2d simpl oveq12d eqeq12d eqidd oveq123d 3anbi123d syl5bb sbc2ie
      eleq2d oveq2d eqeq2d anbi1d syl6eqr eleq12d df-slmd elrab2 3anass bitr4i
      fveq2 ) LUNUOLUPUOZHUQUOZNURZBURZEUSZKUOZXKXLAURZCUSZEUSZXMXKXOEUSZCUSZUT
      ZOURZXKDUSZXLEUSZYAXLEUSZXMCUSZUTZVAZYAXKFUSZXLEUSZYAXMEUSZUTZGXLEUSZXLUT
      ZJXLEUSZMUTZVAZVBZBKVCZAKVCZNIVCZOIVCZVBZVBXIXJUUAVAUFURZUQUOZXKXLUGURZUS
      ZUHURZUOZXKXLXOUIURZUSZUUEUSZUUFXKXOUUEUSZUUIUSZUTZYAXKUJURZUSZXLUUEUSZYA
      XLUUEUSZUUFUUIUSZUTZVAZYAXKUKURZUSZXLUUEUSZYAUUFUUEUSZUTZUUCVDVEZXLUUEUSZ
      XLUTZUUCVFVEZXLUUEUSZULURZVFVEZUTZVAZVBZBUUGVCAUUGVCZNUMURZVCZOUVRVCZVBZU
      KUUCVGVEZVHUJUUCVIVEZVHUMUUCVRVEZVHZUFUVLVJVEZVHUGUVLVKVEZVHZUIUVLVIVEZVH
      UHUVLVRVEZVHZUUBULLUPUNUWKUWFUQUOZXKXLUWGUSZUWJUOZXKXLXOUWIUSZUWGUSZUWMXK
      XOUWGUSZUWIUSZUTZYAXKUWFVIVEZUSZXLUWGUSZYAXLUWGUSZUWMUWIUSZUTZVAZYAXKUWFV
      GVEZUSZXLUWGUSZYAUWMUWGUSZUTZUWFVDVEZXLUWGUSZXLUTZUWFVFVEZXLUWGUSZUVMUTZV
      AZVBZBUWJVCZAUWJVCZNUWFVRVEZVCZOUYBVCZVBZUVLLUTZUUBUWHUYEUHUIUWJUWIUVLVRV
      LUVLVIVLUWHUWLUWMUUGUOZXKUUJUWGUSZUWMUWQUUIUSZUTZUXBUXCUWMUUIUSZUTZVAZUXR
      VBZBUUGVCZAUUGVCZNUYBVCZOUYBVCZVBZUUGUWJUTZUUIUWIUTZVBZUYEUWEUYSUGUFUWGUW
      FUVLVKVLUVLVJVLUWEUUDUUHUUNYAXKUWCUSZXLUUEUSZUUSUTZVAZYAXKUWBUSZXLUUEUSZU
      VEUTZUVIUVNVAZVBZBUUGVCAUUGVCZNUWDVCZOUWDVCZVBZUUEUWGUTZUUCUWFUTZVBZUYSUW
      AVUOUMUJUKUWDUWCUWBUUCVRVLUUCVIVLUUCVGVLUVRUWDUTZUUOUWCUTZUVBUWBUTZVAZUVT
      VUNUUDVVBUVSVUMOUVRUWDVUSVUTVVAVMZVVBUVQVULNUVRUWDVVCVVBUVPVUKABUUGUUGVVB
      UVAVUFUVOVUJVVBUUTVUEUUHUUNVVBUUQVUDUUSVVBUUPVUCXLUUEVVBUUOUWCYAXKVUSVUTV
      VAVNVOVPVQVSVVBUVFVUIUVIUVNVVBUVDVUHUVEVVBUVCVUGXLUUEVVBUVBUWBYAXKVUSVUTV
      VAVTVOVPVQWAWBWCWDWDWEWFVURUUDUWLVUNUYRVURUUCUWFUQVUPVUQWHZWGVURVUMUYQOUW
      DUYBVURUUCUWFVRVVDWIZVURVULUYPNUWDUYBVVEVURVUKUYNABUUGUUGVURVUFUYMVUJUXRV
      URUUHUYGUUNUYJVUEUYLVURUUFUWMUUGVURUUEUWGXKXLVUPVUQWJZVOZWGVURUUKUYHUUMUY
      IVURUUEUWGXKUUJVVFVOVURUUFUWMUULUWQUUIVVGVURUUEUWGXKXOVVFVOWKWLVURVUDUXBU
      USUYKVURVUCUXAXLXLUUEUWGVVFVURUWCUWTYAXKVURUUCUWFVIVVDWIVOVURXLWMZWNVURUU
      RUXCUUFUWMUUIVURUUEUWGYAXLVVFVOVVGWKWLWOVURVUIUXKUVIUXNUVNUXQVURVUHUXIUVE
      UXJVURVUGUXHXLXLUUEUWGVVFVURUWBUXGYAXKVURUUCUWFVGVVDWIVOVVHWNVURYAYAUUFUW
      MUUEUWGVVFVURYAWMVVGWNWLVURUVHUXMXLVURUVGUXLXLXLUUEUWGVVFVURUUCUWFVDVVDWI
      VVHWNVQVURUVKUXPUVMVURUVJUXOXLXLUUEUWGVVFVURUUCUWFVFVVDWIVVHWNVQWOWBWCWDW
      DWBWPWQVUBUYRUYDUWLVUBUYPUYAONUYBUYBVUBUYOUXTAUUGUWJUYTVUAWJZVUBUYNUXSBUU
      GUWJVVIVUBUYMUXFUXRVUBUYGUWNUYJUWSUYLUXEVUBUUGUWJUWMVVIWRVUBUYHUWPUYIUWRV
      UBUUJUWOXKUWGVUBUUIUWIXLXOUYTVUAWHZVOWSVUBUUIUWIUWMUWQVVJVOWLVUBUYKUXDUXB
      VUBUUIUWIUXCUWMVVJVOWTWOXAWDWDWCWEWPWQUYFUWLXJUYDUUAUYFUWFHUQUYFUWFLVJVEH
      UVLLVJXHTXBZWGUYFUYCYTOUYBIUYFUYBHVRVEIUYFUWFHVRVVKWIUAXBZUYFUYAYSNUYBIVV
      LUYFUXTYRAUWJKUYFUWJLVRVEKUVLLVRXHPXBZUYFUXSYQBUWJKVVMUYFUXFYGUXRYPUYFUWN
      XNUWSXTUXEYFUYFUWMXMUWJKUYFUWGEXKXLUYFUWGLVKVEEUVLLVKXHRXBZVOZVVMXCUYFUWP
      XQUWRXSUYFXKXKUWOXPUWGEVVNUYFXKWMUYFUWICXLXOUYFUWILVIVECUVLLVIXHQXBZVOWNU
      YFUWMXMUWQXRUWICVVPVVOUYFUWGEXKXOVVNVOWNWLUYFUXBYCUXDYEUYFUXAYBXLXLUWGEVV
      NUYFUWTDYAXKUYFUWTHVIVEDUYFUWFHVIVVKWIUBXBVOUYFXLWMZWNUYFUXCYDUWMXMUWICVV
      PUYFUWGEYAXLVVNVOVVOWNWLWOUYFUXKYKUXNYMUXQYOUYFUXIYIUXJYJUYFUXHYHXLXLUWGE
      VVNUYFUXGFYAXKUYFUXGHVGVEFUYFUWFHVGVVKWIUCXBVOVVQWNUYFYAYAUWMXMUWGEVVNUYF
      YAWMVVOWNWLUYFUXMYLXLUYFUXLGXLXLUWGEVVNUYFUXLHVDVEGUYFUWFHVDVVKWIUDXBVVQW
      NVQUYFUXPYNUVMMUYFUXOJXLXLUWGEVVNUYFUXOHVFVEJUYFUWFHVFVVKWIUEXBVVQWNUYFUV
      MLVFVEMUVLLVFXHSXBWLWOWBWDWDWDWDWBWPABUHUKUFULUMUGNOUJUIXDXEXIXJUUAXFXG
      $.


    $( Lemma for properties of a semimodule.  (Contributed by NM, 8-Dec-2013.)
       (Revised by Mario Carneiro, 19-Jun-2014.)  (Revised by Thierry Arnoux,
       1-Apr-2018.) $)
    slmdlema $p |- ( ( W e. SLMod /\ ( Q e. K /\ R e. K )
          /\ ( X e. V /\ Y e. V ) ) ->
                ( ( ( R .x. Y ) e. V
                 /\ ( R .x. ( Y .+ X ) ) = ( ( R .x. Y ) .+ ( R .x. X ) )
                 /\ ( ( Q .+^ R ) .x. Y ) = ( ( Q .x. Y ) .+ ( R .x. Y ) )
               ) /\ ( ( ( Q .X. R ) .x. Y ) = ( Q .x. ( R .x. Y ) )
                 /\ ( .1. .x. Y ) = Y 
                 /\ ( O .x. Y ) = .0. ) ) ) $=
      ( vw vx vr vq cslmd wcel wa co wceq w3a cv wral ccmn isslmd simp3bi oveq1
      csrg oveq1d eqeq12d 3anbi3d 3anbi1d anbi12d 2ralbidv eleq1d oveq12d oveq2
      oveq2d 3anbi123d biidd 3anbi13d rspc2v mpan9 3anbi2d anbi1d eqeq1d 3impia
      id syl5com ) LUJUKZCIUKDIUKULZMKUKNKUKULZDNEUMZKUKZDNMAUMZEUMZWGDMEUMZAUM
      ZUNZCDBUMZNEUMZCNEUMZWGAUMZUNZUOZCDFUMZNEUMZCWGEUMZUNZGNEUMZNUNZJNEUMZOUN
      ZUOZULZWDWEULDUFUPZEUMZKUKZDXJUGUPZAUMZEUMZXKDXMEUMZAUMZUNZWNXJEUMZCXJEUM
      ZXKAUMZUNZUOZWTXJEUMZCXKEUMZUNZGXJEUMZXJUNZJXJEUMZOUNZUOZULZUFKUQUGKUQZWF
      XIWDUHUPZXJEUMZKUKZYNXNEUMZYOYNXMEUMZAUMZUNZUIUPZYNBUMZXJEUMZUUAXJEUMZYOA
      UMZUNZUOZUUAYNFUMZXJEUMZUUAYOEUMZUNZYHYJUOZULZUFKUQUGKUQZUHIUQUIIUQZWEYMW
      DLURUKHVBUKUUOUGUFABEFGHIJKLOUHUIPQRSTUAUBUCUDUEUSUTUUNYMYPYTCYNBUMZXJEUM
      ZXTYOAUMZUNZUOZCYNFUMZXJEUMZCYOEUMZUNZYHYJUOZULZUFKUQUGKUQUIUHCDIIUUACUNZ
      UUMUVFUGUFKKUVGUUGUUTUULUVEUVGUUFUUSYPYTUVGUUCUUQUUEUURUVGUUBUUPXJEUUACYN
      BVAVCUVGUUDXTYOAUUACXJEVAVCVDVEUVGUUKUVDYHYJUVGUUIUVBUUJUVCUVGUUHUVAXJEUU
      ACYNFVAVCUUACYOEVAVDVFVGVHYNDUNZUVFYLUGUFKKUVHUUTYCUVEYKUVHYPXLYTXRUUSYBU
      VHYOXKKYNDXJEVAZVIUVHYQXOYSXQYNDXNEVAUVHYOXKYRXPAUVIYNDXMEVAVJVDUVHUUQXSU
      URYAUVHUUPWNXJEYNDCBVKVCUVHYOXKXTAUVIVLVDVMUVHUVDYFYJYJYHUVHUVBYDUVCYEUVH
      UVAWTXJEYNDCFVKVCUVHYOXKCEUVIVLVDUVHYJVNVOVGVHVPVQYLXIXLDXJMAUMZEUMZXKWKA
      UMZUNZYBUOZYKULUGUFMNKKXMMUNZYCUVNYKUVOXRUVMXLYBUVOXOUVKXQUVLUVOXNUVJDEXM
      MXJAVKVLUVOXPWKXKAXMMDEVKVLVDVRVSXJNUNZUVNWSYKXHUVPXLWHUVMWMYBWRUVPXKWGKX
      JNDEVKZVIUVPUVKWJUVLWLUVPUVJWIDEXJNMAVAVLUVPXKWGWKAUVQVCVDUVPXSWOYAWQXJNW
      NEVKUVPXTWPXKWGAXJNCEVKUVQVJVDVMUVPYFXCYHXEYJXGUVPYDXAYEXBXJNWTEVKUVPXKWG
      CEUVQVLVDUVPYGXDXJNXJNGEVKUVPWBVDUVPYIXFOXJNJEVKVTVMVGVPWCWA $.
  $}
  
  ${
    $d a f g k p q r s v w x F $.  $d a f g k p q r s v w x K $.
    $d q r w x Q $.  $d r w x R $.  $d a f g k p q r s v w x V $.
    $d a f g q r v w x W $.  $d w x X $.  $d w Y $.
    $d a f g k p q r s t v w x .X. $.  $d a f g k p q r s v w x .+ $.
    $d a f g k p q r s v w x .+^ $.  $d a f g k p q r s v w x .1. $.
    $d a f g k p q r s v w x .x. $.
    $( Left semimodules generalize the notion of left modules.  (Contributed by
       Thierry Arnoux, 1-Apr-2018.) $)
    lmodslmd $p |- ( W e. LMod -> W e. SLMod ) $=
      ( vr vw vx vq wcel cfv cv co cbs cplusg wceq w3a c0g wral r19.21bi simpld
      wa eqid ralrimiva clmod ccmn csca csrg cvsca cmulr cur cslmd lmodcmn cgrp
      crg islmod simp2bi rngsrg syl simp3bi simprd simp-4l lmod0vs syl2anc 3jca
      simpr jca isslmd syl3anbrc ) AUAFZAUBFAUCGZUDFZBHZCHZAUEGZIZAJGZFVIVJDHZA
      KGZIVKIVLVIVNVKIVOILEHZVIVGKGZIVJVKIVPVJVKIVLVOILMZVPVIVGUFGZIVJVKIVPVLVK
      ILZVGUGGZVJVKIVJLZVGNGZVJVKIANGZLZMZRZCVMOZDVMOZBVGJGZOZEWJOAUHFAUIVFVGUK
      FZVHVFAUJFZWLVRVTWBRZRZCVMOZDVMOZBWJOZEWJOZDCVOVQVKVSWAVGWJVMABEVMSZVOSZV
      KSZVGSZWJSZVQSZVSSZWASZULZUMVGUNUOVFWKEWJVFVPWJFZRZWIBWJXJVIWJFZRZWHDVMXL
      VNVMFZRZWGCVMXNVJVMFZRZVRWFXPVRWNXNWOCVMXLWPDVMXJWQBWJVFWREWJVFWMWLWSXHUP
      PPPPZQXPVTWBWEXPVTWBXPVRWNXQUQZQXPVTWBXRUQXPVFXOWEVFXIXKXMXOURXNXOVBVKVGW
      CVMAVJWDWTXCXBWCSZWDSZUSUTVAVCTTTTDCVOVQVKVSWAVGWJWCVMAWDBEWTXAXBXTXCXDXE
      XFXGXSVDVE $.
  $}

  ${
    $d q r w x y z F $.  $d q r w x y z W $.
    $( A semimodule is a commutative monoid.  (Contributed by Thierry Arnoux,
       1-Apr-2018.) $)
    slmdcmn $p |- ( W e. SLMod -> W e. CMnd ) $=
      ( vz vy vx vw cslmd wcel ccmn csca cfv csrg cv co cbs cplusg wceq w3a c0g
      wral eqid cvsca cmulr cur wa isslmd simp1bi ) AFGAHGAIJZKGBLZCLZAUAJZMZAN
      JZGUHUIDLZAOJZMUJMUKUHUMUJMUNMPELZUHUGOJZMUIUJMUOUIUJMUKUNMPQUOUHUGUBJZMU
      IUJMUOUKUJMPUGUCJZUIUJMUIPUGRJZUIUJMARJZPQUDCULSDULSBUGNJZSEVASDCUNUPUJUQ
      URUGVAUSULAUTBEULTUNTUJTUTTUGTVATUPTUQTURTUSTUEUF $.

    $( A semimodule is a monoid.  (Contributed by Thierry Arnoux, 1-Apr-2018.)
       $)
    slmdmnd $p |- ( W e. SLMod -> W e. Mnd ) $=
      ( cslmd wcel ccmn cmnd slmdcmn cmnmnd syl ) ABCADCAECAFAGH $.

    slmdsrg.1 $e |- F = ( Scalar ` W ) $.
    $( The scalar component of a semimodule is a semiring.  (Contributed by NM,
       8-Dec-2013.)  (Revised by Mario Carneiro, 19-Jun-2014.)  (Revised by
       Thierry Arnoux, 1-Apr-2018.) $)
    slmdsrg $p |- ( W e. SLMod -> F e. SRing ) $=
      ( vz vy vx vw cslmd wcel ccmn cv cfv co cbs cplusg wceq w3a c0g wral eqid
      csrg cvsca cmulr cur wa isslmd simp2bi ) BHIBJIAUAIDKZEKZBUBLZMZBNLZIUHUI
      FKZBOLZMUJMUKUHUMUJMUNMPGKZUHAOLZMUIUJMUOUIUJMUKUNMPQUOUHAUCLZMUIUJMUOUKU
      JMPAUDLZUIUJMUIPARLZUIUJMBRLZPQUEEULSFULSDANLZSGVASFEUNUPUJUQURAVAUSULBUT
      DGULTUNTUJTUTTCVATUPTUQTURTUSTUFUG $.
  $}

  ${
    slmdbn0.b $e |- B = ( Base ` W ) $.
    $( The base set of a semimodule is nonempty.  (Contributed by Thierry 
       Arnoux, 1-Apr-2018.) $)
    slmdbn0 $p |- ( W e. SLMod -> B =/= (/) ) $=
      ( cslmd wcel cmnd c0g cfv c0 wne slmdmnd eqid mndidcl ne0i 3syl ) BDEBFEB
      GHZAEAIJBKABPCPLMAPNO $.
  $}

  ${
    slmdacl.f $e |- F = ( Scalar ` W ) $.
    slmdacl.k $e |- K = ( Base ` F ) $.
    slmdacl.p $e |- .+ = ( +g ` F ) $.
    $( Closure of ring addition for a semimodule.  (Contributed by Thierry
       Arnoux, 1-Apr-2018.) $)
    slmdacl $p |- ( ( W e. SLMod /\ X e. K /\ Y e. K ) -> ( X .+ Y ) e. K ) $=
      ( cslmd wcel cmnd co csrg slmdsrg srgmnd syl mndcl syl3an1 ) DJKZBLKZECKF
      CKEFAMCKTBNKUABDGOBPQCABEFHIRS $.
  $}

  ${
    slmdmcl.f $e |- F = ( Scalar ` W ) $.
    slmdmcl.k $e |- K = ( Base ` F ) $.
    slmdmcl.t $e |- .x. = ( .r ` F ) $.
    $( Closure of ring multiplication for a semimodule.  (Contributed by NM,
       14-Jan-2014.)  (Revised by Mario Carneiro, 19-Jun-2014.)  (Revised by
       Thierry Arnoux, 1-Apr-2018.) $)
    slmdmcl $p |- ( ( W e. SLMod /\ X e. K /\ Y e. K ) -> ( X .x. Y ) e. K ) $=
      ( cslmd wcel csrg co slmdsrg srgcl syl3an1 ) DJKBLKECKFCKEFAMCKBDGNCBAEFH
      IOP $.
  $}

  ${
    slmdsn0.f $e |- F = ( Scalar ` W ) $.
    slmdsn0.b $e |- B = ( Base ` F ) $.
    $( The set of scalars in a semimodule is nonempty.  (Contributed by Thierry
       Arnoux, 1-Apr-2018.) $)
    slmdsn0 $p |- ( W e. SLMod -> B =/= (/) ) $=
      ( wcel c0g cfv c0 wne csrg cmnd slmdsrg srgmnd eqid mndidcl 3syl ne0i syl
      cslmd ) CTFZBGHZAFZAIJUABKFBLFUCBCDMBNABUBEUBOPQAUBRS $.
  $}

  ${
    slmdvacl.v $e |- V = ( Base ` W ) $.
    slmdvacl.a $e |- .+ = ( +g ` W ) $.
    $( Closure of vector addition for a semiring left module.  (Contributed by
       NM, 8-Dec-2013.)  (Revised by Mario Carneiro, 19-Jun-2014.)  (Revised by
       Thierry Arnoux, 1-Apr-2018.) $)
    slmdvacl $p |- ( ( W e. SLMod /\ X e. V /\ Y e. V ) -> ( X .+ Y ) e. V ) $=
      ( cslmd wcel cmnd co slmdmnd mndcl syl3an1 ) CHICJIDBIEBIDEAKBICLBACDEFGM
      N $.

    $( Semiring left module vector sum is associative.  (Contributed by NM,
       10-Jan-2014.)  (Revised by Mario Carneiro, 19-Jun-2014.)  (Revised by
       Thierry Arnoux, 1-Apr-2018.) $)
    slmdass $p |- ( ( W e. SLMod /\ ( X e. V /\ Y e. V /\ Z e. V ) ) ->
                    ( ( X .+ Y ) .+ Z ) = ( X .+ ( Y .+ Z ) ) ) $=
      ( cslmd wcel cmnd w3a co wceq slmdmnd mndass sylan ) CIJCKJDBJEBJFBJLDEAM
      FAMDEFAMAMNCOBACDEFGHPQ $.
  $}

  ${
    slmdvscl.v $e |- V = ( Base ` W ) $.
    slmdvscl.f $e |- F = ( Scalar ` W ) $.
    slmdvscl.s $e |- .x. = ( .s ` W ) $.
    slmdvscl.k $e |- K = ( Base ` F ) $.
    $( Closure of scalar product for a semiring left module.  ( ~ hvmulcl
       analog.)  (Contributed by NM, 8-Dec-2013.)  (Revised by Mario Carneiro,
       19-Jun-2014.)  (Revised by Thierry Arnoux, 1-Apr-2018.) $)
    slmdvscl $p |- ( ( W e. SLMod /\ R e. K /\ X e. V ) -> ( R .x. X ) e. V ) $=
      ( wcel wa co pm4.24 w3a cplusg cfv wceq eqid cslmd cmulr cur c0g slmdlema
      biid simpld simp1d syl3anb ) FUALZUJADLZUKUKMZGELZUMUMMZAGBNZELZUJUFUKOUM
      OUJULUNPZUPAGGFQRZNBNUOUOURNZSZAACQRZNGBNUSSZUQUPUTVBPAACUBRZNGBNAUOBNSCU
      CRZGBNGSCUDRZGBNFUDRZSPURVAAABVCVDCDVEEFGGVFHURTJVFTIKVATVCTVDTVETUEUGUHU
      I $.
  $}

  ${
    slmdvsdi.v $e |- V = ( Base ` W ) $.
    slmdvsdi.a $e |- .+ = ( +g ` W ) $.
    slmdvsdi.f $e |- F = ( Scalar ` W ) $.
    slmdvsdi.s $e |- .x. = ( .s ` W ) $.
    slmdvsdi.k $e |- K = ( Base ` F ) $.
    $( Distributive law for scalar product.  ( ~ ax-hvdistr1 analog.)
       (Contributed by NM, 10-Jan-2014.)  (Revised by Mario Carneiro,
       22-Sep-2015.)  (Revised by Thierry Arnoux, 1-Apr-2018.) $)
    slmdvsdi $p |- ( ( W e. SLMod /\ ( R e. K /\ X e. V /\ Y e. V ) ) ->
                     ( R .x. ( X .+ Y ) ) = ( ( R .x. X ) .+ ( R .x. Y ) ) ) $=
      ( wcel co wceq w3a cfv eqid cslmd wa cplusg cmulr cur c0g slmdlema simpld
      wi simp2d 3expia anabsan2 exp4b com34 3imp2 ) GUAOZBEOZHFOZIFOZBHIAPCPBHC
      PZBICPAPQZUPUQUSURVAUPUQUSURVAUPUQUSURUBZVAUIUPUQUQUBZVBVAUPVCVBRZUTFOZVA
      BBDUCSZPHCPUTUTAPQZVDVEVAVGRBBDUDSZPHCPBUTCPQDUESZHCPHQDUFSZHCPGUFSZQRAVF
      BBCVHVIDEVJFGIHVKJKMVKTLNVFTVHTVITVJTUGUHUJUKULUMUNUO $.
  $}

  ${
    slmdvsdir.v $e |- V = ( Base ` W ) $.
    slmdvsdir.a $e |- .+ = ( +g ` W ) $.
    slmdvsdir.f $e |- F = ( Scalar ` W ) $.
    slmdvsdir.s $e |- .x. = ( .s ` W ) $.
    slmdvsdir.k $e |- K = ( Base ` F ) $.
    slmdvsdir.p $e |- .+^ = ( +g ` F ) $.
    $( Distributive law for scalar product.  ( ~ ax-hvdistr1 analog.)
       (Contributed by NM, 10-Jan-2014.)  (Revised by Mario Carneiro,
       22-Sep-2015.)  (Revised by Thierry Arnoux, 1-Apr-2018.) $)
    slmdvsdir $p |- ( ( W e. SLMod /\ ( Q e. K /\ R e. K /\ X e. V ) ) ->
                    ( ( Q .+^ R ) .x. X ) = ( ( Q .x. X ) .+ ( R .x. X ) ) ) $=
      ( wcel co wceq cfv cslmd wa w3a cmulr cur c0g eqid slmdlema simpld simp3d
      3expa anabsan2 exp42 3imp2 ) IUAQZCGQZDGQZJHQZCDBRJERCJERDJERZARSZUOUPUQU
      RUTUOUPUQUBZUBURUTUOVAURURUBZUTUOVAVBUCZUSHQZDJJARERUSUSARSZUTVCVDVEUTUCC
      DFUDTZRJERCUSERSFUETZJERJSFUFTZJERIUFTZSUCABCDEVFVGFGVHHIJJVIKLNVIUGMOPVF
      UGVGUGVHUGUHUIUJUKULUMUN $.

  $}


  ${
    slmdvsass.v $e |- V = ( Base ` W ) $.
    slmdvsass.f $e |- F = ( Scalar ` W ) $.
    slmdvsass.s $e |- .x. = ( .s ` W ) $.
    slmdvsass.k $e |- K = ( Base ` F ) $.
    slmdvsass.t $e |- .X. = ( .r ` F ) $.
    $( Associative law for scalar product.  ( ~ ax-hvmulass analog.)
       (Contributed by NM, 10-Jan-2014.)  (Revised by Mario Carneiro,
       22-Sep-2015.)  (Revised by Thierry Arnoux, 1-Apr-2018.) $)
    slmdvsass $p |- ( ( W e. SLMod /\ ( Q e. K /\ R e. K /\ X e. V ) ) ->
                      ( ( Q .X. R ) .x. X ) = ( Q .x. ( R .x. X ) ) ) $=
      ( wcel co wceq wa cfv eqid cslmd w3a cur c0g cplusg slmdlema simprd 3expa
      simp1d anabsan2 exp42 3imp2 ) HUAOZAFOZBFOZIGOZABDPICPABICPZCPQZUMUNUOUPU
      RUMUNUORZRUPURUMUSUPUPRZURUMUSUTUBZUREUCSZICPIQZEUDSZICPHUDSZQZVAUQGOBIIH
      UESZPCPUQUQVGPQABEUESZPICPAICPUQVGPQUBURVCVFUBVGVHABCDVBEFVDGHIIVEJVGTLVE
      TKMVHTNVBTVDTUFUGUIUHUJUKUL $.
  $}

  ${
    slmd0cl.f $e |- F = ( Scalar ` W ) $.
    slmd0cl.k $e |- K = ( Base ` F ) $.
    slmd0cl.z $e |- .0. = ( 0g ` F ) $.
    $( The ring zero in a semimodule belongs to the ring base set.
       (Contributed by NM, 11-Jan-2014.)  (Revised by Mario Carneiro,
       19-Jun-2014.)  (Revised by Thierry Arnoux, 1-Apr-2018.) $)
    slmd0cl $p |- ( W e. SLMod -> .0. e. K ) $=
      ( cslmd wcel csrg slmdsrg srg0cl syl ) CHIAJIDBIACEKBADFGLM $.
  $}

  ${
    slmd1cl.f $e |- F = ( Scalar ` W ) $.
    slmd1cl.k $e |- K = ( Base ` F ) $.
    slmd1cl.u $e |- .1. = ( 1r ` F ) $.
    $( The ring unit in a semiring left module belongs to the ring base set.
       (Contributed by NM, 11-Jan-2014.)  (Revised by Mario Carneiro,
       19-Jun-2014.)  (Revised by Thierry Arnoux, 1-Apr-2018.) $)
    slmd1cl $p |- ( W e. SLMod -> .1. e. K ) $=
      ( cslmd wcel csrg slmdsrg srgidcl syl ) DHIBJIACIBDEKCBAFGLM $.
  $}

  ${
    slmdvs1.v $e |- V = ( Base ` W ) $.
    slmdvs1.f $e |- F = ( Scalar ` W ) $.
    slmdvs1.s $e |- .x. = ( .s ` W ) $.
    slmdvs1.u $e |- .1. = ( 1r ` F ) $.
    $( Scalar product with ring unit.  ( ~ ax-hvmulid analog.)  (Contributed by
       NM, 10-Jan-2014.)  (Revised by Mario Carneiro, 19-Jun-2014.)  (Revised
       by Thierry Arnoux, 1-Apr-2018.) $)
    slmdvs1 $p |- ( ( W e. SLMod /\ X e. V ) -> ( .1. .x. X ) = X ) $=
      ( cslmd wcel wa cfv co wceq eqid w3a c0g cplusg simpl slmd1cl simpr cmulr
      cbs adantr slmdlema simprd simp2d syl122anc ) EKLZFDLZMUKBCUENZLZUNULULBF
      AOZFPZUKULUAUKUNULBCUMEHUMQZJUBUFZURUKULUCZUSUKUNUNMULULMRZBBCUDNZOFAOBUO
      AOPZUPCSNZFAOESNZPZUTUODLBFFETNZOAOUOUOVFOZPBBCTNZOFAOVGPRVBUPVERVFVHBBAV
      ABCUMVCDEFFVDGVFQIVDQHUQVHQVAQJVCQUGUHUIUJ $.
  $}

  ${
    slmd0vcl.v $e |- V = ( Base ` W ) $.
    slmd0vcl.z $e |- .0. = ( 0g ` W ) $.
    $( The zero vector is a vector.  ( ~ ax-hv0cl analog.)  (Contributed by NM,
       10-Jan-2014.)  (Revised by Mario Carneiro, 19-Jun-2014.)  (Revised by
       Thierry Arnoux, 1-Apr-2018.) $)
    slmd0vcl $p |- ( W e. SLMod -> .0. e. V ) $=
      ( cslmd wcel cmnd slmdmnd mndidcl syl ) BFGBHGCAGBIABCDEJK $.
  $}

  ${
    slmd0vlid.v $e |- V = ( Base ` W ) $.
    slmd0vlid.a $e |- .+ = ( +g ` W ) $.
    slmd0vlid.z $e |- .0. = ( 0g ` W ) $.
    $( Left identity law for the zero vector.  ( ~ hvaddid2 analog.)
       (Contributed by NM, 10-Jan-2014.)  (Revised by Mario Carneiro,
       19-Jun-2014.)  (Revised by Thierry Arnoux, 1-Apr-2018.) $)
    slmd0vlid $p |- ( ( W e. SLMod /\ X e. V ) -> ( .0. .+ X ) = X ) $=
      ( cslmd wcel cmnd co wceq slmdmnd mndlid sylan ) CIJCKJDBJEDALDMCNBACDEFG
      HOP $.

    $( Right identity law for the zero vector.  ( ~ ax-hvaddid analog.)
       (Contributed by NM, 10-Jan-2014.)  (Revised by Mario Carneiro,
       19-Jun-2014.)  (Revised by Thierry Arnoux, 1-Apr-2018.) $)
    slmd0vrid $p |- ( ( W e. SLMod /\ X e. V ) -> ( X .+ .0. ) = X ) $=
      ( cslmd wcel cmnd co wceq slmdmnd mndrid sylan ) CIJCKJDBJDEALDMCNBACDEFG
      HOP $.
  $}

  ${
    slmd0vs.v $e |- V = ( Base ` W ) $.
    slmd0vs.f $e |- F = ( Scalar ` W ) $.
    slmd0vs.s $e |- .x. = ( .s ` W ) $.
    slmd0vs.o $e |- O = ( 0g ` F ) $.
    slmd0vs.z $e |- .0. = ( 0g ` W ) $.
    $( Zero times a vector is the zero vector.  Equation 1a of [Kreyszig]
       p. 51.  ( ~ ax-hvmul0 analog.)  (Contributed by NM, 12-Jan-2014.)
       (Revised by Mario Carneiro, 19-Jun-2014.)  (Revised by Thierry Arnoux,
       1-Apr-2018.) $)
    slmd0vs $p |- ( ( W e. SLMod /\ X e. V ) -> ( O .x. X ) = .0. ) $=
      ( wcel wa cfv co wceq cplusg w3a eqid cslmd cmulr cur simpl slmd0cl simpr
      cbs syl slmdlema syl122anc simprd simp3d ) EUAMZFDMZNZCCBUBOZPFAPCCFAPZAP
      QZBUCOZFAPFQZUQGQZUOUQDMCFFEROZPAPUQUQVBPZQCCBROZPFAPVCQSZURUTVASZUOUMCBU
      GOZMZVHUNUNVEVFNUMUNUDZUOUMVHVIBVGECIVGTZKUEUHZVKUMUNUFZVLVBVDCCAUPUSBVGC
      DEFFGHVBTJLIVJVDTUPTUSTKUIUJUKUL $.
  $}

  ${
    slmdvs0.f $e |- F = ( Scalar ` W ) $.
    slmdvs0.s $e |- .x. = ( .s ` W ) $.
    slmdvs0.k $e |- K = ( Base ` F ) $.
    slmdvs0.z $e |- .0. = ( 0g ` W ) $.
    $( Anything times the zero vector is the zero vector.  Equation 1b of
       [Kreyszig] p. 51.  ( ~ hvmul0 analog.)  (Contributed by NM,
       12-Jan-2014.)  (Revised by Mario Carneiro, 19-Jun-2014.)  (Revised by
       Thierry Arnoux, 1-Apr-2018.) $)
    slmdvs0 $p |- ( ( W e. SLMod /\ X e. K ) -> ( X .x. .0. ) = .0. ) $=
      ( cslmd wcel wa c0g cfv cmulr co wceq eqid adantr csrg srgrz sylan oveq1d
      slmdsrg cbs simpl simpr srg0cl slmd0vcl slmdvsass syl13anc slmd0vs syldan
      syl oveq2d eqtrd 3eqtr3d ) DKLZECLZMZEBNOZBPOZQZFAQZVBFAQZEFAQZFVAVDVBFAU
      SBUALZUTVDVBRBDGUEZCBVCEVBIVCSZVBSZUBUCUDVAVEEVFAQZVGVAUSUTVBCLZFDUFOZLZV
      EVLRUSUTUGUSUTUHVAVHVMUSVHUTVITCBVBIVKUIUOUSVOUTVNDFVNSZJUJTZEVBAVCBCVNDF
      VPGHIVJUKULVAVFFEAUSUTVOVFFRVQABVBVNDFFVPGHVKJUMUNZUPUQVRUR $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Finitely supported group sums - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d k A $.  $d k B $.  $d k D $.  $d k E $.  $d k ph $.  $d k V $.
    $d k W $.
    sumpr.1 $e |- ( k = A -> C = D ) $.
    sumpr.2 $e |- ( k = B -> C = E ) $.
    sumpr.3 $e |- ( ph -> ( D e. CC /\ E e. CC ) ) $.
    sumpr.4 $e |- ( ph -> ( A e. V /\ B e. W ) ) $.
    sumpr.5 $e |- ( ph -> A =/= B ) $.
    $( A sum over a pair is the sum of the elements.  (Contributed by Thierry
       Arnoux, 12-Dec-2016.) $)
    sumpr $p |- ( ph -> sum_ k e. { A , B } C = ( D + E ) ) $=
      ( csu csn caddc wceq wcel cc cpr co wne cin disjsn2 syl cun df-pr a1i cfn
      c0 prfi wral wa wb eleq1d ralprg mpbird r19.21bi fsumsplit simpld syl2anc
      cv sumsn simprd oveq12d eqtrd ) ABCUAZDFOBPZDFOZCPZDFOZQUBEGQUBAVIVKDVHFA
      BCUCVIVKUDUKRNBCUEUFVHVIVKUGRABCUHUIVHUJSABCULUIADTSZFVHAVMFVHUMZETSZGTSZ
      UNZLABHSZCISZUNVNVQUOMVMVOVPFBCHIFVCZBRDETJUPVTCRDGTKUPUQUFURUSUTAVJEVLGQ
      AVRVOVJERAVRVSMVAAVOVPLVADEFBHJVDVBAVSVPVLGRAVRVSMVEAVOVPLVEDGFCIKVDVBVFV
      G $.
  $}

  ${
    $d k B $.  $d k C $.  $d k G $.  $d k M $.  $d k ph $.
    gsumsn2.b $e |- B = ( Base ` G ) $.
    gsumsn2.g $e |- G e. Mnd $.
    gsumsn2.s $e |- ( ( ph /\ k = M ) -> A = C ) $.
    gsumsn2.m $e |- ( ph -> M e. V ) $.
    gsumsn2.c $e |- ( ph -> C e. B ) $.
    $( Group sum of a singleton.  (Contributed by Thierry Arnoux,
       30-Jan-2017.) $)
    gsumsn2 $p |- ( ph -> ( G gsum ( k e. { M } |-> A ) ) = C ) $=
      ( cmpt cgsu co cfv c1 wcel wceq csn chash cmg elsni sylan2 mpteq2dva cmnd
      oveq2d cfn a1i snfi eqid gsumconst syl3anc eqtrd hashsng syl oveq1d mulg1
      cv 3eqtrd ) AFEGUAZBNZOPZVBUBQZDFUCQZPZRDVFPZDAVDFEVBDNZOPZVGAVCVIFOAEVBB
      DEUTZVBSAVKGTBDTVKGUDKUEUFUHAFUGSZVBUISZDCSZVJVGTVLAJUJVMAGUKUJMVBCVFEFDI
      VFULZUMUNUOAVERDVFAGHSVERTLGHUPUQURAVNVHDTMCVFFDIVOUSUQVA $.
  $}

  ${
    $d a b A $.  $d a b B $.  $d a b f m n s t x F $.  $d a b f m n s t x G $.
    $d a b f m n s t x H $.  $d a b f m n s t x ph $.
    gsumpropd2.f $e |- ( ph -> F e. V ) $.
    gsumpropd2.g $e |- ( ph -> G e. W ) $.
    gsumpropd2.h $e |- ( ph -> H e. X ) $.
    gsumpropd2.b $e |- ( ph -> ( Base ` G ) = ( Base ` H ) ) $.
    gsumpropd2.c $e |- ( ( ph /\ ( s e. ( Base ` G ) /\ t e. ( Base ` G ) ) )
                                -> ( s ( +g ` G ) t ) e. ( Base ` G ) ) $.
    gsumpropd2.e $e |- ( ( ph /\ ( s e. ( Base ` G ) /\ t e. ( Base ` G ) ) )
                                -> ( s ( +g ` G ) t ) = ( s ( +g ` H ) t ) ) $.
    gsumpropd2.n $e |- ( ph -> Fun F ) $.
    gsumpropd2.r $e |- ( ph -> ran F C_ ( Base ` G ) ) $.
    ${
      gsumprop2dlem.1 $e |- A = ( `' F " ( _V \ { s e. ( Base ` G ) | A. t e. (
       Base ` G ) ( ( s ( +g ` G ) t ) = t /\ ( t ( +g ` G ) s ) = t ) } ) ) $.
      gsumprop2dlem.2 $e |- B = ( `' F " ( _V \ { s e. ( Base ` H ) | A. t e. (
       Base ` H ) ( ( s ( +g ` H ) t ) = t /\ ( t ( +g ` H ) s ) = t ) } ) ) $.
      $( Lemma for ~ gsumpropd2 (Contributed by Thierry Arnoux,
         28-Jun-2017.) $)
      gsumpropd2lem $p |- ( ph -> ( G gsum F ) = ( H gsum F ) ) $=
        ( vm vn vx vf va vb crn cv cplusg cfv co wceq cbs wral crab wss c0g cdm
        wa cfz wcel cseq cuz wrex wex cio c1 chash wf1o ccom cif cgsu adantr wb
        eqeq1d proplem ancom2s anbi12d anassrs raleqbidva rabeqbidva grpidpropd
        sseq2d eqidd simprl ad2antrr wfun simpr simplrr eleqtrrd fvelrn syl2anc
        sseldd adantlr seqfeq4 eqeq2d pm5.32da rexbidva iotabidv ccnv cdif cima
        exbidv cvv difeq2d imaeq2d 3eqtr4g fveq2d ad3antrrr f1ofun f1odm oveq2d
        ad3antlr eqtrd fvco difpreima syl syl5eq difss syl6eqss dfdm4 syl6sseqr
        dfrn4 eqtri sylan wn c0 wfn 1z seqfn fndm mp2b sylnibr ndmfv bitrd eqid
        eleq2i a1i gsumvalx wf ffvelrnd eqeltrd simpll caovclg eqtr4d pm2.61dan
        f1of cz f1oeq2 f1oeq3 anbi1d ifeq12d ifbieq12d 3eqtr4d ) AEUHZKUIZBUIZF
        UJUKZULZUURUMZUURUUQUUSULZUURUMZUTZBFUNUKZUOZKUVEUPZUQZFURUKZEUSZVAUHVB
        ZUVJUBUIZUCUIZVAULZUMZUDUIZUVMUUSEUVLVCUKZUMZUTZUCUVLVDUKZVEZUBVFZUDVGZ
        VHCVIUKZVAULZCUEUIZVJZUVPUWDUUSEUWFVKZVHVCZUKZUMZUTZUEVFZUDVGZVLZVLUUPU
        UQUURGUJUKZULZUURUMZUURUUQUWPULZUURUMZUTZBGUNUKZUOZKUXBUPZUQZGURUKZUVKU
        VOUVPUVMUWPEUVLVCUKZUMZUTZUCUVTVEZUBVFZUDVGZVHDVIUKZVAULZDUWFVJZUVPUXMU
        WPUWHVHVCZUKZUMZUTZUEVFZUDVGZVLZVLFEVMULGEVMULAUVHUXEUVIUWOUXFUYBAUVGUX
        DUUPAUVFUXCKUVEUXBOAUUQUVEVBZUTUVDUXABUVEUXBAUVEUXBUMUYCOVNAUYCUURUVEVB
        ZUVDUXAVOAUYCUYDUTZUTZUVAUWRUVCUWTUYFUUTUWQUURQVPUYFUVBUWSUURAUYDUYCUVB
        UWSUMAUFUGUVEUVEUUSUWPUURUUQAKBUVEUVEUUSUWPUFUIZUGUIZQVQZVQVRVPVSVTWAWB
        ZWDAKBUVEFGAUVEWEOQWCAUVKUWCUXLUWNUYAAUWBUXKUDAUWAUXJUBAUVSUXIUCUVTAUVM
        UVTVBZUTUVOUVRUXHAUYKUVOUVRUXHVOAUYKUVOUTZUTZUVQUXGUVPUYMKBUUSUWPUVEEUV
        LUVMAUYKUVOWFUYMUUQUVNVBZUTZUUPUVEUUQEUKZAUUPUVEUQZUYLUYNSWGUYOEWHZUUQU
        VJVBUYPUUPVBAUYRUYLUYNRWGUYOUUQUVNUVJUYMUYNWIAUYKUVOUYNWJWKUUQEWLWMWNAU
        YEUUTUVEVBUYLPWOAUYEUUTUWQUMUYLQWOWPWQVTWRWSXDWTAUWMUXTUDAUWLUXSUEAUWLU
        WGUXRUTUXSAUWGUWKUXRAUWGUTZUWJUXQUVPUYSUWJUXMUWIUKZUXQAUWJUYTUMUWGAUWDU
        XMUWIACDVIAEXAZXEUVGXBZXCZVUAXEUXDXBZXCZCDAVUBVUDVUAAUVGUXDXEUYJXFXGTUA
        XHZXIZXIVNUYSUXMVHVDUKZVBZUYTUXQUMZUYSVUIUTZUFUGUUSUWPUVEUWHVHUXMUYSVUI
        WIVUKUYGUXNVBZUTZUUPUVEUYGUWHUKZAUYQUWGVUIVULSXJVUMVUNUYGUWFUKZEUKZUUPV
        UMUWFWHZUYGUWFUSZVBVUNVUPUMUWGVUQAVUIVULUWECUWFXKXNVUMUYGUXNVURVUKVULWI
        ZVUMVURUWEUXNUWGVURUWEUMAVUIVULUWECUWFXLXNAUWEUXNUMZUWGVUIVULAUWDUXMVHV
        AVUGXMZXJZXOWKUYGEUWFXPWMVUMUYRVUOUVJVBVUPUUPVBAUYRUWGVUIVULRXJVUMCUVJV
        UOACUVJUQUWGVUIVULACVUAXEXCZUVJACVVCVUAUVGXCZXBZVVCACVUCVVETAUYRVUCVVEU
        MRXEUVGEXQXRXSVVCVVDXTYAUVJVUAUHVVCEYBVUAYDYEYCXJVUMUWECUYGUWFUWGUWECUW
        FUUAAVUIVULUWECUWFUUHXNVUMUYGUXNUWEVUSVVBWKUUBWNVUOEWLWMUUCWNVUKAUYGUVE
        VBUYHUVEVBUTZUYGUYHUUSULZUVEVBAUWGVUIUUDZAKBUYGUYHUVEUVEUVEUUSPUUEYFVUK
        AVVFVVGUYGUYHUWPULUMVVHUYIYFWPAVUIYGZVUJUWGAVVIUTZUYTYHUXQVVJUXMUWIUSZV
        BZYGUYTYHUMVVJVUIVVLAVVIWIZVVKVUHUXMVHUUIVBZUWIVUHYIVVKVUHUMYJUUSUWHVHY
        KVUHUWIYLYMYRYNUXMUWIYOXRVVJUXMUXPUSZVBZYGUXQYHUMVVJVUIVVPVVMVVOVUHUXMV
        VNUXPVUHYIVVOVUHUMYJUWPUWHVHYKVUHUXPYLYMYRYNUXMUXPYOXRUUFWOUUGXOWQWRAUW
        GUXOUXRAUWGUXNCUWFVJZUXOAVUTUWGVVQVOVVAUWEUXNCUWFUUJXRACDUMVVQUXOVOVUFC
        DUXNUWFUUKXRYPUULYPXDWTUUMUUNAUDBUVJUVEUUSUEUBUCEFUVGICHUVIKUVEYQUVIYQU
        USYQUVGYQCVUCUMATYSMLAUVJWEZYTAUDBUVJUXBUWPUEUBUCEGUXDJDHUXFKUXBYQUXFYQ
        UWPYQUXDYQDVUEUMAUAYSNLVVRYTUUO $.
    $}

    $( A stronger version of ~ gsumpropd , working for magma, where only the
       closure of the addition operation on a common base is required.
       (Contributed by Thierry Arnoux, 28-Jun-2017.) $)
    gsumpropd2 $p |- ( ph -> ( G gsum F ) = ( H gsum F ) ) $=
      ( cfv co wceq ccnv cvv cv cplusg wa cbs wral crab cdif cima gsumpropd2lem
      eqid ) ABCUAZUBIUCZBUCZDUDRZSUOTUOUNUPSUOTUEBDUFRZUGIUQUHUIUJZUMUBUNUOEUD
      RZSUOTUOUNUSSUOTUEBEUFRZUGIUTUHUIUJZCDEFGHIJKLMNOPQURULVAULUK $.
  $}

  ${
    $d k l A $.  $d l B $.  $d l G $.  $d l X $.
    gsumconstf.k $e |- F/_ k X $.
    gsumconstf.b $e |- B = ( Base ` G ) $.
    gsumconstf.m $e |- .x. = ( .g ` G ) $.
    $( Sum of a constant series (Contributed by Thierry Arnoux, 5-Jul-2017.) $)
    gsumconstf $p |- ( ( G e. Mnd /\ A e. Fin /\ X e. B ) ->
      ( G gsum ( k e. A |-> X ) ) = ( ( # ` A ) .x. X ) ) $=
      ( vl cmnd wcel cfn w3a cmpt cgsu co chash cfv nfcv eqidd cbvmpt gsumconst
      weq oveq2i syl5eq ) EKLAMLFBLNEDAFOZPQEJAFOZPQARSFCQUGUHEPDJAFFJFTGDJUDFU
      AUBUEABCJEFHIUCUF $.
  $}

  ${
    $( TODO can be shortened using ~ gsumunsn $)
    $d a e y .<_ $.  $d a e x y A $.  $d x B $.  $d a e x y F $.
    $d a e x y G $.  $d a e x y M $.  $d a e y ph $.
    gsumle.b $e |- B = ( Base ` M ) $.
    gsumle.l $e |- .<_ = ( le ` M ) $.
    gsumle.m $e |- ( ph -> M e. oMnd ) $.
    gsumle.n $e |- ( ph -> M e. CMnd ) $.
    gsumle.a $e |- ( ph -> A e. Fin ) $.
    gsumle.f $e |- ( ph -> F : A --> B ) $.
    gsumle.g $e |- ( ph -> G : A --> B ) $.
    gsumle.c $e |- ( ph -> F oR .<_ G ) $.
    $( A finite sum in an ordered monoid is monotonic.  This proof would be
       much easier in an ordered group, where an inverse element would be
       available.  (Contributed by Thierry Arnoux, 13-Mar-2018.) $)
    gsumle $p |- ( ph -> ( M gsum F ) .<_ ( M gsum G ) ) $=
      ( cres cgsu co wcel wceq va ve vy vx cfn wbr wss ssid wa cv wi c0 csn cun
      sseq1 anbi2d reseq2 oveq2d breq12d imbi12d comnd ctos omndtos tospos 3syl
      cpo c0g res0 oveq2i eqid gsum0 eqtri cmnd omndmnd mndidcl syl5eqel posref
      cfv syl2anc eqtr4i breq2i sylib adantr wn ssun1 sstr2 ax-mp anim2i imim1i
      simplr simpllr simpr cplusg ad3antrrr wf ad2antrr ssun2 snss mpbir sseldd
      vex a1i ffvelrnd ccmn syl5ss fssres cdif ssfi fisuppfi gsumcl cofr simpll
      cvv syl wfn ffn inidm eqidd ofrval syl3anc ccnv cima cdm cnvimass sseqtri
      dmres inss1 sstri gsumsplit resabs1 oveq12i syl6eq feqresmpt fveq2 gsumsn
      cin cmpt eqtrd ex fnresdm omndadd2d disjsn sylibr cmnmnd 3brtr4d syl21anc
      snex unex a2d syl5 findcard2s imp mpanr2 mpancom 3brtr3d ) AGDBPZQRZGEBPZ
      QRZGDQRGEQRFBUESZAUUQUUSFUFZLUUTABBUGZUVABUHUUTAUVBUIZUVAAUAUJZBUGZUIZGDU
      VDPZQRZGEUVDPZQRZFUFZUKAULBUGZUIZGDULPZQRZGEULPZQRZFUFZUKAUBUJZBUGZUIZGDU
      VSPZQRZGEUVSPZQRZFUFZUKZAUVSUCUJZUMZUNZBUGZUIZGDUWJPZQRZGEUWJPZQRZFUFZUKZ
      UVCUVAUKUAUBUCBUVDULTZUVFUVMUVKUVRUWSUVEUVLAUVDULBUOUPUWSUVHUVOUVJUVQFUWS
      UVGUVNGQUVDULDUQURUWSUVIUVPGQUVDULEUQURUSUTUVDUVSTZUVFUWAUVKUWFUWTUVEUVTA
      UVDUVSBUOUPUWTUVHUWCUVJUWEFUWTUVGUWBGQUVDUVSDUQURUWTUVIUWDGQUVDUVSEUQURUS
      UTUVDUWJTZUVFUWLUVKUWQUXAUVEUWKAUVDUWJBUOUPUXAUVHUWNUVJUWPFUXAUVGUWMGQUVD
      UWJDUQURUXAUVIUWOGQUVDUWJEUQURUSUTUVDBTZUVFUVCUVKUVAUXBUVEUVBAUVDBBUOUPUX
      BUVHUUQUVJUUSFUXBUVGUUPGQUVDBDUQURUXBUVIUURGQUVDBEUQURUSUTAUVRUVLAUVOUVOF
      UFZUVRAGVFSZUVOCSUXCAGVASZGVBSUXDJGVCGVDVEAUVOGVGVRZCUVOGULQRUXFUVNULGQDV
      HZVIGUXFUXFVJZVKVLAUXEGVMSZUXFCSJGVNCGUXFHUXHVOVEVPCGFUVOHIVQVSUVOUVQUVOF
      UVNUVPGQUVNULUVPUXGEVHVTVIWAWBWCUWGUWLUWFUKUVSUESZUWHUVSSWDZUIZUWRUWLUWAU
      WFUWKUVTAUVSUWJUGZUWKUVTUKUVSUWIWEZUVSUWJBWFWGWHWIUXLUWLUWFUWQUXLUWLUWFUW
      QUKUXLUWLUIZUWFUWQUXOUWFUIUWLUXKUWFUWQUXLUWLUWFWJUXJUXKUWLUWFWKUXOUWFWLUW
      LUXKUIZUWFUIZUWCUWHDVRZGWMVRZRZUWEUWHEVRZUXSRZUWNUWPFUXQCUXSFGUYAUWCUXRUW
      EHIUXSVJZAUXEUWKUXKUWFJWNUXPUYACSZUWFUXPBCUWHEABCEWOZUWKUXKNWPZUXPUWJBUWH
      AUWKUXKWJZUWHUWJSZUXPUYHUWIUWJUGZUWIUVSWQZUWHUWJUCXAZWRWSXBWTZXCZWCUXPUWC
      CSUWFUXPUVSCUWBGXMUXFHUXHAGXDSZUWKUXKKWPZUVSXMSUXPUBXAZXBZUXPBCDWOZUVTUVS
      CUWBWOAUYRUWKUXKMWPZUXPUVSUWJBUXNUYGXEZBCUVSDXFVSZUXPUVSCXMUXFUMXGZUWBUXP
      UUTUVTUXJAUUTUWKUXKLWPZUYTBUVSXHVSZVUAXIXJWCUXPUXRCSZUWFUXPBCUWHDUYSUYLXC
      ZWCUXPUWECSUWFUXPUVSCUWDGXMUXFHUXHUYOUYQUXPUYEUVTUVSCUWDWOUYFUYTBCUVSEXFV
      SZUXPUVSCVUBUWDVUDVUGXIXJWCUXPUWFWLUXPUXRUYAFUFZUWFUXPADEFXKUFZUWHBSZVUHA
      UWKUXKXLZUXPAVUIVUKOXNUYLABBUXRUYAFBDEUEUEUWHAUYRDBXOZMBCDXPXNZAUYEEBXOZN
      BCEXPXNZLLBXQAVUJUIZUXRXRVUPUYAXRXSXTWCUXPUYNUWFUYOWCUUAUXPUWNUXTTUWFUXPU
      WNUWCGDUWIPZQRZUXSRZUXTUXPUWNGUWMUVSPZQRZGUWMUWIPZQRZUXSRVUSUXPUWJCUVSUWI
      UXSUWMGXMUXFHUXHUYCUYOUWJXMSUXPUVSUWIUYPUWHUUGUUHXBZUXPUYRUWKUWJCUWMWOUYS
      UYGBCUWJDXFVSUXPUUTUWMYAVUBYBZBUGVVEUESVUCUXPVVEUWJBVVEUWJDYCZYPZUWJVVEUW
      MYCVVGUWMVUBYDDUWJYFYEUWJVVFYGYHUYGXEBVVEXHVSUXPUXKUVSUWIYPULTUWLUXKWLUVS
      UWHUUBUUCZUXPUWJXRZYIVVAUWCVVCVURUXSVUTUWBGQUXMVUTUWBTUXNDUVSUWJYJWGVIVVB
      VUQGQUYIVVBVUQTUYJDUWIUWJYJWGVIYKYLUXPVURUXRUWCUXSUXPVURGUDUWIUDUJZDVRZYQ
      ZQRZUXRUXPVUQVVLGQUXPUDBCUWIDUYSUXPUWIUWJBUYJUYGXEZYMURUXPUXIUWHXMSZVUEVV
      MUXRTUXPUYNUXIUYOGUUDXNZVVOUXPUYKXBZVUFVVKCUXRUDGUWHXMHVVJUWHDYNYOXTYRURY
      RWCUXPUWPUYBTUWFUXPUWPUWEGEUWIPZQRZUXSRZUYBUXPUWPGUWOUVSPZQRZGUWOUWIPZQRZ
      UXSRVVTUXPUWJCUVSUWIUXSUWOGXMUXFHUXHUYCUYOVVDUXPUYEUWKUWJCUWOWOUYFUYGBCUW
      JEXFVSUXPUUTUWOYAVUBYBZBUGVWEUESVUCUXPVWEUWJBVWEUWJEYCZYPZUWJVWEUWOYCVWGU
      WOVUBYDEUWJYFYEUWJVWFYGYHUYGXEBVWEXHVSVVHVVIYIVWBUWEVWDVVSUXSVWAUWDGQUXMV
      WAUWDTUXNEUVSUWJYJWGVIVWCVVRGQUYIVWCVVRTUYJEUWIUWJYJWGVIYKYLUXPVVSUYAUWEU
      XSUXPVVSGUDUWIVVJEVRZYQZQRZUYAUXPVVRVWIGQUXPUDBCUWIEUYFVVNYMURUXPUXIVVOUY
      DVWJUYATVVPVVQUYMVWHCUYAUDGUWHXMHVVJUWHEYNYOXTYRURYRWCUUEUUFYSYSUUIUUJUUK
      UULUUMUUNAUUPDGQAVULUUPDTVUMBDYTXNURAUUREGQAVUNUURETVUOBEYTXNURUUO $.
  $}

  ${
    $d x y A $.  $d x B $.  $d y C $.  $d x y D $.  $d x E $.  $d x y ph $.
    gsummptf1o.x $e |- F/_ x H $.
    gsummptf1o.b $e |- B = ( Base ` G ) $.
    gsummptf1o.z $e |- .0. = ( 0g ` G ) $.
    gsummptf1o.i $e |- ( x = E -> C = H ) $.              
    gsummptf1o.g $e |- ( ph -> G e. CMnd ) $.
    gsummptf1o.a $e |- ( ph -> A e. Fin ) $.
    gsummptf1o.d $e |- ( ph -> F C_ B ) $.
    gsummptf1o.f $e |- ( ( ph /\ x e. A ) -> C e. F ) $.
    gsummptf1o.e $e |- ( ( ph /\ y e. D ) -> E e. A ) $.
    gsummptf1o.h $e |- ( ( ph /\ x e. A ) -> E! y e. D x = E ) $.
    $( Re-index a finite group sum using a bijection.  
       (Contributed by Thierry Arnoux, 29-Mar-2018.) $)
    gsummptf1o $p |- ( ph -> ( G gsum ( x e. A |-> C ) )
      = ( G gsum ( y e. D |-> H ) ) ) $=
      ( cmpt cgsu co ccom cfn cv wcel wss adantr sseldd eqid fmptd cvv csn cdif
      wa fisuppfi wral wceq wreu wf1o ralrimiva f1ompt sylanbrc gsumf1o fmptcos
      csb eqidd nfv wnfc a1i adantl csbiedf mpteq2dva eqtrd oveq2d ) AJBDFUCZUD
      UEJVSCGHUCZUFZUDUEJCGKUCZUDUEADEGVSJVTUGLNOQRABDFEVSABUHZDUIZURIEFAIEUJWD
      SUKTULVSUMUNZADEUOLUPUQVSRWEUSAHDUIZCGUTWCHVAZCGVBZBDUTGDVTVCAWFCGUAVDZAW
      HBDUBVDCBGDHVTVTUMVEVFVGAWAWBJUDAWACGBHFVIZUCWBACBGDHFVTVSWIAVTVJAVSVJVHA
      CGWJKACUHGUIURZBHFKDWKBVKBKVLWKMVMUAWGFKVAWKPVNVOVPVQVRVQ $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x ph $.
    gsummptun.b $e |- B = ( Base ` W ) $.
    gsummptun.z $e |- .0. = ( 0g ` W ) $.
    gsummptun.p $e |- .+ = ( +g ` W ) $.
    gsummptun.w $e |- ( ph -> W e. CMnd ) $.
    gsummptun.a $e |- ( ph -> ( A u. C ) e. Fin ) $.
    gsummptun.d $e |- ( ph -> ( A i^i C ) = (/) ) $.
    gsummptun.1 $e |- ( ( ph /\ x e. ( A u. C ) ) -> D e. B ) $.
    $( Group sum of a disjoint union, whereas sums are expressed as mappings.
       (Contributed by Thierry Arnoux, 28-Mar-2018.) $)
    gsummptun $p |- ( ph -> ( W gsum ( x e. ( A u. C ) |-> D ) ) =
      ( ( W gsum ( x e. A |-> D ) ) .+ ( W gsum ( x e. C |-> D ) ) ) ) $=
      ( cmpt cgsu co cres cun cfn eqid fmptd cdif fisuppfi eqidd gsumsplit wceq
      cvv csn wss ssun1 resmpt ax-mp oveq2i ssun2 oveq12i syl6eq ) AHBCEUAZFQZR
      SHVACTZRSZHVAETZRSZGSHBCFQZRSZHBEFQZRSZGSAUTDCEGVAHUBIJKLMNABUTFDVAPVAUCU
      DZAUTDUJIUKUEVANVJUFOAUTUGUHVCVGVEVIGVBVFHRCUTULVBVFUICEUMBUTCFUNUOUPVDVH
      HREUTULVDVHUIECUQBUTEFUNUOUPURUS $.
  $}
  
  ${
    $d p x y A $.  $d p x y B $.  $d p y C $.  $d p x y E $.  $d p x y F $.
    $d p x y ph $.  $d x y .0. $.  $d x y W $.
    gsummpt2co.b $e |- B = ( Base ` W ) $.
    gsummpt2co.z $e |- .0. = ( 0g ` W ) $.
    gsummpt2co.w $e |- ( ph -> W e. CMnd ) $.
    gsummpt2co.a $e |- ( ph -> A e. Fin ) $.
    gsummpt2co.e $e |- ( ph -> E ~<_ om ) $.
    gsummpt2co.1 $e |- ( ( ph /\ x e. A ) -> C e. B ) $.
    gsummpt2co.2 $e |- ( ( ph /\ x e. A ) -> D e. E ) $.
    gsummpt2co.3 $e |- F = ( x e. A |-> D ) $.
    $( Split a finite sum into a sum of a collection of sums over disjoint
       subsets.  (Contributed by Thierry Arnoux, 27-Mar-2018.) $)
    gsummpt2co $p |- ( ph -> ( W gsum ( x e. A |-> C ) ) =
      ( W gsum ( y e. E |-> ( W gsum ( x e. ( `' F " { y } ) |-> C ) ) ) ) ) $=
      ( wcel vp cmpt cgsu co ccnv cv c2nd cfv csb csn cmpt2 nfcsb1v csbeq1a wss
      cima ssid a1i cop wceq wbr wex elcnv vex op2ndd adantr cdm dmmptss breldm
      wa sseldi adantl eqeltrd exlimivv sylbi wfun wreu funmpt2 funcnvcnv ax-mp
      crn dfdm4 dmeqi ralrimiva dmmptg syl syl5eq syl5eqr eleq2d biimpar relcnv
      wral wrel fcnvgreu mpanl1 syl2anc gsummptf1o cxp ciun rnmptss dfcnv2 nfcv
      mpteq1d csbeq1 csbid syl6eq mpt2mptxf oveq2d cvv cdom ctex mptfi syl5eqel
      com cnvfi 3syl imaexg simpll imassrn sseqtr4i sstri elimasn biimpi sylibr
      cfn anasss wn df-br pm2.24d imp gsum2d2 3eqtrd ) AJBDFUBUCUDJUAIUEZBUAUFZ
      UGUHZFUIZUBZUCUDJCBHYLCUFZUJZUOZFUKZUCUDJCHJBYSFUBUCUDUBUCUDABUADEFYLYNEJ
      YOKBYNFULZLMBYNFUMNOEEUNAEUPUQQYMYLTZYNDTZAUUBYMYQBUFZURZUSZUUDYQIUTZVIZB
      VACVAUUCCBYMIVBUUHUUCCBUUHYNUUDDUUFYNUUDUSZUUGYQUUDYMCVCZBVCZVDZVEUUGUUDD
      TZUUFUUGIVFZDUUDBDGISVGZUUDYQIUUKUUJVHVJVKVLVMVNVKAUUMVIZYLUEVOZUUDYLVTZT
      ZUUDYNUSUAYLVPZUUQUUPIVOUUQBDGISVQIVRVSUQAUUSUUMAUURDUUDAUURUUNDIWAZAUUNB
      DGUBZVFZDIUVBSWBAGHTZBDWKZUVCDUSAUVDBDRWCZBDGHWDWEWFWGWHWIYLWLUUQUUSUUTIW
      JYLUUDUAWMWNWOWPAYPYTJUCAYPUACHYRYSWQWRZYOUBYTAUAYLUVGYOAIVTHUNZYLUVGUSAU
      VEUVHUVFBDGHISWSWECHIWTWEXBCBUAHYSYOFCYOXAUUAUUFYOBUUDFUIZFUUFUUIYOUVIUSU
      ULBYNUUDFXCWEBFXDXEXFXEXGAHEYSYLCBJXHXHFKLMNAHXMXIUTHXHTPHXJWEAYSXHTZYQHT
      ZAYLYDTZUVJADYDTZIYDTUVLOUVMIUVBYDSBDGXKXLIXNXOZYLYRYDXPWEVEAUVKUUDYSTZFE
      TZAUVKVIZUVOVIZAUUMUVPAUVKUVOXQUVRYSDUUDYSUUNDYSUURUUNYLYRXRUVAXSUUOXTUVR
      UUEYLTZUVOUVOUVSUVQUVOUVSYLYQUUDUUJUUKYAZYBVKZUVTYCVJQWOYEUVNAUVKUVOVIZYQ
      UUDYLUTZYFZFKUSZAUWBVIZUWDUWEUWFUWCUWEAUVKUVOUWCUVRUVSUWCUWAYQUUDYLYGYCYE
      YHYIYEYJYK $.
  $}

$(
  @{
    gsummptmhm.b @e |- B = ( Base ` G ) @.
    gsummptmhm.z @e |- .0. = ( 0g ` G ) @.
    gsummptmhm.g @e |- ( ph -> G e. CMnd ) @.
    gsummptmhm.h @e |- ( ph -> H e. Mnd ) @.
    gsummptmhm.a @e |- ( ph -> A e. V ) @.
    gsummptmhm.k @e |- ( ph -> K e. ( G MndHom H ) ) @.
    gsummptmhm.c @e |- ( ( ph /\ x e. A ) -> C e. B ) @.
    gsummptmhm.w @e |- ( ph -> 
                         ( `' ( x e. A |-> C ) " ( _V \ { .0. } ) ) e. Fin ) @.
    @( Apply a group homomorphism to a group sum expressed with a mapping.
       (Contributed by Thierry Arnoux, 19-Mar-2018.) @)
    gsummptmhm @p |- ( ph -> ( H gsum ( x e. A |-> ( K ` C ) ) )
      = ( K ` ( G gsum ( x e. A |-> C ) ) ) ) @=
      ? @.
  @}
  
  @{
    regsumfsum.1 @e |- ( ph -> A e. Fin ) @.
    regsumfsum.2 @e |- ( ( ph /\ k e. A ) -> B e. RR ) @.
    @( Relate a group sum on ` ( CCfld |``s RR ) ` to a finite sum on the reals.
       (Contributed by Mario Carneiro, 28-Dec-2014.) @)
    regsumfsum @p |- ( ph -> ( ( CCfld |`s RR ) gsum ( k e. A |-> B ) ) 
                         = sum_ k e. A B ) @=
      ? @.
  @}

  @{
    gsumov.b @e |- B = ( Base ` W ) @.
    gsumov.z @e |- .0. = ( 0g ` W ) @.
    gsumov.p @e |- .+ = ( +g ` W ) @.
    gsumov.a @e |- ( ph -> A e. Fin ) @.
    gsumov.w @e |- ( ph -> W e. CMnd ) @.
    @{
      gsumov1.k @e |- ( ph -> K e. U ) @.
      gsumov1.n @e |- ( ph -> P e. K ) @.
      gsumov1.c @e |- ( ( ph /\ k e. A ) -> Q e. B ) @.
      gsumov1.d @e |- ( ( ph /\ ( r e. K /\ x e. B /\ y e. B ) ) ->
                     ( r .x. ( x .+ y ) ) = ( ( r .x. x ) .+ ( r .x. y ) ) ) @.
      gsumov1.o @e |- ( ( ph /\ r e. K ) -> ( r .x. .0. ) = .0. ) @.
      @( Finite sum of a distributive operation.  (Contributed by Thierry
         Arnoux, 16-Mar-2018.) @)
      gsumov1 @p |- ( ph -> ( W gsum ( k e. A |-> ( P .x. Q ) ) ) =
                             ( P .x. ( W gsum ( k e. A |-> Q ) ) ) ) @=
        ? @.
    @}

    @{
      gsumov2.z @e |- .0b = ( 0g ` G ) @.
      gsumov2.q @e |- .+^ = ( +g ` G ) @.
      gsumov2.k @e |- ( ph -> K C_ ( Base ` G ) ) @.
      gsumov2.h @e |- ( ph -> G e. CMnd ) @.
      gsumov2.n @e |- ( ph -> Q e. B ) @.
      gsumov2.c @e |- ( ( ph /\ k e. A ) -> P e. K ) @.
      gsumov2.d @e |- ( ( ph /\ ( r e. K /\ s e. K /\ x e. B ) ) ->
                    ( ( r .+^ s ) .x. x ) = ( ( r .x. x ) .+ ( s .x. x ) ) ) @.
      gsumov2.o @e |- ( ( ph /\ x e. B ) -> ( .0b .x. x ) = .0. ) @.
      @( Finite sum of a distributive operation.  (Contributed by Thierry
         Arnoux, 16-Mar-2018.) @)
      gsumov2 @p |- ( ph -> ( W gsum ( k e. A |-> ( P .x. Q ) ) ) =
                             ( ( G gsum ( k e. A |-> P ) ) .x. Q ) ) @=
        ? @.
    @}
  @}

  @{
    gsumvsca.b @e |- B = ( Base ` W ) @.
    gsumvsca.g @e |- G = ( Scalar ` W ) @.
    gsumvsca.z @e |- .0. = ( 0g ` W ) @.
    gsumvsca.t @e |- .x. = ( .s ` W ) @.
    gsumvsca.p @e |- .+ = ( +g ` W ) @.
    gsumvsca.k @e |- ( ph -> K C_ ( Base ` G ) ) @.
    gsumvsca.a @e |- ( ph -> A e. Fin ) @.
    gsumvsca.w @e |- ( ph -> W e. SLMod ) @.
    @{
      gsumvsca1.n @e |- ( ph -> P e. K ) @.
      gsumvsca1.c @e |- ( ( ph /\ k e. A ) -> Q e. B ) @.
      @( Scalar product of a finite group sum for a left module over a semiring
         (Contributed by Thierry Arnoux, 16-Mar-2018.) @)
      gsumvsca1 @p |- ( ph -> ( W gsum ( k e. A |-> ( P .x. Q ) ) ) =
                             ( P .x. ( W gsum ( k e. A |-> Q ) ) ) ) @=
        ( vx vy vr cvv cslmd wcel ccmn slmdcmn syl cbs cfv fvex a1i ssexd cv wa
        w3a co wceq adantr wss simpr1 sseldd simpr2 simpr3 eqid slmdvsdi sselda
        syl13anc slmdvs0 syl2anc gsumov1 ) AUCUDBCDEFGUFHJKLUEMOQSAKUGUHZKUIUHT
        KUJUKAJIULUMZUFVPUFUHAIULUNUORUPUAUBAUEUQZJUHZUCUQZCUHZUDUQZCUHZUSZURZV
        OVQVPUHZVTWBVQVSWAEUTGUTVQVSGUTVQWAGUTEUTVAAVOWCTVBWDJVPVQAJVPVCWCRVBAV
        RVTWBVDVEAVRVTWBVFAVRVTWBVGEVQGIVPCKVSWAMQNPVPVHZVIVKAVRURVOWEVQLGUTLVA
        AVOVRTVBAJVPVQRVJGIVPKVQLNPWFOVLVMVN @.
    @}

    @{
      gsumvsca2.n @e |- ( ph -> Q e. B ) @.
      gsumvsca2.c @e |- ( ( ph /\ k e. A ) -> P e. K ) @.
      @( Scalar product of a finite group sum for a left module over a semiring
         (Contributed by Thierry Arnoux, 16-Mar-2018.) @)
      gsumvsca2 @p |- ( ph -> ( W gsum ( k e. A |-> ( P .x. Q ) ) ) =
                             ( ( G gsum ( k e. A |-> P ) ) .x. Q ) ) @=
        ( vx vs vr cplusg cfv c0g cslmd wcel ccmn slmdcmn syl eqid csrg slmdsrg
        srgcmn 3syl cv w3a wa cbs co wceq adantr simpr1 sseldd simpr2 slmdvsdir
        wss simpr3 syl13anc simpr slmd0vs syl2anc gsumov2 ) AUCBCDEIUFUGZFGHIJK
        LIUHUGZUDUEMOQSAKUIUJZKUKUJTKULUMVRUNZVQUNZRAVSIUOUJIUKUJTIKNUPIUQURUAU
        BAUEUSZJUJZUDUSZJUJZUCUSZCUJZUTZVAZVSWBIVBUGZUJWDWJUJWGWBWDVQVCWFGVCWBW
        FGVCWDWFGVCEVCVDAVSWHTVEWIJWJWBAJWJVJWHRVEZAWCWEWGVFVGWIJWJWDWKAWCWEWGV
        HVGAWCWEWGVKEVQWBWDGIWJCKWFMQNPWJUNWAVIVLAWGVAVSWGVRWFGVCLVDAVSWGTVEAWG
        VMGIVRCKWFLMNPVTOVNVOVP @.
    @}
  @}

  @{
    gsummptadd.b @e |- B = ( Base ` G ) @.
    gsummptadd.z @e |- .0. = ( 0g ` G ) @.
    gsummptadd.p @e |- .+ = ( +g ` G ) @.
    gsummptadd.g @e |- ( ph -> G e. CMnd ) @.
    gsummptadd.a @e |- ( ph -> A e. Fin ) @.
    gsummptadd.f @e |- ( ( ph /\ x e. A ) -> C e. B ) @.
    gsummptadd.h @e |- ( ( ph /\ x e. A ) -> D e. B ) @.
    @( The sum of two group sums expressed as mappings.  (Contributed by 
       Thierry Arnoux, 19-Mar-2018.) @)
    gsummptadd @p |- ( ph -> ( G gsum ( x e. A |-> ( C .+ D ) ) ) 
      = ( ( G gsum ( x e. A |-> C ) ) .+ ( G gsum ( x e. A |-> D ) ) ) ) @=
      ? @.
  @}

  @{
    gsummptres.b @e |- B = ( Base ` G ) @.
    gsummptres.z @e |- .0. = ( 0g ` G ) @.
    gsummptres.g @e |- ( ph -> G e. CMnd ) @.
    gsummptres.a @e |- ( ph -> A e. Fin ) @.
    gsummptres.f @e |- ( ( ph /\ x e. A ) -> C e. B ) @.
    gsummptres.s @e |- ( ( ph /\ x e. ( A \ D ) ) -> C = .0. ) @.
    @( Extend a finite group sum by padding outside with zeroes.
       (Contributed by Thierry Arnoux, 27-Mar-2018.) @)
    gsummptres @p |- ( ph 
      -> ( G gsum ( x e. A |-> C ) ) = ( G gsum ( x e. D |-> C ) ) ) @=
      ? @.
  @}

$)

  ${
    $d r s u v w y z A $.  $d r s u v w y z F $.  $d r s u v w y z ph $.
    $d r s u v w y z G $.  $d r u v w y z S $.
    xrge0tsmsd.g $e |- G = ( RR*s |`s ( 0 [,] +oo ) ) $.
    xrge0tsmsd.a $e |- ( ph -> A e. V ) $.
    xrge0tsmsd.f $e |- ( ph -> F : A --> ( 0 [,] +oo ) ) $.
    xrge0tsmsd.s $e |- ( ph -> S = sup (
      ran ( s e. ( ~P A i^i Fin ) |-> ( G gsum ( F |` s ) ) ) , RR* , < ) ) $.
    $( Any finite or infinite sum in the nonnegative extended reals is uniquely
       convergent to the supremum of all finite sums.  (Contributed by Mario
       Carneiro, 13-Sep-2015.)  (Revised by Thierry Arnoux, 30-Jan-2017.) $)
    xrge0tsmsd $p |- ( ph -> ( G tsums F ) = { S } ) $=
      ( vz co wcel cc0 cxr wbr wa cvv syl vu vy vx vv vr vw ctsu wceq cpnf cicc
      csn cv wss cres cgsu wi cpw cfn cin wral wrex cle cordt cfv crest crn clt
      cmpt csup cxrs ax-mp cmnf cdif cress eqid wne ge0nemnf elxrge0 mp2an ccmn
      wf jca eqeltri a1i elfpw simprbi simplbi fssres fisuppfi gsumcl sseldi c0
      cc reseq2 syl6eq oveq2d elrnmpt1s supxrub sylancl breqtrrd sylanbrc letop
      ctop wb ovex inss1 cioo simplrl simplrr simpr elin syl2anc simprrr adantr
      simprrl sstrd simprlr xrge0gsumle xrltletrd weq w3a mpbir3and sseldd expr
      cr ralrimiva ad3antrrr breqtrd mpbid sylib reximddv syl5ibrcom syl5bi mpd
      eleq2 simprr ad2antrr ad2antrl ctps cha iccssxr xrsbas ressbas2 xrge0subm
      cbs csubmnd difexg simpl eldifsn 3imtr4i ssriv ressabs eqtr4i xrs10 subm0
      c0g xrex xrge0cmn adantl syl2an frn supxrcl eqeltrd 0ss 0fin mpbir2an 0cn
      fmptd res0 gsum0 sseli ctg reex elrestr mp3an12 xrtgioo syl6eleqr tg2 cxp
      elrest wfn ioof ffn ovelrn mp2b syl6ss simp-4l simprll eliooord xrlelttrd
      ssfi simprd elioo1 anassrs simpld supxrlub rgenw cbvmptv rexrnmpt anbi12d
      breq2 imbi1d rexlimdvva rexlimdv cioc eqeltrrd pnfnei simp-5l rexr simprl
      sseq1 pnfge pnfxr elioc1 simplr rexlimddv wo xrnemnf mpjaodan syl5 imbi2d
      rexralbidv imbi12d rexlimdva ralrimiv cts xrstset resstset topnval xrstps
      ltpnf resstps eltsms mpbir2and ctsr letsr ordthaus resthaus haustsms2
      mp1i ) ACEDUGMZNZVUACUKUHAVUBCOUIUJMZNZCUAULZNZLULZUBULZUMZEDVUHUNZUOMZVU
      ENZUPZUBBUQURUSZUTLVUNVAZUPZUAVBVCVDZVUCVEMZUTACPNZOCVBQZVUDACGVUNEDGULZU
      NZUOMZVHZVFZPVGVIZPKAVVEPUMZVVFPNAVUNPVVDWAVVGAGVUNVVCPVVDAVVAVUNNZRZVUCP
      VVCOUIUUAZVVIVVAVUCVVBEUROVUCPUMVUCEUUEVDUHVVJVUCPEVJHUUBUUCVKZVUCVJPVLUK
      ZVMZVNMZUUFVDNOEUUPVDUHVVNVVNVOZUUDVUCEVVNOEVJVUCVNMZVVNVUCVNMZHVVMSNZVUC
      VVMUMVVQVVPUHPSNVVRUUQPVVLSUUGVKUCVUCVVMUCULZPNZOVVSVBQZRZVVTVVSVLVPZRVVS
      VUCNVVSVVMNVWBVVTVWCVVTVWAUUHVVSVQWBVVSVRVVSPVLUUIUUJUUKVVMVUCVJSUULVSUUM
      VVNVVOUUNUUOVKZEVTNZVVIEVVPVTHUURWCZWDVVHVVAURNZAVVHVVABUMZVWGVVABWEZWFUU
      SZABVUCDWAZVWHVVAVUCVVBWAVVHJVVHVWHVWGVWIWGBVUCVVADWHUUTZVVIVVAVUCSOUKVMZ
      VVBVWJVWLWIWJWKVVDVOZUVHVUNPVVDUVATZVVEUVBTUVCZAOVVFCVBAVVGOVVENZOVVFVBQV
      WOWLVUNNZOWMNVWQVWRWLBUMWLURNBUVDUVEWLBWEUVFUVGGVUNVVCOWLVVDWMVWNVVAWLUHZ
      VVCEWLUOMOVWSVVBWLEUOVWSVVBDWLUNWLVVAWLDWNDUVIWOWPEOVWDUVJWOWQVSVVEOWRWSK
      WTZCVRXAAVUPUAVURVUEVURNZVUEUDULZVUCUSZUHZUDVUQVAZAVUPVUQXCNZVUCSNZVXAVXE
      XDXBOUIUJXEZUDVUEVUCVUQXCSUVTVSAVXDVUPUDVUQAVXBVUQNZRZVUPVXDCVXCNZVUIVUKV
      XCNZUPZUBVUNUTZLVUNVAZUPVXKCVXBNZVXJVXOVXCVXBCVXBVUCXFUVKAVXIVXPVXOAVXIVX
      PRZRZCYENZVXOCUIUHZVXRVXSRZVUFVUEVXBYEUSZUMZRZUAXGVFZVAZVXOVYAVYBVYEUVLVD
      ZNCVYBNZVYFVYAVYBVUQYEVEMZVYGVYAVXIVYBVYINZAVXIVXPVXSXHVXFYESNVXIVYJXBUVM
      VXBYEVUQXCSUVNUVOTVYIVYIVOUVPUVQVYAVXPVXSVYHAVXIVXPVXSXIVXRVXSXJCVXBYEXKX
      AUAVYBVYECUVRXLVYAVYDVXOUAVYEVUEVYENZVUEUEULZUFULZXGMZUHZUFPVAUEPVAZVYAVY
      DVXOUPZPPUVSZYEUQZXGWAXGVYRUWAVYKVYPXDUWBVYRVYSXGUWCUEUFPPVUEXGUWDUWEVYAV
      YOVYQUEUFPPVYAVYLPNZVYMPNZRZRVYQVYOCVYNNZVYNVYBUMZRZVXOUPVYAWUBWUEVXOVYAW
      UBWUERZRZVYLEDVUGUNZUOMZVGQZVXNLVUNWUGVUGVUNNZWUJRZRZVXMUBVUNWUMVUHVUNNZV
      UIVXLWUGWULWUNVUIRZVXLWUGWULWUORZRZVUKVXBNZVUKVUCNZVXLWUQVYNVXBVUKWUQVYNV
      YBVXBWUGWUDWUPVYAWUBWUCWUDXMXNVXBYEXFUWFWUQVUKVYNNZVUKPNZVYLVUKVGQZVUKVYM
      VGQZWUQVUCPVUKVVJWUQVUHVUCVUJEUROVVKVWDVWEWUQVWFWDZWUQWUNVUHURNZWUGWULWUN
      VUIXOZWUNVUHBUMZWVEVUHBWEZWFZTZWUQVWKWVGVUHVUCVUJWAZWUQAVWKAVXQVXSWUFWUPU
      WGZJTZWUQWUNWVGWVFWUNWVGWVEWVHWGZTZBVUCVUHDWHZXLZWUQVUHVUCVWMVUJWVJWVQWIW
      JZWKZWUQVYLWUIVUKWUGVYTWUPVYAVYTWUAWUEUWHZXNZWUQVUCPWUIVVJWUQVUGVUCWUHEUR
      OVVKVWDWVDWUQWVEVUIVUGURNZWVJWUGWULWUNVUIXMZVUHVUGUWKZXLZWUQVWKVUGBUMZVUG
      VUCWUHWAZWVMWUQVUGVUHBWWCWVOXPBVUCVUGDWHZXLZWUQVUGVUCVWMWUHWWEWWIWIWJWKWV
      SWUGWUKWUJWUOXQWUQBVUHVUGDEFHWUQABFNZWVLITWVMWVFWWCXRXSWUQVUKCVYMWVSWUQAV
      USWVLVWPTWUGWUAWUPVYAVYTWUAWUEXQXNZWUQVUKVVFCVBWUQVVGVUKVVENZVUKVVFVBQWUQ
      AVVGWVLVWOTWUQWUNVUKSNWWLWVFEVUJUOXEGVUNVVCVUKVUHVVDSVWNGUBXTVVBVUJEUOVVA
      VUHDWNWPWQWSVVEVUKWRXLWUQACVVFUHZWVLKTWTWUGCVYMVGQZWUPWUGVYLCVGQZWWNWUGWU
      CWWOWWNRVYAWUBWUCWUDXOCVYLVYMUWITZUWLXNUWJWUQVYTWUAWUTWVAWVBWVCYAXDWWAWWK
      VYLVYMVUKUWMXLYBYCWVRVUKVXBVUCXKZXAUWNYDYFWUGVYLVYMVGQZUFVVEVAZWUJLVUNVAZ
      WUGVYLVVFVGQZWWSWUGVYLCVVFVGWUGWWOWWNWWPUWOAWWMVXQVXSWUFKYGYHWUGVVGVYTWXA
      WWSXDZAVVGVXQVXSWUFVWOYGWVTUFVVEVYLUWPZXLYIWUISNZLVUNUTWWSWWTXDWXDLVUNEWU
      HUOXEUWQWWRWUJLUFVUNWUIVVDSGLVUNVVCWUIGLXTVVBWUHEUOVVAVUGDWNWPUWRVYMWUIVY
      LVGUXAUWSVKZYJYKYDVYOVYDWUEVXOVYOVUFWUCVYCWUDVUEVYNCYOVUEVYNVYBUXKUWTUXBY
      LUXCYMUXDYNVXRVXTRZVYLUIUXEMZVXBUMZVXOUEYEWXFVXIUIVXBNWXHUEYEVAAVXIVXPVXT
      XHWXFCUIVXBVXRVXTXJAVXIVXPVXTXIUXFUEVXBUXGXLWXFVYLYENZWXHRZRZWUJVXNLVUNWX
      KWULRZVXMUBVUNWXLWUNVUIVXLWXLWUORZWURWUSVXLWXMWXGVXBVUKWXKWXHWULWUOWXFWXI
      WXHYPYQWXMVUKWXGNZWVAWVBVUKUIVBQZWXMVUCPVUKVVJWXMVUHVUCVUJEUROVVKVWDVWEWX
      MVWFWDZWUNWVEWXLVUIWVIYRZWXMVWKWVGWVKWXMAVWKAVXQVXTWXJWULWUOUXHZJTZWUNWVG
      WXLVUIWVNYRZWVPXLZWXMVUHVUCVWMVUJWXQWYAWIWJZWKZWXMVYLWUIVUKWXKVYTWULWUOWX
      IVYTWXFWXHVYLUXIYRZYQZWXMVUCPWUIVVJWXMVUGVUCWUHEUROVVKVWDWXPWXMWVEVUIWWBW
      XQWXLWUNVUIYPZWWDXLZWXMVWKWWFWWGWXSWXMVUGVUHBWYFWXTXPWWHXLZWXMVUGVUCVWMWU
      HWYGWYHWIWJWKWYCWXKWUKWUJWUOXIWXMBVUHVUGDEFHWXMAWWJWXRITWXSWXLWUNVUIUXJWY
      FXRXSWXMWVAWXOWYCVUKUXLTWXMVYTUIPNWXNWVAWVBWXOYAXDWYEUXMVYLUIVUKUXNWSYBYC
      WYBWWQXAYDYFWXKWWSWWTWXKWXAWWSWXKVYLCVVFVGWXKVYLUICVGWXIVYLUIVGQWXFWXHVYL
      UYKYRVXRVXTWXJUXOWTAWWMVXQVXTWXJKYGYHWXKVVGVYTWXBAVVGVXQVXTWXJVWOYGWYDWXC
      XLYIWXEYJYKUXPVXRVUSCVLVPZRZVXSVXTUXQAWYJVXQAVUSWYIVWPAVUSVUTWYIVWPVWTCVQ
      XLWBXNCUXRYJUXSYDUXTVXDVUFVXKVUOVXOVUEVXCCYOVXDVUMVXMLUBVUNVUNVXDVULVXLVU
      IVUEVXCVUKYOUYAUYBUYCYLUYDYMUYEAUBLUABVUCCVUNDEVURFVVKVUCVUQEVVKVXGVUQEUY
      FVDUHVXHVUCVJEVUQSHUYGUYHVKUYIZVUNVOVWEAVWFWDZEYSNAEVVPYSHVJYSNVXGVVPYSNU
      YJVXHVUCVJSUYLVSWCWDZIJUYMUYNABVUCDEVURFCVVKWYLWYMIJWYKAVUQYTNZVXGVURYTNV
      BUYONWYNAUYPVBUYQUYTVXHVUCVUQSUYRWSUYSYN $.
  $}

  ${
    $d x A $.  $d x F $.  $d x G $.  $d x ph $.
    xrge0tsmseq.g $e |- G = ( RR*s |`s ( 0 [,] +oo ) ) $.
    xrge0tsmseq.a $e |- ( ph -> A e. V ) $.
    xrge0tsmseq.f $e |- ( ph -> F : A --> ( 0 [,] +oo ) ) $.
    $( Any limit of a finite or infinite sum in the nonnegative extended reals
       is the union of the sets limits, since this set is a singleton.
       (Contributed by Thierry Arnoux, 23-Jun-2017.) $)
    xrge0tsmsbi $p |- ( ph ->
                           ( C e. ( G tsums F ) <-> C = U. ( G tsums F ) ) ) $=
      ( ctsu co wcel cuni csn wceq c1o cen wbr cc0 cvv cpnf wf xrge0tsms2 sylib
      cicc syl2anc en1b eleq2d wb ovex uniex eleq1 mpbiri elsncg syl ibir elsni
      impbii syl6bbr ) ACEDJKZLCUTMZNZLZCVAOZAUTVBCAUTPQRZUTVBOABFLBSUAUEKDUBVE
      HIBDEFGUCUFUTUGUDUHVDVCVDVCVDCTLZVCVDUIVDVFVATLUTEDJUJUKCVATULUMCVATUNUOU
      PCVAUQURUS $.
    ${
      xrge0tsmseq.h $e |- ( ph -> C e. ( G tsums F ) ) $.
      $( Any limit of a finite or infinite sum in the nonnegative extended
         reals is the union of the sets limits, since this set is a singleton.
         (Contributed by Thierry Arnoux, 24-Mar-2017.) $)
      xrge0tsmseq $p |- ( ph -> C = U. ( G tsums F ) ) $=
        ( ctsu co cuni csn wcel c1o cen wbr wceq syl2anc cc0 cpnf wf xrge0tsms2
        cicc en1eqsn unieqd unisng syl eqtr2d ) AEDKLZMCNZMZCAUKULACUKOZUKPQRZU
        KULSJABFOBUAUBUELDUCUOHIBDEFGUDTCUKUFTUGAUNUMCSJCUKUHUIUJ $.
    $}
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
    Rings - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


  ${
    $d x B $.  $d e x R $.  $d e x .1. $.  $d x .0. $.  $d x .x. $.
    $d e x ph $. 
    rngurd.b $e |- ( ph -> B = ( Base ` R ) ) $.
    rngurd.p $e |- ( ph -> .x. = ( .r ` R ) ) $.
    rngurd.z $e |- ( ph -> .1. e. B ) $.
    rngurd.i $e |- ( ( ph /\ x e. B ) -> ( .1. .x. x ) = x ) $.
    rngurd.j $e |- ( ( ph /\ x e. B ) -> ( x .x. .1. ) = x ) $.
    $( Deduce the unit of a ring from its properties.  (Contributed by Thierry
       Arnoux, 6-Sep-2016.) $)
    rngurd $p |- ( ph -> .1. = ( 1r ` R ) ) $=
      ( ve wcel co wceq wa wral oveqd eqeq1d anbi12d cur cfv cbs cmulr cio eqid
      cv dfur2 eleqtrd jca ralrimiva adantr raleqbidva mpbid wb wi simpr oveq2d
      weu wal eqeq12d rspcdv mpd adantrr simprr oveq2 id oveq1 rspcv imp simprd
      syl2anc eqtr3d ex eleq2d imbi1d alrimiv eleq1 ralbidv eqeu iota2 mpbi2and
      syl3anc syl5req ) ADUAUBZLUGZDUCUBZMZWFBUGZDUDUBZNZWIOZWIWFWJNZWIOZPZBWGQ
      ZPZLUEZFBWGDWJWELWGUFWJUFWEUFUHAFWGMZFWIWJNZWIOZWIFWJNZWIOZPZBWGQZWRFOZAF
      CWGIGUIZAFWIENZWIOZWIFENZWIOZPZBCQXEAXLBCAWICMZPZXIXKJKUJUKAXLXDBCWGGXNXI
      XAXKXCXNXHWTWIXNEWJFWIAEWJOXMHULZRSXNXJXBWIXNEWJWIFXORSTUMUNZAFCMZWQLUSZW
      SXEPZXFUOIAWSXSWQWFFOZUPZLUTXRXGAWSXEXGXPUJAYALAWFCMZWFWIENZWIOZWIWFENZWI
      OZPZBCQZPZXTUPYAAYIXTAYIPZFWFENZWFFAYBYKWFOZYHAYBPZXIBCQZYLAYNYBAXIBCJUKU
      LYMXIYLBWFCAYBUQYMWIWFOZPZXHYKWIWFYPWIWFFEYMYOUQZURYQVAVBVCVDYJXQYHYKFOZA
      XQYIIULAYBYHVEXQYHPWFFENZFOZYRXQYHYTYRPZYGUUABFCWIFOZYDYTYFYRUUBYCYSWIFWI
      FWFEVFUUBVGZVAUUBYEYKWIFWIFWFEVHUUCVATVIVJVKVLVMVNAYIWQXTAYBWHYHWPACWGWFG
      VOAYGWOBCWGGXNYDWLYFWNXNYCWKWIXNEWJWFWIXORSXNYEWMWIXNEWJWIWFXORSTUMTVPUNV
      QWQXSLFWGXTWHWSWPXEWFFWGVRXTWOXDBWGXTWLXAWNXCXTWKWTWIWFFWIWJVHSXTWMXBWIWF
      FWIWJVFSTVSTZVTWCWQXSLFCUUDWAVLWBWD $.
  $}

  ${
    $d x .1. $.  $d x A $.  $d x B $.  $d x R $.  $d x S $.
    ress1r.s $e |- S = ( R |`s A ) $.
    ress1r.b $e |- B = ( Base ` R ) $.
    ress1r.1 $e |- .1. = ( 1r ` R ) $.
    $( ` 1r ` is unaffected by restriction.  This is a bit more generic than
       ~ subrg1 (Contributed by Thierry Arnoux, 6-Sep-2018.) $)
    ress1r $p |- ( ( R e. Ring /\ .1. e. A /\ A C_ B ) -> .1. = ( 1r ` S ) ) $=
      ( vx crg wcel wss w3a cmulr cfv cbs wceq cvv co syl2anc ressbas2 3ad2ant3
      simp3 fvex eqeltri ssexg sylancl eqid ressmulr syl simp2 cv simpl1 sselda
      wa rnglidm rngridm rngurd ) CJKZEAKZABLZMZIADCNOZEVAUSADPOQUTABDCFGUAUBVB
      ARKZVCDNOQVBVABRKVDUSUTVAUCZBCPORGCPUDUEABRUFUGACDVCRFVCUHZUIUJUSUTVAUKVB
      IULZAKZUOZUSVGBKZEVGVCSVGQUSUTVAVHUMZVBABVGVEUNZBCVCEVGGVFHUPTVIUSVJVGEVC
      SVGQVKVLBCVCEVGGVFHUQTUR $.
  $}

  ${
    dvrdir.b $e |- B = ( Base ` R ) $.
    dvrdir.u $e |- U = ( Unit ` R ) $.
    dvrdir.p $e |- .+ = ( +g ` R ) $.
    dvrdir.t $e |- ./ = ( /r ` R ) $.
    $( Distributive law for the division operation of a ring.  (Contributed by
       Thierry Arnoux, 30-Oct-2017.) $)
    dvrdir $p |- ( ( R e. Ring /\ ( X e. B /\ Y e. B /\ Z e. U ) ) ->
                     ( ( X .+ Y ) ./ Z ) = ( ( X ./ Z ) .+ ( Y ./ Z ) ) ) $=
      ( crg wcel co cfv wceq eqid dvrval syl2anc w3a cinvr simpr1 simpr2 unitss
      wa cmulr simpl simpr3 unitinvcl syldan sseldi rngdir syl13anc cgrp rnggrp
      adantr grpcl syl3anc oveq12d 3eqtr4d ) DMNZFANZGANZHENZUAZUFZFGCOZHDUBPZP
      ZDUGPZOZFVJVKOZGVJVKOZCOZVHHBOZFHBOZGHBOZCOVGVBVCVDVJANVLVOQVBVFUHVBVCVDV
      EUCZVBVCVDVEUDZVGEAVJADEIJUEVBVFVEVJENVBVCVDVEUIZDEVIHJVIRZUJUKULACDVKFGV
      JIKVKRZUMUNVGVHANZVEVPVLQVGDUONZVCVDWDVBWEVFDUPUQVSVTACDFGIKURUSWAABDVKEV
      IVHHIWCJWBLSTVGVQVMVRVNCVGVCVEVQVMQVSWAABDVKEVIFHIWCJWBLSTVGVDVEVRVNQVTWA
      ABDVKEVIGHIWCJWBLSTUTVA $.

    rdivmuldivd.p $e |- .x. = ( .r ` R ) $.
    rdivmuldivd.r $e |- ( ph -> R e. CRing ) $.
    rdivmuldivd.a $e |- ( ph -> X e. B ) $.
    rdivmuldivd.b $e |- ( ph -> Y e. U ) $.
    rdivmuldivd.c $e |- ( ph -> Z e. B ) $.
    rdivmuldivd.d $e |- ( ph -> W e. U ) $.
    $( Multiplication of two ratios.  Theorem I.14 of [Apostol] p. 18.
       (Contributed by Thierry Arnoux, 30-Oct-2017.) $)
    rdivmuldivd $p |- ( ph -> ( ( X ./ Y ) .x. ( Z ./ W ) ) =
                             ( ( X .x. Z ) ./ ( Y .x. W ) ) ) $=
      ( co cinvr cfv wcel wceq wa eqid dvrval oveq1d syl2anc crg crngrng unitss
      ccrg unitinvcl sseldi dvrcl syl3anc rngass syl13anc crngcom oveq2d 3eqtrd
      syl cmgp cress cplusg cgrp unitgrp unitgrpbas invrfval grpinvadd cvv fvex
      cui eqeltri mgpress sylancl fveq2d cmulr ressmulr ax-mp mgpplusg syl6reqr
      oveqd 3eqtr4d rngcl unitmulcl eqtr4d 3eqtr3rd 3eqtr4rd eqtrd ) AIJCUBZKHC
      UBZFUBZIWOJEUCUDZUDZFUBZFUBZIKFUBZJHFUBZCUBZAWPIWRFUBZWOFUBZIWRWOFUBZFUBZ
      WTAIBUEZJGUEZWPXEUFRSXHXIUGWNXDWOFBCEFGWQIJLPMWQUHZOUIUJUKAEULUEZXHWRBUEZ
      WOBUEZXEXGUFAEUOUEZXKQEUMVEZRAGBWRBEGLMUNZAXKXIWRGUEXOSEGWQJMXJUPUKUQZAXK
      KBUEZHGUEZXMXOTUABCEGKHLMOURUSZBEFIWRWOLPUTVAAXFWSIFAXNXLXMXFWSUFQXQXTBEF
      WRWOLPVBUSVCVDAXAXBWQUDZFUBZXAHWQUDZWRFUBZFUBZXCWTAYAYDXAFAJHEVFUDZGVGUBZ
      VHUDZUBZWQUDZYCWRYHUBZYAYDAYGVIUEZXIXSYJYKUFAXKYLXOEGYGMYGUHZVJVESUAGYHYG
      WQJHEGYGMYMVKYHUHEGYGWQMYMXJVLVMUSAXBYIWQAFYHJHAYHEGVGUBZVFUDZVHUDFAYGYOV
      HAXKGVNUEZYGYOUFXOGEVPUDVNMEVPVOVQZGEYNYFULVNYNUHZYFUHVRVSVTYNFYOYOUHYPFY
      NWAUDUFYQGEYNFVNYRPWBWCWDWEZWFVTAFYHYCWRYSWFWGVCAXABUEZXBGUEZXCYBUFAXKXHX
      RYTXORTBEFIKLPWHUSZAXKXIXSUUAXOSUAEFGJHMPWIUSBCEFGWQXAXBLPMXJOUIUKAXAYCFU
      BZWRFUBZIWOFUBZWRFUBZYEWTAUUCUUEWRFAUUCIKYCFUBZFUBZUUEAXKXHXRYCBUEZUUCUUH
      UFXORTAGBYCXPAXKXSYCGUEXOUAEGWQHMXJUPUKUQZBEFIKYCLPUTVAAWOUUGIFAXRXSWOUUG
      UFTUABCEFGWQKHLPMXJOUIUKVCWJUJAXKYTUUIXLUUDYEUFXOUUBUUJXQBEFXAYCWRLPUTVAA
      XKXHXMXLUUFWTUFXORXTXQBEFIWOWRLPUTVAWKWLWM $.
  $}

  ${
    $d y R $.  $d y U $.  $d y X $.
    rnginvval.b $e |- B = ( Base ` R ) $.
    rnginvval.p $e |- .* = ( .r ` R ) $.
    rnginvval.o $e |- .1. = ( 1r ` R ) $.
    rnginvval.n $e |- N = ( invr ` R ) $.
    rnginvval.u $e |- U = ( Unit ` R ) $.
    $( The ring inverse expressed in terms of multiplication.  (Contributed by
       Thierry Arnoux, 23-Oct-2017.) $)
    rnginvval $p |- ( ( R e. Ring /\ X e. U ) ->
                             ( N ` X ) = ( iota_ y e. U ( y .* X ) = .1. ) ) $=
      ( wcel wa cfv co wceq eqid cvv crg cv cmgp c0g crio unitgrpbas cplusg cui
      cress fvex eqeltri mgpplusg ressplusg invrfval grpinvval adantl unitgrpid
      ax-mp adantr eqeq2d riotabidva eqtr4d ) CUANZHDNZOHGPZAUBZHFQZCUCPZDUIQZU
      DPZRZADUEZVGERZADUEZVDVEVLRVCADFVIGHVJCDVIMVISZUFDTNFVIUGPRDCUHPTMCUHUJUK
      DFVHVITVOCFVHVHSJULUMURVJSCDVIGMVOLUNUOUPVCVNVLRVDVCVMVKADVCVFDNZOEVJVGVC
      EVJRVPCDEVIMVOKUQUSUTVAUSVB $.
  $}

  ${
    dvrcan5.b $e |- B = ( Base ` R ) $.
    dvrcan5.o $e |- U = ( Unit ` R ) $.
    dvrcan5.d $e |- ./ = ( /r ` R ) $.
    dvrcan5.t $e |- .x. = ( .r ` R ) $.
    $( Cancellation law for common factor in ratio.  ( ~ divcan5 analog.)
       (Contributed by Thierry Arnoux, 26-Oct-2016.) $)
    dvrcan5 $p |- ( ( R e. Ring /\ ( X e. B /\ Y e. U /\ Z e. U ) ) ->
      ( ( X .x. Z ) ./ ( Y .x. Z ) ) = ( X ./ Y ) ) $=
      ( wcel co cfv wceq sseldi eqid syl2anc cvv crg w3a wa cinvr unitss simpr3
      unitmulcl 3adant3r1 dvrval cmgp cress simpl unitgrp syl simpr2 unitgrpbas
      cgrp cplusg cui fvex eqeltri mgpplusg ressplusg invrfval grpinvadd oveq2d
      syl3anc cur unitrinv oveq1d 3ad2antr3 unitinvcl 3ad2antr2 rngass syl13anc
      ax-mp rnglidm 3eqtr3d 3eqtrd simpr1 dvrass 3eqtr4d ) CUAMZFAMZGEMZHEMZUBZ
      UCZFHGHDNZBNZDNZFGCUDOZOZDNZFHDNWIBNZFGBNZWHWJWMFDWHWJHWIWLOZDNZHHWLOZWMD
      NZDNZWMWHHAMZWIEMZWJWRPWHEAHACEIJUEZWCWDWEWFUFZQZWCWEWFXCWDCDEGHJLUGUHZAB
      CDEWLHWIILJWLRZKUISWHCUJOZEUKNZUQMZWEWFWRXAPWHWCXKWCWGULZCEXJJXJRZUMUNWCW
      DWEWFUOZXEXKWEWFUBWQWTHDEDXJWLGHCEXJJXMUPETMDXJUROPECUSOTJCUSUTVAEDXIXJTX
      MCDXIXIRLVBVCVPCEXJWLJXMXHVDVEVFVGWHHWSDNZWMDNZCVHOZWMDNZXAWMWCWDWFXPXRPW
      EWCWFUCXOXQWMDCDEXQWLHJXHLXQRZVIVJVKWHWCXBWSAMWMAMZXPXAPXLXFWHEAWSXDWCWDW
      FWSEMWECEWLHJXHVLVKQWHEAWMXDWCWDWEWMEMWFCEWLGJXHVLVMQZACDHWSWMILVNVOWHWCX
      TXRWMPXLYAACDXQWMILXSVQSVRVSVFWHWCWDXBXCWOWKPXLWCWDWEWFVTZXFXGABCDEFHWIIJ
      KLWAVOWHWDWEWPWNPYBXNABCDEWLFGILJXHKUISWB $.
  $}

  ${
    $( If ` A ` is a subring of ` R ` , then they have the same characteristic.
       (Contributed by Thierry Arnoux, 24-Feb-2018.) $)
    subrgchr $p |- ( A e. ( SubRing ` R ) ->
      ( chr ` ( R |`s A ) ) = ( chr ` R ) ) $=
      ( csubrg cfv wcel cress cur cod cchr csubg wceq subrgsubg subrg1cl subgod
      co eqid syl2anc subrg1 fveq2d chrval eqtr2d 3eqtr3g ) ABCDEZBAFOZGDZUDHDZ
      DZBGDZBHDZDZUDIDZBIDZUCUJUHUFDZUGUCABJDEUHAEUJUMKABLABUHUHPZMUHUFBUDUIAUD
      PZUIPZUFPZNQUCUHUEUFABUDUHUOUNRSUAUKUDUEUFUQUEPUKPTULBUHUIUPUNULPTUB $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
    Ordered rings and fields
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c oRing $.
  $c oField $.

  $( Extend class notation with the class of all ordered rings. $)
  corng $a class oRing $.

  $( Extend class notation with the class of all ordered fields. $)
  cofld $a class oField $.

  ${
    $d a b f l r t v z $.
    $( Define class of all ordered rings.  An ordered ring is a ring with a
       total ordering compatible with its operations.  (Contributed by Thierry
       Arnoux, 23-Mar-2018.) $)
    df-orng $a |- oRing = { r e. ( Ring i^i oGrp ) | [. ( Base ` r ) / v ].
      [. ( 0g ` r ) / z ]. [. ( .r ` r ) / t ]. [. ( le ` r ) / l ].
      A. a e. v A. b e. v ( ( z l a /\ z l b ) -> z l ( a t b ) ) } $.

    $( Define class of all ordered fields.  An ordered field is a field with a
       total ordering compatible with its operations.  (Contributed by Thierry
       Arnoux, 18-Jan-2018.) $)
    df-ofld $a |- oField = ( Field i^i oRing ) $.
  $}

  ${
    $d a b l r t v z B $.  $d a b l r t v z R $.  $d l r t z .0. $.
    $d l r .<_ $.  $d l r t .x. $.
    isorng.0 $e |- B = ( Base ` R ) $.
    isorng.1 $e |- .0. = ( 0g ` R ) $.
    isorng.2 $e |- .x. = ( .r ` R ) $.
    isorng.3 $e |- .<_ = ( le ` R ) $.
    $( An ordered ring is a ring with a total ordering compatible with its
       operations.  (Contributed by Thierry Arnoux, 18-Jan-2018.) $)
    isorng $p |- ( R e. oRing <-> ( R e. Ring /\ R e. oGrp /\
      A. a e. B A. b e. B ( ( .0. .<_ a /\ .0. .<_ b )
        -> .0. .<_ ( a .x. b ) ) ) ) $=
      ( vl vt wcel wbr wa wral cfv wsbc wceq vz vv vr crg cogrp cin cv co corng
      wi w3a elin anbi1i cple cmulr c0g cbs cvv fvex simpr simpl fveq2d syl6eqr
      a1i eqtrd oveqd breq2d imbi2d 2ralbidv sbcbidv sbcied wb fveq2 raleqbi1dv
      adantr raleq breq1d anbi12d imbi12d bitr2d 3bitr3d df-orng elrab2 3bitr4i
      syl breqd df-3an ) BUDUEUFZNZEFUGZDOZEGUGZDOZPZEWJWLCUHZDOZUJZGAQFAQZPBUD
      NZBUENZPZWRPBUINWSWTWRUKWIXAWRBUDUEULUMUAUGZWJLUGZOZXBWLXCOZPZXBWJWLMUGZU
      HZXCOZUJZGUBUGZQZFXKQZLUCUGZUNRZSZMXNUORZSZUAXNUPRZSZUBXNUQRZSZWRUCBWHUIX
      NBTZEWJXCOZEWLXCOZPZEXHXCOZUJZGAQFAQZLXOSZMXQSZYFEWOXCOZUJZGAQFAQZLXOSZYB
      WRYCYJYOMXQURXQURNYCXNUOUSVDYCXGXQTZPZYIYNLXOYQYHYMFGAAYQYGYLYFYQXHWOEXCY
      QXGCWJWLYQXGXQCYCYPUTYQXQBUORCYQXNBUOYCYPVAVBJVCVEVFVGVHVIVJVKYCYBXJGAQZF
      AQZLXOSZMXQSZUAXSSZYKYCXTUUBUBYAURYAURNYCXNUQUSVDYCXKYATZPZXRUUAUAXSUUDXP
      YTMXQUUDXMYSLXOUUDXKATXMYSVLUUDXKYAAYCUUCUTYCYAATUUCYCYABUQRAXNBUQVMHVCVO
      VEXLYRFXKAXJGXKAVPVNWEVJVJVJVKYCUUAYKUAXSURXSURNYCXNUPUSVDYCXBXSTZPZYTYJM
      XQUUFYSYILXOUUFXJYHFGAAUUFXFYFXIYGUUFXDYDXEYEUUFXBEWJXCUUFXBXSEYCUUEUTYCX
      SETUUEYCXSBUPREXNBUPVMIVCVOVEZVQUUFXBEWLXCUUGVQVRUUFXBEXHXCUUGVQVSVIVJVJV
      KVTYCYNWRLXOURXOURNYCXNUNUSVDYCXCXOTZPZYMWQFGAAUUIYFWNYLWPUUIYDWKYEWMUUIX
      CDEWJUUIXCXODYCUUHUTUUIXOBUNRDUUIXNBUNYCUUHVAVBKVCVEZWFUUIXCDEWLUUJWFVRUU
      IXCDEWOUUJWFVSVIVKWAUAUBMUCFGLWBWCWSWTWRWGWD $.
  $}

  ${
    $d a b R $.
    $( An ordered ring is a ring.  (Contributed by Thierry Arnoux,
       23-Mar-2018.) $)
    orngrng $p |- ( R e. oRing -> R e. Ring ) $=
      ( va vb corng wcel crg cogrp c0g cfv cv cple wbr wa cmulr co wi wral eqid
      cbs isorng simp1bi ) ADEAFEAGEAHIZBJZAKIZLUBCJZUDLMUBUCUEANIZOUDLPCASIZQB
      UGQUGAUFUDUBBCUGRUBRUFRUDRTUA $.

    $( An ordered ring is an ordered group.  (Contributed by Thierry Arnoux,
       23-Mar-2018.) $)
    orngogrp $p |- ( R e. oRing -> R e. oGrp ) $=
      ( va vb corng wcel crg cogrp c0g cfv cv cple wbr wa cmulr co wi wral eqid
      cbs isorng simp2bi ) ADEAFEAGEAHIZBJZAKIZLUBCJZUDLMUBUCUEANIZOUDLPCASIZQB
      UGQUGAUFUDUBBCUGRUBRUFRUDRTUA $.
  $}

  $( An ordered field is a field with a total ordering compatible with its
    operations.  (Contributed by Thierry Arnoux, 23-Mar-2018.) $)
  isofld $p |- ( F e. oField <-> ( F e. Field /\ F e. oRing ) ) $=
    ( cfield corng cofld df-ofld elin2 ) ABCDEF $.

  ${
    $d a b B $.  $d a b R $.  $d a b X $.  $d b Y $.  $d a b .0. $.
    $d a b .<_ $.  $d a b .x. $.
    orngmul.0 $e |- B = ( Base ` R ) $.
    orngmul.1 $e |- .<_ = ( le ` R ) $.
    orngmul.2 $e |- .0. = ( 0g ` R ) $.
    orngmul.3 $e |- .x. = ( .r ` R ) $.
    $( In an ordered field, the ordering is compatible with the ring
       multiplication operation.  (Contributed by Thierry Arnoux,
       20-Jan-2018.) $)
    orngmul $p |- ( ( R e. oRing
      /\ ( X e. B /\ .0. .<_ X ) /\ ( Y e. B /\ .0. .<_ Y ) )
      -> .0. .<_ ( X .x. Y ) ) $=
      ( va vb wcel wbr wa co cv wi wral w3a simp2r simp3r jca simp2l simp3l crg
      corng cogrp isorng simp3bi 3ad2ant1 wceq breq2 biidd anbi12d oveq1 breq2d
      imbi12d oveq2 rspc2v imp syl21anc mpd ) BUHNZEANZGEDOZPZFANZGFDOZPZUAZVGV
      JPZGEFCQZDOZVLVGVJVEVFVGVKUBVEVHVIVJUCUDVLVFVIGLRZDOZGMRZDOZPZGVPVRCQZDOZ
      SZMATLATZVMVOSZVEVFVGVKUEVEVHVIVJUFVEVHWDVKVEBUGNBUINWDABCDGLMHJKIUJUKULV
      FVIPWDWEWCWEVGVSPZGEVRCQZDOZSLMEFAAVPEUMZVTWFWBWHWIVQVGVSVSVPEGDUNWIVSUOU
      PWIWAWGGDVPEVRCUQURUSVRFUMZWFVMWHVOWJVGVGVSVJWJVGUOVRFGDUNUPWJWGVNGDVRFEC
      UTURUSVAVBVCVD $.

    $( In an ordered field, all squares are positive.  (Contributed by
       Thierry Arnoux, 20-Jan-2018.) $)
    orngsqr $p |- ( ( R e. oRing /\ X e. B ) -> .0. .<_ ( X .x. X ) ) $=
      ( wcel wa wbr co syl3anc cfv syl eqid wceq wo corng simpll simplr orngmul
      simpr jca wn cminusg cgrp orngrng ad2antrr rnggrp grpinvcl syl2anc cplusg
      crg comnd w3a cogrp orngogrp isogrp simprbi grpidcl 3jca cplt simpl pltle
      wi 3syl con3d imp sylan w3o wor ctos omndtos cid cres wss tosso ibi solin
      simpld syl12anc 3orass sylib orel1 sylc orcom eqcom orbi2i bitri mpbi cpo
      imbi2i wb tospos pleval2 mpbird omndadd grprinv grplid rngm2neg pm2.61dan
      3brtr3d breqtrd ) BUAKZEAKZLZFEDMZFEECNZDMZXIXJLZXGXHXJLZXNXLXGXHXJUBXMXH
      XJXGXHXJUCXIXJUEUFZXOABCDEEFGHIJUDOXIXJUGZLZFEBUHPZPZXSCNZXKDXQXGXSAKZFXS
      DMZLZYCFXTDMXGXHXPUBZXQYAYBXQBUIKZXHYAXQBUPKZYEXGYFXHXPBUJZUKZBULZQZXGXHX
      PUCZABXREGXRRZUMUNZXQEXSBUOPZNZFXSYNNZFXSDXQBUQKZXHFAKZYAUREFDMZYOYPDMXQX
      GYQYDXGBUSKZYQBUTYTYEYQBVAVBQZQXQXHYRYAYKXQYEYRYJABFGIVCZQZYMVDXQYSEFBVEP
      ZMZEFSZTZXQFESZUUETZVHXQUUGVHXQFEUUDMZUGZUUJUUITZUUIXIXGYRXHURZXPUUKXIXGY
      RXHXGXHVFZXIXGYRUUNXGYFYEYRYGYIUUBVIQXGXHUEVDUUMXPUUKUUMUUJXJUAAAUUDBDFEH
      UUDRZVGVJVKVLXQUUJUUHUUEVMZUULXQAUUDVNZYRXHUUPXQXGBVOKZUUQYDXGYQUURUUABVP
      QZUURUUQVQAVRDVSZUURUUQUUTLAUUDBDVOGHUUOVTWAWCVIUUCYKAFEUUDWBWDUUJUUHUUEW
      EWFUUJUUIWGWHUUIUUGXQUUIUUEUUHTUUGUUHUUEWIUUHUUFUUEFEWJWKWLWOWMXQBWNKZXHY
      RYSUUGWPXQXGUURUVAYDUUSBWQVIYKUUCAUUDBDEFGHUUOWROWSAYNDBEFXSGHYNRZWTOXQYE
      XHYOFSYJYKAYNBXREFGUVBIYLXAUNXQYEYAYPXSSYJYMAYNBXSFGUVBIXBUNXEUFZUVCABCDX
      SXSFGHIJUDOXQABCXREEGJYLYHYKYKXCXFXD $.
  $}

  ${
    orngmullt.b $e |- B = ( Base ` R ) $.
    orngmullt.t $e |- .x. = ( .r ` R ) $.
    orngmullt.0 $e |- .0. = ( 0g ` R ) $.
    orngmullt.1 $e |- ( ph -> R e. oRing ) $.
    orngmullt.2 $e |- ( ph -> X e. B ) $.
    orngmullt.3 $e |- ( ph -> Y e. B ) $.
    orngmullt.4 $e |- ( ph -> Z e. B ) $.
    ${
      orngmulle.l $e |- .<_ = ( le ` R ) $.
      orngmulle.5 $e |- ( ph -> X .<_ Y ) $.
      orngmulle.6 $e |- ( ph -> .0. .<_ Z ) $.
      $( In an ordered ring, multiplication with a positive does not change
         comparison.  (Contributed by Thierry Arnoux, 10-Apr-2018.) $)
      ornglmulle $p |- ( ph -> ( Z .x. X ) .<_ ( Z .x. Y ) ) $=
        ( wcel co cplusg cfv csg comnd wbr cogrp corng orngogrp syl cgrp isogrp
        simprbi crg orngrng rnggrp grpidcl rngcl syl3anc eqid grpsubcl grpsubid
        wceq syl2anc ogrpsub syl131anc eqbrtrrd orngmul rngsubdi breqtrd grplid
        syl122anc omndadd grpnpcan 3brtr3d ) AHIFDUAZCUBUCZUAZIGDUAZVPCUDUCZUAZ
        VPVQUAZVPVSEACUETZHBTZWABTZVPBTZHWAEUFVRWBEUFACUGTZWCACUHTZWGMCUIUJZWGC
        UKTZWCCULUMUJAWJWDACUNTZWJAWHWKMCUOUJZCUPUJZBCHJLUQUJAWJVSBTZWFWEWMAWKI
        BTZGBTZWNWLPOBCDIGJKURUSZAWKWOFBTZWFWLPNBCDIFJKURUSZBCVTVSVPJVTUTZVAUSW
        SAHIGFVTUAZDUAZWAEAWHWOHIEUFXABTZHXAEUFHXBEUFMPSAWJWPWRXCWMONBCVTGFJWTV
        AUSAFFVTUAZHXAEAWJWRXDHVCWMNBCVTFHJLWTVBVDAWGWRWPWRFGEUFXDXAEUFWINONRBC
        EVTFGFJQWTVEVFVGBCDEIXAHJQLKVHVLABCDVTIGFJKWTWLPONVIVJBVQECHWAVPJQVQUTZ
        VMVFAWJWFVRVPVCWMWSBVQCVPHJXELVKVDAWJWNWFWBVSVCWMWQWSBVQCVTVSVPJXEWTVNU
        SVO $.

      $( In an ordered ring, multiplication with a positive does not change
         comparison.  (Contributed by Thierry Arnoux, 10-Apr-2018.) $)
      orngrmulle $p |- ( ph -> ( X .x. Z ) .<_ ( Y .x. Z ) ) $=
        ( wcel co cplusg cfv csg comnd wbr cogrp corng orngogrp syl cgrp isogrp
        simprbi crg orngrng rnggrp grpidcl rngcl syl3anc eqid grpsubcl grpsubid
        wceq syl2anc ogrpsub syl131anc orngmul syl122anc breqtrd omndadd grplid
        eqbrtrrd rngsubdir grpnpcan 3brtr3d ) AHFIDUAZCUBUCZUAZGIDUAZVPCUDUCZUA
        ZVPVQUAZVPVSEACUETZHBTZWABTZVPBTZHWAEUFVRWBEUFACUGTZWCACUHTZWGMCUIUJZWG
        CUKTZWCCULUMUJAWJWDACUNTZWJAWHWKMCUOUJZCUPUJZBCHJLUQUJAWJVSBTZWFWEWMAWK
        GBTZIBTZWNWLOPBCDGIJKURUSZAWKFBTZWPWFWLNPBCDFIJKURUSZBCVTVSVPJVTUTZVAUS
        WSAHGFVTUAZIDUAZWAEAWHXABTZHXAEUFWPHIEUFHXBEUFMAWJWOWRXCWMONBCVTGFJWTVA
        USAFFVTUAZHXAEAWJWRXDHVCWMNBCVTFHJLWTVBVDAWGWRWOWRFGEUFXDXAEUFWINONRBCE
        VTFGFJQWTVEVFVLPSBCDEXAIHJQLKVGVHABCDVTGFIJKWTWLONPVMVIBVQECHWAVPJQVQUT
        ZVJVFAWJWFVRVPVCWMWSBVQCVPHJXELVKVDAWJWNWFWBVSVCWMWQWSBVQCVTVSVPJXEWTVN
        USVO $.
    $}

    ${
      orngmullt.l $e |- .< = ( lt ` R ) $.
      orngmullt.d $e |- ( ph -> R e. DivRing ) $.
      orngmullt.5 $e |- ( ph -> X .< Y ) $.
      orngmullt.6 $e |- ( ph -> .0. .< Z ) $.
      $( In an ordered ring, multiplication with a positive does not change
         strict comparison.  (Contributed by Thierry Arnoux, 9-Apr-2018.) $)
      ornglmullt $p |- ( ph -> ( Z .x. X ) .< ( Z .x. Y ) ) $=
        ( co wbr cple cfv wne eqid corng wcel w3a imp syl31anc crg cgrp orngrng
        pltle syl rnggrp grpidcl 3syl ornglmulle wceq wa cinvr simpr oveq2d cur
        cui cdr pltne necomd drngunit biimpar syl12anc unitlinv oveq1d rnginvcl
        syl2anc rngass syl13anc rnglidm 3eqtr3d adantr neneqd pm2.65da wb rngcl
        neneqad syl3anc pltval mpbir2and ) AIFEUAZIGEUAZDUBZWKWLCUCUDZUBZWKWLUE
        ZABCEWNFGHIJKLMNOPWNUFZACUGUHZFBUHZGBUHZFGDUBZFGWNUBZMNOSWRWSWTUIZXAXBU
        GBBDCWNFGWQQUOUJUKAWRHBUHZIBUHZHIDUBZHIWNUBZMACULUHZCUMUHXDAWRXHMCUNUPZ
        CUQBCHJLURUSZPTWRXDXEUIZXFXGUGBBDCWNHIWQQUOUJUKUTAWKWLAWKWLVAZFGVAAXLVB
        ZICVCUDZUDZWKEUAZXOWLEUAZFGXMWKWLXOEAXLVDVEAXPFVAXLAXOIEUAZFEUAZCVFUDZF
        EUAZXPFAXRXTFEAXHICVGUDZUHZXRXTVAXIACVHUHZXEIHUEZYCRPAHIAWRXDXEXFHIUEZM
        XJPTXKXFYFUGBBDCHIQVIUJUKVJYDYCXEYEVBBCYBIHJYBUFZLVKVLVMZCEYBXTXNIYGXNU
        FZKXTUFZVNVQZVOAXHXOBUHZXEWSXSXPVAXIAXHYCYLXIYHBCYBXNIYGYIJVPVQZPNBCEXO
        IFJKVRVSAXHWSYAFVAXINBCEXTFJKYJVTVQWAWBAXQGVAXLAXRGEUAZXTGEUAZXQGAXRXTG
        EYKVOAXHYLXEWTYNXQVAXIYMPOBCEXOIGJKVRVSAXHWTYOGVAXIOBCEXTGJKYJVTVQWAWBW
        AXMFGAFGUEZXLAWRWSWTXAYPMNOSXCXAYPUGBBDCFGQVIUJUKWBWCWDWGAWRWKBUHZWLBUH
        ZWMWOWPVBWEMAXHXEWSYQXIPNBCEIFJKWFWHAXHXEWTYRXIPOBCEIGJKWFWHUGBBDCWNWKW
        LWQQWIWHWJ $.

      $( In an ordered ring, multiplication with a positive does not change
         strict comparison.  (Contributed by Thierry Arnoux, 9-Apr-2018.) $)
      orngrmullt $p |- ( ph -> ( X .x. Z ) .< ( Y .x. Z ) ) $=
        ( co wbr cple cfv wne eqid corng wcel w3a imp syl31anc crg cgrp orngrng
        pltle syl rnggrp grpidcl 3syl orngrmulle wceq cdvr simpr oveq1d cui cdr
        wa pltne necomd drngunit biimpar syl12anc dvrcan3 syl3anc adantr neneqd
        3eqtr3d pm2.65da neneqad wb rngcl pltval mpbir2and ) AFIEUAZGIEUAZDUBZW
        DWECUCUDZUBZWDWEUEZABCEWGFGHIJKLMNOPWGUFZACUGUHZFBUHZGBUHZFGDUBZFGWGUBZ
        MNOSWKWLWMUIZWNWOUGBBDCWGFGWJQUOUJUKAWKHBUHZIBUHZHIDUBZHIWGUBZMACULUHZC
        UMUHWQAWKXAMCUNUPZCUQBCHJLURUSZPTWKWQWRUIZWSWTUGBBDCWGHIWJQUOUJUKUTAWDW
        EAWDWEVAZFGVAAXEVGZWDICVBUDZUAZWEIXGUAZFGXFWDWEIXGAXEVCVDAXHFVAZXEAXAWL
        ICVEUDZUHZXJXBNACVFUHZWRIHUEZXLRPAHIAWKWQWRWSHIUEZMXCPTXDWSXOUGBBDCHIQV
        HUJUKVIXMXLWRXNVGBCXKIHJXKUFZLVJVKVLZBXGCEXKFIJXPXGUFZKVMVNVOAXIGVAZXEA
        XAWMXLXSXBOXQBXGCEXKGIJXPXRKVMVNVOVQXFFGAFGUEZXEAWKWLWMWNXTMNOSWPWNXTUG
        BBDCFGQVHUJUKVOVPVRVSAWKWDBUHZWEBUHZWFWHWIVGVTMAXAWLWRYAXBNPBCEFIJKWAVN
        AXAWMWRYBXBOPBCEGIJKWAVNUGBBDCWGWDWEWJQWBVNWC $.
    $}
  $}

  $( An ordered field is a field.  (Contributed by Thierry Arnoux,
     20-Jan-2018.) $)
  ofldfld $p |- ( F e. oField -> F e. Field ) $=
    ( cofld wcel cfield corng isofld simplbi ) ABCADCAECAFG $.

  $( An ordered field is a totally ordered set.  (Contributed by Thierry
     Arnoux, 20-Jan-2018.) $)
  ofldtos $p |- ( F e. oField -> F e. Toset ) $=
    ( cofld wcel comnd ctos corng cogrp cfield isofld orngogrp cgrp isogrp 3syl
    simprbi omndtos syl ) ABCZADCZAECQAFCZAGCZRQAHCSAINAJTAKCRALNMAOP $.

  ${
    orng0le1.1 $e |- .0. = ( 0g ` F ) $.
    orng0le1.2 $e |- .1. = ( 1r ` F ) $.
    ${
      orng0le1.3 $e |- .<_ = ( le ` F ) $.
      $( In an ordered ring, the ring unit is positive.  (Contributed by
         Thierry Arnoux, 21-Jan-2018.) $)
      orng0le1 $p |- ( F e. oRing -> .0. .<_ .1. ) $=
        ( corng wcel cmulr cfv co cbs wbr crg orngrng eqid rngidcl syl orngsqr
        mpdan wceq rnglidm syl2anc breqtrd ) BHIZDAABJKZLZACUFABMKZIZDUHCNUFBOI
        ZUJBPZUIBAUIQZFRSZUIBUGCADUMGEUGQZTUAUFUKUJUHAUBULUNUIBUGAAUMUOFUCUDUE
        $.
    $}

    ${
      ofld0lt1.3 $e |- .< = ( lt ` F ) $.
      $( In an ordered field, the ring unit is strictly positive.  (Contributed
         by Thierry Arnoux, 21-Jan-2018.) $)
      ofldlt1 $p |- ( F e. oField -> .0. .< .1. ) $=
        ( cofld wcel wbr cple cfv wne corng cfield cvv c0g fvex eqeltri cur syl
        isofld simprbi eqid orng0le1 cdr ofldfld ccrg isfld simplbi 3syl necomd
        drngunz wa wb pltval mp3an23 mpbir2and ) CHIZDBAJZDBCKLZJZDBMZUSCNIZVBU
        SCOIZVDCUBUCBCVADEFVAUDZUEUAUSBDUSVECUFIZBDMCUGVEVGCUHICUIUJCBDEFUMUKUL
        USDPIBPIUTVBVCUNUODCQLPECQRSBCTLPFCTRSHPPACVADBVFGUPUQUR $.
    $}
  $}

  ${
    $d m n F $.  $d n y F $.
    $( The characteristic of an ordered field is zero.  (Contributed by Thierry
       Arnoux, 21-Jan-2018.) $)
    ofldchr $p |- ( F e. oField -> ( chr ` F ) = 0 ) $=
      ( vy wcel cfv cc0 eqid co wceq cn 3syl wa wbr wi c1 breq2d imbi2d syl3anc
      oveq1 syl cvv vn vm cofld cchr cur cod chrval cv cmg c0g crab c0 clt ccnv
      cr csup cif crg cbs cfield cdr ofldfld ccrg isfld simplbi drngrng rngidcl
      odval wn wral cplt wne caddc ofldlt1 breqtrrd cpo w3a ctos ofldtos tospos
      mulg1 ad2antlr cgrp rnggrp grpidcl grpmnd simpll mulgnncl peano2nnd simpr
      cmnd cplusg cogrp simplr isofld simprbi orngogrp ogrpaddlt grplid syl2anc
      3jca corng eqcomd mulgnnp1 ccmn rngcmn cmncom eqtrd 3brtr4d jca plttr imp
      syl21anc ex a2d nnind impcom fvex ovex pltne mp3an23 adantr necomd neneqd
      mpd ralrimiva rabeq0 sylibr iftrue syl5eqr ) AUCCZAUDDZAUEDZAUFDZDZEYLAYM
      YNYNFZYMFZYLFUGYKYOBUHZYMAUIDZGZAUJDZHZBIUKZULHZEUUCUOUMUNUPZUQZEYKAURCZY
      MAUSDZCZYOUUFHYKAUTCZAVACZUUGAVBUUJUUKAVCCAVDVEAVFJZUUHAYMUUHFZYQVGZBYMYS
      AUUCYNUUHUUAUUMYSFZUUAFZYPUUCFVHJYKUUDUUFEHYKUUBVIZBIVJUUDYKUUQBIYKYRICZK
      ZYTUUAUUSUUAYTUUSUUAYTAVKDZLZUUAYTVLZUURYKUVAYKUUAUAUHZYMYSGZUUTLZMYKUUAN
      YMYSGZUUTLZMYKUUAUBUHZYMYSGZUUTLZMYKUUAUVHNVMGZYMYSGZUUTLZMYKUVAMUAUBYRUV
      CNHZUVEUVGYKUVNUVDUVFUUAUUTUVCNYMYSROPUVCUVHHZUVEUVJYKUVOUVDUVIUUAUUTUVCU
      VHYMYSROPUVCUVKHZUVEUVMYKUVPUVDUVLUUAUUTUVCUVKYMYSROPUVCYRHZUVEUVAYKUVQUV
      DYTUUAUUTUVCYRYMYSROPYKUUAYMUVFUUTUUTYMAUUAUUPYQUUTFZVNZYKUUIUVFYMHYKUUGU
      UIUULUUNSZUUHYSAYMUUMUUOWASVOUVHICZYKUVJUVMUWAYKUVJUVMMUWAYKKZUVJUVMUWBUV
      JKZAVPCZUUAUUHCZUVIUUHCZUVLUUHCZVQZUVJUVIUVLUUTLZKZUVMYKUWDUWAUVJYKAVRCUW
      DAVSAVTSWBUWCUWEUWFUWGUWCAWCCZUWEYKUWKUWAUVJYKUUGUWKUULAWDSWBZUUHAUUAUUMU
      UPWESZUWCAWKCZUWAUUIUWFUWCUWKUWNUWLAWFSZUWAYKUVJWGZYKUUIUWAUVJUVTWBZUUHYS
      AUVHYMUUMUUOWHQZUWCUWNUVKICUUIUWGUWOUWCUVHUWPWIUWQUUHYSAUVKYMUUMUUOWHQXAU
      WCUVJUWIUWBUVJWJUWCUUAUVIAWLDZGZYMUVIUWSGZUVIUVLUUTUWCAWMCZUWEUUIUWFVQUUA
      YMUUTLZUWTUXAUUTLUWCYKAXBCZUXBUWAYKUVJWNZYKUUJUXDAWOWPAWQJUWCUWEUUIUWFUWM
      UWQUWRXAUWCYKUXCUXEUVSSUUHUWSUUTAUUAYMUVIUUMUVRUWSFZWRQUWCUWTUVIUWCUWKUWF
      UWTUVIHUWLUWRUUHUWSAUVIUUAUUMUXFUUPWSWTXCUWCUVLUVIYMUWSGZUXAUWCUWAUUIUVLU
      XGHUWPUWQUUHUWSYSAUVHYMUUMUUOUXFXDWTUWCAXECZUWFUUIUXGUXAHUWCYKUUGUXHUXEUU
      LAXFJUWRUWQUUHUWSAUVIYMUUMUXFXGQXHXIXJUWDUWHKUWJUVMUUHUUTAUUAUVIUVLUUMUVR
      XKXLXMXNXNXOXPXQYKUVAUVBMZUURYKUUATCYTTCUXIAUJXRYRYMYSXSUCTTUUTAUUAYTUVRX
      TYAYBYEYCYDYFUUBBIYGYHUUDEUUEYISXHYJ $.
  $}

  ${
    $d a b c x y A $.  $d a b x y R $.
    $( Every subring of an ordered ring is also an ordered ring.  (Contributed
       by Thierry Arnoux, 21-Jan-2018.) $)
    suborng $p |- ( ( R e. oRing /\ ( R |`s A ) e. Ring )
      -> ( R |`s A ) e. oRing ) $=
      ( va vb wcel cress co wa c0g cfv wbr cbs cgrp syl jca c0 wceq eqid adantr
      cvv corng crg cogrp cv cple cmulr wi wral w3a simpr comnd rnggrp orngogrp
      isogrp simprbi rngmnd anim12i submomnd sylibr simp-4l wn reldmress ovprc2
      cmnd wss fveq2d adantl base0 syl6eqr wne cur rngidcl ne0i ad2antlr neneqd
      condan ressbas inss2 syl6eqssr ad3antrrr simpllr sseldd simprl wb orngrng
      cin csubg ressinbas oveq2d eqtrd eqeltrrd 3jca issubg subg0 eqtr4d ressle
      ad2antrr eqidd breq123d mpbird simplr simprr orngmul ressmulr oveqd mpbid
      syl3anc ex anasss ralrimivva isorng ) BUAEZBAFGZUBEZHZXNXMUCEZXMIJZCUDZXM
      UEJZKZXQDUDZXSKZHZXQXRYAXMUFJZGZXSKZUGZDXMLJZUHCYHUHZUIXMUAEXOXNXPYIXLXNU
      JZXOXMMEZXMUKEZHXPXOYKYLXOXNYKYJXMULNZXOBUKEZXMVDEZHYLXLYNXNYOXLBUCEZYNBU
      MYPBMEZYNBUNUONXMUPUQABURNOXMUNUSXOYGCDYHYHXOXRYHEZYAYHEZYGXOYRHZYSHZYCYF
      UUAYCHZBIJZXRYABUFJZGZBUEJZKZYFUUBXLXRBLJZEZUUCXRUUFKZHYAUUHEZUUCYAUUFKZH
      UUGXLXNYRYSYCUTUUBUUIUUJUUBYHUUHXRXOYHUUHVEZYRYSYCXOATEZUUMXOUUNYHPQXOUUN
      VAZHZYHPLJZPUUOYHUUQQXOUUOXMPLBAFVBVCVFVGVHVIUUPYHPXNYHPVJZXLUUOXNXMVKJZY
      HEUURYHXMUUSYHRZUUSRVLYHUUSVMNVNVOVPZUUNYHAUUHWFZUUHAUUHXMTBXMRZUUHRZVQZA
      UUHVRVSNZVTZXOYRYSYCWAWBUUBUUJXTUUAXTYBWCUUAUUJXTWDYCUUAUUCXQXRXRUUFXSXOU
      UCXQQZYRYSXOUUCBYHFGZIJZXQXOYHBWGJEZUUCUVJQXOYQUUMUVIMEZUIUVKXOYQUUMUVLXL
      YQXNXLBUBEYQBWEBULNSUVFXOXMUVIMXOUUNXMUVIQUVAUUNXMBUVBFGUVIAUUHBTUVDWHUUN
      UVBYHBFUVEWIWJNZYMWKWLUUHYHBUVDWMUSYHBUVIUUCUVIRUUCRZWNNXOXMUVIIUVMVFWOWQ
      ZUUAUUNUUFXSQZXOUUNYRYSUVAWQZABUUFTXMUVCUUFRZWPNZUUAXRWRWSSWTOUUBUUKUULUU
      BYHUUHYAUVGYTYSYCXAWBUUBUULYBUUAXTYBXBUUAUULYBWDYCUUAUUCXQYAYAUUFXSUVOUVS
      UUAYAWRWSSWTOUUHBUUDUUFXRYAUUCUVDUVRUVNUUDRZXCXGUUBUUCXQUUEYEUUFXSUUAUVHY
      CUVOSUUAUVPYCUVSSUUBUUDYDXRYAUUBUUNUUDYDQUUAUUNYCUVQSABXMUUDTUVCUVTXDNXEW
      SXFXHXIXJWLYHXMYDXSXQCDUUTXQRYDRXSRXKUS $.
  $}

  $( Every subfield of an ordered field is also an ordered field.
     (Contributed by Thierry Arnoux, 21-Jan-2018.) $)
  subofld $p |- ( ( F e. oField /\ ( F |`s A ) e. Field )
    -> ( F |`s A ) e. oField ) $=
    ( cofld wcel cress co cfield corng simpr crg isofld simprbi adantr ccrg cdr
    wa isfld crngrng 3syl suborng syl2anc jca sylibr ) BCDZBAEFZGDZPZUFUEHDZPUE
    CDUGUFUHUDUFIZUGBHDZUEJDZUHUDUJUFUDBGDUJBKLMUGUFUENDZUKUIUFUEODULUEQLUERSAB
    TUAUBUEKUC $.

  ${
    $d n x y z B $.  $d n x y z W $.  $d x y z H $.  $d n x y z .< $. 
    isarchiofld.b $e |- B = ( Base ` W ) $.
    isarchiofld.h $e |- H = ( ZRHom ` W ) $.
    isarchiofld.l $e |- .< = ( lt ` W ) $.
    $( Axiom of Archimedes : a characterization of the Archimedean property for
       ordered fields.  (Contributed by Thierry Arnoux, 9-Apr-2018.) $)
    isarchiofld $p |- ( W e. oField ->
      ( W e. Archi <-> A. x e. B E. n e. NN x .< ( H ` n ) ) ) $=
      ( wcel cfv wbr co cn wral eqid 3syl wceq syl wa vy vz cofld carchi c0g cv
      cmg wi corng cogrp wb cfield isofld simprbi orngogrp isarchi3 cur orngrng
      wrex crg rngidcl breq2 oveq2 breq2d rexbidv imbi12d ralbidv rspcv ofldlt1
      pm5.5 sylibd cz nnz ccnfld cress zrhmulg syl2an rexbidva sylibrd nfv nfan
      nfra1 cdvr cui ad3antrrr simplrr wne simplrl simpr simplll rnggrp grpidcl
      cgrp pltne syl3anc mpd necomd simplbi ccrg isfld drngunit mpbir2and dvrcl
      cdr breq1 cbvralv sylib ad2antrr imp syl2anc cmulr simp-4l simp-4r simprd
      simpld simpllr simplr mulgcl eqeltrd orngrmullt dvrcan1 mulgass2 syl13anc
      oveq1d rnglidm oveq2d 3brtr3d ex reximdva adantllr expr ralrimi ralrimiva
      3eqtrd impbid bitrd ) FUCJZFUDJZFUEKZUAUFZCLZAUFZDUFZYTFUGKZMZCLZDNUSZUHZ
      ABOZUABOZUUBUUCEKZCLZDNUSZABOZYQFUIJZFUJJYRUUJUKYQFULJZUUOFUMZUNZFUOUAABC
      UUDDFYSGYSPZIUUDPZUPQYQUUJUUNYQUUJUUBUUCFUQKZUUDMZCLZDNUSZABOZUUNYQUUJYSU
      VACLZUVDUHZABOZUVEYQUVABJZUUJUVHUHYQUUOFUTJZUVIUURFURZBFUVAGUVAPZVAZQUUIU
      VHUAUVABYTUVARZUUHUVGABUVNUUAUVFUUGUVDYTUVAYSCVBUVNUUFUVCDNUVNUUEUVBUUBCY
      TUVAUUCUUDVCVDVEVFVGVHSYQUVGUVDABYQUVFUVGUVDUKCUVAFYSUUSUVLIVIUVFUVDVJSVG
      VKYQUUMUVDABYQUULUVCDNYQUUCNJZTUUKUVBUUBCYQUVJUUCVLJZUUKUVBRZUVOYQUUOUVJU
      URUVKSZUUCVMZFUUDUVAEUUCVNVLVOMZUVTPHUUTUVLVPVQZVDVRVGVSYQUUNUUJYQUUNTZUU
      IUABUWBYTBJZTUUHABUWBUWCAYQUUNAYQAVTUUMABWBWAUWCAVTWAUWBUWCUUBBJZUUHUWBUW
      CUWDTZTZUUAUUGUWFUUATZUUBYTFWCKZMZUUKCLZDNUSZUUGUWGUWIBJZUBUFZUUKCLZDNUSZ
      UBBOZUWKUWGUVJUWDYTFWDKZJZUWLYQUVJUUNUWEUUAUVRWEZUWBUWCUWDUUAWFUWGUWRUWCY
      TYSWGZUWBUWCUWDUUAWHZUWGYSYTUWGUUAYSYTWGZUWFUUAWIUWGYQYSBJZUWCUUAUXBUHZYQ
      UUNUWEUUAWJZUWGUVJFWMJZUXCUWSFWKZBFYSGUUSWLZQUXAUCBBCFYSYTIWNZWOWPWQUWGYQ
      FXDJZUWRUWCUWTTUKZUXEYQUUPUXJYQUUPUUOUUQWRUUPUXJFWSJFWTWRSZBFUWQYTYSGUWQP
      ZUUSXAZQXBBUWHFUWQUUBYTGUXMUWHPZXCZWOUWBUWPUWEUUAUWBUUNUWPYQUUNWIUUMUWOAU
      BBUUBUWMRUULUWNDNUUBUWMUUKCXEVEXFXGXHUWLUWPUWKUWOUWKUBUWIBUWMUWIRUWNUWJDN
      UWMUWIUUKCXEVEVHXIXJYQUWEUUAUWKUUGUHUUNYQUWETZUUATZUWJUUFDNUXRUVOTZUWJUUF
      UXSUWJTZUWIYTFXKKZMZUUKYTUYAMZUUBUUECUXTBFCUYAUWIUUKYSYTGUYAPZUUSUXTYQUUO
      YQUWEUUAUVOUWJXLZUURSUXTUVJUWDUWRUWLUXTYQUVJUYEUVRSZUXTUWCUWDYQUWEUUAUVOU
      WJXMZXNZUXTUWRUWCUWTUXTUWCUWDUYGXOZUXTYSYTUXTUUAUXBUXQUUAUVOUWJXPZUXTYQUX
      CUWCUXDUYEUXTUVJUXFUXCUYFUXGUXHQUYIUXIWOWPWQUXTYQUXJUXKUYEUXLUXNQXBZUXPWO
      UXTUUKUVBBUXTYQUVOUVQUYEUXRUVOUWJXQZUWAXJZUXTUXFUVPUVIUVBBJUXTUVJUXFUYFUX
      GSUXTUVOUVPUYLUVSSZUXTUVJUVIUYFUVMSZBUUDFUUCUVAGUUTXRWOXSUYIIUXTYQUXJUYEU
      XLSUXSUWJWIUYJXTUXTUVJUWDUWRUYBUUBRUYFUYHUYKBUWHFUYAUWQUUBYTGUXMUXOUYDYAW
      OUXTUYCUVBYTUYAMZUUCUVAYTUYAMZUUDMZUUEUXTUUKUVBYTUYAUYMYDUXTUVJUVPUVIUWCU
      YPUYRRUYFUYNUYOUYIBFUUDUYAUUCUVAYTGUUTUYDYBYCUXTUYQYTUUCUUDUXTUVJUWCUYQYT
      RUYFUYIBFUYAUVAYTGUYDUVLYEXJYFYNYGYHYIYJWPYHYKYLYMYHYOYP $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
    Ring homomorphisms - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d c y A $.  $d c y B $.  $d c y F $.  $d c R $.  $d c y S $.  $d c X $.
    $d c .|| $.
    rhmdvdsr.x $e |- X = ( Base ` R ) $.
    rhmdvdsr.m $e |- .|| = ( ||r ` R ) $.
    rhmdvdsr.n $e |- ./ = ( ||r ` S ) $.
    $( A ring homomorphism preserves the divisibility relation.  (Contributed
       by Thierry Arnoux, 22-Oct-2017.) $)
    rhmdvdsr $p |- ( ( ( F e. ( R RingHom S ) /\ A e. X /\ B e. X )
      /\ A .|| B ) -> ( F ` A ) ./ ( F ` B ) ) $=
      ( vy vc co wcel wa cfv wceq wrex syl2anc crh w3a wbr cbs cv simpl1 simpl2
      cmulr eqid rhmf ffvelrnda wral simpll1 simpr adantr rhmmul syl3anc dvdsr2
      ralrimiva biimpac r19.29 fveq2d eqtr3d reximi syl eqeq1d rspcev rexlimivw
      simpl oveq1 dvdsr sylanbrc ) GEFUANOZAHOZBHOZUBZABCUCZPZAGQZFUDQZOZLUEZVS
      FUHQZNZBGQZRZLVTSZVSWEDUCVRVMVNWAVMVNVOVQUFVMVNVOVQUGZVMHVTAGHVTEFGIVTUIZ
      UJZUKTVRMUEZGQZVTOZWLVSWCNZWERZPZMHSZWGVRWMMHULWOMHSZWQVRWMMHVRWKHOZPZVMW
      SWMVMVNVOVQWSUMZVRWSUNZVMHVTWKGWJUKTUSVRWKAEUHQZNZGQZWNRZMHULZXDBRZMHSZWR
      VRXFMHWTVMWSVNXFXAXBVRVNWSWHUOWKAEFXCWCGHIXCUIZWCUIZUPUQUSVRVQVNXIVPVQUNW
      HVNVQXIMHCEXCABIJXJURUTTXGXIPXFXHPZMHSWRXFXHMHVAXLWOMHXLXEWNWEXFXHVIXLXDB
      GXFXHUNVBVCVDVETWMWOMHVATWPWGMHWFWOLWLVTWBWLRWDWNWEWBWLVSWCVJVFVGVHVELVTD
      FWCVSWEWIKXKVKVL $.
  $}

  ${
    $d x y F $.  $d x y R $.  $d x y S $.
    $( A ring homomorphism is also a ring homomorphism for the opposite rings.
       (Contributed by Thierry Arnoux, 27-Oct-2017.) $)
    rhmopp $p |- ( F e. ( R RingHom S )
       -> F e. ( ( oppR ` R ) RingHom ( oppR ` S ) ) ) $=
      ( vx vy wcel coppr cfv cbs cmulr cur eqid crg opprrngb sylib oppr1 eqcomi
      co cv wa crh rhmrcl1 rhmrcl2 rhm1 wceq simpl simprr opprbas simprl rhmmul
      syl6eleqr syl3anc opprmul fveq2i 3eqtr4g cgrp cplusg wral cghm rnggrp syl
      wf rhmf rhmghm ad2antrr simplr simpr ghmlin ralrimiva jca31 oppradd isghm
      jca sylibr isrhm2d ) CABUARFZDEAGHZIHZVQBGHZVQJHZVSJHZVQKHZCVSKHZVRLWBLWC
      LVTLZWALZVPAMFVQMFZABCUBAVQVQLZNOZVPBMFVSMFZABCUCBVSVSLZNOZABWBCWCAKHZWBA
      WLVQWGWLLPQBKHZWCBWMVSWJWMLPQUDVPDSZVRFZESZVRFZTZTZWPWNAJHZRZCHZWPCHZWNCH
      ZBJHZRZWNWPVTRZCHXDXCWARWSVPWPAIHZFZWNXHFZXBXFUEVPWRUFWSWPVRXHVPWOWQUGXHA
      VQWGXHLZUHZUKWSWNVRXHVPWOWQUIXLUKWPWNABWTXECXHXKWTLZXELZUJULXGXACXHAVTWTV
      QWNWPXKXMWGWDUMUNBIHZBWAXEVSXDXCXOLZXNWJWEUMUOVPVQUPFZVSUPFZTXHXOCVBZWNWP
      AUQHZRCHXDXCBUQHZRUEZEXHURZDXHURZTZTCVQVSUSRFVPXQXRYEVPWFXQWHVQUTVAVPWIXR
      WKVSUTVAVPXSYDXHXOABCXKXPVCVPYCDXHVPXJTZYBEXHYFXITCABUSRFZXJXIYBVPYGXJXIA
      BCVDVEVPXJXIVFYFXIVGXTYAABWNCWPXHXKXTLZYALZVHULVIVIVMVJEDXTYAVQVSCXHXOXLX
      OBVSWJXPUHXTAVQWGYHVKYABVSWJYIVKVLVNVO $.
  $}

  ${
    $( Ring homomorphisms preserve unit elements.  (Contributed by Thierry
       Arnoux, 23-Oct-2017.) $)
    elrhmunit $p |- ( ( F e. ( R RingHom S ) /\ A e. ( Unit ` R ) )
      -> ( F ` A ) e. ( Unit ` S ) ) $=
      ( crh co wcel cui cfv wa cur cdsr wbr coppr eqid isunit rhmdvdsr syl31anc
      wb adantr cbs simpl unitss simpr sseldi rhmrcl1 rngidcl 3syl sylib simpld
      crg rhm1 breq2d mpbid rhmopp simprd opprbas sylanbrc ) DBCEFGZABHIZGZJZAD
      IZCKIZCLIZMZVCVDCNIZLIZMZVCCHIZGVBVCBKIZDIZVEMZVFVBUSABUAIZGZVKVNGZAVKBLI
      ZMZVMUSVAUBZVBUTVNAVNBUTVNOZUTOZUCUSVAUDZUEZVBUSBUKGVPVSBCDUFVNBVKVTVKOZU
      GUHZVBVRAVKBNIZLIZMZVBVAVRWHJWBVQBWFUTVKWGAWAWDVQOZWFOZWGOZPUIZUJAVKVQVEB
      CDVNVTWIVEOZQRUSVMVFSVAUSVLVDVCVEBCVKDVDWDVDOZULZUMTUNVBVCVLVHMZVIVBDWFVG
      EFGZVOVPWHWPUSWQVABCDUOTWCWEVBVRWHWLUPAVKWGVHWFVGDVNVNBWFWJVTUQWKVHOZQRUS
      WPVISVAUSVLVDVCVHWOUMTUNVECVGVJVDVHVCVJOWNWMVGOWRPUR $.
  $}

$(
  @{
    rhmdvr.u @e |- U = ( Unit ` R ) @.
    rhmdvr.x @e |- X = ( Base ` R ) @.
    rhmdvr.m @e |- ./ = ( /r ` R ) @.
    rhmdvr.d @e |- .|| = ( ||r ` R ) @.
    rhmdvr.n @e |- D = ( /r ` S ) @.
    @( A ring homomorphism preserves ring division.  (Contributed  by Thierry
       Arnoux, 22-Oct-2017.) @)
    rhmdvr @p |- ( ( F e. ( R RingHom S ) /\ A e. X /\ B .|| A ) ->
      ( F ` ( A ./ B ) ) = ( ( F ` A ) D ( F ` B ) ) ) @=
      ? @.
  @}
$)

  ${
    rhmdvd.u $e |- U = ( Unit ` S ) $.
    rhmdvd.x $e |- X = ( Base ` R ) $.
    rhmdvd.d $e |- ./ = ( /r ` S ) $.
    rhmdvd.m $e |- .x. = ( .r ` R ) $.
    $( A ring homomorphism preserves ratios.  (Contributed by Thierry Arnoux,
       22-Oct-2017.) $)
    rhmdvd $p |- ( ( F e. ( R RingHom S ) /\ ( A e. X /\ B e. X /\ C e. X )
      /\ ( ( F ` B ) e. U /\ ( F ` C ) e. U ) ) -> ( ( F ` A ) ./ ( F ` B ) )
         = ( ( F ` ( A .x. C ) ) ./ ( F ` ( B .x. C ) ) ) ) $=
      ( co wcel w3a cfv wceq eqid crh cmulr simp21 simp23 rhmmul syl3anc simp22
      wa simp1 oveq12d crg cbs rhmrcl2 3ad2ant1 wf rhmf ffvelrnd simp3l dvrcan5
      simp3r syl13anc eqtr2d ) IEFUAOPZAJPZBJPZCJPZQZBIRZHPZCIRZHPZUHZQZACGOIRZ
      BCGOIRZDOAIRZVJFUBRZOZVHVJVQOZDOZVPVHDOZVMVNVRVOVSDVMVCVDVFVNVRSVCVGVLUIZ
      VCVDVEVFVLUCZVCVDVEVFVLUDZACEFGVQIJLNVQTZUEUFVMVCVEVFVOVSSWBVCVDVEVFVLUGW
      DBCEFGVQIJLNWEUEUFUJVMFUKPZVPFULRZPVIVKVTWASVCVGWFVLEFIUMUNVMJWGAIVCVGJWG
      IUOVLJWGEFILWGTZUPUNWCUQVCVGVIVKURVCVGVIVKUTWGDFVQHVPVHVJWHKMWEUSVAVB $.
  $}

  ${
    $d x y A $.  $d y F $.  $d x y R $.  $d y S $.
    $( Ring homomorphisms preserve the inverse of unit elements.  (Contributed
       by Thierry Arnoux, 23-Oct-2017.) $)
    rhmunitinv $p |- ( ( F e. ( R RingHom S ) /\ A e. ( Unit ` R ) )
      -> ( F ` ( ( invr ` R ) ` A ) ) = ( ( invr ` S ) ` ( F ` A ) ) ) $=
      ( co wcel cui cfv cinvr cmulr wceq cur crg eqid unitlinv unitinvcl sseldi
      sylan adantr elrhmunit crh rhmrcl1 fveq2d cbs simpl unitss rhmmul syl3anc
      wa simpr rhm1 3eqtr3d rhmrcl2 syl2anc eqtr4d cmgp cress wb unitgrp syldan
      cgrp syl unitgrpbas cplusg fvex mgpplusg ressplusg ax-mp grprcan syl13anc
      cvv mpbid ) DBCUAEFZABGHZFZUIZABIHZHZDHZADHZCJHZEZVTCIHZHZVTWAEZKZVSWDKZV
      PWBCLHZWEVPVRABJHZEZDHZBLHZDHZWBWHVPWJWLDVMBMFZVOWJWLKBCDUBZBWIVNWLVQAVNN
      ZVQNZWINZWLNZORUCVPVMVRBUDHZFAWTFWKWBKVMVOUEVPVNWTVRWTBVNWTNZWPUFZVMWNVOV
      RVNFZWOBVNVQAWPWQPRZQVPVNWTAXBVMVOUJQVRABCWIWADWTXAWRWANZUGUHVMWMWHKVOBCW
      LDWHWSWHNZUKSULVPCMFZVTCGHZFZWEWHKVMXGVOBCDUMZSZABCDTZCWAXHWHWCVTXHNZWCNZ
      XEXFOUNUOVPCUPHZXHUQEZVAFZVSXHFZWDXHFZXIWFWGURVMXQVOVMXGXQXJCXHXPXMXPNZUS
      VBSVMVOXCXRXDVRBCDTUTVPXGXIXSXKXLCXHWCVTXMXNPUNXLXHWAXPVSWDVTCXHXPXMXTVCX
      HVKFWAXPVDHKCGVEXHWAXOXPVKXTCWAXOXONXEVFVGVHVIVJVL $.
  $}

$(
  @{
    rhmuntghm.1 @e |- G = ( ( mulGrp ` R ) |`s ( Unit ` R ) ) @.
    rhmuntghm.2 @e |- H = ( ( mulGrp ` S ) |`s ( Unit ` S ) ) @.
    @( A ring homomorphism induces a group homomorphism on the group units
       @)
    rhmuntghm @p |- ( F e. ( R RingHom S ) -> ( F |` G ) e. ( G GrpHom H ) ) @=
      ? @.
  @}
$)

  ${
    $d x .0. $.  $d x .1. $.  $d x F $.  $d x R $.  $d x S $.  $d x U $.
    kerunit.1 $e |- U = ( Unit ` R ) $.
    kerunit.2 $e |- .0. = ( 0g ` S ) $.
    kerunit.3 $e |- .1. = ( 1r ` S ) $.
    $( If a unit element lies in the kernel of a ring homomorphism, then
       ` 0 = 1 ` , i.e. the target ring is the zero ring.  (Contributed by
       Thierry Arnoux, 24-Oct-2017.) $)
    kerunit $p |- ( ( F e. ( R RingHom S ) /\
      ( U i^i ( `' F " { .0. } ) ) =/= (/) ) -> .1. = .0. ) $=
      ( vx co wcel wa wceq cfv cmulr crg eqid syldan adantr crh ccnv csn cin c0
      cima wne wrex cinvr cur elin biimpi adantl simpld rhmrcl1 unitlinv fveq2d
      cv sylan cbs simpl rnginvcl syl2anc unitcl syl rhmmul syl3anc simprd rhmf
      wf wfn wb elpreima 3syl simplbda fvex elsnc sylib oveq2d rhmrcl2 ffvelrnd
      ffn rngrz 3eqtrd rhm1 3eqtr3rd reximdva0 id rexlimivw ) EABUAKLZCEUBFUCZU
      FZUDZUEUGMDFNZJWMUHWNWJWNJWMWJJURZWMLZMZWOAUIOZOZWOAPOZKZEOZAUJOZEOZFDWJW
      PWOCLZXBXDNZWQXEWOWLLZWPXEXGMZWJWPXHWOCWLUKULUMZUNZWJAQLZXEXFABEUOZXKXEMX
      AXCEAWTCXCWRWOGWRRZWTRZXCRZUPUQUSSWQXBWSEOZWOEOZBPOZKZXPFXRKZFWQWJWSAUTOZ
      LZWOYALZXBXSNWJWPVAWQXKXEYBWJXKWPXLTXJYAACWRWOGXMYARZVBVCZWQXEYCXJYAACWOY
      DGVDVEWSWOABWTXREYAYDXNXRRZVFVGWQXQFXPXRWQXQWKLZXQFNWJWPXGYGWQXEXGXIVHWJX
      GYCYGWJYABUTOZEVJZEYAVKXGYCYGMVLYAYHABEYDYHRZVIZYAYHEWBYAWOWKEVMVNVOSXQFW
      OEVPVQVRVSWQBQLZXPYHLXTFNWJYLWPABEVTTWQYAYHWSEWJYIWPYKTYEWAYHBXRXPFYJYFHW
      CVCWDWJXDDNWPABXCEDXOIWETWFWGWNWNJWMWNWHWIVE $.
  $}

$(
  @{
    ker2idl.i @e |- I = ( 2Ideal ` R ) @.
    ker2idl.0 @e |- .0. = ( 0g ` S ) @.
    @( The kernel of a ring homomorphism is a two-sided ideal.
       See also ~ keridl . @)
    ker2idl @p |- ( F e. ( R RingHom S ) -> ( `' F " { .0. } ) e. I ) @=
      ? @.
  @}
$)

  ${
    $d x y .0. $.  $d x y A $.  $d x B $.  $d x y F $.  $d x y N $.
    $d x y R $.  $d x y S $.
    kerf1hrm.a $e |- A = ( Base ` R ) $.
    kerf1hrm.b $e |- B = ( Base ` S ) $.
    kerf1hrm.n $e |- N = ( 0g ` R ) $.
    kerf1hrm.0 $e |- .0. = ( 0g ` S ) $.
    $( TODO use ~ ghmf1 to shorten one direction $)
    $( A ring homomorphism ` F ` is injective if and only if its kernel is the
       singleton ` { N } ` .  (Contributed by Thierry Arnoux, 27-Oct-2017.) $)
    kerf1hrm $p |- ( F e. ( R RingHom S ) -> ( F : A -1-1-> B <->
      ( `' F " { .0. } ) = { N } ) ) $=
      ( vx vy co wcel wceq wa cfv wb adantr crh wf1 ccnv csn cima cv simpl f1fn
      wfn adantl elpreima syl biimpa simpld simprd fvex elsnc sylib cghm rhmghm
      ghmid ad2antrr eqeq2d wi wral cgrp rhmrcl1 rnggrp grpidcl 3syl wf simprbi
      crg dff13 r19.21bi fveq2 eqeq2 imbi12d rspcva syl2anc sylbird syl21anc ex
      imp elsn syl6ibr ssrdv wss rhmf ffn mpbir2and snssd eqssd w3a csg simpr2l
      sylibr simpr2r simpr3 eqid ghmeqker simpr1 eleqtrd ovex grpsubeq0 syl3anc
      syl31anc mpbid 3anassrs ralrimivva sylanbrc impbida ) ECDUANOZABEUBZEUCGU
      DZUEZFUDZPZXMXNQZXPXQXSLXPXQXSLUFZXPOZXTFPZXTXQOXSYAYBXSYAQZXSXTAOZXTERZG
      PZYBXSYAUGYCYDYEXOOZXSYAYDYGQZXSEAUIZYAYHSXNYIXMABEUHUJAXTXOEUKULUMZUNYCY
      GYFYCYDYGYJUOYEGXTEUPUQURXSYDQZYFYBYKYFYEFERZPZYBYKYLGYEXMYLGPZXNYDXMECDU
      SNOZYNCDEUTZCDEFGJKVAULZVBVCYKFAOZYEMUFZERZPZXTYSPZVDZMAVEZYMYBVDZYKCVMOZ
      CVFOZYRXMUUFXNYDCDEVGZVBCVHZACFHJVIZVJXSUUDLAXNUUDLAVEZXMXNABEVKZUUKLMABE
      VNZVLUJVOUUCUUEMFAYSFPZUUAYMUUBYBUUNYTYLYEYSFEVPVCYSFXTVQVRVSVTWAWDWBWCLF
      WEWFWGXMXQXPWHXNXMFXPXMFXPOZYRYLXOOZXMUUFUUGYRUUHUUIUUJVJXMYNUUPYQYLGFEUP
      UQWQXMUULYIUUOYRUUPQSABCDEHIWIZABEWJAFXOEUKVJWKWLTWMXMXRQZUULUUKXNXMUULXR
      UUQTUURUUCLMAAUURYDYSAOZQZQUUAUUBXMXRUUTUUAUUBXMXRUUTUUAWNZQZXTYSCWORZNZF
      PZUUBUVBUVDXQOUVEUVBUVDXPXQUVBYOYDUUSUUAUVDXPOZXMYOUVAYPTYDUUSXRUUAXMWPZY
      DUUSXRUUAXMWRZXMXRUUTUUAWSYOYDUUSWNUUAUVFACDXTEXPUVCYSGHKXPWTUVCWTZXAUMXG
      XMXRUUTUUAXBXCUVDFXTYSUVCXDUQURUVBUUGYDUUSUVEUUBSUVBUUFUUGXMUUFUVAUUHTUUI
      ULUVGUVHACUVCXTYSFHJUVIXEXFXHXIWCXJUUMXKXL $.

$(
    @( If ` R ` is a field and ` S ` is a non-zero ring then a ring
       homomorphism between ` R ` and ` S ` is injective. @)
    hrmf1 @p |- ( ( F e. ( R RingHom S ) /\ R e. Field /\ S e. NzRing ) ->
      F : A -1-1-> B ) @=
      ? @.
$)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
    The commutative ring of integers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    zzs.1 $e |- Z = ( CCfld |`s ZZ ) $.
    $( The base of the ring of integers.  (Contributed by Thierry Arnoux,
       31-Oct-2017.) $)
    zzsbase $p |- ZZ = ( Base ` Z ) $=
      ( cz cc wss cbs cfv wceq zsscn ccnfld cnfldbas ressbas2 ax-mp ) CDECAFGHI
      CDAJBKLM $.

    $( The addition operation of the ring of integers.  (Contributed by Thierry
       Arnoux, 8-Nov-2017.) $)
    zzsplusg $p |- + = ( +g ` Z ) $=
      ( cz cvv wcel caddc cplusg cfv wceq zex ccnfld cnfldadd ressplusg ax-mp )
      CDEFAGHIJCFKADBLMN $.

    $d x y $.
    $( The multiplication (group power) opereation of the group of integers.
       (Contributed by Thierry Arnoux, 31-Oct-2017.) $)
    zzsmulg $p |- ( ( A e. ZZ /\ B e. ZZ )
      -> ( A ( .g ` Z ) B ) = ( A x. B ) ) $=
      ( vx vy cz wcel wa ccnfld cmg cfv co cmul csubg wceq c1 cv zcn eqid 1z cc
      zaddcl znegcl cnsubglem subgmulg mp3an1 simpr cnfldmulg syldan eqtr3d
      zcnd ) AGHZBGHZIZABJKLZMZABCKLZMZABNMZGJOLHUMUNUQUSPEFGQERZSVAFRUCVAUDUAU
      EGURUPJCABUPTDURTUFUGUMUNBUBHUQUTPUOBUMUNUHULABUIUJUK $.

    $( The multiplication operation of the ring of integers.  (Contributed by
       Thierry Arnoux, 1-Nov-2017.) $)
    zzsmulr $p |- x. = ( .r ` Z ) $=
      ( cz cvv wcel cmul cmulr cfv wceq zex ccnfld cnfldmul ressmulr ax-mp ) CD
      EFAGHIJCKAFDBLMN $.

    $( The neutral element of the ring of integers.  (Contributed by Thierry
       Arnoux, 1-Nov-2017.) $)
    zzs0 $p |- 0 = ( 0g ` Z ) $=
      ( ccnfld cmnd wcel cc0 cz wss c0g cfv wceq ccrg crg cncrng crngrng rngmnd
      cc mp2b 0z zsscn cnfldbas cnfld0 ress0g mp3an ) CDEZFGEGQHFAIJKCLECMEUENC
      OCPRSTGQCAFBUAUBUCUD $.

    $( The multiplicative neutral element of the ring of integers (Contributed
       by Thierry Arnoux, 1-Nov-2017.) $)
    zzs1 $p |- 1 = ( 1r ` Z ) $=
      ( cz ccnfld csubrg cfv wcel c1 cur wceq zsubrg cnfld1 subrg1 ax-mp ) CDEF
      GHAIFJKCDAHBLMN $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
    Scalar restriction operation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c |`v $.

  $( Extend class notation with the scalar restriction operation. $)
  cresv $a class |`v $.
  
  ${
    $d w x $.
    $( Define an operator to restrict the scalar field component of an extended
       structure.  (Contributed by Thierry Arnoux, 5-Sep-2018.) $)
    df-resv $a |- |`v = ( w e. _V , x e. _V |-> 
      if ( ( Base ` ( Scalar ` w ) ) C_ x , w , ( w sSet <. ( Scalar ` ndx ) , 
      ( ( Scalar ` w ) |`s x ) >. ) ) ) $.
  $}

  ${
    $d x y $.  $d w A $.  $d w W $.
    $( The scalar restriction is a proper operator, so it can be used with
       ~ ovprc1 .  (Contributed by Thierry Arnoux, 6-Sep-2018.) $)
    reldmresv $p |- Rel dom |`v $=
      ( vy vx cvv cv csca cfv cbs wss cnx cress co cop csts cif cresv reldmmpt2
      df-resv ) ABCCADZEFZGFBDZHRRIEFSTJKLMKNOBAQP $.
  $}

  ${
    $d w x A $.  $d w x B $.  $d w x F $.  $d w x W $.
    resvsca.r $e |- R = ( W |`v A ) $.
    resvsca.f $e |- F = ( Scalar ` W ) $.
    resvsca.b $e |- B = ( Base ` F ) $.
    $( Value of structure restriction.  (Contributed by Thierry Arnoux,
       6-Sep-2018.) $)
    resvval $p |- ( ( W e. X /\ A e. Y ) -> R = if ( B C_ A , W ,
            ( W sSet <. ( Scalar ` ndx ) , ( F |`s A ) >. ) ) ) $=
      ( vw vx wcel co csca cfv cress csts cvv wceq wa wss cnx cop cif elex ovex
      cresv ifcl mpan2 adantr cv cbs simpl fveq2d syl6eqr simpr sseq12d oveq12d
      opeq2d ifbieq12d df-resv ovmpt2ga mpd3an3 syl2an syl5eq ) EFMZAGMZUACEAUH
      NZBAUBZEEUCOPZDAQNZUDZRNZUEZHVGESMZASMZVIVOTZVHEFUFAGUFVPVQVOSMZVRVPVSVQV
      PVNSMVSEVMRUGVJEVNSUIUJUKKLEASSKULZOPZUMPZLULZUBZVTVTVKWAWCQNZUDZRNZUEVOU
      HSVTETZWCATZUAZWDVJVTWGEVNWJWBBWCAWJWBDUMPBWJWADUMWJWAEOPDWJVTEOWHWIUNZUO
      IUPZUOJUPWHWIUQZURWKWJVTEWFVMRWKWJWEVLVKWJWADWCAQWLWMUSUTUSVALKVBVCVDVEVF
      $.

    $( General behavior of trivial restriction.  (Contributed by Thierry
       Arnoux, 6-Sep-2018.) $)
    resvid2 $p |- ( ( B C_ A /\ W e. X /\ A e. Y ) -> R = W ) $=
      ( wss wcel wceq wa cnx csca cfv cress co cop cif resvval iftrue sylan9eqr
      csts 3impb ) BAKZEFLZAGLZCEMUHUINUGCUGEEOPQDARSTUESZUAEABCDEFGHIJUBUGEUJU
      CUDUF $.

    $( Value of nontrivial structure restriction.  (Contributed by Thierry
       Arnoux, 6-Sep-2018.) $)
    resvval2 $p |- ( ( -. B C_ A /\ W e. X /\ A e. Y ) -> R = ( W sSet
        <. ( Scalar ` ndx ) , ( F |`s A ) >. ) ) $=
      ( wss wn wcel cnx csca cfv cress co cop csts wa resvval iffalse sylan9eqr
      wceq cif 3impb ) BAKZLZEFMZAGMZCENOPDAQRSTRZUEUJUKUAUICUHEULUFULABCDEFGHI
      JUBUHEULUCUDUG $.

    $( Base set of a structure restriction.  (Contributed by Thierry Arnoux,
       6-Sep-2018.) $)
    resvsca $p |- ( A e. V -> ( F |`s A ) = ( Scalar ` R ) ) $=
      ( cvv wcel cress co csca cfv wceq w3a fveq2d 3eqtr4a c0 wss wa wi eqeltri
      fvex eqid ressid2 mp3an2 3adant2 resvid2 3expib cnx csts simp2 ovex scaid
      cop setsid sylancl resvval2 eqtr4d pm2.61i 0fv 0ex strfvn ress0 3eqtr4ri
      wn fvprc syl5eq oveq1d cresv reldmresv ovprc1 adantr pm2.61ian ) FJKZAEKZ
      DALMZCNOZPZBAUAZVQVRUBWAUCWBVQVRWAWBVQVRQZDFNOZVSVTHWBVRVSDPZVQWBDJKVRWED
      WDJHFNUEUDABVSDJEVSUFIUGUHUIWCCFNABCDFJEGHIUJRSUKWBVHZVQVRWAWFVQVRQZVSFUL
      NOZVSUQUMMZNOZVTWGVQVSJKVSWJPWFVQVRUNDALUOJVSNJFUPURUSWGCWINABCDFJEGHIUTR
      VAUKVBVQVHZWAVRWKTALMZTNOZVSVTWHTOTWMWLWHVCTNWHVDUPVEAVFVGWKDTALWKDWDTHFN
      VIVJVKWKCTNWKCFAVLMTGFAVLVMVNVJRSVOVP $.
  $}

  ${
    resvlem.r $e |- R = ( W |`v A ) $.
    resvlem.e $e |- C = ( E ` W ) $.
    resvlem.f $e |- E = Slot N $.
    resvlem.n $e |- N e. NN $.
    resvlem.b $e |- N =/= 5 $.
    $( Other elements of a structure restriction.  (Contributed by Thierry
       Arnoux, 6-Sep-2018.) $)
    resvlem $p |- ( A e. V -> C = ( E ` R ) ) $=
      ( wcel cfv cvv csca w3a fveq2d co c0 wceq cbs wss wa wi resvid2 3expib wn
      eqid cnx cress cop csts resvval2 ndxid c5 ndxarg eqnetri neeqtrri setsnid
      scandx syl6eqr pm2.61i cresv reldmresv ovprc1 syl5eq str0 fvprc pm2.61ian
      eqtr4d adantr syl6reqr ) AFMZCDNZGDNZBGOMZVNVOVPUAZGPNZUBNZAUCZVQVNUDVRUE
      WAVQVNVRWAVQVNQCGDAVTCVSGOFHVSUIZVTUIZUFRUGWAUHZVQVNVRWDVQVNQZVOGUJPNZVSA
      UKSZULUMSZDNVPWECWHDAVTCVSGOFHWBWCUNRWGWFDGDEJKUOUJDNZUPWFWIEUPDEJKUQLURV
      AUSUTVBUGVCVQUHZVRVNWJVOTVPWJVOTDNTWJCTDWJCGAVDSTHGAVDVEVFVGRDEJVHVBGDVIV
      KVLVJIVM $.
  $}

  ${
    resvbas.1 $e |- H = ( G |`v A ) $.
    ${
      resvbas.2 $e |- B = ( Base ` G ) $.
      $( ` Base ` is unaffected by scalar restriction.  (Contributed by Thierry
         Arnoux, 6-Sep-2018.) $)
      resvbas $p |- ( A e. V -> B = ( Base ` H ) ) $=
        ( cbs c1 df-base 1nn c5 1re 1lt5 ltneii resvlem ) ABDHIECFGJKILMNOP $.
    $}

    ${
      resvplusg.2 $e |- .+ = ( +g ` G ) $.
      $( ` +g ` is unaffected by scalar restriction.  (Contributed by Thierry
         Arnoux, 6-Sep-2018.) $)
      resvplusg $p |- ( A e. V -> .+ = ( +g ` H ) ) $=
        ( cplusg c2 df-plusg 2nn c5 2re 2lt5 ltneii resvlem ) ABDHIECFGJKILMNOP
        $.
    $}

    ${
      resvvsca.2 $e |- .x. = ( .s ` G ) $.
      $( ` .s ` is unaffected by scalar restriction.  (Contributed by Thierry
         Arnoux, 6-Sep-2018.) $)
      resvvsca $p |- ( A e. V -> .x. = ( .s ` H ) ) $=
        ( cvsca c6 df-vsca 6nn c5 5re 5lt6 ltneii necomi resvlem ) ABDHIECFGJKL
        ILIMNOPQ $.
    $}

    ${
      resvmulr.2 $e |- .x. = ( .r ` G ) $.
      $( ` .s ` is unaffected by scalar restriction.  (Contributed by Thierry
         Arnoux, 6-Sep-2018.) $)
      resvmulr $p |- ( A e. V -> .x. = ( .r ` H ) ) $=
        ( cmulr c3 df-mulr 3nn c5 3re 3lt5 ltneii resvlem ) ABDHIECFGJKILMNOP
        $.
    $}

    ${
      $d x y A $.  $d x y G $.  $d x y H $.  $d x y V $.
      resv0g.2 $e |- .0. = ( 0g ` G ) $.
      $( ` 0g ` is unaffected by scalar restriction.  (Contributed by Thierry
         Arnoux, 6-Sep-2018.) $)
      resv0g $p |- ( A e. V -> .0. = ( 0g ` H ) ) $=
        ( vx vy wcel c0g cfv cbs wceq eqid a1i resvbas cv wa cplusg grpidpropd
        resvplusg adantr oveqd syl5eq ) ADJZEBKLCKLGUFHIBMLZBCUGUGNUFUGOZPAUGBC
        DFUHQUFHRZUGJIRZUGJSZSBTLZCTLZUIUJUFULUMNUKAULBCDFULOUBUCUDUAUE $.
    $}

    ${
      $d e x A $.  $d e x G $.  $d e x H $.  $d e x V $.
      resv1r.2 $e |- .1. = ( 1r ` G ) $.
      $( ` 1r ` is unaffected by scalar restriction.  (Contributed by Thierry
         Arnoux, 6-Sep-2018.) $)
      resv1r $p |- ( A e. V -> .1. = ( 1r ` H ) ) $=
        ( ve vx wcel cv cbs cfv cmulr co wceq wa wral cio eqid resvbas resvmulr
        cur eleq2d oveqd eqeq1d anbi12d raleqbidv iotabidv dfur2 3eqtr4g ) AEJZ
        HKZCLMZJZUMIKZCNMZOZUPPZUPUMUQOZUPPZQZIUNRZQZHSUMDLMZJZUMUPDNMZOZUPPZUP
        UMVGOZUPPZQZIVERZQZHSBDUCMZULVDVNHULUOVFVCVMULUNVEUMAUNCDEFUNTZUAZUDULV
        BVLIUNVEVQULUSVIVAVKULURVHUPULUQVGUMUPAUQCDEFUQTZUBZUEUFULUTVJUPULUQVGU
        PUMVSUEUFUGUHUGUIIUNCUQBHVPVRGUJIVEDVGVOHVETVGTVOTUJUK $.
    $}

    ${
      $d x y A $.  $d x y G $.  $d x y H $.  $d x y V $.
      $( Scalar restriction preserves commutative monoids.  (Contributed by
         Thierry Arnoux, 6-Sep-2018.) $)
      resvcmn $p |- ( A e. V -> ( G e. CMnd <-> H e. CMnd ) ) $=
        ( vx vy wcel cbs cfv eqidd eqid resvbas cv cplusg wceq resvplusg adantr
        wa oveqd cmnpropd ) ADHZFGBIJZBCUBUCKAUCBCDEUCLMUBFNZUCHGNZUCHSZSBOJZCO
        JZUDUEUBUGUHPUFAUGBCDEUGLQRTUA $.
    $}
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
    The commutative ring of gaussian integers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The gaussian integers form a commutative ring.  (Contributed by Thierry
     Arnoux, 18-Mar-2018.) $)
  gzcrng $p |- ( CCfld |`s Z[i] ) e. CRing $=
    ( ccnfld ccrg wcel cgz csubrg cfv cress cncrng gzsubrg eqid subrgcrng mp2an
    co ) ABCDAEFCADGMZBCHIDANNJKL $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
    The ordered field of reals
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    re.1 $e |- R = ( CCfld |`s RR ) $.
    $( The base of the field of reals.  (Contributed by Thierry Arnoux,
       1-Nov-2017.) $)
    rebase $p |- RR = ( Base ` R ) $=
      ( cr cc wss cbs cfv wceq ax-resscn ccnfld cnfldbas ressbas2 ax-mp ) CDECA
      FGHICDAJBKLM $.

    $d x y $.
    $( The multiplication (group power) operation of the group of reals.
       (Contributed by Thierry Arnoux, 1-Nov-2017.) $)
    remulg $p |- ( ( N e. ZZ /\ A e. RR )
      -> ( N ( .g ` R ) A ) = ( N x. A ) ) $=
      ( vx vy cz wcel cr wa ccnfld cmg cfv co cmul csubg wceq c1 cv eqid mp3an1
      recn readdcl renegcl 1re cnsubglem subgmulg simpr cnfldmulg syldan eqtr3d
      cc recnd ) CGHZAIHZJZCAKLMZNZCABLMZNZCAONZIKPMHUNUOURUTQEFIRESZUBVBFSUCVB
      UDUEUFIUSUQKBCAUQTDUSTUGUAUNUOAULHURVAQUPAUNUOUHUMCAUIUJUK $.

    $( The addition operation of the field of reals.  (Contributed by Thierry
       Arnoux, 21-Jan-2018.) $)
    replusg $p |- + = ( +g ` R ) $=
      ( cr cvv wcel caddc cplusg cfv wceq reex ccnfld cnfldadd ressplusg ax-mp
      ) CDEFAGHIJCFKADBLMN $.

    $( The multiplication operation of the field of reals.  (Contributed by
       Thierry Arnoux, 1-Nov-2017.) $)
    remulr $p |- x. = ( .r ` R ) $=
      ( cr cvv wcel cmul cmulr cfv wceq reex ccnfld cnfldmul ressmulr ax-mp ) C
      DEFAGHIJCKAFDBLMN $.

    $( The neutral element of the field of reals.  (Contributed by Thierry
       Arnoux, 1-Nov-2017.) $)
    re0g $p |- 0 = ( 0g ` R ) $=
      ( ccnfld cmnd wcel cc0 cr wss c0g cfv wceq ccrg crg cncrng crngrng rngmnd
      cc mp2b 0re ax-resscn cnfldbas cnfld0 ress0g mp3an ) CDEZFGEGQHFAIJKCLECM
      EUENCOCPRSTGQCAFBUAUBUCUD $.

    $( The multiplicative neutral element of the field of reals.  (Contributed
       by Thierry Arnoux, 1-Nov-2017.) $)
    re1r $p |- 1 = ( 1r ` R ) $=
      ( cr ccnfld csubrg cfv wcel c1 cur wceq cress co cdr simpli cnfld1 subrg1
      resubdrg ax-mp ) CDEFGZHAIFJSDCKLMGQNCDAHBOPR $.

    $( The ordering relation of the field of reals.  (Contributed by Thierry
       Arnoux, 21-Jan-2018.) $)
    rele2 $p |- <_ = ( le ` R ) $=
      ( cr cvv wcel cle cple cfv wceq reex ccnfld cnfldle ressle ax-mp ) CDEFAG
      HIJCKFDABLMN $.

    $( The ordering relation of the field of reals.  (Contributed by Thierry
       Arnoux, 21-Jan-2018.) $)
    relt $p |- < = ( lt ` R ) $=
      ( clt cle cid cdif cplt cfv dflt2 cvv wcel wceq ccnfld cress ovex eqeltri
      cr co rele2 eqid pltfval ax-mp eqtr4i ) CDEFZAGHZIAJKUEUDLAMQNRJBMQNOPJUE
      ADABSUETUAUBUC $.

    $( The division operation of the field of reals.  (Contributed by Thierry
       Arnoux, 1-Nov-2017.) $)
    redvr $p |- ( ( A e. RR /\ B e. RR /\ B =/= 0 )
      -> ( A ( /r ` R ) B ) = ( A / B ) ) $=
      ( wcel cc0 wne w3a cdiv cdvr cfv ccnfld csubrg cui wceq cdr resubdrg eqid
      cr co cress simpli simp1 wa 3simpc wb simpri eqeltri rebase re0g drngunit
      a1i ax-mp sylibr cnflddiv subrgdv syl3anc eqcomd ) ASEZBSEZBFGZHZABITZABC
      JKZTZVBSLMKEZUSBCNKZEZVCVEOVFVBVFLSUATZPEZQUBULUSUTVAUCVBUTVAUDZVHUSUTVAU
      ECPEVHVKUFCVIPDVFVJQUGUHSCVGBFCDUIVGRZCDUJUKUMUNSILCVGVDABDUOVLVDRUPUQUR
      $.

    $( The real numbers are a totally ordered set.  (Contributed by Thierry
       Arnoux, 21-Jan-2018.) $)
    retos $p |- R e. Toset $=
      ( vx ctos wcel cr clt wor cid cres cle wss ltso wbr idref leid cvv ccnfld
      cv cress mprgbir wa wb co ovex eqeltri rebase rele2 tosso ax-mp mpbir2an
      relt ) ADEZFGHZIFJKLZMUOCSZUPKNCFCFKOUPPUAAQEUMUNUOUBUCARFTUDQBRFTUEUFFGA
      KQABUGABUHABULUIUJUK $.

    $( The real numbers form a field.  (Contributed by Thierry Arnoux,
       1-Nov-2017.) $)
    refld $p |- R e. Field $=
      ( cfield wcel cdr ccrg ccnfld cr cress csubrg cfv resubdrg simpri eqeltri
      co cncrng simpli subrgcrng mp2an isfld mpbir2an ) ACDAEDAFDZAGHIOZEBHGJKD
      ZUCEDZLMNGFDUDUBPUDUELQHGABRSATUA $.

    $d a b c R $.
    $( The real numbers form an ordered field.  (Contributed by Thierry Arnoux,
       21-Jan-2018.) $)
    reofld $p |- R e. oField $=
      ( va vb vc wcel wa cc0 cv cle wbr cmul co wi wral w3a ax-mp caddc mpbir
      cr cofld cfield corng refld crg cogrp cdr ccrg isfld simplbi drngrng mp2b
      cgrp comnd rnggrp cmnd grpmnd retos simpl simpr1 simpr2 leadd1dd 3anassrs
      ctos simpr3 3impa rgen3 3pm3.2i rebase replusg rele2 isomnd pm3.2i isogrp
      ex mulge0 an4s rgen2 re0g remulr isorng isofld ) AUAFAUBFZAUCFZGWCWDABUDZ
      WDAUEFZAUFFZHCIZJKZHDIZJKZGZHWHWJLMJKZNZDTOCTOZPWFWGWOWCAUGFZWFWEWCWPAUHF
      AUIUJAUKULZWGAUMFZAUNFZGWRWSWFWRWQAUOQZWSAUPFZAVDFZWHWJJKZWHEIZRMWJXDRMJK
      ZNZETODTOCTOZPXAXBXGWRXAWTAUQQABURXFCDETTTWHTFZWJTFZXDTFZXFXHXIGZXJGXCXEX
      HXIXJXCXEXHXIXJXCPZGWHWJXDXHXLUSXHXIXJXCUTXHXIXJXCVAXHXIXJXCVEVBVCVOVFVGV
      HTRJACDEABVIZABVJABVKZVLSVMAVNSWNCDTTXKWLWMXHWIXIWKWMWHWJVPVQVOVRVHTALJHC
      DXMABVSABVTXNWASVMAWBS $.
  $}

  $( The nonnegative integers form an ordered monoid.  (Contributed by
     Thierry Arnoux, 23-Mar-2018.) $)
  nn0omnd $p |- ( CCfld |`s NN0 ) e. oMnd $=
    ( ccnfld cr cress co cn0 comnd cvv wcel wss wceq reex nn0ssre ressabs mp2an
    cmnd cofld eqid reofld simprbi ax-mp corng cfield isofld orngogrp cgrp 3syl
    cogrp isogrp csubmnd cfv nn0subm submmnd eqeltri submomnd eqeltrri ) ABCDZE
    CDZAECDZFBGHEBIUQURJKLBEAGMNZUPFHZUQOHUQFHUPPHZUTUPUPQRVAUPUAHZUPUGHZUTVAUP
    UBHVBUPUCSUPUDVCUPUEHUTUPUHSUFTUQUROUSEAUIUJHUROHUKEURAURQULTUMEUPUNNUO $.

  ${
    $d n x $.
    $( The field of the real numbers is Archimedean. See also ~ arch .
       (Contributed by Thierry Arnoux, 9-Apr-2018.) $)
    rearchi $p |- ( CCfld |`s RR ) e. Archi $=
      ( vx vn ccnfld cr cress co carchi wcel cv czrh cfv clt cn wrex cz wb wceq
      wbr c1 eqid wral arch nnz cmg cmul crg cfield refld isfld simplbi drngrng
      cdr ccrg mp2b re1r zrhmulg 1re remulg mpan2 zcn mulid1d 3eqtrd breq2d syl
      mpan rexbiia sylibr rgen cofld reofld rebase relt isarchiofld ax-mp mpbir
      ) CDEFZGHZAIZBIZVPJKZKZLRZBMNZADUAZWCADVRDHVRVSLRZBMNWCVRBUBWBWEBMVSMHVSO
      HZWBWEPVSUCWFWAVSVRLWFWAVSSVPUDKZFZVSSUEFZVSVPUFHZWFWAWHQVPUGHZVPULHZWJVP
      VPTZUHWKWLVPUMHVPUIUJVPUKUNVPWGSVTVSCOEFZWNTVTTZWGTVPWMUOUPVEWFSDHWHWIQUQ
      SVPVSWMURUSWFVSVSUTVAVBVCVDVFVGVHVPVIHVQWDPVPWMVJADLBVTVPVPWMVKWOVPWMVLVM
      VNVO $.
  $}

  ${
    $d q r w x W $.
    xrge0slmod.1 $e |- G = ( RR*s |`s ( 0 [,] +oo ) ) $.
    xrge0slmod.2 $e |- W = ( G |`v ( 0 [,) +oo ) ) $.
    $( The extended nonnegative real numbers form a semiring left module.
       One could also have used ` subringAlg ` to get the same structure.
       (Contributed by Thierry Arnoux, 6-Sep-2018.) $)
    xrge0slmod $p |- W e. SLMod $=
      ( wcel ccnfld cc0 cpnf co cress cxmu cxad wceq c1 cvv ax-mp sseldi cr cxr
      cfv vr vw vx vq cslmd ccmn cico csrg cv cicc caddc w3a cmul wral xrge0cmn
      wa cxrs eqeltri wb ovex resvcmn rge0srg icossicc simplr ge0xmulcl syl2anc
      mpbi simprr simprl xrge0adddi syl3anc cmnf cioo clt wbr cle wss mnfxr 0re
      pnfxr mnflt pnfge icossioo mp4an ioomax sseqtri simpll rexadd xrge0adddir
      oveq1d eqtr3d 3jca rexmul rexrd iccssxr xmulass xmulid2 xmul02 ralrimivva
      syl jca rgen2a cbs xrge0base fveq2i eqtr4i resvbas cplusg resvplusg cvsca
      xrge0plusg ax-xrsvsca ressvsca resvvsca c0g xrge00 cin csca reex ressress
      resv0g mp2an ax-xrssca resssca rebase resvsca incom df-ss eqtr3i 3eqtr3ri
      eqid oveq2i cc ax-resscn sstri cnfldbas cndrng 1re ltpnf mp3an cmulr 0le1
      ressbas2 cnfldadd ressplusg cnfldmul ressmulr crg cur cdr drngrng 3pm3.2i
      elico2 mpbir cnfld1 ress1r cmnd rngmnd mp2b lbico1 cnfld0 ress0g mpbir3an
      0xr isslmd ) BUEEBUFEZFGHUGIZJIZUHEUAUIZUBUIZKIZGHUJIZEZUVIUVJUCUIZLIKIUV
      KUVIUVNKILIMZUDUIZUVIUKIZUVJKIZUVPUVJKIUVKLIZMZULZUVPUVIUMIZUVJKIZUVPUVKK
      IZMZNUVJKIUVJMZGUVJKIGMZULZUPZUBUVLUNUCUVLUNZUAUVGUNUDUVGUNAUFEZUVFAUQUVL
      JIZUFCUOURUVGOEZUWKUVFUSGHUGUTZUVGABODVAPVGVBUWJUDUAUVGUVPUVGEZUVIUVGEZUP
      ZUWIUCUBUVLUVLUWQUVNUVLEZUVJUVLEZUPZUPZUWAUWHUXAUVMUVOUVTUXAUVIUVLEZUWSUV
      MUXAUVGUVLUVIGHVCZUWOUWPUWTVDZQZUWQUWRUWSVHZUVIUVJVEVFUXAUWSUWRUXBUVOUXFU
      WQUWRUWSVIUXEUVJUVNUVIVJVKUXAUVPUVILIZUVJKIZUVRUVSUXAUXGUVQUVJKUXAUVPREZU
      VIREZUXGUVQMUXAUVGRUVPUVGVLHVMIZRVLSEHSEZVLGVNVOZHHVPVOZUVGUXKVQVRVTGREZU
      XMVSGWAPUXLUXNVTHWBPVLHGHWCWDWEWFZUWOUWPUWTWGZQZUXAUVGRUVIUXPUXDQZUVPUVIW
      HVFWJUXAUVPUVLEUXBUWSUXHUVSMUXAUVGUVLUVPUXCUXQQUXEUXFUVPUVIUVJWIVKWKWLUXA
      UWEUWFUWGUXAUVPUVIKIZUVJKIZUWCUWDUXAUXTUWBUVJKUXAUXIUXJUXTUWBMUXRUXSUVPUV
      IWMVFWJUXAUVPSEUVISEUVJSEZUYAUWDMUXAUVPUXRWNUXAUVIUXSWNUXAUVLSUVJGHWOUXFQ
      ZUVPUVIUVJWPVKWKUXAUYBUWFUYCUVJWQWTUXAUYBUWGUYCUVJWRWTWLXAWSXBUCUBLUKKUMN
      UVHUVGGUVLBGUAUDUWMUVLBXCTMUWNUVGUVLABODUVLUWLXCTAXCTXDAUWLXCCXEXFXGPUWML
      BXHTMUWNUVGLABODLUWLXHTAXHTXKAUWLXHCXEXFXIPUWMKBXJTMUWNUVGKABODUVLOEZKAXJ
      TMGHUJUTZUVLKUQAOCXLXMPXNPUWMGBXOTMUWNUVGABOGDGUWLXOTAXOTXPAUWLXOCXEXFYAP
      FRJIZUVGJIZFRUVGXQZJIZBXRTZUVHROEUWMUYGUYIMXSUWNRUVGFOOXTYBUWMUYGUYJMUWNU
      VGRBUYFOADUYDUYFAXRTMUYEUVLUYFUQAOCYCYDPUYFUYFYKYEYFPUYHUVGFJUVGRXQZUYHUV
      GUVGRYGUVGRVQUYKUVGMUXPUVGRYHVGYIYLYJUVGYMVQZUVGUVHXCTMUVGRYMUXPYNYOZUVGY
      MUVHFUVHYKZYPUUCPUWMUKUVHXHTMUWNUVGUKFUVHOUYNUUDUUEPUWMUMUVHUUATMUWNUVGFU
      VHUMOUYNUUFUUGPFUUHEZNUVGEZUYLNUVHUUITMFUUJEZUYOYQFUUKZPUYPNREZGNVPVOZNHV
      NVOZULZUYSUYTVUAYRUUBUYSVUAYRNYSPUULUXOUXLUYPVUBUSVSVTGHNUUMYBUUNUYMUVGYM
      FUVHNUYNYPUUOUUPYTFUUQEZGUVGEZUYLGUVHXOTMUYQUYOVUCYQUYRFUURUUSGSEUXLGHVNV
      OZVUDUVDVTUXOVUEVSGYSPGHUUTYTUYMUVGYMFUVHGUYNYPUVAUVBYTUVEUVC $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Topology
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Regular spaces
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
$(
    regclnei.1 @e |- X = U. J @.
    regclnei.2 @e |- B = ( ( Clsd ` J ) i^i ( ( nei ` J ) ` { A } ) ) @.
    @( For a regular space ` J ` , the set of closed neighborhoods of any point
       ` X ` is a filter base which generates the filter of neighborhoods of
       ` X ` . Condition O_III of [BourbakiTop1] p.  I.56. @)
    regclnei @p |- ( ( J e. Reg /\ A e. X ) ->
      ( B e. ( fBas ` X ) /\ ( X filGen B ) = ( ( nei ` J ) ` { A } ) ) ) @=
      ? @.

    @( Given any point ` A ` and neighborhood ` N ` of ` A ` , there is a
       closed neighborhood ` E ` of ` A `` that is a subset of  ` N ` .
       Same as ~ regsep ??? @)
    regclnei $p |- ( ( J e. Reg /\ A e. X /\ N e. ( ( nei ` J ) ` { A } ) )
      -> E. E e. ( ( Clsd ` J ) i^i ( ( nei ` J ) ` { A } ) ) E C_ N ) @=
      ? @.
$)
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
        Pseudometrics
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Declare new constant symbols and define their syntactical properties. $)
  $c ~Met $.
  $c pstoMet $.

  $( Extend class notation with the class of metric identifications. $)
  cmetid $a class ~Met $.

  $( Extend class notation with the metric induced by a pseudometric. $)
  cpstm $a class pstoMet $.

  ${
    $d d x y $.
    $( Define the metric identification relation for a pseudometric.
       (Contributed by Thierry Arnoux, 7-Feb-2018.) $)
    df-metid $a |- ~Met = ( d e. U. ran PsMet |-> { <. x , y >. |
      ( ( x e. dom dom d /\ y e. dom dom d ) /\ ( x d y ) = 0 ) } ) $.
  $}

  ${
    $d a b d x y z $.
    $( Define the metric induced by a pseudometric.  (Contributed by Thierry
       Arnoux, 7-Feb-2018.) $)
    df-pstm $a |- pstoMet = ( d e. U. ran PsMet |->
      ( a e. ( dom dom d /. ( ~Met ` d ) ) , b e. ( dom dom d /. ( ~Met ` d ) )
      |-> U. { z | E. x e. a E. y e. b z = ( x d y ) } ) ) $.
  $}

  ${
    $d d w x y z $.  $d d x y D $.  $d d x y X $.
    $( Value of the metric identification relation.  (Contributed by Thierry
       Arnoux, 7-Feb-2018.) $)
    metidval $p |- ( D e. ( PsMet ` X ) -> ( ~Met ` D ) =
      { <. x , y >. | ( ( x e. X /\ y e. X ) /\ ( x D y ) = 0 ) } ) $=
      ( vd vz vw cpsmet cfv wcel cv cdm wa co cc0 wceq copab cvv eleq2d wral wb
      crn cuni cmetid cmpt df-metid simpr dmeqd psmetdmdm adantr eqtr4d anbi12d
      a1i oveqd eqeq1d opabbidv wrex elfvdm fveq2 mpancom wfun cxad cle wbr cxr
      rspcev cxp cmap df-psmet funmpt2 elunirn ax-mp sylibr wss opabssxp elfvex
      crab xpexg syl2anc ssexg sylancr fvmptd ) CDHIZJZECAKZEKZLZLZJZBKZWHJZMZW
      EWJWFNZOPZMZABQZWEDJZWJDJZMZWEWJCNZOPZMZABQZHUBUCZUDRUDEXDWPUEPWDABEUFUMW
      DWFCPZMZWOXBABXFWLWSWNXAXFWIWQWKWRXFWHDWEXFWHCLZLZDXFWGXGXFWFCWDXEUGZUHUH
      WDDXHPXECDUIUJUKZSXFWHDWJXJSULXFWMWTOXFWFCWEWJXIUNUOULUPWDCWEHIZJZAHLZUQZ
      CXDJZDXMJWDXNCDHURXLWDADXMWEDPXKWCCWEDHUSSVFUTHVAXOXNUAARWJWJWFNOPWJFKZWF
      NGKZWJWFNXQXPWFNVBNVCVDGWETFWETMBWETEVEWEWEVGVHNVQHABFGEVIVJACHVKVLVMWDXC
      DDVGZVNXRRJZXCRJXAABDDVOWDDRJZXTXSCDHVPZYADDRRVRVSXCXRRVTWAWB $.

    $( As a relation, the metric identification is a subset of a cross product.
       (Contributed by Thierry Arnoux, 7-Feb-2018.) $)
    metidss $p |- ( D e. ( PsMet ` X ) -> ( ~Met ` D ) C_ ( X X. X ) ) $=
      ( vx vy cpsmet cfv wcel cmetid cv wa cc0 wceq copab cxp metidval opabssxp
      co syl6eqss ) ABEFGAHFCIZBGDIZBGJSTAQKLZJCDMBBNCDABOUACDBBPR $.
  $}

  ${
    $d a b A $.  $d a b B $.  $d a b D $.  $d a b X $.
    $( ` A ` and ` B ` identify by the metric ` D ` if their distance is zero.
       (Contributed by Thierry Arnoux, 7-Feb-2018.) $)
    metidv $p |- ( ( D e. ( PsMet ` X ) /\ ( A e. X /\ B e. X ) )
      -> ( A ( ~Met ` D ) B <-> ( A D B ) = 0 ) ) $=
      ( va vb cpsmet cfv wcel wa cmetid wbr co cc0 wceq cv copab eleq1 adantl
      wb metidval adantr breqd bi2anan9 oveq12 eqeq1d anbi12d eqid brabga bitrd
      ibar bitr4d ) CDGHIZADIZBDIZJZJZABCKHZLZUPABCMZNOZJZVAUQUSABEPZDIZFPZDIZJ
      ZVCVECMZNOZJZEFQZLZVBUQURVKABUMURVKOUPEFCDUAUBUCUPVLVBTUMVJVBEFABVKDDVCAO
      ZVEBOZJZVGUPVIVAVMVDUNVNVFUOVCADRVEBDRUDVOVHUTNVCAVEBCUEUFUGVKUHUISUJUPVA
      VBTUMUPVAUKSUL $.
  $}

  ${
    $( Basic property of the metric identification relation.  (Contributed by
       Thierry Arnoux, 7-Feb-2018.) $)
    metideq $p |- ( ( D e. ( PsMet ` X ) /\
      ( A ( ~Met ` D ) B /\ E ( ~Met ` D ) F ) ) -> ( A D E ) = ( B D F ) ) $=
      ( wcel wbr wa co wceq cle cxr wss syl syl2anc sseldd psmetsym cxad cc0 wb
      cpsmet cfv cmetid simpl cdm metidss dmss dmxpid syl6sseq wrel xpss syl6ss
      cxp cvv df-rel sylibr simprl releldm syl3anc fovrnda syl12anc eqeltrd crn
      simprr psmetf rnss rnxpid eqeltrrd psmettri2 syl13anc jca metidv syl21anc
      relelrn biimpa eqtr3d oveq1d xaddid2 eqtrd breqtrd oveq2d xaddid1 xrletrd
      3eqtrd 3eqtr4d xrletri3 mpbird ) CFUBUCGZABCUDUCZHZDEWJHZIZIZADCJZBECJZKZ
      WOWPLHZWPWOLHZIZWNWRWSWNWOBDCJZWPWNWODACJZMWNWIAFGZDFGZWOXBKWIWMUEZWNWJUF
      ZFAWNWIXFFNXEWIXFFFUNZUFZFWIWJXGNZXFXHNCFUGZWJXGUHOFUIUJOZWNWJUKZWKAXFGWN
      WIXLXEWIWJUOUOUNZNXLWIWJXGXMXJFFULUMWJUPUQOZWIWKWLURZABWJUSPQZWNXFFDXKWNX
      LWLDXFGXNWIWKWLVEZDEWJUSPQZADCFRUTZWNWIXDXCXBMGZXEXRXPWIDAMFFCCFVFZVAVBZV
      CZWNWIBFGZXDXAMGZXEWNWJVDZFBWNWIYFFNXEWIYFXGVDZFWIXIYFYGNXJWJXGVGOFVHUJOZ
      WNXLWKBYFGXNXOABWJVOPQZXRWIBDMFFCYAVAVBZWNEBCJZWPMWNWIEFGZYDYKWPKXEWNYFFE
      YHWNXLWLEYFGXNXQDEWJVOPQZYIEBCFRUTZWNWIYLYDYKMGZXEYMYIWIEBMFFCYAVAVBZVIZW
      NWOBACJZXASJZXALWNWIYDXCXDWOYSLHXEYIXPXRADBCFVJVKWNYSTXASJZXAWNYRTXASWNAB
      CJZYRTWNWIXCYDUUAYRKXEXPYIABCFRUTWNWIXCYDIZWKUUATKZXEWNXCYDXPYIVLXOWIUUBI
      WKUUCABCFVMVPVNZVQVRWNYEYTXAKYJXAVSOVTWAWNXAYKEDCJZSJZWPLWNWIYLYDXDXAUUFL
      HXEYMYIXRBDECFVJVKWNUUFYKTSJZYKWPWNUUETYKSWNUUEDECJZTWNWIYLXDUUEUUHKXEYMX
      REDCFRUTWNWIXDYLIZWLUUHTKZXEWNXDYLXRYMVLXQWIUUIIWLUUJDECFVMVPVNZVTWBWNYOU
      UGYKKYPYKWCOYNWEWAWDWNWPAECJZWOYQWNWIXCYLUULMGZXEXPYMWIAEMFFCYAVAVBZYCWNW
      PUUAUULSJZUULLWNWIXCYDYLWPUUOLHXEXPYIYMBEACFVJVKWNUUOTUULSJZUULWNUUATUULS
      UUDVRWNUUMUUPUULKUUNUULVSOVTWAWNUULXBUUHSJZWOLWNWIXDXCYLUULUUQLHXEXRXPYMA
      EDCFVJVKWNXBTSJZXBUUQWOWNXTUURXBKYBXBWCOWNUUHTXBSUUKWBXSWFWAWDVLWNWOMGWPM
      GWQWTUAYCYQWOWPWGPWH $.

    $d x y z D $.  $d x y z X $.
    $( The metric identification is an equivalence relation. (Contributed by
       Thierry Arnoux, 11-Feb-2018.) $)
    metider $p |- ( D e. ( PsMet ` X ) -> ( ~Met ` D ) Er X ) $=
      ( vx wcel cv wbr wa ssbrd imp brxp sylib co cc0 wceq metidv wb cle syldan
      cxad simpld cpsmet cfv cmetid cvv cxp wss wrel metidss xpss syl6ss df-rel
      vy sylibr psmetsym 3expb eqeq1d ancom2s 3bitr4d biimpd impancom mpd simpl
      vz simprr simprl simprd psmettri2 syl13anc eqtr3d oveq12d cxr 0xr xaddid1
      mpbid ax-mp breqtrd psmetge0 syl3anc psmetcl xrletri3 mpan2 syl mpbir2and
      syl6eq syl12anc mpbird psmet0 anabsan2 impbida iserd ) ABUAUBDZCULVCBAUCU
      BZWKWLUDUDUEZUFWLUGWKWLBBUEZWMABUHZBBUIUJWLUKUMWKCEZULEZWLFZGZWPBDZWQBDZG
      ZWQWPWLFZWSWPWQWNFZXBWKWRXDWKWLWNWPWQWOHIWPWQBBJKZWKXBWRXCWKXBGZWRXCXFWPW
      QALZMNZWQWPALZMNZWRXCXFXGXIMWKWTXAXGXINZWPWQABUNUOZUPWPWQABOZWKXAWTXCXJPW
      QWPABOUQURUSUTVAWKWRWQVCEZWLFZGZGZWPXNWLFZWPXNALZMNZXQXTXSMQFZMXSQFZXQXSX
      IWQXNALZSLZMQXQWKXAWTXNBDZXSYDQFWKXPVBZXQXAYEWKXPXOXAYEGZWKWRXOVDZWKXOGWQ
      XNWNFZYGWKXOYIWKWLWNWQXNWOHIWQXNBBJKRZTXQWTXAWKXPWRXBWKWRXOVEZXERZTZXQXAY
      EYJVFZWPXNWQABVGVHXQYDMMSLZMXQXIMYCMSXQXGXIMWKXPXBXKYLXLRXQWRXHYKWKXPXBWR
      XHPYLXMRVNVIXQXOYCMNZYHWKXPYGXOYPPYJWQXNABORVNVJMVKDZYOMNVLMVMVOWDVPXQWKW
      TYEYBYFYMYNWPXNABVQVRXQXSVKDZXTYAYBGPZXQWKWTYEYRYFYMYNWPXNABVSVRYRYQYSVLX
      SMVTWAWBWCXQWKWTYEXRXTPYFYMYNWPXNABOWEWFWKWTWPWPWLFZWKWTGYTWPWPALMNZWPABW
      GWKWTYTUUAPWPWPABOWHWFWKYTGZWTWTUUBWPWPWNFZWTWTGWKYTUUCWKWLWNWPWPWOHIWPWP
      BBJKTWIWJ $.
  $}

  ${
    $d a b c d x y z D $.  $d a b c d x y z X $.  $d a b c d x y z .~ $.
    pstmval.1 $e |- .~ = ( ~Met ` D ) $.
    $( Value of the metric induced by a pseudometric ` D ` .  (Contributed by
       Thierry Arnoux, 7-Feb-2018.) $)
    pstmval $p |- ( D e. ( PsMet ` X ) -> ( pstoMet ` D ) =
      ( a e. ( X /. .~ ) , b e. ( X /. .~ )
      |-> U. { z | E. x e. a E. y e. b z = ( x D y ) } ) ) $=
      ( vd vc cpsmet cfv wcel cv cdm co wceq wrex cvv cmetid cqs cab cuni cmpt2
      crn cpstm cmpt df-pstm wa psmetdmdm adantr dmeq dmeqd adantl eqtr4d qseq1
      a1i syl fveq2 syl6reqr eqtr2d mpt2eq12 syl2anc w3a simp1r eqeq2d 2rexbidv
      qseq2 oveqd abbidv unieqd mpt2eq3dva elfvdm eleq2d rspcev mpancom wfun wb
      eqtrd cc0 cxad cle wbr wral cxr cmap crab df-psmet funmpt2 elunirn sylibr
      cxp ax-mp elfvex qsexg eqid mpt2exg fvmptd ) DFLMZNZJDGHJOZPZPZXBUAMZUBZX
      FCOZAOZBOZXBQZRZBHOZSAGOZSZCUCZUDZUEZGHFEUBZXRXGXHXIDQZRZBXLSAXMSZCUCZUDZ
      UEZLUFUDZUGTUGJYEXQUHRXAABCGHJUIURXAXBDRZUJZXQGHXRXRXPUEZYDYGXFXRRZYIXQYH
      RYGXRXDEUBZXFYGFXDRXRYJRYGFDPZPZXDXAFYLRYFDFUKULYFXDYLRXAYFXCYKXBDUMUNUOU
      PFXDEUQUSYFYJXFRZXAYFEXERYMYFXEDUAMEXBDUAUTIVAEXEXDVIUSUOVBZYNGHXFXFXRXRX
      PVCVDYGGHXRXRXPYCYGXMXRNZXLXRNZVEZXOYBYQXNYACYQXKXTABXMXLYQXJXSXGYQXBDXHX
      IXAYFYOYPVFVJVGVHVKVLVMVTXADXHLMZNZALPZSZDYENZFYTNXAUUADFLVNYSXAAFYTXHFRY
      RWTDXHFLUTVOVPVQLVRUUBUUAVSATXMXMXBQWARXMXLXBQKOZXMXBQUUCXLXBQWBQWCWDKXHW
      EHXHWEUJGXHWEJWFXHXHWMWGQWHLAGHKJWIWJADLWKWNWLXAXRTNZUUDYDTNXAFTNUUDDFLWO
      FETWPUSZUUEGHXRXRYCTTYDYDWQWRVDWS $.

    $d a b e f z .~ $.  $d a b e f x y z A $.  $d a b e f x y z B $.
    $d e f z D $.  $d e f z X $.
    $( Function value of the metric induced by a pseudometric ` D `
       (Contributed by Thierry Arnoux, 11-Feb-2018.) $)
    pstmfval $p |- ( ( D e. ( PsMet ` X ) /\ A e. X /\ B e. X ) ->
      ( [ A ] .~ ( pstoMet ` D ) [ B ] .~ ) = ( A D B ) ) $=
      ( vx vy vz va vb ve wcel co cv wceq wrex cvv wbr wb vf cpsmet cfv w3a cec
      cpstm cqs cab cuni cmpt2 pstmval 3ad2ant1 cmetid eqeltri ecelqsi 3ad2ant2
      oveqd fvex 3ad2ant3 rexeq abbidv unieqd rexbidv eqid ecexg ax-mp ab2rexex
      uniex ovmpt2 syl2anc csn wa simpr3 simpl1 simpr1 cxp wss metidss syl5eqss
      wrel syl6ss df-rel sylibr adantr relelec mpbid breqi sylib simpr2 metideq
      xpss syl12anc eqtr4d adantlr 3anassrs oveq1 eqeq2d cbvrex2v biimpi adantl
      syl oveq2 r19.29_2a cc0 simpl2 psmet0 3syl a1i breqd metidv 3bitrd mpbird
      ex simpl3 simpr rspc2ev syl3anc impbid df-sn syl6eqr unisn syl6eq 3eqtrd
      ovex ) CEUBUCMZAEMZBEMZUDZADUEZBDUEZCUFUCZNYIYJGHEDUGZYLIOZJOZKOZCNZPZKHO
      ZQZJGOZQZIUHZUIZUJZNZYQKYJQZJYIQZIUHZUIZABCNZYHYKUUDYIYJYEYFYKUUDPYGJKICD
      EGHFUKULUQYHYIYLMZYJYLMZUUEUUIPYFYEUUKYGEADDCUMUCZRFCUMURUNZUOUPYGYEUULYF
      EBDUUNUOUSGHYIYJYLYLUUCUUIUUDYSJYIQZIUHZUIYTYIPZUUBUUPUUQUUAUUOIYSJYTYIUT
      VAVBYRYJPZUUPUUHUURUUOUUGIUURYSUUFJYIYQKYRYJUTVCVAVBUUDVDUUHJKIYIYJYPDRMZ
      YIRMUUNARDVEVFUUSYJRMUUNBRDVEVFVGVHVIVJYHUUIUUJVKZUIUUJYHUUHUUTYHUUHYMUUJ
      PZIUHUUTYHUUGUVAIYHUUGUVAYHUUGUVAYHUUGVLZYMLOZUAOZCNZPZUVALUAYIYJUVBUVCYI
      MZUVDYJMZUVFUVAYHUVGUVHUVFUDZUVAUUGYHUVIVLZYMUVEUUJYHUVGUVHUVFVMUVJYEAUVC
      UUMSZBUVDUUMSZUUJUVEPYEYFYGUVIVNUVJAUVCDSZUVKUVJUVGUVMYHUVGUVHUVFVOUVJDVT
      ZUVGUVMTYHUVNUVIYEYFUVNYGYEDRRVPZVQUVNYEDEEVPZUVOYEDUUMUVPFCEVRVSEEWKWADW
      BWCZULWDZUVCADWEXAWFAUVCDUUMFWGWHUVJBUVDDSZUVLUVJUVHUVSYHUVGUVHUVFWIUVJUV
      NUVHUVSTUVRUVDBDWEXAWFBUVDDUUMFWGWHAUVCCBUVDEWJWLWMWNWOUUGUVFUAYJQLYIQZYH
      UUGUVTYQUVFYMUVCYOCNZPJKLUAYIYJYNUVCPYPUWAYMYNUVCYOCWPWQYOUVDPUWAUVEYMYOU
      VDUVCCXBWQWRWSWTXCXMYHUVAUUGYHUVAVLZAYIMZBYJMZUVAUUGUWBUWCAACNXDPZUWBYEYF
      UWEYEYFYGUVAVNZYEYFYGUVAXEZACEXFVJUWBUWCAADSZAAUUMSZUWEUWBYEUVNUWCUWHTUWF
      UVQAADWEXGUWBDUUMAADUUMPUWBFXHZXIUWBYEYFYFUWIUWETUWFUWGUWGAACEXJWLXKXLUWB
      UWDBBCNXDPZUWBYEYGUWKUWFYEYFYGUVAXNZBCEXFVJUWBUWDBBDSZBBUUMSZUWKUWBYEUVNU
      WDUWMTUWFUVQBBDWEXGUWBDUUMBBUWJXIUWBYEYGYGUWNUWKTUWFUWLUWLBBCEXJWLXKXLYHU
      VAXOYQUVAYMAYOCNZPJKABYIYJYNAPYPUWOYMYNAYOCWPWQYOBPUWOUUJYMYOBACXBWQXPXQX
      MXRVAIUUJXSXTVBUUJABCYDYAYBYC $.

    $( The metric induced by a pseudometric is a full-fledged metric on the
       equivalence classes of the metric identification.  (Contributed by
       Thierry Arnoux, 11-Feb-2018.) $)
    pstmxmet $p |- ( D e. ( PsMet ` X ) ->
      ( pstoMet ` D ) e. ( *Met ` ( X /. .~ ) ) ) $=
      ( vx vy vz va vb wcel cxr cv co cc0 wceq wb wral wa cvv r19.29a vc cpsmet
      cfv cpstm cqs cxmt cxp wf cxad cle wbr wfn wrex cuni cmpt2 ab2rexex uniex
      cab vex rgen2w eqid fnmpt2 ax-mp pstmval fneq1d cec simpllr simpr oveq12d
      mpbiri simp-5l simp-4r simplr pstmfval syl3anc eqtrd psmetf eqeltrd elqsi
      fovrnd ad2antll ad2antrr ad2antrl ralrimivva ffnov sylanbrc simpll eqeq1d
      syl cmetid breqi metidv anassrs syl5bb bitr4d wer ereq1 sylibr erth bitrd
      metider adantllr adantlr adantr eqeq12d 3bitr4d simp-6l simp-6r psmettri2
      syl13anc simp-5r syl21anc breq12d adantl6r ad5antlr adantl5r ad4antlr jca
      mpbird adantl4r ad3antlr ralrimiva anasss elfvex qsexg isxmet 3syl ) ACUB
      UCJZAUDUCZCBUEZUFUCJZYJYJUGZKYIUHZELZFLZYIMZNOZYNYOOZPZYPGLZYNYIMZYTYOYIM
      ZUIMZUJUKZGYJQZRZFYJQEYJQZRZYHYMUUGYHYIYLULZYPKJZFYJQEYJQYMYHUUIEFYJYJYTH
      LZILZAMZOIYOUMHYNUMGURZUNZUOZYLULZUUOSJZFYJQEYJQUUQUUREFYJYJUUNHIGYNYOUUM
      EUSFUSUPUQUTEFYJYJUUOUUPSUUPVAVBVCYHYLYIUUPHIGABCEFDVDVEVJYHUUJEFYJYJYHYN
      YJJZYOYJJZRZRZYNUUKBVFZOZUUJHCUVBUUKCJZRZUVDRZYOUULBVFZOZUUJICUVGUULCJZRZ
      UVIRZYPUUMKUVLYPUVCUVHYIMZUUMUVLYNUVCYOUVHYIUVFUVDUVJUVIVGZUVKUVIVHZVIZUV
      LYHUVEUVJUVMUUMOZYHUVAUVEUVDUVJUVIVKZUVBUVEUVDUVJUVIVLZUVGUVJUVIVMZUUKUUL
      ABCDVNZVOVPUVLUUKUULKCCAUVLYHCCUGKAUHUVRACVQWIUVSUVTVTVRUVBUVIICUMZUVEUVD
      UUTUWBYHUUSICYOBVSZWAWBZTUUSUVDHCUMZYHUUTHCYNBVSZWCZTWDEFYJYJKYIWEWFYHUUF
      EFYJYJUVBYSUUEUVBUVDYSHCUVGUVIYSICUVLUVMNOZUVCUVHOZYQYRUVKUWHUWIPZUVIUVFU
      VJUWJUVDYHUVEUVJUWJUVAYHUVERZUVJRZUWHUUKUULBUKZUWIUWLUWHUUMNOZUWMUWLUVMUU
      MNUWLYHUVEUVJUVQYHUVEUVJWGZYHUVEUVJVMZUWKUVJVHUWAVOZWHUWMUUKUULAWJUCZUKZU
      WLUWNUUKUULBUWRDWKYHUVEUVJUWSUWNPUUKUULACWLWMWNWOUWLUUKUULBCUWLCUWRWPZCBW
      PZUWLYHUWTUWOACXAWIBUWROUXAUWTPDCBUWRWQVCWRUWPWSWTXBXCXDUVLYPUVMNUVPWHUVL
      YNUVCYOUVHUVNUVOXEXFUWDTUWGTYHUUSUUTUUEYHUUSRUUTRZUUDGYJUXBYTYJJZRUVDUUDH
      CYHUUSUUTUXCUVEUVDUUDYHUUTRUXCRUVERUVDRUVIUUDICYHUUTUXCUVEUVDUVJUVIUUDYHU
      XCRUVERUVDRUVJRUVIRYTUALZBVFZOZUUDUACYHUXCUVEUVDUVJUVIUXDCJZUXFUUDUWKUVDR
      ZUVJRZUVIRZUXGRZUXFRZUUDUUMUXDUUKAMZUXDUULAMZUIMZUJUKZUXLYHUXGUVEUVJUXPYH
      UVEUVDUVJUVIUXGUXFXGZUXJUXGUXFVMZYHUVEUVDUVJUVIUXGUXFXHZUXHUVJUVIUXGUXFVL
      ZUUKUULUXDACXIXJUXLYPUUMUUCUXOUJUXLYPUVMUUMUXLYNUVCYOUVHYIUWKUVDUVJUVIUXG
      UXFXKZUXIUVIUXGUXFVGZVIUXLYHUVEUVJUVQUXQUXSUXTUWQXLVPUXLUUAUXMUUBUXNUIUXL
      UUAUXEUVCYIMZUXMUXLYTUXEYNUVCYIUXKUXFVHZUYAVIUXLYHUXGUVEUYCUXMOUXQUXRUXSU
      XDUUKABCDVNVOVPUXLUUBUXEUVHYIMZUXNUXLYTUXEYOUVHYIUYDUYBVIUXLYHUXGUVJUYEUX
      NOUXQUXRUXTUXDUULABCDVNVOVPVIXMXSXNUXCUXFUACUMYHUVEUVDUVJUVIUACYTBVSXOTXP
      UUTUWBYHUXCUVEUVDUWCXQTXTUUSUWEYHUUTUXCUWFYATYBYCXRWDXRYHCSJYJSJYKUUHPACU
      BYDCBSYEEFGSYIYJYFYGXS $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Continuity - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    hauseqcn.x $e |- X = U. J $.
    hauseqcn.k $e |- ( ph -> K e. Haus ) $.
    hauseqcn.f $e |- ( ph -> F e. ( J Cn K ) ) $.
    hauseqcn.g $e |- ( ph -> G e. ( J Cn K ) ) $.
    hauseqcn.e $e |- ( ph -> ( F |` A ) = ( G |` A ) ) $.
    hauseqcn.a $e |- ( ph -> A C_ X ) $.
    hauseqcn.c $e |- ( ph -> ( ( cls ` J ) ` A ) = X ) $.
    $( In a Hausdorff topology, two continuous functions which agree on a dense
       set agree everywhere.  (Contributed by Thierry Arnoux, 28-Dec-2017.) $)
    hauseqcn $p |- ( ph -> F = G ) $=
      ( wceq cin wss cfv wcel 3syl cuni cdm ccl ctop ccn co cntop1 dmin wf eqid
      syl cnf fdm ineq12d syl6eq syl5sseq cres wfn wb syl6sseq fnreseql syl3anc
      inidm ffn mpbid ccld hauseqlcld cldcls 3sstr3d syl5eqssr fneqeql2 syl2anc
      clsss mpbird ) ACDOZEUAZCDPUBZQZAVPGVQHABEUCRZRZVQVSRZGVQAEUDSZVQVPQBVQQZ
      VTWAQACEFUEUFZSZWBJCEFUGUKACUBZDUBZPZVQVPCDUHAWHVPVPPVPAWFVPWGVPAWEVPFUAZ
      CUIZWFVPOJCEFVPWIVPUJZWIUJZULZVPWICUMTADWDSZVPWIDUIZWGVPOKDEFVPWIWKWLULZV
      PWIDUMTUNVPVCUOUPACBUQDBUQOZWCLACVPURZDVPURZBVPQWQWCUSAWEWJWRJWMVPWICVDTZ
      AWNWOWSKWPVPWIDVDTZABGVPMHUTVPCDBVAVBVEVQBEVPWKVMVBNAVQEVFRSWAVQOACDEFIJK
      VGVQEVHUKVIVJAWRWSVOVRUSWTXAVPCDVKVLVN $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Topology of the closed unit
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The closed unit is a subset of the set of the complex numbers Useful lemma
     for manipulating probabilities within the closed unit.  (Contributed by
     Thierry Arnoux, 12-Dec-2016.) $)
  unitsscn $p |- ( 0 [,] 1 ) C_ CC $=
    ( cc0 c1 cicc co cr cc unitssre ax-resscn sstri ) ABCDEFGHI $.

  $( The closed unit is a subset of the set of the real numbers Useful lemma
     for manipulating probabilities within the closed unit.  (Contributed by
     Thierry Arnoux, 21-Dec-2016.) $)
  elunitrn $p |- ( A e. ( 0 [,] 1 ) -> A e. RR ) $=
    ( cc0 c1 cicc co wcel cr cle wbr 0re 1re elicc2i simp1bi ) ABCDEFAGFBAHIACH
    IBCAJKLM $.

  $( The closed unit is a subset of the set of the complext numbers Useful
     lemma for manipulating probabilities within the closed unit.  (Contributed
     by Thierry Arnoux, 21-Dec-2016.) $)
  elunitcn $p |- ( A e. ( 0 [,] 1 ) -> A e. CC ) $=
    ( cc0 c1 cicc co wcel elunitrn recnd ) ABCDEFAAGH $.

  $( An element of the closed unit is positive Useful lemma for manipulating
     probabilities within the closed unit.  (Contributed by Thierry Arnoux,
     20-Dec-2016.) $)
  elunitge0 $p |- ( A e. ( 0 [,] 1 ) -> 0 <_ A ) $=
    ( cc0 c1 cicc co wcel cr cle wbr 0re 1re elicc2i simp2bi ) ABCDEFAGFBAHIACH
    IBCAJKLM $.

  $( The closed unit is a subset of the set of the extended non-negative
     reals.  Useful lemma for manipulating probabilities within the closed
     unit.  (Contributed by Thierry Arnoux, 12-Dec-2016.) $)
  unitssxrge0 $p |- ( 0 [,] 1 ) C_ ( 0 [,] +oo ) $=
    ( cc0 cpnf cicc co wcel c1 wss cxr cle wbr 0xr pnfxr pnfge ax-mp lbicc2 1re
    mp3an rexri 0le1 mp2an w3a wb elicc1 mpbir3an iccss2 ) AABCDZEZFUFEZAFCDUFG
    AHEZBHEZABIJZUGKLUIUKKAMNABOQUHFHEZAFIJZFBIJZFPRZSULUNUOFMNUIUJUHULUMUNUAUB
    KLABFUCTUDABAFUET $.

  $( Necessary conditions for a quotient to be in the closed unit.  (somewhat
     too strong, it would be sufficient that A and B are in RR+) (Contributed
     by Thierry Arnoux, 20-Dec-2016.) $)
  unitdivcld $p |- ( ( A e. ( 0 [,] 1 ) /\ B e. ( 0 [,] 1 ) /\ B =/= 0 ) ->
                                   ( A <_ B <-> ( A / B ) e. ( 0 [,] 1 ) ) ) $=
    ( cc0 c1 cicc co w3a cle wbr cr wa elunitrn 3ad2ant1 simp3 adantr elunitge0
    wcel wb 0re 1re wne cdiv 3ad2ant2 redivcld clt ltlen sylancr biimpar 3com23
    3impb mpd3an3 3adant1 divge0 syl22anc a1i ledivmul syl112anc ax-1rid breq2d
    cmul syl bitr2d biimpa 3jca ex syl5ibr impbid elicc2i syl6bbr ) ACDEFZQZBVJ
    QZBCUAZGZABHIZABUBFZJQZCVPHIZVPDHIZGZVPVJQVNVOVTVNVOVTVNVOKVQVRVSVNVQVOVNAB
    VKVLAJQZVMALMZVLVKBJQZVMBLZUCZVKVLVMNUDOVNVRVOVNWACAHIZWCCBUEIZVRWBVKVLWFVM
    APMWEVLVMWGVKVLVMCBHIZWGVLWHVMBPOVLWHVMWGVLWHVMWGVLWGWHVMKZVLCJQWCWGWIRSWDC
    BUFUGUHUJUIUKULZABUMUNOVNVOVSVNVSABDUTFZHIZVOVNWADJQZWCWGVSWLRWBWMVNTUOWEWJ
    ADBUPUQVNWCWLVORWEWCWKBAHBURUSVAVBZVCVDVEVTVOVNVSVQVRVSNWNVFVGCDVPSTVHVI $.

  ${
    $d x y $.
    df-iis $e |- I = ( ( mulGrp ` CCfld ) |`s ( 0 [,] 1 ) ) $.
    $( The closed unit forms a topological monoid.  (Contributed by Thierry
       Arnoux, 25-Mar-2017.) $)
    iistmd $p |- I e. TopMnd $=
      ( vx vy ccnfld cmgp cfv ctmd wcel cc0 c1 cicc co csubmnd cnnrg mp2b cc cv
      cmul wral cnrg ctrg nrgtrg trgtmd wss unitsscn 1elunit iimulcl rgen2a w3a
      eqid cmnd wb crg nrgrng rngmgp cnfldbas mgpbas rngidval cnfldmul mgpplusg
      cnfld1 issubm ax-mp mpbir3an submtmd mp2an ) EFGZHIZJKLMZVHNGIZAHIEUAIZEU
      BIVIOEUCEVHVHUKZUDPVKVJQUEZKVJIZCRZDRZSMVJIZDVJTCVJTZUFUGVRCDVJVPVQUHUIVH
      ULIZVKVNVOVSUJUMVLEUNIVTOEUOEVHVMUPPCDQSVJVHKQEVHVMUQUREKVHVMVBUSESVHVMUT
      VAVCVDVEVJVHABVFVG $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Topology of ` ( RR X. RR ) `
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    unicls.1 $e |- J e. Top $.
    unicls.2 $e |- X = U. J $.
    $( The union of the closed set is the underlying set of the topology.
       (Contributed by Thierry Arnoux, 21-Sep-2017.) $)
    unicls $p |- U. ( Clsd ` J ) = X $=
      ( ccld cfv cuni wss wcel wceq cpw cldss2 sspwuni mpbi ctop topcld unissel
      ax-mp mp2an ) AEFZGZBHZBTIZUABJTBKHUBABDLTBMNAOIUCCABDPRTBQS $.
  $}

  ${
    tpr2tp.0 $e |- J = ( topGen ` ran (,) ) $.
    $( The usual topology on ` ( RR X. RR ) ` is the product topology of the
       usual topology on ` RR ` .  (Contributed by Thierry Arnoux,
       21-Sep-2017.) $)
    tpr2tp $p |- ( J tX J ) e. ( TopOn ` ( RR X. RR ) ) $=
      ( cr ctopon cfv wcel ctx cxp cioo crn ctg retopon eqeltri txtopon mp2an
      co ) ACDEZFZRAAGPCCHDEFAIJKEQBLMZSAACCNO $.

    $( The usual topology on ` ( RR X. RR ) ` is the product topology of the
       usual topology on ` RR ` .  (Contributed by Thierry Arnoux,
       21-Sep-2017.) $)
    tpr2uni $p |- U. ( J tX J ) = ( RR X. RR ) $=
      ( cr cxp ctx co cuni tpr2tp toponunii eqcomi ) CCDZAAEFZGKLABHIJ $.
  $}

  ${
    $d r A $.  $d r B $.
    $( Rewrite the cartesian product of two sets as the intersection of their
       preimage by ` 1st ` and ` 2nd ` , the projections on the first and
       second elements.  (Contributed by Thierry Arnoux, 22-Sep-2017.) $)
    xpinpreima $p |- ( A X. B ) = ( ( `' ( 1st |` ( _V X. _V ) ) " A )
                                i^i ( `' ( 2nd |` ( _V X. _V ) ) " B ) ) $=
      ( vr c1st cfv wcel cvv cxp crab c2nd cin cres ccnv cima wf wceq fncnvima2
      wfn ffn mp2b cv wa inrab f1stres fvres eleq1d rabbiia f2ndres ineq12i xp2
      eqtri 3eqtr4ri ) CUAZDEZAFZCGGHZIZUMJEZBFZCUPIZKUOUSUBCUPIDUPLZMANZJUPLZM
      BNZKABHUOUSCUPUCVBUQVDUTVBUMVAEZAFZCUPIZUQUPGVAOVAUPRVBVGPGGUDUPGVASCUPAV
      AQTVFUOCUPUMUPFZVEUNAUMUPDUEUFUGUKVDUMVCEZBFZCUPIZUTUPGVCOVCUPRVDVKPGGUHU
      PGVCSCUPBVCQTVJUSCUPVHVIURBUMUPJUEUFUGUKUICABUJUL $.

    $d r E $.  $d r F $.
    $( Rewrite the cartesian product of two sets as the intersection of their
       preimage by ` 1st ` and ` 2nd ` , the projections on the first and
       second elements.  (Contributed by Thierry Arnoux, 22-Sep-2017.) $)
    xpinpreima2 $p |- ( ( A C_ E /\ B C_ F )
                -> ( A X. B ) = ( ( `' ( 1st |` ( E X. F ) ) " A )
                              i^i ( `' ( 2nd |` ( E X. F ) ) " B ) ) ) $=
      ( vr wss wa cxp c1st cfv wcel crab c2nd cin cres ccnv cima sseldd syl6eqr
      cvv cv xpss rabss2 mp1i simprl simpll simprrl simplr simprrr jca sylanbrc
      elxp7 rabss3d eqssd xp2 syl6reqr inrab wf wfn wceq f1stres fncnvima2 mp2b
      ffn fvres eleq1d rabbiia eqtri f2ndres ineq12i ) ACFZBDFZGZABHZEUAZIJZAKZ
      ECDHZLZVOMJZBKZEVRLZNZIVROZPAQZMVROZPBQZNVMVNVQWAGZEVRLZWCVMWIWHETTHZLZVN
      VMWIWKVRWJFWIWKFVMCDUBWHEVRWJUCUDVMWHEWJVRVMVOWJKZWHGZGZWLVPCKZVTDKZGVOVR
      KZVMWLWHUEWNWOWPWNACVPVKVLWMUFVMWLVQWAUGRWNBDVTVKVLWMUHVMWLVQWAUIRUJVOCDU
      LUKUMUNEABUOUPVQWAEVRUQSWEVSWGWBWEVOWDJZAKZEVRLZVSVRCWDURWDVRUSWEWTUTCDVA
      VRCWDVDEVRAWDVBVCWSVQEVRWQWRVPAVOVRIVEVFVGVHWGVOWFJZBKZEVRLZWBVRDWFURWFVR
      USWGXCUTCDVIVRDWFVDEVRBWFVBVCXBWAEVRWQXAVTBVOVRMVEVFVGVHVJS $.
  $}

  ${
    $( The complex square of side ` D ` is a subset of the complex circle of
       radius ` D ` .  (Contributed by Thierry Arnoux, 25-Sep-2017.) $)
    sqsscirc1 $p |- ( ( ( ( X e. RR /\ 0 <_ X ) /\ ( Y e. RR /\ 0 <_ Y ) )
      /\ D e. RR+ ) -> ( ( X < ( D / 2 ) /\ Y < ( D / 2 ) ) ->
      ( sqr ` ( ( X ^ 2 ) + ( Y ^ 2 ) ) ) < D ) ) $=
      ( cr wcel cc0 cle wbr wa c2 cdiv co clt csqr cfv a1i cmul 2re c1 c4 caddc
      crp simp-4l resqcld simpllr simpld readdcld sqge0d addge0d resqrcld rpred
      simplr rehalfcld simprl simp-4r rpge0d divge0d lt2sqd mpbid simprr simprd
      cexp 2rp lt2addd sqrltd rpre recnd 2timesd fveq2d rpge0 sqrsqd oveq2d 0re
      2pos ltleii sqrmuld cc 2cn sqrcld rpcn 2ne0 div32d 3eqtr4d eqtr3d 2lt4 wb
      wne 4re 4pos sqrlt mp4an mpbi sqrpclii ltdiv1ii sqrsq mp2an oveq1i fveq2i
      wceq sq2 dividi 3eqtr3i breqtri 1re ltmul1d mpbii mulid2d breqtrd eqbrtrd
      id syl lttrd ex ) BDEZFBGHZIZCDEZFCGHZIZIZAUBEZIZBAJKLZMHZCYCMHZIZBJVBLZC
      JVBLZUALZNOZAMHYBYFIZYJYCJVBLZYLUALZNOZAYKYIYKYGYHYKBXNXOXSYAYFUCZUDZYKCY
      KXQXRXPXSYAYFUEZUFZUDZUGZYKYGYHYPYSYKBYOUHYKCYRUHUIZUJYKYMYKYLYLYKYCYKAYK
      AXTYAYFULZUKZUMZUDZUUEUGZYKYLYLUUEUUEYKYCUUDUHZUUGUIZUJUUCYKYIYMMHYJYNMHY
      KYGYHYLYLYPYSUUEUUEYKYDYGYLMHYBYDYEUNYKBYCYOUUDXNXOXSYAYFUOYKAJUUCJUBEZYK
      VCPYKAUUBUPUQZURUSYKYEYHYLMHYBYDYEUTYKCYCYRUUDYKXQXRYQVAUUJURUSVDYKYIYMYT
      UUAUUFUUHVEUSYKYAYNAMHUUBYAYNJNOZJKLZAQLZAMYAJYLQLZNOZYNUUMYAUUNYMNYAYLYA
      YLYAYCYAAAVFZUMZUDZVGVHVIYAUUKYLNOZQLUUKYCQLUUOUUMYAUUSYCUUKQYAYCUUQYAAJU
      UPUUIYAVCPAVJUQVKVLYAJYLJDEZYARPZFJGHZYAFJVMRVNVOZPZUURYAYCUUQUHVPYAUUKJA
      YAJJVQEYAVRPZVSUVEAVTZJFWGYAWAPWBWCWDYAUUMSAQLZAMYAUULSMHUUMUVGMHUULTNOZJ
      KLZSMUUKUVHMHZUULUVIMHJTMHZUVJWEUUTUVBTDEFTGHUVKUVJWFRUVCWHFTVMWHWIVOJTWJ
      WKWLUUKUVHJJRVNWMTWHWIWMRVNWNWLJJVBLZNOZJKLJJKLUVISUVMJJKUUTUVBUVMJWSRUVC
      JWOWPWQUVMUVHJKUVLTNWTWRWQJVRWAXAXBXCYAUULSAYAUUKYAJUVAUVDUJUMSDEYAXDPYAX
      JXEXFYAAUVFXGXHXIXKXLXM $.
  $}

  ${
    $( The complex square of side ` D ` is a subset of the complex disc of
       radius ` D ` .  (Contributed by Thierry Arnoux, 25-Sep-2017.) $)
    sqsscirc2 $p |- ( ( ( A e. CC /\ B e. CC ) /\ D e. RR+ ) ->
      ( ( ( abs ` ( Re ` ( B - A ) ) ) < ( D / 2 ) /\
          ( abs ` ( Im ` ( B - A ) ) ) < ( D / 2 ) )
                                              -> ( abs ` ( B - A ) ) < D ) ) $=
      ( cc wcel wa co cfv cabs c2 clt wbr cexp caddc csqr cc0 cle recnd abscld
      cr crp cmin cre cim wi simplr simpll subcld recld absge0d jca imcld simpr
      cdiv sqsscirc1 syl21anc absval2d breq1d absresq syl oveq12d fveq2d bitr4d
      wceq sylibrd ) ADEZBDEZFZCUAEZFZBAUBGZUCHZIHZCJUNGZKLVKUDHZIHZVNKLFZVMJMG
      ZVPJMGZNGZOHZCKLZVKIHZCKLZVJVMTEZPVMQLZFVPTEZPVPQLZFVIVQWBUEVJWEWFVJVLVJV
      LVJVKVJBAVFVGVIUFVFVGVIUGUHZUIZRZSVJVLWKUJUKVJWGWHVJVOVJVOVJVKWIULZRZSVJV
      OWMUJUKVHVIUMCVMVPUOUPVJWDVLJMGZVOJMGZNGZOHZCKLWBVJWCWQCKVJVKWIUQURVJWAWQ
      CKVJVTWPOVJVRWNVSWONVJVLTEVRWNVDWJVLUSUTVJVOTEVSWOVDWLVOUSUTVAVBURVCVE $.
  $}

  ${
    $d x y F $.  $d x G $.  $d x y H $.  $d x y X $.  $d x y Y $.
    cnre2csqlem.1 $e |- ( G |` ( RR X. RR ) ) = ( H o. F ) $.
    cnre2csqlem.2 $e |- F Fn ( RR X. RR ) $.
    cnre2csqlem.3 $e |- G Fn _V $.
    cnre2csqlem.4 $e |- ( x e. ( RR X. RR ) -> ( G ` x ) e. RR ) $.
    cnre2csqlem.5 $e |- ( ( x e. ran F /\ y e. ran F )
                          -> ( H ` ( x - y ) ) = ( ( H ` x ) - ( H ` y ) ) ) $.
    $( Lemma for ~ cnre2csqima (Contributed by Thierry Arnoux, 27-Sep-2017.) $)
    cnre2csqlem $p |- ( ( X e. ( RR X. RR ) /\ Y e. ( RR X. RR ) /\ D e. RR+ )
      -> ( Y e. ( `' ( G |` ( RR X. RR ) )
                                " ( ( ( G ` X ) - D ) (,) ( ( G ` X ) + D ) ) )
           -> ( abs ` ( H ` ( ( F ` Y ) - ( F ` X ) ) ) ) < D ) ) $=
      ( cr wcel cfv cmin co clt wceq cxp crp w3a cres ccnv caddc cioo cima cabs
      wbr wa wfn wb cvv wss fnssres mp2an elpreima mp1i simplbda ex simp2 fvres
      ssv syl eleq1d simp1 cv fveq2 vtoclga simp3 rpred resubcld rexrd readdcld
      cxr elioo2 syl2anc biimpa simp2d simp3d jca sylbid absdiflt biimprd 3syld
      wi syl3anc crn fnfvelrn sylancr oveq1 fveq2d oveq1d oveq2 oveq2d vtocl2ga
      eqeq12d ccom fveq1i fvco2 3eqtr3a oveq12d eqtr4d breq1d sylibrd ) GNNUAZO
      ZHXGOZCUBOZUCZHEXGUDZUEGEPZCQRZXMCUFRZUGRZUHOZHEPZXMQRZUIPZCSUJZHDPZGDPZQ
      RZFPZUIPZCSUJXKXQHXLPZXPOZXNXRSUJZXRXOSUJZUKZYAXKXQYHXKXQXIYHXLXGULZXQXIY
      HUKUMXKEUNULXGUNUOYLKXGVDUNXGEUPUQXGHXPXLURUSUTVAXKYHXRXPOZYKXKYGXRXPXKXI
      YGXRTXHXIXJVBZHXGEVCVEZVFXKYMYKXKYMUKZYIYJYPXRNOZYIYJXKYMYQYIYJUCZXKXNVPO
      XOVPOYMYRUMXKXNXKXMCXKXHXMNOZXHXIXJVGZAVHZEPZNOZYSAGXGUUAGTUUBXMNUUAGEVIV
      FLVJVEZXKCXHXIXJVKVLZVMVNXKXOXKXMCUUDUUEVOVNXNXOXRVQVRVSZVTYPYQYIYJUUFWAW
      BVAWCXKYQYSCNOZYKYAWGXKXIYQYNUUCYQAHXGUUAHTUUBXRNUUAHEVIVFLVJVEUUDUUEYQYS
      UUGUCYAYKXRXMCWDWEWHWFXKYFXTCSXKYEXSUIXKYEYBFPZYCFPZQRZXSXKYBDWIZOZYCUUKO
      ZYEUUJTZXKDXGULZXIUULJYNXGHDWJWKXKUUOXHUUMJYTXGGDWJWKUUABVHZQRZFPZUUAFPZU
      UPFPZQRZTYBUUPQRZFPZUUHUUTQRZTUUNABYBYCUUKUUKUUAYBTZUURUVCUVAUVDUVEUUQUVB
      FUUAYBUUPQWLWMUVEUUSUUHUUTQUUAYBFVIWNWRUUPYCTZUVCYEUVDUUJUVFUVBYDFUUPYCYB
      QWOWMUVFUUTUUIUUHQUUPYCFVIWPWRMWQVRXKXRUUHXMUUIQXKYGHFDWSZPZXRUUHHXLUVGIW
      TYOXKUUOXIUVHUUHTJYNXGFDHXAWKXBXKGXLPZGUVGPZXMUUIGXLUVGIWTXKXHUVIXMTYTGXG
      EVCVEXKUUOXHUVJUUITJYTXGFDGXAWKXBXCXDWMXEXF $.
  $}


  ${
    $d x y z $.  $d u z F $.  $d u z X $.  $d u z Y $.
    cnre2csqima.1 $e |- F = ( x e. RR , y e. RR |-> ( x + ( _i x. y ) ) ) $.
    $( Image of a centered square by the canonical bijection from
       ` ( RR X. RR ) ` to ` CC ` .  (Contributed by Thierry Arnoux,
       27-Sep-2017.) $)
    cnre2csqima $p |- ( ( X e. ( RR X. RR ) /\ Y e. ( RR X. RR ) /\ D e. RR+ )
      -> ( Y e. ( ( ( ( 1st ` X ) - D ) (,) ( ( 1st ` X ) + D ) )
               X. ( ( ( 2nd ` X ) - D ) (,) ( ( 2nd ` X ) + D ) ) ) ->
           ( ( abs ` ( Re ` ( ( F ` Y ) - ( F ` X ) ) ) ) < D /\
             ( abs ` ( Im ` ( ( F ` Y ) - ( F ` X ) ) ) ) < D ) ) ) $=
      ( vz c1st cfv co caddc c2nd wcel cr cre cim cc wceq cvv vu cmin cioo cres
      cxp ccnv cima cin crp w3a cabs clt wbr wa wss wb xpinpreima2 eleq2d mp2an
      ioossre elin cv ci cmul ccj cdiv cmpt2 ccom simpl recnd ax-icn a1i mulcld
      c2 simpr addcld reval syl crre eqtr3d mpt2eq3ia wtru adantl cmpt df-re id
      fveq2 oveq12d oveq1d fmpt2co trud df1stres 3eqtr4ri wral wfn rgen2a ax-mp
      fnmpt2 wfo fo1st fofn xp1st crn cab rnmpt2 adantr eqeltrd rexlimivv abssi
      wrex ex eqsstri sseldi resubd cnre2csqlem imval crim df-im oveq1 df2ndres
      fveq2d fo2nd xp2nd imsubd anim12d syl5bi ) FEIJZCUBKZYGCLKZUCKZEMJZCUBKZY
      KCLKZUCKZUEZNZFIOOUEZUDZUFYJUGZMYQUDZUFYNUGZUHZNZEYQNFYQNCUINUJZFDJEDJUBK
      ZPJUKJCULUMZUUEQJUKJCULUMZUNZYJOUOZYNOUOZYPUUCUPYHYIUTYLYMUTUUIUUJUNYOUUB
      FYJYNOOUQURUSUUCFYSNZFUUANZUNUUDUUHFYSUUAVAUUDUUKUUFUULUUGHUACDIPEFABOOAV
      BZVCBVBZVDKZLKZUUPVEJZLKZVNVFKZVGZABOOUUMVGPDVHZYRABOOUUSUUMUUMONZUUNONZU
      NZUUPPJZUUSUUMUVDUUPRNZUVEUUSSUVDUUMUUOUVDUUMUVBUVCVIVJUVDVCUUNVCRNUVDVKV
      LUVDUUNUVBUVCVOVJVMVPZUUPVQVRUUMUUNVSVTWAUVAUUTSWBABHOORUUPHVBZUVHVEJZLKZ
      VNVFKZUUSDPUVDUVFWBUVGWCZDABOOUUPVGSWBGVLZPHRUVKWDSWBHWEVLUVHUUPSZUVJUURV
      NVFUVNUVHUUPUVIUUQLUVNWFUVHUUPVEWGWHWIWJWKABOOWLWMUVFBOWNAOWNDYQWOUVFABOU
      VGWPABOOUUPDRGWRWQZTTIWSITWOWTTTIXAWQUVHOOXBUVHDXCZNZUAVBZUVPNZUNZUVHUVRU
      VTUVPRUVHUVPUVNBOXJAOXJZHXDRABHOOUUPDGXEUWAHRUVNUVHRNZABOOUVDUVNUWBUVDUVN
      UNUVHUUPRUVDUVNVOUVDUVFUVNUVGXFXGXKXHXIXLZUVQUVSVIXMZUVTUVPRUVRUWCUVQUVSV
      OXMZXNXOHUACDMQEFABOOUUPVCVFKZPJZVGZABOOUUNVGQDVHZYTABOOUWGUUNUVDUUPQJZUW
      GUUNUVDUVFUWJUWGSUVGUUPXPVRUUMUUNXQVTWAUWIUWHSWBABHOORUUPUVHVCVFKZPJZUWGD
      QUVLUVMQHRUWLWDSWBHXRVLUVNUWKUWFPUVHUUPVCVFXSYAWJWKABOOXTWMUVOTTMWSMTWOYB
      TTMXAWQUVHOOYCUVTUVHUVRUWDUWEYDXOYEYFYF $.
  $}

  ${
    $d u v x y z $.  $d d m r x A $.  $d d r B $.  $d d m x G $.  $d d x J $.
    $d d x y m r X $.
    tpr2rico.0 $e |- J = ( topGen ` ran (,) ) $.
    tpr2rico.1 $e |- G = ( u e. RR , v e. RR |-> ( u + ( _i x. v ) ) ) $.
    tpr2rico.2 $e |- B = ran ( x e. ran (,) , y e. ran (,) |-> ( x X. y ) ) $.
    $( For any point of an open set of the usual topology on ` ( RR X. RR ) `
       there is an opened square which contains that point and is entirely in
       the open set.  This is square is actually a ball by the ` ( l ^ +oo ) `
       norm ` X ` .  (Contributed by Thierry Arnoux, 21-Sep-2017.) $)
    tpr2rico $p |- ( ( A e. ( J tX J ) /\ X e. A ) ->
      E. r e. B ( X e. r /\ r C_ A ) ) $=
      ( vd co wcel wa crp cr cc vz vm ctx c1st cfv cv cdiv cmin caddc cioo c2nd
      c2 cxp wss wrex wral crn cmpt2 wceq cxr wfn cpw clt df-ioo ixxf mp1i cuni
      wf ffn elssuni ctop retop eqeltri uniretop unieqi eqtr4i txunii syl6sseqr
      ctg ad2antrr simplr sseldd xp1st syl simpr rpred rehalfcld resubcld rexrd
      readdcld fnovrn syl3anc xp2nd eqeq2d eqid vex syl6eleqr ralrimiva cvv wbr
      rphalfcld ltsubrpd ltaddrpd w3a wb elioo1 syl2anc mpbir3and jca cabs cima
      eqidd cmnf cpnf mnfle pnfge mnfxr ioossioo mpanl12 ioomax syl6sseq sselda
      cle pnfxr wi adantr wf1o mp2b a1i syl21anc imp cnxmet ex wfun ax-mp f1odm
      cdm funfvima sylancr r19.29 xpeq1 xpeq2 rspc2ev xpex elrnmpt2 sylibr xpss
      sseldi elxp7 sylanbrc ccnv ccom cbl xpss12 expcom ancld imdistanri simpr1
      cre 3anassrs cnre2csqima ccnfld ctopn chmeo cnrehmeo cnfldtopon toponunii
      cim hmeof1o f1of ffvelrnd ffvelrnda sqsscirc2 rpxrd jctil cnmetdval elbl3
      cxmt eqbrtrd biimpar syldan syld f1ocnv f1ofun f1ocnvfv1 eleq1d biimpd ci
      3syld ssrdv cmul mpt2fun hmeoima cnfldtopn elmopn2 simprbi sseq1d rexbidv
      mpan oveq1 rspcva imass2 f1of1 f1imacnv sseq2d syl5ib reximdv sstr reximi
      wf1 mpd eleq2 sseq1 anbi12d rspcev rexlimivw ) EHHUCOZPZIEPZQZIUDUEZNUFZU
      LUGOZUHOZUYAUYCUIOZUJOZIUKUEZUYCUHOZUYGUYCUIOZUJOZUMZFPZIUYKPZUYKEUNZQZQZ
      NRUOZIJUFZPZUYREUNZQZJFUOZUXTUYLNRUPUYONRUOZUYQUXTUYLNRUXTUYBRPZQZUYKABUJ
      UQZVUFAUFZBUFZUMZURZUQZFVUEUYKVUIUSZBVUFUOAVUFUOZUYKVUKPVUEUYFVUFPZUYJVUF
      PZUYKUYKUSZVUMVUEUJUTUTUMZVAZUYDUTPZUYEUTPZVUNVUQUTVBZUJVHVURVUEABUAVCVCU
      JABUAVDVEVUQVVAUJVIVFZVUEUYDVUEUYAUYCVUEISSUMZPZUYASPVUEEVVCIUXREVVCUNZUX
      SVUDUXREUXQVGVVCEUXQVJHHSSHVUFVSUEZVKKVLVMZVVGSVVFVGHVGVNHVVFKVOVPZVVHVQZ
      VRZVTUXRUXSVUDWAWBZISSWCWDZVUEUYBVUEUYBUXTVUDWEZWFWGZWHWIZVUEUYEVUEUYAUYC
      VVLVVNWJWIZUTUTUYDUYEUJWKWLVUEVURUYHUTPZUYIUTPZVUOVVBVUEUYHVUEUYGUYCVUEVV
      DUYGSPVVKISSWMWDZVVNWHWIZVUEUYIVUEUYGUYCVVSVVNWJWIZUTUTUYHUYIUJWKWLVUEUYK
      XLVULVUPUYKUYFVUHUMZUSABUYFUYJVUFVUFVUGUYFUSVUIVWBUYKVUGUYFVUHUUAWNVUHUYJ
      USVWBUYKUYKVUHUYJUYFUUBWNUUCWLABVUFVUFVUIUYKVUJVUJWOVUGVUHAWPBWPUUDUUEUUF
      MWQWRUXTUYMNRUPUYNNRUOZVUCUXTUYMNRVUEIWSWSUMZPUYAUYFPZUYGUYJPZQUYMVUEVVCV
      WDISSUUGVVKUUHVUEVWEVWFVUEVWEUYAUTPZUYDUYAVCWTZUYAUYEVCWTZVUEUYAVVLWIVUEU
      YAUYCVVLVUEUYBVVMXAZXBVUEUYAUYCVVLVWJXCVUEVUSVUTVWEVWGVWHVWIXDXEVVOVVPUYD
      UYEUYAXFXGXHVUEVWFUYGUTPZUYHUYGVCWTZUYGUYIVCWTZVUEUYGVVSWIVUEUYGUYCVVSVWJ
      XBVUEUYGUYCVVSVWJXCVUEVVQVVRVWFVWKVWLVWMXDXEVVTVWAUYHUYIUYGXFXGXHXIIUYFUY
      JUUIUUJWRUXTUYKGUUKZIGUEZUYBXJUHUULZUUMUEZOZXKZUNZVWSEUNZQZNRUOZVWCUXTVWT
      NRUPVXANRUOZVXCUXTVWTNRVUEAUYKVWSVUEVUGUYKPZVUGVWSPZVUEVXEQVUEVUGVVCPZQZV
      XEQVXFVXEVUEVXHVXEVUEVXGVUEVXEVXGVUEUYKVVCVUGVUEUYFSUNUYJSUNUYKVVCUNVUEUY
      FXMXNUJOZSVUEXMUYDYCWTZUYEXNYCWTZUYFVXIUNZVUEVUSVXJVVOUYDXOWDVUEVUTVXKVVP
      UYEXPWDXMUTPZXNUTPZVXJVXKQVXLXQYDXMXNUYDUYEXRXSXGXTYAVUEUYJVXISVUEXMUYHYC
      WTZUYIXNYCWTZUYJVXIUNZVUEVVQVXOVVTUYHXOWDVUEVVRVXPVWAUYIXPWDVXMVXNVXOVXPQ
      VXQXQYDXMXNUYHUYIXRXSXGXTYAUYFSUYJSUUNXGYBUUOUUPUUQVXHVXEVXFVXHVXEVUGGUEZ
      VWRPZVXRVWNUEZVWSPZVXFVXHVXEVXRVWOUHOZUUSUEXJUEUYCVCWTVYBUVHUEXJUEUYCVCWT
      QZVXSVXHVVDVXGUYCRPVXEVYCYEUXRUXSVUDVXGVVDUXRUXSVUDVXGXDZQEVVCIUXRVVEVYDV
      VJYFUXRUXSVUDVXGUURWBUUTZVUEVXGWEZVXHUYBUXTVUDVXGWAZXADCUYCGIVUGLUVAWLVXH
      VYCVXSVXHVYCVYBXJUEZUYBVCWTZVXSVXHVYCVYIVXHVWOTPZVXRTPZVUDVYCVYIYEVXHVVCT
      IGVVCTGVHZVXHGUXQUVBUVCUEZUVDOPZVVCTGYGZVYLDCGHVYMLKVYMWOZUVEZGUXQVYMVVCT
      VVITVYMVYMVYPUVFUVGUVIZVVCTGUVJYHZYIVYEUVKZVUEVVCTVUGGVYLVUEVYSYIUVLZVYGV
      WOVXRUYBUVMYJYKVXHVYIQZVWPTUVRUEPZUYBUTPZQZVYJVYKQZVXRVWOVWPOZUYBVCWTZVXS
      WUBWUDWUCVXHWUDVYIVXHUYBVYGUVNYFYLUVOWUBVYJVYKVXHVYJVYIVYTYFZVXHVYKVYIWUA
      YFZXIWUBWUGVYHUYBVCWUBVYKVYJWUGVYHUSWUJWUIVXRVWOVWPVWPWOUVPXGVXHVYIWEUVSW
      UEWUFQVXSWUHVXRVWPVWOUYBTUVQUVTYJUWAYMUWBVXHVWNYNZVXRVWNYQZPVXSVYAYETVVCV
      WNYGZWUKVYNVYOWUMVYQVYRVVCTGUWCYHZTVVCVWNUWDYOVXHVXRTWULWUAWUMWULTUSWUNTV
      VCVWNYPYOWQVWRVXRVWNYRYSVXHVYAVXFVXHVXTVUGVWSVXHVYOVXGVXTVUGUSVYNVYOVXHVY
      QVYRVFVYFVVCTVUGGUWEXGUWFUWGUWIYKWDYMUWJWRUXTVWRGEXKZUNZNRUOZVXDUXTVWOWUO
      PZUBUFZUYBVWQOZWUOUNZNRUOZUBWUOUPZWUQUXTGYNZIGYQZPZUXSWURWVDUXTDCSSDUFUWH
      CUFUWKOUIOGLUWLYIUXTIVVCWVEUXREVVCIVVJYBVYNVYOWVEVVCUSVYQVYRVVCTGYPYHWQUX
      RUXSWEWVDWVFQUXSWUREIGYRYKYJUXRWVCUXSUXRWUOVYMPZWVCVYNUXRWVGVYQEGUXQVYMUW
      MUWSWVGWUOTUNZWVCWUCWVGWVHWVCQXEYLUBNWUOVWPVYMTVYMVYPUWNUWOYOUWPWDYFWVBWU
      QUBVWOWUOWUSVWOUSZWVAWUPNRWVIWUTVWRWUOWUSVWOUYBVWQUWTUWQUWRUXAXGUXRWUQVXD
      YEUXSUXRWUPVXANRWUPVWSVWNWUOXKZUNUXRVXAVWRWUOVWNUXBUXRWVJEVWSUXRVVCTGUXJZ
      VVEWVJEUSVYNVYOWVKVYQVYRVVCTGUXCYHVVJVVCTEGUXDYSUXEUXFUXGYFUXKVWTVXANRYTX
      GVXBUYNNRUYKVWSEUXHUXIWDUYMUYNNRYTXGUYLUYONRYTXGUYPVUBNRVUAUYOJUYKFUYRUYK
      USUYSUYMUYTUYNUYRUYKIUXLUYRUYKEUXMUXNUXOUXPWD $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Order topology - misc. additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y z A $.  $d x y B $.
    cnvordtrestixx.1 $e |- A C_ RR* $.
    cnvordtrestixx.2 $e |- ( ( x e. A /\ y e. A ) -> ( x [,] y ) C_ A ) $.
    $( The restriction of the 'greater than' order to an interval gives the
       same topology as the subspace topology.  (Contributed by Thierry Arnoux,
       1-Apr-2017.) $)
    cnvordtrestixx $p |- ( ( ordTop ` <_ ) |`t A ) =
      ( ordTop ` ( `' <_ i^i ( A X. A ) ) ) $=
      ( vz cle cordt cfv crest co wceq wtru cxr wcel ax-mp wss cv wa wbr cnvtsr
      ccnv cxp cin crn cdm lern df-rn eqtri ctsr letsr a1i crab wb brcnvg simpr
      adantlr simplr syl2anc anbi12d ancom syl6bb rabbidva sseldi iccval ancoms
      cicc simpl eqsstr3d eqsstrd adantl ordtrest2 trud cps tsrps oveq1i eqtr2i
      ordtcnv ) GUBZCCUCUDHIZVSHIZCJKZGHIZCJKVTWBLMBAFCVSNNGUEVSUFUGGUHUIVSUJOZ
      MGUJOZWDUKGUAPULCNQMDULBRZCOZARZCOZSZWFFRZVSTZWKWHVSTZSZFNUMZCQMWJWOWHWKG
      TZWKWFGTZSZFNUMZCWJWNWRFNWJWKNOZSZWNWQWPSWRXAWLWQWMWPWGWTWLWQUNWIWFWKCNGU
      OUQXAWTWIWMWPUNWJWTUPWGWIWTURWKWHNCGUOUSUTWQWPVAVBVCWJWSWHWFVGKZCWJWHNOWF
      NOXBWSLWJCNWHDWGWIUPVDWJCNWFDWGWIVHVDFWHWFVEUSWIWGXBCQEVFVIVJVKVLVMWAWCCJ
      GVNOZWAWCLWEXCUKGVOPGVRPVPVQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Continuity in topological spaces - misc. additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d a b y .* $.  $d a x y .* $.  $d a b y .+ $.  $d a b C $.  $d a b y F $.
    $d a b J $.  $d a b K $.  $d x y .+ $.  $d x y B $.  $d x y F $.
    mndpluscn.f $e |- F e. ( J Homeo K ) $.
    mndpluscn.p $e |- .+ : ( B X. B ) --> B $.
    mndpluscn.t $e |- .* : ( C X. C ) --> C $.
    mndpluscn.j $e |- J e. ( TopOn ` B ) $.
    mndpluscn.k $e |- K e. ( TopOn ` C ) $.
    mndpluscn.h $e |- ( ( x e. B /\ y e. B ) ->
                           ( F ` ( x .+ y ) ) = ( ( F ` x ) .* ( F ` y ) ) ) $.
    mndpluscn.o $e |- .+ e. ( ( J tX J ) Cn J ) $.
    $( A mapping that is both a homeomorphism and a monoid homomorphism
       preserves the "continuousness" of the operation.  (Contributed by
       Thierry Arnoux, 25-Mar-2017.) $)
    mndpluscn $p   |- .* e. ( ( K tX K ) Cn K ) $=
      ( va vb cfv co cv ccnv cmpt2 ctx ccn cxp wf wfn wceq ffn fnov biimpi mp2b
      wcel wral wf1o chmeo toponunii hmeof1o ax-mp f1ocnvdm mpan anim12i rgen2a
      wa oveq1 fveq2d oveq1d eqeq12d oveq2d rspc2va sylancl f1ocnvfv2 oveqan12d
      fveq2 oveq2 eqtr2d mpt2eq3ia eqtri ctopon a1i cnmpt1st hmeocnvcn cnmpt21f
      wtru mp1i cnmpt2nd cnmpt22f hmeocn trud eqeltri ) GQRDDQUAZFUBZSZRUAZWMSZ
      ETZFSZUCZIIUDTIUETZGQRDDWLWOGTZUCZWSDDUFZDGUGGXCUHZGXBUIZLXCDGUJXDXEQRDDG
      UKULUMQRDDXAWRWLDUNZWODUNZVEZWRWNFSZWPFSZGTZXAXHWNCUNZWPCUNZVEAUAZBUAZETZ
      FSZXNFSZXOFSZGTZUIZBCUOACUOWRXKUIZXFXLXGXMCDFUPZXFXLFHIUQTUNZYCJFHICDCHMU
      RDINURUSUTZCDWLFVAVBYCXGXMYECDWOFVAVBVCYAABCOVDYAYBWNXOETZFSZXIXSGTZUIABW
      NWPCCXNWNUIZXQYGXTYHYIXPYFFXNWNXOEVFVGYIXRXIXSGXNWNFVOVHVIXOWPUIZYGWRYHXK
      YJYFWQFXOWPWNEVPVGYJXSXJXIGXOWPFVOVJVIVKVLXFXGXIWLXJWOGYCXFXIWLUIYECDWLFV
      MVBYCXGXJWOUIYECDWOFVMVBVNVQVRVSWSWTUNWEQRWQFIIHIDDIDVTSUNWENWAZYKWEQRWNW
      PEIIHHHDDYKYKWEQRWLWMIIIHDDYKYKWEQRIIDDYKYKWBYDWMIHUETUNWEJFHIWCWFZWDWEQR
      WOWMIIIHDDYKYKWEQRIIDDYKYKWGYLWDEHHUDTHUETUNWEPWAWHYDFHIUETUNWEJFHIWIWFWD
      WJWK $.
  $}

  ${
    $d x y F $.  $d x y S $.  $d x y T $.
    mhmhmeotmd.m $e |- F e. ( S MndHom T ) $.
    mhmhmeotmd.h $e |- F e. ( ( TopOpen ` S ) Homeo ( TopOpen ` T ) ) $.
    mhmhmeotmd.t $e |- S e. TopMnd $.
    mhmhmeotmd.s $e |- T e. TopSp $.
    $( Deduce a Topological Monoid using mapping that is both a homeomorphism
       and a monoid homomorphism.  (Contributed by Thierry Arnoux,
       21-Jun-2017.) $)
    mhmhmeotmd $p |- T e. TopMnd $=
      ( vx vy ctmd wcel cmnd cplusf cfv ctopn ctx co ax-mp wf eqid ctps mhmrcl2
      ccn cmhm cbs cxp mhmrcl1 mndplusf ctopon tmdtopon istps mpbi cv wa cplusg
      wceq mhmlin mp3an1 plusfval fveq2d mhmf ffvelrni syl2an 3eqtr4d mndpluscn
      tmdcn istmd mpbir3an ) BJKBLKZBUAKZBMNZBONZVLPQVLUCQKCABUDQKZVIDABCUBRZGH
      IAUENZBUENZAMNZCVKAONZVLEALKZVOVOUFVOVQSVMVSDABCUGRVOVQAVOTZVQTZUHRVIVPVP
      UFVPVKSVNVPVKBVPTZVKTZUHRAJKZVRVOUINKFAVRVOVRTZVTUJRVJVLVPUINKGVPVLBWBVLT
      ZUKULHUMZVOKZIUMZVOKZUNZWGWIAUONZQZCNZWGCNZWICNZBUONZQZWGWIVQQZCNWOWPVKQZ
      VMWHWJWNWRUPDVOWLWQABCWGWIVTWLTZWQTZUQURWKWSWMCVOWLVQAWGWIVTXAWAUSUTWHWOV
      PKWPVPKWTWRUPWJVOVPWGCVMVOVPCSDVOVPABCVTWBVARZVBVOVPWICXCVBVPWQVKBWOWPWBX
      BWCUSVCVDWDVQVRVRPQVRUCQKFVQAVRWEWAVFRVEVKBVLWCWFVGVH $.
  $}

  ${
    $d w x C $.  $d w x ph $.  $d x y z C $.
    rmulccn.1 $e |- J = ( topGen ` ran (,) ) $.
    rmulccn.2 $e |- ( ph -> C e. RR ) $.
    $( Multiplication by a real constant is a continuous function (Contributed
       by Thierry Arnoux, 23-May-2017.) $)
    rmulccn $p |- ( ph -> ( x e. RR |-> ( x x. C ) ) e. ( J Cn J ) ) $=
      ( vy vz vw cc cv cmul co cr cfv ccn wcel a1i wceq ax-resscn cmpt cres wss
      ccnfld ctopn crest ctopon eqid cnfldtopon cnmptid recnd cmpt2 ctx cxp wfn
      cnmptc wf ax-mulf ax-mp fnov mpbi mulcn eqeltrri oveq12 cnmpt12 toponunii
      ffn cnrest sylancl crn wb wral wa simpr adantr mulcld ralrimiva fnmpt syl
      fnssres fvres oveq1 fvmpt eqtrd remulcld eqeltrd fnfvrnss syl2anc cnrest2
      recn ovex syl3anc mpbid resmpt cioo tgioo2 eqtri oveq12i eqcomi 3eltr3g
      ctg ) ABJBKZCLMZUAZNUBZUDUEOZNUFMZXGPMZBNXCUAZDDPMZAXEXGXFPMQZXEXHQZAXDXF
      XFPMQNJUCZXKABGHXBCGKZHKZLMZXCXFXFXFXFJJJXFJUGOQZAXFXFUHZUIZRZABXFJXTUJAB
      CXFXFJJXTXTACFUKZUPXTXTGHJJXPULZXFXFUMMXFPMZQALYBYCLJJUNZUOZLYBSYDJLUQYEU
      RYDJLVGUSGHJJLUTVAXFXRVBVCRXNXBXOCLVDVETNXDXFXFJJXFXSVFVHVIAXQXEVJNUCZXMX
      KXLVKXTAXENUOZIKZXEOZNQZINVLYFAXDJUOZXMYGAXCJQZBJVLYKAYLBJAXBJQZVMXBCAYMV
      NACJQYMYAVOVPVQBJXCXDJXDUHZVRVSTJNXDVTVIAYJINAYHNQZVMZYIYHCLMZNYPYOYIYQSA
      YOVNZYOYIYHXDOZYQYHNXDWAYOYHJQYSYQSYHWJBYHXCYQJXDXBYHCLWBYNYHCLWKWCVSWDVS
      YPYHCYRACNQYOFVOWEWFVQINNXEWGWHXMATRNXEXGXFJWIWLWMXMXEXISTBJNXCWNUSXJXHDX
      GDXGPDWOVJXAOXGEXFXRWPWQZYTWRWSWT $.
  $}

  ${
    $d x y $.
    raddcn.1 $e |- J = ( topGen ` ran (,) ) $.
    $( Addition in the real numbers is a continuous function.  (Contributed by
       Thierry Arnoux, 23-May-2017.) $)
    raddcn $p |- ( x e. RR , y e. RR |-> ( x + y ) ) e. ( ( J tX J ) Cn J ) $=
      ( caddc cr cxp ctx co cfv crest ccn wcel wss ax-resscn mp2an ctop cvv crn
      cc cres ccnfld ctopn cv cmpt2 eqid addcn xpss12 cnfldtop toponunii txunii
      cnfldtopon cnrest wceq reex txrest mp4an cioo tgioo2 eqtr2i oveq12i eqtri
      ctg oveq1i eleqtri ctopon wb wfn wf ax-addf ax-mp fnssres fnov mpbi ovres
      mpt2eq3ia rneqi wral readdcl rgen2a rnmpt2ss eqsstri cnrest2 mp3an oveq2i
      ffn 3eltr3i ) EFFGZUAZCCHIZUBUCJZFKIZLIZABFFAUDZBUDZEIZUEZWJCLIWIWJWKLIZM
      ZWIWMMZWIWKWKHIZWHKIZWKLIZWREXAWKLIMWHTTGZNZWIXCMWKWKUFZUGFTNZXGXEOOFTFTU
      HPZWHEXAWKXDWKWKTTWKXFUIZXITWKWKXFULZUJZXKUKUMPXBWJWKLXBWLWLHIZWJWKQMZXMF
      RMZXNXBXLUNXIXIUOUOFFWKWKQQRRUPUQWLCWLCHCURSVCJWLDWKXFUSUTZXOVAVBVDVEWKTV
      FJMWISZFNXGWSWTVGXJXPWQSZFWIWQWIABFFWNWOWIIZUEZWQWIWHVHZWIXSUNEXDVHZXEXTX
      DTEVIYAVJXDTEWFVKXHXDWHEVLPABFFWIVMVNABFFXRWPWNWOFFEVOVPVBZVQWPFMZBFVRAFV
      RXQFNYCABFWNWOVSVTABFFWPFWQWQUFWAVKWBOFWIWJWKTWCWDVNYBWLCWJLXOWEWG $.
  $}

  ${
    $d x y C $.  $d x y F $.  $d x y ph $.
    xrmulc1cn.k $e |- J = ( ordTop ` <_ ) $.
    xrmulc1cn.f $e |- F = ( x e. RR* |-> ( x *e C ) ) $.
    xrmulc1cn.c $e |- ( ph -> C e. RR+ ) $.
    $( The operation multiplying an extended real number by a non-negative
       constant is continuous.  (Contributed by Thierry Arnoux, 5-Jul-2017.) $)
    xrmulc1cn $p |- ( ph -> F e. ( J Cn J ) ) $=
      ( vy cle cfv co wcel cxr wral cxmu wceq wa simpr ralrimiva cordt ccn ctsr
      wiso letsr a1i wf1o cv wbr wb wreu crp adantr rpxrd xmulcld cc0 wne rpred
      rpne0d xreceu syl3anc eqcom adantlr xmulcom eqeq1d syl5bb reubidva mpbird
      cr syl2anc f1ompt sylanbrc simplr ad2antrr xlemul1 cvv ovex sylancl oveq1
      fvmpt2 fvmpt adantl breq12d bitr4d df-isom ordthmeolem oveq12i syl6eleqr
      ledm ) ADJUAKZWJUBLZEEUBLAJUCMZWLNNJJDUDZDWKMWLAUEUFZWNANNDUGZBUHZIUHZJUI
      ZWPDKZWQDKZJUIZUJZINOZBNOWMAWPCPLZNMZBNOWQXDQZBNUKZINOWOAXEBNAWPNMZRZWPCA
      XHSXICACULMZXHHUMUNZUOTAXGINAWQNMZRZXGCWPPLZWQQZBNUKZXMXLCVIMCUPUQXPAXLSX
      MCAXJXLHUMZURXMCXQUSBWQCUTVAXMXFXOBNXFXDWQQXMXHRZXOWQXDVBXRXDXNWQXRXHCNMZ
      XDXNQXMXHSAXHXSXLXKVCWPCVDVJVEVFVGVHTBINNXDDGVKVLAXCBNXIXBINXIXLRZWRXDWQC
      PLZJUIZXAXTXHXLXJWRYBUJAXHXLVMZXIXLSAXJXHXLHVNWPWQCVOVAXTWSXDWTYAJXTXHXDV
      PMWSXDQYCWPCPVQBNXDVPDGVTVRXLWTYAQXIBWQXDYANDWPWQCPVSGWQCPVQWAWBWCWDTTBIN
      NJJDWEVLJJDUCUCNNWIWIWFVAEWJEWJUBFFWGWH $.
  $}

  ${
    $d b e x y B $.  $d b d e x y D $.  $d b d e x y E $.  $d b d e x y F $.
    $d b d e x y J $.  $d b d e x y K $.  $d b d e x y X $.  $d b d e x y Y $.
    fmcncfil.1 $e |- J = ( MetOpen ` D ) $.
    fmcncfil.2 $e |- K = ( MetOpen ` E ) $.
    $( The image of a Cauchy filter by a continuous filter map is a Cauchy
       filter.  (Contributed by Thierry Arnoux, 12-Nov-2017.) $)
    fmcncfil $p |- ( ( ( D e. ( CMet ` X ) /\ E e. ( *Met ` Y )
      /\ F e. ( J Cn K ) ) /\ B e. ( CauFil ` D ) ) ->
      ( ( Y FilMap F ) ` B ) e. ( CauFil ` E ) ) $=
      ( vx vb cfv wcel co wa cv cflim wex wral vy vd cms cxmt ccn w3a ccfil cfm
      ve simpl2 cflf wi wal simpl1 c0 wne cmetcvg n0 sylib sylancom cme cmetmet
      cfil metxmet 3syl cfilfil ctopon mopntopon simpl3 cnflf simplbda syl21anc
      syl wf wceq oveq2 fveq1d eleq2d raleqbidv rspcv sylc df-ral 19.29r pm3.35
      eximi syl2anc clt wbr crp metcn biimpa simpld flfval syl3anc exbidv mpbid
      wrex flimcfil ex exlimdv ) BGUCMNZCHUDMNZDEFUEONZUFZABUGMNZPZXBKQZDMZFAHD
      UHOMZROZNZKSZXICUGMNZXAXBXCXEUJZXFXHDFAUKOZMZNZKSZXLXFXGEAROZNZKSZXTXQULZ
      KUMZXRXDXEXAYAXAXBXCXEUNZXAXEPXSUOUPYABAEGIUQKXSURUSUTXFXQKXSTZYCXFAGVCMZ
      NZXHDFLQZUKOZMZNZKEYHROZTZLYFTZYEXDXEBGUDMNZYGXFXABGVAMNYOYDBGVBBGVDVEZBA
      GVFUTZXFEGVGMNZFHVGMNZXCYNXFYOYRYPBEGIVHVMXFXBYSXNCFHJVHVMZXAXBXCXEVIZYRY
      SPXCGHDVNZYNKLDEFGHVJVKVLYMYELAYFYHAVOZYKXQKYLXSYHAERVPUUCYJXPXHUUCDYIXOY
      HAFUKVPVQVRVSVTWAXQKXSWBUSYAYCPXTYBPZKSXRXTYBKWCUUDXQKXTXQWDWEVMWFXFXQXKK
      XFXPXJXHXFYSYGUUBXPXJVOYTYQXFUUBXGUAQZBOUBQWGWHXHUUEDMCOUIQWGWHULUAGTUBWI
      WQUIWITKGTZXFYOXBXCUUBUUFPZYPXNUUAYOXBPXCUUGKUIUBUABCDEFGHIJWJWKVLWLDFAHG
      WMWNVRWOWPXBXKXMKXBXKXMXHCXIFHJWRWSWTWA $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Topology of the extended non-negative real numbers monoid
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The extended non-negative reals are homeomorphic to the closed unit
     interval.  (Contributed by Thierry Arnoux, 24-Mar-2017.) $)
  xrge0hmph $p |- II ~= ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) ) $=
    ( vx cc0 c1 cicc co cv wceq cpnf cmin cdiv cif cmpt cii cle cordt cfv crest
    chmeo clt eqid wcel chmph wbr wiso iccpnfhmeo simpri hmphi ax-mp ) ABCDEZAF
    ZCGHUJCUJIEJEKLZMNOPBHDEZQEZREUAZMUMUBUCUIULSSUKUDUNAUKUMUKTUMTUEUFUKMUMUGU
    H $.

  ${
    $d x y $.
    xrge0iifhmeo.1 $e |- F = ( x e. ( 0 [,] 1 ) |->
                                       if ( x = 0 , +oo , -u ( log ` x ) ) ) $.
    $( Define a bijection from ` [ 0 , 1 ] ` to ` [ 0 , +oo ] ` .  (Contributed
       by Thierry Arnoux, 29-Mar-2017.) $)
    xrge0iifcnv $p |- ( F : ( 0 [,] 1 ) -1-1-onto-> ( 0 [,] +oo ) /\ `' F =
      ( y e. ( 0 [,] +oo ) |-> if ( y = +oo , 0 , ( exp ` -u y ) ) ) ) $=
      ( cc0 c1 co cpnf wceq wa wcel cxr cle wbr 0xr pnfxr wn clt cr wb cicc cfv
      wf1o ccnv cv cneg ce cif cmpt wtru clog pnfge ax-mp ubicc2 mp3an a1i cico
      icossicc cioc csn wo wi cun uncom rexri 0le1 snunioc eqtr3i eleq2i bitr3i
      1re elun pm2.53 sylbi elsni syl6 con1d imp cioo 0le0 ltpnf iocssioo mp4an
      crp wss ioorp sseqtri sseli relogcld renegcld rexrd w3a mp2an simp3bi 1rp
      elioc1 logled mpbid log1 syl6breq le0neg1d elico1 syl3anbrc sseldi ifclda
      syl adantl 0elunit iocssicc snunico cmnf mnfxr 0re xrleid icossioo ioomax
      mnflt reefcld efgt0 simp2bi le0neg2d efle sylancl ef0 eqeq2 bibi1d iftrue
      simpr eqeq2d syl5ibrcom wnel ubico df-nel mpbir neleq1 bibi2d cc ifbothda
      syl2an recnd mpbiri syl5ibcom iffalse eqeltrd ad2antrr syl5bi syld impbid
      ex wne ltned adantll neneqd eqeq1 notbid simplr 2falsed relogeftb negcon2
      eqcom 3bitr2d an4s anass1rs f1ocnv2d trud ) EFUAGZEHUAGZCUCCUDBUVGBUEZHIZ
      EUVHUFZUGUBZUHZUIIJUJABUVFUVGAUEZEIZHUVMUKUBZUFZUHZUVLCDUVMUVFKZUVQUVGKUJ
      UVRUVNHUVPUVGHUVGKZUVRUVNJELKZHLKZEHMNZUVSOPUVTUWBOEULUMZEHUNUOUPUVRUVNQZ
      JZEHUQGZUVGUVPEHURUWEUVMEFUSGZKZUVPUWFKZUVRUWDUWHUVRUWHUVNUVRUWHQZUVMEUTZ
      KZUVNUVRUWHUWLVAZUWJUWLVBUVRUVMUWGUWKVCZKUWMUWNUVFUVMUWKUWGVCZUWNUVFUWKUW
      GVDUVTFLKZEFMNUWOUVFIOFVKVEZVFEFVGUOVHVIUVMUWGUWKVLVJUWHUWLVMVNUVMEVOVPVQ
      VRZUWHUVPLKZEUVPMNZUVPHRNZUWIUWHUVPUWHUVOUWHUVMUWGWDUVMUWGEHVSGZWDUVTUWAE
      EMNFHRNZUWGUXBWEOPVTFSKUXCVKFWAUMEHEFWBWCWFWGWHZWIZWJZWKUWHUVOEMNUWTUWHUV
      OFUKUBZEMUWHUVMFMNZUVOUXGMNUWHUVMLKZEUVMRNZUXHUVTUWPUWHUXIUXJUXHWLTOUWQEF
      UVMWPWMWNUWHUVMFUXDFWDKUWHWOUPWQWRWSWTUWHUVOUXEXAWRUWHUVPSKUXAUXFUVPWAXFU
      VTUWAUWIUWSUWTUXAWLTOPEHUVPXBWMXCXFZXDXEXGUVHUVGKZUVLUVFKUJUXLUVIEUVKUVFE
      UVFKUXLUVIJXHUPUXLUVIQZJZUWGUVFUVKEFXIUXNUVHUWFKZUVKUWGKZUXLUXMUXOUXLUXOU
      VIUXLUXOQZUVHHUTZKZUVIUXLUXOUXSVAZUXQUXSVBUXLUVHUWFUXRVCZKUXTUYAUVGUVHUVT
      UWAUWBUYAUVGIOPUWCEHXJUOVIUVHUWFUXRVLVJUXOUXSVMVNUVHHVOVPVQVRZUXOUVKLKZEU
      VKRNZUVKFMNZUXPUXOUVKUXOUVJUXOUVHUWFSUVHUWFXKHVSGZSXKLKUWAXKERNZHHMNZUWFU
      YFWEXLPESKZUYGXMEXQUMUWAUYHPHXNUMXKHEHXOWCXPWGWHZWJZXRWKUXOUVJSKZUYDUYKUV
      JXSXFZUXOUVKEUGUBZFMUXOUVJEMNZUVKUYNMNZUXOEUVHMNZUYOUXOUVHLKZUYQUVHHRNZUV
      TUWAUXOUYRUYQUYSWLTOPEHUVHXBWMXTUXOUVHUYJYAWRUXOUYLUYIUYOUYPTUYKXMUVJEYBY
      CWRYDWTUVTUWPUXPUYCUYDUYEWLTOUWQEFUVKWPWMXCXFXDXEXGUVRUXLJZUVMUVLIZUVHUVQ
      IZTZUJUVIUVNVUBTUVMUVKIZVUBTZVUCUYTEUVKEUVLIUVNVUAVUBEUVLUVMYEYFUVKUVLIVU
      DVUAVUBUVKUVLUVMYEYFUYTUVIJZUVNVUBVUFVUBUVNUVIUYTUVIYHUVNUVQHUVHUVNHUVPYG
      YIYJVUFVUBUVQUWFYKZUVNVUFUVHUWFYKZVUBVUGVUFVUHHUWFYKZVUIHUWFKQZUYIUWAVUJX
      MPEHYLWMHUWFYMYNUVIVUHVUITUYTUVHHUWFYOXGUUAUVHUVQUWFYOUUBVUGUVQUWFKZQVUFU
      VNUVQUWFYMVUFUVNVUKUVRUWDVUKVBUXLUVIUVRUWDVUKUWEUVQUVPUWFUWDUVQUVPIUVRUVN
      HUVPUUCXGUXKUUDUUIUUEVQUUFUUGUUHUVNVUDUVITVUDUVHUVPIZTZVUEUYTUXMJZHUVPHUV
      QIUVIVUBVUDHUVQUVHYEYPUVPUVQIVULVUBVUDUVPUVQUVHYEYPVUNUVNJVUDUVIVUNUVNVUD
      QZVUNVUOUVNEUVKIZQVUNEUVKUXLUXMEUVKUUJUVRUXNEUVKUYIUXNXMUPUXNUXOUYDUYBUYM
      XFUUKUULUUMUVNVUDVUPUVMEUVKUUNUUOYJVRUYTUXMUVNUUPUUQUYTUWDUXMVUMUVRUWDUXL
      UXMVUMUWEUWHUXOVUMUXNUWRUYBUWHUXOJZVUDUVKUVMIZUVOUVJIZVULVUDVURTVUQUVMUVK
      UUTUPUWHUVMWDKUYLVUSVURTUXOUXDUYKUVMUVJUURYSUWHUVOYQKUVHYQKVUSVULTUXOUWHU
      VOUXEYTUXOUVHUYJYTUVOUVHUUSYSUVAYSUVBUVCYRYRXGUVDUVE $.

    $d x X $.
    $( The defined function's value in the real.  (Contributed by Thierry
       Arnoux, 1-Apr-2017.) $)
    xrge0iifcv $p |- ( X e. ( 0 (,] 1 ) -> ( F ` X ) = -u ( log ` X ) ) $=
      ( cc0 c1 cioc co wcel cfv wceq cpnf clog cneg cif cicc cxr syl cr wbr clt
      iocssicc sseli cv eqeq1 fveq2 negeqd ifbieq2d pnfxr elexi negex fvmpt cle
      ifex wn w3a wb 0xr 1re elioc2 mp2an simp2bi gt0ne0d neneqd iffalse eqtrd
      ) CEFGHZIZCBJZCEKZLCMJZNZOZVLVHCEFPHZIVIVMKVGVNCEFUBUCACAUDZEKZLVOMJZNZOV
      MVNBVOCKZVPVJVRVLLVOCEUEVSVQVKVOCMUFUGUHDVJLVLLQUIUJVKUKUNULRVHVJUOVMVLKV
      HCEVHCVHCSIZECUATZCFUMTZEQIFSIVHVTWAWBUPUQURUSEFCUTVAVBVCVDVJLVLVERVF $.

    $d w x y z F $.  $d x X $.
    $( The defined bijection from the closed unit interval and the extended
       non-negative reals is an order isomorphism.  (Contributed by Thierry
       Arnoux, 31-Mar-2017.) $)
    xrge0iifiso $p |- F Isom < , `' < ( ( 0 [,] 1 ) , ( 0 [,] +oo ) ) $=
      ( vw vz cc0 c1 co clt cpnf wbr cfv cxr wceq wcel cle 1re cr wb crp wor cv
      cicc ccnv wpo wfo wral wiso wss iccssxr xrltso soss cnvso mpbi sopo ax-mp
      wi mp2 poss wf1o cneg ce cif cmpt xrge0iifcnv simpli f1ofo csn wo cun 0xr
      cioc rexri 0le1 snunioc mp3an eleq2i elun bitr3i wa elunitrn adantr simpr
      elsn 0re elicc2i simp3bi w3a elioc2 mp2an syl3anbrc clog cioo pnfxr ltpnf
      iocssioo mp4an ioorp sseqtri sseli relogcl renegcld brcnvg sylancr mpbird
      0le0 xrge0iifcv breqtrrd ex breq1 fveq2 0elunit iftrue elexi fvmpt syl6eq
      syl breq1d imbi12d syl5ibr sylbi simpll ad2antlr a1i rpred ad2antrr lttrd
      simp2bi relogcld adantl ltnegd logltb syl2an negex brcnv biimpd breqan12d
      jca 3bitr4d sylibrd sylc exp31 jaoi imp rgen2a soisoi ) FGUCHZIUAZFJUCHZI
      UDZUEZUUGUUIBUFZDUBZEUBZIKZUUMBLZUUNBLZUUJKZUQZEUUGUGDUUGUGUUGUUIIUUJBUHU
      UGMUIMIUAZUUHFGUJUKUUGMIULURUUIMUIMUUJUEZUUKFJUJMUUJUAZUVAUUTUVBUKMIUMUNM
      UUJUOUPUUIMUUJUSURUUGUUIBUTZUULUVCBUDEUUIUUNJNFUUNVAVBLVCVDNAEBCVEVFUUGUU
      IBVGUPUUSDEUUGUUMUUGOZUUNUUGOZUUSUVDUUMFVHZOZUUMFGVLHZOZVIZUVEUUSUQZUVDUU
      MUVFUVHVJZOUVJUVLUUGUUMFMOZGMOFGPKUVLUUGNVKGQVMVNFGVOVPVQUUMUVFUVHVRVSUVG
      UVKUVIUVGUUMFNZUVKDFWDUVEUUSUVNFUUNIKZJUUQUUJKZUQUVEUVOUVPUVEUVOVTZUUNUVH
      OZUVPUVQUUNROZUVOUUNGPKZUVRUVEUVSUVOUUNWAZWBUVEUVOWCUVEUVTUVOUVEUVSFUUNPK
      UVTFGUUNWEQWFWGZWBUVMGROZUVRUVSUVOUVTWHSVKQFGUUNWIWJZWKUVRJUUNWLLZVAZUUQU
      UJUVRUUNTOZJUWFUUJKZUVHTUUNUVHFJWMHZTUVMJMOZFFPKGJIKZUVHUWIUIVKWNXFUWCUWK
      QGWOUPFJFGWPWQWRWSZWTZUWGUWHUWFJIKZUWGUWFROZUWNUWGUWEUUNXAXBZUWFWOXQUWGUW
      JUWOUWHUWNSWNUWPJUWFMRIXCXDXEXQABUUNCXGZXHXQXIUVNUUOUVOUURUVPUUMFUUNIXJUV
      NUUPJUUQUUJUVNUUPFBLZJUUMFBXKFUUGOUWRJNXLAFAUBZFNZJUWSWLLVAZVCJUUGBUWTJUX
      AXMCJMWNXNXOUPXPXRXSXTYAUVIUVEUUOUURUVIUVEVTZUUOVTZUVIUVRVTZUUOUURUXCUVIU
      VRUVIUVEUUOYBUXCUVSUVOUVTUVRUVEUVSUVIUUOUWAYCZUXCFUUMUUNFROUXCWEYDUVIUUMR
      OZUVEUUOUVIUUMUVHTUUMUWLWTZYEYFUXEUVIFUUMIKZUVEUUOUVIUXFUXHUUMGPKZUVMUWCU
      VIUXFUXHUXIWHSVKQFGUUMWIWJYHYFUXBUUOWCZYGUVEUVTUVIUUOUWBYCUWDWKYRUXJUXDUU
      OUUMWLLZVAZUWFUUJKZUURUXDUUOUXMUXDUXKUWEIKZUWFUXLIKZUUOUXMUXDUXKUWEUXDUUM
      UVIUUMTOZUVRUXGWBYIUXDUUNUVRUWGUVIUWMYJYIYKUVIUXPUWGUUOUXNSUVRUXGUWMUUMUU
      NYLYMUXMUXOSUXDUXLUWFIUXKYNUWEYNYOYDYSYPUVIUVRUUPUXLUUQUWFUUJABUUMCXGUWQY
      QYTUUAUUBUUCYAUUDUUEDEUUGUUIIUUJBUUFWQ $.

    $d x u $.
    xrge0iifhmeo.k $e |- J = ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) ) $.
    $( Expose a homeomorphism from the closed unit interval and the extended
       non-negative reals.  (Contributed by Thierry Arnoux, 1-Apr-2017.) $)
    xrge0iifhmeo $p |- F e. ( II Homeo J ) $=
      ( cle cc0 co cordt cfv cpnf chmeo cvv wcel wiso cps cxr mp2an mpbi cdm vy
      c1 cicc cxp cin ccnv ctsr letsr tsrps ax-mp elexi inex1 cnvps xrge0iifiso
      cii clt wss wb iccssxr gtiso isores1 isores2 wceq ledm psssdm eqcomi lern
      crn df-rn eqtri ordthmeo mp3an dfii5 crest iccss2 cnvordtrestixx eleqtrri
      cv oveq12i ) BFGUBUCHZVTUDZUEZIJZFUFZGKUCHZWEUDZUEZIJZLHZUOCLHWBMNWGMNVTW
      EWBWGBOZBWINFWAFPFUGNFPNZUHFUIUJZUKULWDWFWDPWKWDPNZWLFUMUJZUKULVTWEWBWDBO
      ZWJVTWEFWDBOZWOVTWEUPUPUFBOZWPABDUNVTQUQZWEQUQZWQWPURGUBUSZGKUSZVTWEBUTRS
      VTWEFWDBVASVTWEWBWDBVBSWBWGBMMVTWEWBTZVTWKWRXBVTVCWLWTVTFQVDVERVFWGTZWEWM
      WSXCWEVCWNXAWEWDQQFVHWDTVGFVIVJVERVFVKVLUOWCCWHLVMCFIJWEVNHWHEAUAWEXAGKAV
      RUAVRVOVPVJVSVQ $.


    $d x Y $.
    $( The defined function from the closed unit interval and the extended
       non-negative reals is also a monoid homomorphism.  (Contributed by
       Thierry Arnoux, 5-Apr-2017.) $)
    xrge0iifhom $p |- ( ( X e. ( 0 [,] 1 ) /\ Y e. ( 0 [,] 1 ) ) ->
      ( F ` ( X x. Y ) ) = ( ( F ` X ) +e ( F ` Y ) ) ) $=
      ( cc0 c1 co wcel wceq cfv cxad cxr wbr cpnf cmnf cr sseldi cicc cioc cmul
      wo csn cun cle 0xr 1re rexri 0le1 snunioc mp3an eleq2i elun bitr3i orim1i
      elsni sylbi wa 0elunit cv clog cneg iftrue pnfxr elexi fvmpt ax-mp oveq2i
      cif wne eqeq1 fveq2 negeqd ifbieq2d ifex a1i wn elunitrn adantr elunitge0
      negex simpr neneqad ne0gt0d elrpd relogcld renegcld rexrd ifclda pnfnemnf
      eqeltrd neeq1 renemnfd ifbothda eqnetrd xaddpnf1 syl5eq cc unitsscn simpl
      syl2anc mul01d fveq2d syl6eq eqtr4d oveq2d 3eqtr4rd oveq1i xrge0iifcv crp
      cioo clt wss ltpnf iocssioo mp4an ioorp sseqtri sseli syl xaddpnf2 rpssre
      0le0 sstri ax-resscn mul02d oveq1d caddc rexadd oveqan12d remulcld rpgt0d
      rpred mulgt0d iocssicc iimulcl 0re recnd elicc2i simp3bi w3a elioc2 mp2an
      wb syl3anbrc relogmuld negdid 3eqtrd jaoian sylan jaodan sylan2 ) EHIUAJZ
      KZDUUOKZEHLZEHIUBJZKZUDZDEUCJZBMZDBMZEBMZNJZLZUUPEHUEZKZUUTUDZUVAUUPEUVHU
      USUFZKUVJUVKUUOEHOKZIOKHIUGPUVKUUOLUHIUIUJUKHIULUMZUNEUVHUUSUOUPUVIUURUUT
      EHURUQUSUUQUURUVGUUTUUQUURUTZUVDHBMZNJZDHUCJZBMZUVFUVCUVNUVPQUVRUVNUVPUVD
      QNJZQUVOQUVDNHUUOKUVOQLVAAHAVBZHLZQUVTVCMZVDZVKZQUUOBUWAQUWCVEFQOVFVGZVHV
      IZVJUVNUVDOKZUVDRVLZUVSQLUUQUWGUURUUQUVDDHLZQDVCMZVDZVKZOADUWDUWLUUOBUVTD
      LZUWAUWIUWCUWKQUVTDHVMUWMUWBUWJUVTDVCVNVOVPFUWIQUWKUWEUWJWCVQVHZUUQUWIQUW
      KOQOKZUUQUWIUTZVFVRUUQUWIVSZUTZUWKUWRUWJUWRDUWRDUUQDSKUWQDVTWAZUWRDUWSUUQ
      HDUGPUWQDWBWAUWRDHUUQUWQWDWEWFWGWHWIZWJWKWMWAUUQUWHUURUUQUVDUWLRUWNUWIQRV
      LZUWKRVLUWLRVLUUQQUWKQUWLRWNUWKUWLRWNUXAUWPWLVRUWRUWKUWTWOWPWQWAUVDWRXCWS
      UVNUVRUVOQUVNUVQHBUVNDUVNUUOWTDXAUUQUURXBTXDXEUWFXFXGUVNUVEUVOUVDNUVNEHBU
      UQUURWDZXEXHUVNUVBUVQBUVNEHDUCUXBXHXEXIUUQUWIDUUSKZUDZUUTUVGUUQDUVHKZUXCU
      DZUXDUUQDUVKKUXFUVKUUODUVMUNDUVHUUSUOUPUXEUWIUXCDHURUQUSUWIUUTUVGUXCUWIUU
      TUTZUVOUVENJZHEUCJZBMZUVFUVCUXGUXHQUXJUXGUXHQUVENJZQUVOQUVENUWFXJUXGUVEOK
      ZUVERVLZUXKQLUXGUUTUXLUWIUUTWDZUUTUVEUUTUVEEVCMZVDZSABEFXKZUUTUXOUUTEUUSX
      LEUUSHQXMJZXLUVLUWOHHUGPIQXNPZUUSUXRXOUHVFYEISKZUXSUIIXPVIHQHIXQXRXSXTZYA
      WHWIWMZWJYBUXGUUTUXMUXNUUTUVEUYBWOYBUVEYCXCWSUXGUXJUVOQUXGUXIHBUXGEUXGUUS
      WTEUUSSWTUUSXLSUYAYDYFYGYFUXNTYHXEUWFXFXGUXGUVDUVOUVENUXGDHBUWIUUTXBZXEYI
      UXGUVBUXIBUXGDHEUCUYCYIXEXIUXCUUTUTZUWKUXPNJZUWKUXPYJJZUVFUVCUYDUWKSKUXPS
      KUYEUYFLUYDUWJUYDDUYDUUSXLDUYAUXCUUTXBZTZWHZWIUYDUXOUYDEUYDUUSXLEUYAUXCUU
      TWDZTZWHZWIUWKUXPYKXCUXCUUTUVDUWKUVEUXPNABDFXKUXQYLUYDUVCUVBVCMZVDZUWJUXO
      YJJZVDUYFUYDUVBUUSKZUVCUYNLUYDUVBSKZHUVBXNPZUVBIUGPZUYPUYDDEUYDDUYHYOZUYD
      EUYKYOZYMUYDDEUYTVUAUYDDUYHYNUYDEUYKYNYPUYDUVBUUOKZUYSUYDUUQUUPVUBUYDUUSU
      UODHIYQZUYGTUYDUUSUUOEVUCUYJTDEYRXCVUBUYQHUVBUGPUYSHIUVBYSUIUUAUUBYBUVLUX
      TUYPUYQUYRUYSUUCUUFUHUIHIUVBUUDUUEUUGABUVBFXKYBUYDUYMUYOUYDDEUYHUYKUUHVOU
      YDUWJUXOUYDUWJUYIYTUYDUXOUYLYTUUIUUJXIUUKUULUUMUUN $.

    $( Condition for the defined function, ` -u ( log `` x ) ` to be a monoid
       homomorphism.  (Contributed by Thierry Arnoux, 20-Jun-2017.) $)
    xrge0iif1 $p |- ( F ` 1 ) = 0 $=
      ( c1 cc0 cicc co wcel cfv wceq 1elunit cv cpnf clog cneg cif wn wne neeq1
      ax-1ne0 mpbiri neneqd iffalse syl fveq2 negeqd log1 negeqi neg0 eqtri a1i
      3eqtrd c0ex fvmpt ax-mp ) FGFHIZJFBKGLMAFANZGLZOUSPKZQZRZGURBUSFLZVCVBFPK
      ZQZGVDUTSVCVBLVDUSGVDUSGTFGTUBUSFGUAUCUDUTOVBUEUFVDVAVEUSFPUGUHVFGLVDVFGQ
      GVEGUIUJUKULUMUNDUOUPUQ $.

    $( The defined function from the closed unit interval and the extended
       non-negative reals is a monoid homomorphism.  (Contributed by Thierry
       Arnoux, 21-Jun-2017.) $)
    xrge0iifmhm $p |- F e. ( ( ( mulGrp ` CCfld ) |`s ( 0 [,] 1 ) )
                                         MndHom ( RR*s |`s ( 0 [,] +oo ) ) ) $=
      ( vy vz ccnfld cfv cc0 c1 cicc co cress wcel cmul wceq ax-mp cc cvv wa wf
      cmgp cxrs cpnf cmhm cmnd cv cxad wral ctmd eqid iistmd tmdmnd ccmn cmnmnd
      w3a xrge0cmn pm3.2i wf1o ccnv cneg ce cmpt xrge0iifcnv simpli xrge0iifhom
      cif rgen2a xrge0iif1 3pm3.2i wss cbs unitsscn cnfldbas ressbas2 xrge0base
      f1of mgpbas cnfldex ovex mgpress mp2an cmulr cnfldmul ressmulr xrge0plusg
      mgpplusg crg c0g cnrng 1elunit cnfld1 rngidss mp3an xrge00 ismhm mpbir2an
      ) BHUCIZJKLMZNMZUDJUELMZNMZUFMOXAUGOZXCUGOZUAWTXBBUBZFUHZGUHZPMBIXGBIXHBI
      UIMQZGWTUJFWTUJZKBIJQZUQXDXEXAUKOXDXAXAULZUMXAUNRXCUOOXEURXCUPRUSXFXJXKWT
      XBBUTZXFXMBVAFXBXGUEQJXGVBVCIVHVDQAFBDVEVFWTXBBVRRXIFGWTABCXGXHDEVGVIABCD
      EVJVKFGWTXBPUIXAXCBJKWTSVLZWTXAVMIQVNWTSXAWSXLSHWSWSULZVOVSVPRVQHWTNMZPXA
      HTOWTTOZXAXPUCIQVTJKLWAZWTHXPWSTTXPULZXOWBWCXQPXPWDIQXRWTHXPPTXSWEWFRWHWG
      HWIOXNKWTOKXAWJIQWKVNWLWTSHKXAXLVOWMWNWOWPWQWR $.

    $d x v $.  $d a b .+ $.  $d u v .+ $.  $d u v F $.
    xrge0pluscn.1 $e |- .+ = ( +e |` ( ( 0 [,] +oo ) X. ( 0 [,] +oo ) ) ) $.
    $( The addition operation of the extended non-negative real numbers monoid
       is continuous.  (Contributed by Thierry Arnoux, 24-Mar-2017.) $)
    xrge0pluscn $p   |- .+ e. ( ( J tX J ) Cn J ) $=
      ( vu vv cc0 co cmul cii wf wcel cc cxad cxr cfv ccnfld va vb vy cicc cpnf
      c1 cxp cres xrge0iifhmeo wfn cv wral wss unitsscn xpss12 mp2an wb ax-mulf
      ffn fnssresb mpbir wa ovres iimulcl eqeltrd rgen2a ffnov mpbir2an iccssxr
      mp2b xaddf fneq1i oveqi ge0xaddcl syl5eqel iitopon cle cordt crest ctopon
      letopon resttopon eqeltri wceq wf1o ccnv cneg cif cmpt xrge0iifcnv simpli
      f1of ax-mp ffvelrni syl2an syl5eq xrge0iifhom eqcomd fveq2d 3eqtr2rd cmgp
      ce cress ctmd ctx ccn eqid iistmd cvv cnfldex ovex mgpress mgptopn cplusf
      dfii4 cnfldbas mgpbas cnfldmul mgpplusg ressplusf eqcomi tmdcn mndpluscn
      ) HIJUFUDKZJUEUDKZLYDYDUGZUHZCBMDACDEFUIYFYDYGNYGYFUJZHUKZIUKZYGKZYDOZIYD
      ULHYDULYHYFPPUGZUMZYDPUMZYOYNUNUNYDPYDPUOUPYMPLNZLYMUJZYHYNUQURYMPLUSZYMY
      FLUTVJVAYLHIYDYIYDOZYJYDOZVBZYKYIYJLKZYDYIYJYDYDLVCZYIYJVDVEVFHIYDYDYDYGV
      GVHYEYEUGZYEBNBUUDUJZUAUKZUBUKZBKZYEOZUBYEULUAYEULUUEQUUDUHZUUDUJZUUKUUDR
      RUGZUMZYERUMZUUNUUMJUEVIZUUOYERYERUOUPUULRQNQUULUJUUKUUMUQVKUULRQUSUULUUD
      QUTVJVAUUDBUUJGVLVAUUIUAUBYEUUFYEOUUGYEOVBZUUHUUFUUGUUJKZYEBUUJUUFUUGGVMU
      UPUUQUUFUUGQKYEUUFUUGYEYEQVCUUFUUGVNVEVOVFUAUBYEYEYEBVGVHVPDVQVRSZYEVSKZY
      EVTSZFUURRVTSOUUNUUSUUTOWAUUOYEUURRWBUPWCUUAYICSZYJCSZBKZUVAUVBQKZUUBCSYK
      CSUUAUVCUVAUVBUUJKZUVDBUUJUVAUVBGVMYSUVAYEOUVBYEOUVEUVDWDYTYDYEYICYDYECWE
      ZYDYECNUVFCWFUCYEUCUKZUEWDJUVGWGXBSWHWIWDAUCCEWJWKYDYECWLWMZWNYDYEYJCUVHW
      NUVAUVBYEYEQVCWOWPACDYIYJEFWQUUAUUBYKCUUAYKUUBUUCWRWSWTTXASZYDXCKZXDOYGMM
      XEKMXFKOUVJUVJXGZXHYGUVJMTYDXCKZMUVJTXIOYDXIOUVJUVLXASWDXJJUFUDXKYDTUVLUV
      IXIXIUVLXGZUVIXGZXLUPUVLUVMXOXMUVJXNSYGYDPLUVIUVJPTUVIUVNXPXQUVKTLUVIUVNX
      RXSYPYQURYRWMUNXTYAYBWMYC $.
  $}

  ${
    $d x y C $.
    xrge0mulc1cn.k $e |- J = ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) ) $.
    xrge0mulc1cn.f $e |- F = ( x e. ( 0 [,] +oo ) |-> ( x *e C ) ) $.
    xrge0mulc1cn.c $e |- ( ph -> C e. ( 0 [,) +oo ) ) $.
    $( The operation multiplying a non-negative real numbers by a non-negative
       constant is continuous.  (Contributed by Thierry Arnoux, 6-Jul-2017.) $)
    xrge0mulc1cn $p |- ( ph -> F e. ( J Cn J ) ) $=
      ( vy cc0 wceq ccn co wcel cpnf cfv cxr a1i cxmu crp cioo ctopon csn cordt
      cicc wf cle crest wss letopon iccssxr resttopon mp2an eqeltri pnfxr pnfge
      wbr 0xr ax-mp lbicc2 mp3an cxp cv wa simpl oveq2d simpr sseldi xmul01 syl
      cmpt eqtrd mpteq2dva fconstmpt 3eqtr4g c0ex fconst2 sylibr cnconst adantl
      syl22anc cres eqid oveq1 cbvmptv xrmulc1cn letopuni cnrest sylancl resmpt
      id eqtr4i eqcomi oveq1i 3eltr3g ioorp ioossicc eqsstr3i ge0xmulcl syl2anc
      crn wb fmptd frn cnrest2 syl3anc mpbid oveq2i syl6eleqr eleq2s cico wo cr
      clt 0re ltpnf elicoelioo sylib mpjaodan ) ACJKZDEELMZNZCJOUAMZNZXTYBAXTEJ
      OUEMZUBPZNZYGJYENZYEJUCZDUFZYBYGXTEUGUDPZYEUHMZYFFYKQUBPNZYEQUIZYLYFNUJJO
      UKZYEYKQULUMUNRZYPYHXTJQNZOQNZJOUGUQZYHURUOYQYSURJUPUSJOUTVARXTDYEYIVBZKY
      JXTBYEBVCZCSMZVKZBYEJVKDYTXTBYEUUBJXTUUAYENZVDZUUBUUAJSMZJUUECJUUASXTUUDV
      EVFUUEUUAQNUUFJKUUEYEQUUAYOXTUUDVGVHUUAVIVJVLVMGBYEJVNVOYEJDVPVQVRJDEEYEY
      EVSWAVTYDYBAYBCTYCCTNZDEYLLMZYAUUGDEYKLMZNZDUUHNZUUGBQUUBVKZYEWBZYLYKLMZD
      UUIUUGUULYKYKLMNYNUUMUUNNUUGICUULYKYKWCBIQUUBIVCZCSMUUAUUOCSWDWEUUGWKWFYO
      YEUULYKYKQWGWHWIUUMUUCDYNUUMUUCKYOBQYEUUBWJUSGWLYLEYKLEYLFWMWNWOUUGYMDXAY
      EUIZYNUUJUUKXBYMUUGUJRUUGYEYEDUFUUPUUGBYEUUBYEDUUGUUDVDZUUDCYENUUBYENUUGU
      UDVGUUQTYECTYCYEWPJOWQWRUUGUUDVEVHUUACWSWTGXCYEYEDXDVJYNUUGYORYEDEYKQXEXF
      XGEYLELFXHXIWPXJVTACJOXKMNZXTYDXLZHYQYRJOXNUQZUURUUSXBURUOJXMNUUTXOJXPUSJ
      OCXQVAXRXS $.
  $}

  $( The extended non-negative real numbers monoid forms a topological space.
     (Contributed by Thierry Arnoux, 19-Jun-2017.) $)
  xrge0tps $p |- ( RR*s |`s ( 0 [,] +oo ) ) e. TopSp $=
    ( cxrs ctps wcel cc0 cpnf cicc co cvv cress xrstps ovex resstps mp2an ) ABC
    DEFGZHCANIGBCJDEFKNAHLM $.

  $( The topology of the extended non-negative real numbers.  (Contributed by
     Thierry Arnoux, 20-Jun-2017.) $)
  xrge0topn $p |- ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) ) =
                                       ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) ) $=
    ( cle cordt cfv cc0 cpnf cicc co crest cxrs cress ctopn eqid xrstopn eqcomi
    resstopn ) ABCZDEFGZHGIQJGZKCQRPIRLMON $.

  $( The topology of the extended non-negative real numbers is Hausdorff.
     (Contributed by Thierry Arnoux, 26-Jul-2017.) $)
  xrge0haus $p |- ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) ) e. Haus $=
    ( cxrs cc0 cpnf cicc cress ctopn cfv cle cordt crest cha xrge0topn wcel cvv
    co xrhaus ovex resthaus mp2an eqeltri ) ABCDOZEOFGHIGZUAJOZKLUBKMUANMUCKMPB
    CDQUAUBNRST $.

  ${
    $d x y $.
    $( The extended non-negative real numbers monoid is a topological monoid.
       (Contributed by Thierry Arnoux, 26-Mar-2017.) (Proof modification is
       discouraged.)  (New usage is discouraged.) $)
    xrge0tmdOLD $p |- ( RR*s |`s ( 0 [,] +oo ) ) e. TopMnd $=
      ( vx vy cxrs cc0 cpnf cicc co wcel cxad cxp cfv ax-mp wceq clog cneg eqid
      cv cif cxr cvv cress ctmd cmnd ctps cres cle cordt crest ctx ccn xrge0cmn
      ccmn cmnmnd xrge0tps cmpt eqeq1 fveq2 negeqd ifbieq2d cbvmptv xrge0pluscn
      c1 cplusf xrsbas xrsadd wf wfn ffn iccssxr ressplusf eqcomi xrge0base cts
      xaddf ovex xrstset resstset topnval istmd mpbir3an ) CDEFGZUAGZUBHWBUCHZW
      BUDHIWAWAJUEZUFUGKZWAUHGZWFUIGWFUJGHWBULHWCUKWBUMLUNAWDBDVBFGZBQZDMZEWHNK
      ZOZRZUOWFBAWGWLAQZDMZEWMNKZOZRWHWMMZWIWNWKWPEWHWMDUPWQWJWOWHWMNUQURUSUTWF
      PWDPVAWDWBWFWBVCKWDWASICWBVDWBPZVESSJZSIVFIWSVGVNWSSIVHLDEVIVJVKWAWEWBVLW
      ATHWEWBVMKMDEFVOWACWBWETWRVPVQLVRVSVT $.
  $}

  ${
    $d x y $.
    $( The extended non-negative real numbers monoid is a topological monoid.
       (Contributed by Thierry Arnoux, 26-Mar-2017.)  (Proof Shortened by
       Thierry Arnoux, 21-Jun-2017.) $)
    xrge0tmd $p |- ( RR*s |`s ( 0 [,] +oo ) ) e. TopMnd $=
      ( vx vy ccnfld cmgp cfv cc0 c1 cicc co cress cpnf cv wceq clog cneg chmeo
      cif cii cvv eqid cxrs cmpt ctopn nfcv eqeq1 fveq2 negeqd cbvmpt xrge0topn
      ifbieq2d xrge0iifmhm xrge0iifhmeo wcel cnfldex ovex mgpress mp2an mgptopn
      dfii4 oveq1i eleqtri iistmd xrge0tps mhmhmeotmd ) CDEZFGHIZJIZUAFKHIJIZAV
      FALZFMZKVINEZOZQZUBZBVNVHUCEZABVFVMBLZFMZKVPNEZOZQZBVMUDAVTUDVIVPMZVJVQVL
      VSKVIVPFUEWAVKVRVIVPNUFUGUJUHZUIUKVNRVOPIVGUCEZVOPIBVNVOWBUIULRWCVOPCVFJI
      ZRVGCSUMVFSUMVGWDDEMUNFGHUOVFCWDVESSWDTZVETUPUQWDWEUSURUTVAVGVGTVBVCVD $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Limits - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    lmlim.j $e |- J e. ( TopOn ` Y ) $.
    lmlim.f $e |- ( ph -> F : NN --> X ) $.
    lmlim.p $e |- ( ph -> P e. X ) $.
    lmlim.t $e |- ( J |`t X ) = ( ( TopOpen ` CCfld ) |`t X ) $.
    lmlim.x $e |- X C_ CC $.
    $( Relate a limit in a given topology to a complex number limit, provided
       that topology agrees with the common topology on ` CC ` on the required
       subset.  (Contributed by Thierry Arnoux, 11-Jul-2017.) $)
    lmlim $p |- ( ph -> ( F ( ~~>t ` J ) P <-> F ~~> P ) ) $=
      ( clm cfv wbr c1 cvv cn cc wcel a1i crest ccnfld ctopn cli eqid nnuz cnex
      co wss ssexd ctop topontopi cz 1z wb fveq2i breqi cnfldtop wf fss sylancl
      lmss lmclimf sylancr bitr3d 3bitrd ) ACBDLMNCBDEUAUHZLMZNZCBUBUCMZEUAUHZL
      MZNZCBUDNZABCDVGOPEQVGUEUFAERPRPSAUGTERUIZAKTUJZDUKSAFDGULTIOUMSZAUNTZHVB
      VIVMUOACBVHVLVGVKLJUPUQTACBVJLMNZVMVNABCVJVKOPEQVKUEUFVPVJUKSAVJVJUEZURTI
      VRHVBAVQQRCUSZVSVNUOUNAQECUSVOWAHKQERCUTVABCVJOQVTUFVCVDVEVF $.
  $}

  ${
    lmlimxrge0.j $e |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) ) $.
    lmlimxrge0.f $e |- ( ph -> F : NN --> X ) $.
    lmlimxrge0.p $e |- ( ph -> P e. X ) $.
    lmlimxrge0.x $e |- X C_ ( 0 [,) +oo ) $.
    $( Relate a limit in the non-negative extended reals to a complex limit,
       provided the considered function is a real function.  (Contributed by
       Thierry Arnoux, 11-Jul-2017.) $)
    lmlimxrge0 $p |- ( ph -> ( F ( ~~>t ` J ) P <-> F ~~> P ) ) $=
      ( cc0 cpnf co cfv crest cxr wcel wss cvv cr cmnf cordt ctopon cress ctopn
      cicc cle cxrs xrge0topn eqtri letopon iccssxr resttopon mp2an ccnfld wceq
      eqeltri fvex cico icossicc sstri ovex restabs mp3an oveq1i cioo clt mnfxr
      wbr pnfxr mnflt ax-mp pnfge icossioo mp4an ioomax sseqtri xrrest2 3eqtr4i
      0re eqid cc ax-resscn lmlim ) ABCDEJKUELZDUFUAMZWDNLZWDUBMZDUGWDUCLUDMWFF
      UHUIZWEOUBMPWDOQWFWGPUJJKUKWDWEOULUMUPGHWFENLZWEENLZDENLUNUDMZENLZWERPEWD
      QWDRPWIWJUOUFUAUQEJKURLZWDIJKUSUTJKUEVAEWDWERRVBVCDWFENWHVDESQWLWJUOEWMSI
      WMTKVELZSTOPKOPZTJVFVHZKKUFVHZWMWNQVGVIJSPWPVSJVJVKWOWQVIKVLVKTKJKVMVNVOV
      PUTZEWKWEWKVTWEVTVQVKVRESWAWRWBUTWC $.
  $}

  ${
    $d j k x z F $.
    $( Implication of convergence for a non-negative series.  This could be
       used to shorten ~ prmreclem6 (Contributed by Thierry Arnoux,
       28-Jul-2017.) $)
    rge0scvg $p |- ( ( F : NN --> ( 0 [,) +oo ) /\ seq 1 ( + , F ) e. dom ~~> )
      -> sup ( ran seq 1 ( + , F ) , RR , < ) e. RR ) $=
      ( vz vx vj vk cn cc0 cpnf wf c1 cli wcel wa cr c0 cv cle wbr cmnf adantr
      cico co caddc cseq cdm crn wss wne wral wrex clt csup nnuz cz 1z a1i cioo
      cxr mnfxr pnfxr 0re mnflt ax-mp pnfge icossioo mp4an ioomax sseqtri mpan2
      fss ffvelrnda serfre frn syl 1nn fdm syl5eleqr ne0i dm0rn0 necon3bii 3syl
      sylib climdm biimpi adantl climrecl simpr simplll ffvelrn syl2anc elrege0
      cfv sseldi simprbi adantlr climserle ralrimiva wceq ralbidv rspcev wb wfn
      breq2 ffn breq1 ralrn rexbidv mpbird suprcl syl3anc ) FGHUAUBZAIZUCAJUDZK
      UELZMZXMUFZNUGZXPOUHZBPZCPZQRZBXPUIZCNUJZXPNUKULNLXLXQXNXLFNXMIZXQXLDAJFU
      MJUNLZXLUOUPXLFNDPZAXLXKNUGFNAIXKSHUQUBZNSURLHURLZSGUKRZHHQRZXKYGUGUSUTGN
      LYIVAGVBVCYHYJUTHVDVCSHGHVEVFVGVHZFXKNAVJVIVKVLZFNXMVMVNTXLXRXNXLYDJXMUEZ
      LZXRYLYDJFYMVOFNXMVPVQYNYMOUHXRYMJVRYMOXPOXMVSVTWBWATXOYCEPZXMWLZXTQRZEFU
      IZCNUJZXOXMKWLZNLYPYTQRZEFUIZYSXOYTEXMJFUMYEXOUOUPXNXMYTKRZXLXNUUCXMWCWDW
      EZXOFNYOXMXLYDXNYLTVKWFXOUUAEFXOYOFLZMZYTDAJYOFUMXOUUEWGXOUUCUUEUUDTUUFYF
      FLZMXLUUGYFAWLZNLZXLXNUUEUUGWHUUFUUGWGXLUUGMZXKNUUHYKFXKYFAWIZWMWJXOUUGGU
      UHQRZUUEXLUUGUULXNUUJUUHXKLZUULUUKUUMUUIUULUUHWKWNVNWOWOWPWQYRUUBCYTNXTYT
      WRYQUUAEFXTYTYPQXCWSWTWJXLYCYSXAXNXLYBYRCNXLYDXMFXBYBYRXAYLFNXMXDYAYQBEFX
      MXSYPXTQXEXFWAXGTXHCBXPXIXJ $.
  $}

  ${
    $d x y A $.  $d y J $.
    pnfneige0.j $e |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) ) $.
    $( A neighborhood of ` +oo ` contains an unbounded interval based at a real
       number.  See ~ pnfnei (Contributed by Thierry Arnoux, 31-Jul-2017.) $)
    pnfneige0 $p |- ( ( A e. J /\ +oo e. A ) ->
      E. x e. RR ( x (,] +oo ) C_ A ) $=
      ( vy wcel cpnf wa cioc co cc0 cin wss cr a1i wceq cxr cfv ctop cvv cv clt
      wrex wbr cif 0re wn simpllr ifclda rexr 0xr iocinif syl3anc ovif syl6reqr
      pnfxr ad2antlr cicc iocssicc sslin mp1i simpr ssin biimpri simpld ssinss1
      3syl sstrd eqsstrd oveq1 sseq1d rspcev syl2anc cordt crest ctopon letopon
      iccssxr resttopon mp2an topontopi ovex cress ctopn xrge0topn eqtri eleq2i
      cxrs biimpi elrestr letop restabs mp3an syl6eleq wb iocpnfordt ssid inss2
      restopnb syl23anc mpbird adantr ltpnf ubioc1 elin sylanbrc pnfnei r19.29a
      cle ax-mp ) BCFZGBFZHZEUAZGIJZBKGIJZLZMZAUAZGIJZBMZANUCZENXMXNNFZHZXRHZXN
      KUBUDZKXNUEZNFYGGIJZBMZYBYEYFKXNNKNFZYEYFHUFOXMYCXRYFUGUHUIYEYHXOXPLZBYCY
      HYKPXMXRYCYKYFXPXOUEZYHYCXNQFKQFZGQFZYKYLPXNUJYMYCUKOYNYCUPOXNKGULUMYFKXN
      GIUNUOUQYEYKXOKGURJZLZBXPYOMZYKYPMYEKGUSZXPYOXOUTVAYEXRXOBMZYPBMYDXRVBXRY
      SXOXPMZYSYTHXRXOBXPVCVDVEXOYOBVFVGVHVIYAYIAYGNXSYGPXTYHBXSYGGIVJVKVLVMXMX
      QXIVNRZFZGXQFZXRENUCXKUUBXLXKUUBXQUUAXPVOJZFZXKXQUUAYOVOJZXPVOJZUUDXKUUFS
      FZXPTFZBUUFFZXQUUGFUUHXKYOUUFUUAQVPRFYOQMUUFYOVPRFVQKGVRYOUUAQVSVTWAOUUIX
      KKGIWBOZXKUUJCUUFBCWHYOWCJWDRUUFDWEWFWGWIBXPUUFSTWJUMUUASFZYQYOTFUUGUUDPW
      KYRKGURWBXPYOUUASTWLWMWNXKUULUUIXPUUAFZXPXPMZXQXPMZUUBUUEWOUULXKWKOUUKUUM
      XKKWPOUUNXKXPWQOUUOXKBXPWROXPXPXQUUATWSWTXAXBXMXLGXPFZUUCXKXLVBUUPXMYMYNK
      GUBUDZUUPUKUPYJUUQUFKXCXJKGXDWMOGBXPXEXFEXQXGVMXH $.
  $}

  ${
    $d a j l x A $.  $d a j k l x F $.  $d a k l x J $.  $d a k l x ph $.
    lmxrge0.j $e |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) ) $.
    lmxrge0.6 $e |- ( ph -> F : NN --> ( 0 [,] +oo ) ) $.
    lmxrge0.7 $e |- ( ( ph /\ k e. NN ) -> ( F ` k ) = A ) $.
    $( Express "sequence ` F ` converges to plus infinity" (i.e. diverges), for
       a sequence of non-negative extended real numbers.  (Contributed by
       Thierry Arnoux, 2-Aug-2017.) $)
    lmxrge0 $p |- ( ph -> ( F ( ~~>t ` J ) +oo <-> A. x e. RR E. j e. NN
      A. k e. ( ZZ>= ` j ) x < A ) ) $=
      ( vl cpnf cfv wbr wcel cn cr cc0 wa cxr va clm cv cuz wral wrex wi clt co
      cicc ctopon cle cordt crest cxrs cress ctopn eqid xrstopn resstopn eqtr4i
      c1 wss letopon iccssxr resttopon mp2an eqeltri a1i nnuz cz 1z lmbrf pnfxr
      0xr pnfge ax-mp ubicc2 mp3an biantrur syl6bbr cioc cin rexr ltpnf syl3anc
      ubioc1 0re jctir elin sylibr ad2antlr ctop letop iocpnfordt inopn elrestr
      ovex wceq inss2 iocssicc sstri sseqin2 mpbi incom eqtr3i 3eltr4i wb eleq2
      cvv adantl biimprd simp-5r rexrd simpr simp-4r eleqtrd simplbi syl elioc1
      w3a mpan2 biimpa simp2d syl2anc ralimdva reximdva raleqdv cbvrexv syl6ibr
      ex fveq2 imim12d rspcimdv imp mpd ralrimdva simpllr simplr sseldd simplll
      pnfneige0 r19.29r simp-4l uznnssnn jca ffvelrnda eqeltrrd sseldi ad2antrr
      biimpar syl13anc adantlr syl21anc syl5bi expimpd rexlimdva syl12anc exp31
      syl5 impbid bitrd ) AFLGUBMNZLUAUCZOZCUVDOZEKUCZUDMZUEZKPUFZUGZUAGUEZBUCZ
      CUHNZEDUCZUDMZUEZDPUFZBQUEZAUVCLRLUJUIZOZUVLSUVLAUACLKEFGVBUVTPGUVTUKMZOA
      GULUMMZUVTUNUIZUWBGUOUVTUPUIZUQMUWDHUVTUWEUWCUOUWEURUSUTVAZUWCTUKMOUVTTVC
      UWDUWBOVDRLVEZUVTUWCTVFVGVHVIVJVBVKOAVLVIIJVMUWAUVLRTOZLTOZRLULNZUWAVOVNU
      WHUWJVORVPVQRLVRVSVTWAAUVLUVSAUVLUVRBQAUVMQOZSZUVLUVRUWLUVLSLUVMLWBUIZRLW
      BUIZWCZOZUVRUWKUWPAUVLUWKLUWMOZLUWNOZSUWPUWKUWQUWRUWKUVMTOZUWIUVMLUHNUWQU
      VMWDUWIUWKVNVIUVMWEUVMLWGWFUWHUWIRLUHNZUWRVOVNRQOUWTWHRWEVQRLWGVSWILUWMUW
      NWJWKWLUWLUVLUWPUVRUGZUWLUVKUXAUAUWOGUWOGOUWLUWOUVTWCZUWDUWOGUWCWMOZUVTXJ
      OUWOUWCOZUXBUWDOWNRLUJWRUXCUWMUWCOUWNUWCOUXDWNUVMWORWOUWMUWNUWCWPVSUWOUVT
      UWCWMXJWQVSUVTUWOWCZUWOUXBUWOUVTVCUXEUWOWSUWOUWNUVTUWMUWNWTRLXAXBUWOUVTXC
      XDUVTUWOXEXFUWFXGVIUWLUVDUWOWSZSZUWPUVEUVJUVRUXGUVEUWPUXFUVEUWPXHUWLUVDUW
      OLXIXKXLUXGUVJUVNEUVHUEZKPUFZUVRUXGUVIUXHKPUXGUVGPOZSZUVFUVNEUVHUXKEUCZUV
      HOZSZUVFUVNUXNUVFSZUWSCUWMOZUVNUXOUVMAUWKUXFUXJUXMUVFXMXNUXOCUWOOZUXPUXOC
      UVDUWOUXNUVFXOUWLUXFUXJUXMUVFXPXQUXQUXPCUWNOCUWMUWNWJXRXSUWSUXPSCTOZUVNCL
      ULNZUWSUXPUXRUVNUXSYAZUWSUWIUXPUXTXHVNUVMLCXTYBZYCYDYEYKYFYGUVQUXHDKPUVOU
      VGWSUVNEUVPUVHUVOUVGUDYLYHYIZYJYMYNYOYPYKYQAUVSUVKUAGAUVDGOZSZUVSUVEUVJUY
      DUVSSZUVESZAUWMUVDVCZBQUFZUVSUVJAUYCUVSUVEUUAUYFUYCUVEUYHAUYCUVSUVEYRUYEU
      VEXOBUVDGHUUBYEUYDUVSUVEYSAUYHUVSSZUVJUYIUYGUVRSZBQUFAUVJUYGUVRBQUUCAUYJU
      VJBQUWLUYGUVRUVJUVRUXIUWLUYGSZUVJUYBUYKUXHUVIKPUYKUXJSZUVNUVFEUVHUYLUXMSZ
      AUXLPOZSZUWKUYGUVNUVFUGUYMAUYNAUWKUYGUXJUXMUUDUYMUVHPUXLUXJUVHPVCUYKUXMUV
      GUUEWLUYLUXMXOYTUUFAUWKUYGUXJUXMXPUWLUYGUXJUXMYRUYOUWKSZUYGSZUVNUVFUYQUVN
      SUWMUVDCUYPUYGUVNYSUYPUVNUXPUYGUYPUVNSZUWSUXRUVNUXSUXPUYRUVMUYOUWKUVNYSXN
      UYOUXRUWKUVNUYOUVTTCUWGUYOUXLFMCUVTJAPUVTUXLFIUUGUUHUUIUUJZUYPUVNXOUYRUXR
      UXSUYSCVPXSUWSUXPUXTUYAUUKUULUUMYTYKUUNYFYGUUOUUPUUQUUTYOUURUUSYQUVAUVB
      $.
  $}

  ${
    $d j k l x F $.  $d j k l x ph $.
    lmdvg.1 $e |- ( ph -> F : NN --> ( 0 [,) +oo ) ) $.
    lmdvg.2 $e |- ( ( ph /\ k e. NN ) -> ( F ` k ) <_ ( F ` ( k + 1 ) ) ) $.
    lmdvg.3 $e |- ( ph -> -. F e. dom ~~> ) $.
    $( If a monotonic sequence of real numbers diverges, it is unbounded.
       (Contributed by Thierry Arnoux, 4-Aug-2017.) $)
    lmdvg $p |- ( ph
               -> A. x e. RR E. j e. NN A. k e. ( ZZ>= ` j ) x < ( F ` k ) ) $=
      ( vl cfv wbr wral cn cr wcel wa cle c1 cpnf co cv clt cuz wrex wn cli cdm
      crn csup nnuz cz 1z a1i wf cc0 cico wss cmnf cioo mnfxr pnfxr mnflt ax-mp
      cxr 0re pnfge mp4an ioomax sseqtri fss sylancl adantr caddc ralrimiva weq
      icossioo fveq2 oveq1 fveq2d breq12d cbvralv sylib r19.21bi adantlr breq1d
      simpr rexbii climsup cvv nnex fex ltso supex breldmg syl3anc syldan mtand
      ralnex sylibr simplr ffvelrnda ltnled rexbidva ralbidva ad2antrr uznnssnn
      rexnal syl6bb mpbird ad3antrrr ad3antlr sseldd simp-4l simpllr cfz fzssnn
      ffvelrnd cmin simplll syl2anc monoord syl21anc ltletrd ex reximdva mpd )
      ABUAZDUAZEJZUBKZDCUAZUCJZLZCMUDZBNAYGNOZPZYGYKEJZUBKZCMUDZYNAYSBNAYSBNLYQ
      YGQKZCMLZUEZBNLZAUUABNUDZUEUUCAUUDEUFUGOZHAUUDEEUHZNUBUIZUFKZUUEAUUDPZBIE
      RMUJRUKOUUIULUMAMNEUNZUUDAMUOSUPTZEUNZUUKNUQUUJFUUKURSUSTZNURVDOSVDOZURUO
      UBKZSSQKZUUKUUMUQUTVAUONOUUOVEUOVBVCUUNUUPVASVFVCURSUOSVPVGVHVIMUUKNEVJVK
      ZVLAIUAZMOZUUREJZUURRVMTZEJZQKZUUDAUVCIMAYIYHRVMTZEJZQKZDMLUVCIMLAUVFDMGV
      NUVFUVCDIMDIVOZYIUUTUVEUVBQYHUUREVQUVGUVDUVAEYHUURRVMVRVSVTWAWBWCZWDUUIUU
      DUUTYGQKZIMLZBNUDAUUDWFUUAUVJBNYTUVICIMCIVOYQUUTYGQYKUUREVQWEWAWGWBWHAUUH
      PZEWIOZUUGWIOZUUHUUEAUVLUUHAUULMWIOUVLFWJMUUKWIEWKVKVLUVMUVKNUUFUBWLWMUMA
      UUHWFEUUGWIWIUFWNWOWPWQUUABNWRWSAYSUUBBNYPYSYTUEZCMUDUUBYPYRUVNCMYPYKMOZP
      ZYGYQAYOUVOWTZYPMNYKEAUUJYOUUQVLZXAZXBXCYTCMXGXHXDXIWCYPYRYMCMUVPYRYMUVPY
      RPZYJDYLUVTYHYLOZPZYGYQYIUVPYOYRUWAUVQXEUVPYQNOYRUWAUVSXEUWBMNYHEYPUUJUVO
      YRUWAUVRXJUWBYLMYHUVOYLMUQYPYRUWAYKXFXKUVTUWAWFZXLXQUVPYRUWAWTUWBAUVOUWAY
      QYIQKAYOUVOYRUWAXMYPUVOYRUWAXNUWCAUVOPZUWAPZIEYKYHUWDUWAWFUWEUURYKYHXOTZO
      ZPZMNUUREAUUJUVOUWAUWGUUQXJUWHUWFMUURUVOUWFMUQAUWAUWGYKYHXPXKUWEUWGWFXLXQ
      UWEUURYKYHRXRTZXOTZOZPZAUUSUVCAUVOUWAUWKXSUWLUWJMUURUVOUWJMUQAUWAUWKYKUWI
      XPXKUWEUWKWFXLUVHXTYAYBYCVNYDYEYFVN $.
  $}

  ${
    $d j k x F $.  $d k x J $.  $d j k x ph $.
    lmdvglim.j $e |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) ) $.
    lmdvglim.1 $e |- ( ph -> F : NN --> ( 0 [,) +oo ) ) $.
    lmdvglim.2 $e |- ( ( ph /\ k e. NN ) -> ( F ` k ) <_ ( F ` ( k + 1 ) ) ) $.
    lmdvglim.3 $e |- ( ph -> -. F e. dom ~~> ) $.
    $( If a monotonic real number sequence ` F ` diverges, it converges in the
       extended real numbers and its limit is plus infinity.  (Contributed by
       Thierry Arnoux, 3-Aug-2017.) $)
    lmdvglim $p |- ( ph -> F ( ~~>t ` J ) +oo ) $=
      ( vx vj cpnf clm cfv wbr cv wral cn cc0 co wf clt wrex cr lmdvg cico cicc
      cuz wss icossicc fss sylancl wcel wa eqidd lmxrge0 mpbird ) ACKDLMNIOBOZC
      MZUANBJOUGMPJQUBIUCPAIJBCFGHUDAIURJBCDEAQRKUESZCTUSRKUFSZUHQUTCTFRKUIQUSU
      TCUJUKAUQQULUMURUNUOUP $.
  $}
