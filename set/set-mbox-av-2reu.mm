$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Double restricted existential uniqueness
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Restricted quantification (extension)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    r19.32.1 $e |- F/ x ph $.
    $( Theorem 19.32 of [Margaris] p. 90 with restricted quantifiers, analogous
       to ~ r19.32v .  (Contributed by Alexander van der Vekens,
       29-Jun-2017.) $)
    r19.32 $p |- ( A. x e. A ( ph \/ ps ) <-> ( ph \/ A. x e. A ps ) ) $=
      ( wn wi wral wo nfn r19.21 df-or ralbii 3bitr4i ) AFZBGZCDHOBCDHZGABIZCDH
      AQIOBCDACEJKRPCDABLMAQLN $.
  $}

  ${
    $d x y A $.  $d y ph $.
    $( An equivalent expression for restricted existence, analogous to ~ exsb .
       (Contributed by Alexander van der Vekens, 1-Jul-2017.) $)
    rexsb $p |- ( E. x e. A ph <-> E. y e. A A. x ( x = y -> ph ) ) $=
      ( weq wi wal nfv nfa1 ax12v sp com12 impbid cbvrexw ) ABCEZAFZBGZBCDACHPB
      IOAQABCJQOAPBKLMN $.

    $( An equivalent expression for restricted existence, analogous to ~ exsb .
       (Contributed by Alexander van der Vekens, 1-Jul-2017.) $)
    rexrsb $p |- ( E. x e. A ph <-> E. y e. A A. x e. A ( x = y -> ph ) ) $=
      ( wrex weq wi wal wral rexsb cv wcel alral df-ral wa 19.27v pm2.04 eleq1w
      biimprd imim1d a2i 3syl alimi sylbir ex sylbi com12 impbid2 rexbiia bitri
      imp ) ABDEBCFZAGZBHZCDEUMBDIZCDEABCDJUNUOCDCKDLZUNUOUMBDMUOUPUNUOBKDLZUMG
      ZBHZUPUNGUMBDNUSUPUNUSUPOURUPOZBHUNURUPBPUTUMBURUPUMURULUQAGZGULUPAGZGUPU
      MGUQULAQULVAVBULUPUQAULUQUPBCDRSTUAULUPAQUBUKUCUDUEUFUGUHUIUJ $.
  $}

  ${
    $d w x y z B $.  $d w x z A $.  $d z w ph $.
    $( An equivalent expression for double restricted existence, analogous to
       ~ rexsb .  (Contributed by Alexander van der Vekens, 1-Jul-2017.) $)
    2rexsb $p |- ( E. x e. A E. y e. B ph <-> E. z e. A E. w e. B
                   A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wrex weq wi wal wa rexsb rexbii rexcom bitri impexp albii 19.21v bitr2i
      ) ACGHZBFHZCEIZAJZCKZBFHZEGHZBDIZUCLAJZCKZBKZEGHDFHZUBUEEGHZBFHUGUAUMBFAC
      EGMNUEBEFGOPUGUKDFHZEGHULUFUNEGUFUHUEJZBKZDFHUNUEBDFMUPUKDFUOUJBUJUHUDJZC
      KUOUIUQCUHUCAQRUHUDCSTRNPNUKEDGFOPP $.

    $( An equivalent expression for double restricted existence, analogous to
       ~ 2exsb .  (Contributed by Alexander van der Vekens, 1-Jul-2017.) $)
    2rexrsb $p |- ( E. x e. A E. y e. B ph <-> E. z e. A E. w e. B
                   A. x e. A A. y e. B ( ( x = z /\ y = w ) -> ph ) ) $=
      ( wrex wi wral wa rexrsb rexbii rexcom bitri impexp ralbii r19.21v bitr2i
      weq ) ACGHZBFHZCETZAIZCGJZBFHZEGHZBDTZUCKAIZCGJZBFJZEGHDFHZUBUEEGHZBFHUGU
      AUMBFACEGLMUEBEFGNOUGUKDFHZEGHULUFUNEGUFUHUEIZBFJZDFHUNUEBDFLUPUKDFUOUJBF
      UJUHUDIZCGJUOUIUQCGUHUCAPQUHUDCGRSQMOMUKEDGFNOO $.
  $}

  ${
    $d x z A $.  $d x y B $.  $d z y B $.  $d w y B $.
    cbvral2.1 $e |- F/ z ph $.
    cbvral2.2 $e |- F/ x ch $.
    cbvral2.3 $e |- F/ w ch $.
    cbvral2.4 $e |- F/ y ps $.
    cbvral2.5 $e |- ( x = z -> ( ph <-> ch ) ) $.
    cbvral2.6 $e |- ( y = w -> ( ch <-> ps ) ) $.
    $( Change bound variables of double restricted universal quantification,
       using implicit substitution, analogous to ~ cbvral2v .  (Contributed by
       Alexander van der Vekens, 2-Jul-2017.) $)
    cbvral2 $p |- ( A. x e. A A. y e. B ph <-> A. z e. A A. w e. B ps ) $=
      ( wral nfcv nfral weq cbvralw ralbidv ralbii bitri ) AEIPZDHPCEIPZFHPBGIP
      ZFHPUDUEDFHAFEIFIQJRCDEIDIQKRDFSACEINUATUEUFFHCBEGILMOTUBUC $.

    $( Change bound variables of double restricted universal quantification,
       using implicit substitution, analogous to ~ cbvrex2v .  (Contributed by
       Alexander van der Vekens, 2-Jul-2017.) $)
    cbvrex2 $p |- ( E. x e. A E. y e. B ph <-> E. z e. A E. w e. B ps ) $=
      ( wrex nfcv nfrexw weq cbvrexw rexbidv rexbii bitri ) AEIPZDHPCEIPZFHPBGI
      PZFHPUDUEDFHAFEIFIQJRCDEIDIQKRDFSACEINUATUEUFFHCBEGILMOTUBUC $.
  $}

  $( Example for a theorem about a restricted universal quantification in which
     the restricting class depends on (actually is) the bound variable:  All
     sets containing themselves contain the universal class.  (Contributed by
     AV, 24-Jun-2023.) $)
  ralndv1 $p |- A. x e. x _V e. x $=
    ( cvv cv wcel wel elirrv pm2.21i rgen ) BACZDZAIAAEJAFGH $.

  $( Second example for a theorem about a restricted universal quantification
     in which the restricting class depends on the bound variable: all subsets
     of a set are sets.  (Contributed by AV, 24-Jun-2023.) $)
  ralndv2 $p |- A. x e. ~P x x e. _V $=
    ( cv cvv wcel cpw vex rgenw ) ABZCDAHEAFG $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Restricted uniqueness and "at most one" quantification
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d B x y $.  $d C x y $.  $d F x y $.  $d ph x y $.  $d ps y $.  $d ps z $.
    $d th x $.  $d x z $.
    reuf1odnf.f $e |- ( ph -> F : C -1-1-onto-> B ) $.
    reuf1odnf.x $e |- ( ( ph /\ x = ( F ` y ) ) -> ( ps <-> ch ) ) $.
    reuf1odnf.z $e |- ( x = z -> ( ps <-> th ) ) $.
    reuf1odnf.n $e |- F/ x ch $.
    $( There is exactly one element in each of two isomorphic sets.  Variant of
       ~ reuf1od with no distinct variable condition for ` ch ` .  (Contributed
       by AV, 19-Mar-2023.) $)
    reuf1odnf $p |- ( ph -> ( E! x e. B ps <-> E! y e. C ch ) ) $=
      ( wreu cv wsbc wceq wa wb cfv wf1o f1of syl ffvelcdmda wcel f1ofveu eqcom
      wf reubii sylibr sylan sbceq1a adantl cbvsbcvw bitrdi reuxfr1d a1i bicomd
      reubidv cvv fvexd nfv wnf sbciedf 3bitrd ) ABEHODGFPZJUAZQZFIOBEVHQZFIOCF
      IOABVIEFVHHIAIHVGJAIHJUBZIHJUIKIHJUCUDUEAVKEPZHUFZVLVHRZFIOZKVKVMSVHVLRZF
      IOVOFIHVLJUGVNVPFIVLVHUHUJUKULAVNSBVJVIVNBVJTABEVHUMUNBDEGVHMUOZUPUQAVIVJ
      FIAVJVIVJVITAVQURUSUTAVJCFIABCEVHVAAVGJVBLAEVCCEVDANURVEUTVF $.
  $}

  ${
    $d B x y $.  $d C x y $.  $d F x y $.  $d ph x y $.  $d ps y $.  $d ch x $.
    reuf1od.f $e |- ( ph -> F : C -1-1-onto-> B ) $.
    reuf1od.x $e |- ( ( ph /\ x = ( F ` y ) ) -> ( ps <-> ch ) ) $.
    $( There is exactly one element in each of two isomorphic sets.
       (Contributed by AV, 19-Mar-2023.) $)
    reuf1od $p |- ( ph -> ( E! x e. B ps <-> E! y e. C ch ) ) $=
      ( cv cfv wf1o wf f1of syl ffvelcdmda wcel wceq wreu f1ofveu reubii sylibr
      wa eqcom sylan reuxfr1d ) ABCDEEKZHLZFGAGFUHHAGFHMZGFHNIGFHOPQAUJDKZFRZUK
      UISZEGTZIUJULUDUIUKSZEGTUNEGFUKHUAUMUOEGUKUIUEUBUCUFJUG $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d V x y $.
    $( There is a set which is equal to one of two other sets iff the other
       sets are equal.  (Contributed by AV, 24-Jan-2023.) $)
    euoreqb $p |- ( ( A e. V /\ B e. V ) -> ( E! x e. V ( x = A \/ x = B )
                                              <-> A = B ) ) $=
      ( vy wcel wa cv wceq wo wi eqeq1 orbi12d eqeq2 imbi12d rspcv wn com12 ex
      wreu weq wral wrex reu8 simprlr ioran eqid pm2.24i simplbiim eqtr2 ancoms
      syl a1d expimpd ja syld simprll adantr sylbi jaoi impd rexlimdva biimtrid
      reueq bilani wb adantl orbi1d oridm bitrdi reubidv mpbird impbid ) BDFZCD
      FZGZAHZBIZVQCIZJZADTZBCIZWAVTEHZBIZWCCIZJZAEUAZKZEDUBZGZADUCVPWBVTWFAEDWG
      VRWDVSWEVQWCBLVQWCCLMUDVPWJWBADVPVQDFZGZVTWIWBVTWLWIWBKZVRWLWMKVSVRWLWMVR
      WLGZWICBIZCCIZJZVSKZWBWNVOWIWRKVRVNVOWKUEWHWRECDWEWFWQWGVSWEWDWOWEWPWCCBL
      WCCCLMWCCVQNOPULWRWNWBWQVSWNWBKZWQQWOQWPQWSWOWPUFWPWSCUGUHUIVSVRWLWBVSVRG
      WBWLVRVSWBVQBCUJZUKUMUNUORUPSVSWLWMVSWLGZWIBBIZWBJZVRKZWBXAVNWIXDKVSVNVOW
      KUQWHXDEBDWDWFXCWGVRWDWDXBWEWBWCBBLWCBCLMWCBVQNOPULXDXAWBXCVRXAWBKZXCQXBQ
      ZWBQZGXEXBWBUFXFXEXGXBXEBUGUHURUSVRVSWLWBVRVSGWBWLWTUMUNUORUPSUTRVAVBVCVP
      WBWAVPWBGZWAVSADTZVPXIWBVOXIVNADCVDVEURXHVTVSADXHVTVSVSJVSXHVRVSVSWBVRVSV
      FVPBCVQNVGVHVSVIVJVKVLSVM $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Analogs to Existential uniqueness (double quantification)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y A $.  $d x y B $.
    $( Double restricted existential uniqueness, analogous to ~ 2eu3 .
       (Contributed by Alexander van der Vekens, 29-Jun-2017.) $)
    2reu3 $p |- ( A. x e. A A. y e. B ( E* x e. A ph \/ E* y e. B ph ) ->
                ( ( E! x e. A E! y e. B ph /\ E! y e. B E! x e. A ph )
                <-> ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) ) ) $=
      ( wrmo wo wral wreu wa wrex orcom ralbii nfrmo1 r19.32 bitri 2reu1 biimpd
      wb 2rexreu nfcv nfralw ancom imbitrdi adantld adantrd jaoi ancoms impbid1
      wi jca sylbi ) ABDFZACEFZGZCEHZBDHZUMCEHZUNBDHZGZACEIBDIZABDICEIZJZACEKBD
      IZABDKCEIZJZSUQURUNGZBDHUTUPVGBDUPUNURGZVGUPUNUMGZCEHVHUOVICEUMUNLMUNUMCE
      ACENOPUNURLPMURUNBDUMBCEBEUAABDNUBOPUTVCVFURVCVFUJUSURVBVFVAURVBVEVDJZVFU
      RVBVJACBEDQRVEVDUCUDUEUSVAVFVBUSVAVFABCDEQRUFUGVFVAVBABCDETVEVDVBACBEDTUH
      UKUIUL $.
  $}

  ${
    $d x A $.  $d x y B $.
    $( Two equivalent expressions for double restricted existential uniqueness,
       analogous to ~ 2eu7 .  (Contributed by Alexander van der Vekens,
       2-Jul-2017.) $)
    2reu7 $p |- ( ( E! x e. A E. y e. B ph /\ E! y e. B E. x e. A ph ) <->
                  E! x e. A E! y e. B ( E. x e. A ph /\ E. y e. B ph ) ) $=
      ( wrex wreu wa nfcv nfre1 nfreuw reuan ancom reubii 3bitri 3bitr4ri ) ABD
      FZCEGZACEFZHZBDGRSBDGZHQSHZCEGZBDGUARHRSBDQBCEBEIABDJKLUCTBDUCSQHZCEGSRHT
      UBUDCEQSMNSQCEACEJLSRMONUARMP $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Two equivalent expressions for double restricted existential uniqueness,
       analogous to ~ 2eu8 .  Curiously, we can put ` E! ` on either of the
       internal conjuncts but not both.  We can also commute
       ` E! x e. A E! y e. B ` using ~ 2reu7 .  (Contributed by Alexander van
       der Vekens, 2-Jul-2017.) $)
    2reu8 $p |- ( E! x e. A E! y e. B ( E. x e. A ph /\ E. y e. B ph ) <->
                  E! x e. A E! y e. B ( E! x e. A ph /\ E. y e. B ph ) ) $=
      ( wrex wreu wa 2reu2 pm5.32i nfcv nfreu1 nfreuw reuan ancom reubii 3bitri
      nfre1 3bitr4ri 2reu7 3bitr3ri ) ACEFZBDGZABDGZCEGZHZUCABDFZCEGZHUDUBHZCEG
      ZBDGZUGUBHCEGBDGUCUEUHACBEDIJUEUBHZBDGUEUCHUKUFUEUBBDUDBCEBEKABDLMNUJULBD
      UJUBUDHZCEGUBUEHULUIUMCEUDUBOPUBUDCEACERNUBUEOQPUCUEOSABCDETUA $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Additional theorems for double restricted existential uniqueness
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A a b u v w x y $.  $d B a b u v w x y $.  $d ph a b u v w $.
    $d ch a b u v y $.  $d ta a b u x $.  $d th a b u x $.  $d et u w y $.
    $d ps u w x y $.  $d ze x $.
    2reu8i.x $e |- ( x = v -> ( ph <-> ta ) ) $.
    2reu8i.v $e |- ( x = v -> ( ch <-> th ) ) $.
    2reu8i.w $e |- ( y = w -> ( ph <-> ch ) ) $.
    2reu8i.b $e |- ( y = b -> ( ph <-> et ) ) $.
    2reu8i.a $e |- ( x = a -> ( ch <-> ze ) ) $.
    2reu8i.1 $e |- ( ( ( ch -> y = w ) /\ ze ) -> y = w ) $.
    2reu8i.2 $e |- ( ( x = a /\ y = b ) -> ( ph <-> ps ) ) $.
    $( Implication of a double restricted existential uniqueness in terms of
       restricted existential quantification and restricted universal
       quantification, see also ~ 2reu8 .  The involved wffs depend on the
       setvar variables as follows: ph(x,y), ta(v,y), ch(x,w), th(v,w),
       et(x,b), ps(a,b), ze(a,w).  (Contributed by AV, 1-Apr-2023.) $)
    2reu8i $p |- ( E! x e. A E! y e. B ph -> E. x e. A E. y e. B
                                             ( ph /\ A. a e. A A. b e. B
                                  ( et -> ( b = y /\ ( ps -> a = x ) ) ) ) ) $=
      ( vu wreu weq wi wral wa wrex reubii imbi1d ralbidv anbi12d rexbidv bitri
      reu8 wsb cv wcel nfv nfs1v nfcv nfim nfan sbequ12 equequ1 imbi12d cbvrexw
      nfralw imbi1i ralbii anbi2i nfrexw r19.41 bitr4i r19.28v equequ2 ad2antrl
      simplr anbi2d rspc adantl imp sbievw bicomi sbco2vv pm3.35 equcomd sylbir
      sbbii ex com12 ad2antlr simplrr ad2antrr wb sbbidv imbi2d wsbc vex sbc2ie
      sbequ a1i biimprd adantld sbsbc sylibr pm2.27 biimtrid syl6 syld ralimdva
      ax7 exp31 com24 imp41 jca rspcedvd sbcom2 sbf 3bitri anbi12i syl impancom
      rexbii exp32 jcad expimpd ralrimivv syl5 expd impd reximdva reximia sylbi
      mpd ) AIMUDZHLUDZACIJUEZUFZJMUGZUHZIMUIZEDYSUFZJMUGZUHZIMUIZHKUEZUFZKLUGZ
      UHZHLUIZAFOIUEZBNHUEZUFZUHUFZOMUGNLUGZUHZIMUIZHLUIYRUUCHLUDUULYQUUCHLACIJ
      MRUPUJUUCUUGHKLUUHUUBUUFIMUUHAEUUAUUEPUUHYTUUDJMUUHCDYSQUKULUMUNUPUOUUKUU
      SHLUUKUUBEIUCUQZDIUCUQZUCJUEZUFZJMUGZUHZUCMUIZUUHUFZKLUGZUHZIMUIZHURLUSZU
      USUUKUUCUVHUHUVJUUJUVHUUCUUIUVGKLUUGUVFUUHUUFUVEIUCMUUFUCUTUUTUVDIEIUCVAU
      VCIJMIMVBZUVAUVBIDIUCVAUVBIUTVCVIVDZIUCUEZEUUTUUEUVDEIUCVEUVNUUDUVCJMUVND
      UVAYSUVBDIUCVEIUCJVFVGULUMVHVJVKVLUUBUVHIMUVGIKLILVBUVFUUHIUVEIUCMUVLUVMV
      MUUHIUTVCVIVNVOUVKUVIUURIMUVKIURMUSUHZUUBUVHUURUVOAUUAUVHUURUFUVOAUHZUUAU
      VHUURUUAUVHUHUUAUVGUHZKLUGZUVPUURUUAUVGKLVPUVPUVRUURUVPUVRUHZAUUQUVOAUVRV
      SUVSUUPNOLMUVPNURZLUSZOURZMUSZUHZUVRUUPUVPUWDUHZUVRUUAUUTKNUQZUVAKNUQZUVB
      UFZJMUGZUHZUCMUIZHNUEZUFZUHZUUPUWAUVRUWNUFUVPUWCUVQUWNKUVTLUUAUWMKUUAKUTU
      WKUWLKUWJKUCMKMVBZUWFUWIKUUTKNVAUWHKJMUWOUWGUVBKUVAKNVAUVBKUTVCVIVDVMUWLK
      UTVCVDKNUEZUVGUWMUUAUWPUVFUWKUUHUWLUWPUVEUWJUCMUWPUUTUWFUVDUWIUUTKNVEUWPU
      VCUWHJMUWPUVAUWGUVBUVAKNVEUKULUMUNKNHVQVGVTWAVRUWEUUAUWMUUPUWEUUAUHZCJOUQ
      ZIOUEZUFZUWMUUPUFZUWEUUAUWTUWDUUAUWTUFZUVPUWCUXBUWAYTUWTJUWBMUWRUWSJCJOVA
      UWSJUTVCJOUECUWRYSUWSCJOVEJOIVQVGWAWBWBWCUWTAIOUQZUWSUFZUWQUXAUWRUXCUWSUW
      RAIJUQZJOUQUXCCUXEJOUXECACIJRWDZWEZWJAIOJWFUOVJUWQUXDUWMUUPUWQUXDUHZUWMUH
      ZFUUMUUOUXDFUUMUFUWQUWMFUXDUUMFUXCUXDUUMUFAFIOSWDZUXCUXDUUMUXCUXDUHIOUXCU
      WSWGWHWKWIWLWMUXIFBUUNUXIFBUHZUHHNUXIUXKUWLUXHUXKUWMUWLUXHUXKUHZUWKUWMUWL
      UFUXLAIUCUQZHNUQZUXEHNUQZUVBUFZJMUGZUHZUCMUIUWKUXLUXRUXCHNUQZUXOOJUEZUFZJ
      MUGZUHZUCUWBMUWQUWCUXDUXKUVPUWAUWCUUAWNWOUCOUEZUXRUYCWPUXLUYDUXNUXSUXQUYB
      UYDUXMUXCHNAUCOIXBWQUYDUXPUYAJMUYDUVBUXTUXOUCOJVFWRULUMWBUXLUXSUYBUXLAIUW
      BWSZHUVTWSZUXSUXHUXKUYFUXHBUYFFUXHUYFBUYFBWPUXHABHIUVTUWBNWTOWTUBXAXCXDXE
      WCUXSUYEHNUQUYFUXCUYEHNAIOXFWJUYEHNXFUOXGUWEUUAUXDUXKUYBUWEUXKUXDUUAUYBUW
      EUXKUXDUUAUYBUFUWEUXKUHZUXDUHZYTUYAJMUYHJURMUSZUHZYTUYAUXOGUYJYTUHZUXTUXO
      CHNUQGUXECHNUXFWJCGHNTWDUOUYKGYSUXTYTGYSUFUYJYTGYSUAWKWBUYHYSUXTUFZUYIYTU
      YGUXDUYLUYGUXDUWSUYLUXDFUWSUFZUYGUWSUXCFUWSUXJVJFUYMUWSUFUWEBFUWSXHVRXIIO
      JXMXJWCWOXKXIWKXLXNXOXPXQXRUWJUXRUCMUWFUXNUWIUXQUWFUXMHKUQZKNUQUXNUUTUYNK
      NUUTAHKUQZIUCUQUYNEUYOIUCUYOEAEHKPWDWEWJAHKIUCXSUOWJUXMHNKWFUOUWHUXPJMUWG
      UXOUVBUWGCIUCUQZHKUQZKNUQUYPHNUQUXOUVAUYQKNUVACHKUQZIUCUQUYQDUYRIUCUYRDCD
      HKQWDWEWJCHKIUCXSUOWJUYPHNKWFUYPUXEHNUYPUXEIUCUQUXECUXEIUCUXGWJUXEIUCAIJV
      AXTUOWJYAVJVKYBYEXGUWKUWLXHYCYDWCWHYFYGXNXIYPYHXKYDYIXQWKYJYKYHYLYMXIYNYO
      $.
  $}

  ${
    $d V a b c d e f $.  $d ph c d e $.  $d th b d e f $.  $d ch a e f $.
    $d ta a e f $.  $d et b f $.  $d ps c $.
    2reuimp.c $e |- ( b = c -> ( ph <-> th ) ) $.
    2reuimp.d $e |- ( a = d -> ( ph <-> ch ) ) $.
    2reuimp.a $e |- ( a = d -> ( th <-> ta ) ) $.
    2reuimp.e $e |- ( b = e -> ( ph <-> et ) ) $.
    2reuimp.f $e |- ( c = f -> ( th <-> ps ) ) $.
    $( Implication of a double restricted existential uniqueness in terms of
       restricted existential quantification and restricted universal
       quantification.  The involved wffs depend on the setvar variables as
       follows: ph(a,b), th(a,c), ch(d,b), ta(d,c), et(a,e), ps(a,f)
       (Contributed by AV, 13-Mar-2023.) $)
    2reuimp0 $p |- ( E! a e. V E! b e. V ph
                    -> E. a e. V A. d e. V A. b e. V E. e e. V A. f e. V
                   ( ( et /\ ( ( ch /\ A. c e. V ( ta -> b = c ) ) -> a = d ) )
                     /\ ( ps -> e = f ) ) ) $=
      ( wral wa wreu wi wrex reu8 reubii imbi1d ralbidv anbi12d rexbidv r19.28v
      weq equequ1 imbi2d cbvrexvw r19.23v ancom r19.42v bitr4i equequ2 cbvralvw
      imbi12d ex expcom syl7bi imp32 reximi sylbi ralimi syl biimtrrid imp ) AK
      IUAZJIUAADKLUKZUBZLISZTZKIUCZJIUAZFCEVMUBZLISZTZJMUKZUBZTZBGHUKZUBZTHISZG
      IUCZKISZMISZJIUCZVLVQJIADKLINUDUEVRVQWAKIUCZWBUBZMISTZJIUCWKVQWLJMIWBVPWA
      KIWBACVOVTOWBVNVSLIWBDEVMPUFUGUHUIUDWNWJJIWNVQWMTZMISWJVQWMMIUJWOWIMIVQWM
      WIVQFDGLUKZUBZLISZTZGIUCZWMWIUBVPWSKGIKGUKZAFVOWRQXAVNWQLIXAVMWPDKGLULUMU
      GUHUNWMWCKISZWTWIWAWBKIUOWTXBWIWTXBTWTWCTZKISWIWTWCKIUJXCWHKIXCWCWSTZGIUC
      ZWHXCWCWTTXEWTWCUPWCWSGIUQURXDWGGIWCFWRWGWRWFHISZWCFWGWQWFLHILHUKDBWPWERL
      HGUSVAUTFWCXFWGUBWDXFWGWDWFHIUJVBVCVDVEVFVGVHVIVBVJVGVKVHVIVFVGVG $.

    $d ch c $.  $d et c $.
    $( Implication of a double restricted existential uniqueness in terms of
       restricted existential quantification and restricted universal
       quantification if the class of the quantified elements is not empty.
       (Contributed by AV, 13-Mar-2023.) $)
    2reuimp $p |- ( ( V =/= (/) /\ E! a e. V E! b e. V ph )
                 -> E. a e. V A. d e. V A. b e. V E. e e. V A. f e. V E. c e. V
                   ( ( ch /\ ( ta -> b = c ) )
                     -> ( ps -> ( et /\ ( a = d /\ e = f ) ) ) ) ) $=
      ( wi wa c0 wne weq wral wrex wreu r19.28zv bicomd imbi1d r19.36zv r19.42v
      pm5.31r an12 ancoms syl6 sylan reximi sylbir expcom expd biimtrrdi sylbid
      imbitrdi com23 imp4c ralimdv reximdv 2reuimp0 impel ) IUAUBZFCEKLUCSZLIUD
      TZJMUCZSZTBGHUCZSZTZHIUDZGIUEZKIUDZMIUDZJIUECVKTZBFVMVOTTZSZSZLIUEZHIUDZG
      IUEZKIUDZMIUDZJIUEAKIUFJIUFVJWAWJJIVJVTWIMIVJVSWHKIVJVRWGGIVJVQWFHIVJFVNV
      PWFVJVNFVPWFSZVJVNWBLIUDZVMSZFWKSZVJVLWLVMVJWLVLCVKLIUGUHUIVJWMWBVMSZLIUE
      ZWNWBVMLIUJWPFVPWFFVPTZWPWFWQWPTWQWOTZLIUEWFWQWOLIUKWRWELIWQBFVOTZSZWOWEB
      VOFULWTWOTWBWTVMTWDWBVMWTULVMWTWDVMWTTBVMWSTWCBWSVMULVMFVOUMVCUNUOUPUQURU
      SUTVAVBVDVEVFVGVFVFVGABCDEFGHIJKLMNOPQRVHVI $.
  $}

