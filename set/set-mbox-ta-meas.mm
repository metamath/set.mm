$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Abstract measure
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Sigma-Algebra
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c sigAlgebra $.

  $( Extend class notation to include the function giving the sigma-algebras on
     a given base set. $)
  csiga $a class sigAlgebra $.

  ${
    $d o s x $.
    $( Define a sigma-algebra, i.e. a set closed under complement and countable
       union.  Literature usually uses capital greek sigma and omega letters
       for the algebra set, and the base set respectively.  We are using ` S `
       and ` O ` as a parallel.  (Contributed by Thierry Arnoux,
       3-Sep-2016.) $)
    df-siga $a |- sigAlgebra = ( o e. _V |-> { s | ( s C_ ~P o /\
      ( o e. s /\ A. x e. s ( o \ x ) e. s
      /\ A. x e. ~P s ( x ~<_ _om -> U. x e. s ) ) ) } ) $.
  $}

  ${
    $d o s $.
    $( Lemma for ~ issiga and ~ isrnsiga .  The class of sigma-algebras with
       base set ` o ` is a set.  Note: a more generic version with
       ` ( O e. _V -> ... ) ` could be useful for ~ sigaval .  (Contributed by
       Thierry Arnoux, 24-Oct-2016.) $)
    sigaex $p |- { s | ( s C_ ~P o /\ ( o e. s /\ A. x e. s ( o \ x ) e. s
      /\ A. x e. ~P s ( x ~<_ _om -> U. x e. s ) ) ) } e. _V $=
      ( cv wcel cdif wral com cdom wbr cuni wi cpw w3a crab wss cab cvv pwexg
      wa df-rab velpw anbi1i abbii eqtri vex mp2b rabex eqeltrri ) BDZCDZEUJADZ
      FUKEAUKGULHIJULKUKELAUKMGNZCUJMZMZOZUKUNPZUMTZCQZRUPUKUOEZUMTZCQUSUMCUOUA
      VAURCUTUQUMCUNUBUCUDUEUMCUOUJREUNREUOREBUFUJRSUNRSUGUHUI $.
  $}

  ${
    $d s o x O $.
    $( The set of sigma-algebra with a given base set.  (Contributed by Thierry
       Arnoux, 23-Sep-2016.) $)
    sigaval $p |- ( O e. _V -> ( sigAlgebra ` O ) = { s | ( s C_ ~P O /\
      ( O e. s /\ A. x e. s ( O \ x ) e. s
      /\ A. x e. ~P s ( x ~<_ _om -> U. x e. s ) ) ) } ) $=
      ( vo cvv wcel cv cpw wss cdif wral com cdom wbr w3a cab csiga wceq pwexg
      wa cuni wi cfv crab df-rab velpw anbi1i abbii eqtri rabexg 3syl eqeltrrid
      sseq2d eleq1 difeq1 eleq1d ralbidv 3anbi12d anbi12d abbidv df-siga fvmptg
      pweq mpdan ) BEFZCGZBHZIZBVFFZBAGZJZVFFZAVFKZVJLMNVJUAVFFUBAVFHKZOZTZCPZE
      FBQUCVQRVEVQVOCVGHZUDZEVSVFVRFZVOTZCPVQVOCVRUEWAVPCVTVHVOCVGUFUGUHUIVEVGE
      FVREFVSEFBESVGESVOCVREUJUKULDBVFDGZHZIZWBVFFZWBVJJZVFFZAVFKZVNOZTZCPVQEEQ
      WBBRZWJVPCWKWDVHWIVOWKWCVGVFWBBVCUMWKWEVIWHVMVNWBBVFUNWKWGVLAVFWKWFVKVFWB
      BVJUOUPUQURUSUTADCVAVBVD $.
  $}

  ${
    $d o s x O $.  $d o s x S $.
    $( An alternative definition of the sigma-algebra, for a given base set.
       (Contributed by Thierry Arnoux, 19-Sep-2016.) $)
    issiga $p |- ( S e. _V -> ( S e. ( sigAlgebra ` O ) <->
      ( S C_ ~P O /\ ( O e. S /\ A. x e. S ( O \ x ) e. S
      /\ A. x e. ~P S ( x ~<_ _om -> U. x e. S ) ) ) ) ) $=
      ( vs vo cvv wcel wa csiga cpw wss cv cdif wral wi w3a elex a1i wb wceq
      cfv com cdom wbr cuni elfvex jca simpr1 anc2ri df-siga sigaex pweq sseq2d
      syl sseq1 eleq12 simpr difeq1 adantr eleq1d eleq2 adantl raleqbidv imbi2d
      sylan9bb bitrd 3anbi123d anbi12d abfmpel pm5.21ndd ) BFGZCFGZVKHZBCIUAZGZ
      BCJZKZCBGZCALZMZBGZABNZVSUBUCUDZVSUEZBGZOZABJZNZPZHZVOVMOVKVOVLVKBCIUFBVN
      QUGRVKWJVLWJVLOVKWJVRVLVQVRWBWHUHCBQUNRUIVMVOWJSOVKDLZELZJZKZWLWKGZWLVSMZ
      WKGZAWKNZWCWDWKGZOZAWKJZNZPZHWJEDCBIFFAEDUJAEDUKWLCTZWKBTZHZWNVQXCWIXDWNW
      KVPKXEVQXDWMVPWKWLCULUMWKBVPUOVEXFWOVRWRWBXBWHWLCWKBUPXFWQWAAWKBXDXEUQXFW
      QVTWKGZWAXFWPVTWKXDWPVTTXEWLCVSURUSUTXEXGWASXDWKBVTVAVBVFVCXEXBWHSXDXEWTW
      FAXAWGWKBULXEWSWEWCWKBWDVAVDVCVBVGVHVIRVJ $.
  $}

  ${
    $d o s x S $.
    $( The property of being a sigma-algebra on an indefinite base set.
       (Contributed by Thierry Arnoux, 3-Sep-2016.)  (Proof shortened by
       Thierry Arnoux, 23-Oct-2016.) $)
    isrnsiga $p |- ( S e. U. ran sigAlgebra <-> ( S e. _V /\
      E. o ( S C_ ~P o /\ ( o e. S /\ A. x e. S ( o \ x ) e. S
      /\ A. x e. ~P S ( x ~<_ _om -> U. x e. S ) ) ) ) ) $=
      ( vs csiga crn cuni wcel cvv cv cpw wss cdif wral com cdom wi w3a eleq2
      wa wbr wrex df-siga sigaex wceq sseq1 raleqbi1dv pweq raleqbidv 3anbi123d
      wex imbi2d anbi12d abfmpunirn rexv anbi2i bitri ) BEFGHBIHZBCJZKZLZUSBHZU
      SAJZMZBHZABNZVCOPUAZVCGZBHZQZABKZNZRZTZCIUBZTURVNCUKZTDJZUTLZUSVQHZVDVQHZ
      AVQNZVGVHVQHZQZAVQKZNZRZTVNCDBEIACDUCACDUDVQBUEZVRVAWFVMVQBUTUFWGVSVBWAVF
      WEVLVQBUSSVTVEAVQBVQBVDSUGWGWCVJAWDVKVQBUHWGWBVIVGVQBVHSULUIUJUMUNVOVPURV
      NCUOUPUQ $.

    $( A sigma-algebra contains the empty set.  (Contributed by Thierry Arnoux,
       4-Sep-2016.) $)
    0elsiga $p |- ( S e. U. ran sigAlgebra -> (/) e. S ) $=
      ( vo vx csiga crn cuni wcel cv cpw wss cdif wral com wbr wi w3a wa wex c0
      cdom cvv isrnsiga simprbi 3simpa adantl eximi difeq2 eqtrdi eleq1d rspcva
      weq difid exlimiv 3syl ) ADEFGZABHZIJZUPAGZUPCHZKZAGZCALZUSMTNUSFAGOCAILZ
      PZQZBRZURVBQZBRSAGZUOAUAGVFCABUBUCVEVGBVDVGUQURVBVCUDUEUFVGVHBVAVHCUPACBU
      KZUTSAVIUTUPUPKSUSUPUPUGUPULUHUIUJUMUN $.

    $d x A $.
    $( A sigma-algebra contains its base universe set.  (Contributed by Thierry
       Arnoux, 26-Oct-2016.) $)
    baselsiga $p |- ( S e. ( sigAlgebra ` A ) -> A e. S ) $=
      ( vx cvv wcel csiga cfv elex wa cv cdif wral com cdom wbr cuni wi cpw wss
      w3a issiga simplbda simp1d mpancom ) BDEZBAFGZEZABEZBUFHUEUGIUHACJZKBECBL
      ZUIMNOUIPBEQCBRLZUEUGBARSUHUJUKTCBAUAUBUCUD $.

    $( A sigma-algebra is a set of subset of the base set.  (Contributed by
       Thierry Arnoux, 18-Jan-2017.) $)
    sigasspw $p |- ( S e. ( sigAlgebra ` A ) -> S C_ ~P A ) $=
      ( vx csiga cfv wcel cpw wss cv cdif wral com cdom wbr cuni wi w3a wa elex
      cvv issiga biimpa mpancom simpld ) BADEZFZBAGHZABFACIZJBFCBKUHLMNUHOBFPCB
      GKQZBTFZUFUGUIRZBUESUJUFUKCBAUAUBUCUD $.

    $( A sigma-algebra is closed under countable union.  (Contributed by
       Thierry Arnoux, 26-Dec-2016.) $)
    sigaclcu $p |- ( ( S e. U. ran sigAlgebra /\ A e. ~P S /\ A ~<_ _om )
        -> U. A e. S ) $=
      ( vx vo csiga crn cuni wcel cpw com cdom wbr w3a cv wi wral simp2 cdif wa
      wss wex cvv isrnsiga simprbi simpr3 exlimiv syl 3ad2ant1 simp3 wceq breq1
      unieq eleq1d imbi12d rspcv syl3c ) BEFGHZABIZHZAJKLZMUSCNZJKLZVAGZBHZOZCU
      RPZUTAGZBHZUQUSUTQUQUSVFUTUQBDNZITZVIBHZVIVARBHCBPZVFMSZDUAZVFUQBUBHVNCBD
      UCUDVMVFDVJVKVLVFUEUFUGUHUQUSUTUIVEUTVHOCAURVAAUJZVBUTVDVHVAAJKUKVOVCVGBV
      AAULUMUNUOUP $.

    ${
      $d z A $.  $d z B $.  $d k z S $.
      sigaclcuni.1 $e |- F/_ k A $.
      $( A sigma-algebra is closed under countable union: indexed union
         version.  (Contributed by Thierry Arnoux, 8-Jun-2017.) $)
      sigaclcuni $p |- ( ( S e. U. ran sigAlgebra /\ A. k e. A B e. S
             /\ A ~<_ _om ) -> U_ k e. A B e. S ) $=
        ( vz csiga crn cuni wcel wral com cdom wbr wceq 3ad2ant2 wa eqeltrd syl
        wrex w3a ciun cv cab dfiun2g cpw simp1 wss r19.29 simpr simpl rexlimivw
        ex abssdv wb elpw2g mpbird abrexctf 3ad2ant3 sigaclcu syl3anc ) CGHIZJZ
        BCJZDAKZALMNZUAZDABUBZFUCZBOZDATZFUDZIZCVEVCVHVMOVFDFABCUEPVGVCVLCUFJZV
        LLMNZVMCJVCVEVFUGZVGVNVLCUHZVEVCVQVFVEVKFCVEVKVICJZVEVKQVDVJQZDATVRVDVJ
        DAUIVSVRDAVSVIBCVDVJUJVDVJUKRULSUMUNPVGVCVNVQUOVPVLCVBUPSUQVFVCVOVEDFAB
        EURUSVLCUTVAR $.
    $}

    $( A sigma-algebra is closed under finite union.  (Contributed by Thierry
       Arnoux, 28-Dec-2016.) $)
    sigaclfu $p |- ( ( S e. U. ran sigAlgebra /\ A e. ~P S /\ A e. Fin )
      -> U. A e. S ) $=
      ( cfn wcel csiga crn cuni cpw com cdom wbr fict sigaclcu syl3an3 ) ACDBEF
      GDABHDAIJKAGBDALABMN $.

    $d k x S $.
    $( A sigma-algebra is closed under countable union - indexing on ` NN `
       (Contributed by Thierry Arnoux, 29-Dec-2016.) $)
    sigaclcu2 $p |- ( ( S e. U. ran sigAlgebra /\ A. k e. NN A e. S )
      -> U_ k e. NN A e. S ) $=
      ( vx csiga crn cuni wcel cn wral wa ciun cv wceq wrex cab com cdom wbr wi
      dfiun2g adantl cpw simpl wss abid eleq1a ralimi r19.23v sylib imp adantll
      sylan2b ralrimiva nfcv dfss3f sylibr wb elpw2g adantr mpbird nnct abrexct
      nfab1 mp1i sigaclcu syl3anc eqeltrd ) BEFGZHZABHZCIJZKZCIALZDMZANZCIOZDPZ
      GZBVLVNVSNVJCDIABUAUBVMVJVRBUCHZVRQRSZVSBHVJVLUDVMVTVRBUEZVMVOBHZDVRJWBVM
      WCDVRVOVRHVMVQWCVQDUFVLVQWCVJVLVQWCVLVPWCTZCIJVQWCTVKWDCIABVOUGUHVPWCCIUI
      UJUKULUMUNDVRBVQDVDDBUOUPUQVJVTWBURVLVRBVIUSUTVAIQRSWAVMVBCDIAVCVEVRBVFVG
      VH $.

    $d k N $.
    $( A sigma-algebra is closed under finite union - indexing on
       ` ( 1 ..^ N ) ` .  (Contributed by Thierry Arnoux, 28-Dec-2016.) $)
    sigaclfu2 $p |- ( ( S e. U. ran sigAlgebra /\ A. k e. ( 1 ..^ N ) A e. S )
      -> U_ k e. ( 1 ..^ N ) A e. S ) $=
      ( csiga crn cuni wcel c1 cfzo co wral wa ciun cn cun wceq iuneq2i eqtri
      c0 cv cif cdif iunxun wss fzossnn undif mpbi iuneq1 ax-mp iftrue iffalsed
      eldifn uneq12i 3eqtr3i un0 0elsiga wi simpr simpllr mpd wn simplll ifclda
      iun0 exp31 ralimdv2 imp sylan sigaclcu2 syldan eqeltrrid ) BEFGHZABHZCIDJ
      KZLZMCVOANZCOCUAZVOHZATUBZNZBWAVQTPZVQCVOOVOUCZPZVTNZCVOVTNZCWCVTNZPWAWBC
      VOWCVTUDWDOQZWEWAQVOOUEWHDUFVOOUGUHCWDOVTUIUJWFVQWGTCVOVTAVSATUKRWGCWCTNT
      CWCVTTVRWCHVSATVROVOUMULRCWCVESUNUOVQUPSVMVPVTBHZCOLZWABHVMTBHZVPWJBUQWKV
      PWJWKVNWICVOOWKVSVNURZVROHZWIWKWLMWMMZVSATBWNVSMVSVNWNVSUSWKWLWMVSUTVAWKW
      LWMVSVBVCVDVFVGVHVIVTBCVJVKVL $.

    $d k M $.  $d k ph $.
    sigaclcu3.1 $e |- ( ph -> S e. U. ran sigAlgebra ) $.
    sigaclcu3.2 $e |- ( ph -> ( N = NN \/ N = ( 1 ..^ M ) ) ) $.
    sigaclcu3.3 $e |- ( ( ph /\ k e. N ) -> A e. S ) $.
    $( A sigma-algebra is closed under countable or finite union.  (Contributed
       by Thierry Arnoux, 6-Mar-2017.) $)
    sigaclcu3 $p |- ( ph -> U_ k e. N A e. S ) $=
      ( cn wceq ciun wcel wa simpr iuneq1d wral adantr raleqtrdv syl2anc c1 crn
      cfzo co csiga cuni ralrimiva sigaclcu2 eqeltrd sigaclfu2 mpjaodan ) AFJKZ
      DFBLZCMFUAEUCUDZKZAULNZUMDJBLZCUPDFJBAULOZPUPCUEUBUFMZBCMZDJQUQCMAUSULGRU
      PUTDFJAUTDFQZULAUTDFIUGZRURSBCDUHTUIAUONZUMDUNBLZCVCDFUNBAUOOZPVCUSUTDUNQ
      VDCMAUSUOGRVCUTDFUNAVAUOVBRVESBCDEUJTUIHUK $.
  $}

  ${
    $d o x S $.  $d x O $.
    $( Property of being a sigma-algebra with a given base set, noting that the
       base set of a sigma-algebra is actually its union set.  (Contributed by
       Thierry Arnoux, 24-Sep-2016.)  (Revised by Thierry Arnoux,
       23-Oct-2016.) $)
    issgon $p |- ( S e. ( sigAlgebra ` O ) <->
      ( S e. U. ran sigAlgebra /\ O = U. S ) ) $=
      ( vx vo csiga wcel cuni wceq wa elex cpw wss cdif wral w3a elpwuni biimpa
      cv ancom eqcom cfv crn fvssunirn sseli cvv com cdom wbr wi issiga 3imtr4i
      3ad2antr1 biimtrdi mpcom jca isrnsiga simprbi wb pweq sseq2d eleq1 difeq1
      wex eleq1d ralbidv anbi12d syl ibi exlimiv simprd biimprd pwuni sseqtrrid
      3anbi12d jctild anim2d biimpar syl56 impcom impbii ) ABEUAZFZAEUBGZFZBAGZ
      HZIWBWDWFWAWCAEBUCUDAUEFZWBWFAWAJWGWBABKZLZBAFZBCRZMZAFZCANZWKUFUGUHWKGAF
      UICAKNZOZIZWFCABUJZWIWNWJWFWOWJWIIWEBHZWIWJIWFWJWIWSABPQWIWJSBWETUKULUMUN
      UOWFWDWBWDWGWEAFZWEWKMZAFZCANZWOOZIWFWGWQIWBWDWGXDAWCJWDAWEKZLZXDWDADRZKZ
      LZXGAFZXGWKMZAFZCANZWOOZIZDVCZXFXDIZWDWGXPCADUPUQXOXQDXOXQXOXGWEHZXOXQURX
      IXMXJXRWOXJXIIWEXGHZXIXJIXRXJXIXSAXGPQXIXJSXGWETUKULXRXIXFXNXDXRXHXEAXGWE
      USUTXRXJWTXMXCWOXGWEAVAXRXLXBCAXRXKXAAXGWEWKVBVDVEVNVFVGVHVIVGVJUOWFXDWQW
      GWFXDWPWIWFWPXDWFWJWTWNXCWOBWEAVAWFWMXBCAWFWLXAABWEWKVBVDVEVNVKWFXEAWHAVL
      BWEUSVMVOVPWGWBWQWRVQVRVSVT $.
  $}

  $( A sigma-algebra is a sigma on its union set.  (Contributed by Thierry
     Arnoux, 6-Jun-2017.) $)
  sgon $p |- ( S e. U. ran sigAlgebra -> S e. ( sigAlgebra ` U. S ) ) $=
    ( csiga crn cuni wcel wceq cfv eqid wa issgon biimpri mpan2 ) ABCDEZADZNFZA
    NBGEZNHPMOIANJKL $.

  $( An element of a sigma-algebra is a subset of the base set.  (Contributed
     by Thierry Arnoux, 6-Jun-2017.) $)
  elsigass $p |- ( ( S e. U. ran sigAlgebra /\ A e. S ) -> A C_ U. S ) $=
    ( csiga crn cuni wcel wa cpw cfv wss sgon sigasspw syl sselda elpwid ) BCDE
    FZABFGABEZPBQHZAPBQCIFBRJBKQBLMNO $.

  $( Dropping the base information off a sigma-algebra.  (Contributed by
     Thierry Arnoux, 13-Feb-2017.) $)
  elrnsiga $p |- ( S e. ( sigAlgebra ` O ) -> S e. U. ran sigAlgebra ) $=
    ( csiga cfv crn cuni fvssunirn sseli ) BCDCEFACBGH $.

  ${
    $d x S $.
    $( The property of being a sigma-algebra, universe is the union set.
       (Contributed by Thierry Arnoux, 11-Nov-2016.) $)
    isrnsigau $p |- ( S e. U. ran sigAlgebra -> ( S C_ ~P U. S /\ ( U. S e. S
      /\ A. x e. S ( U. S \ x ) e. S
      /\ A. x e. ~P S ( x ~<_ _om -> U. x e. S ) ) ) ) $=
      ( csiga crn cuni wcel cfv cpw wss cv cdif wral com cdom wbr wi w3a wa cvv
      sgon wb elex issiga syl mpbid ) BCDEZFZBBEZCGFZBUHHIUHBFUHAJZKBFABLUJMNOU
      JEBFPABHLQRZBTUGBSFUIUKUABUFUBABUHUCUDUE $.

    $( A sigma-algebra contains its universe set.  (Contributed by Thierry
       Arnoux, 13-Feb-2017.)  (Shortened by Thierry Arnoux, 6-Jun-2017.) $)
    unielsiga $p |- ( S e. U. ran sigAlgebra -> U. S e. S ) $=
      ( csiga crn cuni wcel cfv sgon baselsiga syl ) ABCDEAADZBFEJAEAGJAHI $.
  $}

  ${
    $d x y $.
    $( Lebesgue-measurable subsets of ` RR ` form a sigma-algebra.
       (Contributed by Thierry Arnoux, 10-Sep-2016.)  (Revised by Thierry
       Arnoux, 24-Oct-2016.) $)
    dmvlsiga $p |- dom vol e. ( sigAlgebra ` RR ) $=
      ( vx vy cvol cdm cr csiga cfv wcel cpw wss cv cdif wral com cdom wbr cuni
      wi rgen cn w3a pwssb mblss mprgbir rembl cmmbl ciun nnenom ensymi domentr
      cen mpan2 elpwi dfss3 iunmbl2 syl2anr uniiun eleq1i imbitrrdi 3pm3.2i cvv
      sylib ex wa wb reex pwex ssexi issiga ax-mp mpbir2an ) CDZEFGHZVLEIZJZEVL
      HZEAKZLVLHZAVLMZVQNOPZVQQZVLHZRZAVLIZMZUAZVOVQEJAVLAVLEUBVQUCUDZVPVSWEUEV
      RAVLVQUFSWCAWDVQWDHZVTBVQBKZUGZVLHZWBWHVTWKVTVQTOPZWIVLHBVQMZWKWHVTNTUKPW
      LTNUHUIVQNTUJULWHVQVLJWMVQVLUMBVQVLUNVBVQWIBUOUPVCWAWJVLBVQUQURUSSUTVLVAH
      VMVOWFVDVEVLVNEVFVGWGVHAVLEVIVJVK $.
  $}

  ${
    $d x O $.  $d x V $.
    $( Any power set forms a sigma-algebra.  (Contributed by Thierry Arnoux,
       13-Sep-2016.)  (Revised by Thierry Arnoux, 24-Oct-2016.) $)
    pwsiga $p |- ( O e. V -> ~P O e. ( sigAlgebra ` O ) ) $=
      ( vx wcel cpw csiga cfv wss cv cdif wral com cdom wbr cuni ssidd ralrimiv
      wi w3a a1d pwidg difss elpw2g mpbiri vuniex elpw bitr4i biimpi elpwi mp1i
      sspwuni imim1i 3jca cvv wa wb pwexg issiga syl mpbir2and ) ABDZAEZAFGDZVB
      VBHZAVBDZACIZJZVBDZCVBKZVFLMNZVFOZVBDZRZCVBEZKZSZVAVBPVAVEVIVOABUAVAVHCVB
      VAVHVFVBDVAVHVGAHAVFUBVGABUCUDTQVAVMCVNVFVBHZVMRVFVNDZVMRVAVQVLVJVQVLVQVK
      AHVLVFAUKVKACUEUFUGUHTVRVQVMVFVBUIULUJQUMVAVBUNDVCVDVPUOUPABUQCVBAURUSUT
      $.
  $}

  ${
    $d x O $.
    $( The smallest possible sigma-algebra containing ` O ` .  (Contributed by
       Thierry Arnoux, 13-Sep-2016.) $)
    prsiga $p |- ( O e. V -> { (/) , O } e. ( sigAlgebra ` O ) ) $=
      ( vx wcel c0 cpr cpw cdif wral cuni 0ex cvv wceq eleq1d ralprg cun pm3.2i
      wa wb unieq wss cv com cdom wbr wi w3a csiga cfv 0elpw pwidg prssi prid2g
      sylancr dif0 eqeltrid difid prid1 a1i difeq2 mpan mpbir2and eqeltri unisn
      uni0 snex mp1i mpbiri unisng eqeltrd uniprg uncom eqtri eqtrdi prex ralun
      csn un0 syl2anc pwpr raleqi sylibr ax-1 ralimi 3jca issiga ax-mp sylanbrc
      syl ) ABDZEAFZAGZUAZAWKDZACUBZHZWKDZCWKIZWOUCUDUEZWOJZWKDZUFZCWKGZIZUGZWK
      AUHUIDZWJEWLDAWLDWMAUJABUKEAWLULUNWJWNWRXDEABUMZWJWRAEHZWKDZAAHZWKDZWJXHA
      WKAUOXGUPWJXJEWKAUQEWKDWJEAKURZUSUPELDZWJWRXIXKRSKWQXIXKCEALBWOEMZWPXHWKW
      OEAUTNWOAMWPXJWKWOAAUTNOVAVBWJXACXCIZXDWJXACEEVQZFZAVQZWKFZPZIZXOWJXACXQI
      ZXACXSIZYAWJYBEJZWKDZXPJZWKDZRZYEYGYDEWKVEXLVCYFEWKEKVDXLVCQXMXPLDZRYBYHS
      WJXMYIKEVFQXAYEYGCEXPLLXNWTYDWKWOETNWOXPMWTYFWKWOXPTNOVGVHWJYCXRJZWKDZWKJ
      ZWKDZWJYJAWKABVIXGVJWJYLAWKWJYLEAPZAXMWJYLYNMKEALBVKVAYNAEPAEAVLAVRVMVNXG
      VJXRLDZWKLDZRYCYKYMRSWJYOYPAVFEAVOZQXAYKYMCXRWKLLWOXRMWTYJWKWOXRTNWOWKMWT
      YLWKWOWKTNOVGVBXACXQXSVPVSXACXCXTEAVTWAWBXAXBCXCXAWSWCWDWIWEYPXFWMXERSYQC
      WKAWFWGWH $.
  $}

  ${
    $d x y z A $.  $d x y z S $.
    $( A sigma-algebra is closed under countable intersections.  Deduction
       version.  The proof uses ~ abrexct rather than ~ abrexdom2jm , and so
       does not require ~ ax-ac .  (Contributed by Thierry Arnoux,
       19-Sep-2016.)  (Revised by Vincent Gonzalez, 19-Aug-2026.) $)
    sigaclci $p |- ( ( ( S e. U. ran sigAlgebra /\ A e. ~P S ) /\
      ( A ~<_ _om /\ A =/= (/) ) ) -> |^| A e. S ) $=
      ( vz vx vy cuni wcel wa com cdom wbr cv cdif wral wi wss adantr wb adantl
      wceq csiga crn cpw c0 wne cint ciun w3a isrnsigau simprd simp2d cab elpwi
      wrex ssrexv syl ss2abdv uniiunlem mpbid sylan9ssr cvv elpwg mpbird simp3d
      abrexexg abrexct ex breq1 unieq eleq1d imbi12d rspcva sylsyld ssralv sylc
      jca dfiun2g eleq1 3syl sylibrd difeq2 rspccv adantrd imp simpr iundifdifd
      pwuni sstrdi adantld syl6 ) BUAUBFGZABUCZGZHZAIJKZAUDUEZHZHAUFZBGZBFZCAWT
      CLZMZUGZMZBGZWNWQXEWNWOXEWPWNWTDLZMZBGZDBNZWOXCBGZXEWKXIWMWKWTBGZXIXFIJKZ
      XFFZBGZOZDWLNZWKBWTUCZPZXKXIXPUHDBUIUJZUKQWNWOELXBTZCAUNZEULZFZBGZXJWNYBW
      LGZXPHWOYBIJKZYDWNYEXPWNYEYBBPZWMWKYBXTCBUNZEULZBWMYAYHEWMABPZYAYHOABUMZX
      TCABUOUPUQWKXBBGZCBNZYIBPZWKXKYMXAIJKXAFBGOCWLNZWKXRXKYMYOUHCBUIUJUKZWKYM
      YMYNRYPCEBXBBBURUPUSUTWMYEYGRZWKWMYBVAGYQCEAXBWLVEYBBVAVBUPSVCWKXPWMWKXKX
      IXPXSVDQVPWMWOYFOWKWMWOYFWOYFWMCEAXBVFSVGSXOYFYDODYBWLXFYBTZXLYFXNYDXFYBI
      JVHYRXMYCBXFYBVIVJVKVLVMWNYLCANZXCYCTXJYDRWNYJYMYSWMYJWKYKSWKYMWMYPQYLCAB
      VNVOCEAXBBVQXCYCBVRVSVTXHXEDXCBXFXCTXGXDBXFXCWTWAVJWBVMWCWDWNWQWSXERZWNWQ
      WRXDTZYTWNWPUUAWOWNWMAXQPWPUUAOWKWMWEWMABXQYKBWGWHCAWTWFVSWIWRXDBVRWJWDVC
      $.
  $}

  ${
    $d x A $.  $d x S $.
    $( A sigma-algebra is closed under complement relative to its base set.
       This is immediate from the definition, see ~ issiga , but the library
       states it nowhere in this form.  (Contributed by Vincent Gonzalez,
       17-Aug-2026.) $)
    difunielsiga $p |- ( ( S e. U. ran sigAlgebra /\ A e. S ) ->
      ( U. S \ A ) e. S ) $=
      ( vx csiga crn cuni wcel cv cdif wral com wbr wi cpw wss isrnsigau simprd
      cdom w3a simp2d wceq difeq2 eleq1d rspccva sylan ) BDEFGZBFZCHZIZBGZCBJZA
      BGUGAIZBGZUFUGBGZUKUHKRLUHFBGMCBNJZUFBUGNOUNUKUOSCBPQTUJUMCABUHAUAUIULBUH
      AUGUBUCUDUE $.
    $( $j usage 'difunielsiga' avoids 'ax-ac' 'ax-ac2'; $)
  $}

  ${
    $d x A $.  $d x B $.  $d x S $.
    $( A sigma-algebra is closed under pairwise unions.  (Contributed by
       Thierry Arnoux, 13-Dec-2016.) $)
    unelsiga $p |- ( ( S e. U. ran sigAlgebra /\ A e. S /\ B e. S ) ->
      ( A u. B ) e. S ) $=
      ( vx csiga crn cuni wcel w3a cpr cun wceq uniprg 3adant1 com cdom wbr cpw
      wi wral cv cdif isrnsigau simprd simp3d 3ad2ant1 prct prelpwi breq1 unieq
      wss wa eleq1d imbi12d rspcv syl mp2d eqeltrrd ) CEFGHZACHZBCHZIZABJZGZABK
      ZCUTVAVDVELUSABCCMNVBDUAZOPQZVFGZCHZSZDCRZTZVCOPQZVDCHZUSUTVLVAUSCGZCHZVO
      VFUBCHDCTZVLUSCVORUKVPVQVLIDCUCUDUEUFUTVAVMUSABCCUGNUTVAVLVMVNSZSZUSUTVAU
      LVCVKHVSABCUHVJVRDVCVKVFVCLZVGVMVIVNVFVCOPUIVTVHVDCVFVCUJUMUNUOUPNUQUR $.
  $}

  $( A sigma-algebra is closed under class differences.  The proof goes through
     ~ difunielsiga and ~ unelsiga rather than countable intersection, and so
     does not use ~ ax-ac .  (Contributed by Thierry Arnoux, 13-Sep-2016.)
     (Proof shortened by Vincent Gonzalez, 17-Aug-2026.) $)
  difelsiga $p |- ( ( S e. U. ran sigAlgebra /\ A e. S /\ B e. S ) ->
    ( A \ B ) e. S ) $=
    ( csiga crn cuni wcel w3a cdif cun wceq difun1 a1i wss simp1 simp2 elsigass
    syl2anc dfss4 difunielsiga sylib difeq1d eqtrd unelsiga syl3anc eqeltrrd
    simp3 ) CDEFGZACGZBCGZHZCFZULAIZBJZIZABIZCUKUOULUMIZBIZUPUOURKUKULUMBLMUKUQ
    ABUKAULNZUQAKUKUHUIUSUHUIUJOZUHUIUJPZACQRAULSUAUBUCUKUHUNCGZUOCGUTUKUHUMCGZ
    UJVBUTUKUHUIVCUTVAACTRUHUIUJUGUMBCUDUEUNCTRUF $.
    $( $j usage 'difelsiga' avoids 'ax-ac' 'ax-ac2'; $)

  $( A sigma-algebra is closed under pairwise intersections.  (Contributed by
     Thierry Arnoux, 13-Dec-2016.) $)
  inelsiga $p |- ( ( S e. U. ran sigAlgebra /\ A e. S /\ B e. S ) ->
    ( A i^i B ) e. S ) $=
    ( csiga crn cuni wcel w3a cin cdif dfin4 difelsiga syld3an3 eqeltrid ) CDEF
    GZACGZBCGZHABIAABJZJZCABKOPQRCGSCGABCLARCLMN $.

  ${
    $d x A $.  $d x S $.
    $( Building a sigma-algebra from intersections with a given set.
       (Contributed by Thierry Arnoux, 26-Dec-2016.) $)
    sigainb $p |- ( ( S e. U. ran sigAlgebra /\ A e. S ) ->
      ( S i^i ~P A ) e. ( sigAlgebra ` A ) ) $=
      ( vx csiga cuni wcel wa cpw wss wral simpr syl elind simplr syl3anc elpwg
      ralrimiva sstr mpan2 3syl crn cin cvv cv cdif com cdom wbr w3a cfv inex1g
      adantr inss2 a1i pwidg simpll inss1 sselid difelsiga difss mpbiri simplll
      wi elpwi biimpar syl2anc sigaclcu sspwuni vuniex elpw bitr4i sylib issiga
      ex 3jca syl12anc ) BDUAEZFZABFZGZBAHZUBZUCFZWBWAIZAWBFZACUDZUEZWBFZCWBJZW
      FUFUGUHZWFEZWBFZVCZCWBHZJZUIZWBADUJFZVRWCVSBWAVQUKULWDVTBWAUMZUNVTWEWIWOV
      TBWAAVRVSKZVTVSAWAFWSABUOLMVTWHCWBVTWFWBFZGZBWAWGXAVRVSWFBFWGBFZVRVSWTUPV
      RVSWTNXAWBBWFBWAUQZVTWTKURAWFBUSOZXAXBWGWAFZXDXBXEWGAIAWFUTWGABPVALMQVTWM
      CWNVTWFWNFZGZWJWLXGWJGZBWAWKXHVRWFBHFZWJWKBFVRVSXFWJVBXHXFWFBIZXIVTXFWJNZ
      XHXFWFWBIZXJXKWFWBVDZXLWBBIXJXCWFWBBRSTXFXIXJWFBWNPVEVFXGWJKWFBVGOXHWFWAI
      ZWKWAFZXHXFXLXNXKXMXLWDXNWRWFWBWARSTXNWKAIXOWFAVHWKACVIVJVKVLMVNQVOWCWQWD
      WPGCWBAVMVEVP $.
  $}

  ${
    $d s x A $.  $d s x O $.
    $( The intersection of a collection of sigma-algebras of same base is a
       sigma-algebra.  (Contributed by Thierry Arnoux, 27-Dec-2016.) $)
    insiga $p |- ( ( A =/= (/) /\ A e. ~P ( sigAlgebra ` O ) )
      -> |^| A e. ( sigAlgebra ` O ) ) $=
      ( vx vs csiga cpw wcel wa cvv wss cv wral cuni simpr syl ralrimiva elintg
      wb mpbird jca c0 wne cfv cint cdif com cdom wbr w3a intex birani intssuni
      wi adantr elpwi sigasspw velpw sylibr ssriv sstrdi sspwuni simplr elelpwi
      sylib sstrd syl2anc vex issiga ax-mp simprd simp1d wex eximdv mpd exlimiv
      n0 ex elfvex simpll elinti adantll simp2d r19.21bi difexd simplll simpllr
      imp intss1 sylan9ss sylancom simp3d sylc uniexg ad2antlr biimpar syl12anc
      3jca ) AUAUBZABEUCZFGZHZAUDZIGZXBBFZJZBXBGZBCKZUEZXBGZCXBLZXGUFUGUHZXGMZX
      BGZUMZCXBFZLZUIZXBWSGZWRXCWTAUJUKXAXBAMZXDWRXBXSJWTAULUNXAAXDFZJZXSXDJXAW
      TYAWRWTNWTAWSXTAWSUODWSXTDKZWSGZYBXDJZYBXTGBYBUPDXDUQURUSUTOAXDVAVDVEXAXF
      XJXPXAXFBYBGZDALZXAYEDAXAYBAGZHZYEXHYBGZCYBLZXKXLYBGZUMZCYBFZLZYHYDYEYJYN
      UIZYHYCYDYOHZYHYGWTYCXAYGNWRWTYGVBYBAWSVCVFZYBIGYCYPRDVGCYBBVHVIVDVJZVKPX
      ABIGZXFYFRXAYCDVLZYSXAYGDVLZYTWRUUAWTDAVPUKXAYGYCDXAYGYCYQVQVMVNYCYSDYBBE
      VRVOOZDBAIQOSXAXICXBXAXGXBGZHZXIYIDALZUUDYIDAUUDYGHZYHXGYBGZYIUUFXAYGXAUU
      CYGVSUUDYGNTUUCYGUUGXAUUCYGUUGXGAYBVTWGWAYHYICYBYHYEYJYNYRWBWCVFPUUDXHIGZ
      XIUUERXAUUHUUCXABXGIUUBWDUNDXHAIQOSPXAXNCXOXAXGXOGZHZXKXMUUJXKHZXMYKDALZU
      UKYKDAUUKYGHZYHXGYMGZHXKYKUUMYHUUNUUMXAYGXAUUIXKYGWEUUKYGNTUUKYGUUIUUNXAU
      UIXKYGWFUUIYGHXGYBJUUNUUIYGXGXBYBXGXBUOYBAWHWICYBUQURWJTUUJXKYGVBYHYLCYMY
      HYEYJYNYRWKWCWLPUUKXLIGZXMUULRUUIUUOXAXKXGXOWMWNDXLAIQOSVQPWQXCXRXEXQHCXB
      BVHWOWP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Generated sigma-Algebra
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c sigaGen $.
  $( Extend class notation to include the sigma-algebra generator. $)
  csigagen $a class sigaGen $.

  ${
    $d s x $.
    $( Define the sigma-algebra generated by a given collection of sets as the
       intersection of all sigma-algebra containing that set.  (Contributed by
       Thierry Arnoux, 27-Dec-2016.) $)
    df-sigagen $a |- sigaGen = ( x e. _V |->
      |^| { s e. ( sigAlgebra ` U. x ) | x C_ s } ) $.
  $}

  ${
    $d s x A $.  $d x V $.
    $( Value of the generated sigma-algebra.  (Contributed by Thierry Arnoux,
       27-Dec-2016.) $)
    sigagenval $p |- ( A e. V -> ( sigaGen ` A ) =
      |^| { s e. ( sigAlgebra ` U. A ) | A C_ s } ) $=
      ( vx wcel cv wss cuni cfv crab cint cvv csigagen cmpt wceq df-sigagen a1i
      csiga unieq fveq2d sseq1 rabeqbidv inteqd adantl c0 wne cpw uniexg pwsiga
      elex wa syl pwuni jctir sseq2 elrab sylibr ne0d intex sylib fvmptd ) ABEZ
      DADFZCFZGZCVCHZRIZJZKZAVDGZCAHZRIZJZKZLMLMDLVINOVBDCPQVCAOZVIVNOVBVOVHVMV
      OVEVJCVGVLVOVFVKRVCASTVCAVDUAUBUCUDABUJVBVMUEUFVNLEVBVMVKUGZVBVPVLEZAVPGZ
      UKVPVMEVBVQVRVBVKLEVQABUHVKLUIULAUMUNVJVRCVPVLVDVPAUOUPUQURVMUSUTVA $.
  $}

  ${
    $d s A $.
    $( A generated sigma-algebra is a sigma-algebra.  (Contributed by Thierry
       Arnoux, 27-Dec-2016.) $)
    sigagensiga $p |- ( A e. V -> ( sigaGen ` A ) e. ( sigAlgebra ` U. A ) ) $=
      ( vs wcel csigagen cfv cv wss cuni csiga crab cint sigagenval wne cpw cvv
      c0 fvex eqeltrrdi sylibr intex ssrab2 a1i elpw2 insiga syl2anc eqeltrd )
      ABDZAEFZACGHZCAIZJFZKZLZULABCMZUHUMQNZUMULODZUNULDUHUNPDUPUHUNUIPUOAERSUM
      UATUHUMULHZUQURUHUJCULUBUCUMULUKJRUDTUMUKUEUFUG $.
  $}

  ${
    sgsiga.1 $e |- ( ph -> A e. V ) $.
    $( A generated sigma-algebra is a sigma-algebra.  (Contributed by Thierry
       Arnoux, 30-Jan-2017.) $)
    sgsiga $p |- ( ph -> ( sigaGen ` A ) e. U. ran sigAlgebra ) $=
      ( wcel csigagen cfv cuni csiga crn sigagensiga elrnsiga 3syl ) ABCEBFGZBH
      ZIGENIJHEDBCKNOLM $.
  $}

  $( The sigma-algebra generated by a collection ` A ` is a sigma-algebra on
     ` U. A ` .  (Contributed by Thierry Arnoux, 27-Dec-2016.) $)
  unisg $p |- ( A e. V -> U. ( sigaGen ` A ) = U. A ) $=
    ( wcel cuni csigagen cfv csiga crn wceq wa sigagensiga issgon simprd eqcomd
    sylib ) ABCZADZAEFZDZPRGHDCZQSIZPRQGFCTUAJABKRQLOMN $.

  ${
    $d j s $.
    $( A sigma-algebra can be generated from any set.  (Contributed by Thierry
       Arnoux, 21-Jan-2017.) $)
    dmsigagen $p |- dom sigaGen = _V $=
      ( vj vs cvv cv wss cuni csiga cfv crab cint csigagen c0 wne wcel wrex cpw
      vuniex pwsiga ax-mp pwuni sseq2 rspcev mp2an rabn0 mpbir intex df-sigagen
      mpbi dmmpti ) ACADZBDZEZBUJFZGHZIZJZKUOLMZUPCNUQULBUNOZUMPZUNNZUJUSEZURUM
      CNUTAQUMCRSUJTULVABUSUNUKUSUJUAUBUCULBUNUDUEUOUFUHABUGUI $.
  $}

  ${
    $d s A $.
    $( A set is a subset of the sigma-algebra it generates.  (Contributed by
       Thierry Arnoux, 24-Jan-2017.) $)
    sssigagen $p |- ( A e. V -> A C_ ( sigaGen ` A ) ) $=
      ( vs wcel cv wss cuni cfv crab cint csigagen ssintub sigagenval sseqtrrid
      csiga ) ABDACEFCAGOHZIJAAKHCAPLABCMN $.
  $}

  $( A subset of the generating set is also a subset of the generated
     sigma-algebra.  (Contributed by Thierry Arnoux, 22-Sep-2017.) $)
  sssigagen2 $p |- ( ( A e. V /\ B C_ A ) -> B C_ ( sigaGen ` A ) ) $=
    ( wcel wss wa csigagen cfv simpr sssigagen adantr sstrd ) ACDZBAEZFBAAGHZMN
    IMAOENACJKL $.

  $( Any element of a set is also an element of the sigma-algebra that set
     generates.  (Contributed by Thierry Arnoux, 27-Mar-2017.) $)
  elsigagen $p |- ( ( A e. V /\ B e. A ) -> B e. ( sigaGen ` A ) ) $=
    ( wcel csigagen cfv sssigagen sselda ) ACDAAEFBACGH $.

  $( Any countable union of elements of a set is also in the sigma-algebra that
     set generates.  (Contributed by Thierry Arnoux, 17-Sep-2017.) $)
  elsigagen2 $p |- ( ( A e. V /\ B C_ A /\ B ~<_ _om )
                                      -> U. B e. ( sigaGen ` A ) ) $=
    ( wcel wss com cdom wbr w3a csigagen cfv csiga crn cuni cpw simp1 sssigagen
    sgsiga 3syl cvv sspw simp2 simp3 ctex elpwg mpbird sseldd sigaclcu syl3anc
    wb ) ACDZBAEZBFGHZIZAJKZLMNDBUOOZDUMBNUODUNACUKULUMPZRUNAOZUPBUNUKAUOEURUPE
    UQACQAUOUASUNBURDZULUKULUMUBUNUMBTDUSULUJUKULUMUCZBUDBATUESUFUGUTBUOUHUI $.

  ${
    $d s A $.  $d s S $.
    $( The generated sigma-algebra is a subset of all sigma-algebras containing
       the generating set, i.e. the generated sigma-algebra is the smallest
       sigma-algebra containing the generating set, here ` A ` .  (Contributed
       by Thierry Arnoux, 4-Jun-2017.) $)
    sigagenss $p |- ( ( S e. ( sigAlgebra ` U. A ) /\ A C_ S ) ->
      ( sigaGen ` A ) C_ S ) $=
      ( vs cuni csiga cfv wcel wss wa csigagen cv crab cint cvv wceq sigagenval
      ssexg ancoms syl sseq2 intminss eqsstrd ) BADEFZGZABHZIZAJFZACKZHZCUCLMZB
      UFANGZUGUJOUEUDUKABUCQRANCPSUIUECBUCUHBATUAUB $.
  $}

  $( Sufficient condition for inclusion of sigma-algebras.  This is used to
     prove equality of sigma-algebras.  (Contributed by Thierry Arnoux,
     10-Oct-2017.) $)
  sigagenss2 $p |- ( ( U. A = U. B /\ A C_ ( sigaGen ` B ) /\ B e. V ) ->
    ( sigaGen ` A ) C_ ( sigaGen ` B ) ) $=
    ( cuni wceq csigagen cfv wss wcel csiga sigagensiga 3ad2ant3 simp1 eleqtrrd
    w3a fveq2d simp2 sigagenss syl2anc ) ADZBDZEZABFGZHZBCIZOZUCTJGZIUDAFGUCHUF
    UCUAJGZUGUEUBUCUHIUDBCKLUFTUAJUBUDUEMPNUBUDUEQAUCRS $.

  $( The sigma-algebra generated by a sigma-algebra is itself.  (Contributed by
     Thierry Arnoux, 4-Jun-2017.) $)
  sigagenid $p |- ( S e. U. ran sigAlgebra -> ( sigaGen ` S ) = S ) $=
    ( csiga crn cuni wcel csigagen cfv wss sgon ssid sigagenss sssigagen eqssd
    sylancl ) ABCDZEZAFGZAPAADBGEAAHQAHAIAJAAKNAOLM $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  lambda and pi-Systems, Rings of Sets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Because they are not widely used outside of measure theory, we do not
  introduce specific definitions for lambda- and pi-systems.  Instead, we
  define ` P ` and ` L ` respectively as the classes of pi- and lambda-systems
  in ` O ` throughout this section.

$)

  ${
    $d O s t x y $.  $d S s x y $.  $d P t $.
    ispisys.p $e |- P = { s e. ~P ~P O | ( fi ` s ) C_ s } $.
    $( The property of being a pi-system.  (Contributed by Thierry Arnoux,
       10-Jun-2020.) $)
    ispisys $p |- ( S e. P <-> ( S e. ~P ~P O /\ ( fi ` S ) C_ S ) ) $=
      ( cv cfi cfv wss cpw wceq fveq2 id sseq12d elrab2 ) DFZGHZPIBGHZBIDBCJJAP
      BKZQRPBPBGLSMNEO $.

    $( The property of being a pi-system, expanded version.  Pi-systems are
       closed under finite intersections.  (Contributed by Thierry Arnoux,
       13-Jun-2020.) $)
    ispisys2 $p |- ( S e. P <-> ( S e. ~P ~P O
      /\ A. x e. ( ( ~P S i^i Fin ) \ { (/) } ) |^| x e. S ) ) $=
      ( vy wcel cpw cfi cfv wss wa cv cint cfn cin c0 wral cvv csn cdif ispisys
      dfss3 elex adantr eldifsn bilani simpld elin1d elpwid simprd elin2d elfir
      syl13anc wceq wrex elfi2 biimpa simpr eleq1d ralxfrd bitrid pm5.32i bitri
      wne ) CBHCDIIZHZCJKZCLZMVHANZOZCHZACIZPQZRUAUBZSZMBCDEFUCVHVJVQVJGNZCHZGV
      ISVHVQGVICUDVHVSVMGAVLVIVPVHVKVPHZMZCTHZVKCLVKRVFZVKPHVLVIHVHWBVTCVGUEUFW
      AVKCWAVNPVKWAVKVOHZWCVTWDWCMVHVKVORUGUHZUIZUJUKWAWDWCWEULWAVNPVKWFUMVKCTU
      NUOVHVRVIHVRVLUPZAVPUQAVRCVGURUSVHWGMVRVLCVHWGUTVAVBVCVDVE $.

    $d A x $.  $d B x $.  $d P x $.
    $( Pi-systems are closed under pairwise intersections.  (Contributed by
       Thierry Arnoux, 6-Jul-2020.) $)
    inelpisys $p |- ( ( S e. P /\ A e. S /\ B e. S ) -> ( A i^i B ) e. S ) $=
      ( vx wcel w3a cpr cint cin wceq intprg 3adant1 cv cpw cfn c0 inteq eleq1d
      csn cdif wral ispisys2 simprbi 3ad2ant1 prelpwi prfi elind prnzg 3ad2ant2
      a1i wne neneqd elsni nsyl eldifd rspcdva eqeltrrd ) DCIZADIZBDIZJZABKZLZA
      BMZDVCVDVGVHNVBABDDOPVEHQZLZDIZVGDIHDRZSMZTUCZUDZVFVIVFNVJVGDVIVFUAUBVBVC
      VKHVOUEZVDVBDERRIVPHCDEFGUFUGUHVEVFVMVNVEVLSVFVCVDVFVLIVBABDUIPVFSIVEABUJ
      UNUKVEVFTNVFVNIVEVFTVCVBVFTUOVDABDULUMUPVFTUQURUSUTVA $.

    $( All sigma-algebras are pi-systems.  (Contributed by Thierry Arnoux,
       13-Jun-2020.) $)
    sigapisys $p |- ( sigAlgebra ` O ) C_ P $=
      ( vt vx csiga cfv cv wcel cpw cint cfn cin c0 csn cdif wral wa sylibr wss
      sigasspw velpw crn cuni com wbr wne elrnsiga adantr eldifsn bilani simpld
      cdom elin1d elin2d fict simprd sigaclci syl22anc ralrimiva ispisys2 ssriv
      syl jca ) EBGHZAEIZVFJZVGBKZKJZFIZLVGJZFVGKZMNZOPQZRZSVGAJVHVJVPVHVGVIUAV
      JBVGUBEVIUCTVHVLFVOVHVKVOJZSZVGGUDUEJZVKVMJVKUFUNUGZVKOUHZVLVHVSVQVGBUIUJ
      VRVMMVKVRVKVNJZWAVQWBWASVHVKVNOUKULZUMZUOVRVKMJVTVRVMMVKWDUPVKUQVDVRWBWAW
      CURVKVGUSUTVAVEFAVGBCDVBTVC $.
  $}

  ${
    $d s u y $.  $d L t $.  $d O s t x $.  $d S s x $.  $d V x $.
    isldsys.l $e |- L = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s ( O \ x ) e. s
      /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. s ) ) } $.
    $( The property of being a lambda-system or Dynkin system.  Lambda-systems
       contain the empty set, are closed under complement, and closed under
       countable disjoint union.  (Contributed by Thierry Arnoux,
       13-Jun-2020.) $)
    isldsys $p |- ( S e. L
      <-> ( S e. ~P ~P O /\ ( (/) e. S /\ A. x e. S ( O \ x ) e. S
      /\ A. x e. ~P S ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. S ) ) ) ) $=
      ( c0 cv wcel cdif wral com cdom wbr wdisj wi cpw w3a eleq2 cuni wceq pweq
      wa raleqbi1dv imbi2d raleqbidv 3anbi123d elrab2 ) HFIZJZEAIZKZUJJZAUJLZUL
      MNOBULBIPUDZULUAZUJJZQZAUJRZLZSHCJZUMCJZACLZUPUQCJZQZACRZLZSFCERRDUJCUBZU
      KVBUOVDVAVHUJCHTUNVCAUJCUJCUMTUEVIUSVFAUTVGUJCUCVIURVEUPUJCUQTUFUGUHGUI
      $.

    $( The power set of the universe set ` O ` is always a lambda-system.
       (Contributed by Thierry Arnoux, 21-Jun-2020.) $)
    pwldsys $p |- ( O e. V -> ~P O e. L ) $=
      ( wcel cpw c0 cv cdif wral com cdom wa cvv pwidg ralrimiva wss wdisj cuni
      wbr wi w3a pwexg syl 0elpw a1i adantr elpwdifcl elpwi sylib adantl vuniex
      sspwuni elpw sylibr a1d 3jca isldsys sylanbrc ) DEHZDIZVDIZHZJVDHZDAKZLVD
      HZAVDMZVHNOUCBVHBKUAPZVHUBZVDHZUDZAVEMZUEVDCHVCVDQHVFDEUFVDQRUGVCVGVJVOVG
      VCDUHUIVCVIAVDVCVHVDHZPDVHDVCDVDHVPDERUJUKSVCVNAVEVCVHVEHZPZVMVKVRVLDTZVM
      VQVSVCVQVHVDTVSVHVDULVHDUPUMUNVLDAUOUQURUSSUTABVDCDFGVAVB $.

    ${
      $d s x y z $.  $d A y z $.  $d B y z $.  $d O z $.  $d S z $.  $d ph z $.
      unelldsys.s $e |- ( ph -> S e. L ) $.
      unelldsys.a $e |- ( ph -> A e. S ) $.
      unelldsys.b $e |- ( ph -> B e. S ) $.
      unelldsys.c $e |- ( ph -> ( A i^i B ) = (/) ) $.
      $( Lambda-systems are closed under disjoint set unions.  (Contributed by
         Thierry Arnoux, 21-Jun-2020.) $)
      unelldsys $p |- ( ph -> ( A u. B ) e. S ) $=
        ( vz wcel c0 wceq wa adantr cun uneq1 adantl un0 eqtr3i eqeltrd wne cpr
        uncom eqtrdi cuni uniprg syl2anc com cdom wbr wdisj prct cin wex bilani
        cv wb n0 wn disjel sylan adantll mpdan adantlr exlimddv disjprg syl3anc
        nelne1 id mpbird wi cpw breq1 disjeq1 anbi12d unieq eleq1d imbi12d cdif
        wral w3a crab biid difeq2 cbvralvw 3anbi123i rabbii eqtri isldsys sylib
        simprd simp3d prelpwi rspcdva mp2and eqeltrrd pm2.61dane ) ADEUAZFPDQAD
        QRZSZXDEFXFXDQEUAZEXEXDXGRADQEUBUCEQUAXGEEQUIEUDUEUJAEFPZXEMTUFADQUGZSZ
        DEUHZUKZXDFAXLXDRZXIADFPZXHXMLMDEFFULUMTXJXKUNUOUPZCXKCVBZUQZXLFPZAXOXI
        AXNXHXOLMDEFFURUMTXJXQDEUSQRZAXSXINTXJXNXHDEUGZXQXSVCAXNXILTAXHXIMTXJOV
        BZDPZXTOXIYBOUTAODVDVAAYBXTXIAYBSYAEPVEZXTAXSYBYCNDEYAVFVGYBYCXTAYADEVN
        VHVIVJVKCDEXPDEFXPDRVOXPERVOVLVMVPAXOXQSZXRVQZXIAYAUNUOUPZCYAXPUQZSZYAU
        KZFPZVQZYEOFVRZXKYAXKRZYHYDYJXRYMYFXOYGXQYAXKUNUOVSCYAXKXPVTWAYMYIXLFYA
        XKWBWCWDAQFPZHYAWEZFPOFWFZYKOYLWFZAFHVRVRZPZYNYPYQWGZAFGPYSYTSKOCFGHIGQ
        IVBZPZHBVBZWEZUUAPZBUUAWFZUUCUNUOUPZCUUCXPUQZSZUUCUKZUUAPZVQZBUUAVRZWFZ
        WGZIYRWHUUBYOUUAPZOUUAWFZYHYIUUAPZVQZOUUMWFZWGZIYRWHJUUOUVAIYRUUBUUBUUF
        UUQUUNUUTUUBWIUUEUUPBOUUAUUCYARZUUDYOUUAUUCYAHWJWCWKUULUUSBOUUMUVBUUIYH
        UUKUURUVBUUGYFUUHYGUUCYAUNUOVSCUUCYAXPVTWAUVBUUJYIUUAUUCYAWBWCWDWKWLWMW
        NWOWPWQWRAXNXHXKYLPLMDEFWSUMWTTXAXBXC $.
    $}

    $( All sigma-algebras are lambda-systems.  (Contributed by Thierry Arnoux,
       13-Jun-2020.) $)
    sigaldsys $p |- ( sigAlgebra ` O ) C_ L $=
      ( vt csiga cfv cv wcel cpw c0 wral cuni sylibr adantr syl3anc ralrimiva
      wa cdif com cdom wbr wdisj wi w3a wss sigasspw velpw crn elrnsiga 0elsiga
      syl baselsiga simpr difelsiga ad2antrr simplr simprl sigaclcu ex 3jca jca
      isldsys ssriv ) GDHIZCGJZVGKZVHDLZLKZMVHKZDAJZUAVHKZAVHNZVMUBUCUDZBVMBJUE
      ZTZVMOVHKZUFZAVHLZNZUGZTVHCKVIVKWCVIVHVJUHVKDVHUIGVJUJPVIVLVOWBVIVHHUKOKZ
      VLVHDULZVHUMUNVIVNAVHVIVMVHKZTWDDVHKZWFVNVIWDWFWEQVIWGWFDVHUOQVIWFUPDVMVH
      UQRSVIVTAWAVIVMWAKZTZVRVSWIVRTWDWHVPVSVIWDWHVRWEURVIWHVRUSWIVPVQUTVMVHVAR
      VBSVCVDABVHCDEFVEPVF $.

    $d t y $.  $d A s t u x $.  $d L s u x $.  $d ph t u x $.
    ldsysgenld.1 $e |- ( ph -> O e. V ) $.
    ldsysgenld.2 $e |- ( ph -> A C_ ~P O ) $.
    $( The intersection of all lambda-systems containing a given collection of
       sets ` A ` , which is called the lambda-system generated by ` A ` , is
       itself also a lambda-system.  (Contributed by Thierry Arnoux,
       16-Jun-2020.) $)
    ldsysgenld $p |- ( ph -> |^| { t e. L | A C_ t } e. L ) $=
      ( cv cpw wcel wral wa wi elintrab ex vu wss crab cint cdif com cdom wdisj
      c0 wbr cuni w3a csiga pwsiga sigaldsys sselid sseq2 elrab sylanbrc intss1
      cfv syl sselpwd isldsys simprbi simp1d adantl a1d ralrimiva sylibr nfrab1
      0ex nfv nfcv nfint nfel simplr vex biimpi r19.21bi simp2d syl2anc ralrimi
      nfan imp wb cvv difexg elintrabg 3syl adantr mpbird nfpw simpllr syl21anc
      simpr ssrdv sspwd simp-4r sseldd simp3d vuniex 3jca jca ) AEDMZUBZDFUCZUD
      ZGNZNZOZUIXHOZGBMZUEZXHOZBXHPZXMUFUGUJCXMCMUHQZXMUKZXHOZRZBXHNZPZULZQXHFO
      AXKYCAXHXIGUMVAZAGHOZXIYDOKGHUNVBZAXIXGOZXHXIUBAXIFOEXIUBZYGAYDFXIBCFGIJU
      OYFUPLXFYHDXIFXEXIEUQURUSXIXGUTVBVCAXLXPYBAXFUIXEOZRZDFPXLAYJDFAXEFOZQYIX
      FYKYIAYKYIXNXEOZBXEPZXQXRXEOZRZBXENZPZYKXEXJOYIYMYQULBCXEFGIJVDVEZVFVGVHV
      IXFDUIFVLSVJAXOBXHAXMXHOZQZXOXFYLRZDFPZYTUUADFAYSDADVMZDXMXHDXMVNZDXGXFDF
      VKVOZVPWDYTYKUUAYTYKQZXFYLUUFXFQYKXMXEOZYLYTYKXFVQUUFXFUUGYTXFUUGRZDFYSUU
      HDFPZAYSUUIXFDXMFBVRSVSVGVTWEYKYLBXEYKYIYMYQYRWAVTWBTTWCAXOUUBWFZYSAYEXNW
      GOUUJKGXMHWHXFDXNFWGWIWJWKWLVIAXTBYAAXMYAOZQZXQXSUULXQQZXFYNRZDFPXSUUMUUN
      DFUULXQDAUUKDUUCDXMYAUUDDXHUUEWMVPWDXQDVMWDUUMYKUUNUUMYKQZXFYNUUOXFQZYKXM
      YPOZXQYNUUMYKXFVQUUPYAYPXMUUPXHXEUUPUAXHXEUUPUAMZXHOZUURXEOZUUPUUSQUUSYKX
      FUUTUUPUUSWPUUMYKXFUUSWNUUOXFUUSVQUUSYKQXFUUTUUSXFUUTRZDFUUSUVADFPXFDUURF
      UAVRSVSVTWEWOTWQWRAUUKXQYKXFWSWTUULXQYKXFWNYKUUQQXQYNYKYOBYPYKYIYMYQYRXAV
      TWEWOTTWCXFDXRFBXBSVJTVIXCXDBCXHFGIJVDVJ $.
  $}

  ${
    $d f i n s t x y z $.  $d L f i n t x y $.  $d O s t x $.
    $d P f i n t x y $.
    dynkin.p $e |- P = { s e. ~P ~P O | ( fi ` s ) C_ s } $.
    dynkin.l $e |- L = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s ( O \ x ) e. s
      /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. s ) ) } $.
    ${
      $d A n $.  $d B x $.  $d N n x $.
      sigapildsyslem.n $e |- F/ n ph $.
      sigapildsyslem.1 $e |- ( ph -> t e. ( P i^i L ) ) $.
      sigapildsyslem.2 $e |- ( ph -> A e. t ) $.
      sigapildsyslem.3 $e |- ( ph -> N e. Fin ) $.
      sigapildsyslem.4 $e |- ( ( ph /\ n e. N ) -> B e. t ) $.
      $( Lemma for ~ sigapildsys .  (Contributed by Thierry Arnoux,
         13-Jun-2020.) $)
      sigapildsyslem $p |- ( ph -> ( A \ U_ n e. N B ) e. t ) $=
        ( wcel ciun cdif cv c0 wceq wa iuneq1 0iun eqtrdi difeq2d adantl adantr
        dif0 eqeltrd wne ciin iindif2 cfi cfv cpw wss cin elin1d ispisys simprd
        sylib wral cfn nfv nfan simpld elpwid sseldd difin2 syl cdom wdisj cuni
        com wbr w3a elin2d isldsys simp2d adantlr difeq2 eleq1d rspc mpd inelfi
        wi syl3anc ex ralrimi simpr cvv vex iinfi mpan eqeltrrd pm2.61dane ) AE
        HJFUAZUBZDUCZTJUDAJUDUEZUFXCEXDXEXCEUEAXEXCEUDUBEXEXBUDEXEXBHUDFUAUDHJU
        DFUGHFUHUIUJEUMUIUKAEXDTZXEQULUNAJUDUOZUFZHJEFUBZUPZXCXDXGXJXCUEAHJEFUQ
        UKXHXDURUSZXDXJXHXDKUTZUTTZXKXDVAZXHXDGTXMXNUFXHGIXDAXDGIVBZTZXGPULZVCG
        XDKLMVDVFZVEZXHXIXDTZHJVGZXGJVHTZXJXKTZXHXTHJAXGHOXGHVIVJXHHUCJTZXTXHYD
        UFZXIKFUBZEVBZXDYEEKVAZXIYGUEXHYHYDXHEKXHXDXLEXHXDXLXHXMXNXRVKVLAXFXGQU
        LZVMVLULEFKVNVOYEXKXDYGXHXNYDXSULYEXPYFXDTZXFYGXKTXHXPYDXQULYEKBUCZUBZX
        DTZBXDVGZYJXHYNYDXHUDXDTZYNYKVSVPVTCYKCUCVQUFYKVRXDTWKBXDUTVGZXHXMYOYNY
        PWAZXHXDITXMYQUFXHGIXDXQWBBCXDIKLNWCVFVEWDULYEFXDTZYNYJWKAYDYRXGSWEYMYJ
        BFXDYJBVIYKFUEYLYFXDYKFKWFWGWHVOWIXHXFYDYIULYFEXOXDWJWLVMUNWMWNAXGWOAYB
        XGRULXDWPTYAXGYBWAYCDWQHJXIXDWPWRWSWLVMWTXA $.
    $}

    $( Sigma-algebra are exactly classes which are both lambda and pi-systems.
       (Contributed by Thierry Arnoux, 13-Jun-2020.) $)
    sigapildsys $p |- ( sigAlgebra ` O ) = ( P i^i L ) $=
      ( vn vi cv wcel com cdom wbr wa c0 wceq cn cvv vt csiga cfv cin sigapisys
      vf sigaldsys ssini cpw wss cdif wral cuni wi w3a cfi elin1d ispisys sylib
      simpld elpwid dif0 wdisj elin2d isldsys simprd simp2d simp1d difeq2 eqidd
      id eleq12d rspcv syl eqeltrrid unieq uni0 eqtrdi adantl ad3antrrr eqeltrd
      mpd wne wfo csdm wex vex bilanri cen simplr nnenom ensymi domentr sylancl
      0sdom fodomr syl2anc c1 cfzo ciun fveq2 iundisj crn wfn fofn fniunfv forn
      co unieqd eqtrd eqtr3id cmpt fvex difexg dfiun3 nfv nfcv nfmpt1 nfrn nfel
      ax-mp nfan simpr nfiu1 nfdif nfeq ad7antr simp-4r wf fof ffvelcdmd sseldd
      nfmpt a1i adantr ex wb sylibr mp1i imp ad4antlr cfn sselda sigapildsyslem
      fzofi fzossnn wrex eqid elrnmpti bilani r19.29af ssrdv mptex elpwg simp3d
      nnex rnex ad4antr nnct mptct rnct iundisj2 disjrnmpt breq1 disjeq1 eleq1d
      anbi12d syl22anc eqeltrid eqeltrrd exlimddv pm2.61dane ralrimiva 3jca jca
      imbi12d issiga ssriv eqssi ) EUBUCZCDUDZUVTCDCEFGUEABDEFHUGUHUAUWAUVTUAKZ
      UWALZUWBEUIZUJZEUWBLZEAKZUKZUWBLZAUWBULZUWGMNOZUWGUMZUWBLZUNZAUWBUIZULZUO
      ZPZUWBUVTLZUWCUWEUWQUWCUWBUWDUWCUWBUWDUILZUWBUPUCUWBUJZUWCUWBCLUWTUXAPUWC
      CDUWBUWCVKZUQCUWBEFGURUSUTVAUWCUWFUWJUWPUWCEEQUKZUWBEVBUWCUWJUXCUWBLZUWCQ
      UWBLZUWJUWKBUWGBKZVCZPZUWMUNZAUWOULZUWCUWTUXEUWJUXJUOZUWCUWBDLUWTUXKPUWCC
      DUWBUXBVDABUWBDEFHVEUSVFZVGZUWCUXEUWJUXDUNUWCUXEUWJUXJUXLVHZUWIUXDAQUWBUW
      GQRZUWHUXCUWBUWBUWGQEVIUXOUWBVJVLVMVNWBVOUXMUWCUWNAUWOUWCUWGUWOLZPZUWKUWM
      UXQUWKPZUWMUWGQUXRUXOPUWLQUWBUXOUWLQRUXRUXOUWLQUMQUWGQVPVQVRVSUWCUXEUXPUW
      KUXOUXNVTWAUXRUWGQWCZPZSUWGUFKZWDZUWMUFUXTQUWGWEOZUWGSNOZUYBUFWFUYCUXSUXR
      UWGAWGWOWHUXTUWKMSWIOUYDUXQUWKUXSWJSMWKWLUWGMSWMWNSUWGUFWPWQUXTUYBPZISIKZ
      UYAUCZJWRUYFWSXHZJKZUYAUCZWTZUKZWTZUWLUWBUYBUYMUWLRUXTUYBUYMISUYGWTZUWLUY
      GUYJJIUYFUYIUYAXAZXBUYBUYNUYAXCZUMZUWLUYBUYASXDUYNUYQRSUWGUYAXEISUYAXFVNU
      YBUYPUWGSUWGUYAXGXIXJXKVSUYEUYMISUYLXLZXCZUMZUWBISUYLUYGTLUYLTLUYFUYAXMUY
      GUYKTXNYAZXOUYEUYSUWOLZUXJUYSMNOZBUYSUXFVCZUYTUWBLZUYEUYSUWBUJZVUBUYEBUYS
      UWBUYEUXFUYSLZUXFUWBLZUYEVUGPZUXFUYLRZVUHISUYEVUGIUYEIXPIUXFUYSIUXFXQIUYR
      ISUYLXRXSXTYBVUIUYFSLZPZVUJPZUXFUYLUWBVULVUJYCVUMABUAUYGUYJCJDUYHEFGHVULV
      UJJVUIVUKJUYEVUGJUYEJXPJUXFUYSJUXFXQZJUYRJISUYLJSXQJUYGUYKJUYGXQJUYHUYJYD
      YEZYMXSXTYBVUKJXPYBJUXFUYLVUNVUOYFYBUWCUWCUXPUWKUXSUYBVUGVUKVUJUXBYGVUMUW
      GUWBUYGVUMUWGUWBUYEUXPVUGVUKVUJUWCUXPUWKUXSUYBYHVTVAZVUMSUWGUYFUYAUYBSUWG
      UYAYIZUXTVUGVUKVUJSUWGUYAYJUUAZVUIVUKVUJWJYKYLUYHUUBLVUMWRUYFUUEYNVUMUYIU
      YHLZPZUWGUWBUYJVUMUWGUWBUJVUSVUPYOVUTSUWGUYIUYAVUMVUQVUSVURYOVUMUYHSUYIUY
      HSUJVUMUYFUUFYNUUCYKYLUUDWAVUGVUJISUUGUYEISUYLUXFUYRUYRUUHVUAUUIUUJUUKYPU
      ULUYSTLVUBVUFYQUYRISUYLUUPUUMUUQUYSUWBTUUNYAYRUWCUXJUXPUWKUXSUYBUWCUXEUWJ
      UXJUXLUUOUURUYRMNOZVUCUYESMNOVVAUUSISUYLUUTYAUYRUVAYSISUYLVCVUDUYEUYGUYJJ
      IUYOUVBIBSUYLUVCYSVUBUXJPVUCVUDPZVUEVUBUXJVVBVUEUNZUXIVVCAUYSUWOUWGUYSRZU
      XHVVBUWMVUEVVDUWKVUCUXGVUDUWGUYSMNUVDBUWGUYSUXFUVEUVGVVDUWLUYTUWBUWGUYSVP
      UVFUVPVMYTYTUVHUVIUVJUVKUVLYPUVMUVNUVOUWBTLUWSUWRYQUAWGAUWBEUVQYAYRUVRUVS
      $.

    $d L s t u x $.  $d O t u $.  $d S t $.  $d T s t u x $.  $d ph t x $.
    dynkin.o $e |- ( ph -> O e. V ) $.
    ${
      ldgenpisys.e $e |- E = |^| { t e. L | T C_ t } $.
      ldgenpisys.1 $e |- ( ph -> T e. P ) $.
      ${
        $d b s x $.  $d A b s t x y z $.  $d E b s t x y $.  $d L z $.
        $d O b t y $.  $d V x $.  $d T y $.  $d ph y $.
        ldgenpisyslem1.1 $e |- ( ph -> A e. E ) $.
        $( Lemma for ~ ldgenpisys .  (Contributed by Thierry Arnoux,
           29-Jun-2020.) $)
        ldgenpisyslem1 $p |- ( ph -> { b e. ~P O | ( A i^i b ) e. E } e. L ) $=
          ( wcel vz cv cin cpw crab c0 cdif wral com cdom wbr wdisj wa cuni w3a
          wi wss ssrab2 cvv wb pwexg rabexg elpwg 4syl mpbiri wceq ineq2 eleq1d
          0elpw a1i cint isldsys simprbi simp1d ad2antlr ralrimiva 0ex elintrab
          ex sylibr in0 3eltr4g elrabd elrab pwidg syl adantr elpwdifcl pwldsys
          cun cfi cfv ispisys sylib simpld elpwid sseq2 intminss syl2anc sseldd
          eqsstrid ad3antrrr difin difin2 eqtrid eqtrdi difuncomp eqtr3d difeq2
          incom simp2d cbvralvw simplr eleqtrdi elintrabg r19.21bi imp adantllr
          mpbid simpr rspcdva simpllr simprd vex inex2 mp1i rspa syl21anc inss1
          disjdif ssdisj mp2an eleqtrrdi nfan nfcv breq1 anbi12d unieq imbi12d
          nfv eqtri unelldsys eqeltrd inex1g mpbird jca sylan2b sspwi elpwunicl
          sselid cmpt crn ciun uniin2 dfiun3 eqtr3i nfdisj1 elpwi sselda eleq2i
          ad4antlr sylanb ralrimi rnmptss sselpwd 1stcrestlem disjin2 disjrnmpt
          bitri eqid 3syl nfmpt1 nfrn cbvdisjf disjeq1f simp3d disjeq1 syl22anc
          id eqeltrid vuniex 3jca sylanbrc ) AEMUBZUCZHTZMJUDZUEZUWGUDZTZUFUWHT
          ZJBUBZUGZUWHTZBUWHUHZUWLUIUJUKZCUWLCUBZULZUMZUWLUNZUWHTZUPZBUWHUDZUHZ
          UOUWHITAUWJUWHUWGUQZUWFMUWGURZAJKTZUWGUSTUWHUSTUWJUXEUTPJKVAUWFMUWGUS
          VBUWHUWGUSVCVDVEAUWKUWOUXDAUWFEUFUCZHTMUFUWGUWDUFVFUWEUXHHUWDUFEVGVHU
          FUWGTAJVIVJAUFGDUBZUQZDIUEVKZUXHHAUXJUFUXITZUPZDIUHUFUXKTAUXMDIAUXIIT
          ZUMZUXJUXLUXNUXLAUXJUXNUXLUWMUXITZBUXIUHZUWSUWTUXITZUPZBUXIUDZUHZUXNU
          XIUWITUXLUXQUYAUOBCUXIIJLOVLVMZVNVOVSVPUXJDUFIVQVRVTEWAQWBWCAUWNBUWHA
          UWLUWHTZUMUWMUWGTZEUWMUCZHTZUMZUWNUYCAUWLUWGTZEUWLUCZHTZUMZUYGUWFUYJM
          UWLUWGUWDUWLVFUWEUYIHUWDUWLEVGVHWDAUYKUMZUYDUYFUYLJUWLJAJUWGTZUYKAUXG
          UYMPJKWEWFWGWHUYLUYEUXKHUYLUYEUXKTZUXJUYEUXITZUPZDIUHZUYLUYPDIUYLUXNU
          MZUXJUYOUYRUXJUMZUYEJJEUGZUYIWJZUGZUXIUYSEJUQZUYEVUBVFAVUCUYKUXNUXJAE
          JAHUWGEAHUXKUWGQAUWGITZGUWGUQZUXKUWGUQAUXGVUDPBCIJKLOWIWFAGUWGAGUWITZ
          GWKWLGUQZAGFTVUFVUGUMRFGJLNWMWNWOWPUXJVUEDUWGIUXIUWGGWQWRWSXASWTWPXBV
          UCEUYIUGZUYEVUBVUCVUHUWMEUCZUYEVUCVUHEUWLUGVUIEUWLXCEUWLJXDXEUWMEXJXF
          EUYIJXGXHWFUYSJUWQUGZUXITZVUBUXITCUXIVUAUWQVUAVFVUJVUBUXIUWQVUAJXIVHU
          YSUXQVUKCUXIUHUXNUXQUYLUXJUXNUXLUXQUYAUYBXKZVOUXPVUKBCUXIUWLUWQVFUWMV
          UJUXIUWLUWQJXIVHXLWNUYSBCUYTUYIUXIIJLOUYLUXNUXJXMZUYSUXNEUXITZUYTUXIT
          ZVUMAUXNUXJVUNUYKUXOUXJVUNAUXJVUNUPZDIAEUXKTZVUPDIUHZAEHUXKSQXNAEHTZV
          UQVURUTSUXJDEIHXOWFXSXPXQXRUXNVUNUMUXPVUOBUXIEUWLEVFUWMUYTUXIUWLEJXIV
          HUXNUXQVUNVULWGUXNVUNXTYAWSUYSUXJUYIUXITZUPZDIUHZUXNUXJVUTUYSUYIUXKTZ
          VVBUYSUYIHUXKUYSUYHUYJAUYKUXNUXJYBYCQXNUYIUSTVVCVVBUTUYSUWLEBYDYEUXJD
          UYIIUSXOYFXSVUMUYRUXJXTVVBUXNUMUXJVUTVVADIYGXQYHUYTUYIUCZUFVFUYSVVDUY
          IUYTUCZUFUYTUYIXJUYIEUQEUYTUCUFVFVVEUFVFEUWLYIEJYJUYIEUYTYKYLUUAVJUUB
          YAUUCVSVPUYLUYEUSTZUYNUYQUTAVVFUYKAVUSVVFSEUWMHUUDWFWGUXJDUYEIUSXOWFU
          UEQYMUUFUUGUWFUYFMUWMUWGUWDUWMVFUWEUYEHUWDUWMEVGVHWDVTVPAUXBBUXCAUWLU
          XCTZUMZUWSUXAVVHUWSUMZUWFEUWTUCZHTMUWTUWGUWDUWTVFUWEVVJHUWDUWTEVGVHVV
          IUWLJVVIUXCUWIUWLUWHUWGUXFUUHAVVGUWSXMUUJUUIVVIVVJUXKHVVIUXJVVJUXITZU
          PZDIUHVVJUXKTVVIVVLDIVVIUXNUMZUXJVVKVVMUXJUMZVVJCUWLEUWQUCZUUKZUULZUN
          ZUXICUWLVVOUUMVVJVVRCEUWLUUNCUWLVVOUWQECYDYEZUUOUUPVVNUXNVVQUXTTZVVQU
          IUJUKZCVVQUWQULZVVRUXITZVVIUXNUXJXMZVVNVVQUXIIVWDVVNVVOUXITZCUWLUHVVQ
          UXIUQVVNVWECUWLVVMUXJCVVIUXNCVVHUWSCVVHCYTUWPUWRCUWPCYTCUWLUWQUUQYNYN
          UXNCYTYNUXJCYTYNVVNUWQUWLTZVWEVVNVWFUMZVVOHTZUXNUXJVWEVWGUWQUWHTZVWHV
          VNUWLUWHUWQVVGUWLUWHUQAUWSUXNUXJUWLUWHUURUVAUUSVWIUWQUWGTVWHUWFVWHMUW
          QUWGUWDUWQVFUWEVVOHUWDUWQEVGVHWDVMWFVVIUXNUXJVWFYBVVMUXJVWFXMVWHUXNUM
          UXJVWEVWHUXJVWEUPZDIUHZUXNVWJVWHVVOUXKTVWKHUXKVVOQUUTUXJDVVOIVVSVRUVI
          VWJDIYGUVBXQYHVSUVCCUWLVVOUXIVVPVVPUVJUVDWFUVEVVNUWPVWAVVNUWPUWRVVHUW
          SUXNUXJYBZWOCUWLVVOUVFWFVVNUAVVQUAUBZULZVWBVVNUWRCUWLVVOULVWNVVNUWPUW
          RVWLYCCEUWLUWQUVGCUAUWLVVOUVHUVKCUAVVQUWQVWMCVVPCUWLVVOUVLUVMZUAUWQYO
          CVWMYOZUWQVWMVFUVSUVNVTUXNVVTUMZVWAVWBUMZVWCVWQVWMUIUJUKZCVWMUWQULZUM
          ZVWMUNZUXITZUPZVWRVWCUPUAUXTVVQVWMVVQVFZVXAVWRVXCVWCVXEVWSVWAVWTVWBVW
          MVVQUIUJYPCVWMVVQUWQVWPVWOUVOYQVXEVXBVVRUXIVWMVVQYRVHYSUXNVXDUAUXTUHZ
          VVTUXNUYAVXFUXNUXLUXQUYAUYBUVPUXSVXDBUAUXTUWLVWMVFZUWSVXAUXRVXCVXGUWP
          VWSUWRVWTUWLVWMUIUJYPCUWLVWMUWQUVQYQVXGUWTVXBUXIUWLVWMYRVHYSXLWNWGUXN
          VVTXTYAXQUVRUVTVSVPUXJDVVJIUWTEBUWAYEVRVTQYMWCVSVPUWBBCUWHIJLOVLUWC
          $.

        ldgenpisyslem2.1 $e |- ( ph -> T C_ { b e. ~P O | ( A i^i b ) e. E } )
          $.
        $( Lemma for ~ ldgenpisys .  (Contributed by Thierry Arnoux,
           18-Jul-2020.) $)
        ldgenpisyslem2 $p |- ( ph -> E C_ { b e. ~P O | ( A i^i b ) e. E } ) $=
          ( cv wss crab cint cin wcel cpw ldgenpisyslem1 jca sseq2 elrab sylibr
          wa intss1 syl eqsstrid ) AHGDUAZUBZDIUCZUDZEMUAUEHUFMJUGUCZQAVAUSUFZU
          TVAUBAVAIUFZGVAUBZUMVBAVCVDABCDEFGHIJKLMNOPQRSUHTUIURVDDVAIUQVAGUJUKU
          LVAUSUNUOUP $.
      $}

      ${
        $d A b s t x y $.  $d E b s t x y $.  $d L y $.  $d O b y $.
        $d T b s t x y $.  $d V x $.  $d ph b y $.
        ldgenpisyslem3.1 $e |- ( ph -> A e. T ) $.
        $( Lemma for ~ ldgenpisys .  (Contributed by Thierry Arnoux,
           18-Jul-2020.) $)
        ldgenpisyslem3 $p |- ( ph -> E C_ { b e. ~P O | ( A i^i b ) e. E } ) $=
          ( wcel cv wss crab cint wi wral id rgenw ssintrab sseqtrri sselid cpw
          mpbir cin cfi cfv ispisys sylib simpld elpwi syl adantr simpr syl3anc
          wa inelpisys ralrimiva jca ssrab sylibr ldgenpisyslem2 ) ABCDEFGHIJKL
          MNOPQRAGHEGGDUAUBZDIUCUDZHGVMUBVLVLUEZDIUFVNDIVLUGUHVLDGIUIUMQUJZSUKA
          GJULZUBZEMUAZUNZHTZMGUFZVEGVTMVPUCUBAVQWAAGVPULTZVQAWBGUOUPGUBZAGFTZW
          BWCVERFGJLNUQURUSGVPUTVAAVTMGAVRGTZVEZGHVSVOWFWDEGTZWEVSGTAWDWERVBAWG
          WESVBAWEVCEVRFGJLNVFVDUKVGVHVTMVPGVIVJVK $.
      $}

      $d E a b c s t x y $.  $d L b y $.  $d O b c y $.  $d T b c y $.
      $d V x $.  $d ph a b c y $.
      $( The lambda system ` E ` generated by a pi-system ` T ` is also a
         pi-system.  (Contributed by Thierry Arnoux, 18-Jun-2020.) $)
      ldgenpisys $p |- ( ph -> E e. P ) $=
        ( vc wcel wa cv va vb cpw cfi cfv wss cdif wral com cdom wbr wdisj cuni
        c0 w3a crab ssrab2 cint eleqtrdi sselid elpwid ldsysgenld eqeltrid wceq
        wi cin simprr simprl adantr simpr sselda ad2antrr ldgenpisyslem3 simplr
        incom sseldd ineq2 eleq1d elrab sylib simprd eqeltrrid jca sylibr ssrdv
        ex ldgenpisyslem2 syldan ssrab rspcv ralrimivva inficl syl mpbid eqimss
        sylc wb ispisys ) AGIUCZUCZRZGUDUEZGUFZSGERAXAXCAUNKTZRIBTZUGXDRBXDUHXE
        UIUJUKCXECTULSXEUMXDRVEBXDUCUHUOZKWTUPZWTGXFKWTUQAGHXGAGFDTUFDHUPURHOAB
        CDFHIJKMNAFWSAXDUDUEXDUFZKWTUPZWTFXHKWTUQAFEXIPLUSUTVAZVBVCZMUSUTAXBGVD
        ZXCAUATZUBTZVFZGRZUBGUHUAGUHZXLAXPUAUBGGAXMGRZXNGRZSZSZXSXMQTZVFZGRZQGU
        HZXPAXRXSVGYAGWSUFZYEYAGYDQWSUPZUFZYFYESAXTXRYHAXRXSVHAXRSZBCDXMEFGHIJK
        QLMAIJRZXRNVIOAFERZXRPVIAXRVJYIUBFYGYIXNFRZXNYGRZYIYLSZXNWSRZXPSYMYNYOX
        PYIFWSXNAFWSUFXRXJVIVKYNXOXNXMVFZGXNXMVOYNXMWSRZYPGRZYNXMXNYBVFZGRZQWSU
        PZRYQYRSYNGUUAXMYNBCDXNEFGHIJKQLMAYJXRYLNVLOAYKXRYLPVLYIYLVJVMAXRYLVNVP
        YTYRQXMWSYBXMVDYSYPGYBXMXNVQVRVSVTWAWBWCYDXPQXNWSYBXNVDYCXOGYBXNXMVQVRZ
        VSWDWFWEWGWHYDQWSGWIVTWAYDXPQXNGUUBWJWPWKAGHRXQXLWQXKUAUBGHWLWMWNXBGWOW
        MWCEGIKLWRWD $.
    $}

    $d L s u v $.  $d O v y $.  $d S v $.  $d T v y $.  $d V x $.  $d ph v y $.
    $d t v x $.
    dynkin.1 $e |- ( ph -> S e. L ) $.
    dynkin.2 $e |- ( ph -> T e. P ) $.
    dynkin.3 $e |- ( ph -> T C_ S ) $.
    $( Dynkin's lambda-pi theorem: if a lambda-system contains a pi-system, it
       also contains the sigma-algebra generated by that pi-system.
       (Contributed by Thierry Arnoux, 16-Jun-2020.) $)
    dynkin $p |- ( ph -> |^| { u e. ( sigAlgebra ` O ) | T C_ u } C_ S ) $=
      ( vv wss wcel vt cv csiga cfv crab cint cin cbvrabv inteqi ldgenpisys cpw
      sseq2 cfn c0 csn cdif wral ispisys2 simplbi elpwid ldsysgenld sigapildsys
      syl elind eleqtrrdi ssintub a1i intminss syl2anc sstrd ) AGDUBZSZDIUCUDZU
      EUFZGRUBZSZRHUEZUFZFAVRVMTGVRSZVNVRSAVREHUGVMAEHVRABCUAEGVRHIJKLMNVQGUAUB
      ZSZUAHUEVPWARUAHVOVTGULUHUIPUJABCRGHIJKMNAGIUKZAGETZGWBUKTZPWCWDBUBUFGTBG
      UKUMUGUNUOUPUQBEGIKLURUSVCUTVAVDBCEHIKLMVBVEVSARGHVFVGVLVSDVRVMVKVRGULVHV
      IAFHTGFSZVRFSOQVPWERFHVOFGULVHVIVJ $.
  $}

  ${
    $d A u v $.  $d B u v $.  $d O s $.  $d S s u v x y $.
    isros.1 $e |- Q = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s
      ( ( x u. y ) e. s /\ ( x \ y ) e. s ) ) } $.
    $( The property of being a rings of sets, i.e. containing the empty set,
       and closed under finite union and set complement.  (Contributed by
       Thierry Arnoux, 18-Jul-2020.) $)
    isros $p |- ( S e. Q <-> ( S e. ~P ~P O /\ (/) e. S /\ A. u e. S A. v e. S
      ( ( u u. v ) e. S /\ ( u \ v ) e. S ) ) ) $=
      ( wcel c0 cv cun cdif wa wral wceq eleq2 anbi12d eleq1d raleqbi1dv elrab2
      cpw w3a 3anass uneq1 difeq1 uneq2 difeq2 cbvral2vw 3anbi3i 3bitr2i ) FEJF
      GUCUCZJZKFJZALZBLZMZFJZUPUQNZFJZOZBFPZAFPZOZOUNUOVDUDUNUODLZCLZMZFJZVFVGN
      ZFJZOZCFPDFPZUDKHLZJZURVNJZUTVNJZOZBVNPZAVNPZOVEHFUMEVNFQZVOUOVTVDVNFKRVS
      VCAVNFVRVBBVNFWAVPUSVQVAVNFURRVNFUTRSUAUASIUBUNUOVDUEVDVMUNUOVBVLVFUQMZFJ
      ZVFUQNZFJZOABDCFFUPVFQZUSWCVAWEWFURWBFUPVFUQUFTWFUTWDFUPVFUQUGTSUQVGQZWCV
      IWEVKWGWBVHFUQVGVFUHTWGWDVJFUQVGVFUITSUJUKUL $.

    $( A ring of sets is a collection of subsets of ` O ` .  (Contributed by
       Thierry Arnoux, 18-Jul-2020.) $)
    rossspw $p |- ( S e. Q -> S C_ ~P O ) $=
      ( vu vv wcel cpw c0 cv cun cdif wa wral isros simp1bi elpwid ) DCJZDEKZUA
      DUBKJLDJHMZIMZNDJUCUDODJPIDQHDQABIHCDEFGRST $.

    $( A ring of sets contains the empty set.  (Contributed by Thierry Arnoux,
       18-Jul-2020.) $)
    0elros $p |- ( S e. Q -> (/) e. S ) $=
      ( vu vv wcel cpw c0 cv cun cdif wa wral isros simp2bi ) DCJDEKKJLDJHMZIMZ
      NDJTUAODJPIDQHDQABIHCDEFGRS $.

    $( A ring of sets is closed under union.  (Contributed by Thierry Arnoux,
       18-Jul-2020.) $)
    unelros $p |- ( ( S e. Q /\ A e. S /\ B e. S ) -> ( A u. B ) e. S ) $=
      ( vu vv wcel cun cdif cv wa wral cpw wceq eleq1d w3a simp2 simp3 c0 isros
      simp3bi 3ad2ant1 uneq1 difeq1 anbi12d difeq2 rspc2va syl21anc simpld
      uneq2 ) FELZCFLZDFLZUAZCDMZFLZCDNZFLZUSUQURJOZKOZMZFLZVDVENZFLZPZKFQJFQZV
      AVCPZUPUQURUBUPUQURUCUPUQVKURUPFGRRLUDFLVKABKJEFGHIUEUFUGVJVLCVEMZFLZCVEN
      ZFLZPJKCDFFVDCSZVGVNVIVPVQVFVMFVDCVEUHTVQVHVOFVDCVEUITUJVEDSZVNVAVPVCVRVM
      UTFVEDCUOTVRVOVBFVEDCUKTUJULUMUN $.

    $( A ring of sets is closed under set complement.  (Contributed by Thierry
       Arnoux, 18-Jul-2020.) $)
    difelros $p |- ( ( S e. Q /\ A e. S /\ B e. S ) -> ( A \ B ) e. S ) $=
      ( vu vv wcel cun cdif cv wa wral cpw wceq eleq1d w3a simp2 simp3 c0 isros
      simp3bi 3ad2ant1 uneq1 difeq1 anbi12d difeq2 rspc2va syl21anc simprd
      uneq2 ) FELZCFLZDFLZUAZCDMZFLZCDNZFLZUSUQURJOZKOZMZFLZVDVENZFLZPZKFQJFQZV
      AVCPZUPUQURUBUPUQURUCUPUQVKURUPFGRRLUDFLVKABKJEFGHIUEUFUGVJVLCVEMZFLZCVEN
      ZFLZPJKCDFFVDCSZVGVNVIVPVQVFVMFVDCVEUHTVQVHVOFVDCVEUITUJVEDSZVNVAVPVCVRVM
      UTFVEDCUOTVRVOVBFVEDCUKTUJULUMUN $.

    $( A ring of sets is closed under intersection.  (Contributed by Thierry
       Arnoux, 19-Jul-2020.) $)
    inelros $p |- ( ( S e. Q /\ A e. S /\ B e. S ) -> ( A i^i B ) e. S ) $=
      ( wcel w3a cin cdif dfin4 difelros syld3an3 eqeltrid ) FEJZCFJZDFJZKCDLCC
      DMZMZFCDNRSTUAFJUBFJABCDEFGHIOABCUAEFGHIOPQ $.

    ${
      $d B i n $.  $d N i k n $.  $d S i k n $.  $d ph i k n $.
      fiunelros.1 $e |- ( ph -> S e. Q ) $.
      fiunelros.2 $e |- ( ph -> N e. NN ) $.
      fiunelros.3 $e |- ( ( ph /\ k e. ( 1 ..^ N ) ) -> B e. S ) $.
      $( A ring of sets is closed under finite union.  (Contributed by Thierry
         Arnoux, 19-Jul-2020.) $)
      fiunelros $p |- ( ph -> U_ k e. ( 1 ..^ N ) B e. S ) $=
        ( wcel c1 cfzo ciun cle wceq vn vi cn co wa wbr simpr nnred leidd cv wi
        caddc breq1 oveq2 iuneq1d eleq1d imbi12d fzo0 iuneq1 ax-mp eqtri 0elros
        c0 0iun syl eqeltrid a1d csn cun simpllr cuz cfv fzosplitsn nnuz eleq2s
        iunxun eqtrdi ad3antrrr clt wb nnltp1le syl2anc mpbird ltled simplr mpd
        nfcsb1v csbeq1a iunxsngf simplll elfzo1 syl3anbrc nfcv nfel nfim eleq1w
        csb nfv anbi2d chvarfv eqeltrd unelros syl3anc ex nnindd mpdan ) AHUCOZ
        GPHQUDZDRZFOZMAXGUEZHHSUFZXJXKHXKHAXGUGUHUIAUAUJZHSUFZGPXMQUDZDRZFOZUKP
        HSUFZGPPQUDZDRZFOZUKUBUJZHSUFZGPYBQUDZDRZFOZUKZYBPULUDZHSUFZGPYHQUDZDRZ
        FOZUKXLXJUKUAUBHXMPTZXNXRXQYAXMPHSUMYMXPXTFYMGXOXSDXMPPQUNUOUPUQXMYBTZX
        NYCXQYFXMYBHSUMYNXPYEFYNGXOYDDXMYBPQUNUOUPUQXMYHTZXNYIXQYLXMYHHSUMYOXPY
        KFYOGXOYJDXMYHPQUNUOUPUQXMHTZXNXLXQXJXMHHSUMYPXPXIFYPGXOXHDXMHPQUNUOUPU
        QAYAXRAXTVCFXTGVCDRZVCXSVCTXTYQTPURGXSVCDUSUTGDVDVAAFEOZVCFOLBCEFIJKVBV
        EVFVGAYBUCOZUEZYGUEZYIYLUUAYIUEZYKYEGYBVHZDRZVIZFUUBYKGYDUUCVIZDRZUUEUU
        BYSYKUUGTAYSYGYIVJZYSGYJUUFDYJUUFTYBPVKVLUCPYBVMVNVOUOVEGYDUUCDVPVQUUBY
        RYFUUDFOUUEFOAYRYSYGYILVRUUBYCYFUUBYBHUUBYBUUHUHUUBHAXGYSYGYIMVRZUHUUBY
        BHVSUFZYIUUAYIUGUUBYSXGUUJYIVTUUHUUIYBHWAWBWCZWDYTYGYIWEWFUUBUUDGYBDWQZ
        FUUBYSUUDUULTUUHGYBDUULUCGYBDWGZGYBDWHZWIVEUUBAYBXHOZUULFOZAYSYGYIWJUUB
        YSXGUUJUUOUUHUUIUUKHYBWKWLAGUJZXHOZUEZDFOZUKAUUOUEZUUPUKGUBUVAUUPGUVAGW
        RGUULFUUMGFWMWNWOUUQYBTZUUSUVAUUTUUPUVBUURUUOAGUBXHWPWSUVBDUULFUUNUPUQN
        WTWBXABCYEUUDEFIJKXBXCXAXDXEWFXF $.
    $}
  $}

  ${
    $d s t x y $.  $d O s $.  $d S s x y z $.  $d A x y z $.  $d B y z $.
    issros.1 $e |- N = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s
      ( ( x i^i y ) e. s /\ E. z e. ~P s ( z e. Fin /\ Disj_ t e. z t
      /\ ( x \ y ) = U. z ) ) ) } $.
    $( The property of being a semirings of sets, i.e., collections of sets
       containing the empty set, closed under finite intersection, and where
       complements can be written as finite disjoint unions.  (Contributed by
       Thierry Arnoux, 18-Jul-2020.) $)
    issros $p |- ( S e. N <-> ( S e. ~P ~P O /\ (/) e. S /\ A. x e. S A. y e. S
      ( ( x i^i y ) e. S /\ E. z e. ~P S ( z e. Fin /\ Disj_ t e. z t
      /\ ( x \ y ) = U. z ) ) ) ) $=
      ( wcel cpw c0 cv wceq w3a wrex wa wral eleq2 anbi12d wdisj cdif cuni pweq
      cin cfn rexeqdv raleqbi1dv elrab2 3anass bitr4i ) EFJEGKKZJZLEJZAMZBMZUEZ
      EJZCMZUFJDUSDMUAUOUPUBUSUCNOZCEKZPZQZBERZAERZQZQUMUNVEOLHMZJZUQVGJZUTCVGK
      ZPZQZBVGRZAVGRZQVFHEULFVGENZVHUNVNVEVGELSVMVDAVGEVLVCBVGEVOVIURVKVBVGEUQS
      VOUTCVJVAVGEUDUGTUHUHTIUIUMUNVEUJUK $.

    $( A semiring of sets is a collection of subsets of ` O ` .  (Contributed
       by Thierry Arnoux, 18-Jul-2020.) $)
    srossspw $p |- ( S e. N -> S C_ ~P O ) $=
      ( wcel cpw c0 cv cin cfn wdisj cdif cuni wceq wral wrex wa issros simp1bi
      w3a elpwid ) EFJZEGKZUGEUHKJLEJAMZBMZNEJCMZOJDUKDMPUIUJQUKRSUECEKUAUBBETA
      ETABCDEFGHIUCUDUF $.

    $( A semiring of sets contains the empty set.  (Contributed by Thierry
       Arnoux, 18-Jul-2020.) $)
    0elsros $p |- ( S e. N -> (/) e. S ) $=
      ( wcel cpw c0 cv cin cfn wdisj cdif cuni wceq wral wrex wa issros simp2bi
      w3a ) EFJEGKKJLEJAMZBMZNEJCMZOJDUHDMPUFUGQUHRSUECEKUAUBBETAETABCDEFGHIUCU
      D $.

    $( A semiring of sets is closed under union.  (Contributed by Thierry
       Arnoux, 18-Jul-2020.) $)
    inelsros $p |- ( ( S e. N /\ A e. S /\ B e. S ) -> ( A i^i B ) e. S ) $=
      ( wcel w3a cin cv cdif wceq cpw wrex wa cfn wdisj cuni simp2 simp3 issros
      wral c0 simp3bi 3ad2ant1 ineq1 eleq1d difeq1 eqeq1d 3anbi3d rexbidv ineq2
      anbi12d difeq2 rspc2va syl21anc simpld ) GHLZEGLZFGLZMZEFNZGLZCOZUALZDVID
      OUBZEFPZVIUCZQZMZCGRZSZVFVDVEAOZBOZNZGLZVJVKVRVSPZVMQZMZCVPSZTZBGUGAGUGZV
      HVQTZVCVDVEUDVCVDVEUEVCVDWGVEVCGIRRLUHGLWGABCDGHIJKUFUIUJWFWHEVSNZGLZVJVK
      EVSPZVMQZMZCVPSZTABEFGGVREQZWAWJWEWNWOVTWIGVREVSUKULWOWDWMCVPWOWCWLVJVKWO
      WBWKVMVREVSUMUNUOUPURVSFQZWJVHWNVQWPWIVGGVSFEUQULWPWMVOCVPWPWLVNVJVKWPWKV
      LVMVSFEUSUNUOUPURUTVAVB $.

    $( In semiring of sets, complements can be written as finite disjoint
       unions.  (Contributed by Thierry Arnoux, 18-Jul-2020.) $)
    diffiunisros $p |- ( ( S e. N /\ A e. S /\ B e. S )
      -> E. z e. ~P S ( z e. Fin /\ Disj_ t e. z t /\ ( A \ B ) = U. z ) ) $=
      ( wcel w3a cin cv cdif wceq cpw wrex wa cfn wdisj cuni simp2 simp3 issros
      wral c0 simp3bi 3ad2ant1 ineq1 eleq1d difeq1 eqeq1d 3anbi3d rexbidv ineq2
      anbi12d difeq2 rspc2va syl21anc simprd ) GHLZEGLZFGLZMZEFNZGLZCOZUALZDVID
      OUBZEFPZVIUCZQZMZCGRZSZVFVDVEAOZBOZNZGLZVJVKVRVSPZVMQZMZCVPSZTZBGUGAGUGZV
      HVQTZVCVDVEUDVCVDVEUEVCVDWGVEVCGIRRLUHGLWGABCDGHIJKUFUIUJWFWHEVSNZGLZVJVK
      EVSPZVMQZMZCVPSZTABEFGGVREQZWAWJWEWNWOVTWIGVREVSUKULWOWDWMCVPWOWCWLVJVKWO
      WBWKVMVREVSUMUNUOUPURVSFQZWJVHWNVQWPWIVGGVSFEUQULWPWMVOCVPWPWLVNVJVKWPWKV
      LVMVSFEUSUNUOUPURUTVAVB $.
  $}

  ${
    $d O s $.  $d Q x y $.  $d S s u v x y z $.  $d s t x y z $.
    rossros.q $e |- Q = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s
      ( ( x u. y ) e. s /\ ( x \ y ) e. s ) ) } $.
    rossros.n $e |- N = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s
      ( ( x i^i y ) e. s /\ E. z e. ~P s ( z e. Fin /\ Disj_ t e. z t
      /\ ( x \ y ) = U. z ) ) ) } $.
    $( Rings of sets are semirings of sets.  (Contributed by Thierry Arnoux,
       18-Jul-2020.) $)
    rossros $p |- ( S e. Q -> S e. N ) $=
      ( vu vv wcel cpw cv wceq wa wral eleq1d c0 cin cfn cdif cuni w3a wrex wss
      wdisj rossspw elpwg mpbird 0elros cun crab uneq1 difeq1 anbi12d cbvral2vw
      uneq2 difeq2 anbi2i rabbii eqtr4i inelros 3expb csn difelros snssd sylibr
      snex elpw snfi a1i disjxsn unisng syl eqcomd eleq1 unieq eqeq2d 3anbi123d
      disjeq1 rspcev syl13anc jca ralrimivva 3jca issros ) FENZFHOZOZNZUAFNZAPZ
      BPZUBFNZCPZUCNZDWRDPZUIZWOWPUDZWRUEZQZUFZCFOZUGZRZBFSAFSZUFFGNWJWMWNXIWJW
      MFWKUHABEFHIJUJFWKEUKULABEFHIJUMWJXHABFFWJWOFNZWPFNZRRZWQXGWJXJXKWQLMWOWP
      EFHIEUAIPZNZWOWPUNZXMNZXBXMNZRZBXMSAXMSZRZIWLUOXNLPZMPZUNZXMNZYAYBUDZXMNZ
      RZMXMSLXMSZRZIWLUOJYIXTIWLYHXSXNYGXRWOYBUNZXMNZWOYBUDZXMNZRLMABXMXMYAWOQZ
      YDYKYFYMYNYCYJXMYAWOYBUPTYNYEYLXMYAWOYBUQTURYBWPQZYKXPYMXQYOYJXOXMYBWPWOU
      TTYOYLXBXMYBWPWOVATURUSVBVCVDZVEVFXLXBVGZXFNZYQUCNZDYQWTUIZXBYQUEZQZXGXLY
      QFUHYRXLXBFWJXJXKXBFNZLMWOWPEFHIYPVHVFZVIYQFXBVKVLVJYSXLXBVMVNYTXLDXBWTVO
      VNXLUUAXBXLUUCUUAXBQUUDXBFVPVQVRXEYSYTUUBUFCYQXFWRYQQZWSYSXAYTXDUUBWRYQUC
      VSDWRYQWTWCUUEXCUUAXBWRYQVTWAWBWDWEWFWGWHABCDFGHIKWIVJ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The Borel algebra on the real numbers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c BrSiga $.
  $( The Borel Algebra on real numbers, usually a gothic B $)
  cbrsiga $a class BrSiga $. $( Extend class notation with the Borel Algebra $)

  $( A Borel Algebra is defined as a sigma-algebra generated by a topology.
     'The' Borel sigma-algebra here refers to the sigma-algebra generated by
     the topology of open intervals on real numbers.  The Borel algebra of a
     given topology ` J ` is the sigma-algebra generated by ` J ` ,
     ` ( sigaGen `` J ) ` , so there is no need to introduce a special constant
     function for Borel sigma-algebra.  (Contributed by Thierry Arnoux,
     27-Dec-2016.) $)
  df-brsiga $a |- BrSiga = ( sigaGen ` ( topGen ` ran (,) ) ) $.

  ${
    $d s x $.
    $( The Borel Algebra on real numbers is a Borel sigma-algebra.
       (Contributed by Thierry Arnoux, 27-Dec-2016.) $)
    brsiga $p |- BrSiga e. ( sigaGen " Top ) $=
      ( vx vs cbrsiga cioo crn ctg csigagen ctop cima df-brsiga wcel retop wfun
      cfv cvv cv cuni csiga c0 mp2b cdm wi wss crab cint df-sigagen sigagensiga
      funmpt2 fvex elrnsiga 0elsiga elfvdm funfvima mp2an ax-mp eqeltri ) CDEZF
      NZGNZGHIZJURHKZUSUTKZLGMURGUAKZVAVBUBAOAPZBPUCBVDQRNUDUEGABUFUHUSREQKZSUS
      KVCUROKUSURQZRNKVEUQFUIUROUGUSVFUJTUSUKSURGULTHURGUMUNUOUP $.
  $}

  $( The Borel Algebra is a sigma-algebra on the real numbers.  (Contributed by
     Thierry Arnoux, 27-Dec-2016.) $)
  brsigarn $p |- BrSiga e. ( sigAlgebra ` RR ) $=
    ( cioo crn ctg cfv csigagen cuni csiga cbrsiga cr cvv wcel fvex sigagensiga
    ax-mp df-brsiga uniretop fveq2i 3eltr4i ) ABZCDZEDZTFZGDZHIGDTJKUAUCKSCLTJM
    NOIUBGPQR $.

  $( The Borel Algebra is a set of subsets of the real numbers.  (Contributed
     by Thierry Arnoux, 19-Jan-2017.) $)
  brsigasspwrn $p |- BrSiga C_ ~P RR $=
    ( cbrsiga cr csiga cfv wcel cpw wss brsigarn sigasspw ax-mp ) ABCDEABFGHBAI
    J $.

  $( The union of the Borel Algebra is the set of real numbers.  (Contributed
     by Thierry Arnoux, 21-Jan-2017.) $)
  unibrsiga $p |- U. BrSiga = RR $=
    ( cioo crn ctg cfv csigagen cuni cbrsiga cr ctop wcel retop unisg df-brsiga
    wceq ax-mp unieqi uniretop 3eqtr4i ) ABCDZEDZFZSFZGFHSIJUAUBNKSILOGTMPQR $.

  ${
    $d x J $.
    $( A Borel Algebra contains all closed sets of its base topology.
       (Contributed by Thierry Arnoux, 27-Mar-2017.) $)
    cldssbrsiga $p |- ( J e. Top -> ( Clsd ` J ) C_ ( sigaGen ` J ) ) $=
      ( vx ctop wcel ccld cfv csigagen cv cuni cdif wss wceq cldss adantl dfss4
      wa eqid csiga adantr cvv sylib topopn difopn sylan crn sgsiga sigagensiga
      id elex baselsiga 3syl elsigagen difelsiga syl3anc syldan eqeltrrd ssrdv
      ex ) ACDZBAEFZAGFZUSBHZUTDZVBVADUSVCPZAIZVEVBJZJZVBVAVDVBVEKZVGVBLVCVHUSV
      BAVEVEQZMNVBVEOUAUSVCVFADZVGVADZUSVEADVCVJAVEVIUBVEVBAVEVIUCUDUSVJPVARUEI
      DZVEVADZVFVADVKUSVLVJUSACUSUHUFSUSVMVJUSATDVAVERFDVMACUIATUGVEVAUJUKSAVFC
      ULVEVFVAUMUNUOUPURUQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Product Sigma-Algebra
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c sX $.

  $( Extend class notation with the product sigma-algebra operation. $)
  csx $a class sX $. $( Circled times operator $)

  ${
    $d s t x y $.
    $( Define the product sigma-algebra operation, analogous to ~ df-tx .
       (Contributed by Thierry Arnoux, 1-Jun-2017.) $)
    df-sx $a |- sX = ( s e. _V , t e. _V |->
             ( sigaGen ` ran ( x e. s , y e. t |-> ( x X. y ) ) ) ) $.
  $}

  ${
    $d s t x y S $.  $d s t x y T $.
    sxval.1 $e |- A = ran ( x e. S , y e. T |-> ( x X. y ) ) $.
    $( Value of the product sigma-algebra operation.  (Contributed by Thierry
       Arnoux, 1-Jun-2017.) $)
    sxval $p |- ( ( S e. V /\ T e. W ) -> ( S sX T ) = ( sigaGen ` A ) ) $=
      ( vs vt wcel csx cv cmpo crn csigagen cfv cvv wceq eqidd wa co mpoeq123dv
      cxp elex id rneqd fveq2d df-sx fvex ovmpo syl2an fveq2i eqtr4di ) DFKZEGK
      ZUADELUBZABDEAMBMUDZNZOZPQZCPQUODRKERKUQVASUPDFUEEGUEIJDERRABIMZJMZURNZOZ
      PQVALABDVCURNZOZPQVBDSZVEVGPVHVDVFVHABVBVCURDVCURVHUFVHVCTVHURTUCUGUHVCES
      ZVGUTPVIVFUSVIABDVCURDEURVIDTVIUFVIURTUCUGUHABJIUIUTPUJUKULCUTPHUMUN $.
  $}

  ${
    $d x y S $.  $d x y T $.
    $( A product sigma-algebra is a sigma-algebra.  (Contributed by Thierry
       Arnoux, 1-Jun-2017.) $)
    sxsiga $p |- ( ( S e. U. ran sigAlgebra /\ T e. U. ran sigAlgebra ) ->
      ( S sX T ) e. U. ran sigAlgebra ) $=
      ( vx vy csiga crn cuni wcel wa csx co cv cxp cmpo cfv csigagen eqid sxval
      cvv syl txbasex sigagensiga eqeltrd elrnsiga ) AEFGZHBUEHIZABJKZCDABCLDLM
      NFZGZEOZHUGUEHUFUGUHPOZUJCDUHABUEUEUHQZRUFUHSHUKUJHCDUHABUEUEULUAUHSUBTUC
      UGUIUDT $.

    $( A product sigma-algebra is a sigma-algebra on the product of the bases.
       (Contributed by Thierry Arnoux, 1-Jun-2017.) $)
    sxsigon $p |- ( ( S e. U. ran sigAlgebra /\ T e. U. ran sigAlgebra ) ->
      ( S sX T ) e. ( sigAlgebra ` ( U. S X. U. T ) ) ) $=
      ( vx vy csiga crn cuni wcel wa csx co cxp wceq sxsiga cv cmpo eqid txuni2
      cfv cvv csigagen sxval unieqd mpoexga rnexg unisg eqtr4id issgon sylanbrc
      3syl eqtrd ) AEFGZHBULHIZABJKZULHAGZBGZLZUNGZMUNUQESHABNUMUQCDABCODOLZPZF
      ZGZURCDVAABUOUPVAQZUOQUPQRUMURVAUASZGZVBUMUNVDCDVAABULULVCUBUCUMUTTHVATHV
      EVBMCDABUSULULUDUTTUEVATUFUJUKUGUNUQUHUI $.
  $}

  $( The base set of a product sigma-algebra.  (Contributed by Thierry Arnoux,
     1-Jun-2017.) $)
  sxuni $p |- ( ( S e. U. ran sigAlgebra /\ T e. U. ran sigAlgebra ) ->
    ( U. S X. U. T ) = U. ( S sX T ) ) $=
    ( csiga crn cuni wcel wa csx co cxp cfv wceq sxsigon issgon simprbi syl ) A
    CDEZFBQFGABHIZAEBEJZCKFZSRELZABMTRQFUARSNOP $.

  ${
    $d x y A $.  $d x y B $.  $d x y S $.  $d x y T $.
    $( The cartesian product of two open sets is an element of the product
       sigma-algebra.  (Contributed by Thierry Arnoux, 3-Jun-2017.) $)
    elsx $p |- ( ( ( S e. V /\ T e. W ) /\ ( A e. S /\ B e. T ) )
                                               -> ( A X. B ) e. ( S sX T ) ) $=
      ( vx vy wcel wa cxp cv cmpo cvv eqid syl adantr wceq wrex eqeq2d csigagen
      crn cfv csx co wss txbasex sssigagen xpeq1 xpeq2 mp3an3 wb xpexg elrnmpog
      rspc2ev mpbird adantl sseldd sxval eleqtrrd ) CEIDFIJZACIZBDIZJZJZABKZGHC
      DGLZHLZKZMZUBZUAUCZCDUDUEZVEVKVLVFVAVKVLUFZVDVAVKNIVNGHVKCDEFVKOZUGVKNUHP
      QVDVFVKIZVAVDVPVFVIRZHDSGCSZVBVCVFVFRZVRVFOVQVSVFAVHKZRGHABCDVGARVIVTVFVG
      AVHUITVHBRVTVFVFVHBAUJTUOUKVDVFNIVPVRULABCDUMGHCDVIVFVJNVJOUNPUPUQURVAVMV
      LRVDGHVKCDEFVOUSQUT $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Measures
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c measures $. $( The class of the measures on a sigma-algebra $)

  $( Extend class notation to include the class of measures. $)
  cmeas $a class measures $.

  ${
    $d m x y $.  $d m s x S $.  $d s y $.
    $( Define a measure as a nonnegative countably additive function over a
       sigma-algebra onto ` ( 0 [,] +oo ) ` .  (Contributed by Thierry Arnoux,
       10-Sep-2016.) $)
    df-meas $a |- measures = ( s e. U. ran sigAlgebra |->
      { m | ( m : s --> ( 0 [,] +oo ) /\ ( m ` (/) ) = 0
      /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y )
      -> ( m ` U. x ) = sum* y e. x ( m ` y ) ) ) } ) $.

    $( The base set of a measure is a sigma-algebra.  (Contributed by Thierry
       Arnoux, 25-Dec-2016.) $)
    measbase $p |- ( M e. ( measures ` S ) -> S e. U. ran sigAlgebra ) $=
      ( vs vm vx vy cmeas cfv wcel cdm csiga crn cuni cv cc0 cpnf cicc wceq cab
      cvv elfvdm co wf c0 com cdom wbr wdisj wa cesum wi cpw wral w3a vex mapex
      ovex mp2an simp1 ss2abi ssexi df-meas dmmpti eleqtrdi ) BAGHIAGJKLMZBAGUA
      CVECNZOPQUBZDNZUCZUDVHHORZENZUEUFUGFVKFNZUHUIVKMVHHVKVLVHHFUJRUKEVFULUMZU
      NZDSZGVOVIDSZVFTIVGTIVPTICUOOPQUQVFVGTTDUPURVNVIDVIVJVMUSUTVAEFDCVBVCVD
      $.

    $( The value of the ` measures ` function applied on a sigma-algebra.
       (Contributed by Thierry Arnoux, 17-Oct-2016.) $)
    measval $p |- ( S e. U. ran sigAlgebra -> ( measures ` S ) =
      { m | ( m : S --> ( 0 [,] +oo ) /\ ( m ` (/) ) = 0
      /\ A. x e. ~P S ( ( x ~<_ _om /\ Disj_ y e. x y )
      -> ( m ` U. x ) = sum* y e. x ( m ` y ) ) ) } ) $=
      ( vs cuni wcel cc0 cpnf cicc cv wf cfv wceq cpw wral w3a cab cvv cmeas co
      csiga crn c0 com cdom wbr wdisj wa cesum wi simp1 ss2abi ovex mapex mpan2
      wss ssexg sylancr feq2 pweq raleqdv 3anbi13d abbidv df-meas fvmptg mpdan
      ) CUBUCFZGZCHIJUAZDKZLZUDVKMHNZAKZUEUFUGBVNBKZUHUIVNFVKMVNVOVKMBUJNUKZACO
      ZPZQZDRZSGZCTMVTNVIVTVLDRZUQWBSGZWAVSVLDVLVMVRULUMVIVJSGWCHIJUNCVJVHSDUOU
      PVTWBSURUSECEKZVJVKLZVMVPAWDOZPZQZDRVTVHSTWDCNZWHVSDWIWEVLWGVRVMWDCVJVKUT
      WIVPAWFVQWDCVAVBVCVDABDEVEVFVG $.
  $}

  ${
    $d x y m s M $.  $d x m s S $.
    $( The property of being a measure.  (Contributed by Thierry Arnoux,
       10-Sep-2016.)  (Revised by Thierry Arnoux, 19-Oct-2016.) $)
    ismeas $p |- ( S e. U. ran sigAlgebra -> ( M e. ( measures ` S ) <-> (
      M : S --> ( 0 [,] +oo ) /\ ( M ` (/) ) = 0
      /\ A. x e. ~P S ( ( x ~<_ _om /\ Disj_ y e. x y )
      -> ( M ` U. x ) = sum* y e. x ( M ` y ) ) ) ) ) $=
      ( vs vm cuni wcel cvv cmeas cfv cc0 cpnf c0 wceq cv wa wi wb fveq1 crn co
      csiga cicc com cdom wbr wdisj cesum cpw wral w3a elex a1i simp1 ovex fex2
      wf 3expb expcom mpan2 syl5 df-meas cab vex mapex mp2an ss2abi ssexi simpr
      simpl feq12d eqeq1d adantl esumeq2sdv eqeq12d raleqbidv 3anbi123d abfmpel
      pweqd imbi2d ex pm5.21ndd ) CUCUAGZHZDIHZDCJKZHZCLMUDUBZDURZNDKZLOZAPZUEU
      FUGBWMBPZUHQZWMGZDKZWMWNDKZBUIZOZRZACUJZUKZULZWHWFRWEDWGUMUNXDWJWEWFWJWLX
      CUOWEWIIHZWJWFRLMUDUPZWJWEXEQWFWJWEXEWFCWIDWDIUQUSUTVAVBWEWFWHXDSEPZWIFPZ
      URZNXHKZLOZWOWPXHKZWMWNXHKZBUIZOZRZAXGUJZUKZULZXDEFCDJWDIABFEVCXSFVDXIFVD
      ZXGIHXEXTIHEVEXFXGWIIIFVFVGXSXIFXIXKXRUOVHVIXGCOZXHDOZQZXIWJXKWLXRXCYCXGC
      WIXHDYAYBVJYAYBVKZVLYBXKWLSYAYBXJWKLNXHDTVMVNYCXPXAAXQXBYCXGCYDVTYBXPXASY
      AYBXOWTWOYBXLWQXNWSWPXHDTYBWMXMWRBWNXHDTVOVPWAVNVQVRVSWBWC $.
  $}

  ${
    $d m s x y M $.
    $( The property of being a measure on an undefined base sigma-algebra.
       (Contributed by Thierry Arnoux, 25-Dec-2016.) $)
    isrnmeas $p |- ( M e. U. ran measures
      -> ( dom M e. U. ran sigAlgebra /\ ( M : dom M --> ( 0 [,] +oo )
      /\ ( M ` (/) ) = 0 /\ A. x e. ~P dom M ( ( x ~<_ _om /\ Disj_ y e. x y )
      -> ( M ` U. x ) = sum* y e. x ( M ` y ) ) ) ) ) $=
      ( vs vm cmeas crn cuni wcel cv cc0 wf c0 cfv wceq wa wral w3a cvv fveq1
      cpnf cicc co com cdom wbr wdisj cesum cpw csiga wrex cdm df-meas cab ovex
      vex mapex mp2an simp1 ss2abi ssexi feq1 eqeq1d esumeq2sdv eqeq12d ralbidv
      wi imbi2d 3anbi123d abfmpunirn simprbi 3ad2ant1 adantl simpl eqeltrd feq2
      fdm biimpar syl2anc simp2 simp3 pweq raleqdv 3jca jca rexlimiva syl ) CFG
      HIZDJZKUAUBUCZCLZMCNZKOZAJZUDUEUFBWNBJZUGPZWNHZCNZWNWOCNZBUHZOZVGZAWIUIZQ
      ZRZDUJGHZUKZCULZXFIZXHWJCLZWMXBAXHUIZQZRZPZWHCSIXGWIWJEJZLZMXONZKOZWPWQXO
      NZWNWOXONZBUHZOZVGZAXCQZRZXEDECFXFABEDUMYEEUNXPEUNZWISIWJSIYFSIDUPKUAUBUO
      WIWJSSEUQURYEXPEXPXRYDUSUTVAXOCOZXPWKXRWMYDXDWIWJXOCVBYGXQWLKMXOCTVCYGYCX
      BAXCYGYBXAWPYGXSWRYAWTWQXOCTYGWNXTWSBWOXOCTVDVEVHVFVIVJVKXEXNDXFWIXFIZXEP
      ZXIXMYIXHWIXFXEXHWIOZYHWKWMYJXDWIWJCVQVLZVMYHXEVNVOXEXMYHXEXJWMXLXEYJWKXJ
      YKWKWMXDUSYJXJWKXHWIWJCVPVRVSWKWMXDVTXEYJXDXLYKWKWMXDWAYJXLXDYJXBAXKXCXHW
      IWBWCVRVSWDVMWEWFWG $.
  $}

  ${
    $d x y M $.
    $( The domain of a measure is a sigma-algebra.  (Contributed by Thierry
       Arnoux, 19-Feb-2018.) $)
    dmmeas $p |- ( M e. U. ran measures -> dom M e. U. ran sigAlgebra ) $=
      ( vx vy cmeas crn cuni wcel cdm csiga cc0 cpnf cicc co wf c0 cfv wceq com
      cv cdom wbr wdisj wa cesum wi cpw wral w3a isrnmeas simpld ) ADEFGAHZIEFG
      UKJKLMANOAPJQBSZRTUACULCSZUBUCULFAPULUMAPCUDQUEBUKUFUGUHBCAUIUJ $.

    $( The base set of a measure is its domain.  (Contributed by Thierry
       Arnoux, 25-Dec-2016.) $)
    measbasedom $p |- ( M e. U. ran measures <-> M e. ( measures ` dom M ) ) $=
      ( vx vy cmeas crn cuni wcel cdm cfv cc0 cpnf cicc co wf wceq com cdom wbr
      c0 cv wdisj wa cesum cpw wral w3a csiga isrnmeas simprd dmmeas ismeas syl
      wi wb mpbird elfvunirn impbii ) ADEFGZAAHZDIGZURUTUSJKLMANSAIJOBTZPQRCVAC
      TZUAUBVAFAIVAVBAICUCOUMBUSUDUEUFZURUSUGEFGZVCBCAUHUIURVDUTVCUNAUJBCUSAUKU
      LUOUSADUPUQ $.
  $}

  ${
    $d x y M $.  $d y S $.
    $( A measure is a function over its base to the positive extended reals.
       (Contributed by Thierry Arnoux, 26-Dec-2016.) $)
    measfrge0 $p |- ( M e. ( measures ` S ) -> M : S --> ( 0 [,] +oo ) ) $=
      ( vy vx cmeas cfv wcel cc0 cpnf cicc co wf c0 wceq cv com cdom wdisj cuni
      wbr wa cesum wi cpw wral w3a csiga crn wb measbase ismeas syl ibi simp1d
      ) BAEFGZAHIJKBLZMBFHNZCOZPQTDURDOZRUAURSBFURUSBFDUBNUCCAUDUEZUOUPUQUTUFZU
      OAUGUHSGUOVAUIABUJCDABUKULUMUN $.
  $}

  $( A measure is a function on its base sigma-algebra.  (Contributed by
     Thierry Arnoux, 13-Feb-2017.) $)
  measfn $p |- ( M e. ( measures ` S ) -> M Fn S ) $=
    ( cmeas cfv wcel cc0 cpnf cicc co measfrge0 ffnd ) BACDEAFGHIBABJK $.

  $( The values of a measure are positive extended reals.  (Contributed by
     Thierry Arnoux, 26-Dec-2016.) $)
  measvxrge0 $p |- ( ( M e. ( measures ` S ) /\ A e. S ) ->
    ( M ` A ) e. ( 0 [,] +oo ) ) $=
    ( cmeas cfv wcel cc0 cpnf cicc co measfrge0 ffvelcdmda ) CBDEFBGHIJACBCKL
    $.

  ${
    $d x y M $.  $d y S $.
    $( The measure of the empty set is always zero.  (Contributed by Thierry
       Arnoux, 26-Dec-2016.) $)
    measvnul $p |- ( M e. ( measures ` S ) -> ( M ` (/) ) = 0 ) $=
      ( vy vx cmeas cfv wcel cc0 cpnf cicc co wf c0 wceq cv com cdom wdisj cuni
      wbr wa cesum wi cpw wral w3a csiga crn wb measbase ismeas syl ibi simp2d
      ) BAEFGZAHIJKBLZMBFHNZCOZPQTDURDOZRUAURSBFURUSBFDUBNUCCAUDUEZUOUPUQUTUFZU
      OAUGUHSGUOVAUIABUJCDABUKULUMUN $.
  $}

  $( A measure is nonnegative.  (Contributed by Thierry Arnoux, 9-Mar-2018.) $)
  measge0 $p |- ( ( M e. ( measures ` S ) /\ A e. S ) -> 0 <_ ( M ` A ) ) $=
    ( cmeas cfv wcel wa cxr cc0 cle wbr cpnf co measvxrge0 elxrge0 sylib simprd
    cicc ) CBDEFABFGZACEZHFZITJKZSTILRMFUAUBGABCNTOPQ $.

  $( If the measure of a given set is bounded by zero, it is zero.
     (Contributed by Thierry Arnoux, 20-Oct-2017.) $)
  measle0 $p |- ( ( M e. ( measures ` S ) /\ A e. S /\ ( M ` A ) <_ 0 )
    -> ( M ` A ) = 0 ) $=
    ( cmeas cfv wcel cc0 cle wbr w3a wceq simp3 wa cpnf cicc measvxrge0 elxrge0
    cxr co sylib 3adant3 simprd wb simpld 0xr xrletri3 sylancl mpbir2and ) CBDE
    FZABFZACEZGHIZJZUKGKZULGUKHIZUIUJULLUMUKRFZUOUIUJUPUOMZULUIUJMUKGNOSFUQABCP
    UKQTUAZUBUMUPGRFUNULUOMUCUMUPUOURUDUEUKGUFUGUH $.

  ${
    $d x y A $.  $d x y M $.  $d y S $.
    $( The measure of a countable disjoint union is the sum of the measures.
       (Contributed by Thierry Arnoux, 26-Dec-2016.) $)
    measvun $p |- ( ( M e. ( measures ` S ) /\ A e. ~P S /\
      ( A ~<_ _om /\ Disj_ x e. A x ) )
      -> ( M ` U. A ) = sum* x e. A ( M ` x ) ) $=
      ( vy cmeas cfv wcel com cdom wbr cv wdisj wa w3a cuni cesum wceq wi cc0
      cpw wral simp2 cpnf cicc co wf c0 csiga crn wb measbase ismeas syl simp3d
      3ad2ant1 simp3 breq1 disjeq1 anbi12d unieq fveq2d esumeq1 eqeq12d imbi12d
      ibi rspcv syl3c ) DCFGHZBCUAZHZBIJKZABALZMZNZOVKELZIJKZAVPVMMZNZVPPZDGZVP
      VMDGZAQZRZSZEVJUBZVOBPZDGZBWBAQZRZVIVKVOUCVIVKWFVOVICTUDUEUFDUGZUHDGTRZWF
      VIWKWLWFOZVICUIUJPHVIWMUKCDULEACDUMUNVFUOUPVIVKVOUQWEVOWJSEBVJVPBRZVSVOWD
      WJWNVQVLVRVNVPBIJURAVPBVMUSUTWNWAWHWCWIWNVTWGDVPBVAVBVPBWBAVCVDVEVGVH $.
  $}

  ${
    $d x A $.  $d x B $.  $d x M $.  $d x S $.
    $( The measure the union of two complementary sets is the sum of their
       measures.  (Contributed by Thierry Arnoux, 10-Mar-2017.) $)
    measxun2 $p |- ( ( M e. ( measures ` S ) /\ ( A e. S /\ B e. S )
      /\ B C_ A ) -> ( M ` A ) = ( ( M ` B ) +e ( M ` ( A \ B ) ) ) ) $=
      ( vx cfv wcel wa wss cpr cuni co wdisj wceq syl3anc syl2anc cin fveq2d c0
      cc0 cmeas w3a cdif cv cesum cxad cpw com cdom simp1 simp2r csiga measbase
      wbr crn simp2l difelsiga prelpwi prct simp3 disjdifprg2 prcom dfss biimpi
      syl incom eqtrdi preq2d eqtr3id disjeq1d biimprd mpan9 jca measvun uniprg
      cun undif sylan9eq simpr cpnf cicc measvxrge0 wo eqimss ssdifeq0 measvnul
      sylib sylan9eqr sylan orcd ex esumpr2 3eqtr3d ) DCUAFGZACGZBCGZHZBAIZUBZB
      ABUCZJZKZDFZXAEUDZDFZEUEZADFZBDFZWTDFZUFLWSWNXACUGGZXAUHUIUNZEXAXDMZHXCXF
      NWNWQWRUJZWSWPWTCGZXJWNWOWPWRUKZWSCULUOKGZWOWPXNWSWNXPXMCDUMVEWNWOWPWRUPZ
      XOABCUQOZBWTCURPWSXKXLWSWPXNXKXOXRBWTCCUSPWSWOWRXLXQWNWQWRUTZWOEWTABQZJZX
      DMZWRXLEABCVAWRXLYBWREXAYAXDWRXAWTBJYAWTBVBWRBXTWTWRBBAQZXTWRBYCNBAVCVDBA
      VFVGVHVIVJVKVLPVMEXACDVNOWSWPXNHZWRXCXGNWSWPXNXOXRVMXSYDWRHXBADYDWRXBBWTV
      PZABWTCCVOWRYEANBAVQVDVRRPWSBWTXEXHEXICCWSXDBNZHXDBDWSYFVSRWSXDWTNZHXDWTD
      WSYGVSRXOXRWSWNWPXHTVTWALZGXMXOBCDWBPWSWNXNXIYHGXMXRWTCDWBPWSBWTNZXHTNZXH
      VTNZWCWSYIHYJYKWSWNYIYJXMYIWNXHSDFTYIBSDYIBWTIBSNBWTWDBAWEWGRCDWFWHWIWJWK
      WLWM $.
  $}

  $( The measure the union of two disjoint sets is the sum of their measures.
     (Contributed by Thierry Arnoux, 10-Mar-2017.) $)
  measun $p |- ( ( M e. ( measures ` S ) /\ ( A e. S /\ B e. S )
    /\ ( A i^i B ) = (/) )
    -> ( M ` ( A u. B ) ) = ( ( M ` A ) +e ( M ` B ) ) ) $=
    ( cmeas cfv wcel wa c0 wceq cun cdif cxad co cxr cc0 cpnf measvxrge0 sselid
    syl2anc cin w3a wss simp1 crn cuni measbase 3ad2ant1 simp2l simp2r unelsiga
    csiga syl3anc ssun2 a1i measxun2 syl121anc difun2 uneq1 uncom eqtri inundif
    eqtrdi eqtr3di eqtrid fveq2d oveq2d 3ad2ant3 cicc iccssxr xaddcom 3eqtrd
    un0 ) DCEFGZACGZBCGZHZABUAZIJZUBZABKZDFZBDFZWABLZDFZMNZWCADFZMNZWGWCMNZVTVN
    WACGZVPBWAUCZWBWFJVNVQVSUDZVTCULUEUFGZVOVPWJVNVQWMVSCDUGUHVNVOVPVSUIZVNVOVP
    VSUJZABCUKUMWOWKVTBAUNUOWABCDUPUQVSVNWFWHJVQVSWEWGWCMVSWDADVSWDABLZAABURVSV
    RWPKZWPAVSWQIWPKZWPVRIWPUSWRWPIKWPIWPUTWPVMVAVCABVBVDVEVFVGVHVTWCOGZWGOGZWH
    WIJVTVNVPWSWLWOVNVPHPQVINZOWCPQVJZBCDRSTVTVNVOWTWLWNVNVOHXAOWGXBACDRSTWCWGV
    KTVL $.

  ${
    $d y z A $.  $d x y z M $.  $d x y S $.  $d y z B $.  $d z S $.
    measvunilem.1 $e |- F/_ x A $.
    $( Lemma for ~ measvuni .  (Contributed by Thierry Arnoux, 7-Feb-2017.)
       (Revised by Thierry Arnoux, 19-Feb-2017.)  (Revised by Thierry Arnoux,
       6-Mar-2017.) $)
    measvunilem $p |- ( ( M e. ( measures ` S ) /\
      A. x e. A B e. ( S \ { (/) } ) /\ ( A ~<_ _om /\ Disj_ x e. A B ) )
      -> ( M ` U_ x e. A B ) = sum* x e. A ( M ` B ) ) $=
      ( vy vz cfv wcel wral com cdom wbr wdisj cv wceq cvv syl nfcv c0 csn cdif
      cmeas wa w3a wrex cab cuni cesum ciun cpw simp1 wss simp3l abrexctf simp2
      ctex eldifi ralimi abrexss elpwg biimpar syl2anc simp3r measvun syl112anc
      disjabrexf dfiun2g fveq2d nfra1 nfbr nfdisj1 nfan nf3an r19.21bi disjdsct
      nfv fveq2 cc0 cpnf cicc co simpl1 measvxrge0 sylan2 esumc 3eqtr4d ) EDUDI
      JZCDUAUBZUCZJZABKZBLMNZABCOZUEZUFZGPCQABUGGUHZUIZEIZWRHPZEIZHUJZABCUKZEIZ
      BCEIZAUJWQWIWRDULJZWRLMNZHWRXAOZWTXCQWIWMWPUMWQWRRJZWRDUNZXGWQXHXJWQWNXHW
      IWMWNWOUOZAGBCFUPSZWRURSWQWMXKWIWMWPUQZWMCDJZABKXKWLXOABCDWJUSZUTAGBCDADT
      VASSXJXGXKWRDRVBVCVDXMWQWOXIWIWMWNWOVEZAHGBCFVHSHWRDEVFVGWQWMXEWTQXNWMXDW
      SEAGBCWKVIVJSWQHGBXFCXBARWKAXBTWIWMWPAWIAVRWLABVKWNWOAABLMFAMTALTVLABCVMV
      NVOZFXACEVSWQWNBRJXLBURSWQABCDXRFWQWLABXNVPZXQVQWQAPBJZUEWIWLXFVTWAWBWCJZ
      WIWMWPXTWDXSWLWIXOYAXPCDEWEWFVDXSWGWH $.
  $}

  ${
    $d x M $.  $d x S $.
    measvunilem.0.1 $e |- F/_ x A $.
    $( Lemma for ~ measvuni .  (Contributed by Thierry Arnoux, 6-Mar-2017.) $)
    measvunilem0 $p |- ( ( M e. ( measures ` S ) /\
      A. x e. A B e. { (/) } /\ ( A ~<_ _om /\ Disj_ x e. A B ) )
      -> ( M ` U_ x e. A B ) = sum* x e. A ( M ` B ) ) $=
      ( cfv wcel c0 com cdom wa cc0 cesum ciun cvv wceq nfcv fveq2d eqtrd cmeas
      csn wral wbr wdisj w3a simp3l ctex esum0 3syl nfv nfra1 nfbr nfdisj1 nfan
      nf3an eqidd cv simp2 r19.21bi elsni measvnul 3ad2ant1 adantr esumeq12dvaf
      syl iuneq12daf iun0 eqtrdi 3eqtr4rd ) EDUAGHZCIUBHZABUCZBJKUDZABCUEZLZUFZ
      BMANZMBCEGZANABCOZEGZVQVNBPHVRMQVKVMVNVOUGBUHBAPFUIUJVQBBVSMAVKVMVPAVKAUK
      VLABULVNVOAABJKFAKRAJRUMABCUNUOUPZVQBUQZVQAURBHZLZVSIEGZMWECIEWEVLCIQVQVL
      ABVKVMVPUSUTCIVAVFZSVQWFMQZWDVKVMWHVPDEVBVCZVDTVEVQWAWFMVQVTIEVQVTABIOIVQ
      ABBCIWBFFWCWGVGABVHVISWITVJ $.
  $}

  ${
    $d x A $.  $d x M $.  $d x S $.
    $( The measure of a countable disjoint union is the sum of the measures.
       This theorem uses a collection rather than a set of subsets of ` S ` .
       (Contributed by Thierry Arnoux, 7-Mar-2017.) $)
    measvuni $p |- ( ( M e. ( measures ` S ) /\ A. x e. A B e. S /\
      ( A ~<_ _om /\ Disj_ x e. A B ) ) -> ( M ` U_ x e. A B ) =
      sum* x e. A ( M ` B ) ) $=
      ( cfv wcel wral com wa c0 crab ciun wceq adantl ralrimiva 3ad2ant1 adantr
      cesum cin cmeas cdom wbr wdisj w3a csn cdif co simp1 cv rabid simprbi wss
      cxad ssrab2 ssct mpan 3ad2ant3 simp3r nfrab1 mpsyl measvunilem0 syl112anc
      nfcv disjss1f measvunilem oveq12d cun nfra1 nfdisj1 nfan nf3an nfun simp2
      nfv rabid2 sylibr elun csiga cuni measbase 0elsiga snssi 3syl undif sylib
      wo crn eleq2d bitr3id rabbidv eqtr4d unrab eqtr4di eqidd iuneq12df fveq2d
      iunxun fveq2i eqtrdi wb elsni eleq1d mpbird syl2an sigaclcuni syl3anc syl
      eldifad iuneq2i iun0 eqtri ineq1 0in mp1i measun syl121anc eqtrd esumeq1d
      cvv ctex inrab noel disjdif eleq2i mtbir elin mtbi rgenw rabeq0 mpbir a1i
      wn cc0 cpnf cicc sylan measvxrge0 syl2anc esumsplit 3eqtr4d ) EDUAFGZCDGZ
      ABHZBIUBUCZABCUDZJZUEZACKUFZGZABLZCMZEFZACDUUIUGZGZABLZCMZEFZUNUHZUUKCEFZ
      ASZUUPUUTASZUNUHZABCMZEFZBUUTASZUUHUUMUVAUURUVBUNUUHUUBUUJAUUKHZUUKIUBUCZ
      AUUKCUDZUUMUVANUUBUUDUUGUIZUUBUUDUVGUUGUUBUUJAUUKAUJZUUKGZUUJUUBUVLUVKBGZ
      UUJUUJABUKULZOPQUUGUUBUVHUUDUUEUVHUUFUUKBUMZUUEUVHUUJABUOZUUKBUPUQRURZUVO
      UUHUUFUVIUVPUUBUUDUUEUUFUSZAUUKBCUUJABUTZABVDZVEVAAUUKCDEUVSVBVCUUHUUBUUO
      AUUPHZUUPIUBUCZAUUPCUDZUURUVBNUVJUUBUUDUWAUUGUUBUUOAUUPUVKUUPGZUUOUUBUWDU
      VMUUOUUOABUKULZOZPQUUGUUBUWBUUDUUEUWBUUFUUPBUMZUUEUWBUUOABUOZUUPBUPUQRURZ
      UWGUUHUUFUWCUWHUVRAUUPBCUUOABUTZUVTVEVAAUUPCDEUWJVFVCVGUUHUVEUULUUQVHZEFZ
      UUSUUHUVEAUUKUUPVHZCMZEFUWLUUHUVDUWNEUUHABUWMCCUUBUUDUUGAUUBAVOUUCABVIUUE
      UUFAUUEAVOABCVJVKVLZUVTAUUKUUPUVSUWJVMUUHBUUJUUOWGZABLZUWMUUHBUUCABLZUWQU
      UHUUDBUWRNUUBUUDUUGVNUUCABVPVQUUBUUDUWQUWRNUUGUUBUWPUUCABUWPCUUIUUNVHZGUU
      BUUCCUUIUUNVRUUBUWSDCUUBUUIDUMZUWSDNUUBDVSWHVTGZKDGZUWTDEWAZDWBZKDWCWDUUI
      DWEWFWIWJWKQWLUUJUUOABWMWNZUUHCWOWPWQUWNUWKEAUUKUUPCWRWSWTUUHUUBUULDGZUUQ
      DGZUULUUQTZKNZUWLUUSNUVJUUHUXAUUCAUUKHZUVHUXFUUBUUDUXAUUGUXCQZUUBUUDUXJUU
      GUUBUUCAUUKUUBUXAUUJUUCUVLUXCUVNUXAUUJJUUCUXBUXAUXBUUJUXDRUUJUUCUXBXAUXAU
      UJCKDCKXBZXCOXDXEZPQUVQUUKCDAUVSXFXGUUHUXAUUCAUUPHZUWBUXGUXKUUBUUDUXNUUGU
      UBUUCAUUPUUBUWDJCDUUIUWFXIPQUWIUUPCDAUWJXFXGUULKNZUXIUUHUULAUUKKMKAUUKCKU
      VLUUJCKNUVNUXLXHXJAUUKXKXLUXOUXHKUUQTKUULKUUQXMUUQXNWTXOUULUUQDEXPXQXRUUH
      UVFUWMUUTASUVCUUHBUWMUUTAUWOUXEXSUUHUUKUUPUUTAUWOUVSUWJUUHUVHUUKXTGUVQUUK
      YAXHUUHUWBUUPXTGUWIUUPYAXHUUKUUPTZKNUUHUXPUUJUUOJZABLZKUUJUUOABYBUXRKNUXQ
      YMZABHUXSABCUUIUUNTZGZUXQUYACKGCYCUXTKCUUIDYDYEYFCUUIUUNYGYHYIUXQABYJYKXL
      YLUUHUVLJUUBUUCUUTYNYOYPUHGZUUHUUBUVLUVJRUUHUUBUVLUUCUVJUXMYQCDEYRZYSUUHU
      WDJZUUBUUCUYBUUHUUBUWDUVJRUYDCDUUIUWDUUOUUHUWEOXIUYCYSYTXRUUA $.
  $}

  ${
    $d y A $.  $d y B $.  $d y M $.  $d y S $.  $d y ph $.
    measssd.1 $e |- ( ph -> M e. ( measures ` S ) ) $.
    measssd.2 $e |- ( ph -> A e. S ) $.
    measssd.3 $e |- ( ph -> B e. S ) $.
    measssd.4 $e |- ( ph -> A C_ B ) $.
    $( A measure is monotone with respect to set inclusion.  (Contributed by
       Thierry Arnoux, 28-Dec-2016.) $)
    measssd $p |- ( ph -> ( M ` A ) <_ ( M ` B ) ) $=
      ( vy cfv cle cc0 wbr wcel syl syl2anc wceq wss adantl cdif cxad cpnf cicc
      co cmeas csiga crn cuni measbase difelsiga syl3anc measvxrge0 cxr elxrge0
      simprbi wi simplbi xraddge02 mpd cpr cesum cpw cdom wdisj prssi prex elpw
      com sylibr prct disjdifprg prcom a1i disjeq1d mpbid measvun syl112anc cun
      cv uniprg undif sylib eqtrd fveq2d fveq2 wo eqimss ssdifeq0 measvnul orcd
      wa c0 adantr ex esumpr2 3eqtr3d breqtrrd ) ABEKZWSCBUAZEKZUBUEZCEKZLAMXAL
      NZWSXBLNZAXAMUCUDUEZOZXDAEDUFKOZWTDOZXGFADUGUHUIOZCDOZBDOZXIAXHXJFDEUJPHG
      CBDUKULZWTDEUMQZXGXAUNOZXDXAUOZUPPAWSUNOZXOXDXEUQAWSXFOZXQAXHXLXRFGBDEUMQ
      ZXRXQMWSLNWSUOURPAXGXOXNXGXOXDXPURPWSXAUSQUTABWTVAZUIZEKZXTJVTZEKZJVBZXCX
      BAXHXTDVCOZXTVIVDNZJXTYCVEZYBYERFAXTDSZYFAXLXIYIGXMBWTDVFQXTDBWTVGVHVJAXL
      XIYGGXMBWTDDVKQAJWTBVAZYCVEZYHAXLXKYKGHJBCDDVLQAJYJXTYCYJXTRAWTBVMVNVOVPJ
      XTDEVQVRAYACEAYABWTVSZCAXLXIYAYLRGXMBWTDDWAQABCSYLCRIBCWBWCWDWEABWTYDWSJX
      ADDYCBRYDWSRAYCBEWFTYCWTRYDXARAYCWTEWFTGXMXSXNABWTRZWSMRZWSUCRZWGAYMWLZYN
      YOYPWSWMEKZMYPBWMEYMBWMRZAYMBWTSYRBWTWHBCWIWCTWEAYQMRZYMAXHYSFDEWJPWNWDWK
      WOWPWQWR $.
  $}

  ${
    measunl.1 $e |- ( ph -> M e. ( measures ` S ) ) $.
    measunl.2 $e |- ( ph -> A e. S ) $.
    measunl.3 $e |- ( ph -> B e. S ) $.
    $( A measure is sub-additive with respect to union.  (Contributed by
       Thierry Arnoux, 20-Oct-2017.) $)
    measunl $p |- ( ph -> ( M ` ( A u. B ) ) <_ ( ( M ` A ) +e ( M ` B ) ) ) $=
      ( cun cfv co cle wcel cin wceq cxr wbr measvxrge0 syl2anc sselid cmeas c0
      cdif cxad undif1 fveq2i csiga crn measbase syl difelsiga syl3anc disjdifr
      cuni a1i measun syl121anc eqtr3id cc0 cpnf cicc iccssxr wa inelsiga sylib
      elxrge0 simprd xraddge02 mpd uncom inundif eqtr3i incom breqtrrd xleadd1a
      wi inindif syl31anc eqbrtrd ) ABCIZEJZBCUCZEJZCEJZUDKZBEJZWDUDKZLAWAWBCIZ
      EJZWEWHVTEBCUEUFAEDUAJMZWBDMZCDMZWBCNUBOZWIWEOFADUGUHUNMZBDMZWLWKAWJWNFDE
      UIUJZGHBCDUKULZHWMACBUMUOWBCDEUPUQURAWCPMZWFPMWDPMWCWFLQWEWGLQAUSUTVAKZPW
      CUSUTVBZAWJWKWCWSMFWQWBDERSTZAWSPWFWTAWJWOWFWSMFGBDERSTAWSPWDWTAWJWLWDWSM
      FHCDERSTAWCWCBCNZEJZUDKZWFLAUSXCLQZWCXDLQZAXCPMZXEAXCWSMZXGXEVCAWJXBDMZXH
      FAWNWOWLXIWPGHBCDVDULZXBDERSZXCVFVEVGAWRXGXEXFVPXAAWSPXCWTXKTWCXCVHSVIAWF
      WBXBIZEJZXDXLBEXBWBIXLBXBWBVJBCVKVLUFAWJWKXIWBXBNZUBOZXMXDOFWQXJXOAXBWBNX
      NUBXBWBVMBCVQVLUOWBXBDEUPUQURVNWCWFWDVOVRVS $.
  $}

  ${
    $d k A $.  $d k n I $.  $d n M $.  $d k n N $.  $d k n S $.  $d k n ph $.
    measiuns.0 $e |- F/_ n B $.
    measiuns.1 $e |- ( n = k -> A = B ) $.
    measiuns.2 $e |- ( ph -> ( N = NN \/ N = ( 1 ..^ I ) ) ) $.
    measiuns.3 $e |- ( ph -> M e. ( measures ` S ) ) $.
    measiuns.4 $e |- ( ( ph /\ n e. N ) -> A e. S ) $.
    $( The measure of the union of a collection of sets, expressed as the sum
       of a disjoint set.  This is used as a lemma for both ~ measiun and
       ~ meascnbl .  (Contributed by Thierry Arnoux, 22-Jan-2017.)  (Proof
       shortened by Thierry Arnoux, 7-Feb-2017.) $)
    measiuns $p |- ( ph -> ( M ` U_ n e. N A )
      = sum* n e. N ( M ` ( A \ U_ k e. ( 1 ..^ n ) B ) ) ) $=
      ( cfv c1 wcel wa cn wss ciun cv cfzo co cdif cesum iundisjcnt fveq2d wral
      cmeas com cdom wbr wdisj wceq crn cuni measbase syl adantr simpll fzossnn
      csiga simpr sseqtrrid cuz simplr eleqtrd elfzouz2 fzoss2 3syl sseqtrrd wo
      mpjaodan sselda wsb sbimi sban sbv clelsb1 anbi12i bitri csb sbsbc wb cvv
      wsbc sbcel1g elv nfcv cbvcsbw csbid eqtri eleq1i 3bitri 3imtr3i ralrimiva
      syl2anc sigaclfu2 difelsiga syl3anc eqimss sseq1 mpbiri jaoi nnct sylancl
      ssct iundisj2cnt measvuni syl112anc eqtrd ) AFIBUAZHOFIBEPFUBZUCUDZCUAZUE
      ZUAZHOZIXQHOFUFZAXMXRHABCEFGIJKLUGUHAHDUJOQZXQDQZFIUIIUKULUMZFIXQUNXSXTUO
      MAYBFIAXNIQZRZDVCUPUQQZBDQZXPDQZYBAYFYDAYAYFMDHURUSUTZNYEYFCDQZEXOUIYHYIY
      EYJEXOYEEUBZXOQZRAYKIQZYJAYDYLVAYEXOIYKYEISUOZXOITIPGUCUDZUOZYEYNRSXOIXNV
      BYEYNVDVEYEYPRZXOYOIYQXNYOQGXNVFOQXOYOTYQXNIYOAYDYPVGYEYPVDZVHXNPGVIXNPGV
      JVKYRVLAYNYPVMZYDLUTVNVOYEFEVPZYGFEVPZAYMRZYJYEYGFENVQYTAFEVPZYDFEVPZRUUB
      AYDFEVRUUCAUUDYMAFEVSFEIVTWAWBUUAYGFYKWGZFYKBWCZDQZYJYGFEWDUUEUUGWEEFYKBD
      WFWHWIUUFCDUUFEYKCWCCFEYKBCEBWJJKWKECWLWMWNWOWPWRWQCDEXNWSWRBXPDWTXAWQAIS
      TZSUKULUMYCAYSUUHLYNUUHYPISXBYPUUHYOSTGVBIYOSXCXDXEUSXFISXHXGABCEFGIJKLXI
      FIXQDHXJXKXL $.
  $}

  ${
    $d k m n $.  $d k n ph $.  $d n k S $.  $d k B $.  $d n M $.
    measiun.1 $e |- ( ph -> M e. ( measures ` S ) ) $.
    measiun.2 $e |- ( ph -> A e. S ) $.
    measiun.3 $e |- ( ( ph /\ n e. NN ) -> B e. S ) $.
    measiun.4 $e |- ( ph -> A C_ U_ n e. NN B ) $.
    $( A measure is sub-additive.  (Contributed by Thierry Arnoux,
       30-Dec-2016.)  (Proof shortened by Thierry Arnoux, 7-Feb-2017.) $)
    measiun $p |- ( ph -> ( M ` A ) <_ sum* n e. NN ( M ` B ) ) $=
      ( vk cfv cn co cxr wcel measvxrge0 syl2anc wral wi vm ciun cesum cc0 cpnf
      cicc iccssxr cmeas sselid csiga crn cuni measbase syl ralrimiva sigaclcu2
      cvv nnex cv wa adantr nfcv esumcl sylancr measssd c1 cfzo csb cle nfcsb1v
      cdif csbeq1a wceq eqidd orcd measiuns a1i nfv nfel1 eleq1w eleq1d imbi12d
      nfim imbi2d ex chvarfv ralrimiv wss fzossnn ssralv ax-mp sigaclfu2 sylan2
      difelsiga syl3anc difssd esumle eqbrtrd xrletrd ) ABFLZEMCUBZFLZMCFLZEUCZ
      AUDUEUFNZOWTUDUEUGZAFDUHLPZBDPWTXEPGHBDFQRUIAXEOXBXFAXGXADPZXBXEPGADUJUKU
      LPZCDPZEMSXHAXGXIGDFUMUNZAXJEMIUOCDEUPRZXADFQRUIAXEOXDXFAMUQPZXCXEPZEMSXD
      XEPURAXNEMAEUSZMPZUTZXGXJXNAXGXPGVAZICDFQRZUOMXCEUQEMVBVCVDUIABXADFGHXLJV
      EAXBMCKVFXOVGNZEKUSZCVHZUBZVKZFLZEUCXDVIACYBDKEUAUSZFMEYACVJZEYACVLZAMMVM
      MVFYFVGNVMAMVNVOGIVPAMYEXCEUQXMAURVQXQXGYDDPZYEXEPXRXQXIXJYCDPZYIAXIXPXKV
      AIAYJXPAXIYBDPZKMSZYJXKAYKKMAXPXJTZTAYAMPZYKTZTEKAYOEAEVRYNYKEEYAMEYAVBVS
      EYBDYGVSWCWCXOYAVMZYMYOAYPXPYNXJYKEKMVTYPCYBDYHWAWBWDAXPXJIWEWFWGYLXIYKKX
      TSZYJXTMWHYLYQTXOWIYKKXTMWJWKYBDKXOWLWMRVACYCDWNWOZYDDFQRXSXQYDCDFXRYRIXQ
      CYCWPVEWQWRWS $.
  $}

  ${
    $d i k n o p x F $.  $d i n J $.  $d i n o p M $.  $d i k n S $.
    $d i k n o p ph $.
    meascnbl.0 $e |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) ) $.
    meascnbl.1 $e |- ( ph -> M e. ( measures ` S ) ) $.
    meascnbl.2 $e |- ( ph -> F : NN --> S ) $.
    meascnbl.3 $e |- ( ( ph /\ n e. NN ) -> ( F ` n ) C_ ( F ` ( n + 1 ) ) ) $.
    $( A measure is continuous from below.  Cf. ~ volsup .  (Contributed by
       Thierry Arnoux, 18-Jan-2017.)  (Revised by Thierry Arnoux,
       11-Jul-2017.) $)
    meascnbl $p |- ( ph -> ( M o. F ) ( ~~>t ` J ) ( M ` U. ran F ) ) $=
      ( vi vk cn c1 cv co cfv cfzo wcel wceq vo vp vx ciun cdif cesum cmpt ccom
      cfz crn cuni clm cmeas cc0 cpnf cicc adantr csiga measbase syl ffvelcdmda
      wa wral simpll fzossnn simpr sselid syl2anc ralrimiva sigaclfu2 difelsiga
      syl3anc measvxrge0 fveq2 oveq2 iuneq1d difeq12d fveq2d esumcvg2 measfrge0
      wf fcompt caddc nfcv cz nnzd fzval3 olcd eleq2d biimpa ffnd iuninc eqtr3d
      measiuns mpteq2dva eqtr4d wrex cab dfiun2g wfn fnrnfv unieqd orcd 3brtr4d
      eqidd ) AKMNKOZUIPZCOZDQZLNXHRPZLOZDQZUDZUEZFQZCUFZUGZMXOCUFZFDUHZDUJZUKZ
      FQZEULQAXOUAOZDQZLNYCRPZXLUDZUEZFQUBOZDQZLNYHRPZXLUDZUEZFQCUBKEUAGAXHMSZV
      BZFBUMQSZXNBSZXOUNUOUPPZSAYOYMHUQYNBURUJUKSZXIBSZXMBSZYPAYRYMAYOYRHBFUSUT
      UQZAMBXHDIVAZYNYRXLBSZLXJVCYTUUAYNUUCLXJYNXKXJSZVBZAXKMSUUCAYMUUDVDUUEXJM
      XKXHVEYNUUDVFVGAMBXKDIVAVHVIXLBLXHVJVHXIXMBVKVLXNBFVMVHXHYCTZXNYGFUUFXIYD
      XMYFXHYCDVNUUFLXJYEXLXHYCNRVOVPVQVRXHYHTZXNYLFUUGXIYIXMYKXHYHDVNUUGLXJYJX
      LXHYHNRVOVPVQVRVSAXSKMXFDQZFQZUGZXQABYQFWAZMBDWAXSUUJTAYOUUKHBFVTUTIKFDMB
      YQWBVHAKMXPUUIAXFMSZVBZCXGXIUDZFQXPUUIUUMXIXLBLCXFNWCPZFXGCXLWDZXHXKDVNZU
      UMXGNUUORPZTZXGMTUUMXFWESUUSUUMXFAUULVFWFNXFWGUTZWHAYOUULHUQUUMXHXGSZVBZA
      YMYSAUULUVAVDUVBUURMXHUUOVEUUMUVAXHUURSUUMXGUURXHUUTWIWJVGUUBVHWNUUMUUNUU
      HFAKCDAMBDIWKZJWLVRWMWOWPACMXIUDZFQYBXRAUVDYAFAUVDUCOXITCMWQUCWRZUKZYAAYS
      CMVCUVDUVFTAYSCMUUBVICUCMXIBWSUTAXTUVEADMWTXTUVETUVCCUCMDXAUTXBWPVRAXIXLB
      LCUUOFMUUPUUQAMMTMUURTAMXEXCHUUBWNWMXD $.
  $}

  ${
    $d x y z A $.  $d x B $.  $d x y z S $.  $d x y z M $.
    $( Lemma for ~ measinb .  (Contributed by Thierry Arnoux, 2-Jun-2017.) $)
    measinblem $p |- ( ( ( ( M e. ( measures ` S ) /\ A e. S ) /\ B e. ~P S )
      /\ ( B ~<_ _om /\ Disj_ x e. B x ) ) ->
      ( M ` ( U. B i^i A ) ) = sum* x e. B ( M ` ( x i^i A ) ) ) $=
      ( cmeas cfv wcel wa cpw com cdom wbr cv wdisj cuni cin ciun nfv nfan wral
      cesum iunin1 uniiun ineq1i eqtr4i fveq2i wceq simplll nfdisj1 w3a simp1ll
      csiga crn measbase simp1r elelpwi syl2anc simp1lr inelsiga syl3anc 3expia
      syl simp3 ralrimi simprl disjin ad2antll measvuni syl112anc eqtr3id ) EDF
      GHZBDHZIZCDJHZIZCKLMZACANZOZIZIZCPZBQZEGACVRBQZRZEGZCWDEGAUBZWEWCEWEACVRR
      ZBQWCACBVRUCWBWHBACUDUEUFUGWAVLWDDHZACUAVQACWDOZWFWGUHVLVMVOVTUIWAWIACVPV
      TAVPASVQVSAVQASACVRUJTTVPVTVRCHZWIVPVTWKUKZDUMUNPHZVRDHZVMWIWLVLWMVLVMVOV
      TWKULDEUOVCWLWKVOWNVPVTWKVDVNVOVTWKUPVRCDUQURVLVMVOVTWKUSVRBDUTVAVBVEVPVQ
      VSVFVSWJVPVQABCVRVGVHACWDDEVIVJVK $.

    $( Building a measure restricted to the intersection with a given set.
       (Contributed by Thierry Arnoux, 25-Dec-2016.) $)
    measinb $p |- ( ( M e. ( measures ` S ) /\ A e. S ) ->
      ( x e. S |-> ( M ` ( x i^i A ) ) ) e. ( measures ` S ) ) $=
      ( vz vy cfv wcel wa cv cin wceq inelsiga syl3anc measvxrge0 syl2anc eqidd
      cc0 c0 syl cmeas cmpt cpnf cicc co com cdom wbr wdisj cuni cesum cpw wral
      wf wi simpll csiga crn measbase ad2antrr simpr simplr fmpttd cr ineq1 0in
      eqtrdi fveq2d adantl measvnul eqtrd adantr 0elsiga 0red fvmptd measinblem
      simplll simprl sigaclcu simpllr elpwi ad2antlr sseldd esumeq2dv ralrimiva
      wss 3eqtr4d ex w3a wb ismeas mpbir3and ) DCUAGZHZBCHZIZACAJZBKZDGZUBZWMHZ
      CRUCUDUEZWTUNZSWTGRLZEJZUFUGUHZFXEFJZUIZIZXEUJZWTGZXEXGWTGZFUKZLZUOZECULZ
      UMZWPACWSXBWPWQCHZIZWNWRCHZWSXBHWNWOXRUPXSCUQURUJHZXRWOXTWNYAWOXRCDUSZUTW
      PXRVAWNWOXRVBWQBCMNWRCDOPVCWPASWSRCWTVDWPWTQWPWQSLZIWSSDGZRYCWSYDLWPYCWRS
      DYCWRSBKSWQSBVEBVFVGVHVIWNYDRLWOYCCDVJUTVKWPYASCHWNYAWOYBVLZCVMTWPVNVOWPX
      OEXPWPXEXPHZIZXIXNYGXIIZXJBKZDGZXEXGBKZDGZFUKZXKXMFBXECDVPYHAXJWSYJCWTXBY
      HWTQYHWQXJLZIWRYIDYNWRYILYHWQXJBVEVIVHYHYAYFXFXJCHZYHWNYAWNWOYFXIVQZYBTZW
      PYFXIVBYGXFXHVRXECVSNZYHWNYICHZYJXBHYPYHYAYOWOYSYQYRWNWOYFXIVTXJBCMNYICDO
      PVOYGXMYMLXIYGXEXLYLFYGXGXEHZIZAXGWSYLCWTXBUUAWTQUUAWQXGLZIWRYKDUUBWRYKLU
      UAWQXGBVEVIVHUUAXECXGYFXECWFWPYTXECWAWBYGYTVAWCZUUAWNYKCHZYLXBHWNWOYFYTVQ
      ZUUAYAXGCHWOUUDUUAWNYAUUEYBTUUCWNWOYFYTVTXGBCMNYKCDOPVOWDVLWGWHWEWPYAXAXC
      XDXQWIWJYEEFCWTWKTWL $.
  $}

  ${
    $d x y S $.  $d x y M $.  $d x y T $.
    $( Building a measure restricted to a smaller sigma-algebra.  (Contributed
       by Thierry Arnoux, 25-Dec-2016.) $)
    measres $p |- ( ( M e. ( measures ` S ) /\ T e. U. ran sigAlgebra
        /\ T C_ S ) -> ( M |` T ) e. ( measures ` T ) ) $=
      ( vx vy cmeas cfv wcel cuni w3a cc0 wf c0 wceq cv wa cesum simp2 3ad2ant1
      cpw csiga crn wss cpnf cicc co cres com cdom wbr wdisj wi measfrge0 simp3
      wral fssresd 0elsiga fvres 3syl measvnul eqtrd simp11 simp13 sspw syl2anc
      sselda measvun syl3anc simp3l fvresd elpwi adantll 3adant3 3eqtr4d 3expia
      sigaclcu esumeq2dv ralrimiva 3jca ismeas biimprd sylc ) CAFGHZBUAUBIHZBAU
      CZJZWDBKUDUEUFZCBUGZLZMWHGZKNZDOZUHUIUJZEWLEOZUKZPZWLIZWHGZWLWNWHGZEQZNZU
      LZDBTZUOZJZWHBFGHZWCWDWERZWFWIWKXDWFAWGBCWCWDAWGCLWEACUMSWCWDWEUNUPWFWJMC
      GZKWFWDMBHWJXHNXGBUQMBCURUSWCWDXHKNWEACUTSVAWFXBDXCWFWLXCHZWPXAWFXIWPJZWQ
      CGZWLWNCGZEQZWRWTXJWCWLATZHZWPXKXMNWCWDWEXIWPVBXJWEXIXOWCWDWEXIWPVCWFXIWP
      RZWEXCXNWLBAVDVFVEWFXIWPUNEWLACVGVHXJWQBCXJWDXIWMWQBHWFXIWDWPXGSXPWFXIWMW
      OVIWLBVPVHVJWFXIWTXMNWPWFXIPZWLWSXLEXQWNWLHZPWNBCXIXRWNBHWFXIWLBWNWLBVKVF
      VLVJVQVMVNVOVRVSWDXFXEDEBWHVTWAWB $.
  $}

  ${
    $d x A $.  $d x S $.  $d x M $.
    $( Building a measure restricted to the intersection with a given set.
       (Contributed by Thierry Arnoux, 25-Dec-2016.) $)
    measinb2 $p |- ( ( M e. ( measures ` S ) /\ A e. S ) ->
      ( x e. ( S i^i ~P A ) |-> ( M ` ( x i^i A ) ) )
      e. ( measures ` ( S i^i ~P A ) ) ) $=
      ( cmeas cfv wcel wa cpw cin cv cmpt cres resmpt3 inin eqid mpteq12i eqtri
      csiga crn wss measinb measbase sigainb elrnsiga syl sylan measres syl3anc
      cuni inss1 a1i eqeltrrid ) DCEFZGZBCGZHZACBIZJZAKBJDFZLZACUTLZUSMZUSEFZVC
      ACUSJZUTLVAACUSUTNAVEUTUSUTCUROUTPQRUQVBUNGUSSTUJZGZUSCUAZVCVDGABCDUBUOCV
      FGZUPVGCDUCVIUPHUSBSFGVGBCUDUSBUEUFUGVHUQCURUKULCUSVBUHUIUM $.
  $}

  ${
    $d x y z A $.  $d x y z M $.  $d x y z S $.
    $( Division of a measure by a positive constant is a measure.  (Contributed
       by Thierry Arnoux, 25-Dec-2016.)  (Revised by Thierry Arnoux,
       30-Jan-2017.) $)
    measdivcst $p |- ( ( M e. ( measures ` S ) /\ A e. RR+ )
      -> ( M oFC /e A ) e. ( measures ` S ) ) $=
      ( vx vy vz cfv wcel wa cxdiv co cv wceq cc0 adantr eqtrd cvv syl oveq1d
      c0 cmeas crp cofc cmpt cdm ofcfval3 cpnf cicc measfrge0 fdmd mpteq1d cdom
      wf com wbr wdisj cuni cesum cpw wral measvxrge0 adantlr simplr xrpxdivcld
      fmpttd csiga crn measbase 0elsiga ovex fveq2 eqid fvmptg sylancl measvnul
      xdiv0rp sylan9eq simpll simprl simprr w3a vex a1i simplll wss velpw ssel2
      sylanb adantll syl2anc esumdivc 3ad2antr1 ad2antrr simpr1 simpr2 sigaclcu
      wi syl3anc fvmpt3i simpr3 measvun syl112anc esumeq2dv 3eqtr4d syl13anc ex
      ralrimiva wb ismeas biimprd mp3and eqeltrd ) CBUAGZHZAUBHZIZCAJUCKZDBDLZC
      GZAJKZUDZXMXPXQDCUEZXTUDYADAJCXMUBUFXPDYBBXTXNYBBMXOXNBNUGUHKZCBCUIUJOUKP
      XPBYCYAUMZTYAGZNMZELZUNULUOZFYGFLZUPZIZYGUQZYAGZYGYIYAGZFURZMZWQZEBUSZUTZ
      YAXMHZXPDBXTYCXPXRBHZIXSAXNUUAXSYCHXOXRBCVAVBXNXOUUAVCVDVEXPYETCGZAJKZNXP
      TBHZUUCQHYEUUCMXNUUDXOXNBVFVGUQHZUUDBCVHZBVIROUUBAJVJDTXTUUCBQYAXRTMXSUUB
      AJXRTCVKSYAVLZVMVNXNXOUUCNAJKNXNUUBNAJBCVOSAVPVQPXPYQEYRXPYGYRHZIZYKYPUUI
      YKIXPUUHYHYJYPXPUUHYKVRXPUUHYKVCUUIYHYJVSUUIYHYJVTXPUUHYHYJWAZIZYGYICGZFU
      RZAJKZYGUULAJKZFURZYMYOXPYHUUHUUNUUPMYJUUIYGUULAFQYGQHUUIEWBWCUUIYIYGHZIX
      NYIBHZUULYCHXNXOUUHUUQWDUUHUUQUURXPUUHYGBWEUUQUUREBWFYGBYIWGWHZWIYIBCVAWJ
      XNXOUUHVCWKWLUUKYMYLCGZAJKZUUNUUKYLBHZYMUVAMUUKUUEUUHYHUVBXNUUEXOUUJUUFWM
      XPUUHYHYJWNZXPUUHYHYJWOZYGBWPWRDYLXTUVABYAXRYLMXSUUTAJXRYLCVKSUUGXSAJVJZW
      SRUUKUUTUUMAJUUKXNUUHYHYJUUTUUMMXNXOUUJVRUVCUVDXPUUHYHYJWTFYGBCXAXBSPUUKU
      UHYOUUPMUVCUUHYGYNUUOFUUHUUQIUURYNUUOMUUSDYIXTUUOBYAXRYIMXSUULAJXRYICVKSU
      UGUVEWSRXCRXDXEXFXGXNYDYFYSWAZYTWQXOXNYTUVFXNUUEYTUVFXHUUFEFBYAXIRXJOXKXL
      $.

    $( Alternate version of ~ measdivcst .  (Contributed by Thierry Arnoux,
       25-Dec-2016.)  (New usage is discouraged.) $)
    measdivcstALTV $p |- ( ( M e. ( measures ` S ) /\ A e. RR+ )
      -> ( x e. S |-> ( ( M ` x ) /e A ) ) e. ( measures ` S ) ) $=
      ( vy vz cfv wcel wa cc0 co cv cxdiv c0 wceq wi cvv simplr syl oveq1d cpnf
      cmeas crp cicc cmpt wf com cdom wbr wdisj cuni cesum cpw wral w3a wfn crn
      wss wfun cdm funmpt ovex rgenw dmmptg ax-mp mpbir2an a1i wrex wb vex eqid
      df-fn elrnmpt measfrge0 ffvelcdm sylan adantlr xrpxdivcld eleq1a biimtrid
      rexlimdva ssrdv sylanbrc csiga measbase 0elsiga adantr jctir fveq2 fvmptg
      df-f measvnul xdiv0rp eqtrd simpll simprl simprr 3jca simplll simpr elpwg
      sylan9eq ssel2 sylanb syl2anc measvxrge0 esumdivc 3ad2antr1 simpr1 simpr2
      ad2antrr sigaclcu syl3anc fvmpt3i jca simpr3 measvun 3expia r19.21bi sylc
      ralrimiva esumeq2dv 3eqtr4d ex ismeas biimprd mpd ) DCUBGZHZBUCHZIZCJUAUD
      KZACALZDGZBMKZUEZUFZNYPGZJOZELZUGUHUIZFYTFLZUJZIZYTUKZYPGZYTUUBYPGZFULZOZ
      PZECUMZUNZUOZYPYHHZYKYQYSUULYKYPCUPZYPUQZYLURYQUUOYKUUOYPUSYPUTCOZACYOVAY
      OQHZACUNUUQUURACYNBMVBZVCACYOQVDVEYPCVLVFVGYKEUUPYLYTUUPHZYTYOOZACVHZYKYT
      YLHZYTQHZUUTUVBVIEVJZACYOYTYPQYPVKZVMVEYKUVAUVCACYKYMCHZIZYOYLHUVAUVCPUVH
      YNBYIUVGYNYLHZYJYICYLDUFUVGUVICDVNCYLYMDVOVPVQYIYJUVGRVRYOYLYTVSSWAVTWBCY
      LYPWKWCYKYRNDGZBMKZJYKNCHZUVKQHZIYRUVKOYKUVLUVMYIUVLYJYICWDUQUKHZUVLCDWEZ
      CWFSWGUVJBMVBWHANYOUVKCQYPYMNOYNUVJBMYMNDWITUVFWJSYIYJUVKJBMKJYIUVJJBMCDW
      LTBWMXBWNYKUUJEUUKYKYTUUKHZIZUUDUUIUVQUUDIZYKUVPUUAUUCUOZUUIYKUVPUUDWOUVR
      UVPUUAUUCYKUVPUUDRUVQUUAUUCWPUVQUUAUUCWQWRYKUVSIZYTUUBDGZFULZBMKZYTUWABMK
      ZFULZUUFUUHYKUUAUVPUWCUWEOUUCUVQYTUWABFQUVDUVQUVEVGUVQUUBYTHZIZYIUUBCHZUW
      AYLHYIYJUVPUWFWSUWGUVPUWFUWHYKUVPUWFRUVQUWFWTUVPYTCURZUWFUWHUVDUVPUWIVIUV
      EYTCQXAVEYTCUUBXCXDZXEUUBCDXFXEYIYJUVPRXGXHUVTUUFUUEDGZBMKZUWCUVTUUECHZUU
      FUWLOUVTUVNUVPUUAUWMYIUVNYJUVSUVOXKYKUVPUUAUUCXIZYKUVPUUAUUCXJZYTCXLXMAUU
      EYOUWLCYPYMUUEOYNUWKBMYMUUEDWITUVFUUSXNSUVTUWKUWBBMUVTYIUVPIUUDUWKUWBOZUV
      TYIUVPYIYJUVSWOUWNXOUVTUUAUUCUWOYKUVPUUAUUCXPXOYIUUDUWPPZEUUKYIUWQEUUKYIU
      VPUUDUWPFYTCDXQXRYAXSXTTWNUVTUVPUUHUWEOUWNUVPYTUUGUWDFUVPUWFIUWHUUGUWDOUW
      JAUUBYOUWDCYPYMUUBOYNUWABMYMUUBDWITUVFUUSXNSYBSYCXEYDYAWRYIUUMUUNPYJYIUUN
      UUMYIUVNUUNUUMVIUVOEFCYPYESYFWGYG $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The counting measure
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y S $.
    $( The Counting measure is a measure on any sigma-algebra.  (Contributed by
       Thierry Arnoux, 25-Dec-2016.) $)
    cntmeas $p |- ( S e. U. ran sigAlgebra
                                         -> ( # |` S ) e. ( measures ` S ) ) $=
      ( vx vy cuni wcel chash cfv cc0 wf c0 wceq cv wa cesum cpw wral cvv fvres
      wi wss csiga crn cres cmeas cpnf cicc co com cdom wbr wdisj hashf2 fssres
      ssv mp2an a1i 0elsiga syl hash0 vex hasheuni mpan ad2antll cdif isrnsigau
      eqtrdi w3a simprd simp3d imim2i ralimi r19.21bi imp elpwi sseld esumeq2dv
      adantrr syl6 ad2antlr 3eqtr4d ex ralrimiva ismeas mpbir3and ) AUAUBDEZFAU
      CZAUDGEAHUEUFUGZWFIZJWFGZHKBLZUHUIUJZCWJCLZUKZMZWJDZWFGZWJWLWFGZCNZKZSZBA
      OZPWHWEQWGFIAQTWHULAUNQWGAFUMUOUPWEWIJFGZHWEJAEWIXBKAUQJAFRURUSVFWEWTBXAW
      EWJXAEZMZWNWSXDWNMWOFGZWJWLFGZCNZWPWRWMXEXGKZXDWKWJQEWMXHBUTCWJQVAVBVCXDW
      KWPXEKZWMXDWKXIWEWKXISZBXAWEWKWOAEZSZBXAPZXJBXAPWEADZAEZXNWJVDAEBAPZXMWEA
      XNOTXOXPXMVGBAVEVHVIXLXJBXAXKXIWKWOAFRVJVKURVLVMVQXCWRXGKWEWNXCWJWQXFCXCW
      LWJEZWQXFKZXCXQWLAEXRXCWJAWLWJAVNVOWLAFRVRVMVPVSVTWAWBBCAWFWCWD $.
  $}

  $( The counting measure is a measure on any power set.  (Contributed by
     Thierry Arnoux, 24-Jan-2017.) $)
  pwcntmeas $p |- ( O e. V -> ( # |` ~P O ) e. ( measures ` ~P O ) ) $=
    ( wcel cpw csiga cfv crn cuni chash cres cmeas pwsiga elrnsiga cntmeas 3syl
    ) ABCADZAEFCPEGHCIPJPKFCABLPAMPNO $.

  $( Counting and Lebesgue measures are different.  (Contributed by Thierry
     Arnoux, 27-Jan-2017.) $)
  cntnevol $p |- ( # |` ~P O ) =/= vol $=
    ( c1 wcel chash cpw cvol wne cfv cc0 a1i wceq syl cr 1re eqtrdi cdm necon3i
    ax-mp wss wn cres ax-1ne0 snelpwi fvres hashsng covol ovolsn nulmbl syl2anc
    csn snssi mblvol mp2b 3netr4d fveq1 biantrur snex elpw dmhashres eleq2i 1ex
    wa snss 3bitr4i notbii bitr3i nelne1 sylbir necomd dmeq pm2.61i ) BACZDAEZU
    AZFGZVLBUJZVNHZVPFHZGVOVLBIVQVRBIGVLUBJVLVQVPDHZBVLVPVMCZVQVSKBAUCVPVMDUDLB
    MCZVSBKNBMUEROVRIKZVLWAVPFPZCZWBNWAVPMSVPUFHZIKZWDBMUKBUGZVPUHUIZWDVRWEIVPU
    LWAWFNWGROUMJUNVNFVQVRVPVNFUOQLVLTZVNPZWCGVOWIWCWJWIWDVPWJCZTZVBZWCWJGWMWLW
    IWDWLWAWDNWHRUPWKVLVTVPASWKVLVPABUQURWJVMVPVMUSUTBAVAVCVDVEVFVPWCWJVGVHVIVN
    FWJWCVNFVJQLVK $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The Lebesgue measure - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

$(
  @{
    @d n y F @. @d n y X @. @d n y ph @.
    volmeaslem.1 @e |- ( ph -> X e. ~P dom vol ) @.
    volmeaslem.2 @e |- ( ph -> Disj_ y e. X y ) @.
    volmeaslem.3 @e |- ( ph -> F : NN -1-1-onto-> X ) @.
    volmeaslem.4 @e |- ( ( ph /\ y e. X ) -> ( vol ` y ) e. RR )  @.
    @( Lemma for ~ volmeas .
     (Contributed by Thierry Arnoux, 7-Apr-2017.) @)
    volmeaslem @p |- ( ph -> ( vol ` U. X ) = sum* y e. X ( vol ` y ) ) @=
      ( vn cvol cfv cn wcel cr wa wceq adantr syl2anc a1i nfcv cuni cesum caddc
      cv ciun cmpt c1 cseq crn cxr clt csup cdm wral wdisj cpw wf1o wf f1of syl
      ffvelcdmda elelpwi ralrimiva fveq2 eleq1d rspcv sylc simpr disjrdx mpbird
      jca eqid voliun wfo f1ofo iunrdx uniiun syl6reqr fveq2d fvmpt2d cpnf cicc
      cc0 co volf ffvelcdmd esumsup 3eqtr4d nfv eqidd esumf1o eqtr4d )
      ADUAZJKZL
      IUDZCKZJKZIUBZDBUDZJKZBUBAILWPUEZJKZUCILWQUFZUGUHZUIUJUKULZWNWRAWPJUMZMZW
      QNMZOZILUNILWPUOZXBXEPAXIILAWOLMZOZXGXHXLWPDMZDXFUPZMZXGALDWOCALDCUQZLDCU
      RGLDCUSUTVAZAXOXKEQWPDXFVBRZXLXMWTNMZBDUNZXHXQAXTXKAXSBDHVCQXSXHBWPDWSWPP
      ZWTWQNWSWPJVDZVEVFVGZVKVCAXJBDWSUOFAIBLWPDWSCGAYAVHZVIVJWPXDIXCXDVLZXCVLZ
      VMRAWMXAJAXABDWSUEWMAIBLWPDWSCAXPLDCVNGLDCVOUTYDVPBDVQVRVSAWQIXCXDYEAILWQ
      XCNXCXCPAYFSYCVTXLXFWCWAWBWDZWPJXFYGJURZXLWESXRWFWGWHADWTLWQBICWPXNAIWIID
      TILTICTYBEGXLWPWJAWSDMZOZXFYGWSJYHYJWESYJYIXOWSXFMAYIVHAXOYIEQWSDXFVBRWFW
      KWL @.
      @( [7-Apr-2017] @)
  @}
$)

  ${
    $d k n $.  $d k A $.
    $( The Lebesgue measure function is countably additive.  This formulation
       on the extended reals, allows for ` +oo ` for the measure of any set in
       the sum.  Cf. ~ ovoliun and ~ voliun .  (Contributed by Thierry Arnoux,
       16-Oct-2017.) $)
    voliune $p |- ( ( A. n e. NN A e. dom vol /\ Disj_ n e. NN A ) ->
      ( vol ` U_ n e. NN A ) = sum* n e. NN ( vol ` A ) ) $=
      ( vk cvol wcel cn wral wa cfv wceq cpnf c1 cxr cc0 syl adantlr cle wbr wb
      wrex cdm wdisj ciun cesum caddc cmpt cseq crn clt csup r19.26 eqid voliun
      cr sylanbr an32s cv nfra1 nfan cicc co rspa volf ffvelcdmi fvmpt2 syl2anc
      simpr ex ralrimi esumeq2d cico wf r19.21bi w3a pnfxr elicc1 mp2an simp2bi
      0xr ltpnf 0re elico2 syl3anbrc fmptdf nfmpt1 esumfsupre eqtr3d eqtr4d csb
      nfv nfcv nfcsb1v nffv nfeq1 weq csbeq1a fveqeq2d cbvrexw bilani wss nfel1
      eleq1d rspc impcom iunmbl adantr ssiun2sf volss syl3anc ralrimiva r19.29r
      adantl breq1 biimpa reximi c0 wne 1nn ne0i r19.9rzv sylibr iccssxr sselid
      mp2b ad2antrr mpbid cvv nfdisj1 nfre1 nnex 3ad2antr3 3anassrs esumpinfval
      xgepnf a1i wo wn exmid rexnal orbi2i mpbir r19.29 xrge0nre sylan mpjaodan
      orim2d mpi ) ADUAZEZBFGZBFAUBZHZADIZUNEZBFGZBFAUCZDIZFUUMBUDZJUUMKJZBFTZU
      ULUUOHUUQUEBFUUMUFZLUGZUHMUIUJZUURUUJUUOUUKUUQUVCJZUUJUUOHZUUIUUNHBFGUUKU
      VDUUIUUNBFUKAUVBBUVAUVBULUVAULZUMUOUPUUJUUOUURUVCJUUKUVEFBUQZUVAIZBUDZUUR
      UVCUVEFUVHUUMBUUJUUOBUUIBFURZUUNBFURUSZUVEUVHUUMJZBFUVKUVEUVGFEZUVLUUJUVM
      UVLUUOUUJUVMHZUVMUUMNKUTVAZEZUVLUUJUVMVGUVNUUIUVPUUIBFVBUUHUVOADVCVDZOZBF
      UUMUVOUVAUVFVEVFPVHVIVJUVEFNKVKVAZUVAVLUVIUVCJUVEBFUUMUVSUVAUVKUVEUVMHZUU
      NNUUMQRZUUMKUIRZUUMUVSEZUVEUUNBFUUJUUOVGVMZUVTUVPUWAUUJUVMUVPUUOUVRPUVPUU
      MMEZUWAUUMKQRZNMEKMEZUVPUWEUWAUWFVNSVSVONKUUMVPVQVROUVTUUNUWBUWDUUMVTONUN
      EUWGUWCUUNUWAUWBVNSWAVONKUUMWBVQWCUVFWDBUVABFUUMWEWFOWGPWHUULUUTHZUUQKUUR
      UWHKUUQQRZUUQKJZUWHUWICFTZUWIUWHBCUQZAWIZDIZKJZUWNUUQQRZHZCFTZUWKUWHUWOCF
      TZUWPCFGUWRUUTUWSUULUUSUWOBCFUUSCWJBUWNKBUWMDBDWKBUWLAWLZWMWNBCWOZAUWMKDB
      UWLAWPZWQWRWSUWHUWPCFUULUWLFEZUWPUUTUUJUXCUWPUUKUUJUXCHUWMUUHEZUUPUUHEZUW
      MUUPWTZUWPUXCUUJUXDUUIUXDBUWLFBUWMUUHUWTXAUXAAUWMUUHUXBXBXCXDUUJUXEUXCABX
      EZXFUXCUXFUUJBFAUWLUWMBFWKBUWLWKUWTUXBXGXLUWMUUPXHXIPPXJUWOUWPCFXKVFUWQUW
      ICFUWOUWPUWIUWNKUUQQXMXNXOOLFEFXPXQUWIUWKSXRFLXSUWICFXTYDYAUWHUUQMEZUWIUW
      JSUUJUXHUUKUUTUUJUXEUXHUXGUXEUVOMUUQNKYBUUHUVOUUPDVCVDYCOYEUUQYNOYFUWHFUU
      MBYGUULUUTBUUJUUKBUVJBFAYHUSUUSBFYIUSFYGEUWHYJYOUUJUUKUUTUVMUVPUUJUUKUVMU
      VPUUTUVRYKYLUULUUTVGYMWHUUJUUOUUTYPZUUKUUJUUOUUNYQZBFTZYPZUXIUXLUUOUUOYQZ
      YPUUOYRUXKUXMUUOUUNBFYSYTUUAUUJUXKUUTUUOUUJUXKUUTUUJUXKHUUIUXJHZBFTUUTUUI
      UXJBFUUBUXNUUSBFUUIUVPUXJUUSUVQUUMUUCUUDXOOVHUUFUUGXFUUE $.
  $}

  ${
    $d k n A $.  $d k B $.
    $( The Lebesgue measure function is countably additive.  This theorem is to
       ~ volfiniun what ~ voliune is to ~ voliun .  (Contributed by Thierry
       Arnoux, 16-Oct-2017.) $)
    volfiniune $p |- ( ( A e. Fin /\ A. n e. A B e. dom vol /\ Disj_ n e. A B )
      -> ( vol ` U_ n e. A B ) = sum* n e. A ( vol ` B ) ) $=
      ( vk cfn wcel cvol wral w3a cfv wceq cpnf wrex nfcv cc0 cle wbr syl cxr
      wa cdm wdisj cr ciun cesum csu simpl1 simpl2 simpr r19.26 sylanbrc simpl3
      volfiniun syl3anc nfel1 nfra1 nfdisj1 nf3an nfan cv cico co r19.21bi cicc
      clt rspa volf ffvelcdmi sylan wb 0xr pnfxr elicc1 mp2an simp2bi ltpnf 0re
      elico2 syl3anbrc esumpfinvalf csb nfv nfcsb1v nffv nfeq1 csbeq1a fveqeq2d
      eqtr4d cbvrexw sylib eleq1d rspc impcom adantll finiunmbl adantr ssiun2sf
      wss adantl volss 3adantl3 adantlr ralrimiva r19.29r syl2anc biimpa reximi
      breq1 wex rexex 19.9v iccssxr sselid 3adant3 xgepnf mpbid nfre1 3ad2antl2
      esumpinfval wo wn exmid rexnal orbi2i mpbir r19.29 xrge0nre ex orim2d mpi
      3ad2ant2 mpjaodan ) AEFZBGUAZFZCAHZCABUBZIZBGJZUCFZCAHZCABUDZGJZAYSCUEZKY
      SLKZCAMZYRUUATZUUCAYSCUFZUUDUUGYMYOYTTCAHZYQUUCUUHKYMYPYQUUAUGZUUGYPUUAUU
      IYMYPYQUUAUHZYRUUAUIZYOYTCAUJUKYMYPYQUUAULABCUMUNUUGAYSCCANZYRUUACYMYPYQC
      CAEUUMUOYOCAUPCABUQURZYTCAUPUSUUJUUGCUTZAFZTZYTOYSPQZYSLVEQZYSOLVAVBFZUUG
      YTCAUULVCZUUQYSOLVDVBZFZUURUUGYPUUPUVCUUKYPUUPTYOUVCYOCAVFYNUVBBGVGVHZRZV
      IUVCYSSFZUURYSLPQZOSFLSFZUVCUVFUURUVGIVJVKVLOLYSVMVNVORUUQYTUUSUVAYSVPROU
      CFUVHUUTYTUURUUSIVJVQVLOLYSVRVNVSVTWHYRUUFTZUUCLUUDUVILUUCPQZUUCLKZUVIUVJ
      DAMZUVJUVICDUTZBWAZGJZLKZUVOUUCPQZTZDAMZUVLUVIUVPDAMZUVQDAHUVSUVIUUFUVTYR
      UUFUIZUUEUVPCDAUUEDWBCUVOLCUVNGCGNCUVMBWCZWDWEUUOUVMKZBUVNLGCUVMBWFZWGWIW
      JUVIUVQDAYRUVMAFZUVQUUFYMYPUWEUVQYQYMYPTZUWETUVNYNFZUUBYNFZUVNUUBWRZUVQYP
      UWEUWGYMUWEYPUWGYOUWGCUVMACUVNYNUWBUOUWCBUVNYNUWDWKWLWMWNUWFUWHUWEABCWOZW
      PUWEUWIUWFCABUVMUVNUUMCUVMNUWBUWDWQWSUVNUUBWTUNXAXBXCUVPUVQDAXDXEUVRUVJDA
      UVPUVQUVJUVOLUUCPXHXFXGRUVLUVJDXIUVJUVJDAXJUVJDXKWJRUVIUUCSFZUVJUVKVJYRUW
      KUUFYMYPUWKYQUWFUWHUWKUWJUWHUVBSUUCOLXLYNUVBUUBGVGVHXMRXNWPUUCXORXPUVIAYS
      CEYRUUFCUUNUUECAXQUSYMYPYQUUFUGYRUUPUVCUUFYPYMUUPUVCYQUVEXRXBUWAXSWHYPYMU
      UAUUFXTZYQYPUUAYTYAZCAMZXTZUWLUWOUUAUUAYAZXTUUAYBUWNUWPUUAYTCAYCYDYEYPUWN
      UUFUUAYPUWNUUFYPUWNTYOUWMTZCAMUUFYOUWMCAYFUWQUUECAYOUVCUWMUUEUVDYSYGVIXGR
      YHYIYJYKYL $.
  $}

  ${
    $d f n x y $.
    $( The Lebesgue measure is a measure.  (Contributed by Thierry Arnoux,
       16-Oct-2017.) $)
    volmeas $p |- vol e. ( measures ` dom vol ) $=
      ( vx vy vf vn cvol cfv wcel cc0 c0 wceq cv com wbr wa wral cen simpr nfcv
      cn nfv cdm cmeas cpnf cicc co wf cdom wdisj cuni cesum wi cpw covol csiga
      crn cr fvssunirn dmvlsiga sselii 0elsiga ax-mp mblvol ovol0 eqtri nfdisj1
      volf cfn nfan wss elpwi ad3antrrr sseldd ex ralrimi simplrr uniiun fveq2i
      w3a ciun volfiniune eqtrid syl3anc wf1o wex bren fveq2 simpl eqidd sselda
      a1i ffvelcdmd esumf1o adantlr f1of adantl ffvelcdmda ralrimiva id disjrdx
      syl biimpar syl2anc voliune f1ofo iunrdx eqtr4di 3eqtr2rd exlimdv sylan2b
      fveq2d imp wo csdm brdom2 biimpi isfinite2 ensymb entr mpan sylbi orim12i
      nnenom ad2antrl mpjaodan rgen wb ismeas mpbir3an ) EEUAZUBFGZYIHUCUDUEZEU
      FZIEFZHJZAKZLUGMZBYOBKZUHZNZYOUIZEFZYOYQEFZBUJZJZUKZAYIULZOZVFYMIUMFZHIYI
      GZYMUUHJYIUNUOUIZGZUUIUPUNFUUJYIUNUPUQURUSZYIUTVAIVBVAVCVDUUEAUUFYOUUFGZY
      SUUDUUMYSNZYOVGGZUUDSYOPMZUUNUUONZUUOYQYIGZBYOOZYRUUDUUNUUOQUUQUURBYOUUNU
      UOBUUMYSBUUMBTYPYRBYPBTBYOYQVEVHVHUUOBTVHUUQYQYOGZUURUUQUUTNYOYIYQUUMYOYI
      VIZYSUUOUUTYOYIVJZVKUUQUUTQVLVMVNUUMYPYRUUOVOUUOUUSYRVRUUABYOYQVSZEFUUCYT
      UVCEBYOVPZVQYOYQBVTWAWBUUPUUNSYOCKZWCZCWDZUUDSYOCWEUUNUVGUUDUUNUVFUUDCUUN
      UVFUUDUUNUVFNZUUCSDKZUVEFZEFZDUJZDSUVJVSZEFZUUAUUMUVFUUCUVLJYSUUMUVFNZYOU
      UBSUVKBDUVEUVJUUFUVODTDUUBRBUVKRDYORDSRDUVERYQUVJEWFUUMUVFWGZUUMUVFQUVOUV
      ISGZNUVJWHUVOUUTNZYIYKYQEYLUVRVFWJUVOYOYIYQUVOUUMUVAUVPUVBWTWIWKWLWMUVHUV
      JYIGZDSODSUVJUHZUVNUVLJUVHUVSDSUVHUVQNYOYIUVJUUMUVAYSUVFUVQUVBVKUVHSYOUVI
      UVEUVFSYOUVEUFUUNSYOUVEWNWOWPVLWQUVHUVFYRUVTUUNUVFQUUMYPYRUVFVOUVFUVTYRUV
      FDBSUVJYOYQUVEUVFWRUVFYQUVJJQZWSXAXBUVJDXCXBUVFUVNUUAJUUNUVFUVMYTEUVFUVMU
      VCYTUVFDBSUVJYOYQUVESYOUVEXDUWAXEUVDXFXJWOXGVMXHXKXIYPUUOUUPXLZUUMYRYPYOL
      XMMZYOLPMZXLZUWBYPUWEYOLXNXOUWCUUOUWDUUPYOXPUWDLYOPMZUUPYOLXQSLPMUWFUUPYB
      SLYOXRXSXTYAWTYCYDVMYEUUKYJYLYNUUGVRYFUULABYIEYGVAYH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The Dirac delta measure
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c Ddelta $. $( Dirac delta measure, usually noted &delta;. $)

  $( Extend class notation to include the Dirac delta measure. $)
  cdde $a class Ddelta $.

  $( Define the Dirac delta measure.  (Contributed by Thierry Arnoux,
     14-Sep-2018.) $)
  df-dde $a |- Ddelta = ( a e. ~P RR |-> if ( 0 e. a , 1 , 0 ) ) $.

  ${
    $d a A $.
    $( Value of the delta measure.  (Contributed by Thierry Arnoux,
       14-Sep-2018.) $)
    ddeval1 $p |- ( ( A C_ RR /\ 0 e. A ) -> ( Ddelta ` A ) = 1 ) $=
      ( va cr wss cc0 wcel cdde cfv c1 cif cpw wceq cvv reex ssex elpwg biimpar
      mpancom cv eleq2 ifbid df-dde 1ex c0ex ifex fvmpt syl iftrue sylan9eq ) A
      CDZEAFZAGHZUKIEJZIUJACKZFZULUMLAMFZUJUOACNOUPUOUJACMPQRBAEBSZFZIEJUMUNGUQ
      ALURUKIEUQAETUABUBUKIEUCUDUEUFUGUKIEUHUI $.

    $( Value of the delta measure.  (Contributed by Thierry Arnoux,
       14-Sep-2018.) $)
    ddeval0 $p |- ( ( A C_ RR /\ -. 0 e. A ) -> ( Ddelta ` A ) = 0 ) $=
      ( va cr wss cc0 wcel wn cdde cfv cif cpw wceq cvv reex ssex elpwg biimpar
      c1 mpancom cv eleq2 ifbid df-dde 1ex c0ex ifex fvmpt syl iffalse sylan9eq
      ) ACDZEAFZGAHIZULREJZEUKACKZFZUMUNLAMFZUKUPACNOUQUPUKACMPQSBAEBTZFZREJUNU
      OHURALUSULREURAEUAUBBUCULREUDUEUFUGUHULREUIUJ $.
  $}

  ${
    $d a k x y $.
    $( The Dirac delta measure is a measure.  (Contributed by Thierry Arnoux,
       14-Sep-2018.) $)
    ddemeas $p |- Ddelta e. ( measures ` ~P RR ) $=
      ( vx vy va vk cdde cr cfv wcel cc0 cpnf c0 wceq wa cesum c1 cxr wn adantl
      wss cvv cpw cmeas cicc co wf cv com cdom wbr wdisj cuni wral cif cle 0le1
      wi 1xr pnfge ax-mp w3a wb 0xr pnfxr elicc1 mp2an mpbir3an 0e0iccpnf ifcli
      rgenw df-dde fmpt mpbi 0ss noel ddeval0 crab cun rabxm esumeq1 nfv rabexg
      cxad nfcv cin rabnc a1i elrabi simpl elelpwi syl2anc ffvelcdmi syl eqtrid
      esumsplit adantr wrex csn simp-4l vex rabsnel eleq2w rabsnt adantrr simpr
      ancoms fveq2d esumsn elpwid simprr ddeval1 syl12anc wex wreu wrmo df-disj
      eqtrd wal c0ex eleq1 rmobidv spcv sylbi rmo5 biimpi imp sylan reusn sylib
      cbvrabv eqeq1i ancri sylbir df-rex biimpri syl2an adantlr eqtr4d eqtrdi
      elrab csiga eximi sylibr adantll r19.29a elpwi sspwuni eluni2 nfre1 exbii
      nfn neq0 3bitr4i con1i esumeq1d esumnul con3i pm2.61dan simprbi esumeq2dv
      notbid rabex esum0 oveq12d vuniex elpw iccssxr xaddrid 3eqtrrd adantrl ex
      sselid 4syl rgen crn reex pwsiga elrnsiga ismeas mp2b ) EFUAZUBGHZUVTIJUC
      UDZEUEZKEGILZAUFZUGUHUIZBUWEBUFZUJZMZUWEUKZEGZUWEUWGEGZBNZLZUPZAUVTUAZULZ
      ICUFZHZOIUMZUWBHZCUVTULUWCUXACUVTUWSOIUWBOUWBHZOPHZIOUNUIZOJUNUIZUQUOUXCU
      XEUQOURUSIPHJPHUXBUXCUXDUXEUTVAVBVCIJOVDVEVFVGVHVICUVTUWBUWTECVJVKVLZKFSI
      KHQUWDFVMIVNKVOVEUWOAUWPUWEUWPHZUWIUWNUXGUWHUWNUWFUXGUWHMZUWMUWSCUWEVPZUW
      LBNZUWSQZCUWEVPZUWLBNZWBUDZUWKIWBUDZUWKUXGUWMUXNLUWHUXGUWMUXIUXLVQZUWLBNZ
      UXNUWEUXPLUWMUXQLUWSCUWEVRUWEUXPUWLBVSUSUXGUXIUXLUWLBUXGBVTBUXIWCBUXLWCZU
      WSCUWEUWPWAUXKCUWEUWPWAUXIUXLWDKLUXGUWSCUWEWEWFUXGUWGUXIHZMZUWGUVTHZUWLUW
      BHZUXTUWGUWEHZUXGUYAUXSUYCUXGUWSCUWGUWEWGRUXGUXSWHUWGUWEUVTWIZWJUVTUWBUWG
      EUXFWKZWLUXGUWGUXLHZMZUYAUYBUYGUYCUXGUYAUYFUYCUXGUXKCUWGUWEWGRUXGUYFWHUYD
      WJZUYEWLWNWMWOUXHUXJUWKUXMIWBUXHIUWGHZBUWEWPZUXJUWKLUXHUYJMZUXJOUWKUYKUXI
      DUFZWQZLZUXJOLDUWEUYKUYLUWEHZMZUYNMZUXJUYMUWLBNZOUYNUXJUYRLUYPUXIUYMUWLBV
      SRUYQUXGUYOIUYLHZUYROLUXGUWHUYJUYOUYNWRUYNUYOUYPUWSCUWEUYLDWSZWTZRUYNUYSU
      YPUWSUYSCUWEUYLUYTCDIXAXBRUXGUYOUYSMMZUYRUYLEGZOVUBUYLUVTHZUYRVUCLUXGUYOV
      UDUYSUYOUXGVUDUYLUWEUVTWIXEXCZVUDUWLVUCBUYLTVUDUWGUYLLZMUWGUYLEVUDVUFXDXF
      UYLTHVUDUYTWFUVTUWBUYLEUXFWKXGWLVUBUYLFSUYSVUCOLVUBUYLFVUEXHUXGUYOUYSXIUY
      LXJWJXPXKXPUWHUYJUYNDUWEWPZUXGUWHUYJMZUYIBUWEVPZUYMLZDXLZVUGVUHUYIBUWEXMZ
      VUKUWHUYIBUWEXNZUYJVULUWHUYLUWGHZBUWEXNZDXQVUMBDUWEUWGXOVUOVUMDIXRUYLILVU
      NUYIBUWEUYLIUWGXSXTYAYBVUMUYJVULVUMUYJVULUPUYIBUWEYCYDYEYFUYIBDUWEYGYHVUK
      UYOUYNMZDXLVUGVUJVUPDVUJUYNVUPUXIVUIUYMUWSUYICBUWECBIXAZYIYJUYNUYOVUAYKYL
      UUAUYNDUWEYMUUBWLUUCUUDUXGUYJUWKOLZUWHUXGUWJFSZIUWJHZVURUYJUXGUWEUVTSVUSU
      WEUVTUUEUWEFUUFYHZVUTUYJBIUWEUUGZYNUWJXJYOYPYQUXHUYJQZMUXJIUWKVVCUXJILUXH
      VVCUXJKUWLBNIVVCUXIKUWLBUYJBUYIBUWEUUHUUJUXIKLZUYJVVDQZUYJUXSBXLUYCUYIMZB
      XLVVEUYJUXSVVFBUWSUYICUWGUWEVUQYSUUIBUXIUUKUYIBUWEYMUULYDUUMUUNBUWLUUOYRR
      UXGVVCUWKILZUWHUXGVUSVUTQVVGVVCVVAVUTUYJVUTUYJVVBYDUUPUWJVOYOYPYQUUQUXGUX
      MILUWHUXGUXMUXLIBNZIUXGUXLUWLIBUYGUWGFSUYIQZUWLILUYGUWGFUYHXHUYFVVIUXGUYF
      UYCVVIUXKVVICUWGUWEUWRUWGLUWSUYIVUQUUTYSUURRUWGVOWJUUSUXLTHVVHILUXKCUWEAW
      SUVAUXLBTUXRUVBUSYRWOUVCUXGUXOUWKLZUWHUXGVUSUWJUVTHZUWKPHVVJVVAVVKVUSUWJF
      AUVDUVEYNVVKUWBPUWKIJUVFUVTUWBUWJEUXFWKUVKUWKUVGUVLWOUVHUVIUVJUVMUVTFYTGH
      ZUVTYTUVNUKHUWAUWCUWDUWQUTVAFTHVVLUVOFTUVPUSUVTFUVQABUVTEUVRUVSVF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The 'almost everywhere' relation
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c ae $. $( 'almost everywhere', noted &mu;-a.e. for a given measure &mu;. $)
  $c ~ae $. $( 'almost everywhere' builder for functions $)

  $( Extend class notation to include the 'almost everywhere' relation. $)
  cae $a class ae $.

  $( Extend class notation to include the 'almost everywhere' builder. $)
  cfae $a class ~ae $.

  ${
    $d a m $.
    $( Define 'almost everywhere' with regard to a measure ` M ` .  A property
       holds almost everywhere if the measure of the set where it does not hold
       has measure zero.  (Contributed by Thierry Arnoux, 20-Oct-2017.) $)
    df-ae $a |- ae = { <. a , m >. | ( m ` ( U. dom m \ a ) ) = 0 } $.

    $( 'almost everywhere' is a relation.  (Contributed by Thierry Arnoux,
       20-Oct-2017.) $)
    relae $p |- Rel ae $=
      ( vm va cv cdm cuni cdif cfv cc0 wceq cae df-ae relopabiv ) ACZDEBCFMGHIB
      AJABKL $.
  $}

  ${
    $d a m A $.  $d a m M $.
    $( 'almost everywhere' relation for a measure and a measurable set ` A ` .
       (Contributed by Thierry Arnoux, 20-Oct-2017.) $)
    brae $p |- ( ( M e. U. ran measures /\ A e. dom M ) ->
      ( A ae M <-> ( M ` ( U. dom M \ A ) ) = 0 ) ) $=
      ( vm va cdm wcel cmeas crn cuni cae wbr cdif cfv cc0 wb cv wa simpr dmeqd
      wceq unieqd simpl difeq12d fveq12d eqeq1d df-ae brabga ancoms ) ABEZFBGHI
      ZFABJKUIIZALZBMZNTZOCPZEZIZDPZLZUOMZNTUNDCABJUIUJURATZUOBTZQZUTUMNVCUSULU
      OBVAVBRZVCUQUKURAVCUPUIVCUOBVDSUAVAVBUBUCUDUECDUFUGUH $.
  $}

  ${
    $d a m x O $.  $d a m M $.  $d a m ph $.
    braew.1 $e |- U. dom M = O $.
    $( 'almost everywhere' relation for a measure ` M ` and a property ` ph `
       (Contributed by Thierry Arnoux, 20-Oct-2017.) $)
    braew $p |- ( M e. U. ran measures -> ( { x e. O | ph } ae M
      <-> ( M ` { x e. O | -. ph } ) = 0 ) ) $=
      ( vm va cmeas crn cuni wcel crab cae cdm cdif cfv cc0 wceq cvv cv wbr syl
      wn wb dmexg uniexd eqeltrrid rabexg wa simpr dmeqd simpl difeq12d fveq12d
      unieqd eqeq1d df-ae brabga mpancom difeq1i notrab fveq2i eqeq1i bitrdi
      eqtri ) CHIJZKZABDLZCMUAZCNZJZVHOZCPZQRZAUCBDLZCPZQRVHSKZVGVIVNUDVGDSKVQV
      GDVKSEVGVJSCVFUEUFUGABDSUHUBFTZNZJZGTZOZVRPZQRVNGFVHCMSVFWAVHRZVRCRZUIZWC
      VMQWFWBVLVRCWDWEUJZWFVTVKWAVHWFVSVJWFVRCWGUKUOWDWEULUMUNUPFGUQURUSVMVPQVL
      VOCVLDVHOVOVKDVHEUTABDVAVEVBVCVD $.
  $}

  ${
    $d x O $.  $d x ph $.
    truae.1 $e |- U. dom M = O $.
    truae.2 $e |- ( ph -> M e. U. ran measures ) $.
    truae.3 $e |- ( ph -> ps ) $.
    $( A truth holds almost everywhere.  (Contributed by Thierry Arnoux,
       20-Oct-2017.) $)
    truae $p |- ( ph -> { x e. O | ps } ae M ) $=
      ( crab cae wbr wn cfv cc0 wceq c0 wss wcel syl cmeas cv wi wral ralrimivw
      pm2.24d rabss sylibr ss0 fveq2d crn cuni measbasedom measvnul sylbi eqtrd
      cdm wb braew mpbird ) ABCEIDJKZBLZCEIZDMZNOZAVCPDMZNAVBPDAVBPQZVBPOAVACUA
      PRZUBZCEUCVFAVHCEABVGHUEUDVACEPUFUGVBUHSUIADTUJUKRZVENOZGVIDDUPZTMRVJDULV
      KDUMUNSUOAVIUTVDUQGBCDEFURSUS $.
  $}

  ${
    $d x O $.
    aean.1 $e |- U. dom M = O $.
    $( A conjunction holds almost everywhere if and only if both its terms do.
       (Contributed by Thierry Arnoux, 20-Oct-2017.) $)
    aean $p |- ( ( M e. U. ran measures /\ { x e. O | -. ph } e. dom M
      /\ { x e. O | -. ps } e. dom M ) -> ( { x e. O | ( ph /\ ps ) } ae M
      <-> ( { x e. O | ph } ae M /\ { x e. O | ps } ae M ) ) ) $=
      ( wcel wn crab cfv cc0 wceq cae wbr cle 3ad2ant1 adantr breqtrd syl3anc
      wa cmeas crn cuni cdm w3a wo unrab ianor rabbii eqtr4i fveq2i measbasedom
      cun eqeq1i biimpi simp2 csiga dmmeas unelsiga syl3an1 wss ssun1 a1i simpr
      measssd measle0 simp3 jca measbase syl cxad measunl simprl simprr oveq12d
      ssun2 co cxr 0xr xaddrid ax-mp eqtrdi impbida bitr3id wb anbi12d 3bitr4d
      braew ) DUAUBUCGZAHZCEIZDUDZGZBHZCEIZWLGZUEZABTZHZCEIZDJZKLZWKDJZKLZWODJZ
      KLZTZWRCEIDMNZACEIDMNZBCEIDMNZTZXBWKWOUMZDJZKLZWQXGXMXAKXLWTDXLWJWNUFZCEI
      WTWJWNCEUGWSXOCEABUHUIUJUKUNWQXNXGWQXNTZXDXFXPDWLUAJGZWMXCKONXDWQXQXNWIWM
      XQWPWIXQDULUOPZQZWQWMXNWIWMWPUPZQXPXCXMKOWQXCXMONXNWQWKXLWLDXRXTWIWLUQUBU
      CGZWMWPXLWLGZDURWKWOWLUSZUTZWKXLVAWQWKWOVBVCVEQWQXNVDZRWKWLDVFSXPXQWPXEKO
      NXFXSWQWPXNWIWMWPVGZQXPXEXMKOWQXEXMONXNWQWOXLWLDXRYFYDWOXLVAWQWOWKVPVCVEQ
      YERWOWLDVFSVHWQXGTZXQYBXMKONXNWQXQXGXRQZYGYAWMWPYBYGXQYAYHWLDVIVJWQWMXGXT
      QZWQWPXGYFQZYCSYGXMXCXEVKVQZKOYGWKWOWLDYHYIYJVLYGYKKKVKVQZKYGXCKXEKVKWQXD
      XFVMWQXDXFVNVOKVRGYLKLVSKVTWAWBRXLWLDVFSWCWDWIWMXHXBWEWPWRCDEFWHPWIWMXKXG
      WEWPWIXIXDXJXFACDEFWHBCDEFWHWFPWG $.
  $}

  ${
    $d r m f g x $.
    $( Define a builder for an 'almost everywhere' relation between functions,
       from relations between function values.  In this definition, the range
       of ` f ` and ` g ` is enforced in order to ensure the resulting relation
       is a set.  (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    df-fae $a |- ~ae = ( r e. _V , m e. U. ran measures |-> { <. f , g >. |
      ( ( f e. ( dom r ^m U. dom m ) /\ g e. ( dom r ^m U. dom m ) ) /\
        { x e. U. dom m | ( f ` x ) r ( g ` x ) } ae m ) } ) $.
  $}

  ${
    $d f g m r x M $.  $d f g m r x R $.
    $( Value of the 'almost everywhere' relation for a given relation and
       measure.  (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    faeval $p |- ( ( R e. _V /\ M e. U. ran measures ) ->
      ( R ~ae M ) = { <. f , g >. |
        ( ( f e. ( dom R ^m U. dom M ) /\ g e. ( dom R ^m U. dom M ) ) /\
          { x e. U. dom M | ( f ` x ) R ( g ` x ) } ae M ) } ) $=
      ( vr vm cuni cv cdm cmap co wcel wa cfv wbr crab cae copab wceq cvv cmeas
      crn cfae simpl dmeqd simpr unieqd oveq12d anbi12d breqd rabeqbidv breq12d
      eleq2d opabbidv df-fae cxp ovex xpex opabssxp ssexi ovmpoa ) FGBEUAUBUCHC
      IZFIZJZGIZJZHZKLZMZDIZVIMZNZAIZVCOZVNVKOZVDPZAVHQZVFRPZNZCDSVCBJZEJZHZKLZ
      MZVKWDMZNZVOVPBPZAWCQZERPZNZCDSZUDVDBTZVFETZNZVTWKCDWOVMWGVSWJWOVJWEVLWFW
      OVIWDVCWOVEWAVHWCKWOVDBWMWNUEZUFWOVGWBWOVFEWMWNUGZUFUHZUIZUNWOVIWDVKWSUNU
      JWOVRWIVFERWOVQWHAVHWCWRWOVDBVOVPWPUKULWQUMUJUOACDGFUPWLWDWDUQWDWDWAWCKUR
      ZWTUSWJCDWDWDUTVAVB $.
  $}

  ${
    $d f g x M $.  $d f g x R $.
    $( The 'almost everywhere' builder for functions produces relations.
       (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    relfae $p |- ( ( R e. _V /\ M e. U. ran measures ) -> Rel ( R ~ae M ) ) $=
      ( vf vg vx cvv wcel cmeas crn cuni wa cfae co wrel cdm cmap cfv wbr crab
      cv cae copab relopabv faeval releqd mpbiri ) AFGBHIJGKZABLMZNCTZAOBOJZPMZ
      GDTZUKGKETZUIQUMULQAREUJSBUARKZCDUBZNUNCDUCUGUHUOEACDBUDUEUF $.
  $}

  ${
    $d f g x F $.  $d f g x G $.  $d f g x M $.  $d f g x R $.
    brfae.0 $e |- dom R = D $.
    brfae.1 $e |- ( ph -> R e. _V ) $.
    brfae.2 $e |- ( ph -> M e. U. ran measures ) $.
    brfae.3 $e |- ( ph -> F e. ( D ^m U. dom M ) ) $.
    brfae.4 $e |- ( ph -> G e. ( D ^m U. dom M ) ) $.
    $( 'almost everywhere' relation for two functions ` F ` and ` G ` with
       regard to the measure ` M ` .  (Contributed by Thierry Arnoux,
       22-Oct-2017.) $)
    brfae $p |- ( ph -> ( F ( R ~ae M ) G
      <-> { x e. U. dom M | ( F ` x ) R ( G ` x ) } ae M ) ) $=
      ( vf vg cv cmap wcel wa cfv wbr cdm cuni co crab copab cfae wb wceq simpl
      cae eleq1d simpr anbi12d fveq1d breq12d rabbidv breq1d brabga syl2anc cvv
      eqid cmeas crn faeval breqd oveq1i eleqtrrdi jca biantrurd 3bitr4d ) AEFM
      OZDUAZGUAUBZPUCZQZNOZVNQZRZBOZVKSZVSVPSZDTZBVMUDZGUJTZRZMNUEZTZEVNQZFVNQZ
      RZVSESZVSFSZDTZBVMUDZGUJTZRZEFDGUFUCZTWOAECVMPUCZQFWRQWGWPUGKLWEWPMNEFWFW
      RWRVKEUHZVPFUHZRZVRWJWDWOXAVOWHVQWIXAVKEVNWSWTUIZUKXAVPFVNWSWTULZUKUMXAWC
      WNGUJXAWBWMBVMXAVTWKWAWLDXAVSVKEXBUNXAVSVPFXCUNUOUPUQUMWFVAURUSAWQWFEFADU
      TQGVBVCUBQWQWFUHIJBDMNGVDUSVEAWJWOAWHWIAEWRVNKVLCVMPHVFZVGAFWRVNLXDVGVHVI
      VJ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Measurable functions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c MblFnM $. $( Measurable function $)

  $( Extend class notation with the measurable functions builder. $)
  cmbfm $a class MblFnM $.

  ${
    $d f s t x $.
    $( Define the measurable function builder, which generates the set of
       measurable functions from a measurable space to another one.  Here, the
       measurable spaces are given using their sigma-algebras ` s ` and ` t ` ,
       and the spaces themselves are recovered by ` U. s ` and ` U. t ` .

       Note the similarities between the definition of measurable functions in
       measure theory, and of continuous functions in topology.

       This is the definition for the generic measure theory.  For the specific
       case of functions from ` RR ` to ` CC ` , see ~ df-mbf .  (Contributed
       by Thierry Arnoux, 23-Jan-2017.) $)
    df-mbfm $a |- MblFnM = ( s e. U. ran sigAlgebra , t e. U. ran sigAlgebra
      |-> { f e. ( U. t ^m U. s ) | A. x e. t ( `' f " x ) e. s } ) $.
  $}

  ${
    $d f x F $.  $d f s t x S $.  $d f s t x T $.
    ismbfm.1 $e |- ( ph -> S e. U. ran sigAlgebra ) $.
    ismbfm.2 $e |- ( ph -> T e. U. ran sigAlgebra ) $.
    $( The predicate " ` F ` is a measurable function from the measurable space
       ` S ` to the measurable space ` T ` ".  Cf. ~ ismbf .  (Contributed by
       Thierry Arnoux, 23-Jan-2017.) $)
    ismbfm $p |- ( ph -> ( F e. ( S MblFnM T ) <->
            ( F e. ( U. T ^m U. S ) /\ A. x e. T ( `' F " x ) e. S ) ) ) $=
      ( vf vs vt cmbfm co wcel cv ccnv wral cuni cmap crab wceq csiga crn unieq
      cima oveq2d eleq2 ralbidv rabeqbidv oveq1d raleq df-mbfm ovex rabex ovmpo
      wa syl2anc eleq2d cnveq imaeq1d eleq1d elrab bitrdi ) AECDKLZMEHNZOZBNZUD
      ZCMZBDPZHDQZCQZRLZSZMEVLMEOZVFUDZCMZBDPZUOAVCVMEACUAUBQZMDVRMVCVMTFGIJCDV
      RVRVGINZMZBJNZPZHWAQZVSQZRLZSVMKVHBWAPZHWCVKRLZSVSCTZWBWFHWEWGWHWDVKWCRVS
      CUCUEWHVTVHBWAVSCVGUFUGUHWADTZWFVIHWGVLWIWCVJVKRWADUCUIVHBWADUJUHBJHIUKVI
      HVLVJVKRULUMUNUPUQVIVQHEVLVDETZVHVPBDWJVGVOCWJVEVNVFVDEURUSUTUGVAVB $.
  $}

  ${
    $d x f $.  $d a s t F $.  $d f s t $.  $d s t x F $.
    $( The property of being a measurable function.  (Contributed by Thierry
       Arnoux, 23-Jan-2017.) $)
    elunirnmbfm $p |- ( F e. U. ran MblFnM <->
        E. s e. U. ran sigAlgebra E. t e. U. ran sigAlgebra
        ( F e. ( U. t ^m U. s ) /\ A. x e. t ( `' F " x ) e. s ) ) $=
      ( va vf cmbfm crn cuni wcel cv co csiga wrex cmap ccnv cima wral wa cfv
      cdm cxp wfun wb crab df-mbfm mpofun elunirn ax-mp ovex rabex dmmpo rexeqi
      cop wceq fveq2 df-ov eqtr4di eleq2d rexxp 3bitri simpl simpr ismbfm bitri
      2rexbiia ) CGHIJZCDKZBKZGLZJZBMHIZNDVLNZCVIIZVHIZOLZJCPAKZQVHJAVIRSZBVLND
      VLNVGCEKZGTZJZEGUAZNZWAEVLVLUBZNVMGUCVGWCUDDBVLVLFKPVQQVHJAVIRZFVPUEZGABF
      DUFZUGECGUHUIWAEWBWDDBVLVLWFGWGWEFVPVNVOOUJUKULUMWAVKEDBVLVLVSVHVIUNZUOZV
      TVJCWIVTWHGTVJVSWHGUPVHVIGUQURUSUTVAVKVRDBVLVLVHVLJZVIVLJZSAVHVICWJWKVBWJ
      WKVCVDVFVE $.
  $}

  ${
    $d s t x F $.
    mbfmfun.1 $e |- ( ph -> F e. U. ran MblFnM ) $.
    $( A measurable function is a function.  (Contributed by Thierry Arnoux,
       24-Jan-2017.) $)
    mbfmfun $p |- ( ph -> Fun F ) $=
      ( vt vs vx cmbfm cuni wcel cv cmap co ccnv cima wral csiga wrex rexlimivw
      crn wa wfun elunirnmbfm biimpi elmapfun adantr 3syl ) ABGSHIZBDJZHZEJZHZK
      LIZBMFJNUJIFUHOZTZDPSHZQZEUOQZBUAZCUGUQFDBEUBUCUPUREUOUNURDUOULURUMBUIUKU
      DUERRUF $.
  $}

  ${
    $d x F $.  $d x S $.  $d x T $.
    mbfmf.1 $e |- ( ph -> S e. U. ran sigAlgebra ) $.
    mbfmf.2 $e |- ( ph -> T e. U. ran sigAlgebra ) $.
    mbfmf.3 $e |- ( ph -> F e. ( S MblFnM T ) ) $.
    $( A measurable function as a function with domain and codomain.
       (Contributed by Thierry Arnoux, 25-Jan-2017.) $)
    mbfmf $p |- ( ph -> F : U. S --> U. T ) $=
      ( vx cuni cmap co wcel wf ccnv cv cima wral cmbfm wa ismbfm simpld elmapi
      mpbid syl ) ADCIZBIZJKLZUFUEDMAUGDNHOPBLHCQZADBCRKLUGUHSGAHBCDEFTUCUADUEU
      FUBUD $.

    $d x A $.
    mbfmcnvima.4 $e |- ( ph -> A e. T ) $.
    $( The preimage by a measurable function is a measurable set.  (Contributed
       by Thierry Arnoux, 23-Jan-2017.) $)
    mbfmcnvima $p |- ( ph -> ( `' F " A ) e. S ) $=
      ( vx ccnv cv cima wcel wceq imaeq2 eleq1d cuni cmap co cmbfm ismbfm mpbid
      wral wa simprd rspcdva ) AEKZJLZMZCNZUHBMZCNJDBUIBOUJULCUIBUHPQAEDRCRSTNZ
      UKJDUDZAECDUATNUMUNUEHAJCDEFGUBUCUFIUG $.
  $}

  ${
    isanmbfm.1 $e |- ( ph -> F e. ( S MblFnM T ) ) $.
    $( The predicate to be a measurable function.  (Contributed by Thierry
       Arnoux, 30-Jan-2017.)  Remove hypotheses.  (Revised by SN,
       13-Jan-2025.) $)
    isanmbfm $p |- ( ph -> F e. U. ran MblFnM ) $=
      ( cmbfm co crn cuni ovssunirn sselid ) ABCFGFHIDFBCJEK $.
  $}

  ${
    mbfmbfmOLD.1 $e |- ( ph -> M e. U. ran measures ) $.
    mbfmbfmOLD.2 $e |- ( ph -> J e. Top ) $.
    mbfmbfmOLD.3 $e |- ( ph -> F e. ( dom M MblFnM ( sigaGen ` J ) ) ) $.
    $( A measurable function to a Borel Set is measurable.  (Contributed by
       Thierry Arnoux, 24-Jan-2017.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    mbfmbfmOLD $p |- ( ph -> F e. U. ran MblFnM ) $=
      ( cdm csigagen cfv isanmbfm ) ADHCIJBGK $.
  $}

  ${
    mbfmbfm.1 $e |- ( ph -> F e. ( dom M MblFnM ( sigaGen ` J ) ) ) $.
    $( A measurable function to a Borel Set is measurable.  (Contributed by
       Thierry Arnoux, 24-Jan-2017.)  Remove hypotheses.  (Revised by SN,
       13-Jan-2025.) $)
    mbfmbfm $p |- ( ph -> F e. U. ran MblFnM ) $=
      ( cdm csigagen cfv isanmbfm ) ADFCGHBEI $.
  $}

  ${
    $d x A $.  $d y F $.  $d x y S $.  $d x y T $.  $d x y ph $.
    mbfmcst.1 $e |- ( ph -> S e. U. ran sigAlgebra ) $.
    mbfmcst.2 $e |- ( ph -> T e. U. ran sigAlgebra ) $.
    mbfmcst.3 $e |- ( ph -> F = ( x e. U. S |-> A ) ) $.
    mbfmcst.4 $e |- ( ph -> A e. U. T ) $.
    $( A constant function is measurable.  Cf. ~ mbfconst .  (Contributed by
       Thierry Arnoux, 26-Jan-2017.) $)
    mbfmcst $p |- ( ph -> F e. ( S MblFnM T ) ) $=
      ( vy wcel cuni ccnv cima adantr syl c0 cxp cdm cmbfm co cmap cv wf fmpt3d
      wral csiga crn unielsiga elmapd mpbird cmpt csn cin wceq fconstmpt cnveqi
      cres cnvxp eqtr3i imaeq1i df-ima df-rn 3eqtri cvv df-res inxp inv1 xpeq2i
      dmeqi xpeq2 xp0 eqtrdi dmeqd dm0 adantl 0elsiga eqeltrd eqeltrid wne dmxp
      wa pm2.61dane ralrimivw cnveqd imaeq1d eleq1d ralbidv ismbfm mpbir2and )
      AFDEUAUBLFEMZDMZUCUBLZFNZKUDZOZDLZKEUGZAWNWMWLFUEABWMCWLFIACWLLBUDWMLJPUF
      AWLWMFEDAEUHUIMZLWLELHEUJQADWTLZWMDLZGDUJQZUKULAWSBWMCUMZNZWPOZDLZKEUGAXG
      KEAXGCUNZWPUOZRAXIRUPZWCZXFWMXISZTZDXFXHWMSZWPUSZNZTZXIWMSZNZTXMXFXNWPOXO
      UIXQXEXNWPWMXHSZNXEXNXTXDBWMCUQURWMXHUTVAVBXNWPVCXOVDVEXPXSXOXRXOXNWPVFSU
      OXIWMVFUOZSXRXNWPVGXHWMWPVFVHYAWMXIWMVIVJVEURVKXSXLXIWMUTVKVEZXKXMRDXJXMR
      UPAXJXMRTRXJXLRXJXLWMRSRXIRWMVLWMVMVNVOVPVNVQARDLZXJAXAYCGDVRQPVSVTAXIRWA
      ZWCZXFXMDYBYEXMWMDYDXMWMUPAWMXIWBVQAXBYDXCPVSVTWDWEAWRXGKEAWQXFDAWOXEWPAF
      XDIWFWGWHWIULAKDEFGHWJWK $.
  $}

  ${
    $d a z S $.  $d a z T $.  $d a z ph $.
    1stmbfm.1 $e |- ( ph -> S e. U. ran sigAlgebra ) $.
    1stmbfm.2 $e |- ( ph -> T e. U. ran sigAlgebra ) $.
    $( The first projection map is measurable with regard to the product
       sigma-algebra.  (Contributed by Thierry Arnoux, 3-Jun-2017.) $)
    1stmbfm $p |- ( ph -> ( 1st |` ( U. S X. U. T ) )
                                               e. ( ( S sX T ) MblFnM S ) ) $=
      ( va vz c1st cuni cxp co wcel csiga wceq syl2anc syl wa cfv wss adantr cv
      cres csx cmbfm cmap ccnv cima wral wf f1stres sxuni feq2d mpbii unielsiga
      crn sxsiga elmapd mpbird wfn wb ffn elpreima mp2b eleq1d c2nd cop 1st2nd2
      fvres xp2nd elxp6 anass an32 3bitr2i baib pm5.32i bitri cpw sgon sigasspw
      bitr4d pwssb biimpi 4syl r19.21bi xpss1 sseld pm4.71rd bitr4id eqrdv eqid
      simpr issgon sylanblrc baselsiga elsx syl22anc ralrimiva ismbfm mpbir2and
      eqeltrd ) AHBIZCIZJZUBZBCUCKZBUDKLXDXAXEIZUEKLZXDUFFUAZUGZXELZFBUHAXGXFXA
      XDUIZAXCXAXDUIZXKXAXBUJZAXCXFXAXDABMUOIZLZCXNLZXCXFNDEBCUKOULUMAXAXFXDBXE
      AXOXABLDBUNPAXEXNLZXFXELAXOXPXQDEBCUPOZXEUNPUQURAXJFBAXHBLZQZXIXHXBJZXEXT
      GXIYAXTGUAZXILZYBXCLZYBYALZQZYEYCYDYBXDRZXHLZQZYFXLXDXCUSYCYIUTXMXCXAXDVA
      XCYBXHXDVBVCYDYHYEYDYHYBHRZXHLZYEYDYGYJXHYBXCHVHVDYDYBYJYBVERZVFNZYLXBLZY
      EYKUTYBXAXBVGYBXAXBVIYEYMYNQZYKYEYMYKYNQQYMYKQYNQYOYKQYBXHXBVJYMYKYNVKYMY
      KYNVLVMVNOVTVOVPXTYEYDXTYAXCYBXTXHXASZYAXCSAYPFBAXOBXAMRLBXAVQSZYPFBUHZDB
      VRXABVSYQYRFBXAWAWBWCWDXHXAXBWEPWFWGWHWIXTXOXPXSXBCLZYAXELAXOXSDTAXPXSETA
      XSWKAYSXSACXBMRLZYSAXPXBXBNYTEXBWJCXBWLWMXBCWNPTXHXBBCXNXNWOWPWTWQAFXEBXD
      XRDWRWS $.

    $( The second projection map is measurable with regard to the product
       sigma-algebra.  (Contributed by Thierry Arnoux, 3-Jun-2017.) $)
    2ndmbfm $p |- ( ph -> ( 2nd |` ( U. S X. U. T ) )
                                                e. ( ( S sX T ) MblFnM T ) ) $=
      ( va vz c2nd cuni cxp co wcel csiga wceq syl2anc syl wa cfv wss adantr cv
      cres csx cmbfm cmap ccnv cima wral wf f2ndres sxuni feq2d mpbii unielsiga
      crn sxsiga elmapd mpbird wfn wb ffn elpreima mp2b eleq1d c1st cop 1st2nd2
      fvres xp1st elxp6 anass bitr4i baib pm5.32i bitri cpw sgon sigasspw pwssb
      bitr4d biimpi 4syl r19.21bi xpss2 sseld pm4.71rd bitr4id issgon sylanblrc
      eqrdv eqid baselsiga simpr syl22anc eqeltrd ralrimiva ismbfm mpbir2and
      elsx ) AHBIZCIZJZUBZBCUCKZCUDKLXCXAXDIZUEKLZXCUFFUAZUGZXDLZFCUHAXFXEXAXCU
      IZAXBXAXCUIZXJWTXAUJZAXBXEXAXCABMUOIZLZCXMLZXBXENDEBCUKOULUMAXAXEXCCXDAXO
      XACLECUNPAXDXMLZXEXDLAXNXOXPDEBCUPOZXDUNPUQURAXIFCAXGCLZQZXHWTXGJZXDXSGXH
      XTXSGUAZXHLZYAXBLZYAXTLZQZYDYBYCYAXCRZXGLZQZYEXKXCXBUSYBYHUTXLXBXAXCVAXBY
      AXGXCVBVCYCYGYDYCYGYAHRZXGLZYDYCYFYIXGYAXBHVHVDYCYAYAVERZYIVFNZYKWTLZYDYJ
      UTYAWTXAVGYAWTXAVIYDYLYMQZYJYDYLYMYJQQYNYJQYAWTXGVJYLYMYJVKVLVMOVTVNVOXSY
      DYCXSXTXBYAXSXGXASZXTXBSAYOFCAXOCXAMRLCXAVPSZYOFCUHZECVQXACVRYPYQFCXAVSWA
      WBWCXGXAWTWDPWEWFWGWJXSXNXOWTBLZXRXTXDLAXNXRDTAXOXRETAYRXRABWTMRLZYRAXNWT
      WTNYSDWTWKBWTWHWIWTBWLPTAXRWMWTXGBCXMXMWSWNWOWPAFXDCXCXQEWQWR $.
  $}

  ${
    $d a x y F $.  $d a x y K $.  $d a x y S $.  $d a x y T $.  $d a x y ph $.
    imambfm.1 $e |- ( ph -> K e. _V ) $.
    imambfm.2 $e |- ( ph -> S e. U. ran sigAlgebra ) $.
    imambfm.3 $e |- ( ph -> T = ( sigaGen ` K ) ) $.
    $( If the sigma-algebra in the range of a given function is generated by a
       collection of basic sets ` K ` , then to check the measurability of that
       function, we need only consider inverse images of basic sets ` a ` .
       (Contributed by Thierry Arnoux, 4-Jun-2017.) $)
    imambfm $p |- ( ph -> ( F e. ( S MblFnM T )
                <-> ( F : U. S --> U. T /\ A. a e. K ( `' F " a ) e. S ) ) ) $=
      ( vx vy wcel cuni cima wral wa adantr wss syl wceq cmbfm co wf ccnv csiga
      crn csigagen cfv cvv sgsiga eqeltrd simpr mbfmf ad2antrr simplr sssigagen
      cv sseqtrrd sseldd mbfmcnvima ralrimiva jca cmap unielsiga simprl biimpar
      elmapg syl21anc crab cpw cdif com wbr wi w3a simpl ssrab2 pwuni sstri a1i
      cdom fimacnv ad2antrl imaeq2 eleq1d elrab elrabi adantl difelsiga syl3anc
      sylanbrc wfun simplrl ffun difpreima 3syl difeq1d simprbi ad3antrrr sspwi
      sseli ad2antlr sigaclcu ciun simpllr unipreima elelpwi syl2anc sigaclcuni
      simpld nfcv ex wb rabexg issiga syl12anc unieqd unisg eqtrd fveq2d eleq2d
      mpbid simprr ssrab sigagenss eqsstrd eqssd rabid2 sylib mpbir2and impbida
      3jca ismbfm ) ADBCUAUBLZBMZCMZDUCZDUDZFUQZNZBLZFEOZPZAYNPZYQUUBUUDBCDABUE
      UFMZLZYNHQACUUELZYNACEUGUHZUUEIAEUIGUJUKZQAYNULUMUUDUUAFEUUDYSELZPZYSBCDA
      UUFYNUUJHUNAUUGYNUUJUUIUNAYNUUJUOUUKECYSAECRZYNUUJAEUUHCAEUILZEUUHRGEUIUP
      SIURZUNUUDUUJULUSUTVAVBAUUCPZYNDYPYOVCUBLZUUAFCOZUUOYPCLZYOBLZYQUUPAUURUU
      CAUUGUURUUICVDZSQZAUUSUUCAUUFUUSHBVDZSQZAYQUUBVEUURUUSPUUPYQYPYODCBVGVFVH
      UUOCUUAFCVIZTUUQUUOCUVDUUOCUUHUVDACUUHTUUCIQUUOUVDEMZUEUHZLZEUVDRZUUHUVDR
      UUOUVDYPUEUHZLZUVGUUOAUVDYPVJZRZYPUVDLZYPJUQZVKZUVDLZJUVDOZUVNVLWAVMZUVNM
      ZUVDLZVNZJUVDVJZOZVOZUVJAUUCVPUVLUUOUVDCUVKUUAFCVQZCVRVSVTUUOUVMUVQUWCUUO
      UURYRYPNZBLZUVMUVAUUOUWFYOBYQUWFYOTAUUBYOYPDWBWCZUVCUKUUAUWGFYPCYSYPTYTUW
      FBYSYPYRWDWEWFWKUUOUVPJUVDUUOUVNUVDLZPZUVOCLZYRUVONZBLZUVPUWJUUGUURUVNCLZ
      UWKAUUGUUCUWIUUIUNZUWJUUGUURUWOUUTSUWIUWNUUOUUAFUVNCWGWHYPUVNCWIWJUWJUWLU
      WFYRUVNNZVKZBUWJYQDWLZUWLUWQTAYQUUBUWIWMYOYPDWNZYPUVNDWOWPUWJUWQYOUWPVKZB
      UUOUWQUWTTUWIUUOUWFYOUWPUWHWQQUWJUUFUUSUWPBLZUWTBLAUUFUUCUWIHUNZUWJUUFUUS
      UXBUVBSUWIUXAUUOUWIUWNUXAUUAUXAFUVNCYSUVNTYTUWPBYSUVNYRWDWEWFWRWHYOUWPBWI
      WJUKUKUUAUWMFUVOCYSUVOTYTUWLBYSUVOYRWDWEWFWKVAUUOUWAJUWBUUOUVNUWBLZPZUVRU
      VTUXDUVRPZUVSCLZYRUVSNZBLZUVTUXEUUGUVNCVJZLZUVRUXFAUUGUUCUXCUVRUUIWSUXCUX
      JUUOUVRUWBUXIUVNUVDCUWEWTXAXBUXDUVRULZUVNCXCWJUXEUXGKUVNYRKUQZNZXDZBUXEYQ
      UWRUXGUXNTUXEYQUUBAUUCUXCUVRXEXJUWSKUVNDXFWPUXEUUFUXMBLZKUVNOUVRUXNBLAUUF
      UUCUXCUVRHWSUXEUXOKUVNUXEUXLUVNLZPZUXLUVDLZUXOUXQUXPUXCUXRUXEUXPULUUOUXCU
      VRUXPXEUXLUVNUVDXGXHUXRUXLCLUXOUUAUXOFUXLCYSUXLTYTUXMBYSUXLYRWDWEWFWRSVAU
      XKUVNUXMBKKUVNXKXIWJUKUUAUXHFUVSCYSUVSTYTUXGBYSUVSYRWDWEWFWKXLVAYLAUVJUVL
      UWDPZAUUGUVDUILUVJUXSXMUUIUUAFCUUEXNJUVDYPXOWPVFXPAUVJUVGXMUUCAUVIUVFUVDA
      YPUVEUEAYPUUHMZUVEACUUHIXQAUUMUXTUVETGEUIXRSXSXTYAQYBUUOUULUUBUVHAUULUUCU
      UNQAYQUUBYCUUAFCEYDWKEUVDYEXHYFUVDCRUUOUWEVTYGUUAFCYHYIUUOFBCDAUUFUUCHQAU
      UGUUCUUIQYMYJYK $.
  $}

  ${
    $d a F $.  $d a K $.  $d a S $.  $d a T $.  $d a ph $.
    cnmbfm.1 $e |- ( ph -> F e. ( J Cn K ) ) $.
    cnmbfm.2 $e |- ( ph -> S = ( sigaGen ` J ) ) $.
    cnmbfm.3 $e |- ( ph -> T = ( sigaGen ` K ) ) $.
    $( A continuous function is measurable with respect to the Borel Algebra of
       its domain and range.  (Contributed by Thierry Arnoux, 3-Jun-2017.) $)
    cnmbfm $p |- ( ph -> F e. ( S MblFnM T ) ) $=
      ( va co wcel cuni wf eqid syl csigagen cfv ctop 3syl cmbfm ccnv cima wral
      ccn cnf unieqd wceq cntop1 unisg eqtrd cntop2 feq23d mpbird wss sssigagen
      cv wa sseqtrrd adantr cnima sylan sseldd ralrimiva elex csiga sigagensiga
      cvv crn eqeltrd elrnsiga imambfm mpbir2and ) ADBCUAKLBMZCMZDNZDUBJUQZUCZB
      LZJFUDAVPEMZFMZDNZADEFUEKLZWBGDEFVTWAVTOWAOUFPAVNVOVTWADAVNEQRZMZVTABWDHU
      GAWCESLZWEVTUHGDEFUIZESUJTUKAVOFQRZMZWAACWHIUGAWCFSLZWIWAUHGDEFULZFSUJTUK
      UMUNAVSJFAVQFLZUREBVRAEBUOWLAEWDBAWCWFEWDUOGWGESUPTHUSUTAWCWLVRELGVQDEFVA
      VBVCVDABCDFJAWCWJFVHLGWKFSVETABVTVFRZLBVFVIMLABWDWMHAWCWFWDWMLGWGESVGTVJB
      VTVKPIVLVM $.
  $}

  ${
    mbfmco.1 $e |- ( ph -> R e. U. ran sigAlgebra ) $.
    mbfmco.2 $e |- ( ph -> S e. U. ran sigAlgebra ) $.
    mbfmco.3 $e |- ( ph -> T e. U. ran sigAlgebra ) $.
    ${
      $d a F $.  $d a G $.  $d a R $.  $d a T $.  $d a ph $.
      mbfmco.4 $e |- ( ph -> F e. ( R MblFnM S ) ) $.
      mbfmco.5 $e |- ( ph -> G e. ( S MblFnM T ) ) $.
      $( The composition of two measurable functions is measurable.  See
         ~ cnmpt11 .  (Contributed by Thierry Arnoux, 4-Jun-2017.) $)
      mbfmco $p |- ( ph -> ( G o. F ) e. ( R MblFnM T ) ) $=
        ( va cmbfm co wcel cuni ccnv cima wf adantr ccom cmap cv wral mbfmf fco
        syl2anc csiga crn unielsiga syl elmapd mpbird cnvco imaeq1i imaco eqtri
        wa simpr mbfmcnvima eqeltrid ralrimiva ismbfm mpbir2and ) AFEUAZBDMNOVE
        DPZBPZUBNOZVEQZLUCZRZBOZLDUDAVHVGVFVESZACPZVFFSVGVNESVMACDFHIKUEABCEGHJ
        UEVGVNVFFEUFUGAVFVGVEDBADUHUIPZOZVFDOIDUJUKABVOOZVGBOGBUJUKULUMAVLLDAVJ
        DOZURZVKEQZFQZVJRZRZBVKVTWAUAZVJRWCVIWDVJFEUNUOVTWAVJUPUQVSWBBCEAVQVRGT
        ACVOOVRHTZAEBCMNOVRJTVSVJCDFWEAVPVRITAFCDMNOVRKTAVRUSUTUTVAVBALBDVEGIVC
        VD $.
    $}

    ${
      $d a b c H $.  $d a b c R $.  $d a b c S $.  $d a b c T $.
      $d a b c ph $.  $d x R $.  $d x S $.  $d x T $.  $d x ph $.  $d x F $.
      $d x G $.  $d x H $.
      mbfmco2.4 $e |- ( ph -> F e. ( R MblFnM S ) ) $.
      mbfmco2.5 $e |- ( ph -> G e. ( R MblFnM T ) ) $.
      mbfmco2.6 $e |- H = ( x e. U. R |-> <. ( F ` x ) , ( G ` x ) >. ) $.
      $( The pair building of two measurable functions is measurable.  ( cf.
         ~ cnmpt1t ).  (Contributed by Thierry Arnoux, 6-Jun-2017.) $)
      mbfmco2 $p |- ( ph -> H e. ( R MblFnM ( S sX T ) ) ) $=
        ( vc va vb wcel cuni 3ad2ant1 csx co cmbfm wf ccnv cv cima cxp cmpo crn
        wral cfv cop mbfmf ffvelcdmda opelxpi syl2anc wceq csiga adantr eleqtrd
        wa sxuni fmptd wrex eqid vex xpex elrnmpo w3a simp3 simp1 simp2l simp2r
        imaeq2d xppreima2 mbfmcnvima inelsiga syl3anc eqeltrd 3expia rexlimdvva
        cin simp2 imp sylan2b ralrimiva cvv txbasex csigagen imambfm mpbir2and
        sxval ) AHCDEUAUBZUCUBRCSZWNSZHUDHUEZOUFZUGZCRZOPQDEPUFZQUFZUHZUIZUJZUK
        ABWOBUFZFULZXFGULZUMZWPHAXFWORZVBZXIDSZESZUHZWPXKXGXLRXHXMRXIXNRAWOXLXF
        FACDFIJLUNZUOAWOXMXFGACEGIKMUNZUOXGXHXLXMUPUQAXNWPURZXJADUSUJSZRZEXRRZX
        QJKDEVCUQUTVANVDAWTOXEWRXERAWRXCURZQEVEPDVEZWTPQDEXCWRXDXDVFXAXBPVGQVGV
        HVIAYBWTAYAWTPQDEAXADRZXBERZVBZYAWTAYEYAVJZWSWQXCUGZCYFWRXCWQAYEYAVKVOY
        FAYCYDYGCRAYEYAVLAYCYDYAVMAYCYDYAVNAYCYDVJZYGFUEXAUGZGUEXBUGZWCZCAYCYGY
        KURYDABWOXLXMFGHXAXBXOXPNVPTYHCXRRZYICRYJCRYKCRAYCYLYDITZYHXACDFYMAYCXS
        YDJTAYCFCDUCUBRYDLTAYCYDWDVQYHXBCEGYMAYCXTYDKTAYCGCEUCUBRYDMTAYCYDVKVQY
        IYJCVRVSVTVSVTWAWBWEWFWGACWNHXEOAXSXTXEWHRJKPQXEDEXRXRXEVFZWIUQIAXSXTWN
        XEWJULURJKPQXEDEXRXRYNWMUQWKWL $.
    $}
  $}

  $( Measurable functions with respect to the Lebesgue measure are real-valued
     functions on the real numbers.  (Contributed by Thierry Arnoux,
     27-Mar-2017.) $)
  mbfmvolf $p |- ( F e. ( dom vol MblFnM BrSiga ) -> F : RR --> RR ) $=
    ( cvol cdm cbrsiga cmbfm co wcel cuni wf cr csiga crn wceq wa issgon simpli
    cfv mpbi a1i simpri dmvlsiga brsigarn id mbfmf feq23i sylibr ) ABCZDEFGZUGH
    ZDHZAIJJAIUHUGDAUGKLHZGZUHULJUIMZUGJKQZGULUMNUAUGJORZPSDUKGZUHUPJUJMZDUNGUP
    UQNUBDJORZPSUHUCUDJJUIUJAULUMUOTUPUQURTUEUF $.

$(
  @{
    @d x F @.
    mbfmvol.1 @e |- S = ( sigaGen ` ( MetOpen ` ( abs o. - ) ) ) @.
    @( Measurable functions with respect to the Lebesgue measure are
       complex-valued functions in ` MblFn ` .
       (Contributed by Thierry Arnoux, 27-Mar-2017.) @)
    mbfmvol @p |- ( MblFnM ` <. dom vol , S >. )
                                                = ( MblFn i^i ( CC ^m RR ) ) @=
      ? @.
      @( [27-Mar-2017] @)
  @}

  @{
    @d x F @.
    @( Measurable functions with respect to the Lebesgue measure are
       real-valued functions in ` MblFn ` .
       (Contributed by Thierry Arnoux, 27-Mar-2017.) @)
    elmbfmvol @p |- ( F e. ( MblFnM ` <. dom vol , BrSiga >. ) <->
                                          ( F e. MblFn /\ F : RR --> RR ) ) @=
      ? @.
      @( [27-Mar-2017] @)
  @}
$)

  ${
    $d x F $.
    $( Measurable functions with respect to the Lebesgue measure.  We only have
       the inclusion, since ` MblFn ` includes complex-valued functions.
       (Contributed by Thierry Arnoux, 26-Jan-2017.) $)
    elmbfmvol2 $p |- ( F e. ( dom vol MblFnM BrSiga ) -> F e. MblFn ) $=
      ( vx cvol cbrsiga co wcel crn wral wss cfv ctb ax-mp ctop cuni cmap wb cr
      csiga elrnsiga mp1i cdm cmbfm cmbf ccnv cima cioo csigagen retopbas bastg
      cv ctg retop sssigagen sstri df-brsiga sseqtrri wceq wa dmvlsiga brsigarn
      eqid ismbfm simprbi ssralv mpsyl simplbi elmapi unibrsiga unidmvol eleq2s
      wf oveq12i ismbf 3syl mpbird ) ACUAZDUBEFZAUCFZAUDBUJUEVPFZBUFGZHZVTDIVQV
      SBDHZWAVTVTUKJZUGJZDVTWCWDVTKFVTWCIUHVTKUILWCMFWCWDIULWCMUMLUNUOUPVQADNZV
      PNZOEZFZWBCCUQZVQWHWBURPCVAWIBVPDAVPQRJZFVPRGNZFWIUSVPQSTDWJFDWKFWIUTDQST
      VBLZVCVSBVTDVDVEVQWHQQAVKZVRWAPVQWHWBWLVFWMAQQOEWGAQQVGWEQWFQOVHVIVLVJBQA
      VMVNVO $.
  $}

  ${
    $d f x y O $.  $d f V $.
    $( All functions are measurable with respect to the counting measure.
       (Contributed by Thierry Arnoux, 24-Jan-2017.) $)
    mbfmcnt $p |- ( O e. V -> ( ~P O MblFnM BrSiga ) = ( RR ^m O ) ) $=
      ( vf vx vy wcel cbrsiga co cuni cmap cr cv wa csiga elrnsiga wf unibrsiga
      cfv cvv biimtrdi cpw cmbfm ccnv cima wral crn pwsiga brsigarn mp1i ismbfm
      syl wfn wb reex eqeltri unipw elex eqeltrid elmapg sylancr bitrdi ffn wss
      feq2i elpreima simpl ssrdv vex cnvex imaexg elpw sylibr ralrimivw pm4.71d
      ax-mp syl6 bitr4d eqrdv oveq12i eqtrdi ) ABFZAUAZGUBHZGIZWBIZJHZKAJHWACWC
      WFWACLZWCFWGWFFZWGUCZDLZUDZWBFZDGUEZMWHWADWBGWGWAWBANRFWBNUFIZFABUGWBAOUK
      GKNRFGWNFWAUHGKOUIUJWAWHWMWAWHWGAULZWMWAWHAWDWGPZWOWAWHWEWDWGPZWPWAWDSFWE
      SFWHWQUMWDKSQUNUOWAWEASAUPZABUQURWDWEWGSSUSUTWEAWDWGWRVDVAAWDWGVBTWOWLDGW
      OWKAVCWLWOEWKAWOELZWKFWSAFZWSWGRWJFZMWTAWSWJWGVEWTXAVFTVGWKAWISFWKSFWGCVH
      VIWIWJSVJVOVKVLVMVPVNVQVRWDKWEAJQWRVSVT $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Borel Algebra on ` ( RR X. RR ) `
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y $.
    $( The base set for the generator of the Borel sigma-algebra on
       ` ( RR X. RR ) ` is indeed ` ( RR X. RR ) ` .  (Contributed by Thierry
       Arnoux, 22-Sep-2017.) $)
    br2base $p |- U. ran ( x e. BrSiga , y e. BrSiga |-> ( x X. y ) )
       = ( RR X. RR ) $=
      ( cbrsiga cv cxp crn cr cpw cuni wceq wcel wral brsigasspwrn sseli elpwid
      wss vex eqid ax-mp wrex cmpo xpss12 syl2an xpex elpw sylibr rgen2 rnmposs
      wa wb unibrsiga csiga cfv brsigarn elrnsiga unielsiga mp2b eqeltrri xpeq1
      eqeq2d xpeq2 rspc2ev mp3an elrnmpo mpbir elpwuni mpbi ) ABCCADZBDZEZUAZFZ
      GGEZHZPZVLIVMJZVJVNKZBCLACLVOVQABCCVHCKZVICKZUIVJVMPZVQVRVHGPVIGPVTVSVRVH
      GCGHZVHMNOVSVIGCWAVIMNOVHGVIGUBUCVJVMVHVIAQBQUDZUEUFUGABCCVJVNVKVKRZUHSVM
      VLKZVOVPUJWDVMVJJZBCTACTZGCKZWGVMVMJZWFCIZGCUKCGULUMKCULFIKWICKUNCGUOCUPU
      QURZWJVMRWEWHVMGVIEZJABGGCCVHGJVJWKVMVHGVIUSUTVIGJWKVMVMVIGGVAUTVBVCABCCV
      JVMVKWCWBVDVEVLVMVFSVG $.
  $}

  $( An upper bound for a dyadic number.  (Contributed by Thierry Arnoux,
     19-Sep-2017.) $)
  dya2ub $p |- ( R e. RR+ ->
      ( 1 / ( 2 ^ ( |_ ` ( 1 - ( 2 logb R ) ) ) ) ) < R ) $=
    ( crp wcel c1 c2 clogb co cmin cfl cfv clt wbr cneg caddc cr relogbzcl wceq
    cz sylancl syl2anc cexp cdiv cuz uzid ax-mp mpan renegcld flltp1 syl fladdz
    2z 1z cc recnd ax-1cn negsubdi negsubdi2 eqtr3d fveq2d breqtrd a1i 2rp 1red
    wa resubcld flcld rpexpcld rpreccld logblt syl3anc logbrec breq1d ltnegcon1
    wb id 3bitrd nnlogbexp breq2d bitrd mpbird ) ABCZDEDEAFGZHGZIJZUAGZUBGZAKLZ
    WBMZWDKLZWAWHWHIJDNGZWDKWAWHOCZWHWJKLWAWBEEUCJCZWAWBOCZERCWLUKEUDUEZEAPUFZU
    GZWHUHUIWAWHDNGZIJZWJWDWAWKDRCWRWJQWPULWHDUJSWAWQWCIWAWBUMCZDUMCZWQWCQWAWBW
    OUNUOWSWTVDWBDHGMWQWCWBDUPWBDUQURSUSURUTWAWGWHEWEFGZKLZWIWAWGEWFFGZWBKLZXAM
    ZWBKLZXBWAWLWFBCWAWGXDVNWLWAWNVAZWAWEWAEWDEBCWAVBVAWAWCWADWBWAVCWOVEVFZVGZV
    HWAVOEWFAVIVJWAXCXEWBKWAWLWEBCZXCXEQXGXIWEEVKTVLWAXAOCZWMXFXBVNWAWLXJXKXGXI
    EWEPTWOXAWBVMTVPWAXAWDWHKWAWLWDRCXAWDQXGXHEWDVQTVRVSVT $.

  ${
    $d e f z $.
    $( The closed half-spaces of ` ( RR X. RR ) ` cover ` ( RR X. RR ) ` .
       (Contributed by Thierry Arnoux, 11-Oct-2017.) $)
    sxbrsigalem0 $p |- U. ( ran ( e e. RR |-> ( ( e [,) +oo ) X. RR ) )
      u. ran ( f e. RR |-> ( RR X. ( f [,) +oo ) ) ) ) = ( RR X. RR ) $=
      ( vz cr cv cpnf cico co cxp cmpt cuni wss wcel pnfxr syl ovex reex cfv wa
      xpex crn cun unissb wo elun cpw eqid rnmptss cxr icossre mpan2 xpss1 elpw
      sylibr mprg sseli xpss2 jaoi sylbi mprgbir c1st cvv c2nd clt wbr rexr a1i
      elpwid ltpnf lbico1 syl3anc anim1i anim2i elxp7 3imtr4i wceq xp1st xpeq1d
      oveq1 fvmpt eleqtrrd elfvunirn ssriv ssun3 ax-mp uniun sseqtrri eqssi ) A
      DAEZFGHZDIZJZUAZBDDBEZFGHZIZJZUAZUBZKZDDIZWTXALCEZXALZCWSCWSXAUCXBWSMXBWM
      MZXBWRMZUDXCXBWMWRUEXDXCXEXDXBXAWMXAUFZXBWKXFMZWMXFLADADWKXFWLWLUGZUHWIDM
      ZWKXALZXGXIWJDLZXJXIFUIMZXKNWIFUJUKWJDDULOWKXAWJDWIFGPQTUMUNUOUPVHXEXBXAW
      RXFXBWPXFMZWRXFLBDBDWPXFWQWQUGUHWNDMZWPXALZXMXNWODLZXOXNXLXPNWNFUJUKWODDU
      QOWPXADWOQWNFGPTUMUNUOUPVHURUSUTXAWMKZWRKZUBZWTXAXQLXAXSLCXAXQXBXAMZXBXBV
      ARZWLRZMXBXQMXTXBYAFGHZDIZYBXBVBVBIMZYADMZXBVCRDMZSZSYEYAYCMZYGSZSXTXBYDM
      YHYJYEYFYIYGYFYAUIMXLYAFVDVEYIYAVFXLYFNVGYAVIYAFVJVKVLVMXBDDVNXBYCDVNVOXT
      YFYBYDVPXBDDVQAYAWKYDDWLWIYAVPWJYCDWIYAFGVSVRXHYCDYAFGPQTVTOWAYAXBWLWBOWC
      XAXQXRWDWEWMWRWFWGWH $.
  $}

  ${
    sxbrsiga.0 $e |- J = ( topGen ` ran (,) ) $.

    ${
      $d e f u v $.  $d u v J $.
      $( The sigma-algebra generated by the closed half-spaces of
         ` ( RR X. RR ) ` is a subset of the sigma-algebra generated by the
         closed sets of ` ( RR X. RR ) ` .  (Contributed by Thierry Arnoux,
         11-Oct-2017.) $)
      sxbrsigalem3 $p |-
         ( sigaGen ` ( ran ( e e. RR |-> ( ( e [,) +oo ) X. RR ) )
                    u. ran ( f e. RR |-> ( RR X. ( f [,) +oo ) ) ) ) )
           C_ ( sigaGen ` ( Clsd ` ( J tX J ) ) ) $=
        ( vu vv cr cv cpnf cico co cxp cuni ccld cfv wss wcel ovex reex xpex c0
        cmpt crn cun ctx wceq csigagen cvv sxbrsigalem0 cioo ctop retop eqeltri
        ctg txtopi uniretop unieqi eqtr4i txunii unicls wfn wral eqid weq oveq1
        fnmpti xpeq1d fvmpt icopnfcld fveq2i eleqtrrdi cdif dif0 ax-mp eqeltrri
        0opn opncld mp2an txcld sylancl eqeltrd rgen fnfvrnss xpeq2d unssi fvex
        sylancr sssigagen sstri sigagenss2 mp3an ) AGAHZIJKZGLZUBZUCZBGGBHZIJKZ
        LZUBZUCZUDZMZCCUEKZNOZMZUFXBXEUGOZPXEUHQZXBUGOXGPXCGGLZXFABUIXDXICCCUJU
        CUNOZUKDULUMZXKUOCCGGXKXKGXJMCMUPCXJDUQURZXLUSUTURXBXEXGWPXAXEWOGVAEHZW
        OOZXEQZEGVBWPXEPAGWNWOWMGWLIJRSTWOVCZVFXOEGXMGQZXNXMIJKZGLZXEAXMWNXSGWO
        AEVDWMXRGWLXMIJVEVGXPXRGXMIJRSTVHXQXRCNOZQGXTQZXSXEQXQXRXJNOZXTXMVICXJN
        DVJZVKGUAVLZGXTGVMCUKQZUACQZYDXTQXKYEYFXKCVPVNUACGXLVQVRVOZXRGCCVSVTWAW
        BEGXEWOWCVRWTGVAFHZWTOZXEQZFGVBXAXEPBGWSWTGWRSWQIJRTWTVCZVFYJFGYHGQZYIG
        YHIJKZLZXEBYHWSYNGWTBFVDWRYMGWQYHIJVEWDYKGYMSYHIJRTVHYLYAYMXTQYNXEQYGYL
        YMYBXTYHVIYCVKGYMCCVSWGWAWBFGXEWTWCVRWEXHXEXGPXDNWFZXEUHWHVNWIYOXBXEUHW
        JWK $.
    $}

    ${
      $d x n $.
      dya2ioc.1 $e |- I = ( x e. ZZ , n e. ZZ |->
                       ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) ) $.

      ${
        $d m n u x $.  $d m u N $.  $d m u X $.
        $( The function ` I ` returns closed-below open-above dyadic rational
           intervals covering the real line.  This is the same construction as
           in ~ dyadmbl .  (Contributed by Thierry Arnoux, 24-Sep-2017.) $)
        dya2iocival $p |- ( ( N e. ZZ /\ X e. ZZ ) -> ( X I N ) =
          ( ( X / ( 2 ^ N ) ) [,) ( ( X + 1 ) / ( 2 ^ N ) ) ) ) $=
          ( vu vm cz co c2 cexp cdiv c1 caddc cico wceq cv oveq1 oveq1d oveq12d
          wcel oveq2 oveq2d cmpo cbvmpov eqtr4i ovex ovmpo ancoms ) FKUDEKUDFEC
          LFMENLZOLZFPQLZUMOLZRLZSIJFEKKITZMJTZNLZOLZURPQLZUTOLZRLZUQCFUTOLZUOU
          TOLZRLURFSZVAVEVCVFRURFUTOUAVGVBUOUTOURFPQUAUBUCUSESZVEUNVFUPRVHUTUMF
          OUSEMNUEZUFVHUTUMUOOVIUFUCCABKKATZMBTZNLZOLZVJPQLZVLOLZRLZUGIJKKVDUGH
          IJABKKVDVPVJUTOLZVNUTOLZRLURVJSZVAVQVCVRRURVJUTOUAVSVBVNUTOURVJPQUAUB
          UCUSVKSZVQVMVRVORVTUTVLVJOUSVKMNUEZUFVTUTVLVNOWAUFUCUHUIUNUPRUJUKUL
          $.
      $}

      $( Dyadic intervals are subsets of ` RR ` .  (Contributed by Thierry
         Arnoux, 18-Sep-2017.) $)
      dya2iocress $p |- ( ( N e. ZZ /\ X e. ZZ ) -> ( X I N ) C_ RR ) $=
        ( cz wcel wa co c2 cexp cdiv c1 caddc cico cr rerpdivcld cxr simpr zred
        dya2iocival wss crp 2rp a1i simpl rpexpcld 1red icossre syl2anc eqsstrd
        readdcld rexrd ) EIJZFIJZKZFECLFMENLZOLZFPQLZUTOLZRLZSABCDEFGHUDUSVASJV
        CUAJVDSUEUSFUTUSFUQURUBUCZUSMEMUFJUSUGUHUQURUIUJZTUSVCUSVBUTUSFPVEUSUKU
        OVFTUPVAVCULUMUN $.

      $( Dyadic intervals are Borel sets of ` RR ` .  (Contributed by Thierry
         Arnoux, 22-Sep-2017.) $)
      dya2iocbrsiga $p |- ( ( N e. ZZ /\ X e. ZZ ) -> ( X I N ) e. BrSiga ) $=
        ( cz wcel co c2 cdiv cbrsiga cmnf cioo cxr cr cfv ctop wa cexp c1 caddc
        cico dya2iocival cdif clt wbr wceq mnfxr a1i simpr crp simpl rerpdivcld
        zred 2rp rpexpcld rexrd 1red readdcld mnflt syl syl31anc csiga crn cuni
        brsigarn elrnsiga ax-mp ctg csigagen retop iooretop elsigagen df-brsiga
        difioo mp2an eleqtrri difelsiga mp3an eqeltrrdi eqeltrd ) EIJZFIJZUAZFE
        CKFLEUBKZMKZFUCUDKZWHMKZUEKZNABCDEFGHUFWGWLOWKPKZOWIPKZUGZNWGOQJZWIQJWK
        QJOWIUHUIZWOWLUJWPWGUKULWGWIWGFWHWGFWEWFUMUQZWGLELUNJWGURULWEWFUOUSZUPZ
        UTWGWKWGWJWHWGFUCWRWGVAVBWSUPUTWGWIRJWQWTWIVCVDOWIWKVRVENVFVGVHJZWMNJWN
        NJWONJNRVFSJXAVINRVJVKWMPVGVLSZVMSZNXBTJZWMXBJWMXCJVNOWKVOXBWMTVPVSVQVT
        WNXCNXDWNXBJWNXCJVNOWIVOXBWNTVPVSVQVTWMWNNWAWBWCWD $.

      ${
        $d d n x $.  $d d I $.
        $( Dyadic intervals are Borel sets of ` RR ` .  (Contributed by Thierry
           Arnoux, 22-Sep-2017.)  (Revised by Thierry Arnoux, 13-Oct-2017.) $)
        dya2icobrsiga $p |- ran I C_ BrSiga $=
          ( vd crn cbrsiga cv wcel c2 co cz cmnf cioo cxr cr cfv ctop cexp cdiv
          c1 caddc cico wceq wrex ovex elrnmpo wa simpr clt wbr mnfxr a1i simpl
          cdif zred crp 2rp rpexpcld rerpdivcld rexrd readdcld mnflt syl difioo
          1red syl31anc csiga brsigarn elrnsiga ctg csigagen iooretop elsigagen
          ax-mp retop mp2an df-brsiga eleqtrri difelsiga mp3an eqeltrrdi adantr
          cuni eqeltrd ex rexlimivv sylbi ssriv ) GCHZIGJZWLKWMAJZLBJZUAMZUBMZW
          NUCUDMZWPUBMZUEMZUFZBNUGANUGWMIKZABNNWTWMCFWQWSUEUHUIXAXBABNNWNNKZWON
          KZUJZXAXBXEXAUJWMWTIXEXAUKXEWTIKXAXEWTOWSPMZOWQPMZUQZIXEOQKZWQQKWSQKO
          WQULUMZXHWTUFXIXEUNUOXEWQXEWNWPXEWNXCXDUPURZXELWOLUSKXEUTUOXCXDUKVAZV
          BZVCXEWSXEWRWPXEWNUCXKXEVHVDXLVBVCXEWQRKXJXMWQVEVFOWQWSVGVIIVJHWFKZXF
          IKXGIKXHIKIRVJSKXNVKIRVLVQXFPHVMSZVNSZIXOTKZXFXOKXFXPKVROWSVOXOXFTVPV
          SVTWAXGXPIXQXGXOKXGXPKVROWQVOXOXGTVPVSVTWAXFXGIWBWCWDWEWGWHWIWJWK $.
      $}

      $d x I $.
      ${
        $d n x $.  $d b D $.  $d b I $.  $d b x N $.  $d b x X $.
        dya2icoseg.1 $e |- N = ( |_ ` ( 1 - ( 2 logb D ) ) ) $.
        $( For any point and any closed-below, open-above interval of ` RR `
           centered on that point, there is a closed-below open-above dyadic
           rational interval which contains that point and is included in the
           original interval.  (Contributed by Thierry Arnoux, 19-Sep-2017.) $)
        dya2icoseg $p |- ( ( X e. RR /\ D e. RR+ ) -> E. b e. ran I
          ( X e. b /\ b C_ ( ( X - D ) (,) ( X + D ) ) ) ) $=
          ( wcel c2 co cmin caddc cz cdiv c1 wbr crp cexp cmul cfl cfv crn cioo
          cr wa wss cv wrex cxp wfn cico ovex fnmpoi a1i simpl 2rp clogb cuz 2z
          1red uzid ax-mp relogbzcl mpan resubcld flcld eqeltrid rpexpcl adantl
          rpred sylancr remulcld fnovrn syl3anc cle zred fllelt simpld lediv1dd
          clt syl recnd 2cnd cc0 wne expne0d divcan4d breqtrd readdcld ltdiv1dd
          2ne0 simprd eqbrtrrd cxr w3a wb redivcld rexrd syl2anc mpbir3and wceq
          elico2 eleqtrrd simpr rereccld oveq2i dya2ub eqbrtrid ltsub2dd mulcld
          dya2iocival 1cnd divsubdird oveq1d eqtrd pncand ltled ltletrd divdird
          ltsub1dd leadd1dd ltadd2dd lelttrd eqsstrd eleq2 sseq1 anbi12d rspcev
          icossioo syl22anc syl12anc ) GUHLZBUALZUIZGMFUBNZUCNZUDUEZFDNZDUFZLZG
          UUBLZUUBGBONZGBPNZUGNZUJZGHUKZLZUUJUUHUJZUIZHUUCULYRDQQUMUNZUUAQLZFQL
          ZUUDUUNYRACQQAUKZMCUKUBNZRNZUUQSPNUURRNZUONDJUUSUUTUOUPUQURYRYTYRGYSY
          PYQUSZYQYSUHLZYPYQMUALZUUPUVBUTYQFSMBVANZONZUDUEZQKYQUVEYQSUVDYQVDMMV
          BUELZYQUVDUHLMQLUVGVCMVEVFMBVGVHVIVJVKZUVCUUPUIYSMFVLZVNVOVMZVPZVJZYQ
          UUPYPUVHVMZQQUUAFDVQVRYRGUUAYSRNZUUASPNZYSRNZUONZUUBYRGUVQLZYPUVNGVST
          ZGUVPWDTZUVAYRUVNYTYSRNZGVSYRUUAYTYSYRUUAUVLVTZUVKYRUVCUUPYSUALUTUVMU
          VIVOZYRUUAYTVSTZYTUVOWDTZYRYTUHLUWDUWEUIUVKYTWAWEZWBZWCYRGYSYRGUVAWFZ
          YRYSUVJWFZYRMFYRWGMWHWIYRWOURUVMWJZWKZWLYRUWAGUVPWDUWKYRYTUVOYSUVKYRU
          UASUWBYRVDZWMZUWCYRUWDUWEUWFWPZWNWQYRUVNUHLUVPWRLUVRYPUVSUVTWSWTYRUUA
          YSUWBUVJUWJXAZYRUVPYRUVOYSUWMUVJUWJXAZXBUVNUVPGXFXCXDYRUUPUUOUUBUVQXE
          UVMUVLACDEFUUAIJXOXCZXGYRUUBUVQUUHUWQYRUUFWRLUUGWRLUUFUVNWDTUVPUUGVST
          UVQUUHUJYRUUFYRGBUVAYRBYPYQXHVNZVIZXBYRUUGYRGBUVAUWRWMZXBYRUUFGSYSRNZ
          ONZUVNUWSYRGUXAUVAYRYSUVJUWJXIZVIUWOYRUXABGUXCUWRUVAYRUXASMUVFUBNZRNZ
          BWDYSUXDSRFUVFMUBKXJXJYQUXEBWDTYPBXKVMXLZXMYRYTSONZYSRNZUXBUVNVSYRUXH
          UWAUXAONUXBYRYTSYSYRGYSUWHUWIXNZYRXPZUWIUWJXQYRUWAGUXAOUWKXRXSYRUXGUU
          AYSYRYTSUVKUWLVIZUWBUWCYRUXGUUAUXKUWBYRUXGUVOSONUUAWDYRYTUVOSUVKUWMUW
          LUWNYDYRUUASYRUUAUWBWFUXJXTWLYAWCWQYBYRUVPUUGUWPUWTYRUVPGUXAPNZUUGUWP
          YRGUXAUVAUXCWMUWTYRUVPYTSPNZYSRNZUXLVSYRUVOUXMYSUWMYRYTSUVKUWLWMUWCYR
          UUAYTSUWBUVKUWLUWGYEWCYRUXNUWAUXAPNUXLYRYTSYSUXIUXJUWIUWJYCYRUWAGUXAP
          UWKXRXSWLYRUXABGUXCUWRUVAUXFYFYGYAUUFUUGUVNUVPYMYNYHUUMUUEUUIUIHUUBUU
          CUUJUUBXEUUKUUEUULUUIUUJUUBGYIUUJUUBUUHYJYKYLYO $.
      $}

      ${
        $d b n x $.  $d b d x E $.  $d b d I $.  $d b d x X $.
        $( For any point and any open interval of ` RR ` containing that point,
           there is a closed-below open-above dyadic rational interval which
           contains that point and is included in the original interval.
           (Contributed by Thierry Arnoux, 12-Oct-2017.) $)
        dya2icoseg2 $p |- ( ( X e. RR /\ E e. ran (,) /\ X e. E ) ->
          E. b e. ran I ( X e. b /\ b C_ E ) ) $=
          ( vd cr wcel cioo co wss wa wrex crp cfv crefld crn w3a cv cmin caddc
          wral c1 c2 clogb cfl eqid dya2icoseg ralrimiva 3ad2ant1 cabs ccom cxp
          cres cbl simp3 ctg cvv iooex bastg ax-mp simp2 sselid eleqtrrdi cxmet
          rnex wb rexmet cxms cmopn wceq ccms cms recms cmsms msxms mp2b retopn
          ctopn eqtri rebase cds reds reseq1i xmstopn elmopn2 simprbi syl oveq1
          sseq1d rexbidv rspcva syl2anc rpre bl2ioo sylan2 mpbid r19.29 r19.41v
          rexbidva sstr anim2i anassrs reximi sylbir rexlimivw ) FKLZCMUAZLZFCL
          ZUBZFGUCZLZXPFJUCZUDNFXRUENMNZOZPZGDUAZQZXSCOZPZJRQZXQXPCOZPZGYBQZXOY
          CJRUFZYDJRQZYFXKXMYJXNXKYCJRAXRBDEUGUHXRUINUDNUJSZFGHIYLUKULUMUNXOFXR
          UOUDUPZKKUQZURZUSSZNZCOZJRQZYKXOXNAUCZXRYPNZCOZJRQZACUFZYSXKXMXNUTXOC
          ELZUUDXOCXLVASZEXOXLUUFCXLVBLXLUUFOMVCVJXLVBVDVEXKXMXNVFVGHVHUUECKOZU
          UDYOKVISLUUEUUGUUDPVKYOYOUKZVLAJCYOEKTVMLZEYOVNSVOTVPLTVQLUUIVRTVSTVT
          WAYOETKEUUFTWCSHWBWDWEYMTWFSYNWGWHWIVEWJVEWKWLUUCYSAFCYTFVOZUUBYRJRUU
          JUUAYQCYTFXRYPWMWNWOWPWQXKXMYSYKVKXNXKYRYDJRXRRLXKXRKLZYRYDVKXRWRXKUU
          KPYQXSCFXRYOUUHWSWNWTXDUNXAYCYDJRXBWQYEYIJRYEYAYDPZGYBQYIYAYDGYBXCUUL
          YHGYBXQXTYDYHXTYDPYGXQXPXSCXEXFXGXHXIXJWL $.
      $}

      $d u v I $.
      dya2ioc.2 $e |- R = ( u e. ran I , v e. ran I |-> ( u X. v ) ) $.
      $( The function returning dyadic square covering for a given size has
         domain ` ( ran I X. ran I ) ` .  (Contributed by Thierry Arnoux,
         19-Sep-2017.) $)
      dya2iocrfn $p |- R Fn ( ran I X. ran I ) $=
        ( crn cv cxp vex xpex fnmpoi ) CBFKZQCLZBLZMDJRSCNBNOP $.

      $( The dyadic rectangle set is countable.  (Contributed by Thierry
         Arnoux, 18-Sep-2017.)  (Revised by Thierry Arnoux, 11-Oct-2017.) $)
      dya2iocct $p |- ran R ~<_ _om $=
        ( crn com cdom wbr cz cv co cn mp2an cvv c2 cexp cdiv c1 caddc cico cen
        cmpo znnen nnct endomtr wcel ovex rgen2w mpocti eqbrtri rnct wa cxp vex
        ax-mp xpex breq1i biimpri 3syl ) FKZLMNZVGDKLMNZFLMNVGFAEOOAPZUAEPUBQZU
        CQZVIUDUEQVJUCQZUFQZUHZLMIOLMNZVOVNLMNORUGNRLMNVOUIUJORLUKSZVPAEOOVMTVM
        TULAEOOVKVLUFUMUNUOSUPFUQVAZVQVGVGURCBVFVFCPZBPZUSZUHZLMNZDLMNZVHCBVFVF
        VTTVTTULCBVFVFVRVSCUTBUTVBUNUOWCWBDWALMJVCVDDUQVES $.

      $(
        $d m n x y $.  $d m I $.  $d m x y N $.  $d x y V $.
        @( The value of a dyadic square cover of ` ( RR X. RR ) ` .
           (Contributed by Thierry Arnoux, 24-Sep-2017.) @)
        dya2iocrrnval $p |- ( W e. ran R <-> E. x e. ZZ E. y e. ZZ
          E. m e. ZZ E. n e. ZZ W = ( ( x I n ) X. ( y I m ) ) ) $=
          ( vm cz wcel cv co cxp cmpo oveq2d nfcv cfv crn wceq wrex mpoeq3dva
          w3a simp1 xpeq12d rneqd cmpt c2 cexp cdiv c1 cico nfmpo2 nfcxfr nfov
          caddc nfxp nfmpo nfrn cbvmpt eqtr4i zex mpoex rnex eleq2d eqid ovex
          fvmpt xpex elrnmpo bitrdi ) GMNZHGCUAZNHABMMAOZGEPZBOZGEPZQZRZUBZNHW
          AUCBMUDAMUDVOVPWCHLGABMMVQLOZEPZVSWDEPZQZRZUBZWCMCWDGUCZWHWBWJABMMWGW
          AWJVQMNZVSMNZUFZWEVRWFVTWMWDGVQEWJWKWLUGZSWMWDGVSEWNSUHUEUICDMABMMVQD
          OZEPZVSWOEPZQZRZUBZUJLMWIUJKLDMWIWTDWHABDMMWGDMTZXADWEWFDVQWDEDVQTDEA
          DMMVQUKWOULPZUMPVQUNUSPXBUMPUOPZRJADMMXCUPUQZDWDTZURDVSWDEDVSTXDXEURU
          TVAVBLWTTWDWOUCZWHWSXFABMMWGWRXFWKWLUFZWEWPWFWQXGWDWOVQEXFWKWLUGZSXGW
          DWOVSEXHSUHUEUIVCVDWBABMMWAVEVEVFVGVKVHABMMWAHWBWBVIVRVTVQGEVJVSGEVJV
          LVMVN $.
      $)

      $d u v x $.
      ${
        $d n s t x $.  $d b e f s t A $.  $d s t u v x I $.  $d b e f s t R $.
        $d b e f s t x X $.
        dya2iocnrect.1 $e |-
                      B = ran ( e e. ran (,) , f e. ran (,) |-> ( e X. f ) ) $.
        $( For any point of an open rectangle in ` ( RR X. RR ) ` , there is a
           closed-below open-above dyadic rational square which contains that
           point and is included in the rectangle.  (Contributed by Thierry
           Arnoux, 12-Oct-2017.) $)
        dya2iocnrect $p |- ( ( X e. ( RR X. RR ) /\ A e. B /\ X e. A ) ->
          E. b e. ran R ( X e. b /\ b C_ A ) ) $=
          ( wcel wrex wa vs vt cr cxp w3a cv wceq cioo crn wss cmpo eleq2i eqid
          xpex elrnmpo sylbb 3ad2ant2 simp1 simp3 jca32 r19.41vv biimpri simprl
          vex simpl simprr eleqtrd 3jca c1st cfv c2nd simpr xp1st adantl simpll
          3ad2ant1 3ad2ant3 dya2icoseg2 syl3anc xp2nd simplr reeanv xpeq1 xpeq2
          sylanbrc eqeq2d rspc2ev mp3an3 sylibr ad2antrl cvv xpss simpl1 sselid
          simprrl simpld simprrr syl12anc simprd xpss12 syl2anc simpl2 sseqtrrd
          elxp7 eleq2 sseq1 anbi12d rspcev rexlimdvv sylc sylan2 rexlimivv 3syl
          exp32 ex ) LUCUCUDZRZDERZLDRZUEZDGUFZHUFZUDZUGZHUHUIZSGYESZXQXSTZTZYD
          YGTZHYESGYESZLMUFZRZYKDUJZTZMFUIZSZXTYFXQXSXRXQYFXSXRDGHYEYEYCUKZUIZR
          YFEYRDQULGHYEYEYCDYQYQUMYAYBGVDHVDUNUOUPUQXQXRXSURXQXRXSUSUTYJYHYDYGG
          HYEYEVAVBYIYPGHYEYEYAYERZYBYERZTZYIYPYIUUAXQYDLYCRZUEZYPYIXQYDUUBYDXQ
          XSVCYDYGVEZYILDYCYDXQXSVFUUDVGVHUUAUUCTZUUCLVIVJZUAUFZRZUUGYAUJZTZLVK
          VJZUBUFZRZUULYBUJZTZTZUBJUIZSUAUUQSZYPUUAUUCVLUUEUUJUAUUQSZUUOUBUUQSZ
          UURUUEUUFUCRZYSUUFYARZUUSUUCUVAUUAXQYDUVAUUBLUCUCVMVPVNYSYTUUCVOUUCUV
          BUUAUUBXQUVBYDLYAYBVMVQVNAIYAJKUUFUANOVRVSUUEUUKUCRZYTUUKYBRZUUTUUCUV
          CUUAXQYDUVCUUBLUCUCVTVPVNYSYTUUCWAUUCUVDUUAUUBXQUVDYDLYAYBVTVQVNAIYBJ
          KUUKUBNOVRVSUUJUUOUAUBUUQUUQWBWEUUCUUPYPUAUBUUQUUQUUCUUGUUQRZUULUUQRZ
          TZUUPYPUUCUVGUUPTZTZUUGUULUDZYORZLUVJRZUVJDUJZYPUVGUVKUUCUUPUVGUVJCUF
          ZBUFZUDZUGZBUUQSCUUQSZUVKUVEUVFUVJUVJUGZUVRUVJUMUVQUVSUVJUUGUVOUDZUGC
          BUUGUULUUQUUQUVNUUGUGUVPUVTUVJUVNUUGUVOWCWFUVOUULUGUVTUVJUVJUVOUULUUG
          WDWFWGWHCBUUQUUQUVPUVJFPUVNUVOCVDBVDUNUOWIWJUVILWKWKUDZRZUUHUUMUVLUVI
          XPUWALUCUCWLXQYDUUBUVHWMWNUVIUUHUUIUUCUVGUUJUUOWOZWPUVIUUMUUNUUCUVGUU
          JUUOWQZWPUVLUWBUUHUUMTTLUUGUULXDVBWRUVIUVJYCDUVIUUIUUNUVJYCUJUVIUUHUU
          IUWCWSUVIUUMUUNUWDWSUUGYAUULYBWTXAXQYDUUBUVHXBXCYNUVLUVMTMUVJYOYKUVJU
          GYLUVLYMUVMYKUVJLXEYKUVJDXFXGXHWRXNXIXJXKXOXLXM $.
      $}

      ${
        $d b e f u v x $.  $d b e r A $.  $d x I $.  $d e J $.  $d b e f r R $.
        $d b e f r x X $.
        $( For any point of an open set of the usual topology on
           ` ( RR X. RR ) ` there is a closed-below open-above dyadic rational
           square which contains that point and is entirely in the open set.
           (Contributed by Thierry Arnoux, 21-Sep-2017.) $)
        dya2iocnei $p |- ( ( A e. ( J tX J ) /\ X e. A ) ->
          E. b e. ran R ( X e. b /\ b C_ A ) ) $=
          ( vr ve vf wcel wa cr cv ctx cxp wss cioo crn cmpo wrex elunii ancoms
          co cuni tpr2uni eleqtrdi cmul caddc tpr2rico anass dya2iocnrect 3expb
          ci eqid anim1i anasss sylan2br r19.41v simpll simplr simpr jca reximi
          sstrd sylbir syl rexlimdvaa sylc ) DHHUAUJZQZIDQZRZISSUBZQZINTZQZWBDU
          CZRZNOPUDUEZWFOTPTUBUFUEZUGIJTZQZWHDUCZRZJEUEZUGZVSIVPUKZVTVRVQIWNQID
          VPUHUIHKULUMOPBCDWGCBSSCTUTBTUNUJUOUJUFZHINKWOVAWGVAZUPWAWEWMNWGWAWBW
          GQZWERZRWIWHWBUCZRZJWLUGZWDRZWMWRWAWQWCRZWDRXBWQWCWDUQWAXCWDXBWAXCRXA
          WDWAWQWCXAABCWBWGEOPFGHIJKLMWPURUSVBVCVDXBWTWDRZJWLUGWMWTWDJWLVEXDWKJ
          WLXDWIWJWIWSWDVFXDWHWBDWIWSWDVGWTWDVHVKVIVJVLVMVNVO $.
      $}

      ${
        $d m p x $.  $d b c m p u v z A $.  $d m J $.  $d b c m p R $.
        $d b m z $.
        $( Every open set of ` ( RR X. RR ) ` is a union of closed-below
           open-above dyadic rational rectangular subsets of ` ( RR X. RR ) ` .
           This union must be a countable union by ~ dya2iocct .  (Contributed
           by Thierry Arnoux, 18-Sep-2017.) $)
        dya2iocuni $p |- ( A e. ( J tX J ) -> E. c e. ~P ran R U. c = A ) $=
          ( vz vb vp wcel cv wrex wceq c0 vm ctx co wel wss crn crab cpw ssrab2
          wa cuni cxp wfn cvv dya2iocrfn cz c2 cexp cdiv c1 caddc cico cmpo zex
          mpoex eqeltri rnex xpex fnex mp2an elpw2 mpbir a1i wn wral rex0 rexeq
          mtbiri ralrimivw rabeq0 sylibr unieqd uni0 eqtrdi 0ss eqsstrdi elequ2
          sseq1 anbi12d rexbidv elrab simpr r19.9rzv imbitrrid adantld biimtrid
          reximi ralrimiv unissb pm2.61ine dya2iocnei simpl ssel2 ancoms adantl
          wne elequ1 anbi1d rspcev syl2anc jca simprl reximi2 syl eqelssd unieq
          eluni2 eqeq1d ) DHHUBUCPZMNUDZNQZDUEZUJZMDRZNEUFZUGZYEUHZPZYFUKZDSZIQ
          ZUKZDSZIYGRYHXSYHYFYEUEYDNYEUIYFYEEEGUFZYNULZUMYOUNPEUNPABCEFGHJKLUOY
          NYNGGAFUPUPAQZUQFQURUCZUSUCYPUTVAUCYQUSUCVBUCZVCUNKAFUPUPYRVDVDVEVFVG
          ZYSVHYOUNEVIVJVGVKVLVMXSUAYIDYIDUEZXSYTDTDTSZYITDUUAYITUKTUUAYFTUUAYD
          VNZNYEVOYFTSUUAUUBNYEUUAYDYCMTRYCMVPYCMDTVQVRVSYDNYEVTWAWBWCWDDWEWFDT
          XFZOQZDUEZOYFVOYTUUCUUEOYFUUDYFPZUUDYEPZMOUDZUUEUJZMDRZUJZUUCUUEYDUUJ
          NUUDYEYAUUDSZYCUUIMDUULXTUUHYBUUENOMWGYAUUDDWHWIWJWKZUUCUUJUUEUUGUUJU
          UEUUCUUEMDRUUIUUEMDUUHUUEWLWQUUEMDWMWNWOWPWROYFDWSWAWTVMXSUAQZDPZUJZU
          AOUDZOYFRZUUNYIPUUPUUQUUEUJZOYERUURABCDEFGHUUNOJKLXAUUSUUQOYEYFUUGUUS
          UJZUUFUUQUUTUUKUUFUUTUUGUUJUUGUUSXBUUTUUOUUSUUJUUSUUOUUGUUEUUQUUOUUDD
          UUNXCXDXEUUGUUSWLUUIUUSMUUNDMQUUNSUUHUUQUUEMUAOXGXHXIXJXKUUMWAUUGUUQU
          UEXLXKXMXNOUUNYFXQWAXOYMYJIYFYGYKYFSYLYIDYKYFXPXRXIXJ $.
      $}

      ${
        $d c d n u v x $.  $d d u v I $.  $d c d R $.
        $( The dyadic rectangular set collection covers ` ( RR X. RR ) ` .
           (Contributed by Thierry Arnoux, 18-Sep-2017.) $)
        dya2iocucvr $p |- U. ran R = ( RR X. RR ) $=
          ( vd cr wss cv wcel wrex wa c2 co cz vc crn cuni cxp unissb wceq xpex
          vex elrnmpo simpr cpw pwssb cexp cdiv caddc cico ovex cxr simpll zred
          c1 2re a1i cc0 wne 2ne0 reexpclzd 2cnd expne0d redivcld 1red readdcld
          simplr rexrd icossre syl2anc eqsstrd ex rexlimivv sylbi mprgbir sseli
          elpwid xpss12 syl2an adantr ctx ctop cioo ctg eqeltri txtopi uniretop
          cfv retop unieqi eqtr4i txunii topopn dya2iocuni mp2b unissd eqsstrrd
          elpwi rexlimiva ax-mp eqssi ) DUBZUCZLLUDZXIXJMKNZXJMZKXHKXHXJUEXKXHO
          XKCNZBNZUDZUFZBFUBZPCXQPXLCBXQXQXOXKDJXMXNCUHBUHUGUIXPXLCBXQXQXMXQOZX
          NXQOZQZXPXLXTXPQXKXOXJXTXPUJXTXOXJMZXPXRXMLMXNLMYAXSXRXMLXQLUKZXMXQYB
          MXKLMZKXQKXQLULXKXQOXKANZRENZUMSZUNSZYDVAUOSZYFUNSZUPSZUFZETPATPYCAET
          TYJXKFIYGYIUPUQUIYKYCAETTYDTOZYETOZQZYKYCYNYKQZXKYJLYNYKUJYOYGLOYIURO
          YJLMYOYDYFYOYDYLYMYKUSUTZYORYERLOYOVBVCRVDVEYOVFVCZYLYMYKVMZVGZYORYEY
          OVHYQYRVIZVJYOYIYOYHYFYOYDVAYPYOVKVLYSYTVJVNYGYIVOVPVQVRVSVTWAZWBWCXS
          XNLXQYBXNUUAWBWCXMLXNLWDWEWFVQVRVSVTWAUANZUCZXJUFZUAXHUKZPZXJXIMZGGWG
          SZWHOXJUUHOUUFGGGWIUBWJWNZWHHWOWKZUUJWLUUHXJGGLLUUJUUJLUUIUCGUCWMGUUI
          HWPWQZUUKWRWSABCXJDEFGUAHIJWTXAUUDUUGUAUUEUUBUUEOZUUDQZXJUUCXIUULUUDU
          JUUMUUBXHUULUUBXHMUUDUUBXHXDWFXBXCXEXFXG $.
      $}

      $d n u v y $.  $d n x y R $.  $d x J $.
      $( The Borel algebra on ` ( RR X. RR ) ` is a subset of the sigma-algebra
         generated by the dyadic closed-below, open-above rectangular subsets
         of ` ( RR X. RR ) ` .  This is a step of the proof of Proposition
         1.1.5 of [Cohn] p. 4.  (Contributed by Thierry Arnoux,
         17-Sep-2017.) $)
      sxbrsigalem1 $p |- ( sigaGen ` ( J tX J ) ) C_ ( sigaGen ` ran R ) $=
        ( vy cuni crn wceq csigagen cfv wss cvv wcel cr ctx co dya2iocucvr cioo
        cxp ctg ctop retop eqeltri uniretop unieqi eqtr4i txunii eqtr2i cv wrex
        cpw dya2iocuni wa simpr com cdom dya2iocct ctex mp1i elpwi ssct sylancl
        wbr elsigagen2 syl3anc adantr eqeltrrd rexlimiva ssriv ax-mp sigagenss2
        syl mp3an ) GGUAUBZLZDMZLZNVTWBOPZQWBRSZVTOPWDQWCTTUEWAABCDEFGHIJUCGGTT
        GUDMUFPZUGHUHUIZWGTWFLGLUJGWFHUKULZWHUMUNAVTWDAUOZVTSKUOZLZWINZKWBUQZUP
        WIWDSZABCWIDEFGKHIJURWLWNKWMWJWMSZWLUSWKWIWDWOWLUTWOWKWDSZWLWOWEWJWBQZW
        JVAVBVIZWPWBVAVBVIZWEWOABCDEFGHIJVCZWBVDZVEWJWBVFZWOWQWSWRXBWTWJWBVGVHW
        BWJRVJVKVLVMVNVRVOWSWEWTXAVPVTWBRVQVS $.

      ${
        $d d e f n u v x $.  $d u v x I $.  $d x J $.  $d d R $.
        $( The sigma-algebra generated by the dyadic closed-below, open-above
           rectangular subsets of ` ( RR X. RR ) ` is a subset of the
           sigma-algebra generated by the closed half-spaces of
           ` ( RR X. RR ) ` .  The proof goes by noting the fact that the
           dyadic rectangles are intersections of a 'vertical band' and an
           'horizontal band', which themselves are differences of closed
           half-spaces.  (Contributed by Thierry Arnoux, 17-Sep-2017.) $)
        sxbrsigalem2 $p |- ( sigaGen ` ran R ) C_ ( sigaGen `
           ( ran ( e e. RR |-> ( ( e [,) +oo ) X. RR ) )
          u. ran ( f e. RR |-> ( RR X. ( f [,) +oo ) ) ) ) ) $=
          ( cr cpnf cico cxp wceq wcel wrex cz vd crn cuni cv cmpt cun csigagen
          co cfv wss cvv dya2iocucvr sxbrsigalem0 eqtr4i vex xpex elrnmpo simpr
          c1st cres ccnv cima c2nd cin cbrsiga dya2icobrsiga brsigasspwrn sstri
          wa cpw sseli elpwid xpinpreima2 syl2an csiga wtru reex mptex rnex a1i
          unex sgsiga mptru 1stpreima syl c2 cexp cdiv c1 caddc ovex xpeq1d cxr
          cdif cle wbr simpl zred rpexpcld rerpdivcld rexrd 1red readdcld pnfxr
          crp 2rp lep1d lediv1dd pnfge difico syl32anc eqtr3di ssun1 eqid oveq1
          rspceeqv sylancl elrnmpti elsigagen sylancr difelsiga syl3anc eqeltrd
          difxp1 sylibr sselid adantr ex rexlimivv sylbi 2ndpreima xpeq2d ssun2
          difxp2 adantl inelsiga ssriv sigagenss2 mp3an ) DUBZUCZEMEUDZNOUHZMPZ
          UEZUBZFMMFUDZNOUHZPZUEZUBZUFZUCZQYTUULUGUIZUJUULUKRZYTUGUIUUNUJUUAMMP
          ZUUMABCDGHIJKLULEFUMUNUAYTUUNUAUDZYTRUUQCUDZBUDZPZQZBHUBZSCUVBSUUQUUN
          RZCBUVBUVBUUTUUQDLUURUUSCUOBUOUPUQUVAUVCCBUVBUVBUURUVBRZUUSUVBRZVIZUV
          AUVCUVFUVAVIUUQUUTUUNUVFUVAURUVFUUTUUNRUVAUVFUUTUSUUPUTVAUURVBZVCUUPU
          TVAUUSVBZVDZUUNUVDUURMUJZUUSMUJZUUTUVIQUVEUVDUURMUVBMVJZUURUVBVEUVLAG
          HIJKVFVGVHZVKVLZUVEUUSMUVBUVLUUSUVMVKVLZUURUUSMMVMVNUVFUUNVOUBUCRZUVG
          UUNRZUVHUUNRZUVIUUNRUVPUVFUVPVPUULUKUUOVPUUFUUKUUEEMUUDVQVRVSUUJFMUUI
          VQVRVSWAZVTWBWCZVTUVDUVQUVEUVDUVGUURMPZUUNUVDUVJUVGUWAQUVNUURMMWDWEUV
          DUURAUDZWFGUDZWGUHZWHUHZUWBWIWJUHZUWDWHUHZOUHZQZGTSATSUWAUUNRZAGTTUWH
          UURHKUWEUWGOWKZUQUWIUWJAGTTUWBTRZUWCTRZVIZUWIUWJUWNUWIVIZUWAUWHMPZUUN
          UWOUURUWHMUWNUWIURWLUWNUWPUUNRUWIUWNUWPUWENOUHZMPZUWGNOUHZMPZWNZUUNUW
          NUWQUWSWNZMPUWPUXAUWNUXBUWHMUWNUWEWMRUWGWMRZNWMRZUWEUWGWOWPUWGNWOWPZU
          XBUWHQUWNUWEUWNUWBUWDUWNUWBUWLUWMWQWRZUWNWFUWCWFXERUWNXFVTUWLUWMURWSZ
          WTZXAUWNUWGUWNUWFUWDUWNUWBWIUXFUWNXBXCZUXGWTZXAZUXDUWNXDVTUWNUWBUWFUW
          DUXFUXIUXGUWNUWBUXFXGXHUWNUXCUXEUXKUWGXIWEUWEUWGNXJXKZWLUWQUWSMYDXLUW
          NUVPUWRUUNRZUWTUUNRZUXAUUNRUVPUWNUVTVTZUWNUUOUWRUULRUXMUVSUWNUUFUULUW
          RUUFUUKXMZUWNUWRUUDQEMSZUWRUUFRUWNUWEMRZUWRUWRQUXQUXHUWRXNEUWEMUUDUWR
          UWRUUBUWEQUUCUWQMUUBUWENOXOWLXPXQEMUUDUWRUUEUUEXNZUUCMUUBNOWKVQUPZXRY
          EYFUULUWRUKXSXTUWNUUOUWTUULRUXNUVSUWNUUFUULUWTUXPUWNUWTUUDQEMSZUWTUUF
          RUWNUWGMRZUWTUWTQUYAUXJUWTXNEUWGMUUDUWTUWTUUBUWGQUUCUWSMUUBUWGNOXOWLX
          PXQEMUUDUWTUUEUXSUXTXRYEYFUULUWTUKXSXTUWRUWTUUNYAYBYCYGYCYHYIYJYCYGUV
          EUVRUVDUVEUVHMUUSPZUUNUVEUVKUVHUYCQUVOUUSMMYKWEUVEUUSUWHQZGTSATSUYCUU
          NRZAGTTUWHUUSHKUWKUQUYDUYEAGTTUWNUYDUYEUWNUYDVIZUYCMUWHPZUUNUYFUUSUWH
          MUWNUYDURYLUWNUYGUUNRUYDUWNUYGMUWQPZMUWSPZWNZUUNUWNMUXBPUYGUYJUWNUXBU
          WHMUXLYLMUWQUWSYNXLUWNUVPUYHUUNRZUYIUUNRZUYJUUNRUXOUWNUUOUYHUULRUYKUV
          SUWNUUKUULUYHUUKUUFYMZUWNUYHUUIQFMSZUYHUUKRUWNUXRUYHUYHQUYNUXHUYHXNFU
          WEMUUIUYHUYHUUGUWEQUUHUWQMUUGUWENOXOYLXPXQFMUUIUYHUUJUUJXNZMUUHVQUUGN
          OWKUPZXRYEYFUULUYHUKXSXTUWNUUOUYIUULRUYLUVSUWNUUKUULUYIUYMUWNUYIUUIQF
          MSZUYIUUKRUWNUYBUYIUYIQUYQUXJUYIXNFUWGMUUIUYIUYIUUGUWGQUUHUWSMUUGUWGN
          OXOYLXPXQFMUUIUYIUUJUYOUYPXRYEYFUULUYIUKXSXTUYHUYIUUNYAYBYCYGYCYHYIYJ
          YCYOUVGUVHUUNYPYBYCYGYCYHYIYJYQUVSYTUULUKYRYS $.
      $}

      ${
        $d e f n u v x $.
        $( The Borel algebra on ` ( RR X. RR ) ` is generated by the dyadic
           closed-below, open-above rectangular subsets of ` ( RR X. RR ) ` .
           Proposition 1.1.5 of [Cohn] p. 4 .  Note that the interval used in
           this formalization are closed-below, open-above instead of
           open-below, closed-above in the proof as they are ultimately
           generated by the floor function.  (Contributed by Thierry Arnoux,
           21-Sep-2017.) $)
        sxbrsigalem4 $p |- ( sigaGen ` ( J tX J ) ) = ( sigaGen ` ran R ) $=
          ( ve vf co csigagen cfv crn cr cv cpnf cxp ctx sxbrsigalem1 ccld cico
          cmpt cun sxbrsigalem2 sxbrsigalem3 sstri cuni wceq wss ctop topontopi
          wcel tpr2tp eqid unicls cldssbrsiga ax-mp sigagenss2 mp3an eqssi ) GG
          UAMZNOZDPNOZABCDEFGHIJUBVFVDUCOZNOZVEVFKQKRSUDMQTUEPLQQLRSUDMTUEPUFNO
          VHABCDKLEFGHIJUGKLGHUHUIVGUJVDUJZUKVGVEULZVDUMUOZVHVEULVDVIQQTVDGHUPU
          NZVIUQURVKVJVLVDUSUTVLVGVDUMVAVBUIVC $.
      $}

      ${
        $d e f g n u v x $.  $d e f g u v I $.  $d n x R $.  $d u x J $.
        $d v J $.
        $( First direction for ~ sxbrsiga .  (Contributed by Thierry Arnoux,
           22-Sep-2017.)  (Revised by Thierry Arnoux, 11-Oct-2017.) $)
        sxbrsigalem5 $p |- ( sigaGen ` ( J tX J ) ) C_ ( BrSiga sX BrSiga ) $=
          ( ve vf vg cfv cbrsiga cv cxp wss wcel wa crn csigagen cmpo cuni wceq
          ctx co csx cvv cr dya2iocucvr br2base csiga brsigarn elexi mpoex rnex
          eqtr4i coprab dya2icobrsiga sseli anim1i ssoprab2i df-mpo eqtri xpeq1
          anim12i xpeq2 cbvmpov 3sstr4i ax-mp sssigagen2 mp2an sigagenss2 mp3an
          rnss sxbrsigalem4 eqid sxval ) DUAZUBNZKLOOKPZLPZQZUCZUAZUBNZGGUFUGUB
          NOOUHUGZVTUDZWFUDZUEVTWGRZWFUISZWAWGRWIUJUJQWJABCDEFGHIJUKKLULURWLVTW
          FRZWKWEKLOOWDOUJUMNZUNUOZWOUPUQZDWERWMCPZFUAZSZBPZWRSZTZMPWQWTQZUEZTZ
          CBMUSZWQOSZWTOSZTZXDTZCBMUSZDWEXEXJCBMXBXIXDWSXGXAXHWROWQAEFGHIUTZVAW
          ROWTXLVAVGVBVCDCBWRWRXCUCXFJCBMWRWRXCVDVEWECBOOXCUCXKKLCBOOWDXCWQWCQW
          BWQWCVFWCWTWQVHVICBMOOXCVDVEVJDWEVPVKWFVTUIVLVMWPVTWFUIVNVOABCDEFGHIJ
          VQOWNSZXMWHWGUEUNUNKLWFOOWNWNWFVRVSVMVJ $.
      $}
    $}

    ${
      $d a m n u v x $.  $d u v x J $.
      $( First direction for ~ sxbrsiga , same as sxbrsigalem6, dealing with
         the antecedents.  (Contributed by Thierry Arnoux, 10-Oct-2017.) $)
      sxbrsigalem6 $p |- ( sigaGen ` ( J tX J ) ) C_ ( BrSiga sX BrSiga ) $=
        ( vx vv vu va vm vn cz cv c2 cexp co cdiv c1 caddc cico cmpo weq oveq1
        crn cxp oveq1d oveq12d oveq2 oveq2d cbvmpov eqid sxbrsigalem5 ) CDEEDFG
        IIFJZKGJZLMZNMZUJOPMZULNMZQMZRZUAZUREJDJUBRZHUQABFGCHIIUPCJZKHJZLMZNMZU
        TOPMZVBNMZQMUTULNMZVDULNMZQMFCSZUMVFUOVGQUJUTULNTVHUNVDULNUJUTOPTUCUDGH
        SZVFVCVGVEQVIULVBUTNUKVAKLUEZUFVIULVBVDNVJUFUDUGUSUHUI $.
    $}

    ${
      $d e f J $.
      $( The product sigma-algebra ` ( BrSiga sX BrSiga ) ` is the Borel
         algebra on ` ( RR X. RR ) ` See example 5.1.1 of [Cohn] p. 143 .
         (Contributed by Thierry Arnoux, 10-Oct-2017.) $)
      sxbrsiga $p |- ( BrSiga sX BrSiga ) = ( sigaGen ` ( J tX J ) ) $=
        ( ve vf cbrsiga co csigagen cfv cv crn cr csiga wcel wceq brsigarn cuni
        mp2an wss mp1i a1i csx ctx cxp cmpo sxval ctopon br2base tpr2uni eqtr4i
        eqid wral wa c1st cres ccnv cima c2nd cin cpw brsigasspwrn sseli elpwid
        xpinpreima2 syl2an tpr2tp sigagensiga ax-mp elrnsiga sgsiga ccn retopon
        ctg eqeltri tx1cn eqidd df-brsiga fveq2i cnmbfm mbfmcnvima adantr tx2cn
        cioo id inelsiga syl3anc eqeltrd rgen2 rnmposs sigagenss2 mp3an eqsstri
        adantl sxbrsigalem6 eqssi ) EEUAFZAAUBFZGHZWOCDEECIZDIZUCZUDZJZGHZWQEKL
        HZMZXEWOXCNOOCDXBEEXDXDXBUJUEQXBPZWPPZNXBWQRZWPKKUCZUFHZMZXCWQRXFXIXGCD
        UGABUHUIWTWQMZDEUKCEUKXHXLCDEEWREMZWSEMZULZWTUMXIUNZUOWRUPZUQXIUNZUOWSU
        PZURZWQXMWRKRWSKRWTXTNXNXMWRKEKUSZWRUTVAVBXNWSKEYAWSUTVAVBWRWSKKVCVDXOW
        QLJPZMZXQWQMZXSWQMZXTWQMWQXGLHMZYCXOXKYFABVEZWPXJVFVGWQXGVHSXMYDXNXMWRW
        QEXPXMWPXJXKXMYGTVIXEEYBMZXMOEKVHZSXMWQEXPWPAXPWPAVJFZMZXMAKUFHZMZYMYKA
        WBJVLHZYLBVKVMZYOAAKKVNQTXMWQVOEAGHZNZXMEYNGHYPVPAYNGBVQUIZTVRXMWCVSVTX
        NYEXMXNWSWQEXRXNWPXJXKXNYGTVIXEYHXNOYISXNWQEXRWPAXRYJMZXNYMYMYSYOYOAAKK
        WAQTXNWQVOYQXNYRTVRXNWCVSWLXQXSWQWDWEWFWGCDEEWTWQXAXAUJWHVGYGXBWPXJWIWJ
        WKABWMWN $.
    $}
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Caratheodory's extension theorem
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  In this section, we define a function ` toOMeas ` which constructs an outer
  measure, from a pre-measure ` R ` .  An explicit generic definition of an
  outer measure is not given. It consists of the three following statements:
  - the outer measure of an empty set is zero ( ~ oms0 )
  - it is monotone ( ~ omsmon )
  - it is countably sub-additive ( ~ omssubadd )
  See Definition 1.11.1 of [Bogachev] p. 41.

$)

  $c toOMeas $.

  $( Class declaration for the outer measure construction function. $)
  coms $a class toOMeas $.

  ${
    $d r a x y z $.
    $( Define a function constructing an outer measure.  See ~ omsval for its
       value.  Definition 1.5 of [Bogachev] p. 16.  (Contributed by Thierry
       Arnoux, 15-Sep-2019.)  (Revised by AV, 4-Oct-2020.) $)
    df-oms $a |- toOMeas = ( r e. _V |-> ( a e. ~P U. dom r |->
      inf ( ran ( x e. { z e. ~P dom r | ( a C_ U. z /\ z ~<_ _om ) }
                  |-> sum* y e. x ( r ` y ) ) , ( 0 [,] +oo ) , < ) ) ) $.
  $}

  ${
    $d a r s t w x y z R $.
    $( Value of the function mapping a content function to the corresponding
       outer measure.  (Contributed by Thierry Arnoux, 15-Sep-2019.)  (Revised
       by AV, 4-Oct-2020.) $)
    omsval $p |- ( R e. _V -> ( toOMeas ` R ) =
      ( a e. ~P U. dom R |-> inf ( ran ( x e. { z e. ~P dom R | ( a C_ U. z /\
      z ~<_ _om ) } |-> sum* y e. x ( R ` y ) ) , ( 0 [,] +oo ) , < ) ) ) $=
      ( vr cvv wcel cv cdm cuni cpw wa crab cfv cesum cmpt crn clt wceq wss com
      cdom wbr cc0 cpnf cicc cinf coms df-oms dmeq unieqd pweqd rabeq syl simpl
      co fveq1d esumeq2dv mpteq12dv rneqd infeq1d id dmexg uniexg pwexg fvmptd3
      mptexg 4syl ) DGHZFDEFIZJZKZLZAEICIZKUAVOUBUCUDMZCVLLZNZAIZBIZVKOZBPZQZRZ
      UEUFUGUQZSUHZQEDJZKZLZAVPCWGLZNZVSVTDOZBPZQZRZWESUHZQZGUIGABCFEUJVKDTZEVN
      WFWIWPWRVMWHWRVLWGVKDUKZULUMWRWEWDWOSWRWCWNWRAVRWBWKWMWRVQWJTVRWKTWRVLWGW
      SUMVPCVQWJUNUOWRVSWAWLBWRVTVSHZMVTVKDWRWTUPURUSUTVAVBUTVJVCVJWGGHWHGHWIGH
      WQGHDGVDWGGVEWHGVFEWIWPGVHVIVG $.

    $d A a s t w x y z $.  $d Q a x y z $.  $d V a x y z $.
    $( Value of the outer measure evaluated for a given set ` A ` .
       (Contributed by Thierry Arnoux, 15-Sep-2019.)  (Revised by AV,
       4-Oct-2020.) $)
    omsfval $p |- ( ( Q e. V /\ R : Q --> ( 0 [,] +oo ) /\ A C_ U. Q )
      -> ( ( toOMeas ` R ) ` A ) = inf ( ran ( x e.
        { z e. ~P dom R | ( A C_ U. z /\ z ~<_ _om ) }
      |-> sum* y e. x ( R ` y ) ) , ( 0 [,] +oo ) , < ) ) $=
      ( va wcel cc0 cpnf cuni wss cv wa cmpt clt cvv wceq cxr cicc w3a com cdom
      co wbr cdm cpw crab cfv cesum crn cinf coms simp2 simp1 fexd omsval simpr
      syl sseq1d anbi1d rabbidv mpteq1d rneqd infeq1d simp3 fdm 3ad2ant2 unieqd
      wf sseqtrrd wb uniexd ssexg syl2anc elpwg mpbird wor xrltso iccssxr ax-mp
      wi soss mp1i infexd fvmptd ) EGIZEJKUAUEZFVKZDELZMZUBZHDAHNZCNZLZMZWOUCUD
      UFZOZCFUGZUHZUIZANBNFUJBUKZPZULZWIQUMZADWPMZWROZCXAUIZXCPZULZWIQUMWTLZUHZ
      FUNUJZRWMFRIXNHXMXFPSWMEWIGFWHWJWLUOWHWJWLUPZUQABCFHURUTWMWNDSZOZWIXEXKQX
      QXDXJXQAXBXIXCXQWSXHCXAXQWQXGWRXQWNDWPWMXPUSVAVBVCVDVEVFWMDXMIZDXLMZWMDWK
      XLWHWJWLVGZWMWTEWJWHWTESWLEWIFVHVIVJVLWMDRIZXRXSVMWMWLWKRIYAXTWMEGXOVNDWK
      RVOVPDXLRVQUTVRWMWIXKQTQVSZWIQVSZWMVTWITMYBYCWCJKWAWITQWDWBWEWFWG $.

    $( A closure lemma for the constructed outer measure.  (Contributed by
       Thierry Arnoux, 17-Sep-2019.) $)
    omscl $p |- ( ( Q e. V /\ R : Q --> ( 0 [,] +oo ) /\ A e. ~P U. dom R )
      -> ran ( x e. { z e. ~P dom R | ( A C_ U. z /\ z ~<_ _om ) }
        |-> sum* y e. x ( R ` y ) ) C_ ( 0 [,] +oo ) ) $=
      ( wcel cc0 cpnf cicc cuni cpw cv wss wa wral cvv syl ralrimiva co cdm w3a
      wf cfv cesum com cdom wbr crab crn vex simp2 ad2antrr ssrab2 simpr sselid
      cmpt wceq pweqd adantr eleqtrd elpwi sselda ffvelcdmd nfcv esumcl sylancr
      fdm eqid rnmptss ) EGHZEIJKUAZFUDZDFUBZLMHZUCZANZBNZFUEZBUFZVMHZADCNZLOWC
      UGUHUIPZCVOMZUJZQAWFWAURZUKVMOVQWBAWFVQVRWFHZPZVRRHVTVMHZBVRQWBAULWIWJBVR
      WIVSVRHZPEVMVSFVQVNWHWKVLVNVPUMZUNWIVREVSWIVREMZHVREOWIVRWEWMWIWFWEVRWDCW
      EUOVQWHUPUQVQWEWMUSZWHVQVNWNWLVNVOEEVMFVIUTSVAVBVREVCSVDVETVRVTBRBVRVFVGV
      HTAWFWAVMWGWGVJVKS $.

    $( A constructed outer measure is a function.  (Contributed by Thierry
       Arnoux, 17-Sep-2019.)  (Revised by AV, 4-Oct-2020.) $)
    omsf $p |- ( ( Q e. V /\ R : Q --> ( 0 [,] +oo ) ) ->
      ( toOMeas ` R ) : ~P U. dom R --> ( 0 [,] +oo ) ) $=
      ( va vx vz vy vt vw vs wcel wa cuni cpw cv wss wbr cfv clt cxr cpnf co wf
      cc0 cicc cdm com cdom crab cmpt crn cinf coms wor iccssxr xrltso soss mp2
      cesum a1i wn wral wrex wi omscl 3expa xrge0infss syl infcl cvv fex ancoms
      wceq omsval simpll simplr simpr fdm unieqd pweqd ad2antlr eleqtrd omsfval
      elpwi syl3anc eqeltrd fmpt2d ) ACKZAUDUAUEUBZBUCZLZDDBUFZMZNZEDOZFOZMPWPU
      GUHQLFWLNUIEOGOBRGUSUJUKZWISULZWIBUMRZWIWKWOWNKZLZHIJWIWQSWISUNZXAWITPTSU
      NXBUDUAUOUPWITSUQURUTXAWQWIPZIOZHOZSQVAIWQVBXEXDSQJOXDSQJWQVCVDIWIVBLHWIV
      CWHWJWTXCEGFWOABCVEVFHIJWQVGVHVIZWKBVJKZWSDWNWRUJVMWJWHXGAWICBVKVLEGFBDVN
      VHXAWOWSRZWRWIXAWHWJWOAMZPZXHWRVMWHWJWTVOWHWJWTVPXAWOXINZKXJXAWOWNXKWKWTV
      QWJWNXKVMWHWTWJWMXIWJWLAAWIBVRVSVTWAWBWOXIWDVHEGFWOABCWCWEXFWFWG $.
  $}

  ${
    $d Q x y z $.  $d R a x y z $.  $d V x y z $.  $d a x y z ph $.
    oms.m $e |- M = ( toOMeas ` R ) $.
    oms.o $e |- ( ph -> Q e. V ) $.
    oms.r $e |- ( ph -> R : Q --> ( 0 [,] +oo ) ) $.
    ${
      oms.d $e |- ( ph -> (/) e. dom R ) $.
      oms.0 $e |- ( ph -> ( R ` (/) ) = 0 ) $.
      $( A constructed outer measure evaluates to zero for the empty set.
         (Contributed by Thierry Arnoux, 15-Sep-2019.)  (Revised by AV,
         4-Oct-2020.) $)
      oms0 $p |- ( ph -> ( M ` (/) ) = 0 ) $=
        ( vx vy c0 cc0 wa clt wcel wceq cxr cvv vz cfv coms fveq1i cuni wss com
        va cv cdom wbr cdm cpw crab cesum cmpt crn cpnf cicc co cinf 0ss unieqd
        fdmd sseqtrid omsfval syl3anc wor iccssxr xrltso soss mp2 a1i 0e0iccpnf
        wf wrex csn snssd p0ex elpw sylibr snct ax-mp pm3.2i jctir unieq sseq2d
        0ex breq1 anbi12d elrab simpr fveq2d adantr eqtrd esumsn eqcomd esumeq1
        rspceeqv syl2anc wb 0xr eqid elrnmpt wn cle nfmpt1 nfrn nfcri nfan wral
        nfv vex nfesum1 nfmpt nfeq2 ad4antr ssrab2 simpllr sselid pweqd eleqtrd
        nfcv elpwid sseldd ffvelcdmd ex ralrimi esumcl sylancr eqeltrd r19.29af
        bilani pnfxr iccgelb mp3an12 syl xrlenlt bicomd mpbird infmin eqtrid )
        AMDUBMCUCUBZUBZNMDUUCFUDAUUDKMUAUIZUEZUFZUUEUGUJUKZOZUACULZUMZUNZKUIZLU
        IZCUBZLUOZUPZUQZNURUSUTZPVAZNABEQBUUSCVOZMBUEZUFUUDUUTRGHAUUJUEZMUVBUVC
        VBAUUJBABUUSCHVDZVCVEKLUAMBCEVFVGAUHUUSUURNPUUSPVHZAUUSSUFSPVHUVENURVIZ
        VJUUSSPVKVLVMNUUSQAVNVMZANUUPRKUULVPZNUURQZAMVQZUULQZNUVJUUOLUOZRUVHAUV
        JUUKQZMUVJUEZUFZUVJUGUJUKZOZOUVKAUVMUVQAUVJUUJUFUVMAMUUJIVRUVJUUJVSVTWA
        UVOUVPUVNVBMTQUVPWHMTWBWCWDWEUUIUVQUAUVJUUKUUEUVJRZUUGUVOUUHUVPUVRUUFUV
        NMUUEUVJWFWGUUEUVJUGUJWIWJWKWAAUVLNAUUONLMUUJAUUNMRZOZUUOMCUBZNUVTUUNMC
        AUVSWLWMAUWANRUVSJWNWOIUVGWPWQKUVJUULUUPUVLNUUMUVJUUOLWRWSWTNSQZUVIUVHX
        AXBKUULUUPNUUQSUUQXCZXDWCWAAUHUIZUURQZOZUWDNPUKXEZNUWDXFUKZUWFUWDUUSQZU
        WHUWFUWDUUPRZUWIKUULAUWEKAKXLKUHUURKUUQKUULUUPXGXHXIXJUWFUUMUULQZOZUWJO
        ZUWDUUPUUSUWLUWJWLUWMUUMTQUUOUUSQZLUUMXKUUPUUSQKXMUWMUWNLUUMUWLUWJLUWFU
        WKLAUWELALXLLUHUURLUUQLKUULUUPLUULYCUUMUUOLLUUMYCZXNZXOXHXIXJUWKLXLXJLU
        WDUUPUWPXPXJUWMUUNUUMQZUWNUWMUWQOZBUUSUUNCAUVAUWEUWKUWJUWQHXQUWRUUMBUUN
        UWRUUMBUWRUUMUUKBUMZUWRUULUUKUUMUUIUAUUKXRUWFUWKUWJUWQXSXTAUUKUWSRUWEUW
        KUWJUWQAUUJBUVDYAXQYBYDUWMUWQWLYEYFYGYHUUMUUOLTUWOYIYJYKUWEUWJKUULVPZAU
        WDTQUWEUWTXAUHXMKUULUUPUWDUUQTUWCXDWCYMYLZUWBURSQUWIUWHXBYNNURUWDYOYPYQ
        UWFUWBUWDSQZUWGUWHXAXBUWFUUSSUWDUVFUXAXTUWBUXBOUWHUWGNUWDYRYSYJYTUUAWOU
        UB $.
    $}

    ${
      $d A x y z $.  $d B x y z $.  $d Q x y z $.  $d V x y z $.
      omsmon.a $e |- ( ph -> A C_ B ) $.
      omsmon.b $e |- ( ph -> B C_ U. Q ) $.
      $( A constructed outer measure is monotone.  Note in Example 1.5.2 of
         [Bogachev] p. 17.  (Contributed by Thierry Arnoux, 15-Sep-2019.)
         (Revised by AV, 4-Oct-2020.) $)
      omsmon $p |- ( ph -> ( M ` A ) <_ ( M ` B ) ) $=
        ( vx vz vy cfv wss wa wcel syl coms cle cuni com cdom wbr cdm cpw cesum
        cv crab cmpt crn cc0 cpnf cicc co cinf cres wceq wi adantr sstr2 anim1d
        clt ss2rabdv resmpt resss eqsstrrdi rnss wral wf ad2antrr ssrab2 simplr
        sselid elpwi fdmd sseqtrd simpr sseldd ffvelcdmd ralrimiva cvv vex nfcv
        esumcl rnmptss xrge0infssd sstrd omsfval syl3anc 3brtr4d fveq1i 3brtr4g
        mpan eqid ) ABEUAPZPZCWRPZBFPCFPUBAMBNUJZUCZQZXAUDUEUFZRZNEUGZUHZUKZMUJ
        ZOUJZEPZOUIZULZUMZUNUOUPUQZVEURZMCXBQZXDRZNXGUKZXLULZUMZXOVEURZWSWTUBAX
        NYAAXTXMQYAXNQAXTXMXSUSZXMAXSXHQYCXTUTAXRXENXGAXAXGSZRZXQXCXDYEBCQZXQXC
        VAAYFYDKVBBCXBVCTVDVFMXHXSXLVGTXMXSVHVIXTXMVJTAXLXOSZMXHVKXNXOQAYGMXHAX
        IXHSZRZXKXOSZOXIVKZYGYIYJOXIYIXJXISZRZDXOXJEADXOEVLZYHYLJVMYMXIDXJYMXIX
        FDYMXIXGSXIXFQYMXHXGXIXENXGVNAYHYLVOVPXIXFVQTAXFDUTYHYLADXOEJVRVMVSYIYL
        VTWAWBWCXIWDSYKYGMWEXIXKOWDOXIWFWGWPTWCMXHXLXOXMXMWQWHTWIADGSZYNBDUCZQW
        SXPUTIJABCYPKLWJMONBDEGWKWLAYOYNCYPQWTYBUTIJLMONCDEGWKWLWMBFWRHWNCFWRHW
        NWO $.
    $}

    $d A e t u w x z $.  $d E u x $.  $d M u x $.  $d Q w x z $.
    $d R e t u w x z $.  $d V w x z $.  $d ph u $.
    ${
      omssubaddlem.a $e |- ( ph -> A C_ U. Q ) $.
      omssubaddlem.m $e |- ( ph -> ( M ` A ) e. RR ) $.
      omssubaddlem.e $e |- ( ph -> E e. RR+ ) $.
      $( For any small margin ` E ` , we can find a covering approaching the
         outer measure of a set ` A ` by that margin.  (Contributed by Thierry
         Arnoux, 18-Sep-2019.)  (Revised by AV, 4-Oct-2020.) $)
      omssubaddlem $p |- ( ph -> E. x e. { z e. ~P dom R | ( A C_ U. z
        /\ z ~<_ _om ) } sum* w e. x ( R ` w ) < ( ( M ` A ) + E ) ) $=
        ( vu clt wbr wcel ve vt cv cfv caddc co cuni wss com cdom cdm cpw cesum
        crab cmpt crn wrex cc0 cpnf cicc cinf cxr cle rpred readdcld rexrd coms
        wa wf omsf syl2anc feq1i sylibr unieqd sseqtrrd cvv wb uniexd jca ssexg
        fdmd elpwg mpbird ffvelcdmd elxrge0 simprbi syl rpge0d addge0d sylanbrc
        3syl fveq1i omsfval syl3anc eqtr2id ltaddrpd eqbrtrd wor iccssxr xrltso
        wceq soss mp2 a1i wn wral wi omscl xrge0infss infglb mp2and eqid esumex
        wex elrnmpti anbi1i r19.41v bitr4i exbii df-rex rexcom4 3bitr4i exlimiv
        breq1 biimpa reximi sylbi ) AQUCZEIUDZHUEUFZRSZQBECUCZUGUHYLUIUJSVHCGUK
        ZULUNZBUCZDUCGUDZDUMZUOZUPZUQZYQYJRSZBYNUQZAYJURUSUTUFZTZYSUUCRVAZYJRSY
        TAYJVBTURYJVCSUUDAYJAYIHOAHPVDZVEVFAYIHOUUFAYIUUCTZURYIVCSZAYMUGZULZUUC
        EIAUUJUUCGVGUDZVIZUUJUUCIVIAFJTZFUUCGVIZUULLMFGJVJVKUUJUUCIUUKKVLVMAEUU
        JTZEUUIUHZAEFUGZUUINAYMFAFUUCGMWAVNVOAEUUQUHZUUQVPTZVHEVPTUUOUUPVQAUURU
        USNAFJLVRVSEUUQVPVTEUUIVPWBWKWCZWDUUGYIVBTUUHYIWEWFWGAHPWHWIYJWEWJAUUEY
        IYJRAYIEUUKUDZUUEEIUUKKWLAUUMUUNUURUVAUUEXALMNBDCEFGJWMWNWOAYIHOPWPWQAU
        AUBQUUCYSYJRUUCRWRZAUUCVBUHVBRWRUVBURUSWSWTUUCVBRXBXCXDAYSUUCUHZUBUCZUA
        UCZRSXEUBYSXFUVEUVDRSYHUVDRSQYSUQXGUBUUCXFVHUAUUCUQAUUMUUNUUOUVCLMUUTBD
        CEFGJXHWNUAUBQYSXIWGXJXKYTYHYQXAZYKVHZQXNZBYNUQZUUBYHYSTZYKVHZQXNUVGBYN
        UQZQXNYTUVIUVKUVLQUVKUVFBYNUQZYKVHUVLUVJUVMYKBYNYQYHYRYRXLYOYPDXMXOXPUV
        FYKBYNXQXRXSYKQYSXTUVGBQYNYAYBUVHUUABYNUVGUUAQUVFYKUUAYHYQYJRYDYEYCYFYG
        WG $.
    $}

    ${
      $d f g A $.  $d A e f g t u w x z $.  $d A h u v w x z $.
      $d e f g x M $.  $d x y z Q $.  $d w x y z Q $.
      $d c e g t u w x y z R $.  $d R h u v w x z $.  $d V w x y z $.
      $d c e f g t u w x y z X $.  $d c e f g u w x y z ph $.
      omssubadd.a $e |- ( ( ph /\ y e. X ) -> A C_ U. Q ) $.
      omssubadd.b $e |- ( ph -> X ~<_ _om ) $.
      $( A constructed outer measure is countably sub-additive.  Lemma 1.5.4 of
         [Bogachev] p. 17.  (Contributed by Thierry Arnoux, 21-Sep-2019.)
         (Revised by AV, 4-Oct-2020.) $)
      omssubadd $p |- ( ph -> ( M ` U_ y e. X A ) <_ sum* y e. X ( M ` A ) ) $=
        ( vz vw wcel wbr wa clt cvv vf ve vg vx vu vv vh vc vt cfv cesum cr cle
        ciun cn cv wex cdom com sylancl syl adantr caddc crp wral cpw crab cuni
        co wss cexp cdiv wrex simplll ctex nfv nfcv nfan cmpt crn cc0 cpnf cinf
        wf c2 simpr cxad wceq sylibr syl2anc wb mpbird ffvelcdmd adantlr rpssre
        elpwg simplr 2rp a1i ccnv wfun adantl rpexpcld rpdivcld sselid adantl3r
        nnzd sylan syl3anc cxr wn wi imp syl21anc eqid breq1 ax-mp unieq sseq2d
        anbi12d elrab simprbi simpld mpd ralrimi ad2antrr ralrimiva 3syl sselda
        ex esumcl rexrd simpllr sylib ralimi c1 cxmu oveq2d cc xrletrd wf1 nfel
        cen nnenom ensymi domentr brdomi cdm nfesum1 cicc coms omsf fdmd unieqd
        feq1i uniexd ssexg esumcvgre df-f1 simplbi ffvelcdmda rexadd cioo dfrp2
        sseqtrrd ioossicc eqsstri xrge0addcld eqeltrrd rpgt0d 2re adantllr 2pos
        cz expgt0 divgt0d ltaddposd fveq1i omsfval eqtrid eqcomd breq1d jca wor
        mpbid xrltso soss mp2 biid mpbi omscl xrge0infss infglb esumex elrnmpti
        iccssxr anbi1i r19.41v bitr4i df-rex rexcom4 3bitr4i idd sylbid exlimiv
        exbii reximi sylbi ss2rabi rexss anim1d reximdv biimtrid esumeq1 iunexg
        ac6sg iunss ad4antr rnexg uniexg simp-5l frn ssrab2 sstrdi unissd unipw
        fexd sseqtrdi sseqtrd simp-5r rpxrd xaddcld ad2antlr sstr mpan2 sspwuni
        fnct rnct dfss3 biimpi unictb syl2an simpl fvssunirn unissi jca32 fveq2
        wfn cbvesumv rspceeqv elrnmpt inflb breq2d notbid sylibrd xrlenlt nfra1
        sylc simp-6l ad3antrrr elpwid fssdmd fvex mpan fniunfv esumeq1d esumiun
        ffn sseldd eqbrtrrd eqbrtrid simp-4l id biimpar xrltle adantld r19.21bi
        syld ralim esumlef esumaddf simp-4r vex rnex frnd rpreccld syldan sseli
        1xr elxrge0 nnex esummono csu oveq2 cico ioossico eqidd fvmptd cseq cli
        ovexd ax-1cn geo2lim 1re esumcvgsum geoihalfsum eqtrdi breqtrd xlemul2a
        syl31anc cmul recnd wne 2cn 2ne0 expne0d divrecd rexmul eqtr4d esumeq2d
        1rp esummulc2 cab feqmptd cnveqd funeqd fnrnfv 3eqtr2rd xmulrid 3brtr3d
        esumc xleadd2a eqbrtrd rpred anasss exlimdv xralrple xrge0nre pm2.61dan
        pnfge breqtrrd ) AHCFUJZBUKZULPZBHCUNZFUJZWUCUMQZAWUDRZHUOUAUPZUUAZUAUQ
        ZWUGAWUKWUDAHUOURQZWUKAHUSURQZUSUOUUCQWULMUOUSUUDUUEHUSUOUUFUTHUOUAUUGV
        AVBWUHWUJWUGUAWUHWUJWUGWUHWUJRZWUGWUFWUCUBUPZVCVIZUMQZUBVDVEZWUNWUQUBVD
        WUNWUOVDPZRZHNUPZUSURQZNEUUHZVFZVGZUCUPZWDZCBUPZWVFUJZVHZVJZWVIOUPZEUJZ
        OUKZWUBWUOWEWVHWUIUJZVKVIZVLVIZVCVIZSQZRZBHVEZRZUCUQZWUQWUTHTPZCUDUPZVH
        ZVJZWWEWVMOUKZWVRSQZRZUDWVEVMZBHVEZWWCWUTAWWDAWUDWUJWUSVNZAWUMWWDMHVOZV
        AZVAWUTWWKBHWUNWUSBWUHWUJBAWUDBABVPZBWUCULHWUBBBHVQZUUIBULVQUUBVRZWUJBV
        PZVRWUSBVPZVRZWUTWVHHPZWWKWUTWXBRZWWIUDCWVAVHZVJZWVBRZNWVDVGZVMZWWKWXCU
        EUPZWVRSQZUEUDWXGWWHVSZVTZVMZWXHWXCAWXBWVRWAWBUUJVIZPZWXLWXNSWCZWVRSQZR
        ZWXMWUTAWXBWWMVBWUTWXBWFWXCWXOWXQWXCWUBWVQWGVIZWVRWXNWXCWUBULPZWVQULPZW
        XSWVRWHWUNWXBWXTWUSWUHWXBWXTWUJWUHHWUBBTWWRAWWDWUDWWOVBZAWXBWUBWXNPZWUD
        AWXBRZWVCVHZVFZWXNCFAWYFWXNFWDZWXBADGPZDWXNEWDZWYGJKWYHWYIRWYFWXNEUUKUJ
        ZWDWYGDEGUULWYFWXNFWYJIUUOWIWJZVBWYDCWYFPZCWYEVJZWYDCDVHZWYELAWYEWYNWHW
        XBAWVCDADWXNEKUUMZUUNZVBUVEZWYDCTPZWYLWYMWKWYDCWYNVJZWYNTPZWYRLAWYTWXBA
        DGJUUPVBCWYNTUUQWJZCWYETWPVAWLZWMZWNAWUDWFUURZWNWNZAWUJWUSWXBWYAWUDAWUJ
        RZWUSRZWXBRZVDULWVQWOXUHWUOWVPXUFWUSWXBWQZXUFWXBWVPVDPWUSXUFWXBRZWEWVOW
        EVDPZXUJWRWSXUJWVOXUFHUOWVHWUIWUJHUOWUIWDZAWUJXULWUIWTZXAZHUOWUIUUSZUUT
        ZXBZUVAZXGZXCZWNXDZXEXFZWUBWVQUVBZWJWXCWUBWVQWUTAWXBWYCWWMXUCXHAWUJWUSW
        XBWVQWXNPZWUDXUHVDWXNWVQVDWAWBUVCVIZWXNUVDWAWBUVFUVGZXVAXEXFZUVHUVIWXCW
        XQWUBWVRSQZWXCWAWVQSQXVHWXCWUOWVPAWUJWUSWXBWUOULPZWUDXUHVDULWUOWOXUIXEZ
        XFAWUJWUSWXBWVPULPZWUDXUFWXBXVKWUSXUJVDULWVPWOXUTXEZWNXFWXCWUOWUNWUSWXB
        WQUVJWXCWEULPZWVOUVNPZWAWESQZWAWVPSQXVMWXCUVKWSWUNWXBXVNWUSAWUJWXBXVNWU
        DXUSUVLWNXVOWXCUVMWSWEWVOUVOXIUVPWXCWVQWUBXVBXUEUVQUWEWXCWXPWUBWVRSWXCW
        UBWXPWUTAWXBWUBWXPWHWWMWYDWUBCWYJUJZWXPCFWYJIUVRWYDWYHWYIWYSXVPWXPWHAWY
        HWXBJVBZAWYIWXBKVBZLUDONCDEGUVSXIUVTXHUWAUWBWLUWCWYDWXRWXMWYDUFUGUEWXNW
        XLWVRSWXNSUWDZWYDXVSXVSWXNXJVJXJSUWDXVSWAWBUWPZUWFWXNXJSUWGUWHXVSUWIUWJ
        ZWSWYDWXLWXNVJZUGUPZUFUPZSQXKUGWXLVEXWDXWCSQWXIXWCSQUEWXLVMXLUGWXNVERUF
        WXNVMWYDWYHWYIWYLXWBXVQXVRXUBUDONCDEGUWKXIUFUGUEWXLUWLVAUWMXMXNWXMWXIWW
        HWHZWXJRZUEUQZUDWXGVMZWXHWXIWXLPZWXJRZUEUQXWFUDWXGVMZUEUQWXMXWHXWJXWKUE
        XWJXWEUDWXGVMZWXJRXWKXWIXWLWXJUDWXGWWHWXIWXKWXKXOWWEWVMOUWNUWOUWQXWEWXJ
        UDWXGUWRUWSUXFWXJUEWXLUWTXWFUDUEWXGUXAUXBXWGWWIUDWXGXWFWWIUEXWEWXJWWIXW
        EWXJWWIWWIWXIWWHWVRSXPXWEWWIUXCUXDXMUXEUXGUXHVAWXHWWEWXGPZWWIRZUDWVEVMZ
        WXCWWKWXGWVEVJWXHXWOWKWXFWVBNWVDWXFWVBXLWVAWVDPWXEWVBWFWSUXIWWIUDWXGWVE
        UXJXQWXCXWNWWJUDWVEWXCXWMWWGWWIXWMWWGXLWXCXWMWWGWWEUSURQZXWMWWEWVDPWWGX
        WPRZWXFXWQNWWEWVDWVAWWEWHZWXEWWGWVBXWPXWRWXDWWFCWVAWWEXRXSWVAWWEUSURXPX
        TYAYBYCWSUXKUXLUXMYDYJYEWWDWWLWWCWWJWVTBUDHWVEUCTWWEWVIWHZWWGWVKWWIWVSX
        WSWWFWVJCWWEWVIXRXSXWSWWHWVNWVRSWWEWVIWVMOUXNUWBXTUXPXMWJWUTWWBWUQUCWUT
        WWBWUQWUTWVGWWAWUQWUTWVGRZWWARZWUFWUCWUOWGVIZWUPUMXXAWUFWVFVTZVHZUHUPZE
        UJZUHUKZXXBXXAAWUFXJPZWUTAWVGWWAWWMYFZAWXNXJWUFXVTAWYFWXNWUEFWYKAWUEWYF
        PZWUEWYEVJZAWYMBHVEXXKAWYMBHWYQYGBHCWYEUXQWIZAWUETPZXXJXXKWKAWWDWYRBHVE
        XXMWWOAWYRBHXUAYGBHCTTUXOWJWUEWYETWPVAWLZWMXEZVAZXXAWXNXJXXGXVTXXAXXDTP
        ZXXFWXNPZUHXXDVEZXXGWXNPXXAWVFTPXXCTPXXQXXAHWVETWVFWUTWVGWWAWQZWUHWWDWU
        JWUSWVGWWAWYBUXRZUYGWVFTUXSXXCTUXTYHXXAAWVGXXSAWUDWUJWUSWVGWWAUYAXXTAWV
        GRZXXRUHXXDXYBXXEXXDPZRDWXNXXEEAWYIWVGXYCKYFXYBXXDDXXEXYBXXDWVCDWVGXXDW
        VCVJZAWVGXXDWVDVHWVCWVGXXCWVDWVGXXCWVEWVDHWVEWVFUYBZWVBNWVDUYCZUYDUYEWV
        CUYFUYHXBAWVCDWHWVGWYOVBUYIYIWMYGWJXXDXXFUHTUHXXDVQYKWJXEZXXAWUCWUOXXAW
        UCAWUDWUJWUSWVGWWAUYJZYLZXXAWUOWUNWUSWVGWWAYMZUYKZUYLZXXAWUFXXGUMQZXXGW
        UFSQZXKZXXAXYOXYOXXAAXXGUDWUEWXDVJZWVBRZNWVDVGZWWHVSZVTZPZXYOXXIXXAXXGW
        WHWHUDXYRVMZYUAXXAXXDXYRPZXXGXXDWVMOUKZWHYUBXXAXXDWVDPZWUEXXDVHZVJZXXDU
        SURQZRZRYUCXXAYUEYUGYUHXXAYUEXYDXXAXXCWVEVJZXYDWVGYUJWUTWWAXYEUYMZYUJXX
        CWVDVJZXYDYUJWVEWVDVJYULXYFXXCWVEWVDUYNUYOXXCWVCUYPYNVAXXAYUHXXQYUEXYDW
        KXXAWVFHVUHZWUMYUJYUHWVGYUMWUTWWAHWVEWVFVVHZUYMXXAAWUMXXIMVAZYUKYUMWUMR
        ZXXCUSURQZWVLUSURQZOXXCVEZYUHYUJYUPWVFUSURQYUQHWVFUYQWVFUYRVAYUJWVLWVEP
        ZOXXCVEZYUSYUJYVAOXXCWVEUYSUYTYUTYUROXXCYUTWVLWVDPYURWVBYURNWVLWVDWVAWV
        LUSURXPYAYBYOVAOXXCVUAVUBXNZXXDVOXXDWVCTWPYHWLWWAYUGXWTWWAWVKBHVEZYUGWV
        TWVKBHWVKWVSVUCYOYVCCYUFVJZBHVEYUGWVKYVDBHWVKWVJYUFVJYVDWVIXXDWVFWVHVUD
        VUECWVJYUFUYNUYOYOBHCYUFUXQWIVAXBYVBVUFXYQYUINXXDWVDWVAXXDWHZXYPYUGWVBY
        UHYVEWXDYUFWUEWVAXXDXRXSWVAXXDUSURXPXTYAWIXXDXXFWVMUHOXXEWVLEVUGVUIZUDX
        XDXYRWWHYUDXXGWWEXXDWVMOUXNVUJUTXXGTPYUAYUBWKXXDXXFUHUWNUDXYRWWHXXGXYST
        XYSXOVUKXQWIAYUAXXGXYTWXNSWCZSQZXKXYOAUBUIUEWXNXYTXXGSXVSAXWAWSAXYTWXNV
        JZUIUPZWUOSQXKUIXYTVEWUOYVJSQWXIYVJSQUEXYTVMXLUIWXNVERUBWXNVMAWYHWYIXXJ
        YVIJKXXNUDONWUEDEGUWKXIUBUIUEXYTUWLVAVULAXYNYVHAWUFYVGXXGSAWUFWUEWYJUJZ
        YVGWUEFWYJIUVRAWYHWYIWUEWYNVJYVKYVGWHJKAWUEWYEWYNXXLWYPUYIUDONWUEDEGUVS
        XIUVTVUMVUNVUOVURXYOUWIYNXXAXXHXXGXJPXYMXYOWKXXPXYGWUFXXGVUPWJWLXXAXXGH
        WVNBUKZXXBXYGXXAWXNXJYVLXVTXXAWWDWVNWXNPZBHVEYVLWXNPXYAXXAYVMBHXWTWWABW
        UTWVGBWXAWVGBVPVRZWVTBHVUQVRZXXAWXBYVMXXAWXBRZAWVGWXBYVMAWUDWUJWUSWVGWW
        AWXBVUSZWUTWVGWWAWXBYMXXAWXBWFZXYBWXBRZWVMWXNPZOWVIVEZYVMYVSYVTOWVIYVSW
        VLWVIPZRZDWXNWVLEAWYIWVGWXBYWBKVUTZYWCWVIDWVLYWCDWXNWVIEYWDYWCWVIWVCYWC
        WVEWVDWVIXYFYWCHWVEWVHWVFAWVGWXBYWBYMXYBWXBYWBWQWMXEVVAVVBYVSYWBWFVVIWM
        ZYGWVITPZYWAYVMWVHWVFVVCZWVIWVMOTOWVIVQYKVVDVAZXNZYJYEHWVNBTWWQYKWJXEZX
        YLXXAXXGYUDYVLUMYVFXWTYUDYVLUMQZWWAWUTAWVGYWKWWMXYBBHWVIUNZWVMOUKYUDYVL
        UMXYBYWLXXDWVMOXYBOVPXYBWVGYUMYWLXXDWHAWVGWFYUNBHWVFVVEYHVVFXYBHWVIWVMB
        OTTAWWDWVGWWOVBYWFYVSYWGWSYWEVVGVVJXHVBVVKXXAYVLHWXSBUKZXXBYWJXXAWXNXJY
        WMXVTXXAWWDWXSWXNPZBHVEYWMWXNPXYAXXAYWNBHYVOXXAWXBYWNYVPWUBWVQYVPAWXBWY
        CYVQYVRXUCWJYVPWUTWXBXVDWUTWVGWWAWXBVNYVRXVGWJZUVHZYJYEHWXSBTWWQYKWJXEX
        YLXXAHWVNWXSBTYVOWWQXXAWUMWWDYUOWWNVAZYWIYWPXXAWVNWXSUMQZBHXWTWWAYWRBHV
        EZXWTWVTYWRXLZBHVEWWAYWSXLXWTYWTBHYVNXWTWXBYWTXWTWXBRZWVSYWRWVKYXAWVSWV
        NWXSSQZYWRYXAWVSYXBYXAWVSRWXTWYAWVSYXBYXAWXTWVSYXAWUHWXBWXTWUHWUJWUSWVG
        WXBVVLZXWTWXBWFZXUDWJZVBYXAWYAWVSWUTWXBWYAWVGXVBWNZVBWVSWVSYXAWVSVVMXBW
        XTWYARZYXBWVSYXGWXSWVRWVNSXVCVUMVVNXNYJYXAWVNXJPWXSXJPYXBYWRXLYXAWXNXJW
        VNXVTYXAAWVGWXBYVMYXAAWUDYXCYCWUTWVGWXBWQYXDYWHXNXEYXAWUBWVQYXAWUBYXEYL
        YXAWVQYXFYLUYLWVNWXSVVOWJVVRVVPYJYEWVTYWRBHVVSVAXMVVQVVTXXAYWMWUCHWVQBU
        KZWGVIZXXBUMXXAHWUBWVQBTYVOWWQYWQXXAAWXBWYCXXIXUCXHYWOVWAXXAYXHXJPWUOXJ
        PZWUCXJPYXHWUOUMQZYXIXXBUMQXXAWXNXJYXHXVTXXAWWDXVDBHVEYXHWXNPXYAXXAXVDB
        HYVOXXAWXBXVDYWOYJYEHWVQBTWWQYKWJXEXYKXYIXXAAWUJWUSYXKXXIWUHWUJWUSWVGWW
        AVWBXYJXUGWUOWUIVTZYPWEWVAVKVIZVLVIZNUKZYQVIZWUOYPYQVIZYXHWUOUMXUGYXOXJ
        PYPXJPZYXJWAWUOUMQZRZYXOYPUMQZYXPYXQUMQXUGWXNXJYXOXVTXUGYXLTPZYXNWXNPZN
        YXLVEYXOWXNPYYBXUGWUIUAVWCVWDWSXUGYYCNYXLXUGWVAYXLPWVAUOPZYYCXUGYXLUOWV
        AXUFYXLUOVJWUSXUFHUOWUIXUQVWEZVBYIXUFYYDYYCWUSXUFYYDRZVDWXNYXNXVFYYFYXM
        YYFWEWVAXUKYYFWRWSYYFWVAXUFYYDWFXGXCVWFZXEZWNVWGYGYXLYXNNTNYXLVQYKWJXEY
        XRXUGVWIWSXUGWUOWXNPZYXTWUSYYIXUFVDWXNWUOXVFVWHXBWUOVWJYNZXUFYYAWUSXUFY
        XOUOYXNNUKZYPUMXUFYXLYXNUONTXUFNVPZUOTPXUFVWKWSYYHYYEVWLXUFYYKUOYXNNVWM
        YPXUFYXNYPWEWVLVKVIZVLVIZONOUOYYNVSZYPWVAWVLWHYXMYYMYPVLWVAWVLWEVKVWNYR
        YYFVDWAWBVWOVIZYXNVDXVEYYPUVDWAWBVWPUVGZYYGXEYYDWVAYYOUJYXNWHXUFYYDOWVA
        YYNYXNUOYYOTYYDYYOVWQYYDWVLWVAWHZRZYYMYXMYPVLYYSWVLWVAWEVKYYDYYRWFYRYRY
        YDVVMYYDYPYXMVLVXAVWRXBVCYYOYPVWSYPVWTQZXUFYPYSPYYTVXBYPOYYOYYOXOVXCXQW
        SYPULPXUFVXDWSVXENVXFVXGVXHVBYXOYPWUOVXIVXJXUGYXHHWUOYPWVPVLVIZYQVIZBUK
        WUOHUUUABUKZYQVIYXPXUGHWVQUUUBBXUFWUSBAWUJBWWPWWSVRZWWTVRXUGWVQUUUBWHBH
        XUHWVQWUOUUUAVXKVIZUUUBXUHWUOWVPXUHWUOXVJVXLXUFWXBWVPYSPWUSXUJWVPXVLVXL
        WNXUFWXBWVPWAVXMWUSXUJWEWVOWEYSPXUJVXNWSWEWAVXMXUJVXOWSXUSVXPWNVXQXUHXV
        IUUUAULPZUUUBUUUEWHXVJXUFWXBUUUFWUSXUJVDULUUUAWOXUJYPWVPYPVDPXUJVYAWSXU
        TXDZXEWNWUOUUUAVXRWJVXSYGVXTXUGHUUUAWUOBTAWWDWUJWUSWWOYFXUFWXBUUUAWXNPW
        USXUJVDWXNUUUAXVFUUUGXEZWNXUFVDYYPWUOVDYYPVJXUFYYQWSYIVYBXUGUUUCYXOWUOY
        QXUFUUUCYXOWHWUSXUFUUUCWWEWVOWHBHVMUDVYCZYXNNUKYXOXUFNUDHUUUAWVOYXNBTUO
        BYXNVQUUUDWWQWVAWVOWHYXMWVPYPVLWVAWVOWEVKVWNYRAWWDWUJWWOVBWUJBHWVOVSZWT
        ZXAZAWUJXUNUUULWUJXULXUNXUOYBWUJXUMUUUKWUJWUIUUUJWUJBHUOWUIXUPVYDVYEVYF
        UWEXBUUUHXURVYKXUFYXLUUUIYXNNYYLXUFXULWUIHVUHYXLUUUIWHXUQHUOWUIVVHBUDHW
        UIVYGYHVVFVXSVBYRVYHXUGYXJYXQWUOWHXUGYXJYXSYYJYCWUOVYIVAVYJXNYXHWUOWUCV
        YLVXJVYMYTYTYTXXAWUDXVIXXBWUPWHXYHXXAWUOXYJVYNWUCWUOUVBWJVXHVYOYJVYPYDY
        GWUHWUGWURWKZWUJAXXHWUDUUUMXXOUBWUFWUCVYQXHVBWLYJVYPYDAWUDXKZRZWUFWBWUC
        UMUUUOXXHWUFWBUMQAXXHUUUNXXOVBWUFVYTVAAWUCWXNPZUUUNWUCWBWHAWWDWYCBHVEUU
        UPWWOAWYCBHXUCYGHWUBBTWWQYKWJWUCVYRXHWUAVYS $.
    $}
  $}

  $c toCaraSiga $.

  $( Class declaration for the Caratheodory sigma-Algebra construction. $)
  ccarsg $a class toCaraSiga $.

  ${
    $d m a e $.
    $( Define a function constructing Caratheodory measurable sets for a given
       outer measure.  See ~ carsgval for its value.  Definition 1.11.2 of
       [Bogachev] p. 41.  (Contributed by Thierry Arnoux, 17-May-2020.) $)
    df-carsg $a |- toCaraSiga = ( m e. _V |-> { a e. ~P U. dom m |
       A. e e. ~P U. dom m
         ( ( m ` ( e i^i a ) ) +e ( m ` ( e \ a ) ) ) = ( m ` e ) } ) $.
  $}

  ${
    $d M a e m $.  $d O a e m $.  $d a e m ph $.
    carsgval.1 $e |- ( ph -> O e. V ) $.
    carsgval.2 $e |- ( ph -> M : ~P O --> ( 0 [,] +oo ) ) $.
    $( Value of the Caratheodory sigma-Algebra construction function.
       (Contributed by Thierry Arnoux, 17-May-2020.) $)
    carsgval $p |- ( ph ->
       ( toCaraSiga ` M ) = { a e. ~P O | A. e e. ~P O
         ( ( M ` ( e i^i a ) ) +e ( M ` ( e \ a ) ) ) = ( M ` e ) } ) $=
      ( vm cv cfv cxad co wceq cdm cuni cpw cvv fveq1 wcel cin cdif wral ccarsg
      crab df-carsg wa simpr dmeqd cc0 cpnf cicc fdmd adantr eqtrd unieqd unipw
      eqtrdi pweqd oveq12d eqeq12d adantl raleqbidv rabeqbidv pwexd fexd rabexg
      wb pwexg 3syl fvmptd2 ) AICBJZFJZUAZIJZKZVLVMUBZVOKZLMZVLVOKZNZBVOOZPZQZU
      CZFWDUEVNCKZVQCKZLMZVLCKZNZBDQZUCZFWKUEZRUDRBIFUFAVOCNZUGZWEWLFWDWKWOWCDW
      OWCWKPDWOWBWKWOWBCOZWKWOVOCAWNUHUIAWPWKNWNAWKUJUKULMZCHUMUNUOUPDUQURUSZWO
      WAWJBWDWKWRWNWAWJVHAWNVSWHVTWIWNVPWFVRWGLVNVOCSVQVOCSUTVLVOCSVAVBVCVDAWKW
      QRCHADEGVEVFADETWKRTWMRTGDEVIWLFWKRVGVJVK $.

    $( Closure of the Caratheodory measurable sets.  (Contributed by Thierry
       Arnoux, 17-May-2020.) $)
    carsgcl $p |- ( ph -> ( toCaraSiga ` M ) C_ ~P O ) $=
      ( ve va ccarsg cfv cv cin cdif cxad co wceq cpw wral crab carsgval ssrab2
      eqsstrdi ) ABIJGKZHKZLBJUCUDMBJNOUCBJPGCQZRZHUESUEAGBCDHEFTUFHUEUAUB $.

    $d A a e $.
    $( Property of being a Caratheodory measurable set.  (Contributed by
       Thierry Arnoux, 17-May-2020.) $)
    elcarsg $p |- ( ph -> ( A e. ( toCaraSiga ` M )
       <-> ( A C_ O /\ A. e e. ~P O
         ( ( M ` ( e i^i A ) ) +e ( M ` ( e \ A ) ) ) = ( M ` e ) ) ) ) $=
      ( va cfv wcel cv cin cdif cxad co wceq wral wa fveq2d ccarsg cpw crab wss
      carsgval eleq2d ineq2 difeq2 oveq12d eqeq1d ralbidv elrab cvv wi elex a1i
      adantr simpr ssexd ex wb elpwg pm5.21ndd anbi1d bitrid bitrd ) ABDUAJZKBC
      LZILZMZDJZVHVINZDJZOPZVHDJZQZCEUBZRZIVQUCZKZBEUDZVHBMZDJZVHBNZDJZOPZVOQZC
      VQRZSZAVGVSBACDEFIGHUEUFVTBVQKZWHSAWIVRWHIBVQVIBQZVPWGCVQWKVNWFVOWKVKWCVM
      WEOWKVJWBDVIBVHUGTWKVLWDDVIBVHUHTUIUJUKULAWJWAWHABUMKZWJWAWJWLUNABVQUOUPA
      WAWLAWASBEFAEFKWAGUQAWAURUSUTWLWJWAVAUNABEUMVBUPVCVDVEVF $.

    ${
      baselcarsg.1 $e |- ( ph -> ( M ` (/) ) = 0 ) $.
      $( The universe set, ` O ` , is Caratheodory measurable.  (Contributed by
         Thierry Arnoux, 17-May-2020.) $)
      baselcarsg $p |- ( ph -> O e. ( toCaraSiga ` M ) ) $=
        ( ve cfv wcel wss cxad co wceq wa cc0 sylib fveq2d c0 adantr ccarsg cin
        cv cdif cpw wral ssidd elpwi adantl dfss2 ssdif0 eqtrd oveq12d cxr cpnf
        cicc iccssxr wf simpr ffvelcdmd sselid xaddrid syl ralrimiva jca mpbird
        elcarsg ) ACBUAIJCCKZHUCZCUBZBIZVICUDZBIZLMZVIBIZNZHCUEZUFZOAVHVRACUGAV
        PHVQAVIVQJZOZVNVOPLMZVOVTVKVOVMPLVTVJVIBVTVICKZVJVINVSWBAVICUHUIZVICUJQ
        RVTVMSBIZPVTVLSBVTWBVLSNWCVICUKQRAWDPNVSGTULUMVTVOUNJWAVONVTPUOUPMZUNVO
        PUOUQVTVQWEVIBAVQWEBURVSFTAVSUSUTVAVOVBVCULVDVEACHBCDEFVGVF $.

      $( The empty set is Caratheodory measurable.  (Contributed by Thierry
         Arnoux, 30-May-2020.) $)
      0elcarsg $p |- ( ph -> (/) e. ( toCaraSiga ` M ) ) $=
        ( ve c0 ccarsg cfv wcel cxad co wceq a1i cc0 fveq2i cxr cpnf wss cv cin
        cdif cpw wral 0ss wa eqtrid dif0 oveq12d adantr cicc iccssxr ffvelcdmda
        in0 sselid xaddlid syl eqtrd ralrimiva elcarsg mpbir2and ) AIBJKLICUAZH
        UBZIUCZBKZVEIUDZBKZMNZVEBKZOZHCUEZUFVDACUGPAVLHVMAVEVMLZUHZVJQVKMNZVKAV
        JVPOVNAVGQVIVKMAVGIBKQVFIBVEUPRGUIVIVKOAVHVEBVEUJRPUKULVOVKSLVPVKOVOQTU
        MNZSVKQTUNAVMVQVEBFUOUQVKURUSUTVAAIHBCDEFVBVC $.

      $( The union of all Caratheodory measurable sets is the universe.
         (Contributed by Thierry Arnoux, 22-May-2020.) $)
      carsguni $p |- ( ph -> U. ( toCaraSiga ` M ) = O ) $=
        ( va ccarsg cfv cuni wss wcel wceq cv wral wa cpw carsgcl sselda elpwid
        ralrimiva unissb sylibr baselcarsg unissel syl2anc ) ABIJZKZCLZCUHMUICN
        AHOZCLZHUHPUJAULHUHAUKUHMQUKCAUHCRUKABCDEFSTUAUBHUHCUCUDABCDEFGUEUHCUFU
        G $.
    $}

    ${
      difelcarsg.1 $e |- ( ph -> A e. ( toCaraSiga ` M ) ) $.
      $( Caratheodory measurable sets are subsets of the universe.
         (Contributed by Thierry Arnoux, 21-May-2020.) $)
      elcarsgss $p |- ( ph -> A C_ O ) $=
        ( ccarsg cfv cpw carsgcl sseldd elpwid ) ABDACIJDKBACDEFGLHMN $.

      $( The Caratheodory measurable sets are closed under complement.
         (Contributed by Thierry Arnoux, 17-May-2020.) $)
      difelcarsg $p |- ( ph -> ( O \ A ) e. ( toCaraSiga ` M ) ) $=
        ( ve cdif cfv wcel wss cin cxad co wceq wa c0 cxr ccarsg cv wral difssd
        cpw indif2 elpwi adantl dfss2 sylib difeq1d eqtrid fveq2d ssdif0 uneq1d
        cun difdif2 uncom un0 eqtr3i eqtrdi oveq12d cpnf cicc iccssxr wf adantr
        cc0 elpwdifcl ffvelcdmd sselid elpwincl1 xaddcom syl2anc elcarsg simprd
        simpr mpbid r19.21bi 3eqtrd ralrimiva jca mpbird ) ADBJZCUAKZLWDDMZIUBZ
        WDNZCKZWGWDJZCKZOPZWGCKZQZIDUEZUCZRAWFWPADBUDAWNIWOAWGWOLZRZWLWGBJZCKZW
        GBNZCKZOPZXBWTOPZWMWRWIWTWKXBOWRWHWSCWRWHWGDNZBJWSWGDBUFWRXEWGBWRWGDMZX
        EWGQWQXFAWGDUGUHZWGDUIUJUKULUMWRWJXACWRWJWGDJZXAUPZXAWGDBUQWRXISXAUPZXA
        WRXHSXAWRXFXHSQXGWGDUNUJUOXASUPXJXAXASURXAUSUTVAULUMVBWRWTTLXBTLXCXDQWR
        VHVCVDPZTWTVHVCVEZWRWOXKWSCAWOXKCVFWQGVGZWRWGBDAWQVQZVIVJVKWRXKTXBXLWRW
        OXKXACXMWRWGBDXNVLVJVKWTXBVMVNAXDWMQZIWOABDMZXOIWOUCZABWELXPXQRHABICDEF
        GVOVRVPVSVTWAWBAWDICDEFGVOWC $.

      $d A a b f $.  $d B a b e f $.  $d M a b f $.  $d O a b f $.
      $d a b f ph $.
      inelcarsg.1 $e |- ( ( ph /\ a e. ~P O /\ b e. ~P O )
          -> ( M ` ( a u. b ) ) <_ ( ( M ` a ) +e ( M ` b ) ) ) $.
      inelcarsg.2 $e |- ( ph -> B e. ( toCaraSiga ` M ) ) $.
      $( The Caratheodory measurable sets are closed under intersection.
         (Contributed by Thierry Arnoux, 18-May-2020.) $)
      inelcarsg $p |- ( ph -> ( A i^i B ) e. ( toCaraSiga ` M ) ) $=
        ( cfv wcel cxad co wceq cle cxr ve cin ccarsg wss cdif cpw wral elcarsg
        vf cv wa mpbid simpld ssinss1 syl wbr cpnf cicc iccssxr wf adantr simpr
        cc0 elpwdifcl ffvelcdmd sselid xaddcld cun indifundif fveq2i ralrimivva
        elpwincl1 3expb uneq1 fveq2d fveq2 oveq1d breq12d uneq2 oveq2d syl21anc
        rspc2v imp eqbrtrrid xleadd2a syl31anc simprd wb difeq1 oveq12d eqeq12d
        ineq1 adantl rspcdv mpd xrge0addass syl3anc inass oveq1i eqtrdi 3eqtr3d
        r19.21bi breqtrd inundif ffvelcdmda xrletri3 syl2anc mpbird ralrimiva
        jca ) ABCUBZDUCNZOXKEUDZUAUJZXKUBZDNZXNXKUEZDNZPQZXNDNZRZUAEUFZUGZUKAXM
        YCABEUDZXMAYDXNBUBZDNZXNBUEZDNZPQZXTRZUAYBUGZABXLOYDYKUKKABUADEFIJUHULZ
        UMBCEUNUOAYAUAYBAXNYBOZUKZYAXSXTSUPZXTXSSUPZUKZYNYOYPYNXSXPYECUEZDNZYHP
        QZPQZXTSYNXRTOYTTOXPTOXRYTSUPXSUUASUPYNVCUQURQZTXRVCUQUSZYNYBUUBXQDAYBU
        UBDUTYMJVAZYNXNXKEAYMVBZVDZVEVFZYNYSYHYNUUBTYSUUCYNYBUUBYRDUUDYNYECEYNX
        NBEUUEVLZVDZVEZVFYNUUBTYHUUCYNYBUUBYGDUUDYNXNBEUUEVDZVEZVFVGYNUUBTXPUUC
        YNYBUUBXODUUDYNXNXKEUUEVLZVEVFZYNXRYRYGVHZDNZYTSUUOXQDXNBCVIVJYNYRYBOZY
        GYBOZGUJZHUJZVHZDNZUUSDNZUUTDNZPQZSUPZHYBUGGYBUGZUUPYTSUPZUUIUUKAUVGYMA
        UVFGHYBYBAUUSYBOUUTYBOUVFLVMVKVAZUUQUURUKUVGUVHUVFUVHYRUUTVHZDNZYSUVDPQ
        ZSUPGHYRYGYBYBUUSYRRZUVBUVKUVEUVLSUVMUVAUVJDUUSYRUUTVNVOUVMUVCYSUVDPUUS
        YRDVPVQVRUUTYGRZUVKUUPUVLYTSUVNUVJUUODUUTYGYRVSVOUVNUVDYHYSPUUTYGDVPVTV
        RWBWCWAWDXRYTXPWEWFYNYECUBZDNZYSPQZYHPQZYIUUAXTYNUVQYFYHPYNUIUJZCUBZDNZ
        UVSCUEZDNZPQZUVSDNZRZUIYBUGZUVQYFRZAUWGYMACEUDZUWGACXLOUWIUWGUKMACUIDEF
        IJUHULWGVAYNUWFUWHUIYEYBUUHUVSYERZUWFUWHWHYNUWJUWDUVQUWEYFUWJUWAUVPUWCY
        SPUWJUVTUVODUVSYECWLVOUWJUWBYRDUVSYECWIVOWJUVSYEDVPWKWMWNWOVQYNUVRUVPYT
        PQZUUAYNUVPUUBOYSUUBOYHUUBOUVRUWKRYNYBUUBUVODUUDYNYECEUUHVLVEUUJUULUVPY
        SYHWPWQUVPXPYTPUVOXODXNBCWRVJWSWTAYJUAYBAYDYKYLWGXBXAXCYNXTXOXQVHZDNZXS
        SUWLXNDXNXKXDVJYNXOYBOZXQYBOZUVGUWMXSSUPZUUMUUFUVIUWNUWOUKUVGUWPUVFUWPX
        OUUTVHZDNZXPUVDPQZSUPGHXOXQYBYBUUSXORZUVBUWRUVEUWSSUWTUVAUWQDUUSXOUUTVN
        VOUWTUVCXPUVDPUUSXODVPVQVRUUTXQRZUWRUWMUWSXSSUXAUWQUWLDUUTXQXOVSVOUXAUV
        DXRXPPUUTXQDVPVTVRWBWCWAWDXJYNXSTOXTTOYAYQWHYNXPXRUUNUUGVGYNUUBTXTUUCAY
        BUUBXNDJXEVFXSXTXFXGXHXIXJAXKUADEFIJUHXH $.

      $( The Caratheodory-measurable sets are closed under pairwise unions.
         (Contributed by Thierry Arnoux, 21-May-2020.) $)
      unelcarsg $p |- ( ph -> ( A u. B ) e. ( toCaraSiga ` M ) ) $=
        ( cdif cun wss wceq elcarsgss dfss4 difelcarsg ccarsg cfv sylib uneq12d
        cin difindi inelcarsg eqeltrrid eqeltrrd ) AEEBNZNZEECNZNZOZBCODUAUBZAU
        KBUMCABEPUKBQABDEFIJKRBESUCACEPUMCQACDEFIJMRCESUCUDAUNEUJULUEZNUOEUJULU
        FAUPDEFIJAUJULDEFGHIJABDEFIJKTLACDEFIJMTUGTUHUI $.

      $( The Caratheodory-measurable sets are closed under class difference.
         (Contributed by Thierry Arnoux, 30-May-2020.) $)
      difelcarsg2 $p |- ( ph -> ( A \ B ) e. ( toCaraSiga ` M ) ) $=
        ( cdif cin ccarsg cfv wss wceq elcarsgss difin2 syl difelcarsg eqeltrd
        inelcarsg ) ABCNZECNZBOZDPQABERUFUHSABDEFIJKTBCEUAUBAUGBDEFGHIJACDEFIJM
        UCLKUEUD $.
    $}

    ${
      $d A x y $.  $d B y $.  $d M x y $.  $d O x y $.  $d ph x y $.
      carsgmon.1 $e |- ( ph -> A C_ B ) $.
      carsgmon.2 $e |- ( ph -> B e. ~P O ) $.
      carsgmon.3 $e |- ( ( ph /\ x C_ y /\ y e. ~P O )
        -> ( M ` x ) <_ ( M ` y ) ) $.
      $( Utility lemma:  Apply monotony.  (Contributed by Thierry Arnoux,
         29-May-2020.) $)
      carsgmon $p |- ( ph -> ( M ` A ) <_ ( M ` B ) ) $=
        ( wcel wss cfv cle wbr w3a wi cvv cpw ssexd id wa cv wceq sseq1 3anbi2d
        fveq2 breq1d imbi12d sseq2 eleq1 3anbi23d breq2d vtocl2g imp syl23anc )
        ADUANZEGUBZNZADEOZVBDFPZEFPZQRZADEVALKUCLAUDKLUTVBUEAVCVBSZVFABUFZCUFZO
        ZVIVANZSZVHFPZVIFPZQRZTADVIOZVKSZVDVNQRZTVGVFTBCDEUAVAVHDUGZVLVQVOVRVSV
        JVPAVKVHDVIUHUIVSVMVDVNQVHDFUJUKULVIEUGZVQVGVRVFVTVPVCVKVBAVIEDUMVIEVAU
        NUOVTVNVEVDQVIEFUJUPULMUQURUS $.
    $}

    $d A a b e f x y $.  $d E a b e x y $.  $d M a b e f x y $.
    $d O e f x y $.  $d a b e f x y ph $.
    carsgsiga.1 $e |- ( ph -> ( M ` (/) ) = 0 ) $.
    carsgsiga.2 $e |- ( ( ph /\ x ~<_ _om /\ x C_ ~P O )
      -> ( M ` U. x ) <_ sum* y e. x ( M ` y ) ) $.
    $( Lemma for the following theorems.  (Contributed by Thierry Arnoux,
       23-May-2020.) $)
    carsgsigalem $p |- ( ( ph /\ e e. ~P O /\ f e. ~P O )
      -> ( M ` ( e u. f ) ) <_ ( ( M ` e ) +e ( M ` f ) ) ) $=
      ( wcel cfv cle wbr wceq wa fveq2d adantr cv cpw w3a cun cxad simpr uneq2d
      co unidm eqtr3di cxr cc0 cpnf iccssxr wf simp1 syl simp2 ffvelcdmd sselid
      cicc eqeltrrd elxrge0 simprbi xraddge02 imp syl21anc eqbrtrd wne cpr cuni
      simp3 cesum uniprg 3adant1 com cdom wss prct prssi wi prex breq1 3anbi23d
      sseq1 unieq esumeq1 breq12d imbi12d vtoclg ax-mp syl3anc eqbrtrrd adantlr
      cvv esumpr breqtrd pm2.61dane ) ADUAZGUBZMZEUAZWTMZUCZWSXBUDZFNZWSFNZXBFN
      ZUEUHZOPWSXBXDWSXBQZRZXFXGXIOXKXEWSFXKWSWSUDXEWSXKWSXBWSXDXJUFZUGWSUIUJSX
      KXGUKMZXHUKMZULXHOPZXGXIOPZXDXMXJXDULUMVAUHZUKXGULUMUNXDWTXQWSFXDAWTXQFUO
      AXAXCUPZJUQZAXAXCURZUSZUTTZXKXGXHUKXKWSXBFXLSYBVBXKXHXQMZXOXDYCXJXDWTXQXB
      FXSAXAXCVLZUSZTYCXNXOXHVCVDUQXMXNRXOXPXGXHVEVFVGVHXDWSXBVIZRZXFWSXBVJZCUA
      ZFNZCVMZXIOXDXFYKOPYFXDYHVKZFNZXFYKOXAXCYMXFQAXAXCRYLXEFWSXBWTWTVNSVOXDAY
      HVPVQPZYHWTVRZYMYKOPZXRXAXCYNAWSXBWTWTVSVOXAXCYOAWSXBWTVTVOYHWOMAYNYOUCZY
      PWAZWSXBWBABUAZVPVQPZYSWTVRZUCZYSVKZFNZYSYJCVMZOPZWAYRBYHWOYSYHQZUUBYQUUF
      YPUUGYTYNUUAYOAYSYHVPVQWCYSYHWTWEWDUUGUUDYMUUEYKOUUGUUCYLFYSYHWFSYSYHYJCW
      GWHWILWJWKWLWMTYGWSXBYJXGCXHWTWTXDYIWSQZYJXGQYFXDUUHRYIWSFXDUUHUFSWNXDYIX
      BQZYJXHQYFXDUUIRYIXBFXDUUIUFSWNXDXAYFXTTXDXCYFYDTXDXGXQMYFYATXDYCYFYETXDY
      FUFWPWQWR $.

    ${
      fiunelcarsg.1 $e |- ( ph -> A e. Fin ) $.
      fiunelcarsg.2 $e |- ( ph -> A C_ ( toCaraSiga ` M ) ) $.
      $( The Caratheodory measurable sets are closed under finite union.
         (Contributed by Thierry Arnoux, 23-May-2020.) $)
      fiunelcarsg $p |- ( ph -> U. A e. ( toCaraSiga ` M ) ) $=
        ( cv cuni cfv wcel c0 cun wceq va vb ve ccarsg unieq eqidd eleq12d cdif
        vf csn uni0 difid eqtr4i baselcarsg difelcarsg eqeltrid wa uniun unisnv
        wss uneq2i eqtri ad2antrr cpw cc0 cpnf cicc co wf simpr cxad cle simpll
        wbr carsgsigalem syl3an1 simplrr eldifad sseldd unelcarsg ex findcard2d
        ) AUANZOZEUDPZQROZWEQUBNZOZWEQZWGBNZUJZSZOZWEQZDOZWEQUAUBBDWCRTZWDWFWEW
        EWCRUEWPWEUFUGWCWGTZWDWHWEWEWCWGUEWQWEUFUGWCWLTZWDWMWEWEWCWLUEWRWEUFUGW
        CDTZWDWOWEWEWCDUEWSWEUFUGAWFFFUHZWEWFRWTUKFULUMAFEFGHIAEFGHIJUNUOUPAWGD
        UTZWJDWGUHQZUQZUQZWIWNXDWIUQZWMWHWJSZWEWMWHWKOZSXFWGWKURXGWJWHBUSVAVBXE
        WHWJEFGUCUIAFGQXCWIHVCAFVDZVEVFVGVHEVIXCWIIVCXDWIVJXEAUCNZXHQUINZXHQXIX
        JSEPXIEPXJEPVKVHVLVNAXCWIVMABCUCUIEFGHIJKVOVPXEDWEWJADWEUTXCWIMVCXEWJDW
        GAXAXBWIVQVRVSVTUPWALWB $.

      ${
        carsgclctunlem1.1 $e |- ( ph -> Disj_ y e. A y ) $.
        carsgclctunlem1.2 $e |- ( ph -> E e. ~P O ) $.
        $( Lemma for ~ carsgclctun .  (Contributed by Thierry Arnoux,
           23-May-2020.) $)
        carsgclctunlem1 $p |- ( ph
          -> ( M ` ( E i^i U. A ) ) = sum* y e. A ( M ` ( E i^i y ) ) ) $=
          ( cin cfv wceq c0 va vb ve cv cuni cesum csn cun unieq ineq2d esumeq1
          fveq2d eqeq12d cc0 uni0 ineq2i eqtri fveq2i esumnul 3eqtr4g cdif wcel
          in0 wss wa cxad co simpr eqcomd simprr cpw cpnf cicc adantr elpwincl1
          wf ffvelcdmd esumsn oveq12d nfv nfcv cvv vex a1i vsnex eldifbd disjsn
          sylibr ad2antrr esumsplit uniun unisnv uneq2i inass indir inidm incom
          wn wdisj adantrr disjuniel eqtr3id uneq12d eqtrdi eqtrid indif2 uncom
          un0 difeq1i difun2 disj3 biimpi eqtr4id syl wral ccarsg cdom 3adant1r
          com wbr cle cfn ssfi sylan sstrd fiunelcarsg wb elcarsg simprd ineq1d
          mpbid difeq1d rspcdv mpd eqtr3d 3eqtr4rd ex findcard2d ) AEUAUDZUEZQZ
          FRZYSECUDZQZFRZCUFZSETUEZQZFRZTUUECUFZSEUBUDZUEZQZFRZUUKUUECUFZSZEUUK
          BUDZUGZUHZUEZQZFRZUUSUUECUFZSZEDUEZQZFRZDUUECUFZSUAUBBDYSTSZUUBUUIUUF
          UUJUVIUUAUUHFUVIYTUUGEYSTUIUJULYSTUUECUKUMYSUUKSZUUBUUNUUFUUOUVJUUAUU
          MFUVJYTUULEYSUUKUIUJULYSUUKUUECUKUMYSUUSSZUUBUVBUUFUVCUVKUUAUVAFUVKYT
          UUTEYSUUSUIUJULYSUUSUUECUKUMYSDSZUUBUVGUUFUVHUVLUUAUVFFUVLYTUVEEYSDUI
          UJULYSDUUECUKUMATFRZUNUUIUUJKUUHTFUUHETQTUUGTEUOUPEVCUQURCUUEUSUTAUUK
          DVDZUUQDUUKVAZVBZVEZVEZUUPUVDUVRUUPVEZUUOUURUUECUFZVFVGZUUNEUUQQZFRZV
          FVGZUVCUVBUVSUUOUUNUVTUWCVFUVSUUNUUOUVRUUPVHVIUVRUVTUWCSUUPUVRUUEUWCC
          UUQUVOUVRUUCUUQSZVEZUUDUWBFUWFUUCUUQEUVRUWEVHUJULAUVNUVPVJZUVRGVKZUNV
          LVMVGZUWBFAUWHUWIFVPZUVQJVNUVREUUQGAEUWHVBZUVQPVNZVOVQVRVNVSUVRUVCUWA
          SUUPUVRUUKUURUUECUVRCVTCUUKWACUURWAUUKWBVBUVRUBWCWDUURWBVBUVRBWEWDUVR
          UUQUUKVBWRUUKUURQTSUVRUUQDUUKUWGWFUUKUUQWGWHUVRUUCUUKVBZVEZUWHUWIUUDF
          AUWJUVQUWMJWIUWNEUUCGAUWKUVQUWMPWIVOVQUVRUUCUURVBZVEZUWHUWIUUDFAUWJUV
          QUWOJWIUWPEUUCGAUWKUVQUWOPWIVOVQWJVNUVSUVBEUULUUQUHZQZFRZUWDUVAUWRFUU
          TUWQEUUTUULUURUEZUHUWQUUKUURWKUWTUUQUULBWLWMUQUPURUVRUWDUWSSUUPUVRUWR
          UULQZFRZUWRUULVAZFRZVFVGZUWDUWSUVRUXBUUNUXDUWCVFUVRUXAUUMFUVRUXAEUWQU
          ULQZQUUMEUWQUULWNUVRUXFUULEUVRUXFUULUULQZUUQUULQZUHZUULUULUUQUULWOUVR
          UXIUULTUHUULUVRUXGUULUXHTUXGUULSUVRUULWPWDUVRUXHUULUUQQTUULUUQWQUVRCD
          UUKUUQACDUUCWSUVQOVNAUVNUVNUVPAUVNVHZWTUWGXAXBZXCUULXHXDXEUJXEULUVRUX
          CUWBFUVRUXCEUWQUULVAZQUWBEUWQUULXFUVRUXLUUQEUVRUXHTSZUXLUUQSUXKUXMUXL
          UUQUULUHZUULVAZUUQUWQUXNUULUULUUQXGXIUXMUXOUUQUULVAZUUQUUQUULXJUXMUUQ
          UXPSUUQUULXKXLXMXEXNUJXBULVSUVRUCUDZUULQZFRZUXQUULVAZFRZVFVGZUXQFRZSZ
          UCUWHXOZUXEUWSSZAUVNUYEUVPAUVNVEZUULGVDZUYEUYGUULFXPRZVBZUYHUYEVEZUYG
          BCUUKFGHAGHVBUVNIVNAUWJUVNJVNAUVMUNSUVNKVNAUUQXSXQXTUUQUWHVDUUQUEFRUU
          QUUCFRCUFYAXTUVNLXRADYBVBUVNUUKYBVBMDUUKYCYDUYGUUKDUYIUXJADUYIVDUVNNV
          NYEYFAUYJUYKYGUVNAUULUCFGHIJYHVNYKYIWTUVRUYDUYFUCUWRUWHUVREUWQGUWLVOU
          VRUXQUWRSZVEZUYBUXEUYCUWSUYMUXSUXBUYAUXDVFUYMUXRUXAFUYMUXQUWRUULUVRUY
          LVHZYJULUYMUXTUXCFUYMUXQUWRUULUYNYLULVSUYMUXQUWRFUYNULUMYMYNYOVNXMYPY
          QMYR $.
      $}
    $}

    ${
      $d A f k n z $.  $d M f k n z $.  $d O f k z $.  $d k n x y z ph $.
      carsggect.0 $e |- ( ph -> -. (/) e. A ) $.
      carsggect.1 $e |- ( ph -> A ~<_ _om ) $.
      carsggect.2 $e |- ( ph -> A C_ ( toCaraSiga ` M ) ) $.
      carsggect.3 $e |- ( ph -> Disj_ y e. A y ) $.
      carsggect.4 $e |- ( ( ph /\ x C_ y /\ y e. ~P O )
        -> ( M ` x ) <_ ( M ` y ) ) $.
      $( The outer measure is countably superadditive on Caratheodory
         measurable sets.  (Contributed by Thierry Arnoux, 31-May-2020.) $)
      carsggect $p |- ( ph -> sum* z e. A ( M ` z ) <_ ( M ` U. A ) ) $=
        ( cn wcel adantr vf vk vn c0 csn cun cv wf crn wss ccnv cres wfun cesum
        w3a cfv cuni cle wbr com cdom cvv wn wex 0ex a1i padct syl3anc cmpt nfv
        wa simpr1 feqmptd rneqd esumeq1d wceq ccarsg fvex cpw cc0 cpnf 0elcarsg
        cicc co snssd unssd ssexd carsgcl sstrd 0elpw sselda ffvelcdmd esummono
        frnd syl elsni adantl fveq2d eqtrd esumpad breqtrd ssexg sylancl simpr2
        ctex jca cxr iccssxr wral ralrimiva nfcv esumcl syl2anc sselid xrletri3
        wb mpbird fveq2 nnex simpr ad2antrr cima cdif wdisj cnvimass esumrnmpt2
        sseldd 3syl cin 3adant1r wfn mpan2 ax-mp disjss1 sseqtrdi sseqin2 sylib
        c1 cfn eqbrtrrd fssdm ffun difpreima fimacnv difeq1d uncom difun2 difss
        difeq1i eqtr3i eqsstri sspreima eqsstrrd fvimacnvi wf1o fresf1o disjrdx
        simpr3 fvres disjeq2dv bitr3d mpbid disjss3 biimpa syl21anc ciun uniiun
        3eqtr3rd elpwiuncl eqeltrid cfz cbvesum breqtrdi fz1ssnn fzfi fnfi rnfi
        ffn fnssres resss rnss cbvdisj disjun0 sylbi sylc pwidg carsgclctunlem1
        id unissd uniun unisn uneq2i 3eqtri uniss unipw elpwid esumeq2d reseq1d
        resmpt eqtrdi eqcomd adantlr syldan ad3antrrr 3eqtr2d carsgmon esumgect
        un0 wi 3eqtr3d exlimddv ) AREUDUEZUFZUAUGZUHZEUXNUIZUJZUXNUKZEULUMZUOZE
        DUGZFUPZDUNZEUQZFUPZURUSUAAEUTVAUSZUDVBSZUDESVCUXTUAVDNUYGAVEVFMEUAVBUD
        VGVHAUXTVKZRUBUGZUXNUPZFUPZUBUNZUYCUYEURUYHUXPUYBDUNZUBRUYJVIZUIZUYBDUN
        UYCUYLUYHUXPUYOUYBDUYHDVJZUYHUXNUYNUYHUBRUXMUXNAUXOUXQUXSVLZVMZVNVOUYHU
        YMUYCVPZUYMUYCURUSZUYCUYMURUSZVKZUYHUYTVUAUYHUYMUXMUYBDUNUYCURUYHUXPUYB
        UXMDVBUYPUYHUXMFVQUPZVBVUCVBSZUYHFVQVRZVFZUYHEUXLVUCAEVUCUJUXTOTUYHUDVU
        CUYHFGHAGHSZUXTITZAGVSZVTWAWCWDZFUHZUXTJTZAUDFUPZVTVPZUXTKTZWBWEZWFZWGU
        YHUYAUXMSZVKVUIVUJUYAFUYHVUKVURVULTUYHUXMVUIUYAUYHEUXLVUIAEVUIUJZUXTAEV
        UCVUIOAFGHIJWHWIZTZUYHUDVUIUDVUISZUYHGWJZVFWEWFZWKWLUYHRUXMUXNUYQWNZWMU
        YHEUXLUYBDVBVBAEVBSZUXTAUYFVVFNEXEWOZTZUYHUXLVUCVBVUFVUPWGUYHUYAESZVKVU
        IVUJUYAFUYHVUKVVIVULTUYHEVUIUYAVVAWKWLZUYHUYAUXLSZVKZUYBVUMVTVVLUYAUDFV
        VKUYAUDVPUYHUYAUDWPWQWRUYHVUNVVKVUOTWSWTXAUYHEUYBUXPDVBUYPUYHUXPVUCUJVU
        DUXPVBSZUYHUXPUXMVUCVVEVUQWIZVUEUXPVUCVBXBXCZUYHUYAUXPSZVKVUIVUJUYAFUYH
        VUKVVPVULTUYHUXPVUIUYAUYHUXPUXMVUIVVEVVDWIWKWLZAUXOUXQUXSXDZWMXFUYHUYMX
        GSUYCXGSUYSVUBXPUYHVUJXGUYMVTWAXHZUYHVVMUYBVUJSZDUXPXIUYMVUJSVVOUYHVVTD
        UXPVVQXJUXPUYBDVBDUXPXKXLXMXNUYHVUJXGUYCVVSUYHVVFVVTDEXIUYCVUJSVVHUYHVV
        TDEVVJXJEUYBDVBDEXKXLXMXNUYMUYCXOXMXQUYHDRUYJUYBUYKUBVBVUIUYAUYJFXRZRVB
        SUYHXSVFUYHUYIRSZVKZVUIVUJUYJFUYHVUKVWBVULTVWCUXMVUIUYJUYHUXMVUIUJVWBVV
        DTVWCRUXMUYIUXNUYHUXOVWBUYQTUYHVWBXTWLYGZWLZVWDVWCUYJUDVPZVKZUYKVUMVTVW
        GUYJUDFVWCVWFXTWRUYHVUNVWBVWFVUOYAWSUYHUXREYBZRUJZVWFUBRVWHYCZXIZUBVWHU
        YJYDZUBRUYJYDZUYHRUXMVWHUXNUXNEYEUYQUUAUYHVWFUBVWJUYHUYIVWJSZVKZUYJUXLS
        ZVWFVWOUXNUMZUYIUXRUXLYBZSVWPUYHVWQVWNUYHUXOVWQUYQRUXMUXNUUBZWOZTUYHVWJ
        VWRUYIUYHVWJUXRUXMEYCZYBZVWRUYHVXBUXRUXMYBZVWHYCZVWJUYHUXOVWQVXBVXDVPUY
        QVWSUXMEUXNUUCYHUYHVXCRVWHUYHUXOVXCRVPUYQRUXMUXNUUDWOUUEWSUYHVWQVXAUXLU
        JZVXBVWRUJVWTVXEUYHVXAUXLEYCZUXLUXLEUFZEYCVXAVXFVXGUXMEUXLEUUFUUIUXLEUU
        GUUJUXLEUUHUUKVFVXAUXLUXNUULXMUUMWKUYIUXLUXNUUNXMUYJUDWPWOXJUYHCECUGZYD
        ZVWLAVXIUXTPTUYHUBVWHUYIUXNVWHULZUPZYDVXIVWLUYHUBCVWHVXKEVXHVXJUYHVWQUX
        QUXSVWHEVXJUUOVWTVVRAUXOUXQUXSUUREUXNUUPVHUYHVXHVXKVPXTUUQUYHUBVWHVXKUY
        JUYIVWHSVXKUYJVPUYHUYIVWHUXNUUSWQUUTUVAUVBVWIVWKVKVWLVWMUBVWHRUYJUVCUVD
        UVEZYFUVHUYHUYKUYEUBUCUYHVUIVUJUYDFVULAUYDVUISUXTAUYDBEBUGZUVFVUIBEUVGA
        EVXMGBVBVVGAEVUIVXMVUTWKUVIUVJTZWLVWEUYHUCUGZRSZVKZUXNYRVXOUVKWDZULZUIZ
        UQZFUPZVXRUYKUBUNZUYEURVXQGVYAYIZFUPZVXTGUYAYIZFUPZDUNZVYBVYCUYHVYEVYHV
        PVXPUYHBDVXTGFGHVUHVULVUOUYHVXMUTVAUSZVXMVUIUJZUOVXMUQFUPZVXMVXHFUPZCUN
        ZVXMUYBDUNURAVYIVYJVYKVYMURUSUXTLYJVXMVYLUYBCDVXHUYAFXRDVXMXKCVXMXKDVYL
        XKCUYBXKUVLUVMUYHVXSVXRYKZVXSYSSZVXTYSSUYHUXOUXNRYKZVYNUYQRUXMUXNUVRVYP
        VXRRUJZVYNVXOUVNZRVXRUXNUVSYLYHVYNVXRYSSZVYOYRVXOUVOZVXRVXSUVPYLVXSUVQY
        HUYHVXTUXPVUCVXTUXPUJZUYHVXSUXNUJWUAUXNVXRUVTVXSUXNUWAYMVFZVVNWIUYHVXTU
        XMUJZDUXMUYAYDZDVXTUYAYDUYHVXTUXPUXMWUBVVEWIZAWUDUXTAVXIWUDPVXIDEUYAYDW
        UDCDEVXHUYADVXHXKCUYAXKVXHUYAVPUWHUWBDEUWCUWDWOTDVXTUXMUYAYNUWEUYHVUGGV
        UISVUHGHUWFWOUWGTVXQVYDVYAFVXQVYAGUJVYDVYAVPVXQVYAUYDGUYHVYAUYDUJVXPUYH
        VYAUXMUQZUYDUYHVXTUXMWUEUWIWUFUYDUXLUQZUFUYDUDUFUYDEUXLUWJWUGUDUYDUDVEU
        WKUWLUYDUXHUWMYOZTAUYDGUJZUXTVXPAVUSWUIVUTVUSUYDVUIUQGEVUIUWNGUWOYOWOYA
        WIVYAGYPYQWRVXQVYHVXTUYBDUNUBVXRUYJVIZUIZUYBDUNVYCVXQVXTVYGUYBDVXQDVJZV
        XQVYGUYBVPDVXTVXQUYAVXTSVKZVYFUYAFWUMUYAGUJVYFUYAVPWUMUYAGVXQVXTVUIUYAV
        XQVXTUXMVUIUYHWUCVXPWUETVXQEUXLVUIAVUSUXTVXPVUTYAVXQUDVUIVVBVXQVVCVFWEW
        FWIWKUWPUYAGYPYQWRXJUWQVXQWUKVXTUYBDWULVXQWUJVXSVXQVXSWUJVXQVXSUYNVXRUL
        ZWUJUYHVXSWUNVPVXPUYHUXNUYNVXRUYRUWRTVYQWUNWUJVPVYRUBRVXRUYJUWSYMUWTUXA
        VNVOVXQDVXRUYJUYBUYKUBYSVUIVWAVYSVXQVYTVFVXQUYIVXRSZVKZVUIVUJUYJFUYHVUK
        VXPWUOVULYAVXQWUOVWBUYJVUISZVXQVXRRUYIVYQVXQVYRVFWKUYHVWBWUQVXPVWDUXBUX
        CZWLWURWUPVWFVKZUYKVUMVTWUSUYJUDFWUPVWFXTWRUYHVUNVXPWUOVWFVUOUXDWSUYHUB
        VXRUYJYDZVXPUYHVWMWUTVXLVYQVWMWUTUXIVYRUBVXRRUYJYNYMWOTYFUXEUXJUYHVYBUY
        EURUSVXPUYHBCVYAUYDFGHVUHVULWUHVXNAVXMVXHUJVXHVUISVXMFUPVYLURUSUXTQYJUX
        FTYTUXGYTUXK $.
    $}

    carsgsiga.3 $e |- ( ( ph /\ x C_ y /\ y e. ~P O )
      -> ( M ` x ) <_ ( M ` y ) ) $.
    ${
      $d e k n x y $.  $d A n $.  $d E k n $.  $d M k n $.  $d O k $.
      $d ph k n $.
      carsgclctunlem2.1 $e |- ( ph -> Disj_ k e. NN A ) $.
      carsgclctunlem2.2 $e |- ( ( ph /\ k e. NN ) -> A e. ( toCaraSiga ` M ) )
        $.
      carsgclctunlem2.3 $e |- ( ph -> E e. ~P O ) $.
      carsgclctunlem2.4 $e |- ( ph -> ( M ` E ) =/= +oo ) $.
      $( Lemma for ~ carsgclctun .  (Contributed by Thierry Arnoux,
         25-May-2020.) $)
      carsgclctunlem2 $p |- ( ph -> ( ( M ` ( E i^i U_ k e. NN A ) )
        +e ( M ` ( E \ U_ k e. NN A ) ) ) <_ ( M ` E ) ) $=
        ( cn wcel vn ve ciun cin cfv cdif cxad co cle cxr wbr iunin2 fveq2i cc0
        cxne cpnf cicc iccssxr cpw cvv nnex cv wa elpwincl1 elpwiuncl ffvelcdmd
        a1i adantr sselid eqeltrrid elpwdifcl xnegcld xaddcld wral wf ralrimiva
        cesum nfcv esumcl syl2anc cmpt crn cuni wceq dfiun3g syl fveq2d com wss
        cdom nnct mptct rnct mp2b rnmptss w3a mptexg rnexg breq1 sseq1 3anbi23d
        wi unieq esumeq1 breq12d imbi12d vtoclg ax-mp mpd3an23 eqbrtrd fveq2 c0
        eqid simpr ad2antrr eqtrd wdisj wb incom rgenw disjeq2 sylib esumrnmpt2
        disjin breqtrd difssd carsgmon xrge0subcld c1 xrge0neqmnf adantl oveq2d
        cmnf wne 3adant1r cfn sylc 3eqtrd disjss1 syl31anc xnegeq eqtrdi eqtr3d
        cfz xnegneg xnegmnf ccarsg simpll fz1ssnn sselda fzfi mptfi fiunelcarsg
        rnfi eqeltrd elcarsg mpbid simprd ineq1 difeq1 oveq12d eqeq12d xaddpnf1
        rspcv 3eqtr3d neneqd pm2.65da neqned xaddass xnegid oveq1d ineq2d mptss
        syl222anc xaddrid disjrnmpt carsgclctunlem1 ineq2 elexi inss2 sseq2 ss0
        rnss mpbii 3eqtr3rd iunss1 mp1i sscond xleneg syl21anc xleadd2a xrletrd
        biimpa esumgect eqbrtrrid xleadd1a xrge0npcan syl3anc ) AFESDUCZUDZGUEZ
        FUWSUFZGUEZUGUHZFGUEZUXCUOZUGUHZUXCUGUHZUXEUIAUXAUJTUXGUJTUXCUJTZUXAUXG
        UIUKUXDUXHUIUKAUXAESFDUDZUCZGUEZUJUXKUWTGESFDULUMZAUNUPUQUHZUJUXLUNUPUR
        ZAHUSZUXNUXKGKASUXJHEUTSUTTZAVAVGZAEVBZSTZVCZFDHAFUXPTZUXTQVHVDZVEVFVIZ
        VJAUXEUXFAUXNUJUXEUXOAUXPUXNFGKQVFZVIZAUXCAUXNUJUXCUXOAUXPUXNUXBGKAFUWS
        HQVKVFZVIZVLVMZUYHAUXAUXLUXGUIUXMAUXLSUXJGUEZEVQZUXGUYDAUXNUJUYKUXOAUXQ
        UYJUXNTZESVNUYKUXNTUXRAUYLESUYAUXPUXNUXJGAUXPUXNGVOZUXTKVHUYCVFZVPSUYJE
        UTESVRVSVTVIUYIAUXLESUXJWAZWBZCVBZGUEZCVQZUYKUIAUXLUYPWCZGUEZUYSUIAUXKU
        YTGAUXJUXPTZESVNZUXKUYTWDAVUBESUYCVPZESUXJUXPWEWFWGAUYPWHWJUKZUYPUXPWIZ
        VUAUYSUIUKZVUEASWHWJUKUYOWHWJUKVUEWKESUXJWLUYOWMWNVGAVUCVUFVUDESUXJUXPU
        YOUYOXMWOWFUYPUTTZAVUEVUFWPZVUGXBZUXQUYOUTTVUHVAESUXJUTWQUYOUTWRWNABVBZ
        WHWJUKZVUKUXPWIZWPZVUKWCZGUEZVUKUYRCVQZUIUKZXBVUJBUYPUTVUKUYPWDZVUNVUIV
        URVUGVUSVULVUEVUMVUFAVUKUYPWHWJWSVUKUYPUXPWTXAVUSVUPVUAVUQUYSUIVUSVUOUY
        TGVUKUYPXCWGVUKUYPUYRCXDXEXFMXGXHXIXJACSUXJUYRUYJEUTUXPUYQUXJGXKUXRUYNU
        YCUYAUXJXLWDZVCZUYJXLGUEZUNVVAUXJXLGUYAVUTXNWGAVVBUNWDZUXTVUTLXOXPAESDF
        UDZXQZESUXJXQZAESDXQZVVEOEFSDYDWFVVDUXJWDZESVNVVEVVFXRVVHESDFXSXTESVVDU
        XJYAXHYBYCYEAUYJUXGEUAAUXEUXCUYEUYGABCUXBFGHIJKAFUWSYFQNYGZYHUYNAUAVBZS
        TZVCZYIVVJUUDUHZUYJEVQZUXEFEVVMDUCZUFZGUEZUOZUGUHZUXGUIVVLFVVOUDZGUEZVV
        QUGUHZVVRUGUHZVWAVVSVVNVVLVWCVWAVVQVVRUGUHZUGUHZVWAUNUGUHZVWAVVLVWAUJTZ
        VWAYMYNZVVQUJTZVVQYMYNZVVRUJTZVVRYMYNVWCVWEWDVVLUXNUJVWAUXOVVLUXPUXNVVT
        GAUYMVVKKVHZVVLFVVOHAUYBVVKQVHZVDVFZVIZVVLVWAUXNTVWHVWNVWAYJWFZVVLUXNUJ
        VVQUXOVVLUXPUXNVVPGVWLVVLFVVOHVWMVKZVFZVIZVVLVVQUXNTVWJVWRVVQYJWFVVLVVQ
        VWSVLZVVLVVRYMVVLVVRYMWDZUXEUPWDVVLVXAVCZVWBVWAUPUGUHZUXEUPVXBVVQUPVWAU
        GVXBVVRUOZVVQUPVVLVXDVVQWDZVXAVVLVWIVXEVWSVVQUUEWFVHVXBVXDYMUOZUPVXAVXD
        VXFWDVVLVVRYMUUAYKUUFUUBUUCYLVVLVWBUXEWDZVXAVVLUYBUBVBZVVOUDZGUEZVXHVVO
        UFZGUEZUGUHZVXHGUEZWDZUBUXPVNZVXGVWMVVLVVOHWIZVXPVVLVVOGUUGUEZTVXQVXPVC
        VVLVVOEVVMDWAZWBZWCZVXRVVLDVXRTZEVVMVNZVVOVYAWDVVLVYBEVVMVVLUXSVVMTZVCZ
        AUXTVYBAVVKVYDUUHZVVLVVMSUXSVVMSWIZVVLVVJUUIZVGZUUJZPVTZVPZEVVMDVXRWEWF
        ZVVLBCVXTGHIAHITVVKJVHZVWLAVVCVVKLVHZAVULVUMVURVVKMYOZVXTYPTZVVLVVMYPTV
        XSYPTVYQYIVVJUUKZEVVMDUULVXSUUNWNVGZVVLVYCVXTVXRWIVYLEVVMDVXRVXSVXSXMWO
        WFZUUMUUOVVLVVOUBGHIVYNVWLUUPUUQUURVXOVXGUBFUXPVXHFWDZVXMVWBVXNUXEWUAVX
        JVWAVXLVVQUGWUAVXIVVTGVXHFVVOUUSWGWUAVXKVVPGVXHFVVOUUTWGUVAVXHFGXKUVBUV
        DYQZVHVVLVXCUPWDZVXAVVLVWGVWHWUCVWOVWPVWAUVCVTVHUVEVXBUXEUPAUXEUPYNVVKV
        XARXOUVFUVGUVHVWAVVQVVRUVIUVNVVLVWDUNVWAUGVVLVWIVWDUNWDVWSVVQUVJWFYLVVL
        VWGVWFVWAWDVWOVWAUVOWFYRVVLVWBUXEVVRUGWUBUVKVVLVWAFVYAUDZGUEVXTFUYQUDZG
        UEZCVQVVNVVLVVTWUDGVVLVVOVYAFVYMUVLWGVVLBCVXTFGHIVYNVWLVYOVYPVYSVYTVVLV
        XTESDWAZWBZWIZCWUHUYQXQZCVXTUYQXQWUIVVLVYGVXSWUGWIWUIVYHEVVMSDUVMVXSWUG
        UWCWNVGAWUJVVKAVVGWUJOECSDUVPWFVHCVXTWUHUYQYSYQVWMUVQVVLCVVMDWUFUYJEUTV
        XRUYQDWDWUEUXJGUYQDFUVRWGVVMUTTVVLVVMYPVYRUVSVGVYEAUXTUYLVYFVYJUYNVTVYK
        VYEDXLWDZVCZUYJVVBUNWULUXJXLGWUKVUTVYEWUKUXJXLWIZVUTWUKUXJDWIWUMFDUVTDX
        LUXJUWAUWDUXJUWBWFYKWGVVLVVCVYDWUKVYOXOXPVVLVYGVVGEVVMDXQVYIAVVGVVKOVHE
        VVMSDYSYQYCYRUWEVVLVWKUXFUJTUXEUJTZVVRUXFUIUKZVVSUXGUIUKVWTVVLUXCVVLUXN
        UJUXCUXOAUXCUXNTZVVKUYGVHVIZVLAWUNVVKUYFVHVVLUXIVWIUXCVVQUIUKZWUOWUQVWS
        VVLBCUXBVVPGHIVYNVWLVVLVVOUWSFVYGVVOUWSWIVVLVYHEVVMSDUWFUWGUWHVWQAVUKUY
        QWIUYQUXPTVUKGUEUYRUIUKVVKNYOYGUXIVWIVCWURWUOUXCVVQUWIUWMUWJVVRUXFUXEUW
        KYTXJUWNUWLUWOUXAUXGUXCUWPYTAUXEUXNTWUPUXCUXEUIUKUXHUXEWDUYEUYGVVIUXEUX
        CUWQUWRYE $.
    $}

    $d f k n x y z $.  $d A e f g k n x y $.  $d E e f g k n x y $.
    $d M e f g k n x y $.  $d O e f g n x y $.  $d g k n ph x y $.
    ${
      carsgclctun.1 $e |- ( ph -> A ~<_ _om ) $.
      carsgclctun.2 $e |- ( ph -> A C_ ( toCaraSiga ` M ) ) $.
      ${
        carsgclctunlem3.1 $e |- ( ph -> E e. ~P O ) $.
        $( Lemma for ~ carsgclctun .  (Contributed by Thierry Arnoux,
           24-May-2020.) $)
        carsgclctunlem3 $p |- ( ph ->
           ( ( M ` ( E i^i U. A ) ) +e ( M ` ( E \ U. A ) ) ) <_ ( M ` E ) ) $=
          ( vk wcel c0 cn vf vn ve vg vz cuni cin cfv cdif cxad co cle wbr cpnf
          wceq wa cxr cc0 cicc iccssxr cpw elpwincl1 ffvelcdmd sselid elpwdifcl
          xaddcld adantr pnfge syl simpr breqtrrd wne clt wn uni0 eqtrdi ineq2d
          unieq in0 fveq2d difeq2d dif0 oveq12d adantl oveq1d xaddlid 3eqtrd wb
          eqeltrd xeqlelt syl2anc mpbid simpld adantlr wfo csdm cdom wex ccarsg
          cv wss cvv fvex ssex 0sdomg biimpar com nnenom ensymi domentr sylancl
          3syl cen ad2antrr fodomr cfzo ciun fveq2 iundisj crn wfn fofn fniunfv
          c1 forn unieqd eqtrd eqtr3id ad3antrrr wf cesum 3adant1r iundisj2 a1i
          wdisj sseldd wral ralrimiva cfn pm2.61dane ad2antlr carsgsigalem wrex
          ad4antr fof cab ad3antlr fzossnn sselda dfiun2g cmpt eqid rnmpt fzofi
          mptfi rnfi eqeltrri rnmptss eqsstrrid fiunelcarsg difelcarsg2 simpllr
          mp2b carsgclctunlem2 eqbrtrrd exlimddv ) AEDUFZUGZFUHZEUVGUIZFUHZUJUK
          ZEFUHZULUMZUVMUNAUVMUNUOZUPZUVLUNUVMULUVPUVLUQRZUVLUNULUMAUVQUVOAUVIU
          VKAURUNUSUKZUQUVIURUNUTZAGVAZUVRUVHFJAEUVGGPVBVCVDAUVRUQUVKUVSAUVTUVR
          UVJFJAEUVGGPVEVCVDVFVGUVLVHVIAUVOVJVKAUVMUNVLZUPZUVNDSADSUOZUVNUWAAUW
          CUPZUVNUVLUVMVMUMVNZUWDUVLUVMUOZUVNUWEUPZUWDUVLSFUHZUVMUJUKZURUVMUJUK
          ZUVMUWCUVLUWIUOAUWCUVIUWHUVKUVMUJUWCUVHSFUWCUVHESUGSUWCUVGSEUWCUVGSUF
          SDSVRVOVPZVQEVSVPVTUWCUVJEFUWCUVJESUIEUWCUVGSEUWKWAEWBVPVTWCWDUWDUWHU
          RUVMUJAUWHURUOZUWCKVGWEUWDUVMUQRZUWJUVMUOAUWMUWCAUVRUQUVMUVSAUVTUVREF
          JPVCVDVGZUVMWFVIWGZUWDUVQUWMUWFUWGWHUWDUVLUVMUQUWOUWNWIUWNUVLUVMWJWKW
          LWMWNUWBDSVLZUPZTDUAWTZWOZUVNUAUWQSDWPUMZDTWQUMZUWSUAWRAUWPUWTUWAAUWT
          UWPADFWSUHZXAZDXBRUWTUWPWHODUXBFWSXCXDDXBXEXLXFWNAUXAUWAUWPADXGWQUMXG
          TXMUMUXANTXGXHXIDXGTXJXKXNTDUAXOWKUWQUWSUPZEUBTUBWTZUWRUHZQYDUXEXPUKZ
          QWTZUWRUHZXQZUIZXQZUGZFUHZEUXLUIZFUHZUJUKUVLUVMULUXDUXNUVIUXPUVKUJUXD
          UXMUVHFUXDUXLUVGEUXDUXLUBTUXFXQZUVGUXFUXIQUBUXEUXHUWRXRZXSUWSUXQUVGUO
          UWQUWSUXQUWRXTZUFZUVGUWSUWRTYAUXQUXTUOTDUWRYBUBTUWRYCVIUWSUXSDTDUWRYE
          YFYGWDYHZVQVTUXDUXOUVJFUXDUXLUVGEUYAWAVTWCUXDBCUXKUBEFGHAGHRZUWAUWPUW
          SIYIZAUVTUVRFYJZUWAUWPUWSJYIZAUWLUWAUWPUWSKYIZUWQBWTZXGWQUMZUYGUVTXAZ
          UYGUFFUHUYGCWTZFUHZCYKULUMZUWSUWBUYHUYIUYLUWPAUYHUYIUYLUWALYLYLYLZUWQ
          UYGUYJXAZUYJUVTRZUYGFUHUYKULUMZUWSUWBUYNUYOUYPUWPAUYNUYOUYPUWAMYLYLYL
          UBTUXKYOUXDUXFUXIQUBUXRYMYNUXDUXETRZUPZUXFUXJFGHUCUDUXDUYBUYQUYCVGZUX
          DUYDUYQUYEVGZUYRDUXBUXFAUXCUWAUWPUWSUYQOUUDZUYRTDUXEUWRUWSTDUWRYJZUWQ
          UYQTDUWRUUEZUUAUXDUYQVJVCYPUYRBCUCUDFGHUYSUYTUXDUWLUYQUYFVGZUXDUYHUYI
          UYLUYQUYMYLZUUBUYRUXJUEWTUXIUOQUXGUUCUEUUFZUFZUXBUYRUXIDRZQUXGYQUXJVU
          GUOUYRVUHQUXGUYRUXHUXGRZUPZTDUXHUWRUWSVUBUWQUYQVUIVUCUUGUYRUXGTUXHUXG
          TXAUYRUXEUUHYNUUIVCZYRQUEUXGUXIDUUJVIUYRBCVUFFGHUYSUYTVUDVUEVUFYSRUYR
          QUXGUXIUUKZXTZVUFYSQUEUXGUXIVULVULUULZUUMZUXGYSRVULYSRVUMYSRYDUXEUUNQ
          UXGUXIUUOVULUUPUVCUUQYNUYRVUFVUMUXBVUOUYRUXIUXBRZQUXGYQVUMUXBXAUYRVUP
          QUXGVUJDUXBUXIUYRUXCVUIVUAVGVUKYPYRQUXGUXIUXBVULVUNUURVIUUSUUTWIUVAAE
          UVTRUWAUWPUWSPYIAUWAUWPUWSUVBUVDUVEUVFYTYT $.
      $}

      $( The Caratheodory measurable sets are closed under countable union.
         (Contributed by Thierry Arnoux, 21-May-2020.) $)
      carsgclctun $p |- ( ph -> U. A e. ( toCaraSiga ` M ) ) $=
        ( cfv wcel wceq cle wbr cvv ve cuni ccarsg wss cv cin cdif cxad co wral
        cpw unissd carsguni sseqtrd wa adantr cc0 cpnf cicc wf c0 cdom 3adant1r
        com cesum simpr carsgclctunlem3 cpr inex1g adantl difexg prct elpwincl1
        syl2anc elpwdifcl prssi w3a wi prex breq1 sseq1 3anbi23d fveq2d esumeq1
        unieq breq12d imbi12d vtoclg ax-mp mpd3an23 cun uniprg eqtrdi ffvelcdmd
        inundif ineq2 inidm inindif 3eqtr3g ad2antrr eqtrd orcd esumpr2 3brtr3d
        wo ex jca cxr iccssxr sselid xaddcld ffvelcdmda xrletri3 mpbird elcarsg
        wb ralrimiva mpbir2and ) ADUBZEUCOZPXSFUDUAUEZXSUFZEOZYAXSUGZEOZUHUIZYA
        EOZQZUAFUKZUJAXSXTUBFADXTNULAEFGHIJUMUNAYHUAYIAYAYIPZUOZYHYFYGRSZYGYFRS
        ZUOZYKYLYMYKBCDYAEFGAFGPYJHUPAYIUQURUSUIZEUTYJIUPZAVAEOZUQQZYJJUPABUEZV
        DVBSZYSYIUDZYSUBZEOZYSCUEZEOZCVEZRSZYJKVCAYSUUDUDUUDYIPYSEOUUERSYJLVCAD
        VDVBSYJMUPADXTUDYJNUPAYJVFZVGYKYBYDVHZUBZEOZUUIUUECVEZYGYFRYKUUIVDVBSZU
        UIYIUDZUUKUULRSZYKYBTPZYDTPZUUMYJUUPAYAXSYIVIVJYJUUQAYAXSYIVKVJYBYDTTVL
        VNYKYBYIPZYDYIPZUUNYKYAXSFUUHVMZYKYAXSFUUHVOZYBYDYIVPVNAUUMUUNUUOYJUUIT
        PAUUMUUNVQZUUOVRZYBYDVSAYTUUAVQZUUGVRUVCBUUITYSUUIQZUVDUVBUUGUUOUVEYTUU
        MUUAUUNAYSUUIVDVBVTYSUUIYIWAWBUVEUUCUUKUUFUULRUVEUUBUUJEYSUUIWEWCYSUUIU
        UECWDWFWGKWHWIVCWJYKUUJYAEYKUUJYBYDWKZYAYKUURUUSUUJUVFQUUTUVAYBYDYIYIWL
        VNYAXSWOWMWCYKYBYDUUEYCCYEYIYIYKUUDYBQZUOUUDYBEYKUVGVFWCYKUUDYDQZUOUUDY
        DEYKUVHVFWCUUTUVAYKYIYOYBEYPUUTWNZYKYIYOYDEYPUVAWNZYKYBYDQZYCUQQZYCURQZ
        XEYKUVKUOZUVLUVMUVNYCYQUQUVNYBVAEUVKYBVAQYKUVKYBYBUFYBYDUFYBVAYBYDYBWPY
        BWQYAXSWRWSVJWCAYRYJUVKJWTXAXBXFXCXDXGYKYFXHPYGXHPYHYNXPYKYCYEYKYOXHYCU
        QURXIZUVIXJYKYOXHYEUVOUVJXJXKYKYOXHYGUVOAYIYOYAEIXLXJYFYGXMVNXNXQAXSUAE
        FGHIXOXR $.
    $}

    $( The Caratheodory measurable sets constructed from outer measures form a
       Sigma-algebra.  Statement (iii) of Theorem 1.11.4 of [Bogachev] p. 42.
       (Contributed by Thierry Arnoux, 17-May-2020.) $)
    carsgsiga $p |- ( ph -> ( toCaraSiga ` M ) e. ( sigAlgebra ` O ) ) $=
      ( vg cfv wss wcel cv wbr wa ad2antrr 3adant1r cpw cdif wral com cdom cuni
      ccarsg wi w3a csiga carsgcl baselcarsg adantr cc0 cpnf cicc co difelcarsg
      wf simpr ralrimiva wceq cesum cle elpwi ad2antlr carsgclctun 3jca jca cvv
      c0 ex wb fvex issiga ax-mp sylibr ) ADUGMZEUAZNZEVROZELPZUBVROZLVRUCZWBUD
      UEQZWBUFVROZUHZLVRUAZUCZUIZRZVREUJMOZAVTWJADEFGHUKAWAWDWIADEFGHIULAWCLVRA
      WBVROZRWBDEFAEFOZWMGUMAVSUNUOUPUQDUSZWMHUMAWMUTURVAAWGLWHAWBWHOZRZWEWFWQW
      ERBCWBDEFAWNWPWEGSAWOWPWEHSAVKDMUNVBWPWEISWQBPZUDUEQZWRVSNZWRUFDMWRCPZDMZ
      CVCVDQZWEAWSWTXCWPJTTWQWRXANZXAVSOZWRDMXBVDQZWEAXDXEXFWPKTTWQWEUTWPWBVRNA
      WEWBVRVEVFVGVLVAVHVIVRVJOWLWKVMDUGVNLVREVOVPVQ $.
  $}

  ${
    $d M e f x y $.  $d Q f x y $.  $d R f y $.  $d V f y $.  $d S e f x y $.
    $d ph e f g x y $.
    omsmeas.m $e |- M = ( toOMeas ` R ) $.
    omsmeas.s $e |- S = ( toCaraSiga ` M ) $.
    omsmeas.o $e |- ( ph -> Q e. V ) $.
    omsmeas.r $e |- ( ph -> R : Q --> ( 0 [,] +oo ) ) $.
    omsmeas.d $e |- ( ph -> (/) e. dom R ) $.
    omsmeas.0 $e |- ( ph -> ( R ` (/) ) = 0 ) $.
    $( The restriction of a constructed outer measure to Caratheodory
       measurable sets is a measure.  This theorem allows to construct measures
       from pre-measures with the required characteristics, as for the Lebesgue
       measure.  (Contributed by Thierry Arnoux, 17-May-2020.) $)
    omsmeas $p |- ( ph -> ( M |` S ) e. ( measures ` S ) ) $=
      ( vf vy cfv wcel c0 wceq wbr cle ve vg vx cres cmeas cc0 cpnf cicc co com
      wf cv cdom wdisj wa cuni cesum wi cpw wral w3a cdm coms omsf syl2anc fdmd
      a1i eqcomd unieqd pweqd feq12d mpbird ccarsg cvv carsgcl eqsstrid fssresd
      uniexd oms0 0elcarsg eleqtrrdi fvres syl eqtrd id cbvdisj anbi2i ad2antrr
      nfcv ciun simplr elpwid wss sstrd sselda simprl omssubadd uniiun 3ad2ant1
      fveq2i simpl3 simpr simp2 eqbrtrid 3adant1r 3ad2ant3 ad2antlr carsgclctun
      sseldd elpwi omsmon sseqtrdi nfv ralrimiva esumeq2d 3brtr4d csn cdif snex
      eqtrdi adantr ffvelcdmd fveq2d sylan9eqr esumpad2 neldifsnd ssdomg mpisyl
      elsni difss domtr ssdifssd simprr sylib disjss1 mpsyl cxr wb sselid csiga
      carsggect eqbrtrrd unidif0 breqtrdi jca iccssxr xrletri3 sylan2b 3jca crn
      esumcl ex carsgsiga eqeltrid elrnsiga ismeas 3syl ) AEDUDZDUEOPZDUFUGUHUI
      ZUURUKZQUUROZUFRZUAULZUJUMSZMUVDMULZUNZUOZUVDUPZUUROZUVDUVFUUROZMUQZRZURZ
      UADUSZUTZVAZAUVAUVCUVPABUPZUSZUUTDEAUVSUUTEUKZCVBZUPZUSZUUTCVCOZUKZABFPZB
      UUTCUKZUWEIJBCFVDVEAUVSUWCUUTEUWDEUWDRAGVGAUVRUWBABUWAAUWABABUUTCJVFVHVIV
      JVKVLZADEVMOZUVSHAEUVRVNABFIVRZUWHVOVPZVQZAUVBQEOZUFAQDPUVBUWMRAQUWIDAEUV
      RVNUWJUWHABCEFGIJKLVSZVTHWAQDEWBWCUWNWDAUVNUAUVOAUVDUVOPZUOZUVHUVMUVHUWPU
      VEUBUVDUBULZUNZUOZUVMUVGUWRUVEMUBUVDUVFUWQUBUVFWIMUWQWIUVFUWQRWEWFWGUWPUW
      SUOZUVMUVJUVLTSZUVLUVJTSZUOZUWTUXAUXBUWTMUVDUVFWJZEOZUVDUVFEOZMUQZUVJUVLT
      UWTMUVFBCEFUVDGAUWFUWOUWSIWHAUWGUWOUWSJWHUWTUVFUVDPZUOZUVFUVRUWTUVDUVSUVF
      UWTUVDDUVSUWTUVDDAUWOUWSWKZWLADUVSWMUWOUWSUWKWHWNWOZWLUWPUVEUWRWPZWQUWTUV
      IDPZUVJUXERUWTUVIUWIDUWTUCNUVDEUVRVNAUVRVNPUWOUWSUWJWHZAUVTUWOUWSUWHWHZAU
      WMUFRUWOUWSUWNWHZUWPUCULZUJUMSZUXQUVSWMZUXQUPZEOZUXQNULZEOZNUQZTSZUWSAUXR
      UXSUYEUWOAUXRUXSVAZUYANUXQUYBWJZEOUYDTUXTUYGENUXQWRWTUYFNUYBBCEFUXQGAUXRU
      WFUXSIWSAUXRUWGUXSJWSUYFUYBUXQPZUOZUYBUVRUYIUXQUVSUYBAUXRUXSUYHXAUYFUYHXB
      XIWLAUXRUXSXCWQXDZXEXEZUWPUXQUYBWMZUYBUVSPZUXQEOUYCTSZUWSAUYLUYMUYNUWOAUY
      LUYMVAUXQUYBBCEFGAUYLUWFUYMIWSAUYLUWGUYMJWSAUYLUYMXCUYMAUYBUVRWMUYLUYBUVR
      XJXFXKZXEXEZUXLUWTUVDDUWIUWOUVDDWMAUWSUVDDXJXGZHXLZXHHWAZUXMUVJUVIEOZUXEU
      VIDEWBZUVIUXDEMUVDWRWTXTWCUWTUVDUVKUXFMUWTMXMUWTUVKUXFRZMUVDUXIUVFDPVUBUW
      TUVDDUVFUYQWOZUVFDEWBWCXNXOZXPUWTUXGUYTUVLUVJTUWTUXGUVDQXQZXRZUPZEOZUYTTU
      WTVUFUXFMUQUXGVUHTUWTUVDVUEUXFMUVOVNUXJVUEVNPUWTQXSVGUXIUVSUUTUVFEUWTUVTU
      XHUXOYAUXKYBUVFVUEPZUWTUXFUWMUFVUIUVFQEUVFQYIYCUXPYDYEUWTUCNMVUFEUVRVNUXN
      UXOUXPUYKUWTQUVDYFUWTVUFUVDUMSZUVEVUFUJUMSUWTUWOVUFUVDWMZVUJUXJUVDVUEYJZV
      UFUVDUVOYGYHUXLVUFUVDUJYKVEUWTUVDUWIVUEUYRYLVUKUWTNUVDUYBUNZNVUFUYBUNVULU
      WTUWRVUMUWPUVEUWRYMUBNUVDUWQUYBNUWQWIUBUYBWIUWQUYBRWEWFYNNVUFUVDUYBYOYPUY
      PUUAUUBVUGUVIEUVDUUCWTUUDVUDUWTUXMUVJUYTRUYSVUAWCXPUUEUWTUVJYQPUVLYQPUVMU
      XCYRUWTUUTYQUVJUFUGUUFZUWTDUUTUVIUURAUVAUWOUWSUWLWHZUYSYBYSUWTUUTYQUVLVUN
      UWTUWOUVKUUTPZMUVDUTUVLUUTPUXJUWTVUPMUVDUXIDUUTUVFUURUWTUVAUXHVUOYAVUCYBX
      NUVDUVKMUVOMUVDWIUUKVEYSUVJUVLUUGVEVLUUHUULXNUUIADUVRYTOZPDYTUUJUPPUUSUVQ
      YRADUWIVUQHAUCNEUVRVNUWJUWHUWNUYJUYOUUMUUNDUVRUUOUAMDUURUUPUUQVL $.
  $}

  ${
    $d P x y $.  $d R x y $.  $d ph x y $.
    caraext.1 $e |- ( ph -> P : R --> ( 0 [,] +oo ) ) $.
    caraext.2 $e |- ( ph -> ( P ` (/) ) = 0 ) $.
    caraext.3 $e |- ( ( ph /\ ( x ~<_ _om /\ x C_ R /\ Disj_ y e. x y ) )
      -> ( P ` U. x ) = sum* y e. x ( P ` y ) ) $.
    ${
      $d A x y $.  $d B x y $.
      pmeasmono.1 $e |- ( ph -> A e. R ) $.
      pmeasmono.2 $e |- ( ph -> B e. R ) $.
      pmeasmono.3 $e |- ( ph -> ( B \ A ) e. R ) $.
      pmeasmono.4 $e |- ( ph -> A C_ B ) $.
      $( This theorem's hypotheses define a pre-measure.  A pre-measure is
         monotone.  (Contributed by Thierry Arnoux, 19-Jul-2020.) $)
      pmeasmono $p |- ( ph -> ( P ` A ) <_ ( P ` B ) ) $=
        ( cfv wceq wa cc0 adantr wcel cle wbr cdif c0 wss eqimss ssdifeq0 sylib
        fveq2d adantl eqtrd cpnf cicc ffvelcdmd cxr elxrge0 simprbi syl eqbrtrd
        co wne cxad iccssxr wf sselid xrge0addge syl2anc cpr cuni cv cesum cdom
        com wdisj w3a prct prssi cin disjdif wb simpr id disjprg syl3anc mpbiri
        3jca cvv prex biidd breq1 sseq1 disjeq1 3anbi123d anbi12d unieq esumeq1
        wi eqeq12d imbi12d vtoclg ax-mp adantlr mpdan cun uniprg esumpr 3eqtr3d
        undif breqtrrd pm2.61dane ) ADFOZEFOZUAUBDEDUCZADXMPZQZXKRXLUAXOXKUDFOZ
        RXNXKXPPAXNDUDFXNDXMUEDUDPDXMUFDEUGUHUIUJAXPRPXNISUKARXLUAUBZXNAXLRULUM
        UTZTZXQAGXREFHLUNXSXLUOTXQXLUPUQURSUSADXMVAZQZXKXKXMFOZVBUTZXLUAYAXKUOT
        YBXRTXKYCUAUBYAXRUOXKRULVCYAGXRDFAGXRFVDXTHSZADGTZXTKSZUNZVEYAGXRXMFYDA
        XMGTZXTMSZUNZXKYBVFVGYADXMVHZVIZFOZYKCVJZFOZCVKZXLYCYAYKVMVLUBZYKGUEZCY
        KYNVNZVOZYMYPPZYAYQYRYSAYQXTAYEYHYQKMDXMGGVPVGSAYRXTAYEYHYRKMDXMGVQVGSY
        AYSDXMVRUDPZDEVSYAYEYHXTYSUUBVTYFYIAXTWAZCDXMYNDXMGYNDPZWBYNXMPZWBWCWDW
        EWFAYTUUAXTYKWGTAYTQZUUAWQZDXMWHABVJZVMVLUBZUUHGUEZCUUHYNVNZVOZQZUUHVIZ
        FOZUUHYOCVKZPZWQUUGBYKWGUUHYKPZUUMUUFUUQUUAUURAAUULYTUURAWIUURUUIYQUUJY
        RUUKYSUUHYKVMVLWJUUHYKGWKCUUHYKYNWLWMWNUURUUOYMUUPYPUURUUNYLFUUHYKWOUIU
        UHYKYOCWPWRWSJWTXAXBXCYAYLEFAYLEPXTAYLDXMXDZEAYEYHYLUUSPKMDXMGGXEVGADEU
        EUUSEPNDEXHUHUKSUIYADXMYOXKCYBGGYAUUDQYNDFYAUUDWAUIYAUUEQYNXMFYAUUEWAUI
        YFYIYGYJUUCXFXGXIXJ $.
    $}

    ${
      $d A k x y $.  $d B x y $.  $d P k x y $.  $d R k x y $.  $d ph k x y $.
      pmeassubadd.q $e |- Q = { s e. ~P ~P O | ( (/) e. s
        /\ A. x e. s A. y e. s ( ( x u. y ) e. s /\ ( x \ y ) e. s ) ) } $.
      pmeassubadd.1 $e |- ( ph -> R e. Q ) $.
      pmeassubadd.2 $e |- ( ph -> A ~<_ _om ) $.
      pmeassubadd.3 $e |- ( ( ph /\ k e. A ) -> B e. R ) $.
      ${
        pmeasadd.4 $e |- ( ph -> Disj_ k e. A B ) $.
        $( A premeasure on a ring of sets is additive on disjoint countable
           collections.  This is called sigma-additivity.  (Contributed by
           Thierry Arnoux, 19-Jul-2020.) $)
        pmeasadd $p |- ( ph -> ( P ` U_ k e. A B ) = sum* k e. A ( P ` B ) ) $=
          ( wceq ciun cfv cmpt cuni cv cesum wcel wral ralrimiva dfiun3g fveq2d
          crn syl com cdom wbr wss wdisj mptct rnct 3syl eqid rnmptss disjrnmpt
          w3a wa 3jca ancli cvv ctex mptexg rnexg breq1 sseq1 disjeq1 3anbi123d
          wi anbi2d unieq esumeq1 eqeq12d imbi12d vtoclg mpd fveq2 cpnf cicc co
          cc0 wf adantr ffvelcdmd c0 adantl ad2antrr eqtrd esumrnmpt2 3eqtrd )
          AIDEUAZFUBIDEUCZULZUDZFUBZXACUEZFUBZCUFZDEFUBZIUFAWSXBFAEHUGZIDUHZWSX
          BTAXHIDRUIZIDEHUJUMUKAAXAUNUOUPZXAHUQZCXAXDURZVEZVFZXCXFTZAXNAXKXLXMA
          DUNUOUPZWTUNUOUPXKQIDEUSWTUTVAAXIXLXJIDEHWTWTVBVCUMAIDEURXMSICDEVDUMV
          GVHAWTVIUGZXAVIUGXOXPVQZAXQDVIUGZXRQDVJZIDEVIVKVAWTVIVLABUEZUNUOUPZYB
          HUQZCYBXDURZVEZVFZYBUDZFUBZYBXECUFZTZVQXSBXAVIYBXATZYGXOYKXPYLYFXNAYL
          YCXKYDXLYEXMYBXAUNUOVMYBXAHVNCYBXAXDVOVPVRYLYIXCYJXFYLYHXBFYBXAVSUKYB
          XAXECVTWAWBNWCVAWDACDEXEXGIVIHXDEFWEAXQXTQYAUMAIUEDUGZVFZHWIWFWGWHZEF
          AHYOFWJYMLWKRWLRYNEWMTZVFXGWMFUBZWIYPXGYQTYNEWMFWEWNAYQWITYMYPMWOWPSW
          QWR $.
      $}

$(
      @{
        @d A k f i n x y @.  @d B f i n @.  @d O s @.  @d P f n @.
        @d R i n s x y @.  @d ph f i n @.
        @( A premeasure on a ring of sets is subadditive for collections of
           sets where overlaps are allowed.  (Contributed by Thierry Arnoux,
           19-Jul-2020.) @)
        pmeassubadd @p |- ( ph
          -> ( P ` U_ k e. A B ) <_ sum* k e. A ( P ` B ) ) @=
          ( vn wcel vf vi cv cdm cmpt crn wf1o cn wceq c1 chash cfv caddc co wo
          cfzo wa ciun cesum cle wbr com cdom wex rnct 3syl f1ocnt syl cc0 cpnf
          mptct cicc cxr iccssxr cdif cuni dff1o5 simprbi ad2antrl unieqd f1ofn
          wf1 wfn fniunfv wral ralrimiva dfiun3g 3eqtr4rd nfcv fveq2 iundisjcnt
          adantr simprr eqtrd fveq2d wf c0 wss w3a adantlr fz1nnct simplrl f1of
          wdisj eqid rnmptss ad2antrr fss syl2anc simpr ffvelcdmd eqimss
          fzossnn
          sseq1 mpbiri jaoi ad2antll simplrr fz1nntr fiunelros difelros syl3anc
          sselda iundisj2cnt pmeasadd cvv vex dmex a1i esumcl sselid ctex dfin4
          eqeltrd cin inelros eqeltrrid difssd pmeasmono esumle eqbrtrd xrletrd
          simprl esummonof1o exlimddv ) AUAUCZUDZIDEUEZUFZUUFUGZUUGUHUIZUUGUJUU
          IUKULUJUMUNZUPUNZUIZUOZUQZIDEURZFULZDEFULZIUSZUTVAUAAUUIVBVCVAZUUPUAV
          DADVBVCVAZUUHVBVCVAUVAQIDEVKUUHVEVFUUIUAVGVHAUUPUQZUURUUGSUCZUUFULZFU
          LZSUSZUUTUVCVIVJVLUNZVMUURVIVJVNZUVCUURUUGUVEUBUJUVDUPUNZUBUCZUUFULZU
          RZVOZFULZSUSZUVHUVCUURSUUGUVNURZFULUVPUVCUUQUVQFUVCUUQSUUGUVEURZUVQUV
          CUUFUFZVPZUUIVPZUVRUUQUVCUVSUUIUUJUVSUUIUIZAUUOUUJUUGUUIUUFWBUWBUUGUU
          IUUFVQVRVSVTUVCUUFUUGWCZUVRUVTUIUUJUWCAUUOUUGUUIUUFWAVSSUUGUUFWDVHAUU
          QUWAUIZUUPAEHTZIDWEZUWDAUWEIDRWFZIDEHWGVHWLWHUVCUVEUVLUBSUULUUGSUVLWI
          ZUVDUVKUUFWJZAUUJUUOWMZWKWNWOUVCBCUUGUVNFGHSJKAHUVHFWPZUUPLWLZAWQFULV
          IUIZUUPMWLABUCZVBVCVAUWNHWRCUWNCUCZXDWSZUWNVPFULUWNUWOFULCUSUIZUUPNWT
          ZOAHGTZUUPPWLZUVCUUOUUGVBVCVAUWJUUGUULXAVHUVCUVDUUGTZUQZUWSUVEHTZUVMH
          TZUVNHTZUVCUWSUXAUWTWLUXBUUGHUVDUUFUXBUUGUUIUUFWPZUUIHWRZUUGHUUFWPZUX
          BUUJUXFAUUJUUOUXAXBUUGUUIUUFXCVHAUXGUUPUXAAUWFUXGUWGIDEHUUHUUHXEXFVHX
          GUUGUUIHUUFXHXIZUVCUXAXJZXKZUXBBCUVLGHUBUVDJKOAUWSUUPUXAPXGZUVCUUGUHU
          VDUUOUUGUHWRZAUUJUUKUXMUUNUUGUHXLUUNUXMUUMUHWRUULXMUUGUUMUHXNXOXPXQYC
          UXBUVKUVJTZUQUUGHUVKUUFUXBUXHUXNUXIWLUXBUVJUUGUVKUXBUUOUXAUVJUUGWRAUU
          JUUOUXAXRUXJUUGUULUVDXSXIYCXKXTZBCUVEUVMGHJKOYAZYBUVCUVEUVLUBSUULUUGU
          WHUWIUWJYDYEWNZUVCUUGYFTZUVOUVHTZSUUGWEUVPUVHTUXRUVCUUFUAYGYHYIZUVCUX
          SSUUGUXBHUVHUVNFAUWKUUPUXALXGZUXBUWSUXCUXDUXEUXLUXKUXOUXPYBZXKZWFUUGU
          VOSYFSUUGWIZYJXIYNYKUVCUVHVMUVGUVIUVCUXRUVFUVHTZSUUGWEUVGUVHTUXTUVCUY
          ESUUGUXBHUVHUVEFUYAUXKXKZWFUUGUVFSYFUYDYJXIYKAUUTVMTUUPAUVHVMUUTUVIAD
          YFTZUUSUVHTZIDWEUUTUVHTAUVBUYGQDYLVHZAUYHIDAIUCDTZUQHUVHEFAUWKUYJLWLR
          XKWFDUUSIYFIDWIYJXIYKWLUVCUURUVPUVGUTUXQUVCUUGUVOUVFSYFUXTUYCUYFUXBBC
          UVNUVEFHUYAAUWMUUPUXAMXGUVCUWPUWQUXAUWRWTUYBUXKUXBUVEUVNVOUVEUVMYOZHU
          VEUVMYMUXBUWSUXCUXDUYKHTUXLUXKUXOBCUVEUVMGHJKOYPYBYQUXBUVEUVMYRYSYTUU
          AUVCDEHSIFUUFYFAUYGUUPUYIWLAUYJUWEUUPRWTUWLAUUJUUOUUCUUDUUBUUE @.
      @}
$)
    $}

$(
    @d M e s u v x y z @.  @d O s @.  @d P e s u v x y z @.  @d Q u v x y z @.
    @d R e s u v x y z @.  @d ph e s u v x y z @.
    caraext.m @e |- M = ( toOMeas ` P ) @.
    @{
      caraextros.q @e |- Q = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s
        ( ( x u. y ) e. s /\ ( x \ y ) e. s ) ) } @.
      caraextros.4 @e |- ( ph -> R e. Q ) @.
      @( Caratheodory's extension theorem for a ring of sets.  (Contributed by
         Thierry Arnoux, 19-Jul-2020.) @)
      caraextros @p |- ( ph -> ( M |` R ) = P ) @=
        ( vv wa wss wceq wcel vu vz ve cdm cuni cpw wfn cfv wral cres cpnf cicc
        cv cc0 co wf coms omsf syl2anc wb feq1 sylibr ffn syl jca fdm eqsstrrdi
        ax-mp pwuni cle wbr com cdom crab cesum cmpt crn clt ccnv fveq1i adantr
        csup elssuni adantl omsfval syl3anc eqtrid ad2antrr unieq breq1 anbi12d
        sseq2d elrab simplbi pweqd eleqtrd elpwi sselda ffvelcdmd ralrimiva
        nfcv
        cvv vex esumcl mpan eqid rnmptss csn simpr fveq2d esumsn eleqtrrd sylib
        snss snex elpw unisn eqimss2i snct esumex elrnmpt1s eqeltrrd infxrge0lb
        a1i esumeq1 eqbrtrd caddc crp cxr iccssxr sselid ad4antr simplr adantlr
        cr ad3antrrr cin ciun syl21anc mpbird simp-4r rpred readdcld rexrd nfbr
        nfv nfesum1 nfan ralrimi inelros sylancr iunin1 simprbi simpld sseqtrdi
        ex uniiun dfss1 c0 wdisj w3a simprd pmeassubadd eqbrtrrd difelros inss1
        cdif pmeasmono esumle xrletrd xrlelttrd xrltle imp omssubaddlem r19.29a
        xralrple pnfge breqtrrd cmnf wne wo xrge0neqmnf xrnemnf biimpi mpjaodan
        xrletri3 fvreseq1 biimpar ) AGDUDZUEUFZUGZDFUGZQZFUWJRZIUMZGUHZUWODUHZS
        ZIFUIZGFUJDSZAUWKUWLAUWJUNUKULUOZGUPZUWKAUWJUXADUQUHZUPZUXBAFETZFUXADUP
        ZUXDOJFDEURUSGUXCSUXBUXDUTMUWJUXAGUXCVAVHVBZUWJUXAGVCVDAUXFUWLJFUXADVCV
        DVEAFUWIUWJAUXFUWIFSZJFUXADVFZVDZUWIVIVGZAUWRIFAUWOFTZQZUWRUWPUWQVJVKZU
        WQUWPVJVKZQZUXMUXNUXOUXMUWPUAUWOUBUMZUEZRZUXQVLVMVKZQZUBUWIUFZVNZUAUMZP
        UMZDUHZPVOZVPZVQZUXAVRVSWBZUWQVJUXMUWPUWOUXCUHZUYJUWOGUXCMVTUXMUXEUXFUW
        OFUERZUYKUYJSAUXEUXLOWAZAUXFUXLJWAZUXLUYLAUWOFWCWDZUAPUBUWOFDEWEWFWGUXM
        UYIUWQUXMUYGUXATZUAUYCUIUYIUXARUXMUYPUAUYCUXMUYDUYCTZQZUYFUXATZPUYDUIZU
        YPUYRUYSPUYDUYRUYEUYDTZQZFUXAUYEDUXMUXFUYQVUAUYNWHZUYRUYDFUYEUYRUYDFUFZ
        TUYDFRZUYRUYDUYBVUDUYQUYDUYBTZUXMUYQVUFUWOUYDUEZRZUYDVLVMVKZQZUYAVUJUBU
        YDUYBUXQUYDSZUXSVUHUXTVUIVUKUXRVUGUWOUXQUYDWIWLUXQUYDVLVMWJWKWMZWNWDAUY
        BVUDSUXLUYQAUWIFUXJWOWHWPUYDFWQVDZWRZWSZWTUYDXBTZUYTUYPUAXCZUYDUYFPXBPU
        YDXAZXDXEVDZWTUAUYCUYGUXAUYHUYHXFZXGVDUXMUWOXHZUYFPVOZUWQUYIUXMUYFUWQPU
        WOFUXMUYEUWOSZQUYEUWODUXMVVCXIXJAUXLXIZUXMFUXAUWODUYNVVDWSZXKUXMVVAUYCT
        ZVVBXBTZVVBUYITUXMVVAUYBTZUWOVVAUEZRZVVAVLVMVKZQZQVVFUXMVVHVVLUXMVVAUWI
        RZVVHUXMUWOUWITVVMUXMUWOFUWIVVDUXMUXFUXHUYNUXIVDXLUWOUWIIXCZXNXMVVAUWIU
        WOXOXPVBUXMVVJVVKVVJUXMVVIUWOUWOVVNXQXRYDUXLVVKAUWOFXSWDVEVEUYAVVLUBVVA
        UYBUXQVVASZUXSVVJUXTVVKVVOUXRVVIUWOUXQVVAWIWLUXQVVAVLVMWJWKWMVBVVGUXMVV
        AUYFPXTYDUAUYCUYGVVBVVAUYHXBVUTUYDVVAUYFPYEYAUSYBYCYFUXMUWPYOTZUXOUWPUK
        SZUXMVVPQZUXOUWQUWPUCUMZYGUOZVJVKZUCYHUIZVVRVWAUCYHVVRVVSYHTZQZUYGVVTVR
        VKZVWAUAUYCVWDUYQQZVWEQZUWQYITZVVTYITZUWQVVTVRVKZVWAUXMVWHVVPVWCUYQVWEU
        XMUXAYIUWQUNUKYJZVVEYKZYLZVWGVVTVWGUWPVVSUXMVVPVWCUYQVWEUUAVWGVVSVWDVWC
        UYQVWEVVRVWCXIZWHUUBUUCUUDZVWGUWQUYGVVTVWMVWGUXAYIUYGVWKVWGUYQUYTUYPVWD
        UYQVWEYMVWGUYSPUYDVWFVWEPVWFPUUFPUYGVVTVRUYDUYFPVURUUGPVRXAPVVTXAUUEUUH
        VWGVUAUYSVWGVUAQFUXAUYEDVWDUXFUYQVWEVUAUXMUXFVVPVWCUYNWHZYPVWGUYDFUYEVW
        FVUEVWEVVRUYQVUEVWCUXMUYQVUEVVPVUMYNYNWAWRWSUUPUUIUYDUYFPUYCVURXDUSYKVW
        OVWFUWQUYGVJVKZVWEVVRUYQVWQVWCUXMUYQVWQVVPUYRUWQUYDUYEUWOYQZDUHZPVOZUYG
        UXMVWHUYQVWLWAUYRUXAYIVWTVWKUYRVUPVWSUXATZPUYDUIVWTUXATVUQUYRVXAPUYDVUB
        FUXAVWRDVUCVUBUXEUYEFTZUXLVWRFTZUXMUXEUYQVUAUYMWHZVUNUXMUXLUYQVUAVVDWHB
        CUYEUWOEFHINUUJWFZWSZWTUYDVWSPXBVURXDUUKYKUYRUXAYIUYGVWKVUSYKUYRPUYDVWR
        YRZDUHUWQVWTVJUYRVXGUWODUYRVXGPUYDUYEYRZUWOYQZUWOPUYDUWOUYEUULUYRUWOVXH
        RVXIUWOSUYRUWOVUGVXHUYRUYQVUHUXMUYQXIZUYQVUHVUIUYQVUFVUJVULUUMZUUNVDPUY
        DUUQUUOUWOVXHUURXMWGXJUYRBCUYDVWRDEFPHIUXMUXFUYQUYNWAAUUSDUHUNSZUXLUYQK
        WHUXMBUMZVLVMVKVXMFRCVXMCUMZUUTUVAZVXMUEDUHVXMVXNDUHCVOSZUYQAVXOVXPUXLL
        YNYNZNUXMUXEUYQUYMWAUYRUYQVUIVXJUYQVUHVUIVXKUVBVDVXEUVCUVDUYRUYDVWSUYFP
        UYCVXJVXFVUOVUBBCVWRUYEDFVUCAVXLUXLUYQVUAKYPUYRVXOVXPVUAVXQYNVXEVUNVUBU
        XEVXBVXCUYEVWRUVGFTVXDVUNVXEBCUYEVWREFHINUVEWFVWRUYERVUBUYEUWOUVFYDUVHU
        VIUVJYNYNWAVWFVWEXIUVKVWHVWIQVWJVWAUWQVVTUVLUVMYSVWDUAUBPUWOFDVVSGEMUXM
        UXEVVPVWCUYMWHVWPUXMUYLVVPVWCUYOWHUXMVVPVWCYMVWNUVNUVOWTVVRVWHVVPUXOVWB
        UTUXMVWHVVPVWLWAUXMVVPXIUCUWQUWPUVPUSYTUXMVVQQZUWQUKUWPVJVXRVWHUWQUKVJV
        KUXMVWHVVQVWLWAUWQUVQVDUXMVVQXIUVRUXMUWPYITZUWPUVSUVTZVVPVVQUWAZUXMUXAY
        IUWPVWKUXMUWJUXAUWOGAUXBUXLUXGWAAFUWJUWOUXKWRWSZYKZUXMUWPUXATVXTVYBUWPU
        WBVDVXSVXTQVYAUWPUWCUWDUSUWEVEUXMVXSVWHUWRUXPUTVYCVWLUWPUWQUWFUSYTWTUWM
        UWNQUWTUWSIUWJFGDUWGUWHYS @.
    @}

    caraext.n @e |- N = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s
      ( ( x i^i y ) e. s /\ E. z e. ~P s ( z e. Fin /\ Disj_ t e. z t
      /\ ( x \ y ) = U. z ) ) ) } @.
    caraext.4 @e |- ( ph -> R e. N ) @.
    @( Caratheodory's Extension Theorem: Given a pre-measure ` P ` on a
       semiring of sets ` R ` , there exists a measure ` M ` which extends
       ` P ` over the sigma-algebra generated by ` R ` .  @)
    caraext @p |- ( ph -> ( M |` S ) = P ) @=
      ? @.
$)
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Caratheodory's extension theorem: examples and applications
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

$(
  @{
    ovoloms.1 @e |- I = ( ( <_ i^i ( RR X. RR ) ) ^m NN ) @.
    ovoloms.2 @e |- R = U. ran ( f e. I
      |-> { ran ( (,) o. f ) , ran ( ( abs o. - ) o. f ) } ) @.
    @( The pre-measure ` R ` of the Lebesgue measure is defined over unions of
       open intervals.  (Contributed by Thierry Arnoux, 6-Jun-2020.) @)
    ovolomsdm @p |- dom R = U. ran ( f e. I |-> ran ( (,) o. f ) ) @=
      ? @.

    @( The pre-measure of the Lebesgue measure is defined  @)
    ovolomsunidm @p |- U. dom R = RR @=
      ? @.

    @( Express the Lebesgue outer measure as an outer measure.  This could be
       considered as an alternative definition of the Lebesgue outer measure.
       (Contributed by Thierry Arnoux, 6-Jun-2020.) @)
    ovoloms @p |- vol* = ( toOMeas ` R ) @=
      ? @.
  @}
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Caratheodory's extension theorem: measure on RR ^ N
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

