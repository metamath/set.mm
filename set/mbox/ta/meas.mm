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
       union.  Litterature usually uses capital greek sigma and omega letters
       for the algebra set, and the base set respectively.  We are using ` S `
       and ` O ` as a parallel.  (Contributed by Thierry Arnoux,
       3-Sep-2016.) $)
    df-siga $a |- sigAlgebra = ( o e. _V |-> { s | ( s C_ ~P o /\
      ( o e. s /\ A. x e. s ( o \ x ) e. s
      /\ A. x e. ~P s ( x ~<_ om -> U. x e. s ) ) ) } ) $.
  $}

  ${
    $d o s $.
    $( Lemma for ~ issiga and ~ isrnsiga The set of sigma algebra with base set
       ` o ` is a set.  Note: a more generic version with
       ` ( O e. _V -> ... ) ` could be useful for ~ sigaval .  (Contributed by
       Thierry Arnoux, 24-Oct-2016.) $)
    sigaex $p |- { s | ( s C_ ~P o /\ ( o e. s /\ A. x e. s ( o \ x ) e. s
      /\ A. x e. ~P s ( x ~<_ om -> U. x e. s ) ) ) } e. _V $=
      ( cv wcel cdif wral com cdom wbr cuni wi cpw w3a crab cab cvv vex pwexg
      wa wss df-rab elpw anbi1i abbii eqtri mp2b rabex eqeltrri ) BDZCDZEUJADZF
      UKEAUKGULHIJULKUKELAUKMGNZCUJMZMZOZUKUNUAZUMTZCPZQUPUKUOEZUMTZCPUSUMCUOUB
      VAURCUTUQUMUKUNCRUCUDUEUFUMCUOUJQEUNQEUOQEBRUJQSUNQSUGUHUI $.
  $}

  ${
    $d s o x O $.
    $( The set of sigma-algebra with a given base set.  (Contributed by Thierry
       Arnoux, 23-Sep-2016.) $)
    sigaval $p |- ( O e. _V -> ( sigAlgebra ` O ) = { s | ( s C_ ~P O /\
      ( O e. s /\ A. x e. s ( O \ x ) e. s
      /\ A. x e. ~P s ( x ~<_ om -> U. x e. s ) ) ) } ) $=
      ( vo cvv wcel cv cpw wss cdif wral com cdom wbr w3a cab csiga wceq pwexg
      wa cuni cfv crab df-rab vex elpw anbi1i abbii eqtri rabexg 3syl syl5eqelr
      wi pweq sseq2d eleq1 difeq1 eleq1d ralbidv 3anbi12d anbi12d abbidv fvmptg
      df-siga mpdan ) BEFZCGZBHZIZBVGFZBAGZJZVGFZAVGKZVKLMNVKUAVGFUMAVGHKZOZTZC
      PZEFBQUBVRRVFVRVPCVHHZUCZEVTVGVSFZVPTZCPVRVPCVSUDWBVQCWAVIVPVGVHCUEUFUGUH
      UIVFVHEFVSEFVTEFBESVHESVPCVSEUJUKULDBVGDGZHZIZWCVGFZWCVKJZVGFZAVGKZVOOZTZ
      CPVREEQWCBRZWKVQCWLWEVIWJVPWLWDVHVGWCBUNUOWLWFVJWIVNVOWCBVGUPWLWHVMAVGWLW
      GVLVGWCBVKUQURUSUTVAVBADCVDVCVE $.
  $}

  ${
    $d o s x O $.  $d o s x S $.
    $( An alternative definition of the sigma-algebra, for a given base set.
       (Contributed by Thierry Arnoux, 19-Sep-2016.) $)
    issiga $p |- ( S e. _V -> ( S e. ( sigAlgebra ` O ) <->
      ( S C_ ~P O /\ ( O e. S /\ A. x e. S ( O \ x ) e. S
      /\ A. x e. ~P S ( x ~<_ om -> U. x e. S ) ) ) ) ) $=
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
    $d a o s x S $.
    $( The property of being a sigma algebra on an indefinite base set.
       (Contributed by Thierry Arnoux, 3-Sep-2016.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    isrnsigaOLD $p |- ( S e. U. ran sigAlgebra <-> ( S e. _V /\
      E. o ( S C_ ~P o /\ ( o e. S /\ A. x e. S ( o \ x ) e. S
      /\ A. x e. ~P S ( x ~<_ om -> U. x e. S ) ) ) ) ) $=
      ( vs csiga crn cuni wcel cvv cv cpw wss cdif wral com wi w3a wa cab eleq2
      cdom wbr wrex wex df-siga crab df-rab vex elpwg ax-mp anbi1i abbii eqtr2i
      grothpwex pwex rabex eqeltri wceq sseq1 raleqbi1dv pweq imbi12d raleqbidv
      wb biidd 3anbi123d anbi12d abfmpunirn rexv anbi2i bitri ) BEFGHBIHZBCJZKZ
      LZVMBHZVMAJZMZBHZABNZVQOUAUBZVQGZBHZPZABKZNZQZRZCIUCZRVLWHCUDZRDJZVNLZVMW
      KHZVRWKHZAWKNZWAWBWKHZPZAWKKZNZQZRZWHCDBEIACDUEXADSZWTDVNKZUFZIXDWKXCHZWT
      RZDSXBWTDXCUGXFXADXEWLWTWKIHXEWLVDDUHWKVNIUIUJUKULUMWTDXCVNCUNUOUPUQWKBUR
      ZWLVOWTWGWKBVNUSXGWMVPWOVTWSWFWKBVMTWNVSAWKBWKBVRTUTXGWQWDAWRWEWKBVAXGWAW
      AWPWCXGWAVEWKBWBTVBVCVFVGVHWIWJVLWHCVIVJVK $.

    $( The property of being a sigma algebra on an indefinite base set.
       (Contributed by Thierry Arnoux, 3-Sep-2016.)  (Proof shortened by
       Thierry Arnoux, 23-Oct-2016.) $)
    isrnsiga $p |- ( S e. U. ran sigAlgebra <-> ( S e. _V /\
      E. o ( S C_ ~P o /\ ( o e. S /\ A. x e. S ( o \ x ) e. S
      /\ A. x e. ~P S ( x ~<_ om -> U. x e. S ) ) ) ) ) $=
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
      cdom cvv isrnsiga simprbi 3simpa adantl eximi difeq2 syl6eq eleq1d rspcva
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
    sigaclcu $p |- ( ( S e. U. ran sigAlgebra /\ A e. ~P S /\ A ~<_ om )
      -> U. A e. S ) $=
      ( vx vo csiga crn cuni wcel cpw com cdom wbr w3a cv wi wral simp2 cdif wa
      wss wex cvv isrnsiga simprbi simpr3 exlimiv syl 3ad2ant1 simp3 wceq breq1
      unieq eleq1d imbi12d rspcv syl3c ) BEFGHZABIZHZAJKLZMUSCNZJKLZVAGZBHZOZCU
      RPZUTAGZBHZUQUSUTQUQUSVFUTUQBDNZITZVIBHZVIVARBHCBPZVFMSZDUAZVFUQBUBHVNCBD
      UCUDVMVFDVJVKVLVFUEUFUGUHUQUSUTUIVEUTVHOCAURVAAUJZVBUTVDVHVAAJKUKVOVCVGBV
      AAULUMUNUOUP $.

    ${
      $d z x A $.  $d z B $.  $d k z S $.
      sigaclcuni.1 $e |- F/_ k A $.
      $( A sigma-algebra is closed under countable union: indexed union version
         (Contributed by Thierry Arnoux, 8-Jun-2017.) $)
      sigaclcuni $p |- ( ( S e. U. ran sigAlgebra /\ A. k e. A B e. S
                                         /\ A ~<_ om ) -> U_ k e. A B e. S ) $=
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
      ( cfn wcel csiga crn cuni cpw com cdom wbr csdm isfinite sdomdom sigaclcu
      sylbi syl3an3 ) ACDZBEFGDABHDAIJKZAGBDRAILKSAMAINPABOQ $.

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
       ` ( 1 ..^ N ) ` (Contributed by Thierry Arnoux, 28-Dec-2016.) $)
    sigaclfu2 $p |- ( ( S e. U. ran sigAlgebra /\ A. k e. ( 1 ..^ N ) A e. S )
      -> U_ k e. ( 1 ..^ N ) A e. S ) $=
      ( csiga crn cuni wcel c1 cfzo co wral wa ciun cn cun wceq iuneq2i eqtri
      c0 cv cif cdif iunxun wss fzossnn undif mpbi iuneq1 iftrue eldifn iffalse
      ax-mp wn syl iun0 uneq12i 3eqtr3i un0 0elsiga wi simpr simpllr mpd ifclda
      simplll exp31 ralimdv2 imp sylan sigaclcu2 syldan syl5eqelr ) BEFGHZABHZC
      IDJKZLZMCVPANZCOCUAZVPHZATUBZNZBWBVRTPZVRCVPOVPUCZPZWANZCVPWANZCWDWANZPWB
      WCCVPWDWAUDWEOQZWFWBQVPOUEWIDUFVPOUGUHCWEOWAUIUMWGVRWHTCVPWAAVTATUJRWHCWD
      TNTCWDWATVSWDHVTUNZWATQVSOVPUKVTATULUORCWDUPSUQURVRUSSVNVQWABHZCOLZWBBHVN
      TBHZVQWLBUTWMVQWLWMVOWKCVPOWMVTVOVAZVSOHZWKWMWNMWOMZVTATBWPVTMVTVOWPVTVBW
      MWNWOVTVCVDWMWNWOWJVFVEVGVHVIVJWABCVKVLVM $.

    $d k M $.  $d k ph $.  $d x A $.
    sigaclcu3.1 $e |- ( ph -> S e. U. ran sigAlgebra ) $.
    sigaclcu3.2 $e |- ( ph -> ( N = NN \/ N = ( 1 ..^ M ) ) ) $.
    sigaclcu3.3 $e |- ( ( ph /\ k e. N ) -> A e. S ) $.
    $( A sigma-algebra is closed under countable or finite union.  (Contributed
       by Thierry Arnoux, 6-Mar-2017.) $)
    sigaclcu3 $p |- ( ph -> U_ k e. N A e. S ) $=
      ( cn wceq ciun wcel wa simpr iuneq1d wral adantr raleqdv mpbid c1 cfzo co
      csiga crn cuni ralrimiva sigaclcu2 syl2anc eqeltrd sigaclfu2 mpjaodan ) A
      FJKZDFBLZCMFUAEUBUCZKZAUMNZUNDJBLZCUQDFJBAUMOZPUQCUDUEUFMZBCMZDJQZURCMAUT
      UMGRUQVADFQZVBAVCUMAVADFIUGZRUQVADFJUSSTBCDUHUIUJAUPNZUNDUOBLZCVEDFUOBAUP
      OZPVEUTVADUOQZVFCMAUTUPGRVEVCVHAVCUPVDRVEVADFUOVGSTBCDEUKUIUJHUL $.
  $}

  ${
    $d o x S $.  $d x O $.
    $( Property of being a sigma-algebra with a given base set, noting that the
       base set of a sigma algebra is actually its union set.  (Contributed by
       Thierry Arnoux, 24-Sep-2016.)  (Revised by Thierry Arnoux,
       23-Oct-2016.) $)
    issgon $p |- ( S e. ( sigAlgebra ` O ) <->
      ( S e. U. ran sigAlgebra /\ O = U. S ) ) $=
      ( vx vo csiga wcel cuni wceq wa elex cpw wss cdif wral w3a elpwuni biimpa
      cv ancom eqcom cfv crn fvssunirn sseli cvv com cdom wbr wi issiga 3imtr4i
      3ad2antr1 syl6bi mpcom jca wex isrnsiga simprbi pweq sseq2d difeq1 eleq1d
      wb eleq1 ralbidv 3anbi12d anbi12d syl ibi exlimiv biimprd pwuni syl5sseqr
      simprd jctild anim2d biimpar syl56 impcom impbii ) ABEUAZFZAEUBGZFZBAGZHZ
      IWBWDWFWAWCAEBUCUDAUEFZWBWFAWAJWGWBABKZLZBAFZBCRZMZAFZCANZWKUFUGUHWKGAFUI
      CAKNZOZIZWFCABUJZWIWNWJWFWOWJWIIWEBHZWIWJIWFWJWIWSABPQWIWJSBWETUKULUMUNUO
      WFWDWBWDWGWEAFZWEWKMZAFZCANZWOOZIWFWGWQIWBWDWGXDAWCJWDAWEKZLZXDWDADRZKZLZ
      XGAFZXGWKMZAFZCANZWOOZIZDUPZXFXDIZWDWGXPCADUQURXOXQDXOXQXOXGWEHZXOXQVCXIX
      MXJXRWOXJXIIWEXGHZXIXJIXRXJXIXSAXGPQXIXJSXGWETUKULXRXIXFXNXDXRXHXEAXGWEUS
      UTXRXJWTXMXCWOXGWEAVDXRXLXBCAXRXKXAAXGWEWKVAVBVEVFVGVHVIVJVHVNUOWFXDWQWGW
      FXDWPWIWFWPXDWFWJWTWNXCWOBWEAVDWFWMXBCAWFWLXAABWEWKVAVBVEVFVKWFXEAWHAVLBW
      EUSVMVOVPWGWBWQWRVQVRVSVT $.
  $}

  ${
    $( A sigma alebra is a sigma on its union set.  (Contributed by Thierry
       Arnoux, 6-Jun-2017.) $)
    sgon $p |- ( S e. U. ran sigAlgebra -> S e. ( sigAlgebra ` U. S ) ) $=
      ( csiga crn cuni wcel wceq cfv eqid wa issgon biimpri mpan2 ) ABCDEZADZNF
      ZANBGEZNHPMOIANJKL $.
  $}

  ${
    $( An element of a sigma-algebra is a subset of the base set.  (Contributed
       by Thierry Arnoux, 6-Jun-2017.) $)
    elsigass $p |- ( ( S e. U. ran sigAlgebra /\ A e. S ) -> A C_ U. S ) $=
      ( csiga crn cuni wcel wa cpw cfv wss sgon sigasspw syl sselda elpwid ) BC
      DEFZABFGABEZPBQHZAPBQCIFBRJBKQBLMNO $.
  $}

  ${
    $( Dropping the base information off a sigma-algebra.  (Contributed by
       Thierry Arnoux, 13-Feb-2017.) $)
    elrnsiga $p |- ( S e. ( sigAlgebra ` O ) -> S e. U. ran sigAlgebra ) $=
      ( csiga cfv crn cuni fvssunirn sseli ) BCDCEFACBGH $.
  $}

  ${
    $d x S $.
    $( The property of being a sigma algebra, universe is the union set.
       (Contributed by Thierry Arnoux, 11-Nov-2016.) $)
    isrnsigau $p |- ( S e. U. ran sigAlgebra -> ( S C_ ~P U. S /\ ( U. S e. S
      /\ A. x e. S ( U. S \ x ) e. S
      /\ A. x e. ~P S ( x ~<_ om -> U. x e. S ) ) ) ) $=
      ( csiga crn cuni wcel cfv cpw wss cv cdif wral com cdom wbr wi w3a wa cvv
      sgon wb elex issiga syl mpbid ) BCDEZFZBBEZCGFZBUHHIUHBFUHAJZKBFABLUJMNOU
      JEBFPABHLQRZBTUGBSFUIUKUABUFUBABUHUCUDUE $.

    $( A sigma-algebra contains its universe set.  (Contributed by Thierry
       Arnoux, 13-Feb-2017.)  (Shortened by Thierry Arnoux, 6-Jun-2017.) $)
    unielsiga $p |- ( S e. U. ran sigAlgebra -> U. S e. S ) $=
      ( csiga crn cuni wcel cfv sgon baselsiga syl ) ABCDEAADZBFEJAEAGJAHI $.
  $}

  ${
    $d o x y $.
    $( Lebesgue-measurable subsets of ` RR ` form a sigma-algebra (Contributed
       by Thierry Arnoux, 10-Sep-2016.)  (Revised by Thierry Arnoux,
       24-Oct-2016.) $)
    dmvlsiga $p |- dom vol e. ( sigAlgebra ` RR ) $=
      ( vx vy cvol cdm cr csiga cfv wcel cpw wss cv cdif wral com cdom wbr cuni
      wi rgen cn w3a pwssb mblss mprgbir rembl cmmbl ciun nnenom ensymi domentr
      cen mpan2 elpwi dfss3 sylib iunmbl2 syl2anr uniiun eleq1i syl6ibr 3pm3.2i
      ex cvv wa wb reex pwex ssexi issiga ax-mp mpbir2an ) CDZEFGHZVLEIZJZEVLHZ
      EAKZLVLHZAVLMZVQNOPZVQQZVLHZRZAVLIZMZUAZVOVQEJAVLAVLEUBVQUCUDZVPVSWEUEVRA
      VLVQUFSWCAWDVQWDHZVTBVQBKZUGZVLHZWBWHVTWKVTVQTOPZWIVLHBVQMZWKWHVTNTUKPWLT
      NUHUIVQNTUJULWHVQVLJWMVQVLUMBVQVLUNUOVQWIBUPUQVBWAWJVLBVQURUSUTSVAVLVCHVM
      VOWFVDVEVLVNEVFVGWGVHAVLEVIVJVK $.
  $}

  ${
    $d x O $.  $d x V $.
    $( Any power set forms a sigma-algebra.  (Contributed by Thierry Arnoux,
       13-Sep-2016.)  (Revised by Thierry Arnoux, 24-Oct-2016.) $)
    pwsiga $p |- ( O e. V -> ~P O e. ( sigAlgebra ` O ) ) $=
      ( vx wcel cpw csiga cfv wss cdif wral com cdom wbr cuni w3a ssid ralrimiv
      cv wi a1d a1i pwidg difss elpw2g mpbiri sspwuni uniex bitr4i biimpi elpwi
      vex elpw imim1i mp1i 3jca cvv wa wb pwexg issiga syl mpbir2and ) ABDZAEZA
      FGDZVDVDHZAVDDZACRZIZVDDZCVDJZVHKLMZVHNZVDDZSZCVDEZJZOZVFVCVDPUAVCVGVKVQA
      BUBVCVJCVDVCVJVHVDDVCVJVIAHAVHUCVIABUDUETQVCVOCVPVHVDHZVOSVHVPDZVOSVCVSVN
      VLVSVNVSVMAHVNVHAUFVMAVHCUKUGULUHUITVTVSVOVHVDUJUMUNQUOVCVDUPDVEVFVRUQURA
      BUSCVDAUTVAVB $.
  $}

  ${
    $d x O $.
    $( The smallest possible sigma-algebra containing ` O ` (Contributed by
       Thierry Arnoux, 13-Sep-2016.) $)
    prsiga $p |- ( O e. V -> { (/) , O } e. ( sigAlgebra ` O ) ) $=
      ( vx wcel c0 cpr cpw cdif wral cuni 0ex cvv wceq eleq1d ralprg cun pm3.2i
      wa wb unieq wss cv com cdom wbr wi w3a csiga cfv 0elpw pwidg prssi prid2g
      sylancr dif0 syl5eqel difid prid1 a1i difeq2 mpan mpbir2and eqeltri unisn
      uni0 snex mp1i mpbiri unisng eqeltrd uniprg uncom eqtri syl6eq prex ralun
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
    $( A sigma-algebra is closed under countable intersection.  Deduction
       version.  (Contributed by Thierry Arnoux, 19-Sep-2016.) $)
    sigaclci $p |- ( ( ( S e. U. ran sigAlgebra /\ A e. ~P S ) /\
      ( A ~<_ om /\ A =/= (/) ) ) -> |^| A e. S ) $=
      ( vz vx vy cuni wcel wa com cdom wbr cv cdif wral wi wss adantr wceq syl
      wb csiga crn cpw wne cint ciun w3a isrnsigau simprd simp2d wrex cab elpwi
      ssrexv ss2abdv uniiunlem mpbid sylan9ssr cvv abrexexg elpwg adantl mpbird
      c0 simp3d jca abrexdom2jm domtr sylan breq1 eleq1d imbi12d rspcva sylsyld
      ex unieq ssralv sylc dfiun2g eleq1 3syl sylibrd difeq2 rspccv adantrd imp
      simpr pwuni syl6ss iundifdifd adantld syl6 ) BUAUBFGZABUCZGZHZAIJKZAVDUDZ
      HZHAUEZBGZBFZCAXBCLZMZUFZMZBGZWPWSXGWPWQXGWRWPXBDLZMZBGZDBNZWQXEBGZXGWMXK
      WOWMXBBGZXKXHIJKZXHFZBGZOZDWNNZWMBXBUCZPZXMXKXRUGDBUHUIZUJQWPWQELXDRZCAUK
      ZEULZFZBGZXLWPYDWNGZXRHWQYDIJKZYFWPYGXRWPYGYDBPZWOWMYDYBCBUKZEULZBWOYCYJE
      WOABPZYCYJOABUMZYBCABUNSUOWMXDBGZCBNZYKBPZWMXMYOXCIJKXCFBGOCWNNZWMXTXMYOY
      QUGCBUHUIUJZWMYOYOYPTYRCEBXDBBUPSUQURWOYGYITZWMWOYDUSGYSCEAXDWNUTYDBUSVAS
      VBVCWMXRWOWMXMXKXRYAVEQVFWOWQYHOWMWOWQYHWOYDAJKWQYHECAXDWNVGYDAIVHVIVOVBX
      QYHYFODYDWNXHYDRZXNYHXPYFXHYDIJVJYTXOYEBXHYDVPVKVLVMVNWPYNCANZXEYERXLYFTW
      PYLYOUUAWOYLWMYMVBWMYOWOYRQYNCABVQVRCEAXDBVSXEYEBVTWAWBXJXGDXEBXHXERXIXFB
      XHXEXBWCVKWDVNWEWFWPWSXAXGTZWPWSWTXFRZUUBWPWRUUCWQWPWOAXSPWRUUCOWMWOWGWOA
      BXSYMBWHWICAXBWJWAWKWTXFBVTWLWFVC $.
  $}

  ${
    $d x S $.  $d x B $.
    $( A sigma algebra is closed under set difference.  (Contributed by Thierry
       Arnoux, 13-Sep-2016.) $)
    difelsiga $p |- ( ( S e. U. ran sigAlgebra /\ A e. S /\ B e. S ) ->
      ( A \ B ) e. S ) $=
      ( vx csiga crn cuni wcel w3a cdif cpr cint wss wceq wral com cdom wbr cpw
      syl2anc cin simp2 elssuni difin2 cv isrnsigau simprd simp2d difeq2 eleq1d
      3syl wi rspccva sylan 3adant2 intprg eqtr4d c0 wne simp1 prex elpw sylibr
      prssi prct prnzg syl sigaclci syl22anc eqeltrd ) CEFGHZACHZBCHZIZABJZCGZB
      JZAKZLZCVNVOVQAUAZVSVNVLAVPMVOVTNVKVLVMUBZACUCABVPUDUKVNVQCHZVLVSVTNVKVMW
      BVLVKVPDUEZJZCHZDCOZVMWBVKVPCHZWFWCPQRWCGCHULDCSZOZVKCVPSMWGWFWIIDCUFUGUH
      WEWBDBCWCBNWDVQCWCBVPUIUJUMUNUOZWAVQACCUPTUQVNVKVRWHHZVRPQRZVRURUSZVSCHVK
      VLVMUTVNVRCMZWKVNWBVLWNWJWAVQACVDTVRCVQAVAVBVCVNWBVLWLWJWAVQACCVETVNWBWMW
      JVQACVFVGVRCVHVIVJ $.
  $}

  ${
    $d x A $.  $d x B $.  $d x S $.
    $( A sigma algebra is closed under set union.  (Contributed by Thierry
       Arnoux, 13-Dec-2016.) $)
    unelsiga $p |- ( ( S e. U. ran sigAlgebra /\ A e. S /\ B e. S ) ->
      ( A u. B ) e. S ) $=
      ( vx csiga crn cuni wcel w3a cpr cun wceq uniprg 3adant1 com cdom wbr cpw
      wi wral cv cdif isrnsigau simprd simp3d 3ad2ant1 prct prelpwi breq1 unieq
      wss wa eleq1d imbi12d rspcv syl mp2d eqeltrrd ) CEFGHZACHZBCHZIZABJZGZABK
      ZCUTVAVDVELUSABCCMNVBDUAZOPQZVFGZCHZSZDCRZTZVCOPQZVDCHZUSUTVLVAUSCGZCHZVO
      VFUBCHDCTZVLUSCVORUKVPVQVLIDCUCUDUEUFUTVAVMUSABCCUGNUTVAVLVMVNSZSZUSUTVAU
      LVCVKHVSABCUHVJVRDVCVKVFVCLZVGVMVIVNVFVCOPUIVTVHVDCVFVCUJUMUNUOUPNUQUR $.
  $}

  ${
    $( A sigma algebra is closed under set intersection.  (Contributed by
       Thierry Arnoux, 13-Dec-2016.) $)
    inelsiga $p |- ( ( S e. U. ran sigAlgebra /\ A e. S /\ B e. S ) ->
      ( A i^i B ) e. S ) $=
      ( csiga crn cuni wcel w3a cin cdif dfin4 difelsiga syld3an3 syl5eqel ) CD
      EFGZACGZBCGZHABIAABJZJZCABKOPQRCGSCGABCLARCLMN $.
  $}

  ${
    $d x A $.  $d x S $.
    $( Building a sigma algebra from intersections with a given set.
       (Contributed by Thierry Arnoux, 26-Dec-2016.) $)
    sigainb $p |- ( ( S e. U. ran sigAlgebra /\ A e. S ) ->
      ( S i^i ~P A ) e. ( sigAlgebra ` A ) ) $=
      ( vx csiga cuni wcel wa cpw wss wral simpr syl elin sylanbrc simplr elpwg
      syl3anc ralrimiva sstr mpan2 crn cin cvv cdif com cdom wbr w3a cfv inex1g
      cv wi adantr inss2 a1i pwidg simpll inss1 sseldi difelsiga mpbiri simplll
      difss elpwi 3syl biimpar syl2anc sigaclcu sspwuni uniex elpw bitr4i sylib
      vex ex 3jca issiga syl12anc ) BDUAEZFZABFZGZBAHZUBZUCFZWDWCIZAWDFZACUKZUD
      ZWDFZCWDJZWHUEUFUGZWHEZWDFZULZCWDHZJZUHZWDADUIFZVTWEWABWCVSUJUMWFWBBWCUNZ
      UOWBWGWKWQWBWAAWCFZWGVTWAKZWBWAXAXBABUPLABWCMNWBWJCWDWBWHWDFZGZWIBFZWIWCF
      ZWJXDVTWAWHBFXEVTWAXCUQVTWAXCOXDWDBWHBWCURZWBXCKUSAWHBUTQZXDXEXFXHXEXFWIA
      IAWHVCWIABPVALWIBWCMNRWBWOCWPWBWHWPFZGZWLWNXJWLGZWMBFZWMWCFZWNXKVTWHBHFZW
      LXLVTWAXIWLVBXKXIWHBIZXNWBXIWLOZXKXIWHWDIZXOXPWHWDVDZXQWDBIXOXGWHWDBSTVEX
      IXNXOWHBWPPVFVGXJWLKWHBVHQXKWHWCIZXMXKXIXQXSXPXRXQWFXSWTWHWDWCSTVEXSWMAIX
      MWHAVIWMAWHCVNVJVKVLVMWMBWCMNVORVPWEWSWFWRGCWDAVQVFVR $.
  $}

  ${
    $d s x A $.  $d s x O $.
    $( The intersection of a collection of sigma-algebras of same base is a
       sigma-algebra.  (Contributed by Thierry Arnoux, 27-Dec-2016.) $)
    insiga $p |- ( ( A =/= (/) /\ A e. ~P ( sigAlgebra ` O ) )
      -> |^| A e. ( sigAlgebra ` O ) ) $=
      ( vx vs csiga cpw wcel wa cvv wss cv adantr simpr syl wb ralrimiva elintg
      wral mpbird jca c0 wne cfv cint cdif com cdom wbr cuni w3a intex intssuni
      wi biimpi elpwi sigasspw vex elpw sylibr ssriv syl6ss sspwuni sylib sstrd
      simplr elelpwi syl2anc issiga ax-mp simprd simp1d wex n0 ex eximdv elfvex
      mpd exlimiv simpll elinti adantll simp2d r19.21bi difexg simplll sylan9ss
      simpllr intss1 sylancom simp3d sylc uniexg ad2antlr 3jca biimpar syl12anc
      imp ) AUAUBZABEUCZFGZHZAUDZIGZXBBFZJZBXBGZBCKZUEZXBGZCXBRZXGUFUGUHZXGUIZX
      BGZUMZCXBFZRZUJZXBWSGZWRXCWTWRXCAUKUNLXAXBAUIZXDWRXBXSJWTAULLXAAXDFZJZXSX
      DJXAWTYAWRWTMWTAWSXTAWSUODWSXTDKZWSGZYBXDJZYBXTGBYBUPYBXDDUQZURUSUTVANAXD
      VBVCVDXAXFXJXPXAXFBYBGZDARZXAYFDAXAYBAGZHZYFXHYBGZCYBRZXKXLYBGZUMZCYBFZRZ
      YIYDYFYKYOUJZYIYCYDYPHZYIYHWTYCXAYHMWRWTYHVEYBAWSVFVGZYBIGYCYQOYECYBBVHVI
      VCVJZVKPXABIGZXFYGOXAYCDVLZYTXAYHDVLZUUAWRUUBWTWRUUBDAVMUNLXAYHYCDXAYHYCY
      RVNVOVQYCYTDYBBEVPVRNZDBAIQNSXAXICXBXAXGXBGZHZXIYJDARZUUEYJDAUUEYHHZYIXGY
      BGZYJUUGXAYHXAUUDYHVSUUEYHMTUUDYHUUHXAUUDYHUUHXGAYBVTWQWAYIYJCYBYIYFYKYOY
      SWBWCVGPUUEXHIGZXIUUFOXAUUIUUDXAYTUUIUUCBXGIWDNLDXHAIQNSPXAXNCXOXAXGXOGZH
      ZXKXMUUKXKHZXMYLDARZUULYLDAUULYHHZYIXGYNGZHXKYLUUNYIUUOUUNXAYHXAUUJXKYHWE
      UULYHMTUULYHUUJUUOXAUUJXKYHWGUUJYHHXGYBJUUOUUJYHXGXBYBXGXBUOYBAWHWFXGYBCU
      QURUSWITUUKXKYHVEYIYMCYNYIYFYKYOYSWJWCWKPUULXLIGZXMUUMOUUJUUPXAXKXGXOWLWM
      DXLAIQNSVNPWNXCXRXEXQHCXBBVHWOWP $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Generated Sigma-Algebra
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c sigaGen $.
  $( Extend class notation to include the sigma-algebra generator. $)
  csigagen $a class sigaGen $.

  ${
    $d s x $.
    $( Define the sigma algebra generated by a given collection of sets as the
       intersection of all sigma algebra containing that set.  (Contributed by
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
      csiga unieq syl fveq2d sseq1 rabeqbidv inteqd adantl c0 wne cpw wa uniexg
      elex pwsiga pwuni jctir sseq2 elrab sylibr ne0i intex sylib fvmptd ) ABEZ
      DADFZCFZGZCVCHZRIZJZKZAVDGZCAHZRIZJZKZLMLMDLVINOVBDCPQVCAOZVIVNOVBVOVHVMV
      OVEVJCVGVLVOVFVKRVCASUAVCAVDUBUCUDUEABUKVBVMUFUGZVNLEVBVKUHZVMEZVPVBVQVLE
      ZAVQGZUIVRVBVSVTVBVKLEVSABUJVKLULTAUMUNVJVTCVQVLVDVQAUOUPUQVMVQURTVMUSUTV
      A $.
  $}

  ${
    $d s A $.
    $( A generated sigma algebra is a sigma algebra.  (Contributed by Thierry
       Arnoux, 27-Dec-2016.) $)
    sigagensiga $p |- ( A e. V -> ( sigaGen ` A ) e. ( sigAlgebra ` U. A ) ) $=
      ( vs wcel csigagen cfv cv wss cuni csiga crab cint sigagenval wne cpw cvv
      c0 fvex syl6eqelr sylibr intex ssrab2 a1i elpw2 insiga syl2anc eqeltrd )
      ABDZAEFZACGHZCAIZJFZKZLZULABCMZUHUMQNZUMULODZUNULDUHUNPDUPUHUNUIPUOAERSUM
      UATUHUMULHZUQURUHUJCULUBUCUMULUKJRUDTUMUKUEUFUG $.
  $}

  ${
    sgsiga.1 $e |- ( ph -> A e. V ) $.
    $( A generated sigma algebra is a sigma algebra.  (Contributed by Thierry
       Arnoux, 30-Jan-2017.) $)
    sgsiga $p |- ( ph -> ( sigaGen ` A ) e. U. ran sigAlgebra ) $=
      ( wcel csigagen cfv cuni csiga crn sigagensiga elrnsiga 3syl ) ABCEBFGZBH
      ZIGENIJHEDBCKNOLM $.
  $}

  $( The sigma algebra generated by a collection ` A ` is a sigma algebra on
     ` U. A ` .  (Contributed by Thierry Arnoux, 27-Dec-2016.) $)
  unisg $p |- ( A e. V -> U. ( sigaGen ` A ) = U. A ) $=
    ( wcel cuni csigagen cfv csiga crn wceq wa sigagensiga issgon simprd eqcomd
    sylib ) ABCZADZAEFZDZPRGHDCZQSIZPRQGFCTUAJABKRQLOMN $.

  ${
    $d j s $.
    $( A sigma algebra can be generated from any set.  (Contributed by Thierry
       Arnoux, 21-Jan-2017.) $)
    dmsigagen $p |- dom sigaGen = _V $=
      ( vj vs cvv cv wss cuni csiga cfv crab cint csigagen c0 wne wcel wrex cpw
      vex uniex pwsiga ax-mp pwuni sseq2 rspcev mp2an rabn0 mpbir intex dmmpti
      mpbi df-sigagen ) ACADZBDZEZBUKFZGHZIZJZKUPLMZUQCNURUMBUOOZUNPZUONZUKUTEZ
      USUNCNVAUKAQRUNCSTUKUAUMVBBUTUOULUTUKUBUCUDUMBUOUEUFUPUGUIABUJUH $.
  $}

  ${
    $d s A $.
    $( A set is a subset of the sigma algebra it generates.  (Contributed by
       Thierry Arnoux, 24-Jan-2017.) $)
    sssigagen $p |- ( A e. V -> A C_ ( sigaGen ` A ) ) $=
      ( vs wcel cv wss cuni cfv crab cint csigagen ssintub sigagenval syl5sseqr
      csiga ) ABDACEFCAGOHZIJAAKHCAPLABCMN $.
  $}

  $( A subset of the generating set is also a subset of the generated sigma
     algebra.  (Contributed by Thierry Arnoux, 22-Sep-2017.) $)
  sssigagen2 $p |- ( ( A e. V /\ B C_ A ) -> B C_ ( sigaGen ` A ) ) $=
    ( wcel wss wa csigagen cfv simpr sssigagen adantr sstrd ) ACDZBAEZFBAAGHZMN
    IMAOENACJKL $.

  ${
    $d s A $.
    $( Any element of set is also an element of the sigma algebra that set
       generates.  (Contributed by Thierry Arnoux, 27-Mar-2017.) $)
    elsigagen $p |- ( ( A e. V /\ B e. A ) -> B e. ( sigaGen ` A ) ) $=
      ( wcel csigagen cfv sssigagen sselda ) ACDAAEFBACGH $.
  $}

  $( Any countable union of elements of a set is also in the sigma algebra that
     set generates.  (Contributed by Thierry Arnoux, 17-Sep-2017.) $)
  elsigagen2 $p |- ( ( A e. V /\ B C_ A /\ B ~<_ om )
                                      -> U. B e. ( sigaGen ` A ) ) $=
    ( wcel wss com cdom wbr w3a csigagen cfv csiga crn cuni cpw simp1 sssigagen
    sgsiga 3syl cvv sspwb biimpi simp2 simp3 ctex elpwg mpbird sigaclcu syl3anc
    wb sseldd ) ACDZBAEZBFGHZIZAJKZLMNDBUPOZDUNBNUPDUOACULUMUNPZRUOAOZUQBUOULAU
    PEZUSUQEZURACQUTVAAUPUAUBSUOBUSDZUMULUMUNUCUOUNBTDVBUMUJULUMUNUDZBUEBATUFSU
    GUKVCBUPUHUI $.

  ${
    $d s A $.  $d s S $.
    $( The generated sigma-algebra is a subset of all sigma algebra containing
       the generating set, i.e. the generated sigma-algebra is the smallest
       sigma algebra containing the generating set, here ` B ` .  (Contributed
       by Thierry Arnoux, 4-Jun-2017.) $)
    sigagenss $p |- ( ( S e. ( sigAlgebra ` U. A ) /\ A C_ S ) ->
      ( sigaGen ` A ) C_ S ) $=
      ( vs cuni csiga cfv wcel wss wa csigagen cv crab cint cvv wceq sigagenval
      ssexg ancoms syl sseq2 intminss eqsstrd ) BADEFZGZABHZIZAJFZACKZHZCUCLMZB
      UFANGZUGUJOUEUDUKABUCQRANCPSUIUECBUCUHBATUAUB $.
  $}

  ${
    $d s A $.  $d s S $.
    $( Sufficient condition for inclusion of sigma algebra.  This is used to
       prove equality of sigma algebra.  (Contributed by Thierry Arnoux,
       10-Oct-2017.) $)
    sigagenss2 $p |- ( ( U. A = U. B /\ A C_ ( sigaGen ` B ) /\ B e. V ) ->
      ( sigaGen ` A ) C_ ( sigaGen ` B ) ) $=
      ( cuni wceq csigagen cfv wss wcel csiga sigagensiga 3ad2ant3 simp1 fveq2d
      w3a eleqtrrd simp2 sigagenss syl2anc ) ADZBDZEZABFGZHZBCIZOZUCTJGZIUDAFGU
      CHUFUCUAJGZUGUEUBUCUHIUDBCKLUFTUAJUBUDUEMNPUBUDUEQAUCRS $.
  $}

  $( The sigma-algebra generated by a sigma-algebra is itself.  (Contributed by
     Thierry Arnoux, 4-Jun-2017.) $)
  sigagenid $p |- ( S e. U. ran sigAlgebra -> ( sigaGen ` S ) = S ) $=
    ( csiga crn cuni wcel csigagen cfv wss sgon ssid sigagenss sssigagen eqssd
    sylancl ) ABCDZEZAFGZAPAADBGEAAHQAHAIAJAAKNAOLM $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     The Borel algebra on the real numbers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c BrSiga $.
  $( The Borel Algebra on real numbers, usually a gothic B $)
  cbrsiga $a class BrSiga $. $( Extend class notation with the Borel Algebra $)

  $( A Borel Algebra is defined as a sigma algebra generated by a topology.
     'The' Borel sigma algebra here refers to the sigma algebra generated by
     the topology of open intervals on real numbers.  The Borel algebra of a
     given topology ` J ` is the sigma-algebra generated by ` J ` ,
     ` ( sigaGen `` J ) ` , so there is no need to introduce a special constant
     function for Borel sigma Algebra.  (Contributed by Thierry Arnoux,
     27-Dec-2016.) $)
  df-brsiga $a |- BrSiga = ( sigaGen ` ( topGen ` ran (,) ) ) $.

  ${
    $d s x $.
    $( The Borel Algebra on real numbers is a Borel sigma algebra.
       (Contributed by Thierry Arnoux, 27-Dec-2016.) $)
    brsiga $p |- BrSiga e. ( sigaGen " Top ) $=
      ( vx vs cbrsiga cioo crn ctg csigagen ctop cima df-brsiga wcel retop wfun
      cfv cvv cv cuni csiga c0 mp2b cdm wi wss crab cint df-sigagen sigagensiga
      funmpt2 fvex elrnsiga 0elsiga elfvdm funfvima mp2an ax-mp eqeltri ) CDEZF
      NZGNZGHIZJURHKZUSUTKZLGMURGUAKZVAVBUBAOAPZBPUCBVDQRNUDUEGABUFUHUSREQKZSUS
      KVCUROKUSURQZRNKVEUQFUIUROUGUSVFUJTUSUKSURGULTHURGUMUNUOUP $.
  $}

  $( The Borel Algebra is a sigma algebra on the real numbers.  (Contributed by
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
    $( Define the product sigma-algebra operation, analogue to ~ df-tx .
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
      ( vs vt wcel csx cv cmpt2 crn csigagen cfv cvv wceq eqidd cxp mpt2eq123dv
      wa co elex id rneqd fveq2d df-sx fvex ovmpt2 syl2an fveq2i syl6eqr ) DFKZ
      EGKZUCDELUDZABDEAMBMUAZNZOZPQZCPQUODRKERKUQVASUPDFUEEGUEIJDERRABIMZJMZURN
      ZOZPQVALABDVCURNZOZPQVBDSZVEVGPVHVDVFVHABVBVCURDVCURVHUFVHVCTVHURTUBUGUHV
      CESZVGUTPVIVFUSVIABDVCURDEURVIDTVIUFVIURTUBUGUHABJIUIUTPUJUKULCUTPHUMUN
      $.
  $}

  ${
    $d x y S $.  $d x y T $.
    $( A product sigma-algebra is a sigma-algebra (Contributed by Thierry
       Arnoux, 1-Jun-2017.) $)
    sxsiga $p |- ( ( S e. U. ran sigAlgebra /\ T e. U. ran sigAlgebra ) ->
      ( S sX T ) e. U. ran sigAlgebra ) $=
      ( vx vy csiga crn cuni wcel wa csx co cv cxp cmpt2 cfv csigagen sxval cvv
      eqid syl txbasex sigagensiga eqeltrd elrnsiga ) AEFGZHBUEHIZABJKZCDABCLDL
      MNFZGZEOZHUGUEHUFUGUHPOZUJCDUHABUEUEUHSZQUFUHRHUKUJHCDUHABUEUEULUAUHRUBTU
      CUGUIUDT $.

    $( A product sigma-algebra is a sigma-algebra on the product of the bases.
       (Contributed by Thierry Arnoux, 1-Jun-2017.) $)
    sxsigon $p |- ( ( S e. U. ran sigAlgebra /\ T e. U. ran sigAlgebra ) ->
      ( S sX T ) e. ( sigAlgebra ` ( U. S X. U. T ) ) ) $=
      ( vx vy csiga crn cuni wcel wa csx co cxp wceq sxsiga cmpt2 csigagen eqid
      cfv cv cvv sxval unieqd mpt2exga rnexg unisg eqtrd txuni2 syl6reqr issgon
      3syl sylanbrc ) AEFGZHBULHIZABJKZULHAGZBGZLZUNGZMUNUQERHABNUMURCDABCSDSLZ
      OZFZGZUQUMURVAPRZGZVBUMUNVCCDVAABULULVAQZUAUBUMUTTHVATHVDVBMCDABUSULULUCU
      TTUDVATUEUJUFCDVAABUOUPVEUOQUPQUGUHUNUQUIUK $.
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
       sigma algebra.  (Contributed by Thierry Arnoux, 3-Jun-2017.) $)
    elsx $p |- ( ( ( S e. V /\ T e. W ) /\ ( A e. S /\ B e. T ) )
                                               -> ( A X. B ) e. ( S sX T ) ) $=
      ( vx vy wcel wa cxp cv cmpt2 cvv eqid syl adantr wceq wrex eqeq2d crn cfv
      csigagen csx co wss txbasex sssigagen xpeq1 xpeq2 rspc2ev mp3an3 wb xpexg
      elrnmpt2g mpbird adantl sseldd sxval eleqtrrd ) CEIDFIJZACIZBDIZJZJZABKZG
      HCDGLZHLZKZMZUAZUCUBZCDUDUEZVEVKVLVFVAVKVLUFZVDVAVKNIVNGHVKCDEFVKOZUGVKNU
      HPQVDVFVKIZVAVDVPVFVIRZHDSGCSZVBVCVFVFRZVRVFOVQVSVFAVHKZRGHABCDVGARVIVTVF
      VGAVHUITVHBRVTVFVFVHBAUJTUKULVDVFNIVPVRUMABCDUNGHCDVIVFVJNVJOUOPUPUQURVAV
      MVLRVDGHVKCDEFVOUSQUT $.
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
    $( Define a measure as a non-negative countably additive function over a
       sigma-algebra onto ` ( 0 [,] +oo ) ` (Contributed by Thierry Arnoux,
       10-Sep-2016.) $)
    df-meas $a |- measures = ( s e. U. ran sigAlgebra |->
      { m | ( m : s --> ( 0 [,] +oo ) /\ ( m ` (/) ) = 0
      /\ A. x e. ~P s ( ( x ~<_ om /\ Disj_ y e. x y )
      -> ( m ` U. x ) = sum* y e. x ( m ` y ) ) ) } ) $.

    $( The base set of a measure is a sigma-algebra.  (Contributed by Thierry
       Arnoux, 25-Dec-2016.) $)
    measbase $p |- ( M e. ( measures ` S ) -> S e. U. ran sigAlgebra ) $=
      ( vs vm vx vy cmeas cfv wcel cdm csiga crn cuni cv cc0 cpnf cicc wceq cab
      cvv elfvdm co wf c0 com cdom wbr wdisj wa cesum wi cpw wral w3a vex mapex
      ovex mp2an simp1 ss2abi ssexi df-meas dmmpti syl6eleq ) BAGHIAGJKLMZBAGUA
      CVECNZOPQUBZDNZUCZUDVHHORZENZUEUFUGFVKFNZUHUIVKMVHHVKVLVHHFUJRUKEVFULUMZU
      NZDSZGVOVIDSZVFTIVGTIVPTICUOOPQUQVFVGTTDUPURVNVIDVIVJVMUSUTVAEFDCVBVCVD
      $.

    $( The value of the ` measures ` function applied on a sigma-algebra.
       (Contributed by Thierry Arnoux, 17-Oct-2016.) $)
    measval $p |- ( S e. U. ran sigAlgebra -> ( measures ` S ) =
      { m | ( m : S --> ( 0 [,] +oo ) /\ ( m ` (/) ) = 0
      /\ A. x e. ~P S ( ( x ~<_ om /\ Disj_ y e. x y )
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
    $( The property of being a measure (Contributed by Thierry Arnoux,
       10-Sep-2016.)  (Revised by Thierry Arnoux, 19-Oct-2016.) $)
    ismeas $p |- ( S e. U. ran sigAlgebra -> ( M e. ( measures ` S ) <-> (
      M : S --> ( 0 [,] +oo ) /\ ( M ` (/) ) = 0
      /\ A. x e. ~P S ( ( x ~<_ om /\ Disj_ y e. x y )
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
    $( The property of being a measure on an undefined base sigma algebra
       (Contributed by Thierry Arnoux, 25-Dec-2016.) $)
    isrnmeas $p |- ( M e. U. ran measures
      -> ( dom M e. U. ran sigAlgebra /\ ( M : dom M --> ( 0 [,] +oo )
      /\ ( M ` (/) ) = 0 /\ A. x e. ~P dom M ( ( x ~<_ om /\ Disj_ y e. x y )
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
    $d x y M $.  $d m s x y $.
    $( The domain of a measure is a sigma algebra.  (Contributed by Thierry
       Arnoux, 19-Feb-2018.) $)
    dmmeas $p |- ( M e. U. ran measures -> dom M e. U. ran sigAlgebra ) $=
      ( vx vy cmeas crn cuni wcel cdm csiga cc0 cpnf cicc co wf c0 cfv wceq com
      cv cdom wbr wdisj wa cesum wi cpw wral w3a isrnmeas simpld ) ADEFGAHZIEFG
      UKJKLMANOAPJQBSZRTUACULCSZUBUCULFAPULUMAPCUDQUEBUKUFUGUHBCAUIUJ $.

    $( The base set of a measure is its domain.  (Contributed by Thierry
       Arnoux, 25-Dec-2016.) $)
    measbasedom $p |- ( M e. U. ran measures
                                             <-> M e. ( measures ` dom M ) ) $=
      ( vx vy vs vm cmeas crn cuni wcel cfv cc0 wf c0 wceq cv cesum wi cpw wral
      w3a cdm cpnf cicc co com wbr wdisj wa csiga isrnmeas simprd simpld ismeas
      cdom wb syl mpbird wfun cab df-meas funmpt2 elunirn2 mpan impbii ) AFGHIZ
      AAUAZFJIZVEVGVFKUBUCUDZALMAJKNBOZUEUNUFCVICOZUGUHZVIHZAJVIVJAJCPNQBVFRSTZ
      VEVFUIGHZIZVMBCAUJZUKVEVOVGVMUOVEVOVMVPULBCVFAUMUPUQFURVGVEDVNDOZVHEOZLMV
      RJKNVKVLVRJVIVJVRJCPNQBVQRSTEUSFBCEDUTVAVFAFVBVCVD $.
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

  $( A measure is a function on its base sigma algebra.  (Contributed by
     Thierry Arnoux, 13-Feb-2017.) $)
  measfn $p |- ( M e. ( measures ` S ) -> M Fn S ) $=
    ( cmeas cfv wcel cc0 cpnf cicc co wf wfn measfrge0 ffn syl ) BACDEAFGHIZBJB
    AKABLAOBMN $.

  $( The values of a measure are positive extended reals.  (Contributed by
     Thierry Arnoux, 26-Dec-2016.) $)
  measvxrge0 $p |- ( ( M e. ( measures ` S ) /\ A e. S ) ->
    ( M ` A ) e. ( 0 [,] +oo ) ) $=
    ( cmeas cfv wcel cc0 cpnf cicc co measfrge0 ffvelrnda ) CBDEFBGHIJACBCKL $.

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

  $( A measure is non negative.  (Contributed by Thierry Arnoux,
     9-Mar-2018.) $)
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
      ( A ~<_ om /\ Disj_ x e. A x ) )
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
    $d x y A $.  $d x B $.  $d x y M $.  $d x y S $.
    $( The measure the union of two complementary sets is the sum of their
       measures.  (Contributed by Thierry Arnoux, 10-Mar-2017.) $)
    measxun2 $p |- ( ( M e. ( measures ` S ) /\ ( A e. S /\ B e. S )
      /\ B C_ A ) -> ( M ` A ) = ( ( M ` B ) +e ( M ` ( A \ B ) ) ) ) $=
      ( vx cfv wcel wa wss cpr cuni co wdisj wceq syl3anc syl2anc cin fveq2d c0
      cc0 cmeas w3a cdif cv cesum cxad cpw com cdom simp1 simp2r csiga measbase
      wbr crn simp2l difelsiga prelpwi prct simp3 disjdifprg2 prcom dfss biimpi
      syl incom syl6eq preq2d syl5eqr disjeq1d biimprd mpan9 jca measvun uniprg
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

  ${
    $d x y A $.  $d x y M $.  $d y S $.
    $( The measure the union of two disjoint sets is the sum of their
       measures.  (Contributed by Thierry Arnoux, 10-Mar-2017.) $)
    measun $p |- ( ( M e. ( measures ` S ) /\ ( A e. S /\ B e. S )
      /\ ( A i^i B ) = (/) )
      -> ( M ` ( A u. B ) ) = ( ( M ` A ) +e ( M ` B ) ) ) $=
      ( cmeas cfv wcel wa c0 wceq cun cdif cxad cxr cc0 cpnf measvxrge0 syl2anc
      co sseldi cin w3a wss simp1 cuni measbase 3ad2ant1 simp2l simp2r unelsiga
      csiga crn syl3anc ssun2 a1i measxun2 syl121anc difun2 inundif uneq1 uncom
      syl6eq syl5reqr syl5eq fveq2d oveq2d 3ad2ant3 cicc iccssxr xaddcom 3eqtrd
      un0 eqtri ) DCEFGZACGZBCGZHZABUAZIJZUBZABKZDFZBDFZWABLZDFZMSZWCADFZMSZWGW
      CMSZVTVNWACGZVPBWAUCZWBWFJVNVQVSUDZVTCUKULUEGZVOVPWJVNVQWMVSCDUFUGVNVOVPV
      SUHZVNVOVPVSUIZABCUJUMWOWKVTBAUNUOWABCDUPUQVSVNWFWHJVQVSWEWGWCMVSWDADVSWD
      ABLZAABURVSAVRWPKZWPABUSVSWQIWPKZWPVRIWPUTWRWPIKWPIWPVAWPVLVMVBVCVDVEVFVG
      VTWCNGZWGNGZWHWIJVTVNVPWSWLWOVNVPHOPVHSZNWCOPVIZBCDQTRVTVNVOWTWLWNVNVOHXA
      NWGXBACDQTRWCWGVJRVK $.
  $}

  ${
    $d y z A $.  $d x y z M $.  $d x y S $.  $d y z B $.  $d z S $.
    measvunilem.1 $e |- F/_ x A $.
    $( Lemma for ~ measvuni (Contributed by Thierry Arnoux, 7-Feb-2017.)
       (Revised by Thierry Arnoux, 19-Feb-2017.)  (Revised by Thierry Arnoux,
       6-Mar-2017.) $)
    measvunilem $p |- ( ( M e. ( measures ` S ) /\
      A. x e. A B e. ( S \ { (/) } ) /\ ( A ~<_ om /\ Disj_ x e. A B ) )
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
      SEAGBCWKVIVJSWQHGBXFCXBARWKWIWMWPAWIAVRWLABVKWNWOAABLMFAMTALTVLABCVMVNVOZ
      FXACEVSWQWNBRJXLBURSWQABCDXRFWQWLABXNVPZXQVQWQAPBJZUEWIWLXFVTWAWBWCJZWIWM
      WPXTWDXSWLWIXOYAXPCDEWEWFVDXSWGWH $.
  $}

  ${
    $d y z A $.  $d x y z M $.  $d x y S $.  $d y z B $.
    measvunilem.0.1 $e |- F/_ x A $.
    $( Lemma for ~ measvuni .  (Contributed by Thierry Arnoux, 6-Mar-2017.) $)
    measvunilem0 $p |- ( ( M e. ( measures ` S ) /\
      A. x e. A B e. { (/) } /\ ( A ~<_ om /\ Disj_ x e. A B ) )
      -> ( M ` U_ x e. A B ) = sum* x e. A ( M ` B ) ) $=
      ( cfv wcel c0 com cdom wa cc0 cesum ciun cvv wceq nfcv fveq2d eqtrd cmeas
      csn wral wbr wdisj w3a simp3l ctex esum0 3syl nfv nfra1 nfbr nfdisj1 nfan
      nf3an eqidd cv simp2 r19.21bi elsni measvnul 3ad2ant1 adantr esumeq12dvaf
      syl iuneq12daf iun0 syl6eq 3eqtr4rd ) EDUAGHZCIUBHZABUCZBJKUDZABCUEZLZUFZ
      BMANZMBCEGZANABCOZEGZVQVNBPHVRMQVKVMVNVOUGBUHBAPFUIUJVQBBVSMAVKVMVPAVKAUK
      VLABULVNVOAABJKFAKRAJRUMABCUNUOUPZVQBUQZVQAURBHZLZVSIEGZMWECIEWEVLCIQVQVL
      ABVKVMVPUSUTCIVAVFZSVQWFMQZWDVKVMWHVPDEVBVCZVDTVEVQWAWFMVQVTIEVQVTABIOIVQ
      ABBCIWBFFWCWGVGABVHVISWITVJ $.
  $}

  ${
    $d x y z A $.  $d x y z M $.  $d x y S $.  $d y z B $.
    $( The measure of a countable disjoint union is the sum of the measures.
       This theorem uses a collection rather than a set of subsets of ` S ` .
       (Contributed by Thierry Arnoux, 7-Mar-2017.) $)
    measvuni $p |- ( ( M e. ( measures ` S ) /\ A. x e. A B e. S /\
      ( A ~<_ om /\ Disj_ x e. A B ) ) -> ( M ` U_ x e. A B ) =
      sum* x e. A ( M ` B ) ) $=
      ( cfv wcel wral com wa c0 crab ciun wceq adantl ralrimiva 3ad2ant1 adantr
      cesum cin cmeas cdom wbr wdisj w3a csn cdif co simp1 cv rabid simprbi wss
      cxad ssrab2 ssct mpan 3ad2ant3 simp3r nfrab1 mpsyl measvunilem0 syl112anc
      nfcv disjss1f measvunilem oveq12d cun nfra1 nfdisj1 nfan nf3an nfun simp2
      nfv rabid2 sylibr elun csiga cuni measbase 0elsiga snssi 3syl undif sylib
      wo crn eleq2d syl5bbr rabbidv eqtr4d unrab syl6eqr eqidd iuneq12df fveq2d
      iunxun fveq2i syl6eq wb elsni eleq1d mpbird syl2an sigaclcuni syl3anc syl
      eldifad iuneq2i iun0 eqtri ineq1 incom eqtr3i mp1i measun syl121anc eqtrd
      in0 esumeq1d cvv ctex inrab wn noel disjdif eleq2i mtbir elin mtbi rabeq0
      rgenw mpbir a1i cc0 cpnf cicc sylan syl2anc measvxrge0 esumsplit 3eqtr4d
      ) EDUAFGZCDGZABHZBIUBUCZABCUDZJZUEZACKUFZGZABLZCMZEFZACDUUKUGZGZABLZCMZEF
      ZUNUHZUUMCEFZASZUURUVBASZUNUHZABCMZEFZBUVBASZUUJUUOUVCUUTUVDUNUUJUUDUULAU
      UMHZUUMIUBUCZAUUMCUDZUUOUVCNUUDUUFUUIUIZUUDUUFUVIUUIUUDUULAUUMAUJZUUMGZUU
      LUUDUVNUVMBGZUULUULABUKULZOPQUUIUUDUVJUUFUUGUVJUUHUUMBUMZUUGUVJUULABUOZUU
      MBUPUQRURZUVQUUJUUHUVKUVRUUDUUFUUGUUHUSZAUUMBCUULABUTZABVDZVEVAAUUMCDEUWA
      VBVCUUJUUDUUQAUURHZUURIUBUCZAUURCUDZUUTUVDNUVLUUDUUFUWCUUIUUDUUQAUURUVMUU
      RGZUUQUUDUWFUVOUUQUUQABUKULZOZPQUUIUUDUWDUUFUUGUWDUUHUURBUMZUUGUWDUUQABUO
      ZUURBUPUQRURZUWIUUJUUHUWEUWJUVTAUURBCUUQABUTZUWBVEVAAUURCDEUWLVFVCVGUUJUV
      GUUNUUSVHZEFZUVAUUJUVGAUUMUURVHZCMZEFUWNUUJUVFUWPEUUJABUWOCCUUDUUFUUIAUUD
      AVOUUEABVIUUGUUHAUUGAVOABCVJVKVLZUWBAUUMUURUWAUWLVMUUJBUULUUQWGZABLZUWOUU
      JBUUEABLZUWSUUJUUFBUWTNUUDUUFUUIVNUUEABVPVQUUDUUFUWSUWTNUUIUUDUWRUUEABUWR
      CUUKUUPVHZGUUDUUECUUKUUPVRUUDUXADCUUDUUKDUMZUXADNUUDDVSWHVTGZKDGZUXBDEWAZ
      DWBZKDWCWDUUKDWEWFWIWJWKQWLUULUUQABWMWNZUUJCWOWPWQUWPUWMEAUUMUURCWRWSWTUU
      JUUDUUNDGZUUSDGZUUNUUSTZKNZUWNUVANUVLUUJUXCUUEAUUMHZUVJUXHUUDUUFUXCUUIUXE
      QZUUDUUFUXLUUIUUDUUEAUUMUUDUXCUULUUEUVNUXEUVPUXCUULJUUEUXDUXCUXDUULUXFRUU
      LUUEUXDXAUXCUULCKDCKXBZXCOXDXEZPQUVSUUMCDAUWAXFXGUUJUXCUUEAUURHZUWDUXIUXM
      UUDUUFUXPUUIUUDUUEAUURUUDUWFJCDUUKUWHXIPQUWKUURCDAUWLXFXGUUNKNZUXKUUJUUNA
      UUMKMKAUUMCKUVNUULCKNUVPUXNXHXJAUUMXKXLUXQUXJKUUSTZKUUNKUUSXMUUSKTUXRKUUS
      KXNUUSXTXOWTXPUUNUUSDEXQXRXSUUJUVHUWOUVBASUVEUUJBUWOUVBAUWQUXGYAUUJUUMUUR
      UVBAUWQUWAUWLUUJUVJUUMYBGUVSUUMYCXHUUJUWDUURYBGUWKUURYCXHUUMUURTZKNUUJUXS
      UULUUQJZABLZKUULUUQABYDUYAKNUXTYEZABHUYBABCUUKUUPTZGZUXTUYDCKGCYFUYCKCUUK
      DYGYHYICUUKUUPYJYKYMUXTABYLYNXLYOUUJUVNJUUDUUEUVBYPYQYRUHGZUUJUUDUVNUVLRU
      UJUUDUVNUUEUVLUXOYSCDEUUAZYTUUJUWFJZUUDUUEUYEUUJUUDUWFUVLRUYGCDUUKUWFUUQU
      UJUWGOXIUYFYTUUBXSUUC $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y M $.  $d x y S $.  $d y ph $.
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
      ( cun cfv co cle wcel cin c0 wceq cxr wbr measvxrge0 syl2anc undif1 cmeas
      cdif cxad fveq2i csiga crn cuni measbase difelsiga syl3anc disjdif eqtr3i
      syl a1i measun syl121anc syl5eqr cc0 cpnf cicc iccssxr sseldi wa inelsiga
      incom elxrge0 sylib simprd wi xraddge02 mpd uncom inundif wss inss1 inss2
      sstri ssini sseqtri ss0 ax-mp breqtrrd xleadd1a syl31anc eqbrtrd ) ABCIZE
      JZBCUCZEJZCEJZUDKZBEJZWKUDKZLAWHWICIZEJZWLWOWGEBCUAUEAEDUBJMZWIDMZCDMZWIC
      NZOPZWPWLPFADUFUGUHMZBDMZWSWRAWQXBFDEUIUNZGHBCDUJUKZHXAACWINZWTOCWIVFCBUL
      ZUMUOWICDEUPUQURAWJQMZWMQMWKQMWJWMLRWLWNLRAUSUTVAKZQWJUSUTVBZAWQWRWJXIMFX
      EWIDESTVCZAXIQWMXJAWQXCWMXIMFGBDESTVCAXIQWKXJAWQWSWKXIMFHCDESTVCAWJWJBCNZ
      EJZUDKZWMLAUSXMLRZWJXNLRZAXMQMZXOAXMXIMZXQXOVDAWQXLDMZXRFAXBXCWSXSXDGHBCD
      VEUKZXLDESTZXMVGVHVIAXHXQXOXPVJXKAXIQXMXJYAVCWJXMVKTVLAWMWIXLIZEJZXNYBBEX
      LWIIYBBXLWIVMBCVNUMUEAWQWRXSWIXLNZOPZYCXNPFXEXTYEAXLWINZYDOXLWIVFYFOVOYFO
      PYFXFOYFCWIYFXLCXLWIVPBCVQVRXLWIVQVSXGVTYFWAWBUMUOWIXLDEUPUQURWCWJWMWKWDW
      EWF $.
  $}

  ${
    $d k x y A $.  $d x y B $.  $d k n I $.  $d n y M $.  $d k n x y N $.
    $d k n y S $.  $d k n y ph $.
    measiuns.0 $e |- F/_ n B $.
    measiuns.1 $e |- ( n = k -> A = B ) $.
    measiuns.2 $e |- ( ph -> ( N = NN \/ N = ( 1 ..^ I ) ) ) $.
    measiuns.3 $e |- ( ph -> M e. ( measures ` S ) ) $.
    measiuns.4 $e |- ( ( ph /\ n e. N ) -> A e. S ) $.
    $( The measure of the union of a collection of sets, expressed as the sum
       of a disjoint set.  This is used as a lemma for both ~ measiun and
       ~ meascnbl (Contributed by Thierry Arnoux, 22-Jan-2017.)  (Proof
       shortened by Thierry Arnoux, 7-Feb-2017.) $)
    measiuns $p |- ( ph -> ( M ` U_ n e. N A )
      = sum* n e. N ( M ` ( A \ U_ k e. ( 1 ..^ n ) B ) ) ) $=
      ( cfv c1 wcel wa cn wss ciun cv cfzo co cdif cesum iundisjcnt fveq2d wral
      cmeas com cdom wbr wdisj wceq crn cuni measbase syl adantr simpll fzossnn
      csiga simpr syl5sseqr cuz simplr eleqtrd elfzouz2 fzoss2 3syl sseqtr4d wo
      mpjaodan sselda wsb sbimi sban nfv sbf clelsb3 anbi12i bitri csb wsbc cvv
      sbsbc wb vex sbcel1g ax-mp nfcv cbvcsb csbid eqtri eleq1i 3imtr3i syl2anc
      ralrimiva sigaclfu2 difelsiga syl3anc eqimss sseq1 jaoi nnct ssct sylancl
      mpbiri iundisj2cnt measvuni syl112anc eqtrd ) AFIBUAZHOFIBEPFUBZUCUDZCUAZ
      UEZUAZHOZIXRHOFUFZAXNXSHABCEFGIJKLUGUHAHDUJOQZXRDQZFIUIIUKULUMZFIXRUNXTYA
      UOMAYCFIAXOIQZRZDVCUPUQQZBDQZXQDQZYCAYGYEAYBYGMDHURUSUTZNYFYGCDQZEXPUIYIY
      JYFYKEXPYFEUBZXPQZRAYLIQZYKAYEYMVAYFXPIYLYFISUOZXPITIPGUCUDZUOZYFYORSXPIX
      OVBYFYOVDVEYFYQRZXPYPIYRXOYPQGXOVFOQXPYPTYRXOIYPAYEYQVGYFYQVDZVHXOPGVIXOP
      GVJVKYSVLAYOYQVMZYELUTVNVOYFFEVPZYHFEVPZAYNRZYKYFYHFENVQUUAAFEVPZYEFEVPZR
      UUCAYEFEVRUUDAUUEYNAFEAFVSVTEFIWAWBWCUUBFYLBWDZDQZYKUUBYHFYLWEZUUGYHFEWGY
      LWFQUUHUUGWHEWIFYLBDWFWJWKWCUUFCDUUFEYLCWDCFEYLBCEBWLJKWMECWNWOWPWCWQWRWS
      CDEXOWTWRBXQDXAXBWSAISTZSUKULUMYDAYTUUILYOUUIYQISXCYQUUIYPSTGVBIYPSXDXIXE
      USXFISXGXHABCEFGIJKLXJFIXRDHXKXLXM $.
  $}

  ${
    $d k m n y z $.  $d k n y ph $.  $d n y k S $.  $d k y z B $.  $d n y M $.
    measiun.1 $e |- ( ph -> M e. ( measures ` S ) ) $.
    measiun.2 $e |- ( ph -> A e. S ) $.
    measiun.3 $e |- ( ( ph /\ n e. NN ) -> B e. S ) $.
    measiun.4 $e |- ( ph -> A C_ U_ n e. NN B ) $.
    $( A measure is sub-additive.  (Contributed by Thierry Arnoux,
       30-Dec-2016.)  (Proof shortened by Thierry Arnoux, 7-Feb-2017.) $)
    measiun $p |- ( ph -> ( M ` A ) <_ sum* n e. NN ( M ` B ) ) $=
      ( vk cfv cn co cxr wcel measvxrge0 syl2anc wral wi vm ciun cesum cc0 cpnf
      cicc iccssxr cmeas sseldi csiga crn cuni measbase syl ralrimiva sigaclcu2
      cvv nnex cv wa adantr nfcv esumcl sylancr measssd c1 cfzo csb cle nfcsb1v
      cdif csbeq1a wceq eqidd orcd measiuns a1i nfel1 nfim eleq1 eleq1d imbi12d
      nfv imbi2d ex chvar ralrimiv wss fzossnn ssralv ax-mp sigaclfu2 difelsiga
      sylan2 syl3anc difssd esumle eqbrtrd xrletrd ) ABFLZEMCUBZFLZMCFLZEUCZAUD
      UEUFNZOWTUDUEUGZAFDUHLPZBDPWTXEPGHBDFQRUIAXEOXBXFAXGXADPZXBXEPGADUJUKULPZ
      CDPZEMSXHAXGXIGDFUMUNZAXJEMIUOCDEUPRZXADFQRUIAXEOXDXFAMUQPZXCXEPZEMSXDXEP
      URAXNEMAEUSZMPZUTZXGXJXNAXGXPGVAZICDFQRZUOMXCEUQEMVBVCVDUIABXADFGHXLJVEAX
      BMCKVFXOVGNZEKUSZCVHZUBZVKZFLZEUCXDVIACYBDKEUAUSZFMEYACVJZEYACVLZAMMVMMVF
      YFVGNVMAMVNVOGIVPAMYEXCEUQXMAURVQXQXGYDDPZYEXEPXRXQXIXJYCDPZYIAXIXPXKVAIA
      YJXPAXIYBDPZKMSZYJXKAYKKMAXPXJTZTAYAMPZYKTZTEKAYOEAEWCYNYKEEYAMEYAVBVREYB
      DYGVRVSVSXOYAVMZYMYOAYPXPYNXJYKXOYAMVTYPCYBDYHWAWBWDAXPXJIWEWFWGYLXIYKKXT
      SZYJXTMWHYLYQTXOWIYKKXTMWJWKYBDKXOWLWNRVACYCDWMWOZYDDFQRXSXQYDCDFXRYRIXQC
      YCWPVEWQWRWS $.
  $}

  ${
    $d i k l m n o p x F $.  $d i l n J $.  $d i l m n o p M $.  $d i k n S $.
    $d i k l m n o p ph $.
    meascnbl.0 $e |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) ) $.
    meascnbl.1 $e |- ( ph -> M e. ( measures ` S ) ) $.
    meascnbl.2 $e |- ( ph -> F : NN --> S ) $.
    meascnbl.3 $e |- ( ( ph /\ n e. NN ) -> ( F ` n ) C_ ( F ` ( n + 1 ) ) ) $.
    $( A measure is continuous from below.  Cf. ~ volsup .  (Contributed by
       Thierry Arnoux, 18-Jan-2017.)  (Revised by Thierry Arnoux,
       11-Jul-2017.) $)
    meascnbl $p   |- ( ph -> ( M o. F ) ( ~~>t ` J ) ( M ` U. ran F ) ) $=
      ( vi vk cn c1 cv co cfv cfzo wcel wceq vo vp vx ciun cdif cesum cmpt ccom
      cfz crn cuni clm cmeas cc0 cpnf cicc adantr csiga measbase ffvelrnda wral
      wa syl simpll fzossnn simpr syl2anc ralrimiva sigaclfu2 difelsiga syl3anc
      sseldi measvxrge0 fveq2 iuneq1d difeq12d fveq2d esumcvg2 measfrge0 fcompt
      oveq2 wf caddc nfcv cz nnzd fzval3 olcd eleq2d biimpa measiuns wfn iuninc
      ffn eqtr3d mpteq2dva eqtr4d wrex dfiun2g fnrnfv unieqd eqidd orcd 3brtr4d
      cab ) AKMNKOZUIPZCOZDQZLNXHRPZLOZDQZUDZUEZFQZCUFZUGZMXOCUFZFDUHZDUJZUKZFQ
      ZEULQAXOUAOZDQZLNYCRPZXLUDZUEZFQUBOZDQZLNYHRPZXLUDZUEZFQCUBKEUAGAXHMSZVBZ
      FBUMQSZXNBSZXOUNUOUPPZSAYOYMHUQYNBURUJUKSZXIBSZXMBSZYPAYRYMAYOYRHBFUSVCUQ
      ZAMBXHDIUTZYNYRXLBSZLXJVAYTUUAYNUUCLXJYNXKXJSZVBZAXKMSUUCAYMUUDVDUUEXJMXK
      XHVEYNUUDVFVLAMBXKDIUTVGVHXLBLXHVIVGXIXMBVJVKXNBFVMVGXHYCTZXNYGFUUFXIYDXM
      YFXHYCDVNUUFLXJYEXLXHYCNRWAVOVPVQXHYHTZXNYLFUUGXIYIXMYKXHYHDVNUUGLXJYJXLX
      HYHNRWAVOVPVQVRAXSKMXFDQZFQZUGZXQABYQFWBZMBDWBZXSUUJTAYOUUKHBFVSVCIKFDMBY
      QVTVGAKMXPUUIAXFMSZVBZCXGXIUDZFQXPUUIUUNXIXLBLCXFNWCPZFXGCXLWDZXHXKDVNZUU
      NXGNUUPRPZTZXGMTUUNXFWESUUTUUNXFAUUMVFWFNXFWGVCZWHAYOUUMHUQUUNXHXGSZVBZAY
      MYSAUUMUVBVDUVCUUSMXHUUPVEUUNUVBXHUUSSUUNXGUUSXHUVAWIWJVLUUBVGWKUUNUUOUUH
      FAKCDAUULDMWLZIMBDWNVCZJWMVQWOWPWQACMXIUDZFQYBXRAUVFYAFAUVFUCOXITCMWRUCXE
      ZUKZYAAYSCMVAUVFUVHTAYSCMUUBVHCUCMXIBWSVCAXTUVGAUVDXTUVGTUVECUCMDWTVCXAWQ
      VQAXIXLBLCUUPFMUUQUURAMMTMUUSTAMXBXCHUUBWKWOXD $.
  $}

  ${
    $d x y z A $.  $d x B $.  $d x y z S $.  $d x y z M $.
    $( Lemma for ~ measinb (Contributed by Thierry Arnoux, 2-Jun-2017.) $)
    measinblem $p |- ( ( ( ( M e. ( measures ` S ) /\ A e. S ) /\ B e. ~P S )
      /\ ( B ~<_ om /\ Disj_ x e. B x ) ) ->
      ( M ` ( U. B i^i A ) ) = sum* x e. B ( M ` ( x i^i A ) ) ) $=
      ( cmeas cfv wcel wa cpw com cdom wbr cv wdisj cuni cin ciun nfv nfan wral
      cesum iunin1 uniiun ineq1i eqtr4i fveq2i wceq simplll nfdisj1 w3a simp1ll
      csiga crn measbase simp1r elelpwi syl2anc simp1lr inelsiga syl3anc 3expia
      syl simp3 ralrimi simprl disjin ad2antll measvuni syl112anc syl5eqr ) EDF
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
      wf wi simpll csiga crn measbase ad2antrr simpr simplr eqid fmptd cr ineq1
      incom in0 eqtr3i syl6eq fveq2d adantl eqtrd adantr 0elsiga 0re a1i fvmptd
      measvnul measinblem simplll simprl sigaclcu simpllr elpwi ad2antlr sseldd
      wss esumeq2dv 3eqtr4d ex ralrimiva w3a wb ismeas mpbir3and ) DCUAGZHZBCHZ
      IZACAJZBKZDGZUBZWQHZCRUCUDUEZXDUNZSXDGRLZEJZUFUGUHZFXIFJZUIZIZXIUJZXDGZXI
      XKXDGZFUKZLZUOZECULZUMZWTACXCXFXDWTXACHZIZWRXBCHZXCXFHWRWSYBUPYCCUQURUJHZ
      YBWSYDWRYEWSYBCDUSZUTWTYBVAWRWSYBVBXABCMNXBCDOPXDVCVDWTASXCRCXDVEWTXDQWTX
      ASLZIXCSDGZRYGXCYHLWTYGXBSDYGXBSBKZSXASBVFBSKYISBSVGBVHVIVJVKVLWRYHRLWSYG
      CDVSUTVMWTYESCHWRYEWSYFVNZCVOTRVEHWTVPVQVRWTXSEXTWTXIXTHZIZXMXRYLXMIZXNBK
      ZDGZXIXKBKZDGZFUKZXOXQFBXICDVTYMAXNXCYOCXDXFYMXDQYMXAXNLZIXBYNDYSXBYNLYMX
      AXNBVFVLVKYMYEYKXJXNCHZYMWRYEWRWSYKXMWAZYFTZWTYKXMVBYLXJXLWBXICWCNZYMWRYN
      CHZYOXFHUUAYMYEYTWSUUDUUBUUCWRWSYKXMWDXNBCMNYNCDOPVRYLXQYRLXMYLXIXPYQFYLX
      KXIHZIZAXKXCYQCXDXFUUFXDQUUFXAXKLZIXBYPDUUGXBYPLUUFXAXKBVFVLVKUUFXICXKYKX
      ICWHWTUUEXICWEWFYLUUEVAWGZUUFWRYPCHZYQXFHWRWSYKUUEWAZUUFYEXKCHWSUUIUUFWRY
      EUUJYFTUUHWRWSYKUUEWDXKBCMNYPCDOPVRWIVNWJWKWLWTYEXEXGXHYAWMWNYJEFCXDWOTWP
      $.
  $}

  ${
    $d x y z A $.  $d x y z S $.  $d x y z M $.  $d x y T $.
    $( Building a measure restricted to a smaller sigma algebra.  (Contributed
       by Thierry Arnoux, 25-Dec-2016.) $)
    measres $p |- ( ( M e. ( measures ` S ) /\ T e. U. ran sigAlgebra
        /\ T C_ S ) -> ( M |` T ) e. ( measures ` T ) ) $=
      ( vx vy cmeas cfv wcel cuni wss w3a wf c0 wceq cv wa cesum 3ad2ant1 fvres
      cc0 csiga crn cpnf cicc co cres com cdom wbr wdisj wi cpw simp2 measfrge0
      wral simp3 fssres syl2anc 0elsiga 3syl measvnul eqtrd simp11 simp13 sspwb
      ssel2 sylanb measvun syl3anc simp3l sigaclcu syl sselda adantll esumeq2dv
      elpwi 3adant3 3eqtr4d 3expia ralrimiva 3jca ismeas biimprd sylc ) CAFGHZB
      UAUBIHZBAJZKZWFBTUCUDUEZCBUFZLZMWJGZTNZDOZUGUHUIZEWNEOZUJZPZWNIZWJGZWNWPW
      JGZEQZNZUKZDBULZUOZKZWJBFGHZWEWFWGUMZWHWKWMXFWHAWICLZWGWKWEWFXJWGACUNRWEW
      FWGUPAWIBCUQURWHWLMCGZTWHWFMBHWLXKNXIBUSMBCSUTWEWFXKTNWGACVARVBWHXDDXEWHW
      NXEHZWRXCWHXLWRKZWSCGZWNWPCGZEQZWTXBXMWEWNAULZHZWRXNXPNWEWFWGXLWRVCXMWGXL
      XRWEWFWGXLWRVDWHXLWRUMZWGXEXQJXLXRBAVEXEXQWNVFVGURWHXLWRUPEWNACVHVIXMWSBH
      ZWTXNNXMWFXLWOXTWHXLWFWRXIRXSWHXLWOWQVJWNBVKVIWSBCSVLWHXLXBXPNWRWHXLPZWNX
      AXOEYAWPWNHZPWPBHZXAXONXLYBYCWHXLWNBWPWNBVPVMVNWPBCSVLVOVQVRVSVTWAWFXHXGD
      EBWJWBWCWD $.
  $}

  ${
    $d x y z A $.  $d x y z S $.  $d x y z M $.
    $( Building a measure restricted to the intersection with a given set.
       (Contributed by Thierry Arnoux, 25-Dec-2016.) $)
    measinb2 $p |- ( ( M e. ( measures ` S ) /\ A e. S ) ->
      ( x e. ( S i^i ~P A ) |-> ( M ` ( x i^i A ) ) )
      e. ( measures ` ( S i^i ~P A ) ) ) $=
      ( cmeas cfv wcel wa cpw cin cv cmpt cres resmpt3 inin eqid mpteq12i eqtri
      csiga crn wss measinb measbase sigainb elrnsiga syl sylan measres syl3anc
      cuni inss1 a1i syl5eqelr ) DCEFZGZBCGZHZACBIZJZAKBJDFZLZACUTLZUSMZUSEFZVC
      ACUSJZUTLVAACUSUTNAVEUTUSUTCUROUTPQRUQVBUNGUSSTUJZGZUSCUAZVCVDGABCDUBUOCV
      FGZUPVGCDUCVIUPHUSBSFGVGBCUDUSBUEUFUGVHUQCURUKULCUSVBUHUIUM $.
  $}

  ${
    $d x y z A $.  $d x y z M $.  $d x y z S $.
    $( Division of a measure by a positive constant is a measure.  (Contributed
       by Thierry Arnoux, 25-Dec-2016.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    measdivcstOLD $p |- ( ( M e. ( measures ` S ) /\ A e. RR+ )
      -> ( x e. S |-> ( ( M ` x ) /e A ) ) e. ( measures ` S ) ) $=
      ( vy vz cfv wcel wa cc0 co cv cxdiv c0 wceq wi cvv simplr syl oveq1d cpnf
      cmeas crp cicc cmpt wf com cdom wbr wdisj cuni cesum cpw wral w3a wfn crn
      wss wfun cdm funmpt ovex rgenw dmmptg ax-mp mpbir2an a1i wrex wb vex eqid
      df-fn elrnmpt measfrge0 ffvelrn sylan adantlr xrpxdivcld eleq1a rexlimdva
      syl5bi ssrdv sylanbrc csiga measbase 0elsiga adantr jctir fvmptg measvnul
      df-f fveq2 xdiv0rp sylan9eq eqtrd simpll simprl simprr 3jca simplll simpr
      elpwg sylanb syl2anc measvxrge0 esumdivc 3ad2antr1 ad2antrr simpr1 simpr2
      ssel2 sigaclcu syl3anc fvmpt3i jca simpr3 measvun ralrimiva r19.21bi sylc
      3expia esumeq2dv 3eqtr4d ex ismeas biimprd mpd ) DCUBGZHZBUCHZIZCJUAUDKZA
      CALZDGZBMKZUEZUFZNYPGZJOZELZUGUHUIZFYTFLZUJZIZYTUKZYPGZYTUUBYPGZFULZOZPZE
      CUMZUNZUOZYPYHHZYKYQYSUULYKYPCUPZYPUQZYLURYQUUOYKUUOYPUSYPUTCOZACYOVAYOQH
      ZACUNUUQUURACYNBMVBZVCACYOQVDVEYPCVLVFVGYKEUUPYLYTUUPHZYTYOOZACVHZYKYTYLH
      ZYTQHZUUTUVBVIEVJZACYOYTYPQYPVKZVMVEYKUVAUVCACYKYMCHZIZYOYLHUVAUVCPUVHYNB
      YIUVGYNYLHZYJYICYLDUFUVGUVICDVNCYLYMDVOVPVQYIYJUVGRVRYOYLYTVSSVTWAWBCYLYP
      WKWCYKYRNDGZBMKZJYKNCHZUVKQHZIYRUVKOYKUVLUVMYIUVLYJYICWDUQUKHZUVLCDWEZCWF
      SWGUVJBMVBWHANYOUVKCQYPYMNOYNUVJBMYMNDWLTUVFWISYIYJUVKJBMKJYIUVJJBMCDWJTB
      WMWNWOYKUUJEUUKYKYTUUKHZIZUUDUUIUVQUUDIZYKUVPUUAUUCUOZUUIYKUVPUUDWPUVRUVP
      UUAUUCYKUVPUUDRUVQUUAUUCWQUVQUUAUUCWRWSYKUVSIZYTUUBDGZFULZBMKZYTUWABMKZFU
      LZUUFUUHYKUUAUVPUWCUWEOUUCUVQYTUWABFQUVDUVQUVEVGUVQUUBYTHZIZYIUUBCHZUWAYL
      HYIYJUVPUWFWTUWGUVPUWFUWHYKUVPUWFRUVQUWFXAUVPYTCURZUWFUWHUVDUVPUWIVIUVEYT
      CQXBVEYTCUUBXKXCZXDUUBCDXEXDYIYJUVPRXFXGUVTUUFUUEDGZBMKZUWCUVTUUECHZUUFUW
      LOUVTUVNUVPUUAUWMYIUVNYJUVSUVOXHYKUVPUUAUUCXIZYKUVPUUAUUCXJZYTCXLXMAUUEYO
      UWLCYPYMUUEOYNUWKBMYMUUEDWLTUVFUUSXNSUVTUWKUWBBMUVTYIUVPIUUDUWKUWBOZUVTYI
      UVPYIYJUVSWPUWNXOUVTUUAUUCUWOYKUVPUUAUUCXPXOYIUUDUWPPZEUUKYIUWQEUUKYIUVPU
      UDUWPFYTCDXQYAXRXSXTTWOUVTUVPUUHUWEOUWNUVPYTUUGUWDFUVPUWFIUWHUUGUWDOUWJAU
      UBYOUWDCYPYMUUBOYNUWABMYMUUBDWLTUVFUUSXNSYBSYCXDYDXRWSYIUUMUUNPYJYIUUNUUM
      YIUVNUUNUUMVIUVOEFCYPYESYFWGYG $.
  $}

  ${
    $d x y z A $.  $d x y z M $.  $d x y z S $.
    $( Division of a measure by a positive constant is a measure.  (Contributed
       by Thierry Arnoux, 25-Dec-2016.)  (Revised by Thierry Arnoux,
       30-Jan-2017.) $)
    measdivcst $p |- ( ( M e. ( measures ` S ) /\ A e. RR+ )
      -> ( M oFC /e A ) e. ( measures ` S ) ) $=
      ( vx vy vz cfv wcel wa cxdiv co cv wceq cc0 syl adantr eqtrd cvv oveq1d
      c0 crp cofc cmpt cdm ofcfval3 cpnf cicc wf measfrge0 fdm mpteq1d com cdom
      cmeas wbr wdisj cuni cesum wi cpw wral measvxrge0 adantlr xrpxdivcld eqid
      simplr fmptd csiga crn measbase 0elsiga ovex fveq2 fvmptg sylancl xdiv0rp
      measvnul sylan9eq w3a simpll simprl simprr 3jca vex a1i simplll wss ssel2
      sylanb adantll syl2anc esumdivc 3ad2antr1 ad2antrr simpr1 simpr2 sigaclcu
      elpw syl3anc fvmpt3i simpr3 measvun syl112anc esumeq2dv 3eqtr4d ralrimiva
      ex wb ismeas biimprd mp3and eqeltrd ) CBUNGZHZAUAHZIZCAJUBKZDBDLZCGZAJKZU
      CZXMXPXQDCUDZXTUCYADAJCXMUAUEXPDYBBXTXNYBBMZXOXNBNUFUGKZCUHYCBCUIBYDCUJOP
      UKQXPBYDYAUHZTYAGZNMZELZULUMUOZFYHFLZUPZIZYHUQZYAGZYHYJYAGZFURZMZUSZEBUTZ
      VAZYAXMHZXPDBXTYDYAXPXRBHZIXSAXNUUBXSYDHXOXRBCVBVCXNXOUUBVFVDYAVEZVGXPYFT
      CGZAJKZNXPTBHZUUERHYFUUEMXNUUFXOXNBVHVIUQHZUUFBCVJZBVKOPUUDAJVLDTXTUUEBRY
      AXRTMXSUUDAJXRTCVMSUUCVNVOXNXOUUENAJKNXNUUDNAJBCVQSAVPVRQXPYREYSXPYHYSHZI
      ZYLYQUUJYLIZXPUUIYIYKVSZYQXPUUIYLVTUUKUUIYIYKXPUUIYLVFUUJYIYKWAUUJYIYKWBW
      CXPUULIZYHYJCGZFURZAJKZYHUUNAJKZFURZYNYPXPYIUUIUUPUURMYKUUJYHUUNAFRYHRHUU
      JEWDZWEUUJYJYHHZIXNYJBHZUUNYDHXNXOUUIUUTWFUUIUUTUVAXPUUIYHBWGUUTUVAYHBUUS
      WRYHBYJWHWIZWJYJBCVBWKXNXOUUIVFWLWMUUMYNYMCGZAJKZUUPUUMYMBHZYNUVDMUUMUUGU
      UIYIUVEXNUUGXOUULUUHWNXPUUIYIYKWOZXPUUIYIYKWPZYHBWQWSDYMXTUVDBYAXRYMMXSUV
      CAJXRYMCVMSUUCXSAJVLZWTOUUMUVCUUOAJUUMXNUUIYIYKUVCUUOMXNXOUULVTUVFUVGXPUU
      IYIYKXAFYHBCXBXCSQUUMUUIYPUURMUVFUUIYHYOUUQFUUIUUTIUVAYOUUQMUVBDYJXTUUQBY
      AXRYJMXSUUNAJXRYJCVMSUUCUVHWTOXDOXEWKXGXFXNYEYGYTVSZUUAUSXOXNUUAUVIXNUUGU
      UAUVIXHUUHEFBYAXIOXJPXKXL $.
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
      syl6eq w3a simprd simp3d imim2i ralimi r19.21bi imp elpwi sseld esumeq2dv
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
    ( c1 wcel chash cpw cvol wne cfv cc0 a1i wceq syl cr 1re syl6eq cdm necon3i
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

  $( The Lebesgue measure is monotone with respect to set inclusion.
     (Contributed by Thierry Arnoux, 17-Oct-2017.) $)
  volss $p |- ( ( A e. dom vol /\ B e. dom vol /\ A C_ B )
    -> ( vol ` A ) <_ ( vol ` B ) ) $=
    ( cvol cdm wss w3a covol cfv cle cr wbr simp3 mblss 3ad2ant2 ovolss syl2anc
    wcel wceq mblvol 3ad2ant1 3brtr4d ) ACDZQZBUBQZABEZFZAGHZBGHZACHZBCHZIUFUEB
    JEZUGUHIKUCUDUELUDUCUKUEBMNABOPUCUDUIUGRUEASTUDUCUJUHRUEBSNUA $.

  ${
    $( The union of the Lebesgue measurable sets is ` RR ` .  (Contributed by
       Thierry Arnoux, 30-Jan-2017.) $)
    unidmvol $p |- U. dom vol = RR $=
      ( vx cvol cdm cuni cr wss wcel wceq cv unissb mblss mprgbir rembl unissel
      mp2an ) BCZDZEFZEPGQEHRAIZEFAPAPEJSKLMPENO $.
  $}

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
      ffvelrnda elelpwi ralrimiva fveq2 eleq1d rspcv sylc simpr disjrdx mpbird
      jca eqid voliun wfo f1ofo iunrdx uniiun syl6reqr fveq2d fvmpt2d cpnf cicc
      cc0 co volf ffvelrnd esumsup 3eqtr4d nfv eqidd esumf1o eqtr4d ) ADUAZJKZL
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
       the sum.  Cf. ~ ovoliun and ~ voliun (Contributed by Thierry Arnoux,
       16-Oct-2017.) $)
    voliune $p |- ( ( A. n e. NN A e. dom vol /\ Disj_ n e. NN A ) ->
      ( vol ` U_ n e. NN A ) = sum* n e. NN ( vol ` A ) ) $=
      ( vk cvol wcel cn wral wa cfv wceq cpnf wrex cxr cc0 syl adantlr nfcv cle
      wbr wb cdm wdisj cr ciun cesum caddc cmpt cseq crn clt csup r19.26 voliun
      c1 eqid sylanbr an32s cv nfra1 nfan cicc co simpr csb nfcsb1v nfv csbeq1a
      weq equcoms eqcomd eleq1d cbvral rspc syl5bir impcom volf ffvelrni fvmpt2
      nfel1 syl2anc ex ralrimi esumeq2d cico wf r19.21bi w3a pnfxr elicc1 mp2an
      0xr simp2bi ltpnf elico2 syl3anbrc fmptdF nfmpt1 esumfsupre eqtr3d eqtr4d
      nffv nfeq1 fveq2d eqeq1d cbvrex sylib iunmbl adantr ssiun2sf adantl volss
      0re wss syl3anc ralrimiva r19.29r breq1 biimpa reximi c0 wne 1nn r19.9rzv
      ne0i mp2b sylibr iccssxr sseldi ad2antrr mpbid cvv nfdisj1 nfre1 nnex a1i
      xgepnf 3ad2antr3 3anassrs wo wn esumpinfval rexnal orbi2i r19.29 xrge0nre
      exmid mpbir sylan orim2d mpi mpjaodan ) ADUAZEZBFGZBFAUBZHZADIZUCEZBFGZBF
      AUDZDIZFUUQBUEZJUUQKJZBFLZUUPUUSHUVAUFBFUUQUGZUNUHZUIMUJUKZUVBUUNUUSUUOUV
      AUVGJZUUNUUSHZUUMUURHBFGUUOUVHUUMUURBFULAUVFBUVEUVFUOUVEUOZUMUPUQUUNUUSUV
      BUVGJUUOUVIFBURZUVEIZBUEZUVBUVGUVIFUVLUUQBUUNUUSBUUMBFUSZUURBFUSUTZUVIUVL
      UUQJZBFUVOUVIUVKFEZUVPUUNUVQUVPUUSUUNUVQHZUVQUUQNKVAVBZEZUVPUUNUVQVCUVRUU
      MUVTUVQUUNUUMUUNBCURZAVDZUULEZCFGUVQUUMUWCUUMCBFBUWBUULBUWAAVEZVSZUUMCVFZ
      CBVHZUWBAUULUWGAUWBAUWBJBCBUWAAVGZVIVJVKZVLUWCUUMCUVKFUWFUWIVMVNVOUULUVSA
      DVPVQZOZBFUUQUVSUVEUVJVRVTPWAWBWCUVIFNKWDVBZUVEWEUVMUVGJUVIBFUUQUWLUVEUVO
      BFQZBUWLQUVIUVQHZUURNUUQRSZUUQKUJSZUUQUWLEZUVIUURBFUUNUUSVCWFZUWNUVTUWOUU
      NUVQUVTUUSUWKPUVTUUQMEZUWOUUQKRSZNMEKMEZUVTUWSUWOUWTWGTWKWHNKUUQWIWJWLOUW
      NUURUWPUWRUUQWMONUCEUXAUWQUURUWOUWPWGTXLWHNKUUQWNWJWOUVJWPBUVEBFUUQWQWROW
      SPWTUUPUVDHZUVAKUVBUXBKUVARSZUVAKJZUXBUXCCFLZUXCUXBUWBDIZKJZUXFUVARSZHZCF
      LZUXEUXBUXGCFLZUXHCFGUXJUXBUVDUXKUUPUVDVCZUVCUXGBCFUVCCVFBUXFKBUWBDBDQUWD
      XAXBBCVHZUUQUXFKUXMAUWBDUWHXCXDXEXFUXBUXHCFUUPUWAFEZUXHUVDUUNUXNUXHUUOUUN
      UXNHUWCUUTUULEZUWBUUTXMZUXHUXNUUNUWCUUMUWCBUWAFUWEUXMAUWBUULUWHVKVMVOUUNU
      XOUXNABXGZXHUXNUXPUUNBFAUWAUWBUWMBUWAQUWDUWHXIXJUWBUUTXKXNPPXOUXGUXHCFXPV
      TUXIUXCCFUXGUXHUXCUXFKUVARXQXRXSOUNFEFXTYAUXCUXETYBFUNYDUXCCFYCYEYFUXBUVA
      MEZUXCUXDTUUNUXRUUOUVDUUNUXOUXRUXQUXOUVSMUVANKYGUULUVSUUTDVPVQYHOYIUVAYPO
      YJUXBFUUQBYKUUPUVDBUUNUUOBUVNBFAYLUTUVCBFYMUTFYKEUXBYNYOUUNUUOUVDUVQUVTUU
      NUUOUVQUVTUVDUWKYQYRUXLUUAWTUUNUUSUVDYSZUUOUUNUUSUURYTZBFLZYSZUXSUYBUUSUU
      SYTZYSUUSUUFUYAUYCUUSUURBFUUBUUCUUGUUNUYAUVDUUSUUNUYAUVDUUNUYAHUUMUXTHZBF
      LUVDUUMUXTBFUUDUYDUVCBFUUMUVTUXTUVCUWJUUQUUEUUHXSOWAUUIUUJXHUUK $.
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
      clt csb nfcsb1v nfv csbeq1a equcoms eqcomd eleq1d cbvral rspc impcom volf
      syl5bir ffvelrni sylan wb 0xr pnfxr elicc1 mp2an simp2bi ltpnf 0re elico2
      syl3anbrc esumpfinvalf eqtr4d nffv nfeq1 fveq2d eqeq1d cbvrex wss adantll
      sylib finiunmbl adantr ssiun2sf adantl 3adantl3 adantlr ralrimiva r19.29r
      volss syl2anc breq1 biimpa reximi wex rexex iccssxr sseldi 3adant3 xgepnf
      19.9v mpbid nfre1 3ad2antl2 esumpinfval wo wn exmid rexnal mpbir xrge0nre
      orbi2i r19.29 ex orim2d mpi 3ad2ant2 mpjaodan ) AEFZBGUAZFZCAHZCABUBZIZBG
      JZUCFZCAHZCABUDZGJZAUUCCUEZKUUCLKZCAMZUUBUUETZUUGAUUCCUFZUUHUUKYQYSUUDTCA
      HZUUAUUGUULKYQYTUUAUUEUGZUUKYTUUEUUMYQYTUUAUUEUHZUUBUUEUIZYSUUDCAUJUKYQYT
      UUAUUEULABCUMUNUUKAUUCCCANZUUBUUECYQYTUUACCAEUUQUOYSCAUPCABUQURZUUDCAUPUS
      UUNUUKCUTZAFZTZUUDOUUCPQZUUCLVEQZUUCOLVAVBFZUUKUUDCAUUPVCZUVAUUCOLVDVBZFZ
      UVBUUKYTUUTUVGUUOYTUUTTYSUVGUUTYTYSYTCDUTZBVFZYRFZDAHUUTYSUVJYSDCACUVIYRC
      UVHBVGZUOZYSDVHZUVHUUSKZUVIBYRUVNBUVIBUVIKCDCUVHBVIZVJVKVLZVMUVJYSDUUSAUV
      MUVPVNVQVOYRUVFBGVPVRZRZVSUVGUUCSFZUVBUUCLPQZOSFLSFZUVGUVSUVBUVTIVTWAWBOL
      UUCWCWDWERUVAUUDUVCUVEUUCWFROUCFUWAUVDUUDUVBUVCIVTWGWBOLUUCWHWDWIWJWKUUBU
      UJTZUUGLUUHUWBLUUGPQZUUGLKZUWBUWCDAMZUWCUWBUVIGJZLKZUWFUUGPQZTZDAMZUWEUWB
      UWGDAMZUWHDAHUWJUWBUUJUWKUUBUUJUIZUUIUWGCDAUUIDVHCUWFLCUVIGCGNUVKWLWMUUSU
      VHKZUUCUWFLUWMBUVIGUVOWNWOWPWSUWBUWHDAUUBUVHAFZUWHUUJYQYTUWNUWHUUAYQYTTZU
      WNTUVJUUFYRFZUVIUUFWQZUWHYTUWNUVJYQUWNYTUVJYSUVJCUVHAUVLUWMBUVIYRUVOVLVNV
      OWRUWOUWPUWNABCWTZXAUWNUWQUWOCABUVHUVIUUQCUVHNUVKUVOXBXCUVIUUFXHUNXDXEXFU
      WGUWHDAXGXIUWIUWCDAUWGUWHUWCUWFLUUGPXJXKXLRUWEUWCDXMUWCUWCDAXNUWCDXSWSRUW
      BUUGSFZUWCUWDVTUUBUWSUUJYQYTUWSUUAUWOUWPUWSUWRUWPUVFSUUGOLXOYRUVFUUFGVPVR
      XPRXQXAUUGXRRXTUWBAUUCCEUUBUUJCUURUUICAYAUSYQYTUUAUUJUGUUBUUTUVGUUJYTYQUU
      TUVGUUAUVRYBXEUWLYCWKYTYQUUEUUJYDZUUAYTUUEUUDYEZCAMZYDZUWTUXCUUEUUEYEZYDU
      UEYFUXBUXDUUEUUDCAYGYJYHYTUXBUUJUUEYTUXBUUJYTUXBTYSUXATZCAMUUJYSUXACAYKUX
      EUUICAYSUVGUXAUUIUVQUUCYIVSXLRYLYMYNYOYP $.
  $}

  ${
    $d f n x y $.
    $( The Lebesgue measure is a measure.  (Contributed by Thierry Arnoux,
       16-Oct-2017.) $)
    volmeas $p |- vol e. ( measures ` dom vol ) $=
      ( vx vy vf vn cvol cfv wcel cc0 c0 wceq cv com wbr wa wral cen simpr nfan
      cn nfv cdm cmeas cpnf cicc co wf cdom wdisj cuni cesum wi volf covol 0mbl
      cpw mblvol ax-mp ovol0 eqtri cfn nfdisj1 wss elpwi sseldd ralrimi simplrr
      ad3antrrr w3a ciun uniiun fveq2i volfiniune syl5eq syl3anc wf1o bren nfcv
      ex wex fveq2 simpl a1i adantr sselda ffvelrnd esumf1o adantlr f1of adantl
      eqidd ffvelrnda ralrimiva id disjrdx biimpar syl2anc voliune f1ofo iunrdx
      syl6eqr fveq2d 3eqtr2rd exlimdv sylan2b wo brdom2 isfinite2 ensymb nnenom
      imp csdm entr mpan sylbi orim12i ad2antrl mpjaodan csiga crn wb fvssunirn
      rgen cr dmvlsiga sselii ismeas mpbir3an ) EEUAZUBFGZYHHUCUDUEZEUFZIEFZHJZ
      AKZLUGMZBYNBKZUHZNZYNUIZEFZYNYPEFZBUJZJZUKZAYHUOZOZULYLIUMFZHIYHGYLUUGJUN
      IUPUQURUSUUDAUUEYNUUEGZYRUUCUUHYRNZYNUTGZUUCSYNPMZUUIUUJNZUUJYPYHGZBYNOZY
      QUUCUUIUUJQUULUUMBYNUUIUUJBUUHYRBUUHBTYOYQBYOBTBYNYPVARRUUJBTRUULYPYNGZUU
      MUULUUONYNYHYPUUHYNYHVBZYRUUJUUOYNYHVCZVGUULUUOQVDVRVEUUHYOYQUUJVFUUJUUNY
      QVHYTBYNYPVIZEFUUBYSUUREBYNVJZVKYNYPBVLVMVNUUKUUISYNCKZVOZCVSZUUCSYNCVPUU
      IUVBUUCUUIUVAUUCCUUIUVAUUCUUIUVANZUUBSDKZUUTFZEFZDUJZDSUVEVIZEFZYTUUHUVAU
      UBUVGJYRUUHUVANZYNUUASUVFBDUUTUVEUUEUVJDTDYNVQDSVQDUUTVQYPUVEEVTUUHUVAWAU
      UHUVAQUVJUVDSGZNUVEWJUVJUUONZYHYJYPEYKUVLULWBUVJYNYHYPUUHUUPUVAUUQWCWDWEW
      FWGUVCUVEYHGZDSODSUVEUHZUVIUVGJUVCUVMDSUVCUVKNYNYHUVEUUHUUPYRUVAUVKUUQVGU
      VCSYNUVDUUTUVASYNUUTUFUUISYNUUTWHWIWKVDWLUVCUVAYQUVNUUIUVAQUUHYOYQUVAVFUV
      AUVNYQUVADBSUVEYNYPUUTUVAWMUVAYPUVEJQZWNWOWPUVEDWQWPUVAUVIYTJUUIUVAUVHYSE
      UVAUVHUURYSUVADBSUVEYNYPUUTSYNUUTWRUVOWSUUSWTXAWIXBVRXCXJXDYOUUJUUKXEZUUH
      YQYOYNLXKMZYNLPMZXEUVPYNLXFUVQUUJUVRUUKYNXGUVRLYNPMZUUKYNLXHSLPMUVSUUKXIS
      LYNXLXMXNXOXNXPXQVRYBYHXRXSUIZGYIYKYMUUFVHXTYCXRFUVTYHXRYCYAYDYEABYHEYFUQ
      YG $.
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
      ( vm va cv cdm cuni cdif cfv cc0 wceq cae df-ae relopabi ) ACZDEBCFMGHIBA
      JABKL $.
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
      ( vm va cmeas cuni wcel crab cae cdm cdif cfv cc0 wceq cvv syl cv crn wbr
      wn wb dmexg uniexg syl5eqelr rabexg wa simpr dmeqd simpl difeq12d fveq12d
      unieqd eqeq1d df-ae brabga mpancom difeq1i notrab fveq2i eqeq1i syl6bb
      eqtri ) CHUAIZJZABDKZCLUBZCMZIZVHNZCOZPQZAUCBDKZCOZPQVHRJZVGVIVNUDVGDRJVQ
      VGDVKREVGVJRJVKRJCVFUEVJRUFSUGABDRUHSFTZMZIZGTZNZVROZPQVNGFVHCLRVFWAVHQZV
      RCQZUIZWCVMPWFWBVLVRCWDWEUJZWFVTVKWAVHWFVSVJWFVRCWGUKUOWDWEULUMUNUPFGUQUR
      USVMVPPVLVOCVLDVHNVOVKDVHEUTABDVAVEVBVCVD $.
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
      ( wcel wn crab wa cfv cc0 wceq cae wbr wb a1i cle adantr syl3anc crn cuni
      cmeas cdm w3a cun wo unrab ianor rabbiia eqtr4i fveq2i eqeq1i measbasedom
      biimpi 3ad2ant1 simp2 csiga measbase syl unelsiga syl3an1 wss ssun1 simpr
      cv measssd breqtrd measle0 simp3 ssun2 jca cxad co measunl simprl oveq12d
      simprr cxr 0xr xaddid1 ax-mp syl6eq impbida syl5bbr braew anbi12d 3bitr4d
      ) DUCUAUBGZAHZCEIZDUDZGZBHZCEIZWLGZUEZABJZHZCEIZDKZLMZWKDKZLMZWODKZLMZJZW
      RCEIDNOZACEIDNOZBCEIDNOZJZXBWKWOUFZDKZLMZWQXGXMXALXLWTDXLWJWNUGZCEIWTWJWN
      CEUHWSXOCEWSXOPCVFEGABUIQUJUKULUMWQXNXGWQXNJZXDXFXPDWLUCKGZWMXCLROXDWQXQX
      NWIWMXQWPWIXQDUNUOZUPZSZWQWMXNWIWMWPUQZSXPXCXMLRWQXCXMROXNWQWKXLWLDXSYAWI
      WLURUAUBGZWMWPXLWLGZWIXQYBXRWLDUSZUTWKWOWLVAZVBZWKXLVCWQWKWOVDQVGSWQXNVEZ
      VHWKWLDVITXPXQWPXELROXFXTWQWPXNWIWMWPVJZSXPXEXMLRWQXEXMROXNWQWOXLWLDXSYHY
      FWOXLVCWQWOWKVKQVGSYGVHWOWLDVITVLWQXGJZXQYCXMLROXNWQXQXGXSSZYIYBWMWPYCYIX
      QYBYJYDUTWQWMXGYASZWQWPXGYHSZYETYIXMXCXEVMVNZLRYIWKWOWLDYJYKYLVOYIYMLLVMV
      NZLYIXCLXELVMWQXDXFVPWQXDXFVRVQLVSGYNLMVTLWAWBWCVHXLWLDVITWDWEWIWMXHXBPWP
      WRCDEFWFUPWIWMXKXGPWPWIXIXDXJXFACDEFWFBCDEFWFWGUPWH $.
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
      eleq2d opabbidv df-fae cxp ovex xpex opabssxp ssexi ovmpt2a ) FGBEUAUBUCH
      CIZFIZJZGIZJZHZKLZMZDIZVIMZNZAIZVCOZVNVKOZVDPZAVHQZVFRPZNZCDSVCBJZEJZHZKL
      ZMZVKWDMZNZVOVPBPZAWCQZERPZNZCDSZUDVDBTZVFETZNZVTWKCDWOVMWGVSWJWOVJWEVLWF
      WOVIWDVCWOVEWAVHWCKWOVDBWMWNUEZUFWOVGWBWOVFEWMWNUGZUFUHZUIZUNWOVIWDVKWSUN
      UJWOVRWIVFERWOVQWHAVHWCWRWOVDBVOVPWPUKULWQUMUJUOACDGFUPWLWDWDUQWDWDWAWCKU
      RZWTUSWJCDWDWDUTVAVB $.
  $}

  ${
    $d f g x M $.  $d f g x R $.
    $( The 'almost everywhere' builder for functions produces relations.
       (Contributed by Thierry Arnoux, 22-Oct-2017.) $)
    relfae $p |- ( ( R e. _V /\ M e. U. ran measures ) -> Rel ( R ~ae M ) ) $=
      ( vf vg vx cvv wcel cmeas crn cuni wa cfae co wrel cdm cmap cfv wbr crab
      cv cae copab relopab faeval releqd mpbiri ) AFGBHIJGKZABLMZNCTZAOBOJZPMZG
      DTZUKGKETZUIQUMULQAREUJSBUARKZCDUBZNUNCDUCUGUHUOEACDBUDUEUF $.
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
      eqid cmeas crn faeval breqd oveq1i syl6eleqr jca biantrurd 3bitr4d ) AEFM
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
       measurable spaces are given using their sigma algebra ` s ` and ` t ` ,
       and the spaces themselves are recovered by ` U. s ` and ` U. t ` .

       Note the similarities between the definition of measurable functions in
       measure theory, and of continuous functions in topology.

       This is the definition for the generic measure theory.  For the specific
       case of functions from ` RR ` to ` CC ` , see ~ df-mbf (Contributed by
       Thierry Arnoux, 23-Jan-2017.) $)
    df-mbfm $a |- MblFnM = ( s e. U. ran sigAlgebra , t e. U. ran sigAlgebra
      |-> { f e. ( U. t ^m U. s ) | A. x e. t ( `' f " x ) e. s } ) $.
  $}

  ${
    $d f x F $.  $d f s t x S $.  $d f s t x T $.
    ismbfm.1 $e |- ( ph -> S e. U. ran sigAlgebra ) $.
    ismbfm.2 $e |- ( ph -> T e. U. ran sigAlgebra ) $.
    $( The predicate " ` F ` is a measurable function from the measurable space
       ` S ` to the measurable space ` T ` ".  Cf. ~ ismbf (Contributed by
       Thierry Arnoux, 23-Jan-2017.) $)
    ismbfm $p |- ( ph -> ( F e. ( S MblFnM T ) <->
            ( F e. ( U. T ^m U. S ) /\ A. x e. T ( `' F " x ) e. S ) ) ) $=
      ( vf vs vt cmbfm co wcel cv ccnv wral cuni cmap crab wceq csiga crn unieq
      cima wa oveq2d eleq2 ralbidv rabeqbidv oveq1d raleq df-mbfm rabex syl2anc
      ovex ovmpt2 eleq2d cnveq imaeq1d eleq1d elrab syl6bb ) AECDKLZMEHNZOZBNZU
      DZCMZBDPZHDQZCQZRLZSZMEVLMEOZVFUDZCMZBDPZUEAVCVMEACUAUBQZMDVRMVCVMTFGIJCD
      VRVRVGINZMZBJNZPZHWAQZVSQZRLZSVMKVHBWAPZHWCVKRLZSVSCTZWBWFHWEWGWHWDVKWCRV
      SCUCUFWHVTVHBWAVSCVGUGUHUIWADTZWFVIHWGVLWIWCVJVKRWADUCUJVHBWADUKUIBJHIULV
      IHVLVJVKRUOUMUPUNUQVIVQHEVLVDETZVHVPBDWJVGVOCWJVEVNVFVDEURUSUTUHVAVB $.
  $}

  ${
    $d x f $.  $d a s t F $.  $d f s t $.  $d s t x F $.
    $( The property of being a measurable function (Contributed by Thierry
       Arnoux, 23-Jan-2017.) $)
    elunirnmbfm $p |- ( F e. U. ran MblFnM <->
        E. s e. U. ran sigAlgebra E. t e. U. ran sigAlgebra
        ( F e. ( U. t ^m U. s ) /\ A. x e. t ( `' F " x ) e. s ) ) $=
      ( va vf cmbfm crn cuni wcel cv co csiga wrex cmap ccnv cima wral wa cfv
      cdm cxp wfun wb crab df-mbfm mpt2fun elunirn ax-mp ovex dmmpt2 rexeqi cop
      rabex fveq2 df-ov syl6eqr eleq2d rexxp 3bitri simpl simpr ismbfm 2rexbiia
      wceq bitri ) CGHIJZCDKZBKZGLZJZBMHIZNDVLNZCVIIZVHIZOLZJCPAKZQVHJAVIRSZBVL
      NDVLNVGCEKZGTZJZEGUAZNZWAEVLVLUBZNVMGUCVGWCUDDBVLVLFKPVQQVHJAVIRZFVPUEZGA
      BFDUFZUGECGUHUIWAEWBWDDBVLVLWFGWGWEFVPVNVOOUJUNUKULWAVKEDBVLVLVSVHVIUMZVE
      ZVTVJCWIVTWHGTVJVSWHGUOVHVIGUPUQURUSUTVKVRDBVLVLVHVLJZVIVLJZSAVHVICWJWKVA
      WJWKVBVCVDVF $.
  $}

  ${
    $d s t x F $.
    mbfmfun.1 $e |- ( ph -> F e. U. ran MblFnM ) $.
    $( A measurable function is a function.  (Contributed by Thierry Arnoux,
       24-Jan-2017.) $)
    mbfmfun $p |- ( ph -> Fun F ) $=
      ( vt vs vx cmbfm cuni wcel cv cmap co ccnv cima wral csiga wrex rexlimivw
      crn wa wfun elunirnmbfm biimpi wf elmapi ffun syl adantr 3syl ) ABGSHIZBD
      JZHZEJZHZKLIZBMFJNUMIFUKOZTZDPSHZQZEURQZBUAZCUJUTFDBEUBUCUSVAEURUQVADURUO
      VAUPUOUNULBUDVABULUNUEUNULBUFUGUHRRUI $.
  $}

  ${
    $d a s t x F $.  $d s t x S $.  $d t x T $.
    mbfmf.1 $e |- ( ph -> S e. U. ran sigAlgebra ) $.
    mbfmf.2 $e |- ( ph -> T e. U. ran sigAlgebra ) $.
    mbfmf.3 $e |- ( ph -> F e. ( S MblFnM T ) ) $.
    $( A measurable function as a function with domain and codomain
       (Contributed by Thierry Arnoux, 25-Jan-2017.) $)
    mbfmf $p |- ( ph -> F : U. S --> U. T ) $=
      ( vx cuni cmap co wcel wf ccnv cv cima wral cmbfm wa ismbfm simpld elmapi
      mpbid syl ) ADCIZBIZJKLZUFUEDMAUGDNHOPBLHCQZADBCRKLUGUHSGAHBCDEFTUCUADUEU
      FUBUD $.

    $( The predicate to be a measurable function (Contributed by Thierry
       Arnoux, 30-Jan-2017.) $)
    isanmbfm $p |- ( ph -> F e. U. ran MblFnM ) $=
      ( vt vs vx cv cuni cmap co wcel wral wa crn wrex cmbfm csiga ismbfm mpbid
      ccnv cima wceq unieq oveq2d eleq2d ralbidv anbi12d oveq1d rspc2ev syl3anc
      eleq2 raleq elunirnmbfm sylibr ) ADHKZLZIKZLZMNZOZDUDJKUEZVAOZJUSPZQZHUAR
      LZSIVISZDTRLOABVIOCVIODCLZBLZMNZOZVEBOZJCPZQZVJEFADBCTNOVQGAJBCDEFUBUCVHV
      QDUTVLMNZOZVOJUSPZQIHBCVIVIVABUFZVDVSVGVTWAVCVRDWAVBVLUTMVABUGUHUIWAVFVOJ
      USVABVEUOUJUKUSCUFZVSVNVTVPWBVRVMDWBUTVKVLMUSCUGULUIVOJUSCUPUKUMUNJHDIUQU
      R $.

    $d x A $.
    mbfmcnvima.4 $e |- ( ph -> A e. T ) $.
    $( The preimage by a measurable function is a measurable set.  (Contributed
       by Thierry Arnoux, 23-Jan-2017.) $)
    mbfmcnvima $p |- ( ph -> ( `' F " A ) e. S ) $=
      ( vx wcel ccnv cv cima wral cuni cmap co cmbfm wa ismbfm mpbid wceq rspcv
      simprd imaeq2 eleq1d sylc ) ABDKELZJMZNZCKZJDOZUIBNZCKZIAEDPCPQRKZUMAECDS
      RKUPUMTHAJCDEFGUAUBUEULUOJBDUJBUCUKUNCUJBUIUFUGUDUH $.
  $}

  ${
    mbfmbfm.1 $e |- ( ph -> M e. U. ran measures ) $.
    mbfmbfm.2 $e |- ( ph -> J e. Top ) $.
    mbfmbfm.3 $e |- ( ph -> F e. ( dom M MblFnM ( sigaGen ` J ) ) ) $.
    $( A measurable function to a Borel Set is measurable.  (Contributed by
       Thierry Arnoux, 24-Jan-2017.) $)
    mbfmbfm $p |- ( ph -> F e. U. ran MblFnM ) $=
      ( cdm csigagen cfv cmeas cuni wcel csiga measbasedom biimpi measbase 3syl
      crn ctop sgsiga isanmbfm ) ADHZCIJBADKSLMZDUCKJMZUCNSLMEUDUEDOPUCDQRACTFU
      AGUB $.
  $}

  ${
    $d x A $.  $d y F $.  $d x y S $.  $d x y T $.  $d x y ph $.
    mbfmcst.1 $e |- ( ph -> S e. U. ran sigAlgebra ) $.
    mbfmcst.2 $e |- ( ph -> T e. U. ran sigAlgebra ) $.
    mbfmcst.3 $e |- ( ph -> F = ( x e. U. S |-> A ) ) $.
    mbfmcst.4 $e |- ( ph -> A e. U. T ) $.
    $( A constant function is measurable.  Cf. ~ mbfconst (Contributed by
       Thierry Arnoux, 26-Jan-2017.) $)
    mbfmcst $p |- ( ph -> F e. ( S MblFnM T ) ) $=
      ( vy wcel cuni ccnv cima adantr syl c0 cxp cdm cmbfm co cmap cv wf fmpt3d
      wral wb csiga crn unielsiga elmapg syl2anc mpbird cmpt csn wceq fconstmpt
      cin wa cres cnveqi cnvxp eqtr3i imaeq1i df-ima df-rn 3eqtri cvv inxp inv1
      df-res xpeq2i dmeqi xpeq2 xp0 syl6eq dmeqd dm0 adantl 0elsiga eqeltrd wne
      syl5eqel dmxp pm2.61dane ralrimivw cnveqd imaeq1d eleq1d ismbfm mpbir2and
      ralbidv ) AFDEUAUBLFEMZDMZUCUBLZFNZKUDZOZDLZKEUGZAWPWOWNFUEZABWOCWNFIACWN
      LBUDWOLJPUFAWNELZWODLZWPXBUHAEUIUJMZLXCHEUKQADXELZXDGDUKQZWNWOFEDULUMUNAX
      ABWOCUOZNZWROZDLZKEUGAXKKEAXKCUPZWRUSZRAXMRUQZUTZXJWOXMSZTZDXJXLWOSZWRVAZ
      NZTZXMWOSZNZTXQXJXRWROXSUJYAXIXRWRWOXLSZNXIXRYDXHBWOCURVBWOXLVCVDVEXRWRVF
      XSVGVHXTYCXSYBXSXRWRVISUSXMWOVIUSZSYBXRWRVLXLWOWRVIVJYEWOXMWOVKVMVHVBVNYC
      XPXMWOVCVNVHZXOXQRDXNXQRUQAXNXQRTRXNXPRXNXPWORSRXMRWOVOWOVPVQVRVSVQVTARDL
      ZXNAXFYGGDWAQPWBWDAXMRWCZUTZXJXQDYFYIXQWODYHXQWOUQAWOXMWEVTAXDYHXGPWBWDWF
      WGAWTXKKEAWSXJDAWQXIWRAFXHIWHWIWJWMUNAKDEFGHWKWL $.
  $}

  ${
    $d a z S $.  $d a z T $.  $d a z ph $.
    1stmbfm.1 $e |- ( ph -> S e. U. ran sigAlgebra ) $.
    1stmbfm.2 $e |- ( ph -> T e. U. ran sigAlgebra ) $.
    $( The first projection map is measurable with regard to the product sigma
       algebra.  (Contributed by Thierry Arnoux, 3-Jun-2017.) $)
    1stmbfm $p |- ( ph -> ( 1st |` ( U. S X. U. T ) )
                                               e. ( ( S sX T ) MblFnM S ) ) $=
      ( va vz c1st cuni co wcel csiga wceq syl2anc wb syl wa wss cfv adantr cxp
      cres csx cmbfm cmap ccnv cv cima wral f1stres sxuni feq2d mpbii unielsiga
      wf crn sxsiga elmapg mpbird cpw sgon sigasspw pwssb biimpi r19.21bi xpss1
      4syl sseld pm4.71rd wfn ffn elpreima mp2b fvres eleq1d c2nd 1st2nd2 xp2nd
      cop elxp6 anass an32 3bitr2i baib pm5.32i bitri syl6rbbr eqrdv simpr eqid
      bitr4d issgon biimpri sylancl baselsiga syl22anc eqeltrd ralrimiva ismbfm
      elsx mpbir2and ) AHBIZCIZUAZUBZBCUCJZBUDJKXEXBXFIZUEJKZXEUFFUGZUHZXFKZFBU
      IAXHXGXBXEUOZAXDXBXEUOZXLXBXCUJZAXDXGXBXEABLUPIZKZCXOKZXDXGMDEBCUKNULUMAX
      BBKZXGXFKZXHXLOAXPXRDBUNPAXFXOKZXSAXPXQXTDEBCUQNZXFUNPXBXGXEBXFURNUSAXKFB
      AXIBKZQZXJXIXCUAZXFYCGXJYDYCGUGZYDKZYEXDKZYFQZYEXJKZYCYFYGYCYDXDYEYCXIXBR
      ZYDXDRAYJFBAXPBXBLSKBXBUTRZYJFBUIZDBVAXBBVBYKYLFBXBVCVDVGVEXIXBXCVFPVHVIY
      IYGYEXESZXIKZQZYHXMXEXDVJYIYOOXNXDXBXEVKXDYEXIXEVLVMYGYNYFYGYNYEHSZXIKZYF
      YGYMYPXIYEXDHVNVOYGYEYPYEVPSZVSMZYRXCKZYFYQOYEXBXCVQYEXBXCVRYFYSYTQZYQYFY
      SYQYTQQYSYQQYTQUUAYQQYEXIXCVTYSYQYTWAYSYQYTWBWCWDNWKWEWFWGWHYCXPXQYBXCCKZ
      YDXFKAXPYBDTAXQYBETAYBWIAUUBYBACXCLSKZUUBAXQXCXCMZUUCEXCWJUUCXQUUDQCXCWLW
      MWNXCCWOPTXIXCBCXOXOWTWPWQWRAFXFBXEYADWSXA $.

    $( The second projection map is measurable with regard to the product sigma
       algebra (Contributed by Thierry Arnoux, 3-Jun-2017.) $)
    2ndmbfm $p |- ( ph -> ( 2nd |` ( U. S X. U. T ) )
                                                e. ( ( S sX T ) MblFnM T ) ) $=
      ( va vz c2nd cuni co wcel csiga wceq syl2anc wb syl wa wss cfv adantr cxp
      cres csx cmbfm cmap ccnv cv cima wral f2ndres sxuni feq2d mpbii unielsiga
      wf crn sxsiga elmapg mpbird cpw sgon sigasspw pwssb biimpi r19.21bi xpss2
      4syl sseld pm4.71rd wfn ffn elpreima mp2b fvres eleq1d c1st 1st2nd2 xp1st
      cop elxp6 anass bitr4i bitr4d pm5.32i bitri syl6rbbr eqrdv issgon biimpri
      baib eqid sylancl baselsiga simpr elsx eqeltrd ralrimiva ismbfm mpbir2and
      syl22anc ) AHBIZCIZUAZUBZBCUCJZCUDJKXDXBXEIZUEJKZXDUFFUGZUHZXEKZFCUIAXGXF
      XBXDUOZAXCXBXDUOZXKXAXBUJZAXCXFXBXDABLUPIZKZCXNKZXCXFMDEBCUKNULUMAXBCKZXF
      XEKZXGXKOAXPXQECUNPAXEXNKZXRAXOXPXSDEBCUQNZXEUNPXBXFXDCXEURNUSAXJFCAXHCKZ
      QZXIXAXHUAZXEYBGXIYCYBGUGZYCKZYDXCKZYEQZYDXIKZYBYEYFYBYCXCYDYBXHXBRZYCXCR
      AYIFCAXPCXBLSKCXBUTRZYIFCUIZECVAXBCVBYJYKFCXBVCVDVGVEXHXBXAVFPVHVIYHYFYDX
      DSZXHKZQZYGXLXDXCVJYHYNOXMXCXBXDVKXCYDXHXDVLVMYFYMYEYFYMYDHSZXHKZYEYFYLYO
      XHYDXCHVNVOYFYDYDVPSZYOVSMZYQXAKZYEYPOYDXAXBVQYDXAXBVRYEYRYSQZYPYEYRYSYPQ
      QYTYPQYDXAXHVTYRYSYPWAWBWJNWCWDWEWFWGYBXOXPXABKZYAYCXEKAXOYADTAXPYAETAUUA
      YAABXALSKZUUAAXOXAXAMZUUBDXAWKUUBXOUUCQBXAWHWIWLXABWMPTAYAWNXAXHBCXNXNWOW
      TWPWQAFXECXDXTEWRWS $.
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
      cv sseqtr4d sseldd mbfmcnvima ralrimiva jca cmap unielsiga simprl biimpar
      elmapg syl21anc crab cpw cdif com wbr wi w3a simpl ssrab2 pwuni sstri a1i
      cdom fimacnv ad2antrl imaeq2 eleq1d elrab elrabi adantl difelsiga syl3anc
      sylanbrc wfun simplrl ffun difpreima 3syl difeq1d simprbi ad3antrrr sspwb
      mpbi ad2antlr sigaclcu ciun simpllr simpld unipreima elelpwi syl2anc nfcv
      sseli sigaclcuni ex 3jca rabexg issiga syl12anc unieqd unisg eqtrd fveq2d
      eleq2d mpbid simprr ssrab sigagenss eqsstrd eqssd rabid2 ismbfm mpbir2and
      wb sylib impbida ) ADBCUAUBLZBMZCMZDUCZDUDZFUQZNZBLZFEOZPZAYOPZYRUUCUUEBC
      DABUEUFMZLZYOHQACUUFLZYOACEUGUHZUUFIAEUIGUJUKZQAYOULUMUUEUUBFEUUEYTELZPZY
      TBCDAUUGYOUUKHUNAUUHYOUUKUUJUNAYOUUKUOUULECYTAECRZYOUUKAEUUICAEUILZEUUIRG
      EUIUPSIURZUNUUEUUKULUSUTVAVBAUUDPZYODYQYPVCUBLZUUBFCOZUUPYQCLZYPBLZYRUUQA
      UUSUUDAUUHUUSUUJCVDZSQZAUUTUUDAUUGUUTHBVDZSQZAYRUUCVEUUSUUTPUUQYRYQYPDCBV
      GVFVHUUPCUUBFCVIZTUURUUPCUVEUUPCUUIUVEACUUITUUDIQUUPUVEEMZUEUHZLZEUVERZUU
      IUVERUUPUVEYQUEUHZLZUVHUUPAUVEYQVJZRZYQUVELZYQJUQZVKZUVELZJUVEOZUVOVLWAVM
      ZUVOMZUVELZVNZJUVEVJZOZVOZUVKAUUDVPUVMUUPUVECUVLUUBFCVQZCVRVSVTUUPUVNUVRU
      WDUUPUUSYSYQNZBLZUVNUVBUUPUWGYPBYRUWGYPTAUUCYPYQDWBWCZUVDUKUUBUWHFYQCYTYQ
      TUUAUWGBYTYQYSWDWEWFWKUUPUVQJUVEUUPUVOUVELZPZUVPCLZYSUVPNZBLZUVQUWKUUHUUS
      UVOCLZUWLAUUHUUDUWJUUJUNZUWKUUHUUSUWPUVASUWJUWOUUPUUBFUVOCWGWHYQUVOCWIWJU
      WKUWMUWGYSUVONZVKZBUWKYRDWLZUWMUWRTAYRUUCUWJWMYPYQDWNZYQUVODWOWPUWKUWRYPU
      WQVKZBUUPUWRUXATUWJUUPUWGYPUWQUWIWQQUWKUUGUUTUWQBLZUXABLAUUGUUDUWJHUNZUWK
      UUGUUTUXCUVCSUWJUXBUUPUWJUWOUXBUUBUXBFUVOCYTUVOTUUAUWQBYTUVOYSWDWEWFWRWHY
      PUWQBWIWJUKUKUUBUWNFUVPCYTUVPTUUAUWMBYTUVPYSWDWEWFWKVAUUPUWBJUWCUUPUVOUWC
      LZPZUVSUWAUXEUVSPZUVTCLZYSUVTNZBLZUWAUXFUUHUVOCVJZLZUVSUXGAUUHUUDUXDUVSUU
      JWSUXDUXKUUPUVSUWCUXJUVOUVECRZUWCUXJRUWFUVECWTXAXKXBUXEUVSULZUVOCXCWJUXFU
      XHKUVOYSKUQZNZXDZBUXFYRUWSUXHUXPTUXFYRUUCAUUDUXDUVSXEXFUWTKUVODXGWPUXFUUG
      UXOBLZKUVOOUVSUXPBLAUUGUUDUXDUVSHWSUXFUXQKUVOUXFUXNUVOLZPZUXNUVELZUXQUXSU
      XRUXDUXTUXFUXRULUUPUXDUVSUXRXEUXNUVOUVEXHXIUXTUXNCLUXQUUBUXQFUXNCYTUXNTUU
      AUXOBYTUXNYSWDWEWFWRSVAUXMUVOUXOBKKUVOXJXLWJUKUUBUXIFUVTCYTUVTTUUAUXHBYTU
      VTYSWDWEWFWKXMVAXNAUVKUVMUWEPZAUUHUVEUILUVKUYAYLUUJUUBFCUUFXOJUVEYQXPWPVF
      XQAUVKUVHYLUUDAUVJUVGUVEAYQUVFUEAYQUUIMZUVFACUUIIXRAUUNUYBUVFTGEUIXSSXTYA
      YBQYCUUPUUMUUCUVIAUUMUUDUUOQAYRUUCYDUUBFCEYEWKEUVEYFXIYGUXLUUPUWFVTYHUUBF
      CYIYMUUPFBCDAUUGUUDHQAUUHUUDUUJQYJYKYN $.
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
      cv wa sseqtr4d adantr cnima sylan sseldd ralrimiva elex csiga sigagensiga
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
      $( The composition of two measurable functions is measurable.  ( cf.
         ~ cnmpt11 ) (Contributed by Thierry Arnoux, 4-Jun-2017.) $)
      mbfmco $p |- ( ph -> ( G o. F ) e. ( R MblFnM T ) ) $=
        ( va cmbfm co wcel cuni ccnv cima wf adantr ccom cmap cv wral mbfmf fco
        syl2anc wb csiga crn unielsiga syl elmapg mpbird wa cnvco imaeq1i imaco
        eqtri simpr mbfmcnvima syl5eqel ralrimiva ismbfm mpbir2and ) AFEUAZBDMN
        OVFDPZBPZUBNOZVFQZLUCZRZBOZLDUDAVIVHVGVFSZACPZVGFSVHVOESVNACDFHIKUEABCE
        GHJUEVHVOVGFEUFUGAVGDOZVHBOZVIVNUHADUIUJPZOZVPIDUKULABVROZVQGBUKULVGVHV
        FDBUMUGUNAVMLDAVKDOZUOZVLEQZFQZVKRZRZBVLWCWDUAZVKRWFVJWGVKFEUPUQWCWDVKU
        RUSWBWEBCEAVTWAGTACVROWAHTZAEBCMNOWAJTWBVKCDFWHAVSWAITAFCDMNOWAKTAWAUTV
        AVAVBVCALBDVFGIVDVE $.
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
        ( vc va vb wcel cuni 3ad2ant1 csx co cmbfm wf ccnv cv cima cxp crn wral
        cmpt2 cfv cop mbfmf ffvelrnda opelxpi syl2anc wceq csiga adantr eleqtrd
        sxuni fmptd wrex eqid vex xpex elrnmpt2 w3a simp3 imaeq2d simp2l simp2r
        wa simp1 cin xppreima2 simp2 mbfmcnvima inelsiga syl3anc eqeltrd 3expia
        rexlimdvva imp sylan2b ralrimiva cvv txbasex csigagen imambfm mpbir2and
        sxval ) AHCDEUAUBZUCUBRCSZWNSZHUDHUEZOUFZUGZCRZOPQDEPUFZQUFZUHZUKZUIZUJ
        ABWOBUFZFULZXFGULZUMZWPHAXFWORZVNZXIDSZESZUHZWPXKXGXLRXHXMRXIXNRAWOXLXF
        FACDFIJLUNZUOAWOXMXFGACEGIKMUNZUOXGXHXLXMUPUQAXNWPURZXJADUSUISZRZEXRRZX
        QJKDEVBUQUTVANVCAWTOXEWRXERAWRXCURZQEVDPDVDZWTPQDEXCWRXDXDVEXAXBPVFQVFV
        GVHAYBWTAYAWTPQDEAXADRZXBERZVNZYAWTAYEYAVIZWSWQXCUGZCYFWRXCWQAYEYAVJVKY
        FAYCYDYGCRAYEYAVOAYCYDYAVLAYCYDYAVMAYCYDVIZYGFUEXAUGZGUEXBUGZVPZCAYCYGY
        KURYDABWOXLXMFGHXAXBXOXPNVQTYHCXRRZYICRYJCRYKCRAYCYLYDITZYHXACDFYMAYCXS
        YDJTAYCFCDUCUBRYDLTAYCYDVRVSYHXBCEGYMAYCXTYDKTAYCGCEUCUBRYDMTAYCYDVJVSY
        IYJCVTWAWBWAWBWCWDWEWFWGACWNHXEOAXSXTXEWHRJKPQXEDEXRXRXEVEZWIUQIAXSXTWN
        XEWJULURJKPQXEDEXRXRYNWMUQWKWL $.
    $}
  $}

  ${
    $( Measurable functions with respect to the Lebesgue measure are
       real-valued functions on the real numbers.  (Contributed by Thierry
       Arnoux, 27-Mar-2017.) $)
    mbfmvolf $p |- ( F e. ( dom vol MblFnM BrSiga ) -> F : RR --> RR ) $=
      ( cvol cdm cbrsiga cmbfm co wcel cuni wf cr csiga crn wceq wa issgon mpbi
      cfv simpli a1i simpri dmvlsiga brsigarn id mbfmf feq23i sylibr ) ABCZDEFG
      ZUGHZDHZAIJJAIUHUGDAUGKLHZGZUHULJUIMZUGJKQZGULUMNUAUGJOPZRSDUKGZUHUPJUJMZ
      DUNGUPUQNUBDJOPZRSUHUCUDJJUIUJAULUMUOTUPUQURTUEUF $.
  $}

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
      cv ctg retop sssigagen sstri df-brsiga sseqtr4i wceq wa dmvlsiga brsigarn
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
      cfv cvv syl6bi cpw ccnv cima wral crn pwsiga syl brsigarn mp1i ismbfm wfn
      cmbfm wb reex eqeltri unipw elex syl5eqel elmapg sylancr feq2i syl6bb ffn
      wss elpreima simpl ssrdv cnvex imaexg ax-mp elpw sylibr ralrimivw pm4.71d
      vex syl6 bitr4d eqrdv oveq12i syl6eq ) ABFZAUAZGULHZGIZWBIZJHZKAJHWACWCWF
      WACLZWCFWGWFFZWGUBZDLZUCZWBFZDGUDZMWHWADWBGWGWAWBANRFWBNUEIZFABUFWBAOUGGK
      NRFGWNFWAUHGKOUIUJWAWHWMWAWHWGAUKZWMWAWHAWDWGPZWOWAWHWEWDWGPZWPWAWDSFWESF
      WHWQUMWDKSQUNUOWAWEASAUPZABUQURWDWEWGSSUSUTWEAWDWGWRVAVBAWDWGVCTWOWLDGWOW
      KAVDWLWOEWKAWOELZWKFWSAFZWSWGRWJFZMWTAWSWJWGVEWTXAVFTVGWKAWISFWKSFWGCVOVH
      WIWJSVIVJVKVLVMVPVNVQVRWDKWEAJQWRVSVT $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
              Borel Algebra on ` ( RR X. RR ) `
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y $.
    $( The base set for the generator of the Borel sigma algebra on
       ` ( RR X. RR ) ` is indeed ` ( RR X. RR ) ` .  (Contributed by Thierry
       Arnoux, 22-Sep-2017.) $)
    br2base $p |- U. ran ( x e. BrSiga , y e. BrSiga |-> ( x X. y ) )
       = ( RR X. RR ) $=
      ( cbrsiga cv cxp crn cr cpw cuni wceq wcel wral brsigasspwrn sseli elpwid
      wss vex eqid ax-mp wrex wa xpss12 syl2an xpex elpw sylibr rgen2a rnmpt2ss
      cmpt2 unibrsiga csiga cfv brsigarn elrnsiga unielsiga mp2b eqeltrri xpeq1
      wb eqeq2d xpeq2 rspc2ev mp3an elrnmpt2 mpbir elpwuni mpbi ) ABCCADZBDZEZU
      IZFZGGEZHZPZVLIVMJZVJVNKZBCLACLVOVQABCVHCKZVICKZUAVJVMPZVQVRVHGPVIGPVTVSV
      RVHGCGHZVHMNOVSVIGCWAVIMNOVHGVIGUBUCVJVMVHVIAQBQUDZUEUFUGABCCVJVNVKVKRZUH
      SVMVLKZVOVPUSWDVMVJJZBCTACTZGCKZWGVMVMJZWFCIZGCUJCGUKULKCUKFIKWICKUMCGUNC
      UOUPUQZWJVMRWEWHVMGVIEZJABGGCCVHGJVJWKVMVHGVIURUTVIGJWKVMVMVIGGVAUTVBVCAB
      CCVJVMVKWCWBVDVEVLVMVFSVG $.
  $}

  ${
    $( An upper bound for a dyadic number.  (Contributed by Thierry Arnoux,
       19-Sep-2017.) $)
    dya2ub $p |- ( R e. RR+ ->
      ( 1 / ( 2 ^ ( |_ ` ( 1 - ( 2 logb R ) ) ) ) ) < R ) $=
      ( crp wcel c1 c2 clogb co cmin cfl cfv clt cneg caddc cr cz rnlogbcl wceq
      wbr a1i syl2anc cexp cdiv cuz 2z uzid ax-mp renegcld flltp1 syl 1z fladdz
      mpan sylancl cc recnd ax-1cn negsubdi negsubdi2 eqtr3d fveq2d breqtrd 2rp
      wa wb resubcld flcld rpexpcld rpreccld id logblt syl3anc breq1d ltnegcon1
      1re logbrec 3bitrd nnlogbexp breq2d bitrd mpbird ) ABCZDEDEAFGZHGZIJZUAGZ
      UBGZAKRZWBLZWDKRZWAWHWHIJDMGZWDKWAWHNCZWHWJKRWAWBEEUCJCZWAWBNCZEOCWLUDEUE
      UFZEAPULZUGZWHUHUIWAWHDMGZIJZWJWDWAWKDOCWRWJQWPUJWHDUKUMWAWQWCIWAWBUNCZDU
      NCZWQWCQWAWBWOUOUPWSWTVCWBDHGLWQWCWBDUQWBDURUSUMUTUSVAWAWGWHEWEFGZKRZWIWA
      WGEWFFGZWBKRZXALZWBKRZXBWAWLWFBCWAWGXDVDWLWAWNSZWAWEWAEWDEBCWAVBSWAWCWADW
      BDNCWAVNSWOVEVFZVGZVHWAVIEWFAVJVKWAXCXEWBKWAWLWEBCZXCXEQXGXIWEEVOTVLWAXAN
      CZWMXFXBVDWAWLXJXKXGXIEWEPTWOXAWBVMTVPWAXAWDWHKWAWLWDOCXAWDQXGXHEWDVQTVRV
      SVT $.
  $}

  ${
    $d e f z $.
    $( The closed half-spaces of ` ( RR X. RR ) ` cover ` ( RR X. RR ) ` .
       (Contributed by Thierry Arnoux, 11-Oct-2017.) $)
    sxbrsigalem0 $p |- U. ( ran ( e e. RR |-> ( ( e [,) +oo ) X. RR ) )
      u. ran ( f e. RR |-> ( RR X. ( f [,) +oo ) ) ) ) = ( RR X. RR ) $=
      ( vz cr cv cpnf cico co cxp cmpt cuni wss wcel pnfxr syl ovex reex cfv wa
      xpex crn cun unissb wo elun cpw eqid rnmptss cxr icossre mpan2 xpss1 elpw
      sylibr mprg sseli elpwid xpss2 jaoi mprgbir wfun c1st funmpt cvv c2nd clt
      sylbi wbr rexr a1i ltpnf lbico1 syl3anc anim1i anim2i elxp7 3imtr4i xp1st
      wceq oveq1 xpeq1d fvmpt eleqtrrd elunirn2 sylancr ssriv ssun3 ax-mp uniun
      sseqtr4i eqssi ) ADAEZFGHZDIZJZUAZBDDBEZFGHZIZJZUAZUBZKZDDIZXCXDLCEZXDLZC
      XBCXBXDUCXEXBMXEWPMZXEXAMZUDXFXEWPXAUEXGXFXHXGXEXDWPXDUFZXEWNXIMZWPXILADA
      DWNXIWOWOUGZUHWLDMZWNXDLZXJXLWMDLZXMXLFUIMZXNNWLFUJUKWMDDULOWNXDWMDWLFGPQ
      TUMUNUOUPUQXHXEXDXAXIXEWSXIMZXAXILBDBDWSXIWTWTUGUHWQDMZWSXDLZXPXQWRDLZXRX
      QXOXSNWQFUJUKWRDDUROWSXDDWRQWQFGPTUMUNUOUPUQUSVGUTXDWPKZXAKZUBZXCXDXTLXDY
      BLCXDXTXEXDMZWOVAXEXEVBRZWORZMXEXTMADWNVCYCXEYDFGHZDIZYEXEVDVDIMZYDDMZXEV
      ERDMZSZSYHYDYFMZYJSZSYCXEYGMYKYMYHYIYLYJYIYDUIMXOYDFVFVHYLYDVIXOYINVJYDVK
      YDFVLVMVNVOXEDDVPXEYFDVPVQYCYIYEYGVSXEDDVRAYDWNYGDWOWLYDVSWMYFDWLYDFGVTWA
      XKYFDYDFGPQTWBOWCYDXEWOWDWEWFXDXTYAWGWHWPXAWIWJWK $.
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
        fnmpti xpeq1d fvmpt icopnfcld fveq2i syl6eleqr cdif dif0 ax-mp eqeltrri
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
        $d m n u v x $.  $d m u N $.  $d m u X $.
        $( The function ` I ` returns closed below opened above dyadic rational
           intervals covering the the real line.  This is the same construction
           as in ~ dyadmbl .  (Contributed by Thierry Arnoux, 24-Sep-2017.) $)
        dya2iocival $p |- ( ( N e. ZZ /\ X e. ZZ ) -> ( X I N ) =
          ( ( X / ( 2 ^ N ) ) [,) ( ( X + 1 ) / ( 2 ^ N ) ) ) ) $=
          ( vu vm cz co c2 cexp cdiv c1 caddc cico wceq cv oveq1 oveq1d oveq12d
          wcel oveq2 oveq2d cmpt2 cbvmpt2v eqtr4i ovex ovmpt2 ancoms ) FKUDEKUD
          FECLFMENLZOLZFPQLZUMOLZRLZSIJFEKKITZMJTZNLZOLZURPQLZUTOLZRLZUQCFUTOLZ
          UOUTOLZRLURFSZVAVEVCVFRURFUTOUAVGVBUOUTOURFPQUAUBUCUSESZVEUNVFUPRVHUT
          UMFOUSEMNUEZUFVHUTUMUOOVIUFUCCABKKATZMBTZNLZOLZVJPQLZVLOLZRLZUGIJKKVD
          UGHIJABKKVDVPVJUTOLZVNUTOLZRLURVJSZVAVQVCVRRURVJUTOUAVSVBVNUTOURVJPQU
          AUBUCUSVKSZVQVMVRVORVTUTVLVJOUSVKMNUEZUFVTUTVLVNOWAUFUCUHUIUNUPRUJUKU
          L $.
      $}

      $( Dyadic intervals are subsets of ` RR ` .  (Contributed by Thierry
         Arnoux, 18-Sep-2017.) $)
      dya2iocress $p |- ( ( N e. ZZ /\ X e. ZZ ) -> ( X I N ) C_ RR ) $=
        ( cz wcel wa co c2 cexp cdiv c1 caddc cr a1i rerpdivcld dya2iocival cxr
        cico wss simpr zred crp 2rp simpl rpexpcld 1re readdcld icossre syl2anc
        rexrd eqsstrd ) EIJZFIJZKZFECLFMENLZOLZFPQLZUTOLZUCLZRABCDEFGHUAUSVARJV
        CUBJVDRUDUSFUTUSFUQURUEUFZUSMEMUGJUSUHSUQURUIUJZTUSVCUSVBUTUSFPVEPRJUSU
        KSULVFTUOVAVCUMUNUP $.

      $( Dyadic intervals are Borel sets of ` RR ` .  (Contributed by Thierry
         Arnoux, 22-Sep-2017.) $)
      dya2iocbrsiga $p |- ( ( N e. ZZ /\ X e. ZZ ) -> ( X I N ) e. BrSiga ) $=
        ( wcel co c2 c1 cbrsiga cmnf cioo cxr a1i cr cfv ctop cz cexp cdiv cico
        caddc dya2iocival cdif clt wbr wceq mnfxr simpr zred crp simpl rpexpcld
        wa 2rp rerpdivcld rexrd 1re readdcld mnflt syl difioo syl31anc crn cuni
        csiga brsigarn elrnsiga ax-mp ctg csigagen iooretop elsigagen df-brsiga
        retop mp2an eleqtrri difelsiga mp3an syl6eqelr eqeltrd ) EUAIZFUAIZUQZF
        ECJFKEUBJZUCJZFLUEJZWHUCJZUDJZMABCDEFGHUFWGWLNWKOJZNWIOJZUGZMWGNPIZWIPI
        WKPINWIUHUIZWOWLUJWPWGUKQWGWIWGFWHWGFWEWFULUMZWGKEKUNIWGURQWEWFUOUPZUSZ
        UTWGWKWGWJWHWGFLWRLRIWGVAQVBWSUSUTWGWIRIWQWTWIVCVDNWIWKVEVFMVIVGVHIZWMM
        IWNMIWOMIMRVISIXAVJMRVKVLWMOVGVMSZVNSZMXBTIZWMXBIWMXCIVRNWKVOXBWMTVPVSV
        QVTWNXCMXDWNXBIWNXCIVRNWIVOXBWNTVPVSVQVTWMWNMWAWBWCWD $.

      ${
        $d d n x $.  $d d I $.
        $( Dyadic intervals are Borel sets of ` RR ` .  (Contributed by Thierry
           Arnoux, 22-Sep-2017.)  (Revised by Thierry Arnoux, 13-Oct-2017.) $)
        dya2icobrsiga $p |- ran I C_ BrSiga $=
          ( crn cbrsiga cv wcel c2 co c1 cz cmnf cioo cxr a1i cr cfv cexp caddc
          vd cdiv cico wceq wrex ovex elrnmpt2 wa simpr cdif clt wbr mnfxr zred
          simpl crp 2rp rpexpcld rerpdivcld rexrd 1re readdcld mnflt syl difioo
          syl31anc csiga cuni brsigarn elrnsiga ctg csigagen iooretop elsigagen
          ax-mp retop mp2an df-brsiga eleqtrri difelsiga mp3an syl6eqelr adantr
          ctop eqeltrd ex rexlimivv sylbi ssriv ) UCCGZHUCIZWLJWMAIZKBIZUALZUDL
          ZWNMUBLZWPUDLZUELZUFZBNUGANUGWMHJZABNNWTWMCFWQWSUEUHUIXAXBABNNWNNJZWO
          NJZUJZXAXBXEXAUJWMWTHXEXAUKXEWTHJXAXEWTOWSPLZOWQPLZULZHXEOQJZWQQJWSQJ
          OWQUMUNZXHWTUFXIXEUORXEWQXEWNWPXEWNXCXDUQUPZXEKWOKURJXEUSRXCXDUKUTZVA
          ZVBXEWSXEWRWPXEWNMXKMSJXEVCRVDXLVAVBXEWQSJXJXMWQVEVFOWQWSVGVHHVIGVJJZ
          XFHJXGHJXHHJHSVITJXNVKHSVLVQXFPGVMTZVNTZHXOWFJZXFXOJXFXPJVROWSVOXOXFW
          FVPVSVTWAXGXPHXQXGXOJXGXPJVROWQVOXOXGWFVPVSVTWAXFXGHWBWCWDWEWGWHWIWJW
          K $.
      $}

      $d x I $.
      ${
        $d n x $.  $d b D $.  $d b u x G $.  $d b u I $.  $d b u x N $.
        $d b u x X $.
        dya2icoseg.1 $e |- N = ( |_ ` ( 1 - ( 2 logb D ) ) ) $.
        $( For any point and any closed below, opened above interval of ` RR `
           centered on that point, there is a closed below opened above dyadic
           rational interval which contains that point and is included in the
           original interval.  (Contributed by Thierry Arnoux, 19-Sep-2017.) $)
        dya2icoseg $p |- ( ( X e. RR /\ D e. RR+ ) -> E. b e. ran I
          ( X e. b /\ b C_ ( ( X - D ) (,) ( X + D ) ) ) ) $=
          ( wcel c2 co cmin caddc cz cdiv c1 wbr crp cexp cmul cfl cfv crn cioo
          cr wa wss cv wrex cxp wfn cico fnmpt2i a1i simpl 2rp clogb 1re cuz 2z
          ovex uzid ax-mp rnlogbcl mpan resubcld flcld syl5eqel rpexpcl sylancr
          rpred adantl remulcld fnovrn syl3anc cle clt zred fllelt syl lediv1dd
          simpld recnd cc 2cn cc0 2ne0 expne0d divcan4d breqtrd readdcld simprd
          wne ltdiv1dd eqbrtrrd cxr w3a redivcld rexrd elico2 syl2anc mpbir3and
          wb wceq dya2iocival eleqtrrd rereccld oveq2i dya2ub syl5eqbr ltsub2dd
          simpr mulcld ax-1cn divsubdird oveq1d eqtrd ltsub1dd ltletrd leadd1dd
          pncand ltled divdird ltadd2dd lelttrd icossioo syl22anc eqsstrd eleq2
          sseq1 anbi12d rspcev syl12anc ) GUHLZBUALZUIZGMFUBNZUCNZUDUEZFDNZDUFZ
          LZGUUCLZUUCGBONZGBPNZUGNZUJZGHUKZLZUUKUUIUJZUIZHUUDULYSDQQUMUNZUUBQLZ
          FQLZUUEUUOYSACQQAUKZMCUKUBNZRNZUURSPNUUSRNZUONDJUUTUVAUOVDUPUQYSUUAYS
          GYTYQYRURZYRYTUHLZYQYRMUALZUUQUVCUSYRFSMBUTNZONZUDUEZQKYRUVFYRSUVESUH
          LZYRVAUQMMVBUELZYRUVEUHLMQLUVIVCMVEVFMBVGVHVIVJVKZUVDUUQUIYTMFVLZVNVM
          VOZVPZVJZYRUUQYQUVJVOZQQUUBFDVQVRYSGUUBYTRNZUUBSPNZYTRNZUONZUUCYSGUVS
          LZYQUVPGVSTZGUVRVTTZUVBYSUVPUUAYTRNZGVSYSUUBUUAYTYSUUBUVNWAZUVMYSUVDU
          UQYTUALUSUVOUVKVMZYSUUBUUAVSTZUUAUVQVTTZYSUUAUHLUWFUWGUIUVMUUAWBWCZWE
          ZWDYSGYTYSGUVBWFZYSYTUVLWFZYSMFMWGLYSWHUQMWIWPYSWJUQUVOWKZWLZWMYSUWCG
          UVRVTUWMYSUUAUVQYTUVMYSUUBSUWDUVHYSVAUQZWNZUWEYSUWFUWGUWHWOZWQWRYSUVP
          UHLUVRWSLUVTYQUWAUWBWTXFYSUUBYTUWDUVLUWLXAZYSUVRYSUVQYTUWOUVLUWLXAZXB
          UVPUVRGXCXDXEYSUUQUUPUUCUVSXGUVOUVNACDEFUUBIJXHXDZXIYSUUCUVSUUIUWSYSU
          UGWSLUUHWSLUUGUVPVTTUVRUUHVSTUVSUUIUJYSUUGYSGBUVBYSBYQYRXOVNZVIZXBYSU
          UHYSGBUVBUWTWNZXBYSUUGGSYTRNZONZUVPUXAYSGUXCUVBYSYTUVLUWLXJZVIUWQYSUX
          CBGUXEUWTUVBYSUXCSMUVGUBNZRNZBVTYTUXFSRFUVGMUBKXKXKYRUXGBVTTYQBXLVOXM
          ZXNYSUUASONZYTRNZUXDUVPVSYSUXJUWCUXCONUXDYSUUASYTYSGYTUWJUWKXPZSWGLYS
          XQUQZUWKUWLXRYSUWCGUXCOUWMXSXTYSUXIUUBYTYSUUASUVMUWNVIZUWDUWEYSUXIUUB
          UXMUWDYSUXIUVQSONUUBVTYSUUAUVQSUVMUWOUWNUWPYAYSUUBSYSUUBUWDWFUXLYDWMY
          EWDWRYBYSUVRUUHUWRUXBYSUVRGUXCPNZUUHUWRYSGUXCUVBUXEWNUXBYSUVRUUASPNZY
          TRNZUXNVSYSUVQUXOYTUWOYSUUASUVMUWNWNUWEYSUUBUUASUWDUVMUWNUWIYCWDYSUXP
          UWCUXCPNUXNYSUUASYTUXKUXLUWKUWLYFYSUWCGUXCPUWMXSXTWMYSUXCBGUXEUWTUVBU
          XHYGYHYEUUGUUHUVPUVRYIYJYKUUNUUFUUJUIHUUCUUDUUKUUCXGUULUUFUUMUUJUUKUU
          CGYLUUKUUCUUIYMYNYOYP $.
      $}

      ${
        $d a b n x w $.  $d a b d x E $.  $d b d I $.  $d b d x X $.
        $( For any point and any opened interval of ` RR ` containing that
           point, there is a closed below opened above dyadic rational interval
           which contains that point and is included in the original interval.
           (Contributed by Thierry Arnoux, 12-Oct-2017.) $)
        dya2icoseg2 $p |- ( ( X e. RR /\ E e. ran (,) /\ X e. E ) ->
          E. b e. ran I ( X e. b /\ b C_ E ) ) $=
          ( vd cr wcel co wss wa wrex crp cfv eqid cvv cioo crn cmin caddc wral
          w3a cv c1 c2 cfl dya2icoseg ralrimiva 3ad2ant1 cabs ccom cxp cres cbl
          clogb simp3 ctg iooex rnex bastg ax-mp simp2 sseldi syl6eleqr cxmt wb
          rexmet ccnfld cress cxme cmopn wceq cnfldxms reex ressxms mp2an ctopn
          tgioo3 eqtri rebase cds cnfldds reseq1i xmstopn elmopn2 simprbi oveq1
          ressds syl sseq1d rexbidv rspcva syl2anc bl2ioo sylan2 rexbidva mpbid
          rpre r19.29 r19.41v sstr anim2i anassrs reximi sylbir rexlimivw ) FKL
          ZCUAUBZLZFCLZUFZFGUGZLZXPFJUGZUCMFXRUDMUAMZNZOZGDUBZPZXSCNZOZJQPZXQXP
          CNZOZGYBPZXOYCJQUEZYDJQPZYFXKXMYJXNXKYCJQAXRBDEUHUIXRUSMUCMUJRZFGHIYL
          SUKULUMXOFXRUNUCUOZKKUPZUQZURRZMZCNZJQPZYKXOXNAUGZXRYPMZCNZJQPZACUEZY
          SXKXMXNUTXOCELZUUDXOCXLVARZEXOXLUUFCXLTLXLUUFNUAVBVCXLTVDVEXKXMXNVFVG
          HVHUUECKNZUUDYOKVIRLUUEUUGUUDOVJYOYOSZVKAJCYOEKVLKVMMZVNLZEYOVORVPVLV
          NLKTLZUUJVQVRKVLTVSVTYOEUUIKEUUFUUIWARZHUULUULSWBWCUUIUUISZWDYMUUIWER
          ZYNUUKYMUUNVPVRKYMVLUUITUUMWFWLVEWGWHVEWIVEWJWMUUCYSAFCYTFVPZUUBYRJQU
          UOUUAYQCYTFXRYPWKWNWOWPWQXKXMYSYKVJXNXKYRYDJQXRQLXKXRKLZYRYDVJXRXBXKU
          UPOYQXSCFXRYOUUHWRWNWSWTUMXAYCYDJQXCWQYEYIJQYEYAYDOZGYBPYIYAYDGYBXDUU
          QYHGYBXQXTYDYHXTYDOYGXQXPXSCXEXFXGXHXIXJWM $.
      $}

      $d u v I $.
      dya2ioc.2 $e |- R = ( u e. ran I , v e. ran I |-> ( u X. v ) ) $.
      $( The function returning dyadic square covering for a given size has
         domain ` ( ran I X. ran I ) ` .  (Contributed by Thierry Arnoux,
         19-Sep-2017.) $)
      dya2iocrfn $p |- R Fn ( ran I X. ran I ) $=
        ( crn cv cxp vex xpex fnmpt2i ) CBFKZQCLZBLZMDJRSCNBNOP $.

      $( The dyadic rectangle set is countable.  (Contributed by Thierry
         Arnoux, 18-Sep-2017.)  (Revised by Thierry Arnoux, 11-Oct-2017.) $)
      dya2iocct $p |- ran R ~<_ om $=
        ( crn com cdom wbr cz cv co cn mp2an cvv c2 cexp cdiv c1 caddc cico cen
        cmpt2 znnen nnct endomtr wcel ovex rgen2w mpt2cti eqbrtri rnct ax-mp wa
        cxp vex xpex breq1i biimpri 3syl ) FKZLMNZVGDKLMNZFLMNVGFAEOOAPZUAEPUBQ
        ZUCQZVIUDUEQVJUCQZUFQZUHZLMIOLMNZVOVNLMNORUGNRLMNVOUIUJORLUKSZVPAEOOVMT
        VMTULAEOOVKVLUFUMUNUOSUPFUQURZVQVGVGUSCBVFVFCPZBPZUTZUHZLMNZDLMNZVHCBVF
        VFVTTVTTULCBVFVFVRVSCVABVAVBUNUOWCWBDWALMJVCVDDUQVES $.

      $(
        $d m n x y $. $d m I $. $d m x y N $. $d x y V $.
        @( The value of a dyadic square cover of ` ( RR X. RR ) ` .
           (Contributed by Thierry Arnoux, 24-Sep-2017.) @)
        dya2iocrrnval $p |- ( W e. ran R <-> E. x e. ZZ E. y e. ZZ
          E. m e. ZZ E. n e. ZZ W = ( ( x I n ) X. ( y I m ) ) ) $=
          ( vm cz wcel cv co cxp cmpt2 oveq2d nfcv cfv crn wceq wrex mpt2eq3dva
          w3a simp1 xpeq12d rneqd cmpt c2 cexp cdiv c1 cico nfmpt22 nfcxfr nfov
          caddc nfxp nfmpt2 nfrn cbvmpt eqtr4i zex mpt2ex rnex eleq2d eqid ovex
          fvmpt xpex elrnmpt2 syl6bb ) GMNZHGCUAZNHABMMAOZGEPZBOZGEPZQZRZUBZNHW
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
        $( For any point of an opened rectangle in ` ( RR X. RR ) ` , there is
           a closed below opened above dyadic rational square which contains
           that point and is included in the rectangle.  (Contributed by
           Thierry Arnoux, 12-Oct-2017.) $)
        dya2iocnrect $p |- ( ( X e. ( RR X. RR ) /\ A e. B /\ X e. A ) ->
          E. b e. ran R ( X e. b /\ b C_ A ) ) $=
          ( wcel wrex wa vs vt cr cxp w3a cv wceq cioo crn wss cmpt2 eleq2i vex
          eqid xpex elrnmpt2 bitri biimpi 3ad2ant2 simp1 simp3 r19.41vv biimpri
          jca32 simprl simpl simprr eleqtrd 3jca c1st c2nd simpr xp1st 3ad2ant1
          cfv adantl simpll 3ad2ant3 dya2icoseg2 syl3anc simplr reeanv sylanbrc
          xp2nd xpeq1 eqeq2d xpeq2 rspc2ev mp3an3 sylibr ad2antrl simpl1 sseldi
          cvv xpss simprrl simpld simprrr syl12anc simprd xpss12 syl2anc simpl2
          elxp7 sseqtr4d eleq2 sseq1 anbi12d rspcev exp32 rexlimdvv sylc sylan2
          ex rexlimivv 3syl ) LUCUCUDZRZDERZLDRZUEZDGUFZHUFZUDZUGZHUHUIZSGYFSZX
          RXTTZTZYEYHTZHYFSGYFSZLMUFZRZYLDUJZTZMFUIZSZYAYGXRXTXSXRYGXTXSYGXSDGH
          YFYFYDUKZUIZRYGEYSDQULGHYFYFYDDYRYRUNYBYCGUMHUMUOUPUQURUSXRXSXTUTXRXS
          XTVAVDYKYIYEYHGHYFYFVBVCYJYQGHYFYFYBYFRZYCYFRZTZYJYQYJUUBXRYELYDRZUEZ
          YQYJXRYEUUCYEXRXTVEYEYHVFZYJLDYDYEXRXTVGUUEVHVIUUBUUDTZUUDLVJVOZUAUFZ
          RZUUHYBUJZTZLVKVOZUBUFZRZUUMYCUJZTZTZUBJUIZSUAUURSZYQUUBUUDVLUUFUUKUA
          UURSZUUPUBUURSZUUSUUFUUGUCRZYTUUGYBRZUUTUUDUVBUUBXRYEUVBUUCLUCUCVMVNV
          PYTUUAUUDVQUUDUVCUUBUUCXRUVCYELYBYCVMVRVPAIYBJKUUGUANOVSVTUUFUULUCRZU
          UAUULYCRZUVAUUDUVDUUBXRYEUVDUUCLUCUCWDVNVPYTUUAUUDWAUUDUVEUUBUUCXRUVE
          YELYBYCWDVRVPAIYCJKUULUBNOVSVTUUKUUPUAUBUURUURWBWCUUDUUQYQUAUBUURUURU
          UDUUHUURRZUUMUURRZTZUUQYQUUDUVHUUQTZTZUUHUUMUDZYPRZLUVKRZUVKDUJZYQUVH
          UVLUUDUUQUVHUVKCUFZBUFZUDZUGZBUURSCUURSZUVLUVFUVGUVKUVKUGZUVSUVKUNUVR
          UVTUVKUUHUVPUDZUGCBUUHUUMUURUURUVOUUHUGUVQUWAUVKUVOUUHUVPWEWFUVPUUMUG
          UWAUVKUVKUVPUUMUUHWGWFWHWICBUURUURUVQUVKFPUVOUVPCUMBUMUOUPWJWKUVJLWNW
          NUDZRZUUIUUNUVMUVJXQUWBLUCUCWOXRYEUUCUVIWLWMUVJUUIUUJUUDUVHUUKUUPWPZW
          QUVJUUNUUOUUDUVHUUKUUPWRZWQUVMUWCUUIUUNTTLUUHUUMXDVCWSUVJUVKYDDUVJUUJ
          UUOUVKYDUJUVJUUIUUJUWDWTUVJUUNUUOUWEWTUUHYBUUMYCXAXBXRYEUUCUVIXCXEYOU
          VMUVNTMUVKYPYLUVKUGYMUVMYNUVNYLUVKLXFYLUVKDXGXHXIWSXJXKXLXMXNXOXP $.
      $}

      ${
        $d b e f m u v x $.  $d b e r A $.  $d x I $.  $d e J $.
        $d b e f r R $.  $d b e f r x X $.
        $( For any point of an open set of the usual topology on
           ` ( RR X. RR ) ` there is a closed below opened above dyadic
           rational square which contains that point and is entirely in the
           open set.  (Contributed by Thierry Arnoux, 21-Sep-2017.) $)
        dya2iocnei $p |- ( ( A e. ( J tX J ) /\ X e. A ) ->
          E. b e. ran R ( X e. b /\ b C_ A ) ) $=
          ( vr ve vf wcel wa cr cv ctx co cxp wss cioo cmpt2 wrex elunii ancoms
          crn cuni tpr2uni syl6eleq cmul caddc eqid tpr2rico anass dya2iocnrect
          ci 3expb anim1i anasss sylan2br r19.41v simpll simplr simpr sstrd jca
          reximi sylbir syl rexlimdvaa sylc ) DHHUAUBZQZIDQZRZISSUCZQZINTZQZWBD
          UDZRZNOPUEUJZWFOTPTUCUFUJZUGIJTZQZWHDUDZRZJEUJZUGZVSIVPUKZVTVRVQIWNQI
          DVPUHUIHKULUMOPBCDWGCBSSCTUTBTUNUBUOUBUFZHINKWOUPWGUPZUQWAWEWMNWGWAWB
          WGQZWERZRWIWHWBUDZRZJWLUGZWDRZWMWRWAWQWCRZWDRXBWQWCWDURWAXCWDXBWAXCRX
          AWDWAWQWCXAABCWBWGEOPFGHIJKLMWPUSVAVBVCVDXBWTWDRZJWLUGWMWTWDJWLVEXDWK
          JWLXDWIWJWIWSWDVFXDWHWBDWIWSWDVGWTWDVHVIVJVKVLVMVNVO $.
      $}

      ${
        $d m p x $.  $d b c m p u v z A $.  $d m J $.  $d b c m p R $.
        $d b m z $.
        $( Every open set of ` ( RR X. RR ) ` is a union of closed below opened
           above dyadic rational rectangular subsets of ` ( RR X. RR ) ` .
           This union must be a countable union by ~ dya2iocct .  (Contributed
           by Thierry Arnoux, 18-Sep-2017.) $)
        dya2iocuni $p |- ( A e. ( J tX J ) -> E. c e. ~P ran R U. c = A ) $=
          ( vz vb vp wcel cv wrex wceq c0 vm ctx co wel wss crn crab cpw ssrab2
          wa cuni cxp wfn dya2iocrfn cz c2 cexp cdiv c1 caddc cico cmpt2 mpt2ex
          cvv zex eqeltri rnex xpex fnex mp2an elpw2 mpbir a1i wral rex0 mtbiri
          wn ralrimivw rabeq0 sylibr unieqd uni0 syl6eq 0ss syl6eqss wne elequ2
          rexeq sseq1 anbi12d rexbidv elrab simpr reximi syl5ibr adantld syl5bi
          r19.9rzv unissb pm2.61ine dya2iocnei simpl ssel2 ancoms adantl elequ1
          ralrimiv anbi1d rspcev syl2anc jca simprl reximi2 syl eluni2 ex ssrdv
          eqssd unieq eqeq1d ) DHHUBUCPZMNUDZNQZDUEZUJZMDRZNEUFZUGZYGUHZPZYHUKZ
          DSZIQZUKZDSZIYIRYJYAYJYHYGUEYFNYGUIYHYGEEGUFZYPULZUMYQVDPEVDPABCEFGHJ
          KLUNYPYPGGAFUOUOAQZUPFQUQUCZURUCYRUSUTUCYSURUCVAUCZVBVDKAFUOUOYTVEVEV
          CVFVGZUUAVHYQVDEVIVJVGVKVLVMYAYKDYKDUEZYAUUBDTDTSZYKTDUUCYKTUKTUUCYHT
          UUCYFVQZNYGVNYHTSUUCUUDNYGUUCYFYEMTRYEMVOYEMDTWHVPVRYFNYGVSVTWAWBWCDW
          DWEDTWFZOQZDUEZOYHVNUUBUUEUUGOYHUUFYHPZUUFYGPZMOUDZUUGUJZMDRZUJZUUEUU
          GYFUULNUUFYGYCUUFSZYEUUKMDUUNYBUUJYDUUGNOMWGYCUUFDWIWJWKWLZUUEUULUUGU
          UIUULUUGUUEUUGMDRUUKUUGMDUUJUUGWMWNUUGMDWRWOWPWQXGOYHDWSVTWTVMYAUADYK
          YAUAQZDPZUUPYKPZYAUUQUJZUAOUDZOYHRZUURUUSUUTUUGUJZOYGRUVAABCDEFGHUUPO
          JKLXAUVBUUTOYGYHUUIUVBUJZUUHUUTUVCUUMUUHUVCUUIUULUUIUVBXBUVCUUQUVBUUL
          UVBUUQUUIUUGUUTUUQUUFDUUPXCXDXEUUIUVBWMUUKUVBMUUPDMQUUPSUUJUUTUUGMUAO
          XFXHXIXJXKUUOVTUUIUUTUUGXLXKXMXNOUUPYHXOVTXPXQXRYOYLIYHYIYMYHSYNYKDYM
          YHXSXTXIXJ $.
      $}

      ${
        $d c d n u v x y $.  $d d u v I $.  $d c d R $.
        $( The dyadic rectangular set collection covers ` ( RR X. RR ) ` .
           (Contributed by Thierry Arnoux, 18-Sep-2017.) $)
        dya2iocucvr $p |- U. ran R = ( RR X. RR ) $=
          ( vd cr wss cv wcel wrex wa c2 co cz vc crn cuni cxp unissb wceq xpex
          vex elrnmpt2 simpr cpw pwssb cexp cdiv c1 caddc cico ovex simpll zred
          cxr 2re a1i cc0 wne 2ne0 simplr reexpclzd cc 2cn expne0d redivcld 1re
          readdcld rexrd icossre syl2anc eqsstrd rexlimivv sylbi mprgbir elpwid
          sseli xpss12 syl2an adantr ctx ctop cioo ctg cfv retop eqeltri txtopi
          uniretop unieqi eqtr4i txunii topopn dya2iocuni elpwi unissd eqsstr3d
          ex mp2b rexlimiva ax-mp eqssi ) DUBZUCZLLUDZXJXKMKNZXKMZKXIKXIXKUEXLX
          IOXLCNZBNZUDZUFZBFUBZPCXRPXMCBXRXRXPXLDJXNXOCUHBUHUGUIXQXMCBXRXRXNXRO
          ZXOXROZQZXQXMYAXQQXLXPXKYAXQUJYAXPXKMZXQXSXNLMXOLMYBXTXSXNLXRLUKZXNXR
          YCMXLLMZKXRKXRLULXLXROXLANZRENZUMSZUNSZYEUOUPSZYGUNSZUQSZUFZETPATPYDA
          ETTYKXLFIYHYJUQURUIYLYDAETTYETOZYFTOZQZYLYDYOYLQZXLYKLYOYLUJYPYHLOYJV
          AOYKLMYPYEYGYPYEYMYNYLUSUTZYPRYFRLOYPVBVCRVDVEYPVFVCZYMYNYLVGZVHZYPRY
          FRVIOYPVJVCYRYSVKZVLYPYJYPYIYGYPYEUOYQUOLOYPVMVCVNYTUUAVLVOYHYJVPVQVR
          XDVSVTWAZWCWBXTXOLXRYCXOUUBWCWBXNLXOLWDWEWFVRXDVSVTWAUANZUCZXKUFZUAXI
          UKZPZXKXJMZGGWGSZWHOXKUUIOUUGGGGWIUBWJWKZWHHWLWMZUUKWNUUIXKGGLLUUKUUK
          LUUJUCGUCWOGUUJHWPWQZUULWRWSABCXKDEFGUAHIJWTXEUUEUUHUAUUFUUCUUFOZUUEQ
          ZXKUUDXJUUMUUEUJUUNUUCXIUUMUUCXIMUUEUUCXIXAWFXBXCXFXGXH $.
      $}

      $d n u v y $.  $d n x y R $.  $d x J $.
      $( The Borel algebra on ` ( RR X. RR ) ` is a subset of the sigma algebra
         generated by the dyadic closed below, opened above rectangular subsets
         of ` ( RR X. RR ) ` .  This is a step of the proof of Proposition
         1.1.5 of [Cohn] p. 4 (Contributed by Thierry Arnoux, 17-Sep-2017.) $)
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
        $d d e f n u v x y $.  $d u v x I $.  $d x J $.  $d d R $.
        $( The sigma-algebra generated by the dyadic closed below, opened above
           rectangular subsets of ` ( RR X. RR ) ` is a subset of the sigma
           algebra generated by the closed half-spaces of ` ( RR X. RR ) ` .
           The proof goes by noting the fact that the dyadic rectangles are
           intersections of a 'vertical band' and an 'horizontal band', which
           themselves are differences of closed half-spaces.  (Contributed by
           Thierry Arnoux, 17-Sep-2017.) $)
        sxbrsigalem2 $p |- ( sigaGen ` ran R ) C_ ( sigaGen `
           ( ran ( e e. RR |-> ( ( e [,) +oo ) X. RR ) )
          u. ran ( f e. RR |-> ( RR X. ( f [,) +oo ) ) ) ) ) $=
          ( cr cpnf cico cxp wceq wcel wrex cz vd crn cuni cv cmpt cun csigagen
          co cfv wss cvv dya2iocucvr sxbrsigalem0 eqtr4i xpex elrnmpt2 wa simpr
          vex c1st cres ccnv cima c2nd cin cpw dya2icobrsiga brsigasspwrn sstri
          cbrsiga sseli elpwid xpinpreima2 syl2an csiga wtru reex rnex unex a1i
          mptex sgsiga trud 1stpreima syl c2 cexp cdiv caddc ovex xpeq1d difxp1
          c1 cdif cxr cle wbr simpl zred crp rpexpcld rerpdivcld rexrd readdcld
          2rp 1re pnfxr lep1d lediv1dd pnfge syl32anc syl5reqr ssun1 eqid oveq1
          difico eqeq2d rspcev sylancl elrnmpti sylibr sseldi elsigagen sylancr
          difelsiga syl3anc eqeltrd adantr ex rexlimivv 2ndpreima xpeq2d difxp2
          sylbi ssun2 adantl inelsiga ssriv sigagenss2 mp3an ) DUBZUCZEMEUDZNOU
          HZMPZUEZUBZFMMFUDZNOUHZPZUEZUBZUFZUCZQUUAUUMUGUIZUJUUMUKRZUUAUGUIUUOU
          JUUBMMPZUUNABCDGHIJKLULEFUMUNUAUUAUUOUAUDZUUARUURCUDZBUDZPZQZBHUBZSCU
          VCSUURUUORZCBUVCUVCUVAUURDLUUSUUTCUSBUSUOUPUVBUVDCBUVCUVCUUSUVCRZUUTU
          VCRZUQZUVBUVDUVGUVBUQUURUVAUUOUVGUVBURUVGUVAUUORUVBUVGUVAUTUUQVAVBUUS
          VCZVDUUQVAVBUUTVCZVEZUUOUVEUUSMUJZUUTMUJZUVAUVJQUVFUVEUUSMUVCMVFZUUSU
          VCVJUVMAGHIJKVGVHVIZVKVLZUVFUUTMUVCUVMUUTUVNVKVLZUUSUUTMMVMVNUVGUUOVO
          UBUCRZUVHUUORZUVIUUORZUVJUUORUVQUVGUVQVPUUMUKUUPVPUUGUULUUFEMUUEVQWAV
          RUUKFMUUJVQWAVRVSZVTWBWCZVTUVEUVRUVFUVEUVHUUSMPZUUOUVEUVKUVHUWBQUVOUU
          SMMWDWEUVEUUSAUDZWFGUDZWGUHZWHUHZUWCWMWIUHZUWEWHUHZOUHZQZGTSATSUWBUUO
          RZAGTTUWIUUSHKUWFUWHOWJZUPUWJUWKAGTTUWCTRZUWDTRZUQZUWJUWKUWOUWJUQZUWB
          UWIMPZUUOUWPUUSUWIMUWOUWJURWKUWOUWQUUORUWJUWOUWQUWFNOUHZMPZUWHNOUHZMP
          ZWNZUUOUWOUXBUWRUWTWNZMPUWQUWRUWTMWLUWOUXCUWIMUWOUWFWORUWHWORZNWORZUW
          FUWHWPWQUWHNWPWQZUXCUWIQUWOUWFUWOUWCUWEUWOUWCUWMUWNWRWSZUWOWFUWDWFWTR
          UWOXEVTUWMUWNURXAZXBZXCUWOUWHUWOUWGUWEUWOUWCWMUXGWMMRUWOXFVTXDZUXHXBZ
          XCZUXEUWOXGVTUWOUWCUWGUWEUXGUXJUXHUWOUWCUXGXHXIUWOUXDUXFUXLUWHXJWEUWF
          UWHNXPXKZWKXLUWOUVQUWSUUORZUXAUUORZUXBUUORUVQUWOUWAVTZUWOUUPUWSUUMRUX
          NUVTUWOUUGUUMUWSUUGUULXMZUWOUWSUUEQZEMSZUWSUUGRUWOUWFMRZUWSUWSQZUXSUX
          IUWSXNUXRUYAEUWFMUUCUWFQZUUEUWSUWSUYBUUDUWRMUUCUWFNOXOWKXQXRXSEMUUEUW
          SUUFUUFXNZUUDMUUCNOWJVQUOZXTYAYBUUMUWSUKYCYDUWOUUPUXAUUMRUXOUVTUWOUUG
          UUMUXAUXQUWOUXAUUEQZEMSZUXAUUGRUWOUWHMRZUXAUXAQZUYFUXKUXAXNUYEUYHEUWH
          MUUCUWHQZUUEUXAUXAUYIUUDUWTMUUCUWHNOXOWKXQXRXSEMUUEUXAUUFUYCUYDXTYAYB
          UUMUXAUKYCYDUWSUXAUUOYEYFYGYHYGYIYJYNYGYHUVFUVSUVEUVFUVIMUUTPZUUOUVFU
          VLUVIUYJQUVPUUTMMYKWEUVFUUTUWIQZGTSATSUYJUUORZAGTTUWIUUTHKUWLUPUYKUYL
          AGTTUWOUYKUYLUWOUYKUQZUYJMUWIPZUUOUYMUUTUWIMUWOUYKURYLUWOUYNUUORUYKUW
          OUYNMUWRPZMUWTPZWNZUUOUWOUYQMUXCPUYNMUWRUWTYMUWOUXCUWIMUXMYLXLUWOUVQU
          YOUUORZUYPUUORZUYQUUORUXPUWOUUPUYOUUMRUYRUVTUWOUULUUMUYOUULUUGYOZUWOU
          YOUUJQZFMSZUYOUULRUWOUXTUYOUYOQZVUBUXIUYOXNVUAVUCFUWFMUUHUWFQZUUJUYOU
          YOVUDUUIUWRMUUHUWFNOXOYLXQXRXSFMUUJUYOUUKUUKXNZMUUIVQUUHNOWJUOZXTYAYB
          UUMUYOUKYCYDUWOUUPUYPUUMRUYSUVTUWOUULUUMUYPUYTUWOUYPUUJQZFMSZUYPUULRU
          WOUYGUYPUYPQZVUHUXKUYPXNVUGVUIFUWHMUUHUWHQZUUJUYPUYPVUJUUIUWTMUUHUWHN
          OXOYLXQXRXSFMUUJUYPUUKVUEVUFXTYAYBUUMUYPUKYCYDUYOUYPUUOYEYFYGYHYGYIYJ
          YNYGYPUVHUVIUUOYQYFYGYHYGYIYJYNYRUVTUUAUUMUKYSYT $.
      $}

      ${
        $d e f n u v x $.
        $( The Borel algebra on ` ( RR X. RR ) ` is generated by the dyadic
           closed below, opened above rectangular subsets of
           ` ( RR X. RR ) ` .  Proposition 1.1.5 of [Cohn] p. 4 .  Note that
           the interval used in this formalization are closed below, opened
           above instead of opened below, closed above in the proof as they are
           ultimately generated by the floor function.  (Contributed by Thierry
           Arnoux, 21-Sep-2017.) $)
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
          ( ve vf vg cfv cbrsiga cv cxp wss wcel wa crn csigagen cmpt2 ctx cuni
          co csx wceq cr dya2iocucvr br2base eqtr4i csiga brsigarn elexi mpt2ex
          cvv coprab dya2icobrsiga sseli anim12i anim1i ssoprab2i df-mpt2 eqtri
          rnex xpeq1 xpeq2 3sstr4i rnss ax-mp sssigagen2 mp2an sigagenss2 mp3an
          cbvmpt2v sxbrsigalem4 eqid sxval ) DUAZUBNZKLOOKPZLPZQZUCZUAZUBNZGGUD
          UFUBNOOUGUFZVTUEZWFUEZUHVTWGRZWFUQSZWAWGRWIUIUIQWJABCDEFGHIJUJKLUKULW
          LVTWFRZWKWEKLOOWDOUIUMNZUNUOZWOUPVFZDWERWMCPZFUAZSZBPZWRSZTZMPWQWTQZU
          HZTZCBMURZWQOSZWTOSZTZXDTZCBMURZDWEXEXJCBMXBXIXDWSXGXAXHWROWQAEFGHIUS
          ZUTWROWTXLUTVAVBVCDCBWRWRXCUCXFJCBMWRWRXCVDVEWECBOOXCUCXKKLCBOOWDXCWQ
          WCQWBWQWCVGWCWTWQVHVPCBMOOXCVDVEVIDWEVJVKWFVTUQVLVMWPVTWFUQVNVOABCDEF
          GHIJVQOWNSZXMWHWGUHUNUNKLWFOOWNWNWFVRVSVMVI $.
      $}
    $}

    ${
      $d a m n u v x $.  $d u v x J $.
      $( First direction for ~ sxbrsiga , same as sxbrsigalem6, dealing with
         the antecedents.  (Contributed by Thierry Arnoux, 10-Oct-2017.) $)
      sxbrsigalem6 $p |- ( sigaGen ` ( J tX J ) ) C_ ( BrSiga sX BrSiga ) $=
        ( vx vv vu va vm vn cz cv c2 cexp co cdiv c1 caddc cico cmpt2 weq oveq1
        crn cxp oveq1d oveq12d oveq2 oveq2d cbvmpt2v eqid sxbrsigalem5 ) CDEEDF
        GIIFJZKGJZLMZNMZUJOPMZULNMZQMZRZUAZUREJDJUBRZHUQABFGCHIIUPCJZKHJZLMZNMZ
        UTOPMZVBNMZQMUTULNMZVDULNMZQMFCSZUMVFUOVGQUJUTULNTVHUNVDULNUJUTOPTUCUDG
        HSZVFVCVGVEQVIULVBUTNUKVAKLUEZUFVIULVBVDNVJUFUDUGUSUHUI $.
    $}

    ${
      $d x y n $.  $d e f J $.
      $( The product sigma-algebra ` ( BrSiga sX BrSiga ) ` is the Borel
         algebra on ` ( RR X. RR ) ` See example 5.1.1 of [Cohn] p. 143 .
         (Contributed by Thierry Arnoux, 10-Oct-2017.) $)
      sxbrsiga $p |- ( BrSiga sX BrSiga ) = ( sigaGen ` ( J tX J ) ) $=
        ( ve vf cbrsiga co csigagen cfv cv crn cr csiga wcel wceq brsigarn cuni
        mp2an wss mp1i a1i csx ctx cxp cmpt2 eqid ctopon br2base tpr2uni eqtr4i
        sxval wral wa c1st cres ccnv cima c2nd cin cpw brsigasspwrn xpinpreima2
        sseli elpwid syl2an tpr2tp sigagensiga elrnsiga sgsiga ccn cioo retopon
        ax-mp ctg eqeltri tx1cn eqidd df-brsiga fveq2i cnmbfm mbfmcnvima adantr
        tx2cn adantl inelsiga syl3anc eqeltrd rnmpt2ss sigagenss2 mp3an eqsstri
        id rgen2a sxbrsigalem6 eqssi ) EEUAFZAAUBFZGHZWOCDEECIZDIZUCZUDZJZGHZWQ
        EKLHZMZXEWOXCNOOCDXBEEXDXDXBUEUJQXBPZWPPZNXBWQRZWPKKUCZUFHZMZXCWQRXFXIX
        GCDUGABUHUIWTWQMZDEUKCEUKXHXLCDEWREMZWSEMZULZWTUMXIUNZUOWRUPZUQXIUNZUOW
        SUPZURZWQXMWRKRWSKRWTXTNXNXMWRKEKUSZWRUTVBVCXNWSKEYAWSUTVBVCWRWSKKVAVDX
        OWQLJPZMZXQWQMZXSWQMZXTWQMWQXGLHMZYCXOXKYFABVEZWPXJVFVLWQXGVGSXMYDXNXMW
        RWQEXPXMWPXJXKXMYGTVHXEEYBMZXMOEKVGZSXMWQEXPWPAXPWPAVIFZMZXMAKUFHZMZYMY
        KAVJJVMHZYLBVKVNZYOAAKKVOQTXMWQVPEAGHZNZXMEYNGHYPVQAYNGBVRUIZTVSXMWKVTW
        AXNYEXMXNWSWQEXRXNWPXJXKXNYGTVHXEYHXNOYISXNWQEXRWPAXRYJMZXNYMYMYSYOYOAA
        KKWBQTXNWQVPYQXNYRTVSXNWKVTWCXQXSWQWDWEWFWLCDEEWTWQXAXAUEWGVLYGXBWPXJWH
        WIWJABWMWN $.
    $}
  $}

