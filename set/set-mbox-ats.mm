$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Andrew Salmon
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Principia Mathematica * 10
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d ph x $.
    $( Theorem *10.12 in [WhiteheadRussell] p. 146.  In *10, this is treated as
       an axiom, and the proofs in *10 are based on this theorem.  (Contributed
       by Andrew Salmon, 17-Jun-2011.) $)
    pm10.12 $p |- ( A. x ( ph \/ ps ) -> ( ph \/ A. x ps ) ) $=
      ( wo wal 19.32v biimpi ) ABDCEABCEDABCFG $.
  $}

  $( Theorem *10.14 in [WhiteheadRussell] p. 146.  (Contributed by Andrew
     Salmon, 17-Jun-2011.) $)
  pm10.14 $p |- ( ( A. x ph /\ A. x ps ) -> ( [ y / x ] ph /\ [ y / x ] ps )
    ) $=
    ( wal wsb stdpc4 anim12i ) ACEACDFBCEBCDFACDGBCDGH $.

  $( Theorem *10.251 in [WhiteheadRussell] p. 149.  (Contributed by Andrew
     Salmon, 17-Jun-2011.) $)
  pm10.251 $p |- ( A. x -. ph -> -. A. x ph ) $=
    ( wn wal wex alnex 19.2 con3i sylbi ) ACBDABEZCABDZCABFKJABGHI $.

  $( Theorem *10.252 in [WhiteheadRussell] p. 149.  (Contributed by Andrew
     Salmon, 17-Jun-2011.)  (New usage is discouraged.) $)
  pm10.252 $p |- ( -. E. x ph <-> A. x -. ph ) $=
    ( wn wal wex df-ex bicomi con1bii ) ACBDZABEZJICABFGH $.

  $( Theorem *10.253 in [WhiteheadRussell] p. 149.  (Contributed by Andrew
     Salmon, 17-Jun-2011.) $)
  pm10.253 $p |- ( -. A. x ph <-> E. x -. ph ) $=
    ( wn wex wal alex bicomi con1bii ) ACBDZABEZJICABFGH $.

  $( Theorem *10.301 in [WhiteheadRussell] p. 151.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  albitr $p |- ( ( A. x ( ph <-> ps ) /\ A. x ( ps <-> ch ) ) ->
        A. x ( ph <-> ch ) ) $=
    ( wb bitr alanimi ) ABEBCEACEDABCFG $.

  $( Theorem *10.42 in [WhiteheadRussell] p. 155.  (Contributed by Andrew
     Salmon, 17-Jun-2011.) $)
  pm10.42 $p |- ( ( E. x ph \/ E. x ps ) <-> E. x ( ph \/ ps ) ) $=
    ( wo wex 19.43 bicomi ) ABDCEACEBCEDABCFG $.

  ${
    $d ps x $.
    $( Theorem *10.52 in [WhiteheadRussell] p. 155.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)
    pm10.52 $p |- ( E. x ph -> ( A. x ( ph -> ps ) <-> ps ) ) $=
      ( wi wal wex 19.23v pm5.5 bitrid ) ABDCEACFZBDJBABCGJBHI $.
  $}

  $( Theorem *10.53 in [WhiteheadRussell] p. 155.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  pm10.53 $p |- ( -. E. x ph -> A. x ( ph -> ps ) ) $=
    ( wex wn wal wi pm2.21 19.38 syl ) ACDZEKBCFZGABGCFKLHABCIJ $.

  ${
    $d ch x $.
    $( Theorem *10.541 in [WhiteheadRussell] p. 155.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)
    pm10.541 $p |- ( A. x ( ph -> ( ch \/ ps ) ) <->
        ( ch \/ A. x ( ph -> ps ) ) ) $=
      ( wn wi wal wo bi2.04 albii 19.21v bitri df-or imbi2i 3bitr4i ) ACEZBFZFZ
      DGZPABFZDGZFZACBHZFZDGCUAHSPTFZDGUBRUEDAPBIJPTDKLUDRDUCQACBMNJCUAMO $.
  $}

  ${
    $d ch x $.
    $( Theorem *10.542 in [WhiteheadRussell] p. 156.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)
    pm10.542 $p |- ( A. x ( ph -> ( ch -> ps ) ) <->
        ( ch -> A. x ( ph -> ps ) ) ) $=
      ( wi wal bi2.04 albii 19.21v bitri ) ACBEEZDFCABEZEZDFCLDFEKMDACBGHCLDIJ
      $.
  $}

  $( Theorem *10.55 in [WhiteheadRussell] p. 156.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  pm10.55 $p |- ( ( E. x ( ph /\ ps ) /\ A. x ( ph -> ps ) ) <->
        ( E. x ph /\ A. x ( ph -> ps ) ) ) $=
    ( wa wex wi wal exsimpl anim1i exintr imdistanri impbii ) ABDCEZABFCGZDACEZ
    NDMONABCHINOMABCJKL $.

  $( Theorem *10.56 in [WhiteheadRussell] p. 156.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  pm10.56 $p |- ( ( A. x ( ph -> ps ) /\
        E. x ( ph /\ ch ) ) -> E. x ( ps /\ ch ) ) $=
    ( wi wal wa wex pm3.45 aleximi imp ) ABEZDFACGZDHBCGZDHLMNDABCIJK $.

  $( Theorem *10.57 in [WhiteheadRussell] p. 156.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  pm10.57 $p |- ( A. x ( ph -> ( ps \/ ch ) ) ->
        ( A. x ( ph -> ps ) \/ E. x ( ph /\ ch ) ) ) $=
    ( wo wi wal wa wex wn alnex imnan pm2.53 con1d imim3i biimtrrid al2imi orrd
    ) ABCEZFZDGZABFZDGZACHZDIZUAUEUCUEJUDJZDGUAUCUDDKTUFUBDUFACJZFTUBACLSUGBASB
    CBCMNOPQPNR $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Principia Mathematica * 11
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    2alanimi.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Removes two universal quantifiers from a statement.  (Contributed by
       Andrew Salmon, 24-May-2011.) $)
    2alanimi $p |- ( ( A. x A. y ph /\ A. x A. y ps ) -> A. x A. y ch ) $=
      ( wal alanimi ) AEGBEGCEGDABCEFHH $.
  $}

  ${
    2al2imi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Removes two universal quantifiers from a statement.  (Contributed by
       Andrew Salmon, 24-May-2011.) $)
    2al2imi $p |- ( A. x A. y ph -> ( A. x A. y ps -> A. x A. y ch ) ) $=
      ( wal al2imi ) AEGBEGCEGDABCEFHH $.
  $}

  ${
    pm11.11.1 $e |- ph $.
    $( Theorem *11.11 in [WhiteheadRussell] p. 159.  (Contributed by Andrew
       Salmon, 17-Jun-2011.) $)
    pm11.11 $p |- A. z A. w [ z / x ] [ w / y ] ph $=
      ( wsb wal 2stdpc4 ax-gen mpg gen2 ) ACEGBDGZDEACHMBABCDEIACFJKL $.
  $}

  ${
    $d ph x $.  $d ph y $.
    $( Theorem *11.12 in [WhiteheadRussell] p. 159.  (Contributed by Andrew
       Salmon, 17-Jun-2011.) $)
    pm11.12 $p |- ( A. x A. y ( ph \/ ps ) -> ( ph \/ A. x A. y ps ) ) $=
      ( wo wal pm10.12 alimi syl ) ABEDFZCFABDFZEZCFAKCFEJLCABDGHAKCGI $.
  $}

  ${
    $d ps x $.  $d ps y $.
    $( Compare Theorem *11.3 in [WhiteheadRussell] p. 161.  Special case of
       theorem 19.21 of [Margaris] p. 90 with two quantifiers.  See ~ 19.21v .
       (Contributed by Andrew Salmon, 24-May-2011.) $)
    19.21vv $p |- ( A. x A. y ( ps -> ph ) <-> ( ps -> A. x A. y ph ) ) $=
      ( wi wal 19.21v albii bitri ) BAEDFZCFBADFZEZCFBKCFEJLCBADGHBKCGI $.
  $}

  $( Theorem *11.32 in [WhiteheadRussell] p. 162.  Theorem 19.20 of [Margaris]
     p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon, 24-May-2011.) $)
  2alim $p |- ( A. x A. y ( ph -> ps ) ->
        ( A. x A. y ph -> A. x A. y ps ) ) $=
    ( wi id 2al2imi ) ABEZABCDHFG $.

  $( Theorem *11.33 in [WhiteheadRussell] p. 162.  Theorem 19.15 of [Margaris]
     p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon, 24-May-2011.) $)
  2albi $p |- ( A. x A. y ( ph <-> ps ) ->
        ( A. x A. y ph <-> A. x A. y ps ) ) $=
    ( wb wal albi alimi syl ) ABEDFZCFADFZBDFZEZCFKCFLCFEJMCABDGHKLCGI $.

  $( Theorem *11.34 in [WhiteheadRussell] p. 162.  Theorem 19.22 of [Margaris]
     p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon, 24-May-2011.) $)
  2exim $p |- ( A. x A. y ( ph -> ps ) ->
        ( E. x E. y ph -> E. x E. y ps ) ) $=
    ( wi wal wex exim aleximi ) ABEDFADGBDGCABDHI $.

  $( Theorem *11.341 in [WhiteheadRussell] p. 162.  Theorem 19.18 of [Margaris]
     p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon, 24-May-2011.) $)
  2exbi $p |- ( A. x A. y ( ph <-> ps ) ->
        ( E. x E. y ph <-> E. x E. y ps ) ) $=
    ( wb wal wex exbi alimi syl ) ABEDFZCFADGZBDGZEZCFLCGMCGEKNCABDHILMCHJ $.

  $( Theorem *11.36 in [WhiteheadRussell] p. 162.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  spsbce-2 $p |- ( [ z / x ] [ w / y ] ph -> E. x E. y ph ) $=
    ( wsb wex spsbe eximi syl ) ACEFZBDFKBGACGZBGKBDHKLBACEHIJ $.

  $( Theorem *11.421 in [WhiteheadRussell] p. 163.  Theorem 19.33 of [Margaris]
     p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon, 24-May-2011.) $)
  19.33-2 $p |- ( ( A. x A. y ph \/ A. x A. y ps ) ->
        A. x A. y ( ph \/ ps ) ) $=
    ( wal wo orc 2alimi olc jaoi ) ADECEABFZDECEBDECEAKCDABGHBKCDBAIHJ $.

  ${
    $d ps x $.  $d ps y $.
    $( Theorem *11.43 in [WhiteheadRussell] p. 163.  Theorem 19.36 of
       [Margaris] p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon,
       25-May-2011.) $)
    19.36vv $p |- ( E. x E. y ( ph -> ps ) <-> ( A. x A. y ph -> ps ) ) $=
      ( wi wex wal 19.36v exbii bitri ) ABEDFZCFADGZBEZCFLCGBEKMCABDHILBCHJ $.
  $}

  ${
    $d ps x $.  $d ps y $.
    $( Theorem *11.44 in [WhiteheadRussell] p. 163.  Theorem 19.31 of
       [Margaris] p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon,
       24-May-2011.) $)
    19.31vv $p |- ( A. x A. y ( ph \/ ps ) <-> ( A. x A. y ph \/ ps ) ) $=
      ( wo wal 19.31v albii bitri ) ABEDFZCFADFZBEZCFKCFBEJLCABDGHKBCGI $.
  $}

  ${
    $d ps x $.  $d ps y $.
    $( Theorem *11.46 in [WhiteheadRussell] p. 164.  Theorem 19.37 of
       [Margaris] p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon,
       24-May-2011.) $)
    19.37vv $p |- ( E. x E. y ( ps -> ph ) <-> ( ps -> E. x E. y ph ) ) $=
      ( wi wex 19.37v exbii bitri ) BAEDFZCFBADFZEZCFBKCFEJLCBADGHBKCGI $.
  $}

  ${
    $d ps x $.  $d ps y $.
    $( Theorem *11.47 in [WhiteheadRussell] p. 164.  Theorem 19.28 of
       [Margaris] p. 90 with 2 quantifiers.  (Contributed by Andrew Salmon,
       24-May-2011.) $)
    19.28vv $p |- ( A. x A. y ( ps /\ ph ) <-> ( ps /\ A. x A. y ph ) ) $=
      ( wa wal 19.28v albii bitri ) BAEDFZCFBADFZEZCFBKCFEJLCBADGHBKCGI $.
  $}

  $( Theorem *11.52 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  pm11.52 $p |- ( E. x E. y ( ph /\ ps ) <->
        -. A. x A. y ( ph -> -. ps ) ) $=
    ( wa wex wn wi wal df-an 2exbii 2nalexn bitr4i ) ABEZDFCFABGHZGZDFCFODICIGN
    PCDABJKOCDLM $.

  ${
    $d ph y $.  $d ps x $.
    $( Theorem *11.56 in [WhiteheadRussell] p. 165.  Special case of ~ aaan .
       (Contributed by Andrew Salmon, 24-May-2011.) $)
    aaanv $p |- ( ( A. x ph /\ A. y ps ) <-> A. x A. y ( ph /\ ps ) ) $=
      ( wa wal nfv aaan bicomi ) ABEDFCFACFBDFEABCDADGBCGHI $.
  $}

  ${
    $d ph y $.
    $( Theorem *11.57 in [WhiteheadRussell] p. 165.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)
    pm11.57 $p |- ( A. x ph <-> A. x A. y ( ph /\ [ y / x ] ph ) ) $=
      ( wal wsb wa nfv nfal sp stdpc4 jca alrimi axc4i simpl sps alimi impbii )
      ABDZAABCEZFZCDZBDAUABRTCACBACGHRASABIABCJKLMUAABTACASNOPQ $.
  $}

  ${
    $d ph y $.
    $( Theorem *11.58 in [WhiteheadRussell] p. 165.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)
    pm11.58 $p |- ( E. x ph <-> E. x E. y ( ph /\ [ y / x ] ph ) ) $=
      ( wsb wa wex 19.8a nfv sb8e sylib pm4.71i 19.42v bitr4i exbii ) AAABCDZEC
      FZBAAOCFZEPAQAABFQABGABCACHIJKAOCLMN $.
  $}

  ${
    $d ph y $.  $d ps y $.
    $( Theorem *11.59 in [WhiteheadRussell] p. 165.  (Contributed by Andrew
       Salmon, 25-May-2011.) $)
    pm11.59 $p |- ( A. x ( ph -> ps ) ->
        A. y A. x ( ( ph /\ [ y / x ] ph ) -> ( ps /\ [ y / x ] ps ) ) ) $=
      ( wi wal wsb wa nfv nfal sp spsbim anim12d axc4i alrimi ) ABEZCFZAACDGZHB
      BCDGZHEZCFDPDCPDIJPTCQABRSPCKABCDLMNO $.
  $}

  ${
    $d ps x $.  $d ch y $.
    $( Theorem *11.6 in [WhiteheadRussell] p. 165.  (Contributed by Andrew
       Salmon, 25-May-2011.) $)
    pm11.6 $p |- ( E. x ( E. y ( ph /\ ps ) /\ ch ) <->
        E. y ( E. x ( ph /\ ch ) /\ ps ) ) $=
      ( wa wex excom an32 2exbii bitri 19.41v exbii 3bitr3i ) ABFZCFZEGZDGZACFZ
      BFZDGZEGZOEGCFZDGSDGBFZEGRPDGEGUBPDEHPTEDABCIJKQUCDOCELMUAUDESBDLMN $.
  $}

  ${
    $d ph y $.
    $( Theorem *11.61 in [WhiteheadRussell] p. 166.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)
    pm11.61 $p |- ( E. y A. x ( ph -> ps ) -> A. x ( ph -> E. y ps ) ) $=
      ( wi wal wex 19.12 19.37v biimpi alimi syl ) ABEZCFDGMDGZCFABDGEZCFMDCHNO
      CNOABDIJKL $.
  $}

  ${
    $d ph y $.
    $( Theorem *11.62 in [WhiteheadRussell] p. 166.  Importation combined with
       the rearrangement with quantifiers.  (Contributed by Andrew Salmon,
       24-May-2011.) $)
    pm11.62 $p |- ( A. x A. y ( ( ph /\ ps ) -> ch ) <->
        A. x ( ph -> A. y ( ps -> ch ) ) ) $=
      ( wa wi wal impexp albii 19.21v bitri ) ABFCGZEHZABCGZEHGZDNAOGZEHPMQEABC
      IJAOEKLJ $.
  $}

  $( Theorem *11.63 in [WhiteheadRussell] p. 166.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  pm11.63 $p |- ( -. E. x E. y ph -> A. x A. y ( ph -> ps ) ) $=
    ( wex wn wal wi 2nexaln pm2.21 2alimi sylbi ) ADECEFAFZDGCGABHZDGCGACDIMNCD
    ABJKL $.

  $( Theorem *11.7 in [WhiteheadRussell] p. 166.  (Contributed by Andrew
     Salmon, 24-May-2011.) $)
  pm11.7 $p |- ( E. x E. y ( ph \/ ph ) <-> E. x E. y ph ) $=
    ( wo oridm 2exbii ) AADABCAEF $.

  ${
    $d ph y $.  $d ps y $.  $d ch x $.  $d th x $.
    $( Theorem *11.71 in [WhiteheadRussell] p. 166.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)
    pm11.71 $p |- ( ( E. x ph /\ E. y ch ) ->
        ( ( A. x ( ph -> ps ) /\ A. y ( ch -> th ) ) <->
        A. x A. y ( ( ph /\ ch ) -> ( ps /\ th ) ) ) ) $=
      ( wex wa wal nfv nfex exim 19.42v 3imtr3g imim2i syl9 syl5 alimd 19.41v
      wi aaan anim12 2alimi sylbir pm3.21 simpl adantl ax-11 pm3.2 simpr adantr
      jcad impbid2 ) AEGZCFGZHZABTZEIZCDTZFIZHZACHZBDHZTZFIZEIZVAUQUSHZFIEIVFUQ
      USEFUQFJUSEJUAVGVDEFABCDUBUCUDUPVFURUTUOVFURTUNUOVEUQECEFCEJKVEAUOHZBDFGZ
      HZTZUOUQVEVBFGVCFGVHVJVBVCFLACFMBDFMNUOAVHVKBUOAUEVJBVHBVIUFOPQRUGUNVFUTT
      UOVFVDEIZFIUNUTVDEFUHUNVLUSFAFEAFJKVLUNCHZBEGZDHZTZUNUSVLVBEGVCEGVMVOVBVC
      ELACESBDESNUNCVMVPDUNCUIVODVMVNDUJOPQRQUKULUM $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Predicate Calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x z $.
    $( If ` x = y ` always implies ` x = z ` , then ` y = z ` .  (Contributed
       by Andrew Salmon, 2-Jun-2011.) $)
    sbeqal1 $p |- ( A. x ( x = y -> x = z ) -> y = z ) $=
      ( weq wi wal wsb sb2 equsb3 sylib ) ABDACDZEAFKABGBCDKABHABCIJ $.

    sbeqal1i.1 $e |- ( x = y -> x = z ) $.
    $( Suppose you know ` x = y ` implies ` x = z ` , assuming ` x ` and ` z `
       are distinct.  Then, ` y = z ` .  (Contributed by Andrew Salmon,
       3-Jun-2011.) $)
    sbeqal1i $p |- y = z $=
      ( weq wi sbeqal1 mpg ) ABEACEFBCEAABCGDH $.

    $( If ` x = y ` implies ` x = z ` , then we can infer ` z = y ` .
       (Contributed by Andrew Salmon, 3-Jun-2011.) $)
    sbeqal2i $p |- z = y $=
      ( cv sbeqal1i eqcomi ) BECEABCDFG $.
  $}

  $( Proof of a theorem that can act as a sole axiom for pure predicate
     calculus with ~ ax-gen as the inference rule.  This proof extends the idea
     of ~ axc5c711 and related theorems.  (Contributed by Andrew Salmon,
     14-Jul-2011.) $)
  axc5c4c711 $p |- ( ( A. x A. y -. A. x A. y ( A. y ph -> ps ) -> ( ph ->
      A. y ( A. y ph -> ps ) ) ) -> ( A. y ph -> A. y ps ) ) $=
    ( wal wi wn axc4 hbn1 axc7 con1i alrimih ax-11 syl nsyl4 pm2.21 spsd ja ) A
    DEZBFZDEZCEGZDECEZAUAFSBDEZFZUAUEUCABDHZUAGZUBCEZDEUCUGUHDTDIUHUAUACJKLUBDC
    MNOAUAUEAGAUDDAUDPQUFRR $.

  ${
    $d x y $.
    $( Rederivation of ~ sp from ~ axc5c4c711 .  Note that ~ ax6 is used for
       the rederivation.  (Contributed by Andrew Salmon, 14-Jul-2011.)  Revised
       to use ~ ax6v instead of ~ ax6 , so that this rederivation requires only
       ~ ax6v and propositional calculus.  (Revised by BJ, 14-Sep-2019.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    axc5c4c711toc5 $p |- ( A. x ph -> ph ) $=
      ( vy wal wn cv wceq ax6v wi pm2.21 ax-1 axc5c4c711 3syl mtoi con4i ) AABD
      ZAEZPBFCFGEZBDZBCHQAPRIBDZIZTBDEBDBDZUAIPSIATJUAUBKARBBLMNO $.
  $}

  $( Rederivation of ~ axc4 from ~ axc5c4c711 .  Note that only propositional
     calculus is required for the rederivation.  (Contributed by Andrew Salmon,
     14-Jul-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  axc5c4c711toc4 $p |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    ( wal wi wn ax-1 axc5c4c711 3syl ) ACDZBECDZAKEZKCDFCDCDZLEJBCDEKAGLMGABCCH
    I $.

  $( Rederivation of ~ axc7 from ~ axc5c4c711 .  Note that neither ~ axc7 nor
     ~ ax-11 are required for the rederivation.  (Contributed by Andrew Salmon,
     14-Jul-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  axc5c4c711toc7 $p |- ( -. A. x -. A. x ph -> ph ) $=
    ( wal wn wi ax-1 alimi axc4i con3i sps pm2.21 axc5c4c711 syl sp syl6 pm2.27
    id mpg 3syl ) ABCZDZBCZDAAEZBCZAEZBCZBCZDZBCZBCZDZUEAUJUBUIUBBUHUABTUGAUFBA
    UEBAUDFGHIGJIUKUDTAUKUJUCUFEZEUDTEUJULKUCABBLMABNOUCUEAEBUDAPAQRS $.

  $( Rederivation of ~ ax-11 from ~ axc5c4c711 .  Note that ~ ax-11 is not
     required for the rederivation.  (Contributed by Andrew Salmon,
     14-Jul-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  axc5c4c711to11 $p |- ( A. x A. y ph -> A. y A. x ph ) $=
    ( wal wi ax-1 2alimi wn axc5c4c711toc7 con4i pm2.21 axc5c4c711 sp syl alimi
    syl6 nsyl4 pm2.27 id mpg 3syl ) ACDZBDAAEZCDZAEZCDZBDZUEBDZCDZABDCDAUEBCAUD
    FGUGUGHZCDZHZCDZUIUMUGUJCIJULUHCUKBDZHZBDUHUKUOUEBUOUNUCUFEZEZUEUNUPKUQUDUB
    AUCABCLACMPNOUKBIQONUEACBUCUEAECUDARASTGUA $.

  ${
    $d x z w $.
    $( This theorem shows that, given ~ axextb , we can derive a version of
       ~ axc11n .  However, it is weaker than ~ axc11n because it has a
       distinct variable requirement.  (Contributed by Andrew Salmon,
       16-Jul-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    axc11next $p |- ( A. x x = z -> A. z z = x ) $=
      ( vw cv wcel wb wal wceq wi alimi ax9 axc4i wex nfa1 19.23 elequ2 cbvexvw
      19.8a sylib imim12i ax-ext ax-11 biimpr stdpc5v syl syl9 alimdv sps mpcom
      syl5 cbvalivw sylbi alcoms alrimiv spimvw sp impbid axextb albii 3imtr4i
      3syl ) CDZADZEZVBBDZEZFZCGZAGZVFVDFZCGZBGZVCVEHZAGZVEVCHZBGVIVDVDAGZIZCGZ
      AGZVFVFBGZIZCGZBGVLVHVRAVNVIVRVHVMAABCUAJVMVIVRIAVIVGAGZCGVMVRVGACUBVMWCV
      QCVMVDVFWCVPABCKZWCVFVDIZAGVFVPIVGWEAVDVFUCJVFVDAUDUEUFUGUJUHUILVSWBBVQWB
      CAVQAGZWACWFVDAMZVPIWAVDVPAVDANOVFWGVPVTVFVFBMZWGVFBRZVFVDBABACPQSVDVFABW
      DUKTULJUMUNWBVKBWAVKCBWABGZVJCWJWHVTIZVJVFVTBVFBNOWKVFVDVFWHVTVDWIVFVDBAB
      ACKUOTVDWHVTVFVDWGWHVDARVDVFABABCPQSVFBUPTUQULJUMLVAVMVHAABCURUSVOVKBBACU
      RUSUT $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Principia Mathematica * 13 and * 14
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( One result of theorem *13.13 in [WhiteheadRussell] p. 178.  A note on the
     section - to make the theorems more usable, and because inequality is
     notation for set theory (it is not defined in the predicate calculus
     section), this section will use classes instead of sets.  (Contributed by
     Andrew Salmon, 3-Jun-2011.) $)
  pm13.13a $p |- ( ( ph /\ x = A ) -> [. A / x ]. ph ) $=
    ( cv wceq wsbc sbceq1a biimpac ) BDCEAABCFABCGH $.

  $( Theorem *13.13 in [WhiteheadRussell] p. 178 with different variable
     substitution.  (Contributed by Andrew Salmon, 3-Jun-2011.) $)
  pm13.13b $p |- ( ( [. A / x ]. ph /\ x = A ) -> ph ) $=
    ( cv wceq wsbc sbceq1a biimparc ) BDCEAABCFABCGH $.

  $( Theorem *13.14 in [WhiteheadRussell] p. 178.  (Contributed by Andrew
     Salmon, 3-Jun-2011.) $)
  pm13.14 $p |- ( ( [. A / x ]. ph /\ -. ph ) -> x =/= A ) $=
    ( wsbc wn cv wne wceq sbceq1a biimprcd necon3bd imp ) ABCDZAEBFZCGMANCNCHAM
    ABCIJKL $.

  ${
    $d x y A $.
    $( Theorem *13.192 in [WhiteheadRussell] p. 179.  (Contributed by Andrew
       Salmon, 3-Jun-2011.)  (Revised by NM, 4-Jan-2017.) $)
    pm13.192 $p |- ( E. y ( A. x ( x = A <-> x = y ) /\ ph ) <->
      [. A / y ]. ph ) $=
      ( cv wceq weq wb wal wa wex wsbc biimpr alimi eqeq1 equsalvw sylib eqcoms
      wi eqeq2 alrimiv impbii anbi1i exbii sbc5 bitr4i ) BEZDFZBCGZHZBIZAJZCKCE
      ZDFZAJZCKACDLULUOCUKUNAUKUNUKUIUHSZBIUNUJUPBUHUIMNUHUNBCUGUMDOPQUNUJBUJDU
      MDUMUGTRUAUBUCUDACDUEUF $.
  $}

  $( Theorem *13.193 in [WhiteheadRussell] p. 179.  (Contributed by Andrew
     Salmon, 3-Jun-2011.) $)
  pm13.193 $p |- ( ( ph /\ x = y ) <-> ( [ y / x ] ph /\ x = y ) ) $=
    ( weq wsb sbequ12 pm5.32ri ) BCDAABCEABCFG $.

  $( Theorem *13.194 in [WhiteheadRussell] p. 179.  (Contributed by Andrew
     Salmon, 3-Jun-2011.) $)
  pm13.194 $p |- ( ( ph /\ x = y ) <-> ( [ y / x ] ph /\ ph /\ x = y ) ) $=
    ( weq wa wsb w3a wsbc pm13.13a sbsbc sylibr simpl simpr 3jca 3simpc impbii
    cv ) ABCDZEZABCFZARGSTARSABCQZHTABUAIABCJKARLARMNTAROP $.

  ${
    $d y A $.
    $( Theorem *13.195 in [WhiteheadRussell] p. 179.  This theorem is very
       similar to ~ sbc5 .  (Contributed by Andrew Salmon, 3-Jun-2011.)
       (Revised by NM, 4-Jan-2017.) $)
    pm13.195 $p |- ( E. y ( y = A /\ ph ) <-> [. A / y ]. ph ) $=
      ( wsbc cv wceq wa wex sbc5 bicomi ) ABCDBECFAGBHABCIJ $.
  $}

  ${
    $d x y $.  $d ph y $.
    $( Theorem *13.196 in [WhiteheadRussell] p. 179.  The only difference is
       the position of the substituted variable.  (Contributed by Andrew
       Salmon, 3-Jun-2011.) $)
    pm13.196a $p |- ( -. ph <-> A. y ( [ y / x ] ph -> y =/= x ) ) $=
      ( wn weq wsb wa wex wi wal wne sbelx sbalex sbn imbi2i con2b df-ne bicomi
      cv 3bitri albii ) ADZCBEZUBBCFZGCHUCUDIZCJABCFZCSZBSZKZIZCJUBCBLUDCBMUEUJ
      CUEUCUFDZIUFUCDZIUJUDUKUCABCNOUCUFPULUIUFUIULUGUHQROTUAT $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d x y ph $.
    $( Theorem *13.21 in [WhiteheadRussell] p. 179.  (Contributed by Andrew
       Salmon, 3-Jun-2011.) $)
    2sbc6g $p |- ( ( A e. C /\ B e. D ) -> ( A. z A. w ( ( z = A /\
      w = B ) -> ph ) <-> [. A / z ]. [. B / w ]. ph ) ) $=
      ( vx vy wcel cv wceq wa wi wal wsbc wb weq eqeq2 imbi1d anbi2d dfsbcq vex
      2albidv sbcbidv bibi12d anbi1d 19.21v impexp albii imbi2i 3bitr4ri bitr2i
      sbc6 vtocl2g ancoms ) EGJDFJBKZDLZCKZELZMZANZCOBOZACEPZBDPZQZBHRZCIRZMZAN
      ZCOZBOZACIKZPZBHKZPZQVGUTMZANZCOBOZVDBVOPZQVFIHEDGFVMELZVLVSVPVTWAVJVRBCW
      AVIVQAWAVHUTVGVMEUSSUATUDWAVNVDBVOACVMEUBUEUFVODLZVSVCVTVEWBVRVBBCWBVQVAA
      WBVGURUTVODUQSUGTUDVDBVODUBUFVPVGVNNZBOVLVNBVOHUCUNWCVKBVGVHANZNZCOVGWDCO
      ZNVKWCVGWDCUHVJWECVGVHAUIUJVNWFVGACVMIUCUNUKULUJUMUOUP $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d x y ph $.
    $( Theorem *13.22 in [WhiteheadRussell] p. 179.  (Contributed by Andrew
       Salmon, 3-Jun-2011.) $)
    2sbc5g $p |- ( ( A e. C /\ B e. D ) -> ( E. z E. w ( ( z = A /\ w = B )
      /\ ph ) <-> [. A / z ]. [. B / w ]. ph ) ) $=
      ( vx vy wcel cv wceq wa wex wsbc wb weq eqeq2 anbi1d 2exbidv sbcbidv sbc5
      anbi2d dfsbcq bibi12d 19.42v anass anbi2i 3bitr4ri bitr2i vtocl2g ancoms
      exbii ) EGJDFJBKZDLZCKZELZMZAMZCNBNZACEOZBDOZPZBHQZCIQZMZAMZCNZBNZACIKZOZ
      BHKZOZPVDUQMZAMZCNBNZVABVLOZPVCIHEDGFVJELZVIVPVMVQVRVGVOBCVRVFVNAVRVEUQVD
      VJEUPRUCSTVRVKVABVLACVJEUDUAUEVLDLZVPUTVQVBVSVOUSBCVSVNURAVSVDUOUQVLDUNRS
      STVABVLDUDUEVMVDVKMZBNVIVKBVLUBVTVHBVDVEAMZMZCNVDWACNZMVHVTVDWACUFVGWBCVD
      VEAUGUMVKWCVDACVJUBUHUIUMUJUKUL $.
  $}

  ${
    $d x y $.  $d ph y $.
    $( Equivalence between two different forms of ` iota ` .  (Contributed by
       Andrew Salmon, 15-Jul-2011.) $)
    iotain $p |- ( E! x ph -> |^| { x | ph } = ( iota x ph ) ) $=
      ( vy weu cv wceq wb wal wex cab cint cio eu6 csn intsn abbi df-sn eqtr4di
      vex inteqd iotaval 3eqtr4a exlimiv sylbi ) ABDABECEZFZGBHZCIABJZKZABLZFZA
      BCMUGUKCUGUENZKUEUIUJUECSOUGUHULUGUHUFBJULAUFBPBUEQRTABCUAUBUCUD $.
  $}

  ${
    $d y ph $.  $d y x $.
    $( The iota class exists.  This theorem does not require ~ ax-nul for its
       proof.  (Contributed by Andrew Salmon, 11-Jul-2011.) $)
    iotaexeu $p |- ( E! x ph -> ( iota x ph ) e. _V ) $=
      ( vy cv wceq wb wal wex cio weu cvv wcel iotaval eqcomd eximi eu6 3imtr4i
      isset ) ABDCDZEFBGZCHSABIZEZCHABJUAKLTUBCTUASABCMNOABCPCUARQ $.
  $}

  ${
    $d x y $.  $d ph y $.
    $( Definition *14.01 in [WhiteheadRussell] p. 184.  In Principia
       Mathematica, Russell and Whitehead define ` iota ` in terms of a
       function of ` ( iota x ph ) ` .  Their definition differs in that a
       function of ` ( iota x ph ) ` evaluates to "false" when there isn't a
       single ` x ` that satisfies ` ph ` .  (Contributed by Andrew Salmon,
       11-Jul-2011.) $)
    iotasbc $p |- ( E! x ph -> ( [. ( iota x ph ) / y ]. ps <->
         E. y ( A. x ( ph <-> x = y ) /\ ps ) ) ) $=
      ( cio wsbc cv wceq wa wex weu wb wal sbc5 wi cvv wcel iotaexeu eueq sylib
      eu6 iotaval eqcomd ancri eximi sylbi eupick syl2anc impbid1 anbi1d exbidv
      bitrid ) BDACEZFDGZUMHZBIZDJACKZACGUNHLCMZBIZDJBDUMNUQUPUSDUQUOURBUQUOURU
      QUODKZUOURIZDJZUOUROUQUMPQUTACRDUMSTUQURDJVBACDUAURVADURUOURUMUNACDUBUCZU
      DUEUFUOURDUGUHVCUIUJUKUL $.
  $}

  ${
    $d x y z $.  $d ph y z $.  $d ps y z $.
    $( Theorem *14.111 in [WhiteheadRussell] p. 184.  (Contributed by Andrew
       Salmon, 11-Jul-2011.) $)
    iotasbc2 $p |- ( ( E! x ph /\ E! x ps ) -> ( [. ( iota x ph ) / y ].
        [. ( iota x ps ) / z ]. ch <-> E. y E. z ( A. x ( ph <-> x = y ) /\
        A. x ( ps <-> x = z ) /\ ch ) ) ) $=
      ( weu cio wsbc weq wb wal wa wex w3a iotasbc anbi2d 3anass exbii 19.42v
      bitr2i bitrdi exbidv sylan9bb ) ADGCFBDHIZEADHIADEJKDLZUEMZENBDGZUFBDFJKD
      LZCOZFNZENAUEDEPUHUGUKEUHUGUFUICMZFNZMZUKUHUEUMUFBCDFPQUKUFULMZFNUNUJUOFU
      FUICRSUFULFTUAUBUCUD $.
  $}

  ${
    $d ph y $.  $d x y $.
    $( Theorem *14.12 in [WhiteheadRussell] p. 184.  (Contributed by Andrew
       Salmon, 11-Jul-2011.) $)
    pm14.12 $p |- ( E! x ph
        -> A. x A. y ( ( ph /\ [. y / x ]. ph ) -> x = y ) ) $=
      ( weu wmo cv wsbc wa weq wi wal eumo wsb sbsbc anbi2i imbi1i 2albii bitri
      nfv mo3 sylib ) ABDABEZAABCFGZHZBCIZJZCKBKZABLUBAABCMZHZUEJZCKBKUGABCACST
      UJUFBCUIUDUEUHUCAABCNOPQRUA $.
  $}

  ${
    $d y x A $.  $d ph y $.
    $( Theorem *14.122 in [WhiteheadRussell] p. 185.  (Contributed by Andrew
       Salmon, 9-Jun-2011.) $)
    pm14.122a $p |- ( A e. V -> ( A. x ( ph <-> x = A )
        <-> ( A. x ( ph -> x = A ) /\ [. A / x ]. ph ) ) ) $=
      ( cv wceq wb wal wi wa wcel wsbc albiim sbc6g bicomd anbi2d bitrid ) ABEC
      FZGBHARIBHZRAIBHZJCDKZSABCLZJARBMUATUBSUAUBTABCDNOPQ $.

    $( Theorem *14.122 in [WhiteheadRussell] p. 185.  (Contributed by Andrew
       Salmon, 9-Jun-2011.) $)
    pm14.122b $p |- ( A e. V -> ( ( A. x ( ph -> x = A ) /\ [. A / x ]. ph )
        <-> ( A. x ( ph -> x = A ) /\ E. x ph ) ) ) $=
      ( vy wcel cv wceq wi wal wsbc wex weq imbi2d albidv dfsbcq bibi1d imbi12d
      wb eqeq2 wa sbc5 nfa1 simpr ancr sps impbid2 exbid bitrid vtoclg pm5.32d
      ) CDFABGZCHZIZBJZABCKZABLZABEMZIZBJZABEGZKZUQSZIUOUPUQSZIECDVACHZUTUOVCVD
      VEUSUNBVEURUMAVACULTNOVEVBUPUQABVACPQRVBURAUAZBLUTUQABVAUBUTVFABUSBUCUTVF
      AURAUDUSAVFIBAURUEUFUGUHUIUJUK $.

    $( Theorem *14.122 in [WhiteheadRussell] p. 185.  (Contributed by Andrew
       Salmon, 9-Jun-2011.) $)
    pm14.122c $p |- ( A e. V -> ( A. x ( ph <-> x = A ) <->
                    ( A. x ( ph -> x = A ) /\ E. x ph ) ) ) $=
      ( wcel cv wceq wb wal wi wsbc wa wex pm14.122a pm14.122b bitrd ) CDEABFCG
      ZHBIAQJBIZABCKLRABMLABCDNABCDOP $.
  $}

  ${
    $d w A z $.  $d w B z $.
    $( Theorem *14.123 in [WhiteheadRussell] p. 185.  (Contributed by Andrew
       Salmon, 9-Jun-2011.) $)
    pm14.123a $p |- ( ( A e. V /\ B e. W ) -> ( A. z A. w ( ph <->
      ( z = A /\ w = B ) ) <-> ( A. z A. w ( ph -> ( z = A /\ w = B ) ) /\
      [. A / z ]. [. B / w ]. ph ) ) ) $=
      ( cv wceq wa wb wal wi wcel wsbc 2albiim 2sbc6g anbi2d bitrid ) ABHDICHEI
      JZKCLBLATMCLBLZTAMCLBLZJDFNEGNJZUAACEOBDOZJATBCPUCUBUDUAABCDEFGQRS $.

    $( Theorem *14.123 in [WhiteheadRussell] p. 185.  (Contributed by Andrew
       Salmon, 9-Jun-2011.) $)
    pm14.123b $p |- ( ( A e. V /\ B e. W ) -> ( ( A. z A. w ( ph ->
      ( z = A /\ w = B ) ) /\ [. A / z ]. [. B / w ]. ph ) <->
      ( A. z A. w ( ph -> ( z = A /\ w = B ) ) /\ E. z E. w ph ) ) ) $=
      ( wcel wa cv wceq wi wal wsbc wex wb 2sbc5g adantr nfa1 exbid simpr ancrd
      nfa2 2sp impbid2 adantl bitr3d pm5.32da ) DFHEGHIZABJDKCJEKIZLZCMZBMZACEN
      BDNZACOZBOZUIUMIUJAIZCOZBOZUNUPUIUSUNPUMABCDEFGQRUMUSUPPUIUMURUOBULBSUMUQ
      ACUKCBUCUMUQAUJAUAUMAUJUKBCUDUBUETTUFUGUH $.

    $( Theorem *14.123 in [WhiteheadRussell] p. 185.  (Contributed by Andrew
       Salmon, 9-Jun-2011.) $)
    pm14.123c $p |- ( ( A e. V /\ B e. W ) -> ( A. z A. w ( ph <->
      ( z = A /\ w = B ) ) <-> ( A. z A. w ( ph -> ( z = A /\ w = B ) ) /\
      E. z E. w ph ) ) ) $=
      ( wcel wa cv wceq wb wal wi wsbc wex pm14.123a pm14.123b bitrd ) DFHEGHIA
      BJDKCJEKIZLCMBMATNCMBMZACEOBDOIUAACPBPIABCDEFGQABCDEFGRS $.
  $}

  $( Theorem *14.18 in [WhiteheadRussell] p. 189.  (Contributed by Andrew
     Salmon, 11-Jul-2011.) $)
  pm14.18 $p |- ( E! x ph -> ( A. x ps -> [. ( iota x ph ) / x ]. ps ) ) $=
    ( weu cio cvv wcel wal wsbc wi iotaexeu spsbc syl ) ACDACEZFGBCHBCNIJACKBCN
    FLM $.

  ${
    $d x y $.
    $( Theorem *14.2 in [WhiteheadRussell] p. 189.  (Contributed by Andrew
       Salmon, 11-Jul-2011.) $)
    iotaequ $p |- ( iota x x = y ) = y $=
      ( cv wceq wb cio iotaval biid mpg ) ACBCZDZKEKAFJDAKABGKHI $.
  $}

  ${
    $d x y z $.  $d ph z $.
    $( Theorem *14.202 in [WhiteheadRussell] p. 189.  A biconditional version
       of ~ iotaval .  (Contributed by Andrew Salmon, 11-Jul-2011.) $)
    iotavalb $p |- ( E! x ph -> ( A. x ( ph <-> x = y ) <->
        ( iota x ph ) = y ) ) $=
      ( vz weu weq wb wal cio cv wceq iotaval wa wex wsbc iotasbc wcel iotaexeu
      cvv eqsbc1 bitr3d equequ2 bibi2d albidv biimpac exlimiv biimtrrdi impbid2
      syl ) ABEZABCFZGZBHZABIZCJZKZABCLUJUPABDFZGZBHZDCFZMZDNZUMUJUTDUNOZVBUPAU
      TBDPUJUNSQVCUPGABRDUNUOSTUIUAVAUMDUTUSUMUTURULBUTUQUKADCBUBUCUDUEUFUGUH
      $.
  $}

  ${
    $d x y $.  $d ph y $.
    $( Theorem *14.205 in [WhiteheadRussell] p. 190.  (Contributed by Andrew
       Salmon, 11-Jul-2011.) $)
    iotasbc5 $p |- ( E! x ph -> ( [. ( iota x ph ) / y ]. ps <->
        E. y ( y = ( iota x ph ) /\ ps ) ) ) $=
      ( cio wsbc cv wceq wa wex wb weu sbc5 a1i ) BDACEZFDGOHBIDJKACLBDOMN $.
  $}

  ${
    $d y x $.  $d y ph $.
    $( Theorem *14.24 in [WhiteheadRussell] p. 191.  (Contributed by Andrew
       Salmon, 12-Jul-2011.) $)
    pm14.24 $p |- ( E! x ph
        -> A. y ( [. y / x ]. ph <-> y = ( iota x ph ) ) ) $=
      ( weu cv wsbc cio wb weq wal nfeu1 nfsbc1v wa wi pm14.12 19.21bbi ancomsd
      wceq ex impbid expdimp pm13.13b adantl alrimd iotaval eqcomd iota4 dfsbcq
      syl6 syl5ibrcom alrimiv ) ABDZABCEZFZUMABGZRZHCULUNUPULUNABCIZHZBJZUPULUN
      URBABKABUMLULUNURULUNMAUQULUNAUQULAUNUQULAUNMUQNBCABCOPQUAUNUQANULUNUQAAB
      UMUBSUCTSUDUSUOUMABCUEUFUIULUNUPABUOFABUGABUMUOUHUJTUK $.
  $}

  ${
    $d x y $.  $d ph y $.
    $( Theorem *14.242 in [WhiteheadRussell] p. 192.  (Contributed by Andrew
       Salmon, 11-Jul-2011.) $)
    iotavalsb $p |- ( A. x ( ph <-> x = y ) -> ( [. y / z ]. ps <->
        [. ( iota x ph ) / z ]. ps ) ) $=
      ( cv wceq wb wal wex cio 19.8a weu wi eu6 iotavalb dfsbcq eqcoms biimtrdi
      wsbc sylbir mpcom ) ACFDFZGHCIZDJZUDBEUCTBEACKZTHZUDDLUEACMZUDUGNACDOUHUD
      UFUCGUGACDPUGUCUFBEUCUFQRSUAUB $.
  $}

  ${
    $d x y $.  $d ph y $.  $d ps y $.
    $( Theorem *14.25 in [WhiteheadRussell] p. 192.  (Contributed by Andrew
       Salmon, 12-Jul-2011.) $)
    sbiota1 $p |- ( E! x ph
        -> ( A. x ( ph -> ps ) <-> [. ( iota x ph ) / x ]. ps ) ) $=
      ( vy weu wi wal cio wsbc cv wceq wb wex eu6 wsb sbsbc dfsbcq sylc wa cvv
      biimpi iota4 iotaval eqcomd spsbim 3imtr3g imbi12d imbitrid com23 exlimiv
      syl wcel iotaexeu anbi12d imbi1d spesbc sylbir vtoclg expd anc2li eupicka
      sbcan syl6 impbid ) ACEZABFCGZBCACHZIZVEACJDJZKLCGZDMZACVGIZVFVHFZVEVKACD
      NUAACUBZVJVLVMFZDVJVIVGKZVOVJVGVIACDUCUDVPVFVLVHVFACVIIZBCVIIZFVPVLVHFVFA
      CDOBCDOVQVRABCDUEACDPBCDPUFVPVQVLVRVHACVIVGQZBCVIVGQZUGUHUIUKUJRVEVHVEABS
      ZCMZSVFVEVHWBVEVGTULZVLVHWBFACUMVNWCVLVHWBVQVRSZWBFVLVHSZWBFDVGTVPWDWEWBV
      PVQVLVRVHVSVTUNUOWDWACVIIWBABCVIVBWACVIUPUQURUSRUTABCVAVCVD $.
  $}

  $( Theorem *14.26 in [WhiteheadRussell] p. 192.  (Contributed by Andrew
     Salmon, 12-Jul-2011.) $)
  sbaniota $p |- ( E! x ph
      -> ( E. x ( ph /\ ps ) <-> [. ( iota x ph ) / x ]. ps ) ) $=
    ( weu wa wex wi wal cio wsbc eupickbi sbiota1 bitrd ) ACDABECFABGCHBCACIJAB
    CKABCLM $.

  $( Theorem *14.272 in [WhiteheadRussell] p. 193.  (Contributed by Andrew
     Salmon, 11-Jul-2011.) $)
  iotasbcq $p |- ( A. x ( ph <-> ps ) -> ( [. ( iota x ph ) / y ]. ch <->
      [. ( iota x ps ) / y ]. ch ) ) $=
    ( wb wal cio iotabi sbceq1d ) ABFDGCEADHBDHABDIJ $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Set Theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x $.
    $( Any set that contains one element less than the universe is not equal to
       it.  (Contributed by Andrew Salmon, 16-Jun-2011.) $)
    elnev $p |- ( A e. _V <-> { x | -. x = A } =/= _V ) $=
      ( cvv wcel cv wceq wex wn cab wne isset weq eqeq2i wb wal abbib equid tbt
      df-v bitri albii alnex 3bitr2i necon2abii ) BCDAEBFZAGZUEHZAIZCJABKUFUHCU
      HCFUHAALZAIZFZUFHZCUJUHASMUKUGUINZAOUGAOULUGUIAPUGUMAUIUGAQRUAUEAUBUCTUDT
      $.
  $}

  $( A version of Russell's paradox which is proven using proper substitution.
     (Contributed by Andrew Salmon, 18-Jun-2011.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  rusbcALT $p |- { x | x e/ x } e/ _V $=
    ( cv wnel cab cvv wcel wn wb pm5.19 wsbc csb sbcnel12g sbc8g df-nel csbvarg
    eleq12d notbid bitrid 3bitr3d mto mpbir ) ABZUBCZADZECUDEFZGUEUDUDFZUFGZHUF
    IUEUCAUDJAUDUBKZUHCZUFUGAUDUBUBELUCAUDEMUIUHUHFZGUEUGUHUHNUEUJUFUEUHUDUHUDA
    UDEOZUKPQRSTUDENUA $.

  ${
    $d x A $.
    $( Equality between two ways of saying "the complement of ` A ` ".
       (Contributed by Andrew Salmon, 15-Jul-2011.) $)
    compeq $p |- ( _V \ A ) = { x | -. x e. A } $=
      ( cv wcel wn cvv cdif velcomp eqabi ) ACBDEAFBGABHI $.
  $}

  $( The complement of ` A ` is not equal to ` A ` .  (Contributed by Andrew
     Salmon, 15-Jul-2011.)  (Proof shortened by BJ, 11-Nov-2021.) $)
  compne $p |- ( _V \ A ) =/= A $=
    ( cvv c0 wne cdif wceq id difeq1 difabs difid 3eqtr3g eqtr3d difeq2d eqtrdi
    vn0 dif0 necon3i ax-mp ) BCDBAEZADOSABCSAFZSBCTSBCEBTACBTSACTGTSAEAAESCSAAH
    BAIAJKZLMBPNUALQR $.

  $( Two ways of saying "the complement of a class abstraction".  (Contributed
     by Andrew Salmon, 15-Jul-2011.)  (Proof shortened by Mario Carneiro,
     11-Dec-2016.) $)
  compab $p |- ( _V \ { z | ph } ) = { z | -. ph } $=
    ( cvv cdif wn wceq cv wcel wb nfcv nfab1 nfdif cleqf notbii velcomp 3bitr4i
    cab abid mpgbir ) CABQZDZAEZBQZFBGZUAHZUDUCHZIBBUAUCBCTBCJABKLUBBKMUDTHZEUB
    UEUFUGAABRNBTOUBBRPS $.

  $( Contrapositive law for subsets.  (Contributed by Andrew Salmon,
     15-Jul-2011.) $)
  conss2 $p |- ( A C_ ( _V \ B ) <-> B C_ ( _V \ A ) ) $=
    ( cvv wss cdif wb ssv ssconb mp2an ) ACDBCDACBEDBCAEDFAGBGABCHI $.

  $( Contrapositive law for subsets.  (Contributed by Andrew Salmon,
     15-Jul-2011.) $)
  conss1 $p |- ( ( _V \ A ) C_ B <-> ( _V \ B ) C_ A ) $=
    ( cvv difcom ) CABD $.

  ${
    ralbidar.1 $e |- ( ph -> A. x e. A ph ) $.
    ralbidar.2 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( More general form of ~ ralbida .  (Contributed by Andrew Salmon,
       25-Jul-2011.) $)
    ralbidar $p |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $=
      ( cv wcel wi wal wral wb ex ralimi syl df-ral sylib pm2.43 pm5.74d alimi
      albi 3syl 3bitr4g ) ADHEIZBJZDKZUECJZDKZBDELCDELAUEUEBCMZJZJZDKZUFUHMZDKU
      GUIMAUKDELZUMAADELUOFAUKDEAUEUJGNOPUKDEQRULUNDULUEBCUEUJSTUAUFUHDUBUCBDEQ
      CDEQUD $.

    $( More general form of ~ rexbida .  (Contributed by Andrew Salmon,
       25-Jul-2011.) $)
    rexbidar $p |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) ) $=
      ( cv wcel wa wex wrex wb wi wal wral ex ralimi syl df-rex sylib exbi 3syl
      df-ral pm2.43 pm5.32d alimi 3bitr4g ) ADHEIZBJZDKZUICJZDKZBDELCDELAUIUIBC
      MZNZNZDOZUJULMZDOUKUMMAUODEPZUQAADEPUSFAUODEAUIUNGQRSUODEUDUAUPURDUPUIBCU
      IUNUEUFUGUJULDUBUCBDETCDETUH $.
  $}

  ${
    $d ph w $.  $d w x $.  $d w y $.  $d w z $.
    $( Theorem to aid use of the distinctor reduction theorem with ordered pair
       class abstraction.  (Contributed by Andrew Salmon, 25-Jul-2011.) $)
    dropab1 $p |- ( A. x x = y -> { <. x , z >. | ph } =
        { <. y , z >. | ph } ) $=
      ( vw cv wceq wal cop wa wex cab copab opeq1 sps eqeq2d anbi1d drex2 drex1
      df-opab abbidv 3eqtr4g ) BFZCFZGZBHZEFZUCDFZIZGZAJZDKZBKZELUGUDUHIZGZAJZD
      KZCKZELABDMACDMUFUMUREULUQBCUKUPBCDUFUJUOAUFUIUNUGUEUIUNGBUCUDUHNOPQRSUAA
      BDETACDETUB $.

    $( Theorem to aid use of the distinctor reduction theorem with ordered pair
       class abstraction.  (Contributed by Andrew Salmon, 25-Jul-2011.) $)
    dropab2 $p |- ( A. x x = y -> { <. z , x >. | ph } =
        { <. z , y >. | ph } ) $=
      ( vw cv wceq wal cop wa wex cab copab opeq2 sps eqeq2d anbi1d drex1 drex2
      df-opab abbidv 3eqtr4g ) BFZCFZGZBHZEFZDFZUCIZGZAJZBKZDKZELUGUHUDIZGZAJZC
      KZDKZELADBMADCMUFUMUREULUQBCDUKUPBCUFUJUOAUFUIUNUGUEUIUNGBUCUDUHNOPQRSUAA
      DBETADCETUB $.
  $}

  ${
    $d x A $.
    $( If the identity relation partially orders any class, then that class is
       the null class.  (Contributed by Andrew Salmon, 25-Jul-2011.) $)
    ipo0 $p |- ( _I Po A <-> A = (/) ) $=
      ( vx cid wpo c0 wceq cv wcel wbr weq equid vex ideq mpbir wn poirr eq0rdv
      ex mt2i po0 poeq2 mpbiri impbii ) ACDZAEFZUDBAUDBGZAHZUFUFCIZUHBBJBKUFUFB
      LMNUDUGUHOAUFCPRSQUEUDECDCTAECUAUBUC $.

    $( A class that is founded by the identity relation is null.  (Contributed
       by Andrew Salmon, 25-Jul-2011.) $)
    ifr0 $p |- ( _I Fr A <-> A = (/) ) $=
      ( vx cid wfr c0 wceq cv wcel wbr equid ideq mpbir wn frirr ex mt2i eq0rdv
      vex fr0 freq2 mpbiri impbii ) ACDZAEFZUCBAUCBGZAHZUEUECIZUGUEUEFBJUEUEBRK
      LUCUFUGMAUECNOPQUDUCECDCSAECTUAUB $.
  $}

  ${
    $d A x y $.  $d F x y $.
    $( Explicit substitution of a value of a function into a wff.  (Contributed
       by Andrew Salmon, 1-Aug-2011.) $)
    fvsb $p |- ( E! y A F y -> ( [. ( F ` A ) / x ]. ph <->
        E. x ( A. y ( A F y <-> y = x ) /\ ph ) ) ) $=
      ( cfv wsbc cv wbr cio weu wceq wb wal wa wex df-fv dfsbcq ax-mp iotasbc
      bitrid ) ABDEFZGZABDCHZEIZCJZGZUECKUEUDBHLMCNAOBPUBUFLUCUGMCDEQABUBUFRSUE
      ACBTUA $.

    fveqsb.2 $e |- ( x = ( F ` A ) -> ( ph <-> ps ) ) $.
    fveqsb.3 $e |- F/ x ps $.
    $( Implicit substitution of a value of a function into a wff.  (Contributed
       by Andrew Salmon, 1-Aug-2011.) $)
    fveqsb $p |- ( E! y A F y -> ( ps <->
        E. x ( A. y ( A F y <-> y = x ) /\ ph ) ) ) $=
      ( cfv wsbc cv wbr weu weq wb wal wa wex cvv wcel fvex sbciegf ax-mp fvsb
      bitr3id ) BACEFIZJZEDKFLZDMUHDCNODPAQCRUFSTUGBOEFUAABCUFSHGUBUCACDEFUDUE
      $.
  $}

  $( A Cartesian product exists iff its converse does.  Corollary 6.9(1) in
     [TakeutiZaring] p. 26.  (Contributed by Andrew Salmon, 13-Nov-2011.) $)
  xpexb $p |- ( ( A X. B ) e. _V <-> ( B X. A ) e. _V ) $=
    ( cxp cvv wcel ccnv cnvxp cnvexg eqeltrrid impbii ) ABCZDEZBACZDEZLMKFDABGK
    DHINKMFDBAGMDHIJ $.

  $( An element of a transitive set is a proper subset of it.  Theorem 7.2 in
     [TakeutiZaring] p. 35.  Unlike ~ tz7.2 , ~ ax-reg is required for its
     proof.  (Contributed by Andrew Salmon, 13-Nov-2011.) $)
  trelpss $p |- ( ( Tr A /\ B e. A ) -> B C. A ) $=
    ( wtr wcel wa wss wne wpss cep wfr zfregfr tz7.2 mp3an2 df-pss sylibr ) ACZ
    BADZEBAFBAGEZBAHPAIJQRAKABLMBANO $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Arithmetic
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Generalization of commutative law for addition.  Simplifies proofs dealing
     with vectors.  However, it is dependent on our particular definition of
     ordered pair.  (Contributed by Andrew Salmon, 28-Jan-2012.)  (Revised by
     Mario Carneiro, 6-May-2015.) $)
  addcomgi $p |- ( A + B ) = ( B + A ) $=
    ( cc wcel wa caddc co wceq addcom cxp ax-addf fdmi ndmovcom pm2.61i ) ACDBC
    DEABFGBAFGHABIABCFCCJCFKLMN $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Geometry
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c +r -r .v PtDf RR3 $( plane3 $) line3 $.

  $( Introduce the operation of vector addition. $)
  cplusr $a class +r $.

  $( Introduce the operation of vector subtraction. $)
  cminusr $a class -r $.

  $( Introduce the operation of scalar multiplication. $)
  ctimesr $a class .v $.

  $( ` PtDf ` is a predicate that is crucial for the definition of lines as
     well as proving a number of important theorems. $)
  cptdfc $a class PtDf ( A , B ) $.

  $( ` RR3 ` is a class. $)
  crr3c $a class RR3 $.

  $( ` plane3 ` is a class. $)
  $( cplane3 $a class plane3 $. $)

  $( ` line3 ` is a class. $)
  cline3 $a class line3 $.

  ${
    $d v x y A $.  $d v x y B $.
    $( Define the operation of vector addition.  (Contributed by Andrew Salmon,
       27-Jan-2012.) $)
    df-addr $a |- +r = ( x e. _V , y e. _V |->
        ( v e. RR |-> ( ( x ` v ) + ( y ` v ) ) ) ) $.

    $( Define the operation of vector subtraction.  (Contributed by Andrew
       Salmon, 27-Jan-2012.) $)
    df-subr $a |- -r = ( x e. _V , y e. _V |->
        ( v e. RR |-> ( ( x ` v ) - ( y ` v ) ) ) ) $.

    $( Define the operation of scalar multiplication.  (Contributed by Andrew
       Salmon, 27-Jan-2012.) $)
    df-mulv $a |- .v = ( x e. _V , y e. _V |->
        ( v e. RR |-> ( x x. ( y ` v ) ) ) ) $.

    $( Value of the operation of vector addition.  (Contributed by Andrew
       Salmon, 27-Jan-2012.) $)
    addrval $p |- ( ( A e. C /\ B e. D ) -> ( A +r B ) =
      ( v e. RR |-> ( ( A ` v ) + ( B ` v ) ) ) ) $=
      ( vx vy wcel cvv cplusr co cr cv cfv caddc cmpt wceq elex wa fveq1 ovmpoa
      oveqan12d mpteq2dv df-addr reex mptex syl2an ) BDHBIHCIHBCJKALAMZBNZUHCNZ
      OKZPZQCEHBDRCERFGBCIIALUHFMZNZUHGMZNZOKZPULJUMBQZUOCQZSALUQUKURUSUNUIUPUJ
      OUHUMBTUHUOCTUBUCFGAUDALUKUEUFUAUG $.

    $( Value of the operation of vector subtraction.  (Contributed by Andrew
       Salmon, 27-Jan-2012.) $)
    subrval $p |- ( ( A e. C /\ B e. D ) -> ( A -r B ) =
      ( v e. RR |-> ( ( A ` v ) - ( B ` v ) ) ) ) $=
      ( vx vy wcel cvv cminusr co cr cv cfv cmin cmpt wceq elex wa fveq1 ovmpoa
      oveqan12d mpteq2dv df-subr reex mptex syl2an ) BDHBIHCIHBCJKALAMZBNZUHCNZ
      OKZPZQCEHBDRCERFGBCIIALUHFMZNZUHGMZNZOKZPULJUMBQZUOCQZSALUQUKURUSUNUIUPUJ
      OUHUMBTUHUOCTUBUCFGAUDALUKUEUFUAUG $.

    $( Value of the operation of scalar multiplication.  (Contributed by Andrew
       Salmon, 27-Jan-2012.) $)
    mulvval $p |- ( ( A e. C /\ B e. D ) -> ( A .v B ) =
      ( v e. RR |-> ( A x. ( B ` v ) ) ) ) $=
      ( vx vy wcel cvv ctimesr co cr cv cfv cmul cmpt wceq elex wa fveq1 oveq12
      sylan2 mpteq2dv df-mulv reex mptex ovmpoa syl2an ) BDHBIHCIHBCJKALBAMZCNZ
      OKZPZQCEHBDRCERFGBCIIALFMZUIGMZNZOKZPULJUMBQZUNCQZSALUPUKURUQUOUJQUPUKQUI
      UNCTUMBUOUJOUAUBUCFGAUDALUKUEUFUGUH $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x D $.
    $( Vector addition at a value.  The operation takes each vector ` A ` and
       ` B ` and forms a new vector whose values are the sum of each of the
       values of ` A ` and ` B ` .  (Contributed by Andrew Salmon,
       27-Jan-2012.) $)
    addrfv $p |- ( ( A e. E /\ B e. D /\ C e. RR ) -> ( ( A +r B ) ` C ) =
        ( ( A ` C ) + ( B ` C ) ) ) $=
      ( vx wcel cr cplusr co caddc wceq wa cv cmpt addrval fveq1d fveq2 oveq12d
      cfv eqid ovex fvmpt sylan9eq 3impa ) AEGZBDGZCHGZCABIJZTZCATZCBTZKJZLUFUG
      MZUHUJCFHFNZATZUOBTZKJZOZTUMUNCUIUSFABEDPQFCURUMHUSUOCLUPUKUQULKUOCARUOCB
      RSUSUAUKULKUBUCUDUE $.

    $( Vector subtraction at a value.  (Contributed by Andrew Salmon,
       27-Jan-2012.) $)
    subrfv $p |- ( ( A e. E /\ B e. D /\ C e. RR ) -> ( ( A -r B ) ` C ) =
        ( ( A ` C ) - ( B ` C ) ) ) $=
      ( vx wcel cr cminusr co cmin wceq wa cv cmpt subrval fveq1d fveq2 oveq12d
      cfv eqid ovex fvmpt sylan9eq 3impa ) AEGZBDGZCHGZCABIJZTZCATZCBTZKJZLUFUG
      MZUHUJCFHFNZATZUOBTZKJZOZTUMUNCUIUSFABEDPQFCURUMHUSUOCLUPUKUQULKUOCARUOCB
      RSUSUAUKULKUBUCUDUE $.

    $( Scalar multiplication at a value.  (Contributed by Andrew Salmon,
       27-Jan-2012.) $)
    mulvfv $p |- ( ( A e. E /\ B e. D /\ C e. RR ) -> ( ( A .v B ) ` C ) =
        ( A x. ( B ` C ) ) ) $=
      ( vx wcel cr ctimesr co cfv cmul wceq wa cmpt mulvval fveq1d fveq2 oveq2d
      cv eqid ovex fvmpt sylan9eq 3impa ) AEGZBDGZCHGZCABIJZKZACBKZLJZMUFUGNZUH
      UJCFHAFTZBKZLJZOZKULUMCUIUQFABEDPQFCUPULHUQUNCMUOUKALUNCBRSUQUAAUKLUBUCUD
      UE $.

    $( Vector addition produces a function.  (Contributed by Andrew Salmon,
       27-Jan-2012.) $)
    addrfn $p |- ( ( A e. C /\ B e. D ) -> ( A +r B ) Fn RR ) $=
      ( vx wcel wa cplusr co cr wfn cv cfv cmpt ovex eqid fnmpti addrval fneq1d
      caddc mpbiri ) ACFBDFGZABHIZJKEJELZAMZUDBMZTIZNZJKEJUGUHUEUFTOUHPQUBJUCUH
      EABCDRSUA $.

    $( Vector subtraction produces a function.  (Contributed by Andrew Salmon,
       27-Jan-2012.) $)
    subrfn $p |- ( ( A e. C /\ B e. D ) -> ( A -r B ) Fn RR ) $=
      ( vx wcel wa cminusr co wfn cfv cmin cmpt ovex eqid fnmpti subrval fneq1d
      cr cv mpbiri ) ACFBDFGZABHIZSJESETZAKZUDBKZLIZMZSJESUGUHUEUFLNUHOPUBSUCUH
      EABCDQRUA $.

    $( Scalar multiplication producees a function.  (Contributed by Andrew
       Salmon, 27-Jan-2012.) $)
    mulvfn $p |- ( ( A e. C /\ B e. D ) -> ( A .v B ) Fn RR ) $=
      ( vx wcel wa ctimesr co wfn cfv cmul cmpt ovex eqid fnmpti mulvval fneq1d
      cr cv mpbiri ) ACFBDFGZABHIZSJESAETBKZLIZMZSJESUEUFAUDLNUFOPUBSUCUFEABCDQ
      RUA $.

    $( Vector addition is commutative.  (Contributed by Andrew Salmon,
       28-Jan-2012.) $)
    addrcom $p |- ( ( A e. C /\ B e. D ) -> ( A +r B ) = ( B +r A ) ) $=
      ( vx wcel wa cplusr co cr wfn wceq addrfn ancoms cv cfv wral caddc addrfv
      w3a addcomgi 3com12 3eqtr4a 3expia ralrimiv eqfnfv syl5ibrcom mp2and ) AC
      FZBDFZGZABHIZJKZBAHIZJKZULUNLZABCDMUJUIUOBADCMNUKUPUMUOGEOZULPZUQUNPZLZEJ
      QUKUTEJUIUJUQJFZUTUIUJVATUQAPZUQBPZRIVCVBRIZURUSVBVCUAABUQDCSUJUIVAUSVDLB
      AUQCDSUBUCUDUEEJULUNUFUGUH $.
  $}

  ${
    $d x y z A $.  $d x B $.
    $( Define the predicate ` PtDf ` , which is a utility definition used to
       shorten definitions and simplify proofs.  (Contributed by Andrew Salmon,
       15-Jul-2012.) $)
    df-ptdf $a |- PtDf ( A , B ) = ( x e. RR |-> ( ( ( x .v ( B -r A ) )
        +v A ) " { 1 , 2 , 3 } ) ) $.

    $( Define the set of all points ` RR3 ` .  We define each point ` A ` as a
       function to allow the use of vector addition and subtraction as well as
       scalar multiplication in our proofs.  (Contributed by Andrew Salmon,
       15-Jul-2012.) $)
    df-rr3 $a |- RR3 = ( RR ^m { 1 , 2 , 3 } ) $.

    $( Define the set of all lines.  A line is an infinite subset of ` RR3 `
       that satisfies a ` PtDf ` property.  (Contributed by Andrew Salmon,
       15-Jul-2012.) $)
    df-line3 $a |- line3 = { x e. ~P RR3 | ( 2o ~<_ x /\
        A. y e. x A. z e. x ( z =/= y -> ran PtDf ( y , z ) = x ) ) } $.
  $}

$( (End of Andrew Salmon's mathbox.) $)
