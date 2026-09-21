$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Adhemar
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Replacement of a nested antecedent with an outer antecedent.  Commuted
     simplificated form of elimination of a nested antecedent.  Also holds
     intuitionistically.  Polish prefix notation:  CCCpqrCsCqr .  (Contributed
     by ADH, 10-Nov-2023.)  (Proof modification is discouraged.) $)
  adh-jarrsc $p |- ( ( ( ph -> ps ) -> ch ) -> ( th -> ( ps -> ch ) ) ) $=
    ( wi jarr ax-1 ax-mp pm2.04 ) DABECEZBCEZEZEZJDKEELMABCFLDGHDJKIH $.
  $( $j usage 'adh-jarrsc' avoids 'ax-3'; $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Minimal implicational calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Minimal implicational calculus, or intuitionistic implicational calculus, or
  positive implicational calculus, is the implicational fragment of minimal
  calculus (which is also the implicational fragment of intuitionistic calculus
  and of positive calculus).  It is sometimes called "C-pure intuitionism"
  since the letter C is used to denote implication in Polish prefix notation.
  It can be axiomatized by the inference rule of _modus ponens_ ~ ax-mp
  together with the axioms { ~ ax-1 , ~ ax-2 } (sometimes written KS), or with
  { ~ imim1 , ~ ax-1 , ~ pm2.43 } (written B'KW), or with { ~ imim2 ,
  ~ pm2.04 , ~ ax-1 , ~ pm2.43 } (written BCKW), or with the single axiom
  ~ adh-minim , or with the single axiom ~ adh-minimp .  This section proves
  first ~ adh-minim from { ~ ax-1 , ~ ax-2 }, followed by the converse, due to
  Ivo Thomas; and then it proves ~ adh-minimp from { ~ ax-1 , ~ ax-2 }, also
  followed by the converse, also due to Ivo Thomas.

  Sources for this section are
  * Carew Arthur Meredith, _A single axiom of positive logic_, The Journal of
    Computing Systems, volume 1, issue 3, July 1953, pages 169--170;
  * Ivo Thomas, _On Meredith's sole positive axiom_, Notre Dame Journal of
    Formal Logic, volume XV, number 3, July 1974, page 477, in which the
    derivations of { ~ ax-1 , ~ ax-2 } from ~ adh-minim are shortened (compared
    to Meredith's derivations in the aforementioned paper);
  * Carew Arthur Meredith and Arthur Norman Prior, _Notes on the axiomatics of
    the propositional calculus_, Notre Dame Journal of Formal Logic, volume IV,
    number 3, July 1963, pages 171--187; and
  * the webpage
    ~ https://web.ics.purdue.edu/~~dulrich/C-pure-intuitionism-page.htm
    on Dolph Edward "Ted" Ulrich's website, where these and other single
    axioms for the minimal implicational calculus are listed.

  This entire section also holds intuitionistically.

  Users of the Polish prefix notation also often use a compact notation for
  proof derivations known as the D-notation where "D" stands for "condensed
  Detachment".  For instance, "D21" means detaching ~ ax-1 from ~ ax-2 , that
  is, using _modus ponens_ ~ ax-mp with ~ ax-1 as minor premise and ~ ax-2 as
  major premise.  When the numbered lemmas surpass 10, dots are added between
  the numbers.  D-strings are accepted by the grammar
  Dundotted := digit | "D" Dundotted Dundotted ;
  Ddotted := digit + | "D" Ddotted "." Ddotted ;
  Dstr := Dundotted | Ddotted .

  (Contributed by BJ, 11-Apr-2021.)
  (Revised by ADH, 10-Nov-2023.)

$)

  $( A single axiom for minimal implicational calculus, due to Meredith.  Other
     single axioms of the same length are known, but it is thought to be the
     minimal length.  This is the axiom from Carew Arthur Meredith, _A single
     axiom of positive logic_, The Journal of Computing Systems, volume 1,
     issue 3, July 1953, pages 169--170.  A two-line review by Alonzo Church of
     this article can be found in The Journal of Symbolic Logic, volume 19,
     issue 2, June 1954, page 144, ~ https://doi.org/10.2307/2268914 .  Known
     as "HI-1" on Dolph Edward "Ted" Ulrich's web page.  In the next 6 lemmas
     and 3 theorems, ~ ax-1 and ~ ax-2 are derived from this single axiom in 16
     detachments (instances of ~ ax-mp ) in total.  Polish prefix notation:
     CCCpqrCsCCqCrtCqt .  (Contributed by ADH, 10-Nov-2023.) $)
  adh-minim $p |- ( ( ( ph -> ps ) -> ch ) ->
                      ( th -> ( ( ps -> ( ch -> ta ) ) -> ( ps -> ta ) ) ) ) $=
    ( wi pm2.04 adh-jarrsc ax-2 imim2 ax-mp 4syl ax-1 ) DABFCFZBCEFFZBEFZFZFZFZ
    NDQFFRSONPFZFROCPFZOUATBCEGZCBEGZUBNUAPFZFZUATFNUABCFZFZFZUEABCUAHUGUDFZUHU
    EFUAUFPFZFZUIUAOFZUKUCOUJFULUKFBCEIOUJUAJKKUAUFPIKUGUDNJKKNUAPGKLONPGKRDMKD
    NQGK $.
  $( $j usage 'adh-minim' avoids 'ax-3'; $)

  $( First lemma for the derivation of ~ ax-1 and ~ ax-2 from ~ adh-minim and
     ~ ax-mp .  Polish prefix notation:  CpCCqCCrCCsCqtCstuCqu .  (Contributed
     by ADH, 10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minim-ax1-ax2-lem1 $p |- ( ph -> ( ( ps -> ( ( ch -> ( ( th ->
            ( ps -> ta ) ) -> ( th -> ta ) ) ) -> et ) ) -> ( ps -> et ) ) ) $=
    ( wze wi adh-minim ax-mp ) GDHZBHCDBEHHDEHHHZHABLFHHBFHHHGDBCEIKBLAFIJ $.

  $( Second lemma for the derivation of ~ ax-1 and ~ ax-2 from ~ adh-minim and
     ~ ax-mp .  Polish prefix notation:  CCpCCqCCrCpsCrstCpt .  (Contributed by
     ADH, 10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minim-ax1-ax2-lem2 $p |- ( ( ph -> ( ( ps ->
    ( ( ch -> ( ph -> th ) ) -> ( ch -> th ) ) ) -> ta ) ) -> ( ph -> ta ) ) $=
    ( wet wze wsi wrh wmu wla wi adh-minim-ax1-ax2-lem1 ax-mp ) FGHIGJLLIJLLLKL
    LGKLLLZABCADLLCDLLLELLAELLFGHIJKMOABCDEMN $.

  $( Third lemma for the derivation of ~ ax-1 and ~ ax-2 from ~ adh-minim and
     ~ ax-mp .  Polish prefix notation:  CCpCqrCqCsCpr .  (Contributed by ADH,
     10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minim-ax1-ax2-lem3 $p |- ( ( ph -> ( ps -> ch ) ) ->
                                          ( ps -> ( th -> ( ph -> ch ) ) ) ) $=
    ( wi adh-minim-ax1-ax2-lem1 adh-minim-ax1-ax2-lem2 ax-mp ) ABCEEZBDIACEZEED
    JEZEEBKEZEEILEIBDACKFIBDJLGH $.

  $( Fourth lemma for the derivation of ~ ax-1 and ~ ax-2 from ~ adh-minim and
     ~ ax-mp .  Polish prefix notation:  CCCpqrCCqCrsCqs .  (Contributed by
     ADH, 10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minim-ax1-ax2-lem4 $p |- ( ( ( ph -> ps ) -> ch ) ->
                                ( ( ps -> ( ch -> th ) ) -> ( ps -> th ) ) ) $=
    ( wet wze wsi wi adh-minim adh-minim-ax1-ax2-lem2 ax-mp ) ABHCHZEFLGHHFGHHH
    ZBCDHHBDHHZHHLNHABCMDILEFGNJK $.

  $( Derivation of ~ ax-1 from ~ adh-minim and ~ ax-mp .  Carew Arthur Meredith
     derived ~ ax-1 in _A single axiom of positive logic_, The Journal of
     Computing Systems, volume 1, issue 3, July 1953, pages 169--170.  However,
     here we follow the shortened derivation by Ivo Thomas, _On Meredith's sole
     positive axiom_, Notre Dame Journal of Formal Logic, volume XV, number 3,
     July 1974, page 477.  Polish prefix notation:  CpCqp .  (Contributed by
     ADH, 10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minim-ax1 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wch wth wta wet wze wsi wi adh-minim-ax1-ax2-lem1 adh-minim-ax1-ax2-lem3
    adh-minim-ax1-ax2-lem4 ax-mp ) ABCDBEIIDEIIIZAIZIZBAIZIIZAQIZABCDEAJQPIZRSI
    QBFGBHIIGHIIIZOIIZPIIZTQBFGHOJNQIUBIUCTINBAUAKNQUBPLMMBAPQLMM $.

  $( Fifth lemma for the derivation of ~ ax-2 from ~ adh-minim and ~ ax-mp .
     Polish prefix notation:  CpCCCqrsCCrCstCrt .  (Contributed by ADH,
     10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minim-ax2-lem5 $p |- ( ph -> ( ( ( ps -> ch ) -> th ) ->
                              ( ( ch -> ( th -> ta ) ) -> ( ch -> ta ) ) ) ) $=
    ( wi adh-minim-ax1-ax2-lem4 adh-minim-ax1 ax-mp ) BCFDFCDEFFCEFFFZAJFBCDEGJ
    AHI $.

  $( Sixth lemma for the derivation of ~ ax-2 from ~ adh-minim and ~ ax-mp .
     Polish prefix notation:  CCpCCCCqrsCCrCstCrtuCpu .  (Contributed by ADH,
     10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minim-ax2-lem6 $p |- ( ( ph -> ( ( ( ( ps -> ch ) -> th ) ->
    ( ( ch -> ( th -> ta ) ) -> ( ch -> ta ) ) ) -> et ) ) -> ( ph -> et ) ) $=
    ( wze wi adh-minim-ax2-lem5 adh-minim-ax1-ax2-lem4 ax-mp ) GAHZBCHDHCDEHHCE
    HHHZHAMFHHAFHHLBCDEIGAMFJK $.

  $( Derivation of a commuted form of ~ ax-2 from ~ adh-minim and ~ ax-mp .
     Polish prefix notation:  CCpqCCpCqrCpr .  (Contributed by ADH,
     10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minim-ax2c $p |- ( ( ph -> ps ) ->
                                ( ( ph -> ( ps -> ch ) ) -> ( ph -> ch ) ) ) $=
    ( wth wta wet wze wsi wrh wmu wla adh-minim-ax2-lem5 adh-minim-ax1-ax2-lem4
    wi adh-minim-ax2-lem6 ax-mp ) ABNZDENFNEFGNNEGNNNZANZBNZABCNNACNNZNNZQUANZQ
    RABCLSQNTNZUBUCNHINJNIJKNNIKNNNZSNZANZUDUFUEANNUGUEDEFGAOUFHIJKAOPUESABMPSQ
    TUAMPP $.

  $( Derivation of ~ ax-2 from ~ adh-minim and ~ ax-mp .  Carew Arthur Meredith
     derived ~ ax-2 in _A single axiom of positive logic_, The Journal of
     Computing Systems, volume 1, issue 3, July 1953, pages 169--170.  However,
     here we follow the shortened derivation by Ivo Thomas, _On Meredith's sole
     positive axiom_, Notre Dame Journal of Formal Logic, volume XV, number 3,
     July 1974, page 477.  Polish prefix notation:  CCpCqrCCpqCpr .
     (Contributed by ADH, 10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minim-ax2 $p |- ( ( ph -> ( ps -> ch ) ) ->
                                          ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wth wta wi adh-minim-ax2c adh-minim-ax1-ax2-lem3 ax-mp adh-minim-ax2-lem6
    wet wze ) ABCFFZDEFKFEKLFFELFFFZABFZACFZFZFFZMQFOMPFFRABCGOMPNHIMDEKLQJI $.

  $( Derivation of ~ id (reflexivity of implication, PM *2.08 WhiteheadRussell
     p. 101) from ~ adh-minim-ax1 , ~ adh-minim-ax2 , and ~ ax-mp .  It uses
     the derivation written DD211 in D-notation.  (See head comment for an
     explanation.)  Polish prefix notation:  Cpp .  (Contributed by ADH,
     10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minim-idALT $p |- ( ph -> ph ) $=
    ( wps wi adh-minim-ax1 adh-minim-ax2 ax-mp ) ABACZCZAACZABDAGACCHICAGDAGAEF
    F $.

  $( Derivation of ~ pm2.43 WhiteheadRussell p. 106 (also called "hilbert" or
     "W") from ~ adh-minim-ax1 , ~ adh-minim-ax2 , and ~ ax-mp .  It uses the
     derivation written DD22D21 in D-notation.  (See head comment for an
     explanation.)  (Contributed by ADH, 10-Nov-2023.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  adh-minim-pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi adh-minim-ax1 adh-minim-ax2 ax-mp ) AABCZCZAACZCZHGCZAGACCJAGDAGAEFHIG
    CCJKCAABEHIGEFF $.

  $( Another single axiom for minimal implicational calculus, due to Meredith.
     Other single axioms of the same length are known, but it is thought to be
     the minimal length.  Among single axioms of this length, it is the one
     with simplest antecedents (i.e., in the corresponding ordering of binary
     trees which first compares left subtrees, it is the first one).  Known as
     "HI-2" on Dolph Edward "Ted" Ulrich's web page.  In the next 4 lemmas and
     5 theorems, ~ ax-1 and ~ ax-2 are derived from this other single axiom in
     20 detachments (instances of ~ ax-mp ) in total.  Polish prefix notation:
     CpCCqrCCCsqCrtCqt ; or CtCCpqCCCspCqrCpr in Carew Arthur Meredith and
     Arthur Norman Prior, _Notes on the axiomatics of the propositional
     calculus_, Notre Dame Journal of Formal Logic, volume IV, number 3, July
     1963, pages 171--187, on page 180.  (Contributed by BJ, 4-Apr-2021.)
     (Revised by ADH, 10-Nov-2023.) $)
  adh-minimp $p |- ( ph ->
  ( ( ps -> ch ) -> ( ( ( th -> ps ) -> ( ch -> ta ) ) -> ( ps -> ta ) ) ) ) $=
    ( wi jarr ax-2 imim2 ax-mp pm2.04 ax-1 ) BCFZDBFCEFZFZBEFZFFZAQFOMPFZFZQOBN
    FZFZSDBNGTRFUASFBCEHTROIJJOMPKJQALJ $.
  $( $j usage 'adh-minimp' avoids 'ax-3'; $)

  $( First lemma for the derivation of ~ jarr , ~ imim1 , and a commuted form
     of ~ ax-2 , and indirectly ~ ax-1 and ~ ax-2 , from ~ adh-minimp and
     ~ ax-mp .  Polish prefix notation:  CCpqCCCrpCqsCps .  (Contributed by
     ADH, 10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minimp-jarr-imim1-ax2c-lem1 $p |- ( ( ph -> ps ) ->
                      ( ( ( ch -> ph ) -> ( ps -> th ) ) -> ( ph -> th ) ) ) $=
    ( wet wze wsi wrh wmu wi adh-minimp ax-mp ) EFGJHFJGIJJFIJJJJZABJCAJBDJJADJ
    JJEFGHIKMABCDKL $.

  $( Second lemma for the derivation of ~ jarr , and indirectly ~ ax-1 , a
     commuted form of ~ ax-2 , and ~ ax-2 proper, from ~ adh-minimp and
     ~ ax-mp .  Polish prefix notation:  CCCpqCCCrsCCCtrCsuCruvCqv .
     (Contributed by ADH, 10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minimp-jarr-lem2 $p |- ( ( ( ph -> ps ) ->
                   ( ( ( ch -> th ) -> ( ( ( ta -> ch ) -> ( th -> et ) ) ->
                                ( ch -> et ) ) ) -> ze ) ) -> ( ps -> ze ) ) $=
    ( wi adh-minimp adh-minimp-jarr-imim1-ax2c-lem1 ax-mp ) BCDHECHDFHHCFHHHZHA
    BHLGHHBGHHBCDEFIBLAGJK $.

  $( Third lemma for the derivation of ~ jarr and a commuted form of ~ ax-2 ,
     and indirectly ~ ax-1 and ~ ax-2 proper , from ~ adh-minimp and ~ ax-mp .
     Polish prefix notation:  CCCCpqCCCrpCqsCpstt .  (Contributed by ADH,
     10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minimp-jarr-ax2c-lem3 $p |- ( ( ( ( ph -> ps ) ->
      ( ( ( ch -> ph ) -> ( ps -> th ) ) -> ( ph -> th ) ) ) -> ta ) -> ta ) $=
    ( wet wze wsi wrh wmu wi adh-minimp-jarr-lem2 ax-mp ) FGHKIGKHJKKGJKKKZKZAB
    KCAKBDKKADKKKEKZKNEKKPEKFNABCDELOPGHIJELM $.

  $( Derivation of ~ jarr (also called "syll-simp") from ~ minimp and ~ ax-mp .
     Polish prefix notation:  CCCpqrCqr .  (Contributed by BJ, 4-Apr-2021.)
     (Revised by ADH, 10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minimp-sylsimp $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    ( wi adh-minimp-jarr-ax2c-lem3 adh-minimp-jarr-imim1-ax2c-lem1 ax-mp
    adh-minimp-jarr-lem2 ) ABDZICDZCDZDZJBCDZDZIIDZOODODDZJDJDZLIIIIJEIQDJIDQKD
    DLDDQLDIQJKFIQJIPCLHGGJLDBJDLMDDNDDLNDJLBMFJLBJACNHGG $.

  $( Derivation of ~ ax-1 from ~ adh-minimp and ~ ax-mp .  Polish prefix
     notation:  CpCqp .  (Contributed by BJ, 4-Apr-2021.)  (Revised by ADH,
     10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minimp-ax1 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wi adh-minimp-sylsimp ax-mp ) ABCZACBACZCAGCABADFAGDE $.

  $( Derivation of ~ imim1 ("left antimonotonicity of implication", theorem
     *2.06 of [WhiteheadRussell] p. 100) from ~ adh-minimp and ~ ax-mp .
     Polish prefix notation:  CCpqCCqrCpr .  (Contributed by ADH, 10-Nov-2023.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  adh-minimp-imim1 $p |- ( ( ph -> ps ) ->
                                          ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wth wrh wi adh-minimp-sylsimp adh-minimp-jarr-imim1-ax2c-lem1 ax-mp ) DAF
    ZBCFZFACFZFZKLFZFZABFZNFZJKLGEPFZOFQFZOQFPMFSABDCHPMENHIROQGII $.

  $( Derivation of a commuted form of ~ ax-2 from ~ adh-minimp and ~ ax-mp .
     Polish prefix notation:  CCpqCCpCqrCpr .  (Contributed by BJ, 4-Apr-2021.)
     (Revised by ADH, 10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minimp-ax2c $p |- ( ( ph -> ps ) ->
                                ( ( ph -> ( ps -> ch ) ) -> ( ph -> ch ) ) ) $=
    ( wth wta wet wze adh-minimp-jarr-ax2c-lem3 adh-minimp-jarr-imim1-ax2c-lem1
    wi ax-mp adh-minimp-sylsimp adh-minimp-imim1 ) DEJFDJEGJJDGJJJZAJZBCJZJZACJ
    ZJZAPJZRJZJZABJZUAJZTTJZSJUAJZUBTQJZUFOOJZTJQJZUGOAJUIDEFGAHOAOPIKUHTQLKTQT
    RIKUESUALKUCSJUBUDJABNCIUCSUAMKK $.

  $( Fourth lemma for the derivation of ~ ax-2 from ~ adh-minimp and ~ ax-mp .
     Polish prefix notation:  CpCCqCprCqr .  (Contributed by ADH, 10-Nov-2023.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  adh-minimp-ax2-lem4 $p |- ( ph -> ( ( ps ->
                                          ( ph -> ch ) ) -> ( ps -> ch ) ) ) $=
    ( wi adh-minimp-ax2c adh-minimp-sylsimp ax-mp ) BADBACDDBCDDZDAHDBACEBAHFG
    $.

  $( Derivation of ~ ax-2 from ~ adh-minimp and ~ ax-mp .  Polish prefix
     notation:  CCpCqrCCpqCpr .  (Contributed by BJ, 4-Apr-2021.)  (Revised by
     ADH, 10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minimp-ax2 $p |- ( ( ph -> ( ps -> ch ) ) ->
                                          ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi adh-minimp-ax2-lem4 adh-minimp-ax2c ax-mp ) ABCDDZABDZHACDZDDZIJDZDDZH
    LDZHIJEKMNDABCFKHLEGG $.

  $( Derivation of ~ id (reflexivity of implication, PM *2.08 WhiteheadRussell
     p. 101) from ~ adh-minimp-ax1 , ~ adh-minimp-ax2 , and ~ ax-mp .  It uses
     the derivation written DD211 in D-notation.  (See head comment for an
     explanation.)  Polish prefix notation:  Cpp .  (Contributed by ADH,
     10-Nov-2023.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  adh-minimp-idALT $p |- ( ph -> ph ) $=
    ( wps wi adh-minimp-ax1 adh-minimp-ax2 ax-mp ) ABACZCZAACZABDAGACCHICAGDAGA
    EFF $.

  $( Derivation of ~ pm2.43 WhiteheadRussell p. 106 (also called "hilbert" or
     "W") from ~ adh-minimp-ax1 , ~ adh-minimp-ax2 , and ~ ax-mp .  It uses the
     derivation written DD22D21 in D-notation.  (See head comment for an
     explanation.)  Polish prefix notation:  CCpCpqCpq .  (Contributed by BJ,
     31-May-2021.)  (Revised by ADH, 10-Nov-2023.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  adh-minimp-pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi adh-minimp-ax1 adh-minimp-ax2 ax-mp ) AABCZCZAACZCZHGCZAGACCJAGDAGAEFH
    IGCCJKCAABEHIGEFF $.

$( (End of Adhemar's mathbox.) $)
