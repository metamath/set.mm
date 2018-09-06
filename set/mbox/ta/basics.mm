$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Propositional Calculus - misc additions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    bian1d.1 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
    $( Adding a superfluous conjunct in a biconditionnal.  (Contributed by
       Thierry Arnoux, 26-Feb-2017.) $)
    bian1d $p |- ( ph -> ( ( ch /\ ps ) <-> ( ch /\ th ) ) ) $=
      ( wa biimpd adantld wi simpl a1i biimprd jcad impbid ) ACBFCDFZABOCABOEGH
      AOCBOCIACDJKABOELMN $.
  $}

  $( Distributive law for disjunction.  (Contributed by Thierry Arnoux,
     3-Jul-2017.) $)
  or3di $p |- ( ( ph \/ ( ps /\ ch /\ ta ) ) <->
                          ( ( ph \/ ps ) /\ ( ph \/ ch ) /\ ( ph \/ ta ) ) ) $=
    ( w3a wo wa df-3an orbi2i ordi anbi1i 3bitri bitr4i ) ABCDEZFZABFZACFZGZADF
    ZGZPQSEOABCGZDGZFAUAFZSGTNUBABCDHIAUADJUCRSABCJKLPQSHM $.

  $( Distributive law for disjunction.  (Contributed by Thierry Arnoux,
     3-Jul-2017.) $)
  or3dir $p |- ( ( ( ph /\ ps /\ ch ) \/ ta ) <->
              ( ( ph \/ ta ) /\ ( ps \/ ta ) /\ ( ch \/ ta ) ) ) $=
    ( w3a wo or3di orcom 3anbi123i 3bitr3i ) DABCEZFDAFZDBFZDCFZEKDFADFZBDFZCDF
    ZEDABCGDKHLOMPNQDAHDBHDCHIJ $.

  ${
    3o1cs.1 $e |- ( ( ph \/ ps \/ ch ) -> th ) $.
    $( Deduction eliminating disjunct.  (Contributed by Thierry Arnoux,
       19-Dec-2016.) $)
    3o1cs $p |- ( ph -> th ) $=
      ( wo w3o df-3or sylbir orcs ) ABDABFZCDKCFABCGDABCHEIJJ $.

    $( Deduction eliminating disjunct.  (Contributed by Thierry Arnoux,
       19-Dec-2016.) $)
    3o2cs $p |- ( ps -> th ) $=
      ( wo w3o df-3or sylbir orcs olcs ) ABDABFZCDLCFABCGDABCHEIJK $.

    $( Deduction eliminating disjunct.  (Contributed by Thierry Arnoux,
       19-Dec-2016.) $)
    3o3cs $p |- ( ch -> th ) $=
      ( wo w3o df-3or sylbir olcs ) ABFZCDKCFABCGDABCHEIJ $.
  $}

  ${
    adantl3r.1 $e |- ( ( ( ( ph /\ rh ) /\ mu ) /\ la ) -> ka ) $.
    $( Deduction adding 1 conjunct to antecedent.  (Contributed by Thierry
       Arnoux, 11-Feb-2018.) $)
    adantl3r $p |- ( ( ( ( ( ph /\ si ) /\ rh ) /\ mu ) /\ la ) -> ka ) $=
      ( wa wi ex adantllr imp ) ABHCHDHEFACDEFIBACHDHEFGJKL $.
  $}

  ${
    adantl4r.1 $e |- ( ( ( ( ( ph /\ si ) /\ rh ) /\ mu ) /\ la ) -> ka ) $.
    $( Deduction adding 1 conjunct to antecedent.  (Contributed by Thierry
       Arnoux, 11-Feb-2018.) $)
    adantl4r $p |- ( ( ( ( ( ( ph /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la )
      -> ka ) $=
      ( wa wi ex adantl3r imp ) ABICIDIEIFGABCDEFGJACIDIEIFGHKLM $.
  $}

  ${
    adantl5r.1 $e |- ( ( ( ( ( ( ph /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la )
      -> ka ) $.
    $( Deduction adding 1 conjunct to antecedent.  (Contributed by Thierry
       Arnoux, 11-Feb-2018.) $)
    adantl5r $p |- ( ( ( ( ( ( ( ph /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu )
      /\ la ) -> ka ) $=
      ( wa wi ex adantl4r imp ) ABJCJDJEJFJGHABCDEFGHKACJDJEJFJGHILMN $.
  $}

  ${
    adantl6r.1 $e |- ( ( ( ( ( ( ( ph /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu )
      /\ la ) -> ka ) $.
    $( Deduction adding 1 conjunct to antecedent.  (Contributed by Thierry
       Arnoux, 11-Feb-2018.) $)
    adantl6r $p |- ( ( ( ( ( ( ( ( ph /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh )
      /\ mu ) /\ la ) -> ka ) $=
      ( wa wi ex adantl5r imp ) ABKCKDKEKFKGKHIABCDEFGHILACKDKEKFKGKHIJMNO $.
  $}

  ${
    mpjao3dan.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    mpjao3dan.2 $e |- ( ( ph /\ th ) -> ch ) $.
    mpjao3dan.3 $e |- ( ( ph /\ ta ) -> ch ) $.
    mpjao3dan.4 $e |- ( ph -> ( ps \/ th \/ ta ) ) $.
    $( Eliminate a 3-way disjunction in a deduction.  (Contributed by Thierry
       Arnoux, 13-Apr-2018.) $)
    mpjao3dan $p |- ( ph -> ch ) $=
      ( wo jaodan w3o df-3or sylib mpjaodan ) ABDJZCEABCDFGKHABDELPEJIBDEMNO $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Predicate Calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
      Predicate Calculus - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y $.  $d y A $.  $d y ph $.
    abeq2f.0 $e |- F/_ x A $.
    $( Equality of a class variable and a class abstraction.  In this version,
       the fact that ` x ` is a non-free variable in ` A ` is explicitely
       stated as a hypothesis.  (Contributed by Thierry Arnoux,
       11-May-2017.) $)
    abeq2f $p |- ( A = { x | ph } <-> A. x ( x e. A <-> ph ) ) $=
      ( vy cab wceq cv wcel wb wal nfcrii hbab1 cleqh abid bibi2i albii bitri )
      CABFZGBHZCIZTSIZJZBKUAAJZBKBECSBECDLABEMNUCUDBUBAUAABOPQR $.
  $}

  ${
    $d x y z A $.  $d x y z B $.
    $( A variable introduction law for class equality, deduction version.
       (Contributed by Thierry Arnoux, 2-Mar-2017.) $)
    eqvincg $p |- ( A e. V -> ( A = B <-> E. x ( x = A /\ x = B ) ) ) $=
      ( wcel wceq cv wa wex wi elisset ax-1 eqtr ex jca eximi pm3.43 3syl sylib
      19.37v eqtr2 exlimiv impbid1 ) BDEZBCFZAGZBFZUFCFZHZAIZUDUEUIJZAIZUEUJJUD
      UGAIUEUGJZUEUHJZHZAIULABDKUGUOAUGUMUNUGUELUGUEUHUFBCMNOPUOUKAUEUGUHQPRUEU
      IATSUIUEAUFBCUAUBUC $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
      Restricted quantification - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x ph $.
    reximddva.1 $e |- ( ( ph /\ ( x e. A /\ ps ) ) -> ch ) $.
    reximddva.2 $e |- ( ph -> E. x e. A ps ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by
       Thierry Arnoux, 7-Dec-2016.) $)
    reximddv $p |- ( ph -> E. x e. A ch ) $=
      ( wrex cv wcel expr reximdva mpd ) ABDEHCDEHGABCDEADIEJBCFKLM $.
  $}

  ${
    $d x y $.
    ralcom4f.1 $e |- F/_ y A $.
    $( Commutation of restricted and unrestricted universal quantifiers.
       (Contributed by NM, 26-Mar-2004.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.)  (Revised by Thierry Arnoux, 8-Mar-2017.) $)
    ralcom4f $p |- ( A. x e. A A. y ph <-> A. y A. x e. A ph ) $=
      ( cvv wral wal nfcv ralcomf ralv ralbii 3bitr3i ) ACFGZBDGABDGZCFGACHZBDG
      OCHABCDFEBFIJNPBDACKLOCKM $.

    $( Commutation of restricted and unrestricted existential quantifiers.
       (Contributed by NM, 12-Apr-2004.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.)  (Revised by Thierry Arnoux, 8-Mar-2017.) $)
    rexcom4f $p |- ( E. x e. A E. y ph <-> E. y E. x e. A ph ) $=
      ( cvv wrex wex nfcv rexcomf rexv rexbii 3bitr3i ) ACFGZBDGABDGZCFGACHZBDG
      OCHABCDFEBFIJNPBDACKLOCKM $.
  $}

  ${
    $d x y $.  $d y A $.  $d y ph $.
    rabid2f.1 $e |- F/_ x A $.
    $( An "identity" law for restricted class abstraction.  (Contributed by NM,
       9-Oct-2003.)  (Proof shortened by Andrew Salmon, 30-May-2011.)  (Revised
       by Thierry Arnoux, 13-Mar-2017.) $)
    rabid2f $p |- ( A = { x e. A | ph } <-> A. x e. A ph ) $=
      ( cv wcel wa cab wceq wi wal crab wral abeq2f pm4.71 bitr4i df-rab eqeq2i
      wb albii df-ral 3bitr4i ) CBECFZAGZBHZIZUCAJZBKZCABCLZIABCMUFUCUDSZBKUHUD
      BCDNUGUJBUCAOTPUIUECABCQRABCUAUB $.
  $}


  ${
    19.9d2rf.0 $e |- F/ y ph $.
    19.9d2rf.1 $e |- ( ph -> F/ x ps ) $.
    19.9d2rf.2 $e |- ( ph -> F/ y ps ) $.
    19.9d2rf.3 $e |- ( ph -> E. x e. A E. y e. B ps ) $.
    $( A deduction version of one direction of ~ 19.9 with two variables
       (Contributed by Thierry Arnoux, 20-Mar-2017.) $)
    19.9d2rf $p |- ( ph -> ps ) $=
      ( wex wrex rexex eximi 3syl nfexd 19.9d mpd ) ABDKZBASCKZSABDFLZCELUACKTJ
      UACEMUASCBDFMNOSACABCDGHPQRBADIQR $.
  $}

  ${
    $d y ph $.
    19.9d2r.1 $e |- ( ph -> F/ x ps ) $.
    19.9d2r.2 $e |- ( ph -> F/ y ps ) $.
    19.9d2r.3 $e |- ( ph -> E. x e. A E. y e. B ps ) $.
    $( A deduction version of one direction of ~ 19.9 with two variables
       (Contributed by Thierry Arnoux, 30-Jan-2017.) $)
    19.9d2r $p |- ( ph -> ps ) $=
      ( nfv 19.9d2rf ) ABCDEFADJGHIK $.
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Restricted quantifier version of Theorem 19.41 of [Margaris] p. 90.
       Version with two quantifiers (Contributed by Thierry Arnoux,
       25-Jan-2017.) $)
    r19.41vv $p |- ( E. x e. A E. y e. B ( ph /\ ps )
                                      <-> ( E. x e. A E. y e. B ph /\ ps ) ) $=
      ( wa wrex r19.41v rexbii bitri ) ABGDFHZCEHADFHZBGZCEHMCEHBGLNCEABDFIJMBC
      EIK $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
      Substitution (without distinct variables) - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d w y $.  $d w A $.  $d w x $.
    clelsb3f.1 $e |- F/_ y A $.
    $( Substitution applied to an atomic wff (class version of ~ elsb3 ).
       (Contributed by Rodolfo Medina, 28-Apr-2010.)  (Proof shortened by
       Andrew Salmon, 14-Jun-2011.)  (Revised by Thierry Arnoux,
       13-Mar-2017.) $)
    clelsb3f $p |- ( [ x / y ] y e. A <-> x e. A ) $=
      ( vw cv wcel wsb nfcri sbco2 nfv eleq1 sbie sbbii 3bitr3i ) EFZCGZEBHZBAH
      QEAHBFZCGZBAHAFZCGZQEABBECDIJRTBAQTEBTEKPSCLMNQUBEAUBEKPUACLMO $.
  $}

  ${
    $d x ph  $.
    sbceqbid.1 $e |- ( ph -> A = B ) $.
    sbceqbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equality theorem for class substitution.  (Contributed by Thierry
       Arnoux, 4-Sep-2018.) $)
    sbceqbid $p |- ( ph -> ( [. A / x ]. ps <-> [. B / x ]. ch ) ) $=
      ( cab wcel wsbc abbidv eleq12d df-sbc 3bitr4g ) AEBDIZJFCDIZJBDEKCDFKAEFP
      QGABCDHLMBDENCDFNO $.
  $}

  ${
    sbceqbidf.1 $e |- F/ x ph $.
    sbceqbidf.2 $e |- ( ph -> A = B ) $.
    sbceqbidf.3 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equality theorem for class substitution.  (Contributed by Thierry
       Arnoux, 4-Sep-2018.) $)
    sbceqbidf $p |- ( ph -> ( [. A / x ]. ps <-> [. B / x ]. ch ) ) $=
      ( cab wcel wsbc abbid eleq12d df-sbc 3bitr4g ) AEBDJZKFCDJZKBDELCDFLAEFQR
      HABCDGIMNBDEOCDFOP $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
      Existential "at most one" - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y A $.
    $( "At most one" element in a set.  (Contributed by Thierry Arnoux,
       26-Jul-2018.) $)
    moel $p |- ( E* x x e. A <-> A. x e. A A. y e. A x = y ) $=
    ( cv wcel wceq wi wal wral wmo ralcom4 df-ral ralbii alcom eleq1 mo4 impexp
    wa albii bitr4i 3bitr4i 3bitr4ri ) BDZCEZADZUCFZGZBHZACIUGACIZBHZUFBCIZACIU
    ECEZAJZUGABCKUKUHACUFBCLMULUDRUFGZBHAHUNAHZBHUMUJUNABNULUDABUEUCCOPUIUOBUIU
    LUGGZAHUOUGACLUNUPAULUDUFQSTSUAUB $.
  $}

  ${
    $d i j x $.
    mo5f.1 $e |- F/ i ph $.
    mo5f.2 $e |- F/ j ph $.
    $( Alternate definition of "at most one."  (Contributed by Thierry Arnoux,
       1-Mar-2017.) $)
    mo5f $p |- ( E* x ph <->
                   A. i A. j ( ( [ i / x ] ph /\ [ j / x ] ph ) -> i = j ) ) $=
      ( wmo wsb wa weq wi wal mo3 nfsb nfan nfv nfim nfal sb8 sbim nfs1v bicomi
      sban sbf anbi2i bitr4i equsb3 imbi12i bitri sbalv albii 3bitri ) ABGAABDH
      ZIZBDJZKZDLZBLUQBCHZCLABCHZUMIZCDJZKZDLZCLABDFMUQBCUPCDUNUOCAUMCEABDCENOU
      OCPQRSURVCCUPVBBCDUPBCHUNBCHZUOBCHZKVBUNUOBCTVDUTVEVAVDUSUMBCHZIUTAUMBCUC
      UMVFUSVFUMUMBCABDUAUDUBUEUFCBDUGUHUIUJUKUL $.
  $}

  ${
    $d x y $.
    nmo.1 $e |- F/ y ph $.
    $( Negation of "at most one".  (Contributed by Thierry Arnoux,
       26-Feb-2017.) $)
    nmo $p |- ( -. E* x ph <-> A. y E. x ( ph /\ x =/= y ) ) $=
      ( wmo wn weq wi wal wex cv wne wa mo2 notbii alnex pm4.61 biid necon3bbii
      exnal anbi2i bitri exbii bitr3i albii 3bitr2i ) ABEZFABCGZHZBIZCJZFUJFZCI
      ABKZCKZLZMZBJZCIUGUKABCDNOUJCPULUQCULUIFZBJUQUIBTURUPBURAUHFZMUPAUHQUSUOA
      UHUMUNUHRSUAUBUCUDUEUF $.
  $}

  ${
    $d x ph $.
    moimd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( "At most one" is preserved through implication (notice wff reversal).
       (Contributed by Thierry Arnoux, 25-Feb-2017.) $)
    moimd $p |- ( ph -> ( E* x ch -> E* x ps ) ) $=
      ( wi wal wmo alrimiv moim syl ) ABCFZDGCDHBDHFALDEIBCDJK $.
  $}

  ${
    $d x y A $.  $d x y B $. 
    $( Equality's restricted existential "at most one" property.  (Contributed
       by Thierry Arnoux, 30-Mar-2018.) $)
    rmoeq $p |- ( A e. V -> E* x e. B x = A ) $=
      ( vy wcel cv wceq wi wral wex wrmo id rgenw imbi2d ralbidv spcegv mpi nfv
      eqeq2 rmo2 sylibr ) BDFZAGZBHZUDEGZHZIZACJZEKZUEACLUCUEUEIZACJZUJUKACUEMN
      UIULEBDUFBHZUHUKACUMUGUEUEUFBUDTOPQRUEAECUEESUAUB $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
      Existential uniqueness - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y A $.  $d x B $.
    $( A condition allowing swap of uniqueness and existential quantifiers.
       (Contributed by Thierry Arnoux, 7-Apr-2017.) $)
    2reuswap2 $p |- ( A. x e. A E* y ( y e. B /\ ph ) ->
                   ( E! x e. A E. y e. B ph -> E! y e. B E. x e. A ph ) ) $=
      ( cv wcel wa wmo wal wrex wreu wex weu df-reu r19.42v df-rex bitr3i bitri
      wi wral df-ral moanimv albii bitr4i 2euswap exbii eubii 3imtr4g sylbi
      an12 ) CFEGZAHZCIZBDUAZBFDGZUMHZCIZBJZACEKZBDLZABDKZCELZTUOUPUNTZBJUSUNBD
      UBURVDBUPUMCUCUDUEUSUQCMZBNZUQBMZCNZVAVCUQBCUFVAUPUTHZBNVFUTBDOVIVEBVIULU
      PAHZHZCMZVEVIVJCEKVLUPACEPVJCEQRVKUQCULUPAUKUGSUHSVCULVBHZCNVHVBCEOVMVGCV
      MUMBDKVGULABDPUMBDQRUHSUIUJ $.
  $}

  ${
    $d x y ph $.  $d x ps $.  $d x A $.  $d x y B $.  $d x y C $.
    reuxfr3d.1 $e |- ( ( ph /\ y e. C ) -> A e. B ) $.
    reuxfr3d.2 $e |- ( ( ph /\ x e. B ) -> E* y e. C x = A ) $.
    $( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  Cf. ~ reuxfr2d
       (Contributed by Thierry Arnoux, 7-Apr-2017.)  (Revised by Thierry
       Arnoux, 8-Oct-2017.) $)
    reuxfr3d $p |- ( ph
        -> ( E! x e. B E. y e. C ( x = A /\ ps ) <-> E! y e. C ps ) ) $=
      ( cv wceq wa wrex wreu wrmo wi wcel syl ancom wmo wral rmoan rmobii sylib
      ralrimiva 2reuswap 2reuswap2 moeq moani an12 bitri mobii mpbi a1i impbid1
      mprg wb biidd ceqsrexv reubidva bitrd ) ACJZEKZBLZDGMCFNZVDCFMZDGNZBDGNAV
      EVGAVDDGOZCFUAVEVGPAVHCFAVBFQZLZBVCLZDGOZVHVJVCDGOVLIVCBDGUBRVKVDDGBVCSUC
      UDUEVDCDFGUFRVIVDLZCTZVGVEPDGVDDCGFUGVNDJGQZVIBLZVCLZCTVNVCVPCCEUHUIVQVMC
      VQVCVPLVMVPVCSVCVIBUJUKULUMUNUPUOAVFBDGAVOLEFQVFBUQHBBCEFVCBURUSRUTVA $.
  $}

  ${
    $d x y ph $.  $d y ps $.  $d x ch $.  $d x A $.  $d x y B $.  $d x y C $.
    reuxfr4d.1 $e |- ( ( ph /\ y e. C ) -> A e. B ) $.
    reuxfr4d.2 $e |- ( ( ph /\ x e. B ) -> E! y e. C x = A ) $.
    reuxfr4d.3 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
    $( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  Cf. ~ reuxfrd
       (Contributed by Thierry Arnoux, 7-Apr-2017.) $)
    reuxfr4d $p |- ( ph -> ( E! x e. B ps <-> E! y e. C ch ) ) $=
      ( wreu cv wceq wa wrex wcel reurex syl bitrd biantrurd wb r19.41v rexbidv
      pm5.32da syl5bbr adantr reubidva wrmo reurmo reuxfr3d ) ABDGLDMZFNZCOZEHP
      ZDGLCEHLABUODGAULGQZOZBUMEHPZBOZUOUQURBUQUMEHLZURJUMEHRSUAAUSUOUBUPUSUMBO
      ZEHPAUOUMBEHUCAVAUNEHAUMBCKUEUDUFUGTUHACDEFGHIUQUTUMEHUIJUMEHUJSUKT $.
  $}

$(
  @{
    @d x y ph @.  @d x ps @.  @d x A @.  @d x B @.  @d x y C @.
    reuxfr3df.0 @e |- F/_ y B @.
    reuxfr3df.1 @e |- ( ( ph /\ y e. C ) -> A e. B ) @.
    reuxfr3df.2 @e |- ( ( ph /\ x e. B ) -> E* y e. C x = A ) @.
    @( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  Cf. ~ reuxfr2d
       (Contributed by Thierry Arnoux, 7-Apr-2017.)  (Revised by Thierry
       Arnoux, 8-Oct-2017.)  (Revised by Thierry Arnoux, 30-Mar-2018.) @)
    reuxfr3df @p |- ( ph
        -> ( E! x e. B E. y e. C ( x = A /\ ps ) <-> E! y e. C ps ) ) @=
      ? @.
  @}
$)
  ${
    $d b x y $.  $d y A $.  $d b B $.  $d x b F $.  $d x b ph $.
    rexunirn.1 $e |- F = ( x e. A |-> B ) $.
    rexunirn.2 $e |- ( x e. A -> B e. V ) $.
    $( Restricted existential quantification over the union of the range of a
       function.  Cf. ~ rexrn and ~ eluni2 .  (Contributed by Thierry Arnoux,
       19-Sep-2017.) $)
    rexunirn $p |- ( E. x e. A E. y e. B ph -> E. y e. U. ran F ph ) $=
      ( vb wrex cv wcel wa wex crn cuni df-rex bitr4i exbii 19.42v anbi2i mpdan
      elrnmpt1 wceq eleq2 anbi1d rspcev sylan r19.41v sylib eximi eluni2 anbi1i
      bitri sylibr exlimiv sylbi ) ACEKZBDKZBLDMZCLZEMZANZNZCOZBOZACFPZQZKZUTVA
      USNZBOVGUSBDRVFVKBVFVAVDCOZNVKVAVDCUAUSVLVAACERUBSTSVFVJBVFVBJLZMZJVHKZAN
      ZCOZVJVEVPCVEVNANZJVHKZVPVAEVHMZVDVSVAEGMVTIBDEFGHUDUCVRVDJEVHVMEUEVNVCAV
      MEVBUFUGUHUIVNAJVHUJUKULVJVBVIMZANZCOVQACVIRWBVPCWAVOAJVBVHUMUNTUOUPUQUR
      $.
  $}

$(
  @{
    @( Restricted existential quantification for ordered pair abstract builders
       moving one condition outside of the abstract builder. @)
    reuopan @p |- ( E! p e. { <. x , y >. | ( ( x e. A /\ y e. B ) /\ ph ) } ps
      <-> E! p e. { <. x , y >. | ( x e. A /\ y e. B ) } ( ph /\ ps ) ) @=
      ? @.

    @( Restricted existential quantification for ordered pair abstract builders
       @)
    reuopab @p |- ( E! p e. { <. x , y >. | ( x e. A /\ y e. B ) } ph
      <-> ( E! x e. A E! y e. B ( p = <. x , y >. /\ ph ) 
         /\ A. x e. A E* y e. B ( p = <. x , y >. /\ ph ) ) ) @=
      ? @.
  @}
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
      Restricted "at most one" - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x A $.  $d x y B $.  $d x y C $.  $d x y ph $.  $d y ps $.  $d x ch $.
    rmoxfrd.1 $e |- ( ( ph /\ y e. C ) -> A e. B ) $.
    rmoxfrd.2 $e |- ( ( ph /\ x e. B ) -> E! y e. C x = A ) $.
    rmoxfrd.3 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
    $( Transfer "at most one" restricted quantification from a variable ` x `
       to another variable ` y ` contained in expression ` A ` .  (Contributed
       by Thierry Arnoux, 7-Apr-2017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rmoxfrdOLD $p |- ( ph ->
                       ( E* x ( x e. B /\ ps ) <-> E* y ( y e. C /\ ch ) ) ) $=
      ( cv wcel wa wex weu wi wmo wrex wreu wceq reurex rexxfrd df-rex reuxfr4d
      syl 3bitr3g df-reu imbi12d df-mo 3bitr4g ) ADLZGMZBNZDOZUNDPZQELHMCNZEOZU
      QEPZQUNDRUQERAUOURUPUSABDGSCEHSUOURABCDEFGHIAUMNULFUAZEHTUTEHSJUTEHUBUFKU
      CBDGUDCEHUDUGABDGTCEHTUPUSABCDEFGHIJKUEBDGUHCEHUHUGUIUNDUJUQEUJUK $.

    $( Transfer "at most one" restricted quantification from a variable ` x `
       to another variable ` y ` contained in expression ` A ` .  (Contributed
       by Thierry Arnoux, 7-Apr-2017.)  (Revised by Thierry Arnoux,
       8-Oct-2017.) $)
    rmoxfrd $p |- ( ph -> ( E* x e. B ps <-> E* y e. C ch ) ) $=
      ( cv wcel wa wmo wrmo wex weu wrex wreu wi wceq reurex syl rexxfrd df-rex
      3bitr3g reuxfr4d df-reu imbi12d df-mo 3bitr4g df-rmo ) ADLZGMZBNZDOZELHMC
      NZEOZBDGPCEHPAUPDQZUPDRZUAUREQZURERZUAUQUSAUTVBVAVCABDGSCEHSUTVBABCDEFGHI
      AUONUNFUBZEHTVDEHSJVDEHUCUDKUEBDGUFCEHUFUGABDGTCEHTVAVCABCDEFGHIJKUHBDGUI
      CEHUIUGUJUPDUKUREUKULBDGUMCEHUMUL $.
  $}

  ${
    ssrmo.1 $e |- F/_ x A $.
    ssrmo.2 $e |- F/_ x B $.
    $( "At most one" existential quantification restricted to a subclass.
       (Contributed by Thierry Arnoux, 8-Oct-2017.) $)
    ssrmo $p |- ( A C_ B -> ( E* x e. B ph -> E* x e. A ph ) ) $=
      ( wss cv wcel wa wmo wrmo wi wal dfss2f biimpi pm3.45 alimi moim df-rmo
      3syl 3imtr4g ) CDGZBHZDIZAJZBKZUDCIZAJZBKZABDLABCLUCUHUEMZBNZUIUFMZBNUGUJ
      MUCULBCDEFOPUKUMBUHUEAQRUIUFBSUAABDTABCTUB $.
  $}

  ${
    $d x y $.
    rmo3f.1 $e |- F/_ x A $.
    rmo3f.2 $e |- F/_ y A $.
    rmo3f.3 $e |- F/ y ph $.
    $( Restricted "at most one" using explicit substitution.  (Contributed by
       NM, 4-Nov-2012.)  (Revised by NM, 16-Jun-2017.)  (Revised by Thierry
       Arnoux, 8-Oct-2017.) $)
    rmo3f $p |- ( E* x e. A ph <->
               A. x e. A A. y e. A ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      ( cv wcel wa wsb wi wral wal anbi1i bitri 3bitri impexp albii df-ral wrmo
      wmo weq df-rmo sban clelsb3f anbi2i an4 ancom imbi1i nfcri r19.21 3bitr2i
      nfan mo3 3bitr4i ) ABDUABHDIZAJZBUBZAABCKZJZBCUCZLZCDMZBDMZABDUDURURBCKZJ
      ZVBLZCNZBNUQVDLZBNUSVEVIVJBVICHDIZUQVCLZLZCNVLCDMVJVHVMCVHVKUQJZVAJZVBLVN
      VCLVMVGVOVBVGURVKUTJZJUQVKJZVAJVOVFVPURVFUQBCKZUTJVPUQABCUEVRVKUTCBDEUFOP
      UGUQAVKUTUHVQVNVAUQVKUIOQUJVNVAVBRVKUQVCRQSVLCDTUQVCCDCBDFUKZULUMSURBCUQA
      CVSGUNUOVDBDTUPP $.
  $}

  ${
    $d x y $.  $d z A $.  $d y z ph $.  $d z ps $.
    rmo4f.1 $e |- F/_ x A $.
    rmo4f.2 $e |- F/_ y A $.
    rmo4f.3 $e |- F/ x ps $.
    rmo4f.4 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Restricted "at most one" using implicit substitution.  (Contributed by
       NM, 24-Oct-2006.)  (Revised by Thierry Arnoux, 11-Oct-2016.)  (Revised
       by Thierry Arnoux, 8-Mar-2017.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    rmo4fOLD $p |- ( E* x ( x e. A /\ ph ) <->
               A. x e. A A. y e. A ( ( ph /\ ps ) -> x = y ) ) $=
      ( cv wcel wa wi wal wral bitri imbi1i impexp albii df-ral wceq wmo anbi1i
      an4 ancom 3bitri nfcv nfel r19.21 3bitr2i wsb nfv nfan eleq1 anbi12d sbie
      mo3 anbi2i 2albii 3bitr4i ) CJZEKZALZDJZEKZBLZLZVAVDUAZMZDNZCNZVBABLZVHMZ
      DEOZMZCNVCCUBZVNCEOVJVOCVJVEVBVMMZMZDNVQDEOVOVIVRDVIVEVBLZVLLZVHMVSVMMVRV
      GVTVHVGVBVELZVLLVTVBAVEBUDWAVSVLVBVEUEUCPQVSVLVHRVEVBVMRUFSVQDETVBVMDEDVA
      EDVAUGGUHZUIUJSVPVCVCCDUKZLZVHMZDNCNVKVCCDVBADWBADULUMUQWEVICDWDVGVHWCVFV
      CVCVFCDVEBCCVDECVDUGFUHHUMVHVBVEABVAVDEUNIUOUPURQUSPVNCETUT $.

    $( Restricted "at most one" using implicit substitution.  (Contributed by
       NM, 24-Oct-2006.)  (Revised by Thierry Arnoux, 11-Oct-2016.)  (Revised
       by Thierry Arnoux, 8-Mar-2017.)  (Revised by Thierry Arnoux,
       8-Oct-2017.) $)
    rmo4f $p |- ( E* x e. A ph <->
               A. x e. A A. y e. A ( ( ph /\ ps ) -> x = y ) ) $=
      ( wrmo wsb wa weq wi wral nfv rmo3f sbie anbi2i imbi1i 2ralbii bitri ) AC
      EJAACDKZLZCDMZNZDEOCEOABLZUENZDEOCEOACDEFGADPQUFUHCDEEUDUGUEUCBAABCDHIRST
      UAUB $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        General Set Theory
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
           Class abstractions (a.k.a. class builders)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x A $.  $d x ps $.
    ceqsexv2d.1 $e |- A e. _V $.
    ceqsexv2d.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    ceqsexv2d.3 $e |- ps $.
    $( Elimination of an existential quantifier, using implicit substitution.
       (Contributed by Thierry Arnoux, 10-Sep-2016.) $)
    ceqsexv2d $p |- E. x ph $=
      ( cv wceq wa wex ceqsexv biimpri simpr eximi mp2b ) BCHDIZAJZCKZACKGSBABC
      DEFLMRACQANOP $.
  $}

  ${
    $d x ph $.
    rabbidva2.1 $e |- ( ph -> ( ( x e. A /\ ps ) <-> ( x e. B /\ ch ) ) ) $.
    $( Equivalent wff's yield equal restricted class abstractions.
       (Contributed by Thierry Arnoux, 4-Feb-2017.) $)
    rabbidva2 $p |- ( ph -> { x e. A | ps } = { x e. B | ch } ) $=
      ( cv wcel wa cab crab abbidv df-rab 3eqtr4g ) ADHZEIBJZDKPFICJZDKBDELCDFL
      AQRDGMBDENCDFNO $.
  $}

  ${
    rabexgfGS.1 $e |- F/_ x A $.
    $( Separation Scheme in terms of a restricted class abstraction.  To be
       removed in profit of Glauco's equivalent version.  (Contributed by
       Thierry Arnoux, 11-May-2017.) $)
    rabexgfGS $p |- ( A e. V -> { x e. A | ph } e. _V ) $=
      ( wcel crab wss cvv cv wi nfrab1 dfss2f rabid simplbi mpgbir elex sylancr
      ssexg ) CDFABCGZCHZCIFTIFUABJZTFZUBCFZKBBTCABCLEMUCUDAABCNOPCDQTCISR $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
           Image Sets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x y $.
    abrexdomjm.1 $e |- ( y e. A -> E* x ph ) $.
    $( An indexed set is dominated by the indexing set.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    abrexdomjm $p |- ( A e. V -> { x | E. y e. A ph } ~<_ A ) $=
      ( wcel wrex cab cv wa copab crn cdom wex df-rex abbii wbr cvv wmo cdm wfn
      rnopab eqtr4i wss dmopabss ssexg mpan funopab wi moanimv mpbir mpgbir a1i
      wfun funfn sylib fnrndomg sylc ssdomg mpi domtr syl2anc syl5eqbr ) DEGZAC
      DHZBIZCJDGZAKZCBLZMZDNVGVICOZBIVKVFVLBACDPQVICBUCUDVEVKVJUAZNRZVMDNRZVKDN
      RVEVMSGZVJVMUBZVNVMDUEZVEVPACBDUFZVMDEUGUHVEVJUOZVQVTVEVTVIBTZCVICBUIWAVH
      ABTUJFVHABUKULUMUNVJUPUQVMSVJURUSVEVRVOVSVMDEUTVAVKVMDVBVCVD $.
  $}

  ${
    $d A x y $.  $d B x $.
    $( An indexed set is dominated by the indexing set.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    abrexdom2jm $p |- ( A e. V -> { x | E. y e. A x = B } ~<_ A ) $=
      ( cv wceq wmo wcel moeq a1i abrexdomjm ) AFDGZABCEMAHBFCIADJKL $.
  $}

  ${
    $d x y z w $.  $d y z w A $.  $d y z w B $.
    abrexexd.0 $e |- F/_ x A $.
    abrexexd.1 $e |- ( ph -> A e. _V ) $.
    $( Existence of a class abstraction of existentially restricted sets.
       (Contributed by Thierry Arnoux, 10-May-2017.) $)
    abrexexd $p |- ( ph -> { y | E. x e. A y = B } e. _V ) $=
      ( cv wceq wrex cab cmpt crn cvv wcel wa copab wex rnopab df-mpt rneqi cdm
      df-rex abbii 3eqtr4i wfun funmpt crab eqid dmmpt rabexgfGS syl5eqel funex
      sylancr rnexg 3syl syl5eqelr ) ACHEIZBDJZCKZBDELZMZNBHDOURPZBCQZMVCBRZCKV
      BUTVCBCSVAVDBCDETUAUSVECURBDUCUDUEADNOZVANOZVBNOGVFVAUFVAUBZNOVGBDEUGVFVH
      ENOZBDUHNBDEVAVAUIUJVIBDNFUKULNVAUMUNVANUOUPUQ $.
  $}

  ${
    $d x y A $.  $d y B $.  $d y C $.
    elabreximd.1 $e |- F/ x ph $.
    elabreximd.2 $e |- F/ x ch $.
    elabreximd.3 $e |- ( A = B -> ( ch <-> ps ) ) $.
    elabreximd.4 $e |- ( ph -> A e. V ) $.
    elabreximd.5 $e |- ( ( ph /\ x e. C ) -> ps ) $.
    $( Class substitution in an image set.  (Contributed by Thierry Arnoux,
       30-Dec-2016.) $)
    elabreximd $p |- ( ( ph /\ A e. { y | E. x e. C y = B } ) -> ch ) $=
      ( cv wceq wrex cab wcel wa wb eqeq1 rexbidv elabg syl biimpa simpr adantr
      biimpar syl2anc exp31 rexlimd imp syldan ) AFEOZGPZDHQZERSZFGPZDHQZCAURUT
      AFISURUTUAMUQUTEFIUOFPUPUSDHUOFGUBUCUDUEUFAUTCAUSCDHJKADOHSZUSCAVATZUSTUS
      BCVBUSUGVBBUSNUHUSCBLUIUJUKULUMUN $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.  $d x ch $.  $d x ph $.
    elabreximdv.1 $e |- ( A = B -> ( ch <-> ps ) ) $.
    elabreximdv.2 $e |- ( ph -> A e. V ) $.
    elabreximdv.3 $e |- ( ( ph /\ x e. C ) -> ps ) $.
    $( Class substitution in an image set.  (Contributed by Thierry Arnoux,
       30-Dec-2016.) $)
    elabreximdv $p |- ( ( ph /\ A e. { y | E. x e. C y = B } ) -> ch ) $=
      ( nfv elabreximd ) ABCDEFGHIADMCDMJKLN $.
  $}

  ${
    abrexss.1 $e |- F/_ x C $.
    $d x y z $.  $d y z A $.  $d z C $.  $d y z B $.
    $( A necessary condition for an image set to be a subset.  (Contributed by
       Thierry Arnoux, 6-Feb-2017.) $)
    abrexss $p |- ( A. x e. A B e. C -> { y | E. x e. A y = B } C_ C ) $=
      ( vz wcel wral cv wceq wrex cab cvv nfra1 nfcri eleq1 vex a1i id r19.21bi
      elabreximd ex ssrdv ) DEHZACIZGBJDKACLBMZEUFGJZUGHUHEHZUFUEUIABUHDCNUEACO
      AGEFPUHDEQUHNHUFGRSUFUEACUFTUAUBUCUD $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
           Set relations and operations - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    eqri.1 $e |- F/_ x A $.
    eqri.2 $e |- F/_ x B $.
    eqri.3 $e |- ( x e. A <-> x e. B ) $.
    $( Infer equality of classes from equivalence of membership.  (Contributed
       by Thierry Arnoux, 7-Oct-2017.) $)
    eqri $p |- A = B $=
      ( wceq wtru nftru cv wcel wb a1i eqrd trud ) BCGHABCAIDEAJZBKPCKLHFMNO $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ph $.
    rabss3d.1 $e |- ( ( ph /\ ( x e. A /\ ps ) ) -> x e. B ) $.
    $( Subclass law for restricted abstraction.  (Contributed by Thierry
       Arnoux, 25-Sep-2017.) $)
    rabss3d $p |- ( ph -> { x e. A | ps } C_ { x e. B | ps } ) $=
      ( crab nfv nfrab1 cv wcel wa simprr jca ex rabid 3imtr4g ssrd ) ACBCDGZBC
      EGZACHBCDIBCEIACJZDKZBLZUAEKZBLZUASKUATKAUCUEAUCLUDBFAUBBMNOBCDPBCEPQR $.
  $}

  $( Intersection with an intersection (Contributed by Thierry Arnoux,
     27-Dec-2016.) $)
  inin $p |- ( A i^i ( A i^i B ) ) = ( A i^i B ) $=
    ( cin in13 inidm ineq2i incom 3eqtri ) AABCZCBAACZCBACIAABDJABAEFBAGH $.

  $( See ~ inundif (Contributed by Thierry Arnoux, 13-Sep-2017.) $)
  inindif $p |- ( ( A i^i C ) i^i ( A \ C ) ) = (/) $=
    ( cin wss cdif c0 wceq wo inss2 orci inss ax-mp inssdif0 mpbi ) ABCZACBDZOA
    BECFGOBDZABDZHPQRABIJOABKLOABMN $.

  $( If the difference of two sets is not empty, then the sets are not equal.
     (Contributed by Thierry Arnoux, 28-Feb-2017.) $)
  difneqnul $p |- ( ( A \ B ) =/= (/) -> A =/= B ) $=
    ( cdif c0 wceq wss eqimss ssdif0 sylib necon3i ) ABABCZDABEABFKDEABGABHIJ
    $.

  $( Rewriting an equation with set difference, without using quantifiers.
     (Contributed by Thierry Arnoux, 24-Sep-2017.) $)
  difeq $p |- ( ( A \ B ) = C <->
                         ( ( C i^i B ) = (/) /\ ( C u. B ) = ( A u. B ) ) ) $=
    ( cdif wceq cin c0 cun incom disjdif eqtr3i ineq1 syl5reqr undif1 uneq1 jca
    wa simpl disj3 difun2 eqcom bitri sylib difeq1 3eqtr3g eqeq1d adantl impbii
    wb mpbid ) ABDZCEZCBFZGEZCBHZABHZEZQZULUNUQULGUKBFZUMBUKFUSGBUKIBAJKUKCBLMU
    LUPUKBHUOABNUKCBOMPURCBDZCEZULURUNVAUNUQRUNCUTEVACBSCUTUAUBUCUQVAULUIUNUQUT
    UKCUQUOBDUPBDUTUKUOUPBUDCBTABTUEUFUGUJUH $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Unordered pairs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    elpreq.1 $e |- ( ph -> X e. { A , B } ) $.
    elpreq.2 $e |- ( ph -> Y e. { A , B } ) $.
    elpreq.3 $e |- ( ph -> ( X = A <-> Y = A ) ) $.
    $( Equality wihin a pair (Contributed by Thierry Arnoux, 23-Aug-2017.) $)
    elpreq $p |- ( ph -> X = Y ) $=
      ( wceq wa simpr biimpa eqtr4d wn cpr wcel wo elpri syl orcanai simpl 3syl
      notbid wi pm2.53 sylc pm2.61dan ) ADBIZDEIAUHJDBEAUHKAUHEBIZHLMAUHNZJZDCE
      AUHDCIZADBCOZPUHULQFDBCRSTUKAUINZECIZAUJUAAUJUNAUHUIHUCLAEUMPUIUOQUNUOUDG
      EBCRUIUOUEUBUFMUG $.
  $}

  ${
    preqsnd.1 $e |- ( ph -> A e. _V ) $.
    preqsnd.2 $e |- ( ph -> B e. _V ) $.
    preqsnd.3 $e |- ( ph -> C e. _V ) $.
    $( Equivalence for a pair equal to a singleton, deduction form.
       (Contributed by Thierry Arnoux, 27-Dec-2016.) $)
    preqsnd $p |- ( ph -> ( { A , B } = { C } <-> ( A = C /\ B = C ) ) ) $=
      ( cvv wcel cpr csn wceq wa wb dfsn2 eqeq2i wo preq12bg oridm syl6bb
      syl5bb syl22anc ) ABHIZCHIZDHIZUEBCJZDKZLZBDLCDLMZNEFGGUHUFDDJZLZUCUDMUEU
      EMMZUIUGUJUFDOPULUKUIUIQUIBCDDHHHHRUISTUAUB $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Conditional operator - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d a x $.  $d x C $.  $d x D $.  $d x X $.  $d x Y $.  $d x V $.  $d x W $.
    $d x ps $.  $d x ta $.  $d x th $.
    ifeqeqx.1 $e |- ( x = X -> A = C ) $.
    ifeqeqx.2 $e |- ( x = Y -> B = a ) $.
    ifeqeqx.3 $e |- ( x = X -> ( ch <-> th ) ) $.
    ifeqeqx.4 $e |- ( x = Y -> ( ch <-> ps ) ) $.
    ifeqeqx.5 $e |- ( ph -> a = C ) $.
    ifeqeqx.6 $e |- ( ( ph /\ ps ) -> th ) $.
    ifeqeqx.y $e |- ( ph -> Y e. V ) $.
    ifeqeqx.x $e |- ( ph -> X e. W ) $.
    $( An equality theorem tailored for ~ ballotlemsf1o (Contributed by Thierry
       Arnoux, 14-Apr-2017.) $)
    ifeqeqx $p |- ( ( ph /\ x = if ( ps , X , Y ) )
                                                  -> a = if ( ch , A , B ) ) $=
      ( cv wceq cif wa eqeq2 csb simplr wsbc simpll simpr sbceq1a biimpd dfsbcq
      sylc wi csbeq1 eqeq2d imbi12d wcel nfcvd csbiegf syl eqtr4d adantr eqcomd
      a1d wn pm3.24 wb sbcieg anbi1d mtbiri pm2.21d anass1rs ex csbeq1a biimprd
      imp ifbothda notbid nsyld anim2d mtoi expdimp ) CMUBZFUCZWFGUCZWFCFGUDZUC
      AEUBBKLUDZUCZUEZFGFWIWFUFGWIWFUFWLCUEZWKWFEWJFUGZUCZWGAWKCUHZWMACEWJUIZWO
      AWKCUJWMWKCWQWPWLCUKWKCWQCEWJULZUMUOBCEKUIZWFEKFUGZUCZUPCELUIZWFELFUGZUCZ
      UPWQWOUPAKLKWJUCZWSWQXAWOCEKWJUNZXEWTWNWFEKWJFUQURUSLWJUCZXBWQXDWOCELWJUN
      ZXGXCWNWFELWJFUQURUSABUEZXAWSXIWTWFAWTWFUCBAWTHWFAKJUTZWTHUCUAEKFHJXJEHVA
      NVBVCRVDVEVFVGABVHZUEZXBXDAXBXKXDAXBXKUEZXDAXMXDAXMBXKUEZBVIZAXBBXKALIUTZ
      XBBVJTCBELIQVKVCVLVMVNVSVOVPVTUOWKWGWOWKFWNWFEWJFVQURVRUOWLCVHZUEZWKWFEWJ
      GUGZUCZWHAWKXQUHZXRAWQVHZXTAWKXQUJXRWKXQYBYAWLXQUKWKXQYBWKCWQWRWAUMUOBWSV
      HZWFEKGUGZUCZUPXBVHZWFELGUGZUCZUPYBXTUPAKLXEYCYBYEXTXEWSWQXFWAXEYDXSWFEKW
      JGUQURUSXGYFYBYHXTXGXBWQXHWAXGYGXSWFELWJGUQURUSABYCYEABYCUEZYEAYIXNXOAYCX
      KBAYCDBAYCDVHAWSDAXJWSDVJUACDEKJPVKVCWAUMABDSVPWBWCWDVNWEXLYHYFXLYGWFAYGW
      FUCZXKAXPYJTELGWFIXPEWFVAOVBVCVEVFVGVTUOWKWHXTWKGXSWFEWJGVQURVRUOVT $.
  $}

  ${
    ifbieq12d2.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    ifbieq12d2.2 $e |- ( ( ph /\ ps ) -> A = C ) $.
    ifbieq12d2.3 $e |- ( ( ph /\ -. ps ) -> B = D ) $.
    $( Equivalence deduction for conditional operators.  (Contributed by
       Thierry Arnoux, 14-Feb-2017.) $)
    ifbieq12d2 $p |- ( ph -> if ( ps , A , B ) = if ( ch , C , D ) ) $=
      ( cif wceq wa wn wo syl6bi imp eqtr4d ex ancld iftrue iffalse orim12d mpi
      exmid notbid eqif sylibr eqcomd ) ACFGKZBDEKZABUJDLZMZBNZUJELZMZOZUJUKLAB
      UNOUQBUEABUMUNUPABULABULABMUJFDABUJFLZABCURHCFGUAPQIRSTAUNUOAUNUOAUNMUJGE
      AUNUJGLZAUNCNUSABCHUFCFGUBPQJRSTUCUDBUJDEUGUHUI $.
  $}

  $( Move a conditional outside of an operation (Contributed by Thierry Arnoux,
     25-Jan-2017.) $)
  ovif $p |- ( if ( ph , A , B ) F C ) = if ( ph , ( A F C ) , ( B F C ) ) $=
    ( cif co oveq1 ifsb ) ABCABCFZDEGBDEGCDEGJBDEHJCDEHI $.

  ${
    elimifd.1 $e |- ( ph -> ( if ( ps , A , B ) = A -> ( ch <-> th ) ) ) $.
    elimifd.2 $e |- ( ph -> ( if ( ps , A , B ) = B -> ( ch <-> ta ) ) ) $.
    $( Elimination of a conditional operator contained in a wff ` ch ` .
       (Contributed by Thierry Arnoux, 25-Jan-2017.) $)
    elimifd $p |- ( ph -> ( ch <-> ( ( ps /\ th ) \/ ( -. ps /\ ta ) ) ) ) $=
      ( wn wo wa wb exmid biantrur a1i andir wceq syl5 pm5.32d iffalse orbi12d
      cif iftrue 3bitrd ) ACBBJZKZCLZBCLZUFCLZKZBDLZUFELZKCUHMAUGCBNOPUHUKMABUF
      CQPAUIULUJUMABCDBBFGUCZFRACDMBFGUDHSTAUFCEUFUNGRACEMBFGUAISTUBUE $.
  $}

  ${
    elim2if.1 $e |- ( if ( ph , A , if ( ps , B , C ) ) = A ->
                                                             ( ch <-> th ) ) $.
    elim2if.2 $e |- ( if ( ph , A , if ( ps , B , C ) ) = B ->
                                                             ( ch <-> ta ) ) $.
    elim2if.3 $e |- ( if ( ph , A , if ( ps , B , C ) ) = C ->
                                                             ( ch <-> et ) ) $.
    $( Elimination of two conditional operators contained in a wff ` ch ` .
       (Contributed by Thierry Arnoux, 25-Jan-2017.) $)
    elim2if $p |- ( ch <-> ( ( ph /\ th ) \/
                       ( -. ph /\ ( ( ps /\ ta ) \/ ( -. ps /\ et ) ) ) ) ) $=
      ( wn wo wa cif wceq wb pm5.32i eqeq1d exmid biantrur andir iftrue iffalse
      syl syl6bir elimifd orbi12i 3bitri ) CAAMZNZCOACOZUKCOZNADOZUKBEOBMFONZOZ
      NULCAUAUBAUKCUCUMUOUNUQACDAAGBHIPZPZGQCDRAGURUDJUFSUKCUPUKBCEFHIUKURHQUSH
      QCERUKUSURHAGURUEZTKUGUKURIQUSIQCFRUKUSURIUTTLUGUHSUIUJ $.

    elim2ifim.1 $e |- ( ph -> th ) $.
    elim2ifim.2 $e |- ( ( -. ph /\ ps ) -> ta ) $.
    elim2ifim.3 $e |- ( ( -. ph /\ -. ps ) -> et ) $.
    $( Elimination of two conditional operators for an implication.
       (Contributed by Thierry Arnoux, 25-Jan-2017.) $)
    elim2ifim $p |- ch $=
      ( wa wn wo ancli ex exmid pm4.42 ancld orim12i sylbi ax-mp elim2if mpbir
      imp ) CADPZAQZBEPZBQZFPZRZPZRZAUKRUQAUAAUJUKUPADMSUKUOUKUKBPZUKUMPZRUOUKB
      UBURULUSUNUKBULUKBEUKBENTUCUIUKUMUNUKUMFUKUMFOTUCUIUDUESUDUFABCDEFGHIJKLU
      GUH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Indexed union - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.  $d y D $.  $d y ph $.
    iuneq12daf.1 $e |- F/ x ph $.
    iuneq12daf.2 $e |- F/_ x A $.
    iuneq12daf.3 $e |- F/_ x B $.
    iuneq12daf.4 $e |- ( ph -> A = B ) $.
    iuneq12daf.5 $e |- ( ( ph /\ x e. A ) -> C = D ) $.
    $( Equality deduction for indexed union, deduction version.  (Contributed
       by Thierry Arnoux, 13-Mar-2017.) $)
    iuneq12daf $p |- ( ph -> U_ x e. A C = U_ x e. B D ) $=
      ( vy cv wcel wrex wb ciun wceq cab df-iun wal eleq2d rexbida rexeqf bitrd
      wa syl alrimiv abbi eqeq12i bitr4i sylib ) ALMZENZBCOZUMFNZBDOZPZLUAZBCEQ
      ZBDFQZRZAURLAUOUPBCOZUQAUNUPBCGABMCNUFEFUMKUBUCACDRVCUQPJUPBCDHIUDUGUEUHU
      SUOLSZUQLSZRVBUOUQLUIUTVDVAVEBLCETBLDFTUJUKUL $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.
    $( Subset equivalence for an indexed union.  (Contributed by Thierry
       Arnoux, 17-Oct-2016.) $)
    ssiun3 $p |- ( A. y e. C E. x e. A y e. B <-> C C_ U_ x e. A B ) $=
      ( ciun wss cv wcel wi wal wral wrex dfss2 df-ral eliun ralbii 3bitr2ri )
      EACDFZGBHZEITSIZJBKUABELTDIACMZBELBESNUABEOUAUBBEATCDPQR $.
  $}

  ${
    ssiun2sf.1 $e |- F/_ x A $.
    ssiun2sf.2 $e |- F/_ x C $.
    ssiun2sf.3 $e |- F/_ x D $.
    ssiun2sf.4 $e |- ( x = C -> B = D ) $.
    $( Subset relationship for an indexed union.  (Contributed by Thierry
       Arnoux, 31-Dec-2016.) $)
    ssiun2sf $p |- ( C e. A -> D C_ U_ x e. A B ) $=
      ( wcel ciun wss cv wi nfel nfiu1 nfss nfim wceq eleq1 imbi12d vtoclgf
      sseq1d ssiun2 pm2.43i ) DBJZEABCKZLZAMZBJZCUGLZNUFUHNADBGUFUHAADBGFOAEUGH
      ABCPQRUIDSZUJUFUKUHUIDBTULCEUGIUCUAABCUDUBUE $.
  $}

  ${
    $d i j n $.  $d j k n F $.  $d j k n ph $.
    iuninc.1 $e |- ( ph -> F Fn NN ) $.
    iuninc.2 $e |- ( ( ph /\ n e. NN ) -> ( F ` n ) C_ ( F ` ( n + 1 ) ) ) $.
    $( The union of an increasing collection of sets is its last element.
       (Contributed by Thierry Arnoux, 22-Jan-2017.) $)
    iuninc $p |- ( ( ph /\ i e. NN ) ->
      U_ n e. ( 1 ... i ) ( F ` n ) = ( F ` i ) ) $=
      ( vk wcel c1 cfz co cfv ciun wceq wi caddc iuneq1d fveq2 ax-mp cvv imbi2d
      vj cv cn oveq2 eqeq12d csn cz fzsn iuneq1 1ex iunxsn eqtri a1i cun simpll
      1z wa cuz elnnuz fzsuc sylbi iunxun uneq2i syl6eq syl simpr uneq1d simplr
      ovex wss wsb sbt sbim sban nfv sbf clelsb3 anbi12i bitr2i wsbc csb wb vex
      sbsbc sbcssg csbfv2g csbvarg fveq2i csbov1g oveq1i 3eqtri sseq12i 3bitrri
      imbi12i bitr4i mpbi ssequn1 sylib syl2anc 3eqtrd exp31 a2d nnind impcom )
      BUCZUDHACIXFJKZCUCZDLZMZXFDLZNZACIUBUCZJKZXIMZXMDLZNZOACIIJKZXIMZIDLZNZOA
      CIGUCZJKZXIMZYBDLZNZOACIYBIPKZJKZXIMZYGDLZNZOAXLOUBGXFXMINZXQYAAYLXOXSXPX
      TYLCXNXRXIXMIIJUEQXMIDRUFUAXMYBNZXQYFAYMXOYDXPYEYMCXNYCXIXMYBIJUEQXMYBDRU
      FUAXMYGNZXQYKAYNXOYIXPYJYNCXNYHXIXMYGIJUEQXMYGDRUFUAXMXFNZXQXLAYOXOXJXPXK
      YOCXNXGXIXMXFIJUEQXMXFDRUFUAYAAXSCIUGZXIMZXTXRYPNZXSYQNIUHHYRUQIUISCXRYPX
      IUJSCIXIXTUKXHIDRULUMUNYBUDHZAYFYKYSAYFYKYSAURZYFURZYIYDYJUOZYEYJUOZYJUUA
      YSYIUUBNYSAYFUPZYSYICYCYGUGZUOZXIMZUUBYSCYHUUFXIYSYBIUSLHYHUUFNYBUTIYBVAV
      BQUUGYDCUUEXIMZUOUUBCYCUUEXIVCUUHYJYDCYGXIYJYBIPVJXHYGDRULVDUMVEVFUUAYDYE
      YJYTYFVGVHUUAAYSUUCYJNZYSAYFVIUUDAYSURZYEYJVKZUUIAXHUDHZURZXIXHIPKZDLZVKZ
      OZCGVLZUUJUUKOZUUQCGFVMUURUUMCGVLZUUPCGVLZOUUSUUMUUPCGVNUUJUUTUUKUVAUUTAC
      GVLZUULCGVLZURUUJAUULCGVOUVBAUVCYSACGACVPVQGCUDVRVSVTUVAUUPCYBWAZCYBXIWBZ
      CYBUUOWBZVKZUUKUUPCGWEYBTHZUVDUVGWCGWDZCYBXIUUOTWFSUVEYEUVFYJUVECYBXHWBZD
      LZYEUVHUVEUVKNUVICYBXHTDWGSUVJYBDUVHUVJYBNUVICYBTWHSZWIUMUVFCYBUUNWBZDLZU
      VJIPKZDLYJUVHUVFUVNNUVICYBUUNTDWGSUVMUVODUVHUVMUVONUVICYBXHIPTWJSWIUVOYGD
      UVJYBIPUVLWKWIWLWMWNWOWPWQYEYJWRWSWTXAXBXCXDXE $.
  $}

  ${
    $d x A $.  $d x O $.
    $( The intersection of a set is the complement of the union of the
       complements.  (Contributed by Thierry Arnoux, 19-Dec-2016.) $)
    iundifdifd $p |- ( A C_ ~P O ->
      ( A =/= (/) -> |^| A = ( O \ U_ x e. A ( O \ x ) ) ) ) $=
      ( cpw wss c0 cint cv cdif ciun wceq wa ciin iundif2 intiin difeq2i eqtr4i
      wne cuni intssuni2 unipw syl6sseq dfss4 sylib syl5req ex ) BCDZEZBFRZBGZC
      ABCAHZIJZIZKUHUILZUMCCUJIZIZUJULUOCULCABUKMZIUOABCUKNUJUQCABOPQPUNUJCEUPU
      JKUNUJUGSCBUGTCUAUBUJCUCUDUEUF $.
  $}

  ${
    $d x A $.  $d x O $.
    iundifdif.o $e |- O e. _V $.
    iundifdif.2 $e |- A C_ ~P O $.
    $( The intersection of a set is the complement of the union of the
       complements.  TODO shorten using ~ iundifdifd (Contributed by Thierry
       Arnoux, 4-Sep-2016.) $)
    iundifdif $p |- ( A =/= (/) -> |^| A = ( O \ U_ x e. A ( O \ x ) ) ) $=
      ( c0 wne cv cdif ciun cint ciin iundif2 intiin difeq2i eqtr4i wss wceq wa
      cpw cuni jctl intssuni2 unipw sseq2i biimpi 3syl dfss4 sylib syl5req ) BF
      GZCABCAHZIJZICCBKZIZIZUNUMUOCUMCABULLZIUOABCULMUNUQCABNOPOUKUNCQZUPUNRUKB
      CTZQZUKSUNUSUAZQZURUKUTEUBBUSUCVBURVACUNCUDUEUFUGUNCUHUIUJ $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d x y z C $.  $d x z D $.  $d x y F $.
    $d x y z ph $.
    iunrdx.1 $e |- ( ph -> F : A -onto-> C ) $.
    iunrdx.2 $e |- ( ( ph /\ y = ( F ` x ) ) -> D = B ) $.
    $( Re-index an indexed union.  (Contributed by Thierry Arnoux,
       6-Apr-2017.) $)
    iunrdx $p |- ( ph -> U_ x e. A B = U_ y e. C D ) $=
      ( vz cv wcel wrex cab ciun cfv wfo wf df-iun fof syl ffvelrnda wceq sylan
      foelrn wa eleq2d rexxfrd bicomd abbidv 3eqtr4g ) AKLZEMZBDNZKOUMGMZCFNZKO
      BDEPCFGPAUOUQKAUQUOAUPUNCBBLZHQZFDADFURHADFHRZDFHSIDFHUAUBUCAUTCLZFMVAUSU
      DZBDNIBDFVAHUFUEAVBUGGEUMJUHUIUJUKBKDETCKFGTUL $.
  $}

  ${
    $d A x y $.  $d B y $.  $d F x y $.
    $( Preimage of an indexed union.  (Contributed by Thierry Arnoux,
       27-Mar-2018.) $)
    iunpreima $p |- ( Fun F 
      -> ( `' F " U_ x e. A B ) = U_ x e. A ( `' F " B ) ) $=
      ( vy wfun ccnv ciun cima cv cfv wcel cdm crab wrex wb a1i fncnvima2 sylbi
      wceq eliun rabbidv wfn funfn iunrab 3eqtr4d iuneq2d eqtr4d ) DFZDGZABCHZI
      ZABEJDKZCLZEDMZNZHZABUJCIZHUIUMUKLZEUONZUNABOZEUONZULUQUIUSVAEUOUSVAPUIAU
      MBCUAQUBUIDUOUCZULUTTDUDZEUOUKDRSUQVBTUIUNAEBUOUEQUFUIABURUPUIVCURUPTVDEU
      OCDRSUGUH $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Disjointness - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y A $. $d x y B $.
    $( In case ` x ` is not free in ` B ` , disjointness is not so interesting
       since it reduces to cases where ` A ` is a singleton.  (Google Groups
       discussion with Peter Masza) (Contributed by
       Thierry Arnoux, 26-Jul-2018.) $)
    disjnf $p |- ( Disj_ x e. A B <-> ( B = (/) \/ E* x x e. A ) ) $=
      ( vy wdisj c0 wceq cv wral wcel wmo cin eqidd disjor orcom ralbii r19.32v
      wo bitri 3bitri inidm eqeq1i orbi1i moel orbi2i bitr4i ) ABCEZCFGZAHZDHGZ
      DBIZABIZRZUHUIBJAKZRUGCCLZFGZULRZUMUGUJUPRZDBIZABIUPUKRZABIUQBCCADUJCMNUS
      UTABUSUPUJRZDBIUTURVADBUJUPOPUPUJDBQSPUPUKABQTUPUHULUOCFCUAUBUCSUNULUHADB
      UDUEUF $.
  $}
   
  ${
    $d x y z $.  $d y z A $.  $d z B $.  $d z C $.
    cbvdisjf.1 $e |- F/_ x A $.
    cbvdisjf.2 $e |- F/_ y B $.
    cbvdisjf.3 $e |- F/_ x C $.
    cbvdisjf.4 $e |- ( x = y -> B = C ) $.
    $( Change bound variables in a disjoint collection.  (Contributed by
       Thierry Arnoux, 6-Apr-2017.) $)
    cbvdisjf $p |- ( Disj_ x e. A B <-> Disj_ y e. A C ) $=
      ( vz cv wcel wrmo wal wdisj wa wmo nfcri nfan df-rmo nfv weq eleq1 eleq2d
      anbi12d cbvmo 3bitr4i albii df-disj ) JKZDLZACMZJNUJELZBCMZJNACDOBCEOULUN
      JAKZCLZUKPZAQBKZCLZUMPZBQULUNUQUTABUPUKBUPBUABJDGRSUSUMAABCFRAJEHRSABUBZU
      PUSUKUMUOURCUCVADEUJIUDUEUFUKACTUMBCTUGUHAJCDUIBJCEUIUG $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.
    disjss1f.1 $e |- F/_ x A $.
    disjss1f.2 $e |- F/_ x B $.
    $( A subset of a disjoint collection is disjoint.  (Contributed by Thierry
       Arnoux, 6-Apr-2017.) $)
    disjss1f $p |- ( A C_ B -> ( Disj_ x e. B C -> Disj_ x e. A C ) ) $=
      ( vy wss cv wcel wrmo wal wdisj ssrmo alimdv df-disj 3imtr4g ) BCHZGIDJZA
      CKZGLSABKZGLACDMABDMRTUAGSABCEFNOAGCDPAGBDPQ $.
  $}

  ${
    $d x A $.  $d x B $.
    $( A trivial partition into a subset and its complement.  (Contributed by
       Thierry Arnoux, 25-Dec-2016.) $)
    disjdifprg $p |- ( ( A e. V /\ B e. W ) ->
        Disj_ x e. { ( B \ A ) , A } x ) $=
      ( wcel wa c0 wceq cdif cpr wdisj simpr wb elex cvv 0ex mpbiri cin id dif0
      cv csn disjxsn eqidd a1i preqsnd adantr mpbir2and wne in0 disjprg syl3anc
      disjeq1d pm2.61dane ad2antlr difeq2 syl6eq preq12d adantl mpbird wn incom
      eqtr3i difexg ad2antrr wss ssid ssdifeq0 notbii nssne2 sylan2br pm2.61dan
      disjdif mpan ) BDFZCEFZGZBHIZACBJZBKZAUBZLZVRVSGWCACHKZWBLZVQWEVPVSVQWECH
      VQCHIZGZWEAHUCZWBLAHWBUDWGAWDWHWBWGWDWHIZWFHHIZVQWFMWGHUEVQWIWFWJGNWFVQCH
      HCEOZHPFZVQQUFZWMUGUHUIUNRVQCHUJZGZWECHSHIZCUKWOCPFZWLWNWEWPNVQWQWNWKUHWL
      WOQUFVQWNMACHWBCHPWBCITWBHITULUMRUOUPVSWCWENVRVSAWAWDWBVSVTCBHVSVTCHJCBHC
      UQCUAURVSTUSUNUTVAVRVSVBZGZWCVTBSZHIZBVTSWTHBVTVCBCVNVDWSVTPFZBPFZVTBUJZW
      CXANVQXBVPWRCBEVEUPVPXCVQWRBDOVFWRXDVRVTVTVGZWRXDVTVHWRXEBVTVGZVBXDXFVSBC
      VIVJVTBVTVKVLVOUTAVTBWBVTBPWBVTITWBBITULUMRVM $.
  $}

  ${
    $d x A $.  $d x B $.
    $( A trivial partition of a set into its difference and intersection with
       another set.  (Contributed by Thierry Arnoux, 25-Dec-2016.) $)
    disjdifprg2 $p |-
        ( A e. V -> Disj_ x e. { ( A \ B ) , ( A i^i B ) } x ) $=
      ( wcel cin cdif cpr wdisj cvv inex1g elex disjdifprg syl2anc difin preq1i
      cv wceq a1i disjeq1d mpbid ) BDEZABBCFZGZUCHZAQZIZABCGZUCHZUFIUBUCJEBJEUG
      BCDKBDLAUCBJJMNUBAUEUIUFUEUIRUBUDUHUCBCOPSTUA $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d z C $.  $d x z Y $.
    disjif.1 $e |- F/_ x C $.
    disjif.2 $e |- ( x = Y -> B = C ) $.
    $( Property of a disjoint collection: if ` B ( x ) = C ` and
       ` B ( Y ) = D ` , and ` x =/= Y ` , then ` B ` and ` C ` are disjoint.
       (Contributed by Thierry Arnoux, 30-Dec-2016.) $)
    disji2f $p |- ( ( Disj_ x e. A B /\ ( x e. A /\ Y e. A ) /\
      x =/= Y ) -> ( B i^i C ) = (/) ) $=
      ( vy vz cv wcel wa cin c0 wceq wo weq csb wral eqeq1d wdisj df-ne disjors
      wn equequ1 csbeq1 csbid syl6eq ineq1d orbi12d eqeq2 csbhypf ineq2d rspc2v
      wne nfcv syl5bi impcom ord 3impia ) ABCUAZAJZBKEBKLZVBEUOZCDMZNOZVDVBEOZU
      DVAVCLZVFVBEUBVHVGVFVCVAVGVFPZVAHIQZAHJZCRZAIJZCRZMZNOZPZIBSHBSVCVIABCHIU
      CVQVIAIQZCVNMZNOZPHIVBEBBHAQZVJVRVPVTHAIUEWAVOVSNWAVLCVNWAVLAVBCRCAVKVBCU
      FACUGUHUITUJVMEOZVRVGVTVFVMEVBUKWBVSVENWBVNDCAIECDAEUPFGULUMTUJUNUQURUSUQ
      UT $.

    $( Property of a disjoint collection: if ` B ( x ) ` and ` B ( Y ) = D `
       have a common element ` Z ` , then ` x = Y ` .  (Contributed by Thierry
       Arnoux, 30-Dec-2016.) $)
    disjif $p |- ( ( Disj_ x e. A B /\ ( x e. A /\ Y e. A ) /\
      ( Z e. B /\ Z e. C ) ) -> x = Y ) $=
      ( wcel wa wdisj cv cin c0 wne wceq inelcm disji2f 3expia necon1d syl3an3
      3impia ) FCIFDIJABCKZALZBIEBIJZCDMZNOZUDEPZFCDQUCUEUGUHUCUEJUDEUFNUCUEUDE
      OUFNPABCDEGHRSTUBUA $.
  $}

  ${
    $d i j x $.  $d x A $.  $d j x B $.  $d i x C $.
    disjorf.1 $e |- F/_ i A $.
    disjorf.2 $e |- F/_ j A $.
    disjorf.3 $e |- ( i = j -> B = C ) $.
    $( Two ways to say that a collection ` B ( i ) ` for ` i e. A ` is
       disjoint.  (Contributed by Thierry Arnoux, 8-Mar-2017.) $)
    disjorf $p |- ( Disj_ i e. A B <->
      A. i e. A A. j e. A ( i = j \/ ( B i^i C ) = (/) ) ) $=
      ( vx cv wcel wal wceq wo wral wi ralcom4 wex bitri bitr4i wrmo c0 df-disj
      wdisj cin wa wn orcom df-or neq0 exbii imbi1i 19.23v 3bitri ralbii eleq2d
      elin nfv rmo4f albii 3bitr4i ) DABUDIJZBKZDAUAZILZDJEJMZBCUEZUBMZNZEAOZDA
      OZDIABUCVCVBCKZUFZVFPZEAOZILZDAOVODAOZILVKVEVODIAQVJVPDAVJVNILZEAOVPVIVRE
      AVIVHVFNVHUGZVFPZVRVFVHUHVHVFUIVTVMIRZVFPVRVSWAVFVSVBVGKZIRWAIVGUJWBVMIVB
      BCUQUKSULVMVFIUMTUNUOVNEIAQSUOVDVQIVCVLDEAFGVLDURVFBCVBHUPUSUTVAT $.
  $}

  ${
    $d i j x $.  $d i j A $.  $d i j B $.
    disjorsf.1 $e |- F/_ x A $.
    $( Two ways to say that a collection ` B ( i ) ` for ` i e. A ` is
       disjoint.  (Contributed by Thierry Arnoux, 8-Mar-2017.) $)
    disjorsf $p |- ( Disj_ x e. A B <-> A. i e. A A. j e. A
      ( i = j \/ ( [_ i / x ]_ B i^i [_ j / x ]_ B ) = (/) ) ) $=
      ( wdisj cv csb wceq cin c0 wo wral nfcsb1v csbeq1a cbvdisjf csbeq1 disjor
      nfcv bitri ) ABCGDBADHZCIZGUBEHZJUCAUDCIZKLJMEBNDBNADBCUCFDCTAUBCOAUBCPQB
      UCUEDEAUBUDCRSUA $.
  $}

  ${
    $d x y z $.  $d y z A $.  $d y z B $.  $d z C $.  $d x z Y $.
    disjif2.1 $e |- F/_ x A $.
    disjif2.2 $e |- F/_ x C $.
    disjif2.3 $e |- ( x = Y -> B = C ) $.
    $( Property of a disjoint collection: if ` B ( x ) ` and ` B ( Y ) = D `
       have a common element ` Z ` , then ` x = Y ` .  (Contributed by Thierry
       Arnoux, 6-Apr-2017.) $)
    disjif2 $p |- ( ( Disj_ x e. A B /\ ( x e. A /\ Y e. A ) /\
      ( Z e. B /\ Z e. C ) ) -> x = Y ) $=
      ( vy vz wcel wa cv cin c0 wceq wo weq csb wdisj wne wral disjorsf equequ1
      inelcm csbeq1 csbid syl6eq ineq1d eqeq1d orbi12d eqeq2 nfcv ineq2d rspc2v
      csbhypf syl5bi impcom ord necon1ad 3impia syl3an3 ) FCLFDLMABCUAZANZBLEBL
      MZCDOZPUBZVEEQZFCDUFVDVFVHVIVDVFMZVIVGPVJVIVGPQZVFVDVIVKRZVDJKSZAJNZCTZAK
      NZCTZOZPQZRZKBUCJBUCVFVLABCJKGUDVTVLAKSZCVQOZPQZRJKVEEBBJASZVMWAVSWCJAKUE
      WDVRWBPWDVOCVQWDVOAVECTCAVNVECUGACUHUIUJUKULVPEQZWAVIWCVKVPEVEUMWEWBVGPWE
      VQDCAKECDAEUNHIUQUOUKULUPURUSUTVAVBVC $.
  $}

  ${
    $d i j x y z A $.  $d i j y z B $.
    $( Rewriting a disjoint collection into a partition of its image set
       (Contributed by Thierry Arnoux, 30-Dec-2016.) $)
    disjabrex $p |- ( Disj_ x e. A B
                                   -> Disj_ y e. { z | E. x e. A z = B } y ) $=
      ( vi vj wdisj cv wcel csb wa cab cuni wceq wral cvv vex simpllr syl nfcri
      wrex nfdisj1 nfcv nfv nfan nfab nfuni nfcsb1 nfeq1 nfral eqeq2 raleqbi1dv
      nfcsb1v a1i simplll simprl simplr simprr csbeq1a syl122anc simpr eqeltrrd
      csn disjif wb eleq2d mpbid jca impbida equcom syl6bb abbidv df-sn syl6eqr
      unieqd unisn syl6eq csbeq1 csbid ralrimiva elabreximd invdisj ) ADEHZAFIZ
      DJZGIZAWEEKZJZLZFMZNZEKZBIZOZGWNPZBCIEOADUBCMZPBWQWNHWDWPBWQWDWMEOZGEPWPA
      CWNEDQADEUCWOAGWNAWNUDAWMWNAWLEAWKWJAFWFWIAWFAUEAGWHAWEEUNZUAUFUGUHUIUJUK
      WOWRGWNEWNEWMULUMWNQJWDBRUOWDAIZDJZLZWRGEXBWGEJZLZWLWTOZWRXDWLWTVDZNWTXDW
      KXFXDWKWEWTOZFMXFXDWJXGFXDWJWTWEOZXGXDWJXHXDWJLWDXAWFXCWIXHWDXAXCWJUPWDXA
      XCWJSXDWFWIUQXBXCWJURXDWFWIUSADEWHWEWGWSAWEEUTZVEVAXDXHLZWFWIXJWTWEDXDXHV
      BZWDXAXCXHSVCXJXCWIXBXCXHURXJXHXCWIVFXKXHEWHWGXIVGTVHVIVJAFVKVLVMFWTVNVOV
      PWTARVQVRXEWMAWTEKEAWLWTEVSAEVTVRTWAWBWABGWQWNWMWCT $.
  $}

  ${
    $d i j x y z $.  $d i j y z A $.  $d i j y z B $.
    disjabrexf.1 $e |- F/_ x A $.
    $( Rewriting a disjoint collection into a partition of its image set
       (Contributed by Thierry Arnoux, 30-Dec-2016.)  (Revised by Thierry
       Arnoux, 9-Mar-2017.) $)
    disjabrexf $p |- ( Disj_ x e. A B
                                   -> Disj_ y e. { z | E. x e. A z = B } y ) $=
      ( vi vj wdisj cv wcel csb wa cab cuni wceq wral cvv nfcri syl wrex nfcsb1
      nfdisj1 nfcv nfcsb1v nfan nfab nfuni nfeq1 nfral eqeq2 raleqbi1dv vex a1i
      csn simplll simpllr simprl simplr simprr csbeq1a syl122anc simpr eqeltrrd
      disjif2 wb eleq2d mpbid impbida equcom syl6bb abbidv df-sn syl6eqr unieqd
      jca unisn syl6eq csbeq1 csbid ralrimiva elabreximd invdisj ) ADEIZAGJZDKZ
      HJZAWEELZKZMZGNZOZELZBJZPZHWNQZBCJEPADUACNZQBWQWNIWDWPBWQWDWMEPZHEQWPACWN
      EDRADEUCWOAHWNAWNUDAWMWNAWLEAWKWJAGWFWIAAGDFSAHWHAWEEUEZSUFUGUHUBUIUJWOWR
      HWNEWNEWMUKULWNRKWDBUMUNWDAJZDKZMZWRHEXBWGEKZMZWLWTPZWRXDWLWTUOZOWTXDWKXF
      XDWKWEWTPZGNXFXDWJXGGXDWJWTWEPZXGXDWJXHXDWJMWDXAWFXCWIXHWDXAXCWJUPWDXAXCW
      JUQXDWFWIURXBXCWJUSXDWFWIUTADEWHWEWGFWSAWEEVAZVEVBXDXHMZWFWIXJWTWEDXDXHVC
      ZWDXAXCXHUQVDXJXCWIXBXCXHUSXJXHXCWIVFXKXHEWHWGXIVGTVHVPVIAGVJVKVLGWTVMVNV
      OWTAUMVQVRXEWMAWTELEAWLWTEVSAEVTVRTWAWBWABHWQWNWMWCT $.
  $}

  ${
    $d x y z A $.  $d x y z F $.  $d y z B $.
    $( A preimage of a disjoint set is disjoint.  (Contributed by Thierry
       Arnoux, 7-Feb-2017.) $)
    disjpreima $p |- ( ( Fun F /\ Disj_ x e. A B )
                                              -> Disj_ x e. A ( `' F " B ) ) $=
      ( vy vz wdisj cima cv wceq csb cin c0 wo wral csbima12 cvv wcel csbconstg
      vex wfun ccnv inpreima imaeq2 ima0 syl6eq sylan9req ax-mp imaeq1i ineq12i
      ex eqtri eqeq1i syl6ibr orim2d ralimdv disjors 3imtr4g imp ) DUAZABCGZABD
      UBZCHZGZUTEIZFIZJZAVECKZAVFCKZLZMJZNZFBOZEBOVGAVEVCKZAVFVCKZLZMJZNZFBOZEB
      OVAVDUTVMVSEBUTVLVRFBUTVKVQVGUTVKVBVHHZVBVIHZLZMJZVQUTVKWCUTVKWBVBVJHZMVH
      VIDUCVKWDVBMHMVJMVBUDVBUEUFUGUKVPWBMVNVTVOWAVNAVEVBKZVHHVTAVECVBPWEVBVHVE
      QRWEVBJETAVEVBQSUHUIULVOAVFVBKZVIHWAAVFCVBPWFVBVIVFQRWFVBJFTAVFVBQSUHUIUL
      UJUMUNUOUPUPABCEFUQABVCEFUQURUS $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.
    $( If a collection is disjoint, so is the collection of the intersections
       with a given set.  (Contributed by Thierry Arnoux, 14-Feb-2017.) $)
    disjin $p |- ( Disj_ x e. B C -> Disj_ x e. B ( C i^i A ) ) $=
      ( vy cv wcel wrmo wal wdisj wa wi inss1 sseli anim2i ax-gen rmoimi2 alimi
      cin df-disj 3imtr4i ) EFZDGZACHZEIUBDBSZGZACHZEIACDJACUEJUDUGEUFUCACCAFCG
      ZUFKUHUCKLAUFUCUHUEDUBDBMNOPQRAECDTAECUETUA $.
  $}

  ${
    $d a c p q r x A $.  $d b d p q r y B $.  $d a c p C $.  $d b d p D $.
    $d q r x E $.  $d q r y F $.  $d q r ph $.
    disjxpin.1 $e |- ( x = ( 1st ` p ) -> C = E ) $.
    disjxpin.2 $e |- ( y = ( 2nd ` p ) -> D = F ) $.
    disjxpin.3 $e |- ( ph -> Disj_ x e. A C ) $.
    disjxpin.4 $e |- ( ph -> Disj_ y e. B D ) $.
    $( Derive a disjunction over a cross product from the disjunctions over its
       first and second elements.  (Contributed by Thierry Arnoux,
       9-Mar-2018.) $)
    disjxpin $p |- ( ph -> Disj_ p e. ( A X. B ) ( E i^i F ) ) $=
      ( wceq cin csb c0 wo wa vq vr va vc vb vd cv cxp wral wdisj wcel c1st cfv
      c2nd xp1st ad2antrl ad2antll simpl sylib eqeq1 csbeq1 ineq1d eqeq1d eqeq2
      disjors orbi12d ineq2d rspc2v syl5 imp syl21anc xp2nd jca anddi wb xpopth
      orass adantl biimpd wi wss inss2 csbin ineq12i in4 eqtri cvv vex csbnestg
      ax-mp fvex nfcv csbief csbeq2i fveq2 3eqtr3ri 3sstr4i sseq0 adantld inss1
      mpan a1i adantrd jaod orim12d mpd ralrimivva sylibr ) AUAUGZUBUGZOZJXIHIP
      ZQZJXJXLQZPZROZSZUBDEUHZUIUAXRUIJXRXLUJAXQUAUBXRXRAXIXRUKZXJXRUKZTZTZXIUL
      UMZXJULUMZOZXIUNUMZXJUNUMZOZTZYECYFGQZCYGGQZPZROZTZBYCFQZBYDFQZPZROZYHTZY
      RYMTZSZSZSZXQYBYIYNSUUASZUUCYBYEYRSZYHYMSZTUUDYBUUEUUFYBYCDUKZYDDUKZAUUEX
      SUUGAXTXIDEUOUPXTUUHAXSXJDEUOUQAYAURZUUGUUHTZAUUEAUCUGZUDUGZOZBUUKFQZBUUL
      FQZPZROZSZUDDUIUCDUIZUUJUUEABDFUJUUSMBDFUCUDVEUSUURUUEYCUULOZYOUUOPZROZSU
      CUDYCYDDDUUKYCOZUUMUUTUUQUVBUUKYCUULUTUVCUUPUVARUVCUUNYOUUOBUUKYCFVAVBVCV
      FUULYDOZUUTYEUVBYRUULYDYCVDUVDUVAYQRUVDUUOYPYOBUULYDFVAVGVCVFVHVIVJVKYBYF
      EUKZYGEUKZAUUFXSUVEAXTXIDEVLUPXTUVFAXSXJDEVLUQUUIUVEUVFTZAUUFAUEUGZUFUGZO
      ZCUVHGQZCUVIGQZPZROZSZUFEUIUEEUIZUVGUUFACEGUJUVPNCEGUEUFVEUSUVOUUFYFUVIOZ
      YJUVLPZROZSUEUFYFYGEEUVHYFOZUVJUVQUVNUVSUVHYFUVIUTUVTUVMUVRRUVTUVKYJUVLCU
      VHYFGVAVBVCVFUVIYGOZUVQYHUVSYMUVIYGYFVDUWAUVRYLRUWAUVLYKYJCUVIYGGVAVGVCVF
      VHVIVJVKVMYEYRYHYMVNUSYIYNUUAVQUSYBYIXKUUBXPYBYIXKYAYIXKVOAXIXJDEDEVPVRVS
      YBYNXPUUAYBYMXPYEYMXPVTYBXOYLWAYMXPJXIHQZJXJHQZPZJXIIQZJXJIQZPZPZUWGXOYLU
      WDUWGWBXOUWBUWEPZUWCUWFPZPUWHXMUWIXNUWJJXIHIWCJXJHIWCWDUWBUWEUWCUWFWEWFZY
      JUWEYKUWFJXICJUGZUNUMZGQZQZCJXIUWMQZGQZUWEYJXIWGUKZUWOUWQOUAWHZJCXIUWMGWG
      WIWJJXIUWNICUWMGIUWLUNWKCIWLLWMZWNUWPYFOUWQYJOJXIUWMYFUWSJYFWLUWLXIUNWOWM
      CUWPYFGVAWJWPJXJUWNQZCJXJUWMQZGQZUWFYKXJWGUKZUXAUXCOUBWHZJCXJUWMGWGWIWJJX
      JUWNIUWTWNUXBYGOUXCYKOJXJUWMYGUXEJYGWLUWLXJUNWOWMCUXBYGGVAWJWPWDWQXOYLWRX
      AXBZWSYBYSXPYTYBYRXPYHYRXPVTYBXOYQWAYRXPUWHUWDXOYQUWDUWGWTUWKYOUWBYPUWCJX
      IBUWLULUMZFQZQZBJXIUXGQZFQZUWBYOUWRUXIUXKOUWSJBXIUXGFWGWIWJJXIUXHHBUXGFHU
      WLULWKBHWLKWMZWNUXJYCOUXKYOOJXIUXGYCUWSJYCWLUWLXIULWOWMBUXJYCFVAWJWPJXJUX
      HQZBJXJUXGQZFQZUWCYPUXDUXMUXOOUXEJBXJUXGFWGWIWJJXJUXHHUXLWNUXNYDOUXOYPOJX
      JUXGYDUXEJYDWLUWLXJULWOWMBUXNYDFVAWJWPWDWQXOYQWRXAXBXCYBYMXPYRUXFWSXDXDXE
      XFXGJXRXLUAUBVEXH $.
  $}

  ${
    $d a b k m n x y $.  $d a b m x y A $.  $d a b m x y B $.  $d k n x N $.
    iundisjf.1 $e |- F/_ k A $.
    iundisjf.2 $e |- F/_ n B $.
    iundisjf.3 $e |- ( n = k -> A = B ) $.
    $( Rewrite a countable union as a disjoint union.  Cf. ~ iundisj
       (Contributed by Thierry Arnoux, 31-Dec-2016.) $)
    iundisjf $p |- U_ n e. NN A = U_ n e. NN ( A \ U_ k e. ( 1 ..^ n ) B ) $=
      ( vx vm cn ciun c1 cv cfzo wcel wrex cr clt nfcv nfcri cdif csb crab ccnv
      co csup wa cuz cfv wss wne ssrab2 nnuz sseqtri biimpri infmssuzcl sylancr
      c0 rabn0 nfrab1 nfsup nfcsb1 wceq csbeq1a eleq2d elrabf simpld simprd wbr
      sylib nnred ltnrd eliun nfrex nfrab nfbr ad2antrr elfzouz syl6eleqr simpr
      ad2antlr sylanbrc infmssuzle elfzolt2 lelttrd exp31 rexlimd syl5bi eldifd
      cle mtod csbeq1 nfeq2 nfov oveq2 eqidd iuneq12df difeq12d syl2anc nfcsb1v
      rspcev nfv nfiun nfdif iuneq1d cbvrex sylibr eldifi reximi impbii 3bitr4i
      eqriv ) HDJAKZDJACLDMZNUEZBKZUAZKZHMZAOZDJPZXSXQOZDJPZXSXMOXSXROYAYCYAXSD
      IMZAUBZCLYDNUEZBKZUAZOZIJPZYCYAXTDJUCZQRUDZUFZJOZXSDYMAUBZCLYMNUEZBKZUAZO
      ZYJYAYNXSYOOZYAYMYKOZYNYTUGYAYKLUHUIZUJZYKURUKZUUAYKJUUBXTDJULUMUNZUUDYAX
      TDJUSUOYKLUPUQXTYTDYMJDYKQYLXTDJUTDQSDYLSVAZDJSZDHYODYMAUUFVBTXNYMVCAYOXS
      DYMAVDVEVFVJZVGZYAXSYOYQYAYNYTUUHVHYAXSYQOZYMYMRVIZYAYMYAYMUUIVKZVLUUJXSB
      OZCYPPYAUUKCXSYPBVMYAUUMUUKCYPXTCDJCJSZCHAETZVNCYMYMRCYKQYLXTCDJUUOUUNVOC
      QSCYLSVAZCRSUUPVPYACMZYPOZUUMUUKYAUURUGZUUMUGZYMUUQYMYAYMQOUURUUMUULVQZUU
      TUUQUURUUQJOZYAUUMUURUUQUUBJUUQLYMVRUMVSWAZVKUVAUUTUUCUUQYKOZYMUUQWJVIUUE
      UUTUVBUUMUVDUVCUUSUUMVTXTUUMDUUQJDUUQSUUGDHBFTXNUUQVCABXSGVEVFWBUUQYKLWCU
      QUURUUQYMRVIYAUUMUUQLYMWDWAWEWFWGWHWKWIYIYSIYMJYDYMVCZYHYRXSUVEYEYOYGYQDY
      DYMAWLUVECYFYPBBCYDYMUUPWMCYFSCLYMNCLSCNSUUPWNYDYMLNWOUVEBWPWQWRVEXAWSYBY
      IDIJYBIXBDHYHDYEYGDYDAWTCDYFBDYFSFXCXDTXNYDVCZXQYHXSUVFAYEXPYGDYDAVDUVFCX
      OYFBXNYDLNWOXEWRVEXFXGYBXTDJXSAXPXHXIXJDXSJAVMDXSJXQVMXKXL $.

    $( A disjoint union is disjoint.  Cf. ~ iundisj2 (Contributed by Thierry
       Arnoux, 30-Dec-2016.) $)
    iundisj2f $p |- Disj_ n e. NN ( A \ U_ k e. ( 1 ..^ n ) B ) $=
      ( vx vy va vb cn c1 cv cfzo weq csb cin c0 wcel ciun cdif wdisj wceq wral
      co wo wtru tru eqeq12 csbeq1 ineqan12d eqeq1d orbi12d equcom syl6bb incom
      wa syl6eq cr wss nnssre a1i biidd cle wbr w3a wn wne necom df-ne bitri wb
      clt nnre id leltne syl3an wi vex nfcsb1v nfcv nfiun nfdif csbeq1a iuneq1d
      oveq2 difeq12d csbief ineq12i cuz cz simp1 nnuz syl6eleq simp2 nnzd simp3
      cfv elfzo2 syl3anbrc nfcsb csbhypf equcoms eqcomd ssiun2sf ssdifssd ssrin
      syl5eqss disjdif sseq0 sylancl 3expia 3adant3 sylbird syl5bir orrd adantl
      syl wlogle mpan rgen2a disjors mpbir ) DLACMDNZOUFZBUAZUBZUCHIPZDHNZYHQZD
      INZYHQZRZSUDZUGZILUEHLUEYPHILUHYJLTZYLLTZURZYPUIUHJKPZDJNZYHQZDKNZYHQZRZS
      UDZUGYPYPHIJKLJHPZKIPZURZYTYIUUFYOUUAYJUUCYLUJUUIUUEYNSUUGUUHUUBYKUUDYMDU
      UAYJYHUKDUUCYLYHUKULUMUNJIPZKHPZURZYTYIUUFYOUULYTIHPYIUUAYLUUCYJUJIHUOUPU
      ULUUEYNSUULUUEYMYKRYNUUJUUKUUBYMUUDYKDUUAYLYHUKDUUCYJYHUKULYMYKUQUSUMUNLU
      TVAUHVBVCUHYSURYPVDYQYRYJYLVEVFZVGZYPUHUUNYIYOYIVHZYLYJVIZUUNYOUUPYJYLVIU
      UOYLYJVJYJYLVKVLUUNUUPYJYLVNVFZYOYQYJUTTYRYLUTTUUMUUMUUQUUPVMYJVOYLVOUUMV
      PYJYLVQVRYQYRUUQYOVSUUMYQYRUUQYOYQYRUUQVGZYNCMYLOUFZBUAZDYLAQZUUTUBZRZVAU
      VCSUDYOUURYNDYJAQZCMYJOUFZBUAZUBZUVBRZUVCYKUVGYMUVBDYJYHUVGHVTDUVDUVFDYJA
      WACDUVEBDUVEWBFWCWDDHPZAUVDYGUVFDYJAWEUVICYFUVEBYEYJMOWGWFWHWIDYLYHUVBIVT
      DUVAUUTDYLAWACDUUSBDUUSWBFWCWDDIPZAUVAYGUUTDYLAWEUVJCYFUUSBYEYLMOWGWFWHWI
      WJUURUVGUUTVAUVHUVCVAUURUVDUUTUVFUURYJUUSTZUVDUUTVAUURYJMWKWSZTYLWLTUUQUV
      KUURYJLUVLYQYRUUQWMWNWOUURYLYQYRUUQWPWQYQYRUUQWRYJMYLWTXACUUSBYJUVDCUUSWB
      CYJWBZCDYJAUVMEXBCHPUVDBUVDBUDHCDHCNZABDUVNWBFGXCXDXEXFXSXGUVGUUTUVBXHXSX
      IUUTUVAXJYNUVCXKXLXMXNXOXPXQXRXTYAYBDLYHHIYCYD $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d x y z C $.  $d x z D $.  $d x y F $.
    $d x y z ph $.
    disjrdx.1 $e |- ( ph -> F : A -1-1-onto-> C ) $.
    disjrdx.2 $e |- ( ( ph /\ y = ( F ` x ) ) -> D = B ) $.
    $( Re-index a disjunct collection statement.  (Contributed by Thierry
       Arnoux, 7-Apr-2017.) $)
    disjrdx $p |- ( ph -> ( Disj_ x e. A B <-> Disj_ y e. C D ) ) $=
      ( vz cv wcel wrmo wal wdisj wa wceq wreu df-disj cfv wf1o wf f1of f1ofveu
      ffvelrnda sylan eqcom reubii sylib eleq2d rmoxfrd bicomd albidv 3bitr4g
      syl ) AKLZEMZBDNZKOUQGMZCFNZKOBDEPCFGPAUSVAKAVAUSAUTURCBBLZHUAZFDADFVBHAD
      FHUBZDFHUCIDFHUDUPUFACLZFMZQVCVERZBDSZVEVCRZBDSAVDVFVHIBDFVEHUEUGVGVIBDVC
      VEUHUIUJAVIQGEUQJUKULUMUNBKDETCKFGTUO $.
  $}

  ${
    $d z A $.  $d z B $.
    $( Two ways to say that two classes are disjoint (or equal).  (Contributed
       by Thierry Arnoux, 4-Oct-2016.) $)
    disjex $p |- ( ( E. z ( z e. A /\ z e. B ) -> A = B ) <->
      ( A = B \/ ( A i^i B ) = (/) ) ) $=
      ( wceq cv wcel wa wex wn wo cin c0 orcom wne cab df-in neeq1i abn0 bitr2i
      wi necon2bbii orbi2i imor 3bitr4ri ) BCDZAEZBFUFCFGZAHZIZJUIUEJUEBCKZLDZJ
      UHUETUEUIMUKUIUEUHUJLUJLNUGAOZLNUHUJULLABCPQUGARSUAUBUHUEUCUD $.

    disjexc.1 $e |- ( x = y -> A = B ) $.
    $( A variant of ~ disjex , applicable for more generic families.
       (Contributed by Thierry Arnoux, 4-Oct-2016.) $)
    disjexc $p |- ( ( E. z ( z e. A /\ z e. B ) -> x = y ) ->
      ( A = B \/ ( A i^i B ) = (/) ) ) $=
      ( cv wcel wa wex wceq wi cin c0 wo imim2i wn orcom wne cab neeq1i 3bitr4i
      df-in abn0 bitr2i necon2bbii orbi2i imor sylibr ) CGZDHUJEHIZCJZAGBGKZLUL
      DEKZLZUNDEMZNKZOZUMUNULFPUNULQZOUSUNOURUOUNUSRUQUSUNULUPNUPNSUKCTZNSULUPU
      TNCDEUCUAUKCUDUEUFUGULUNUHUBUI $.
  $}
  
  ${
    $d i j x A $.  $d i j B $.  $d i j x C $.  $d i j x M $.  $d i j x V $. 
    disjunsn.s $e |- ( x = M -> B = C ) $.
    $( Append an element to a disjoint collection. Similar to ~ ralunsn , 
       ~ gsumunsn , etc. (Contributed by Thierry Arnoux, 28-Mar-2018.) $)
    disjunsn $p |- ( ( M e. V /\ -. M e. A ) -> ( Disj_ x e. ( A u. { M } ) B
      <-> ( Disj_ x e. A B /\ ( U_ x e. A B i^i C ) = (/) ) ) ) $=
      ( vi vj wa wceq cin c0 wo wral wb ineq1d eqeq1d ralbidv syl6bb wn csn cun
      wcel wdisj cv csb ciun disjors eqeq1 csbeq1 orbi12d ralunsn syl5bb ineq2d
      eqeq2 eqid orci biantru syl6bbr anbi12d bitrd r19.26 anbi1i bitr4i adantr
      orcom ralbii wrex r19.30 risset notbii biorf sylbi adantl syl5ibr syl5bir
      imp olc ralimi impbida nfv nfcv nfcsb1 nfin nfeq csbeq1a cbvral a1i iunss
      wss ss0b iunin1 eqeq1i 3bitr3ri bitri nfcvd csbiegf 3bitr4d bitr4d anbi2d
      eqcom rexbii incom anass anidm anbi2i ) EFUDZEBUDZUAZJZABEUBUCZCUEZABCUEZ
      HUFZEKZAXOCUGZAECUGZLZMKZNZHBOZJZEIUFZKZXRAYDCUGZLZMKZNZIBOZJZXNABCUHDLZM
      KZJZXHXMYKPXJXHXMXOYDKZXQYFLZMKZNZIBOZYAJZHBOZYJJZYKXHXMYRIXLOZHBOZYIIXLO
      ZJZUUBXMUUCHXLOXHUUFAXLCHIUIUUCUUEHBEFXPYRYIIXLXPYOYEYQYHXOEYDUJXPYPYGMXP
      XQXRYFAXOECUKQRULSUMUNXHUUDUUAUUEYJXHUUCYTHBYRYAIBEFYDEKZYOXPYQXTYDEXOUPU
      UGYPXSMUUGYFXRXQAYDECUKZUORULUMSXHUUEYJEEKZXRXRLZMKZNZJYJYIUULIBEFUUGYEUU
      IYHUUKYDEEUPUUGYGUUJMUUGYFXRXRUUHUORULUMUULYJUUIUUKEUQURUSUTVAVBUUAYCYJUU
      AYSHBOZYBJYCYSYAHBVCXNUUMYBABCHIUIVDVEVDTVFXKYKYNYMJZYNXKYCYNYJYMXKYBYMXN
      XKYBXTHBOZYMXKYBUUOXKYBUUOYBXTXPNZHBOZXKUUOUUPYAHBXTXPVGVHUUQUUOXKUUOXPHB
      VIZNZXTXPHBVJXKUUOUURUUONZUUSXJUUOUUTPZXHXJUURUAUVAXIUURHEBVKVLUURUUOVMVN
      VOUURUUOVGTVPVQVRUUOYBXKXTYAHBXTXPVSVTVOWAXHYMUUOPXJXHCDLZMKZABOZXQDLZMKZ
      HBOZYMUUOUVDUVGPXHUVCUVFAHBUVCHWBAUVEMAXQDAXOCAXOWCWDADWCZWEAMWCZWFAUFZXO
      KZUVBUVEMUVKCXQDAXOCWGQRWHWIYMUVDPXHYMUVBMWKZABOZUVDABUVBUHZMWKUVNMKUVMYM
      UVNWLABUVBMWJUVNYLMABDCWMWNWOUVLUVCABUVBWLVHWPWIZXHXTUVFHBXHXSUVEMXHXRDXQ
      AECDFXHADWQGWRZUORSWSVFWTXAXKYJYHIBOZYMXKYJUVQXKYJUVQYJYHYENZIBOZXKUVQUVR
      YIIBYHYEVGVHUVSUVQXKUVQYEIBVIZNZYHYEIBVJXKUVQUVTUVQNZUWAXJUVQUWBPZXHXJUVT
      UAUWCXIUVTXIUUGIBVIUVTIEBVKUUGYEIBYDEXBXCWPVLUVTUVQVMVNVOUVTUVQVGTVPVQVRU
      VQYJXKYHYIIBYHYEVSVTVOWAXHYMUVQPXJXHUVDDYFLZMKZIBOZYMUVQXHUVDYFDLZMKZIBOZ
      UWFUVDUWIPXHUVCUWHAIBUVCIWBAUWGMAYFDAYDCAYDWCWDUVHWEUVIWFUVJYDKZUVBUWGMUW
      JCYFDAYDCWGQRWHWIUWHUWEIBUWGUWDMYFDXDWNVHTUVOXHYHUWEIBXHYGUWDMXHXRDYFUVPQ
      RSWSVFWTVAUUNXNYMYMJZJYNXNYMYMXEUWKYMXNYMXFXGWPTVB $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
     Relations and Functions
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
      Relations - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d a b x y $.  $d a b R $.
    dfrel4.1 $e |- F/_ x R $.
    dfrel4.2 $e |- F/_ y R $.
    $( A relation can be expressed as the set of ordered pairs in it.  An
       analogue of ~ dffn5 for relations.  (Contributed by Mario Carneiro,
       16-Aug-2015.)  (Revised by Thierry Arnoux, 11-May-2017.) $)
    dfrel4 $p |- ( Rel R <-> R = { <. x , y >. | x R y } ) $=
      ( va vb wrel cv wbr copab wceq dfrel4v nfcv nfbr nfv breq12 cbvopab bitri
      eqeq2i ) CHCFIZGIZCJZFGKZLCAIZBIZCJZABKZLFGCMUDUHCUCUGFGABAUAUBCAUANDAUBN
      OBUAUBCBUANEBUBNOUGFPUGGPUAUEUBUFCQRTS $.
  $}

  $( The range of a pair of ordered pairs is the pair of second members.
     (Contributed by Thierry Arnoux, 3-Jan-2017.) $)
  rnpropg $p |- ( ( A e. V /\ B e. W )
    -> ran { <. A , C >. , <. B , D >. } = { C , D } ) $=
    ( wcel cop cpr crn csn cun df-pr rneqi wceq rnsnopg adantr adantl uneq12d
    wa rnun 3eqtr4g syl5eq ) AEGZBFGZTZACHZBDHZIZJUGKZUHKZLZJZCDIZUIULUGUHMNUFU
    JJZUKJZLCKZDKZLUMUNUFUOUQUPURUDUOUQOUEACEPQUEUPUROUDBDFPRSUJUKUACDMUBUC $.

  $( Restriction of a constant function (or other cross product) outside of its
     domain (Contributed by Thierry Arnoux, 25-Jan-2017.) $)
  xpdisjres $p |- ( ( A i^i C ) = (/) -> ( ( A X. B ) |` C ) = (/) ) $=
    ( cin c0 wceq cxp cres cvv df-res xpdisj1 syl5eq ) ACDEFABGZCHMCIGDEMCJACBI
    KL $.

  $( Image of the difference with a cross product (Contributed by Thierry
     Arnoux, 13-Dec-2017.) $)
  imadifxp $p |- ( C C_ A ->
    ( ( R \ ( A X. B ) ) " C ) = ( ( R " C ) \ B ) ) $=
    ( wss cxp cdif cima wceq c0 imaeq2 syl6eq adantl wne cun cin syl5eq cvv crn
    ima0 difeq1d 0dif 3eqtr4a wa inundif imaeq1i imaundir eqtr3i difundir eqtri
    difeq1i inss2 imass1 ssdif mp2b xpima wn incom df-ss biimpi syl5eqr eqnetrd
    cif simpl df-ne iffalse 3syl difid syl5sseq cres df-ima df-res rneqi ineq1i
    ss0 syl xpss1 sslin rnss ssn0 ancoms inss1 ax-mp indif2 difxp2 3sstr4i mp1i
    sseqtrd disj2 sylibr ssdisj syl2anc disj3 sylib eqcomd uneq12d uncom eqtr2i
    rnxp un0 syl6reqr pm2.61dane ) CAEZDABFZGZCHZDCHZBGZIZCJCJIZXIXCXJXEJHJXFXH
    XETCJXEKXJXHJBGJXJXGJBXJXGDJHJCJDKDTLUABUBLUCMCJNZXCXIXKXCUDZXHJXFOZXFXLXHD
    XDPZCHZBGZXFBGZOZXMXHXOXFOZBGXRXGXSBXNXEOZCHXGXSXTDCDXDUEUFXNXECUGUHUKXOXFB
    UIUJXLXPJXQXFXLXPJEXPJIXLXDCHZBGZXPJXNXDEXOYAEXPYBEDXDULXNXDCUMXOYABUNUOXLY
    BBBGJXLYABBXLYAACPZJIZJBVCZBABCUPXLYCJNZYDUQZYEBIXLYCCJXCYCCIXKXCYCCAPZCCAU
    RXCYHCICAUSUTVAMXKXCVDVBYFYGYCJVEUTYDJBVFVGQUABVHLVIXPVOVPXLXFXQXLXFBPZJIXF
    XQIXLYIXECRFZPZSZBPZJXFYLBXFXECVJZSYLXECVKYNYKXECVLVMUJVNXLYLXEARFZPZSZEZYQ
    BPJIZYMJIXCYRXKXCYJYOEYKYPEYRCARVQYJYOXEVRYKYPVSVGMXLAJNZYSXCXKYTCAVTWAYTYQ
    RBGZEYSYTYQAUUAFZSZUUAYPUUBEYQUUCEYTYODPZXDGZYOXDGZYPUUBUUDYOEUUEUUFEYODWBU
    UDYOXDUNWCYOXEPYPUUEYOXEURYODXDWDUHARBWEWFYPUUBVSWGAUUAWSWHYQBWIWJVPYLYQBWK
    WLQXFBWMWNWOWPQXMXFJOXFJXFWQXFWTWRXAWAXB $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
      Functions - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( A different way to write ` F ` is a function.  (Contributed by Thierry
     Arnoux, 7-Dec-2016.) $)
  fdmrn $p |- ( Fun F <-> F : dom F --> ran F ) $=
    ( cdm crn wf wfn wfun wss ssid df-f mpbiran2 wceq eqid df-fn bitr2i ) ABZAC
    ZADZAOEZAFZQRPPGPHOPAIJRSOOKOLAOMJN $.

  $( An involution is a bijection.  (Contributed by Thierry Arnoux,
     7-Dec-2016.) $)
  nvof1o $p |- ( ( F Fn A /\ `' F = F ) -> F : A -1-1-onto-> A ) $=
    ( wfn ccnv wceq wa wf1 wfo wf1o wfun cdm crn fnfun fdmrn sylib adantr df-rn
    wf fndm sylanbrc syl5eq sylan9eqr feq23d mpbid wb funeq adantl mpbird df-f1
    dmeq simpl df-fo df-f1o ) BACZBDZBEZFZAABGZAABHZAABIUQAABRZUOJZURUQBKZBLZBR
    ZUTUNVDUPUNBJZVDABMZBNOPUQVBVCAABUNVBAEUPABSZPUPUNVCVBAUPVCUOKVBBQUOBUJUAVG
    UBZUCUDUQVAVEUNVEUPVFPUPVAVEUEUNUOBUFUGUHAABUITUQUNVCAEUSUNUPUKVHAABULTAABU
    MT $.

  ${
    $d x y A $.  $d x y B $.  $d y C $.  $d x D $.  $d x y ph $.
    f1o3d.1 $e |- ( ph -> F = ( x e. A |-> C ) ) $.
    f1o3d.2 $e |- ( ( ph /\ x e. A ) -> C e. B ) $.
    f1o3d.3 $e |- ( ( ph /\ y e. B ) -> D e. A ) $.
    f1o3d.4 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) ->
                    ( x = D <-> y = C ) ) $.
    $( Describe an implicit one-to-one onto function.  (Contributed by Thierry
       Arnoux, 23-Apr-2017.) $)
    f1o3d $p |- ( ph -> ( F : A -1-1-onto-> B /\ `' F = ( y e. B |-> D ) ) ) $=
      ( ccnv wceq wfn wcel syl wa copab wi wf1o cmpt wral ralrimiva eqid fneq1d
      fnmpt mpbird cv eleq1a impr biimpar exp42 com34 imp32 jcai biimpa impbida
      com23 opabbidv df-mpt syl6eq cnveqd cnvopab a1i 3eqtr4d dff1o4 sylanbrc
      jca ) ADEHUAZHMZCEGUBZNAHDOZVKEOZVJAVMBDFUBZDOZAFEPZBDUCVPAVQBDJUDBDFVOEV
      OUEUGQADHVOIUFUHAVNVLEOZAGDPZCEUCVRAVSCEKUDCEGVLDVLUEUGQAEVKVLABUIZDPZCUI
      ZFNZRZCBSZWBEPZVTGNZRZCBSZVKVLAWDWHCBAWDWHAWDRWFWGAWAWCWFAWARVQWCWFTJFEWB
      UJQUKAWAWCWFWGTAWAWFWCWGAWAWFWCWGAWAWFRRZWGWCLULUMUNUOUPAWHRWAWCAWFWGWAAW
      FRVSWGWATKGDVTUJQUKAWFWGWAWCTAWFWAWGWCAWAWFWGWCTAWAWFWGWCWJWGWCLUQUMUSUNU
      OUPURUTAVKWDBCSZMWEAHWKAHVOWKIBCDFVAVBVCWDBCVDVBVLWINACBEGVAVEVFZUFUHDEHV
      GVHWLVI $.
  $}

  ${
    rinvbij.1 $e |- Fun F $.
    rinvbij.2 $e |- `' F = F $.
    rinvbij.3a $e |- ( F " A ) C_ B $.
    rinvbij.3b $e |- ( F " B ) C_ A $.
    rinvbij.4a $e |- A C_ dom F $.
    rinvbij.4b $e |- B C_ dom F $.
    $( Sufficient conditions for the restriction of an involution to be a
       bijection (Contributed by Thierry Arnoux, 7-Dec-2016.) $)
    rinvf1o $p |- ( F |` A ) : A -1-1-onto-> B $=
      ( cima cres wf1o cdm crn wf1 wss wfun mpbi mp2an wb wf fdmrn funeqi mpbir
      ccnv df-f1 mpbir2an f1ores funimass3 imaeq1i sseqtri eqssi f1oeq3 ax-mp
      wceq ) ACAJZCAKZLZABUQLZCMZCNZCOZAUTPURVBUTVACUAZCUEZQZCQZVCDCUBRVEVFDVDC
      EUCUDUTVACUFUGHUTVAACUHSUPBUOURUSTUPBFBVDAJZUPCBJAPZBVGPZGVFBUTPVHVITDIBA
      CUISRVDCAEUJUKULUPBAUQUMUNR $.
  $}

  ${
    $d x y z $.  $d y z A $.  $d y z F $.
    dfimafnf.1 $e |- F/_ x A $.
    dfimafnf.2 $e |- F/_ x F $.
    $( Alternate definition of the image of a function.  (Contributed by Raph
       Levien, 20-Nov-2006.)  (Revised by Thierry Arnoux, 24-Apr-2017.) $)
    dfimafnf $p |- ( ( Fun F /\ A C_ dom F ) ->
                  ( F " A ) = { y | E. x e. A y = ( F ` x ) } ) $=
      ( vz wfun cdm wss wa cima cv cfv wceq wrex cab wbr wcel nfcv ssel syl5bbr
      wb eqcom funbrfvb ex syl9r imp31 rexbidva abbidv dfima2 syl6reqr nffv nfv
      nfeq2 fveq2 eqeq2d cbvrexf abbii syl6eq ) DHZCDIZJZKZDCLZBMZGMZDNZOZGCPZB
      QZVFAMZDNZOZACPZBQVDVKVGVFDRZGCPZBQVEVDVJVQBVDVIVPGCVAVCVGCSZVIVPUCZVCVRV
      GVBSZVAVSCVBVGUAVAVTVSVIVHVFOVAVTKVPVHVFUDVGVFDUEUBUFUGUHUIUJGBDCUKULVJVO
      BVIVNGACGCTEAVFVHAVGDFAVGTUMUOVNGUNVGVLOVHVMVFVGVLDUPUQURUSUT $.
  $}

  ${
    $d w x y $.  $d w y A $.  $d y B $.  $d z y F $.
    funimass4f.1 $e |- F/_ x A $.
    funimass4f.2 $e |- F/_ x B $.
    funimass4f.3 $e |- F/_ x F $.
    $( use ~ ffnfvf $)
    $( Membership relation for the values of a function whose image is a
       subclass.  (Contributed by Thierry Arnoux, 24-Apr-2017.) $)
    funimass4f $p |- ( ( Fun F /\ A C_ dom F ) ->
                    ( ( F " A ) C_ B <-> A. x e. A ( F ` x ) e. B ) ) $=
      ( vy wfun cdm wss wa cima cv cfv wcel wral nfss nfan wceq nffun funfvima2
      nfdm nfima ssel sylan9 ralrimi cab dfimafnf adantr abrexss adantl eqsstrd
      wrex impbida ) DIZBDJZKZLZDBMZCKZANZDOZCPZABQZUSVALVDABUSVAAUPURAADGUAABU
      QEADGUCRSAUTCADBGEUDFRSUSVBBPVCUTPVAVDBVBDUBUTCVCUEUFUGUSVELUTHNVCTABUNHU
      HZCUSUTVFTVEAHBDEGUIUJVEVFCKUSAHBVCCFUKULUMUO $.
  $}

  ${
    $d x y ph $.  $d x C $.  $d x D $.  $d y A $.  $d y B $.
    mptcnv.1 $e |- ( ph -> ( ( x e. A /\ y = B ) <-> ( y e. C /\ x = D ) ) ) $.
    $( The converse of a mapping function.  (Contributed by Thierry Arnoux,
       16-Jan-2017.) $)
    mptcnv $p |- ( ph -> `' ( x e. A |-> B ) = ( y e. C |-> D ) ) $=
      ( cv wcel wceq wa copab ccnv cmpt cnvopab opabbidv syl5eq df-mpt cnveqi
      3eqtr4g ) ABIZDJCIZEKLZBCMZNZUCFJUBGKLZCBMZBDEOZNCFGOAUFUDCBMUHUDBCPAUDUG
      CBHQRUIUEBCDESTCBFGSUA $.
  $}

  $( Equality theorem for function predicate with domain.  (Contributed by
     Thierry Arnoux, 31-Jan-2017.) $)
  fneq12 $p |- ( ( F = G /\ A = B ) -> ( F Fn A <-> G Fn B ) ) $=
    ( wceq wa simpl simpr fneq12d ) CDEZABEZFABCDJKGJKHI $.

  $( Taking the converse image of a set can be limited to the range of the
     function used.  (Contributed by Thierry Arnoux, 21-Jan-2017.) $)
  fimacnvinrn $p |- ( Fun F -> ( `' F " A ) = ( `' F " ( A i^i ran F ) ) ) $=
    ( wfun ccnv crn cin cima cdm inpreima wf wceq wfo funforn fof sylbi fimacnv
    syl ineq2d cres cnvresima resdm2 funrel dfrel2 sylib syl5eq imaeq1d syl5eqr
    wrel cnveqd 3eqtrrd ) BCZBDZABEZFGULAGZULUMGZFUNBHZFZUNAUMBIUKUOUPUNUKUPUMB
    JZUOUPKUKUPUMBLURBMUPUMBNOUPUMBPQRUKUQBUPSZDZAGUNUPABTUKUTULAUKUSBUKUSULDZB
    BUAUKBUHVABKBUBBUCUDUEUIUFUGUJ $.

  $( Taking the converse image of a set can be limited to the range of the
     function used.  (Contributed by Thierry Arnoux, 17-Feb-2017.) $)
  fimacnvinrn2 $p |- ( ( Fun F /\ ran F C_ B ) ->
                                    ( `' F " A ) = ( `' F " ( A i^i B ) ) ) $=
    ( wfun crn wss ccnv cin cima inass wceq biimpi adantl ineq2d syl5eq imaeq2d
    wa dfss1 fimacnvinrn adantr 3eqtr4rd ) CDZCEZBFZQZCGZABHZUCHZIZUFAUCHZIZUFU
    GIZUFAIZUEUHUJUFUEUHABUCHZHUJABUCJUEUNUCAUDUNUCKZUBUDUOUCBRLMNOPUBULUIKUDUG
    CSTUBUMUKKUDACSTUA $.

  ${
    $d l A $.  $d l B $.  $d l W $.  $d k l Z $.  $d l ph $.
    suppss2f.p $e |- F/ k ph $.
    suppss2f.a $e |- F/_ k A $.
    suppss2f.w $e |- F/_ k W $.
    suppss2f.n $e |- ( ( ph /\ k e. ( A \ W ) ) -> B = Z ) $.
    $( Show that the support of a function is contained in a set.  (Contributed
       by Thierry Arnoux, 22-Jun-2017.) $)
    suppss2f $p |- ( ph -> ( `' ( k e. A |-> B ) " ( _V \ { Z } ) ) C_ W ) $=
      ( vl cvv cdif wcel crab wceq wa wi wsb bitri cmpt ccnv csn cima mptpreima
      eqid cv csb nfv nfcsb1v nfel1 csbeq1a eleq1d cbvrab wne eldifsni wn eldif
      nfcv sbt sbim sban sbf nfdif clelsb3f anbi12i wsbc sbsbc wb sbceq1g ax-mp
      vex imbi12i mpbi sylan2br expr necon1ad ss2rabdv cin dfin5 inss2 eqsstr3i
      syl5 syl6ss syl5eqss ) ADBCUAZUBLFUCMZUDCWGNZDBOZEDBCWGWFWFUFUEAWIDKUGZCU
      HZWGNZKBOZEWHWLDKBHKBUSWHKUIDWKWGDWJCUJUKDUGZWJPCWKWGDWJCULUMUNAWMWJENZKB
      OZEAWLWOKBWLWKFUOAWJBNZQZWOWKLFUPWRWOWKFAWQWOUQZWKFPZWQWSQAWJBEMZNZWTWJBE
      URAWNXANZQZCFPZRZDKSZAXBQZWTRZXFDKJUTXGXDDKSZXEDKSZRXIXDXEDKVAXJXHXKWTXJA
      DKSZXCDKSZQXHAXCDKVBXLAXMXBADKGVCKDXADBEHIVDVEVFTXKXEDWJVGZWTXEDKVHWJLNXN
      WTVIKVLDWJCFLVJVKTVMTVNVOVPVQWCVRWPBEVSEKBEVTBEWAWBWDWEWE $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.  $d x y F $.  $d x y R $.  $d x y S $.
    fovcld.1 $e |- ( ph -> F : ( R X. S ) --> C ) $.
    $( Closure law for an operation.  (Contributed by NM, 19-Apr-2007.)
       (Revised by Thierry Arnoux, 17-Feb-2017.) $)
    fovcld $p |- ( ( ph /\ A e. R /\ B e. S ) -> ( A F B ) e. C ) $=
      ( vx vy wcel w3a wa cv co wral 3simpc cxp wceq eleq1d wf simprbi 3ad2ant1
      wfn ffnov syl oveq1 oveq2 rspc2v sylc ) ABEKZCFKZLUKULMINZJNZGOZDKZJFPIEP
      ZBCGOZDKZAUKULQAUKUQULAEFRZDGUAZUQHVAGUTUDUQIJEFDGUEUBUFUCUPUSBUNGOZDKIJB
      CEFUMBSUOVBDUMBUNGUGTUNCSVBURDUNCBGUHTUIUJ $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x F $.
    elovimad.1 $e |- ( ph -> A e. C ) $.
    elovimad.2 $e |- ( ph -> B e. D ) $.
    elovimad.3 $e |- Fun F $.
    elovimad.4 $e |- ( ph -> ( C X. D ) C_ dom F ) $.
    $( Elementhood of the image set of an operation value (Contributed by
       Thierry Arnoux, 13-Mar-2017.) $)
    elovimad $p |- ( ph -> ( A F B ) e. ( F " ( C X. D ) ) ) $=
      ( co cop cfv cxp cima df-ov wcel opelxpi syl2anc wfun cdm sseldd funfvima
      wi sylancr mpd syl5eqel ) ABCFKBCLZFMZFDENZOZBCFPAUHUJQZUIUKQZABDQCEQULGH
      BCDERSZAFTUHFUAZQULUMUDIAUJUOUHJUNUBUJUHFUCUEUFUG $.
  $}

  ${
    $d x y B $.  $d x y C $.  $d x y F $.  $d y G $.  $d x y .+ $.
    $d x y ph $.
    ofrn.1 $e |- ( ph -> F : A --> B ) $.
    ofrn.2 $e |- ( ph -> G : A --> B ) $.
    ofrn.3 $e |- ( ph -> .+ : ( B X. B ) --> C ) $.
    ofrn.4 $e |- ( ph -> A e. V ) $.
    $( The range of the function operation.  (Contributed by Thierry Arnoux,
       8-Jan-2017.) $)
    ofrn $p |- ( ph -> ran ( F oF .+ G ) C_ C ) $=
      ( vx vy co wf cv wcel wral syl cof crn wss cxp wfn ffnov simprbi r19.21bi
      wa anasss inidm off frn ) ABDFGEUAOZPUNUBDUCAMNBBBECCDFGHHAMQZCRZNQZCRUOU
      QEODRZAUPUIURNCAURNCSZMCACCUDZDEPZUSMCSZKVAEUTUEVBMNCCDEUFUGTUHUHUJIJLLBU
      KULBDUNUMT $.

    $d a z A $.  $d z B $.  $d a z F $.  $d a x z G $.  $d a z .+ $.
    $d a z ph $.  $d x y z a $.
    $( The range of the function operation.  (Contributed by Thierry Arnoux,
       21-Mar-2017.) $)
    ofrn2 $p |- ( ph -> ran ( F oF .+ G ) C_ ( .+ " ( ran F X. ran G ) ) ) $=
      ( vz va vx vy cv crn wcel syl cfv co wceq wrex cab cof cxp cima wa wfn wf
      ffn adantr simprl fnfvelrn syl2anc simprr rspceov syl3anc rexlimdvaa cmpt
      ss2abdv inidm eqidd offval rneqd eqid rnmpt syl6eq wss wb xpss12 ovelimab
      frn abbi2dv 3sstr4d ) AMQZNQZFUAZVRGUAZEUBZUCZNBUDZMUEZVQOQPQEUBUCPGRZUDO
      FRZUDZMUEFGEUFUBZRZEWFWEUGZUHZAWCWGMAWBWGNBAVRBSZWBUIZUIZVSWFSZVTWESZWBWG
      WNFBUJZWLWOAWQWMABCFUKZWQIBCFULTZUMAWLWBUNZBVRFUOUPWNGBUJZWLWPAXAWMABCGUK
      ZXAJBCGULTZUMWTBVRGUOUPAWLWBUQOPWFWEVSVTVQEURUSUTVBAWINBWAVAZRWDAWHXDANBB
      VSVTEBFGHHWSXCLLBVCAWLUIZVSVDXEVTVDVEVFNMBWAXDXDVGVHVIAWGMWKAECCUGZUJZWJX
      FVJZVQWKSWGVKAXFDEUKXGKXFDEULTAWFCVJZWECVJZXHAWRXIIBCFVNTAXBXJJBCGVNTWFCW
      ECVLUPOPXFWFWEVQEVMUPVOVP $.
  $}

  ${
    $d z A $.  $d z B $.  $d z C $.  $d y z G $.  $d x y z ph $.  $d x y S $.
    $d x y T $.  $d x y z F $.  $d x y z R $.  $d x y z U $.
    off2.1 $e |- ( ( ph /\ ( x e. S /\ y e. T ) ) -> ( x R y ) e. U ) $.
    off2.2 $e |- ( ph -> F : A --> S ) $.
    off2.3 $e |- ( ph -> G : B --> T ) $.
    off2.4 $e |- ( ph -> A e. V ) $.
    off2.5 $e |- ( ph -> B e. W ) $.
    off2.6 $e |- ( ph -> ( A i^i B ) = C ) $.
    $( The function operation produces a function - alternative form with all
       antecedents as deduction.  (Contributed by Thierry Arnoux,
       17-Feb-2017.) $)
    off2 $p |- ( ph -> ( F oF R G ) : C --> U ) $=
      ( vz cof co wf cv cfv cmpt wcel wa wral adantr cin inss1 syl6eqssr sselda
      ffvelrnd inss2 ralrimivva proplem2 syl21anc eqid fmptd wfn ffn syl offval
      eqidd mpteq1d eqtrd feq1d mpbird ) AFJKLGUBUCZUDFJUAFUAUEZKUFZVMLUFZGUCZU
      GZUDAUAFVPJVQAVMFUHZUIZVNHUHVOIUHBUECUEGUCJUHZCIUJBHUJZVPJUHVSDHVMKADHKUD
      ZVRPUKAFDVMAFDEULZDTDEUMUNUOUPVSEIVMLAEILUDZVRQUKAFEVMAFWCETDEUQUNUOUPAWA
      VRAVTBCHIOURUKBCHIJGVNVOUSUTVQVAVBAFJVLVQAVLUAWCVPUGVQAUADEVNVOGWCKLMNAWB
      KDVCPDHKVDVEAWDLEVCQEILVDVERSWCVAAVMDUHUIVNVGAVMEUHUIVOVGVFAUAWCFVPTVHVIV
      JVK $.
  $}

  ${
    $d x A $.  $d x B $.  $d x F $.  $d x G $.  $d x R $.  $d x ph $.
    ofresid.1 $e |- ( ph -> F : A --> B ) $.
    ofresid.2 $e |- ( ph -> G : A --> B ) $.
    ofresid.3 $e |- ( ph -> A e. V ) $.
    $( Applying an operation restricted to the range of the functions does not
       change the function operation.  (Contributed by Thierry Arnoux,
       14-Feb-2018.) $)
    ofresid $p |- ( ph -> ( F oF R G ) = ( F oF ( R |` ( B X. B ) ) G ) ) $=
      ( vx cfv co cmpt cof wcel wa ffvelrnda syl df-ov cv cxp cres cop wceq jca
      opelxp sylibr fvres eqcomd 3eqtr4g mpteq2dva wfn ffn inidm offval 3eqtr4d
      wf eqidd ) AKBKUAZELZUTFLZDMZNKBVAVBDCCUBZUCZMZNEFDOMEFVEOMAKBVCVFAUTBPQZ
      VAVBUDZDLZVHVELZVCVFVGVJVIVGVHVDPZVJVIUEVGVACPZVBCPZQVKVGVLVMABCUTEHRABCU
      TFIRUFVAVBCCUGUHVHVDDUISUJVAVBDTVAVBVETUKULAKBBVAVBDBEFGGABCEUREBUMHBCEUN
      SZABCFURFBUMIBCFUNSZJJBUOZVGVAUSZVGVBUSZUPAKBBVAVBVEBEFGGVNVOJJVPVQVRUPUQ
      $.
  $}

  $(
    $d x y ph $. $d x C $. $d x D $. $d y A $. $d y B $.
    mptcnv.1 $e |- ( ph -> ( ( x e. A /\ y = B ) <-> ( y e. C /\ x = D ) ) ) $.
    #( The converse of a mapping function.
       (Contributed by Thierry Arnoux, 16-Jan-2017.) #)
    mptcnv   $p |- ( ph -> `' ( x e. A |-> B ) = ( y e. C |-> D ) ) $=
      ( cv wcel wceq wa copab ccnv cmpt cnvopab opabbidv eqtrd df-mpt
      a1i cnveqi 3eqtr4d ) ABIZDJCIZEKLZBCMZNZUDFJUCGKLZCBMZBDEOZNZCF
      GOZAUGUECBMZUIUGUMKAUEBCPTAUEUHCBHQRUKUGKAUJUFBCDESUATULUIKACBF
      GSTUB $.
      #( [16-Jan-2017] #)
  $)

  ${
    $d x y F $.  $d x y A $.  $d x B $.
    $( Preimage of a class union.  (Contributed by Thierry Arnoux,
       7-Feb-2017.) $)
    unipreima $p |- ( Fun F -> ( `' F " U. A ) = U_ x e. A ( `' F " x ) ) $=
      ( vy wfun cdm wfn ccnv cuni cima cv ciun wceq wcel wa wrex wb a1i 3bitr4d
      elpreima funfn cfv r19.42v bicomi eluni2 anbi2i rexbidv eliun eqrdv sylbi
      ) CECCFZGZCHZBIZJZABUMAKZJZLZMCUAULDUOURULDKZUKNZUSCUBZUNNZOZUSUQNZABPZUS
      UONUSURNZULUTVAUPNZABPZOZUTVGOZABPZVCVEVIVKQULVKVIUTVGABUCUDRVCVIQULVBVHU
      TAVABUEUFRULVDVJABUKUSUPCTUGSUKUSUNCTVFVEQULAUSBUQUHRSUIUJ $.
  $}

  ${
    $( The preimage of a subset is a subset of the preimage.  (Contributed by
       Brendan Leahy, 23-Sep-2017.) $)
    sspreima $p |- ( ( Fun F /\ A C_ B ) -> ( `' F " A ) C_ ( `' F " B ) ) $=
      ( wfun wss wa ccnv cima cin wceq inpreima biimpi imaeq2d sylan9req sylibr
      df-ss ) CDZABEZFCGZAHZSBHZIZTJTUAEQRUBSABIZHTABCKRUCASRUCAJABPLMNTUAPO $.
  $}

  $( Value of a function producing ordered pairs.  (Contributed by Thierry
     Arnoux, 3-Jan-2017.) $)
  opfv $p |- ( ( ( Fun F /\ ran F C_ ( _V X. _V ) ) /\ x e. dom F ) ->
             ( F ` x ) = <. ( ( 1st o. F ) ` x ) , ( ( 2nd o. F ) ` x ) >. ) $=
    ( wfun crn cvv cxp wss wa cv cdm wcel cfv c1st c2nd cop ccom simplr adantlr
    wceq fvco fvelrn sseldd 1st2ndb sylib opeq12d eqtr4d ) BCZBDZEEFZGZHAIZBJKZ
    HZUKBLZUNMLZUNNLZOZUKMBPLZUKNBPLZOZUMUNUIKUNUQSUMUHUIUNUGUJULQUGULUNUHKUJUK
    BUARUBUNUCUDUGULUTUQSUJUGULHURUOUSUPUKMBTUKNBTUERUF $.

  ${
    $d x F $.  $d x Y $.  $d x Z $.
    $( The preimage of a cross product is the intersection of the preimages of
       each component function.  (Contributed by Thierry Arnoux,
       6-Jun-2017.) $)
    xppreima $p |- ( ( Fun F /\ ran F C_ ( _V X. _V ) ) ->
      ( `' F " ( Y X. Z ) ) =
                   ( ( `' ( 1st o. F ) " Y ) i^i ( `' ( 2nd o. F ) " Z ) ) ) $=
      ( vx wfun cvv wss wa ccnv cima c1st wcel c2nd cdm crab cin wceq adantr wb
      cfv crn cxp ccom wfn funfn fncnvima2 sylbi cop fvco opeq12d eqeq2d eleq1d
      anbi12d elxp6 syl6rbbr adantlr opfv biantrurd wfo fo1st fofun ax-mp funco
      cv mpan ssv wf fof fdm mp2b sseqtr4i ssid funimass3 mpan2 mpbii syl6eleqr
      dmco fvimacnv syl2anc fo2nd 3bitr2d rabbidva eqtrd dfin5 ineq12i cnvimass
      sselda dmcoss sstri dfss1 mpbi inrab 3eqtr3ri syl6eq ) AEZAUAFFUBGZHZAIZB
      CUBZJZDVDZKAUCZIBJZLZXAMAUCZICJZLZHZDANZOZXCXFPZWQWTXAATZWSLZDXIOZXJWOWTX
      NQZWPWOAXIUDXOAUEDXIWSAUFUGRWQXMXHDXIWQXAXILZHZXMXLXAXBTZXAXETZUHZQZXRBLZ
      XSCLZHZHZYDXHWOXPXMYESWPWOXPHZYEXLXLKTZXLMTZUHZQZYGBLZYHCLZHZHXMYFYAYJYDY
      MYFXTYIXLYFXRYGXSYHXAKAUIZXAMAUIZUJUKYFYBYKYCYLYFXRYGBYNULYFXSYHCYOULUMUM
      XLBCUNUOUPXQYAYDDAUQURWOXPYDXHSWPYFYBXDYCXGYFXBEZXAXBNZLYBXDSWOYPXPKEZWOY
      PFFKUSZYRUTFFKVAVBKAVCVERYFXAWRKNZJZYQWOXIUUAXAWOAXIJZYTGZXIUUAGZUUBFYTUU
      BVFZYSFFKVGYTFQUTFFKVHFFKVIVJVKWOXIXIGZUUCUUDSXIVLZXIYTAVMVNVOWGKAVQVPXAB
      XBVRVSYFXEEZXAXENZLYCXGSWOUUHXPMEZWOUUHFFMUSZUUJVTFFMVAVBMAVCVERYFXAWRMNZ
      JZUUIWOXIUUMXAWOUUBUULGZXIUUMGZUUBFUULUUEUUKFFMVGUULFQVTFFMVHFFMVIVJVKWOU
      UFUUNUUOSUUGXIUULAVMVNVOWGMAVQVPXACXEVRVSUMUPWAWBWCXIXCPZXIXFPZPXDDXIOZXG
      DXIOZPXKXJUUPUURUUQUUSDXIXCWDDXIXFWDWEUUPXCUUQXFXCXIGUUPXCQXCYQXIXBBWFKAW
      HWIXCXIWJWKXFXIGUUQXFQXFUUIXIXECWFMAWHWIXFXIWJWKWEXDXGDXIWLWMWN $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x F $.  $d x G $.  $d x H $.
    $d x ph $.
    xppreima2.1 $e |- ( ph -> F : A --> B ) $.
    xppreima2.2 $e |- ( ph -> G : A --> C ) $.
    xppreima2.3 $e |- H = ( x e. A |-> <. ( F ` x ) , ( G ` x ) >. ) $.
    $( The preimage of a cross product is the intersection of the preimages of
       each component function.  (Contributed by Thierry Arnoux,
       7-Jun-2017.) $)
    xppreima2 $p |- ( ph -> ( `' H " ( Y X. Z ) ) =
                                         ( ( `' F " Y ) i^i ( `' G " Z ) ) ) $=
      ( ccnv cima c1st c2nd cvv wceq wfn cxp ccom cin crn wss cv cfv funmpt2 wf
      wfun cop wcel wa ffvelrnda opelxp sylanbrc fmptd frn xpss syl6ss xppreima
      syl sylancr wfo fo1st fofn ax-mp opex fnmpti ssv mp3an a1i ffn cdm adantr
      fnco simpr dmmpti syl6eleqr opfv syl21anc fvmpt2 syl2anc eqtr3d fvex opth
      sylib simpld eqfnfvd cnveqd imaeq1d fo2nd simprd ineq12d eqtrd ) AHNIJUAO
      ZPHUBZNZIOZQHUBZNZJOZUCZFNZIOZGNZJOZUCAHUJZHUDZRRUAZUEZWPXCSBCBUFZFUGZXLG
      UGZUKZHMUHZAXIDEUAZXJACXQHUIXIXQUEABCXOXQHAXLCULZUMZXMDULXNEULXOXQULZACDX
      LFKUNACEXLGLUNXMXNDEUOUPZMUQCXQHURVBDEUSUTZHIJVAVCAWSXEXBXGAWRXDIAWQFABCW
      QFWQCTZAPRTZHCTZXIRUEZYCRRPVDYDVERRPVFVGBCXOHXMXNVHZMVIZXIVJZRCPHVPVKVLAC
      DFUIFCTKCDFVMVBXSXLWQUGZXMSZXLWTUGZXNSZXSYJYLUKZXOSYKYMUMXSXLHUGZYNXOXSXH
      XKXLHVNZULYOYNSXHXSXPVLAXKXRYBVOXSXLCYPAXRVQZBCXOHYGMVRVSBHVTWAXSXRXTYOXO
      SYQYABCXOXQHMWBWCWDYJYLXMXNXLWQWEXLWTWEWFWGZWHWIWJWKAXAXFJAWTGABCWTGWTCTZ
      AQRTZYEYFYSRRQVDYTWLRRQVFVGYHYIRCQHVPVKVLACEGUIGCTLCEGVMVBXSYKYMYRWMWIWJW
      KWNWO $.
  $}

  ${
    $d x A $.  $d x B $.  $d x R $.  $d x S $.  $d x ph $.
    fmptapd.0a $e |- ( ph -> A e. _V ) $.
    fmptapd.0b $e |- ( ph -> B e. _V ) $.
    fmptapd.1 $e  |- ( ph -> ( R u. { A } ) = S ) $.
    fmptapd.2 $e  |- ( ( ph /\ x = A ) -> C = B ) $.
    $( Append an additional value to a function.  (Contributed by Thierry
       Arnoux, 3-Jan-2017.) $)
    fmptapd $p    |- ( ph ->
      ( ( x e. R |-> C ) u. { <. A , B >. } ) = ( x e. S |-> C ) ) $=
      ( cmpt cop csn cun cvv wcel wceq fmptsn syl2anc cv elsni sylan2 mpteq2dva
      eqtr4d uneq2d mptun a1i mpteq1d 3eqtr2d ) ABFELZCDMNZOUKBCNZELZOZBFUMOZEL
      ZBGELAULUNUKAULBUMDLZUNACPQDPQULURRHIBCDPPSTABUMEDBUAZUMQAUSCREDRUSCUBKUC
      UDUEUFUQUORABFUMEUGUHABUPGEJUIUJ $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x ph $.
    fmptpr.1 $e |- ( ph -> A e. V ) $.
    fmptpr.2 $e |- ( ph -> B e. W ) $.
    fmptpr.3 $e |- ( ph -> C e. X ) $.
    fmptpr.4 $e |- ( ph -> D e. Y ) $.
    fmptpr.5 $e |- ( ( ph /\ x = A ) -> E = C ) $.
    fmptpr.6 $e |- ( ( ph /\ x = B ) -> E = D ) $.
    $( Express a pair function in maps-to notation.  (Contributed by Thierry
       Arnoux, 3-Jan-2017.) $)
    fmptpr $p |- ( ph ->
      { <. A , C >. , <. B , D >. } = ( x e. { A , B } |-> E ) ) $=
      ( cun c0 wcel cop cpr csn cmpt wceq df-pr a1i uneq1i uncom un0 3eqtri cvv
      mpt0 elex syl eqtr3i fmptapd syl5eqr uneq1d eqcomi 3eqtrd ) ACEUAZDFUAZUB
      ZVBUCZVCUCZRZBCUCZGUDZVFRBCDUBZGUDVDVGUEAVBVCUFUGAVEVIVFAVEBSGUDZVERZVIVL
      SVERVESRVEVKSVEBGUMUHSVEUIVEUJUKABCEGSVHACHTCULTLCHUNUOAEJTEULTNEJUNUOSVH
      RZVHUEAVHSRVMVHVHSUIVHUJUPUGPUQURUSABDFGVHVJADITDULTMDIUNUOAFKTFULTOFKUNU
      OVHDUCRZVJUEAVJVNCDUFUTUGQUQVA $.
  $}

  ${
    $d x A $.  $d x B $.  $d x F $.
    $( Condition for the membership in the union of the range of a function.
       (Contributed by Thierry Arnoux, 13-Nov-2016.) $)
    elunirn2 $p |- ( ( Fun F /\ B e. ( F ` A ) ) -> B e. U. ran F ) $=
      ( vx wfun cfv wcel wa crn cuni cdm wrex elfvdm wceq eleq2d rspcev mpancom
      cv fveq2 adantl wb elunirn adantr mpbird ) CEZBACFZGZHBCIJGZBDRZCFZGZDCKZ
      LZUGUMUEAULGUGUMBACMUKUGDAULUIANUJUFBUIACSOPQTUEUHUMUAUGDBCUBUCUD $.
  $}

  ${
    $d x y B $.  $d x y F $.  $d x y V $.  $d y ps $.
    abfmpunirn.1 $e |- F = ( x e. V |-> { y | ph } ) $.
    abfmpunirn.2 $e |- { y | ph } e. _V $.
    abfmpunirn.3 $e |- ( y = B -> ( ph <-> ps ) ) $.
    $( Membership in a union of a mapping function-defined family of sets.
       (Contributed by Thierry Arnoux, 28-Sep-2016.) $)
    abfmpunirn $p |- ( B e. U. ran F <-> ( B e. _V /\ E. x e. V ps ) ) $=
      ( crn cuni wcel cvv wrex elex cab cv cfv wfn wb fnmpti fnunirn ax-mp wceq
      fvmpt2 mpan2 eleq2d rexbiia bitri elabg rexbidv syl5bb biadan2 ) EFKLZMZE
      NMZBCGOZEUOPUPEADQZMZCGOZUQURUPECRZFSZMZCGOZVAFGTUPVEUACGUSFIHUBCEFGUCUDV
      DUTCGVBGMZVCUSEVFUSNMVCUSUEICGUSNFHUFUGUHUIUJUQUTBCGABDENJUKULUMUN $.
  $}

  ${
    $d x y B $.  $d x y F $.  $d x y V $.  $d y W $.  $d y ps $.
    rabfmpunirn.1 $e |- F = ( x e. V |-> { y e. W | ph } ) $.
    rabfmpunirn.2 $e |- W e. _V $.
    rabfmpunirn.3 $e |- ( y = B -> ( ph <-> ps ) ) $.
    $( Membership in a union of a mapping function-defined family of sets.
       (Contributed by Thierry Arnoux, 30-Sep-2016.) $)
    rabfmpunirn $p |- ( B e. U. ran F <-> E. x e. V ( B e. W /\ ps ) ) $=
      ( crn cuni wcel cvv wa wrex cv crab cmpt cab df-rab mpteq2i eqtri zfausab
      wceq eleq1 anbi12d abfmpunirn elex adantr rexlimivw pm4.71ri bitr4i ) EFL
      MNEONZEHNZBPZCGQZPURDRZHNZAPZUQCDEFGFCGADHSZTCGVADUAZTICGVBVCADHUBUCUDADH
      JUEUSEUFUTUPABUSEHUGKUHUIURUOUQUOCGUPUOBEHUJUKULUMUN $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y F $.  $d x y V $.  $d y W $.  $d x y ch $.
    $d x y ch $.  $d x y ph $.  $d z x $.
    abfmpeld.1 $e |- F = ( x e. V |-> { y | ps } ) $.
    abfmpeld.2 $e |- ( ph -> { y | ps } e. _V ) $.
    abfmpeld.3 $e |- ( ph -> ( ( x = A /\ y = B ) -> ( ps <-> ch ) ) ) $.
    $( Membership in an element of a mapping function-defined family of sets.
       (Contributed by Thierry Arnoux, 19-Oct-2016.) $)
    abfmpeld $p |- ( ph -> ( ( A e. V /\ B e. W ) ->
        ( B e. ( F ` A ) <-> ch ) ) ) $=
      ( wcel wa wb cab cvv wceq wal cfv wsbc alrimiv csbexg fvmpts sylan2 csbab
      csb syl6eq eleq2d adantl cv wi simpll ancomsd impl sbcied ex elabgt bitrd
      syl an13s ) AFINZGJNZOGFHUAZNZCPZVDVCAVGVDVCAOZOVFGBDFUBZEQZNZCVHVFVKPVDV
      HVEVJGVHVEDFBEQZUHZVJAVCVMRNZVEVMSAVLRNZDTVNAVODLUCDFVLRUDVADFVLIHRKUEUFB
      DEFUGUIUJUKVHVDEULGSZVICPZUMZETVKCPVHVREVHVPVQVHVPOBCDFIVCAVPUNVHVPDULFSZ
      BCPZAVPVSOVTUMVCAVSVPVTMUOUKUPUQURUCVICEGJUSUFUTVBUR $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y F $.  $d x y V $.  $d y W $.  $d x y ps $.
    $d y W $.  $d z x $.
    abfmpel.1 $e |- F = ( x e. V |-> { y | ph } ) $.
    abfmpel.2 $e |- { y | ph } e. _V $.
    abfmpel.3 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    $( Membership in an element of a mapping function-defined family of sets.
       (Contributed by Thierry Arnoux, 19-Oct-2016.) $)
    abfmpel $p |- ( ( A e. V /\ B e. W ) -> ( B e. ( F ` A ) <-> ps ) ) $=
      ( wcel wa cab wb cvv wceq cv ancoms cfv wsbc csb csbex fvmpts mpan2 csbab
      syl6eq eleq2d adantr wi wal simpl adantll sbcied ex alrimiv elabgt sylan2
      bitrd ) EHMZFIMZNFEGUAZMZFACEUBZDOZMZBVAVDVGPVBVAVCVFFVAVCCEADOZUCZVFVAVI
      QMVCVIRCEVHKUDCEVHHGQJUEUFACDEUGUHUIUJVBVAVGBPZVAVBDSFRZVEBPZUKZDULVJVAVM
      DVAVKVLVAVKNABCEHVAVKUMVKCSERZABPZVAVNVKVOLTUNUOUPUQVEBDFIURUSTUT $.
  $}

  ${
    $d w x y z $.  $d w z A $.  $d w z A $.  $d w z B $.  $d w z C $.
    cbvmptf.1 $e |- F/_ x A $.
    cbvmptf.2 $e |- F/_ y A $.
    cbvmptf.3 $e |- F/_ y B $.
    cbvmptf.4 $e |- F/_ x C $.
    cbvmptf.5 $e |- ( x = y -> B = C ) $.
    $( Rule to change the bound variable in a maps-to function, using implicit
       substitution.  This version has bound-variable hypotheses in place of
       distinct variable conditions.  (Contributed by Thierry Arnoux,
       9-Mar-2017.) $)
    cbvmptf $p |- ( x e. A |-> B ) = ( y e. A |-> C ) $=
      ( vz vw cv wcel wceq wa copab cmpt nfv weq nfcri nfs1v nfan eleq1 sbequ12
      wsb anbi12d cbvopab1 nfeq2 nfsb eqeq2d sbhypf eqtri df-mpt 3eqtr4i ) AMZC
      NZKMZDOZPZAKQZBMZCNZUREOZPZBKQZACDRBCERVALMZCNZUSALUFZPZLKQVFUTVJAKLUTLSV
      HVIAALCFUAUSALUBUCALTUQVHUSVIUPVGCUDUSALUEUGUHVJVELKBVHVIBBLCGUAUSALBBURD
      HUIUJUCVELSLBTVHVCVIVDVGVBCUDUSVDALVBAUREIUIABTDEURJUKULUGUHUMAKCDUNBKCEU
      NUO $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.  $d y ph $.
    fmptdF.p $e |- F/ x ph $.
    fmptdF.a $e |- F/_ x A $.
    fmptdF.c $e |- F/_ x C $.
    fmptdF.1 $e |- ( ( ph /\ x e. A ) -> B e. C ) $.
    fmptdF.2 $e |- F = ( x e. A |-> B ) $.
    $( Domain and co-domain of the mapping operation; deduction form.  This
       version of ~ fmptd usex bound-variable hypothesis instead of distinct
       variable conditions.  (Contributed by Thierry Arnoux, 28-Mar-2017.) $)
    fmptdF $p |- ( ph -> F : A --> C ) $=
      ( vy wf cv csb wcel wa wsb bitri cvv cmpt wral sbimi sbf clelsb3f anbi12i
      sban wsbc sbsbc sbcel12 wceq vex csbconstgf eleq2i 3imtr3i ralrimiva nfcv
      ax-mp nfcsb1v csbeq1a cbvmptf fmpt sylib feq1i sylibr ) ACEBCDUAZMZCEFMAB
      LNZDOZEPZLCUBVGAVJLCABNCPZQZBLRZDEPZBLRZAVHCPZQZVJVLVNBLJUCVMABLRZVKBLRZQ
      VQAVKBLUGVRAVSVPABLGUDLBCHUEUFSVOVNBVHUHZVJVNBLUIVTVIBVHEOZPVJBVHDEUJWAEV
      IVHTPWAEUKLULBVHETIUMURUNSSUOUPLCEVIVFBLCDVIHLCUQLDUQBVHDUSBVHDUTVAVBVCCE
      FVFKVDVE $.
  $}

  ${
    $d x A $.  $d x C $.  $d x ph $.
    fmpt3d.1 $e |- ( ph -> F = ( x e. A |-> B ) ) $.
    fmpt3d.2 $e |- ( ( ph /\ x e. A ) -> B e. C ) $.
    $( Domain and co-domain of the mapping operation; deduction form.
       (Contributed by Thierry Arnoux, 4-Jun-2017.) $)
    fmpt3d $p |- ( ph -> F : A --> C ) $=
      ( wf cmpt eqid fmptd feq1d mpbird ) ACEFICEBCDJZIABCDEOHOKLACEFOGMN $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.
    resmptf.a $e |- F/_ x A $.
    resmptf.b $e |- F/_ x B $.
    $( Restriction of the mapping operation.  (Contributed by Thierry Arnoux,
       28-Mar-2017.) $)
    resmptf $p |- ( B C_ A -> ( ( x e. A |-> C ) |` B ) = ( x e. B |-> C ) ) $=
      ( vy wss cv cmpt cres resmpt nfcv nfcsb1v csbeq1a cbvmptf reseq1i 3eqtr4g
      csb ) CBHGBAGIZDSZJZCKGCUAJABDJZCKACDJGBCUALUCUBCAGBDUAEGBMGDMZATDNZATDOZ
      PQAGCDUAFGCMUDUEUFPR $.
  $}

  ${
    $d x y $.  $d y z A $.  $d y z B $.  $d y D $.  $d y z F $.
    fvmpt2f.0 $e |- F/_ x A $.
    $( Value of a function given by the "maps to" notation.  (Contributed by
       Thierry Arnoux, 9-Mar-2017.) $)
    fvmpt2f $p |- ( ( x e. A /\ B e. C ) -> ( ( x e. A |-> B ) ` x ) = B ) $=
      ( vy csb cmpt weq csbeq1 csbid syl6eq nfcv nfcsb1v csbeq1a cbvmptf fvmptg
      cv ) FARZAFRZCGZCBDABCHFAIUAASCGCATSCJACKLAFBCUAEFBMFCMATCNATCOPQ $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.
    mptfnf.0 $e |- F/_ x A $.
    $( The maps-to notation defines a function with domain.  (Contributed by
       Scott Fenton, 21-Mar-2011.)  (Revised by Thierry Arnoux,
       10-May-2017.) $)
    mptfnf $p |- ( A. x e. A B e. _V <-> ( x e. A |-> B ) Fn A ) $=
      ( vy wcel wral cv wceq wfn ralbii wex wmo wa wal wi albii df-ral 3bitr4ri
      cab cvv weu cmpt eueq r19.26 eu5 copab wfun cdm df-mpt fneq1i df-fn bitri
      moanimv funopab eqcom dmopab 19.42v abbii eqeq1i wb pm4.71 abeq2f 3bitr4i
      eqtri anbi12i ancom 3bitr2i bitr4i ) CUAFZABGEHCIZEUBZABGZABCUCZBJZVJVLAB
      ECUDKVKELZVKEMZNZABGVPABGZVQABGZNZVMVOVPVQABUEVLVRABVKEUFKVOAHBFZVKNZAEUG
      ZUHZWDUIZBIZNZVTVSNWAVOWDBJWHBVNWDAEBCUJUKWDBULUMVTWEVSWGWCEMZAOWBVQPZAOW
      EVTWIWJAWBVKEUNQWCAEUOVQABRSWBVPNZATZBIBWLIZWGVSWLBUPWFWLBWFWCELZATWLWCAE
      UQWNWKAWBVKEURUSVEUTWBVPPZAOWBWKVAZAOVSWMWOWPAWBVPVBQVPABRWKABDVCVDSVFVTV
      SVGVHSVI $.

    $( The maps-to notation defines a function with domain.  (Contributed by
       NM, 9-Apr-2013.)  (Revised by Thierry Arnoux, 10-May-2017.) $)
    fnmptf $p |- ( A. x e. A B e. V -> ( x e. A |-> B ) Fn A ) $=
      ( wcel wral cvv cmpt wfn elex ralimi mptfnf sylib ) CDFZABGCHFZABGABCIBJO
      PABCDKLABCEMN $.
  $}

  ${
    $d x y $.  $d y A $.  $d y F $.
    feqmptdf.1 $e |- F/_ x A $.
    feqmptdf.2 $e |- F/_ x F $.
    feqmptdf.3 $e |- ( ph -> F : A --> B ) $.
    $( Deduction form of ~ dffn5f .  (Contributed by Mario Carneiro,
       8-Jan-2015.)  (Revised by Thierry Arnoux, 10-May-2017.) $)
    feqmptdf $p |- ( ph -> F = ( x e. A |-> ( F ` x ) ) ) $=
      ( vy wf wfn cv cfv cmpt wceq ffn wcel wa copab wbr wrel fnrel nfcv dfrel4
      sylib nffn nfv fnbr pm4.71rd eqcom fnbrfvb syl5bb pm5.32da bitr4d opabbid
      ex eqtrd df-mpt syl6eqr 3syl ) ACDEJECKZEBCBLZEMZNZOHCDEPVAEVBCQZILZVCOZR
      ZBISZVDVAEVBVFETZBISZVIVAEUAEVKOCEUBBIEGIEUCUDUEVAVJVHBIBCEGFUFVAIUGVAVJV
      EVJRVHVAVJVEVAVJVECVBVFEUHUPUIVAVEVGVJVGVCVFOVAVERVJVFVCUJCVBVFEUKULUMUNU
      OUQBICVCURUSUT $.
  $}

  ${
    $d u v w x y z $.  $d u v w z A $.  $d u y B $.  $d u w z F $.
    $d u w z G $.  $d u y R $.  $d u x S $.  $d u v w y z T $.  $d u w z ph $.
    fmptcof2.1 $e |- F/_ x A $.
    fmptcof2.2 $e |- F/_ x B $.
    fmptcof2.3 $e |- F/ x ph $.
    fmptcof2.4 $e |- ( ph -> A. x e. A R e. B ) $.
    fmptcof2.5 $e |- ( ph -> F = ( x e. A |-> R ) ) $.
    fmptcof2.6 $e |- ( ph -> G = ( y e. B |-> S ) ) $.
    fmptcof2.7 $e |- ( y = R -> S = T ) $.
    $( Composition of two functions expressed as ordered-pair class
       abstractions.  (Contributed by FL, 21-Jun-2012.)  (Revised by Mario
       Carneiro, 24-Jul-2014.)  (Revised by Thierry Arnoux, 10-May-2017.) $)
    fmptcof2 $p |- ( ph -> ( G o. F ) = ( x e. A |-> T ) ) $=
      ( wa wcel wceq vz vw vu ccom cmpt relco wfun wrel funmpt funrel ax-mp wbr
      vv cv wex csb cop cfv wf r19.21bi eqid fmptdF mpbird ffun syl funbrfv imp
      feq1d sylan eqcomd a1d expimpd pm4.71rd exbidv fvex breq2 anbi12d ceqsexv
      breq1 cdm wb funfvbrb fdm eleq2d bitr3d fveq1d eqidd breq123d wi nffvmpt1
      nfcri nfcv nfmpt nfbr nfcsb1v nfeq2 nfbi nfim eleq1 breq1d csbeq1a eqeq2d
      fveq2 bibi12d imbi2d imbi12d cvv simpl eleq1d simpr adantr eqeq12d df-mpt
      vex brabga sylancl fvmpt2f syl2anc biantrurd expcom chvar impcom pm5.32da
      3bitr4d bitrd syl5bb opelco copab eleq2i nfv eqeq1 anbi2d opelopabf bitri
      nfan 3bitr4g eqrelrdv ) AUAUBJIUDZBDHUEZJIUFYSUGYSUHBDHUIYSUJUKAUAUNZUCUN
      ZIULZUUAUBUNZJULZRZUCUOZYTDSZUUCBYTHUPZTZRZYTUUCUQZYRSUUKYSSZAUUFUUAYTIUR
      ZTZUUERZUCUOZUUJAUUEUUOUCAUUEUUNAUUBUUDUUNAUUBRZUUNUUDUUQUUMUUAAIUGZUUBUU
      MUUATZADEIUSZUURAUUTDEBDFUEZUSABDFEUVAMKLAFESZBDNUTZUVAVAVBADEIUVAOVHVCZD
      EIVDVEZUURUUBUUSYTUUAIVFVGVIVJVKVLVMVNUUPYTUUMIULZUUMUUCJULZRZAUUJUUEUVHU
      CUUMYTIVOUUNUUBUVFUUDUVGUUAUUMYTIVPUUAUUMUUCJVSVQVRAUVHUUGYTUVAURZUUCCEGU
      EZULZRUUJAUVFUUGUVGUVKAYTIVTZSZUVFUUGAUURUVMUVFWAUVEYTIWBVEAUVLDYTAUUTUVL
      DTUVDDEIWCVEWDWEAUUMUVIUUCUUCJUVJAYTIUVAOWFPAUUCWGWHVQAUUGUVKUUIUUGAUVKUU
      IWAZBUNZDSZAUVOUVAURZUUCUVJULZUUCHTZWAZWIZWIUUGAUVNWIZWIBUAUUGUWBBBUADKWK
      ZAUVNBMUVKUUIBBUVIUUCUVJBDFYTWJBCEGLBGWLWMBUUCWLWNBUUCUUHBYTHWOZWPWQWRWRU
      VOYTTZUVPUUGUWAUWBUVOYTDWSZUWEUVTUVNAUWEUVRUVKUVSUUIUWEUVQUVIUUCUVJUVOYTU
      VAXCWTUWEHUUHUUCBYTHXAZXBXDXEXFAUVPUVTAUVPRZFUUCUVJULZUVBUVSRZUVRUVSUWHUV
      BUUCXGSUWIUWJWAUVCUBXNZCUNZESZUUAGTZRUWJCUCFUUCUVJEXGUWLFTZUUAUUCTZRZUWMU
      VBUWNUVSUWQUWLFEUWOUWPXHXIUWQUUAUUCGHUWOUWPXJUWOGHTUWPQXKXLVQCUCEGXMXOXPU
      WHUVQFUUCUVJUWHUVPUVBUVQFTAUVPXJUVCBDFEKXQXRWTUWHUVBUVSUVCXSYDXTYAYBYCYEY
      FYEUCYTUUCJIUAXNZUWKYGUULUUKUVPUMUNZHTZRZBUMYHZSUUJYSUXBUUKBUMDHXMYIUXAUU
      GUWSUUHTZRUUJBUMYTUUCUUGUXCBUWCBUWSUUHUWDWPYOUUJUMYJUWRUWKUWEUVPUUGUWTUXC
      UWFUWEHUUHUWSUWGXBVQUWSUUCTUXCUUIUUGUWSUUCUUHYKYLYMYNYPYQ $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x C $.  $d x y D $.  $d x E $.
    fcomptf.1 $e |- F/_ x B $.
    $( Express composition of two functions as a maps-to applying both in
       sequence.  This version has one less distinct variable restriction
       compared to ~ fcompt .  (Contributed by Thierry Arnoux, 30-Jun-2017.) $)
    fcomptf $p |- ( ( A : D --> E /\ B : C --> D ) -> ( A o. B ) = ( x e. C |->
        ( A ` ( B ` x ) ) ) ) $=
      ( vy wf wa cv cfv wcel nfcv nff wfn cmpt wceq ffn sylib ffvelrn ex adantl
      nfan adantll ralrimi dffn5f adantr dffn5 fveq2 fmptcof ) EFBIZDECIZJZAHDE
      AKZCLZHKZBLZUPBLCBUNUPEMZADULUMAAEFBABNAENZAFNOADECGADNUTOUDUNUODMZUSUMVA
      USULDEUOCUAUEUBUFUNCDPZCADUPQRUMVBULDECSUCADCGUGTUNBEPZBHEURQRULVCUMEFBSU
      HHEBUITUQUPBUJUK $.
  $}

  ${
    $d x A $.  $d y B $.  $d x y C $.  $d x y F $.  $d x ph $.
    cofmpt.1 $e |- ( ph -> F : C --> D ) $.
    cofmpt.2 $e |- ( ( ph /\ x e. A ) -> B e. C ) $.
    $( Express composition of a maps-to function with another function in a
       maps-to notation.  (Contributed by Thierry Arnoux, 29-Jun-2017.) $)
    cofmpt $p |- ( ph ->
                     ( F o. ( x e. A |-> B ) ) = ( x e. A |-> ( F ` B ) ) ) $=
      ( vy cv cfv cmpt eqidd feqmptd fveq2 fmptco ) ABJCEDJKZGLDGLBCDMZGIASNAJE
      FGHORDGPQ $.
  $}

  ${
    $d a x y A $.  $d a x y B $.  $d a x y C $.  $d a x y F $.  $d a x y G $.
    $d a N $.  $d a x y R $.  $d a x y ph $.
    ofoprabco.1 $e |- F/_ a M $.
    ofoprabco.2 $e |- ( ph -> F : A --> B ) $.
    ofoprabco.3 $e |- ( ph -> G : A --> C ) $.
    ofoprabco.4 $e |- ( ph -> A e. V ) $.
    ofoprabco.5 $e |- ( ph ->
                            M = ( a e. A |-> <. ( F ` a ) , ( G ` a ) >. ) ) $.
    ofoprabco.6 $e |- ( ph -> N = ( x e. B , y e. C |-> ( x R y ) ) ) $.
    $( Function operation as a composition with an operation.  (Contributed by
       Thierry Arnoux, 4-Jun-2017.) $)
    ofoprabco $p |- ( ph -> ( F oF R G ) = ( N o. M ) ) $=
      ( cvv cv cfv cmpt ccom cof wcel cop cxp ffvelrnda opelxpi syl2anc fvmpt2d
      co wa fveq2d df-ov a1i cmpt2 adantr simprl simprr oveq12d ovmpt2d 3eqtr2d
      wceq ovex mpteq2dva wf wral rgen2w eqid fmpt2 feq1d mpbiri fmpt3d fcomptf
      mpbi feqmptd offval2 3eqtr4rd ) AMDMUAZJUBZKUBZUCZMDWAHUBZWAIUBZGUMZUCKJU
      DZHIGUEUMAMDWCWGAWADUFZUNZWCWEWFUGZKUBZWEWFKUMZWGWJWBWKKAMDWKJEFUHZRWJWEE
      UFWFFUFWKWNUFADEWAHOUIZADFWAIPUIZWEWFEFUJUKZULUOWMWLVEWJWEWFKUPUQWJBCWEWF
      EFBUAZCUAZGUMZWGKTAKBCEFWTURZVEWISUSWJWRWEVEZWSWFVEZUNUNWRWEWSWFGWJXBXCUT
      WJXBXCVAVBWOWPWGTUFWJWEWFGVFUQVCVDVGAWNTKVHZDWNJVHWHWDVEAXDWNTXAVHZWTTUFZ
      CFVIBEVIXEXFBCEFWRWSGVFVJBCEFWTTXAXAVKVLVQAWNTKXASVMVNAMDWKWNJRWQVOMKJDWN
      TNVPUKAMDWEWFGHILEFQWOWPAMDEHOVRAMDFIPVRVSVT $.
  $}

  ${
    $d y z A $.  $d y z B $.  $d y z C $.  $d y F $.  $d y G $.  $d y ph $.
    $d x y z R $.
    offval2f.0 $e |- F/ x ph $.
    offval2f.a $e |- F/_ x A $.
    offval2f.1 $e |- ( ph -> A e. V ) $.
    offval2f.2 $e |- ( ( ph /\ x e. A ) -> B e. W ) $.
    offval2f.3 $e |- ( ( ph /\ x e. A ) -> C e. X ) $.
    offval2f.4 $e |- ( ph -> F = ( x e. A |-> B ) ) $.
    offval2f.5 $e |- ( ph -> G = ( x e. A |-> C ) ) $.
    $( The function operation expressed as a mapping.  (Contributed by Thierry
       Arnoux, 23-Jun-2017.) $)
    offval2f $p |- ( ph -> ( F oF R G ) = ( x e. A |-> ( B R C ) ) ) $=
      ( vy cmpt cof co cv cfv wfn wcel wral ex ralrimi fnmptf syl fneq1d mpbird
      inidm wa wceq adantr fveq1d offval nfcv nffvmpt1 nfov fveq2 oveq12d simpr
      cbvmptf fvmpt2f syl2anc mpteq2da syl5eq eqtrd ) AGHFUAUBSCSUCZBCDTZUDZVLB
      CETZUDZFUBZTZBCDEFUBZTZASCCVNVPFCGHIIAGCUEVMCUEZADJUFZBCUGWAAWBBCLABUCZCU
      FZWBOUHUIBCDJMUJUKACGVMQULUMAHCUEVOCUEZAEKUFZBCUGWEAWFBCLAWDWFPUHUIBCEKMU
      JUKACHVORULUMNNCUNAVLCUFZUOZVLGVMAGVMUPWGQUQURWHVLHVOAHVOUPWGRUQURUSAVRBC
      WCVMUDZWCVOUDZFUBZTVTSBCVQWKSCUTMBVNVPFBCDVLVABFUTBCEVLVAVBSWKUTVLWCUPVNW
      IVPWJFVLWCVMVCVLWCVOVCVDVFABCWKVSLAWDUOZWIDWJEFWLWDWBWIDUPAWDVEZOBCDJMVGV
      HWLWDWFWJEUPWMPBCEKMVGVHVDVIVJVK $.
  $}

  ${
    $d p q s x y A $.  $d s x y B $.  $d s x y C $.  $d p q D $.
    $d p q s x y F $.  $d p q s x y G $.  $d p q s x y R $.  $d p q s x y ph $.
    ofpreima.1 $e |- ( ph -> F : A --> B ) $.
    ofpreima.2 $e |- ( ph -> G : A --> C ) $.
    ofpreima.3 $e |- ( ph -> A e. V ) $.
    ofpreima.4 $e |- ( ph -> R Fn ( B X. C ) ) $.
    $( Express the preimage of a function operation as a union of preimages.
       (Contributed by Thierry Arnoux, 8-Mar-2018.) $)
    ofpreima $p |- ( ph -> ( `' ( F oF R G ) " D ) = U_ p e. ( `' R " D )
         ( ( `' F " { ( 1st ` p ) } ) i^i ( `' G " { ( 2nd ` p ) } ) ) ) $=
      ( vs vq cfv wceq wcel wa vx vy cof co ccnv cima cv cop cmpt c1st csn c2nd
      cin ciun ccom nfmpt1 eqidd cmpt2 fnov sylib ofoprabco cnveqd cnvco syl6eq
      cxp wfn imaeq1d imaco wbr wrex cab dfima2 vex brcnv cdm wfun wb funbrfv2b
      funmpt ax-mp opex dmmpti eleq2i anbi1i bitri fveq2 opeq12d eqeq1d pm5.32i
      eqid fvmpt 3bitri rexbii abbii nfv nfab1 nfcv eliun elin wf fniniseg 3syl
      ffn anbi12d anandi syl6bbr syl5bb adantr cnvimass fndm syl sselda 1st2nd2
      syl5sseq fvex opth syl6bb anbi2d bitr4d rexbidva abid syl5rbb eqrd syl5eq
      eqeq2 eqtrd ) AGHFUCUDZUEZEUFZOBOUGZGQZYJHQZUHZUIZUEZFUEZEUFZUFZJYQGUEJUG
      ZUJQZUKUFZHUEYSULQZUKUFZUMZUNZAYIYOYPUOZEUFYRAYHUUFEAYHFYNUOZUEUUFAYGUUGA
      UAUBBCDFGHYNFIOOBYMUPKLMAYNUQAFCDVEZVFZFUAUBCDUAUGUBUGFUDURRNUAUBCDFUSUTV
      AVBFYNVCVDVGYOYPEVHVDAYRYSPUGZYOVIZJYQVJZPVKZUUEJPYOYQVLAUUMUUJBSZUUJGQZU
      UJHQZUHZYSRZTZJYQVJZPVKZUUEUULUUTPUUKUUSJYQUUKUUJYSYNVIZUUNUUJYNQZYSRZTZU
      USYSUUJYNJVMPVMVNUVBUUJYNVOZSZUVDTZUVEYNVPUVBUVHVQOBYMVSUUJYSYNVRVTUVGUUN
      UVDUVFBUUJOBYMYNYKYLWAYNWJZWBWCWDWEUUNUVDUURUUNUVCUUQYSOUUJYMUUQBYNYJUUJR
      YKUUOYLUUPYJUUJGWFYJUUJHWFWGUVIUUOUUPWAWKWHWIWLWMWNAPUVAUUEAPWOUUTPWPPUUE
      WQUUJUUESUUJUUDSZJYQVJZAUUJUVASZJUUJYQUUDWRAUVKUUTUVLAUVJUUSJYQAYSYQSZTZU
      VJUUNUUOYTRZUUPUUBRZTZTZUUSAUVJUVRVQUVMUVJUUJUUASZUUJUUCSZTZAUVRUUJUUAUUC
      WSAUWAUUNUVOTZUUNUVPTZTUVRAUVSUWBUVTUWCABCGWTGBVFUVSUWBVQKBCGXCBYTUUJGXAX
      BABDHWTHBVFUVTUWCVQLBDHXCBUUBUUJHXAXBXDUUNUVOUVPXEXFXGXHUVNUURUVQUUNUVNUU
      RUUQYTUUBUHZRZUVQUVNYSUUHSYSUWDRUURUWEVQAYQUUHYSAFVOZYQUUHFEXIAUUIUWFUUHR
      NUUHFXJXKXNXLYSCDXMYSUWDUUQYEXBUUOUUPYTUUBUUJGXOUUJHXOXPXQXRXSXTUUTPYAXFY
      BYCYDYDYF $.

    $( Express the preimage of a function operation as a union of preimages.
       This version of ~ ofpreima iterates the union over a smaller set.
       (Contributed by Thierry Arnoux, 8-Mar-2018.) $)
    ofpreima2 $p |- ( ph -> ( `' ( F oF R G ) " D ) =
         U_ p e. ( ( `' R " D ) i^i ( ran F X. ran G ) )
         ( ( `' F " { ( 1st ` p ) } ) i^i ( `' G " { ( 2nd ` p ) } ) ) ) $=
      ( cin ciun wceq syl6eq c0 syl cof co ccnv cima crn cxp c1st cfv c2nd cdif
      cv csn cun ofpreima inundif iuneq1 ax-mp iunxun eqtr3i wral wcel wa wo wn
      simpr eldifbd cop wi difssd cdm cnvimass wfn fndm syl5sseq sselda 1st2nd2
      sstrd elxp6 biimpri ex con3d mpd ianor sylib disjsn orbi12i sylibr wf ffn
      3syl dffn3 fimacnvdisj ineq1 incom in0 eqtri ineq2 jaao syl2anc ralrimiva
      adantr iuneq2 iun0 uneq2d un0 eqtrd ) AGHFUAUBUCEUDZJFUCEUDZGUEZHUEZUFZOZ
      GUCJUKZUGUHZULZUDZHUCXMUIUHZULZUDZOZPZJXHXKUJZXTPZUMZYAAXGJXHXTPZYDABCDEF
      GHIJKLMNUNJXLYBUMZXTPZYEYDYFXHQYGYEQXHXKUOJYFXHXTUPUQJXLYBXTURUSRAYDYASUM
      YAAYCSYAAYCJYBSPZSAXTSQZJYBUTYCYHQAYIJYBAXMYBVAZVBZXIXOOSQZXJXROSQZVCZYIY
      KXNXIVAZVDZXQXJVAZVDZVCZYNYKYOYQVBZVDZYSYKXMXKVAZVDUUAYKXMXHXKAYJVEVFYKYT
      UUBYKXMCDUFZVAXMXNXQVGQZYTUUBVHAYBUUCXMAYBXHUUCAXHXKVIAFVJZXHUUCFEVKAFUUC
      VLUUEUUCQNUUCFVMTVNVQVOXMCDVPUUDYTUUBUUBUUDYTVBXMXIXJVRVSVTWJWAWBYOYQWCWD
      YLYPYMYRXIXNWEXJXQWEWFWGYKBXIGWHZBXJHWHZYNYIVHAUUFYJAGBVLZUUFABCGWHUUHKBC
      GWITBGWKWDXAAUUGYJAHBVLZUUGABDHWHUUILBDHWITBHWKWDXAUUFYLYIUUGYMUUFYLYIUUF
      YLVBXPSQZYIBXIXOGWLUUJXTSXSOZSXPSXSWMUUKXSSOSSXSWNXSWOWPRTVTUUGYMYIUUGYMV
      BXSSQZYIBXJXRHWLUULXTXPSOSXSSXPWQXPWORTVTWRWSWBWTJYBXTSXBTJYBXCRXDYAXERXF
      $.
  $}

  ${
    $d w x y z $.  $d w A $.  $d w B $.  $d y F $.  $d y z ph $.
    funcnvmpt.0 $e |- F/ x ph $.
    funcnvmpt.1 $e |- F/_ x A $.
    funcnvmpt.2 $e |- F/_ x F $.
    funcnvmpt.3 $e |- F = ( x e. A |-> B ) $.
    funcnvmpt.4 $e |- ( ( ph /\ x e. A ) -> B e. V ) $.
    $( Condition for a function in maps-to notation to be single-rooted.
       (Contributed by Thierry Arnoux, 28-Feb-2017.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    funcnvmptOLD $p |- ( ph ->
              ( Fun `' F <-> A. y E* x ( x e. A /\ y = B ) ) ) $=
      ( wfun cv wmo wal wcel wceq wa wb ccnv wbr wrel relcnv nfcv nfcnv dffun6f
      mpbiran vex brcnv mobii albii bitri nfv cfv funmpt funeqi mpbir funbrfv2b
      cdm cmpt ax-mp cvv crab wral syl ex ralrimi rabid2f sylibr dmmpt syl6reqr
      eleq2d anbi1d syl5bb bian1d fveq1i simpr fvmpt2f syl2anc syl5eq eqeq2d wi
      elex biimpar funbrfvb sylancr eqcom bibi1i imbi2i bitr3d pm5.32d 3bitr4rd
      mpbi mobid albid ) FUAZMZBNZCNZFUBZBOZCPZAWSDQZWTERZSZBOZCPWRWTWSWQUBZBOZ
      CPZXCWRWQUCXJFUDCBWQCWQUEBFJUFUGUHXIXBCXHXABWTWSFCUIBUIUJUKULUMAXBXGCACUN
      AXAXFBHAXDXASXDWSFUOZWTRZSZXFXAAXAXDXLXAWSFUTZQZXLSZAXMFMZXAXPTXQBDEVAZMB
      DEUPFXRKUQURZWSWTFUSVBAXOXDXLAXNDWSADEVCQZBDVDZXNAXTBDVEDYARAXTBDHAXDXTAX
      DSZEGQZXTLEGWDVFVGVHXTBDIVIVJBDEFKVKVLVMZVNVOZVPAXDXEXAAXDXEXATYBWTXKRZXE
      XAYBXKEWTYBXKWSXRUOZEWSFXRKVQYBXDYCYGERAXDVRLBDEGIVSVTWAWBYBXLXATZWCYBYFX
      ATZWCYBXQXOYHXSAXOXDYDWEWSWTFWFWGYHYIYBXLYFXAXKWTWHWIWJWNWKVGWLYEWMWOWPVO
      $.

    $( Condition for a function in maps-to notation to be single-rooted.
       (Contributed by Thierry Arnoux, 28-Feb-2017.) $)
    funcnvmpt $p |- ( ph -> ( Fun `' F <-> A. y E* x e. A y = B ) ) $=
      ( wfun cv wbr wmo wal wceq wcel wa ccnv wrmo relcnv nfcnv dffun6f mpbiran
      wrel nfcv vex brcnv mobii albii bitri cfv cdm funmpt2 funbrfv2b ax-mp cvv
      wb crab wral elex syl ralrimi rabid2f sylibr dmmpt syl6reqr eleq2d anbi1d
      ex syl5bb bian1d simpr fveq1i fvmpt2f syl5eq syl2anc eqeq2d eqcom biimpar
      cmpt funbrfvb sylancr syl5bbr bitr3d pm5.32da mobid df-rmo syl6bbr albidv
      3bitr4rd ) FUAZMZBNZCNZFOZBPZCQZAWQERZBDUBZCQWOWQWPWNOZBPZCQZWTWOWNUGXEFU
      CCBWNCWNUHBFJUDUEUFXDWSCXCWRBWQWPFCUIBUIUJUKULUMAWSXBCAWSWPDSZXATZBPXBAWR
      XGBHAXFWRTXFWPFUNZWQRZTZXGWRAWRXFXIWRWPFUOZSZXITZAXJFMZWRXMUTBDEFKUPZWPWQ
      FUQURAXLXFXIAXKDWPADEUSSZBDVAZXKAXPBDVBDXQRAXPBDHAXFXPAXFTZEGSZXPLEGVCVDV
      LVEXPBDIVFVGBDEFKVHVIVJZVKVMZVNAXFXAWRXRWQXHRZXAWRXRXHEWQXRXFXSXHERAXFVOL
      XFXSTXHWPBDEWCZUNEWPFYCKVPBDEGIVQVRVSVTYBXIXRWRXHWQWAXRXNXLXIWRUTXOAXLXFX
      TWBWPWQFWDWEWFWGWHYAWMWIXABDWJWKWLVM $.

    ${
      $d y z A $.  $d y z B $.  $d x y C $.
      funcnv5mpt.1 $e |- ( x = z -> B = C ) $.
      $( Two ways to say that a function in maps-to notation is single-rooted.
         (Contributed by Thierry Arnoux, 1-Mar-2017.) $)
      funcnv5mpt $p |- ( ph -> ( Fun `' F <->
                                A. x e. A A. z e. A ( x = z \/ B =/= C ) ) ) $=
        ( vy cv wceq wal wral wi ccnv wfun wrmo wne wo funcnvmpt wa wcel wn wex
        nne eqvincg syl syl5bb imbi1d orcom df-or bitri 3bitr4g ralbidv ralcom4
        19.23v syl6bb ralbida nfcv nfv eqeq2d rmo4f albii bitr4i syl6bbr bitr4d
        wb ) AGUAUBOPZEQZBDUCZORZBPZCPQZEFUDZUEZCDSZBDSZABODEGHIJKLMUFAWCVOVNFQ
        ZUGZVSTZCDSZORZBDSZVQAWBWHBDIAVRDUHUGZWBWFORZCDSWHWJWAWKCDWJVTUIZVSTZWE
        OUJZVSTWAWKWJWLWNVSWLEFQZWJWNEFUKWJEHUHWOWNVMMOEFHULUMUNUOWAVTVSUEWMVSV
        TUPVTVSUQURWEVSOVBUSUTWFCODVAVCVDVQWGBDSZORWIVPWPOVOWDBCDJCDVEWDBVFVSEF
        VNNVGVHVIWGBODVAVJVKVL $.
    $}

    ${
      $d i j x $.  $d i j A $.  $d i j B $.  $d i F $.  $d x V $.  $d i j ph $.
      $( Two ways to say that a function in maps-to notation is single-rooted.
         (Contributed by Thierry Arnoux, 2-Mar-2017.) $)
      funcnv4mpt $p |- ( ph -> ( Fun `' F <->
        A. i e. A A. j e. A ( i = j \/ [_ i / x ]_ B =/= [_ j / x ]_ B ) ) ) $=
        ( cv csb nfcv cmpt wcel wa wsb nfcsb1v csbeq1a cbvmptf eqtri sbimi nfel
        nfv nfan weq eleq1 anbi2d sbie eleq1d 3imtr3i csbeq1 funcnv5mpt ) AEFCB
        ENZDOZBFNZDOGHAEUGECPZEGPGBCDQECURQLBECDURJUTEDPBUQDUAZBUQDUBZUCUDABNZC
        RZSZBETDHRZBETAUQCRZSZURHRZVEVFBEMUEVEVHBEAVGBIBUQCBUQPJUFUHBEUIZVDVGAV
        CUQCUJUKULVFVIBEBURHVABHPUFVJDURHVBUMULUNBUQUSDUOUP $.
    $}
  $}

  ${
    $d p q x y F $.  $d p q x y X $.
    $( Exactly one point of a function's graph has a given first element.
       (Contributed by Thierry Arnoux, 1-Apr-2018.) $)
    fgreu $p |- ( ( Fun F /\ X e. dom F ) -> E! p e. F X = ( 1st ` p ) ) $=
      ( vq wfun cdm wcel wa cv c1st cfv wceq wral wrex cop syl2anc simpr eqtr4d
      wb cvv wreu funfvop c2nd wrel simplll funrel simplr 1st2nd simpllr opeq1d
      syl eqeltrrd funopfvb biimpar syl21anc opeq12d fveq2d fvex mpan2 ad3antlr
      op1stg eqtr2d impbida ralrimiva eqeq2 bibi2d ralbidv rspcev reu6 sylibr )
      AEZBAFZGZHZBCIZJKZLZVODIZLZSZCAMZDANZVQCAUAVNBBAKZOZAGVQVOWDLZSZCAMZWBBAU
      BVNWFCAVNVOAGZHZVQWEWIVQHZVOVPVOUCKZOZWDWJAUDZWHVOWLLWJVKWMVKVMWHVQUEZAUF
      UKVNWHVQUGZVOAUHPZWJBVPWCWKWIVQQZWJVKVMBWKOZAGZWCWKLZWNVKVMWHVQUIWJVOWRAW
      JVOWLWRWPWJBVPWKWQUJRWOULVNWTWSBWKAUMUNUOUPRWIWEHZVPWDJKZBXAVOWDJWIWEQUQV
      MXBBLZVKWHWEVMWCTGXCBAURBWCVLTVAUSUTVBVCVDWAWGDWDAVRWDLZVTWFCAXDVSWEVQVRW
      DVOVEVFVGVHPVQCDAVIVJ $.
  $}

  ${
    $d p q r A $.  $d p q Y $. 
    $( If the converse of a relation ` A ` is a function, exactly one point of
       its graph has a given second element (that is, function value) 
       (Contributed by Thierry Arnoux, 1-Apr-2018.) $)
    fcnvgreu $p |- ( ( ( Rel A /\ Fun `' A ) /\ Y e. ran A )
      -> E! p e. A Y = ( 2nd ` p ) ) $=
      ( vq vr ccnv wa wcel cv c2nd cfv wceq wreu c1st wb csn cuni cxp syl simpr
      wrel wfun crn df-rn eleq2i fgreu adantll sylan2b cnvcnvss cnvssrndm sseli
      cdm cop dfdm4 xpeq12i syl6eleq 2nd1st eqcomd relcnv cnvf1olem simpld mpan
      mpdan sseldi adantl wral wrex adantr wss relssdmrn sselda syl12anc simplr
      simpl a1i ad2antlr simprd sneqd cnveqd ad2antrr 3eqtr2d impbida ralrimiva
      unieqd biidd eqeq2 bibi12d ralrimivw r19.21bi ralbidva rspcev reu6 sylibr
      syl2anc fvex op2ndd eqeq2d reuxfr4d mpbird ) AUAZAFZUBZGZBAUCZHZGBCIZJKZL
      ZCAMZBDIZNKZLZDXAMZXEXCBXAULZHZXMXDXNBAUDZUEXBXOXMWTXABDUFUGUHXCXIXMOXEXC
      XHXLCDXJJKZXKUMZAXAXJXAHZXRAHXCXSXAFZAXRAUIXSXRXJPZFZQZLZXRXTHZXSYCXRXSXJ
      XNXAUCZRZHYCXRLZXSXJXDAULZRZYGXAYJXJAUJUKXDXNYIYFXPAUNUOUPXJXNYFUQSZURZXA
      UAZXSYDGZYEAUSZYMYNGZYEXJXRPZFZQZLZXAXJXRUTZVAVBVCVDVEXCXFAHZGZXFXRLZXJEI
      ZLZOZDXAVFZEXAVGZUUDDXAMUUCXGXFNKUMZXAHZUUDXJUUJLZOZDXAVFZUUIUUCWTUUBUUJX
      FPZFZQZLZUUKXCWTUUBWTXBVNZVHZXCUUBTZUUCUUQUUJUUCXFYIXDRZHUUQUUJLZXCAUVBXF
      XCWTAUVBVIUUSAVJSVKXFYIXDUQSZURZWTUUBUURGGZUUKXFUUJPZFZQZLZAXFUUJUTZVAVLU
      UCUUMDXAUUCXSGZUUDUULUVLUUDGZXJYSUUQUUJUVMYMXSYDYTYMUVMYOVOUUCXSUUDVMXSYD
      UUCUUDYLVPYPYEYTUUAVQVLUVMUUPYRUVMUUOYQUVMXFXRUVLUUDTVRVSWDUUCUVCXSUUDUVD
      VTWAUVLUULGZXFUVIYCXRUUCUVJXSUULUUCWTUUBUURUVJUUTUVAUVEUVFUUKUVJUVKVQVLVT
      UVNYBUVHUVNYAUVGUVNXJUUJUVLUULTVRVSWDXSYHUUCUULYKVPWAWBWCUUHUUNEUUJXAUUEU
      UJLZUUGUUMDXAUVOUUGUUMOZDXAUVOUVPDXAUVOUUDUUDUUFUULUVOUUDWEUUEUUJXJWFWGWH
      WIWJWKWNUUDDEXAWLWMUUDXHXLOXCUUDXGXKBXQXKXFXJJWOXJNWOWPWQVEWRVHWS $.
  $}

  ${
    $d y z A $.  $d z B $.  $d z C $.  $d x y z D $.  $d z F $.
    rnmpt2ss.1 $e |- F = ( x e. A , y e. B |-> C ) $.
    $( The range of an operation given by the "maps to" notation as a subset.
       (Contributed by Thierry Arnoux, 23-May-2017.) $)
    rnmpt2ss $p |- ( A. x e. A A. y e. B C e. D -> ran F C_ D ) $=
      ( vz wcel wral crn cv wceq wrex rnmpt2 abeq2i wa simpl simpr r19.29d2r wi
      eleq1 biimparc a1i rexlimivv syl ex syl5bi ssrdv ) EFJZBDKACKZIGLZFIMZUMJ
      UNENZBDOACOZULUNFJZUPIUMABICDEGHPQULUPUQULUPRZUKUORZBDOACOUQURUKUOABCDULU
      PSULUPTUAUSUQABCDUSUQUBAMCJBMDJRUOUQUKUNEFUCUDUEUFUGUHUIUJ $.
  $}

  $( Rewrite a function defined by parts, using a mapping and an if construct,
     into a union of functions on disjoint domains.  (Contributed by Thierry
     Arnoux, 30-Mar-2017.) $)
  partfun $p |- ( x e. A |-> if ( x e. B , C , D ) ) =
                ( ( x e. ( A i^i B ) |-> C ) u. ( x e. ( A \ B ) |-> D ) ) $=
    ( cin cdif cun cv wcel cmpt mptun inundif eqid mpteq12i wceq inss2 mpteq2ia
    cif syl sseli iftrue wn eldifn iffalse uneq12i 3eqtr3i ) ABCFZBCGZHZAIZCJZD
    ESZKAUHUMKZAUIUMKZHABUMKAUHDKZAUIEKZHAUHUIUMLAUJUMBUMBCMUMNOUNUPUOUQAUHUMDU
    KUHJULUMDPUHCUKBCQUAULDEUBTRAUIUMEUKUIJULUCUMEPUKBCUDULDEUETRUFUG $.

  ${
    $d x y z A $.  $d x y z R $.
    $( Alternative definition of the converse of a relation.  (Contributed by
       Thierry Arnoux, 31-Mar-2018.) $)
    dfcnv2 $p |- ( ran R C_ A -> 
      `' R = U_ x e. A ( { x } X. ( `' R " { x } ) ) ) $=
      ( vz vy crn wss ccnv cv csn cima cxp ciun relcnv wrel wral wa vex syl6bbr
      wcel relxp rgenw reliun mpbir cop cdm opeldm df-rn syl6eleqr ssel2 sylan2
      ex pm4.71rd elimasn anbi2i wceq sneq imaeq2d opeliunxp2 eqrelrdv ) CFZBGZ
      DECHZABAIZJZVCVEKZLZMZCNVHOVGOZABPVIABVEVFUAUBABVGUCUDVBDIZEIZUEZVCTZVJBT
      ZVKVCVJJZKZTZQZVLVHTVBVMVNVMQVRVBVMVNVBVMVNVMVBVJVATVNVMVJVCUFVAVJVKVCDRZ
      ERZUGCUHUIVABVJUJUKULUMVQVMVNVCVJVKVSVTUNUOSABVFVJVKVPVDVJUPVEVOVCVDVJUQU
      RUSSUT $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
      Operations - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d w x y z A $.  $d w y z B $.  $d w C $.  $d w z D $.
    mpt2mptxf.0 $e |- F/_ x C $.
    mpt2mptxf.1 $e |- F/_ y C $.
    mpt2mptxf.2 $e |- ( z = <. x , y >. -> C = D ) $.
    $( Express a two-argument function as a one-argument function, or
       vice-versa.  In this version ` B ( x ) ` is not assumed to be constant
       w.r.t ` x ` .  (Contributed by Mario Carneiro, 29-Dec-2014.)  (Revised
       by Thierry Arnoux, 31-Mar-2018.) $)
    mpt2mptxf $p |- ( z e. U_ x e. A ( { x } X. B ) |-> C ) =
      ( x e. A , y e. B |-> D ) $=
      ( vw cv wcel wceq wa copab wex nfcv nfeq eqtr4i csn cxp ciun cmpt2 df-mpt
      cmpt coprab df-mpt2 eliunxp anbi1i 19.41 exbii bitri anass eqeq2d pm5.32i
      cop anbi2d 2exbii 3bitr2i opabbii dfoprab2 ) CADALZUAEUBUCZFUFCLZVDMZKLZF
      NZOZCKPZABDEGUDZCKVDFUEVKVCDMBLZEMOZVGGNZOZABKUGZVJABKDEGUHVJVEVCVLUQNZVO
      OZBQAQZCKPVPVIVSCKVIVQVMOZBQZAQZVHOZVTVHOZBQZAQZVSVFWBVHABDEVEUIUJWFWAVHO
      ZAQWCWEWGAVTVHBBVGFBVGRISUKULWAVHAAVGFAVGRHSUKUMWDVRABWDVQVMVHOZOVRVQVMVH
      UNVQWHVOVQVHVNVMVQFGVGJUOURUPUMUSUTVAVOABKCVBTTT $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
         Isomorphisms - misc. add.
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Two ways to write a strictly decreasing function on the reals.
     (Contributed by Thierry Arnoux, 6-Apr-2017.) $)
  gtiso $p |- ( ( A C_ RR* /\ B C_ RR* ) ->
    ( F Isom < , `' < ( A , B ) <-> F Isom <_ , `' <_ ( A , B ) ) ) $=
    ( cxr wss clt ccnv wiso cle cxp cin cdif eqid wceq df-le wrel dfrel2 ineq1i
    wb mpbi isocnv3 a1i cnveqi cnvdif cnvxp ltrel difeq12i 3eqtri indif1 xpss12
    wa eqtri anidms dfss1 sylib difeq1d syl5req adantr isoeq2 syl adantl isoeq3
    3bitrd isocnv2 isores2 isores1 bitri lerel ax-mp 3bitr3ri syl6bbr ) ADEZBDE
    ZUKZABFFGZCHZABIGZAAJZKZIBBJZKZCHZABIVQCHZVNVPABVRFLZVTVOLZCHZABVSWECHZWBVP
    WFSVNABWDWEFVOCWDMWEMUAUBVNWDVSNZWFWGSVLWHVMVLVSDDJZVRKZFLZWDVSWIFLZVRKWKVQ
    WLVRVQWIVOLZGWIGZVOGZLWLIWMOUCWIVOUDWNWIWOFDDUEFPWOFNUFFQTUGUHRWIVRFUIULVLW
    JVRFVLVRWIEZWJVRNVLWPADADUJUMVRWIUNUOUPUQURABWDWEVSCUSUTVNWEWANZWGWBSVMWQVL
    VMWAWIVTKZVOLZWEWAWMVTKWSIWMVTORWIVTVOUIULVMWRVTVOVMVTWIEZWRVTNVMWTBDBDUJUM
    VTWIUNUOUPUQVAABVSWEWACVBUTVCABVQICHZABVQGZVQCHZWBWCABVQICVDXAABVQWACHWBABV
    QICVEABVQWACVFVGXBINZXCWCSIPXDVHIQTABXBVQICUSVIVJVK $.

  ${
    $d x y A $.  $d w x y z B $.  $d x y C $.  $d w x y z D $.  $d w x y z G $.
    $d w x y z H $.  $d x y R $.  $d w x y z S $.  $d w x y z ph $.
    isoun.1 $e |- ( ph -> H Isom R , S ( A , B ) ) $.
    isoun.2 $e |- ( ph -> G Isom R , S ( C , D ) ) $.
    isoun.3 $e |- ( ( ph /\ x e. A /\ y e. C ) -> x R y ) $.
    isoun.4 $e |- ( ( ph /\ z e. B /\ w e. D ) -> z S w ) $.
    isoun.5 $e |- ( ( ph /\ x e. C /\ y e. A ) -> -. x R y ) $.
    isoun.6 $e |- ( ( ph /\ z e. D /\ w e. B ) -> -. z S w ) $.
    isoun.7 $e |- ( ph -> ( A i^i C ) = (/) ) $.
    isoun.8 $e |- ( ph -> ( B i^i D ) = (/) ) $.
    $( Infer an isomorphism from for a union of two isomorphisms.  (Contributed
       by Thierry Arnoux, 30-Mar-2017.) $)
    isoun $p |- ( ph -> ( H u. G ) Isom R , S ( ( A u. C ) , ( B u. D ) ) ) $=
      ( cun wf1o cv wbr cfv wb wral wiso cin c0 wceq isof1o f1oun syl22anc wcel
      syl wa wo elun isorel sylan wfn f1ofn adantr anim1i fvun1 syl3anc adantrr
      wi adantrl breq12d bitr4d anassrs 3expb 3expia ralrimiv ralrimiva wf f1of
      ffvelrnda breq1 breq2 rspc2v syl2anc fvun2 3brtr4d 2thd jaodan sylan2b ex
      mpd wn notbid mtbird 2falsed df-isom sylanbrc ) AFHUBZGIUBZMLUBZUCZBUDZCU
      DZJUEZXCXAUFZXDXAUFZKUEZUGZCWSUHZBWSUHWSWTJKXAUIAFGMUCZHILUCZFHUJUKULZGIU
      JUKULXBAFGJKMUIZXKNFGJKMUMUQZAHIJKLUIZXLOHIJKLUMUQZTUAFGHIMLUNUOAXJBWSAXC
      WSUPZURXICWSXRAXCFUPZXCHUPZUSXDWSUPZXIVJZXCFHUTAXSYBXTAXSURZYAXIYAYCXDFUP
      ZXDHUPZUSZXIXDFHUTZYCYDXIYEAXSYDXIAXSYDURZURZXEXCMUFZXDMUFZKUEZXHAXNYHXEY
      LUGNFGXCXDJKMVAVBYIXFYJXGYKKAXSXFYJULZYDYCMFVCZLHVCZXMXSURYMAYNXSAXKYNXOF
      GMVDUQZVEAYOXSAXLYOXQHILVDUQZVEAXMXSTVFFHMLXCVGVHZVIAYDXGYKULZXSAYDURYNYO
      XMYDURYSAYNYDYPVEAYOYDYQVEAXMYDTVFFHMLXDVGVHZVKVLVMVNAXSYEXIAXSYEURZURZXE
      XHAXSYEXEPVOUUBYJXDLUFZXFXGKUUBDUDZEUDZKUEZEIUHZDGUHZYJUUCKUEZAUUHUUAAUUG
      DGAUUDGUPZURUUFEIAUUJUUEIUPUUFQVPVQVRVEUUBYJGUPZUUCIUPZUUHUUIVJAXSUUKYEAF
      GXCMAXKFGMVSXOFGMVTUQZWAVIAYEUULXSAHIXDLAXLHILVSXQHILVTUQZWAVKUUFUUIYJUUE
      KUEDEYJUUCGIUUDYJUUEKWBUUEUUCYJKWCWDWEWLAXSYMYEYRVIAYEXGUUCULZXSAYEURYNYO
      XMYEURUUOAYNYEYPVEAYOYEYQVEAXMYETVFFHMLXDWFVHZVKWGWHVNWIWJWKAXTURZYAXIYAU
      UQYFXIYGUUQYDXIYEAXTYDXIAXTYDURZURZXEXHAXTYDXEWMRVOUUSXHXCLUFZYKKUEZUUSUU
      FWMZEGUHZDIUHZUVAWMZAUVDUURAUVCDIAUUDIUPZURUVBEGAUVFUUEGUPUVBSVPVQVRVEUUS
      UUTIUPZYKGUPZUVDUVEVJAXTUVGYDAHIXCLUUNWAVIAYDUVHXTAFGXDMUUMWAVKUVBUVEUUTU
      UEKUEZWMDEUUTYKIGUUDUUTULUUFUVIUUDUUTUUEKWBWNUUEYKULUVIUVAUUEYKUUTKWCWNWD
      WEWLUUSXFUUTXGYKKAXTXFUUTULZYDUUQYNYOXMXTURUVJAYNXTYPVEAYOXTYQVEAXMXTTVFF
      HMLXCWFVHZVIAYDYSXTYTVKVLWOWPVNAXTYEXIAXTYEURZURZXEUUTUUCKUEZXHAXPUVLXEUV
      NUGOHIXCXDJKLVAVBUVMXFUUTXGUUCKAXTUVJYEUVKVIAYEUUOXTUUPVKVLVMVNWIWJWKWIWJ
      VQVRBCWSWTJKXAWQWR $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
         Disjointness (additional proof requiring functions)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d i j x $.  $d i j A $.  $d i j B $.  $d x V $.  $d i j ph $.
    disjdsct.0 $e |- F/ x ph $.
    disjdsct.1 $e |- F/_ x A $.
    disjdsct.2 $e |- ( ( ph /\ x e. A ) -> B e. ( V \ { (/) } ) ) $.
    disjdsct.3 $e |- ( ph -> Disj_ x e. A B ) $.
    $( A disjoint collection is distinct, i.e. each set in this collection is
       different of all others, provided that it does not contain the empty set
       This can be expressed as "the converse of the mapping function is a
       function", or "the mapping function is single-rooted".  (Cf. ~ funcnv )
       (Contributed by Thierry Arnoux, 28-Feb-2017.) $)
    disjdsct $p |- ( ph -> Fun `' ( x e. A |-> B ) ) $=
      ( vi vj cv wceq csb wne wral wcel wa c0 wsb cmpt ccnv wfun wdisj disjorsf
      wo cin sylib r19.21bi w3a simpr3 csn cdif eldifsni syl sbimi sbf clelsb3f
      sban anbi12i bitri wsbc sbsbc sbcne12 csb0 neeq2i 3imtr3i 3ad2antr1 disj3
      3bitri biimpi neeq1d biimpa difneqnul 3anassrs ex orim2d ralrimiva nfmpt1
      syl2anc mpd eqid funcnv4mpt mpbird ) ABCDUAZUBUCJLZKLZMZBWFDNZBWGDNZOZUFZ
      KCPZJCPAWMJCAWFCQZRZWLKCWOWGCQZRZWHWIWJUGSMZUFZWLWOWSKCAWSKCPZJCABCDUDWTJ
      CPIBCDJKGUEUHUIUIWQWRWKWHWQWRWKAWNWPWRWKAWNWPWRUJRWRWISOZWKAWNWPWRUKAWPWN
      XAWRABLCQZRZBJTZDSOZBJTZWOXAXCXEBJXCDESULUMZQXEHDESUNUOUPXDABJTZXBBJTZRWO
      AXBBJUSXHAXIWNABJFUQJBCGURUTVAXFXEBWFVBWIBWFSNZOXAXEBJVCBWFDSVDXJSWIBWFVE
      VFVJVGVHWRXARWIWJUMZSOZWKWRXAXLWRWIXKSWRWIXKMWIWJVIVKVLVMWIWJVNUOVTVOVPVQ
      WAVRVRABCDJKWEXGFGBCDVSWEWBHWCWD $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
         First and second members of an ordered pair - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y z A $.  $d x y z B $.
    $( Definition for a restriction of the ` 1st ` (first member of an ordered
       pair) function.  (Contributed by Thierry Arnoux, 27-Sep-2017.) $)
    df1stres $p |- ( 1st |` ( A X. B ) ) = ( x e. A , y e. B |-> x ) $=
      ( vz c1st cxp cres cv wcel wa wceq coprab cvv df1st2 reseq1i resoprab cin
      cmpt2 resres incom xpss df-ss mpbi eqtr3i reseq2i 3eqtr3ri df-mpt2 eqtr4i
      wss eqtri ) FCDGZHZAIZCJBIDJKEIUNLZKABEMZABCDUNSUOABEMZULHFNNGZHZULHZUPUM
      UQUSULABEOPUOABECDQUTFURULRZHUMFURULTVAULFULURRZVAULULURUAULURUJVBULLCDUB
      ULURUCUDUEUFUKUGABECDUNUHUI $.

    $( Definition for a restriction of the ` 2nd ` (second member of an ordered
       pair) function.  (Contributed by Thierry Arnoux, 27-Sep-2017.) $)
    df2ndres $p |- ( 2nd |` ( A X. B ) ) = ( x e. A , y e. B |-> y ) $=
      ( vz c2nd cxp cres cv wcel wa wceq coprab cvv df2nd2 reseq1i resoprab cin
      cmpt2 resres incom xpss df-ss mpbi eqtr3i reseq2i 3eqtr3ri df-mpt2 eqtr4i
      wss eqtri ) FCDGZHZAICJBIZDJKEIUNLZKABEMZABCDUNSUOABEMZULHFNNGZHZULHZUPUM
      UQUSULABEOPUOABECDQUTFURULRZHUMFURULTVAULFULURRZVAULULURUAULURUJVBULLCDUB
      ULURUCUDUEUFUKUGABECDUNUHUI $.
  $}

  $( Value of the first-member function at non-pairs.  (Contributed by Thierry
     Arnoux, 22-Sep-2017.) $)
  1stnpr $p |- ( -. A e. ( _V X. _V ) -> ( 1st ` A ) = (/) ) $=
    ( cvv cxp wcel wn c1st cfv csn cdm cuni c0 1stval wne dmsnn0 biimpri unieqd
    necon1bi uni0 syl6eq syl5eq ) ABBCDZEZAFGAHIZJZKALUBUDKJKUBUCKUAUCKUAUCKMAN
    OQPRST $.

  $( Value of the second-member function at non-pairs.  (Contributed by Thierry
     Arnoux, 22-Sep-2017.) $)
  2ndnpr $p |- ( -. A e. ( _V X. _V ) -> ( 2nd ` A ) = (/) ) $=
    ( cvv cxp wcel wn c2nd cfv csn crn cuni c0 2ndval wne rnsnn0 biimpri unieqd
    necon1bi uni0 syl6eq syl5eq ) ABBCDZEZAFGAHIZJZKALUBUDKJKUBUCKUAUCKUAUCKMAN
    OQPRST $.

  ${
    $d w A $.  $d x y w B $.  $d x y w C $.
    $( TODO shorten like in proof for ~ 1stmbfm ! $)
    $( The preimage by ` 1st ` is a 'vertical band'.  (Contributed by Thierry
       Arnoux, 13-Oct-2017.) $)
    1stpreima $p |- ( A C_ B ->
      ( `' ( 1st |` ( B X. C ) ) " A ) = ( A X. C ) ) $=
      ( vw wss c1st cxp cres ccnv cima cv cfv wcel wa cvv a1i an12 anbi2i elxp7
      wb c2nd anass pm4.71d anbi1d 3bitr4d syl6rbbr syl6bb cin cnvresima eleq2i
      ssel elin vex wfo fo1st fofn elpreima mpbiran anbi1i 3bitri 3bitr4g eqrdv
      wfn mp2b ) ABEZDFBCGZHIAJZACGZVEDKZFLZAMZVIVFMZNZVIOOGMZVKVIUALCMZNNZVIVG
      MZVIVHMVEVMVKVNVONZNZVPVEVSVKVNVJBMZVONNZNZVMVEVKVTNZVRNZVKVTVRNZNZVSWBWD
      WFTVEVKVTVRUBPVEVKWCVRVEVKVTABVJUKUCUDWBWFTVEWAWEVKVNVTVOQRPUEVLWAVKVIBCS
      RUFVKVNVOQUGVQVIFIAJZVFUHZMVIWGMZVLNVMVGWHVIVFAFUIUJVIWGVFULWIVKVLWIVIOMZ
      VKDUMOOFUNFOVCWIWJVKNTUOOOFUPOVIAFUQVDURUSUTVIACSVAVB $.

    $( The preimage by ` 2nd ` is an 'horizontal band'.  (Contributed by
       Thierry Arnoux, 13-Oct-2017.) $)
    2ndpreima $p |- ( A C_ C ->
      ( `' ( 2nd |` ( B X. C ) ) " A ) = ( B X. A ) ) $=
      ( vw wss c2nd cxp cres ccnv cima cv cfv wcel wa cvv wb anass anbi1i elxp7
      a1i c1st ssel pm4.71rd anbi2d bicomi syl6rbbr ancom 3bitr3g cin cnvresima
      3bitrd eleq2i elin vex wfo wfn fo2nd fofn elpreima mpbiran 3bitri 3bitr4g
      mp2b eqrdv ) ACEZDFBCGZHIAJZBAGZVEDKZFLZAMZVIVFMZNZVIOOGMZVIUALBMZVKNNZVI
      VGMZVIVHMVEVLVKNZVNVONZVKNZVMVPVEVTVNVOVJCMZNNZVKNZVRVEVTVSWAVKNZNZVSWANZ
      VKNZWCVEVKWDVSVEVKWAACVJUBUCUDWEWGPVEWGWEVSWAVKQUETWGWCPVEWFWBVKVNVOWAQRT
      UKVLWBVKVIBCSRUFVLVKUGVNVOVKQUHVQVIFIAJZVFUIZMVIWHMZVLNVMVGWIVIVFAFUJULVI
      WHVFUMWJVKVLWJVIOMZVKDUNOOFUOFOUPWJWKVKNPUQOOFUROVIAFUSVCUTRVAVIBASVBVD
      $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.  $d x y F $.
    $d x y G $.
    curry2ima.1 $e |- G = ( F o. `' ( 1st |` ( _V X. { C } ) ) ) $.
    $( The image of a curried function with a constant second argument.
       (Contributed by Thierry Arnoux, 25-Sep-2017.) $)
    curry2ima $p |- ( ( F Fn ( A X. B ) /\ C e. B /\ D C_ A ) ->
        ( G " D ) = { y | E. x e. D y = ( x F C ) } ) $=
      ( cxp wfn wss cv wceq wrex cab cvv wf syl2anc syl wcel w3a cima cfv simp1
      co wfun cdm dffn2 sylib simp2 curry2f ffun fdm sseqtr4d dfimafn curry2val
      simp3 3adant3 eqeq1d eqcom syl6bb rexbidv abbidv eqtrd ) GCDJZKZEDUAZFCLZ
      UBZHFUCZAMZHUDZBMZNZAFOZBPZVNVLEGUFZNZAFOZBPVJHUGZFHUHZLVKVQNVJCQHRZWAVJV
      FQGRZVHWCVJVGWDVGVHVIUEVFGUIUJVGVHVIUKCDEQGHIULSZCQHUMTVJFCWBVGVHVIURVJWC
      WBCNWECQHUNTUOABFHUPSVJVPVTBVJVOVSAFVJVOVRVNNVSVJVMVRVNVGVHVMVRNVICDEVLGH
      IUQUSUTVRVNVAVBVCVDVE $.
  $}

$(
  @{
    coswap.1 @e |- ( ( x = ( 1st ` p ) /\ y = ( 2nd ` p ) ) -> ( ps <-> ch ) ) @.
    coswap.2 @e |- ( ( x = ( 2nd ` p ) /\ y = ( 1st ` p ) ) -> ( ps <-> th ) ) @.
    coswap.3 @e |- ( ( ph /\ p e. A ) -> ch ) @.
    @( A scheme that can be used for swapping ` 1st ` and ` 2nd ` arguments
       in a proof. @)
    coswap @p |- ( ( ph /\ p e. `' A ) -> th ) @=
      ? @.
  @}
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
           Supremum - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z R $.  $d z ph $.
    supssd.0 $e |- ( ph -> R Or A ) $.
    supssd.1 $e |- ( ph -> B C_ C ) $.
    supssd.2 $e |- ( ph -> C C_ A ) $.
    supssd.3 $e |- ( ph -> E. x e. A ( A. y e. B -. x R y
                               /\ A. y e. A ( y R x -> E. z e. B y R z ) ) ) $.
    supssd.4 $e |- ( ph -> E. x e. A ( A. y e. C -. x R y
                               /\ A. y e. A ( y R x -> E. z e. C y R z ) ) ) $.
    $( Inequality deduction for supremum of a subset.  (Contributed by Thierry
       Arnoux, 21-Mar-2017.) $)
    supssd $p |- ( ph -> -. sup ( C , A , R ) R sup ( B , A , R ) ) $=
      ( csup wcel cv wbr wn wral supcl sseld supub syld ralrimiv supnub mp2and
      ) AGEHNZEOUGDPZHQRZDFSUGFEHNHQRABCDEGHIMTAUIDFAUHFOUHGOUIAFGUHJUAABCDEGUH
      HIMUBUCUDABCDEFUGHILUEUF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Countable Sets
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( ` NN ` is countable (Contributed by Thierry Arnoux, 29-Dec-2016.) $)
  nnct $p |- NN ~<_ om $=
    ( cn com cen wbr cdom nnenom endom ax-mp ) ABCDABEDFABGH $.

  $( A finite set is countable (weaker version of ~ isfinite ) (Contributed by
     Thierry Arnoux, 27-Mar-2018.) $)
  fict $p |- ( A e. Fin -> A ~<_ om ) $=
    ( cfn wcel com csdm wbr cdom isfinite sdomdom sylbi ) ABCADEFADGFAHADIJ $.

  ${
    $d f A $.
    $( TODO shorten using ` Rel ~<_ ` and ~ brrelexi ? $)
    $( A countable set is a set (Contributed by Thierry Arnoux,
       29-Dec-2016.) $)
    ctex $p  |- ( A ~<_ om -> A e. _V ) $=
      ( vf com cdom wbr wf1 wex cvv wcel brdomi cdm f1dm dmex syl6eqelr exlimiv
      cv vex syl ) ACDEACBPZFZBGAHIZACBJTUABTASKHACSLSBQMNOR $.
  $}

  $( Any subset of a countable set is countable (Contributed by Thierry Arnoux,
     31-Jan-2017.) $)
  ssct $p |- ( ( A C_ B /\ B ~<_ om ) -> A ~<_ om ) $=
    ( wss com cdom wbr cvv wcel wi ctex ssdomg syl impcom domtr sylancom ) ABCZ
    BDEFZABEFZADEFQPRQBGHPRIBJABGKLMABDNO $.

  $( The cartesian product of two countable sets is countable.  (Contributed by
     Thierry Arnoux, 24-Sep-2017.) $)
  xpct $p |- ( ( A ~<_ om /\ B ~<_ om ) -> ( A X. B ) ~<_ om ) $=
    ( com cdom wbr wa cxp cen cvv wcel ctex adantl simpl xpdom1g syl2anc xpdom2
    omex domtr xpomen domentr sylancl ) ACDEZBCDEZFZABGZCCGZDEZUFCHEUECDEUDUECB
    GZDEZUHUFDEZUGUDBIJZUBUIUCUKUBBKLUBUCMACBINOUCUJUBBCCQPLUEUHUFROSUEUFCTUA
    $.

  $( A singleton is countable (Contributed by Thierry Arnoux, 16-Sep-2016.) $)
  snct $p |- ( A e. V -> { A } ~<_ om ) $=
    ( wcel csn c1o cen wbr com cdom ensn1g c0 csdm peano1 ne0i ax-mp omex 0sdom
    wne mpbir 0sdom1dom mpbi endomtr sylancl ) ABCADZEFGEHIGZUDHIGABJKHLGZUEUFH
    KRZKHCUGMHKNOHPQSHTUAUDEHUBUC $.

  $( An unordered pair is countable (Contributed by Thierry Arnoux,
     16-Sep-2016.) $)
  prct $p |- ( ( A e. V /\ B e. W ) -> { A , B } ~<_ om ) $=
    ( wcel wa cpr csn cun com cdom df-pr wbr snct unctb syl2an syl5eqbr ) ACEZB
    DEZFABGAHZBHZIZJKABLRTJKMUAJKMUBJKMSACNBDNTUAOPQ $.

  $( If the domain of a function is countable, the function is countable.
     (Contributed by Thierry Arnoux, 29-Dec-2016.) $)
  fnct $p |- ( ( F Fn A /\ A ~<_ om ) -> F ~<_ om ) $=
    ( wfn com cdom wbr crn cxp cvv wcel wss ctex adantl cdm adantr sylc syl2anc
    wa sylancom domtr wfun wb fndm eleq1d fnfun funrnex xpexg simpl dffn3 sylib
    mpbird wf fssxp syl ssdomg cen xpdom1g omex fnrndomg xpdom2g sylancr xpomen
    domentr sylancl ) BACZADEFZRZBABGZHZEFZVIDEFZBDEFVGVIIJZBVIKZVJVGAIJZVHIJZV
    LVFVNVEALMZVGBNZIJZBUAZVOVGVRVNVPVEVRVNUBVFVEVQAIABUCUDOUKVEVSVFABUEOIBUFPZ
    AVHIIUGQVGAVHBULZVMVGVEWAVEVFUHZABUIUJAVHBUMUNBVIIUOPVGVIDDHZEFZWCDUPFVKVGV
    IDVHHZEFZWEWCEFZWDVEVFVOWFVTADVHIUQSVGDIJVHDEFZWGURVEVFVHAEFZWHVGVNVEWIVPWB
    AIBUSPVHADTSVHDDIUTVAVIWEWCTQVBVIWCDVCVDBVIDTQ $.

  ${
    $d x A $.
    $( The domain of a countable set is countable.  (Contributed by Thierry
       Arnoux, 29-Dec-2016.) $)
    dmct $p |- ( A ~<_ om -> dom A ~<_ om ) $=
      ( vx com cdom wbr cdm cvv cres dmresv wcel cv c1st cfv cmpt wfo wss resss
      ctex ee10 domtr ssexg sylancr crn wfn fvex eqid fnmpti dffn4 mpbi wrel wb
      wceq relres reldm foeq3 mpbir fodomg ssdomg mpancom syl2anc syl5eqbrr
      mp2b ) ACDEZAFAGHZFZCDAIVCVEVDDEZVDCDEZVECDEVCVDGJZVDVEBVDBKZLMZNZOZVFVCV
      DAPZAGJZVHAGQZARZVDAGUAUBVLVDVKUCZVKOZVKVDUDVRBVDVJVKVILUEVKUFUGVDVKUHUIV
      DUJVEVQULVLVRUKAGUMBVDUNVEVQVDVKUOVBUPVDVEGVKUQSVDADEZVCVGVCVNVMVSVPVOVDA
      GURSVDACTUSVEVDCTUTVA $.
  $}

  $( If a set is countable, so is its converse.  (Contributed by Thierry
     Arnoux, 29-Dec-2016.) $)
  cnvct $p |- ( A ~<_ om -> `' A ~<_ om ) $=
    ( ccnv cdom wbr com cen wrel cvv wcel relcnv ctex cnvexg syl cnven cnvcnvss
    sylancr wss ssdomg ee10 endomtr syl2anc domtr mpancom ) ABZACDZAECDZUDECDUF
    UDUDBZFDZUGACDZUEUFUDGUDHIZUHAJUFAHIZUJAKZAHLMUDHNPUFUKUGAQUIULAOUGAHRSUDUG
    ATUAUDAEUBUC $.

  $( The range of a countable set is countable.  (Contributed by Thierry
     Arnoux, 29-Dec-2016.) $)
  rnct $p |- ( A ~<_ om -> ran A ~<_ om ) $=
    ( com cdom wbr ccnv cdm crn cnvct dmct df-rn breq1i biimpri 3syl ) ABCDAEZB
    CDNFZBCDZAGZBCDZAHNIRPQOBCAJKLM $.

  $( The image by a function of a countable set is countable. (Contributed by
     Thierry Arnoux, 27-Mar-2018.) $)
  fimact $p |- ( ( A ~<_ om /\ Fun F ) -> ( F " A ) ~<_ om ) $=
    ( com cdom wbr wfun wa cima cvv wcel ctex imadomg sylan simpl domtr syl2anc
    imp ) ACDEZBFZGBAHZADEZRTCDERAIJZSUAAKUBSUAAIBLQMRSNTACOP $.

  ${
    $d x y A $.  $d y B $.
    $( A countable mapping set is countable.  (Contributed by Thierry Arnoux,
       29-Dec-2016.) $)
    mptct $p |- ( A ~<_ om -> ( x e. A |-> B ) ~<_ om ) $=
      ( com cdom wbr cmpt wfun cdm funmpt cvv wcel wss ctex eqid dmmptss ssdomg
      ee10 domtr mpancom wfn funfn fnct sylanb sylancr ) BDEFZABCGZHZUGIZDEFZUG
      DEFZABCJUIBEFZUFUJUFBKLUIBMULBNABCUGUGOPUIBKQRUIBDSTUHUGUIUAUJUKUGUBUIUGU
      CUDUE $.

    ${
      $d z A $.  $d x z B $.  $d z C $.
      mpt2cti.1 $e |- A. x e. A A. y e. B C e. V $.
      $( An operation is countable if both its domains are countable.
         (Contributed by Thierry Arnoux, 17-Sep-2017.) $)
      mpt2cti $p |- ( ( A ~<_ om /\ B ~<_ om ) ->
                                          ( x e. A , y e. B |-> C ) ~<_ om ) $=
        ( com cdom wbr wa cmpt2 cxp wfn wcel wral eqid fnmpt2 ax-mp xpct fnct
        sylancr ) CHIJDHIJKABCDELZCDMZNZUDHIJUCHIJEFOBDPACPUEGABCDEUCFUCQRSCDTU
        DUCUAUB $.
    $}

    $( An image set of a countable set is countable.  (Contributed by Thierry
       Arnoux, 29-Dec-2016.) $)
    abrexct $p |- ( A ~<_ om -> { y | E. x e. A y = B } ~<_ om ) $=
      ( com cdom wbr cv wceq wrex cab cmpt crn eqid rnmpt 1stcrestlem syl5eqbrr
      ) CEFGBHDIACJBKACDLZMEFABCDRRNOACDPQ $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.
    mptctf.1 $e |- F/_ x A $.
    $( A countable mapping set is countable, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by Thierry
       Arnoux, 8-Mar-2017.) $)
    mptctf $p |- ( A ~<_ om -> ( x e. A |-> B ) ~<_ om ) $=
      ( com cdom wbr cmpt wfun cdm funmpt cvv wcel wss ctex crab eqid dmmpt cab
      eqsstri cv wa df-rab simpl ss2abi abid2f sseqtri ssdomg domtr mpancom wfn
      ee10 funfn fnct sylanb sylancr ) BEFGZABCHZIZURJZEFGZUREFGZABCKUTBFGZUQVA
      UQBLMUTBNVCBOUTCLMZABPZBABCURURQRVEAUABMZVDUBZASZBVDABUCVHVFASBVGVFAVFVDU
      DUEABDUFUGTTUTBLUHULUTBEUIUJUSURUTUKVAVBURUMUTURUNUOUP $.

    $( An image set of a countable set is countable, using bound-variable
       hypotheses instead of distinct variable conditions.  (Contributed by
       Thierry Arnoux, 8-Mar-2017.) $)
    abrexctf $p |- ( A ~<_ om -> { y | E. x e. A y = B } ~<_ om ) $=
      ( com cdom wbr cv wceq wrex cab cmpt crn eqid rnmpt mptctf rnct syl5eqbrr
      syl ) CFGHZBIDJACKBLACDMZNZFGABCDUBUBOPUAUBFGHUCFGHACDEQUBRTS $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Real and Complex Numbers
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
                      Complex addition - misc. additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Two complex which add up to zero are each other's negatives.  (Contributed
     by Thierry Arnoux, 2-May-2017.) $)
  addeq0 $p |- ( ( A e. CC /\ B e. CC ) -> ( ( A + B ) = 0 <-> A = -u B ) ) $=
    ( cneg wceq cc0 cmin co cc wcel wa caddc df-neg eqeq1i eqcom bitr3i 0cn a1i
    simpr simpl subadd2d syl5rbbr ) ABCZDZEBFGZADZAHIZBHIZJZABKGEDUEUBADUCUBUDA
    BLMUBANOUHEBAEHIUHPQUFUGRUFUGSTUA $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
        Ordering on reals - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d b c A $.  $d b c B $.  $d b c C $.
    lt2addrd.1 $e |- ( ph -> A e. RR ) $.
    lt2addrd.2 $e |- ( ph -> B e. RR ) $.
    lt2addrd.3 $e |- ( ph -> C e. RR ) $.
    lt2addrd.4 $e |- ( ph -> A < ( B + C ) ) $.
    $( If the right-side of a 'less-than' relationship is an addition, then we
       can express the left-side as an addition, too, where each term is
       respectively less than each term of the original right side.
       (Contributed by Thierry Arnoux, 15-Mar-2017.) $)
    lt2addrd $p |- ( ph -> E. b e. RR E. c e. RR
      ( A = ( b + c ) /\ b < B /\ c < C ) ) $=
      ( caddc co cmin cr wcel wceq clt wbr w3a resubcld cdiv readdcld rehalfcld
      c2 cv wrex recnd addcld subcld halfcld subsub4d oveq2d subadd23d 2halvesd
      cc eqeltrd addsubassd 3eqtr4d nncand 3eqtrrd crp wb difrp mpbid rphalfcld
      syl2anc ltsubrpd oveq1 eqeq2d breq1 3anbi12d 3anbi13d rspc2ev syl113anc
      oveq2 ) ACCDKLZBMLZUDUALZMLZNODVRMLZNOBVSVTKLZPZVSCQRZVTDQRZBEUEZFUEZKLZP
      ZWECQRZWFDQRZSZFNUFENUFACVRHAVQAVPBACDHIUBZGTUCZTADVRIWMTAWAVPVRVRKLZMLZV
      PVQMLBACVTVRMLZKLCDWNMLZKLWAWOAWPWQCKADVRVRADIUGZAVQAVPBACDACHUGZWRUHZABG
      UGZUIZUJZXCUKULACVRVTWSXCADVRWRXCUIUMACDWNWSWRAWNVQUOAVQXBUNZXBUPUQURAWNV
      QVPMXDULAVPBWTXAUSUTACVRHAVQABVPQRZVQVAOZJABNOVPNOXEXFVBGWLBVPVCVFVDVEZVG
      ADVRIXGVGWKWBWCWDSBVSWFKLZPZWCWJSEFVSVTNNWEVSPZWHXIWIWCWJXJWGXHBWEVSWFKVH
      VIWEVSCQVJVKWFVTPZXIWBWJWDWCXKXHWABWFVTVSKVOVIWFVTDQVJVLVMVN $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Extended reals - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( An extended real which is greater than plus infinity is plus infinity.
     (Contributed by Thierry Arnoux, 18-Dec-2016.) $)
  xgepnf $p |- ( A e. RR* -> ( +oo <_ A <-> A = +oo ) ) $=
    ( cxr wcel cpnf cle wbr clt wn wceq wb pnfxr xrlenlt mpan nltpnft bitr4d )
    ABCZDAEFZADGFHZADIDBCPQRJKDALMANO $.

  $( An extended real which is less than minus infinity is minus infinity.
     (Contributed by Thierry Arnoux, 18-Feb-2018.) $)
  xlemnf $p |- ( A e. RR* -> ( A <_ -oo <-> A = -oo ) ) $=
    ( cxr wcel cmnf cle wbr clt wn wceq wb mnfxr xrlenlt mpan2 ngtmnft bitr4d )
    ABCZADEFZDAGFHZADIPDBCQRJKADLMANO $.

  $( Trichotomy law for extended reals.  (Contributed by Thierry Arnoux,
     12-Sep-2017.) $)
  xrlelttric $p |- ( ( A e. RR* /\ B e. RR* ) -> ( A <_ B \/ B < A ) ) $=
    ( cxr wcel wa cle wbr clt wo wn pm2.1 xrlenlt orbi1d mpbiri ) ACDBCDEZABFGZ
    BAHGZIQJZQIQKOPRQABLMN $.

  $( Two extended reals which add up to zero are each other's negatives.
     (Contributed by Thierry Arnoux, 13-Jun-2017.) $)
  xaddeq0 $p |-
    ( ( A e. RR* /\ B e. RR* ) -> ( ( A +e B ) = 0 <-> A = -e B ) ) $=
    ( cxr wcel wa cxad cc0 wceq cxne cpnf cmnf syl simplr syl2anc oveq1d eqtr3d
    co simpr ex wne cr w3o wi elxr simpll rexrd xnegneg xnegcld xaddid2 xaddcom
    xpncan ancoms adantr 3eqtr3d xnegeq wn renepnf mp1i eqnetrd neneqd xaddpnf2
    0re con3and nne sylib xnegmnf syl6req eqtrd renemnf xaddmnf2 xnegpnf sylanb
    3jaoian xnegcl ad2antlr xnegid 3eqtrd impbid ) ACDZBCDZEZABFQZGHZABIZHZVSAU
    ADZAJHZAKHZUBVTWCWEUCZAUDWFVTWIWGWHWFVTEZWCWEWJWCEZAIZIZAWDWKVSWMAHWKAWFVTW
    CUEUFZAUGLWKWLBHWMWDHWKGWLFQZWLBWKWLCDWOWLHWKAWNUHWLUILWKWBWLFQBAFQZWLFQZWO
    BWKWBWPWLFWKVSVTWBWPHWNWFVTWCMABUJNOWKWBGWLFWJWCROWJWQBHZWCVTWFWRBAUKULUMUN
    PWLBUOLPSWGVTEZWCWEWSWCEZAJWDWGVTWCUEZWTWDKIZJWTBKHZWDXBHWTBKTZUPZXCWTVTJBF
    QZJHZUPXEWGVTWCMWTXFJWTXFGJWTWBXFGWTAJBFXAOWSWCRPGUADZGJTWTVBGUQURUSUTVTXDX
    GVTXDXGBVASVCNBKVDVEBKUOLVFVGVHSWHVTEZWCWEXIWCEZAKWDWHVTWCUEZXJWDJIZKXJBJHZ
    WDXLHXJBJTZUPZXMXJVTKBFQZKHZUPXOWHVTWCMXJXPKXJXPGKXJWBXPGXJAKBFXKOXIWCRPXHG
    KTXJVBGVIURUSUTVTXNXQVTXNXQBVJSVCNBJVDVEBJUOLVKVGVHSVMVLWAWEWCWAWEEZWBWDBFQ
    ZBWDFQZGXRAWDBFWAWEROXRWDCDZVTXSXTHVTYAVSWEBVNVOVSVTWEMWDBUJNVTXTGHVSWEBVPV
    OVQSVR $.

  ${
    $d y z A $.
    $( The infinimum of a set of extended reals containing minus infnity is
       minus infinity.  (Contributed by Thierry Arnoux, 18-Feb-2018.) $)
    infxrmnf $p |- ( ( A C_ RR* /\ -oo e. A ) -> sup ( A , RR* , `' < ) = -oo )
      $=
      ( cxr wss cmnf wcel wa clt ccnv csup cle wceq infmxrlb wb infmxrcl adantr
      wbr xlemnf syl mpbid ) ABCZDAEZFZABGHIZDJPZUCDKZADLUBUCBEZUDUEMTUFUAANOUC
      QRS $.
  $}

  $( The extended real numbers are unbounded below.  (Contributed by Thierry
     Arnoux, 18-Feb-2018.) $)
  xrinfm $p |- sup ( RR* , RR* , `' < ) = -oo $=
    ( cxr wss cmnf wcel clt ccnv csup wceq ssid mnfxr infxrmnf mp2an ) AABCADAA
    EFGCHAIJAKL $.

  ${
    le2halvesd.1 $e |- ( ph -> A e. RR ) $.
    le2halvesd.2 $e |- ( ph -> B e. RR ) $.
    le2halvesd.3 $e |- ( ph -> C e. RR ) $.
    le2halvesd.4 $e |- ( ph -> A <_ ( C / 2 ) ) $.
    le2halvesd.5 $e |- ( ph -> B <_ ( C / 2 ) ) $.
    $( A sum is less than the whole if each term is less than half.
       (Contributed by Thierry Arnoux, 29-Nov-2017.) $)
    le2halvesd $p |- ( ph -> ( A + B ) <_ C ) $=
      ( caddc co c2 cdiv cle rehalfcld le2addd recnd 2halvesd breqtrd ) ABCJKDL
      MKZTJKDNABCTTEFADGOZUAHIPADADGQRS $.
  $}


  $( A number is less than or equal to itself plus a nonnegative number.
     (Contributed by Thierry Arnoux, 28-Dec-2016.) $)
  xraddge02 $p |- ( ( A e. RR* /\ B e. RR* ) ->
    ( 0 <_ B -> A <_ ( A +e B ) ) ) $=
    ( cxr wcel wa cc0 cle wbr cxad co xrleid adantr simpl jctir xle2add mpancom
    wi 0xr mpand wb xaddid1 breq1d sylibd ) ACDZBCDZEZFBGHZAFIJZABIJZGHZAUIGHZU
    FAAGHZUGUJUDULUEAKLUDFCDZEUFULUGEUJQUFUDUMUDUEMRNAFABOPSUDUJUKTUEUDUHAUIGAU
    AUBLUC $.

  ${
    $d b c A $.  $d b c B $.  $d b c C $.
    xlt2addrd.1 $e |- ( ph -> A e. RR ) $.
    xlt2addrd.2 $e |- ( ph -> B e. RR* ) $.
    xlt2addrd.3 $e |- ( ph -> C e. RR* ) $.
    xlt2addrd.4 $e |- ( ph -> B =/= -oo ) $.
    xlt2addrd.5 $e |- ( ph -> C =/= -oo ) $.
    xlt2addrd.6 $e |- ( ph -> A < ( B +e C ) ) $.
    $( If the right-side of a 'less-than' relationship is an addition, then we
       can express the left-side as an addition, too, where each term is
       respectively less than each term of the original right side.
       (Contributed by Thierry Arnoux, 15-Mar-2017.) $)
    xlt2addrd $p |- ( ph -> E. b e. RR* E. c e. RR*
      ( A = ( b +e c ) /\ b < B /\ c < C ) ) $=
      ( cxad co wceq clt cxr wcel cc0 cr cv wbr w3a wrex cpnf wa rexrd ad2antrr
      0xr a1i xaddid1 eqcomd syl ltpnf simplr breqtrrd ax-mp simpr oveq1 eqeq2d
      0re breq1 3anbi12d oveq2 3anbi13d rspc2ev syl113anc wne c1 cxne 1re rexri
      xnegcld xaddcld cmnf renemnfd cneg cmin wo xrnepnf biimpi sylancom orcomd
      neneqd pm2.53 sylc rexsub sylancl resubcl eqeltrd rexneg renegcld xaddass
      wn syl222anc xaddcom syl2anc xnegid eqtrd oveq2d 3eqtrrd resubcld 3brtr4d
      ltm1d eqbrtrd pm2.61dane caddc rexadd breqtrd lt2addrd 3anbi1d sylibr wss
      2rexbiia wi ressxr ssrexv reximi 3syl ) ABEUAZFUAZMNZOZXTCPUBZYADPUBZUCZF
      QUDZEQUDZCUEACUEOZUFZYHDUEYJDUEOZUFZBQRZSQRZBBSMNZOZBCPUBZSDPUBZYHAYMYIYK
      ABGUGZUHZYNYLUIUJYLYMYPYTYMYOBBUKZULUMYLBUECPYLBTRZBUEPUBAUUBYIYKGUHBUNUM
      AYIYKUOUPYLSUEDPSUEPUBZYLSTRUUCVASUNUQUJYJYKURUPYFYPYQYRUCBBYAMNZOZYQYEUC
      EFBSQQXTBOZYCUUEYDYQYEUUFYBUUDBXTBYAMUSUTXTBCPVBVCYASOZUUEYPYEYRYQUUGUUDY
      OBYASBMVDUTYASDPVBVEVFVGYJDUEVHZUFZBDVIVJZMNZVJZMNZQRUUKQRZBUUMUUKMNZOZUU
      MCPUBZUUKDPUBZYHUUIBUULAYMYIUUHYSUHZUUIUUKUUIDUUJADQRZYIUUHIUHZUUIVIVIQRZ
      UUIVIVKVLZUJVMVNZVMZVNUVDUUIUUOBUULUUKMNZMNZYOBUUIYMBVOVHZUULQRZUULVOVHUU
      NUUKVOVHUUOUVGOUUSUUIBAUUBYIUUHGUHZVPUVEUUIUULUUIUULUUKVQZTUUIUUKTRZUULUV
      KOUUIUUKDVIVRNZTUUIDTRZVITRZUUKUVMOUUIDVOOZUVNVSZUVPWNZUVNUUIUVNUVPYJUUHU
      UTUVNUVPVSZUVAUUTUUHUFUVSDVTWAZWBWCUUIDVOADVOVHZYIUUHKUHWDUVPUVNWEZWFZVKD
      VIWGWHZUUIUVNUVOUVMTRUWCVKDVIWIWHZWJZUUKWKUMUUIUUKUWFWLWJVPUVDUUIUUKUWFVP
      BUULUUKWMWOUUIUVFSBMUUIUVFUUKUULMNZSUUIUVIUUNUVFUWGOUVEUVDUULUUKWPWQUUIUU
      NUWGSOUVDUUKWRUMWSWTUUIYMYOBOZUUSUUAUMXAUUIBUVMVRNZUEUUMCPUUIUWITRUWIUEPU
      BUUIBUVMUVJUWEXBUWIUNUMUUIUUMBUUKVRNZUWIUUIUUBUVLUUMUWJOUVJUWFBUUKWGWQUUI
      UUKUVMBVRUWDWTWSAYIUUHUOXCUUIUUKUVMDPUWDUUIDUWCXDXEYFUUPUUQUURUCBUUMYAMNZ
      OZUUQYEUCEFUUMUUKQQXTUUMOZYCUWLYDUUQYEUWMYBUWKBXTUUMYAMUSUTXTUUMCPVBVCYAU
      UKOZUWLUUPYEUURUUQUWNUWKUUOBYAUUKUUMMVDUTYAUUKDPVBVEVFVGXFACUEVHZUFZYHDUE
      UWPYKUFZCUUJMNZQRZBUWRVJZMNZQRZBUWRUXAMNZOZUWRCPUBZUXADPUBZYHUWQCUUJACQRZ
      UWOYKHUHZUWQVIUVBUWQUVCUJVMVNZUWQBUWTAYMUWOYKYSUHZUWQUWRUXIVMZVNZUWQUXCUX
      AUWRMNZBUWTUWRMNZMNZBUWQUWSUXBUXCUXMOUXIUXLUWRUXAWPWQUWQYMUVHUWTQRZUWTVOV
      HUWSUWRVOVHUXMUXOOUXJUWQBAUUBUWOYKGUHZVPUXKUWQUWTUWQUWTUWRVQZTUWQUWRTRZUW
      TUXROUWQUWRCVIVRNZTUWQCTRZUVOUWRUXTOUWQCVOOZUYAVSZUYBWNZUYAUWQUYAUYBUWQUX
      GUWOUYAUYBVSZUXHAUWOYKUOUXGUWOUFUYECVTWAZWQWCUWQCVOACVOVHZUWOYKJUHWDUYBUY
      AWEZWFZVKCVIWGWHZUWQUYAUVOUXTTRUYIVKCVIWIWHZWJZUWRWKUMUWQUWRUYLWLWJVPUXIU
      WQUWRUYLVPBUWTUWRWMWOUWQUXOYOBUWQUXNSBMUWQUXNUWRUWTMNZSUWQUXPUWSUXNUYMOUX
      KUXIUWTUWRWPWQUWQUWSUYMSOUXIUWRWRUMWSWTUWQYMUWHUXJUUAUMWSXAUWQUWRUXTCPUYJ
      UWQCUYIXDXEUWQBUXTVRNZUEUXADPUWQUYNTRUYNUEPUBUWQBUXTUXQUYKXBUYNUNUMUWQUXA
      BUWRVRNZUYNUWQUUBUXSUXAUYOOUXQUYLBUWRWGWQUWQUWRUXTBVRUYJWTWSUWPYKURXCYFUX
      DUXEUXFUCBUWRYAMNZOZUXEYEUCEFUWRUXAQQXTUWROZYCUYQYDUXEYEUYRYBUYPBXTUWRYAM
      USUTXTUWRCPVBVCYAUXAOZUYQUXDYEUXFUXEUYSUYPUXCBYAUXAUWRMVDUTYAUXADPVBVEVFV
      GUWPUUHUFZYFFTUDZETUDZYGETUDZYHUYTBXTYAXGNZOZYDYEUCZFTUDETUDVUBUYTBCDEFAU
      UBUWOUUHGUHUYTUYCUYDUYAUYTUYAUYBUYTUXGUWOUYEAUXGUWOUUHHUHAUWOUUHUOUYFWQWC
      UYTCVOAUYGUWOUUHJUHWDUYHWFZUYTUVQUVRUVNUYTUVNUVPUWPUUHUUTUVSAUUTUWOUUHIUH
      UVTWBWCUYTDVOAUWAUWOUUHKUHWDUWBWFZUYTBCDMNZCDXGNZPABVUIPUBUWOUUHLUHUYTUYA
      UVNVUIVUJOVUGVUHCDXHWQXIXJYFVUFEFTTXTTRYATRUFZYCVUEYDYEVUKYBVUDBXTYAXHUTX
      KXNXLVUAYGETTQXMZVUAYGXOXPYFFTQXQUQXRVULVUCYHXOXPYGETQXQUQXSXFXF $.
  $}

  ${
    $d x y z B $.  $d x y z C $.  $d z ph $.
    xrsupssd.1 $e |- ( ph -> B C_ C ) $.
    xrsupssd.2 $e |- ( ph -> C C_ RR* ) $.
    $( Inequality deduction for supremum of an extended real subset.
       (Contributed by Thierry Arnoux, 21-Mar-2017.) $)
    xrsupssd $p |- ( ph -> sup ( B , RR* , < ) <_ sup ( C , RR* , < ) ) $=
      ( vx vy vz cxr clt csup wbr wn wss cv wral wrex wi wa xrsupss cle wor a1i
      xrltso sstrd syl supssd wcel wb supcl xrlenlt syl2anc mpbird ) ABIJKZCIJK
      ZUALZUOUNJLMZAFGHIBCJIJUBAUDUCZDEABINFOZGOZJLMZGBPUTUSJLZUTHOJLZHBQRGIPSF
      IQABCIDEUEFGHBTUFZACINVAGCPVBVCHCQRGIPSFIQEFGHCTUFZUGAUNIUHUOIUHUPUQUIAFG
      HIBJURVDUJAFGHICJURVEUJUNUOUKULUM $.
  $}

  ${
    $d a b k u v w x y z X $.  $d a b k u v w x y z Y $.  $d k v w z Z $.
    $d k v w x y z ph $.
    xrofsup.1 $e |- ( ph -> X C_ RR* ) $.
    xrofsup.2 $e |- ( ph -> Y C_ RR* ) $.
    xrofsup.3 $e |- ( ph -> sup ( X , RR* , < ) =/= -oo ) $.
    xrofsup.4 $e |- ( ph -> sup ( Y , RR* , < ) =/= -oo ) $.
    xrofsup.5 $e |- ( ph -> Z = ( +e " ( X X. Y ) ) ) $.
    $( The supremum is preserved by extended addition set operation.  (provided
       minus infinity is not involved as it does not behave well with addition)
       (Contributed by Thierry Arnoux, 20-Mar-2017.) $)
    xrofsup $p |- ( ph -> sup ( Z , RR* , < ) =
      ( sup ( X , RR* , < ) +e sup ( Y , RR* , < ) ) ) $=
      ( vx vy va vb cxr clt cxad wcel wbr wrex wa vz vk vu vv vw wss csup co cv
      cle wral wi wceq cxp cima cfv sseld anim12d imp xaddcl syl ralrimivva cop
      cr fveq2 df-ov syl6eqr eleq1d ralxp sylibr wfun cdm wb xaddf ax-mp xpss12
      wf ffun syl2anc syl6sseqr funimass4 sylancr mpbird eqsstrd supxrcl eleq2d
      fdmi xaddcld pm5.32i nfvd ad2antrr simprl supxrub simprr xle2add syl22anc
      sseldd mp2and fvelima mpan adantl eqeq1d rexxp sylib ancom 2rexbii biimpa
      r19.29d2r breq1 reximi 19.9d2r sylbi ralrimiva w3a simplr simpr xlt2addrd
      cmnf wne nfv nfcv nfre1 nfan id ralrimivw adantr simplll simplr2 supxrlub
      syl21anc simpllr simplr3 reeanv sylanbrc ancoms 3anassrs ex reximdva mpd
      nfrex simplrr simp1d simp-4l simplrl simpld simprd xlt2add biimpar sylan2
      jca32 jca reximia 19.9d2rf elovimad breq2d rspcedv rexlimdvva supxr2 ) AD
      NUFBNOUGZCNOUGZPUHZNQUAUIZUVAUJRZUADUKUVBUVAORZUVBUBUIZORZUBDSZULZUAVDUKD
      NOUGUVAUMADPBCUNZUOZNIAUVJNUFZUCUIZPUPZNQZUCUVIUKZAJUIZKUIZPUHZNQZKCUKJBU
      KUVOAUVSJKBCAUVPBQZUVQCQZTZTUVPNQZUVQNQZTZUVSAUWBUWEAUVTUWCUWAUWDABNUVPEU
      QACNUVQFUQURUSUVPUVQUTVAVBUVNUVSUCJKBCUVLUVPUVQVCZUMZUVMUVRNUWGUVMUWFPUPU
      VRUVLUWFPVEUVPUVQPVFVGZVHVIVJAPVKZUVIPVLZUFZUVKUVOVMNNUNZNPVQUWIVNUWLNPVR
      VOZAUVIUWLUWJABNUFZCNUFZUVIUWLUFEFBNCNVPVSUWLNPVNWGVTZUCUVINPWAWBWCWDAUUS
      UUTAUWNUUSNQZEBWEZVAZAUWOUUTNQZFCWEZVAZWHAUVCUADAUVBDQZTAUVBUVJQZTZUVCAUX
      CUXDADUVJUVBIWFWIUXEUVCJKBCUXEUVCJWJUXEUVCKWJUXEUVRUVBUMZUVRUVAUJRZTZKCSZ
      JBSZUVCKCSZJBSUXEUXGUXFTZKCSJBSUXJUXEUXGUXFJKBCUXEUXGJKBCUXEUWBTZUVPUUSUJ
      RZUVQUUTUJRZUXGUXMUWNUVTUXNAUWNUXDUWBEWKZUXEUVTUWAWLZBUVPWMVSUXMUWOUWAUXO
      AUWOUXDUWBFWKZUXEUVTUWAWNZCUVQWMVSUXMUWCUWDUWQUWTUXNUXOTUXGULUXMBNUVPUXPU
      XQWQUXMCNUVQUXRUXSWQUXMUWNUWQUXPUWRVAUXMUWOUWTUXRUXAVAUVPUVQUUSUUTWOWPWRV
      BUXEUVMUVBUMZUCUVISZUXFKCSJBSUXDUYAAUWIUXDUYAUWMUCUVBUVIPWSWTXAUXTUXFUCJK
      BCUWGUVMUVRUVBUWHXBXCXDXHUXLUXHJKBCUXGUXFXEXFXDUXIUXKJBUXHUVCKCUXFUXGUVCU
      VRUVBUVAUJXIXGXJXJVAXKXLXMAUVHUAVDAUVBVDQZTZUVDUVGUYCUVDTZUVBUDUIZUEUIZPU
      HZORZUECSZUDBSZUVGUYDUWNUWOUVBLUIZMUIZPUHZUMZUYKUUSORZUYLUUTORZXNZMNSZLNS
      ZUYJAUWNUYBUVDEWKAUWOUYBUVDFWKUYDUVBUUSUUTLMAUYBUVDXOAUWQUYBUVDUWSWKAUWTU
      YBUVDUXBWKAUUSXRXSUYBUVDGWKAUUTXRXSUYBUVDHWKUYCUVDXPXQUWNUWOTZUYSTZUYJLMN
      NUYTUYSMUYTMXTUYRMLNMNYAUYQMNYBYTYCVUAUYJLWJVUAUYJMWJVUAUYTUYQTZMNSZLNSUY
      JMNSZLNSVUAUYTUYQLMNNUYTUYTMNUKZLNUKUYSUYTVUELNUYTUYTMNUYTYDYEYEYFUYTUYSX
      PXHVUCVUDLNUYKNQZVUBUYJMNVUFUYLNQZTZVUBUYJVUHVUBTZUYKUYEORZUYLUYFORZTZUEC
      SZUDBSZUYJVUBVUHVUNVUBVUHTZVUJUDBSZVUKUECSZVUNVUOUWNVUFUYOVUPUWNUWOUYQVUH
      YGVUBVUFVUGWLUYNUYOUYPUYTVUHYHUWNVUFTUYOVUPUDBUYKYIXGYJVUOUWOVUGUYPVUQUWN
      UWOUYQVUHYKVUBVUFVUGWNUYNUYOUYPUYTVUHYLUWOVUGTUYPVUQUECUYLYIXGYJVUJVUKUDU
      EBCYMYNYOVUIVUMUYIUDBVUIUYEBQZTZVULUYHUECVUSUYFCQZTZVULUYHVVAVULTZUYNVUHU
      YENQZUYFNQZTTZVULTZUYHVVBUYNUYOUYPVUIVURVUTVULUYQVUHUYTUYQVURVUTVULXNZUUA
      YPUUBVVBVVEVULVVBVUHVVCVVDVUHVUBVURVUTVULUUCVVBBNUYEVVBUWNUWOVUIVURVUTVUL
      UYTVUHUYTUYQVVGUUDYPZUUEVUIVURVUTVULYKWQVVBCNUYFVVBUWNUWOVVHUUFVUSVUTVULX
      OWQUUJVVAVULXPUUKVVFUYNUYMUYGORZUYHVVEVULVVIUYKUYLUYEUYFUUGUSUYNUYHVVIUVB
      UYMUYGOXIUUHUUIVSYQYRYRYSYQYRUULVAUUMYJAUYJUVGULUYBUVDAUYHUVGUDUEBCAVURVU
      TTZTZUVFUYHUBUYGDVVKUYGDQZUYGUVJQZVVKUYEUYFBCPAVURVUTWLAVURVUTWNUWMAUWKVV
      JUWPYFUUNAVVLVVMVMVVJADUVJUYGIWFYFWCVVKUVEUYGUMZTUVEUYGUVBOVVKVVNXPUUOUUP
      UUQWKYSYQXMUAUBDUVAUURWP $.
  $}

  ${
    $d x A $.
    $( The supremum of a non-empty set of extended reals which does not contain
       minus infinity is not minus infinity.  (Contributed by Thierry Arnoux,
       21-Mar-2017.) $)
    supxrnemnf $p |- ( ( A C_ RR* /\ A =/= (/) /\ -. -oo e. A ) ->
                     sup ( A , RR* , < ) =/= -oo ) $=
      ( vx cxr wss c0 wne cmnf wcel w3a clt csup wbr mnfxr a1i supxrcl 3ad2ant1
      wn wa biimprd sylc wrex simp1 jctir wceq simpl sselda simpr simplr nelneq
      cv syl2anc ngtmnft con1d reximdva0 3impa 3com23 supxrlub xrltne syl3anc )
      ACDZAEFZGAHQZIZGCHZACJKZCHZGVEJLZVEGFVDVCMNUTVAVFVBAOPVCUTVDRZGBUJZJLZBAU
      AZVGVCUTVDUTVAVBUBMUCUTVBVAVKUTVBVAVKUTVBRZVJBAVLVIAHZRZVICHZVIGUDZQZVJVL
      ACVIUTVBUEUFVNVMVBVQVLVMUGUTVBVMUHVIGAUIUKVOVJVPVOVPVJQVIULSUMTUNUOUPVHVG
      VKBAGUQSTGVEURUS $.
  $}

  ${
    $( The topology of the extended reals is Hausdorff.  (Contributed by
       Thierry Arnoux, 24-Mar-2017.) $)
    xrhaus $p |- ( ordTop ` <_ ) e. Haus $=
      ( cle ctsr wcel cordt cfv cha letsr ordthaus ax-mp ) ABCADEFCGAHI $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
        Real number intervals - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d a b w x A $.  $d a b w x B $.  $d a b w x C $.  $d a b w x D $.
    $( A closed-below, open-above interval is a subset of its closure.
       (Contributed by Thierry Arnoux, 25-Oct-2016.) $)
    icossicc $p |- ( A [,) B ) C_ ( A [,] B ) $=
      ( va vb vx vw cicc cle clt cico df-ico df-icc cxr wcel cv wa wbr ixxssixx
      idd xrltle ) CDEFABGHIHHJCDEKCDELAMNFOZMNPAUAHQSUABTR $.

    $( A closed-above, open-below interval is a subset of its closure.
       (Contributed by Thierry Arnoux, 1-Apr-2017.) $)
    iocssicc $p |- ( A (,] B ) C_ ( A [,] B ) $=
      ( va vb vx vw cicc clt cle cioc df-ioc df-icc cv xrltle cxr wcel ixxssixx
      wa wbr idd ) CDEFABGHIIIJCDEKCDELAFMZNUAOPBOPRUABISTQ $.

    $( An open interval is a subset of its closure-below.  (Contributed by
       Thierry Arnoux, 3-Mar-2017.) $)
    ioossico $p |- ( A (,) B ) C_ ( A [,) B ) $=
      ( va vb vx vw cico clt cle cioo df-ioo df-ico cv xrltle cxr wcel ixxssixx
      wa wbr idd ) CDEFABGHHIHJCDEKCDELAFMZNUAOPBOPRUABHSTQ $.

    $( Condition for a closed interval to be a subset of an open interval.
       (Contributed by Thierry Arnoux, 29-Mar-2017.) $)
    iocssioo $p |- ( ( ( A e. RR* /\ B e. RR* ) /\
      ( A <_ C /\ D < B ) ) -> ( C (,] D ) C_ ( A (,) B ) ) $=
      ( va vb vx vw cioc clt cle cioo df-ioo df-ioc cv xrlelttr ixxss12 ) EFGHA
      BCDIJJJKLKJEFGMEFGNACHOZPRDBPQ $.

    $( Condition for a closed interval to be a subset of an open interval.
       (Contributed by Thierry Arnoux, 29-Mar-2017.) $)
    icossioo $p |- ( ( ( A e. RR* /\ B e. RR* ) /\
      ( A < C /\ D <_ B ) ) -> ( C [,) D ) C_ ( A (,) B ) ) $=
      ( va vb vx vw cico clt cle cioo df-ioo df-ico cv xrltletr ixxss12 ) EFGHA
      BCDIJJKJLJKEFGMEFGNACHOZPRDBPQ $.

    $( Condition for an open interval to be a subset of an open interval.
       (Contributed by Thierry Arnoux, 26-Sep-2017.) $)
    ioossioo $p |- ( ( ( A e. RR* /\ B e. RR* ) /\
      ( A <_ C /\ D <_ B ) ) -> ( C (,) D ) C_ ( A (,) B ) ) $=
      ( va vb vx vw cioo clt cle df-ioo cv xrlelttr xrltletr ixxss12 ) EFGHABCD
      IJJJJIKKEFGLZQACHMZNRDBOP $.

    $( Disjoint joining an open interval with a closed below, open above
       interval to form a closed below, open above interval.  (Contributed by
       Thierry Arnoux, 26-Sep-2017.) $)
    joiniooico $p |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\
      ( A < B /\ B <_ C ) ) -> ( ( ( A (,) B ) i^i ( B [,) C ) ) = (/)
      /\ ( ( A (,) B ) u. ( B [,) C ) ) = ( A (,) C ) ) ) $=
      ( va vb vx vw cxr wcel w3a clt wbr cle wa cioo co cico cin wceq xrltletr
      c0 cun df-ioo df-ico cv xrlenlt ixxdisj adantr ixxun jca ) AHIBHICHIJZABK
      LBCMLNZNABOPZBCQPZRUASZUMUNUBACOPSUKUOULDEFGABCQKKMKODEFUCZDEFUDZBGUEZUFZ
      UGUHDEFGABCQOKKMKOKMUPUQUSUPURBCTABURTUIUJ $.
  $}

  $( An element of a closed interval is more than or equal to its lower bound
     (Contributed by Thierry Arnoux, 23-Dec-2016.) $)
  iccgelb $p |- ( ( A e. RR* /\ B e. RR* /\ C e. ( A [,] B ) ) -> A <_ C ) $=
    ( cxr wcel cicc co cle wbr wa w3a elicc1 biimpa simp2d 3impa ) ADEZBDEZCABF
    GEZACHIZPQJZRJCDEZSCBHIZTRUASUBKABCLMNO $.

  ${
    $d a b x $.  $d a b x z A $.  $d a b x z B $.
    $( The closure of the open end of a left-open real interval.  (Contributed
       by Thierry Arnoux, 28-Mar-2017.) $)
    snunioc $p |- ( ( A e. RR* /\ B e. RR* /\ A <_ B ) ->
                    ( { A } u. ( A (,] B ) ) = ( A [,] B ) ) $=
      ( va vb vz vx cxr wcel cle wbr w3a cicc co cioc cun csn wceq 3ad2ant1 clt
      wa iccid uneq1d simp1 simp2 xrleid df-icc df-ioc cv xrltnle xrletr simprr
      simp3 wi simpl1 simpl3 xrltle syl2anc mpd ex ixxun syl32anc eqtr3d ) AGHZ
      BGHZABIJZKZAALMZABNMZOZAPZVHOABLMZVFVGVJVHVCVDVGVJQVEAUARUBVFVCVCVDAAIJZV
      EVIVKQVCVDVEUCZVMVCVDVEUDVCVDVLVEAUERVCVDVEULCDEFAABNLIISILIICDEUFZCDEUGA
      FUHZUIVNVOABUJVCVCVOGHZKZVLAVOSJZTZAVOIJZVQVSTZVRVTVQVLVRUKWAVCVPVRVTUMVC
      VCVPVSUNVCVCVPVSUOAVOUPUQURUSUTVAVB $.
  $}

  $( A right-open interval does not contain its right endpoint.  (Contributed
     by Thierry Arnoux, 5-Apr-2017.) $)
  ubico $p |- ( ( A e. RR /\ B e. RR* ) -> -. B e. ( A [,) B ) ) $=
    ( cr wcel cxr wa co cle wbr clt w3a simp3 simp1 ltnrd pm2.65i elico2 mtbiri
    cico ) ACDBEDFBABRGDBCDZABHIZBBJIZKZUBUASTUALUBBSTUAMNOABBPQ $.

  $( Equality in terms of 'less than or equal to', 'less than'.  (Contributed
     by Thierry Arnoux, 5-Jul-2017.) $)
  xeqlelt $p |- ( ( A e. RR* /\ B e. RR* ) ->
               ( A = B <-> ( A <_ B /\ -. A < B ) ) ) $=
    ( cxr wcel wa wceq cle wbr clt wn xrletri3 wb xrlenlt ancoms anbi2d bitrd )
    ACDZBCDZEZABFABGHZBAGHZETABIHJZEABKSUAUBTRQUAUBLBAMNOP $.

  $( Relate elementhood to a closed interval with elementhood to the same
     closed-below, opened-above interval or to its upper bound.  (Contributed
     by Thierry Arnoux, 3-Jul-2017.) $)
  eliccelico $p |- ( ( A e. RR* /\ B e. RR* /\ A <_ B ) ->
                    ( C e. ( A [,] B ) <-> ( C e. ( A [,) B ) \/ C = B ) ) ) $=
    ( cxr wcel cle wbr w3a co wn wa simpl1 simpl2 biimpa syl21anc syl2anc sylib
    wi syl22anc ex cicc cico wceq wo clt simprl elicc1 simp1d simp3d jca simprr
    simp2d elico1 notbid df-3an notbii imnan imp xeqlelt biimpar pm5.6 icossicc
    bitr4i simpr sseldi eqeltrd simpl3 breqtrrd xrleid syl eqbrtrd wb mpbir3and
    jaodan impbid ) ADEZBDEZABFGZHZCABUAIZEZCABUBIZEZCBUCZUDZVSWAWCJZKZWDRWAWER
    VSWGWDVSWGKZCDEZVQCBFGZCBUEGZJZWDWHVPVQWAWIVPVQVRWGLZVPVQVRWGMZVSWAWFUFZVPV
    QKZWAKZWIACFGZWJWPWAWIWRWJHZABCUGZNZUHOZWNWHVPVQWAWJWMWNWOWQWIWRWJXAUIOWHWP
    WFWIWRWLWHVPVQWMWNUJZVSWAWFUKXBWHWPWAWRXCWOWQWIWRWJXAULPWPWFKZWIWRKZWLXDWIW
    RWKHZJZXEWLRZWPWFXGWPWCXFABCUMUNNXGXEWKKZJXHXFXIWIWRWKUOUPXEWKUQVCQURSWIVQK
    WDWJWLKCBUSUTSTWAWCWDVAQVSWEWAVSWCWAWDVSWCKWBVTCABVBVSWCVDVEVSWDKZWAWIWRWJX
    JCBDVSWDVDZVPVQVRWDMZVFXJABCFVPVQVRWDVGXKVHXJCBBFXKXJVQBBFGXLBVIVJVKXJVPVQW
    AWSVLVPVQVRWDLXLWTPVMVNTVO $.

  $( Relate elementhood to a closed-below, opened-above interval with
     elementhood to the same opened interval or to its lower bound.
     (Contributed by Thierry Arnoux, 6-Jul-2017.) $)
  elicoelioo $p |- ( ( A e. RR* /\ B e. RR* /\ A < B ) ->
                    ( C e. ( A [,) B ) <-> ( C = A \/ C e. ( A (,) B ) ) ) ) $=
    ( cxr wcel clt wbr w3a co wceq wo wn wa wi cle simpl1 simpl2 biimpa syl2anc
    syl21anc cico cioo simprl elico1 simp1d simp2d simprr simp3d elioo1 3anan32
    jca notbid notbii imnan bitr4i sylib imp syl22anc xeqlelt biimpar ex syl6ib
    eqcom pm5.6 orcom simpr eqeltrd xrleid breqtrrd simpl3 eqbrtrd wb mpbir3and
    syl ioossico sseldi jaodan impbid ) ADEZBDEZABFGZHZCABUAIZEZCAJZCABUBIZEZKZ
    WBWDWGWEKZWHWBWDWGLZMZWENWDWINWBWKACJZWEWBWKWLWBWKMZVSCDEZACOGZACFGZLZWLVSV
    TWAWKPZWMVSVTWDWNWRVSVTWAWKQZWBWDWJUCZVSVTMZWDMZWNWOCBFGZXAWDWNWOXCHZABCUDZ
    RZUETZWMVSVTWDWOWRWSWTXBWNWOXCXFUFTWMXAWJWNXCWQWMVSVTWRWSUKZWBWDWJUGXGWMXAW
    DXCXHWTXBWNWOXCXFUHSXAWJMZWNXCMZWQXIWNWPXCHZLZXJWQNZXAWJXLXAWGXKABCUIULRXLX
    JWPMZLXMXKXNWNWPXCUJUMXJWPUNUOUPUQURVSWNMWLWOWQMACUSUTURVAACVCVBWDWGWEVDUPW
    GWEVEVBWBWHWDWBWEWDWGWBWEMZWDWNWOXCXOCADWBWEVFZVSVTWAWEPZVGXOAACOXOVSAAOGXQ
    AVHVNXPVIXOCABFXPVSVTWAWEVJVKXOVSVTWDXDVLXQVSVTWAWEQXESVMWBWGMWFWCCABVOWBWG
    VFVPVQVAVR $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Intersection between two opened below, closed above intervals sharing
       the same upper bound.  (Contributed by Thierry Arnoux, 7-Aug-2017.) $)
    iocinioc2 $p |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ A <_ B )
      -> ( ( A (,] C ) i^i ( B (,] C ) ) = ( B (,] C ) ) $=
      ( vx cxr wcel w3a cle wbr wa cioc co cin cv clt wb elioc1 syl2anc 3adant3
      bitr4d simpl1 simpl3 simpl2 anbi12d simp31 simp32 xrlelttrd simp33 3expia
      elin simp2 3jca pm4.71rd syl5bb eqrdv ) AEFZBEFZCEFZGZABHIZJZDACKLZBCKLZM
      ZVCVADNZVDFZVEEFZBVEOIZVECHIZGZVEVCFZVFVEVBFZVKJZVAVJVEVBVCUJVAVMVGAVEOIZ
      VIGZVJJVJVAVLVOVKVJVAUPURVLVOPUPUQURUTUAZUPUQURUTUBZACVEQRVAUQURVKVJPUPUQ
      URUTUCZVQBCVEQRZUDVAVJVOUSUTVJVOUSUTVJGZVGVNVIUSUTVGVHVIUEZVTABVEUSUTUPVJ
      VPSUSUTUQVJVRSWAUSUTVJUKUSUTVGVHVIUFUGUSUTVGVHVIUHULUIUMTUNVSTUO $.
  $}

  ${
    $d x A $.
    xrdifh.1 $e |- A e. RR* $.
    $( Set difference of a half-opened interval in the extended reals.
       (Contributed by Thierry Arnoux, 1-Aug-2017.) $)
    xrdifh $p |- ( RR* \ ( A [,] +oo ) ) = ( -oo [,) A ) $=
      ( vx cxr cpnf cicc co cdif cmnf wcel wn wa wbr cle wo w3a pm5.32i 3bitr4i
      wb mp2an cico clt biortn pnfge notnot sylib biorf syl orcom syl6bbr pnfxr
      cv w3o elicc1 notbii 3ianor 3orass 3bitri a1i 3bitr4rd mpan2 bitr4d eldif
      xrltnle 3anass mnfxr elico1 mnfle biantrurd eqriv ) CDAEFGZHZIAUAGZCULZDJ
      ZVNVKJZKZLVOVNAUBMZLZVNVLJVNVMJZVOVQVRVOVQAVNNMZKZVRVOWBVNENMZKZOZVOKZWEO
      ZWBVQVOWEUCVOWBWDWBOZWEVOWDKZWBWHSVOWCWIVNUDWCUEUFWDWBUGUHWBWDUIUJVQWGSVO
      VQVOWAWCPZKWFWBWDUMWGVPWJADJZEDJVPWJSBUKAEVNUNTUOVOWAWCUPWFWBWDUQURUSUTVO
      WKVRWBSBVNAVDVAVBQVNDVKVCVOIVNNMZVRPZVOWLVRLZLVTVSVOWLVRVEIDJWKVTWMSVFBIA
      VNVGTVOVRWNVOWLVRVNVHVIQRRVJ $.
  $}

  ${
    $( Relate intersection of two opened below, closed above intervals with the
       same upper bound with a conditional construct.  (Contributed by Thierry
       Arnoux, 7-Aug-2017.) $)
    iocinif $p |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) ->
      ( ( A (,] C ) i^i ( B (,] C ) )
                                = if ( A < B , ( B (,] C ) , ( A (,] C ) ) ) $=
      ( cxr wcel w3a clt wbr cioc co cin wa wn wo cle iocinioc2 syldan ex ancld
      wceq cif exmid xrltle imp 3adantl3 simpl2 simpl1 xrlenlt biimpar syl21anc
      simpr 3ancoma incom syl5eqr sylanbr orim12d mpi eqif sylibr ) ADEZBDEZCDE
      ZFZABGHZACIJZBCIJZKZVFTZLZVDMZVGVETZLZNZVGVDVFVEUATVCVDVJNVMVDUBVCVDVIVJV
      LVCVDVHVCVDVHVCVDABOHZVHUTVAVDVNVBUTVALVDVNABUCUDUEABCPQRSVCVJVKVCVJVKVCV
      JBAOHZVKVCVJLVAUTVJVOUTVAVBVJUFUTVAVBVJUGVCVJUKVAUTLVOVJBAUHUIUJVCVAUTVBF
      ZVOVKVAUTVBULVPVOLVGVFVEKVEVFVEUMBACPUNUOQRSUPUQVDVGVFVEURUS $.
  $}

  $( The difference between two opened intervals sharing the same lower bound
     (Contributed by Thierry Arnoux, 26-Sep-2017.) $)
  difioo $p |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\ A < B )
            -> ( ( A (,) C ) \ ( A (,) B ) ) = ( B [,) C ) ) $=
    ( cxr wcel clt wbr wa cle cioo co wceq cin cun wss simpll1 adantr syl simpr
    c0 w3a cdif incom joiniooico anassrs simpld syl5eqr simprd uncom a1i simpl3
    xrleid ioossioo syl22anc ssequn2 sylib 3eqtr4d difeq sylanbrc simpl2 xrltle
    cico imp syl21anc ssdif0 ico0 biimpar eqtr4d wo xrlelttric syl2anc mpjaodan
    ) ADEZBDEZCDEZUAZABFGZHZBCIGZACJKZABJKZUBZBCVBKZLZCBFGZVRVSHZWCWAMZTLWCWANZ
    VTWANZLWDWFWGWAWCMZTWAWCUCWFWJTLZWAWCNZVTLZVPVQVSWKWMHABCUDUEZUFUGWFWLVTWHW
    IWFWKWMWNUHWHWLLWFWCWAUIUJWFWAVTOZWIVTLWFVMVOAAIGZVSWOVMVNVOVQVSPZVRVOVSVMV
    NVOVQUKZQWFVMWPWQAULZRVRVSSACABUMUNWAVTUOUPUQVTWAWCURUSVRWEHZWBTWCWTVTWAOZW
    BTLWTVMVNWPCBIGZXAVMVNVOVQWEPZVRVNWEVMVNVOVQUTZQZWTVMWPXCWSRWTVOVNWEXBVRVOW
    EWRQZXEVRWESVOVNHWEXBCBVAVCVDZABACUMUNVTWAVEUPWTVNVOXBWCTLZXEXFXGVNVOHXHXBB
    CVFVGVDVHVRVNVOVSWEVIXDWRBCVJVKVL $.

  $( The difference between two closed below, opened above intervals sharing
     the same upper bound (Contributed by Thierry Arnoux, 13-Oct-2017.) $)
  difico $p |- ( ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) /\
    ( A <_ B /\ B <_ C ) ) -> ( ( A [,) C ) \ ( B [,) C ) ) = ( A [,) B ) ) $=
    ( cxr wcel w3a cle wbr wa cico co cdif cun cin c0 icodisj undif4 syl adantr
    wceq difid uneq2i un0 eqtri a1i icoun difeq1d 3eqtr3rd ) ADEBDECDEFZABGHBCG
    HIZIZABJKZBCJKZUMLZMZULUMMZUMLZULACJKZUMLUIUOUQTZUJUIULUMNOTUSABCPULUMUMQRS
    UOULTUKUOULOMULUNOULUMUAUBULUCUDUEUKUPURUMABCUFUGUH $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
        Finite intervals of integers - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Finite sets of sequential integers starting from a natural are a subset of
     the natural numbers.  (Contributed by Thierry Arnoux, 4-Aug-2017.) $)
  fzssnn $p |- ( M e. NN -> ( M ... N ) C_ NN ) $=
    ( cn wcel cfz co c1 wss cuz cfv fzss1 nnuz eleq2s fzssuz sseqtr4i syl6ss )
    ACDABEFZGBEFZCQRHAGIJZCAGBKLMRSCGBNLOP $.

  ${
    $d j N $.
    $( Upper set of the natural numbers.  (Contributed by Thierry Arnoux,
       22-Aug-2017.) $)
    nndiffz1 $p |- ( N e. NN0 -> ( NN \ ( 1 ... N ) ) = ( ZZ>= ` ( N + 1 ) ) )
      $=
      ( vj wcel cn c1 co caddc cz cle wbr wn wa baibd zred simpr bitrd pm5.32da
      wb a1i cc0 cn0 cfz cdif cuz cfv cv w3a 1z nn0z elfz1 3anass syl6bb notbid
      sylancr clt simpl ltnled zltp1le bitr3d sylan adantr cr 1re simpll nn0red
      readdcld simplr 0p1e1 nn0ge0d leadd1dd syl5eqbrr letrd ex pm4.71rd bicomd
      0re eldif elnnz1 anbi1i anass 3bitri peano2nn0 nn0zd eluz1 3bitr4d eqrdv
      syl ) AUACZBDEAUBFZUCZAEGFZUDUEZWHBUFZHCZEWMIJZWMWICZKZLZLZWNWKWMIJZLZWMW
      JCZWMWLCZWHWNWRWTWHWNLZWRWOWTLZWTXDWOWQWTXDWOLZWQWMAIJZKZWTXFWPXGXDWPWOXG
      WHWPWNWOXGLZWHWPWNWOXGUGZWNXILWHEHCAHCZWPXJRUHAUIZWMEAUJUNWNWOXGUKULMMUMX
      DXHWTRZWOWHXKWNXMXLXKWNLZAWMUOJXHWTXNAWMXNAXKWNUPNXNWMXKWNONUQAWMURUSUTVA
      PQXDWTXEXDWTWOXDWTWOXDWTLZEWKWMEVBCXOVCSZXOAEXOAWHWNWTVDZVEZXPVFXOWMWHWNW
      TVGNXOETEGFWKIVHXOTAETVBCXOVPSXRXPXOAXQVIVJVKXDWTOVLVMVNVOPQXBWSRWHXBWMDC
      ZWQLWNWOLZWQLWSWMDWIVQXSXTWQWMVRVSWNWOWQVTWASWHWKHCXCXARWHWKAWBWCWKWMWDWG
      WEWF $.
  $}

  ${
    $d n x y z A $.
    $( For any finite subset of ` NN ` , find a superset in the form of a set
       of sequential integers.  (Contributed by Thierry Arnoux,
       13-Sep-2017.) $)
    ssnnssfz $p |- ( A e. ( ~P NN i^i Fin ) -> E. n e. NN A C_ ( 1 ... n ) ) $=
      ( vx vy vz cn cfn wcel c1 cv cfz co wss wrex c0 wceq wa clt adantr wbr cr
      cpw cin 1nn simpr 0ss syl6eqss oveq2 sseq2d sylancr wne csup elin simplbi
      rspcev elpwid wor nnssre ltso mp2 a1i simprbi fisupcl syl13anc sseldd cuz
      soss cfv sselda nnuz syl6eleq cz cle nnzd wn wral wi fisup2g ssrexv supub
      sylc imp nnred lenltd mpbird eluz2 syl3anbrc eluzfz syl2anc ex pm2.61dane
      ssrdv ) AFUBZGUCHZAIBJZKLZMZBFNZAOWNAOPZQZIFHAIIKLZMZWRUDWTAOXAWNWSUEXAUF
      UGWQXBBIFWOIPWPXAAWOIIKUHUIUOUJWNAOUKZQZAFRULZFHAIXEKLZMZWRXDAFXEXDAFWNAW
      MHZXCWNXHAGHZAWMGUMZUNSUPZXDFRUQZXIXCAFMZXEAHZXLXDFUAMUARUQXLURUSFUARVGUT
      VAZWNXIXCWNXHXIXJVBSZWNXCUEZXKFARVCVDZVEXDCAXFXDCJZAHZXSXFHZXDXTQZXSIVFVH
      ZHXEXSVFVHHZYAYBXSFYCXDAFXSXKVIZVJVKYBXSVLHXEVLHXSXEVMTZYDYBXSYEVNYBXEYBA
      FXEXDXMXTXKSXDXNXTXRSVEZVNYBYFXEXSRTVOZXDXTYHXDCDEFAXSRXOXDXMXSDJZRTVODAV
      PYIXSRTYIEJRTEANVQDFVPQZCANZYJCFNXKXDXLXIXCXMYKXOXPXQXKCDEFARVRVDYJCAFVSW
      AVTWBYBXSXEYBXSYEWCYBXEYGWCWDWEXSXEWFWGXSIXEWHWIWJWLWQXGBXEFWOXEPWPXFAWOX
      EIKUHUIUOWIWK $.
  $}

  $( Split the last element of a finite set of sequential integers.  (more
     generic than ~ fzsuc ) (Contributed by Thierry Arnoux, 7-Nov-2016.) $)
  fzspl $p |- ( N e. ( ZZ>= ` M ) ->
                ( M ... N ) = ( ( M ... ( N - 1 ) ) u. { N } ) ) $=
    ( cuz cfv wcel cfz co c1 cmin caddc cun wceq csn wa cc eluzelz zcnd jca syl
    cz 1z a1i npcan syl2anc eleq1d ibir cle wbr eluzelre lem1d wb zsubcld eluz1
    mpbird fzsplit2 oveq1d fzsn eqtrd uneq2d eqeq2d mpbid ) BACDZEZABFGZABHIGZF
    GZVEHJGZBFGZKZLZVDVFBMZKZLVCVGVBEZBVECDEZNVJVCVMVNVCVMVCVGBVBVCBOEHOEVGBLVC
    BABPZQVCHHTEVCUAUBZQBHUCUDZUEUFVCVNBTEZVEBUGUHZNZVCVRVSVOVCBABUIUJRVCVETEVN
    VTUKVCBHVOVPULVEBUMSUNRVEABUOSVCVIVLVDVCVHVKVFVCVHBBFGZVKVCVGBBFVQUPVCVRWAV
    KLVOBUQSURUSUTVA $.

  ${
    $d x K $.  $d x M $.  $d x N $.
    $( Split a finite interval of integers into two parts.  (Contributed by
       Thierry Arnoux, 2-May-2017.) $)
    fzsplit3 $p |- ( K e. ( M ... N ) ->
      ( M ... N ) = ( ( M ... ( K - 1 ) ) u. ( K ... N ) ) ) $=
      ( vx cfz co wcel c1 wo wa wbr cr syl2anr cuz cfv cz elfzuz elfzuz3 adantl
      wb cmin cun cv cle clt elfzelz 1re a1i resubcld lelttric 1z zsubcld elfz5
      zred elfzuzb rbaib eluz syl2an zlem1lt 3bitrd orbi12d mpbird adantr caddc
      syl peano2uz recnd npcand eleq1d mpbid uztrn syl2anc sylanbrc jaodan elun
      impbida syl6bbr eqrdv ) ABCEFZGZDVSBAHUAFZEFZACEFZUBZVTDUCZVSGZWEWBGZWEWC
      GZIZWEWDGVTWFWIVTWFJZWIWEWAUDKZWAWEUEKZIZWFWELGWALGWMVTWFWEWEBCUFZUNVTAHV
      TAABCUFZUNZHLGVTUGUHZUIWEWAUJMWJWGWKWHWLWFWEBNOZGZWAPGWGWKTVTWEBCQVTAHWOH
      PGVTUKUHULWEBWAUMMWJWHWEANOZGZAWEUDKZWLWJCWENOZGZWHXATWFXDVTWEBCRSWHXAXDW
      EACUOUPVEVTAPGZWEPGZXAXBTWFWOWNAWEUQURVTXEXFXBWLTWFWOWNAWEUSURUTVAVBVTWGW
      FWHVTWGJZWSXDWFWGWSVTWEBWAQSXGCWTGZAXCGZXDVTXHWGABCRVCXGWAHVDFZXCGZXIXGWA
      XCGZXKWGXLVTWEBWARSWEWAVFVEVTXKXITWGVTXJAXCVTAHVTAWPVGVTHWQVGVHVIVCVJACWE
      VKVLWEBCUOZVMVTWHJWSXDWFWHXAAWRGWSVTWEACQABCQAWEBVKMWHXDVTWEACRSXMVMVNVPW
      EWBWCVOVQVR $.
  $}

  $( The proportion of one binomial coefficient to another with ` N ` decreased
     by 1.  (Contributed by Thierry Arnoux, 9-Nov-2016.) $)
  bcm1n $p |- ( ( K e. ( 0 ... ( N - 1 ) ) /\ N e. NN ) ->
    ( ( ( N - 1 ) _C K ) / ( N _C K ) ) = ( ( N - K ) / N ) ) $=
    ( cc0 c1 cmin co cfz wcel cn wa cbc cdiv wceq cmul cc wbr adantr clt mpbird
    nnne0d caddc bcp1n nnz zcnd adantl ax-1cn a1i npcand oveq1d oveq12d eqeq12d
    oveq2d syl5ib 3impia 3anidm13 wne wb crp cn0 cle elfznn0 simpr elfzelz zred
    nnnn0d cz elfzle2 zltlem1 syl2an ltled elfz2nn0 syl3anbrc bcrpcl syl subcld
    rpcnd cneg negsubdi2d resubcld recnd addid2d breqtrrd 0re ltsubaddd lt0ne0d
    cr negne0d eqnetrrd divcld rpcnne0d divmul2 syl3anc bccl2 recdivd 3eqtr3d )
    ACBDEFZGFHZBIHZJZDBAKFZWPAKFZLFZLFDBBAEFZLFZLFXAWTLFXCBLFWSXBXDDLWSXBXDMZWT
    XAXDNFZMZWQWRXGWQWRWQXGWQWPDUAFZAKFZXAXHXHAEFZLFZNFZMWSXGAWPUBWSXIWTXLXFWSX
    HBAKWSBDWRBOHWQWRBBUCZUDUEZDOHWSUFUGUHZUIWSXKXDXANWSXHBXJXCLXOWSXHBAEXOUIUJ
    ULUKUMUNUOWSWTOHXDOHXAOHXACUPZJXEXGUQWSWTWSACBGFHZWTURHWSAUSHZBUSHABUTPXQWQ
    XRWRAWPVAQWSBWQWRVBZVEWSABWSAWQAVFHZWRACWPVCZQVDZWSBWRBVFHZWQXMUEVDZWSABRPZ
    AWPUTPZWQYFWRACWPVGQWQXTYCYEYFUQWRYAXMABVHVISZVJABVKVLZABVMVNVPZWSBXCXNWSBA
    XNWQAOHWRWQAYAUDQZVOZWSABEFZVQXCCWSABYJXNVRWSYLWSYLWSABYBYDVSVTWSYLWSYLCRPA
    CBUAFZRPWSABYMRYGWSBXNWAWBWSABCYBYDCWFHWSWCUGWDSWEWGWHZWIWSXAWQXAURHWRAWPVM
    QZWJWTXDXAWKWLSULWSWTXAYIWSXAYOVPWSWTWSXQWTIHYHABWMVNTWQXPWRWQXAAWPWMTQWNWS
    BXCXNYKWSBXSTYNWNWO $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
        Half-open integer ranges - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d k m n x N $.  $d k m x A $.  $d m x B $.
    iundisj3.0 $e |- F/_ n B $.
    iundisj3.1 $e |- ( n = k -> A = B ) $.
    $( Rewrite a countable union as a disjoint union, finite version.  Cf.
       ~ iundisj (Contributed by Thierry Arnoux, 15-Feb-2017.) $)
    iundisjfi $p |- U_ n e. ( 1 ..^ N ) A =
      U_ n e. ( 1 ..^ N ) ( A \ U_ k e. ( 1 ..^ n ) B ) $=
      ( vx vm c1 cfzo co ciun cv wcel wrex cr cn nfcv wceq cdif csb crab ssrab2
      clt ccnv csup cuz cfv wss c0 wne fzossnn nnuz sseqtri sstri rabn0 biimpri
      infmssuzcl sylancr sseldi nfrab1 nfsup nfcsb1 nfcri csbeq1a eleq2d elrabf
      wa sylib simprd nnssre ltnrd eliun ad2antrr elfzouz2 fzoss2 sselda adantr
      wbr 3syl nnred cle simpr sylanbrc infmssuzle elfzolt2 ad2antlr lelttrd ex
      rexlimdva syl5bi mtod eldifd csbeq1 oveq2 iuneq1d difeq12d rspcev syl2anc
      nfv nfcsb1v nfiun nfdif cbvrex sylibr eldifi reximi impbii 3bitr4i eqriv
      ) HDJEKLZAMZDXLACJDNZKLZBMZUAZMZHNZAOZDXLPZXSXQOZDXLPZXSXMOXSXROYAYCYAXSD
      INZAUBZCJYDKLZBMZUAZOZIXLPZYCYAXTDXLUCZQUEUFZUGZXLOZXSDYMAUBZCJYMKLZBMZUA
      ZOZYJYAYKXLYMXTDXLUDZYAYKJUHUIZUJZYKUKULZYMYKOZYKXLUUAYTXLRUUAEUMZUNUOUPZ
      UUCYAXTDXLUQURYKJUSUTZVAZYAXSYOYQYAYNXSYOOZYAUUDYNUUIVIUUGXTUUIDYMXLDYKQY
      LXTDXLVBDQSDYLSVCZDXLSZDHYODYMAUUJVDVEXNYMTAYOXSDYMAVFVGVHVJVKYAXSYQOZYMY
      MUEVTZYAYMYAYKQYMYKRQYKXLRYTUUEUPVLUPUUGVAZVMUULXSBOZCYPPYAUUMCXSYPBVNYAU
      UOUUMCYPYACNZYPOZVIZUUOUUMUURUUOVIZYMUUPYMYAYMQOUUQUUOUUNVOZUUSUUPUUSXLRU
      UPUUEUURUUPXLOZUUOYAYPXLUUPYAYNEYMUHUIOYPXLUJUUHYMJEVPYMJEVQWAVRVSZVAWBUU
      TUUSUUBUUPYKOZYMUUPWCVTUUFUUSUVAUUOUVCUVBUURUUOWDXTUUODUUPXLDUUPSUUKDHBFV
      EXNUUPTABXSGVGVHWEUUPYKJWFUTUUQUUPYMUEVTYAUUOUUPJYMWGWHWIWJWKWLWMWNYIYSIY
      MXLYDYMTZYHYRXSUVDYEYOYGYQDYDYMAWOUVDCYFYPBYDYMJKWPWQWRVGWSWTYBYIDIXLYBIX
      ADHYHDYEYGDYDAXBCDYFBDYFSFXCXDVEXNYDTZXQYHXSUVEAYEXPYGDYDAVFUVECXOYFBXNYD
      JKWPWQWRVGXEXFYBXTDXLXSAXPXGXHXIDXSXLAVNDXSXLXQVNXJXK $.
  $}

  ${
    $d a b k n x y N $.  $d a b k m x y A $.  $d a b m x y B $.
    $d k m n x N $.
    iundisj2fi.0 $e |- F/_ n B $.
    iundisj2fi.1 $e |- ( n = k -> A = B ) $.
    $( A disjoint union is disjoint, finite version.  Cf. ~ iundisj2
       (Contributed by Thierry Arnoux, 16-Feb-2017.) $)
    iundisj2fi $p |- Disj_ n e. ( 1 ..^ N ) ( A \ U_ k e. ( 1 ..^ n ) B ) $=
      ( vx vy va vb c1 cfzo cv weq csb cin c0 wcel cr ciun cdif wdisj wceq wral
      co wo wtru tru eqeq12 csbeq1 ineqan12d eqeq1d orbi12d equcom syl6bb incom
      wa syl6eq wss cn fzossnn nnssre sstri a1i biidd cle wbr necom df-ne bitri
      w3a wn wne clt wb sseli id leltne syl3an nfcsb1v nfcv nfiun nfdif csbeq1a
      wi vex oveq2 iuneq1d difeq12d csbief ineq12i cuz cfv cz simp1 sseldi nnuz
      syl6eleq simp2 nnzd simp3 elfzo2 syl3anbrc csbhypf equcoms eqcomd ssiun2s
      syl ssdifssd ssrin syl5eqss disjdif sseq0 sylancl 3adant3 sylbird syl5bir
      3expia orrd adantl wlogle mpan rgen2a disjors mpbir ) DLEMUFZACLDNZMUFZBU
      AZUBZUCHIOZDHNZYKPZDINZYKPZQZRUDZUGZIYGUEHYGUEYSHIYGUHYMYGSZYOYGSZURZYSUI
      UHJKOZDJNZYKPZDKNZYKPZQZRUDZUGYSYSHIJKYGJHOZKIOZURZUUCYLUUIYRUUDYMUUFYOUJ
      UULUUHYQRUUJUUKUUEYNUUGYPDUUDYMYKUKDUUFYOYKUKULUMUNJIOZKHOZURZUUCYLUUIYRU
      UOUUCIHOYLUUDYOUUFYMUJIHUOUPUUOUUHYQRUUOUUHYPYNQYQUUMUUNUUEYPUUGYNDUUDYOY
      KUKDUUFYMYKUKULYPYNUQUSUMUNYGTUTUHYGVATEVBZVCVDZVEUHUUBURYSVFYTUUAYMYOVGV
      HZVLZYSUHUUSYLYRYLVMZYOYMVNZUUSYRUVAYMYOVNUUTYOYMVIYMYOVJVKUUSUVAYMYOVOVH
      ZYRYTYMTSUUAYOTSUURUURUVBUVAVPYGTYMUUQVQYGTYOUUQVQUURVRYMYOVSVTYTUUAUVBYR
      WFUURYTUUAUVBYRYTUUAUVBVLZYQCLYOMUFZBUAZDYOAPZUVEUBZQZUTUVHRUDYRUVCYQDYMA
      PZCLYMMUFZBUAZUBZUVGQZUVHYNUVLYPUVGDYMYKUVLHWGDUVIUVKDYMAWACDUVJBDUVJWBFW
      CWDDHOZAUVIYJUVKDYMAWEUVNCYIUVJBYHYMLMWHWIWJWKDYOYKUVGIWGDUVFUVEDYOAWACDU
      VDBDUVDWBFWCWDDIOZAUVFYJUVEDYOAWEUVOCYIUVDBYHYOLMWHWIWJWKWLUVCUVLUVEUTUVM
      UVHUTUVCUVIUVEUVKUVCYMUVDSZUVIUVEUTUVCYMLWMWNZSYOWOSUVBUVPUVCYMVAUVQUVCYG
      VAYMUUPYTUUAUVBWPWQWRWSUVCYOUVCYGVAYOUUPYTUUAUVBWTWQXAYTUUAUVBXBYMLYOXCXD
      CUVDBYMUVICHOUVIBUVIBUDHCDHCNZABDUVRWBFGXEXFXGXHXIXJUVLUVEUVGXKXIXLUVEUVF
      XMYQUVHXNXOXSXPXQXRXTYAYBYCYDDYGYKHIYEYF $.
  $}

  ${
    $d a b k n x y $.  $d a b k m x y A $.  $d a b m x y B $.  $d k n M $.
    $d k n x N $.
    iundisjcnt.0 $e |- F/_ n B $.
    iundisjcnt.1 $e |- ( n = k -> A = B ) $.
    iundisjcnt.2 $e |- ( ph -> ( N = NN \/ N = ( 1 ..^ M ) ) ) $.
    $( Rewrite a countable union as a disjoint union.  (Contributed by Thierry
       Arnoux, 16-Feb-2017.) $)
    iundisjcnt $p |- ( ph -> U_ n e. N A =
      U_ n e. N ( A \ U_ k e. ( 1 ..^ n ) B ) ) $=
      ( cn wceq ciun c1 cfzo co wa simpr iuneq1d 3eqtr4a cv cdif nfcv iundisjfi
      iundisjf mpjaodan ) AGKLZEGBMZEGBDNEUAOPCMUBZMZLGNFOPZLZAUGQZEKBMEKUIMUHU
      JBCDEDBUCHIUEUMEGKBAUGRZSUMEGKUIUNSTAULQZEUKBMEUKUIMUHUJBCDEFHIUDUOEGUKBA
      ULRZSUOEGUKUIUPSTJUF $.
  $}

  ${
    $d k n M $.  $d k A $.  $d n N $.
    iundisj2cnt.0 $e |- F/_ n B $.
    iundisj2cnt.1 $e |- ( n = k -> A = B ) $.
    iundisj2cnt.2 $e |- ( ph -> ( N = NN \/ N = ( 1 ..^ M ) ) ) $.
    $( A countable disjoint union is disjoint.  Cf. ~ iundisj2 (Contributed by
       Thierry Arnoux, 16-Feb-2017.) $)
    iundisj2cnt $p |- ( ph -> Disj_ n e. N ( A \ U_ k e. ( 1 ..^ n ) B ) ) $=
      ( cn wceq c1 cfzo co wo cv wdisj disjeq1 mpbiri ciun cdif nfcv iundisj2fi
      iundisj2f jaoi syl ) AGKLZGMFNOZLZPEGBDMEQNOCUAUBZRZJUHULUJUHULEKUKRBCDED
      BUCHIUEEGKUKSTUJULEUIUKRBCDEFHIUDEGUIUKSTUFUG $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
               The ` # ` (finite set size) function - misc additions
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Restriction of the domain of the size function.  (Contributed by Thierry
     Arnoux, 31-Jan-2017.) $)
  hashresfn $p |- ( # |` A ) Fn A $=
    ( chash cvv cin cres wfn cn0 cpnf csn cun hashf ffn fnresin2 mp2b wceq inv1
    wf wb reseq2i fneq12 mp2an mpbi ) BACDZEZUCFZBAEZAFZCGHIJZBQBCFUEKCUHBLCABM
    NUDUFOUCAOUEUGRUCABAPZSUIUCAUDUFTUAUB $.

  $( Restriction of the domain of the size function.  (Contributed by Thierry
     Arnoux, 12-Jan-2017.) $)
  dmhashres $p |- dom ( # |` A ) = A $=
    ( chash cres cdm cin cvv dmres cn0 cpnf csn hashf fdmi ineq2i inv1 3eqtri
    cun ) BACDABDZEAFEABAGQFAFHIJPBKLMANO $.

  ${
    $d x y A $.  $d y ph $.
    hashiunf.1 $e |- F/ x ph $.
    hashiunf.3 $e |- ( ph -> A e. Fin ) $.
    hashunif.4 $e |- ( ph -> A C_ Fin ) $.
    hashunif.5 $e |- ( ph -> Disj_ x e. A x ) $.
    $( The cardinality of a disjoint finite union of finite sets.  Cf.
       ~ hashuni (Contributed by Thierry Arnoux, 17-Feb-2017.) $)
    hashunif $p |- ( ph -> ( # ` U. A ) = sum_ x e. A ( # ` x ) ) $=
      ( vy cuni chash cfv cv ciun csu uniiun fveq2i cfn wdisj wceq a1i cbvdisjv
      sselda id sylib hashiun cbviunv fveq2d fveq2 cbvsumv 3eqtr4d syl5eq ) ACI
      ZJKBCBLZMZJKZCUMJKZBNZULUNJBCOPAHCHLZMZJKCURJKZHNZUOUQAHCUREACQURFUBABCUM
      RHCURRGBHCUMURUMURSUCZUAUDUEAUNUSJUNUSSABHCUMURVBUFTUGUQVASACUPUTBHUMURJU
      HUITUJUK $.
  $}

  ${
    $d a n x A $.  $d i n $.
    $( Any set that is not finite contains subsets of arbitrarily large finite
       cardinality.  Cf. ~ isinf (Contributed by Thierry Arnoux,
       5-Jul-2017.) $)
    ishashinf $p |- ( -. A e. Fin -> A. n e. NN E. x e. ~P A ( # ` x ) = n ) $=
      ( va cfn wcel wn cv chash cfv wceq cn wa wex c1 cen wbr com syl eqtrd cpw
      wrex wss cfz co ccrd wral fzfid ficardom isinf breq2 anbi2d exbidv rspcva
      syl2anr wi vex elpw biimpri a1i hasheni adantl hashcard cn0 nnnn0 hashfz1
      ad2antlr ex anim12d eximdv mpd df-rex sylibr ralrimiva ) BEFGZAHZIJZCHZKZ
      ABUAZUBZCLVOVRLFZMZVPVTFZVSMZANZWAWCVPBUCZVPOVRUDUEZUFJZPQZMZANZWFWBWIRFZ
      WGVPDHZPQZMZANZDRUGWLVOWBWHEFZWMWBOVRUHZWHUISABDUJWQWLDWIRWNWIKZWPWKAWTWO
      WJWGWNWIVPPUKULUMUNUOWCWKWEAWCWGWDWJVSWGWDUPWCWDWGVPBAUQURUSUTWCWJVSWCWJM
      VQWIIJZVRWJVQXAKWCVPWIVAVBWBXAVRKVOWJWBXAWHIJZVRWBWRXAXBKWSWHVCSWBVRVDFXB
      VRKVRVEVRVFSTVGTVHVIVJVKVSAVTVLVMVN $.
  $}

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
                      The greatest common divisor operator - misc. add
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Numerator and denominator of the negative (Contributed by Thierry Arnoux,
     27-Oct-2017.) $)
  numdenneg $p |- ( Q e. QQ -> ( ( numer ` -u Q ) = -u ( numer ` Q )
    /\ ( denom ` -u Q ) = ( denom ` Q ) ) ) $=
    ( cq wcel cneg cnumer cfv cz cdenom cn cgcd wceq cdiv qnegcl qnumcl znegcld
    co c1 wa qdencl eqtrd neggcd syl2anc qnumdencoprm qeqnumdivden negeqd nncnd
    nnzd zcnd nnne0d divnegd w3a qnumdenbi biimpa syl32anc ) ABCZADZBCZAEFZDZGC
    ZAHFZICZUSVAJPZQKZUPUSVALPZKZUPEFUSKUPHFVAKRZAMUOURANZOASZUOVCURVAJPZQUOURG
    CVAGCVCVJKVHUOVAVIUGURVAUAUBAUCTUOUPURVALPZDVEUOAVKAUDUEUOURVAUOURVHUHUOVAV
    IUFUOVAVIUIUJTUQUTVBUKVDVFRVGUPUSVAULUMUN $.

  $( Calculate the reduced form of a quotient using ` gcd ` .  This version
     extends ~ divnumden for the negative integers.  (Contributed by Thierry
     Arnoux, 25-Oct-2017.) $)
  divnumden2 $p |- ( ( A e. ZZ /\ B e. ZZ /\ -u B e. NN ) ->
       ( ( numer ` ( A / B ) ) = -u ( A / ( A gcd B ) )
      /\ ( denom ` ( A / B ) ) = -u ( B / ( A gcd B ) ) ) ) $=
    ( cz wcel cneg cdiv co cnumer cfv cgcd wceq cdenom cc0 wne zcnd syl 3adant2
    cq wa divneg2d cn zssq simp1 sseldi simp2 nnne0 3ad2ant3 neg0 neeq2i sylibr
    w3a neneqd 0cn a1i neg11ad mtbid neneqad qdivcl syl3anc qnumcl simpl gcdcld
    cc nn0cnd negcld wn intnand gcdeq0 necon3abid 3adant3 mpbird negne0d divcld
    wb fveq2d numdenneg simpld gcdneg oveq2d divnumden divnegd div2negd 3eqtr4d
    eqtrd 3eqtr3d neg11d eqtr4d simprd eqtr3d jca ) ACDZBCDZBEZUADZUKZABFGZHIZA
    ABJGZFGZEZKWPLIZBWRFGEZKWOWQAWREZFGZWTWOWQXDWOWQWOWPRDZWQCDWOARDBRDBMNXEWOC
    RAUBWKWLWNUCZUDWOCRBUBWKWLWNUEZUDWOBMWOWMMEZKBMKZWOWMXHWOWMMNZWMXHNWNWKXJWL
    WMUFUGXHMWMUHUIUJULWOBMWOBXGOZMVCDWOUMUNUOUPZUQZABURUSZWPUTPOWOAXCWKWNAVCDW
    LWKWNSZAWKWNVAOQZWOWRWOWRWOABXFXGVBVDZVEZWOWRXQWOWRMNZAMKZXISZVFZWOXIXTXLVG
    WKWLXSYBVNWNWKWLSYAWRMABVHVIVJVKZVLZVMWOWPEZHIZAWMFGZHIZWQEZXDEZWOYEYGHWOAB
    XPXKXMTZVOWOXEYFYIKZXNXEYLYELIZXAKZWPVPZVQPWOAAWMJGZFGZWSYHYJWOYPWRAFWKWLYP
    WRKWNABVRVJZVSWKWNYHYQKZWLXOYSYGLIZWMYPFGZKZAWMVTZVQQWOYJAEXCFGWSWOAXCXPXRY
    DWAWOAWRXPXQYCWBWDWCWEWFWOAWRXPXQYCTWGWOXABXCFGZXBWOYMYTXAUUDWOYEYGLYKVOWOX
    EYNXNXEYLYNYOWHPWOUUAWMWRFGZYTUUDWOYPWRWMFYRVSWKWNUUBWLXOYSUUBUUCWHQWOXBUUD
    UUEWOBWRXKXQYCTZWOBWRXKXQYCWAWIWCWEUUFWGWJ $.

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
          Integers
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d x A $.  $d x y ph $.  $d y ps $.  $d x ch $.  $d x et $.  $d x th $.
    $d x ta $.
    nn0indd.1 $e |- ( x = 0 -> ( ps <-> ch ) ) $.
    nn0indd.2 $e |- ( x = y -> ( ps <-> th ) ) $.
    nn0indd.3 $e |- ( x = ( y + 1 ) -> ( ps <-> ta ) ) $.
    nn0indd.4 $e |- ( x = A -> ( ps <-> et ) ) $.
    nn0indd.5 $e |- ( ph -> ch ) $.
    nn0indd.6 $e |- ( ( ( ph /\ y e. NN0 ) /\ th ) -> ta ) $.
    $( Principle of Mathematical Induction (inference schema) on nonnegative
       integers, a deduction version.  (Contributed by Thierry Arnoux,
       23-Mar-2018.) $)
    nn0indd $p |- ( ( ph /\ A e. NN0 ) -> et ) $=
      ( cn0 wcel wi wceq imbi2d cv cc0 c1 caddc co wa ancoms a2d nn0ind impcom
      ex ) IPQAFABRACRADRAERAFRGHIGUAZUBSBCAJTULHUAZSBDAKTULUMUCUDUESBEALTULISB
      FAMTNUMPQZADEUNADERZAUNUOAUNUFDEOUKUGUKUHUIUJ $.
  $}

  ${
    $d n w x y z $.  $d x A $.  $d w z ph $.  $d x ch $.  $d x ps $.
    $d x ta $.  $d x th $.
    nnindf.x $e |- F/ y ph $.
    $( Substitutions. $)
    nnindf.1 $e |- ( x = 1 -> ( ph <-> ps ) ) $.
    nnindf.2 $e |- ( x = y -> ( ph <-> ch ) ) $.
    nnindf.3 $e |- ( x = ( y + 1 ) -> ( ph <-> th ) ) $.
    nnindf.4 $e |- ( x = A -> ( ph <-> ta ) ) $.
    $( Basis. $)
    nnindf.5 $e |- ps $.
    $( Induction hypothesis. $)
    nnindf.6 $e |- ( y e. NN -> ( ch -> th ) ) $.
    $( Principle of Mathematical Induction, using a bound-variable hypothesis
       instead of distinct variables.  (Contributed by Thierry Arnoux,
       6-May-2018.) $)
    nnindf $p |- ( A e. NN -> ta ) $=
      ( vw cn wcel c1 elrab crab wa caddc wral wss 1nn mpbir2an elrabi peano2nn
      cv a1d anim12d 3imtr4g mpcom rgen nfcv nfrab nfv nfel wceq eleq1d cbvralf
      co oveq1 mpbi peano5nni mp2an sseli sylib simprd ) HQRZVKEVKHAFQUAZRVKEUB
      QVLHSVLRZPUJZSUCVCZVLRZPVLUDZQVLUEVMSQRBUFNABFSQJTUGGUJZSUCVCZVLRZGVLUDVQ
      VTGVLVRQRZVRVLRZVTAFVRQUHWAWACUBVSQRZDUBWBVTWAWAWCCDWAWCWAVRUIUKOULACFVRQ
      KTADFVSQLTUMUNUOVTVPGPVLAGFQIGQUPUQZPVLUPVTPURGVOVLGVOUPWDUSVRVNUTVSVOVLV
      RVNSUCVDVAVBVEPVLVFVGVHAEFHQMTVIVJ $.
  $}

  ${
    $d k m n ph $.  $d k m ps $.  $d k n ta $.  $d k n th $.  $d m n ch $. 
    nn0min.0 $e |- ( n = 0 -> ( ps <-> ch ) ) $.
    nn0min.1 $e |- ( n = m -> ( ps <-> th ) ) $.
    nn0min.2 $e |- ( n = ( m + 1 ) -> ( ps <-> ta ) ) $.
    nn0min.3 $e |- ( ph -> -. ch ) $.
    nn0min.4 $e |- ( ph -> E. n e. NN ps ) $.
    $( Extracting the minimum positive integer for which a property ` ch ` 
       does not hold. This uses substitutions similar to ~ nn0ind .
       (Contributed by Thierry Arnoux, 6-May-2018.) $)
    nn0min $p |- ( ph -> E. m e. NN0 ( -. th /\ ta ) ) $=
      ( vk wn cn0 wi cn c1 nfv wceq wa wral wrex adantr wsbc cv nfra1 nfan nfim
      wsb dfsbcq2 notbid imbi2d sbhypf caddc co sbequ12r wcel 0nn0 sbie syl5bbr
      cc0 wb oveq1 0p1e1 syl6eq 1nn eleq1 mpbiri sbcieg 3syl dfsbcq syl imbi12d
      bitr3d rspcv ax-mp mpan9 nfs1 sbequ12 cbvral nnnn0 rspc syl5bi a2d nnindf
      adantld rgen mpbi ralnex sylib pm2.65da imnan ralbii notbii dfrex2 sylibr
      r19.21v ) ADNZEUAZNZFOUBZNZWTFOUCAWSENZPZFOUBZNXCAXFBGQUCZAXGXFLUDAXFUAZB
      NZGQUBZXGNXHXIPZGQUBXHXJPXKGQXHBGMUJZNZPXHBGRUEZNZPXHWSPXHXDPXKMFGUFZXHXM
      FAXFFAFSXEFOUGUHXMFSUIMUFZRTZXMXOXHXRXLXNBGMRUKULUMXQFUFZTZXMWSXHXTXLDBDG
      MXSDGSZIUNULUMXQXSRUOUPZTZXMXDXHYCXLEBEGMYBEGSJUNULUMXQXPTZXMXIXHYDXLBBMG
      UQULUMACNZXFXOKVBOURXFYEXOPZPUSXEYFFVBOXSVBTZWSYEXDXOYGDCDBGFUJYGCBDGFYAI
      UTBCGFVBCGSHUNVAULYGEXNYGBGYBUEZEXNYGYBRTZYBQURZYHEVCYGYBVBRUOUPRXSVBRUOV
      DVEVFZYIYJRQURVGYBRQVHVIBEGYBQJVJVKYGYIYHXNVCYKBGYBRVLVMVOULVNVPVQVRXSQUR
      ZXHWSXDYLXFXEAXFXEFMUJZMOUBZYLXEXEYMFMOXEMSZXEFMYOVSXEFMVTWAYLXSOURYNXEPX
      SWBYMXEMXSOYOXEMFUQWCVMWDWGWEWFWHXHXIGQWRWIBGQWJWKWLXFXBXEXAFOWSEWMWNWOWK
      WTFOWPWQ $.
  $}

  ${
    ltesubnnd.1 $e |- ( ph -> M e. ZZ ) $.
    ltesubnnd.2 $e |- ( ph -> N e. NN ) $.
    $( Subtracting an integer number from another number decreases it.  See
       ~ ltsubrpd (Contributed by Thierry Arnoux, 18-Apr-2017.) $)
    ltesubnnd $p |- ( ph -> ( ( M + 1 ) - N ) <_ M ) $=
      ( c1 caddc co cmin cle zcnd cc wcel ax-1cn a1i nncnd addsubd clt wbr cz
      zred nnrpd ltsubrpd wb nnzd zsubcld zltp1le syl2anc mpbid eqbrtrd ) ABFGH
      CIHBCIHZFGHZBJABFCABDKFLMANOACEPQAUKBRSZULBJSZABCABDUAACEUBUCAUKTMBTMUMUN
      UDABCDACEUEUFDUKBUGUHUIUJ $.
  $}
