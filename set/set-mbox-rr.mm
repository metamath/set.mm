$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Rohan Ridenour
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Misc
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( ~ sp can be proven from the other classic axioms.  (Contributed by Rohan
       Ridenour, 3-Nov-2023.)  (Proof modification is discouraged.)  Use ~ sp
       instead.  (New usage is discouraged.) $)
    spALT $p |- ( A. x ph -> ph ) $=
      ( vy wal weq wi ax-1 axc4i axc10 syl ) ABDZBCEZKFZBDAAMBKLGHABCIJ $.
  $}

  ${
    $d ph x $.  $d x A $.
    rr-spce.1 $e |- ( ( ph /\ x = A ) -> ps ) $.
    rr-spce.2 $e |- ( ph -> A e. V ) $.
    $( Prove an existential.  (Contributed by Rohan Ridenour, 12-Aug-2023.) $)
    rr-spce $p |- ( ph -> E. x ps ) $=
      ( cv wceq wex cvv wcel elexd isset sylib ex eximdv mpd ) ACHDIZCJZBCJADKL
      TADEGMCDNOASBCASBFPQR $.
  $}

  ${
    $d A x $.  $d A y $.  $d ps y $.  $d th x $.  $d ph y $.  $d ch y $.
    rexlimdvaacbv.1 $e |- ( x = y -> ( ps <-> th ) ) $.
    rexlimdvaacbv.2 $e |- ( ( ph /\ ( y e. A /\ th ) ) -> ch ) $.
    $( Unpack a restricted existential antecedent while changing the variable
       with implicit substitution.  The equivalent of this theorem without the
       bound variable change is ~ rexlimdvaa .  (Contributed by Rohan Ridenour,
       3-Aug-2023.) $)
    rexlimdvaacbv $p |- ( ph -> ( E. x e. A ps -> ch ) ) $=
      ( wrex cbvrexv rexlimdvaa biimtrid ) BEGJDFGJACBDEFGHKADCFGILM $.
  $}

  ${
    $d ph y $.  $d ps y $.  $d ch x $.  $d th y $.  $d x y A $.
    rexlimddvcbvw.1 $e |- ( ph -> E. x e. A th ) $.
    rexlimddvcbvw.2 $e |- ( ( ph /\ ( y e. A /\ ch ) ) -> ps ) $.
    rexlimddvcbvw.3 $e |- ( x = y -> ( th <-> ch ) ) $.
    $( Unpack a restricted existential assumption while changing the variable
       with implicit substitution.  Similar to ~ rexlimdvaacbv .  The
       equivalent of this theorem without the bound variable change is
       ~ rexlimddv .  Version of ~ rexlimddvcbv with a disjoint variable
       condition, which does not require ~ ax-13 .  (Contributed by Rohan
       Ridenour, 3-Aug-2023.)  (Revised by GG, 2-Apr-2024.) $)
    rexlimddvcbvw $p |- ( ph -> ps ) $=
      ( wrex cbvrexvw rexlimdvaa biimtrid mpd ) ADEGKZBHPCFGKABDCEFGJLACBFGIMNO
      $.
  $}

  ${
    $d ph y $.  $d ps y $.  $d ch x $.  $d th y $.  $d x A $.  $d y A $.
    rexlimddvcbv.1 $e |- ( ph -> E. x e. A th ) $.
    rexlimddvcbv.2 $e |- ( ( ph /\ ( y e. A /\ ch ) ) -> ps ) $.
    rexlimddvcbv.3 $e |- ( x = y -> ( th <-> ch ) ) $.
    $( Unpack a restricted existential assumption while changing the variable
       with implicit substitution.  Similar to ~ rexlimdvaacbv .  The
       equivalent of this theorem without the bound variable change is
       ~ rexlimddv .  Usage of this theorem is discouraged because it depends
       on ~ ax-13 , see ~ rexlimddvcbvw for a weaker version that does not
       require it.  (Contributed by Rohan Ridenour, 3-Aug-2023.)
       (New usage is discouraged.) $)
    rexlimddvcbv $p |- ( ph -> ps ) $=
      ( wrex rexlimdvaacbv mpd ) ADEGKBHADBCEFGJILM $.
  $}

  ${
    $d D x $.  $d x A $.  $d x C $.  $d x ph $.
    rr-elrnmpt3d.1 $e |- F = ( x e. A |-> B ) $.
    rr-elrnmpt3d.2 $e |- ( ph -> C e. A ) $.
    rr-elrnmpt3d.3 $e |- ( ph -> D e. V ) $.
    rr-elrnmpt3d.4 $e |- ( ( ph /\ x = C ) -> B = D ) $.
    $( Elementhood in an image set.  (Contributed by Rohan Ridenour,
       11-Aug-2023.) $)
    rr-elrnmpt3d $p |- ( ph -> D e. ran F ) $=
      ( cv wceq wa eqcomd elrnmptdv ) ABCDEFGHIJKABMENODFLPQ $.
  $}

  ${
    rr-phpd.1 $e |- ( ph -> A e. _om ) $.
    rr-phpd.2 $e |- ( ph -> B C_ A ) $.
    rr-phpd.3 $e |- ( ph -> A ~~ B ) $.
    $( Equivalent of ~ php without negation.  (Contributed by Rohan Ridenour,
       3-Aug-2023.) $)
    rr-phpd $p |- ( ph -> A = B ) $=
      ( cen wbr wceq wn com wcel wpss wss adantr simpr neqcomd dfpss2 sylanbrc
      wa php syl2an2r ex mt4d ) ABCGHZBCIZFAUFJZUEJZABKLUGCBMZUHDAUGTZCBNZCBIJU
      IAUKUGEOUJBCAUGPQCBRSBCUAUBUCUD $.
  $}

  ${
    $d ps y $.  $d th x $.  $d et x $.  $d x A $.  $d ph x y $.
    tfindsd.1 $e |- ( x = (/) -> ( ps <-> ch ) ) $.
    tfindsd.2 $e |- ( x = y -> ( ps <-> th ) ) $.
    tfindsd.3 $e |- ( x = suc y -> ( ps <-> ta ) ) $.
    tfindsd.4 $e |- ( x = A -> ( ps <-> et ) ) $.
    tfindsd.5 $e |- ( ph -> ch ) $.
    tfindsd.6 $e |- ( ( ph /\ y e. On /\ th ) -> ta ) $.
    tfindsd.7 $e |- ( ( ph /\ Lim x /\ A. y e. x th ) -> ps ) $.
    tfindsd.8 $e |- ( ph -> A e. On ) $.
    $( Deduction associated with ~ tfinds .  (Contributed by Rohan Ridenour,
       8-Aug-2023.) $)
    tfindsd $p |- ( ph -> et ) $=
      ( con0 wcel cv wi 3exp com12 wlim wral tfinds3 mpcom ) IRSAFQBCDEFAGHIJKL
      MNAHTRSZDEUAAUHDEOUBUCAGTZUDZDHUIUEZBUAAUJUKBPUBUCUFUG $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Monoid rings
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c MndRing $.

  $( Extend class notation with the monoid ring function. $)
  cmnring $a class MndRing $.

  ${
    $d m r v x y i a b $.
    $( Define the monoid ring function.  This takes a monoid ` M ` and a ring
       ` R ` and produces a free left module over ` R ` with a product
       extending the monoid function on ` M ` .  (Contributed by Rohan
       Ridenour, 13-May-2024.) $)
    df-mnring $a |- MndRing = ( r e. _V , m e. _V |->
      [_ ( r freeLMod ( Base ` m ) ) / v ]_
      ( v sSet <. ( .r ` ndx ) ,
        ( x e. ( Base ` v ) , y e. ( Base ` v ) |->
          ( v gsum ( a e. ( Base ` m ) , b e. ( Base ` m ) |->
            ( i e. ( Base ` m ) |-> if (
              i = ( a ( +g ` m ) b ) ,
              ( ( x ` a ) ( .r ` r ) ( y ` b ) ) ,
              ( 0g ` r )
            ) )
          )
        ) )
      >. ) ) $.
  $}

  ${
    $d .+ m r v $.  $d .0. m r v $.  $d .x. m r v $.  $d A m r v $.
    $d B m r v $.  $d V m r v $.  $d R a b i m r v x y $.
    $d M a b i m r v x y $.
    mnringvald.1 $e |- F = ( R MndRing M ) $.
    mnringvald.2 $e |- .x. = ( .r ` R ) $.
    mnringvald.3 $e |- .0. = ( 0g ` R ) $.
    mnringvald.4 $e |- A = ( Base ` M ) $.
    mnringvald.5 $e |- .+ = ( +g ` M ) $.
    mnringvald.6 $e |- V = ( R freeLMod A ) $.
    mnringvald.7 $e |- B = ( Base ` V ) $.
    mnringvald.8 $e |- ( ph -> R e. U ) $.
    mnringvald.9 $e |- ( ph -> M e. W ) $.
    $( Value of the monoid ring function.  (Contributed by Rohan Ridenour,
       14-May-2024.) $)
    mnringvald $p |- ( ph -> F = ( V sSet <. ( .r ` ndx ) ,
      ( x e. B , y e. B |->
        ( V gsum ( a e. A , b e. A |->
          ( i e. A |-> if (
            i = ( a .+ b ) ,
            ( ( x ` a ) .x. ( y ` b ) ) ,
            .0.
          ) )
        )
      ) ) >. ) ) $=
      ( vr vm vv cmnring co cnx cmulr cfv wceq cif cmpt cmpo cgsu cop csts wcel
      cv cvv elexd cbs cfrlm cplusg c0g csb wa nfcvd ovexd simpr simpll eqtr4di
      nfv fveq2 ad2antlr eqtrd fveq2d oveqd eqeq2d ad2antrr ifbieq12d mpteq12dv
      oveq12d mpoeq123dv opeq2d csbiedf df-mnring ovex ovmpoa syl2anc eqtrid )
      AKGLUJUKZMULUMUNZBCEEMPQDDJDJVCZPVCZQVCZFUKZUOZWSBVCUNZWTCVCUNZHUKZOUPZUQ
      ZURZUSUKZURZUTZVAUKZRAGVDVBLVDVBWPXLUOAGIUEVEALNUFVEUGUHGLVDVDUIUGVCZUHVC
      ZVFUNZVGUKZUIVCZWQBCXQVFUNZXRXQPQXOXOJXOWRWSWTXNVHUNZUKZUOZXCXDXMUMUNZUKZ
      XMVIUNZUPZUQZURZUSUKZURZUTZVAUKZVJXLUJXMGUOZXNLUOZVKZUIXPYKXLVDYNUIVQYNUI
      XLVLYNXMXOVGVMYNXQXPUOZVKZXQMYJXKVAYPXQGDVGUKZMYPXQXPYQYNYOVNYPXMGXODVGYL
      YMYOVOYMXODUOYLYOYMXOLVFUNDXNLVFVRUAVPVSZWGVTUCVPZYPYIXJWQYPBCXRXRYHEEXIY
      PXRMVFUNEYPXQMVFYSWAUDVPZYTYPXQMYGXHUSYSYPPQXOXOYFDDXGYRYRYPJXOYEDXFYRYPY
      AXBYCYDXEOYPXTXAWRYMXTXAUOYLYOYMXSFWSWTYMXSLVHUNFXNLVHVRUBVPWBVSWCYLYCXEU
      OYMYOYLYBHXCXDYLYBGUMUNHXMGUMVRSVPWBWDYLYDOUOYMYOYLYDGVIUNOXMGVIVRTVPWDWE
      WFWHWGWHWIWGWJBCUIJUHUGPQWKMXKVAWLWMWNWO $.
  $}

  ${
    $d R a b i x y $.  $d M a b i x y $.
    mnringnmulrd.1 $e |- F = ( R MndRing M ) $.
    mnringnmulrd.2 $e |- E = Slot ( E ` ndx ) $.
    mnringnmulrd.4 $e |- ( E ` ndx ) =/= ( .r ` ndx ) $.
    mnringnmulrd.5 $e |- A = ( Base ` M ) $.
    mnringnmulrd.6 $e |- V = ( R freeLMod A ) $.
    mnringnmulrd.7 $e |- ( ph -> R e. U ) $.
    mnringnmulrd.8 $e |- ( ph -> M e. W ) $.
    $( Components of a monoid ring other than its ring product match its
       underlying free module.  (Contributed by Rohan Ridenour, 14-May-2024.)
       (Revised by AV, 1-Nov-2024.) $)
    mnringnmulrd $p |- ( ph -> ( E ` V ) = ( E ` F ) ) $=
      ( cfv cv co eqid vx vy va vb cnx cmulr cbs cplusg wceq c0g cmpt cmpo cgsu
      vi cif cop csts setsnid mnringvald fveq2d eqtr4id ) AHEQHUEUFQZUAUBHUGQZV
      CHUCUDBBUNBUNRUCRZUDRZGUHQZSUIVDUARQVEUBRQCUFQZSCUJQZUOUKULUMSULZUPUQSZEQ
      FEQVIVBEHKLURAFVJEAUAUBBVCVFCVGDUNFGHIVHUCUDJVGTVHTMVFTNVCTOPUSUTVA $.
  $}

  ${
    mnringbased.1 $e |- F = ( R MndRing M ) $.
    mnringbased.2 $e |- A = ( Base ` M ) $.
    mnringbased.3 $e |- V = ( R freeLMod A ) $.
    mnringbased.4 $e |- B = ( Base ` V ) $.
    mnringbased.5 $e |- ( ph -> R e. U ) $.
    mnringbased.6 $e |- ( ph -> M e. W ) $.
    $( The base set of a monoid ring.  (Contributed by Rohan Ridenour,
       14-May-2024.)  (Proof shortened by AV, 1-Nov-2024.) $)
    mnringbased $p |- ( ph -> B = ( Base ` F ) ) $=
      ( cbs cfv baseid basendxnmulrndx mnringnmulrd eqtrid ) ACHPQFPQMABDEPFGHI
      JRSKLNOTUA $.
  $}

  ${
    mnringbaserd.1 $e |- F = ( R MndRing M ) $.
    mnringbaserd.2 $e |- B = ( Base ` F ) $.
    mnringbaserd.3 $e |- A = ( Base ` M ) $.
    mnringbaserd.4 $e |- V = ( R freeLMod A ) $.
    mnringbaserd.5 $e |- ( ph -> R e. U ) $.
    mnringbaserd.6 $e |- ( ph -> M e. W ) $.
    $( The base set of a monoid ring.  Converse of ~ mnringbased .
       (Contributed by Rohan Ridenour, 14-May-2024.) $)
    mnringbaserd $p |- ( ph -> B = ( Base ` V ) ) $=
      ( cbs cfv eqid mnringbased eqtr4id ) ACFPQHPQZKABUADEFGHIJLMUARNOST $.
  $}

  ${
    mnringelbased.1 $e |- F = ( R MndRing M ) $.
    mnringelbased.2 $e |- B = ( Base ` F ) $.
    mnringelbased.3 $e |- A = ( Base ` M ) $.
    mnringelbased.4 $e |- C = ( Base ` R ) $.
    mnringelbased.5 $e |- .0. = ( 0g ` R ) $.
    mnringelbased.6 $e |- ( ph -> R e. U ) $.
    mnringelbased.7 $e |- ( ph -> M e. W ) $.
    $( Membership in the base set of a monoid ring.  (Contributed by Rohan
       Ridenour, 14-May-2024.) $)
    mnringelbased $p |- ( ph ->
      ( X e. B <-> ( X e. ( C ^m A ) /\ X finSupp .0. ) ) ) $=
      ( wcel co cfrlm cbs cfv cmap cfsupp wbr wa eqid mnringbaserd eleq2d fvexi
      cvv wb frlmelbas sylancl bitrd ) AJCSJEBUATZUBUCZSZJDBUDTSJKUEUFUGZACURJA
      BCEFGHUQILMNUQUHZQRUIUJAEFSBULSUSUTUMQBHUBNUKUREUQBDFULJKVAOPURUHUNUOUP
      $.
  $}

  ${
    mnringbasefd.1 $e |- F = ( R MndRing M ) $.
    mnringbasefd.2 $e |- B = ( Base ` F ) $.
    mnringbasefd.3 $e |- A = ( Base ` M ) $.
    mnringbasefd.4 $e |- C = ( Base ` R ) $.
    mnringbasefd.5 $e |- ( ph -> R e. U ) $.
    mnringbasefd.6 $e |- ( ph -> M e. W ) $.
    mnringbasefd.7 $e |- ( ph -> X e. B ) $.
    $( Elements of a monoid ring are functions.  (Contributed by Rohan
       Ridenour, 14-May-2024.) $)
    mnringbasefd $p |- ( ph -> X : A --> C ) $=
      ( cmap co wcel wf c0g cfv cfsupp wbr wa mnringelbased mpbid simpld elmapi
      eqid syl ) AJDBRSTZBDJUAAUMJEUBUCZUDUEZAJCTUMUOUFQABCDEFGHIJUNKLMNUNUKOPU
      GUHUIJDBUJUL $.
  $}

  ${
    mnringbasefsuppd.1 $e |- F = ( R MndRing M ) $.
    mnringbasefsuppd.2 $e |- B = ( Base ` F ) $.
    mnringbasefsuppd.3 $e |- .0. = ( 0g ` R ) $.
    mnringbasefsuppd.4 $e |- ( ph -> R e. U ) $.
    mnringbasefsuppd.5 $e |- ( ph -> M e. W ) $.
    mnringbasefsuppd.6 $e |- ( ph -> X e. B ) $.
    $( Elements of a monoid ring are finitely supported.  (Contributed by Rohan
       Ridenour, 14-May-2024.) $)
    mnringbasefsuppd $p |- ( ph -> X finSupp .0. ) $=
      ( cbs cfv cmap wcel eqid co cfsupp wbr wa mnringelbased mpbid simprd ) AH
      CPQZFPQZRUASZHIUBUCZAHBSUJUKUDOAUIBUHCDEFGHIJKUITUHTLMNUEUFUG $.
  $}

  ${
    mnringaddgd.1 $e |- F = ( R MndRing M ) $.
    mnringaddgd.2 $e |- A = ( Base ` M ) $.
    mnringaddgd.3 $e |- V = ( R freeLMod A ) $.
    mnringaddgd.4 $e |- ( ph -> R e. U ) $.
    mnringaddgd.5 $e |- ( ph -> M e. W ) $.
    $( The additive operation of a monoid ring.  (Contributed by Rohan
       Ridenour, 14-May-2024.)  (Proof shortened by AV, 1-Nov-2024.) $)
    mnringaddgd $p |- ( ph -> ( +g ` V ) = ( +g ` F ) ) $=
      ( cplusg plusgid plusgndxnmulrndx mnringnmulrd ) ABCDNEFGHIOPJKLMQ $.
  $}

  ${
    $d ph x y $.  $d F x y $.  $d V x y $.
    mnring0gd.1 $e |- F = ( R MndRing M ) $.
    mnring0gd.2 $e |- A = ( Base ` M ) $.
    mnring0gd.3 $e |- V = ( R freeLMod A ) $.
    mnring0gd.4 $e |- ( ph -> R e. U ) $.
    mnring0gd.5 $e |- ( ph -> M e. W ) $.
    $( The additive identity of a monoid ring.  (Contributed by Rohan Ridenour,
       14-May-2024.) $)
    mnring0gd $p |- ( ph -> ( 0g ` V ) = ( 0g ` F ) ) $=
      ( vx vy cbs cfv cv wcel cplusg eqid mnringbased wa mnringaddgd grpidpropd
      eqidd oveqdr ) ANOGPQZGEAUHUFABUHCDEFGHIJKUHUALMUBANRUHSORUHSUCNOGTQETQAB
      CDEFGHIJKLMUDUGUE $.
  $}

  ${
    mnring0g2d.1 $e |- F = ( R MndRing M ) $.
    mnring0g2d.2 $e |- .0. = ( 0g ` R ) $.
    mnring0g2d.3 $e |- A = ( Base ` M ) $.
    mnring0g2d.4 $e |- ( ph -> R e. Ring ) $.
    mnring0g2d.5 $e |- ( ph -> M e. W ) $.
    $( The additive identity of a monoid ring.  (Contributed by Rohan Ridenour,
       14-May-2024.) $)
    mnring0g2d $p |- ( ph -> ( A X. { .0. } ) = ( 0g ` F ) ) $=
      ( csn cxp cfrlm c0g cfv crg wcel cvv co wceq cbs fvexi eqid frlm0 sylancl
      mnring0gd eqtrd ) ABGMNZCBOUAZPQZDPQACRSBTSUJULUBKBEUCJUDCUKBTGUKUEZIUFUG
      ABCRDEUKFHJUMKLUHUI $.
  $}

  ${
    $d ph x y $.  $d A a b x y $.  $d R a b i x y $.  $d M a b i x y $.
    mnringmulrd.1 $e |- F = ( R MndRing M ) $.
    mnringmulrd.2 $e |- B = ( Base ` F ) $.
    mnringmulrd.3 $e |- .x. = ( .r ` R ) $.
    mnringmulrd.4 $e |- .0. = ( 0g ` R ) $.
    mnringmulrd.5 $e |- A = ( Base ` M ) $.
    mnringmulrd.6 $e |- .+ = ( +g ` M ) $.
    mnringmulrd.7 $e |- ( ph -> R e. U ) $.
    mnringmulrd.8 $e |- ( ph -> M e. W ) $.
    $( The ring product of a monoid ring.  (Contributed by Rohan Ridenour,
       14-May-2024.) $)
    mnringmulrd $p |- ( ph ->
      ( x e. B , y e. B |->
        ( F gsum ( a e. A , b e. A |->
          ( i e. A |-> if (
            i = ( a .+ b ) ,
            ( ( x ` a ) .x. ( y ` b ) ) ,
            .0.
          ) )
        )
      ) ) = ( .r ` F ) ) $=
      ( cv co wceq cfv cif cmpt cmpo cgsu cfrlm cbs cmulr eqid mnringbaserd cvv
      wcel fvexi mpoex a1i cmnring ovexi ovex eqtr3id cplusg mnringaddgd eqcomd
      gsumpropd mpoeq123dv cnx csts fvex mulridx setsid mp2an mnringvald fveq2d
      cop eqtr4id eqtrd ) ABCEEKOPDDJDJUEOUEZPUEZFUFUGWCBUEUHWDCUEUHHUFNUIUJZUK
      ZULUFZUKBCGDUMUFZUNUHZWIWHWFULUFZUKZKUOUHZABCEEWGWIWIWJADEGIKLWHMQRUAWHUP
      ZUCUDUQZWNAWFKWHURURURWFURUSAOPDDWEDLUNUAUTZWOVAVBKURUSAKGLVCQVDVBWHURUSZ
      AGDUMVEZVBAKUNUHEWIRWNVFAWHVGUHKVGUHADGIKLWHMQUAWMUCUDVHVIVJVKAWKWHVLUOUH
      WKVTVMUFZUOUHZWLWPWKURUSWKWSUGWQBCWIWIWJWHUNVNZWTVAURWKUOURWHVOVPVQAKWRUO
      ABCDWIFGHIJKLWHMNOPQSTUAUBWMWIUPUCUDVRVSWAWB $.
  $}

  ${
    mnringscad.1 $e |- F = ( R MndRing M ) $.
    mnringscad.2 $e |- ( ph -> R e. U ) $.
    mnringscad.3 $e |- ( ph -> M e. W ) $.
    $( The scalar ring of a monoid ring.  (Contributed by Rohan Ridenour,
       14-May-2024.)  (Proof shortened by AV, 1-Nov-2024.) $)
    mnringscad $p |- ( ph -> R = ( Scalar ` F ) ) $=
      ( cbs cfv cfrlm co csca wcel cvv wceq fvex eqid frlmsca scandxnmulrndx
      sylancl scaid mnringnmulrd eqtrd ) ABBEJKZLMZNKZDNKABCOUFPOBUHQHEJRBUGUFC
      PUGSZTUBAUFBCNDEUGFGUCUAUFSUIHIUDUE $.
  $}

  ${
    mnringvscad.1 $e |- F = ( R MndRing M ) $.
    mnringvscad.2 $e |- B = ( Base ` M ) $.
    mnringvscad.3 $e |- V = ( R freeLMod B ) $.
    mnringvscad.4 $e |- ( ph -> R e. U ) $.
    mnringvscad.5 $e |- ( ph -> M e. W ) $.
    $( The scalar product of a monoid ring.  (Contributed by Rohan Ridenour,
       14-May-2024.)  (Proof shortened by AV, 1-Nov-2024.) $)
    mnringvscad $p |- ( ph -> ( .s ` V ) = ( .s ` F ) ) $=
      ( cvsca vscaid vscandxnmulrndx mnringnmulrd ) ABCDNEFGHIOPJKLMQ $.
  $}

  ${
    $d ph x y $.  $d R x y $.  $d F x y $.  $d M x y $.
    mnringlmodd.1 $e |- F = ( R MndRing M ) $.
    mnringlmodd.2 $e |- ( ph -> R e. Ring ) $.
    mnringlmodd.3 $e |- ( ph -> M e. U ) $.
    $( Monoid rings are left modules.  (Contributed by Rohan Ridenour,
       14-May-2024.) $)
    mnringlmodd $p |- ( ph -> F e. LMod ) $=
      ( vx vy cbs cfv clmod wcel crg cvv eqid syl2anc cv wa cfrlm cplusg oveqdr
      fvexd frlmlmod eqidd mnringbased mnringaddgd csca wceq frlmsca mnringscad
      co cvsca mnringvscad lmodpropd mpbid ) ABEKLZUAUMZMNZDMNABONZURPNZUTGAEKU
      DZBUSURPUSQZUERAIJUSKLZBKLZBUSDAVEUFAURVEBODEUSCFURQZVDVEQGHUGAISZVENJSVE
      NZTIJUSUBLDUBLAURBODEUSCFVGVDGHUHUCAVAVBBUSUILUJGVCBUSUROPVDUKRABODECFGHU
      LVFQAVHVFNVITIJUSUNLDUNLAURBODEUSCFVGVDGHUOUCUPUQ $.
  $}

  ${
    $d ph x y $.  $d .+ x y $.  $d .xb x y $.  $d .0b x y $.  $d F x y $.
    $d A a b x y $.  $d R a b i x y $.  $d M a b i x y $.  $d X a b i x y $.
    $d Y a b i x y $.
    mnringmulrvald.1 $e |- F = ( R MndRing M ) $.
    mnringmulrvald.2 $e |- B = ( Base ` F ) $.
    mnringmulrvald.3 $e |- .xb = ( .r ` R ) $.
    mnringmulrvald.4 $e |- .0b = ( 0g ` R ) $.
    mnringmulrvald.5 $e |- A = ( Base ` M ) $.
    mnringmulrvald.6 $e |- .+ = ( +g ` M ) $.
    mnringmulrvald.7 $e |- .x. = ( .r ` F ) $.
    mnringmulrvald.8 $e |- ( ph -> R e. U ) $.
    mnringmulrvald.9 $e |- ( ph -> M e. W ) $.
    mnringmulrvald.10 $e |- ( ph -> X e. B ) $.
    mnringmulrvald.11 $e |- ( ph -> Y e. B ) $.
    $( Value of multiplication in a monoid ring.  (Contributed by Rohan
       Ridenour, 14-May-2024.) $)
    mnringmulrvald $p |- ( ph -> ( X .x. Y ) =
      ( F gsum ( a e. A , b e. A |->
        ( i e. A |-> if (
          i = ( a .+ b ) ,
          ( ( X ` a ) .xb ( Y ` b ) ) ,
          .0b
        ) )
      ) ) ) $=
      ( vx vy cv co wceq cfv cif cmpt cmpo cvv cmulr mnringmulrd eqtr4di eqcomd
      cgsu fveq1 oveqan12d ifeq1d mpteq2dv mpoeq3dv oveq2d adantl ovexd ovmpod
      wa ) AUIUJMNCCJPQBBIBIUKPUKZQUKZDULUMZVNUIUKZUNZVOUJUKZUNZFULZOUOZUPZUQZV
      CULZJPQBBIBVPVNMUNZVONUNZFULZOUOZUPZUQZVCULZGURAUIUJCCWEUQZGAWMJUSUNGAUIU
      JBCDEFHIJKLOPQRSTUAUBUCUEUFUTUDVAVBVQMUMZVSNUMZVMZWEWLUMAWPWDWKJVCWPPQBBW
      CWJWPIBWBWIWPVPWAWHOWNWOVRWFVTWGFVNVQMVDVOVSNVDVEVFVGVHVIVJUGUHAJWKVCVKVL
      $.
  $}

  ${
    $d B a b $.  $d F a b p $.  $d ph a b i p $.  $d A a b i p $.
    $d R a b i p $.  $d M a b i p $.  $d X a b i p $.  $d Y a b i p $.
    mnringmulrcld.2 $e |- F = ( R MndRing M ) $.
    mnringmulrcld.3 $e |- B = ( Base ` F ) $.
    mnringmulrcld.1 $e |- A = ( Base ` M ) $.
    mnringmulrcld.4 $e |- .x. = ( .r ` F ) $.
    mnringmulrcld.5 $e |- ( ph -> R e. Ring ) $.
    mnringmulrcld.6 $e |- ( ph -> M e. U ) $.
    mnringmulrcld.7 $e |- ( ph -> X e. B ) $.
    mnringmulrcld.8 $e |- ( ph -> Y e. B ) $.
    $( Monoid rings are closed under multiplication.  (Contributed by Rohan
       Ridenour, 14-May-2024.) $)
    mnringmulrcld $p |- ( ph -> ( X .x. Y ) e. B ) $=
      ( va wcel vb vi vp co cv cplusg cfv wceq cmulr c0g cif cmpt cmpo cgsu crg
      eqid mnringmulrvald cxp cvv clmod ccmn mnringlmodd lmodcmn syl fvexi xpex
      cbs a1i wral wf w3a cmap cfsupp wbr 3ad2ant1 mnringbasefd simp2 ffvelcdmd
      wa simp3 ringcl syl3anc ifcld adantr fmpttd elmap sniffsupp mnringelbased
      ring0cl sylibr mpbird 3expb ralrimivva sylib csupp mpoex mnringbasefsuppd
      jca fmpo ffnd cfn fsuppimpd xpfi syl2anc cop wo elxpi simpl 2eximi adantl
      wex nfv nfmpo1 nfcv nffv nfeq nfor nfmpo2 eqeltrrd opelxp wn ianor wne wi
      wfn wb elsuppfn biimprd mpand necon1bd orim12d imp oveq1 ringlz sylan9eqr
      sylan2b oveq2 ringrz eqidd exlimd jaodan csn fconstmpt mnring0g2d eqtr3id
      ifeqda mpteq2dv eqtrd syldan ex orrd 3adant3 eleq1 bitrdi 3ad2ant3 simp2l
      simp2r mptex fvmpopr2d mpd3an23 eqeq1d orbi12d syld3an2 3expia mpd gsumcl
      finnzfsuppd eqeltrd ) AIJEUDGSUABBUBBUBUEZSUEZUAUEZHUFUGZUDZUHZUVJIUGZUVK
      JUGZDUIUGZUDZDUJUGZUKZULZUMZUNUDCABCUVLDUVQEUOUBGHFIJUVSSUAKLUVQUPZUVSUPZ
      MUVLUPNOPQRUQABBURZCUWBGUSGUJUGZLUWFUPZAGUTTGVATADFGHKOPVBGVCVDUWEUSTABBB
      HVGMVEZUWHVFVHAUWACTZUABVISBVIUWECUWBVJAUWISUABBAUVJBTZUVKBTZUWIAUWJUWKVK
      ZUWIUWADVGUGZBVLUDTZUWAUVSVMVNZVSUWLUWNUWOUWLBUWMUWAVJUWNUWLUBBUVTUWMUWLU
      VTUWMTUVIBTUWLUVNUVRUVSUWMUWLDUOTZUVOUWMTZUVPUWMTZUVRUWMTAUWJUWPUWKOVOZUW
      LBUWMUVJIAUWJBUWMIVJUWKABCUWMDUOGHFIKLMUWMUPZOPQVPZVOAUWJUWKVQZVRZUWLBUWM
      UVKJAUWJBUWMJVJUWKABCUWMDUOGHFJKLMUWTOPRVPZVOAUWJUWKVTZVRZUWMDUVQUVOUVPUW
      TUWCWAWBUWLUWPUVSUWMTUWSUWMDUVSUWTUWDWIVDZWCWDWEUWMBUWAUWMDVGUWTVEUWHWFWJ
      UWLUBUVRUWABUSUWMUVMUVSBUSTZUWLUWHVHUXGUWAUPWGWRUWLBCUWMDUOGHFUWAUVSKLMUW
      TUWDUWSAUWJHFTUWKPVOWHWKWLWMSUABBUWACUWBUWBUPWSWNZAUCIUVSWOUDZJUVSWOUDZUR
      ZUWEUSUWBUSUWFUWBUSTASUABBUWAUWHUWHWPVHAUWECUWBUXIWTUWFUSTAUWFGUJUWGVEVHA
      UXJXATUXKXATUXLXATAIUVSACDUOGHFIUVSKLUWDOPQWQXBAJUVSACDUOGHFJUVSKLUWDOPRW
      QXBUXJUXKXCXDAUCUEZUWETZVSZUXMUVJUVKXEZUHZUAXKZSXKZUXMUXLTZUXMUWBUGZUWFUH
      ZXFZUXNUXSAUXNUXQUWJUWKVSZVSZUAXKSXKUXSSUAUXMBBXGUYEUXQSUAUXQUYDXHXIVDXJU
      XOUXRUYCSUXOSXLUXTUYBSUXTSXLSUYAUWFSUXMUWBSUABBUWAXMSUXMXNXOSUWFXNXPXQUXO
      UXQUYCUAUXOUAXLUXTUYBUAUXTUAXLUAUYAUWFUAUXMUWBSUABBUWAXRUAUXMXNXOUAUWFXNX
      PXQAUXNUXQUYCAUYDUXNUXQUYCAUXNUXQVKZUXPUWETUYDUYFUXMUXPUWEAUXNUXQVTAUXNUX
      QVQXSUVJUVKBBXTWNAUYDUXQVKZUYCUVJUXJTZUVKUXKTZVSZUWAUWFUHZXFZAUYDUYLUXQAU
      WJUWKUYLUWLUYJUYKUWLUYJYAZUYKUWLUYMUVOUVSUHZUVPUVSUHZXFZUYKUYMUWLUYHYAZUY
      IYAZXFZUYPUYHUYIYBUWLUYSUYPUWLUYQUYNUYRUYOUWLUYHUVOUVSUWLUWJUVOUVSYCZUYHU
      XBAUWJUWJUYTVSZUYHYDUWKAUYHVUAAIBYEUXHUVSUSTZUYHVUAYFABUWMIUXAWTUXHAUWHVH
      ZVUBAUVSDUJUWDVEVHZUVJIUSUSBUVSYGWBYHVOYIYJUWLUYIUVPUVSUWLUWKUVPUVSYCZUYI
      UXEAUWJUWKVUEVSZUYIYDUWKAUYIVUFAJBYEUXHVUBUYIVUFYFABUWMJUXDWTVUCVUDUVKJUS
      USBUVSYGWBYHVOYIYJYKYLYPUWLUYPVSZUWAUBBUVSULZUWFVUGUBBUVTUVSVUGUVNUVRUVSU
      VSVUGUVRUVSUHZUVNUWLUYNVUIUYOUYNUWLUVRUVSUVPUVQUDZUVSUVOUVSUVPUVQYMUWLUWP
      UWRVUJUVSUHUWSUXFUWMDUVQUVPUVSUWTUWCUWDYNXDYOUYOUWLUVRUVOUVSUVQUDZUVSUVPU
      VSUVOUVQYQUWLUWPUWQVUKUVSUHUWSUXCUWMDUVQUVOUVSUWTUWCUWDYRXDYOUUAWDVUGUVNY
      AVSUVSYSUUFUUGUWLVUHUWFUHZUYPAUWJVULUWKAVUHBUVSUUBURUWFUBBUVSUUCABDGHFUVS
      KUWDMOPUUDUUEVOWDUUHUUIUUJUUKWLUULUYGUXTUYJUYBUYKUXQAUXTUYJYFUYDUXQUXTUXP
      UXLTUYJUXMUXPUXLUUMUVJUVKUXJUXKXTUUNUUOUYGUYAUWAUWFUYGUWJUWKUYAUWAUHAUWJU
      WKUXQUUPAUWJUWKUXQUUQUYGBBUWAUXMUWBUSSUAUYGUWBYSAUYDUXQVTUWAUSTUYGUWJUWKV
      KUBBUVTUWHUURVHUUSUUTUVAUVBWKUVCUVDYTYTUVEUVGUVFUVH $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Shorter primitive equivalent of ax-groth
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Grothendieck universes are closed under collection
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    gru0eld.1 $e |- ( ph -> G e. Univ ) $.
    gru0eld.2 $e |- ( ph -> A e. G ) $.
    $( A nonempty Grothendieck universe contains the empty set.  (Contributed
       by Rohan Ridenour, 11-Aug-2023.) $)
    gru0eld $p |- ( ph -> (/) e. G ) $=
      ( cgru wcel c0 wss 0ss a1i gruss syl3anc ) ACFGBCGHBIZHCGDENABJKBHCLM $.
  $}

  ${
    grusucd.1 $e |- ( ph -> G e. Univ ) $.
    grusucd.2 $e |- ( ph -> A e. G ) $.
    $( Grothendieck universes are closed under ordinal successor.  (Contributed
       by Rohan Ridenour, 9-Aug-2023.) $)
    grusucd $p |- ( ph -> suc A e. G ) $=
      ( csuc csn cun df-suc cgru wcel grusn syl2anc gruun syl3anc eqeltrid ) AB
      FBBGZHZCBIACJKZBCKZQCKZRCKDEASTUADEBCLMBQCNOP $.
  $}

  ${
    r1rankcld.1 $e |- ( ph -> A e. ( R1 ` R ) ) $.
    $( Any rank of the cumulative hierarchy is closed under the rank function.
       (Contributed by Rohan Ridenour, 11-Aug-2023.) $)
    r1rankcld $p |- ( ph -> ( rank ` A ) e. ( R1 ` R ) ) $=
      ( cr1 cdm wcel crnk cfv wa wss onssr1 adantl rankr1ai adantr sseldd wn c0
      syl noel a1i ndmfv neleqtrrd pm2.21dd pm2.61dan ) ACEFGZBHIZCEIZGZAUFJCUH
      UGUFCUHKACLMAUGCGZUFABUHGZUJDBCNSOPAUFQZJUKUIAUKULDOULUKQAULUHRBBRGQULBTU
      ACEUBUCMUDUE $.
  $}

  ${
    $d ph x y $.  $d x y A $.  $d x y G $.
    grur1cld.1 $e |- ( ph -> G e. Univ ) $.
    grur1cld.2 $e |- ( ph -> A e. G ) $.
    $( Grothendieck universes are closed under the cumulative hierarchy
       function.  (Contributed by Rohan Ridenour, 8-Aug-2023.) $)
    grur1cld $p |- ( ph -> ( R1 ` A ) e. G ) $=
      ( vy con0 wcel cr1 cfv wa adantr wi c0 eleq1 fveq2 eleq1d imbi12d syl3anc
      wceq vx cv csuc r10 gru0eld eqeltrid a1d w3a simpl1 simpl2 cgru wss simpr
      syl sssucid a1i gruss mpd cpw r1suc 3ad2ant2 3ad2ant1 simp3 grupw syl2anc
      simpl3 eqeltrd wlim wral ciun r1lim simpl1l word limord ordelss ralrimiva
      ex ralim sylc gruiun tfindsd cdm r1fnon fndmi eleq2i ndmfv sylnbir adantl
      wn pm2.61dan ) ABGHZBIJZCHZAWKKZBCHZWMAWOWKELWNUAUBZCHZWPIJZCHZMNCHZNIJZC
      HZMFUBZCHZXCIJZCHZMZXCUCZCHZXHIJZCHZMWOWMMUAFBWPNTZWQWTWSXBWPNCOXLWRXACWP
      NIPQRWPXCTZWQXDWSXFWPXCCOXMWRXECWPXCIPQRWPXHTZWQXIWSXKWPXHCOXNWRXJCWPXHIP
      QRWPBTZWQWOWSWMWPBCOXOWRWLCWPBIPQRWNXBWTAXBWKAXANCUDABCDEUEZUFLUGWNXCGHZX
      GUHZXIXKXRXIKZWNXQXFXKWNXQXGXIUIZWNXQXGXIUJXSXDXFXSCUKHZXIXCXHULZXDXSWNYA
      XTAYAWKDLZUNXRXIUMYBXSXCUOUPXHXCCUQSWNXQXGXIVFURWNXQXFUHZXJXEUSZCXQWNXJYE
      TXFXCUTVAYDYAXFYECHWNXQYAXFYCVBWNXQXFVCXECVDVEVGSVQWNWPVHZXGFWPVIZUHZWQWS
      YHWQKZWRFWPXEVJZCYIWQYFWRYJTYHWQUMZWNYFYGWQUJZFWPCVKVEYIYAWQXFFWPVIZYJCHY
      IWNYAWNYFYGWQUIYCUNYKYIYGXDFWPVIZYMWNYFYGWQVFYIAYFWQYNAWKYFYGWQVLYLYKAYFW
      QUHZXDFWPYOXCWPHZKZYAWQXCWPULZXDYQAYAAYFWQYPUIDUNAYFWQYPVFYQWPVMZYPYRYQYF
      YSAYFWQYPUJWPVNUNYOYPUMWPXCVOVEWPXCCUQSVPSXDXFFWPVRVSFWPXECVTSVGVQAWKUMWA
      URAWKWIZKWLNCYTWLNTZAWKBIWBZHUUAUUBGBGIWCWDWEBIWFWGWHAWTYTXPLVGWJ $.
  $}

  ${
    grurankcld.1 $e |- ( ph -> G e. Univ ) $.
    grurankcld.2 $e |- ( ph -> A e. G ) $.
    $( Grothendieck universes are closed under the rank function.  (Contributed
       by Rohan Ridenour, 9-Aug-2023.) $)
    grurankcld $p |- ( ph -> ( rank ` A ) e. G ) $=
      ( crnk cfv con0 cin cr1 cgru wcel cima cuni wceq cvv elexd eleqtrrdi eqid
      unir1 grur1 syl2anc eleqtrd r1rankcld eleqtrrd ) ABFGCHIZJGZCABUFABCUGEAC
      KLCJHMNZLCUGODACPUHACKDQTRUFCUFSUAUBZUCUDUIUE $.
  $}

  ${
    grurankrcld.1 $e |- ( ph -> G e. Univ ) $.
    grurankrcld.2 $e |- ( ph -> ( rank ` A ) e. G ) $.
    grurankrcld.3 $e |- ( ph -> A e. V ) $.
    $( If a Grothendieck universe contains a set's rank, it contains that set.
       (Contributed by Rohan Ridenour, 9-Aug-2023.) $)
    grurankrcld $p |- ( ph -> A e. G ) $=
      ( cgru wcel crnk cfv cr1 wss grur1cld r1rankid syl gruss syl3anc ) ACHIBJ
      KZLKZCIBTMZBCIEASCEFNABDIUAGBDOPTBCQR $.
  $}

  ${
    gruscottcld.1 $e |- ( ph -> G e. Univ ) $.
    gruscottcld.2 $e |- ( ph -> B e. G ) $.
    gruscottcld.3 $e |- ( ph -> B e. Scott A ) $.
    $( If a Grothendieck universe contains an element of a Scott's trick set,
       it contains the Scott's trick set.  (Contributed by Rohan Ridenour,
       11-Aug-2023.) $)
    gruscottcld $p |- ( ph -> Scott A e. G ) $=
      ( cscott cvv crnk csuc scottrankd grurankcld grusucd eqeltrd wcel scottex
      cfv a1i grurankrcld ) ABHZDIEAUAJRCJRZKDABCGLAUBDEACDEFMNOUAIPABQST $.
  $}

  $c Coll $.

  $( Extend class notation with the collection operation. $)
  ccoll $a class ( F Coll A ) $.

  ${
    $d x F $.  $d x A $.
    $( Define the collection operation.  This is similar to the image set
       operation ` " ` , but it uses Scott's trick to ensure the output is
       always a set.  (Contributed by Rohan Ridenour, 11-Aug-2023.) $)
    df-coll $a |- ( F Coll A ) = U_ x e. A Scott ( F " { x } ) $.
  $}

  ${
    $d x A $.  $d x y F $.
    $( Alternate definition of the collection operation.  (Contributed by Rohan
       Ridenour, 11-Aug-2023.) $)
    dfcoll2 $p |- ( F Coll A ) = U_ x e. A Scott { y | x F y } $=
      ( ccoll csn cima cscott ciun wbr cab df-coll wcel imasng scotteqd iuneq2i
      cv eqtri ) CDEACDAQZFGZHZIACSBQDJBKZHZIACDLACUAUCSCMTUBBSCDNOPR $.
  $}

  ${
    $d ph x $.  $d x A $.  $d x B $.  $d x F $.  $d x G $.
    colleq12d.1 $e |- ( ph -> F = G ) $.
    colleq12d.2 $e |- ( ph -> A = B ) $.
    $( Equality theorem for the collection operation.  (Contributed by Rohan
       Ridenour, 11-Aug-2023.) $)
    colleq12d $p |- ( ph -> ( F Coll A ) = ( G Coll B ) ) $=
      ( vx csn cima cscott ciun ccoll imaeq1d scotteqd iuneq12d df-coll 3eqtr4g
      cv ) AHBDHSIZJZKZLHCETJZKZLBDMCEMAHBCUBUDGAUAUCADETFNOPHBDQHCEQR $.
  $}

  ${
    $( Equality theorem for the collection operation.  (Contributed by Rohan
       Ridenour, 11-Aug-2023.) $)
    colleq1 $p |- ( F = G -> ( F Coll A ) = ( G Coll A ) ) $=
      ( wceq id eqidd colleq12d ) BCDZAABCHEHAFG $.
  $}

  ${
    $( Equality theorem for the collection operation.  (Contributed by Rohan
       Ridenour, 11-Aug-2023.) $)
    colleq2 $p |- ( A = B -> ( F Coll A ) = ( F Coll B ) ) $=
      ( wceq eqidd id colleq12d ) ABDZABCCHCEHFG $.
  $}

  ${
    $d x y $.  $d y A $.  $d y F $.
    nfcoll.1 $e |- F/_ x F $.
    nfcoll.2 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for the collection operation.
       (Contributed by Rohan Ridenour, 11-Aug-2023.) $)
    nfcoll $p |- F/_ x ( F Coll A ) $=
      ( vy ccoll csn cima cscott ciun df-coll nfcv nfima nfscott nfiun nfcxfr
      cv ) ABCGFBCFRHZIZJZKFBCLFABUAEATACSDASMNOPQ $.
  $}

  ${
    $d ph x $.  $d x A $.  $d x F $.
    collexd.1 $e |- ( ph -> A e. V ) $.
    $( The output of the collection operation is a set if the second input is.
       (Contributed by Rohan Ridenour, 11-Aug-2023.) $)
    collexd $p |- ( ph -> ( F Coll A ) e. _V ) $=
      ( vx ccoll cv csn cima cscott ciun cvv df-coll wcel scottex a1i ralrimivw
      wral iunexg syl2anc eqeltrid ) ABCGFBCFHIJZKZLZMFBCNABDOUDMOZFBSUEMOEAUFF
      BUFAUCPQRFBUDDMTUAUB $.
  $}

  ${
    $d x y z F $.  $d x y z A $.
    cpcolld.1 $e |- ( ph -> x e. A ) $.
    cpcolld.2 $e |- ( ph -> x F y ) $.
    $( Property of the collection operation.  (Contributed by Rohan Ridenour,
       11-Aug-2023.) $)
    cpcolld $p |- ( ph -> E. y e. ( F Coll A ) x F y ) $=
      ( vz cv ccoll wcel wbr wa wex wrex cab cscott vex breq2 sylibr 19.8ad jca
      elab ciun ssiun2 dfcoll2 sseqtrrdi sselda elscottab adantl ex eximdv sylc
      scotteld df-rex ) ACIZDEJZKZBIZUPELZMZCNZUTCUQOAUSDKZUPUSHIZELZHPZQZKZCNV
      BFACVFAUPVFKZCAUTVIGVEUTHUPCRVDUPUSESZUCTUAUNVCVHVACVCVHVAVCVHMURUTVCVGUQ
      UPVCVGBDVGUDUQBDVGUEBHDEUFUGUHVHUTVCVEUTHCVJUIUJUBUKULUMUTCUQUOT $.
  $}

  ${
    $d ph a $.  $d x y F a $.  $d x y A a $.
    cpcoll2d.1 $e |- ( ph -> x e. A ) $.
    cpcoll2d.2 $e |- ( ph -> E. y x F y ) $.
    $( ~ cpcolld with an extra existential quantifier.  (Contributed by Rohan
       Ridenour, 12-Aug-2023.) $)
    cpcoll2d $p |- ( ph -> E. y e. ( F Coll A ) x F y ) $=
      ( va cv wbr ccoll wrex wex breq2 cbvexvw sylibr wa wcel adantr simpr
      cpcolld cbvrexvw sylib exlimddv ) ABIZHIZEJZUECIZEJZCDEKZLZHAUICMUGHMGUGU
      IHCUFUHUEENZOPAUGQZUGHUJLUKUMBHDEAUEDRUGFSAUGTUAUGUIHCUJULUBUCUD $.
  $}

  $( Violates a DV condition on ~ cpcolld.
  @{
    @d ph a @.  @d x y z a @.
    @( ~ cp with an explicit witness, constructed using ` Coll ` .
       (Contributed by Rohan Ridenour, 11-Aug-2023.) @)
    cpcoll @p
      |- A. x e. z ( E. y ph -> E. y e. ( { <. x , y >. | ph } Coll z ) ph ) @=
  ( va wex cv copab ccoll wrex wsb wel nfs1v nfex wceq ax6e sbequ12r wbr nfcv
  wi biimprcd eximdv mpi exlimi wa simpl nfopab2 nfbr weq cop wcel df-br opabid
  bitri breq2 bitr3id biimpi adantl cpcolld nfcoll nfv cbvrexf sylibr rexbii ex
  sbiev sylib exlimdv syl5 rgen ) ACFZACDGZABCHZIZJZTBVLVKACEKZEFZBDLZVOAVQCVPC
  EACEMNAEGZCGZOZEFVQECPAWAVPEWAVPAAECQUAUBUCUDVRVPVOEVRVPVOVRVPUEZBGZVTVMRZCVN
  JZVOWBWCVSVMRZEVNJWEWBBEVLVMVRVPUFVPWFVRVPWFAWFCECWCVSVMCWCSABCUGZCVSSUHZAWDC
  EUIWFWDWCVTUJVMUKAWCVTVMULABCUMUNZVTVSWCVMUOZUPVFUQURUSWDWFCEVNCVLVMWGCVLSUTE
  VNSWDEVAWHWJVBVCWDACVNWIVDVGVEVHVIVJ @.
  @}

  @{
    @d ph w @.  @d x y z w @.
    @( Alternate proof of ~ cp using ~ cpcoll .  (Contributed by Rohan
       Ridenour, 11-Aug-2023.)  (Proof modification is discouraged.)  Use ~ cp
       instead.  (New usage is discouraged.) @)
    rr-cp @p |- E. w A. x e. z ( E. y ph -> E. y e. w ph ) @=
      ( wex cv wrex wral copab ccoll cvv wcel elex collexd elv wceq nfcv nfcoll
      wi nfopab1 nfeq2 nfopab2 rexeqf imbi2d ralbid cpcoll ceqsexv2d ) ACFZACEG
      ZHZTZBDGZIUIACUMABCJZKZHZTZBUMIEUOUOLMDUMLMUMUNLUMLNOPUJUOQZULUQBUMBUJUOB
      UMUNABCUABUMRSUBURUKUPUIACUJUOCUJRCUMUNABCUCCUMRSUDUEUFABCDUGUH @.
  @}
  $)

  ${
    $d ph x z $.  $d x z G $.  $d x y z A $.  $d x y z F $.
    grucollcld.1 $e |- ( ph -> G e. Univ ) $.
    grucollcld.2 $e |- ( ph -> F C_ ( G X. G ) ) $.
    grucollcld.3 $e |- ( ph -> A e. G ) $.
    $( A Grothendieck universe contains the output of a collection operation
       whenever its left input is a relation on the universe, and its right
       input is in the universe.  (Contributed by Rohan Ridenour,
       11-Aug-2023.) $)
    grucollcld $p |- ( ph -> ( F Coll A ) e. G ) $=
      ( vx vy vz ccoll cv wbr cab cscott wcel wa c0 simpr ad2antrr ciun dfcoll2
      cgru wral wceq gru0eld eqeltrd wn wex neq0 cxp breq2 elscottab adantl wss
      wi ssbrd mpd brxp simprbi syl gruscottcld expcom exlimiv impcom pm2.61dan
      sylbi ralrimiva gruiun syl3anc eqeltrid ) ABCKHBHLZILZCMZINZOZUAZDHIBCUBA
      DUCPZBDPZVPDPZHBUDVQDPEGAVTHBAVLBPZQZVPRUEZVTWBWCQZVPRDWBWCSWDBDAVRWAWCET
      AVSWAWCGTUFUGWCUHZWBVTWEJLZVPPZJUIWBVTUPZJVPUJWGWHJWBWGVTWBWGQZVOWFDAVRWA
      WGETWIVLWFDDUKZMZWFDPZWIVLWFCMZWKWGWMWBVNWMIJVMWFVLCULUMUNWICWJVLWFACWJUO
      WAWGFTUQURWKVLDPWLVLWFDDUSUTVAWBWGSVBVCVDVGVEVFVHHBVPDVIVJVK $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Minimal universes
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d z w v U f i k m n q p l $.  $d z w u U f i k m n r p l $.
    ismnu.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    $( The hypothesis of this theorem defines a class M of sets that we
       temporarily call "minimal universes", and which will turn out in
       ~ grumnueq to be exactly Grothendicek universes.  Minimal universes are
       sets which satisfy the predicate on ` y ` in ~ rr-groth , except for the
       ` x e. y ` clause.

       A minimal universe is closed under subsets ( ~ mnussd ), powersets
       ( ~ mnupwd ), and an operation which is similar to a combination of
       collection and union ( ~ mnuop3d ), from which closure under pairing
       ( ~ mnuprd ), unions ( ~ mnuunid ), and function ranges ( ~ mnurnd ) can
       be deduced, from which equivalence with Grothendieck universes
       ( ~ grumnueq ) can be deduced.  (Contributed by Rohan Ridenour,
       13-Aug-2023.) $)
    ismnu $p
      |- ( U e. V -> ( U e. M <-> A. z e. U ( ~P z C_ U /\ A. f E. w e. U
        ( ~P z C_ w /\ A. i e. z ( E. v e. U ( i e. v /\ v e. f )
          -> E. u e. f ( i e. u /\ U. u C_ w ) ) ) ) ) ) $=
  ( cv wss wa cpw wel wrex cuni wral wal wceq weq simpr pweqd simpl sseq12d w3a
  wi wb 3adant3 adantr simpl3 eleq12d simpl13 anbi12d simpl11 cbvrexdva2 unieqd
  simpl2 imbi12d 3expa simpll2 cbvraldva2 simpl1 cbvaldvaw elab2g ) PRZUAZHRZSZ
  VNJRZSZONUBZNIUBZTZNVOUCZOMUBZMRZUDZVQSZTZMIRZUCZUNZOVMUEZTZJVOUCZIUFZTZPVOUE
  ARZUAZESZWQBRZSZGCUBZCFUBZTZCEUCZGDUBZDRZUDZWSSZTZDFRZUCZUNZGWPUEZTZBEUCZFUFZ
  TZAEUEHEKLVOEUGZWOXQPAVOEXRPAUHZTZVPWRWNXPXTVNWQVOEXTVMWPXRXSUIUJZXRXSUKZULXT
  WMXOIFXRXSIFUHZWMXOUOXRXSYCUMZWLXNJBVOEYDJBUHZTZVRWTWKXMYFVNWQVQWSYDVNWQUGZYE
  XRXSYGYCYAUPUQYDYEUIULYFWJXLOGVMWPYDYEOGUHZWJXLUOYDYEYHUMZWBXDWIXKYIWAXCNCVOE
  YINCUHZTZVSXAVTXBYKORZGRZNRZCRZYDYEYHYJURYIYJUIZUSYKYNYOWHXJYPXRXSYCYEYHYJUTU
  SVAXRXSYCYEYHYJVBVCYIWGXIMDWHXJYIMDUHZTZWCXEWFXHYRYLYMWDXFYDYEYHYQURYIYQUIZUS
  YRWEXGVQWSYRWDXFYSVDYDYEYHYQVEULVAXRXSYCYEYHYQUTVCVFVGXRXSYCYEYHVHVIVAXRXSYCY
  EVJVCVGVKVAYBVIQVL $.
  $}

  ${
    $d z w A f i $.  $d z w v U f i k m n q p l $.
    $d z w u U f i k m n r p l $.
    mnuop123d.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnuop123d.2 $e |- ( ph -> U e. M ) $.
    mnuop123d.3 $e |- ( ph -> A e. U ) $.
    $( Operations of a minimal universe.  (Contributed by Rohan Ridenour,
       13-Aug-2023.) $)
    mnuop123d $p
      |- ( ph -> ( ~P A C_ U /\ A. f E. w e. U
        ( ~P A C_ w /\ A. i e. A ( E. v e. U ( i e. v /\ v e. f )
          -> E. u e. f ( i e. u /\ U. u C_ w ) ) ) ) ) $=
  ( wa vz cv cpw wss wel wrex cuni wi wral wal wceq pweq sseq1d anbi12d rexbidv
  raleq albidv wcel ismnu ibi syl rspcdva ) AUAUBZUCZFUDZVDBUBZUDZHCUECGUETCFUF
  HDUEDUBUGVFUDTDGUBUFUHZHVCUIZTZBFUFZGUJZTZEUCZFUDZVNVFUDZVHHEUIZTZBFUFZGUJZTU
  AFEVCEUKZVEVOVLVTWAVDVNFVCEULZUMWAVKVSGWAVJVRBFWAVGVPVIVQWAVDVNVFWBUMVHHVCEUP
  UNUOUQUNAFLURZVMUAFUIZRWCWDUABCDFGHIJKLLMNOPQUSUTVASVB $.
  $}

  ${
    $d w A f i $.  $d w v U f i k m n q p l $.  $d w u U f i k m n r p l $.
    mnussd.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnussd.2 $e |- ( ph -> U e. M ) $.
    mnussd.3 $e |- ( ph -> A e. U ) $.
    mnussd.4 $e |- ( ph -> B C_ A ) $.
    $( Minimal universes are closed under subsets.  (Contributed by Rohan
       Ridenour, 13-Aug-2023.) $)
    mnussd $p |- ( ph -> B e. U ) $=
      ( vi vv vf vu vw cpw wss cv wel wa wrex cuni wi wral wal mnuop123d simpld
      sselpwd sseldd ) ABUBZDCAUPDUCUPUAUDZUCQRUERSUEUFRDUGQTUETUDUHUQUCUFTSUDU
      GUIQBUJUFUADUGSUKAUARTBDSQEFGHIJKLMNOULUMACBDOPUNUO $.
  $}

  ${
    $d ph x $.  $d x A $.  $d x U $.  $d U k m n r p l $.  $d U k m n q p l $.
    mnuss2d.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnuss2d.2 $e |- ( ph -> U e. M ) $.
    mnuss2d.3 $e |- ( ph -> E. x e. U A C_ x ) $.
    $( ~ mnussd with arguments provided with an existential quantifier.
       (Contributed by Rohan Ridenour, 13-Aug-2023.) $)
    mnuss2d $p |- ( ph -> A e. U ) $=
      ( cv wss wcel wa adantr simprl simprr mnussd rexlimddv ) ACBPZQZCDRBDOAUE
      DRZUFSZSUECDEFGHIJKLMADHRUHNTAUGUFUAAUGUFUBUCUD $.
  $}

  ${
    $d U k m n r p l $.  $d U k m n q p l $.
    mnu0eld.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnu0eld.2 $e |- ( ph -> U e. M ) $.
    mnu0eld.3 $e |- ( ph -> A e. U ) $.
    $( A nonempty minimal universe contains the empty set.  (Contributed by
       Rohan Ridenour, 13-Aug-2023.) $)
    mnu0eld $p |- ( ph -> (/) e. U ) $=
      ( c0 wss 0ss a1i mnussd ) ABOCDEFGHIJKLMNOBPABQRS $.
  $}

  ${
    $d ph f $.  $d v F $.  $d f V $.  $d w A f i $.  $d w u f i F $.
    $d w v U f i k m n q p l $.  $d w u U f i k m n r p l $.
    mnuop23d.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnuop23d.2 $e |- ( ph -> U e. M ) $.
    mnuop23d.3 $e |- ( ph -> A e. U ) $.
    mnuop23d.4 $e |- ( ph -> F e. V ) $.
    $( Second and third operations of a minimal universe.  (Contributed by
       Rohan Ridenour, 13-Aug-2023.) $)
    mnuop23d $p
      |- ( ph -> E. w e. U ( ~P A C_ w /\ A. i e. A
        ( E. v e. U ( i e. v /\ v e. F ) -> E. u e. F ( i e. u /\ U. u C_ w ) )
      ) ) $=
  ( vf wcel cpw cv wss wel wa wrex cuni wi wral wal mnuop123d simprd wceq eleq2
  anbi2d rexbidv rexeq imbi12d ralbidv spcgv sylc ) AKMUCEUDZBUEZUFZGCUGZCUBUGZ
  UHZCFUIZGDUGDUEUJVFUFUHZDUBUEZUIZUKZGEULZUHZBFUIZUBUMZVGVHCUEZKUCZUHZCFUIZVLD
  KUIZUKZGEULZUHZBFUIZUAAVEFUFVSABCDEFUBGHIJLNOPQRSTUNUOVRWHUBKMVMKUPZVQWGBFWIV
  PWFVGWIVOWEGEWIVKWCVNWDWIVJWBCFWIVIWAVHVMKVTUQURUSVLDVMKUTVAVBURUSVCVD $.
  $}

  ${
    $d ph w $.  $d w A i $.  $d w v U i k m n q p l $.
    $d w u U i k m n r p l $.
    mnupwd.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnupwd.2 $e |- ( ph -> U e. M ) $.
    mnupwd.3 $e |- ( ph -> A e. U ) $.
    $( Minimal universes are closed under powersets.  (Contributed by Rohan
       Ridenour, 13-Aug-2023.) $)
    mnupwd $p |- ( ph -> ~P A e. U ) $=
      ( vw vi vv vu c0 wrex cpw cv wss wel wcel wa cuni wi cvv 0ex a1i mnuop23d
      wral simpl reximi syl mnuss2d ) AOBUAZCDEFGHIJKLMAUROUBZUCZPQUDQUBSUEUFQC
      TPRUDRUBUGUSUCUFRSTUHPBUMZUFZOCTUTOCTAOQRBCPDEFSGUIHIJKLMNSUIUEAUJUKULVBU
      TOCUTVAUNUOUPUQ $.
  $}

  ${
    $d U k m n r p l $.  $d U k m n q p l $.
    mnusnd.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnusnd.2 $e |- ( ph -> U e. M ) $.
    mnusnd.3 $e |- ( ph -> A e. U ) $.
    $( Minimal universes are closed under singletons.  (Contributed by Rohan
       Ridenour, 13-Aug-2023.) $)
    mnusnd $p |- ( ph -> { A } e. U ) $=
      ( cpw csn mnupwd wss snsspw a1i mnussd ) ABOZBPZCDEFGHIJKLMABCDEFGHIJKLMN
      QUCUBRABSTUA $.
  $}

  ${
    $d U k m n r p l $.  $d U k m n q p l $.
    mnuprssd.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnuprssd.2 $e |- ( ph -> U e. M ) $.
    mnuprssd.3 $e |- ( ph -> C e. U ) $.
    mnuprssd.4 $e |- ( ph -> A C_ C ) $.
    mnuprssd.5 $e |- ( ph -> B C_ C ) $.
    $( A minimal universe contains pairs of subsets of an element of the
       universe.  (Contributed by Rohan Ridenour, 13-Aug-2023.) $)
    mnuprssd $p |- ( ph -> { A , B } e. U ) $=
      ( cpw sselpwd cpr mnupwd prssd mnussd ) ADSZBCUAEFGHIJKLMNOADEFGHIJKLMNOP
      UBABCUEABDEPQTACDEPRTUCUD $.
  $}

  ${
    $d U k m n r p l $.  $d U k m n q p l $.
    mnuprss2d.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnuprss2d.2 $e |- ( ph -> U e. M ) $.
    mnuprss2d.3 $e |- ( ph -> C e. U ) $.
    mnuprss2d.4 $e |- A C_ C $.
    mnuprss2d.5 $e |- B C_ C $.
    $( Special case of ~ mnuprssd .  (Contributed by Rohan Ridenour,
       13-Aug-2023.) $)
    mnuprss2d $p |- ( ph -> { A , B } e. U ) $=
      ( wss a1i mnuprssd ) ABCDEFGHIJKLMNOPBDSAQTCDSARTUA $.
  $}

  ${
    $d v F $.  $d w A i $.  $d ph w v i $.  $d w u i F $.
    $d w v U i k m n q p l $.  $d w u U i k m n r p l $.
    mnuop3d.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnuop3d.2 $e |- ( ph -> U e. M ) $.
    mnuop3d.3 $e |- ( ph -> A e. U ) $.
    mnuop3d.4 $e |- ( ph -> F C_ U ) $.
    $( Third operation of a minimal universe.  (Contributed by Rohan Ridenour,
       13-Aug-2023.) $)
    mnuop3d $p |- ( ph -> E. w e. U A. i e. A
      ( E. v e. F i e. v -> E. u e. F ( i e. u /\ U. u C_ w ) ) ) $=
      ( cpw cv wss wel wcel wa wrex cuni wi wral sselpwd mnuop23d sseld adantrd
      pm3.22 jca2 reximdv2 imim1d ralimdv adantld reximdv mpd ) AEUABUBZUCZGCUD
      ZCUBZKUEZUFZCFUGZGDUDDUBUHVCUCUFDKUGZUIZGEUJZUFZBFUGVECKUGZVJUIZGEUJZBFUG
      ABCDEFGHIJKLFUAMNOPQRSAKFLRTUKULAVMVPBFAVLVPVDAVKVOGEAVNVIVJAVEVHCKFAVGVE
      UFVFFUEZVHAVGVQVEAKFVFTUMUNVGVEUOUPUQURUSUTVAVB $.
  $}

  ${
    $d ph a $.  $d w i $.  $d A a $.  $d F a $.  $d w u a $.  $d u i F $.
    mnuprdlem1.1 $e |- F = { { (/) , { A } } , { { (/) } , { B } } } $.
    mnuprdlem1.3 $e |- ( ph -> A e. U ) $.
    mnuprdlem1.4 $e |- ( ph -> B e. U ) $.
    mnuprdlem1.8 $e
      |- ( ph -> A. i e. { (/) , { (/) } } E. u e. F ( i e. u /\ U. u C_ w ) )
    $.
    $( Lemma for ~ mnuprd .  (Contributed by Rohan Ridenour, 11-Aug-2023.) $)
    mnuprdlem1 $p |- ( ph -> A e. w ) $=
      ( va cv wcel c0 cuni wa cpr wceq wss wrex csn eleq1 rexbidv 0ex prid1 a1i
      anbi1d rspcdva adantr wn simprl simpr 0nep0 snn0d necomd nelprd elnelneqd
      wne adantrr adantrl wo elpri eleq2s orcomd ord sylc unieqd cun snex unipr
      uncom un0 3eqtri eqtrdi simprrr snssg biimprd eleq2w unieq sseq1d anbi12d
      eqsstrrd rexlimddvcbvw ) ADBNZOZPMNZOZWHQZWFUAZRZPCNZOZWMQZWFUAZRZCMHAGNZ
      WMOZWPRZCHUBWQCHUBGPPUCZSZPWRPTZWTWQCHXCWSWNWPWRPWMUDUIUELPXBOAPXAUFUGUHU
      JAWHHOZWLRZRZDFOZDUCZWFUAZWGAXGXEJUKXFXHWJWFXFWJPXHSZQZXHXFWHXJXFXDWHXAEU
      CZSZTZULZWHXJTZAXDWLUMAWLXOXDAWIXOWKAWIRWHXMPAWIUNAPXMOULWIAPXAXLPXAUTAUO
      UHAXLPAEFKUPUQURUKUSVAVBXDXNXPXDXPXNXPXNVCWHXJXMSHWHXJXMVDIVEVFVGVHVIXKPX
      HVJXHPVJXHPXHUFDVKVLPXHVMXHVNVOVPAXDWIWKVQWDXGWGXIDWFFVRVSVHWMWHTZWNWIWPW
      KCMPVTXQWOWJWFWMWHWAWBWCWE $.
  $}

  ${
    $d ph a $.  $d w i $.  $d B a $.  $d F a $.  $d w u a $.  $d u i F $.
    mnuprdlem2.1 $e |- F = { { (/) , { A } } , { { (/) } , { B } } } $.
    mnuprdlem2.4 $e |- ( ph -> B e. U ) $.
    mnuprdlem2.5 $e |- ( ph -> -. A = (/) ) $.
    mnuprdlem2.8 $e
      |- ( ph -> A. i e. { (/) , { (/) } } E. u e. F ( i e. u /\ U. u C_ w ) )
    $.
    $( Lemma for ~ mnuprd .  (Contributed by Rohan Ridenour, 11-Aug-2023.) $)
    mnuprdlem2 $p |- ( ph -> B e. w ) $=
      ( va cv wcel c0 csn wa cpr wceq cuni wrex eleq1 anbi1d rexbidv snex prid2
      wss a1i rspcdva simpl simprl simpr wne 0nep0 necomi 0ex sneqr eqcomd nsyl
      wn neqned nelprd adantr elnelneqd adantrr adantrl elpri eleq2s ord unieqd
      wo sylc cun unipr df-pr eqtr4i eqtrdi simprrr eqsstrrd wb sylancr biimprd
      cvv prssg simprd eleq2w unieq sseq1d anbi12d rexlimddvcbvw ) AEBNZOZPQZMN
      ZOZWOUAZWLUHZRZWNCNZOZWTUAZWLUHZRZCMHAGNZWTOZXCRZCHUBXDCHUBGPWNSZWNXEWNTZ
      XGXDCHXIXFXAXCXEWNWTUCUDUELWNXHOAPWNPUFZUGUIUJAWOHOZWSRZRZPWLOZWMXMAPESZW
      LUHZXNWMRZAXLUKXMXOWQWLXMWQWNEQZSZUAZXOXMWOXSXMXKWOPDQZSZTZVAZWOXSTZAXKWS
      ULAWSYDXKAWPYDWRAWPRWOYBWNAWPUMAWNYBOVAWPAWNPYAWNPUNAPWNUOUPUIAWNYAADPTWN
      YATZKYFPDPDUQURUSUTVBVCVDVEVFVGXKYCYEYCYEVLWOYBXSSHWOYBXSVHIVIVJVMVKXTWNX
      RVNXOWNXRXJEUFVOPEVPVQVRAXKWPWRVSVTAXQXPAPWDOEFOXQXPWAUQJPEWLWDFWEWBWCVMW
      FWTWOTZXAWPXCWRCMWNWGYGXBWQWLWTWOWHWIWJWK $.
    $( $j usage 'mnuprdlem2' avoids 'ax-pow'; $)
  $}

  ${
    $d ph a $.  $d A a $.  $d B a $.  $d v i a $.  $d v F a $.
    mnuprdlem3.1 $e |- F = { { (/) , { A } } , { { (/) } , { B } } } $.
    mnuprdlem3.9 $e |- F/ i ph $.
    $( Lemma for ~ mnuprd .  (Contributed by Rohan Ridenour, 11-Aug-2023.) $)
    mnuprdlem3 $p |- ( ph -> A. i e. { (/) , { (/) } } E. v e. F i e. v ) $=
      ( va cv wcel wrex c0 csn cpr wa wceq prid1 a1i simplr elpri simpr 3eltr4d
      wo 0ex prex eleqtrri rspcime prid2 jaodan sylan2 elequ2 cbvrexvw sylib ex
      snex ralrimi ) AEJZBJKZBFLZEMMNZOZHAURVBKZUTAVCPURIJZKZIFLZUTVCAURMQZURVA
      QZUDVFURMVAUAAVGVFVHAVGPZVEIMCNZOZFVIVDVKQZPZMVKURVDMVKKVMMVJUERSAVGVLTVI
      VLUBUCVKFKVIVKVKVADNZOZOZFVKVOMVJUFRGUGSUHAVHPZVEIVOFVQVDVOQZPZVAVOURVDVA
      VOKVSVAVNMUPRSAVHVRTVQVRUBUCVOFKVQVOVPFVKVOVAVNUFUIGUGSUHUJUKVEUSIBFIBEUL
      UMUNUOUQ $.
    $( $j usage 'mnuprdlem3' avoids 'ax-pow'; $)
  $}

  ${
    $d v F $.  $d w A a $.  $d w B a $.  $d v U a $.  $d ph w v i a $.
    $d w u i F a $.  $d w v U i k m n q p l $.  $d w u U i k m n r p l $.
    mnuprdlem4.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnuprdlem4.2 $e |- F = { { (/) , { A } } , { { (/) } , { B } } } $.
    mnuprdlem4.3 $e |- ( ph -> U e. M ) $.
    mnuprdlem4.4 $e |- ( ph -> A e. U ) $.
    mnuprdlem4.5 $e |- ( ph -> B e. U ) $.
    mnuprdlem4.6 $e |- ( ph -> -. A = (/) ) $.
    $( Lemma for ~ mnuprd .  General case.  (Contributed by Rohan Ridenour,
       13-Aug-2023.) $)
    mnuprdlem4 $p |- ( ph -> { A , B } e. U ) $=
      ( vi va vv vu vw cv wcel wa cpr wel wrex cuni wss csn wral mnu0eld mnusnd
      wi c0 0ss ssid mnuprss2d snsspr1 snsspr2 prssd eqsstrid mnuop3d simprl wb
      wceq eleq2w anbi12d adantl adantr nfv nfra1 mnuprdlem3 ralim ad2antll mpd
      nfan mnuprdlem1 mnuprdlem2 jca rspcedvd rexlimddv simprrl simprrr mnussd
      wn ) ABUAUEZUFZCWJUFZUGZBCUHZDUFUADATUBUIUBHUJZTUCUIUCUEUKUDUEZULUGUCHUJZ
      UQZTURURUMZUHZUNZWMUADUJUDDAUDUBUCWTDTEFGHIJKLMNPAURWSWSDEFGIJKLMNPAURDEF
      GIJKLMNPABDEFGIJKLMNPQUOUPWSUSWSUTVAAHURBUMZUHZWSCUMZUHZUHDOAXCXEDAURXBXB
      DEFGIJKLMNPABDEFGIJKLMNPQUPXBUSXBUTVAAWSXDURCUHDEFGIJKLMNPAURCCDEFGIJKLMN
      PRCUSCUTVAURCVBURCVCVAVDVEVFAWPDUFZXAUGZUGZWMBWPUFZCWPUFZUGZUAWPDAXFXAVGW
      JWPVIZWMXKVHXHXLWKXIWLXJUAUDBVJUAUDCVJVKVLXHXIXJXHUDUCBCDTHOABDUFXGQVMACD
      UFXGRVMZXHWOTWTUNZWQTWTUNZXHUBBCTHOAXGTATVNXFXATXFTVNWRTWTVOVTVTVPXAXNXOU
      QAXFWOWQTWTVQVRVSZWAXHUDUCBCDTHOXMABURVIWIXGSVMXPWBWCWDWEAWJDUFZWMUGZUGZW
      JWNDEFGIJKLMNADIUFXRPVMAXQWMVGXSBCWJAXQWKWLWFAXQWKWLWGVDWHWE $.
  $}

  ${
    $d U k m n r p l $.  $d U k m n q p l $.
    mnuprd.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnuprd.2 $e |- ( ph -> U e. M ) $.
    mnuprd.3 $e |- ( ph -> A e. U ) $.
    mnuprd.4 $e |- ( ph -> B e. U ) $.
    $( Minimal universes are closed under pairing.  (Contributed by Rohan
       Ridenour, 13-Aug-2023.) $)
    mnuprd $p |- ( ph -> { A , B } e. U ) $=
      ( c0 cpr wcel adantr wceq wa simpr 0ss eqsstrdi ssidd mnuprssd mnuprdlem4
      wn csn eqid pm2.61dan ) ABQUAZBCRDSAUMUBZBCCDEFGHIJKLMADHSZUMNTACDSZUMPTU
      NBQCAUMUCCUDUEUNCUFUGAUMUIZUBBCDEFGQBUJRQUJCUJRRZHIJKLMURUKAUOUQNTABDSUQO
      TAUPUQPTAUQUCUHUL $.
  $}

  ${
    $d v A $.  $d v U a $.  $d ph w v i a $.  $d w u A i a $.
    $d w v U i k m n q p l $.  $d w u U i k m n r p l $.
    mnuunid.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnuunid.2 $e |- ( ph -> U e. M ) $.
    mnuunid.3 $e |- ( ph -> A e. U ) $.
    $( Minimal universes are closed under union.  (Contributed by Rohan
       Ridenour, 13-Aug-2023.) $)
    mnuunid $p |- ( ph -> U. A e. U ) $=
      ( va vi cv wcel wss wi vv vu vw cuni csn wrex wa snssd mnuop3d simprl weq
      wral sseq2 adantl elssuni rgen simprr eleq2 rexsng syl wceq unieq anbi12d
      wb sseq1d imbi12d anclb bitr4di imbi2d pm5.4 bitrdi ralbidv2 adantr mpbid
      sstr2 ral2imi mpsyl unissb sylibr rspcedvd rexlimddv mnuss2d ) AOBUDZCDEF
      GHIJKLMAPQZUAQZRZUABUEZUFZWDUBQZRZWIUDZUCQZSZUGZUBWGUFZTZPBULZWCOQZSZOCUF
      UCCAUCUAUBBCPDEFWGGHIJKLMNABCNUHUIAWLCRZWQUGZUGZWSWCWLSZOWLCAWTWQUJOUCUKW
      SXCVDXBWRWLWCUMUNXBWDWLSZPBULZXCWDWCSZPBULXBXCPBULZXEXFPBWDBUOUPXBWQXGAWT
      WQUQAWQXGVDXAAWPXCPBBAWDBRZWPTXHXHXCTZTXIAWPXIXHAWPXHXHXCUGZTXIAWHXHWOXJA
      BCRZWHXHVDNWFXHUABCWEBWDURUSUTAXKWOXJVDNWNXJUBBCWIBVAZWJXHWMXCWIBWDURXLWK
      WCWLWIBVBVEVCUSUTVFXHXCVGVHVIXHXCVJVKVLVMVNXFXCXDPBWDWCWLVOVPVQPBWLVRVSVT
      WAWB $.
  $}

  ${
    $d U k m n r p l $.  $d U k m n q p l $.
    mnuund.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnuund.2 $e |- ( ph -> U e. M ) $.
    mnuund.3 $e |- ( ph -> A e. U ) $.
    mnuund.4 $e |- ( ph -> B e. U ) $.
    $( Minimal universes are closed under binary unions.  (Contributed by Rohan
       Ridenour, 13-Aug-2023.) $)
    mnuund $p |- ( ph -> ( A u. B ) e. U ) $=
      ( cpr cuni cun wcel wceq uniprg syl2anc mnuprd mnuunid eqeltrrd ) ABCQZRZ
      BCSZDABDTCDTUHUIUAOPBCDDUBUCAUGDEFGHIJKLMNABCDEFGHIJKLMNOPUDUEUF $.
  $}

  ${
    $d U k m n r p l $.  $d U k m n q p l $.
    mnutrcld.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnutrcld.2 $e |- ( ph -> U e. M ) $.
    mnutrcld.3 $e |- ( ph -> A e. U ) $.
    mnutrcld.4 $e |- ( ph -> B e. A ) $.
    $( Minimal universes contain the elements of their elements.  (Contributed
       by Rohan Ridenour, 13-Aug-2023.) $)
    mnutrcld $p |- ( ph -> B e. U ) $=
      ( cuni mnuunid wcel wss elssuni syl mnussd ) ABQZCDEFGHIJKLMNABDEFGHIJKLM
      NORACBSCUDTPCBUAUBUC $.
  $}

  ${
    $d ph x y $.  $d x y U $.  $d U k m n r p l $.  $d U k m n q p l $.
    mnutrd.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnutrd.2 $e |- ( ph -> U e. M ) $.
    $( Minimal universes are transitive.  (Contributed by Rohan Ridenour,
       13-Aug-2023.) $)
    mnutrd $p |- ( ph -> Tr U ) $=
      ( vx vy wel cv wcel wa wi wal wtr adantr simprr simprl mnutrcld ex sylibr
      alrimivv dftr2 ) AMNOZNPZBQZRZMPZBQZSZNTMTBUAAUPMNAUMUOAUMRUKUNBCDEFGHIJK
      ABFQUMLUBAUJULUCAUJULUDUEUFUHMNBUIUG $.
  $}

  ${
    $d v F $.  $d w u i a $.  $d v A i a $.  $d u A i a $.  $d u i F a $.
    mnurndlem1.3 $e |- ( ph -> F : A --> U ) $.
    mnurndlem1.4 $e |- A e. _V $.
    mnurndlem1.6 $e |- ( ph -> A. i e. A
      ( E. v e. ran ( a e. A |-> { a , { ( F ` a ) , A } } ) i e. v
        -> E. u e. ran ( a e. A |-> { a , { ( F ` a ) , A } } )
          ( i e. u /\ U. u C_ w ) ) ) $.
    $( Lemma for ~ mnurnd .  (Contributed by Rohan Ridenour, 12-Aug-2023.) $)
    mnurndlem1 $p |- ( ph -> ran F C_ w ) $=
      ( cv wcel wral wss wa cpr wceq cvv wfn cfv crn ffnd cuni cmpt wrex wi vex
      prid1 simpr eleqtrrid eqid id prex a1i preq1d preq12d adantl rr-elrnmpt3d
      fveq2 rspcime rgen ralim mpisyl wb rgenw eleq2 unieq sseq1d anbi12d ax-mp
      rexrnmptw wn simplrl prid2 elnotel elnelneq2d elpri orcomd fveq2d simplrr
      ord sylc unipr sseq1i unss bicomi simprbi sylbi fvex prss simplbi eqeltrd
      cun 3syl ex rexlimiva com12 ralimia syl fnfvrnss syl2anc ) AHEUAGMZHUBZBM
      ZNZGEOZHUCXFPAEFHJUDAXDDMZNZXIUEZXFPZQZDIEIMZXNHUBZERZRZUFZUCZUGZGEOZXHAX
      DCMZNZCXSUGZXTUHGEOYDGEOYALYDGEXDENZYCCXDXEERZRZXSYEYBYGSZQXDYGYBXDYFGUIU
      JYEYHUKULYEIEXQXDYGXRTXRUMZYEUNYGTNYEXDYFUOUPXNXDSZXQYGSYEYJXNXDXPYFYJUNY
      JXOXEEXNXDHVAUQURUSUTVBVCYDXTGEVDVEXTXGGEXTYEXGXTXDXQNZXQUEZXFPZQZIEUGZYE
      XGUHZXQTNZIEOXTYOVFYQIEXNXPUOVGXMYNIDEXQXRTYIXIXQSZXJYKXLYMXIXQXDVHYRXKYL
      XFXIXQVIVJVKVMVLYNYPIEXNENZYNQZYEXGYTYEQZXEXOXFUUAXDXNHUUAYKXDXPSZVNXDXNS
      ZYSYKYMYEVOUUAXDXPEYTYEUKXPENVNZUUAEXPNUUDXOEKVPEXPVQVLUPVRYKUUBUUCYKUUCU
      UBXDXNXPVSVTWCWDWAUUAYMXPXFPZXOXFNZYSYKYMYEWBYMXNXPWOZXFPZUUEYLUUGXFXNXPI
      UIXOEUOWEWFUUHXNXFPZUUEUUIUUEQUUHXNXPXFWGWHWIWJUUEUUFEXFNZUUFUUJQUUEXOEXF
      XNHWKKWLWHWMWPWNWQWRWJWSWTXAGEXFHXBXC $.
  $}

  ${
    $d v A $.  $d v F $.  $d v U a b $.  $d ph w v i a b $.  $d w u A i a b $.
    $d w u i F a b $.  $d w v U i k m n q p l $.  $d w u U i k m n r p l $.
    mnurndlem2.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnurndlem2.2 $e |- ( ph -> U e. M ) $.
    mnurndlem2.3 $e |- ( ph -> A e. U ) $.
    mnurndlem2.4 $e |- ( ph -> F : A --> U ) $.
    mnurndlem2.5 $e |- A e. _V $.
    $( Lemma for ~ mnurnd .  Deduction theorem input.  (Contributed by Rohan
       Ridenour, 13-Aug-2023.) $)
    mnurndlem2 $p |- ( ph -> ran F e. U ) $=
      ( va cv wcel vb vi vv vu vw crn cfv cpr cmpt wrex cuni wss wa wral adantr
      wi simpr mnutrcld ffvelcdmda mnuprd ralrimiva eqid rnmptss mnuop3d simprl
      syl weq wb sseq2 adantl wf simprr mnurndlem1 rspcedvd rexlimddv mnuss2d )
      AUAGUFZCDEFHIJKLMNAUBSZUCSTUCRBRSZVSGUGZBUHZUHZUIZUFZUJVRUDSZTWEUKUESZULU
      MUDWDUJUPUBBUNZVQUASZULZUACUJUECAUEUCUDBCUBDEFWDHIJKLMNOAWBCTZRBUNWDCULAW
      JRBAVSBTZUMZVSWACDEFHIJKLMACHTWKNUOZWLBVSCDEFHIJKLMWMABCTWKOUOZAWKUQURWLV
      TBCDEFHIJKLMWMABCVSGPUSWNUTUTVARBWBCWCWCVBVCVFVDAWFCTZWGUMZUMZWIVQWFULZUA
      WFCAWOWGVEUAUEVGWIWRVHWQWHWFVQVIVJWQUEUCUDBCUBGRABCGVKWPPUOQAWOWGVLVMVNVO
      VP $.
  $}

  ${
    $d U k m n r p l $.  $d U k m n q p l $.
    mnurnd.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnurnd.2 $e |- ( ph -> U e. M ) $.
    mnurnd.3 $e |- ( ph -> A e. U ) $.
    mnurnd.4 $e |- ( ph -> F : A --> U ) $.
    $( Minimal universes contain ranges of functions from an element of the
       universe to the universe.  (Contributed by Rohan Ridenour,
       13-Aug-2023.) $)
    mnurnd $p |- ( ph -> ran F e. U ) $=
      ( cvv wcel c0 wf cif elexd iftrued eqeltrd feq2d mpbird elimel mnurndlem2
      0ex ) ABQRZBSUAZCDEFGHIJKLMNAUKBCAUJBSABCOUBUCZOUDAUKCGTBCGTPAUKBCGULUEUF
      BSQUIUGUH $.
  $}

  ${
    $d ph x y $.  $d x y U $.  $d U k m n r p l $.  $d U k m n q p l $.
    mnugrud.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    mnugrud.2 $e |- ( ph -> U e. M ) $.
    $( Minimal universes are Grothendieck universes.  (Contributed by Rohan
       Ridenour, 13-Aug-2023.) $)
    mnugrud $p |- ( ph -> U e. Univ ) $=
      ( vx vy wcel cv wral wa adantr ralrimiva cgru wtr cpw cpr crn cuni co w3a
      cmap mnutrd simpr mnupwd ad2antrr mnuprd wf elmapi adantl mnuunid 3jca wb
      mnurnd elgrug syl mpbir2and ) ABUAOZBUBZMPZUCBOZVGNPZUDBOZNBQZVIUEZUFBOZN
      BVGUIUGZQZUHZMBQZABCDEFGHIJKLUJAVPMBAVGBOZRZVHVKVOVSVGBCDEFGHIJKABFOZVRLS
      AVRUKZULVSVJNBVSVIBOZRVGVIBCDEFGHIJKAVTVRWBLUMVSVRWBWASVSWBUKUNTVSVMNVNVS
      VIVNOZRZVLBCDEFGHIJKAVTVRWCLUMZWDVGBCDEVIFGHIJKWEVSVRWCWASWCVGBVIUOVSVIBV
      GUPUQVAURTUSTAVTVEVFVQRUTLMNBFVBVCVD $.
  $}

  ${
    $d G a $.  $d ph z a $.  $d z f h j G $.  $d ph w v f h i j $.
    $d w v u h i j F $.  $d z w v f i k m n G q p l $.
    $d z w u f i k m n G r p l $.
    grumnudlem.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    grumnudlem.2 $e |- ( ph -> G e. Univ ) $.
    grumnudlem.3 $e |- F = ( { <. b , c >. |
      E. d ( U. d = c /\ d e. f /\ b e. d ) } i^i ( G X. G ) ) $.
    grumnudlem.4 $e |- ( ( i e. G /\ h e. G )
      -> ( i F h <-> E. j ( U. j = h /\ j e. f /\ i e. j ) ) ) $.
    grumnudlem.5 $e
      |- ( ( h e. ( F Coll z ) /\ ( U. j = h /\ j e. f /\ i e. j ) )
        -> E. u e. f ( i e. u /\ U. u e. ( F Coll z ) ) ) $.
    $( Lemma for ~ grumnud .  (Contributed by Rohan Ridenour, 13-Aug-2023.) $)
    grumnudlem $p |- ( ph -> G e. M ) $=
      ( vw vv va wcel cv cpw wss wel wa wrex cuni wi wral wal cgru gruss 3expia
      syl3an1 alrimiv pwss ccoll cun wceq w3a ssun1 simp3 sseqtrrid simp1l3 wex
      sylibr wbr simp1r simpr unieqd simpl eqtr4d adantll simpll3 simprd simpld
      weq eqeltrd eleqtrrd 3jca simpl2 rr-spce simp1l1 syl simp2 gruuni syl2anc
      rspcime simpl1 gruel 3ad2ant1 sylan rexbidva mpbird rexex cpcoll2d adantr
      syl3anc cxp copab cin inss2 eqsstri a1i grucollcld syl2an2r mpbid rexcom4
      wb rexlimiva exlimiv sylbi elssuni ssun2 sstrdi adantl sseqtrrd ex anim2d
      reximdv sylc rexlimdv3a ralrimiva jca 3expa grupw gruun ismnu ) ALMUIZBUJ
      ZUKZLULZYTUFUJZULZFUJZUGUJZUIZUGDUMZUNZUGLUOUUDCUJZUIZUUIUPZUUBULZUNZCDUJ
      ZUOZUQZFYSURZUNZUFLUOZDUSZUNZBLURZAUVABLAYSLUIZUNZUUAUUTUVDUHUJZYSULZUVEL
      UIZUQZUHUSUUAUVDUVHUHAUVCUVFUVGALUTUIZUVCUVFUVGUBYSUVELVAVCVBVDUHYSLVEVOU
      VDUUSDUVDUURUFYTYSKVFZUPZVGZLAUVCUUBUVLVHZUURAUVCUVMVIZUUCUUQUVNUVLYTUUBY
      TUVKVJAUVCUVMVKVLUVNUUPFYSUVNFBUMZUNZUUHUUOUGLUVPUUELUIZUUHVIZUVMUUJUUKUV
      JUIZUNZCUUNUOZUUOAUVCUVMUVOUVQUUHVMUVRGUJZUPZEUJZVHZUWBUUNUIZUUDUWBUIZVIZ
      GVNZEUVJUOZUWAUVRUUDUWDKVPZEUVJUOUWJUVRFEYSKUVNUVOUVQUUHVQUVRUWKELUOZUWKE
      VNUVRUWLUWIELUOUVRUWIEUUEUPZLUVRUWDUWMVHZUNZUWHGUUELUWOGUGWFZUNZUWEUWFUWG
      UWNUWPUWEUVRUWNUWPUNZUWCUWMUWDUWRUWBUUEUWNUWPVRVSUWNUWPVTWAWBUWQUWBUUEUUN
      UWOUWPVRZUWQUUFUUGUVPUVQUUHUWNUWPWCZWDWGUWQUUDUUEUWBUWQUUFUUGUWTWEUWSWHWI
      UVPUVQUUHUWNWJWKUVRUVIUVQUWMLUIUVRAUVIAUVCUVMUVOUVQUUHWLZUBWMZUVPUVQUUHWN
      UUELWOWPWQUVRUWKUWIELUVRUUDLUIZUWDLUIZUWKUWIXRZUVPUVQUXCUUHUVPUVIUVCUVOUX
      CUVPAUVIAUVCUVMUVOWRUBWMAUVCUVMUVOWJZUVNUVOVRYSUUDLWSXGWTZUDXAXBXCUWKELXD
      WMXEUVRUWKUWIEUVJUVRUXCUWDUVJUIZUXDUXEUXGUVRUXHUNUVIUVJLUIZUXHUXDUVRUVIUX
      HUXBXFUVRAUXHUVCUXIUXAUVRUVCUXHUVPUVQUVCUUHUXFWTXFUVDYSKLAUVIUVCUBXFZKLLX
      HZULUVDKSUJZUPRUJVHUXLUUNUIQUJUXLUIVISVNQRXIZUXKXJUXKUCUXMUXKXKXLXMAUVCVR
      XNZXOUVRUXHVRUVJUWDLWSXGUDXOXBXPUWJUWHEUVJUOZGVNUWAUWHEGUVJXQUXOUWAGUWHUW
      AEUVJUEXSXTYAWMUVMUVTUUMCUUNUVMUVSUULUUJUVMUVSUULUVMUVSUNUUKUVLUUBUVSUUKU
      VLULUVMUVSUUKUVKUVLUUKUVJYBUVKYTYCYDYEUVMUVSVTYFYGYHYIYJYKYLYMYNUVDUVIYTL
      UIZUVKLUIZUVLLUIUXJAUVIUVCUXPUBYSLYOXAAUVIUVCUXIUXQUBUXNUVJLWOXOYTUVKLYPX
      GWQVDYMYLAUVIYRUVBXRUBBUFUGCLDFHIJMUTNOPTUAYQWMXC $.
  $}

  ${
    $d ph z f h i j $.  $d z u f h i j G $.  $d u f h i j b c d $.
    $d z f i k m n G q p l $.  $d z u f i k m n G r p l $.
    grumnud.1 $e |- M = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $.
    grumnud.2 $e |- ( ph -> G e. Univ ) $.
    $( Grothendieck universes are minimal universes.  (Contributed by Rohan
       Ridenour, 12-Aug-2023.) $)
    grumnud $p |- ( ph -> G e. M ) $=
      ( vu vj vd vc vb cv wcel wa vz vf vh cuni wceq w3a wex copab cxp cin eqid
      vi wbr brxp brin rbaib sylbir vex weq unieqd simplr eqeq12d elequ1 adantl
      wb simpr eleq12 adantlr 3anbi123d cbvexdvaw braba bitrdi simplr3 eleqtrrd
      ccoll simplr1 eqtrd simpll eqeltrd jca simpr2 rspcime grumnudlem ) AUAMUB
      UCULNBCDORZUDZPRZUEZWDUBRZSZQRZWDSZUFZOUGZQPUHZEEUIZUJZEFGHIQPOJKLWPUKULR
      ZESUCRZESTZWQWRWPUMZWQWRWNUMZNRZUDZWRUEZXBWHSZWQXBSZUFZNUGZWSWQWRWOUMZWTX
      AVEWQWREEUNWTXAXIWQWRWNWOUOUPUQWMXHQPWQWRWNULURUCURWJWQUEZWFWRUEZTZWLXGON
      XLONUSZTZWGXDWIXEWKXFXNWEXCWFWRXNWDXBXLXMVFUTXJXKXMVAVBXMWIXEVEXLONUBVCVD
      XJXMWKXFVEXKWJWQWDXBVGVHVIVJWNUKVKVLWRUARWPVOZSZXGTZWQMRZSZXRUDZXOSZTMXBW
      HXQMNUSZTZXSYAYCWQXBXRXDXEXFXPYBVMXQYBVFZVNYCXTWRXOYCXTXCWRYCXRXBYDUTXDXE
      XFXPYBVPVQXPXGYBVRVSVTXPXDXEXFWAWBWC $.
  $}

  ${
    $d x k m n r p l $.  $d x k m n q p l $.
    $( The class of Grothendieck universes is equal to the class of minimal
       universes.  (Contributed by Rohan Ridenour, 13-Aug-2023.) $)
    grumnueq $p |- Univ = { k | A. l e. k ( ~P l C_ k /\ A. m E. n e. k
      ( ~P l C_ n /\ A. p e. l ( E. q e. k ( p e. q /\ q e. m )
        -> E. r e. m ( p e. r /\ U. r C_ n ) ) ) ) } $=
      ( vx cgru cv cpw wss wcel wa wrex cuni wi wral wal id cab grumnud mnugrud
      eqid impbii eqriv ) HIGJZKZAJZLUHCJZLFJZEJZMULBJZMNEUIOUKDJZMUNPUJLNDUMOQ
      FUGRNCUIOBSNGUIRAUAZHJZIMZUPUOMZUQABCUPUODEFGUOUDZUQTUBURUPABCUODEFGUSURT
      UCUEUF $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Primitive equivalent of ax-groth
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    expandan.1 $e |- ( ph <-> ps ) $.
    expandan.2 $e |- ( ch <-> th ) $.
    $( Expand conjunction to primitives.  (Contributed by Rohan Ridenour,
       13-Aug-2023.) $)
    expandan $p |- ( ( ph /\ ch ) <-> -. ( ps -> -. th ) ) $=
      ( wa wn wi anbi12i df-an bitri ) ACGBDGBDHIHABCDEFJBDKL $.
  $}

  ${
    expandexn.1 $e |- ( ph <-> -. ps ) $.
    $( Expand an existential quantifier to primitives while contracting a
       double negation.  (Contributed by Rohan Ridenour, 13-Aug-2023.) $)
    expandexn $p |- ( E. x ph <-> -. A. x ps ) $=
      ( wex wn wal exbii exnal bitri ) ACEBFZCEBCGFAKCDHBCIJ $.
  $}

  ${
    expandral.1 $e |- ( ph <-> ps ) $.
    $( Expand a restricted universal quantifier to primitives.  (Contributed by
       Rohan Ridenour, 13-Aug-2023.) $)
    expandral $p |- ( A. x e. A ph <-> A. x ( x e. A -> ps ) ) $=
      ( wral cv wcel wi wal ralbii df-ral bitri ) ACDFBCDFCGDHBICJABCDEKBCDLM
      $.
  $}

  ${
    expandrexn.1 $e |- ( ph <-> -. ps ) $.
    $( Expand a restricted existential quantifier to primitives while
       contracting a double negation.  (Contributed by Rohan Ridenour,
       13-Aug-2023.) $)
    expandrexn $p |- ( E. x e. A ph <-> -. A. x ( x e. A -> ps ) ) $=
      ( wrex wn cv wcel wa wex wi wal rexbii df-rex exanali 3bitri ) ACDFBGZCDF
      CHDIZRJCKSBLCMGARCDENRCDOSBCPQ $.
  $}

  ${
    expandrex.1 $e |- ( ph <-> ps ) $.
    $( Expand a restricted existential quantifier to primitives.  (Contributed
       by Rohan Ridenour, 13-Aug-2023.) $)
    expandrex $p |- ( E. x e. A ph <-> -. A. x ( x e. A -> -. ps ) ) $=
      ( wn notnotb bitri expandrexn ) ABFZCDABJFEBGHI $.
  $}

  ${
    $d x A $.  $d x y B $.
    $( Expand ` U. A C_ B ` to primitives.  (Contributed by Rohan Ridenour,
       13-Aug-2023.) $)
    expanduniss $p
      |- ( U. A C_ B <-> A. x ( x e. A -> A. y ( y e. x -> y e. B ) ) ) $=
  ( cuni wss cv wral wcel wi wal unissb df-ss expandral bitri ) CEDFAGZDFZACHPC
  IBGZPIRDIJBKZJAKACDLQSACBPDMNO $.
  $}

  ${
    $d v u $.  $d v i $.  $d u o $.  $d U f $.  $d z w v $.  $d z v t $.
    $d z v f $.  $d w v U $.  $d w o s $.
    $( Express the predicate on ` U ` in ~ ismnu using only primitives.
       (Contributed by Rohan Ridenour, 13-Aug-2023.) $)
    ismnuprim $p
      |- ( A. z e. U ( ~P z C_ U /\ A. f E. w e. U
        ( ~P z C_ w /\ A. i e. z ( E. v e. U ( i e. v /\ v e. f )
          -> E. u e. f ( i e. u /\ U. u C_ w ) ) ) )
      <-> A. z ( z e. U -> A. f -. A. w ( w e. U -> -.
        A. v -. ( ( A. t ( t e. v -> t e. z ) -> -. ( v e. U -> -. v e. w ) )
          -> -. A. i ( i e. z -> ( v e. U -> ( i e. v -> ( v e. f ->
            -. A. u ( u e. f -> ( i e. u ->
              -. A. o ( o e. u -> A. s ( s e. o -> s e. w ) ) ) ) ) ) ) ) ) ) )
      ) $=
  ( cv wss wel wa wrex wi wal wn bitri bitr3i cpw cuni wral wcel 19.28v r19.42v
  w3a 19.26 jcab albii pwss anbi12i 3bitr4i ralcom4 19.23v 3anass df-rex bitr4i
  wex exbii imbi1i ralbii anass df-ss imbi12i 3impexp biid expanduniss expandan
  df-an expandrexn imbi2i expandral expandrex ) AKZUAZFLZVPBKZLZHCMZCGMZNZCFOZH
  DMZDKZUBVRLZNZDGKZOZPZHVOUCZNZBFOZGQNZVRFUDECMEAMPEQZCKZFUDZCBMZRPRZPZHAMWQVT
  WADGMWDIDMJIMJBMPJQPIQZRPZPDQRZPZPZPZPHQZRPRZCQZRPBQRZGQZAFWNVQWMNZGQXKVQWMGU
  EXLXJGXLVQWLNZBFOXJVQWLBFUFXMXIBFXMWPVOLZWQWRNZPZWQVTWAUGZWIPZHVOUCZNZCQZXIYA
  XPCQZXSCQZNZXMXPXSCUHYDVQVSNZWKNXMYBYEYCWKXNWQPZXNWRPZNZCQYFCQZYGCQZNYBYEYFYG
  CUHXPYHCXNWQWRUIUJVQYIVSYJCVOFUKCVOVRUKULUMYCXRCQZHVOUCWKXRHCVOUNYKWJHVOYKXQC
  USZWIPWJXQWICUOYLWCWIYLWQWBNZCUSWCXQYMCWQVTWAUPUTWBCFUQURVASVBTULVQVSWKVCSSXT
  XHCXPWTXSXGXNWOXOWSEWPVOVDWQWRVJVEXRXFHVOXRWQVTWAWIPZPZPXFWQVTWAWIVFYOXEWQYNX
  DVTWIXCWAWGXBDWHWDWDWFXAWDVGIJWEVRVHVIVKVLVLVLSVMVIUJTVNTUJTVM $.
  $}

  ${
    $d v u $.  $d u o $.  $d z v t $.  $d w o s $.
    $d y z w v f i k m n q p l $.  $d y z w u f i k m n r p l $.
    $( Express "every set is contained in a Grothendieck universe" using only
       primitives.  The right side (without the outermost universal quantifier)
       is proven as ~ rr-grothprim .  (Contributed by Rohan Ridenour,
       13-Aug-2023.) $)
    rr-grothprimbi $p |- ( A. x E. y e. Univ x e. y <->
      A. x -. A. y ( x e. y -> -. A. z ( z e. y
        -> A. f -. A. w ( w e. y -> -. A. v -.
          ( ( A. t ( t e. v -> t e. z ) -> -. ( v e. y -> -. v e. w ) )
            -> -. A. i ( i e. z -> ( v e. y -> ( i e. v -> ( v e. f ->
              -. A. u ( u e. f -> ( i e. u ->
                -. A. o ( o e. u -> A. s ( s e. o -> s e. w ) ) ) ) ) ) ) ) ) )
      ) ) ) $=
      ( cgru wrex cv wcel wi wal wn wa wss vk vm vn vr vq vp vl wel df-rex biid
      wex ancom cpw cuni wb cvv grumnueq ismnu elv ismnuprim expandan expandexn
      wral bitri albii ) ABUHZBLMZVFCNZBNZODNZVIOGNZENZOVKVHOPGQVLVIOZVLVJORPRP
      INZVHOVMVNVLOZVLHNZOZFNZVPOVNVROZJNZVROKNZVTOWAVJOPKQPJQRPPFQRPPPPIQRPREQ
      RPDQRHQPCQZRPZBQRZAVGVILOZVFSZBUKWDVFBLUIWFWCBWFVFWESWCRWEVFULVFVFWEWBVFU
      JWEVHUMZVITWGVJTVOVQSEVIMVSVRUNVJTSFVPMPIVHVCSDVIMHQSCVIVCZWBWEWHUOBCDEFV
      IHIUAUBUCLUPUDUEUFUGUAUBUCUDUEUFUGUQURUSCDEFGVIHIJKUTVDVAVDVBVDVE $.
  $}

  ${
    inagrud.1 $e |- ( ph -> I e. Inacc ) $.
    $( Inaccessible levels of the cumulative hierarchy are Grothendieck
       universes.  (Contributed by Rohan Ridenour, 13-Aug-2023.) $)
    inagrud $p |- ( ph -> ( R1 ` I ) e. Univ ) $=
      ( cr1 cfv ctsk wcel wtr cgru cina inatsk syl r1tr grutsk1 sylancl ) ABDEZ
      FGZPHPIGABJGQCBKLBMPNO $.
  $}

  ${
    $d x A $.
    $( Assuming the Tarski-Grothendieck axiom, every ordinal is contained in an
       inaccessible ordinal.  (Contributed by Rohan Ridenour, 13-Aug-2023.) $)
    inaex $p |- ( A e. On -> E. x e. Inacc A e. x ) $=
      ( con0 wcel cv cina csuc cdif cint wceq wa wss cwina inawina winaon ssriv
      syl onmindif c0 cvv mpan adantr simpr eleqtrrd difss sstri inaprc neli wi
      ssdif0 sucexg ssexg expcom biimtrrid neqned onint sylancr eldifad rspcime
      wne mtoi ) BCDZBAEZDAFBGZHZIZFVBVCVFJZKBVFVCVBBVFDZVGFCLVBVHAFCVCFDVCMDVC
      CDVCNVCOQPZFBRUAUBVBVGUCUDVBVFFVDVBVECLVESUTVFVEDVEFCFVDUEVIUFVBVESVBVESJ
      ZFTDZFTUGUHVJFVDLZVBVKFVDUJVBVDTDZVLVKUIBCUKVLVMVKFVDTULUMQUNVAUOVEUPUQUR
      US $.
  $}

  ${
    $d x y z $.
    $( Assuming the Tarski-Grothendieck axiom, every set is contained in a
       Grothendieck universe.  (Contributed by Rohan Ridenour, 13-Aug-2023.) $)
    gruex $p |- E. y e. Univ x e. y $=
      ( vz crnk cfv wcel cina wrex cgru con0 rankon inaex ax-mp cr1 wceq simplr
      cv wa wb syl cwina inawina winaon ad2antrr vex rankr1a mpbird simpr simpl
      eleqtrrd inagrud rspcime rexlimiva ) AQZDEZCQZFZCGHZUNBQZFZBIHZUOJFURUNKC
      UOLMUQVACGUPGFZUQRZUTBUPNEZIVCUSVDOZRZUNVDUSVFUNVDFZUQVBUQVEPVFUPJFZVGUQS
      VBVHUQVEVBUPUAFVHUPUBUPUCTUDUNUPAUEUFTUGVCVEUHUJVCUPVBUQUIUKULUMM $.
  $}

  ${
    $d x y $.  $d y z w v f i k m n q p l $.  $d y z w u f i k m n r p l $.
    $( An equivalent of ~ ax-groth using only simple defined symbols.
       (Contributed by Rohan Ridenour, 13-Aug-2023.) $)
    rr-groth $p |- E. y ( x e. y /\ A. z e. y ( ~P z C_ y /\ A. f E. w e. y
      ( ~P z C_ w /\ A. i e. z ( E. v e. y ( i e. v /\ v e. f )
        -> E. u e. f ( i e. u /\ U. u C_ w ) ) ) ) ) $=
      ( vk vm vn vr vq cv wcel cgru wrex wss wa wex vp vl cpw cuni wi wal gruex
      wral df-rex exancom wb cvv grumnueq ismnu elv anbi2i exbii 3bitri mpbi )
      ANBNZOZBPQZVACNZUCZUTRVDDNZRHNZENZOVGGNZOSEUTQVFFNZOVIUDVERSFVHQUEHVCUHSD
      UTQGUFSCUTUHZSZBTZABUGVBUTPOZVASBTVAVMSZBTVLVABPUIVMVABUJVNVKBVMVJVAVMVJU
      KBCDEFUTGHIJKPULLMUAUBIJKLMUAUBUMUNUOUPUQURUS $.
  $}

  ${
    $d x y $.  $d u o $.  $d z v t $.  $d w o s $.  $d y z w v u f i $.
    $( An equivalent of ~ ax-groth using only primitives.  This uses only 123
       symbols, which is significantly less than the previous record of 163
       established by ~ grothprim (which uses some defined symbols, and
       requires 229 symbols if expanded to primitives).  (Contributed by Rohan
       Ridenour, 13-Aug-2023.) $)
    rr-grothprim $p |- -. A. y ( x e. y -> -. A. z ( z e. y
      -> A. f -. A. w ( w e. y -> -. A. v
        -. ( ( A. t ( t e. v -> t e. z ) -> -. ( v e. y -> -. v e. w ) )
          -> -. A. i ( i e. z -> ( v e. y -> ( i e. v -> ( v e. f
            -> -. A. u ( u e. f -> ( i e. u ->
              -. A. o ( o e. u -> A. s ( s e. o -> s e. w ) ) ) ) ) ) ) ) ) ) )
      ) $=
      ( wel cv wcel wi wal wn cgru wrex gruex ax-gen rr-grothprimbi mpbi spi )
      ABLZCMZBMZNDMZUGNGMZEMZNUIUFNOGPUJUGNZUJUHNQOQOIMZUFNUKULUJNUJHMZNFMZUMNU
      LUNNJMZUNNKMZUONUPUHNOKPOJPQOOFPQOOOOIPQOQEPQODPQHPOCPQOBPQZAUEBRSZAPUQAP
      URAABTUAABCDEFGHIJKUBUCUD $.
  $}

  ${
    $d U v $.  $d f g i w z $.  $d f g i v z $.  $d U f g i u w $.
    $( Express the predicate on ` U ` and ` z ` in ~ ismnu in a shorter form
       while avoiding complicated definitions.  (Contributed by Rohan Ridenour,
       10-Oct-2024.) $)
    ismnushort $p |- ( A. f e. ~P U E. w e. U
        ( ~P z C_ ( U i^i w ) /\ ( z i^i U. f ) C_ U. ( f i^i ~P ~P w ) )
      <-> ( ~P z C_ U /\ A. f E. w e. U
        ( ~P z C_ w /\ A. i e. z ( E. v e. U ( i e. v /\ v e. f )
          -> E. u e. f ( i e. u /\ U. u C_ w ) ) ) ) ) $=
      ( vg cv cpw cin wss cuni wa wrex wral wcel wi wal wex simpl reximi ralimi
      wel wtru 0elpw a1i wceq biidd rspcdv mptru inss1 sstr2 mpi rexex ax5e syl
      c0 4syl inex2 elpw mpbir unieq ineq2d ineq1 unieqd sseq12d anbi2d rexbidv
      vex rspcv ax-mp alrimiv inss2 an12 bicomi anbi2i bitri exbii df-rex eluni
      3bitr4i w3a simp1 biimpri 3adant1 sseldd sylib elinel1 elin2d elinel2 cvv
      elin elpwpw simprbi anim2i eximi sylibr 3expia biimtrid ralrimiva anim12i
      jca sylg elequ2 rexeq imbi12d ralbidv cbvalvw nfv nfa1 nfan elpwi sp ssin
      biimpi ex adantr simp3 simpl2 simprr simprl 3jca eximdv mpd 3anass bitr4i
      mpbiran imim12d ralimdv imbi1i impexp albii df-ss df-ral imbitrrdi 3impia
      anim12d reximdv 3com23 syl3an2 3expa sylan2 ralrimia impbii ) AIZJZEBIZKZ
      LZUUFFIZMZKZUUKUUHJJZKZMZLZNZBEOZFEJZPZUUGELZUUGUUHLZGCUDZCIZUUKQZNZCEOZG
      DUDZDIZMUUHLZNZDUUKOZRZGUUFPZNZBEOZFSZNZUVAUVBUVRUVAUUJBEOZFUUTPZUVTUVBBE
      OZUVBUUSUVTFUUTUURUUJBEUUJUUQUAUBUCUWAUVTRUEUVTUVTFURUUTURUUTQUEEUFUGUEUU
      KURUHNUVTUIUJUKUUJUVBBEUUJUUIELUVBEUUHULUUGUUIEUMUNUBUWBUVBBTUVBUVBBEUOUV
      BBUPUQUSUVAUVCUVDUVEHIZQZNZCEOZUVLDUWCOZRZGUUFPZNZBEOZHSUVRUVAUUJUUFEUWCK
      ZMZKZUWLUUNKZMZLZNZBEOZUWKHUVAUWSHUWLUUTQZUVAUWSRUWTUWLELEUWCULUWLEUWCEHV
      JUTVAVBUUSUWSFUWLUUTUUKUWLUHZUURUWRBEUXAUUQUWQUUJUXAUUMUWNUUPUWPUXAUULUWM
      UUFUUKUWLVCVDUXAUUOUWOUUKUWLUUNVEVFVGVHVIVKVLVMUWRUWJBEUUJUVCUWQUWIUUJUUI
      UUHLUVCEUUHVNUUGUUIUUHUMUNUWQUWHGUUFUWFGIZUWMQZUWQUXBUUFQZNUWGUVEEQZUWENZ
      CTUVDUVEUWLQZNZCTUWFUXCUXFUXHCUXFUVDUXEUWDNZNUXHUXEUVDUWDVOUXIUXGUVDUXGUX
      IUVEEUWCWMVPVQVRVSUWECEVTCUXBUWLWAWBUWQUXDUXCUWGUWQUXDUXCWCZUVIUVJUWOQZNZ
      DTZUWGUXJUXBUWPQUXMUXJUWNUWPUXBUWQUXDUXCWDUXDUXCUXBUWNQZUWQUXNUXDUXCNUXBU
      UFUWMWMWEWFWGDUXBUWOWAWHUXMUVJUWCQZUVLNZDTUWGUXLUXPDUXLUVIUXOUVKNZNUXPUXK
      UXQUVIUXKUXOUVKUXKEUWCUVJUVJUWLUUNWIWJUXKUVJUUNQZUVKUVJUWLUUNWKUXRUVJWLQZ
      UVKUVJUUHWNZWOUQXCWPUVIUXOUVKVOWHWQUVLDUWCVTWRUQWSWTXAXBUBXDUVQUWKFHUUKUW
      CUHZUVPUWJBEUYAUVOUWIUVCUYAUVNUWHGUUFUYAUVHUWFUVMUWGUYAUVGUWECEUYAUVFUWDU
      VDFHCXEVHVIUVLDUUKUWCXFXGXHVHVIXIWRXCUVSUUSFUUTUVBUVRFUVBFXJUVQFXKXLUUKUU
      TQUVSUUKELZUUSUUKEXMUVBUVRUYBUUSUVRUVBUVQUYBUUSUVQFXNUVBUYBUVQUUSUVBUYBUV
      QUUSUVBUYBNZUVPUURBEUYCUVCUUJUVOUUQUVBUVCUUJRUYBUVBUVCUUJUVBUVCNUUJUUGEUU
      HXOXPXQXRUYCUVOUXBUULQZUXBUUPQZRZGUUFPZUUQUYCUVNUYFGUUFUYCUYDUVHUVMUYEUVB
      UYBUYDUVHUVBUYBUYDWCZUXEUVDUVFWCZCTZUVHUYHUVGCTZUYJUYHUYDUYKUVBUYBUYDXSCU
      XBUUKWAWHUYHUVGUYICUYHUVGUYIUYHUVGNZUXEUVDUVFUYLUUKEUVEUVBUYBUYDUVGXTUYHU
      VDUVFYAZWGUYHUVDUVFYBUYMYCXQYDYEUVHUXEUVGNZCTUYJUVGCEVTUYIUYNCUXEUVDUVFYF
      VSYGWRWSUVMUYERUYCUYEUVMUVIUVJUUOQZNZDTUVJUUKQZUVLNZDTUYEUVMUYPUYRDUYPUVI
      UYQUVKNZNUYRUYOUYSUVIUYOUYQUXRNUYSUVJUUKUUNWMUXRUVKUYQUXRUXSUVKDVJUXTYHVQ
      VRVQUYQUVIUVKVOYGVSDUXBUUOWAUVLDUUKVTWBWEUGYIYJUXBUUMQZUYERZGSUXDUYFRZGSU
      UQUYGVUAVUBGVUAUXDUYDNZUYERVUBUYTVUCUYEUXBUUFUULWMYKUXDUYDUYEYLVRYMGUUMUU
      PYNUYFGUUFYOWBYPYRYSYQYTUUAUUBUUCUUDUUE $.
  $}

  ${
    $d f i k l m n p r u w y z $.  $d f i k l m n p q v w y z $.
    $( Alternative definition of ` Univ ` using only simple defined symbols.
       (Contributed by Rohan Ridenour, 10-Oct-2024.) $)
    dfuniv2 $p |- Univ = { y | A. z e. y A. f e. ~P y E. w e. y
      ( ~P z C_ ( y i^i w ) /\ ( z i^i U. f ) C_ U. ( f i^i ~P ~P w ) ) } $=
      ( vi vv vu vk vm vn cv cpw cin wss cuni wa wrex wral cgru wel vr vq vp vl
      wcel wi wal wb cvv grumnueq ismnu elv ismnushort ralbii bitr4i eqabi ) BK
      ZLZAKZCKZMNUQDKZOMVAUTLLMONPCUSQDUSLRZBUSRZASUSSUEZURUSNURUTNEFTFDTPFUSQE
      GTGKOUTNPGVAQUFEUQRPCUSQDUGPZBUSRZVCVDVFUHABCFGUSDEHIJSUIUAUBUCUDHIJUAUBU
      CUDUJUKULVBVEBUSBCFGUSDEUMUNUOUP $.
  $}

  ${
    $d f w y z $.
    $( Express "every set is contained in a Grothendieck universe" in a short
       form while avoiding complicated definitions.  (Contributed by Rohan
       Ridenour, 8-Oct-2024.) $)
    rr-grothshortbi $p |- ( A. x E. y e. Univ x e. y <->
      A. x E. y ( x e. y /\ A. z e. y A. f e. ~P y E. w e. y
      ( ~P z C_ ( y i^i w ) /\ ( z i^i U. f ) C_ U. ( f i^i ~P ~P w ) ) ) ) $=
      ( wel cgru wrex cv cpw cin wss cuni wral wex wcel df-rex exancom dfuniv2
      wa eqabri anbi2i exbii 3bitri albii ) ABFZBGHZUFCIZJBIZDIZKLUHEIZMKUKUJJJ
      KMLTDUIHEUIJNCUINZTZBOZAUGUIGPZUFTBOUFUOTZBOUNUFBGQUOUFBRUPUMBUOULUFULBGB
      CDESUAUBUCUDUE $.
  $}

  ${
    $d x y $.  $d f w y z $.
    $( A shorter equivalent of ~ ax-groth than ~ rr-groth using a few more
       simple defined symbols.  (Contributed by Rohan Ridenour, 8-Oct-2024.) $)
    rr-grothshort $p |- E. y ( x e. y /\ A. z e. y A. f e. ~P y E. w e. y
      ( ~P z C_ ( y i^i w ) /\ ( z i^i U. f ) C_ U. ( f i^i ~P ~P w ) ) ) $=
      ( wel cv cpw cin wss cuni wa wrex wral wex cgru wal gruex rr-grothshortbi
      ax-gen mpbi spi ) ABFZCGZHBGZDGZIJUDEGZKIUGUFHHIKJLDUEMEUEHNCUENLBOZAUCBP
      MZAQUHAQUIAABRTABCDESUAUB $.
  $}

$( (End of Rohan Ridenour's mathbox.) $)
