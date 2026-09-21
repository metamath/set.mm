$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  General auxiliary theorems (2)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Logical conjunction - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Rearrangement of 4 conjuncts: second and forth positions interchanged.
     (Contributed by AV, 18-Feb-2022.) $)
  an4com24 $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) )
                   <-> ( ( ph /\ th ) /\ ( ch /\ ps ) ) ) $=
    ( wa an43 ancom anbi2i bitri ) ABECDEEADEZBCEZEJCBEZEABCDFKLJBCGHI $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Abbreviated conjunction and disjunction of three wff's - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Commutative law for a conjunction with a triple conjunction: second and
     forth positions interchanged.  (Contributed by AV, 18-Feb-2022.) $)
  3an4ancom24 $p |- ( ( ( ph /\ ps /\ ch ) /\ th )
                      <-> ( ( ph /\ th /\ ch ) /\ ps ) ) $=
    ( wa w3a an4com24 3an4anass 3bitr4i ) ABECDEEADECBEEABCFDEADCFBEABCDGABCDHA
    DCBHI $.

  $( Rearrangement of 4 conjuncts with a triple conjunction.  (Contributed by
     AV, 4-Mar-2022.) $)
  4an21 $p |- ( ( ( ph /\ ps ) /\ ch /\ th )
                <-> ( ps /\ ( ph /\ ch /\ th ) ) ) $=
    ( wa w3a 3anass ancom anbi1i anass bicomi anbi2i bitri ) ABEZCDFNCDEZEZBACD
    FZEZNCDGPBAEZOEZRNSOABHITBAOEZERBAOJUAQBQUAACDGKLMMM $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Negated membership (alternative)
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Declare new connectives. $)
  $c e// $. $( Not an element of (stylized epsilon with slash through it). $)

  $( Extend wff notation to include the 'not element of' relation. $)
  cnelbr $a class e// $.

  ${
    $d x y $.
    $( Define negated membership as binary relation.  Analogous to ~ df-eprel
       (the membership relation).  (Contributed by AV, 26-Dec-2021.) $)
    df-nelbr $a |- e// = { <. x , y >. | -. x e. y } $.

    $( Alternate definition of the negated membership as binary relation.
       (Proposed by BJ, 27-Dec-2021.)  (Contributed by AV, 27-Dec-2021.) $)
    dfnelbr2 $p |- e// = ( ( _V X. _V ) \ _E ) $=
      ( vx vy cv cvv wcel wa copab wel wn cxp cep cnelbr difopab df-xp df-eprel
      cdif difeq12i df-nelbr vex pm3.2i biantrur opabbii eqtri 3eqtr4ri ) ACDEZ
      BCDEZFZABGZABHZABGZPUGUIIZFZABGZDDJZKPLUGUIABMUNUHKUJABDDNABOQLUKABGUMABR
      UKULABUGUKUEUFASBSTUAUBUCUD $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( The binary relation of a set not being a member of another set.
       (Contributed by AV, 26-Dec-2021.) $)
    nelbr $p |- ( ( A e. V /\ B e. W ) -> ( A e// B <-> -. A e. B ) ) $=
      ( vx vy wel wn wcel cnelbr cv wceq wa eleq12 notbid df-nelbr brabga ) EFG
      ZHABIZHEFABJCDEKZALFKZBLMRSTAUABNOEFPQ $.
  $}

  ${
    $d x y $.
    $( If a set is related to another set by the negated membership relation,
       then it is not a member of the other set.  The other direction of the
       implication is not generally true, because if ` A ` is a proper class,
       then ` -. A e. B ` would be true, but not ` A e// B ` .  (Contributed by
       AV, 26-Dec-2021.) $)
    nelbrim $p |- ( A e// B -> -. A e. B ) $=
      ( vx vy cvv wcel wa cnelbr wbr wn wel df-nelbr relopabiv brrelex12i nelbr
      biimpd mpcom ) AEFBEFGZABHIZABFJZABHCDKJCDHCDLMNRSTABEEOPQ $.
  $}

  $( A set is related to another set by the negated membership relation iff it
     is not a member of the other set.  (Contributed by AV, 26-Dec-2021.) $)
  nelbrnel $p |- ( ( A e. V /\ B e. W ) -> ( A e// B <-> A e/ B ) ) $=
    ( wcel wa cnelbr wbr wn wnel nelbr df-nel bitr4di ) ACEBDEFABGHABEIABJABCDK
    ABLM $.

  $( If a set is related to another set by the negated membership relation,
     then it is not a member of the other set.  (Contributed by AV,
     26-Dec-2021.) $)
  nelbrnelim $p |- ( A e// B -> A e/ B ) $=
    ( cnelbr wbr wcel wn wnel nelbrim df-nel sylibr ) ABCDABEFABGABHABIJ $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The empty set - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A x $.  $d ph x $.  $d ta x $.
    $( Selecting one of two alternatives within a restricted generalization if
       one of the alternatives is false.  (Contributed by AV, 6-Sep-2018.)
       (Proof shortened by AV, 13-Oct-2018.) $)
    ralralimp $p |- ( ( ph /\ A =/= (/) )
                -> ( A. x e. A ( ( ph -> ( th \/ ta ) ) /\ -. th ) -> ta ) ) $=
      ( c0 wne wa wo wi wn wral ornld adantr ralimdv rspn0 adantl syld ) AEFGZH
      ZABCIJBKHZDELCDELZCTUACDEAUACJSABCMNOSUBCJACDEPQR $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Indexed union and intersection - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d B a c d e s $.  $d V a c d e s $.  $d W a c d e s $.  $d X a c d e s $.
    $( The union of singletons consisting of ordered triples which have
       distinct first and third components are disjunct.  (Contributed by
       Alexander van der Vekens, 10-Mar-2018.) $)
    otiunsndisjX $p |- ( B e. X
                      -> Disj_ a e. V U_ c e. W { <. a , B , c >. } ) $=
      ( vd vs ve wcel cv cotp csn ciun wceq wral wa wn adantr sylibr weq cin c0
      wo wdisj wi orc a1d wrex eliun wb simprl adantl simpl otthg syl3anc simp1
      w3a biimtrdi con3d ex com13 imp31 velsn eqeq1 notbid sylbi mpbird sylnibr
      nrexdv rexlimdva2 biimtrid ralrimiv oteq3 sneqd eleq2i notbii ralbii disj
      cbviunv olcd pm2.61i ralrimivva oteq1 iuneq2d disjor ) ADJZEGUAZFCEKZAFKZ
      LZMZNZFCGKZAWJLZMZNZUBUCOZUDZGBPEBPEBWMUEWGWSEGBBWHWGWIBJZWNBJZQZQZWSUFWH
      WSXCWHWRUGUHWHRZXCWSXDXCQZWRWHXEHKZWQJZRZHWMPZWRXEXFICWNAIKZLZMZNZJZRZHWM
      PXIXEXOHWMXFWMJXFWLJZFCUIXEXOFXFCWLUJXEXPXOFCXEWJCJZQZXPQZXFXLJZICUIXNXSX
      TICXSXJCJZQZXFXKOZXTYBYCRZWKXKOZRZXSYFYAXRYFXPXDXCXQYFXQXCXDYFXQXCXDYFUFX
      QXCQZYEWHYGYEWHAAOZFIUAZURZWHYGWTWGXQYEYJUKXCWTXQWGWTXAULUMXQWGXBULXQXCUN
      WIAWJWNBAXJDCUOUPWHYHYIUQUSUTVAVBVCSSXSYDYFUKZYAXPYKXRXPXFWKOZYKHWKVDYLYC
      YEXFWKXKVEVFVGUMSVHHXKVDVIVJIXFCXLUJVIVKVLVMXHXOHWMXGXNWQXMXFFICWPXLYIWOX
      KWJXJWNAVNVOVTVPVQVRTHWMWQVSTWAVAWBWCBWMWQEGWHFCWLWPWHWKWOWIWNAWJWDVOWEWF
      T $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Functions - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Equality of function values with conditional arguments, see also ~ fvif .
     (Contributed by Alexander van der Vekens, 21-May-2018.) $)
  fvifeq $p |- ( A = if ( ph , B , C )
                 -> ( F ` A ) = if ( ph , ( F ` B ) , ( F ` C ) ) ) $=
    ( cif wceq cfv fveq2 fvif eqtrdi ) BACDFZGBEHLEHACEHDEHFBLEIACDEJK $.

  ${
    $d i x X $.  $d i x Y $.  $d i x F $.
    $( The range of a one-to-one function ` F ` of an unordered pair into a set
       is the unordered pair of the function values.  (Contributed by Alexander
       van der Vekens, 2-Feb-2018.) $)
    rnfdmpr $p |- ( ( X e. V /\ Y e. W )
                -> ( F Fn { X , Y } -> ran F = { ( F ` X ) , ( F ` Y ) } ) ) $=
      ( vx vi wcel wa cpr cfv wceq cv cab cun fveq2 eqeq2d abbidv csn df-sn wfn
      wrex fnrnfv adantl ciun iunxprg adantr iunab eqcomi uneq12i df-pr 3eqtr3g
      crn eqtr4i eqtrd ex ) DBHECHIZADEJZUAZAUMZDAKZEAKZJZLUQUSIZUTFMZGMZAKZLZG
      URUBFNZVCUSUTVILUQGFURAUCUDVDGURVHFNZUEZVEVALZFNZVEVBLZFNZOZVIVCUQVKVPLUS
      GDEVJVMVOBCVFDLZVHVLFVQVGVAVEVFDAPQRVFELZVHVNFVRVGVBVEVFEAPQRUFUGVHGFURUH
      VPVASZVBSZOVCVMVSVOVTVSVMFVATUIVTVOFVBTUIUJVAVBUKUNULUOUP $.
  $}

  $( The image of the range of a function ` F ` under a function ` E ` if ` F `
     is a function from a pair into the domain of ` E ` .  (Contributed by
     Alexander van der Vekens, 2-Feb-2018.) $)
  imarnf1pr $p |- ( ( X e. V /\ Y e. W )
          -> ( ( ( F : { X , Y } --> dom E /\ E : dom E --> R )
                 /\ ( ( E ` ( F ` X ) ) = A /\ ( E ` ( F ` Y ) ) = B ) )
               -> ( E " ran F ) = { A , B } ) ) $=
    ( wcel wa cpr wf cfv wceq cima wi wfn ffn adantr cdm adantl simpll ad2antll
    crn prid1g ffvelcdmd prid2g fnimapr syl3anc ex impcom rnfdmpr eqcomd preq12
    syl5com imaeq2d 3eqtr3d ) HFJZIGJZKZHILZDUAZEMZVCCDMZKZHENZDNZAOIENZDNZBOKZ
    KZDEUEZPZABLZOVAVLKZDVGVILZPZVHVJLZVNVOVLVAVRVSOZVFVAVTQVKVFVAVTVFVAKZDVCRZ
    VGVCJVIVCJVTVFWBVAVEWBVDVCCDSUBTWAVBVCHEVDVEVAUCZVAHVBJZVFUSWDUTHIFUFTUBUGW
    AVBVCIEWCUTIVBJVFUSHIGUHUDUGVCVGVIDUIUJUKTULVPVQVMDVPVMVQVLVAVMVQOZVFVAWEQZ
    VKVDWFVEVDEVBRVAWEVBVCESEFGHIUMUPTTULUNUQVKVSVOOVAVFVHVJABUOUDURUK $.

  ${
    $d F a v w x y $.
    $( A function is an ordered pair iff it is a singleton of an ordered pair.
       (Contributed by AV, 20-Sep-2020.)  (Avoid depending on this detail.) $)
    funop1 $p |- ( E. x E. y F = <. x , y >.
                  -> ( Fun F <-> E. x E. y F = { <. x , y >. } ) ) $=
      ( vv vw va cv cop wceq wex wfun csn wb wa opeq12 eqeq2d cbvex2vw exlimivv
      weq vex funopsn sneqd spc2ev adantl exlimiv syl expcom funsn funeq mpbiri
      impbid1 sylbi ) CAGZBGZHZIZBJAJCDGZEGZHZIZEJDJCKZCUOLZIZBJAJZMZUPUTABDEAD
      SBESNUOUSCUMUNUQUROPQUTVEDEUTVAVDVAUTVDVAUTNUQFGZLIZCVFVFHZLZIZNZFJVDCUQU
      RFDTETUAVKVDFVJVDVGVCVJABVFVFFTZVLAFSBFSNZVBVICVMUOVHUMUNVFVFOUBPUCUDUEUF
      UGVCVAABVCVAVBKUMUNATBTUHCVBUIUJRUKRUL $.
  $}

  ${
    $d G a b $.
    $( A function with a domain containing (at least) two different elements is
       not an ordered pair.  (Contributed by AV, 21-Sep-2020.)  (Avoid
       depending on this detail.) $)
    fun2dmnopgexmpl $p |- ( G = { <. 0 , 1 >. , <. 1 , 1 >. }
                            -> -. G e. ( _V X. _V ) ) $=
      ( va vb cc0 c1 cop cpr wceq cv wex cvv cxp wcel wn wal csn wa intnanr 1ex
      vex wo 0ne1 neii gen2 eqeq1 propeqop bitrdi notbid 2albidv mpbiri 2nexaln
      c0ex sylibr elvv sylnibr ) ADEFEEFGZHZABIZCIZFZHZCJBJZAKKLMUQVANZCOBOZVBN
      UQVDDEHZURDPHZQZVEUSDEGHQZVHUAZQZNZCOBOVKBCVGVIVEVFDEUBUCRRUDUQVCVKBCUQVA
      VJUQVAUPUTHVJAUPUTUEDEEEURUSULSSSBTCTUFUGUHUIUJVABCUKUMBCAUNUO $.
  $}

  ${
    $d C x y $.  $d ph x y $.
    opabresex0d.x $e |- ( ( ph /\ x R y ) -> x e. C ) $.
    opabresex0d.t $e |- ( ( ph /\ x R y ) -> th ) $.
    opabresex0d.y $e |- ( ( ph /\ x e. C ) -> { y | th } e. V ) $.
    opabresex0d.c $e |- ( ph -> C e. W ) $.
    $( A collection of ordered pairs, the class of all possible second
       components being a set, with a restriction of a binary relation is a
       set.  (Contributed by Alexander van der Vekens, 1-Nov-2017.)  (Revised
       by AV, 1-Jan-2021.) $)
    opabresex0d $p |- ( ph -> { <. x , y >. | ( x R y /\ ps ) } e. _V ) $=
      ( cv wbr wcel wa wal copab cvv wi jca ex alrimivv elexd opabex3d opabbrex
      cab syl2anc ) ADNZENGOZUJFPZCQZUAZERDRUMDESTPUKBQDESTPAUNDEAUKUMAUKQULCJK
      UBUCUDACDEFIMAULQCEUHHLUEUFUMBDEGTUGUI $.

    $( A collection of ordered pairs, the class of all possible second
       components being a set, is a set.  (Contributed by AV, 15-Jan-2021.) $)
    opabbrfex0d $p |- ( ph -> { <. x , y >. | x R y } e. _V ) $=
      ( cv wbr copab wa cvv pm4.24 opabbii opabresex0d eqeltrid ) ACMDMFNZCDOUB
      UBPZCDOQUBUCCDUBRSAUBBCDEFGHIJKLTUA $.
  $}

  ${
    $d A y $.  $d B y $.  $d C x y $.  $d ph x y $.
    opabresexd.x $e |- ( ( ph /\ x R y ) -> x e. C ) $.
    opabresexd.y $e |- ( ( ph /\ x R y ) -> y : A --> B ) $.
    opabresexd.a $e |- ( ( ph /\ x e. C ) -> A e. U ) $.
    opabresexd.b $e |- ( ( ph /\ x e. C ) -> B e. V ) $.
    opabresexd.c $e |- ( ph -> C e. W ) $.
    $( A collection of ordered pairs, the second component being a function,
       with a restriction of a binary relation is a set.  (Contributed by
       Alexander van der Vekens, 1-Nov-2017.)  (Revised by AV, 15-Jan-2021.) $)
    opabresexd $p |- ( ph -> { <. x , y >. | ( x R y /\ ps ) } e. _V ) $=
      ( cv wf cvv wcel wa cab mapex syl2anc opabresex0d ) ABEFDQRZCDGHSKLMACQGT
      UAEITFJTUFDUBSTNOEFIJDUCUDPUE $.

    $( A collection of ordered pairs, the second component being a function, is
       a set.  (Contributed by AV, 15-Jan-2021.) $)
    opabbrfexd $p |- ( ph -> { <. x , y >. | x R y } e. _V ) $=
      ( cv wbr copab wa cvv pm4.24 opabbii opabresexd eqeltrid ) ABPCPGQZBCRUEU
      ESZBCRTUEUFBCUEUAUBAUEBCDEFGHIJKLMNOUCUD $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y C $.  $d x y D $.  $d x y ph $.  $d x ch $.
    f1oresf1orab.1 $e |- F = ( x e. A |-> C ) $.
    f1oresf1orab.2 $e |- ( ph -> F : A -1-1-onto-> B ) $.
    f1oresf1orab.3 $e |- ( ph -> D C_ A ) $.
    f1oresf1orab.4 $e |- ( ( ph /\ x e. A /\ y = C ) -> ( ch <-> x e. D ) ) $.
    $( Build a bijection by restricting the domain of a bijection.
       (Contributed by AV, 1-Aug-2022.) $)
    f1oresf1orab $p |- ( ph -> ( F |` D ) : D -1-1-onto-> { y e. B | ch } ) $=
      ( crab cres wf1o cv wcel f1oresrab wss wceq dfss7 sylib reseq2d f1oeq123d
      eqcomd eqidd mpbird ) AHBDFNZIHOZPCQHRZCENZUIIULOZPAUKBCDEFGIJKMSAHULUIUI
      UJUMAHULIAULHAHETULHUALCEHUBUCUFZUDUNAUIUGUEUH $.
  $}

  ${
    $d x A $.  $d x B $.  $d x y D $.  $d x y F $.  $d x y ph $.  $d x ch $.
    f1oresf1o.1 $e |- ( ph -> F : A -1-1-onto-> B ) $.
    f1oresf1o.2 $e |- ( ph -> D C_ A ) $.
    f1oresf1o.3 $e |- ( ph -> ( E. x e. D ( F ` x ) = y
                                <-> ( y e. B /\ ch ) ) ) $.
    $( Build a bijection by restricting the domain of a bijection.
       (Contributed by AV, 31-Jul-2022.) $)
    f1oresf1o $p |- ( ph -> ( F |` D ) : D -1-1-onto-> { y e. B | ch } ) $=
      ( crab cres wf1o wss syl syl2anc cv wceq cab cima wf1 f1of1 cfv wrex wfun
      f1ores f1ofun f1odm sseqtrrd dfimafn wcel wa abbidv df-rab eqtr4di eqtr2d
      cdm f1oeq3d mpbird ) AGBDFLZHGMZNGHGUAZVBNZAEFHUBZGEOVDAEFHNZVEIEFHUCPJEF
      GHUGQAVAVCGVBAVCCRHUDDRZSCGUEZDTZVAAHUFZGHURZOVCVISAVFVJIEFHUHPAGEVKJAVFV
      KESIEFHUIPUJCDGHUKQAVIVGFULBUMZDTVAAVHVLDKUNBDFUOUPUQUSUT $.
  $}

  ${
    $d x A $.  $d x B $.  $d x y D $.  $d x y F $.  $d x y ph $.  $d x ch $.
    f1oresf1o2.1 $e |- ( ph -> F : A -1-1-onto-> B ) $.
    f1oresf1o2.2 $e |- ( ph -> D C_ A ) $.
    f1oresf1o2.3 $e |- ( ( ph /\ y = ( F ` x ) ) -> ( x e. D <-> ch ) ) $.
    $( Build a bijection by restricting the domain of a bijection.
       (Contributed by AV, 31-Jul-2022.) $)
    f1oresf1o2 $p |- ( ph -> ( F |` D ) : D -1-1-onto-> { y e. B | ch } ) $=
      ( cv wceq wrex wcel wa syl adantr wi ex cfv w3a wf1o f1of sselda ffvelcdm
      wf 3adant3 wb eleq1 3ad2ant3 mpbid eqcom biimpd biimtrid com23 rexlimdv3a
      jca 3imp wfo f1ofo foelcdmi sylan nfre1 nfim expcom eqcoms adantl sylbird
      nfv rspe rexlimd syld impd impbid f1oresf1o ) ABCDEFGHIJACLZHUAZDLZMZCGNZ
      VSFOZBPZAVTWCCGAVQGOZVTUBZWBBWEVRFOZWBWEEFHUGZVQEOZPZWFAWDWIVTAWDPWGWHAWG
      WDAEFHUCZWGIEFHUDQRAGEVQJUEURUHEFVQHUFQVTAWFWBUIWDVRVSFUJUKULAWDVTBAVTWDB
      VTVSVRMZAWDBSZVRVSUMZAWKWLAWKPZWDBKUNTUOUPUSURUQAWBBWAAWBVTCENZBWASZAWBWO
      AEFHUTZWBWOAWJWQIEFHVAQCEFHVSVBVCTAVTWPCEACVJBWACBCVJVTCGVDVEAWHVTWPSVTWK
      AWHPWPWMAWKWPSWHAWKWPWNBWDWAKWKWDWASZAWRVRVSWDVTWAVTCGVKVFVGVHVITRUOTVLVM
      VNVOVP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Maps-to notation - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d M y $.  $d N x y $.  $d X x y $.  $d V x $.  $d ps x $.
    fvmptrab.f $e |- F = ( x e. V |-> { y e. M | ph } ) $.
    fvmptrab.r $e |- ( x = X -> ( ph <-> ps ) ) $.
    fvmptrab.s $e |- ( x = X -> M = N ) $.
    fvmptrab.v $e |- ( X e. V -> N e. _V ) $.
    fvmptrab.n $e |- ( X e/ V -> N = (/) ) $.
    $( Value of a function mapping a set to a class abstraction restricting a
       class depending on the argument of the function.  More general version
       of ~ fvmptrabfv , but relying on the fact that out-of-domain arguments
       evaluate to the empty set, which relies on set.mm's particular encoding.
       (Contributed by AV, 14-Feb-2022.) $)
    fvmptrab $p |- ( F ` X ) = { y e. N | ps } $=
      ( wcel cfv crab wceq cvv c0 cmpt a1i cv rabeqbidv adantl id rabexd fvmptd
      eqid wn fvmptndm wnel df-nel rabeq rab0 eqtr2di syl sylbir eqtrd pm2.61i
      ) IHOZIEPZBDGQZRVACIADFQZVCHESECHVDUARVAJUBCUCIRZVDVCRVAVEABDFGLKUDUEVAUF
      VABDGVCSVCUIMUGUHVAUJZVBTVCCHVDEIJUKVFIHULZTVCRZIHUMVGGTRZVHNVIVCBDTQTBDG
      TUNBDUOUPUQURUSUT $.
  $}

  ${
    $d F x $.  $d G x y $.  $d V x $.  $d X x y $.  $d Y x y $.  $d ps x $.
    fvmptrabdm.f $e |- F = ( x e. V |-> { y e. ( G ` Y ) | ph } ) $.
    fvmptrabdm.r $e |- ( x = X -> ( ph <-> ps ) ) $.
    fvmptrabdm.v $e |- ( Y e. dom G -> X e. dom F ) $.
    $( Value of a function mapping a set to a class abstraction restricting the
       value of another function.  See also ~ fvmptrabfv .  (Suggested by BJ,
       18-Feb-2022.)  (Contributed by AV, 18-Feb-2022.) $)
    fvmptrabdm $p |- ( F ` X ) = { y e. ( G ` Y ) | ps } $=
      ( cdm wcel wi wo crab wceq c0 cvv wn cfv pm2.1 imor wa ordir rabeqdv rab0
      ndmfv eqtr2di sylan9eq rabbidv dmmpt rabid2 fvex rabex a1i mprgbir eqtr4i
      cv eleq2i biimpi fvmptd3 jaoi sylbir expcom sylbi mp2 ) IFMNZHEMZNZOZVKUA
      ZVKPZHEUBZBDIFUBZQZRZLVKUCVLVIUAZVKPZVNVROVIVKUDVNVTVRVNVTUEVMVSUEZVKPVRV
      MVSVKUFWAVRVKVMVSVOSVQHEUIVSVQBDSQSVSBDVPSIFUIUGBDUHUJUKVKCHADVPQZVQGETJC
      UTZHRABDVPKULVKHGNVJGHVJWBTNZCGQZGCGWBEJUMGWERWDCGWDCGUNWDWCGNADVPIFUOZUP
      UQURUSVAVBVQTNVKBDVPWFUPUQVCVDVEVFVGVH $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Subtraction - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( ((a-b)+c)-a = c-a holds for complex numbers a,b,c.  (Contributed by
     Alexander van der Vekens, 23-Mar-2018.) $)
  cnambpcma $p |- ( ( A e. CC /\ B e. CC /\ C e. CC )
                    -> ( ( ( A - B ) + C ) - A ) = ( C - B ) ) $=
    ( cc wcel w3a cmin co caddc subcl 3adant3 simp3 simp1 addsubd wa oveq1d cc0
    wceq 3ad2ant1 3eqtrd simpl simpr sub32 anidms simp2 subadd23d subid addlidd
    3jca syl ancoms 3adant1 ) ADEZBDEZCDEZFZABGHZCIHAGHUQAGHZCIHAAGHZBGHZCIHZCB
    GHZUPUQCAUMUNUQDEUOABJKUMUNUOLZUMUNUOMNUPURUTCIUPUMUNUMFZURUTRUMUNVDUOUMUNO
    UMUNUMUMUNUAZUMUNUBVEUIKABAUCUJPUPVAUSVBIHZQVBIHZVBUPUSBCUMUNUSDEZUOUMVHAAJ
    UDSUMUNUOUEVCUFUMUNVFVGRUOUMUSQVBIAUGPSUNUOVGVBRUMUNUOOVBUOUNVBDECBJUKUHULT
    T $.

  $( ((a+b)-c)+d = ((a+d)+b)-c holds for complex numbers a,b,c,d.  (Contributed
     by Alexander van der Vekens, 23-Mar-2018.) $)
  cnapbmcpd $p |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) )
              -> ( ( ( A + B ) - C ) + D ) = ( ( ( A + D ) + B ) - C ) ) $=
    ( cc wcel wa caddc co addcl adantr simpr adantl simpl addsubd add32d oveq1d
    cmin eqtr3d ) AEFZBEFZGZCEFZDEFZGZGZABHIZDHIZCRIUGCRIDHIADHIBHIZCRIUFUGDCUB
    UGEFUEABJKUEUDUBUCUDLMZUEUCUBUCUDNMOUFUHUICRUFABDUBTUETUANKUBUAUETUALKUJPQS
    $.

  $( The sum of two complex numbers is equal to the difference of these two
     complex numbers iff the subtrahend is 0.  (Contributed by AV,
     8-May-2023.) $)
  addsubeq0 $p |- ( ( A e. CC /\ B e. CC )
                    -> ( ( A + B ) = ( A - B ) <-> B = 0 ) ) $=
    ( cc wcel wa caddc co cmin wceq cneg cc0 negsub eqcomd eqeq2d adantl addcan
    wb negcl mpd3an3 eqneg 3bitrd ) ACDZBCDZEZABFGZABHGZIUEABJZFGZIZBUGIZBKIZUD
    UFUHUEUDUHUFABLMNUBUCUGCDZUIUJQUCULUBBROABUGPSUCUJUKQUBBTOUA $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Ordering on reals (cont.) - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Addition and subtraction on one side of "less than or equal to".
     (Contributed by Alexander van der Vekens, 18-Mar-2018.) $)
  leaddsuble $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
                    ( B <_ C <-> ( ( A + B ) - C ) <_ A ) ) $=
    ( cr wcel w3a cle caddc co cmin wb leadd2 3comr readdcl 3adant3 simp3 simp1
    wbr lesubaddd bitr4d ) ADEZBDEZCDEZFZBCGRZABHIZACHIGRZUFCJIAGRUBUCUAUEUGKBC
    ALMUDUFCAUAUBUFDEUCABNOUAUBUCPUAUBUCQST $.

  $( If two real numbers are less than a third real number, the sum of the real
     numbers is less than twice the third real number.  (Contributed by
     Alexander van der Vekens, 21-May-2018.) $)
  2leaddle2 $p |- ( ( A e. RR /\ B e. RR /\ C e. RR )
                 -> ( ( A < C /\ B < C ) -> ( A + B ) < ( 2 x. C ) ) ) $=
    ( cr wcel w3a clt wbr wa caddc co c2 cle readdcl 3adant3 3ad2ant3 adantr id
    jca sylc cmul anidms 2re remulcl mpan 3jca simpr lt2add recn leidd eqbrtrrd
    2timesd ltletr ex ) ADEZBDEZCDEZFZACGHBCGHIZABJKZLCUAKZGHZURUSIZUTDEZCCJKZD
    EZVADEZFZUTVEGHZVEVAMHZIVBURVHUSURVDVFVGUOUPVDUQABNOUQUOVFUPUQVFCCNUBPUQUOV
    GUPLDEUQVGUCLCUDUEZPUFQVCVIVJVCUOUPIZUQUQIZIZUSVIURVNUSURVLVMUOUPVLUQVLROUQ
    UOVMUPUQUQUQUQRZVOSPSQURUSUGABCCUHTURVJUSUQUOVJUPUQVAVEVAMUQCCUIULUQVAVKUJU
    KPQSUTVEVAUMTUN $.

  $( Variant of trichotomy law for 'less than'.  (Contributed by Alexander van
     der Vekens, 8-Jun-2018.) $)
  ltnltne $p |- ( ( A e. RR /\ B e. RR ) ->
                ( A < B <-> ( -. B < A /\ -. B = A ) ) ) $=
    ( cr wcel wa clt wbr cle wn wceq wo ltnle wb leloe ancoms notbid a1i 3bitrd
    ioran ) ACDZBCDZEZABFGBAHGZIBAFGZBAJZKZIZUDIUEIEZABLUBUCUFUATUCUFMBANOPUGUH
    MUBUDUESQR $.

  $( A real number increasd by 1 is less than or equal to the number increased
     by 2.  (Contributed by Alexander van der Vekens, 17-Sep-2018.) $)
  p1lep2 $p |- ( N e. RR -> ( N + 1 ) <_ ( N + 2 ) ) $=
    ( cr wcel c1 c2 1red 2re a1i id cle wbr 1le2 leadd2dd ) ABCZDEANFEBCNGHNIDE
    JKNLHM $.

  $( If the result of subtracting two numbers is greater than a number, the
     result of adding one of these subtracted numbers to the number is less
     than the result of subtracting the other subtracted number only.
     (Contributed by Alexander van der Vekens, 9-Jun-2018.) $)
  ltsubsubaddltsub $p |- ( ( J e. RR /\ ( L e. RR /\ M e. RR /\ N e. RR ) )
                    -> ( J < ( ( L - M ) - N ) <-> ( J + M ) < ( L - N ) ) ) $=
    ( cr wcel w3a wa cmin clt wbr caddc simpl resubcl 3adant3 simp3 adantl recn
    co cc resubcld simpr2 ltadd1d wceq nnpcan syl3an breq2d bitrd ) AEFZBEFZCEF
    ZDEFZGZHZABCISZDISZJKACLSZUPCLSZJKUQBDISZJKUNAUPCUIUMMUMUPEFUIUMUODUJUKUOEF
    ULBCNOUJUKULPUAQUIUJUKULUBUCUNURUSUQJUMURUSUDZUIUJBTFUKCTFULDTFUTBRCRDRBCDU
    EUFQUGUH $.

  $( An integer minus 1 is positive under certain circumstances.  (Contributed
     by Alexander van der Vekens, 9-Jun-2018.) $)
  zm1nn $p |- ( ( N e. NN0 /\ L e. ZZ )
                 -> ( ( J e. RR /\ 0 <_ J /\ J < ( ( L - N ) - 1 ) )
                      -> ( L - 1 ) e. NN ) ) $=
    ( cr wcel cc0 cle wbr cmin co c1 clt cz wa wi 0red zre adantl 1red adantr
    w3a cn0 cn simpl nn0re resubcl syl2anr peano2rem syl lelttr syl3anc posdifd
    caddc ltaddsubd elnn0z leadd2d readdcli readdcld peano2zm ltaddsub2d biimpd
    1re 0re a1i elnnz sylanbrc ex syld expd sylbid impancom sylbi sylbird com23
    imp 3impib com12 ) ADEZFAGHZABCIJZKIJZLHZUACUBEZBMEZNZBKIJZUCEZVRVSWBWEWGOV
    RWEVSWBNZWGVRWEWHWGOVRWENZWHFWALHZWGWIFDEVRWADEZWHWJOWIPVRWEUDWIVTDEZWKWEWL
    VRWDBDEZCDEZWLWCBQZCUEZBCUFUGZRVTUHUIFAWAUJUKWEWJWGOVRWEWJKVTLHZWGWEKVTWESZ
    WQULWEWRKCUMJZBLHZWGWEKCBWSWCWNWDWPTWDWMWCWORUNWCWDXAWGOZWCCMEZFCGHZNWDXBOC
    UOXCWDXDXBXCWDNZXDKFUMJZWTGHZXBXEFCKXEPXCWNWDCQZTXESUPXEXGXAWGXEXGXANZXFBLH
    ZWGXEXFDEZWTDEZWMXIXJOXKXEKFVBVCUQVDXCXLWDXCKCXCSXHURTWDWMXCWORXFWTBUJUKXEX
    JWGXEXJNWFMEZFWFLHZWGXEXMXJWDXMXCBUSRTXEXJXNWDXJXNOXCWDXJXNWDKFBWDSWDPWOUTV
    ARVOWFVEVFVGVHVIVJVKVLVOVMVMRVHVGVNVPVQ $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Imaginary and complex number properties - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    recnaddnred.a $e |- ( ph -> A e. RR ) $.
    recnaddnred.b $e |- ( ph -> B e. ( CC \ RR ) ) $.
    $( The sum of a real number and an imaginary number is not a real number.
       (Contributed by AV, 23-Jan-2023.) $)
    readdcnnred $p |- ( ph -> ( A + B ) e/ RR ) $=
      ( caddc co cr wcel wn cc cim cfv cc0 wceq wb recnd reim0b syl eqeq1d wnel
      eldifbd df-nel eldifad addcld reim0d oveq1d addlidd imaddd 3bitr4d notbid
      imcld eqtrd bitrd bitrid mpbird ) ABCFGZHUAZCHIZJZACKHEUBURUQHIZJAUTUQHUC
      AVAUSAVAUQLMZNOZUSAUQKIVAVCPABCABDQZACKHEUDZUEUQRSABLMZCLMZFGZNOVGNOZVCUS
      AVHVGNAVHNVGFGVGAVFNVGFABDUFUGAVGAVGACVEULQUHUMTAVBVHNABCVDVEUITACKIUSVIP
      VECRSUJUNUKUOUP $.

    $( The difference of a real number and an imaginary number is not a real
       number.  (Contributed by AV, 23-Jan-2023.) $)
    resubcnnred $p |- ( ph -> ( A - B ) e/ RR ) $=
      ( cmin co cr wcel wn cc cim cfv cc0 wceq wb recnd reim0b syl eqeq1d imcld
      eldifbd df-nel eldifad subcld reim0d oveq1d df-neg eqtr4di imsubd negeq0d
      wnel cneg bitrd 3bitr4d notbid bitrid mpbird ) ABCFGZHULZCHIZJZACKHEUBUTU
      SHIZJAVBUSHUCAVCVAAVCUSLMZNOZVAAUSKIVCVEPABCABDQZACKHEUDZUEUSRSABLMZCLMZF
      GZNOVIUMZNOZVEVAAVJVKNAVJNVIFGVKAVHNVIFABDUFUGVIUHUITAVDVJNABCVFVGUJTAVAV
      INOZVLACKIVAVMPVGCRSAVIAVIACVGUAQUKUNUOUNUPUQUR $.

    cndivrenred.n $e |- ( ph -> A =/= 0 ) $.
    $( The product of a real number and an imaginary number is not a real
       number.  (Contributed by AV, 23-Jan-2023.) $)
    recnmulnred $p |- ( ph -> ( A x. B ) e/ RR ) $=
      ( cmul co cr wnel wcel wn cc eldifbd df-nel cc0 wne wb eldifad mulre
      syl3anc bicomd notbid bitrid mpbird ) ABCGHZIJZCIKZLZACMIENUGUFIKZLAUIUFI
      OAUJUHAUHUJACMKBIKBPQUHUJRACMIESDFCBTUAUBUCUDUE $.

    $( The quotient of an imaginary number and a real number is not a real
       number.  (Contributed by AV, 23-Jan-2023.) $)
    cndivrenred $p |- ( ph -> ( B / A ) e/ RR ) $=
      ( cdiv co cr wcel wn cc cim cfv cc0 wceq wb recnd reim0b syl wnel eldifbd
      df-nel eldifad divcld diveq0ad imdivd eqeq1d 3bitr4d notbid bitrid mpbird
      imcld bitrd ) ACBGHZIUAZCIJZKZACLIEUBUPUOIJZKAURUOIUCAUSUQAUSUOMNZOPZUQAU
      OLJUSVAQACBACLIEUDZABDRZFUEUOSTACMNZBGHZOPVDOPZVAUQAVDBAVDACVBUMRVCFUFAUT
      VEOABCDVBFUGUHACLJUQVFQVBCSTUIUNUJUKUL $.
  $}

  $( The square root of a negative number is not a real number.  (Contributed
     by AV, 28-Feb-2023.) $)
  sqrtnegnre $p |- ( ( X e. RR /\ X < 0 ) -> ( sqrt ` X ) e/ RR ) $=
    ( cr wcel cc0 clt wbr wa csqrt cfv wn wnel ci cneg cmul wceq adantr imp a1i
    co cc recn negnegd eqcomd fveq2d simpl renegcld cle wi 0re mpan2 wb le0neg1
    ltle mpbid sqrtnegd eqtrd ax-icn negcld sqrtcld mulcomd resqrtcld inelr wne
    eldifd lt0neg1 ltne sylan 3imtr3d sqrt00 syl2anc bicomd necon3bid ex sylbid
    recnmulnred df-nel sylib eqneltrd sylibr ) ABCZADEFZGZAHIZBCJWCBKWBWCLAMZHI
    ZNSZBWBWCWDMZHIWFWBAWGHWBWGAVTWGAOWAVTAAUAZUBPUCUDWBWDWBAVTWAUEUFZWBADUGFZD
    WDUGFZVTWAWJVTDBCZWAWJUHUIADUMUJZQVTWJWKUKWAAULZPUNZUOUPWBWFWELNSZBWBLWELTC
    WBUQRZWBWDWBAVTATCWAWHPURUSUTWBWPBKWPBCJWBWELWBWDWIWOVAWBLTBWQLBCJWBVBRVDVT
    WAWEDVCZVTWADWDEFZWRAVEZVTWSWRVTWSGZWDDVCZWRVTWLWSXBWLVTUIRDWDVFVGXAWDDWEDX
    AWEDOZWDDOZXAWDBCWKXCXDUKXAAVTWSUEUFVTWSWKVTWAWJWSWKWMWTWNVHQWDVIVJVKVLUNVM
    VNQVOWPBVPVQVRVRWCBVPVS $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Nonnegative integers (as a subset of complex numbers) - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Closure law for subtraction of reals, restricted to nonnegative integers.
     (Contributed by Alexander van der Vekens, 6-Apr-2018.) $)
  nn0resubcl $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A - B ) e. RR ) $=
    ( cn0 wcel cr cmin co nn0re resubcl syl2an ) ACDAEDBEDABFGEDBCDAHBHABIJ $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Integers (as a subset of complex numbers) - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( If an integer is between another integer and its successor, the integer is
     equal to the other integer.  (Contributed by AV, 30-May-2020.) $)
  zgeltp1eq $p |- ( ( I e. ZZ /\ A e. ZZ )
                      -> ( ( A <_ I /\ I < ( A + 1 ) ) -> I = A ) ) $=
    ( cz wcel wa cle wbr c1 caddc co clt simprr wb zleltp1 adantr mpbird simprl
    wceq cr zre letri3 syl2an mpbir2and ex ) BCDZACDZEZABFGZBAHIJKGZEZBARZUGUJE
    ZUKBAFGZUHULUMUIUGUHUILUGUMUIMUJBANOPUGUHUIQUGUKUMUHEMZUJUEBSDASDUNUFBTATBA
    UAUBOUCUD $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Decimal arithmetic  - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( 11 is 1 times 10 to the power of 1, plus 1.  (Contributed by AV,
     4-Aug-2020.)  (Revised by AV, 9-Sep-2021.) $)
  1t10e1p1e11 $p |- ; 1 1 = ( ( 1 x. ( ; 1 0 ^ 1 ) ) + 1 ) $=
    ( c1 cdc cc0 cmul co caddc cexp dfdec10 ax-1cn 10nn nncni cc wcel wceq exp1
    ax-mp eqcomi oveq2i mulcomli oveq1i eqtri ) AABACBZADEZAFEAUBAGEZDEZAFEAAHU
    CUEAFAUBUEIUBJKZUBUDADUDUBUBLMUDUBNUFUBOPQRSTUA $.

  $( Add 1 to a 2 digit number with carry.  This is a special case of
     ~ decsucc , but in closed form.  As observed by ML, this theorem allows
     for carrying the 1 down multiple decimal constructors, so we can carry the
     1 multiple times down a multi-digit number, e.g., by applying this theorem
     three times we get ` ( ; ; 9 9 9 + 1 ) = ; ; ; 1 0 0 0 ` .  (Contributed
     by AV, 4-Aug-2020.)  (Revised by ML, 8-Aug-2020.)  (Proof shortened by AV,
     10-Sep-2021.) $)
  deccarry $p |- ( A e. NN -> ( ; A 9 + 1 ) = ; ( A + 1 ) 0 ) $=
    ( cn wcel c1 caddc co cc0 cdc c9 cmul df-dec 9nn peano2nn nnmulcld nncnd cc
    a1i nncni eqtr2id eqtrd ax-mp addridd nncn adddid mulridd oveq2d id addassd
    1cnd oveq1i ) ABCZADEFZGHIDEFZULJFZGEFZAIHZDEFZULGKUKUOUNUQUKUNUKUNUKUMULUM
    BCZUKIBCURLIMUAZQZAMNOUBUKUNUMAJFZUMDJFZEFZUQUKUMADUMPCUKUMUSRQZAUCUKUIZUDU
    KVCVAUMEFZUQUKVBUMVAEUKUMVDUEUFUKUQVAIEFZDEFVFUPVGDEAIKUJUKVAIDUKVAUKUMAUTU
    KUGNOIPCUKILRQVEUHSTTTS $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Upper sets of integers - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( If an integer is greater than or equal to a nonnegative integer, then it
     is a nonnegative integer.  (Contributed by Alexander van der Vekens,
     27-Aug-2018.) $)
  eluzge0nn0 $p |- ( N e. ( ZZ>= ` M ) -> ( 0 <_ M -> N e. NN0 ) ) $=
    ( cuz cfv wcel cz cle wbr w3a cc0 cn0 wi eluz2 wa simpl2 cr zre 0red simpl
    ex simpr 3jca syl2an letr syl expcomd 3imp1 elnn0z sylanbrc sylbi ) BACDEAF
    EZBFEZABGHZIZJAGHZBKEZLABMUNUOUPUNUONULJBGHZUPUKULUMUOOUKULUMUOUQUKULUMUOUQ
    LLUKULNZUOUMUQURJPEZAPEZBPEZIZUOUMNUQLUKUTVAVBULAQBQUTVANZUSUTVAVCRUTVASUTV
    AUAUBUCJABUDUEUFTUGBUHUITUJ $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Infinity and the extended real number system (cont.) - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Negated extended trichotomy law for 'less than' and 'less than or equal
     to'.  (Contributed by AV, 18-Jul-2020.) $)
  nltle2tri $p |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* )
                    -> -. ( A < B /\ B <_ C /\ C <_ A ) ) $=
    ( cxr wcel w3a clt wbr wa wi wn xrltletr wo id impcom wb xrltnle 3adant2 ex
    cle biimpd imp olcd expcom syl com23 impd pm2.61i df-3an notbii ianor bitri
    orcd a1d sylibr mpd ) ADEZBDEZCDEZFZABGHZBCTHZIZACGHZJZVAVBCATHZFZKZABCLUTV
    EVHUTVEIZVCKZVFKZMZVHVCVIVLJVCUTVEVLVCVEUTVLVCVEUTVLJZVCVEIVDVMVEVCVDVENOUT
    VDVLUTVDIVKVJUTVDVKUTVDVKUQUSVDVKPURACQRUAUBUCUDUESUFUGVJVLVIVJVJVKVJNUMUNU
    HVHVCVFIZKVLVGVNVAVBVFUIUJVCVFUKULUOSUP $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Finite intervals of integers - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Subset relationship for finite sets of sequential integers.  (Contributed
     by Alexander van der Vekens, 16-Mar-2018.) $)
  ssfz12 $p |- ( ( K e. ZZ /\ L e. ZZ /\ K <_ L )
                 -> ( ( K ... L ) C_ ( M ... N ) -> ( M <_ K /\ L <_ N ) ) ) $=
    ( cz wcel cle wbr w3a cfz co wa wi cuz cfv syl ssel2 eluz2 3ad2ant3 sylbi
    wss eluz biimp3ar eluzfz1 eluzfz2 elfzuz3 pm3.21 com13 elfzuz syl11 3syl ex
    a1i com4t com24 pm2.43i com14 mpcom mpd ) AEFZBEFZABGHZIZAABJKZFZVDCDJKZUAZ
    CAGHZBDGHZLZMZVCBANOFZVEUTVAVLVBABUBUCZABUDPBVDFZVCVEVKMVCVLVNVMABUEPVGVCVE
    VNVJVGVCVEVNVJMZMMVGVEVCVGVOVGVEVCVGVOMMZVGVELAVFFZVPVDVFAQVGVNVQVCVJVGVNVQ
    VCVJMZMZVGVNLBVFFDBNOFZVSVDVFBQBCDUFACNOFZVTVRVQWACEFZUTVHIVTVRMZCARVHWBWCU
    TVCVTVHVJVTVHVJMZMVCVTVADEFZVIIWDBDRVIVAWDWEVIVHUGSTUMUHSTACDUIUJUKULUNPULU
    OUPUQURUS $.

  $( Membership of an integer in a finite set of sequential integers starting
     at 0.  (Contributed by Alexander van der Vekens, 25-May-2018.) $)
  elfz2z $p |- ( ( K e. ZZ /\ N e. ZZ )
                 -> ( K e. ( 0 ... N ) <-> ( 0 <_ K /\ K <_ N ) ) ) $=
    ( cc0 cfz co wcel cn0 wa cle wbr cz w3a elfz2nn0 adantr elnn0z cr wi adantl
    zre ex df-3an bitri wb nn0ge0 simpll anim1i 0red letr syl3anc simplbi2 syld
    sylibr expcomd imp31 jca impbid2 pm5.32rd bitrid ) ACBDEFZAGFZBGFZHZABIJZHZ
    AKFZBKFZHZCAIJZVCHZUSUTVAVCLVDABMUTVAVCUAUBVGVCVBVHVGVCVBVHUCVGVCHZVBVHUTVH
    VAAUDNVJVHVBVJVHHZUTVAVKVEVHHUTVJVEVHVEVFVCUEUFAOULVGVCVHVAVGVHVCVAVGVICBIJ
    ZVAVGCPFAPFZBPFZVIVLQVGUGVEVMVFASNVFVNVEBSRCABUHUIVFVLVAQVEVAVFVLBOUJRUKUMU
    NUOTUPTUQUR $.

  $( If there are two elements in a finite set of sequential integers starting
     at 0, these two elements as well as the upper bound are nonnegative
     integers.  (Contributed by Alexander van der Vekens, 7-Apr-2018.) $)
  2elfz3nn0 $p |- ( ( A e. ( 0 ... N ) /\ B e. ( 0 ... N ) )
                    -> ( A e. NN0 /\ B e. NN0 /\ N e. NN0 ) ) $=
    ( cc0 cfz co wcel cn0 w3a elfznn0 cle wbr wi elfz2nn0 wa 3anass simplbi2com
    3adant3 sylbi mpan9 ) ADCEFZGAHGZBUAGZUBBHGZCHGZIZACJUCUDUEBCKLZIUBUFMZBCNU
    DUEUHUGUFUBUDUEOUBUDUEPQRST $.

  $( The addition of two members of a finite set of sequential integers
     starting at 0 is commutative.  (Contributed by Alexander van der Vekens,
     22-May-2018.)  (Revised by Alexander van der Vekens, 9-Jun-2018.) $)
  fz0addcom $p |- ( ( A e. ( 0 ... N ) /\ B e. ( 0 ... N ) )
                    -> ( A + B ) = ( B + A ) ) $=
    ( cc0 cfz co wcel cc caddc wceq elfznn0 nn0cnd addcom syl2an ) ADCEFZGZAHGB
    HGABIFBAIFJBOGZPAACKLQBBCKLABMN $.

  $( If the sum of two integers of a 0-based finite set of sequential integers
     is greater than the upper bound, the difference between one of the
     integers and the difference between the upper bound and the other integer
     is in the 0-based finite set of sequential integers with the first integer
     as upper bound.  (Contributed by Alexander van der Vekens, 7-Apr-2018.)
     (Revised by Alexander van der Vekens, 31-May-2018.) $)
  2elfz2melfz $p |- ( ( A e. ( 0 ... N ) /\ B e. ( 0 ... N ) )
                  -> ( N < ( A + B ) -> ( B - ( N - A ) ) e. ( 0 ... A ) ) ) $=
    ( cc0 co wcel wa caddc wbr cmin cle cz wi adantr cr zre ad2antrr adantl imp
    zred cfz clt elfzelz elfzel2 simplr zsubcl adantlr zsubcld zaddcl expcom id
    cn0 ltsub1d anim12i resubcld readdcl simpll jca ltle 3syl zcn subidd cc w3a
    wceq simp3 simp1 addcomd oveq1d subsub3 eqtr4d syl3anc sylibd sylbid elnn0z
    breq12d sylanbrc exp31 syl2anc mpan9 elfznn0 zcnd npcan breqtrrd lesubadd2d
    elfzle2 syl mpbird elfz2nn0 syl3anbrc ex ) ADCUAEZFZBWLFZGZCABHEZUBIZBCAJEZ
    JEZDAUAEFZWOWQGWSULFZAULFZWSAKIZWTWOWQXAWMALFZWNWQXAMZADCUCZWNCLFZBLFZXDXEM
    BDCUDBDCUCZXGXHGZXDWQXAXJXDGZWQGWSLFZDWSKIZXAXKXLWQXKBWRXGXHXDUEXGXDWRLFXHC
    AUFUGUHNXKWQXMXKWQCCJEZWPCJEZUBIZXMXKCWPCXGCOFZXHXDCPZQZXJXDWPOFZXHXDXTMXGX
    DXHXTXDXHGWPABUITUJRSXSUMXKXPXNXOKIZXMXKXQBOFZGZAOFZGZXNOFZXOOFZGXPYAMXJYCX
    DYDXGXQXHYBXRBPUNAPUNYEYFYGXQYFYBYDXQCCXQUKZYHUOQYEWPCYCYDXTYBYDXTMXQYDYBXT
    ABUPUJRSXQYBYDUQUOURXNXOUSUTXKXNDXOWSKXGXNDVEXHXDXGCCVAZVBQXKBVCFZCVCFZAVCF
    ZXOWSVEXJYJXDXHYJXGBVARNXGYKXHXDYIQXDYLXJAVARYJYKYLVDZXOBAHEZCJEWSYMWPYNCJY
    MABYJYKYLVFYJYKYLVGVHVIBCAVJVKVLVPVMVNSWSVOVQVRVSVTSWMXBWNWQACWAQWOXCWQWOXC
    BWRAHEZKIWOBCYOKWNBCKIWMBDCWFRWOYKYLGZYOCVEWMYPWNWMYKYLWMCADCUDZWBWMAXFWBUR
    NCAWCWGWDWOBWRAWNYBWMWNBXITRWMWROFWNWMCAWMCYQTWMAXFTZUONWMYDWNYRNWEWHNWSAWI
    WJWK $.

  $( The sum of two integers in 0-based finite sets of sequential integers is
     greater than or equal to zero.  (Contributed by Alexander van der Vekens,
     8-Jun-2018.) $)
  fz0addge0 $p |- ( ( A e. ( 0 ... M ) /\ B e. ( 0 ... N ) )
                    -> 0 <_ ( A + B ) ) $=
    ( cc0 cfz co wcel wa cn0 cr cle wbr caddc elfznn0 anim12i nn0ge0 jca addge0
    nn0re 3syl ) AECFGHZBEDFGHZIAJHZBJHZIZAKHZBKHZIZEALMZEBLMZIZIEABNGLMUBUDUCU
    EACOBDOPUFUIULUDUGUEUHATBTPUDUJUEUKAQBQPRABSUA $.

  $( Membership of an integer in a finite set of sequential integers with the
     integer as upper bound and a lower bound less than or equal to the
     integer.  (Contributed by AV, 21-Oct-2018.) $)
  elfzlble $p |- ( ( N e. ZZ /\ M e. NN0 ) -> N e. ( ( N - M ) ... N ) ) $=
    ( cz wcel cn0 wa cmin co cuz cfv cfz cle wbr zsubcl sylan2 simpl cc0 nn0ge0
    nn0z cr adantl zre nn0re subge02 syl2an mpbid eluz2 syl3anbrc eluzfz2 syl
    wb ) BCDZAEDZFZBBAGHZIJDZBUOBKHDUNUOCDZULUOBLMZUPUMULACDUQASBANOULUMPUNQALM
    ZURUMUSULARUAULBTDATDUSURUKUMBUBAUCBAUDUEUFUOBUGUHUOBUIUJ $.

  $( Membership of an element of a finite set of sequential integers in a
     finite set of sequential integers with the same upper bound and a lower
     bound less than the upper bound.  (Contributed by AV, 21-Oct-2018.) $)
  elfzelfzlble $p |- ( ( M e. ZZ /\ K e. ( 0 ... N ) /\ N < ( M + K ) )
                       -> K e. ( ( N - M ) ... N ) ) $=
    ( cz wcel cc0 cfz co wbr w3a cle wa elfz2 adantr anim2i syl adantl 3jca cr
    wi caddc clt cmin 3simpc sylbi simpl ancomd zsubcl 3adant3 elfzel2 zred zre
    simprr elfzelz simp1 readdcl 3adant1 ltle syl2anc lesubadd2 sylibrd elfzle2
    3impia 3ad2ant2 jca32 sylibr ) BDEZAFCGHEZCBAUAHZUBIZJZCBUCHZDEZCDEZADEZJZV
    LAKIZACKIZLLAVLCGHEVKVPVQVRVGVHVPVJVGVHLZVGVNVOLZLZVPVHVTVGVHFDEZVNVOJZFAKI
    VRLZLVTAFCMWCVTWDWBVNVOUDNUEOWAVMVNVOWAVNVGLVMWAVGVNVTVNVGVNVOUFZOUGCBUHPVT
    VNVGWEQVGVNVOUMRPUIVGVHVJVQVSCSEZBSEZASEZJZVJVQTVSWFWGWHVHWFVGVHCAFCUJUKQVG
    WGVHBULNVHWHVGVHAAFCUNUKQRWIVJCVIKIZVQWIWFVISEZVJWJTWFWGWHUOWGWHWKWFBAUPUQC
    VIURUSCBAUTVAPVCVHVGVRVJAFCVBVDVEAVLCMVF $.

  $( A member of a finite set of sequential integers starting at 2 is a
     positive integer.  (Contributed by AV, 5-Apr-2026.) $)
  elfz2nn $p |- ( K e. ( 2 ... N ) -> K e. NN ) $=
    ( c2 cfz co wcel c1 cn cuz cfv wss 2eluzge1 fzss1 ax-mp sseli elfznn syl )
    ACBDEZFAGBDEZFAHFRSACGIJFRSKLCGBMNOABPQ $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Half-open integer ranges - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Join a predecessor to the beginning of an open integer interval.
     Generalization of ~ fzo0sn0fzo1 .  (Contributed by AV, 14-Jul-2020.) $)
  fzopred $p |- ( ( M e. ZZ /\ N e. ZZ /\ M < N )
                 -> ( M ..^ N ) = ( { M } u. ( ( M + 1 ) ..^ N ) ) ) $=
    ( cz wcel clt wbr w3a cfzo co caddc cun csn cfz wceq fzolb fzofzp1 fzosplit
    c1 sylbir syl fzosn 3ad2ant1 uneq1d eqtrd ) ACDZBCDZABEFZGZABHIZAARJIZHIZUJ
    BHIZKZALZULKUHUJABMIDZUIUMNUHAUIDUOABOABAPSABUJQTUHUKUNULUEUFUKUNNUGAUAUBUC
    UD $.

  $( Join a predecessor and a successor to the beginning and the end of an open
     integer interval.  This theorem holds even if ` N = M ` (then
     ` ( M ... N ) = { M } = ( { M } u. (/) ) u. { M } ) ` .  (Contributed by
     AV, 14-Jul-2020.) $)
  fzopredsuc $p |- ( N e. ( ZZ>= ` M ) -> ( M ... N )
                           = ( ( { M } u. ( ( M + 1 ) ..^ N ) ) u. { N } ) ) $=
    ( wceq wcel cfz co csn c1 caddc cfzo cun wi cz wa oveq1 sylan9eqr uneq1d c0
    wbr ex cuz cfv unidm eqcomi fzsn sneq oveq1d uneq12d clt wn cle zre peano2z
    lep1d zred lenltd mpbid wb fzonlt0 mpancom uneq2d un0 3eqtr4a eluzelz syl11
    eqtrdi fzisfzounsn adantl w3a eluz2 simpl1 simpl2 wne nesym cr ltlen syl2an
    biimprd exp4b 3imp biimtrrid imp 3jca sylbi impcom fzopred eqtrd pm2.61i
    syl ) ABCZBAUAUBDZABEFZAGZAHIFZBJFZKZBGZKZCZLBMDZWJWSWKWTWJWSWTWJNWQWQWQKZW
    LWRXAWQWQUCUDWJWTWLBBEFWQABBEOBUEPWJWTWRWQBHIFZBJFZKZWQKXAWJWPXDWQWJWMWQWOX
    CABUFWJWNXBBJABHIOUGUHQWTXDWQWQWTXDWQRKWQWTXCRWQWTXBBUISUJZXCRCZWTBXBUKSXEW
    TBBULZUNWTBXBXGWTXBBUMZUOUPUQXBMDWTXEXFURXHXBBUSUTUQVAWQVBVFQPVCTABVDVEWJUJ
    ZWKWSXIWKNZWLABJFZWQKZWRWKWLXLCXIABVGVHXJXKWPWQXJAMDZWTABUISZVIZXKWPCWKXIXO
    WKXMWTABUKSZVIZXIXOLABVJXQXIXOXQXINXMWTXNXMWTXPXIVKXMWTXPXIVLXQXIXNXIBAVMZX
    QXNBAVNXMWTXPXRXNLXMWTXPXRXNXMWTNXNXPXRNZXMAVODBVODXNXSURWTAULXGABVPVQVRVSV
    TWAWBWCTWDWEABWFWIQWGTWH $.

  $( Join 0 and a successor to the beginning and the end of an open integer
     interval starting at 1.  (Contributed by AV, 14-Jul-2020.) $)
  1fzopredsuc $p |- ( N e. NN0
                    -> ( 0 ... N ) = ( ( { 0 } u. ( 1 ..^ N ) ) u. { N } ) ) $=
    ( cn0 wcel cc0 cuz cfv cfz co csn c1 cfzo cun wceq elnn0uz caddc fzopredsuc
    0p1e1 oveq1i uneq2i uneq1i eqtrdi sylbi ) ABCADEFCZDAGHZDIZJAKHZLZAIZLZMANU
    CUDUEDJOHZAKHZLZUHLUIDAPULUGUHUKUFUEUJJAKQRSTUAUB $.

  $( An element of an open integer interval starting at 1 joined by 0 and a
     successor at the beginning and the end is either 0 or an element of the
     open integer interval or the successor.  (Contributed by AV,
     14-Jul-2020.) $)
  el1fzopredsuc $p |- ( N e. NN0 -> ( I e. ( 0 ... N )
                              <-> ( I = 0 \/ I e. ( 1 ..^ N ) \/ I = N ) ) ) $=
    ( cn0 wcel cc0 co wceq w3o cz csn cun wi wa wo elun wb elsng adantl df-3or
    ex cfz cfzo elfzelz 1fzopredsuc eleq2d orbi1i orbi1d orbi12d bitrid biimpri
    c1 bitri biimtrdi com23 sylbid mpdi c0ex snid eleq1 mpbird snidg syl5ibrcom
    a1i idd 3orim123d imp sylib sylibr adantr impbid ) BCDZAEBUAFZDZAEGZAUKBUBF
    ZDZABGZHZVKVMAIDZVRAEBUCVKVMAEJZVOKZBJZKZDZVSVRLVKVLWCABUDUEZVKVSWDVRVKVSWD
    VRLVKVSMZWDVNVPNZVQNZVRWDAVTDZVPNZAWBDZNZWFWHWDAWADZWKNWLAWAWBOWMWJWKAVTVOO
    UFULZWFWJWGWKVQWFWIVNVPVSWIVNPVKAEIQRUGVSWKVQPVKABIQRUHUIVRWHVNVPVQSUJUMTUN
    UOUPVKVRVMVKVRMZVMWDWOWLWDWOWIVPWKHZWLVKVRWPVKVNWIVPVPVQWKVNWILVKVNWIEVTDZW
    QVNEUQURVCAEVTUSUTVCVKVPVDVKWKVQBWBDBCVAABWBUSVBVEVFWIVPWKSVGWNVHVKVMWDPVRW
    EVIUTTVJ $.

  $( Subtracting a difference from a number which is not less than the
     difference results in a bounded nonnegative integer.  (Contributed by
     Alexander van der Vekens, 21-May-2018.) $)
  subsubelfzo0 $p |- ( ( A e. ( 0 ..^ N ) /\ I e. ( 0 ..^ N )
                 /\ -. I < ( N - A ) ) -> ( I - ( N - A ) ) e. ( 0 ..^ A ) ) $=
    ( cc0 co wcel cmin clt wbr w3a cz cn0 wi wa cle cr wb adantr syl2anr adantl
    cfzo wn cuz cfv cn elfzo0 nnre 3ad2ant2 nn0re resubcl 3ad2ant1 lenlt bicomd
    syl2anc biimpa nnz zsubcl syl2an impancom imp subge0 mpbird elnn0z sylanbrc
    nn0z ltle simplr1 nn0sub mpbid elnn0uz sylib ltsub1d wceq nncn nn0cn breq2d
    cc nncan biimpd sylbid com3l 3impia impcom 3jca exp31 biimtrid 3adant2 3imp
    ex sylbi elfzo2 sylibr ) ADCUAEZFZBWMFZBCAGEZHIUBZJBWPGEZDUCUDFZAKFZWRAHIZJ
    ZWRDAUAEFWNWOWQXBWNALFZCUEFZACHIZJWOWQXBMZMZACUFXCXEXGXDWOBLFZXDBCHIZJZXCXE
    NZXFBCUFXKXJWQXBXKXJNZWQNZWSWTXAXMWRLFZWSXMWPBOIZXNXLWQXOXLWPPFZBPFZWQXOQXJ
    CPFZAPFZXPXKXDXHXRXICUGZUHZXCXSXEAUIZRZCAUJZSXJXQXKXHXDXQXIBUIZUKTXPXQNXOWQ
    WPBULUMUNUOXMWPLFZXHXOXNQXLYFWQXLWPKFZDWPOIZYFXJCKFZWTYGXKXDXHYIXICUPUHXCWT
    XEAVERZCAUQSXLYHACOIZXKXJYKXCXJXEYKXCXSXRXEYKMXJYBYAACVFURUSUTXJXRXSYHYKQXK
    YAYCCAVASVBWPVCVDRXHXDXIXKWQVGWPBVHUNVIWRVJVKXLWTWQXKWTXJYJRRXLXAWQXJXKXAXH
    XDXIXKXAMXKXHXDNZXIXAXCYLXIXAMZMXEXCYLYMXCYLNZXIWRCWPGEZHIZXAYNBCWPYLXQXCXH
    XQXDYERTYLXRXCXDXRXHXTTZTYLXRXSXPXCYQYBYDSVLYNYPXAYNYOAWRHYLCVQFZAVQFYOAVMX
    CXDYRXHCVNTAVOCAVRSVPVSVTWIRWAWBWCRWDWEWFWGWJWHWRDAWKWL $.

  ${
    $d F i $.  $d M i $.  $d P i $.
    $( Two functions over a half-open range of nonnegative integers are equal
       if and only if their domains have the same length and the function
       values are the same at each position.  (Contributed by Alexander van der
       Vekens, 1-Jul-2018.) $)
    2ffzoeq $p |- ( ( ( M e. NN0 /\ N e. NN0 ) /\ ( F : ( 0 ..^ M ) --> X
                             /\ P : ( 0 ..^ N ) --> Y ) ) -> ( F = P
              <-> ( M = N /\ A. i e. ( 0 ..^ M ) ( F ` i ) = ( P ` i ) ) ) ) $=
      ( cc0 wceq wcel wa cfzo co wf wb wi c0 adantl impcom adantr cn0 cfv eqeq1
      cv wral anbi1d f0bi wfn ffn fndmu cle cz 0z nn0z fzon sylancr nn0ge0 0red
      wbr nn0re letri3d biimprd mpand sylbird syl5com ex syl2imc biimtrdi com3l
      sylbir imp a1i oveq2 fzo0 eqtrdi feq2d bitrdi 3imtr4d feq2i bitri biimpac
      imbi2d anbi12d eqtr3 com12 expd impbid ral0 raleqdv mpbiri biantrud bitrd
      syl wn anim12i eqfnfv2 wne df-ne cn elnnne0 clt w3a 0zd nnz nngt0 fzoopth
      3jca simpr anim1d anim1i impbid1 impancom biimtrrid pm2.61ian ) DHIZDUAJZ
      EUAJZKZHDLMZFCNZHELMZGANZKZKZCAIZDEIZBUDZCUBYGAUBIZBXSUEZKZOXOYDKZYEYFYJY
      KYEYFYDXOYEYFPZYCXRXOYLPXOYCXRYLXOCQIZYBKZXRYEHEIZPZPZYCXRYLPYNYQPXOYEYNX
      RYOYEYNAQIZYBKXRYOPZYEYMYRYBCAQUCUFYRYBYSYRQGANZYBYSPAGUGZYBAYAUHZYTAQUHZ
      YSYAGAUIZQGAUIUUBUUCYSUUBUUCKYAQIZXRYOYAQAUJXRUUEEHUKUSZYOXRHULJZEULJZUUF
      UUEOUMXQUUHXPEUNRHEUOUPXQUUFYOPXPXQHEUKUSZUUFYOEUQXQYOUUIUUFKXQHEXQUREUTV
      AVBVCRVDVEVFVGVJVKVHVIVLXOXTYMYBXOXTQFCNZYMXOXSQFCXOXSHHLMZQDHHLVMZHVNZVO
      ZVPCFUGZVQUFXOYLYPXRXOYFYOYEDHEUCWBWBVRVISSYDXOYFYEPZYCXOUUPPXRYCXOYFYEXO
      YFKZYCYEUUQYCYMYRKYEUUQXTYMYBYRXOXTYMOYFXOXTUUKFCNZYMXOXSUUKFCUULVPUURUUJ
      YMUUKQFCUUMVSUUOVTVQTUUQEHIZYBYROYFXOUUSDEHUCWAUUSYBUUKGANZYRUUSYAUUKGAEH
      HLVMVPUUTYTYRUUKQGAUUMVSUUAVTVQWMWCCAQWDVHWEWFRSWGXOYFYJOYDXOYIYFXOYIYHBQ
      UEYHBWHXOYHBXSQUUNWIWJWKTWLXOWNZYDKZYEXSYAIZYIKZYJUVBCXSUHZUUBKZYEUVDOYDU
      VFUVAYCUVFXRXTUVEYBUUBXSFCUIUUDWORRBXSYACAWPWMYDUVAUVDYJOZXRUVAUVGPYCUVAD
      HWQZXRUVGDHWRXPUVHXQUVGXPUVHKDWSJZXQUVGPDWTUVIXQUVGUVIXQKZUVDYJUVJUVCYFYI
      UVJUVCHHIZYFKZYFUVJUUGDULJZHDXAUSZXBZUVCUVLOUVIUVOXQUVIUUGUVMUVNUVIXCDXDD
      XEXGTHEHDXFWMUVKYFXHVHXIYFUVCYIDEHLVMXJXKVFVJXLXMTSWLXN $.
  $}

  $( A member of a half-open range of integers starting at 2 is a positive
     integer.  (Contributed by AV, 5-Apr-2026.) $)
  elfzo2nn $p |- ( K e. ( 2 ..^ N ) -> K e. NN ) $=
    ( c2 cfzo co wcel cuz cfv cz clt wbr w3a cn elfzo2 eluz2nn 3ad2ant1 sylbi )
    ACBDEFACGHFZBIFZABJKZLAMFZACBNRSUATAOPQ $.

  $( If one factor of a product of integers is at least 2 and less then the
     product, so is the second factor.  (Contributed by AV, 5-Apr-2026.) $)
  nnmul2 $p |- ( ( A e. ( 2 ..^ N ) /\ B e. NN /\ ( A x. B ) = N )
                 -> B e. ( 2 ..^ N ) ) $=
    ( c2 co wcel cmul wceq w3a wbr clt c1 wi wa wb eqeq1d sylbid sylbi 3ad2ant1
    cz cfzo cn cle cuz wo elnn1uz2 oveq2 adantr cr elfzoelz zred ax-1rid elfzo2
    cfv syl breq2 eqcoms adantl eluzelre ltnrd pm2.21d impancom 3adant2 ex 2a1d
    eluzle jaoi 3imp21 eluz2gt1 crp nnrp 3ad2ant2 ltmulgt12d mpbid 3ad2ant3 nnz
    2z a1i elfzoel2 elfzo syl3anc mpbir2and ) ADCUAEZFZBUBFZABGEZCHZIZBWCFZDBUC
    JZBCKJZWEWDWGWJWEBLHZBDUDUNZFZUEWDWGWJMZMZBUFWLWPWNWLWDWOWLWDNWGALGEZCHZWJW
    LWGWROWDWLWFWQCBLAGUGPUHWDWRWJMWLWDWRACHZWJWDWQACWDAUIFZWQAHWDAADCUJUKZAULU
    OPWDAWMFZCTFZACKJZIZWSWJMZADCUMZXBXDXFXCXBWSXDWJXBWSNXDAAKJZWJWSXDXHOZXBXIC
    ACAAKUPUQURXBXHWJMWSXBXHWJXBADAUSUTVAUHQVBVCRQURQVDWNWJWDWGDBVFVEVGRVHWHBWF
    KJZWKWHLAKJZXJWDWEXKWGWDXEXKXGXBXCXKXDAVISRSWHABWDWEWTWGXASWEWDBVJFWGBVKVLV
    MVNWGWDXJWKOWEWFCBKUPVOVNWHBTFZDTFZXCWIWJWKNOWEWDXLWGBVPVLXMWHVQVRWDWEXCWGA
    DCVSSBDCVTWAWB $.

  $( A factor of a product of integers is at least 2 and less then the product
     iff the second factor is at least 2 and less then the product.
     (Contributed by AV, 5-Apr-2026.) $)
  nnmul2b $p |- ( ( A e. NN /\ B e. NN /\ ( A x. B ) = N )
                  -> ( A e. ( 2 ..^ N ) <-> B e. ( 2 ..^ N ) ) ) $=
    ( cn wcel cmul co wceq w3a c2 cfzo wi nnmul2 a1d 3exp com14 wa simpr simpl1
    3imp nnmulcom eqcomd 3adant3 simp3 eqtrd adantr syl3anc ex impbid ) ADEZBDE
    ZABFGZCHZIZAJCKGZEZBUOEZUJUKUMUPUQLUPUKUMUJUQUPUKUMUJUQLUPUKUMIUQUJABCMNOPT
    UNUQUPUNUQQUQUJBAFGZCHZUPUNUQRUJUKUMUQSUNUSUQUNURULCUJUKURULHUMUJUKQULURABU
    AUBUCUJUKUMUDUEUFBACMUGUHUI $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The floor and ceiling functions  - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The ceiling of half of an integer greater than 2 is greater than or equal
     to 2.  (Contributed by AV, 4-Sep-2025.) $)
  2ltceilhalf $p |- ( N e. ( ZZ>= ` 3 ) -> 2 <_ ( |^ ` ( N / 2 ) ) ) $=
    ( c3 cuz cfv wcel wceq c1 caddc co c2 cdiv cceil cle wbr cneg wa 2re c4 a1i
    cr uzp1 ex-ceil leidi breq2 mpbiri adantr ax-mp fvoveq1 breqtrrid rehalfcld
    wo eluzelre ceilcld zred cmul 2t2e4 eluzle eqbrtrid cc0 clt pm3.2i lemuldiv
    wb 2pos mp3an2i mpbid ceilged letrd 3p1e4 fveq2i eleq2s jaoi syl ) ABCDEABF
    ZABGHIZCDZEZUKJAJKIZLDZMNZBAUAVNVTVQVNJBJKIZLDZVSMWBJFZWAOLDGOFZPJWBMNZUBWC
    WEWDWCWEJJMNJQUCWBJJMUDUEUFUGABJLKUHUIVTARCDZVPAWFEZJVRVSJTEZWGQSWGARAULZUJ
    ZWGVSWGVRWJUMUNWGJJUOIZAMNZJVRMNZWGWKRAMUPRAUQURWHWGATEWHUSJUTNZPZWLWMVCQWI
    WOWGWHWNQVDVASJAJVBVEVFWGVRWJVGVHVORCVIVJVKVLVM $.

  $( The ceiling of half of an integer greater than two is greater than one.
     (Contributed by AV, 2-Nov-2025.) $)
  ceilhalfgt1 $p |- ( N e. ( ZZ>= ` 3 ) -> 1 < ( |^ ` ( N / 2 ) ) ) $=
    ( c3 cuz cfv wcel c1 c2 cdiv co cceil cr 2re a1i eluzelre rehalfcld ceilcld
    1red zred clt wbr 1lt2 2ltceilhalf ltletrd ) ABCDEZFGAGHIZJDZUDQGKEUDLMUDUF
    UDUEUDABANOPRFGSTUDUAMAUBUC $.

  ${
    ceilhalfelfzo1.j $e |- J = ( 1 ..^ ( |^ ` ( N / 2 ) ) ) $.
    $( A positive integer less than (the ceiling of) half of another integer is
       in the half-open range of positive integers up to the other integer.
       (Contributed by AV, 7-Sep-2025.) $)
    ceilhalfelfzo1 $p |- ( N e. NN -> ( K e. J -> K e. ( 1 ..^ N ) ) ) $=
      ( wcel c1 c2 cdiv co cceil cfv cfzo cn eleq2i cuz wss cz cle wbr nnre nnz
      rehalfcld ceilcld cn0 nnnn0 2nn nn0ledivnn sylancl ceille eluz2 syl3anbrc
      cr syl3anc fzoss2 syl sseld biimtrid ) BAEBFCGHIZJKZLIZECMEZBFCLIZEAUTBDN
      VAUTVBBVACUSOKEZUTVBPVAUSQECQEZUSCRSZVCVAURVACCTUBZUCCUAZVAURULEVDURCRSZV
      EVFVGVACUDEGMEVHCUEUFCGUGUHURCUIUMUSCUJUKUSFCUNUOUPUQ $.

    gpgedgvtx1lem.i $e |- I = ( 0 ..^ N ) $.
    $( Lemma for ~ gpgedgvtx1 .  (Contributed by AV, 1-Sep-2025.)  (Proof
       shortened by AV, 8-Sep-2025.) $)
    gpgedgvtx1lem $p |- ( ( N e. ( ZZ>= ` 3 ) /\ X e. J ) -> X e. I ) $=
      ( c3 cuz cfv wcel wa c1 cfzo co wss cc0 fzo0ss1 a1i sseqtrrdi adantr syl
      cn wi eluz3nn ceilhalfelfzo1 imp sseldd ) CGHIJZDBJZKLCMNZADUHUJAOUIUHUJP
      CMNZAUJUKOUHCQRFSTUHUIDUJJZUHCUBJUIULUCCUDBDCEUEUAUFUG $.
  $}

  $( Two times a positive integer less than (the ceiling of) half of another
     integer is less than the other integer.  This theorem would hold even for
     integers less than 3, but then a corresponding ` K ` would not exist.
     (Contributed by AV, 9-Sep-2025.) $)
  2tceilhalfelfzo1 $p |- ( ( N e. ( ZZ>= ` 3 )
                             /\ K e. ( 1 ..^ ( |^ ` ( N / 2 ) ) ) )
                         -> ( 2 x. K ) < N ) $=
    ( c1 c2 co cfv wcel c3 cmul clt wbr cn w3a wi cz nnz 3ad2ant1 cr adantr a1i
    cdiv cceil cfzo cuz elfzo1 cmin cle 3ad2ant2 zltlem1d wa nnre 1red resubcld
    eluzelre rehalfcld 3ad2ant3 simpr ceilm1lt syl lelttrd ex cc0 wb 2re ltmul2
    2pos syl112anc cc eluzelcn 2cnd wne 2ne0 divcan2d breq2d biimpd sylbid syld
    3exp com34 3imp sylbi impcom ) ACBDUAEZUBFZUCEGZBHUDFGZDAIEZBJKZWEALGZWDLGZ
    AWDJKZMWFWHNZWDAUEWIWJWKWLWIWJWFWKWHWIWJWFWKWHNWIWJWFMZWKAWDCUFEZUGKZWHWMAW
    DWIWJAOGWFAPQWJWIWDOGWFWDPUHUIWMWOAWCJKZWHWMWOWPWMWOUJAWNWCWMARGZWOWIWJWQWF
    AUKQZSWMWNRGZWOWJWIWSWFWJWDCWDUKWJULUMUHSWMWCRGZWOWFWIWTWJWFBHBUNUOUPZSWMWO
    UQWMWNWCJKZWOWMWTXBXAWCURUSSUTVAWMWPWGDWCIEZJKZWHWMWQWTDRGZVBDJKZWPXDVCWRXA
    XEWMVDTXFWMVFTAWCDVEVGWMXDWHWMXCBWGJWMBDWFWIBVHGWJHBVIUPWMVJDVBVKWMVLTVMVNV
    OVPVQVPVRVSVTWAWB $.

  $( A condition equivalent to ceiling.  Analogous to ~ flbi .  (Contributed by
     AV, 2-Nov-2025.) $)
  ceilbi $p |- ( ( A e. RR /\ B e. ZZ ) ->
                ( ( |^ ` A ) = B <-> ( A <_ B /\ B < ( A + 1 ) ) ) ) $=
    ( cr wcel cz wa cfv wceq cle wbr c1 caddc co clt cc wb syl2an adantl 3bitrd
    cneg cceil cfl ceilval adantr eqeq1d renegcl flcld zcn negcon1 eqcom znegcl
    zcnd a1i flbi simpl lenegd bicomd cmin peano2rem ltnegd 1red ltsubaddd 1cnd
    zre syl negsubdi syl2anr breq2d 3bitr3rd anbi12d ) ACDZBEDZFZAUAGZBHATZUBGZ
    TZBHZBTZVPHZABIJZBAKLMNJZFZVMVNVQBVKVNVQHVLAUCUDUEVKVPODBODZVRVTPVLVKVPVKVO
    AUFZUGULBUHZVPBUIQVMVTVPVSHZVSVOIJZVOVSKLMZNJZFZWCVTWGPVMVSVPUJUMVKVOCDVSED
    WGWKPVLWEBUKVOVSUNQVMWHWAWJWBVMWAWHVMABVKVLUOZVLBCDZVKBVDZRZUPUQVMBKURMZANJ
    VOWPTZNJWBWJVMWPAVLWPCDZVKVLWMWRWNBUSVERWLUTVMBKAWOVMVAWLVBVMWQWIVONVLWDKOD
    WQWIHVKWFVKVCBKVFVGVHVIVJSS $.

  $( The ceiling of one half is one.  (Contributed by AV, 2-Nov-2025.) $)
  ceilhalf1 $p |- ( |^ ` ( 1 / 2 ) ) = 1 $=
    ( c1 c2 cdiv co cceil cfv wceq cle wbr caddc clt halfre halflt1 ltleii cmin
    1re cc0 1m1e0 halfgt0 wcel eqbrtri ltsubaddi cr cz wa wb 1z ceilbi mpbir2an
    mpbi mp2an ) ABCDZEFAGZULAHIZAULAJDKIZULALPMNAAODZULKIUOUPQULKRSUAAAULPPLUB
    UJULUCTAUDTUMUNUOUEUFLUGULAUHUKUI $.

  $( Half of a real number greater than or equal to two is greater than or
     equal to one.  (Contributed by AV, 2-Nov-2025.) $)
  rehalfge1 $p |- ( X e. ( 2 [,) +oo ) -> 1 <_ ( X / 2 ) ) $=
    ( c2 cpnf cico co wcel c1 cmul cle wbr cdiv 2cn mullidi cxr 2re pnfxr id cr
    a1i cc0 rexri icogelbd eqbrtrid 1red wss 0le2 0xr icossico2d ax-mp rge0ssre
    sstri sseli crp 2rp lemuldivd mpbid ) ABCDEZFZGBHEZAIJGABKEIJURUSBAIBLMURBC
    ABNFURBOUASCNFZURPSURQUBUCURGABURUDUQRAUQTCDEZRTBIJZUQVAUEUFVBBTCTNFVBUGSUT
    VBPSVBQUHUIUJUKULBUMFURUNSUOUP $.

  $( The ceiling of half of a positive integer is a positive integer.
     (Contributed by AV, 2-Nov-2025.) $)
  ceilhalfnn $p |- ( N e. NN -> ( |^ ` ( N / 2 ) ) e. NN ) $=
    ( cn wcel c2 cdiv co cceil cfv cz c1 cle wbr nnre rehalfcld ceilcld wceq wo
    cuz cr sylanbrc elnn1uz2 1le1 ceilhalf1 eqtrdi breqtrrid 1red eluzelre zred
    fvoveq1 cpnf cico eluzle wa 2re elicopnf ax-mp rehalfge1 ceilged letrd jaoi
    wb syl sylbi elnnz1 ) ABCZADEFZGHZICJVGKLZVGBCVEVFVEAAMNOVEAJPZADRHCZQVHAUA
    VIVHVJVIJJVGKUBVIVGJDEFGHJAJDGEUIUCUDUEVJJVFVGVJUFVJADAUGZNZVJVGVJVFVLOUHVJ
    ADUJUKFCZJVFKLVJASCZDAKLZVMVKDAULDSCVMVNVOUMVAUNDAUOUPTAUQVBVJVFVLURUSUTVCV
    GVDT $.

  $( 1 is in the half-open integer range from 1 to the ceiling of half of an
     integer greater than two is greater than one.  (Contributed by AV,
     2-Nov-2025.) $)
  1elfzo1ceilhalf1 $p |- ( N e. ( ZZ>= ` 3 )
                            -> 1 e. ( 1 ..^ ( |^ ` ( N / 2 ) ) ) ) $=
    ( c3 cuz cfv wcel c1 cn c2 cdiv co cceil clt wbr 1nn a1i eluz3nn ceilhalfnn
    cfzo syl ceilhalfgt1 elfzo1 syl3anbrc ) ABCDEZFGEZAHIJKDZGEZFUELMFFUERJEUDU
    CNOUCAGEUFAPAQSATUEFUAUB $.

  $( The floor of the reciprocal of an integer greater than 1 is 0.
     (Contributed by AV, 10-Apr-2026.) $)
  nnge2recfl0 $p |- ( N e. ( ZZ>= ` 2 ) -> ( |_ ` ( 1 / N ) ) = 0 ) $=
    ( c2 cuz cfv wcel c1 cdiv co cc0 cico cfl wceq nnge2recico01 ico01fl0 syl )
    ABCDEFAGHZIFJHEPKDILAMPNO $.

  $( The floor of an integer minus the reciprocal of a positive integer is the
     integer minus 1.  (Contributed by AV, 10-Apr-2026.) $)
  flmrecm1 $p |- ( ( M e. ZZ /\ N e. NN )
                   -> ( |_ ` ( M - ( 1 / N ) ) ) = ( M - 1 ) ) $=
    ( cz wcel wa c1 co cmin cfl cfv caddc cc adantr adantl wceq syl cc0 cle wbr
    cr cn cdiv peano2zm zcnd nnrecre recnd zcn npcan1 eqcomd oveq1d assraddsubd
    1cnd fveq2d 1red resubcld flzadd syl2an cico clt nnge1 crp wb nnrp divle1le
    syl2anc mpbird subge0d nnrecgt0 ltsubposd mpbid cxr w3a 0re 1xr pm3.2i mp1i
    elico2 mpbir3and ico01fl0 oveq2d addridd eqtrd 3eqtrd ) ACDZBUADZEZAFBUBGZH
    GZIJAFHGZFWGHGZKGZIJZWIWJIJZKGZWIWFWHWKIWFWHWIFWGWDWILDWEWDWIAUCZUDMZWFULWE
    WGLDWDWEWGBUEZUFNWFAWIFKGZWGHWDAWROZWEWDALDZWSAUGWTWRAAUHUIPMUJUKUMWDWICDWJ
    TDZWLWNOWEWOWEFWGWEUNZWQUOZWJWIUPUQWFWNWIQKGWIWFWMQWIKWEWMQOZWDWEWJQFURGDZX
    DWEXEXAQWJRSZWJFUSSZXCWEXFWGFRSZWEXHFBRSZBUTWEFTDBVADXHXIVBXBBVCFBVDVEVFWEF
    WGXBWQVGVFWEQWGUSSXGBVHWEWGFWQXBVIVJQTDZFVKDZEXEXAXFXGVLVBWEXJXKVMVNVOQFWJV
    QVPVRWJVSPNVTWFWIWPWAWBWC $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The modulo (remainder) operation - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Expressing the floor of a division by the modulo operator.  (Contributed
     by AV, 6-Jun-2020.) $)
  fldivmod $p |- ( ( A e. RR /\ B e. RR+ )
                   -> ( |_ ` ( A / B ) ) = ( ( A - ( A mod B ) ) / B ) ) $=
    ( cr wcel crp wa cdiv cfl cfv cmul cmo caddc cmin wceq rerpdivcl flcld zcnd
    co adantl oveq1d rpcn mulcld modcl recnd pncand addcld subcld cc0 wne rpne0
    cc divmul3d mpbird flpmodeq eqtr3d ) ACDZBEDZFZABGRZHIZBJRZABKRZLRZVBMRZBGR
    ZUTAVBMRZBGRURVEUTNVDVANURVAVBURUTBURUTURUSABOPQZUQBUKDUPBUASZUBZURVBABUCUD
    ZUEURVDUTBURVCVBURVAVBVIVJUFVJUGVGVHUQBUHUIUPBUJSULUMURVDVFBGURVCAVBMABUNTT
    UO $.

  $( Expressing the ceiling of a division by the modulo operator.  (Contributed
     by AV, 7-Sep-2025.) $)
  ceildivmod $p |- ( ( A e. RR /\ B e. RR+ )
               -> ( |^ ` ( A / B ) ) = ( ( A + ( ( B - A ) mod B ) ) / B ) ) $=
    ( cr wcel cdiv co cfv cneg cfl cmo cmin caddc wceq cc adantr adantl divnegd
    sylan eqtrd recnd crp wa cceil rerpdivcl ceilval syl recn rpcn rpne0 fveq2d
    cc0 wne renegcl fldivmod negeqd modcl subcld negsubdid oveq1d negmod oveq2d
    negnegd 3eqtrd ) ACDZBUADZUBZABEFZUCGZVGHZIGZHZAHZVLBJFZKFZHZBEFZABAKFBJFZL
    FZBEFVFVGCDVHVKMABUDVGUEUFVFVKVNBEFZHVPVFVJVSVFVJVLBEFZIGZVSVFVIVTIVFABVDAN
    DVEAUGZOVEBNDVDBUHPZVEBUKULVDBUIPZQUJVDVLCDZVEWAVSMAUMZVLBUNRSUOVFVNBVFVLVM
    VDVLNDVEVDVLWFTOZVFVMVDWEVEVMCDWFVLBUPRTZUQWCWDQSVFVOVRBEVFVOVLHZVMLFAVMLFV
    RVFVLVMWGWHURVFWIAVMLVDWIAMVEVDAWBVBOUSVFVMVQALABUTVAVCUSVC $.

  $( The ceiling of half of 5 is 3.  (Contributed by AV, 7-Sep-2025.) $)
  ceil5half3 $p |- ( |^ ` ( 5 / 2 ) ) = 3 $=
    ( c5 c2 cdiv co cmin cmo caddc c3 cr wcel wceq 5re 2rp mp2an cmul c6 oveq1i
    c1 c4 eqtri cceil cfv crp ceildivmod df-6 3t2e6 2t2e4 4cn addsubassi ax-1cn
    2cn 5cn 4p2e6 mvrladdi 3eqtr2i cz 2re resubcli muladdmod mp3an clt wbr 1lt2
    2z 1mod 3eqtr3i oveq2i 3eqtr4ri 3cn 2ne0 divcan4i ) ABCDUAUBZABAEDZBFDZGDZB
    CDZHAIJBUCJZVLVPKLMABUDNVPHBODZBCDHVOVRBCPARGDZVRVOUEUFVNRAGBBODZVMGDZBFDZR
    BFDZVNRWARBFWASVMGDSBGDZAEDRVTSVMGUGQSBAUHUKULUIWDARULUJWDPVSUMUETUNUOQVMIJ
    VQBUPJWBVNKBAUQLURMVDVMBBUSUTBIJRBVAVBWCRKUQVCBVENVFVGVHQHBVIUKVJVKTT $.

  $( Subtraction and addition modulo a positive integer.  (Contributed by AV,
     7-Sep-2025.) $)
  submodaddmod $p |- ( ( N e. NN /\ ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) )
                      -> ( ( ( A + B ) mod N ) = ( ( A - C ) mod N )
                           <-> ( ( A + ( B + C ) ) mod N ) = ( A mod N ) ) ) $=
    ( wcel cz wa caddc co cmin cdvds wbr cmo wceq cc zcn adantl zaddcl moddvds
    wb cn 3ad2ant1 3ad2ant2 3ad2ant3 pnncand zcnd 3adant1 pncan2d eqtr4d breq2d
    w3a simpl 3adant3 zsubcl 3adant2 syl3anc simp1 simp2 zaddcld simpr1 3bitr4d
    simp3 ) DUAEZAFEZBFEZCFEZUKZGZDABHIZACJIZJIZKLZDABCHIZHIZAJIZKLZVIDMIVJDMIN
    ZVNDMIADMINZVHVKVODKVHVKVMVOVHABCVGAOEZVCVDVEVSVFAPUBQZVGBOEZVCVEVDWAVFBPUC
    QVGCOEZVCVFVDWBVECPUDQUEVHAVMVTVGVMOEZVCVEVFWCVDVEVFGVMBCRUFUGQUHUIUJVHVCVI
    FEZVJFEZVQVLTVCVGULZVGWDVCVDVEWDVFABRUMQVGWEVCVDVFWEVEACUNUOQVIVJDSUPVHVCVN
    FEZVDVRVPTWFVGWGVCVGAVMVDVEVFUQVGBCVDVEVFURVDVEVFVBUSUSQVCVDVEVFUTVNADSUPVA
    $.

  $( Two nonnegative integers are not equal modulo a positive modulus if their
     difference is greater than 0 and less than the modulus.  (Contributed by
     AV, 6-Sep-2025.) $)
  difltmodne $p |- ( ( N e. NN /\ ( A e. ZZ /\ B e. ZZ )
                               /\ ( 1 <_ ( A - B ) /\ ( A - B ) < N ) )
                     -> ( A mod N ) =/= ( B mod N ) ) $=
    ( cn wcel cz wa c1 cmin co cle wbr clt w3a cmo wceq cdvds cfz sylibr syl wn
    simp1 cfzo zsubcl simpl anim12i elnnz1 simp3r elfzo1 syl3anbrc nnz 3ad2ant1
    3adant1 fzoval eleqtrd fzm1ndvds syl2anc wb 3simpa 3anass moddvds mtbird
    neqned ) CDEZAFEZBFEZGZHABIJZKLZVHCMLZGZNZACOJZBCOJZVLVMVNPZCVHQLZVLVDVHHCH
    IJRJZEVPUAVDVGVKUBZVLVHHCUCJZVQVLVHDEZVDVJVHVSEVLVHFEZVIGZVTVGVKWBVDVGWAVKV
    IABUDVIVJUEUFUMVHUGSVRVDVGVIVJUHCVHUIUJVLCFEZVSVQPVDVGWCVKCUKULHCUNTUOCVHUP
    UQVLVDVEVFNZVOVPURVLVDVGGWDVDVGVKUSVDVEVFUTSABCVATVBVC $.

  $( A nonnegative integer is not itself plus a positive integer modulo an
     integer greater than 1 and the positive integer.  (Contributed by AV,
     6-Sep-2025.) $)
  zplusmodne $p |- ( ( N e. ( ZZ>= ` 2 ) /\ A e. ZZ /\ K e. ( 1 ..^ N ) )
                     -> ( ( A + K ) mod N ) =/= ( A mod N ) ) $=
    ( c2 cuz wcel cz c1 co w3a cn cle wbr clt wa cmo 3ad2ant3 zcnd wb adantl cc
    cfv cfzo caddc cmin wne eluz2nn 3ad2ant1 simp2 elfzoelz zaddcld wceq elfzo1
    pncan2d nnge1 anim1i 3adant2 sylbi breq2 breq1 anbi12d difltmodne syl121anc
    adantr mpbird mpdan ) CDEUBFZAGFZBHCUCIFZJZCKFZABUDIZGFVHHVLAUEIZLMZVMCNMZO
    ZVLCPIACPIUFVGVHVKVICUGUHVJABVGVHVIUIZVIVGBGFVHBHCUJZQUKVQVJVMBULZVPVJABVJA
    VQRVIVGBUAFVHVIBVRRQUNVJVSOZVPHBLMZBCNMZOZVJWCVSVIVGWCVHVIBKFZVKWBJWCCBUMWD
    WBWCVKWDWAWBBUOUPUQURQVDVTVNWAVOWBVSVNWASVJVMBHLUSTVSVOWBSVJVMBCNUTTVAVEVFV
    LACVBVC $.

  $( The sum of a nonnegative integer and a positive integer modulo a number
     greater than both integers is not equal to the nonnegative integer.
     (Contributed by AV, 27-Aug-2025.)  (Proof shortened by AV, 6-Sep-2025.) $)
  addmodne $p |- ( ( M e. NN /\ ( A e. NN0 /\ A < M ) /\ ( B e. NN /\ B < M ) )
                   -> ( ( A + B ) mod M ) =/= A ) $=
    ( cn wcel clt wbr wa w3a caddc co cmo c2 cz c1 cle adantr cr nnre ad2antrl
    cn0 cuz cfv cfzo wne a1i nnz 1red nnge1 simprr lelttrd 1zzd zltp1le syl2anr
    2z 1p1e2 breq1i bitrdi mpbid 3jca 3adant2 eluz2 sylibr nn0z 3ad2ant2 simprl
    wb simpl elfzo1 zplusmodne syl3anc crp cc0 wceq nnrp nn0re anim12ci 3adant3
    nn0ge0 anim1i modid syl2anc neeqtrd ) CDEZAUAEZACFGZHZBDEZBCFGZHZIZABJKCLKZ
    ACLKZAWKCMUBUCEZANEZBOCUDKEZWLWMUEWKMNEZCNEZMCPGZIZWNWDWJWTWGWDWJHZWQWRWSWQ
    XAUOUFWDWRWJCUGZQXAOCFGZWSXAOBCXAUHWHBREWDWIBSTWDCREWJCSQWHOBPGWDWIBUITWDWH
    WIUJZUKXAXCOOJKZCPGZWSWJONEWRXCXFVGWDWJULXBOCUMUNXEMCPUPUQURUSUTVAMCVBVCWGW
    DWOWJWEWOWFAVDQVEWKWHWDWIIZWPWDWJXGWGXAWHWDWIWDWHWIVFWDWJVHXDUTVACBVIVCABCV
    JVKWKAREZCVLEZHZVMAPGZWFHZWMAVNWDWGXJWJWDXIWGXHCVOWEXHWFAVPQVQVRWGWDXLWJWEX
    KWFAVSVTVEACWAWBWC $.

  $( A nonnegative integer is not itself plus a positive integer less than 5
     modulo 5.  (Contributed by AV, 6-Sep-2025.) $)
  plusmod5ne $p |- ( ( A e. ( 0 ..^ 5 ) /\ K e. ( 1 ..^ 5 ) )
                     -> ( ( A + K ) mod 5 ) =/= A ) $=
    ( c5 cn wcel cc0 cfzo co cn0 clt wbr wa caddc cmo wne 5nn w3a 3simpb sylbi
    c1 elfzo0 elfzo1 addmodne mp3an3an ) CDEZAFCGHEZAIEZACJKZLZBTCGHEZBDEZBCJKZ
    LZABMHCNHAOPUFUGUEUHQUIACUAUGUEUHRSUJUKUEULQUMCBUBUKUEULRSABCUCUD $.

  $( An integer is not itself plus 1 modulo an integer greater than 1.
     (Contributed by AV, 6-Sep-2025.) $)
  zp1modne $p |- ( ( N e. ( ZZ>= ` 2 ) /\ A e. ZZ )
                   -> ( ( A + 1 ) mod N ) =/= ( A mod N ) ) $=
    ( c2 cuz cfv wcel cz c1 cfzo co caddc cmo fzo1lb biranri zplusmodne mpd3an3
    wne ) BCDEFZAGFZHHBIJFZAHKJBLJABLJQTRSBMNAHBOP $.

  $( A nonnegative integer is not itself plus 1 modulo an integer greater than
     1 and the nonnegative integer.  (Contributed by AV, 6-Sep-2025.) $)
  p1modne $p |- ( ( N e. ( ZZ>= ` 2 ) /\ A e. ( 0 ..^ N ) )
                  -> ( ( A + 1 ) mod N ) =/= A ) $=
    ( c2 cuz cfv wcel cc0 cfzo co wa c1 caddc cmo cz wne elfzoelz zp1modne wceq
    sylan2 zmodidfzoimp adantl neeqtrd ) BCDEFZAGBHIFZJAKLIBMIZABMIZAUDUCANFUEU
    FOAGBPABQSUDUFARUCABTUAUB $.

  $( A nonnegative integer is not itself minus 1 modulo an integer greater than
     1 and the nonnegative integer.  (Contributed by AV, 6-Sep-2025.) $)
  m1modne $p |- ( ( N e. ( ZZ>= ` 2 ) /\ A e. ( 0 ..^ N ) )
                  -> ( ( A - 1 ) mod N ) =/= A ) $=
    ( c2 cuz wcel cc0 co wa c1 cmin cmo cz cle wbr clt adantr jca adantl wceq
    wb cfv cfzo cn eluz2nn elfzoelz 1zzd zsubcld cc zcnd 1cnd nncand 1le1 breq2
    mpbiri eluz2gt1 breq1 mpbird difltmodne syl3anc necomd zmodidfzoimp neeqtrd
    wne mpdan ) BCDUAEZAFBUBGEZHZAIJGZBKGZABKGZAVGVJVIVGBUCEZALEZVHLEZHZIAVHJGZ
    MNZVOBONZHZVJVIVCVEVKVFBUDPVFVNVEVFVLVMAFBUEZVFAIVSVFUFUGQRVGVOISZVRVGAIVFA
    UHEVEVFAVSUIRVGUJUKVGVTHZVPVQWAVPIIMNZULVTVPWBTVGVOIIMUMRUNWAVQIBONZVGWCVTV
    EWCVFBUOPPVTVQWCTVGVOIBOUPRUQQVDAVHBURUSUTVFVJASVEABVARVB $.

  $( A nonnegative integer is not itself minus a positive integer less than 5
     modulo 5.  (Contributed by AV, 7-Sep-2025.) $)
  minusmod5ne $p |- ( ( A e. ( 0 ..^ 5 ) /\ K e. ( 1 ..^ 5 ) )
                     -> ( ( A - K ) mod 5 ) =/= A ) $=
    ( cc0 c5 cfzo co wcel c1 wa cmin cmo cn cz cle wbr clt elfzoelz adantr wceq
    adantl wne 5nn a1i zsubcld cc zcnd nncan syl2an elfzo1 nnge1 anim1i 3adant2
    w3a sylbi breq2 breq1 anbi12d syl5ibrcom mpd difltmodne necomd zmodidfzoimp
    syl121anc neeqtrd ) ACDEFGZBHDEFGZIZABJFZDKFZADKFZAVGVJVIVGDLGZAMGZVHMGHAVH
    JFZNOZVMDPOZIZVJVIUAVKVGUBUCVEVLVFACDQZRZVGABVRVFBMGVEBHDQZTUDVGVMBSZVPVEAU
    EGBUEGVTVFVEAVQUFVFBVSUFABUGUHVGVPVTHBNOZBDPOZIZVFWCVEVFBLGZVKWBUMWCDBUIWDW
    BWCVKWDWAWBBUJUKULUNTVTVNWAVOWBVMBHNUOVMBDPUPUQURUSAVHDUTVCVAVEVJASVFADVBRV
    D $.

  $( The difference of an element of a half-open range of nonnegative integers
     and the upper bound of this range modulo an integer greater than the upper
     bound.  (Contributed by AV, 1-Sep-2025.) $)
  submodlt $p |- ( ( N e. NN /\ A e. ( 0 ..^ B ) /\ B < N )
                      -> ( ( A - B ) mod N ) = ( ( N + A ) - B ) ) $=
    ( cn wcel cc0 co clt wbr w3a cmin cmo cc wa wceq 3ad2ant2 zred 3ad2ant1 cle
    cr cfzo cneg elfzoel2 zcnd elfzoelz jca negsubdi2 syl eqcomd oveq1d zsubcld
    caddc crp nnrp negmod syl2anc eqtrd nnz nnre elfzo0suble simp3 leltletr imp
    cz syl32anc subge0d mpbird cn0 elfzo0 nn0re posdif syl2an biimp3a ltsubposd
    wb sylbi mpbid modid syl22anc nncn subsub3d 3eqtrd ) CDEZAFBUAGEZBCHIZJZABK
    GZCLGZCBAKGZKGZCLGZWJCAULGBKGWFWHWIUBZCLGZWKWFWGWLCLWFWLWGWFBMEZAMEZNZWLWGO
    WDWCWPWEWDWNWOWDBAFBUCZUDZWDAAFBUEZUDZUFPBAUGUHUIUJWFWITEZCUMEZWMWKOWDWCXAW
    EWDWIWDBAWQWSUKZQPZWCWDXBWECUNRZWICUOUPUQWFWJTEXBFWJSIZWJCHIZWKWJOWFWJWFCWI
    WCWDCVDEWECURRWDWCWIVDEWEXCPUKQXEWFXFWICSIZWFXABTEZCTEZWIBSIZWEXHXDWDWCXIWE
    WDBWQQPWCWDXJWECUSRZWDWCXKWEABUTPWCWDWEVAXAXIXJJXKWENXHWIBCVBVCVEWFCWIXLXDV
    FVGWFFWIHIZXGWDWCXMWEWDAVHEZBDEZABHIZJXMABVIXNXOXPXMXNATEXIXPXMVOXOAVJBUSAB
    VKVLVMVPPWFWICXDXLVNVQWJCVRVSWFCBAWCWDCMEWECVTRWDWCWNWEWRPWDWCWOWEWTPWAWB
    $.

  $( An integer minus ` B ` is not itself plus ` C ` modulo an integer greater
     than the sum of ` B ` and ` C ` .  (Contributed by AV, 6-Sep-2025.) $)
  submodneaddmod $p |- ( ( N e. NN /\ ( A e. ZZ /\ B e. ZZ /\ C e. ZZ )
                           /\ ( 1 <_ ( B + C ) /\ ( B + C ) < N ) )
                         -> ( ( A + B ) mod N ) =/= ( ( A - C ) mod N ) ) $=
    ( wcel cz w3a c1 caddc co cle wbr clt wa cmin cmo jca 3ad2ant2 cc zcn simp1
    cn wne zaddcl 3adant3 zsubcl 3adant2 wceq 3ad2ant1 3ad2ant3 pnncand simpl3l
    wb breq2 adantl mpbird simpl3r breq1 mpdan difltmodne syl3anc ) DUBEZAFEZBF
    EZCFEZGZHBCIJZKLZVGDMLZNZGZVBABIJZFEZACOJZFEZNZHVLVNOJZKLZVQDMLZNZVLDPJVNDP
    JUCVBVFVJUAVFVBVPVJVFVMVOVCVDVMVEABUDUEVCVEVOVDACUFUGQRVKVQVGUHZVTVKABCVFVB
    ASEZVJVCVDWBVEATUIRVFVBBSEZVJVDVCWCVEBTRRVFVBCSEZVJVEVCWDVDCTUJRUKVKWANZVRV
    SWEVRVHVHVIVBVFWAULWAVRVHUMVKVQVGHKUNUOUPWEVSVIVHVIVBVFWAUQWAVSVIUMVKVQVGDM
    URUOUPQUSVLVNDUTVA $.

  $( A nonnegative integer minus 1 is not itself plus 2 modulo an integer
     greater than 3 and the nonnegative integer.  (Contributed by AV,
     6-Sep-2025.) $)
  m1modnep2mod $p |- ( ( N e. ( ZZ>= ` 4 ) /\ A e. ZZ )
                       -> ( ( A - 1 ) mod N ) =/= ( ( A + 2 ) mod N ) ) $=
    ( c4 cuz cfv wcel cz wa c2 caddc co cmo c1 cle wbr clt adantr a1i c3 2p1e3
    cmin cn wne eluz4nn simpr 2z 1zzd 1le3 breqtrri w3a eluz2 df-4 breq1i wb 3z
    zltp1le sylan biimprd biimtrid 3impia sylbi submodneaddmod syl132anc necomd
    eqbrtrid ) BCDEFZAGFZHZAIJKBLKZAMUAKBLKZVHBUBFZVGIGFZMGFMIMJKZNOZVMBPOZVIVJ
    UCVFVKVGBUDQVFVGUEVLVHUFRVHUGVNVHMSVMNUHTUIRVFVOVGVFVMSBPTVFCGFZBGFZCBNOZUJ
    SBPOZCBUKVPVQVRVSVRSMJKZBNOZVPVQHZVSCVTBNULUMWBVSWAVPSGFZVQVSWAUNWCVPUORSBU
    PUQURUSUTVAVEQAIMBVBVCVD $.

  $( A nonnegative integer minus a positive integer 1 or 2 is not itself plus 2
     times the positive integer modulo 5.  (Contributed by AV, 8-Sep-2025.) $)
  minusmodnep2tmod $p |- ( ( A e. ZZ /\ B e. ( 1 ..^ 3 ) )
                   -> ( ( A - B ) mod 5 ) =/= ( ( A + ( 2 x. B ) ) mod 5 ) ) $=
    ( cz wcel c1 c3 co c5 cmo c2 cmul caddc wceq cdvds wbr eqtrdi c6 adantl a1i
    wb cfzo wa cmin wn wo elpri 5ndvds3 oveq2 3t1e3 breq2d mtbiri 5ndvds6 3t2e6
    cpr jaoi syl fzo13pr eleq2s cn simpl elfzoelz zmulcld submodaddmod syl13anc
    2z 2cnd zcnd adddirp1d eqcomd 2p1e3 oveq1i oveq2d oveq1d eqeq1d bitrd eqcom
    5nn 3z addmulmodb 3bitr4d mtbird neqned ) ACDZBEFUAGZDZUBZABUCGHIGZAJBKGZLG
    HIGZWFWGWIMZHFBKGZNOZWEWLUDZWCWMBEJUNZWDBWNDBEMZBJMZUEWMBEJUFWOWMWPWOWLHFNO
    UGWOWKFHNWOWKFEKGFBEFKUHUIPUJUKWPWLHQNOULWPWKQHNWPWKFJKGQBJFKUHUMPUJUKUOUPU
    QURRWFWIWGMZAWKLGZHIGZAHIGZMZWJWLWFWQAWHBLGZLGZHIGZWTMZXAWFHUSDZWCWHCDBCDZW
    QXETXFWFVQSZWCWEUTZWFJBJCDWFVESWEXGWCBEFVAZRZVBXKAWHBHVCVDWFXDWSWTWFXCWRHIW
    FXBWKALWFXBJELGZBKGZWKWEXBXMMWCWEXMXBWEJBWEVFWEBXJVGVHVIRXLFBKVJVKPVLVMVNVO
    WJWQTWFWGWIVPSWFXFWCFCDZXGWLXATXHXIXNWFVRSXKAFBHVSVDVTWAWB $.

  $( An integer decreased by 1 is 0 modulo a positive integer iff the integer
     is 1 modulo the same modulus.  (Contributed by AV, 6-Jun-2020.) $)
  m1mod0mod1 $p |- ( ( A e. RR /\ N e. RR /\ 1 < N )
                     -> ( ( ( A - 1 ) mod N ) = 0 <-> ( A mod N ) = 1 ) ) $=
    ( cr wcel c1 clt wbr w3a cmin co cmo cc0 wceq wa caddc eqcomd adantr oveq1d
    syl 3adant1 cc recn npcan1 3ad2ant1 simpr 1mod oveq12d peano2rem 1red simpl
    crp 0lt1 0re 1re lttr mp3an12 mpani imp elrpd modaddabs 0p1e1 oveq1i eqtrid
    wi 3eqtr3d eqtrd oveq2d simp1 modcld recnd subidd modsubmod syl3anc impbida
    3jca 0mod ) ACDZBCDZEBFGZHZAEIJZBKJZLMZABKJZEMZVTWCNZWDWAEOJZBKJZEWFAWGBKVT
    AWGMZWCVQVRWIVSVQAUADZWIAUBWJWGAAUCPSUDQRWFWBEBKJZOJZBKJZLEOJZBKJZWHEWFWLWN
    BKWFWBLWKEOVTWCUEVTWKEMZWCVRVSWPVQBUFZTQUGRWFWACDZECDZBUKDZHZWMWHMVTXAWCVTW
    RWSWTVQVRWRVSAUHUDVTUIVRVSWTVQVRVSNZBVRVSUJVRVSLBFGZVRLEFGZVSXCULLCDWSVRXDV
    SNXCVDUMUNLEBUOUPUQURUSTZVOQWAEBUTSVTWOEMZWCVRVSXFVQXBWOWKEWNEBKVAVBWQVCTQV
    EVFVTWENZWBAWDIJZBKJZLXGWAXHBKXGEWDAIXGWDEVTWEUEPVGRVTXILMWEVTWDWDIJZBKJZLB
    KJZXILVTXJLBKVTWDVTWDVTABVQVRVSVHZXEVIZVJVKRVTVQWDCDWTXKXIMXMXNXEAWDBVLVMVT
    WTXLLMXEBVPSVEQVFVN $.

  $( An integer modulo 2 is either 0 or 1.  (Contributed by AV, 24-May-2020.)
     (Proof shortened by OpenAI, 3-Jul-2020.) $)
  elmod2 $p |- ( N e. ZZ -> ( N mod 2 ) e. { 0 , 1 } ) $=
    ( cz wcel c2 cmo co cc0 cfzo cpr 2nn zmodfzo ancoms mpan fzo0to2pr eleqtrdi
    c1 cn ) ABCZADEFZGDHFZGPIDQCZRSTCZJRUAUBADKLMNO $.

  ${
    $d A x $.  $d N x $.
    $( If an integer is 0 modulo a positive integer, this integer must be a
       multiple of the modulus.  (Contributed by AV, 7-Jun-2020.) $)
    mod0mul $p |- ( ( A e. ZZ /\ N e. NN )
                    -> ( ( A mod N ) = 0 -> E. x e. ZZ A = ( x x. N ) ) ) $=
      ( cz wcel cn wa cmo co cc0 wceq cdiv cv cmul wrex cr wb adantl cc adantr
      crp zre nnrp mod0 syl2an simpr oveq1 eqeq2d zcn wne nnne0 divcan1d eqcomd
      nncn rspcedvd ex sylbid ) BDEZCFEZGZBCHIJKZBCLIZDEZBAMZCNIZKZADOZURBPECUA
      EVAVCQUSBUBCUCBCUDUEUTVCVGUTVCGZVFBVBCNIZKZAVBDUTVCUFVDVBKZVFVJQVHVKVEVIB
      VDVBCNUGUHRVHVIBUTVIBKVCUTBCURBSEUSBUITUSCSEURCUNRUSCJUJURCUKRULTUMUOUPUQ
      $.
  $}

  ${
    $d A x y $.  $d N x y $.
    $( If an integer is not 0 modulo a positive integer, this integer must be
       the sum of a multiple of the modulus and a positive integer less than
       the modulus.  (Contributed by AV, 7-Jun-2020.) $)
    modn0mul $p |- ( ( A e. ZZ /\ N e. NN ) -> ( ( A mod N ) =/= 0
                -> E. x e. ZZ E. y e. ( 1 ..^ N ) A = ( ( x x. N ) + y ) ) ) $=
      ( cz wcel wa co cc0 wne cv cmul caddc wceq cfzo wrex adantr adantl eqeq2d
      cr cn cmo c1 cdiv cfl cfv zre nnre nnne0 redivcld flcld anim1i fzo1fzo0n0
      zmodfzo sylibr crp anim12i flpmodeq syl eqcomd oveq1 oveq1d oveq2 rspc2ev
      nnrp syl3anc ex ) CEFZDUAFZGZCDUBHZIJZCAKZDLHZBKZMHZNZBUCDOHZPAEPZVJVLGZC
      DUDHZUEUFZEFZVKVRFZCWBDLHZVKMHZNZVSVJWCVLVJWAVJCDVHCTFZVICUGZQVIDTFVHDUHR
      VIDIJVHDUIRUJUKQVTVKIDOHFZVLGWDVJWJVLCDUNULVKDUMUOVTWFCVTWHDUPFZGZWFCNVJW
      LVLVHWHVIWKWIDVEUQQCDURUSUTVQWGCWEVOMHZNABWBVKEVRVMWBNZVPWMCWNVNWEVOMVMWB
      DLVAVBSVOVKNWMWFCVOVKWEMVCSVDVFVG $.

    $( An integer decreased by 1 modulo a positive integer minus the integer
       modulo the same modulus is either -1 or the modulus minus 1.
       (Contributed by AV, 7-Jun-2020.) $)
    m1modmmod $p |- ( ( A e. ZZ /\ N e. NN )
                     -> ( ( ( A - 1 ) mod N ) - ( A mod N ) )
                        = if ( ( A mod N ) = 0 , ( N - 1 ) , -u 1 ) ) $=
      ( vx cz wcel wa cmo co cc0 wceq c1 adantl cr adantr oveq1d caddc cc eqtrd
      cmin wbr vy cn cneg cif oveq2 peano2zm zred crp nnrp modcld recnd subid1d
      cv cmul wrex mod0mul imp wi oveq1 zcn nncn mulcl npcand eqcomd mulsubfacd
      syl2anr zcnd 1cnd addsubassd peano2rem syl addcomd modcyc syl3anc cle clt
      nnre jca nnm1ge0 ltm1d modid syl12anc 3eqtrd sylan9eqr rexlimdva2 3eqtrrd
      mpd wn df-ne cfzo modn0mul oveq12d elfzoelz simprl anim12ci elfzole1 0lt1
      wne 0red 1red ltleletr mpani elfzolt2 cuz cfv w3a elfzo2 eluz2 zre subge0
      biimp3ar sylbi 3ad2ant1 eluzelz ltle syl2an 3impia anim1i 3adant3 zlem1lt
      wb mpbid impcom sub32d subidd df-neg eqtr4di ex rexlimdvva syld biimtrrid
      a1d ifeqda ) ADEZBUBEZFZABGHZIJZBKSHZKUCZUDAKSHZBGHZYQSHZYPYRYSYTUUCYPYRF
      ZUUCUUBISHZUUBYSYRUUCUUEJYPYQIUUBSUELYPUUEUUBJYRYPUUBYPUUBYPUUABYNUUAMEYO
      YNUUAAUFUGNYOBUHEZYNBUIZLZUJUKULNUUDACUMZBUNHZJZCDUOZUUBYSJZYPYRUULCABUPU
      QYPUULUUMURYRYPUUKUUMCDUUKYPUUIDEZFZUUBUUJKSHZBGHZYSUUKUUAUUPBGAUUJKSUSOU
      UOUUQUUIKSHZBUNHZYSPHZBGHYSUUSPHZBGHZYSUUOUUPUUTBGUUOUUPUUSBPHZKSHUUTUUOU
      UJUVCKSUUOUUJUUJBSHZBPHZUVCUUOUVEUUJUUOUUJBUUNUUIQEZBQEZUUJQEZYPUUIUTZYOU
      VGYNBVALZUUIBVBZVFYPUVGUUNUVJNZVCVDUUOUVDUUSBPUUOUUIBUUNUVFYPUVILUVLVEORO
      UUOUUSBKUUNUURQEUVGUUSQEYPUUNUURUUIUFZVGUVJUURBVBVFZUVLUUOVHVIROUUOUUTUVA
      BGUUOUUSYSUVNYPYSQEZUUNYOUVOYNYOYSYOBMEZYSMEZBVQZBVJVKZUKLNVLOUUOUVBYSBGH
      ZYSUUOUVQUUFUURDEZUVBUVTJYPUVQUUNYOUVQYNUVSLNYPUUFUUNUUHNUUNUWAYPUVMLYSBU
      URVMVNUUOUVQUUFFZIYSVOTZYSBVPTZUVTYSJYPUWBUUNYOUWBYNYOUVQUUFUVSUUGVRLNYPU
      WCUUNYOUWCYNBVSLNYPUWDUUNYOUWDYNYOBUVRVTLNYSBWAWBRWCWDWENWGWFYPYRWHZYTUUC
      JZUWEYQIWRZYPUWFYQIWIYPUWGAUUJUAUMZPHZJZUAKBWJHZUOCDUOUWFCUAABWKYPUWJUWFC
      UADUWKYPUUNUWHUWKEZFZFZUWJUWFUWNUWJFZUUCYTUWOUUCUWHKSHZBGHZUWHSHZYTUWJUWN
      UUCUWIKSHZBGHZUWIBGHZSHUWRUWJUUBUWTYQUXASUWJUUAUWSBGAUWIKSUSOAUWIBGUSWLUW
      NUWTUWQUXAUWHSUWNUWTUWPUUJPHZBGHZUWQUWNUWSUXBBGUWNUWSUUJUWPPHUXBUWNUUJUWH
      KUWMUVFUVGUVHYPUUNUVFUWLUVINUVJUVKVFZUWMUWHQEZYPUWLUXEUUNUWLUWHUWHKBWMZVG
      ZLLZUWNVHVIUWNUUJUWPUXDUWMUWPQEZYPUWLUXIUUNUWLUWPUWLUWHDEZUWPDEUXFUWHUFVK
      ZVGLLVLROUWNUWPMEZUUFUUNUXCUWQJUWMUXLYPUWLUXLUUNUWLUWPUXKUGLZLYPUUFUWMUUH
      NZYPUUNUWLWNZUWPBUUIVMVNRUWNUXAUWHUUJPHZBGHZUWHBGHZUWHUWNUWIUXPBGUWNUUJUW
      HUXDUXHVLOUWNUWHMEZUUFUUNUXQUXRJUWMUXSYPUWLUXSUUNUWLUWHUXFUGZLZLUXNUXOUWH
      BUUIVMVNUWNUXSUUFFZIUWHVOTZUWHBVPTZFZFUXRUWHJUWNUYBUYEYPUUFUWMUXSUUHUYAWO
      UWMUYEYPUWLUYEUUNUWLUYCUYDUWLKUWHVOTZUYCUWHKBWPUWLIKVPTZUYFUYCWQUWLIMEKME
      ZUXSUYGUYFFUYCURUWLWSUWLWTUXTIKUWHXAVNXBWGUWHKBXCVRLLVRUWHBWAVKWCWLWDUWNU
      WRYTJUWJUWNUWRUWPUWHSHZYTUWNUWQUWPUWHSUWNUXLUUFFIUWPVOTZUWPBVPTZUWQUWPJYP
      UUFUWMUXLUUHUXMWOUWMUYJYPUWLUYJUUNUWLUWHKXDXEEZBDEZUYDXFZUYJUWHKBXGZUYLUY
      MUYJUYDUYLKDEZUXJUYFXFUYJKUWHXHUYPUXJUYJUYFUXJUXSUYHUYJUYFYAUYPUWHXIKXIUW
      HKXJVFXKXLXMXLLLUWMYPUYKUWLYPUYKURZUUNUWLUYNUYQUYOUYNUYKYPUYNUWHBVOTZUYKU
      YLUYMUYDUYRUYLUXSUVPUYDUYRURUYMUYLUWHKUWHXNZUGBXIUWHBXOXPXQUYNUXJUYMFZUYR
      UYKYAUYLUYMUYTUYDUYLUXJUYMUYSXRXSUWHBXTVKYBYLXLLYCUWPBWAWBOUWNUYIIKSHZYTU
      WMUYIVUAJZYPUWLVUBUUNUWLUYIUWHUWHSHZKSHVUAUWLUWHKUWHUXGUWLVHUXGYDUWLVUCIK
      SUWLUWHUXGYEORLLKYFYGRNRVDYHYIYJYKUQYMVD $.
  $}

  $( The difference between an integer modulo a positive integer and the
     integer decreased by 1 modulo the same modulus is less than the modulus
     decreased by 1 (if the modulus is greater than 2).  This theorem would not
     be valid for an odd ` A ` and ` N = 2 ` , since
     ` ( ( A mod N ) - ( ( A - 1 ) mod N ) ) ` would be ` ( 1 - 0 ) = 1 ` which
     is not less than ` ( N - 1 ) = 1 ` .  (Contributed by AV, 6-Jun-2012.)
     (Proof shortened by SN, 27-Nov-2025.) $)
  difmodm1lt $p |- ( ( A e. ZZ /\ N e. NN /\ 2 < N )
                     -> ( ( A mod N ) - ( ( A - 1 ) mod N ) ) < ( N - 1 ) ) $=
    ( cz wcel c2 clt wbr cmo cmin wceq cneg 3ad2ant1 crp 3ad2ant2 modcld negeqd
    co c1 cr eqbrtrd cn w3a cc0 cif peano2zm zred nnrp zre negsubdi2d m1modmmod
    recnd 3adant3 eqtr3d wa iftrue adantr 1red 2re a1i nnre 1lt2 simp3 lttrd wb
    difrp syl2anc mpbid neglt syl adantl wn iffalse negneg1e1 caddc df-2 breq1i
    biimpi 3ad2ant3 ltaddsub2d eqbrtrid pm2.61ian ) ACDZBUADZEBFGZUBZABHQZARIQZ
    BHQZIQZWFUCJZBRIQZRKZUDZKZWKFWEWHWFIQZKWIWNWEWHWFWEWHWEWGBWEWGWBWCWGCDWDAUE
    LUFWCWBBMDWDBUGNZOUKWEWFWEABWBWCASDWDAUHLWPOUKUIWEWOWMWBWCWOWMJWDABUJULPUMW
    JWEWNWKFGWJWEUNZWNWKKZWKFWQWMWKWJWMWKJWEWJWKWLUOUPPWEWRWKFGZWJWEWKMDZWSWERB
    FGZWTWEREBWEUQZESDWEURUSWCWBBSDZWDBUTNZREFGWEVAUSWBWCWDVBVCWERSDXCXAWTVDXBX
    DRBVEVFVGWKVHVIVJTWJVKZWEUNZWNWLKZWKFXFWMWLXEWMWLJWEWJWKWLVLUPPWEXGWKFGXEWE
    XGRWKFVMWERRVNQZBFGZRWKFGWDWBXIWCWDXIEXHBFVOVPVQVRWERRBXBXBXDVSVGVTVJTWAT
    $.

  $( 8 modulo 5 is 3.  (Contributed by AV, 20-Nov-2025.) $)
  8mod5e3 $p |- ( 8 mod 5 ) = 3 $=
    ( c8 c5 cmo co c3 caddc 5p3e8 eqcomi oveq1i cn0 wcel clt wbr wceq 3nn0 3lt5
    cn 5nn addmodid mp3an eqtri ) ABCDBEFDZBCDZEAUBBCUBAGHIEJKBQKEBLMUCENORPEBS
    TUA $.

  ${
    $( If an integer minus a constant equals another integer plus the constant
       modulo ` N ` , then the first integer plus the constant equals the
       second integer minus the constant modulo ` N ` iff the fourfold of the
       constant is a multiple of ` N ` .  (Contributed by AV, 15-Nov-2025.) $)
    modmkpkne $p |- ( ( N e. NN /\ ( X e. ZZ /\ Y e. ZZ /\ K e. ZZ ) )
                      -> ( ( ( Y - K ) mod N ) = ( ( X + K ) mod N )
                        -> ( ( ( Y + K ) mod N ) = ( ( X - K ) mod N )
                             <-> ( ( 4 x. K ) mod N ) = 0 ) ) ) $=
      ( wcel cz cmin co cmo caddc wceq c4 cmul wb zsubcl syl2an23an c2 3ad2ant3
      cc0 adantl cn w3a wa 3adant1 zaddcl 3adant2 simpl difmod0 cc zcn 3ad2ant2
      3ad2ant1 subsubadd23 2timesd eqcomd oveq2d eqtrd oveq1d eqeq1d 3adant3 2z
      ancoms a1i zmulcld bitrd cneg addsubsub23 summodnegmod adantr eqeq1 2t2e4
      id eqcomi oveq1i 2cnd mulassd zcnd eqtrid bitr2d sylan9bbr 3bitr3d sylbid
      ex sylbird ) BUAEZCFEZDFEZAFEZUBZUCZDAGHZBIHCAJHZBIHKZWKWLGHZBIHZSKZDAJHZ
      BIHCAGHZBIHKZLAMHZBIHZSKZNZWIWKFEZWLFEZWEWEWPWMNWGWHXDWFDAOUDWFWHXEWGCAUE
      UFWEWIUGZWKWLBUHPWJWPDCGHZBIHZQAMHZBIHZKZXCWJWPXGXIGHZBIHZSKZXKWJWOXMSWJW
      NXLBIWIWNXLKWEWIWNXGAAJHZGHXLWIDACAWGWFDUIEZWHDUJUKZWHWFAUIEZWGAUJZRZWFWG
      CUIEZWHCUJULZXTUMWIXOXIXGGWHWFXOXIKZWGWHXIXOWHAXSUNUORZUPUQTURUSWIXGFEZXI
      FEZWEWEXNXKNWFWGYEWHWGWFYEDCOVBUTZWHWFYFWGWHQAQFEWHVAVCWHVLVDZRZXFXGXIBUH
      PVEWJXKXCWJXKUCWQWRGHZBIHZSKZXHXIVFBIHZKZWSXBWJYLYNNXKWJYLXGXIJHZBIHZSKZY
      NWJYKYPSWJYJYOBIWJYJXGXOJHYOWJDACAWIXPWEXQTWIXRWEXTTZWIYAWEYBTYRVGWJXOXIX
      GJWIYCWEYDTUPUQURUSWIYEYFWEWEYQYNNYGYIXFXGXIBVHPVEVIWJYLWSNZXKWIWQFEZWRFE
      ZWEWEYSWGWHYTWFDAUEUDWFWHUUAWGCAOUFXFWQWRBUHPVIXKYNXJYMKZWJXBXHXJYMVJWJXB
      XIXIJHZBIHZSKZUUBWJXAUUDSWJWTUUCBIWIWTUUCKZWEWHWFUUFWGWHWTQQMHZAMHZUUCLUU
      GAMUUGLVKVMVNWHUUHQXIMHUUCWHQQAWHVOZUUIXSVPWHXIWHXIYHVQUNUQVRRTURUSWIYFYF
      WEWEUUEUUBNYIYIXFXIXIBVHPVSVTWAWCWBWD $.
  $}

  ${
    modmknepk.j $e |- J = ( 1 ..^ ( |^ ` ( N / 2 ) ) ) $.
    modmknepk.i $e |- I = ( 0 ..^ N ) $.
    $( A nonnegative integer less than the modulus plus/minus a positive
       integer less than (the ceiling of) half of the modulus are not equal
       modulo the modulus.  For this theorem, it is essential that
       ` K < ( N / 2 ) ` !  (Contributed by AV, 3-Sep-2025.)  (Revised by AV,
       15-Nov-2025.) $)
    modmknepk $p |- ( ( N e. ( ZZ>= ` 3 ) /\ Y e. I /\ K e. J )
                      -> ( ( Y - K ) mod N ) =/= ( ( Y + K ) mod N ) ) $=
      ( cfv wcel w3a cn cz c1 co cle wbr clt wa eleq2s c2 c3 cuz caddc cmin cmo
      wne eluz3nn 3ad2ant1 cfzo elfzoelz 3ad2ant2 cdiv cceil 3ad2ant3 cmul wceq
      cc0 zcnd 2timesd eqcomd adantl 1red zred a1i zmulcld elfzole1 cn0 simp1bi
      elfzo1 nnnn0d nn0le2x syl letrd eleq2i 2tceilhalfelfzo1 sylan2b jca breq2
      2z breq1 anbi12d syl5ibrcom mpd 3adant2 submodneaddmod necomd syl131anc )
      DUAUBHIZEAIZCBIZJDKIZELIZCLIZWMMCCUCNZOPZWNDQPZRZECUDNDUENZECUCNDUENZUFWH
      WIWKWJDUGUHWIWHWLWJWLEUQDUINAEUQDUJGSUKWJWHWMWIWMCMDTULNUMHZUINZBCMWTUJFS
      ZUNZXCWHWJWQWIWHWJRZWNTCUONZUPZWQWJXFWHWJXEWNWJCWJCXBURUSUTVAXDWQXFMXEOPZ
      XEDQPZRXDXGXHWJXGWHWJMCXEWJVBWJCXBVCWJXEWJTCTLIWJVSVDXBVEVCMCOPCXABCMWTVF
      FSWJCVGICXEOPWJCCKIZCXABCXAIZXIWTKICWTQPWTCVIVHFSVJCVKVLVMVAWJWHXJXHBXACF
      VNCDVOVPVQXFWOXGWPXHWNXEMOVRWNXEDQVTWAWBWCWDWKWLWMWMJWQJWSWRECCDWEWFWG $.
  $}

  ${
    $d N z $.  $d X z $.
    $( An integer with an absolute value less than a positive integer is 0
       modulo the positive integer iff it is 0.  (Contributed by AV,
       21-Nov-2025.) $)
    modlt0b $p |- ( ( N e. NN /\ X e. ZZ /\ ( abs ` X ) < N )
                    -> ( ( X mod N ) = 0 <-> X = 0 ) ) $=
      ( vz wcel cz cabs cfv clt wbr cmo co cc0 wceq cmul wa wi adantl adantr c1
      sylbid cn w3a wrex pm3.22 3adant3 mod0mul syl simpr fveq2 breq1d zcn nncn
      cv cc absmul syl2anr nnre nnnn0 nn0ge0d absidd oveq2d eqtrd cdiv cr nngt0
      abscld jca ltmuldiv syl3anc nnne0 dividd breq2d bitrd zabs0b oveq1 mul02d
      wb sylan9eqr expl com23 3impia impl rexlimdva syld crp nnrp 0mod 3ad2ant1
      ex impbid ) AUADZBEDZBFGZAHIZUBZBAJKZLMZBLMZWOWQBCUMZANKZMZCEUCZWRWOWLWKO
      ZWQXBPWKWLXCWNWKWLUDUECBAUFUGWOXAWRCEWOWSEDZOZXAWRXEXAOBWTLXEXAUHWOXDXAWT
      LMZWKWLWNXDXAOZXFPWKWLOXGWNXFWKXGWNXFPZPWLWKXDXAXHWKXDOZXAOZWNWTFGZAHIZXF
      XJWMXKAHXAWMXKMXIBWTFUIQUJXIXLXFPXAXIXLWSFGZANKZAHIZXFXIXKXNAHXIXKXMAFGZN
      KZXNXDWSUNDAUNDXKXQMWKWSUKZAULZWSAUOUPXIXPAXMNWKXPAMXDWKAAUQZWKAAURUSUTRV
      AVBUJXIXOXMSHIZXFXIXOXMAAVCKZHIZYAXIXMVDDZAVDDZYELAHIZOZXOYCVQXDYDWKXDWSX
      RVFQWKYEXDXTRWKYGXDWKYEYFXTAVEVGRXMAAVHVIXIYBSXMHWKYBSMXDWKAXSAVJVKRVLVMX
      IYAWSLMZXFXDYAYHVQWKWSVNQWKYHXFPXDWKYHXFYHWKWTLANKLWSLANVOWKAXSVPVRWIRTTT
      RTVSRVTWAWBVBWIWCWDWOWRWQWRWOWPLAJKZLBLAJVOWKWLYILMZWNWKAWEDYJAWFAWGUGWHV
      RWIWJ $.
  $}

  ${
    mod2addne.i $e |- I = ( 0 ..^ N ) $.
    $( The sums of a nonnegative integer less than the modulus and two integers
       whose difference is less than the modulus are not equal modulo the
       modulus.  (Contributed by AV, 15-Nov-2025.) $)
    mod2addne $p |- ( ( N e. NN /\ ( X e. I /\ A e. ZZ /\ B e. ZZ )
                        /\ ( abs ` ( A - B ) ) e. ( 1 ..^ N ) )
                      -> ( ( X + A ) mod N ) =/= ( ( X + B ) mod N ) ) $=
      ( wcel cz w3a co cabs caddc cmo wceq cc0 wb wi wa adantl 3ad2ant1 cn cmin
      cfv c1 cfzo wne wn clt wbr simp1 zsubcl 3adant1 3ad2ant2 elfzolt2 modlt0b
      3ad2ant3 syl3anc fveq2 eleq1d abs0 eleq1i a1i elfzo1 pm2.21i sylbi sylbid
      0nnn adantr ex com23 3impia pm2.01d simp2 simp3 simpl 3adant3 difmod0 syl
      3jca mtbid elfzoelz eleq2s zcnd addcomd oveq1d eqeq12d cr crp zre anim12i
      nnrp zred anim12ci jca modaddb bitr4d necon3abid mpbird ) DUAGZECGZAHGZBH
      GZIZABUBJZKUCZUDDUEJZGZIZEALJZDMJZEBLJZDMJZUFADMJBDMJNZUGXHXDDMJONZXMXHXN
      XHXNXDONZXNUGZXHWSXDHGZXEDUHUIZXNXOPWSXCXGUJXCWSXQXGXAXBXQWTABUKULUMXGWSX
      RXCXEUDDUNUPDXDUOUQWSXCXGXOXPQWSXCRZXOXGXPXSXOXGXPQXSXORXGOKUCZXFGZXPXOXG
      YAPXSXOXEXTXFXDOKURUSSXSYAXPQXOXSYAOXFGZXPYAYBPXSXTOXFUTVAVBYBXPQXSYBOUAG
      ZWSODUHUIZIXPDOVCYCWSXPYDYCXPVGVDTVEVBVFVHVFVIVJVKVFVLXHXAXBWSIZXNXMPWSXC
      YEXGXSXAXBWSXCXAWSWTXAXBVMZSXCXBWSWTXAXBVNZSWSXCVOVSVPABDVQVRVTXHXMXJXLXH
      XJXLNZAELJZDMJZBELJZDMJZNZXMXCWSYHYMPXGXCXJYJXLYLXCXIYIDMXCEAXCEWTXAEHGZX
      BYNEODUEJCEODWAFWBZTWCZXCAYFWCWDWEXCXKYKDMXCEBYPXCBYGWCWDWEWFUMXHAWGGZBWG
      GZRZEWGGZDWHGZRZRZXMYMPWSXCUUCXGXSYSUUBXCYSWSXAXBYSWTXAYQXBYRAWIBWIWJULSW
      SUUAXCYTDWKWTXAYTXBWTEYOWLTWMWNVPABEDWOVRWPWQWR $.
  $}

  ${
    modm1nep1.i $e |- I = ( 0 ..^ N ) $.
    $( A nonnegative integer less than a modulus greater than 2 plus/minus one
       are not equal modulo the modulus.  (Contributed by AV, 15-Nov-2025.) $)
    modm1nep1 $p |- ( ( N e. ( ZZ>= ` 3 ) /\ Y e. I )
                      -> ( ( Y - 1 ) mod N ) =/= ( ( Y + 1 ) mod N ) ) $=
      ( c3 cuz cfv wcel c1 c2 cdiv co cceil cfzo cmo caddc wne 1elfzo1ceilhalf1
      cmin adantr eqid modmknepk mpd3an3 ) BEFGHZCAHZIIBJKLMGNLZHZCISLBOLCIPLBO
      LQUDUGUEBRTAUFIBCUFUADUBUC $.

    $( A nonnegative integer less than a modulus greater than 4 plus one/minus
       two are not equal modulo the modulus.  (Contributed by AV,
       22-Nov-2025.) $)
    modm2nep1 $p |- ( ( N e. ( ZZ>= ` 5 ) /\ Y e. I )
                      -> ( ( Y - 2 ) mod N ) =/= ( ( Y + 1 ) mod N ) ) $=
      ( c5 cfv wcel wa c2 co cmo caddc c1 cz cabs adantr a1i c3 wbr cr cuz cmin
      cneg wceq cc0 cfzo elfzoelz eleq2s zcnd 2cnd negsubd adantl eqcomd oveq1d
      cn wne eluz5nn simpr 1zzd 2z znegcld ax-1cn 2cn subnegi 1p2e3 fveq2i 3nn0
      eqtri nn0absidi clt 3nn cle w3a eluz2 3re 5re 3lt5 ltletrd 3adant1 elfzo1
      zre sylbi syl3anbrc eqeltrid mod2addne syl131anc necomd eqnetrd ) BEUAFGZ
      CAGZHZCIUBJZBKJCIUCZLJZBKJZCMLJBKJZWKWLWNBKWKWNWLWJWNWLUDWIWJCIWJCCNGCUEB
      UFJACUEBUGDUHUIWJUJUKULUMUNWKWPWOWKBUOGZWJMNGWMNGMWMUBJZOFZMBUFJZGWPWOUPW
      IWQWJBUQZPWIWJURWKUSWKIINGWKUTQVAWKWSRWTWSROFRWRROWRMILJRMIVBVCVDVEVHVFRV
      GVIVHWIRWTGZWJWIRUOGZWQRBVJSZXBXCWIVKQXAWIENGZBNGZEBVLSZVMXDEBVNXFXGXDXEX
      FXGHZREBRTGXHVOQETGXHVPQXFBTGXGBWAPREVJSXHVQQXFXGURVRVSWBBRVTWCPWDMWMABCD
      WEWFWGWH $.

    $( A nonnegative integer less than a modulus greater than 4 plus one/plus
       two are not equal modulo the modulus.  (Contributed by AV,
       22-Nov-2025.) $)
    modp2nep1 $p |- ( ( N e. ( ZZ>= ` 5 ) /\ Y e. I )
                      -> ( ( Y + 2 ) mod N ) =/= ( ( Y + 1 ) mod N ) ) $=
      ( c5 cuz cfv wcel c2 cz c1 co cabs caddc cmo adantr a1i clt wbr cr wa wne
      cn cmin cfzo eluz5nn simpr 2z 1zzd 2m1e1 fveq2i abs1 eqtri cle eluz2 1red
      w3a 5re zre 3ad2ant2 1lt5 simp3 ltletrd sylbi sylanbrc eqeltrid mod2addne
      1elfzo1 syl131anc ) BEFGHZCAHZUAZBUCHZVKIJHZKJHIKUDLZMGZKBUELZHCINLBOLCKN
      LBOLUBVJVMVKBUFZPVJVKUGVNVLUHQVLUIVLVPKVQVPKMGKVOKMUJUKULUMVJKVQHZVKVJVMK
      BRSZVSVRVJEJHZBJHZEBUNSZUQZVTEBUOWDKEBWDUPETHWDURQWBWABTHWCBUSUTKERSWDVAQ
      WAWBWCVBVCVDBVHVEPVFIKABCDVGVI $.

    $( A nonnegative integer less than a modulus greater than 4 plus one/minus
       two are not equal modulo the modulus.  (Contributed by AV,
       22-Nov-2025.) $)
    modm1nep2 $p |- ( ( N e. ( ZZ>= ` 5 ) /\ Y e. I )
                      -> ( ( Y - 1 ) mod N ) =/= ( ( Y + 2 ) mod N ) ) $=
      ( c5 cfv wcel wa c1 co cmo caddc c2 cz cabs adantr a1i c3 wbr cr cuz cmin
      cneg wceq cc0 cfzo elfzoelz eleq2s zcnd 1cnd negsubd eqcomd oveq1d adantl
      cn wne eluz5nn simpr 2z 1zzd znegcld 2cn ax-1cn subnegi 2p1e3 fveq2i 3nn0
      eqtri nn0absidi clt 3nn cle w3a eluz2 3re 5re 3lt5 ltletrd 3adant1 elfzo1
      zre sylbi syl3anbrc eqeltrid mod2addne syl131anc necomd eqnetrd ) BEUAFGZ
      CAGZHZCIUBJZBKJZCIUCZLJZBKJZCMLJBKJZWJWMWPUDWIWJWLWOBKWJWOWLWJCIWJCCNGCUE
      BUFJACUEBUGDUHUIWJUJUKULUMUNWKWQWPWKBUOGZWJMNGZWNNGMWNUBJZOFZIBUFJZGWQWPU
      PWIWRWJBUQZPWIWJURWSWKUSQWKIWKUTVAWKXARXBXAROFRWTROWTMILJRMIVBVCVDVEVHVFR
      VGVIVHWIRXBGZWJWIRUOGZWRRBVJSZXDXEWIVKQXCWIENGZBNGZEBVLSZVMXFEBVNXHXIXFXG
      XHXIHZREBRTGXJVOQETGXJVPQXHBTGXIBWAPREVJSXJVQQXHXIURVRVSWBBRVTWCPWDMWNABC
      DWEWFWGWH $.

    $( A nonnegative integer less than a modulus greater than 4 minus one/minus
       two are not equal modulo the modulus.  (Contributed by AV,
       22-Nov-2025.) $)
    modm1nem2 $p |- ( ( N e. ( ZZ>= ` 5 ) /\ Y e. I )
                      -> ( ( Y - 1 ) mod N ) =/= ( ( Y - 2 ) mod N ) ) $=
      ( c5 cfv wcel wa c1 cmin co cmo c2 wne cneg cz cabs adantr a1i wbr cuz cn
      caddc cfzo eluz5nn simpr 1zzd znegcld 2z cc wceq ax-1cn 2cn neg2sub mp2an
      2m1e1 eqtri fveq2i abs1 clt cle w3a eluz2 1red cr 5re zre ltletrd 3adant1
      1lt5 1elfzo1 sylanbrc eqeltrid mod2addne syl131anc wb cc0 elfzoelz eleq2s
      sylbi zcnd 1cnd negsubd eqcomd oveq1d 2cnd neeq12d adantl mpbird ) BEUAFG
      ZCAGZHZCIJKZBLKZCMJKZBLKZNZCIOZUCKZBLKZCMOZUCKZBLKZNZWLBUBGZWKWRPGXAPGWRX
      AJKZQFZIBUDKZGXDWJXEWKBUEZRWJWKUFWLIWLUGUHWLMMPGWLUISUHWLXGIXHXGIQFIXFIQX
      FMIJKZIIUJGMUJGXFXJUKULUMIMUNUOUPUQURUSUQWJIXHGZWKWJXEIBUTTZXKXIWJEPGZBPG
      ZEBVATZVBXLEBVCXNXOXLXMXNXOHZIEBXPVDEVEGXPVFSXNBVEGXOBVGRIEUTTXPVJSXNXOUF
      VHVIVTBVKVLRVMWRXAABCDVNVOWKWQXDVPWJWKWNWTWPXCWKWMWSBLWKWSWMWKCIWKCCPGCVQ
      BUDKACVQBVRDVSWAZWKWBWCWDWEWKWOXBBLWKXBWOWKCMXQWKWFWCWDWEWGWHWI $.

    $( If an integer minus one equals another integer plus one modulo an
       integer greater than 4, then the first integer plus one is not equal to
       the second integer minus one modulo the same modulus.  (Contributed by
       AV, 15-Nov-2025.) $)
    modm1p1ne $p |- ( ( N e. ( ZZ>= ` 5 ) /\ X e. I /\ Y e. I )
                      -> ( ( ( Y - 1 ) mod N ) = ( ( X + 1 ) mod N )
                        -> ( ( Y + 1 ) mod N ) =/= ( ( X - 1 ) mod N ) ) ) $=
      ( c5 cuz wcel c1 co cmo wceq wne c4 cc0 cz wbr clt a1i cr cfv w3a cmin wa
      caddc cmul wn cfzo cle eluz2 cn0 cn 4nn0 simp2 0red 5re zre 3ad2ant2 5pos
      simp3 ltletrd elnnz sylanbrc 4re 4lt5 elfzo0 syl3anbrc sylbi zmodidfzoimp
      syl eqnetrd df-ne 4cn mulridi oveq1i neeq1i bitr3i sylibr 3ad2ant1 adantr
      4ne0 wb uzuzle35 eluz3nn elfzoelz eleq2s 3ad2ant3 1zzd modmkpkne syl13anc
      wi c3 imp mtbird neqned ex ) BFGUAHZCAHZDAHZUBZDIUCJBKJCIUEJBKJLZDIUEJBKJ
      ZCIUCJBKJZMWTXAUDZXBXCXDXBXCLZNIUFJZBKJZOLZWTXHUGZXAWQWRXIWSWQNBKJZOMZXIW
      QXJNOWQNOBUHJZHZXJNLWQFPHZBPHZFBUIQZUBZXMFBUJXQNUKHZBULHZNBRQXMXRXQUMSXQX
      OOBRQXSXNXOXPUNXQOFBXQUOFTHXQUPSZXOXNBTHXPBUQURZOFRQXQUSSXNXOXPUTZVABVBVC
      XQNFBNTHXQVDSXTYANFRQXQVESYBVANBVFVGVHNBVIVJNOMWQWASVKXIXGOMXKXGOVLXGXJOX
      FNBKNVMVNVOVPVQVRVSVTWTXAXEXHWBZWTXSCPHZDPHZIPHXAYCWKWQWRXSWSWQBWLGUAHXSB
      WCBWDVJVSWRWQYDWSYDCXLACOBWEEWFURWSWQYEWRYEDXLADOBWEEWFWGWTWHIBCDWIWJWMWN
      WOWP $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The infinite sequence builder "seq"
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d k n x F $.  $d k n x M $.  $d k n x N $.  $d k n x ph $.
    smonoord.0 $e |- ( ph -> M e. ZZ ) $.
    smonoord.1 $e |- ( ph -> N e. ( ZZ>= ` ( M + 1 ) ) ) $.
    smonoord.2 $e |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) e. RR ) $.
    smonoord.3 $e |- ( ( ph /\ k e. ( M ... ( N - 1 ) ) ) ->
                   ( F ` k ) < ( F ` ( k + 1 ) ) ) $.
    $( Ordering relation for a strictly monotonic sequence, increasing case.
       Analogous to ~ monoord (except that the case ` M = N ` must be
       excluded).  Duplicate of ~ monoords ?  (Contributed by AV,
       12-Jul-2020.) $)
    smonoord $p |- ( ph -> ( F ` M ) < ( F ` N ) ) $=
      ( c1 caddc co wcel cfv clt wbr wi fveq2 sylc cr vx vn cfz cuz eluzfz2 syl
      cv wceq eleq1 breq2d imbi12d imbi2d cz cmin wral eluzp1m1 syl2anc eluzfz1
      weq ralrimiva fvoveq1 breq12d rspcv a1d wa peano2fzr adantll ex peano2uzr
      a1i imim1d adantr impcom eluzelz adantl elfzuz3 ad2antll elfzuzb sylanbrc
      syl11 cle zre lep1d jccir eluzuzle eleq1d fzp1ss sseld com12 lttr syl3anc
      wss mpan2d animpimp2impd uzind4 mpcom mpd ) AEDJKLZEUCLZMZDCNZECNZOPZAEWR
      UDNZMZWTGWREUEUFXEAWTXCQZGAUAUGZWSMZXAXGCNZOPZQZQAWRWSMZXAWRCNZOPZQZQZAUB
      UGZWSMZXAXQCNZOPZQZQAXQJKLZWSMZXAYBCNZOPZQZQAXFQUAUBWREXGWRUHZXKXOAYGXHXL
      XJXNXGWRWSUIYGXIXMXAOXGWRCRUJUKULUAUBUSZXKYAAYHXHXRXJXTXGXQWSUIYHXIXSXAOX
      GXQCRUJUKULXGYBUHZXKYFAYIXHYCXJYEXGYBWSUIYIXIYDXAOXGYBCRUJUKULXGEUHZXKXFA
      YJXHWTXJXCXGEWSUIYJXIXBXAOXGECRUJUKULXPWRUMMAXNXLADDEJUNLZUCLZMZBUGZCNZYN
      JKLCNZOPZBYLUOZXNAYKDUDNZMZYMADUMMZXEYTFGDEUPUQDYKURUFAYQBYLIUTZYQXNBDYLY
      NDUHZYOXAYPXMOYNDCRZYNDJCKVAVBVCSVDVJXQXDMZAYAYCYEXTAUUEVEZYCXRXTUUFYCXRU
      UEYCXRAXQWREVFVGVHVKAUUEYCVEZVEZXTXSYDOPZYEUUHXQYLMZYRUUIUUHXQYSMZYKXQUDN
      MZUUJUUGAUUKUUEAUUKQYCUUAUUEUUKAUUAUUEUUKDXQVIVHFVTVLVMZUUHXQUMMZEYBUDNMZ
      UULUUGUUNAUUEUUNYCWRXQVNVLVOYCUUOAUUEYBWREVPVQXQEUPUQXQDYKVRVSAYRUUGUUBVL
      YQUUIBXQYLBUBUSZYOXSYPYDOYNXQCRZYNXQJCKVAVBVCSUUHXATMZXSTMZYDTMZXTUUIVEYE
      QAUURUUGADDEUCLZMZYOTMZBUVAUOZUURAEYSMZUVBAUUADWRWAPZVEXEUVEAUUAUVFFUUADD
      WBWCWDGWRDEWESDEURUFAUVCBUVAHUTZUVCUURBDUVAUUCYOXATUUDWFVCSVLUUHXQUVAMZUV
      DUUSUUHUUKYBUVAMZUVHUUMUUGAUVIYCAUVIQUUEAYCUVIAWSUVAYBAUUAWSUVAWLFDEWGUFW
      HWIVOVMZXQDEVFUQAUVDUUGUVGVLZUVCUUSBXQUVAUUPYOXSTUUQWFVCSUUHUVIUVDUUTUVJU
      VKUVCUUTBYBUVAYNYBUHYOYDTYNYBCRWFVCSXAXSYDWJWKWMWNWOWPWQ $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Integer powers - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Two times an integer greater than 2 is less than the square of the
     integer.  (Contributed by AV, 6-Apr-2026.) $)
  2timesltsq $p |- ( A e. ( ZZ>= ` 3 ) -> ( 2 x. A ) < ( A ^ 2 ) ) $=
    ( c3 cuz cfv wcel c2 cmul co cexp clt cr cc0 wbr wa 2re a1i eluzelz eluz3nn
    zred cle nngt0d eluzle c1 caddc df-3 breq1i cz 2z zltp1led biimprd biimtrid
    jca mpd ltmul1a syl31anc zcnd sqvald breqtrrd ) ABCDEZFAGHZAAGHZAFIHJUSFKEZ
    AKEZVCLAJMZNFAJMZUTVAJMVBUSOPUSABAQZSZUSVCVDVGUSAARUAULUSBATMZVEBAUBVHFUCUD
    HZATMZUSVEBVIATUEUFUSVEVJUSFAFUGEUSUHPVFUIUJUKUMFAAUNUOUSAUSAVFUPUQUR $.

  $( Two times an integer greater than 2 is less than the square of the integer
     minus 1.  (Contributed by AV, 7-Apr-2026.) $)
  2timesltsqm1 $p |- ( A e. ( ZZ>= ` 3 ) -> ( 2 x. A ) < ( ( A ^ 2 ) - 1 ) ) $=
    ( c3 wcel c2 cmul co c1 cmin cr 2re a1i remulcld peano2rem syl cle wbr 1red
    cz mpbid clt cuz cfv cexp eluzelre eluzelz zsqcl zred caddc eluzle eqbrtrid
    2p1e3 wb leaddsub mp3an2i eluz3nn lemul1d eluzelcn mulsubfacd sqvald eqcomd
    nnrpd oveq1d w3a eluz2 wi df-3 breq1i 2z id zltp1led bitr4id wa adantr 1lt2
    zre simpr lttrd ex sylbid 3imp sylbi ltsub2dd eqbrtrd eqbrtrrd lelttrd ) AB
    UAUBCZDAEFZAGHFZAEFZADUCFZGHFZWFDADICZWFJKZBAUDZLWFWHAWFAICZWHICWNAMNZWNLWF
    WJICWKICWFWJWFARCZWJRCBAUEAUFNUGZWJMNWFDWHOPZWGWIOPWFDGUHFZAOPZWSWFWTBAOUKB
    AUIUJWLWFGICWOXAWSULJWFQZWNDGAUMUNSWFDWHAWMWPWFAAUOVAUPSWFAAEFZAHFZWIWKTWFA
    ABAUQZXEURWFXDWJAHFWKTWFXCWJAHWFWJXCWFAXEUSUTVBWFGAWJXBWNWRWFBRCZWQBAOPZVCG
    ATPZBAVDXFWQXGXHWQXGXHVEVEXFWQXGDATPZXHWQXGXAXIBWTAOVFVGWQDADRCWQVHKWQVIVJV
    KWQXIXHWQXIVLZGDAXJQWLXJJKWQWOXIAVOVMGDTPXJVNKWQXIVPVQVRVSKVTWAWBWCWDWE $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Finite and infinite sums - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d A k x $.  $d B x $.  $d X k x $.
    $( A finite sum with one of its integer summands removed is a real number.
       (Contributed by Alexander van der Vekens, 31-Aug-2018.) $)
    fsummsndifre $p |- ( ( A e. Fin /\ A. k e. A B e. ZZ )
                            -> sum_ k e. ( A \ { X } ) B e. RR ) $=
      ( vx cfn wcel cz wral wa csn cdif csu cv csb csbeq1a nfcv nfcsb1v cbvsum
      cr diffi adantr wi eldifi rspcsbela sylan zred expcom adantl imp fsumrecl
      eqeltrid ) AFGZBHGCAIZJZADKZLZBCMUQCENZBOZEMTUQBUSCECURBPEBQCURBRSUOUQUSE
      UMUQFGUNAUPUAUBUOURUQGZUSTGZUNUTVAUCUMUTUNVAUTUNJUSUTURAGUNUSHGURAUPUDCUR
      ABHUEUFUGUHUIUJUKUL $.

    $( Separate out a term in a finite sum by splitting the sum into two parts.
       (Contributed by Alexander van der Vekens, 31-Aug-2018.) $)
    fsumsplitsndif $p |- ( ( A e. Fin /\ X e. A /\ A. k e. A B e. ZZ )
          -> sum_ k e. A B = ( sum_ k e. ( A \ { X } ) B + [_ X / k ]_ B ) ) $=
      ( vx cfn wcel cz wral csu caddc co csb wceq cun cc rspcsbela zcnd cbvsum
      wa w3a csn cdif cv wn cin neldifsnd disjsn sylibr uncom simp2 snssd undif
      c0 wss sylib eqtr2id simp1 expcom 3ad2ant3 fsumsplit csbeq1a nfcv nfcsb1v
      wi imp oveq12i 3eqtr4g 3adant1 sumsns syl2anc oveq2d eqtrd ) AFGZDAGZBHGC
      AIZUAZABCJZADUBZUCZBCJZVSBCJZKLZWACDBMZKLVQACEUDZBMZEJVTWFEJZVSWFEJZKLVRW
      CVQVTVSWFAEVQDVTGUEVTVSUFUNNVQDAUGVTDUHUIVQVTVSOVSVTOZAVTVSUJVQVSAUOWIANV
      QDAVNVOVPUKZULVSAUMUPUQVNVOVPURVQWEAGZWFPGZVPVNWKWLVEVOWKVPWLWKVPTWFCWEAB
      HQRUSUTVFVAABWFCECWEBVBZEBVCZCWEBVDZSWAWGWBWHKVTBWFCEWMWNWOSVSBWFCEWMWNWO
      SVGVHVQWBWDWAKVQVOWDPGZWBWDNWJVOVPWPVNVOVPTWDCDABHQRVIBCDAVJVKVLVM $.

    $d N k x $.
    $( A finite sum of summands modulo a positive number with one of its
       summands removed is a real number.  (Contributed by Alexander van der
       Vekens, 31-Aug-2018.) $)
    fsummmodsndifre $p |- ( ( A e. Fin /\ N e. NN /\ A. k e. A B e. ZZ )
                            -> sum_ k e. ( A \ { X } ) ( B mod N ) e. RR ) $=
      ( vx cfn wcel cn cz cmo co csu csb cr wa wi cvv adantr eqeltrid wral cdif
      w3a csn csbeq1a nfcv nfcsb1v cbvsum diffi 3ad2ant1 eldifi rspcsbela sylan
      expcom 3ad2ant3 imp wceq vex csbov1g ax-mp zre adantl crp modcld 3ad2ant2
      cv nnrp ex mpd fsumrecl ) AGHZDIHZBJHCAUAZUCZAEUDZUBZBDKLZCMVPCFVFZVQNZFM
      OVPVQVSCFCVRVQUEFVQUFCVRVQUGUHVNVPVSFVKVLVPGHVMAVOUIUJVNVRVPHZPCVRBNZJHZV
      SOHZVNVTWBVMVKVTWBQVLVTVMWBVTVRAHVMWBVRAVOUKCVRABJULUMUNUOUPVNWBWCQZVTVLV
      KWDVMVLWBWCVLWBPZVSWADKLZOVRRHVSWFUQFURCVRBDKRUSUTWEWADWBWAOHVLWAVAVBVLDV
      CHWBDVGSVDTVHVESVIVJT $.
  $}

  ${
    $d A k x $.  $d B x $.  $d N k x $.  $d k x z $.
    $( A finite sum of summands modulo a positive number with an additional
       summand is an integer.  (Contributed by Alexander van der Vekens,
       1-Sep-2018.) $)
    fsummmodsnunz $p |- ( ( A e. Fin /\ N e. NN
                             /\ A. k e. ( A u. { z } ) B e. ZZ )
                           -> sum_ k e. ( A u. { z } ) ( B mod N ) e. ZZ ) $=
      ( vx cfn wcel cn cz cv csn cmo co csu csb wa wi cvv eqeltrid cun wral w3a
      csbeq1a nfcv nfcsb1v cbvsum snfi mpan2 3ad2ant1 rspcsbela expcom 3ad2ant3
      unfi imp wceq vex csbov1g ax-mp simpr simpl zmodcld nn0zd 3ad2ant2 adantr
      ex mpd fsumzcl ) BGHZEIHZCJHDBAKZLZUAZUBZUCZVMCEMNZDOVMDFKZVPPZFOJVMVPVRD
      FDVQVPUDFVPUEDVQVPUFUGVOVMVRFVIVJVMGHZVNVIVLGHVSVKUHBVLUNUIUJVOVQVMHZQDVQ
      CPZJHZVRJHZVOVTWBVNVIVTWBRVJVTVNWBDVQVMCJUKULUMUOVOWBWCRZVTVJVIWDVNVJWBWC
      VJWBQZVRWAEMNZJVQSHVRWFUPFUQDVQCEMSURUSWEWFWEWAEVJWBUTVJWBVAVBVCTVFVDVEVG
      VHT $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  The divides relation - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    $d M m n $.  $d N m n $.
    $( Definition of the divides relation for divisors greater than 1.
       (Contributed by AV, 5-Apr-2026.) $)
    nndivides2 $p |- ( ( M e. ( 2 ..^ N ) /\ N e. NN )
                      -> ( M || N <-> E. n e. ( 2 ..^ N ) ( n x. M ) = N ) ) $=
      ( vm c2 cfzo co wcel cn wa cv cmul wceq wrex wb simpr adantr wss c1 mp1i
      cdvds wbr elfzo2nn nndivides sylan oveq1 eqeq1d cbvrexvw simplll nnmulcom
      weq anim1i syl eqtrd nnmul2 syl3anc adantl rspcedvd ex rexlimdva biimtrid
      mpdan wi fzossnn cuz cfv 2eluzge1 fzoss1 sstrd ax-mp ssrexv impbid bitrd
      id ) BECFGZHZCIHZJZBCUAUBZAKZBLGZCMZAINZWBAVONZVPBIHZVQVSWCOBCUCZABCUDUEV
      RWCWDWCDKZBLGZCMZDINVRWDWBWIADIADUKZWAWHCVTWGBLUFUGZUHVRWIWDDIVRWGIHZJZWI
      WDWMWIJZWGVOHZWDWNVPWLBWGLGZCMWOVPVQWLWIUIWMWLWIVRWLPQWNWPWHCWNWEWLJZWPWH
      MWMWQWIVRWEWLVPWEVQWFQULQBWGUJUMWMWIPZUNBWGCUOUPWNWOJZWBWIAWGVOWNWOPWJWBW
      IOWSWKUQWNWIWOWRQURVBUSUTVAVOIRZWDWCVCVRSCFGZIRZWTCVDXBVOXAIESVEVFHVOXARX
      BVGESCVHTXBVNVIVJWBAVOIVKTVLVM $.
  $}

  $( The factorial of a nonnegative integer divides the factorial of an integer
     which is greater than or equal to the first integer.  (Contributed by AV,
     6-Apr-2026.) $)
  facnn0dvdsfac $p |- ( M e. ( 0 ... N ) -> ( ! ` M ) || ( ! ` N ) ) $=
    ( cc0 cfz co wcel cfa cfv cdvds wbr cdiv cz cn permnn nnz syl wne cn0 faccl
    nnzd w3a wb elfznn0 facne0 elfz3nn0 3jca dvdsval2 mpbird ) ACBDEFZAGHZBGHZI
    JZUKUJKEZLFZUIUMMFUNABNUMOPUIUJLFZUJCQZUKLFZUAULUNUBUIUOUPUQUIUJUIARFZUJMFA
    BUCZASPTUIURUPUSAUDPUIUKUIBRFUKMFABUEBSPTUFUJUKUGPUH $.

  $( The product of two different positive integers divides the factorial of
     the bigger integer.  (Contributed by AV, 6-Apr-2026.) $)
  muldvdsfacgt $p |- ( A e. ( 1 ..^ B ) -> ( A x. B ) || ( ! ` B ) ) $=
    ( c1 co wcel cmul cfa cfv cdvds cz w3a wbr cn cuz clt cc0 wa wi cr syl cfzo
    cmin elfzoelz cn0 simp2 cle eluz2 1re zre lelttr mp3an3an 0lt1 0re mp3an12i
    lttr mpani adantl syld exp4b com23 a1i 3imp sylbi jca elnnz 3imtr4i nnm1nn0
    elfzo2 faccl nnzd elfzoel2 3jca simp1bi 3ad2ant1 peano2zm 3ad2ant2 nnltlem1
    elfzo1 nnz biimp3a dvdsfac syl2anc dvdsmulc sylc wceq facnn2 breqtrrd ) ACB
    UADEZABFDZBCUBDZGHZBFDZBGHZIWHAJEZWKJEZBJEZKAWKILZWIWLILWHWNWOWPACBUCWHWJUD
    EZWOWHBMEZWRACNHEZWPABOLZKZWPPBOLZQWHWSXBWPXCWTWPXAUEWTWPXAXCWTCJEZWNCAUFLZ
    KWPXAXCRZRZCAUGXDWNXEXGWNXEXGRRXDWNWPXEXFWNWPXEXAXCWNWPQXEXAQZCBOLZXCCSEZWN
    ASEWPBSEZXHXIRUHAUIBUIZCABUJUKWPXIXCRWNWPPCOLZXIXCULPSEXJWPXKXMXIQXCRUMUHXL
    PCBUOUNUPUQURUSUTVAVBVCVBVDACBVHBVEVFZBVGTWRWKWJVIVJTACBVKVLWHAMEZWJANHEZWQ
    WHXOWSXABAVRZVMXOWSXAKZWNWJJEZAWJUFLZKWHXPXRWNXSXTXOWSWNXAAVSVNWSXOXSXAWSWP
    XSBVSBVOTVPXOWSXAXTABVQVTVLXQAWJUGVFAWJWAWBBAWKWCWDWHWSWMWLWEXNBWFTWG $.

  $( The product of two different positive integers less than a third integer
     divides the factorial of the third integer decreased by 1.  By assumption,
     the third integer must be greater than 3.  (Contributed by AV,
     6-Apr-2026.) $)
  muldvdsfacm1 $p |- ( ( A e. ( 1 ..^ B ) /\ B e. ( 1 ..^ N ) )
                       -> ( A x. B ) || ( ! ` ( N - 1 ) ) ) $=
    ( c1 cfzo co wcel wa cfa cfv cz elfzoelz clt wbr sylbi adantl cc0 wi cr syl
    cmul cmin zmulcl syl2an cn0 cuz w3a elfzo2 cn elnnuz sylbir 3ad2ant1 faccld
    nnnn0 nnzd simp2 cle eluz2 1red zre adantr lelttr 0lt1 0red lttr mpani syld
    syl3anc exp4b com23 3imp elnnz sylanbrc nnm1nn0 cdvds muldvdsfacgt 1eluzge0
    a1i cfz fzoss1 sseld ax-mp wb elfzoel2 fzoval eleq2d facnn0dvdsfac dvdstrd
    mpbid ) ADBEFGZBDCEFZGZHZABUAFZBIJZCDUBFZIJZWJAKGBKGZWNKGWLADBLBDCLABUCUDWM
    WOWMBWLBUEGZWJWLBDUFJGZCKGZBCMNZUGZWSBDCUHZWTXAWSXBWTBUIGWSBUJBUNUKULOPUMUO
    WMWQWMWPWLWPUEGZWJWLXCXEXDXCCUIGZXEXCXAQCMNZXFWTXAXBUPWTXAXBXGWTDKGZWRDBUQN
    ZUGXAXBXGRZRZDBURXHWRXIXKWRXIXKRRXHWRXAXIXJWRXAXIXBXGWRXAHZXIXBHZDCMNZXGXLD
    SGZBSGZCSGZXMXNRXLUSWRXPXABUTVAXAXQWRCUTZPDBCVBVHXAXNXGRWRXAQDMNZXNXGVCXAQS
    GXOXQXSXNHXGRXAVDXAUSXRQDCVEVHVFPVGVIVJVRVKOVKCVLVMCVNTOPUMUOWJWNWOVONWLABV
    PVAWMBQWPVSFZGZWOWQVONWLYAWJWLBQCEFZGZYADQUFJGZWLYCRVQYDWKYBBDQCVTWAWBWLXAY
    CYAWCBDCWDXAYBXTBQCWEWFTWIPBWPWGTWH $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Extensible structures - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  ${
    setsidel.s $e |- ( ph -> S e. V ) $.
    setsidel.b $e |- ( ph -> B e. W ) $.
    setsidel.r $e |- R = ( S sSet <. A , B >. ) $.
    $( The injected slot is an element of the structure with replacement.
       (Contributed by AV, 10-Nov-2021.) $)
    setsidel $p |- ( ph -> <. A , B >. e. R ) $=
      ( cop cvv csn cdif cres cun wcel opex snid elun2 mp1i csts co wceq eqtrid
      setsval syl2anc eleqtrrd ) ABCKZELBMNOZUIMZPZDUIUKQUIULQAUIBCRSUIUKUJTUAA
      DEUIUBUCZULJAEFQCGQUMULUDHIBCEFGUFUGUEUH $.

    setsnidel.c $e |- ( ph -> C e. X ) $.
    setsnidel.d $e |- ( ph -> D e. Y ) $.
    setsnidel.s $e |- ( ph -> <. C , D >. e. S ) $.
    setsnidel.n $e |- ( ph -> A =/= C ) $.
    $( The injected slot is an element of the structure with replacement.
       (Contributed by AV, 10-Nov-2021.) $)
    setsnidel $p |- ( ph -> <. C , D >. e. R ) $=
      ( cvv wcel cop csn cdif cres cun elexd necomd eldifsn sylanbrc wa opelres
      wne wb syl mpbir2and elun1 csts co wceq setsval syl2anc eqtrid eleqtrrd )
      ADEUAZGSBUBUCZUDZBCUAZUBZUEZFAVDVFTZVDVITAVJDVETZVDGTZADSTDBULVKADJOUFABD
      RUGDSBUHUIQAEKTVJVKVLUJUMPVEDEGKUKUNUOVDVFVHUPUNAFGVGUQURZVINAGHTCITVMVIU
      SLMBCGHIUTVAVBVC $.
  $}

  $( The value of the structure replacement function is a set.  (Contributed by
     AV, 10-Nov-2021.) $)
  setsv $p |- ( ( S e. V /\ B e. W ) -> ( S sSet <. A , B >. ) e. _V ) $=
    ( wcel wa cop csts co cvv csn cdif cres cun setsval resexg snex a1i unexg
    syl2an2r eqeltrd ) CDFZBEFZGZCABHZIJCKALMZNZUFLZOZKABCDEPUCUHKFUDUIKFZUJKFC
    UGDQUKUEUFRSUHUIKKTUAUB $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Preimages of function values
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  According to Wikipedia ("Image (mathematics)", 17-Mar-2024,
  ~ https://en.wikipedia.org/wiki/ImageSupport_(mathematics) ): "... evaluating
  a given function ` f ` at each element of a given subset ` A ` of its domain
  produces a set, called the "image of ` A ` under (or through) ` f `".
  Similarly, the inverse image (or preimage) of a given subset ` B ` of the
  codomain of ` f ` is the set of all elements of the domain that map to the
  members of ` B ` ."  The preimage of a set ` B ` under a function ` f ` is
  often denoted as "f^-1 (B)", but in set.mm, the idiom ` ( ``' f " B ) ` is
  used.  As a special case, the idiom for the preimage of a function value at
  ` X ` under a function ` F ` is ` ( ``' F " { ( F `` X ) } ) ` (according to
  Wikipedia, the preimage of a singleton is also called a "fiber").

  We use the label fragment "preima" (as in ~ mptpreima ) for theorems about
  preimages (sometimes, also "imacnv" is used as in ~ fvimacnvi ), and
  "preimafv" (as in ~ preimafvn0 ) for theorems about preimages of a function
  value.

  In this section, ` P = { z | E. x e. A z = ( ``' F " { ( F `` x ) } ) } `
  will be the set of all preimages of function values of a function ` F `,
  that means ` S e. P ` is a preimage of a function value (see, for example,
  ~ elsetpreimafv ): ` S = ( ``' F " { ( F `` x ) } ) `.

  With the help of such a set, it is shown that every function ` F : A --> B `
  can be decomposed into a surjective and an injective function (see
  ~ fundcmpsurinj ) by constructing a surjective function ` g : A -onto-> P `
  and an injective function ` h : P -1-1-> B ` so that ` F = ( h o. g ) ` ( see
  ~ fundcmpsurinjpreimafv ).  See also Wikipedia ("Surjective function",
  17-Mar-2024, ~ https://en.wikipedia.org/wiki/Surjective_function (section
  "Composition and decomposition").  This is different from the decomposition
  of ` F ` into the surjective function ` g : A -onto-> ( F " A ) ` (with
  ` ( g `` x ) = ( F `` x ) ` for ` x e. A `) and the injective function
  ` h = ( _I |`` ( F " A ) ) `,  ( see ~ fundcmpsurinjimaid ), see also
  Wikipedia ("Bijection, injection and surjection", 17-Mar-2024,
  ~ https://en.wikipedia.org/wiki/Bijection,_injection_and_surjection (section
  "Properties").

  Finally, it is shown that every function ` F : A --> B ` can be decomposed
  into a surjective, a bijective and an injective function (see
  ~ fundcmpsurbijinj ), by showing that there is a bijection between the set of
  all preimages of values of a function and the range of the function (see
  ~ imasetpreimafvbij ).  From this, both variants of decompositions of a
  function into a surjective and an injective function can be derived:

  Let ` F = ( ( I o. B ) o. S ) ` be a decomposition of a function into a
  surjective, a bijective and an injective function, then ` F = ( J o. S ) `
  with ` J = ( I o. B ) ` (an injective function) is a decomposition into a
  surjective and an injective function corresponding to ~ fundcmpsurinj , and
  ` F = ( I o. O ) ` with ` O = ( B o. S ) ` (a surjective function) is a
  decomposition into a surjective and an injective function corresponding to
  ~ fundcmpsurinjimaid .

$)

  $( The preimage of a function value at ` X ` contains ` X ` .  (Contributed
     by AV, 7-Mar-2024.) $)
  preimafvsnel $p |- ( ( F Fn A /\ X e. A )
                       -> X e. ( `' F " { ( F ` X ) } ) ) $=
    ( wfn wcel wa ccnv cfv csn cima wceq simpr eqidd fniniseg adantr mpbir2and
    wb ) BADZCAEZFZCBGCBHZIJEZSUAUAKZRSLTUAMRUBSUCFQSAUACBNOP $.

  $( The preimage of a function value is not empty.  (Contributed by AV,
     7-Mar-2024.) $)
  preimafvn0 $p |- ( ( F Fn A /\ X e. A )
                     -> ( `' F " { ( F ` X ) } ) =/= (/) ) $=
    ( wfn wcel wa ccnv cfv csn cima preimafvsnel ne0d ) BADCAEFBGCBHIJCABCKL $.

  ${
    $d F x y $.  $d S x y $.  $d X x y $.
    $( The union of the image of a subset ` S ` of the domain of a function
       with elements having the same function value is the function value at
       one of the elements of ` S ` .  (Contributed by AV, 5-Mar-2024.) $)
    uniimafveqt $p |- ( ( F : A --> B /\ S C_ A /\ X e. S )
                       -> ( A. x e. S ( F ` x ) = ( F ` X )
                          -> U. ( F " S ) = ( F ` X ) ) ) $=
      ( vy wf wss wcel w3a cv cfv wceq wral cima cuni wa ciun wfun 3ad2ant1 syl
      ffun adantr funiunfv simp3 cbvralvw biimpi fveq2 iuneqconst syl2an eqtr3d
      fveqeq2 ex ) BCEHZDBIZFDJZKZALZEMFEMZNZADOZEDPQZUTNURVBRZGDGLZEMZSZVCUTVD
      ETZVGVCNURVHVBUOUPVHUQBCEUCUAUDGDEUEUBURUQVFUTNZGDOZVGUTNVBUOUPUQUFVBVJVA
      VIAGDUSVEUTEUMUGUHGDVFUTFVEFEUIUJUKULUN $.
  $}

  ${
    $d A x $.  $d F x $.  $d X x $.
    $( The union of the image of the preimage of a function value is the
       function value.  (Contributed by AV, 12-Mar-2024.) $)
    uniimaprimaeqfv $p |- ( ( F Fn A /\ X e. A )
                        -> U. ( F " ( `' F " { ( F ` X ) } ) ) = ( F ` X ) ) $=
      ( vx wfn wcel wa crn wf ccnv cfv csn cima wss w3a wceq wral cuni adantr
      cv dffn3 birani cdm cnvimass fndm sseqtrid preimafvsnel wb fniniseg simpr
      3jca biimtrdi ralrimiv uniimafveqt sylc ) BAEZCAFZGZABHZBIZBJCBKZLZMZANZC
      VCFZODTZBKVAPZDVCQBVCMRVAPURUTVDVEUPUTUQABUAUBUPVDUQUPBUCVCABVBUDABUEUFSA
      BCUGUKURVGDVCURVFVCFZVFAFZVGGZVGUPVHVJUHUQAVAVFBUISVIVGUJULUMDAUSVCBCUNUO
      $.
  $}

  ${
    $d A x z $.  $d F x z $.
    setpreimafvex.p $e |- P = { z | E. x e. A z = ( `' F " { ( F ` x ) } ) } $.
    $( The class ` P ` of all preimages of function values is a set.
       (Contributed by AV, 10-Mar-2024.) $)
    setpreimafvex $p |- ( A e. V -> P e. _V ) $=
      ( wcel cv ccnv cfv csn cima wceq wrex cab cvv abrexexg eqeltrid ) CFHDBIE
      JAIEKLMZNACOBPQGABCTFRS $.

    ${
      $d S x z $.
      $( The characterization of an element of the class ` P ` of all preimages
         of function values.  (Contributed by AV, 10-Mar-2024.) $)
      elsetpreimafvb $p |- ( S e. V
                  -> ( S e. P <-> E. x e. A S = ( `' F " { ( F ` x ) } ) ) ) $=
        ( wcel cv ccnv cfv csn cima wceq wrex cab eleq2i eqeq1 rexbidv bitrid
        elabg ) EDIEBJZFKAJFLMNZOZACPZBQZIEGIEUDOZACPZDUGEHRUFUIBEGUCEOUEUHACUC
        EUDSTUBUA $.

      $( An element of the class ` P ` of all preimages of function values.
         (Contributed by AV, 8-Mar-2024.) $)
      elsetpreimafv $p |- ( S e. P
                                 -> E. x e. A S = ( `' F " { ( F ` x ) } ) ) $=
        ( wcel ccnv cv cfv csn cima wceq wrex elsetpreimafvb ibi ) EDHEFIAJFKLM
        NACOABCDEFDGPQ $.

      $( An element of the class ` P ` of all preimages of function values is a
         subset of the domain of the function.  (Contributed by AV,
         8-Mar-2024.) $)
      elsetpreimafvssdm $p |- ( ( F Fn A /\ S e. P ) -> S C_ A ) $=
        ( wcel wfn wss ccnv cv cfv csn cima wceq wrex wi elsetpreimafv wa sseq1
        cdm cnvimass fndm sseqtrid adantr syl5ibrcom expcom rexlimiv syl impcom
        com23 ) EDHZFCIZECJZUMEFKALZFMNZOZPZACQUNUORZABCDEFGSUSUTACUPCHZUNUSUOU
        NVAUSUORUNVATUOUSURCJZUNVBVAUNFUBURCFUQUCCFUDUEUFEURCUAUGUHULUIUJUK $.

      $( There is an element in a preimage ` S ` of function values so that
         ` S ` is the preimage of the function value at this element.
         (Contributed by AV, 8-Mar-2024.) $)
      fvelsetpreimafv $p |- ( ( F Fn A /\ S e. P )
                                 -> E. x e. S S = ( `' F " { ( F ` x ) } ) ) $=
        ( wfn ccnv cv cfv csn cima wceq wrex wcel wa preimafvsnel adantrr wb ex
        eleq2 ad2antll mpbird simprr jca reximdv2 elsetpreimafv impel ) FCHZEFI
        AJZFKLMZNZACOUMAEOEDPUJUMUMACEUJUKCPZUMQZUKEPZUMQUJUOQZUPUMUQUPUKULPZUJ
        UNURUMCFUKRSUMUPURTUJUNEULUKUBUCUDUJUNUMUEUFUAUGABCDEFGUHUI $.
    $}

    ${
      $d X x z $.
      $( The preimage of a function value is an element of the class ` P ` of
         all preimages of function values.  (Contributed by AV,
         10-Mar-2024.) $)
      preimafvelsetpreimafv $p |- ( ( F Fn A /\ A e. V /\ X e. A )
                                    -> ( `' F " { ( F ` X ) } ) e. P ) $=
        ( wfn wcel w3a ccnv cfv csn cima cv wceq wrex wb cvv fveq2 sneqd eqeq2d
        id imaeq2d adantl eqidd rspcedvd 3ad2ant3 wa fnex cnvexg imaexg 3adant3
        3syl elsetpreimafvb syl mpbird ) ECIZCFJZGCJZKZELZGEMZNZOZDJZVFVCAPZEMZ
        NZOZQZACRZVAUSVMUTVAVLVFVFQZAGCVAUDVHGQZVLVNSVAVOVKVFVFVOVJVEVCVOVIVDVH
        GEUAUBUEUCUFVAVFUGUHUIVBVFTJZVGVMSUSUTVPVAUSUTUJETJVCTJVPCFEUKETULVCVET
        UMUOUNABCDVFETHUPUQUR $.
    $}

    ${
      $d A s z $.  $d F s $.  $d P s x $.
      $( The class ` P ` of all preimages of function values is a subset of the
         power set of the domain of the function.  (Contributed by AV,
         5-Mar-2024.) $)
      preimafvsspwdm $p |- ( F Fn A -> P C_ ~P A ) $=
        ( vs wfn cv wss wral cpw elsetpreimafvssdm ralrimiva pwssb sylibr ) ECH
        ZGIZCJZGDKDCLJQSGDABCDREFMNGDCOP $.
    $}

    $( The empty set is not an element of the class ` P ` of all preimages of
       function values.  (Contributed by AV, 6-Mar-2024.) $)
    0nelsetpreimafv $p |- ( F Fn A -> (/) e/ P ) $=
      ( wfn c0 wcel wn wnel ccnv cv cfv csn cima wceq wral sylibr cvv ralrimiva
      wrex wa preimafvsnel n0i ralnex eqcom notbii ralbii bitr3i elsetpreimafvb
      syl wb 0ex ax-mp sylnibr df-nel ) ECGZHDIZJHDKURHELAMZENOPZQZACUBZUSURVAH
      QZJZACRZVCJZURVEACURUTCIUCUTVAIVECEUTUDVAUTUEULUAVGVBJZACRVFVBACUFVHVEACV
      BVDHVAUGUHUIUJSHTIUSVCUMUNABCDHETFUKUOUPHDUQS $.

    ${
      $d S x z $.  $d X x $.  $d Y x $.
      $( An element of the preimage of a function value is an element of the
         domain of the function with the same value as another element of the
         preimage.  (Contributed by AV, 9-Mar-2024.) $)
      elsetpreimafvbi $p |- ( ( F Fn A /\ S e. P /\ X e. S )
                     -> ( Y e. S <-> ( Y e. A /\ ( F ` Y ) = ( F ` X ) ) ) ) $=
        ( wfn wcel cfv wceq wa wb ccnv cv wi fniniseg eleq2 csn cima wrex eqeq2
        anbi2d eqcoms sylan9bb ex adantld sylbid bibi1d imbitrrid elsetpreimafv
        imbi12d rexlimivw syl11 3imp ) FCJZEDKZGEKZHEKZHCKZHFLZGFLZMZNZOZEFPAQF
        LZUAUBZMZACUCURUTVGRZUSVJURVKRACURVKVJGVIKZHVIKZVFOZRURVLGCKZVDVHMZNVNC
        VHGFSURVPVNVOURVPVNURVMVBVCVHMZNZVPVFCVHHFSVRVFOVHVDVHVDMVQVEVBVHVDVCUD
        UEUFUGUHUIUJVJUTVLVGVNEVIGTVJVAVMVFEVIHTUKUNULUOABCDEFIUMUPUQ $.

      $( The elements of the preimage of a function value have the same
         function values.  (Contributed by AV, 5-Mar-2024.) $)
      elsetpreimafveqfv $p |- ( ( F Fn A /\ ( S e. P /\ X e. S /\ Y e. S ) )
                                -> ( F ` X ) = ( F ` Y ) ) $=
        ( wfn wcel cfv wceq wi w3a wa elsetpreimafvbi simpr eqcomd biimtrdi
        3exp 3imp2 ) FCJZEDKZGEKZHEKZGFLZHFLZMZUCUDUEUFUINUCUDUEOUFHCKZUHUGMZPZ
        UIABCDEFGHIQULUHUGUJUKRSTUAUB $.

      $( If an element of the domain of the function has the same function
         value as an element of the preimage of a function value, then it is an
         element of the same preimage.  (Contributed by AV, 9-Mar-2024.) $)
      eqfvelsetpreimafv $p |- ( ( F Fn A /\ S e. P /\ X e. S )
                      -> ( ( Y e. A /\ ( F ` Y ) = ( F ` X ) ) -> Y e. S ) ) $=
        ( wfn wcel w3a cfv wceq wa elsetpreimafvbi biimprd ) FCJEDKGEKLHEKHCKHF
        MGFMNOABCDEFGHIPQ $.
    $}

    ${
      $d A y $.  $d F y $.  $d P y $.  $d S x z $.  $d S y $.  $d X x y $.
      $( An element of the preimage of a function value expressed as a
         restricted class abstraction.  (Contributed by AV, 9-Mar-2024.) $)
      elsetpreimafvrab $p |- ( ( F Fn A /\ S e. P /\ X e. S )
                                -> S = { x e. A | ( F ` x ) = ( F ` X ) } ) $=
        ( vy wfn wcel w3a cv cfv wceq crab wa elsetpreimafvbi fveqeq2 elrab
        bitr4di eqrdv ) FCJEDKGEKLZIEAMZFNGFNZOZACPZUCIMZEKUHCKUHFNUEOZQUHUGKAB
        CDEFGUHHRUFUIAUHCUDUHUEFSTUAUB $.

      $d P x y $.
      $( The image of an element of the preimage of a function value is the
         singleton consisting of the function value at one of its elements.
         (Contributed by AV, 5-Mar-2024.) $)
      imaelsetpreimafv $p |- ( ( F Fn A /\ S e. P /\ X e. S )
                                -> ( F " S ) = { ( F ` X ) } ) $=
        ( vy wcel w3a cv cfv csn cima wceq wrex wa 3adant3 3ad2ant1 fveq2 sneqd
        wfn ccnv fvelsetpreimafv imaeq2d eqeq2d cbvrexvw sylibr imaeq2 3ad2ant3
        crn cin fnfun funimacnv syl elsetpreimafvbi wi wss fnfvelrn snssd dfss2
        wfun sylib simp3 eqtrd 3expib sylbid imp 3eqtrd rexlimdv3a mpd ) FCUCZE
        DJZGEJZKZEFUDZILZFMZNZOZPZIEQZFEOZGFMZNZPZVMVNWCVOVMVNREVQALZFMZNZOZPZA
        EQWCABCDEFHUEWBWLIAEVRWHPZWAWKEWMVTWJVQWMVSWIVRWHFUAUBUFUGUHUISVPWBWGIE
        VPVREJZWBKWDFWAOZVTFULZUMZWFWBVPWDWOPWNEWAFUJUKVPWNWOWQPZWBVMVNWRVOVMFV
        CWRCFUNVTFUOUPTTVPWNWQWFPZWBVPWNWSVPWNVRCJZVSWEPZRZWSABCDEFGVRHUQVMVNXB
        WSURVOVMWTXAWSVMWTXAKZWQVTWFVMWTWQVTPZXAVMWTRZVTWPUSXDXEVSWPCVRFUTVAVTW
        PVBVDSXCVSWEVMWTXAVEUBVFVGTVHVISVJVKVL $.

      $( The union of the image of an element of the preimage of a function
         value is an element of the range of the function.  (Contributed by AV,
         5-Mar-2024.)  (Revised by AV, 22-Mar-2024.) $)
      uniimaelsetpreimafv $p |- ( ( F Fn A /\ S e. P )
                                  -> U. ( F " S ) e. ran F ) $=
        ( vy wfn wcel wa cv cima cuni crn wex c0 wnel wi 0nelsetpreimafv wne n0
        elnelne2 sylib expcom syl imp cfv csn wceq imaelsetpreimafv unieqd fvex
        3expa unisn eqtrdi wf dffn3 biimpi ad2antrr elsetpreimafvssdm ffvelcdmd
        sselda eqeltrd exlimddv ) FCIZEDJZKZHLZEJZFEMZNZFOZJHVFVGVJHPZVFQDRZVGV
        NSABCDFGTVGVOVNVGVOKEQUAVNEQDUCHEUBUDUEUFUGVHVJKZVLVIFUHZVMVPVLVQUIZNVQ
        VPVKVRVFVGVJVKVRUJABCDEFVIGUKUNULVQVIFUMUOUPVPCVMVIFVFCVMFUQZVGVJVFVSCF
        URUSUTVHECVIABCDEFGVAVCVBVDVE $.
    $}

    ${
      $d R x z $.  $d S x z $.  $d X x $.  $d Y x $.
      $( If two preimages of function values contain elements with identical
         function values, then both preimages are equal.  (Contributed by AV,
         8-Mar-2024.) $)
      elsetpreimafveq $p |- ( ( F Fn A /\ ( S e. P /\ R e. P )
                                                 /\ ( X e. S /\ Y e. R ) )
                                 -> ( ( F ` X ) = ( F ` Y ) -> S = R ) ) $=
        ( wcel wa w3a cfv wceq crab simpl 3anim123i adantr elsetpreimafvrab wfn
        cv eqeq2 rabbidv adantl id syl simpr 3eqtr4d ex ) GCUAZFDKZEDKZLZHFKZIE
        KZLZMZHGNZIGNZOZFEOURVALZAUBGNZUSOZACPZVCUTOZACPZFEVAVEVGOURVAVDVFACUSU
        TVCUCUDUEVBUKULUOMZFVEOURVHVAUKUKUNULUQUOUKUFZULUMQUOUPQRSABCDFGHJTUGVB
        UKUMUPMZEVGOURVJVAUKUKUNUMUQUPVIULUMUHUOUPUHRSABCDEGIJTUGUIUJ $.
    $}
  $}

  ${
    $d A x z $.  $d F x z $.
    fundcmpsurinj.p $e |- P = { z | E. x e. A z = ( `' F " { ( F ` x ) } ) } $.
    ${
      fundcmpsurinj.g $e |- G = ( x e. A |-> ( `' F " { ( F ` x ) } ) ) $.
      $( Lemma 1 for ~ fundcmpsurinj .  (Contributed by AV, 4-Mar-2024.) $)
      fundcmpsurinjlem1 $p |- ran G = P $=
        ( crn cv ccnv cfv csn cima wceq wrex cab rnmpt eqtr4i ) FIBJEKAJELMNZOA
        CPBQDABCTFHRGS $.

      $d V x $.
      $( Lemma 2 for ~ fundcmpsurinj .  (Contributed by AV, 4-Mar-2024.) $)
      fundcmpsurinjlem2 $p |- ( ( F Fn A /\ A e. V ) -> G : A -onto-> P ) $=
        ( wfn wcel wa crn wceq wfo ccnv cv cfv csn cvv cima wral fnex ralrimivw
        cnvexg imaexg 3syl fnmpt syl fundcmpsurinjlem1 df-fo sylanblrc ) ECJCGK
        LZFCJZFMDNCDFOUMEPZAQERSZUAZTKZACUBUNUMURACUMETKUOTKURCGEUCETUEUOUPTUFU
        GUDACUQFTIUHUIABCDEFHIUJCDFUKUL $.
    $}

    ${
      $d F p $.  $d P p $.  $d X p $.
      fundcmpsurinj.h $e |- H = ( p e. P |-> U. ( F " p ) ) $.
      $( Lemma 3 for ~ fundcmpsurinj .  (Contributed by AV, 3-Mar-2024.) $)
      fundcmpsurinjlem3 $p |- ( ( Fun F /\ X e. P )
                                -> ( H ` X ) = U. ( F " X ) ) $=
        ( wfun wcel wa cv cima cuni cvv cmpt wceq a1i imaeq2 unieqd funimaexg
        adantl simpr uniexd fvmptd ) EKZGDLZMZHGEHNZOZPZEGOZPZDFQFHDUMRSUJJTUKG
        SZUMUOSUJUPULUNUKGEUAUBUDUHUIUEUJUNQEGDUCUFUG $.

      $d A p x z $.  $d P x $.
      $( Lemma for ~ imasetpreimafvbij : the mapping ` H ` is a function into
         the range of function ` F ` .  (Contributed by AV, 22-Mar-2024.) $)
      imasetpreimafvbijlemf $p |- ( F Fn A -> H : P --> ( F " A ) ) $=
        ( wfn cv cima cuni wcel wa crn uniimaelsetpreimafv wceq fnima adantr
        eleqtrrd fmptd ) ECJZGDEGKZLMZECLZFUCUDDNZOUEEPZUFABCDUDEHQUCUFUHRUGCES
        TUAIUB $.

      $d A y $.  $d F y $.  $d P y $.  $d X x y $.  $d Y p $.  $d Y x y $.
      $d Y z $.
      $( Lemma for ~ imasetpreimafvbij : the value of the mapping ` H ` at a
         preimage of a value of function ` F ` .  (Contributed by AV,
         5-Mar-2024.) $)
      imasetpreimafvbijlemfv $p |- ( ( F Fn A /\ Y e. P /\ X e. Y )
                                -> ( H ` Y ) = ( F ` X ) ) $=
        ( vy wfn wcel w3a cfv cima wa wceq syl cuni cv ciun wfun anim1i 3adant3
        fnfun fundcmpsurinjlem3 3ad2ant1 funiunfv wral simpl1 elsetpreimafveqfv
        simp3 simpl2 simpr simpl3 syl13anc ralrimiva iuneqconst syl2anc 3eqtr2d
        fveq2 ) ECMZHDNZGHNZOZHFPZEHQUAZLHLUBZEPZUCZGEPZVGEUDZVERZVHVISVDVEVOVF
        VDVNVECEUGZUEUFABCDEFHIJKUHTVGVNVLVISVDVEVNVFVPUILHEUJTVGVFVKVMSZLHUKVL
        VMSVDVEVFUNVGVQLHVGVJHNZRVDVEVRVFVQVDVEVFVRULVDVEVFVRUOVGVRUPVDVEVFVRUQ
        ABCDHEVJGJUMURUSLHVKVMGVJGEVCUTVAVB $.

      $d X z $.  $d p y $.
      $( Lemma for ~ imasetpreimafvbij : for a preimage of a value of function
         ` F ` there is an element of the preimage so that the value of the
         mapping ` H ` at this preimage is the function value at this element.
         (Contributed by AV, 5-Mar-2024.) $)
      imasetpreimafvbijlemfv1 $p |- ( ( F Fn A /\ X e. P )
                                      -> E. y e. X ( H ` X ) = ( F ` y ) ) $=
        ( wfn wcel wa c0 wne cfv cv wceq wex wrex wnel 0nelsetpreimafv elnelne2
        wi expcom syl imp simpr imasetpreimafvbijlemfv 3expa jca eximdv 3imtr4g
        ex n0 df-rex mpd ) FDLZHEMZNZHOPZHGQBRZFQSZBHUAZUSUTVBUSOEUBZUTVBUEACDE
        FJUCUTVFVBHOEUDUFUGUHVAVCHMZBTVGVDNZBTVBVEVAVGVHBVAVGVHVAVGNVGVDVAVGUIU
        SUTVGVDACDEFGVCHIJKUJUKULUOUMBHUPVDBHUQUNUR $.

      $d A a b r s x $.  $d A r s z $.  $d F a b p r s $.  $d H a b r s $.
      $d P a b r s $.
      $( Lemma for ~ imasetpreimafvbij : the mapping ` H ` is an injective
         function into the range of function ` F ` .  (Contributed by AV,
         9-Mar-2024.)  (Revised by AV, 22-Mar-2024.) $)
      imasetpreimafvbijlemf1 $p |- ( F Fn A -> H : P -1-1-> ( F " A ) ) $=
        ( vs vr vb va cv cfv wceq wi wral wcel wa cima wf imasetpreimafvbijlemf
        wfn wf1 wrex imasetpreimafvbijlemfv1 anim12dan wb eqeq12 ancoms simplll
        adantl simpllr simpr anim1i elsetpreimafveq syl3anc adantr sylbid exp32
        rexlimdva com23 impd mpd ralrimivva dff13 sylanbrc ) ECUDZDECUAZFUBJNZF
        OZKNZFOZPZVKVMPZQZKDRJDRDVJFUEABCDEFGHIUCVIVQJKDDVIVKDSZVMDSZTZTZVLLNZE
        OZPZLVKUFZVNMNZEOZPZMVMUFZTVQVIVRWEVSWIALBCDEFVKGHIUGAMBCDEFVMGHIUGUHWA
        WEWIVQWAWDWIVQQLVKWAWBVKSZTZWIWDVQWKWHWDVQQMVMWKWFVMSZTZWHWDVQWMWHWDTZT
        VOWCWGPZVPWNVOWOUIZWMWDWHWPVLWCVNWGUJUKUMWMWOVPQZWNWMVIVTWJWLTWQVIVTWJW
        LULVIVTWJWLUNWKWJWLWAWJUOUPABCDVMVKEWBWFHUQURUSUTVAVBVCVBVDVEVFJKDVJFVG
        VH $.

      $d V a p y $.  $d a z $.
      $( Lemma for ~ imasetpreimafvbij : the mapping ` H ` is a function onto
         the range of function ` F ` .  (Contributed by AV, 22-Mar-2024.) $)
      imasetpreimafvbijlemfo $p |- ( ( F Fn A /\ A e. V )
                                     -> H : P -onto-> ( F " A ) ) $=
        ( va vy wcel wa cima wceq adantr cv cfv wrex imasetpreimafvbijlemf cuni
        wfn wf crn wfo cab csn preimafvelsetpreimafv 3expa imaeq2 unieqd eqeq2d
        ccnv wb adantl uniimaprimaeqfv adantlr eqcomd rspcedvd eqeq1 syl5ibrcom
        eqcoms rexbidv rexlimdva sylan9eq ex reximdva elsetpreimafv fveq2 sneqd
        imaeq2d cbvrexvw sylibr impel eqeq2 impbid abbidv cdm wss fnfun eqimss2
        wfun fndm syl jca dfimafn rnmpt a1i 3eqtr4rd dffo2 sylanbrc ) ECUCZCGMZ
        NZDECOZFUDZFUEZWPPDWPFUFWMWQWNABCDEFHIJUAQWOKRZESZLRZPZKCTZLUGZXAEHRZOZ
        UBZPZHDTZLUGZWPWRWOXCXILWOXCXIWOXBXIKCWOWSCMZNZXIXBWTXGPZHDTXLXMWTEEUNZ
        WTUHZOZOZUBZPZHXPDWMWNXKXPDMABCDEGWSIUIUJXEXPPZXMXSUOXLXTXGXRWTXTXFXQXE
        XPEUKULZUMUPXLXRWTWMXKXRWTPWNCEWSUQURUSZUTXBXHXMHDXHXMUOXAWTXAWTXGVAVCV
        DVBVEWOXHXCHDWOXEDMZNXCXHXMKCTZWOXTKCTZYDYCWOXTXMKCXLXTXMXLXTWTXRXGYBXT
        XGXRYAUSVFVGVHYCXEXNARZESZUHZOZPZACTYEABCDXEEIVIXTYJKACWSYFPZXPYIXEYKXO
        YHXNYKWTYGWSYFEVJVKVLUMVMVNVOXHXBXMKCXAXGWTVPVDVBVEVQVRWOEWCZCEVSZVTZNZ
        WPXDPWMYOWNWMYLYNCEWAWMYMCPYNCEWDCYMWBWEWFQKLCEWGWEWRXJPWOHLDXGFJWHWIWJ
        DWPFWKWL $.

      $( The mapping ` H ` is a bijective function between the set ` P ` of all
         preimages of values of function ` F ` and the range of ` F ` .
         (Contributed by AV, 22-Mar-2024.) $)
      imasetpreimafvbij $p |- ( ( F Fn A /\ A e. V )
                                -> H : P -1-1-onto-> ( F " A ) ) $=
        ( wfn wcel wa cima imasetpreimafvbijlemf1 adantr imasetpreimafvbijlemfo
        wf1 wfo wf1o df-f1o sylanbrc ) ECKZCGLZMDECNZFRZDUEFSDUEFTUCUFUDABCDEFH
        IJOPABCDEFGHIJQDUEFUAUB $.
    $}

    $d A a x z $.  $d A i $.  $d A g h y $.  $d B a g h i $.  $d B x y z $.
    $d F a i y $.  $d F g h $.  $d P a i $.  $d P g h x y $.  $d V a $.
    $d V x y $.
    $( Every function ` F : A --> B ` can be decomposed into a surjective
       function onto ` P ` , a bijective function from ` P ` and an injective
       function into the codomain of ` F ` .  (Contributed by AV,
       22-Mar-2024.) $)
    fundcmpsurbijinjpreimafv $p |- ( ( F : A --> B /\ A e. V )
           -> E. g E. h E. i ( ( g : A -onto-> P /\ h : P -1-1-onto-> ( F " A )
                  /\ i : ( F " A ) -1-1-> B ) /\ F = ( ( i o. h ) o. g ) ) ) $=
      ( va vy wcel cv cfv cima cmpt cvv wceq wf ccnv csn cuni cid cres w3a wf1o
      wa wfo wf1 ccom wex simpr mptexd setpreimafvex adantl wfun ffun funimaexg
      sylan resiexd 3jca wfn fveq2 sneqd imaeq2d cbvmptv fundcmpsurinjlem2 eqid
      ffn imasetpreimafvbij wi f1oi f1of1 wss fimass f1ss sylan2 ex mp2b adantr
      uniimaprimaeqfv fveq2d mpteq2dva crn funfvima2d fvresi syl eqtrd ad2antrr
      ffrn preimafvelsetpreimafv syl3anc eqidd imaeq2 unieqd fmptco dffn5 sylib
      3eqtr4rd f1of fnima eqcomd feq2d mpbird uniimaelsetpreimafv cofmpt coeq1d
      mp1i jca wb foeq1 3ad2ant1 f1oeq1 3ad2ant2 f1eq1 3ad2ant3 3anbi123d simp3
      simp2 coeq12d simp1 eqeq2d anbi12d spc3egv sylc ) CDIUAZCJNZUIZLCIUBZLOZI
      PZUCZQZRZSNZMEIMOZQZUDZRZSNZUEICQZUFZSNZUGCEYPUJZEUUCUUAUHZUUCDUUDUKZUGZI
      UUDUUAULZYPULZTZUIZCEFOZUJZEUUCGOZUHZUUCDHOZUKZUGZIUURUUPULZUUNULZTZUIZHU
      MGUMFUMYJYQUUBUUEYJLCYOJYHYIUNZUOYJMEYTSYIESNYHABCEIJKUPUQUOYJUUCSYHIURYI
      UUCSNCDIUSICJUTVAVBVCYJUUIUULYJUUFUUGUUHYHICVDZYIUUFCDIVKZABCEIYPJKLACYOY
      KAOZIPZUCZQYLUVHTZYNUVJYKUVKYMUVIYLUVHIVEVFVGVHVIVAYHUVFYIUUGUVGABCEIUUAJ
      MKUUAVJVLVAYHUUHYIUUCUUCUUDUHZUUCUUCUUDUKZYHUUHVMUUCVNZUUCUUCUUDVOUVMYHUU
      HYHUVMUUCDVPUUHCDICVQUUCUUCDUUDVRVSVTWAWBVCYJIMEYTUUDPZRZYPULZUUKYJLCIYOQ
      ZUDZUUDPZRZLCYMRZUVQIYJUWALCYMUUDPZRUWBYJLCUVTUWCYJYLCNZUIZUVSYMUUDYJUVFU
      WDUVSYMTYHUVFYIUVGWBZCIYLWCVAWDWEYJLCUWCYMUWEYMUUCNUWCYMTYJCIWFZIYLYHCUWG
      IUAYICDIWLWBWGUUCYMWHWIWEWJYJLMCEYOUVOUVTYPUVPUWEUVFYIUWDYOENYHUVFYIUWDUV
      GWKYJYIUWDUVEWBYJUWDUNABCEIJYLKWMWNYJYPWOYJUVPWOYRYOTZYTUVSUUDUWHYSUVRYRY
      OIWPWQWDWRYHIUWBTZYIYHUVFUWIUVGLCIWSWTWBXAYJUVPUUJYPYJUVFUVPUUJTUWFUVFUUJ
      UVPUVFMEYTUWGUUCUUDUVFUWGUUCUUDUAUUCUUCUUDUAZUVLUWJUVFUVNUUCUUCUUDXBXJUVF
      UWGUUCUUCUUDUVFUUCUWGCIXCXDXEXFABCEYRIKXGXHXDWIXIWJXKUVDUUMFGHYPUUAUUDSSS
      UUNYPTZUUPUUATZUURUUDTZUGZUUTUUIUVCUULUWNUUOUUFUUQUUGUUSUUHUWKUWLUUOUUFXL
      UWMCEUUNYPXMXNUWLUWKUUQUUGXLUWMEUUCUUPUUAXOXPUWMUWKUUSUUHXLUWLUUCDUURUUDX
      QXRXSUWNUVBUUKIUWNUVAUUJUUNYPUWNUURUUDUUPUUAUWKUWLUWMXTUWKUWLUWMYAYBUWKUW
      LUWMYCYBYDYEYFYG $.

    $d A f g j x $.  $d B f h j $.  $d F f j $.  $d P f j $.  $d V f g j $.
    $( Every function ` F : A --> B ` can be decomposed into a surjective
       function onto ` P ` and an injective function from ` P ` .  (Contributed
       by AV, 12-Mar-2024.)  (Proof shortened by AV, 22-Mar-2024.) $)
    fundcmpsurinjpreimafv $p |- ( ( F : A --> B /\ A e. V ) -> E. g E. h
                  ( g : A -onto-> P /\ h : P -1-1-> B /\ F = ( h o. g ) ) ) $=
      ( vf vj wcel wa cv wf1 w3a ccom wceq wex wf cima fundcmpsurbijinjpreimafv
      wfo wf1o cvv vex coex simprl1 simp3 3ad2ant2 f1co syl2anc ad2antrl simprr
      f1of1 3jca f1eq1 coeq1 eqeq2d 3anbi23d spcegv mpsyl exlimdvv eximdv mpd
      ex ) CDHUACIMNZCEFOZUDZEHCUBZKOZUEZVKDLOZPZQZHVNVLRZVIRZSZNZLTKTZFTVJEDGO
      ZPZHWBVIRZSZQZGTZFTABCDEFKLHIJUCVHWAWGFVHVTWGKLVHVTWGVQUFMVHVTNZVJEDVQPZV
      SQZWGVNVLLUGKUGUHWHVJWIVSVJVMVOVSVHUIVPWIVHVSVPVOEVKVLPZWIVJVMVOUJVMVJWKV
      OEVKVLUPUKEVKDVNVLULUMUNVHVPVSUOUQWFWJGVQUFWBVQSZWCWIWEVSVJEDWBVQURWLWDVR
      HWBVQVIUSUTVAVBVCVGVDVEVF $.
  $}

  ${
    $d A g h p x y z $.  $d B g h p x y z $.  $d F g h p x y z $.
    $d V g x y $.
    $( Every function ` F : A --> B ` can be decomposed into a surjective and
       an injective function.  (Contributed by AV, 13-Mar-2024.) $)
    fundcmpsurinj $p |- ( ( F : A --> B /\ A e. V ) -> E. g E. h E. p
                   ( g : A -onto-> p /\ h : p -1-1-> B /\ F = ( h o. g ) ) ) $=
      ( vz vx vy wcel cv wfo wf1 wceq w3a wex cfv csn cima wf wa ccom ccnv wrex
      cab cvv abrexexg adantl fveq2 sneqd eqeq2d cbvrexvw fundcmpsurinjpreimafv
      imaeq2d abbii foeq3 f1eq2 3anbi12d 2exbidv spcedv exrot3 sylib ) ABEUAZAF
      KZUBZAGLZCLZMZVGBDLZNZEVJVHUCOZPZDQCQZGQVMGQDQCQVFVNAHLZEUDZILZERZSZTZOZI
      AUEZHUFZVHMZWCBVJNZVLPZDQCQGUGWCVEWCUGKVDIHAVTFUHUIJHABWCCDEFWBVOVPJLZERZ
      SZTZOZJAUEHWAWKIJAVQWGOZVTWJVOWLVSWIVPWLVRWHVQWGEUJUKUOULUMUPUNVGWCOZVMWF
      CDWMVIWDVKWEVLVGWCAVHUQVGWCBVJURUSUTVAVMGCDVBVC $.

    $d A g h i p q x y z $.  $d B i q $.  $d F i q $.
    $( Every function ` F : A --> B ` can be decomposed into a surjective, a
       bijective and an injective function.  (Contributed by AV,
       23-Mar-2024.) $)
    fundcmpsurbijinj $p |- ( ( F : A --> B /\ A e. V )
         -> E. g E. h E. i E. p E. q ( ( g : A -onto-> p /\ h : p -1-1-onto-> q
                          /\ i : q -1-1-> B ) /\ F = ( ( i o. h ) o. g ) ) ) $=
      ( vz vy vx wcel wa cv wceq wex cima cvv wb wfo wf1o wf1 w3a ccom ccnv cfv
      wf csn wrex wfun ffun funimaexg sylan abrexexg adantl fveq2 sneqd imaeq2d
      eqeq2d cbvrexvw abbii fundcmpsurbijinjpreimafv foeq3 f1oeq23 ancoms f1eq2
      cab adantr 3anbi123d anbi1d 3exbidv spc2egv syl21anc exrot4 excom13 bitri
      imp 2exbii sylib ) ABFUHZAGMZNZAIOZCOZUAZWDHOZDOZUBZWGBEOZUCZUDZFWJWHUEWE
      UEPZNZEQZDQCQZIQHQZWNHQIQEQZDQCQZWCFARZSMZJOZFUFZKOZFUGZUIZRZPZKAUJZJVHZS
      MZAXJWEUAZXJWTWHUBZWTBWJUCZUDZWMNZEQDQCQZWQWAFUKWBXAABFULFAGUMUNWBXKWAKJA
      XGGUOUPLJABXJCDEFGXIXBXCLOZFUGZUIZRZPZLAUJJXHYBKLAXDXRPZXGYAXBYCXFXTXCYCX
      EXSXDXRFUQURUSUTVAVBVCXAXKNXQWQWPXQHIWTXJSSWGWTPZWDXJPZNZWNXPCDEYFWLXOWMY
      FWFXLWIXMWKXNYEWFXLTYDWDXJAWEVDUPYEYDWIXMTWDXJWGWTWHVEVFYDWKXNTYEWGWTBWJV
      GVIVJVKVLVMVRVNWQWOIQHQZDQCQWSWOHICDVOYGWRCDWNHIEVPVSVQVT $.
  $}

  ${
    $d A x $.  $d B x $.  $d F x $.  $d H x $.  $d I x $.
    fundcmpsurinjimaid.i $e |- I = ( F " A ) $.
    fundcmpsurinjimaid.g $e |- G = ( x e. A |-> ( F ` x ) ) $.
    fundcmpsurinjimaid.h $e |- H = ( _I |` I ) $.
    $( Every function ` F : A --> B ` can be decomposed into a surjective
       function onto the image ` ( F " A ) ` of the domain of ` F ` and an
       injective function from the image ` ( F " A ) ` .  (Contributed by AV,
       17-Mar-2024.) $)
    fundcmpsurinjimaid $p |- ( F : A --> B
                -> ( G : A -onto-> I /\ H : I -1-1-> B /\ F = ( H o. G ) ) ) $=
      ( wf wfo wf1 ccom wceq cfv cmpt eqtrid a1i ax-mp cima fimadmfo cv wfn ffn
      dffn5 sylib eqcomd eqidd foeq123d mpbird cid cres wf1o wi f1of1 wss f1eq1
      f1oi wb biimpri fimass eqsstrid f1ss syl2an ex mp2b wcel wa fveq1i adantr
      simpr fnfvimad eleqtrrdi fvresi syl mpteq2dva coeq2i feq1i mpbir 3eqtr4rd
      f1of cofmpt 3jca ) BCDKZBGELZGCFMZDFENZOWEWFBDBUAZDLBCDUBWEBBGWIEDWEEABAU
      CZDPZQZDIWEDWLWEDBUDZDWLOBCDUEZABDUFUGZUHRWEBUIGWIOWEHSUJUKGGULGUMZUNZGGW
      PMZWEWGUOGUSZGGWPUPWRWEWGWRGGFMZGCUQWGWEWTWRFWPOWTWRUTJGGFWPURTVAWEGWICHB
      CDBVBVCGGCFVDVEVFVGWEABWKFPZQZWLWHDWEABXAWKWEWJBVHZVIZXAWKWPPZWKWKFWPJVJX
      DWKGVHXEWKOXDWKWIGXDBWJBDWEWMXCWNVKWEXCVLZXFVMHVNZGWKVOVPRVQWEWHFWLNXBEWL
      FIVRWEABWKGGFGGFKZWEXHGGWPKZWQXIWSGGWPWBTGGFWPJVSVTSXGWCRWOWAWD $.
  $}

  ${
    $d A g h p y $.  $d B g h p y $.  $d F g h p y $.
    $( Alternate proof of ~ fundcmpsurinj , based on ~ fundcmpsurinjimaid :
       Every function ` F : A --> B ` can be decomposed into a surjective and
       an injective function.  (Proof modification is discouraged.)
       (New usage is discouraged.)  (Contributed by AV, 13-Mar-2024.) $)
    fundcmpsurinjALT $p |- ( ( F : A --> B /\ A e. V ) -> E. g E. h E. p
                   ( g : A -onto-> p /\ h : p -1-1-> B /\ F = ( h o. g ) ) ) $=
      ( vy wcel wa cv cvv w3a wfo wf1 ccom wceq wex eqid eqidd wf cfv cmpt cima
      cid cres mptexg wfun ffun funimaexg sylan resiexd 3jca fundcmpsurinjimaid
      adantl adantr simp1 simp3 foeq123d wb simpl simpr f1eq123d 3adant1 ancoms
      coeq12d 3adant3 eqeq2d 3anbi123d spc3egv sylc ) ABEUAZAFIZJZHAHKEUBZUCZLI
      ZUEEAUDZUFZLIZVRLIZMAVRVPNZVRBVSOZEVSVPPZQZMZAGKZCKZNZWGBDKZOZEWJWHPZQZMZ
      GRDRCRVNVQVTWAVMVQVLHAVOFUGUOVNVRLVLEUHVMWAABEUIEAFUJUKZULWOUMVLWFVMHABEV
      PVSVRVRSVPSVSSUNUPWNWFCDGVPVSVRLLLWHVPQZWJVSQZWGVRQZMZWIWBWKWCWMWEWSAAWGV
      RWHVPWPWQWRUQWSATWPWQWRURUSWQWRWKWCUTWPWQWRJZWGVRBBWJVSWQWRVAWQWRVBWTBTVC
      VDWSWLWDEWPWQWLWDQZWRWQWPXAWQWPJWJVSWHVPWQWPVAWQWPVBVFVEVGVHVIVJVK $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Partitions of real intervals
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Based on the theorems of the fourierdlem* series of GS's mathbox.

$)

  $c RePart $.

  $( Extend class notation with the partitions of a closed interval of extended
     reals. $)
  ciccp $a class RePart $.

  ${
    $d i m p $.
    $( Define partitions of a closed interval of extended reals.  Such
       partitions are finite increasing sequences of extended reals.
       (Contributed by AV, 8-Jul-2020.) $)
    df-iccp $a |- RePart = ( m e. NN |-> { p e. ( RR* ^m ( 0 ... m ) ) |
                       A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) } ) $.

    $d M i m p $.
    $( Partition consisting of a fixed number ` M ` of parts.  (Contributed by
       AV, 9-Jul-2020.) $)
    iccpval $p |- ( M e. NN -> ( RePart ` M ) = { p e. ( RR* ^m ( 0 ... M ) ) |
                       A. i e. ( 0 ..^ M ) ( p ` i ) < ( p ` ( i + 1 ) ) } ) $=
      ( vm cv cfv c1 caddc co clt wbr cc0 cfzo wral cxr cfz cmap crab cn oveq2
      ciccp wceq oveq2d raleqdv rabeqbidv df-iccp ovex rabex fvmpt ) DBAEZCEZFU
      JGHIUKFJKZALDEZMIZNZCOLUMPIZQIZRULALBMIZNZCOLBPIZQIZRSUAUMBUBZUOUSCUQVAVB
      UPUTOQUMBLPTUCVBULAUNURUMBLMTUDUEADCUFUSCVAOUTQUGUHUI $.

    $d P i p $.
    $( A special partition.  Corresponds to ~ fourierdlem2 in GS's mathbox.
       (Contributed by AV, 9-Jul-2020.) $)
    iccpart $p |- ( M e. NN -> ( P e. ( RePart ` M )
             <-> ( P e. ( RR* ^m ( 0 ... M ) )
                  /\ A. i e. ( 0 ..^ M ) ( P ` i ) < ( P ` ( i + 1 ) ) ) ) ) $=
      ( vp cn wcel ciccp cfv cv c1 caddc co clt wbr cc0 cfzo wral cxr cfz fveq1
      cmap crab wa iccpval eleq2d wceq breq12d ralbidv elrab bitrdi ) CEFZACGHZ
      FABIZDIZHZUMJKLZUNHZMNZBOCPLZQZDROCSLUALZUBZFAVAFUMAHZUPAHZMNZBUSQZUCUKUL
      VBABCDUDUEUTVFDAVAUNAUFZURVEBUSVGUOVCUQVDMUMUNATUPUNATUGUHUIUJ $.

    $d I i $.
    $( Implications for a class being a partition.  (Contributed by AV,
       11-Jul-2020.) $)
    iccpartimp $p |- ( ( M e. NN /\ P e. ( RePart ` M ) /\ I e. ( 0 ..^ M ) )
                       -> ( P e. ( RR* ^m ( 0 ... M ) )
                            /\ ( P ` I ) < ( P ` ( I + 1 ) ) ) ) $=
      ( vi cn wcel ciccp cfv cc0 cfzo co cxr cfz cmap c1 caddc clt wbr wa wi cv
      wral iccpart wceq fveq2 fvoveq1 breq12d rspccv adantl simpl biimtrdi 3imp
      jctild ) CEFZACGHFZBICJKZFZALICMKNKFZBAHZBOPKAHZQRZSZUNUOURDUAZAHZVCOPKAH
      ZQRZDUPUBZSZUQVBTADCUCVHUQVAURVGUQVATURVFVADBUPVCBUDVDUSVEUTQVCBAUEVCBOAP
      UFUGUHUIURVGUJUMUKUL $.
  $}

  ${
    $d M i $.  $d P i $.
    $( The restriction of a partition is a partition.  (Contributed by AV,
       16-Jul-2020.) $)
    iccpartres $p |- ( ( M e. NN /\ P e. ( RePart ` ( M + 1 ) ) )
                       -> ( P |` ( 0 ... M ) ) e. ( RePart ` M ) ) $=
      ( vi cn wcel c1 caddc co ciccp cfv cc0 cfz cxr clt wral wa wb syl wss wi
      cres cmap cv wbr cfzo peano2nn iccpart simpl cuz uzid peano2uz elmapssres
      nnz fzss2 syl2anr fzoss2 ssralv adantld imp wceq fzossfz a1i sselda fvres
      eqcomd simpr elfzouz adantl fzofzp1b mpbid breq12d biimpd ralimdva adantr
      cz ex impcom mpd mpbir2and sylbid ) BDEZABFGHZIJEZAKBLHZUAZBIJEZWAWCAMKWB
      LHZUBHEZCUCZAJZWIFGHZAJZNUDZCKWBUEHZOZPZWFWAWBDEWCWPQBUFACWBUGRWAWPWFWAWP
      PZWFWEMWDUBHEZWIWEJZWKWEJZNUDZCKBUEHZOZWPWHWDWGSZWRWAWHWOUHWAWBBUIJZEZXDW
      ABXEEZXFWABVOEXGBUMBUJRBBUKRZBKWBUNRAMWGWDULUOWQWMCXBOZXCWAWPXIWAWOXIWHWA
      XBWNSZWOXITWAXFXJXHBKWBUPRWMCXBWNUQRURUSWPWAXIXCTZWHWAXKTWOWHWAXKWHWAPZWM
      XACXBXLWIXBEZPZWMXAXNWJWSWLWTNXNWIWDEZWJWSUTXLXBWDWIXBWDSXLKBVAVBVCXOWSWJ
      WIWDAVDVERXNWTWLXNWKWDEZWTWLUTXNXMXPXLXMVFXNWIKUIJEZXMXPQXMXQXLWIKBVGVHKB
      WIVIRVJWKWDAVDRVEVKVLVMVPVNVQVRWAWFWRXCPQWPWECBUGVNVSVPVTUS $.
  $}

  ${
    iccpartgtprec.m $e |- ( ph -> M e. NN ) $.
    iccpartgtprec.p $e |- ( ph -> P e. ( RePart ` M ) ) $.
    ${
      $d M i $.  $d P i $.
      iccpartxr.i $e |- ( ph -> I e. ( 0 ... M ) ) $.
      $( If there is a partition, then all intermediate points and bounds are
         extended real numbers.  (Contributed by AV, 11-Jul-2020.) $)
      iccpartxr $p |- ( ph -> ( P ` I ) e. RR* ) $=
        ( vi cc0 cfz co cxr cmap wcel wf cv cfv c1 caddc syl clt wbr cfzo ciccp
        wral wa cn wb iccpart mpbid simpld elmapi ffvelcdmd ) AIDJKZLCBABLUNMKN
        ZUNLBOAUOHPZBQUPRSKBQUAUBHIDUCKUEZABDUDQNZUOUQUFZFADUGNURUSUHEBHDUITUJU
        KBLUNULTGUM $.
    $}

    ${
      iccpartgtprec.i $e |- ( ph -> I e. ( 1 ... M ) ) $.
      $( If there is a partition, then all intermediate points and the upper
         bound are strictly greater than the preceeding intermediate points or
         lower bound.  (Contributed by AV, 11-Jul-2020.) $)
      iccpartgtprec $p |- ( ph -> ( P ` ( I - 1 ) ) < ( P ` I ) ) $=
        ( c1 cmin co cfv caddc clt cc0 cfz wcel cfzo cz wb syl cxr wbr cn ciccp
        cmap wa nnzd fzval3 eleq2d mpbid cc nncnd pncan1 eqcomd oveq2d elfzelzd
        wceq peano2zd elfzom1b syl2anc bitr4d mpbird syl3anc simprd zcnd npcan1
        iccpartimp fveq2d breqtrrd ) ACHIJZBKZVJHLJZBKZCBKMABUANDOJUEJPZVKVMMUB
        ZADUCPBDUDKPVJNDQJZPZVNVOUFEFAVQCHDHLJZQJZPZACHDOJZPZVTGADRPZWBVTSADEUG
        ZWCWAVSCHDUHUITUJAVQVJNVRHIJZQJZPZVTAVPWFVJADWENQAWEDADUKPWEDUQADEULDUM
        TUNUOUIACRPVRRPVTWGSACHDGUPZADWDURCVRUSUTVAVBBVJDVGVCVDACVLBAVLCACUKPVL
        CUQACWHVECVFTUNVHVI $.
    $}

    ${
      iccpartipre.i $e |- ( ph -> I e. ( 1 ..^ M ) ) $.
      $( If there is a partition, then all intermediate points are real
         numbers.  (Contributed by AV, 11-Jul-2020.) $)
      iccpartipre $p |- ( ph -> ( P ` I ) e. RR ) $=
        ( c1 cmin co cfv cxr wcel wbr cc0 cfz cz syl sseldd iccpartxr caddc clt
        cr cuz wss cn cle w3a nnz peano2zm id zre lem1d 3jca eluz2 sylibr fzss2
        cfzo fzossfz sselid elfzoelz nnzd elfzm1b syl2anc mpbid 1eluzge0 fzoss1
        wb mp1i sstrdi fzofzp1 iccpartgtprec ciccp wa iccpartimp syl3anc simprd
        cmap xrre2 syl32anc ) ACHIJZBKZLMCBKZLMCHUAJZBKZLMWBWCUBNWCWEUBNZWCUCMA
        BWADEFAODHIJZPJZODPJZWAADWGUDKMZWHWIUEADUFMZWJEWKWGQMZDQMZWGDUGNZUHZWJW
        KWMWODUIWMWLWMWNDUJWMUKWMDDULUMUNRWGDUOUPRWGODUQRACHDPJZMZWAWHMZAHDURJZ
        WPCHDUSGUTZACQMZWMWQWRVHACWSMXAGCHDVARADEVBCDVCVDVESTABCDEFAWSWICAWSODU
        RJZWIHOUDKMWSXBUEAVFHODVGVIZODUSVJGSTABWDDEFACXBMZWDWIMAWSXBCXCGSZODCVK
        RTABCDEFWTVLABLWIVRJMZWFAWKBDVMKMXDXFWFVNEFXEBCDVOVPVQWBWCWEVSVT $.
    $}

    $d M i k $.  $d P i k $.  $d ph i k $.
    $( If there is a partition, then all intermediate points are strictly less
       than the upper bound.  (Contributed by AV, 12-Jul-2020.) $)
    iccpartiltu $p |- ( ph -> A. i e. ( 1 ..^ M ) ( P ` i ) < ( P ` M ) ) $=
      ( wcel cfv clt wbr c1 co wi wa adantr adantl cr w3a imp syl vk cn cv cfzo
      wral wceq c0 ral0 oveq2 fzo0 eqtrdi fveq2 breq2d raleqbidv mpbiri 2a1d wn
      cxr simpr ciccp cc0 cfz cn0 nnnn0 nn0fz0 sylib iccpartxr cpnf cmnf w3o cz
      elfzoelz ad2antll caddc cuz elfzo2 cle eluzelz peano2zd 3ad2ant1 simp2 wb
      elxr zltp1le sylan biimp3a eluz2 syl3anbrc sylbi eqcomd eleq1d com12 1red
      biimpcd zre syl3anc expcomd adantrd 3adant2 3ad2ant3 biimtrid 3adant3 wne
      elfz2 letr anim12ci 3adant1 ltlen nesym anbi2i bitr2di biimpd adantld jca
      expd elfzelz 1zzd elfzel2 3jca 3ad2ant2 mpbird 3exp impcom iccpartipre ex
      pm2.61i cmin cmap wss 1eluzge0 fzoss1 mp1i elfzoel2 fzoval eleq2d elfzouz
      elfzo sseld sylbid breq2 sseldd iccpartimp simprd ltpnf imbitrrid elfzofz
      smonoord elfzubelfz iccpartgtprec nnne0 df-ne bilanri nn0n0n1ge2 ige2m1fz
      eqcoms c2 nltmnf pm2.21dd 3jaoi impl ralrimiva mpcom expcom mpd ) ADUBGZC
      UCZBHZDBHZIJZCKDUDLZUEZEDKUFZAUVEUVKMZMUVLUVKAUVEUVLUVKUVGKBHZIJZCUGUEUVO
      CUHUVLUVIUVOCUVJUGUVLUVJKKUDLUGDKKUDUIKUJUKUVLUVHUVNUVGIDKBULUMUNUOUPAUVL
      UQZUVMAUVPNZUVEUVKUVHURGZUVQUVENZUVKUVSBDDUVQUVEUSZUVQBDUTHGZUVEAUWAUVPFO
      OZUVEDVADVBLZGZUVQUVEDVCGZUWDDVDZDVEVFPVGUVRUVHQGZUVHVHUFZUVHVIUFZVJZUVSU
      VKMUVHWCUWJUVSUVKUWJUVSNUVICUVJUWJUVSUVFUVJGZUVIUWGUVSUWKNZUVIMUWHUWIUWGU
      WLUVIUWGUWLNZUABUVFDUWKUVFVKGZUWGUVSUVFKDVLVMUWKDUVFKVNLZVOHGZUWGUVSUWKUV
      FKVOHGZDVKGZUVFDIJZRZUWPUVFKDVPZUWTUWOVKGZUWRUWODVQJZUWPUWQUWRUXBUWSUWQUV
      FKUVFVRZVSVTUWQUWRUWSWAUWQUWRUWSUXCUWQUWNUWRUWSUXCWBUXDUVFDWDWEWFUWODWGWH
      WIVMUAUCZDUFZUWMUXEUVFDVBLGZNZUXEBHZQGZMUXHUXFUXJUWMUXFUXJMZUXGUWGUXKUWLU
      XFUWGUXJUXFUVHUXIQUXFUXIUVHUXEDBULWJWKWNOOWLUXFUQZUXHUXJUXLUXHNBUXEDUXHUV
      EUXLUWMUVEUXGUWLUVEUWGUVSUVEUWKUVTOZPZOPUXHUWAUXLUWMUWAUXGUWLUWAUWGUVSUWA
      UWKUWBOZPZOPUXHUXLUXEUVJGZUWMUXGUXLUXQMZUWKUXGUXRMUWGUVSUWKUXGUXLUXQUWKUX
      GUXLRZUXQKUXEVQJZUXEDIJZNZUXSUXTUYAUWKUXGUXTUXLUWKUXGUXTUXGUWNUWRUXEVKGZR
      ZUVFUXEVQJZUXEDVQJZNZNZUWKUXTUXEUVFDXDZUWKUWTUYHUXTMZUXAUWQUWRUYJUWSUWQKV
      KGZUWNKUVFVQJZRUYJKUVFWGUYLUYKUYJUWNUYHUYLUXTUYDUYGUYLUXTMZUWNUYCUYGUYMMU
      WRUWNUYCNZUYEUYMUYFUYNUYLUYEUXTUYNKQGUVFQGZUXEQGZUYLUYENUXTMUYNWMUWNUYOUY
      CUVFWOOUYCUYPUWNUXEWOZPKUVFUXEXEWPWQWRWSSWLWTWIVTWIXASXBUXGUXLUYAUWKUXGUX
      LUYAUXGUYHUXLUYAMZUYIUYDUYGUYRUYDUYFUYRUYEUYDUYFUXLUYAUYDUYFUXLNZUYAUYDUY
      AUYFDUXEXCZNZUYSUYDUYPDQGZNZUYAVUAWBUWRUYCVUCUWNUWRVUBUYCUYPDWOUYQXFXGUXE
      DXHTUYTUXLUYFDUXEXIXJXKXLXOXMSWISXGXNUXSUYCUYKUWRRZUXQUYBWBUXGUWKVUDUXLUX
      GUYCUYKUWRUXEUVFDXPUXGXQUXEUVFDXRXSXTUXEKDYQTYAYBVMSYCYDYEYFUWMUXEUVFDKYG
      LZVBLZGZNZBURUWCYHLGZUXIUXEKVNLBHIJZVUHUVEUWAUXEVADUDLZGZVUIVUJNUWMUVEVUG
      UXNOUWMUWAVUGUXPOUWMVUGVULUWKVUGVULMUWGUVSUWKVUGVULUWKVUGNZUVJVUKUXEKVAVO
      HGUVJVUKYIVUMYJKVADYKYLUWKVUGUXQUWKVUGUXEUVFDUDLZGUXQUWKVUFVUNUXEUWKVUNVU
      FUWKUWRVUNVUFUFUVFKDYMUVFDYNTWJYOUWKVUNUVJUXEUWKUWQVUNUVJYIUVFKDYPUVFKDYK
      TYRYSSUUAYEVMSBUXEDUUBWPUUCUUGYEUWLUVIUWHUVGVHIJZUWLUVGQGVUOUWLBUVFDUXMUX
      OUVSUWKUSYDUVGUUDTUVHVHUVGIYTUUEUWIUWLUVIUWIUWLNZVUEBHZVIIJZUVIVUPVURVUQU
      VHIJZVUPBDDUWLUVEUWIUXMPZUWLUWAUWIUXOPZVUPUVFKDVBLZGZDVVBGUWKVVCUWIUVSUVF
      KDUUFVMUVFKDUUHTUUIUWIVURVUSWBZUWLVVDVIUVHVIUVHVUQIYTUUOOYAVUPVUQURGVURUQ
      VUPBVUEDVUTVVAVUPUWEUUPDVQJZNZVUEUWCGUWLVVFUWIUWLUWEVVEUVSUWEUWKUVEUWEUVQ
      UWFPZOUWLUWEDVAXCZDKXCZRZVVEUVSVVJUWKUVSUWEVVHVVIVVGUVEVVHUVQDUUJPUVQVVIU
      VEVVIUVPADKUUKUULOXSODUUMTXNPDUUNTVGVUQUUQTUURYEUUSUUTUVAYEWIUVBYEUVCYFUV
      D $.

    $( If there is a partition, then all intermediate points are strictly
       greater than the lower bound.  (Contributed by AV, 12-Jul-2020.) $)
    iccpartigtl $p |- ( ph -> A. i e. ( 1 ..^ M ) ( P ` 0 ) < ( P ` i ) ) $=
      ( c1 cc0 cfv clt wbr co wi wcel wa syl adantr cr adantl ad2antrl vk cv c0
      wceq cfzo wral ral0 oveq2 eqtrdi raleqdv mpbiri a1d wn cxr cn0 cfz nnnn0d
      fzo0 0elfz iccpartxr cpnf cmnf w3o elxr 0zd caddc elfzouz 0p1e1 eleqtrrdi
      cuz fveq2i fveq2 eqcomd eleq1d biimpcd ad3antrrr wne cn ciccp elfz2nn0 cz
      cle w3a elfzo2 simpl1 simpr2 nn0ge0 0red eluzelre syl3anc expcomd syl5com
      zre lelttr 3impia 3ad2ant2 imp elnnz sylanbrc nn0re expd exp31 com34 3imp
      com35 expdcom 3imp1 elfzo0 syl3anbrc ex biimtrid sylbi impcom iccpartipre
      simpr fzo1fzo0n0 exp32 expdimp pm2.61dne cmin cmap ad3antlr fzoval eleq2d
      elfzoelz wss elfzouz2 fzoss2 sseld sylbid iccpartimp simprd lbfzo0 sylibr
      smonoord ralrimiva 3jca wb breq1 mpbid 1nn0 nnnn0 nnge1 eqeltrid pm2.21dd
      a1i pnfnlt mnflt ralbidv mpbird 3jaoi mpcom expcom pm2.61i ) DGUDZAHBIZCU
      BZBIZJKZCGDUELZUFZMUUOUVAAUUOUVAUUSCUCUFUUSCUGUUOUUSCUUTUCUUOUUTGGUELUCDG
      GUEUHGURUIUJUKULAUUOUMZUVAUUPUNNZAUVBOZUVAAUVCUVBABHDEFADUONZHHDUPLZNADEU
      QDUSPUTQUVCUUPRNZUUPVAUDZUUPVBUDZVCUVDUVAMZUUPVDUVGUVJUVHUVIUVGUVDUVAUVGU
      VDOZUUSCUUTUVKUUQUUTNZOZUABHUUQUVMVEUVLUUQHGVFLZVJIZNUVKUVLUUQGVJIZUVOUUQ
      GDVGUVNGVJVHVKVISUVMUAUBZHUUQUPLNZOUVQBIZRNZUVQHUVGUVQHUDZUVTMUVDUVLUVRUW
      AUVGUVTUWAUUPUVSRUWAUVSUUPUVQHBVLVMVNVOVPUVMUVRUVQHVQZUVTUVKUVLUVRUWBOZUV
      TMZAUVLUWDMUVGUVBAUVLUWCUVTAUVLUWCOZOBUVQDADVRNZUWEEQABDVSINZUWEFQUWEUVQU
      UTNZAUWEUVQHDUELZNZUWBUWHUWCUVLUWJUVRUVLUWJMZUWBUVRUVQUONZUUQUONZUVQUUQWB
      KZWCZUWKUVQUUQVTUVLUUQUVPNZDWANZUUQDJKZWCZUWOUWJUUQGDWDUWOUWSUWJUWOUWSOZU
      WLUWFUVQDJKZUWJUWLUWMUWNUWSWEUWTUWQHDJKZUWFUWOUWPUWQUWRWFUWOUWSUXBUWMUWLU
      WSUXBMUWNUWMHUUQWBKZUWSUXBUUQWGUWPUWQUWRUXCUXBMUWPUWQOZUXCUWRUXBUXDHRNUUQ
      RNZDRNZUXCUWROUXBMUXDWHUWPUXEUWQGUUQWIQUWQUXFUWPDWMSZHUUQDWNWJWKWOWLWPWQD
      WRWSUWLUWMUWNUWSUXAUWLUWMUWSUWNUXAUWSUWLUWMUWNUXAMZUWPUWQUWRUWLUWMOZUXHMU
      WPUWQUWNUXIUWRUXAUWPUWQUXIUWNUWRUXAMZUWPUWQUXIUWNUXJMZUXDUXIOUVQRNZUXEUXF
      UXKUWLUXLUXDUWMUVQWTTUXIUXEUXDUWMUXEUWLUUQWTSSUXDUXFUXIUXGQUXLUXEUXFWCUWN
      UWRUXAUVQUUQDWNXAWJXBXCXEXDXFXCXGUVQDXHXIXJXKXLQXMUWCUWBUVLUVRUWBXOSUVQDX
      PWSSXNXQTWQXRXSUVMUVQHUUQGXTLUPLZNZOZBUNUVFYALNZUVSUVQGVFLBIJKZUXOUWFUWGU
      WJUXPUXQOUVDUWFUVGUVLUXNAUWFUVBEQYBUVDUWGUVGUVLUXNAUWGUVBFQYBUVMUXNUWJUVM
      UXNUVQHUUQUELZNUWJUVMUXMUXRUVQUVMUUQWANZUXMUXRUDUVLUXSUVKUUQGDYESUXSUXRUX
      MHUUQYCVMPYDUVMUXRUWIUVQUVMDUUQVJINZUXRUWIYFUVLUXTUVKUUQGDYGSUUQHDYHPYIYJ
      WQBUVQDYKWJYLYOYPXJUVHUVDUVAUVHUVDOZUUSCUUTUYAUVLOZVAUVNBIZJKZUUSUYBUUPUY
      CJKZUYDUYBUXPUYEUYBUWFUWGHUWINZWCZUXPUYEOUYAUYGUVLAUYGUVHUVBAUWFUWGUYFEFA
      UWFUYFEDYMYNYQTQBHDYKPYLUYAUYEUYDYRZUVLUVHUYHUVDUUPVAUYCJYSQQYTUYBUYCUNNU
      YDUMUYBBUVNDUYAUWFUVLAUWFUVHUVBETQUYAUWGUVLAUWGUVHUVBFTQUYAUVNUVFNZUVLAUY
      IUVHUVBAUVNGUVFVHAGUONZUVEGDWBKZWCZGUVFNAUWFUYLEUWFUYJUVEUYKUYJUWFUUAUUFD
      UUBDUUCYQPGDVTYNUUDTQUTUYCUUGPUUEYPXJUVIUVDUVAUVIUVDOZUVAVBUURJKZCUUTUFZA
      UYOUVIUVBAUYNCUUTAUVLOZUURRNUYNUYPBUUQDAUWFUVLEQAUWGUVLFQAUVLXOXNUURUUHPY
      PTUYMUUSUYNCUUTUVIUUSUYNYRUVDUUPVBUURJYSQUUIUUJXJUUKXLUULUUMUUN $.

    $( If there is a partition, then the lower bound is strictly less than the
       upper bound.  Corresponds to ~ fourierdlem11 in GS's mathbox.
       (Contributed by AV, 12-Jul-2020.) $)
    iccpartlt $p |- ( ph -> ( P ` 0 ) < ( P ` M ) ) $=
      ( vi c1 wceq cc0 cfv clt wbr wi wa co cxr wcel adantr syl iccpartxr caddc
      cfz cmap cn ciccp cfzo lbfzo0 sylibr iccpartimp simprd adantl fveq2 1e0p1
      syl3anc fveq2i eqtrdi breqtrrd ex wn wral iccpartiltu iccpartigtl 1nn a1i
      wne df-ne cle nnge1d 1red nnred ltlend biimprd mpand biimtrrid imp elfzo1
      cv syl3anbrc breq2d rspcv breq1d cn0 nnnn0 0elfz 3syl 1nn0 elfz2nn0 sylib
      nn0fz0 xrlttr expcomd syld com23 com24 mp2d com12 pm2.61i ) CGHZAIBJZCBJZ
      KLZMWRAXAWRANWSIGUAOZBJZWTKAWSXCKLZWRABPICUBOZUCOQZXDACUDQZBCUEJQZIICUFOQ
      ZXFXDNDEAXGXIDCUGUHBICUIUNUJUKWRWTXCHAWRWTGBJZXCCGBULGXBBUMUOUPRUQURAWRUS
      ZXAAFVQZBJZWTKLZFGCUFOZUTZWSXMKLZFXOUTZXKXAMABFCDEVAABFCDEVBAXKXRXPXAAXKX
      RXPXAMZMAXKNZXRWSXJKLZXSXTGXOQZXRYAMXTGUDQZXGGCKLZYBYCXTVCVDAXGXKDRZAXKYD
      XKCGVEZAYDCGVFAGCVGLZYFYDACDVHZAYDYGYFNAGCAVIACDVJVKVLVMVNVOCGVPVRZXQYAFG
      XOXLGHZXMXJWSKXLGBULZVSVTSXTXPYAXAXTXPXJWTKLZYAXAMXTYBXPYLMYIXNYLFGXOYJXM
      XJWTKYKWAVTSXTYAYLXAXTWSPQZXJPQWTPQZYAYLNXAMAYMXKABICDEAXGCWBQZIXEQDCWCZC
      WDWETRXTBGCYEAXHXKERXTGWBQZYOYGGXEQYQXTWFVDAYOXKAXGYODYPSRAYGXKYHRGCWGVRT
      AYNXKABCCDEAXGCXEQZDXGYOYRYPCWIWHSTRWSXJWTWJUNWKWLWMWLURWNWOWPWQ $.

    $( If there is a partition, then all intermediate points and the lower
       bound are strictly less than the upper bound.  (Contributed by AV,
       14-Jul-2020.) $)
    iccpartltu $p |- ( ph -> A. i e. ( 0 ..^ M ) ( P ` i ) < ( P ` M ) ) $=
      ( vk cv cfv clt wbr cc0 cfzo co wcel c1 cun cz wceq syl csn caddc w3a 0zd
      cn nnz nngt0 3jca fzopred 0p1e1 a1i oveq1d uneq2d eqtrd eleq2d wo elun wi
      elsni wa fveq2 adantr iccpartlt adantl eqbrtrd ex wral breq1d iccpartiltu
      weq rspccv syl11 jaoi com12 biimtrid sylbid ralrimiv ) ACHZBIZDBIZJKZCLDM
      NZAVRWBOVRLUAZPDMNZQZOZWAAWBWEVRAWBWCLPUBNZDMNZQZWEALROZDROZLDJKZUCZWBWIS
      ADUEOZWMEWNWJWKWLWNUDDUFDUGUHTLDUITAWHWDWCAWGPDMWGPSAUJUKULUMUNUOWFVRWCOZ
      VRWDOZUPZAWAVRWCWDUQWQAWAWOAWAURZWPWOVRLSZWRVRLUSWSAWAWSAUTVSLBIZVTJWSVSW
      TSAVRLBVAVBAWTVTJKWSABDEFVCVDVEVFTGHZBIZVTJKZGWDVGWPWAAXCWAGVRWDGCVJXBVSV
      TJXAVRBVAVHVKABGDEFVIVLVMVNVOVPVQ $.

    $( If there is a partition, then all intermediate points and the upper
       bound are strictly greater than the lower bound.  (Contributed by AV,
       14-Jul-2020.) $)
    iccpartgtl $p |- ( ph -> A. i e. ( 1 ... M ) ( P ` 0 ) < ( P ` i ) ) $=
      ( vk cc0 cfv cv clt wbr c1 co wcel wceq wo wb a1i fveq2 cfz csn cn elnnuz
      cfzo cun cuz sylib fzisfzounsn syl eleq2d elun velsn orbi2d 3bitrd wi weq
      wral breq2d rspccv iccpartigtl syl11 wa iccpartlt adantl breqtrrd ex jaoi
      adantr com12 sylbid ralrimiv ) AHBIZCJZBIZKLZCMDUANZAVNVQOZVNMDUENZOZVNDP
      ZQZVPAVRVNVSDUBZUFZOZVTVNWCOZQZWBAVQWDVNADMUGIOZVQWDPADUCOWHEDUDUHMDUIUJU
      KWEWGRAVNVSWCULSAWFWAVTWFWARACDUMSUNUOWBAVPVTAVPUPWAVMGJZBIZKLZGVSURVTVPA
      WKVPGVNVSGCUQWJVOVMKWIVNBTUSUTABGDEFVAVBWAAVPWAAVCVMDBIZVOKAVMWLKLWAABDEF
      VDVEWAVOWLPAVNDBTVIVFVGVHVJVKVL $.

    ${
      $d M j k $.  $d P i j $.  $d ph j $.
      $( If there is a partition, then all intermediate points and the bounds
         are strictly ordered.  (Contributed by AV, 18-Jul-2020.) $)
      iccpartgt $p |- ( ph -> A. i e. ( 0 ... M ) A. j e. ( 0 ... M )
                              ( i < j -> ( P ` i ) < ( P ` j ) ) ) $=
        ( vk clt wbr cfv wi cc0 co wcel c1 wceq wa cz cle cfz csn cun caddc cuz
        cv cn0 nnnn0d elnn0uz sylib fzpred syl 0p1e1 oveq1i uneq2d eqtrd eleq2d
        a1i wo elun velsn orbi1i bitri cfzo fzisfzounsn orbi2i bitrdi wne simpl
        wral simpr gt0ne0d fzo1fzo0n0 sylanbrc iccpartigtl fveq2 breq2d syl2imc
        rspcv expd impcom breq1 imbi12d imbitrrid com12 iccpartlt breqan12rd ex
        breq1d a1dd elfzelz ad3antlr w3a peano2zd ad2antlr elfzoelz ad2antrr wb
        jaoi anim12ci adantr zltp1le mpbid 3jca eluz2 sylibr ciccp 1zzd elfzle1
        cn adantl cr 1red elfzel1 zred syl3anc mpan2d syl5com syl3anbrc elfzel2
        letr imp ad4antr nnred elfzle2 elfzolt2 lelttrd elfzo2 iccpartipre cmin
        cxr cmap ad3antrrr fzoval wss elfzo0le 0le1 0red mpani sylbid ssfzo12bi
        mpd 0zd elfzoel2 mpbird eqsstrrd sselda iccpartimp smonoord exp31 com23
        jca simprd elfzuz iccpartiltu breq2 anbi2d exp4c com13 com3r ralrimivva
        3imtr4d sylbi imp32 ) ACUFZDUFZIJZUVEBKZUVFBKZIJZLZCDMEUANZUVLAUVEUVLOZ
        UVFUVLOZUVKAUVMUVEMUBZPEUANZUCZOZUVNUVKLZAUVLUVQUVEAUVLUVOMPUDNZEUANZUC
        ZUVQAEMUEKOZUVLUWBQAEUGOUWCAEFUHEUIUJZMEUKULAUWAUVPUVOUWAUVPQAUVTPEUAUM
        UNURUOUPUQUVRAUVSUVRUVEMQZUVEUVPOZUSZAUVSLUVRUVEUVOOZUWFUSUWGUVEUVOUVPU
        TUWHUWEUWFCMVAVBVCAUVNUWGUVKAUVNUVFMEVDNZOZUVFEQZUSZUWGUVKLAUVNUVFUWIEU
        BZUCZOZUWLAUVLUWNUVFAUWCUVLUWNQUWDMEVEULUQUWOUWJUVFUWMOZUSUWLUVFUWIUWMU
        TUWPUWKUWJDEVAVFVCVGUWGUWLAUVKUWEUWLAUVKLZLUWFUWLUWEUWQUWJUWEUWQLUWKUWE
        UWJUWQUWEUWJAUVKUWJARUVKUWEMUVFIJZMBKZUVIIJZLZAUWJUXAAUWJUWRUWTUWJUWRRZ
        UVFPEVDNZOZAUWSHUFZBKZIJZHUXCVJUWTUXBUWJUVFMVHUXDUWJUWRVIUXBUVFUWJUWRVK
        VLUVFEVMVNABHEFGVOUXGUWTHUVFUXCUXEUVFQUXFUVIUWSIUXEUVFBVPVQVSVRVTWAUWEU
        VGUWRUVJUWTUVEMUVFIWBUWEUVHUWSUVIIUVEMBVPZWIWCWDVTWEUWKUWEUWQUWKUWERZAU
        VJUVGAUVJUXIUWSEBKZIJABEFGWFUWEUWKUVHUWSUVIUXJIUXHUVFEBVPZWGWDWJWHWSWEU
        WLUWFUWQUWJUWFUWQLUWKUWJUWFUWQUWJUWFRZUVGAUVJUXLUVGAUVJUXLUVGRZARZHBUVE
        UVFUWFUVESOZUWJUVGAUVEPEWKZWLUXNUVEPUDNZSOZUVFSOZUXQUVFTJZWMZUVFUXQUEKO
        UXMUYAAUXMUXRUXSUXTUWFUXRUWJUVGUWFUVEUXPWNWOUWJUXSUWFUVGUVFMEWPZWQUXMUV
        GUXTUXLUVGVKZUXMUXOUXSRZUVGUXTWRUXLUYDUVGUWJUXSUWFUXOUYBUXPWTXAZUVEUVFX
        BULXCXDXAUXQUVFXEXFUXNUXEUVEUVFUANOZRZBUXEEAEXJOZUXMUYFFWOZABEXGKOZUXMU
        YFGWOUYGUXEPUEKZOZESOZUXEEIJUXEUXCOUYGPSOUXESOZPUXETJZUYLUYGXHUYFUYNUXN
        UXEUVEUVFWKZXKUXNUYFUYOUWFUYFUYOLUWJUVGAUWFPUVETJZUYFUYOUVEPEXIZUYFUYQU
        VEUXETJZUYOUXEUVEUVFXIUYFPXLOZUVEXLOZUXEXLOZUYQUYSRUYOLUYFXMUYFUVEUXEUV
        EUVFXNXOUYFUXEUYPXOZPUVEUXEYAXPXQXRWLYBPUXEXEXSUXMUYMAUYFUWFUYMUWJUVGUV
        EPEXTZWOWQUYGUXEUVFEUYFVUBUXNVUCXKUWJUVFXLOUWFUVGAUYFUWJUVFUYBXOYCUYGEU
        YIYDUYFUXEUVFTJUXNUXEUVEUVFYEXKUWJUVFEIJUWFUVGAUYFUVFMEYFYCYGUXEPEYHXSY
        IUXNUXEUVEUVFPYJNUANZOZRZBYKUVLYLNOZUXFUXEPUDNBKIJZVUGUYHUYJUXEUWIOVUHV
        UIRAUYHUXMVUFFWOAUYJUXMVUFGWOUXNVUEUWIUXEUXNVUEUVEUVFVDNZUWIUXNUXSVUJVU
        EQUWJUXSUWFUVGAUYBYMUVEUVFYNULUXMVUJUWIYOZAUXMVUKMUVETJZUVFETJZRZUXLVUN
        UVGUWJVUMUWFVULUVFEYPUWFUYQVULUYRUWFMPTJZUYQVULYQUWFMXLOUYTVUAVUOUYQRVU
        LLUWFYRUWFXMUWFUVEUXPXOMPUVEYAXPYSUUBWTXAUXMUYDMSOZUYMRZUVGVUKVUNWRUYEU
        WJVUQUWFUVGUWJVUPUYMUWJUUCUVFMEUUDUULWQUYCUVEUVFMEUUAXPUUEXAUUFUUGBUXEE
        UUHXPUUMUUIUUJUUKWHUWKUWFAUVGUVJUWKUWFARZUVEEIJZRZUVHUXJIJZVURUVGRUVJVU
        TVVALUWKVURVUSVVAAUWFVUSVVALAUWFVUSVVAUWFVUSRZUVEUXCOZAUXFUXJIJZHUXCVJV
        VAVVBUVEUYKOZUYMVUSVVCUWFVVEVUSUVEPEUUNXAUWFUYMVUSVUDXAUWFVUSVKUVEPEYHX
        SABHEFGUUOVVDVVAHUVEUXCUXEUVEQUXFUVHUXJIUXEUVEBVPWIVSVRVTWAYBURUWKUVGVU
        SVURUVFEUVEIUUPUUQUWKUVIUXJUVHIUXKVQUVBUURWSWEWSUUSYTUUTUVCWEYTUVDUVA
        $.
    $}

    $( If there is a partition, then all intermediate points and the lower and
       the upper bound are less than or equal to the upper bound.  (Contributed
       by AV, 14-Jul-2020.) $)
    iccpartleu $p |- ( ph -> A. i e. ( 0 ... M ) ( P ` i ) <_ ( P ` M ) ) $=
      ( vk cv cfv cle wbr cc0 co wcel wceq wo syl a1i adantr clt cfz csn cun cn
      cfzo cuz cn0 nnnn0 elnn0uz sylib fzisfzounsn eleq2d wb elun orbi2d 3bitrd
      velsn wi wa ciccp wss fzossfz sselda iccpartxr cxr nn0fz0 wral iccpartltu
      weq fveq2 breq1d rspccv imp xrltled expcom xrleidd adantl eqbrtrd ex jaoi
      com12 sylbid ralrimiv ) ACHZBIZDBIZJKZCLDUAMZAWDWHNZWDLDUEMZNZWDDOZPZWGAW
      IWDWJDUBZUCZNZWKWDWNNZPZWMAWHWOWDADLUFINZWHWOOADUDNZWSEWTDUGNZWSDUHZDUIUJ
      QLDUKQULWPWRUMAWDWJWNUNRAWQWLWKWQWLUMACDUQRUOUPWMAWGWKAWGURWLAWKWGAWKUSZW
      EWFXCBWDDAWTWKESABDUTINWKFSAWJWHWDWJWHVAALDVBRVCVDAWFVENWKABDDEFAWTDWHNZE
      WTXAXDXBDVFUJQVDZSAWKWEWFTKZAGHZBIZWFTKZGWJVGWKXFURABGDEFVHXIXFGWDWJGCVIX
      HWEWFTXGWDBVJVKVLQVMVNVOWLAWGWLAUSWEWFWFJWLWEWFOAWDDBVJSAWFWFJKWLAWFXEVPV
      QVRVSVTWAWBWC $.

    $( If there is a partition, then all intermediate points and the upper and
       the lower bound are greater than or equal to the lower bound.
       (Contributed by AV, 14-Jul-2020.) $)
    iccpartgel $p |- ( ph -> A. i e. ( 0 ... M ) ( P ` 0 ) <_ ( P ` i ) ) $=
      ( vk cc0 cfv cle wbr cfz co wcel wceq c1 syl a1i adantr clt cv wo csn cun
      caddc cuz cn0 nnnn0d elnn0uz sylib fzpred eleq2d elun velsn 0p1e1 orbi12d
      wb oveq1d 3bitrd wi 0elfz iccpartxr xrleidd fveq2 breq2d imbitrrid wa cxr
      ciccp wss 1nn0 fzss1 sselda wral iccpartgtl weq rspccv imp xrltled expcom
      cn jaoi com12 sylbid ralrimiv ) AHBIZCUAZBIZJKZCHDLMZAWGWJNZWGHOZWGPDLMZN
      ZUBZWIAWKWGHUCZHPUEMZDLMZUDZNZWGWPNZWGWRNZUBZWOAWJWSWGADHUFIZNZWJWSOADUGN
      ZXEADEUHZDUIUJHDUKQULWTXCUQAWGWPWRUMRAXAWLXBWNXAWLUQACHUNRAWRWMWGAWQPDLWQ
      POAUORURULUPUSWOAWIWLAWIUTWNAWIWLWFWFJKAWFABHDEFAXFHWJNXGDVAQVBZVCWLWHWFW
      FJWGHBVDVEVFAWNWIAWNVGZWFWHAWFVHNWNXHSXIBWGDADWANWNESABDVIINWNFSAWMWJWGAP
      XDNZWMWJVJAPUGNZXJXKAVKRPUIUJPHDVLQVMVBAWNWFWHTKZAWFGUAZBIZTKZGWMVNWNXLUT
      ABGDEFVOXOXLGWGWMGCVPXNWHWFTXMWGBVDVEVQQVRVSVTWBWCWDWE $.

    $d M i p $.  $d P p $.  $d ph p $.
    $( If there is a partition, then all intermediate points and bounds are
       contained in a closed interval of extended reals.  (Contributed by AV,
       14-Jul-2020.) $)
    iccpartrn $p |- ( ph -> ran P C_ ( ( P ` 0 ) [,] ( P ` M ) ) ) $=
      ( vi vk cc0 cfv co cv wcel wb cxr wbr wral wa syl adantr cle vp cicc wceq
      crn cfz wrex wfn ciccp cmap c1 caddc clt cfzo cn iccpart elmapfn biimtrdi
      mpd fvelrnb simpr iccpartxr iccpartgel weq fveq2 breq2d rspcva expcom imp
      wi iccpartleu breq1d w3a cn0 nnnn0 0elfz 3syl nn0fz0 jca elicc1 mpbir3and
      sylib eleq1 syl5ibcom rexlimdva sylbid ssrdv ) AUABUDZHBIZCBIZUBJZAUAKZWG
      LZFKZBIZWKUCZFHCUEJZUFZWKWJLZABWPUGZWLWQMABCUHILZWSEAWTBNWPUIJLZWNWMUJUKJ
      BIULOFHCUMJPZQZWSACUNLZWTXCMDBFCUORXAWSXBBNWPUPSUQURFWPWKBUSRAWOWRFWPAWMW
      PLZQZWNWJLZWOWRXFXGWNNLZWHWNTOZWNWITOZXFBWMCAXDXEDSAWTXEESAXEUTVAAXEXIAWH
      GKZBIZTOZGWPPZXEXIVIABGCDEVBXEXNXIXMXIGWMWPGFVCZXLWNWHTXKWMBVDZVEVFVGRVHA
      XEXJAXLWITOZGWPPZXEXJVIABGCDEVJXEXRXJXQXJGWMWPXOXLWNWITXPVKVFVGRVHXFWHNLZ
      WINLZQZXGXHXIXJVLMAYAXEAXSXTABHCDEAXDCVMLZHWPLDCVNZCVOVPVAABCCDEAXDCWPLZD
      XDYBYDYCCVQWARVAVRSWHWIWNVSRVTWNWKWJWBWCWDWEWF $.

    $( The range of the partition is between its starting point and its ending
       point.  Corresponds to ~ fourierdlem15 in GS's mathbox.  (Contributed by
       Glauco Siliprandi, 11-Dec-2019.)  (Revised by AV, 14-Jul-2020.) $)
    iccpartf $p |- ( ph -> P : ( 0 ... M ) --> ( ( P ` 0 ) [,] ( P ` M ) ) ) $=
      ( vi cc0 cfz co wfn crn cfv cicc wss wf cn wcel ciccp cxr cmap cv clt wbr
      c1 caddc cfzo wral wa iccpart elmapfn adantr biimtrdi sylc iccpartrn df-f
      sylanbrc ) ABGCHIZJZBKGBLCBLMIZNUQUSBOACPQZBCRLQZURDEUTVABSUQTIQZFUAZBLVC
      UDUEIBLUBUCFGCUFIUGZUHURBFCUIVBURVDBSUQUJUKULUMABCDEUNUQUSBUOUP $.

    $( If there is a partition, then all intermediate points and bounds are
       contained in a closed interval of extended reals.  (Contributed by AV,
       14-Jul-2020.) $)
    iccpartel $p |- ( ( ph /\ I e. ( 0 ... M ) )
                      -> ( P ` I ) e. ( ( P ` 0 ) [,] ( P ` M ) ) ) $=
      ( cc0 cfz co cfv cicc iccpartf ffvelcdmda ) AGDHIGBJDBJKICBABDEFLM $.
  $}

  ${
    $d M i p x $.  $d X i p x y $.
    $( An element of any partitioned half-open interval of extended reals is an
       element of a part of this partition.  (Contributed by AV,
       18-Jul-2020.) $)
    iccelpart $p |- ( M e. NN -> A. p e. ( RePart ` M )
                           ( X e. ( ( p ` 0 ) [,) ( p ` M ) )
                             -> E. i e. ( 0 ..^ M )
                                X e. ( ( p ` i ) [,) ( p ` ( i + 1 ) ) ) ) ) $=
      ( cc0 cfv cico co wcel c1 cfzo wi ciccp fveq2 eleq2d syl adantr cvv csb
      wa vx vy cv caddc wrex wral csn oveq2d oveq2 fzo01 eqtrdi rexeqdv imbi12d
      wceq raleqbidv weq cn0 wb 0nn0 fv0p1e1 oveq12d rexsng ax-mp biimpri rgenw
      nfv nfra1 nfan cle wbr nnnn0 fzonn0p1 ad2antrr fvoveq1 adantl cxr clt w3a
      peano2nn simpr cfz nnnn0d 0elfz iccpartxr nn0fz0 sylib jca adantlr elico1
      cn simp1 simpl simpr3 3jca ex sylbid impr fzelp1 ad2ant2r mpbird rspcedvd
      exp43 wn cres iccpartres rspsbca vex resex sbcimg sbcel2 csbov12g csbfv12
      csbvarg csbconstg fveq12d eqtrid eqtrd bitrid sbcrex rexbidv bitrd simpr2
      xrltnle syl2anr exbiri com23 imp31 eqcomd biimpa elfzofz fzofzp1 rexbidva
      wsbc fvres wss cz cuz nnz uzid com24 peano2uz fzoss2 ssrexv embantd com34
      4syl syld com13 sylbi mpcom imp pm2.61d ralrimi nnind ) CEDUCZFZUAUCZUUOF
      ZGHZIZCAUCZUUOFZUVAJUDHZUUOFZGHZIZAEUUQKHZUEZLZDUUQMFZUFCUUPJUUOFZGHZIZUV
      FAEUGZUEZLZDJMFZUFCUUPUBUCZUUOFZGHZIZUVFAEUVRKHZUEZLZDUVRMFZUFZCUUPUVRJUD
      HZUUOFZGHZIZUVFAEUWGKHZUEZLZDUWGMFZUFZCUUPBUUOFZGHZIZUVFAEBKHZUEZLZDBMFZU
      FUAUBBUUQJUNZUVIUVPDUVJUVQUUQJMNUXCUUTUVMUVHUVOUXCUUSUVLCUXCUURUVKUUPGUUQ
      JUUONUHOUXCUVFAUVGUVNUXCUVGEJKHUVNUUQJEKUIUJUKULUMUOUAUBUPZUVIUWDDUVJUWEU
      UQUVRMNUXDUUTUWAUVHUWCUXDUUSUVTCUXDUURUVSUUPGUUQUVRUUONUHOUXDUVFAUVGUWBUU
      QUVREKUIULUMUOUUQUWGUNZUVIUWMDUVJUWNUUQUWGMNUXEUUTUWJUVHUWLUXEUUSUWICUXEU
      URUWHUUPGUUQUWGUUONUHOUXEUVFAUVGUWKUUQUWGEKUIULUMUOUUQBUNZUVIUXADUVJUXBUU
      QBMNUXFUUTUWRUVHUWTUXFUUSUWQCUXFUURUWPUUPGUUQBUUONUHOUXFUVFAUVGUWSUUQBEKU
      IULUMUOUVPDUVQUVOUVMEUQIUVOUVMURUSUVFUVMAEUQUVAEUNZUVEUVLCUXGUVBUUPUVDUVK
      GUVAEUUONUUOUVAUTVAOVBVCVDVEUVRWJIZUWFUWOUXHUWFTZUWMDUWNUXHUWFDUXHDVFUWDD
      UWEVGVHUXIUVSCVIVJZUUOUWNIZUWMLZUXHUXJUXLLUWFUXHUXJUXKUWJUWLUXHUXJTZUXKUW
      JTZTZUVFCUVSUWHGHZIZAUVRUWKUXHUVRUWKIZUXJUXNUXHUVRUQIZUXRUVRVKZUVRVLPVMAU
      BUPZUVFUXQURUXOUYAUVEUXPCUYAUVBUVSUVDUWHGUVAUVRUUONUVAUVRJUUOUDVNVAOVOUXO
      UXQCVPIZUXJCUWHVQVJZVRZUXMUXKUWJUYDUXMUXKTZUWJUYBUUPCVIVJZUYCVRZUYDUYEUUP
      VPIZUWHVPIZTZUWJUYGURZUXHUXKUYJUXJUXHUXKTZUYHUYIUYLUUOEUWGUXHUWGWJIUXKUVR
      VSZQZUXHUXKVTZUXHEEUWGWAHZIZUXKUXHUWGUQIZUYQUXHUWGUYMWBZUWGWCPQWDZUYLUUOU
      WGUWGUYNUYOUXHUWGUYPIZUXKUXHUYRVUAUYSUWGWEWFQWDZWGZWHUUPUWHCWIZPUXMUYGUYD
      LZUXKUXJVUEUXHUXJUYGUYDUXJUYGTUYBUXJUYCUYGUYBUXJUYBUYFUYCWKZVOUXJUYGWLUXJ
      UYBUYFUYCWMWNWOVOQWPWQUXOUVSVPIZUYITZUXQUYDURUXHUXKVUHUXJUWJUYLVUGUYIUYLU
      UOUVRUWGUYNUYOUXHUVRUYPIZUXKUXHUVREUVRWAHZIZVUIUXHUXSVUKUXTUVRWEWFZUVREUV
      RWRPQWDZVUBWGWSUVSUWHCWIPWTXAXBQUXHUWFUXJXCZUXLLUXHUXKVUNUWFUWMUXHUXKVUNU
      WFUWMLLZUUOVUJXDZUWEIZUYLVUOUUOUVRXEVUQUWFVUNUYLUWMVUQUWFVUNUYLUWMLLZVUQU
      WFTUWDDVUPYMZVURUWDDVUPUWEXFVUSCEVUPFZUVRVUPFZGHZIZCUVAVUPFZUVCVUPFZGHZIZ
      AUWBUEZLZVURVUPRIZVUSVVIURUUOVUJDXGXHVVJVUSUWADVUPYMZUWCDVUPYMZLVVIUWAUWC
      DVUPRXIVVJVVKVVCVVLVVHVVKCDVUPUVTSZIVVJVVCDVUPCUVTXJVVJVVMVVBCVVJVVMDVUPU
      UPSZDVUPUVSSZGHVVBDVUPUUPUVSGRXKVVJVVNVUTVVOVVAGVVJVVNDVUPESZDVUPUUOSZFVU
      TDVUPEUUOXLVVJVVPEVVQVUPDVUPRXMZDVUPERXNXOXPVVJVVODVUPUVRSZVVQFVVADVUPUVR
      UUOXLVVJVVSUVRVVQVUPVVRDVUPUVRRXNXOXPVAXQOXRVVLUVFDVUPYMZAUWBUEVVJVVHUVFD
      AVUPUWBXSVVJVVTVVGAUWBVVTCDVUPUVESZIVVJVVGDVUPCUVEXJVVJVWAVVFCVVJVWADVUPU
      VBSZDVUPUVDSZGHVVFDVUPUVBUVDGRXKVVJVWBVVDVWCVVEGVVJVWBDVUPUVASZVVQFVVDDVU
      PUVAUUOXLVVJVWDUVAVVQVUPVVRDVUPUVARXNXOXPVVJVWCDVUPUVCSZVVQFVVEDVUPUVCUUO
      XLVVJVWEUVCVVQVUPVVRDVUPUVCRXNXOXPVAXQOXRXTXRUMYAVCUYLVUNVVIUWMUYLVUNUWJV
      VIUWLUYLVUNUWJVVIUWLLZLUYLVUNTZUWJUWAVWFVWGUWJUYGUWAUYLUYKVUNUYLUYJUYKVUC
      VUDPQVWGUYGUWAVWGUYGTZUWAUYBUYFCUVSVQVJZVRZVWHUYBUYFVWIUYGUYBVWGVUFVOVWGU
      YBUYFUYCYBUYLVUNUYGVWIUYLUYGVUNVWIUYLUYGVWIVUNUYGUYBVUGVWIVUNURUYLVUFVUMC
      UVSYCYDYEYFYGWNVWHUYHVUGTZUWAVWJURUYLVWKVUNUYGUYLUYHVUGUYTVUMWGVMUUPUVSCW
      IPWTWOWPUYLUWAVWFLVUNUYLUWAVWFUYLUWATZVVCVVHUWLUYLUWAVVCUYLUVTVVBCUYLUUPV
      UTUVSVVAGUYLVUTUUPUYLEVUJIZVUTUUPUNUXHVWMUXKUXHUXSVWMUXTUVRWCPQEVUJUUOYNP
      YHUYLVVAUVSUYLVUKVVAUVSUNUXHVUKUXKVULQUVRVUJUUOYNPYHVAOYIVWLVVHUWCUWLVWLV
      VGUVFAUWBVWLUVAUWBIZTZVVFUVECVWOVVDUVBVVEUVDGVWOUVAVUJIZVVDUVBUNVWNVWPVWL
      UVAEUVRYJVOUVAVUJUUOYNPUYLVWNVVEUVDUNZUWAUYLVWNTUVCVUJIZVWQVWNVWRUYLEUVRU
      VAYKVOUVCVUJUUOYNPWHVAOYLVWLUWBUWKYOZUWCUWLLUXHVWSUXKUWAUXHUVRYPIUVRUVRYQ
      FZIUWGVWTIVWSUVRYRUVRYSUVRUVRUUAUVREUWGUUBUUFVMUVFAUWBUWKUUCPWPUUDWOQUUGW
      OUUEUUHUUIPWOYTUUJWOYTUUKUULUUMWOUUN $.
  $}

  ${
    $d M i j k p $.  $d P i j k p $.  $d X i p $.  $d M i p x $.  $d P x $.
    $d ph i j k $.  $d ph x $.
    iccpartiun.m $e |- ( ph -> M e. NN ) $.
    iccpartiun.p $e |- ( ph -> P e. ( RePart ` M ) ) $.
    $( A half-open interval of extended reals is the union of the parts of its
       partition.  (Contributed by AV, 18-Jul-2020.) $)
    iccpartiun $p |- ( ph -> ( ( P ` 0 ) [,) ( P ` M ) )
                 = U_ i e. ( 0 ..^ M ) ( ( P ` i ) [,) ( P ` ( i + 1 ) ) ) ) $=
      ( vp vj vk cc0 cfv cico co cv wcel wi wral fveq1 cle wbr vx cfzo c1 caddc
      ciun wrex ciccp cn iccelpart oveq12d eleq2d rexbidv imbi12d rspcva expcom
      wceq 3syl mpd wa cxr wss cn0 cfz nnnn0 iccpartxr nn0fz0 biimpi jca adantr
      0elfz elfzofz iccpartgel fveq2 breq2d syl2anr fzofzp1 iccpartleu icossico
      weq breq1d syl12anc sseld rexlimdva impbid eliun bitr4di eqrdv ) AUAJBKZD
      BKZLMZCJDUBMZCNZBKZWLUCUDMZBKZLMZUEZAUANZWJOZWRWPOZCWKUFZWRWQOAWSXAABDUGK
      ZOZWSXAPZFADUHOZWRJGNZKZDXFKZLMZOZWRWLXFKZWNXFKZLMZOZCWKUFZPZGXBQZXCXDPEC
      DWRGUIXCXQXDXPXDGBXBXFBUPZXJWSXOXAXRXIWJWRXRXGWHXHWILJXFBRDXFBRUJUKXRXNWT
      CWKXRXMWPWRXRXKWMXLWOLWLXFBRWNXFBRUJUKULUMUNUOUQURAWTWSCWKAWLWKOZUSZWPWJW
      RXTWHUTOZWIUTOZUSZWHWMSTZWOWISTZWPWJVAAYCXSAYAYBABJDEFAXEDVBOZJJDVCMZOEDV
      DZDVJUQVEABDDEFAXEYFDYGOZEYHYFYIDVFVGUQVEVHVIXSWLYGOWHHNZBKZSTZHYGQYDAWLJ
      DVKABHDEFVLYLYDHWLYGHCVSYKWMWHSYJWLBVMVNUNVOXSWNYGOINZBKZWISTZIYGQYEAJDWL
      VPABIDEFVQYOYEIWNYGYMWNUPYNWOWISYMWNBVMVTUNVOWHWIWMWOVRWAWBWCWDCWRWKWPWEW
      FWG $.

    $d I i j $.  $d J j $.
    $( Lemma for ~ icceuelpart .  (Contributed by AV, 19-Jul-2020.) $)
    icceuelpartlem $p |- ( ph -> ( ( I e. ( 0 ..^ M ) /\ J e. ( 0 ..^ M ) )
                          -> ( I < J -> ( P ` ( I + 1 ) ) <_ ( P ` J ) ) ) ) $=
      ( vi vj cc0 co wcel wa clt wbr cfv wceq wi adantr adantl cfzo c1 caddc wo
      cle fveq2 olcd a1d wn cz elfzoelz wne zltp1le biimpcd impcom df-ne sylbb1
      necom jca cr wb peano2z zred zre anim12i ltlen syl mpbird syl2an cfz wral
      ex iccpartgt fzofzp1 elfzofz breq1 breq1d imbi12d breq2 breq2d mpan9 syld
      cv rspc2v expdimp orcd pm2.61i cxr cn ciccp iccpartxr xrleloe exp31 ) ACJ
      EUAKZLZDWNLZMZCDNOZCUBUCKZBPZDBPZUEOZAWQMZWRMZXBWTXANOZWTXAQZUDZWSDQZXDXG
      RXHXGXDXHXFXEWSDBUFUGUHXHUIZXDXGXIXDMXEXFXDXIXEXCWRXIXEXCWRXIMZWSDNOZXEWQ
      XJXKRZAWOCUJLZDUJLZXLWPCJEUKDJEUKXMXNMZXJXKXOXJMZXKWSDUEOZDWSULZMZXPXQXRX
      JXOXQWRXOXQRXIXOWRXQCDUMUNSUOXJXRXOXIXRWRWSDULXIXRWSDUPWSDURUQTTUSXPWSUTL
      ZDUTLZMZXKXSVAXOYBXJXMXTXNYAXMWSCVBVCDVDVESWSDVFVGVHVLVITAHWCZIWCZNOZYCBP
      ZYDBPZNOZRZIJEVJKZVKHYJVKZWQXKXERZABHIEFGVMWOWSYJLZDYJLZYKYLRWPJECVNZDJEV
      OZYIYLWSYDNOZWTYGNOZRHIWSDYJYJYCWSQZYEYQYHYRYCWSYDNVPYSYFWTYGNYCWSBUFVQVR
      YDDQZYQXKYRXEYDDWSNVSYTYGXAWTNYDDBUFVTVRWDVIWAWBWEUOWFVLWGXDWTWHLZXAWHLZM
      ZXBXGVAXCUUCWRXCUUAUUBXCBWSEAEWILWQFSZABEWJPLWQGSZWQYMAWOYMWPYOSTWKXCBDEU
      UDUUEWQYNAWPYNWOYPTTWKUSSWTXAWLVGVHWM $.

    $d X j $.
    $( An element of a partitioned half-open interval of extended reals is an
       element of exactly one part of the partition.  (Contributed by AV,
       19-Jul-2020.) $)
    icceuelpart $p |- ( ( ph /\ X e. ( ( P ` 0 ) [,) ( P ` M ) ) )
                       -> E! i e. ( 0 ..^ M )
                          X e. ( ( P ` i ) [,) ( P ` ( i + 1 ) ) ) ) $=
      ( vj cc0 cfv cico co wcel wa wi adantr com12 cxr wbr adantl vp cv c1 cfzo
      caddc wrex weq wral wreu ciccp cn iccelpart syl wceq fveq1 oveq12d eleq2d
      rexbidv imbi12d rspcva adantld mp2and cle clt w3a cfz elfzofz fzofzp1 jca
      iccpartxr adantrr elico1 adantrl anbi12d w3o elfzoelz zred anim12i lttri4
      wb cr icceuelpartlem imp31 wn simpl nltle2tri syl3anc pm2.21d 3expd com23
      com25 imp4b 3adant3 3ad2ant3 imp syldan expcom 2a1 ancomsd 3ad2ant2 3jaoi
      ex 3adant2 mpcom sylbid ralrimivva fveq2 fvoveq1 reu4 sylanbrc ) AEIBJZDB
      JZKLZMZNZECUBZBJZXPUCUELZBJZKLZMZCIDUDLZUFZYAEHUBZBJZYDUCUELZBJZKLZMZNZCH
      UGZOZHYBUHCYBUHZYACYBUIXOBDUJJZMZEIUAUBZJZDYPJZKLZMZEXPYPJZXRYPJZKLZMZCYB
      UFZOZUAYNUHZYCAYOXNGPAUUGXNADUKMZUUGFCDEUAULUMPYOUUGNZXOYCUUIXNYCAUUFXNYC
      OUABYNYPBUNZYTXNUUEYCUUJYSXMEUUJYQXKYRXLKIYPBUODYPBUOUPUQUUJUUDYACYBUUJUU
      CXTEUUJUUAXQUUBXSKXPYPBUOXRYPBUOUPUQURUSUTVAQVBAYMXNAYLCHYBYBAXPYBMZYDYBM
      ZNZNZYJERMZXQEVCSZEXSVDSZVEZUUOYEEVCSZEYGVDSZVEZNZYKUUNYAUURYIUVAUUNXQRMZ
      XSRMZNZYAUURVTAUUKUVEUULAUUKNZUVCUVDUVFBXPDAUUHUUKFPZAYOUUKGPZUUKXPIDVFLZ
      MAXPIDVGTVJZUVFBXRDUVGUVHUUKXRUVIMAIDXPVHTVJZVIVKXQXSEVLUMUUNYERMZYGRMZNZ
      YIUVAVTAUULUVNUUKAUULNZUVLUVMUVOBYDDAUUHUULFPZAYOUULGPZUULYDUVIMAYDIDVGTV
      JZUVOBYFDUVPUVQUULYFUVIMAIDYDVHTVJZVIVMYEYGEVLUMVNXPYDVDSZYKYDXPVDSZVOZUU
      NUVBYKOZUUNXPWAMZYDWAMZNZUWBUUMUWFAUUKUWDUULUWEUUKXPXPIDVPVQUULYDYDIDVPVQ
      VRTXPYDVSUMUVTUUNUWCOYKUWAUUNUVTUWCUUNUVTXSYEVCSZUWCAUUMUVTUWGABXPYDDFGWB
      WCUVBUUNUWGNZYKUURUVAUWHYKOZUUQUUOUVAUWIOUUPUVAUUQUWIUUOUUSUUQUWIOUUTUUOU
      USNUWHUUQYKUUOUUSUUNUWGUUQYKOUUOUUQUUNUWGUUSYKUUOUUNUUQUWGUUSYKOOZUUOUUNU
      UQUWJOUUOUUNNZUUQUWGUUSYKUWKUUQUWGUUSVEZYKUWKUUOUVDUVLUWLWDUUOUUNWEZUUNUV
      DUUOAUUKUVDUULUVKVKTUUNUVLUUOAUULUVLUUKUVRVMTEXSYEWFWGWHWIXBWJWKWLWJWMQWN
      WOQWPWQYKUUNUVBWRUUNUWAUWCUUNUWAYGXQVCSZUWCAUUMUWAUWNAUULUUKUWAUWNOABYDXP
      DFGWBWSWCUVBUUNUWNNZYKUURUVAUWOYKOZUUPUUOUVAUWPOUUQUVAUUPUWPUUOUUTUUPUWPO
      UUSUUOUUTNUWOUUPYKUUOUUTUUNUWNUUPYKOZUUOUUNUUTUWNUWQOZUUOUUNUUTUWROUWKUUT
      UWNUUPYKUWKUUTUWNUUPVEZYKUWKUUOUVMUVCUWSWDUWMUUNUVMUUOAUULUVMUUKUVSVMTUUN
      UVCUUOAUUKUVCUULUVJVKTEYGXQWFWGWHWIXBWJWLWJXCQWTWOQWPWQXAXDXEXFPYAYICHYBY
      KXTYHEYKXQYEXSYGKXPYDBXGXPYDUCBUEXHUPUQXIXJ $.

    $d ph p $.
    $( The segments of a partitioned half-open interval of extended reals are a
       disjoint collection.  (Contributed by AV, 19-Jul-2020.) $)
    iccpartdisj $p |- ( ph -> Disj_ i e. ( 0 ..^ M )
                                    ( ( P ` i ) [,) ( P ` ( i + 1 ) ) ) ) $=
      ( vp vj cv cfv co cico wcel cc0 wi cxr cle wbr adantr ex c1 cfzo wrmo wal
      caddc wdisj wrex wreu nfv nfreu1 wa simpl wss cn ciccp cfz cn0 nnnn0 3syl
      0elfz iccpartxr nn0fz0 biimpi wral iccpartgel elfzofz adantl fveq2 breq2d
      wceq rspcv syl mpid imp iccpartleu fzofzp1 breq1d icossico syl22anc sseld
      icceuelpart syl6an rexlimd rmo5 sylibr alrimiv df-disj ) AGIZCIZBJZWIUAUE
      KZBJZLKZMZCNDUBKZUCZGUDCWOWMUFAWPGAWNCWOUGWNCWOUHZOWPAWNWQCWOACUIWNCWOUJA
      WIWOMZWNWQOAWRUKZAWNWHNBJZDBJZLKZMWQAWRULWSWMXBWHWSWTPMXAPMWTWJQRZWLXAQRZ
      WMXBUMWSBNDADUNMZWRESZABDUOJMWRFSZANNDUPKZMZWRAXEDUQMZXIEDURZDUTUSSVAWSBD
      DXFXGADXHMZWRAXEXJXLEXKXJXLDVBVCUSSVAAWRXCAWRWTHIZBJZQRZHXHVDZXCABHDEFVEA
      WRXPXCOZWSWIXHMZXQWRXRAWINDVFVGXOXCHWIXHXMWIVJXNWJWTQXMWIBVHVIVKVLTVMVNAW
      RXDAWRXNXAQRZHXHVDZXDABHDEFVOAWRXTXDOZWSWKXHMZYAWRYBANDWIVPVGXSXDHWKXHXMW
      KVJXNWLXAQXMWKBVHVQVKVLTVMVNWTXAWJWLVRVSVTABCDWHEFWAWBTWCWNCWOWDWEWFCGWOW
      MWGWE $.
  $}

  ${
    $d I i k x $.  $d M i k x $.  $d P i k x $.  $d X x $.  $d ph i k x $.
    iccpartnel.m $e |- ( ph -> M e. NN ) $.
    iccpartnel.p $e |- ( ph -> P e. ( RePart ` M ) ) $.
    iccpartnel.x $e |- ( ph -> X e. ran P ) $.
    $( A point of a partition is not an element of any open interval determined
       by the partition.  Corresponds to ~ fourierdlem12 in GS's mathbox.
       (Contributed by Glauco Siliprandi, 11-Dec-2019.)  (Revised by AV,
       8-Jul-2020.) $)
    iccpartnel $p |- ( ( ph /\ I e. ( 0 ..^ M ) )
                       -> -. X e. ( ( P ` I ) (,) ( P ` ( I + 1 ) ) ) ) $=
      ( vi cfv wcel wa wi clt wbr wb adantr mpd ex com12 vx vk c1 caddc co cioo
      cc0 cfzo wn cxr w3a elioo3g wceq cfz wrex crn wfn ciccp cmap wral iccpart
      cv cn syl elmapfn biimtrdi fvelrnb mpbid cle elfzelz zred adantl elfzoelz
      wo cr lelttric syl2an breq2 breq1 anbi12d leloe iccpartgt simpr weq fveq2
      elfzofz breq1d imbi12d breq2d rspc2v pm3.35 iccpartxr simp1 xrltle sylibd
      syl2anr xrlenlt com13 imp pm2.21d xrltnr 3ad2ant1 sylbid jaoi com23 com14
      a1d biimtrrdi impd com24 cz zltp1le peano2zd bitrd fzofzp1 simp2 xrltnsym
      expcom expd 3ad2ant2 rexlimdva sylbi ax-1 pm2.61i ) ECBJZCUCUDUEZBJZUFUEK
      ZACUGDUHUEZKZLZYHUIZMZYHYEUJKZYGUJKZEUJKZUKZYEENOZEYGNOZLZLZYMYEYGEULYKUU
      AYLAYJUUAYLMZAUAVBZBJZEUMZUAUGDUNUEZUOZYJUUBMZAEBUPKZUUGHABUUFUQZUUIUUGPA
      BDURJKZUUJGAUUKBUJUUFUSUEKZIVBZBJZUUMUCUDUEBJNOIYIUTZLZUUJADVCKZUUKUUPPFB
      IDVAVDUULUUJUUOBUJUUFVEQVFRUAUUFEBVGVDVHAUUEUUHUAUUFAUUCUUFKZLZYJUUEUUBUU
      SYJUUEUUBMZUUSYJLZUUCCVIOZCUUCNOZVNZUUTUUSUUCVOKZCVOKZUVDYJUURUVEAUURUUCU
      UCUGDVJZVKVLZYJCCUGDVMZVKZUUCCVPVQUVDUVAUUTUVBUVAUUTMUVCUVBUUAUUEUVAYLUVB
      YQYTUUEUVAYLMZMZUVBYTYQUVLUUEYTYQUVBUVKUUEYTYEUUDNOZUUDYGNOZLZYQUVBUVKMMZ
      UUEUVMYRUVNYSUUDEYENVRUUDEYGNVSVTZUVMUVPUVNUVAYQUVBUVMYLUVAUVBYQUVMYLMZUV
      AUVBUUCCNOZUUCCUMZVNZYQUVRMZUUSUVEUVFUVBUWAPYJUVHUVJUUCCWAVQUWAUVAUWBUVSU
      VAUWBMZUVTUVAUVSUWBUVAUVSUUDYENOZMZUVSUWBMUVAUUMUBVBZNOZUUNUWFBJZNOZMZUBU
      UFUTIUUFUTZUWEUUSUWKYJAUWKUURABIUBDFGWBQQZUUSUURCUUFKUWKUWEMYJAUURWCZCUGD
      WFUWJUWEUUCUWFNOZUUDUWHNOZMIUBUUCCUUFUUFIUAWDZUWGUWNUWIUWOUUMUUCUWFNVSUWP
      UUNUUDUWHNUUMUUCBWEWGWHUWFCUMZUWNUVSUWOUWDUWFCUUCNVRUWQUWHYEUUDNUWFCBWEWI
      WHWJVQRUVSUWEUVAUWBUVSUWEUWCUVSUWELUWDUWCUVSUWDWKUWDUVAUWBUWDUVALZYQUVRUW
      RYQLUVMYLUWRYQUVMUIZUWDUVAYQUWSMYQUVAUWDUWSYQUVAUWDUWSMYQUVALUWDUUDYEVIOZ
      UWSUVAUUDUJKZYNUWDUWTMYQUUSUXAYJUUSBUUCDAUUQUURFQAUUKUURGQUWMWLQZYNYOYPWM
      ZUUDYEWNWPUVAUXAYNUWTUWSPYQUXBUXCUUDYEWQWPWOSWRWSWSWTSSVDSWRRTUVTUWBUVAUV
      TYQUVRUVTYQLZUVMYEYENOZYLUVTUVMUXEPYQUVTUUDYEYENUUCCBWEWIQUXDUXEYLYQUXEUI
      ZUVTYNYOUXFYPYEXAXBVLWTXCSXGXDTXCXEXFQXHXFXEXIXJUVCUUAUUEUVAYLUVCYQYTUVLU
      VCYTYQUVLUUEYTYQUVCUVKUUEYTUVOYQUVCUVKMMUVQUVAYQUVCUVOYLUVAUVCYQUVOYLMZUV
      AUVCYFUUCNOZYFUUCUMZVNZYQUXGMZUVAUVCYFUUCVIOZUXJYJCXKKUUCXKKZUVCUXLPUUSUV
      IUURUXMAUVGVLCUUCXLWPYJYFVOKUVEUXLUXJPUUSYJYFYJCUVIXMVKUVHYFUUCWAWPXNUXJU
      VAUXKUXHUVAUXKMZUXIUVAUXHUXKUVAUXHYGUUDNOZMZUXHUXKMUVAUWKUXPUWLYJYFUUFKUU
      RUWKUXPMUUSUGDCXOUWMUWJUXPYFUWFNOZYGUWHNOZMIUBYFUUCUUFUUFUUMYFUMZUWGUXQUW
      IUXRUUMYFUWFNVSUXSUUNYGUWHNUUMYFBWEWGWHUBUAWDZUXQUXHUXRUXOUWFUUCYFNVRUXTU
      WHUUDYGNUWFUUCBWEWIWHWJWPRUXHUXPUVAUXKUXHUXPUXNUXHUXPLUXOUXNUXHUXOWKUVOUV
      AYQUXOYLUVNUVAYQUXOYLMZMMUVMUVNUVAYQUYAUVAYQLZUVNUYAUYBUVNLUXOYLUYBUVNUXO
      UIZUVAUXAYOUVNUYCMYQUXBYNYOYPXPUUDYGXQVQWSWTXRXSVLXFVDSWRRTUXIUXKUVAUXIUV
      OYQYLUXIUVOYEYGNOZYGYGNOZLYQYLMZUXIUYDUVMUYEUVNUXIYGUUDYENYFUUCBWEZWIUXIY
      GUUDYGNUYGWGVTUYEUYFUYDYQUYEYLYQUYEYLYOYNUYEUIYPYGXAXTWTTVLXHXEXGXDTXCXEX
      FXHXFXEXIXJXDTRSXEYARWSTYBYLYKYCYD $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Shifting functions with an integer range domain
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d F x $.  $d E x $.  $d X x $.
    fargshift.g $e |- G = ( x e. ( 0 ..^ ( # ` F ) ) |-> ( F ` ( x + 1 ) ) ) $.
    $( If a class is a function, then the values of the "shifted function"
       correspond to the function values of the class.  (Contributed by
       Alexander van der Vekens, 23-Nov-2017.) $)
    fargshiftfv $p |- ( ( N e. NN0 /\ F : ( 1 ... N ) --> dom E )
                  -> ( X e. ( 0 ..^ N ) -> ( G ` X ) = ( F ` ( X + 1 ) ) ) ) $=
      ( cn0 wcel c1 cfz co cdm wa cc0 cfzo cfv caddc wceq cvv wfn ffn fseq1hash
      wf chash wi oveq2 eqcoms eleq2d biimpd syl sylan2 imp fvex fvoveq1 fvmptg
      cv sylancl ex ) EHIZJEKLZBMZCUDZNZFOEPLZIZFDQFJRLZCQZSZVDVFNFOCUEQZPLZIZV
      HTIVIVDVFVLVCUTCVAUAZVFVLUFZVAVBCUBUTVMNVJESZVNCEUCVOVFVLVOVEVKFVEVKSEVJE
      VJOPUGUHUIUJUKULUMVGCUNAFAUQZJRLCQVHVKTDVPFJCRUOGUPURUS $.

    $( If a class is a function, then also its "shifted function" is a
       function.  (Contributed by Alexander van der Vekens, 23-Nov-2017.) $)
    fargshiftf $p |- ( ( N e. NN0 /\ F : ( 1 ... N ) --> dom E )
                     -> G : ( 0 ..^ ( # ` F ) ) --> dom E ) $=
      ( cn0 wcel c1 cfz co cdm wf wa cv caddc cfv cc0 chash wceq cfzo fseq1hash
      wfn ffn sylan2 wb eleq1 oveq2 feq2d anbi12d eqcoms wi fz0add1fz1 ffvelcdm
      wral expcom syl impancom ralrimiv biimtrdi mpcom fmpt sylib ) EGHZIEJKZBL
      ZCMZNZAOZIPKZCQZVFHZARCSQZUAKZUOZVNVFDMVMETZVHVOVGVDCVEUCVPVEVFCUDCEUBUEV
      PVHVMGHZIVMJKZVFCMZNZVOVHVTUFEVMEVMTZVDVQVGVSEVMGUGWAVEVRVFCEVMIJUHUIUJUK
      VTVLAVNVQVIVNHZVSVLVQWBNVJVRHZVSVLULVMVIUMVSWCVLVRVFVJCUNUPUQURUSUTVAAVNV
      FVKDFVBVC $.

    $d F k l x y z $.  $d E y z $.  $d G y z $.
    $( If a function is 1-1, then also the shifted function is 1-1.
       (Contributed by Alexander van der Vekens, 23-Nov-2017.) $)
    fargshiftf1 $p |- ( ( N e. NN0 /\ F : ( 1 ... N ) -1-1-> dom E )
                     -> G : ( 0 ..^ ( # ` F ) ) -1-1-> dom E ) $=
      ( vy vz vk vl wcel c1 co wa cfv wceq wi adantl adantr impcom cn0 cfz cfzo
      cdm wf1 cc0 chash wf cv weq f1f fargshiftf sylan2 wfn ffn fseq1hash eleq1
      wral wb oveq2 f1eq2 anbi12d dff13 caddc fz0add1fz1 anim12dan fveq2 eqeq1d
      syl eqeq1 imbi12d eqeq2d eqeq2 rspc2v fargshiftfv expcom com13 eqeq12d cc
      w3a elfzoelz zcnd 1cnd 3jca addcan2 imbi2d biimpa sylbid syld exp31 com24
      ex imp mpd ralrimdvv sylbi biimtrrdi mpcom sylanbrc ) EUAKZLEUBMZBUDZCUEZ
      NZUFCUGOZUCMZXBDUHZGUIZDOZHUIZDOZPZGHUJZQZHXFURGXFURZXFXBDUEXCWTXAXBCUHZX
      GXAXBCUKZABCDEFULUMXEEPZXDXOXCWTXPXRXQXPWTCXAUNXRXAXBCUOCEUPUMUMXRXDXEUAK
      ZLXEUBMZXBCUEZNXOXRXSWTYAXCXEEUAUQXRXTXAPYAXCUSXEELUBUTXTXAXBCVAVIVBYAXSX
      OYAXTXBCUHZIUIZCOZJUIZCOZPZIJUJZQZJXTURIXTURZNZXSXOQIJXTXBCVCYKXSXNGHXFXF
      XHXFKZXJXFKZNZXSYKXNXSYNYKXNQZXSYNNZXHLVDMZXTKZXJLVDMZXTKZNZYOXSYLYRYMYTX
      EXHVEXEXJVEVFYKUUAYPXNYBYJUUAYPXNQQYBYPUUAYJXNYBYPUUAYJXNQYBYPNZUUANZYJYQ
      COZYSCOZPZYQYSPZQZXNUUAYJUUHQUUBYIUUHUUDYFPZYQYEPZQIJYQYSXTXTYCYQPZYGUUIY
      HUUJUUKYDUUDYFYCYQCVGVHYCYQYEVJVKYEYSPZUUIUUFUUJUUGUULYFUUEUUDYEYSCVGVLYE
      YSYQVMVKVNRUUCUUHXNUUCUUHNXLUUFXMUUCXLUUFUSZUUHUUBUUMUUAUUBXIUUDXKUUEYPYB
      XIUUDPZYNXSYBUUNQZYLXSUUOQYMYBXSYLUUNXSYBYLUUNQABCDXEXHFVOVPVQSTTYPYBXKUU
      EPZYNXSYBUUPQZYMXSUUQQYLYBXSYMUUPXSYBYMUUPQABCDXEXJFVOVPVQRTTVRSSUUCUUHUU
      FXMQUUCUUGXMUUFUUCXHVSKZXJVSKZLVSKZVTZUUGXMUSUUBUVAUUAYPUVAYBYPUURUUSUUTY
      NUURXSYLUURYMYLXHXHUFXEWAWBSRYNUUSXSYMUUSYLYMXJXJUFXEWAWBRRYPWCWDRSXHXJLW
      EVIWFWGWHWLWIWJWKWMVQWNVPVQWOWPTWQWRGHXFXBDVCWS $.

    $d N x y z $.
    $( If a function is onto, then also the shifted function is onto.
       (Contributed by Alexander van der Vekens, 24-Nov-2017.) $)
    fargshiftfo $p |- ( ( N e. NN0 /\ F : ( 1 ... N ) -onto-> dom E )
                     -> G : ( 0 ..^ ( # ` F ) ) -onto-> dom E ) $=
      ( vy vz wcel c1 co wa cc0 cfv cfzo wceq sylan2 caddc adantl wb cn0 cfz wf
      cdm wfo chash crn fof fargshiftf cv wrex cab rnmpt wfn fofn fnrnfv syl wi
      df-fo bilani eqeq1 eqcom bitrdi ffn fseq1hash fz0add1fz1 cmin nn0z fzval3
      cz nn0cn 1cnd addcomd oveq2d eqtrd eleq2d biimpa adantr fzosubel3 syl2anc
      oveq1 eqeq2d cc elfzelz zcnd npcand eqcomd rspcedvd fveq2 rexxfrd rexeqdv
      oveq2 bibi2d mpbird syldan abbidv eqeq1d biimpcd biimtrdi com23 mpcom mpd
      eqtrid dffo2 sylanbrc ) EUAIZJEUBKZBUDZCUEZLZMCUFNZOKZXHDUCZDUGZXHPXLXHDU
      EXIXFXGXHCUCZXMXGXHCUHZABCDEFUIQXJXNGUJZAUJZJRKZCNZPZAXLUKZGULZXHAGXLXTDF
      UMXJCUGZXQHUJZCNZPZHXGUKZGULZPZYCXHPZXIYJXFXICXGUNZYJXGXHCUOHGXGCUPUQSYLY
      DXHPZLZXJYJYKURZXIYNXFXGXHCUSUTYMXJYOURYLYMYJXJYKYMYJYIXHPZXJYKURYMYJXHYI
      PYPYDXHYIVAXHYIVBVCXJYPYKXJYIYCXHXJYHYBGXFXIXKEPZYHYBTZXIXFXOYQXPXOXFYLYQ
      XGXHCVDCEVEQQXFYQLYRYHYAAMEOKZUKZTZXFUUAYQXFYGYAHAXSXGYSEXRVFXFYEXGIZLZYE
      XSPZYEYEJVGKZJRKZPZAUUEYSUUCYEJJERKZOKZIZEVJIZUUEYSIXFUUBUUJXFXGUUIYEXFXG
      JEJRKZOKZUUIXFUUKXGUUMPEVHZJEVIUQXFUULUUHJOXFEJEVKXFVLVMVNVOVPVQXFUUKUUBU
      UNVRYEJEVSVTXRUUEPZUUDUUGTUUCUUOXSUUFYEXRUUEJRWAWBSUUCUUFYEUUCYEJUUBYEWCI
      XFUUBYEYEJEWDWESUUCVLWFWGWHUUDYGYATXFUUDYFXTXQYEXSCWIWBSWJVRYQYRUUATXFYQY
      BYTYHYQYAAXLYSXKEMOWLWKWMSWNWOWPWQWRWSWTSXAXBXCXLXHDXDXE $.

    $d E k $.  $d G k $.  $d N k $.  $d P k $.  $d E l $.  $d N l $.  $d P l $.
    $( The values of a shifted function correspond to the value of the original
       function.  (Contributed by Alexander van der Vekens, 24-Nov-2017.) $)
    fargshiftfva $p |- ( ( N e. NN0 /\ F : ( 1 ... N ) --> dom E )
      -> ( A. k e. ( 1 ... N ) ( E ` ( F ` k ) ) = [_ k / x ]_ P
        -> A. l e. ( 0 ..^ N ) ( E ` ( G ` l ) ) = [_ ( l + 1 ) / x ]_ P ) ) $=
      ( wcel c1 co wa cv cfv csb wceq wral wi ex cn0 cfz cdm wf cfzo fz0add1fz1
      caddc cc0 simpl adantr 2fveq3 csbeq1 eqeq12d adantl anim1i simpr ad3antlr
      wb fargshiftfv imp eqcomd syl2anc fveqeq2d bitrd rspcdv com23 com24 imp31
      mpancom ralrimiv ) GUAJZKGUBLZDUCEUDZMZCNZEODOZAVOBPZQZCVLRZHNZFOZDOAVTKU
      GLZBPZQZHUHGUELZRVNVSMWDHWEVKVMVSVTWEJZWDSVKWFVSVMWDVKWFVSVMWDSSZWBVLJZVK
      WFMZWGGVTUFWHWIMZVMVSWDWJVMVSWDSWJVMMZVRWDCWBVLWJWHVMWHWIUIUJWKVOWBQZMZVR
      WBEOZDOZWCQZWDWLVRWPURWKWLVPWOVQWCVOWBDEUKAVOWBBULUMUNWMWNWAWCDWMVNWFWNWA
      QWKVNWLWJVKVMWIVKWHVKWFUIUNUOUJWIWFWHVMWLVKWFUPUQVNWFMWAWNVNWFWAWNQADEFGV
      TIUSUTVAVBVCVDVETVFVITVGVHVJT $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Words over a set (extension)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Last symbol of a word - extension
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( The last symbol of a nonempty word exists.  The empty set must be excluded
     as symbol, because otherwise, it cannot be distinguished between valid
     cases ( ` (/) ` is the last symbol) and invalid cases ( ` (/) ` means that
     no last symbol exists).  This is because of the special definition of a
     function in set.mm.  (Contributed by Alexander van der Vekens,
     18-Mar-2018.) $)
  lswn0 $p |- ( ( W e. Word V /\ (/) e/ V /\ ( # ` W ) =/= 0 )
                  -> ( lastS ` W ) =/= (/) ) $=
    ( cword wcel c0 wnel chash cfv cc0 wne w3a clsw c1 cmin co wceq wi wa com12
    cn0 lsw 3ad2ant1 cfzo wrdf lencl simpll clt wbr elnnne0 biimpri nnm1nn0 syl
    wf cn nn0re adantr elfzo0 syl3anbrc adantll ffvelcdmd syl2anc eleq1a eqcoms
    ltm1d ex wn nnel imbitrrdi necon2ad syl6 com23 3imp eqnetrd ) BACZDZEAFZBGH
    ZIJZKBLHZVQMNOZBHZEVOVPVSWAPVRBVNUAUBVOVPVRWAEJZVOVRVPWBVOVRWAADZVPWBQVOIVQ
    UCOZABUMZVQTDZVRWCQABUDABUEWEWFRZVRWCWGVRRWDAVTBWEWFVRUFWFVRVTWDDZWEWFVRRZV
    TTDZVQUNDZVTVQUGUHZWHWIWKWJWKWIVQUIUJZVQUKULWMWFWLVRWFVQVQUOVDUPVTVQUQURUSU
    TVEVAWCVPWAEWCWAEPZEADZVPVFWNWCWOWCWOQEWAWCEWAPWOWAAEVBSVCSEAVGVHVIVJVKVLVM
    $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Unordered pairs
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Interchangeable setvar variables
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c <> $.

  $( Extend wff notation to include the property of a wff ` ph ` that the
     setvar variables ` x ` and ` y ` are interchangeable.  Read this notation
     as " ` x ` and ` y ` are interchangeable in wff ` ph ` ". $)
  wich $a wff [ x <> y ] ph $.

  ${
    $d a ph $.  $d a x $.  $d a y $.
    $( Define the property of a wff ` ph ` that the setvar variables ` x ` and
       ` y ` are interchangeable.  For an alternate definition using implicit
       substitution and a temporary setvar variable see ~ ichcircshi .
       Another, equivalent definition using two temporary setvar variables is
       provided in ~ dfich2 .  (Contributed by AV, 29-Jul-2023.) $)
    df-ich $a |- ( [ x <> y ] ph <-> A. x A. y
                               ( [ x / a ] [ y / x ] [ a / y ] ph <-> ph ) ) $.
  $}

  ${
    $d a y $.  $d a x $.  $d a ph $.
    $( The first interchangeable setvar variable is not free.  (Contributed by
       AV, 21-Aug-2023.) $)
    nfich1 $p |- F/ x [ x <> y ] ph $=
      ( va wich wsb wb wal df-ich nfa1 nfxfr ) ABCEACDFBCFDBFAGCHZBHBABCDILBJK
      $.

    $( The second interchangeable setvar variable is not free.  (Contributed by
       AV, 21-Aug-2023.) $)
    nfich2 $p |- F/ y [ x <> y ] ph $=
      ( va wich wsb wb wal df-ich nfa2 nfxfr ) ABCEACDFBCFDBFAGZCHBHCABCDILCBJK
      $.
  $}

  ${
    $d a x ph $.  $d a y ph $.
    $( Setvar variables are interchangeable in a wff they do not appear in.
       (Contributed by SN, 23-Nov-2023.) $)
    ichv $p |- [ x <> y ] ph $=
      ( va wich wsb wb wal sbv sbbii bitri gen2 df-ich mpbir ) ABCEACDFZBCFZDBF
      ZAGZCHBHRBCQADBFAPADBPABCFAOABCACDIJABCIKJADBIKLABCDMN $.
  $}

  ${
    $d a x $.  $d a y $.  $d a ph $.
    ichf.1 $e |- F/ x ph $.
    ichf.2 $e |- F/ y ph $.
    $( Setvar variables are interchangeable in a wff they are not free in.
       (Contributed by SN, 23-Nov-2023.) $)
    ichf $p |- [ x <> y ] ph $=
      ( va wich wsb wb wal sbf sbbii bitri sbv gen2 df-ich mpbir ) ABCGACFHZBCH
      ZFBHZAIZCJBJUABCTAFBHASAFBSABCHARABCACFEKLABCDKMLAFBNMOABCFPQ $.
  $}

  ${
    $d a ph $.  $d a x $.
    $( A setvar variable is always interchangeable with itself.  (Contributed
       by AV, 29-Jul-2023.) $)
    ichid $p |- [ x <> x ] ph $=
      ( va wich wsb wb wal sbid sbbii sbid2vw bitri gen2 df-ich mpbir ) ABBDABC
      EZBBEZCBEZAFZBGBGRBBQOCBEAPOCBOBHIACBJKLABBCMN $.
  $}

  ${
    $d a x $.  $d a y $.  $d a ph $.
    icht.1 $e |- ph $.
    $( A theorem is interchangeable.  (Contributed by SN, 4-May-2024.) $)
    icht $p |- [ x <> y ] ph $=
      ( va wich wsb wb wal sbt 2th gen2 df-ich mpbir ) ABCFACEGZBCGZEBGZAHZCIBI
      RBCQAPEBOBCACEDJJJDKLABCEMN $.
  $}

  ${
    $d a x ph $.  $d a y ph $.  $d a ps $.  $d a ch $.
    ichbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula building rule for interchangeability (deduction).  (Contributed
       by SN, 4-May-2024.) $)
    ichbidv $p |- ( ph -> ( [ x <> y ] ps <-> [ x <> y ] ch ) ) $=
      ( va wsb wb wal wich sbbidv bibi12d albidv df-ich 3bitr4g ) ABEGHZDEHZGDH
      ZBIZEJZDJCEGHZDEHZGDHZCIZEJZDJBDEKCDEKAUAUFDATUEEASUDBCARUCGDAQUBDEABCEGF
      LLLFMNNBDEGOCDEGOP $.
  $}

  ${
    $d z ph $.  $d x ps $.  $d y ch $.  $d x y z $.
    ichcircshi.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    ichcircshi.2 $e |- ( y = x -> ( ps <-> ch ) ) $.
    ichcircshi.3 $e |- ( z = y -> ( ch <-> ph ) ) $.
    $( The setvar variables are interchangeable if they can be circularily
       shifted using a third setvar variable, using implicit substitution.
       (Contributed by AV, 29-Jul-2023.) $)
    ichcircshi $p |- [ x <> y ] ph $=
      ( wich wsb wb wal weq bicomd equcoms sbievw 2sbbii sbbii 3bitri df-ich
      gen2 mpbir ) ADEJAEFKZDEKFDKZALZEMDMUFDEUECDEKZFDKBFDKAUDCFDEDACEFACLFEFE
      NCAIOPQRUGBFDCBDECBLEDEDNBCHOPQSBAFDBALDFDFNABGOPQTUBADEFUAUC $.
  $}

  ${
    $d ph x $.  $d ps x $.  $d a x $.  $d b x $.
    $( If two setvar variables are interchangeable in two wffs, then they are
       interchangeable in the conjunction of these two wffs.  Notice that the
       reverse implication is not necessarily true.  Corresponding theorems
       will hold for other commutative operations, too.  (Contributed by AV,
       31-Jul-2023.)  Use ~ df-ich instead of ~ dfich2 to reduce axioms.
       (Revised by SN, 4-May-2024.) $)
    ichan $p |- ( ( [ a <> b ] ph /\ [ a <> b ] ps )
                  -> [ a <> b ] ( ph /\ ps ) ) $=
      ( vx wsb wb wal wa wich sbbii 3bitri pm4.38 bitrid alanimi df-ich anbi12i
      sban 3imtr4i ) ADEFZCDFZECFZAGZDHZCHZBDEFZCDFZECFZBGZDHZCHZIABIZDEFZCDFZE
      CFZULGZDHZCHACDJZBCDJZIULCDJUDUJUQCUCUIUPDUOUBUHIZUCUIIULUOTUFIZCDFZECFUA
      UGIZECFUTUNVBECUMVACDABDERKKVBVCECTUFCDRKUAUGECRLUBUHABMNOOURUEUSUKACDEPB
      CDEPQULCDEPS $.
  $}

  ${
    $d a u $.  $d b u $.  $d ph u $.
    $( Negation does not affect interchangeability.  (Contributed by SN,
       30-Aug-2023.) $)
    ichn $p |- ( [ a <> b ] ph <-> [ a <> b ] -. ph ) $=
      ( vu wsb wb wal wn wich notbi sbn sbbii bitri bibi1i bitr4i 2albii df-ich
      3bitr4i ) ACDEZBCEZDBEZAFZCGBGAHZCDEZBCEZDBEZUCFZCGBGABCIUCBCIUBUGBCUBUAH
      ZUCFUGUAAJUFUHUCUFTHZDBEUHUEUIDBUESHZBCEUIUDUJBCACDKLSBCKMLTDBKMNOPABCDQU
      CBCDQR $.
  $}

  $( Formula building rule for implication in interchangeability.  (Contributed
     by SN, 4-May-2024.) $)
  ichim $p |- ( ( [ a <> b ] ph /\ [ a <> b ] ps )
                                       -> [ a <> b ] ( ph -> ps ) ) $=
    ( wich wa wn wi ichn ichan sylan2b sylib wtru iman a1i ichbidv mptru sylibr
    wb ) ACDEZBCDEZFZABGZFZGZCDEZABHZCDEZUBUDCDEZUFUATUCCDEUIBCDIAUCCDJKUDCDILU
    HUFSMUGUECDUGUESMABNOPQR $.

  ${
    $d a b ph $.  $d z ph $.  $d a b x y $.  $d x y z $.
    $( Alternate definition of the property of a wff ` ph ` that the setvar
       variables ` x ` and ` y ` are interchangeable.  (Contributed by AV and
       WL, 6-Aug-2023.) $)
    dfich2 $p |- ( [ x <> y ] ph <-> A. a A. b
                   ( [ a / x ] [ b / y ] ph <-> [ b / x ] [ a / y ] ph ) ) $=
      ( vz wich wsb wb df-ich nfs1v nfsbv sbbib albii sbco4 bibi1i 2albii bitri
      wal nfv alcom 3bitr3i ) ABCGACFHBCHFBHZAIZCSBSZACEHZBDHZACDHZBEHIESZDSZAB
      CFJUGEBHZDCHZAIZCSZBSUKUHIZDSZBSZUEUJUNUPBUKADCUGEBCUFBDCACEKLLADTMNUMUDB
      CULUCAABCFEDOPQUQUOBSZDSUJUOBDUAURUIDUGUHEBUFBDKUHETMNRUBR $.
  $}

  ${
    $d a b x y $.  $d ps a b $.
    $( The interchangeability of setvar variables is commutative.  (Contributed
       by AV, 20-Aug-2023.) $)
    ichcom $p |- ( [ x <> y ] ps <-> [ y <> x ] ps ) $=
      ( va vb wsb wb wal wich alcom sbcom2 bibi12i 2albii bitri dfich2 3bitr4i
      ) ACDFBEFZACEFBDFZGZDHEHZABEFCDFZABDFCEFZGZEHDHZABCIACBITSEHDHUDSEDJSUCDE
      QUARUBACDBEKACEBDKLMNABCEDOACBDEOP $.
  $}

  ${
    $d a b u v ps $.  $d u v x y ch $.  $d a b x y $.
    ichbi12i.1 $e |- ( ( x = a /\ y = b ) -> ( ps <-> ch ) ) $.
    $( Equivalence for interchangeable setvar variables.  (Contributed by AV,
       29-Jul-2023.) $)
    ichbi12i $p |- ( [ x <> y ] ps <-> [ a <> b ] ch ) $=
      ( vv vu wsb wb wal wich nfv sbco2v sbbii sbcom2 bitri nfsbv 2sbbii bicomi
      2sbievw 3bitr3i 3bitr3ri bibi12i 2albii dfich2 3bitr4i ) ADHJZCIJZADIJZCH
      JZKZHLILBFHJEIJZBFIJEHJZKZHLILACDMBEFMUMUPIHUJUNULUOUICEJZEIJADFJZCEJZFHJ
      ZEIJUJUNUQUTEIUQURFHJZCEJUTUIVACEVAUIADHFAFNZOUAPURFHCEQRPUICIEADHEAENZSO
      USBEFHIABCDFEGUBZTUCUSFIJZEHJUKCEJZEHJUOULVEVFEHVEURFIJZCEJVFURCEFIQVGUKC
      EADIFVBOPRPUSBEFIHVDTUKCHEADIEVCSOUDUEUFACDIHUGBEFIHUGUH $.
  $}

  $( In an equality for the same setvar variable, the setvar variable is
     interchangeable by itself.  Special case of ~ ichid and ~ icheq without
     distinct variables restriction.  (Contributed by AV, 29-Jul-2023.) $)
  icheqid $p |- [ x <> x ] x = x $=
    ( weq ichid ) AABAC $.

  ${
    $d x y z $.
    $( In an equality of setvar variables, the setvar variables are
       interchangeable.  (Contributed by AV, 29-Jul-2023.) $)
    icheq $p |- [ x <> y ] x = y $=
      ( vz weq wich wsb wb equsb3r 2sbbii equsb3 sbbii equcom bitri 3bitri gen2
      wal df-ich mpbir ) ABDZABESBCFZABFCAFZSGZBPAPUBABUAACDZABFZCAFBCDZCAFZSTU
      CCABABCAHIUDUECAABCJKUFBADSCABHBALMNOSABCQR $.
  $}

  ${
    $d b x y $.
    $( Lemma for ~ ichnfim :  A substitution for a nonfree variable has no
       effect.  (Contributed by Wolf Lammen, 6-Aug-2023.)  Avoid ~ ax-13 .
       (Revised by GG, 1-May-2024.) $)
    ichnfimlem $p |- ( A. y F/ x ph
                       -> ( [ a / x ] [ b / y ] ph <-> [ b / y ] ph ) ) $=
      ( wnf wal wsb wb weq nfa1 sb6 a1i biimpri axc4i biimtrdi nf5d nfim1 nfal
      wi sbequ12 imbi2d equsalv bicomi nfv nfnf1 sp nfim nfxfr pm5.5 mpbii sbft
      nfbidf syl ) ABFZCGZACEHZBFZUQBDHUQIUPUPUQTZBFURUSCEJZUPATZTZCGZBVCUSVAUS
      CEUPUQCUOCKZUPUQCVDUPUQUTATZCGZUQCGUQVFIUPACELZMVEUQCUQVFVGNOPQRUTAUQUPAC
      EUAUBUCUDVBBCUTVABUTBUEUPABUOBCABUFSZUOCUGRUHSUIUPUSUQBVHUPUQUJUMUKUQBDUL
      UN $.
  $}

  ${
    $d a b x y $.  $d a b ph $.
    $( If in an interchangeability context ` x ` is not free in ` ph ` , the
       same holds for ` y ` .  (Contributed by Wolf Lammen, 6-Aug-2023.)
       (Revised by AV, 23-Sep-2023.) $)
    ichnfim $p |- ( ( A. y F/ x ph /\ [ x <> y ] ph ) -> A. x F/ y ph ) $=
      ( va vb wnf wal wich nfnf1 nfal nfich1 nfan wsb dfich2 ichnfimlem bibi12d
      wa wb bicom1 biimtrdi 2alimdv biimtrid imp sbnf2 sylibr alrimi ) ABFZCGZA
      BCHZQZACFZBUHUIBUGBCABIJABCKLUJACDMZACEMZRZEGDGZUKUHUIUOUIUMBDMZULBEMZRZE
      GDGUHUOABCDENUHURUNDEUHURUMULRUNUHUPUMUQULABCDEOABCEDOPUMULSTUAUBUCACDEUD
      UEUF $.
  $}

  ${
    $d x y $.
    $( If ` x ` and ` y ` are interchangeable in ` ph ` , they are both free or
       both not free in ` ph ` .  (Contributed by Wolf Lammen, 6-Aug-2023.)
       (Revised by AV, 23-Sep-2023.) $)
    ichnfb $p |- ( [ x <> y ] ph -> ( A. x F/ y ph <-> A. y F/ x ph ) ) $=
      ( wich wnf wal ichcom ichnfim sylan2b expcom impbid ) ABCDZACEBFZABECFZML
      NLMACBDNABCGACBHIJNLMABCHJK $.
  $}

  ${
    $d a u x $.  $d b u x $.  $d ph u $.
    $( Move a universal quantifier inside interchangeability.  (Contributed by
       SN, 30-Aug-2023.) $)
    ichal $p |- ( A. x [ a <> b ] ph -> [ a <> b ] A. x ph ) $=
      ( vu wsb wal wich ax-11 alimi sbal 2sbbii sbbii 3bitri albi bitrid 2alimi
      wb 3syl df-ich albii 3imtr4i ) ADEFZCDFZECFZARZDGZCGZBGZABGZDEFZCDFECFZUJ
      RZDGCGZACDHZBGUJCDHUIUGBGZCGUFBGZDGZCGUNUGBCIUPURCUFBDIJUQUMCDULUEBGZUQUJ
      ULUCBGZCDFZECFUDBGZECFUSUKUTECDCABDEKLVAVBECUCBCDKMUDBECKNUEABOPQSUOUHBAC
      DETUAUJCDETUB $.
  $}

  $( Two setvar variables are always interchangeable when there are two
     universal quantifiers.  (Contributed by SN, 23-Nov-2023.) $)
  ich2al $p |- [ x <> y ] A. x A. y ph $=
    ( wal nfa1 nfa2 ichf ) ACDZBDBCHBEACBFG $.

  $( Two setvar variables are always interchangeable when there are two
     existential quantifiers.  (Contributed by SN, 23-Nov-2023.) $)
  ich2ex $p |- [ x <> y ] E. x E. y ph $=
    ( wex nfe1 excom nfxfr ichf ) ACDZBDZBCIBEJABDZCDCABCFKCEGH $.

  ${
    $d a b c t $.
    $( Example for interchangeable setvar variables in a statement of predicate
       calculus with equality.  (Contributed by AV, 31-Jul-2023.) $)
    ichexmpl1 $p |- [ a <> b ] E. a E. b E. c
                               ( a = b /\ a =/= c /\ b =/= c ) $=
      ( vt weq cv wne w3a wex wb equequ1 neeq1 3anbi12d 2exbidv cbvexvw equequ2
      a1i 3anbi13d exbidv bitri exbii 3ancomb equcom 3anbi1i 3exbii ichcircshi
      excom ) ABEZAFZCFZGZBFZUJGZHZCIBIZAIZDBEZDFZUJGZUMHZCIZBIZDIZDAEZUSUKHZCI
      ZAIZDIZABDUPVCJADEZUOVBADVIUNUTBCVIUHUQUKUSUMADBKUIURUJLMNOQVCVHJBAEZVBVG
      DVAVFBAVJUTVECVJUQVDUMUKUSBADPULUIUJLRSOUAQVHUPJUQVHVJUMUKHZCIZAIZBIZUPVG
      VMDBUQVEVKACUQVDVJUSUMUKDBAKURULUJLMNOVNVLBIAIUPVLBAUGVKUNABCVKVJUKUMHUNV
      JUMUKUBVJUHUKUMBAUCUDTUETTQUF $.
  $}

  ${
    $d a b c t $.
    $( Example for interchangeable setvar variables in an arithmetic
       expression.  (Contributed by AV, 31-Jul-2023.) $)
    ichexmpl2 $p |- [ a <> b ] ( ( a e. CC /\ b e. CC /\ c e. CC )
                     -> ( ( a ^ 2 ) + ( b ^ 2 ) ) = ( c ^ 2 ) ) $=
      ( vt cv cc wcel w3a c2 cexp co caddc wceq weq eleq1w 3anbi1d oveq1 eqeq1d
      wi imbi12d oveq1d 3anbi2d oveq2d 3ancoma imbi1i 3ad2ant2 3ad2ant1 addcomd
      sqcl pm5.74i bitri bitrdi ichcircshi ) AEZFGZBEZFGZCEZFGZHZUNIJKZUPIJKZLK
      ZURIJKZMZSZDEZFGZUQUSHZVGIJKZVBLKZVDMZSVHUOUSHZVJVALKZVDMZSZABDADNZUTVIVE
      VLVQUOVHUQUSADFOPVQVCVKVDVQVAVJVBLUNVGIJQUARTBANZVIVMVLVOVRUQUOVHUSBAFOUB
      VRVKVNVDVRVBVAVJLUPUNIJQUCRTDBNZVPUQUOUSHZVBVALKZVDMZSZVFVSVMVTVOWBVSVHUQ
      UOUSDBFOPVSVNWAVDVSVJVBVALVGUPIJQUARTWCUTWBSVFVTUTWBUQUOUSUDUEUTWBVEUTWAV
      CVDUTVBVAUQUOVBFGUSUPUIUFUOUQVAFGUSUNUIUGUHRUJUKULUM $.
  $}

  ${
    $d A a b x y $.  $d B a b x y $.  $d X a b $.  $d ph x y $.
    $( If the setvar variables are interchangeable in a wff, there is an
       ordered pair fulfilling the wff iff there is an unordered pair
       fulfilling the wff.  (Contributed by AV, 16-Jul-2023.) $)
    ich2exprop $p |- ( ( A e. X /\ B e. X /\ [ a <> b ] ph )
                     -> ( E. a E. b ( { A , B } = { a , b } /\ ph )
                      <-> E. a E. b ( <. A , B >. = <. a , b >. /\ ph ) ) ) $=
      ( vx vy wcel cv wceq wa wex cop wsbc nfv nfex wi wb cvv wich nfich1 nf3an
      w3a cpr nfcv nfsbc1v nfsbcw nfich2 wo vex mpanr12 3adant3 or2expropbilem1
      nfan preq12bg ichcom biimpi 3ad2ant3 adantr pm3.2i anim12i simpr anim12ci
      a1i opeq12 eqeq2d adantl dfsbcq sbceq1a wsb wal df-ich sbsbc sbcbii bitri
      bitr3id sylbi sylan9bbr bitrd anbi12d spc2ed sylc exp31 com23 jaod sylbid
      2sp impd exlimd or2expropbilem2 imbitrrdi oppr anim1d 2eximdv impbid ) BD
      IZCDIZAEFUAZUDZBCUEEJZFJZUEKZALZFMZEMZBCNZXAXBNKZALZFMEMZWTXFXGGJZHJZNZKZ
      AEXKOZFXLOZLZHMZGMZXJWTXEXSEWQWRWSEWQEPWREPAEFUBUCXREGXQEHXNXPEXNEPXOEFXL
      EXLUFAEXKUGUHUOQQWTXDXSFWQWRWSFWQFPWRFPAEFUIUCXRFGXQFHXNXPFXNFPXOFXLUGUOQ
      QWTXCAXSWTXCBXAKCXBKLZBXBKCXAKLZUJZAXSRZWQWRXCYBSZWSWQWRLZXATIZXBTIZYDEUK
      ZFUKZBCXAXBDDTTUPULUMWTXTYCYAWQWRXTYCRWSAGHBCDEFUNUMWTAYAXSWTAYAXSWTALZYA
      LAFEUAZYGYFLZLXGXBXANZKZALZXSYJYKYAYLWTYKAWSWQYKWRWSYKAEFUQURUSUTYLYAYGYF
      YIYHVAVEVBYJAYAYNWTAVCBCXBXAVFVDYKXQYOGHXBXATTYOGPYOHPYKXKXBKZXLXAKZLZLZX
      NYNXPAYRXNYNSYKYRXMYMXGXKXLXBXAVFVGVHYSXPXOFXAOZAYRXPYTSZYKYQUUAYPXOFXLXA
      VIVHVHYRYTYTGXBOZYKAYPYTUUBSYQYTGXBVJUTYKAEGVKZFEVKZGFVKZASZEVLFVLZUUBASA
      FEGVMUUBUUEUUGAUUEUUDGXBOUUBUUDGFVNUUDYTGXBUUDUUCFXAOYTUUCFEVNUUCXOFXAAEG
      VNVOVPVOVPUUFFEWHVQVRVSVTWAWBWCWDWEWFWGWIWJWJAGHBCEFWKWLWQWRXJXFRWSYEXIXD
      EFYEXHXCABCXAXBDDWMWNWOUMWP $.
  $}

  ${
    $d a b c d v w x y $.  $d a b v w x y p $.  $d c d v w x y ph $.
    $d p ph $.  $d X p $.  $d X c d v w x y $.
    $( If the setvar variables are interchangeable in a wff, there is never a
       unique ordered pair with different components fulfilling the wff
       (because if ` <. a , b >. ` fulfils the wff, then also ` <. b , a >. `
       fulfils the wff).  (Contributed by AV, 27-Aug-2023.) $)
    ichnreuop $p |- ( [ a <> b ] ph -> -. E! p e. ( X X. X )
                            E. a E. b ( p = <. a , b >. /\ a =/= b /\ ph ) ) $=
      ( vx vy vv vc vd cv cop wceq w3a wex wi wa wn nfv adantl vw wich wne wral
      wrex cxp wreu wcel wo notnotb wsbc nfsbc1v nf3an nfcv nfsbcw opeq12 simpl
      eqeq2d simpr neeq12d sbceq1a sylan9bbr 3anbi123d cbvex2v vex opth biimpcd
      eleq1w com12 sylbi 3ad2ant1 impcom adantr eqidd necom biimpi 3ad2ant2 wsb
      wb wal dfich2 2sp sbsbc sbbii bitri 3bitr3g biimpd 3ad2ant3 sbccom sylibr
      3jca opeq2 neeq2 spcegf sylc nfex opeq1 neeq1 exbidv opth1 necon3ai eqeq2
      equcomd mtbird 3adant3 jcnd eqeq1d 3anbi1d 2exbidv imbi12d notbid rspc2ev
      syl3anc rexnal2 sylib exlimdvv biimtrid biimtrrid orrd ralrimivva ralnex2
      ex ianor eqeq1 reuop sylnibr ) ADEUBZFKZGKZLZDKZEKZLZMZYKYLUCZANZEODOZHKZ
      UAKZLZYMMZYOANZEODOZYTYJMZPZUABUDHBUDZQZGBUEFBUEZCKZYMMZYOANZEODOZCBBUFUG
      YGUUGRZGBUDFBUDUUHRYGUUMFGBBYGYHBUHZYIBUHZQZQZYQRZUUFRZUIUUMUUQUURUUSUURR
      YQUUQUUSYQUJYQYJIKZJKZLZMZUUTUVAUCZAEUVAUKZDUUTUKZNZJOIOUUQUUSYPUVGDEIJYP
      ISYPJSUVCUVDUVFDUVCDSUVDDSUVEDUUTULUMUVCUVDUVFEUVCESUVDESUVEEDUUTEUUTUNZA
      EUVAULUOUMYKUUTMZYLUVAMZQZYNUVCYOUVDAUVFUVKYMUVBYJYKYLUUTUVAUPURUVKYKUUTY
      LUVAUVIUVJUQUVIUVJUSUTUVJAUVEUVIUVFAEUVAVAUVEDUUTVAVBVCVDUUQUVGUUSIJUUQUV
      GUUSUUQUVGQZUUERZUABUEHBUEZUUSUVLUVABUHZUUTBUHZUVAUUTLZYMMZYOANZEOZDOZUVQ
      YJMZPZRZUVNUVGUUQUVOUVCUVDUUQUVOPZUVFUVCYHUUTMZYIUVAMZQZUWEYHYIUUTUVAFVEG
      VEVFZUWGUWEUWFUUQUWGUVOUUPUWGUVOPZYGUUOUWJUUNUWGUUOUVOGJBVHVGTTVITVJVKVLZ
      UVGUUQUVPUVCUVDUUQUVPPZUVFUVCUWHUWLUWIUWFUWLUWGUUQUWFUVPUUPUWFUVPPZYGUUNU
      WMUUOUWFUUNUVPFIBVHVGVMTVIVMVJVKVLZUVLUWAUWBUVLUVOUVQUVAYLLZMZUVAYLUCZADU
      VAUKZNZEOZUWAUWKUVLUVPUVQUVQMZUVAUUTUCZUWREUUTUKZNZUWTUWNUVLUXAUXBUXCUVLU
      VQVNUVGUXBUUQUVDUVCUXBUVFUVDUXBUUTUVAVOVPVQTUVLAEUUTUKZDUVAUKZUXCUVGUUQUX
      FUVFUVCUUQUXFPUVDUUQUVFUXFYGUVFUXFPZUUPYGAEJVRZDIVRZAEIVRZDJVRZVSZJVTIVTZ
      UXGADEIJWAUXMUVFUXFUXMUXIUXKUVFUXFUXLIJWBUXIUVEDIVRUVFUXHUVEDIAEJWCWDUVED
      IWCWEUXKUXEDJVRUXFUXJUXEDJAEIWCWDUXEDJWCWEWFWGVJVMVIWHVLAEDUUTUVAWIWJWKUW
      SUXDEUUTBUVHUXAUXBUXCEUXAESUXBESUWREUUTULUMYLUUTMZUWPUXAUWQUXBUWRUXCUXNUW
      OUVQUVQYLUUTUVAWLURYLUUTUVAWMUWREUUTVAVCWNWOUVTUWTDUVABDUVAUNUWSDEUWPUWQU
      WRDUWPDSUWQDSADUVAULUMWPYKUVAMZUVSUWSEUXOUVRUWPYOUWQAUWRUXOYMUWOUVQYKUVAY
      LWQURYKUVAYLWRADUVAVAVCWSWNWOUVGUWBRZUUQUVCUVDUXPUVFUVCUVDQUWBUVQUVBMZUVD
      UXQRUVCUXQUUTUVAUXQJIUVAUUTUUTUVAJVEIVEWTXCXATUVCUWBUXQVSUVDYJUVBUVQXBVMX
      DXETXFUVMUWDUVAYSLZYMMZYOANZEODOZUXRYJMZPZRHUAUVAUUTBBYRUVAMZUUEUYCUYDUUC
      UYAUUDUYBUYDUUBUXTDEUYDUUAUXSYOAUYDYTUXRYMYRUVAYSWQZXGXHXIUYDYTUXRYJUYEXG
      XJXKYSUUTMZUYCUWCUYFUYAUWAUYBUWBUYFUXTUVSDEUYFUXSUVRYOAUYFUXRUVQYMYSUUTUV
      AWLZXGXHXIUYFUXRUVQYJUYGXGXJXKXLXMUUEHUABBXNXOYBXPXQXRXSYQUUFYCWJXTUUGFGB
      BYAXOUULYQUUCHUABBCFGUUIYJMZUUKYPDEUYHUUJYNYOAUUIYJYMYDXHXIUUIYTMZUUKUUBD
      EUYIUUJUUAYOAUUIYTYMYDXHXIYEYF $.
  $}

  ${
    $d X a b p v w x y $.  $d ph p v w x y $.
    $( If the setvar variables are interchangeable in a wff, and there is a
       unique ordered pair fulfilling the wff, then both setvar variables must
       be equal.  (Contributed by AV, 28-Aug-2023.) $)
    ichreuopeq $p |- ( [ a <> b ] ph
                    -> ( E! p e. ( X X. X ) E. a E. b ( p = <. a , b >. /\ ph )
                         -> E. a E. b ( a = b /\ ph ) ) ) $=
      ( vx vy vv vw cv cop wceq wa wex wi nfv nfan nfcv wsbc wsb wreu wral wrex
      cxp wich eqeq1 anbi1d 2exbidv reuop wcel nfich1 nfe1 nfralw nfich2 opeq12
      nfim nfex eqeq1d imbi12d ancoms adantl simprr adantr simpl eqidd vex opth
      rspc2gv wb sbceq1a equcoms sylan9bbr wal dfich2 sbsbc sbbii bitri 3bitr3g
      2sp sylbi biimpd com12 biimtrdi imp impcom sbccom sylibr jca opeq2 eqeq2d
      nfsbc1v anbi12d spcegf sylc opeq1 exbidv 3eqtr3rd anim1i exp31 impd opth1
      biimtrid syl11 19.8ad ex embantd syl5d exlimd rexlimdvva ) CJZDJZEJZKZLZA
      MZENDNZCBBUDUAFJZGJZKZXMLZAMZENZDNZHJZIJZKZXMLZAMZENZDNZYFXSLZOZIBUBZHBUB
      ZMZGBUCFBUCADEUEZXKXLLZAMZENZDNZXPYCYJHIBBCFGXJXSLZXOYADEUUAXNXTAXJXSXMUF
      UGUHXJYFLZXOYHDEUUBXNYGAXJYFXMUFUGUHUIYPYOYTFGBBYPXQBUJZXRBUJZMZMZYCYNYTU
      UFYBYNYTOZDYPUUEDADEUKUUEDPQYNYTDYMDHBDBRZYLDIBUUHYJYKDYIDULYKDPUPUMUMYSD
      ULUPUUFYAUUGEYPUUEEADEUNUUEEPQYNYTEYMEHBEBRZYLEIBUUIYJYKEYIEDYHEULUQYKEPU
      PUMUMYSEDYREULUQUPUUFYNXRXQKZXMLZAMZENZDNZUUJXSLZOZYAYTUUEYNUUPOZYPUUDUUC
      UUQYLUUPHIXRXQBBYDXRLYEXQLMZYJUUNYKUUOUURYHUULDEUURYGUUKAUURYFUUJXMYDYEXR
      XQUOZURUGUHUURYFUUJXSUUSURUSVHUTVAUUFYAUUPYTOUUFYAMZUUNUUOYTUUTUUDUUJXRXL
      KZLZADXRSZMZENZUUNUUFUUDYAYPUUCUUDVBVCUUTUUCUUJUUJLZUVCEXQSZMZUVEUUFUUCYA
      UUEUUCYPUUCUUDVDVAVCUUTUVFUVGUUTUUJVEUUTAEXQSZDXRSZUVGYAUUFUVJXTAUUFUVJOZ
      XTXQXKLZXRXLLZMZAUVKOXQXRXKXLFVFZGVFZVGZUVNAAEXRSZDXQSZUVKUVMAUVRUVLUVSAU
      VRVIEGAEXRVJVKUVRUVSVIDFUVRDXQVJVKVLUUFUVSUVJYPUVSUVJOUUEYPUVSUVJYPAEGTZD
      FTZAEFTZDGTZVIZGVMFVMZUVSUVJVIADEFGVNUWEUWAUWCUVSUVJUWDFGVSUWAUVRDFTUVSUV
      TUVRDFAEGVOVPUVRDFVOVQUWCUVIDGTUVJUWBUVIDGAEFVOVPUVIDGVOVQVRVTWAVCWBWCVTW
      DWEAEDXQXRWFWGWHUVDUVHEXQBEXQRUVFUVGEUVFEPUVCEXQWKQXLXQLZUVBUVFUVCUVGUWFU
      VAUUJUUJXLXQXRWIWJUVCEXQVJWLWMWNUUMUVEDXRBDXRRUVDDEUVBUVCDUVBDPADXRWKQUQX
      KXRLZUULUVDEUWGUUKUVBAUVCUWGXMUVAUUJXKXRXLWOWJADXRVJWLWPWMWNUUTUUOYTUUTUU
      OMZYSDUWHYREUUTUUOYRYAUUOYROUUFXRXQLZYAYRUUOUWIXTAYRXTUVNUWIAYROUVQUWIUVN
      AYRUWIUVNMZYQAUWJXRXQXLXKUWIUVNVDUWIUVLUVMVBUVNUVLUWIUVLUVMVDVAWQWRWSXBWT
      XRXQXQXRUVPUVOXAXCVAWDXDXDXEXFXEXGXHXHWTXIXB $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Set of unordered pairs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Two identical representations of the class of all unordered pairs.
     (Contributed by AV, 21-Nov-2021.) $)
  sprid $p |- { p | E. a e. _V E. b e. _V p = { a , b } }
              = { p | E. a E. b p = { a , b } } $=
    ( cv cpr wceq cvv wrex wex rexv exbii bitri abbii ) ADBDCDEFZCGHZBGHZNCIZBI
    ZAPOBIROBJOQBNCJKLM $.

  ${
    $d A a b p $.  $d B a b p $.
    $( An unordered pair is an element of all unordered pairs.  At least one of
       the two elements of the unordered pair must be a set.  Otherwise, the
       unordered pair would be the empty set, see ~ prprc , which is not an
       element of all unordered pairs, see ~ spr0nelg .  (Contributed by AV,
       21-Nov-2021.) $)
    elsprel $p |- ( ( A e. V \/ B e. W )
                    -> { A , B } e. { p | E. a E. b p = { a , b } } ) $=
      ( wcel wo cpr cv wceq wex cvv elex wa csn adantr adantl ex cab orim12i wi
      elisset exdistrv preq12 eqcomd 2eximi sylbir syl2an expcom wn preq2 dfsn2
      sneq eqtr3id eqtr2d spimevw prprc2 eqeq1d exbidv mpbird eximdv syl5 preq1
      pm2.61i prprc1 impcom excom sylibr syl11 jaoi syl prex eqeq1 2exbidv elab
      ) ACHZBDHZIZABJZFKZGKZJZLZGMZFMZWAEKZWDLZGMFMZEUAHVTANHZBNHZIWGVRWKVSWLAC
      OBDOUBWKWGWLWLWKWGUCWKWLWGWKWBALZFMZWCBLZGMZWGWLFANUDZGBNUDZWNWPPWMWOPZGM
      FMWGWMWOFGUEWSWEFGWSWDWAWBWCABUFUGUHUIUJZUKWKWNWLULZWGWQXAWMWFFXAWMWFXAWM
      PZWFAQZWDLZGMZWMXEXAWMXDGFWCWBLZWMXDXFWMPZWDWBWBJZXCXFWDXHLWMWCWBWBUMRXGX
      HWBQZXCWBUNWMXIXCLXFWBAUOSUPUQTURSXBWEXDGXBWAXCWDXAWAXCLWMABUSRUTVAVBTVCV
      DVFWKWLWGUCWKWLWGWTTWPWKULZWGWLWPXJWGWPXJPWEFMZGMZWGXJWPXLXJWOXKGXJWOXKXJ
      WOPZXKBQZWDLZFMZWOXPXJWOXOFGWBWCLZWOXOXQWOPZWDWCWCJZXNXQWDXSLWOWBWCWCVERX
      RXSWCQZXNWCUNWOXTXNLXQWCBUOSUPUQTURSXMWEXOFXMWAXNWDXJWAXNLWOABVGRUTVAVBTV
      CVHWEFGVIVJTWRVKVFVLVMWJWGEWAABVNWHWALWIWEFGWHWAWDVOVPVQVJ $.
  $}

  ${
    $d a p $.  $d b p $.
    $( The empty set is not an element of all unordered pairs.  (Contributed by
       AV, 21-Nov-2021.) $)
    spr0nelg $p |- (/) e/ { p | E. a E. b p = { a , b } } $=
      ( c0 cv cpr wceq wex cab wnel wa wn wo wal ianor bicomi albii alnex bitri
      vex nesymi eqeq1 mtbiri alrimivv 2nexaln sylibr imori mpgbi df-nel clelab
      prnz wcel xchbinx mpbir ) DAEZBEZCEZFZGZCHBHZAIZJZUODGZUTKZAHZLZVCLUTLZMZ
      VFAVHANVDLZANVFVHVIAVIVHVCUTOPQVDARSVCVGVCUSLZCNBNVGVCVJBCVCUSDURGURDUPUQ
      BTUKUAUODURUBUCUDUSBCUEUFUGUHVBDVAULVEDVAUIUTADUJUMUN $.
  $}

  $( Declare new symbols needed. $)
  $c Pairs $.

  $( Extend class notation with set of pairs. $)
  cspr $a class Pairs $.

  ${
    $d a b p v $.
    $( Define the function which maps a set ` v ` to the set of pairs
       consisting of elements of the set ` v ` .  (Contributed by AV,
       21-Nov-2021.) $)
    df-spr $a |- Pairs = ( v e. _V |-> { p | E. a e. v E. b e. v
                                             p = { a , b } } ) $.
  $}

  ${
    $d V a b p v $.  $d W a b p v $.
    $( The set of all unordered pairs over a given set ` V ` .  (Contributed by
       AV, 21-Nov-2021.) $)
    sprval $p |- ( V e. W -> ( Pairs ` V ) = { p | E. a e. V E. b e. V
                                                    p = { a , b } } ) $=
      ( vv wcel cpr wceq wrex cab cvv cspr cmpt df-spr wral ralrimivw abrexex2g
      cv mpdan a1i wa wb id rexeq rexeqbidv adantl abbidv elex weu zfpair2 eueq
      mpbi euabex mp1i fvmptd ) ABGZFACSDSESHZIZEFSZJZDUTJZCKZUSEAJZDAJZCKZLMLM
      FLVCNIUQFCDEOUAUQUTAIZUBVBVECVGVBVEUCUQVGVAVDDUTAVGUDUSEUTAUEUFUGUHABUIUQ
      VDCKLGZDAPVFLGUQVHDAUQUSCKLGZEAPVHUQVIEAUSCUJZVIUQURLGVJDEUKCURULUMUSCUNU
      OQUSECABLRTQVDDCABLRTUP $.
  $}

  ${
    $d V a b p $.  $d W a b p $.
    $( The set of all unordered pairs over a given set ` V ` , expressed by a
       restricted class abstraction.  (Contributed by AV, 21-Nov-2021.) $)
    sprvalpw $p |- ( V e. W -> ( Pairs ` V ) = { p e. ~P V |
                                       E. a e. V E. b e. V p = { a , b } } ) $=
      ( wcel cspr cfv cv cpr wceq wrex cab cpw crab sprval wa wb wss prssi prex
      eleq1 elpw bitrdi syl5ibrcom rexlimivv pm4.71ri a1i abbidv df-rab eqtr4di
      eqtrd ) ABFZAGHCIZDIZEIZJZKZEALDALZCMZUSCANZOZABCDEPUMUTUNVAFZUSQZCMVBUMU
      SVDCUSVDRUMUSVCURVCDEAAUOAFUPAFQVCURUQASZUOUPATURVCUQVAFVEUNUQVAUBUQAUOUP
      UAUCUDUEUFUGUHUIUSCVAUJUKUL $.

    $( The set of all unordered pairs over a given set ` V ` is a subset of the
       set of all unordered pairs.  (Contributed by AV, 21-Nov-2021.) $)
    sprssspr $p |- ( Pairs ` V ) C_ { p | E. a E. b p = { a , b } } $=
      ( cvv wcel cspr cfv cv cpr wceq wex cab wss wrex sprval wa a1i eqsstrd c0
      wi wal r2ex simpr 2eximi sylbi ax-gen ss2ab sylibr wn fvprc 0ss pm2.61i )
      AEFZAGHZBICIZDIZJKZDLCLZBMZNUNUOURDAOCAOZBMZUTAEBCDPUNVAUSUAZBUBZVBUTNVDU
      NVCBVAUPAFUQAFQZURQZDLCLUSURCDAAUCVFURCDVEURUDUEUFUGRVAUSBUHUISUNUJZUOTUT
      AGUKTUTNVGUTULRSUM $.

    $( The empty set is not an unordered pair over any set ` V ` .
       (Contributed by AV, 21-Nov-2021.) $)
    spr0el $p |- (/) e/ ( Pairs ` V ) $=
      ( vp va vb c0 cv cpr wceq wex cab wnel cspr cfv spr0nelg wcel wn sprssspr
      sseli con3i df-nel 3imtr4i ax-mp ) EBFCFDFGHDICIBJZKZEALMZKZBCDNEUCOZPEUE
      OZPUDUFUHUGUEUCEABCDQRSEUCTEUETUAUB $.

    $( The set of all unordered pairs over a given set ` V ` , expressed by a
       restricted class abstraction.  (Contributed by AV, 21-Nov-2021.) $)
    sprvalpwn0 $p |- ( V e. W -> ( Pairs ` V ) = { p e. ( ~P V \ { (/) } ) |
                                       E. a e. V E. b e. V p = { a , b } } ) $=
      ( wcel cspr cfv cv cpr wceq wrex cpw crab c0 csn wa wne a1i anbi1i wi vex
      cdif sprvalpw prnz eqnetrd rexlimivv adantl pm4.71ri ancom eldifsn bicomi
      id anass 3bitr3i bitri rabbia2 eqtrdi ) ABFAGHCIZDIZEIZJZKZEALDALZCAMZNVD
      CVEOPUCZNABCDEUDVDVDCVEVFUSVEFZVDQZUSORZVHQZUSVFFZVDQZVHVIVDVIVGVCVIDEAAV
      CVIUAUTAFVAAFQVCUSVBOVCUMVBORVCUTVADUBUESUFSUGUHUIVIVGQZVDQVGVIQZVDQVJVLV
      MVNVDVIVGUJTVIVGVDUNVNVKVDVKVNUSVEOUKULTUOUPUQUR $.

    $d X a b p $.
    $( An element of the set of all unordered pairs over a given set ` V ` is a
       pair of elements of the set ` V ` .  (Contributed by AV,
       22-Nov-2021.) $)
    sprel $p |- ( X e. ( Pairs ` V ) -> E. a e. V E. b e. V X = { a , b } ) $=
      ( vp cvv wcel cspr cfv cv cpr wceq wrex elfvex crab sprvalpw eleq2d eqeq1
      cpw 2rexbidv elrab simprbi biimtrdi mpcom ) AFGZBAHIZGZBCJDJKZLZDAMCAMZBA
      HNUEUGBEJZUHLZDAMCAMZEASZOZGZUJUEUFUOBAFECDPQUPBUNGUJUMUJEBUNUKBLULUICDAA
      UKBUHRTUAUBUCUD $.

    $( An element of a subset of the set of all unordered pairs over a given
       set ` V ` , is a pair of elements of the set ` V ` .  (Contributed by
       AV, 22-Nov-2021.) $)
    prssspr $p |- ( ( P C_ ( Pairs ` V ) /\ X e. P )
                    -> E. a e. V E. b e. V X = { a , b } ) $=
      ( cspr cfv wss wcel wa cv cpr wceq wrex ssel2 sprel syl ) ABFGZHCAIJCRICD
      KEKLMEBNDBNARCOBCDEPQ $.

    $d Y a b p $.
    $( An unordered pair of elements of a fixed set ` V ` belongs to the set of
       all unordered pairs over the set ` V ` .  (Contributed by AV,
       21-Nov-2021.) $)
    prelspr $p |- ( ( V e. W /\ ( X e. V /\ Y e. V ) )
                    -> { X , Y } e. ( Pairs ` V ) ) $=
      ( vp va vb wcel wa cpr wceq wrex cpw crab cspr cfv prelpwi eqidd eqeq2d
      cv preq1 preq2 rspc2ev mpd3an3 jca adantl 2rexbidv sylibr sprvalpw adantr
      eqeq1 elrab eleqtrrd ) ABHZCAHZDAHZIZIZCDJZETZFTZGTZJZKZGALFALZEAMZNZAOPZ
      URUSVFHZUSVCKZGALFALZIZUSVGHUQVLUNUQVIVKCDAQUOUPUSUSKZVKUQUSRVJVMUSCVBJZK
      FGCDAAVACKVCVNUSVACVBUASVBDKVNUSUSVBDCUBSUCUDUEUFVEVKEUSVFUTUSKVDVJFGAAUT
      USVCUKUGULUHUNVHVGKUQABEFGUIUJUM $.

    $d U a b $.  $d W a b $.
    $( The elements of a pair from the set of all unordered pairs over a given
       set ` V ` are elements of the set ` V ` .  (Contributed by AV,
       22-Nov-2021.) $)
    prsprel $p |- ( ( { X , Y } e. ( Pairs ` V ) /\ ( X e. U /\ Y e. W ) )
                      -> ( X e. V /\ Y e. V ) ) $=
      ( va vb cpr cspr wcel wa cv wceq wrex wi wb eleq1 eqcoms bi2anan9 biimpd
      sprel wo preq12bg ancomsd jaoi com12 adantl sylbid expcom com23 rexlimivv
      cfv syl imp ) DEHZBIULJZDAJECJKZDBJZEBJZKZUPUOFLZGLZHMZGBNFBNUQUTOZBUOFGU
      AVCVDFGBBVABJZVBBJZKZUQVCUTUQVGVCUTOUQVGKVCDVAMZEVBMZKZDVBMZEVAMZKZUBZUTD
      EVAVBACBBUCVGVNUTOUQVNVGUTVJVGUTOVMVJVGUTVHVEURVIVFUSVEURPVADVADBQRVFUSPV
      BEVBEBQRSTVMVFVEUTVMVFVEKUTVKVFURVLVEUSVFURPVBDVBDBQRVEUSPVAEVAEBQRSTUDUE
      UFUGUHUIUJUKUMUN $.

    $( The elements of a pair from a subset of the set of all unordered pairs
       over a given set ` V ` are elements of the set ` V ` .  (Contributed by
       AV, 21-Nov-2021.) $)
    prsssprel $p |- ( ( P C_ ( Pairs ` V ) /\ { X , Y } e. P
                        /\ ( X e. U /\ Y e. W ) )
                      -> ( X e. V /\ Y e. V ) ) $=
      ( cspr cfv wss cpr wcel wa ssel2 prsprel stoic3 ) ACGHZIEFJZAKQPKEBKFDKLE
      CKFCKLAPQMBCDEFNO $.
  $}

  ${
    $d V a b p $.  $d W a b p $.
    $( The set of all unordered pairs over a given set ` V ` , expressed by a
       restricted class abstraction.  (Contributed by AV, 24-Nov-2021.) $)
    sprvalpwle2 $p |- ( V e. W -> ( Pairs ` V )
                            = { p e. ( ~P V \ { (/) } ) | ( # ` p ) <_ 2 } ) $=
      ( va vb wcel cspr cfv cv cpr wceq wrex cpw c0 csn cdif crab chash c2 cle
      wbr sprvalpwn0 wa wb hashle2prv adantl bicomd rabbidva eqtrd ) ABFZAGHCIZ
      DIEIJKEALDALZCAMNOPZQUKRHSTUAZCUMQABCDEUBUJULUNCUMUJUKUMFZUCUNULUOUNULUDU
      JUKADEUEUFUGUHUI $.
  $}

  ${
    $d P c p x y $.  $d V c p x y $.
    $( Lemma for ~ sprsymrelf and ~ sprsymrelfv .  (Contributed by AV,
       19-Nov-2021.) $)
    sprsymrelfvlem $p |- ( P C_ ( Pairs ` V )
             -> { <. x , y >. | E. c e. P c = { x , y } } e. ~P ( V X. V ) ) $=
      ( vp cvv wcel cspr wss cv wceq wrex wi wa eleq1 biimtrdi com12 adantl c0
      cfv cpr copab cxp cpw simpl prsssprel 3exp com13 el2v rexlimiv imp simpld
      simprd opabex2 cop wex elopab adantld wb ad2antrr opelxp bitrdi mpbird ex
      exlimivv sylbi ssrdv elpwd wn fvprc sseq2d ss0b wal rexeq mtbiri alrimivv
      rex0 opab0 sylibr 0elpw eqeltrdi pm2.61i ) DGHZCDIUAZJZEKZAKZBKZUBZLZECMZ
      ABUCZDDUDZUEZHZNWDWFWPWDWFOZWMWNGWQWLABDDGGWDWFUFZWRWQWLOZWHDHZWIDHZWQWLW
      TXAOZWFWLXBNWDWLWFXBWKWFXBNZECWKWGCHZXCWKXDWJCHZXCWGWJCPXEXCNABWFXEWHGHWI
      GHOZXBWFXEXFXBCGDGWHWIUGUHUIUJQRUKZRSULZUMWSWTXAXHUNUOWQFWMWNFKZWMHZWQXIW
      NHZXJXIWHWIUPZLZWLOZBUQAUQWQXKNZWLABXIURXNXOABXNWQXKXNWQOZXKXBXNWQXBXNWFX
      BWDWLXCXMXGSUSULXPXKXLWNHZXBXMXKXQUTWLWQXIXLWNPVAWHWIDDVBVCVDVEVFVGRVHVIV
      EWDVJZWFCTLZWPXRWFCTJXSXRWETCDIVKVLCVMVCXSWMTWOXSWLVJZBVNAVNWMTLXSXTABXSW
      LWKETMWKEVRWKECTVOVPVQWLABVSVTWNWAWBQWC $.
  $}

  ${
    $d V c p i j $.  $d a b c i j p x y $.
    $( Lemma for ~ sprsymrelf1 .  (Contributed by AV, 22-Nov-2021.) $)
    sprsymrelf1lem $p |- ( ( a C_ ( Pairs ` V ) /\ b C_ ( Pairs ` V ) )
                           -> ( { <. x , y >. | E. c e. a c = { x , y } }
                              = { <. x , y >. | E. c e. b c = { x , y } }
                                -> a C_ b ) ) $=
      ( vp vi vj cv wss wa cpr wceq wrex wel wi wcel wb ex cfv prssspr ad4ant14
      cspr copab simpr adantr eleq1d eqeq1 adantl eqidd rspcedvd adantlr preq12
      cop weq eqeq2d rexbidv opelopabga bicomd ad3antrrr mpbid sylbid eleq2 cvv
      ad2antll el2v eqtr3 equcomd biimpd com13 rexlimiva com12 biimtrid expimpd
      imp syld rexlimdva2 rexlimiv mpcom ssrdv ) DJZCUDUAZKZEJZWCKZLZFJZAJZBJZM
      ZNZFWBOZABUEZWLFWEOZABUEZNZWBWEKWGWQLZGWBWEWRGDPZGEPZGJZHJZIJZMZNZICOZHCO
      ZWRWSLZWTWDWSXGWFWQWBCXAHIUBUCXFXHWTQZHCXBCRZXEXIICXJXCCRLZXELZWRWSWTXLWR
      LZWSXBXCUOZWNRZWTXMWSXDWBRZXOXMXAXDWBXLXEWRXKXEUFUGUHXMXPXOXMXPLWHXDNZFWB
      OZXOXLXPXRWRXLXPLZXQXDXDNZFXDWBXLXPUFXQXQXTSXSWHXDXDUIUJXSXDUKULUMXKXRXOS
      XEWRXPXKXOXRWMXRABXBXCCCAHUPBIUPLZWLXQFWBYAWKXDWHWIWJXBXCUNUQZURUSUTVAVBT
      VCXMXOXNWPRZWTWQXOYCSXLWGWNWPXNVDVFYCXQFWEOZXMWTYCYDSHIWOYDABXBXCVEVEYAWL
      XQFWEYBURUSVGXLYDWTQZWRXEYEXKYDXEWTXQXEWTQZFWEFEPZXQYFXEXQYGWTXEXQYGWTQXE
      XQLZYGWTYHWHXAWEYHGFXAWHXDVHVIUHVJTVKVPVLVMUJUGVNVCVQVOVRVSVTTWAT $.
  $}

  ${
    $d V q $.
    sprsymrelfo.q $e |- Q = { q e. ( Pairs ` V ) | A. a e. V A. b e. V
                                                ( q = { a , b } -> a R b ) } $.
    $( Lemma 1 for ~ sprsymrelfo .  (Contributed by AV, 22-Nov-2021.) $)
    sprsymrelfolem1 $p |- Q e. ~P ( Pairs ` V ) $=
      ( cv cpr wceq wbr wi wral cspr cfv crab cpw cvv fvex ssrab2 eqeltri
      elpwi2 ) ADHEHZFHZIJUCUDBKLFCMECMZDCNOZPZUFQGUGUFRCNSUEDUFTUBUA $.

    $d Q c $.  $d R a b c q x y $.  $d V a b c x y $.  $d W a b c $.
    $( Lemma 2 for ~ sprsymrelfo .  (Contributed by AV, 23-Nov-2021.) $)
    sprsymrelfolem2 $p |- ( ( V e. W /\ R C_ ( V X. V )
                              /\ A. x e. V A. y e. V ( x R y <-> y R x ) )
                            -> ( x R y <-> E. c e. Q c = { x , y } ) ) $=
      ( wcel cv wral wceq wa wi imp weq com12 cxp wss wbr w3a cpr wrex cspr cfv
      wb df-br simpl ssel adantl opelxp sylib prelspr syl2an2r biimtrid 3adant3
      cop ex vex preq12b breq12 biimpd adantr rsp2 ancomsd 3ad2ant3 com23 eleq1
      bi2anan9r ancoms imbi12d mpbid expimpd jaoi ralrimivva crab eleq2i imbi1d
      wo eqeq1 2ralbidv elrab bitri sylanbrc rspcev syl2anc cvv prsprel mpanr12
      eqidd biimtrdi preq1 eqeq2d breq1 preq2 breq2 rspc2v a1d sylanb rexlimiva
      imp4c mpcom impbid ) EFLZDEEUAZUBZAMZBMZDUCZXKXJDUCZUIZBENAENZUDZXLJMZXJX
      KUEZOZJCUFZXPXLXTXPXLPZXRCLZXRXROZXTYAXREUGUHZLZXRHMZIMZUEZOZYFYGDUCZQZIE
      NHENZYBXPXLYEXGXIXLYEQXOXLXJXKUTZDLZXGXIPZYEXJXKDUJYOYNYEYOXGYNXJELZXKELZ
      PZYEXGXIUKYOYNPYMXHLZYRYOYNYSXIYNYSQXGDXHYMULUMRXJXKEEUNUOEFXJXKUPUQVAURU
      SRYAYKHIEEYIAHSBISPZAISZBHSZPZWBZYAYFELZYGELZPZPZYJXJXKYFYGAVBZBVBZHVBIVB
      VCUUDUUHYJYTUUHYJQUUCUUHYTYJYAYTYJQZUUGXLUUKXPYTXLYJYTXLYJXJYFXKYGDVDVETU
      MVFTUUCYAUUGYJUUCYAPYQYPPZXMQZUUGYJQZYAUUMUUCXPXLUUMXPUULXLXMXOXGUULXLXMQ
      ZQXIXOUULUUOXOUULPXLXMXOUULXNXOYPYQXNXNABEEVGVHRVEVAVIVJRUMUUCUUMUUNUIYAU
      UCUULUUGXMYJUUBYQUUEUUAYPUUFXKYFEVKXJYGEVKVLUUBUUAXMYJUIXKYFXJYGDVDVMVNVF
      VOVPVQTURVRYBXRGMZYHOZYJQZIENHENZGYDVSZLYEYLPCUUTXRKVTUUSYLGXRYDUUPXROZUU
      RYKHIEEUVAUUQYIYJUUPXRYHWCWAWDWEWFWGYAXRWMXSYCJXRCXQXRXRWCWHWIVAXTXPXLXSX
      PXLQZJCXQCLZXQYDLZXQYHOZYJQZIENHENZPZXSUVBUVCXQUUTLUVHCUUTXQKVTUUSUVGGXQY
      DGJSZUURUVFHIEEUVIUUQUVEYJUUPXQYHWCWAWDWEWFUVHXSPZXLXPYRUVJXLUVHXSYRUVDXS
      YRQUVGXSUVDYRXSUVDYEYRXQXRYDVKYEXJWJLXKWJLYRUUIUUJWJEWJXJXKWKWLWNTVFRYRUV
      DUVGXSXLYRUVGXSXLQZQUVDUVFUVKXQXJYGUEZOZXJYGDUCZQHIXJXKEEHASZUVEUVMYJUVNU
      VOYHUVLXQYFXJYGWOWPYFXJYGDWQVNIBSZUVMXSUVNXLUVPUVLXRXQYGXKXJWRWPYGXKXJDWS
      VNWTXAXDXEXAXBXCTXF $.
  $}

  ${
    $d P p $.  $d V c x y $.  $d c p x y $.
    sprsymrelf.p $e |- P = ~P ( Pairs ` V ) $.
    sprsymrelf.r $e |- R = { r e. ~P ( V X. V ) |
                             A. x e. V A. y e. V ( x r y <-> y r x ) } $.
    ${
      $d X c p x y $.
      sprsymrelf.f $e |- F = ( p e. P |-> { <. x , y >. |
                                            E. c e. p c = { x , y } } ) $.
      $( The value of the function ` F ` which maps a subset of the set of
         pairs over a fixed set ` V ` to the relation relating two elements of
         the set ` V ` iff they are in a pair of the subset.  (Contributed by
         AV, 19-Nov-2021.) $)
      sprsymrelfv $p |- ( X e. P -> ( F ` X ) = { <. x , y >. |
                                                 E. c e. X c = { x , y } } ) $=
        ( wcel cv cpr wceq wrex copab cpw cxp rexeq opabbidv cspr cfv wss elpwi
        id eleq2s sprsymrelfvlem syl fvmptd3 ) GCNZIGJOAOBOPQZJIOZRZABSUNJGRZAB
        SZCEFFUATZMUOGQUPUQABUNJUOGUBUCUMUHUMGFUDUEZUFZURUSNVAGUTTCGUTUGKUIABGF
        JUJUKUL $.

      $d a b c p x y $.  $d p r $.  $d R p $.  $d V c r x y $.
      $( The mapping ` F ` is a function from the subsets of the set of pairs
         over a fixed set ` V ` into the symmetric relations ` R ` on the fixed
         set ` V ` .  (Contributed by AV, 19-Nov-2021.) $)
      sprsymrelf $p |- F : P --> R $=
        ( va vb cv wceq wcel wbr wral wa cpr wrex copab wb cxp cpw crab cfv wss
        cspr sprsymrelfvlem wel prcom a1i eqeq2d rexbidva cop df-br opabidw vex
        bitri weq preq12 rexbidv cbvopabv 3bitr4g ralrimivva jca eleq2i nfopab1
        braba elpw nfeq2 nfopab2 bibi12d ralbid elrab 3imtr4i eleqtrrdi fmpti
        breq ) HCDIOZAOZBOZUAZPZIHOZUBZABUCZELWGCQZWIWCWDGOZRZWDWCWKRZUDZBFSZAF
        SZGFFUEUFZUGZDWGFUJUHZUIZWIWQQZWCWDWIRZWDWCWIRZUDZBFSZAFSZTWJWIWRQWTXAX
        FABWGFIUKWTXDABFFWTWCFQWDFQTTZWHWBWDWCUAZPZIWGUBZXBXCXGWFXIIWGXGIHULTZW
        EXHWBWEXHPXKWCWDUMUNUOUPXBWCWDUQWIQWHWCWDWIURWHABUSVAWBMOZNOZUAZPZIWGUB
        ZXJMNWDWCWIBUTAUTMBVBNAVBTZXOXIIWGXQXNXHWBXLXMWDWCVCUOVDWHXPABMNAMVBBNV
        BTZWFXOIWGXRWEXNWBWCWDXLXMVCUOVDVEVKVFVGVHWJWGWSUFZQWTCXSWGJVIWGWSHUTVL
        VAWPXFGWIWQWKWIPZWOXEAFAWKWIWHABVJVMXTWNXDBFBWKWIWHABVNVMXTWLXBWMXCWCWD
        WKWIWAWDWCWKWIWAVOVPVPVQVRKVSVT $.

      $d F a b $.  $d P a b $.  $d V a b $.
      $( The mapping ` F ` is a one-to-one function from the subsets of the set
         of pairs over a fixed set ` V ` into the symmetric relations ` R ` on
         the fixed set ` V ` .  (Contributed by AV, 19-Nov-2021.) $)
      sprsymrelf1 $p |- F : P -1-1-> R $=
        ( va vb cv cfv wceq wcel wa wss wf1 wf weq wi wral sprsymrelf cpr copab
        wrex sprsymrelfv eqeqan12d cspr cpw eleq2i vex bitri sprsymrelf1lem imp
        elpw eqcom biimtrid ancoms eqssd ex syl2anb sylbid rgen2 dff13 mpbir2an
        ) CDEUACDEUBMOZEPZNOZEPZQZMNUCZUDZNCUEMCUEABCDEFGHIJKLUFVPMNCCVJCRZVLCR
        ZSVNIOAOBOUGQZIVJUIABUHZVSIVLUIABUHZQZVOVQVRVKVTVMWAABCDEFVJGHIJKLUJABC
        DEFVLGHIJKLUJUKVQVJFULPZTZVLWCTZWBVOUDVRVQVJWCUMZRWDCWFVJJUNVJWCMUOUSUP
        VRVLWFRWECWFVLJUNVLWCNUOUSUPWDWESZWBVOWGWBSVJVLWGWBVJVLTABFMNIUQURWGWBV
        LVJTZWEWDWBWHUDWBWAVTQWEWDSWHVTWAUTABFNMIUQVAVBURVCVDVEVFVGMNCDEVHVI $.

      $d a b c f q t x y $.  $d r t $.  $d F f t $.  $d P f t $.  $d R f p $.
      $d R t $.  $d V f q c t x y $.  $d W a b c f t x y $.
      $( The mapping ` F ` is a function from the subsets of the set of pairs
         over a fixed set ` V ` onto the symmetric relations ` R ` on the fixed
         set ` V ` .  (Contributed by AV, 23-Nov-2021.) $)
      sprsymrelfo $p |- ( V e. W -> F : P -onto-> R ) $=
        ( vt vf cv wceq wral wa wi vq va vb wcel wf cfv wrex wfo sprsymrelf a1i
        cpr copab cxp cpw wbr breq bibi12d 2ralbidv elrab2 cspr sprsymrelfolem1
        crab eqid eleqtrri rexeq opabbidv eqeq2d adantl wss velpw wrel cvv xpss
        wb sstr2 mpi df-rel sylibr dfrel4v nfv nfra1 nfan sprsymrelfolem2 3expa
        nfra2w opabbid biimpd ex com23 biimtrid mpd expcom sylbi imp31 rspcedvd
        impcom sprsymrelfv rexbidva mpbird ralrimiva dffo3 sylanbrc ) FGUDZCDEU
        EZNPZOPZEUFZQZOCUGZNDRCDEUHXDXCABCDEFHIJKLMUIUJXCXINDXCXEDUDZSZXIXEJPAP
        ZBPZUKQZJXFUGZABULZQZOCUGZXJXCXRXJXEFFUMZUNZUDZXLXMXEUOZXMXLXEUOZVNZBFR
        ZAFRZSZXCXRTXLXMHPZUOZXMXLYHUOZVNZBFRAFRYFHXEXTDYHXEQZYKYDABFFYLYIYBYJY
        CXLXMYHXEUPXMXLYHXEUPUQURLUSYGXCXRYGXCSZXQXEXNJUAPUBPZUCPZUKQYNYOXEUOTU
        CFRUBFRUAFUTUFZVBZUGZABULZQZOYQCYQCUDYMYQYPUNCYQXEFUAUBUCYQVCZVAKVDUJXF
        YQQZXQYTVNYMUUBXPYSXEUUBXOYRABXNJXFYQVEVFVGVHYAYFXCYTYAXEXSVIZYFXCYTTTN
        XSVJUUCXCYFYTXCUUCYFYTTZXCUUCSZXEVKZUUDUUCUUFXCUUCXEVLVLUMZVIZUUFUUCXSU
        UGVIUUHFFVMXEXSUUGVOVPXEVQVRVHUUFXEYBABULZQZUUEUUDABXEVSUUEYFUUJYTUUEYF
        UUJYTTUUEYFSZUUJYTUUKUUIYSXEUUKYBYRABUUEYFAUUEAVTYEAFWAWBUUEYFBUUEBVTYD
        ABFFWEWBXCUUCYFYBYRVNABYQXEFGUAUBUCJUUAWCWDWFVGWGWHWIWJWKWLWIWMWNWOWHWM
        WPXKXHXQOCXKXFCUDZSXGXPXEUULXGXPQXKABCDEFXFHIJKLMWQVHVGWRWSWTONCDEXAXB
        $.

      $( The mapping ` F ` is a bijection between the subsets of the set of
         pairs over a fixed set ` V ` into the symmetric relations ` R ` on the
         fixed set ` V ` .  (Contributed by AV, 23-Nov-2021.) $)
      sprsymrelf1o $p |- ( V e. W -> F : P -1-1-onto-> R ) $=
        ( wcel wf1 wfo wf1o sprsymrelf1 a1i sprsymrelfo df-f1o sylanbrc ) FGNZC
        DEOZCDEPCDEQUDUCABCDEFHIJKLMRSABCDEFGHIJKLMTCDEUAUB $.
    $}

    $d c p r x y $.  $d f c p x y $.  $d P f $.  $d R f p $.  $d V r $.
    $d W c x y $.
    $( There is a bijection between the subsets of the set of pairs over a
       fixed set ` V ` and the symmetric relations ` R ` on the fixed set
       ` V ` .  (Contributed by AV, 23-Nov-2021.) $)
    sprbisymrel $p |- ( V e. W -> E. f f : P -1-1-onto-> R ) $=
      ( vp vc wcel cv cpr wceq wrex cvv wf1o cspr cmpt wex cfv cpw fvex eqeltri
      copab pwex mptexg mp1i eqid sprsymrelf1o f1oeq1 spcegv sylc ) FGMZKCLNANB
      NOPLKNQABUGZUAZRMZCDURSZCDENZSZEUBCRMUSUPCFTUCZUDRIVCFTUEUHUFKCUQRUIUJABC
      DURFGHKLIJURUKULVBUTEURRCDVAURUMUNUO $.

    $( The class ` P ` of subsets of the set of pairs over a fixed set ` V `
       and the class ` R ` of symmetric relations on the fixed set ` V ` are
       equinumerous.  (Contributed by AV, 27-Nov-2021.) $)
    sprsymrelen $p |- ( V e. W -> P ~~ R ) $=
      ( vf wcel cv wf1o wex cen wbr sprbisymrel bren sylibr ) EFKCDJLMJNCDOPABC
      DJEFGHIQCDJRS $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Proper (unordered) pairs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Proper (unordered) pairs are unordered pairs with exactly 2 elements.  The
  set of proper pairs with elements of a class ` V ` is defined by
  ` { x e. ~P V | ( # `` x ) = 2 } `.

  For example, ` { 1 ,  2 } ` is a proper pair, because ` 1 =/= 2 ` ( see
  ~ 1ne2 ).  Examples for not proper unordered pairs are ` { 1 , 1 } = { 1 } `
  (see ~ preqsn ), ` { 1 , _V } = { 1 } ` (see ~ prprc2 ) or
  ` { _V , _V } = (/) ` (see ~ prprc ).

$)

  ${
    $d V x $.  $d V a b $.  $d X x $.  $d X a b $.
    prpair.p $e |- P = { x e. ~P V | ( # ` x ) = 2 } $.
    $( Characterization of a proper pair:  A class is a proper pair iff it
       consists of exactly two different sets.  (Contributed by AV,
       11-Mar-2023.) $)
    prpair $p |- ( X e. P <-> E. a e. V E. b e. V
                              ( X = { a , b } /\ a =/= b ) ) $=
      ( wcel cv chash cfv c2 wceq cpw crab wa wrex fveqeq2 imp adantr cpr elrab
      wne eleq2i hash2prb wss elpwi ancom 2rexbii biimpi ss2rexv syl2im prelpwi
      sylbid hashprg biimpd adantld wb eleq1 anbi12d adantl mpbir2and rexlimivv
      ex impbii 3bitri ) DBHDAIZJKLMZACNZOZHDVIHZDJKLMZPZDEIZFIZUAZMZVNVOUCZPZF
      CQECQZBVJDGUDVHVLADVIVGDLJRUBVMVTVKVLVTVKVLVRVQPZFDQEDQZVTDVIEFUEVKDCUFWB
      VSFDQEDQZVTDCUGWBWCWAVSEFDDVRVQUHUIUJVSEFDCUKULUNSVSVMEFCCVNCHVOCHPZVSVMW
      DVSPVMVPVIHZVPJKLMZWDWEVSVNVOCUMTWDVSWFWDVRWFVQWDVRWFVNVOCCUOUPUQSVSVMWEW
      FPURZWDVQWGVRVQVKWEVLWFDVPVIUSDVPLJRUTTVAVBVDVCVEVF $.
  $}

  ${
    $d V p $.  $d W p $.
    prproropf1o.o $e |- O = ( R i^i ( V X. V ) ) $.
    $( Lemma 0 for ~ prproropf1o .  Remark: ` O ` , the set of ordered ordered
       pairs, i.e., ordered pairs in which the first component is less than the
       second component, can alternatively be written as
       ` O = { x e. ( V X. V ) | ( 1st `` x ) R ( 2nd `` x ) } ` or even as
       ` O = { x e. ( V X. V ) | <. ( 1st `` x ) , ( 2nd `` x ) >. e. R } ` ,
       by which the relationship between ordered and unordered pair is
       immediately visible.  (Contributed by AV, 18-Mar-2023.) $)
    prproropf1olem0 $p |- ( W e. O <-> ( W = <. ( 1st ` W ) , ( 2nd ` W ) >.
                                    /\ ( ( 1st ` W ) e. V /\ ( 2nd ` W ) e. V )
                                    /\ ( 1st ` W ) R ( 2nd ` W ) ) ) $=
      ( wcel cxp cin wa c1st cfv c2nd cop wceq wbr w3a eleq2i elin ancom wb
      eleq1 df-br bitr4di adantr pm5.32i bitri anbi2i df-3an 3bitr4i 3bitri
      elxp6 ) DBFDACCGZHZFDAFZDULFZIZDDJKZDLKZMZNZUQCFURCFIZUQURAOZPZBUMDEQDAUL
      RUNUTVAIZIZVDVBIZUPVCVEVDUNIVFUNVDSVDUNVBUTUNVBTVAUTUNUSAFVBDUSAUAUQURAUB
      UCUDUEUFUOVDUNDCCUKUGUTVAVBUHUIUJ $.

    prproropf1o.p $e |- P = { p e. ~P V | ( # ` p ) = 2 } $.
    $( Lemma 1 for ~ prproropf1o .  (Contributed by AV, 12-Mar-2023.) $)
    prproropf1olem1 $p |- ( ( R Or V /\ W e. O )
                            -> { ( 1st ` W ) , ( 2nd ` W ) } e. P ) $=
      ( wor wcel wa c1st cfv c2nd cpr chash c2 wceq cvv fvex cpw cop wbr simpr2
      w3a prproropf1olem0 prelpwi syl wne wpo sopo adantr po2ne syl3anc hashprg
      simpr3 wb mp2an sylib jca sylan2b cv fveqeq2 elrab2 sylibr ) DBIZECJZKELM
      ZENMZOZDUAZJZVJPMQRZKZVJAJVGVFEVHVIUBRZVHDJVIDJKZVHVIBUCZUEZVNBCDEGUFVFVR
      KZVLVMVSVPVLVFVOVPVQUDZVHVIDUGUHVSVHVIUIZVMVSDBUJZVPVQWAVFWBVRDBUKULVTVFV
      OVPVQUPVHVIBDUMUNVHSJVISJWAVMUQELTENTVHVISSUOURUSUTVAFVBZPMQRVMFVJVKAWCVJ
      QPVCHVDVE $.

    $d R a b $.  $d V a b $.  $d X a b $.  $d X p $.
    $( Lemma 2 for ~ prproropf1o .  (Contributed by AV, 13-Mar-2023.) $)
    prproropf1olem2 $p |- ( ( R Or V /\ X e. P )
                       -> <. inf ( X , V , R ) , sup ( X , V , R ) >. e. O ) $=
      ( va vb wcel wa cinf csup cop cv wrex wbr cif ifcl wor cxp cin cpr prpair
      wceq wne simpll simplrl simplrr infsupprpr syl13anc df-br sylib w3a infpr
      simprr 3adant1 eqeltrd suppr jca 3expb adantr opelxp sylibr infeq1 supeq1
      elind wb opeq12d eleq1d ad2antrl mpbird rexlimdvva biimtrid imp eleqtrrdi
      ex ) DBUAZEAKZLEDBMZEDBNZOZBDDUBZUCZCVSVTWCWEKZVTEIPZJPZUDZUFZWGWHUGZLZJD
      QIDQVSWFFADEIJHUEVSWLWFIJDDVSWGDKZWHDKZLZLZWLWFWPWLLZWFWIDBMZWIDBNZOZWEKZ
      WQBWDWTWQWRWSBRZWTBKWQVSWMWNWKXBVSWOWLUHVSWMWNWLUIVSWMWNWLUJWPWJWKUQDWGWH
      BUKULWRWSBUMUNWQWRDKZWSDKZLZWTWDKWPXEWLVSWMWNXEVSWMWNUOZXCXDXFWRWGWHBRZWG
      WHSZDDWGWHBUPWMWNXHDKVSXGWGWHDTURUSXFWSWHWGBRZWGWHSZDDWGWHBUTWMWNXJDKVSXI
      WGWHDTURUSVAVBVCWRWSDDVDVEVHWJWFXAVIWPWKWJWCWTWEWJWAWRWBWSDEWIBVFDEWIBVGV
      JVKVLVMVRVNVOVPGVQ $.

    ${
      $d O p $.  $d P p $.  $d R p $.
      prproropf1o.f $e |- F = ( p e. P |-> <. inf ( p , V , R ) ,
                                              sup ( p , V , R ) >. ) $.
      $( Lemma 3 for ~ prproropf1o .  (Contributed by AV, 13-Mar-2023.) $)
      prproropf1olem3 $p |- ( ( R Or V /\ W e. O )
                            -> ( F ` { ( 1st ` W ) , ( 2nd ` W ) } )
                               = <. ( 1st ` W ) , ( 2nd ` W ) >. ) $=
        ( wcel wa cfv cinf csup cop cvv wceq opeq12d wbr wor c1st cpr cv infeq1
        c2nd supeq1 w3a prproropf1olem0 cif simpl simprll simprlr infpr syl3anc
        iftrue ad2antll eqtrd suppr wn impr iffalsed 3adantr1 sylan2b sylan9eqr
        soasym prproropf1olem1 opex a1i fvmptd2 ) EBUAZFDKZLZGFUBMZFUFMZUCZGUDZ
        EBNZVQEBOZPZVNVOPZACQJVQVPRZVMVTVPEBNZVPEBOZPZWAWBVRWCVSWDEVQVPBUEEVQVP
        BUGSVLVKFWARZVNEKZVOEKZLZVNVOBTZUHWEWARZBDEFHUIVKWIWJWKWFVKWIWJLZLZWCVN
        WDVOWMWCWJVNVOUJZVNWMVKWGWHWCWNRVKWLUKZVKWGWHWJULZVKWGWHWJUMZEVNVOBUNUO
        WJWNVNRVKWIWJVNVOUPUQURWMWDVOVNBTZVNVOUJZVOWMVKWGWHWDWSRWOWPWQEVNVOBUSU
        OWMWRVNVOVKWIWJWRUTEBVNVOVFVAVBURSVCVDVEABDEFGHIVGWAQKVMVNVOVHVIVJ $.

      $d R c d $.  $d V c d $.  $d W a b c d $.  $d Z a b c d $.  $d Z p $.
      $( Lemma 4 for ~ prproropf1o .  (Contributed by AV, 14-Mar-2023.) $)
      prproropf1olem4 $p |- ( ( R Or V /\ W e. P /\ Z e. P )
                              -> ( ( F ` Z ) = ( F ` W ) -> Z = W ) ) $=
        ( wcel wceq wi wa wb wn biimtrdi eqeq1d ex vc vd va vb wor w3a cfv cinf
        csup cop cvv infeq1 supeq1 opeq12d simp3 opex a1i fvmptd3 simp2 eqeq12d
        cv cpr wne wrex prpair id infexd supexd jca ad4antr opthg syl wbr solin
        w3o cif infpr 3expb iftrue sylan9eqr eqeq2d suppr adantl sotric iffalse
        wo ioran simplbiim impcom eqtrd anbi12d adantrr simprll simprlr syl3anc
        adantr simpl orc eqneqall adantld ancomd sylan2 anbi1d olc ancoms 3jaoi
        mpcom ad2antrl imp a1d ancom2s expdimp vex preq12b imbitrrdi eqeqan12rd
        sylbid eqeq12 imbi12d com12 mpbird rexlimdvva com13 biimtrid 3imp31
        sylbi ) EBUEZFALZGALZUFZGCUGZFCUGZMGEBUHZGEBUIZUJZFEBUHZFEBUIZUJZMZGFMZ
        YJYKYOYLYRYJHGHVAZEBUHZUUAEBUIZUJZYOACUKKUUAGMUUBYMUUCYNEUUAGBULEUUAGBU
        MUNYGYHYIUOYOUKLYJYMYNUPUQURYJHFUUDYRACUKKUUAFMUUBYPUUCYQEUUAFBULEUUAFB
        UMUNYGYHYIUSYRUKLYJYPYQUPUQURUTYIYHYGYSYTNZYIGUAVAZUBVAZVBZMZUUFUUGVCZO
        ZUBEVDUAEVDZYHYGUUENZNHAEGUAUBJVEYHFUCVAZUDVAZVBZMZUUNUUOVCZOZUDEVDUCEV
        DZUULUUMHAEFUCUDJVEYGUUTUULUUEYGUUSUULUUENZUCUDEEYGUUNELZUUOELZOZOZUUSU
        VAUVEUUSOZUUKUUEUAUBEEUVFUUFELZUUGELZOZOZUUKUUEUVJUUKOZUUEUUHEBUHZUUHEB
        UIZUJZUUPEBUHZUUPEBUIZUJZMZUUHUUPMZNZUVKUVRUVLUVOMZUVMUVPMZOZUVSUVKUVLU
        KLZUVMUKLZOZUVRUWCPYGUWFUVDUUSUVIUUKYGUWDUWEYGEUUHBYGVFZVGYGEUUHBUWGVHV
        IVJUVLUVMUVOUVPUKUKVKVLUVKUWCUUFUUNMZUUGUUOMZOZUUFUUOMZUUGUUNMZOZWFZUVS
        UVJUUKUWCUWNNZUVJUUJUWOUUIUVFUVIUUJUWOUVEUUSUVIUUJOZUWONZUVEUURUWQUUQUU
        NUUOBVMZUUNUUOMZUUOUUNBVMZVOUVEUURUWQNZEUUNUUOBVNUWRUVEUXANUWSUWTUWRUVE
        UXAUWRUVEOZUWQUURUXBUWPUWOUXBUWPOUWCUVLUUNMZUVMUUOMZOZUWNUXBUWCUXEPUWPU
        XBUWAUXCUWBUXDUXBUVOUUNUVLUVEUWRUVOUWRUUNUUOVPZUUNYGUVBUVCUVOUXFMZEUUNU
        UOBVQVRZUWRUUNUUOVSVTWAUXBUVPUUOUVMUXBUVPUWTUUNUUOVPZUUOUVEUVPUXIMZUWRY
        GUVBUVCUXJEUUNUUOBWBVRZWCUVEUWRUXIUUOMZUVEUWRUWSUWTWFQZUXLEUUNUUOBWDUXM
        UWSQUWTQUXLUWSUWTWGUWTUUNUUOWEWHRWIWJWAWKWPUXBUWPUXEUWNNZYGUWPUXNNUWRUV
        DYGUWPUXNUUFUUGBVMZUUFUUGMZUUGUUFBVMZVOZYGUWPOZUXNYGUVIUXRUUJEUUFUUGBVN
        WLZUXOUXSUXNNUXPUXQUXOUXSUXNUXOUXSOZUXEUWJUWNUYAUXCUWHUXDUWIUYAUVLUUFUU
        NUXSUXOUVLUXOUUFUUGVPZUUFUXSYGUVGUVHUVLUYBMZYGUWPWQZYGUVGUVHUUJWMZYGUVG
        UVHUUJWNZEUUFUUGBVQWOZUXOUUFUUGVSVTZSUYAUVMUUGUUOUYAUVMUXQUUFUUGVPZUUGU
        XSUVMUYIMZUXOUXSYGUVGUVHUYJUYDUYEUYFEUUFUUGBWBWOZWCUXSUXOUYIUUGMZUXSUXO
        UXPUXQWFQZUYLYGUVIUXOUYMPUUJEUUFUUGBWDWLUYMUXPQUXQQUYLUXPUXQWGUXQUUFUUG
        WEWHRWIWJZSWKUWJUWMWRZRTUXPUWPUXNYGUXPUUJUXNUVIUXNUUFUUGWSWTWTUXQUXSUXN
        UXQUXSOZUXEUYBUUNMZUWKOZUWNUYPUXCUYQUXDUWKUYPUVLUYBUUNUXSUYCUXQUYGWCZSU
        YPUVMUUFUUOUXSUXQUVMUYIUUFUYKUXQUUFUUGVSVTZSWKUYPUYRUWLUWKOUWNUYPUYQUWL
        UWKUXSUXQUYQUWLPZUXSUXQUUGUUFMZUXOWFQZVUAUWPYGUVHUVGOUXQVUCPUWPUVGUVHUV
        IUUJWQXAEUUGUUFBWDXBZVUCUYBUUGUUNVUCVUBQUXOQUYBUUGMZVUBUXOWGUXOUUFUUGWE
        WHZSRWIXCUWKUWLUWNUWMUWJXDZXERXQTXFXGTXHXIXQTXJTUWSUXAUVEUWQUUNUUOWSXJU
        WTUVEUXAUWTUVEOZUWQUURVUHUWPUWOVUHUWPOUWCUVLUUOMZUVMUUNMZOZUWNVUHUWCVUK
        PUWPVUHUWAVUIUWBVUJVUHUVOUUOUVLVUHUVOUXFUUOUVEUXGUWTUXHWCUVEUWTUXFUUOMZ
        UVEUWTUUOUUNMZUWRWFQZVULYGUVCUVBUWTVUNPEUUOUUNBWDXKVUNVUMQUWRQVULVUMUWR
        WGUWRUUNUUOWEWHRWIWJWAVUHUVPUUNUVMUVEUWTUVPUXIUUNUXKUWTUUNUUOVSVTWAWKWP
        VUHUWPVUKUWNNZYGUWPVUONUWTUVDYGUWPVUOUXRUXSVUOUXTUXOUXSVUONUXPUXQUXOUXS
        VUOUYAVUKUWMUWNUYAVUIUWKVUJUWLUYAUVLUUFUUOUYHSUYAUVMUUGUUNUYNSWKVUGRTUX
        PUWPVUOYGUXPUUJVUOUVIVUOUUFUUGWSWTWTUXQUXSVUOUYPVUKUWIUWHOUWNUYPVUIUWIV
        UJUWHUYPUVLUUGUUOUYPUVLUYBUUGUYSUXSUXQVUEUXSUXQVUCVUEVUDVUFRWIWJSUYPUVM
        UUFUUNUYTSWKUWHUWIUWNUYOXERTXFXGTXHXIXQTXJTXFXGWTXIXLWTXIUUFUUGUUNUUOUA
        XMUBXMUCXMUDXMXNXOXQUUKUVJUUEUVTPZUUIUVJVUPNUUJUVJUUIVUPUVFUUIVUPNZUVIU
        UQVUQUVEUURUUQUUIVUPUUQUUIOYSUVRYTUVSUUIUUQYOUVNYRUVQUUIYMUVLYNUVMEGUUH
        BULEGUUHBUMUNUUQYPUVOYQUVPEFUUPBULEFUUPBUMUNXPUUIUUQYTUVSPGUUHFUUPXRXEX
        STXHWPXTWPWIYATYBTYBYCYDYFYEXQ $.

      $d p w z $.  $d F w z $.  $d O p w z $.  $d P p w z $.  $d R p w z $.
      $d V w z $.
      $( There is a bijection between the set of proper pairs and the set of
         ordered ordered pairs, i.e., ordered pairs in which the first
         component is less than the second component.  (Contributed by AV,
         15-Mar-2023.) $)
      prproropf1o $p |- ( R Or V -> F : P -1-1-onto-> O ) $=
        ( vz vw cv cfv wceq wral cinf cop wcel wa sylanbrc wor wf1 wf1o wf csup
        wfo wi prproropf1olem2 cmpt infeq1 supeq1 opeq12d cbvmptv eqtri 3ancomb
        fmptd w3a 3anass bitri prproropf1olem4 sylbir ralrimivva wrex c1st c2nd
        dff13 cpr prproropf1olem1 eqeq2d adantl prproropf1olem3 prproropf1olem0
        wb fveq2 wbr simp1bi eqcomd eqtr2d rspcedvd ralrimiva dffo3 df-f1o ) EB
        UAZADCUBZADCUFZADCUCWCADCUDZJLZCMZKLZCMNWGWINUGZKAOJAOWDWCKAWIEBPZWIEBU
        EZQZDCABDEWIFGHUHCFAFLZEBPZWNEBUEZQZUIKAWMUIIFKAWQWMWNWINWOWKWPWLEWNWIB
        UJEWNWIBUKULUMUNUPZWCWJJKAAWCWGARZWIARZSSZWCWTWSUQZWJXBWCWSWTUQXAWCWTWS
        UOWCWSWTURUSABCDEWIWGFGHIUTVAVBJKADCVFTWCWFWIWHNZJAVCZKDOWEWRWCXDKDWCWI
        DRZSZXCWIWIVDMZWIVEMZVGZCMZNZJXIAABDEWIFGHVHWGXINZXCXKVMXFXLWHXJWIWGXIC
        VNVIVJXFXJXGXHQZWIABCDEWIFGHIVKXEXMWINWCXEWIXMXEWIXMNXGERXHERSXGXHBVOBD
        EWIGVLVPVQVJVRVSVTJKADCWATADCWBT $.
    $}

    $d O f p $.  $d P f p $.  $d R f p $.  $d V f $.
    $( The set of proper pairs and the set of ordered ordered pairs, i.e.,
       ordered pairs in which the first component is less than the second
       component, are equinumerous.  (Contributed by AV, 15-Mar-2023.) $)
    prproropen $p |- ( ( V e. W /\ R Or V ) -> O ~~ P ) $=
      ( vf wcel wor wa cv wf1o wex cen wbr cinf csup cvv cop cmpt chash c2 wceq
      cfv cpw rabexd adantr mptexd eqid prproropf1o adantl f1oeq1 spcedv ensymb
      pwexg bren bitri sylibr ) DEJZDBKZLZACIMZNZIOZCAPQZVCVEACFAFMZDBRVHDBSUAZ
      UBZNZITVJVCFAVITVAATJVBVAVHUCUFUDUEFDUGATHDEUQUHUIUJVBVKVAABVJCDFGHVJUKUL
      UMACVDVJUNUOVGACPQVFCAUPACIURUSUT $.
  $}

  ${
    $d O p x y $.  $d P p x y $.  $d R p x y $.  $d V p x y $.  $d ch x $.
    $d ph p x y $.  $d ps y $.  $d ps z $.  $d th x $.  $d x z $.
    prproropreud.o $e |- O = ( R i^i ( V X. V ) ) $.
    prproropreud.p $e |- P = { p e. ~P V | ( # ` p ) = 2 } $.
    prproropreud.b $e |- ( ph -> R Or V ) $.
    prproropreud.x $e |- ( x = <. inf ( y , V , R ) , sup ( y , V , R ) >.
                           -> ( ps <-> ch ) ) $.
    prproropreud.z $e |- ( x = z -> ( ps <-> th ) ) $.
    $( There is exactly one ordered ordered pair fulfilling a wff iff there is
       exactly one proper pair fulfilling an equivalent wff.  (Contributed by
       AV, 20-Mar-2023.) $)
    prproropreud $p |- ( ph -> ( E! x e. O ps <-> E! y e. P ch ) ) $=
      ( wreu cv wceq cinf csup cop cmpt cfv wsbc wor prproropf1o syl wb sbceq1a
      wf1o eqid adantl nfsbc1v reuf1odnf wcel wa cvv eqidd infeq1 opeq12d simpr
      supeq1 opex a1i fvmptd sbceq1d sbcieg bitrd reubidva ) ABEJRBEFSZLHLSZKIU
      AZVMKIUBZUCZUDZUEZUFZFHRCFHRABVSDEFGJHVQAKIUGHJVQULOHIVQJKLMNVQUMUHUIESVR
      TBVSUJABEVRUKUNQBEVRUOUPAVSCFHAVLHUQZURZVSBEVLKIUAZVLKIUBZUCZUFZCWABEVRWD
      WALVLVPWDHVQUSWAVQUTVMVLTZVPWDTWAWFVNWBVOWCKVMVLIVAKVMVLIVDVBUNAVTVCWDUSU
      QZWAWBWCVEVFZVGVHWAWGWECUJWHBCEWDUSPVIUIVJVKVJ $.
  $}

  ${
    $d p x $.  $d V x $.
    pairreueq.p $e |- P = { x e. ~P V | ( # ` x ) = 2 } $.
    $( Two equivalent representations of the existence of a unique proper pair.
       (Contributed by AV, 1-Mar-2023.) $)
    pairreueq $p |- ( E! p e. P ph
                      <-> E! p e. ~P V ( ( # ` p ) = 2 /\ ph ) ) $=
      ( cv wcel wa weu cpw chash cfv c2 wceq wreu fveqeq2 elrab2 anbi1i df-reu
      anass bitri eubii 3bitr4i ) EGZCHZAIZEJUEDKZHZUELMNOZAIZIZEJAECPUKEUHPUGU
      LEUGUIUJIZAIULUFUMABGZLMNOUJBUEUHCUNUENLQFRSUIUJAUAUBUCAECTUKEUHTUD $.
  $}

  ${
    $d A a b p q x y $.  $d B a b p q x y $.  $d P a b p q x y $.
    $d V a b x $.  $d ph a b p x y $.
    paireqne.a $e |- ( ph -> A e. V ) $.
    paireqne.b $e |- ( ph -> B e. V ) $.
    paireqne.p $e |- P = { x e. ~P V | ( # ` x ) = 2 } $.
    $( Two sets are not equal iff there is exactly one proper pair whose
       elements are either one of these sets.  (Contributed by AV,
       27-Jan-2023.) $)
    paireqne $p |- ( ph -> ( E! p e. P A. x e. p ( x = A \/ x = B )
                             <-> A =/= B ) ) $=
      ( va vb wceq wi wa wcel wb eqeq1 syl ex vq vy cv wral wreu wne wrex raleq
      wo weq reu8 cpr chash cfv c2 cpw crab eleq2i elss2prb bitri orbi12d ralpr
      vex bitrdi imbi2d ralbidv anbi12d prelpwi ad3antrrr hashprg adantl biimpd
      ad2antll jca com12 adantr impcom eqtr3 eqneqall a1d equcoms preq12 eqcomd
      impd expcom prcom eqtrid imp fveqeq2d mpbird fveqeq2 elrab sylibr imbi12d
      jaoi eqeq2 rspcv ralprg imbi1d eqid orci olci pm5.5 mp2an pm3.2i preq12bg
      cvv sylancr eqeq12 necon3bid necom imbitrrdi ad2antrl biimtrid rexlimdvva
      sylbid syld rexlimdva bilani ralrimiva prid1g eleq2 prid2g simplrr eqtr2d
      elpr wel exp32 mpdd rspcedvd impbid ) ABUCZCMZYLDMZUIZBGUCZUDZGEUEZCDUFZY
      RYQYOBUAUCZUDZGUAUJZNZUAEUDZOZGEUGAYSYQUUAGUAEYOBYPYTUHUKAUUEYSGEAYPEPZUU
      EYSNZUUFKUCZLUCZUFZYPUUHUUIULZMZOZLFUGKFUGZAUUGUUFYPYLUMUNUOMZBFUPZUQZPUU
      NEUUQYPJURKLBYPFUSUTAUUMUUGKLFFAUUHFPZUUIFPZOZOZUUMUUGUVAUUMOZUUEUUHCMZUU
      HDMZUIZUUICMZUUIDMZUIZOZUUAUUKYTMZNZUAEUDZOZYSUULUUEUVMQUVAUUJUULYQUVIUUD
      UVLUULYQYOBUUKUDUVIYOBYPUUKUHYOUVEUVHBUUHUUIKVCZLVCZBKUJYMUVCYNUVDYLUUHCR
      YLUUHDRVAZBLUJYMUVFYNUVGYLUUICRYLUUIDRVAZVBVDUULUUCUVKUAEUULUUBUVJUUAYPUU
      KYTRVEVFVGVMUVBUVIUVLYSUVBUVIUVLYSNUVBUVIOZUVLYOBCDULZUDZUUKUVSMZNZYSUVRU
      VSEPZUVLUWBNUVRUVSUUPPZUVSUMUNUOMZOZUWCUVRUWDUWEAUWDUUTUUMUVIACFPZDFPZOZU
      WDAUWGUWHHIVNZCDFVHSZVIUVRUWEUUKUMUNUOMZUVBUWLUVIUUMUVAUWLUUJUVAUWLNUULUV
      AUUJUWLUVAUUJUWLUUTUUJUWLQAUUHUUIFFVJVKVLVOVPVQVPUVRUVSUUKUOUMUVIUVBUVSUU
      KMZUVEUVHUVBUWMNZUVCUVHUWNNUVDUVHUVCUWNUVFUVCUWNNUVGUVFUVCUWNUVFUVCOLKUJZ
      UWNUUIUUHCVRUWNKLKLUJZUVAUUMUWMUWPUUMUWMNUVAUWPUUJUULUWMUULUWMNUUHUUIVSWD
      VTWDWAZSTUVCUVGUWNUVCUVGOZUWMUVBUWRUUKUVSUUHUUICDWBZWCVTWEWOVOUVHUVDUWNUV
      FUVDUWNNUVGUVFUVDUWNUVFUVDOZUWMUVBUWTUUKUVSUWTUUKUUIUUHULUVSUUHUUIWFUUIUU
      HCDWBWGZWCVTTUVGUVDUWNUVGUVDOUWOUWNUUIUUHDVRUWQSTWOVOWOWHVQWIWJVNUWCUVSUU
      QPUWFEUUQUVSJURUUOUWEBUVSUUPYLUVSUOUMWKWLUTZWMUVKUWBUAUVSEYTUVSMUUAUVTUVJ
      UWAYOBYTUVSUHYTUVSUUKWPWNWQSUVRUWBCCMZCDMZUIZDCMZDDMZUIZOZUWANZYSAUWBUXJQ
      UUTUUMUVIAUVTUXIUWAAUWIUVTUXIQUWJYOUXEUXHBCDFFYMYMUXCYNUXDYLCCRYLCDRVAYNY
      MUXFYNUXGYLDCRYLDDRVAWRSWSVIUXJUWAUVRYSUXEUXHUXJUWAQUXCUXDCWTXAUXGUXFDWTX
      BUXIUWAXCXDUVBUWAYSNUVIUVBUWAUWRUVDUVFOZUIZYSUVAUWAUXLQZUUMAUXMUUTAUUHXGP
      ZUUIXGPZOUWIUXMUXNUXOUVNUVOXEUWJUUHUUICDXGXGFFXFXHVPVPUUJUXLYSNUVAUULUXLU
      UJYSUWRUUJYSNUXKUWRUUJYSUWRUUHUUICDUUHCUUIDXIXJVLUXKUUJDCUFZYSUXKUUJUXPUX
      KUUHUUIDCUUHDUUICXIXJVLCDXKXLWOVOXMXPVPXNXPXQTWDXPTXOXNWHXRXNAYSYRAYSOZYQ
      YOBUBUCZUDZGUBUJZNZUBEUDZOZGEUGYRUXQUYCUVTUXSUVSUXRMZNZUBEUDZOZGUVSEUXQUW
      FUWCUXQUWDUWEAUWDYSUWKVPAYSUWEAYSUWEAUWIYSUWEQUWJCDFFVJSVLWHVNUXBWMYPUVSM
      ZUYCUYGQUXQUYHYQUVTUYBUYFYOBYPUVSUHUYHUYAUYEUBEUYHUXTUYDUXSYPUVSUXRRVEVFV
      GVKUXQUVTUYFUXQYOBUVSYLUVSPYOUXQYLCDBVCYFXSXTUXQUYEUBEUXQUXREPZUYEUYIUUJU
      XRUUKMZOZLFUGKFUGZUXQUYEUYIUXRUUQPUYLEUUQUXRJURKLBUXRFUSUTUXQUYKUYEKLFFUX
      QUUTOZUYKUYEUYMUYKOZUXSUVEUYDUYNKUBYGZUXSUVENUYNUYOUUHUUKPZUYMUYPUYKUURUY
      PUXQUUSUUHUUIFYAXMVPUYJUYOUYPQUYMUUJUXRUUKUUHYBVMWJYOUVEBUUHUXRUVPWQSUYNU
      XSUVHUVEUYDNUYNLUBYGZUXSUVHNUYNUYQUUIUUKPZUYMUYRUYKUUSUYRUXQUURUUHUUIFYCV
      MVPUYJUYQUYRQUYMUUJUXRUUKUUIYBVMWJYOUVHBUUIUXRUVQWQSUYNUVHUVEUYDUYNUVHUVE
      OZOUXRUUKUVSUYMUUJUYJUYSYDUYSUYNUWAUVHUVEUYNUWANZUVFUVEUYTNUVGUVEUVFUYTUV
      CUVFUYTNUVDUVCUVFUYTUVCUVFOUWPUYTUUHUUICVRUYNUWPUWAUUJUWPUWANUYMUYJUWPUUJ
      UWAUWAUUHUUIVSVOXMVOZSTUVFUVDUYTUWTUWAUYNUXAVTWEWOVOUVEUVGUYTUVCUVGUYTNUV
      DUVCUVGUYTUWRUWAUYNUWSVTTUVDUVGUYTUVDUVGOUWPUYTUUHUUIDVRVUASTWOVOWOWHVQYE
      YHXQYITXOXNWHXTVNYJYQUXSGUBEYOBYPUXRUHUKWMTYK $.
  $}


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Set of proper unordered pairs
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Declare new symbols needed. $)
  $c PrPairs $.

  $( Extend class notation with set of proper unordered pairs. $)
  cprpr $a class PrPairs $.

  ${
    $d a b p v $.
    $( Define the function which maps a set ` v ` to the set of proper
       unordered pairs consisting of exactly two (different) elements of the
       set ` v ` .  (Contributed by AV, 29-Apr-2023.) $)
    df-prpr $a |- PrPairs = ( v e. _V |-> { p | E. a e. v E. b e. v
                                            ( a =/= b /\ p = { a , b } ) } ) $.
  $}

  ${
    $d V a b p v $.  $d W a b p v $.
    $( The set of all proper unordered pairs over a given set ` V ` .
       (Contributed by AV, 29-Apr-2023.) $)
    prprval $p |- ( V e. W -> ( PrPairs ` V )
                              = { p | E. a e. V E. b e. V
                                      ( a =/= b /\ p = { a , b } ) } ) $=
      ( vv wcel cv wne cpr wceq wa wrex cab cvv cprpr ralrimivw abrexex2g mpdan
      wral df-prpr rexeq rexeqbi1dv abbidv adantl elex wss simpr ss2abi zfpair2
      weu eueqi euabex mp1i ssexg sylancr fvmptd2 ) ABGZFADHZEHZIZCHUSUTJZKZLZE
      FHZMZDVEMZCNZVDEAMZDAMZCNZOPOFCDEUAVEAKZVHVKKURVLVGVJCVFVIDVEAVDEVEAUBUCU
      DUEABUFURVICNOGZDATVKOGURVMDAURVDCNZOGZEATVMURVOEAURVNVCCNZUGVPOGZVOVDVCC
      VAVCUHUIVCCUKVQURCVBDEUJULVCCUMUNVNVPOUOUPQVDECABORSQVIDCABORSUQ $.
  $}

  ${
    $d V a b p $.  $d W a b p $.
    $( The set of all proper unordered pairs over a given set ` V ` , expressed
       by a restricted class abstraction.  (Contributed by AV, 29-Apr-2023.) $)
    prprvalpw $p |- ( V e. W -> ( PrPairs ` V )
                                = { p e. ~P V | E. a e. V E. b e. V
                                           ( a =/= b /\ p = { a , b } ) } ) $=
      ( wcel cprpr cfv cv wne cpr wceq wa wrex cab cpw crab prprval wb wss prex
      prssi eleq1 adantl bitrdi syl5ibrcom rexlimivv pm4.71ri a1i abbidv df-rab
      elpw eqtr4di eqtrd ) ABFZAGHDIZEIZJZCIZUPUQKZLZMZEANDANZCOZVCCAPZQZABCDER
      UOVDUSVEFZVCMZCOVFUOVCVHCVCVHSUOVCVGVBVGDEAAUPAFUQAFMVGVBUTATZUPUQAUBVBVG
      UTVEFZVIVAVGVJSURUSUTVEUCUDUTAUPUQUAULUEUFUGUHUIUJVCCVEUKUMUN $.

    $d P a b p $.
    $( An element of the set of all proper unordered pairs over a given set
       ` V ` is a subset of ` V ` of size two.  (Contributed by AV,
       29-Apr-2023.) $)
    prprelb $p |- ( V e. W -> ( P e. ( PrPairs ` V )
                                <-> ( P e. ~P V /\ ( # ` P ) = 2 ) ) ) $=
      ( va vb vp wcel cprpr cfv cpw cv wne cpr wceq wrex chash bitrdi wex cvv
      wa c2 crab prprvalpw eleq2d eqeq1 anbi2d 2rexbidv elrab hash2exprb prelpw
      eleq1 wb el2v biimpri biimtrdi com12 adantld pm4.71rd 2exbidv r2ex bitr2d
      bitr4di pm5.32i ) BCGZABHIZGZABJZGZDKZEKZLZAVIVJMZNZTZEBODBOZTZVHAPIUANZT
      VDVFAVKFKZVLNZTZEBODBOZFVGUBZGVPVDVEWBABCFDEUCUDWAVOFAVGVRANZVTVNDEBBWCVS
      VMVKVRAVLUEUFUGUHQVHVOVQVHVQVNERDRZVOAVGDEUIVHWDVIBGVJBGTZVNTZERDRVOVHVNW
      FDEVHVNWEVHVMWEVKVMVHWEVMVHVLVGGZWEAVLVGUKWEWGWEWGULDEVIVJBSSUJUMUNUOUPUQ
      URUSVNDEBBUTVBVAVCQ $.
  $}

  ${
    $d P a b p $.  $d X a b p $.
    $( A set is an element of the set of all proper unordered pairs over a
       given set ` X ` iff it is a pair of different elements of the set
       ` X ` .  (Contributed by AV, 7-May-2023.) $)
    prprelprb $p |- ( P e. ( PrPairs ` X ) <-> ( X e. _V
                     /\ E. a e. X E. b e. X ( P = { a , b } /\ a =/= b ) ) ) $=
      ( vp cvv wcel cprpr cv wceq wa wrex wb eleq2d reximdvva imp adantl adantr
      wi ex cfv cpr wne cpw prprvalpw eqeq1 anbi2d 2rexbidv elrab bitrdi pm3.22
      crab a1i anim2i simpr ancomd prelpwi eleq1 mpbird r19.41vv biancomi sylib
      jca impbid1 bitrd wn c0 fvprc noel pm2.21 mp1i impd impbid pm2.61i ) BFGZ
      ABHUAZGZVOACIZDIZUBZJZVRVSUCZKZDBLCBLZKZMVOVQABUDZGZWBWAKZDBLCBLZKZWEVOVQ
      AWBEIZVTJZKZDBLCBLZEWFULZGWJVOVPWOABFECDUENWNWIEAWFWKAJZWMWHCDBBWPWLWAWBW
      KAVTUFUGUHUIUJVOWJWEVOWJWEWJWDVOWGWIWDWGWHWCCDBBWHWCSWGVRBGVSBGKZKWBWAUKU
      MOPUNTWEWHWGKZDBLCBLZWJVOWDWSVOWCWRCDBBVOWQKZWCWRWTWCKZWHWGXAWAWBWTWCUOUP
      XAWGVTWFGZWTXBWCWQXBVOVRVSBUQQRWCWGXBMZWTWAXCWBAVTWFURRQUSVCTOPWSWGWIWHWG
      CDBBUTVAVBVDVEVOVFZVQAVGGZWEXDVPVGABHVHNXDXEWEXEVFXEWESXDAVIXEWEVJVKXDVOW
      DXEVOWDXESVJVLVMVEVN $.
  $}

  ${
    $d V a b p $.
    $( The set of all proper unordered pairs over a given set ` V ` is the set
       of all unordered pairs over that set of size two.  (Contributed by AV,
       29-Apr-2023.) $)
    prprspr2 $p |- ( PrPairs ` V ) = { p e. ( Pairs ` V ) | ( # ` p ) = 2 } $=
      ( va vb cvv wcel cprpr cfv cv chash c2 wceq cspr crab wa cab wrex wb a1i
      c0 wne sprval eqabrd anbi1d r19.41vv fveqeq2 hashprg el2v bitr4di pm5.32i
      cpr biancomi 2rexbidva bitr3id bitrd abbidv df-rab prprval 3eqtr4rd fvprc
      wn rab0 rabeqdv pm2.61i ) AEFZAGHZBIZJHKLZBAMHZNZLVEVGVIFZVHOZBPZCIZDIZUA
      ZVGVNVOUKZLZOZDAQCAQZBPVJVFVEVLVTBVEVLVRDAQCAQZVHOZVTVEVKWAVHVEWABVIAEBCD
      UBUCUDWBVRVHOZDAQCAQVEVTVRVHCDAAUEVEWCVSCDAAWCVSRVEVNAFVOAFOOWCVPVRVRVHVP
      VRVHVQJHKLZVPVGVQKJUFVPWDRCDVNVOEEUGUHUIUJULSUMUNUOUPVJVMLVEVHBVIUQSAEBCD
      URUSVEVAZVHBTNZTVJVFWFTLWEVHBVBSWEVHBVITAMUTVCAGUTUSVD $.
  $}

  ${
    $d V p $.  $d W p $.
    $( There is a unique proper unordered pair over a given set ` V `
       fulfilling a wff iff there is a unique unordered pair over ` V ` of size
       two fulfilling this wff.  (Contributed by AV, 30-Apr-2023.) $)
    prprsprreu $p |- ( V e. W -> ( E! p e. ( PrPairs ` V ) ph
                       <-> E! p e. ( Pairs ` V ) ( ( # ` p ) = 2 /\ ph ) ) ) $=
      ( wcel cv cprpr cfv wa weu cspr chash c2 wceq wreu wb prprspr2 reqabi a1i
      df-reu anbi1d anass bitrdi eubidv 3bitr4g ) BCEZDFZBGHZEZAIZDJUGBKHZEZUGL
      HMNZAIZIZDJADUHOUNDUKOUFUJUODUFUJULUMIZAIUOUFUIUPAUIUPPUFUMDUHUKBDQRSUAUL
      UMAUBUCUDADUHTUNDUKTUE $.
  $}

  ${
    $d V p $.  $d W p $.
    $( There is a unique proper unordered pair over a given set ` V `
       fulfilling a wff iff there is a unique subset of ` V ` of size two
       fulfilling this wff.  (Contributed by AV, 29-Apr-2023.) $)
    prprreueq $p |- ( V e. W -> ( E! p e. ( PrPairs ` V ) ph
                                <-> E! p e. ~P V ( ( # ` p ) = 2 /\ ph ) ) ) $=
      ( wcel cv cprpr cfv wa weu chash c2 wceq wreu prprelb anbi1d anass bitrdi
      cpw df-reu eubidv 3bitr4g ) BCEZDFZBGHZEZAIZDJUDBSZEZUDKHLMZAIZIZDJADUENU
      KDUHNUCUGULDUCUGUIUJIZAIULUCUFUMAUDBCOPUIUJAQRUAADUETUKDUHTUB $.
  $}

  ${
    $d a b x y p $.  $d ph x y $.  $d ps p $.
    sbcpr.x $e |- ( p = { x , y } -> ( ph <-> ps ) ) $.
    $( The proper substitution of an unordered pair for a setvar variable
       corresponds to a proper substitution of each of its elements.
       (Contributed by AV, 7-Apr-2023.) $)
    sbcpr $p |- ( [. { a , b } / p ]. ph <-> [. b / y ]. [. a / x ]. ps ) $=
      ( cv wsbc wa wex sbc5 wi wal alrimiv sbc6 sylibr exlimiv sylbi cpr weq wb
      wceq preq12 eqcomd eqeq2d biimpa syl biimpd expcom com24 imp31 vex bicomd
      expd ex com13 impcom prex impbii ) AEFIZGIZUAZJZBCVBJZDVCJZVEEIZVDUDZAKZE
      LVGAEVDMVJVGEVJDGUBZVFNZDOVGVJVLDVJVKVFVJVKKZCFUBZBNZCOVFVMVOCVIAVKVOVIVN
      VKABVIVNVKABNZVNVKKZVIVPVQVIKZABVRVHCIZDIZUAZUDZABUCVQVIWBVQVDWAVHVQWAVDV
      SVTVBVCUEUFUGUHZHUIUJUKUPULUMPBCVBFUNQRUQPVFDVCGUNQRSTVGVIANZEOVEVGWDEVGV
      KVFKZDLWDVFDVCMWEWDDVFVKWDVFVNBKZCLVKWDNZBCVBMWFWGCBVNWGBVNVKWDVIVQBAVQVI
      BANVRBAVRWBBAUCWCWBABHUOUIUJUKURUPUSSTUSSTPAEVDVBVCUTQRVA $.
  $}

  ${
    $d V a b c d p q x y $.  $d X a b c d p q x y $.  $d X p q w $.
    $d ps q w $.  $d ps a b c d q x y $.  $d th c d p q $.  $d ch c d p q $.
    reupr.a $e |- ( p = { a , b } -> ( ps <-> ch ) ) $.
    reupr.x $e |- ( p = { x , y } -> ( ps <-> th ) ) $.
    $( There is a unique unordered pair fulfilling a wff iff there are uniquely
       two sets fulfilling a corresponding wff.  (Contributed by AV,
       7-Apr-2023.) $)
    reupr $p |- ( X e. V -> ( E! p e. ( Pairs ` X ) ps
             <-> E. a e. X E. b e. X ( ch /\ A. x e. X A. y e. X
                                       ( th -> { x , y } = { a , b } ) ) ) ) $=
      ( vq cv wsbc wceq wi wa wrex wcel vw vc vd cspr cfv wreu wral cpr nfsbc1v
      sbceq1a dfsbcq reu8nf sprel biimpcd adantr ad2antlr imp pm3.22 prelspr wb
      eqeq2 imbi12d adantl rspcdv syl sbcie pm2.27 sylbir eqcom imbitrrdi com12
      zfpair2 eqcoms imbi2d syl5ibrcom a1d syl6 expimpd imp4c impcom ralrimivva
      jca ex reximdvva expcom com13 rexlimdva simprl nfv nfim preq1 preq2 rspc2
      eqeq1d sbcpr sylbi impd rexlimdvva impel ralrimiva nfcv nfralw nfan eqeq1
      ralbidv anbi12d rspce syl12anc impbid bitrid ) AHGUDUEZUFAAHMNZOZHNZXLPZQ
      ZMXKUGZRZHXKSZGFTZBCDNZENZUHZINZJNZUHZPZQZEGUGDGUGZRZJGSIGSZAXMAHUANZOHMU
      AXKAHXLUIZAHYLUIAHYLUJAHYLXLUKULXTXSYKXTXRYKHXKXNXKTZXTXRYKQZYNXNYFPZJGSI
      GSZXTYOQGXNIJUMXRXTYQYKXTXRYQYKQXTXRRZYPYJIJGGYRYDGTYEGTRZRZYPYJYTYPRZBYI
      YTYPBXRYPBQZXTYSAUUBXQYPABKUNUOUPUQUUAYHDEGGYAGTYBGTRZUUAYHUUCYRYSYPYHUUC
      XTXRYSYPYHQZQZUUCXTRZAXQUUEUUFARZXQAHYCOZXNYCPZQZUUEUUGXTUUCRZXQUUJQUUFUU
      KAUUCXTURUOUUKXPUUJMYCXKGFYAYBUSXLYCPZXPUUJUTUUKUULXMUUHXOUUIAHXLYCUKXLYC
      XNVAVBVCVDVEUUJUUDYSUUJYHYPCYCXNPZQCUUJUUMCUUJUUIUUMCUUHUUJUUIQACHYCDEVLL
      VFUUHUUIVGVHYCXNVIVJVKYPYGUUMCYGUUMUTYFXNYFXNYCVAVMVNVOVPVQVRVRVSVTWAWBWC
      WDWEWFVEVTWGXTYJXSIJGGXTYSRZYJXSUUNYJRZYFXKTZBXMYFXLPZQZMXKUGZXSUUNUUPYJG
      FYDYEUSUOUUNBYIWHUUOUURMXKUUOXLUBNZUCNZUHZPZUCGSUBGSUURXLXKTUUOUVCUURUBUC
      GGUUOUUTGTUVAGTRZRUURUVCAHUVBOZYFUVBPZQZUVDUUOUVGUVDUUNYJUVGUUNUVDYJUVGQU
      UNUVDRZBYIUVGUVHBRYICDUUTOZEUVAOZUVBYFPZQZUVGUVDYIUVLQUUNBYHUVLUVIUUTYBUH
      ZYFPZQDEUUTUVAGGUVIUVNDCDUUTUIUVNDWIWJUVJUVKEUVIEUVAUIUVKEWIWJYAUUTPZCUVI
      YGUVNCDUUTUJUVOYCUVMYFYAUUTYBWKWNVBYBUVAPZUVIUVJUVNUVKUVIEUVAUJUVPUVMUVBY
      FYBUVAUUTWLWNVBWMUPUVEUVLUVFUVEUVLUVKUVFUVEUVJUVLUVKQACDEHUBUCLWOUVJUVKVG
      WPYFUVBVIVJVKVQVRWEWQVTUVCXMUVEUUQUVFAHXLUVBUKXLUVBYFVAVBVOWRGXLUBUCUMWSW
      TXRBUUSRHYFXKBUUSHBHWIUURHMXKHXKXAXMUUQHYMUUQHWIWJXBXCYPABXQUUSKYPXPUURMX
      KYPXOUUQXMXNYFXLXDVNXEXFXGXHWCWRXIXJ $.

    $( There is a unique proper unordered pair fulfilling a wff iff there are
       uniquely two different sets fulfilling a corresponding wff.
       (Contributed by AV, 30-Apr-2023.) $)
    reuprpr $p |- ( X e. V -> ( E! p e. ( PrPairs ` X ) ps
             <-> E. a e. X E. b e. X ( a =/= b /\ ch /\ A. x e. X A. y e. X
                        ( ( x =/= y /\ th ) -> { x , y } = { a , b } ) ) ) ) $=
      ( cfv cv chash c2 wceq wa wrex cvv wcel cprpr wreu cspr wne wi prprsprreu
      cpr wral w3a fveqeq2 hashprg el2v bitr4di anbi12d reupr df-3an bicomi a1i
      wb 2rexbidv 3bitrd ) GFUAZAHGUBMUCHNZOMPQZARZHGUDMUCINZJNZUEZBRZDNZENZUEZ
      CRZVKVLUHZVGVHUHZQUFEGUIDGUIZRZJGSIGSVIBVQUJZJGSIGSAGFHUGVFVJVNDEFGHIJVDV
      PQZVEVIABVTVEVPOMPQZVIVDVPPOUKVIWAUTIJVGVHTTULUMUNKUOVDVOQZVEVMACWBVEVOOM
      PQZVMVDVOPOUKVMWCUTDEVKVLTTULUMUNLUOUPVCVRVSIJGGVRVSUTVCVSVRVIBVQUQURUSVA
      VB $.
  $}

  $( Equality for unordered pairs with partially ordered elements.
     (Contributed by AV, 9-Jul-2023.) $)
  poprelb $p |- ( ( ( Rel R /\ R Po X ) /\ ( A e. X /\ B e. X )
                                        /\ ( A R B /\ C R D ) )
                  -> ( { A , B } = { C , D } <-> ( A = C /\ B = D ) ) ) $=
    ( wrel wpo wa wcel wbr w3a cpr wceq wo cvv wb simp2 an3 wi 3adant2 preq12bg
    brrelex12 syl syl2anc idd breq12 ancoms bicomd anbi2d po2nr adantll pm2.21d
    wn ex com13 biimtrdi com23 com14 3imp jaod orc impbid1 bitrd ) EGZFEHZIZAFJ
    BFJIZABEKZCDEKZIZLZABMCDMNZACNBDNIZADNZBCNZIZOZVNVLVHCPJDPJIZVMVRQVGVHVKRVL
    VEVJIZVSVGVKVTVHVEVFVIVJSUACDEUCUDABCDFFPPUBUEVLVRVNVLVNVNVQVLVNUFVGVHVKVQV
    NTVQVHVKVGVNVQVKVHVGVNTZVQVKVIBAEKZIZVHWATVQVJWBVIVQWBVJVPVOWBVJQBCADEUGUHU
    IUJVGVHWCVNVGVHWCVNTVGVHIWCVNVFVHWCUNVEFABEUKULUMUOUPUQURUSUTVAVNVQVBVCVD
    $.

  $( The existence of an ordered pair fulfilling a wff implies the existence of
     an unordered pair fulfilling the wff.  (Contributed by AV,
     29-Jul-2023.) $)
  2exopprim $p |- ( E. a E. b ( <. A , B >. = <. a , b >. /\ ph )
                    -> E. a E. b ( { A , B } = { a , b } /\ ph ) ) $=
    ( cop cv wceq wa cpr wi cvv oppr el2v eqcomd eqcoms anim1i 2eximi ) BCFZDGZ
    EGZFZHZAIBCJZTUAJZHZAIDEUCUFAUFUBSUBSHZUEUDUGUEUDHKDETUABCLLMNOPQR $.

  ${
    $d V m n p v w $.  $d X a b i j m n p x y $.  $d X a b m n p v w x y $.
    $d i j m n p ph x y $.  $d ph v w x y $.
    $( There is a unique unordered pair with ordered elements fulfilling a wff
       if there is a unique ordered pair fulfilling the wff.  (Contributed by
       AV, 28-Jul-2023.) $)
    reuopreuprim $p |- ( X e. V -> ( E! p e. ( X X. X ) E. a E. b
                                                 ( p = <. a , b >. /\ ph )
                                 -> E! p e. ( Pairs ` X ) E. a E. b
                                                 ( p = { a , b } /\ ph ) ) ) $=
      ( vm vn cv wceq wa wex wi wral anbi1d 2exbidv nfv nfan eqeq1d wb vx vy vi
      vj vv vw cop cxp wreu wrex wcel cpr cspr cfv eqeq1 simpll simplr cvv oppr
      reuop el2v anim1i 2eximi adantr adantl nfe1 nfcv nfim nfralw nfex preq12b
      wo vex opeq1 imbi12d opeq2 rspc2v w3a wsbc pm3.22 3adant2 sbceq1a equcoms
      eqidd sylan9bb 3ad2ant2 biimpa jca32 nfsbc1v nfsbcw opeq12 eqeq2d anbi12d
      spc2ed imp pm2.27 3syl syl6 com23 3exp com24 syld com13 a1d imp42 anim1ci
      ancoms sylan9bbr prcom eqtr3id jaod biimtrid impd exlimd ralrimivva preq1
      ex imbi2d 2ralbidv preq2 rspc2ev syl112anc rexlimivv reupr imbitrrid ) DI
      ZEIZFIZUGZJZAKZFLELZDCCUHUIUAIZUBIZUGZYIJZAKZFLZELZUCIZUDIZUGZYIJZAKZFLZE
      LZUUBYOJZMZUDCNZUCCNZKZUBCUJUACUJZCBUKZYFYGYHULZJZAKZFLELZDCUMUNUIZYLYSUU
      FUCUDCCDUAUBYFYOJZYKYQEFUUSYJYPAYFYOYIUOOPYFUUBJZYKUUDEFUUTYJUUCAYFUUBYIU
      OOPUTUULUURUUMUEIZUFIZULZUUNJZAKZFLELZGIZHIZULZUUNJZAKZFLZELZUVIUVCJZMZHC
      NGCNZKZUFCUJUECUJZUUKUVRUAUBCCYMCUKZYNCUKZKZUUKUVRUWAUUKKZUVSUVTYMYNULZUU
      NJZAKZFLELZUVMUVIUWCJZMZHCNGCNZUVRUVSUVTUUKUPUVSUVTUUKUQUUKUWFUWAYSUWFUUJ
      YQUWEEFYPUWDAYPUWDMUAUBYMYNYGYHURURUSVAVBVCVDVEUWBUWHGHCCUWBUVGCUKZUVHCUK
      ZKZKZUVLUWGEUWBUWLEUWAUUKEUWAEQYSUUJEYREVFUUIEUCCECVGZUUHEUDCUWNUUFUUGEUU
      EEVFUUGEQVHVIVIRRUWLEQRUWGEQUWMUVKUWGFUWBUWLFUWAUUKFUWAFQYSUUJFYRFEYQFVFV
      JUUIFUCCFCVGZUUHFUDCUWOUUFUUGFUUEFEUUDFVFVJUUGFQVHVIVIRRUWLFQRUWGFQUWMUVJ
      AUWGUVJUVGYGJZUVHYHJZKZUVGYHJZUVHYGJZKZVLUWMAUWGMZUVGUVHYGYHGVMHVMEVMFVMV
      KUWMUWRUXBUXAUWAYSUUJUWLUWRUXBMZUWAUUJUWLUXCMMYSUWLUUJUWAUXCUWLUUJUVGUVHU
      GZYIJZAKZFLELZUXDYOJZMZUWAUXCMUUHUXIUVGUUAUGZYIJZAKZFLELZUXJYOJZMUCUDUVGU
      VHCCYTUVGJZUUFUXMUUGUXNUXOUUDUXLEFUXOUUCUXKAUXOUUBUXJYIYTUVGUUAVNZSOPUXOU
      UBUXJYOUXPSVOUUAUVHJZUXMUXGUXNUXHUXQUXLUXFEFUXQUXKUXEAUXQUXJUXDYIUUAUVHUV
      GVPZSOPUXQUXJUXDYOUXRSVOVQUWLUWRUWAUXIUXBUWLUWRUWAUXIUXBMUWLUWRUWAVRZAUXI
      UWGUXSAUXIUWGMUXSAKZUXIUXHUWGUXTUWAUWLKZUXDUXDJZAEUVGVSZFUVHVSZKZKUXGUXIU
      XHMUXTUYAUYBUYDUXSUYAAUWLUWAUYAUWRUWLUWAVTWAVDUXTUXDWDUXSAUYDUWRUWLAUYDTU
      WAUWPAUYCUWQUYDAUYCTEGAEUVGWBZWCUYCUYDTFHUYCFUVHWBZWCWEWFWGWHUYAUYEUXGUWA
      UXFUYEEFUVGUVHCCUYBUYDEUYBEQUYCEFUVHEUVHVGAEUVGWIWJRUYBUYDFUYBFQUYCFUVHWI
      RYGUVGJZYHUVHJZKZUXFUYETUWAUYJUXEUYBAUYDUYJYIUXDUXDYGYHUVGUVHWKWLUYHAUYCU
      YIUYDUYFUYGWEWMVEWNWOUXGUXHWPWQUXHUWGMGHUVGUVHYMYNURURUSVAWRXQWSWTXAXBXCX
      DXEUWAYSUUJUWLUXAUXBMZUWAUUJUWLUYKMMYSUWLUUJUWAUYKUWLUUJUVHUVGUGZYIJZAKZF
      LELZUYLYOJZMZUWAUYKMUWKUWJUUJUYQMUUHUYQUVHUUAUGZYIJZAKZFLELZUYRYOJZMUCUDU
      VHUVGCCYTUVHJZUUFVUAUUGVUBVUCUUDUYTEFVUCUUCUYSAVUCUUBUYRYIYTUVHUUAVNZSOPV
      UCUUBUYRYOVUDSVOUUAUVGJZVUAUYOVUBUYPVUEUYTUYNEFVUEUYSUYMAVUEUYRUYLYIUUAUV
      GUVHVPZSOPVUEUYRUYLYOVUFSVOVQXGUWLUXAUWAUYQUXBUWLUXAUWAUYQUXBMUWLUXAUWAVR
      ZAUYQUWGVUGAUYQUWGMVUGAKZUYQUYPUWGVUHUWAUWKUWJKZKZUYLUYLJZAFUVGVSZEUVHVSZ
      KZKUYOUYQUYPMVUHVUJVUKVUMVUGVUJAUWLUWAVUJUXAUWLVUIUWAUWJUWKVTXFWAVDVUHUYL
      WDVUGAVUMUXAUWLAVUMTUWAUWSAVULUWTVUMAVULTFGAFUVGWBZWCVULVUMTEHVULEUVHWBZW
      CWEWFWGWHVUJVUNUYOUWAUYNVUNEFUVHUVGCCVUKVUMEVUKEQVULEUVHWIRVUKVUMFVUKFQVU
      LFEUVHFUVHVGAFUVGWIWJRYGUVHJZYHUVGJZKZUYNVUNTUWAVUSUYMVUKAVUMVUSYIUYLUYLY
      GYHUVHUVGWKWLVURAVULVUQVUMVUOVUPXHWMVEWNWOUYOUYPWPWQUYPUVIUVHUVGULZUWCUVH
      UVGXIUYPVUTUWCJMHGUVHUVGYMYNURURUSVAXJWRXQWSWTXAXBXCXDXEXKXLXMXNXNXOUVQUW
      FUWIKYMUVBULZUUNJZAKZFLELZUVMUVIVVAJZMZHCNGCNZKUEUFYMYNCCUVAYMJZUVFVVDUVP
      VVGVVHUVEVVCEFVVHUVDVVBAVVHUVCVVAUUNUVAYMUVBXPZSOPVVHUVOVVFGHCCVVHUVNVVEU
      VMVVHUVCVVAUVIVVIWLXRXSWMUVBYNJZVVDUWFVVGUWIVVJVVCUWEEFVVJVVBUWDAVVJVVAUW
      CUUNUVBYNYMXTZSOPVVJVVFUWHGHCCVVJVVEUWGUVMVVJVVAUWCUVIVVKWLXRXSWMYAYBXQYC
      UUQUVFUVMGHBCDUEUFYFUVCJZUUPUVEEFVVLUUOUVDAYFUVCUUNUOOPYFUVIJZUUPUVKEFVVM
      UUOUVJAYFUVIUUNUOOPYDYEXL $.
  $}
