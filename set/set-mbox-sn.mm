$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Steven Nguyen
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Utility theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    jarrii.1 $e |- ps $.
    jarrii.2 $e |- ( ( ph -> ps ) -> ch ) $.
    $( Inference associated with ~ jarri .  A consequence of ~ ax-mp and
       ~ ax-1 .  (Contributed by SN, 14-Oct-2025.) $)
    jarrii $p |- ch $=
      ( wi a1i ax-mp ) ABFCBADGEH $.
    $( $j usage 'jarrii' avoids 'ax-2'; $)
  $}

  $( Introduction of conjunct inside of a contradiction.  Would be used in
     ~ elfvov1 .  (Contributed by SN, 18-May-2025.) $)
  intnanrt $p |- ( -. ph -> -. ( ph /\ ps ) ) $=
    ( wa simpl con3i ) ABCAABDE $.

  ${
    ioin9i8.1 $e |- ( ph -> ( ps \/ ch ) ) $.
    ioin9i8.2 $e |- ( ch -> -. th ) $.
    ioin9i8.3 $e |- ( ps -> th ) $.
    $( Miscellaneous inference creating a biconditional from an implied
       converse implication.  (Contributed by Steven Nguyen, 17-Jul-2022.) $)
    ioin9i8 $p |- ( ph -> ( ps <-> th ) ) $=
      ( wn ord syl6 con4d impbid2 ) ABDGABDABHCDHABCEIFJKL $.
  $}

  ${
    jaodd.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    jaodd.2 $e |- ( ph -> ( ps -> ( ta -> th ) ) ) $.
    $( Double deduction form of ~ jaoi .  (Contributed by Steven Nguyen,
       17-Jul-2022.) $)
    jaodd $p |- ( ph -> ( ps -> ( ( ch \/ ta ) -> th ) ) ) $=
      ( wi wo jao syl6c ) ABCDHEDHCEIDHFGCDEJK $.
  $}

  ${
    syl3an12.1 $e |- ( ph -> ps ) $.
    syl3an12.2 $e |- ( ch -> th ) $.
    syl3an12.s $e |- ( ( ps /\ th /\ ta ) -> et ) $.
    $( A double syllogism inference.  (Contributed by SN, 15-Sep-2024.) $)
    syl3an12 $p |- ( ( ph /\ ch /\ ta ) -> et ) $=
      ( id syl3an ) ABCDEEFGHEJIK $.
  $}

  ${
    exbiii.1 $e |- E. x ph $.
    exbiii.2 $e |- ( ph <-> ps ) $.
    $( Inference associated with ~ exbii .  Weaker version of ~ eximii .
       (Contributed by SN, 14-Oct-2025.) $)
    exbiii $p |- E. x ps $=
      ( biimpi eximii ) ABCDABEFG $.
  $}

  ${
    $d x ph $.
    sbtd.1 $e |- ( ph -> ps ) $.
    $( A true statement is true upon substitution (deduction).  A similar proof
       is possible for ~ icht .  (Contributed by SN, 4-May-2024.) $)
    sbtd $p |- ( ph -> [ t / x ] ps ) $=
      ( wal wsb alrimiv stdpc4 syl ) ABCFBCDGABCEHBCDIJ $.
  $}

  $( One direction of ~ sbor , using fewer axioms.  Compare ~ 19.33 .
     (Contributed by Steven Nguyen, 18-Aug-2023.) $)
  sbor2 $p |- ( ( [ t / x ] ph \/ [ t / x ] ps ) -> [ t / x ] ( ph \/ ps ) ) $=
    ( wsb wo orc sbimi olc jaoi ) ACDEABFZCDEBCDEAKCDABGHBKCDBAIHJ $.

  ${
    $d x y $.
    sbalexi.1 $e |- E. x ( x = y /\ ph ) $.
    $( Inference form of ~ sbalex , avoiding ~ ax-10 by using ~ ax-gen .
       (Contributed by SN, 12-Aug-2025.) $)
    sbalexi $p |- A. x ( x = y -> ph ) $=
      ( weq wi wa wex ax12ev2 ax-mp ax-gen ) BCEZAFZBLAGBHMDABCIJK $.
    $( $j usage 'sbalexi' avoids 'ax-10'; $)
  $}

  ${
    nfalh.1 $e |- ( ph -> A. x ph ) $.
    $( Version of ~ nfal with an 'h' hypothesis, avoiding ~ ax-12 .
       (Contributed by SN, 11-Feb-2026.) $)
    nfalh $p |- F/ x A. y ph $=
      ( wal hbal nf5i ) ACEBABCDFG $.
    $( $j usage 'nfalh' avoids 'ax-12'; $)
  $}

  $( An inner existential quantifier's variable is bound.  (Contributed by SN,
     11-Feb-2026.) $)
  nfe2 $p |- F/ x E. y E. x ph $=
    ( wex excom nfe1 nfxfr ) ABDCDACDZBDBACBEHBFG $.
  $( $j usage 'nfe2' avoids 'ax-12'; $)

  $( An inner existential quantifier's variable is bound.  (Contributed by SN,
     11-Feb-2026.) $)
  nfale2 $p |- F/ x A. y E. x ph $=
    ( wex hbe1 nfalh ) ABDBCABEF $.
  $( $j usage 'nfale2' avoids 'ax-12'; $)

  ${
    $d ph y $.
    19.9dev.1 $e |- ( ph -> F/ x ps ) $.
    $( ~ 19.9d in the case of an existential quantifier, avoiding the ~ ax-10
       from ~ nfex that would be used for the hypothesis of ~ 19.9d , at the
       cost of an additional DV condition on ` y ` , ` ph ` .  (Contributed by
       SN, 26-May-2024.) $)
    19.9dev $p |- ( ph -> ( E. x E. y ps <-> E. y ps ) ) $=
      ( wex excom wnf wb 19.9t syl exbidv bitrid ) BDFZCFBCFZDFANBCDGAOBDABCHOB
      IEBCJKLM $.
    $( $j usage '19.9dev' avoids 'ax-10'; $)
  $}

  ${
    $d ph x y z $.  $d ch x $.  $d th y $.  $d ta z $.  $d D x y z $.
    $d A x y z $.  $d B y z $.  $d C z $.
    3rspcedvd.a $e |- ( ph -> A e. D ) $.
    3rspcedvd.b $e |- ( ph -> B e. D ) $.
    3rspcedvd.c $e |- ( ph -> C e. D ) $.
    3rspcedvd.1 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
    3rspcedvd.2 $e |- ( ( ph /\ y = B ) -> ( ch <-> th ) ) $.
    3rspcedvd.3 $e |- ( ( ph /\ z = C ) -> ( th <-> ta ) ) $.
    3rspcedvd.4 $e |- ( ph -> ta ) $.
    $( Triple application of ~ rspcedvd .  (Contributed by Steven Nguyen,
       27-Feb-2023.) $)
    3rspcedvd $p |- ( ph -> E. x e. D E. y e. D E. z e. D ps ) $=
      ( wrex cv wceq wa 2rexbidv rexbidv rspcedvd ) ABHLTGLTCHLTZGLTFILMAFUAIUB
      UCBCGHLLPUDAUGDHLTGJLNAGUAJUBUCCDHLQUEADEHKLORSUFUFUF $.
  $}

  ${
    $d w x y z $.  $d y ph $.
    $( A condensed form of ~ axrep5 .  (Contributed by SN, 21-Sep-2023.) $)
    sn-axrep5v $p |-
              ( A. w e. x E* z ph -> E. y A. z ( z e. y <-> E. w e. x ph ) ) $=
      ( wel wa wmo wal cv wrex wb wex wral axrep6 wi albii exbii dfmo 3bitr4i
      weq 19.37v impexp 19.21v bitri imbi2i df-ral rexanid bibi2i 3imtr3i ) EBF
      ZAGZDHZEIZDCFZULEBJZKZLZDIZCMADHZEUPNZUOAEUPKZLZDIZCMULBCDEOULDCUAZPZDIZC
      MZEIUKUTPZEIUNVAVHVIEUKAVEPZDIZPZCMUKVKCMZPVHVIUKVKCUBVGVLCVGUKVJPZDIVLVF
      VNDUKAVEUCQUKVJDUDUERUTVMUKADCSUFTQUMVHEULDCSQUTEUPUGTUSVDCURVCDUQVBUOAEU
      PUHUIQRUJ $.
  $}

  ${
    $d w x y z $.  $d y z ph $.  $d a y z $.  $d b y z $.
    $( ~ axprlem3 using only Tarski's FOL axiom schemes and ~ ax-rep .
       (Contributed by SN, 22-Sep-2023.) $)
    sn-axprlem3 $p |-
               E. y A. z ( z e. y <-> E. w e. x if- ( ph , z = a , z = b ) ) $=
      ( weq wif wal wex ax6evr biimpd equtrr sylan9r alrimiv expcom eximdv mpi
      wa wmo wel cv wrex wb axrep6 wi ifptru wn ifpfal pm2.61i dfmo mpbir mpg )
      ADFHZDGHZIZDUAZDCUBUQEBUCUDUEDJCKEUQBCDEUFURUQDCHZUGZDJZCKZAVBAFCHZCKVBCF
      LAVCVACVCAVAVCATUTDAUQUOVCUSAUQUOAUOUPUHMFCDNOPQRSAUIZGCHZCKVBCGLVDVEVACV
      EVDVAVEVDTUTDVDUQUPVEUSVDUQUPAUOUPUJMGCDNOPQRSUKUQDCULUMUN $.
  $}

  ${
    $d w x y z $.
    $( Alternate proof of ~ exel , avoiding ~ ax-pr but requiring ~ ax-5 ,
       ~ ax-9 , and ~ ax-pow .  This is similar to how ~ elALT2 uses ~ ax-pow
       instead of ~ ax-pr compared to ~ el .  (Contributed by SN, 18-Sep-2023.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sn-exelALT $p |- E. y E. x x e. y $=
      ( vw vz wel wi wal wex ax-pow weq ax6ev ax9v1 alrimiv eximii exim mpi ) C
      AECDEFZCGZABEZFAGZSAHZBDBACITRAHUAADJZRAADKUBQCADCLMNRSAOPN $.
    $( $j usage 'sn-exelALT' avoids 'ax-7' 'ax-8' 'ax-ext' 'ax-sep' 'ax-nul'
       'ax-pr'; $)
  $}

  ${
    $d ph x $.  $d A x $.
    ssabdv.1 $e |- ( ph -> ( x e. A -> ps ) ) $.
    $( Deduction of abstraction subclass from implication.  (Contributed by SN,
       22-Dec-2024.) $)
    ssabdv $p |- ( ph -> A C_ { x | ps } ) $=
      ( cv wcel cab abid1 ss2abdv eqsstrid ) ADCFDGZCHBCHCDIALBCEJK $.
  $}

  ${
    $d w x y z $.  $d ph w y z $.
    $( An unused lemma showing that many equivalences involving ~ df-iota are
       potentially provable without ~ ax-10 , ~ ax-11 , ~ ax-12 .  (Contributed
       by SN, 6-Nov-2024.) $)
    sn-iotalem $p |- { y | { x | ph } = { y } } =
               { z | { y | { x | ph } = { y } } = { z } } $=
      ( vw cab cv csn wceq wcel weq eqeq1 wb cvv sneqbg elv equcom eqeq2d elabg
      sneq bitri bitrdi velsn 3bitr4g eqrdv vsnid eleq2 mpbiri impbii 3bitr4i
      sylib eqriv ) EABFZCGZHZIZCFZUQDGZHZIZDFZUMEGZHZIZUQVCIZVBUQJZVBVAJZVDVEV
      DDUQVCVDUMUSIZDEKZURUQJZURVCJVDVHVCUSIZVIUMVCUSLVKEDKZVIVKVLMEVBURNOPEDQU
      AUBVJVHMDUPVHCURNCDKUOUSUMUNURTRSPDVBUCUDUEVEVFVDVEVFVBVCJEUFUQVCVBUGUHVF
      VDMEUPVDCVBNCEKUOVCUMUNVBTRSPZUKUIVMVGVEMEUTVEDVBNVIUSVCUQURVBTRSPUJUL $.
    $( $j usage 'sn-iotalem' avoids 'ax-10' 'ax-11' 'ax-12'; $)

    $( Corollary of ~ sn-iotalem .  Compare ~ sb8iota .  (Contributed by SN,
       6-Nov-2024.) $)
    sn-iotalemcor $p |- ( iota x ph ) = ( iota y { x | ph } = { y } ) $=
      ( vz cab cv csn wceq cuni cio sn-iotalem unieqi df-iota 3eqtr4i ) ABECFGH
      ZCEZIPDFGHDEZIABJOCJPQABCDKLABCMOCDMN $.
  $}

  ${
    $d x y $.
    $( Originally part of ~ uniabio .  Convert a theorem about ~ df-iota to one
       about ~ dfiota2 , without ~ ax-10 , ~ ax-11 , ~ ax-12 .  Although, ~ eu6
       uses ~ ax-10 and ~ ax-12 .  (Contributed by SN, 23-Nov-2024.) $)
    abbi1sn $p |- ( A. x ( ph <-> x = y ) -> { x | ph } = { y } ) $=
      ( weq wb wal cab cv csn abbi df-sn eqtr4di ) ABCDZEBFABGMBGCHZIAMBJBNKL
      $.
  $}

  $( Move a relation inside and outside the conditional operator.  (Contributed
     by SN, 14-Aug-2024.) $)
  brif2 $p |- ( C R if ( ph , A , B ) <-> if- ( ph , C R A , C R B ) ) $=
    ( cif wbr iftrue breq2d wn iffalse casesifp ) ADABCFZEGDBEGDCEGAMBDEABCHIAJ
    MCDEABCKIL $.

  $( Move a relation inside and outside the conditional operator.  (Contributed
     by SN, 14-Aug-2024.) $)
  brif12 $p |-
    ( if ( ph , A , B ) R if ( ph , C , D ) <-> if- ( ph , A R C , B R D ) ) $=
    ( cif wbr iftrue breq12d wn iffalse casesifp ) AABCGZADEGZFHBDFHCEFHANBODFA
    BCIADEIJAKNCOEFABCLADELJM $.

  $( The proper subset of a set is also a set.  (Contributed by Steven Nguyen,
     17-Jul-2022.) $)
  pssexg $p |- ( ( A C. B /\ B e. C ) -> A e. _V ) $=
    ( wpss wss wcel cvv pssss ssexg sylan ) ABDABEBCFAGFABHABCIJ $.

  $( A proper superset is nonempty.  (Contributed by Steven Nguyen,
     17-Jul-2022.) $)
  pssn0 $p |- ( A C. B -> B =/= (/) ) $=
    ( wpss c0 wceq npss0 psseq2 mtbiri necon2ai ) ABCZBDBDEJADCAFBDAGHI $.

  $( Classes are proper subclasses if and only if their power classes are
     proper subclasses.  (Contributed by Steven Nguyen, 17-Jul-2022.) $)
  psspwb $p |- ( A C. B <-> ~P A C. ~P B ) $=
    ( wss wne wa cpw wpss sspwb pweqb necon3bii anbi12i df-pss 3bitr4i ) ABCZAB
    DZEAFZBFZCZPQDZEABGPQGNROSABHABPQABIJKABLPQLM $.

  $( Proper subset theorem for Cartesian product.  (Contributed by Steven
     Nguyen, 17-Jul-2022.) $)
  xppss12 $p |- ( ( A C. B /\ C C. D ) -> ( A X. C ) C. ( B X. D ) ) $=
    ( wpss wa cxp wss wne pssss xpss12 syl2an wn simpl pssne necomd neneq pssn0
    wceq c0 intnanrd 3syl wb xp11 mtbird neqne syl df-pss sylanbrc ) ABEZCDEZFZ
    ACGZBDGZHZUMUNIZUMUNEUJABHCDHUOUKABJCDJABCDKLULUNUMSZMZUPULUQBASZDCSZFZULUJ
    BAIZVAMUJUKNUJABABOPVBUSUTBAQUAUBUJBTIDTIUQVAUCUKABRCDRBDACUDLUEURUNUMUNUMU
    FPUGUMUNUHUI $.

  ${
    elpwbi.1 $e |- B e. _V $.
    $( Membership in a power set, biconditional.  (Contributed by Steven
       Nguyen, 17-Jul-2022.)  (Proof shortened by Steven Nguyen,
       16-Sep-2022.) $)
    elpwbi $p |- ( A C_ B <-> A e. ~P B ) $=
      ( cpw wcel wss elpw2 bicomi ) ABDEABFABCGH $.
  $}

  ${
    $d x y A $.
    $( The image of a class of ordered pairs.  (Contributed by Steven Nguyen,
       6-Jun-2023.) $)
    imaopab $p |- ( { <. x , y >. | ph } " A ) = { y | E. x e. A ph } $=
      ( copab cima cres crn cv wcel wa wrex cab df-ima resopab rneqi wex rnopab
      df-rex abbii eqtr4i 3eqtri ) ABCEZDFUCDGZHBIDJAKZBCEZHZABDLZCMZUCDNUDUFAB
      CDOPUGUEBQZCMUIUEBCRUHUJCABDSTUAUB $.
  $}

  ${
    eqresfnbd.g $e |- ( ph -> F Fn B ) $.
    eqresfnbd.1 $e |- ( ph -> A C_ B ) $.
    $( Property of being the restriction of a function.  Note that this is
       closer to ~ funssres than ~ fnssres .  (Contributed by SN,
       11-Mar-2025.) $)
    eqresfnbd $p |- ( ph -> ( R = ( F |` A ) <-> ( R Fn A /\ R C_ F ) ) ) $=
      ( cres wceq wfn wss wa fnssresd resss jctir fneq1 anbi12d syl5ibrcom wfun
      sseq1 fnfund adantr cdm funssres eqcomd fndm adantl eqeq2d imbitrid mpand
      reseq2d expimpd impbid ) ADEBHZIZDBJZDEKZLZAURUOUNBJZUNEKZLAUSUTACBEFGMEB
      NOUOUPUSUQUTBDUNPDUNETQRAUPUQUOAUPLZESZUQUOAVBUPACEFUAUBVBUQLZDEDUCZHZIVA
      UOVCVEDEDUDUEVAVEUNDVAVDBEUPVDBIABDUFUGUKUHUIUJULUM $.
  $}

  ${
    $d u v w x y B $.  $d u w x y z C $.  $d x y ph $.  $d u v w x y S $.
    $d u v w x y A $.  $d u v w z R $.  $d z T $.
    fmpocos.1 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> R e. C ) $.
    fmpocos.2 $e |- ( ph -> F = ( x e. A , y e. B |-> R ) ) $.
    fmpocos.3 $e |- ( ph -> G = ( z e. C |-> S ) ) $.
    fmpocos.4 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> [_ R / z ]_ S = T ) $.
    $( Composition of two functions.  Variation of ~ fmpoco with more context
       in the substitution hypothesis for ` T ` .  (Contributed by SN,
       14-Mar-2025.) $)
    fmpocos $p |- ( ph -> ( G o. F ) = ( x e. A , y e. B |-> T ) ) $=
      ( vw vu vv csb ccom cxp c2nd cfv c1st cmpt cmpo wcel wral ralrimivva eqid
      cv wf fmpo sylib nfcv nfcsb1v nfcsbw weq csbeq1a sylan9eq cbvmpo cop wceq
      op2ndd op1std csbeq1d csbeq12dv mpompt eqtr4i sylibr eqtrdi fmptcos 3impb
      vex fmpt wa mpoeq3dva eqtrid eqtrd ) ALKUAQEFUBZDCQULZUCUDZBWBUEUDZHTZTZI
      TZUFZBCEFJUGZAQDWAGWFIKLAWAGBCEFHUGZUMZWFGUHQWAUIAHGUHZCFUIBEUIWKAWLBCEFM
      UJBCEFHGWJWJUKUNUOQWAGWFWJWJRSEFCSULZBRULZHTZTZUGQWAWFUFZBCRSEFHWPRHUPSHU
      PBCWMWOBWMUPBWNHUQURZCWMWOUQZBRUSZCSUSZHWOWPBWNHUTCWMWOUTVAZVBRSQEFWFWPWB
      WNWMVCVDZCWCWEWMWOWNWMWBRVOZSVOZVEXCBWDWNHWNWMWBXDXEVFVGVHZVIVJZVPVKAKWJW
      QNXGVLOVMAWHBCEFDHITZUGZWIWHRSEFDWPITZUGXIRSQEFWGXJXCDWFWPIXFVGVIBCRSEFXH
      XJRXHUPSXHUPBDWPIWRBIUPURCDWPIWSCIUPURWTXAVQDHWPIXBVGVBVJABCEFXHJABULEUHC
      ULFUHXHJVDPVNVRVSVT $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d S x y $.  $d ph x y $.
    ovmpogad.f $e |- F = ( x e. C , y e. D |-> R ) $.
    ovmpogad.s $e |- ( ( x = A /\ y = B ) -> R = S ) $.
    ovmpogad.1 $e |- ( ph -> A e. C ) $.
    ovmpogad.2 $e |- ( ph -> B e. D ) $.
    ovmpogad.v $e |- ( ph -> S e. V ) $.
    $( Value of an operation given by a maps-to rule.  Deduction form of
       ~ ovmpoga .  (Contributed by SN, 14-Mar-2025.) $)
    ovmpogad $p |- ( ph -> ( A F B ) = S ) $=
      ( cmpo wceq a1i cv wa adantl ovmpod ) ABCDEFGHIJKJBCFGHQRALSBTDRCTERUAHIR
      AMUBNOPUC $.
  $}

  ${
    $d ph x $.  $d A x $.  $d B x $.  $d C x $.  $d D x $.  $d M x $.
    $d N x $.  $d R x $.
    ofun.a $e |- ( ph -> A Fn M ) $.
    ofun.b $e |- ( ph -> B Fn M ) $.
    ofun.c $e |- ( ph -> C Fn N ) $.
    ofun.d $e |- ( ph -> D Fn N ) $.
    ofun.m $e |- ( ph -> M e. V ) $.
    ofun.n $e |- ( ph -> N e. W ) $.
    ofun.1 $e |- ( ph -> ( M i^i N ) = (/) ) $.
    $( A function operation of unions of disjoint functions is a union of
       function operations.  (Contributed by SN, 16-Jun-2024.) $)
    ofun $p |- ( ph ->
         ( ( A u. C ) oF R ( B u. D ) ) = ( ( A oF R B ) u. ( C oF R D ) ) ) $=
      ( co cfv adantr vx cun cof cvv fnund unexd inidm offn cv wcel eqidd ofval
      wa wo wceq wfn cin c0 simpr fvun1d oveq12d 3eqtr4rd fvun2d jaodan sylan2b
      elun eqtrd eqfnfvd ) AUAGHUBZBDUBZCEUBZFUCZRZBCVLRZDEVLRZUBZAVIVIFVIVJVKU
      DUDAGHBDKMQUEZAGHCELNQUEZAGHIJOPUFZVSVIUGZUHAGHVNVOAGGFGBCIIKLOOGUGZUHZAH
      HFHDEJJMNPPHUGZUHZQUEAUAUIZVIUJZUMZWEVMSWEVJSZWEVKSZFRZWEVPSZAVIVIWHWIFVI
      VJVKUDUDWEVQVRVSVSVTWGWHUKWGWIUKULWFAWEGUJZWEHUJZUNWJWKUOZWEGHVFAWLWNWMAW
      LUMZWEVNSWEBSZWECSZFRWKWJAGGWPWQFGBCIIWEKLOOWAWOWPUKWOWQUKULWOGHVNVOWEAVN
      GUPZWLWBTAVOHUPZWLWDTAGHUQURUOZWLQTZAWLUSZUTWOWHWPWIWQFWOGHBDWEABGUPZWLKT
      ADHUPZWLMTXAXBUTWOGHCEWEACGUPZWLLTAEHUPZWLNTXAXBUTVAVBAWMUMZWEVOSWEDSZWEE
      SZFRWKWJAHHXHXIFHDEJJWEMNPPWCXGXHUKXGXIUKULXGGHVNVOWEAWRWMWBTAWSWMWDTAWTW
      MQTZAWMUSZVCXGWHXHWIXIFXGGHBDWEAXCWMKTAXDWMMTXJXKVCXGGHCEWEAXEWMLTAXFWMNT
      XJXKVCVAVBVDVEVGVH $.
  $}

  ${
    $d x y A $.  $d x y R $.
    $( Alternate definition of quotient set.  (Contributed by Steven Nguyen,
       7-Jun-2023.) $)
    dfqs3 $p |- ( A /. R ) = U_ x e. A { [ x ] R } $=
      ( vy cqs cv cec wceq wrex cab csn ciun df-qs iunsn eqtr4i ) BCEDFAFCGZHAB
      IDJABPKLADBCMADBPNO $.
  $}

  ${
    qseq12d.1 $e |- ( ph -> A = B ) $.
    qseq12d.2 $e |- ( ph -> C = D ) $.
    $( Equality theorem for quotient set, deduction form.  (Contributed by
       Steven Nguyen, 30-Apr-2023.) $)
    qseq12d $p |- ( ph -> ( A /. C ) = ( B /. D ) ) $=
      ( wceq cqs qseq12 syl2anc ) ABCHDEHBDICEIHFGBCDEJK $.
  $}

  ${
    $d ph a x y $.  $d a x y A $.  $d a x y .~ $.  $d a y N $.
    qsalrel.1 $e |- ( ( ph /\ ( x e. A /\ y e. A ) ) -> x .~ y ) $.
    qsalrel.2 $e |- ( ph -> .~ Er A ) $.
    qsalrel.3 $e |- ( ph -> N e. A ) $.
    $( The quotient set is equal to the singleton of ` A ` when all elements
       are related and ` A ` is nonempty.  (Contributed by SN, 8-Jun-2023.) $)
    qsalrel $p |- ( ph -> ( A /. .~ ) = { A } ) $=
      ( va cv cec cmpt crn csn wcel adantr wbr wral wb cqs dfqs2 wer ralrimivva
      wa simpr weq breq1 ralbidv adantl rspcdv wi wceq breq2 syld mpd mpteq2dva
      erthi rneqd eqid ne0d rnmptc ecss ersym elecg syl2anc mpbird sneqd 3eqtrd
      eqelssd eqtrid ) ADEUAJDJKZELZMZNZDOZJDEUBAVOJDFELZMZNVQOVPAVNVRAJDVMVQAV
      LDPZUEZVLFEDADEUCVSHQZVTBKZCKZERZCDSZBDSZVLFERZAWFVSAWDBCDDGUDQVTWFVLWCER
      ZCDSZWGVTWEWIBVLDAVSUFZBJUGZWEWITVTWKWDWHCDWBVLWCEUHUIUJUKAWIWGULVSAWHWGC
      FDIWCFUMWHWGTAWCFVLEUNUJUKQUOUPZURUQUSAJDVQVRVRUTADFIVAVBAVQDAJVQDAFEDHVC
      VTVLVQPZFVLERZVTVLFEDWAWLVDVTVSFDPZWMWNTWJAWOVSIQVLFEDDVEVFVGVJVHVIVK $.
  $}

  ${
    $d A v w x y z $.  $d B v w x y z $.  $d .< v w x y z $.  $d ph v $.
    supinf.1 $e |- ( ph -> .< Or A ) $.
    supinf.2 $e |- ( ph -> E. x e. A (
      A. y e. B -. x .< y /\ A. y e. A ( y .< x -> E. z e. B y .< z ) ) ) $.
    $( The supremum is the infimum of the upper bounds.  (Contributed by SN,
       29-Jun-2025.) $)
    supinf $p |- ( ph -> sup ( B , A , .< ) =
                         inf ( { x e. A | A. w e. B -. x .< w } , A , .< ) ) $=
      ( vv cv wbr wn wral breq1 notbid ralbidv wa wrex crab cinf supcl ralrimiv
      csup wceq supub breq2 cbvralvw sylib elrabd wcel elrab wi cbvrexvw imbi2i
      weq ralbii anbi2i rexbii supnub biimtrid imp infmin eqcomd ) ABLZELZHMZNZ
      EGOZBFUAZFHUBGFHUEZAKFVKVLHIABCDFGHIJUCZAVJVLVGHMZNZEGOZBVLFVFVLUFZVIVOEG
      VQVHVNVFVLVGHPQRVMAVLKLZHMZNZKGOVPAVTKGABCDFGVRHIJUGUDVTVOKEGKEUQVSVNVRVG
      VLHUHQUIUJUKAVRVKULZVRVLHMNZWAVRFULVRVGHMZNZEGOZSAWBVJWEBVRFBKUQZVIWDEGWF
      VHWCVFVRVGHPQRUMABCEFGVRHIAVFCLZHMNCGOZWGVFHMZWGDLZHMZDGTZUNZCFOZSZBFTWHW
      IWGVGHMZEGTZUNZCFOZSZBFTJWOWTBFWNWSWHWMWRCFWLWQWIWKWPDEGWJVGWGHUHUOUPURUS
      UTUJVAVBVCVDVE $.
  $}

  ${
    mapcod.1 $e |- ( ph -> F e. ( A ^m B ) ) $.
    mapcod.2 $e |- ( ph -> G e. ( B ^m C ) ) $.
    $( Compose two mappings.  (Contributed by SN, 11-Mar-2025.) $)
    mapcod $p |- ( ph -> ( F o. G ) e. ( A ^m C ) ) $=
      ( ccom cvv wcel cmap co wa elmapex syl simpld simprd wf elmapi elmapdd
      fcod ) ABDEFIJJABJKZCJKZAEBCLMKZUCUDNGEBCOPQAUDDJKZAFCDLMKZUDUFNHFCDOPRAD
      CBEFAUECBESGEBCTPAUGDCFSHFCDTPUBUA $.
  $}

  $( A finite set is dominated by the set of natural numbers.  (Contributed by
     SN, 6-Jul-2025.) $)
  fisdomnn $p |- ( A e. Fin -> A ~< NN ) $=
    ( cfn wcel cpw csdm wbr cn cdom canth2g pwfi c1 chash cfv cfz cvv fzfi nnex
    co wss sylbi fz1ssnn ssdomfi2 mp3an wb isfinite4 mpbii sdomdomtrfi mpd3an23
    cen domen1 ) ABCZAADZEFULGHFZAGEFABIUKULBCZUMAJUNKULLMZNRZGHFZUMUPBCGOCUPGS
    UQKUOPQUOUAUPGOUBUCUNUPULUIFUQUMUDULUEUPULGUJTUFTAULGUGUH $.

  $( The less-than relation is a set.  (Contributed by SN, 5-Jun-2025.) $)
  ltex $p |- < e. _V $=
    ( clt cxr cxp xrex xpex ltrelxr ssexi ) ABBCBBDDEFG $.

  $( The less-than-or-equal-to relation is a set.  (Contributed by SN,
     5-Jun-2025.) $)
  leex $p |- <_ e. _V $=
    ( cle cxr cxp xrex xpex lerelxr ssexi ) ABBCBBDDEFG $.

  $( The subtraction operation is a set.  (Contributed by SN, 5-Jun-2025.) $)
  subex $p |- - e. _V $=
    ( cc cxp cmin wf cvv wcel subf cnex xpex fex2 mp3an ) AABZACDLEFAEFCEFGAAHH
    IHLACEEJK $.

  $( The absolute value function is a set.  (Contributed by SN, 5-Jun-2025.) $)
  absex $p |- abs e. _V $=
    ( cc cr cabs wf cvv wcel absf cnex reex fex2 mp3an ) ABCDAEFBEFCEFGHIABCEEJ
    K $.

  $( The conjugate function is a set.  (Contributed by SN, 5-Jun-2025.) $)
  cjex $p |- * e. _V $=
    ( cc ccj wf cvv wcel cjf cnex fex2 mp3an ) AABCADEZJBDEFGGAABDDHI $.

  ${
    $d B k $.  $d M k $.  $d N k $.  $d ph k $.
    fzosumm1.1 $e |- ( ph -> ( N - 1 ) e. ( ZZ>= ` M ) ) $.
    fzosumm1.2 $e |- ( ( ph /\ k e. ( M ..^ N ) ) -> A e. CC ) $.
    fzosumm1.3 $e |- ( k = ( N - 1 ) -> A = B ) $.
    fzosumm1.n $e |- ( ph -> N e. ZZ ) $.
    $( Separate out the last term in a finite sum.  (Contributed by Steven
       Nguyen, 22-Aug-2023.) $)
    fzosumm1 $p |- ( ph -> sum_ k e. ( M ..^ N ) A =
                          ( sum_ k e. ( M ..^ ( N - 1 ) ) A + B ) ) $=
      ( c1 cmin co cfz csu caddc cfzo wcel cz wceq cv fzoval syl eqcomd sumeq1d
      cc eleq2d biimpa syldan fsumm1 cuz cfv eluzelz 3syl oveq1d 3eqtr4d ) AEFK
      LMZNMZBDOEUQKLMNMZBDOZCPMEFQMZBDOEUQQMZBDOZCPMABCDEUQGADUAZURRZVDVARZBUFR
      AVEVFAURVAVDAVAURAFSRVAURTJEFUBUCZUDUGUHHUIIUJAVAURBDVGUEAVCUTCPAVBUSBDAU
      QEUKULRUQSRVBUSTGEUQUMEUQUBUNUEUOUP $.
  $}

  ${
    ccatcan2d.a $e |- ( ph -> A e. Word V ) $.
    ccatcan2d.b $e |- ( ph -> B e. Word V ) $.
    ccatcan2d.c $e |- ( ph -> C e. Word V ) $.
    $( Cancellation law for concatenation.  (Contributed by SN, 6-Sep-2023.) $)
    ccatcan2d $p |- ( ph -> ( ( A ++ C ) = ( B ++ C ) <-> A = B ) ) $=
      ( cconcat co wceq chash cfv cpfx cc wcel cn0 lencl adantr syl2anc ccatlen
      wa simpr cword syl caddc fveq2 sylan9req eqtrd addcan2ad oveq12d pfxccat1
      nn0cnd ex eqeq12d sylibd oveq1 impbid1 ) ABDIJZCDIJZKZBCKZAVAUSBLMZNJZUTC
      LMZNJZKZVBAVAVGAVAUBZUSUTVCVENAVAUCVHVCVEDLMZAVCOPVAAVCABEUDZPZVCQPFEBRUE
      UMSAVEOPVAAVEACVJPZVEQPGECRUEUMSAVIOPVAAVIADVJPZVIQPHEDRUEUMSVHVCVIUFJZUT
      LMZVEVIUFJZAVAVNUSLMZVOAVKVMVQVNKFHEEBDUATUSUTLUGUHAVOVPKZVAAVLVMVRGHEECD
      UATSUIUJUKUNAVDBVFCAVKVMVDBKFHEBDULTAVLVMVFCKGHECDULTUOUPBCDIUQUR $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Arithmetic theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Towards the start of this section are several proofs regarding the different
  complex number axioms that could be used to prove some results.

  For example, ~ ax-1rid is used in ~ mulrid related theorems, so one could
  trade off the extra axioms in ~ mulrid for the axioms needed to prove that
  something is a real number.  Another example is avoiding complex number
  closure laws by using real number closure laws and then using ~ ax-resscn ;
  in the other direction, real number closure laws can be avoided by using
  ~ ax-resscn and then the complex number closure laws.  (This only works if
  the result of ` ( A .+ B ) ` only needs to be a complex number).

  The natural numbers are especially amenable to axiom reductions, as the set
  ` NN ` is the recursive set ` { 1 , ( 1 + 1 ) , ( ( 1 + 1 ) + 1 ) } ` , etc.,
  i.e. the set of numbers formed by only additions of 1.  The digits 2 through
  9 are defined so that they expand into additions of 1.  This conveniently
  allows for adding natural numbers by rearranging parentheses, as shown below:

  ` ( 4 + 3 ) = 7 `

  ` ( ( 3 + 1 ) + ( 2 + 1 ) ) = ( 6 + 1 ) `

  ` ( ( ( ( 1 + 1 ) + 1 ) + 1 ) + ( ( 1 + 1 ) + 1 ) ) = `

  ` ( ( ( ( ( ( 1 + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) + 1 ) `

  This only requires ~ ax-addass , ~ ax-1cn , and ~ ax-addcl .  (And in
  practice, the expression isn't fully expanded into ones.)

  Multiplication by 1 requires either ~ mullidi or ( ~ ax-1rid and ~ 1re ) as
  seen in ~ 1t1e1 and ~ 1t1e1ALT .  Multiplying with greater natural numbers
  uses ~ ax-distr .  Still, this takes fewer axioms than adding zero, which is
  often implicit in theorems such as ` ( 9 + 1 ) = ; 1 0 ` .  Adding zero uses
  almost every complex number axiom, though notably not ~ ax-mulcom (see
  ~ readdrid and ~ readdlid ).

$)

  $( Alternate proof of ~ c0ex using more set theory axioms but fewer complex
     number axioms (add ~ ax-10 , ~ ax-11 , ~ ax-13 , ~ ax-nul , and remove
     ~ ax-1cn , ~ ax-icn , ~ ax-addcl , and ~ ax-mulcl ).  (Contributed by
     Steven Nguyen, 4-Dec-2022.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  c0exALT $p |- 0 e. _V $=
    ( cc0 ci cmul co c1 caddc ax-i2m1 eqcomi ovexi ) ABBCDZEFJEFDAGHI $.

  $( Alternate proof of ~ 0cn using ~ ax-resscn , ~ ax-addrcl , ~ ax-rnegex ,
     ~ ax-cnre instead of ~ ax-icn , ~ ax-addcl , ~ ax-mulcl , ~ ax-i2m1 .
     Version of ~ 0cnALT using ~ ax-1cn instead of ~ ax-icn .  (Contributed by
     Steven Nguyen, 7-Jan-2022.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  0cnALT3 $p |- 0 e. CC $=
    ( cc0 0re recni ) ABC $.

  ${
    $d x A $.
    $( Specialized version of ~ 0red without using ~ ax-1cn and ~ ax-cnre .
       (Contributed by Steven Nguyen, 28-Jan-2023.) $)
    elre0re $p |- ( A e. RR -> 0 e. RR ) $=
      ( vx cr wcel cv caddc cc0 wceq wrex ax-rnegex readdcl syl5ibcom rexlimdva
      co wa eleq1 mpd ) ACDZABEZFNZGHZBCIGCDZBAJRUAUBBCRSCDOTCDUAUBASKTGCPLMQ
      $.
  $}

  ${
    lttrii.a $e |- A e. RR $.
    lttrii.b $e |- B e. RR $.
    lttrii.c $e |- C e. RR $.
    lttrii.1 $e |- A < B $.
    lttrii.2 $e |- B < C $.
    $( 'Less than' is transitive.  (Contributed by SN, 26-Aug-2025.) $)
    lttrii $p |- A < C $=
      ( clt wbr lttri mp2an ) ABIJBCIJACIJGHABCDEFKL $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d ph x $.
    remulcan2d.1 $e |- ( ph -> A e. RR ) $.
    remulcan2d.2 $e |- ( ph -> B e. RR ) $.
    remulcan2d.3 $e |- ( ph -> C e. RR ) $.
    remulcan2d.4 $e |- ( ph -> C =/= 0 ) $.
    $( ~ mulcan2d for real numbers using fewer axioms.  (Contributed by Steven
       Nguyen, 15-Apr-2023.) $)
    remulcan2d $p |- ( ph -> ( ( A x. C ) = ( B x. C ) <-> A = B ) ) $=
      ( vx cmul co wceq c1 cr wcel wa oveq1 adantr recnd mulassd cv wi cc0 wrex
      wne ax-rrecex syl2anc simprl simprr oveq2d ax-1rid syl imbitrid rexlimddv
      3eqtrd eqeq12d impbid1 ) ABDJKZCDJKZLZBCLZADIUAZJKZMLZUTVAUBINADNOZDUCUEV
      DINUDGHIDUFUGUTURVBJKZUSVBJKZLAVBNOZVDPZPZVAURUSVBJQVJVFBVGCVJVFBVCJKBMJK
      ZBVJBDVBVJBABNOZVIERZSVJDAVEVIGRSZVJVBAVHVDUHSZTVJVCMBJAVHVDUIZUJVJVLVKBL
      VMBUKULUOVJVGCVCJKCMJKZCVJCDVBVJCACNOZVIFRZSVNVOTVJVCMCJVPUJVJVRVQCLVSCUK
      ULUOUPUMUNBCDJQUQ $.
  $}

  ${
    readdridaddlidd.a $e |- ( ph -> A e. RR ) $.
    readdridaddlidd.b $e |- ( ph -> B e. RR ) $.
    readdridaddlidd.1 $e |- ( ph -> ( B + A ) = B ) $.
    $( Given some real number ` B ` where ` A ` acts like a right additive
       identity, derive that ` A ` is a left additive identity.  Note that the
       hypothesis is weaker than proving that ` A ` is a right additive
       identity (for all numbers).  Although, if there is a right additive
       identity, then by ~ readdcan , ` A ` is the right additive identity.
       (Contributed by Steven Nguyen, 14-Jan-2023.) $)
    readdridaddlidd $p |- ( ( ph /\ C e. RR ) -> ( A + C ) = C ) $=
      ( cr wcel wa caddc co wceq adantr recnd simpr addassd oveq1d eqtr3d wb
      readdcld readdcan syl3anc mpbid ) ADHIZJZCBDKLZKLZCDKLZMZUGDMZUFCBKLZDKLU
      HUIUFCBDUFCACHIZUEFNZOUFBABHIUEENZOUFDAUEPZOQUFULCDKAULCMUEGNRSUFUGHIUEUM
      UJUKTUFBDUOUPUAUPUNUGDCUBUCUD $.
  $}

  $( A shorter proof of ~ 4p4e8 if ~ 6p2e8 was moved up.  The most clean way to
     do this would be to start with ~ 7p2e9 , then go ~ 6p2e8 , ~ 6p3e9 , etc.,
     which is still inelegant.  The idea here is that using ` 4 = 2 + 2 ` and
     ~ 2cn is shorter than using ` 4 = 3 + 1 ` , ~ 3cn , and ~ ax-1cn .  This
     also works with ~ 5p4e9 .  (Contributed by SN, 24-Aug-2026.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  4p4e8ALT $p |- ( 4 + 4 ) = 8 $=
    ( c4 c2 caddc co c8 4cn 2cn addassi 4p2e6 oveq1i 6p2e8 eqtri 2p2e4 3eqtr3ri
    c6 oveq2i ) ABCDZBCDZABBCDZCDEAACDABBFGGHROBCDEQOBCIJKLSAACMPN $.

  $( These proofs are longer than necessary to avoid axioms. See ~ 1p2e3 . $)
  $( 1 + 3 = 4.  (Contributed by SN, 19-Nov-2025.) $)
  1p3e4 $p |- ( 1 + 3 ) = 4 $=
    ( c1 c3 caddc co c2 df-3 oveq2i ax-1cn 2cn addassi 1p2e3 oveq1i 3p1e4 eqtri
    c4 3eqtr2i ) ABCDAEACDZCDAECDZACDZOBQACFGAEAHIHJSBACDORBACKLMNP $.

  $( 1 + 4 = 5.  (Contributed by SN, 24-Aug-2026.) $)
  1p4e5 $p |- ( 1 + 4 ) = 5 $=
    ( c1 c4 caddc co c3 df-4 oveq2i ax-1cn 3cn addassi 1p3e4 oveq1i 4p1e5 eqtri
    c5 3eqtr2i ) ABCDAEACDZCDAECDZACDZOBQACFGAEAHIHJSBACDORBACKLMNP $.

  $( 1 + 5 = 6.  (Contributed by SN, 24-Aug-2026.) $)
  1p5e6 $p |- ( 1 + 5 ) = 6 $=
    ( c1 c5 caddc co c4 df-5 oveq2i ax-1cn 4cn addassi 1p4e5 oveq1i 5p1e6 eqtri
    c6 3eqtr2i ) ABCDAEACDZCDAECDZACDZOBQACFGAEAHIHJSBACDORBACKLMNP $.

  $( 1 + 6 = 7.  (Contributed by SN, 24-Aug-2026.) $)
  1p6e7 $p |- ( 1 + 6 ) = 7 $=
    ( c1 c6 caddc co c5 df-6 oveq2i ax-1cn 5cn addassi 1p5e6 oveq1i 6p1e7 eqtri
    c7 3eqtr2i ) ABCDAEACDZCDAECDZACDZOBQACFGAEAHIHJSBACDORBACKLMNP $.

  $( 1 + 7 = 8.  (Contributed by SN, 24-Aug-2026.) $)
  1p7e8 $p |- ( 1 + 7 ) = 8 $=
    ( c1 c7 caddc co c6 df-7 oveq2i ax-1cn 6cn addassi 1p6e7 oveq1i 7p1e8 eqtri
    c8 3eqtr2i ) ABCDAEACDZCDAECDZACDZOBQACFGAEAHIHJSBACDORBACKLMNP $.

  $( 1 + 8 = 9.  (Contributed by SN, 24-Aug-2026.) $)
  1p8e9 $p |- ( 1 + 8 ) = 9 $=
    ( c1 c8 caddc co c7 df-8 oveq2i ax-1cn 7cn addassi 1p7e8 oveq1i 8p1e9 eqtri
    c9 3eqtr2i ) ABCDAEACDZCDAECDZACDZOBQACFGAEAHIHJSBACDORBACKLMNP $.

  $( 2 + 3 = 5.  (Contributed by SN, 24-Aug-2026.) $)
  2p3e5 $p |- ( 2 + 3 ) = 5 $=
    ( c2 c1 caddc co c5 c3 ax-1cn addassi 2p1e3 oveq1i 3p2e5 eqtri 1p2e3 oveq2i
    2cn 3eqtr3ri ) ABCDZACDZABACDZCDEAFCDABAOGOHRFACDEQFACIJKLSFACMNP $.

  $( 2 + 4 = 6.  (Contributed by SN, 24-Aug-2026.) $)
  2p4e6 $p |- ( 2 + 4 ) = 6 $=
    ( c2 caddc co c6 c4 2cn addassi 2p2e4 oveq1i 4p2e6 eqtri oveq2i 3eqtr3ri )
    AABCZABCZANBCDAEBCAAAFFFGOEABCDNEABHIJKNEABHLM $.

  $( 2 + 5 = 7.  (Contributed by SN, 24-Aug-2026.) $)
  2p5e7 $p |- ( 2 + 5 ) = 7 $=
    ( c2 c3 caddc co c7 2cn 3cn addassi 2p3e5 oveq1i 5p2e7 eqtri 3p2e5 3eqtr3ri
    c5 oveq2i ) ABCDZACDZABACDZCDEAOCDABAFGFHROACDEQOACIJKLSOACMPN $.

  $( 2 + 6 = 8.  (Contributed by SN, 24-Aug-2026.) $)
  2p6e8 $p |- ( 2 + 6 ) = 8 $=
    ( c2 caddc co c4 c8 2cn 4cn addassi 2p2e4 oveq1i 4p4e8 eqtri 2p4e6 3eqtr3ri
    c6 oveq2i ) AABCZDBCZAADBCZBCEAOBCAADFFGHRDDBCEQDDBIJKLSOABMPN $.

  $( 2 + 7 = 9.  (Contributed by SN, 24-Aug-2026.) $)
  2p7e9 $p |- ( 2 + 7 ) = 9 $=
    ( c2 c5 caddc co c9 2cn 5cn addassi 2p5e7 oveq1i 7p2e9 eqtri 5p2e7 3eqtr3ri
    c7 oveq2i ) ABCDZACDZABACDZCDEAOCDABAFGFHROACDEQOACIJKLSOACMPN $.

  $( 3 + 4 = 7.  (Contributed by SN, 24-Aug-2026.) $)
  3p4e7 $p |- ( 3 + 4 ) = 7 $=
    ( c3 c2 caddc co c7 c4 3cn addassi c5 3p2e5 oveq1i 5p2e7 eqtri 2p2e4 oveq2i
    2cn 3eqtr3ri ) ABCDZBCDZABBCDZCDEAFCDABBGPPHSIBCDERIBCJKLMTFACNOQ $.

  $( 3 + 5 = 8.  (Contributed by SN, 24-Aug-2026.) $)
  3p5e8 $p |- ( 3 + 5 ) = 8 $=
    ( c3 c2 caddc co c8 3cn 2cn addassi 3p2e5 oveq1i 5p3e8 eqtri 2p3e5 3eqtr3ri
    c5 oveq2i ) ABCDZACDZABACDZCDEAOCDABAFGFHROACDEQOACIJKLSOACMPN $.

  $( 3 + 6 = 9.  (Contributed by SN, 24-Aug-2026.) $)
  3p6e9 $p |- ( 3 + 6 ) = 9 $=
    ( c3 caddc co c9 c6 3cn addassi 3p3e6 oveq1i 6p3e9 eqtri oveq2i 3eqtr3ri )
    AABCZABCZANBCDAEBCAAAFFFGOEABCDNEABHIJKNEABHLM $.

  $( 4 + 5 = 9.  (Contributed by SN, 24-Aug-2026.) $)
  4p5e9 $p |- ( 4 + 5 ) = 9 $=
    ( c4 c5 caddc co c1 c9 df-5 oveq2i 4cn ax-1cn addassi c8 4p4e8 oveq1i 8p1e9
    eqtri 3eqtr2i ) ABCDAAECDZCDAACDZECDZFBRACGHAAEIIJKTLECDFSLECMNOPQ $.

  $( The number 5 is nonzero.  (Contributed by SN, 22-Oct-2025.) $)
  5ne0 $p |- 5 =/= 0 $=
    ( c5 5nn nnne0i ) ABC $.

  $( The number 6 is nonzero.  (Contributed by SN, 22-Oct-2025.) $)
  6ne0 $p |- 6 =/= 0 $=
    ( c6 6nn nnne0i ) ABC $.

  $( The number 7 is nonzero.  (Contributed by SN, 22-Oct-2025.) $)
  7ne0 $p |- 7 =/= 0 $=
    ( c7 7nn nnne0i ) ABC $.

  $( The number 8 is nonzero.  (Contributed by SN, 22-Oct-2025.) $)
  8ne0 $p |- 8 =/= 0 $=
    ( c8 8nn nnne0i ) ABC $.

  $( The number 9 is nonzero.  (Contributed by SN, 22-Oct-2025.) $)
  9ne0 $p |- 9 =/= 0 $=
    ( c9 9nn nnne0i ) ABC $.

  $( A proof of ~ 1ne2 without using ~ ax-mulcom , ~ ax-mulass ,
     ~ ax-pre-mulgt0 .  Based on ~ mul02lem2 .  (Contributed by SN,
     13-Dec-2023.) $)
  sn-1ne2 $p |- 1 =/= 2 $=
    ( c1 caddc co c2 wne cc0 wceq 0ne1 wa cmul ax-icn mulcli ax-1cn addassi a1i
    ci simpr oveq2d cr wcel ax-i2m1 3eqtr2rd simpl oveq1d 3eqtr3d 0red readdcan
    wb 1red syl3anc mpbid ex necon3d mpi oveq2 0re ax-1rid ax-mp adddii oveq12i
    0cn eqtri 3eqtr3g necon3i pm2.61ine df-2 neeqtrri ) AAABCZDAVHEZFFFBCZFVJGZ
    FAEVIHVKAVHFAVKAVHGZFAGZVKVLIZVJFABCZGZVMVNFPPJCZABCZABCZVJVOVNVSVQVHBCZVRF
    VSVTGVNVQAAPPKKLMMNOVNAVHVQBVKVLQRVRFGVNUAOZUBVKVLUCVNVRFABWAUDUEVNFSTZASTW
    BVPVMUHVNUFZVNUIWCFAFUGUJUKULUMUNAVHFVJVLFAJCZFVHJCZFVJAVHFJUOWBWDFGUPFUQUR
    ZWEWDWDBCVJFAAVAMMUSWDFWDFBWFWFUTVBVCVDVEVFVG $.

  ${
    $d x y z A $.
    $( A positive integer that is not 1 is a successor of some other positive
       integer.  (Contributed by Steven Nguyen, 19-Aug-2023.) $)
    nnn1suc $p |- ( ( A e. NN /\ A =/= 1 ) -> E. x e. NN ( x + 1 ) = A ) $=
      ( vy vz cn wcel c1 wne cv caddc co wceq wrex wi neeq1 rexbidv imbi12d weq
      eqeq2 wn df-ne eqid pm2.24i sylbi oveq1 adantl rspcedeq1vd 2a1d nnind imp
      id ) BEFBGHZAIZGJKZBLZAEMZCIZGHZUNUQLZAEMZNGGHZUNGLZAEMZNDIZGHZUNVDLZAEMZ
      NZVDGJKZGHZUNVILZAEMZNULUPNCDBUQGLZURVAUTVCUQGGOVMUSVBAEUQGUNSPQCDRZURVEU
      TVGUQVDGOVNUSVFAEUQVDUNSPQUQVILZURVJUTVLUQVIGOVOUSVKAEUQVIUNSPQUQBLZURULU
      TUPUQBGOVPUSUOAEUQBUNSPQVAGGLZTVCGGUAVQVCGUBUCUDVDEFZVLVHVJVRAVDEUNVIVRUK
      ADRVKVRUMVDGJUEUFUGUHUIUJ $.
  $}

  ${
    readdrcl2d.a $e |- ( ph -> A e. RR ) $.
    readdrcl2d.b $e |- ( ph -> B e. CC ) $.
    readdrcl2d.c $e |- ( ph -> ( A + B ) e. RR ) $.
    $( Reverse closure for addition: the second addend is real if the first
       addend is real and the sum is real.  (Contributed by SN,
       25-Apr-2025.) $)
    readdrcl2d $p |- ( ph -> B e. RR ) $=
      ( caddc co cmin cr recnd pncan2d resubcld eqeltrrd ) ABCGHZBIHCJABCABDKEL
      AOBFDMN $.
  $}

  ${
    mvrrsubd.a $e |- ( ph -> B e. CC ) $.
    mvrrsubd.b $e |- ( ph -> C e. CC ) $.
    mvrrsubd.1 $e |- ( ph -> A = ( B - C ) ) $.
    $( Move a subtraction in the RHS to a right-addition in the LHS. Converse
       of ~ mvlraddd .

       EDITORIAL:  Do not move until it would have 7 uses: current additional
       uses:  (none).  (Contributed by SN, 21-Aug-2024.) $)
    mvrrsubd $p |- ( ph -> ( A + C ) = B ) $=
      ( caddc co cmin cc subcld eqeltrd addcld pncand eqtrd subcan2d ) ABDHIZCD
      ABDABCDJIZKGACDEFLMZFNEFARDJIBSABDTFOGPQ $.
  $}

  ${
    laddrotrd.a $e |- ( ph -> A e. CC ) $.
    laddrotrd.b $e |- ( ph -> B e. CC ) $.
    laddrotrd.1 $e |- ( ph -> ( A + B ) = C ) $.
    $( Rotate the variables right in an equation with addition on the left,
       converting it into a subtraction.  Version of ~ mvlladdd with a commuted
       consequent, and of ~ mvrladdd with a commuted hypothesis.

       EDITORIAL:  The label for this theorem is questionable.  Do not move
       until it would have 7 uses: current additional uses: ~ ply1dg3rt0irred .
       (Contributed by SN, 21-Aug-2024.) $)
    laddrotrd $p |- ( ph -> ( C - A ) = B ) $=
      ( cmin co mvlladdd eqcomd ) ACDBHIABCDEFGJK $.
  $}

  ${
    raddswap12d.b $e |- ( ph -> B e. CC ) $.
    raddswap12d.c $e |- ( ph -> C e. CC ) $.
    raddswap12d.1 $e |- ( ph -> A = ( B + C ) ) $.
    $( Swap the first two variables in an equation with addition on the right,
       converting it into a subtraction.  Version of ~ mvrraddd with a commuted
       consequent, and of ~ mvlraddd with a commuted hypothesis.

       EDITORIAL:  The label for this theorem is questionable.  Do not move
       until it would have 7 uses: current additional uses:  (none).
       (Contributed by SN, 21-Aug-2024.) $)
    raddswap12d $p |- ( ph -> B = ( A - C ) ) $=
      ( cmin co mvrraddd eqcomd ) ABDHICABCDEFGJK $.
  $}

  ${
    lsubrotld.a $e |- ( ph -> A e. CC ) $.
    lsubrotld.b $e |- ( ph -> B e. CC ) $.
    lsubrotld.1 $e |- ( ph -> ( A - B ) = C ) $.
    $( Rotate the variables left in an equation with subtraction on the left,
       converting it into an addition.

       EDITORIAL:  The label for this theorem is questionable.  Do not move
       until it would have 7 uses: current additional uses:  (none).
       (Contributed by SN, 21-Aug-2024.) $)
    lsubrotld $p |- ( ph -> ( B + C ) = A ) $=
      ( caddc co cmin cc subcld eqeltrrd addcld pncan2d eqtr4d subcan2d ) ACDHI
      ZBCACDFABCJIZDKGABCEFLMZNEFARCJIDSACDFTOGPQ $.
  $}

  ${
    rsubrotld.b $e |- ( ph -> B e. CC ) $.
    rsubrotld.c $e |- ( ph -> C e. CC ) $.
    rsubrotld.1 $e |- ( ph -> A = ( B - C ) ) $.
    $( Rotate the variables left in an equation with subtraction on the right,
       converting it into an addition.

       EDITORIAL:  The label for this theorem is questionable.  Do not move
       until it would have 7 uses: current additional uses:  (none).
       (Contributed by SN, 4-Jul-2025.) $)
    rsubrotld $p |- ( ph -> B = ( C + A ) ) $=
      ( caddc co cmin eqcomd lsubrotld ) ADBHICACDBEFABCDJIGKLK $.
  $}

  ${
    lsubswap23d.a $e |- ( ph -> A e. CC ) $.
    lsubswap23d.b $e |- ( ph -> B e. CC ) $.
    lsubswap23d.1 $e |- ( ph -> ( A - B ) = C ) $.
    $( Swap the second and third variables in an equation with subtraction on
       the left, converting it into an addition.

       EDITORIAL:  The label for this theorem is questionable.  Do not move
       until it would have 7 uses: current additional uses:  (none).
       (Contributed by SN, 23-Aug-2024.) $)
    lsubswap23d $p |- ( ph -> ( A - C ) = B ) $=
      ( cmin co cc subcld eqeltrrd caddc lsubrotld eqcomd mvrraddd ) ABCDFABCHI
      DJGABCEFKLACDMIBABCDEFGNOP $.
  $}

  $( Relation between sums and differences.  (Contributed by Steven Nguyen,
     5-Jan-2023.) $)
  addsubeq4com $p |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) ) ->
    ( ( A + B ) = ( C + D ) <-> ( A - C ) = ( D - B ) ) ) $=
    ( caddc co wceq cc wcel wa cmin eqcom wb addsubeq4 ancoms bitrid ) ABEFZCDE
    FZGRQGZAHIBHIJZCHIDHIJZJACKFDBKFGZQRLUATSUBMCDABNOP $.

  ${
    sqsumi.1 $e |- A e. CC $.
    sqsumi.2 $e |- B e. CC $.
    $( A sum squared.  (Contributed by Steven Nguyen, 16-Sep-2022.) $)
    sqsumi $p |- ( ( A + B ) x. ( A + B ) ) =
      ( ( ( A x. A ) + ( B x. B ) ) + ( 2 x. ( A x. B ) ) ) $=
      ( caddc co cmul c2 muladdi mulcli 2timesi eqcomi oveq2i eqtri ) ABEFZOGFA
      AGFBBGFEFZABGFZQEFZEFPHQGFZEFABABCDCDIRSPESRQABCDJKLMN $.
  $}

  ${
    negn0nposznnd.1 $e |- ( ph -> A =/= 0 ) $.
    negn0nposznnd.2 $e |- ( ph -> -. 0 < A ) $.
    negn0nposznnd.3 $e |- ( ph -> A e. ZZ ) $.
    $( Lemma for ~ dffltz .  (Contributed by Steven Nguyen, 27-Feb-2023.) $)
    negn0nposznnd $p |- ( ph -> -u A e. NN ) $=
      ( cz wcel cn0 wn cneg cn cc0 wceq wo wa clt wbr nngt0 nsyl neneqd sylnibr
      jca pm4.56 sylib elnn0 znnn0nn syl2anc ) ABFGBHGZIBJKGEABKGZBLMZNZUHAUIIZ
      UJIZOUKIAULUMALBPQUIDBRSABLCTUBUIUJUCUDBUEUABUFUG $.
  $}

  ${
    sqmid3api.a $e |- A e. CC $.
    sqmid3api.n $e |- N e. CC $.
    sqmid3api.b $e |- ( A + N ) = B $.
    sqmid3api.c $e |- ( B + N ) = C $.
    $( Value of the square of the middle term of a 3-term arithmetic
       progression.  (Contributed by Steven Nguyen, 20-Sep-2022.) $)
    sqmid3api $p |- ( B x. B ) = ( ( A x. C ) + ( N x. N ) ) $=
      ( caddc co cmul muladdi oveq12i mulcli addcli add32i adddii oveq1i oveq2i
      eqtri addassi 3eqtr3ri 3eqtr3i ) ADIJZUDKJAAKJZDDKJZIJADKJZUGIJZIJZBBKJAC
      KJZUFIJZADADEFEFLUDBUDBKGGMUIUEUHIJZUFIJUKUEUFUHAAEENZDDFFNUGUGADEFNZUNOP
      ULUJUFIAUDDIJZKJAUDKJZUGIJZUJULAUDDEADEFOFQUOCAKUOBDIJCUDBDIGRHTSUQUEUGIJ
      ZUGIJULUPURUGIAADEEFQRUEUGUGUMUNUNUATUBRTUC $.
  $}

  ${
    decaddcom.a $e |- A e. NN0 $.
    decaddcom.b $e |- B e. NN0 $.
    decaddcom.c $e |- C e. NN0 $.
    $( Commute ones place in addition.  (Contributed by Steven Nguyen,
       29-Jan-2023.) $)
    decaddcom $p |- ( ; A B + C ) = ( ; A C + B ) $=
      ( cdc caddc co eqid decaddi nn0cni addcomi eqtr4i ) ABGZCHIABCHIZGACGZBHI
      ABPOCDEFOJPJKACPQBDFEQJCBCFLBELMKN $.
  $}

  ${
    sqn5i.1 $e |- A e. NN0 $.
    $( The square of a number ending in 5.  This shortcut only works because 5
       is half of 10.  (Contributed by Steven Nguyen, 16-Sep-2022.) $)
    sqn5i $p |- ( ; A 5 x. ; A 5 ) = ; ; ( A x. ( A + 1 ) ) 2 5 $=
      ( c5 cdc cmul co cc0 caddc c2 0nn0 deccl nn0cni 5nn0 eqid addlidi decaddi
      5cn 2nn0 cn0 eqtri 5p5e10 decaddci2 sqmid3api 5t5e25 wcel peano2nn0 ax-mp
      c1 nn0mulcli decmulnc mul01i deceq2i 2cn mul02i oveq1i decma ) ACDZUQEFAG
      DZAUHHFZGDZEFCCEFZHFAUSEFZIDZCDURUQUTCURAGBJKLQAGCURCBJMURNZCQOZPACUSUQCB
      MMUQNUSNUAUBUCAGICUTVCCURVABJRMVDUDUSGASUEUSSUEBAUFUGZJKZVBGIAUTEFZIAUSBV
      FUIJRVHVBAGEFZDVBGDUSGABVFJUJVIGVBAABLUKULTIUMOPGUTEFZCHFGCHFCVJGCHUTUTVG
      LUNUOVETUPT $.

    sqn5ii.2 $e |- ( A + 1 ) = B $.
    sqn5ii.3 $e |- ( A x. B ) = C $.
    $( The square of a number ending in 5.  This shortcut only works because 5
       is half of 10.  (Contributed by Steven Nguyen, 16-Sep-2022.) $)
    sqn5ii $p |- ( ; A 5 x. ; A 5 ) = ; ; C 2 5 $=
      ( c5 cdc cmul co c1 caddc c2 sqn5i oveq2i eqtri deceq1i ) AGHZRIJAAKLJZIJ
      ZMHZGHCMHZGHADNUAUBGTCMTABIJCSBAIEOFPQQP $.
  $}

  ${
    decpmulnc.a $e |- A e. NN0 $.
    decpmulnc.b $e |- B e. NN0 $.
    decpmulnc.c $e |- C e. NN0 $.
    decpmulnc.d $e |- D e. NN0 $.
    decpmulnc.1 $e |- ( A x. C ) = E $.
    decpmulnc.2 $e |- ( ( A x. D ) + ( B x. C ) ) = F $.
    ${
      decpmulnc.3 $e |- ( B x. D ) = G $.
      $( Partial products algorithm for two digit multiplication, no carry.
         Compare ~ muladdi .  (Contributed by Steven Nguyen, 9-Dec-2022.) $)
      decpmulnc $p |- ( ; A B x. ; C D ) = ; ; E F G $=
        ( cdc cmul co eqid nn0mulcli nn0cni deccl cn0 eqeltrri addcomli decmul1
        decrmanc decmul2c ) CDEFOGABOZADPQZCDOZABHIUAJKUJRBDPQGUBNBDIKSUCADHKSZ
        ABCEFUHUIHIUKUHRZJLUIBCPQZFUIUKTUMBCIJSTMUDUFABUIGDUHKHIULUIRNUEUG $.
    $}

    decpmul.3 $e |- ( B x. D ) = ; G H $.
    decpmul.4 $e |- ( ; E G + F ) = I $.
    decpmul.g $e |- G e. NN0 $.
    decpmul.h $e |- H e. NN0 $.
    $( Partial products algorithm for two digit multiplication.  (Contributed
       by Steven Nguyen, 10-Dec-2022.) $)
    decpmul $p |- ( ; A B x. ; C D ) = ; I H $=
      ( co cdc cmul c1 cc0 caddc decpmulnc dfdec10 cn0 nn0mulcli eqeltrri numcl
      deccl 0nn0 dec0u eqid decaddcom eqtri nn0cni addlidi decadd 3eqtri ) ABUA
      CDUAUBTEFUAZGHUAZUAUCUDUAVBUBTZVCUETIHUAABCDEFVCJKLMNOPUFVBVCUGVBUDGHIHVD
      VCEFACUBTEUHNACJLUIUJZADUBTBCUBTZUETFUHODVFAJMBCKLUIUKUJZULZUMRSVBVHUNVCU
      OVBGUETEGUAFUETIEFGVEVGRUPQUQHHSURUSUTVA $.
  $}

  ${
    sqdeccom12.a $e |- A e. NN0 $.
    sqdeccom12.b $e |- B e. NN0 $.
    $( The square of a number in terms of its digits switched.  (Contributed by
       Steven Nguyen, 3-Jan-2023.) $)
    sqdeccom12 $p |- ( ( ; A B x. ; A B ) - ( ; B A x. ; B A ) ) =
      ( ; 9 9 x. ( ( A x. A ) - ( B x. B ) ) ) $=
      ( cmul co caddc cdc cmin c1 cc0 c9 cc wcel 0nn0 deccl nn0cni eqid oveq12i
      mulcli wceq nn0mulcli subadd4 mp4an addlidi decaddi eqtr2i addcomi decadd
      numcl 3eqtr4i addsubeq4com mpbi 10nn0 ax-1cn subcli subdiri subdii mul02i
      wb dec0u decmul1 eqtri mullidi decpmulnc 9p1e10 decsucc addcomli mvlladdi
      9nn0 oveq1i ) AAEFZABEFZBAEFZGFZHZBBEFZHZVQVOHZVLHZIFZJKHZKHZJIFZVLVQIFZE
      FZABHZWGEFZBAHZWIEFZIFLLHZWEEFVLKHZVQHZVQKHZVLHZIFZWLKHZWNKHZIFZWEIFZWAWF
      WTWQVQGFZWRVLGFZIFZWPWQMNWRMNVLMNVQMNWTXCUAWQWLKVLKAACCUBZOPZOPQWRWNKVQKB
      BDDUBZOPZOPQAAACQZXHTZBBBDQZXJTZWQWRVLVQUCUDXAWMXBWOIWLKVQWQVQXEOXFWQRVQX
      KUEUFWNKVLWRVLXGOXDWRRVLXIUEUFSUGVRWOGFZVTWMGFZUAZWAWPUAZVQVLGFZVOKGFZHZV
      LVQGFZHZXTXLXMXTRVPVQWNVLXRXSVRWOVLVOXDBVNACDBADCUBUJZPZXFXGXDVRRWORVLVOV
      QKXPXQVPWNXDYAXFOVPRWNRVLVQXIXKUHXQRZUIVQVLXKXIUHUIVSVLWLVQXRXSVTWMVQVOXF
      YAPZXDXEXFVTRWMRVQVOVLKXPXQVSWLXFYAXDOVSRWLRXPRYCUIXSRUIUKVRMNWOMNVTMNWMM
      NXNXOUTVRVPVQYBXFPQWOWNVLXGXDPQVTVSVLYDXDPQWMWLVQXEXFPQVRWOVTWMULUDUMWFWC
      WEEFZJWEEFZIFWTWCJWEWCWBKUNOPQZUOVLVQXIXKUPZUQYEWSYFWEIYEWCVLEFZWCVQEFZIF
      WSWCVLVQYGXIXKURYIWQYJWRIWBKWLKVLWCXDUNOWCRZVLXDVAVLXIUSVBWBKWNKVQWCXFUNO
      YKVQXFVAVQXKUSVBSVCWEYHVDSVCUKWHVRWJVTIABABVLVOVQCDCDVLRZVORVQRZVEBABAVQV
      OVLDCDCYMVNVMBAXJXHTABXHXJTUHYLVESWKWDWEEJWKWCUOWKLLVJVJPQZWKJWCYNUOLWBWK
      VJVFWKRVGVHVIVKUK $.

    sq3deccom12.c $e |- C e. NN0 $.
    sq3deccom12.d $e |- ( A + C ) = D $.
    $( Variant of ~ sqdeccom12 with a three digit square.  (Contributed by
       Steven Nguyen, 3-Jan-2023.) $)
    sq3deccom12 $p |- ( ( ; ; A B C x. ; ; A B C ) - ( ; D B x. ; D B ) ) =
      ( ; 9 9 x. ( ( ; A B x. ; A B ) - ( C x. C ) ) ) $=
      ( cdc cmul co cmin c9 cc0 caddc 0nn0 eqid nn0cni addcomli addlidi decaddi
      decadd deccl eqtr3i oveq12i oveq2i sqdeccom12 eqtri ) ABIZCIZUJJKZDBIZULJ
      KZLKUKCUIIZUNJKZLKMMIUIUIJKCCJKLKJKUMUOUKLULUNULUNJCNIZUIOKULUNCNABDBUPUI
      GPEFUPQZUIQACDAERCGRHSBBFRTUBCNUIUPUIGPABEFUCZUQUIUIURRTUAUDZUSUEUFUICURG
      UGUH $.
  $}

  $( 4 times 5 equals 20.  (Contributed by SN, 30-Mar-2025.) $)
  4t5e20 $p |- ( 4 x. 5 ) = ; 2 0 $=
    ( c5 c4 c2 cc0 cdc 5cn 4cn 5t4e20 mulcomli ) ABCDEFGHI $.

  $( A third of a number plus the number is four thirds of the number.
     (Contributed by SN, 19-Nov-2025.) $)
  3rdpwhole $p |- ( A e. CC -> ( ( A / 3 ) + A ) = ( 4 x. ( A / 3 ) ) ) $=
    ( cc wcel c1 c3 caddc co cdiv cmul c4 1cnd 3cn a1i cc0 3ne0 mp3an23 adddird
    wne divcl wceq 1p3e4 oveq1d mullidd divcan2 oveq12d 3eqtr3rd ) ABCZDEFGZAEH
    GZIGDUIIGZEUIIGZFGJUIIGUIAFGUGDEUIUGKEBCZUGLMUGULENRZUIBCLOAESPZQUGUHJUIIUH
    JTUGUAMUBUGUJUIUKAFUGUIUNUCUGULUMUKATLOAEUDPUEUF $.

  $( The square of 4 is 16.  (Contributed by SN, 26-Aug-2025.) $)
  sq4 $p |- ( 4 ^ 2 ) = ; 1 6 $=
    ( c4 c2 cexp co cmul c1 c6 cdc 4cn sqvali 4t4e16 eqtri ) ABCDAAEDFGHAIJKL
    $.

  $( The square of 5 is 25.  (Contributed by SN, 26-Aug-2025.) $)
  sq5 $p |- ( 5 ^ 2 ) = ; 2 5 $=
    ( c5 c2 cexp co cmul cdc 5cn sqvali 5t5e25 eqtri ) ABCDAAEDBAFAGHIJ $.

  $( The square of 6 is 36.  (Contributed by SN, 26-Aug-2025.) $)
  sq6 $p |- ( 6 ^ 2 ) = ; 3 6 $=
    ( c6 c2 cexp co cmul c3 cdc 6cn sqvali 6t6e36 eqtri ) ABCDAAEDFAGAHIJK $.

  $( The square of 7 is 49.  (Contributed by SN, 26-Aug-2025.) $)
  sq7 $p |- ( 7 ^ 2 ) = ; 4 9 $=
    ( c7 c2 cexp co cmul c4 c9 cdc 7cn sqvali 7t7e49 eqtri ) ABCDAAEDFGHAIJKL
    $.

  $( The square of 8 is 64.  (Contributed by SN, 26-Aug-2025.) $)
  sq8 $p |- ( 8 ^ 2 ) = ; 6 4 $=
    ( c8 c2 cexp co cmul c6 c4 cdc 8cn sqvali 8t8e64 eqtri ) ABCDAAEDFGHAIJKL
    $.

  $( The square of 9 is 81.  (Contributed by SN, 30-Mar-2025.) $)
  sq9 $p |- ( 9 ^ 2 ) = ; 8 1 $=
    ( c9 c2 cexp co cmul c8 c1 cdc 9cn sqvali 9t9e81 eqtri ) ABCDAAEDFGHAIJKL
    $.

  $( The positive reals are a subset of the complex numbers.  (Contributed by
     SN, 1-Oct-2025.) $)
  rpsscn $p |- RR+ C_ CC $=
    ( crp cr cc rpssre ax-resscn sstri ) ABCDEF $.

  $( 4 is a positive real.  (Contributed by SN, 26-Aug-2025.) $)
  4rp $p |- 4 e. RR+ $=
    ( c4 4re 4pos elrpii ) ABCD $.

  $( 6 is a positive real.  (Contributed by SN, 26-Aug-2025.) $)
  6rp $p |- 6 e. RR+ $=
    ( c6 6re 6pos elrpii ) ABCD $.

  $( 7 is a positive real.  (Contributed by SN, 26-Aug-2025.) $)
  7rp $p |- 7 e. RR+ $=
    ( c7 7re 7pos elrpii ) ABCD $.

  $( 8 is a positive real.  (Contributed by SN, 26-Aug-2025.) $)
  8rp $p |- 8 e. RR+ $=
    ( c8 8re 8pos elrpii ) ABCD $.

  $( 9 is a positive real.  (Contributed by SN, 26-Aug-2025.) $)
  9rp $p |- 9 e. RR+ $=
    ( c9 9re 9pos elrpii ) ABCD $.

  $( Calculate a product by long multiplication as a base comparison with other
     multiplication algorithms.

     Conveniently, ` 7 1 1 ` has two ones which greatly simplifies calculations
     like ` 2 3 5 x. 1 ` .  There isn't a higher level ~ mulcomli saving the
     lower level uses of ~ mulcomli within ` 2 3 5 x. 7 ` since mulcom2 doesn't
     exist, but if commuted versions of theorems like ~ 7t2e14 are added then
     this proof would benefit more than ~ ex-decpmul .

     For practicality, this proof doesn't have "e167085" at the end of its name
     like ~ 2p2e4 or ~ 8t7e56 .  (Contributed by Steven Nguyen, 10-Dec-2022.)
     (New usage is discouraged.) $)
  235t711 $p |- ( ; ; 2 3 5 x. ; ; 7 1 1 ) = ; ; ; ; ; 1 6 7 0 8 5 $=
    ( c7 c1 cdc c6 c5 c2 c3 2nn0 3nn0 deccl 5nn0 7nn0 1nn0 eqid c4 caddc co 2cn
    decaddi cmul cc0 c8 8nn0 nn0cni 3p2e5 addcomli 0nn0 4nn0 6nn0 nn0addcli 7cn
    7t2e14 mulcomli 4p2e6 3cn 7t3e21 decmul1c 4cn addcli ax-1cn 6p1e7 eqtri 5cn
    oveq1i 7t5e35 3p1e4 5p5e10 decaddci2 decmac mulridi 5p3e8 decma2c decmul2c
    ) ABCZBBDCZACZUACZUBCEFGCZECZVRVNBCZVREFGHIJZKJZABLMJMVTNKWAABFGVSVQUBVRVNV
    RLMHIVNNVRNZWBUCWAVREFEAVPUAOVSFVRPQWAKHKVSNVRFFECVRWAUDRFGEVRFHIHWCUESUFLU
    GUHVOBAVRATQFOPQZBDMUIJMFOHUHUJFGVOBAFVRLHIWCMHBODFATQFMUHHAFBOCUKRULUMUNSA
    GFBCUKUOUPUMUQWDBAFORURUSUTWDBPQDBPQAWDDBPOFDURRUNUFVDVAVBUFSGEOEATQEIKKAEG
    ECUKVCVEUMVFVGVHVIVREUBVSBTQGWAKIVSVSWBUDVJZVKSVLWEVM $.

  $( Example usage of ~ decpmul .  This proof is significantly longer than
     ~ 235t711 .  There is more unnecessary carrying compared to ~ 235t711 .
     Although saving 5 visual steps, using ~ mulcomli early on increases the
     compressed proof length.  (Contributed by Steven Nguyen, 10-Dec-2022.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  ex-decpmul $p |- ( ; ; 2 3 5 x. ; ; 7 1 1 ) = ; ; ; ; ; 1 6 7 0 8 5 $=
    ( c2 c3 cdc c5 c7 c1 c6 c8 2nn0 3nn0 deccl 5nn0 7nn0 1nn0 eqid cmul decaddi
    cc0 co 5cn 6nn0 c4 4nn0 7cn 2cn 7t2e14 mulcomli 4p2e6 7t3e21 decmul1c 1p2e3
    3cn nn0cni mulridi decmul2c 7t5e35 mullidi decmul1 5p2e7 5p3e8 decadd dec0h
    addcomli eqtri 0nn0 8nn0 caddc 3p3e6 6p1e7 7p3e10 decaddc2 addlidi decpmul
    8cn ) ABCZDEFCZFFGCZBCZBCZBECZHCZRDVQECZRCZHCABIJKZLEFMNKZNEFVRBVOAVPWDMNVP
    OZJIVQFBVOEPSAFGNUAKZNIABVQFEAVOMIJVOONIFUBGAEPSANUCIEAFUBCUDUEUFUGUHQEBAFC
    UDULUIUGUJUKQVOVOWDUMUNZUOABBDCZDVTHVOFPSDVPPSIJBDJLKZLWHVPDWIDCVPWEUMTEFWI
    DDVPLMNWFUPDTUQURUGWIAVTWIWJUMUEBDEWIAJLIWIOUSQVCDBHTULUTVCVADFPSDRDCDTUNDL
    VBVDVSRVTHWCHVSRCZWAVRBVQBWGJKZJKVEBEJMKVFWKOWAOVRBBEWBVSVTWLJJMVSOVTOVQGEV
    RBVGSFWGUANVQBGVRBWGJJVROVHQVIQEBFRCUDULVJVCVKHVNVLVAVELVM $.

  $( Membership in a successor upper set of integers.  (Contributed by SN,
     5-Jul-2025.) $)
  eluzp1 $p |- ( M e. ZZ ->
    ( N e. ( ZZ>= ` ( M + 1 ) ) <-> ( N e. ZZ /\ M < N ) ) ) $=
    ( cz wcel clt wbr wa c1 caddc cle cuz cfv zltp1le pm5.32da peano2z 3biant1d
    co w3a eluz2 bitr4di bitr2d ) ACDZBCDZABEFZGUCAHIQZBJFZGZBUEKLDZUBUCUDUFABM
    NUBUGUECDZUCUFRUHUBUFUCUIAOPUEBSTUA $.

  $( Shorter proof of ~ eluzp1l .  (Contributed by NM, 12-Sep-2005.)  (Revised
     by SN, 5-Jul-2025.) $)
  sn-eluzp1l $p |- ( ( M e. ZZ /\ N e. ( ZZ>= ` ( M + 1 ) ) ) -> M < N ) $=
    ( cz wcel c1 caddc co cuz cfv clt wbr eluzp1 simplbda ) ACDBAEFGHIDBCDABJKA
    BLM $.

  ${
    $d N k $.  $d C k $.
    fz1sumconst.n $e |- ( ph -> N e. NN0 ) $.
    fz1sumconst.c $e |- ( ph -> C e. CC ) $.
    $( The sum of ` N ` constant terms ( ` k ` is not free in ` C ` ).
       (Contributed by SN, 21-Mar-2025.) $)
    fz1sumconst $p |- ( ph -> sum_ k e. ( 1 ... N ) C = ( N x. C ) ) $=
      ( c1 cfz co csu chash cfv cmul cfn wcel cc wceq fzfi fsumconst sylancr
      cn0 hashfz1 syl oveq1d eqtrd ) AGDHIZBCJZUFKLZBMIZDBMIAUFNOBPOUGUIQGDRFUF
      BCSTAUHDBMADUAOUHDQEDUBUCUDUE $.
  $}

  ${
    $d B k $.  $d N k $.  $d ph k $.
    fz1sump1.n $e |- ( ph -> N e. NN0 ) $.
    fz1sump1.a $e |- ( ( ph /\ k e. ( 1 ... ( N + 1 ) ) ) -> A e. CC ) $.
    fz1sump1.s $e |- ( k = ( N + 1 ) -> A = B ) $.
    $( Add one more term to a sum.  Special case of ~ fsump1 generalized to
       ` N e. NN0 ` .  (Contributed by SN, 22-Mar-2025.) $)
    fz1sump1 $p |- ( ph -> sum_ k e. ( 1 ... ( N + 1 ) ) A =
                             ( sum_ k e. ( 1 ... N ) A + B ) ) $=
      ( c1 caddc co cfz csu cmin cn cuz cfv cn0 wcel nn0p1nn nnuz fsumm1 nn0cnd
      syl eleqtrdi 1cnd pncand oveq2d sumeq1d oveq1d eqtrd ) AIEIJKZLKBDMIULINK
      ZLKZBDMZCJKIELKZBDMZCJKABCDIULAULOIPQAERSULOSFETUDUAUEGHUBAUOUQCJAUNUPBDA
      UMEILAEIAEFUCAUFUGUHUIUJUK $.
  $}

  ${
    $d N k $.
    $( The Odd Number Theorem.  The sum of the first ` N ` odd numbers is
       ` N ^ 2 ` .  A corollary of ~ arisum .  (Contributed by SN,
       21-Mar-2025.) $)
    oddnumth $p |-
      ( N e. NN0 -> sum_ k e. ( 1 ... N ) ( ( 2 x. k ) - 1 ) = ( N ^ 2 ) ) $=
      ( cn0 wcel c1 cfz co c2 cmul cmin csu cexp caddc fzfid 2cnd elfznn adantl
      cv cc 1cnd nncnd mulcld fsumsub cdiv arisum oveq2d fsummulc2 nn0cn addcld
      wa sqcld cc0 wne 2ne0 a1i divcan2d 3eqtr3d id fz1sumconst mulridd oveq12d
      eqtrd pncand 3eqtrd ) BCDZEBFGZHARZIGZEJGAKVFVHAKZVFEAKZJGBHLGZBMGZBJGVKV
      EVFVHEAVEEBNZVGVFDZVHSDVEVNHVGVNOVNVGVGBPUAZUBQVEVNUJTUCVEVIVLVJBJVEHVFVG
      AKZIGHVLHUDGZIGVIVLVEVPVQHIABUEUFVEVFVGHAVMVEOZVNVGSDVEVOQUGVEVLHVEVKBVEB
      BUHZUKZVSUIVRHULUMVEUNUOUPUQVEVJBEIGBVEEABVEURVETUSVEBVSUTVBVAVEVKBVTVSVC
      VD $.

    $( Nicomachus's Theorem.  The sum of the odd numbers from ` N ^ 2 - N + 1 `
       to ` N ^ 2 + N - 1 ` is ` N ^ 3 ` .  Proof 2 from
       ~ https://proofwiki.org/wiki/Nicomachus%27s_Theorem .  (Contributed by
       SN, 21-Mar-2025.) $)
    nicomachus $p |- ( N e. NN0 ->
      sum_ k e. ( 1 ... N ) ( ( ( N ^ 2 ) - N ) + ( ( 2 x. k ) - 1 ) )
                                                               = ( N ^ 3 ) ) $=
      ( cn0 wcel c1 cfz co c2 cexp cmin cmul caddc csu c3 cc subcld a1i oveq12d
      sqcld 3eqtrd cv fzfid nn0cn adantr 2cnd elfznn adantl mulcld 1cnd fsumadd
      wa nncnd fz1sumconst subdid df-3 oveq2i 2nn0 expp1d eqtrid mulcomd eqtr2d
      id sqvald eqcomd oddnumth 3nn0 expcld npcand ) BCDZEBFGZBHIGZBJGZHAUAZKGZ
      EJGZLGAMVJVLAMZVJVOAMZLGBNIGZVKJGZVKLGVRVIVJVLVOAVIEBUBVIVMVJDZUKZVKBWABV
      IBODVTBUCZUDZSWCPWAVNEWAHVMWAUEVTVMODVIVTVMVMBUFULUGUHWAUIPUJVIVPVSVQVKLV
      IVPBVLKGBVKKGZBBKGZJGVSVIVLABVIVBVIVKBVIBWBSZWBPUMVIBVKBWBWFWBUNVIWDVRWEV
      KJVIVRVKBKGZWDVIVRBHELGZIGWGNWHBIUOUPVIBHWBHCDVIUQQURUSVIVKBWFWBUTVAVIVKW
      EVIBWBVCVDRTABVERVIVRVKVIBNWBNCDVIVFQVGWFVHT $.

    $d N k l m x y $.
    $( The sum of the first ` N ` perfect cubes is the sum of the first ` N `
       nonnegative integers, squared.  This is the Proof by Nicomachus from
       ~ https://proofwiki.org/wiki/Sum_of_Sequence_of_Cubes using induction
       and index shifting to collect all the odd numbers.  (Contributed by SN,
       22-Mar-2025.) $)
    sumcubes $p |- ( N e. NN0 -> sum_ k e. ( 1 ... N ) ( k ^ 3 )
                             = ( sum_ k e. ( 1 ... N ) k ^ 2 ) ) $=
      ( vl vm cn0 wcel c1 cfz co c2 cmin cmul caddc csu wceq cc0 sumeq1d oveq2d
      c0 cc vx vy cv cexp c3 oveq2 eqeq12d weq sum0 eqtr4i sumeq1i eqtri oveq2i
      fz10 3eqtr4i wa simpr fzfid cn elfznn adantl nnnn0d fsumnn0cl nn0p1nn syl
      nn0zd nnzd peano2nn0 zaddcld 2cnd elfzelz zcnd mulcld subcld fsumshftm cz
      1cnd oveq1d zred fsumrecl pncan2d nn0cnd oveq12d adantr adddid addsubassd
      recnd addsub12d cdiv arisum nn0cn sqcld addcld wne 2ne0 divcan2d pnpcan2d
      a1i binom21 2timesd mvrladdd eqtrd 3eqtrrd 3eqtrd sylan2 sumeq12dv eqtr2d
      addcl syl2an adantll fsumcl oveq1 fz1sump1 clt wbr cin fzdisj cuz cfv cun
      id ltp1d eleqtrdi uzidd uzaddcl syl2anc fzsplit2 fsumsplit 3eqtr4d nn0ind
      nnuz ex wss fz1ssnn nnssnn0 sstri sselda nicomachus sumeq2dv oddnumth
      3eqtr3d ) BEFZGBHIZGAUCZHIZUUDJUDIZUUDKIZJCUCZLIZGKIZMIZCNZANZGUUCUUDANZH
      IZJDUCZLIZGKIZDNZUUCUUDUEUDIZANUUNJUDIZGUAUCZHIZUULANZGUVCUUDANZHIZUURDNZ
      OGPHIZUULANZGUVHUUDANZHIZUURDNZOGUBUCZHIZUULANZGUVNUUDANZHIZUURDNZOZGUVMG
      MIZHIZUULANZGUWAUUDANZHIZUURDNZOZUUMUUSOUAUBBUVBPOZUVDUVIUVGUVLUWGUVCUVHU
      ULAUVBPGHUFZQUWGUVFUVKUURDUWGUVEUVJGHUWGUVCUVHUUDAUWHQRQUGUAUBUHZUVDUVOUV
      GUVRUWIUVCUVNUULAUVBUVMGHUFZQUWIUVFUVQUURDUWIUVEUVPGHUWIUVCUVNUUDAUWJQRQU
      GUVBUVTOZUVDUWBUVGUWEUWKUVCUWAUULAUVBUVTGHUFZQUWKUVFUWDUURDUWKUVEUWCGHUWK
      UVCUWAUUDAUWLQRQUGUVBBOZUVDUUMUVGUUSUWMUVCUUCUULAUVBBGHUFZQUWMUVFUUOUURDU
      WMUVEUUNGHUWMUVCUUCUUDAUWNQRQUGSUULANZSUURDNZUVIUVLUWOPUWPUULAUIUURDUIUJU
      VHSUULAUNUKUVKSUURDUVKUVHSUVJPGHUVJSUUDANPUVHSUUDAUNUKUUDAUIULUMUNULUKUOU
      VMEFZUVSUWFUWQUVSUPZUVOUWAUVTJUDIZUVTKIZUUJMIZCNZMIZUVRUVPGMIZUVPUVTMIZHI
      ZUURDNZMIZUWBUWEUWRUVOUVRUXBUXGMUWQUVSUQUWQUXBUXGOUVSUWQUXGUXDUVPKIZUXEUV
      PKIZHIZJUUHUVPMIZLIZGKIZCNUXBUWQUURUXNDCUVPUXDUXEUWQUVPUWQUVNUUDAUWQGUVMU
      RZUWQUUDUVNFZUPZUUDUXPUUDUSFUWQUUDUVMUTVAVBVCZVFZUWQUXDUWQUVPEFUXDUSFUXRU
      VPVDVEZVGUWQUVPUVTUXSUWQUVTUVMVHZVFVIUWQUUPUXFFZUPZUUQGUYCJUUPUYCVJUYBUUP
      TFZUWQUYBUUPUUPUXDUXEVKVLVAVMUYCVQVNUUPUXLOUUQUXMGKUUPUXLJLUFVRVOUWQUXKUW
      AUXNUXACUWQUXIGUXJUVTHUWQUVPGUWQUVPUWQUVNUUDAUXOUXQUUDUXPUUDVPFUWQUUDGUVM
      VKVAVSVTZWGZUWQVQZWAUWQUVPUVTUYFUWQUVTUYAWBWAWCUUHUXKFZUWQUUHTFZUXNUXAOUY
      HUUHUUHUXIUXJVKVLUWQUYIUPZUXNUUIJUVPLIZMIZGKIUUIUYKGKIMIZUXAUYJUXMUYLGKUY
      JJUUHUVPUYJVJZUWQUYIUQZUWQUVPTFUYIUYFWDZWEVRUYJUUIUYKGUYJJUUHUYNUYOVMZUYJ
      JUVPUYNUYPVMZUYJVQZWFUYJUYMUYKUUJMIUXAUYJUUIUYKGUYQUYRUYSWHUYJUYKUWTUUJMU
      WQUYKUWTOUYIUWQUYKJUVMJUDIZUVMMIZJWIIZLIVUAUWTUWQUVPVUBJLAUVMWJRUWQVUAJUW
      QUYTUVMUWQUVMUVMWKZWLZVUCWMUWQVJZJPWNUWQWOWRWPUWQUWTUYTJUVMLIZMIZGMIZUVTK
      IVUGUVMKIZVUAUWQUWSVUHUVTKUWQUVMTFUWSVUHOVUCUVMWSVEVRUWQVUGUVMGUWQUYTVUFV
      UDUWQJUVMVUEVUCVMZWMVUCUYGWQUWQVUIUYTVUFUVMKIZMIVUAUWQUYTVUFUVMVUDVUJVUCW
      FUWQVUKUVMUYTMUWQVUFUVMUVMVUCVUCUWQUVMVUCWTXARXBXCXDWDVRXBXDXEXFXGWDWCUWQ
      UWBUXCOUVSUWQUULUXBAUVMUWQYAZUWQUUDUWAFZUPZUUEUUKCVUNGUUDURVUMUUHUUEFZUUK
      TFZUWQVUMUUGTFUUJTFVUPVUOVUMUUFUUDVUMUUDVUMUUDUUDGUVTVKVLZWLVUQVNVUOUUIGV
      UOJUUHVUOVJVUOUUHUUHGUUDVKVLVMVUOVQVNUUGUUJXHXIXJXKUUDUVTOZUUEUWAUUKUXACU
      UDUVTGHUFVURUUKUXAOVUOVURUUGUWTUUJMVURUUFUWSUUDUVTKUUDUVTJUDXLVURYAZWCVRW
      DXFXMWDUWRUWEGUXEHIZUURDNZUXHUWRUWDVUTUURDUWRUWCUXEGHUWQUWCUXEOUVSUWQUUDU
      VTAUVMVULVUMUUDTFUWQVUQVAVUSXMWDRQUWQVVAUXHOUVSUWQUVQUXFUURVUTDUWQUVPUXDX
      NXOUVQUXFXPSOUWQUVPUYEYBGUVPUXDUXEXQVEUWQUXDGXRXSZFUXEUVPXRXSZFZVUTUVQUXF
      XTOUWQUXDUSVVBUXTYKYCUWQUVPVVCFUVTEFVVDUWQUVPUXSYDUYAUVTUVPUVPYEYFUVPGUXE
      YGYFUWQGUXEURUWQUUPVUTFZUPZUUQGVVFJUUPVVFVJVVEUYDUWQVVEUUPUUPGUXEVKVLVAVM
      VVFVQVNYHWDXBYIYLYJUUBUUCUULUUTAUUBUUDUUCFUPUUDEFUULUUTOUUBUUCEUUDUUCEYMU
      UBUUCUSEBYNYOYPWRYQZCUUDYRVEYSUUBUUNEFUUSUVAOUUBUUCUUDAUUBGBURVVGVCDUUNYT
      VEUUA $.
  $}

  $( ` _i ` is not 1.  (Contributed by SN, 25-Apr-2025.) $)
  ine1 $p |- _i =/= 1 $=
    ( c1 ci cr wcel wn wne 1re inelr nelne2 mp2an necomi ) ABACDBCDEABFGHABCIJK
    $.

  $( 0 times ` _i ` equals 0.  (Contributed by SN, 25-Apr-2025.) $)
  0tie0 $p |- ( 0 x. _i ) = 0 $=
    ( ci cc0 ax-icn 0cn it0e0 mulcomli ) ABBCDEF $.

  $( ` _i ` times 1 equals ` _i ` .  (Contributed by SN, 25-Apr-2025.) $)
  it1ei $p |- ( _i x. 1 ) = _i $=
    ( ci ax-icn mulridi ) ABC $.

  $( 1 times ` _i ` equals ` _i ` .  (Contributed by SN, 25-Apr-2025.) $)
  1tiei $p |- ( 1 x. _i ) = _i $=
    ( ci ax-icn mullidi ) ABC $.

  $( ` _i ` times a real is real iff the real is zero.  (Contributed by SN,
     25-Apr-2025.) $)
  itrere $p |- ( R e. RR -> ( ( _i x. R ) e. RR <-> R = 0 ) ) $=
    ( cr wcel ci cmul co cc0 wceq rimul ex oveq2 it0e0 eqeltri eqeltrdi impbid1
    0re ) ABCZDAEFZBCZAGHZQSTAIJTRDGEFZBAGDEKUAGBLPMNO $.

  $( A real times ` _i ` is real iff the real is zero.  (Contributed by SN,
     25-Apr-2025.) $)
  retire $p |- ( R e. RR -> ( ( R x. _i ) e. RR <-> R = 0 ) ) $=
    ( cr wcel ci cmul co cc0 wceq recn ax-icn a1i mulcomd eleq1d itrere bitrd
    cc ) ABCZADEFZBCDAEFZBCAGHQRSBQADAIDPCQJKLMANO $.

  ${
    $d A w x y z $.  $d B w x y z $.  $d C w x y z $.
    ixxdisjd.a $e |- ( ph -> A e. RR* ) $.
    ixxdisjd.b $e |- ( ph -> B e. RR* ) $.
    ixxdisjd.c $e |- ( ph -> C e. RR* ) $.
    $( Adjacent intervals where the lower interval is right-closed and the
       upper interval is open are disjoint.  (Contributed by SN,
       1-Oct-2025.) $)
    iocioodisjd $p |- ( ph -> ( ( A (,] B ) i^i ( B (,) C ) ) = (/) ) $=
      ( vx vy vz vw cxr wcel cioc co cioo cin c0 wceq clt df-ioc df-ioo xrltnle
      cle cv ixxdisj syl3anc ) ABLMCLMDLMBCNOCDPOQRSEFGHIJKBCDPTUDTTNHIJUAHIJUB
      CKUEUCUFUG $.
  $}

  $( A positive real is its own absolute value.  (Contributed by SN,
     1-Oct-2025.) $)
  rpabsid $p |- ( R e. RR+ -> ( abs ` R ) = R ) $=
    ( crp wcel cr cc0 cle wbr cabs cfv wceq rpre rpge0 absid syl2anc ) ABCADCEA
    FGAHIAJAKALAMN $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Exponents and divisibility
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    oexpreposd.n $e |- ( ph -> N e. RR ) $.
    oexpreposd.m $e |- ( ph -> M e. NN ) $.
    oexpreposd.1 $e |- ( ph -> -. ( M / 2 ) e. NN ) $.
    $( Lemma for ~ dffltz .  For a more standard version, see ~ expgt0b .
       TODO-SN?:  This can be used to show ~ exp11d holds for all integers when
       the exponent is odd.  (Contributed by SN, 4-Mar-2023.) $)
    oexpreposd $p |- ( ph -> ( 0 < N <-> 0 < ( N ^ M ) ) ) $=
      ( cc0 clt wbr cexp co wa cr wcel adantr simpr wn wceq cn c2 cz syl3anc ex
      nnzd expgt0 wo lttrid notbid notnotr 0re ltnri 0expd breq2d mtbiri eqcomd
      0red oveq1d mtbird cneg renegcld cc cdvds recnd cdiv cnumer cfv cdenom c1
      cmul cq wb zq adantl qden1elz syl mpbird oveq2d qmuldeneqnum zcnd mulridd
      3eqtr3rd nnred 2re a1i nngt0d 2pos divgt0d qgt0numnn syl2anr mtand evend2
      eqeltrd oexpneg biimpd nnnn0d reexpcld biimtrdi lt0neg1d lt0neg2d 3imtr4d
      pm2.46 3syld jaod syl5 sylbid impcon4bid ) AGCHIZGCBJKZHIZAXGXIAXGLCMNZBU
      ANZXGXIAXJXGDOAXKXGABEUDZOAXGPCBUEUBUCAXGQGCRZCGHIZUFZQZQZXIQZAXGXPAGCAUP
      ZDUGUHXQXOAXRXOUIAXMXRXNAXMXRAXMLZXIGGBJKZHIZAYBQXMAYBGGHIGUJUKAYAGGHABEU
      LUMUNOXTXHYAGHXTCGBJXTGCAXMPUOUQUMURUCAGCUSZHIZXHUSZGHIZQZXNXRAYDGYCBJKZH
      IZGYEHIZYGAYDYIAYDLYCMNZXKYDYIAYKYDACDUTOAXKYDXLOAYDPYCBUEUBUCAYIYJAYHYEG
      HACVANBSNTBVBIZQYHYERACDVCEAYLBTVDKZUANZAYNYMSNFAYNLZYMYMVEVFZSYOYMYMVGVF
      ZVIKZYMVHVIKYPYMYOYQVHYMVIYOYQVHRZYNAYNPZYOYMVJNZYSYNVKYNUUAAYMVLZVMZYMVN
      VOVPVQYOUUAYRYPRUUCYMVRVOYOYMYOYMYTVSVTWAYNUUAGYMHIYPSNAUUBABTABEWBTMNAWC
      WDABEWEGTHIAWFWDWGYMWHWIWLWJAXKYLYNVKXLBWKVOURCBWMUBUMWNAYJGYERZYFUFQYGAG
      YEXSAXHACBDABEWOWPZUTUGUUDYFXAWQXBACDWRAXIYFAXHUUEWSUHWTXCXDXEXF $.
  $}

  ${
    explt1d.a $e |- ( ph -> A e. RR ) $.
    explt1d.n $e |- ( ph -> N e. NN ) $.
    explt1d.0 $e |- ( ph -> 0 <_ A ) $.
    explt1d.1 $e |- ( ph -> A < 1 ) $.
    $( A nonnegative real number less than one raised to a positive integer is
       less than one.  (Contributed by SN, 3-Jul-2025.) $)
    explt1d $p |- ( ph -> ( A ^ N ) < 1 ) $=
      ( cexp co c1 clt wbr cc0 wceq crp wcel wa adantr simpr a1i breq1d wne cle
      oveq1 cr ne0gt0d elrpd 1rp cn ltexp1dd syldan 0lt1 0expd cz nnzd 1exp syl
      3brtr4d pm2.61ne breqtrd ) ABCHIZJCHIZJKAVAVBKLZMCHIZVBKLBMBMNVAVDVBKBMCH
      UDUAABMUBZBOPZVCAVEQZBABUEPVEDRZVGBVHAMBUCLVEFRAVESUFUGAVFQZBJCAVFSJOPVIU
      HTACUIPVFERABJKLVFGRUJUKAMJVDVBKMJKLAULTACEUMACUNPVBJNACEUOCUPUQZURUSVJUT
      $.
  $}

  ${
    expeq1d.a $e |- ( ph -> A e. RR ) $.
    expeq1d.n $e |- ( ph -> N e. NN ) $.
    expeq1d.0 $e |- ( ph -> 0 <_ A ) $.
    $( A nonnegative real number is one if and only if it is one when raised to
       a positive integer.  (Contributed by SN, 3-Jul-2025.) $)
    expeq1d $p |- ( ph -> ( ( A ^ N ) = 1 <-> A = 1 ) ) $=
      ( cexp co c1 wceq cz wcel nnzd 1exp adantr cc0 wne a1i oveq1 eqeq1d wa cr
      syl eqeq2d cle wbr 0ne1 0expd 3netr4d biimpac adantll mteqand ne0gt0d crp
      elrpd 1rp cn simpr exp11nnd ex sylbird syl5ibrcom impbid ) ABCGHZIJZBIJZA
      VEVDICGHZJZVFAVGIVDACKLVGIJZACEMCNUCZUDAVHVFAVHUAZBICVKBABUBLVHDOZVKBVLAP
      BUEUFVHFOVKBPPCGHZVGAVMVGQVHAPIVMVGPIQAUGRACEUHVJUIOVHBPJZVMVGJZAVNVHVOVN
      VDVMVGBPCGSTUJUKULUMUOIUNLVKUPRACUQLVHEOAVHURUSUTVAAVEVFVIVJVFVDVGIBICGST
      VBVC $.
  $}

  ${
    expeqidd.a $e |- ( ph -> A e. RR ) $.
    expeqidd.n $e |- ( ph -> N e. ( ZZ>= ` 2 ) ) $.
    expeqidd.0 $e |- ( ph -> 0 <_ A ) $.
    $( A nonnegative real number is zero or one if and only if it is itself
       when raised to an integer greater than one.  (Contributed by SN,
       3-Jul-2025.) $)
    expeqidd $p |- ( ph -> ( ( A ^ N ) = A <-> ( A = 0 \/ A = 1 ) ) ) $=
      ( cexp co wceq cc0 c1 wa cdiv wcel ad2antrr cn syl adantr ex oveq1 wo wne
      wn df-ne cmin cc recnd simplr cz cuz cfv eluz2nn nnzd expm1d simpr oveq1d
      c2 dividd 3eqtrd cr uz2m1nn cle wbr expeq1d biimpa syldan an32s biimtrrid
      orrd 0expd id eqeq12d syl5ibrcom 1exp jaod impbid ) ABCGHZBIZBJIZBKIZUAZA
      VRWAAVRLZVSVTVSUCBJUBZWBVTBJUDWBWCVTAWCVRVTAWCLZVRBCKUEHZGHZKIZVTWDVRLZWF
      VQBMHBBMHKWHBCABUFNWCVRABDUGOZAWCVRUHZACUINZWCVRACACUQUJUKNZCPNECULQZUMZO
      UNWHVQBBMWDVRUOUPWHBWIWJURUSWDWGVTWDBWEABUTNWCDRAWEPNZWCAWLWOECVAQRAJBVBV
      CWCFRVDVEVFVGSVHVISAVSVRVTAVRVSJCGHZJIACWMVJVSVQWPBJBJCGTVSVKVLVMAVRVTKCG
      HZKIZAWKWRWNCVNQVTVQWQBKBKCGTVTVKVLVMVOVP $.
  $}

  ${
    exp11d.1 $e |- ( ph -> A e. RR+ ) $.
    exp11d.2 $e |- ( ph -> B e. RR+ ) $.
    exp11d.3 $e |- ( ph -> N e. ZZ ) $.
    exp11d.4 $e |- ( ph -> N =/= 0 ) $.
    exp11d.5 $e |- ( ph -> ( A ^ N ) = ( B ^ N ) ) $.
    $( ~ exp11nnd for nonzero integer exponents.  (Contributed by SN,
       14-Sep-2023.) $)
    exp11d $p |- ( ph -> A = B ) $=
      ( cc0 wceq cn wcel wa simpr adantr crp cexp co cc wne pm2.21ddne exp11nnd
      cneg rpcnd nnnn0d expcld rpne0d nnzd expne0d c1 cdiv zcnd expneg2 syl3anc
      cn0 3eqtr3d rec11d cr w3o cz elz sylib simprd mpjao3dan ) ADJKZBCKZDLMZDU
      DZLMZAVFNVGDJAVFOADJUAVFHPUBAVHNBCDABQMZVHEPACQMZVHFPAVHOABDRSZCDRSZKZVHI
      PUCAVJNZBCVIAVKVJEPZAVLVJFPZAVJOZVPBVIRSZCVIRSZVPBVIVPBVQUEZVPVIVSUFZUGVP
      CVIVPCVRUEZWCUGVPBVIWBVPBVQUHVPVIVSUIZUJVPCVIWDVPCVRUHWEUJVPVMVNUKVTULSZU
      KWAULSZAVOVJIPVPBTMDTMZVIUPMZVMWFKWBAWHVJADGUMPZWCBDUNUOVPCTMWHWIVNWGKWDW
      JWCCDUNUOUQURUCADUSMZVFVHVJUTZADVAMWKWLNGDVBVCVDVE $.
  $}

  $( 0 divides 0.  (Contributed by SN, 15-Sep-2024.) $)
  0dvds0 $p |- 0 || 0 $=
    ( cc0 cz wcel cdvds wbr 0z dvds0 ax-mp ) ABCAADEFAGH $.

  $( Divisibility is invariant under taking the absolute value on both sides.
     (Contributed by SN, 15-Sep-2024.) $)
  absdvdsabsb $p |- ( ( M e. ZZ /\ N e. ZZ ) ->
                        ( M || N <-> ( abs ` M ) || ( abs ` N ) ) ) $=
    ( cz wcel wa cdvds wbr cabs cfv absdvdsb wb zabscl dvdsabsb sylan bitrd ) A
    CDZBCDZEABFGAHIZBFGZRBHIFGZABJPRCDQSTKALRBMNO $.

  $( The ` gcd ` of a nonnegative integer and itself is the integer.
     (Contributed by SN, 25-Aug-2024.) $)
  gcdnn0id $p |- ( N e. NN0 -> ( N gcd N ) = N ) $=
    ( cn0 wcel cgcd co cabs cfv wceq nn0z gcdid syl nn0re nn0ge0 absidd eqtrd
    cz ) ABCZAADEZAFGZAQAPCRSHAIAJKQAALAMNO $.

  ${
    gcdle1d.m $e |- ( ph -> M e. NN ) $.
    gcdle1d.n $e |- ( ph -> N e. ZZ ) $.
    $( The greatest common divisor of a positive integer and another integer is
       less than or equal to the positive integer.  (Contributed by SN,
       25-Aug-2024.) $)
    gcdle1d $p |- ( ph -> ( M gcd N ) <_ M ) $=
      ( cgcd co cdvds wbr cle cz wcel wa nnzd gcddvds syl2anc simpld cn gcdcld
      wi nn0zd dvdsle mpd ) ABCFGZBHIZUDBJIZAUEUDCHIZABKLCKLUEUGMABDNZEBCOPQAUD
      KLBRLUEUFTAUDABCUHESUADUDBUBPUC $.
  $}

  ${
    gcdle2d.m $e |- ( ph -> M e. ZZ ) $.
    gcdle2d.n $e |- ( ph -> N e. NN ) $.
    $( The greatest common divisor of a positive integer and another integer is
       less than or equal to the positive integer.  (Contributed by SN,
       25-Aug-2024.) $)
    gcdle2d $p |- ( ph -> ( M gcd N ) <_ N ) $=
      ( cgcd co cdvds wbr cle cz wcel wa nnzd gcddvds syl2anc simprd cn gcdcld
      wi nn0zd dvdsle mpd ) ABCFGZCHIZUDCJIZAUDBHIZUEABKLCKLUGUEMDACENZBCOPQAUD
      KLCRLUEUFTAUDABCDUHSUAEUDCUBPUC $.
  $}

  ${
    dvdsexpad.1 $e |- ( ph -> A e. ZZ ) $.
    dvdsexpad.2 $e |- ( ph -> B e. ZZ ) $.
    dvdsexpad.3 $e |- ( ph -> N e. NN0 ) $.
    dvdsexpad.5 $e |- ( ph -> A || B ) $.
    $( Deduction associated with ~ dvdsexpim .  (Contributed by SN,
       21-Aug-2024.) $)
    dvdsexpad $p |- ( ph -> ( A ^ N ) || ( B ^ N ) ) $=
      ( cdvds wbr cexp co cz wcel cn0 wi dvdsexpim syl3anc mpd ) ABCIJZBDKLCDKL
      IJZHABMNCMNDONTUAPEFGBCDQRS $.
  $}

  $( ~ dvdssqlem generalized to positive integer exponents.  (Contributed by
     SN, 20-Aug-2024.) $)
  dvdsexpnn $p |- ( ( A e. NN /\ B e. NN /\ N e. NN ) ->
                                    ( A || B <-> ( A ^ N ) || ( B ^ N ) ) ) $=
    ( cn wcel w3a cdvds wbr cexp co cz cn0 nnz wa nnrpd 3adant3 adantr nnexpcld
    cgcd wceq wi nnnn0 dvdsexpim syl3an gcdnncl simpl1 simpl3 expgcd syl3an3 wb
    crp simp1 3ad2ant3 simp2 gcdeq syl2anc biimpar eqtrd exp11nnd simprd syl2an
    gcddvds eqbrtrrd ex impbid ) ADEZBDEZCDEZFZABGHZACIJZBCIJZGHZVFAKEZVGBKEZVH
    CLEZVJVMUAAMZBMZCUBZABCUCUDVIVMVJVIVMNZABSJZABGVTWAACVIWAUKEZVMVFVGWBVHVFVG
    NWAABUEOPQVTAVFVGVHVMUFOVFVGVHVMUGVTWACIJZVKVLSJZVKVIWCWDTZVMVHVFVGVPWEVSAB
    CUHUIQVIWDVKTZVMVIVKDEVLDEWFVMUJVIACVFVGVHULVHVFVPVGVSUMZRVIBCVFVGVHUNWGRVK
    VLUOUPUQURUSVIWABGHZVMVFVGWHVHVFVNVOWHVGVQVRVNVONWAAGHWHABVBUTVAPQVCVDVE $.

  $( ~ dvdsexpnn generalized to include zero bases.  (Contributed by SN,
     15-Sep-2024.) $)
  dvdsexpnn0 $p |- ( ( A e. NN0 /\ B e. NN0 /\ N e. NN ) ->
                                    ( A || B <-> ( A ^ N ) || ( B ^ N ) ) ) $=
    ( cn0 wcel cn cdvds wbr cexp co wb cc0 wceq wo elnn0 wa adantl syl bibi12d
    cz wi dvdsexpnn 3expia cc nncn expeq0 sylan 0exp breq1d nnexpcl sylan2 nnzd
    nnnn0 0dvds bitrd nnz 3bitr4rd breq1 oveq1 imbitrrid expdimp dvds0 breqtrrd
    adantr 2thd breq2 breq2d syl5ibrcom breq12d bicomd breq12 simpl simpr ccase
    impancom oveq1d syl2anb 3impia ) ADEZBDEZCFEZABGHZACIJZBCIJZGHZKZVSAFEZALMZ
    NBFEZBLMZNWAWFUAZVTAOBOWGWIWHWJWKWGWIWAWFABCUBUCWHWIWAWFWIWAPZWFWHLBGHZLCIJ
    ZWDGHZKWLWDLMZWJWOWMWIBUDEWAWPWJKBUEBCUFUGWLWOLWDGHZWPWLWNLWDGWAWNLMZWICUHZ
    QUIWLWDTEWQWPKWLWDWAWICDEZWDFECUMZBCUJUKULWDUNRUOWIWMWJKZWAWIBTEXBBUPBUNRVD
    UQWHWBWMWEWOALBGURWHWCWNWDGALCIUSUISUTVAWGWAWJWFWGWAPZWFWJALGHZWCWNGHZKXCXD
    XEWGXDWAWGATEXDAUPAVBRVDXCWCLWNGXCWCTEWCLGHXCWCWAWGWTWCFEXAACUJUKULWCVBRWAW
    RWGWSQVCVEWJWBXDWEXEBLAGVFWJWDWNWCGBLCIUSVGSVHVOWAWFWHWJPZLLGHZWNWNGHZKWAXH
    XGWAWNLWNLGWSWSVIVJXFWBXGWEXHALBLGVKXFWCWNWDWNGXFALCIWHWJVLVPXFBLCIWHWJVMVP
    VISUTVNVQVR $.

  $( ~ dvdssq generalized to positive integer exponents.  (Contributed by SN,
     15-Sep-2024.) $)
  dvdsexpb $p |- ( ( A e. ZZ /\ B e. ZZ /\ N e. NN ) ->
                                    ( A || B <-> ( A ^ N ) || ( B ^ N ) ) ) $=
    ( cz wcel cn w3a cabs cfv cdvds wbr cexp co wb nn0abscl absexpd absdvdsabsb
    cn0 zcnd zexpcld dvdsexpnn0 simp1 simp3 nnnn0d simp2 breq12d bitr4d 3adant3
    syl3an12 syl2anc 3bitr4d ) ADEZBDEZCFEZGZAHIZBHIZJKZACLMZHIZBCLMZHIZJKZABJK
    ZUSVAJKZUOURUPCLMZUQCLMZJKZVCULUPREUMUQREUNURVHNAOBOUPUQCUAUIUOUTVFVBVGJUOA
    CUOAULUMUNUBZSUOCULUMUNUCUDZPUOBCUOBULUMUNUEZSVJPUFUGULUMVDURNUNABQUHUOUSDE
    VADEVEVCNUOACVIVJTUOBCVKVJTUSVAQUJUK $.

  ${
    posqsqznn.1 $e |- ( ph -> ( A ^ 2 ) e. ZZ ) $.
    posqsqznn.2 $e |- ( ph -> A e. QQ ) $.
    posqsqznn.3 $e |- ( ph -> 0 < A ) $.
    $( When a positive rational squared is an integer, the rational is a
       positive integer. ~ zsqrtelqelz with all terms squared and positive.
       (Contributed by SN, 23-Aug-2024.) $)
    posqsqznn $p |- ( ph -> A e. NN ) $=
      ( cz wcel cc0 clt wbr cn c2 cexp co csqrt cfv qred 0red ltled cq eqeltrrd
      sqrtsqd eqeltrd zsqrtelqelz syl2anc elnnz sylanbrc ) ABFGHBIJBKGABLMNZOPZ
      BFABABDQZAHBARUJESUBZAUHFGUITGUIFGCAUIBTUKDUCUHUDUEUAEBUFUG $.
  $}

  ${
    $d ph k $.  $d M k $.  $d N k $.
    zdivgd.1 $e |- ( ph -> M e. CC ) $.
    zdivgd.2 $e |- ( ph -> N e. CC ) $.
    zdivgd.3 $e |- ( ph -> M =/= 0 ) $.
    $( Two ways to express " ` N ` is an integer multiple of ` M ` ".
       Originally a subproof of ~ zdiv .  (Contributed by SN, 25-Apr-2025.) $)
    zdivgd $p |- ( ph -> ( E. k e. ZZ ( M x. k ) = N <-> ( N / M ) e. ZZ ) ) $=
      ( cv cmul co wceq cz wrex cdiv wcel wa cc zcn adantl adantr cc0 wne oveq1
      divcan3d sylan9req simplr eqeltrrd rexlimdva2 oveq2 eqeq1d rspcev syl5com
      divcan2d ex impbid ) ACBHZIJZDKZBLMZDCNJZLOZAURVABLAUPLOZPZURPUPUTLVCURUP
      UQCNJUTVCUPCVBUPQOAUPRSACQOVBETACUAUBVBGTUDUQDCNUCUEAVBURUFUGUHACUTIJZDKZ
      VAUSADCFEGUMVAVEUSURVEBUTLUPUTKUQVDDUPUTCIUIUJUKUNULUO $.
  $}

  ${
    efsubd.a $e |- ( ph -> A e. CC ) $.
    efsubd.b $e |- ( ph -> B e. CC ) $.
    $( Difference of exponents law for exponential function, deduction form.
       (Contributed by SN, 25-Apr-2025.) $)
    efsubd $p |-
      ( ph -> ( exp ` ( A - B ) ) = ( ( exp ` A ) / ( exp ` B ) ) ) $=
      ( cc wcel cmin co ce cfv cdiv wceq efsub syl2anc ) ABFGCFGBCHIJKBJKCJKLIM
      DEBCNO $.
  $}

  ${
    $d ph n $.  $d A n $.  $d B n $.
    ef11d.a $e |- ( ph -> A e. CC ) $.
    ef11d.b $e |- ( ph -> B e. CC ) $.
    $( General condition for the exponential function to be one-to-one. ~ efper
       shows that exponentiation is periodic.  (Contributed by SN,
       25-Apr-2025.) $)
    ef11d $p |- ( ph -> ( ( exp ` A ) = ( exp ` B ) <->
      E. n e. ZZ A = ( B + ( ( _i x. ( 2 x. _pi ) ) x. n ) ) ) ) $=
      ( co ce cfv c1 wceq ci c2 cpi cmul cz wcel cc a1i mulcld cmin cdiv efsubd
      caddc wrex eqeq1d ax-icn 2cnd picn subcld cc0 wne ine0 2ne0 pine0 mulne0d
      cv zdivgd wa eqcom adantr zcn adantl addrsub bitrid rexbidva wb efeq1 syl
      3bitr4rd efcld efne0d diveq1ad 3bitr3rd ) ABCUAGZHIZJKZBHIZCHIZUBGZJKBCLM
      NOGZOGZDUQZOGZUDGZKZDPUEZVRVSKAVPVTJABCEFUCUFAWDVOKZDPUEVOWBUBGPQZWGVQADW
      BVOALWALRQAUGSZAMNAUHZNRQAUISZTZTZABCEFUJZALWAWJWMLUKULAUMSAMNWKWLMUKULAU
      NSNUKULAUOSUPUPURAWFWHDPWFWEBKAWCPQZUSZWHBWEUTWQCWDBACRQWPFVAWQWBWCAWBRQW
      PWNVAWPWCRQAWCVBVCTABRQWPEVAVDVEVFAVORQVQWIVGWOVOVHVIVJAVRVSABEVKACFVKACF
      VLVMVN $.
  $}

  ${
    logccne0d.a $e |- ( ph -> A e. CC ) $.
    logccne0d.0 $e |- ( ph -> A =/= 0 ) $.
    logccne0d.1 $e |- ( ph -> A =/= 1 ) $.
    $( The logarithm isn't 0 if its argument isn't 0 or 1, deduction form.
       (Contributed by SN, 25-Apr-2025.) $)
    logccne0d $p |- ( ph -> ( log ` A ) =/= 0 ) $=
      ( cc wcel cc0 wne c1 clog cfv logccne0 syl3anc ) ABFGBHIBJIBKLHICDEBMN $.
  $}

  ${
    $d ph n $.  $d A n $.  $d B n $.  $d C n $.
    cxp112d.c $e |- ( ph -> C e. CC ) $.
    cxp112d.a $e |- ( ph -> A e. CC ) $.
    cxp112d.b $e |- ( ph -> B e. CC ) $.
    cxp112d.0 $e |- ( ph -> C =/= 0 ) $.
    cxp112d.1 $e |- ( ph -> C =/= 1 ) $.
    $( General condition for complex exponentiation to be one-to-one with
       respect to the second argument.  (Contributed by SN, 25-Apr-2025.) $)
    cxp112d $p |- ( ph -> ( ( C ^c A ) = ( C ^c B ) <-> E. n e. ZZ
      A = ( B + ( ( ( _i x. ( 2 x. _pi ) ) x. n ) / ( log ` C ) ) ) ) ) $=
      ( co wceq cfv cmul caddc cz cdiv wcel cc adantr ccxp clog ce ci c2 cpi cv
      wrex cxpefd eqeq12d logcld mulcld ef11d wa ax-icn 2cn picn mulcli a1i zcn
      adantl addcld cc0 wne logccne0d ldiv divdird divcan4d oveq1d eqtrd eqeq2d
      bitrd rexbidva 3bitrd ) ADBUAKZDCUAKZLBDUBMZNKZUCMZCVQNKZUCMZLVRVTUDUEUFN
      KZNKZEUGZNKZOKZLZEPUHBCWEVQQKZOKZLZEPUHAVOVSVPWAADBFIGUIADCFIHUIUJAVRVTEA
      BVQGADFIUKZULACVQHWKULZUMAWGWJEPAWDPRZUNZWGBWFVQQKZLWJWNBVQWFABSRWMGTAVQS
      RWMWKTZWNVTWEAVTSRWMWLTZWNWCWDWCSRWNUDWBUOUEUFUPUQURURUSWMWDSRAWDUTVAULZV
      BAVQVCVDWMADFIJVEZTZVFWNWOWIBWNWOVTVQQKZWHOKWIWNVTWEVQWQWRWPWTVGWNXACWHOA
      XACLWMACVQHWKWSVHTVIVJVKVLVMVN $.
  $}

  ${
    $d ph n $.  $d A n $.  $d B n $.  $d C n $.
    cxp111d.a $e |- ( ph -> A e. CC ) $.
    cxp111d.b $e |- ( ph -> B e. CC ) $.
    cxp111d.c $e |- ( ph -> C e. CC ) $.
    cxp111d.1 $e |- ( ph -> A =/= 0 ) $.
    cxp111d.2 $e |- ( ph -> B =/= 0 ) $.
    cxp111d.3 $e |- ( ph -> C =/= 0 ) $.
    $( General condition for complex exponentiation to be one-to-one with
       respect to the first argument.  (Contributed by SN, 25-Apr-2025.) $)
    cxp111d $p |- ( ph -> ( ( A ^c C ) = ( B ^c C ) <-> E. n e. ZZ
      ( log ` A ) = ( ( log ` B ) +
                        ( ( ( _i x. ( 2 x. _pi ) ) x. n ) / C ) ) ) ) $=
      ( co wceq cfv cmul caddc cz wcel cc adantr ccxp clog ce ci c2 cpi cv wrex
      cdiv cxpefd eqeq12d logcld mulcld ef11d wa cc0 wne ax-icn 2cn picn mulcli
      wb a1i adantl addcld div11 syl112anc divcan3d divdird oveq1d eqtrd bitr3d
      zcn rexbidva 3bitrd ) ABDUALZCDUALZMDBUBNZOLZUCNZDCUBNZOLZUCNZMVSWBUDUEUF
      OLZOLZEUGZOLZPLZMZEQUHVRWAWGDUILZPLZMZEQUHAVPVTVQWCABDFIHUJACDGJHUJUKAVSW
      BEADVRHABFIULZUMZADWAHACGJULZUMZUNAWIWLEQAWFQRZUOZVSDUILZWHDUILZMZWIWLWRV
      SSRZWHSRDSRZDUPUQZXAWIVBAXBWQWNTWRWBWGAWBSRWQWPTZWRWEWFWESRWRUDWDURUEUFUS
      UTVAVAVCWQWFSRAWFVMVDUMZVEAXCWQHTZAXDWQKTZVSWHDVFVGWRWSVRWTWKAWSVRMWQAVRD
      WMHKVHTWRWTWBDUILZWJPLWKWRWBWGDXEXFXGXHVIWRXIWAWJPAXIWAMWQAWADWOHKVHTVJVK
      UKVLVNVO $.
  $}

  ${
    $d ph n $.  $d A n $.  $d B n $.
    cxpi11d.a $e |- ( ph -> A e. CC ) $.
    cxpi11d.b $e |- ( ph -> B e. CC ) $.
    $( ` _i ` to the powers of ` A ` and ` B ` are equal iff ` A ` and ` B `
       are a multiple of 4 apart.  EDITORIAL:  This theorem may be revised to a
       more convenient form.  (Contributed by SN, 25-Apr-2025.) $)
    cxpi11d $p |- ( ph -> ( ( _i ^c A ) = ( _i ^c B ) <-> E. n e. ZZ
      A = ( B + ( 4 x. n ) ) ) ) $=
      ( ci co wceq c2 cpi cmul cdiv cc wcel ax-icn a1i cc0 wne wtru ccxp cv cfv
      clog caddc cz wrex c4 ine0 c1 ine1 cxp112d 2cn picn mulcli logcl logccne0
      mp2an mp3an div23d logi oveq2i 2ne0 divcli pine0 divne0i divcan5d divassi
      mptru 2cnd ddcand 2t2e4 3eqtri oveq1i eqtrdi oveq2d eqeq2d rexbiia bitrdi
      zcn ) AGBUAHGCUAHIBCGJKLHZLHZDUBZLHGUDUCZMHZUEHZIZDUFUGBCUHWCLHZUEHZIZDUF
      UGABCGDGNOZAPQEFGRSZAUIQGUJSZAUKQULWGWJDUFWCUFOZWFWIBWNWEWHCUEWNWEWBWDMHZ
      WCLHWHWNWBWCWDWBNOWNGWAPJKUMUNUOZUOQWCVTWDNOZWNWKWLWQPUIGUPURQWDRSZWNWKWL
      WMWRPUIUKGUQUSQUTWOUHWCLWOWBGKJMHZLHZMHZWAWSMHZUHWDWTWBMVAVBXAXBITWAWSGWA
      NOTWPQWSNOTKJUNUMVCVDZQWKTPQWSRSTKJUNUMVEVCVFZQWLTUIQVGVIXBJKWSMHZLHJJLHU
      HJKWSUMUNXCXDVHXEJJLXEJITKJKNOTUNQTVJKRSTVEQJRSTVCQVKVIVBVLVMVMVNVOVPVQVR
      VS $.
  $}

  ${
    logne0d.a $e |- ( ph -> A e. RR+ ) $.
    logne0d.1 $e |- ( ph -> A =/= 1 ) $.
    $( Deduction form of ~ logne0 .  See ~ logccne0d for a more general
       version.  (Contributed by SN, 25-Apr-2025.) $)
    logne0d $p |- ( ph -> ( log ` A ) =/= 0 ) $=
      ( crp wcel c1 wne clog cfv cc0 logne0 syl2anc ) ABEFBGHBIJKHCDBLM $.
  $}

  ${
    rxp112d.c $e |- ( ph -> C e. RR+ ) $.
    rxp112d.a $e |- ( ph -> A e. RR ) $.
    rxp112d.b $e |- ( ph -> B e. RR ) $.
    rxp112d.1 $e |- ( ph -> C =/= 1 ) $.
    rxp112d.2 $e |- ( ph -> ( C ^c A ) = ( C ^c B ) ) $.
    $( Real exponentiation is one-to-one with respect to the second argument.
       (TODO:  Note that the base ` C ` must be positive since ` -u C ^ A ` is
       ` C ^ A x. _e ^ _i _pi A ` , so in the negative case ` A = B + 2 k ` ).
       (Contributed by SN, 25-Apr-2025.) $)
    rxp112d $p |- ( ph -> A = B ) $=
      ( clog cfv recnd relogcld logne0d ccxp co cmul fveq2d logcxpd 3eqtr3d
      mulcan2ad ) ABCDJKZABFLACGLAUBADEMLADEHNADBOPZJKDCOPZJKBUBQPCUBQPAUCUDJIR
      ADBEFSADCEGSTUA $.
  $}

  ${
    log11d.a $e |- ( ph -> A e. CC ) $.
    log11d.b $e |- ( ph -> B e. CC ) $.
    log11d.1 $e |- ( ph -> A =/= 0 ) $.
    log11d.2 $e |- ( ph -> B =/= 0 ) $.
    $( The natural logarithm is one-to-one.  (Contributed by SN,
       25-Apr-2025.) $)
    log11d $p |- ( ph -> ( ( log ` A ) = ( log ` B ) <-> A = B ) ) $=
      ( clog cfv wceq ce fveq2 cc wcel cc0 wne eflog syl2anc eqeq12d imbitrid
      impbid1 ) ABHIZCHIZJZBCJZUDUBKIZUCKIZJAUEUBUCKLAUFBUGCABMNBOPUFBJDFBQRACM
      NCOPUGCJEGCQRSTBCHLUA $.
  $}

  ${
    rplog11d.a $e |- ( ph -> A e. RR+ ) $.
    rplog11d.b $e |- ( ph -> B e. RR+ ) $.
    $( The natural logarithm is one-to-one on positive reals.  (Contributed by
       SN, 25-Apr-2025.) $)
    rplog11d $p |- ( ph -> ( ( log ` A ) = ( log ` B ) <-> A = B ) ) $=
      ( rpcnd rpne0d log11d ) ABCABDFACEFABDGACEGH $.
  $}

  ${
    rxp11d.1 $e |- ( ph -> A e. RR+ ) $.
    rxp11d.2 $e |- ( ph -> B e. RR+ ) $.
    rxp11d.3 $e |- ( ph -> C e. RR ) $.
    rxp11d.4 $e |- ( ph -> C =/= 0 ) $.
    rxp11d.5 $e |- ( ph -> ( A ^c C ) = ( B ^c C ) ) $.
    $( Real exponentiation is one-to-one with respect to the first argument.
       (Contributed by SN, 25-Apr-2025.) $)
    rxp11d $p |- ( ph -> A = B ) $=
      ( clog cfv wceq relogcld recnd ccxp co cmul fveq2d logcxpd 3eqtr3d mpbid
      mulcanad rplog11d ) ABJKZCJKZLBCLAUDUEDAUDABEMNAUEACFMNADGNHABDOPZJKCDOPZ
      JKDUDQPDUEQPAUFUGJIRABDEGSACDFGSTUBABCEFUCUA $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Trigonometry and Calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    tanhalfpim.a $e |- ( ph -> A e. CC ) $.
    tanhalfpim.1 $e |- ( ph -> ( sin ` A ) =/= 0 ) $.
    $( The tangent of ` _pi / 2 ` minus a number is the cotangent, here
       represented by ` cos A / sin A ` .  (Contributed by SN, 2-Sep-2025.) $)
    tanhalfpim $p |- ( ph ->
      ( tan ` ( ( _pi / 2 ) - A ) ) = ( ( cos ` A ) / ( sin ` A ) ) ) $=
      ( cpi c2 cdiv co cmin ctan cfv csin ccos cc wcel cc0 wne wceq picn syl
      2cn 2ne0 divcli subcld coshalfpim eqnetrd tanval syl2anc sinhalfpim eqtrd
      a1i oveq12d ) AEFGHZBIHZJKZUNLKZUNMKZGHZBMKZBLKZGHZAUNNOUQPQUOURRAUMBUMNO
      AEFSUAUBUCUKCUDAUQUTPABNOZUQUTRCBUEZTDUFUNUGUHAVBURVARCVBUPUSUQUTGBUIVCUL
      TUJ $.
  $}

  $( Sine of a number subtracted from ` _pi ` .  (Contributed by SN,
     19-Nov-2025.) $)
  sinpim $p |- ( A e. CC -> ( sin ` ( _pi - A ) ) = ( sin ` A ) ) $=
    ( cc wcel cpi cmin cneg csin cfv wceq picn a1i subcld sinneg syl negsubdi2d
    co id fveq2d sincl sinmpi eqcomd negcon1ad 3eqtr3d ) ABCZADEPZFZGHZUEGHZFZD
    AEPZGHAGHZUDUEBCUGUIIUDADUDQZDBCUDJKZLUEMNUDUFUJGUDADULUMORUDUKUHASUDUHUKFA
    TUAUBUC $.

  $( Cosine of a number subtracted from ` _pi ` .  (Contributed by SN,
     19-Nov-2025.) $)
  cospim $p |- ( A e. CC -> ( cos ` ( _pi - A ) ) = -u ( cos ` A ) ) $=
    ( cc wcel cpi cmin cneg ccos cfv wceq picn a1i subcld cosneg syl negsubdi2d
    co id fveq2d cosmpi 3eqtr3d ) ABCZADEPZFZGHZUBGHZDAEPZGHAGHFUAUBBCUDUEIUAAD
    UAQZDBCUAJKZLUBMNUAUCUFGUAADUGUHORAST $.

  $( The tangent of ` _pi / 3 ` is ` sqrt 3 ` .  (Contributed by SN,
     2-Sep-2025.) $)
  tan3rdpi $p |- ( tan ` ( _pi / 3 ) ) = ( sqrt ` 3 ) $=
    ( cpi c3 cdiv co ctan cfv csin ccos csqrt c2 c1 cc wcel cc0 wne sincos3rdpi
    wceq 3cn wtru a1i picn 3ne0 divcli simpri 0re halfgt0 gtneii eqnetri tanval
    mp2an simpli oveq12i sqrtcld 1cnd ax-1ne0 divcan7d div1d eqtrd mptru 3eqtri
    2cnd 2ne0 ) ABCDZEFZVCGFZVCHFZCDZBIFZJCDZKJCDZCDZVHVCLMVFNOVDVGQABUARUBUCVF
    VJNVEVIQZVFVJQZPUDZNVJUEUFUGUHVCUIUJVEVIVFVJCVLVMPUKVNULVKVHQSVKVHKCDVHSVHK
    JSBBLMSRTUMZSUNSVAKNOSUOTJNOSVBTUPSVHVOUQURUSUT $.

  $( The sine of ` 2 x. ( _pi / 3 ) ` is ` ( sqrt 3 ) / 2 ` .  (Contributed by
     SN, 19-Nov-2025.) $)
  sin2t3rdpi $p |- ( sin ` ( 2 x. ( _pi / 3 ) ) ) = ( ( sqrt ` 3 ) / 2 ) $=
    ( c2 cpi c3 cdiv co cmul csin cfv cmin csqrt c1 3cn ax-1cn picn 3ne0 divcli
    subdiri 3m1e2 oveq1i wceq divcan2i mullidi oveq12i 3eqtr3i fveq2i cc sinpim
    wcel ax-mp ccos sincos3rdpi simpli 3eqtri ) ABCDEZFEZGHBUNIEZGHZUNGHZCJHADE
    ZUOUPGCKIEZUNFECUNFEZKUNFEZIEUOUPCKUNLMBCNLOPZQUTAUNFRSVABVBUNIBCNLOUAUNVCU
    BUCUDUEUNUFUHUQURTVCUNUGUIURUSTUNUJHKADETUKULUM $.

  $( The cosine of ` 2 x. ( _pi / 3 ) ` is ` -u 1 / 2 ` .  (Contributed by SN,
     19-Nov-2025.) $)
  cos2t3rdpi $p |- ( cos ` ( 2 x. ( _pi / 3 ) ) ) = -u ( 1 / 2 ) $=
    ( c2 cpi c3 cdiv co cmul ccos cfv cmin cneg c1 3cn ax-1cn picn 3ne0 subdiri
    divcli 3m1e2 oveq1i wceq divcan2i mullidi oveq12i 3eqtr3i fveq2i wcel ax-mp
    cc cospim csin csqrt sincos3rdpi simpri negeqi 3eqtri ) ABCDEZFEZGHBUPIEZGH
    ZUPGHZJZKADEZJUQURGCKIEZUPFECUPFEZKUPFEZIEUQURCKUPLMBCNLOQZPVCAUPFRSVDBVEUP
    IBCNLOUAUPVFUBUCUDUEUPUHUFUSVATVFUPUIUGUTVBUPUJHCUKHADETUTVBTULUMUNUO $.

  $( The sine of ` 4 x. ( _pi / 3 ) ` is ` -u ( sqrt 3 ) / 2 ` .  (Contributed
     by SN, 19-Nov-2025.) $)
  sin4t3rdpi $p |- ( sin ` ( 4 x. ( _pi / 3 ) ) ) = -u ( ( sqrt ` 3 ) / 2 ) $=
    ( cpi c3 cdiv co caddc csin cfv cneg c4 cmul csqrt c2 cc wcel wceq picn 3cn
    3ne0 divcli ax-mp sinppi 3rdpwhole fveq2i ccos c1 sincos3rdpi simpli negeqi
    3eqtr3i ) ABCDZAEDZFGZUJFGZHZIUJJDZFGBKGLCDZHUJMNULUNOABPQRSUJUATUKUOFAMNUK
    UOOPAUBTUCUMUPUMUPOUJUDGUELCDOUFUGUHUI $.

  $( The cosine of ` 4 x. ( _pi / 3 ) ` is ` -u 1 / 2 ` .  (Contributed by SN,
     19-Nov-2025.) $)
  cos4t3rdpi $p |- ( cos ` ( 4 x. ( _pi / 3 ) ) ) = -u ( 1 / 2 ) $=
    ( cpi c3 cdiv co caddc ccos cfv cneg c4 cmul c1 c2 cc wcel wceq picn divcli
    3cn 3ne0 ax-mp cosppi 3rdpwhole fveq2i csin csqrt sincos3rdpi simpri negeqi
    3eqtr3i ) ABCDZAEDZFGZUJFGZHZIUJJDZFGKLCDZHUJMNULUNOABPRSQUJUATUKUOFAMNUKUO
    OPAUBTUCUMUPUJUDGBUEGLCDOUMUPOUFUGUHUI $.

  $( The arcsine of ` 1 / 2 ` is ` _pi / 6 ` .  (Contributed by SN,
     31-Aug-2025.) $)
  asin1half $p |- ( arcsin ` ( 1 / 2 ) ) = ( _pi / 6 ) $=
    ( cpi c6 cdiv co cfv casin c2 wceq wcel cr cle wbr pire cc0 neghalfpire clt
    halfpire wtru crp a1i csin c1 ccos csqrt sincos6thpi simpli fveq2i cneg 6re
    c3 cicc 0re 6pos gtneii redivcli 2re pipos 2pos divgt0ii mpbii ax-mp lttrii
    lt0neg2 ltleii 2lt6 2rp 6rp ltdiv2d mptru elicc2i mpbir3an reasinsin eqtr3i
    pirp ) ABCDZUAEZFEZUBGCDZFEVOVPVRFVPVRHVOUCEUJUDEGCDHUEUFUGVOAGCDZUHZVSUKDI
    ZVQVOHWAVOJIVTVOKLVOVSKLABMUINBULUMUNUOZVTVOOWBVTNVOOULWBVSJIZVTNPLZQWCNVSP
    LWDAGMUPUQURUSVSVCUTVAABMUIUQUMUSVBVDVOVSWBQVOVSPLZRGBPLWEVERGBAGSIRVFTBSIR
    VGTASIRVNTVHUTVIVDVTVSVOOQVJVKVOVLVAVM $.

  $( The arccosine of ` 1 / 2 ` is ` _pi / 3 ` .  (Contributed by SN,
     31-Aug-2024.) $)
  acos1half $p |- ( arccos ` ( 1 / 2 ) ) = ( _pi / 3 ) $=
    ( cpi c3 cdiv co cfv cacos c1 c2 wceq wcel cc0 pire 3re cxr clt rexri pipos
    wbr 3pos mp2an ccos csin csqrt sincos3rdpi simpri fveq2i cioo 3ne0 redivcli
    cc recni cr rere ax-mp divgt0ii picn gt0ne0ii dividi 1lt3 eqbrtri ltdiv23ii
    cre mpbir w3a wb 0xr elioo1 mpbir3an eqeltri acoscos eqtr3i ) ABCDZUAEZFEZG
    HCDZFEVLVMVOFVLUBEBUCEHCDIVMVOIUDUEUFVLUJJVLVBEZKAUGDZJVNVLIVLABLMUHUIZUKVP
    VLVQVLULJVPVLIVRVLUMUNVLVQJZVLNJZKVLORZVLAORZVLVRPABLMQSUOWBAACDZBORWCGBOAU
    PALQUQURUSUTABALMLSQVAVCKNJANJVSVTWAWBVDVEVFALPKAVLVGTVHVIVLVJTVK $.

  ${
    dvun.j $e |- J = ( K |`t S ) $.
    dvun.k $e |- K = ( TopOpen ` CCfld ) $.
    dvun.s $e |- ( ph -> S C_ CC ) $.
    dvun.f $e |- ( ph -> F : A --> CC ) $.
    dvun.g $e |- ( ph -> G : B --> CC ) $.
    dvun.a $e |- ( ph -> A C_ S ) $.
    dvun.b $e |- ( ph -> B C_ S ) $.
    dvun.d $e |- ( ph -> ( A i^i B ) = (/) ) $.
    dvun.n $e |- ( ph -> ( ( ( int ` J ) ` A ) u. ( ( int ` J ) ` B ) )
                         = ( ( int ` J ) ` ( A u. B ) ) ) $.
    $( Condition for the union of the derivatives of two disjoint functions to
       be equal to the derivative of the union of the two functions.  If ` A `
       and ` B ` are open sets, this condition (dvun.n) is satisfied by
       ~ isopn3i .  (Contributed by SN, 30-Sep-2025.) $)
    dvun $p |- ( ph -> ( ( S _D F ) u. ( S _D G ) ) = ( S _D ( F u. G ) ) ) $=
      ( cdv cres wceq cun co cnt cfv resundi reseq2d eqtr3id cc wss fun2d unssd
      wf dvres syl22anc wfn cin c0 ffnd fnunres1 syl3anc oveq2d eqtr3d fnunres2
      uneq12d fnresdm syl 3eqtr3d ) ADEFUAZRUBZBGUCUDZUDZSZVICVJUDZSZUAZVIBCUAZ
      VJUDZSZDERUBZDFRUBZUAVIAVOVIVKVMUAZSVRVIVKVMUEAWAVQVIQUFUGAVLVSVNVTADVHBS
      ZRUBZVLVSADUHUIZVPUHVHULZVPDUIZBDUIWCVLTKABCUHEFLMPUJZABCDNOUKZNVPBDGVHHJ
      IUMUNAWBEDRAEBUOZFCUOZBCUPUQTZWBETABUHELURZACUHFMURZPBCEFUSUTVAVBADVHCSZR
      UBZVNVTAWDWEWFCDUIWOVNTKWGWHOVPCDGVHHJIUMUNAWNFDRAWIWJWKWNFTWLWMPBCEFVCUT
      VAVBVDADVHVPSZRUBZVRVIAWDWEWFWFWQVRTKWGWHWHVPVPDGVHHJIUMUNAWPVHDRAVHVPUOW
      PVHTAVPUHVHWGURVPVHVEVFVAVBVG $.
  $}

  $( A good example of ~ dvmptco is ~ dvsinexp . $)

  ${
    $d x y $.  $d D x $.
    redvabs.d $e |- D = ( RR \ { 0 } ) $.
    $( The derivative of the absolute value, for real numbers.  (Contributed by
       SN, 30-Sep-2025.) $)
    redvmptabs $p |- ( RR _D ( x e. D |-> ( abs ` x ) ) ) =
                             ( x e. D |-> if ( x < 0 , -u 1 , 1 ) ) $=
      ( cr cc0 clt cmpt cun cdv co wcel c1 cfv wceq wtru cc a1i wa wss wn vy cv
      wbr cab cin cneg cdif cif cabs partfun cpr reelprrecn inss1 difss eqsstri
      csn ax-resscn sstri sseli adantl 1cnd crn ctg ccnfld ctopn sselda dvmptid
      cioo 1red ssinss1 mp1i tgioo4 eqid cmnf wne eleq2i eldifsn bitri vex elab
      breq1 anbi12i lt0ne0 expcom pm4.71d bicomd pm5.32ri elin cxr 0xr elioomnf
      wb ax-mp 3bitr4i eqriv iooretop eqeltri dvmptres dvmptneg ssdifssd notbii
      mptru cpnf anass wo elre0re id lttrid ioran bicomi bianbi bitr2di pm5.32i
      nesym 3bitri eldif repos uneq12i negcld fmpttd ssdifss inindif ctop retop
      c0 cnt isopn3i mp2an unopn mp3an eqtr4i dvun 3eqtr2ri elioore 0red eqcomd
      simprbi eleq2s sylbir crp absnidd rpabsid ifeqda mpteq2ia eqtr3i ifbieq2i
      ltled ioorp oveq2i mpteq2i 3eqtr3i ) DABUAUBZEFUCZUAUDZUEZAUBZUFZGZABUUNU
      GZUUPGZHZIJZABUUPUUNKZLUFZLUHZGZDABUUPUIMZGZIJABUUPEFUCZUVDLUHZGUVFAUUOUV
      DGZAUUSLGZHDUURIJZDUUTIJZHZUVBABUUNUVDLUJUVMUVKUVNUVLUVMUVKNOAUUPLDPUUODD
      PUKKOULQZUUPUUOKZUUPPKOUUOPUUPUUOBPBUUNUMBDPBDEUPZUGZDCDUVRUNUOZUQURURUSU
      TZOUVQRZVAOAUUPLDVHVBVCMZVDVEMZDDUUOUVPODPUUPDPSOUQQZVFZOUUPDKZRVIZOADUVP
      VGZBDSZUUODSOUVTBUUNDVJVKZVLUWDVMZUUOUWCKZOUUOVNEVHJZUWCAUUOUWNUUPBKZUVCR
      ZUWGUVIRZUVQUUPUWNKZUWPUWGUUPEVOZRZUVIRUWQUWOUWTUVCUVIUWOUUPUVSKUWTBUVSUU
      PCVPUUPDEVQVRZUUMUVIUAUUPAVSUULUUPEFWAVTZWBUVIUWTUWGUVIUWGUWTUVIUWGUWSUWG
      UVIUWSUUPWCWDWEWFWGVRUUPBUUNWHZEWIKUWRUWQWLWJEUUPWKWMZWNWOZVNEWPWQZQWRWSX
      BUVNUVLNOAUUPLDUWCUWDDDUUSUVPUWFUWHUWIOBDUUNUWJOUVTQWTZVLUWLUUSUWCKZOUUSE
      XCVHJZUWCAUUSUXIUWOUVCTZRZUWGEUUPFUCZRZUUPUUSKZUUPUXIKUXKUWTUVITZRUWGUWSU
      XORZRUXMUWOUWTUXJUXOUXAUVCUVIUXBXAWBUWGUWSUXOXDUWGUXPUXLUWGUXLEUUPNZUVIXE
      TZUXPUWGEUUPUUPXFUWGXGXHUXRUXQTZUXOUWSUXQUVIXIUWSUXSUUPEXNXJXKXLXMXOUUPBU
      UNXPZUUPXQWNWOZEXCWPWQZQWRXBXRUVOUVBNOUUOUUSDUURUUTUWCUWDVLUWLUWEOAUUOUUQ
      PUWBUUPUWAXSXTOAUUSUUPPOUUSPUUPUUSPSOUUSDPUWJUUSDSUVTBDUUNYAWMUQURQVFXTUW
      KUXGUUOUUSUEYENOBUUNYBQUUOUWCYFMZMZUUSUYCMZHZUUOUUSHZUYCMZNOUYFUYGUYHUYDU
      UOUYEUUSUWCYCKZUWMUYDUUONYDUXFUUOUWCYGYHUYIUXHUYEUUSNYDUYBUUSUWCYGYHXRUYI
      UYGUWCKZUYHUYGNYDUYIUWMUXHUYJYDUXFUYBUUOUUSUWCYIYJUYGUWCYGYHYKQYLXBYMUVAU
      VHDIABUVCUUQUUPUHZGUVAUVHABUUNUUQUUPUJABUYKUVGUWOUVCUUQUUPUVGUWPUVQUUQUVG
      NZUXCUYLUUPUWNUUOUWRUVGUUQUWRUUPUUPVNEYNZUWRUUPEUYMUWRYOUWRUWGUVIUXDYQUUG
      UUAYPUXEYRYSUXKUXNUUPUVGNZUXTUYNUUPUXIUUSUYNUUPYTUXIUUPYTKUVGUUPUUPUUBYPU
      UHYRUYAYRYSUUCUUDUUEUUIABUVEUVJUVCUVILLUVDUXBLVMUUFUUJUUK $.

    $( The antiderivative of 1/x in real numbers, without using the absolute
       value function.  (Contributed by SN, 1-Oct-2025.) $)
    readvrec2 $p |- ( RR _D ( x e. D |-> ( ( log ` ( x ^ 2 ) ) / 2 ) ) ) =
                            ( x e. D |-> ( 1 / x ) ) $=
      ( vy cr c2 co clog cdiv cmpt cdv c1 cmul wceq wtru cc wcel a1i cc0 crp cv
      cexp cfv cvv cpr reelprrecn wne csn wa eleq2i eldifsn bitri simplbi recnd
      cdif sqcld simprbi wb sqne0 syl mpbird logcld adantl cmnf cioc cnelprrecn
      ovexd cin c0 cpnf cioo incom dfrp2 ineq2i cxr mnfxr 0xr pnfxr iocioodisjd
      mptru 3eqtri disjdif2 ax-mp wss rpsscn ssdif sqn0rp syl2an2 sselid eldifi
      eqsstrri wn eldifn clt wbr mnflt0 0le0 elioc1 mp2an mpbir3an eleq1 mpbiri
      cle w3a necon3bi cmin crn ctg ccnfld ctopn recn eqid cnopn ax-resscn mpbi
      dfss2 sqcl 2nn dvexp mp1i dvmptres3 ssriv tgioo4 ccld cha rehaus uniretop
      cn sncld cldopn eqeltri dvmptres 2m1e1 oveq2i oveq2d mpteq2ia 2cnd oveq1d
      0re 2ne0 exp1d eqtrid eqtrdi cres wf1o logf1o snssi sscon feqresmpt dvlog
      f1of eqtr3di fveq2 oveq2 dvmptco dvmptdivc resqcld rereccld mul12d mulcld
      wf divcan3d sqvald recdiv2d reccld divcan1d 3eqtr2d 3eqtrd eqtri ) EABAUA
      ZFUBGZHUCZFIGJKGZABLUVKIGZFUVJMGZMGZFIGZJZABLUVJIGZJUVMUVRNOAUVLUVPFEUDBE
      EPUEZQOUFRZUVJBQZUVLPQOUWBUVKUWBUVJUWBUVJUWBUVJEQZUVJSUGZUWBUVJESUHZUOZQU
      WCUWDUIBUWFUVJCUJUVJESUKULZUMZUNZUPUWBUVKSUGZUWDUWBUWCUWDUWGUQZUWBUVJPQZU
      WJUWDURUWIUVJUSUTVAZVBVCOUWBUIZUVNUVOMVGOADUVKUVODUAZHUCZLUWOIGZEPUVLUVNU
      DUDBPVDSVEGZUOZUWAPUVTQOVFRUWNTUWSUVKTTUWRUOZUWSTUWRVHZVINUWTTNUXAUWRTVHU
      WRSVJVKGZVHZVITUWRVLTUXBUWRVMVNUXCVINOVDSVJVDVOQZOVPRSVOQZOVQRVJVOQOVRRVS
      VTWATUWRWBWCTPWDUWTUWSWDWETPUWRWFWCWKUWBUWCOUWDUVKTQUWHUWBUWDOUWKVCUVJWGW
      HWIUWNFUVJMVGUWOUWSQZUWPPQOUXFUWOUWOPUWRWJUXFUWOUWRQZWLUWOSUGUWOPUWRWMUXG
      UWOSUWOSNUXGSUWRQZUXHUXEVDSWNWOZSSXCWOZVQWPWQUXDUXEUXHUXEUXIUXJXDURVPVQVD
      SSWRWSWTZUWOSUWRXAXBXEUTVBVCOUXFUILUWOIVGOEABUVKJKGABFUVJFLXFGZUBGZMGZJAB
      UVOJOAUVKUXNEVKXGXHUCZXIXJUCZUDEBUWAOUWCUIZUVJUWCUWLOUVJXKVCUPUXQFUXMMVGO
      AUVKUXNEUXPUDPEUXPXLZUWAPUXPQOXMREPVHENZOEPWDUXSXNEPXPXORUWLUVKPQOUVJXQVC
      OUWLUIFUXMMVGFYHQPAPUVKJKGAPUXNJNOXRAFXSXTYABEWDOABEUWHYBRYCUXRBUXOQOBUWF
      UXOCUWEUXOYDUCQZUWFUXOQUXOYEQSEQUXTYFYSSUXOEYGYIWSUWEUXOEYGYJWCYKRYLABUXN
      UVOUWBUXMUVJFMUWBUXMUVJLUBGUVJUXLLUVJUBYMYNUWBUVJUWIUUAUUBYOYPUUCOPHUWSUU
      DZKGPDUWSUWPJZKGDUWSUWQJOUYAUYBPKODPUWEUOZHXGZUWSHUYCUYDHUUEUYCUYDHUVAOUU
      FUYCUYDHUUKXTUWEUWRWDZUWSUYCWDOUXHUYEUXKSUWRUUGWCUWEUWRPUUHXTUUIYODUWSUWS
      XLUUJUULUWOUVKHUUMUWOUVKLIUUNUUOOYQFSUGZOYTRUUPVTABUVQUVSUWBUVQFUVNUVJMGZ
      MGZFIGUYGUVSUWBUVPUYHFIUWBUVNFUVJUWBUVNUWBUVKUWBUVJUWHUUQUWMUURUNZUWBYQZU
      WIUUSYRUWBUYGFUWBUVNUVJUYIUWIUUTUYJUYFUWBYTRUVBUWBUYGLUVJUVJMGZIGZUVJMGUV
      SUVJIGZUVJMGUVSUWBUVNUYLUVJMUWBUVKUYKLIUWBUVJUWIUVCYOYRUWBUYMUYLUVJMUWBUV
      JUVJUWIUWIUWKUWKUVDYRUWBUVSUVJUWBUVJUWIUWKUVEUWIUWKUVFUVGUVHYPUVI $.

    $( For real numbers, the antiderivative of 1/x is ln|x|.  (Contributed by
       SN, 30-Sep-2025.) $)
    readvrec $p |- ( RR _D ( x e. D |-> ( log ` ( abs ` x ) ) ) ) =
                            ( x e. D |-> ( 1 / x ) ) $=
      ( vy cr clog cmpt cdv co c1 cdiv cc0 cmul wceq wtru cc cmnf wcel a1i wa
      cv cabs cfv clt wbr cneg cif cvv cioc cdif cpr reelprrecn cnelprrecn cpnf
      crp cioo dfrp2 cin c0 cxr mnfxr pnfxr iocioodisjd mptru ineqcomi disjdif2
      0xr ax-mp eqtr4i wss ioosscn ssdif eqsstri wne csn eleq2i eldifsn simplbi
      bitri recnd adantl simprbi absrpcld sselid negex 1ex eldifi eldifn mnflt0
      ifex wn ubioc1 mp3an eleq1 mpbiri necon3bi syl logcld redvmptabs cres crn
      ovexd wf1o wf logf1o f1of mp1i eqid logdmss feqresmpt oveq2i dvlog eqtr3i
      fveq2 oveq2 dvmptco ovif2 simpll abscld simplr absne0d reccld neg1cn 1cnd
      mulcomd mulm1d divneg2d simpr ltled absnidd eqcomd negcon1ad oveq2d eqtrd
      0red 3eqtrd sylanb recn ad2antrr rereccld mulridd cle simpl lenltd absidd
      biimpar ifeqda eqtrid mpteq2ia eqtri ) EABAUAZUBUCZFUCZGHIZABJUULKIZUUKLU
      DUEZJUFZJUGZMIZGZABJUUKKIZGUUNUUTNOADUULUURDUAZFUCZJUVBKIZEPUUMUUOUHUHBPQ
      LUIIZUJZEEPUKZROULSPUVGROUMSOUUKBRZTZUOUVFUULUOLUNUPIZUVEUJZUVFUOUVJUVKUQ
      UVJUVEURUSNUVKUVJNUVEUVJUSUVEUVJURUSNOQLUNQUTRZOVASLUTRZOVGSUNUTROVBSVCVD
      VEUVJUVEVFVHVIUVJPVJUVKUVFVJLUNVKUVJPUVEVLVHVMUVIUUKUVHUUKPRZOUVHUUKUVHUU
      KERZUUKLVNZUVHUUKELVOZUJZRUVOUVPTZBUVRUUKCVPUUKELVQVSZVRVTWAUVHUVPOUVHUVO
      UVPUVTWBWAWCWDUURUHRUVIUUPUUQJJWEWFWJSOUVBUVFRZTZUVBUWAUVBPROUVBPUVEWGWAU
      WAUVBLVNZOUWAUVBUVERZWKUWCUVBPUVEWHUWDUVBLUVBLNUWDLUVERZUVLUVMQLUDUEUWEVA
      VGWIQLWLWMUVBLUVEWNWOWPWQWAWRUWBJUVBKXBEABUULGHIABUURGNOABCWSSPDUVFUVCGZH
      IZDUVFUVDGZNOPFUVFWTZHIUWGUWHUWIUWFPHUWIUWFNODPUVQUJZFXAZUVFFUWJUWKFXCUWJ
      UWKFXDOXEUWJUWKFXFXGUVFUWJVJOUVFUVFXHZXISXJVDXKDUVFUWLXLXMSUVBUULFXNUVBUU
      LJKXOXPVDABUUSUVAUVHUUSUUPUUOUUQMIZUUOJMIZUGUVAUUPUUOUUQJMXQUVHUUPUWMUWNU
      VAUVHUVSUUPUWMUVANUVTUVSUUPTZUWMUUQUUOMIUUOUFZUVAUWOUUOUUQUWOUULUWOUULUWO
      UUKUWOUUKUVOUVPUUPXRZVTZXSVTZUWOUUKUWRUVOUVPUUPXTYAZYBZUUQPRUWOYCSYEUWOUU
      OUXAYFUWOUWPJUULUFZKIUVAUWOJUULUWOYDUWSUWTYGUWOUXBUUKJKUWOUUKUULUWRUWOUUL
      UUKUFUWOUUKUWQUWOUUKLUWQUWOYOUVSUUPYHYIYJYKYLYMYNYPYQUVHUVSUUPWKZUWNUVANU
      VTUVSUXCTZUWNUUOUVAUXDUUOUXDUUOUXDUULUVOUULERUVPUXCUVOUUKUUKYRZXSYSUXDUUK
      UVOUVNUVPUXCUXEYSUVOUVPUXCXTYAYTVTUUAUXDUULUUKJKUXDUUKUVOUVPUXCXRUVSLUUKU
      UBUEUXCUVSLUUKUVSYOUVOUVPUUCUUDUUFUUEYMYNYQUUGUUHUUIUUJ $.
  $}

  ${
    readvcot.d $e |- D = { y e. RR | ( sin ` y ) =/= 0 } $.
    $( The support of sin ( ~ df-supp ) restricted to the reals is an open set.
       (Contributed by SN, 7-Oct-2025.) $)
    resuppsinopn $p |- D e. ( topGen ` ran (,) ) $=
      ( csin cr cres ccnv cc cc0 csn cdif cfv co wcel ax-resscn mp2an crab wtru
      ccn a1i cima ccnfld ctopn crest cioo crn ctg wss ccncf sincn eqid cncfcn1
      eleqtri unicntop cnrest cnn0opn cnima cv wa resincl recnd adantr eldifsnd
      wne eldifsni adantl impbida rabbiia cmpt wceq wf sinf feqresmpt mptpreima
      simpr mptru 3eqtr4i tgioo4 3eltr4i ) DEFZGHIJKZUAZUBUCLZEUDMZBUEUFUGLVTWD
      WCSMNZWAWCNWBWDNDWCWCSMZNEHUHZWEDHHUIMWFUJWCWCUKULUMOEDWCWCHUNUOPUPWAVTWD
      WCUQPAURZDLZIVDZAEQWIWANZAEQBWBWJWKAEWHENZWJWKWLWJUSWIHIWLWIHNWJWLWIWHUTV
      AVBWLWJVOVCWKWJWLWIHIVEVFVGVHCAEWIWAVTVTAEWIVIVJRAHHEDHHDVKRVLTWGROTVMVPV
      NVQVRVS $.

    $d D x $.  $d x y $.  $d x z $.
    $( Real antiderivative of cotangent.  (Contributed by SN, 7-Oct-2025.) $)
    readvcot $p |- ( RR _D ( x e. D |-> ( log ` ( abs ` ( sin ` x ) ) ) ) )
                         = ( x e. D |-> ( ( cos ` x ) / ( sin ` x ) ) ) $=
      ( vz cr csin cfv cmpt cdv co cdiv ccos wtru cc0 cc wcel a1i wa adantl cvv
      cv cabs clog c1 cmul wceq csn cdif cpr reelprrecn wne fveq2 neeq1d elrab2
      weq resincl adantr simpr eldifsnd sylbi fvexd eldifi recnd abscld absne0d
      eldifsni logcld ovexd cioo crn ctg ccnfld ctopn cnopn cin ax-resscn dfss2
      eqid wss mpbi sincl dvsin wf sinf feqmptd oveq2d 3eqtr3a dvmptres3 ssrab3
      tgioo4 resuppsinopn dvmptres readvrec 2fveq3 oveq2 dvmptco mptru recoscld
      cosf simplbi divrec2d mpteq2ia eqtr4i ) FACAUBZGHZUCHUDHZIJKZACUEXFLKZXEM
      HZUFKZIZACXJXFLKZIXHXLUGNAEXFXJEUBZUCHZUDHZUEXNLKZFFXGXIUAUACFOUHZUIZFFPU
      JQNUKRZXTXECQZXFXSQZNYAXEFQZXFOULZSZYBBUBZGHZOULZYDBXEFCBAUPYGXFOYFXEGUMU
      NDUOZYEXFFOYCXFFQZYDXEUQZURZYCYDUSZUTVATNYASXEMVBNXNXSQZSZXOYOXOYOXNYOXNY
      NXNFQNXNFXRVCTVDZVEVDYOXNYPYNXNOULNXNFOVGTVFVHYOUEXNLVINAXFXJFVJVKVLHZVMV
      NHZUAFCXTYCXFPQZNYCXFYKVDTNYCSXEMVBNAXFXJFYRUAPFYRVSZXTPYRQNVORFPVPFUGZNF
      PVTUUAVQFPVRWARXEPQZYSNXEWBTNUUBSXEMVBNPGJKMPAPXFIZJKAPXJIWCNGUUCPJNAPPGP
      PGWDNWERWFWGNAPPMPPMWDNWTRWFWHWICFVTNYHBFCDWJRWKYTCYQQNBCDWLRWMFEXSXPIJKE
      XSXQIUGNEXSXSVSWNRXNXFUDUCWOXNXFUELWPWQWRACXMXKYAXJXFYAXJYAXEYAYCYDYIXAWS
      VDYAXFYAYEYJYIYLVAVDYAYEYDYIYMVAXBXCXD $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Independence of ax-mulcom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section mainly concerns the independence of ~ ax-mulcom , which is the
  only real and complex number axiom whose independence is open (
  ~ https://us.metamath.org/mpeuni/mmcomplex.html ).  In particular, this is a
  combination of attempts to prove more and more properties of real and complex
  numbers without ~ ax-mulcom .  Completing this direction would show that
  ~ ax-mulcom is not independent.

  Alternatively, one could search for a model satisfying all axioms except
  ~ ax-mulcom , thus showing it is independent.  A few models satisfying
  non-commutativity which only violate one other axiom are provided at
  ~ https://gist.github.com/icecream17/933f95d820e0b8f1cab0d4293b68eaf9 .  I
  conjecture that if it is possible to prove ~ ax-mulcom from the other axioms,
  then all the other axioms are needed.

  In abstract terms, the symbol ` RR ` would have to correspond to an infinite
  non-commutative left-near-field with a Dedekind-complete order compatible
  with its ring operations.

  (Note: ~ https://en.wikipedia.org/wiki/Near-field_(mathematics) does not
  require commutativity despite having "field" in the name.)

  Needless to say, this is a very undeveloped area of math.  In addition, such
  a structure for ` RR ` would have to, together with the structure for the
  symbol ` CC ` , satisfy ~ ax-resscn , ~ ax-icn , ~ ax-i2m1 , and most
  crucially ~ ax-cnre .

  None of the theorems in this section should be moved to main.  If there is a
  naming conflict, feel free to add the prefix "sn-".

$)

  $c -R $.

  $( Real number subtraction. $)
  cresub $a class -R $.

  ${
    $d x y z $.
    $( Define subtraction between real numbers.  This operator saves a few
       axioms over ~ df-sub in certain situations.  Theorem ~ resubval shows
       its value, ~ resubadd relates it to addition, and ~ rersubcl proves its
       closure.  It is the restriction of ~ df-sub to the reals: ~ subresre .
       (Contributed by Steven Nguyen, 7-Jan-2023.) $)
    df-resub $a |- -R = ( x e. RR , y e. RR |->
                       ( iota_ z e. RR ( y + z ) = x ) ) $.
  $}

  ${
    $d x y z A $.  $d x y z B $.
    $( Value of real subtraction, which is the (unique) real ` x ` such that
       ` B + x = A ` .  (Contributed by Steven Nguyen, 7-Jan-2023.) $)
    resubval $p |- ( ( A e. RR /\ B e. RR ) ->
                   ( A -R B ) = ( iota_ x e. RR ( B + x ) = A ) ) $=
      ( vy vz cr cv caddc wceq crio cresub eqeq2 riotabidv oveq1 eqeq1d riotaex
      co df-resub ovmpo ) DEBCFFEGZAGZHQZDGZIZAFJCUAHQZBIZAFJKUBBIZAFJUCBIUDUGA
      FUCBUBLMTCIZUGUFAFUHUBUEBTCUAHNOMDEARUFAFPS $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d ph x y $.
    renegeulemv.b $e |- ( ph -> B e. RR ) $.
    renegeulemv.1 $e |- ( ph -> E. y e. RR ( B + y ) = A ) $.
    $( Lemma for ~ renegeu and similar.  Derive existential uniqueness from
       existence.  (Contributed by Steven Nguyen, 28-Jan-2023.) $)
    renegeulemv $p |- ( ph -> E! x e. RR ( B + x ) = A ) $=
      ( cv caddc co wceq cr wreu wcel wa weq wb wral simprl simplrr simpr bitrd
      eqcomd eqeq2d simplrl ad2antrr readdcan syl3anc ralrimiva reu6i rexlimddv
      syl2anc ) AECHZIJZDKZEBHZIJZDKZBLMZCLGAUMLNZUOOZOZUTURBCPZQZBLRUSAUTUOSVB
      VDBLVBUPLNZOZURUQUNKZVCVFDUNUQVFUNDAUTUOVETUCUDVFVEUTELNZVGVCQVBVEUAAUTUO
      VEUEAVHVAVEFUFUPUMEUGUHUBUIURBLUMUJULUK $.

    $( Lemma for ~ renegeu and similar.  Remove a change in bound variables
       from ~ renegeulemv .  (Contributed by Steven Nguyen, 28-Jan-2023.) $)
    renegeulem $p |- ( ph -> E! y e. RR ( B + y ) = A ) $=
      ( vx cv caddc co wceq cr wreu wrex renegeulemv reurex syl ) ABGCDEADGHIJC
      KZGLMRGLNAGBCDEFORGLPQO $.
  $}

  ${
    $d A x $.
    $( Existential uniqueness of real negatives.  (Contributed by Steven
       Nguyen, 7-Jan-2023.) $)
    renegeu $p |- ( A e. RR -> E! x e. RR ( A + x ) = 0 ) $=
      ( cr wcel cc0 id ax-rnegex renegeulem ) BCDZAEBIFABGH $.

    $( Closure law for negative reals.  (Contributed by Steven Nguyen,
       7-Jan-2023.) $)
    rernegcl $p |- ( A e. RR -> ( 0 -R A ) e. RR ) $=
      ( vx cr wcel cc0 cresub co cv caddc wceq elre0re resubval mpancom renegeu
      crio wreu riotacl syl eqeltrd ) ACDZEAFGZABHIGEJZBCOZCECDTUAUCJAKBEALMTUB
      BCPUCCDBANUBBCQRS $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Relationship between real negation and addition.  (Contributed by Steven
       Nguyen, 7-Jan-2023.) $)
    renegadd $p |- ( ( A e. RR /\ B e. RR ) ->
                   ( ( 0 -R A ) = B <-> ( A + B ) = 0 ) ) $=
      ( vx cr wcel wa cc0 cresub co wceq cv caddc crio elre0re resubval mpancom
      wb eqeq1d adantr wreu renegeu oveq2 riota2 sylan2 ancoms bitr4d ) ADEZBDE
      ZFGAHIZBJZACKZLIZGJZCDMZBJZABLIZGJZUGUJUOQUHUGUIUNBGDEUGUIUNJANCGAOPRSUHU
      GUQUOQZUGUHUMCDTURCAUAUMUQCDBUKBJULUPGUKBALUBRUCUDUEUF $.
  $}

  $( Addition of a real number and its negative.  (Contributed by Steven
     Nguyen, 7-Jan-2023.) $)
  renegid $p |- ( A e. RR -> ( A + ( 0 -R A ) ) = 0 ) $=
    ( cr wcel cc0 cresub co wceq caddc eqid wb rernegcl renegadd mpdan mpbii )
    ABCZDAEFZPGZAPHFDGZPIOPBCQRJAKAPLMN $.

  $( Negative zero is a left additive identity.  (Contributed by Steven Nguyen,
     7-Jan-2023.) $)
  reneg0addlid $p |- ( A e. RR -> ( ( 0 -R 0 ) + A ) = A ) $=
    ( cc0 cr wcel cresub co caddc wceq elre0re rernegcl renegid readdridaddlidd
    mpancom ) BCDZACDBBEFZAGFAHAINOBABJBIBKLM $.

  $( Lemma for ~ resubeu .  A value which when added to zero, results in
     negative zero.  (Contributed by Steven Nguyen, 7-Jan-2023.) $)
  resubeulem1 $p |- ( A e. RR -> ( 0 + ( 0 -R ( 0 + 0 ) ) ) = ( 0 -R 0 ) ) $=
    ( cr wcel cc0 cresub caddc wceq elre0re recnd readdcld rernegcl syl addassd
    co renegid eqtr3d wb renegadd syl2anc mpbird eqcomd ) ABCZDDENZDDDDFNZENZFN
    ZUBUCUFGZDUFFNZDGZUBUDUEFNZUHDUBDDUEUBDAHZIZULUBUEUBUDBCZUEBCUBDDUKUKJZUDKL
    ZIMUBUMUJDGUNUDOLPUBDBCUFBCUGUIQUKUBDUEUKUOJDUFRSTUA $.

  $( Lemma for ~ resubeu .  A value which when added to ` A ` , results in
     ` B ` .  (Contributed by Steven Nguyen, 7-Jan-2023.) $)
  resubeulem2 $p |- ( ( A e. RR /\ B e. RR ) ->
    ( A + ( ( 0 -R A ) + ( ( 0 -R ( 0 + 0 ) ) + B ) ) ) = B ) $=
    ( cr wcel wa cc0 cresub co caddc renegid adantr oveq1d simpl recnd rernegcl
    wceq readdcld adantl addassd 3eqtr3d elre0re resubeulem1 recn reneg0addlid
    syl id ) ACDZBCDZEZAFAGHZIHZFFFIHZGHZBIHZIHFUNIHZAUJUNIHIHBUIUKFUNIUGUKFPUH
    AJKLUIAUJUNUIAUGUHMNUIUJUGUJCDUHAOKNUIUNUHUNCDUGUHUMBUHULCDUMCDUHFFBUAZUPQU
    LOUEZUHUFQRNSUHUOBPUGUHFUMIHZBIHFFGHZBIHUOBUHURUSBIBUBLUHFUMBUHFUPNUHUMUQNB
    UCSBUDTRT $.

  ${
    $d x A $.  $d x B $.
    $( Existential uniqueness of real differences.  (Contributed by Steven
       Nguyen, 7-Jan-2023.) $)
    resubeu $p |- ( ( A e. RR /\ B e. RR ) -> E! x e. RR ( A + x ) = B ) $=
      ( cr wcel wa simpl cc0 cresub co caddc wceq wrex rernegcl adantr readdcld
      cv elre0re syl simpr resubeulem2 oveq2 eqeq1d rspcev syl2anc renegeulem )
      BDEZCDEZFZACBUGUHGUIHBIJZHHHKJZIJZCKJZKJZDEBUNKJZCLZBAQZKJZCLZADMUIUJUMUG
      UJDEUHBNOUIULCUGULDEZUHUGUKDEUTUGHHBRZVAPUKNSOUGUHTPPBCUAUSUPAUNDUQUNLURU
      OCUQUNBKUBUCUDUEUF $.

    $( Closure for real subtraction.  Based on ~ subcl .  (Contributed by
       Steven Nguyen, 7-Jan-2023.) $)
    rersubcl $p |- ( ( A e. RR /\ B e. RR ) -> ( A -R B ) e. RR ) $=
      ( vx cr wcel wa cresub co cv caddc wceq crio resubval wreu resubeu ancoms
      riotacl syl eqeltrd ) ADEZBDEZFZABGHBCIJHAKZCDLZDCABMUBUCCDNZUDDEUATUECBA
      OPUCCDQRS $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Relation between real subtraction and addition.  Based on ~ subadd .
       (Contributed by Steven Nguyen, 7-Jan-2023.) $)
    resubadd $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
                   ( ( A -R B ) = C <-> ( B + C ) = A ) ) $=
      ( vx cr wcel w3a cresub co wceq cv caddc crio wb wa resubval 3adant3 wreu
      eqeq1d resubeu oveq2 riota2 sylan2 3impb 3com13 bitr4d ) AEFZBEFZCEFZGABH
      IZCJZBDKZLIZAJZDEMZCJZBCLIZAJZUGUHUKUPNUIUGUHOUJUOCDABPSQUIUHUGURUPNZUIUH
      UGUSUHUGOUIUNDERUSDBATUNURDECULCJUMUQAULCBLUASUBUCUDUEUF $.
  $}

  ${
    resubaddd.1 $e |- ( ph -> A e. RR ) $.
    resubaddd.2 $e |- ( ph -> B e. RR ) $.
    resubaddd.3 $e |- ( ph -> C e. RR ) $.
    $( Relationship between subtraction and addition.  Based on ~ subaddd .
       (Contributed by Steven Nguyen, 8-Jan-2023.) $)
    resubaddd $p |- ( ph -> ( ( A -R B ) = C <-> ( B + C ) = A ) ) $=
      ( cr wcel cresub co wceq caddc wb resubadd syl3anc ) ABHICHIDHIBCJKDLCDMK
      BLNEFGBCDOP $.
  $}

  ${
    $d x y z $.
    $( Real subtraction is an operation on the real numbers.  Based on ~ subf .
       (Contributed by Steven Nguyen, 7-Jan-2023.) $)
    resubf $p |- -R : ( RR X. RR ) --> RR $=
      ( vy vz vx cv caddc co wceq cr crio wcel wral cresub wf resubval rersubcl
      cxp wa eqeltrrd rgen2 df-resub fmpo mpbi ) ADZBDEFCDZGBHIZHJZAHKCHKHHPHLM
      UFCAHHUDHJUCHJQUDUCLFUEHBUDUCNUDUCORSCAHHUEHLCABTUAUB $.
  $}

  $( Addition and subtraction of equals.  Compare ~ pncan2 .  (Contributed by
     Steven Nguyen, 8-Jan-2023.) $)
  repncan2 $p |- ( ( A e. RR /\ B e. RR ) -> ( ( A + B ) -R A ) = B ) $=
    ( cr wcel wa caddc co cresub wceq eqid readdcl simpl simpr resubaddd mpbiri
    ) ACDZBCDZEZABFGZAHGBISSISJRSABABKPQLPQMNO $.

  $( Addition and subtraction of equals.  Based on ~ pncan3 .  (Contributed by
     Steven Nguyen, 8-Jan-2023.) $)
  repncan3 $p |- ( ( A e. RR /\ B e. RR ) -> ( A + ( B -R A ) ) = B ) $=
    ( cr wcel cresub caddc wceq rersubcl w3a eqid resubadd mpbii mpd3an3 ancoms
    co ) BCDZACDZABAEOZFOBGZPQRCDZSBAHPQTIRRGSRJBARKLMN $.

  $( Law for addition and subtraction.  (Contributed by Steven Nguyen,
     28-Jan-2023.) $)
  readdsub $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
    ( ( A + B ) -R C ) = ( ( A -R C ) + B ) ) $=
    ( cr wcel w3a caddc co cresub simp3 readdcl 3adant3 repncan3 syl2anc ancoms
    wceq 3adant2 oveq1d recnd rersubcl simp2 addassd wb readdcld readdcan mpbid
    3eqtr2d syl3anc ) ADEZBDEZCDEZFZCABGHZCIHZGHZCACIHZBGHZGHZPZUNUQPZULUOUMCUP
    GHZBGHURULUKUMDEZUOUMPUIUJUKJZUIUJVBUKABKLZCUMMNULVAABGUIUKVAAPZUJUKUIVECAM
    OQRULCUPBULCVCSULUPUIUKUPDEUJACTQZSULBUIUJUKUAZSUBUGULUNDEZUQDEUKUSUTUCULVB
    UKVHVDVCUMCTNULUPBVFVGUDVCUNUQCUEUHUF $.

  ${
    reladdrsub.1 $e |- ( ph -> A e. RR ) $.
    reladdrsub.2 $e |- ( ph -> B e. RR ) $.
    reladdrsub.3 $e |- ( ph -> ( A + B ) = C ) $.
    $( Move LHS of a sum into RHS of a (real) difference.  Version of
       ~ mvlladdd with real subtraction.  (Contributed by Steven Nguyen,
       8-Jan-2023.) $)
    reladdrsub $p |- ( ph -> B = ( C -R A ) ) $=
      ( cresub co cr wcel wceq readdcld eqeltrrd w3a resubadd syl5ibrcom mp3and
      caddc eqcomd ) ADBHIZCADJKZBJKZCJKZUACLZABCSIZDJGABCEFMNEFAUEUBUCUDOUFDLG
      DBCPQRT $.
  $}

  $( Subtraction from both sides of 'less than'.  Compare ~ ltsub1 .
     (Contributed by SN, 13-Feb-2024.) $)
  reltsub1 $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
                    ( A < B <-> ( A -R C ) < ( B -R C ) ) ) $=
    ( cr wcel w3a cresub co clt wbr caddc rersubcl 3adant2 3adant1 ltadd2d wceq
    simp3 repncan3 ancoms breq12d bitr2d ) ADEZBDEZCDEZFZACGHZBCGHZIJCUFKHZCUGK
    HZIJABIJUEUFUGCUBUDUFDEUCACLMUCUDUGDEUBBCLNUBUCUDQOUEUHAUIBIUBUDUHAPZUCUDUB
    UJCARSMUCUDUIBPZUBUDUCUKCBRSNTUA $.

  $( 'Less than' relationship between addition and subtraction.  Compare
     ~ ltsubadd2 .  (Contributed by SN, 13-Feb-2024.) $)
  reltsubadd2 $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
                       ( ( A -R B ) < C <-> A < ( B + C ) ) ) $=
    ( cr wcel w3a caddc co clt cresub wb simp1 readdcl 3adant1 reltsub1 syl3anc
    wbr simp2 wceq repncan2 breq2d bitr2d ) ADEZBDEZCDEZFZABCGHZIQZABJHZUGBJHZI
    QZUICIQUFUCUGDEZUDUHUKKUCUDUELUDUEULUCBCMNUCUDUERAUGBOPUFUJCUIIUDUEUJCSUCBC
    TNUAUB $.

  $( Cancellation law for real subtraction.  Compare ~ subcan2 .  (Contributed
     by Steven Nguyen, 8-Jan-2023.) $)
  resubcan2 $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
                  ( ( A -R C ) = ( B -R C ) <-> A = B ) ) $=
    ( cr wcel w3a cresub co wceq wa caddc simpl1 simpl3 simpl2 rersubcl syl2anc
    simpr resubaddd mpbid repncan3 eqtr3d ex oveq1 impbid1 ) ADEZBDEZCDEZFZACGH
    BCGHZIZABIZUHUJUKUHUJJZCUIKHZABULUJUMAIUHUJQULACUIUEUFUGUJLUEUFUGUJMZULUFUG
    UIDEUEUFUGUJNZUNBCOPRSULUGUFUMBIUNUOCBTPUAUBABCGUCUD $.

  $( Law for double subtraction.  Compare ~ subsub4 .  (Contributed by Steven
     Nguyen, 14-Jan-2023.) $)
  resubsub4 $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
                  ( ( A -R B ) -R C ) = ( A -R ( B + C ) ) ) $=
    ( cr wcel w3a caddc co readdcl 3adant1 rersubcl 3adant3 simp3 syl2anc simp2
    cresub recnd addassd wceq repncan3 oveq2d simp1 3eqtrd reladdrsub ) ADEZBDE
    ZCDEZFZBCGHZABPHZCPHZAUFUGUIDEUEBCIJUHUJDEZUGUKDEUEUFULUGABKLZUEUFUGMZUJCKN
    ZUHUIUKGHBCUKGHZGHBUJGHZAUHBCUKUHBUEUFUGOZQUHCUNQUHUKUOQRUHUPUJBGUHUGULUPUJ
    SUNUMCUJTNUAUHUFUEUQASURUEUFUGUBBATNUCUD $.

  $( Cancellation law for real subtraction.  Compare ~ nnncan2 .  (Contributed
     by Steven Nguyen, 14-Jan-2023.) $)
  rennncan2 $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
                  ( ( A -R C ) -R ( B -R C ) ) = ( A -R B ) ) $=
    ( cr wcel cresub co caddc wceq simp1 simp3 simp2 rersubcl syl2anc resubsub4
    w3a syl3anc repncan3 oveq2d eqtrd ) ADEZBDEZCDEZPZACFGBCFGZFGZACUEHGZFGZABF
    GUDUAUCUEDEZUFUHIUAUBUCJUAUBUCKZUDUBUCUIUAUBUCLZUJBCMNACUEOQUDUGBAFUDUCUBUG
    BIUJUKCBRNST $.

  $( Cancellation law for real subtraction.  Compare ~ npncan3 .  (Contributed
     by Steven Nguyen, 28-Jan-2023.) $)
  renpncan3 $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
                  ( ( A -R B ) + ( C -R A ) ) = ( C -R B ) ) $=
    ( cr wcel cresub co caddc wceq simp1 rersubcl ancoms 3adant2 simp2 readdsub
    w3a syl3anc repncan3 oveq1d eqtr3d ) ADEZBDEZCDEZPZACAFGZHGZBFGZABFGUEHGZCB
    FGUDUAUEDEZUBUGUHIUAUBUCJUAUCUIUBUCUAUICAKLMUAUBUCNAUEBOQUDUFCBFUAUCUFCIUBA
    CRMST $.

  $( Cancellation law for addition and real subtraction.  Compare ~ pnpcan .
     (Contributed by Steven Nguyen, 19-May-2023.) $)
  repnpcan $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
                  ( ( A + B ) -R ( A + C ) ) = ( B -R C ) ) $=
    ( cr wcel w3a caddc co cresub wceq readdcl resubsub4 stoic4a 3adant3 oveq1d
    repncan2 eqtr3d ) ADEZBDEZCDEZFZABGHZAIHZCIHZUBACGHIHZBCIHRSUBDETUDUEJABKUB
    ACLMUAUCBCIRSUCBJTABPNOQ $.

  $( Cancellation law for mixed addition and real subtraction.  Compare
     ~ ppncan .  (Contributed by SN, 3-Sep-2023.) $)
  reppncan $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
                  ( ( A + C ) + ( B -R C ) ) = ( A + B ) ) $=
    ( cr wcel w3a caddc co cresub wceq repnpcan readdcl 3adant3 3adant2 3adant1
    rersubcl resubaddd mpbid ) ADEZBDEZCDEZFZABGHZACGHZIHBCIHZJUDUEGHUCJABCKUBU
    CUDUESTUCDEUAABLMSUAUDDETACLNTUAUEDESBCPOQR $.

  ${
    resubidaddridlem.a $e |- ( ph -> A e. RR ) $.
    resubidaddridlem.b $e |- ( ph -> B e. RR ) $.
    resubidaddridlem.c $e |- ( ph -> C e. RR ) $.
    resubidaddridlem.1 $e |- ( ph -> ( A -R B ) = ( B -R C ) ) $.
    $( Lemma for ~ resubidaddlid .  A special case of ~ npncan .  (Contributed
       by Steven Nguyen, 8-Jan-2023.) $)
    resubidaddlidlem $p |-
      ( ph -> ( ( A -R B ) + ( B -R C ) ) = ( A -R C ) ) $=
      ( cresub co caddc cr wcel rersubcl syl2anc readdcld resubaddd mpbid recnd
      wceq eqcomd oveq1d addassd 3eqtr3d reladdrsub ) ADBCIJZCDIJZKJZBGAUFUGABL
      MCLMZUFLMEFBCNOZAUIDLMUGLMFGCDNOZPADUFKJZUGKJCUGKJZDUHKJBAULCUGKAUGUFTULC
      TAUFUGHUAACDUFFGUJQRUBADUFUGADGSAUFUJSAUGUKSUCAUFUGTUMBTHABCUGEFUKQRUDUE
      $.
  $}

  $( Any real number subtracted from itself forms a left additive identity.
     (Contributed by Steven Nguyen, 8-Jan-2023.) $)
  resubidaddlid $p |- ( ( A e. RR /\ B e. RR ) -> ( ( A -R A ) + B ) = B ) $=
    ( cr wcel wa caddc co cresub wceq readdsub 3anidm13 repncan2 eqtr3d ) ACDZB
    CDZEABFGAHGZAAHGBFGZBNOPQIABAJKABLM $.

  $( Distribution of multiplication over real subtraction.  (Contributed by
     Steven Nguyen, 3-Jun-2023.) $)
  resubdi $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
                 ( A x. ( B -R C ) ) = ( ( A x. B ) -R ( A x. C ) ) ) $=
    ( cr wcel w3a cmul co remulcl 3adant2 simp1 rersubcl 3adant1 remulcld caddc
    cresub recnd simp3 adddid wceq repncan3 ancoms oveq2d eqtr3d reladdrsub ) A
    DEZBDEZCDEZFZACGHZABCPHZGHZABGHZUFUHUJDEUGACIJUIAUKUFUGUHKZUGUHUKDEUFBCLMZN
    UIACUKOHZGHUJULOHUMUIACUKUIAUNQUICUFUGUHRQUIUKUOQSUIUPBAGUGUHUPBTZUFUHUGUQC
    BUAUBMUCUDUE $.

  $( Equality of two left-additive identities.  See ~ resubidaddlid .  Uses
     ~ ax-i2m1 .  (Contributed by SN, 25-Dec-2023.) $)
  re1m1e0m0 $p |- ( 1 -R 1 ) = ( 0 -R 0 ) $=
    ( c1 cresub co cc0 wceq wtru 0red cr wcel 1re rersubcl mp2an a1i caddc cmul
    ci ax-icn mulcli ax-1cn ax-i2m1 recni addassi repncan3 oveq2i eqtri 3eqtr3i
    oveq1i reladdrsub mptru ) AABCZDDBCEFDUJDFGUJHIZFAHIZULUKJJAAKLZMDUJNCZDEFP
    POCZANCZUJNCZUPUNDUQUOAUJNCZNCUPUOAUJPPQQRSUJUMUAUBURAUONULULURAEJJAAUCLUDU
    EUPDUJNTUGTUFMUHUI $.

  $( Lemma for ~ sn-00id .  (Contributed by SN, 25-Dec-2023.) $)
  sn-00idlem1 $p |- ( A e. RR -> ( A x. ( 0 -R 0 ) ) = ( A -R A ) ) $=
    ( cr wcel cresub cmul cc0 wceq 1re resubdi mp3an23 re1m1e0m0 oveq2i ax-1rid
    c1 co a1i oveq12d 3eqtr3d ) ABCZANNDOZEOZANEOZUBDOZAFFDOZEOZAADOSNBCZUFUAUC
    GHHANNIJUAUEGSTUDAEKLPSUBAUBADAMZUGQR $.

  $( Lemma for ~ sn-00id .  (Contributed by SN, 25-Dec-2023.) $)
  sn-00idlem2 $p |- ( ( 0 -R 0 ) =/= 0 -> ( 0 -R 0 ) = 1 ) $=
    ( cc0 cresub co wne cmul c1 wceq cr wcel rennncan2 mp3an re1m1e0m0 rernegcl
    0re eqtr4i ax-mp sn-00idlem1 1re 3eqtr4i a1i 1red id remulcan2d mpbii ) AAB
    CZADZUEUEECZFUEECZGUEFGUEUEBCZFFBCZUGUHUIUEUJAHIZUKUKUIUEGNNNAAAJKLOUEHIZUG
    UIGUKULNAMPZUEQPFHIUHUJGRFQPSUFUEFUEULUFUMTZUFUAUNUFUBUCUD $.

  $( Lemma for ~ sn-00id .  (Contributed by SN, 25-Dec-2023.) $)
  sn-00idlem3 $p |- ( ( 0 -R 0 ) = 1 -> ( 0 + 0 ) = 0 ) $=
    ( cc0 cresub co c1 wceq caddc cmul oveq2 wcel 0re sn-00idlem1 ax-mp ax-1rid
    cr 3eqtr3g oveq1d resubidaddlid mp2an eqtr3di ) AABCZDEZTAFCZAAFCAUATAAFUAA
    TGCZADGCZTATDAGHANIZUCTEJAKLUEUDAEJAMLOPUEUEUBAEJJAAQRS $.

  $( ~ 00id proven without ~ ax-mulcom but using ~ ax-1ne0 .  (Though note that
     the current version of ~ 00id can be changed to avoid ~ ax-icn ,
     ~ ax-addcl , ~ ax-mulcl , ~ ax-i2m1 , ~ ax-cnre .  Most of this is by
     using ~ 0cnALT3 instead of ~ 0cn ).  (Contributed by SN, 25-Dec-2023.)
     (Proof modification is discouraged.) $)
  sn-00id $p |- ( 0 + 0 ) = 0 $=
    ( cc0 caddc co wceq wn cresub wne cr wcel wb 0re resubadd mp3an sn-00idlem2
    necon3abii c1 sn-00idlem3 syl sylbir pm2.18i ) AABCADZUAEAAFCZAGZUAUAUBAAHI
    ZUDUDUBADUAJKKKAAALMOUCUBPDUANQRST $.
  $( $j usage 'sn-00id' avoids 'ax-mulcom'; $)

  $( Real number version of ~ 0m0e0 proven without ~ ax-mulcom .  (Contributed
     by SN, 23-Jan-2024.) $)
  re0m0e0 $p |- ( 0 -R 0 ) = 0 $=
    ( cc0 cresub co wceq wtru 0red caddc sn-00id a1i reladdrsub mptru eqcomi )
    AAABCZAMDEAAAEFZNAAGCADEHIJKL $.
  $( $j usage 're0m0e0' avoids 'ax-mulcom'; $)

  $( Real number version of ~ addlid .  (Contributed by SN, 23-Jan-2024.) $)
  readdlid $p |- ( A e. RR -> ( 0 + A ) = A ) $=
    ( cr wcel cc0 caddc co cresub re0m0e0 oveq1i reneg0addlid eqtr3id ) ABCDAEF
    DDGFZAEFALDAEHIAJK $.
  $( $j usage 'readdlid' avoids 'ax-mulcom'; $)

  ${
    $d A x y $.
    $( ~ addlid without ~ ax-mulcom .  (Contributed by SN, 23-Jan-2024.) $)
    sn-addlid $p |- ( A e. CC -> ( 0 + A ) = A ) $=
      ( vx vy cc wcel cv ci cmul co caddc wceq cr wrex cc0 cnre w3a 0cnd simp2l
      wa recnd ax-icn a1i simp2r mulcld addassd readdlid adantr 3ad2ant2 oveq1d
      eqtr3d simp3 oveq2d 3eqtr4d 3exp rexlimdvv mpd ) ADEZABFZGCFZHIZJIZKZCLMB
      LMNAJIZAKZBCAOUQVBVDBCLLUQURLEZUSLEZSZVBVDUQVGVBPZNVAJIZVAVCAVHNURJIZUTJI
      VIVAVHNURUTVHQVHURUQVEVFVBRTVHGUSGDEVHUAUBVHUSUQVEVFVBUCTUDUEVHVJURUTJVGU
      QVJURKZVBVEVKVFURUFUGUHUIUJVHAVANJUQVGVBUKZULVLUMUNUOUP $.
    $( $j usage 'sn-addlid' avoids 'ax-mulcom'; $)
  $}

  ${
    $d A x $.
    $( Real number version of ~ mul02 proven without ~ ax-mulcom .
       (Contributed by SN, 23-Jan-2024.) $)
    remul02 $p |- ( A e. RR -> ( 0 x. A ) = 0 ) $=
      ( vx cr wcel c1 c2 wne cmul co wceq wa oveq1i cresub re0m0e0 3eqtri recnd
      cc0 1re mulassd 3eqtrd sn-1ne2 cv elre0re remulcld ax-rrecex sylan simprr
      wrex id caddc eqcomi oveq2i readdcli sn-00idlem1 ax-mp repnpcan re1m1e0m0
      df-2 mp3an eqtr2i a1i 2cnd 0cnd simpll oveq1d ad2antrr simprl 2re ax-1rid
      oveq2d mp1i eqtr3d rexlimddv ex necon1d mpi ) ACDZEFGQAHIZQJUAVQVRQEFVQVR
      QGZEFJZVQVSKZVRBUBZHIZEJZVTBCVQVRCDZVSWDBCUHVQQAAUCVQUIUDZBVRUEUFWAWBCDZW
      DKZKZWCEFWAWGWDUGZWIWCFWCHIZFEHIZFWIWCFQHIZAHIZWBHIZFVRHIZWBHIWKWCWOJWIVR
      WNWBHQWMAHWMEEUJIZQHIZQFWQQHURLWRWQQQMIZHIZWQWQMIZQQWSWQHWSQNUKULWQCDWTXA
      JEERRUMWQUNUOXAEEMIZWSQECDZXCXCXAXBJRRREEEUPUSUQNOOUTLLVAWIWNWPWBHWIFQAWI
      VBZWIVCWIAVQVSWHVDPSVEWIFVRWBXDWIVRVQWEVSWHWFVFPWIWBWAWGWDVGPSTWIWCEFHWJV
      JFCDWLFJWIVHFVIVKTVLVMVNVOVP $.
    $( $j usage 'remul02' avoids 'ax-mulcom'; $)
  $}

  $( ~ 0ne2 without ~ ax-mulcom .  (Contributed by SN, 23-Jan-2024.) $)
  sn-0ne2 $p |- 0 =/= 2 $=
    ( cc0 c1 caddc co c2 wne cr wcel 1re ax-mp clt wbr 2re ltadd2i biimpi 1p1e2
    c3 1p2e3 3brtr3g 3re wceq readdlid wo sn-1ne2 lttri2i mpbi 1red lttri mpdan
    ltned a1i mpancom gtned jaoi df-3 neeqtri eqnetri oveq1 necon3i ) ABCDZEBCD
    ZFAEFUTBVABGHUTBUAIBUBJBQVABEKLZEBKLZUCZBQFZBEFVDUDBEIMUEUFVBVEVCVBBQVBUGVB
    EQKLBQKLVBBBCDZBECDZEQKVBVFVGKLBEBIMINOPRSBEQIMTUHUIUJVCQBQGHVCTUKQEKLVCQBK
    LVCVGVFQEKVCVGVFKLEBBMIINORPSQEBTMIUHULUMUNJUOUPUQAEUTVAAEBCURUSJ $.
  $( $j usage 'sn-0ne2' avoids 'ax-mulcom'; $)

  ${
    $d A x $.
    $( Real number version of ~ mul01 proven without ~ ax-mulcom .
       (Contributed by SN, 23-Jan-2024.) $)
    remul01 $p |- ( A e. RR -> ( A x. 0 ) = 0 ) $=
      ( vx cr wcel cc0 cmul co c1 wne wceq wa 2re eqtrd wrex a1i remulcld recnd
      c2 mulassd oveq2d wn wi oveq2 adantl ax-1rid mp1i cv simpl sn-0ne2 necomi
      0red mteqand ax-rrecex syl2an 2cnd simplll simprl simprr remul02 ad2antrl
      eqtr2 0cnd 3eqtr3rd rexlimddv sn-1ne2 eqnetrd pm2.21ddne ex pm2.01 neqned
      mpdan syl id elre0re sylan simpll necon1d mpd ) ACDZAEFGZHIZVTEJVSVTHJZWB
      UAZUBZWAVSWBWCVSWBKZWCRVTFGZRWEWFRHFGZRWBWFWGJVSVTHRFUCUDRCDZWGRJWELRUEUF
      MZWEWFHRWEWFRJZWFHJZWIWEWJKZWFBUGZFGZHJZWKBCWEWFCDWFEIWOBCNWJWERVTWHWELOW
      EAEVSWBUHWEUKPPWJWFEREREIWJERUIUJOWFREVAULBWFUMUNWLWMCDZWOKZKZWNRVTWMFGZF
      GHWFWRRVTWMWRUOWRVTWRAEVSWBWJWQUPZWRUKPQWRWMWLWPWOUQQZSWLWPWOURWRWSVTRFWR
      WSAEWMFGZFGZVTWRAEWMWRAWTQWRVBXASWRXBEAFWPXBEJWLWOWMUSZUTTMTVCVDVKHRIWEVE
      OVFVGVHWDVTHWBVIVJVLVSVTEVTHVSVTEIZWBVSXEKZWSHJZWBBCVSVTCDXEXGBCNVSAEVSVM
      AVNPBVTUMVOXFWPXGKZKZWSXCHVTXIAEWMXIAVSXEXHVPQXIVBXIWMXFWPXGUQQSXFWPXGURW
      PXCVTJXFXGWPXBEAFXDTUTVCVDVHVQVR $.
    $( $j usage 'remul01' avoids 'ax-mulcom'; $)
  $}

  ${
    sn-remul0ord.a $e |- ( ph -> A e. RR ) $.
    sn-remul0ord.b $e |- ( ph -> B e. RR ) $.
    $( A product is zero iff one of its factors are zero.  (Contributed by SN,
       24-Nov-2025.) $)
    sn-remul0ord $p |- ( ph -> ( ( A x. B ) = 0 <-> ( A = 0 \/ B = 0 ) ) ) $=
      ( cmul co cc0 wceq wo wa wne cr wcel remul02 syl adantr eqeq2d syl5ibrcom
      eqeq1d 0red simpr remulcan2d bitr3d biimpd impancom necon1bd orrd remul01
      ex oveq1 oveq2 jaod impbid ) ABCFGZHIZBHIZCHIZJZAUPUSAUPKZUQURUTUQCHACHLZ
      UPUQAVAKZUPUQVBUOHCFGZIUPUQVBVCHUOAVCHIZVAACMNZVDECOPZQRVBBHCABMNZVADQVBU
      AAVEVAEQAVAUBUCUDUEUFUGUHUJAUQUPURAUPUQVDVFUQUOVCHBHCFUKTSAUPURBHFGZHIZAV
      GVIDBUIPURUOVHHCHBFULTSUMUN $.
    $( $j usage 'sn-remul0ord' avoids 'ax-mulcom'; $)
  $}

  $( Subtraction of a real number from itself (compare ~ subid ).  (Contributed
     by SN, 23-Jan-2024.) $)
  resubid $p |- ( A e. RR -> ( A -R A ) = 0 ) $=
    ( cr wcel cc0 cresub co cmul re0m0e0 oveq2i sn-00idlem1 remul01 3eqtr3a ) A
    BCADDEFZGFADGFAAEFDMDAGHIAJAKL $.

  $( Real number version of ~ addrid without ~ ax-mulcom .  (Contributed by SN,
     23-Jan-2024.) $)
  readdrid $p |- ( A e. RR -> ( A + 0 ) = A ) $=
    ( cr wcel cresub co cc0 wceq caddc resubid id elre0re resubaddd mpbid ) ABC
    ZAADEFGAFHEAGAINAAFNJZOAKLM $.
  $( $j usage 'readdrid' avoids 'ax-mulcom'; $)

  $( Real number version of ~ subid1 without ~ ax-mulcom .  (Contributed by SN,
     23-Jan-2024.) $)
  resubid1 $p |- ( A e. RR -> ( A -R 0 ) = A ) $=
    ( cr wcel cc0 cresub co wceq caddc readdlid id elre0re resubaddd mpbird ) A
    BCZADEFAGDAHFAGAINADANJZAKOLM $.
  $( $j usage 'resubid1' avoids 'ax-mulcom'; $)

  $( A real number is equal to the negative of its negative.  Compare
     ~ negneg .  (Contributed by SN, 13-Feb-2024.) $)
  renegneg $p |- ( A e. RR -> ( 0 -R ( 0 -R A ) ) = A ) $=
    ( cr wcel cc0 cresub co caddc wceq rernegcl syl id renegid elre0re readdrid
    eqeltrd repncan3 syl2anc oveq2d 3eqtr4d recnd readdlid recn oveq1d readdcan
    addassd w3a biimpa syl31anc ) ABCZDDAEFZEFZBCZUIAUJGFZBCZUMUKGFZUMAGFZHZUKA
    HZUIUJBCZULAIZUJIJZUIKUIUMDBALZAMZOUIAUJUKGFZGFZDAGFZUOUPUIADGFAVEVFANUIVDD
    AGUIUSDBCVDDHUTVCUJDPQRAUASUIAUJUKAUBUIUJUTTUIUKVATUEUIUMDAGVBUCSULUIUNUFUQ
    URUKAUMUDUGUH $.

  $( Commuted version of ~ readdcan without ~ ax-mulcom .  (Contributed by SN,
     21-Feb-2024.) $)
  readdcan2 $p |- ( ( A e. RR /\ B e. RR /\ C e. RR ) ->
                           ( ( A + C ) = ( B + C ) <-> A = B ) ) $=
    ( cr wcel caddc co wceq cc0 oveq1 adantl simpl recnd simpr addassd readdrid
    wa oveq2d adantr 3eqtrd w3a cresub rernegcl renegid 3adant2 3adant1 3eqtr3d
    ex impbid1 ) ADEZBDEZCDEZUAZACFGZBCFGZHZABHZUMUPUQUMUPQUNICUBGZFGZUOURFGZAB
    UPUSUTHUMUNUOURFJKUMUSAHZUPUJULVAUKUJULQZUSACURFGZFGZAIFGZAVBACURVBAUJULLMV
    BCUJULNMVBURULURDEZUJCUCZKMOULVDVEHUJULVCIAFCUDZRKUJVEAHULAPSTUESUMUTBHZUPU
    KULVIUJUKULQZUTBVCFGZBIFGZBVJBCURVJBUKULLMVJCUKULNMVJURULVFUKVGKMOULVKVLHUK
    ULVCIBFVHRKUKVLBHULBPSTUFSUGUHABCFJUI $.
  $( $j usage 'readdcan2' avoids 'ax-mulcom'; $)

  $( Commuted version of ~ renegid .  (Contributed by SN, 4-May-2024.) $)
  renegid2 $p |- ( A e. RR -> ( ( 0 -R A ) + A ) = 0 ) $=
    ( cr wcel cresub co caddc wceq renegid oveq2d rernegcl readdrid eqtrd recnd
    cc0 syl recn addassd readdlid 3eqtr4d wb readdcld elre0re readdcan2 syl3anc
    id mpbid ) ABCZNADEZAFEZUHFEZNUHFEZGZUINGZUGUHAUHFEZFEZUHUJUKUGUOUHNFEZUHUG
    UNNUHFAHIUGUHBCZUPUHGAJZUHKOLUGUHAUHUGUHURMZAPUSQUGUQUKUHGURUHROSUGUIBCNBCU
    QULUMTUGUHAURUGUEUAAUBURUINUHUCUDUF $.

  ${
    remulneg2d.a $e |- ( ph -> A e. RR ) $.
    remulneg2d.b $e |- ( ph -> B e. RR ) $.
    $( Product with negative is negative of product.  (Contributed by SN,
       25-Jan-2025.) $)
    remulneg2d $p |- ( ph -> ( A x. ( 0 -R B ) ) = ( 0 -R ( A x. B ) ) ) $=
      ( cc0 cresub co cmul cr wcel wceq 0red resubdi syl3anc remul01 syl oveq1d
      eqtrd ) ABFCGHIHZBFIHZBCIHZGHZFUBGHABJKZFJKCJKTUCLDAMEBFCNOAUAFUBGAUDUAFL
      DBPQRS $.
  $}

  ${
    $d a b $.
    $( Proof of ~ it0e0 without ~ ax-mulcom .  Informally, a real number times
       0 is 0, and ` E. r e. RR r = _i x. s ` by ~ ax-cnre and ~ renegid2 .
       (Contributed by SN, 30-Apr-2024.) $)
    sn-it0e0 $p |- ( _i x. 0 ) = 0 $=
      ( va vb cc wcel cv ci cmul co caddc wceq cr wrex wa remul01 adantr oveq1d
      cc0 recn syl eqtr3d 0cn cnre cresub oveq2 ax-icn a1i mulassd oveq2d eqtrd
      ad2antlr rernegcl recnd mulcld adantl addassd renegid2 sn-addlid sylan9eq
      0cnd eqeq2d biimpa elre0re readdcld ad2antrr ex syl5 rexlimivv mp2b ) QCD
      QAEZFBEZGHZIHZJZBKLAKLFQGHZQJZUAABQUBVMVOABKKVMQVIUCHZQIHZVPVLIHZJZVIKDZV
      JKDZMZVOQVLVPIUDWBVSVOWBVSMZVKQGHZVNQWAWDVNJVTVSWAWDFVJQGHZGHVNWAFVJQFCDW
      AUEUFZVJRZWAUSUGWAWEQFGVJNUHUIUJWCVQQGHZWDQWCVQVKQGWBVSVQVKJWBVRVKVQWBVPV
      IIHZVKIHZVRVKWBVPVIVKVTVPCDWAVTVPVIUKZULOVTVICDWAVIROWAVKCDZVTWAFVJWFWGUM
      ZUNUOVTWAWJQVKIHZVKVTWIQVKIVIUPPWAWLWNVKJWMVKUQSURTUTVAPWCVQKDZWHQJVTWOWA
      VSVTVPQWKVIVBVCVDVQNSTTVEVFVGVH $.
    $( $j usage 'sn-it0e0' avoids 'ax-mulcom'; $)
  $}

  ${
    $d A b x y $.
    $( A combination of ~ cnegex and ~ cnegex2 , this proof takes ~ cnre
       ` A = r + _i x. s ` and shows that ` _i x. -u s + -u r ` is both a left
       and right inverse.  (Contributed by SN, 5-May-2024.)  (Proof shortened
       by SN, 4-Jul-2025.) $)
    sn-negex12 $p |- ( A e. CC ->
                             E. b e. CC ( ( A + b ) = 0 /\ ( b + A ) = 0 ) ) $=
      ( vx vy cc wcel ci cmul co caddc wceq cr wrex cc0 wa eqeq1d adantl adantr
      addassd oveq2d cnre cresub oveq2 oveq1 anbi12d ax-icn a1i rernegcl mulcld
      cv recnd addcld recn adddid sn-it0e0 eqtrdi eqtr3d readdrid 3eqtrd oveq1d
      renegid 3eqtr3d renegid2 sn-addlid syl 3eqtr3rd 3eqtr2d rspcedvdw rexbidv
      jca syl5ibrcom rexlimdvva mpd ) AEFZACUJZGDUJZHIZJIZKZDLMCLMABUJZJIZNKZVT
      AJIZNKZOZBEMZCDAUAVNVSWFCDLLVNVOLFZVPLFZOZOWFVSVRVTJIZNKZVTVRJIZNKZOZBEMZ
      WIWOVNWIWNVRGNVPUBIZHIZNVOUBIZJIZJIZNKZWSVRJIZNKZOBWSEVTWSKZWKXAWMXCXDWJW
      TNVTWSVRJUCPXDWLXBNVTWSVRJUDPUEWIWQWRWHWQEFWGWHGWPGEFWHUFUGZWHWPVPUHUKZUI
      QZWGWREFWHWGWRVOUHUKRZULWIXAXCWIVRWQJIZWRJIVOWRJIZWTNWIXIVOWRJWIXIVOVQWQJ
      IZJIVONJIZVOWIVOVQWQWGVOEFWHVOUMRZWHVQEFZWGWHGVPXEVPUMZUIQZXGSWIXKNVOJWHX
      KNKWGWHGVPWPJIZHIZXKNWHGVPWPXEXOXFUNWHXRGNHIZNWHXQNGHVPVATUOUPUQQTWGXLVOK
      WHVOURRUSUTWIVRWQWRWIVOVQXMXPULZXGXHSWGXJNKWHVOVARVBWIXBWQWRVRJIZJIWQVQJI
      ZNWIWQWRVRXGXHXTSWIVQYAWQJWIWRVOJIZVQJINVQJIZYAVQWIYCNVQJWGYCNKWHVOVCRUTW
      IWRVOVQXHXMXPSWIXNYDVQKXPVQVDVEVFTWHYBNKWGWHGWPVPJIZHIZYBNWHGWPVPXEXFXOUN
      WHYFXSNWHYENGHVPVCTUOUPUQQVGVJVHQVSWEWNBEVSWBWKWDWMVSWAWJNAVRVTJUDPVSWCWL
      NAVRVTJUCPUEVIVKVLVM $.

    $( Proof of ~ cnegex without ~ ax-mulcom .  (Contributed by SN,
       30-Apr-2024.) $)
    sn-negex $p |- ( A e. CC -> E. b e. CC ( A + b ) = 0 ) $=
      ( cc wcel cv caddc co cc0 wceq wa wrex sn-negex12 simpl reximi syl ) ACDA
      BEZFGHIZPAFGHIZJZBCKQBCKABLSQBCQRMNO $.
    $( $j usage 'sn-negex' avoids 'ax-mulcom'; $)

    $( Proof of ~ cnegex2 without ~ ax-mulcom .  (Contributed by SN,
       5-May-2024.) $)
    sn-negex2 $p |- ( A e. CC -> E. b e. CC ( b + A ) = 0 ) $=
      ( cc wcel cv caddc co cc0 wceq wa wrex sn-negex12 simpr reximi syl ) ACDA
      BEZFGHIZPAFGHIZJZBCKRBCKABLSRBCQRMNO $.
    $( $j usage 'sn-negex2' avoids 'ax-mulcom'; $)
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d ph x $.
    sn-addcand.a $e |- ( ph -> A e. CC ) $.
    sn-addcand.b $e |- ( ph -> B e. CC ) $.
    sn-addcand.c $e |- ( ph -> C e. CC ) $.
    $( ~ addcand without ~ ax-mulcom .  Note how the proof is almost identical
       to ~ addcan .  (Contributed by SN, 5-May-2024.) $)
    sn-addcand $p |- ( ph -> ( ( A + B ) = ( A + C ) <-> B = C ) ) $=
      ( vx caddc co cc0 wceq cc wcel syl wa oveq2 oveq1d adantr addassd cv wrex
      wb sn-negex2 simprr sn-addlid 3eqtr3d eqeq12d imbitrid impbid1 rexlimddv
      simprl ) AHUAZBIJZKLZBCIJZBDIJZLZCDLZUCHMABMNZUOHMUBEBHUDOAUMMNZUOPZPZURU
      SURUMUPIJZUMUQIJZLVCUSUPUQUMIQVCVDCVEDVCUNCIJKCIJZVDCVCUNKCIAVAUOUEZRVCUM
      BCAVAUOULZAUTVBESZACMNZVBFSZTVCVJVFCLVKCUFOUGVCUNDIJKDIJZVEDVCUNKDIVGRVCU
      MBDVHVIADMNZVBGSZTVCVMVLDLVNDUFOUGUHUICDBIQUJUK $.
    $( $j usage 'sn-addcand' avoids 'ax-mulcom'; $)
  $}

  ${
    $d A x $.
    $( ~ addrid without ~ ax-mulcom .  (Contributed by SN, 5-May-2024.) $)
    sn-addrid $p |- ( A e. CC -> ( A + 0 ) = A ) $=
      ( vx cc wcel caddc cc0 wceq sn-negex2 simprr oveq1d sn-00id eqtrdi simprl
      cv co wa simpl 0cnd addassd 3eqtr2rd addcld sn-addcand mpbid rexlimddv )
      ACDZBNZAEOZFGZAFEOZAGZBCABHUEUFCDZUHPZPZUFUIEOZUGGUJUMUGFUGFEOZUNUEUKUHIZ
      UMUOFFEOFUMUGFFEUPJKLUMUFAFUEUKUHMZUEULQZUMRZSTUMUFUIAUQUMAFURUSUAURUBUCU
      D $.
    $( $j usage 'sn-addrid' avoids 'ax-mulcom'; $)
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d ph x $.
    sn-addcan2d.a $e |- ( ph -> A e. CC ) $.
    sn-addcan2d.b $e |- ( ph -> B e. CC ) $.
    sn-addcan2d.c $e |- ( ph -> C e. CC ) $.
    $( ~ addcan2d without ~ ax-mulcom .  (Contributed by SN, 5-May-2024.) $)
    sn-addcan2d $p |- ( ph -> ( ( A + C ) = ( B + C ) <-> A = B ) ) $=
      ( vx caddc co cc0 wceq cc wcel syl wa oveq1 adantr addassd oveq2d cv wrex
      wb sn-negex simprl simprr sn-addrid eqeq12d imbitrid impbid1 rexlimddv
      3eqtrd ) ADHUAZIJZKLZBDIJZCDIJZLZBCLZUCHMADMNZUOHMUBGDHUDOAUMMNZUOPZPZURU
      SURUPUMIJZUQUMIJZLVCUSUPUQUMIQVCVDBVECVCVDBUNIJBKIJZBVCBDUMABMNZVBERZAUTV
      BGRZAVAUOUEZSVCUNKBIAVAUOUFZTVCVGVFBLVHBUGOULVCVECUNIJCKIJZCVCCDUMACMNZVB
      FRZVIVJSVCUNKCIVKTVCVMVLCLVNCUGOULUHUIBCDIQUJUK $.
    $( $j usage 'sn-addcan2d' avoids 'ax-mulcom'; $)
  $}

  $( ~ ixi without ~ ax-mulcom .  (Contributed by SN, 5-May-2024.) $)
  reixi $p |- ( _i x. _i ) = ( 0 -R 1 ) $=
    ( ci cmul co cc0 c1 cresub wceq wtru caddc ax-i2m1 wcel 1re renegid2 eqtr4i
    cr ax-mp cc ax-icn mulcli a1i rernegcl recnd mp1i sn-addcan2d mpbii mptru
    1cnd ) AABCZDEFCZGZHUHEICZUIEICZGUJUKDULJEOKZULDGLEMPNHUHUIEUHQKHAARRSTUMUI
    QKHLUMUIEUAUBUCHUGUDUEUF $.
  $( $j usage 'reixi' avoids 'ax-mulcom'; $)

  $( ~ i4 without ~ ax-mulcom .  (Contributed by SN, 27-May-2024.) $)
  rei4 $p |- ( ( _i x. _i ) x. ( _i x. _i ) ) = 1 $=
    ( ci cmul co cc0 c1 cresub reixi oveq12i wcel wceq rernegcl 1red remulneg2d
    cr 1re ax-1rid syl oveq2d renegneg 3eqtrd ax-mp eqtri ) AABCZUCBCDEFCZUDBCZ
    EUCUDUCUDBGGHENIZUEEJOUFUEDUDEBCZFCDUDFCEUFUDEEKZUFLMUFUGUDDFUFUDNIUGUDJUHU
    DPQRESTUAUB $.
  $( $j usage 'rei4' avoids 'ax-mulcom'; $)

  ${
    sn-addid0.a $e |- ( ph -> A e. CC ) $.
    sn-addid0.1 $e |- ( ph -> ( A + A ) = A ) $.
    $( A number that sums to itself is zero.  Compare ~ addid0 ,
       ~ readdridaddlidd .  (Contributed by SN, 5-May-2024.) $)
    sn-addid0 $p |- ( ph -> A = 0 ) $=
      ( caddc co cc0 wceq cc wcel sn-addrid syl eqtr4d 0cnd sn-addcand mpbid )
      ABBEFZBGEFZHBGHAQBRDABIJRBHCBKLMABBGCCANOP $.
    $( $j usage 'sn-addid0' avoids 'ax-mulcom'; $)
  $}

  $( ~ mul01 without ~ ax-mulcom .  (Contributed by SN, 5-May-2024.) $)
  sn-mul01 $p |- ( A e. CC -> ( A x. 0 ) = 0 ) $=
    ( cc wcel cc0 cmul co id 0cnd mulcld caddc adddid sn-00id eqtr3di sn-addid0
    oveq2i ) ABCZADEFZPADPGZPHZIPADDJFZEFQQJFQPADDRSSKTDAELOMN $.
  $( $j usage 'sn-mul01' avoids 'ax-mulcom'; $)

  ${
    $d A x y $.  $d B x y $.
    $( ~ negeu without ~ ax-mulcom and complex number version of ~ resubeu .
       (Contributed by SN, 5-May-2024.) $)
    sn-subeu $p |- ( ( A e. CC /\ B e. CC ) -> E! x e. CC ( A + x ) = B ) $=
      ( vy cc wcel wa cv caddc co wceq wreu wrex sn-negex adantr wb wral simprl
      cc0 addcld simplr simplrr oveq1d simplll simplrl simpllr addassd 3eqtr3rd
      sn-addlid eqeq2d simpr sn-addcand bitrd ralrimiva reu6i syl2anc rexlimddv
      syl ) BEFZCEFZGZBDHZIJZSKZBAHZIJZCKZAELZDEUSVDDEMUTBDNOVAVBEFZVDGZGZVBCIJ
      ZEFVGVEVLKZPZAEQVHVKVBCVAVIVDRUSUTVJUATVKVNAEVKVEEFZGZVGVFBVLIJZKVMVPCVQV
      FVPVCCIJSCIJZVQCVPVCSCIVAVIVDVOUBUCVPBVBCUSUTVJVOUDZVAVIVDVOUEZUSUTVJVOUF
      ZUGVPUTVRCKWACUIURUHUJVPBVEVLVSVKVOUKVPVBCVTWATULUMUNVGAEVLUOUPUQ $.
    $( $j usage 'sn-subeu' avoids 'ax-mulcom'; $)

    $( ~ subcl without ~ ax-mulcom .  (Contributed by SN, 5-May-2024.) $)
    sn-subcl $p |- ( ( A e. CC /\ B e. CC ) -> ( A - B ) e. CC ) $=
      ( vx cc wcel wa cmin co cv caddc wceq crio subval sn-subeu ancoms riotacl
      wreu syl eqeltrd ) ADEZBDEZFZABGHBCIJHAKZCDLZDCABMUBUCCDQZUDDEUATUECBANOU
      CCDPRS $.
    $( $j usage 'sn-subcl' avoids 'ax-mulcom'; $)

    $d x z $.  $d y z $.
    $( ~ subf without ~ ax-mulcom .  (Contributed by SN, 5-May-2024.) $)
    sn-subf $p |- - : ( CC X. CC ) --> CC $=
      ( vy vz vx cv caddc co wceq cc crio wcel wral cxp cmin wf subval sn-subcl
      wa eqeltrrd rgen2 df-sub fmpo mpbi ) ADZBDEFCDZGBHIZHJZAHKCHKHHLHMNUFCAHH
      UDHJUCHJQUDUCMFUEHBUDUCOUDUCPRSCAHHUEHMCABTUAUB $.
    $( $j usage 'sn-subf' avoids 'ax-mulcom'; $)

    $( Equivalence between real subtraction and subtraction.  (Contributed by
       SN, 5-May-2024.) $)
    resubeqsub $p |- ( ( A e. RR /\ B e. RR ) -> ( A -R B ) = ( A - B ) ) $=
      ( vx cr wcel wa cv caddc co wceq crio cresub cmin wss wrex wreu ax-resscn
      cc recn syl2an resubeu reurex syl sn-subeu riotass ancoms resubval subval
      mp3an2i 3eqtr4d ) ADEZBDEZFBCGHIAJZCDKZUMCRKZABLIABMIZULUKUNUOJZDRNULUKFZ
      UMCDOZUMCRPZUQQURUMCDPUSCBAUAUMCDUBUCULBREZAREZUTUKBSZASZCBAUDTUMCDRUEUIU
      FCABUGUKVBVAUPUOJULVDVCCABUHTUJ $.

    $( Subtraction restricted to the reals.  (Contributed by SN,
       5-May-2024.) $)
    subresre $p |- -R = ( - |` ( RR X. RR ) ) $=
      ( vx vy cresub cmin cr cxp cres wceq wtru cc cv co resubeqsub 3adant1 wss
      wcel ax-resscn a1i wf resubf sn-subf oprres mptru ) CDEEFZGHIABEJCDJEAKZE
      PBKZEPUEUFCLUEUFDLHIUEUFMNEJOIQRUDECSITRJJFJDSIUARUBUC $.
  $}

  ${
    $d A x $.  $d B x $.
    addinvcom.a $e |- ( ph -> A e. CC ) $.
    addinvcom.b $e |- ( ph -> B e. CC ) $.
    addinvcom.1 $e |- ( ph -> ( A + B ) = 0 ) $.
    $( A number commutes with its additive inverse.  Compare ~ remulinvcom .
       (Contributed by SN, 5-May-2024.) $)
    addinvcom $p |- ( ph -> ( B + A ) = 0 ) $=
      ( vx caddc co cc0 wceq wa cc crio wreu wcel wb eqeq1d riota2 syl2anc wral
      cv wss wi wrex ssidd simpl rgenw a1i sn-negex12 syl 0cn sn-subeu riotass2
      sylancl syl22anc oveq2 mpbid eqtrd wrmo reurmo rmoimi 3syl sylanbrc oveq1
      reu5 anbi12d mpbird simprd ) ABCHIZJKZCBHIZJKZAVKVMLZBGUBZHIZJKZVOBHIZJKZ
      LZGMNZCKZAWAVQGMNZCAMMUCVTVQUDZGMUAZVTGMUEZVQGMOZWAWCKAMUFWEAWDGMVQVSUGZU
      HUIABMPZWFDBGUJUKZAWIJMPWGDULGBJUMUOZVTVQGMMUNUPAVKWCCKZFACMPZWGVKWLQEWKV
      QVKGMCVOCKZVPVJJVOCBHUQRZSTURUSAWMVTGMOZVNWBQEAWFVTGMUTZWPWJAWGVQGMUTWQWK
      VQGMVAVTVQGMWHVBVCVTGMVFVDVTVNGMCWNVQVKVSVMWOWNVRVLJVOCBHVERVGSTVHVI $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d ph x y $.
    remulinvcom.1 $e |- ( ph -> A e. RR ) $.
    remulinvcom.2 $e |- ( ph -> B e. RR ) $.
    remulinvcom.3 $e |- ( ph -> ( A x. B ) = 1 ) $.
    $( A left multiplicative inverse is a right multiplicative inverse.  Proven
       without ~ ax-mulcom .  (Contributed by SN, 5-Feb-2024.) $)
    remulinvcom $p |- ( ph -> ( B x. A ) = 1 ) $=
      ( vx vy cmul co c1 wceq cr wcel cc0 wa simpr oveq2d ad2antrr recnd cv wne
      ax-1ne0 a1i eqnetrd adantr remul01 eqtrd mteqand ax-rrecex syl2anc simprl
      wrex syl simprr simplrr remulcld simplrl mulassd oveq12d 1t1e1ALT 3eqtr3d
      oveq1d eqtrdi ax-1rid 3eqtr3rd eqtr4d remulcan2d mpbid mpdan rexlimddv )
      ACGUAZIJZKLZCBIJZKLZGMACMNZCOUBVNGMUMEACOBCIJZOAVRKOFKOUBZAUCUDUEACOLZPZV
      RBOIJZOWACOBIAVTQRWABMNZWBOLAWCVTDUFBUGUNUHUIGCUJUKAVLMNZVNPZPZVLHUAZIJZK
      LZVPHMWFWDVLOUBWIHMUMAWDVNULWFVLOVMOWFVMKOAWDVNUOZVSWFUCUDUEWFVLOLZPZVMCO
      IJZOWLVLOCIWFWKQRWLVQWMOLAVQWEWKESCUGUNUHUIHVLUJUKWFWGMNZWIPZPZBVLLZVPWPB
      WGIJZWHLWQWPWRKWHWPBVMIJZWGIJZBKIJZWGIJKWRWPWSXAWGIWPVMKBIAWDVNWOUPRVCWPV
      RVLIJZWGIJVRWHIJZWTKWPVRVLWGWPVRWPBCAWCWEWODSZAVQWEWOESZUQTWPVLAWDVNWOURZ
      TZWPWGWFWNWIULZTUSWPXBWSWGIWPBCVLWPBXDTWPCXETXGUSVCWPXCKKIJKWPVRKWHKIAVRK
      LWEWOFSWFWNWIUOZUTVAVDVBWPXABWGIWPWCXABLXDBVEUNVCVFXIVGWPBVLWGXDXFXHWPWGO
      WHOWPWHKOXIVSWPUCUDUEWPWGOLZPZWHVLOIJZOXKWGOVLIWPXJQRXKWDXLOLWPWDXJXFUFVL
      UGUNUHUIVHVIWPWQPZVOVMKXMBVLCIWPWQQRWFVNWOWQWJSUHVJVKVK $.
    $( $j usage 'remulinvcom' avoids 'ax-mulcom'; $)
  $}

  ${
    $d A x $.
    $( Commuted version of ~ ax-1rid without ~ ax-mulcom .  (Contributed by SN,
       5-Feb-2024.) $)
    remullid $p |- ( A e. RR -> ( 1 x. A ) = A ) $=
      ( vx cr wcel cc0 wceq c1 co wn wne df-ne wa ax-rrecex simpll recnd simprl
      cmul cv mulassd simprr oveq1d remulinvcom ax-1rid eqtrd 3eqtr3d rexlimddv
      oveq2d syl ex biimtrrid 1re remul01 mp1i oveq2 id 3eqtr4d pm2.61d2 ) ACDZ
      AEFZGAQHZAFZUSIAEJZURVAAEKURVBVAURVBLZABRZQHZGFZVABCBAMVCVDCDZVFLZLZVEAQH
      AVDAQHZQHZUTAVIAVDAVIAURVBVHNZOZVIVDVCVGVFPZOVMSVIVEGAQVCVGVFTZUAVIVKAGQH
      ZAVIVJGAQVIAVDVLVNVOUBUGVIURVPAFVLAUCUHUDUEUFUIUJUSGEQHZEUTAGCDVQEFUSUKGU
      LUMAEGQUNUSUOUPUQ $.
    $( $j usage 'remullid' avoids 'ax-mulcom'; $)
  $}

  $( Lemma for ~ sn-mullid and ~ sn-it1ei .  (Contributed by SN,
     27-May-2024.) $)
  sn-1ticom $p |- ( 1 x. _i ) = ( _i x. 1 ) $=
    ( ci cmul co ax-icn mulcli mulassi oveq2i 3eqtr4i eqtri rei4 oveq1i 3eqtr3i
    c1 ) AABCZNBCZABCZAOBCZMABCAMBCPNNABCZBCZQNNAAADDEZTDFNANBCZBCAAUABCZBCSQAA
    UADDANDTEFRUANBAAADDDFGOUBABAANDDTFGHIOMABJKOMABJGL $.

  ${
    $d A x y $.
    $( ~ mullid without ~ ax-mulcom .  (Contributed by SN, 27-May-2024.) $)
    sn-mullid $p |- ( A e. CC -> ( 1 x. A ) = A ) $=
      ( vx vy cc wcel cv ci cmul co caddc wceq cr wrex recn adantr a1i remullid
      c1 adantl mulassd cnre 1cnd ax-icn mulcld adddid sn-1ticom oveq1i oveq12d
      wa oveq2d 3eqtrd eqtr3d eqtrd oveq2 id eqeq12d syl5ibrcom rexlimivv syl )
      ADEABFZGCFZHIZJIZKZCLMBLMRAHIZAKZBCAUAVDVFBCLLUTLEZVALEZUIZVFVDRVCHIZVCKV
      IVJRUTHIZRVBHIZJIVCVIRUTVBVIUBZVGUTDEVHUTNOVIGVAGDEVIUCPZVHVADEVGVANSZUDU
      EVIVKUTVLVBJVGVKUTKVHUTQOVIRGHIZVAHIZVLVBVIRGVAVMVNVOTVIVQGRHIZVAHIZGRVAH
      IZHIVBVQVSKVIVPVRVAHUFUGPVIGRVAVNVMVOTVIVTVAGHVHVTVAKVGVAQSUJUKULUHUMVDVE
      VJAVCAVCRHUNVDUOUPUQURUS $.
    $( $j usage 'sn-mullid' avoids 'ax-mulcom'; $)
  $}

  $( ~ it1ei without ~ ax-mulcom .  (See ~ sn-mullid for commuted version).
     (Contributed by SN, 1-Jun-2024.) $)
  sn-it1ei $p |- ( _i x. 1 ) = _i $=
    ( c1 ci cmul co sn-1ticom cc wcel wceq ax-icn sn-mullid ax-mp eqtr3i ) ABCD
    ZBACDBEBFGMBHIBJKL $.
  $( $j usage 'sn-it1ei' avoids 'ax-mulcom'; $)

  $( The multiplicative inverse of ` _i ` (per ~ i4 ) is also its additive
     inverse.  (Contributed by SN, 30-Jun-2024.) $)
  ipiiie0 $p |- ( _i + ( _i x. ( _i x. _i ) ) ) = 0 $=
    ( ci cmul co caddc c1 cc0 cresub sn-it1ei eqcomi reixi oveq2i ax-icn ax-1cn
    oveq12i cr wcel 1re rernegcl ax-mp recni adddii wceq renegid sn-it0e0 eqtri
    3eqtr2i ) AAAABCZBCZDCAEBCZAFEGCZBCZDCAEUJDCZBCZFAUIUHUKDUIAHIUGUJABJKNAEUJ
    LMUJEOPZUJOPQERSTUAUMAFBCFULFABUNULFUBQEUCSKUDUEUF $.

  ${
    $d A x $.  $d B x $.  $d C x $.  $d ph x $.
    remulcand.1 $e |- ( ph -> A e. RR ) $.
    remulcand.2 $e |- ( ph -> B e. RR ) $.
    remulcand.3 $e |- ( ph -> C e. RR ) $.
    remulcand.4 $e |- ( ph -> C =/= 0 ) $.
    $( Commuted version of ~ remulcan2d without ~ ax-mulcom .  (Contributed by
       SN, 21-Feb-2024.) $)
    remulcand $p |- ( ph -> ( ( C x. A ) = ( C x. B ) <-> A = B ) ) $=
      ( vx cmul co wceq c1 cr wcel wa adantr recnd syl 3eqtr3d cv cc0 ax-rrecex
      wi wne wrex syl2anc simplr simpr remulinvcom ex w3a oveq2 3ad2ant3 oveq1d
      simp2 simp1r 3ad2ant1 simp1l mulassd remullid 3exp syld rexlimddv impbid1
      impr ) ADBJKZDCJKZLZBCLZADIUAZJKMLZVIVJUDZINADNOZDUBUEVLINUFGHIDUCUGAVKNO
      ZVLVMAVOPZVLVKDJKZMLZVMVPVLVRVPVLPDVKVPVNVLAVNVOGQZQAVOVLUHVPVLUIUJUKVPVR
      VIVJVPVRVIULZVKVGJKZVKVHJKZBCVIVPWAWBLVRVGVHVKJUMUNVTVQBJKMBJKZWABVTVQMBJ
      VPVRVIUPZUOVTVKDBVTVKAVOVRVIUQRZVTDVPVRVNVIVSURRZVTBVTABNOZAVOVRVIUSZESZR
      UTVTWGWCBLWIBVASTVTVQCJKMCJKZWBCVTVQMCJWDUOVTVKDCWEWFVTCVTACNOZWHFSZRUTVT
      WKWJCLWLCVASTTVBVCVFVDBCDJUMVE $.
    $( $j usage 'remulcand' avoids 'ax-mulcom'; $)
  $}

  $c /R $.

  $( Real number division. $)
  crediv $a class /R $.

  ${
    $d x y z $.
    $( Define division between real numbers.  This operator saves ~ ax-mulcom
       over ~ df-div in certain situations.  (Contributed by SN,
       25-Nov-2025.) $)
    df-rediv $a |- /R = ( x e. RR , y e. ( RR \ { 0 } ) |->
                       ( iota_ z e. RR ( y x. z ) = x ) ) $.
  $}

  ${
    $d A x y z $.  $d B x y z $.
    redivvald.a $e |- ( ph -> A e. RR ) $.
    redivvald.b $e |- ( ph -> B e. RR ) $.
    redivvald.z $e |- ( ph -> B =/= 0 ) $.
    $( Value of real division, which is the (unique) real ` x ` such that
       ` ( B x. x ) = A ` .  (Contributed by SN, 25-Nov-2025.) $)
    redivvald $p |- ( ph -> ( A /R B ) = ( iota_ x e. RR ( B x. x ) = A ) ) $=
      ( vz vy cr wcel cc0 csn crediv co cv cmul wceq crio riotabidv eqeq2 oveq1
      cdif eldifsnd eqeq1d df-rediv riotaex ovmpo syl2anc ) ACJKDJLMUCZKCDNODBP
      ZQOZCRZBJSZREADJLFGUDHICDJUJIPZUKQOZHPZRZBJSUNNUPCRZBJSUQCRURUSBJUQCUPUAT
      UODRZUSUMBJUTUPULCUODUKQUBUETHIBUFUMBJUGUHUI $.

    $d ph x y $.
    $( Existential uniqueness of real quotients.  (Contributed by SN,
       25-Nov-2025.) $)
    rediveud $p |- ( ph -> E! x e. RR ( B x. x ) = A ) $=
      ( vy cv cmul co wceq cr wrex wa wral c1 wcel adantr recnd weq wi wreu cc0
      wne ax-rrecex syl2anc oveq2 eqeq1d simprl remulcld simprr oveq1d remullid
      cc mulassd syl 3eqtr3d rspcedvdw rexlimddv eqtr3 imbitrid ralrimivva reu4
      remulcand sylanbrc ) ADBIZJKZCLZBMNZVIDHIZJKZCLZOZBHUAZUBZHMPBMPVIBMUCAVL
      QLZVJHMADMRZDUDUEZVQHMNFGHDUFUGAVKMRZVQOZOZVIDVKCJKZJKZCLBWCMVGWCLVHWDCVG
      WCDJUHUIWBVKCAVTVQUJZACMRZWAESUKWBVLCJKQCJKZWDCWBVLQCJAVTVQULUMWBDVKCADUO
      RWAADFTSWBVKWETACUORWAACETSUPAWGCLZWAAWFWHECUNUQSURUSUTAVPBHMMVNVHVLLAVGM
      RZVTOZOZVOVHVLCVAWKVGVKDAWIVTUJAWIVTULAVRWJFSAVSWJGSVEVBVCVIVMBHMVOVHVLCV
      GVKDJUHUIVDVF $.

    $( Closure law for real division.  (Contributed by SN, 25-Nov-2025.) $)
    sn-redivcld $p |- ( ph -> ( A /R B ) e. RR ) $=
      ( vx crediv co cv cmul wceq crio redivvald wreu wcel rediveud riotacl syl
      cr eqeltrd ) ABCHICGJKIBLZGTMZTAGBCDEFNAUBGTOUCTPAGBCDEFQUBGTRSUA $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d ph x $.
    redivmuld.a $e |- ( ph -> A e. RR ) $.
    redivmuld.b $e |- ( ph -> B e. RR ) $.
    redivmuld.c $e |- ( ph -> C e. RR ) $.
    redivmuld.z $e |- ( ph -> C =/= 0 ) $.
    $( Relationship between division and multiplication.  (Contributed by SN,
       25-Nov-2025.) $)
    redivmuld $p |- ( ph -> ( ( A /R C ) = B <-> ( C x. B ) = A ) ) $=
      ( vx crediv co wceq cv cmul cr crio redivvald eqeq1d wcel wreu wb syl2anc
      rediveud oveq2 riota2 bitr4d ) ABDJKZCLDIMZNKZBLZIOPZCLZDCNKZBLZAUGUKCAIB
      DEGHQRACOSUJIOTUNULUAFAIBDEGHUCUJUNIOCUHCLUIUMBUHCDNUDRUEUBUF $.

    $( Relationship between division and multiplication.  (Contributed by SN,
       2-Apr-2026.) $)
    redivmul2d $p |- ( ph -> ( ( A /R C ) = B <-> A = ( C x. B ) ) ) $=
      ( crediv co wceq cmul redivmuld eqcom bitrdi ) ABDIJCKDCLJZBKBPKABCDEFGHM
      PBNO $.
  $}

  ${
    redivcan2d.a $e |- ( ph -> A e. RR ) $.
    redivcan2d.b $e |- ( ph -> B e. RR ) $.
    redivcan2d.z $e |- ( ph -> B =/= 0 ) $.
    $( A cancellation law for division.  (Contributed by SN, 25-Nov-2025.) $)
    redivcan2d $p |- ( ph -> ( B x. ( A /R B ) ) = A ) $=
      ( crediv co wceq cmul eqidd sn-redivcld redivmuld mpbid ) ABCGHZOICOJHBIA
      OKABOCDABCDEFLEFMN $.

    $( A cancellation law for division.  (Contributed by SN, 25-Nov-2025.) $)
    redivcan3d $p |- ( ph -> ( ( B x. A ) /R B ) = A ) $=
      ( cmul co crediv wceq eqidd remulcld redivmuld mpbird ) ACBGHZCIHBJOOJAOK
      AOBCACBEDLDEFMN $.

    $( A ratio is zero iff the numerator is zero.  (Contributed by SN,
       25-Nov-2025.) $)
    rediveq0d $p |- ( ph -> ( ( A /R B ) = 0 <-> A = 0 ) ) $=
      ( crediv co cc0 wceq cmul 0red redivmul2d wcel remul01 syl eqeq2d bitrd
      cr ) ABCGHIJBCIKHZJBIJABICDALEFMATIBACSNTIJECOPQR $.

    $( The ratio of nonzero numbers is nonzero.  (Contributed by SN,
       2-Apr-2026.) $)
    redivne0bd $p |- ( ph -> ( A =/= 0 <-> ( A /R B ) =/= 0 ) ) $=
      ( cc0 crediv co wceq rediveq0d bicomd necon3bid ) ABGBCHIZGANGJBGJABCDEFK
      LM $.

    $( Equality in terms of unit ratio.  (Contributed by SN, 2-Apr-2026.) $)
    rediveq1d $p |- ( ph -> ( ( A /R B ) = 1 <-> A = B ) ) $=
      ( crediv co c1 wceq cmul 1red redivmul2d cr wcel ax-1rid syl eqeq2d bitrd
      ) ABCGHIJBCIKHZJBCJABICDALEFMATCBACNOTCJECPQRS $.
  $}

  ${
    sn-rediv1d.a $e |- ( ph -> A e. RR ) $.
    $( A number divided by 1 is itself.  (Contributed by SN, 2-Apr-2026.) $)
    sn-rediv1d $p |- ( ph -> ( A /R 1 ) = A ) $=
      ( c1 crediv co wceq cmul wcel remullid syl 1red cc0 wne ax-1ne0 redivmuld
      cr a1i mpbird ) ABDEFBGDBHFBGZABQITCBJKABBDCCALDMNAORPS $.
  $}

  ${
    sn-rediv0d.a $e |- ( ph -> A e. RR ) $.
    sn-rediv0d.z $e |- ( ph -> A =/= 0 ) $.
    $( Division into zero is zero.  (Contributed by SN, 2-Apr-2026.) $)
    sn-rediv0d $p |- ( ph -> ( 0 /R A ) = 0 ) $=
      ( cc0 crediv co wceq eqidd 0red rediveq0d mpbird ) AEBFGEHEEHAEIAEBAJCDKL
      $.

    $( A number divided by itself is 1.  (Contributed by SN, 2-Apr-2026.) $)
    sn-redividd $p |- ( ph -> ( A /R A ) = 1 ) $=
      ( crediv co c1 wceq eqidd rediveq1d mpbird ) ABBEFGHBBHABIABBCCDJK $.
  $}

  ${
    sn-rereccld.a $e |- ( ph -> A e. RR ) $.
    sn-rereccld.z $e |- ( ph -> A =/= 0 ) $.
    $( Closure law for reciprocal.  (Contributed by SN, 25-Nov-2025.) $)
    sn-rereccld $p |- ( ph -> ( 1 /R A ) e. RR ) $=
      ( c1 1red sn-redivcld ) AEBAFCDG $.

    $( The reciprocal of a nonzero number is nonzero.  (Contributed by SN,
       4-Apr-2026.) $)
    rerecne0d $p |- ( ph -> ( 1 /R A ) =/= 0 ) $=
      ( c1 cc0 wne crediv co ax-1ne0 1red redivne0bd mpbii ) AEFGEBHIFGJAEBAKCD
      LM $.

    $( Multiplication of a number and its reciprocal.  (Contributed by SN,
       25-Nov-2025.) $)
    rerecidd $p |- ( ph -> ( A x. ( 1 /R A ) ) = 1 ) $=
      ( c1 1red redivcan2d ) AEBAFCDG $.

    $( Multiplication of a number and its reciprocal.  (Contributed by SN,
       25-Nov-2025.) $)
    rerecid2d $p |- ( ph -> ( ( 1 /R A ) x. A ) = 1 ) $=
      ( c1 crediv co sn-rereccld rerecidd remulinvcom ) ABEBFGCABCDHABCDIJ $.
    $( $j usage 'rerecid2d' avoids 'ax-mulcom'; $)

    $( A number is equal to the reciprocal of its reciprocal.  (Contributed by
       SN, 2-Apr-2026.) $)
    rerecrecd $p |- ( ph -> ( 1 /R ( 1 /R A ) ) = A ) $=
      ( c1 crediv co wceq cmul rerecid2d sn-rereccld rerecne0d redivmuld mpbird
      1red ) AEEBFGZFGBHPBIGEHABCDJAEBPAOCABCDKABCDLMN $.
  $}

  ${
    redivrec2d.a $e |- ( ph -> A e. RR ) $.
    redivrec2d.b $e |- ( ph -> B e. RR ) $.
    redivrec2d.z $e |- ( ph -> B =/= 0 ) $.
    $( Relationship between division and reciprocal.  (Contributed by SN,
       9-Apr-2026.) $)
    redivrec2d $p |- ( ph -> ( A /R B ) = ( ( 1 /R B ) x. A ) ) $=
      ( crediv co c1 cmul rerecidd oveq1d recnd sn-rereccld mulassd cr remullid
      wceq wcel syl 3eqtr3d remulcld redivmuld mpbird ) ABCGHICGHZBJHZRCUFJHZBR
      ACUEJHZBJHIBJHZUGBAUHIBJACEFKLACUEBACEMAUEACEFNZMABDMOABPSUIBRDBQTUAABUFC
      DAUEBUJDUBEFUCUD $.
  $}

  ${
    rediv23d.a $e |- ( ph -> A e. RR ) $.
    rediv23d.b $e |- ( ph -> B e. RR ) $.
    rediv23d.c $e |- ( ph -> C e. RR ) $.
    rediv23d.z $e |- ( ph -> C =/= 0 ) $.
    $( A "commutative"/associative law for division.  (Contributed by SN,
       9-Apr-2026.) $)
    rediv23d $p |- ( ph -> ( ( A x. B ) /R C ) = ( ( A /R C ) x. B ) ) $=
      ( c1 crediv co cmul sn-rereccld recnd redivrec2d oveq1d remulcld 3eqtr4rd
      mulassd ) AIDJKZBLKZCLKTBCLKZLKBDJKZCLKUBDJKATBCATADGHMNABENACFNSAUCUACLA
      BDEGHOPAUBDABCEFQGHOR $.
    $( $j usage 'rediv23d' avoids 'ax-mulcom'; $)

    $( Distribution of division over addition.  (Contributed by SN,
       9-Apr-2026.) $)
    redivdird $p |-
      ( ph -> ( ( A + B ) /R C ) = ( ( A /R C ) + ( B /R C ) ) ) $=
      ( caddc co crediv wceq cmul recnd sn-redivcld redivcan2d oveq12d readdcld
      adddid eqtrd redivmuld mpbird ) ABCIJZDKJBDKJZCDKJZIJZLDUFMJZUCLAUGDUDMJZ
      DUEMJZIJUCADUDUEADGNAUDABDEGHOZNAUEACDFGHOZNSAUHBUICIABDEGHPACDFGHPQTAUCU
      FDABCEFRAUDUEUJUKRGHUAUB $.

    $( One-to-one relationship for division.  (Contributed by SN,
       9-Apr-2026.) $)
    rediv11d $p |- ( ph -> ( ( A /R C ) = ( B /R C ) <-> A = B ) ) $=
      ( crediv co wceq cmul sn-redivcld redivmul2d redivcan2d eqeq2d bitrd ) AB
      DIJCDIJZKBDRLJZKBCKABRDEACDFGHMGHNASCBACDFGHOPQ $.
  $}

  ${
    $d a b x y $.
    $( Lemma for ~ sn-mul02 .  Commuted version of ~ sn-it0e0 .  (Contributed
       by SN, 30-Jun-2024.) $)
    sn-0tie0 $p |- ( 0 x. _i ) = 0 $=
      ( cc0 ci cmul co wcel caddc wceq cr ax-icn wa syl a1i recnd eqtrdi oveq2d
      c1 eqtrd oveq1d mulassd ax-1cn va vb vx vy vz wrex 0cn mulcli cnre simplr
      cc cv wn cresub wne neqne adantl simplll rernegcl 1red readdcld ax-rrecex
      sylan 1cnd adddid sn-it1ei oveq2i 0cnd renegid2 ad3antrrr simpllr addassd
      mulcld sn-addlid 3eqtr3d sn-mul01 eqtr3d oveq12d reixi 1re ax-mp remulcld
      eqeltri eqeltrrd remul02 ad2antrr addcld simprl rexlimddv necon1d renegid
      simprr ex mpd readdlid readdrid 0re oveq1i mulassi eqtr3i 3eqtr4d ax-1rid
      3eqtr3rd mp1i eqeq2i oveq2 eqtri rei4 oveq12i 3eqtr3g readdcli c2 sn-0ne2
      adddii df-2 necomi eqnetrri mp2an addcli addassi ipiiie0 3eqtr2i remullid
      simpl eqtrid simpr 1t1e1ALT rexlimdvaa mpi mpdan sylbi pm2.18da rexlimivv
      adantr mp2b ) ABCDZUKEZYPUAULZBUBULZCDZFDZGZUBHUFUAHUFYPAGZABUGIUHZUAUBYP
      UIUUBUUCUAUBHHYRHEZYSHEZJZUUBUUCUUGUUBJZUUCUUHUUCUMZJZYPPBPCDZFDZGZUUCUUJ
      YPUUAUULUUGUUBUUIUJZUUJYRPYTUUKFUUJYRAYRUNDZPFDZFDZYRAFDZPYRUUJUUPAYRFUUJ
      YPAUOZUUPAGUUIUUSUUHYPAUPUQZUUJUUPAYPAUUJUUPAUOZUUCUUJUVAJZUUPUCULZCDZPGZ
      UUCUCHUUJUUPHEUVAUVEUCHUFUUJUUOPUUJUUEUUOHEZUUEUUFUUBUUIURZYRUSKZUUJUTZVA
      UCUUPVBVCUVBUVCHEZUVEJZJZABUUPCDZCDZUVCCDZAUVCCDZYPAUVLUVNAUVCCUUJUVNAGUV
      AUVKUUJUVNABUUOCDZCDZYPFDZAUUJUVNAUVQBFDZCDUVSUUJUVMUVTACUUJUVMUVQUUKFDUV
      TUUJBUUOPBUKEZUUJILZUUJUUOUVHMZUUJVDZVEUUKBUVQFVFVGNOUUJAUVQBUUJVHZUUJBUU
      OUWBUWCVMUWBVEQUUJYPUUOYPFDZCDZYPYTCDZUVSAUUJUWFYTYPCUUJUWFUUOUUAFDZYTUUJ
      YPUUAUUOFUUNOUUJUUOYRFDZYTFDAYTFDZUWIYTUUJUWJAYTFUUEUWJAGUUFUUBUUIYRVIVJR
      UUJUUOYRYTUWCUUJYRUVGMZUUJBYSUWBUUJYSUUEUUFUUBUUIVKZMZVMZVLUUJYTUKEUWKYTG
      UWOYTVNKVOQOUUJUWGYPUUOCDZYPYPCDZFDUVSUUJYPUUOYPYQUUJUUDLZUWCUWRVEUUJUWPU
      VRUWQYPFUUJABUUOUWEUWBUWCSUUJYPACDZBCDUWQYPUUJYPABUWRUWEUWBSUUJUWSABCUUJY
      QUWSAGUWRYPVPKRVQVRQUUJUWHABYTCDZCDZAUUJABYTUWEUWBUWOSUUJUWTHEUXAAGUUJBBC
      DZYSCDUWTHUUJBBYSUWBUWBUWNSUUJUXBYSUXBHEUUJUXBAPUNDZHVSPHEZUXCHEVTPUSWAWC
      LUWMWBWDUWTWEKQVOQWFRUVLUVOAUVMUVCCDZCDYPUVLAUVMUVCUVLVHUVLBUUPUWAUVLILZU
      VLUUOPUVLUUOUUJUVFUVAUVKUVHWFMUVLVDWGZVMUVLUVCUVBUVJUVEWHZMZSUVLUXEBACUVL
      UXEBUVDCDZBUVLBUUPUVCUXFUXGUXISUVLUXJUUKBUVLUVDPBCUVBUVJUVEWLOVFNQOQUVLUV
      JUVPAGUXHUVCWEKVOWIWMWJWNOUUJYRUUOFDZPFDZUUQPUUJYRUUOPUWLUWCUWDVLUUJUXLAP
      FDZPUUJUXKAPFUUJUUEUXKAGUVGYRWKKRUXDUXMPGVTPWOWAZNVQUUJUUEUURYRGUVGYRWPKX
      CZUUJYSPBCUUJPAYSUNDZFDZYSFDZAYSFDZPYSUUJUXQAYSFUUJUUSUXQAGUUTUUJUXQAYPAU
      UJUXQAUOZUUCUUJUXTJZUXQUDULZCDZPGZUUCUDHUUJUXQHEUXTUYDUDHUFUUJPUXPUVIUUJU
      UFUXPHEUWMYSUSKZVAUDUXQVBVCUYAUYBHEZUYDJZJZABUXQCDZCDZUYBCDZAUYBCDZYPAUYH
      UYJAUYBCUUJUYJAGUXTUYGUUJUYJAPCDZAUUJUYJAYPBUXPCDZFDZCDZUYMUUJABUYNFDZCDZ
      AYPCDZAUYNCDZFDZUYJUYPUUJUYRYPUYTFDVUAUUJABUYNUWEUWBUUJBUXPUWBUUJUXPUYEMZ
      VMZVEUUJYPUYSUYTFYPUYSGUUJAACDZBCDZYPUYSVUDABCAHEZVUDAGWQAWEWAWRZAABUGUGI
      WSZWTLRQUUJUYIUYQACUUJUYIUUKUYNFDUYQUUJBPUXPUWBUWDVUBVEUUJUUKBUYNFUUKBGUU
      JVFLRQOUUJAYPUYNUWEUWRVUCVEXAUUJUYOPACUUJUYOPYTFDZUYNFDZPUUJYPVUIUYNFUUJY
      PUUAVUIUUNUUJYRPYTFUXORQRUUJVUJPYTUYNFDZFDZPUUJPYTUYNUWDUWOVUCVLUUJVULPAF
      DZPUUJVUKAPFUUJBYSUXPFDZCDBACDZVUKAUUJVUNABCUUJUUFVUNAGUWMYSWKKOUUJBYSUXP
      UWBUWNVUBVEUWAVUOAGUUJIBVPXDVOOUXDVUMPGVTPWPWAZNQQOQVUFUYMAGWQAXBWAZNWFRU
      YHUYKAUYIUYBCDZCDYPUYHAUYIUYBUYHVHUYHBUXQUWAUYHILZUYHPUXPUYHVDUUJUXPUKEUX
      TUYGVUBWFWGZVMUYHUYBUYAUYFUYDWHZMZSUYHVURBACUYHVURBUYCCDZBUYHBUXQUYBVUSVU
      TVVBSUYHVVCUUKBUYHUYCPBCUYAUYFUYDWLOVFNQOQUYHUYFUYLAGVVAUYBWEKVOWIWMWJWNR
      UUJUXRPUXPYSFDZFDZPUUJPUXPYSUWDVUBUWNVLUUJVVEVUMPUUJVVDAPFUUJUUFVVDAGUWMY
      SVIKOVUPNQUUJUUFUXSYSGUWMYSWOKXCOVRQUUMYPPGZUUCUUMYPPBFDZGZVVFUULVVGYPUUK
      BPFVFVGXEVVHYPUXBBCDZPFDZGZVVFVVHVVIYPCDZVVIVVGCDZYPVVJYPVVGVVICXFVVIACDZ
      BCDVVLYPVVIABUXBBBBIIUHZIUHZUGIWSVVNABCVVIUKEVVNAGVVPVVIVPWAWRWTVVMVVIPCD
      ZVVIBCDZFDVVJVVIPBVVPTIXNVVQVVIVVRPFVVQUXBUUKCDVVIUXBBPVVOITWSUUKBUXBCVFV
      GXGVVRUXBUXBCDPUXBBBVVOIIWSXHXGXIXGXJVVHVVKJZPPFDZUEULZCDZPGZUEHUFZVVFVVT
      HEZVVTAUOVWDPPVTVTXKZXLVVTAXOAXLXMXPXQUEVVTVBXRVVSVWCVVFUEHVVSVWAHEZVWCJZ
      JZYPVVTCDZVWACDZPVVTCDZVWACDZYPPVVSVWKVWMGVWHVVSVWJVWLVWACVVSVVGVVJFDZVVT
      VWJVWLVWNVVTGVVSVWNPBVVJFDZFDPBVVIFDZPFDZFDVVTPBVVJTIVVIPVVPTXSXTVWQVWOPF
      BVVIPIVVPTXTVGVWQPPFVWQUXMPVWPAPFVWPBBUXBCDZFDAVVIVWRBFBBBIIIWSVGYAXGWRUX
      NXGVGYBLVVSVWJYPPCDZVWSFDVWNYPPPUUDTTXNVVSVWSVVGVWSVVJFVVSVWSYPVVGVWSAUUK
      CDYPABPUGITWSUUKBACVFVGXGZVVHVVKYDYEVVSVWSYPVVJVWTVVHVVKYFYEVRYEVWEVWLVVT
      GVVSVWFVVTYCXDXARYNVWIVWKYPVWBCDZYPVWIYPVVTVWAYQVWIUUDLVWIPPVWIVDZVXBWGZV
      WIVWAVVSVWGVWCWHMZSVWIVXAVWSYPVWIVWBPYPCVVSVWGVWCWLZOVWTNQVWIVWMPVWBCDZPV
      WIPVVTVWAVXBVXCVXDSVWIVXFPPCDPVWIVWBPPCVXEOYGNQVOYHYIYJYKVVFUYSUYMYPAYPPA
      CXFVUEUYSYPVUHVUGWTVUQXJKKYLWMYMYO $.
  $}

  ${
    $d A x y $.
    $( ~ mul02 without ~ ax-mulcom .  See
       ~ https://github.com/icecream17/Stuff/blob/main/math/0A%3D0.md for an
       outline.  (Contributed by SN, 30-Jun-2024.) $)
    sn-mul02 $p |- ( A e. CC -> ( 0 x. A ) = 0 ) $=
      ( vx vy cc wcel cv ci cmul co caddc wceq wrex cc0 cnre recn adantr adantl
      cr wa remul02 0cnd ax-icn mulcld sn-0tie0 mulassd 3eqtr3a oveq12d sn-00id
      a1i adddid oveq1i eqtrdi eqtrd oveq2 eqeq1d syl5ibrcom rexlimivv syl ) AD
      EABFZGCFZHIZJIZKZCRLBRLMAHIZMKZBCANVCVEBCRRUSREZUTREZSZVEVCMVBHIZMKVHVIMU
      SHIZMVAHIZJIZMVHMUSVAVHUAZVFUSDEVGUSOPVHGUTGDEVHUBUIZVGUTDEVFUTOQZUCUJVHV
      LMMJIMVHVJMVKMJVFVJMKVGUSTPVHMGHIZUTHIMUTHIZVKMVPMUTHUDUKVHMGUTVMVNVOUEVG
      VQMKVFUTTQUFUGUHULUMVCVDVIMAVBMHUNUOUPUQUR $.
    $( $j usage 'sn-mul02' avoids 'ax-mulcom'; $)
  $}

  $( ~ ltaddpos without ~ ax-mulcom .  (Contributed by SN, 13-Feb-2024.) $)
  sn-ltaddpos $p |-
                   ( ( A e. RR /\ B e. RR ) -> ( 0 < A <-> B < ( B + A ) ) ) $=
    ( cr wcel wa cc0 clt wbr caddc co wb 0re ltadd2 mp3an1 wceq readdrid adantl
    breq1d bitrd ) ACDZBCDZEZFAGHZBFIJZBAIJZGHZBUEGHFCDTUAUCUFKLFABMNUBUDBUEGUA
    UDBOTBPQRS $.
  $( $j usage 'sn-ltaddpos' avoids 'ax-mulcom'; $)

  $( ~ ltaddneg without ~ ax-mulcom .  (Contributed by SN, 25-Jan-2025.) $)
  sn-ltaddneg $p |-
                   ( ( A e. RR /\ B e. RR ) -> ( A < 0 <-> ( B + A ) < B ) ) $=
    ( cr wcel wa cc0 clt wbr caddc co wb 0re ltadd2 mp3an2 wceq readdrid adantl
    breq2d bitrd ) ACDZBCDZEZAFGHZBAIJZBFIJZGHZUDBGHTFCDUAUCUFKLAFBMNUBUEBUDGUA
    UEBOTBPQRS $.
  $( $j usage 'sn-ltaddneg' avoids 'ax-mulcom'; $)

  $( Comparison of two numbers whose difference is positive.  Compare
     ~ posdif .  (Contributed by SN, 13-Feb-2024.) $)
  reposdif $p |- ( ( A e. RR /\ B e. RR ) -> ( A < B <-> 0 < ( B -R A ) ) ) $=
    ( cr wcel wa clt wbr cresub co cc0 wb reltsub1 3anidm13 wceq resubid adantr
    breq1d bitrd ) ACDZBCDZEZABFGZAAHIZBAHIZFGZJUDFGSTUBUEKABALMUAUCJUDFSUCJNTA
    OPQR $.

  $( Comparison of a real and its negative to zero.  Compare ~ lt0neg1 .
     (Contributed by SN, 13-Feb-2024.) $)
  relt0neg1 $p |- ( A e. RR -> ( A < 0 <-> 0 < ( 0 -R A ) ) ) $=
    ( cr wcel cc0 clt wbr cresub co wb 0re reposdif mpan2 ) ABCDBCADEFDDAGHEFIJ
    ADKL $.

  $( Comparison of a real and its negative to zero.  Compare ~ lt0neg2 .
     (Contributed by SN, 13-Feb-2024.) $)
  relt0neg2 $p |- ( A e. RR -> ( 0 < A <-> ( 0 -R A ) < 0 ) ) $=
    ( cr wcel cc0 clt wbr cresub co wb elre0re id reltsub1 syl3anc breq2d bitrd
    resubid ) ABCZDAEFZDAGHZAAGHZEFZSDEFQDBCQQRUAIAJQKZUBDAALMQTDSEAPNO $.

  ${
    sn-addlt0d.a $e |- ( ph -> A e. RR ) $.
    sn-addlt0d.b $e |- ( ph -> B e. RR ) $.
    sn-addlt0d.1 $e |- ( ph -> A < 0 ) $.
    sn-addlt0d.2 $e |- ( ph -> B < 0 ) $.
    $( The sum of negative numbers is negative.  (Contributed by SN,
       25-Jan-2025.) $)
    sn-addlt0d $p |- ( ph -> ( A + B ) < 0 ) $=
      ( caddc co cc0 readdcld 0red clt wbr cr wcel wb sn-ltaddneg syl2anc mpbid
      lttrd ) ABCHIZBJABCDEKDALACJMNZUBBMNZGACOPBOPUCUDQEDCBRSTFUA $.
    $( $j usage 'sn-addlt0d' avoids 'ax-mulcom'; $)
  $}

  ${
    sn-addgt0d.a $e |- ( ph -> A e. RR ) $.
    sn-addgt0d.b $e |- ( ph -> B e. RR ) $.
    sn-addgt0d.1 $e |- ( ph -> 0 < A ) $.
    sn-addgt0d.2 $e |- ( ph -> 0 < B ) $.
    $( The sum of positive numbers is positive.  Proof of ~ addgt0d without
       ~ ax-mulcom .  (Contributed by SN, 25-Jan-2025.) $)
    sn-addgt0d $p |- ( ph -> 0 < ( A + B ) ) $=
      ( cc0 caddc co 0red readdcld clt wbr cr wcel wb sn-ltaddpos syl2anc mpbid
      lttrd ) AHBBCIJZAKDABCDELFAHCMNZBUBMNZGACOPBOPUCUDQEDCBRSTUA $.
    $( $j usage 'sn-addgt0d' avoids 'ax-mulcom'; $)
  $}

  ${
    $d A x y $.
    $( ~ nnne0 without ~ ax-mulcom .  (Contributed by SN, 25-Jan-2025.) $)
    sn-nnne0 $p |- ( A e. NN -> A =/= 0 ) $=
      ( vx vy cn wcel cc0 c1 clt wbr wne wa cv breq2 ad2antlr 1red simpr simpll
      id nnindd breq1 wo 0ne1 0re lttri2i mpbi caddc co nnre sn-addgt0d gt0ne0d
      1re cr ancoms sn-addlt0d lt0ne0d jaodan mpan2 ) ADEZFGHIZGFHIZUAZAFJZFGJV
      AUBFGUCUKUDUEURUSVBUTUSURVBUSURKAUSFBLZHIUSFCLZHIZFVDGUFUGZHIFAHIBCAVCGFH
      MVCVDFHMVCVFFHMVCAFHMUSRUSVDDEZKZVEKZVDGVGVDULEZUSVEVDUHZNVIOVHVEPUSVGVEQ
      UISUJUMUTURVBUTURKAUTVCFHIUTVDFHIZVFFHIAFHIBCAVCGFHTVCVDFHTVCVFFHTVCAFHTU
      TRUTVGKZVLKZVDGVGVJUTVLVKNVNOVMVLPUTVGVLQUNSUOUMUPUQ $.
    $( $j usage 'sn-nnne0' avoids 'ax-mulcom'; $)
  $}

  $( ~ elznn0nn restated using ~ df-resub .  (Contributed by SN,
     25-Jan-2025.) $)
  reelznn0nn $p |-
    ( N e. ZZ <-> ( N e. NN0 \/ ( N e. RR /\ ( 0 -R N ) e. NN ) ) ) $=
    ( cz wcel cn0 cr cneg cn wa cc0 cresub elznn0nn cmin df-neg wceq resubeqsub
    wo co 0re mpan eqtr4id eleq1d pm5.32i orbi2i bitri ) ABCADCZAECZAFZGCZHZPUE
    UFIAJQZGCZHZPAKUIULUEUFUHUKUFUGUJGUFUGIALQZUJAMIECUFUJUMNRIAOSTUAUBUCUD $.

  $( Addition is commutative for nonnegative integers.  Proven without
     ~ ax-mulcom .  (Contributed by SN, 1-Feb-2025.) $)
  nn0addcom $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A + B ) = ( B + A ) ) $=
    ( cn0 wcel cn cc0 wceq wo caddc co elnn0 readdlid readdrid eqtr4d syl oveq1
    cr oveq2 eqeq12d syl5ibrcom nnaddcom nnre impcom jaoian sylanb nn0re jaodan
    imp sylan2b ) BCDACDZBEDZBFGZHABIJZBAIJZGZBKUJUKUOULUJAEDZAFGZHUKUOAKUPUKUO
    UQABUAUKUQUOUKUOUQFBIJZBFIJZGZUKBQDZUTBUBVAURBUSBLBMNOUQUMURUNUSAFBIPAFBIRS
    TUCUDUEUJULUOUJUOULAFIJZFAIJZGZUJAQDZVDAUFVEVBAVCAMALNOULUMVBUNVCBFAIRBFAIP
    STUHUGUI $.
  $( $j usage 'nn0addcom' avoids 'ax-mulcom'; $)

  $( Lemma for ~ zaddcom .  (Contributed by SN, 1-Feb-2025.) $)
  zaddcomlem $p |- ( ( ( A e. RR /\ ( 0 -R A ) e. NN ) /\ B e. NN0 ) ->
                     ( A + B ) = ( B + A ) ) $=
    ( cr wcel cc0 cresub co cn wa cn0 caddc simpr nn0cnd ad2antrr recnd addassd
    wceq syl oveq1d addcld rernegcl simpll renegid2 oveq2d nn0re adantl 3eqtrrd
    readdrid readdlid sylan9eq nnnn0 nn0addcom sylan adantll 3eqtr4d sn-addcand
    adantr 3eqtr3d mpbid ) ACDZEAFGZHDZIZBJDZIZVAABKGZKGZVABAKGZKGZQVFVHQVEVAAK
    GZBKGZVABKGZAKGZVGVIVEBBVAKGZAKGZVKVMVEVOBVJKGBEKGZBVEBVAAVEBVCVDLMZVEVAUTV
    ACDVBVDAUANOZVEAUTVBVDUBOZPVEVJEBKUTVJEQVBVDAUCZNUDVDVPBQZVCVDBCDZWABUEZBUH
    RUFUGVCVDVKEBKGZBUTVKWDQVBUTVJEBKVTSUQVDWBWDBQWCBUIRUJVEVLVNAKVBVDVLVNQZUTV
    BVAJDVDWEVAUKVABULUMUNSUOVEVAABVRVSVQPVEVABAVRVQVSPURVEVAVFVHVRVEABVSVQTVEB
    AVQVSTUPUS $.

  $( Addition is commutative for integers.  Proven without ~ ax-mulcom .
     (Contributed by SN, 25-Jan-2025.) $)
  zaddcom $p |- ( ( A e. ZZ /\ B e. ZZ ) -> ( A + B ) = ( B + A ) ) $=
    ( cz wcel cn0 cr cresub co cn wa wo caddc wceq reelznn0nn zaddcomlem oveq1d
    cc0 nncnd addassd 3eqtr4d nn0addcom eqcomd renegid2 ad2antrl ad2antrr recnd
    ancoms simplr simpll simprl readdlid oveq2d simprr addcld nnaddcom ad2ant2l
    3eqtr3d nnaddcld sn-addcand mpbid ccase syl2anb ) ACDAEDZAFDZQAGHZIDZJZKBED
    ZBFDZQBGHZIDZJZKABLHZBALHZMZBCDANBNVCVHVGVLVOABUAABOVLVCVOVLVCJVNVMBAOUBUGV
    GVLJZVEVJLHZVMLHZVQVNLHZMVOVPVJVELHZVMLHZVEVJVNLHZLHZVRVSVPVJVEVMLHZLHZVEAL
    HZWAWCVPVJBLHZQWEWFVIWGQMVGVKBUCUDZVPWDBVJLVPWFBLHQBLHZWDBVPWFQBLVDWFQMVFVL
    AUCUEZPVPVEABVPVEVDVFVLUHZRZVPAVDVFVLUIUFZVPBVGVIVKUJUFZSVIWIBMVGVKBUKUDUQU
    LWJTVPVJVEVMVPVJVGVIVKUMZRZWLVPABWMWNUNZSVPWBAVELVPWGALHQALHZWBAVPWGQALWHPV
    PVJBAWPWNWMSVDWRAMVFVLAUKUEUQULTVPVQVTVMLVFVKVQVTMVDVIVEVJUOUPPVPVEVJVNWLWP
    VPBAWNWMUNZSTVPVQVMVNVPVQVPVEVJWKWOURRWQWSUSUTVAVB $.
  $( $j usage 'zaddcom' avoids 'ax-mulcom'; $)

  ${
    $d A x y $.  $d N x y $.  $d ph x y $.
    renegmulnnass.a $e |- ( ph -> A e. RR ) $.
    renegmulnnass.n $e |- ( ph -> N e. NN ) $.
    $( Move multiplication by a natural number inside and outside negation.
       (Contributed by SN, 25-Jan-2025.) $)
    renegmulnnass $p |- ( ph -> ( ( 0 -R A ) x. N ) = ( 0 -R ( A x. N ) ) ) $=
      ( vx wcel cc0 cresub co cmul wceq caddc oveq2 oveq2d eqeq12d syl ad2antrr
      c1 cr vy cn cv weq rernegcl ax-1rid eqtr4d wa 0red nnre ad2antlr remulcld
      simpr readdsub syl3anc readdlid oveq1d eqtr3d resubsub4 3eqtr4d nnadd1com
      3eqtrd cc recnd 1cnd nncn adddid eqtrd nnindd mpdan ) ACUBGHBIJZCKJZHBCKJ
      ZIJZLZEAVKFUCZKJZHBVPKJZIJZLVKSKJZHBSKJZIJZLVKUAUCZKJZHBWCKJZIJZLZVKWCSMJ
      ZKJZHBWHKJZIJZLVOFUACVPSLZVQVTVSWBVPSVKKNWLVRWAHIVPSBKNOPFUAUDZVQWDVSWFVP
      WCVKKNWMVRWEHIVPWCBKNOPVPWHLZVQWIVSWKVPWHVKKNWNVRWJHIVPWHBKNOPVPCLZVQVLVS
      VNVPCVKKNWOVRVMHIVPCBKNOPAVTVKWBAVKTGZVTVKLABTGZWPDBUEQZVKUFQZAWABHIAWQWA
      BLDBUFQZOUGAWCUBGZUHZWGUHZVTWDMJZHWEWAMJZIJZWIWKXCVKWDMJZHWEBMJZIJZXDXFXC
      XGVKWFMJZWFBIJZXIXCWDWFVKMXBWGUMOXCHWFMJZBIJZXJXKXCHTGZWFTGZWQXMXJLXCUIZX
      CWETGZXOXCBWCAWQXAWGDRZXAWCTGAWGWCUJUKULZWEUEQZXRHWFBUNUOXCXLWFBIXCXOXLWF
      LXTWFUPQUQURXCXNXQWQXKXILXPXSXRHWEBUSUOVBAXDXGLXAWGAVTVKWDMWSUQRAXFXILXAW
      GAXEXHHIAWABWEMWTOORUTXCWIVKSWCMJZKJZXDXAWIYBLAWGXAWHYAVKKWCVAOUKXCVKSWCA
      VKVCGXAWGAVKWRVDRXCVEZXAWCVCGAWGWCVFUKZVGVHXCWJXEHIXCBWCSABVCGXAWGABDVDRY
      DYCVGOUTVIVJ $.
  $}

  $( Multiplication is commutative for nonnegative integers.  Proven without
     ~ ax-mulcom .  (Contributed by SN, 25-Jan-2025.) $)
  nn0mulcom $p |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A x. B ) = ( B x. A ) ) $=
    ( cn0 wcel cn cc0 wceq wo cmul co elnn0 cr remul02 remul01 eqtr4d syl oveq1
    oveq2 eqeq12d syl5ibrcom nnmulcom impcom jaoian sylanb nn0re jaodan sylan2b
    nnre imp ) BCDACDZBEDZBFGZHABIJZBAIJZGZBKUJUKUOULUJAEDZAFGZHUKUOAKUPUKUOUQA
    BUAUKUQUOUKUOUQFBIJZBFIJZGZUKBLDZUTBUHVAURFUSBMBNOPUQUMURUNUSAFBIQAFBIRSTUB
    UCUDUJULUOUJUOULAFIJZFAIJZGZUJALDZVDAUEVEVBFVCANAMOPULUMVBUNVCBFAIRBFAIQSTU
    IUFUG $.
  $( $j usage 'nn0mulcom' avoids 'ax-mulcom'; $)

  $( Lemma for ~ zmulcom .  (Contributed by SN, 25-Jan-2025.) $)
  zmulcomlem $p |- ( ( ( A e. RR /\ ( 0 -R A ) e. NN ) /\ B e. NN0 ) ->
                     ( A x. B ) = ( B x. A ) ) $=
    ( cn0 wcel cr cc0 cresub co cn wa wceq wo cmul elnn0 oveq1d ad2antrr oveq2d
    adantl remul01 3eqtr3d renegneg rernegcl renegmulnnass adantll nnre resubdi
    simpr nnmulcom 0red syl3anc eqtrd 3eqtr2d remul02 eqtr4d adantr oveq2 oveq1
    syl eqeq12d syl5ibrcom imp jaodan sylan2b ) BCDAEDZFAGHZIDZJZBIDZBFKZLABMHZ
    BAMHZKZBNVGVHVLVIVGVHJZFVEGHZBMHZVJVJVKVDVOVJKVFVHVDVNABMAUAZOPZVQVMVOFVEBM
    HZGHZVJVKVMVEBVDVEEDZVFVHAUBPZVGVHUGUCVQVMVSFBVEMHZGHZBVNMHZVKVMVRWBFGVFVHV
    RWBKVDVEBUHUDQVMWDBFMHZWBGHZWCVMBEDZFEDVTWDWFKVHWGVGBUEZRVMUIWABFVEUFUJVMWE
    FWBGVHWEFKZVGVHWGWIWHBSURROUKVMVNABMVDVNAKVFVHVPPQULTTVGVIVLVGVLVIAFMHZFAMH
    ZKZVDWLVFVDWJFWKASAUMUNUOVIVJWJVKWKBFAMUPBFAMUQUSUTVAVBVC $.

  $( Multiplication is commutative for integers.  Proven without ~ ax-mulcom .
     From this result and ~ grpcominv1 , we can show that rationals commute
     under multiplication without using ~ ax-mulcom .  (Contributed by SN,
     25-Jan-2025.) $)
  zmulcom $p |- ( ( A e. ZZ /\ B e. ZZ ) -> ( A x. B ) = ( B x. A ) ) $=
    ( cz wcel cn0 cr cc0 cresub co cn wa cmul wceq reelznn0nn zmulcomlem oveq2d
    wo rernegcl ad2antrr ad2antrl eqcomd ancoms nnmulcom ad2ant2l renegmulnnass
    nn0mulcom simprr simplr 3eqtr4d remulneg2d renegneg oveq12d 3eqtr3d syl2anb
    syl ccase ) ACDAEDZAFDZGAHIZJDZKZQBEDZBFDZGBHIZJDZKZQABLIZBALIZMZBCDANBNUQV
    BVAVFVIABUFABOVFUQVIVFUQKVHVGBAOUAUBVAVFKZGUSHIZGVDHIZLIZVLVKLIZVGVHVJGVKVD
    LIZHIGVLUSLIZHIVMVNVJVOVPGHVJGUSVDLIZHIGVDUSLIZHIVOVPVJVQVRGHUTVEVQVRMURVCU
    SVDUCUDPVJUSVDURUSFDZUTVFARZSZVAVCVEUGUEVJVDUSVCVDFDZVAVEBRZTZURUTVFUHUEUIP
    VJVKVDURVKFDZUTVFURVSWEVTUSRUOSWDUJVJVLUSVCVLFDZVAVEVCWBWFWCVDRUOTWAUJUIVJV
    KAVLBLURVKAMUTVFAUKSZVCVLBMVAVEBUKTZULVJVLBVKALWHWGULUMUPUN $.
  $( $j usage 'zmulcom' avoids 'ax-mulcom'; $)

  $( Thanks to ~ ax-pre-mulgt0 and many creative manipulations, the entirety of
     "A is positive XOR B is positive XOR A times B is positive" is provable
     without ~ ax-mulcom .

     (In other words, 1 or 3 of {A, B, A times B} is positive, and toggling
     the positivity of one affects the positivity of one other.) $)

  ${
    mulgt0con1dlem.a $e |- ( ph -> A e. RR ) $.
    mulgt0con1dlem.b $e |- ( ph -> B e. RR ) $.
    mulgt0con1dlem.1 $e |- ( ph -> ( 0 < A -> 0 < B ) ) $.
    mulgt0con1dlem.2 $e |- ( ph -> ( A = 0 -> B = 0 ) ) $.
    $( Lemma for ~ mulgt0con1d .  Contraposes a positive deduction to a
       negative deduction.  (Contributed by SN, 26-Jun-2024.) $)
    mulgt0con1dlem $p |- ( ph -> ( B < 0 -> A < 0 ) ) $=
      ( cc0 clt wbr wceq wo wn 0red lttrid orim12d con3d sylibrd sylbid ) ACHIJ
      CHKZHCIJZLZMZBHIJZACHEANZOAUCBHKZHBIJZLZMUDAUHUBAUFTUGUAGFPQABHDUEORS $.
  $}

  ${
    mulgt0con1d.a $e |- ( ph -> A e. RR ) $.
    mulgt0con1d.b $e |- ( ph -> B e. RR ) $.
    mulgt0con1d.1 $e |- ( ph -> 0 < B ) $.
    mulgt0con1d.2 $e |- ( ph -> ( A x. B ) < 0 ) $.
    $( Counterpart to ~ mulgt0con2d , though not a lemma.  This is the first
       use of ~ ax-pre-mulgt0 .  One direction of ~ mulgt0b2d .  (Contributed
       by SN, 26-Jun-2024.) $)
    mulgt0con1d $p |- ( ph -> A < 0 ) $=
      ( cmul co cc0 clt wbr remulcld wa cr wcel adantr simpr mulgt0d wceq oveq1
      ex remul02 syl eqeq1d syl5ibrcom mulgt0con1dlem mpd ) ABCHIZJKLBJKLGABUID
      ABCDEMAJBKLZJUIKLAUJNBCABOPUJDQACOPZUJEQAUJRAJCKLUJFQSUBAUIJTBJTZJCHIZJTZ
      AUKUNECUCUDULUIUMJBJCHUAUEUFUGUH $.
  $}

  ${
    mulgt0con2d.a $e |- ( ph -> A e. RR ) $.
    mulgt0con2d.b $e |- ( ph -> B e. RR ) $.
    mulgt0con2d.1 $e |- ( ph -> 0 < A ) $.
    mulgt0con2d.2 $e |- ( ph -> ( A x. B ) < 0 ) $.
    $( Lemma for ~ mulgt0b1d and contrapositive of ~ mulgt0 .  (Contributed by
       SN, 26-Jun-2024.) $)
    mulgt0con2d $p |- ( ph -> B < 0 ) $=
      ( cmul co cc0 clt wbr remulcld wa cr wcel adantr simpr mulgt0d wceq oveq2
      ex remul01 syl eqeq1d syl5ibrcom mulgt0con1dlem mpd ) ABCHIZJKLCJKLGACUIE
      ABCDEMAJCKLZJUIKLAUJNBCABOPZUJDQACOPUJEQAJBKLUJFQAUJRSUBAUIJTCJTZBJHIZJTZ
      AUKUNDBUCUDULUIUMJCJBHUAUEUFUGUH $.
  $}

  ${
    mulgt0b1d.a $e |- ( ph -> A e. RR ) $.
    mulgt0b1d.b $e |- ( ph -> B e. RR ) $.
    mulgt0b1d.1 $e |- ( ph -> 0 < A ) $.
    $( Biconditional, deductive form of ~ mulgt0 .  The second factor is
       positive iff the product is.  (Contributed by SN, 26-Jun-2024.) $)
    mulgt0b1d $p |- ( ph -> ( 0 < B <-> 0 < ( A x. B ) ) ) $=
      ( cc0 clt wbr cmul co wa cr wcel adantr c1 cresub recnd breq1d syl ex 1re
      simpr mulgt0d rernegcl mp1i remulcld mulassd biimpa mulgt0con2d relt0neg2
      wb 1red remulneg2d wceq ax-1rid oveq2d eqtrd bitr4d 3imtr4d impbid ) AGCH
      IZGBCJKZHIZAVBVDAVBLBCABMNZVBDOACMNZVBEOAGBHIZVBFOAVBUCUDUAAVCGPQKZJKZGHI
      ZCVHJKZGHIZVDVBAVJVLAVJLBVKAVEVJDOAVKMNVJACVHEPMNVHMNAUBPUEUFZUGOAVGVJFOA
      VJBVKJKZGHIAVIVNGHABCVHABDRACERAVHVMRUHSUIUJUAAVDGVCQKZGHIZVJAVCMNZVDVPUL
      ABCDEUGZVCUKTAVIVOGHAVIGVCPJKZQKVOAVCPVRAUMZUNAVSVCGQAVQVSVCUOVRVCUPTUQUR
      SUSAVBGCQKZGHIZVLAVFVBWBULECUKTAVKWAGHAVKGCPJKZQKWAACPEVTUNAWCCGQAVFWCCUO
      ECUPTUQURSUSUTVA $.
  $}

  ${
    sn-ltmul2d.a $e |- ( ph -> A e. RR ) $.
    sn-ltmul2d.b $e |- ( ph -> B e. RR ) $.
    sn-ltmul2d.c $e |- ( ph -> C e. RR ) $.
    sn-ltmul2d.1 $e |- ( ph -> 0 < C ) $.
    $( ~ ltmul2d without ~ ax-mulcom .  (Contributed by SN, 26-Jun-2024.) $)
    sn-ltmul2d $p |- ( ph -> ( ( C x. A ) < ( C x. B ) <-> A < B ) ) $=
      ( cc0 cmul co cresub clt wbr cr wcel syl2anc wb remulcld reposdif resubdi
      rersubcl mulgt0b1d wceq syl3anc breq2d bitr2d 3bitr4d ) AIDCJKZDBJKZLKZMN
      ZICBLKZMNZUJUIMNZBCMNZAUNIDUMJKZMNULADUMGACOPZBOPZUMOPFECBUBQHUCAUQUKIMAD
      OPURUSUQUKUDGFEDCBUAUEUFUGAUJOPUIOPUOULRADBGESADCGFSUJUITQAUSURUPUNREFBCT
      QUH $.
    $( $j usage 'sn-ltmul2d' avoids 'ax-mulcom'; $)
  $}

  ${
    sn-ltmulgt11d.a $e |- ( ph -> A e. RR ) $.
    sn-ltmulgt11d.b $e |- ( ph -> B e. RR ) $.
    sn-ltmulgt11d.1 $e |- ( ph -> 0 < B ) $.
    $( ~ ltmulgt11d without ~ ax-mulcom .  (Contributed by SN, 26-Jun-2024.) $)
    sn-ltmulgt11d $p |- ( ph -> ( 1 < A <-> B < ( B x. A ) ) ) $=
      ( c1 cmul co clt wbr 1red sn-ltmul2d wcel wceq ax-1rid syl breq1d bitr3d
      cr ) ACGHIZCBHIZJKGBJKCUBJKAGBCALDEFMAUACUBJACTNUACOECPQRS $.
    $( $j usage 'sn-ltmulgt11d' avoids 'ax-mulcom'; $)
  $}

  $( ~ 0lt1 without ~ ax-mulcom .  (Contributed by SN, 13-Feb-2024.) $)
  sn-0lt1 $p |- 0 < 1 $=
    ( c1 cc0 clt wbr wo wne ax-1ne0 1re 0re lttri2i mpbi cresub co cmul cr wcel
    rernegcl mp1i ax-mp wceq wb relt0neg1 biimpi mulgt0d remulneg2d ax-1rid syl
    1red oveq2d renegneg 3eqtrd breqtrdi id jaoi ) ABCDZBACDZEZUPABFUQGABHIJKUO
    UPUPUOBBALMZURNMZACUOURURAOPZUROPZUOHAQZRZVCUOBURCDZUTUOVDUAHAUBSUCZVEUDUTU
    SATHUTUSBURANMZLMBURLMAUTURAVBUTUHUEUTVFURBLUTVAVFURTVBURUFUGUIAUJUKSULUPUM
    UNS $.
  $( $j usage 'sn-0lt1' avoids 'ax-mulcom'; $)

  $( ~ ltp1 without ~ ax-mulcom .  (Contributed by SN, 13-Feb-2024.) $)
  sn-ltp1 $p |- ( A e. RR -> A < ( A + 1 ) ) $=
    ( c1 cr wcel caddc co clt wbr 1re wa cc0 sn-0lt1 sn-ltaddpos mpbii mpan ) B
    CDZACDZAABEFGHZIPQJKBGHRLBAMNO $.
  $( $j usage 'sn-ltp1' avoids 'ax-mulcom'; $)

  ${
    sn-recgt0d.a $e |- ( ph -> A e. RR ) $.
    sn-recgt0d.z $e |- ( ph -> 0 < A ) $.
    $( The reciprocal of a positive real is positive.  (Contributed by SN,
       26-Nov-2025.) $)
    sn-recgt0d $p |- ( ph -> 0 < ( 1 /R A ) ) $=
      ( cc0 c1 crediv co clt wbr sn-0lt1 gt0ne0d rerecidd breqtrrid sn-rereccld
      cmul mulgt0b1d mpbird ) AEFBGHZIJEBSPHZIJAEFTIKABCABDLZMNABSCABCUAODQR $.
  $}

  ${
    mulgt0b2d.a $e |- ( ph -> A e. RR ) $.
    mulgt0b2d.b $e |- ( ph -> B e. RR ) $.
    mulgt0b2d.1 $e |- ( ph -> 0 < B ) $.
    $( Biconditional, deductive form of ~ mulgt0 .  The first factor is
       positive iff the product is.  (Contributed by SN, 24-Nov-2025.) $)
    mulgt0b2d $p |- ( ph -> ( 0 < A <-> 0 < ( A x. B ) ) ) $=
      ( cc0 clt wbr cmul co wa cr wcel adantr simpr mulgt0d c1 wceq recnd oveq2
      crediv remulcld gt0ne0d remul01 syl sylan9eqr mteqand sn-rereccld mulassd
      sn-recgt0d rerecidd oveq2d ax-1rid 3eqtrd breqtrd impbida ) AGBHIZGBCJKZH
      IZAURLBCABMNZURDOACMNZUREOAURPAGCHIURFOQAUTLZGUSRCUBKZJKZBHVCUSVDAUSMNUTA
      BCDEUCOVCCAVBUTEOZVCCGUSGVCUSAUTPZUDCGSVCUSBGJKZGCGBJUAVCVAVHGSAVAUTDOZBU
      EUFUGUHUIZVGAGVDHIUTACEFUKOQVCVEBCVDJKZJKZBRJKZBVCBCVDVCBVITVCCVFTVCVDVJT
      UJAVLVMSUTAVKRBJACEACFUDULUMOVCVAVMBSVIBUNUFUOUPUQ $.
    $( $j usage 'mulgt0b2d' avoids 'ax-mulcom'; $)
  $}

  ${
    sn-mulgt1d.a $e |- ( ph -> A e. RR ) $.
    sn-mulgt1d.b $e |- ( ph -> B e. RR ) $.
    sn-mulgt1d.1 $e |- ( ph -> 1 < A ) $.
    sn-mulgt1d.2 $e |- ( ph -> 1 < B ) $.
    $( ~ mulgt1d without ~ ax-mulcom .  (Contributed by SN, 26-Jun-2024.) $)
    sn-mulgt1d $p |- ( ph -> 1 < ( A x. B ) ) $=
      ( c1 cmul 1red remulcld clt wbr cc0 0red sn-0lt1 a1i lttrd sn-ltmulgt11d
      co mpbid ) AHBBCITZAJZDABCDEKFAHCLMBUBLMGACBEDANHBAOUCDNHLMAPQFRSUAR $.
    $( $j usage 'sn-mulgt1d' avoids 'ax-mulcom'; $)
  $}

  $(
    If this could be proved, then it would prove ~ arch .  However, proving
    ~ reltm1 from ~ sn-ltp1 is non-trivial, since the statement corresponds to
    ` 1 + A ` instead of ` A + 1 ` .  Specifically, we can show
    ` ( A -R 1 ) = ( 0 -R 1 ) + A ` , but we can only prove
    ` ( A e. RR -> A + ( 0 -R 1 ) < A ) ` .

    @( A number minus 1 is less than itself.  Compare ~ ltm1 . @)
    reltm1 $p |- ( A e. RR -> ( A -R 1 ) < A ) $=
      ? $.

    Of course, there are still further barriers if ~ arch is provable.  In the
    current proof of ~ ax-mulcom from ~ arch
    ~ https://github.com/metamath/set.mm/pull/3792#issuecomment-1910092517 we
    also need to commute ~ sn-ltmul2d and show that the inverse of a natural
    number (additively) commutes with all reals.
  $)

  $( Negative one is a negative number.  (Contributed by SN, 1-Jun-2024.) $)
  reneg1lt0 $p |- ( 0 -R 1 ) < 0 $=
    ( cc0 c1 clt wbr cresub co sn-0lt1 cr wcel wb 1re relt0neg2 ax-mp mpbi ) AB
    CDZABEFACDZGBHIOPJKBLMN $.

  ${
    sn-reclt0d.a $e |- ( ph -> A e. RR ) $.
    sn-reclt0d.z $e |- ( ph -> A < 0 ) $.
    $( The reciprocal of a negative real is negative.  (Contributed by SN,
       26-Nov-2025.) $)
    sn-reclt0d $p |- ( ph -> ( 1 /R A ) < 0 ) $=
      ( c1 crediv co cc0 cresub lt0ne0d sn-rereccld cr wcel rernegcl syl clt wb
      wbr relt0neg1 cmul mpbid remulneg2d rerecid2d eqtrd reneg1lt0 a1i eqbrtrd
      oveq2d mulgt0con1d ) AEBFGZHBIGZABCABDJZKZABLMZUKLMCBNOABHPRZHUKPRZDAUNUO
      UPQCBSOUAAUJUKTGZHEIGZHPAUQHUJBTGZIGURAUJBUMCUBAUSEHIABCULUCUHUDURHPRAUEU
      FUGUI $.
  $}

  ${
    mullt0b1d.a $e |- ( ph -> A e. RR ) $.
    mullt0b1d.b $e |- ( ph -> B e. RR ) $.
    mullt0b1d.1 $e |- ( ph -> A < 0 ) $.
    ${
      mulltgt0d.2 $e |- ( ph -> 0 < B ) $.
      $( Negative times positive is negative.  (Contributed by SN,
         26-Nov-2025.) $)
      mulltgt0d $p |- ( ph -> ( A x. B ) < 0 ) $=
        ( cmul co cc0 clt wbr wceq wo wn wne wa lt0ne0d gt0ne0d jca mtbird 0red
        neanior sylib sn-remul0ord ltnsymd mtbid ioran sylanbrc remulcld lttrid
        mulgt0b2d mpbird ) ABCHIZJKLUNJMZJUNKLZNOZAUOOUPOUQAUOBJMCJMNZABJPZCJPZ
        QUROAUSUTABFRACGSTBJCJUCUDABCDEUEUAAJBKLUPABJDAUBZFUFABCDEGULUGUOUPUHUI
        AUNJABCDEUJVAUKUM $.
    $}

    $( When the first term is negative, the second term is positive iff the
       product is negative.  (Contributed by SN, 26-Nov-2025.) $)
    mullt0b1d $p |- ( ph -> ( 0 < B <-> ( A x. B ) < 0 ) ) $=
      ( cc0 clt wbr cmul co wa cr wcel adantr simpr cresub c1 recnd syl lt0ne0d
      mulltgt0d crediv sn-rereccld remulcld remulneg2d rerecid2d oveq1d mulassd
      wceq remullid 3eqtr3d oveq2d eqtrd rernegcl sn-reclt0d eqbrtrrd relt0neg1
      ex wb relt0neg2 3imtr4d imp impbida ) AGCHIZBCJKZGHIZAVELBCABMNVEDOACMNZV
      EEOABGHIVEFOAVEPUBAVGVEAGGVFQKZHIZGCQKZGHIZVGVEAVJVLAVJLZRBUCKZVIJKZVKGHA
      VOVKUJVJAVOGVNVFJKZQKVKAVNVFABDABFUAZUDZABCDEUEZUFAVPCGQAVNBJKZCJKRCJKZVP
      CAVTRCJABDVQUGUHAVNBCAVNVRSABDSACESUIAVHWACUJECUKTULUMUNOVMVNVIAVNMNVJVRO
      AVIMNZVJAVFMNZWBVSVFUOTOAVNGHIVJABDFUPOAVJPUBUQUSAWCVGVJUTVSVFURTAVHVEVLU
      TECVATVBVCVD $.
  $}

  ${
    mullt0b2d.a $e |- ( ph -> A e. RR ) $.
    mullt0b2d.b $e |- ( ph -> B e. RR ) $.
    mullt0b2d.1 $e |- ( ph -> B < 0 ) $.
    $( When the second term is negative, the first term is positive iff the
       product is negative.  (Contributed by SN, 26-Nov-2025.) $)
    mullt0b2d $p |- ( ph -> ( 0 < A <-> ( A x. B ) < 0 ) ) $=
      ( cc0 clt wbr cmul co wa wceq wo wn wne simpr adantr cr mpbird sylib wcel
      gt0ne0d lt0ne0d neanior sn-remul0ord mtbird ltnsymd mulgt0b1d mtbid ioran
      jca 0red sylanbrc remulcld lttrid remul02 syl ltnrd eqnbrtrd oveq1 breq1d
      wb notbid syl5ibcom con2d imp simplr ad2antrr mullt0b1d mtand impbida ) A
      GBHIZBCJKZGHIZAVMLZVOVNGMZGVNHIZNOZVPVQOVROVSVPVQBGMCGMNZVPBGPZCGPZLVTOVP
      WAWBVPBAVMQZUCVPCACGHIVMFRUDULBGCGUEUAVPBCABSUBZVMDRZACSUBZVMERZUFUGVPGCH
      IZVRAWHOZVMACGEAUMZFUHZRVPBCWEWGWCUIUJVQVRUKUNAVOVSVCVMAVNGABCDEUOWJUPRTA
      VOLZVMGBMZBGHIZNOZWLWMOZWNOWOAVOWPAWMVOAGCJKZGHIZOWMVOOAWQGGHAWFWQGMECUQU
      RAGWJUSUTWMWRVOWMWQVNGHGBCJVAVBVDVEVFVGWLWNWHAWIVOWKRWLWNLZWHVOAVOWNVHWSB
      CAWDVOWNDVIAWFVOWNEVIWLWNQVJTVKWMWNUKUNAVMWOVCVOAGBWJDUPRTVL $.
    $( $j usage 'mullt0b2d' avoids 'ax-mulcom'; $)
  $}

  ${
    sn-mullt0d.a $e |- ( ph -> A e. RR ) $.
    sn-mullt0d.b $e |- ( ph -> B e. RR ) $.
    sn-mullt0d.1 $e |- ( ph -> A < 0 ) $.
    sn-mullt0d.2 $e |- ( ph -> B < 0 ) $.
    $( The product of two negative numbers is positive.  (Contributed by SN,
       1-Dec-2025.) $)
    sn-mullt0d $p |- ( ph -> 0 < ( A x. B ) ) $=
      ( cc0 cmul co clt wbr wceq wo wn wne wa lt0ne0d jca neanior sylib neqcomd
      sn-remul0ord mtbird 0red ltnsymd mullt0b1d mtbid sylanbrc remulcld lttrid
      ioran mpbird ) AHBCIJZKLHUNMZUNHKLZNOZAUOOUPOUQAUNHAUNHMBHMCHMNZABHPZCHPZ
      QUROAUSUTABFRACGRSBHCHTUAABCDEUCUDUBAHCKLUPACHEAUEZGUFABCDEFUGUHUOUPULUIA
      HUNVAABCDEUJUKUM $.
    $( $j usage 'sn-mullt0d' avoids 'ax-mulcom'; $)
  $}

  ${
    sn-msqgt0d.a $e |- ( ph -> A e. RR ) $.
    sn-msqgt0d.u $e |- ( ph -> A =/= 0 ) $.
    $( A nonzero square is positive.  (Contributed by SN, 1-Dec-2025.) $)
    sn-msqgt0d $p |- ( ph -> 0 < ( A x. A ) ) $=
      ( cc0 clt wbr cmul co wa cr wcel adantr simpr sn-mullt0d mulgt0d wne 0red
      wo lttri2d mpbid mpjaodan ) ABEFGZEBBHIFGEBFGZAUCJBBABKLZUCCMZUFAUCNZUGOA
      UDJBBAUEUDCMZUHAUDNZUIPABEQUCUDSDABECARTUAUB $.
  $}

  $( ~ inelr without ~ ax-mulcom .  (Contributed by SN, 1-Jun-2024.) $)
  sn-inelr $p |- -. _i e. RR $=
    ( ci cr wcel cc0 cmul co clt wbr c1 cresub reneg1lt0 1re rernegcl ax-mp 0re
    wn ltnsymi id wceq caddc reixi breq2i mtbir wne 0ne1 oveq12d oveq1d ax-i2m1
    a1i remul02 oveq1i readdlid eqtri 3eqtr3g adantl mteqand sn-msqgt0d mto ) A
    BCZDAAEFZGHZVADDIJFZGHZVBDGHVCPKVBDIBCZVBBCLIMNOQNUTVBDGUAUBUCUSAUSRUSADDID
    IUDUSUEUIADSZDISUSVEUTITFDDEFZITFZDIVEUTVFITVEADADEVERZVHUFUGUHVGDITFZIVFDI
    TDBCVFDSODUJNUKVDVIISLIULNUMUNUOUPUQUR $.
  $( $j usage 'sn-inelr' avoids 'ax-mulcom'; $)

  ${
    $d R x $.
    $( ` _i ` times a real is real iff the real is zero.  (Contributed by SN,
       27-Jun-2024.) $)
    sn-itrere $p |- ( R e. RR -> ( ( _i x. R ) e. RR <-> R = 0 ) ) $=
      ( cr wcel ci cmul co cc0 wceq wne wn wa sn-inelr crediv ax-icn a1i simpll
      c1 cc recnd ex simplr sn-rereccld mulassd rerecidd oveq2d sn-it1ei 3eqtrd
      simpr remulcld eqeltrrd mtoi necon4ad oveq2 sn-it0e0 0re eqeltri eqeltrdi
      impbid1 ) ABCZDAEFZBCZAGHZUSVAAGUSAGIZVAJUSVCKZVADBCZLVDVAVEVDVAKZUTQAMFZ
      EFZDBVFVHDAVGEFZEFDQEFZDVFDAVGDRCVFNOVFAUSVCVAPZSVFVGVFAVKUSVCVAUAZUBZSUC
      VFVIQDEVFAVKVLUDUEVJDHVFUFOUGVFUTVGVDVAUHVMUIUJTUKTULVBUTDGEFZBAGDEUMVNGB
      UNUOUPUQUR $.
    $( $j usage 'sn-itrere' avoids 'ax-mulcom'; $)

    $( Commuted version of ~ sn-itrere .  (Contributed by SN, 27-Jun-2024.) $)
    sn-retire $p |- ( R e. RR -> ( ( R x. _i ) e. RR <-> R = 0 ) ) $=
      ( cr wcel ci cmul co cc0 wceq wne sn-inelr crediv simpll simplr rerecid2d
      wn wa c1 recnd a1i ex oveq1d sn-rereccld cc ax-icn mulassd sn-it1ei eqtri
      sn-1ticom 3eqtr3d simpr remulcld eqeltrrd necon4ad oveq1 sn-0tie0 eqeltri
      mtoi 0re eqeltrdi impbid1 ) ABCZADEFZBCZAGHZVAVCAGVAAGIZVCOVAVEPZVCDBCZJV
      FVCVGVFVCPZQAKFZVBEFZDBVHVIAEFZDEFQDEFZVJDVHVKQDEVHAVAVEVCLZVAVEVCMZNUAVH
      VIADVHVIVHAVMVNUBZRVHAVMRDUCCVHUDSUEVLDHVHVLDQEFDUHUFUGSUIVHVIVBVOVFVCUJU
      KULTUQTUMVDVBGDEFZBAGDEUNVPGBUOURUPUSUT $.
    $( $j usage 'sn-retire' avoids 'ax-mulcom'; $)
  $}

  ${
    cnreeu.r $e |- ( ph -> r e. RR ) $.
    cnreeu.s $e |- ( ph -> s e. RR ) $.
    cnreeu.t $e |- ( ph -> t e. RR ) $.
    cnreeu.u $e |- ( ph -> u e. RR ) $.
    $( The reals in the expression given by ~ cnre uniquely define a complex
       number.  (Contributed by SN, 27-Jun-2024.) $)
    cnreeu $p |- ( ph ->
      ( ( r + ( _i x. s ) ) = ( t + ( _i x. u ) ) <-> ( r = t /\ s = u ) ) ) $=
      ( ci cmul co caddc wceq cc0 oveq2d wcel cr syl adantr cv weq cresub oveq1
      recnd ax-icn a1i mulcld rernegcl addassd renegid adddid sn-it0e0 readdrid
      wa 3eqtr3d 3eqtrd oveq1d sn-addlid renegid2 3eqtr4d addcld eqeq12d biimpa
      cc 3eqtr3rd simpr readdcld eqeltrrd sn-itrere syl2anc oveq2 adantl syldan
      readdlid sylan9req eqtr2d jca ex syl5 id oveqan12d impbid1 ) AEUAZJDUAZKL
      ZMLZCUAZJBUAZKLZMLZNZECUBZDBUBZUOZWLOWHUCLZWGJOWEUCLZKLZMLZMLZWPWKWRMLZML
      ZNZAWOWLWSXAWPMWGWKWRMUDPAXCWOAXCWPWDMLZJWIWQMLZKLZNZWOAXCXGAWTXDXBXFAWSW
      DWPMAWSWDWFWRMLZMLWDOMLZWDAWDWFWRAWDFUEZAJWEJVEQAUFUGZAWEGUEZUHAJWQXKAWQA
      WERQZWQRQZGWEUISZUEZUHZUJAXHOWDMAJWEWQMLZKLJOKLZXHOAXROJKAXMXRONGWEUKSPAJ
      WEWQXKXLXPULXSONZAUMUGUPPAWDRQZXIWDNFWDUNSUQPAWPWHMLZWJMLZWRMLZWPWKMLZWRM
      LXFXBAYCYEWRMAWPWHWJAWPAWHRQZWPRQZHWHUISZUEZAWHHUEZAJWIXKAWIIUEZUHZUJURAO
      WJMLZWRMLWJWRMLYDXFAYMWJWRMAWJVEQYMWJNYLWJUSSURAYCYMWRMAYBOWJMAYFYBONHWHU
      TSURURAJWIWQXKYKXPULVAAWPWKWRYIAWHWJYJYLVBXQUJVFVCVDAXGUOZWMWNAXGXDONZWMY
      NXDXFXSOAXGVGZYNXEOJKYNXERQZXFRQZXEONZYNWIWQAWIRQZXGITAXNXGXOTVHYNXDXFRYP
      YNWPWDAYGXGYHTAYAXGFTVHVIYQYRYSXEVJVDVKZPXTYNUMUGUQAYOUOZWHXDMLZWHOMLZWDW
      HYOUUCUUDNAXDOWHMVLVMUUBWHWPMLZWDMLOWDMLZUUCWDUUBUUEOWDMAUUEONZYOAYFUUGHW
      HUKSTURUUBWHWPWDAWHVEQYOYJTAWPVEQYOYITAWDVEQYOXJTUJAUUFWDNZYOAYAUUHFWDVOS
      TUPUUBYFUUDWHNAYFYOHTWHUNSUPVNAXGYSWNUUAAYSUOWIOWEMLZWEAYSWIXEWEMLZUUIAUU
      JWIWQWEMLZMLWIOMLZWIAWIWQWEYKXPXLUJAUUKOWIMAXMUUKONGWEUTSPAYTUULWINIWIUNS
      UQXEOWEMUDVPAUUIWENZYSAXMUUMGWEVOSTVQVNVRVNVSVTWMWNWDWHWFWJMWMWAWEWIJKVLW
      BWC $.
  $}

  ${
    $d x y z A $.
    $( ~ sup2 with exactly the same proof except for using ~ sn-ltp1 instead of
       ~ ltp1 , saving ~ ax-mulcom .  (Contributed by SN, 26-Jun-2024.) $)
    sn-sup2 $p |- ( ( A C_ RR /\ A =/= (/) /\
                  E. x e. RR A. y e. A ( y < x \/ y = x ) ) ->
               E. x e. RR ( A. y e. A -. x < y /\
                  A. y e. RR ( y < x -> E. z e. A y < z ) ) ) $=
      ( cr cv clt wbr wceq wral wrex w3a wi wa wcel wex c1 caddc adantr imp wss
      c0 wne wo wn co peano2re a1i ssel sn-ltp1 ancli lttr 3expb sylan2 sylan2i
      exp4b com34 pm2.43d breq1 syl5ibrcom adantl jaod ex syl6 ralimdv2 expimpd
      com23 a2d jcad eleq1 breq2 ralbidv anbi12d spcev exlimdv cbvexvw imbitrdi
      ovex df-rex 3imtr4g imdistani df-3an 3imtr4i axsup syl ) DEUAZDUBUCZBFZAF
      ZGHZWHWIIZUDZBDJZAEKZLZWFWGWJBDJZAEKZLZWIWHGHUEBDJWJWHCFZGHZCDKMBEJNAEKWF
      WGNZWNNXAWQNWOWRXAWNWQWFWNWQMWGWFWIEOZWMNZAPZXBWPNZAPZWNWQWFXDWSEOZWTBDJZ
      NZCPZXFWFXCXJAWFXCWIQRUFZEOZWHXKGHZBDJZNZXJWFXCXLXNXCXLMWFXBXLWMWIUGZSUHW
      FXBWMXNWFXBNZWLXMBDDXQWHDOZWLXMWFXBXRWLXMMZMWFXRXBXSWFXRWHEOZXBXSMDEWHUIX
      TXBXSXTXBNZWJXMWKXTXBWJXMMZXTXBYBXTXBWJXBXMXTXBWJXBXMXBYAWJWIXKGHZXMWIUJZ
      XBXTXBXLNWJYCNXMMZXBXLXPUKXTXBXLYEWHWIXKULUMUNUOUPUQURTXBWKXMMXTXBXMWKYCY
      DWHWIXKGUSUTVAVBVCVDVGTVHVEVFVIXIXOCXKWIQRVRWSXKIZXGXLXHXNWSXKEVJYFWTXMBD
      WSXKWHGVKVLVMVNVDVOXIXECAWSWIIZXGXBXHWPWSWIEVJYGWTWJBDWSWIWHGVKVLVMVPVQWM
      AEVSWPAEVSVTSWAWFWGWNWBWFWGWQWBWCABCDWDWE $.
    $( $j usage 'sn-sup2' avoids 'ax-mulcom'; $)
  $}

  ${
    $d A x y z $.
    sn-sup3d.1 $e |- ( ph -> A C_ RR ) $.
    sn-sup3d.2 $e |- ( ph -> A =/= (/) ) $.
    sn-sup3d.3 $e |- ( ph -> E. x e. RR A. y e. A y <_ x ) $.
    $( ~ sup3 without ~ ax-mulcom , proven trivially from ~ sn-sup2 .
       (Contributed by SN, 29-Jun-2025.) $)
    sn-sup3d $p |- ( ph -> E. x e. RR ( A. y e. A -. x < y /\
      A. y e. RR ( y < x -> E. z e. A y < z ) ) ) $=
      ( cr wss c0 wne cv clt wbr wral wrex wa wb wcel weq wo wn cle ssel expcom
      wi leloe syl9 imp31 ralbidva rexbidva syl mpbid sn-sup2 syl3anc ) AEIJZEK
      LCMZBMZNOZCBUAUBZCEPZBIQZUSURNOUCCEPUTURDMNODEQUGCIPRBIQFGAURUSUDOZCEPZBI
      QZVCHAUQVFVCSFUQVEVBBIUQUSITZRVDVACEUQVGURETZVDVASZUQVHURITZVGVIEIURUEVJV
      GVIURUSUHUFUIUJUKULUMUNBCDEUOUP $.
    $( $j usage 'sn-sup3d' avoids 'ax-mulcom'; $)

    $( ~ suprcld without ~ ax-mulcom , proven trivially from ~ sn-sup3d .
       (Contributed by SN, 29-Jun-2025.) $)
    sn-suprcld $p |- ( ph -> sup ( A , RR , < ) e. RR ) $=
      ( vz cr clt wor ltso a1i sn-sup3d supcl ) ABCHIDJIJKALMABCHDEFGNO $.
    $( $j usage 'sn-suprcld' avoids 'ax-mulcom'; $)

    sn-suprubd.4 $e |- ( ph -> B e. A ) $.
    $( ~ suprubd without ~ ax-mulcom , proven trivially from ~ sn-suprcld .
       (Contributed by SN, 29-Jun-2025.) $)
    sn-suprubd $p |- ( ph -> B <_ sup ( A , RR , < ) ) $=
      ( vz cr clt csup sseldd sn-suprcld wcel wbr wn wor ltso a1i sn-sup3d mpd
      supub nltled ) AEDKLMZADKEFINABCDFGHOAEDPUFELQRIABCJKDELKLSATUAABCJDFGHUB
      UDUCUE $.
    $( $j usage 'sn-suprubd' avoids 'ax-mulcom'; $)
  $}

  $( ~ infm3 depends on ~ leneg and ~ ltneg , so it does not currently seem
     provable without ~ ax-mulcom .  If ` A < B -> -B < -A ` then we have
     ` 0 < -A + B -> 0 < B + -A ` (a commuted addition). $)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Structures
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Avoid axioms in ~ base0 by using the discouraged ~ df-base .  This kind of
     axiom save is probably not worth it.  (Contributed by SN, 16-Sep-2025.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  sn-base0 $p |- (/) = ( Base ` (/) ) $=
    ( cbs c1 df-base str0 ) ABCD $.
  $( $j usage 'sn-base0' avoids 'ax-pow' 'ax-un' 'ax-cnex' 'ax-1cn'
     'ax-addcl'; $)

  ${
    nelsubginvcld.g $e |- ( ph -> G e. Grp ) $.
    nelsubginvcld.s $e |- ( ph -> S e. ( SubGrp ` G ) ) $.
    nelsubginvcld.x $e |- ( ph -> X e. ( B \ S ) ) $.
    nelsubginvcld.b $e |- B = ( Base ` G ) $.

    ${
      nelsubginvcld.p $e |- N = ( invg ` G ) $.
      $( The inverse of a non-subgroup-member is a non-subgroup-member.
         (Contributed by Steven Nguyen, 15-Apr-2023.) $)
      nelsubginvcld $p |- ( ph -> ( N ` X ) e. ( B \ S ) ) $=
        ( cfv cgrp wcel eldifad grpinvcl syl2anc eldifbd wa wceq csubg eqeltrrd
        grpinvinv adantr subginvcl sylan mtand eldifd ) AFELZBCADMNZFBNZUIBNGAF
        BCIOZBDEFJKPQAUICNZFCNAFBCIRAUMSUIELZFCAUNFTZUMAUJUKUOGULBDEFJKUCQUDACD
        UALNUMUNCNHCDEUIKUEUFUBUGUH $.
    $}

    nelsubgcld.y $e |- ( ph -> Y e. S ) $.
    ${
      nelsubgcld.p $e |- .+ = ( +g ` G ) $.
      $( A non-subgroup-member plus a subgroup member is a non-subgroup-member.
         (Contributed by Steven Nguyen, 15-Apr-2023.) $)
      nelsubgcld $p |- ( ph -> ( X .+ Y ) e. ( B \ S ) ) $=
        ( co cgrp wcel eldifad cfv syl3anc adantr csubg wss subgss sseldd grpcl
        syl eldifbd wa wceq eqid grppncan simpr subgsubcl eqeltrrd mtand eldifd
        csg ) AFGCNZBDAEOPZFBPZGBPZURBPHAFBDJQZADBGADEUARPZDBUBIBDEKUCUFLUDZBCE
        FGKMUESAURDPZFDPAFBDJUGAVEUHZURGEUQRZNZFDAVHFUIZVEAUSUTVAVIHVBVDBCEVGFG
        KMVGUJZUKSTVFVCVEGDPZVHDPAVCVEITAVEULAVKVELTDEVGURGVJUMSUNUOUP $.
    $}

    ${
      nelsubgsubcld.p $e |- .- = ( -g ` G ) $.
      $( A non-subgroup-member minus a subgroup member is a
         non-subgroup-member.  (Contributed by Steven Nguyen, 15-Apr-2023.) $)
      nelsubgsubcld $p |- ( ph -> ( X .- Y ) e. ( B \ S ) ) $=
        ( co cminusg cfv cplusg wcel eqid syl2anc cdif eldifad csubg wss subgss
        wceq syl sseldd grpsubval subginvcl nelsubgcld eqeltrd ) AFGENZFGDOPZPZ
        DQPZNZBCUAAFBRGBRUMUQUFAFBCJUBACBGACDUCPRZCBUDIBCDKUEUGLUHBUPDUNEFGKUPS
        ZUNSZMUITABUPCDFUOHIJKAURGCRUOCRILCDUNGUTUJTUSUKUL $.
    $}
  $}

  ${
    $d N x y $.  $d .1. x y $.  $d W x y $.
    rnasclg.a $e |- A = ( algSc ` W ) $.
    rnasclg.o $e |- .1. = ( 1r ` W ) $.
    rnasclg.n $e |- N = ( LSpan ` W ) $.
    $( The set of injected scalars is also interpretable as the span of the
       identity.  (Contributed by Mario Carneiro, 9-Mar-2015.) $)
    rnasclg $p |- ( ( W e. LMod /\ W e. Ring ) -> ran A = ( N ` { .1. } ) ) $=
      ( vx vy clmod wcel crg wa crn cv cvsca cfv wceq cbs eqid co csca wrex cab
      csn asclfval rnmpt ringidcl lspsn sylan2 eqtr4id ) DJKZDLKZMANHOIOBDPQZUA
      ZRIDUBQZSQZUCHUDZBUECQZIHUQUOAIAUNBUPUQDEUPTZUQTZUNTZFUFUGUMULBDSQZKUSURR
      VCDBVCTZFUHHUNIUPUQCVCDBUTVAVDVBGUIUJUK $.
  $}

  ${
    frlmfielbas.f $e |- F = ( R freeLMod I ) $.
    frlmfielbas.n $e |- N = ( Base ` R ) $.
    frlmfielbas.b $e |- B = ( Base ` F ) $.
    $( The vectors of a finite free module are the functions from ` I ` to
       ` N ` .  (Contributed by SN, 31-Aug-2023.) $)
    frlmfielbas $p |- ( ( R e. V /\ I e. Fin ) ->
                                 ( X e. B <-> X : I --> N ) ) $=
      ( wcel cbs cfv cfn wa wf eleq2i cmap co cvv frlmfibas eleq2d fvexi elmapd
      a1i simpr bitr3d bitrid ) GAKGCLMZKZBFKZDNKZOZDEGPZAUIGJQUMGEDRSZKUJUNUMU
      OUIGBCDEFHIUAUBUMEDGTNETKUMEBLIUCUEUKULUFUDUGUH $.
  $}

  ${
    frlmfzwrd.w $e |- W = ( K freeLMod ( 0 ... N ) ) $.
    frlmfzwrd.b $e |- B = ( Base ` W ) $.
    frlmfzwrd.s $e |- S = ( Base ` K ) $.
    $( A vector of a module with indices from 0 to ` N ` is a word over the
       scalars of the module.  (Contributed by SN, 31-Aug-2023.) $)
    frlmfzwrd $p |- ( X e. B -> X e. Word S ) $=
      ( wcel cc0 cfz co wf cword cvv ovex frlmbasf mpan ffz0iswrd syl ) FAJZKDL
      MZBFNZFBOJUCPJUBUDKDLQACEUCBPFGIHRSBDFTUA $.
  $}

  ${
    frlmfzowrd.w $e |- W = ( K freeLMod ( 0 ..^ N ) ) $.
    frlmfzowrd.b $e |- B = ( Base ` W ) $.
    frlmfzowrd.s $e |- S = ( Base ` K ) $.
    $( A vector of a module with indices from 0 to ` N - 1 ` is a word over the
       scalars of the module.  (Contributed by SN, 31-Aug-2023.) $)
    frlmfzowrd $p |- ( X e. B -> X e. Word S ) $=
      ( wcel cc0 cfzo co wf cword cvv ovex frlmbasf mpan iswrdi syl ) FAJZKDLMZ
      BFNZFBOJUCPJUBUDKDLQACEUCBPFGIHRSBDFTUA $.

    $( The dimension of a vector of a module with indices from 0 to ` N - 1 ` .
       (Contributed by SN, 1-Sep-2023.) $)
    frlmfzolen $p |- ( ( N e. NN0 /\ X e. B ) -> ( # ` X ) = N ) $=
      ( cn0 wcel cc0 cfzo co wf chash cfv wceq cvv ovexd frlmbasf sylan syldan
      fnfzo0hash ) DJKZFAKZLDMNZBFOZFPQDRUEUGSKUFUHUELDMTACEUGBSFGIHUAUBBFDUDUC
      $.

    $( The vectors of a module with indices 0 to ` N - 1 ` are the length-
       ` N ` words over the scalars of the module.  (Contributed by SN,
       1-Sep-2023.) $)
    frlmfzowrdb $p |- ( ( K e. V /\ N e. NN0 ) ->
                         ( X e. B <-> ( X e. Word S /\ ( # ` X ) = N ) ) ) $=
      ( wcel cn0 wa cword chash wi cc0 cfzo co wf cfv frlmfzowrd a1i frlmfzolen
      wceq ex adantl jcad w3a simp3l syl simp3r oveq2d feq2d mpbid cfn wb simp1
      wrdf fzofi frlmfielbas sylancl mpbird 3expia impbid ) CEKZDLKZMZGAKZGBNKZ
      GOUAZDUEZMZVHVIVJVLVIVJPVHABCDFGHIJUBUCVGVIVLPVFVGVIVLABCDFGHIJUDUFUGUHVF
      VGVMVIVFVGVMUIZVIQDRSZBGTZVNQVKRSZBGTZVPVNVJVRVFVGVJVLUJBGUSUKVNVQVOBGVNV
      KDQRVFVGVJVLULUMUNUOVNVFVOUPKVIVPUQVFVGVMURQDUTACFVOBEGHJIVAVBVCVDVE $.
  $}

  ${
    frlmfzoccat.w $e |- W = ( K freeLMod ( 0 ..^ L ) ) $.
    frlmfzoccat.x $e |- X = ( K freeLMod ( 0 ..^ M ) ) $.
    frlmfzoccat.y $e |- Y = ( K freeLMod ( 0 ..^ N ) ) $.
    frlmfzoccat.b $e |- B = ( Base ` W ) $.
    frlmfzoccat.c $e |- C = ( Base ` X ) $.
    frlmfzoccat.d $e |- D = ( Base ` Y ) $.
    frlmfzoccat.k $e |- ( ph -> K e. Z ) $.
    frlmfzoccat.l $e |- ( ph -> ( M + N ) = L ) $.
    frlmfzoccat.m $e |- ( ph -> M e. NN0 ) $.
    frlmfzoccat.n $e |- ( ph -> N e. NN0 ) $.
    frlmfzoccat.u $e |- ( ph -> U e. C ) $.
    frlmfzoccat.v $e |- ( ph -> V e. D ) $.
    $( The concatenation of two vectors of dimension ` N ` and ` M ` forms a
       vector of dimension ` N + M ` .  (Contributed by SN, 31-Aug-2023.) $)
    frlmfzoccat $p |- ( ph -> ( U ++ V ) e. B ) $=
      ( cconcat co wcel cbs cfv cword chash wceq eqid frlmfzowrd ccatcl syl2anc
      syl caddc ccatlen cn0 cc0 wf cvv ovexd frlmbasf fnfzo0hash oveq12d 3eqtrd
      cfzo wa wb nn0addcld eqeltrrd frlmfzowrdb mpbir2and ) AEJUGUHZBUIZVRFUJUK
      ZULZUIZVRUMUKZGUNZAEWAUIZJWAUIZWBAECUIZWEUECVTFHLEPSVTUOZUPUSZAJDUIZWFUFD
      VTFIMJQTWHUPUSZVTEJUQURAWCEUMUKZJUMUKZUTUHZHIUTUHZGAWEWFWCWNUNWIWKVTVTEJV
      AURAWLHWMIUTAHVBUIVCHVKUHZVTEVDZWLHUNUCAWPVEUIWGWQAVCHVKVFUECFLWPVTVEEPWH
      SVGURVTEHVHURAIVBUIVCIVKUHZVTJVDZWMIUNUDAWRVEUIWJWSAVCIVKVFUFDFMWRVTVEJQW
      HTVGURVTJIVHURVIUBVJAFNUIGVBUIVSWBWDVLVMUAAWOGVBUBAHIUCUDVNVOBVTFGNKVRORW
      HVPURVQ $.

    $d x ph $.  $d x A $.  $d x L $.  $d x M $.  $d x N $.
    frlmvscadiccat.o $e |- O = ( .s ` W ) $.
    frlmvscadiccat.p $e |- .xb = ( .s ` X ) $.
    frlmvscadiccat.q $e |- .x. = ( .s ` Y ) $.
    frlmvscadiccat.s $e |- S = ( Base ` K ) $.
    frlmvscadiccat.a $e |- ( ph -> A e. S ) $.
    $( Scalar multiplication distributes over concatenation.  (Contributed by
       SN, 6-Sep-2023.) $)
    frlmvscadiccat $p |- ( ph ->
      ( A O ( U ++ V ) ) = ( ( A .xb U ) ++ ( A .x. V ) ) ) $=
      ( vx cc0 cfzo co csn cxp cconcat cmulr cfv cof wcel wf fconstg ffnd chash
      syl caddc cword iswrdi 3syl ccatvalfn syl2anc cmul wceq fzofi snfi hashxp
      wfn cfn mp2an c1 hashsng oveq2d cn0 hashcl nn0cnd mulridd hashfzo0 3eqtrd
      mp1i eqtrid oveq12d eqtrd fneq2d mpbid cv wa clt cmin adantr breq2d ifbid
      wbr cif cuz cz elfzouz ad2antlr ad2antrr nn0zd elfzo2 syl3anbrc fvconst2g
      simpr syl2an2r wn cle elfzonn0 nn0red elfzoelz adantl zred lenltd biimpar
      nn0sub2 syl3anc recnd 3eqtr4d frlmfzowrd cvv frlmbasf hashfn frlmvscafval
      ovexd elnn0uz sylib elfzolt2 pncan3d 3brtr4d ltadd2d mpbird ifeqda eqtr2d
      resubcld eqeltrd sylan ccatsymb eqfnfvd oveq1d eqtr4d ofccat frlmfzoccat
      eqid ) AURKUSUTZBVAZVBZIOVCUTZJVDVEZVFZUTZURLUSUTZUVAVBZIUVEUTZURMUSUTZUV
      AVBZOUVEUTZVCUTZBUVCNUTBIGUTZBOHUTZVCUTAUVFUVHUVKVCUTZUVCUVEUTUVMAUVBUVPU
      VCUVEAUQUUTUVBUVPAUUTUVAUVBABFVGZUUTUVAUVBVHUPUUTBFVIVLVJAUVPURUVHVKVEZUV
      KVKVEZVMUTZUSUTZWDZUVPUUTWDAUVHUVAVNZVGZUVKUWCVGZUWBAUVQUVGUVAUVHVHZUWDUP
      UVGBFVIZUVALUVHVOZVPZAUVQUVJUVAUVKVHZUWEUPUVJBFVIZUVAMUVKVOZVPZUVHUVKUVAV
      QVRAUWAUUTUVPAUVTKURUSAUVTLMVMUTZKAUVRLUVSMVMAUVRUVGVKVEZUVAVKVEZVSUTZLUV
      GWEVGZUVAWEVGZUVRUWQVTURLWAZBWBZUVGUVAWCWFZAUWQUWOWGVSUTZUWOLAUWPWGUWOVSA
      UVQUWPWGVTUPBFWHVLZWIZAUWOAUWOUWRUWOWJVGAUWTUVGWKWPWLWMZALWJVGZUWOLVTUHLW
      NVLWOWQZAUVSUVJVKVEZUWPVSUTZMUVJWEVGZUWSUVSUXJVTURMWAZUXAUVJUVAWCWFZAUXJU
      XIWGVSUTZUXIMAUWPWGUXIVSUXDWIZAUXIAUXIUXKUXIWJVGAUXLUVJWKWPWLWMZAMWJVGZUX
      IMVTUIMWNVLWOWQWRUGWSWIWTXAAUQXBZUUTVGZXCZBUXRUVRXDXIZUXRUVHVEZUXRUVRXEUT
      ZUVKVEZXJZUXRUVBVEZUXRUVPVEZUXTUYEUXRLXDXIZUYBUYDXJBUXTUYAUYHUYBUYDUXTUVR
      LUXRXDAUVRLVTZUXSUXHXFXGXHUXTUYHUYBUYDBUXTUVQUYHUXRUVGVGZUYBBVTAUVQUXSUPX
      FZUXTUYHXCZUXRURXKVEZVGZLXLVGUYHUYJUXSUYNAUYHUXRURKXMXNUYLLAUXGUXSUYHUHXO
      XPUXTUYHXTUXRURLXQXRUVGBUXRFXSYAUXTUVQUYHYBZUYCUVJVGUYDBVTUYKUXTUYOXCZUYC
      UXRLXEUTZUVJUYPUVRLUXRXEAUYIUXSUYOUXHXOWIUYPUYQUYMVGZMXLVGUYQMXDXIZUYQUVJ
      VGUYPUYQWJVGZUYRUYPUXGUXRWJVGZLUXRYCXIZUYTAUXGUXSUYOUHXOUXSVUAAUYOUXRKYDX
      NUXTVUBUYOUXTLUXRUXTLAUXGUXSUHXFYEZUXTUXRUXSUXRXLVGZAUXRURKYFYGZYHZYIYJLU
      XRYKYLUYQUUAUUBUYPMAUXQUXSUYOUIXOXPUXTUYSUYOUXTUYSLUYQVMUTZUWNXDXIUXTUXRK
      VUGUWNXDUXSUXRKXDXIAUXRURKUUCYGUXTLUXRUXTLVUCYMUXTUXRVUFYMUUDAUWNKVTUXSUG
      XFUUEUXTUYQMLUXTUXRLVUFVUCUUJUXTMAUXQUXSUIXFYEVUCUUFUUGXFUYQURMXQXRUUKUVJ
      BUYCFXSYAUUHUUIAUVQUXSUYFBVTUPUUTBUXRFXSUULUXTUWDUWEVUDUYGUYEVTUXTUVQUWFU
      WDUYKUWGUWHVPUXTUVQUWJUWEUYKUWKUWLVPVUEUVHUVKUXRUVAUUMYLYNUUNUUOAUVDUVAFU
      VHUVKIOUWIUWMAIDVGZIFVNZVGUJDFJLQIUAUDUOYOVLAOEVGZOVUIVGUKEFJMROUBUEUOYOV
      LAUXCUWOUVRIVKVEZUXFAUVRUWQUXCUXBUXEWQAIUVGWDVUKUWOVTAUVGFIAUVGYPVGVUHUVG
      FIVHAURLUSYTZUJDJQUVGFYPIUAUOUDYQVRVJUVGIYRVLYNAUVSUXIOVKVEZAUVSUXJUXIUXM
      AUXJUXNUXIUXOUXPWSWQAOUVJWDVUMUXIVTAUVJFOAUVJYPVGVUJUVJFOVHAURMUSYTZUKEJR
      UVJFYPOUBUOUEYQVRVJUVJOYRVLUUPUUQWSABCJNUVDUUTFYPUVCPTUCUOAURKUSYTUPACDEI
      JKLMOPQRSTUAUBUCUDUEUFUGUHUIUJUKUURULUVDUUSZYSAUVNUVIUVOUVLVCABDJGUVDUVGF
      YPIQUAUDUOVULUPUJUMVUOYSABEJHUVDUVJFYPORUBUEUOVUNUPUKUNVUOYSWRYN $.
  $}

  ${
    grpasscan2d.b $e |- B = ( Base ` G ) $.
    grpasscan2d.p $e |- .+ = ( +g ` G ) $.
    grpasscan2d.n $e |- N = ( invg ` G ) $.
    grpasscan2d.g $e |- ( ph -> G e. Grp ) $.
    grpasscan2d.1 $e |- ( ph -> X e. B ) $.
    grpasscan2d.2 $e |- ( ph -> Y e. B ) $.
    $( An associative cancellation law for groups.  (Contributed by SN,
       29-Jan-2025.) $)
    grpasscan2d $p |- ( ph -> ( ( X .+ ( N ` Y ) ) .+ Y ) = X ) $=
      ( cgrp wcel cfv co wceq grpasscan2 syl3anc ) ADNOFBOGBOFGEPCQGCQFRKLMBCDE
      FGHIJST $.
  $}

  ${
    grpcominv.b $e |- B = ( Base ` G ) $.
    grpcominv.p $e |- .+ = ( +g ` G ) $.
    grpcominv.n $e |- N = ( invg ` G ) $.
    grpcominv.g $e |- ( ph -> G e. Grp ) $.
    grpcominv.x $e |- ( ph -> X e. B ) $.
    grpcominv.y $e |- ( ph -> Y e. B ) $.
    grpcominv.1 $e |- ( ph -> ( X .+ Y ) = ( Y .+ X ) ) $.
    $( If two elements commute, then they commute with each other's inverses
       (case of the first element commuting with the inverse of the second
       element).  (Contributed by SN, 29-Jan-2025.) $)
    grpcominv1 $p |- ( ph -> ( X .+ ( N ` Y ) ) = ( ( N ` Y ) .+ X ) ) $=
      ( cfv co wceq grpassd 3eqtr4rd wcel grpinvcld c0g grplinvd oveq1d grplidd
      eqid eqtr2d oveq2d grpasscan2d cgrp wb grpcld grprcan syl13anc mpbid ) AF
      GEOZCPZGCPZUPFCPZGCPZQZUQUSQZAUPFGCPZCPZFUTURAUPGCPZFCPZUPGFCPZCPFVDABCDU
      PGFHIKABDEGHJKMUAZMLRAVFDUBOZFCPFAVEVIFCABCDEGVIHIVIUFZJKMUCUDABCDFVIHIVJ
      KLUEUGAVCVGUPCNUHSABCDUPFGHIKVHLMRABCDEFGHIJKLMUISADUJTUQBTUSBTGBTVAVBUKK
      ABCDFUPHIKLVHULABCDUPFHIKVHLULMBCDUQUSGHIUMUNUO $.

    $( If two elements commute, then they commute with each other's inverses
       (case of the second element commuting with the inverse of the first
       element).  (Contributed by SN, 1-Feb-2025.) $)
    grpcominv2 $p |- ( ph -> ( Y .+ ( N ` X ) ) = ( ( N ` X ) .+ Y ) ) $=
      ( co eqcomd grpcominv1 ) ABCDEGFHIJKMLAFGCOGFCONPQ $.
  $}

  ${
    $d S a $.  $d G a $.  $d ph a $.
    finsubmsubg.b $e |- B = ( Base ` G ) $.
    finsubmsubg.g $e |- ( ph -> G e. Grp ) $.
    finsubmsubg.s $e |- ( ph -> S e. ( SubMnd ` G ) ) $.
    finsubmsubg.1 $e |- ( ph -> B e. Fin ) $.
    $( A submonoid of a finite group is a subgroup.  This does not extend to
       infinite groups, as the submonoid ` NN0 ` of the group ` ( ZZ , + ) `
       shows.  Note also that the union of a submonoid and its inverses need
       not be a submonoid, as the submonoid ` ( NN0 \ { 1 } ) ` of the group
       ` ( ZZ , + ) ` shows: 3 is in that submonoid, -2 is the inverse of 2,
       but 1 is not in their union.  Or simply, the subgroup generated by
       ` ( NN0 \ { 1 } ) ` is ` ZZ ` , not ` ( ZZ \ { 1 , -u 1 } ) ` .
       (Contributed by SN, 31-Jan-2025.) $)
    finsubmsubg $p |- ( ph -> S e. ( SubGrp ` G ) ) $=
      ( va cod cfv eqid cv cn wcel wa cgrp cfn adantr csubmnd wss submss sselda
      syl odcl2 syl3anc ralrimiva finodsubmsubg ) ACDDJKZIUILZFGAIMZUIKNOZICAUK
      COZPDQOZBROZUKBOULAUNUMFSAUOUMHSACBUKACDTKOCBUAGBCDEUBUDUCUKDUIBEUJUEUFUG
      UH $.
  $}

  ${
    opprgrp.o $e |- O = ( oppR ` R ) $.
    $( A class is a monoid if and only if its opposite (ring) is a monoid.
       (Contributed by SN, 20-Jun-2025.) $)
    opprmndb $p |- ( R e. Mnd <-> O e. Mnd ) $=
      ( baseid basendxnmulrndx opprlem cplusg plusgid plusgndxnmulrndx mndprop
      cbs ) ABAKBCDEFAGBCHIFJ $.

    $( A class is a group if and only if its opposite (ring) is a group.
       (Contributed by SN, 20-Jun-2025.) $)
    opprgrpb $p |- ( R e. Grp <-> O e. Grp ) $=
      ( baseid basendxnmulrndx opprlem cplusg plusgid plusgndxnmulrndx grpprop
      cbs ) ABAKBCDEFAGBCHIFJ $.

    $( A class is an Abelian group if and only if its opposite (ring) is an
       Abelian group.  (Contributed by SN, 20-Jun-2025.) $)
    opprablb $p |- ( R e. Abel <-> O e. Abel ) $=
      ( baseid basendxnmulrndx opprlem cplusg plusgid plusgndxnmulrndx ablprop
      cbs ) ABAKBCDEFAGBCHIFJ $.
  $}

  ${
    $d C a b x y $.  $d F a b $.  $d M a b $.  $d S a b $.  $d ph a b x y $.
    imacrhmcl.c $e |- C = ( N |`s ( F " S ) ) $.
    imacrhmcl.h $e |- ( ph -> F e. ( M RingHom N ) ) $.
    imacrhmcl.m $e |- ( ph -> M e. CRing ) $.
    imacrhmcl.s $e |- ( ph -> S e. ( SubRing ` M ) ) $.
    $( The image of a commutative ring homomorphism is a commutative ring.
       (Contributed by SN, 10-Jan-2025.) $)
    imacrhmcl $p |- ( ph -> C e. CRing ) $=
      ( vx vy va vb wcel cfv co wceq wa eqid crg cv cmulr wral ccrg cima csubrg
      cbs crh rhmima syl2anc subrgring syl ressbasss2 anim12i wrex wfun wf rhmf
      sseli ffund fvelima sylan adantrr adantrl adantr ad3antrrr subrgss sseldd
      simplrl simprl crngcom syl3anc fveq2d rhmmul 3eqtr3d imaexg ressmulr 3syl
      wss simplrr simprr oveq123d rexlimddv sylan2 ralrimivva iscrng2 sylanbrc
      cvv ) ABUAOZKUBZLUBZBUCPZQZWLWKWMQZRZLBUHPZUDKWQUDBUEOADCUFZFUGPOZWJADEFU
      IQZOZCEUGPOZWSHJDEFCUJUKWRFBGULUMAWPKLWQWQWKWQOZWLWQOZSAWKWROZWLWROZSZWPX
      CXEXDXFWQWRWKWRBFGUNZUTWQWRWLXHUTUOAXGSZMUBZDPZWKRZWPMCAXEXLMCUPZXFADUQZX
      EXMAEUHPZFUHPZDAXAXOXPDURHXOXPEFDXOTZXPTUSUMVAZMWKCDVBVCVDXIXJCOZXLSZSZNU
      BZDPZWLRZWPNCXIYDNCUPZXTAXFYEXEAXNXFYEXRNWLCDVBVCVEVFYAYBCOZYDSZSZXKYCFUC
      PZQZYCXKYIQZWNWOYHXJYBEUCPZQZDPZYBXJYLQZDPZYJYKYHYMYODYHEUEOZXJXOOZYBXOOZ
      YMYORAYQXGXTYGIVGYHCXOXJACXOVTZXGXTYGAXBYTJCXOEXQVHUMVGZXIXSXLYGVJVIZYHCX
      OYBUUAYAYFYDVKVIZXOEYLXJYBXQYLTZVLVMVNYHXAYRYSYNYJRAXAXGXTYGHVGZUUBUUCXJY
      BEFYLYIDXOXQUUDYITZVOVMYHXAYSYRYPYKRUUEUUCUUBYBXJEFYLYIDXOXQUUDUUFVOVMVPY
      HXKWKYCWLYIWMAYIWMRZXGXTYGAXAWRWIOUUGHDCWTVQWRFBYIWIGUUFVRVSVGZXIXSXLYGWA
      ZYAYFYDWBZWCYHYCWLXKWKYIWMUUHUUJUUIWCVPWDWDWEWFKLWQBWMWQTWMTWGWH $.
  $}

  ${
    $d R f $.  $d S f $.
    $( Ring isomorphism preserves (multiplicative) commutativity.  (Contributed
       by SN, 10-Jan-2025.) $)
    riccrng1 $p |- ( ( R ~=r S /\ R e. CRing ) -> S e. CRing ) $=
      ( vf cric wbr cv crs co wcel wex ccrg c0 cbs cfv wceq eqid crg syl adantr
      cress wne brric n0 bitri wi cima wf1o wfo rimf1o f1ofo foima 3syl rimrcl2
      wa oveq2d ressid eqtr2d crh rimrhm simpr csubrg crngringd subrgid eqeltrd
      imacrhmcl ex exlimiv imp sylanb ) ABDEZCFZABGHZIZCJZAKIZBKIZVJVLLUAVNABUB
      CVLUCUDVNVOVPVMVOVPUECVMVOVPVMVOUNZBBVKAMNZUFZTHZKVMBVTOVOVMVTBBMNZTHZBVM
      VSWABTVMVRWAVKUGVRWAVKUHVSWAOVRWAABVKVRPZWAPZUIVRWAVKUJVRWAVKUKULUOVMBQIW
      BBOABVKUMWABQWDUPRUQSVQVTVRVKABVTPVMVKABURHIVOABVKUSSVMVOUTZVQAQIVRAVANIV
      QAWEVBVRAWCVCRVEVDVFVGVHVI $.
  $}

  $( A ring is commutative if and only if an isomorphic ring is commutative.
     (Contributed by SN, 10-Jan-2025.) $)
  riccrng $p |- ( R ~=r S -> ( R e. CRing <-> S e. CRing ) ) $=
    ( cric wbr ccrg wcel riccrng1 ricsym sylan impbida ) ABCDZAEFZBEFZABGKBACDM
    LABHBAGIJ $.

  ${
    $d N x $.  $d ph x y $.  $d .^ x y $.  $d X x y $.  $d .0. x y $.
    domnexpgn0cl.b $e |- B = ( Base ` R ) $.
    domnexpgn0cl.0 $e |- .0. = ( 0g ` R ) $.
    domnexpgn0cl.e $e |- .^ = ( .g ` ( mulGrp ` R ) ) $.
    domnexpgn0cl.r $e |- ( ph -> R e. Domn ) $.
    domnexpgn0cl.n $e |- ( ph -> N e. NN0 ) $.
    domnexpgn0cl.x $e |- ( ph -> X e. ( B \ { .0. } ) ) $.
    $( In a domain, a (nonnegative) power of a nonzero element is nonzero.
       (Contributed by SN, 6-Jul-2024.) $)
    domnexpgn0cl $p |- ( ph -> ( N .^ X ) e. ( B \ { .0. } ) ) $=
      ( co wcel wne wceq oveq1 neeq1d ad2antrr vx vy cmgp cfv eqid mgpbas cdomn
      crg cmnd domnring ringmgp 3syl csn eldifad mulgnn0cld cn0 cv cc0 c1 caddc
      weq cur ringidval mulg0 syl cnzr domnnzr nzrnz eqnetrd wa simplr mgpplusg
      cmulr mulgnn0p1 syl3anc simpr eldifsni domnmuln0 syl122anc mpdan eldifsnd
      cdif nn0indd ) AEFDNZBGABDCUCUDZEFBCWEWEUEZHUFZJACUGOZCUHOWEUIOZKCUJCWEWF
      UKULZLAFBGUMZMUNZUOAEUPOWDGPZLAUAUQZFDNZGPURFDNZGPUBUQZFDNZGPZWQUSUTNZFDN
      ZGPWMUAUBEWNURQWOWPGWNURFDRSUAUBVAWOWRGWNWQFDRSWNWTQWOXAGWNWTFDRSWNEQWOWD
      GWNEFDRSAWPCVBUDZGAFBOZWPXBQWLBDWEFXBWGCXBWEWFXBUEZVCJVDVEAWHCVFOXBGPKCVG
      CXBGXDIVHULVIAWQUPOZVJZWSVJZXAWRFCVMUDZNZGXGWIXEXCXAXIQAWIXEWSWJTZAXEWSVK
      ZAXCXEWSWLTZBXHDWEWQFWGJCXHWEWFXHUEZVLVNVOXGWHWRBOWSXCFGPZXIGPAWHXEWSKTXG
      BDWEWQFWGJXJXKXLUOXFWSVPXLAXNXEWSAFBWKWBOXNMFBGVQVETBCXHWRFGHXMIVRVSVIWCV
      TWA $.
  $}

  ${
    drnginvrn0d.b $e |- B = ( Base ` R ) $.
    drnginvrn0d.0 $e |- .0. = ( 0g ` R ) $.
    drnginvrn0d.i $e |- I = ( invr ` R ) $.
    drnginvrn0d.r $e |- ( ph -> R e. DivRing ) $.
    drnginvrn0d.x $e |- ( ph -> X e. B ) $.
    drnginvrn0d.1 $e |- ( ph -> X =/= .0. ) $.
    $( A multiplicative inverse in a division ring is nonzero.  ( ~ recne0d
       analog).  (Contributed by SN, 14-Aug-2024.) $)
    drnginvrn0d $p |- ( ph -> ( I ` X ) =/= .0. ) $=
      ( cdr wcel wne cfv drnginvrn0 syl3anc ) ACMNEBNEFOEDPFOJKLBCDEFGHIQR $.
  $}

  ${
    drngmullcan.b $e |- B = ( Base ` R ) $.
    drngmullcan.0 $e |- .0. = ( 0g ` R ) $.
    drngmullcan.t $e |- .x. = ( .r ` R ) $.
    drngmullcan.r $e |- ( ph -> R e. DivRing ) $.
    drngmullcan.x $e |- ( ph -> X e. B ) $.
    drngmullcan.y $e |- ( ph -> Y e. B ) $.
    drngmullcan.z $e |- ( ph -> Z e. B ) $.
    drngmullcan.1 $e |- ( ph -> Z =/= .0. ) $.
    ${
      drngmullcan.2 $e |- ( ph -> ( Z .x. X ) = ( Z .x. Y ) ) $.
      $( Cancellation of a nonzero factor on the left for multiplication.
         ( ~ mulcanad analog).  (Contributed by SN, 14-Aug-2024.)  (Proof
         shortened by SN, 25-Jun-2025.) $)
      drngmullcan $p |- ( ph -> X = Y ) $=
        ( eldifsnd cdr wcel cdomn drngdomn syl domnlcan ) ABCDHEGFIJKAHBGOPRMNA
        CSTCUATLCUBUCQUD $.
    $}

    ${
      drngmulrcan.2 $e |- ( ph -> ( X .x. Z ) = ( Y .x. Z ) ) $.
      $( Cancellation of a nonzero factor on the right for multiplication.
         ( ~ mulcan2ad analog).  (Contributed by SN, 14-Aug-2024.)  (Proof
         shortened by SN, 25-Jun-2025.) $)
      drngmulrcan $p |- ( ph -> X = Y ) $=
        ( eldifsnd cdr wcel cdomn drngdomn syl domnrcan ) ABCDEFGHIJKMNAHBGOPRA
        CSTCUATLCUBUCQUD $.
    $}
  $}

  ${
    drnginvmuld.b $e |- B = ( Base ` R ) $.
    drnginvmuld.z $e |- .0. = ( 0g ` R ) $.
    drnginvmuld.t $e |- .x. = ( .r ` R ) $.
    drnginvmuld.i $e |- I = ( invr ` R ) $.
    drnginvmuld.r $e |- ( ph -> R e. DivRing ) $.
    drnginvmuld.x $e |- ( ph -> X e. B ) $.
    drnginvmuld.y $e |- ( ph -> Y e. B ) $.
    drnginvmuld.1 $e |- ( ph -> X =/= .0. ) $.
    drnginvmuld.2 $e |- ( ph -> Y =/= .0. ) $.
    $( Inverse of a nonzero product.  (Contributed by SN, 14-Aug-2024.) $)
    drnginvmuld $p |-
      ( ph -> ( I ` ( X .x. Y ) ) = ( ( I ` Y ) .x. ( I ` X ) ) ) $=
      ( co cfv wne drngringd ringcld drngmulne0 drnginvrcld cur eqid drnginvrld
      mpbir2and oveq1d eqtrd oveq2d eqcomd ringassd 3eqtr3d 3eqtr4d drngmulrcan
      ringlidmd ) ABCDFGDRZESZGESZFESZDRZHURIJKMABCEURHIJLMABCDFGIKACMUAZNOUBZA
      URHTFHTGHTPQABCDFGHIJKMNOUCUHZUDABCDUTVAIKVCABCEGHIJLMOQUDZABCEFHIJLMNPUD
      ZUBVDVEACUESZUTVAURDRZDRZUSURDRVBURDRAUTGDRZUTVAFDRZGDRZDRZVHVJAVNVKAVMGU
      TDAVMVHGDRGAVLVHGDABCDVHEFHIJKVHUFZLMNPUGUIABCDVHGIKVOVCOUQUJUKULABCDVHEG
      HIJKVOLMOQUGAVMVIUTDABCDVAFGIKVCVGNOUMUKUNABCDVHEURHIJKVOLMVDVEUGABCDUTVA
      URIKVCVFVGVDUMUOUP $.
  $}

  ${
    $d R f $.  $d S f $.
    $( A ring isomorphism maps a division ring to a division ring.
       (Contributed by SN, 18-Feb-2025.) $)
    ricdrng1 $p |- ( ( R ~=r S /\ R e. DivRing ) -> S e. DivRing ) $=
      ( vf co wcel cdr wne wi wa cbs cfv cress wceq eqid 3syl crg adantr adantl
      syl c0g cric wbr cv crs wex c0 brric n0 bitri cima wfo rimf1o f1ofo foima
      wf1o oveq2d rimrcl2 ressid eqtr2d crh rimrhm csdrg sdrgid crn csn forn wn
      cur rhmrcl2 ringidcl drngunz wf1 drngring ring0cl jca f1veqaeq syl2an imp
      f1of1 mteqand rhm1 rhmghm ghmid 3netr3d nelne1 syl2an2r eqnetrd imadrhmcl
      cghm nelsn eqeltrd ex exlimiv sylanb ) ABUAUBZCUCZABUDDZEZCUEZAFEZBFEZWOW
      QUFGWSABUGCWQUHUIWSWTXAWRWTXAHCWRWTXAWRWTIZBBWPAJKZUJZLDZFWRBXEMWTWRXEBBJ
      KZLDZBWRXDXFBLWRXCXFWPUOZXCXFWPUKZXDXFMXCXFABWPXCNZXFNZULZXCXFWPUMZXCXFWP
      UNOUPWRBPEZXGBMABWPUQXFBPXKURSUSQXBXEXCWPABBTKZXENXONZWRWPABUTDEZWTABWPVA
      ZQZWTXCAVBKEWRXCAXJVCRXBWPVDZXFXOVEZWRXTXFMZWTWRXHXIYBXLXMXCXFWPVFOQWRBVH
      KZXFEZWTYCYAEVGZXFYAGWRXQXNYDXRABWPVIXFBYCXKYCNZVJOXBYCXOGYEXBAVHKZWPKZAT
      KZWPKZYCXOXBYHYJYGYIWTYGYIGWRAYGYIYINZYGNZVKRXBYHYJMZYGYIMZWRXCXFWPVLZYGX
      CEZYIXCEZIYMYNHWTWRXHYOXLXCXFWPVSSWTYPYQWTAPEZYPAVMZXCAYGXJYLVJSWTYRYQYSX
      CAYIXJYKVNSVOXCXFYGYIWPVPVQVRVTXBXQYHYCMXSABYGWPYCYLYFWASXBXQWPABWIDEYJXO
      MXSABWPWBABWPYIXOYKXPWCOWDYCXOWJSYCXFYAWEWFWGWHWKWLWMVRWN $.
  $}

  $( A ring is a division ring if and only if an isomorphic ring is a division
     ring.  (Contributed by SN, 18-Feb-2025.) $)
  ricdrng $p |- ( R ~=r S -> ( R e. DivRing <-> S e. DivRing ) ) $=
    ( cric wbr cdr wcel ricdrng1 ricsym sylan impbida ) ABCDZAEFZBEFZABGKBACDML
    ABHBAGIJ $.

  $( A ring is a field if and only if an isomorphic ring is a field.
     (Contributed by SN, 18-Feb-2025.) $)
  ricfld $p |- ( R ~=r S -> ( R e. Field <-> S e. Field ) ) $=
    ( cric wbr cdr wcel ccrg wa cfield ricdrng riccrng anbi12d isfld 3bitr4g )
    ABCDZAEFZAGFZHBEFZBGFZHAIFBIFOPRQSABJABKLAMBMN $.

  ${
    $d W s $.  $d A s $.  $d B s $.  $d S s $.  $d K s $.  $d N s $.
    $d .0. s $.
    asclf1.a $e |- A = ( algSc ` W ) $.
    asclf1.b $e |- B = ( Base ` W ) $.
    asclf1.s $e |- S = ( Scalar ` W ) $.
    asclf1.k $e |- K = ( Base ` S ) $.
    asclf1.0 $e |- .0. = ( 0g ` W ) $.
    asclf1.n $e |- N = ( 0g ` S ) $.
    asclf1.r $e |- ( ph -> W e. Ring ) $.
    asclf1.m $e |- ( ph -> W e. LMod ) $.
    $( Two ways of saying the scalar injection is one-to-one.  (Contributed by
       SN, 3-Jul-2025.) $)
    asclf1 $p |- ( ph ->
      ( A : K -1-1-> B <-> A. s e. K ( ( A ` s ) = .0. -> s = N ) ) ) $=
      ( cghm co wceq wcel wf1 cv cfv wi wral wb asclghm ghmf1 syl ) ABDGRSUAECB
      UBIUCZBUDHTUKFTUEIEUFUGABDGJLPQUHIECDGBFHMKONUIUJ $.
  $}

  $( Using ~ asclf1 we can derive an isomorphism between ` R ` and the
     equivalence classes of constant polynomials modulo some polynomial, which
     forms a field that ` ( R polyFld P ) ` extends. $)

  ${
    $d ph x y $.  $d .^ x y $.  $d F x y $.  $d X x y $.  $d N x y $.
    abvexp.a $e |- A = ( AbsVal ` R ) $.
    abvexp.e $e |- .^ = ( .g ` ( mulGrp ` R ) ) $.
    abvexp.b $e |- B = ( Base ` R ) $.
    abvexp.r $e |- ( ph -> R e. NzRing ) $.
    abvexp.f $e |- ( ph -> F e. A ) $.
    abvexp.x $e |- ( ph -> X e. B ) $.
    abvexp.n $e |- ( ph -> N e. NN0 ) $.
    $( Move exponentiation in and out of absolute value.  (Contributed by SN,
       3-Jul-2025.) $)
    abvexp $p |- ( ph -> ( F ` ( N .^ X ) ) = ( ( F ` X ) ^ N ) ) $=
      ( wcel co cfv cexp wceq vx vy cn0 cv cc0 c1 caddc fvoveq1 eqeq12d weq cur
      oveq2 c0g wne cnzr eqid nzrnz abv1z syl2anc mgpbas ringidval mulg0 fveq2d
      syl cmgp cr abvcl recnd exp0d 3eqtr4d wa cmulr cmul ad2antrr cmnd nzrring
      ringmgp 3syl simplr mulgnn0cld abvmul syl3anc simpr oveq1d eqtrd mgpplusg
      crg mulgnn0p1 cc expp1d nn0indd mpdan ) AGUCPGHEQFRZHFRZGSQZTZOAUAUDZHEQF
      RZWNWQSQZTUEHEQZFRZWNUESQZTUBUDZHEQZFRZWNXCSQZTZXCUFUGQZHEQZFRZWNXHSQZTWP
      UAUBGWQUETWRXAWSXBWQUEHFEUHWQUEWNSULUIUAUBUJWRXEWSXFWQXCHFEUHWQXCWNSULUIW
      QXHTWRXJWSXKWQXHHFEUHWQXHWNSULUIWQGTWRWMWSWOWQGHFEUHWQGWNSULUIADUKRZFRZUF
      XAXBAFBPZXLDUMRZUNZXMUFTMADUOPZXPLDXLXOXLUPZXOUPZUQVDBDXLFXOIXRXSURUSAWTX
      LFAHCPZWTXLTNCEDVERZHXLCDYAYAUPZKUTZDXLYAYBXRVAJVBVDVCAWNAWNAXNXTWNVFPMNB
      CDFHIKVGUSVHZVIVJAXCUCPZVKZXGVKZXDHDVLRZQZFRZXFWNVMQZXJXKYGYJXEWNVMQZYKYG
      XNXDCPXTYJYLTAXNYEXGMVNYGCEYAXCHYCJAYAVOPZYEXGAXQDWGPYMLDVPDYAYBVQVRVNZAY
      EXGVSZAXTYEXGNVNZVTYPBCDYHFXDHIKYHUPZWAWBYGXEXFWNVMYFXGWCWDWEYGXIYIFYGYMY
      EXTXIYITYNYOYPCYHEYAXCHYCJDYHYAYBYQWFWHWBVCYGWNXCAWNWIPYEXGYDVNYOWJVJWKWL
      $.
  $}

  ${
    $d .x. o p q r $.  $d A o p q r $.  $d ph o p q r $.
    fimgmcyclem.s $e |- ( ph ->
            E. o e. NN E. q e. NN ( o =/= q /\ ( o .x. A ) = ( q .x. A ) ) ) $.
    $( Lemma for ~ fimgmcyc .  (Contributed by SN, 7-Jul-2025.) $)
    fimgmcyclem $p |-
      ( ph -> E. o e. NN E. q e. NN ( o < q /\ ( o .x. A ) = ( q .x. A ) ) ) $=
      ( vp vr cv clt wbr co wceq wa cn wrex weq oveq1 anbi12d cbvrexvw simpr wo
      rexcom eqcom anbi2i 2rexbii sylbb breq2 eqeq1d breq1 eqeq2d rexbii adantl
      rexbidv 3imtr4i wne wcel simpl nnred lttri2d anbi1d andir bitrdi 2rexbiia
      r19.43 3bitri sylib mpjaodan ) ADIZEIZJKZVIBCLZVJBCLZMZNZEOPZDOPZVQVJVIJK
      ZVNNZEOPZDOPZAVQUAWAVQAGIZVIJKZVLWBBCLZMZNZGOPZDOPZVIHIZJKZVLWIBCLZMZNZHO
      PZDOPZWAVQWBWIJKZWKWDMZNZGOPZHOPZWPWDWKMZNZHOPZGOPZWHWOWTWRHOPGOPXDWRHGOO
      UCWRXBGHOOWQXAWPWKWDUDUEUFUGWGWSDHODHQZWFWRGOXEWCWPWEWQVIWIWBJUHXEVLWKWDV
      IWIBCRUISUNTWNXCDGODGQZWMXBHOXFWJWPWLXAVIWBWIJUJXFVLWDWKVIWBBCRUISUNTUOVT
      WGDOVSWFEGOEGQZVRWCVNWEVJWBVIJUJXGVMWDVLVJWBBCRUKSTULVPWNDOVOWMEHOEHQZVKW
      JVNWLVJWIVIJUHXHVMWKVLVJWIBCRUKSTULUOUMAVIVJUPZVNNZEOPDOPZVQWAUBZFXKVOVSU
      BZEOPZDOPVPVTUBZDOPXLXJXMDEOOVIOUQZVJOUQZNZXJVKVRUBZVNNXMXRXIXSVNXRVIVJXR
      VIXPXQURUSXRVJXPXQUAUSUTVAVKVRVNVBVCVDXNXODOVOVSEOVEULVPVTDOVEVFVGVH $.
  $}

  ${
    $d A n o p q $.  $d .x. n o p q $.  $d ph n o p q $.  $d A n $.  $d B n $.
    fimgmcyc.b $e |- B = ( Base ` M ) $.
    fimgmcyc.m $e |- .x. = ( .g ` M ) $.
    fimgmcyc.s $e |- ( ph -> M e. Mgm ) $.
    fimgmcyc.f $e |- ( ph -> B e. Fin ) $.
    fimgmcyc.a $e |- ( ph -> A e. B ) $.
    $( Version of ~ odcl2 for finite magmas: the multiples of an element
       ` A e. B ` are eventually periodic.  (Contributed by SN, 3-Jul-2025.) $)
    fimgmcyc $p |- ( ph -> E. o e. NN E. p e. NN
                                         ( o .x. A ) = ( ( o + p ) .x. A ) ) $=
      ( vq vn co wrex cn wbr wa wcel cv wceq c1 caddc cuz cfv clt weq wi wn wne
      wral cmpt wf1 cdom csdm domnsym cfn fisdomnn syl nsyl3 cbs fvexi f1dom wf
      nsyl cmgm adantr simpr mulgnncl syl3anc fmpttd dff13 baib mtbid eqid ovex
      wb oveq1 fvmpt eqeqan12d imbi1d ralbidva ralbiia sylnib df-ne ancom annim
      anbi1i 3bitri 2rexbii rexnal2 bitri sylibr fimgmcyclem wex nnz eluzp1 idd
      cz a1i cc0 0red cr ad2antrr zre adantl nngt0 simplr lttrd elnnz rbaibr ex
      nnre pm5.21ndd pm5.32rd bitrd anbi1d bitrdi exbidv df-rex 3bitr4g rexbiia
      anass cle peano2nnd nnzd nnaddcld nnred nnge1d leadd2dd syl3anbrc eluzp1l
      1red eluz2 cmin sylan peano2nn mpbid cc eluznn syl2anc eluzelcn rsubrotld
      nnsub ad2antlr nncn rspcedeq2vd eqeq2d rexxfrd rexbidva ) AEUAZBDOZMUAZBD
      OZUBZMUULUCUDOZUEUFZPZEQPZUUMUULGUAZUDOZBDOZUBZGQPZEQPAUULUUNUGRZUUPSZMQP
      ZEQPUUTABDEMAUUPEMUHZUIZMQULZEQULZUJZUULUUNUKZUUPSZMQPEQPZAUULNQNUAZBDOZU
      MZUFZUUNUVSUFZUBZUVIUIZMQULZEQULZUVLAQCUVSUNZUWEAQCUORZUWFUWGCQUPRZAQCUQA
      CURTUWHKCUSUTVAQCUVSCFVBHVCVDVFAQCUVSVEZUWFUWEVRANQUVRCAUVQQTZSFVGTZUWJBC
      TZUVRCTAUWKUWJJVHAUWJVIAUWLUWJLVHCDFUVQBHIVJVKVLUWFUWIUWEEMQCUVSVMVNUTVOU
      WDUVKEQUULQTZUWCUVJMQUWMUUNQTZSUWBUUPUVIUWMUWNUVTUUMUWAUUONUULUVRUUMQUVSU
      VQUULBDVSUVSVPZUULBDVQVTNUUNUVRUUOQUVSUVQUUNBDVSUWOUUNBDVQVTWAWBWCWDWEUVP
      UVJUJZMQPEQPUVMUVOUWPEMQQUVOUVIUJZUUPSUUPUWQSUWPUVNUWQUUPUULUUNWFWIUWQUUP
      WGUUPUVIWHWJWKUVJEMQQWLWMWNWOUUSUVHEQUWMUUNUURTZUUPSZMWPUWNUVGSZMWPUUSUVH
      UWMUWSUWTMUWMUWSUWNUVFSZUUPSUWTUWMUWRUXAUUPUWMUWRUUNWTTZUVFSZUXAUWMUULWTT
      ZUWRUXCVRUULWQUULUUNWRUTUWMUVFUXBUWNUWMUVFUXBUWNVRZUWMUVFSZUXBUXBUWNUXFUX
      BWSUWNUXBUIUXFUUNWQXAUXFUXBUXEUXFUXBSZXBUUNUGRZUXEUXGXBUULUUNUXGXCUWMUULX
      DTUVFUXBUULXNXEUXBUUNXDTUXFUUNXFXGUWMXBUULUGRUVFUXBUULXHXEUWMUVFUXBXIXJUW
      NUXBUXHUUNXKXLUTXMXOXMXPXQXRUWNUVFUUPYDXSXTUUPMUURYAUVGMQYAYBYCWNAUUSUVEE
      QAUWMSZUUPUVDMGUVBUURQUXIUVAQTZSZUUQWTTUVBWTTUUQUVBYERUVBUURTUXKUUQUXKUUL
      AUWMUXJXIZYFYGUXKUVBUXKUULUVAUXLUXIUXJVIZYHYGUXKUCUVAUULUXKYNUXKUVAUXMYIU
      XKUULUXLYIUXKUVAUXMYJYKUUQUVBYOYLUXIUWRSZGUUNUULYPOZQUUNUVBUXNUVFUXOQTZUX
      IUXDUWRUVFUXIUULAUWMVIYGUULUUNYMYQUXNUWMUWNUVFUXPVRAUWMUWRXIUXIUUQQTZUWRU
      WNUWMUXQAUULYRXGUUNUUQUUAYQUULUUNUUEUUBYSUXNUVAUXOUBZSUVAUUNUULUWRUUNYTTU
      XIUXRUUQUUNUUCUUFUXIUULYTTZUWRUXRUWMUXSAUULUUGXGXEUXNUXRVIUUDUUHUUNUVBUBZ
      UUPUVDVRUXIUXTUUOUVCUUMUUNUVBBDVSUUIXGUUJUUKYS $.
  $}

  ${
    $d .1. n o p $.  $d A n o p $.  $d .^ n o p $.  $d ph o p $.
    fidomncyc.b $e |- B = ( Base ` R ) $.
    fidomncyc.0 $e |- .0. = ( 0g ` R ) $.
    fidomncyc.1 $e |- .1. = ( 1r ` R ) $.
    fidomncyc.e $e |- .^ = ( .g ` ( mulGrp ` R ) ) $.
    fidomncyc.r $e |- ( ph -> R e. Domn ) $.
    fidomncyc.f $e |- ( ph -> B e. Fin ) $.
    fidomncyc.a $e |- ( ph -> A e. ( B \ { .0. } ) ) $.
    $( Version of ~ odcl2 for multiplicative groups of finite domains (that is,
       a finite monoid where nonzero elements are cancellable): one ( ` .1. ` )
       is a multiple of any nonzero element.  (Contributed by SN,
       3-Jul-2025.) $)
    fidomncyc $p |- ( ph -> E. n e. NN ( n .^ A ) = .1. ) $=
      ( vp co cn wcel adantr vo cv wceq wrex cmgp cfv eqid mgpbas cmnd cmgm crg
      caddc cdomn domnring syl ringmgp mndmgm eldifad fimgmcyc wa simplrr cmulr
      csn cdif cn0 nnnn0 ad2antrl domnexpgn0cl simprr mulgnncl syl3anc ringidcl
      ad2antrr ringridmd simpr csgrp mndsgrp simplrl mgpplusg mulgnndir 3eqtrrd
      syl13anc domnlcan weq oveq1 eqeq1d rspcev syl2anc ex rexlimdvva mpd ) AUA
      UBZBGQZWLPUBZULQBGQZUCZPRUDUARUDFUBZBGQZEUCZFRUDZABCGUADUEUFZPCDXAXAUGZIU
      HZLAXAUISZXAUJSZADUKSZXDADUMSZXFMDUNUOZDXAXBUPUOZXAUQUOZNABCHVCZOURZUSAWP
      WTUAPRRAWLRSZWNRSZUTZUTZWPWTXPWPUTZXNWNBGQZEUCZWTAXMXNWPVAZXQCDDVBUFZWMXR
      HEIJYAUGZXPWMCXKVDZSWPXPCDGWLBHIJLAXGXOMTXMWLVESAXNWLVFVGABYCSXOOTVHZTXPX
      RCSZWPXPXEXNBCSZYEAXEXOXJTAXMXNVIAYFXOXLTZCGXAWNBXCLVJVKTAECSZXOWPAXFYHXH
      CDEIKVLUOVMAXGXOWPMVMXQWMEYAQZWMWOWMXRYAQZXPYIWMUCWPXPCDYAEWMIYBKAXFXOXHT
      XPWMCXKYDURVNTXPWPVOXQXAVPSZXMXNYFWOYJUCAYKXOWPAXDYKXIXAVQUOVMAXMXNWPVRXT
      XPYFWPYGTCYAGXAWLWNBXCLDYAXAXBYBVSVTWBWAWCWSXSFWNRFPWDWRXREWQWNBGWEWFWGWH
      WIWJWK $.
  $}

  ${
    $d ph a b n x $.  $d A a b n $.  $d B b n x $.  $d R n x $.  $d .0. n x $.
    $d T a b $.
    fiabv.a $e |- A = ( AbsVal ` R ) $.
    fiabv.b $e |- B = ( Base ` R ) $.
    fiabv.0 $e |- .0. = ( 0g ` R ) $.
    fiabv.t $e |- T = ( x e. B |-> if ( x = .0. , 0 , 1 ) ) $.
    fiabv.r $e |- ( ph -> R e. Domn ) $.
    fiabv.f $e |- ( ph -> B e. Fin ) $.
    $( In a finite domain (a finite field), the only absolute value is the
       trivial one ( ~ abvtrivg ).  (Contributed by SN, 3-Jul-2025.) $)
    fiabv $p |- ( ph -> A = { T } ) $=
      ( wcel wa syl cfv wceq c1 cc0 va vb vn cv cr abvf ffnd adantl wf abvtrivg
      wfn cdomn adantr fveq2 eqeq12d wne cmgp cmg co cur eqid ad3antrrr cfn csn
      cn cdif eldifsn biimpri adantll fidomncyc cexp simprr fveq2d cnzr domnnzr
      ad4antr simp-4r simpllr simprl nnnn0d simpr nzrnz abv1z syl2anc abvcl cle
      abvexp 3eqtr3d wbr abvge0 expeq1d mpbid rexlimddv cif weq eqeq1 ifnefalse
      ifbid sylan9eqr simplr 1cnd fvmptd2 adantllr eqtr4d abv0 pm2.61ne eqfnfvd
      cc eqsnd ) AUACFAUAUDZCNZOZUBDXJFXKXJDUKAXKDUEXJCDEXJHIUFUGUHAFDUKXKADUEF
      AFCNZDUEFUIAEULNZXMLBCDEFGHIJKUJPZCDEFHIUFPUGUMXLUBUDZDNZOZXPXJQZXPFQZRGX
      JQZGFQZRZXPGXPGRZXSYAXTYBXPGXJUNXPGFUNUOXRXPGUPZOZXSSXTYFUCUDZXPEUQQURQZU
      SZEUTQZRZXSSRZUCVEYFXPDEYJUCYHGIJYJVAZYHVAZAXNXKXQYELVBADVCNXKXQYEMVBXQYE
      XPDGVDVFNZXLYOXQYEOXPDGVGVHVIVJYFYGVENZYKOZOZXSYGVKUSZSRYLYRYIXJQYJXJQZYS
      SYRYIYJXJYFYPYKVLVMYRCDEYHXJYGXPHYNIAEVNNZXKXQYEYQAXNUUALEVOZPVPAXKXQYEYQ
      VQZXLXQYEYQVRZYRYGYFYPYKVSZVTWGXLYTSRZXQYEYQXLXKYJGUPZUUFAXKWAAUUGXKAXNUU
      GLXNUUAUUGUUBEYJGYMJWBPPUMCEYJXJGHYMJWCWDVBWHYRXSYGYRXKXQXSUENUUCUUDCDEXJ
      XPHIWEWDUUEYRXKXQTXSWFWIUUCUUDCDEXJXPHIWJWDWKWLWMAXQYEXTSRXKAXQOZYEOZBXPB
      UDZGRZTSWNZSDFXHKBUBWOZUUIUULYDTSWNZSUUMUUKYDTSUUJXPGWPWRYEUUNSRUUHXPGTSW
      QUHWSAXQYEWTUUIXAXBXCXDXLYCXQXLYATYBXKYATRACEXJGHJXEUHAYBTRZXKAXMUUOXOCEF
      GHJXEPUMXDUMXFXGXOXI $.
  $}

  $( A vector space is a group.  (Contributed by SN, 28-May-2023.) $)
  lvecgrp $p |- ( W e. LVec -> W e. Grp ) $=
    ( clvec wcel lveclmod lmodgrpd ) ABCAADE $.

  ${
    lvecring.1 $e |- F = ( Scalar ` W ) $.
    $( The scalar component of a vector space is a ring.  (Contributed by SN,
       28-May-2023.) $)
    lvecring $p |- ( W e. LVec -> F e. Ring ) $=
      ( clvec wcel clmod crg lveclmod lmodring syl ) BDEBFEAGEBHABCIJ $.
  $}

  ${
    frlm0vald.f $e |- F = ( R freeLMod I ) $.
    frlm0vald.0 $e |- .0. = ( 0g ` R ) $.
    frlm0vald.r $e |- ( ph -> R e. Ring ) $.
    frlm0vald.i $e |- ( ph -> I e. W ) $.
    frlm0vald.j $e |- ( ph -> J e. I ) $.
    $( All coordinates of the zero vector are zero.  (Contributed by SN,
       14-Aug-2024.) $)
    frlm0vald $p |- ( ph -> ( ( 0g ` F ) ` J ) = .0. ) $=
      ( csn cxp cfv c0g crg wcel wceq frlm0 syl2anc fveq1d fvconst2 syl eqtr3d
      fvexi ) AEDGMNZOZECPOZOGAEUGUIABQRDFRUGUISJKBCDFGHITUAUBAEDRUHGSLDGEGBPIU
      FUCUDUE $.
  $}

  ${
    $d I x y $.  $d K u x y $.  $d F x y $.  $d W t u x y $.  $d I t u $.
    frlmsnic.w $e |- W = ( K freeLMod { I } ) $.
    frlmsnic.1 $e |- F = ( x e. ( Base ` W ) |-> ( x ` I ) ) $.
    $( Given a free module with a singleton as the index set, that is, a free
       module of one-dimensional vectors, the function that maps each vector to
       its coordinate is a module isomorphism from that module to its ring of
       scalars seen as a module.  (Contributed by Steven Nguyen,
       18-Aug-2023.) $)
    frlmsnic $p |- ( ( K e. Ring /\ I e. _V ) ->
                                  F e. ( W LMIso ( ringLMod ` K ) ) ) $=
      ( vy crg wcel cvv wa cfv co cbs eqid adantr wceq syl fveq1 vt clmhm clmim
      vu crglmod wf1o cvsca csca clmod csn snex frlmlmod rlmlmod rlmsca frlmsca
      mpan2 eqtr3d cplusg rlmbas rlmplusg cgrp lmodgrp cv frlmbasf adantl snidg
      wf mpan ffvelcdmd fmptd simpll a1i simprl frlmvplusgvalc lmodvacl syl3anc
      simprr cmpt cbvmptv eqtri fvexd fvmpt3 fvmpt2d mpdan oveq12d isghmd cmulr
      3eqtr4d eqcomd fveq2d eleq2d biimpa adantrr frlmvscaval rlmvsca lmodvscld
      oveqi eqtrdi sylan2 fvmptd3 fvex fvmpt3i oveq2d islmhmd simplr simpr fsnd
      cop cfn snfi frlmfielbas sylancl mpbird simpllr vex fvsng eqtr2d wfn ffnd
      wb ex fnsnbg biimpd sylc opeq2 sneqd eqeq2d syl5ibrcom impbid f1o2d mpbid
      f1oeq3d islmim sylanbrc ) DIJZCKJZLZBEDUEMZUBNJEOMZYROMZBUFZBEYRUCNJYQAHE
      YREUGMZYRUGMZBYRUHMZEUHMZUUEOMZYSYSPZUUBPZUUCPUUEPZUUDPUUFPZYOEUIJZYPYOCU
      JZKJZUUKCUKZDEUULKFULZUPQZYOYRUIJZYPDUMZQYQDUUDUUEYODUUDRYPDIUNQYODUUERZY
      PYOUUMUUSUUNDEUULIKFUOUPQZUQYQAHEURMZDURMZEYRBYSDOMZUUGDUSZUVAPZDUTYQUUKE
      VAJUUPEVBSYOYRVAJZYPYOUUQUVFUURYRVBSQYQAYSCAVCZMZUVCBYQUVGYSJZLUULUVCCUVG
      UVIUULUVCUVGVGZYQUUMUVIUVJUUNYSDEUULUVCKUVGFUVCPZUUGVDVHVEZYQCUULJZUVIYPU
      VMYOCKVFVEZQVIZGVJYQUVIHVCZYSJZLZLZCUVGUVPUVANZMZUVHCUVPMZUVBNUVTBMZUVGBM
      ZUVPBMZUVBNUVSYSUVBUVADEUULCIKUVGUVPFUUGYOYPUVRVKUUMUVSUUNVLYQUVIUVQVMZYQ
      UVIUVQVQZYQUVMUVRUVNQUVBPUVEVNUVSUVTYSJZUWCUWARUVSUUKUVIUVQUWHYQUUKUVRUUP
      QUWFUWGUVAYSEUVGUVPUUGUVEVOVPUAUVTCUAVCZMZUWAYSBKCUWIUVTTBAYSUVHVRZUAYSUW
      JVRGAUAYSUVHUWJCUVGUWITVSVTUWIYSJCUWIWAWBSUVSUWDUVHUWEUWBUVBUVSUVIUWDUVHR
      UWFUVSAYSUVHBKBUWKRUVSGVLUVSUVILCUVGWAWCWDUVSUVQUWEUWBRZUWGAUVPUVHUWBYSBK
      CUVGUVPTZGUVICUVGWAWBSWEWHWFYQUVGUUFJZUVQLZLZCUVGUVPUUBNZMZUVGUWBUUCNZUWQ
      BMUVGUWEUUCNUWPUWRUVGUWBDWGMZNUWSUWPUVGYSDUUBUWTUULCUVCKUVPEFUUGUVKUUMUWP
      UUNVLYQUWNUVGUVCJZUVQYQUWNUXAYQUUFUVCUVGYQUUEDOYQDUUEUUTWIWJWKWLWMYQUWNUV
      QVQZYQUVMUWOUVNQUUHUWTPWNUWTUUCUVGUWBDWOWQWRUWPUDUWQCUDVCZMZUWRYSBKBUWKUD
      YSUXDVRGAUDYSUVHUXDCUVGUXCTVSVTCUXCUWQTUWPUVGUUBUUEUUFYSEUVPUUGUUIUUHUUJY
      QUUKUWOYPYOUUMUUKUUMYPUUNVLUUOWSQYQUWNUVQVMUXBWPUWPCUWQWAWTUWPUWEUWBUVGUU
      CUWPUVQUWLUXBAUVPUVHUWBYSBUWMGCUVGXAXBSXCWHXDYQYSUVCBUFUUAYQAHYSUVCUVHCUV
      PXHZUJZBGUVOYQUVPUVCJZLZUXFYSJZUULUVCUXFVGZUXHCUVPKUVCYOYPUXGXEYQUXGXFXGU
      XHYOUULXIJUXIUXJXTYOYPUXGVKCXJYSDEUULUVCIUXFFUVKUUGXKXLXMYQUVIUXGLZLZUVGU
      XFRZUVPUVHRZUXLUXMUXNUXLUXMLZUVHCUXFMZUVPUXMUVHUXPRUXLCUVGUXFTVEUXOYPUVPK
      JUXPUVPRYOYPUXKUXMXNHXOCUVPKKXPXLXQYAUXLUXMUXNUVGCUVHXHZUJZRZUXLYPUVGUULX
      RZUXSYOYPUXKXEUXLUULUVCUVGYQUVIUVJUXGUVLWMXSYPUXTUXSCUVGKYBYCYDUXNUXFUXRU
      VGUXNUXEUXQUVPUVHCYEYFYGYHYIYJYQUVCYTYSBUVCYTRYQUVDVLYLYKYSYTEYRBUUGYTPYM
      YN $.
  $}

  ${
    uvccl.u $e |- U = ( R unitVec I ) $.
    uvccl.y $e |- Y = ( R freeLMod I ) $.
    uvccl.b $e |- B = ( Base ` Y ) $.
    $( A unit vector is a vector.  (Contributed by Steven Nguyen,
       16-Jul-2023.) $)
    uvccl $p |- ( ( R e. Ring /\ I e. W /\ J e. I ) -> ( U ` J ) e. B ) $=
      ( crg wcel w3a wf uvcff 3adant3 simp3 ffvelcdmd ) BKLZDFLZEDLZMDAECSTDACN
      UAABCDFGHIJOPSTUAQR $.
  $}

  ${
    uvcn0.u $e |- U = ( R unitVec I ) $.
    uvcn0.y $e |- Y = ( R freeLMod I ) $.
    uvcn0.b $e |- B = ( Base ` Y ) $.
    uvcn0.0 $e |- .0. = ( 0g ` Y ) $.
    $( A unit vector is nonzero.  (Contributed by Steven Nguyen,
       16-Jul-2023.) $)
    uvcn0 $p |- ( ( R e. NzRing /\ I e. W /\ J e. I ) -> ( U ` J ) =/= .0. ) $=
      ( cnzr wcel w3a cfv c0g wne eqid 3ad2ant1 cur nzrnz simp1 simp2 simp3 crg
      uvcvv1 nzrring frlm0vald 3netr4d fveq1 necon3i syl wceq a1i neeqtrrd ) BM
      NZDFNZEDNZOZECPZGQPZHUTEVAPZEVBPZRVAVBRUTBUAPZBQPZVCVDUQURVEVFRUSBVEVFVES
      ZVFSZUBTUTBCVEDEMFIUQURUSUCUQURUSUDZUQURUSUEZVGUGUTBGDEFVFJVHUQURBUFNUSBU
      HTVIVJUIUJVAVBVCVDEVAVBUKULUMHVBUNUTLUOUP $.
  $}

  $( If 0propd (akin to mndpropd) is ever proven, then from ~ pwsbas ,
     ~ psrbas , ~ pwsplugval , and ~ psradd , we can prove ~ psr0 a different
     way.  This might be overall shorter since we can then derive ~ psr0cl and
     ~ psr0lid from ~ psr0 .  This would let ~ psrmnd generalize results using
     ~ psrgrp .

     A possible way to show 0propd is by showing mhmpropd. $)

  ${
    $d f x y ph $.  $d f x y R $.  $d f x y S $.  $d f x y I $.
    psrmnd.s $e |- S = ( I mPwSer R ) $.
    psrmnd.i $e |- ( ph -> I e. V ) $.
    psrmnd.r $e |- ( ph -> R e. Mnd ) $.
    $( The ring of power series is a monoid.  (Contributed by SN,
       25-Apr-2025.) $)
    psrmnd $p |- ( ph -> S e. Mnd ) $=
      ( vf cv wcel cmap co cmnd cvv eqid cbs cfv cplusg eleq2d vx ccnv cima cfn
      vy cn cn0 crab cpws ovex rabex pwsmnd sylancl pwsbas psrbas eqcomd wa cof
      wceq adantr a1i biimpa adantrr adantrl pwsplusgval psradd eqtr4d mndpropd
      biimpar mpbid ) ABIJUBUFUCUDKZIUGDLMZUHZUIMZNKZCNKABNKZVMOKZVOHVKIVLUGDLU
      JUKZBVMOVNVNPZULUMAUAUEBQRZVMLMZVNCAVPVQWAVNQRZUSHVRVTBVMNOVNVSVTPZUNUMZA
      CQRZWAAWEVMBCIDVTEFWCVMPWEPZGUOZUPAUAJZWAKZUEJZWAKZUQZUQZWHWJVNSRZMWHWJBS
      RZURMWHWJCSRZMWMWBWOWNBWHWJVMNOVNVSWBPAVPWLHUTVQWMVRVAAWIWHWBKZWKAWIWQAWA
      WBWHWDTVBVCAWKWJWBKZWIAWKWRAWAWBWJWDTVBVDWOPZWNPVEWMWEWOWPBCDWHWJFWFWSWPP
      AWIWHWEKZWKAWTWIAWEWAWHWGTVIVCAWKWJWEKZWIAXAWKAWEWAWJWGTVIVDVFVGVHVJ $.
  $}

  ${
    $d I f $.
    mhmcopsr.p $e |- P = ( I mPwSer R ) $.
    mhmcopsr.q $e |- Q = ( I mPwSer S ) $.
    mhmcopsr.b $e |- B = ( Base ` P ) $.
    mhmcopsr.c $e |- C = ( Base ` Q ) $.
    mhmcopsr.h $e |- ( ph -> H e. ( R MndHom S ) ) $.
    mhmcopsr.f $e |- ( ph -> F e. B ) $.
    $( The composition of a monoid homomorphism and a power series is a power
       series.  (Contributed by SN, 18-May-2025.) $)
    mhmcopsr $p |- ( ph -> ( H o. F ) e. C ) $=
      ( vf cbs wcel cvv ccom cfv cv ccnv cn cima cfn cmap crab fvexd ovex rabex
      cn0 co a1i cmhm eqid mhmf syl psrelbas fcod elmapdd cmps reldmpsr elbasov
      wf wa simpld psrbas eleqtrrd ) AIHUAZGRUBZQUCUDUEUFUGSZQUMJUHUNZUIZUHUNCA
      VLVOVKTTAGRUJVOTSAVMQVNUMJUHUKULUOAVOFRUBZVLIHAIFGUPUNSVPVLIVFOVPVLFGIVPU
      QZVLUQZURUSABVOFDQJVPHKVQVOUQZMPUTVAVBACVOGEQJVLTLVRVSNAJTSZFTSZAHBSVTWAV
      GPHBDVCJFVDKMVEUSVHVIVJ $.
  $}

  ${
    $d I f $.
    mhmcoaddpsr.p $e |- P = ( I mPwSer R ) $.
    mhmcoaddpsr.q $e |- Q = ( I mPwSer S ) $.
    mhmcoaddpsr.b $e |- B = ( Base ` P ) $.
    mhmcoaddpsr.c $e |- C = ( Base ` Q ) $.
    mhmcoaddpsr.1 $e |- .+ = ( +g ` P ) $.
    mhmcoaddpsr.2 $e |- .+b = ( +g ` Q ) $.
    mhmcoaddpsr.h $e |- ( ph -> H e. ( R MndHom S ) ) $.
    mhmcoaddpsr.f $e |- ( ph -> F e. B ) $.
    mhmcoaddpsr.g $e |- ( ph -> G e. B ) $.
    $( Show that the ring homomorphism in ~ rhmpsr preserves addition.
       (Contributed by SN, 18-May-2025.) $)
    mhmcoaddpsr $p |- ( ph -> ( H o. ( F .+ G ) ) =
                              ( ( H o. F ) .+b ( H o. G ) ) ) $=
      ( vf cplusg cfv cof co ccom cmhm wcel cbs cv ccnv cima cfn cmap crab wceq
      cn0 cvv fvexd ovex rabex a1i eqid psrelbas elmapdd mhmvlin syl3anc psradd
      cn coeq2d mhmcopsr 3eqtr4d ) ALJKHUDUEZUFUGZUHZLJUHZLKUHZIUDUEZUFUGZLJKEU
      GZUHVRVSFUGALHIUIUGUJJHUKUEZUCULUMVKUNUOUJZUCUSMUPUGZUQZUPUGZUJKWGUJVQWAU
      RTAWCWFJUTUTAHUKVAZWFUTUJAWDUCWEUSMUPVBVCVDZABWFHDUCMWCJNWCVEZWFVEZPUAVFV
      GAWCWFKUTUTWHWIABWFHDUCMWCKNWJWKPUBVFVGWCVOVTLWFHIJKWJVOVEZVTVEZVHVIAWBVP
      LABVOEHDMJKNPWLRUAUBVJVLACVTFIGMVRVSOQWMSABCDGHIJLMNOPQTUAVMABCDGHIKLMNOP
      QTUBVMVJVN $.
  $}

  ${
    $d ph d k $.  $d R d k $.  $d S d k $.  $d F d k $.  $d G d k $.
    $d H d k $.  $d I d e f k $.  $d B d k $.  $d C d k $.
    rhmcomulpsr.p $e |- P = ( I mPwSer R ) $.
    rhmcomulpsr.q $e |- Q = ( I mPwSer S ) $.
    rhmcomulpsr.b $e |- B = ( Base ` P ) $.
    rhmcomulpsr.c $e |- C = ( Base ` Q ) $.
    rhmcomulpsr.1 $e |- .x. = ( .r ` P ) $.
    rhmcomulpsr.2 $e |- .xb = ( .r ` Q ) $.
    rhmcomulpsr.h $e |- ( ph -> H e. ( R RingHom S ) ) $.
    rhmcomulpsr.f $e |- ( ph -> F e. B ) $.
    rhmcomulpsr.g $e |- ( ph -> G e. B ) $.
    $( Show that the ring homomorphism in ~ rhmpsr preserves multiplication.
       (Contributed by SN, 18-May-2025.) $)
    rhmcomulpsr $p |- ( ph -> ( H o. ( F .x. G ) ) =
                              ( ( H o. F ) .xb ( H o. G ) ) ) $=
      ( vk vf vd ve cv ccnv cn cima cfn wcel cn0 cmap co crab cle cofr wbr cmin
      cfv cof cmulr cmpt cgsu ccom cbs crh eqid rhmf syl crg rhmrcl1 rhmpsrlem2
      wf psrelbas cofmpt wa cvv c0g ccmn ringcmnd cmnd rhmrcl2 ringgrpd grpmndd
      adantr ovex rabex cmhm cghm rhmghm ghmmhm 3syl ad2antrr elrabi ffvelcdmda
      a1i sylan2 adantlr psrbagconcl adantll ringcld rhmpsrlem1 gsummptmhm wceq
      ffvelcdmd rhmmul syl3anc adantl fvco3d oveq12d eqtr4d oveq2d eqtr3d eqtrd
      mpteq2dva psrmulfval coeq2d mhmcopsr 3eqtr4d ) ALUCUDUGUHUIUJUKULZUDUMMUN
      UOZUPZFUEUFUGUCUGZUQURUSZUFYDUPZUEUGZJVAZYEYHUTVBUOZKVAZFVCVAZUOZVDVEUOZV
      DZVFZUCYDGUEYGYHLJVFZVAZYJLKVFZVAZGVCVAZUOZVDZVEUOZVDZLJKIUOZVFYQYSHUOAYP
      UCYDYNLVAZVDUUEAUCYDYNFVGVAZGVGVAZLALFGVHUOULZUUHUUILVOTUUHUUIFGLUUHVIZUU
      IVIVJVKAUEUFYDFUDUCMJKYDVIZAUUJFVLULZTFGLVMVKZABYDFDUDMUUHJNUUKUULPUAVPZA
      BYDFDUDMUUHKNUUKUULPUBVPZVNVQAUCYDUUGUUDAYEYDULZVRZGUEYGYMLVAZVDZVEUOUUGU
      UDUURUEYGUUHYMFGLVSFVTVAZUUKUVAVIAFWAULUUQAFUUNWBWGAGWCULUUQAGAGAUUJGVLUL
      TFGLWDVKWEWFWGYGVSULUURYFUFYDYBUDYCUMMUNWHWIWIWRALFGWJUOULZUUQAUUJLFGWKUO
      ULUVBTFGLWLFGLWMWNZWGUURYHYGULZVRZUUHFYLYIYKUUKYLVIZAUUMUUQUVDUUNWOAUVDYI
      UUHULZUUQUVDAYHYDULZUVGYFUFYHYDWPZAYDUUHYHJUUOWQWSWTZUVEYDUUHYJKAYDUUHKVO
      UUQUVDUUPWOZUVEYJYGULZYJYDULUUQUVDUVLAUFYDYGUDYEMYHUULYGVIXAXBYFUFYJYDWPV
      KZXGZXCAUEUFYDFUDUCMJKUULUUNUUOUUPXDXEUURUUTUUCGVEUURUEYGUUSUUBUVEUUSYILV
      AZYKLVAZUUAUOZUUBUVEUUJUVGYKUUHULUUSUVQXFAUUJUUQUVDTWOUVJUVNYIYKFGYLUUALU
      UHUUKUVFUUAVIZXHXIUVEYRUVOYTUVPUUAUVEYDUUHYHLJAYDUUHJVOUUQUVDUUOWOUVDUVHU
      URUVIXJXKUVEYDUUHYJLKUVKUVMXKXLXMXQXNXOXQXPAUUFYOLAUEUFBYDFDIYLUDUCJKMNPU
      VFRUULUAUBXRXSAUEUFCYDGEHUUAUDUCYQYSMOQUVRSUULABCDEFGJLMNOPQUVCUAXTABCDEF
      GKLMNOPQUVCUBXTXRYA $.
  $}

  ${
    $d B p x y $.  $d F x y $.  $d H d p $.  $d I d f $.  $d P d p x y $.
    $d Q d p x y $.  $d R d f $.  $d S d f $.  $d V d $.  $d ph d p x y $.
    rhmpsr.p $e |- P = ( I mPwSer R ) $.
    rhmpsr.q $e |- Q = ( I mPwSer S ) $.
    rhmpsr.b $e |- B = ( Base ` P ) $.
    rhmpsr.f $e |- F = ( p e. B |-> ( H o. p ) ) $.
    rhmpsr.i $e |- ( ph -> I e. V ) $.
    rhmpsr.h $e |- ( ph -> H e. ( R RingHom S ) ) $.
    $( Provide a ring homomorphism between two power series algebras over their
       respective base rings given a ring homomorphism between the two base
       rings.  (Contributed by SN, 8-Feb-2025.) $)
    rhmpsr $p |- ( ph -> F e. ( P RingHom Q ) ) $=
      ( cfv eqid wcel vx vy vd cbs cplusg cmulr cur crh crg rhmrcl1 syl psrring
      vf co rhmrcl2 ccom cv ccnv cn cima cfn cn0 cmap crab cc0 csn cxp wceq c0g
      cif cmpt psr1 coeq2d wf rhmf ringidcl ring0cl ifcld adantr fvif rhm1 cghm
      cofmpt rhmghm ghmid 3syl ifeq12d eqtrid mpteq2dv 3eqtrd cvv coeq2 fvmptd3
      coexd 3eqtr4d simprl simprr rhmcomulpsr ringcld oveq12d cmhm ghmmhm simpr
      wa mhmcopsr fmptd mhmcoaddpsr ringgrpd grpcld isrhmd ) AUAUBBDUDRZCUERZDU
      ERZCDCUFRZDUFRZCUGRZGDUGRZNXPSZXQSZXNSZXOSZAECIJLPAHEFUHUNZTZEUITZQEFHUJU
      KZULZAFDIJMPAYCFUITQEFHUOUKZULAHXPUPZUCUMUQURUSUTVATUMVBIVCUNVDZUCUQZIVEV
      FVGVHZFUGRZFVIRZVJZVKZXPGRXQAYHHUCYIYKEUGRZEVIRZVJZVKZUPUCYIYRHRZVKYOAXPY
      SHAUCYIECXPYPUMIJYQLPYEYISZYQSZYPSZXRVLVMAUCYIYREUDRZFUDRZHAYCUUDUUEHVNQU
      UDUUEEFHUUDSZUUESVOUKAYRUUDTYJYITAYKYPYQUUDAYDYPUUDTYEUUDEYPUUFUUCVPUKAYD
      YQUUDTYEUUDEYQUUFUUBVQUKVRVSWCAUCYIYTYNAYTYKYPHRZYQHRZVJYNYKYPYQHVTAYKUUG
      YLUUHYMAYCUUGYLVHQEFYPHYLUUCYLSZWAUKAYCHEFWBUNTZUUHYMVHQEFHWDZEFHYQYMUUBY
      MSZWEWFWGWHWIWJAKXPHKUQZUPZYHBGWKOUUMXPHWLACUITZXPBTYFBCXPNXRVPUKZAHXPYBB
      QUUPWNWMAUCYIFDXQYLUMIJYMMPYGUUAUULUUIXSVLWOAUAUQZBTZUBUQZBTZXDZXDZHUUQUU
      SXNUNZUPZHUUQUPZHUUSUPZXOUNUVCGRUUQGRZUUSGRZXOUNUVBBXKCDEFXOXNUUQUUSHILMN
      XKSZXTYAAYCUVAQVSZAUURUUTWPZAUURUUTWQZWRUVBKUVCUUNUVDBGWKOUUMUVCHWLUVBBCX
      NUUQUUSNXTAUUOUVAYFVSZUVKUVLWSZUVBHUVCYBBUVJUVNWNWMUVBUVGUVEUVHUVFXOUVBKU
      UQUUNUVEBGWKOUUMUUQHWLUVKUVBHUUQYBBUVJUVKWNWMZUVBKUUSUUNUVFBGWKOUUMUUSHWL
      UVLUVBHUUSYBBUVJUVLWNWMZWTWOUVIXLSZXMSZAKBUUNXKGAUUMBTZXDBXKCDEFUUMHILMNU
      VIAHEFXAUNTZUVSAYCUUJUVTQUUKEFHXBZWFVSAUVSXCXEOXFUVBHUUQUUSXLUNZUPZUVEUVF
      XMUNUWBGRUVGUVHXMUNUVBBXKCXLXMDEFUUQUUSHILMNUVIUVQUVRUVBYCUUJUVTUVJUUKUWA
      WFUVKUVLXGUVBKUWBUUNUWCBGWKOUUMUWBHWLUVBBXLCUUQUUSNUVQUVBCUVMXHUVKUVLXIZU
      VBHUWBYBBUVJUWDWNWMUVBUVGUVEUVHUVFXMUVOUVPWTWOXJ $.
  $}

  ${
    $d P x y $.  $d Q x y $.  $d R x y $.  $d S x y $.  $d ph x y $.  $d B p $.
    $d H p $.  $d R p $.  $d S p $.  $d ph p $.
    rhmpsr1.p $e |- P = ( PwSer1 ` R ) $.
    rhmpsr1.q $e |- Q = ( PwSer1 ` S ) $.
    rhmpsr1.b $e |- B = ( Base ` P ) $.
    rhmpsr1.f $e |- F = ( p e. B |-> ( H o. p ) ) $.
    rhmpsr1.h $e |- ( ph -> H e. ( R RingHom S ) ) $.
    $( Provide a ring homomorphism between two univariate power series algebras
       over their respective base rings given a ring homomorphism between the
       two base rings.  (Contributed by SN, 8-Feb-2025.) $)
    rhmpsr1 $p |- ( ph -> F e. ( P RingHom Q ) ) $=
      ( c1o eqid wcel a1i cfv wceq vx vy cmps co crh psr1bas2 1oex rhmpsr eqidd
      cvv cbs cv cplusg psr1plusg eqcomi oveqd cmulr psr1mulr rhmpropd eleqtrd
      wa ) AGOEUCUDZOFUCUDZUEUDCDUEUDABVBVCEFGHOUJIVBPZVCPZBECVBJLVDUFMOUJQAUGR
      NUHAUAUBCUKSZDUKSZVBVCCDVFVBUKSTAVFECVBJVFPVDUFRVGVCUKSTAVGFDVCKVGPVEUFRA
      VFUIAVGUIAUAULZVFQUBULZVFQVAVAZVBUMSZCUMSZVHVIVKVLTVJVLVKVLEVBCJVDVLPUNUO
      RUPAVHVGQVIVGQVAVAZVCUMSZDUMSZVHVIVNVOTVMVOVNVOFVCDKVEVOPUNUORUPVJVBUQSZC
      UQSZVHVIVPVQTVJVQVPEVBVQCJVDVQPURUORUPVMVCUQSZDUQSZVHVIVRVSTVMVSVRFVCVSDK
      VEVSPURUORUPUSUT $.
  $}

  $( TODO:  Investigate the usefulness of theorems ~ mndvcl to ~ mhmvlin and
     ~ grpvlinv to ~ ringvcl , and convert ~ ofco2 to deduction form and move
     it up. $)

  ${
    evl0.q $e |- Q = ( I eval R ) $.
    evl0.b $e |- B = ( Base ` R ) $.
    evl0.w $e |- W = ( I mPoly R ) $.
    evl0.o $e |- O = ( 0g ` R ) $.
    evl0.0 $e |- .0. = ( 0g ` W ) $.
    evl0.i $e |- ( ph -> I e. V ) $.
    evl0.r $e |- ( ph -> R e. CRing ) $.
    $( The zero polynomial evaluates to zero.  (Contributed by SN,
       23-Nov-2024.) $)
    evl0 $p |- ( ph -> ( Q ` .0. ) = ( ( B ^m I ) X. { O } ) ) $=
      ( cascl cfv cmap wcel co csn cxp crngringd mplascl0 fveq2d ring0cl evlsca
      eqid crg syl eqtr3d ) AFHQRZRZCRICRBESUAFUBUCAUNICAUMDEFGHILUMUIZMNOADPUD
      ZUEUFAUMBCDEGHFJLKUOOPADUJTFBTUPBDFKMUGUKUHUL $.
  $}

  ${
    $d .0. s $.  $d .1. s $.  $d .^ b $.  $d A b v $.  $d B b v $.  $d B h $.
    $d B s $.  $d D b v $.  $d D s $.  $d F b $.  $d I b v $.  $d I h $.
    $d K b v $.  $d M b $.  $d P b $.  $d R b $.  $d R s $.  $d S b v $.
    $d U b h $.  $d U s $.  $d W b h $.  $d W v $.  $d ph v $.  $d ph b s $.
    evlsbagval.q $e |- Q = ( ( I evalSub S ) ` R ) $.
    evlsbagval.p $e |- P = ( I mPoly U ) $.
    evlsbagval.u $e |- U = ( S |`s R ) $.
    evlsbagval.w $e |- W = ( Base ` P ) $.
    evlsbagval.k $e |- K = ( Base ` S ) $.
    evlsbagval.m $e |- M = ( mulGrp ` S ) $.
    evlsbagval.e $e |- .^ = ( .g ` M ) $.
    evlsbagval.z $e |- .0. = ( 0g ` U ) $.
    evlsbagval.o $e |- .1. = ( 1r ` U ) $.
    evlsbagval.d $e |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin } $.
    evlsbagval.f $e |- F = ( s e. D |-> if ( s = B , .1. , .0. ) ) $.
    evlsbagval.i $e |- ( ph -> I e. V ) $.
    evlsbagval.s $e |- ( ph -> S e. CRing ) $.
    evlsbagval.r $e |- ( ph -> R e. ( SubRing ` S ) ) $.
    evlsbagval.a $e |- ( ph -> A e. ( K ^m I ) ) $.
    evlsbagval.b $e |- ( ph -> B e. D ) $.
    $( Polynomial evaluation builder for a bag of variables.  EDITORIAL:  This
       theorem should stay in my mathbox until there's another use, since
       ` .0. ` and ` .1. ` using ` U ` instead of ` S ` may not be convenient.
       (Contributed by SN, 29-Jul-2024.) $)
    evlsbagval $p |- ( ph -> ( F e. W /\ ( ( Q ` F ) ` A ) =
                    ( M gsum ( v e. I |-> ( ( B ` v ) .^ ( A ` v ) ) ) ) ) ) $=
      ( vb wcel cfv cv co cmpt cgsu wceq cmps cbs cfsupp wbr cmap fvexd ccnv cn
      cvv cima cfn cn0 ovexd rabexd cif crg subrgring syl eqid ringidcl ring0cl
      csubrg ifcld adantr fmptd elmapdd psrbas eleqtrrd mplelbas sylanbrc cmulr
      sniffsupp evlsvvval csn wss snssd resmpt oveq2d c0g crngringd ringcmnd wa
      cres subrgbas subrgss eqsstrrd fssd ffvelcdmda simpr evlsvvvallem ringcld
      ccrg fmpttd cdif wn eldifsnneq adantl iffalsed weq eqeq1 ifbid eldifi cur
      fvexi ifex a1i fvmptd3 subrg0 eqtr4di oveq1d sylan2 ringlz syl2an2r eqtrd
      3eqtr4d suppss2 evlsvvvallem2 gsumres cmnd crnggrpd ffvelcdmd fveq2 fveq1
      grpmndd oveq12d gsumsn syl3anc iftrue subrg1 3eqtr4a ringlidmd 3eqtrd jca
      mpteq2dv 3eqtr3d ) ANSUSZCNGUTUTZQBOBVAZDUTZUVCCUTZMVBZVCZVDVBZVEANOJVFVB
      ZVGUTZUSNTVHVIUVAANJVGUTZEVJVBUVJAUVKENVNVNAJVGVKALVAVLVMVOVPUSLVQOVJVBEV
      NUKAVQOVJVRVSZAUAEUAVAZDVEZKTVTZUVKNAUVOUVKUSUVMEUSAUVNKTUVKAJWAUSZKUVKUS
      AHIWGUTUSZUVPUOHIJUDWBWCZUVKJKUVKWDZUJWEWCAUVPTUVKUSUVRUVKJTUVSUIWFWCZWHW
      IULWJZWKAUVJEJUVILOUVKRUVIWDZUVSUKUVJWDZUMWLWMAUAKNEVNUVKDTUVLUVTULWQUVJF
      JUVISONTUCUWBUWCUIUEWNWOZAUVBIUREURVAZNUTZQBOUVCUWEUTZUVEMVBZVCZVDVBZIWPU
      TZVBZVCZVDVBZUVHACSEFGHIUWKJLBMNOPQRURUBUCUEUDUKUFUGUHUWKWDZUMUNUOUWDUPWR
      AIUWMDWSZXHZVDVBIURUWPUWLVCZVDVBZUWNUVHAUWQUWRIVDAUWPEWTUWQUWRVEADEUQXAUR
      EUWPUWLXBWCXCAEPUWMIVNUWPIXDUTZUFUWTWDZAIAIUNXEZXFUVLAUREUWLPAUWEEUSZXGZP
      IUWKUWFUWJUFUWOAIWAUSZUXCUXBWIAEPUWENAEUVKPNUWAAUVQUVKPWTUOUVQUVKHPHIJUDX
      IHPIUFXJXKWCXLZXMUXDBCUWEEILMOPQRUKUFUGUHAORUSUXCUMWIAIXQUSUXCUNWIACPOVJV
      BUSUXCUPWIAUXCXNXOZXPXRAEUWLURVNUWPUWTAUWEEUWPXSUSZXGZUWLUWTUWJUWKVBZUWTU
      XIUWFUWTUWJUWKUXIUWEDVEZKTVTZTUWFUWTUXIUXKKTUXHUXKXTAUWEEDYAYBYCUXIUAUWEU
      VOUXLENVNULUAURYDUVNUXKKTUVMUWEDYEYFUXHUXCAUWEEUWPYGZYBUXLVNUSUXIUXKKTKJY
      HUJYIZTJXDUIYIYJYKYLAUWTTVEZUXHAUVQUXOUOUVQUWTJXDUTTHIJUWTUDUXAYMUIYNWCWI
      YTYOAUXEUXHUWJPUSZUXJUWTVEUXBUXHAUXCUXPUXMUXGYPPIUWKUWJUWTUFUWOUXAYQYRYSU
      VLUUAABCSEFHIUWKJLMNOPQRURUKUCUDUEUFUGUHUWOUMUNUOUWDUPUUBUUCAUWSDNUTZUVHU
      WKVBZIYHUTZUVHUWKVBUVHAIUUDUSDEUSUXRPUSUWSUXRVEAIAIUNUUEUUIUQAPIUWKUXQUVH
      UFUWOUXBAEPDNUXFUQUUFABCDEILMOPQRUKUFUGUHUMUNUPUQXOZXPUWLPUXRURIDEUFUXKUW
      FUXQUWJUVHUWKUWEDNUUGUXKUWIUVGQVDUXKBOUWHUVFUXKUWGUVDUVEMUVCUWEDUUHYOUUSX
      CUUJUUKUULAUXQUXSUVHUWKAKJYHUTZUXQUXSUJAUADUVOKENVNULUVNKTUUMUQKVNUSAUXNY
      KYLAUVQUXSUYAVEUOHIJUXSUDUXSWDZUUNWCUUOYOAPIUWKUXSUVHUFUWOUYBUXBUXTUUPUUQ
      UUTYSUUR $.
  $}

  ${
    $d B h $.  $d I h $.  $d I v $.  $d ph b v $.  $d B v $.  $d R b h v $.
    $d K b h v $.  $d F b $.  $d D b v $.
    evlvvvallem.d $e |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin } $.
    evlvvvallem.p $e |- P = ( I mPoly R ) $.
    evlvvvallem.b $e |- B = ( Base ` P ) $.
    evlvvvallem.k $e |- K = ( Base ` R ) $.
    evlvvvallem.m $e |- M = ( mulGrp ` R ) $.
    evlvvvallem.w $e |- .^ = ( .g ` M ) $.
    evlvvvallem.x $e |- .x. = ( .r ` R ) $.
    evlvvvallem.i $e |- ( ph -> I e. V ) $.
    evlvvvallem.r $e |- ( ph -> R e. CRing ) $.
    evlvvvallem.f $e |- ( ph -> F e. B ) $.
    evlvvvallem.a $e |- ( ph -> A e. ( K ^m I ) ) $.
    $( Lemma for theorems using ~ evlvvval .  Version of ~ evlsvvvallem2 using
       ~ df-evl .  (Contributed by SN, 11-Mar-2025.) $)
    evlvvvallem $p |- ( ph -> ( b e. D |->
      ( ( F ` b ) .x. ( M gsum ( v e. I |-> ( ( b ` v ) .^ ( A ` v ) ) ) ) ) )
                                                        finSupp ( 0g ` R ) ) $=
      ( cress cmpl cbs cfv eqid crg wcel csubrg crngringd subrgid syl ccrg wceq
      co ressid oveq2d eqtr4di fveq2d eleqtrrd evlsvvvallem2 ) ABCLGMUHVAZUIVAZ
      UJUKZEVIMGHVHIJKLMNOPQVIULVHULVJULTUAUBUCUDUEAGUMUNMGUOUKUNAGUEUPMGTUQURA
      KDVJUFAVJFUJUKDAVIFUJAVILGUIVAFAVHGLUIAGUSUNVHGUTUEMGUSTVBURVCRVDVESVDVFU
      GVG $.
  $}

  ${
    $d c d f $.  $d d g $.  $d d h $.  $d I f $.  $d J f $.  $d I c e h $.
    $d J c e g $.  $d C c d e $.  $d D c d e $.  $d E c d e $.  $d ph c d e $.
    $( ChatGPT-4o gave the idea for ~ evlselvlem . $)
    evlselvlem.d $e |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin } $.
    evlselvlem.e $e |- E = { g e. ( NN0 ^m J ) | ( `' g " NN ) e. Fin } $.
    evlselvlem.c $e |-
               C = { f e. ( NN0 ^m ( I \ J ) ) | ( `' f " NN ) e. Fin } $.
    evlselvlem.h $e |- H = ( c e. C , e e. E |-> ( c u. e ) ) $.
    evlselvlem.i $e |- ( ph -> I e. V ) $.
    evlselvlem.j $e |- ( ph -> J C_ I ) $.
    $( Lemma for ~ evlselv .  Used to re-index to and from bags of variables in
       ` I ` and bags of variables in the subsets ` J ` and ` I \ J ` .
       (Contributed by SN, 10-Mar-2025.) $)
    evlselvlem $p |- ( ph -> H : ( C X. E ) -1-1-onto-> D ) $=
      ( cn0 vd cv cun cdif cres wcel wa wf ccnv cima cfn wceq wss undifr adantr
      cn sylib psrbagf ad2antrl ad2antll cin disjdifr a1i feq2dd cc0 cfsupp wbr
      c0 fun2d cvv cz unexg adantl 0zd ffund psrbagfsupp isfsuppd fcdmnn0fsuppg
      fsuppun wb syl2anc mpbid psrbag syl mpbir2and difssd simpr psrbagres wrel
      cdm freld fdmd eqtr4d reldmun adantrl uneq12 syl5ibrcom wfn ffnd fnunres1
      eqeq2d syl3anc eqcomd fnunres2 jca adantrr reseq1 anbi12d impbid mpof1o2d
      ) AMDUABHMUBZDUBZUCZCIUAUBZJKUDZUEZXNKUEZQAXKBUFZXLHUFZUGZUGZXMCUFZJTXMUH
      ZXMUIUPUJUKUFZYAXOKUCZJTXMAYEJULZXTAKJUMZYFSKJUNZUQUOYAXOKTXKXLXRXOTXKUHA
      XSBEXKXOPURUSZXSKTXLUHAXRHFXLKOURUTZXOKVAVHULZYAKJVBVCZVIZVDYAXMVEVFVGZYD
      YAXMVJVKVEXTXMVJUFZAXKXLBHVLVMZYAVNYAYETXMYMVOYAXKXLVEXRXKVEVFVGAXSBEXKXO
      PVPUSXSXLVEVFVGAXRHFXLKOVPUTVSVQYAYOYETXMUHYNYDVTYPYMXMYEVJVRWAWBYAJLUFZY
      BYCYDUGVTAYQXTRUOCGXMJLNWCWDWEAXNCUFZUGZCEGBXNJXOLNPAYQYRRUOZYSJKWFAYRWGZ
      WHYSCFGHXNJKLNOYTAYGYRSUOZUUAWHAXTYRUGUGZXKXPULZXLXQULZUGZXNXMULZUUCUUGUU
      FXNXPXQUCZULZAYRUUIXTYSXNWIXNWJZYEULUUIYSJTXNYRJTXNUHACGXNJNURVMZWKYSUUJJ
      YEYSJTXNUUKWLYSYGYFUUBYHUQWMXOKXNWNWAWOUUFXMUUHXNXKXPXLXQWPXAWQUUCUUFUUGX
      KXMXOUEZULZXLXMKUEZULZUGZAXTUUPYRYAUUMUUOYAUULXKYAXKXOWRZXLKWRZYKUULXKULY
      AXOTXKYIWSZYAKTXLYJWSZYLXOKXKXLWTXBXCYAUUNXLYAUUQUURYKUUNXLULUUSUUTYLXOKX
      KXLXDXBXCXEXFUUGUUDUUMUUEUUOUUGXPUULXKXNXMXOXGXAUUGXQUUNXLXNXMKXGXAXHWQXI
      XJ $.
  $}

  ${
    $d A a b c d e i j k u v $.  $d B d $.  $d F a b c d e u $.
    $d I a b c d e f h i j k u v $.  $d J a b c d e f g h i j k u v $.
    $d K a b c d e i j k u v $.  $d L c e j u $.  $d P d $.
    $d R a b c d e f h i j k u v $.  $d T e g j $.  $d U c e g j u $.
    $d ph a b c d e f g i j k u v $.
    evlselv.p $e |- P = ( I mPoly R ) $.
    evlselv.k $e |- K = ( Base ` R ) $.
    evlselv.b $e |- B = ( Base ` P ) $.
    evlselv.u $e |- U = ( ( I \ J ) mPoly R ) $.
    evlselv.t $e |- T = ( J mPoly U ) $.
    evlselv.l $e |- L = ( algSc ` U ) $.
    evlselv.i $e |- ( ph -> I e. V ) $.
    evlselv.r $e |- ( ph -> R e. CRing ) $.
    evlselv.j $e |- ( ph -> J C_ I ) $.
    evlselv.f $e |- ( ph -> F e. B ) $.
    evlselv.a $e |- ( ph -> A e. ( K ^m I ) ) $.
    $( Evaluating a selection of variable assignments, then evaluating the rest
       of the variables, is the same as evaluating with all assignments.
       (Contributed by SN, 10-Mar-2025.) $)
    evlselv $p |- ( ph ->
          ( ( ( ( I \ J ) eval R ) `
                  ( ( ( J eval U ) ` ( ( ( I selectVars R ) ` J ) ` F ) ) `
                                           ( L o. ( A |` J ) ) )
                                       ) ` ( A |` ( I \ J ) ) )
                = ( ( ( I eval R ) ` F ) ` A ) ) $=
      ( vc vf vk vd vh vi ve vg vb va vj vu vv ccnv cima cfn wcel cn0 cdif cmap
      cv cn crab cres ccom cfv cevl cmgp cmpt cgsu cbs eqid cvv ad2antrr mplelf
      co wa adantr ffvelcdmda ccrg fvexd simpr evlsvvvallem ringcld eqidd fveq1
      wf a1i cmnd syl ad3antrrr psrbagf adantl fssresd mulgnn0cld cmhm wceq crh
      eqcomd oveq1d syl3anc oveq2d mpteq2dva ccmn eqeltrrd fveq2d eqtrid fmpttd
      eqtrd c0g cur cfsupp feqmptd psrbagfsupp eqbrtrrd mulg0 fsuppssov1 gsumcl
      cc0 wbr fveq1d evlvvval ovex rabex wfun csupp ssidd suppssr fsuppsssuppgd
      funmpt suppss2 fveq2 mpteq2dv oveq12d cz fvresd cslv cmg cmpo csca difssd
      cmulr ssexd mplcrngd crngringd selvcl mplasclf elmapdd elmapssresd mapcod
      crg fvexi fmptco cvsca mgpbas ringmgp elmapi casa mplassa syl2anc asclrhm
      cofmpt mplsca eleqtrd rhmmhm mhmmulg crngmgp eleqtrdi ringidval breqtrrdi
      fvco3d eqtr4d eqtrdi breqtrd eqtr3d asclmul2 eleqtrrd mplvscaval crngcomd
      gsummhm an32s evlcl fvmptd3 ringcmnd crnggrpd grpmndd cghm cgrp mplmapghm
      simplr ghmmhm evlvvvallem 3eqtr4rd mplelsfi csn cxp mpl0 fvconst2 ringlzd
      mptex fvex gsummulc1 3eqtr4d simpl fveq12d ovmpoa cun psrbagres ffvelcdmd
      adantll wss adantlr mptexd fsuppres eldifi sylan2 selvvvval eqbrtrd ovexd
      evlselvlem gsumf1o ad2antrl ad2antll c0 disjdifr fun2d undifr sylib feq2d
      0zd cin mpbid vex unex fsuppun isfsuppd wb fcdmnn0fsuppg psrbag mpbir2and
      ffund csb reseq1 csbie wfn fnunres2 fnunres1 fmpocos anasss simprr simprl
      ffnd wral ralrimivva fmpo wf1o wf1 f1of1 fsuppco gsumxp ringassd mgpplusg
      3eqtrd disjdif undif gsumsplit resmptd cbvmptv eqtr2d 3eqtr2d ) AEUEUFVEU
      RVFUSUTVAZUFVBIJVCZVDVTZVGZUEVEZLBJVHZVIZHJIEUUAVTVJVJZJGVKVTZVJVJZVJZEVL
      VJZUGVVPUGVEZVVSVJZVWGBVVPVHZVJZVWFUUBVJZVTZVMZVNVTZEUUFVJZVTZVMZVNVTZEUH
      UIVEURVFUSUTVAZUIVBIVDVTZVGZUHVEZHVJZVWFUJIUJVEZVXBVJZVXDBVJZVWKVTZVMZVNV
      TZVWOVTZVMZVNVTZVWIVWDVVPEVKVTZVJVJBHIEVKVTZVJVJAVWREUEVVREUKULVEURVFUSUT
      VAZULVBJVDVTZVGZVVSUKVEZUMUNVVRVXQUMVEZUNVEZVWBVJZVJZVWFUOJUOVEZVXTVJZVYC
      VVTVJZVWKVTZVMZVNVTZVWOVTZVWFUGVVPVWGVXSVJZVWJVWKVTZVMZVNVTZVWOVTZUUCZVTZ
      VMZVNVTZVMZVNVTZEUHVXAVXBVVPVHZVXBJVHZVWBVJZVJZVWFUOJVYCWUBVJZVYEVWKVTZVM
      ZVNVTZVWOVTZVWFUGVVPVWGWUAVJZVWJVWKVTZVMZVNVTZVWOVTZVMZVNVTZVXLAVWQVYSEVN
      AUEVVRVWPVYRAVVSVVRVAZWAZVWPEUKVXQVVSVXRVWBVJZVJZVWFUOJVYCVXRVJZVYEVWKVTZ
      VMZVNVTZVWOVTZVWNVWOVTZVMZVNVTZVYRWUREUPGVOVJZVVSUPVEZVJZVMZUKVXQWUSGVLVJ
      ZUOJWVAVYCVWAVJZWVMUUBVJZVTZVMZVNVTZGUUFVJZVTZVMZVIZVNVTZVWNVWOVTEUKVXQWV
      EVMZVNVTZVWNVWOVTVWPWVHWURWWCWWEVWNVWOWURWWCEUKVXQGUUDVJZVLVJZWVCVNVTZWUT
      VWOVTZVMZVNVTWWEWURWWBWWJEVNWURWWBUKVXQVVSWVTVJZVMWWJWURUKUPVXQWVIWVTWVKW
      WKWWAWVLWURVXRVXQVAZWAZWVIGWVSWUSWVRWVIVPZWVSVPZAGUUOVAZWUQWWLAGAGEVVPVQQ
      AVVPIMTAIJUUEZUUGZUAUUHZUUIZVRWURVXQWVIVXRVWBAVXQWVIVWBWKZWUQAFVOVJZVXQFG
      ULJWVIVWBRWWNWXBVPZVXQVPZACDEFGWXBHIJNPQRWXCUAUBUCUUJZVSZWBZWCZWWMUOVWAVX
      RVXQGULWVOJWVIWVMVQWXDWWNWVMVPZWVOVPZAJVQVAZWUQWWLAJIMTUBUUGZVRZAGWDVAZWU
      QWWLWWSVRAVWAWVIJVDVTVAZWUQWWLAWVIKJLVVTAWVIKLVQVQAGVOWEKVQVAAKEVOOUUPWLA
      LWVIGEVVPKVQQWWNOSWWRAEUAUUIZUUKZUULABKIJUDUBUUMZUUNZVRWURWWLWFWGWHZWURWW
      AWIWURWVLWIVVSWVJWVTWJUUQWURUKVXQWWKWWIWWMWWKVVSWWHWUSGUURVJZVTZVJWWIWWMV
      VSWVTWYBWWMWVTWUSWWHLVJZWVSVTZWYBWWMWVRWYCWUSWVSWWMWVMLWVCVIZVNVTWVRWYCWW
      MWYEWVQWVMVNWWMWYEUOJWVBLVJZVMWVQWWMUOJWVBKWVILAKWVILWKWUQWWLWXQVRWWMVYCJ
      VAZWAZKVWKVWFWVAVYEKEVWFVWFVPZOUUSZVWKVPZAVWFWMVAZWUQWWLWYGAEUUOVAZWYLWXP
      EVWFWYIUUTWNZWOWWMJVBVYCVXRWWLJVBVXRWKWURVXQULVXRJWXDWPWQZWCZWWMJKVYCVVTA
      JKVVTWKZWUQWWLAIKJBABKIVDVTVAIKBWKZUDBKIUVAWNZUBWRZVRWCZWSZUVFWWMUOJWYFWV
      PWYHWYFWVAVYELVJZWVOVTZWVPWYHLVWFWVMWTVTVAZWVAVBVAVYEKVAZWYFXUDXAAXUEWUQW
      WLWYGALEGXBVTZVAXUEALWWFGXBVTZXUGAGUVBVAZLXUHVAZAVVPVQVAZEWDVAZXUIWWRUAGE
      VVPVQQUVCUVDZLWWFGSWWFVPZUVEWNZAWWFEGXBAEWWFAGEVVPVQWDQWWRUAUVGZXCZXDUVHE
      GLVWFWVMWYIWXIUVIWNWOWYPXUAKVWKWVOLVWFWVMWVAVYEWYJWYKWXJUVJXEWYHWVNXUCWVA
      WVOWYHJKVYCLVVTAWYQWUQWWLWYGWYTWOWWMWYGWFUVOXFUVPXGXMXFWWMJWWGVOVJZWVCWWG
      WVMLVQWWGXNVJZXURVPXUSVPAWWGXHVAZWUQWWLAWWFWDVAXUTAEWWFWDXUPUAXIWWFWWGWWG
      VPZUVKWNVRZAWVMWMVAZWUQWWLAWWPXVCWWTGWVMWXIUUTWNVRWXMALWWGWVMWTVTVAZWUQWW
      LAXUJXVDXUOWWFGLWWGWVMXVAWXIUVIWNVRWWMUOJWVBXURWYHWVBWWFVOVJZXURWYHWVBKXV
      EXUBAKXVEXAZWUQWWLWYGAKEVOVJZXVEOAEWWFVOXUPXJXKZWOUVHZXVEWWFWWGXVAXVEVPZU
      USZUVLXLWWMWVCEXOVJZXUSXPWWMWVCVWFXNVJZXVLXPWWMUOUGWVAVYEJKVWKVBVQYCXVMWW
      MVXRUOJWVAVMYCXPWWMUOJVBVXRWYOXQWWLVXRYCXPYDWURVXQULVXRJWXDXRWQXSVWGKVAZY
      CVWGVWKVTXVMXAZWWMKVWKVWFVWGXVMWYJXVMVPZWYKXTZWQWYPXUAWWMVWFXNWEYAEXVLVWF
      WYIXVLVPUVMUVNAXVLXUSXAWUQWWLAXVLWWFXOVJZXUSAEWWFXOXUPXJWWFXVRWWGXVAXVRVP
      UVMZUVQVRUVRZUWDUVSXFWWMXUIWWHXVEVAWUSWVIVAWYDWYBXAAXUIWUQWWLXUMVRWWMJXVE
      WVCWWGVQXVRXVKXVSXVBWXMWWMUOJWVBXVEXVIXLWWMWVCXUSXVRXPXVTXVSUVNYBZWXHLWWH
      WYAWVSWWFXVEWVIGWUSSXUNXVJWWNWWOWYAVPZUVTXEXMYEWWMWVIVVRGEWYAVWOUFWUSVVPK
      WWHVVSQXWBOWWNVWOVPZVVRVPZWWMWWHXVEKXWAAXVFWUQWWLXVHVRUWAZWXHAWUQWWLUWNUW
      BXMXGXMXFWURWWJWWDEVNWURUKVXQWWIWVEWWMWWIWVDWUTVWOVTWVEWWMWWHWVDWUTVWOWWM
      WWGVWFWVCVNAWWGVWFXAWUQWWLAWWFEVLXUQXJVRXDZXDWWMKEVWOWVDWUTOXWCAXULWUQWWL
      UAVRWWMWWHWVDKXWFXWEXIZAWWLWUQWUTKVAAWWLWAZVVRKVVSWUSXWHWVIVVRGEUFVVPKWUS
      QOWWNXWDAVXQWVIVXRVWBWXFWCVSWCUWEZUWCXMXGXFXMXDWURVWEWWCVWNVWOWURGWWAVNVT
      ZWVLVJVVSXWJVJZWWCVWEWURUPXWJWVKXWKWVIWVLVQWVLVPZVVSWVJXWJWJAXWJWVIVAWUQA
      VWDXWJWVIAVWAWXBVXQFVWCGWVSULUOWVOVWBJWVIWVMVQUKVWCVPZRWXCWXDWWNWXIWXJWWO
      WXLWWSWXEWXSYFZAVWAWXBFVWCGVWBJWVIVQXWMRWXCWWNWXLWWSWXEWXSUWFZXIWBWURVVSX
      WJWEUWGWURVXQWVIWWAGEWVLVQGXNVJZWWNXWPVPZAGXHVAWUQAGWWTUWHWBAEWMVAWUQAEAE
      UAUWIZUWJWBVXQVQVAZWURVXOULVXPVBJVDYGYHZWLZWURWVLGEUWKVTVAWVLGEWTVTVAWURW
      VIVVRGEUFVVSWVLVVPVQUPQWWNXWDXWLAXUKWUQWWRWBZAEUWLVAWUQXWRWBAWUQWFUWMGEWV
      LUWOWNWURUKVXQWVTWVIWXTXLWURUOVWAWXBVXQFGWVSULWVOVWBJWVIWVMVQUKWXDRWXCWWN
      WXIWXJWWOAWXKWUQWXLWBAWXNWUQWWSWBAVWBWXBVAWUQWXEWBAWXOWUQWXSWBUWPUWDWURVV
      SVWDXWJAVWDXWJXAWUQXWNWBYEUWQXDWURVXQKEVWOUKVQWVEVWNEXNVJZOXXCVPZXWCAWYMW
      UQWXPWBXXAWURVVPKVWMVWFVQXVMWYJXVPAVWFXHVAZWUQAXULXXEUAEVWFWYIUVKWNZWBXXB
      WURUGVVPVWLKWURVWGVVPVAZWAZKVWKVWFVWHVWJWYJWYKAWYLWUQXXGWYNVRWURVVPVBVWGV
      VSWUQVVPVBVVSWKAVVRUFVVSVVPXWDWPWQZWCWURVVPKVWGVWIAVVPKVWIWKWUQAIKVVPBWYS
      WWQWRZWBWCZWSXLWURUGUQVWHVWJVVPKVWKVQVQYCXVMWURVVSUGVVPVWHVMYCXPWURUGVVPV
      BVVSXXIXQWUQVVSYCXPYDAVVRUFVVSVVPXWDXRWQXSUQVEZKVAZYCXXLVWKVTXVMXAWURKVWK
      VWFXXLXVMWYJXVPWYKXTWQXXHVWGVVSWEXXKWURVWFXNWEYAYBWWMKEVWOWUTWVDOXWCAWYMW
      UQWWLWXPVRXWIXWGWHWURUKUQWUTWVDVXQKVWOKVQXXCXXCWURVWBUKVXQWUTVMZXWPVQVQXX
      CXXNVQVAWURUKVXQWUTXWTUXDWLWUREXNWEZXXNYIWURUKVXQWUTYNWLAVWBXWPXPYDWUQAWX
      BFGVWBJXWPRWXCXWQWXEUWRWBWURVXQWUTUKVQVWBXWPYJVTZXXCWURVXRVXQXXPVCVAZWAZW
      UTVVSXWPVJZXXCXXRVVSWUSXWPWURVXQWVIVQVWBVQXXPVXRXWPWXGWURXXPYKXXAWURGXNWE
      YLYEWURXXSXXCXAXXQWURXXSVVSVVRXXCUWSUWTZVJZXXCWURVVSXWPXXTAXWPXXTXAWUQAVV
      RGEUFVVPXXCVQXWPQXWDXXDXWQWWRXWRUXAWBYEWUQXYAXXCXAAVVRXXCVVSEXNUXEUXBWQXM
      WBXMXXAYOYMWURXXMWAKEVWOXXLXXCOXWCXXDAWYMWUQXXMWXPVRWURXXMWFUXCXWIXWGXXOY
      AUXFUXGWURVYQWVGEVNWURUKVXQVYPWVFWUQWWLVYPWVFXAAUMUNVVSVXRVVRVXQVYNWVFVYO
      VXSVVSXAZVXTVXRXAZWAZVYIWVEVYMVWNVWOXYDVYBWUTVYHWVDVWOXYDVXSVVSVYAWUSXYCV
      YAWUSXAXYBVXTVXRVWBYPWQXYBXYCUXHUXIXYDVYGWVCVWFVNXYDUOJVYFWVBXYDVYDWVAVYE
      VWKXYCVYDWVAXAXYBVYCVXTVXRWJWQXDYQXFYRXYDVYLVWMVWFVNXYDUGVVPVYKVWLXYDVYJV
      WHVWJVWKXYBVYJVWHXAXYCVWGVXSVVSWJWBXDYQXFYRVYOVPZWVEVWNVWOYGUXJUXNXGXFUVP
      XGXFAWUPEWUOUMUNVVRVXQVXSVXTUXKZUUCZVIZVNVTEVYOVNVTVYTAVXAKVVRVXQUWTZWUOE
      XYGVQXXCOXXDAEWXPUWHZVXAVQVAAVWSUIVWTVBIVDYGYHZWLAUHVXAWUNKAVXBVXAVAZWAZK
      EVWOWUIWUMOXWCAWYMXYLWXPWBZXYMKEVWOWUDWUHOXWCXYNXYMVVRKWUAWUCXYMWVIVVRGEU
      FVVPKWUCQOWWNXWDXYMVXQWVIWUBVWBAWXAXYLWXFWBXYMVXAULUIVXQVXBIJMVXAVPZWXDAI
      MVAZXYLTWBZAJIUXOZXYLUBWBZAXYLWFZUXLUXMVSXYMVXAUFUIVVRVXBIVVPMXYOXWDXYQXY
      MIJUUEZXYTUXLUXMZXYMJKWUGVWFVQXVMWYJXVPAXXEXYLXXFWBZAWXKXYLWXLWBZXYMUOJWU
      FKXYMWYGWAZKVWKVWFWUEVYEWYJWYKAWYLXYLWYGWYNVRXYMJVBVYCWUBXYMIVBJVXBXYLIVB
      VXBWKAVXAUIVXBIXYOWPWQZXYSWRZWCAWYGXUFXYLAJKVYCVVTWYTWCUXPZWSXLXYMWUBWUGY
      CVQVQXVMAWUGVQVAXYLAUOJWUFVQWXLUXQWBXYMVWFXNWEZWUGYIXYMUOJWUFYNWLXYMVXBYS
      JYCXYLVXBYCXPYDAVXAUIVXBIXYOXRWQZXYMUYNZUXRXYMJWUFUOVQWUBYCYJVTZXVMXYMVYC
      JYULVCVAZWAZWUFYCVYEVWKVTZXVMYUNWUEYCVYEVWKXYMJVBYSWUBVQYULVYCYCYUGXYMYUL
      YKYUDYUKYLXDYUMXYMWYGYUOXVMXAZVYCJYULUXSYUEXUFYUPYUHKVWKVWFVYEXVMWYJXVPWY
      KXTWNUXTXMYUDYOYMYBZWHXYMVVPKWULVWFVQXVMWYJXVPYUCAXUKXYLWWRWBZXYMUGVVPWUK
      KXYMXXGWAZKVWKVWFWUJVWJWYJWYKAWYLXYLXXGWYNVRXYMVVPVBVWGWUAXYMIVBVVPVXBYUF
      YUAWRZWCAXXGVWJKVAZXYLAVVPKVWGVWIXXJWCUXPZWSXLXYMWUAWULYCVQVQXVMXYMUGVVPW
      UKVQYURUXQYUIWULYIXYMUGVVPWUKYNWLXYMVXBYSVVPYCYUJYUKUXRXYMVVPWUKUGVQWUAYC
      YJVTZXVMXYMVWGVVPYVCVCVAZWAZWUKYCVWJVWKVTZXVMYVEWUJYCVWJVWKXYMVVPVBYSWUAV
      QYVCVWGYCYUTXYMYVCYKYURYUKYLXDYVEYVAYVFXVMXAYVDXYMXXGYVAVWGVVPYVCUXSYVBUX
      TKVWKVWFVWJXVMWYJXVPWYKXTWNXMYURYOYMYBZWHXLAUHUQWUIWUMVXAKVWOVQVQXXCXXCAU
      HUQWUDWUHVXAKVWOVQVQXXCXXCAUHVXAWUDVMUHVXAVXCVMZXXCXPAUHVXAWUDVXCXYMCVXAD
      EUIHIJVXBXYONPAXULXYLUAWBXYSAHCVAXYLUCWBXYTUYAZXGAHYVHXXCXPAUHVXAXVGHACVX
      ADEUIIXVGHNXVGVPPXYOUCVSXQACDEHIXXCNPXXDUCUWRXSUYBAXXMWAKEVWOXXLXXCOXWCXX
      DAWYMXXMWXPWBAXXMWFUXCZXYMWUAWUCWEYUQAEXNWEZYAYVJXYMWUDWUHVWOUYCYVGYVKYAZ
      AVVRVXAUNUFULUIVXQXYGIJMUMXYOWXDXWDXYGVPTUBUYDZUYEAXYHVYOEVNAUMUNUHVVRVXQ
      VXAXYFWUNVYNXYGWUOAVXSVVRVAZVXTVXQVAZWAZWAZXYFVXAVAZIVBXYFWKZXYFURVFUSUTV
      AZYVQVVPJUXKZVBXYFWKYVSYVQVVPJVBVXSVXTYVNVVPVBVXSWKAYVOVVRUFVXSVVPXWDWPZU
      YFYVOJVBVXTWKAYVNVXQULVXTJWXDWPUYGZVVPJUYOUYHXAZYVQJIUYIWLZUYJYVQYWAIVBXY
      FAYWAIXAZYVPAXYRYWFUBJIUYKUYLWBUYMUYPZYVQXYFYCXPYDZYVTYVQXYFVQYSYCXYFVQVA
      ZYVQVXSVXTUMUYQUNUYQUYRZWLZYVQUYNYVQIVBXYFYWGVUEYVQVXSVXTYCYVNVXSYCXPYDAY
      VOVVRUFVXSVVPXWDXRUYFYVOVXTYCXPYDAYVNVXQULVXTJWXDXRUYGUYSUYTYVQYWIYVSYWHY
      VTVUAYWKYWGXYFIVQVUBUVDUYPYVQXYPYVRYVSYVTWAVUAAXYPYVPTWBVXAUIXYFIMXYOVUCW
      NVUDAXYGWIAWUOWIYVQUHXYFWUNVUFXYFVVPVHZXYFJVHZVWBVJZVJZVWFUOJVYCYWMVJZVYE
      VWKVTZVMZVNVTZVWOVTZVWFUGVVPVWGYWLVJZVWJVWKVTZVMZVNVTZVWOVTZVYNUHXYFWUNYX
      EYWJVXBXYFXAZWUIYWTWUMYXDVWOYXFWUDYWOWUHYWSVWOYXFWUAYWLWUCYWNYXFWUBYWMVWB
      VXBXYFJVUGZXJVXBXYFVVPVUGZUXIYXFWUGYWRVWFVNYXFUOJWUFYWQYXFWUEYWPVYEVWKYXF
      VYCWUBYWMYXGYEXDYQXFYRYXFWULYXCVWFVNYXFUGVVPWUKYXBYXFWUJYXAVWJVWKYXFVWGWU
      AYWLYXHYEXDYQXFYRVUHYVQYWTVYIYXDVYMVWOYVQYWOVYBYWSVYHVWOYVQYWLVXSYWNVYAYV
      QYWMVXTVWBYVQVXSVVPVUIZVXTJVUIZYWDYWMVXTXAYVNYXIAYVOYVNVVPVBVXSYWBVUPUYFZ
      YVQJVBVXTYWCVUPZYWEVVPJVXSVXTVUJXEZXJYVQYXIYXJYWDYWLVXSXAYXKYXLYWEVVPJVXS
      VXTVUKXEZUXIYVQYWRVYGVWFVNYVQUOJYWQVYFYVQYWPVYDVYEVWKYVQVYCYWMVXTYXMYEXDY
      QXFYRYVQYXCVYLVWFVNYVQUGVVPYXBVYKYVQYXAVYJVWJVWKYVQVWGYWLVXSYXNYEXDYQXFYR
      XKVULZXFAVVRKVXQUEUKVYOEVQVQXXCOXXDXYJVVRVQVAAVVOUFVVQVBVVPVDYGYHWLXWSAXW
      TWLAVYNKVAZUNVXQVUQUMVVRVUQXYIKVYOWKAYXPUMUNVVRVXQYVQKEVWOVYIVYMOXWCAWYMY
      VPWXPWBZYVQKEVWOVYBVYHOXWCYXQAYVNYVOVYBKVAZAYVOYVNYXRAYVOWAZVVRKVXSVYAYXS
      WVIVVRGEUFVVPKVYAQOWWNXWDAVXQWVIVXTVWBWXFWCVSWCUWEVUMYVQUOVVTVXTVXQEULVWK
      JKVWFVQWXDOWYIWYKAWXKYVPWXLWBAXULYVPUAWBZAVVTKJVDVTVAYVPWXRWBAYVNYVOVUNWG
      WHYVQUGVWIVXSVVREUFVWKVVPKVWFVQXWDOWYIWYKAXUKYVPWWRWBYXTAVWIKVVPVDVTVAYVP
      ABKIVVPUDWWQUUMZWBAYVNYVOVUOWGWHVURUMUNVVRVXQVYNKVYOXYEVUSUYLAXYHVYOXXCXP
      YXOAWUOXYGVQVQXYIVXAXXCYVLAXYIVXAXYGVUTXYIVXAXYGVVAYVMXYIVXAXYGVVBWNYVKWU
      OVQVAAUHVXAWUNXYKUXDWLVVCXSVVDVVGAWUOVXKEVNAUHVXAWUNVXJXYMWUNWUDWUHWUMVWO
      VTZVWOVTVXJXYMKEVWOWUDWUHWUMOXWCXYNYUBYUQYVGVVEXYMWUDVXCYYBVXIVWOYVIXYMVX
      IVWFVXHJVHZVNVTZVWFVXHVVPVHZVNVTZVWOVTYYBXYMIKJVVPVWOVXHVWFMXVMWYJXVPEVWO
      VWFWYIXWCVVFYUCXYQXYMUJIVXGKXYMVXDIVAZWAKVWKVWFVXEVXFWYJWYKAWYLXYLYYGWYNV
      RXYMIVBVXDVXBYUFWCZXYMIKVXDBAWYRXYLWYSWBWCZWSXLXYMUJUGVXEVXFIKVWKVBVQYCXV
      MXYMVXBUJIVXEVMYCXPXYMUJIVBVXBYUFXQYUJXSXVNXVOXYMXVQWQYYHYYIYUIYAJVVPUYOU
      YHXAXYMJIVVHWLAIJVVPUXKZXAXYLAYYJIAXYRYYJIXAUBJIVVIUYLXCWBVVJXYMYYDWUHYYF
      WUMVWOXYMYYCWUGVWFVNXYMYYCUJJVXGVMZWUGXYMUJIJVXGXYSVVKXYMYYKUOJVYCVXBVJZV
      YCBVJZVWKVTZVMWUGUJUOJVXGYYNVXDVYCXAVXEYYLVXFYYMVWKVXDVYCVXBYPVXDVYCBYPYR
      VVLXYMUOJYYNWUFYUEWUFYYNYUEWUEYYLVYEYYMVWKYUEVYCJVXBXYMWYGWFZYTYUEVYCJBYY
      OYTYRXCXGXKXMXFXYMYYEWULVWFVNXYMYYEUJVVPVXGVMZWULXYMUJIVVPVXGYUAVVKXYMYYP
      UGVVPVWGVXBVJZVWGBVJZVWKVTZVMWULUJUGVVPVXGYYSVXDVWGXAVXEYYQVXFYYRVWKVXDVW
      GVXBYPVXDVWGBYPYRVVLXYMUGVVPYYSWUKYUSWUKYYSYUSWUJYYQVWJYYRVWKYUSVWGVVPVXB
      XYMXXGWFZYTYUSVWGVVPBYYTYTYRXCXGXKXMXFYRVVMYRXMXGXFVVNAVWIWVIVVRGVXMEVWOU
      FUGVWKVWDVVPKVWFVQUEVXMVPQWWNXWDOWYIWYKXWCWWRUAXWOYYAYFABCVXADVXNEVWOUIUJ
      VWKHIKVWFMUHVXNVPNPXYOOWYIWYKXWCTUAUCUDYFUXG $.
  $}

  ${
    $d V z $.  $d V c $.  $d X h $.  $d .+ m x y $.  $d .+ v $.  $d .0. c v $.
    $d .0. a b $.  $d .0. i j $.  $d .0. h n $.  $d .0. l m x y z $.
    $d I a b c h x $.  $d I l m y z $.  $d I j v $.  $d I i n $.  $d H b l $.
    $d H i n $.  $d H y $.  $d H h j m x z $.  $d H a $.  $d ph h j l v x z $.
    $d ph m y $.  $d ph i n $.  $d ph a b c $.  $d B a b z $.  $d B h i n $.
    $d B j l m x $.  $d B c v $.
    fsuppind.b $e |- B = ( Base ` G ) $.
    fsuppind.z $e |- .0. = ( 0g ` G ) $.
    fsuppind.p $e |- .+ = ( +g ` G ) $.
    fsuppind.g $e |- ( ph -> G e. Grp ) $.
    fsuppind.v $e |- ( ph -> I e. V ) $.
    fsuppind.0 $e |- ( ph -> ( I X. { .0. } ) e. H ) $.
    fsuppind.1 $e |- ( ( ph /\ ( a e. I /\ b e. B ) ) ->
                                ( x e. I |-> if ( x = a , b , .0. ) ) e. H ) $.
    fsuppind.2 $e |- ( ( ph /\ ( x e. H /\ y e. H ) ) ->
                                                        ( x oF .+ y ) e. H ) $.
    $( Induction on functions ` F : A --> B ` with finite support, or in other
       words the base set of the free module (see ~ frlmelbas and
       ~ frlmplusgval ).  This theorem is structurally general for polynomial
       proof usage (see ~ mplelbas and ~ mpladd ).  Note that hypothesis 0 is
       redundant when ` I ` is nonempty.  (Contributed by SN, 18-May-2024.) $)
    fsuppind $p |- ( ( ph /\ ( X : I --> B /\ X finSupp .0. ) ) -> X e. H ) $=
      ( vh vn vi vj vc vv vl vm vz wf cfsupp wbr wcel wa csupp co chash cfv cc0
      cn wceq cmap wb cvv fvexi a1i elmapd adantr wi cv c1 eqeq1 imbi1d ralbidv
      wral weu eqcom ovex ax-mp wne wfn elmapfn adantl elsuppfn syl3anc bitr4di
      cif cmpt ad2antlr fvex ifex fnmpti fveq2 ifbieq1d fvmpt3i wn simpr neeq1d
      eqid syl2anc imp eqtr2d eqfnfvd ralrimivva ad2antrr ifbid mpteq2dv eleq1d
      weq eqeq2d biimparc ifeq1da rspc2va syl21anc eqeltrd ex ralrimiva fvoveq1
      wrex syl ad5antr simprl mapfvd ad4antr adantrl csn cn0 ad2antrl ad3antrrr
      simprr simplrr wo adantllr c0 eqnetrrd hasheq0 sylib eleq1w imbi12d caddc
      cbs euhash1 bitri wreu c0g eubidv df-reu crio eqidd simplr riota2 3bitr4g
      necom biimpd necon1bd ifeqda riotacl elmapi ffvelcdmd sylbid biimtrid cof
      eqeq2 oveq1 anbi12d cgrp grpidcl ifcld fmpttd mpbird cdif ovexd mpbir2and
      simpllr nnnn0d eqcomd w3a hashdifsnp1 syl31anc eldifsn iftrue olc iffalse
      eqeq1d biorf orcom bitrd pm2.61i necon3abid neanior anbi2d anass ifbieq2d
      2thd equequ1 pm5.32da anbi1d bitr2d bitrid eqrdv fveq2d eqtr3d inidm offn
      3bitr4d ofval simplrl anassrs grplid grprid ifeq12d ovif12 eqcomi 3eqtr4g
      ifid jca rspcedvdw crab suppvalfn peano2nn ad3antlr nnne0d necon3bid mp1i
      mpbid reximddv rexcom rspccva adantll adantlrr adantrr equequ2 rexlimdvva
      rabn0 ovrspc2v mpd exp32 ralrimiv cbvralvw nnindd ralcom ceqsralv biimpcd
      biidd ralimi eleq1 rspcv syl5com com23 sylbird an32s cxp fnsuppeq0 biimpa
      adantlr ffn sylan2b cfn fsuppimpd hashcl elnn0 mpjaodan anasss ) AHDJUKZJ
      KULUMZJGUNZAVVEUOZVVFUOZJKUPUQZURUSZVAUNZVVGVVKUTVBZVVHVVLVVGVVFAVVLVVEVV
      GAVVLUOZVVEVVGVVNVVEJDHVCUQZUNZVVGAVVPVVEVDVVLADHJVEIDVEUNZADFUUBNVFZVGRV
      HVIAVVLVVPVVGVJAVVPVVLVVGAUBVKZKUPUQZURUSZVAUNZVVSGUNZVJZUBVVOVPZVVPVVLVV
      GVJZAUCVKZVWAVBZVWCVJZUCVAVPZUBVVOVPZVWEAVWIUBVVOVPZUCVAVPVWKAVWLUCVAAUDV
      KZVWAVBZVWCVJZUBVVOVPVLVWAVBZVWCVJZUBVVOVPUEVKZVWAVBZVWCVJZUBVVOVPZVWRVLU
      UAUQZVWAVBZVWCVJZUBVVOVPZVWLUDUEVWGVWMVLVBZVWOVWQUBVVOVXFVWNVWPVWCVWMVLVW
      AVMVNVOVWMVWRVBZVWOVWTUBVVOVXGVWNVWSVWCVWMVWRVWAVMVNVOVWMVXBVBZVWOVXDUBVV
      OVXHVWNVXCVWCVWMVXBVWAVMVNVOVWMVWGVBZVWOVWIUBVVOVXIVWNVWHVWCVWMVWGVWAVMVN
      VOAVWQUBVVOVWPUFVKZVVTUNZUFVQZAVVSVVOUNZUOZVWCVWPVWAVLVBZVXLVLVWAVRVVTVEU
      NVXOVXLVDVVSKUPVSVVTVEUFUUCVTUUDVXNVXLVXJVVSUSZKWAZUFHUUEZVWCVXNVXLVXJHUN
      VXQUOZUFVQVXRVXNVXKVXSUFVXNVVSHWBZHIUNZKVEUNZVXKVXSVDVXMVXTAVVSDHWCZWDAVY
      AVXMRVIVYBVXNKFUUFOVFZVGVXJVVSIVEHKWEWFUUGVXQUFHUUHWGVXNVXRVWCVXNVXRUOZVV
      SBHBVKZVXQUFHUUIZVBZVYFVVSUSZKWHZWIZGVYEUGHVVSVYKVXMVXTAVXRVYCWJVYKHWBVYE
      BHVYJVYKVYHVYIKVYFVVSWKVYDWLZVYKWTZWMVGVYEUGVKZHUNZUOZVYNVYKUSZVYNVYGVBZV
      YNVVSUSZKWHZVYSVYOVYQVYTVBVYEBVYNVYJVYTHVYKVYFVYNVBZVYHVYRVYIVYSKVYFVYNVY
      GVMVYFVYNVVSWNWOVYMVYLWPWDVYPVYRVYSKVYSVYPVYRUOVYSUUJVYPVYRWQKVYSVBVYPVYR
      KVYSVYPKVYSWAZVYRVYPVYSKWAZVYGVYNVBZWUBVYRVYPVYOVXRWUCWUDVDVYEVYOWRVXNVXR
      VYOUUKVXQWUCUFHVYNVXJVYNVBVXPVYSKVXJVYNVVSWNWSUULXAKVYSUUNVYNVYGVRUUMUUOU
      UPXBUUQXCXDVYEVYGHUNZVYGVVSUSZDUNBHBLXJZMVKZKWHZWIZGUNZMDVPLHVPZVYKGUNZVX
      RWUEVXNVXQUFHUURWDZVYEHDVYGVVSVXMHDVVSUKAVXRVVSDHUUSWJWUNUUTAWULVXMVXRAWU
      KLMHDTXEZXFWUKWUMBHVYHWUHKWHZWIZGUNLMVYGWUFHDLVKZVYGVBZWUJWUQGWUSBHWUIWUP
      WUSWUGVYHWUHKWURVYGVYFUVDXGXHXIWUHWUFVBZWUQVYKGWUTBHWUPVYJWUTVYHWUHVYIKVY
      HWUHVYIVBWUTVYHVYIWUFWUHVYFVYGVVSWNXKXLXMXHXIXNXOXPXQUVAUVBXRAVWRVAUNZUOZ
      VXAUOZVXBUHVKZKUPUQZURUSZVBZWVDGUNZVJZUHVVOVPVXEWVCWVIUHVVOWVCWVDVVOUNZWV
      GWVHWVCWVJWVGUOZUOZVWRUIVKZKUPUQURUSZVBZWVDWVMBHVYFUJVKZVBZVYFWVDUSZKWHZW
      IZEUVCZUQZVBZUOZUJHXTUIVVOXTZWVHWVLWWDUIVVOXTZUJHXTWWEWVLWVPWVDUSZKWAZWWF
      UJHWVLWVPHUNZWWHUOZUOWWDVWRBHWVQKWVRWHZWIZKUPUQZURUSZVBZWVDWWLWVTWWAUQZVB
      ZUOZUIWWLVVOWVMWWLVBZWVOWWOWWCWWQWWSWVNWWNVWRWVMWWLKURUPXSXKWWSWWBWWPWVDW
      VMWWLWVTWWAUVEXKUVFWVLWWHWWLVVOUNZWWIWVLWWHUOZWWTHDWWLUKWXABHWWKDWXAVYFHU
      NZUOZWVQKWVRDAKDUNZWVAVXAWVKWWHWXBAFUVGUNZWXDQDFKNOUVHYAYBWXCDHWVDVVOVYFV
      VOWTZWVLWVJWWHWXBWVCWVJWVGYCZXFWXAWXBWRYDUVIUVJWXADHWWLVEIVVQWXAVVRVGAVYA
      WVAVXAWVKWWHRYEVHUVKYFWVBWVKWWJWWRVXAWVBWVKUOZWWJUOZWWOWWQWXIWVEWVPYGUVLZ
      URUSZVWRWWNWXIWVEVEUNZWVPWVEUNZVWRYHUNZWVFVXBVBZWXKVWRVBZWXIWVDKUPUVMWXIW
      XMWWIWWHWXHWWIWWHYCWXHWWIWWHYKWXIWVDHWBZVYAVYBWXMWWJVDWXHWXQWWJWVJWXQWVBW
      VGWVDDHWCZYIZVIAVYAWVAWVKWWJRYJVYBWXIVYDVGWVPWVDIVEHKWEWFUVNWXIVWRAWVAWVK
      WWJUVOUVPWXIVXBWVFWVBWVJWVGWWJYLUVQWXLWXMWXNUVRWXOWXPWVPWVEVEVWRUVSXBUVTW
      XHWWHWXKWWNVBWWIWXHWWHUOZWXJWWMURWXTUGWXJWWMVYNWXJUNVYNWVEUNZVYNWVPWAZUOZ
      WXTVYNWWMUNZVYNWVEWVPUWAWXTWYDVYOVYNWWLUSZKWAZUOZWYCWXTWWLHWBZVYAVYBWYDWY
      GVDWYHWXTBHWWKWWLWVQKWVRVYDVYFWVDWKZWLZWWLWTZWMVGZAVYAWVAWVKWWHRYJZVYBWXT
      VYDVGZVYNWWLIVEHKWEWFWXTVYOVYNWVPVBZKVYNWVDUSZWHZKWAZUOZVYOWYPKWAZUOZWYBU
      OZWYGWYCWXTWYSVYOWYTWYBUOZUOXUBWXTWYRXUCVYOWXTWYRWYPKVBZWYOYMZWQXUCWXTXUE
      WYQKWYQKVBZXUEVDZWXTWYOXUGWYOXUFXUEWYOKWYPUWBWYOXUDUWCUWOWYOWQZXUFXUDXUEX
      UHWYQWYPKWYOKWYPUWDUWEXUHXUDWYOXUDYMXUEWYOXUDUWFXUDWYOUWGWGUWHUWIVGUWJWYP
      KVYNWVPUWKWGUWLVYOWYTWYBUWMWGWXTVYOWYFWYRWXTVYOUOZWYEWYQKVYOWYEWYQVBWXTBV
      YNWWKWYQHWWLWUAWVQWYOWVRWYPKBUGUJUWPZVYFVYNWVDWNZUWNWYKWYJWPWDZWSUWQWXTWY
      AXUAWYBWXTWXQVYAVYBWYAXUAVDWXHWXQWWHWXSVIZWYMWYNVYNWVDIVEHKWEWFUWRUXFUWSU
      WTUXAUXBYFUXCWXHWWHWWQWWIWXTUGHWVDWWPXUMWXTHHEHWWLWVTIIWYLWVTHWBWXTBHWVSW
      VTWVQWVRKWYIVYDWLZWVTWTZWMVGZWYMWYMHUXDZUXEXUIVYNWWPUSWYQWYOWYPKWHZEUQZWY
      PWXTHHWYQXUREHWWLWVTIIVYNWYLXUPWYMWYMXUQXULVYOVYNWVTUSXURVBWXTBVYNWVSXURH
      WVTWUAWVQWYOWVRWYPKXUJXUKWOXUOXUNWPWDUXGXUIWYOKWYPEUQZWYPKEUQZWHZWYOWYPWY
      PWHZXUSWYPXUIWXEWYPDUNZXVBXVCVBAWXEWVAWVKWWHVYOQYEXUIDHWVDVVOVYNWXFWXHWWH
      VYOWVJWVBWVJWVGWWHVYOUOUXHUXIWXTVYOWRYDWXEXVDUOWYOXUTWYPXVAWYPDEFWYPKNPOU
      XJDEFWYPKNPOUXKUXLXAWYOKWYPWYPKEUXMXVCWYPWYOWYPUXPUXNUXOXCXDYFUXQYNUXRWVL
      WWHUJHUXSZYOWAWWHUJHXTWVLWVEXVEYOWVLWXQVYAVYBWVEXVEVBWVJWXQWVCWVGWXRYIAVY
      AWVAVXAWVKRYJVYBWVLVYDVGUJWVDIVEHKUXTWFWVLWVFUTWAZWVEYOWAZWVLVXBWVFUTWVCW
      VJWVGYKWVLVXBWVAVXBVAUNAVXAWVKVWRUYAUYBUYCYPWXLXVFXVGVDWVLWVDKUPVSWXLWVFU
      TWVEYOWVEVEYQUYDUYEUYFYPWWHUJHUYOYRUYGWWDUJUIHVVOUYHYRWVLWWDWVHUIUJVVOHWV
      LWVMVVOUNZWWIUOZUOZWWDWVHXVJWWDUOZWVDWWBGXVJWVOWWCYKXVKWVMGUNZWVTGUNZVYFC
      VKWWAUQGUNZCGVPBGVPZWWBGUNXVJWVOXVLWWCWVLXVHWVOXVLWWIWVCXVHWVOXVLWVKWVCXV
      HUOWVOXVLVXAXVHWVOXVLVJZWVBVWTXVPUBWVMVVOVVSWVMVBZVWSWVOVWCXVLXVQVWAWVNVW
      RVVSWVMKURUPXSXKUBUIGYSYTUYIUYJXBYNUYKUYLXVKWWIWWGDUNWULXVMWVLXVHWWIWWDYL
      ZXVKDHWVDVVOWVPWXFWVLWVJXVIWWDWXGXFXVRYDAWULWVAVXAWVKXVIWWDWUOYBWUKXVMBHW
      VQWUHKWHZWIZGUNLMWVPWWGHDLUJXJZWUJXVTGXWABHWUIXVSXWAWUGWVQWUHKLUJBUYMXGXH
      XIWUHWWGVBZXVTWVTGXWBBHXVSWVSXWBWVQWUHWVRKWVQWUHWVRVBXWBWVQWVRWWGWUHVYFWV
      PWVDWNXKXLXMXHXIXNXOAXVOWVAVXAWVKXVIWWDAXVNBCGGUAXEYBBCGGGWWAWVMWVTUYPXOX
      PXQUYNUYQUYRUYSWVIVXDUHUBVVOWVDVVSVBZWVGVXCWVHVWCXWCWVFVWAVXBWVDVVSKURUPX
      SXKUHUBGYSYTUYTYRVUAXRVWIUCUBVAVVOVUBYRVWJVWDUBVVOVWBVWJVWCVWCVWCUCVWAVAV
      WHVWCVUEVUCVUDVUFYAVWDVWFUBJVVOVVSJVBZVWBVVLVWCVVGXWDVWAVVKVAVVSJKURUPXSX
      IVVSJGVUGYTVUHVUIVUJXBVUKXBVULVUPVVMVVIVVJYOVBZVVGVVJVEUNVVMXWEVDJKUPVSVV
      JVEYQVTVVIXWEUOJHKYGVUMZGVVIXWEJXWFVBZVVIJHWBZVYAVYBXWEXWGVDVVEXWHAVVFHDJ
      VUQWJAVYAVVEVVFRXFVYBVVIVYDVGHJVEIKVUNWFVUOAXWFGUNVVEVVFXWESYJXPVURVVIVVK
      YHUNZVVLVVMYMVVIVVJVUSUNXWIVVIJKVVHVVFWRVUTVVJVVAYAVVKVVBYRVVCVVD $.
  $}

  ${
    $d ph x $.  $d F x $.  $d I x $.
    fsuppssindlem1.z $e |- ( ph -> .0. e. W ) $.
    fsuppssindlem1.v $e |- ( ph -> I e. V ) $.
    fsuppssindlem1.1 $e |- ( ph -> F : I --> B ) $.
    fsuppssindlem1.2 $e |- ( ph -> ( F supp .0. ) C_ S ) $.
    $( Lemma for ~ fsuppssind .  Functions are zero outside of their support.
       (Contributed by SN, 15-Jul-2024.) $)
    fsuppssindlem1 $p |- ( ph ->
               F = ( x e. I |-> if ( x e. S , ( ( F |` S ) ` x ) , .0. ) ) ) $=
      ( cv cfv cmpt wcel cres wa wceq cif feqmptd fvres adantl wn eldif suppssr
      cdif eqcomd sylan2br anassrs ifeqda mpteq2dva eqtr4d ) AEBFBNZEOZPBFUODQZ
      UOEDROZIUAZPABFCELUBABFUSUPAUOFQZSZUQURIUPUQURUPTVAUODEUCUDAUTUQUEZIUPTZU
      TVBSAUOFDUHQZVCUOFDUFAVDSUPIAFCHEGDUOILMKJUGUIUJUKULUMUN $.
  $}

  ${
    $d I f x $.  $d S f x $.  $d F f x $.  $d .0. f x $.  $d H f $.  $d B f $.
    fsuppssindlem2.b $e |- ( ph -> B e. W ) $.
    fsuppssindlem2.v $e |- ( ph -> I e. V ) $.
    fsuppssindlem2.s $e |- ( ph -> S C_ I ) $.
    $( Lemma for ~ fsuppssind .  Write a function as a union.  (Contributed by
       SN, 15-Jul-2024.) $)
    fsuppssindlem2 $p |- ( ph -> ( F e.
      { f e. ( B ^m S ) | ( x e. I |-> if ( x e. S , ( f ` x ) , .0. ) ) e. H }
           <-> ( F : S --> B /\ ( F u. ( ( I \ S ) X. { .0. } ) ) e. H ) ) ) $=
      ( cv wcel cfv cmpt wa wceq cif cmap co crab cdif csn cxp cun fveq1 ifeq1d
      mpteq2dv eleq1d elrab cvv ssexd elmapd anbi1d cin partfun sseqin2 mpteq1d
      wss sylib adantr simpr feqmptd eqtr4d fconstmpt eqcomi a1i uneq12d eqtrid
      wf pm5.32da bitrd bitrid ) FBHBOZDPZVQEOZQZKUAZRZGPZECDUBUCZUDPFWDPZBHVRV
      QFQZKUAZRZGPZSZADCFVMZFHDUEZKUFUGZUHZGPZSZWCWIEFWDVSFTZWBWHGWQBHWAWGWQVRV
      TWFKVQVSFUIUJUKULUMAWJWKWISWPAWEWKWIACDFJUNLADHIMNUOUPUQAWKWIWOAWKSZWHWNG
      WRWHBHDURZWFRZBWLKRZUHWNBHDWFKUSWRWTFXAWMWRWTBDWFRZFAWTXBTWKABWSDWFADHVBW
      SDTNDHUTVCVAVDWRBDCFAWKVEVFVGXAWMTWRWMXABWLKVHVIVJVKVLULVNVOVP $.
  $}

  ${
    $d B a b f s $.  $d B t u v $.  $d .0. a b f i s $.  $d .0. t x y $.
    $d .0. j $.  $d .0. u v $.  $d .+ f i t s $.  $d .+ x y $.  $d .+ j $.
    $d .+ u v $.  $d ph a b i s $.  $d ph t x y $.  $d ph j $.  $d ph u v $.
    $d I a b f i $.  $d I s x y $.  $d I j $.  $d I t u v $.  $d S a b f i $.
    $d S t x y $.  $d S j $.  $d S s u v $.  $d H a b f i s $.  $d H t x y $.
    $d H u v $.  $d X i f $.
    fsuppssind.b $e |- B = ( Base ` G ) $.
    fsuppssind.z $e |- .0. = ( 0g ` G ) $.
    fsuppssind.p $e |- .+ = ( +g ` G ) $.
    fsuppssind.g $e |- ( ph -> G e. Grp ) $.
    fsuppssind.v $e |- ( ph -> I e. V ) $.
    fsuppssind.s $e |- ( ph -> S C_ I ) $.
    fsuppssind.0 $e |- ( ph -> ( I X. { .0. } ) e. H ) $.
    fsuppssind.1 $e |- ( ( ph /\ ( a e. S /\ b e. B ) ) ->
                                ( s e. I |-> if ( s = a , b , .0. ) ) e. H ) $.
    fsuppssind.2 $e |- ( ( ph /\ ( x e. H /\ y e. H ) ) ->
                                                        ( x oF .+ y ) e. H ) $.
    fsuppssind.3 $e |- ( ph -> X : I --> B ) $.
    fsuppssind.4 $e |- ( ph -> X finSupp .0. ) $.
    fsuppssind.5 $e |- ( ph -> ( X supp .0. ) C_ S ) $.
    $( Induction on functions ` F : A --> B ` with finite support (see
       ~ fsuppind ) whose supports are subsets of ` S ` .  (Contributed by SN,
       15-Jun-2024.) $)
    fsuppssind $p |- ( ph -> X e. H ) $=
      ( vi vf vt vu vv vj cres cv wcel cfv cif cmpt cmap co crab cfsupp fssresd
      wf wbr cvv c0g fvexi a1i fsuppres jca ssexd csn cxp cdif cun cgrp grpidcl
      syl fconst6g xpundir wss wceq undif xpeq1d eqtr3id eqeltrd fsuppssindlem2
      wa sylib cbs mpbir2and weq simplrr ad2antrr ifcld fmpttd fconstmpt uneq2i
      wn eldifn eleq1a con3dimp adantlr adantll sylan2 iffalsed mpteq2dva mptun
      uneq2d adantr mpteq1d eqtr3d eqtrid anbi12d grpcl syl3an1 simprll simprrl
      cof 3expb off ffnd wfn fnconstg mp1i difexd cin c0 disjdif ofun fvconst2g
      inidm sylan grplid syl2anc sylancom wb eleq1d eqtr4d offveq eqtrd caovclg
      adantrrl adantrll eqeltrrd sylbida fsuppind elmapd mpbird ifeq1d mpteq2dv
      mpdan fveq1 elrab3 fsuppssindlem1 bitr4d mpbid ) AKFUNZUHIUHUOZFUPZUVAUIU
      OZUQZLURZUSZHUPZUIDFUTVAZVBZUPZKHUPZAFDUUTVEZUUTLVCVFZWJUVJAUVLUVMAIDFKUE
      UAVDZAKVGFLUFLVGUPZALGVHQVIZVJZVKVLAMUJDEGUVIFVGUUTLNOPQRSAFIJTUAVMZAFLVN
      ZVOZUVIUPFDUVTVEZUVTIFVPZUVSVOZVQZHUPALDUPZUWAAGVRUPZUWESDGLPQVSVTZFLDWAV
      TAUWDIUVSVOZHAUWDFUWBVQZUVSVOUWHFUWBUVSWBAUWIIUVSAFIWCZUWIIWDZUAFIWEZWKWF
      WGUBWHAUHDFUIUVTHIJVGLDVGUPZADGWLPVIZVJZTUAWIWMANUOZFUPZOUOZDUPZWJZWJZMFM
      NWNZUWRLURZUSZUVIUPFDUXDVEUXDUWCVQZHUPUXAMFUXCDUXAMUOZFUPZWJUXBUWRLDAUWQU
      WSUXGWOAUWEUWTUXGUWGWPWQWRUXAUXEMIUXCUSZHUXAUXEUXDMUWBLUSZVQZUXHUWCUXIUXD
      MUWBLWSWTUXAUXDMUWBUXCUSZVQZUXJUXHUXAUXKUXIUXDUXAMUWBUXCLUXAUXFUWBUPZWJUX
      BUWRLUXMUXAUXGXAZUXBXAZUXFIFXBUWTUXNUXOAUWQUXNUXOUWSUWQUXBUXGUWPFUXFXCXDX
      EXFXGXHXIXKUXAUXLMUWIUXCUSUXHMFUWBUXCXJUXAMUWIIUXCUXAUWJUWKAUWJUWTUAXLZUW
      LWKXMWGXNXOUCWHUXAUHDFUIUXDHIJVGLUWMUXAUWNVJAIJUPUWTTXLUXPWIWMAUXFUVIUPZU
      JUOZUVIUPZWJFDUXFVEZUXFUWCVQZHUPZWJZFDUXRVEZUXRUWCVQZHUPZWJZWJZUXFUXREYAZ
      VAZUVIUPZAUXQUYCUXSUYGAUHDFUIUXFHIJVGLUWOTUAWIAUHDFUIUXRHIJVGLUWOTUAWIXPA
      UYHWJZUYKFDUYJVEZUYJUWCVQZHUPZUYLUKULFFFEDDDUXFUXRVGVGAUKUOZDUPZULUOZDUPZ
      WJUYPUYREVADUPZUYHAUYQUYSUYTAUWFUYQUYSUYTSDEGUYPUYRPRXQXRYBXEAUXTUYBUYGXS
      ZAUYCUYDUYFXTZAFVGUPUYHUVRXLZVUCFYNYCUYLUYAUYEUYIVAZUYNHUYLVUDUYJUWCUWCUY
      IVAZVQZUYNUYLUXFUXRUWCUWCEFUWBVGVGUYLFDUXFVUAYDUYLFDUXRVUBYDUVOUWCUWBYEZU
      YLUVPUWBLVGYFZYGZVUIVUCAUWBVGUPUYHAIFJTYHZXLFUWBYIYJWDUYLFIYKVJYLAVUFUYNW
      DUYHAVUEUWCUYJAUMUWBLLEUWCUWCUWCVGVUJUVOVUGAUVPVUHYGZVUKVUKAUVOUMUOZUWBUP
      ZVULUWCUQZLWDZUVQUWBLVULVGYMZYOZVUQAVUMWJZLLEVAZLVUNAVUSLWDZVUMAUWFUWEVUT
      SUWGDEGLLPRQYPYQXLAVUMUVOVUOUVOVURUVPVJVUPYRUUAUUBXKXLUUCAUYBUYGVUDHUPZUX
      TAUYBUYFVVAUYDABCUYAUYEHHHUYIUDUUDUUEUUFUUGAUYKUYMUYOWJYSUYHAUHDFUIUYJHIJ
      VGLUWOTUAWIXLWMUUHUUIUUNAUVJUHIUVBUVAUUTUQZLURZUSZHUPZUVKAUUTUVHUPZUVJVVE
      YSAVVFUVLUVNADFUUTVGVGUWOUVRUUJUUKUVGVVEUIUUTUVHUVCUUTWDZUVFVVDHVVGUHIUVE
      VVCVVGUVBUVDVVBLUVAUVCUUTUUOUULUUMYTUUPVTAKVVDHAUHDFKIJVGLUVQTUEUGUUQYTUU
      RUUS $.
  $}

  ${
    $d .0. a b s $.  $d .0. s x y $.  $d B a b s $.  $d D a b g s $.
    $d D g s x y $.  $d G a b s $.  $d G s x y $.  $d H a b s $.  $d H s x y $.
    $d I h $.  $d N a b g s $.  $d N g s x y $.  $d P a b s $.  $d P s x y $.
    $d R s x y $.  $d S s $.  $d ph a b s $.  $d ph s x y $.  $d g h $.
    mhpind.h $e |- H = ( I mHomP R ) $.
    mhpind.b $e |- B = ( Base ` R ) $.
    mhpind.z $e |- .0. = ( 0g ` R ) $.
    mhpind.p $e |- P = ( I mPoly R ) $.
    mhpind.a $e |- .+ = ( +g ` P ) $.
    mhpind.d $e |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin } $.
    mhpind.s $e |- S = { g e. D | ( ( CCfld |`s NN0 ) gsum g ) = N } $.
    mhpind.r $e |- ( ph -> R e. Grp ) $.
    mhpind.x $e |- ( ph -> X e. ( H ` N ) ) $.
    mhpind.0 $e |- ( ph -> ( D X. { .0. } ) e. G ) $.
    mhpind.1 $e |- ( ( ph /\ ( a e. S /\ b e. B ) ) ->
                             ( s e. D |-> if ( s = a , b , .0. ) ) e. G ) $.
    mhpind.2 $e |- ( ( ph /\
        ( x e. ( ( H ` N ) i^i G ) /\ y e. ( ( H ` N ) i^i G ) ) ) ->
                                                        ( x .+ y ) e. G ) $.
    $( The homogeneous polynomials of degree ` N ` are generated by the terms
       of degree ` N ` and addition.  (Contributed by SN, 28-Jul-2024.) $)
    mhpind $p |- ( ph -> X e. G ) $=
      ( cfv cplusg ccnfld cn0 cress co cv cgsu wceq crab cin cvv eqid ccnv cima
      cn cfn wcel cmap ovexd rabexd wss ssrab2 a1i csn cxp cmhp reldmmhp mhprcl
      elfvov1 mhp0cl elind weq cif cmpt eleq2i biimpri wa cbs adantr cfsupp wbr
      cmps wf simplrr cgrp grpidcl ad2antrr ifcld fmpttd wb fvexi elmapd mpbird
      syl psrbas eleqtrrd c0g sniffsupp mplelbas sylanbrc csupp cdif wne necomd
      elneeldif adantll adantlrr neneqd iffalsed suppss2 ismhp2 sylanr1 elinel1
      sseqtrdi cof ad2antrl mhpmpl ad2antll mpladd mhpaddcl eqeltrrd fsuppssind
      mplelf mplelsfi mhpdeg elin2d ) AOMUMZLPABCDHUNUMZUOUPUQURJUSUTUROVAZJEVB
      ZHYTLVCZEVDPQRSTUBUCUUAVEZUHAKUSVFVHVGVIVJKUPNVKUREVDUFAUPNVKVLVMZUUCEVNA
      UUBJEVOVPAYTLEQVQVRAEHKMNOVDQUAUCUFAHMNVSPOVTUAUIWBZUHAHMNOPUAUIWAZWCUJWD
      SUSZUUCVJZAUUIIVJZTUSZDVJZRERSWEZUULQWFZWGZUUDVJUUKUUJIUUCUUIUGWHWIAUUKUU
      MWJZWJZYTLUUPUURFWKUMZEFHJKMNOUUPQUAUDUUSVEZUCUFAOUPVJUUQUUHWLUURUUPNHWOU
      RZWKUMZVJUUPQWMWNZUUPUUSVJUURUUPDEVKURZUVBUURUUPUVDVJZEDUUPWPZUURREUUODUU
      RRUSZEVJZWJUUNUULQDAUUKUUMUVHWQAQDVJZUUQUVHAHWRVJZUVIUHDHQUBUCWSXGWTXAXBA
      UVEUVFXCUUQADEUUPVDVDDVDVJADHWKUBXDVPUUFXEWLXFAUVBUVDVAUUQAUVBEHUVAKNDVDU
      VAVEZUBUFUVBVEZUUGXHWLXIAUVCUUQARUULUUPEVDVDUUIQUUFQVDVJAQHXJUCXDVPUUPVEX
      KWLUVBFHUVAUUSNUUPQUDUVKUVLUCUUTXLXMUURUUPQXNURIUUCUUREUUORVDIQUURUVGEIXO
      VJZWJZUUNUULQUVNUVGUUIAUUKUVMUVGUUIXPZUUMUUKUVMUVOAUUKUVMWJUUIUVGIEUUIUVG
      XRXQXSXTYAYBAEVDVJUUQUUFWLYCUGYGYDUKWDYEABUSZUUDVJZCUSZUUDVJZWJZWJZUVPUVR
      GURZUVPUVRUUAYHURUUDUWAUUSFUUAGHNUVPUVRUDUUTUUEUEUWAUUSFHMNOUVPUAUDUUTUVQ
      UVPYTVJAUVSUVPYTLYFYIZYJUWAUUSFHMNOUVRUAUDUUTUVSUVRYTVJAUVQUVRYTLYFYKZYJY
      LUWAYTLUWBUWAFGHMNOUVPUVRUAUDUEAUVJUVTUHWLUWCUWDYMULWDYNAUUSEFHKNDPUDUBUU
      TUFAUUSFHMNOPUAUDUUTUIYJZYPAUUSFHPNQUDUUTUCUWEYQAEHJKMNOPQUAUCUFUIYRYOYS
      $.
  $}

  ${
    $d A b i $.  $d D b i $.  $d D g $.  $d F b $.  $d G b $.  $d I b h $.
    $d I i $.  $d K b i $.  $d N g $.  $d R b $.  $d S b i $.  $d U b h $.
    $d U i $.  $d ph b i $.  $d g h $.
    evlsmhpvvval.q $e |- Q = ( ( I evalSub S ) ` R ) $.
    evlsmhpvvval.p $e |- H = ( I mHomP U ) $.
    evlsmhpvvval.u $e |- U = ( S |`s R ) $.
    evlsmhpvvval.d $e |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin } $.
    evlsmhpvvval.g $e |- G = { g e. D | ( ( CCfld |`s NN0 ) gsum g ) = N } $.
    evlsmhpvvval.k $e |- K = ( Base ` S ) $.
    evlsmhpvvval.m $e |- M = ( mulGrp ` S ) $.
    evlsmhpvvval.w $e |- .^ = ( .g ` M ) $.
    evlsmhpvvval.x $e |- .x. = ( .r ` S ) $.
    evlsmhpvvval.s $e |- ( ph -> S e. CRing ) $.
    evlsmhpvvval.r $e |- ( ph -> R e. ( SubRing ` S ) ) $.
    evlsmhpvvval.f $e |- ( ph -> F e. ( H ` N ) ) $.
    evlsmhpvvval.a $e |- ( ph -> A e. ( K ^m I ) ) $.
    $( Give a formula for the evaluation of a homogeneous polynomial given
       assignments from variables to values.  The difference between this and
       ~ evlsvvval is that ` b e. D ` is restricted to ` b e. G ` , that is, we
       can evaluate an ` N ` -th degree homogeneous polynomial over just the
       terms where the sum of all variable degrees is ` N ` .  (Contributed by
       SN, 5-Mar-2025.) $)
    evlsmhpvvval $p |- ( ph -> ( ( Q ` F ) ` A ) = ( S gsum ( b e. G |->
      ( ( F ` b ) .x.
                ( M gsum ( i e. I |-> ( ( b ` i ) .^ ( A ` i ) ) ) ) ) ) ) ) $=
      ( cfv cv co cmpt cgsu cres cmpl cbs cvv eqid cmhp reldmmhp elfvov1 mhpmpl
      evlsvvval c0g crngringd ringcmnd wcel ccnv cn cima cfn cn0 cmap rabex2 wa
      a1i crg adantr mplelf csubrg wss subrgbas subrgss eqsstrrd syl ffvelcdmda
      ovex fssd ccrg simpr evlsvvvallem ringcld fmpttd cdif csupp subrg0 oveq2d
      wceq ccnfld cress crab mhpdeg eqsstrd fvexd suppssr oveq1d eldifi ringlzd
      sseqtrrdi sylan2 suppss2 evlsvvvallem2 gsumres ssrab3 resmptd 3eqtr2d
      eqtrd ) ABMDUNUNFTCTUOZMUNZRKPKUOZYCUNYEBUNLUPUQURUPZGUPZUQZURUPFYHNUSZUR
      UPFTNYGUQZURUPABPHUTUPZVAUNZCYKDEFGHJKLMPQRVBTUAYKVCZYLVCZUCUDUFUGUHUIAHO
      PVDMSVEUBULVFZUJUKAYLYKHOPSMUBYMYNULVGZUMVHACQYHFVBNFVIUNZUFYQVCZAFAFUJVJ
      ZVKCVBVLAJUOVMVNVOVPVLJVQPVRUPCUDVQPVRWLVSWAZATCYGQAYCCVLZVTZQFGYDYFUFUIA
      FWBVLZUUAYSWCACQYCMACHVAUNZQMAYLCYKHJPUUDMYMUUDVCYNUDYPWDAEFWEUNVLZUUDQWF
      UKUUEUUDEQEFHUCWGEQFUFWHWIWJWMZWKUUBKBYCCFJLPQRVBUDUFUGUHAPVBVLUUAYOWCAFW
      NVLUUAUJWCABQPVRUPVLUUAUMWCAUUAWOWPZWQWRACYGTVBNYQAYCCNWSVLZVTZYGYQYFGUPY
      QUUIYDYQYFGACQVBMVBNYCYQUUFAMYQWTUPMHVIUNZWTUPZNAYQUUJMWTAUUEYQUUJXCUKEFH
      YQUCYRXAWJXBAUUKXDVQXEUPIUOURUPSXCZICXFNACHIJOPSMUUJUBUUJVCUDULXGUEXNXHYT
      AFVIXIXJXKUUIQFGYFYQUFUIYRAUUCUUHYSWCUUHAUUAYFQVLYCCNXLUUGXOXMYBYTXPAKBYL
      CYKEFGHJLMPQRVBTUDYMUCYNUFUGUHUIYOUJUKYPUMXQXRAYIYJFURATCNYGNCWFAUULICNUE
      XSWAXTXBYA $.
  $}

  ${
    $d .x. n v x y $.  $d B n $.  $d D g $.  $d G n x y $.  $d H n v x y $.
    $d I h $.  $d I n v $.  $d L n v x y $.  $d N g $.  $d a g $.  $d a h $.
    $d a n v x y $.  $d ph n v x y $.
    mhphflem.d $e |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin } $.
    mhphflem.h $e |- H = { g e. D | ( ( CCfld |`s NN0 ) gsum g ) = N } $.
    mhphflem.k $e |- B = ( Base ` G ) $.
    mhphflem.e $e |- .x. = ( .g ` G ) $.
    mhphflem.i $e |- ( ph -> I e. V ) $.
    mhphflem.g $e |- ( ph -> G e. Mnd ) $.
    mhphflem.l $e |- ( ph -> L e. B ) $.
    mhphflem.n $e |- ( ph -> N e. NN0 ) $.
    $( Lemma for ~ mhphf .  Add several multiples of ` L ` together, in a case
       where the total amount of multiplies is ` N ` .  (Contributed by SN,
       30-Jul-2024.) $)
    mhphflem $p |- ( ( ph /\ a e. H ) ->
              ( G gsum ( v e. I |-> ( ( a ` v ) .x. L ) ) ) = ( N .x. L ) ) $=
      ( vn vx vy cv wcel wa cfv cmpt cgsu ccnfld cn0 cress cc0 csubmnd cbs wceq
      co nn0subm eqid submbas ax-mp c0g cnfld0 subm0 crg cnring ringcmn submcmn
      ccmn mp2an a1i cmnd adantr caddc cnfldadd ressplusg submmnd mp1i ad2antrr
      cplusg simpr mulgnn0cld fmpttd simprl simprr mulgnn0dir syl13anc nn0addcl
      cvv oveq1 adantl ovexd fvmptd3 oveq12d 3eqtr4d 0nn0 mulg0 eqtrd ismhmd wf
      crab elrabi eleq2s psrbagf ffvelcdmda cfsupp feqmptd psrbagfsupp eqbrtrrd
      syl wbr gsummhm2 oveq2d weq oveq2 eqeq1d elrab2 simprbi eqtr3d oveq1d ) A
      NUFZIUGZUHZHBJBUFZYCUIZKEUSZUJUKUSULUMUNUSZBJYGUJZUKUSZKEUSZLKEUSYEUCJUMU
      CUFZKEUSZYHBYLYIHMYGUOUMULUPUIZUGZUMYIUQUIURUTUMYIULYIVAZVBVCZYPUOYIVDUIU
      RUTUMYIULUOYQVEVFVCZYIVKUGZYEULVKUGZYPYTULVGUGUUAVHULVIVCUTUMULYIYQVJVLVM
      AHVNUGZYDTVOZAJMUGYDSVOYEUDUEUMCVPHWBUIZYIHUCUMYNUJZUOHVDUIZYRQYPVPYIWBUI
      URUTUMVPULYIYOYQVQVRVCUUDVAZYSUUFVAZYPYIVNUGYEUTUMYIULYQVSVTUUCYEUCUMYNCY
      EYMUMUGZUHCEHYMKQRAUUBYDUUITWAYEUUIWCAKCUGZYDUUIUAWAWDWEYEUDUFZUMUGZUEUFZ
      UMUGZUHZUHZUUKUUMVPUSZKEUSZUUKKEUSZUUMKEUSZUUDUSZUUQUUEUIUUKUUEUIZUUMUUEU
      IZUUDUSUUPUUBUULUUNUUJUURUVAURAUUBYDUUOTWAYEUULUUNWFZYEUULUUNWGZAUUJYDUUO
      UAWACUUDEHUUKUUMKQRUUGWHWIUUPUCUUQYNUURUMUUEWKUUEVAZYMUUQKEWLUUOUUQUMUGYE
      UUKUUMWJWMUUPUUQKEWNWOUUPUVBUUSUVCUUTUUDUUPUCUUKYNUUSUMUUEWKUVFYMUUKKEWLU
      VDUUPUUKKEWNWOUUPUCUUMYNUUTUMUUEWKUVFYMUUMKEWLUVEUUPUUMKEWNWOWPWQYEUOUUEU
      IUOKEUSZUUFYEUCUOYNUVGUMUUEWKUVFYMUOKEWLUOUMUGYEWRVMYEUOKEWNWOYEUUJUVGUUF
      URAUUJYDUAVOCEHKUUFQUUHRWSXLWTXAYEJUMYFYCYEYCDUGZJUMYCXBYDUVHAUVHYCYIFUFZ
      UKUSZLURZFDXCIUVKFYCDXDPXEWMZDGYCJOXFXLZXGYEYCYJUOXHYEBJUMYCUVMXIZYEUVHYC
      UOXHXMUVLDGYCJOXJXLXKYMYGKEWLYMYKKEWLXNYEYKLKEYEYIYCUKUSZYKLYEYCYJYIUKUVN
      XOYDUVOLURZAYDUVHUVPUVKUVPFYCDIFNXPUVJUVOLUVIYCYIUKXQXRPXSXTWMYAYBWT $.
  $}

  ${
    $d .^ b i k $.  $d .x. b i j k $.  $d A b i k $.  $d I b g h i k $.
    $d I j k $.  $d K b i j k $.  $d L b i j k $.  $d N b g i k $.  $d R b $.
    $d S b i k $.  $d U b h i $.  $d X b $.  $d ph b i j k $.
    mhphf.q $e |- Q = ( ( I evalSub S ) ` R ) $.
    mhphf.h $e |- H = ( I mHomP U ) $.
    mhphf.u $e |- U = ( S |`s R ) $.
    mhphf.k $e |- K = ( Base ` S ) $.
    mhphf.m $e |- .x. = ( .r ` S ) $.
    mhphf.e $e |- .^ = ( .g ` ( mulGrp ` S ) ) $.
    mhphf.s $e |- ( ph -> S e. CRing ) $.
    mhphf.r $e |- ( ph -> R e. ( SubRing ` S ) ) $.
    mhphf.l $e |- ( ph -> L e. R ) $.
    mhphf.x $e |- ( ph -> X e. ( H ` N ) ) $.
    mhphf.a $e |- ( ph -> A e. ( K ^m I ) ) $.
    $( A homogeneous polynomial defines a homogeneous function.  Equivalently,
       an algebraic form is a homogeneous function.  (An algebraic form is the
       function corresponding to a homogeneous polynomial, which in this case
       is the ` ( Q `` X ) ` which corresponds to ` X ` ).  (Contributed by SN,
       28-Jul-2024.)  (Proof shortened by SN, 8-Mar-2025.) $)
    mhphf $p |- ( ph -> ( ( Q ` X ) ` ( ( I X. { L } ) oF .x. A ) ) =
                        ( ( N .^ L ) .x. ( ( Q ` X ) ` A ) ) ) $=
      ( vb vg vh vi vk vj ccnfld cn0 cress co cgsu wceq ccnv cima cfn wcel cmap
      cv cn crab cfv cmgp csn cxp cof cmpt wa cvv wf elmapi ffnd fndmexd adantr
      syl wfn ofc1 oveq2d ccmn ccrg eqid crngmgp ad2antrr elrabi psrbagf adantl
      eqidd ffvelcdmda csubrg subrgss sseldd mgpbas mgpplusg mulgnn0di syl13anc
      wss eqtrd mpteq2dva cur ringidval crg crngringd ringmgp mulgnn0cld mptexd
      cmnd cc0 fvexd wfun funmpt a1i cfsupp psrbagfsupp csupp cz feqmptd oveq1d
      wbr eqimsscd mulg0 0zd suppssov1 fsuppsssuppgd gsummptfsadd mhprcl 3eqtrd
      mhphflem cmpl mhpmpl mplelf subrgbas eqsstrrd sylan2 rabex evlsmhpvvval
      cbs fssd simpr evlsvvvallem crng12d c0g ovex ringcld ssrab2 evlsvvvallem2
      mptss fsuppss gsummulc2 fvexi ringcl syl3an1 3expb fconst6g inidm elmapdd
      mp1i off 3eqtr4d ) AEUFULUMUNUOUGVCUPUOMUQZUGUHVCURVDUSUTVAZUHUMJVBUOZVEZ
      VEZUFVCZNVFZEVGVFZUIJUIVCZUVHVFZUVKJLVHVIZBFVJUOZVFZHUOZVKZUPUOZFUOZVKZUP
      UOZMLHUOZEUFUVGUVIUVJUIJUVLUVKBVFZHUOZVKZUPUOZFUOZVKZUPUOZFUOZUVNNCVFZVFU
      WBBUWKVFZFUOAUWAEUFUVGUWBUWGFUOZVKZUPUOUWJAUVTUWNEUPAUFUVGUVSUWMAUVHUVGVA
      ZVLZUVSUVIUWBUWFFUOZFUOUWMUWPUVRUWQUVIFUWPUVRUVJUIJUVLLHUOZUWDFUOZVKZUPUO
      UVJUIJUWRVKZUPUOZUWFFUOUWQUWPUVQUWTUVJUPUWPUIJUVPUWSUWPUVKJVAZVLZUVPUVLLU
      WCFUOZHUOZUWSUXDUVOUXEUVLHUWPJLUWCFBVMDUVKAJVMVAZUWOAJBKJVBUOZUEAJKBABUXH
      VAZJKBVNZUEBKJVOVSZVPZVQZVRZALDVAUWOUCVRABJVTUWOUXLVRUXDUWCWKWAWBUXDUVJWC
      VAZUVLUMVALKVAZUWCKVAUXFUWSUQAUXOUWOUXCAEWDVAZUXOUAEUVJUVJWEZWFZVSWGUWPJU
      MUVKUVHUWOJUMUVHVNZAUWOUVHUVFVAZUXTUVCUGUVHUVFWHZUVFUHUVHJUVFWEZWIVSWJZWL
      ZAUXPUWOUXCADKLADEWMVFVAZDKWTUBDKERWNZVSUCWOZWGZUWPJKUVKBAUXJUWOUXKVRWLZK
      FHUVJUVLLUWCKEUVJUXRRWPZTEFUVJUXRSWQZWRWSXAXBWBUWPUIJKUWRUWDFUXAUVJUWEVME
      XCVFZUYKEUYMUVJUXRUYMWEXDZUYLUWPUXQUXOAUXQUWOUAVRZUXSVSUXNUXDKHUVJUVLLUYK
      TAUVJXJVAZUWOUXCAEXEVAZUYPAEUAXFZEUVJUXRXGVSZWGZUYEUYIXHUXDKHUVJUVLUWCUYK
      TUYTUYEUYJXHUWPUXAWKUWPUWEWKUWPUVHUXAXKVMVMUYMAUXAVMVAUWOAUIJUWRVMUXMXIVR
      UWPEXCXLZUXAXMUWPUIJUWRXNXOUWOUVHXKXPYBZAUWOUYAVUBUYBUVFUHUVHJUYCXQVSWJZU
      WPUIUJUVLLJKUVHXKXRUOZHUMXSXKUYMUWPVUDUIJUVLVKZXKXRUOUWPUVHVUEXKXRUWPUIJU
      MUVHUYDXTYAYCZUJVCZKVAZXKVUGHUOUYMUQUWPKHUVJVUGUYMUYKUYNTYDWJZUYEUYIUWPYE
      ZYFYGUWPUVHUWEXKVMVMUYMAUWEVMVAUWOAUIJUWDVMUXMXIVRVUAUWEXMUWPUIJUWDXNXOVU
      CUWPUIUJUVLUWCJKVUDHUMXSXKUYMVUFVUIUYEUYJVUJYFYGYHUWPUXBUWBUWFFAUIKUVFHUG
      UHUVJUVGJLMVMUFUYCUVGWEZUYKTUXMUYSUYHAGIJMNPUDYIZYKYAYJWBUWPKEFUVIUWBUWFR
      SUYOUWOAUYAUVIKVAUYBAUVFKUVHNAUVFGYTVFZKNAJGYLUOZYTVFZUVFVUNGUHJVUMNVUNWE
      ZVUMWEVUOWEZUYCAVUOVUNGIJMNPVUPVUQUDYMZYNAUYFVUMKWTUBUYFVUMDKDEGQYOUYGYPV
      SUUAWLZYQAUWBKVAUWOAKHUVJMLUYKTUYSVULUYHXHZVRUWOAUYAUWFKVAUYBAUYAVLZUIBUV
      HUVFEUHHJKUVJVMUYCRUXRTAUXGUYAUXMVRAUXQUYAUAVRAUXIUYAUEVRAUYAUUBUUCZYQUUD
      XAXBWBAUVGKEFUFVMUWGUWBEUUEVFZRVVCWESUYRUVGVMVAAUVCUGUVFUVDUHUVEUMJVBUUFY
      RYRXOVUTUWOAUYAUWGKVAUYBVVAKEFUVIUWFRSAUYQUYAUYRVRVUSVVBUUGYQAUWHUFUVFUWG
      VKZVVCUVGUVFWTUWHVVDWTAUVCUGUVFUUHUFUVGUVFUWGUUJUUTAUIBVUOUVFVUNDEFGUHHNJ
      KUVJVMUFUYCVUPQVUQRUXRTSUXMUAUBVURUEUUIUUKUULXAAUVNUVFCDEFGUGUHUIHNUVGIJK
      UVJMUFOPQUYCVUKRUXRTSUAUBUDAKJUVNVMVMKVMVAAKEYTRUUMXOUXMAUKUJJJJFKKKUVMBV
      MVMAUKVCZKVAZVUHVVEVUGFUOKVAZAUYQVVFVUHVVGUYRKEFVVEVUGRSUUNUUOUUPAUXPJKUV
      MVNUYHJLKUUQVSUXKUXMUXMJUURUVAUUSYSAUWLUWIUWBFABUVFCDEFGUGUHUIHNUVGIJKUVJ
      MUFOPQUYCVUKRUXRTSUAUBUDUEYSWBUVB $.
  $}

  ${
    mhphf2.q $e |- Q = ( ( I evalSub S ) ` R ) $.
    mhphf2.h $e |- H = ( I mHomP U ) $.
    mhphf2.u $e |- U = ( S |`s R ) $.
    mhphf2.k $e |- K = ( Base ` S ) $.
    mhphf2.b $e |- .xb = ( .s ` ( ( ringLMod ` S ) ^s I ) ) $.
    mhphf2.m $e |- .x. = ( .r ` S ) $.
    mhphf2.e $e |- .^ = ( .g ` ( mulGrp ` S ) ) $.
    mhphf2.s $e |- ( ph -> S e. CRing ) $.
    mhphf2.r $e |- ( ph -> R e. ( SubRing ` S ) ) $.
    mhphf2.l $e |- ( ph -> L e. R ) $.
    mhphf2.x $e |- ( ph -> X e. ( H ` N ) ) $.
    mhphf2.a $e |- ( ph -> A e. ( K ^m I ) ) $.
    $( A homogeneous polynomial defines a homogeneous function; this is ~ mhphf
       with simpler notation in the conclusion in exchange for a complex
       definition of ` .xb ` , which is based on ~ frlmvscafval but without the
       finite support restriction ( ~ frlmpws , ~ frlmbas ) on the assignments
       ` A ` from variables to values.

       TODO?:  Polynomials ( ~ df-mpl ) are defined to have a finite amount of
       terms (of finite degree).  As such, any assignment may be replaced by an
       assignment with finite support (as only a finite amount of variables
       matter in a given polynomial, even if the set of variables is infinite).
       So the finite support restriction can be assumed without loss of
       generality.  (Contributed by SN, 11-Nov-2024.) $)
    mhphf2 $p |- ( ph -> ( ( Q ` X ) ` ( L .xb A ) ) =
                         ( ( N .^ L ) .x. ( ( Q ` X ) ` A ) ) ) $=
      ( cfv csn cxp cof cmulr crglmod cpws cbs csca cvv eqid rlmvsca fvexd cmhp
      co reldmmhp elfvov1 csubrg wcel wss subrgss syl sseldd ccrg rlmsca fveq2d
      wceq eqtrid eleqtrd cmap oveq1i eleqtrdi rlmbas pwsbas pwsvscafval eqcomi
      syl2anc ofeq mp1i oveqd eqtrd mhphf ) AMBFVBZOCUHZUHKMUIUJZBGUKZVBZWKUHNM
      IVBBWKUHGVBAWJWNWKAWJWLBEULUHZUKZVBWNAMEUMUHZKUNVBZUOUHZWQFWOWQUPUHZKWTUO
      UHZUQUQBWRWRURZWSUREUSTWTURXAURAEUMUTZAHJKVAONVCQUFVDZAMLXAADLMADEVEUHVFD
      LVGUDDLESVHVIUEVJALEUOUHZXASAEWTUOAEVKVFEWTVNUCEVKVLVIVMVOVPABXEKVQVBZWSA
      BLKVQVBXFUGLXEKVQSVRVSAWQUQVFKUQVFXFWSVNXCXDXEWQKUQUQWRXBEVTWAWDVPWBAWPWM
      WLBWOGVNWPWMVNAGWOUAWCWOGWEWFWGWHVMABCDEGHIJKLMNOPQRSUAUBUCUDUEUFUGWIWH
      $.
  $}

  ${
    mhphf3.q $e |- Q = ( ( I evalSub S ) ` R ) $.
    mhphf3.h $e |- H = ( I mHomP U ) $.
    mhphf3.u $e |- U = ( S |`s R ) $.
    mhphf3.k $e |- K = ( Base ` S ) $.
    mhphf3.f $e |- F = ( S freeLMod I ) $.
    mhphf3.m $e |- M = ( Base ` F ) $.
    mhphf3.b $e |- .xb = ( .s ` F ) $.
    mhphf3.x $e |- .x. = ( .r ` S ) $.
    mhphf3.e $e |- .^ = ( .g ` ( mulGrp ` S ) ) $.
    mhphf3.s $e |- ( ph -> S e. CRing ) $.
    mhphf3.r $e |- ( ph -> R e. ( SubRing ` S ) ) $.
    mhphf3.l $e |- ( ph -> L e. R ) $.
    mhphf3.p $e |- ( ph -> X e. ( H ` N ) ) $.
    mhphf3.a $e |- ( ph -> A e. M ) $.
    $( A homogeneous polynomial defines a homogeneous function; this is
       ~ mhphf2 with the finite support restriction ( ~ frlmpws , ~ frlmbas )
       on the assignments ` A ` from variables to values.  See comment of
       ~ mhphf2 .  (Contributed by SN, 23-Nov-2024.) $)
    mhphf3 $p |- ( ph -> ( ( Q ` X ) ` ( L .xb A ) ) =
                         ( ( N .^ L ) .x. ( ( Q ` X ) ` A ) ) ) $=
      ( co cfv csn cxp cof cvv cmhp reldmmhp elfvov1 csubrg wcel subrgss sseldd
      wss syl frlmvscafval fveq2d cmap frlmbasmap syl2anc mhphf eqtrd ) ANBFULZ
      QCUMZUMLNUNUOBGUPULZVOUMPNIULBVOUMGULAVNVPVOANOEFGLMUQBJUBUCUAAHKLURQPUSS
      UJUTZADMNADEVAUMVBDMVEUHDMEUAVCVFUIVDUKUDUEVGVHABCDEGHIKLMNPQRSTUAUEUFUGU
      HUIUJALUQVBBOVBBMLVIULVBVQUKOEJLMUQBUBUAUCVJVKVLVM $.
  $}

  ${
    mhphf4.q $e |- Q = ( I eval S ) $.
    mhphf4.h $e |- H = ( I mHomP S ) $.
    mhphf4.k $e |- K = ( Base ` S ) $.
    mhphf4.f $e |- F = ( S freeLMod I ) $.
    mhphf4.m $e |- M = ( Base ` F ) $.
    mhphf4.b $e |- .xb = ( .s ` F ) $.
    mhphf4.x $e |- .x. = ( .r ` S ) $.
    mhphf4.e $e |- .^ = ( .g ` ( mulGrp ` S ) ) $.
    mhphf4.s $e |- ( ph -> S e. CRing ) $.
    mhphf4.l $e |- ( ph -> L e. K ) $.
    mhphf4.p $e |- ( ph -> X e. ( H ` N ) ) $.
    mhphf4.a $e |- ( ph -> A e. M ) $.
    $( A homogeneous polynomial defines a homogeneous function; this is
       ~ mhphf3 with ` evalSub ` collapsed to ` eval ` .  (Contributed by SN,
       23-Nov-2024.) $)
    mhphf4 $p |- ( ph -> ( ( Q ` X ) ` ( L .xb A ) ) =
                         ( ( N .^ L ) .x. ( ( Q ` X ) ` A ) ) ) $=
      ( co cmhp evlval eqid crg wcel csubrg cfv crngringd subrgid syl ccrg wceq
      cress ressid eqcomd oveq2d eqtrid fveq1d eleqtrd mhphf3 ) ABCKDEFDKVAUHZG
      HJVIUIUHZJKLMNOKCDJPRUJVJUKVIUKRSTUAUBUCUDADULUMKDUNUOUMADUDUPKDRUQURUEAO
      NIUONVJUOUFANIVJAIJDUIUHVJQADVIJUIAVIDADUSUMVIDUTUDKDUSRVBURVCVDVEVFVGUGV
      H $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Projective spaces
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Looking at a corner in 3D space, one can see three right angles.  It is
  impossible to draw three lines in 2D space such that any two of these lines
  are perpendicular, but a good enough representation is made by casting lines
  from the 2D surface.  Points along the same cast line are collapsed into one
  point on the 2D surface.

  In many cases, the 2D surface is smaller than whatever needs to be
  represented.  If the lines cast were perpendicular to the 2D surface, then
  only areas as small as the 2D surface could be represented.  To fix this,
  the lines need to get further apart as they go farther from the 2D surface.
  On the other side of the 2D surface the lines will get closer together and
  intersect at a point (because it's defined that way).

  From this perspective, two parallel lines in 3D space will be represented by
  two lines that seem to intersect at a point "at infinity".  Considering all
  maximal classes of parallel lines on a 2D plane in 3D space, these classes
  will all appear to intersect at different points at infinity, forming a
  _line at infinity_.  Therefore the _real projective plane_ can be thought of
  as the real _affine_ plane together with the line at infinity.

  The projective plane takes care of some exceptions that may be found in the
  affine plane.  For example, consider the curve that is the zeroes of
  ` y = x ^ 2 ` .  Any line connecting the point (0, 1) to the x-axis
  intersects with the curve twice, except for the vertical line between (0, 1)
  and (0, 0).  In the projective plane, the curve becomes an ellipse and there
  is no exception.

  While it may not seem like it, points at infinity and points corresponding to
  the affine plane are the same type of point.  Consider a line going through
  the origin in 3D (affine) space.  Either it intersects the plane ` z = 1 `
  once, or it is entirely within the plane ` z = 0 ` .  If it is entirely
  within the plane ` z = 0 ` , then it corresponds to the point at infinity
  intersecting all lines on the plane ` z = 1 ` with the same slope.  Else it
  corresponds to the point in the 2D plane ` z = 1 ` that it intersects.  So
  there is a bijection between 3D lines through the origin and points on the
  real projective plane.

  The concept of projective spaces generalizes the projective plane to any
  dimension.

$)

  $c PrjSp $.

  $( Extend class notation with the projective space function. $)
  cprjsp $a class PrjSp $.

  ${
    $d v b x y l $.
    $( Define the projective space function.  In the bijection between 3D lines
       through the origin and points in the projective plane (see section
       comment), this is equivalent to making any two 3D points (excluding the
       origin) equivalent iff one is a multiple of another.  This definition
       does not quite give all the properties needed, since the scalars of a
       left vector space can be "less dense" than the vectors (for example,
       making equivalent rational multiples of real numbers).  Compare
       ~ df-lsatoms .  (Contributed by BJ and SN, 29-Apr-2023.) $)
    df-prjsp $a |- PrjSp = ( v e. LVec |->
      [_ ( ( Base ` v ) \ { ( 0g ` v ) } ) / b ]_ (
        b /. { <. x , y >. | ( ( x e. b /\ y e. b ) /\
        E. l e. ( Base ` ( Scalar ` v ) ) x = ( l ( .s ` v ) y ) ) } ) ) $.
  $}

  ${
    $d b l v x y V $.  $d b v B $.  $d b v .x. $.  $d b v K $.
    prjspval.b $e |- B = ( ( Base ` V ) \ { ( 0g ` V ) } ) $.
    prjspval.x $e |- .x. = ( .s ` V ) $.
    prjspval.s $e |- S = ( Scalar ` V ) $.
    prjspval.k $e |- K = ( Base ` S ) $.
    $( Value of the projective space function, which is also known as the
       projectivization of ` V ` .  (Contributed by Steven Nguyen,
       29-Apr-2023.) $)
    prjspval $p |- ( V e. LVec -> ( PrjSp ` V ) = ( B /.
      { <. x , y >. | ( ( x e. B /\ y e. B ) /\ E. l e. K x = ( l .x. y ) ) }
      ) ) $=
      ( vb cv cbs cfv wa wceq fveq2 eqtr4di vv c0g csn cdif wel cvsca csca wrex
      copab cqs csb wcel clvec cprjsp cvv fvex difexi a1i sneqd difeq12d eqeq2d
      co biimpd imp wb imdistani eleq2 anbi12d fveq2d oveqd rexeqbidv bi2anan9r
      syl opabbidv qseq12d csbied df-prjsp eqeltri qsex fvmpt ) UAGMUANZOPZWAUB
      PZUCZUDZMNZAMUEZBMUEZQZANZHNZBNZWAUFPZVBZRZHWAUGPZOPZUHZQZABUIZUJZUKCWJCU
      LZWLCULZQZWJWKWLEVBZRZHFUHZQZABUIZUJZUMUNWAGRZMWEXAXJUOWEUOULXKWBWDWAOUPU
      QURXKWFWERZQZWFCWTXIXKXLWFCRZXKXLXNXKWECWFXKWEGOPZGUBPZUCZUDZCXKWBXOWDXQW
      AGOSXKWCXPWAGUBSUSUTITVAVCZVDXMWSXHABXMXKXNQWSXHVEXKXLXNXSVFXNWIXDXKWRXGX
      NWGXBWHXCWFCWJVGWFCWLVGVHXKWOXFHWQFXKWQDOPFXKWPDOXKWPGUGPDWAGUGSKTVILTXKW
      NXEWJXKWMEWKWLXKWMGUFPEWAGUFSJTVJVAVKVLVMVNVOVPABUAMHVQCXICXRUOIXOXQGOUPU
      QVRVSVT $.
  $}

  ${
    $d B x y $.  $d X x y l m $.  $d Y x y l m $.  $d K x y l m $.
    $d .x. x y l m $.
    prjsprel.1 $e |- .~ = { <. x , y >. |
      ( ( x e. B /\ y e. B ) /\ E. l e. K x = ( l .x. y ) ) } $.
    $( Utility theorem regarding the relation used in ` PrjSp ` .  (Contributed
       by Steven Nguyen, 29-Apr-2023.) $)
    prjsprel $p |- ( X .~ Y <->
      ( ( X e. B /\ Y e. B ) /\ E. m e. K X = ( m .x. Y ) ) ) $=
      ( cv co wceq wrex wa weq simpll simpr simplr oveq12d eqeq12d cbvrexdva
      brab2a ) ALZJLZBLZEMZNZJGOHFLZIEMZNZFGOABHICCDUEHNZUGINZPZUIULJFGUOJFQZPZ
      UEHUHUKUMUNUPRUQUFUJUGIEUOUPSUMUNUPTUAUBUCKUD $.

    $d Z l m n o x y $.  $d V m n o $.  $d X n o $.  $d Y n o $.  $d K n o $.
    $d .x. n o $.  $d S o $.  $d .~ m n o $.
    prjspertr.b $e |- B = ( ( Base ` V ) \ { ( 0g ` V ) } ) $.
    prjspertr.s $e |- S = ( Scalar ` V ) $.
    prjspertr.x $e |- .x. = ( .s ` V ) $.
    prjspertr.k $e |- K = ( Base ` S ) $.
    $( The relation in ` PrjSp ` is transitive.  (Contributed by Steven Nguyen,
       1-May-2023.) $)
    prjspertr $p |- ( ( V e. LMod /\ ( X .~ Y /\ Y .~ Z ) ) -> X .~ Z ) $=
      ( wcel wa co vm vn vo clmod wbr cv wceq prjsprel simprbi ad2antrl simplrr
      wrex syl simplrl anassrs simpll sylbi adantr simplr cmulr cfv eqeq2d eqid
      oveq1 crg lmodring ad3antrrr simprl ringcld simprr oveq2d cbs simplll c0g
      csn cdif eldifi lmodvsass syl13anc 3eqtr4d rspcedvdw syl21anbrc rexlimddv
      eleq2s ) HUDRZIJDUEZJKDUEZSZSZIUAUFZJFTZUGZIKDUEZUAGWFWLUAGULZWEWGWFICRZJ
      CRZSZWNABCDFUAGIJLMUHZUIUJWIWJGRZWLSZSZJUBUFZKFTZUGZWMUBGXAWGXDUBGULZWEWF
      WGWTUKZWGWPKCRZSZXEABCDFUBGJKLMUHZUIUMXAXBGRZXDSZSZWOXGIUCUFZKFTZUGZUCGUL
      WMXLWFWOWIWTXKWFWEWFWGWTXKSUNUOWFWQWNSWOWRWOWPWNUPUQUMXLWGXGXAWGXKXFURWGX
      HXESXGXIWPXGXEUSUQUMZXLXOIWJXBEUTVAZTZKFTZUGUCXRGXMXRUGXNXSIXMXRKFVDVBXLG
      EXQWJXBQXQVCZWEEVERWHWTXKEHOVFVGWIWSWLXKUNZXAXJXDVHZVIXLWKWJXCFTZIXSXLJXC
      WJFXAXJXDVJVKWIWSWLXKUKXLWEWSXJKHVLVAZRZXSYCUGWEWHWTXKVMYAYBXLXGYEXPYEKYD
      HVNVAVOZVPCKYDYFVQNWDUMWJXBFXQEGYDHKYDVCOPQXTVRVSVTWAABCDFUCGIKLMUHWBWCWC
      $.

    $d B m $.  $d S m $.
    $( The relation in ` PrjSp ` is reflexive.  (Contributed by Steven Nguyen,
       30-Apr-2023.) $)
    prjsperref $p |- ( V e. LMod -> ( X e. B <-> X .~ X ) ) $=
      ( vm wcel wceq wa cfv clmod cv co wrex wbr cur eqeq2d eqid lmod1cl adantr
      cbs c0g csn cdif eldifi eleq2s lmodvs1 sylan2 eqcomd rspcedvdw ex pm4.71d
      oveq1 pm4.24 anbi1i prjsprel bitr4i bitrdi ) HUAQZICQZVJIPUBZIFUCZRZPGUDZ
      SZIIDUEZVIVJVNVIVJVNVIVJSZVMIEUFTZIFUCZRPVRGVKVRRVLVSIVKVRIFVCUGVIVRGQVJV
      REGHMOVRUHZUIUJVQVSIVJVIIHUKTZQZVSIRWBIWAHULTUMZUNCIWAWCUOLUPFVREWAHIWAUH
      MNVTUQURUSUTVAVBVOVJVJSZVNSVPVJWDVNVJVDVEABCDFPGIIJKVFVGVH $.

    $d S n $.
    $( The relation in ` PrjSp ` is symmetric.  (Contributed by Steven Nguyen,
       1-May-2023.) $)
    prjspersym $p |- ( ( V e. LVec /\ X .~ Y ) -> Y .~ X ) $=
      ( wcel wa wceq cfv vm vn clvec wbr cv wrex simpllr prjsprel pm3.22 adantr
      co sylbi syl cinvr oveq1 eqeq2d cdr c0g wne simplll simplr simpll cbs csn
      lvecdrng cdif eldifsni eleq2s 3syl simpr oveq1d clmod ad4antr eldifi eqid
      lveclmod lmod0vs syl2anc 3eqtrd mteqand drnginvrcl syl3anc eldifd lvecinv
      wn nelsn mpbid rspcedvdw sylanbrc adantl r19.29a ) HUCQZIJDUDZRZIUAUEZJFU
      KZSZJIDUDZUAGWNWOGQZRZWQRZJCQZICQZRZJUBUEZIFUKZSZUBGUFWRXAWMXDWLWMWSWQUGZ
      WMXCXBRZWQUAGUFZRZXDABCDFUAGIJKLUHZXIXDXJXCXBUIUJULUMXAXGJWOEUNTZTZIFUKZS
      ZUBXNGXEXNSXFXOJXEXNIFUOUPXAEUQQZWSWOEURTZUSZXNGQXAWLXQWLWMWSWQUTZEHNVEUM
      WNWSWQVAZXAWOXRIHURTZXAWMXCIYBUSZXHWMXKXCXLXCXBXJVBULZYCIHVCTZYBVDZVFZCIY
      EYBVGMVHVIXAWOXRSZRZIWPXRJFUKZYBWTWQYHVAYIWOXRJFXAYHVJVKYIHVLQZJYEQZYJYBS
      WLYKWMWSWQYHHVPVMXAYLYHXAWMXBYLXHWMXKXBXLXCXBXJVAULYLJYGCJYEYFVNMVHVIZUJF
      EXRYEHJYBYEVOZNOXRVOZYBVOVQVRVSVTZGEXMWOXRPYOXMVOZWAWBXAWQXPWTWQVJXAWOFEX
      MGYEHIJXRYNONPYOYQXTXAWOGXRVDZYAXAXSWOYRQWEYPWOXRWFUMWCXAWMXCIYEQZXHYDYSI
      YGCIYEYFVNMVHVIYMWDWGWHABCDFUBGJIKLUHWIWMXJWLWMXKXJXLXIXJVJULWJWK $.

    $d V a b c $.  $d B a $.  $d .~ a b c $.  $d a b c l x y $.
    $( The relation used to define ` PrjSp ` is an equivalence relation.
       (Contributed by Steven Nguyen, 1-May-2023.) $)
    prjsper $p |- ( V e. LVec -> .~ Er B ) $=
      ( va vb wcel cv wa wbr vc clvec wrel wceq wrex relopabiv prjspersym clmod
      co a1i lveclmod prjspertr sylan wb prjsperref syl iserd ) HUBQZOPUACDDUCU
      RARZCQBRZCQSUSIRUTFUIUDIGUESABDJUFUJABCDEFGHORZPRZIJKLMNUGURHUHQZVAVBDTVB
      UARZDTSVAVDDTHUKZABCDEFGHVAVBVDIJKLMNULUMURVCVACQVAVADTUNVEABCDEFGHVAIJKL
      MNUOUPUQ $.

    ${
      $d .0. m $.
      prjspreln0.z $e |- .0. = ( 0g ` S ) $.
      $( Two nonzero vectors are equivalent by a nonzero scalar.  (Contributed
         by Steven Nguyen, 31-May-2023.) $)
      prjspreln0 $p |- ( V e. LVec -> ( X .~ Y <-> ( ( X e. B /\ Y e. B ) /\
         E. m e. ( K \ { .0. } ) X = ( m .x. Y ) ) ) ) $=
        ( wcel wbr wa cv co wceq wrex clvec csn cdif prjsprel simprl wne wn c0g
        cfv simplrl cbs eldifsni eleq2s syl simplrr simpr oveq1d clmod lveclmod
        difss eqsstri anassrs sselid eqid lmod0vs syl2anc 3eqtrd mteqand eldifd
        ad3antrrr nelsn ex jca2 reximdv2 wss ssrexv mp1i impbid pm5.32da bitrid
        wi ) JKDUAJCTZKCTZUBZJGUCZKFUDZUEZGHUFZUBIUGTZWJWMGHLUHZUIZUFZUBABCDFGH
        JKMNUJWOWJWNWRWOWJUBZWNWRWSWMWMGHWQWSWKHTZWMUBZWKWQTZWMWSXAXBWSXAUBZWKH
        WPWSWTWMUKXCWKLULWKWPTUMXCWKLJIUNUOZXCWHJXDULZWOWHWIXAUPXEJIUQUOZXDUHZU
        IZCJXFXDUROUSUTXCWKLUEZUBZJWLLKFUDZXDWSWTWMXIVAXJWKLKFXCXIVBVCXJIVDTZKX
        FTXKXDUEWOXLWJXAXIIVEVPXJCXFKCXHXFOXFXGVFVGWSXAXIWIWOWHWIXAXIUBVAVHVIFE
        LXFIKXDXFVJPQSXDVJVKVLVMVNWKLVQUTVOVRWTWMVBVSVTWQHWAWRWNWGWSHWPVFWMGWQH
        WBWCWDWEWF $.

      $d l m x y N $.
      $( A nonzero multiple of a vector is equivalent to the vector.
         (Contributed by Steven Nguyen, 6-Jun-2023.) $)
      prjspvs $p |- ( ( V e. LVec /\ X e. B /\ N e. ( K \ { .0. } ) ) ->
                                                         ( N .x. X ) .~ X ) $=
        ( vm wcel clvec csn cdif w3a co cv wceq wrex wbr cbs cfv c0g eqid clmod
        lveclmod 3ad2ant1 eldifi 3ad2ant3 difss eqsstri sseli 3ad2ant2 eldifsni
        lmodvscld eleq2s simp1 lvecvsn0 mpbir2and eldifsnd eleqtrrdi simp2 wtru
        wne wb oveq1 eqcoms tbtru sylib trud rspcedvdw prjsprel syl21anbrc ) IU
        ATZJCTZHGKUBZUCTZUDZHJFUEZCTWDWHSUFZJFUEUGZSGUHWHJDUIWGWHIUJUKZIULUKZUB
        ZUCZCWGWHWKWLWGHFEGWKIJWKUMZOPQWCWDIUNTWFIUOUPWFWCHGTWDHGWEUQURZWDWCJWK
        TWFCWKJCWNWKNWKWMUSUTVAVBZVDWGWHWLVMHKVMZJWLVMZWFWCWRWDHGKVCURWDWCWSWFW
        SJWNCJWKWLVCNVEVBWGHFEGKWKIJWLWOPOQRWLUMWCWDWFVFWPWQVGVHVINVJWCWDWFVKWG
        WJVLSHGWIHUGWJWJVLVNWJHWIHWIJFVOVPWJVQVRWPWGVSVTABCDFSGWHJLMWAWB $.
    $}

    ${
      prjsprellsp.n $e |- N = ( LSpan ` V ) $.
      $( Two vectors are equivalent iff their spans are equal.  (Contributed by
         Steven Nguyen, 31-May-2023.) $)
      prjsprellsp $p |- ( ( V e. LVec /\ ( X e. B /\ Y e. B ) ) ->
         ( X .~ Y <-> ( N ` { X } ) = ( N ` { Y } ) ) ) $=
        ( wcel cfv vm clvec wa cv wceq c0g csn cdif wrex wbr ibar bicomd adantl
        co wb eqid prjspreln0 adantr cbs simpl eldifi ad2antrl ad2antll lspsneq
        eleq2s 3bitr4d ) IUBSZJCSZKCSZUCZUCZVJJUAUDKFUNUEUAGEUFTZUGUHUIZUCZVMJK
        DUJZJUGHTKUGHTUEVJVNVMUOVGVJVMVNVJVMUKULUMVGVOVNUOVJABCDEFUAGIJKVLLMNOP
        QVLUPZUQURVKEFUAGHIUSTZIJKVLVQUPOQVPPRVGVJUTVHJVQSZVGVIVRJVQIUFTUGZUHZC
        JVQVSVANVEVBVIKVQSZVGVHWAKVTCKVQVSVANVEVCVDVF $.

      $d l x V $.  $d l x N $.  $d l S $.  $d l B $.
      $( The vectors equivalent to a vector ` X ` are the nonzero vectors in
         the span of ` X ` .  (Contributed by Steven Nguyen, 6-Jun-2023.) $)
      prjspeclsp $p |- ( ( V e. LVec /\ X e. B ) ->
         [ X ] .~ = ( ( N ` { X } ) \ { ( 0g ` V ) } ) ) $=
        ( wcel wa wceq clvec ccnv cec cv co wrex cbs cfv crab c0g csn cab copab
        cdif cnveqi cnvopab eqtri eceq2i cima df-ec imaopab df-rex velsn anbi1i
        a1i wex eleq1 anbi2d oveq2 eqeq2d rexbidv anbi12d pm5.32i bitri elisset
        exbii 19.41v ad2antlr pm4.71ri bitr4i 3bitri abbii bicomd anbi1d abbidv
        iba eqtrid adantl 3eqtrd df-rab rabeqi rabdif eqtr4id 3eqtr2d wer ercnv
        prjsper adantr eqcomd syl clmod lveclmod difss eqsstri sseli eqid lspsn
        eceq2d syl2an simpr lmodvscld eqeltrd rexlimdva2 pm4.71rd eqtr4di eqtrd
        difeq1d 3eqtr4d ) IUARZJCRZSZJDUBZUCZAUDZKUDZJFUEZTZKGUFZAIUGUHZUIZIUJU
        HUKZUNZJDUCJUKZHUHZYKUNYAYCYDCRZYHSZAULZYHACUIZYLYAYCJYOBUDZCRZSZYDYEYS
        FUEZTZKGUFZSZBAUMZUCZYQYBUUFJYBUUEABUMZUBUUFDUUHLUOUUEABUPUQURYAUUGUUFY
        MUSZUUEBYMUFZAULZYQUUGUUITYAJUUFUTVEUUIUUKTYAUUEBAYMVAVEXTUUKYQTXSXTUUK
        YOXTSZYHSZAULYQUUJUUMAUUJYSYMRZUUESZBVFYSJTZUUMSZBVFZUUMUUEBYMVBUUOUUQB
        UUOUUPUUESUUQUUNUUPUUEBJVCVDUUPUUEUUMUUPUUAUULUUDYHUUPYTXTYOYSJCVGVHUUP
        UUCYGKGUUPUUBYFYDYSJYEFVIVJVKVLVMVNVPUURUUPBVFZUUMSUUMUUPUUMBVQUUMUUSXT
        UUSYOYHBJCVOVRVSVTWAWBXTUUMYPAXTUULYOYHXTYOUULXTYOWFWCWDWEWGWHWIWGYRYQT
        YAYHACWJVEYAYRYHAYIYKUNZUIZYLYHACUUTMWKYLUVATYAYHAYIYKWLVEWMWNYADYBJYAC
        DWOZDYBTXSUVBXTABCDEFGIKLMNOPWQWRUVBYBDCDWPWSWTXHYAYNYJYKYAYNYHAULZYJXS
        IXARZJYIRZYNUVCTXTIXBZCYIJCUUTYIMYIYKXCXDXEZAFKEGHYIIJNPYIXFZOQXGXIYAUV
        CYDYIRZYHSZAULYJYAYHUVJAYAYHUVIYAYGUVIKGYAYEGRZSZYGSYDYFYIUVLYGXJUVLYFY
        IRYGUVLYEFEGYIIJUVHNOPYAUVDUVKXSUVDXTUVFWRWRYAUVKXJXTUVEXSUVKUVGVRXKWRX
        LXMXNWEYHAYIWJXOXPXQXR $.
    $}
  $}

  ${
    $d l x y z V $.  $d l x y z B $.  $d l x N $.
    prjspval2.0 $e |- .0. = ( 0g ` V ) $.
    prjspval2.b $e |- B = ( ( Base ` V ) \ { .0. } ) $.
    prjspval2.n $e |- N = ( LSpan ` V ) $.
    $( Alternate definition of projective space.  (Contributed by Steven
       Nguyen, 7-Jun-2023.) $)
    prjspval2 $p |- ( V e. LVec ->
                 ( PrjSp ` V ) = U_ z e. B { ( ( N ` { z } ) \ { .0. } ) } ) $=
      ( vx vy vl wcel cfv cv wa wceq cbs csn cdif eqid clvec cvsca co csca wrex
      cprjsp copab cqs cec ciun c0g sneqi difeq2i eqtri prjspval a1i prjspeclsp
      dfqs3 eqtr4di sneqd iuneq2dv 3eqtrd ) DUALZDUFMBINZBLJNZBLOVDKNVEDUBMZUCP
      KDUDMZQMZUEOIJUGZUHZABANZVIUIZRZUJZABVKRCMZERZSZRZUJIJBVGVFVHDKBDQMZVPSVS
      DUKMZRZSGVPWAVSEVTFULZUMUNZVFTZVGTZVHTZUOVJVNPVCABVIURUPVCABVMVRVCVKBLOZV
      LVQWGVLVOWASVQIJBVIVGVFVHCDVKKVITWCWEWDWFHUQVPWAVOWBUMUSUTVAVB $.
  $}

  $c PrjSpn $.

  $( Extend class notation with the n-dimensional projective space function. $)
  cprjspn $a class PrjSpn $.

  ${
    $d n k $.
    $( Define the n-dimensional projective space function.  A projective space
       of dimension 1 is a projective line, and a projective space of dimension
       2 is a projective plane.  Compare ~ df-ehl .  This space is considered
       n-dimensional because the vector space ` ( k freeLMod ( 0 ... n ) ) ` is
       (n+1)-dimensional and the ` PrjSp ` function returns equivalence classes
       with respect to a linear (1-dimensional) relation.  (Contributed by BJ
       and Steven Nguyen, 29-Apr-2023.) $)
    df-prjspn $a |- PrjSpn = ( n e. NN0 , k e. DivRing |->
      ( PrjSp ` ( k freeLMod ( 0 ... n ) ) ) ) $.
  $}

  ${
    $d n k N $.  $d n k K $.
    $( Value of the n-dimensional projective space function.  (Contributed by
       Steven Nguyen, 1-May-2023.) $)
    prjspnval $p |- ( ( N e. NN0 /\ K e. DivRing ) -> ( N PrjSpn K ) =
      ( PrjSp ` ( K freeLMod ( 0 ... N ) ) ) ) $=
      ( vn vk cn0 cdr cv cc0 cfz co cfrlm cprjsp cfv cprjspn wceq oveq2d fveq2d
      oveq2 fvoveq1 df-prjspn fvex ovmpo ) CDBAEFDGZHCGZIJZKJZLMAHBIJZKJZLMNUCU
      GKJZLMUDBOZUFUILUJUEUGUCKUDBHIRPQUCAUGLKSDCTUHLUAUB $.
  $}

  ${
    $d K x y $.  $d W l $.  $d S l $.
    prjspnerlem.e $e |- .~ = { <. x , y >. |
      ( ( x e. B /\ y e. B ) /\ E. l e. S x = ( l .x. y ) ) } $.
    prjspnerlem.w $e |- W = ( K freeLMod ( 0 ... N ) ) $.
    prjspnerlem.b $e |- B = ( ( Base ` W ) \ { ( 0g ` W ) } ) $.
    prjspnerlem.s $e |- S = ( Base ` K ) $.
    prjspnerlem.x $e |- .x. = ( .s ` W ) $.
    $( A lemma showing that the equivalence relation used in ~ prjspnval2 and
       the equivalence relation used in ~ prjspval are equal, but only with the
       antecedent ` K e. DivRing ` .  (Contributed by SN, 15-Jul-2023.) $)
    prjspnerlem $p |- ( K e. DivRing ->
        .~ = { <. x , y >. | ( ( x e. B /\ y e. B ) /\
                     E. l e. ( Base ` ( Scalar ` W ) ) x = ( l .x. y ) ) } ) $=
      ( wcel cv wa cfv cbs cdr co wceq wrex copab csca cc0 cfz cvv ovex frlmsca
      mpan2 fveq2d eqtrid rexeqdv anbi2d opabbidv ) GUAPZDAQZCPBQZCPRZUSJQUTFUB
      UCZJEUDZRZABUEVAVBJIUFSZTSZUDZRZABUEKURVDVHABURVCVGVAURVBJEVFUREGTSVFNURG
      VETURUGHUHUBZUIPGVEUCUGHUHUJGIVIUAUILUKULUMUNUOUPUQUN $.
  $}

  ${
    $d W l x y $.  $d K x y $.  $d S l $.
    prjspnval2.e $e |- .~ = { <. x , y >. |
      ( ( x e. B /\ y e. B ) /\ E. l e. S x = ( l .x. y ) ) } $.
    prjspnval2.w $e |- W = ( K freeLMod ( 0 ... N ) ) $.
    prjspnval2.b $e |- B = ( ( Base ` W ) \ { ( 0g ` W ) } ) $.
    prjspnval2.s $e |- S = ( Base ` K ) $.
    prjspnval2.x $e |- .x. = ( .s ` W ) $.
    $( Value of the n-dimensional projective space function, expanded.
       (Contributed by Steven Nguyen, 15-Jul-2023.) $)
    prjspnval2 $p |-
      ( ( N e. NN0 /\ K e. DivRing ) -> ( N PrjSpn K ) = ( B /. .~ ) ) $=
      ( wcel wa co cprjsp cfv cn0 cdr cprjspn cc0 cfz cqs prjspnval wceq fveq2i
      cfrlm csca cbs wrex copab clvec cvv ovex frlmlvec mpan2 eqid prjspval syl
      cv prjspnerlem qseq2d eqtr4d eqtr3id adantl eqtrd ) HUAPZGUBPZQHGUCRGUDHU
      ERZUJRZSTZCDUFZGHUGVKVNVOUHVJVKVNISTZVOIVMSLUIVKVPCAVCZCPBVCZCPQVQJVCVRFR
      UHJIUKTZULTZUMQABUNZUFZVOVKIUOPZVPWBUHVKVLUPPWCUDHUEUQGIVLUPLURUSABCVSFVT
      IJMOVSUTVTUTVAVBVKDWACABCDEFGHIJKLMNOVDVEVFVGVHVI $.
  $}

  ${
    $d W l x y $.  $d B x y $.  $d S l $.  $d .x. l x y $.  $d K x y $.
    prjspner.e $e |- .~ = { <. x , y >. |
      ( ( x e. B /\ y e. B ) /\ E. l e. S x = ( l .x. y ) ) } $.
    prjspner.w $e |- W = ( K freeLMod ( 0 ... N ) ) $.
    prjspner.b $e |- B = ( ( Base ` W ) \ { ( 0g ` W ) } ) $.
    prjspner.s $e |- S = ( Base ` K ) $.
    prjspner.x $e |- .x. = ( .s ` W ) $.
    prjspner.k $e |- ( ph -> K e. DivRing ) $.
    $( The relation used to define ` PrjSp ` (and indirectly ` PrjSpn ` through
       ~ df-prjspn ) is an equivalence relation.  This is a lemma that converts
       the equivalence relation used in results like ~ prjspertr and
       ~ prjspersym (see ~ prjspnerlem ).  Several theorems are covered in one
       thanks to the theorems around ~ df-er .  (Contributed by SN,
       14-Aug-2023.) $)
    prjspner $p |- ( ph -> .~ Er B ) $=
      ( cv wcel eqid wer wa co wceq csca cfv cbs wrex copab clvec cdr cc0 ovexd
      cfz cvv frlmlvec syl2anc prjsper syl wb prjspnerlem ereq1 3syl mpbird ) A
      DEUAZDBRZDSCRZDSUBVFKRVGGUCUDKJUEUFZUGUFZUHUBBCUIZUAZAJUJSZVKAHUKSZULIUNU
      CZUOSVLQAULIUNUMHJVNUOMUPUQBCDVJVHGVIJKVJTNVHTPVITURUSAVMEVJUDVEVKUTQBCDE
      FGHIJKLMNOPVADEVJVBVCVD $.
  $}

  ${
    $d W l x y $.  $d B x y $.  $d S l $.  $d .x. l x y $.  $d K x y $.
    $d X l x y $.  $d C l x y $.
    prjspnvs.e $e |- .~ = { <. x , y >. |
      ( ( x e. B /\ y e. B ) /\ E. l e. S x = ( l .x. y ) ) } $.
    prjspnvs.w $e |- W = ( K freeLMod ( 0 ... N ) ) $.
    prjspnvs.b $e |- B = ( ( Base ` W ) \ { ( 0g ` W ) } ) $.
    prjspnvs.s $e |- S = ( Base ` K ) $.
    prjspnvs.x $e |- .x. = ( .s ` W ) $.
    prjspnvs.0 $e |- .0. = ( 0g ` K ) $.
    prjspnvs.k $e |- ( ph -> K e. DivRing ) $.
    prjspnvs.1 $e |- ( ph -> X e. B ) $.
    prjspnvs.2 $e |- ( ph -> C e. S ) $.
    prjspnvs.3 $e |- ( ph -> C =/= .0. ) $.
    $( A nonzero multiple of a vector is equivalent to the vector.  This
       converts the equivalence relation used in ~ prjspvs (see
       ~ prjspnerlem ).  (Contributed by SN, 8-Aug-2024.) $)
    prjspnvs $p |- ( ph -> ( C .x. X ) .~ X ) $=
      ( co wbr cv wcel wa wceq csca cfv cbs wrex copab c0g csn cdif cdr cc0 cfz
      clvec cvv ovexd frlmlvec syl2anc wne wn nelsn eldifd frlmsca fveq2d sneqd
      syl eqtrid difeq12d eleqtrd eqid prjspvs syl3anc prjspnerlem breqd mpbird
      ) AELHUEZLFUFWDLBUGZDUHCUGZDUHUIWENUGWFHUEUJNKUKULZUMULZUNUIBCUOZUFZAKVBU
      HZLDUHEWHWGUPULZUQZURZUHWJAIUSUHZUTJVAUEZVCUHZWKUAAUTJVAVDZIKWPVCPVEVFUBA
      EGMUQZURWNAEGWSUCAEMVGEWSUHVHUDEMVIVNVJAGWHWSWMAGIUMULWHRAIWGUMAWOWQIWGUJ
      UAWRIKWPUSVCPVKVFZVLVOAMWLAMIUPULWLTAIWGUPWTVLVOVMVPVQBCDWIWGHWHEKLWLNWIV
      RQWGVRSWHVRWLVRVSVTAFWIWDLAWOFWIUJUABCDFGHIJKNOPQRSWAVNWBWC $.
  $}

  ${
    $d W l x y $.  $d K l x y $.  $d B x y $.
    prjspnssbas.p $e |- P = ( N PrjSpn K ) $.
    prjspnssbas.w $e |- W = ( K freeLMod ( 0 ... N ) ) $.
    prjspnssbas.b $e |- B = ( ( Base ` W ) \ { ( 0g ` W ) } ) $.
    prjspnssbas.n $e |- ( ph -> N e. NN0 ) $.
    prjspnssbas.k $e |- ( ph -> K e. DivRing ) $.
    $( A projective point spans a subset of the (nonzero) affine points.
       (Contributed by SN, 17-Jan-2025.) $)
    prjspnssbas $p |- ( ph -> P C_ ~P B ) $=
      ( vx vy vl cv wcel wa cfv co eqid cvsca wceq cbs wrex cqs cpw cprjspn cn0
      copab cdr prjspnval2 syl2anc eqtrid prjspner qsss eqsstrd ) ACBLOZBPMOZBP
      QUQNOURFUARZSUBNDUCRZUDQLMUIZUEZBUFACEDUGSZVBGAEUHPDUJPVCVBUBJKLMBVAUTUSD
      EFNVATZHIUTTZUSTZUKULUMABVAALMBVAUTUSDEFNVDHIVEVFKUNUOUP $.

    prjspnn0.a $e |- ( ph -> A e. P ) $.
    $( A projective point is nonempty.  (Contributed by SN, 17-Jan-2025.) $)
    prjspnn0 $p |- ( ph -> A =/= (/) ) $=
      ( vx vy vl cv wcel wceq eqid wa cvsca cfv co cbs copab cdm cqs c0 wne wer
      wrex prjspner erdm syl cprjspn cn0 cdr prjspnval2 syl2anc eqtrid eleqtrd
      elqsn0 ) ANQZCROQZCRUAVDPQVEGUBUCZUDSPEUEUCZULUANOUFZUGCSZBCVHUHZRBUIUJAC
      VHUKVIANOCVHVGVFEFGPVHTZIJVGTZVFTZLUMCVHUNUOABDVJMADFEUPUDZVJHAFUQREURRVN
      VJSKLNOCVHVGVFEFGPVKIJVLVMUSUTVAVBCBVHVCUT $.
  $}

  ${
    0prjspnlem.b $e |- B = ( ( Base ` W ) \ { ( 0g ` W ) } ) $.
    0prjspnlem.w $e |- W = ( K freeLMod ( 0 ... 0 ) ) $.
    0prjspnlem.1 $e |- .1. = ( ( K unitVec ( 0 ... 0 ) ) ` 0 ) $.
    $( Lemma for ~ 0prjspn .  The given unit vector is a nonzero vector.
       (Contributed by Steven Nguyen, 16-Jul-2023.) $)
    0prjspnlem $p |- ( K e. DivRing -> .1. e. B ) $=
      ( cdr wcel cc0 cfz co cuvc cfv cbs c0g csn cdif cvv eqid drngnzr eleqtrri
      cnzr ovex c0ex snid fz0sn w3a wne crg nzrring uvccl syl3an1 uvcn0 eldifsn
      sylanbrc mp3an23 syl 3eltr4g ) CHIZJCJJKLZMLZNZDONZDPNZQRZBAUTCUCIZVCVFIZ
      CUAVGVASIZJVAIZVHJJKUDJJQVAJUEUFUGUBVGVIVJUHVCVDIZVCVEUIVHVGCUJIVIVJVKCUK
      VDCVBVAJSDVBTZFVDTZULUMVDCVBVAJSDVEVLFVMVETUNVCVDVEUOUPUQURGEUS $.
  $}

  ${
    $d .0. b $.  $d .x. b $.  $d B b $.  $d I b $.  $d X b $.
    prjspnfv01.f $e |- F = ( b e. B |->
      if ( ( b ` 0 ) = .0. , b , ( ( I ` ( b ` 0 ) ) .x. b ) ) ) $.
    prjspnfv01.b $e |- B = ( ( Base ` W ) \ { ( 0g ` W ) } ) $.
    prjspnfv01.w $e |- W = ( K freeLMod ( 0 ... N ) ) $.
    prjspnfv01.t $e |- .x. = ( .s ` W ) $.
    prjspnfv01.0 $e |- .0. = ( 0g ` K ) $.
    prjspnfv01.1 $e |- .1. = ( 1r ` K ) $.
    prjspnfv01.i $e |- I = ( invr ` K ) $.
    prjspnfv01.k $e |- ( ph -> K e. DivRing ) $.
    prjspnfv01.n $e |- ( ph -> N e. NN0 ) $.
    prjspnfv01.x $e |- ( ph -> X e. B ) $.
    $( Any vector is equivalent to a vector whose zeroth coordinate is ` .0. `
       or ` .1. ` (proof of the value of the zeroth coordinate).  (Contributed
       by SN, 13-Aug-2023.) $)
    prjspnfv01 $p |-
      ( ph -> ( ( F ` X ) ` 0 ) = if ( ( X ` 0 ) = .0. , .0. , .1. ) ) $=
      ( cc0 cfv wceq co cif cv cvv fveq1 eqeq1d id fveq2d ifbieq12d ovexd ifexd
      oveq12d fvmptd3 fveq1d iffv a1i simpr wn wa cmulr cbs cfz eqid cdr wne wf
      wcel c0g csn cdif eleqtrdi eldifad frlmbasf syl2anc 0elfz ffvelcdmd neqne
      cn0 syl drnginvrcl syl2an3an adantr frlmvscaval drnginvrl ifeq12da 3eqtrd
      eqtrd ) AUCJEUDZUDUCUCJUDZKUEZJWNFUDZJCUFZUGZUDZWOWNUCWQUDZUGZWOKDUGAUCWM
      WRALJUCLUHZUDZKUEZXBXCFUDZXBCUFZUGWRBEUIMXBJUEZXDWOXBXFJWQXGXCWNKUCXBJUJZ
      UKXGULZXGXEWPXBJCXGXCWNFXHUMXIUQUNUBAWOJWQBUIUBAWPJCUOUPURUSWSXAUEAWOUCJW
      QUTVAAWOWNWTKDAWOVBAWOVCZVDZWTWPWNGVEUDZUFZDXKWPIVFUDZGCXLUCHVGUFZUCGVFUD
      ZUIJIOXNVHZXPVHZXKUCHVGUOAGVIVLZWNXPVLZXJWNKVJZWPXPVLTAXOXPUCJAXOUIVLJXNV
      LZXOXPJVKAUCHVGUOAJXNIVMUDVNZAJBXNYCVOUBNVPVQZXNGIXOXPUIJOXRXQVRVSAHWCVLU
      CXOVLZUAHVTWDZWAZWNKWBZXPGFWNKXRQSWEWFAYBXJYDWGAYEXJYFWGPXLVHZWHAXSXTXJYA
      XMDUETYGYHXPGXLDFWNKXRQYIRSWIWFWLWJWK $.
  $}

  ${
    $d B x y $.  $d X l x y $.  $d W l x y $.  $d .x. l x y $.  $d S l $.
    $d I l x y $.  $d K x y $.  $d .0. x y $.  $d B b $.  $d X b $.
    $d .0. b $.  $d .x. b $.  $d I b $.  $d ph b $.
    prjspner01.e $e |- .~ = { <. x , y >. |
      ( ( x e. B /\ y e. B ) /\ E. l e. S x = ( l .x. y ) ) } $.
    prjspner01.f $e |- F = ( b e. B |->
      if ( ( b ` 0 ) = .0. , b , ( ( I ` ( b ` 0 ) ) .x. b ) ) ) $.
    prjspner01.b $e |- B = ( ( Base ` W ) \ { ( 0g ` W ) } ) $.
    prjspner01.w $e |- W = ( K freeLMod ( 0 ... N ) ) $.
    prjspner01.t $e |- .x. = ( .s ` W ) $.
    prjspner01.s $e |- S = ( Base ` K ) $.
    prjspner01.0 $e |- .0. = ( 0g ` K ) $.
    prjspner01.i $e |- I = ( invr ` K ) $.
    prjspner01.k $e |- ( ph -> K e. DivRing ) $.
    prjspner01.n $e |- ( ph -> N e. NN0 ) $.
    prjspner01.x $e |- ( ph -> X e. B ) $.
    $( Any vector is equivalent to a vector whose zeroth coordinate is ` .0. `
       or ` .1. ` (proof of the equivalence).  (Contributed by SN,
       13-Aug-2023.) $)
    prjspner01 $p |- ( ph -> X .~ ( F ` X ) ) $=
      ( cc0 cfv wceq co cif wbr wif prjspner erref adantr wn wa wer cdr wne cfz
      wcel cvv cbs wf ovexd c0g csn cdif eleqtrdi eldifad eqid frlmbasf syl2anc
      cn0 0elfz syl ffvelcdmd drnginvrcl syl2an3an drnginvrn0 prjspnvs ifpimpda
      neqne ersym brif2 sylibr cv fveq1 eqeq1d fveq2d oveq12d ifbieq12d fvmptd3
      id ifexd breqtrrd ) AMUHMUIZNUJZMWTIUIZMGUKZULZMHUIEAXAMMEUMZMXCEUMZUNMXD
      EUMAXAXEXFAXEXAAMEDABCDEFGJKLPQTSUBUAUEUOZUGUPUQAXAURZUSZXCMEDADEUTXHXGUQ
      XIBCDXBEFGJKLMNPQTSUBUAUCAJVAVDZXHUEUQAMDVDXHUGUQAXJWTFVDZXHWTNVBZXBFVDUE
      AUHKVCUKZFUHMAXMVEVDMLVFUIZVDXMFMVGAUHKVCVHAMXNLVIUIVJZAMDXNXOVKUGSVLVMXN
      JLXMFVEMTUBXNVNVOVPAKVQVDUHXMVDUFKVRVSVTZWTNWFZFJIWTNUBUCUDWAWBAXJXKXHXLX
      BNVBUEXPXQFJIWTNUBUCUDWCWBWDWGWEXAMXCMEWHWIAOMUHOWJZUIZNUJZXRXSIUIZXRGUKZ
      ULXDDHVERXRMUJZXTXAXRYBMXCYCXSWTNUHXRMWKZWLYCWQZYCYAXBXRMGYCXSWTIYDWMYEWN
      WOUGAXAMXCDVEUGAXBMGVHWRWPWS $.

    $d Y l m x y $.  $d Y b $.  $d B m $.  $d I m $.  $d X m $.  $d .x. m $.
    $d ph m $.  $d S m x y $.
    prjspner1.y $e |- ( ph -> Y e. B ) $.
    prjspner1.1 $e |- ( ph -> ( X ` 0 ) =/= .0. ) $.
    prjspner1.2 $e |- ( ph -> ( Y ` 0 ) =/= .0. ) $.
    $( Two vectors whose zeroth coordinate is nonzero are equivalent if and
       only if they have the same representative in the (n-1)-dimensional
       affine subspace { x_0 = 1 } .  For example, vectors in 3D space whose
       ` x ` coordinate is nonzero are equivalent iff they intersect at the
       plane ` x = 1 ` at the same point (also see section header).
       (Contributed by SN, 13-Aug-2023.) $)
    prjspner1 $p |- ( ph -> ( X .~ Y <-> ( F ` X ) = ( F ` Y ) ) ) $=
      ( vm wbr cfv wceq wcel wa cv co wrex prjsprel cc0 cif wne fveq1 drngringd
      c0g cfz cvv ovexd cn0 syl frlm0vald sylan9eqr mteqand cdr frlmsca syl2anc
      0elfz csca fveq2d eqtrid oveq1d clmod cbs frlmlvec lveclmodd csn eleqtrdi
      clvec cdif eldifad eqid lmod0vs eqtrd neeqtrrd ad2antrr neeq2d syl5ibrcom
      oveq1 necon2d ancrd cmulr simplr ad3antrrr frlmvscaval frlmbasf ffvelcdmd
      simpr drnginvmuld drnginvrcld ringcld eleqtrd lmodvsass syl13anc ringassd
      crg oveqd cur drnginvrld oveq2d ringridmd 3eqtr3d 3eqtr2d oveq12d expimpd
      wf id eqeq1d syld rexlimdva impr neneqd iffalsed adantr 3eqtr4d ifbieq12d
      ifexd fvmptd3 prjspner01 simprll simprlr sylan2b wer prjspner ercl2 erref
      wb breq2 adantl mpbid ertr4d ertrd impbida ) AMNEUMZMHUNZNHUNZUOZUUOAMDUP
      ZNDUPZUQZMULURZNGUSZUOZULFUTZUQZUURBCDEGULFMNQRVAAUVFUQZVBMUNZOUOZMUVHIUN
      ZMGUSZVCZVBNUNZOUOZNUVMIUNZNGUSZVCZUUPUUQUVGUVKUVPUVLUVQAUVAUVEUVKUVPUOZA
      UVAUQZUVDUVRULFUVSUVBFUPZUQZUVDUVBOVDZUVDUQUVRUWAUVDUWBUWAUVBOMUVCUWAMUVC
      VDUVBOUOZMONGUSZVDZAUWEUVAUVTAMLVGUNZUWDAMUWFUVHOUJMUWFUOAUVHVBUWFUNOVBMU
      WFVEAJLVBKVHUSZVBVIOUAUDAJUFVFZAVBKVHVJZAKVKUPVBUWGUPZUGKVSVLZVMVNVOAUWDL
      VTUNZVGUNZNGUSZUWFAOUWMNGAOJVGUNUWMUDAJUWLVGAJVPUPZUWGVIUPZJUWLUOZUFUWIJL
      UWGVPVIUAVQZVRZWAWBWCALWDUPZNLWEUNZUPZUWNUWFUOALAUWOUWPLWJUPUFUWIJLUWGVIU
      AWFVRWGZANUXAUWFWHZANDUXAUXDWKUITWIWLZGUWLUWMUXALNUWFUXAWMZUWLWMZUBUWMWMU
      WFWMWNVRWOWPWQUWCUVCUWDMUVBONGWTWRWSXAXBUWAUWBUVDUVRUWAUWBUQZUVRUVDVBUVCU
      NZIUNZUVCGUSZUVPUOUXHUXKUVOUVBIUNZJXCUNZUSZUVCGUSZUXNUVBUWLXCUNZUSZNGUSZU
      VPUXHUXJUXNUVCGUXHUXJUVBUVMUXMUSZIUNUXNUXHUXIUXSIUXHUVBUXAJGUXMUWGVBFVINL
      UAUXFUCUXHVBKVHVJZUVSUVTUWBXDZAUXBUVAUVTUWBUXEXEZAUWJUVAUVTUWBUWKXEUBUXMW
      MZXFWAUXHFJUXMIUVBUVMOUCUDUYCUEAUWOUVAUVTUWBUFXEZUYAAUVMFUPUVAUVTUWBAUWGF
      VBNAUWPUXBUWGFNYGUWIUXEUXAJLUWGFVINUAUCUXFXGVRUWKXHXEZUWAUWBXIZAUVMOVDUVA
      UVTUWBUKXEZXJWOWCUXHUWTUXNUWLWEUNZUPUVBUYHUPUXBUXRUXOUOAUWTUVAUVTUWBUXCXE
      UXHUXNFUYHUXHFJUXMUVOUXLUCUYCAJXQUPUVAUVTUWBUWHXEZUXHFJIUVMOUCUDUEUYDUYEU
      YGXKZUXHFJIUVBOUCUDUEUYDUYAUYFXKZXLAFUYHUOUVAUVTUWBAFJWEUNUYHUCAJUWLWEUWS
      WAWBXEZXMUXHUVBFUYHUYAUYLXMUYBUXNUVBGUXPUWLUYHUXALNUXFUXGUBUYHWMUXPWMXNXO
      UXHUXQUVONGUXHUXNUVBUXMUSUVOUXLUVBUXMUSZUXMUSZUXQUVOUXHFJUXMUVOUXLUVBUCUY
      CUYIUYJUYKUYAXPUXHUXMUXPUXNUVBUXHJUWLXCUXHUWOUWPUWQUYDUXTUWRVRWAXRUXHUYNU
      VOJXSUNZUXMUSUVOUXHUYMUYOUVOUXMUXHFJUXMUYOIUVBOUCUDUYCUYOWMZUEUYDUYAUYFXT
      YAUXHFJUXMUYOUVOUCUYCUYPUYIUYJYBWOYCWCYDUVDUVKUXKUVPUVDUVJUXJMUVCGUVDUVHU
      XIIVBMUVCVEWAUVDYHYEYIWSYFYJYKYLAUVLUVKUOUVFAUVIMUVKAUVHOUJYMYNYOAUVQUVPU
      OUVFAUVNNUVPAUVMOUKYMYNYOYPUVGPMVBPURZUNZOUOZUYQUYRIUNZUYQGUSZVCZUVLDHVIS
      UYQMUOZUYSUVIUYQVUAMUVKVUCUYRUVHOVBUYQMVEZYIVUCYHZVUCUYTUVJUYQMGVUCUYRUVH
      IVUDWAVUEYEYQAUUSUUTUVEUUAZUVGUVIMUVKDVIVUFUVGUVJMGVJYRYSUVGPNVUBUVQDHVIS
      UYQNUOZUYSUVNUYQVUANUVPVUGUYRUVMOVBUYQNVEZYIVUGYHZVUGUYTUVOUYQNGVUGUYRUVM
      IVUHWAVUIYEYQAUUSUUTUVEUUBZUVGUVNNUVPDVIVUJUVGUVONGVJYRYSYPUUCAUURUQZMUUP
      NEDADEUUDUURABCDEFGJKLQRUATUCUBUFUUEZYOZAMUUPEUMUURABCDEFGHIJKLMOPQRSTUAU
      BUCUDUEUFUGUHYTZYOVUKUUPUUQNEDVUMVUKUUPUUPEUMZUUPUUQEUMZVUKUUPEDVUMAUUPDU
      PUURAMUUPEDVULVUNUUFYOUUGUURVUOVUPUUHAUUPUUQUUPEUUIUUJUUKANUUQEUMUURABCDE
      FGHIJKLNOPQRSTUAUBUCUDUEUFUGUIYTYOUULUUMUUN $.
  $}

  ${
    $d B x y m $.  $d X x y l m $.  $d K x y l m $.  $d .x. x y l m $.
    $d .1. x y l m $.  $d S x y l m $.  $d S n $.  $d .x. n $.  $d .1. n $.
    $d .1. c $.  $d .1. d $.  $d B c $.  $d B d $.  $d B m n $.  $d X c n $.
    $d X d $.  $d K c $.  $d K d n $.
    0prjspnrel.e $e |- .~ = { <. x , y >. |
      ( ( x e. B /\ y e. B ) /\ E. l e. S x = ( l .x. y ) ) } $.
    0prjspnrel.b $e |- B = ( ( Base ` W ) \ { ( 0g ` W ) } ) $.
    0prjspnrel.x $e |- .x. = ( .s ` W ) $.
    0prjspnrel.s $e |- S = ( Base ` K ) $.
    0prjspnrel.w $e |- W = ( K freeLMod ( 0 ... 0 ) ) $.
    0prjspnrel.1 $e |- .1. = ( ( K unitVec ( 0 ... 0 ) ) ` 0 ) $.
    $( In the zero-dimensional projective space, all vectors are equivalent to
       the unit vector.  (Contributed by Steven Nguyen, 7-Jun-2023.) $)
    0prjspnrel $p |- ( ( K e. DivRing /\ X e. B ) -> X .~ .1. ) $=
      ( wcel cc0 cvv vm vn vc vd cdr wa cv co wceq wrex simpr 0prjspnlem adantr
      wbr cfz csn cxp cbs cfv sneq xpeq2d eqeq2d ovexd cdif difss eqsstri sseli
      wf c0g adantl eqid frlmbasf syl2anc c0ex snid eleqtrri a1i ffvelcdmd cmap
      fz0sn frlmbasmap fvex mapsnconst syl rspcedvdw weq oveq1 simprl eleqtrrdi
      cmulr cof ad2antrr sselid frlmvscafval cur wss wral crg drngring ringidcl
      cuvc elfz1eq fveq12d simplll uvcvv1 elsn sylibr eqeltrd ralrimiva fcdmssb
      wb snssd mpbid vex elsni oveq2d ringridmd sylan9eqr caofid2 eqtrd biimprd
      impr rexlimddv prjsprel syl21anbrc ) HUERZJCRZUFZYGGCRZJUAUGZGFUHZUIZUAEU
      JZJGDUNYFYGUKYFYIYGCGHIMPQULZUMYHJSSUOUHZUBUGZUPZUQZUIZYMUBHURUSZYHYSJYOS
      JUSZUPZUQZUIZUBUUAYTYPUUAUIZYRUUCJUUEYQUUBYOYPUUAUTVAVBYHYOYTSJYHYOTRZJIU
      RUSZRZYOYTJVHYHSSUOVCZYGUUHYFCUUGJCUUGIVIUSUPZVDUUGMUUGUUJVEVFZVGVJZUUGHI
      YOYTTJPYTVKZUUGVKZVLVMSYORZYHSSUPYOSVNVOVTVPZVQVRYHJYTYOVSUHRZUUDYHUUFUUH
      UUQUUIUULUUGHIYOYTTJPUUMUUNWAVMYTYOJSVTHURWBVNWCWDWEYHYPYTRZYSUFUFZYLJYPG
      FUHZUIZUAYPEUAUBWFYKUUTJYJYPGFWGVBUUSYPYTEYHUURYSWHOWIYHUURYSUVAYHUURUFZU
      VAYSUVBUUTYRJUVBUUTYRGHWJUSZWKUHYRUVBYPUUGHFUVCYOYTTGIPUUNUUMUVBSSUOVCZYH
      UURUKZUVBCUUGGUUKYFYIYGUURYNWLWMZNUVCVKZWNUVBUCYOYPYPUVCHWOUSZUPZGTTTUVDU
      VBYOYTGVHZYOUVIGVHZUVBUUFGUUGRUVJUVDUVFUUGHIYOYTTGPUUMUUNVLVMUVBUVIYTWPUD
      UGZGUSZUVIRZUDYOWQUVJUVKXKUVBUVHYTYFUVHYTRZYGUURYFHWRRZUVOHWSZYTHUVHUUMUV
      HVKZWTWDWLXLUVBUVNUDYOUVBUVLYORZUFZUVMSSHYOXAUHZUSZUSZUVIUVSUVMUWCUIUVBUV
      SUVLSGUWBGUWBUIUVSQVQUVLSXBXCVJUVTUWCUVHUIUWCUVIRUVTHUWAUVHYOSUETUWAVKYFY
      GUURUVSXDUVTSSUOVCUUOUVTUUPVQUVRXEUWCUVHSUWBWBXFXGXHXIYOUDGUVIYTXJVMXMYPT
      RUVBUBXNVQZUWDUCUGZUVIRZUVBYPUWEUVCUHYPUVHUVCUHYPUWFUWEUVHYPUVCUWEUVHXOXP
      UVBYTHUVCUVHYPUUMUVGUVRYFUVPYGUURUVQWLUVEXQXRXSXTVBYAYBWEYCABCDFUAEJGKLYD
      YE $.
  $}

  ${
    $d W a b l x y $.  $d K a b l x y $.  $d B a b x y $.
    0prjspn.w $e |- W = ( K freeLMod ( 0 ... 0 ) ) $.
    0prjspn.b $e |- B = ( ( Base ` W ) \ { ( 0g ` W ) } ) $.
    $( A zero-dimensional projective space has only 1 point.  (Contributed by
       Steven Nguyen, 9-Jun-2023.) $)
    0prjspn $p |- ( K e. DivRing -> ( 0 PrjSpn K ) = { B } ) $=
      ( vx vy vl wcel cc0 co cv wa cfv wceq cbs eqid cvv wbr adantr cdr cprjspn
      va vb cvsca wrex copab cqs csca csn cn0 0nn0 prjspnval2 mpan ovex frlmsca
      cfz mpan2 fveq2d rexeqdv anbi2d opabbidv qseq2d cuvc clmod clvec frlmlvec
      lveclmod 0prjspnrel breqdi adantrr prjspersym syl2an2r prjspertr syl12anc
      syl adantrl wer prjsper 0prjspnlem qsalrel 3eqtrd ) BUAIZJBUBKZAFLZAIGLZA
      IMZWEHLWFCUENZKOZHBPNZUFZMZFGUGZUHZAWGWIHCUINZPNZUFZMZFGUGZUHAUJJUKIWCWDW
      NOULFGAWMWJWHBJCHWMQZDEWJQZWHQZUMUNWCWMWSAWCWLWRFGWCWKWQWGWCWIHWJWPWCBWOP
      WCJJUQKZRIZBWOOJJUQUOZBCXCUARDUPURUSUTVAVBZVCWCUCUDAWSJBXCVDKNZWCUCLZAIZU
      DLZAIZMZMCVEIZXHXGWSSZXGXJWSSZXHXJWSSWCXMXLWCCVFIZXMWCXDXPXEBCXCRDVGURZCV
      HVPTWCXIXNXKWCXIMWMWSXHXGWCWMWSOZXIXFTFGAWMWJWHXGBCXHHWTEXBXADXGQZVIVJVKW
      CXKXOXIWCXPXKXJXGWSSXOXQWCXKMWMWSXJXGWCXRXKXFTFGAWMWJWHXGBCXJHWTEXBXADXSV
      IVJFGAWSWOWHWPCXJXGHWSQZEWOQZXBWPQZVLVMVQFGAWSWOWHWPCXHXGXJHXTEYAXBYBVNVO
      WCXPAWSVRXQFGAWSWOWHWPCHXTEYAXBYBVSVPAXGBCEDXSVTWAWB $.
  $}

  $(
    TODO: The proof is that <. a , b , c , ... >. has either a = 0 or a =/= 0.
    Since <. 0 , b , c , ... >. .~ <. 0 , nb, nc , ... >., the case a = 0
    corresponds to the (n-1)-dimensional projective space.  When a =/= 0, there
    is <. a , b , c , ... >. .~ <. 1 , b/a, c/a, ... >.  Since the later terms
    are irreducible it corresponds to all (n-1)-tuples of ( Base ` K ) which is
    equivalent to the construction of an affine space.  Note that the closest
    definition to affine space so far seems to be ~ df-ehl , which is specific
    to reals.

    It would be nice to use ~ df-tcph and related theorems to easily
    standardize vectors to a length (norm) of one, but such definitions require
    the scalars to be a subset of the complex numbers.  While these theorems
    may ultimately be only used by subsets of the complex numbers, intermediate
    theorems without such a hypothesis are possible.

    The most relevant theorem for this seems to be ~ f1oun , but due to the
    definition of ordered pairs it is possible for a point in the affine space
    to be equal to a point in the projective space.  It seems the closest
    theorem possible is something like:

    prjspnenm1.f $e |- F = ??? $.
    prjspnenm1.g $e |- G = ??? $.
    @( The canonical bijection from an n-dimensional projective K-space onto
       the disjoint union of the n-dimensional affine K-space and the
       (n-1)-dimensional projective space (its "hypersurface at infinity").
       (Contributed by SN, ??-???-202?.) @)
    prjspnf1om1 @p |- ( ( N e. NN /\ K e. DivRing ) ->
      ( F u. G ) : ( N PrjSpn K ) -1-1-onto-> (
        ( ( K ^m ( 0 ... ( N - 1 ) ) ) |_| ( ( N - 1 ) PrjSpn K ) ) ) @=
      ? $.

    The actual necessity is to define a modular form.  The definition goes as
    follows: consider an ` N ` -variable polynomial ` P ` whose terms _have the
    same degree_.  Crucially, given a zero (an n-dimensional vector where ` P `
    applied to the vector gives zero), all scalar multiples of that zero are
    also zeroes.  So one can define the zeroes in _projective_ ` N ` -space
    for an ` N ` -variable homogeneous polynomial.

    A ` N - 1 ` -variable non-homogeneous polynomial ` Q ` can be converted to
    an ` N ` -variable homogeneous polynomial ` P ` by adding an argument ` a `
    and defining `` ( P ` <. a , x , y , z , ... >. ) `` =
    `` ( ( a ^ ( N - 1 ) ) .s ( Q ` <. x / a , y / a , z / a , ... >. ) ) `` .

    See Wikipedia _homogeneous polynomial_, _homogeneous function_, and
    _algebraic variety_ as well as ~ df-mhp.
  $)

  $c PrjCrv $.

  $( Extend class notation with the projective curve function. $)
  cprjcrv $a class PrjCrv $.

  ${
    $d n k f p $.
    $( Define the projective curve function.  This takes a homogeneous
       polynomial and outputs the homogeneous coordinates where the polynomial
       evaluates to zero (the "zero set").  (In other words, scalar multiples
       are collapsed into the same projective point.  See ~ mhphf4 and
       ~ prjspvs ).  (Contributed by SN, 23-Nov-2024.) $)
    df-prjcrv $a |- PrjCrv = ( n e. NN0 , k e. Field |->
       ( f e. U. ran ( ( 0 ... n ) mHomP k ) |->
          { p e. ( n PrjSpn k ) |
             ( ( ( ( 0 ... n ) eval k ) ` f ) " p ) = { ( 0g ` k ) } } ) ) $.
  $}

  ${
    $d N n k f p $.  $d K n k f p $.  $d .0. n k $.  $d E n k $.  $d P n k p $.
    $d H n k f $.
    prjcrvfval.h $e |- H = ( ( 0 ... N ) mHomP K ) $.
    prjcrvfval.e $e |- E = ( ( 0 ... N ) eval K ) $.
    prjcrvfval.p $e |- P = ( N PrjSpn K ) $.
    prjcrvfval.0 $e |- .0. = ( 0g ` K ) $.
    prjcrvfval.n $e |- ( ph -> N e. NN0 ) $.
    prjcrvfval.k $e |- ( ph -> K e. Field ) $.
    $( Value of the projective curve function.  (Contributed by SN,
       23-Nov-2024.) $)
    prjcrvfval $p |- ( ph -> ( N PrjCrv K ) =
      ( f e. U. ran H |-> { p e. P | ( ( E ` f ) " p ) = { .0. } } ) ) $=
      ( co cv cfv wceq cmhp cn0 wcel cfield cprjcrv crn cuni cima csn crab cmpt
      vn vk cc0 cfz cevl c0g cprjspn wa oveq2 oveq12 sylan eqtr4di rneqd unieqd
      oveqan12d fveq1d imaeq1d fveq2 adantl sneqd rabeqbidv mpteq12dv df-prjcrv
      id eqeq12d ovexi rnex uniex mptex ovmpoa syl2anc ) AGUAUBFUCUBGFUDPCEUEZU
      FZCQZDRZIQZUGZHUHZSZIBUIZUJZSNOUKULGFUAUCCUMUKQZUNPZULQZTPZUEZUFZWDWMWNUO
      PZRZWFUGZWNUPRZUHZSZIWLWNUQPZUIZUJWKUDWLGSZWNFSZURZCWQXEWCWJXHWPWBXHWOEXH
      WOUMGUNPZFTPZEXFWMXISXGWOXJSWLGUMUNUSZWMXIWNFTUTVAJVBVCVDXHXCWIIXDBXHXDGF
      UQPBWLGWNFUQUTLVBXHWTWGXBWHXHWSWEWFXHWDWRDXHWRXIFUOPDXFXGWMXIWNFUOXKXGVNV
      EKVBVFVGXHXAHXGXAHSXFXGXAFUPRHWNFUPVHMVBVIVJVOVKVLCULUKIVMCWCWJWBEEXIFTJV
      PVQVRVSVTWA $.

    $d .0. f $.  $d F f p $.  $d E f $.  $d P f $.  $d ph f $.
    prjcrvval.f $e |- ( ph -> F e. U. ran H ) $.
    $( Value of the projective curve function.  (Contributed by SN,
       23-Nov-2024.) $)
    prjcrvval $p |- ( ph ->
      ( ( N PrjCrv K ) ` F ) = { p e. P | ( ( E ` F ) " p ) = { .0. } } ) $=
      ( vf cv cfv wceq cima csn crab crn cuni cprjcrv cvv fveq2 imaeq1d rabbidv
      co eqeq1d prjcrvfval wcel cprjspn ovexi rabex a1i fvmptd4 ) AQDQRZCSZIRZU
      AZHUBZTZIBUCDCSZVBUAZVDTZIBUCZEUDUEGFUFUKUGUTDTZVEVHIBVJVCVGVDVJVAVFVBUTD
      CUHUIULUJABQCEFGHIJKLMNOUMPVIUGUNAVHIBBGFUOLUPUQURUS $.
  $}

  ${
    $d K k p $.  $d N k p $.  $d P p $.  $d ph p $.  $d N h $.  $d .0. p $.
    prjcrv0.y $e |- Y = ( ( 0 ... N ) mPoly K ) $.
    prjcrv0.0 $e |- .0. = ( 0g ` Y ) $.
    prjcrv0.p $e |- P = ( N PrjSpn K ) $.
    prjcrv0.n $e |- ( ph -> N e. NN0 ) $.
    prjcrv0.k $e |- ( ph -> K e. Field ) $.
    $( The "curve" (zero set) corresponding to the zero polynomial contains all
       coordinates.  (Contributed by SN, 23-Nov-2024.) $)
    prjcrv0 $p |- ( ph -> ( ( N PrjCrv K ) ` .0. ) = P ) $=
      ( vp vh vk co cfv wceq eqid wcel cvv cprjcrv cc0 cfz cevl cv cima c0g csn
      crab cmhp crn cuni fvssunirn ccnv cn cfn cn0 cmap ovexd fldcrngd crnggrpd
      cxp mpl0 mhp0cl eqeltrd sselid prjcrvval cbs ccrg adantr evl0 imaeq1d cin
      wa wne wss cpw cfrlm cdif flddrngd prjspnssbas cfsupp wbr frlmbas syl2anc
      c0 cfield ssrab2 eqsstrrdi ssdifssd sspwd sstrd sselda elpwid sseqin2 cdr
      sylib simpr prjspnn0 eqnetrd xpima2 syl eqtrd rabeqcda ) AFDCUAOPFUBDUCOZ
      CUDOZPZLUEZUFZCUGPZUHZQZLBUIBABXFFXECUJOZCDXJLXMRZXFRZIXJRZJKADXMPZXMUKUL
      FXMDUMAFMUEUNUOUFUPSMUQXEUROUIZXKVBXQAXRECMXEXJTFGXRRZXPHAUBDUCUSZACACKUT
      ZVAZVCAXRCMXMXEDTXJXNXPXSXTYBJVDVEVFVGAXLLBAXHBSZVNZXICVHPZXEUROZXKVBZXHU
      FZXKYDXGYGXHYDYEXFCXEXJTEFXOYERZGXPHYDUBDUCUSACVISYCYAVJVKVLYDYFXHVMZWFVO
      YHXKQYDYJXHWFYDXHYFVPYJXHQYDXHYFABYFVQZXHABCXEVROZVHPZYLUGPUHZVSZVQYKAYOB
      CDYLIYLRZYORZJACKVTZWAAYOYFAYMYFYNAYMNUEXJWBWCZNYFUIZYFACWGSXETSYTYMQKXTY
      TCNYLXEYEWGTXJYPYIXPYTRWDWEYSNYFWHWIWJWKWLWMWNXHYFWOWQYDXHYOBCDYLIYPYQADU
      QSYCJVJACWPSYCYRVJAYCWRWSWTYFXKXHXAXBXCXDXC $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Basic reductions for Fermat's Last Theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( TODO:
    @( Lemma for ~ dffltz .  If two or more terms are negative, then negating
       every term produces a solution with at most one negative term.
       (Contributed by Steven Nguyen, 6-Jun-2023.) @)
    dffltzlem @p |- ( n e. ( ZZ>= ` 3 ) -> (
      E. a e. ( ZZ \ { 0 } ) E. b e. ( ZZ \ { 0 } ) E. c e. ( ZZ \ { 0 } )
      ( ( a ^ n ) + ( b ^ n ) ) = ( c ^ n ) ->
      E. x e. NN E. y e. ( ZZ \ { 0 } ) E. z e. NN
      ( ( x ^ n ) + ( y ^ n ) ) = ( z ^ n ) ) ) @=
      ? @.
  $)

  ${
    $d n a b c x y z $.
    $( Fermat's Last Theorem (FLT) for nonzero integers is equivalent to the
       original scope of natural numbers.  The backwards direction takes
       ` ( a ^ n ) + ( b ^ n ) = ( c ^ n ) ` , and adds the negative of any
       negative term to both sides, thus creating the corresponding equation
       with only positive integers.  There are six combinations of negativity,
       so the proof is particularly long.  (Contributed by Steven Nguyen,
       27-Feb-2023.) $)
    dffltz $p |- ( A. n e. ( ZZ>= ` 3 ) A. x e. NN A. y e. NN A. z e. NN
      ( ( x ^ n ) + ( y ^ n ) ) =/= ( z ^ n ) <->
      A. n e. ( ZZ>= ` 3 ) A. a e. ( ZZ \ { 0 } ) A. b e. ( ZZ \ { 0 } )
      A. c e. ( ZZ \ { 0 } ) ( ( a ^ n ) + ( b ^ n ) ) =/= ( c ^ n ) ) $=
      ( cexp co caddc cn cz cc0 wceq wcel wa oveq1d 3syl 3eqtr4d adantl cv wral
      wne c3 cuz cfv csn cdif wrex wn c2 cdiv cabs clt cneg oveq1 eqeq1d oveq2d
      wbr cif eqeq2d simp-4r eldifi eldifsni jca nnabscl simp-6r eldifad simplr
      elnnz sylanbrc ad6antlr negn0nposznnd simp-7r ifclda ad7antlr ifcld simpr
      simpllr simp-5r ad5antlr syl syl2anc zred eluz3nn ad7antr nnnn0d reexpcld
      oexpreposd mpbid mpbird simp-8r wo neneqd cc wb mtbird mtbid ioran lttrid
      zcn eqcomd cr absresq abscld recnd cn0 a1i expmuld oveq12d iftrue simp-8l
      cmin sylancl oexpneg syl3anc expcld negcld addcomd negsubd 3eqtrd ad8antr
      2nn addcanad iffalse pm2.61dan eqtr4d negeqd negdid expclzd rexlimdva nne
      eqtrd bicomi rexbii rexnal bitri wss ax-mp neeq1d addgt0d readdcld expeq0
      breqtrd 0red eluzelz expne0d lt2addd 00id breqtrdi ltnsymd breq2d simp-5l
      cmul 2nn0 nncn 2cnd 2ne0 divcan2d cdvds nndivdvds nnnn0 mvrraddd mvlraddd
      subcld pncan3d addcld negidd addassd addlidd pncand 3rspcedvdw rexlimdva2
      3eqtr3d eqtr3d negnegd reximia 3imtr3i con4i wi dfn2 nn0ssz ssdif eqsstri
      ssel ss2ralv imim12d ralimdv2 neeq2d cbvral3vw sylib ralimi impbii ) AUAZ
      DUAZHIZBUAZUWOHIZJIZCUAZUWOHIZUCZCKUBZBKUBZAKUBZDUDUEUFZUBZEUAZUWOHIZFUAZ
      UWOHIZJIZGUAZUWOHIZUCZGLMUGZUHZUBZFUXQUBZEUXQUBZDUXFUBZUYAUXGUXLUXNNZGUXQ
      UIZFUXQUIZEUXQUIZDUXFUIZUWSUXANZCKUIZBKUIZAKUIZDUXFUIZUYAUJZUXGUJZUYEUYJD
      UXFUWOUXFOZUYDUYJEUXQUYNUXHUXQOZPZUYCUYJFUXQUYPUXJUXQOZPZUYBUYJGUXQUYRUXM
      UXQOZPZUYBPZUYGUWOUKULIZKOZUXHUMUFZMUXHUNUSZMUXJUNUSZUXHMUXMUNUSZUXJUOZUX
      HUTZUTZVUFVUGUXHUOZUXJUTZVUKUTZUTZUTZUWOHIZUWRJIZUXANVUPVUCUXJUMUFZVUEVUF
      UXJVUGUXMUXMUOZUTZUTZVUFVUTVUHUTZUTZUTZUWOHIZJIZUXANVVFVUCUXMUMUFZVUEVUFU
      XMVUGUXHVUHUTZUTZVUFVUGUXJVUKUTZVUSUTZUTZUTZUWOHIZNZABCVUOVVDVVMKKKUWNVUO
      NZUWSVUQUXAVVPUWPVUPUWRJUWNVUOUWOHUPQUQUWQVVDNZVUQVVFUXAVVQUWRVVEVUPJUWQV
      VDUWOHUPURUQUWTVVMNUXAVVNVVFUWTVVMUWOHUPVAVUAVUCVUDVUNKVUAUYOUXHLOZUXHMUC
      ZPVUDKOUYNUYOUYQUYSUYBVBUYOVVRVVSUXHLUXPVCZUXHLMVDZVEUXHVFRVUAVUEVUJVUMKV
      UAVUEPZVUFUXHVUIKVWBVUFPZVVRVUEUXHKOZVWCUXHLUXPUYNUYOUYQUYSUYBVUEVUFVGVHV
      UAVUEVUFVIUXHVJZVKVWBVUFUJZPZVUGVUHUXHKVWGVUGPZUXJUYQUXJMUCZUYPUYSUYBVUEV
      WFVUGUXJLMVDZVLVWBVWFVUGVIUYQUXJLOZUYPUYSUYBVUEVWFVUGUXJLUXPVCZVLVMVWGVUG
      UJZPZVVRVUEVWDVWNUXHLUXPUYNUYOUYQUYSUYBVUEVWFVWMVNVHVUAVUEVWFVWMVSVWEVKVO
      VOVUAVUEUJZPZVUFVULVUKKVWPVUFPZVUGVUKUXJKVWQVUGPZUXHUYOVVSUYNUYQUYSUYBVWO
      VUFVUGVWAVPVUAVWOVUFVUGVSUYOVVRUYNUYQUYSUYBVWOVUFVUGVVTVPVMVWQVWMPZVWKVUF
      UXJKOZVWSUXJLUXPUYPUYQUYSUYBVWOVUFVWMVGVHVWPVUFVWMVIUXJVJZVKVOVWPVWFPZUXH
      UYOVVSUYNUYQUYSUYBVWOVWFVWAVLVUAVWOVWFVIUYOVVRUYNUYQUYSUYBVWOVWFVVTVLVMVO
      VOVQVUAVUCVURVVCKVUAUYQVWKVWIPVURKOUYPUYQUYSUYBVSUYQVWKVWIVWLVWJVEUXJVFRV
      UAVUEVVAVVBKVWBVUFUXJVUTKVWCVWKVUFVWTVWCUXJLUXPUYPUYQUYSUYBVUEVUFVTVHVWBV
      UFVRVXAVKVWGVUGUXMVUSKVWHUXMLOZVUGUXMKOZVWHUXMLUXPUYRUYSUYBVUEVWFVUGVTVHV
      WGVUGVRUXMVJZVKVWNUXMUYSUXMMUCZUYRUYBVUEVWFVWMUXMLMVDZWAVWGVWMVRUYSVXCUYR
      UYBVUEVWFVWMUXMLUXPVCZWAVMVOVOVWPVUFVUTVUHKVWQVUGUXMVUSKVWRVXCVUGVXDVWRUX
      MLUXPUYRUYSUYBVWOVUFVUGVTVHVWQVUGVRVXEVKVWSUXMUYSVXFUYRUYBVWOVUFVWMVXGWAV
      WQVWMVRUYSVXCUYRUYBVWOVUFVWMVXHWAVMVOVXBUXJUYQVWIUYPUYSUYBVWOVWFVWJWAVWPV
      WFVRUYQVWKUYPUYSUYBVWOVWFVWLWAVMVOVOVQVUAVUCVVGVVLKVUAVUCPZVXCVXFVVGKOVXI
      UXMLUXPUYRUYSUYBVUCVSZVHZVXIUYSVXFVXJVXGWBUXMVFWCVUAVUCUJZPZVUEVVIVVKKVXM
      VUEPZVUFUXMVVHKVXNVUFPZVXCVUGVXDVXOUXMLUXPUYRUYSUYBVXLVUEVUFVTVHZVXOVUGMU
      XNUNUSZVXOMUXLUXNUNVXOUXIUXKVXOUXHUWOVXOUXHVXOUXHLUXPUYNUYOUYQUYSUYBVXLVU
      EVUFVNVHWDZVXOUWOUYNUWOKOZUYOUYQUYSUYBVXLVUEVUFUWOWEZWFZWGZWHVXOUXJUWOVXO
      UXJVXOUXJLUXPUYPUYQUYSUYBVXLVUEVUFVGVHWDZVYBWHVXOVUEMUXIUNUSZVXMVUEVUFVIV
      XOUWOUXHVXRVYAVUAVXLVUEVUFVSZWIWJVXOVUFMUXKUNUSZVXNVUFVRVXOUWOUXJVYCVYAVY
      EWIWJUUAUYTUYBVXLVUEVUFVBZUUDVXOUWOUXMVXOUXMVXPWDVYAVYEWIWKVXEVKVXNVWFPZV
      UGUXHVUHKVYHVUGPZVVRVUEVWDVYIUXHLUXPUYNUYOUYQUYSUYBVXLVUEVWFVUGWLZVHVXMVU
      EVWFVUGVSVWEVKVYHVWMPZUXJVYKUYQVWIUYPUYQUYSUYBVXLVUEVWFVWMVNZVWJWBVXNVWFV
      WMVIVYKUXJLUXPVYLVHVMVOVOVXMVWOPZVUFVVJVUSKVYMVUFPZVUGUXJVUKKVYNVUGPZVWKV
      UFVWTVYOUXJLUXPUYPUYQUYSUYBVXLVWOVUFVUGVNZVHVYMVUFVUGVIVXAVKVYNVWMPZUXHVY
      QUYOVVSUYNUYOUYQUYSUYBVXLVWOVUFVWMWLZVWAWBVXMVWOVUFVWMVSVYQUXHLUXPVYRVHVM
      VOVYMVWFPZUXMVYSUYSVXFUYRUYSUYBVXLVWOVWFVTZVXGWBVYSVUGVXQVYSVXQMUXLUNUSVY
      SUXLMVYSUXIUXKVYSUXHUWOVYSUXHVYSUXHLUXPUYNUYOUYQUYSUYBVXLVWOVWFVNZVHWDZVY
      SUWOUYNVXSUYOUYQUYSUYBVXLVWOVWFVXTWFZWGZWHZVYSUXJUWOVYSUXJVYSUXJLUXPUYPUY
      QUYSUYBVXLVWOVWFVGZVHWDZWUDWHZUUBVYSUUEZVYSUXLMMJIMUNVYSUXIUXKMMWUEWUHWUI
      WUIVYSUXIMUNUSUXIMNZVYDWMUJZVYSWUJUJVYDUJWUKVYSWUJUXHMNZVYSUYOWULUJWUAUYO
      UXHMVWAWNWBVYSUXHWOOZVXSWUJWULWPVYSUYOVVRWUMWUAVVTUXHXAZRZWUCUXHUWOUUCWCW
      QVYSVUEVYDVXMVWOVWFVIVYSUWOUXHWUBWUCVUAVXLVWOVWFVSZWIWRWUJVYDWSVKVYSUXIMW
      UEWUIWTWKVYSUXKMUNUSUXKMNZVYFWMUJZVYSWUQUJVYFUJWURVYSUXKMVYSUXJUWOVYSUYQV
      WKUXJWOOZWUFVWLUXJXAZRZVYSUYQVWIWUFVWJWBZUYNUWOLOUYOUYQUYSUYBVXLVWOVWFUDU
      WOUUFWFZUUGWNVYSVUFVYFVYMVWFVRVYSUWOUXJWUGWUCWUPWIWRWUQVYFWSVKVYSUXKMWUHW
      UIWTWKUUHUUIUUJUUKVYSUXNUXLMUNVYSUXLUXNUYTUYBVXLVWOVWFVBZXBUULWQVYSUWOUXM
      VYSUXMVYSUXMLUXPVYTVHZWDWUCWUPWIWQWVEVMVOVOVOVUAVUCVVOVXIVUDUWOHIZVURUWOH
      IZJIZVVGUWOHIZVVFVVNVXIUXLUXNWVHWVIUYTUYBVUCVIVXIWVFUXIWVGUXKJVXIVUDUKVUB
      UUNIZHIZUXHWVJHIZWVFUXIVXIVUDUKHIZVUBHIUXHUKHIZVUBHIWVKWVLVXIWVMWVNVUBHVX
      IUXHXCOWVMWVNNVXIUXHVXIUXHLUXPUYNUYOUYQUYSUYBVUCVTZVHWDUXHXDWBQVXIVUDUKVU
      BVXIVUDVXIUXHVXIUYOVVRWUMWVOVVTWUNRZXEXFVXIVUBVUAVUCVRWGZUKXGOVXIUUOXHZXI
      VXIUXHUKVUBWVPWVQWVRXISVXIUWOWVJVUDHVXIWVJUWOVXIUWOUKVXIUYNVXSUWOWOOUYNUY
      OUYQUYSUYBVUCUUMVXTUWOUUPRVXIUUQUKMUCVXIUURXHUUSXBZURVXIUWOWVJUXHHWVSURSV
      XIVURWVJHIZUXJWVJHIZWVGUXKVXIVURUKHIZVUBHIUXJUKHIZVUBHIWVTWWAVXIWWBWWCVUB
      HVXIUXJXCOWWBWWCNVXIUXJVXIUXJLUXPUYPUYQUYSUYBVUCVBZVHWDUXJXDWBQVXIVURUKVU
      BVXIVURVXIUXJVXIUYQVWKWUSWWDVWLWUTRZXEXFWVQWVRXIVXIUXJUKVUBWWEWVQWVRXISVX
      IUWOWVJVURHWVSURVXIUWOWVJUXJHWVSURSXJVXIVVGWVJHIZUXMWVJHIZWVIUXNVXIVVGUKH
      IZVUBHIUXMUKHIZVUBHIWWFWWGVXIWWHWWIVUBHVXIUXMXCOWWHWWINVXIUXMVXKWDUXMXDWB
      QVXIVVGUKVUBVXIVVGVXIUXMVXIUYSVXCUXMWOOZVXJVXHUXMXAZRZXEXFWVQWVRXIVXIUXMU
      KVUBWWLWVQWVRXISVXIUWOWVJVVGHWVSURVXIUWOWVJUXMHWVSURSSVUCVVFWVHNVUAVUCVUP
      WVFVVEWVGJVUCVUOVUDUWOHVUCVUDVUNXKQVUCVVDVURUWOHVUCVURVVCXKQXJTVUCVVNWVIN
      VUAVUCVVMVVGUWOHVUCVVGVVLXKQTSVXMVUNUWOHIZVVCUWOHIZJIZVVLUWOHIZVVFVVNVXMV
      UEWWOWWPNVXNVUJUWOHIZVVAUWOHIZJIZVVIUWOHIZWWOWWPVXNVUFWWSWWTNVXOUXLUXNWWS
      WWTVYGVUFWWSUXLNVXNVUFWWQUXIWWRUXKJVUFVUJUXHUWOHVUFUXHVUIXKQVUFVVAUXJUWOH
      VUFUXJVUTXKQXJTVUFWWTUXNNVXNVUFVVIUXMUWOHVUFUXMVVHXKQTSVYHVUIUWOHIZVUTUWO
      HIZJIZVVHUWOHIZWWSWWTVYHVUGWXCWXDNVYIVUHUWOHIZUXNJIZUXIWXCWXDVYIWXFUXKUOZ
      UXNJIZUXNUXKXMIZUXIVYIWXEWXGUXNJVYIWUSVXSUKUWOUUTUSZUJZWXEWXGNZVYIUYQVWKW
      USUYPUYQUYSUYBVXLVUEVWFVUGVNVWLWUTRZVYIUYNVXSUYNUYOUYQUYSUYBVXLVUEVWFVUGX
      LZVXTWBZVYIWXJVUCVUAVXLVUEVWFVUGVBVYIVXSUKKOZWXJVUCWPZWXOYCUWOUKUVAZXNWQU
      XJUWOXOZXPQVYIWXHUXNWXGJIZWXIVYIWXGUXNVYIUXKVYIUXJUWOWXMVYIUYNVXSUWOXGOZW
      XNVXTUWOUVBZRZXQZXRVYIUXMUWOVYIUYSVXCWWJUYRUYSUYBVXLVUEVWFVUGVGVXHWWKRWYC
      XQZXSVYIUXNUXKWYEWYDXTYMVYIUXNUXIUXKVYIUXHUWOVYIUYOVVRWUMVYJVVTWUNRWYCXQW
      YDVYIUXLUXNUYTUYBVXLVUEVWFVUGVTXBUVCYAVUGWXCWXFNVYHVUGWXAWXEWXBUXNJVUGVUI
      VUHUWOHVUGVUHUXHXKQVUGVUTUXMUWOHVUGUXMVUSXKQZXJTVUGWXDUXINVYHVUGVVHUXHUWO
      HVUGUXHVUHXKQTSVYKUXIVUSUWOHIZJIZWXEWXCWXDVYKUXIUXNUOZJIZWXGWYHWXEVYKWYJU
      XIUXNXMIZWXGVYKUXIUXNVYKUXHUWOVYKUYOVVRWUMUYNUYOUYQUYSUYBVXLVUEVWFVWMWLVV
      TWUNRVYKUWOUYNVXSUYOUYQUYSUYBVXLVUEVWFVWMVXTYBZWGZXQZVYKUXMUWOVYKUYSVXCWW
      JUYRUYSUYBVXLVUEVWFVWMVGVXHWWKRZWYMXQZXTVYKUXNWYKWXGWYPVYKUXIUXNWYNWYPUVE
      VYKUXKVYKUXJUWOVYKUYQVWKWUSVYLVWLWUTRZWYMXQZXRVYKUXIWXIUXNWYKJIWXTVYKUXIU
      XKUXNWYNWYRUYTUYBVXLVUEVWFVWMVTUVDVYKUXNUXIWYPWYNUVFVYKUXNUXKWYPWYRXTSYDY
      MVYKWYGWYIUXIJVYKWWJVXSWXKWYGWYINZWYOWYLVYKWXJVUCVUAVXLVUEVWFVWMVBVYKVXSW
      XPWXQWYLYCWXRXNWQZUXMUWOXOZXPURVYKWUSVXSWXKWXLWYQWYLWYTWXSXPSVWMWXCWYHNVY
      HVWMWXAUXIWXBWYGJVWMVUIUXHUWOHVUGVUHUXHYEQVWMVUTVUSUWOHVUGUXMVUSYEQZXJTVW
      MWXDWXENVYHVWMVVHVUHUWOHVUGUXHVUHYEQTSYFVWFWWSWXCNVXNVWFWWQWXAWWRWXBJVWFV
      UJVUIUWOHVUFUXHVUIYEQVWFVVAVUTUWOHVUFUXJVUTYEQXJTVWFWWTWXDNVXNVWFVVIVVHUW
      OHVUFUXMVVHYEQTSYFVUEWWOWWSNVXMVUEWWMWWQWWNWWRJVUEVUNVUJUWOHVUEVUJVUMXKQV
      UEVVCVVAUWOHVUEVVAVVBXKQXJTVUEWWPWWTNVXMVUEVVLVVIUWOHVUEVVIVVKXKQTSVYMVUM
      UWOHIZVVBUWOHIZJIZVVKUWOHIZWWOWWPVYMVUFXUEXUFNVYNVULUWOHIZWXBJIZVVJUWOHIZ
      XUEXUFVYNVUGXUHXUINVYOVUKUWOHIZUXNJIZUXKXUHXUIVYOXUKUXIUOZUXNJIZUXKVYOXUJ
      XULUXNJVYOWUMVXSWXKXUJXULNZVYOUYOVVRWUMUYNUYOUYQUYSUYBVXLVWOVUFVUGWLVVTWU
      NRZUYNVXSUYOUYQUYSUYBVXLVWOVUFVUGVXTYBZVYOWXJVUCVUAVXLVWOVUFVUGVBVYOVXSWX
      PWXQXUPYCWXRXNWQUXHUWOXOZXPQVYOUXIXUMUXKVYOUXHUWOXUOVYOUWOXUPWGZXQZVYOXUL
      UXNVYOUXIXUSXRZVYOUXMUWOVYOUYSVXCWWJUYRUYSUYBVXLVWOVUFVUGVGVXHWWKRXURXQZU
      VGVYOUXJUWOVYOUYQVWKWUSVYPVWLWUTRXURXQVYOUXIXUMJIZUXNUXLVYOUXIXULJIZUXNJI
      MUXNJIXVBUXNVYOXVCMUXNJVYOUXIXUSUVHQVYOUXIXULUXNXUSXUTXVAUVIVYOUXNXVAUVJU
      VNUYTUYBVXLVWOVUFVUGVTYGYDYMVUGXUHXUKNVYNVUGXUGXUJWXBUXNJVUGVULVUKUWOHVUG
      VUKUXJXKQWYFXJTVUGXUIUXKNVYNVUGVVJUXJUWOHVUGUXJVUKXKQTSVYQUXKWYGJIZXUJXUH
      XUIVYQWXHUOZXULXVDXUJVYQWXHUXIVYQWXHWXTWXIUXIVYQWXGUXNVYQUXKVYQUXJUWOVYQU
      YQVWKWUSUYPUYQUYSUYBVXLVWOVUFVWMVNVWLWUTRVYQUYNVXSWYAUYNUYOUYQUYSUYBVXLVW
      OVUFVWMXLZVXTWYBRZXQZXRZVYQUXMUWOVYQUYSVXCWWJUYRUYSUYBVXLVWOVUFVWMVGVXHWW
      KRZXVGXQZXSVYQUXNUXKXVKXVHXTVYQUXLUXKXMIWXIUXIVYQUXLUXNUXKXMUYTUYBVXLVWOV
      UFVWMVTQVYQUXIUXKVYQUXHUWOVYQUYOVVRWUMVYRVVTWUNRZXVGXQXVHUVKUVOYAYHVYQUXK
      WYIJIWXGUOZWYIJIXVDXVEVYQUXKXVMWYIJVYQXVMUXKVYQUXKXVHUVPXBQVYQWYGWYIUXKJV
      YQWWJVXSWXKWYSXVJVYQUYNVXSXVFVXTWBZVYQWXJVUCVUAVXLVWOVUFVWMVBVYQVXSWXPWXQ
      XVNYCWXRXNWQZXUAXPURVYQWXGUXNXVIXVKYISVYQWUMVXSWXKXUNXVLXVNXVOXUQXPSVWMXU
      HXVDNVYNVWMXUGUXKWXBWYGJVWMVULUXJUWOHVUGVUKUXJYEQXUBXJTVWMXUIXUJNVYNVWMVV
      JVUKUWOHVUGUXJVUKYEQTSYFVUFXUEXUHNVYMVUFXUCXUGXUDWXBJVUFVUMVULUWOHVUFVULV
      UKXKQVUFVVBVUTUWOHVUFVUTVUHXKQXJTVUFXUFXUINVYMVUFVVKVVJUWOHVUFVVJVUSXKQTS
      VYSXUJWXEJIZWYGXUEXUFVYSUXLUOZWYIXVPWYGVYSUXLUXNWVDYHVYSXVPXULWXGJIXVQVYS
      XUJXULWXEWXGJVYSWUMVXSWXKXUNWUOWUCVYSWXJVUCWUPVYSVXSWXPWXQWUCYCWXRXNWQZXU
      QXPVYSWUSVXSWXKWXLWVAWUCXVRWXSXPXJVYSUXIUXKVYSUXHUWOWUOVYSUYOVVSWUAVWAWBW
      VCYJVYSUXJUWOWVAWVBWVCYJYIYGVYSWWJVXSWXKWYSVYSUYSVXCWWJVYTVXHWWKRWUCXVRXU
      AXPSVWFXUEXVPNVYMVWFXUCXUJXUDWXEJVWFVUMVUKUWOHVUFVULVUKYEQVWFVVBVUHUWOHVU
      FVUTVUHYEQXJTVWFXUFWYGNVYMVWFVVKVUSUWOHVUFVVJVUSYEQTSYFVWOWWOXUENVXMVWOWW
      MXUCWWNXUDJVWOVUNVUMUWOHVUEVUJVUMYEQVWOVVCVVBUWOHVUEVVAVVBYEQXJTVWOWWPXUF
      NVXMVWOVVLVVKUWOHVUEVVIVVKYEQTSYFVXLVVFWWONVUAVXLVUPWWMVVEWWNJVXLVUOVUNUW
      OHVUCVUDVUNYEQVXLVVDVVCUWOHVUCVURVVCYEQXJTVXLVVNWWPNVUAVXLVVMVVLUWOHVUCVV
      GVVLYEQTSYFUVLUVMYKYKUVQUYFUXTUJZDUXFUIUYLUYEXVSDUXFUYEUXSUJZEUXQUIXVSUYD
      XVTEUXQUYDUXRUJZFUXQUIXVTUYCXWAFUXQUYCUXOUJZGUXQUIXWAUYBXWBGUXQXWBUYBUXLU
      XNYLYNYOUXOGUXQYPYQYOUXRFUXQYPYQYOUXSEUXQYPYQYOUXTDUXFYPYQUYKUXEUJZDUXFUI
      UYMUYJXWCDUXFUYJUXDUJZAKUIXWCUYIXWDAKUYIUXCUJZBKUIXWDUYHXWEBKUYHUXBUJZCKU
      IXWEUYGXWFCKXWFUYGUWSUXAYLYNYOUXBCKYPYQYOUXCBKYPYQYOUXDAKYPYQYOUXEDUXFYPY
      QUVRUVSUXTUXEDUXFUXTUXOGKUBFKUBZEKUBZUXEKUXQYRZUXTXWHUVTKXGUXPUHZUXQUWAXG
      LYRXWJUXQYRUWBXGLUXPUWCYSUWDXWIUXSXWGEUXQKXWIVWDUYOUXSXWGKUXQUXHUWEUXOFGK
      UXQUWFUWGUWHYSUXOUXBUWPUXKJIZUXNUCUWSUXNUCEFGABCKKKUXHUWNNZUXLXWKUXNXWLUX
      IUWPUXKJUXHUWNUWOHUPQYTUXJUWQNZXWKUWSUXNXWMUXKUWRUWPJUXJUWQUWOHUPURYTUXMU
      WTNUXNUXAUWSUXMUWTUWOHUPUWIUWJUWKUWLUWM $.
  $}

  ${
    fltmul.s $e |- ( ph -> S e. CC ) $.
    fltmul.a $e |- ( ph -> A e. CC ) $.
    fltmul.b $e |- ( ph -> B e. CC ) $.
    fltmul.c $e |- ( ph -> C e. CC ) $.
    fltmul.n $e |- ( ph -> N e. NN0 ) $.
    fltmul.1 $e |- ( ph -> ( ( A ^ N ) + ( B ^ N ) ) = ( C ^ N ) ) $.
    $( A counterexample to FLT stays valid when scaled.  The hypotheses are
       more general than they need to be for convenience.  (There does not seem
       to be a standard term for Fermat or Pythagorean triples extended to any
       ` N e. NN0 ` , so the label is more about the context in which this
       theorem is used).  (Contributed by SN, 20-Aug-2024.) $)
    fltmul $p |- ( ph
       -> ( ( ( S x. A ) ^ N ) + ( ( S x. B ) ^ N ) ) = ( ( S x. C ) ^ N ) ) $=
      ( cexp co cmul caddc expcld adddid oveq2d mulexpd eqtr3d oveq12d 3eqtr4d
      ) AEFMNZBFMNZONZUDCFMNZONZPNZUDDFMNZONZEBONFMNZECONFMNZPNEDONFMNAUDUEUGPN
      ZONUIUKAUDUEUGAEFGKQABFHKQACFIKQRAUNUJUDOLSUAAULUFUMUHPAEBFGHKTAECFGIKTUB
      AEDFGJKTUC $.
  $}

  ${
    fltdiv.s $e |- ( ph -> S e. CC ) $.
    fltdiv.0 $e |- ( ph -> S =/= 0 ) $.
    fltdiv.a $e |- ( ph -> A e. CC ) $.
    fltdiv.b $e |- ( ph -> B e. CC ) $.
    fltdiv.c $e |- ( ph -> C e. CC ) $.
    fltdiv.n $e |- ( ph -> N e. NN0 ) $.
    fltdiv.1 $e |- ( ph -> ( ( A ^ N ) + ( B ^ N ) ) = ( C ^ N ) ) $.
    $( A counterexample to FLT stays valid when scaled.  The hypotheses are
       more general than they need to be for convenience.  (Contributed by SN,
       20-Aug-2024.) $)
    fltdiv $p |- ( ph
       -> ( ( ( A / S ) ^ N ) + ( ( B / S ) ^ N ) ) = ( ( C / S ) ^ N ) ) $=
      ( cexp co cdiv caddc expcld nn0zd expdivd expne0d divdird oveq12d 3eqtr4d
      oveq1d eqtr3d ) ABFNOZEFNOZPOZCFNOZUHPOZQOZDFNOZUHPOZBEPOFNOZCEPOFNOZQODE
      POFNOAUGUJQOZUHPOULUNAUGUJUHABFILRACFJLRAEFGLRAEFGHAFLSUAUBAUQUMUHPMUEUFA
      UOUIUPUKQABEFIGHLTACEFJGHLTUCADEFKGHLTUD $.
  $}

  ${
    flt0.a $e |- ( ph -> A e. CC ) $.
    flt0.b $e |- ( ph -> B e. CC ) $.
    flt0.c $e |- ( ph -> C e. CC ) $.
    flt0.n $e |- ( ph -> N e. NN0 ) $.
    flt0.1 $e |- ( ph -> ( ( A ^ N ) + ( B ^ N ) ) = ( C ^ N ) ) $.
    $( A counterexample for FLT does not exist for ` N = 0 ` .  (Contributed by
       SN, 20-Aug-2024.) $)
    flt0 $p |- ( ph -> N e. NN ) $=
      ( wcel cc0 wne cexp co caddc c1 exp0d wceq oveq2 cn0 cn c2 sn-1ne2 necomi
      1p1e2 eqnetri a1i oveq12d 3netr4d eqeq12d syl5ibcom imp mteqand sylanbrc
      elnnne0 ) AEUAKELMEUBKIAELBLNOZCLNOZPOZDLNOZAQQPOZQUSUTVAQMAVAUCQUFQUCUDU
      EUGUHAUQQURQPABFRACGRUIADHRUJAELSZUSUTSZABENOZCENOZPOZDENOZSVBVCJVBVFUSVG
      UTVBVDUQVEURPELBNTELCNTUIELDNTUKULUMUNEUPUO $.
  $}

  ${
    fltdvdsabdvdsc.a $e |- ( ph -> A e. NN ) $.
    fltdvdsabdvdsc.b $e |- ( ph -> B e. NN ) $.
    fltdvdsabdvdsc.c $e |- ( ph -> C e. NN ) $.
    fltdvdsabdvdsc.n $e |- ( ph -> N e. NN ) $.
    fltdvdsabdvdsc.1 $e |- ( ph -> ( ( A ^ N ) + ( B ^ N ) ) = ( C ^ N ) ) $.
    $( Any factor of both ` A ` and ` B ` also divides ` C ` .  This
       establishes the validity of ~ fltabcoprmex .  (Contributed by SN,
       21-Aug-2024.) $)
    fltdvdsabdvdsc $p |- ( ph -> ( A gcd B ) || C ) $=
      ( co cdvds wbr cexp cn wcel syl2anc nnexpcld nnzd cz caddc gcdnncl nnnn0d
      wa gcddvds simpld dvdsexpad simprd dvds2addd breqtrd wb dvdsexpnn syl3anc
      cgcd mpbird ) ABCUNKZDLMZUPENKZDENKZLMZAURBENKZCENKZUAKUSLAURVAVBAURAUPEA
      BOPCOPUPOPZFGBCUBQZAEIUCZRSAVAABEFVERSAVBACEGVERSAUPBEAUPVDSZABFSZVEAUPBL
      MZUPCLMZABTPCTPVHVIUDVGACGSZBCUEQZUFUGAUPCEVFVJVEAVHVIVKUHUGUIJUJAVCDOPEO
      PUQUTUKVDHIUPDEULUMUO $.
  $}

  ${
    fltabcoprmex.a $e |- ( ph -> A e. NN ) $.
    fltabcoprmex.b $e |- ( ph -> B e. NN ) $.
    fltabcoprmex.c $e |- ( ph -> C e. NN ) $.
    fltabcoprmex.n $e |- ( ph -> N e. NN0 ) $.
    fltabcoprmex.1 $e |- ( ph -> ( ( A ^ N ) + ( B ^ N ) ) = ( C ^ N ) ) $.
    $( A counterexample to FLT implies a counterexample to FLT with ` A , B `
       (assigned to ` A / ( A gcd B ) ` and ` B / ( A gcd B ) ` ) coprime (by
       ~ divgcdcoprm0 ).  (Contributed by SN, 20-Aug-2024.) $)
    fltabcoprmex $p |- ( ph -> ( ( ( A / ( A gcd B ) ) ^ N )
                             + ( ( B / ( A gcd B ) ) ^ N ) )
                             = ( ( C / ( A gcd B ) ) ^ N ) ) $=
      ( cgcd co cn wcel gcdnncl syl2anc nncnd nnne0d fltdiv ) ABCDBCKLZEATABMNC
      MNTMNFGBCOPZQATUARABFQACGQADHQIJS $.

    $d A i $.  $d B i $.  $d C i $.  $d ph i $.
    fltaccoprm.1 $e |- ( ph -> ( A gcd B ) = 1 ) $.
    $( A counterexample to FLT with ` A , B ` coprime also has ` A , C `
       coprime.  (Contributed by SN, 20-Aug-2024.) $)
    fltaccoprm $p |- ( ph -> ( A gcd C ) = 1 ) $=
      ( vi cdvds wbr wa cn co wcel cz nnzd cv c1 wceq wi wral cgcd wb coprmgcdb
      syl2anc mpbird simprl cexp simpr adantr dvdsexpim syl3anc anim12d ancomsd
      cmin cn0 imp nnexpcld ad2antrr dvds2sub mpd nncnd expcld laddrotrd simplr
      breqtrd flt0 dvdsexpnn jca ex imim1d ralimdva mpbid ) ALUAZBMNZVRDMNZOZVR
      UBUCZUDZLPUEZBDUFQUBUCZAVSVRCMNZOZWBUDZLPUEZWDAWIBCUFQUBUCZKABPRZCPRZWIWJ
      UGFGBCLUHUIUJAWHWCLPAVRPRZOZWAWGWBWNWAWGWNWAOZVSWFWNVSVTUKWOWFVREULQZCEUL
      QZMNZWOWPDEULQZBEULQZUSQZWQMWOWPWSMNZWPWTMNZOZWPXAMNZWNWAXDWNVTVSXDWNVTXB
      VSXCWNVRSRZDSRZEUTRZVTXBUDWNVRAWMUMZTZAXGWMADHTUNAXHWMIUNZVRDEUOUPWNXFBSR
      ZXHVSXCUDXJAXLWMABFTUNXKVRBEUOUPUQURVAWOWPSRZWSSRZWTSRZXDXEUDWNXMWAWNWPWN
      VREXIXKVBTUNAXNWMWAAWSADEHIVBTVCAXOWMWAAWTABEFIVBTVCWPWSWTVDUPVEAXAWQUCWM
      WAAWTWQWSABEABFVFZIVGACEACGVFZIVGJVHVCVJWOWMWLEPRZWFWRUGAWMWAVIAWLWMWAGVC
      AXRWMWAABCDEXPXQADHVFIJVKVCVRCEVLUPUJVMVNVOVPVEAWKDPRWDWEUGFHBDLUHUIVQ $.

    $( A counterexample to FLT with ` A , B ` coprime also has ` B , C `
       coprime.  Proven from ~ fltaccoprm using commutativity of addition.
       (Contributed by SN, 20-Aug-2024.) $)
    fltbccoprm $p |- ( ph -> ( B gcd C ) = 1 ) $=
      ( cexp co caddc nnexpcld nncnd addcomd eqtrd cgcd nnzd gcdcomd fltaccoprm
      c1 ) ACBDEGFHIACELMZBELMZNMUEUDNMDELMAUDUEAUDACEGIOPAUEABEFIOPQJRACBSMBCS
      MUCACBACGTABFTUAKRUB $.
  $}

  ${
    $d A i $.  $d B i $.  $d C i $.  $d ph i $.
    fltabcoprm.a $e |- ( ph -> A e. NN ) $.
    fltabcoprm.b $e |- ( ph -> B e. NN ) $.
    fltabcoprm.c $e |- ( ph -> C e. NN ) $.
    fltabcoprm.2 $e |- ( ph -> ( A gcd C ) = 1 ) $.
    fltabcoprm.3 $e |- ( ph -> ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) ) $.
    $( A counterexample to FLT with ` A , C ` coprime also has ` A , B `
       coprime.  Converse of ~ fltaccoprm .  (Contributed by SN,
       22-Aug-2024.) $)
    fltabcoprm $p |- ( ph -> ( A gcd B ) = 1 ) $=
      ( vi cdvds wbr wa wceq cn co wcel wb syl2anc c2 cv c1 wral cgcd coprmgcdb
      wi mpbird simprl cexp caddc simplr nnsqcld nnzd ad2antrr dvdssqlem simprr
      mpbid dvds2addd breqtrd jca ex imim1d ralimdva mpd ) AJUAZBKLZVECKLZMZVEU
      BNZUFZJOUCZBCUDPUBNZAVFVEDKLZMZVIUFZJOUCZVKAVPBDUDPUBNZHABOQZDOQZVPVQREGB
      DJUESUGAVOVJJOAVEOQZMZVHVNVIWAVHVNWAVHMZVFVMWAVFVGUHZWBVMVETUIPZDTUIPZKLZ
      WBWDBTUIPZCTUIPZUJPZWEKWBWDWGWHWBWDWBVEAVTVHUKZULUMWBWGWBBAVRVTVHEUNZULUM
      WBWHWBCACOQZVTVHFUNZULUMWBVFWDWGKLZWCWBVTVRVFWNRWJWKVEBUOSUQWBVGWDWHKLZWA
      VFVGUPWBVTWLVGWORWJWMVECUOSUQURAWIWENVTVHIUNUSWBVTVSVMWFRWJAVSVTVHGUNVEDU
      OSUGUTVAVBVCVDAVRWLVKVLREFBCJUESUQ $.
  $}

  ${
    $d ph x z $.  $d ps x z $.  $d ch y $.  $d th y $.  $d S x y z $.
    infdesc.x $e |- ( y = x -> ( ps <-> ch ) ) $.
    infdesc.z $e |- ( y = z -> ( ps <-> th ) ) $.
    infdesc.s $e |- ( ph -> S C_ ( ZZ>= ` M ) ) $.
    infdesc.1 $e |-
        ( ( ph /\ ( x e. S /\ ch ) ) -> E. z e. S ( th /\ z < x ) ) $.
    $( Infinite descent.  The hypotheses say that ` S ` is lower bounded, and
       that if ` ps ` holds for an integer in ` S ` , it holds for a smaller
       integer in ` S ` .  By infinite descent, eventually we cannot go any
       smaller, therefore ` ps ` holds for no integer in ` S ` .  (Contributed
       by SN, 20-Aug-2024.) $)
    infdesc $p |- ( ph -> { y e. S | ps } = (/) ) $=
      ( c0 wn wa wral wrex wcel cr crab wne df-ne cv cle wbr cuz cfv wss ssrab2
      wceq sstrid uzwo sylan elrab wb uzssre sstrdi adantr sselda ltnled anbi2d
      clt rexbidva adantrr sylan2b rexrab sylibr ralrimiva rexnal ralbii ralnex
      mpbid bitri sylib pm2.21dd sylan2br pm2.18da ) ABFHUAZNUKZVTOAVSNUBZVTVSN
      UCAWAPEUDZGUDZUEUFZGVSQZEVSRZVTAVSIUGUHZUIWAWFAVSHWGBFHUJLULVSEGIUMUNAWFO
      ZWAAWDOZGVSRZEVSQZWHAWJEVSAWBVSSZPDWIPZGHRZWJWLAWBHSZCPZWNBCFWBHJUOAWPPDW
      CWBVCUFZPZGHRZWNMAWOWSWNUPCAWOPZWRWMGHWTWCHSZPZWQWIDXBWCWBWTHTWCAHTUIWOAH
      WGTLIUQURZUSUTWTWBTSXAAHTWBXCUTUSVAVBVDVEVMVFBDWIGFHKVGVHVIWKWEOZEVSQWHWJ
      XDEVSWDGVSVJVKWEEVSVLVNVOUSVPVQVR $.
  $}

  ${
    fltne.a $e |- ( ph -> A e. NN ) $.
    fltne.b $e |- ( ph -> B e. NN ) $.
    fltne.c $e |- ( ph -> C e. NN ) $.
    fltne.n $e |- ( ph -> N e. ( ZZ>= ` 2 ) ) $.
    fltne.1 $e |- ( ph -> ( ( A ^ N ) + ( B ^ N ) ) = ( C ^ N ) ) $.
    $( If a counterexample to FLT exists, its addends are not equal.
       (Contributed by SN, 1-Jun-2023.) $)
    fltne $p |- ( ph -> A =/= B ) $=
      ( c2 cdiv co cq wcel wceq cn adantr cexp nncnd c1 ccxp wne cprime cuz cfv
      wn cr cdif 2prm rtprmirr sylancr eldifbd nnzd znq syl2anc eleq1a necon3bd
      wi cz syl mpd crp 2rp a1i eluz2nn nnrecred rpcxpcld nnrpd rpdivcld nnnn0d
      wa nnexpcld 2cnd nnne0d caddc times2d simpr oveq1d oveq2d 3eqtrd mvllmuld
      cmul cc 2cn cxproot expdivd 3eqtr4d exp11nnd mteqand ) ABCKUAELMZUBMZDBLM
      ZAWLNOZUGWLWMUCAWLUHNAKUDOEKUEUFOZWLUHNUIOUJIKEUKULUMAWNWLWMAWMNOZWLWMPWN
      USADUTOBQOWPADHUNFDBUOUPWMNWLUQVAURVBABCPZVLZWLWMEAWLVCOWQAKWKKVCOAVDVEAE
      AWOEQOZIEVFVAZVGVHRAWMVCOWQADBADHVIABFVIVJRAWSWQWTRWRKDESMZBESMZLMZWLESMZ
      WMESMZWRXBKXAWRXBAXBQOWQABEFAEWTVKZVMZRZTWRVNWRXBXHVOWRXBKWCMZXBXBVPMZXBC
      ESMZVPMZXAAXIXJPWQAXBAXBXGTVQRWRXBXKXBVPWRBCESAWQVRVSVTAXLXAPWQJRWAWBAXDK
      PZWQAKWDOWSXMWEWTKEWFULRAXEXCPWQADBEADHTABFTABFVOXFWGRWHWIWJ $.
  $}

  ${
    flt4lem.a $e |- ( ph -> A e. CC ) $.
    $( Raising a number to the fourth power is equivalent to squaring it twice.
       (Contributed by SN, 21-Aug-2024.) $)
    flt4lem $p |- ( ph -> ( A ^ 4 ) = ( ( A ^ 2 ) ^ 2 ) ) $=
      ( c4 cexp co c2 cmul 2t2e4 oveq2i cn0 wcel 2nn0 a1i expmuld eqtr3id ) ABD
      EFBGGHFZEFBGEFGEFQDBEIJABGGCGKLAMNZROP $.
  $}

  ${
    flt4lem1.a $e |- ( ph -> A e. NN ) $.
    flt4lem1.b $e |- ( ph -> B e. NN ) $.
    flt4lem1.c $e |- ( ph -> C e. NN ) $.
    flt4lem1.1 $e |- ( ph -> -. 2 || A ) $.
    flt4lem1.2 $e |- ( ph -> ( A gcd C ) = 1 ) $.
    flt4lem1.3 $e |- ( ph -> ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) ) $.
    $( Satisfy the antecedent used in several ~ pythagtrip lemmas, with
       ` A , C ` coprime rather than ` A , B ` .  (Contributed by SN,
       21-Aug-2024.) $)
    flt4lem1 $p |- ( ph -> ( ( A e. NN /\ B e. NN /\ C e. NN ) /\
                           ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\
                           ( ( A gcd B ) = 1 /\ -. 2 || A ) ) ) $=
      ( cn wcel w3a c2 cexp co caddc wceq cgcd 3jca c1 cdvds wbr fltabcoprm jca
      wn wa ) ABKLZCKLZDKLZMBNOPCNOPQPDNOPRBCSPUARZNBUBUCUFZUGAUHUIUJEFGTJAUKUL
      ABCDEFGIJUDHUET $.
  $}

  ${
    $d A i $.  $d B i $.  $d C i $.  $d ph i $.
    flt4lem2.a $e |- ( ph -> A e. NN ) $.
    flt4lem2.b $e |- ( ph -> B e. NN ) $.
    flt4lem2.c $e |- ( ph -> C e. NN ) $.
    flt4lem2.1 $e |- ( ph -> 2 || A ) $.
    flt4lem2.2 $e |- ( ph -> ( A gcd C ) = 1 ) $.
    flt4lem2.3 $e |- ( ph -> ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) ) $.
    $( If ` A ` is even, ` B ` is odd.  (Contributed by SN, 22-Aug-2024.) $)
    flt4lem2 $p |- ( ph -> -. 2 || B ) $=
      ( vi c2 cdvds wbr wa wcel cz adantr cn nnzd cgcd co c1 wceq wn wne cv cuz
      cfv wrex breq1 anbi12d 2z uzid ax-mp a1i gcdnncl syl2anc simpr wi dvdsgcd
      syl3anc mp2and fltdvdsabdvdsc dvdstrd rspcedvdw wb ncoprmgcdne1b mpbid ex
      2nn jca necon2bd mpd ) ABDUAUBZUCUDLCMNZUEIAVPVOUCAVPVOUCUFZAVPOZKUGZBMNZ
      VSDMNZOZKLUHUIZUJZVQVRWBLBMNZLDMNZOKLWCVSLUDVTWEWAWFVSLBMUKVSLDMUKULLWCPZ
      VRLQPZWGUMLUNUOUPVRWEWFAWEVPHRZVRLBCUAUBZDWHVRUMUPZAWJQPVPAWJABSPZCSPWJSP
      EFBCUQURTRVRDADSPZVPGRZTVRWEVPLWJMNZWIAVPUSVRWHBQPCQPZWEVPOWOUTWKVRBAWLVP
      ERZTAWPVPACFTRLBCVAVBVCAWJDMNVPABCDLEFGLSPAVKUPJVDRVEVLVFVRWLWMWDVQVGWQWN
      BDKVHURVIVJVMVN $.
  $}

  ${
    flt4lem3.a $e |- ( ph -> A e. NN ) $.
    flt4lem3.b $e |- ( ph -> B e. NN ) $.
    flt4lem3.c $e |- ( ph -> C e. NN ) $.
    flt4lem3.1 $e |- ( ph -> 2 || A ) $.
    flt4lem3.2 $e |- ( ph -> ( A gcd C ) = 1 ) $.
    flt4lem3.3 $e |- ( ph -> ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) ) $.
    $( Equivalent to ~ pythagtriplem4 .  Show that ` C + A ` and ` C - A ` are
       coprime.  (Contributed by SN, 22-Aug-2024.) $)
    flt4lem3 $p |- ( ph -> ( ( C + A ) gcd ( C - A ) ) = 1 ) $=
      ( caddc co cgcd c1 nnzd cn wcel c2 cexp wceq cmin zaddcld zsubcld gcdcomd
      w3a cdvds wbr wn wa flt4lem2 cn0 2nn0 fltabcoprm fltbccoprm nnsqcld nncnd
      a1i addcomd eqtrd flt4lem1 pythagtriplem4 syl ) ADBKLZDBUALZMLVDVCMLZNAVC
      VDADBADGOZABEOZUBADBVFVGUCUDACPQBPQDPQUECRSLZBRSLZKLZDRSLZTCBMLNTRCUFUGUH
      UIUEVENTACBDFEGABCDEFGHIJUJABCDREFGRUKQAULUQJABCDEFGIJUMUNAVJVIVHKLVKAVHV
      IAVHACFUOUPAVIABEUOUPURJUSUTCBDVAVBUS $.
  $}

  ${
    flt4lem4.a $e |- ( ph -> A e. NN ) $.
    flt4lem4.b $e |- ( ph -> B e. NN ) $.
    flt4lem4.c $e |- ( ph -> C e. NN ) $.
    flt4lem4.1 $e |- ( ph -> ( A gcd B ) = 1 ) $.
    flt4lem4.2 $e |- ( ph -> ( A x. B ) = ( C ^ 2 ) ) $.
    $( If the product of two coprime factors is a perfect square, the factors
       are perfect squares.  (Contributed by SN, 22-Aug-2024.) $)
    flt4lem4 $p |-
      ( ph -> ( A = ( ( A gcd C ) ^ 2 ) /\ B = ( ( B gcd C ) ^ 2 ) ) ) $=
      ( cgcd co c2 cexp wceq cn0 wcel cz c1 wi nnnn0d eqcomd nn0zd oveq1d eqtrd
      cmul 1gcd syl coprimeprodsq syl31anc mpd nnzd coprimeprodsq2 jca ) ABBDJK
      LMKNZCCDJKLMKNZADLMKZBCUEKZNZUNAUQUPIUAZABOPCQPDOPZBCJKZDJKZRNZURUNSABETA
      CACFTZUBADGTZAVBRDJKZRAVARDJHUCADQPVFRNADVEUBDUFUGUDZBCDUHUIUJAURUOUSABQP
      COPUTVCURUOSABEUKVDVEVGBCDULUIUJUM $.
  $}

  ${
    $d A i $.  $d B i $.  $d C i $.  $d M i $.  $d N i $.
    flt4lem5.1 $e |-
      M = ( ( ( sqrt ` ( C + B ) ) + ( sqrt ` ( C - B ) ) ) / 2 ) $.
    flt4lem5.2 $e |-
      N = ( ( ( sqrt ` ( C + B ) ) - ( sqrt ` ( C - B ) ) ) / 2 ) $.
    $( In the context of the lemmas of ~ pythagtrip , ` M ` and ` N ` are
       coprime.  (Contributed by SN, 23-Aug-2024.) $)
    flt4lem5 $p |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\
      ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) /\ ( ( A gcd B ) = 1 /\ -. 2 || A )
      ) -> ( M gcd N ) = 1 ) $=
      ( vi cn wcel c2 cexp co wceq cdvds wbr wa wi nnzd ad2antrr w3a caddc cgcd
      c1 wn cv simp3l wb simp11 simp12 coprmgcdb syl2anc mpbird pythagtriplem11
      wral cmin simplr nnsqcld pythagtriplem13 simprl cz 2nn dvdsexp2im syl3anc
      a1i mpd simprr dvds2subd pythagtriplem15 breqtrrd 2z nnmulcld dvdsmultr2d
      cmul pythagtriplem16 jca ex imim1d ralimdva mpbid ) AIJZBIJZCIJZUAZAKLMBK
      LMUBMCKLMNZABUCMUDNZKAOPUEZQZUAZHUFZDOPZWJEOPZQZWJUDNZRZHIUOZDEUCMUDNZWIW
      JAOPZWJBOPZQZWNRZHIUOZWPWIXBWFWDWEWFWGUGWIWAWBXBWFUHWAWBWCWEWHUIWAWBWCWEW
      HUJABHUKULUMWIXAWOHIWIWJIJZQZWMWTWNXDWMWTXDWMQZWRWSXEWJDKLMZEKLMZUPMZAOXE
      WJXFXGXEWJWIXCWMUQSZXEXFXEDWIDIJZXCWMABCDFUNZTZURSXEXGXEEWIEIJZXCWMABCEGU
      SZTZURSXEWKWJXFOPZXDWKWLUTXEWJVAJZDVAJKIJZWKXPRXIXEDXLSZXRXEVBVEZWJDKVCVD
      VFXEWLWJXGOPZXDWKWLVGZXEXQEVAJXRWLYARXIXEEXOSZXTWJEKVCVDVFVHWIAXHNXCWMABC
      DEFGVITVJXEWJKDEVNMZVNMZBOXEWJKYDXIKVAJXEVKVEXEYDXEDEXLXOVLSXEWJDEXIXSYCY
      BVMVMWIBYENXCWMABCDEFGVOTVJVPVQVRVSVFWIXJXMWPWQUHXKXNDEHUKULVT $.
  $}

  ${
    $d ph p $.  $d M p $.  $d R p $.  $d S p $.
    flt4lem5elem.m $e |- ( ph -> M e. NN ) $.
    flt4lem5elem.r $e |- ( ph -> R e. NN ) $.
    flt4lem5elem.s $e |- ( ph -> S e. NN ) $.
    flt4lem5elem.1 $e |- ( ph -> M = ( ( R ^ 2 ) + ( S ^ 2 ) ) ) $.
    flt4lem5elem.2 $e |- ( ph -> ( R gcd S ) = 1 ) $.
    $( Version of ~ fltaccoprm and ~ fltbccoprm where ` M ` is not squared.
       This can be proved in general for any polynomial in three variables:
       using ~ prmdvdsncoprmbd , ~ dvds2addd , and ~ prmdvdsexp , we can show
       that if two variables are coprime, the third is also coprime to the two.
       (Contributed by SN, 24-Aug-2024.) $)
    flt4lem5elem $p |- ( ph -> ( ( R gcd M ) = 1 /\ ( S gcd M ) = 1 ) ) $=
      ( vp co c1 cdvds wbr wa cprime wcel cz nnzd ad2antrr cgcd wceq cv wrex wn
      prmdvdsncoprmbd necon2bbid mpbid simprl cexp cmin simplr prmz syl nnsqcld
      c2 simprr wb prmdvdssq syl2anc dvds2subd cc nncnd mvrladdd breqtrd mpbird
      caddc jca ex reximdva mtod mvrraddd ) ABDUAKZLUBZCDUAKZLUBZAVNJUCZBMNZVQD
      MNZOZJPUDZUEAWAVRVQCMNZOZJPUDZABCUAKZLUBWDUEIAWDWELABCJFGUFUGUHZAVTWCJPAV
      QPQZOZVTWCWHVTOZVRWBWHVRVSUIZWIWBVQCUPUJKZMNZWIVQDBUPUJKZUKKWKMWIVQDWMWIW
      GVQRQZAWGVTULZVQUMZUNADRQZWGVTADESZTAWMRQWGVTAWMABFUOZSTWHVRVSUQWIVRVQWMM
      NZWJWIWGBRQZVRWTURZWOAXAWGVTABFSZTVQBUSZUTUHVAWIDWMWKAWMVBQZWGVTAWMWSVCZT
      AWKVBQZWGVTAWKACGUOZVCZTADWMWKVGKUBZWGVTHTVDVEWIWGCRQZWBWLURZWOAXKWGVTACG
      SZTVQCUSZUTVFVHVIVJVKAWAVMLABDJFEUFUGVFAVPWBVSOZJPUDZUEAXPWDWFAXOWCJPWHXO
      WCWHXOOZVRWBXQVRWTXQVQDWKUKKWMMXQVQDWKXQWGWNAWGXOULZWPUNAWQWGXOWRTAWKRQWG
      XOAWKXHSTWHWBVSUQXQWBWLWHWBVSUIZXQWGXKXLXRAXKWGXOXMTXNUTUHVAXQDWMWKAXEWGX
      OXFTAXGWGXOXITAXJWGXOHTVLVEXQWGXAXBXRAXAWGXOXCTXDUTVFXSVHVIVJVKAXPVOLACDJ
      GEUFUGVFVH $.
  $}

  ${
    flt4lem5a.m $e |- M = (
      ( ( sqrt ` ( C + ( B ^ 2 ) ) ) + ( sqrt ` ( C - ( B ^ 2 ) ) ) ) / 2 ) $.
    flt4lem5a.n $e |- N = (
      ( ( sqrt ` ( C + ( B ^ 2 ) ) ) - ( sqrt ` ( C - ( B ^ 2 ) ) ) ) / 2 ) $.
    flt4lem5a.r $e |-
      R = ( ( ( sqrt ` ( M + N ) ) + ( sqrt ` ( M - N ) ) ) / 2 ) $.
    flt4lem5a.s $e |-
      S = ( ( ( sqrt ` ( M + N ) ) - ( sqrt ` ( M - N ) ) ) / 2 ) $.
    flt4lem5a.a $e |- ( ph -> A e. NN ) $.
    flt4lem5a.b $e |- ( ph -> B e. NN ) $.
    flt4lem5a.c $e |- ( ph -> C e. NN ) $.
    flt4lem5a.1 $e |- ( ph -> -. 2 || A ) $.
    flt4lem5a.2 $e |- ( ph -> ( A gcd C ) = 1 ) $.
    flt4lem5a.3 $e |- ( ph -> ( ( A ^ 4 ) + ( B ^ 4 ) ) = ( C ^ 2 ) ) $.
    $( Part 1 of Equation 1 of
       ~ https://crypto.stanford.edu/pbc/notes/numberfield/fermatn4.html .
       (Contributed by SN, 22-Aug-2024.) $)
    flt4lem5a $p |- ( ph -> ( ( A ^ 2 ) + ( N ^ 2 ) ) = ( M ^ 2 ) ) $=
      ( c2 co cexp cn wcel w3a caddc wceq cgcd c1 cdvds wn wa nnsqcld cprime cz
      wbr wb 2prm nnzd prmdvdssq sylancr mtbid wi 2nn a1i rplpwr syl3anc mpd c4
      nncnd flt4lem oveq12d eqtr3d flt4lem1 pythagtriplem11 syl pythagtriplem13
      cmin pythagtriplem15 mvrrsubd ) ABSUATZGSUATZHSUATZAWAAGAVTUBUCCSUATZUBUC
      DUBUCZUDVTSUATZWCSUATZUETZDSUATZUFVTWCUGTUHUFSVTUIUOZUJUKUDZGUBUCAVTWCDAB
      MULACNULOASBUIUOZWIPASUMUCBUNUCWKWIUPUQABMURSBUSUTVAABDUGTUHUFZVTDUGTUHUF
      ZQABUBUCWDSUBUCZWLWMVBMOWNAVCVDBDSVEVFVGABVHUATZCVHUATZUETWGWHAWOWEWPWFUE
      ABABMVIVJACACNVIVJVKRVLVMZVTWCDGIVNVOULVIAWBAHAWJHUBUCWQVTWCDHJVPVOULVIAW
      JVTWAWBVQTUFWQVTWCDGHIJVRVOVS $.

    $( Part 2 of Equation 1 of
       ~ https://crypto.stanford.edu/pbc/notes/numberfield/fermatn4.html .
       (Contributed by SN, 22-Aug-2024.) $)
    flt4lem5b $p |- ( ph -> ( 2 x. ( M x. N ) ) = ( B ^ 2 ) ) $=
      ( c2 co cexp cmul cn wcel w3a caddc wceq cgcd c1 cdvds wbr nnsqcld cprime
      wn wa cz wb 2prm prmdvdssq sylancr mtbid wi 2nn a1i rplpwr syl3anc mpd c4
      nnzd nncnd flt4lem oveq12d eqtr3d flt4lem1 pythagtriplem16 syl eqcomd ) A
      CSUATZSGHUBTUBTZABSUATZUCUDVRUCUDDUCUDZUEVTSUATZVRSUATZUFTZDSUATZUGVTVRUH
      TUIUGSVTUJUKZUNUOUEVRVSUGAVTVRDABMULACNULOASBUJUKZWFPASUMUDBUPUDWGWFUQURA
      BMVISBUSUTVAABDUHTUIUGZVTDUHTUIUGZQABUCUDWASUCUDZWHWIVBMOWJAVCVDBDSVEVFVG
      ABVHUATZCVHUATZUFTWDWEAWKWBWLWCUFABABMVJVKACACNVJVKVLRVMVNVTVRDGHIJVOVPVQ
      $.

    $( Part 2 of Equation 2 of
       ~ https://crypto.stanford.edu/pbc/notes/numberfield/fermatn4.html .
       (Contributed by SN, 22-Aug-2024.) $)
    flt4lem5c $p |- ( ph -> N = ( 2 x. ( R x. S ) ) ) $=
      ( c2 co cn wcel cexp caddc wceq cgcd c1 cdvds wbr cmul w3a nnsqcld cprime
      wn wa cz wb 2prm prmdvdssq sylancr mtbid wi 2nn a1i rplpwr syl3anc mpd c4
      nncnd flt4lem oveq12d eqtr3d flt4lem1 pythagtriplem13 syl pythagtriplem11
      nnzd flt4lem5a gcdcomd eqtrd addcomd fltabcoprm pythagtriplem16 syl312anc
      flt4lem5 ) ABUAUBZHUAUBZGUAUBZBSUCTZHSUCTZUDTZGSUCTZUEBHUFTZUGUESBUHUIZUN
      HSEFUJTUJTUEMAWIUAUBCSUCTZUAUBDUAUBZUKWISUCTZWOSUCTZUDTZDSUCTZUEWIWOUFTUG
      UESWIUHUIZUNUOUKZWGAWIWODABMULZACNULOAWNXAPASUMUBBUPUBWNXAUQURABMVQZSBUSU
      TVAABDUFTUGUEZWIDUFTUGUEZQAWFWPSUAUBZXEXFVBMOXGAVCVDBDSVEVFVGABVHUCTZCVHU
      CTZUDTWSWTAXHWQXIWRUDABABMVIVJACACNVIVJVKRVLVMZWIWODHJVNVOZAXBWHXJWIWODGI
      VPVOZABCDEFGHIJKLMNOPQRVRZAWMHBUFTUGABHXDAHXKVQZVSAHBGXKMXLAHGUFTGHUFTZUG
      AHGXNAGXLVQVSAXBXOUGUEXJWIWODGHIJWEVOVTAWJWIUDTWKWLAWJWIAWJAHXKULVIAWIXCV
      IWAXMVTWBVTPBHGEFKLWCWD $.

    $( Part 3 of Equation 2 of
       ~ https://crypto.stanford.edu/pbc/notes/numberfield/fermatn4.html .
       (Contributed by SN, 23-Aug-2024.) $)
    flt4lem5d $p |- ( ph -> M = ( ( R ^ 2 ) + ( S ^ 2 ) ) ) $=
      ( c2 co cn wcel cexp caddc wceq cgcd c1 cdvds wbr wn wa nnsqcld cprime cz
      w3a wb 2prm nnzd prmdvdssq sylancr mtbid wi 2nn a1i rplpwr syl3anc mpd c4
      nncnd flt4lem oveq12d eqtr3d flt4lem1 pythagtriplem13 syl pythagtriplem11
      flt4lem5a gcdcomd flt4lem5 addcomd fltabcoprm pythagtriplem17 syl312anc
      eqtrd ) ABUAUBZHUAUBZGUAUBZBSUCTZHSUCTZUDTZGSUCTZUEBHUFTZUGUESBUHUIZUJGES
      UCTFSUCTUDTUEMAWHUAUBCSUCTZUAUBDUAUBZUOWHSUCTZWNSUCTZUDTZDSUCTZUEWHWNUFTU
      GUESWHUHUIZUJUKUOZWFAWHWNDABMULZACNULOAWMWTPASUMUBBUNUBWMWTUPUQABMURZSBUS
      UTVAABDUFTUGUEZWHDUFTUGUEZQAWEWOSUAUBZXDXEVBMOXFAVCVDBDSVEVFVGABVHUCTZCVH
      UCTZUDTWRWSAXGWPXHWQUDABABMVIVJACACNVIVJVKRVLVMZWHWNDHJVNVOZAXAWGXIWHWNDG
      IVPVOZABCDEFGHIJKLMNOPQRVQZAWLHBUFTUGABHXCAHXJURZVRAHBGXJMXKAHGUFTGHUFTZU
      GAHGXMAGXKURVRAXAXNUGUEXIWHWNDGHIJVSVOWDAWIWHUDTWJWKAWIWHAWIAHXJULVIAWHXB
      VIVTXLWDWAWDPBHGEFKLWBWC $.

    $( Satisfy the hypotheses of ~ flt4lem4 .  (Contributed by SN,
       23-Aug-2024.) $)
    flt4lem5e $p |- ( ph -> (
      ( ( R gcd S ) = 1 /\ ( R gcd M ) = 1 /\ ( S gcd M ) = 1 ) /\
      ( R e. NN /\ S e. NN /\ M e. NN ) /\
      ( ( M x. ( R x. S ) ) = ( ( B / 2 ) ^ 2 ) /\ ( B / 2 ) e. NN ) ) ) $=
      ( co c2 cgcd c1 wceq w3a cn wcel cmul cdiv cexp wa caddc cdvds wn nnsqcld
      wbr cprime cz wb 2prm nnzd prmdvdssq sylancr mtbid 2nn a1i rplpwr syl3anc
      wi mpd c4 flt4lem oveq12d eqtr3d flt4lem1 pythagtriplem13 pythagtriplem11
      nncnd syl flt4lem5a gcdcomd flt4lem5 eqtrd fltabcoprm syl312anc flt4lem5d
      addcomd flt4lem5elem 3anass sylanbrc 3jca cc sq2 4cn eqeltri nnmulcld cc0
      wne 4ne0 eqnetri 2cn sqvali oveq1i 2cnd flt4lem5c eqeltrrd mulassd eqcomd
      oveq2d flt4lem5b 3eqtrd eqtrid mvllmuld 2ne0 sqdivd eqtr4d cq znq sylancl
      mul4d clt nngt0d cr nnred halfpos2 mpbid posqsqznn jca ) AEFUASUBUCZEGUAS
      UBUCZFGUASUBUCZUDZEUEUFZFUEUFZGUEUFZUDGEFUGSZUGSZCTUHSZTUISZUCZYQUEUFZUJA
      YHYIYJUJYKABUEUFZHUEUFZYNBTUISZHTUISZUKSZGTUISZUCZBHUASZUBUCZTBULUOZUMZYH
      MAUUCUEUFCTUISZUEUFDUEUFZUDUUCTUISZUULTUISZUKSZDTUISZUCUUCUULUASUBUCTUUCU
      LUOZUMUJUDZUUBAUUCUULDABMUNZACNUNOAUUJUURPATUPUFBUQUFUUJUURURUSABMUTZTBVA
      VBVCABDUASUBUCZUUCDUASUBUCZQAUUAUUMTUEUFZUVBUVCVHMOUVDAVDVEBDTVFVGVIABVJU
      ISZCVJUISZUKSUUPUUQAUVEUUNUVFUUOUKABABMVQVKACACNVQZVKVLRVMVNZUUCUULDHJVOV
      RZAUUSYNUVHUUCUULDGIVPVRZABCDEFGHIJKLMNOPQRVSZAUUHHBUASUBABHUVAAHUVIUTZVT
      AHBGUVIMUVJAHGUASGHUASZUBAHGUVLAGUVJUTVTAUUSUVMUBUCUVHUUCUULDGHIJWAVRWBAU
      UDUUCUKSUUEUUFAUUDUUCAUUDAHUVIUNVQAUUCUUTVQWFUVKWBWCWBZPBHGEFKLWAWDZAEFGU
      VJAUUAUUBYNUUGUUIUUKYLMUVIUVJUVKUVNPBHGEKVPWDZAUUAUUBYNUUGUUIUUKYMMUVIUVJ
      UVKUVNPBHGFLVOWDZABCDEFGHIJKLMNOPQRWEUVOWGYHYIYJWHWIAYLYMYNUVPUVQUVJWJAYS
      YTAYPUULTTUISZUHSYRAUVRYPUULUVRWKUFAUVRVJWKWLWMWNVEAYPAGYOUVJAEFUVPUVQWOZ
      WOZVQUVRWPWQAUVRVJWPWLWRWSVEAUVRYPUGSTTUGSZYPUGSZUULUVRUWAYPUGTWTXAXBAUWB
      TGUGSTYOUGSZUGSZTGHUGSZUGSZUULATTGYOAXCZUWGAGUVJVQZAYOUVSVQXSAUWDTGUWCUGS
      ZUGSUWFATGUWCUWGUWHAUWCAHUWCUEABCDEFGHIJKLMNOPQRXDZUVIXEVQXFAUWIUWETUGAUW
      CHGUGAHUWCUWJXGXHXHWBABCDEFGHIJKLMNOPQRXIXJXKXLACTUVGUWGTWPWQAXMVEXNXOZAY
      QAYPYRUQUWKAYPUVTUTXEACUQUFUVDYQXPUFACNUTVDCTXQXRAWPCXTUOZWPYQXTUOZACNYAA
      CYBUFUWLUWMURACNYCCYDVRYEYFYGWJ $.

    $( Final equation of
       ~ https://crypto.stanford.edu/pbc/notes/numberfield/fermatn4.html .
       Given ` A ^ 4 + B ^ 4 = C ^ 2 ` , provide a smaller solution.  This
       satisfies the infinite descent condition.  (Contributed by SN,
       24-Aug-2024.) $)
    flt4lem5f $p |- ( ph -> ( ( M gcd ( B / 2 ) ) ^ 2 ) =
      ( ( ( R gcd ( B / 2 ) ) ^ 4 ) + ( ( S gcd ( B / 2 ) ) ^ 4 ) ) ) $=
      ( co cgcd c2 cexp caddc cdiv c4 flt4lem5d wceq cmul cn wcel w3a flt4lem5e
      c1 wa simp2d simp3d simp1d nnmulcld simprd nnzd gcdcomd eqtrd cz wi rpmul
      syl3anc mp2and simpld nncnd mul32d mulassd oveq1d gcdnncl syl2anc flt4lem
      flt4lem4 eqtr4d oveq12d 3eqtr3d ) AGEUAUBSZFUAUBSZUCSGCUAUDSZTSUAUBSZEWBT
      SZUEUBSZFWBTSZUEUBSZUCSABCDEFGHIJKLMNOPQRUFAGWCUGEFUHSZWHWBTSUAUBSUGAGWHW
      BAEUIUJZFUIUJZGUIUJZAEFTSZUMUGZEGTSZUMUGZFGTSZUMUGZUKZWIWJWKUKZGWHUHSZWBU
      AUBSZUGZWBUIUJZUNZABCDEFGHIJKLMNOPQRULZUOZUPZAEFAWIWJWKXFUQZAWIWJWKXFUOZU
      RAXBXCAWRWSXDXEUPZUSZAGETSZUMUGZGFTSZUMUGZGWHTSUMUGZAXLWNUMAGEAGXGUTZAEXH
      UTZVAAWMWOWQAWRWSXDXEUQZUOZVBAXNWPUMAGFXQAFXIUTZVAAWMWOWQXSUPZVBAGVCUJZEV
      CUJZFVCUJZXMXOUNXPVDXQXRYAGEFVEVFVGAXBXCXJVHZVPVHAVTWEWAWGUCAVTWDUAUBSZUA
      UBSWEAEYGUAUBAGFUHSZYHWBTSUAUBSUGEYGUGAYHEWBAGFXGXIURZXHXKAYHETSEYHTSZUMA
      YHEAYHYIUTXRVAAWOWMYJUMUGZXTAWMWOWQXSUQZAYDYCYEWOWMUNYKVDXRXQYAEGFVEVFVGV
      BAYHEUHSGEUHSZFUHSZXAAGFEAGXGVIZAFXIVIZAEXHVIZVJAYNWTXAAGEFYOYQYPVKYFVBZV
      BVPUSVLAWDAWDAWIXCWDUIUJXHXKEWBVMVNVIVOVQAWAWFUAUBSZUAUBSWGAFYSUAUBAYMYMW
      BTSUAUBSUGFYSUGAYMFWBAGEXGXHURZXIXKAYMFTSFYMTSZUMAYMFAYMYTUTYAVAAWQFETSZU
      MUGZUUAUMUGZYBAUUBWLUMAFEYAXRVAYLVBAYEYCYDWQUUCUNUUDVDYAXQXRFGEVEVFVGVBYR
      VPUSVLAWFAWFAWJXCWFUIUJXIXKFWBVMVNVIVOVQVRVS $.
  $}

  ${
    flt4lem6.a $e |- ( ph -> A e. NN ) $.
    flt4lem6.b $e |- ( ph -> B e. NN ) $.
    flt4lem6.c $e |- ( ph -> C e. NN ) $.
    flt4lem6.1 $e |- ( ph -> ( ( A ^ 4 ) + ( B ^ 4 ) ) = ( C ^ 2 ) ) $.
    $( Remove shared factors in a solution to ` A ^ 4 + B ^ 4 = C ^ 2 ` .
       (Contributed by SN, 24-Jul-2024.) $)
    flt4lem6 $p |- ( ph -> (
      ( ( A / ( A gcd B ) ) e. NN /\ ( B / ( A gcd B ) ) e. NN
                                  /\ ( C / ( ( A gcd B ) ^ 2 ) ) e. NN ) /\
      ( ( ( A / ( A gcd B ) ) ^ 4 ) + ( ( B / ( A gcd B ) ) ^ 4 ) )
                                   = ( ( C / ( ( A gcd B ) ^ 2 ) ) ^ 2 ) ) ) $=
      ( co cdiv cn wcel c2 cexp c4 caddc cz nnzd syl2anc nncnd cgcd w3a gcdnncl
      divgcdnn divgcdnnr flt4lem oveq12d nnne0d cn0 a1i expdivd expcld nnexpcld
      wceq divdird eqtr4d nnsqcld sqdivd 3eqtr4d nnaddcld eqeltrrd cq znq nnred
      4nn0 nngt0d divgt0d posqsqznn 3jca jca ) ABBCUAIZJIZKLZCVKJIZKLZDVKMNIZJI
      ZKLZUBVLONIZVNONIZPIZVQMNIZUNAVMVOVRABKLZCQLVMEACFRBCUDSZACKLZBQLVOFABERC
      BUESZAVQAWAWBQABONIZCONIZPIZVKONIZJIZDMNIZVPMNIZJIWAWBAWIWLWJWMJHAVKAVKAW
      CWEVKKLEFBCUCSZTZUFUGAWAWGWJJIZWHWJJIZPIWKAVSWPVTWQPABVKOABETZWOAVKWNUHZO
      UILAVEUJZUKACVKOACFTZWOWSWTUKUGAWGWHWJABOWRWTULACOXAWTULAVKOWOWTULAWJAVKO
      WNWTUMUHUOUPADVPADGTAVPAVKWNUQZTAVPXBUHURUSZAWAAVSVTAVLOWDWTUMAVNOWFWTUMU
      TRVAADQLVPKLVQVBLADGRXBDVPVCSADVPADGVDAVPXBVDADGVFAVPXBVFVGVHVIXCVJ $.
  $}

  ${
    $d ph l $.  $d ph m n $.  $d B l m n $.  $d C l m n $.  $d g h l m n $.
    flt4lem7.a $e |- ( ph -> A e. NN ) $.
    flt4lem7.b $e |- ( ph -> B e. NN ) $.
    flt4lem7.c $e |- ( ph -> C e. NN ) $.
    flt4lem7.1 $e |- ( ph -> -. 2 || A ) $.
    flt4lem7.2 $e |- ( ph -> ( A gcd B ) = 1 ) $.
    flt4lem7.3 $e |- ( ph -> ( ( A ^ 4 ) + ( B ^ 4 ) ) = ( C ^ 2 ) ) $.
    $( Convert ~ flt4lem5f into a convenient form for ~ nna4b4nsq .  TODO-SN:
       The change to ` ( A gcd B ) = 1 ` points at some inefficiency in the
       lemmas.  (Contributed by SN, 25-Aug-2024.) $)
    flt4lem7 $p |- ( ph -> E. l e. NN ( E. g e. NN E. h e. NN ( -. 2 || g /\
      ( ( g gcd h ) = 1 /\ ( ( g ^ 4 ) + ( h ^ 4 ) ) = ( l ^ 2 ) ) )
                                     /\ l < C ) ) $=
      ( cgcd co c1 wceq c2 cn wcel vm vn cv clt wbr c4 cexp caddc wa wrex cdvds
      wn csqrt cfv cmin cdiv breq1 eqeq2d anbi2d 2rexbidv anbi12d w3a cmul eqid
      oveq1 nnsqcld cn0 2nn0 a1i nncnd flt4lem oveq12d eqtr3d 2nn rppwr syl3anc
      wi mpd fltaccoprm cz wb nnzd rpexp flt4lem5e simp2d simp3d simprd gcdnncl
      mpbid syl2anc nnred gcdle2d crp nnrpd rphalflt 4nn0 nnexpcld 2lt4 2z 1red
      syl 4z cr 2re 1lt2 cle 2t1e2 nnge1d 2rp lemuldiv2d mpbird ltletrd ltexp2d
      eqbrtrrid mpbii cc0 nngt0d lttrd eqeq1d oveq1d oveq2 oveq2d simp1d gcdass
      gcdcomd jca 2rspcedvdw breq2 notbid simplrl adantr ad2antrr simpr simp-4r
      weq eqtrd simplrr dvdsexp2im mp3an2i ex ltaddpos2d breqtrd ltexp1d nnnn0d
      lelttrd gcdnn0id eqtr2d 3eqtr4rd 3eqtrd flt4lem5f eqcomd rspcedvdw simprr
      1gcd 3eqtr3d simplr addcomd jca32 simprl simp-5r flt4lem2 mtod imor sylib
      wo imp mpjaodan rexlimdvva expimpd reximdva ) AGUCZDUDUEZUAUCZUBUCZNOZPQZ
      UVMUFUGOZUVNUFUGOZUHOZUVKRUGOZQZUIZUBSUJUASUJZUIZGSUJREUCZUKUEZULZUWEFUCZ
      NOZPQZUWEUFUGOZUWHUFUGOZUHOZUVTQZUIZUIZFSUJESUJZUVLUIZGSUJAUWDDCRUGOZUHOU
      MUNZDUWSUOOUMUNZUHORUPOZCRUPOZNOZDUDUEZUVPUVSUXDRUGOZQZUIZUBSUJUASUJZUIGU
      XDSUVKUXDQZUVLUXEUWCUXIUVKUXDDUDUQUXJUWBUXHUAUBSSUXJUWAUXGUVPUXJUVTUXFUVS
      UVKUXDRUGVEURUSUTVAAUXBSTZUXCSTZUXDSTAUXBUWTUXAUOORUPOZUHOUMUNZUXBUXMUOOU
      MUNZUHORUPOZSTZUXNUXOUOORUPOZSTZUXKAUXPUXRNOZPQZUXPUXBNOPQZUXRUXBNOPQZVBZ
      UXQUXSUXKVBZUXBUXPUXRVCOVCOUXCRUGOQZUXLUIZABCDUXPUXRUXBUXMUXBVDZUXMVDZUXP
      VDZUXRVDZHIJKABRUGOZDNOPQZBDNOPQZAUYLUWSDRABHVFACIVFZJRVGTZAVHVIABUFUGOZC
      UFUGOZUHOZUYLRUGOZUWSRUGOZUHODRUGOZAUYQUYTUYRVUAUHABABHVJVKACACIVJVKVLMVM
      ABCNOPQZUYLUWSNOPQZLABSTCSTRSTZVUCVUDVQHIVUEAVNVIZBCRVOVPVRVSABVTTDVTTVUE
      UYMUYNWAABHWBADJWBVUFBDRWCVPWIZMWDZWEZWFZAUYFUXLAUYDUYEUYGVUHWFWGZUXBUXCW
      HWJZAUXEUXIAUXDUXCDAUXDVULWKAUXCVUKWKZADJWKZAUXBUXCAUXBVUJWBVUKWLAUXCCDVU
      MACIWKZVUNACWMTUXCCUDUEACIWNZCWOXAACDUDUEUWSVUBUDUEAUWSUYRVUBAUWSUYOWKAUY
      RACUFIUFVGTZAWPVIZWQWKZAVUBADJVFWKARUFUDUEUWSUYRUDUEWRACRUFVUORVTTZAWSVIU
      FVTTAXBVIAPRCAWTZRXCTAXDVIVUOPRUDUEAXEVIARRPVCOZCXFXGAVVBCXFUEPUXCXFUEAUX
      CVUKXHAPCRVVAVUORWMTAXIVIXJXKXNXLXMXOAUYRUYSVUBUDAXPUYQUDUEUYRUYSUDUEAUYQ
      ABUFHVURWQZXQAUYQUYRAUYQVVCWKVUSUUAWIMUUBXRACDRVUPADJWNVUFUUCXKXRUUEAUXHU
      XPUXCNOZUVNNOZPQZVVDUFUGOZUVRUHOZUXFQZUIVVDUXRUXCNOZNOZPQZVVGVVJUFUGOZUHO
      ZUXFQZUIUAUBVVDVVJSSUVMVVDQZUVPVVFUXGVVIVVPUVOVVEPUVMVVDUVNNVEXSVVPUVSVVH
      UXFVVPUVQVVGUVRUHUVMVVDUFUGVEXTXSVAUVNVVJQZVVFVVLVVIVVOVVQVVEVVKPUVNVVJVV
      DNYAXSVVQVVHVVNUXFVVQUVRVVMVVGUHUVNVVJUFUGVEYBXSVAAUXQUXLVVDSTAUXQUXSUXKV
      UIYCZVUKUXPUXCWHWJAUXSUXLVVJSTAUXQUXSUXKVUIWEZVUKUXRUXCWHWJZAVVLVVOAVVKUX
      PUXCVVJNOZNOZUXPVVJNOZPAUXPVTTZUXCVTTZVVJVTTVVKVWBQAUXPVVRWBZAUXCVUKWBZAV
      VJVVTWBVVJUXCUXPYDVPAVWAVVJUXPNAUXCUXCNOZUXRNOZUXCUXCUXRNOZNOZVVJVWAAVWEV
      WEUXRVTTZVWIVWKQVWGVWGAUXRVVSWBZUXRUXCUXCYDVPAVWIVWJVVJAVWHUXCUXRNAUXCVGT
      VWHUXCQAUXCVUKUUDUXCUUFXAXTAUXCUXRVWGVWMYEUUGAVVJVWJUXCNAUXRUXCVWMVWGYEYB
      UUHYBAUXTUXCNOZPUXCNOZVWCPAUXTPUXCNAUYAUYBUYCAUYDUYEUYGVUHYCYCXTAVWDVWLVW
      EVWNVWCQVWFVWMVWGUXCUXRUXPYDVPAVWEVWOPQVWGUXCUUNXAUUOUUIAUXFVVNABCDUXPUXR
      UXBUXMUYHUYIUYJUYKHIJKVUGMUUJUUKYFYGYFUULAUWDUWRGSAUVKSTZUIZUVLUWCUWRVWQU
      VLUIZUWBUWRUAUBSSVWRUVMSTZUVNSTZUIZUIZUWBUWRVXBUWBUIZRUVMUKUEZULZUWRRUVNU
      KUEZULZVXCVXEUIZUWQUVLVXHUWPVXEUVMUWHNOZPQZUVQUWLUHOZUVTQZUIZUIVXEUWBUIEF
      UVMUVNSSEUAYOZUWGVXEUWOVXMVXNUWFVXDUWEUVMRUKYHYIVXNUWJVXJUWNVXLVXNUWIVXIP
      UWEUVMUWHNVEXSVXNUWMVXKUVTVXNUWKUVQUWLUHUWEUVMUFUGVEXTXSVAVAFUBYOZVXMUWBV
      XEVXOVXJUVPVXLUWAVXOVXIUVOPUWHUVNUVMNYAXSVXOVXKUVSUVTVXOUWLUVRUVQUHUWHUVN
      UFUGVEYBXSVAUSVXCVWSVXEVWRVWSVWTUWBYJZYKVXBVWTUWBVXEVWRVWSVWTUUMZYLVXHVXE
      UWBVXCVXEYMVXBUWBVXEUUPYFYGVWQUVLVXAUWBVXEYNYFVXCVXGUIZUWQUVLVXRUWPVXGUVN
      UWHNOZPQZUVRUWLUHOZUVTQZUIZUIVXGUVNUVMNOZPQZUVRUVQUHOZUVTQZUIZUIEFUVNUVMS
      SEUBYOZUWGVXGUWOVYCVYIUWFVXFUWEUVNRUKYHYIVYIUWJVXTUWNVYBVYIUWIVXSPUWEUVNU
      WHNVEXSVYIUWMVYAUVTVYIUWKUVRUWLUHUWEUVNUFUGVEXTXSVAVAFUAYOZVYCVYHVXGVYJVX
      TVYEVYBVYGVYJVXSVYDPUWHUVMUVNNYAXSVYJVYAVYFUVTVYJUWLUVQUVRUHUWHUVMUFUGVEY
      BXSVAUSVXBVWTUWBVXGVXQYLZVXCVWSVXGVXPYKZVXRVXGVYEVYGVXCVXGYMVXRVYDUVOPVXR
      UVNUVMVXRUVNVYKWBVXRUVMVYLWBYEVXBUVPUWAVXGYJYPVXRVYFUVSUVTVXRUVRUVQVXRUVR
      VXRUVNUFVYKVUQVXRWPVIZWQVJVXRUVQVXRUVMUFVYLVYMWQVJUUQVXBUVPUWAVXGYQYPUURY
      GVWQUVLVXAUWBVXGYNYFVXCVXDVXGVQVXEVXGUVEVXCVXDVXGVXCVXDUIZVXFRUVNRUGOZUKU
      EZVYNUVMRUGOZVYOUVKVYNUVMVXBVWSUWBVXDVWRVWSVWTUUSYLZVFZVYNUVNVXBVWTUWBVXD
      VXQYLZVFZAVWPUVLVXAUWBVXDUUTZVXCVXDRVYQUKUEZVUTVXCUVMVTTVUEVXDWUCVQWSVXCU
      VMVXPWBVUEVXCVNVIRUVMRYRYSUVFVYNVYQVYOUVKRVYSWUAWUBUYPVYNVHVIVYNUVSVYQRUG
      OZVYORUGOZUHOUVTVYNUVQWUDUVRWUEUHVYNUVMVYNUVMVYRVJVKVYNUVNVYNUVNVYTVJVKVL
      VXBUVPUWAVXDYQVMZVYNUVPVYQVYONOPQZVXBUVPUWAVXDYJVYNVWSVWTVUEUVPWUGVQVYRVY
      TVUEVYNVNVIZUVMUVNRVOVPVRVSWUFUVAVUTVYNUVNVTTVUEVXFVYPVQWSVYNUVNVYTWBWUHR
      UVNRYRYSUVBYTVXDVXGUVCUVDUVGYTUVHUVIUVJVR $.
  $}

  ${
    $d ph a b c d e f i j k l $.  $d A a b c $.  $d B a b c $.  $d C c $.
    $d a b c d e f g h i j k l $.
    nna4b4nsq.a $e |- ( ph -> A e. NN ) $.
    nna4b4nsq.b $e |- ( ph -> B e. NN ) $.
    nna4b4nsq.c $e |- ( ph -> C e. NN ) $.
    $( Strengthening of Fermat's last theorem for exponent 4, where the sum is
       only assumed to be a square.  (Contributed by SN, 23-Aug-2024.) $)
    nna4b4nsq $p |- ( ph -> ( ( A ^ 4 ) + ( B ^ 4 ) ) =/= ( C ^ 2 ) ) $=
      ( cn wcel c4 cexp co caddc c2 wceq wa oveq1 eqeq1d cgcd c1 vc va vb vd ve
      vf vg vh vi vl vj vk cv wn wral crab c0 wrex oveq1d oveq2d ad2antrr simpr
      wne wss 2rspcedvdw ss2rabdv cdvds wbr weq eqeq2d anbi2d 2rexbidv cuz nnuz
      ex cfv eqimssi a1i clt breq2 notbid anbi12d oveq2 simplrl simplrr simpllr
      cbvrex2vw simprl simprrl simprrr flt4lem7 rexlimdvva biimtrid impr simprr
      infdesc simplr jca nnzd gcdcomd eqtrd cn0 nnexpcld nncnd addcomd jca32 wi
      4nn0 wo nnsqcld simp-4r cz 2z 2nn dvdsexp2im mp3an2i 2nn0 flt4lem oveq12d
      imp eqtr3d rppwr syl3anc mpd fltaccoprm flt4lem2 mtod imor sylib mpjaodan
      reximdva con3d ralnex 3imtr4g rabeq0 cdiv w3a flt4lem6 simpld simp3d sylc
      simp1d simp2d cc0 nnne0d divgcdcoprm0 3rspcedvdw rexlimdvaa sseq0 syl2anc
      simprd necon3bbid rspcv ) ADHIBJKLZCJKLZMLZUAUMZNKLZOZUNZUAHUOZUUPDNKLZVC
      ZGAUUSUAHUPZUQOZUVAAUVDUBUMZJKLZUCUMZJKLZMLZUUROZUCHURZUBHURZUAHUPZVDUVNU
      QOZUVEAUUSUVMUAHAUUQHIZPZUUSUVMUVQUUSPUVKUUNUVIMLZUUROUUSUBUCBCHHUVFBOZUV
      JUVRUURUVSUVGUUNUVIMUVFBJKQUSRUVHCOZUVRUUPUURUVTUVIUUOUUNMUVHCJKQUTRABHIU
      VPUUSEVAACHIUVPUUSFVAUVQUUSVBVEVOVFAUDUMZUEUMZSLZTOZUWAJKLZUWBJKLZMLZUFUM
      ZNKLZOZPZUEHURUDHURZUFHUPUQOZUVOANUGUMZVGVHZUNZUWNUHUMZSLZTOZUWNJKLZUWQJK
      LZMLZUWIOZPZPZUHHURUGHURZUFHUPUQOZUWMAUXFUWPUWSUXBUIUMZNKLZOZPZPZUHHURUGH
      URZUWPUWSUXBUJUMZNKLZOZPZPZUHHURUGHURZUIUFUJHTUFUIVIZUXEUXLUGUHHHUXTUXDUX
      KUWPUXTUXCUXJUWSUXTUWIUXIUXBUWHUXHNKQVJVKVKVLUFUJVIZUXEUXRUGUHHHUYAUXDUXQ
      UWPUYAUXCUXPUWSUYAUWIUXOUXBUWHUXNNKQVJVKVKVLHTVMVPZVDAHUYBVNVQVRAUXHHIZUX
      MUXSUXNUXHVSVHPUJHURZUXMNUKUMZVGVHZUNZUYEULUMZSLZTOZUYEJKLZUYHJKLZMLZUXIO
      ZPZPZULHURUKHURAUYCPZUYDUXLUYPUYGUYEUWQSLZTOZUYKUXAMLZUXIOZPZPUGUHUKULHHU
      GUKVIZUWPUYGUXKVUBVUCUWOUYFUWNUYENVGVTWAVUCUWSUYSUXJVUAVUCUWRUYRTUWNUYEUW
      QSQRVUCUXBUYTUXIVUCUWTUYKUXAMUWNUYEJKQUSRWBWBUHULVIZVUBUYOUYGVUDUYSUYJVUA
      UYNVUDUYRUYITUWQUYHUYESWCRVUDUYTUYMUXIVUDUXAUYLUYKMUWQUYHJKQUTRWBVKWGUYQU
      YPUYDUKULHHUYQUYEHIZUYHHIZPZPZUYPUYDVUHUYPPUYEUYHUXHUGUHUJUYQVUEVUFUYPWDU
      YQVUEVUFUYPWEAUYCVUGUYPWFVUHUYGUYOWHVUHUYGUYJUYNWIVUHUYGUYJUYNWJWKVOWLWMW
      NWPAUXFUNUFHUOZUWLUNUFHUOZUXGUWMAUXFUFHURZUNUWLUFHURZUNZVUIVUJAVULVUKAUWL
      UXFUFHAUWHHIZPZUWKUXFUDUEHHVUOUWAHIZUWBHIZPZPZUWKUXFVUSUWKPZNUWAVGVHZUNZU
      XFNUWBVGVHZUNZVUTVVBPZUXEVVBUWAUWQSLZTOZUWEUXAMLZUWIOZPZPVVBUWKPUGUHUWAUW
      BHHUGUDVIZUWPVVBUXDVVJVVKUWOVVAUWNUWANVGVTWAVVKUWSVVGUXCVVIVVKUWRVVFTUWNU
      WAUWQSQRVVKUXBVVHUWIVVKUWTUWEUXAMUWNUWAJKQUSRWBWBUHUEVIZVVJUWKVVBVVLVVGUW
      DVVIUWJVVLVVFUWCTUWQUWBUWASWCRVVLVVHUWGUWIVVLUXAUWFUWEMUWQUWBJKQUTRWBVKVU
      SVUPUWKVVBVUOVUPVUQWHZVAVUSVUQUWKVVBVUOVUPVUQWOZVAVVEVVBUWKVUTVVBVBVUSUWK
      VVBWQWRVEVUTVVDPZUXEVVDUWBUWQSLZTOZUWFUXAMLZUWIOZPZPVVDUWBUWASLZTOZUWFUWE
      MLZUWIOZPZPUGUHUWBUWAHHUGUEVIZUWPVVDUXDVVTVWFUWOVVCUWNUWBNVGVTWAVWFUWSVVQ
      UXCVVSVWFUWRVVPTUWNUWBUWQSQRVWFUXBVVRUWIVWFUWTUWFUXAMUWNUWBJKQUSRWBWBUHUD
      VIZVVTVWEVVDVWGVVQVWBVVSVWDVWGVVPVWATUWQUWAUWBSWCRVWGVVRVWCUWIVWGUXAUWEUW
      FMUWQUWAJKQUTRWBVKVUSVUQUWKVVDVVNVAZVUSVUPUWKVVDVVMVAZVVOVVDVWBVWDVUTVVDV
      BVVOVWAUWCTVVOUWBUWAVVOUWBVWHWSVVOUWAVWIWSWTVUSUWDUWJVVDWDXAVVOVWCUWGUWIV
      VOUWFUWEVVOUWFVVOUWBJVWHJXBIVVOXHVRZXCXDVVOUWEVVOUWAJVWIVWJXCXDXEVUSUWDUW
      JVVDWEXAXFVEVUTVVAVVDXGVVBVVDXIVUTVVAVVDVUTVVAPZVVCNUWBNKLZVGVHZVWKUWANKL
      ZVWLUWHVWKUWAVUSVUPUWKVVAVVMVAZXJZVWKUWBVUSVUQUWKVVAVVNVAZXJZAVUNVURUWKVV
      AXKZVUTVVANVWNVGVHZNXLIZVUTUWAXLINHIZVVAVWTXGXMVUTUWAVUOVUPVUQUWKWDWSVXBV
      UTXNVRNUWANXOXPXTVWKVWNVWLUWHNVWPVWRVWSNXBIVWKXQVRVWKUWGVWNNKLZVWLNKLZMLU
      WIVWKUWEVXCUWFVXDMVWKUWAVWKUWAVWOXDXRVWKUWBVWKUWBVWQXDXRXSVUSUWDUWJVVAWEY
      AZVWKUWDVWNVWLSLTOZVUSUWDUWJVVAWDVWKVUPVUQVXBUWDVXFXGVWOVWQVXBVWKXNVRZUWA
      UWBNYBYCYDYEVXEYFVXAVWKUWBXLIVXBVVCVWMXGXMVWKUWBVWQWSVXGNUWBNXOXPYGVOVVAV
      VDYHYIYJVOWLYKYLUXFUFHYMUWLUFHYMZYNUXFUFHYOUWLUFHYOZYNYDAVUJUVMUNUAHUOZUW
      MUVOAVUMUVMUAHURZUNVUJVXJAVXKVULAUVLVULUAUBHHAUVPUVFHIZPPZUVKVULUCHVXMUVH
      HIZUVKPZPZUWKUWDUWGUUQUVFUVHSLZNKLYPLZNKLZOZPUVFVXQYPLZUWBSLZTOZVYAJKLZUW
      FMLZVXSOZPVYAUVHVXQYPLZSLZTOZVYDVYGJKLZMLZVXSOZPUFUDUEVXRVYAVYGHHHUWHVXRO
      ZUWJVXTUWDVYMUWIVXSUWGUWHVXRNKQVJVKUWAVYAOZUWDVYCVXTVYFVYNUWCVYBTUWAVYAUW
      BSQRVYNUWGVYEVXSVYNUWEVYDUWFMUWAVYAJKQUSRWBUWBVYGOZVYCVYIVYFVYLVYOVYBVYHT
      UWBVYGVYASWCRVYOVYEVYKVXSVYOUWFVYJVYDMUWBVYGJKQUTRWBVXPVYAHIZVYGHIZVXRHIZ
      VXPVYPVYQVYRYQZVYLVXPUVFUVHUUQAUVPVXLVXOWEZVXMVXNUVKWHZAUVPVXLVXOWDVXMVXN
      UVKWOYRZYSZYTVXPVYPVYQVYRWUCUUBVXPVYPVYQVYRWUCUUCVXPVYIVYLVXPUVFXLIUVHXLI
      UVHUUDVCVYIVXPUVFVYTWSVXPUVHWUAWSVXPUVHWUAUUEUVFUVHUUFYCVXPVYSVYLWUBUUKWR
      UUGUUHWLYLVXHUVMUAHYMYNVXIUVMUAHYOYNYDUVDUVNUUIUUJUUSUAHYOYIUUTUVCUADHUUQ
      DOZUUSUUPUVBWUDUURUVBUUPUUQDNKQVJUULUUMUUA $.
  $}

  $(
    fermrtt.a @e |- ( ph -> A e. NN ) @.
    fermrtt.b @e |- ( ph -> B e. NN ) @.
    fermrtt.c @e |- ( ph -> C e. NN ) @.
    @( Fermat's right triangle theorem, which implies Fermat's last theorem for
       exponent 4.  (Contributed by TODO-SN, ??-???-202?.) @)
    fermrtt @p |- ( ph -> ( ( A ^ 4 ) - ( B ^ 4 ) ) =/= ( C ^ 2 ) ) @=
      ? @.
  $)

  $(
    flt4.a @e |- ( ph -> A e. NN ) @.
    flt4.b @e |- ( ph -> B e. NN ) @.
    flt4.c @e |- ( ph -> C e. NN ) @.
    @( Fermat's last theorem for the exponent four.  (Contributed by ??,
       ??-???-????.) @)
    flt4 @p |- ( ph -> ( ( A ^ 4 ) + ( B ^ 4 ) ) =/= ( C ^ 4 ) ) @=
      ? @.
  $)

  ${
    fltltc.a $e |- ( ph -> A e. NN ) $.
    fltltc.b $e |- ( ph -> B e. NN ) $.
    fltltc.c $e |- ( ph -> C e. NN ) $.
    fltltc.n $e |- ( ph -> N e. ( ZZ>= ` 3 ) ) $.
    fltltc.1 $e |- ( ph -> ( ( A ^ N ) + ( B ^ N ) ) = ( C ^ N ) ) $.
    $( ` ( C ^ N ) ` is the largest term and therefore ` B < C ` .
       (Contributed by Steven Nguyen, 22-Aug-2023.) $)
    fltltc $p |- ( ph -> B < C ) $=
      ( clt wbr cexp co cmin nncnd c3 wcel expcld nnrpd cuz cn eluz3nn mvlladdd
      cfv nnnn0d nnred reexpcld nnzd rpexpcld ltsubrpd eqbrtrd ltexp1d mpbird
      syl ) ACDKLCEMNZDEMNZKLAUPUQBEMNZONUQKAURUPUQABEABFPAEAEQUAUEREUBRIEUCUOZ
      UFZSACEACGPUTSJUDAUQURADEADHUGUTUHABEABFTAEUSUIUJUKULACDEACGTADHTUSUMUN
      $.

    $d N k $.  $d B k $.  $d C k $.  $d ph k $.
    $( Lemma for ~ fltnlta .  A lower bound for ` A ` based on ~ pwdif .
       (Contributed by Steven Nguyen, 22-Aug-2023.) $)
    fltnltalem $p |- ( ph -> (
        ( C - B ) x. ( ( C ^ ( N - 1 ) ) + ( ( N - 1 ) x. ( B ^ ( N - 1 ) ) ) )
                                                             ) < ( A ^ N ) ) $=
      ( vk cmin co c1 cexp cmul caddc cc0 wcel adantr clt cfzo cv csu nnred cuz
      c3 cfv cn cn0 eluz3nn nnm1nn0 reexpcld nn0red remulcld readdcld cfn fzofi
      3syl a1i wa cr elfzonn0 adantl fzonnsub syl fsumrecl wbr crp fltltc difrp
      syl2anc mpbid nnnn0d simpr 1nn0 elfzoext sylancl wceq nnnn0 nn0cnd subcld
      wb 1cnd npcand oveq2d eleqtrd c2 cc sub1m1 uz3m2nn eqeltrd nncnd uzuzle23
      cle uz2m1nn expm1t eqcomd expcld adddirp1d oveq1d 3eqtr2rd eqled sumeq2dv
      pncan3d expaddd chash fsumconst hashfzo0 eqtrd 3eqtr3d nnrpd rpge0d ltled
      breqtrrd expge0d leexp1a syl32anc lemul1ad fsumle ltexp1dd lelttrd nncand
      ltmul1dd leltaddd exp1d cz 0zd peano2zd 0cn ax-1cn addassi addcli addlidi
      eluzp1m1 mulcld oveq2 oveq12d nn0zd fzosumm1 1p1e2 3eqtri fveq2d eleqtrrd
      ltadd2dd fsumcl addcomd sub32d nnncand subidd exp0d recnd mulridd elnn0uz
      sylib ltmul2dd pwdif syl3anc mvlraddd ) ADCLMZDENLMZOMZUVACUVAOMZPMZQMZPM
      ZDEOMZCEOMZLMZBEOMZUAAUVFUUTREUBMZDKUCZOMZCEUVLLMZNLMZOMZPMZKUDZPMZUVIUAA
      UVEUVRUUTAUVBUVDADUVAADHUEZAEUGUFUHSZEUISZUVAUJSZIEUKZEULUSZUMZAUVAUVCAUV
      AUWEUNACUVAACGUEZUWEUMUOZUPAUVKUVQKUVKUQSAREURUTAUVLUVKSZVAZUVMUVPUWJDUVL
      ADVBSZUWIUVTTUWIUVLUJSZAUVLEVCVDZUMUWJCUVOACVBSZUWIUWGTUWJUVNUISZUVOUJSUW
      IUWOAUVLREVEVDUVNULVFZUMUOVGACDUAVHZUUTVISZABCDEFGHIJVJZAUWNUWKUWQUWRWCUW
      GUVTCDVKVLVMAUVERUVAUBMZUVQKUDZUVBCEUVALMZNLMZOMZPMZQMZUVRUAAUVEUWTUVMCUV
      AUVLLMZOMZPMZKUDZUVBQMZUXFUAAUVEUVBUXJQMUXKUAAUVDUXJUVBUWHAUWTUXIKUWTUQSA
      RUVAURUTZAUVLUWTSZVAZUVMUXHUXNDUVLAUWKUXMUVTTUXMUWLAUVLUVAVCZVDZUMUXNCUXG
      AUWNUXMUWGTUXMUXGUJSZAUXMUXGUVLRUVAVEVNZVDZUMUOVGUWFAUVDRUVANLMZUBMZUXIKU
      DZDUXTOMZCUVAUXTLMZOMZPMZQMZUXJUAAUVDUYBUYCCPMZQMZUYGUAAUVDUYACUVLOMZUXHP
      MZKUDZCUXTOMZCPMZQMZUYIUWHAUYLUYNAUYAUYKKUYAUQSZARUXTURUTZAUVLUYASZVAZUYJ
      UXHUYSCUVLAUWNUYRUWGTZUYRUWLAUVLUXTVCVDZUMZUYSCUXGUYTUYSUXMUXQUYSUVLRUXTN
      QMZUBMZUWTUYSUYRNUJSUVLVUDSAUYRVOVPNRUXTUVLVQVRAVUDUWTVSUYRAVUCUVARUBAUVA
      NAENAEAUWAUWBEUJSZIUWDEVTUSZWAZAWDZWBZVUHWEZWFTWGZUXRVFZUMZUOZVGZAUYMCACU
      XTUWGAUXTAUXTEWHLMZUIAEWISZUXTVUPVSVUGEWJVFAUWAVUPUISIEWKVFWLZVNZUMZUWGUO
      ZUPAUYBUYHAUYAUXIKUYQUYSUVMUXHUYSDUVLAUWKUYRUVTTZVUAUMZVUMUOZVGZAUYCCADUX
      TUVTVUSUMZUWGUOZUPAUVDUXTUVCPMZUYNQMZUYOWOAUVDVVIUWHAVVIVVHUVCQMVUCUVCPMU
      VDAUYNUVCVVHQAUVCUYNACWISZUVAUISZUVCUYNVSACGWMZAEWHUFUHZSZVVKAUWAVVNIEWNV
      FZEWPVFCUVAWQVLWRWFAUXTUVCAUVANVUIVUHWBACUVAVVLUWEWSZWTAVUCUVAUVCPVUJXAXB
      XCAUYLVVHUYNQAUYACUVLUXGQMZOMZKUDUYAUVCKUDZUYLVVHAUYAVVRUVCKUYSVVQUVACOUY
      SUVLUVAUYSUXMUVLWISZVUKUXMUVLUXOWAZVFAUVAWISUYRVUITXEWFXDAUYAVVRUYKKUYSCU
      VLUXGAVVJUYRVVLTVULVUAXFXDAVVSUYAXGUHZUVCPMZVVHAUYPUVCWISVVSVWCVSUYQVVPUY
      AUVCKXHVLAVWBUXTUVCPAUXTUJSVWBUXTVSVUSUXTXIVFXAXJXKXAXOAUYLUYNUYBUYHVUOVV
      AVVEVVGAUYAUYKUXIKUYQVUNVVDUYSUYJUVMUXHVUBVVCVUMUYSCUXGUYTVULARCWOVHZUYRA
      CACGXLZXMTZXPUYSUWNUWKUWLVWDCDWOVHZUYJUVMWOVHUYTVVBVUAVWFAVWGUYRACDUWGUVT
      UWSXNTCDUVLXQXRXSXTAUYMUYCCVUTVVFVWEACDUXTVWEADHXLVURUWSYAYDYEYBAUYFUYHUY
      BQAUYECUYCPAUYECNOMCAUYDNCOAUVANVUIVUHYCWFACVVLYFXJWFWFXOAUXIUYFKRUVAARYG
      SUVARNQMZUFUHSZUXTRUFUHZSAYHZAVWHYGSEVWHNQMZUFUHZSVWIARVWKYIAEVVMVWMVVOAV
      WLWHUFVWLWHVSAVWLRNNQMZQMVWNWHRNNYJYKYKYLVWNNNYKYKYMYNUUAUUBUTUUCUUDVWHEY
      OVLRUVAYOVLUXNUVMUXHUXNDUVLADWISZUXMADHWMZTUXPWSUXNCUXGAVVJUXMVVLTUXSWSYP
      ZUVLUXTVSZUVMUYCUXHUYEPUVLUXTDOYQVWRUXGUYDCOUVLUXTUVALYQWFYRAUVAUWEYSYTXO
      UUEAUXJUVBAUWTUXIKUXLVWQUUFADUVAVWPUWEWSUUGXOAUXAUXJUXEUVBQAUWTUVQUXIKUXN
      UVPUXHUVMPUXNUVOUXGCOUXNEUVLNAVUQUXMVUGTUXMVVTAVWAVDUXNWDUUHWFWFXDAUXEUVB
      NPMUVBAUXDNUVBPAUXDCROMNAUXCRCOAUXCEELMRAEENVUGVUGVUHUUIAEVUGUUJXJWFACVVL
      UUKXJWFAUVBAUVBUWFUULUUMXJYRXOAUVQUXEKREAUWCUVAVWJSUWEUVAUUNUUOUWJUVMUVPU
      WJDUVLAVWOUWIVWPTUWMWSUWJCUVOAVVJUWIVVLTUWPWSYPUVLUVAVSZUVMUVBUVPUXDPUVLU
      VADOYQVWSUVOUXCCOVWSUVNUXBNLUVLUVAELYQXAWFYRAEVUFYSYTXOUUPAVUEVWOVVJUVIUV
      SVSVUFVWPVVLDCKEUUQUURXOAUVJUVHUVGABEABFWMVUFWSACEVVLVUFWSJUUSXO $.

    $( Since ` A =/= B ` by ~ fltne , we may assume ` A < B ` without loss of
       generality.  TODO-SN: Remove hypothesis.  Also, generalize this thanks
       to ~ https://youtu.be/EymVXkPWxyc&lc=Ugzns5rcAoyB9z2LKJ14AaABAg . $)
    fltnlta.1 $e |- ( ph -> A < B ) $.
    $( In a Fermat counterexample, the exponent ` N ` is less than all three
       numbers ( ` A ` , ` B ` , and ` C ` ).  Note that ` A < B ` (hypothesis)
       and ` B < C ` ( ~ fltltc ).  See ~ https://youtu.be/EymVXkPWxyc for an
       outline.  (Contributed by SN, 24-Aug-2023.) $)
    fltnlta $p |- ( ph -> N < A ) $=
      ( co c1 cexp cmul caddc cdiv wcel nnred remulcld cmin cuz cfv eluz3nn syl
      c3 cn resubcld c2 uzuzle23 uz2m1nn 3syl nnnn0d reexpcld readdcld rpexpcld
      nnrpd nnzd rerpdivcld clt 1cnd nncnd recnd adddird pncan3d oveq1d mullidd
      cr 3eqtr3rd oveq2d eqeltrrd nn0ge0d 1red wbr cle fltltc wb nnltp1le mpbid
      syl2anc leidd lesub3d rpred mulassd mulcld nnne0d expne0d divcan4d eqtr3d
      lemulge12d crp difrp ltexp1dd ltmul2dd ltdiv1dd eqbrtrrd lelttrd breqtrrd
      ltadd1dd lttrd fltnltalem nncand expsubd exp1d 3eqtr3d breqtrd ) AEDCUALZ
      DEMUALZNLZXHCXHNLZOLZPLZOLZBXHNLZQLZBAEAEUFUBUCRZEUGRIEUDUEZSZAXMXNAXGXLA
      DCADHSZACGSZUHZAXIXKADXHXSAXHAXPEUIUBUCRXHUGRIEUJEUKULZUMZUNZAXHXJAXHYBSA
      CXHXTYCUNZTZUOZTZABXHABFUQZAXHYBURZUPZUSZABFSZAEXGXJXKPLZOLZXNQLZXOXRAYOX
      NAXGYNYAAXJXKYEYFUOZTZYKUSZYLAEXGEXJOLZOLZXNQLZYPUTAEXGEOLZUUBXRAXGEYAXRT
      AYPUUBVHAYOUUAXNQAYNYTXGOAMXHPLZXJOLMXJOLZXKPLYTYNAMXHXJAVAZAXHYBVBAXJYEV
      CZVDAUUDEXJOAMEUUFAEXQVBZVEVFAUUEXJXKPAXJUUGVGVFVIZVJZVFZYSVKAEXGXRYAAEAE
      XQUMZVLADCMCXSXTAVMXTACDUTVNZCMPLDVOVNZABCDEFGHIJVPZACUGRDUGRUUMUUNVQGHCD
      VRVTVSACXTWAWBWJAXGEXNOLZOLZXNQLZUUCUUBUTAUUCXNOLZXNQLUURUUCAUUSUUQXNQAXG
      EXNAXGYAVCZUUHAXNAXNYKWCZVCZWDVFAUUCXNAXGEUUTUUHWEUVBABXHABFVBZABFWFZYJWG
      WHWIAUUQUUAXNAXGUUPYAAEXNXRUVATZTAYOUUAVHUUJYRVKYKAUUPYTXGUVEAYNYTVHUUIYQ
      VKAUUMXGWKRZUUOACVHRDVHRUUMUVFVQXTXSCDWLVTVSZAXNXJEUVAYEAEXQUQABCXHYIACGU
      QZYBKWMWNWNWOWPWQUUKWRAYOXMXNYRYHYKAYNXLXGYQYGUVGAXJXIXKYEYDYFACDXHUVHADH
      UQYBUUOWMWSWNWOWTAXOBENLZXNQLZBUTAXMUVIXNYHABEYMUULUNYKABCDEFGHIJXAWOABEX
      HUALZNLBMNLUVJBAUVKMBNAEMUUHUUFXBVJABEXHUVCUVDYJAEXQURXCABUVCXDXEXFWT $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Exemplar theorems
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  These theorems were added for illustration or pedagogical purposes without
  the intention of being used, but some may still be moved to main and used,
  of course.

$)

  ${
    iddii.1 $e |- ph $.
    iddii.2 $e |- ps $.
    $( Version of ~ a1ii with the hypotheses switched.  The first hypothesis is
       redundant so this theorem should not normally appear in a proof.
       Inference associated with ~ idd .  (Contributed by SN, 1-Apr-2025.)
       (New usage is discouraged.) $)
    iddii $p |- ps $=
      (  ) D $.
  $}

  ${
    bicomdALT.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Alternate proof of ~ bicomd which is shorter after expanding all parent
       theorems (as of 8-Aug-2024, ~ bicom depends on ~ bicom1 and ~ sylib
       depends on ~ syl ).  Additionally, the labels ~ bicom1 and ~ syl happen
       to contain fewer characters than ~ bicom and ~ sylib .  However, neither
       of these conditions count as a shortening according to ~ conventions .
       In the first case, the criteria could easily be broken by upstream
       changes, and in many cases the upstream dependency tree is nontrivial
       (see ~ orass and ~ pm2.31 ).  For the latter case, theorem labels are up
       to revision, so they are not counted in the size of a proof.
       (Contributed by SN, 21-May-2022.)  (New usage is discouraged.)
       (Proof modification is discouraged.) $)
    bicomdALT $p |- ( ph -> ( ch <-> ps ) ) $=
      ( wb bicom1 syl ) ABCECBEDBCFG $.
  $}

  $( Alias for ~ 19.26 for easier lookup.  (Contributed by SN, 12-Aug-2025.)
     (New usage is discouraged.) $)
  alan $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ A. x ps ) ) $=
    ( 19.26 ) ABCD $.

  $( Alias for ~ 19.43 for easier lookup.  (Contributed by SN, 5-Jul-2025.)
     (New usage is discouraged.) $)
  exor $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ E. x ps ) ) $=
    ( 19.43 ) ABCD $.

  $( Alias for ~ r19.43 for easier lookup.  (Contributed by SN, 5-Jul-2025.)
     (New usage is discouraged.) $)
  rexor $p |-
    ( E. x e. A ( ph \/ ps ) <-> ( E. x e. A ph \/ E. x e. A ps ) ) $=
    ( r19.43 ) ABCDE $.

  $( Alternate proof of ~ ruv with one fewer syntax step thanks to using
     ~ elirrv instead of ~ elirr .  However, it does not change the compressed
     proof size or the number of symbols in the generated display, so it is not
     considered a shortening according to ~ conventions .  (Contributed by SN,
     1-Sep-2024.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  ruvALT $p |- { x | x e/ x } = _V $=
    ( cvv cv wnel cab wcel vex elirrv nelir 2th eqabi eqcomi ) BACZMDZAENABMBFN
    AGMMAHIJKL $.

  $( Alternative to ~ wcdeq and ~ df-cdeq .  This flattens the syntax
     representation ( wi ( weq vx vy ) wph ) to ( sn-wcdeq vx vy wph ),
     illustrating the comment of ~ df-cdeq .  (Contributed by SN, 26-Sep-2024.)
     (New usage is discouraged.) $)
  sn-wcdeq $p wff ( x = y -> ph ) $=
    ( weq wi ) BCDAE $.

  $( 45 squared is 2025.  (Contributed by SN, 30-Mar-2025.) $)
  sq45 $p |- ( ; 4 5 ^ 2 ) = ; ; ; 2 0 2 5 $=
    ( c4 c5 cdc c2 cexp co cmul cc0 4nn0 5nn0 deccl nn0cni sqvali 4t5e20 sqn5ii
    4p1e5 eqtri ) ABCZDEFRRGFDHCZDCBCRRABIJKLMABSIPNOQ $.

  $( The sum of the first nine perfect cubes is 2025.  (Contributed by SN,
     30-Mar-2025.) $)
  sum9cubes $p |- sum_ k e. ( 1 ... 9 ) ( k ^ 3 ) = ; ; ; 2 0 2 5 $=
    ( c1 c9 co cexp csu c2 c4 c5 cdc cc0 wceq 9nn0 ax-mp caddc cdiv cmul oveq1i
    c8 1nn0 cfz cv c3 cn0 wcel sumcubes arisum 8nn0 sq9 8p1e9 9cn ax-1cn 9p1e10
    addcomli decaddci2 2nn0 4nn0 5nn0 eqid 0nn0 4t2e8 eqtri 5t2e10 eqtr4i deccl
    decmul1c nn0cni 2cn 2ne0 divcan4i 3eqtri sq45 ) BCUADZAUBZUCEDAFZVMVNAFZGED
    ZHIJZGEDGKJGJIJCUDUEZVOVQLMACUFNVPVRGEVPCGEDZCODZGPDZVRGQDZGPDVRVSVPWBLMACU
    GNWAWCGPWACKJWCSBCVTCUHTMUIUJCBBKJUKULUMUNUOHICKGBVRUPUQURVRUSUTTHGQDZBODSB
    ODCWDSBOVARUJVBVCVFVDRVRGVRHIUQURVEVGVHVIVJVKRVLVK $.

  ${
    $d s t w u v f S $.  $d s t w u v f T $.  $d u v f t s X $.
    $d u v f s t .+ $.  $d u v f s t Y $.  $d u v f s t .+^ $.
    $d u v f s t F $.
    sn-isghm.w $e |- X = ( Base ` S ) $.
    sn-isghm.x $e |- Y = ( Base ` T ) $.
    sn-isghm.a $e |- .+ = ( +g ` S ) $.
    sn-isghm.b $e |- .+^ = ( +g ` T ) $.
    $( Longer proof of ~ isghm , unsuccessfully attempting to simplify ~ isghm
       using ~ elovmpo according to an editorial note (now removed).
       (Contributed by SN, 7-Jun-2025.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    sn-isghm $p |- ( F e. ( S GrpHom T ) <->
         ( ( S e. Grp /\ T e. Grp ) /\ ( F : X --> Y /\ A. u e. X A. v e. X
               ( F ` ( u .+ v ) ) = ( ( F ` u ) .+^ ( F ` v ) ) ) ) ) $=
      ( vf wcel cfv wceq wral cbs cvv vw vt vs cghm co cgrp cv wf wa cab cplusg
      wsbc df-ghm fvex feq2 raleq raleqbi1dv anbi12d sbcie abbii fsetex abanssl
      w3a ax-mp ssexi eqeltri fveq2 adantr adantl feq23d oveqd fveq2d eqeqan12d
      eqtr4di raleqbidv abbidv eqtrid elovmpo fex2 mp3an23 feq1 oveq12d eqeq12d
      fvexi fveq1 2ralbidv elab3 3anbi3i df-3an 3bitri ) GEFUDUEOEUFOZFUFOZGHIN
      UGZUHZBUGZAUGZCUEZWMPZWOWMPZWPWMPZDUEZQZAHRZBHRZUIZNUJZOZVCWKWLHIGUHZWQGP
      ZWOGPZWPGPZDUEZQZAHRBHRZUIZVCWKWLUIXOUIUFUFUAUGZUBUGZSPZWMUHZWOWPUCUGZUKP
      ZUEZWMPZWSWTXQUKPZUEZQZAXPRZBXPRZUIZUAXTSPZULZNUJZUDXFGEFUCUBBAUAUBNUCUMY
      LYJXRWMUHZYFAYJRZBYJRZUIZNUJZTYKYPNYIYPUAYJXTSUNXPYJQXSYMYHYOXPYJXRWMUOYG
      YNBXPYJYFAXPYJUPUQURUSUTZYQYMNUJZXRTOYSTOXQSUNYJXRNTVAVDYMYONVBVEVFXTEQZX
      QFQZUIZYLYQXFYRUUBYPXENUUBYMWNYOXDUUBYJXRHIWMYTYJHQUUAYTYJESPHXTESVGJVNVH
      ZUUAXRIQYTUUAXRFSPIXQFSVGKVNVIVJUUBYNXCBYJHUUCUUBYFXBAYJHUUCYTUUAYCWRYEXA
      YTYBWQWMYTYACWOWPYTYAEUKPCXTEUKVGLVNVKVLUUAYDDWSWTUUAYDFUKPDXQFUKVGMVNVKV
      MVOVOURVPVQVRXGXOWKWLXEXONGTXHGTOZXNXHHTOITOUUDHESJWDIFSKWDHIGTTVSVTVHWMG
      QZWNXHXDXNHIWMGWAUUEXBXMBAHHUUEWRXIXAXLWQWMGWEUUEWSXJWTXKDWOWMGWEWPWMGWEW
      BWCWFURWGWHWKWLXOWIWJ $.
  $}

  $( An abuse of notation.  (Contributed by Prof.  Loof Lirpa, 1-Apr-2025.)
     (New usage is discouraged.)  (Proof modification is discouraged.) $)
  aprilfools2025 $p |- { <" A p r i l "> , <" f o o l s ! "> } e. _V $=
    ( cN ve vv cv cs5 cs4 cs3 cs2 cs6 cfa cvv wcel vg vn va vy vu vt vd vw prex
    cword cpr s4cli iddii ) IJLZKLZUNFLZMZUALZDLZUBLZUTUCLZMZURCLZUOUNNUDLZUSUE
    LZOZVEGLZPMZUQVBHLZUNUFLZOVFUGLZUSUHLUTNMZUQVBVJVEUPUTNVAUPUSVEUTVKQVAUTVKO
    MZVKUNELZUNUPVJQVDUSVERNPZNSUJTAVGUPVCVIMZBLUSUSVIVNRQZUKSTVHVLVMVOULVPVQUI
    UM $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Standard replacements of ax-10 , ax-11 , ax-12
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  It is known that ~ ax-10 , ~ ax-11 , and ~ ax-12 are logically redundant in
  a weak sense.  Practically, they can be replaced with ~ hbn1w , ~ alcomimw ,
  and ~ ax12wlem as long as you can fully substitute ` y ` for ` x ` in the
  relevant wff (that is, ` x ` cannot appear in the wff after substituting).

  This strategy (which I will call a "standard replacement" of axioms) has a
  lot of potential, for example it works with ~ df-fv and ~ df-mpt , two very
  common constructions.  But doing a standard replacement of ~ ax-10 ,
  ~ ax-11 , and ~ ax-12 takes unsatisfyingly long.  Usually, if another
  approach is found, that approach is shorter and better.

$)

  ${
    $d x y $.  $d ph y $.  $d ps x $.
    nfa1w.x $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Replace ~ ax-10 in ~ nfa1 with a substitution hypothesis.  (Contributed
       by SN, 2-Sep-2025.) $)
    nfa1w $p |- F/ x A. x ph $=
      ( wal cbvalvw nfv nfxfr ) ACFBDFZCABCDEGJCHI $.
    $( $j usage 'nfa1w' avoids 'ax-10'; $)
  $}

  ${
    $d x y z $.  $d x ps $.  $d x th $.  $d y z ph $.
    eu6w.x $e |- ( x = z -> ( ph <-> ps ) ) $.
    eu6w.y $e |- ( x = y -> ( ph <-> th ) ) $.
    $( Replace ~ ax-10 , ~ ax-12 in ~ eu6 with substitution hypotheses.
       (Contributed by SN, 27-May-2025.) $)
    eu6w $p |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) ) $=
      ( wex weq wb wal wa wi wn alimi imbi2d 19.8aw syl eximi weu pm2.21 sylbir
      alnex equequ2 albidv biimp wnf equequ1 imbi12d nfa1w bibi12d nfim cbvalvw
      ja 19.38b imbi12i a1i spw nfrd syl5 impbid2 bitr3d ax-mp ax12wlem embantd
      id com12 ancld albiim imbitrrdi mpgbi eximdv impbii anbi2i 3bitr4ri ancom
      abai eu3v biimpr exsbim biantru 3bitr4i bitri ) ADUAZADIZADEJZKZDLZEIZMZW
      JWFWFWJNZMWFAWGNZDLZEIZMWKWEWLWOWFWLWOWFWJWOWFOZWNWOWPAOZDLWNADUDWQWMDAWG
      UBPUCWNADFJZNZDLEFEFJZWMWSDWTWGWRAEFDUEQUFRSWIWNEWHWMDAWGUGPTUOWFWOWJWFWN
      WIEAWNWINZNZWFXANZDXADUHZXBDLZXCKWNWIDWMBFEJZNZDFWRABWGXFGDFEUIZUJZUKWHBX
      FKZDFWRABWGXFGXHULZUKUMXDWFXADLZNXEXCAXADUPXDXLXAWFXDXLXAXAXGFLZXJFLZNZDF
      XAXOKWRWNXMWIXNWMXGDFXIUNWHXJDFXKUNUQURZUSXAXADIXDXLXAXODFXPRXDXADXDVGUTV
      AVBQVCVDAWNWNWGANZDLZMWIAWNXRWNWMAXRWMXGDFXIUSAAWGXRAVGWGAXRACDEHVEVHVFVA
      VIAWGDVJVKVLVMVHVNVOWFWJVRADEVSVPWJWFMWJWJWFNZMWKWJWJWFVRWFWJVQXSWJWJXREI
      WFWIXREWHXQDAWGVTPTADEWASWBWCWD $.
    $( $j usage 'eu6w' avoids 'ax-10' 'ax-11' 'ax-12'; $)
  $}

  ${
    $d x y $.  $d x th $.  $d x ch $.  $d y ph $.  $d y ps $.
    abbibw.ph $e |- ( x = y -> ( ph <-> th ) ) $.
    abbibw.ps $e |- ( x = y -> ( ps <-> ch ) ) $.
    $( Replace ~ ax-10 , ~ ax-11 , ~ ax-12 in ~ abbib with substitution
       hypotheses.  (Contributed by SN, 27-May-2025.) $)
    abbibw $p |- ( { x | ph } = { x | ps } <-> A. x ( ph <-> ps ) ) $=
      ( cab wceq cv wcel wb wal dfcleq vex elab bibi12i albii weq bicomd 3bitri
      bibi12d equcoms cbvalvw ) AEIZBEIZJFKZUFLZUHUGLZMZFNDCMZFNABMZENFUFUGOUKU
      LFUIDUJCADEUHFPZGQBCEUHUNHQRSULUMFEULUMMEFEFTZUMULUOADBCGHUCUAUDUEUB $.
    $( $j usage 'abbibw' avoids 'ax-10' 'ax-11' 'ax-12'; $)
  $}

  ${
    $d y ph $.  $d x ps $.  $d x y Y $.
    absnw.y $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Replace ~ ax-10 , ~ ax-11 , ~ ax-12 in ~ absn with a substitution
       hypothesis.  (Contributed by SN, 27-May-2025.) $)
    absnw $p |- ( { x | ph } = { Y } <-> A. x ( ph <-> x = Y ) ) $=
      ( cab csn wceq cv wb wal df-sn eqeq2i eqeq1 abbibw bitri ) ACGZEHZIRCJZEI
      ZCGZIAUAKCLSUBRCEMNAUADJZEIBCDFTUCEOPQ $.
    $( $j usage 'absnw' avoids 'ax-10' 'ax-11' 'ax-12'; $)

    $d th x $.  $d ph z $.  $d x y z $.
    euabsn2w.z $e |- ( x = z -> ( ph <-> th ) ) $.
    $( Replace ~ ax-10 , ~ ax-11 , ~ ax-12 in ~ euabsn2 with substitution
       hypotheses.  (Contributed by SN, 27-May-2025.) $)
    euabsn2w $p |- ( E! x ph <-> E. y { x | ph } = { y } ) $=
      ( weu weq wb wal wex cab cv csn wceq eu6w absnw exbii bitr4i ) ADIADEJKDL
      ZEMADNEOZPQZEMACBDEFHGRUDUBEACDFUCHSTUA $.
    $( $j usage 'euabsn2w' avoids 'ax-10' 'ax-11' 'ax-12'; $)
  $}


$( (End of Steven Nguyen's mathbox.) $)
