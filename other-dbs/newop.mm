$[ set.mm $]


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Alternate ordered pairs
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c << >> XX. $.

  cnewop $a class << A , B >> $.
  cnewxp $a class ( A XX. B ) $.

  df-newop $a |- << A , B >> = { { A } , { A , { B } } } $.

  ${ $d A x y z $. $d B x y z $.
     df-newxp $a |- ( A XX. B ) = { z | E. x e. A E. y e. B z = << x , y >> } $.
  $}

  newopex $p |- << A , B >> e. _V $=
    ( cnewop csn cpr cvv df-newop prex eqeltri ) ABCADZABDEZEFABGJKHI $.
    $( [?] $) $( [22-Mar-2012] $)

  newopeq1 $p |- ( A = B -> << A , C >> = << B , C >> ) $=
    ( wceq csn cpr cnewop sneq preq1 syl preq2 eqtrd df-newop 3eqtr4g ) ABDZAEZ
    ACEZFZFZBEZBQFZFZACGBCGOSTRFZUBOPTDSUCDABHPTRIJORUADUCUBDABQIRUATKJLACMBCMN
    $.
    $( [?] $) $( [22-Mar-2012] $)

  newopeq2 $p |- ( A = B -> << C , A >> = << C , B >> ) $=
    ( wceq csn cpr cnewop sneq preq2 3syl df-newop 3eqtr4g ) ABDZCEZCAEZFZFZNCB
    EZFZFZCAGCBGMORDPSDQTDABHORCIPSNIJCAKCBKL $.
    $( [?] $) $( [22-Mar-2012] $)

  newopeq12 $p |- ( ( A = B /\ C = D ) -> << A , C >> = << B , D >> ) $=
    ( wceq cnewop newopeq1 newopeq2 sylan9eq ) ABECDEACFBCFBDFABCGCDBHI $.
    $( [?] $) $( [22-Mar-2012] $)

  newopth1sn $p |- ( << A , B >> = << C , D >> -> { A } = { C } ) $=
    ( cnewop wceq csn cpr df-newop eqeq12i wa wo snex prex preq12b pm3.26 wss 
    snsspr1 sseq2 mpbii adantl mpbiri adantr eqssd jaoi sylbi ) ABEZCDEZFAGZABG
    ZHZHZCGZCDGZHZHZFZUIUMFZUGULUHUPABICDIJUQURUKUOFZKZUIUOFZUKUMFZKZLURUIUKUMU
    OAMAUJNCMCUNNOUTURVCURUSPVCUIUMVBUIUMQZVAVBUIUKQVDAUJRUKUMUISTUAVAUMUIQZVBV
    AVEUMUOQCUNRUIUOUMSUBUCUDUEUFUF $.
    $( [?] $) $( [22-Mar-2012] $)

  newopth2sn $p |- ( << A , B >> = << C , D >> -> { B } = { D } ) $=
    ( csn wceq cnewop newopth1sn cpr preq1 cun uneq1 df-pr 3eqtr4g preq2 syl 
    eqtrd df-newop syl5eq a1i eqeq12d prex preqr2 snex syl6bi mpcom ) AEZCEZFZA
    BGZCDGZFZBEZDEZFZABCDHUIULUHCUMIZIZUHCUNIZIZFZUOUIUJUQUKUSUIUGAUMIZIZUQUJUI
    VBUHVAIZUQUGUHVAJUIVAUPFVCUQFUIUGUMEZKUHVDKVAUPUGUHVDLAUMMCUMMNVAUPUHOPQABR
    SUKUSFUICDRTUAUTUPURFUOUPURUHCUMUBCUNUBUCUMUNCBUDDUDUCPUEUF $.
    $( [?] $) $( [22-Mar-2012] $)

  newopth1 $p |- ( A e. X -> ( << A , B >> = << C , D >> -> A = C ) ) $=
    ( wcel csn wceq cnewop sneqrg newopth1sn syl5 ) AEFAGCGHACHABICDIHACEJABCDK
    L $.
    $( [?] $) $( [22-Mar-2012] $)

  newopth2 $p |- ( B e. X -> ( << A , B >> = << C , D >> -> B = D ) ) $=
    ( wcel csn wceq cnewop sneqrg newopth2sn syl5 ) BEFBGDGHBDHABICDIHBDEJABCDK
    L $.
    $( [?] $) $( [22-Mar-2012] $)

  newopthg $p |- ( ( A e. X /\ B e. Y ) -> 
  	      	   ( << A , B >> = << C , D >> <-> ( A = C /\ B = D ) ) ) $=
    ( wcel wa cnewop wceq newopth1 newopth2 anim12ii newopeq12 impbid1 ) AEGZBF
    GZHABICDIJZACJZBDJZHPRSQTABCDEKABCDFLMACBDNO $.
    $( [?] $) $( [22-Mar-2012] $)

  ${ $d A x y z $. $d B x y z $. $d X x y z $. $d Y x y z $.
     newopelnewxp $p |- ( << X , Y >> e. ( A XX. B ) <-> 
     ( X e. A /\ Y e. B ) ) $=
       ( vx vy vz cnewop cnewxp wcel cv wceq wrex wa newopex eqeq2 eqcom 
       syl5bb 2rexbidv df-newxp elab2 cvv wb visset newopthg mp2an 2rexbii 
       eleq1 bi2anan9 biimpcd r19.23aivv eqid pm3.2i eqeq1 anbi1d anbi2d 
       rcla42ev mp3an3 impbii 3bitri ) CDHZABIZJEKZFKZHZVALZFBMEAMZVCCLZVDDLZNZ
       FBMEAMZCAJZDBJZNZGKZVELZFBMEAMVGGVAVBCDOVOVALZVPVFEFABVQVEVOLVFVPVOVAVEP
       VOVEQRSEFGABTUAVFVJEFABVCUBJVDUBJVFVJUCEUDFUDVCVDCDUBUBUEUFUGVKVNVJVNEFA
       BVJVCAJZVDBJZNVNVHVRVLVIVSVMVCCAUHVDDBUHUIUJUKVLVMCCLZDDLZNZVKVTWACULDUL
       UMVJWBVTVINEFCDABVHVHVTVIVCCCUNUOVIVIWAVTVDDDUNUPUQURUSUT $.
       $( [?] $) $( [22-Mar-2012] $)
  $}
