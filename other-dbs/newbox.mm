  $( A biconditional in the antecedent is the same as two implications $)
  biimpexp $p |- ( ( ( ph <-> ps ) -> ch ) <-> 
  	      	   ( ( ph -> ps ) -> ( ( ps -> ph ) -> ch ) ) ) $=
    ( wb wi wa dfbi2 imbi1i impexp bitri ) ABDZCEABEZBAEZFZCELMCEEKNCABGHLMCIJ 
    $.
    $( [?] $) $( [12-Dec-2010] $)

 $( A version of ~ ax-ext for use with defined equality $)
  axextdfeq $p |- E. z ( ( z e. x -> z e. y ) ->
   	      	   ( ( z e. y -> z e. x ) -> ( x e. w -> y e. w ) ) ) 
	$=
      ( wel wb wi wex weq axextnd ax-13 imim2i 19.22i ax-mp biimpexp exbii 
      mpbi ) CAEZCBEZFZADEBDEGZGZCHZRSGSRGUAGGZCHTABIZGZCHUCCABJUFUBCUEUATABDKL
      MNUBUDCRSUAOPQ $.
      $( [?] $) $( [12-Dec-2010] $)

 $( A version of ~ ax-13 for use with defined equality $)
  ax13dfeq $p |- E. z ( ( z e. x -> z e. y ) -> ( w e. x -> w e. y ) ) $=
      ( weq wex wel wi a9e ax-13 equcoms imim12d 19.22i ax-mp ) CDEZCFCAGZCBGZH
      DAGZDBGZHHZCFCDIOTCORPQSRPHDCDCAJKCDBJLMN $.
      $( [?] $) $( [12-Dec-2010] $)

 ${ $d w x $. $d w y $. $d z w $.

   $( ~ ax-ext with distinctors instead of distinct variable restrictions $)
   axextdist $p |- ( ( -. A. z z = x /\ -. A. z z = y ) -> 
   	     	     ( A. z ( z e. x <-> z e. y ) -> x = y ) ) $=
     ( vw weq wal wn wa wel wb hbnae hban wi dveel2 adantr adantl hbbid elequ1 
     bibi12d a1i cbvald axext3 syl6bir ) CAECFGZCBECFGZHZCAIZCBIZJZCFDAIZDBIZJZ
     DFABEUFULUIDCUDUECCACKCBCKLZUFUJUKCUMUDUJUJCFMUECADNOUEUKUKCFMUDCBDNPQDCEZ
     ULUIJMUFUNUJUGUKUHDCARDCBRSTUAABDUBUC $.
     $( [?] $) $( [13-Dec-2010] $)

   $( ~ axext4 with distinctors instead of distinct variable restrictions $)
   axext4dist $p |- ( ( -. A. z z = x /\ -. A. z z = y ) -> 
   	     	     ( x = y <-> A. z ( z e. x <-> z e. y ) ) ) $=
     ( weq wal wn wa wel wb wi ax-12 imp hbnae hban elequ2 a1i 19.20d syld 
     axextdist impbid ) CADCEFZCBDCEFZGZABDZCAHCBHIZCEZUCUDUDCEZUFUAUBUDUGJABCK
     LUCUDUECUAUBCCACMCBCMNUDUEJUCABCOPQRABCST $.
     $( [?] $) $( [13-Dec-2010] $)


 $}

  ${ $d x y $.
     19.12b.1 $e |- ( ph -> A. y ph ) $.
     19.12b.2 $e |- ( ps -> A. x ps ) $.

     $( ~ 19.12vv with not-free hypotheses, instead of distinct variable 
     	conditions $)
     19.12b $p |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) ) $=
       ( wi wal wex 19.21 exbii hbal 19.36 albii bitr2i 3bitri ) ABGZDHZCIABDHZ
       GZCIACHZSGZQCIZDHZRTCABDEJKASCBCDFLMUDUABGZDHUBUCUEDABCFMNUABDADCELJOP 
       $.
       $( [?] $) $( [13-Dec-2010] $)
  $}
  
  ${
     jad.1 $e |- ( ph -> ( -. ps -> th ) ) $.
     jad.2 $e |- ( ph -> ( ch -> th ) ) $.

     $( Deduction form of ~ ja $)
     jad $p |- ( ph -> ( ( ps -> ch ) -> th ) ) $=
       ( wi wn imim2d pm2.27 syl9r pm3.27im syl5 pm2.61d ) ABCGZBHZGZODGZAPDOEI
       ABRQHBOCADBCJFKOBLMN $.
       $( [?] $) $( [13-Dec-2010] $)
  $}

  $( A more general form of ~ hbnt $)
  hbntg $p |- ( A. x ( ph -> A. x ps ) -> ( -. ps -> A. x -. ph ) ) $=
    ( wal wi wn con3 19.20ii ax-6o con1i syl5 ) ABCDZEZCDLFZCDZAFZCDBFMNPCALGHO
    BBCIJK $.
    $( [?] $) $( [13-Dec-2010] $)

  $( A more general and closed form of ~ hbim $)
  hbimtg $p |- ( ( A. x ( ph -> A. x ch ) /\ ( ps -> A. x th ) ) ->
  	      	( ( ch -> ps ) -> A. x ( ph -> th ) ) ) $=
    ( wal wi wa wn hbntg pm2.21 19.20i syl6 adantr ax-1 imim2i adantl jad ) ACE
    FGEFZBDEFZGZHCBADGZEFZSCIZUCGUASUDAIZEFUCACEJUEUBEADKLMNUABUCGSTUCBDUBEDAOL
    PQR $.
    $( [?] $) $( [13-Dec-2010] $)

  $( A more general and closed form of ~ hbal $)
  hbaltg $p |- ( A. x ( ph -> A. y ps ) -> ( A. x ph -> A. y A. x ps ) ) $=
    ( wal wi 19.20 ax-7 imim2i ax-mp ) ABDEZFCEZACEZKCEZFZFLMBCEDEZFZFAKCGOQLNP
    MBCDHIIJ $.
    $( [?] $) $( [13-Dec-2010] $)

  ${
     hbg.1 $e |- ( ph -> A. x ps ) $.

     $( A more general form of ~ hbn $)
     hbng $p |- ( -. ps -> A. x -. ph ) $=
       ( wal wi wn hbntg mpg ) ABCEFBGAGCEFCABCHDI $.
       $( [?] $) $( [13-Dec-2010] $)

     ${
	hbg.2 $e |- ( ch -> A. x th ) $.

	$( A more general form of ~ hbim $)
	hbimg $p |- ( ( ps -> ch ) -> A. x ( ph -> th ) ) $=
  ( wal wi ax-gen hbimtg mp2an ) ABEHIZEHCDEHIBCIADIEHIMEFJGACBDEKL $.
  $( [?] $) $( [13-Dec-2010] $)

     $}
  $}

  $( There is always a set not in ` y ` $)
  exnel $p |- E. x -. x e. y $=
    ( cv wcel wn wex elirr hbth wceq ax-13 con3d a4ime ax-mp ) BCZNDZEZACZNDZEZ
    AFNGZPSABPATHQNIROABBJKLM $.
    $( [?] $) $( [13-Dec-2010] $)

  ${ $d x z $. $d y z $.
     $( Distinctors in terms of membership (NOTE: this only works
     	with relations where we can prove ~ el and ~ elirrv ) $)
     distel $p |- ( -. A. y y = x <-> -. A. y -. x e. y ) $=
       ( vz weq wal wn wel wex el hbnae dveel1 hbnd wb wi elequ2 notbid a1i 
       cbvald df-ex 3bitr4g mpbii sylib elirrv elequ1 mtbii 19.20i con3i 
       impbii ) BADZBEZFZABGZFZBEZFZUKULBHZUOUKACGZCHZUPACIUKUQFZCEZFUOURUPUKUT
       UNUKUSUMCBBABJZUKUQBVABACKLCBDZUSUMMNUKVBUQULCBAOPQRPUQCSULBSZTUAVCUBUJU
       NUIUMBUIBBGULBUCBABUDUEUFUGUH $.
       $( [?] $) $( [15-Dec-2010] $)
  $}

  $( ~ axextnd as a biconditional $)
  axextndbi $p |- E. z ( x = y <-> ( z e. x <-> z e. y ) ) $=
    ( cv wceq wcel wb wex wi wa axextnd elequ2 pm3.2 ax-mp 19.22i dfbi2 exbii 
    mpbir ) ADZBDZEZCDZSFUBTFGZGZCHUAUCIZUCUAIZJZCHZUFCHUHCABKUFUGCUEUFUGIABCLU
    EUFMNONUDUGCUAUCPQR $.
    $( [?] $) $( [14-Dec-2010] $)

