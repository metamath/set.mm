$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              The Predecessor Class
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


  $c Pred $. $( The predecessors symbol $)
  cpred $a class Pred ( R , A , X ) $. 

  $( Define the predecessor class of a relationship. This is the
     class of all elements ` y ` of ` A ` such that ` y R X `. $)
  df-pred $a |- Pred ( R , A , X ) = ( A i^i ( `' R " { X } ) ) $.

  $( Equality theorem for the predecessor class $)
  predeq1 $p |- ( R = S -> Pred ( R , A , X ) = Pred ( S , A , X ) ) $=
    ( wceq ccnv csn cima cin cpred cnveq imaeq1d ineq2d df-pred 3eqtr4g ) BCEZA
    BFZDGZHZIACFZRHZIABDJACDJPSUAAPQTRBCKLMABDNACDNO $.
    $( [2-Feb-2011] $)

  $( Equality theorem for the predecessor class $)
  predeq2 $p |- ( A = B -> Pred ( R , A , X ) = Pred ( R , B , X ) ) $=
    ( wceq ccnv csn cima cin cpred ineq1 df-pred 3eqtr4g ) ABEACFDGHZIBNIACDJBC
    DJABNKACDLBCDLM $.
    $( [2-Feb-2011] $)

  $( Equality theorem for the predecessor class $)
  predeq3 $p |- ( X = Y -> Pred ( R , A , X ) = Pred ( R , A , Y ) ) $=
    ( wceq ccnv csn cima cin cpred sneq imaeq2d ineq2d df-pred 3eqtr4g ) CDEZAB
    FZCGZHZIAQDGZHZIABCJABDJPSUAAPRTQCDKLMABCNABDNO $.
    $( [2-Feb-2011] $)

  ${
     predeq1d.1 $e |- ( ph -> R = S ) $.

     $( Equality deduction for the predecessor class $)
     predeq1d $p |- ( ph -> Pred ( R , A , X ) = Pred ( S , A , X ) ) $=
       ( wceq cpred predeq1 syl ) ACDGBCEHBDEHGFBCDEIJ $.
       $( [2-Feb-2011] $)
  $}

  ${
     predeq2d.1 $e |- ( ph -> A = B ) $.

     $( Equality deduction for the predecessor class $)
     predeq2d $p |- ( ph -> Pred ( R , A , X ) = Pred ( R , B , X ) ) $=
       ( wceq cpred predeq2 syl ) ABCGBDEHCDEHGFBCDEIJ $.
       $( [2-Feb-2011] $)
  $}

  ${
     predeq3d.1 $e |- ( ph -> X = Y ) $.

     $( Equality deduction for the predecessor class $)
     predeq3d $p |- ( ph -> Pred ( R , A , X ) = Pred ( R , A , Y ) ) $=
       ( wceq cpred predeq3 syl ) ADEGBCDHBCEHGFBCDEIJ $.
       $( [2-Feb-2011] $)
  $}

  $( If ` A ` is a subset of ` B `, then their predecessor classes
     are also subsets $)
  predpredss $p |- ( A C_ B -> Pred ( R , A , X ) C_ Pred ( R , B , X ) ) $=
    ( wss ccnv csn cima cin cpred ssrin df-pred 3sstr4g ) ABEACFDGHZIBNIACDJBCD
    JABNKACDLBCDLM $.
    $( [2-Feb-2011] $)

  $( The predecessor class of ` A ` is a subset of ` A ` $)
  predss $p |- Pred ( R , A , X ) C_ A $=
    ( cpred wss ccnv csn cima cin inss1 df-pred sseq1i mpbir ) ABCDZAEABFCGHZIZ
    AEAOJNPAABCKLM $.
    $( [2-Feb-2011] $)

  $( Another subset/predecessor class relationship $)
  sspred $p |- ( ( B C_ A /\ Pred ( R , A , X ) C_ B ) -> 
  	       	 Pred ( R , A , X ) = Pred ( R , B , X ) ) $=
    ( cin wceq ccnv csn cima cpred wss wa ineq1 eqeq1d biimpa df-pred eqeq12i 
    biimpri eqcoms syl sseqin2 sseq1i df-ss in23 eqeq1i 3bitri syl2anb ) ABEZBF
    ZUHCGDHIZEZAUJEZFZACDJZBCDJZFZBAKUNBKZUIUMLBUJEZULFZUPUIUMUSUIUKURULUHBUJMN
    OUPULURUPULURFUNULUOURACDPZBCDPQRSTBAUAUQULBKULBEZULFUMUNULBUTUBULBUCVAUKUL
    AUJBUDUEUFUG $.
    $( [6-Feb-2011] $)

  ${ $d R y $. $d X y $.
     dfpred2.1 $e |- X e. _V $.

     $( An alternate definition of predecessor class when ` X ` is a set. $)
     dfpred2 $p |- Pred ( R , A , X ) = ( A i^i { y | y R X } ) $=
       ( cpred ccnv csn cima cin cv wbr cab df-pred cvv wcel wceq iniseg ax-mp 
       ineq2i eqtri ) BCDFBCGDHIZJBAKDCLAMZJBCDNUBUCBDOPUBUCQEACDORSTUA $.
       $( [8-Feb-2011] $)
  $}


  ${
     elpred.1 $e |- Y e. _V $.

     $( Membership in a predecessor class $)
     elpred $p |- ( X e. D -> ( Y e. Pred ( R , A , X ) <-> 
     	       	      	      	( Y e. A /\ Y R X ) ) ) $=
       ( wcel cpred ccnv csn cima wa wbr wb cin df-pred eleq2i elin bitri a1i 
       eliniseg anbi2d bitrd ) DBGZEACDHZGZEAGZECIDJKZGZLZUGEDCMZLUFUJNUDUFEAUH
       OZGUJUEULEACDPQEAUHRSTUDUIUKUGCDEBFUAUBUC $.
       $( [4-Feb-2011] $)
  $}

  $( Membership in a predecessor class $)
  elpredg $p |- ( ( X e. A /\ Y e. A ) -> 
      	     	  ( Y e. Pred ( R , A , X ) <-> Y R X ) ) $=
    ( wcel wa cpred ccnv csn cima wbr wb cin df-pred eleq2i elin bitri baib 
    adantl cop elimasng df-br bicomi a1i brcnvg 3bitrd bitrd ) CAEZDAEZFZDABCGZ
    EZDBHZCIJZEZDCBKZUIULUOLUHULUIUOULDAUNMZEUIUOFUKUQDABCNODAUNPQRSUJUOCDTUMEZ
    CDUMKZUPUMCDAAUAURUSLUJUSURCDUMUBUCUDCDAABUEUFUG $.
    $( [2-Feb-2011] $)

 
  ${ $d A y $. $d F y $. $d G y $. $d X y $. $d R y $.
     predreseq.1 $e |- X e. _V $.

     $( Equality of restriction to predecessor classes $)
     predreseq $p |- ( ( F Fn A /\ G Fn A ) ->
     	       	       ( ( F |` Pred ( R , A , X ) ) = 
		       	 ( G |` Pred ( R , A , X ) ) <->
			 A. y e. A ( y R X -> ( F ` y ) = ( G ` y ) ) ) ) $=
       ( wfn wa cpred cres wceq cv cfv wral wbr wi wss wb predss fvreseq mpan2 
       wcel wal df-ral cvv visset elpred ax-mp imbi1i albii impexp 3bitri 
       bitr4i syl6bb ) DBHEBHIZDBCFJZKEUQKLZAMZDNUSENLZAUQOZUSFCPZUTQZABOZUPUQB
       RURVASBCFTABUQDEUAUBVAUSBUCZVCQZAUDZVDVAUSUQUCZUTQZAUDVEVBIZUTQZAUDVGUTA
       UQUEVIVKAVHVJUTFUFUCVHVJSGBUFCFUSAUGUHUIUJUKVKVFAVEVBUTULUKUMVCABUEUNUO 
       $.
       $( [8-Feb-2011] $)
  $}

  ${
     predasetex.1 $e |- A e. _V $.

     $( The predecessor class exists when ` A ` does. $)
     predasetex $p |- Pred ( R , A , X ) e. _V $=
       ( cpred ccnv csn cima cin cvv df-pred inex1 eqeltri ) ABCEABFCGHZIJABCKA
       NDLM $.
       $( [8-Feb-2011] $)
  $}

  ${ $d R x z $. $d R y z $. $d A x z $. $d A y z $.
     $( Change the bound variable in the statement stating that ` R ` is
     	set-like $)
     cbvsetlike $p |- ( A. x e. A Pred ( R , A , x ) e. _V <-> 
     		      	A. y e. A Pred ( R , A , y ) e. _V ) $=
       ( vz cv cpred cvv wcel wral weq predeq3 eleq1d cbvralv bitr4i ) CDAFZGZH
       IZACJCDEFZGZHIZECJCDBFZGZHIZBCJRUAAECAEKQTHCDPSLMNUDUABECBEKUCTHCDUBSLMN
       O $.
       $( [2-Feb-2011] $)
  $}

  ${ $d x y R $. $d x A $.
     $( Alternate definition of founded relation $)
     dffr4 $p |- ( R Fr A <-> 
     	      	   A. x ( ( x C_ A /\ x =/= (/) ) 
		     	  -> E. y e. x Pred ( R , x , y ) = (/) ) ) $=
       ( wfr cv wss c0 wne wa ccnv csn cima cin wceq wrex wi wal cpred dffr3 
       df-pred eqeq1i rexbii imbi2i albii bitr4i ) CDEAFZCGUGHIJZUGDKBFZLMNZHOZ
       BUGPZQZARUHUGDUISZHOZBUGPZQZARABCDTUQUMAUPULUHUOUKBUGUNUJHUGDUIUAUBUCUDU
       EUF $.
       $( [2-Feb-2011] $)
  $}

  ${
     $( Membership in the predecessor class implies membership in the
     	base class $)
     predel $p |- ( Y e. Pred ( R , A , X ) -> Y e. A ) $=
       ( cpred wcel ccnv csn cima cin df-pred eleq2i elin pm3.26bi sylbi ) DABC
       EZFDABGCHIZJZFZDAFZPRDABCKLSTDQFDAQMNO $.
       $( [11-Feb-2011] $)
  $}

  ${ $d R z $. $d A z $. $d X z $. $d Y z $.
     $( Property of the predecessor class for strict orderings $)
     predso $p |- ( ( R Or A /\ X e. A ) ->
     	       	    ( Y e. Pred ( R , A , X ) -> 
		      Pred ( R , A , Y ) C_ Pred ( R , A , X ) ) ) $=
       ( vz wor wcel wa cpred wss predel w3a cv wi wal wbr wb elpredg adantll 
       sotr 3exp2 com24 imp31 com13 ex com14 sylbid com23 3imp imdistand 
       visset elpred 3ad2ant3 adantl 3ad2ant1 3imtr4d 19.21aiv dfss2 sylibr 
       3exp mpdi ) ABFZCAGZHZDABCIZGZDAGZABDIZVEJZABCDKVDVFVGVIVDVFVGLZEMZVHGZV
       KVEGZNZEOVIVJVNEVJVKAGZVKDBPZHZVOVKCBPZHZVLVMVJVOVPVRVDVFVGVOVPVRNNZVDVG
       VFVTVDVGVFVTNVDVGHZVFDCBPZVTVCVGVFWBQVBABCDRSVPWBVOWAVRVPWBVOWAVRNNWAVOV
       PWBHZVRVBVCVGVOWCVRNZNVBVOVGVCWDVBVOVGVCWDAVKDCBTUAUBUCUDUEUFUGUEUHUIUJV
       GVDVLVQQVFAABDVKEUKZULUMVDVFVMVSQZVGVCWFVBAABCVKWEULUNUOUPUQEVHVEURUSUTV
       A $.
       $( [11-Feb-2011] $)
  $}

  ${
     predbr.1 $e |- X e. _V $.
     predbr.2 $e |- Y e. _V $.

     $( If a set is in the predecessor class, then it is less than
     	the base element $)
     predbr $p |- ( Y e. Pred ( R , A , X ) -> Y R X ) $=
       ( cpred wcel wbr wa cvv wb elpred ax-mp biimpi pm3.27d ) DABCGHZDAHZDCBI
       ZQRSJZCKHQTLEAKBCDFMNOP $.
       $( [11-Feb-2011] $)
  $}     

  ${ $d R x $. $d A x $. $d X x $.
     $( If ` R ` is set-like in ` A ` then all predecessors classes
     	of elements of ` A ` exist $)
     setlikespec $p |- ( ( X e. A /\ A. x e. A Pred ( R , A , x ) e. _V )
     		       	 -> Pred ( R , A , X ) e. _V ) $=
       ( cv cpred cvv wcel wceq predeq3 eleq1d rcla4va ) BCAEZFZGHBCDFZGHADBMDI
       NOGBCMDJKL $.
       $( [20-Feb-2011] $)
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
              Well-founded induction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${ $d A x z w t u v $. $d A y $. 
     $d B x z w t u v $. $d B y $.
     $d R x z w t u v $. $d R y $.
     $d y z w t u v $.
     $( All nonempty (possibly proper) subclasses of ` A `, which
     	has a well-founded relation ` R `, have ` R `-minimal elements.
	Proposition 6.26 of [TakeutiZaring] p. 31. $)
     tz6.26 $p |- ( ( ( R We A /\ 
     	       	      	A. x e. A Pred ( R , A , x ) e. _V ) /\
     	    	      ( B C_ A /\ B =/= (/) ) ) ->
		    E. y e. B Pred ( R , B , y ) = (/) ) $=
       ( vt vz vw wwe cv cpred cvv wcel wral wa wss c0 wne wceq wrex wi wess 
       ssralv predpredss ssexg ex syl r19.20sdv syld cbvsetlike syl5ib anim12d 
       wex weq predeq3 eqeq1d rcla4ev adantl predss wfr wefr eleq1d rcla4cva 
       anim12i anassrs sseq1 neeq1 anbi12d predeq2 rexeqd imbi12d imbi2d wal 
       dffr4 ax-4 sylbi vtoclg impcom mpani wor wbr w3a sotr 3exp2 com23 com34 
       3imp exp3a 3exp imp43 wb elpredg adantll adantlr 3adant2 mpbird 
       imdistand visset elpred ax-mp ancom bitri 3imtr4g ssrdv sseq0 weso 
       anim1i biimpi syl2an r19.22dva ssrexv syl6 pm2.61dne 19.23adv n0 
       syl6com imp32 ) CEIZCEAJKLMACNZOZDCPZDQRZDEBJZKZQSZBDTZYAXTDEIZDEFJZKZLM
       ZFDNZOZYBYFUAYAXRYGXSYKDCEUBYACEYHKZLMZFCNZYKXSYAYOYNFDNYKYNFDCUCYAYNYJF
       DYAYIYMPZYNYJUADCEYHUDYPYNYJYIYMLUEUFUGUHUIAFCEUJUKULYLGJZDMZGUMYFYBYLYR
       YFGYLYRYFYLYROZYFDEYQKZQYRYTQSZYFUAYLYRUUAYFYEUUABYQDBGUNYDYTQDEYCYQUOUP
       UQUFURYSYTQRZYEBYTTZYFYSUUBYTEYCKZQSZBYTTZUUCYSYTDPZUUBUUFDEYQUSZYSDEUTZ
       YTLMZOZUUGUUBOZUUFUAZYGYKYRUUKYGUUIYKYROUUJDEVAYJUUJFYQDFGUNYIYTLDEYHYQU
       OVBVCVDVEUUJUUIUUMUUIHJZDPZUUNQRZOZUUNEYCKZQSZBUUNTZUAZUAUUIUUMUAHYTLUUN
       YTSZUVAUUMUUIUVBUUQUULUUTUUFUVBUUOUUGUUPUUBUUNYTDVFUUNYTQVGVHUUSUUEBUUNY
       TUVBUURUUDQUUNYTEYCVIUPVJVKVLUUIUVAHVMUVAHBDEVNUVAHVOVPVQVRUGVSYGYRUUFUU
       CUAYKYGYROZUUEYEBYTDEVTZYROZYCDMZYCYQEWAZOZUUEYEUAZUVCYCYTMZUVEUVHOZYDUU
       DPZUVIUVKHYDUUDUVKUUNYCEWAZUUNDMZOZUVMUUNYTMZOZUUNYDMZUUNUUDMZUVKUVMUVNU
       VPUVKUVMUVNUVPUVKUVMUVNWBUVPUUNYQEWAZUVKUVMUVNUVTUVDYRUVFUVGUVMUVNUVTUAZ
       UAZUVDUVFYRUVGUWBUAZUVDUVFYRUWCUVDUVFYRWBZUVMUVGUWAUWDUVMUVGUWAUWDUVNUVM
       UVGOZUVTUVDUVFYRUVNUWEUVTUAZUAUVDUVFUVNYRUWFUVDUVNUVFYRUWFUAUVDUVNUVFYRU
       WFDUUNYCYQEWCWDWEWFWGWEWHWEWIWEWJWGUVKUVNUVPUVTWKZUVMUVEUVNUWGUVHYRUVNUW
       GUVDDEYQUUNWLWMWNWOWPWIWQUVRUVNUVMOZUVOYCLMZUVRUWHWKBWRZDLEYCUUNHWRZWSWT
       UVNUVMXAXBUVSUVPUVMOZUVQUWIUVSUWLWKUWJYTLEYCUUNUWKWSWTUVPUVMXAXBXCXDUVLU
       UEYEYDUUDXEUFUGYGUVDYRDEXFXGUVJUVHYQLMUVJUVHWKGWRDLEYQYCUWJWSWTXHXIXJWNU
       IUUGUUCYFUAUUHYEBYTDXKWTXLXMUFXNGDXOUKXPXQ $.
       $( [29-Jan-2011] $)
  $}


  ${ $d A x $. $d A y $. $d B x $. $d B y $. $d R x $. $d R y $.
     $( The Principle of Well-Founded Induction. Theorem 6.27 of 
     	[TakeutiZaring]. This principle states that if ` B ` is a subclass
	of a well-ordered class ` A ` with the property that every
	element of ` B ` whose inital segment is included in ` A ` is
	itself equal to ` A `. $)

      wfi $p |- ( ( ( R We A /\ A. x e. A Pred ( R , A , x ) e. _V ) /\
      	     	    ( B C_ A /\
		      A. y e. A ( Pred ( R , A , y ) C_ B -> y e. B ) ) )
                  -> A = B ) $=
        ( wwe cv cpred cvv wcel wral wa wss wi cdif c0 wne wn difss wceq wrex 
        tz6.26 eldif anbi1i anass ancom ccnv csn cima cin indif2 df-pred incom 
        eqtri difeq1i 3eqtr4i eqeq1i ssdif0 bitr4i bitri anbi2i 3bitri rexbii2 
        rexanali sylib ex mpani necon3bbii syl5ib con4d imp adantrl simprl 
        eqssd ) CEFCEAGHIJACKLZDCMZCEBGZHZDMZVQDJZNBCKZLLCDVOWACDMZVPVOWAWBVOWB
        WAVOCDOZPQZWARZWBRVOWCCMZWDWECDSVOWFWDLZWEVOWGLWCEVQHZPTZBWCUAZWEABCWCE
        UBWJVSVTRZLZBCUAWEWIWLBWCCVQWCJZWILVQCJZWKLZWILWNWKWILZLWNWLLWMWOWIVQCD
        UCUDWNWKWIUEWPWLWNWPWIWKLWLWKWIUFWIVSWKWIVRDOZPTVSWHWQPEUGVQUHUIZWCUJZW
        RCUJZDOWHWQWRCDUKWHWCWRUJWSWCEVQULWCWRUMUNVRWTDVRCWRUJWTCEVQULCWRUMUNUO
        UPUQVRDURUSUDUTVAVBVCVSVTBCVDUTVEVFVGWBWCPCDURVHVIVJVKVLVOVPWAVMVN $.
        $( [29-Jan-2011] $)
  $}

  ${ $d A x $. $d A y $. $d B x $. $d B y $. $d R x $. $d R y $.
     wfi.1 $e |- R We A $.
     wfi.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.

     $( The Principle of Well-Founded Induction. Theorem 6.27 of 
     	[TakeutiZaring]. This principle states that if ` B ` is a subclass
	of a well-ordered class ` A ` with the property that every
	element of ` B ` whose inital segment is included in ` A ` is
	itself equal to ` A `. $)

     wfii $p |- ( ( B C_ A /\
		    A. y e. A ( Pred ( R , A , y ) C_ B -> y e. B ) )
                  -> A = B ) $=
       ( wwe cv cpred cvv wcel wral wa wss wi wceq pm3.2i wfi mpan ) CEHZCEAIJK
       LACMZNDCOCEBIZJDOUCDLPBCMNCDQUAUBFGRABCDEST $.
       $( [29-Jan-2011] $)
  $}


   ${ $d A w x y $. $d A z $. $d ph w x $. $d ph z $. $d R w x y $. $d R z $.
      $d w y z $.
      wfisg.1 $e |- ( y e. A -> 
      	       	       ( A. z e. Pred ( R , A , y ) [ z / y ] ph -> ph ) ) $.

      $( Well-Founded Induction Schema. If a property passes from all elements
       	 less than ` y ` of a well founded class ` A ` to ` y ` itself 
	 (induction hypothesis), then the property holds for all elements 
	 of ` A `. $)
      wfisg $p |- ( ( R We A /\ A. x e. A Pred ( R , A , x ) e. _V )
      	     	     -> A. y e. A ph ) $=
        ( vw wwe cv cpred cvv wcel wral wa crab wceq wss wi ssrab2 wsbc ax-17 
        hbs1 hbral hbim eleq1 predeq3 raleq1d sbequ12 imbi12d chvar dfss3 
        elrabsf pm3.27bi r19.20si sylbi syl5 anc2li syl6ibr rgen wfi mpanr12 
        rabid2 sylib ) EFIEFBJKLMBENOZEACEPZQZACENVEVFEREFHJZKZVFRZVHVFMZSZHENV
        GACETVLHEVHEMZVJVMACVHUAZOVKVMVJVNVMACDJZUAZDVINZVNVJCJZEMZVPDEFVRKZNZA
        SZSVMVQVNSZSCHVMWCCVMCUBZVQVNCVPCDVIVOVIMCUBACDUCUDACHUCUEUEVRVHQZVSVMW
        BWCVRVHEUFWEWAVQAVNWEVPDVTVIEFVRVHUGUHACHUIUJUJGUKVJVOVFMZDVINVQDVIVFUL
        WFVPDVIWFVOEMVPACHVOEWDUMUNUOUPUQURACHVHEWDUMUSUTBHEVFFVAVBACEVCVD $.
        $( [11-Feb-2011] $)
  $}


  ${ $d A w y z $. $d A x $. $d ph w z $. $d ph x $. $d R w y z $.
     $d R x $. $d x y $.
     wfis.1 $e |- R We A $.
     wfis.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
     wfis.3 $e |- ( y e. A -> 
     	       	    ( A. z e. Pred ( R , A , y ) [ z / y ] ph -> ph ) ) $.

     $( Well-Founded Induction Schema. If all elements less than a given
     	set ` x ` of the well founded class ` A ` have a property (induction 
	hypothesis), then all elements of ` A ` have that property. $)

     wfis $p |- ( y e. A -> ph ) $=
       ( wwe cv cpred cvv wcel wral wfisg mp2an rspec ) ACEEFJEFBKLMNBEOACEOGHA
       BCDEFIPQR $.
       $( [29-Jan-2011] $)
  $}

   ${ $d A x y $. $d A z $. $d ph x $. $d ph z $. $d R x y $. $d R z $.
     $d y z $.
     wfis2fg.1 $e |- ( ps -> A. y ps ) $.
     wfis2fg.2 $e |- ( y = z -> ( ph <-> ps ) ) $.
     wfis2fg.3 $e |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.

      $( Well-Founded Induction Schema, using implicit substitution. $)
      wfis2fg $p |- ( ( R We A /\ A. x e. A Pred ( R , A , x ) e. _V )
      	     	     -> A. y e. A ph ) $=
        ( cv wcel cpred wral wsbc sbie ralbii syl5ib wfisg ) ACDEFGDKZFLBEFGTMZ
        NAADEKOZEUANJUBBEUAABDEHIPQRS $.
        $( [11-Feb-2011] $)
  $}

  ${ $d A x y $. $d A z $. $d ph x $. $d ph z $. $d R x y $. $d R z $.
     $d y z $.
     wfis2f.1 $e |- R We A $.
     wfis2f.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
     wfis2f.3 $e |- ( ps -> A. y ps ) $.
     wfis2f.4 $e |- ( y = z -> ( ph <-> ps ) ) $.
     wfis2f.5 $e |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.

     $( Well Founded Induction schema, using implicit substitution $)
     wfis2f $p |- ( y e. A -> ph ) $=
       ( wwe cv cpred cvv wcel wral wfis2fg mp2an rspec ) ADFFGMFGCNOPQCFRADFRH
       IABCDEFGJKLSTUA $.
       $( [29-Jan-2011] $)
  $}

   ${ $d A x y $. $d A z $. $d ph x $. $d ph z $. $d ps y $. $d R x y $.
     $d R z $. $d y z $.
     wfis2g.1 $e |- ( y = z -> ( ph <-> ps ) ) $.
     wfis2g.2 $e |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.

      $( Well-Founded Induction Schema, using implicit substitution. $)
      wfis2g $p |- ( ( R We A /\ A. x e. A Pred ( R , A , x ) e. _V )
      	     	     -> A. y e. A ph ) $=
        ( ax-17 wfis2fg ) ABCDEFGBDJHIK $.
        $( [11-Feb-2011] $)
  $}

  ${ $d A x y $. $d A z $. $d ph x $. $d ph z $. $d ps y $. $d R x y $.
     $d R z $. $d y z $.
     wfis2.1 $e |- R We A $.
     wfis2.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
     wfis2.3 $e |- ( y = z -> ( ph <-> ps ) ) $.
     wfis2.4 $e |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.

     $( Well Founded Induction schema, using implicit substitution $)
     wfis2 $p |- ( y e. A -> ph ) $=
       ( wwe cv cpred cvv wcel wral wfis2g mp2an rspec ) ADFFGLFGCMNOPCFQADFQHI
       ABCDEFGJKRST $.
       $( [29-Jan-2011] $)
  $}

  ${ $d A x y $. $d A z $. $d B y $. $d ch y $. $d ph x $. $d ph z $.
     $d ps y $. $d R x y $. $d R z $. $d y z $.
     wfis3.1 $e |- R We A $.
     wfis3.2 $e |- A. x e. A Pred ( R , A , x ) e. _V $.
     wfis3.3 $e |- ( y = z -> ( ph <-> ps ) ) $.
     wfis3.4 $e |- ( y = B -> ( ph <-> ch ) ) $.
     wfis3.5 $e |- ( y e. A -> ( A. z e. Pred ( R , A , y ) ps -> ph ) ) $.


     $( Well Founded Induction schema, using implicit substitution $)
     wfis3 $p |- ( B e. A -> ch ) $=
       ( wfis2 vtoclga ) ACEHGMABDEFGIJKLNOP $.
       $( [29-Jan-2011] $)
  $}

