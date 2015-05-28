  ${ $d x A $. $d x R $. $d x B $.
     tz6.26i.1 $e |- R We A $.
     tz6.26i.2 $e |- A. x e. A ( `' R " { x } ) e. _V $.
     tz6.26i.3 $e |- B C_ A $.
     tz6.26i.4 $e |- B =/= (/) $.     

     $( All nonempty (possibly proper) subclasses of ` A `, which
     	has a well-founded relation ` R `, have ` R `-minimal elements.
	Proposition 6.26 of [TakeutiZaring] p. 31. $)
     tz6.26i $p |- E. x e. B ( B i^i ( `' R " { x } ) ) = (/) $=
       ( wwe ccnv cv csn cima cvv wcel wral wa wss c0 wne cin wceq wrex pm3.2i 
       tz6.26 mp2an ) BDIZDJAKLMZNOABPZQCBRZCSTZQCUHUASUBACUCUGUIEFUDUJUKGHUDAB
       CDUEUF $.
       $( [?] $) $( [28-Jan-2011] $)
  $}

  ${ $d x y z A $. $d x y z B $. $d x y z R $.
     $( The Principle of Well-Founded Induction. Theorem 6.27 of 
     	[TakeutiZaring]. This principle states that if ` B ` is a subclass
	of a well-ordered class ` A ` with the property that every
	element of ` B ` whose inital segment is included in ` A ` is
	itself equal to ` A `. $)

      wfi $p |- ( ( ( R We A /\ A. x e. A ( `' R " { x } ) e. _V ) /\
      	     	    B C_ A /\
		    A. x e. A ( ( A i^i ( `' R " { x } ) ) C_ B -> x e. B ) )
                  -> A = B ) $=
        ( vy wwe ccnv cv csn cima cvv wcel wral wa wss cin wi w3a wceq cdif c0 
        eqss biimpri expcom ssdif0 syl5ibr 3ad2ant2 wne difss wrex tz6.26 weq 
        sneq imaeq2d ineq2d eqeq1d cbvrexv wn eldif pm2.27 pm2.24 syl8 com24 
        imp sylbi ssrin ax-mp incom 3sstr3i sseq0 mpan difindir syl5eq sylibr 
        syl5 sseq1d eleq1 imbi12d rcla4cv syl7 r19.23aiv syl ex mpani com23 
        3adant2 pm2.61dne ) BDFDGZAHZIZJZKLABMNZCBOZBWKPZCOZWICLZQZABMZRBCSZBCT
        ZUAWMWLWTUASZWSQWRWMBCOZWSXAXBWMWSWSXBWMNBCUBUCUDBCUEUFUGWLWRWTUAUHZWSQ
        ZWMWLWRXDWLXCWRWSWLWTBOZXCWRWSQZBCUIWLXEXCNZXFWLXGNWTWKPZUASZAWTUJZXFAB
        WTDUKXJWTWHEHZIZJZPZUASZEWTUJXFXIXOAEWTAEULZXHXNUAXPWKXMWTXPWJXLWHWIXKU
        MUNZUOUPUQXOXFEWTXKWTLZXOXKBLZBXMPZCOZXKCLZQZQZWSWRXRYAYDWSQZXOXRXSYBUR
        ZNYAYEQZXKBCUSXSYFYGXSYDYAYFWSXSYDYAYBYFWSQXSYCUTYBWSVAVBVCVDVEXOXTCTZU
        ASYAXOWTXMCTZPZUAYHYJXNOXOYJUASYIWTPZXMWTPZYJXNYIXMOYKYLOXMCUIYIXMWTVFV
        GYIWTVHXMWTVHVIYJXNVJVKBXMCVLVMXTCUEVNVOWQYCAXKBXPWOYAWPYBXPWNXTCXPWKXM
        BXQUOVPWIXKCVQVRVSVTWAVEWBWCWDWEVDWFWG $.
        $( [?] $) $( [29-Jan-2011] $)
  $}

  ${ $d x A $. $d x B $. $d x R $.
     wfi.1 $e |- R We A $.
     wfi.2 $e |- A. x e. A ( `' R " { x } ) e. _V $.

     $( The Principle of Well-Founded Induction. Theorem 6.27 of 
     	[TakeutiZaring]. This principle states that if ` B ` is a subclass
	of a well-ordered class ` A ` with the property that every
	element of ` B ` whose inital segment is included in ` A ` is
	itself equal to ` A `. $)

     wfii $p |- ( ( B C_ A /\
		    A. x e. A ( ( A i^i ( `' R " { x } ) ) C_ B -> x e. B ) )
                  -> A = B ) $=
       ( wwe ccnv cv csn cima cvv wcel wral wa wss cin wi wceq pm3.2i wfi 
       mp3an1 ) BDGZDHAIZJKZLMABNZOCBPBUEQCPUDCMRABNBCSUCUFEFTABCDUAUB $.
       $( [?] $) $( [29-Jan-2011] $)
  $}

  ${ $d x y z $. $d x y z A $. $d x y z R $. $d y z ph $.
     wfis.1 $e |- R We A $.
     wfis.2 $e |- A. x e. A ( `' R " { x } ) e. _V $.
     wfis.3 $e |- ( x e. A -> 
     	       	    ( A. y e. A ( y R x -> [ y / x ] ph ) -> ph ) ) $.

     $( Well-Founded Induction Schema. If all elements less than a given
     	set ` x ` of the well founded class ` A ` have a property (induction 
	hypothesis), then all elements of ` A ` have that property. $)

     wfis $p |- ( x e. A -> ph ) $=
       ( vz cv wcel crab wss ccnv csn cima cin wi wral wceq ssrab2 wsb wa wbr 
       ax-17 hbs1 hbim hbral weq eleq1 breq2 imbi1d ralbidv sbequ12 imbi12d 
       chvar cab dfrab2 cvv visset iniseg ax-mp ineq1i incom 3eqtr2i sseq1i 
       dfss3 eleq2i elin ancom 3bitri imbi2i anclb wn wo cun elun unab breq1 
       notbid elab notbii bitr4i orbi1i 3bitr3i imor abbii 3bitr4i bitr3i 
       imdistan imbi12i ralbii2 elrabsf pm3.27bi sbim sbie imbi1i bitri sylib 
       r19.20si sylbir sylbi syl5 anc2li syl6ibr rgen sneq imaeq2d eleq1d 
       cbvralv mpbi wfii mp2an rabeq2i ) BJZDKZXPAABDDABDLZDMDENZIJZOZPZQZXQMZX
       SXQKZRZIDSDXQTABDUAYEIDXSDKZYCYFABIUBZUCYDYFYCYGYFCJZXSEUDZABCUBZRZCDSZY
       GYCXPYHXOEUDZYJRZCDSZARZRYFYLYGRZRBIYFYQBYFBUEZYLYGBYKBCDYHDKZBUEYIYJBYI
       BUEZABCUFUGUHABIUFUGUGBIUIZXPYFYPYQXOXSDUJUUAYOYLAYGUUAYNYKCDUUAYMYIYJXO
       XSYHEUKULUMABIUNUOUOHUPYCXOXSEUDZBDLZXQMZYLUUCYBXQUUCUUBBUQZDQZYADQYBUUB
       BDURZYAUUEDXSUSKYAUUETIUTBEXSUSVAVBVCYADVDVEVFUUDYHXQKZCUUCSZYLCUUCXQVGU
       UIYHUUBARZBDLZKZCDSYLUULUUHCDUUCYSUULRZYSYHUUEKZUCZYSYHABUQZKZUCZRZYHUUC
       KZUUHRUUMYSYSYHUUJBUQZKZUCZRZYSUUNUUQRZRZUUSUULUVCYSUULYHUVADQZKUVBYSUCU
       VCUUKUVGYHUUJBDURVHYHUVADVIUVBYSVJVKVLUVDYSUVBRUVFYSUVBVMUVBUVEYSYHUUBVN
       ZAVOZBUQZKZUUNVNZUUQVOZUVBUVEYHUVHBUQZUUPVPZKYHUVNKZUUQVOUVKUVMYHUVNUUPV
       QUVOUVJYHUVHABVRVHUVPUVLUUQUVPYIVNZUVLUVHUVQBYHCUTZBCUIUUBYIXOYHXSEVSZVT
       WAUUNYIUUBYIBYHUVRUVSWAWBWCWDWEUVAUVJYHUUJUVIBUUBAWFWGVHUUNUUQWFWHVLWIYS
       UUNUUQWJVKUUTUUOUUHUURUUTYHUUFKUUNYSUCUUOUUCUUFYHUUGVHYHUUEDVIUUNYSVJVKU
       UHYHUUPDQZKUUQYSUCUURXQUVTYHABDURVHYHUUPDVIUUQYSVJVKWKWCWLUULYKCDUULUUJB
       CUBZYKUULYSUWAUUJBIYHDYRWMWNUWAUUBBCUBZYJRYKUUBABCWOUWBYIYJUUBYIBCYTUVSW
       PWQWRWSWTXAXBXAXCXDABIXSDYRWMXEXFIDXQEFXRXOOZPZUSKZBDSYAUSKZIDSGUWEUWFBI
       DUUAUWDYAUSUUAUWCXTXRXOXSXGXHXIXJXKXLXMXNWN $.
       $( [?] $) $( [29-Jan-2011] $)
  $}

  ${ $d x y $. $d ph y $. $d x y A $. $d x y R $.
     wfis2f.1 $e |- R We A $.
     wfis2f.2 $e |- A. x e. A ( `' R " { x } ) e. _V $.
     wfis2f.3 $e |- ( ps -> A. x ps ) $.
     wfis2f.4 $e |- ( x = y -> ( ph <-> ps ) ) $.
     wfis2f.5 $e |- ( x e. A -> ( A. y e. A ( y R x -> ps ) -> ph ) ) $.

     $( Well Founded Induction schema, using implicit substitution $)
     wfis2f $p |- ( x e. A -> ph ) $=
       ( cv wcel wbr wi wral wsb sbie imbi2i ralbii syl5ib wfis ) ACDEFGHCLZEMD
       LUCFNZBOZDEPAUDACDQZOZDEPKUGUEDEUFBUDABCDIJRSTUAUB $.
       $( [?] $) $( [29-Jan-2011] $)
  $}

  ${ $d x y $. $d ph y $. $d x y A $. $d x y R $. $d ps x $.
     wfis2.1 $e |- R We A $.
     wfis2.2 $e |- A. x e. A ( `' R " { x } ) e. _V $.
     wfis2.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
     wfis2.4 $e |- ( x e. A -> ( A. y e. A ( y R x -> ps ) -> ph ) ) $.

     $( Well Founded Induction schema, using implicit substitution $)
     wfis2 $p |- ( x e. A -> ph ) $=
      ( ax-17 wfis2f ) ABCDEFGHBCKIJL $.
       $( [?] $) $( [29-Jan-2011] $)
  $}

  ${ $d ps x $. $d ph y $. $d ch x $. $d x B $. $d x y A $. $d x y R $.
     wfis3.1 $e |- R We A $.
     wfis3.2 $e |- A. x e. A ( `' R " { x } ) e. _V $.
     wfis3.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
     wfis3.4 $e |- ( x = B -> ( ph <-> ch ) ) $.
     wfis3.5 $e |- ( x e. A -> ( A. y e. A ( y R x -> ps ) -> ph ) ) $.


     $( Well Founded Induction schema, using implicit substitution $)
     wfis3 $p |- ( B e. A -> ch ) $=
       ( wfis2 vtoclga ) ACDGFLABDEFHIJKMNO $.
       $( [?] $) $( [29-Jan-2011] $)
  $}
