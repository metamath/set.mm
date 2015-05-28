  $c ( ) -/\ wff |- $.

  $v ph ps ch th ta et $.

  wph $f wff ph $.
  wps $f wff ps $.
  wch $f wff ch $.
  wth $f wff th $.
  wta $f wff ta $.
  wet $f wff et $.

  wna $a wff ( ph -/\ ps ) $.


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The axiom of propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ax-nic $a |- ( ( ph -/\ ( ch -/\ ps ) ) -/\
                   ( ( th -/\ ( th -/\ th ) ) -/\
                     ( ( th -/\ ch ) -/\
                       ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $.

  ${
     ded.1 $e |- ph $.
     ded.2 $e |- ( ph -/\ ( ps -/\ ch ) ) $.

     ax-ded $a |- ch $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Sheffer Stroke propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
     axi.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.

     axi $p |- ( ( th -/\ ch ) -/\
                      ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $=
       ( wna ax-nic ax-ded ) ACBFFDDDFFDCFADFZIFFEABCDGH $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ${
     sssyl2.1 $e |- ( ph -/\ ( ps -/\ ch ) ) $.
     sssyl2.2 $e |- ( th -/\ ps ) $.

     sssyl2 $p |- ( ph -/\ th ) $=
       ( wna axi ax-ded ) DBGADGZJFACBDEHI $.
       $( [?] $) $( [27-Dec-2010] $)
  $}

  lem1 $p |- ( ( ph -/\ ( ( ps -/\ ( ch -/\ th ) ) -/\ ta ) ) -/\
       	       ( ( ( ta -/\ ( et -/\ ( et -/\ et ) ) ) -/\ ph ) -/\
	       	 ( ( ta -/\ ( et -/\ ( et -/\ et ) ) ) -/\ ph ) ) ) $=
    ( wna ax-nic axi ) EFFFGGZGBCDGGZEGZLAKFCGBFGZMGGJEBDCFHII $.
    $( [?] $) $( [24-Dec-2010] $)

  ssid $p |- ( ph -/\ ( ph -/\ ph ) ) $=
    ( wps wna ax-nic ax-ded ) BBBCZCZGFFFCCZCZCZHAAACCZBBBBDZHKCZGCZJMCZOJNNLMI
    ICCZGGGCCJNNCCGKABCBACZQCCZCCHHHCCPBBBADGRKHDEMIIGDEEJGBGCGBCZSCCZCCMMMCCNO
    OCCGHGBDJTGMDEEE $.
    $( [?] $) $( [24-Dec-2010] $)

  sscom $p |- ( ( ph -/\ ps ) -/\ ( ( ps -/\ ph ) -/\ ( ps -/\ ph ) ) ) $=
    ( ssid axi ) BBBABCD $.
    $( [?] $) $( [24-Dec-2010] $)

  ${
     sscomi.1 $e |- ( ph -/\ ps ) $.

     sscomi $p |- ( ps -/\ ph ) $=
       ( wna sscom ax-ded ) ABDBADZGCABEF $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ssid2 $p |- ( ( ph -/\ ph ) -/\ ph ) $=
    ( wps wna ax-nic ax-ded ) BBBCZCZGFFFCCZCZCZABCBACZKCCZAACZACZBBBBDZLNCZGCZ
    JPCZRGAMCZLCZCZQQBBBADPTTCCZGGGCCZUAQQCCSNNCCZLLLCCUBMMMCCZSUDJHUEOHUECZGCZ
    JUFCZUHJUGUGOUFIICCZUCJUGUGCCGUEMBCBMCZUJCCZCCHHHCCUIBBBMDGUKUEHDEUFIIGDEEJ
    GBGCGBCZULCCZCCZUFUFUFCCUGUHUHCCGHGBDZJUMGUFDEEEMMMADESNNLDEPTTGDEEUNPPPCCQ
    RRCCUOJUMGPDEEE $.
    $( [?] $) $( [24-Dec-2010] $)

  ssrev $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ 
  	        ( ( ( ch -/\ ps ) -/\ ph ) -/\ ( ( ch -/\ ps ) -/\ ph ) ) ) $=
    ( wna sscom axi ) CBDBCDZGACBEF $.
    $( [?] $) $( [24-Dec-2010] $)

  ${
     ssrevi.1 $e |- ( ph -/\ ( ps -/\ ch ) ) $.

     ssrevi $p |- ( ( ch -/\ ps ) -/\ ph ) $=
       ( wna ssrev ax-ded ) ABCEECBEAEZHDABCFG $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  sscom3 $p |- ( ( ( ph -/\ ps ) -/\ ch ) -/\ 
  	         ( ( ( ps -/\ ph ) -/\ ch ) -/\ ( ( ps -/\ ph ) -/\ ch ) ) ) $=
    ( wna ssrev ssrevi ) BADCDZGDCABDZCHDGGCABEFF $.
    $( [?] $) $( [27-Dec-2010] $)

  ${
     sssyl.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
     sssyl.2 $e |- ( ps -/\ ch ) $.
     
     sssyl $p |- ( ph -/\ ch ) $=
       ( sscomi sssyl2 ) ABBCDBCEFG $.
       $( [?] $) $( [27-Dec-2010] $)
  $}

  ${
     sscom2i.1 $e |- ( ph -/\ ( ps -/\ ch ) ) $.

     sscom2i $p |- ( ph -/\ ( ch -/\ ps ) ) $=
       ( wna ssrevi sscomi ) CBEAABCDFG $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ${ 
     sscom3i.1 $e |- ( ( ph -/\ ps ) -/\ ch ) $.
     
     sscom3i $p |- ( ( ps -/\ ph ) -/\ ch ) $=
       ( wna sscom3 ax-ded ) ABECEBAECEZHDABCFG $.
       $( [?] $) $( [27-Dec-2010] $)
  $}

  ${
     ded2.1 $e |- ph $.
     ded2.2 $e |- ( ph -/\ ( ps -/\ ch ) ) $.
     
     ded2 $p |- ps $=
       ( sscom2i ax-ded ) ACBDABCEFG $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  pm3.26ss $p |- ( ( ( ph -/\ ps ) -/\ ( ph -/\ ps ) ) -/\ ( ph -/\ ph ) ) $=
    ( wna ssid2 sssyl2 ) ABCZFCABAACFDADE $.
    $( [?] $) $( [27-Dec-2010] $)

  pm3.27ss $p |- ( ( ( ph -/\ ps ) -/\ ( ph -/\ ps ) ) -/\ ( ps -/\ ps ) ) $=
    ( wna sscom ssrevi ssid2 sssyl2 ) ABCZHCBABBCBACHHBADEBFG $.
    $( [?] $) $( [27-Dec-2010] $)

  ssexplode2 $p |- ( ph -/\ ( ( ( ph -/\ ph ) -/\ ps ) -/\ 
  	     	     	      ( ( ph -/\ ph ) -/\ ps ) ) ) $=
    ( wna ssid2 axi ssrev lem1 ax-ded sscom3i ) AAACZCZJBCZLCZACZNCZCNAMCZMBJAL
    DEOKNPCZQOOCCOKCQCZRNAMFQNMAOAGHIH $.
    $( [?] $) $( [27-Dec-2010] $)

  ssadant $p |- ( ph -/\ 
  	     	  ( ( ps -/\ ( ph -/\ ph ) ) -/\ 
		    ( ps -/\ ( ph -/\ ph ) ) ) ) $=
    ( wna sscom ssrevi axi ssrev lem1 ax-ded sscom3i ) AAACZCZBKCZMCZACZOCZCOAN
    CZNBKAKBCMMKBDEFPLOQCZRPPCCPLCRCZSOANGRONAPAHIJI $.
    $( [?] $) $( [24-Dec-2010] $)

  ${
     ssadanti.1 $e |- ph $.
     
     ssadanti $p |- ( ps -/\ ( ph -/\ ph ) ) $=
       ( wna ssadant ax-ded ) ABAADDZGCABEF $.
  $}

  ssimssim1 $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\
  	       	    ( ( ( ps -/\ th ) -/\ 
		      	( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) -/\
		      ( ( ps -/\ th ) -/\ 
		      	( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    ( wta wna ax-nic lem1 ax-ded sscomi ssrev ssrevi sscom2i sssyl2 ) ABCFFZDBF
    ZADFZQFZFZEEEFFZBDFRFZUAFZSTFZOODDDFFSFFUCOFZUDACBDGODDDSEHIJUBRPRPFUAUARDB
    KLMN $.
    $( [?] $) $( [27-Dec-2010] $)

  ${
     ssimssimi.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.

     ssimssim1i $p |- ( ( ps -/\ ch ) -/\ 
     		      	( ( ph -/\ ch ) -/\ ( ph -/\ ch ) ) ) $=
       ( wna ssimssim1 ax-ded ) ABBEEBCEACEZHEEZIDABBCFG $.
       $( [?] $) $( [24-Dec-2010] $)


     ssimssim2i $p |- ( ( ch -/\ ( ph -/\ ph ) ) -/\ 
     		        ( ( ch -/\ ( ps -/\ ps ) ) -/\ 
			  ( ch -/\ ( ps -/\ ps ) ) ) ) $=
       ( wna axi sscom sssyl ssimssim1i ) CAAEZEZCABEZEZCBBEZEZOEZKLCEMMELJJCAB
       BADFFLCGHMNCEPNLLCABBDIFNCGHH $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ssexplode $p |- ( ( ph -/\ ph ) -/\ ( ( ph -/\ ps ) -/\ ( ph -/\ ps ) ) ) $=
    ( wna pm3.26ss ssrevi ) ABCZFCAAABDE $.
    $( [?] $) $( [27-Dec-2010] $)

  sspeirce $p |- ( ( ( ph -/\ ps ) -/\ ( ph -/\ ph ) ) -/\ ( ph -/\ ph ) ) $=
    ( wch wna ax-nic lem1 ax-ded sscomi ssrev ssadant sscom3i sssyl ssrevi 
    sssyl2 ) AADZABDZOOPDZOADZOODZSDZDZCCCDDZOUAUBDZQQOSDUADDUCQDZUDOBAOEQOOOUA
    CFGHUAAATROTRDAODZTDOTOAITUEOOTTDDTUEDODZUFOSJOSOOTAFGKLKMNK $.
    $( [?] $) $( [27-Dec-2010] $)

  ssabsorb $p |- ( ( ph -/\ ( ( ph -/\ ps ) -/\ ch ) ) -/\ ( ( ph -/\ ps ) -/\ ( ph -/\ ps ) ) ) $=
    ( wth wna ax-nic lem1 ax-ded sscomi sscom3 sspeirce sssyl ssrevi sssyl2 ) 
    AABEZCEEZBOEOOEZEZDDDEEZQRSEZPPBBBEEREETPEZUAACOBFPBBBRDGHIROOROBEQEQBOQJOB
    KLMN $.
    $( [?] $) $( [27-Dec-2010] $)

  ssinev $p |- ( ( ( ph -/\ ps ) -/\ ch ) -/\ 
  	       	 ( ( ( ph -/\ ch ) -/\ ch ) -/\ ( ( ph -/\ ch ) -/\ ch ) ) ) $=
    ( wth wna ssexplode2 ax-nic ax-ded sscom sssyl lem1 sscomi axi sscom3i 
    ssrev ssadant ssrevi sssyl2 sscom2i ssexplode ssimssim1i ) CABEZACEZCEZUDEZ
    UCCUBEZCEZUGEZEZUFUEEZUJCAUHUFCAEZCEZULEZEZUKUHEZUOUKCCEZUPEZEZUMEUNUNURCUK
    EZUMCUQUQEEUKUKUKEZEZURUSUSEECUPFZCUQUQUKGHCUKIJUMURUNUNEUFDDDEEZURUMURVCEZ
    UFUFCUPEZUREEVDUFEZVFCBACGUFCCCURDKHLMNHCULEZUHEZUOUOEZEUNVIEZVJUKVGUHUKVGE
    ZUKEUKVGVGEZEZVMVKULCEZUKEZVOUKUKCULOUKUKVNUKVNVNEZEZUKUKVNEZEZVSUKCUSEZVPU
    KCUTEZVTVTEZUKCPWAUSUQEZVCWBWCVCEZWAWAVEWCEEWDWAEZWECUKUKCGWACCCWCDKHLWCVTV
    TCUQUQUSVBMQRJCCUKOJVQVRUTUTEZEZVCVSVSEWGVCEZVQVQVAWGEEWHVQEZWIUKVNVNUKGVQU
    KUKUKWGDKHLWGVSVSUKWFWFVRUKUTFMQRHSRUKVKVMVMEZUKVKEVLUKEWJVLVKVKUKVLVGUKEVK
    VKEVGUKTVGUKIJMVLUKIJNHUAVIVHVJVJEUNVCVHVIVHVCEZUNUNVEVHEEWKUNEZWLUFULULCGU
    NCCCVHDKHLMNHHNCUGEZUEEZUJUJEZEUIWOEZWPUFWMUEUFWMEZUFEUFWMWMEZEZWSWQUGCEZUF
    EZXAUFUFCUGOUFUFWTUFWTWTEZEZUFUFWTEZEZXEUFCCUFEZEZXBUFCUFUFEZEZXGXGEZUFCPXI
    XFUQEZVCXJXKVCEZXIXIVEXKEEXLXIEZXMCUFUFCGXICCCXKDKHLXKXGXGCUQUQXFVBMQRJCCUF
    OJXCXDXHXHEZEZVCXEXEEXOVCEZXCXCUFXHEXOEEXPXCEZXQUFWTWTUFGXCUFUFUFXODKHLXOXE
    XEUFXNXNXDUFXHFMQRHSRUFWQWSWSEZUFWQEWRUFEXRWRWQWQUFWRWMUFEWQWQEWMUFTWMUFIJM
    WRUFIJNHUAWOWNWPWPEUIVCWNWOWNVCEZUIUIVEWNEEXSUIEZXTUCUGUGCGUICCCWNDKHLMNHHN
    $.
    $( [?] $) $( [28-Dec-2010] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Biconditional
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c <-> $.

  wb $a wff ( ph <-> ps ) $.

  df-bi $a |- ( ( ( ph <-> ps ) -/\ ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) ) -/\ ( ( ( ph <-> ps ) -/\ ( ph <-> ps ) ) -/\ ( ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) -/\ ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) ) ) ) $.

  ${
     bitoss.1 $e |- ( ph <-> ps ) $.

     bitoss $p |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) $=
       ( wb wna df-bi ssid sssyl2 sscomi ax-ded ) ABDZKABEAAEBBEEEZCKLEZKMKKELL
       EKABFKGHIJ $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ${
     sstobi.1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) $.

     sstobi $p |- ( ph <-> ps ) $=
       ( wna wb df-bi ssrevi ssid sssyl2 sscomi ax-ded ) ABDAADBBDDDZLABEZCLMDZ
       LNLLDZMMDZLOPDMLMLDPOABFGGLHIJK $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ${
     bissimpi.1 $e |- ( ph <-> ps ) $.
     
     bissimpi $p |- ( ph -/\ ( ps -/\ ps ) ) $=
       ( wna bitoss ssid sssyl2 sscomi sscom2i ssid2 ) ABABBDZAABABDZALAADKAABC
       EAFGHIBJG $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ${
     bissimpri.1 $e |- ( ph <-> ps ) $.
     
     bissimpri $p |- ( ps -/\ ( ph -/\ ph ) ) $=
       ( wna bitoss ssrevi ssid sssyl2 sscomi sscom2i ssid2 ) BABAADZBBABADZBMB
       BDZLBNLDABABDLNABCEFFBGHIJAKH $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ${
     ssimpbii.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
     ssimpbii.2 $e |- ( ps -/\ ( ph -/\ ph ) ) $.

     ssimpbii $p |- ( ph <-> ps ) $=
       ( wna axi ssimssim1i sscom sssyl2 ssrevi sscom2i sstobi ) ABABEAAEZMMBBE
       ZEZABBACFOBAEZMEZQMPNNMBAABDFFMMPMPEZAARMMEZSMMPPMBAADGFAAHIJKIIL $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ${
     mpbi.1 $e |- ph $.
     mpbi.2 $e |- ( ph <-> ps ) $.

     mpbi $p |- ps $=
       ( bissimpi ax-ded ) ABBCABDEF $.
  $}

  ${
     mpbir.1 $e |- ps $.
     mpbir.2 $e |- ( ph <-> ps ) $.

     mpbir $p |- ph $=
       ( bissimpri ax-ded ) BAACABDEF $.
  $}


  ${
     bicomi.1 $e |- ( ph <-> ps ) $.

     bicomi $p |- ( ps <-> ph ) $=
       ( wna bitoss ssrevi sstobi ) BABBDZAADZDABABDIHABCEFFG $.
       $( [?] $) $( [24-Dec-2010] $)
  $}
  
  dfbi1 $p |- ( ( ph <-> ps ) <-> 
  	      ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) ) $=
    ( wb wna df-bi sstobi ) ABCABDAADBBDDDABEF $.
    $( [?] $) $( [24-Dec-2010] $)

  sscomb $p |- ( ( ph -/\ ps ) <-> ( ps -/\ ph ) ) $=
    ( wna sscom ssimpbii ) ABCBACABDBADE $.
    $( [?] $) $( [24-Dec-2010] $)

  biid $p |- ( ph <-> ph ) $=
    ( ssid ssimpbii ) AAABZDC $.
    $( [?] $) $( [24-Dec-2010] $)

  ss4bi $p |- ( ph <-> ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) ) $=
    ( wna ssadant ssid2 ssimpbii ) AAABZFBAFCFDE $.
    $( [?] $) $( [24-Dec-2010] $)

  ${
     bitri.1 $e |- ( ph <-> ps ) $.
     bitri.2 $e |- ( ps <-> ch ) $.

     bitri $p |- ( ph <-> ch ) $=
       ( wna bissimpi sssyl bissimpri ssimpbii ) ACABCCFABDGBCEGHCBAAFBCEIAB
       DIHJ $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ${
     bitr2i.1 $e |- ( ph <-> ps ) $.
     bitr2i.2 $e |- ( ps <-> ch ) $.

     bitr2i $p |- ( ch <-> ph ) $=
       ( bitri bicomi ) ACABCDEFG $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ${
     bitr3i.1 $e |- ( ps <-> ph ) $.
     bitr3i.2 $e |- ( ps <-> ch ) $.

     bitr3i $p |- ( ph <-> ch ) $=
       ( bicomi bitri ) ABCBADFEG $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ${
     bitr4i.1 $e |- ( ph <-> ps ) $.
     bitr4i.2 $e |- ( ch <-> ps ) $.

     bitr4i $p |- ( ph <-> ch ) $=
       ( bicomi bitri ) ABCDCBEFG $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ${
     3bitri.1 $e |- ( ph <-> ps ) $.
     3bitri.2 $e |- ( ps <-> ch ) $.
     3bitri.3 $e |- ( ch <-> th ) $.

     3bitri $p |- ( ph <-> th ) $=
       ( bitri ) ACDABCEFHGH $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ${
     3bitr4i.1 $e |- ( ph <-> ps ) $.
     3bitr4i.2 $e |- ( ch <-> ph ) $.
     3bitr4i.3 $e |- ( th <-> ps ) $.

     3bitr4i $p |- ( ch <-> th ) $=
       ( bicomi 3bitri ) CABDFEDBGHI $.
       $( [?] $) $( [24-Dec-2010] $)
  $}


  ${
     ssbii.1 $e |- ( ph <-> ps ) $.

     ssbi1i $p |- ( ( ph -/\ ch ) <-> ( ps -/\ ch ) ) $=
       ( wna bissimpri ssimssim1i bissimpi ssimpbii ) ACEBCEBACABDFGABCABDHGI 
       $.
       $( [?] $) $( [24-Dec-2010] $)

     ssbi2i $p |- ( ( ch -/\ ph ) <-> ( ch -/\ ps ) ) $=
       ( wna sscomb ssbi1i 3bitri ) CAEACEBCECBECAFABCDGBCFH $.
       $( [?] $) $( [24-Dec-2010] $)
    
    ${ 
       ssbii.2 $e |- ( ch <-> th ) $.

       ssbi12i $p |- ( ( ph -/\ ch ) <-> ( ps -/\ th ) ) $=
         ( wna ssbi1i ssbi2i bitri ) ACGBCGBDGABCEHCDBFIJ $.
         $( [?] $) $( [24-Dec-2010] $)
    $}

  $}


  bicomssimp $p |- ( ( ph <-> ps ) -/\ ( ( ps <-> ph ) -/\ ( ps <-> ph ) ) ) $=
    ( wb wna ssrev sssyl dfbi1 ssbi12i mpbir ) ABCZBACZKDZDABDZAADZBBDZDDZBADON
    DZDZRDZDPQMDSMNOEQABEFJPLSABGKRKRBAGZTHHI $.
    $( [?] $) $( [28-Dec-2010] $)

  bicom $p |- ( ( ph <-> ps ) <-> ( ps <-> ph ) ) $=
    ( wb bicomssimp ssimpbii ) ABCBACABDBADE $.
    $( [?] $) $( [28-Dec-2010] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Negation 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c -. $.

  wn $a wff -. ph $.

  df-neg $a |- ( -. ph <-> ( ph -/\ ph ) ) $.

  ${
     nbii.1 $e |- ( ph <-> ps ) $.

     notbii $p |- ( -. ph <-> -. ps ) $=
       ( wna wn ssbi12i df-neg 3bitr4i ) AADBBDAEBEABABCCFAGBGH $.
       $( [?] $) $( [24-Dec-2010] $)
  $}

  ssnot $p |- ( ph -/\ -. ph ) $=
    ( wn wna ssid df-neg ssbi2i mpbir ) AABZCAAACZCADHIAAEFG $.
    $( [?] $) $( [27-Dec-2010] $)

  notnot $p |- ( ph <-> -. -. ph ) $=
    ( wna wn ss4bi df-neg notbii bitri bitr4i ) AAABZIBZACZCZADLICJKIAEFIEGH $.
    $( [?] $) $( [27-Dec-2010] $)

  dfbi2 $p |- ( ( ph <-> ps ) <-> ( ( ph -/\ ps ) -/\ ( -. ph -/\ -. ps ) ) ) $=
    ( wb wna wn dfbi1 df-neg ssbi12i ssbi2i bitr4i ) ABCABDZAADZBBDZDZDKAEZBEZD
    ZDABFQNKOLPMAGBGHIJ $.
    $( [?] $) $( [27-Dec-2010] $)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Implication
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c -> $.

  wi $a wff ( ph -> ps ) $.

  df-imp $a |- ( ( ph -> ps ) <-> ( ph -/\ -. ps ) ) $.

  ${
     ibii.1 $e |- ( ph <-> ps ) $.

     imbi1i $p |- ( ( ph -> ch ) <-> ( ps -> ch ) ) $=
       ( wn wna wi ssbi1i df-imp 3bitr4i ) ACEZFBKFACGBCGABKDHACIBCIJ $.
       $( [?] $) $( [27-Dec-2010] $)

     imbi2i $p |- ( ( ch -> ph ) <-> ( ch -> ps ) ) $=
       ( wn wna wi notbii ssbi2i df-imp 3bitr4i ) CAEZFCBEZFCAGCBGLMCABDHICAJCB
       JK $.
       $( [?] $) $( [27-Dec-2010] $)

     ${
        ibii.2 $e |- ( ch <-> th ) $.

	imbi12i $p |- ( ( ph -> ch ) <-> ( ps -> th ) ) $=
  ( wi imbi1i imbi2i bitri ) ACGBCGBDGABCEHCDBFIJ $.
  $( [?] $) $( [27-Dec-2010] $)
     $}
  $}

  dfimp $p |- ( ( ph -> ps ) <-> ( ph -/\ ( ps -/\ ps ) ) ) $=
    ( wi wn wna df-imp df-neg ssbi2i bitri ) ABCABDZEABBEZEABFJKABGHI $.
    $( [?] $) $( [27-Dec-2010] $)

  ${
     mp.1 $e |- ph $.
     mp.2 $e |- ( ph -> ps ) $.

     mp $p |- ps $=
       ( wi wna dfimp mpbi ax-ded ) ABBCABEABBFFDABGHI $.
       $( [?] $) $( [27-Dec-2010] $)
  $}

  ${
     syl.1 $e |- ( ph -> ps ) $.
     syl.2 $e |- ( ps -> ch ) $.

     syl $p |- ( ph -> ch ) $=
       ( wi wna dfimp mpbi sssyl mpbir ) ACFACCGZGABLABFABBGGDABHIBCFBLGEBCHIJA
       CHK $.
       $( [?] $) $( [27-Dec-2010] $)
  $}

  ax1 $p |- ( ph -> ( ps -> ph ) ) $=
    ( wi wna ssadant wn df-imp df-neg ssbi2i bitri notbii mpbir ) ABACZCZABAADZ
    DZPDZDZABENAMFZDRAMGSQASPFQMPMBAFZDPBAGTOBAHIJKPHJIJL $.
    $( [?] $) $( [27-Dec-2010] $)

  ${
     biimpi.1 $e |- ( ph <-> ps ) $.
     
     biimpi $p |- ( ph -> ps ) $=
       ( wi wna bissimpi dfimp mpbir ) ABDABBEEABCFABGH $.
       $( [?] $) $( [27-Dec-2010] $)

     biimpri $p |- ( ps -> ph ) $=
       ( wi wna bissimpri dfimp mpbir ) BADBAAEEABCFBAGH $.
       $( [?] $) $( [27-Dec-2010] $)  
  $}

  ${
     impbii.1 $e |- ( ph -> ps ) $.
     impbii.2 $e |- ( ps -> ph ) $.

     impbii $p |- ( ph <-> ps ) $=
       ( wi wna dfimp mpbi ssimpbii ) ABABEABBFFCABGHBAEBAAFFDBAGHI $.
       $( [?] $) $( [27-Dec-2010] $)
  $}

  notnot1 $p |- ( ph -> -. -. ph ) $=
    ( wn notnot biimpi ) AABBACD $.
    $( [?] $) $( [27-Dec-2010] $)

  notnot2 $p |- ( -. -. ph -> ph ) $=
    ( wn notnot biimpri ) AABBACD $.
    $( [?] $) $( [27-Dec-2010] $)

  pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wn wi wna ssid2 df-imp ssbi1i bitri mpbir ) ABZACZACZJJDZJDZJELKJDNKAFKMJ
    JAFGHI $.
    $( [?] $) $( [27-Dec-2010] $)

  id $p |- ( ph -> ph ) $=
    ( wi wna ssid dfimp mpbir ) AABAAACCADAAEF $.
    $( [?] $) $( [27-Dec-2010] $)

  pm2.01 $p |- ( ( ph -> -. ph ) -> -. ph ) $=
    ( wn wi pm2.18 notnot imbi1i mpbir ) AABZCZHCHBZHCZHCHDIKHAJHAEFFG $.
    $( [?] $) $( [27-Dec-2010] $)

  pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( wn wi wna ssexplode dfimp mpbir df-neg imbi12i ) ACZABDZDAAEZABBEZEZDZPMO
    OEEANFMOGHKMLOAIABGJH $.
    $( [?] $) $( [27-Dec-2010] $)

  peirce $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    ( wi wn wna sspeirce dfimp df-imp df-neg ssbi12i bitri ssbi1i mpbir ) ABCZA
    CZACZABDZEZAAEZEZSEZAQFPOSEUAOAGOTSONADZETNAHNRUBSABHAIJKLKM $.
    $( [?] $) $( [27-Dec-2010] $)

  ${
     imim.1 $e |- ( ph -> ps ) $.

     imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $=
       ( wi wna dfimp mpbi ssimssim1i mpbir imbi12i ) BCEZACEZEBCCFZFZANFZEZQOP
       PFFABNABEABBFFDABGHIOPGJLOMPBCGACGKJ $.
       $( [?] $) $( [27-Dec-2010] $)

     imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
       ( wi wna dfimp mpbi ssimssim2i imbi12i bitri mpbir ) CAEZCBEZEZCAAFFZCBB
       FZFZRFFZABCABEAQFDABGHIOPRESMPNRCAGCBGJPRGKL $.
       $( [?] $) $( [27-Dec-2010] $)
  $}

  con34b $p |- ( ( ph -> ps ) <-> ( -. ps -> -. ph ) ) $=
    ( wn wna wi sscomb df-imp notnot ssbi2i bitr4i 3bitr4i ) ABCZDLADZABELACZEZ
    ALFABGOLNCZDMLNGAPLAHIJK $.
    $( [?] $) $( [27-Dec-2010] $)

  con3 $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $=
    ( wi wn con34b biimpi ) ABCBDADCABEF $.
    $( [?] $) $( [27-Dec-2010] $)

  ax3 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    ( wi wn con34b biimpri ) BACADBDCBAEF $.
    $( [?] $) $( [27-Dec-2010] $)

  ${
     con3i.1 $e |- ( ph -> ps ) $.

     con3i $p |- ( -. ps -> -. ph )  $=
       ( wi wn con3 mp ) ABDBEAEDCABFG $.
       $( [?] $) $( [27-Dec-2010] $)
  $}

  con1b $p |- ( ( -. ph -> ps ) <-> ( -. ps -> ph ) ) $=
    ( wn wi con34b notnot imbi2i bitr4i ) ACZBDBCZICZDJADIBEAKJAFGH $.
    $( [?] $) $( [27-Dec-2010] $)

  con1 $p |- ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) $=
    ( wn wi con1b biimpi ) ACBDBCADABEF $.
    $( [?] $) $( [27-Dec-2010] $)

  con2b $p |- ( ( ph -> -. ps ) <-> ( ps -> -. ph ) ) $=
    ( wn wi con34b notnot imbi1i bitr4i ) ABCZDICZACZDBKDAIEBJKBFGH $.
    $( [?] $) $( [27-Dec-2010] $)

  con2 $p |- ( ( ph -> -. ps ) -> ( ps -> -. ph ) ) $=
    ( wn wi con2b biimpi ) ABCDBACDABEF $.
    $( [?] $) $( [27-Dec-2010] $)

  ${ 
     con1d.1 $e |- ( ph -> ( -. ps -> ch ) ) $.

     con1d $p |- ( ph -> ( -. ch -> ps ) ) $=
       ( wn wi con1 syl ) ABECFCEBFDBCGH $.
       $( [?] $) $( [28-Dec-2010] $)
  $}

  ${
     con2d.1 $e |- ( ph -> ( ps -> -. ch ) ) $.
     
     con2d $p |- ( ph -> ( ch -> -. ps ) ) $=
       ( wn wi con2 syl ) ABCEFCBEFDBCGH $.
       $( [?] $) $( [27-Dec-2010] $)
  $}

  imim1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wi wna ssimssim1 wn df-imp dfimp imbi12i bitri notbii df-neg ssbi12i 
    mpbir ) ABDZBCDZACDZDZDZABBEEZBCCEZEZAUBEZUDEEZUEEZEZABBUBFTPSGZEUGPSHPUAUH
    UFABIUHUEGUFSUESUCUDDUEQUCRUDBCIACIJUCUDIKLUEMKNKO $.
    $( [?] $) $( [27-Dec-2010] $)

  pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wn wi wna ssexplode2 df-imp df-neg ssbi1i bitri imbi2i dfimp mpbir ) AACZ
    BDZDZAAAEZBCZEZSEEZARFPASDTOSAONRESNBGNQRAHIJKASLJM $.
    $( [?] $) $( [27-Dec-2010] $)

  pm2.43 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wi wn wna ssabsorb df-imp imbi2i dfimp bitri imbi12i mpbir ) AABCZCZMCZAA
    BDZEZQEZEZREZAPQFOSQCTNSMQNAQCSMQAABGZHAQIJUAKSQIJL $.
    $( [?] $) $( [27-Dec-2010] $)

  pm2.27 $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi ax1 imim1 syl pm2.43 ) AABCZHBCZCZIAHACJAHDHABEFHBGF $.
    $( [?] $) $( [27-Dec-2010] $)

  pm2.04 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi imim1 pm2.27 imim1i syl ) ABCDZDICDZACDZDBKDAICEBJKBCFGH $.
    $( [?] $) $( [27-Dec-2010] $)

  ${
     com12.1 $e |- ( ph -> ( ps -> ch ) ) $.

     com12 $p |- ( ps -> ( ph -> ch ) ) $=
       ( wi pm2.04 mp ) ABCEEBACEEDABCFG $.
       $( [?] $) $( [27-Dec-2010] $)
  $}

  ${
     com23.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.

     com23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
       ( wi pm2.04 syl ) ABCDFFCBDFFEBCDGH $.
       $( [?] $) $( [28-Dec-2010] $)
  $}

  imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi imim1 com12 ) CADABDCBDCABEF $.
    $( [?] $) $( [27-Dec-2010] $)

  ax2 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi pm2.04 imim2 pm2.43 imim2i syl ) ABCDDBACDZDZABDZJDZABCEKLAJDZDMBJAFNJ
    LACGHII $.
    $( [?] $) $( [27-Dec-2010] $)

  ssim $p |- ( ( ph -/\ ps ) <-> ( ph -> -. ps ) ) $=
    ( wna wn wi notnot ssbi2i df-imp bitr4i ) ABCABDZDZCAJEBKABFGAJHI $.
    $( [?] $) $( [27-Dec-2010] $)

  ${
     syl6.1 $e |- ( ph -> ( ps -> ch ) ) $.
     syl6.2 $e |- ( ch -> th ) $.

     syl6 $p |- ( ph -> ( ps -> th ) ) $=
       ( wi imim2i syl ) ABCGBDGECDBFHI $.
       $( [?] $) $( [27-Dec-2010] $)
  $}

  ${
     syl6ib.1 $e |- ( ph -> ( ps -> ch ) ) $.
     syl6ib.2 $e |- ( ch <-> th ) $.

     syl6ib $p |- ( ph -> ( ps -> th ) ) $=
       ( biimpi syl6 ) ABCDECDFGH $.
       $( [?] $) $( [27-Dec-2010] $)
  $}

  ${
     syl6ibr.1 $e |- ( ph -> ( ps -> ch ) ) $.
     syl6ibr.2 $e |- ( th <-> ch ) $.

     syl6ibr $p |- ( ph -> ( ps -> th ) ) $=
       ( bicomi syl6ib ) ABCDEDCFGH $.
       $( [?] $) $( [27-Dec-2010] $)
  $}

  looinv $p |- ( ( ( ph -> ps ) -> ps ) -> ( ( ps -> ph ) -> ph ) ) $=
    ( wi imim1 peirce syl6 ) ABCZBCBACGACAGBADABEF $.
    $( [?] $) $( [27-Dec-2010] $)

  pm2.61 $p |- ( ( ph -> ps ) -> ( ( -. ph -> ps ) -> ps ) ) $=
    ( wi wn con1 imim1 syl com12 pm2.18 syl6 ) ABCZADBCZBDZBCZBLKNLMACKNCABEMAB
    FGHBIJ $.
    $( [?] $) $( [27-Dec-2010] $)

  bi1 $p |- ( ( ph <-> ps ) -> ( ph -> ps ) ) $=
    ( wb wi wna ssexplode2 axi ssexplode sscom3 sscom sssyl sssyl2 dfbi1 dfimp 
    imbi12i bitri mpbir ) ABCZABDZDZABEZAAEBBEZEZEZAUBEZUEEZEZUDAUAEZUHUFAUCUCU
    AAUBFGUFUEUBAEZEZUHUEUIHUJUIUIEZUKUHAUBUIIUBUAUAAUBBAEUAUAEBAHBAJKGLKLTUDUE
    DUGRUDSUEABMABNOUDUENPQ $.
    $( [?] $) $( [28-Dec-2010] $)

  ${
     sylbi.1 $e |- ( ph <-> ps ) $.
     sylbi.2 $e |- ( ps -> ch ) $.

     sylbi $p |- ( ph -> ch ) $=
       ( biimpi syl ) ABCABDFEG $.
       $( [?] $) $( [28-Dec-2010] $)
  $}

  ${
     sylbir.1 $e |- ( ps <-> ph ) $.
     sylbir.2 $e |- ( ps -> ch ) $.

     sylbir $p |- ( ph -> ch ) $=
       ( bicomi sylbi ) ABCBADFEG $.
       $( [?] $) $( [28-Dec-2010] $)
  $}

  bi2 $p |- ( ( ph <-> ps ) -> ( ps -> ph ) ) $=
    ( wb wi bicom bi1 sylbi ) ABCBACBADABEBAFG $.
    $( [?] $) $( [28-Dec-2010] $)
  
 ${
   mpd.1 $e |- ( ph -> ps ) $.
   mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
   
   mpd $p |- ( ph -> ch ) $=
     ( wi ax2 mp ) ABFZACFZDABCFFIJFEABCGHH $.
     $( [?] $) $( [28-Dec-2010] $)
 $}

 ${
   sylc.1 $e |- ( ph -> ( ps -> ch ) ) $.
   sylc.2 $e |- ( th -> ph ) $.
   sylc.3 $e |- ( th -> ps ) $.

   sylc $p |- ( th -> ch ) $=
     ( wi syl mpd ) DBCGDABCHFEIJ $.
     $( [?] $) $( [28-Dec-2010] $)
 $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Conjunction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c /\ $.

  wa $a wff ( ph /\ ps ) $.

  df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -/\ ps ) ) $.

  ${
     abii.1 $e |- ( ph <-> ps ) $.

     anbi1i $p |- ( ( ph /\ ch ) <-> ( ps /\ ch ) ) $=
       ( wna wn wa ssbi1i notbii df-an 3bitr4i ) ACEZFBCEZFACGBCGLMABCDHIACJBCJ
       K $.
       $( [?] $) $( [27-Dec-2010] $)

     anbi2i $p |- ( ( ch /\ ph ) <-> ( ch /\ ps ) ) $=
       ( wna wn wa ssbi2i notbii df-an 3bitr4i ) CAEZFCBEZFCAGCBGLMABCDHICAJCBJ
       K $.
       $( [?] $) $( [27-Dec-2010] $)

     ${
        abii.2 $e |- ( ch <-> th ) $.

	anbi12i $p |- ( ( ph /\ ch ) <-> ( ps /\ th ) ) $=
  ( wa anbi1i anbi2i bitri ) ACGBCGBDGABCEHCDBFIJ $.
  $( [?] $) $( [27-Dec-2010] $)
     $}
  $}


  ancom $p |- ( ( ph /\ ps ) <-> ( ps /\ ph ) ) $=
    ( wna wn wa sscomb notbii df-an 3bitr4i ) ABCZDBACZDABEBAEJKABFGABHBAHI $.
    $( [?] $) $( [27-Dec-2010] $)

  pm3.22 $p |- ( ( ph /\ ps ) -> ( ps /\ ph ) ) $=
    ( wa ancom biimpi ) ABCBACABDE $.
    $( [?] $) $( [27-Dec-2010] $)

  pm3.26 $p |- ( ( ph /\ ps ) -> ph ) $=
    ( wa wi wna pm3.26ss wn df-an df-neg bitri imbi1i dfimp mpbir ) ABCZADZABEZ
    PEZAAEEZABFOQADRNQANPGQABHPIJKQALJM $.
    $( [?] $) $( [27-Dec-2010] $)

  pm3.27 $p |- ( ( ph /\ ps ) -> ps ) $=
    ( wa wi wna pm3.27ss wn df-an df-neg bitri imbi1i dfimp mpbir ) ABCZBDZABEZ
    PEZBBEEZABFOQBDRNQBNPGQABHPIJKQBLJM $.
    $( [?] $) $( [27-Dec-2010] $)

  dfan2 $p |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $=
    ( wa wna wn wi df-an ssim notbii bitri ) ABCABDZEABEFZEABGKLABHIJ $.
    $( [?] $) $( [27-Dec-2010] $)
 
  pm3.2 $p |- ( ph -> ( ps -> ( ph /\ ps ) ) ) $=
    ( wn wi wa pm2.27 con2d dfan2 syl6ibr ) ABABCZDZCABEAKBAJFGABHI $.
    $( [?] $) $( [27-Dec-2010] $)

  ssan $p |- ( ( ph -/\ ps ) <-> -. ( ph /\ ps ) ) $=
    ( wna wn wa notnot df-an notbii bitr4i ) ABCZJDZDABEZDJFLKABGHI $.
    $( [?] $) $( [27-Dec-2010] $)

  impexp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ph -> ( ps -> ch ) ) ) $=
    ( wa wi pm3.2 imim1 syl com12 wn con3 imim2i com23 con1d dfan2 imbi1i 
    biimpri impbii ) ABDZCEZABCEZEZATUAABSETUAEABFBSCGHIUBABJZEZJZCEZTUBCUDUBAC
    JZUCUAUGUCEABCKLMNTUFSUECABOPQHR $.
    $( [?] $) $( [28-Dec-2010] $)

  ${
     jca.1 $e |- ( ph -> ps ) $.
     jca.2 $e |- ( ph -> ch ) $.

     jca $p |- ( ph -> ( ps /\ ch ) ) $=
       ( wa pm3.2 sylc ) BCBCFABCGDEH $.
       $( [?] $) $( [28-Dec-2010] $)
  $}

  ${
     imp.1 $e |- ( ph -> ( ps -> ch ) ) $.

     imp $p |- ( ( ph /\ ps ) -> ch ) $=
       ( wa wi impexp mpbir ) ABECFABCFFDABCGH $.
       $( [?] $) $( [28-Dec-2010] $)
  $}
  
  ${
     ex.1 $e |- ( ( ph /\ ps ) -> ch ) $.
     
     ex $p |- ( ph -> ( ps -> ch ) ) $=
       ( wa wi impexp mpbi ) ABECFABCFFDABCGH $.
       $( [?] $) $( [28-Dec-2010] $)
  $}

  ${
     jcad.1 $e |- ( ph -> ( ps -> ch ) ) $.
     jcad.2 $e |- ( ph -> ( ps -> th ) ) $.

     jcad $p |- ( ph -> ( ps -> ( ch /\ th ) ) ) $=
       ( wa imp jca ex ) ABCDGABGCDABCEHABDFHIJ $.
       $( [?] $) $( [28-Dec-2010] $)
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Disjunction 
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c \/ $.

  wo $a wff ( ph \/ ps ) $.

  df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -/\ -. ps ) ) $.

  ${
     obii.1 $e |- ( ph <-> ps ) $.

     orbi1i $p |- ( ( ph \/ ch ) <-> ( ps \/ ch ) ) $=
       ( wn wna wo notbii ssbi1i df-or 3bitr4i ) AEZCEZFBEZMFACGBCGLNMABDHIACJB
       CJK $.
       $( [?] $) $( [27-Dec-2010] $)

     orbi2i $p |- ( ( ch \/ ph ) <-> ( ch \/ ps ) ) $=
       ( wn wna wo notbii ssbi2i df-or 3bitr4i ) CEZAEZFLBEZFCAGCBGMNLABDHICAJC
       BJK $.
       $( [?] $) $( [27-Dec-2010] $)

     ${
        obii.2 $e |- ( ch <-> th ) $.

	orbi12i $p |- ( ( ph \/ ch ) <-> ( ps \/ th ) ) $=
  ( wo orbi1i orbi2i bitri ) ACGBCGBDGABCEHCDBFIJ $.
  $( [?] $) $( [27-Dec-2010] $)
     $}
  $}

  orcom $p |- ( ( ph \/ ps ) <-> ( ps \/ ph ) ) $=
    ( wn wna wo sscomb df-or 3bitr4i ) ACZBCZDJIDABEBAEIJFABGBAGH $.
    $( [?] $) $( [27-Dec-2010] $)

  pm1.2 $p |- ( ( ph \/ ph ) -> ph ) $=
    ( wo wi wn wna ssid2 df-or imbi1i df-imp bitri mpbir ) AABZACZADZNEZNEZNFMO
    ACPLOAAAGHOAIJK $.
    $( [?] $) $( [27-Dec-2010] $)

  pm1.4 $p |- ( ( ph \/ ps ) -> ( ps \/ ph ) ) $=
    ( wo orcom biimpi ) ABCBACABDE $.
    $( [?] $) $( [27-Dec-2010] $)

  dfor2 $p |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $=
    ( wo wn wna wi df-or df-imp bitr4i ) ABCADZBDEJBFABGJBHI $.
    $( [?] $) $( [27-Dec-2010] $)

  dfbi3 $p |- ( ( ph <-> ps ) <-> ( ( ph -/\ ps ) -/\ ( ph \/ ps ) ) ) $=
    ( wb wna wn wo dfbi2 df-or ssbi2i bitr4i ) ABCABDZAEBEDZDKABFZDABGMLKABHIJ 
    $.
    $( [?] $) $( [27-Dec-2010] $)

  ssor $p |- ( ( ph -/\ ps ) <-> ( -. ph \/ -. ps ) ) $=
    ( wna wn wo notnot ssbi12i df-or bitr4i ) ABCADZDZBDZDZCJLEAKBMAFBFGJLHI $.
    $( [?] $) $( [27-Dec-2010] $)

  ianor $p |- ( -. ( ph /\ ps ) <-> ( -. ph \/ -. ps ) ) $=
    ( wa wn wna wo ssan ssor bitr3i ) ABCDABEADBDFABGABHI $.
    $( [?] $) $( [27-Dec-2010] $)

  pm4.62 $p |- ( ( ph -> -. ps ) <-> ( -. ph \/ -. ps ) ) $=
    ( wn wi wna wo ssim ssor bitr3i ) ABCZDABEACJFABGABHI $.
    $( [?] $) $( [27-Dec-2010] $)

  anor $p |- ( ( ph /\ ps ) <-> -. ( -. ph \/ -. ps ) ) $=
    ( wa wn wi wo dfan2 pm4.62 notbii bitri ) ABCABDZEZDADKFZDABGLMABHIJ $.
    $( [?] $) $( [27-Dec-2010] $)

  ioran $p |- ( -. ( ph \/ ps ) <-> ( -. ph /\ -. ps ) ) $=
    ( wo wn wa notnot orbi12i notbii anor bitr4i ) ABCZDADZDZBDZDZCZDLNEKPAMBOA
    FBFGHLNIJ $.
    $( [?] $) $( [27-Dec-2010] $)
