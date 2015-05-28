$( -*-text-*- $)
  $c ( ) -/\ |- wff $.
  $v ph ps ch th ta et ze DUMMY $.

  wph $f wff ph $.
  wps $f wff ps $.
  wch $f wff ch $.
  wth $f wff th $.
  wta $f wff ta $.
  wet $f wff et $.
  wze $f wff ze $.
  wdummy $f wff DUMMY $.

  wna $a wff ( ph -/\ ps ) $.

  ax-org $a |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ 
  	       	 ( ( ph -/\ ( ps -/\ ch ) ) -/\ 
		   ( ( th -/\ ch ) -/\ 
		     ( ( ch -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $.

  ${
     ax-ded.1 $e |- ph $.
     ax-ded.2 $e |- ( ph -/\ ( ps -/\ ch ) ) $.

     ax-ded $a |- ch $.
  $}

  nicDIRECT $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ 
       	      ( ( th -/\ ( th -/\ th ) ) -/\ 
	      	( ( ta -/\ ps ) -/\ 
		( ( ph -/\ ta ) -/\ ( ph -/\ ta ) ) ) ) ) $=
    ( wna ax-org ax-ded ) ??ABCFFDDDFFEBFAEFZIFFFF?????????????????????????????
    ????????GZ??????JJHZJHZHZJHLH???????????????????????????J??????MKHZNHH???K?
    ??MNHZHZHZQHQHZRHOHZSHQH??????SPHZJHZHHZUAHZUBH?????????J??????LJHJHHKHJHHU
    BHZKHZ?????????TQH????????????UDUCHZUFH??????UFUEHUEHHZUEHZHUEHHUHHUGH $.
    $( [?] $) $( [24-Apr-2012] $)

  ${
     axi.1 $e |- ( ph -/\ ( ps -/\ ch ) ) $.

     axi $p |- ( ( th -/\ ch ) -/\ ( ( ch -/\ th ) -/\ ( ph -/\ th ) ) ) $=
       ( wna ax-org ax-ded ) ABCFFZIDCFCDFADFFFEABCDGH $.
       $( [?] $) $( [29-Dec-2010] $)
  $}

  ${
     nasyl2.1 $e |- ( ph -/\ ( ps -/\ ch ) ) $.
     nasyl2.2 $e |- ( th -/\ ch ) $.

     nasyl2 $p |- ( ph -/\ th ) $=
       ( wna axi ax-ded ) DCGCDGADGFABCDEHI $.
       $( [?] $) $( [29-Dec-2010] $)
  $}

  ${
     niclem1.1 $e |- ( ph -/\ 
  	      	      ( ( ( ( ps -/\ ch ) -/\ 
		      	    ( ( ch -/\ ps ) -/\ ( ta -/\ ps ) ) ) -/\ 
		        ( ( et -/\ ch ) -/\ 
			  ( ( ch -/\ et ) -/\ ( ta -/\ et ) ) ) ) -/\ th ) ) $.

     niclem1 $p |- ( ( th -/\ ( ze -/\ ch ) ) -/\ ph ) $=
       ( wna ax-org axi nasyl2 ax-ded ) ABCICBIEBIIIZFCICFIEFIIIZIZDIZIZQAIZDGC
       IZIZAIZHPETIZIZFQIQFIUAFIIIZRSUBIIZPONIUCNIUCUCUCONEGCFJKEGCBJLUDUDUATDI
       ZQIIZUEUFIZPETDJUIUFUEIUHUEIUHUHUHUFUEUAUGQAJKUAUGQFJLLMM $.
       $( [?] $) $( [30-Dec-2010] $)
  $}

  niclem2 $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ 
  	      	( ( ( ps -/\ ch ) -/\ ph ) -/\ 
		  ( ( ch -/\ ch ) -/\ ph ) ) ) $=
    ( wze wna ax-org axi nasyl2 ax-ded niclem1 ) CCEZKBCEZEEZDLELDEKDEEEZEZBLE
    ZEZNALELAEKAEEEZPPMEZEZSPEZQBBCCFZPNNEZEZDSESDEODEEEZTUAQEEZPPMUCUBUCUCOMMM
    NNKKLDFZGUGHHUDUDONMEZSEEZUEUFEZPNNMFUJUFUEEUIUEEUIUIUIUFUEOUHSPFGOUHSDFHHI
    INREALOKDBMMRNKKLAFGJI $.
    $( [29-Dec-2010] $)

  ${
     nasimp3i.1 $e |- ( ph -/\ ( ps -/\ ch ) ) $.

     nasimp3i $p |- ( ( ch -/\ ch ) -/\ ph ) $=
       ( wna niclem2 ax-ded ) ABCEZEHAECCEAEDABCFG $.
       $( [?] $) $( [30-Dec-2010] $)
  $}

  niclem3 $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ 
  	      	( ( ( th -/\ th ) -/\ th ) -/\ 
		  ( ( th -/\ th ) -/\ th ) ) ) $=
    ( wze wna niclem2 nasimp3i ax-ded niclem1 ) DDFZDFZLFZECAEEBMMFMECFCEFEEFF
    FZNFAFZFZPMDLDLFLDFLDKDGHHPPFOMOMFPPOLLGHHIJ $.
    $( [29-Dec-2010] $)

  naid2 $p |- ( ( ph -/\ ph ) -/\ ph ) $=
    ( wze wna ax-org niclem3 ax-ded ) BBBCZCZHGGGCCZCCAACACZJBBBBDHHIAEF $.
    $( [29-Dec-2010] $)

  niclem4 $p |- ( ( ph -/\ ( ( ps -/\ ps ) -/\ ps ) ) -/\ 
  	      	( ( ( ( ps -/\ ps ) -/\ ps ) -/\ ph ) -/\ 
		  ( ch -/\ ph ) ) ) $=
    ( wze wna niclem3 ax-org axi niclem1 ax-ded ) CDBBEBEZEZEZLKDECDEEZEZEZKKE
    EOAKEKAECAEEEZMLNBFOQEAKPCDKMMQOCDKAGHIJ $.
    $( [29-Dec-2010] $)

  niclem5 $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ 
  	      	( ( ( ps -/\ ch ) -/\ ph ) -/\ 
		  ( ( ps -/\ ch ) -/\ ph ) ) ) $=
    ( wze wna ax-org axi nasimp3i nasyl2 niclem4 naid2 ax-ded ) DCECDEDDEEEZMEZ
    BCEZOEZEZAOEOAEZREEZEZPOEZEZSSTSQEOPEZQEUAUCUCSQOOOAFGNDOPDOEZUDMDBCDFHGIUB
    UATETTEZSSETOTJUEQSTKHIL $.
    $( [29-Dec-2010] $)

  niclem6 $p |- ( ( ( ( ph -/\ ps ) -/\ 
  	     	    ( ( ps -/\ ph ) -/\ ( ps -/\ ph ) ) ) -/\ 
  	      	  ( ch -/\ ( ps -/\ ps ) ) ) -/\ 
  	      	( ch -/\ ( th -/\ ps ) ) ) $=
    ( wze wna ax-org axi nasyl2 niclem4 niclem5 ax-ded ) CDBFFZABFBAFZNFFZCBBFZ
    FZFZFRMFZSMEQFQEFPBFZEFFFZQOFZTFZRMMTBPFZQFZFZUAUCFZCDBPGUGUCUAFUFUAFUFUFUE
    TFUCUAUBRUETUDUDOQBBBAGHHHTUDQEGIIUCRFRUCFZUHUCTUBFUBUBFRUBBUBJOCPKIUCOQKLI
    MOQKL $.
    $( [29-Dec-2010] $)

  nacom $p |- ( ( ph -/\ ps ) -/\ ( ( ps -/\ ph ) -/\ ( ps -/\ ph ) ) ) $=
    ( wze wna niclem6 niclem4 niclem5 nasyl2 ax-ded ) ABDZBADZKDZDZCBDZNDZBBDDZ
    DZONDZDZPMABOCESRQDQQDPMDQNQFPJLGHI $.
    $( [29-Dec-2010] $)

  ${
     nacomi.1 $e |- ( ph -/\ ps ) $.

     nacomi $p |- ( ps -/\ ph ) $=
       ( wna nacom ax-ded ) ABDBADZGCABEF $.
       $( [?] $) $( [29-Dec-2010] $)
  $}

  ${
     nasyl.1 $e |- ( ph -/\ ( ps -/\ ch ) ) $.
     nasyl.2 $e |- ( ch -/\ th ) $.
     
     nasyl $p |- ( ph -/\ th ) $=
       ( nacomi nasyl2 ) ABCDECDFGH $.
       $( [?] $) $( [29-Dec-2010] $)
  $}

  ${
     nasyl3.1 $e |- ( ( ps -/\ ch ) -/\ ph ) $.
     nasyl3.2 $e |- ( ch -/\ th ) $.

     nasyl3 $p |- ( ph -/\ th ) $=
       ( wna nacomi nasyl ) ABCDBCGAEHFI $.
       $( [?] $) $( [30-Dec-2010] $)
  $}

  ${
     nasyl4.1 $e |- ( ( ps -/\ ch ) -/\ ph ) $.
     nasyl4.2 $e |- ( th -/\ ch ) $.

     nasyl4 $p |- ( ph -/\ th ) $=
       ( wna nacomi nasyl2 ) ABCDBCGAEHFI $.
       $( [?] $) $( [30-Dec-2010] $)
  $}

  ${
     nasimpi.1 $e |- ( ph -/\ ( ps -/\ ch ) ) $.
     
     nasimpi $p |- ( ph -/\ ( ch -/\ ch ) ) $=
       ( wna nasimp3i nacomi ) CCEAABCDFG $.
       $( [?] $) $( [30-Dec-2010] $)
  $}

  naid $p |- ( ph -/\ ( ph -/\ ph ) ) $=
    ( wna naid2 nacomi ) AABAACD $.
    $( [?] $) $( [29-Dec-2010] $)

  narev $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ 
      	      ( ( ( ch -/\ ps ) -/\ ph ) -/\ 
	      	( ( ch -/\ ps ) -/\ ph ) ) ) $=
    ( wze wna nacom ax-org niclem6 nasyl2 ax-ded ) CBEZBCEZLEEZDKAEZENDEZOEEZAL
    EZNNEEZCBFMMQLAEZNEEPREKLLAGDNQSHIJ $.
    $( [?] $) $( [29-Dec-2010] $)

  nacomdt $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ 
  	      	( ( ph -/\ ( ch -/\ ps ) ) -/\ 
		  ( ph -/\ ( ch -/\ ps ) ) ) ) $=
    ( wna narev nacom nasyl ) ABCDDCBDZADZIAHDZJDABCEHAFG $.
    $( [?] $) $( [29-Dec-2010] $)

  ${
     narevi.1 $e |- ( ph -/\ ( ps -/\ ch ) ) $.

     narevi $p |- ( ( ch -/\ ps ) -/\ ph ) $=
       ( wna narev ax-ded ) ABCEECBEAEZHDABCFG $.
       $( [?] $) $( [29-Dec-2010] $)
  $}


  ${
     nacom2i.1 $e |- ( ph -/\ ( ps -/\ ch ) ) $.

     nacom2i $p |- ( ph -/\ ( ch -/\ ps ) ) $=
       ( wna narevi nacomi ) CBEAABCDFG $.
       $( [?] $) $( [29-Dec-2010] $)
  $}

  ${
     nacom3i.1 $e |- ( ( ph -/\ ps ) -/\ ch ) $.
     
     nacom3i $p |- ( ( ps -/\ ph ) -/\ ch ) $=
       ( wna nacomi nacom2i ) CBAECABABECDFGF $.
       $( [?] $) $( [29-Dec-2010] $)
  $}

  ${
     nacom4i.1 $e |- ( ( ph -/\ ps ) -/\ ( ch -/\ th ) ) $.

     nacom4i $p |- ( ( ps -/\ ph ) -/\ ( th -/\ ch ) ) $=
       ( wna narevi ) DCFABABFCDEGG $.
       $( [?] $) $( [29-Dec-2010] $)
  $}

  ${
     ded2.1 $e |- ph $.
     ded2.2 $e |- ( ph -/\ ( ps -/\ ch ) ) $.

     ded2 $p |- ps $=
       ( nacom2i ax-ded ) ACBDABCEFG $.
       $( [?] $) $( [29-Dec-2010] $)
  $}

  ${
     ded3.1 $e |- ph $.
     ded3.2 $e |- ( ( ps -/\ ch ) -/\ ph ) $.

     ded3 $p |- ch $=
       ( wna nacomi ax-ded ) ABCDBCFAEGH $.
       $( [?] $) $( [29-Dec-2010] $)
  $}


  ${ 
     nasimp2i.1 $e |- ( ph -/\ ( ps -/\ ch ) ) $.
     
     nasimp2i $p |- ( ph -/\ ( ps -/\ ps ) ) $=
       ( nacom2i nasimpi ) ACBABCDEF $.
       $( [?] $) $( [30-Dec-2010] $)
  $}

  nic $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ 
       	      ( ( th -/\ ( th -/\ th ) ) -/\ 
	      	( ( ta -/\ ps ) -/\ 
		( ( ph -/\ ta ) -/\ ( ph -/\ ta ) ) ) ) ) $=
    ( wze wna nacomdt niclem4 nasimpi nasyl ax-org niclem6 nasyl2 nacom2i ) ABC
    GGZEBGZAEGZRGGZDDDGZGZPACBGGZUBSUAGZABCHUCFRGRFGZUDGGZSGZUFUBUCSTDGZGZUHUFU
    FGSDTHUHUGSGUFSDUEIJKUBUBQBEGZRGGUFACBELFRQUIMNNNO $.
    $( [29-Dec-2010] $)



