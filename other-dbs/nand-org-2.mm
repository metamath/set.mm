$( -*-text-*- $)
  $c ( ) -/\ |- wff $.

  $v ph $.  $( Greek phi $)
  $v ps $.  $( Greek psi $)
  $v ch $.  $( Greek chi $)
  $v th $.  $( Greek theta $)
  $v ta $.  $( Greek tau $)
  $v et $.  $( Greek eta $)
  $v ze $.  $( Greek zeta $)
  $v si $.  $( Greek sigma $)
  $v rh $.  $( Greek rho $)
  $v mu $.  $( Greek mu $)
  $v la $.  $( Greek lambda $)
  $v ka $.  $( Greek kappa $)

  $( Specify some variables that we will use to represent wff's.
     The fact that a variable represents a wff is relevant only to a theorem
     referring to that variable, so we may use $f hypotheses.  The symbol
     ` wff ` specifies that the variable that follows it represents a wff. $)
  $( Let variable ` ph ` be a wff. $)
  wph $f wff ph $.
  $( Let variable ` ps ` be a wff. $)
  wps $f wff ps $.
  $( Let variable ` ch ` be a wff. $)
  wch $f wff ch $.
  $( Let variable ` th ` be a wff. $)
  wth $f wff th $.
  $( Let variable ` ta ` be a wff. $)
  wta $f wff ta $.
  $( Let variable ` et ` be a wff. $)
  wet $f wff et $.
  $( Let variable ` ze ` be a wff. $)
  wze $f wff ze $.
  $( Let variable ` si ` be a wff. $)
  wsi $f wff si $.
  $( Let variable ` rh ` be a wff. $)
  wrh $f wff rh $.
  $( Let variable ` mu ` be a wff. $)
  wmu $f wff mu $.
  $( Let variable ` la ` be a wff. $)
  wla $f wff la $.
  $( Let variable ` ka ` be a wff. $)
  wka $f wff ka $.

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

  niclem49 $p |- ( ( ph -/\ ( ( ps -/\ ch ) -/\ ( ( ch -/\ ps ) -/\ ( th -/\ ps ) ) ) ) -/\ ( ( ( ( ps -/\ ch ) -/\ ( ( ch -/\ ps ) -/\ ( th -/\ ps ) ) ) -/\ ph ) -/\ ( ( th -/\ ( ta -/\ ch ) ) -/\ ph ) ) ) $=
    ( wna ax-org ax-ded ) DECFFZIBCFCBFDBFFFZFFZKAJFJAFIAFFFDECBGIIJAGH $.
    $( [26-Jun-2014] $)

  niclem50 $p |- ( ( ph -/\ ( ( ps -/\ ( ch -/\ th ) ) -/\ ta ) ) -/\ ( ( ( ( ps -/\ ( ch -/\ th ) ) -/\ ta ) -/\ ph ) -/\ ( ( ta -/\ ( ( et -/\ th ) -/\ ( ( th -/\ et ) -/\ ( ps -/\ et ) ) ) ) -/\ ph ) ) ) $=
    ( wna niclem49 ax-org ax-ded ) EFDGDFGBFGGGZGZKEGZBCDGGEGZGGZOANGNAGLAGGGE
    FDBCHLMNAIJ $.
    $( [26-Jun-2014] $)

  niclem54 $p |- ( ( ( ( ph -/\ ps ) -/\ ( ( ps -/\ ph ) -/\ ( ch -/\ ph ) ) ) -/\ ( ( th -/\ ps ) -/\ ( ( ps -/\ th ) -/\ ( ch -/\ th ) ) ) ) -/\ ( ch -/\ ( ta -/\ ps ) ) ) $=
    ( wna ax-org niclem50 ax-ded ) CEBFFZJABFBAFCAFFFZFZFLJFKDBFBDFCDFFFFJFCEB
    AGJCEBKDHI $.
    $( [26-Jun-2014] $)

  niclem67 $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( ( th -/\ ( ph -/\ ta ) ) -/\ ( ( ( ph -/\ ta ) -/\ th ) -/\ ( ( ta -/\ ch ) -/\ th ) ) ) -/\ ( ( et -/\ ( ph -/\ ta ) ) -/\ ( ( ( ph -/\ ta ) -/\ et ) -/\ ( ( ta -/\ ch ) -/\ et ) ) ) ) ) $=
    ( wna niclem54 niclem49 ax-ded ) DAEGZGKDGECGZDGGGFKGKFGLFGGGGZLCEGZKGGZGO
    MGABCGGMGDKLFNHMECABIJ $.
    $( [26-Jun-2014] $)

  niclem84 $p |- ( ( ph -/\ ( ( ( ( ps -/\ ch ) -/\ ( ( ch -/\ ps ) -/\ ( th -/\ ps ) ) ) -/\ ( ( ta -/\ ch ) -/\ ( ( ch -/\ ta ) -/\ ( th -/\ ta ) ) ) ) -/\ et ) ) -/\ ( ( ( ( ( ( ps -/\ ch ) -/\ ( ( ch -/\ ps ) -/\ ( th -/\ ps ) ) ) -/\ ( ( ta -/\ ch ) -/\ ( ( ch -/\ ta ) -/\ ( th -/\ ta ) ) ) ) -/\ et ) -/\ ph ) -/\ ( ( et -/\ ( ze -/\ ch ) ) -/\ ph ) ) ) $=
    ( wsi wna niclem54 niclem67 ax-ded ) BCICBIDBIIIECICEIDEIIIIZDGCIZIIHMFIZI
    OHIFNIZHIIIAOIOAIPAIIIBCDEGJMDNHFAKL $.
    $( [26-Jun-2014] $)

  niclem155 $p |- ( ( ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( th -/\ ch ) -/\ ( ( ch -/\ th ) -/\ ( ph -/\ th ) ) ) ) -/\ ( ta -/\ ch ) ) -/\ ( ( ( th -/\ ch ) -/\ ( ( ch -/\ th ) -/\ ( ph -/\ th ) ) ) -/\ ( ( et -/\ ch ) -/\ ( ( ch -/\ et ) -/\ ( ph -/\ et ) ) ) ) ) $=
    ( wna niclem49 niclem84 ax-ded ) DCGCDGADGGGZFCGCFGAFGGGZGZLKGABCGGKGZGZGOM
    GNECGGMGKFCABHMFCADNEIJ $.
    $( [26-Jun-2014] $)

  niclem210 $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( ( ps -/\ ch ) -/\ ph ) -/\ ( ( ch -/\ ch ) -/\ ph ) ) ) $=
    ( wsi wze wrh wna ax-org niclem67 ax-ded niclem155 ) CCGZLBCGZGGZDMGMDGLDGG
    GZGZBMGZGZOAMGMAGLAGGGQQNGZGZSQGZRBBCCHQEMGMEGLEGGGZOGGFSGSFGPFGGGTUARGGBBC
    ECDIQUBOFNQIJJLLMDBAKJ $.
    $( [26-Jun-2014] $)

  niclem264 $p |- ( ( ( ph -/\ ps ) -/\ ( ph -/\ ps ) ) -/\ ( ( ( ps -/\ ps ) -/\ ch ) -/\ ( ( ps -/\ ps ) -/\ ch ) ) ) $=
    ( wna niclem210 ax-ded ) BBDCDZGDZCABDZDZDZJHDIIDHDJICDZGDZDMJDKCABEJLGEFHC
    IEF $.
    $( [26-Jun-2014] $)

  niclem298 $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( ( th -/\ th ) -/\ th ) -/\ ( ( th -/\ th ) -/\ th ) ) ) $=
    ( wta wet wna niclem264 ax-ded niclem84 ) DDGZDGZLGZECGCEGDEGGGFCGCFGDFGGGG
    AGZGZNMGABCGGMGMMGOOKDDHLLNHIMECDFABJI $.
    $( [26-Jun-2014] $)

  niclem305 $p |- ( ( ph -/\ ( ( ps -/\ ps ) -/\ ps ) ) -/\ ( ( ( ( ps -/\ ps ) -/\ ps ) -/\ ph ) -/\ ( ch -/\ ph ) ) ) $=
    ( wth wta wna niclem298 niclem155 ax-ded ) CDBBFBFZFFZEJFZJEFCEFFZFZFJJFFNA
    JFJAFCAFFFKLMBGCDJEJAHI $.
    $( [26-Jun-2014] $)

  niclem343 $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( ( ps -/\ ch ) -/\ ph ) -/\ ( ( ch -/\ ( ( th -/\ th ) -/\ th ) ) -/\ ph ) ) ) $=
    ( wna niclem305 ax-org ax-ded ) CDDEDEZEZICEZBCEZEEZMALELAEJAEEECDBFJKLAGH
    $.
    $( [26-Jun-2014] $)

  niclem461 $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( ( ps -/\ ch ) -/\ ph ) -/\ ( ( ps -/\ ch ) -/\ ph ) ) ) $=
    ( wth wet wta wze wsi wrh wmu wna niclem54 ax-org ax-ded niclem50 niclem298
    niclem210 niclem343 ) DCKCDKEDKKKFCKCFKEFKKKKZBCKZTKZKZATKTAKZUCKKZKZUATKZK
    ZUDUDUFTUAKUBKZKZUHUFKUGSETKKZUJUIDCEFBLSETUAMNUFTTTUBAONUDUDKZUEUEKZKZULUK
    KUGUKKULUEKZUEULKUMGHIKKZUOJIKIJKGJKKKZKKUNUNGHIJMUOUOUPUEPNULUBUDQNUKUEUET
    RNN $.
    $( [26-Jun-2014] $)

  niclem493 $p |- ( ( ( ( ph -/\ ps ) -/\ ch ) -/\ ( ( th -/\ th ) -/\ th ) ) -/\ ( ch -/\ ( ph -/\ ps ) ) ) $=
    ( wna niclem461 niclem343 ax-ded ) CABEZEZICEZKEZELJEKDDEDEEJECABFJKKDGH $.
    $( [26-Jun-2014] $)

  niclem609 $p |- ( ( ( ( ph -/\ ps ) -/\ ( ( ps -/\ ph ) -/\ ( ps -/\ ph ) ) ) -/\ ( ch -/\ ( ps -/\ ps ) ) ) -/\ ( ch -/\ ( th -/\ ps ) ) ) $=
    ( wta wna niclem493 niclem461 ax-ded ax-org niclem50 niclem49 ) CDBFFZABFB
    AFZNFFZCBBFZFZFZFZRMFZTRQOFPBFZFZFZUBRFZSUDUCUCCPOBGUBOQHIMEQFQEFUAEFFFZUBF
    ZFZUGUCUDSFFUFUABPFZQFZFZFZUJUFFUGUJUJUEFZFZULUJFZUKUAUHQEJUFUBUEFZULFFZUPU
    MUNUKFFUJUIUAFZUBFFZURUPUABBBQAKUJUQUBUEJIUFUOULUJJIIUFPBCDLIMUEUBRJIIMOQHI
    $.
    $( [26-Jun-2014] $)

  niclem697 $p |- ( ( ph -/\ ps ) -/\ ( ( ps -/\ ph ) -/\ ( ps -/\ ph ) ) ) $=
    ( wch wna niclem609 niclem493 ax-ded ) ABDZBADZIDZDZCBDZLDZBBDDZDMLDDNKABMC
    EHJNLFG $.
    $( [26-Jun-2014] $)

  niclem714 $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( ( th -/\ ( ph -/\ ta ) ) -/\ ( ( ( ph -/\ ta ) -/\ th ) -/\ ( ( ph -/\ ta ) -/\ th ) ) ) -/\ ( ( ta -/\ ch ) -/\ ( ( ph -/\ ta ) -/\ ( ph -/\ ta ) ) ) ) ) $=
    ( wna niclem609 niclem49 ax-ded ) DAEFZFJDFZKFFECFZJJFFFZLCEFZJFFZFOMFABCFF
    MFDJLNGMECABHI $.
    $( [26-Jun-2014] $)

  niclem949 $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ph -/\ ( ch -/\ ps ) ) ) ) $=
    ( wta wth wna niclem697 niclem461 ax-ded niclem714 ) ACBFZFZLFZKAFZFZABCFZF
    ZMFZRNMFOOKAGNLLHIQNNFFZDRFRDFZTFFORRFFKPPFFENFNEFZUAFFSCBGKPPEAJIQNNDMJII
    $.
    $( [26-Jun-2014] $)

  niclem994 $p |- ( ( ph -/\ ( ps -/\ ( ch -/\ th ) ) ) -/\ ( ( ( ps -/\ ( th -/\ ch ) ) -/\ ph ) -/\ ( ( ps -/\ ( th -/\ ch ) ) -/\ ph ) ) ) $=
    ( wta wna niclem949 niclem714 ax-ded ) BDCFFZBCDFFZKFFEJAFZFLEFZMFFAKFLLFFB
    DCGJKKEAHI $.
    $( [26-Jun-2014] $)

  nic $p |- ( ( ph -/\ ( ps -/\ ch ) ) -/\ ( ( th -/\ ( th -/\ th ) ) -/\ ( ( ta -/\ ps ) -/\ ( ( ph -/\ ta ) -/\ ( ph -/\ ta ) ) ) ) ) $=
    ( wet wze wna niclem714 niclem305 niclem210 ax-ded niclem994 niclem949 ) A
    BCHHZEBHAEHZPHHZDDDHZHZHZHZOSQHHZUBTACBHHZHZUAUAUCFPHPFHZUEHHZQHZHZUDUDACBF
    EITUGUGHZHZGUDHUDGHZUKHHUHUDUDHHUIQRDHZHZHZUJUJUMULQHZUGHZHUPUMHUNQDUFJUMUO
    UGKLUIQRDMLTUGUGGUCILLTACBMLOQSNL $.
    $( [26-Jun-2014] $)

