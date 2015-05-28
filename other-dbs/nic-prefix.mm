  
  $c ( $.  
  $c ) $.  
  $c | $. 
  $c wff $.
  $c |- $. 
  $v ph $. 
  $v ps $.  
  $v ch $.  
  $v th $.  
  $v ta $.  
  $v ze $.

  wph $f wff ph $.
  wps $f wff ps $.
  wch $f wff ch $.
  wth $f wff th $.
  wta $f wff ta $.
  wze $f wff ze $.

  wna $a wff ( | ph ps ) $.

  ax-nic $a |- ( | ( | ph ( | ch ps ) )
  	       	 ( | ( | th ( | th th ) ) 
		     ( | ( | th ch ) ( | ( | ph th ) ( | ph th ) ) ) )
	       ) $.

  ${
     ax-ded.min $e |- ph $.
     ax-ded.maj $e |- ( | ph ( | ps ch ) ) $.

     ax-ded $a |- ch $.
  $}

  ${
     axi.1 $e |- ( | ph ( | ps ch ) ) $.

     axi $p |- ( | ( | th ps ) ( | ( | ph th ) ( | ph th ) ) ) $=
       ( wna ax-nic ax-ded ) ABCFFDDDFFDBFADFZIFFEACBDGH $.
       $( [?] $) $( [15-Dec-2010] $)
  $}

  lem1 $p |- ( | ( | ph ( | ps ( | ps ps ) ) ) ( | ( | ( | ch ( | th ta ) ) ph ) ( | ( | ch ( | th ta ) ) ph ) ) ) $=
    ( wna ax-nic axi ) CDEFFBBBFFBDFCBFZIFFACEDBGH $.
    $( [?] $) $( [15-Dec-2010] $)

  id $p |- ( | ph ( | ph ph ) ) $=
    wph wph wph wna wna wph wph wph wna wna wph wph wna wph wph wna wph wph wna
    wna wna wna wna wph wph wna wph wph wna wph wph wna wna wna wph wph wph wna
    wna wph wph wph wph ax-nic wph wph wna wph wph wna wph wph wna wna wna wph
    wph wph wna wna wna wph wph wph wna wna wna wph wph wph wna wna wph wph wph
    wna wna wph wph wna wph wph wna wph wph wna wna wna wna wna wph wph wna wph
    wph wna wph wph wna wna wna wph wph wph wna wna wna wna wph wph wph wna wna
    wph wph wph wna wna wph wph wna wph wph wna wph wph wna wna wna wna wna wph
    wph wna wph wph wna wph wph wna wna wna wph wph wph wna wna wna wna wph wph
    wph wna wna wph wph wph wna wna wph wph wna wph wph wna wph wph wna wna wna
    wna wna wph wph wna wph wph wna wph wph wna wna wna wph wph wph wna wna wna
    wph wph wph wna wna wna wph wph wna wph wph wna wph wph wna wna wna wph wph
    wph wna wna wna wph wph wph wna wna wna wph wph wph wph ax-nic wph wph wna
    wph wph wna wph wph wna wna wna wph wph wph wna wna wna wph wph wph wna wna
    wph wph wna wph wph wna wph wph wna wna wna wna wph wph wph wna wna wph wph
    wna wph wph wna wph wph wna wna wna wna wph wph wph wna wna wph wph wna wph
    wph wna wph wph wna wna wna wph wph wph wph lem1 axi ax-ded wph wph wna wph
    wph wna wph wph wna wna wna wph wph wph wna wna wna wph wph wph wph wna wna
    wph wph wph wna wna wph wph wna wph wph wna wph wph wna wna wna lem1 ax-ded
    ax-ded $.
    $( [?] $) $( [22-Jun-2011] $)
    $( | [?] $) $( | [15-Dec-2010] $)

  comm $p |- ( | ( | ph ps ) ( | ( | ps ph ) ( | ps ph ) ) ) $=
    ( id axi ) BBBABCD $.
    $( [?] $) $( [15-Dec-2010] $)

  ${
     commi.1 $e |- ( | ph ps ) $.

     commi $p |- ( | ps ph ) $=
       ( wna comm ax-ded ) ABDBADZGCABEF $.
       $( [?] $) $( [15-Dec-2010] $)
  $}
