  $c -> ( ) _|_ wff |- $.
  $v ph ps ch th ta et $.
  
  wph $f wff ph $.
  wps $f wff ps $.
  wch $f wff ch $.
  wth $f wff th $.
  wta $f wff ta $.
  wet $f wff et $.

  wf $a wff _|_ $.
  wi $a wff ( ph -> ps ) $.

  ax-co $a |- ( ( ( ( ( ph -> ps ) -> ( ch -> _|_ ) ) -> th ) -> ta ) ->
  	      	( ( ta -> ph ) -> ( ch -> ph ) ) ) $.

  ${
     ax-mp.min $e |- ph $.
     ax-mp.maj $e |- ( ph -> ps ) $.

     ax-mp $a |- ps $.
  $}

  ${
     axi.1 $e |- ( ( ( ( ph -> ps ) -> ( ch -> _|_ ) ) -> th ) -> ta ) $.

     axi $p |- ( ( ta -> ph ) -> ( ch -> ph ) ) $=
       ( wi wf ax-co ax-mp ) ABGCHGGDGEGEAGCAGGFABCDEIJ $.
       $( [?] $) $( [28-Dec-2010] $)
  $}

  ${
    detach.1 $e |- ( ( ( ( ( ( ph -> ps ) -> ( ch -> _|_ ) ) -> th ) -> ta ) ->
  	      	( ( ta -> ph ) -> ( ch -> ph ) ) ) -> et ) $.

    detach $p |- et $=
      ( wi wf ax-co ax-mp ) ABHCIHHDHEHEAHCAHHHFABCDEJGK $.
      $( [?] $) $( [28-Dec-2010] $)
  $}

  lem1 $p |- ( ph -> ( ps -> ( _|_ -> ch ) ) ) $=
    ( wth wf wi ax-co axi ax-mp ) DEDFZFZECFZFZBLFZFANFLEBJKJBEFZDLLEFOFEDBDEFL
    GHHNEALMLAEFZKNNEFPFECAKEFNGHHI $.
    $( [?] $) $( [28-Dec-2010] $)

  lem2 $p |- ( ph -> ( _|_ -> ps ) ) $=
    ( wch wf wi lem1 detach ) CCCCCADBEECCEZCDEECECEHHEEABFG $.
    $( [?] $) $( [28-Dec-2010] $)

  false $p |- ( _|_ -> ph ) $=
    ( wps wf wi lem2 detach ) BBBBBCADBBDZBCDDBDBDGGDDAEF $.
    $( [?] $) $( [28-Dec-2010] $)

  tc $p |- ( ph -> ( ps -> ph ) ) $=
    ( wch wi wf lem2 axi ax-co ax-mp detach ) CCCCCABADZDZEADZKDZLDCCDZCEDDCDCD
    OODDZLDKCACMKCDAEDDCDAFGLBEDPENAKBPEDEHGIJ $.
    $( [?] $) $( [28-Dec-2010] $)

  idd $p |- ( ph -> ( ps -> ps ) ) $= $.

  id $p |- ( ph -> ph ) $= $.
