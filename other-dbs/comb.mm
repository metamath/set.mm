$( -*-text-*- $)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Pre-logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c |- wff ( ) -> $.
  $v ph ps ch th ta et ze si rh $.

  wph $f wff ph $.
  wps $f wff ps $.
  wch $f wff ch $.
  wth $f wff th $.
  wta $f wff ta $.
  wet $f wff et $.
  wze $f wff ze $.
  wsi $f wff si $.
  wrh $f wff rh $.


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
                           Combinatorial calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  wi $a wff ( ph -> ps ) $.

  ax-K $a |- ( ph -> ( ps -> ph ) ) $.

  ax-S $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.

  ${
    min $e |- ph $.
    maj $e |- ( ph -> ps ) $.

    ax-D $a |- ps $.
  $}

  ${
    DK.1 $e |- ph $.

    DK $p |- ( ps -> ph ) $=
      ( wi ax-K ax-D ) ABADCABEF $.
      $( [?] $) $( [10-Oct-2011] $)
  $}

  ${
    DS.1 $e |- ( ph -> ( ps -> ch ) ) $.

    DS $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $=
      ( wi ax-S ax-D ) ABCEEABEACEEDABCFG $.
      $( [?] $) $( [10-Oct-2011] $)
  $}

  I $p |- ( ph -> ph ) $=
    ( wps wi ax-K DS ax-D ) ABACZCAACABDAGAAGDEF $.
    $( [?] $) $( [10-Oct-2011] $)

  B $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi ax-K ax-S DK DS ax-D ) ABDZCJDZDJCADCBDDZDJCEJKLKLDJCABFGHI $.
    $( [?] $) $( [10-Oct-2011] $)

  ${
     DB.1 $e |- ( ph -> ps ) $.
     
     DB $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
       ( wi B ax-D ) ABECAECBEEDABCFG $.
       $( [?] $) $( [10-Oct-2011] $)
  $}

  ${
     DDB.1 $e |- ( ps -> ch ) $.
     DDB.2 $e |- ( ph -> ps ) $.
     
     DDB $p |- ( ph -> ch ) $=
       ( wi DB ax-D ) ABFACFEBCADGH $.
       $( [?] $) $( [10-Oct-2011] $)
  $}

  C $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi ax-K DK B ax-S DDB DS ax-D ) ABCDDZBABDZDZDLBACDZDZDNLBAEFLNPLMODNPDMO
    BGABCHIJK $.
    $( [?] $) $( [10-Oct-2011] $)

  ${
     DC.1 $e |- ( ph -> ( ps -> ch ) ) $.

     DC $p |- ( ps -> ( ph -> ch ) ) $=
       ( wi C ax-D ) ABCEEBACEEDABCFG $.
       $( [?] $) $( [10-Oct-2011] $)
  $}

  succ $p |- ( ( ( ph -> ps ) -> ( ch -> ph ) ) -> 
       	       ( ( ph -> ps ) -> ( ch -> ps ) ) ) $=
    ( wi B DS ) ABDCADCBDABCEF $.
    $( [?] $) $( [10-Oct-2011] $)
