$( -*-text-*- $)

  $c ( ) -> -. wff |- <-> \/ /\ -/\ $.

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

  wn $a wff -. ph $.
  wi $a wff ( ph -> ps ) $.
  wb $a wff ( ph <-> ps ) $.
  wa $a wff ( ph /\ ps ) $.
  wo $a wff ( ph \/ ps ) $.
  wna $a wff ( ph -/\ ps ) $.
  ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
  ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
  ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.

  ${
    ax-mp.min $e |- ph $.
    ax-mp.maj $e |- ( ph -> ps ) $.

    ax-mp $a |- ps $.
  $}


  df-bi $a |- -. ( ( ( ph <-> ps ) -> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) )
        -> -. ( -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) -> ( ph <-> ps ) ) ) $.
  df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.
  df-or $a |- ( ( ph \/ ps ) <-> ( -. ph -> ps ) ) $.
  df-nand $a |- ( ( ph -/\ ps ) <-> -. ( ph /\ ps ) ) $.


  ${
     a1i.1 $e |- ph $.

     a1i $p |- ( ps -> ph ) $=
       ( wi ax-1 ax-mp ) ABADCABEF $.
       $( [?] $) $( [31-Aug-2011] $)
  $}

  ${
     a2i.1 $e |- ( ph -> ( ps -> ch ) ) $.

     a2i $p |- ( ( ph -> ps ) -> ( ph -> ch ) ) $=
       ( wi ax-2 ax-mp ) ABCEEABEACEEDABCFG $.
       $( [?] $) $( [31-Aug-2011] $)
  $}

  ${
     con4i.1 $e |- ( -. ph -> -. ps ) $.

     con4i $p |- ( ps -> ph ) $=
       ( wn wi ax-3 ax-mp ) ADBDEBAECABFG $.
       $( [?] $) $( [31-Aug-2011] $)
  $}

  id $p |- ( ph -> ph ) $=
    ( wps wi ax-1 ax-2 ax-mp ) ABACZCZAACZABDAGACCHICAGDAGAEFF $.
    $( [?] $) $( [31-Aug-2011] $)

  ${
     syl.1 $e |- ( ph -> ps ) $.
     syl.2 $e |- ( ps -> ch ) $.

     syl $p |- ( ph -> ch ) $=
       ( wi a1i a2i ax-mp ) ABFACFDABCBCFAEGHI $.
       $( [?] $) $( [31-Aug-2011] $)
  $}

  fa $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( wn wi ax-1 ax-3 syl ) ACZBCZHDABDHIEBAFG $.
    $( [?] $) $( [31-Aug-2011] $)

  tafc $p |- ( ph -> ( -. ps -> -. ( ph -> ps ) ) ) $=
    ( wch wi wn ax-1 id a2i syl fa ax-3 ax-mp con4i a1i ax-2 ) AABDZBDZBEZPEZDZ
    APADQAPFPABPGHIQPREZDZTPBUABUADPUABUAEZCUCDZDUCRDUCCFUCUDRUCUAUDEZDUDRDUAUE
    JRUDKIHLMNHUBSEZUADZTUBUFUBDZUGUBUFFUHUFPDZDUHUGDUFUBPUFSUBEZDUBPDSUJJPUBKI
    HUHUIUGUFPUAOHLISRKIII $.
    $( [?] $) $( [31-Aug-2011] $)

  notnot1 $p |- ( ph -> -. -. ph ) $=
    ( wps wn wi ax-1 fa ax-3 syl a2i ax-mp con4i ) ACZCZAMCZBNDZDNLDNBENOLNMOCZ
    DOLDMPFLOGHIJK $.
    $( [?] $) $( [31-Aug-2011] $)

  inev $p |- ( ( ph -> ps ) -> ( ( -. ph -> ps ) -> ps ) ) $= ? $.

  dfbi1 $p |- ( ( ph <-> ps ) <-> -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ) $=
    ( wch wth wb wi wn df-bi ax-1 a1i con4i syl ax-mp ) ABEZABFBAFGFGZFONFGFGZN
    OEZABHCDCFFZPQFZCDISRSGZQPFZTFZRGZTUAIUCUBUBGUCGNOHJKLKMM $.
    $( [?] $) $( [31-Aug-2011] $)


