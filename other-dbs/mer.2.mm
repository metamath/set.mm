$( -*-text-*- $)

  $c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c -> $. $( Right arrow (read:  "implies") $)
  $c -. $. $( Right handle (read:  "not") $)
  $c wff $. $( Well-formed formula symbol (read:  "the following symbol
               sequence is a wff") $)
  $c |- $. $( Turnstile (read:  "the following symbol sequence is provable" or
              'a proof exists for") $)

  $( wff variable sequence:  ph ps ch th ta et ze si rh mu la ka $)
  $( Introduce some variable names we will use to represent well-formed
     formulas (wff's). $)
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
  wph $f wff ph $.
  wps $f wff ps $.
  wch $f wff ch $.
  wth $f wff th $.
  wta $f wff ta $.
  wet $f wff et $.
  wze $f wff ze $.
  wsi $f wff si $.
  wrh $f wff rh $.
  wmu $f wff mu $.
  wla $f wff la $.
  wka $f wff ka $.

  wn $a wff -. ph $.
  wi $a wff ( ph -> ps ) $.

  ax-mer $a |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $.

  ${
    ax-mp.min $e |- ph $.
    ax-mp.maj $e |- ( ph -> ps ) $.

    ax-mp $a |- ps $.
  $}

  ${
    mp2.1 $e |- ph $.
    mp2.2 $e |- ps $.
    mp2.3 $e |- ( ph -> ( ps -> ch ) ) $.

    $( Double invocation of ~ ax-mp . $)
    mp2 $p |- ch $=
      ( wi ax-mp ) BCEABCGDFHH $.
      $( [?] $) $( [15-Feb-2013] $)
  $}

  ${
    meri.1 $e |- ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) -> ta ) $.

    $( Inference form of ~ ax-mer $)
    meri $p |- ( ( ta -> ph ) -> ( th -> ph ) ) $=
      ( wi wn ax-mer ax-mp ) ABGCHDHGGCGEGEAGDAGGFABCDEIJ $.
      $( [?] $) $( [15-Feb-2013] $)
  $}

  ${
     merii.1 $e |- ( ( ( ( ps -> et ) -> ( -. ze -> -. ph ) ) -> ze ) -> 
     	      	   ( ( ch -> ta ) -> ( -. ps -> -. th ) ) ) $.

     $( Double invocation of ~ meri $)
     merii $p |- ( ( ( ph -> ps ) -> ch ) -> ( th -> ch ) ) $=
       ( wi wn meri ) CEBDABIBFGACEIBJDJIIHKK $.
       $( [?] $) $( [15-Feb-2013] $)
  $}

  $( If identity implies a consequence, then anything implies that
     consequence $)
  idant $p |- ( ( ( ph -> ph ) -> ps ) -> ( ch -> ps ) ) $=
    ( wth wn wi ax-mer meri merii ) AABCDAEZJCEZFZLJBDFZEFZELEZEFAMAJFOJFFJKNOA
    GHI $.
    $( [?] $) $( [15-Feb-2013] $)

  $( Double deduction form of identity $)
  iddd $p |- ( ph -> ( ps -> ( ch -> ch ) ) ) $=
    ( wi idant ax-mp ) CCDZGDBGDZDAHDCGBEGHAEF $.
    $( [?] $) $( [15-Feb-2013] $)

  $( Eliminate an antecedent from an implication $)
  elimant $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    ( wth wi wn iddd merii ) ABCBDDDBDEDFAFEEDECDEBFGH $.
    $( [?] $) $( [15-Feb-2013] $)

  ${
     elimanti.1 $e |- ( ( ph -> ps ) -> ch ) $.

     $( Inference form of ~ elimant $)
     elimanti $p |- ( ps -> ch ) $=
       ( wi elimant ax-mp ) ABECEBCEDABCFG $.
       $( [?] $) $( [15-Feb-2013] $)
  $}

  $( Rule of contraction. $)
  pm2.24 $p |- ( ph -> ( -. ph -> ps ) ) $=
    ( wch wn wi elimant meri ax-mp ) BDZADZEZBEZJBEZEAMEIJBFMCBALMCEKBFGH $.
    $( [?] $) $( [5-Feb-2013] $)

  $( Deduction form of ~ id $)
  idd $p |- ( ph -> ( ps -> ps ) ) $=
    ( wch wi wn ax-mer iddd ax-mp ) CCDZCEZJDDCDCDIIDDZABBDDCCCCCFKABGH $.
    $( [?] $) $( [15-Feb-2013] $)

  $( Rule of identity $)
  id $p |- ( ph -> ph ) $=
    ( wps wi wn ax-mer idd ax-mp ) BBCZBDZICCBCBCHHCCZAACBBBBBEJAFG $.
    $( [?] $) $( [15-Feb-2013] $)

  $( Rule of the true consequence $)
  tc $p |- ( ph -> ( ps -> ph ) ) $=
    ( wch wi wn idant ax-mer meri mp2 ) AADBADZDZAJDZDCCDZCEZNDDCDCDMMDDZLAJAFC
    CCCCGLAEOEDZEBEDAOKAJPBAGHI $.
    $( [?] $) $( [15-Feb-2013] $)

  ${
     tci.1 $e |- ph $.

     $( Inference form of ~ tc $)
     tci $p |- ( ps -> ph ) $=
       ( wi tc ax-mp ) ABADCABEF $.
       $( [?] $) $( [15-Feb-2013] $)
  $}

  $( Double negation elimination $)
  notnot1 $p |- ( -. -. ph -> ph ) $=
    ( wps wi wn tc ax-mer idant ax-mp merii mp2 meri ) BBCZBDZMCCBCBCLLCCZDZADZ
    DZCQACZDZQCCZRCZNRRUACNUARTEBBBBBFZQAUANOBBUAUACUAOCPOCCZCABCMQDCCBCZUCCOQR
    PUAFUAUCUDGHIJUBRODOCZDSDCONTQAUESOFKJ $.
    $( [?] $) $( [15-Feb-2013] $)

  $( The law of absorption $)
  absorb $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    ( wch wi wn ax-mer elimanti merii ax-mp mp2 ) AABDZDZLKDZDZCCDZCEZPDDCDCDOO
    DDZMKCDPLEZDDCDZADNDQNKCCLAFCCCCCFZSANQQEZBNUADAEZUADDZERDZQMUCDZKUDESEDZDU
    DDZUCDZTLMUCUACDZPUBEDDCDNUCUACCUBNFGGMUEUHDZDQUJDUCCDPUGEDDCDMUJUCCCUGMFGL
    KUJQUAUFUCUEUHUJUADKEZUADDZUIPUKEDDCDUJULUACCUKUJFGGHIJHJTMCDPUADDCDZLDNQMD
    ZDZDQUOMCCQLFTUMLUOQUAKUOUADRUADDZEUADZQUNUPDZMUQEUMEDZDUQDZUPDZTNUNUPUIPRE
    DDCDUOUPUACCRUOFGGUNURVADZDQVBDUPCDPUTEDDCDUNVBUPCCUTUNFGQMVBQUAUSUPURVAVBU
    ADMEZUADDZUIPVCEDDCDVBVDUACCVCVBFGGHIJHJJ $.
    $( [?] $) $( [15-Feb-2013] $)

  ${
    absorbi.1 $e |- ( ph -> ( ph -> ps ) ) $.

    $( Inference form of ~ absorb . $)
    absorbi $p |- ( ph -> ps ) $=
      ( wi absorb ax-mp ) AABDZDGCABEF $.
      $( [?] $) $( [15-Feb-2013] $)
  $}

  $( Proof by contradiction $)
  pm2.18 $p |- ( ( -. ph -> ph ) -> ph ) $=
    ( wps wn wi ax-mer merii tci mp2 elimanti ax-mp absorbi meri ) ACZADZAANCZM
    NMAODZMCZODZDZMDZMSTTMDDZOBDBCZQCDDBDZADSDBBDZUBUBDDBDBDUDUDDDZSOBBQAEBBBBB
    EUCASUEUECZBBSUFDMUFDDABDUBUCCDDBDPRUFMQUFCPCDZCRCZCDUFQOUGUHUFEFGFHMBDUBTC
    DDBDSUAMBBTSEIJKLK $.
    $( [?] $) $( [7-Feb-2013] $)

  $( A closed form of syllogism (see ~ syl ). $)
  imim1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    ( wth wi wn ax-mer tc elimanti ax-mp absorbi merii tci mp2 idant meri ) CDE
    ZAFZFZFZREZEZSEZBEZBCEACEEZEABEZUEECDSABGUEDUFFZFZUFUDUFUDEUEDEZUHFZUGEZEZU
    HEZUDEBDAUCABDEZRUCFZEZEZAEZAUPURURAEEZDDFZFZDEEZUOEZUOEZUPVCUOVBVCVDEZDVAH
    ZUODEZUTVCFEEDEVBVEUODDVCVBGIJKUODUORVCUOFZSEZVGVIEZUOEVCEZDDEZUTUTEEDEDEVL
    VLEEZUCSEZVIDDDDDGZUCSUBUCVNEZRREZUAEZUBRDEZUTTFEEDEZREVREVMVRRDDTRGVOVTRVR
    VMVMFZDDVRWAESWAEEVSUTVTFEEDEVQUAWASTWAFZVQFEZFUAFZFEWATRWCWDWAGLMLNRUAQOJS
    DEZUTUOEEDEUBVPSDDUCUBGIJKWEUTVHFEEDEZUCEVNVIEZEVMWGESDDVHUCGWFUCWGVMWADDWG
    WAEUOWAEEUCDEUTWFFEEDEVNVIWAUOVHWBVNFEZFVIFZFEWAVHSWHWIWAGLMLJNVGVIVKVGUTVB
    FEZEDEVJVKUODDVBVJGIIJPJUNUPUSADEUTURFEEDEUQUSADDURUQGIIJKPUDDUFUMUFUDDEZUG
    UMFZEZEZUFEZUFWMWOWOUFEEZVBWLEZWLEZWMWQWLVBWQWREZVFWLDEZUTWQFEEDEVBWSWLDDWQ
    VBGIJKWLDWLUGWQWLFZUHEZWTXBEZWLEWQEZVMUMUHEZXBVOUMUHULUMXEEZUGUGEZUKEZULUGD
    EZUTUJFEEDEZUGEXHEVMXHUGDDUJUGGVOXJUGXHVMWADDXHWAEUHWAEEXIUTXJFEEDEXGUKWAUH
    UJWBXGFEZFUKFZFEWAUJUGXKXLWAGLMLNUGUKUIOJUHDEZUTWLEEDEULXFUHDDUMULGIJKXMUTX
    AFEEDEZUMEXEXBEZEVMXOEUHDDXAUMGXNUMXOVMWADDXOWAEWLWAEEUMDEUTXNFEEDEXEXBWAWL
    XAWBXEFEZFXBFZFEWAXAUHXPXQWAGLMLJNWTXBXDWTWJEDEXCXDWLDDVBXCGIIJPJWKWMWPUFDE
    UTWOFEEDEWNWPUFDDWOWNGIIJKPJPJ $.
    $( [?] $) $( [15-Feb-2013] $)

  ${
    imim1i.1 $e |- ( ph -> ps ) $.

    $( Inference form of ~ imim1 $)
    imim1i $p |- ( ( ps -> ch ) -> ( ph -> ch ) ) $=
      ( wi imim1 ax-mp ) ABEBCEACEEDABCFG $.
      $( [?] $) $( [15-Feb-2013] $)
  $}

  ${
     syl.1 $e |- ( ph -> ps ) $.
     syl.2 $e |- ( ps -> ch ) $.

     $( The law of syllogism $)
     syl $p |- ( ph -> ch ) $=
       ( wi imim1i ax-mp ) BCFACFEABCDGH $.
       $( [?] $) $( [15-Feb-2013] $)
  $}

  $( The law of assertion $)
  assert $p |- ( ph -> ( ( ph -> ps ) -> ps ) ) $=
    ( wi imim1 elimanti absorb syl ) AABCZHBCZCZIHAJHABDEHBFG $.
    $( [?] $) $( [15-Feb-2013] $)

  $( Commutation law for premeses in an implication $)
  com12 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    ( wi imim1 assert imim1i syl ) ABCDZDICDZACDZDBKDAICEBJKBCFGH $.
    $( [?] $) $( [15-Feb-2013] $)

  ${
     com12i.1 $e |- ( ph -> ( ps -> ch ) ) $.

     $( Inference form of ~ com12 $)
     com12i $p |- ( ps -> ( ph -> ch ) ) $=
       ( wi com12 ax-mp ) ABCEEBACEEDABCFG $.
       $( [?] $) $( [15-Feb-2013] $)
  $}

  $( A closed form of syllogism. $)
  imim2 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    ( wi imim1 com12i ) CADABDCBDCABEF $.
    $( [?] $) $( [15-Feb-2013] $)

  ${
     imim2i.1 $e |- ( ph -> ps ) $.

     $( Inference form of ~ imim2 . $)
     imim2i $p |- ( ( ch -> ph ) -> ( ch -> ps ) ) $=
       ( wi imim2 ax-mp ) ABECAECBEEDABCFG $.
       $( [?] $) $( [15-Feb-2013] $)
  $}

  $( The law of distribution $)
  dist $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    ( wi com12 imim2 absorb imim2i syl ) ABCDDBACDZDZABDZJDZABCEKLAJDZDMBJAFNJL
    ACGHII $.
    $( [?] $) $( [15-Feb-2013] $)


  ${
     syl5.1 $e |- ( ph -> ( ps -> ch ) ) $.
     syl5.2 $e |- ( th -> ps ) $.

     $( A syllogism rule of inference. The second premise is used to 
     	replace the second antecedent of the first premise. $)
     syl5 $p |- ( ph -> ( th -> ch ) ) $=
       ( wi imim1i syl ) ABCGDCGEDBCFHI $.
       $( [?] $) $( [15-Feb-2013] $)
  $}

  ${
     syl6.1 $e |- ( ph -> ( ps -> ch ) ) $.
     syl6.2 $e |- ( ch -> th ) $.

     $( A syllogism rule of inference. The second premise is used to 
     	replace the consequent of the first premise. $)
     syl6 $p |- ( ph -> ( ps -> th ) ) $=
       ( wi imim2i syl ) ABCGBDGECDBFHI $.
       $( [?] $) $( [15-Feb-2013] $)
  $}


  $( From a wff and its negation, anything is true $)
  pm2.21 $p |- ( -. ph -> ( ph -> ps ) ) $=
    ( wn pm2.24 com12i ) AACBABDE $.
    $( [?] $) $( [15-Feb-2013] $)

  $( Contraposition law $)
  con4 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    ( wn wi pm2.21 imim2i dist syl pm2.18 syl6 tc syl5 ) ACZBCZDZMBDZABOPMADZAO
    MBADZDPQDNRMBAEFMBAGHAIJBMKL $.
    $( [?] $) $( [15-Feb-2013] $)
