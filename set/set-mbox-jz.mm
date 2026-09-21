$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Jiamin Zhao
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Cross product and scalar triple product in RR^3
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( ` 1 ` is not equal to ` 3 ` .  (Contributed by Jiamin Zhao,
     1-Aug-2026.) $)
  1ne3 $p |- 1 =/= 3 $=
    ( c1 c3 1re 1lt3 ltneii ) ABCDE $.

  $( ` 2 ` is not equal to ` 3 ` .  (Contributed by Jiamin Zhao,
     1-Aug-2026.) $)
  2ne3 $p |- 2 =/= 3 $=
    ( c2 c3 2re 2lt3 ltneii ) ABCDE $.

  $( Membership of 1 in the integer interval ( 1 ... 3 ).  (Suggested by
     avekens.)  (Contributed by Jiamin Zhao, 1-Aug-2026.)  (Proof shortened by
     Jiamin Zhao, 13-Aug-2026.) $)
  1elfz13 $p |- 1 e. ( 1 ... 3 ) $=
    ( c1 c3 cfz co wcel cn cle wbr 1nn 3nn 1le3 elfz1b mpbir3an ) AABCDEAFEBFEA
    BGHIJKBALM $.

  $( Membership of 2 in the integer interval ( 1 ... 3 ).  (Suggested by
     tirix.)  (Contributed by Jiamin Zhao, 1-Aug-2026.)  (Proof shortened by
     Jiamin Zhao, 13-Aug-2026.) $)
  2elfz13 $p |- 2 e. ( 1 ... 3 ) $=
    ( c2 c1 c3 cfz co wcel cn cle wbr 2nn 3nn 2le3 elfz1b mpbir3an ) ABCDEFAGFC
    GFACHIJKLCAMN $.

  $( Membership of 3 in the integer interval ( 1 ... 3 ).  (Contributed by
     Jiamin Zhao, 1-Aug-2026.) $)
  3elfz13 $p |- 3 e. ( 1 ... 3 ) $=
    ( c3 cn wcel c1 cfz co 3nn elfz1end mpbi ) ABCADAEFCGAHI $.

  $( The components of a 3-dimensional real coordinate vector are real numbers.
     (Contributed by Jiamin Zhao, 31-Jul-2026.) $)
  rr3fvcl $p
    |- ( A e. ( RR ^m ( 1 ... 3 ) ) ->
         ( ( A ` 1 ) e. RR /\ ( A ` 2 ) e. RR /\ ( A ` 3 ) e. RR ) ) $=
  ( cr c1 c3 cfz co cmap wcel cfv elmapi 1elfz13 ffvelcdmd 2elfz13 3elfz13 3jca
  c2 a1i ) ABCDEFZGFHZCAIBHPAIBHDAIBHSRBCAABRJZCRHSKQLSRBPATPRHSMQLSRBDATDRHSNQ
  LO $.

  ${
    rr3fvd.1 $e |- ( ph -> A e. ( RR ^m ( 1 ... 3 ) ) ) $.
    $( First component of a 3-dimensional real coordinate vector is real.
       (Contributed by Jiamin Zhao, 10-Aug-2026.) $)
    rr3fv1cld $p |- ( ph -> ( A ` 1 ) e. RR ) $=
      ( c1 cfv cr wcel c2 c3 cfz co cmap w3a rr3fvcl syl simp1d ) ADBEFGZHBEFGZ
      IBEFGZABFDIJKLKGQRSMCBNOP $.

    $( Second component of a 3-dimensional real coordinate vector is real.
       (Contributed by Jiamin Zhao, 10-Aug-2026.) $)
    rr3fv2cld $p |- ( ph -> ( A ` 2 ) e. RR ) $=
      ( c1 cfv cr wcel c2 c3 cfz co cmap w3a rr3fvcl syl simp2d ) ADBEFGZHBEFGZ
      IBEFGZABFDIJKLKGQRSMCBNOP $.

    $( Third component of a 3-dimensional real coordinate vector is real.
       (Contributed by Jiamin Zhao, 10-Aug-2026.) $)
    rr3fv3cld $p |- ( ph -> ( A ` 3 ) e. RR ) $=
      ( c1 cfv cr wcel c2 c3 cfz co cmap w3a rr3fvcl syl simp3d ) ADBEFGZHBEFGZ
      IBEFGZABFDIJKLKGQRSMCBNOP $.
  $}

  $c crossp $.

  $( Extend class notation to include the cross product operation.
     (Contributed by Jiamin Zhao, 31-Jul-2026.) $)
  ccrossp $a class crossp $.

  ${
    $d k u v $.

    $( Define the cross product of two 3-dimensional real coordinate vectors.
       Vectors are represented as functions on ` ( 1 ... 3 ) ` .  (Contributed
       by Jiamin Zhao, 31-Jul-2026.) $)
    df-crossp $a |- crossp =
      ( u e. ( RR ^m ( 1 ... 3 ) ) ,
        v e. ( RR ^m ( 1 ... 3 ) ) |->
        ( k e. ( 1 ... 3 ) |->
          if ( k = 1 ,
             ( ( ( u ` 2 ) x. ( v ` 3 ) ) - ( ( u ` 3 ) x. ( v ` 2 ) ) ) ,
             if ( k = 2 ,
                ( ( ( u ` 3 ) x. ( v ` 1 ) ) - ( ( u ` 1 ) x. ( v ` 3 ) ) ) ,
                ( ( ( u ` 1 ) x. ( v ` 2 ) ) - ( ( u ` 2 ) x. ( v ` 1 ) ) )
              ) ) ) ) $.
  $}

  $c tripp $.

  $( Extend class notation to include the scalar triple product of
     3-dimensional real coordinate vectors.  (Contributed by Jiamin Zhao,
     31-Jul-2026.) $)
  ctripp $a class tripp $.

  ${
    $d k x y z $.

    $( Define the scalar triple product of three 3-dimensional real coordinate
       vectors as the dot product of the first vector ` x ` with the cross
       product of the other two ( ` y ` and ` z ` ).  Apply as
       ` ( y ( tripp `` x ) z ) ` .  Vectors are represented as functions on
       ` ( 1 ... 3 ) ` .  (Contributed by Jiamin Zhao, 31-Jul-2026.) $)
    df-tripp $a |- tripp =
      ( x e. ( RR ^m ( 1 ... 3 ) ) |->
        ( y e. ( RR ^m ( 1 ... 3 ) ) ,
          z e. ( RR ^m ( 1 ... 3 ) ) |->
          ( RRfld gsum
            ( k e. ( 1 ... 3 ) |->
              ( ( x ` k ) x. ( ( y crossp z ) ` k ) ) ) ) ) ) $.
  $}

  ${
    $d A k u v $.  $d B k u v $.

    $( Value of the cross product of two 3-dimensional real coordinate vectors
       as a function on ` ( 1 ... 3 ) ` .  (Contributed by Jiamin Zhao,
       31-Jul-2026.) $)
    crosspval $p
      |- ( ( A e. ( RR ^m ( 1 ... 3 ) ) /\
             B e. ( RR ^m ( 1 ... 3 ) ) )
      -> ( A crossp B ) =
        ( k e. ( 1 ... 3 ) |->
          if ( k = 1 ,
             ( ( ( A ` 2 ) x. ( B ` 3 ) ) - ( ( A ` 3 ) x. ( B ` 2 ) ) ) ,
             if ( k = 2 ,
                ( ( ( A ` 3 ) x. ( B ` 1 ) ) - ( ( A ` 1 ) x. ( B ` 3 ) ) ) ,
                ( ( ( A ` 1 ) x. ( B ` 2 ) ) - ( ( A ` 2 ) x. ( B ` 1 ) ) )
             ) ) ) ) $=
  ( vu vv c1 c3 co cv wceq c2 cfv cmul cmin fveq1 oveq1d oveq12d ifeq12d oveq2d
  cif cr cfz cmap cmpt ccrossp mpteq2dv df-crossp ovex mptex ovmpo ) DEABUAFGUB
  HZUCHZULCUKCIZFJZKDIZLZGEIZLZMHZGUOLZKUQLZMHZNHZUMKJZUTFUQLZMHZFUOLZURMHZNHZV
  GVAMHZUPVEMHZNHZTZTZUDCUKUNKALZGBLZMHZGALZKBLZMHZNHZVDVRFBLZMHZFALZVPMHZNHZWD
  VSMHZVOWBMHZNHZTZTZUDUECUKUNVOURMHZVRVAMHZNHZVDVRVEMHZWDURMHZNHZWDVAMHZVOVEMH
  ZNHZTZTZUDUOAJZCUKVNXBXCUNVCWNVMXAXCUSWLVBWMNXCUPVOURMKUOAOZPXCUTVRVAMGUOAOZP
  QXCVDVIWQVLWTXCVFWOVHWPNXCUTVRVEMXEPXCVGWDURMFUOAOZPQXCVJWRVKWSNXCVGWDVAMXFPX
  CUPVOVEMXDPQRRUFUQBJZCUKXBWKXGUNWNWAXAWJXGWLVQWMVTNXGURVPVOMGUQBOZSXGVAVSVRMK
  UQBOZSQXGVDWQWFWTWIXGWOWCWPWENXGVEWBVRMFUQBOZSXGURVPWDMXHSQXGWRWGWSWHNXGVAVSW
  DMXISXGVEWBVOMXJSQRRUFEDCUGCUKWKFGUBUHUIUJ $.
  $}

  ${
    crosspcled.1 $e |- ( ph -> A e. ( RR ^m ( 1 ... 3 ) ) ) $.
    crosspcled.2 $e |- ( ph -> B e. ( RR ^m ( 1 ... 3 ) ) ) $.
    $( Closure of the first component of the cross product's coordinate
       formula.  (Contributed by Jiamin Zhao, 11-Aug-2026.) $)
    crosspcle1d $p |-
      ( ph -> ( ( ( A ` 2 ) x. ( B ` 3 ) ) -
                ( ( A ` 3 ) x. ( B ` 2 ) ) ) e. RR ) $=
      ( c2 cfv c3 cmul co rr3fv2cld rr3fv3cld remulcld resubcld ) AFBGZHCGZIJHB
      GZFCGZIJAOPABDKACELMAQRABDLACEKMN $.

    $( Closure of the second component of the cross product's coordinate
       formula.  (Contributed by Jiamin Zhao, 11-Aug-2026.) $)
    crosspcle2d $p |-
      ( ph -> ( ( ( A ` 3 ) x. ( B ` 1 ) ) -
                  ( ( A ` 1 ) x. ( B ` 3 ) ) ) e. RR ) $=
      ( c3 cfv c1 cmul co rr3fv3cld rr3fv1cld remulcld resubcld ) AFBGZHCGZIJHB
      GZFCGZIJAOPABDKACELMAQRABDLACEKMN $.

    $( Closure of the third component of the cross product's coordinate
       formula.  (Contributed by Jiamin Zhao, 11-Aug-2026.) $)
    crosspcle3d $p |-
      ( ph -> ( ( ( A ` 1 ) x. ( B ` 2 ) ) -
                ( ( A ` 2 ) x. ( B ` 1 ) ) ) e. RR ) $=
      ( c1 cfv c2 cmul co rr3fv1cld rr3fv2cld remulcld resubcld ) AFBGZHCGZIJHB
      GZFCGZIJAOPABDKACELMAQRABDLACEKMN $.
  $}

  ${
    crosspd.1 $e |- ( ph -> A e. ( RR ^m ( 1 ... 3 ) ) ) $.
    crosspd.2 $e |- ( ph -> B e. ( RR ^m ( 1 ... 3 ) ) ) $.
    $( Lemma for ~ crosspcld .  Closure of the three-way coordinate case split
       used in the cross product's mapping rule.  (Contributed by Jiamin Zhao,
       11-Aug-2026.) $)
    crosspclem $p |- ( ph -> if ( k = 1 ,
      ( ( ( A ` 2 ) x. ( B ` 3 ) ) - ( ( A ` 3 ) x. ( B ` 2 ) ) ) ,
      if ( k = 2 , ( ( ( A ` 3 ) x. ( B ` 1 ) ) -
                     ( ( A ` 1 ) x. ( B ` 3 ) ) ) ,
                   ( ( ( A ` 1 ) x. ( B ` 2 ) ) -
                     ( ( A ` 2 ) x. ( B ` 1 ) ) ) ) ) e. RR ) $=
      ( cv c1 wceq c2 cfv c3 cmul co cmin cif cr crosspcle1d crosspcle2d ifcld
      crosspcle3d ) ADGZHIJBKZLCKZMNLBKZJCKZMNONUBJIZUEHCKZMNHBKZUDMNONZUIUFMNU
      CUHMNONZPQABCEFRAUGUJUKQABCEFSABCEFUATT $.

    $d A k $.  $d B k $.  $d ph k $.
    $( Closure of the cross product: the cross product of two 3-dimensional
       real coordinate vectors is again such a vector.  (Contributed by Jiamin
       Zhao, 12-Aug-2026.) $)
    crosspcld $p |- ( ph -> ( A crossp B ) e. ( RR ^m ( 1 ... 3 ) ) ) $=
      ( vk ccrossp co c1 c3 cfz cv wceq c2 cfv cmul cmin cif cr wcel syl2anc wf
      cmpt cmap crosspval crosspclem adantr fmpttd reex elmap sylibr eqeltrd
      ovex ) ABCGHZFIJKHZFLZIMNBOZJCOZPHJBOZNCOZPHQHUPNMUSICOZPHIBOZURPHQHVBUTP
      HUQVAPHQHRRZUCZSUOUDHZABVETCVETUNVDMDEBCFUEUAAUOSVDUBVDVETAFUOVCSAVCSTUPU
      OTABCFDEUFUGUHSUOVDUIIJKUMUJUKUL $.

    $( Value of the first component of the cross product.  (Contributed by
       Jiamin Zhao, 12-Aug-2026.) $)
    crosspv1d $p |-
      ( ph -> ( ( A crossp B ) ` 1 ) =
              ( ( ( A ` 2 ) x. ( B ` 3 ) ) - ( ( A ` 3 ) x. ( B ` 2 ) ) ) ) $=
      ( vk c1 cv wceq c2 cfv c3 cmul co cmin cif cfz ccrossp cr wcel iftrue a1i
      cmap cmpt crosspval syl2anc 1elfz13 crosspcle1d fvmptd4 ) AFGFHZGIZJBKZLC
      KZMNLBKZJCKZMNONZUJJIUNGCKZMNGBKZUMMNONURUOMNULUQMNONPZPZUPGLQNZBCRNZSUKU
      PUSUAABSVAUCNZTCVCTVBFVAUTUDIDEBCFUEUFGVATAUGUBABCDEUHUI $.

    $( Value of the second component of the cross product.  (Contributed by
       Jiamin Zhao, 12-Aug-2026.) $)
    crosspv2d $p |-
      ( ph -> ( ( A crossp B ) ` 2 ) =
              ( ( ( A ` 3 ) x. ( B ` 1 ) ) - ( ( A ` 1 ) x. ( B ` 3 ) ) ) ) $=
      ( vk c2 cv c1 wceq cfv c3 cmul co cmin cif cfz cr a1i wcel ccrossp id wne
      1ne2 eqnetrd necon2bi iffalsed iftrue cmap cmpt crosspval syl2anc 2elfz13
      eqtrd crosspcle2d fvmptd4 ) AFGFHZIJZGBKZLCKZMNLBKZGCKZMNONZUQGJZVAICKZMN
      IBKZUTMNONZVFVBMNUSVEMNONZPZPZVGILQNZBCUANZRVDVJVIVGVDURVCVIURUQGURUQIGUR
      UBIGUCURUDSUEUFUGVDVGVHUHUNABRVKUINZTCVMTVLFVKVJUJJDEBCFUKULGVKTAUMSABCDE
      UOUP $.

    $( Value of the third component of the cross product.  (Contributed by
       Jiamin Zhao, 12-Aug-2026.) $)
    crosspv3d $p |-
      ( ph -> ( ( A crossp B ) ` 3 ) =
              ( ( ( A ` 1 ) x. ( B ` 2 ) ) - ( ( A ` 2 ) x. ( B ` 1 ) ) ) ) $=
      ( vk c3 c1 wceq c2 cfv cmul co cmin cif cr id wne a1i wcel cv cfz ccrossp
      1ne3 eqnetrd necon2bi iffalsed 2ne3 eqtrd cmap cmpt crosspval crosspcle3d
      syl2anc 3elfz13 fvmptd4 ) AFGFUAZHIZJBKZGCKZLMGBKZJCKZLMNMZUQJIZVAHCKZLMH
      BKZUTLMNMZVFVBLMUSVELMNMZOZOZVHHGUBMZBCUCMZPUQGIZVJVIVHVMURVCVIURUQGURUQH
      GURQHGRURUDSUEUFUGVMVDVGVHVDUQGVDUQJGVDQJGRVDUHSUEUFUGUIABPVKUJMZTCVNTVLF
      VKVJUKIDEBCFULUNGVKTAUOSABCDEUMUP $.
  $}

  ${
    $d A k s w z $.  $d B k w z $.  $d C k w z $.  $d ph w z $.
    crosspdot0lem.1 $e |- ( ph -> A e. ( RR ^m ( 1 ... 3 ) ) ) $.
    crosspdot0lem.2 $e |- ( ph -> B e. ( RR ^m ( 1 ... 3 ) ) ) $.
    crosspdot0lem.3 $e |- ( ph -> C e. ( RR ^m ( 1 ... 3 ) ) ) $.
    $( Lemma for ~ crosspdotd .  Unfold the curried scalar triple product
       application into an explicit group sum.  (Contributed by Jiamin Zhao,
       12-Aug-2026.) $)
    crosspdot0lem $p |-
      ( ph -> ( B ( tripp ` A ) C ) =
        ( RRfld gsum ( k e. ( 1 ... 3 ) |->
                       ( ( A ` k ) x. ( ( B crossp C ) ` k ) ) ) ) ) $=
      ( vw vz vs co crefld cv cfv ccrossp cmul cmpt cgsu wceq cr c1 c3 cfz cmap
      ctripp cvv cmpo df-tripp fveq1 oveq1d mpteq2dv oveq2d mpoeq3dv wcel mpoex
      ovex a1i fvmptd3 wa oveq12 fveq1d adantl ovexd ovmpod ) AIJCDUAUBUCUDLZUE
      LZVGMEVFENZBOZVHINZJNZPLZOZQLZRZSLZMEVFVIVHCDPLZOZQLZRZSLZBUFOUGAKBIJVGVG
      MEVFVHKNZOZVMQLZRZSLZUHIJVGVGVPUHZVGUFUGKIJEUIWBBTZIJVGVGWFVPWHWEVOMSWHEV
      FWDVNWHWCVIVMQVHWBBUJUKULUMUNFWGUGUOAIJVGVGVPUAVFUEUQZWIUPURUSVJCTVKDTUTZ
      VPWATAWJVOVTMSWJEVFVNVSWJVMVRVIQWJVHVLVQVJCVKDPVAVBUMULUMVCGHAMVTSVDVE $.
  $}

  ${
    $d A k $.  $d B k $.  $d C k $.
    crosspdotd.1 $e |- ( ph -> A e. ( RR ^m ( 1 ... 3 ) ) ) $.
    crosspdotd.2 $e |- ( ph -> B e. ( RR ^m ( 1 ... 3 ) ) ) $.
    crosspdotd.3 $e |- ( ph -> C e. ( RR ^m ( 1 ... 3 ) ) ) $.
    $( Lemma for ~ crosspdotd .  Expand the group sum over ` ( 1 ... 3 ) ` into
       an explicit three-term sum.  (Contributed by Jiamin Zhao,
       12-Aug-2026.) $)
    crosspdotsumlem $p |- ( ph -> ( RRfld gsum
        ( k e. ( 1 ... 3 ) |-> ( ( A ` k ) x. ( ( B crossp C ) ` k ) ) ) ) =
      ( ( ( A ` 1 ) x. ( ( B crossp C ) ` 1 ) ) +
        ( ( ( A ` 2 ) x. ( ( B crossp C ) ` 2 ) ) +
          ( ( A ` 3 ) x. ( ( B crossp C ) ` 3 ) ) ) ) ) $=
      ( cr c1 c3 co wcel cfv cmul c2 caddc wceq a1i cz cfz cmap w3a crefld cmpt
      cv ccrossp cgsu ccnfld cress csu df-refld oveq1i fzfid wa wf simp1 elmapi
      syl ffvelcdmda simp2 simp3 crosspcld remulcld regsumfsum ctp 1p2e3 eqcomi
      3jca oveq2i fztp ax-mp eqtri sumeq1i eqidd 1p1e2 tpeq123d fveq2 rr3fv1cld
      1z oveq12d cc recnd rr3fv2cld rr3fv3cld 2z 3z 3pm3.2i wne 1ne2 1ne3 sumtp
      2ne3 addassd eqtrd 3eqtrd ) ABIJKUALZUBLZMZCWRMZDWRMZUCZUDEWQEUFZBNZXCCDU
      GLZNZOLZUEZUHLZJBNZJXENZOLZPBNZPXENZOLZKBNZKXENZOLZQLQLZRAWSWTXAFGHVIXBXI
      UIIUJLZXHUHLZWQXGEUKZXSXIYARXBUDXTXHUHULUMSXBWQXGEXBJKUNXBXCWQMUOXDXFXBWQ
      IXCBXBWSWQIBUPWSWTXAUQZBIWQURUSUTXBWQIXCXEXBXEWRMWQIXEUPXBCDWSWTXAVAWSWTX
      AVBVCZXEIWQURUSUTVDVEXBYBJJJQLZJPQLZVFZXGEUKZJPKVFZXGEUKZXSYBYHRXBWQYGXGE
      WQJYFUALZYGKYFJUAYFKVGVHVJJTMZYKYGRVTJVKVLVMVNSYHYJRXBYGYIXGEYLYGYIRVTYLJ
      JYEPYFKYLJVOYEPRYLVPSYFKRYLVGSVQVLVNSXBYJXLXOQLXRQLXSXBJPKXGEXLXOXRTTTXCJ
      RXDXJXFXKOXCJBVRXCJXEVRWAXCPRXDXMXFXNOXCPBVRXCPXEVRWAXCKRXDXPXFXQOXCKBVRX
      CKXEVRWAXBXLWBMXOWBMXRWBMXBXLXBXJXKXBBYCVSXBXEYDVSVDWCZXBXOXBXMXNXBBYCWDX
      BXEYDWDVDWCZXBXRXBXPXQXBBYCWEXBXEYDWEVDWCZVIYLPTMZKTMZUCXBYLYPYQVTWFWGWHS
      JPWIXBWJSJKWIXBWKSPKWIXBWMSWLXBXLXOXRYMYNYOWNWOWPWPUS $.

    $( Value of the scalar triple product, expanded into the standard six-term
       Sarrus polynomial.  (Contributed by Jiamin Zhao, 12-Aug-2026.) $)
    crosspdotd $p |- ( ph -> ( B ( tripp ` A ) C ) =
      ( ( ( ( ( A ` 1 ) x. ( B ` 2 ) ) x. ( C ` 3 ) ) -
          ( ( ( A ` 1 ) x. ( B ` 3 ) ) x. ( C ` 2 ) ) ) +
        ( ( ( ( ( A ` 2 ) x. ( B ` 3 ) ) x. ( C ` 1 ) ) -
            ( ( ( A ` 2 ) x. ( B ` 1 ) ) x. ( C ` 3 ) ) ) +
          ( ( ( ( A ` 3 ) x. ( B ` 1 ) ) x. ( C ` 2 ) ) -
            ( ( ( A ` 3 ) x. ( B ` 2 ) ) x. ( C ` 1 ) ) ) ) ) ) $=
      ( cfv co c1 cmul cmin caddc oveq12d recnd remulcld mulassd eqcomd eqtrd
      c3 vk ctripp crefld cv ccrossp cmpt cgsu c2 crosspdot0lem crosspdotsumlem
      crosspv1d oveq2d crosspv2d crosspv3d rr3fv1cld rr3fv2cld rr3fv3cld subdid
      cfz ) ACDBUBHIUCUAJTUSIUAUDZBHUTCDUEIZHKIUFUGIZJBHZUHCHZKITDHZKIZVCTCHZKI
      UHDHZKIZLIZUHBHZVGKIJDHZKIZVKJCHZKIVEKIZLIZTBHZVNKIVHKIZVQVDKIVLKIZLIZMIZ
      MIZABCDUAEFGUIAVBVCJVAHZKIZVKUHVAHZKIZVQTVAHZKIZMIZMIZWBABCDUAEFGUJAWJVCV
      DVEKIZVGVHKIZLIZKIZVKVGVLKIZVNVEKIZLIZKIZVQVNVHKIZVDVLKIZLIZKIZMIZMIWBAWD
      WNWIXCMAWCWMVCKACDFGUKULAWFWRWHXBMAWEWQVKKACDFGUMULAWGXAVQKACDFGUNULNNAWN
      VJXCWAMAWNVCWKKIZVCWLKIZLIVJAVCWKWLAVCABEUOOZAWKAVDVEACFUPZADGUQZPOAWLAVG
      VHACFUQZADGUPZPOURAXDVFXEVILAVFXDAVCVDVEXFAVDXGOZAVEXHOZQRAVIXEAVCVGVHXFA
      VGXIOZAVHXJOZQRNSAWRVPXBVTMAWRVKWOKIZVKWPKIZLIVPAVKWOWPAVKABEUPOZAWOAVGVL
      XIADGUOZPOAWPAVNVEACFUOZXHPOURAXOVMXPVOLAVMXOAVKVGVLXQXMAVLXROZQRAVOXPAVK
      VNVEXQAVNXSOZXLQRNSAXBVQWSKIZVQWTKIZLIVTAVQWSWTAVQABEUQOZAWSAVNVHXSXJPOAW
      TAVDVLXGXRPOURAYBVRYCVSLAVRYBAVQVNVHYDYAXNQRAVSYCAVQVDVLYDXKXTQRNSNNSSS
      $.
  $}

  ${
    $d A k t $.  $d B k t $.  $d ph t $.
    crosspaltd.1 $e |- ( ph -> A e. ( RR ^m ( 1 ... 3 ) ) ) $.
    crosspaltd.2 $e |- ( ph -> B e. ( RR ^m ( 1 ... 3 ) ) ) $.
    $( Antisymmetry of the cross product: swapping the two vectors negates the
       result.  (Contributed by Jiamin Zhao, 12-Aug-2026.) $)
    crosspaltd $p |- ( ph ->
      ( A crossp B ) = ( k e. ( 1 ... 3 ) |-> -u ( ( B crossp A ) ` k ) ) ) $=
      ( c1 c3 co cfv cneg cr wcel wa wceq c2 cmul cmin ad2antrr recnd vt cfz cv
      ccrossp cmpt cmap wfn crosspcld elmapfn syl negex eqid fnmpti caddc simpr
      a1i fveq2d crosspv1d rr3fv2cld rr3fv3cld remulcld negsubdi2d eqtrd negeqd
      mulcomd oveq12d 3eqtr4rd 3eqtrd crosspv2d rr3fv1cld remulcl syl2anc 1p1e2
      cc eqtr4d eqtrdi crosspv3d 1p2e3 ctp eqcomi oveq2i cz 1z fztp ax-mp eqtri
      w3o eleqtrdi eltpi mpjao3dan cvv weq fveq2 fvmptd3 eqfnfvd ) AUAGHUBIZBCU
      DIZDWPDUCZCBUDIZJZKZUEZAWQLWPUFIMWQWPUGABCEFUHWQLWPUIUJXBWPUGADWPXAXBWTUK
      XBULZUMUPAUAUCZWPMZNZXDWQJZXDWSJZKZXDXBJXFXDGOZXGXIOXDGGUNIZOZXDGPUNIZOZX
      FXJNZXGGWQJZPBJZHCJZQIZHBJZPCJZQIZRIZXIXOXDGWQXFXJUOZUQAXPYCOXEXJABCEFURS
      XOYAXTQIZXRXQQIZRIZKZYFYERIZXIYCAYHYIOXEXJAYEYFAYEAYAXTACFUSZABEUTZVATAYF
      AXRXQACFUTZABEUSZVATVBSXOXHYGXOXHGWSJZYGXOXDGWSYDUQAYNYGOXEXJACBFEURSVCVD
      XOXSYFYBYERAXSYFOXEXJAXQXRAXQYMTZAXRYLTZVESAYBYEOXEXJAXTYAAXTYKTZAYAYJTZV
      ESVFVGVHXFXLNZPWSJZKZPWQJZXIXGYSUUAXTGCJZQIZGBJZXRQIZRIZUUBYSUUAXRUUEQIZU
      UCXTQIZRIZKZUUIUUHRIZUUGYSYTUUJAYTUUJOXEXLACBFEVISVDAUUKUULOXEXLAUUHUUIAU
      UHAXRUUEYLABEVJZVATAUUCLMZXTLMZUUIVNMACFVJZYKUUNUUONUUIUUCXTVKTVLVBSYSUUI
      UUDUUHUUFRAUUIUUDOXEXLAUUCXTAUUCUUPTZYQVESAUUHUUFOXEXLAXRUUEYPAUUEUUMTZVE
      SVFVHAUUBUUGOXEXLABCEFVISVOYSXHYTYSXDPWSYSXDXKPXFXLUOVMVPZUQVDYSXDPWQUUSU
      QVGXFXNNZHWSJZKZHWQJZXIXGUUTUVBUUEYAQIZXQUUCQIZRIZUVCUUTUVBUUCXQQIZYAUUEQ
      IZRIZKZUVHUVGRIZUVFUUTUVAUVIAUVAUVIOXEXNACBFEVQSVDAUVJUVKOXEXNAUVGUVHAUVG
      AUUCXQUUPYMVATAYALMZUUELMZUVHVNMYJUUMUVLUVMNUVHYAUUEVKTVLVBSUUTUVHUVDUVGU
      VERAUVHUVDOXEXNAYAUUEYRUURVESAUVGUVEOXEXNAUUCXQUUQYOVESVFVHAUVCUVFOXEXNAB
      CEFVQSVOUUTXHUVAUUTXDHWSUUTXDXMHXFXNUOVRVPZUQVDUUTXDHWQUVNUQVGXFXDGXKXMVS
      ZMXJXLXNWGXFXDWPUVOAXEUOZWPGXMUBIZUVOHXMGUBXMHVRVTWAGWBMUVQUVOOWCGWDWEWFW
      HXDGXKXMWIUJWJXFDXDXAXIWPXBWKXCDUAWLWTXHWRXDWSWMVDUVPXIWKMXFXHUKUPWNVOWO
      $.
  $}

  ${
    $d X k t $.  $d Y k t $.  $d Z k t $.  $d ph t $.
    crossp3d.1 $e |- ( ph -> X e. ( RR ^m ( 1 ... 3 ) ) ) $.
    crossp3d.2 $e |- ( ph -> Y e. ( RR ^m ( 1 ... 3 ) ) ) $.
    crossp3d.3 $e |- ( ph -> Z e. ( RR ^m ( 1 ... 3 ) ) ) $.
    $( The vector triple product expansion (BAC-CAB rule): the cross product of
       ` X ` with ` ( Y crossp Z ) ` equals ` Y ` scaled by the dot product of
       ` X ` and ` Z ` , minus ` Z ` scaled by the dot product of ` X ` and
       ` Y ` .  The dot products are written out as explicit three-term sums of
       component products, matching the pointwise style of ~ df-crossp rather
       than introducing a separate dot product operator.  (Contributed by
       Jiamin Zhao, 12-Aug-2026.) $)
    crossp3d $p |- ( ph -> ( X crossp ( Y crossp Z ) ) = ( k e. ( 1 ... 3 ) |->
      ( ( ( ( ( ( X ` 1 ) x. ( Z ` 1 ) ) + ( ( X ` 2 ) x. ( Z ` 2 ) ) ) +
            ( ( X ` 3 ) x. ( Z ` 3 ) ) ) x. ( Y ` k ) ) -
        ( ( ( ( ( X ` 1 ) x. ( Y ` 1 ) ) + ( ( X ` 2 ) x. ( Y ` 2 ) ) ) +
            ( ( X ` 3 ) x. ( Y ` 3 ) ) ) x. ( Z ` k ) ) ) ) ) $=
      ( c1 co cfv cmul caddc cmin wcel ad2antrr oveq2d oveq12d cc mulcld vt cfz
      c3 ccrossp c2 cv cmpt cmap crosspcld elmapi syl ffnd wfn ovex eqid fnmpti
      cr wf a1i wceq simpr fveq2d crosspv1d crosspv3d crosspv2d eqtrd rr3fv2cld
      recnd rr3fv1cld remulcld subdid rr3fv3cld addcld adddird addsub4d mulassd
      oveq1d mulcomd pnpcand subcld subsub2d 3eqtr4d 3eqtrd eqtr2d eqcomd 1p1e2
      wa eqtrdi addcomd addassd subadd4d eqtr4d 1p2e3 pnpcan2d simplr ffvelcdmd
      3eqtr4rd ctp w3o eqcomi oveq2i cz 1z ax-mp eqtri eleqtrdi eltpi mpjao3dan
      fztp weq fveq2 readdcld adantr ffvelcdmda resubcld fvmptd3 eqfnfvd ) AUAI
      UCUBJZCDEUDJZUDJZBXRICKZIEKZLJZUECKZUEEKZLJZMJZUCCKZUCEKZLJZMJZBUFZDKZLJZ
      YAIDKZLJZYDUEDKZLJZMJZYHUCDKZLJZMJZYLEKZLJZNJZUGZAXRUQXTAXTUQXRUHJZOXRUQX
      TURACXSFADEGHUIZUIXTUQXRUJUKULUUFXRUMABXRUUEUUFYNUUDNUNUUFUOZUPUSAUAUFZXR
      OZWGZUUJXTKZYKUUJDKZLJZUUBUUJEKZLJZNJZUUJUUFKUULUUJIUTZUUMUURUTUUJIIMJZUT
      ZUUJIUEMJZUTZUULUUSWGZUUMIXTKZYKYOLJZUUBYBLJZNJZUURUVDUUJIXTUULUUSVAZVBUV
      DUVEYDYOYELJZYQYBLJZNJZLJZYHYTYBLJZYOYILJZNJZLJZNJZYDUVJLJZYDUVKLJZNJZYHU
      VNLJZYHUVOLJZNJZNJZUVHUVDUVEYDUCXSKZLJZYHUEXSKZLJZNJZUVRAUVEUWJUTUUKUUSAC
      XSFUUHVCPUVDUWGUVMUWIUVQNUVDUWFUVLYDLAUWFUVLUTZUUKUUSADEGHVDZPQUVDUWHUVPY
      HLAUWHUVPUTUUKUUSADEGHVEZPQRVFUVDUVMUWAUVQUWDNUVDYDUVJUVKAYDSOZUUKUUSAYDA
      CFVGZVHZPZAUVJSOZUUKUUSAUVJAYOYEADGVIZAEHVGZVJVHPAUVKSOZUUKUUSAUVKAYQYBAD
      GVGZAEHVIZVJVHPVKUVDYHUVNUVOAYHSOZUUKUUSAYHACFVLZVHZPZAUVNSOUUKUUSAUVNAYT
      YBADGVLZUXCVJVHPAUVOSOUUKUUSAUVOAYOYIUWSAEHVLZVJVHPVKRUVDUVHYGYOLJZYJYOLJ
      ZMJZYSYBLJZUUAYBLJZMJZNJZUWEUVDUVFUXLUVGUXONUVDYGYJYOAYGSOZUUKUUSAYCYFAYA
      YBAYAACFVIZVHZAYBUXCVHZTZAYDYEUWPAYEUWTVHZTZVMZPAYJSOZUUKUUSAYHYIUXFAYIUX
      IVHZTZPAYOSOZUUKUUSAYOUWSVHZPZVNUVDYSUUAYBAYSSOZUUKUUSAYPYRAYAYOUXSUYITZA
      YDYQUWPAYQUXBVHZTZVMZPAUUASOZUUKUUSAYHYTUXFAYTUXHVHZTZPAYBSOZUUKUUSUXTPZV
      NRUVDUXPUXJUXMNJZUXKUXNNJZMJYCYOLJZYFYOLJZMJZYPYBLJZYRYBLJZMJZNJZVUBMJZUW
      EUVDUXJUXKUXMUXNAUXJSOUUKUUSAYGYOUYDUYITPAUXKSOUUKUUSAYJYOUYGUYITPAUXMSOU
      UKUUSAYSYBUYOUXTTPAUXNSOUUKUUSAUUAYBUYRUXTTPVOUVDVUAVUIVUBMUVDUXJVUEUXMVU
      HNUVDYCYFYOAYCSOZUUKUUSUYAPAYFSOZUUKUUSUYCPUYJVNUVDYPYRYBAYPSOZUUKUUSUYLP
      AYRSOZUUKUUSUYNPUYTVNRVQUVDVUJYAYOYBLJZLJZVUDMJZVUHNJZVUBMJVUQVUPVUGMJZNJ
      ZVUBMJZUWEUVDVUIVURVUBMUVDVUEVUQVUHNUVDVUCVUPVUDMUVDVUCYAYBYOLJZLJVUPUVDY
      AYBYOAYASOZUUKUUSUXSPZUYTUYJVPUVDVVBVUOYALUVDYBYOUYTUYJVRQVFVQVQVQUVDVURV
      UTVUBMUVDVUHVUSVUQNUVDVUFVUPVUGMUVDYAYOYBVVDUYJUYTVPVQQVQUVDVUDVUGNJZVUBM
      JUWAUWCUWBNJZMJVVAUWEUVDVVEUWAVUBVVFMUVDVUDUVSVUGUVTNUVDVUDYDYEYOLJZLJUVS
      UVDYDYEYOUWQAYESOZUUKUUSUYBPZUYJVPUVDVVGUVJYDLUVDYEYOVVIUYJVRQVFUVDYDYQYB
      UWQAYQSOZUUKUUSUYMPUYTVPRUVDUXKUWCUXNUWBNUVDUXKYHYIYOLJZLJUWCUVDYHYIYOUXG
      AYISOUUKUUSUYFPZUYJVPUVDVVKUVOYHLUVDYIYOVVLUYJVRQVFUVDYHYTYBUXGAYTSOZUUKU
      USUYQPUYTVPRRUVDVUTVVEVUBMUVDVUPVUDVUGAVUPSOUUKUUSAYAVUOUXSAYOYBUYIUXTTTP
      AVUDSOUUKUUSAYFYOUYCUYITPAVUGSOUUKUUSAYRYBUYNUXTTPVSVQUVDUWAUWBUWCAUWASOU
      UKUUSAUVSUVTAYDUVJUWPAYOYEUYIUYBTZTAYDUVKUWPAYQYBUYMUXTTZTVTPAUWBSOUUKUUS
      AYHUVNUXFAYTYBUYQUXTTZTPAUWCSOUUKUUSAYHUVOUXFAYOYIUYIUYFTZTPWAWBWCWCWDWCU
      VDUVFUUOUVGUUQNUVDYOUUNYKLUVDIUUJDUVDUUJIUVIWEZVBQUVDYBUUPUUBLUVDIUUJEVVR
      VBQRWCUULUVAWGZUUMUEXTKZYHIXSKZLJZYAUWFLJZNJZUURVVSUUJUEXTVVSUUJUUTUEUULU
      VAVAWFWHZVBAVVTVWDUTUUKUVAACXSFUUHVEPVVSVWDYKYQLJZUUBYELJZNJZUURVVSVWDYHY
      QYILJZYTYELJZNJZLJZYAUVLLJZNJYHVWILJZYHVWJLJZNJZYAUVJLJZYAUVKLJZNJZNJZVWH
      VVSVWBVWLVWCVWMNVVSVWAVWKYHLAVWAVWKUTUUKUVAADEGHVCZPQVVSUWFUVLYALAUWKUUKU
      VAUWLPQRVVSVWLVWPVWMVWSNVVSYHVWIVWJAUXDUUKUVAUXFPZAVWISOUUKUVAAYQYIUYMUYF
      TZPAVWJSOUUKUVAAYTYEUYQUYBTZPVKVVSYAUVJUVKAVVCUUKUVAUXSPZAUWRUUKUVAVVNPAU
      XAUUKUVAVVOPVKRVVSVWTYCYQLJZYFYQLJZMJZVWNMJZYPYELJZYRYELJZMJZVWOMJZNJZYGY
      QLJZYJYQLJZMJZYSYELJZUUAYELJZMJZNJVWHVVSVWTVWRYDYQYELJZLJZMJZVWNMJZVWQVYB
      MJZVWOMJZNJZYAYBYQLJZLJZYDYEYQLJZLJZMJZVWNMJZVYFNJVXNVVSVYGVYBVWRMJZVWNMJ
      ZVYBVWQMJZVWOMJZNJZVWTVVSVYDVYOVYFVYQNVVSVYCVYNVWNMVVSVWRVYBAVWRSOUUKUVAA
      YAUVKUXSVVOTZPZAVYBSOUUKUVAAYDVYAUWPAYQYEUYMUYBTTPZWIVQVVSVYEVYPVWOMVVSVW
      QVYBAVWQSOUUKUVAAYAUVJUXSVVNTZPZWUAWIVQRVVSVYRVYBVWRVWNMJZMJZVYBVWQVWOMJZ
      MJZNJWUDWUFNJZVWTVVSVYOWUEVYQWUGNVVSVYBVWRVWNWUAVYTAVWNSOUUKUVAAYHVWIUXFV
      XCTZPZWJVVSVYBVWQVWOWUAWUCAVWOSOUUKUVAAYHVWJUXFVXDTZPZWJRVVSVYBWUDWUFWUAA
      WUDSOUUKUVAAVWRVWNVYSWUIVMPAWUFSOUUKUVAAVWQVWOWUBWUKVMPVSVVSVWTVWNVWRMJZV
      WOVWQMJZNJWUHVVSVWNVWOVWQVWRWUJWULWUCVYTWKVVSWUMWUDWUNWUFNVVSVWNVWRWUJVYT
      WIVVSVWOVWQWULWUCWIRWDWCWDVVSVYDVYMVYFNVVSVYCVYLVWNMVVSVWRVYIVYBVYKMVVSVY
      IVWRVVSVYHUVKYALVVSYBYQAUYSUUKUVAUXTPZAVVJUUKUVAUYMPZVRQWEVVSVYKVYBVVSVYJ
      VYAYDLVVSYEYQAVVHUUKUVAUYBPZWUPVRQWERVQVQVVSVYMVXIVYFVXMNVVSVYLVXHVWNMVVS
      VYIVXFVYKVXGMVVSVXFVYIVVSYAYBYQVXEWUOWUPVPWEVVSVXGVYKVVSYDYEYQAUWNUUKUVAU
      WPPZWUQWUPVPWERVQVVSVYEVXLVWOMVVSVWQVXJVYBVXKMVVSVXJVWQVVSYAYOYEVXEAUYHUU
      KUVAUYIPWUQVPWEVVSVXKVYBVVSYDYQYEWURWUPWUQVPWERVQRWCVVSVXIVXQVXMVXTNVVSVX
      HVXOVWNVXPMVVSVXOVXHVVSYCYFYQAVUKUUKUVAUYAPAVULUUKUVAUYCPWUPVNWEAVWNVXPUT
      UUKUVAAVXPYHYIYQLJZLJVWNAYHYIYQUXFUYFUYMVPAWUSVWIYHLAYIYQUYFUYMVRQWDPRVVS
      VXTVXMVVSVXRVXLVXSVWOMVVSYPYRYEAVUMUUKUVAUYLPAVUNUUKUVAUYNPWUQVNVVSYHYTYE
      VXBAVVMUUKUVAUYQPWUQVPRWERVVSVXQVWFVXTVWGNVVSVWFVXQVVSYGYJYQAUXQUUKUVAUYD
      PAUYEUUKUVAUYGPWUPVNWEVVSVWGVXTVVSYSUUAYEAUYKUUKUVAUYOPAUYPUUKUVAUYRPWUQV
      NWERWCWCVVSUUOVWFUUQVWGNVVSUUNYQYKLVVSUUJUEDVWEVBQVVSUUPYEUUBLVVSUUJUEEVW
      EVBQRWLWCUULUVCWGZUUMUVBXTKUCXTKZUURWUTUUJUVBXTUULUVCVAZVBWUTUVBUCXTUVBUC
      UTWUTWMUSVBWUTWVAYAUWHLJZYDVWALJZNJZYAUVPLJZYDVWKLJZNJZUURAWVAWVEUTUUKUVC
      ACXSFUUHVDPAWVEWVHUTUUKUVCAWVCWVFWVDWVGNAUWHUVPYALUWMQAVWAVWKYDLVXAQRPWUT
      YGUUNLJZYJUUNLJZMJZYSUUPLJZUUAUUPLJZMJZNJZYAUVNLJZYAUVOLJZNJZYDVWILJZYDVW
      JLJZNJZNJZUURWVHWUTWVOYGYTLJZYJYTLJZMJZYSYILJZUUAYILJZMJZNJZWWBWUTWVKWWEW
      VNWWHNWUTWVIWWCWVJWWDMWUTUUNYTYGLWUTUUJUCDWUTUUJUVBUCWVBWMWHZVBZQWUTUUNYT
      YJLWWKQRWUTWVLWWFWVMWWGMWUTUUPYIYSLWUTUUJUCEWWJVBZQWUTUUPYIUUALWWLQRRAWWI
      WWBUTUUKUVCAWWIYCYTLJZYFYTLJZMJZYHYIYTLJZLJZMJZYPYILJZYRYILJZMJZYHYTYILJZ
      LJZMJZNJYAYBYTLJZLJZWVTMJZWWQMJZWVQWVSMJZWWQMJZNJZWWBAWWEWWRWWHWXDNAWWCWW
      OWWDWWQMAYCYFYTUYAUYCUYQVNAYHYIYTUXFUYFUYQVPRAWWFWXAWWGWXCMAYPYRYIUYLUYNU
      YFVNAYHYTYIUXFUYQUYFVPRRAWWRWXHWXDWXJNAWWOWXGWWQMAWWMWXFWWNWVTMAYAYBYTUXS
      UXTUYQVPAWWNYDYEYTLJZLJWVTAYDYEYTUWPUYBUYQVPAWXLVWJYDLAYEYTUYBUYQVRQVFRVQ
      AWXAWXIWXCWWQMAWWSWVQWWTWVSMAYAYOYIUXSUYIUYFVPAYDYQYIUWPUYMUYFVPRAWXBWWPY
      HLAYTYIUYQUYFVRQRRAWVPWVTMJZWWQMJZWXJNJWXMWXINJWXKWWBAWXMWXIWWQAWVPWVTAYA
      UVNUXSVVPTZAYDVWJUWPVXDTZVMAWVQWVSAYAUVOUXSVVQTZAYDVWIUWPVXCTZVMAYHWWPUXF
      AYIYTUYFUYQTTWNAWXHWXNWXJNAWXGWXMWWQMAWXFWVPWVTMAWXEUVNYALAYBYTUXTUYQVRQV
      QVQVQAWVPWVQWVSWVTWXOWXQWXRWXPWKWBWCPVFWUTUUOWVKUUQWVNNWUTYGYJUUNAUXQUUKU
      VCUYDPAUYEUUKUVCUYGPWUTUUNWUTXRUQUUJDAXRUQDURZUUKUVCADUUGOWXSGDUQXRUJUKZP
      AUUKUVCWOZWPVHVNWUTYSUUAUUPAUYKUUKUVCUYOPAUYPUUKUVCUYRPWUTUUPWUTXRUQUUJEA
      XRUQEURZUUKUVCAEUUGOWYBHEUQXRUJUKZPWYAWPVHVNRAWVHWWBUTUUKUVCAWVFWVRWVGWWA
      NAYAUVNUVOUXSVVPVVQVKAYDVWIVWJUWPVXCVXDVKRPWQWCWCUULUUJIUUTUVBWRZOUUSUVAU
      VCWSUULUUJXRWYDAUUKVAZXRIUVBUBJZWYDUCUVBIUBUVBUCWMWTXAIXBOWYFWYDUTXCIXIXD
      XEXFUUJIUUTUVBXGUKXHUULBUUJUUEUURXRUUFUQUUIBUAXJZYNUUOUUDUUQNWYGYMUUNYKLY
      LUUJDXKQWYGUUCUUPUUBLYLUUJEXKQRWYEUULUUOUUQUULYKUUNAYKUQOUUKAYGYJAYCYFAYA
      YBUXRUXCVJAYDYEUWOUWTVJXLAYHYIUXEUXIVJXLXMAXRUQUUJDWXTXNVJUULUUBUUPAUUBUQ
      OUUKAYSUUAAYPYRAYAYOUXRUWSVJAYDYQUWOUXBVJXLAYHYTUXEUXHVJXLXMAXRUQUUJEWYCX
      NVJXOXPWLXQ $.
  $}

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Veronese map and linear dependence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c veronese $.

  $( Extend class notation to include the quadratic Veronese map on real
     3-vectors.  (Contributed by Jiamin Zhao, 14-Aug-2026.) $)
  cveronese $a class veronese $.

  ${
    $d k q $.

    $( Define the quadratic Veronese map on real 3-vectors, with coordinates
       ordered as ( x^2 , y^2 , z^2 , x y , y z , z x ).  (Contributed by
       Jiamin Zhao, 14-Aug-2026.) $)
    df-veronese $a |- veronese =
      ( q e. ( RR ^m ( 1 ... 3 ) ) |->
        ( k e. ( 1 ... 6 ) |->
          ( ( ( if ( k = 1 , ( ( q ` 1 ) ^ 2 ) , 0 ) +
                if ( k = 2 , ( ( q ` 2 ) ^ 2 ) , 0 ) ) +
              if ( k = 3 , ( ( q ` 3 ) ^ 2 ) , 0 ) ) +
            ( ( if ( k = 4 , ( ( q ` 1 ) x. ( q ` 2 ) ) , 0 ) +
                if ( k = 5 , ( ( q ` 2 ) x. ( q ` 3 ) ) , 0 ) ) +
              if ( k = 6 , ( ( q ` 3 ) x. ( q ` 1 ) ) , 0 ) ) ) ) ) $.
  $}

  ${
    $d x W $.  $d x I $.  $d x F $.  $d x K $.  $d x B $.  $d x R $.
    $d x .x. $.  $d x .0. $.  $d x Y $.  $d x L $.
    nellindf.b $e |- B = ( Base ` W ) $.
    nellindf.r $e |- R = ( Scalar ` W ) $.
    nellindf.t $e |- .x. = ( .s ` W ) $.
    nellindf.z $e |- .0. = ( 0g ` W ) $.
    nellindf.y $e |- Y = ( 0g ` R ) $.
    nellindf.l $e |- L = ( Base ` ( R freeLMod I ) ) $.
    $( A nonzero coefficient vector whose weighted combination of ` F ` sums to
       the zero vector implies that ` F ` is not linearly independent.
       (Contributed by Jiamin Zhao, 27-Aug-2026.) $)
    nellindf $p |- ( ( ( W e. LMod /\ I e. _V /\ F : I --> B ) /\
                       ( K e. L /\ K =/= ( I X. { Y } ) /\
                          ( W gsum ( K oF .x. F ) ) = .0. ) ) ->
                     -. F LIndF W ) $=
      ( vx wcel co wceq clmod cvv wf w3a csn cxp wne cof cgsu wa clindf cv wral
      wbr wi simpr2 neneqd simpr3 simpr1 oveq1 oveq2d eqeq1d eqeq1 imbi12d mpid
      rspcv syl mtod wb islindf4 adantr mtbird ) HUAREUBREADUCUDZFGRZFEIUEUFZUG
      ZHFDCUHZSZUISZJTZUDZUJZDHUKUNZHQULZDVQSZUISZJTZWDVOTZUOZQGUMZWBWJFVOTZWBF
      VOVMVNVPVTUPUQWBWJVTWKVMVNVPVTURWBVNWJVTWKUOZUOVMVNVPVTUSWIWLQFGWDFTZWGVT
      WHWKWMWFVSJWMWEVRHUIWDFDVQUTVAVBWDFVOVCVDVFVGVEVHVMWCWJVIWAQABCDEGHUBIJKL
      MNOPVJVKVL $.
  $}


  ${
    $d P k q $.
    veroneseval.1 $e |- ( ph -> P e. ( RR ^m ( 1 ... 3 ) ) ) $.
    $( Value of the Veronese map at a point, expressed as a maps-to function on
       the six coordinates.  (Contributed by Jiamin Zhao, 14-Aug-2026.) $)
    veronesevald $p |- ( ph -> ( veronese ` P ) =
      ( k e. ( 1 ... 6 ) |->
        ( ( ( if ( k = 1 , ( ( P ` 1 ) ^ 2 ) , 0 ) +
              if ( k = 2 , ( ( P ` 2 ) ^ 2 ) , 0 ) ) +
            if ( k = 3 , ( ( P ` 3 ) ^ 2 ) , 0 ) ) +
          ( ( if ( k = 4 , ( ( P ` 1 ) x. ( P ` 2 ) ) , 0 ) +
              if ( k = 5 , ( ( P ` 2 ) x. ( P ` 3 ) ) , 0 ) ) +
            if ( k = 6 , ( ( P ` 3 ) x. ( P ` 1 ) ) , 0 ) ) ) ) ) $=
      ( vq c1 c3 cfz co cfv c6 wceq c2 cexp cc0 cif caddc cmul ifeq1d oveq12d
      cr cmap wcel cveronese cv c4 cmpt fveq1 oveq1d mpteq2dv df-veronese mptex
      c5 ovex fvmpt3i syl ) ABUAFGHIUBIZUCBUDJCFKHIZCUEZFLZFBJZMNIZOPZUSMLZMBJZ
      MNIZOPZQIZUSGLZGBJZMNIZOPZQIZUSUFLZVAVERIZOPZUSUMLZVEVJRIZOPZQIZUSKLZVJVA
      RIZOPZQIZQIZUGZLDEBCURUTFEUEZJZMNIZOPZVDMWGJZMNIZOPZQIZVIGWGJZMNIZOPZQIZV
      NWHWKRIZOPZVQWKWORIZOPZQIZWAWOWHRIZOPZQIZQIZUGWFUQUDWGBLZCURXGWEXHWRVMXFW
      DQXHWNVHWQVLQXHWJVCWMVGQXHUTWIVBOXHWHVAMNFWGBUHZUISXHVDWLVFOXHWKVEMNMWGBU
      HZUISTXHVIWPVKOXHWOVJMNGWGBUHZUISTXHXCVTXEWCQXHWTVPXBVSQXHVNWSVOOXHWHVAWK
      VERXIXJTSXHVQXAVROXHWKVEWOVJRXJXKTSTXHWAXDWBOXHWOVJWHVARXKXITSTTUJCEUKCUR
      XGFKHUNULUOUP $.
  $}

  ${
    $d K k $.  $d Q k $.
    $( Every coordinate of the Veronese map of a real 3-vector is real.
       (Contributed by Jiamin Zhao, 19-Aug-2026.) $)
    veronesefvcl $p |- ( ( Q e. ( RR ^m ( 1 ... 3 ) ) /\ K e. ( 1 ... 6 ) )
      -> ( ( veronese ` Q ) ` K ) e. RR ) $=
      ( vk cr c1 c3 co wcel cfv wceq c2 cexp cc0 cif caddc resqcld adantr ifcld
      cmul readdcld cfz cmap c6 wa cveronese cv c4 c5 simpl veronesevald fveq1d
      cmpt rr3fv1cld 0red rr3fv2cld rr3fv3cld remulcld fmpttd ffvelcdmd eqeltrd
      simpr ) ADEFUAGUBGHZBEUCUAGZHZUDZBAUEIZIBCVCCUFZEJZEAIZKLGZMNZVGKJZKAIZKL
      GZMNZOGZVGFJZFAIZKLGZMNZOGZVGUGJZVIVMSGZMNZVGUHJZVMVRSGZMNZOGZVGUCJZVRVIS
      GZMNZOGZOGZULZIDVEBVFWNVEACVBVDUIZUJUKVEVCDBWNVECVCWMDVEVGVCHZUDZWAWLWQVP
      VTWQVKVOWQVHVJMDVEVJDHWPVEVIVEAWOUMZPQWQUNZRWQVLVNMDVEVNDHWPVEVMVEAWOUOZP
      QWSRTWQVQVSMDVEVSDHWPVEVRVEAWOUPZPQWSRTWQWHWKWQWDWGWQWBWCMDVEWCDHWPVEVIVM
      WRWTUQQWSRWQWEWFMDVEWFDHWPVEVMVRWTXAUQQWSRTWQWIWJMDVEWJDHWPVEVRVIXAWRUQQW
      SRTTURVBVDVAUSUT $.
  $}

  ${
    $d P k $.  $d x P $.  $d x ph $.
    veronesevrow.1 $e |- ( ph -> P e. ( RR ^m ( 1 ... 3 ) ) ) $.
    $( Lemma for ~ veronesevrowd .  Value of the first coordinate of the
       Veronese map at a point.  (Contributed by Jiamin Zhao, 15-Aug-2026.) $)
    veronesev1lem $p |- ( ph -> ( ( veronese ` P ) ` 1 ) =
                                ( ( P ` 1 ) ^ 2 ) ) $=
      ( c1 wceq c2 co cc0 cif caddc c3 c4 c5 c6 oveq1d wne mpbiri neneqd oveq2d
      neeq1 vx cv cfv cexp cmul cfz cveronese veronesevald iftrue 1ne2 iffalsed
      cr wa eqtrd 1ne3 1re 1lt4 ltneii 3eqtrd 1lt5 1lt6 adantl rr3fv1cld adantr
      wcel resqcld 0red readdcld addridd 00id a1i 1zzd cz 6nn nnzi cle wbr 1le1
      recnd 6re ltleii elfzd fvmptd ) AUADUAUBZDEZDBUCZFUDGZHIZWDFEZFBUCZFUDGZH
      IZJGZWDKEZKBUCZFUDGZHIZJGZWDLEZWFWJUEGZHIZWDMEZWJWOUEGZHIZJGZWDNEZWOWFUEG
      ZHIZJGZJGZWGDNUFGBUGUCULABUACUHAWEUMZXJWGHJGZHJGZHHJGZHJGZJGZXLWGWEXJXPEA
      WEXJXMHXDJGZXHJGZJGZXMXNXHJGZJGXPWEXJXLWQJGZXIJGZXMXIJGXSWEXJWGWLJGZWQJGZ
      XIJGYBWEWRYDXIJWEWMYCWQJWEWHWGWLJWEWGHUIOOOWEYDYAXIJWEYCXLWQJWEWLHWGJWEWI
      WKHWEWDFWEWDFPDFPUJWDDFTQRUKSOOUNWEYAXMXIJWEWQHXLJWEWNWPHWEWDKWEWDKPDKPUO
      WDDKTQRUKSOWEXIXRXMJWEXEXQXHJWEXAHXDJWEWSWTHWEWDLWEWDLPDLPDLUPUQURWDDLTQR
      UKOOSUSWEXRXTXMJWEXQXNXHJWEXDHHJWEXBXCHWEWDMWEWDMPDMPDMUPUTURWDDMTQRUKSOS
      WEXTXOXMJWEXHHXNJWEXFXGHWEWDNWEWDNPDNPDNUPVAURWDDNTQRUKSSUSVBXKXPWGXOJGZW
      GXNJGXLXKXPXLXOJGYEXKXMXLXOJXKXLXKXLXKWGHXKWFAWFULVEWEABCVCZVDVFZXKVGZVHV
      SVIOXKXLWGXOJXKWGXKWGYGVSVIZOUNXKXOXNWGJXKXNXKXNXKHHYHYHVHVSVISXKXNHWGJXN
      HEXKVJVKSUSYIUSADDNAVLZNVMVEANVNVOVKYJDDVPVQAVRVKDNVPVQADNUPVTVAWAVKWBAWF
      YFVFWC $.

    $( Lemma for ~ veronesevrowd .  Value of the second coordinate of the
       Veronese map at a point.  (Contributed by Jiamin Zhao, 16-Aug-2026.) $)
    veronesev2lem $p |- ( ph -> ( ( veronese ` P ) ` 2 ) =
                                ( ( P ` 2 ) ^ 2 ) ) $=
      ( c2 c1 wceq co cc0 cif caddc c3 c4 c5 c6 oveq2d oveq1d wne mpbiri neneqd
      neeq1 vx cv cfv cexp cmul cveronese cr veronesevald wa iftrue 1ne2 necomi
      cfz iffalsed eqtrd 2ne3 2re 2lt4 ltneii 3eqtrd 2lt5 2lt6 adantl 0red wcel
      rr3fv2cld adantr resqcld readdcld recnd addridd addlidd 00id a1i 1zzd 6nn
      cz nnzi 2z cle wbr 1le2 6re ltleii elfzd fvmptd ) AUADUAUBZEFZEBUCZDUDGZH
      IZWGDFZDBUCZDUDGZHIZJGZWGKFZKBUCZDUDGZHIZJGZWGLFZWIWMUEGZHIZWGMFZWMWRUEGZ
      HIZJGZWGNFZWRWIUEGZHIZJGZJGZWNENUMGBUFUCUGABUACUHAWLUIZXMHWNJGZHJGZHHJGZH
      JGZJGZWNHJGZWNWLXMXSFAWLXMXPHXGJGZXKJGZJGZXPXQXKJGZJGXSWLXMXOWTJGZXLJGZXP
      XLJGYCWLXMWKWNJGZWTJGZXLJGYFWLXAYHXLJWLWPYGWTJWLWOWNWKJWLWNHUJOPPWLYHYEXL
      JWLYGXOWTJWLWKHWNJWLWHWJHWLWGEWLWGEQDEQEDUKULWGDETRSUNPPPUOWLYEXPXLJWLWTH
      XOJWLWQWSHWLWGKWLWGKQDKQUPWGDKTRSUNOPWLXLYBXPJWLXHYAXKJWLXDHXGJWLXBXCHWLW
      GLWLWGLQDLQDLUQURUSWGDLTRSUNPPOUTWLYBYDXPJWLYAXQXKJWLXGHHJWLXEXFHWLWGMWLW
      GMQDMQDMUQVAUSWGDMTRSUNOPOWLYDXRXPJWLXKHXQJWLXIXJHWLWGNWLWGNQDNQDNUQVBUSW
      GDNTRSUNOOUTVCXNXSWNXRJGZWNXQJGXTXNXSXOXRJGYIXNXPXOXRJXNXOXNXOXNHWNXNVDZX
      NWMAWMUGVEWLABCVFZVGVHZVIVJVKPXNXOWNXRJXNWNXNWNYLVJZVLPUOXNXRXQWNJXNXQXNX
      QXNHHYJYJVIVJVKOXNXQHWNJXQHFXNVMVNOUTXNWNYMVKUTADENAVONVQVEANVPVRVNDVQVEA
      VSVNEDVTWAAWBVNDNVTWAADNUQWCVBWDVNWEAWMYKVHWF $.

    $( Lemma for ~ veronesevrowd .  Value of the third coordinate of the
       Veronese map at a point.  (Contributed by Jiamin Zhao, 17-Aug-2026.) $)
    veronesev3lem $p |- ( ph -> ( ( veronese ` P ) ` 3 ) =
                                ( ( P ` 3 ) ^ 2 ) ) $=
      ( c3 c1 wceq c2 co cc0 cif caddc c4 c5 c6 oveq2d oveq1d wne mpbiri neneqd
      neeq1 vx cv cfv cexp cmul cveronese cr veronesevald wa iftrue 1ne3 necomi
      cfz iffalsed eqtrd 2ne3 3re 3lt4 ltneii 3eqtrd 3lt5 3lt6 adantl 00id wcel
      a1i rr3fv3cld adantr resqcld recnd addlidd 0red readdcld addridd 1zzd 6nn
      cz nnzi 3z cle wbr 1le3 6re ltleii elfzd fvmptd ) AUADUAUBZEFZEBUCZGUDHZI
      JZWGGFZGBUCZGUDHZIJZKHZWGDFZDBUCZGUDHZIJZKHZWGLFZWIWMUEHZIJZWGMFZWMWRUEHZ
      IJZKHZWGNFZWRWIUEHZIJZKHZKHZWSENUMHBUFUCUGABUACUHAWQUIZXMIIKHZWSKHZXOIKHZ
      KHZWSIKHZWSWQXMXRFAWQXMXPIXGKHZXKKHZKHZXPXOXKKHZKHXRWQXMIWOKHZWSKHZXLKHZX
      PXLKHYBWQXMWPWSKHZXLKHYFWQXAYGXLKWQWTWSWPKWQWSIUJOPWQYGYEXLKWQWPYDWSKWQWK
      IWOKWQWHWJIWQWGEWQWGEQDEQEDUKULWGDETRSUNPPPUOWQYEXPXLKWQYDXOWSKWQWOIIKWQW
      LWNIWQWGGWQWGGQDGQGDUPULWGDGTRSUNOPPWQXLYAXPKWQXHXTXKKWQXDIXGKWQXBXCIWQWG
      LWQWGLQDLQDLUQURUSWGDLTRSUNPPOUTWQYAYCXPKWQXTXOXKKWQXGIIKWQXEXFIWQWGMWQWG
      MQDMQDMUQVAUSWGDMTRSUNOPOWQYCXQXPKWQXKIXOKWQXIXJIWQWGNWQWGNQDNQDNUQVBUSWG
      DNTRSUNOOUTVCXNXRWSXQKHZWSXOKHXSXNXRIWSKHZXQKHYHXNXPYIXQKXNXOIWSKXOIFXNVD
      VFZPPXNYIWSXQKXNWSXNWSXNWRAWRUGVEWQABCVGZVHVIVJZVKPUOXNXQXOWSKXNXOXNXOXNI
      IXNVLZYMVMVJVNOXNXOIWSKYJOUTXNWSYLVNUTADENAVONVQVEANVPVRVFDVQVEAVSVFEDVTW
      AAWBVFDNVTWAADNUQWCVBWDVFWEAWRYKVIWF $.

    $( Lemma for ~ veronesevrowd .  Value of the fourth coordinate of the
       Veronese map at a point.  (Contributed by Jiamin Zhao, 17-Aug-2026.) $)
    veronesev4lem $p |- ( ph -> ( ( veronese ` P ) ` 4 ) =
                                ( ( P ` 1 ) x. ( P ` 2 ) ) ) $=
      ( c4 c1 wceq c2 co cc0 cif caddc c3 c5 c6 wne mpbiri neneqd oveq1d oveq2d
      neeq1 vx cv cfv cexp cmul cfz cveronese cr veronesevald 1re 1lt4 iffalsed
      wa gtneii iftrue oveq12d 2re 2lt4 3re 3lt4 3eqtrd 4lt5 ltneii 4lt6 adantl
      4re 0red readdcld recnd addridd 00id a1i eqtrd rr3fv1cld adantr rr3fv2cld
      wcel remulcld addlidd 1zzd cz 6nn nnzi 4z cle wbr ltleii 6re elfzd fvmptd
      ) AUADUAUBZEFZEBUCZGUDHZIJZWKGFZGBUCZGUDHZIJZKHZWKLFZLBUCZGUDHZIJZKHZWKDF
      ZWMWQUEHZIJZWKMFZWQXBUEHZIJZKHZWKNFZXBWMUEHZIJZKHZKHZXGENUFHBUGUCUHABUACU
      IAXFUMZXQIIKHZIKHZXGIKHZIKHZKHZIXGKHZXGXFXQYCFAXFXQXTXGXKKHZXOKHZKHZXTYAX
      OKHZKHYCXFXQIWSKHZXDKHZYFKHXSXDKHZYFKHYGXFXEYJXPYFKXFWTYIXDKXFWOIWSKXFWLW
      NIXFWKEXFWKEODEOEDUJUKUNWKDETPQULRRXFXLYEXOKXFXHXGXKKXFXGIUORRUPXFYJYKYFK
      XFYIXSXDKXFWSIIKXFWPWRIXFWKGXFWKGODGOGDUQURUNWKDGTPQULSRRXFYKXTYFKXFXDIXS
      KXFXAXCIXFWKLXFWKLODLOLDUSUTUNWKDLTPQULSRVAXFYFYHXTKXFYEYAXOKXFXKIXGKXFXI
      XJIXFWKMXFWKMODMODMVFVBVCWKDMTPQULSRSXFYHYBXTKXFXOIYAKXFXMXNIXFWKNXFWKNOD
      NODNVFVDVCWKDNTPQULSSVAVEXRYCIYBKHZIYAKHYDXRYCXSYBKHYLXRXTXSYBKXRXSXRXSXR
      IIXRVGZYMVHVIVJRXRXSIYBKXSIFXRVKVLRVMXRYBYAIKXRYAXRYAXRXGIXRWMWQAWMUHVQXF
      ABCVNZVOAWQUHVQXFABCVPZVOVRZYMVHVIVJSXRYAXGIKXRXGXRXGYPVIZVJSVAXRXGYQVSVA
      ADENAVTNWAVQANWBWCVLDWAVQAWDVLEDWEWFAEDUJVFUKWGVLDNWEWFADNVFWHVDWGVLWIAWM
      WQYNYOVRWJ $.

    $( Lemma for ~ veronesevrowd .  Value of the fifth coordinate of the
       Veronese map at a point.  (Contributed by Jiamin Zhao, 17-Aug-2026.) $)
    veronesev5lem $p |- ( ph -> ( ( veronese ` P ) ` 5 ) =
                                ( ( P ` 2 ) x. ( P ` 3 ) ) ) $=
      ( c5 c1 wceq c2 co cc0 cif caddc c3 c4 c6 wne mpbiri neneqd oveq1d oveq2d
      neeq1 vx cv cfv cexp cmul cfz cveronese cr veronesevald 1re 1lt5 iffalsed
      gtneii iftrue oveq12d 2re 2lt5 3re 3lt5 3eqtrd 4re 4lt5 5re ltneii adantl
      wa 5lt6 0red readdcld recnd addridd 00id eqtrd rr3fv2cld adantr rr3fv3cld
      a1i wcel remulcld addlidd 1zzd cz 6nn 5nn cle wbr ltleii 6re elfzd fvmptd
      nnzi ) AUADUAUBZEFZEBUCZGUDHZIJZWLGFZGBUCZGUDHZIJZKHZWLLFZLBUCZGUDHZIJZKH
      ZWLMFZWNWRUEHZIJZWLDFZWRXCUEHZIJZKHZWLNFZXCWNUEHZIJZKHZKHZXKENUFHBUGUCUHA
      BUACUIAXJVFZXRIIKHZIKHZIXKKHZIKHZKHZYBXKXJXRYDFAXJXRYAXIXKKHZXPKHZKHZYAYB
      XPKHZKHYDXJXRIWTKHZXEKHZYFKHXTXEKHZYFKHYGXJXFYJXQYFKXJXAYIXEKXJWPIWTKXJWM
      WOIXJWLEXJWLEODEOEDUJUKUMWLDETPQULRRXJXMYEXPKXJXLXKXIKXJXKIUNSRUOXJYJYKYF
      KXJYIXTXEKXJWTIIKXJWQWSIXJWLGXJWLGODGOGDUPUQUMWLDGTPQULSRRXJYKYAYFKXJXEIX
      TKXJXBXDIXJWLLXJWLLODLOLDURUSUMWLDLTPQULSRUTXJYFYHYAKXJYEYBXPKXJXIIXKKXJX
      GXHIXJWLMXJWLMODMOMDVAVBUMWLDMTPQULRRSXJYHYCYAKXJXPIYBKXJXNXOIXJWLNXJWLNO
      DNODNVCVGVDWLDNTPQULSSUTVEXSYDIYCKHZIYBKHYBXSYDXTYCKHYLXSYAXTYCKXSXTXSXTX
      SIIXSVHZYMVIVJVKRXSXTIYCKXTIFXSVLVQRVMXSYCYBIKXSYBXSYBXSIXKYMXSWRXCAWRUHV
      RXJABCVNZVOAXCUHVRXJABCVPZVOVSZVIVJVKSXSYBXKIKXSXKXSXKYPVJVTZSUTYQUTADENA
      WANWBVRANWCWKVQDWBVRADWDWKVQEDWEWFAEDUJVCUKWGVQDNWEWFADNVCWHVGWGVQWIAWRXC
      YNYOVSWJ $.

    $( Lemma for ~ veronesevrowd .  Value of the sixth coordinate of the
       Veronese map at a point.  (Contributed by Jiamin Zhao, 17-Aug-2026.) $)
    veronesev6lem $p |- ( ph -> ( ( veronese ` P ) ` 6 ) =
                                ( ( P ` 3 ) x. ( P ` 1 ) ) ) $=
      ( c6 c1 wceq c2 co cc0 cif caddc c3 c4 c5 wne gtneii mpbiri oveq1d oveq2d
      neeq1 vx cv cfv cexp cmul cfz cveronese cr veronesevald 1re 1lt6 iffalsed
      neneqd iftrue oveq12d 2re 2lt6 3re 3lt6 3eqtrd 4re 4lt6 5re 5lt6 readdcld
      wa adantl 0red recnd addridd 00id eqtrd wcel rr3fv3cld rr3fv1cld remulcld
      a1i adantr addlidd 1zzd cz 6nn nnzi cle wbr 6re ltleii leidi elfzd fvmptd
      ) AUADUAUBZEFZEBUCZGUDHZIJZWKGFZGBUCZGUDHZIJZKHZWKLFZLBUCZGUDHZIJZKHZWKMF
      ZWMWQUEHZIJZWKNFZWQXBUEHZIJZKHZWKDFZXBWMUEHZIJZKHZKHZXNEDUFHBUGUCUHABUACU
      IAXMVFZXQIIKHZIKHZXSXNKHZKHZIXNKHZXNXMXQYBFAXMXQXTXLXNKHZKHZXTIXKKHZXNKHZ
      KHYBXMXQIWSKHZXDKHZYDKHXSXDKHZYDKHYEXMXEYIXPYDKXMWTYHXDKXMWOIWSKXMWLWNIXM
      WKEXMWKEODEOEDUJUKPWKDETQUMULRRXMXOXNXLKXMXNIUNSUOXMYIYJYDKXMYHXSXDKXMWSI
      IKXMWPWRIXMWKGXMWKGODGOGDUPUQPWKDGTQUMULSRRXMYJXTYDKXMXDIXSKXMXAXCIXMWKLX
      MWKLODLOLDURUSPWKDLTQUMULSRUTXMYDYGXTKXMXLYFXNKXMXHIXKKXMXFXGIXMWKMXMWKMO
      DMOMDVAVBPWKDMTQUMULRRSXMYGYAXTKXMYFXSXNKXMXKIIKXMXIXJIXMWKNXMWKNODNONDVC
      VDPWKDNTQUMULSRSUTVGXRYBIYAKHZIYCKHYCXRYBXSYAKHYKXRXTXSYAKXRXSXRXSXRIIXRV
      HZYLVEVIVJRXRXSIYAKXSIFXRVKVQZRVLXRYAYCIKXRXSIXNKYMRSXRYCXNIKXRXNXRXNXRXB
      WMAXBUHVMXMABCVNZVRAWMUHVMXMABCVOZVRVPVIVSZSUTYPUTADEDAVTDWAVMADWBWCVQZYQ
      EDWDWEAEDUJWFUKWGVQDDWDWEADWFWHVQWIAXBWMYNYOVPWJ $.

    $d x k $.
    $( The Veronese map at a point, expressed explicitly as a piecewise maps-to
       function on the six coordinates.  (Contributed by Jiamin Zhao,
       17-Aug-2026.) $)
    veronesevrowd $p |- ( ph -> ( veronese ` P ) = ( k e. ( 1 ... 6 ) |->
      if ( k = 1 , ( ( P ` 1 ) ^ 2 ) ,
      if ( k = 2 , ( ( P ` 2 ) ^ 2 ) ,
      if ( k = 3 , ( ( P ` 3 ) ^ 2 ) ,
      if ( k = 4 , ( ( P ` 1 ) x. ( P ` 2 ) ) ,
      if ( k = 5 , ( ( P ` 2 ) x. ( P ` 3 ) ) ,
      ( ( P ` 3 ) x. ( P ` 1 ) ) ) ) ) ) ) ) ) $=
      ( c1 c6 cfz co cfv wceq c2 c3 c4 c5 mpbiri wcel wo wne neeq1 neneqd vx cv
      cveronese cexp cmul cif cmpt wfn cc0 ovex eqid fnmpti veronesevald fneq1d
      caddc ifex a1i wa veronesev1lem ad2antrr simpr fveq2d cle wbr 1nn 6nn 1re
      6re 1lt6 ltleii elfz1b mpbir3an iftrue fvmpt3i ax-mp eqtrdi veronesev2lem
      cn 3eqtr4d 2nn 2re 2lt6 1ne2 necomi iffalsed jaodan veronesev3lem 3nn 3re
      eqtrd 3lt6 1ne3 2ne3 3eqtrd veronesev4lem 4nn 4re 4lt6 1lt4 veronesev5lem
      gtneii 2lt4 3lt4 5nn 5re 5lt6 1lt5 2lt5 3lt5 4lt5 veronesev6lem leidi cuz
      wb elnnuz elfzp1 5p1e6 oveq2i eleq2i eqeq2i orbi2i 3bitr3i 4p1e5 2eluzge1
      mpbi 3p1e4 2p1e3 1p1e2 elfz1eq orim1i sylbi syl mpjaodan eqfnfvd ) AUAEFG
      HZBUCIZCYOCUBZEJZEBIZKUDHZYQKJZKBIZKUDHZYQLJZLBIZKUDHZYQMJZYSUUBUEHZYQNJZ
      UUBUUEUEHZUUEYSUEHZUFZUFZUFZUFZUFZUGZAYPYOUHCYOYRYTUIUFUUAUUCUIUFUOHUUDUU
      FUIUFUOHZUUGUUHUIUFUUIUUJUIUFUOHYQFJZUUKUIUFUOHZUOHZUGZYOUHCYOUVAUVBUURUU
      TUOUJUVBUKULAYOYPUVBABCDUMUNOUUQYOUHACYOUUPUUQYRYTUUOYSKUDUJUUAUUCUUNUUBK
      UDUJUUDUUFUUMUUEKUDUJUUGUUHUULYSUUBUEUJUUIUUJUUKUUBUUEUEUJUUEYSUEUJUPUPUP
      UPUPZUUQUKZULUQAUAUBZYOPZURZUVEEJZUVEKJZQZUVELJZQZUVEMJZQZUVENJZQZUVEYPIZ
      UVEUUQIZJZUVEFJZUVGUVNUVSUVOUVGUVLUVSUVMUVGUVJUVSUVKUVGUVHUVSUVIUVGUVHURZ
      EYPIZYTUVQUVRAUWBYTJUVFUVHABDUSUTUWAUVEEYPUVGUVHVAZVBUWAUVREUUQIZYTUWAUVE
      EUUQUWCVBEYOPZUWDYTJUWEEVRPZFVRPZEFVCVDVEVFEFVGVHVIVJFEVKVLCEUUPYTYOUUQYR
      YTUUOVMUVDUVCVNVOVPVSUVGUVIURZKYPIZUUCUVQUVRAUWIUUCJUVFUVIABDVQUTUWHUVEKY
      PUVGUVIVAZVBUWHUVRKUUQIZUUCUWHUVEKUUQUWJVBKYOPZUWKUUCJUWLKVRPUWGKFVCVDVTV
      FKFWAVHWBVJFKVKVLCKUUPUUCYOUUQUUAUUPUUOUUCUUAYRYTUUOUUAYQEUUAYQERZKEREKWC
      WDYQKESOTWEUUAUUCUUNVMWJUVDUVCVNVOVPVSWFUVGUVKURZLYPIZUUFUVQUVRAUWOUUFJUV
      FUVKABDWGUTUWNUVELYPUVGUVKVAZVBUWNUVRLUUQIZUUFUWNUVELUUQUWPVBLYOPZUWQUUFJ
      UWRLVRPZUWGLFVCVDWHVFLFWIVHWKVJFLVKVLCLUUPUUFYOUUQUUDUUPUUOUUNUUFUUDYRYTU
      UOUUDYQEUUDUWMLERELWLWDYQLESOTWEUUDUUAUUCUUNUUDYQKUUDYQKRZLKRKLWMWDYQLKSO
      TWEUUDUUFUUMVMWNUVDUVCVNVOVPVSWFUVGUVMURZMYPIZUUHUVQUVRAUXBUUHJUVFUVMABDW
      OUTUXAUVEMYPUVGUVMVAZVBUXAUVRMUUQIZUUHUXAUVEMUUQUXCVBMYOPZUXDUUHJUXEMVRPZ
      UWGMFVCVDWPVFMFWQVHWRVJFMVKVLCMUUPUUHYOUUQUUGUUPUUNUUMUUHUUGUUPUUOUUNUUGY
      RYTUUOUUGYQEUUGUWMMEREMVGWSXAYQMESOTWEUUGUUAUUCUUNUUGYQKUUGUWTMKRKMWAXBXA
      YQMKSOTWEWJUUGUUDUUFUUMUUGYQLUUGYQLRZMLRLMWIXCXAYQMLSOTWEUUGUUHUULVMWNUVD
      UVCVNVOVPVSWFUVGUVOURZNYPIZUUJUVQUVRAUXIUUJJUVFUVOABDWTUTUXHUVENYPUVGUVOV
      AZVBUXHUVRNUUQIZUUJUXHUVENUUQUXJVBNYOPZUXKUUJJUXLNVRPZUWGNFVCVDXDVFNFXEVH
      XFVJFNVKVLCNUUPUUJYOUUQUUIUUPUUMUULUUJUUIUUPUUOUUNUUMUUIYRYTUUOUUIYQEUUIU
      WMNERENVGXGXAYQNESOTWEUUIUUAUUCUUNUUIYQKUUIUWTNKRKNWAXHXAYQNKSOTWEUUIUUDU
      UFUUMUUIYQLUUIUXGNLRLNWIXIXAYQNLSOTWEWNUUIUUGUUHUULUUIYQMUUIYQMRZNMRMNWQX
      JXAYQNMSOTWEUUIUUJUUKVMWNUVDUVCVNVOVPVSWFUVGUVTURZFYPIZUUKUVQUVRAUXPUUKJU
      VFUVTABDXKUTUXOUVEFYPUVGUVTVAZVBUXOUVRFUUQIZUUKUXOUVEFUUQUXQVBFYOPZUXRUUK
      JUXSUWGUWGFFVCVDVFVFFVHXLFFVKVLCFUUPUUKYOUUQUUSUUPUUMUULUUKUUSUUPUUOUUNUU
      MUUSYRYTUUOUUSYQEUUSUWMFEREFVGVIXAYQFESOTWEUUSUUAUUCUUNUUSYQKUUSUWTFKRKFW
      AWBXAYQFKSOTWEUUSUUDUUFUUMUUSYQLUUSUXGFLRLFWIWKXAYQFLSOTWEWNUUSUUGUUHUULU
      USYQMUUSUXNFMRMFWQWRXAYQFMSOTWEUUSUUIUUJUUKUUSYQNUUSYQNRFNRNFXEXFXAYQFNSO
      TWEWNUVDUVCVNVOVPVSUVGUVFUVPUVTQZAUVFVAUVFUVEENGHZPZUVTQZUXTUVEENEUOHZGHZ
      PZUYBUVEUYDJZQZUVFUYCNEXMIZPZUYFUYHXNUXMUYJXDNXOYEUVEENXPVOUYEYOUVEUYDFEG
      XQXRXSUYGUVTUYBUYDFUVEXQXTYAYBUYBUVPUVTUYBUVEEMGHZPZUVOQZUVPUVEEMEUOHZGHZ
      PZUYLUVEUYNJZQZUYBUYMMUYIPZUYPUYRXNUXFUYSWPMXOYEUVEEMXPVOUYOUYAUVEUYNNEGY
      CXRXSUYQUVOUYLUYNNUVEYCXTYAYBUYLUVNUVOUYLUVEELGHZPZUVMQZUVNUVEELEUOHZGHZP
      ZVUAUVEVUCJZQZUYLVUBLUYIPZVUEVUGXNUWSVUHWHLXOYEUVEELXPVOVUDUYKUVEVUCMEGYF
      XRXSVUFUVMVUAVUCMUVEYFXTYAYBVUAUVLUVMVUAUVEEKGHZPZUVKQZUVLUVEEKEUOHZGHZPZ
      VUJUVEVULJZQZVUAVUKKUYIPVUNVUPXNYDUVEEKXPVOVUMUYTUVEVULLEGYGXRXSVUOUVKVUJ
      VULLUVEYGXTYAYBVUJUVJUVKVUJUVEEEGHPZUVIQZUVJUVEEEEUOHZGHZPZVUQUVEVUSJZQZV
      UJVUREUYIPZVVAVVCXNUWFVVDVEEXOYEUVEEEXPVOVUTVUIUVEVUSKEGYHXRXSVVBUVIVUQVU
      SKUVEYHXTYAYBVUQUVHUVIUVEEYIYJYKYJYKYJYKYJYKYJYKYLYMYN $.
  $}

  ${
    $d A i j $.  $d V i j $.  $d A i k u v $.  $d V u v $.  $d ph u v $.
    $d j u v $.
    veronesemat.a $e |- V = ( i e. ( 1 ... 6 ) , j e. ( 1 ... 6 ) |->
                              ( ( veronese ` ( A ` i ) ) ` j ) ) $.
    veronesemat.f $e |- ( ph -> A : ( 1 ... 6 ) --> ( RR ^m ( 1 ... 3 ) ) ) $.
    $( The matrix whose ` i ` -th row is the Veronese image of ` A `` i `
       belongs to the base set of ` ( 1 ... 6 ) Mat RRfld ` .  (Contributed by
       Jiamin Zhao, 19-Aug-2026.) $)
    veronesematbasd $p |-
      ( ph -> V e. ( Base ` ( ( 1 ... 6 ) Mat RRfld ) ) ) $=
      ( vu vv cr c1 c6 cfz co crefld cfv wcel cv cveronese cvv cxp cmap cmat wf
      cbs cmpo weq 2fveq3 fveq1d fveq2 cbvmpov eqtri a1i wa c3 adantr ffvelcdmd
      wceq simprl simprr veronesefvcl syl2anc fmpod reex ovex sqxpexg ax-mp cfn
      elmap sylibr fzfi cfield refld elexi eqid rebase matbas2 mp2an eleqtrdi )
      AEJKLMNZVTUAZUBNZVTOUCNZUEPZAWAJEUDEWBQAHIVTVTIRZHRZBPZSPZPZJEEHIVTVTWIUF
      ZURAECDVTVTDRZCRZBPSPZPZUFWJFCDHIVTVTWNWIWKWHPCHUGWKWMWHWLWFSBUHUIWKWEWHU
      JUKULUMAWFVTQZWEVTQZUNZUNZWGJKUOMNUBNZQWPWIJQWRVTWSWFBAVTWSBUDWQGUPAWOWPU
      SUQAWOWPUTWGWEVAVBVCJWAEVDVTTQWATQKLMVEVTTVFVGVIVJVTVHQOTQWBWDURKLVKOVLVM
      VNWCOJVTTWCVOVPVQVRVS $.

    $( Currying the Veronese matrix gives the indexed family of Veronese images
       of the points ` A `` i ` .  (Contributed by Jiamin Zhao,
       19-Aug-2026.) $)
    veronesematrowd $p |- ( ph -> curry V =
      ( i e. ( 1 ... 6 ) |-> ( veronese ` ( A ` i ) ) ) ) $=
      ( vu vv c1 c6 co cv cfv cmpt wcel wceq cc0 cif caddc vk ccur cveronese cr
      cfz cmpo 2fveq3 fveq1d fveq2 cbvmpov eqtri wa c3 cmap wf adantr ffvelcdmd
      weq simprl simprr veronesefvcl syl2anc ralrimivva wne cle wbr 1nn 6nn 1re
      c0 cn 6re 1lt6 ltleii elfz1b mpbir3an ne0ii a1i mpocurryd c2 cexp c4 cmul
      wfn c5 ovex eqid fnmpti ffvelcdmda veronesevald fneq1d mpbiri dffn5 sylib
      eqcomd mpteq2dva eqtrd cbvmptv eqtrdi ) AEUBZHJKUELZHMZBNZUCNZOZCXACMZBNU
      CNZOAWTHXAIXAIMZXDNZOZOXEAHIXIEUDXAXAECDXAXADMZXGNZUFHIXAXAXIUFFCDHIXAXAX
      LXIXKXDNCHURXKXGXDXFXBUCBUGUHXKXHXDUIUJUKAXIUDPZHIXAXAAXBXAPZXHXAPZULZULZ
      XCUDJUMUELUNLZPXOXMXQXAXRXBBAXAXRBUOXPGUPAXNXOUSUQAXNXOUTXCXHVAVBVCXAVJVD
      AJXAJXAPJVKPKVKPJKVEVFVGVHJKVIVLVMVNKJVOVPVQVRVSAHXAXJXDAXNULZXDXJXSXDXAW
      DZXDXJQXSXTUAXAUAMZJQJXCNZVTWALRSYAVTQVTXCNZVTWALRSTLYAUMQUMXCNZVTWALRSTL
      ZYAWBQYBYCWCLRSYAWEQYCYDWCLRSTLYAKQYDYBWCLRSTLZTLZOZXAWDUAXAYGYHYEYFTWFYH
      WGWHXSXAXDYHXSXCUAAXAXRXBBGWIWJWKWLIXAXDWMWNWOWPWQHCXAXDXGXBXFUCBUGWRWS
      $.

    $( Currying the Veronese matrix gives the indexed family of Veronese
       images, with each image expressed explicitly by coordinates.
       (Contributed by Jiamin Zhao, 19-Aug-2026.) $)
    veronesematrowexpd $p |- ( ph -> curry V =
      ( i e. ( 1 ... 6 ) |-> ( k e. ( 1 ... 6 ) |->
        if ( k = 1 , ( ( ( A ` i ) ` 1 ) ^ 2 ) ,
        if ( k = 2 , ( ( ( A ` i ) ` 2 ) ^ 2 ) ,
        if ( k = 3 , ( ( ( A ` i ) ` 3 ) ^ 2 ) ,
        if ( k = 4 , ( ( ( A ` i ) ` 1 ) x. ( ( A ` i ) ` 2 ) ) ,
        if ( k = 5 , ( ( ( A ` i ) ` 2 ) x. ( ( A ` i ) ` 3 ) ) ,
        ( ( ( A ` i ) ` 3 ) x. ( ( A ` i ) ` 1 ) ) ) ) ) ) ) ) ) ) $=
      ( vu c1 co wceq cfv c2 cexp c3 cmul cif cmpt ifeq12d ccur c6 cfz cv c4 c5
      cveronese veronesematrowd 2fveq3 cbvmptv wcel wa ffvelcdmda veronesevrowd
      eqtrdi cr cmap mpteq2dva eqtrd weq fveq2 fveq1d oveq1d oveq12d mpteq2dv )
      AFUAZIJUBUCKZEVGEUDZJLZJIUDZBMZMZNOKZVHNLZNVKMZNOKZVHPLZPVKMZNOKZVHUELZVL
      VOQKZVHUFLZVOVRQKZVRVLQKZRZRZRZRZRZSZSZCVGEVGVIJCUDZBMZMZNOKZVNNWMMZNOKZV
      QPWMMZNOKZVTWNWPQKZWBWPWRQKZWRWNQKZRZRZRZRZRZSZSAVFIVGVKUGMZSZWKAVFCVGWMU
      GMZSXJABCDFGHUHCIVGXKXIWLVJUGBUIUJUOAIVGXIWJAVJVGUKULVKEAVGUPJPUCKUQKVJBH
      UMUNURUSICVGWJXHICUTZEVGWIXGXLVIVMWOWHXFXLVLWNNOXLJVKWMVJWLBVAZVBZVCXLVNV
      PWQWGXEXLVOWPNOXLNVKWMXMVBZVCXLVQVSWSWFXDXLVRWRNOXLPVKWMXMVBZVCXLVTWAWTWE
      XCXLVLWNVOWPQXNXOVDXLWBWCXAWDXBXLVOWPVRWRQXOXPVDXLVRWRVLWNQXPXNVDTTTTTVEU
      JUO $.
  $}

  ${
    $d A i j $.  $d V i j $.  $d ph i $.
    veroquad.a $e |- V = ( i e. ( 1 ... 6 ) , j e. ( 1 ... 6 ) |->
                              ( ( veronese ` ( A ` i ) ) ` j ) ) $.
    veroquad.f $e |- ( ph -> A : ( 1 ... 6 ) --> ( RR ^m ( 1 ... 3 ) ) ) $.
    veroquad.k $e |- ( ph -> K : ( 1 ... 6 ) --> RR ) $.
    $( Under ` ph `, for each ` i e. ( 1 ... 6 ) `, the point ` A `` i `
       satisfies the homogeneous quadratic equation with coefficients ` K ` in
       the canonical order ( x^2 , y^2 , z^2 , xy , yz , zx ). $)
    veroquad.q $e |- ( ( ph /\ i e. ( 1 ... 6 ) ) ->
      ( ( ( ( ( K ` 1 ) x. ( ( ( A ` i ) ` 1 ) ^ 2 ) ) +
            ( ( K ` 2 ) x. ( ( ( A ` i ) ` 2 ) ^ 2 ) ) ) +
          ( ( K ` 3 ) x. ( ( ( A ` i ) ` 3 ) ^ 2 ) ) ) +
        ( ( ( ( K ` 4 ) x. ( ( ( A ` i ) ` 1 ) x. ( ( A ` i ) ` 2 ) ) ) +
            ( ( K ` 5 ) x. ( ( ( A ` i ) ` 2 ) x. ( ( A ` i ) ` 3 ) ) ) ) +
          ( ( K ` 6 ) x. ( ( ( A ` i ) ` 3 ) x. ( ( A ` i ) ` 1 ) ) ) ) )
      = 0 ) $.

    ${
      $d A k $.  $d ph k $.  $d i k $.  $d A n $.  $d ph n $.  $d i j n $.

      ${
        $d K j u v w $.  $d A u v w $.  $d V u v w $.  $d ph u v w $.
        $d i u v w $.
        $( Lemma for ~ veroquadmodzerod .  Express the common homogeneous
           quadratic equation in ` RRfld gsum ` form using the Veronese matrix
           ` V ` .  (Contributed by Jiamin Zhao, 19-Aug-2026.) $)
        veroquadgsumlem $p |- ( ( ph /\ i e. ( 1 ... 6 ) ) ->
          ( RRfld gsum ( j e. ( 1 ... 6 ) |->
                        ( ( K ` j ) x. ( ( curry V ` i ) ` j ) ) ) ) = 0 ) $=
          ( c1 c6 co wcel cfv cmul c2 caddc c3 c4 vv cv cfz wa crefld ccur cmpt
          cgsu cexp c5 cc0 cseq cr cvv rebase replusg cfield refld elexi a1i cn
          cuz 6nn eleqtri wf ad2antrr simpr ffvelcdmd cveronese veronesematrowd
          nnuz fvexd fvmpt2d adantr fveq1d simplr veronesefvcl sylancom eqeltrd
          wceq remulcld fmpttd gsumval2 seqp1 ax-mp 5p1e6 fveq2i oveq2i 3eqtr3i
          cmap 5nn 4nn 4p1e5 3nn 3p1e4 2eluzge1 2p1e3 1nn 1p1e2 1z eqid oveq12d
          fveq2 cle wbr 1re 6re ltleii elfz1b mpbir3an ovexd fvmptd3 ffvelcdmda
          1lt6 veronesev1lem eqtrd oveq2d 2nn 2re 2lt6 veronesev2lem eqtrid 3re
          3lt6 veronesev3lem 4re 4lt6 veronesev4lem veronesev5lem veronesev6lem
          seq1i 5re 5lt6 leidi rr3fv1cld resqcld recnd rr3fv2cld addcld addassd
          rr3fv3cld oveq1d 3eqtrd weq cbvmptv 3eqtr3d ) ACUBZKLUCMZNZUDZUEUAUUH
          UAUBZEOZUUKUUGFUFZOZOZPMZUGZUHMZKEOZKUUGBOZOZQUIMZPMZQEOZQUUTOZQUIMZP
          MZRMZSEOZSUUTOZQUIMZPMZRMZTEOZUVAUVEPMZPMZUJEOZUVEUVJPMZPMZRMZLEOZUVJ
          UVAPMZPMZRMRMZUEDUUHDUBZEOZUWEUUNOZPMZUGZUHMUKUUJUURLRUUQKULZOZUVMUVP
          RMZUVSRMZUWCRMZUWDUUJUMRUUQUEKLUNUOUPUEUNNUUJUEUQURUSUTLKVBOZNUUJLVAU
          WOVCVKVDUTUUJUAUUHUUPUMUUJUUKUUHNZUDZUULUUOUWQUUHUMUUKEAUUHUMEVEZUUIU
          WPIVFUUJUWPVGVHUWQUUOUUKUUTVIOZOZUMUWQUUKUUNUWSUUJUUNUWSVTUWPACUUHUWS
          UUMUNABCDFGHVJUUJUUTVIVLVMZVNVOUUJUWPUUTUMKSUCMWJMZNUWTUMNUWQUUHUXBUU
          GBAUUHUXBBVEUUIUWPHVFAUUIUWPVPVHUUTUUKVQVRVSWAWBWCUUJUWKUJUWJOZLUUQOZ
          RMZUWNUJKRMZUWJOZUXCUXFUUQOZRMZUWKUXEUJUWONUXGUXIVTUJVAUWOWKVKVDRUUQK
          UJWDWEUXFLUWJWFWGUXHUXDUXCRUXFLUUQWFWGWHWIUUJUXCUWMUXDUWCRUUJUXCTUWJO
          ZUJUUQOZRMZUWMTKRMZUWJOZUXJUXMUUQOZRMZUXCUXLTUWONUXNUXPVTTVAUWOWLVKVD
          RUUQKTWDWEUXMUJUWJWMWGUXOUXKUXJRUXMUJUUQWMWGWHWIUUJUXJUWLUXKUVSRUUJUX
          JSUWJOZTUUQOZRMZUWLSKRMZUWJOZUXQUXTUUQOZRMZUXJUXSSUWONUYAUYCVTSVAUWOW
          NVKVDRUUQKSWDWEUXTTUWJWOWGUYBUXRUXQRUXTTUUQWOWGWHWIUUJUXQUVMUXRUVPRUU
          JUXQQUWJOZSUUQOZRMZUVMQKRMZUWJOZUYDUYGUUQOZRMZUXQUYFQUWONUYHUYJVTWPRU
          UQKQWDWEUYGSUWJWQWGUYIUYEUYDRUYGSUUQWQWGWHWIUUJUYDUVHUYEUVLRUUJUYDKUW
          JOZQUUQOZRMZUVHKKRMZUWJOZUYKUYNUUQOZRMZUYDUYMKUWONUYOUYQVTKVAUWOWRVKV
          DRUUQKKWDWEUYNQUWJWSWGUYPUYLUYKRUYNQUUQWSWGWHWIUUJUYKUVCUYLUVGRUUJUVC
          RUUQKWTUUJKUUQOUUSKUUNOZPMZUVCUUJUAKUUPUYSUUHUUQUNUUQXAZUUKKVTUULUUSU
          UOUYRPUUKKEXCUUKKUUNXCXBKUUHNZUUJVUAKVANLVANZKLXDXEWRVCKLXFXGXNXHLKXI
          XJUTZUUJUUSUYRPXKXLUUJUYRUVBUUSPUUJUYRKUWSOUVBUUJKUUNUWSUXAVOUUJUUTAU
          UHUXBUUGBHXMZXOXPXQXPYKUUJUYLUVDQUUNOZPMZUVGUUJUAQUUPVUFUUHUUQUNUYTUU
          KQVTUULUVDUUOVUEPUUKQEXCUUKQUUNXCXBQUUHNZUUJVUGQVANVUBQLXDXEXRVCQLXSX
          GXTXHLQXIXJUTZUUJUVDVUEPXKXLUUJVUEUVFUVDPUUJVUEQUWSOUVFUUJQUUNUWSUXAV
          OUUJUUTVUDYAXPXQXPXBYBUUJUYEUVISUUNOZPMZUVLUUJUASUUPVUJUUHUUQUNUYTUUK
          SVTUULUVIUUOVUIPUUKSEXCUUKSUUNXCXBSUUHNZUUJVUKSVANVUBSLXDXEWNVCSLYCXG
          YDXHLSXIXJUTZUUJUVIVUIPXKXLUUJVUIUVKUVIPUUJVUISUWSOUVKUUJSUUNUWSUXAVO
          UUJUUTVUDYEXPXQXPXBYBUUJUXRUVNTUUNOZPMZUVPUUJUATUUPVUNUUHUUQUNUYTUUKT
          VTUULUVNUUOVUMPUUKTEXCUUKTUUNXCXBTUUHNZUUJVUOTVANVUBTLXDXEWLVCTLYFXGY
          GXHLTXIXJUTZUUJUVNVUMPXKXLUUJVUMUVOUVNPUUJVUMTUWSOUVOUUJTUUNUWSUXAVOU
          UJUUTVUDYHXPXQXPXBYBUUJUXKUVQUJUUNOZPMZUVSUUJUAUJUUPVURUUHUUQUNUYTUUK
          UJVTUULUVQUUOVUQPUUKUJEXCUUKUJUUNXCXBUJUUHNZUUJVUSUJVANVUBUJLXDXEWKVC
          UJLYLXGYMXHLUJXIXJUTZUUJUVQVUQPXKXLUUJVUQUVRUVQPUUJVUQUJUWSOUVRUUJUJU
          UNUWSUXAVOUUJUUTVUDYIXPXQXPXBYBUUJUXDUWALUUNOZPMZUWCUUJUALUUPVVBUUHUU
          QUNUYTUUKLVTUULUWAUUOVVAPUUKLEXCUUKLUUNXCXBLUUHNZUUJVVCVUBVUBLLXDXEVC
          VCLXGYNLLXIXJUTZUUJUWAVVAPXKXLUUJVVAUWBUWAPUUJVVALUWSOUWBUUJLUUNUWSUX
          AVOUUJUUTVUDYJXPXQXPXBYBUUJUWNUVMUVTRMZUWCRMUWDUUJUWMVVEUWCRUUJUVMUVP
          UVSUUJUVHUVLUUJUVCUVGUUJUVCUUJUUSUVBUUJUUHUMKEAUWRUUIIVNZVUCVHUUJUVAU
          UJUUTVUDYOZYPWAYQUUJUVGUUJUVDUVFUUJUUHUMQEVVFVUHVHUUJUVEUUJUUTVUDYRZY
          PWAYQYSUUJUVLUUJUVIUVKUUJUUHUMSEVVFVULVHUUJUVJUUJUUTVUDUUAZYPWAYQYSZU
          UJUVPUUJUVNUVOUUJUUHUMTEVVFVUPVHUUJUVAUVEVVGVVHWAWAYQZUUJUVSUUJUVQUVR
          UUJUUHUMUJEVVFVUTVHUUJUVEUVJVVHVVIWAWAYQZYTUUBUUJUVMUVTUWCVVJUUJUVPUV
          SVVKVVLYSUUJUWCUUJUWAUWBUUJUUHUMLEVVFVVDVHUUJUVJUVAVVIVVGWAWAYQYTXPUU
          CUUJUUQUWIUEUHUUQUWIVTUUJUADUUHUUPUWHUADUUDUULUWFUUOUWGPUUKUWEEXCUUKU
          WEUUNXCXBUUEUTXQJUUF $.
      $}

      $d K i m n u v $.  $d A m u v $.  $d V m n u v $.  $d ph m u v $.
      $d i j m u v $.
      $( The columns of the Veronese matrix, weighted by the coefficients
         ` K ` , sum to the zero vector of ` RRfld freeLMod ( 1 ... 6 ) ` .
         (Contributed by Jiamin Zhao, 19-Aug-2026.) $)
      veroquadmodzerod $p |- ( ph ->
        ( ( RRfld freeLMod ( 1 ... 6 ) ) gsum
          ( K oF ( .s ` ( RRfld freeLMod ( 1 ... 6 ) ) ) curry tpos V ) ) =
        ( 0g ` ( RRfld freeLMod ( 1 ... 6 ) ) ) ) $=
        ( vn vu crefld co cfv cmul cvv cr wcel caddc vm vv c1 c6 cfz cfrlm ccur
        ctpos cvsca cof cgsu cc0 cmpt c0g cv cveronese csn ffnd cmap wf c0 cdif
        cxp cmpo weq 2fveq3 fveq1d fveq2 cbvmpov eqtri tposmpo a1i wa c3 adantr
        wceq simprr ffvelcdmd simprl veronesefvcl syl2anc fmpod wne ovex cn cle
        wbr 1nn 6nn 1re 1lt6 ltleii elfz1b mpbir3an ne0ii eldifsn mpbir2an reex
        6re curf syl3anc inidm eqidd wral ralrimivva simpr mpocurryvald mpteq2i
        csb csbfv eqtrdi cbvmptv offval cbs eqid rebase ffvelcdmda cfield refld
        cfn elexi frlmfibas mp2an feq3dd eqeltrrd remulr frlmvscafval mpteq2dva
        fzfi wfn fvexd fnconstg syl fvex 3eqtrd oveq2d c2 cexp oveq1d oveq12d
        fnmpti fvconst2 fvmptd3 adantlr crg cdr ccrg isfld mpbi simpli drngring
        ax-mp simpll simplr remulcld fmpttd fsuppmptdm frlmgsum veronesematrowd
        elmap sylibr fvmptd4 eqcomd c4 eqeq1d ralrimiva rspcdva veroquadgsumlem
        an32s c5 eqtrd fconstmpt re0g frlm0 eqtr3i ) AMUCUDUENZUFNZEFUHZUGZUVQU
        IOZUJNZUKNZUAUVPULUMZUVQUNOZAUWBUVQKUVPUAUVPKUOZEOZUWEUAUOZBOZUPOZOZPNZ
        UMZUMZUKNUAUVPMKUVPUWKUMZUKNZUMUWCAUWAUWMUVQUKAUWAKUVPUWFCUVPUWECUOZBOZ
        UPOZOZUMZUVTNZUMKUVPUVPUWFUQVCZUWTPUJNZUMUWMAKUVPUVPUWFUWTUVTUVPEUVSQQA
        UVPREIURAUVPRUVPUSNZUVSAUVPUVPVCRUVRUTUVPQVAUQVBSZRQSZUVPUXDUVSUTAUBLUV
        PUVPUBUOZLUOZBOZUPOZOZRUVRUVRUBLUVPUVPUXKVDVPALUBUVPUVPUXKFFCDUVPUVPDUO
        ZUWROZVDZLUBUVPUVPUXKVDGCDLUBUVPUVPUXMUXKUXLUXJOCLVEUXLUWRUXJUWPUXHUPBV
        FVGUXLUXGUXJVHVIVJVKZVLAUXGUVPSZUXHUVPSZVMZVMZUXIRUCVNUENUSNZSUXPUXKRSZ
        UXSUVPUXTUXHBAUVPUXTBUTZUXRHVOAUXPUXQVQVRAUXPUXQVSUXIUXGVTWAZWBUXEAUXEU
        VPQSZUVPVAWCZUCUDUEWDZUCUVPUCUVPSUCWESUDWESUCUDWFWGWHWIUCUDWJWSWKWLUDUC
        WMWNWOZUVPQVAWPWQVLUXFAWRVLUVPUVPRUVRQQWTXAZURUYDAUYFVLZUYIUVPXBZAUWEUV
        PSZVMZUWFXCUYLUWEUVSOZLUVPUWEUXJOZUMZUWTUYLUYMLUVPUBUWEUXKXIZUMUYOUYLUB
        LUWEUXKUVRRQUVPUVPUXOAUYALUVPXDUBUVPXDUYKAUYAUBLUVPUVPUYCXEVOUYEUYLUYGV
        LUYDUYLUYFVLZAUYKXFXGLUVPUYPUYNUBUWEUXJXJXHXKLCUVPUYNUWSLCVEUWEUXJUWRUX
        HUWPUPBVFVGXLXKZXMAKUVPUXAUXCUYLUWFUVQXNOZMUVTPUVPRQUWTUVQUVQXOZUYSXOXP
        UYQAUVPRUWEEIXQZUYLUYMUWTUYSUYRAUVPUYSUWEUVSAUVPUXDUYSUVSUXDUYSVPZAMQSU
        VPXTSZVUBMXRXSYAUCUDYIZMUVQUVPRQUYTXPYBYCZVLUYHYDXQYEUVTXOYFYGYHAKUVPUX
        CUWLUYLUAUVPUVPUWFUWJPUVPUXBUWTQQUYLUWFQSUXBUVPYJUYLUWEEYKUVPUWFQYLYMUW
        TUVPYJUYLCUVPUWSUWTUWEUWRYNUWTXOZUUAVLUYQUYQUYJUYLUWGUVPSZVMZVUGUWGUXBO
        UWFVPUYLVUGXFZUVPUWFUWGUWEEYNUUBYMAVUGUWGUWTOUWJVPUYKAVUGVMZCUWGUWSUWJU
        VPUWTQVUFCUAVEZUWEUWRUWIUWPUWGUPBVFZVGAVUGXFZVUJUWEUWIYKUUCUUDXMYHYOYPA
        UAKUXDMUWKUVPUVPQQUVQUWDUYTVUEUWDXOUYIUYIMUUESZAMUUFSZVUNVUOMUUGSZMXRSV
        UOVUPVMXSMUUHUUIUUJMUUKUULZVLUYLUVPRUWLUTUWLUXDSUYLUAUVPUWKRVUHUWFUWJUY
        LUWFRSVUGVUAVOVUHUWHUXTSUYKUWJRSVUHUVPUXTUWGBVUHAUYBAUYKVUGUUMZHYMVUIVR
        AUYKVUGUUNUWHUWEVTWAUUOUUPRUVPUWLWRUYFUUTUVAZAKUVPUWMUXDQUWLUWDUWMXOVUC
        AVUDVLVUSAUVQUNYKUUQUURAUAUVPUWOULVUJUWOMKUVPUWFUWEUWGFUGZOZOZPNZUMZUKN
        ULVUJUWNVVDMUKVUJKUVPUWKVVCAUYKVUGUWKVVCVPVUHUWJVVBUWFPVUHVVBUWJVUHUWEV
        VAUWIVUHCUWGUWRUWIUVPVUTQVULVUHAVUTCUVPUWRUMVPVURABCDFGHUUSYMVUIVUHUWHU
        PYKUVBVGUVCYPUVIYHYPABUAKEFFUXNUAKUVPUVPUWJVDGCDUAKUVPUVPUXMUWJUXLUWIOV
        UKUXLUWRUWIVULVGUXLUWEUWIVHVIVJHIVUJUCEOZUCUWQOZYQYRNZPNZYQEOZYQUWQOZYQ
        YRNZPNZTNZVNEOZVNUWQOZYQYRNZPNZTNZUVDEOZVVFVVJPNZPNZUVJEOZVVJVVOPNZPNZT
        NZUDEOZVVOVVFPNZPNZTNZTNZULVPZVVEUCUWHOZYQYRNZPNZVVIYQUWHOZYQYRNZPNZTNZ
        VVNVNUWHOZYQYRNZPNZTNZVVSVWLVWOPNZPNZVWBVWOVWSPNZPNZTNZVWFVWSVWLPNZPNZT
        NZTNZULVPCUVPUWGVUKVWJVXKULVUKVVRVXBVWIVXJTVUKVVMVWRVVQVXATVUKVVHVWNVVL
        VWQTVUKVVGVWMVVEPVUKVVFVWLYQYRVUKUCUWQUWHUWPUWGBVHZVGZYSYPVUKVVKVWPVVIP
        VUKVVJVWOYQYRVUKYQUWQUWHVXLVGZYSYPYTVUKVVPVWTVVNPVUKVVOVWSYQYRVUKVNUWQU
        WHVXLVGZYSYPYTVUKVWEVXGVWHVXITVUKVWAVXDVWDVXFTVUKVVTVXCVVSPVUKVVFVWLVVJ
        VWOPVXMVXNYTYPVUKVWCVXEVWBPVUKVVJVWOVVOVWSPVXNVXOYTYPYTVUKVWGVXHVWFPVUK
        VVOVWSVVFVWLPVXOVXMYTYPYTYTUVEAVWKCUVPXDVUGAVWKCUVPJUVFVOVUMUVGUVHUVKYH
        YOUVPULUQVCZUWCUWDUAUVPULUVLVUNUYDVXPUWDVPVUQUYFMUVQUVPQULUYTUVMUVNYCUV
        OXK $.
    $}

    ${
      $d K i u v $.  $d A u v $.  $d V u v $.  $d ph u v $.  $d j u v $.
      veroquadnolindf.n $e |- ( ph -> K =/= ( ( 1 ... 6 ) X. { 0 } ) ) $.
      $( A nonzero homogeneous quadratic equation satisfied by all six points
         gives a linear dependence among the columns of the Veronese matrix.
         (Contributed by Jiamin Zhao, 27-Aug-2026.) $)
      veroquadnolindfd $p |- ( ph -> -. curry tpos V LIndF ( RRfld freeLMod
        ( 1 ... 6 ) ) ) $=
        ( vu crefld c1 c6 co wcel cvv cfv cr cfz cfrlm clmod cbs ctpos ccur cc0
        vv wf csn cxp wne cvsca cof cgsu c0g wceq clindf wbr wn crg ccrg cfield
        cdr refld isfld mpbi simpli drngring ax-mp ovex eqid frlmlmod mp2an a1i
        wa cmap cfn elexi fzfi rebase frlmfibas c0 cdif cv cveronese weq 2fveq3
        fveq1d fveq2 cbvmpov eqtri tposmpo adantr simprr ffvelcdmd veronesefvcl
        cmpo c3 simprl syl2anc fmpod cle 1nn 6nn 1re 6re ltleii elfz1b mpbir3an
        cn 1lt6 ne0ii eldifsn mpbir2an reex syl3anc feq3dd elmap sylibr eleqtrd
        curf veroquadmodzerod csca frlmsca re0g nellindf syl33anc ) AMNOUAPZUBP
        ZUCQZYIRQZYIYJUDSZFUEZUFZUIEYMQEYIUGUJUKULYJEYOYJUMSZUNPUOPYJUPSZUQYOYJ
        URUSUTYKAMVAQZYLYKMVDQZYRYSMVBQZMVCQYSYTVPVEMVFVGVHMVIVJNOUAVKZMYJYIRYJ
        VLZVMVNVOYLAUUAVOAYITYIVQPZYMYOUUCYMUQZAMRQZYIVRQUUDMVCVEVSZNOVTMYJYITR
        UUBWAWBVNVOZAYIYIUKTYNUIYIRWCUJWDQZTRQZYIUUCYOUIAUHLYIYIUHWEZLWEZBSZWFS
        ZSZTYNYNUHLYIYIUUNWRUQALUHYIYIUUNFFCDYIYIDWEZCWEZBSWFSZSZWRLUHYIYIUUNWR
        GCDLUHYIYIUURUUNUUOUUMSCLWGUUOUUQUUMUUPUUKWFBWHWIUUOUUJUUMWJWKWLWMVOAUU
        JYIQZUUKYIQZVPZVPZUULTNWSUAPVQPZQUUSUUNTQUVBYIUVCUUKBAYIUVCBUIUVAHWNAUU
        SUUTWOWPAUUSUUTWTUULUUJWQXAXBUUHAUUHYLYIWCULUUANYINYIQNXKQOXKQNOXCUSXDX
        ENOXFXGXLXHONXIXJXMYIRWCXNXOVOUUIAXPVOYIYITYNRRYBXQXRAEUUCYMAYITEUIEUUC
        QITYIEXPUUAXSXTUUGYAKABCDEFGHIJYCYMMYPYOYIEYMYJUGYQYMVLZUUEYLMYJYDSUQUU
        FUUAMYJYIRRUUBYEVNYPVLYQVLYFUVDYGYH $.

      $( The Veronese matrix of six points satisfying a common nonzero
         homogeneous quadratic equation has determinant zero.  (Contributed by
         Jiamin Zhao, 27-Aug-2026.) $)
      veroquaddetzerod $p |- ( ph -> ( ( ( 1 ... 6 ) maDet RRfld ) ` V )
        = 0 ) $=
        ( vv vu co crefld cfv cr wcel eqid cvv c1 c6 cfz cmdat c0g cc0 wne wceq
        wn ccrg cmat cbs cdr cfield wa refld mpbi simpri veronesematbasd rebase
        isfld mdetcl sylancr cui ctpos mdettpos ccur cfrlm wbr veroquadnolindfd
        clindf wb cxp cmap wf cv cveronese cmpo weq 2fveq3 fveq1d fveq2 cbvmpov
        eqtri tposmpo a1i c3 adantr simprr ffvelcdmd veronesefvcl syl2anc fmpod
        simprl reex ovex sqxpexg ax-mp elmap sylibr fzfi elexi matbas2 eleqtrdi
        cfn mp2an matunitlindf mtbird matunit eqneltrrd simpli drngunit mpnanrd
        mtbid mp1i nne sylib re0g eqtr4di ) AFUAUBUCNZOUDNZPZOUEPZUFAYBYCUGZUIY
        BYCUHAYBQRZYDAOUJRZFXTOUKNZULPZRZYEOUMRZYFOUNRZYJYFUOUPOVAUQZURZABCDFGH
        USZYGYHYAOQFXTYASZYGSZYHSZUTVBVCAYBOVDPZRZYEYDUOZAFVEZYAPZYBYRAYFYIUUBY
        BUHYMYNYGYHYAOFXTYOYPYQVFVCAUUAYGVDPZRZUUBYRRZAUUDUUAVGOXTVHNVKVIZABCDE
        FGHIJKVJAYKUUAYHRZUUDUUFVLUPAUUAQXTXTVMZVNNZYHAUUHQUUAVOUUAUUIRALMXTXTL
        VPZMVPZBPZVQPZPZQUUAUUALMXTXTUUNVRUHAMLXTXTUUNFFCDXTXTDVPZCVPZBPVQPZPZV
        RMLXTXTUUNVRGCDMLXTXTUURUUNUUOUUMPCMVSUUOUUQUUMUUPUUKVQBVTWAUUOUUJUUMWB
        WCWDWEWFAUUJXTRZUUKXTRZUOZUOZUULQUAWGUCNVNNZRUUSUUNQRUVBXTUVCUUKBAXTUVC
        BVOUVAHWHAUUSUUTWIWJAUUSUUTWNUULUUJWKWLWMQUUHUUAWOXTTRUUHTRUAUBUCWPXTTW
        QWRWSWTXTXEROTRUUIYHUHUAUBXAOUNUPXBYGOQXTTYPUTXCXFXDZOXTUUAXGVCXHAYFUUG
        UUDUUEVLYMUVDYGYHYAOUUCUUAXTYRYPYOYQUUCSYRSZXIVCXNXJYJYSYTVLAYJYFYLXKQO
        YRYBYCUTUVEYCSXLXOXNXMYBYCXPXQXRXS $.
    $}
  $}

$( (End of Jiamin Zhao's mathbox.) $)
