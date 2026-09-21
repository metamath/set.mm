$[ set-main.mm $]
$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Mathbox for Saveliy Skresanov
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Ceva's theorem
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    sigar $e |- G = ( x e. CC , y e. CC |->
                          ( Im ` ( ( * ` x ) x. y ) ) ) $.
    $( Define the signed area by treating complex numbers as vectors with two
       components.  (Contributed by Saveliy Skresanov, 19-Sep-2017.) $)
    sigarval $p |- ( ( A e. CC /\ B e. CC )
          -> ( A G B ) = ( Im ` ( ( * ` A ) x. B ) ) ) $=
      ( cc cv ccj cfv cmul co cim wceq wa simpl fveq2d simpr oveq12d fvex
      ovmpoa ) ABCDGGAHZIJZBHZKLZMJCIJZDKLZMJEUBCNZUDDNZOZUEUGMUJUCUFUDDKUJUBCI
      UHUIPQUHUIRSQFUGMTUA $.

    $( Signed area takes value in reals.  (Contributed by Saveliy Skresanov,
       19-Sep-2017.) $)
    sigarim $p |- ( ( A e. CC /\ B e. CC ) -> ( A G B ) e. RR ) $=
      ( cc wcel wa co ccj cfv cmul cim cr sigarval simpl cjcld simpr mulcld
      imcld eqeltrd ) CGHZDGHZIZCDEJCKLZDMJZNLOABCDEFPUEUGUEUFDUECUCUDQRUCUDSTU
      AUB $.

    $( Signed area is anticommutative.  (Contributed by Saveliy Skresanov,
       19-Sep-2017.) $)
    sigarac $p |- ( ( A e. CC /\ B e. CC ) -> ( A G B ) = -u ( B G A ) ) $=
      ( cc wcel wa co ccj cfv cmul cim cneg sigarval cjcl adantl simpl cjmuld
      simpr cjcjd oveq1d cjcld mulcomd 3eqtrrd fveq2d mulcld 3eqtrd wceq ancoms
      imcjd negeqd eqtr4d ) CGHZDGHZIZCDEJZDKLZCMJZNLZOZDCEJZOUQURCKLZDMJZNLUTK
      LZNLVBABCDEFPUQVEVFNUQVFUSKLZVDMJDVDMJVEUQUSCUPUSGHUODQRZUOUPSZTUQVGDVDMU
      QDUOUPUAZUBUCUQDVDVJUQCVIUDUEUFUGUQUTUQUSCVHVIUHULUIUQVCVAUPUOVCVAUJABDCE
      FPUKUMUN $.

    $( Signed area is additive by the first argument.  (Contributed by Saveliy
       Skresanov, 19-Sep-2017.) $)
    sigaraf $p |- ( ( A e. CC /\ B e. CC /\ C e. CC )
          -> ( ( A + C ) G B ) = ( ( A G B ) + ( C G B ) ) ) $=
      ( cc wcel caddc co ccj cfv cmul cim wceq wa cjcld eqtrd sigarval 3adant2
      w3a cjadd oveq1d simp1 simp3 adddird fveq2d mulcld imaddd syl2anc 3adant3
      simp2 addcld 3simpc ancomd syl oveq12d 3eqtr4d ) CHIZDHIZEHIZUBZCEJKZLMZD
      NKZOMZCLMZDNKZOMZELMZDNKZOMZJKZVDDFKZCDFKZEDFKZJKVCVGVIVLJKZOMVNVCVFVROVC
      VFVHVKJKZDNKZVRUTVBVFVTPVAUTVBQVEVSDNCEUCUDUAVCVHVKDVCCUTVAVBUEZRZVCEUTVA
      VBUFZRZUTVAVBUMZUGSUHVCVIVLVCVHDWBWEUIVCVKDWDWEUIUJSVCVDHIVAVOVGPVCCEWAWC
      UNWEABVDDFGTUKVCVPVJVQVMJUTVAVPVJPVBABCDFGTULVCVBVAQVQVMPVCVAVBUTVAVBUOUP
      ABEDFGTUQURUS $.

    $( Signed area is additive (with respect to subtraction) by the first
       argument.  (Contributed by Saveliy Skresanov, 19-Sep-2017.) $)
    sigarmf $p |- ( ( A e. CC /\ B e. CC /\ C e. CC )
          -> ( ( A - C ) G B ) = ( ( A G B ) - ( C G B ) ) ) $=
      ( cc wcel cmin co ccj cfv cmul cim wceq wa cjcld eqtrd sigarval w3a cjsub
      oveq1d 3adant2 subdird fveq2d mulcld imsubd subcld syl2anc 3adant3 3simpc
      simp1 simp3 simp2 ancomd syl oveq12d 3eqtr4d ) CHIZDHIZEHIZUAZCEJKZLMZDNK
      ZOMZCLMZDNKZOMZELMZDNKZOMZJKZVDDFKZCDFKZEDFKZJKVCVGVIVLJKZOMVNVCVFVROVCVF
      VHVKJKZDNKZVRUTVBVFVTPVAUTVBQVEVSDNCEUBUCUDVCVHVKDVCCUTVAVBUMZRZVCEUTVAVB
      UNZRZUTVAVBUOZUESUFVCVIVLVCVHDWBWEUGVCVKDWDWEUGUHSVCVDHIVAVOVGPVCCEWAWCUI
      WEABVDDFGTUJVCVPVJVQVMJUTVAVPVJPVBABCDFGTUKVCVBVAQVQVMPVCVAVBUTVAVBULUPAB
      EDFGTUQURUS $.

    $( Signed area is additive by the second argument.  (Contributed by Saveliy
       Skresanov, 19-Sep-2017.) $)
    sigaras $p |- ( ( A e. CC /\ B e. CC /\ C e. CC )
          -> ( A G ( B + C ) ) = ( ( A G B ) + ( A G C ) ) ) $=
      ( cc wcel w3a caddc co cneg wceq sigarac syl2anc wa cr ancomd sigarim syl
      simp1 simp2 simp3 addcld sigaraf negeqd 3com12 3simpa recnd 3simpb negdid
      eqtrd eqcomd oveq12d 3eqtrd ) CHIZDHIZEHIZJZCDEKLZFLZVACFLZMZDCFLZMZECFLZ
      MZKLZCDFLZCEFLZKLUTUQVAHIVBVDNUQURUSUBZUTDEUQURUSUCZUQURUSUDZUEABCVAFGOPU
      TVDVEVGKLZMZVIURUQUSVDVPNURUQUSJVCVOABDCEFGUFUGUHUTVEVGUTVEUTURUQQVERIUTU
      QURUQURUSUISABDCFGTUAUJUTVGUTUSUQQVGRIUTUQUSUQURUSUKSABECFGTUAUJULUMUTVFV
      JVHVKKUTVJVFUTUQURVJVFNVLVMABCDFGOPUNUTVKVHUTUQUSVKVHNVLVNABCEFGOPUNUOUP
      $.

    $( Signed area is additive (with respect to subtraction) by the second
       argument.  (Contributed by Saveliy Skresanov, 19-Sep-2017.) $)
    sigarms $p |- ( ( A e. CC /\ B e. CC /\ C e. CC )
          -> ( A G ( B - C ) ) = ( ( A G B ) - ( A G C ) ) ) $=
      ( cc wcel w3a cmin co cneg wceq sigarac syl2anc wa cr ancomd sigarim syl
      simp1 simp2 simp3 subcld negeqd 3com12 3simpa recnd 3simpb caddc negsubdi
      sigarmf simpl negcld simpr subnegd eqtr4d eqtrd eqcomd oveq12d 3eqtrd ) C
      HIZDHIZEHIZJZCDEKLZFLZVGCFLZMZDCFLZMZECFLZMZKLZCDFLZCEFLZKLVFVCVGHIVHVJNV
      CVDVEUBZVFDEVCVDVEUCZVCVDVEUDZUEABCVGFGOPVFVJVKVMKLZMZVOVDVCVEVJWBNVDVCVE
      JVIWAABDCEFGUMUFUGVFVKHIZVMHIZWBVONVFVKVFVDVCQVKRIVFVCVDVCVDVEUHSABDCFGTU
      AUIVFVMVFVEVCQVMRIVFVCVEVCVDVEUJSABECFGTUAUIWCWDQZWBVLVMUKLVOVKVMULWEVLVM
      WEVKWCWDUNUOWCWDUPUQURPUSVFVLVPVNVQKVFVPVLVFVCVDVPVLNVRVSABCDFGOPUTVFVQVN
      VFVCVEVQVNNVRVTABCEFGOPUTVAVB $.

    $( Signed area is linear by the second argument.  (Contributed by Saveliy
       Skresanov, 19-Sep-2017.) $)
    sigarls $p |- ( ( A e. CC /\ B e. CC /\ C e. RR )
          -> ( A G ( B x. C ) ) = ( ( A G B ) x. C ) ) $=
      ( cc wcel cfv cmul cim recnd 3adant1 fveq2d mulcld mulcomd 3eqtr4d wceq
      co cr w3a ccj simp1 cjcld simp2 wa simpr mulassd simp3 immul2d syl eqtr3d
      imcl simpl sigarval syl2anc 3adant3 oveq1d ) CHIZDHIZEUAIZUBZCUCJZDEKTZKT
      ZLJZVDDKTZLJZEKTZCVEFTZCDFTZEKTVCVHEKTZLJZVGVJVCVMVFLVCVDDEVCCUTVAVBUDZUE
      ZUTVAVBUFZVAVBEHIUTVAVBUGZEVAVBUHMZNZUIOVCEVHKTZLJEVIKTVNVJVCEVHUTVAVBUJV
      CVDDVPVQPZUKVCVMWALVCVHEWBVTQOVCVIEVCVHHIZVIHIWBWCVIVHUNMULVTQRUMVCUTVEHI
      ZVKVGSVOVAVBWDUTVRDEVAVBUOVSPNABCVEFGUPUQVCVLVIEKUTVAVLVISVBABCDFGUPURUSR
      $.

    $( Signed area of a flat parallelogram is zero.  (Contributed by Saveliy
       Skresanov, 20-Sep-2017.) $)
    sigarid $p |- ( A e. CC -> ( A G A ) = 0 ) $=
      ( cc wcel co ccj cfv cmul cim cc0 wceq sigarval anidms cr cjcl id mulcomd
      cjmulrcl eqeltrd reim0d eqtrd ) CFGZCCDHZCIJZCKHZLJZMUEUFUINABCCDEOPUEUHU
      EUHCUGKHQUEUGCCRUESTCUAUBUCUD $.

    $( Expand the signed area formula by linearity.  (Contributed by Saveliy
       Skresanov, 20-Sep-2017.) $)
    sigarexp $p |- ( ( A e. CC /\ B e. CC /\ C e. CC )
  -> ( ( A - C ) G ( B - C ) ) = ( ( ( A G B ) - ( A G C ) ) - ( C G B ) ) ) $=
      ( cc wcel w3a cmin co wceq simp2 simp3 subcld sigarms cc0 oveq2d 3eqtrd
      sigarmf syld3an2 oveq1d syld3an1 sigarid wa sigarim recnd syl2anc subid1d
      syl ) CHIZDHIZEHIZJZCEKLDEKLZFLZCUPFLZEUPFLZKLZCDFLCEFLKLZUSKLVAEDFLZKLUL
      UPHIUMUNUQUTMUODEULUMUNNZULUMUNOZPABCUPEFGUAUBUOURVAUSKABCDEFGQUCUOUSVBVA
      KUOUSVBEEFLZKLZVBRKLVBUNUMULUNUSVFMVDABEDEFGQUDUOVERVBKUOUNVERMVDABEFGUEU
      KSUOVBUOUNUMVBHIVDVCUNUMUFVBABEDFGUGUHUIUJTST $.

    $( Signed area ` ( A - C ) G ( B - C ) ` acts as a double area of a
       triangle ` A B C ` .  Here we prove that cyclically permuting the
       vertices doesn't change the area.  (Contributed by Saveliy Skresanov,
       20-Sep-2017.) $)
    sigarperm $p |- ( ( A e. CC /\ B e. CC /\ C e. CC )
          -> ( ( A - C ) G ( B - C ) ) = ( ( B - A ) G ( C - A ) ) ) $=
      ( cc wcel co cmin caddc cneg wa sigarim recnd syl2anc negsubd wceq cr w3a
      simp2 simp3 sigarac eqcomd oveq2d eqtr3d oveq1d sigarexp addcomd 3eqtr2rd
      simp1 3comr sub32d 3eqtrd 3eqtr4rd ) CHIZDHIZEHIZUAZDEFJZDCFJZKJZCEFJZKJZ
      VACDFJZLJZVDKJZDCKJECKJFJZCEKJDEKJFJZUTVCVGVDKUTVAVBMZLJVCVGUTVAVBUTURUSV
      AHIUQURUSUBZUQURUSUCZURUSNVAABDEFGOPQZUTURUQVBHIVLUQURUSULZURUQNVBABDCFGO
      PQRUTVKVFVALUTVFVKUTUQURVFVKSVOVLABCDFGUDQUEUFUGUHURUSUQVIVESABDECFGUIUMU
      TVJVFVDKJEDFJZKJVFVPKJZVDKJVHABCDEFGUIUTVFVDVPUTVFUTUQURVFTIVOVLABCDFGOQP
      ZUTVDUTUQUSVDTIVOVMABCEFGOQPUTVPUTUSURVPTIVMVLABEDFGOQPZUNUTVQVGVDKUTVGVF
      VALJVFVPMZLJVQUTVAVFVNVRUJUTVTVAVFLUTVAVTUTURUSVAVTSVLVMABDEFGUDQUEUFUTVF
      VPVRVSRUKUHUOUP $.

    sigardiv.a $e |- ( ph -> ( A e. CC /\ B e. CC /\ C e. CC ) ) $.
    sigardiv.b $e |- ( ph -> -. C = A ) $.
    sigardiv.c $e |- ( ph -> ( ( B - A ) G ( C - A ) ) = 0 ) $.
    $( If signed area between vectors ` B - A ` and ` C - A ` is zero, then
       those vectors lie on the same line.  (Contributed by Saveliy Skresanov,
       22-Sep-2017.) $)
    sigardiv $p |- ( ph -> ( ( B - A ) / ( C - A ) ) e. RR ) $=
      ( co cdiv ccj cfv cr cc wcel cmul eqeltrrd simp2d simp1d subcld divcan5rd
      simp3d neqned subne0d cjdivd cjcld cjne0d mulcld cim cc0 sigarval syl2anc
      cmin wceq eqtr3d reim0bd mulcomd cjmulrcld mulne0d redivcld eqeltrd cjred
      divcld cjcjd ) AEDUPLZFDUPLZMLZNOZVJPAVKNOVKVJAVKAVKVHNOZVINOZMLZPAVHVIAE
      DADQRZEQRZFQRZIUAAVOVPVQIUBZUCZAFDAVOVPVQIUEZVRUCZAFDVTVRAFDJUFUGZUHAVLVI
      SLZVMVISLZMLVNPAVLVMVIAVHVSUIZAVIWAUIZWAAVIWAWBUJZWBUDAWCWDAWCAVLVIWEWAUK
      AVHVIGLZWCULOZUMAVHQRVIQRWHWIUQVSWABCVHVIGHUNUOKURUSAVIVMSLWDPAVIVMWAWFUT
      AVIWAVATAVMVIWFWAWGWBVBVCTVDZVEAVJAVHVIVSWAWBVFVGURWJT $.
  $}

  ${
    $d x y A $.  $d x y B $.
    sigarimcd.sigar $e |- G = ( x e. CC , y e. CC |->
                          ( Im ` ( ( * ` x ) x. y ) ) ) $.
    sigarimcd.a $e |- ( ph -> ( A e. CC /\ B e. CC ) ) $.
    $( Signed area takes value in complex numbers.  Deduction version.
       (Contributed by Saveliy Skresanov, 23-Sep-2017.) $)
    sigarimcd $p |- ( ph -> ( A G B ) e. CC ) $=
      ( cc wcel wa co sigarim recnd syl ) ADIJEIJKZDEFLZIJHPQBCDEFGMNO $.

    sigariz.a $e |- ( ph -> ( A G B ) = 0 ) $.
    $( If signed area is zero, the signed area with swapped arguments is also
       zero.  Deduction version.  (Contributed by Saveliy Skresanov,
       23-Sep-2017.) $)
    sigariz $p |- ( ph -> ( B G A ) = 0 ) $=
      ( cc0 cneg co cc wcel wa wceq sigarac syl eqtr3d negeqd sigarimcd negnegd
      neg0 a1i ancomd 3eqtr3rd ) AJKZEDFLZKZKJUHAJUIADEFLZJUIIADMNZEMNZOUJUIPHB
      CDEFGQRSTUGJPAUCUDAUHABCEDFGAUKULHUEUAUBUF $.
  $}

  ${
    $d t x y A $.  $d t x y B $.  $d t x y C $.  $d t G $.  $d t ph $.
    sigarcol.sigar $e |- G
        = ( x e. CC , y e. CC |-> ( Im ` ( ( * ` x ) x. y ) ) ) $.
    sigarcol.a $e |- ( ph -> ( A e. CC /\ B e. CC /\ C e. CC ) ) $.
    sigarcol.b $e |- ( ph -> -. A = B ) $.
    $( Given three points ` A ` , ` B ` and ` C ` such that ` -. A = B ` , the
       point ` C ` lies on the line going through ` A ` and ` B ` iff the
       corresponding signed area is zero.  That justifies the usage of signed
       area as a collinearity indicator.  (Contributed by Saveliy Skresanov,
       22-Sep-2017.) $)
    sigarcol $p |- ( ph -> ( ( ( A - C ) G ( B - C ) ) = 0
          <-> E. t e. RR C = ( B + ( t x. ( A - B ) ) ) ) ) $=
      ( cmin co cc0 wceq cmul caddc wcel cc adantr cv cr wrex w3a simp2d simp3d
      wa cdiv simp1d 3jca wn sigarperm syl eqeq1d biimpa sigardiv subcld neqned
      eqtrd subne0d divcan1d oveq2d pncan3d eqtr2d rspceeqv syl2anc ex 3ad2ant1
      oveq1 simp2 recnd mulcld mvrladdd mulcomd sigarac sigarls syl3anc sigarid
      simp3 oveq1d cneg mul02d 3eqtrd negeqd neg0 a1i rexlimdv3a impbid ) AEGLM
      FGLMHMZNOZGFDUAZEFLMZPMZQMZOZDUBUCZAWJWPAWJUGZGFLMZWLUHMZUBRGFWSWLPMZQMZO
      WPWQBCFGEHIAFSRZGSRZESRZUDZWJAXBXCXDAXDXBXCJUEZAXDXBXCJUFZAXDXBXCJUIZUJZT
      AEFOUKWJKTZAWJWRWLHMZNOAWIXKNAWIFELMGELMHMZXKAXDXBXCUDWIXLOJBCEFGHIULUMAX
      EXLXKOXIBCFGEHIULUMUSZUNUOUPWQXAFWRQMGWQWTWRFQWQWRWLAWRSRWJAGFXGXFUQTAWLS
      RZWJAEFXHXFUQTWQEFAXDWJXHTAXBWJXFTZWQEFXJURUTVAVBWQFGXOAXCWJXGTVCVDDWSUBW
      NXAGWKWSOWMWTFQWKWSWLPVIVBVEVFVGAWOWJDUBAWKUBRZWOUDZWIXKWLWKPMZWLHMZNAXPW
      IXKOWOXMVHXQXKWMWLHMXSXQWRWMWLHXQGFWMAXPXBWOXFVHZXQWKWLXQWKAXPWOVJZVKZXQE
      FAXPXDWOXHVHXTUQZVLAXPWOVSVMVTXQWMXRWLHXQWKWLYBYCVNVTUSXQXSWLXRHMZWAZNWAZ
      NXQXRSRXNXSYEOXQWLWKYCYBVLYCBCXRWLHIVOVFXQYDNXQYDWLWLHMZWKPMZNWKPMNXQXNXN
      XPYDYHOYCYCYABCWLWLWKHIVPVQXQYGNWKPXQXNYGNOYCBCWLHIVRUMVTXQWKYBWBWCWDYFNO
      XQWEWFWCWCWGWH $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.
    sharhght.sigar $e |- G
        = ( x e. CC , y e. CC |-> ( Im ` ( ( * ` x ) x. y ) ) ) $.
    sharhght.a $e |- ( ph -> ( A e. CC /\ B e. CC /\ C e. CC ) ) $.
    sharhght.b $e |- ( ph -> ( D e. CC /\ ( ( A - D ) G ( B - D ) ) = 0 ) ) $.
    $( Let ` A B C ` be a triangle, and let ` D ` lie on the line ` A B ` .
       Then (doubled) areas of triangles ` A D C ` and ` C D B ` relate as
       lengths of corresponding bases ` A D ` and ` D B ` .  (Contributed by
       Saveliy Skresanov, 23-Sep-2017.) $)
    sharhght $p |- ( ph -> ( ( ( C - A ) G ( D - A ) ) x. ( B - D ) )
          = ( ( ( C - B ) G ( D - B ) ) x. ( A - D ) ) ) $=
      ( wceq cmin co cmul cc0 cc wcel subcld adantr wa cr simp3d simp1d sigarim
      simpld syl2anc recnd mul01d simp2d simpr subeq0bd oveq2d ccj cfv sigarval
      cim eqcomd cjcld eqtrd fveq2d 0red reim0d 3eqtrd oveq1d mul02d 3eqtr4d wn
      cdiv npncand sigaraf syl3anc eqtr3d simprd sigarperm addridd 3eqtr2d cneg
      c1 negsubdi2d neqned subne0d divnegd dividd negeqd mulm1d div32d sigardiv
      caddc 3jca sigarls divcld mulassd divcan1d pm2.61dan ) AEGLZFDMNZGDMNZHNZ
      EGMNZONZFEMNZGEMNZHNZDGMNZONZLAWPUAZWSPONPXAXFXGWSXGWSXGWQQRZWRQRZWSUBRAX
      HWPAFDADQRZEQRZFQRZJUCZAXJXKXLJUDZSTAXIWPAGDAGQRZXEWTHNZPLZKUFZXNSZTBCWQW
      RHIUEUGUHUIXGWTPWSOXGEGAXKWPAXJXKXLJUJZTAWPUKZULUMXGXFPXEONPXGXDPXEOXGXDX
      BUNUOZXCONZUQUOZPUQUOPXGXBQRZXCQRZXDYDLAYEWPAFEXMXTSTZAYFWPAGEXRXTSTBCXBX
      CHIUPUGXGYCPUQXGYCYBPONPXGXCPYBOXGGEAXOWPXRTZXGEGYAURULUMXGYBXGXBYGUSUIUT
      VAXGPXGVBVCVDVEXGXEXGDGAXJWPXNTYHSVFUTVGAWPVHZUAZXAXDXEWTVINZONZWTONXDYKW
      TONZONXFYJWSYLWTOYJWSXBWRHNZXBXCYKONZHNZYLYJWSYNEDMNZWRHNZWINZYNPWINYNYJX
      BYQWINZWRHNZWSYSYJYTWQWRHYJFEDAXLYIXMTZAXKYIXTTZAXJYIXNTZVJVEYJYEXIYQQRUU
      AYSLYJFEUUBUUCSZAXIYIXSTZYJEDUUCUUDSBCXBWRYQHIVKVLVMYJPYRYNWIYJXPPYRAXQYI
      AXOXQKVNTZYJXJXKXOXPYRLUUDUUCAXOYIXRTZBCDEGHIVOVLVMUMYJYNYJYNYJYEXIYNUBRU
      UEUUFBCXBWRHIUEUGUHVPVQYJWRYOXBHYJXCWTVINZXEONZWRYOYJUUJVSVRZXEONXEVRWRYJ
      UUIUUKXEOYJUUIWTVRZWTVINWTWTVINZVRUUKYJXCUULWTVIYJUULXCYJEGUUCUUHVTURVEYJ
      WTWTYJEGUUCUUHSZUUNYJEGUUCUUHYJEGAYIUKZWAWBZWCYJUUMVSYJWTUUNUUPWDWEVQVEYJ
      XEYJDGUUDUUHSZWFYJDGUUDUUHVTVDYJXCWTXEYJGEUUHUUCSZUUNUUQUUPWGVMUMYJYEYFYK
      UBRYPYLLUUEUURYJBCGDEHIYJXOXJXKUUHUUDUUCWJUUOUUGWHBCXBXCYKHIWKVLVDVEYJXDY
      KWTYJYEYFXDQRUUEUURYEYFUAXDBCXBXCHIUEUHUGYJXEWTUUQUUNUUPWLUUNWMYJYMXEXDOY
      JXEWTUUQUUNUUPWNUMVDWO $.

    $( Subtracting (double) area of ` A D C ` from ` A B C ` yields the
       (double) area of ` D B C ` .  (Contributed by Saveliy Skresanov,
       23-Sep-2017.) $)
    sigaradd $p |- ( ph -> ( ( ( B - C ) G ( A - C ) )
              - ( ( D - C ) G ( A - C ) ) ) = ( ( B - C ) G ( D - C ) ) ) $=
      ( cmin co cc0 cc wcel wceq subcld syl3anc cneg simp1d simp3d nnncan1d jca
      simpld oveq2d simp2d sigarms eqtr3d sigarac syl2anc simprd negeqd negnegd
      sigarimcd neg0 3eqtr3d subid1d 3eqtrd nnncan2d oveq1d sigarmf 3eqtr2rd c1
      a1i cmul cr 1red renegcld sigarls mulm1d 1cnd negcld negsubdi2d sigarperm
      mulcomd 3eqtr4d ) AEFLMZDFLMZHMGFLMZVSHMLMZEGLMZVTHMZFGLMZWBHMZVRVTHMZAWC
      WBVSHMZVRVTLMZVSHMZWAAWCWGWBDGLMZHMZLMZWGNLMWGAWBVSWJLMZHMZWCWLAWMVTWBHAD
      FGADOPZEOPZFOPZJUAZAWOWPWQJUBZAGOPZWJWBHMZNQZKUEZUCUFAWBOPZVSOPZWJOPZWNWL
      QAEGAWOWPWQJUGZXCRZADFWRWSRZADGWRXCRZBCWBVSWJHIUHSUIAWKNWGLAWKTZTNTZWKNAX
      KNAXAXKNAXFXDXAXKQXJXHBCWJWBHIUJUKAWTXBKULUIUMAWKABCWBWJHIAXDXFXHXJUDUOUN
      XLNQAUPVEUQUFAWGABCWBVSHIAXDXEXHXIUDUOURUSAWHWBVSHAEGFXGXCWSUTVAAVROPXEVT
      OPWIWAQAEFXGWSRXIAGFXCWSRBCVRVSVTHIVBSVCAWBWDVDTZVFMZHMZWBWDHMZXMVFMZWCWE
      AXDWDOPZXMVGPXOXQQXHAFGWSXCRZAVDAVHVIBCWBWDXMHIVJSAXNVTWBHAXMWDVFMWDTXNVT
      AWDXSVKAXMWDAVDAVLVMZXSVPAFGWSXCVNUQUFAXMXPVFMXPTZXQWEAXPABCWBWDHIAXDXRXH
      XSUDUOZVKAXPXMYBXTVPAXRXDWEYAQXSXHBCWDWBHIUJUKVQUQAWQWPWTWEWFQWSXGXCBCFEG
      HIVOSUS $.
  $}

  ${
    cevathlem1.a $e |- ( ph -> ( A e. CC /\ B e. CC /\ C e. CC ) ) $.
    cevathlem1.b $e |- ( ph -> ( D e. CC /\ E e. CC /\ F e. CC ) ) $.
    cevathlem1.c $e |- ( ph -> ( G e. CC /\ H e. CC /\ K e. CC ) ) $.
    cevathlem1.d $e |- ( ph -> ( A =/= 0 /\ E =/= 0 /\ C =/= 0 ) ) $.
    cevathlem1.e $e |- ( ph -> ( ( A x. B ) = ( C x. D ) /\ ( E x. F )
        = ( A x. G ) /\ ( C x. H ) = ( E x. K ) ) ) $.
    $( Ceva's theorem first lemma.  Multiplies three identities and divides by
       the common factors.  (Contributed by Saveliy Skresanov, 24-Sep-2017.) $)
    cevathlem1 $p |- ( ph -> ( ( B x. F ) x. H ) = ( ( D x. G ) x. K ) ) $=
      ( cmul co cc wcel mulcld simp2d simp3d cc0 wne mulne0d wceq oveq12d mul4d
      simp1d 3eqtr3d mul32d mulcomd oveq1d eqtrd eqtr4d mulcanad ) ACGPQZIPQZEH
      PQZJPQZBFPQZDPQZAUQIACGABRSZCRSZDRSZKUAZAERSZFRSZGRSZLUBZTZAHRSZIRSZJRSZM
      UAZTAUSJAEHAVGVHVILUIZAVLVMVNMUIZTZAVLVMVNMUBZTAVADABFAVCVDVEKUIZAVGVHVIL
      UAZTZAVCVDVEKUBZTAVADWBWCABFVTWAABUCUDZFUCUDZDUCUDZNUIAWDWEWFNUAUEAWDWEWF
      NUBUEAVBURPQZDBPQZFPQZUTPQZVBUTPQAVAUQPQZDIPQZPQWHUSPQZFJPQZPQWGWJAWKWMWL
      WNPABCPQZFGPQZPQDEPQZBHPQZPQWKWMAWOWQWPWRPAWOWQUFZWPWRUFZWLWNUFZOUIAWSWTX
      AOUAUGABCFGVTVFWAVJUHADEBHWCVPVTVQUHUJAWSWTXAOUBUGAVAUQDIWBVKWCVOUHAWHUSF
      JADBWCVTTVRWAVSUHUJAVBWIUTPAVBBDPQZFPQWIABFDVTWAWCUKAXBWHFPABDVTWCULUMUNU
      MUOUP $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.  $d x y O $.
    $d x y E $.  $d x y F $.
    cevath.sigar $e |- G
        = ( x e. CC , y e. CC |-> ( Im ` ( ( * ` x ) x. y ) ) ) $.
    cevath.a $e |- ( ph -> ( A e. CC /\ B e. CC /\ C e. CC ) ) $.
    cevath.b $e |- ( ph -> ( F e. CC /\ D e. CC /\ E e. CC ) ) $.
    cevath.c $e |- ( ph -> O e. CC ) $.
    cevath.d $e |- ( ph -> ( ( ( A - O ) G ( D - O ) ) = 0
       /\ ( ( B - O ) G ( E - O ) ) = 0 /\ ( ( C - O ) G ( F - O ) ) = 0 ) ) $.
    cevath.e $e |- ( ph -> ( ( ( A - F ) G ( B - F ) ) = 0
       /\ ( ( B - D ) G ( C - D ) ) = 0 /\ ( ( C - E ) G ( A - E ) ) = 0 ) ) $.
    cevath.f $e |- ( ph -> ( ( ( A - O ) G ( B - O ) ) =/= 0
   /\ ( ( B - O ) G ( C - O ) ) =/= 0 /\ ( ( C - O ) G ( A - O ) ) =/= 0 ) ) $.
    $( Ceva's theorem second lemma.  Relate (doubled) areas of triangles
       ` C A O ` and ` A B O ` with of segments ` B D ` and ` D C ` .
       (Contributed by Saveliy Skresanov, 24-Sep-2017.) $)
    cevathlem2 $p |- ( ph -> ( ( ( C - O ) G ( A - O ) ) x. ( B - D ) )
          = ( ( ( A - O ) G ( B - O ) ) x. ( D - C ) ) ) $=
      ( cmin co cmul cneg wcel simp2d simp1d 3jca cc0 wceq jca sigariz sigaradd
      cc subcld sigarperm syl3anc eqtr4d oveq1d sigarimcd simp3d subdird eqtr3d
      sharhght oveq12d cr sigarim syl2anc recnd 3eqtrrd sigarac mulneg12 oveq2d
      negsubdi2d eqtrd 3eqtrd ) AFKSTZDKSTZJTZEGSTZUATZEKSTZVPJTZFGSTZUATZVPVTJ
      TZUBZWBUATZWDGFSTZUATZAWCDESTZGESTZJTZWBUATZKESTZWJJTZWBUATZSTZDFSTZWGJTZ
      VRUATZKFSTZWGJTZVRUATZSTZVSAWKWNSTZWBUATWCWPAXDWAWBUAAXDWIWMJTZWAABCGDEKJ
      LAGULUCZDULUCZEULUCZAIULUCXFHULUCNUDZAXGXHFULUCZMUEZAXGXHXJMUDZUFAKULUCZG
      KSTZVPJTUGUHOABCVPXNJLAVPULUCZXNULUCADKXKOUMZAGKXIOUMUIAVPXNJTUGUHVTHKSTJ
      TUGUHVOIKSTJTUGUHPUEUJUIZUKAXHXGXMWAXEUHXLXKOBCEDKJLUNUOUPUQAWKWNWBABCWIW
      JJLAWIULUCWJULUCZADEXKXLUMAGEXIXLUMZUIURABCWMWJJLAWMULUCXRAKEOXLUMXSUIURA
      FGAXGXHXJMUSZXIUMZUTVAAWLWSWOXBSABCEFDGJLAXHXJXGXLXTXKUFAXFVRWBJTUGUHZXIA
      DISTEISTJTUGUHYBFHSTDHSTJTUGUHQUDUIZVBABCEFKGJLAXHXJXMXLXTOUFYCVBVCAWRXAS
      TZVRUATXCVSAWRXAVRAWRAWQULUCWGULUCZWRVDUCADFXKXTUMAGFXIXTUMZBCWQWGJLVEVFV
      GABCWTWGJLAWTULUCYEAKFOXTUMYFUIURAEGXLXIUMUTAYDVQVRUAAYDWQWTJTZVQABCGDFKJ
      LAXFXGXJXIXKXTUFXQUKAXJXGXMVQYGUHXTXKOBCFDKJLUNUOUPUQVAVHAWAWEWBUAAVTULUC
      ZXOWAWEUHAEKXLOUMZXPBCVTVPJLVIVFUQAWFWDWBUBZUATZWHAWDULUCWBULUCWFYKUHABCV
      PVTJLAXOYHXPYIUIURYAWDWBVJVFAYJWGWDUAAFGXTXIVLVKVMVN $.

    $( Ceva's theorem.  Let ` A B C ` be a triangle and let points ` F ` ,
       ` D ` and ` E ` lie on sides ` A B ` , ` B C ` , ` C A `
       correspondingly.  Suppose that cevians ` A D ` , ` B E ` and ` C F `
       intersect at one point ` O ` .  Then triangle's sides are partitioned
       into segments and their lengths satisfy a certain identity.  Here we
       obtain a bit stronger version by using complex numbers themselves
       instead of their absolute values.

       The proof goes by applying ~ cevathlem2 three times and then using
       ~ cevathlem1 to multiply obtained identities and prove the theorem.

       In the theorem statement we are using function ` G ` as a collinearity
       indicator.  For justification of that use, see ~ sigarcol .  This is
       Metamath 100 proof #61.  (Contributed by Saveliy Skresanov,
       24-Sep-2017.) $)
    cevath $p |- ( ph -> ( ( ( A - F ) x. ( C - E ) ) x. ( B - D ) )
          = ( ( ( F - B ) x. ( E - A ) ) x. ( D - C ) ) ) $=
      ( co cc cmin wcel simp2d subcld simp3d jca sigarimcd simp1d 3jca cc0 cmul
      wne wceq cevathlem2 cevathlem1 ) AEKUASZFKUASZJSZDIUASZUQDKUASZJSZIEUASZU
      TUPJSZFHUASZHDUASZEGUASZGFUASZAURTUBUSTUBVATUBABCUPUQJLAUPTUBZUQTUBZAEKAD
      TUBZETUBZFTUBZMUCZOUDZAFKAVJVKVLMUEZOUDZUFUGADIAVJVKVLMUHZAITUBZGTUBZHTUB
      ZNUHZUDABCUQUTJLAVIUTTUBZVPADKVQOUDZUFUGUIAVBTUBVCTUBVDTUBAIEWAVMUDABCUTU
      PJLAWBVHWCVNUFUGAFHVOAVRVSVTNUEZUDUIAVETUBVFTUBVGTUBAHDWDVQUDAEGVMAVRVSVT
      NUCZUDAGFWEVOUDUIAURUJULZVCUJULZVAUJULZAWGWFWHRUCZAWGWFWHRUHZAWGWFWHRUEZU
      IAURUSUKSVAVBUKSUMVCVDUKSURVEUKSUMVAVFUKSVCVGUKSUMABCFDEIGHJKLAVLVJVKVOVQ
      VMUIAVTVRVSWDWAWEUIOAUQIKUASJSUJUMZUTGKUASJSUJUMZUPHKUASJSUJUMZAWMWNWLPUE
      ZAWMWNWLPUHZAWMWNWLPUCZUIAVDDHUASJSUJUMZUSEIUASJSUJUMZVFFGUASJSUJUMZAWSWT
      WRQUEZAWSWTWRQUHZAWSWTWRQUCZUIAWHWGWFWKWJWIUIUNABCEFDHIGJKLAVKVLVJVMVOVQU
      IAVSVTVRWEWDWAUIOAWNWLWMWQWOWPUIAWTWRWSXCXAXBUIAWFWHWGWIWKWJUIUNABCDEFGHI
      JKLMNOPQRUNUIUO $.
  $}


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Simple groups
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    simpcntrab.a $e |- B = ( Base ` G ) $.
    simpcntrab.b $e |- .0. = ( 0g ` G ) $.
    simpcntrab.c $e |- Z = ( Cntr ` G ) $.
    simpcntrab.d $e |- ( ph -> G e. SimpGrp ) $.
    $( The center of a simple group is trivial or the group is abelian.
       (Contributed by SS, 3-Jan-2024.) $)
    simpcntrab $p |- ( ph -> ( Z = { .0. } \/ G e. Abel ) ) $=
      ( wceq wo wa cabl wcel cgrp cfv syl cress co adantr csn simpggrpd cntrnsg
      cnsg simpgnsgeqd ancli andi biimpi simpr orim1i ccntr oveq2 oveq2i adantl
      eqtr3di ressid eqtr3d eqid cntrabl eqeltrrd orim2i 4syl ) AAEDUAJZEBJZKZL
      ZAVCLZAVDLZKZVCVHKVCCMNZKAVEAEBCDFGIACONZECUDPNACIUBZCEHUCQUEUFVFVIAVCVDU
      GUHVGVCVHAVCUIUJVHVJVCVHCCUKPZRSZCMVHCBRSZVNCVDVOVNJAVDCERSVOVNEBCRULEVMC
      RHUMUOUNAVOCJZVDAVKVPVLBCOFUPQTUQAVNMNZVDAVKVQVLCVNVNURUSQTUTVAVB $.
  $}

$( (End of Saveliy Skresanov's mathbox.) $)
