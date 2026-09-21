$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Extended sum
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c sum* $. $( Summation sign. $)

  $( Extend class notation to include infinite summations. $)
  cesum $a class sum* k e. A B $.

  $( Define a short-hand for the possibly infinite sum over the extended
     nonnegative reals. ` sum* ` is relying on the properties of the
     ` tsums ` , developed by Mario Carneiro.  (Contributed by Thierry Arnoux,
     21-Sep-2016.) $)
  df-esum $a |- sum* k e. A B =
    U. ( ( RR*s |`s ( 0 [,] +oo ) ) tsums ( k e. A |-> B ) ) $.

  $( An extended sum is a set by definition.  (Contributed by Thierry Arnoux,
     5-Sep-2017.) $)
  esumex $p |- sum* k e. A B e. _V $=
    ( cesum cxrs cc0 cpnf cicc co cress cmpt ctsu cuni cvv df-esum ovex eqeltri
    uniex ) ABCDEFGHIJIZCABKZLIZMNABCOUASTLPRQ $.

  ${
    $d k V $.
    esumcl.1 $e |- F/_ k A $.
    $( Closure for extended sum in the extended positive reals.  (Contributed
       by Thierry Arnoux, 2-Jan-2017.) $)
    esumcl $p |- ( ( A e. V /\ A. k e. A B e. ( 0 [,] +oo ) ) ->
                        sum* k e. A B e. ( 0 [,] +oo ) ) $=
      ( wcel cc0 cpnf cicc co wral wa cxrs cress cmpt ctsu cesum xrge0base eqid
      a1i ccmn xrge0cmn ctps xrge0tps simpl nfel1 nfra1 nfan nfcv simpr fmptdf2
      r19.21bi tsmscl cuni wceq df-esum xrge0tsmsbi mpbiri sseldd ) ADFZBGHIJZF
      ZCAKZLZMVANJZCABOZPJZVAABCQZVDAVAVFVEDRVEUAFVDUBTVEUCFVDUDTUTVCUEZVDCABVA
      VFUTVCCCADEUFVBCAUGUHECVAUIVDVBCAUTVCUJULVFSUKZUMVDVHVGFVHVGUNUOABCUPVDAV
      HVFVEDVESVIVJUQURUS $.
  $}

  ${
    esumeq12dvaf.1 $e |- F/ k ph $.
    esumeq12dvaf.2 $e |- ( ph -> A = B ) $.
    esumeq12dvaf.3 $e |- ( ( ph /\ k e. A ) -> C = D ) $.
    $( Equality deduction for extended sum.  (Contributed by Thierry Arnoux,
       26-Mar-2017.) $)
    esumeq12dvaf $p |- ( ph -> sum* k e. A C = sum* k e. B D ) $=
      ( cxrs cc0 cpnf cicc co cmpt ctsu cuni cesum wceq df-esum wal wral alrimi
      cress cv wcel ex ralrimi mpteq12f syl2anc oveq2d unieqd 3eqtr4g ) AJKLMNU
      DNZFBDOZPNZQUNFCEOZPNZQBDFRCEFRAUPURAUOUQUNPABCSZFUADESZFBUBUOUQSAUSFGHUC
      AUTFBGAFUEBUFUTIUGUHFBDCEUIUJUKULBDFTCEFTUM $.
  $}

  ${
    $d k ph $.
    esumeq12dva.1 $e |- ( ph -> A = B ) $.
    esumeq12dva.2 $e |- ( ( ph /\ k e. A ) -> C = D ) $.
    $( Equality deduction for extended sum.  (Contributed by Thierry Arnoux,
       18-Feb-2017.)  (Revised by Thierry Arnoux, 29-Jun-2017.) $)
    esumeq12dva $p |- ( ph -> sum* k e. A C = sum* k e. B D ) $=
      ( nfv esumeq12dvaf ) ABCDEFAFIGHJ $.
  $}

  ${
    $d k ph $.
    esumeq12d.1 $e |- ( ph -> A = B ) $.
    esumeq12d.2 $e |- ( ph -> C = D ) $.
    $( Equality deduction for extended sum.  (Contributed by Thierry Arnoux,
       18-Feb-2017.) $)
    esumeq12d $p |- ( ph -> sum* k e. A C = sum* k e. B D ) $=
      ( wceq cv wcel adantr esumeq12dva ) ABCDEFGADEIFJBKHLM $.
  $}

  ${
    $d k A $.  $d k B $.
    $( Equality theorem for an extended sum.  (Contributed by Thierry Arnoux,
       18-Feb-2017.) $)
    esumeq1 $p |- ( A = B -> sum* k e. A C = sum* k e. B C ) $=
      ( wceq id eqidd esumeq12d ) ABEZABCCDIFICGH $.
  $}

  ${
    esumeq1d.0 $e |- F/ k ph $.
    esumeq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality theorem for an extended sum.  (Contributed by Thierry Arnoux,
       19-Oct-2017.) $)
    esumeq1d $p |- ( ph -> sum* k e. A C = sum* k e. B C ) $=
      ( cv wcel wa eqidd esumeq12dvaf ) ABCDDEFGAEHBIJDKL $.
  $}

  ${
    $d k A $.
    $( Equality theorem for extended sum.  (Contributed by Thierry Arnoux,
       24-Dec-2016.) $)
    esumeq2 $p |- ( A. k e. A B = C -> sum* k e. A B = sum* k e. A C ) $=
      ( wceq wral cxrs cc0 cpnf cicc co cress cmpt ctsu cuni cesum eqid mpteq12
      mpan df-esum oveq2d unieqd 3eqtr4g ) BCEDAFZGHIJKLKZDABMZNKZOUEDACMZNKZOA
      BDPACDPUDUGUIUDUFUHUENAAEUDUFUHEAQDABACRSUAUBABDTACDTUC $.
  $}

  ${
    esumeq2d.0 $e |- F/ k ph $.
    esumeq2d.1 $e |- ( ph -> A. k e. A B = C ) $.
    $( Equality deduction for extended sum.  (Contributed by Thierry Arnoux,
       21-Sep-2016.) $)
    esumeq2d $p |- ( ph -> sum* k e. A B = sum* k e. A C ) $=
      ( eqidd wceq r19.21bi esumeq12dvaf ) ABBCDEFABHACDIEBGJK $.
  $}

  ${
    $d k ph $.
    esumeq2dv.1 $e |- ( ( ph /\ k e. A ) -> B = C ) $.
    $( Equality deduction for extended sum.  (Contributed by Thierry Arnoux,
       2-Jan-2017.) $)
    esumeq2dv $p |- ( ph -> sum* k e. A B = sum* k e. A C ) $=
      ( nfv wceq ralrimiva esumeq2d ) ABCDEAEGACDHEBFIJ $.
  $}

  ${
    $d k ph $.
    esumeq2sdv.1 $e |- ( ph -> B = C ) $.
    $( Equality deduction for extended sum.  (Contributed by Thierry Arnoux,
       25-Dec-2016.) $)
    esumeq2sdv $p |- ( ph -> sum* k e. A B = sum* k e. A C ) $=
      ( wceq cv wcel adantr esumeq2dv ) ABCDEACDGEHBIFJK $.
  $}

  ${
    nfesum1.1 $e |- F/_ k A $.
    $( Bound-variable hypothesis builder for extended sum.  (Contributed by
       Thierry Arnoux, 19-Oct-2017.) $)
    nfesum1 $p |- F/_ k sum* k e. A B $=
      ( cesum cxrs cc0 cpnf cicc cress cmpt ctsu cuni df-esum nfcv nfmpt1 nfuni
      co nfov nfcxfr ) CABCEFGHIRJRZCABKZLRZMABCNCUCCUAUBLCUAOCLOCABPSQT $.
  $}

  ${
    $d k x $.
    nfesum2.1 $e |- F/_ x A $.
    nfesum2.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for extended sum.  (Contributed by
       Thierry Arnoux, 2-May-2020.) $)
    nfesum2 $p |- F/_ x sum* k e. A B $=
      ( cesum cxrs cc0 cpnf cicc cress cmpt ctsu cuni df-esum nfcv nfmpt nfov
      co nfuni nfcxfr ) ABCDGHIJKTLTZDBCMZNTZOBCDPAUEAUCUDNAUCQANQADBCEFRSUAUB
      $.
  $}

  ${
    $d j k $.
    cbvesum.1 $e |- ( j = k -> B = C ) $.
    ${
      cbvesum.2 $e |- F/_ k A $.
      cbvesum.3 $e |- F/_ j A $.
      cbvesum.4 $e |- F/_ k B $.
      cbvesum.5 $e |- F/_ j C $.
      $( Change bound variable in an extended sum.  (Contributed by Thierry
         Arnoux, 19-Jun-2017.) $)
      cbvesum $p |- sum* j e. A B = sum* k e. A C $=
        ( cxrs cc0 cpnf cicc co cmpt ctsu cuni cesum df-esum cbvmptf 3eqtr4i
        cress oveq2i unieqi ) KLMNOUCOZDABPZQOZRUFEACPZQOZRABDSACESUHUJUGUIUFQD
        EABCHGIJFUAUDUEABDTACETUB $.
    $}

    $d A j $.  $d A k $.  $d B k $.  $d C j $.
    $( Change bound variable in an extended sum.  (Contributed by Thierry
       Arnoux, 19-Jun-2017.) $)
    cbvesumv $p |- sum* j e. A B = sum* k e. A C $=
      ( cxrs cc0 cpnf cicc co cress cmpt ctsu cuni cesum cbvmptv oveq2i df-esum
      unieqi 3eqtr4i ) GHIJKLKZDABMZNKZOUBEACMZNKZOABDPACEPUDUFUCUEUBNDEABCFQRT
      ABDSACESUA $.
    $( $j usage 'cbvesumv' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    esumid.p $e |- F/ k ph $.
    esumid.0 $e |- F/_ k A $.
    esumid.1 $e |- ( ph -> A e. V ) $.
    esumid.2 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumid.3 $e |- ( ph -> C e. ( ( RR*s |`s ( 0 [,] +oo ) )
                                                  tsums ( k e. A |-> B ) ) ) $.
    $( Identify the extended sum as any limit points of the infinite sum.
       (Contributed by Thierry Arnoux, 9-May-2017.) $)
    esumid $p |- ( ph -> sum* k e. A B = C ) $=
      ( cesum cxrs cc0 cpnf cicc co cress cmpt eqid df-esum fmptdf2 xrge0tsmseq
      ctsu cuni nfcv eqtr4id ) ABCELMNOPQZRQZEBCSZUDQUEDBCEUAABDUJUIFUITIAEBCUH
      UJGHEUHUFJUJTUBKUCUG $.
  $}

  ${
    esumgsum.1 $e |- F/ k ph $.
    esumgsum.2 $e |- F/_ k A $.
    esumgsum.3 $e |- ( ph -> A e. Fin ) $.
    esumgsum.4 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    $( A finite extended sum is the group sum over the extended nonnegative
       real numbers.  (Contributed by Thierry Arnoux, 24-Apr-2020.) $)
    esumgsum $p |- ( ph -> sum* k e. A B
      = ( ( RR*s |`s ( 0 [,] +oo ) ) gsum ( k e. A |-> B ) ) ) $=
      ( cxrs cc0 cpnf cicc co cress cmpt cgsu cfn wcel a1i cxr xrge0base xrge00
      ccmn xrge0cmn ctps xrge0tps nfcv eqid fmptdf2 wral wfn ralrimi fnmptf syl
      cv ex 0xr fndmfifsupp tsmsid esumid ) ABCIJKLMZNMZDBCOZPMDQEFGHABVAVCVBQJ
      UAUBVBUCRAUDSVBUERAUFSGADBCVAVCEFDVAUGHVCUHUIABVCTJACVARZDBUJVCBUKAVDDBEA
      DUOBRVDHUPULDBCVAFUMUNGJTRAUQSURUSUT $.
  $}

  ${
    $d k x $.  $d x A $.  $d x ph $.  $d x B $.
    esumval.p $e |- F/ k ph $.
    esumval.0 $e |- F/_ k A $.
    esumval.1 $e |- ( ph -> A e. V ) $.
    esumval.2 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumval.3 $e |- ( ( ph /\ x e. ( ~P A i^i Fin ) ) ->
                  ( ( RR*s |`s ( 0 [,] +oo ) ) gsum ( k e. x |-> B ) ) = C ) $.
    $( Develop the value of the extended sum.  (Contributed by Thierry Arnoux,
       4-Jan-2017.) $)
    esumval $p |- ( ph -> sum* k e. A B =
                     sup ( ran ( x e. ( ~P A i^i Fin ) |-> C ) , RR* , < ) ) $=
      ( cfn cmpt crn cxr clt cuni co cgsu cesum cpw cin csup csn cxrs cpnf cicc
      cc0 cress ctsu df-esum eqid nfcv fmptdf2 cv cres wcel wa wceq inss1 sseli
      wss elpwid adantl resmptf oveq2d eqtr2d mpteq2dva rneqd xrge0tsmsd unieqd
      syl supeq1d eqtrid xrltso supex unisn eqtrdi ) ACDFUAZBCUBZMUCZENZOZPQUDZ
      UEZRZWEAVTUFUIUGUHSZUJSZFCDNZUKSZRWGCDFULAWKWFACWEWJWIGBWIUMJAFCDWHWJHIFW
      HUNKWJUMUOAPWDBWBWIWJBUPZUQZTSZNZOQAWCWOABWBEWNAWLWBURZUSZWNWIFWLDNZTSEWQ
      WMWRWITWQWLCVCZWMWRUTWPWSAWPWLCWBWAWLWAMVAVBVDVEFCWLDIFWLUNVFVMVGLVHVIVJV
      NVKVLVOWEPWDQVPVQVRVS $.
  $}

  ${
    $d x k $.  $d x A $.  $d k V $.  $d x ph $.  $d x B $.
    esumel.1 $e |- F/ k ph $.
    esumel.2 $e |- F/_ k A $.
    esumel.3 $e |- ( ph -> A e. V ) $.
    esumel.4 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    $( The extended sum is a limit point of the corresponding infinite group
       sum.  (Contributed by Thierry Arnoux, 24-Mar-2017.) $)
    esumel $p |- ( ph -> sum* k e. A B e.
                     ( ( RR*s |`s ( 0 [,] +oo ) ) tsums ( k e. A |-> B ) ) ) $=
      ( vx cesum co cmpt wcel cv syl eqid nfcv cgsu cfn csn cxrs cc0 cpnf cress
      cicc ctsu wral ralrimi esumcl syl2anc snidg fmptdf2 cres cpw cin wss wceq
      ex wa inss1 simpr sselid elpwid resmptf eqcomd oveq2d xrge0tsmsd eleqtrrd
      esumval ) ABCDKZVKUAZUBUCUDUFLZUELZDBCMZUGLAVKVMNZVKVLNABENCVMNZDBUHVPHAV
      QDBFADOBNVQIUSUIBCDEGUJUKVKVMULPABVKVOVNEJVNQHADBCVMVOFGDVMRIVOQUMAJBCVNV
      OJOZUNZSLDEFGHIAVRBUOZTUPZNZUTZDVRCMZVSVNSWCVSWDWCVRBUQVSWDURWCVRBWCWAVTV
      RVTTVAAWBVBVCVDDBVRCGDVRRVEPVFVGVJVHVI $.
  $}

  ${
    $d x y $.  $d y A $.
    $( Extended sum over the empty set.  (Contributed by Thierry Arnoux,
       19-Feb-2017.) $)
    esumnul $p |- sum* x e. (/) A = 0 $=
      ( vy c0 cfn cin cc0 cmpt cxr clt csup csn wceq wtru cvv wcel 0ex a1i cgsu
      co cesum cpw nftru nfcv cpnf cicc wral ral0 r19.21bi cv cxrs cress ineq1i
      crn pw0 0fi snssi dfss2 sylib ax-mp eqtri eleq2i velsn sylbb mpteq1d mpt0
      wss eqtrdi oveq2d xrge00 gsum0 adantl esumval mptru cxp fconstmpt wfn wne
      eqcomi wb rgenw eqid fnmpt snnz eqnetri fconst5 mp2an mpbi supeq1i xrltso
      0xr wor supsn 3eqtri ) DBAUAZCDUBZEFZGHZUNZIJKZGLZIJKZGWOWTMNCDBGAOAUCADU
      DDOPNQRNBGUEUFTZPZADXDADUGNXDAUHRUICUJZWQPZUKXCULTZAXEBHZSTZGMNXFXIXGDSTG
      XFXHDXGSXFXHADBHDXFAXEDBXFXEDLZPXEDMWQXJXEWQXJEFZXJWPXJEUOUMDEPZXKXJMZUPX
      LXJEVGXMDEUQXJEURUSUTVAZVBCDVCVDVEABVFVHVIXGGVJVKVHVLVMVNIWSXAJWRWQXAVOZM
      ZWSXAMZXOWRCWQGVPVSWRWQVQZWQDVRXPXQVTGIPZCWQUGXRXSCWQWKWACWQGWRIWRWBWCUTW
      QXJDXNDQWDWEWQGWRWFWGWHWIIJWLXSXBGMWJWKIGJWMWGWN $.
  $}

  ${
    esum0.k $e |- F/_ k A $.
    $d x A $.  $d k x V $.
    $( Extended sum of zero.  (Contributed by Thierry Arnoux, 3-Mar-2017.) $)
    esum0 $p |- ( A e. V -> sum* k e. A 0 = 0 ) $=
      ( vx wcel cc0 cfn cmpt cxr clt csup co cv wa a1i wceq cvv mp2an c0 cpw id
      cesum nfel1 cpnf cicc 0e0iccpnf cxrs cress cgsu cmnd ccmn xrge0cmn cmnmnd
      cin crn ax-mp vex xrge00 esumval csn cxp fconstmpt eqcomi wfn wne wb wral
      gsumz 0xr rgenw eqid fnmpt 0elpw elin mpbir2an ne0ii fconst5 mpbi supeq1d
      0fi wor xrltso supsn eqtrdi eqtrd ) ACFZAGBUCEAUAZHUOZGIZUPZJKLZGWGEAGGBC
      BACDUDDWGUBGGUEUFMZFWGBNAFOUGPUHWMUIMZBENZGIUJMGQZWGWOWIFOWNUKFZWORFWPWNU
      LFWQUMWNUNUQEURWOBWNRGUSVISPUTWGWLGVAZJKLZGWGJWKWRKWKWRQZWGWJWIWRVBZQZWTX
      AWJEWIGVCVDWJWIVEZWITVFXBWTVGGJFZEWIVHXCXDEWIVJVKEWIGWJJWJVLVMUQTWITWIFTW
      HFTHFAVNWATWHHVOVPVQWIGWJVRSVSPVTJKWBXDWSGQWCVJJGKWDSWEWF $.
  $}

  ${
    $d k n $.  $d k A $.  $d k C $.  $d k G $.  $d k ph $.
    esumf1o.0 $e |- F/ n ph $.
    esumf1o.b $e |- F/_ n B $.
    esumf1o.d $e |- F/_ k D $.
    esumf1o.a $e |- F/_ n A $.
    esumf1o.c $e |- F/_ n C $.
    esumf1o.f $e |- F/_ n F $.
    esumf1o.1 $e |- ( k = G -> B = D ) $.
    esumf1o.2 $e |- ( ph -> A e. V ) $.
    esumf1o.3 $e |- ( ph -> F : C -1-1-onto-> A ) $.
    esumf1o.4 $e |- ( ( ph /\ n e. C ) -> ( F ` n ) = G ) $.
    esumf1o.5 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    $( Re-index an extended sum using a bijection.  (Contributed by Thierry
       Arnoux, 6-Apr-2017.) $)
    esumf1o $p |- ( ph -> sum* k e. A B = sum* n e. C D ) $=
      ( cxrs cc0 cpnf cicc co cress cmpt ctsu cuni ccom xrge0base ccmn xrge0cmn
      cesum wcel a1i ctps xrge0tps fmpttd tsmsf1o cv wa wf1o wf f1of ffvelcdmda
      cfv syl eqeltrrd ex ralrimi feqmptdf mpteq2da eqtrd eqidd fmptcof2 oveq2d
      unieqd df-esum 3eqtr4g ) AUBUCUDUEUFZUGUFZFBCUHZUIUFZUJWCGDEUHZUIUFZUJBCF
      UODEGUOAWEWGAWEWCWDHUKZUIUFWGABWBDWDWCHJULWCUMUPAUNUQWCURUPAUSUQRAFBCWBUA
      UTSVAAWHWFWCUIAGFDBICEHWDLMONKAIBUPZGDKAGVBZDUPZWIAWKVCWJHVHZIBTADBWJHADB
      HVDDBHVESDBHVFVIZVGVJVKVLAHGDWLUHGDIUHAGDBHOPWMVMAGDWLIKTVNVOAWDVPQVQVRVO
      VSBCFVTDEGVTWA $.
  $}

  ${
    $d k y z $.  $d y z A $.  $d y B $.  $d y z C $.  $d y ph $.
    esumc.0 $e |- F/_ k D $.
    esumc.1 $e |- F/ k ph $.
    esumc.2 $e |- F/_ k A $.
    esumc.3 $e |- ( y = C -> D = B ) $.
    esumc.4 $e |- ( ph -> A e. V ) $.
    esumc.5 $e |- ( ph -> Fun `' ( k e. A |-> C ) ) $.
    esumc.6 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumc.7 $e |- ( ( ph /\ k e. A ) -> C e. W ) $.
    $( Convert from the collection form to the class-variable form of a sum.
       (Contributed by Thierry Arnoux, 10-May-2017.) $)
    esumc $p |- ( ph ->
                       sum* k e. A B = sum* y e. { z | E. k e. A z = C } D ) $=
      ( wceq wcel cv wrex cab cesum cmpt cvv nfcv nfab nfmpt1 elex syl abrexexd
      nfre1 wfn ccnv wfun crn wf1o wral ex ralrimi fnmptf eqid rnmpt a1i dff1o2
      syl3anbrc wa cfv simpr fvmpt2f syl2anc cc0 cpnf cicc co vex eqeq1 rexbidv
      elab reximi sylbi nfel eleq1 syl5ibrcom rexlimd imp sylan2 esumf1o eqcomd
      wi ) ACUAZFSZHDUBZCUCZGBUDDEHUDAWOGDEBHHDFUEZFUFLKBEUGWNHCWMHDUMUHMHDFUIN
      AHCDFMADITDUFTODIUJUKULAWPDUNZWPUOUPWPUQWOSZDWOWPURAFJTZHDUSWQAWSHDLAHUAZ
      DTZWSRUTVAHDFJMVBUKPWRAHCDFWPWPVCVDVEDWOWPVFVGAXAVHZXAWSWTWPVIFSAXAVJRHDF
      JMVKVLBUAZWOTZAGESZHDUBZGVMVNVOVPZTZXDXCFSZHDUBZXFWNXJCXCBVQWLXCSWMXIHDWL
      XCFVRVSVTXIXEHDNWAWBAXFXHAXEXHHDLHGXGKHXGUGWCAXAXEXHWKXBXHXEEXGTQGEXGWDWE
      UTWFWGWHWIWJ $.
  $}

  ${
    $d A y z $.  $d B y z $.  $d C k $.  $d D y $.  $d W k $.  $d ph k y z $.
    esumrnmpt.0 $e |- F/_ k A $.
    esumrnmpt.1 $e |- ( y = B -> C = D ) $.
    esumrnmpt.2 $e |- ( ph -> A e. V ) $.
    esumrnmpt.3 $e |- ( ( ph /\ k e. A ) -> D e. ( 0 [,] +oo ) ) $.
    esumrnmpt.4 $e |- ( ( ph /\ k e. A ) -> B e. ( W \ { (/) } ) ) $.
    esumrnmpt.5 $e |- ( ph -> Disj_ k e. A B ) $.
    $( Rewrite an extended sum into a sum on the range of a mapping function.
       (Contributed by Thierry Arnoux, 27-May-2020.) $)
    esumrnmpt $p |- ( ph -> sum* y e. ran ( k e. A |-> B ) C = sum* k e. A D )
      $=
      ( vz cmpt crn cesum wceq cv wrex cab eqid rnmpt esumeq1 ax-mp c0 csn cdif
      nfcv nfv disjdsct esumc eqtr4id ) AGCDQZRZEBSZPUADTGCUBPUCZEBSZCFGSUQUSTU
      RUTTGPCDUPUPUDUEUQUSEBUFUGABPCFDEGHIUHUIUJGEUKAGULZJKLAGCDIVAJNOUMMNUNUO
      $.
  $}

  ${
    esumsplit.1 $e |- F/ k ph $.
    esumsplit.2 $e |- F/_ k A $.
    esumsplit.3 $e |- F/_ k B $.
    esumsplit.4 $e |- ( ph -> A e. _V ) $.
    esumsplit.5 $e |- ( ph -> B e. _V ) $.
    esumsplit.6 $e |- ( ph -> ( A i^i B ) = (/) ) $.
    esumsplit.7 $e |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) ) $.
    esumsplit.8 $e |- ( ( ph /\ k e. B ) -> C e. ( 0 [,] +oo ) ) $.
    $( Split an extended sum into two parts.  (Contributed by Thierry Arnoux,
       9-May-2017.) $)
    esumsplit $p |- ( ph -> sum* k e. ( A u. B ) C =
                                        ( sum* k e. A C +e sum* k e. B C ) ) $=
      ( cesum cxad co cvv wcel cmpt ctsu cun nfun unexg syl2anc cv wo cpnf cicc
      cc0 elun jaodan sylan2b cxrs cress xrge0base xrge0plusg ccmn xrge0cmn a1i
      ctmd xrge0tmd nfcv eqid fmptdf2 cres esumel wss wceq ssun1 resmptf oveq2d
      mp1i eleqtrrd ssun2 eqidd tsmssplit esumid ) ABCUAZDBDENZCDENZOPEQFEBCGHU
      BZABQRCQRVRQRIJBCQQUCUDZEUEZVRRAWCBRZWCCRZUFDUIUGUHPZRZWCBCUJAWDWGWELMUKU
      LZAVRWFBCOEVRDSZUMWFUNPZQVSVTUOUPWJUQRAURUSWJUTRAVAUSWBAEVRDWFWIFWAEWFVBW
      HWIVCVDAVSWJEBDSZTPWJWIBVEZTPABDEQFGILVFAWLWKWJTBVRVGWLWKVHABCVIEVRBDWAGV
      JVLVKVMAVTWJECDSZTPWJWICVEZTPACDEQFHJMVFAWNWMWJTCVRVGWNWMVHACBVNEVRCDWAHV
      JVLVKVMKAVRVOVPVQ $.
  $}

  ${
    $d k A $.  $d k C $.
    esummono.f $e |- F/ k ph $.
    esummono.c $e |- ( ph -> C e. V ) $.
    esummono.b $e |- ( ( ph /\ k e. C ) -> B e. ( 0 [,] +oo ) ) $.
    esummono.a $e |- ( ph -> A C_ C ) $.
    $( Extended sum is monotonic.  (Contributed by Thierry Arnoux,
       19-Oct-2017.) $)
    esummono $p |- ( ph -> sum* k e. A B <_ sum* k e. C B ) $=
      ( cesum co cle cc0 wbr cpnf wcel cvv syl2anc cxr cdif cxad cicc difexd cv
      wral simpr eldifad syldan ralrimi nfcv esumcl elxrge0 simprbi syl iccssxr
      wa ex wi ssexd sselda sselid xraddge02 mpd cun cin wceq disjdif esumsplit
      c0 a1i wss undif sylib esumeq1d eqtr3d breqtrd ) ABCEKZVRDBUAZCEKZUBLZDCE
      KZMANVTMOZVRWAMOZAVTNPUCLZQZWCAVSRQCWEQZEVSUFWFADBFHUDZAWGEVSGAEUEZVSQZWG
      AWJWIDQZWGAWJUQWIDBAWJUGUHIUIZURUJVSCEREVSUKZULSZWFVTTQZWCVTUMUNUOAVRTQWO
      WCWDUSAWETVRNPUPZABRQWGEBUFVRWEQABDFHJUTZAWGEBGAWIBQZWGAWRWKWGABDWIJVAIUI
      ZURUJBCEREBUKZULSVBAWETVTWPWNVBVRVTVCSVDABVSVEZCEKWAWBABVSCEGWTWMWQWHBVSV
      FVJVGABDVHVKWSWLVIAXADCEGABDVLXADVGJBDVMVNVOVPVQ $.
  $}

$(
  @{
    esummonof1o.1 @e |- ( ph -> A e. V ) @.
    esummonof1o.2 @e |- ( ( ph /\ k e. A ) -> B e. C ) @.
    esummonof1o.3 @e |- ( ph -> F : C --> ( 0 [,] +oo ) ) @.
    esummonof1o.4 @e |- ( ph -> G : dom G -1-1-onto-> ran ( k e. A |-> B ) ) @.
    @( Because of the way the extended sum is written, the same term can be
      counted several times. Here we provide a lower bound where each term is
      counted exactly once. @)
    esummonof1o @p |- ( ph
      -> sum* j e. dom G ( F ` ( G ` j ) ) <_ sum* k e. A ( F ` B ) ) @=
      ? @.
  @}
$)

  ${
    $d A k $.  $d B k $.  $d V k $.  $d k ph $.
    esumpad.1 $e |- ( ph -> A e. V ) $.
    esumpad.2 $e |- ( ph -> B e. W ) $.
    esumpad.3 $e |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) ) $.
    esumpad.4 $e |- ( ( ph /\ k e. B ) -> C = 0 ) $.
    $( Extend an extended sum by padding outside with zeroes.  (Contributed by
       Thierry Arnoux, 31-May-2020.) $)
    esumpad $p |- ( ph -> sum* k e. ( A u. B ) C = sum* k e. A C ) $=
      ( cun cesum cxad co wcel cvv syl wceq cc0 cdif nfv nfcv difexd c0 disjdif
      elex cin a1i cv cpnf difssd sselda wa 0e0iccpnf eqeltrdi syldan esumsplit
      cicc undif2 esumeq1 ax-mp ralrimiva esumeq2d esum0 eqtrd cxr iccssxr wral
      oveq2d esumcl syl2anc sselid xaddrid 3eqtr3d ) ABCBUAZLZDEMZBDEMZVPDEMZNO
      ZBCLZDEMZVSABVPDEAEUBZEBUCZEVPUCZABFPZBQPHBFUGRACBGIUDZBVPUHUESABCUFUIJAE
      UJZVPPZWICPZDTUKUSOZPZAVPCWIACBULUMZAWKUNDTWLKUOUPUQURVRWCSZAVQWBSWOBCUTV
      QWBDEVAVBUIAWAVSTNOZVSAVTTVSNAVTVPTEMZTAVPDTEWDADTSZEVPAWJWKWRWNKUQVCVDAV
      PQPWQTSWHVPEQWFVERVFVJAVSVGPWPVSSAWLVGVSTUKVHAWGWMEBVIVSWLPHAWMEBJVCBDEFW
      EVKVLVMVSVNRVFVO $.

    $( Remove zeroes from an extended sum.  (Contributed by Thierry Arnoux,
       5-Jun-2020.) $)
    esumpad2 $p |- ( ph -> sum* k e. ( A \ B ) C = sum* k e. A C ) $=
      ( cesum wceq cle wbr cvv wcel syl2anc cc0 cxr cdif wa nfv difssd esummono
      cun unexg cv wo cpnf cicc co elun 0e0iccpnf eqeltrdi jaodan sylan2b ssun1
      wss a1i undif1 esumeq1 ax-mp difexd sselda syldan esumpad eqtr3id breqtrd
      jca wb iccssxr wral ralrimiva nfcv esumcl sselid xrletri3 mpbird ) ABCUAZ
      DELZBDELZMZWAWBNOZWBWANOZUBZAWDWEAVTDBEFAEUCZHJABCUDZUEAWBBCUFZDELZWANABD
      WIEPWGABFQZCGQWIPQHIBCFGUGREUHZWIQAWLBQZWLCQZUIDSUJUKULZQZWLBCUMAWMWPWNJA
      WNUBDSWOKUNUOUPUQBWIUSABCURUTUEAWJVTCUFZDELZWAWQWIMWRWJMBCVAWQWIDEVBVCAVT
      CDEPGABCFHVDZIAWLVTQWMWPAVTBWLWHVEJVFZKVGVHVIVJAWATQWBTQWCWFVKAWOTWASUJVL
      ZAVTPQWPEVTVMWAWOQWSAWPEVTWTVNVTDEPEVTVOVPRVQAWOTWBXAAWKWPEBVMWBWOQHAWPEB
      JVNBDEFEBVOVPRVQWAWBVRRVS $.
  $}

  ${
    $d k A $.  $d k V $.  $d k ph $.
    esumadd.0 $e |- ( ph -> A e. V ) $.
    esumadd.1 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumadd.2 $e |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) ) $.
    $( Addition of infinite sums.  (Contributed by Thierry Arnoux,
       24-Mar-2017.) $)
    esumadd $p |- ( ph -> sum* k e. A ( B +e C ) =
                        ( sum* k e. A B +e sum* k e. A C ) ) $=
      ( cxad co cesum nfv wcel cmpt ctsu a1i fmpttd esumel eqidd nfcv cv wa cc0
      cpnf cicc ge0xaddcl syl2anc cxrs cress xrge0base xrge0plusg ccmn xrge0cmn
      cof ctmd xrge0tmd tsmsadd offval2 oveq2d eleqtrd esumid ) ABCDJKZBCELZBDE
      LZJKZEFAEMZEBUAZGAEUBBNUCCUDUEUFKZNDVINVCVINHICDUGUHAVFUIVIUJKZEBCOZEBDOZ
      JUOKZPKVJEBVCOZPKABVIJVKVJVLFVDVEUKULVJUMNAUNQVJUPNAUQQGAEBCVIHRAEBDVIIRA
      BCEFVGVHGHSABDEFVGVHGISURAVMVNVJPAEBCDJVKVLFVIVIGHIAVKTAVLTUSUTVAVB $.

    esumle.3 $e |- ( ( ph /\ k e. A ) -> B <_ C ) $.
    $( If all of the terms of an extended sums compare, so do the sums.
       (Contributed by Thierry Arnoux, 8-Jun-2017.) $)
    esumle $p |- ( ph -> sum* k e. A B <_ sum* k e. A C ) $=
      ( cesum cxad co cle cxr wcel cc0 wbr cpnf syl2anc cxne cicc esumcl sselid
      iccssxr wral ralrimiva nfcv cv wa xnegcld xaddcld wb xsubge0 mpbird pnfge
      syl w3a 0xr pnfxr elicc1 mp2an syl3anbrc a1i elicc4 syl3anc xraddge02 imp
      mpbid simpld syl21anc xaddcom breqtrd esumadd xrge0npcan esumeq2dv eqtr3d
      wceq ) ABCEKZBDCUAZLMZEKZVSLMZBDEKZNAVSVSWBLMZWCNAVSOPZWBOPZQWBNRZVSWENRZ
      AQSUBMZOVSQSUEZABFPZCWJPZEBUFVSWJPGAWMEBHUGBCEFEBUHZUCTUDZAWJOWBWKAWLWAWJ
      PZEBUFWBWJPZGAWPEBAEUIBPUJZWAOPZQWANRZWASNRZWPWRDVTWRWJODWKIUDZWRCWRWJOCW
      KHUDZUKULZWRWTCDNRZJWRDOPCOPWTXEUMXBXCDCUNTUOWRWSXAXDWAUPUQQOPZSOPZWPWSWT
      XAURUMUSUTQSWAVAVBVCZUGBWAEFWNUCTZUDZAWHWBSNRZAWQWHXKUJZXIAXFXGWGWQXLUMXF
      AUSVDXGAUTVDXJQSWBVEVFVIVJWFWGUJWHWIVSWBVGVHVKAWFWGWEWCVRWOXJVSWBVLTVMABW
      ACLMZEKWCWDABWACEFGXHHVNABXMDEWRDWJPWMXEXMDVRIHJDCVOVFVPVQVM $.
  $}

  ${
    $d a k x y A $.  $d a x y B $.  $d a x y ph $.
    gsumesum.0 $e |- F/ k ph $.
    gsumesum.1 $e |- ( ph -> A e. Fin ) $.
    gsumesum.2 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    $( Relate a group sum on ` ( RR*s |``s ( 0 [,] +oo ) ) ` to a finite
       extended sum.  (Contributed by Thierry Arnoux, 19-Oct-2017.)  (Proof
       shortened by AV, 12-Dec-2019.) $)
    gsumesum $p |- ( ph -> ( ( RR*s |`s ( 0 [,] +oo ) ) gsum ( k e. A |-> B ) )
      = sum* k e. A B ) $=
      ( vx va cfn cc0 co cgsu cxr wcel wa a1i sselid wceq syl2anc cesum cpw cin
      vy cxrs cpnf cicc cress cv cmpt crn clt csup eqidd esumval xrltso iccssxr
      nfcv xrge0base ccmn xrge0cmn ex ralrimi gsummptcl wrex pwidg elind mpteq1
      wor syl oveq2d rspceeqv eqid ovex elrnmpti sylibr cle wbr wn wral cbvmptv
      bilani cdif cxad inss2 simpr nfv nfan wel simpll wss inss1 sseli ad2antlr
      elpwid sseldd diffi adantr eldifad elxrge0 simprbi xraddge02 imp syl21anc
      adantlr adantl cres xrge00 xrge0plusg wf fmptdf cfsupp cvv wfn fnmpt c0ex
      fndmfifsupp disjdif cun undif biimpi eqcomd gsumsplit resmpt difss oveq2i
      c0 ax-mp oveq12d eqtrd breqtrrd ralrimiva r19.29r breq1 biimpar rexlimivw
      wb rnmptss sselda xrltnle con2bid mpbid supmax eqtr2d ) ABCDUAHBUBZJUCZUE
      KUFUGLZUHLZDHUIZCUJZMLZUJZUKZNULUMUUHDBCUJZMLZAHBCUUKDJEDBURFGAUUIUUFOZPZ
      UUKUNUOAUDNUUMUUOULNULVIAUPQAUUGNUUOKUFUQZAUUGDUUHBCUSUUHUTOZAVAQFACUUGOZ
      DBEADUIZBOZUUTGVBVCZVDRZAUUOUUKSHUUFVEZUUOUUMOABUUFOUUOUUOSUVEAUUEJBABJOZ
      BUUEOFBJVFVJFVGAUUOUNHBUUFUUKUUOUUOUUIBSUUJUUNUUHMDUUIBCVHVKVLTHUUFUUKUUO
      UULUULVMZUUHUUJMVNVOVPAUDUIZUUMOZPZUVHUUOVQVRZUUOUVHULVRZVSZUVJUVHUUHDIUI
      ZCUJZMLZSZIUUFVEZUVPUUOVQVRZIUUFVTZUVKUVIUVRAIUUFUVPUVHUULHIUUFUUKUVPUUIU
      VNSUUJUVOUUHMDUUIUVNCVHVKWAUUHUVOMVNVOWBUVJUVSIUUFUVJUVNUUFOZPZUVPUVPUUHD
      BUVNWCZCUJZMLZWDLZUUOVQAUWAUVPUWFVQVRZUVIAUWAPZUVPNOZUWENOZKUWEVQVRZUWGUW
      HUUGNUVPUURUWHUUGDUUHUVNCUSUUSUWHVAQZUWHUUFJUVNUUEJWEZAUWAWFRUWHUUTDUVNAU
      WADEUWADWGWHZUWHDIWIZUUTUWHUWOPZAUVBUUTAUWAUWOWJUWPUVNBUVAUWAUVNBWKZAUWOU
      WAUVNBUUFUUEUVNUUEJWLZWMWOZWNUWHUWOWFWPGTVBVCVDRUWHUUGNUWEUURUWHUUGDUUHUW
      CCUSUWLAUWCJOZUWAAUVFUWTFBUVNWQVJWRUWHUUTDUWCUWNUWHUVAUWCOZUUTUWHUXAPZAUV
      BUUTAUWAUXAWJUXBUVABUVNUWHUXAWFWSGTVBVCVDZRUWHUWEUUGOZUWKUXCUXDUWJUWKUWEW
      TXAVJUWIUWJPUWKUWGUVPUWEXBXCXDXEUWBAUWQUUOUWFSAUVIUWAWJUWAUWQUVJUWSXFAUWQ
      PZUUOUUHUUNUVNXGZMLZUUHUUNUWCXGZMLZWDLUWFUXEBUUGUVNUWCWDUUNUUHJKUSXHXIUUS
      UXEVAQAUVFUWQFWRABUUGUUNXJUWQADBCUUGUUNEGUUNVMZXKWRAUUNKXLVRUWQABUUNXMKAU
      UTDBVTUUNBXNUVCDBCUUNUUGUXJXOVJFKXMOAXPQXQWRUVNUWCUCYGSUXEUVNBXRQUWQBUVNU
      WCXSZSAUWQUXKBUWQUXKBSUVNBXTYAYBXFYCUXEUXGUVPUXIUWEWDUWQUXGUVPSAUWQUXFUVO
      UUHMDBUVNCYDVKXFUXIUWESUXEUXHUWDUUHMUWCBWKUXHUWDSBUVNYEDBUWCCYDYHYFQYIYJT
      YKYLUVRUVTPUVQUVSPZIUUFVEUVKUVQUVSIUUFYMUXLUVKIUUFUVQUVKUVSUVHUVPUUOVQYNY
      OYPVJTUVJUUONOZUVHNOZUVKUVMYQAUXMUVIUVDWRAUUMNUVHAUUKNOZHUUFVTUUMNWKAUXOH
      UUFUUQUUGNUUKUURUUQUUGDUUHUUICUSUUSUUQVAQUUQUUFJUUIUWMAUUPWFRUUQUUTDUUIAU
      UPDEUUPDWGWHUUQDHWIZUUTUUQUXPPZAUVBUUTAUUPUXPWJUXQUUIBUVAUXQUUIBUUPUUIUUE
      OAUXPUUFUUEUUIUWRWMWNWOUUQUXPWFWPGTVBVCVDRYLHUUFUUKNUULUVGYRVJYSUXMUXNPUV
      LUVKUUOUVHYTUUATUUBUUCUUD $.
  $}

  ${
    $d a k x y A $.  $d a x y B $.  $d a y X $.  $d a x y ph $.
    esumlub.f $e |- F/ k ph $.
    esumlub.0 $e |- ( ph -> A e. V ) $.
    esumlub.1 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumlub.2 $e |- ( ph -> X e. RR* ) $.
    esumlub.3 $e |- ( ph -> X < sum* k e. A B ) $.
    $( The extended sum is the lowest upper bound for the partial sums.
       (Contributed by Thierry Arnoux, 19-Oct-2017.)  (Proof shortened by AV,
       12-Dec-2019.) $)
    esumlub $p |- ( ph -> E. a e. ( ~P A i^i Fin ) X < sum* k e. a B ) $=
      ( vx clt wbr cfn cxr wcel wa simpr vy cxrs cc0 cpnf cicc co cress cv cmpt
      cgsu cpw cin wrex cesum crn csup nfcv eqidd esumval breq2d wss wb iccssxr
      wral xrge0base ccmn xrge0cmn a1i inss2 sselid nfv nfan simpll inss1 sseli
      ad2antlr elpwid sseldd syl2anc ex ralrimi gsummptcl ralrimiva rnmptss syl
      eqid supxrlub bitrd cvv ovex wceq mpteq1 oveq2d cbvmptv elrnmpti rexxfr2d
      mpbid gsumesum biimpd reximdva mpd ) AFUBUCUDUEUFZUGUFZDGUHZCUIZUJUFZNOZG
      BUKZPULZUMZFXDCDUNZNOZGXIUMAFUAUHZNOZUAMXIXCDMUHZCUIZUJUFZUIZUOZUMZXJAFBC
      DUNZNOZXTLAYBFXSQNUPZNOZXTAYAYCFNAMBCXQDEHDBUQIJAXOXIRZSZXQURUSUTAXSQVAZF
      QRYDXTVBAXQQRZMXIVDYGAYHMXIYFXBQXQUCUDVCYFXBDXCXOCVEXCVFRYFVGVHYFXIPXOXHP
      VIZAYETVJYFCXBRZDXOAYEDHYEDVKVLYFDUHZXORZYJYFYLSZAYKBRZYJAYEYLVMYMXOBYKYM
      XOBYEXOXHRAYLXIXHXOXHPVNZVOVPVQYFYLTVRJVSVTWAWBVJWCMXIXQQXRXRWFWDWEKUAXSF
      WGVSWHWQAXNXGUAGXFXSXIWIXFWIRAXDXIRZSZXCXEUJWJZVHXMXSRXMXFWKZGXIUMVBAGXIX
      FXMXRMGXIXQXFXOXDWKXPXEXCUJDXOXDCWLWMWNYRWOVHAYSSXMXFFNAYSTUTWPWQAXGXLGXI
      YQXGXLYQXFXKFNYQXDCDAYPDHYPDVKVLYQXIPXDYIAYPTVJYQYKXDRZSZAYNYJAYPYTVMUUAX
      DBYKUUAXDBYPXDXHRAYTXIXHXDYOVOVPVQYQYTTVRJVSWRUTWSWTXA $.
  $}

  ${
    $d k V $.
    esumaddf.0 $e |- F/ k ph $.
    esumaddf.a $e |- F/_ k A $.
    esumaddf.1 $e |- ( ph -> A e. V ) $.
    esumaddf.2 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumaddf.3 $e |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) ) $.
    $( Addition of infinite sums.  (Contributed by Thierry Arnoux,
       22-Jun-2017.) $)
    esumaddf $p |- ( ph -> sum* k e. A ( B +e C ) =
                        ( sum* k e. A B +e sum* k e. A C ) ) $=
      ( cxad co cesum wcel cmpt ctsu a1i eqid fmptdf2 cv wa cpnf cicc ge0xaddcl
      cc0 syl2anc cxrs cress cof xrge0base xrge0plusg ccmn xrge0cmn ctmd esumel
      xrge0tmd nfcv tsmsadd eqidd offval2f oveq2d eleqtrd esumid ) ABCDLMZBCENZ
      BDENZLMZEFGHIAEUABOUBCUFUCUDMZODVIOVEVIOJKCDUEUGAVHUHVIUIMZEBCPZEBDPZLUJM
      ZQMVJEBVEPZQMABVILVKVJVLFVFVGUKULVJUMOAUNRVJUOOAUQRIAEBCVIVKGHEVIURZJVKST
      AEBDVIVLGHVOKVLSTABCEFGHIJUPABDEFGHIKUPUSAVMVNVJQAEBCDLVKVLFVIVIGHIJKAVKU
      TAVLUTVAVBVCVD $.

    esumlef.3 $e |- ( ( ph /\ k e. A ) -> B <_ C ) $.
    $( If all of the terms of an extended sums compare, so do the sums.
       (Contributed by Thierry Arnoux, 8-Jun-2017.) $)
    esumlef $p |- ( ph -> sum* k e. A B <_ sum* k e. A C ) $=
      ( cesum co cle cxr wcel cc0 wbr cpnf cxne cxad cicc iccssxr cv ex ralrimi
      wral esumcl syl2anc sselid wa xnegcld xaddcld wb xsubge0 mpbird pnfge syl
      w3a 0xr pnfxr elicc1 mp2an syl3anbrc elicc4 syl3anc mpbid simpld syl21anc
      a1i xraddge02 wceq xaddcom breqtrd esumaddf xrge0npcan esumeq2d eqtr3d
      imp ) ABCEMZBDCUAZUBNZEMZWAUBNZBDEMZOAWAWAWDUBNZWEOAWAPQZWDPQZRWDOSZWAWGO
      SZARTUCNZPWARTUDZABFQZCWLQZEBUHWAWLQIAWOEBGAEUEBQZWOJUFUGBCEFHUIUJUKZAWLP
      WDWMAWNWCWLQZEBUHWDWLQZIAWREBGAWPWRAWPULZWCPQZRWCOSZWCTOSZWRWTDWBWTWLPDWM
      KUKZWTCWTWLPCWMJUKZUMUNZWTXBCDOSZLWTDPQCPQXBXGUOXDXEDCUPUJUQWTXAXCXFWCURU
      SRPQZTPQZWRXAXBXCUTUOVAVBRTWCVCVDVEZUFUGBWCEFHUIUJZUKZAWJWDTOSZAWSWJXMULZ
      XKAXHXIWIWSXNUOXHAVAVKXIAVBVKXLRTWDVFVGVHVIWHWIULWJWKWAWDVLVTVJAWHWIWGWEV
      MWQXLWAWDVNUJVOABWCCUBNZEMWEWFABWCCEFGHIXJJVPABXODEGAXODVMZEBGAWPXPWTDWLQ
      WOXGXPKJLDCVQVGUFUGVRVSVO $.
  $}

  ${
    $d a l n x y z A $.  $d a l n x y z B $.  $d a k l n x y V $.
    esumcst.1 $e |- F/_ k A $.
    esumcst.2 $e |- F/_ k B $.
    $( The extended sum of a constant.  (Contributed by Thierry Arnoux,
       3-Mar-2017.)  (Revised by Thierry Arnoux, 5-Jul-2017.) $)
    esumcst $p |- ( ( A e. V /\ B e. ( 0 [,] +oo ) ) ->
                                        sum* k e. A B = ( ( # ` A ) *e B ) ) $=
      ( vx wcel cc0 cpnf co wa cfn chash cxmu cxr clt wceq syl2anc wbr vy vz vn
      va vl cicc cesum cpw cin cv cfv cmpt crn csup nfel1 nfan simpl cxrs cress
      simplr cgsu cmg cmnd ctmd xrge0tmd tmdmnd ax-mp a1i inss2 simpr xrge0base
      sselid eqid gsumconstf syl3anc cn0 syl xrge0mulgnn0 eqtrd esumval wss cle
      hashcl wral wrex wi cr csn cun nn0ssre ressxr sstri pnfxr snssi unssi cvv
      wf hashf vex ffvelcdm mp2an sselii iccssxr adantr xmulcld fmpttd hashxrcl
      frnd wb elrnmpt biimpi 0xr iccgelb jca cdom inss1 sseli elpwi 3syl ssdomg
      sylc ralrimiva elin sylibr fveq2 oveq1d rspceeqv ovex adantl breq2 rspcev
      r19.29r c0 oveq2d xmul01 elrnmpti simpllr cn simp-4r c1 hashdomi xlemul1a
      syl31anc syl2anr eqbrtrd rexlimivw pwidg ancri mpan2 0elpw mpbir2an hash0
      wn crp 0fi eqeltri eqtr2di ad4antr breqtrd cdiv eqeltrd nnnn0 elind eqidd
      hashclb cmul simp-8r nnred simp-5r ltdivmul2d mpbid rpred rexmul breqtrrd
      rexlimdva2 impr rerpdivcld ishashinf ad2antlr r19.29a wex nfielex snelpwi
      arch snfi jctir hashsng eqeltrdi 0lt1 breqtrrid xmulpnf1 exlimddv adantll
      1re eqtr2d ltpnf w3o elxrge02 sylib mpjao3dan pm2.61dan supxr2 syl22anc
      ex ) ADHZBIJUFKZHZLZABCUGGAUHZMUIZGUJZNUKZBOKZULZUMZPQUNZANUKZBOKZUXHGABU
      XMCDUXEUXGCCADEUOCBUXFFUOUPEUXEUXGUQZUXEUXGCUJAHUTUXHUXKUXJHZLZURUXFUSKZC
      UXKBULVAKZUXLBUYBVBUKZKZUXMUYAUYBVCHZUXKMHZUXGUYCUYERUYFUYAUYBVDHUYFVEUYB
      VFVGVHUYAUXJMUXKUXIMVIUXHUXTVJZVLZUXEUXGUXTUTZUXKUXFUYDCUYBBFVKUYDVMVNVOU
      YAUXLVPHZUXGUYEUXMRUYAUYGUYKUYIUXKWCVQUYJUXLBVRSVSVTUXHUXOPWAUXRPHUAUJZUX
      RWBTZUAUXOWDUYLUXRQTZUYLUBUJZQTZUBUXOWEZWFZUAWGWDUXPUXRRUXHUXJPUXNUXHGUXJ
      UXMPUYAUXLBUXLPHZUYAVPJWHZWIZPUXLVPUYTPVPWGPWJWKWLJPHZUYTPWAWMJPWNVGWOWPV
      UANWQUXKWPHUXLVUAHWRGWSWPVUAUXKNWTXAXBVHZUXHBPHZUXTUXHUXFPBIJXCUXEUXGVJVL
      ZXDZXEXFXHUXHUXQBUXEUXQPHZUXGADXGXDZVUEXEUXHUYMUAUXOUXHUYLUXOHZLUYLUXMRZU
      XMUXRWBTZLZGUXJWEZUYMVUIVUJGUXJWEZVUKGUXJWDVUMUXHVUIVUNUYLWPHVUIVUNXIUAWS
      GUXJUXMUYLUXNWPUXNVMZXJVGXKUXHVUKGUXJUYAUYSVUGVUDIBWBTZLUXLUXQWBTZVUKVUCU
      XHVUGUXTVUHXDUYAVUDVUPVUFUYAIPHZVUBUXGVUPVURUYAXLVHVUBUYAWMVHUYJIJBXMVOXN
      UYAUXKAXOTZVUQUYAUXEUXKAWAZVUSUXHUXEUXTUXSXDUYAUXTUXKUXIHVUTUYHUXJUXIUXKU
      XIMXPXQUXKAXRXSUXKADXTYAUXKAUUAVQUXLUXQBUUBUUCYBVUJVUKGUXJYLUUDVULUYMGUXJ
      VULUYLUXMUXRWBVUJVUKUQVUJVUKVJUUEUUFVQYBUXHUYRUAWGUXHUYLWGHZLZUYNUYQVVBUY
      NLZAMHZUYQVVCVVDLUXRUXOHZUYNUYQVVDVVEVVCVVDAUXJHZVVEVVDAUXIHZVVDLVVFVVDVV
      GAMUUGUUHAUXIMYCYDVVFUXRUXMRGUXJWEZVVEVVFUXRUXRRVVHUXRVMGAUXJUXMUXRUXRUXK
      ARUXLUXQBOUXKANYEYFYGUUIUXRWPHVVEVVHXIUXQBOYHGUXJUXMUXRUXNWPVUOXJVGYDVQYI
      VVBUYNVVDUTUYPUYNUBUXRUXOUYOUXRUYLQYJYKSVVCVVDUUMZLZBIRZUYQBUUNHZBJRZVVJV
      VKLZIUXOHZUYLIQTZUYQVVNIUXMRGUXJWEZVVOVVNYMUXJHZIYMNUKZBOKZRVVQVVRVVNVVRY
      MUXIHYMMHAUUJUUOYMUXIMYCUUKVHVVNVVTVVSIOKZIVVNBIVVSOVVJVVKVJZYNVVSPHVWAIR
      VVSIPUULXLUUPVVSYOVGUUQGYMUXJUXMVVTIUXKYMRUXLVVSBOUXKYMNYEYFYGSGUXJUXMIUX
      NVUOUXLBOYHZYPYDVVNUYLUXRIQVVBUYNVVIVVKYQVVNUXRUXQIOKZIVVNBIUXQOVWBYNVVNV
      UGVWDIRUXHVUGVVAUYNVVIVVKVUHUURUXQYOVQVSUUSUYPVVPUBIUXOUYOIUYLQYJYKSVVJVV
      LLZUYLBUUTKZUCUJZQTZUDUJZNUKZVWGRZUDUXIWEZLZUYQUCYRVWEVWGYRHZLZVWHVWLUYQV
      WOVWHLZVWKUYQUDUXIVWPVWIUXIHZLZVWKLZVWJBOKZUXOHZUYLVWTQTZUYQVWSVWTUXMRGUX
      JWEZVXAVWSVWIUXJHVWTVWTRVXCVWSUXIMVWIVWPVWQVWKUTVWSVWJYRHZVWIMHZVWSVWJVWG
      YRVWRVWKVJZVWEVWNVWHVWQVWKYSZUVAVXDVWJVPHZVXEVWJUVBVWIWPHVXEVXHXIUDWSVWIW
      PUVEVGYDVQUVCVWSVWTUVDGVWIUXJUXMVWTVWTUXKVWIRUXLVWJBOUXKVWINYEYFYGSGUXJUX
      MVWTUXNVUOVWCYPYDVWSUYLVWGBUVFKZVWTQVWSVWHUYLVXIQTVWOVWHVWQVWKYQVWSUYLVWG
      BUXHVVAUYNVVIVVLVWNVWHVWQVWKUVGVWSVWGVXGUVHZVVJVVLVWNVWHVWQVWKUVIZUVJUVKV
      WSVWTVWGBOKZVXIVWSVWJVWGBOVXFYFVWSVWGWGHBWGHVXLVXIRVXJVWSBVXKUVLVWGBUVMSV
      SUVNUYPVXBUBVWTUXOUYOVWTUYLQYJYKSUVOUVPVWEVWHUCYRWEZVWLUCYRWDZVWMUCYRWEVW
      EVWFWGHVXMVWEUYLBUXHVVAUYNVVIVVLYSVVJVVLVJUVQVWFUCUWDVQVVIVXNVVCVVLUDAUCU
      VRUVSVWHVWLUCYRYLSUVTVVJVVMLZJUXOHZUYLJQTZUYQVXOJUXMRGUXJWEZVXPVVIVVMVXRV
      VCVVIVVMLZUEUJZAHZVXRUEVVIVYAUEUWAVVMUEAUWBXDVXSVYALZVXTWHZUXJHZJVYCNUKZB
      OKZRVXRVYAVYDVXSVYAVYCUXIHZVYCMHZLVYDVYAVYGVYHVXTAUWCVXTUWEUWFVYCUXIMYCYD
      YIVYBVYFVYEJOKZJVYBBJVYEOVVIVVMVYAUTYNVYAVYIJRZVXSVYAVYEPHIVYEQTVYJVYAVYE
      YTPVXTAUWGZWGPYTWKUWNXBUWHVYAIYTVYEQUWIVYKUWJVYEUWKSYIUWOGVYCUXJUXMVYFJUX
      KVYCRUXLVYEBOUXKVYCNYEYFYGSUWLUWMGUXJUXMJUXNVUOVWCYPYDVXOVVAVXQUXHVVAUYNV
      VIVVMYSUYLUWPVQUYPVXQUBJUXOUYOJUYLQYJYKSVVJUXGVVKVVLVVMUWQUXEUXGVVAUYNVVI
      YSBUWRUWSUWTUXAUXDYBUAUBUXOUXRUXBUXCVS $.
  $}

  ${
    $d A x $.  $d B l x $.  $d M k l x $.  $d ph k x $.
    esumsnf.0 $e |- F/_ k B $.
    esumsnf.1 $e |- ( ( ph /\ k = M ) -> A = B ) $.
    esumsnf.2 $e |- ( ph -> M e. V ) $.
    esumsnf.3 $e |- ( ph -> B e. ( 0 [,] +oo ) ) $.
    $( The extended sum of a singleton is the term.  (Contributed by Thierry
       Arnoux, 2-Jan-2017.)  (Revised by Thierry Arnoux, 2-May-2020.) $)
    esumsnf $p |- ( ph -> sum* k e. { M } A = B ) $=
      ( vx cc0 co wceq a1i cfn wcel cxr clt c0 vl csn cesum cxrs cpnf cicc cmpt
      cress ctsu cuni df-esum eqid snfi wf cop cv elsni sylan2 mpteq2dva fmptsn
      wa nfcv eqidd cbvmpt eqtr4di syl2anc eqtr4d wb fsng mpbird snssd fssd cpr
      csup wbr cif cpw cin cres cgsu crn wor xrltso 0xr cle elxrge0 sylib suppr
      simpld syl3anc 0fi reseq2 res0 eqtrdi oveq2d xrge00 gsum0 adantl wss ssid
      resmpt ax-mp xrge0base cmnd xrge0cmn cmnmnd nfv gsumsnfd sylan9eqr fmptpr
      ccmn pwsn prssi mp2an eqsstri dfss2 eqtri mpteq12i rnpropg eqtr3d supeq1d
      mpbi rneqd wn wo simprd xrlenlt mpbid jca olcd sylibr 3eqtr4rd xrge0tsmsd
      eqif unieqd unisng syl 3eqtrd ) AEUBZBDUCZUDLUEUFMZUHMZDYSBUGZUIMZUJZCUBZ
      UJZCYTUUENAYSBDUKOAUUDUUFAYSCUUCUUBPKUUBULYSPQZAEUMZOZAYSUUFUUAUUCAYSUUFU
      UCUNZUUCECUOUBZNZAUUCDYSCUGZUULADYSBCDUPZYSQAUUOENBCNUUOEUQHURUSAEFQZCUUA
      QZUULUUNNIJUUPUUQVAUULUAYSCUGUUNUAECFUUAUTDUAYSCCUACVBGUUOUAUPNCVCVDVEVFV
      GAUUPUUQUUKUUMVHIJECFUUAUUCVIVFVJACUUAJVKVLALCVMZRSVNZCLSVOZLCVPZKYSVQZPV
      RZUUBUUCKUPZVSZVTMZUGZWAZRSVNCARSWBZLRQZCRQZUUSUVANUVIAWCOUVJAWDOZAUVKLCW
      EVOZAUUQUVKUVMVAJCWFWGZWIZRLCSWHWJARUVHUURSATLUOYSCUOVMZWAZUVHUURAUVPUVGA
      UVPKTYSVMZUVFUGUVGAKTYSLCUVFPPRUUATPQZAWKOZUUJUVLJUVDTNZUVFLNAUWAUVFUUBTV
      TMLUWAUVETUUBVTUWAUVEUUCTVSTUVDTUUCWLUUCWMWNWOUUBLWPWQWNWRUVDYSNZAUVFUUBU
      UCVTMCUWBUVEUUCUUBVTUWBUVEUUCYSVSZUUCUVDYSUUCWLYSYSWSUWCUUCNYSWTDYSYSBXAX
      BWNWOABUUACDUUBEFXCUUBXDQZAUUBXKQUWDXEUUBXFXBOIJHADXGGXHXIXJKUVCUVFUVRUVF
      UVCUVBUVRUVBPWSUVCUVBNUVBUVRPEXLZUVSUUHUVRPWSWKUUITYSPXMXNXOUVBPXPYBUWEXQ
      UVFULXRVEYCAUVSUUHUVQUURNUVTUUJTYSLCPPXSVFXTYAAUUTCLNVAZUUTYDZCCNZVAZYECU
      VANAUWIUWFAUWGUWHAUVMUWGAUVKUVMUVNYFAUVJUVKUVMUWGVHUVLUVOLCYGVFYHACVCYIYJ
      UUTCLCYNYKYLYMYOAUUQUUGCNJCUUAYPYQYR $.
  $}

  ${
    $d k B $.  $d k M $.  $d k V $.  $d k ph $.
    esumsn.1 $e |- ( ( ph /\ k = M ) -> A = B ) $.
    esumsn.2 $e |- ( ph -> M e. V ) $.
    esumsn.3 $e |- ( ph -> B e. ( 0 [,] +oo ) ) $.
    $( The extended sum of a singleton is the term.  (Contributed by Thierry
       Arnoux, 2-Jan-2017.)  (Shortened by Thierry Arnoux, 2-May-2020.) $)
    esumsn $p |- ( ph -> sum* k e. { M } A = B ) $=
      ( nfcv esumsnf ) ABCDEFDCJGHIK $.
  $}

  ${
    $d A k $.  $d B k $.  $d k D $.  $d k E $.  $d k ph $.  $d k V $.
    $d k W $.
    esumpr.1 $e |- ( ( ph /\ k = A ) -> C = D ) $.
    esumpr.2 $e |- ( ( ph /\ k = B ) -> C = E ) $.
    esumpr.3 $e |- ( ph -> A e. V ) $.
    esumpr.4 $e |- ( ph -> B e. W ) $.
    esumpr.5 $e |- ( ph -> D e. ( 0 [,] +oo ) ) $.
    esumpr.6 $e |- ( ph -> E e. ( 0 [,] +oo ) ) $.
    ${
      esumpr.7 $e |- ( ph -> A =/= B ) $.
      $( Extended sum over a pair.  (Contributed by Thierry Arnoux,
         2-Jan-2017.) $)
      esumpr $p |- ( ph -> sum* k e. { A , B } C = ( D +e E ) ) $=
        ( cesum cxad wceq wcel cpr csn cun df-pr esumeq1 mp1i nfv nfcv cvv snex
        co a1i wne cin c0 disjsn2 syl cv wa cc0 cpnf cicc sylan2 adantr eqeltrd
        elsni esumsplit esumsn oveq12d 3eqtrd ) ABCUAZDFQZBUBZCUBZUCZDFQZVMDFQZ
        VNDFQZRUKEGRUKVKVOSVLVPSABCUDVKVODFUEUFAVMVNDFAFUGFVMUHFVNUHVMUITABUJUL
        VNUITACUJULABCUMVMVNUNUOSPBCUPUQAFURZVMTZUSDEUTVAVBUKZVTAVSBSDESVSBVFJV
        CAEWATVTNVDVEAVSVNTZUSDGWAWBAVSCSDGSVSCVFKVCAGWATWBOVDVEVGAVQEVRGRADEFB
        HJLNVHADGFCIKMOVHVIVJ $.
    $}

    ${
      esumpr2.1 $e |- ( ph -> ( A = B -> ( D = 0 \/ D = +oo ) ) ) $.
      $( Extended sum over a pair, with a relaxed condition compared to
         ~ esumpr .  (Contributed by Thierry Arnoux, 2-Jan-2017.) $)
      esumpr2 $p |- ( ph -> sum* k e. { A , B } C = ( D +e E ) ) $=
        ( cxad wceq adantr cpnf cpr cesum co wa csn simpr dfsn2 eqtr2id esumeq1
        preq2 3syl esumsn eqtrd cc0 oveq2 cxr wcel 0xr eleq1 mpbiri xaddrid syl
        wo cmnf wne pnfxr pnfnemnf neeq1 xaddpnf1 syl2anc 3eqtr4d jaoi syl6 imp
        id cv simpll wi eqeq2 biimprd cicc eqtr3d oveq2d 3eqtr2d adantlr esumpr
        pm2.61dane ) ABCUAZDFUBZEGQUCZRBCABCRZUDZWIEEEQUCZWJWLWIBUEZDFUBZEWLWKW
        HWNRWIWORAWKUFZWKWNBBUAWHBUGBCBUJUHWHWNDFUIUKAWOERWKADEFBHJLNULSUMAWKWM
        ERZAWKEUNRZETRZVCWQPWRWQWSWRWMEUNQUCZEEUNEQUOWREUPUQZWTERWRXAUNUPUQUREU
        NUPUSUTEVAVBUMWSETQUCZTWMEWSXAEVDVEZXBTRWSXATUPUQVFETUPUSUTWSXCTVDVEVGE
        TVDVHUTEVIVJETEQUOWSVOVKVLVMVNWLEGEQWLCUEDFUBZEGWLDEFCIWLFVPZCRZUDAXEBR
        ZDERZAWKXFVQWLXFXGWLWKXFXGVRWPWKXGXFBCXEVSVTVBVNJVJACIUQZWKMSAEUNTWAUCZ
        UQZWKNSULAXDGRWKADGFCIKMOULSWBWCWDABCVEZUDBCDEFGHIAXGXHXLJWEAXFDGRXLKWE
        ABHUQXLLSAXIXLMSAXKXLNSAGXJUQXLOSAXLUFWFWG $.
    $}
  $}

  ${
    $d A k y $.  $d B y $.  $d C k $.  $d D y $.  $d W k $.  $d k ph y $.
    esumrnmpt2.1 $e |- ( y = B -> C = D ) $.
    esumrnmpt2.2 $e |- ( ph -> A e. V ) $.
    esumrnmpt2.3 $e |- ( ( ph /\ k e. A ) -> D e. ( 0 [,] +oo ) ) $.
    esumrnmpt2.4 $e |- ( ( ph /\ k e. A ) -> B e. W ) $.
    esumrnmpt2.5 $e |- ( ( ( ph /\ k e. A ) /\ B = (/) ) -> D = 0 ) $.
    esumrnmpt2.6 $e |- ( ph -> Disj_ k e. A B ) $.
    $( Rewrite an extended sum into a sum on the range of a mapping function.
       (Contributed by Thierry Arnoux, 30-May-2020.) $)
    esumrnmpt2 $p |- ( ph -> sum* y e. ran ( k e. A |-> B ) C = sum* k e. A D )
      $=
      ( c0 wceq cvv wcel cc0 crab cmpt crn cun cesum cxad nfrab1 wss ssrab2 a1i
      wn co ssexd cv cpnf cicc sselda syldan wa csn rabid simprbi adantl wb syl
      elsng mtbird eldifd wdisj nfcv disjss1f sylc esumrnmpt cle wbr wrex velsn
      snex bilani nfre1 nfan simpllr simpr eqtr4d simp-4l simplr syl21anc eqtrd
      nfv r19.29af2 0e0iccpnf eqeltrdi nfmpt1 nfrn nfel ad2antlr sylibr elrnmpt
      vex eqid ax-mp r19.29af ex ssrdv adantr esummono 0ex esumsn breqtrd rabn0
      nfn wne biimpi necon1bi mpteq12df mpt0 eqtrdi rneqd esumeq1d esumnul 0le0
      rn0 wral mptexgf rnexg 3syl simplll adantlr syl2anc eqeltrd ralrimiva cxr
      esumcl sselid oveq1d xaddlid 3eqtr4d cin esumsplit eqtri eqbrtrdi elxrge0
      pm2.61dan jca iccssxr sselii xrletri3 mpbird simpl esumeq2d ssrind neqned
      esum0 incom necomd neneqd mtbir disjsn mpbir eqtr3i sseqtrdi ss0 mpteq12i
      nrex rabnc rabxm mptun rneqi rnun ) AGDPQZGCUAZDUBZUCZGUVJUKZGCUAZDUBZUCZ
      UDZEBUEZUVKUVOUDZFGUEZGCDUBZUCZEBUECFGUEAUVMEBUEZUVQEBUEZUFULZUVKFGUEZUVO
      FGUEZUFULZUVSUWAAUWEUWHUWFUWIABUVODEFGRIUVNGCUGZJAUVOCHKUVOCUHZAUVNGCUIUJ
      ZUMZAGUNZUVOSZUWNCSZFTUOUPULZSZAUVOCUWNUWLUQZLURZAUWOUSZDIPUTZAUWOUWPDISZ
      UWSMURZUXADUXBSZUVJUWOUVNAUWOUWPUVNUVNGCVAVBZVCUXAUXCUXEUVJVDUXDDPIVFVEVG
      VHAUWKGCDVIGUVODVIUWLOGUVOCDUWJGCVJVKVLVMZAUWFTUWEUFULZUWEAUWDTUWEUFAUWDT
      QZUWDTVNVOZTUWDVNVOZUSZAUXJUXKAUVJGCVPZUXJAUXMUSZUWDUXBEBUETVNUXNUVMEUXBB
      RUXNBWIUXBRSUXNPVRUJUXNBUNZUXBSZUSETUWQUXNUXPUXOPQZETQZUXPUXQUXNBPVQZVSUX
      NUXQUSZUVJUXRGCUXNUXQGAUXMGAGWIZUVJGCVTZWAUXQGWIWAUXRGWIUXTUWPUSZUVJUSZEF
      TUYDUXODQZEFQZUYDUXOPDUXNUXQUWPUVJWBUYCUVJWCZWDJVEUYDAUWPUVJFTQZAUXMUXQUW
      PUVJWEUXTUWPUVJWFUYGNWGWHAUXMUXQWFWJZURWKWLAUVMUXBUHUXMABUVMUXBAUXOUVMSZU
      XPAUYJUSZUYEUXPGUVKAUYJGUYAGUXOUVMGUXOVJZGUVLGUVKDWMWNWOWAZUYKUWNUVKSZUSZ
      UYEUSZUXQUXPUYPUXODPUYOUYEWCUYNUVJUYKUYEUYNUWPUVJUVJGCVAVBZWPWHUXSWQUYJUY
      EGUVKVPZAUXORSZUYJUYRVDBWSZGUVKDUXOUVLRUVLWTWRXAVSZXBXCXDZXEXFUXNETBPRUYI
      PRSZUXNXGUJTUWQSUXNWKUJXHXIAUXMUKZUSVUDUXJAVUDWCVUDUWDTTVNVUDUWDPEBUETVUD
      UVMPEBVUDBWIVUDUVMPUCPVUDUVLPVUDUVLGPDUBPVUDGUVKDPDUXMGUYBXKUXMUVKPUVKPXL
      UXMUVJGCXJXMXNDDQVUDDWTZUJXOGDXPXQXRYBXQXSBEXTXQYAUUAVEUUCAUWDUWQSZUXKAUV
      MRSZEUWQSZBUVMYCVUFAUVKRSZUVLRSVUGAUVKCHKUVKCUHAUVJGCUIUJZUMZGUVKDRUVJGCU
      GZYDUVLRYEYFZAVUHBUVMUYKUYEVUHGUVKUYMUYPEFUWQUYEUYFUYOJVCUYPAUWPUWRAUYJUY
      NUYEYGUYOUWPUYEAUYNUWPUYJAUVKCUWNVUJUQZYHXELYIYJVUAXBZYKUVMEBRBUVMVJZYMYI
      ZVUFUWDYLSZUXKUWDUUBVBVEUUDAVURTYLSZUXIUXLVDAUWQYLUWDTUOUUEZVUQYNVUSAUWQY
      LTVUTWKUUFUJUWDTUUGYIUUHYOAUWEYLSUXHUWEQAUWEUWHYLUXGAUWQYLUWHVUTAUVORSZUW
      RGUVOYCUWHUWQSUWMAUWRGUVOUWTYKUVOFGRUWJYMYIYNZYJUWEYPVEWHAUWITUWHUFULZUWH
      AUWGTUWHUFAUWGUVKTGUEZTAUVKFTGUYAAUYHGUVKAUYNUSAUWPUVJUYHAUYNUUIVUNUYNUVJ
      AUYQVCNWGYKUUJAVUIVVDTQVUKUVKGRVULUUMVEWHYOAUWHYLSVVCUWHQVVBUWHYPVEWHYQAU
      VMUVQEBABWIZVUPBUVQVJVUMAVVAUVPRSUVQRSUWMGUVODRUWJYDUVPRYEYFAUVMUVQYRZPUH
      VVFPQAVVFUXBUVQYRZPAUVMUXBUVQVUBUUKUVQUXBYRZVVGPUVQUXBUUNVVHPQPUVQSZUKVVI
      PDQZGUVOVPZVVJGUVOUWOPDUWODPUWODPUXFUULUUOUUPUVDVUCVVIVVKVDXGGUVODPUVPRUV
      PWTZWRXAUUQUVQPUURUUSUUTUVAVVFUVBVEVUOAUXOUVQSZUSZUYEVUHGUVOAVVMGUYAGUXOU
      VQUYLGUVPGUVODWMWNWOWAVVNUWOUSZUYEUSZEFUWQUYEUYFVVOJVCVVPAUWPUWRAVVMUWOUY
      EYGVVOUWPUYEAUWOUWPVVMUWSYHXELYIYJVVMUYEGUVOVPZAUYSVVMVVQVDUYTGUVODUXOUVP
      RVVLWRXAVSXBYSAUVKUVOFGUYAVULUWJVUKUWMUVKUVOYRPQAUVJGCUVEUJAUYNUWPUWRVUNL
      URUWTYSYQAUWCUVREBVVEUWCUVRQAUWCUVLUVPUDZUCUVRUWBVVRUWBGUVTDUBVVRGCDUVTDU
      VJGCUVFZVUEUVCGUVKUVODUVGYTUVHUVLUVPUVIYTUJXSACUVTFGUYACUVTQAVVSUJXSYQ $.
  $}

  ${
    $d i k n x $.  $d i n x F $.  $d i k N $.
    esumfzf.1 $e |- F/_ k F $.
    $( Formulating a partial extended sum over integers using the recursive
       sequence builder.  (Contributed by Thierry Arnoux, 18-Oct-2017.) $)
    esumfzf $p |- ( ( F : NN --> ( 0 [,] +oo ) /\ N e. NN )
      -> sum* k e. ( 1 ... N ) ( F ` k ) = ( seq 1 ( +e , F ) ` N ) ) $=
      ( vx cn wcel co c1 cfz cfv cesum cxad wceq wi nfv esumeq1d fveq2 nfcv wa
      vi vn cc0 cpnf cicc wf cv cseq caddc oveq2 eqeq12d imbi2d nffv cbvesum cz
      csn simpr fveq2d 1z a1i 1nn ffvelcdm mpan2 esumsn fzsn ax-mp esumeq1 seq1
      eqtrid 3eqtr4g cuz simpl nnuz eleqtrdi seqp1 syl adantr cun nfci nff nfan
      oveq1d fzsuc ovexd cvv cin c0 fzp1disj simplr wss fzssnn sselid ffvelcdmd
      snex velsn bilani simpll peano2nnd eqeltrd esumsplit oveq2d 3eqtrrd exp31
      3eqtr2rd a2d nnind impcom ) CFGFUCUDUEHZBUFZICJHZAUGZBKZALZCMBIUHZKZNZXII
      UAUGZJHZXLALZXQXNKZNZOXIIIJHZXLALZIXNKZNZOXIIUBUGZJHZXLALZYFXNKZNZOXIIYFI
      UIHZJHZXLALZYKXNKZNZOXIXPOUAUBCXQINZYAYEXIYPXSYCXTYDYPXRYBXLAYPAPXQIIJUJQ
      XQIXNRUKULXQYFNZYAYJXIYQXSYHXTYIYQXRYGXLAYQAPXQYFIJUJQXQYFXNRUKULXQYKNZYA
      YOXIYRXSYMXTYNYRXRYLXLAYRAPXQYKIJUJQXQYKXNRUKULXQCNZYAXPXIYSXSXMXTXOYSXRX
      JXLAYSAPXQCIJUJQXQCXNRUKULXIIUPZXLALZIBKZYCYDXIUUAYTEUGZBKZELUUBYTXLUUDAE
      XKUUCBRZEYTSAYTSEXLSZAUUCBDAUUCSUMZUNXIUUDUUBEIUOXIUUCINZTUUCIBXIUUHUQURI
      UOGZXIUSUTXIIFGZUUBXHGVAFXHIBVBVCVDVIYBYTNZYCUUANUUIUUKUSIVEVFYBYTXLAVGVF
      UUIYDUUBNUSMBIVHVFVJYFFGZXIYJYOUULXIYJYOUULXITZYJTZYNYIYKBKZMHZYHUUOMHZYM
      UUMYNUUPNZYJUUMYFIVKKZGZUURUUMYFFUUSUULXIVLZVMVNZMBIYFVOVPVQUUNYHYIUUOMUU
      MYJUQWBUUMUUQYMNYJUUMYMYGYKUPZVRZXLALYHUVCXLALZMHUUQUUMYLUVDXLAUULXIAUULA
      PZAFXHBDAUBFUVFVSAXHSVTWAZUUMUUTYLUVDNUVBIYFWCVPQUUMYGUVCXLAUVGAYGSAUVCSZ
      UUMIYFJWDUVCWEGUUMYKWNUTYGUVCWFWGNUUMIYFWHUTUUMXKYGGZTZFXHXKBUULXIUVIWIUV
      JYGFXKUUJYGFWJVAIYFWKVFUUMUVIUQWLWMUUMXKUVCGZTZFXHXKBUULXIUVKWIUVLXKYKFUV
      KXKYKNUUMAYKWOWPUVLYFUULXIUVKWQWRWSWMWTUUMUVEUUOYHMUUMUVEUVCUUDELUUOUVCXL
      UUDAEUUEEUVCSUVHUUFUUGUNUUMUUDUUOEYKFUUMUUCYKNZTUUCYKBUUMUVMUQURUUMYFUVAW
      RZUUMFXHYKBUULXIUQUVNWMVDVIXAXBVQXDXCXEXFXG $.
  $}

  ${
    $d a k n x $.  $d a n x F $.  $d k n x y $.  $d y F $.
    esumfsup.1 $e |- F/_ k F $.
    $( Formulating an extended sum over integers using the recursive sequence
       builder.  (Contributed by Thierry Arnoux, 18-Oct-2017.) $)
    esumfsup $p |- ( F : NN --> ( 0 [,] +oo )
      -> sum* k e. NN ( F ` k ) = sup ( ran seq 1 ( +e , F ) , RR* , < ) ) $=
      ( vx vn va cn c1 cxr clt wcel wbr wral wrex wceq wa cvv nfcv nfan simpr
      vy cc0 cpnf cicc co wf cxad cseq crn csup cv cfv cesum wss cle wi wfn cuz
      cr cz 1z seqfn ax-mp nnuz fneq2i mpbir iccssxr cfz esumfzf nff nfv simpll
      ovex 1nn fzssnn mp1i sseldd ffvelcdmd ex ralrimi esumcl sylancr ralrimiva
      eqeltrrd sselid fnfvrnss nnex ffvelcdm wb fvelrnb eqeq1d bitr3id rexbidva
      eqcom bitr4d biimpa a1i adantlr esummono adantr jca r19.29r breq1 biimpar
      rexlimivw 3syl cpw cfn nfesum1 nfbr simplll sylancom simplr rexrd esumlub
      ssnnssfz r19.42v simp-4l reximi sylbir sylan2 rexbii sylibr syl2anc nfel1
      cin simp-4r simp-5l simpllr inss1 sseli elpwi xrltletr reximdva rexlimdva
      vex syl3anc mpd breq2d rexxfr2d ad2antrr mpbird supxr2 syl22anc eqcomd )
      GUBUCUDUEZBUFZUGBHUHZUIZIJUJZGAUKZBULZAUMZUUGUUIIUNZUUMIKDUKZUUMUOLZDUUIM
      UUOUUMJLZUUOUAUKZJLZUAUUINZUPZDUSMUUJUUMOUUGUUHGUQZEUKZUUHULZIKZEGMUUNUVB
      UUHHURULZUQZHUTKUVGVAUGBHVBVCGUVFUUHVDVEVFZUUGUVEEGUUGUVCGKZPZUUFIUVDUBUC
      VGZUVJHUVCVHUEZUULAUMZUVDUUFABUVCCVIZUVJUVLQKZUULUUFKZAUVLMZUVMUUFKZHUVCV
      HVMZUVJUVPAUVLUUGUVIAAGUUFBCAGRZAUUFRVJZUVIAVKZSZUVJUUKUVLKZUVPUVJUWDPZGU
      UFUUKBUUGUVIUWDVLUWEUVLGUUKHGKZUVLGUNZUWEVNHUVCVOZVPUVJUWDTVQVRVSVTUVLUUL
      AQAUVLRWAZWBZWDWEWCEGIUUHWFWBUUGUUFIUUMUVKUUGGQKZUVPAGMUUMUUFKWGUUGUVPAGU
      WAUUGUUKGKZUVPGUUFUUKBWHZVSVTGUULAQUVTWAWBWEUUGUUPDUUIUUGUUOUUIKZPZUUOUVM
      OZEGNZUVMUUMUOLZEGMZPUWPUWRPZEGNUUPUWOUWQUWSUUGUWNUWQUUGUWNUVDUUOOZEGNZUW
      QUVBUWNUXBWIUUGUVHEGUUOUUHWJVPUUGUWPUXAEGUWPUVMUUOOUVJUXAUVMUUOWNUVJUVMUV
      DUUOUVNWKWLWMWOWPUUGUWSUWNUUGUWREGUVJUVLUULGAQUWCUWKUVJWGWQUUGUWLUVPUVIUW
      MWRUWFUWGUVJVNUWHVPWSWCWTXAUWPUWREGXBUWTUUPEGUWPUUPUWRUUOUVMUUMUOXCXDXEXF
      WCUUGUVADUSUUGUUOUSKZPZUUQUUTUXDUUQPZUUTUUOUVMJLZEGNZUXEUUOFUKZUULAUMZJLZ
      UXIUVMUOLZPZEGNZFGXGZXHYFZNZUXGUXEUXJFUXONZUXKEGNZFUXOMZUXPUXEGUULAQUUOFU
      XDUUQAUUGUXCAUWAUXCAVKSAUUOUUMJAUUORAJRGUULAUVTXIXJSZUWKUXEWGWQUXEUWLUUGU
      VPUUGUXCUUQUWLXKUWMXLUXEUUOUUGUXCUUQXMXNUXDUUQTXOUXEUXRFUXOUXHUXOKZUXEUXH
      UVLUNZEGNZUXRUXHEXPUXEUYCPUXEUYBPZEGNUXRUXEUYBEGXQUYDUXKEGUYDUXHUULUVLAQU
      XEUYBAUXTUYBAVKSUVOUYDUVSWQUYDUWDPZGUUFUUKBUUGUXCUUQUYBUWDXRUYEUVLGUUKUWF
      UWGVNUWHVCZUYDUWDTWEVRUXEUYBTWSXSXTYAWCUXQUXSPUXJUXRPZFUXONUXPUXJUXRFUXOX
      BUXMUYGFUXOUXJUXKEGXQYBYCYDUXEUXMUXGFUXOUXEUYAPZUXLUXFEGUYHUVIPZUUOIKUXII
      KUVMIKUXLUXFUPUYIUUOUUGUXCUUQUYAUVIYGXNUYIUUFIUXIUVKUYIUXHQKUVPAUXHMUXIUU
      FKFYPUYIUVPAUXHUYHUVIAUXEUYAAUXTAUXHUXOAUXHRZYESUWBSZUYIUUKUXHKZUVPUYIUYL
      PZGUUFUUKBUUGUXCUUQUYAUVIUYLYHUYMUXHGUUKUYMUYAUXHUXNKUXHGUNUXEUYAUVIUYLYI
      UXOUXNUXHUXNXHYJYKUXHGYLXFUYIUYLTVQVRVSVTUXHUULAQUYJWAWBWEUYIUUFIUVMUVKUY
      IUVOUVQUVRUVSUYIUVPAUVLUYKUYIUWDUVPUYIUWDPZGUUFUUKBUUGUXCUUQUYAUVIUWDYHUY
      NUVLGUUKUYFUYIUWDTWEVRVSVTUWIWBWEUUOUXIUVMYMYQYNYOYRUUGUUTUXGWIUXCUUQUUGU
      USUXFUAEUVMUUIGUUFUWJUUGUURUUIKZUVDUUROZEGNZUURUVMOZEGNUVBUYOUYQWIUUGUVHE
      GUURUUHWJVPUUGUYRUYPEGUYRUVMUUROUVJUYPUVMUURWNUVJUVMUVDUURUVNWKWLWMWOUUGU
      YRPUURUVMUUOJUUGUYRTYSYTUUAUUBVSWCDUAUUIUUMUUCUUDUUE $.

    $( Formulating an extended sum over integers using the recursive sequence
       builder.  This version is limited to real-valued functions.
       (Contributed by Thierry Arnoux, 19-Oct-2017.) $)
    esumfsupre $p |- ( F : NN --> ( 0 [,) +oo )
      -> sum* k e. NN ( F ` k ) = sup ( ran seq 1 ( + , F ) , RR* , < ) ) $=
      ( vx vy cn cc0 cpnf co wf cv cfv cxad c1 cxr clt caddc wcel wa cr crn wss
      cico cesum cseq csup cicc wceq icossicc fss mpan2 esumfsup syl cuz elnnuz
      1zzd ffvelcdm sylan2br ge0addcl adantl simprl sselid simprr rexadd eqcomd
      rge0ssre syl2anc seqfeq3 rneqd supeq1d eqtr4d ) FGHUCIZBJZFAKBLAUDZMBNUEZ
      UAZOPUFZQBNUEZUAZOPUFVMFGHUGIZBJZVNVQUHVMVLVTUBWAGHUIFVLVTBUJUKABCULUMVMO
      VSVPPVMVRVOVMDEQMVLBNVMUPDKZNUNLRVMWBFRWBBLVLRWBUOFVLWBBUQURWBVLRZEKZVLRZ
      SZWBWDQIZVLRVMWBWDUSUTVMWFSZWBTRZWDTRZWGWBWDMIZUHWHVLTWBVFVMWCWEVAVBWHVLT
      WDVFVMWCWEVCVBWIWJSWKWGWBWDVDVEVGVHVIVJVK $.
  $}

  ${
    esumss.p $e |- F/ k ph $.
    esumss.a $e |- F/_ k A $.
    esumss.b $e |- F/_ k B $.
    esumss.1 $e |- ( ph -> A C_ B ) $.
    esumss.2 $e |- ( ph -> B e. V ) $.
    esumss.3 $e |- ( ( ph /\ k e. B ) -> C e. ( 0 [,] +oo ) ) $.
    esumss.4 $e |- ( ( ph /\ k e. ( B \ A ) ) -> C = 0 ) $.
    $( Change the index set to a subset by adding zeroes.  (Contributed by
       Thierry Arnoux, 19-Jun-2017.) $)
    esumss $p |- ( ph -> sum* k e. A C = sum* k e. B C ) $=
      ( cc0 co cmpt ctsu cuni cesum wcel cxrs cpnf cicc cress cres wceq resmptf
      wss syl oveq2d xrge0base xrge00 ccmn xrge0cmn a1i ctps xrge0tps nfcv eqid
      fmptdf2 suppss2f tsmsres eqtr3d unieqd df-esum 3eqtr4g ) AUANUBUCOZUDOZEB
      DPZQOZRVHECDPZQOZRBDESCDESAVJVLAVHVKBUEZQOVJVLAVMVIVHQABCUHVMVIUFJECBDIHU
      GUIUJACVGVKVHFBNUKULVHUMTAUNUOVHUPTAUQUOKAECDVGVKGIEVGURLVKUSUTACDEFBNGIH
      MKVAVBVCVDBDEVECDEVEVF $.
  $}

  ${
    $d k A $.  $d k V $.
    esumpinfval.0 $e |- F/ k ph $.
    esumpinfval.1 $e |- ( ph -> A e. V ) $.
    esumpinfval.2 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumpinfval.3 $e |- ( ph -> E. k e. A B = +oo ) $.
    $( The value of the extended sum of nonnegative terms, with at least one
       infinite term.  (Contributed by Thierry Arnoux, 19-Jun-2017.) $)
    esumpinfval $p |- ( ph -> sum* k e. A B = +oo ) $=
      ( cesum cxr wcel cpnf cle wbr wceq cc0 syl2anc wa cvv cicc iccssxr esumcl
      co wral cv ex ralrimi nfcv sselid cif crab nfrab1 wss ssrab2 pnfxr 0lepnf
      a1i 0xr ubicc2 mp3an 0e0iccpnf ifclda eldif rabid simplbi2 con3dimp sylbi
      cdif adantl iffalsed esumss chash cxmu eqidd simprbi iftrued esumeq12dvaf
      wn cfv ssexd esumcst sylancl clt hashxrcl syl c0 wne rabn0 sylibr hashgt0
      wrex xmulpnf1 3eqtrd eqtr3d breq1 pnfge ax-mp breq2 mpbiri adantr iccgelb
      mp3an12 ifbothda esumlef eqbrtrrd xgepnf biimpd sylc ) ABCDJZKLZMXJNOZXJM
      PZAQMUAUDZKXJQMUBABELCXNLZDBUEXJXNLGAXODBFADUFZBLZXOHUGUHBCDEDBUIZUCRUJAB
      CMPZMQUKZDJZMXJNAXSDBULZXTDJZYAMAYBBXTDEFXSDBUMZXRYBBUNAXSDBUOURZGAXQSZXS
      MQXNMXNLZYFXSSQKLZMKLZQMNOYGUSUPUQQMUTVAZURQXNLYFXSVSZSZVBURVCZAXPBYBVILZ
      SXSMQYNYKAYNXQXPYBLZVSSYKXPBYBVDXQXSYOYOXQXSXSDBVEZVFVGVHVJVKVLAYCYBMDJZY
      BVMVTZMVNUDZMAYBYBXTMDFAYBVOYOXTMPAYOXSMQYOXQXSYPVPVQVJVRAYBTLZYGYQYSPAYB
      BEGYEWAZYJYBMDTYDDMUIWBWCAYRKLZQYRWDOZYSMPAYTUUBUUAYBTWEWFAYTYBWGWHZUUCUU
      AAXSDBWLUUDIXSDBWIWJYBTWKRYRWMRWNWOABXTCDEFXRGYMHXSMCNOZQCNOZXTCNOYFMQMXT
      CNWPQXTCNWPXSUUEYFXSUUEMMNOZYIUUGUPMWQWRCMMNWSWTVJYLXOUUFYFXOYKHXAYHYIXOU
      UFUSUPQMCXBXCWFXDXEXFXKXLXMXJXGXHXI $.
  $}

  ${
    $d x y A $.  $d x y F $.  $d x y V $.
    $( Lemma for ~ esumpfinval .  (Contributed by Thierry Arnoux,
       28-Jun-2017.) $)
    esumpfinvallem $p |- ( ( A e. V /\ F : A --> ( 0 [,) +oo ) ) ->
      ( CCfld gsum F ) = ( ( RR*s |`s ( 0 [,] +oo ) ) gsum F ) ) $=
      ( vx wcel cc0 cpnf co wa ccnfld cress cgsu cxrs cvv wceq cc cr caddc cxad
      a1i vy cico wf cicc fex ancoms ovexd cbs cfv wss rge0ssre ax-resscn sstri
      cnfldbas ressbas2 ax-mp cxr icossxr xrsbas eqtr3i cplusg simprl eleqtrrdi
      eqid simprr ge0addcl ovex cnfldadd ressplusg oveqi 3eltr3g syl2anc sselid
      cv simpl simpr rexadd eqcomd xrsadd 3eqtr3g ffund crn sseqtrdi gsumpropd2
      frnd cnfldex 0e0icopnf addlidd jca gsumress xrge0base xrge0plusg ressress
      addridd cin mp2an icossicc dfss mpbi eqtr4i oveq2i eqtr2i iccssxr xaddlid
      incom syl xaddrid 3eqtr4d ) ACEZAFGUBHZBUCZIZJXJKHZBLHMXJKHZBLHJBLHMFGUDH
      ZKHZBLHXLUABXMXNNNNDXKXIBNEAXJCBUEUFXLJXJKUGXLMXJKUGXMUHUIZXNUHUIZOXLXJXQ
      XRXJPUJZXJXQOXJQPUKULUMZXJPXMJXMVDZUNUOUPZXJUQUJXJXROFGURXJUQXNMXNVDZUSUO
      UPUTTXLDVNZXQEZUAVNZXQEZIIZYDXJEZYFXJEZYDYFXMVAUIZHZXQEYHYDXQXJXLYEYGVBYB
      VCZYHYFXQXJXLYEYGVEYBVCZYIYJIZYDYFRHZXJYLXQYDYFVFRYKYDYFXJNEZRYKOFGUBVGZX
      JRJXMNYAVHVIUPVJZYBVKVLYHYIYJYLYDYFXNVAUIZHZOYMYNYOYPYDYFSHZYLUUAYOYDQEZY
      FQEZYPUUBOYOXJQYDUKYIYJVOVMYOXJQYFUKYIYJVPVMUUCUUDIUUBYPYDYFVQVRVLYSSYTYD
      YFYQSYTOYRXJSMXNNYCVSVIUPVJVTVLXLAXJBXIXKVPZWAXLBWBXJXQXLAXJBUUEWEYBWCWDX
      LDAPRXJBJXMNCFUNVHYAJNEXLWFTXIXKVOZXSXLXTTUUEFXJEXLWGTZXLYDPEZIZFYDRHYDOY
      DFRHYDOUUIYDXLUUHVPZWHUUIYDUUJWNWIWJXLDAXOSXJBXPXNNCFWKWLXPXJKHZMXOXJWOZK
      HZXNXONEYQUUKUUMOFGUDVGYRXOXJMNNWMWPUULXJMKUULXJXOWOZXJXOXJXEXJXOUJZXJUUN
      OFGWQZXJXOWRWSWTXAXBXLMXOKUGUUFUUOXLUUPTUUEUUGXLYDXOEZIZFYDSHYDOZYDFSHYDO
      ZUURYDUQEZUUSUURXOUQYDFGXCXLUUQVPVMZYDXDXFUURUVAUUTUVBYDXGXFWIWJXH $.
  $}

  ${
    $d k A $.  $d k ph $.
    esumpfinval.a $e |- ( ph -> A e. Fin ) $.
    esumpfinval.b $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) ) $.
    $( The value of the extended sum of a finite set of nonnegative finite
       terms.  (Contributed by Thierry Arnoux, 28-Jun-2017.)  (Proof shortened
       by AV, 25-Jul-2019.) $)
    esumpfinval $p |- ( ph -> sum* k e. A B = sum_ k e. A B ) $=
      ( cc0 cpnf cicc co cgsu cuni cfv cfn wcel a1i sselid fmpttd cvv cha cesum
      cxrs cress cmpt ccnfld csu ctsu df-esum cordt crest xrge0base xrge00 ccmn
      csn xrge0cmn ctps xrge0tps cv wa cico icossicc eqid c0ex fsuppmptdm ctopn
      cle xrge0topn eqcomi xrhaus resthaus mp2an haustsmsid unieqd eqtrid unisn
      ovex eqtrdi wf wceq esumpfinvallem syl2anc cc cr rge0ssre ax-resscn sstri
      gsumfsum 3eqtr2d ) ABCDUAZUBGHIJZUCJZDBCUDZKJZUEWLKJZBCDUFAWIWMUNZLZWMAWI
      WKWLUGJZLWPBCDUHAWQWOABWJWLWKVFUIMZWJUJJZNGUKULWKUMOAUOPWKUPOAUQPEADBCWJA
      DURBOUSZGHUTJZWJCGHVAFQRADBWLXASCGWLVBEFGSOAVCPVDWKVEMWSVGVHWSTOZAWRTOWJS
      OXBVIGHIVPWJWRSVJVKPVLVMVNWMWKWLKVPVOVQABNOBXAWLVRWNWMVSEADBCXAFRBWLNVTWA
      ABCDEWTXAWBCXAWCWBWDWEWFFQWGWH $.
  $}

  ${
    $d k l $.  $d l A $.  $d l B $.  $d l ph $.
    esumpfinvalf.1 $e |- F/_ k A $.
    esumpfinvalf.2 $e |- F/ k ph $.
    esumpfinvalf.a $e |- ( ph -> A e. Fin ) $.
    esumpfinvalf.b $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) ) $.
    $( Same as ~ esumpfinval , minus distinct variable restrictions.
       (Contributed by Thierry Arnoux, 28-Aug-2017.)  (Proof shortened by AV,
       25-Jul-2019.) $)
    esumpfinvalf $p |- ( ph -> sum* k e. A B = sum_ k e. A B ) $=
      ( vl cc0 cpnf co cgsu ccnfld wcel a1i nfcv cvv cc wsb cesum cxrs cicc csu
      cress cmpt csn cuni ctsu df-esum cle cordt cfv crest cfn xrge0base xrge00
      ccmn xrge0cmn ctps xrge0tps cv wa cico icossicc sselid fmptdf2 fdmfifsupp
      eqid c0ex ctopn xrge0topn eqcomi xrhaus ovex resthaus mp2an unieqd eqtrid
      cha haustsmsid unisn eqtrdi wf wceq esumpfinvallem syl2anc wi cr rge0ssre
      csb ax-resscn sstri sbt sbim sban clelsb1fw anbi12i bitri wsbc wb sbcel1g
      sbf sbsbc elv imbi12i mpbi gsumfsum nfcsb1v csbeq1a cbvmptf oveq2i cbvsum
      3eqtr4g 3eqtr2d ) ABCDUAZUBJKUCLZUELZDBCUFZMLZNXSMLZBCDUDZAXPXTUGZUHZXTAX
      PXRXSUILZUHYDBCDUJAYEYCABXQXSXRUKULUMZXQUNLZUOJUPUQXRUROAUSPXRUTOAVAPGADB
      CXQXSFEDXQQADVBBOZVCZJKVDLZXQCJKVEHVFXSVIZVGZABXQXSRJYLGJROAVJPVHXRVKUMYG
      VLVMYGVTOZAYFVTOXQROYMVNJKUCVOXQYFRVPVQPWAVRVSXTXRXSMVOWBWCABUOOBYJXSWDYA
      XTWEGADBCYJXSFEDYJQHYKVGBXSUOWFWGANIBDIVBZCWKZUFZMLBYOIUDYAYBABYOIGYICSOZ
      WHZDITZAYNBOZVCZYOSOZWHZYRDIYIYJSCYJWISWJWLWMHVFWNYSYIDITZYQDITZWHUUCYIYQ
      DIWOUUDUUAUUEUUBUUDADITZYHDITZVCUUAAYHDIWPUUFAUUGYTADIFXCDIBEWQWRWSUUEYQD
      YNWTZUUBYQDIXDUUHUUBXAIDYNCSRXBXEWSXFWSXGXHXSYPNMDIBCYOEIBQICQZDYNCXIZDYN
      CXJZXKXLBCYODIUUKUUIUUJXMXNXO $.
  $}

  ${
    $d k V $.  $d k M $.
    esumpinfsum.p $e |- F/ k ph $.
    esumpinfsum.a $e |- F/_ k A $.
    esumpinfsum.1 $e |- ( ph -> A e. V ) $.
    esumpinfsum.2 $e |- ( ph -> -. A e. Fin ) $.
    esumpinfsum.3 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumpinfsum.4 $e |- ( ( ph /\ k e. A ) -> M <_ B ) $.
    esumpinfsum.5 $e |- ( ph -> M e. RR* ) $.
    esumpinfsum.6 $e |- ( ph -> 0 < M ) $.
    $( The value of the extended sum of infinitely many terms greater than one.
       (Contributed by Thierry Arnoux, 29-Jun-2017.) $)
    esumpinfsum $p |- ( ph -> sum* k e. A B = +oo ) $=
      ( cxr wcel cpnf cle wbr cc0 cesum wceq cicc co iccssxr wral cv ex ralrimi
      esumcl syl2anc sselid chash cfv cxmu clt 0xr xrltle sylancr mpd pnfge syl
      wi w3a wb pnfxr elicc1 mp2an syl3anbrc nfcv esumcst cfn wn hashinf oveq1d
      xmulpnf2 3eqtrd adantr esumlef eqbrtrrd xgepnf biimpd sylc ) ABCDUAZOPZQW
      DRSZWDQUBZATQUCUDZOWDTQUEABFPZCWHPZDBUFWDWHPIAWJDBGADUGBPZWJKUHUIBCDFHUJU
      KULABEDUAZQWDRAWLBUMUNZEUOUDZQEUOUDZQAWIEWHPZWLWNUBIAEOPZTERSZEQRSZWPMATE
      UPSZWRNATOPZWQWTWRVCUQMTEURUSUTAWQWSMEVAVBXAQOPWPWQWRWSVDVEUQVFTQEVGVHVIZ
      BEDFHDEVJVKUKAWMQEUOAWIBVLPVMWMQUBIJBFVNUKVOAWQWTWOQUBMNEVPUKVQABECDFGHIA
      WPWKXBVRKLVSVTWEWFWGWDWAWBWC $.
  $}

  ${
    $d k l n s x y z $.  $d b l m n s x y A $.  $d k m n s x y z B $.
    $d b k m n x y ph $.
    esumpcvgval.1 $e |- ( ( ph /\ k e. NN ) -> A e. ( 0 [,) +oo ) ) $.
    esumpcvgval.2 $e |- ( k = l -> A = B ) $.
    esumpcvgval.3 $e |- ( ph ->
                      ( n e. NN |-> sum_ k e. ( 1 ... n ) A ) e. dom ~~> ) $.
    $( The value of the extended sum when the corresponding series sum is
       convergent.  (Contributed by Thierry Arnoux, 31-Jul-2017.) $)
    esumpcvgval $p |- ( ph -> sum* k e. NN A = sum_ k e. NN A ) $=
      ( cn c1 cr wcel wa cc0 wceq cle wbr syl c0 vb vx vy vs vm cpw cfn cin csu
      vz cv cmpt crn cxr clt csup caddc cseq cesum wor xrltso a1i nnuz 1zzd cfv
      cpnf co weq eqcom 3imtr3i cbvmptv fmptd ffvelcdmda elrege0 simplbi serfre
      cico adantr simpr peano2nnd ffvelcdmd simprbi addge01d mpbid cuz eleqtrdi
      wf seqp1 breqtrrd wral fvmpt2 syl2anc rge0ssre sselid cfz cli cdm feqmptd
      wrex simpll elfznn adantl recnd fsumser wss adantlr ralrimiva wn elrnmpti
      fzfid sylan2 ex imp rexlimdva sylan2b simplr fsumrecl ad2antrr simprr wne
      breq1 wfn mpbir rspceeqv simpr1r 3anassrs wb w3a 0xr pnfxr mp2an mpbir2an
      elin sumeq1 wo xrlelttric mpan mpjaodan cvv cgsu eqcomd eqeltrrd isumrecl
      cc mpteq2dva eqtr2d fzssuz sseqtrri isumless eqbrtrrd brralrspcev climsup
      climrecl rexrd eqid sumex ssnnssfz reximdv rexbidv syl5ibrcom inss2 inss1
      fsumless elpwid sseldd eqeltrd r19.29an frnd 1nn ne0ii dm0rn0 fdmd eqeq1d
      bitr3id necon3bid mpbiri cz seqfn ax-mp fneq2i dffn5 mpbi r19.29 biimparc
      1z rexlimivw reximi fveq2 sylibr ad2ant2r suprub syl31anc letrd rexlimddv
      fvex lenltd ad3antrrr pnfnlt notbid mpbird simplll simpr1l syl3anbrc 3jca
      pm2.21dd elico1 simprl suprlub biimpa syl21anc wi ssriv ovex elpw 3imtr4g
      fzfi eqtr4d ssrdv ssrexv syldan syl12anc simplrl xgepnf orbi1d 0elpw sum0
      0fi eqcomi rspcev ad2antrl eqsupd nfv nfcv nnex cicc icossicc ccnfld cxrs
      breq2 elex fmpttd esumpfinvallem gsumfsum eqtr3d esumval isumclim 3eqtr4d
      cress ) AUAJUFZUGUHZUAUKZBDUIZULZUMZUNUOUPUQFJCULZKURZUMZLUOUPZJBDUSJBDUI
      ZAUBUCUNVUNVURUOUNUOUTAVAVBAVURAVUREVUPKJVCAVDZAUDEVUPKJVCVUTAUBVUOKJVCVU
      TAUBUKZJMNVVAVUOVEZOVFVQVGZMZVVBLMZAJVVCVVAVUOADJBVVCVUOGFDJCBDFVHBCPFDVH
      CBPHDUKZFUKVIBCVIVJVKZVLZVMVVDVVEOVVBQRVVBVNVOSVPZAEUKZJMZNZVVJVUPVEZVVMV
      VJKUQVGZVUOVEZUQVGZVVNVUPVEZQVVLOVVOQRZVVMVVPQRVVLVVOVVCMZVVRVVLJVVCVVNVU
      OAJVVCVUOWGVVKVVHVRVVLVVJAVVKVSZVTWAZVVSVVOLMZVVRVVOVNZWBSVVLVVMVVOAJLVVJ
      VUPVVIVMZVVLVVSVWBVWAVVSVWBVVRVWCVOSWCWDVVLVVJKWEVEZMVVQVVPPVVLVVJJVWEVVT
      VCWFZUQVUOKVVJWHSWIAVUSLMVVMVUSQRZEJWJVVMUDUKZQRZEJWJZUDLWSZABDVUOKJVCVUT
      AVVFJMZNZVWLBVVCMZVVFVUOVEBPZAVWLVSGDJBVVCVUOVVGWKWLZVWMVVCLBWMGWNZAEJKVV
      JWOVGZBDUIZULZVUPWPWQZAVUPEJVVMULZVWTAEJLVUPVVIWRAEJVVMVWSVVLVWSVVMVVLBDV
      UOKVVJVVLVVFVWRMZNZAVWLVWOAVVKVXCWTZVXCVWLVVLVVFVVJXAZXBZVWPWLVWFVXDAVWLB
      UUDMVXEVXGVWMBVWQXCZWLXDZUUAUUEUUFIUUBZUUCAVWGEJVVLVWSVVMVUSQVXIVVLVWRBDV
      UOKJVCVVLVDVVLKVVJXJVWRJXEZVVLVWRVWEJKVVJUUGVCUUHVBAVWLVWOVVKVWPXFAVWLBLM
      ZVVKVWQXFVVLVWLNVWNOBQRZAVWLVWNVVKGXFVWNVXLVXMBVNZWBZSAVUPVXAMVVKVXJVRUUI
      UUJXGUDEVVMVUSQLJUUKWLZUULZVWDUUMZUUNZAVVAVUNMZNZVVAVURQRZVURVVAUORXHVYAV
      VAKUEUKZWOVGZBDUIZQRZVYBUEJVXTAVVAVULPZUAVUJWSZVYFUEJWSZUAVUJVULVVAVUMVUM
      UUOZVUKBDUUPZXIZAVYHVYIAVYGVYIUAVUJAVUKVUJMZNZVYIVYGVULVYEQRZUEJWSZVYMAVU
      KVYDXEZUEJWSZVYPVUKUEUUQAVYRVYPAVYQVYOUEJAVYQVYOAVYQNZVYDBVUKDVYSKVYCXJAV
      VFVYDMZVXLVYQAVYTNZVWNVXLVYTAVWLVWNVVFVYCXAZGXKZVWNVXLVXMVXNVOZSZXFAVYTVX
      MVYQWUAVWNVXMWUCVXOSXFAVYQVSUVCXLUURXMXKVYGVYFVYOUEJVVAVULVYEQYAUUSUUTXNX
      MXOVYAVYCJMZVYFNZNZVVAVYEVURVYAVVALMZWUGVXTAVYHWUIVYLAVYGWUIUAVUJVYNVYGNV
      VAVULLVYNVYGVSVYNVULLMVYGVYNVUKBDVYNVUJUGVUKVUIUGUVAAVYMVSWNZVYNVVFVUKMZN
      ZVWNVXLWULAVWLVWNAVYMWUKWTWULVUKJVVFWULVUKJWULVUJVUIVUKVUIUGUVBAVYMWUKXPW
      NUVDVYNWUKVSUVEGWLZWUDSZXQVRUVFUVGXOZVRAVYELMVXTWUGAVYDBDAKVYCXJWUEXQXRAV
      URLMZVXTWUGVXRXRVYAWUFVYFXSWUHVUQLXEZVUQTXTZUJUKZVWHQRZUJVUQWJZUDLWSZVYEV
      UQMZVYEVURQRAWUQVXTWUGAJLVUPVVIUVHZXRAWURVXTWUGAWURJTXTKJUVIUVJAVUQTJTVUQ
      TPVUPWQZTPAJTPVUPUVKAWVEJTAJLVUPVVIUVLUVMUVNUVOUVPZXRAWVBVXTWUGAVWKWVBVXP
      VWJWVAUDLVWJWUTUJVUQWUSVUQMVWJWUSVVMPZEJWSZWUTEJVVMWUSVUPVUPJYBZVUPVXBPWV
      IVUPVWEYBZKUVQMWVJUWEUQVUOKUVRUVSJVWEVUPVCUVTYCEJVUPUWAUWBZVVJVUPUWOZXIVW
      JWVHNVWIWVGNZEJWSWUTVWIWVGEJUWCWVMWUTEJWVGWUTVWIWUSVVMVWHQYAUWDUWFSXOXGUW
      GSZXRAWUFWVCVXTVYFAWUFNZVYEVVMPEJWSZWVCWVOWUFVYEVYCVUPVEZPWVPAWUFVSZWVOBD
      VUOKVYCWVOVYTNZAVWLVWOAWUFVYTWTZVYTVWLWVOWUBXBZVWPWLWVOVYCJVWEWVRVCWFWVSB
      WVSVWNVXLWVSAVWLVWNWVTWWAGWLWUDSXCXDEVYCJVVMWVQVYEVVJVYCVUPUWHYDWLEJVVMVY
      EVUPWVKWVLXIUWIUWJUDUJVUQVYEUWKUWLUWMUWNVYAVVAVURWUOAWUPVXTVXRVRUWPWDAVVA
      UNMZVVAVURUORZNZNZOVVAQRZVVAUCUKZUORZUCVUNWSZVVAOUORZWWEWWFNZVVAVFPZWWIVV
      AVFUORZWWKWWLNZWWCWWIAWWDWWFWWLWWCWWBWWCWWFWWLAYEYFWWNWWCXHZVFVURUORZXHZW
      WNVURUNMZWWQAWWRWWDWWFWWLVXSUWQVURUWRSWWLWWOWWQYGWWKWWLWWCWWPVVAVFVURUOYA
      UWSXBUWTUXEWWKWWMNZAVVAVVCMZWWCWWIAWWDWWFWWMUXAWWSWWBWWFWWMWWTAWWDWWFWWMW
      WBWWBWWCWWFWWMAUXBYFWWEWWFWWMXPWWKWWMVSOUNMZVFUNMZWWTWWBWWFWWMYHYGYIYJOVF
      VVAUXFYKUXCAWWDWWFWWMWWCWWBWWCWWFWWMAYEYFAWWTWWCNZWWHUCVUQWSZWWIAWXCNZWUQ
      WURWVBYHZWUIWWCWXDWXEWUQWURWVBAWUQWXCWVDVRAWURWXCWVFVRAWVBWXCWVNVRUXDWXEV
      VCLVVAWMAWWTWWCUXGWNAWWTWWCXSWXFWUINWWCWXDUDUJUCVUQVVAUXHUXIUXJAWXDWWIAVU
      QVUNXEWXDWWIUXKAUCVUQVUNAWWGVVMPZEJWSWWGVULPUAVUJWSZWWGVUQMWWGVUNMAWXGWXH
      EJVVLWXGWXHVVLWXGNZVWRVUJMZWWGVWSPWXHWXJWXIWXJVWRVUIMZVWRUGMWXKVXKDVWRJVX
      FUXLVWRJKVVJWOUXMUXNYCKVVJUXPVWRVUIUGYMYLVBWXIWWGVVMVWSVVLWXGVSVVLVWSVVMP
      WXGVXIVRUXQUAVWRVUJVULVWSWWGVUKVWRBDYNYDWLXLXNEJVVMWWGVUPWVKWVLXIUAVUJVUL
      WWGVUMVYJVYKXIUXOUXRWWHUCVUQVUNUXSSXMUXTUYAWWKWWBWWLWWMYOZAWWBWWCWWFUYBWW
      BVFVVAQRZWWMYOZWXLWXBWWBWXNYJVFVVAYPYQWWBWXMWWLWWMVVAUYCUYDWDSYRWWJWWIWWE
      OVUNMZWWJWWIWXOOVULPUAVUJWSZTVUJMZOTBDUIZPWXPWXQTVUIMTUGMJUYEUYGTVUIUGYMY
      LWXROBDUYFUYHUATVUJVULWXROVUKTBDYNYDYKUAVUJVULOVUMVYJVYKXIYCWWHWWJUCOVUNW
      WGOVVAUOUYSUYIYQXBWWBWWFWWJYOZAWWCWXAWWBWXSYIOVVAYPYQUYJYRUYKAUAJBVULDYSA
      DUYLDJUYMJYSMAUYNVBVWMVVCOVFUYOVGZBOVFUYPGWNVYNUYQDVUKBULZYTVGZUYRWXTVUHV
      GWYAYTVGZVULVYNVUKYSMZVUKVVCWYAWGWYBWYCPVYMWYDAVUKVUJUYTXBVYNDVUKBVVCWUMV
      UAVUKWYAYSVUBWLVYNVUKBDWUJWULBWUNXCVUCVUDVUEABVURDVUOKJVCVUTVWPVXHVXQVUFV
      UG $.
  $}

  ${
    $d k M $.  $d k N $.  $d k ph $.
    esumpmono.1 $e |- ( ph -> M e. NN ) $.
    esumpmono.2 $e |- ( ph -> N e. ( ZZ>= ` M ) ) $.
    esumpmono.3 $e |- ( ( ph /\ k e. NN ) -> A e. ( 0 [,) +oo ) ) $.
    $( The partial sums in an extended sum form a monotonic sequence.
       (Contributed by Thierry Arnoux, 31-Aug-2017.) $)
    esumpmono $p |- ( ph ->
                        sum* k e. ( 1 ... M ) A <_ sum* k e. ( 1 ... N ) A ) $=
      ( c1 cfz co cesum cc0 cle wbr cpnf cxr cvv wcel cn cxad cicc iccssxr wral
      caddc ovexd cv elfznn wa cico sselid sylan2 ralrimiva nfcv esumcl syl2anc
      icossicc xrleidd cuz cfv adantr peano2nn nnuz eleqtrdi fzss1 simpr sseldd
      wss syl syldan elxrge0 simprbi wi 0xr a1i xle2add syl22anc mp2and xaddrid
      3syl wceq eqcomd cun eluzfz fzsplit esumeq1 nfv clt cin nnre ltp1d fzdisj
      c0 esumsplit eqtrd 3brtr4d ) AIDJKZBCLZMUAKZWRDIUEKZEJKZBCLZUAKZWRIEJKZBC
      LZNAWRWRNOZMXBNOZWSXCNOZAWRAMPUBKZQWRMPUCZAWQRSBXISZCWQUDWRXISAIDJUFZAXKC
      WQCUGZWQSAXMTSZXKXMDUHAXNUIMPUJKXIBMPUQHUKZULZUMWQBCRCWQUNZUOUPUKZURAXBXI
      SZXGAXARSXKCXAUDXSAWTEJUFZAXKCXAAXMXASZXNXKAYAUIZXMXDSXNYBXAXDXMYBDTSZWTI
      USUTZSXAXDVHAYCYAFVAYCWTTYDDVBVCVDWTIEVEVTAYAVFVGXMEUHVIXOVJZUMXABCRCXAUN
      ZUOUPZXSXBQSZXGXBVKVLVIAWRQSZMQSZYIYHXFXGUIXHVMXRYJAVNVOXRAXIQXBXJYGUKWRM
      WRXBVPVQVRAWSWRAYIWSWRWAXRWRVSVIWBAXEWQXAWCZBCLZXCADXDSZXDYKWAXEYLWAADYDS
      EDUSUTSYMADTYDFVCVDGDIEWDUPDIEWEXDYKBCWFVTAWQXABCACWGXQYFXLXTAYCDWTWHOWQX
      AWIWMWAFYCDDWJWKIDWTEWLVTXPYEWNWOWP $.
  $}

  ${
    $d k A $.  $d x y k C $.  $d k V $.  $d x y k ph $.
    esumcocn.j $e |- J = ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) ) $.
    esumcocn.a $e |- ( ph -> A e. V ) $.
    esumcocn.b $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumcocn.1 $e |- ( ph -> C e. ( J Cn J ) ) $.
    esumcocn.0 $e |- ( ph -> ( C ` 0 ) = 0 ) $.
    esumcocn.f $e |- ( ( ph /\ x e. ( 0 [,] +oo ) /\ y e. ( 0 [,] +oo ) ) ->
                           ( C ` ( x +e y ) ) = ( ( C ` x ) +e ( C ` y ) ) ) $.
    $( Lemma for ~ esummulc2 and co.  Composing with a continuous function
       preserves extended sums.  (Contributed by Thierry Arnoux,
       29-Jun-2017.) $)
    esumcocn $p |- ( ph -> ( C ` sum* k e. A B ) = sum* k e. A ( C ` B ) ) $=
      ( cfv wcel cc0 co xrge0base cesum nfv nfcv cv wa cpnf cicc ccn cxrs cress
      wf ctps cuni xrge0tps cle cordt crest ctopn xrge0topn eqtr4i tpsuni ax-mp
      wceq cnf syl adantr ffvelcdmd cmpt ccom ctsu ccmn xrge0cmn cmnd cxad wral
      a1i cmhm cmnmnd 3expib ralrimivv xrge0plusg xrge00 ismhm biimpri syl23anc
      w3a eqidd fmpt3d esumel tsmsmhm cofmpt oveq2d eleqtrd esumid eqcomd ) ADE
      FPZGUADEGUAZFPZADWPWRGIAGUBZGDUCZKAGUDDQZUERUFUGSZXBEFAXBXBFUKZXAAFHHUHSQ
      XCMFHHXBXBUIXBUJSZULQZXBHUMVCUNXBHXDTHUOUPPXBUQSXDURPJUSUTZVAVBZXGVDVEZVF
      LVGAWRXDFGDEVHZVIZVJSXDGDWPVHZVJSADXBFXIXDXDHHIWQTXFXFXDVKQZAVLVPZXEAUNVP
      ZXMXNAXDVMQZXOXCBUDZCUDZVNSFPXPFPXQFPVNSVCZCXBVOBXBVOZRFPRVCZFXDXDVQSQZXO
      AXLXOVLXDVRVBVPZYBXHAXRBCXBXBAXPXBQXQXBQXROVSVTNYAXOXOUEXCXSXTWFUEBCXBXBV
      NVNXDXDFRRTTWAWAWBWBWCWDWEMKAGDEXBXIAXIWGLWHADEGIWSWTKLWIWJAXJXKXDVJAGDEX
      BXBFXHLWKWLWMWNWO $.
  $}

  ${
    $d k z A $.  $d z B $.  $d k x y z C $.  $d k V $.  $d k x y z ph $.
    esummulc2.a $e |- ( ph -> A e. V ) $.
    esummulc2.b $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esummulc2.c $e |- ( ph -> C e. ( 0 [,) +oo ) ) $.
    $( An extended sum multiplied by a constant.  (Contributed by Thierry
       Arnoux, 6-Jul-2017.) $)
    esummulc1 $p |- ( ph ->
                           ( sum* k e. A B *e C ) = sum* k e. A ( B *e C ) ) $=
      ( vz cc0 co cxmu cfv wceq wcel fvmptd cvv wa simpr vx cesum cpnf cicc cle
      vy cmpt cordt crest eqid xrge0mulc1cn eqidd oveq1 cxr cico icossxr sselid
      xmul02 syl sylan9eqr 0e0iccpnf a1i w3a cxad simp2 simp3 icossicc 3ad2ant1
      cv xrge0adddir syl3anc oveq1d 3adant1 ovexd oveq12d 3eqtr4d esumcocn wral
      ge0xaddcl ralrimiva nfcv esumcl syl2anc esumeq2dv 3eqtr3d ) ABCEUBZJKUCUD
      LZJVIZDMLZUGZNBCWJNZEUBWFDMLZBCDMLZEUBAUAUFBCWJEUEUHNWGUILZFWNUJZGHAJDWJW
      NWOWJUJIUKAJKWIKWGWJWGAWJULZWHKOAWIKDMLZKWHKDMUMADUNPWQKOAKUCUOLZUNDKUCUP
      IUQDURUSUTKWGPAVAVBZWSQAUAVIZWGPZUFVIZWGPZVCZWTXBVDLZDMLZWTDMLZXBDMLZVDLZ
      XEWJNWTWJNZXBWJNZVDLXDXAXCDWGPXFXIOAXAXCVEZAXAXCVFZXDWRWGDKUCVGAXADWRPXCI
      VHUQWTXBDVJVKXDJXEWIXFWGWJRXDWJULZXDWHXEOZSWHXEDMXDXOTVLXAXCXEWGPAWTXBVSV
      MXDXEDMVNQXDXJXGXKXHVDXDJWTWIXGWGWJRXNXDWHWTOZSWHWTDMXDXPTVLXLXDWTDMVNQXD
      JXBWIXHWGWJRXNXDWHXBOZSWHXBDMXDXQTVLXMXDXBDMVNQVOVPVQAJWFWIWLWGWJRWPAWHWF
      OZSWHWFDMAXRTVLABFPCWGPZEBVRWFWGPGAXSEBHVTBCEFEBWAWBWCAWFDMVNQABWKWMEAEVI
      BPSZJCWIWMWGWJRXTWJULXTWHCOZSWHCDMXTYATVLHXTCDMVNQWDWE $.

    $( An extended sum multiplied by a constant.  (Contributed by Thierry
       Arnoux, 6-Jul-2017.) $)
    esummulc2 $p |- ( ph ->
                           ( C *e sum* k e. A B ) = sum* k e. A ( C *e B ) ) $=
      ( cesum cxmu co cxr wcel wceq cc0 cpnf sselid syl2anc xmulcom cico esumcl
      icossxr cicc iccssxr wral ralrimiva nfcv esummulc1 cv wa adantr esumeq2dv
      3eqtrd ) ADBCEJZKLZUODKLZBCDKLZEJBDCKLZEJADMNZUOMNUPUQOAPQUALMDPQUCIRZAPQ
      UDLZMUOPQUEZABFNCVBNZEBUFUOVBNGAVDEBHUGBCEFEBUHUBSRDUOTSABCDEFGHIUIABURUS
      EAEUJBNZUKZCMNUTURUSOVFVBMCVCHRAUTVEVAULCDTSUMUN $.
  $}

  ${
    $d k A $.  $d k C $.  $d k V $.  $d k ph $.
    esumdivc.a $e |- ( ph -> A e. V ) $.
    esumdivc.b $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumdivc.c $e |- ( ph -> C e. RR+ ) $.
    $( An extended sum divided by a constant.  (Contributed by Thierry Arnoux,
       6-Jul-2017.) $)
    esumdivc $p |- ( ph -> ( sum* k e. A B /e C ) = sum* k e. A ( B /e C ) ) $=
      ( cesum c1 cxdiv co cc0 cpnf wcel wceq syl3anc sselid cxr cxmu cdiv rpred
      cico wne 1red rpne0d rexdiv cioo ioorp ioossico eqsstrri rpreccld eqeltrd
      cr crp esummulc1 cicc iccssxr wral ralrimiva esumcl syl2anc xdivrec cv wa
      nfcv adantr esumeq2dv 3eqtr4d ) ABCEJZKDLMZUAMZBCVLUAMZEJVKDLMZBCDLMZEJAB
      CVLEFGHAVLKDUBMZNOUDMZAKUOPDUOPZDNUEZVLVQQAUFADIUCZADIUGZKDUHRAUPVRVQUPNO
      UIMVRUJNOUKULADIUMSUNUQAVKTPVSVTVOVMQANOURMZTVKNOUSZABFPCWCPZEBUTVKWCPGAW
      EEBHVABCEFEBVGVBVCSWAWBVKDVDRABVPVNEAEVEBPZVFZCTPVSVTVPVNQWGWCTCWDHSAVSWF
      WAVHAVTWFWBVHCDVDRVIVJ $.
  $}

  $( Lemma for ~ hasheuni .  (Contributed by Thierry Arnoux, 19-Nov-2016.) $)
  hashf2 $p |- # : _V --> ( 0 [,] +oo ) $=
    ( vx cvv cn0 cpnf csn cun chash wf cc0 cicc co wss hashf cv wcel cxr cle cz
    wbr cr nn0z zre rexr 3syl nn0ge0 elxrge0 sylanbrc ssriv pnfxr 0lepnf ubicc2
    0xr mp3an snssi ax-mp unssi fss mp2an ) BCDEZFZGHUTIDJKZLBVAGHMCUSVAACVAANZ
    COZVBPOZIVBQSVBVAOVCVBROVBTOVDVBUAVBUBVBUCUDVBUEVBUFUGUHDVAOZUSVALIPODPOIDQ
    SVEULUIUJIDUKUMDVAUNUOUPBUTVAGUQUR $.

  ${
    $d x A $.  $d x V $.
    $( The cardinality of a disjoint union, not necessarily finite. cf.
       ~ hashuni .  (Contributed by Thierry Arnoux, 19-Nov-2016.)  (Revised by
       Thierry Arnoux, 2-Jan-2017.)  (Revised by Thierry Arnoux,
       20-Jun-2017.) $)
    hasheuni $p |- ( ( A e. V /\ Disj_ x e. A x )
                                   -> ( # ` U. A ) = sum* x e. A ( # ` x ) ) $=
      ( wcel wa cfn chash cesum wceq wss nfv cc0 cpnf co wral syl wn cvv a1i c0
      cv wdisj cuni cfv w3a nfdisj1 nf3an simp2 simp3 simp1 hashunif simpl cico
      csu dfss3 cn0 hashcl cr cle nn0re nn0ge0 elrege0 sylanbrc ralimi r19.21bi
      wbr sylbi adantll esumpfinval 3adant1 eqtr4d 3adant1l 3expa uniexg notbii
      wrex rexnal bitr4i elssuni ssfi expcom con3d rexlimiv hashinf syl2an mpan
      wi vex reximi nfre1 nfan cicc wf hashf2 ffvelcdm mp2an esumpinfval sylan2
      simpr 3adant2 3adant1r pm2.61dan cpw pwfi pwuni mpan2 con3i crab cxad cun
      wtru nftru wo unrab exmid rgenw rabid2 mpbir eqtr4i esumeq1d mptru nfrab1
      rabexg cin rabnc esumsplit eqtr3id adantr c1 cdif csn cab dfrab3 wb ax-mp
      hasheq0 abbii syl2anc wne cxr df-sn ineq2i eqtri snfi inss2 difinf notrab
      eqeltri eleq1i sylnib bilani simprd biimpri necon3bi hashge1 1xr clt 0lt1
      rabid esumpinfsum oveq2d cmnf iccssxr ralrimiva esumcl sselid xrge0neqmnf
      xaddpnf1 3eqtrd adantlr ) BCDZABAUAZUBZEZBFDZBUCZGUDZBUVLGUDZAHZIZUVNUVOE
      BFJZUVTUVNUVOUWAUVTUVMUVOUWAUVTUVKUVMUVOUWAUEZUVQBUVRAUNZUVSUWBABUVMUVOUW
      AAABUVLUFUVOAKUWAAKUGUVMUVOUWAUHUVMUVOUWAUIUVMUVOUWAUJUKUVOUWAUVSUWCIUVMU
      VOUWAEBUVRAUVOUWAULUWAUVLBDZUVRLMUMNDZUVOUWAUWEABUWAUVLFDZABOZUWEABOABFUO
      ZUWFUWEABUWFUVRUPDZUWEUVLUQUWIUVRURDLUVRUSVFUWEUVRUTUVRVAUVRVBVCPVDVGVEVH
      VIVJVKVLVMUVNUVOUWAQZUVTUVKUVOUWJUVTUVMUVKUWJUVTUVOUVKUWJEUVQMUVSUVKUVPRD
      ZUVPFDZQZUVQMIZUWJBCVNZUWJUWFQZABVPZUWMUWJUWGQUWQUWAUWGUWHVOUWFABVQVRZUWP
      UWMABUWDUVLUVPJZUWPUWMWGUVLBVSUWSUWLUWFUWLUWSUWFUVPUVLVTWAWBPWCVGUVPRWDZW
      EUWJUVKUVRMIZABVPZUVSMIUWJUWQUXBUWRUWPUXAABUVLRDZUWPUXAAWHZUVLRWDWFWIVGUV
      KUXBEZBUVRACUVKUXBAUVKAKZUXAABWJWKUVKUXBULUVRLMWLNZDZUXEUWDERUXGGWMUXCUXH
      WNUXDRUXGUVLGWOWPZSUVKUXBWSWQWRVKWTXAVMXBUVKUVOQZUVTUVMUVKUXJEZUVQMUVSUVK
      UWKUWMUWNUXJUWOUWLUVOUWLUVPXCZFDZUVOUVPXDUXMBUXLJUVOBXEUXLBVTXFVGXGUWTWEU
      XKUVSUVRLIZABXHZUVRAHZUXNQZABXHZUVRAHZXINZUXPMXINZMUVKUVSUXTIUXJUVKUVSUXO
      UXRXJZUVRAHZUXTUYCUVSIXKUYBBUVRAAXLUYBBIXKUYBUXNUXQXMZABXHZBUXNUXQABXNBUY
      EIUYDABOUYDABUXNXOXPUYDABXQXRXSSXTYAUVKUXOUXRUVRAUXFUXNABYBZUXQABYBZUXNAB
      CYCZUXQABCYCZUXOUXRYDTIUVKUXNABYESUXHUVKUVLUXODZEUXISUXHUVKUVLUXRDZEUXISY
      FYGYHUXKUXSMUXPXIUXKUXRUVRAYIRUXKAKUYGUVKUXRRDUXJUYIYHUXKBUXOYJZFDZUXRFDU
      XKUXJUXOFDZUYMQUVKUXJWSUYNUXKUXOBTYKZYDZFUXOBUXNAYLZYDUYPUXNABYMUYQUYOBUY
      QUVLTIZAYLUYOUXNUYRAUXCUXNUYRYNUXDUVLRYPYOZYQATUUAXSUUBUUCUYOFDUYPUYOJUYP
      FDTUUDBUYOUUEUYOUYPVTWPUUHSBUXOUUFYRUYLUXRFUXNABUUGUUIUUJUXHUXKUYKEZUXISU
      YTUXCUVLTYSZYIUVRUSVFUXCUYTUXDSUYTUXQVUAUYTUWDUXQUYKUWDUXQEUXKUXQABUUSUUK
      UULUXNUVLTUXNUYRUYSUUMUUNPUVLRUUOYRYIYTDUXKUUPSLYIUUQVFUXKUURSUUTUVAUXKUX
      PYTDUXPUVBYSZUYAMIUXKUXGYTUXPLMUVCUXKUXORDZUXHAUXOOUXPUXGDZUVKVUCUXJUYHYH
      UXKUXHAUXOUXHUXKUYJEUXISUVDUXOUVRARUYFUVEYRZUVFUXKVUDVUBVUEUXPUVGPUXPUVHY
      RUVIVKUVJXB $.
  $}

  ${
    $d k l x y z $.  $d l m n x y z A $.  $d k l n x y B $.
    $d k l m n x y F $.  $d k n J $.  $d k l m n x y ph $.
    esumcvg.j $e |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) ) $.
    esumcvg.f $e |- F = ( n e. NN |-> sum* k e. ( 1 ... n ) A ) $.
    esumcvg.a $e |- ( ( ph /\ k e. NN ) -> A e. ( 0 [,] +oo ) ) $.
    esumcvg.m $e |- ( k = m -> A = B ) $.
    $( The sequence of partial sums of an extended sum converges to the whole
       sum. cf. ~ fsumcvg2 .  (Contributed by Thierry Arnoux, 5-Sep-2017.) $)
    esumcvg $p |- ( ph -> F ( ~~>t ` J ) sum* k e. NN A ) $=
      ( vl cpnf wcel cn wceq wa c1 cvv vx vy vz cc0 cico wral cesum clm cfv wbr
      co wrex cli csu nnuz simpr cv cc cr rge0ssre weq eleq1d adantl imp sselid
      wi adantlr cfz fzfid elfznn sylan2 esumpfinval eqtrid wf fmptd adantr cle
      cmpt simplll cicc eqidd eqcom fvmptd sylancom sylib caddc wfn ovex simpll
      elrege0 syl2anc ralrimiva nfcv esumcl sylancr cuz cz mpbir eqtrd wb mpbid
      a1i breqtrrd nnzd uzid 3syl esumeq1 syl simp-4l cfn cxr clt nfv nnex cgsu
      oveq2 simplr fmpttd breq2d reximdva wss eqid mp2an cres cxp eleq1w anbi2d
      rspce imbi12d nfan ovexd esumpinfval ctopon 0xr pnfxr 0lepnf mp3an syldan
      chvarvv wo cdm 1zzd ax-resscn sstri cbvralvw rsp sylbir mpteq2dva fvmpt2d
      fsumcl isumclim3 fsumrp0cl eqeltrd 3imtr3i simpld cseq seqfn ax-mp fneq2i
      ffnd eleqtrdi fsumser eqfnfvd eqeltrrd isumrecl simprd isumge0 lmlimxrge0
      1z sylanbrc ssid mpbird eqeltrrid esumpcvgval wn esumpmono eqtr4d cbvmptv
      peano2uz eqtr4i w3a simpr3 3anassrs peano2nnd 3brtr4d lmdvglim cpw ccnfld
      cin crn csup cxrs cress inss1 elpwid sseldd esumpfinvallem inss2 gsumfsum
      eqtr3d esumval r19.21bi nnz fveq2d rspcdv reximia ad2antrr ffvelcdmd ltle
      lmdvg esumex fvmptd3 sylibd fzssuz sseqtrri elpw fzfi elin mpbir2an sumex
      mpd sumeq1 elrnmpt1s breq2 mpan rexlimivw adantllr fsumrecl frn supxrunb1
      rexrd pm2.61dan csn reseq1i sbequ12r anbi12d fveq2 reseq2d xpeq1d eqeq12d
      wsb nfs1v simpllr elnnuz eluzfz sylanb sbequ12 mpteq12 uznnssnn fconstmpt
      sylan resmpt 3eqtr4d mpdan ex cordt crest ctopn xrge0topn letopon iccssxr
      eqtri resttopon eqeltri ubicc2 lmconst syl3anc breq1 biimprd mpan9 nnsscn
      cpm elpm2r syl22anc lmres biimpar r19.29an nfre1 eliccelico r19.30 eqeq1d
      cnex cbvrexvw orbi2i sylibr mpjaodan ) ACUDNUEUKZOZEPUFZGPBDUGZHUHUIZUJZB
      NQZDPULZAVWIRZGUMUUAZOZVWLVWOVWQRZGPBDUNZVWJVWKVWRGVWSVWKUJGVWSUMUJVWRBFD
      GSPUOVWRUUBZVWOVWQUPZVWODUQZPOZBUROZVWQVWOVXCRVWGURBVWGUSURUTUUCUUDZVWOVX
      CBVWGOZVWIVXCVXFVFZAVWIVXFDPUFVXGVXFVWHDEPDEVAZBCVWGLVBUUEVXFDPUUFUUGVCVD
      ZVEZVGVWOFUQZPOZVXKGUIZSVXKVHUKZBDUNZQVWQVWOFPVXOGURVWOGFPVXNBDUGZVRZFPVX
      OVRZJVWOFPVXPVXOVWOVXLRZVXNBDVXSSVXKVIZVWOVXBVXNOZVXFVXLVYAVWOVXCVXFVXBVX
      KVJZVXIVKVGZVLZUUHZVMVXSVXNBDVXTVXSVYARVWGURBVXEVYCVEZUUJUUIZVGUUKVWRVWSG
      HVWGIVWOPVWGGVNZVWQVWOFPVXPVWGGVXSVXPVXOVWGVYDVXSVXNBDVXTVYCUULUUMJVOZVPV
      WRVWSUSOUDVWSVQUJVWSVWGOVWRBDEPCVRZSPUOVWTVWRVXCAVXBVYJUIBQZAVWIVWQVXCVSA
      VXCRZEVXBCBPVYJUDNVTUKZVYLVYJWAEDVAZCBQZVYLVXHBCQVYNVYOLVXBEUQZWBBCWBUUNV
      CAVXCUPZKWCZWDZVWRVXCRZBUSOZUDBVQUJZVYTVXFWUAWUBRVWOVXCVXFVWQVXIVGZBWJWEZ
      UUOZVWRGWFVYJSUUPZVWPVWOGWUFQVWQVWOFPGWUFAGPWGVWIAPVYMGAFPVXPVYMGAVXLRZVX
      NTOBVYMOZDVXNUFVXPVYMOSVXKVHWHWUGWUHDVXNWUGVYARAVXCWUHAVXLVYAWIVYAVXCWUGV
      YBVCKWKWLVXNBDTDVXNWMWNWOJVOZUUTVPWUFPWGZVWOWUJWUFSWPUIZWGZSWQOWULUVIWFVY
      JSUUQUURPWUKWUFUOUUSWRXBVXSVXMVXOVXKWUFUIVYGVXSBDVYJSVXKVXSVYAAVYKAVWIVXL
      VYAVSVYAAVXCVYKVYBVYRVKWDVXSVXKPWUKVWOVXLUPUOUVAVYFUVBWSUVCVPVXAUVDZUVEVW
      RBDVYJSPUOVWTVYSWUEWUMVYTWUAWUBWUDUVFUVGVWSWJUVJVWGUVKUVHUVLVWRBCDFEWUCLV
      WRVXQVWPOZVXRVWPOZVWRVXQGVWPJVXAUVMVWOWUNWUOWTVWQVWOVXQVXRVWPVYEVBVPXAUVN
      XCVWOVWQUVOZRZGNVWJVWKWUQFGHIVWOVYHWUPVYIVPZWUQVXLRZVXPSVXKSWFUKZVHUKZBDU
      GZVXMWUTGUIVQWUSBDVXKWUTWUQVXLUPZWUSVXKWQOVXKVXKWPUIZOWUTWVDOWUSVXKWVCXDV
      XKXEVXKVXKUVSXFWUSVXCVWOVXFVWOWUPVXLVXCVSVXIWDUVPVWOVXLVXMVXPQWUPVXSVXMVX
      OVXPVYGVYDUVQVGWUSMWUTSMUQZVHUKZBDUGZWVBPGVYMGMPWVGVRZQWUSGVXQWVHJMFPWVGV
      XPMFVAWVFVXNQWVGVXPQWVEVXKSVHXPWVFVXNBDXGXHUVRUVTXBVWOWUPVXLWVEWUTQZWVGWV
      BQZVWOWUPVXLWVIUWARWVIWVFWVAQWVJVWOWUPVXLWVIUWBWVEWUTSVHXPWVFWVABDXGXFUWC
      WUSVXKWVCUWDWUSWVATOWUHDWVAUFWVBVYMOSWUTVHWHWUSWUHDWVAWUSVXBWVAOZRAVXCWUH
      AVWIWUPVXLWVKXIWVKVXCWUSVXBWUTVJVCKWKWLWVABDTDWVAWMWNWOWCUWEZVWOWUPUPZUWF
      WUQVWJUAPUWGZXJUWIZUAUQZBDUNZVRZUWJZXKXLUWKZNVWOVWJWVTQWUPVWOUAPBWVQDTVWO
      DXMDPWMPTOZVWOXNXBAVXCWUHVWIKVGVWOWVPWVOOZRZUWHDWVPBVRZXOUKZUWLVYMUWMUKZW
      WDXOUKZWVQWWCWWBWVPVWGWWDVNWWEWWGQVWOWWBUPZWWCDWVPBVWGWWCVXBWVPOZRZVWOVXC
      VXFVWOWWBWWIWIZWWJWVPPVXBWWJWVPPWWJWVOWVNWVPWVNXJUWNVWOWWBWWIXQVEUWOWWCWW
      IUPUWPZVXIWKZXRWVPWWDWVOUWQWKWWCWVPBDWWCWVOXJWVPWVNXJUWRZWWHVEWWJVWOVXCVX
      DWWKWWLVXJWKUWSUWTUXAVPWUQUBUQZUCUQZVQUJZUCWVSULZUBUSUFZWVTNQZWUQWWRUBUSW
      UQWWOUSOZRZWWOWVFBDUNZVQUJZMPULZWWRWXBWWOWVEGUIZXLUJZMPULZWXEWXBWWOVXMXLU
      JZFWVEWPUIZUFZMPULZWXHWUQWXLUBUSWUQUBMFGWURWVLWVMUXJUXBWXKWXGMPWVEPOZWXIW
      XGFWVEWXJWXMWVEWQOWVEWXJOWVEUXCWVEXEXHWXMFMVAZRZVXMWXFWWOXLWXOVXKWVEGWXMW
      XNUPUXDXSUXEUXFXHWXBWXGWXDMPWXBWXMRZWXGWWOWXFVQUJZWXDWXPWXAWXFUSOWXGWXQVF
      WUQWXAWXMXQWXPVWGUSWXFUTWXPPVWGWVEGWUQVYHWXAWXMWURUXGWXBWXMUPZUXHVEWWOWXF
      UXIWKWXPWXFWXCWWOVQWXPWXFWVGWXCWXPFWVEVXPWVGPGTJWXNVXNWVFQVXPWVGQVXKWVESV
      HXPVXNWVFBDXGXHWXRWVGTOWXPWVFBDUXKXBUXLWXPWVFBDWXPSWVEVIWXPVXBWVFOZRVWOVX
      CVXFVWOWUPWXAWXMWXSXIWXSVXCWXPVXBWVEVJVCVXIWKVLWSXSUXMXTUYAWXDWWRMPWXCWVS
      OZWXDWWRWVFWVOOZWXCTOWXTWYAWVFWVNOZWVFXJOWYBWVFPYAWVFWUKPSWVEUXNUOUXOWVFP
      SWVEVHWHUXPWRSWVEUXQWVFWVNXJUXRUXSWVFBDUXTUAWVOWVQWXCWVFWVRTWVRYBWVPWVFBD
      UYBUYCYCWWQWXDUCWXCWVSWXDUCXMWWPWXCWWOVQUYDYHUYEUYFXHWLWUQWVOXKWVRVNWVSXK
      YAWWSWWTWTWUQUAWVOWVQXKWUQWWBRZWVQWYCWVPBDWYCWVOXJWVPWWNWUQWWBUPVEWYCWWIR
      VWGUSBUTVWOWWBWWIVXFWUPWWMUYGVEUYHUYKXRWVOXKWVRUYIUBUCWVSUYJXFXAWSXCUYLAV
      WNRZGNVWJVWKAVWNGVXBWPUIZYDZWYENUYMZYEZQZDPULZGNVWKUJZAVWNWYJAVWMWYIDPVYL
      VWMWYIVYLVWMRZWYFVXQWYEYDZWYHGVXQWYEJUYNAWXMRZVWMDMVUAZRZVXQWXJYDZWXJWYGY
      EZQZVFWYLWYMWYHQZVFMDMDVAZWYPWYLWYSWYTXUAWYNVYLWYOVWMXUAWXMVXCAMDPYFYGVWM
      MDUYOUYPXUAWYQWYMWYRWYHXUAWXJWYEVXQWVEVXBWPUYQZUYRXUAWXJWYEWYGXUBUYSUYTYI
      WYPVXPNQZFWXJUFZWYSWYPXUCFWXJWYPVXKWXJOZRZVXNBDTWYPXUEDWYNWYODWYNDXMVWMDM
      VUBZYJXUEDXMYJXUFSVXKVHYKXUFVYARAVXCWUHAWXMWYOXUEVYAXIVYAVXCXUFVYBVCKWKXU
      FWVEVXNOZWYOVWMDVXNULWYPXUEWXMXUHAWXMWYOXUEVUCWXMWVEWUKOXUEXUHWVEVUDWVESV
      XKVUEVUFWDWYNWYOXUEXQVWMWYODWVEVXNXUGVWMDMVUGYHWKYLWLWYPXUDRZFWXJVXPVRZFW
      XJNVRZWYQWYRWYPWXJWXJQXUDXUJXUKQWYPWXJWAFWXJVXPWXJNVUHVUKWYPWYQXUJQZXUDWY
      PWXMWXJPYAXULAWXMWYOXQWVEVUIFPWXJVXPVULXFVPWYRXUKQXUIFWXJNVUJXBVUMVUNYSVM
      VUOXTVDAWYIWYKDPVYLWYIWYFNVWKUJZWYKVYLWYHNVWKUJZWYIXUMVYLHVYMYMUIZOZNVYMO
      ZVXBWQOXUNXUPVYLHVQVUPUIZVYMVUQUKZXUOHWWFVURUIXUSIVUSVVBXURXKYMUIOVYMXKYA
      XUSXUOOVUTUDNVVAVYMXURXKVVCYCVVDXBZXUQVYLUDXKOZNXKOZUDNVQUJZXUQYNYOYPUDNV
      VEYQXBVYLVXBVYQXDZNHVXBVYMWYEWYEYBVVFVVGWYIXUMXUNWYFWYHNVWKVVHVVIVVJVYLWY
      KXUMVYLNGHVXBVYMXUTVYLVYMTOURTOZPVYMGVNZPURYAZGVYMURVVLUKOVYLUDNVTYKXVEVY
      LVWBXBAXVFVXCWUIVPXVGVYLVVKXBVYMURPGTTVVMVVNXVDVVOVVPYRVVQYRWYDPBDTAVWNDA
      DXMVWMDPVVRYJWWAWYDXNXBAVXCWUHVWNKVGAVWNUPYLXCAVWICNQZEPULZYTZVWIVWNYTAVW
      HXVHYTZEPUFXVJAXVKEPAVYPPOZRZCVYMOZXVKVYLWUHVFXVMXVNVFDEVXHVYLXVMWUHXVNVX
      HVXCXVLADEPYFYGVXHBCVYMLVBYIKYSXVAXVBXVCXVNXVKWTYNYOYPUDNCVVSYQWEWLVWHXVH
      EPVVTXHVWNXVIVWIVWMXVHDEPVXHBCNLVWAVWCVWDVWEVWF $.
  $}

  ${
    $d i k l m n $.  $d i l m n A $.  $d k n B $.  $d k l n C $.  $d k n J $.
    $d k l n ph $.
    esumcvg2.j $e |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) ) $.
    esumcvg2.a $e |- ( ( ph /\ k e. NN ) -> A e. ( 0 [,] +oo ) ) $.
    esumcvg2.l $e |- ( k = l -> A = B ) $.
    esumcvg2.m $e |- ( k = m -> A = C ) $.
    $( Simpler version of ~ esumcvg .  (Contributed by Thierry Arnoux,
       5-Sep-2017.) $)
    esumcvg2 $p |- ( ph -> ( n e. NN |-> sum* k e. ( 1 ... n ) A )
      ( ~~>t ` J ) sum* k e. NN A ) $=
      ( vi cn c1 cv cfz cesum wceq co cmpt clm cfv cbvesumv esumeq1 syl eqtr3id
      oveq2 cbvmptv esumcvg eqbrtrrid ) AGOPGQZRUAZBESZUBNOPNQZRUAZDFSZUBZOBESH
      UCUDNGOURUOUPUMTZURUQBESZUOUQBDEFMUEUTUQUNTVAUOTUPUMPRUIUQUNBEUFUGUHUJZAB
      CEIGUSHJVBKLUKUL $.
  $}

  ${
    $d i j k $.  $d i j A $.  $d j k B $.  $d j k F $.  $d j k ph $.
    esumcvgsum.1 $e |- ( k = i -> A = B ) $.
    esumcvgsum.2 $e |- ( ( ph /\ k e. NN ) -> A e. ( 0 [,) +oo ) ) $.
    esumcvgsum.3 $e |- ( ( ph /\ k e. NN ) -> ( F ` k ) = A ) $.
    esumcvgsum.4 $e |- ( ph -> seq 1 ( + , F ) ~~> L ) $.
    esumcvgsum.5 $e |- ( ph -> L e. RR ) $.
    $( The value of the extended sum when the corresponding sum is convergent.
       (Contributed by Thierry Arnoux, 29-Oct-2019.) $)
    esumcvgsum $p |- ( ph -> sum* k e. NN A = sum_ k e. NN A ) $=
      ( vj cn c1 wcel cc0 cpnf cr cmnf cv cfz co csu cmpt caddc cseq cfv cli wa
      cdm wceq simpll elfznn adantl syl2anc cuz nnuz eleq2i bilani cico cxr clt
      cioo wbr cle wss mnfxr pnfxr 0re mnflt ax-mp pnfge icossioo mp4an sseqtri
      ioomax sselid recnd fsumser mpteq2dva wfn cz 1z seqfn wb fneq2 mpbir mpbi
      dffn5 cvv seqex a1i breldmg syl3anc eqeltrrid eqeltrd esumpcvgval ) ABCEM
      DIHAMNOMUAZUBUCZBEUDZUEMNWSUFFOUGZUHZUEZUIUKZAMNXAXCAWSNPZUJZBEFOWSXGEUAZ
      WTPZUJZAXHNPZXHFUHBULAXFXIUMZXIXKXGXHWSUNUOZJUPXFWSOUQUHZPANXNWSURUSUTXJB
      XJQRVAUCZSBXOTRVDUCZSTVBPRVBPZTQVCVEZRRVFVEZXOXPVGVHVIQSPXRVJQVKVLXQXSVIR
      VMVLTRQRVNVOVQVPXJAXKBXOPXLXMIUPVRVSVTWAAXDXBXEXBNWBZXBXDULXTXBXNWBZOWCPY
      AWDUFFOWEVLNXNULXTYAWFURNXNXBWGVLWHMNXBWJWIAXBWKPZGSPXBGUIVEXBXEPYBAUFFOW
      LWMLKXBGWKSUIWNWOWPWQWR $.
  $}

  ${
    $d A n z $.  $d B n z $.  $d k n z ph $.
    esumsup.1 $e |- ( ph -> B e. ( 0 [,] +oo ) ) $.
    esumsup.2 $e |- ( ( ph /\ k e. NN ) -> A e. ( 0 [,] +oo ) ) $.
    $( Express an extended sum as a supremum of extended sums.  (Contributed by
       Thierry Arnoux, 24-May-2020.) $)
    esumsup $p |- ( ph -> sum* k e. NN A
      = sup ( ran ( n e. NN |-> sum* k e. ( 1 ... n ) A ) , RR* , < ) ) $=
      ( cn cv cmpt cfv cesum cxad c1 cxr clt wceq wcel wa syl2anc cseq crn csup
      cfz co cc0 cpnf cicc wf fmpttd nfmpt1 esumfsup syl simpr fvmpt2 esumeq2dv
      eqid wfn cuz cz 1z seqfn ax-mp nnuz fneq2i mpbir nfcv dffn5f mpbi a1i wss
      fz1ssnn sselda simpll esumfzf sylan eqtr3d mpteq2dva eqtr4d rneqd supeq1d
      3eqtr3d ) AHDIZDHBJZKZDLZMWDNUAZUBZOPUCZHBDLEHNEIZUDUEZBDLZJZUBZOPUCAHUFU
      GUHUEZWDUIZWFWIQADHBWOGUJZDWDDHBUKZULUMAHWEBDAWCHRZSWSBWORZWEBQZAWSUNGDHB
      WOWDWDUQUOZTUPAOWHWNPAWGWMAWGEHWJWGKZJZWMWGXDQZAWGHURZXEXFWGNUSKZURZNUTRX
      HVAMWDNVBVCHXGWGVDVEVFEHWGEWGVGVHVIVJAEHWLXCAWJHRZSZWKWEDLZWLXCXJWKWEBDXJ
      WCWKRZSZWSWTXAXJWKHWCWKHVKXJWJVLVJVMZXMAWSWTAXIXLVNXNGTXBTUPAWPXIXKXCQWQD
      WDWJWRVOVPVQVRVSVTWAWB $.

    esumgect.1 $e |- ( ( ph /\ n e. NN ) -> sum* k e. ( 1 ... n ) A <_ B ) $.
    $( "Send ` n ` to ` +oo ` " in an inequality with an extended sum.
       (Contributed by Thierry Arnoux, 24-May-2020.) $)
    esumgect $p |- ( ph -> sum* k e. NN A <_ B ) $=
      ( vz cn cv cxr cle wbr wral wcel wa syl2anc ralrimiva wss cesum c1 cfz co
      cmpt crn clt csup esumsup wceq nfcv nfmpt1 nfrn nfel simpr simplll simplr
      nfv nfan eqbrtrd wrex eqid esumex elrnmpti bilani r19.29af cc0 cpnf ovexd
      wb cvv simpll fz1ssnn a1i sselda esumcl rnmptss syl iccssxr sstrdi sselid
      cicc supxrleub mpbird ) AJBDUAEJUBEKZUCUDZBDUAZUEZUFZLUGUHZCMABCDEFGUIAWJ
      CMNZIKZCMNZIWIOZAWMIWIAWLWIPZQZWLWGUJZWMEJAWOEAEUREWLWIEWLUKEWHEJWGULUMUN
      USWPWEJPZQZWQQZWLWGCMWSWQUOWTAWRWGCMNAWOWRWQUPWPWRWQUQHRUTWOWQEJVAAEJWGWL
      WHWHVBZWFBDVCVDVEVFSAWILTCLPWKWNVJAWIVGVHWBUDZLAWGXBPZEJOWIXBTAXCEJAWRQZW
      FVKPBXBPZDWFOXCXDUBWEUCVIXDXEDWFXDDKZWFPZQAXFJPXEAWRXGVLXDWFJXFWFJTXDWEVM
      VNVOGRSWFBDVKDWFUKVPRSEJWGXBWHXAVQVRVGVHVSZVTAXBLCXHFWAIWICWCRWDUT $.
  $}

  ${
    $d k A $.  $d k V $.
    esumcvgre.0 $e |- F/ k ph $.
    esumcvgre.1 $e |- ( ph -> A e. V ) $.
    esumcvgre.2 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumcvgre.3 $e |- ( ph -> sum* k e. A B e. RR ) $.
    $( All terms of a converging extended sum shall be finite.  (Contributed by
       Thierry Arnoux, 23-Sep-2019.) $)
    esumcvgre $p |- ( ( ph /\ k e. A ) -> B e. RR ) $=
      ( wcel wa cpnf wceq wn cr adantr cc0 wne wi syl wrex wral cesum nfan cicc
      cv nfre1 co adantlr simpr esumpinfval clt ltpnf gtned necom imbi2i neneqd
      wbr mpbi pm2.65da ralnex sylibr r19.21bi cmnf eliccxr xrge0neqmnf xrnemnf
      wo cxr biimpi syl2anc orcomd orcanai mpdan ) ADUFBJZKZCLMZNZCOJZAVRDBAVQD
      BUAZNVRDBUBAVTBCDUCZLMAVTKZBCDEAVTDFVQDBUGUDABEJVTGPAVOCQLUEUHJZVTHUIAVTU
      JUKWBWALWBLWARZSWBWALRZSAWDVTAWALIAWAOJWALULURIWAUMTUNPWDWEWBLWAUOUPUSUQU
      TVQDBVAVBVCVPVQVSVPVSVQVPWCVSVQVHZHWCCVIJZCVDRZWFCQLVECVFWGWHKWFCVGVJVKTV
      LVMVN $.
  $}

  ${
    $d i j k l t $.  $d A a b c j k l r s t u z $.  $d C a b c l s t u z $.
    $d B a b c i k l r s t u z $.  $d F a b c j l r s t u $.  $d W j k $.
    $d ph a b c j k l r s t u z $.
    esum2d.0 $e |- F/_ k F $.
    esum2d.1 $e |- ( z = <. j , k >. -> F = C ) $.
    esum2d.2 $e |- ( ph -> A e. V ) $.
    esum2d.3 $e |- ( ( ph /\ j e. A ) -> B e. W ) $.
    esum2d.4 $e |- ( ( ph /\ ( j e. A /\ k e. B ) ) -> C e. ( 0 [,] +oo ) ) $.
    ${
      esum2dlem.e $e |- ( ph -> A e. Fin ) $.
      $( Lemma for ~ esum2d (finite case).  (Contributed by Thierry Arnoux,
         17-May-2020.)  (Proof shortened by AV, 17-Sep-2021.) $)
      esum2dlem $p |- ( ph ->
        sum* j e. A sum* k e. B C = sum* z e. U_ j e. A ( { j } X. B ) F ) $=
        ( wceq wcel wa cvv va vb vl vt vi cv cesum csn cxp ciun cun esumeq1 nfv
        c0 iuneq1 esumeq1d eqeq12d cc0 esumnul 0iun ax-mp 3eqtr4ri a1i wss cdif
        cxad co simpr nfcsb1v nfesum2 csbeq1a esumeq12d adantl simprr cpnf cicc
        csb wral eldifad adantlr ralrimiva rspcsbela syl2anc simpll adantr wsbc
        sbcimdv sbcan sbcel1v sbcel2 anbi12i bitri vex sbcel1g 3imtr3g syl12anc
        ex wb imp nfcv esumcl esumsnf cop wrex cab wi nfeq2 nfim eqeq2d imbi12d
        opeq1 chvarfv cmpt ccnv wfun vsnid opelxpd c2nd cfv wreu c1st fvex elsn
        xp2nd xp1st sylib mpbirand eqcom bitrdi ad2antlr eqtrd syldan vsnex cin
        eqop sselda esumsplit xpexg sylancr syl syl2an2 f1mptrn csbcnv csbmpt12
        sbcfung csbopg csbvarg csbconstg opeq12d mpteq2dv cnveqd eqtr3id funeqd
        reu6i bitrd esumc nfab1 rexbidv rexsn abid 3bitr4ri eqri eqtrdi oveq12d
        elxp2 wn eldifbd disjsn sylibr simprl anassrs snssd iunxun nfxp xpeq12d
        sneq iunxsngf uneq2i iunexg wne nelne2 disjsn2 xpdisj1 iuneq2dv iunin1f
        eqtri 3syl iun0 3eqtr3g iunss1 nfiu1 nfcri nfan simp-5l simp-4r eqeltrd
        nfel simplr elsnxp biimpa adantll eliun bilani r19.29af ssiun2sf eqtrid
        r19.29af2 3eqtr4d findcard2d ) AUAUFZDEGUGZFUGZFUXJFUFZUHZDUIZUJZHBUGZQ
        UNUXKFUGZFUNUXOUJZHBUGZQZUBUFZUXKFUGZFUYBUXOUJZHBUGZQZUYBUCUFZUHZUKZUXK
        FUGZFUYIUXOUJZHBUGZQZCUXKFUGZFCUXOUJZHBUGZQUAUBUCCUXJUNQZUXLUXRUXQUXTUX
        JUNUXKFULUYQUXPUXSHBUYQBUMFUXJUNUXOUOUPUQUXJUYBQZUXLUYCUXQUYEUXJUYBUXKF
        ULUYRUXPUYDHBUYRBUMFUXJUYBUXOUOUPUQUXJUYIQZUXLUYJUXQUYLUXJUYIUXKFULUYSU
        XPUYKHBUYSBUMFUXJUYIUXOUOUPUQUXJCQZUXLUYNUXQUYPUXJCUXKFULUYTUXPUYOHBUYT
        BUMFUXJCUXOUOUPUQUYAAUNHBUGZURUXTUXRBHUSUXSUNQUXTVUAQFUXOUTUXSUNHBULVAF
        UXKUSVBVCAUYBCVDZUYGCUYBVEZRZSZSZUYFUYMVUFUYFSZUYCUYHUXKFUGZVFVGZUYEUYH
        FUYGDVQZUIZHBUGZVFVGZUYJUYLVUGUYCUYEVUHVULVFVUFUYFVHVUFVUHVULQUYFVUFVUH
        VUJFUYGEVQZGUGZVULVUFUXKVUOFUYGVUCFVUJVUNGFUYGDVIZFUYGEVIZVJUXMUYGQZUXK
        VUOQVUFVURDVUJEVUNGFUYGDVKZFUYGEVKZVLVMAVUBVUDVNZVUFVUJJRZVUNURVOVPVGZR
        ZGVUJVRVUOVVCRVUFUYGCRZDJRZFCVRVVBVUFUYGCUYBVVAVSZVUFVVFFCAUXMCRZVVFVUE
        NVTZWAFUYGCDJWBWCZVUFVVDGVUJVUFGUFZVUJRZSZAVVEVVLVVDAVUEVVLWDVUFVVEVVLV
        VGWEVUFVVLVHZAVVEVVLSZVVDAVVHVVKDRZSZFUYGWFZEVVCRZFUYGWFZVVOVVDAVVQVVSF
        UYGAVVQVVSOWQWGVVRVVHFUYGWFZVVPFUYGWFZSVVOVVHVVPFUYGWHVWAVVEVWBVVLFUYGC
        WIZFUYGVVKDWJWKWLUYGTRZVVTVVDWRUCWMZFUYGEVVCTWNVAWOWSWPZWAVUJVUNGJGVUJW
        TZXAWCXBVUFVUOUDUFZUYGVVKXCZQZGVUJXDZUDXEZHBUGZVULVUFBUDVUJVUNVWIHGJVUK
        KVUFGUMVWGBUFZUXMVVKXCZQZHEQZXFVWNVWIQZHVUNQZXFFUCVWRVWSFVWRFUMFHVUNVUQ
        XGXHVURVWPVWRVWQVWSVURVWOVWIVWNUXMUYGVVKXKXIVUREVUNHVUTXIXJLXLVVJAVUEVV
        EGVUJVWIXMZXNZXOZVVGAVVEVXBAVWAGDVWOXMZXNZXOZFUYGWFZVVEVXBAVVHVXEFUYGAV
        VHVXEAVVHSZGBDVWOUXOVXGVVPSZUXMVVKUXNDUXMUXNRVXHFXPVCVXGVVPVHXQVWNUXORZ
        VWNXRXSZDRVXGVWPVVKVXJQZWRZGDVRVWPGDXTVWNUXNDYDVXGVXISVXLGDVXIVXLVXGVVP
        VXIVWPVXJVVKQZVXKVXIVWPVWNYAXSZUXMQZVXMVXIVXNUXNRVXOVWNUXNDYEVXNUXMVWNY
        AYBYCYFVWNUXMVVKUXNDYOYGVXJVVKYHYIYJWAVWPGDVXJUUNUUAUUBWQWGVWCVWDVXFVXB
        WRVWEVWDVXFFUYGVXDVQZXOVXBFUYGVXDTUUEVWDVXPVXAVWDVXPFUYGVXCVQZXNVXAFUYG
        VXCUUCVWDVXQVWTVWDVXQGVUJFUYGVWOVQZXMVWTFGUYGTDVWOUUDVWDGVUJVXRVWIVWDVX
        RFUYGUXMVQZFUYGVVKVQZXCVWIFUYGUXMVVKTUUFVWDVXSUYGVXTVVKFUYGTUUGFUYGVVKT
        UUHUUIYKUUJYKUUKUULUUMUUOVAWOWSYLVWFVVMUYGVVKUYHVUJUYGUYHRVVMUCXPVCVVNX
        QUUPVWLVUKQVWMVULQUDVWLVUKVWKUDUUQUDVUKWTVWHUEUFZVVKXCZQZGVUJXDZUEUYHXD
        VWKVWHVUKRVWHVWLRVYDVWKUEUYGVWEVYAUYGQZVYCVWJGVUJVYEVYBVWIVWHVYAUYGVVKX
        KXIUURUUSUEGVWHUYHVUJUVEVWKUDUUTUVAUVBVWLVUKHBULVAUVCYKWEUVDVUFUYJVUIQU
        YFVUFUYBUYHUXKFVUFFUMFUYBWTFUYHWTZUYBTRZVUFUBWMZVCUYHTRZVUFUCYMZVCVUFUY
        GUYBRUVFZUYBUYHYNUNQVUFUYGCUYBVVAUVGZUYBUYGUVHUVIVUFUXMUYBRZSZAVVHUXKVV
        CRZAVUEVYMWDVUFUYBCUXMAVUBVUDUVJZYPZVXGVVFVVSGDVRVYONVXGVVSGDAVVHVVPVVS
        OUVKWADEGJGDWTXAWCZWCVUFUXMUYHRZSAVVHVYOAVUEVYSWDVUFUYHCUXMVUFUYGCVVGUV
        LYPVYRWCYQWEVUFUYLVUMQUYFVUFUYLUYDVUKUKZHBUGZVUMUYKVYTQUYLWUAQUYKUYDFUY
        HUXOUJZUKVYTFUYBUYHUXOUVMWUBVUKUYDVWDWUBVUKQVWEFUYGUXOVUKTFUYHVUJVYFVUP
        UVNZVURUXNUYHDVUJUXMUYGUVPVUSUVOZUVQVAUVRUWFUYKVYTHBULVAVUFUYDVUKHBVUFB
        UMBUYDWTBVUKWTVUFVYGUXOTRZFUYBVRUYDTRVYHVUFWUEFUYBVYNUXNTRVVFWUEFYMVUFV
        YMVVHVVFVYQVVIYLUXNDTJYRYSWAFUYBUXOTTUVSYSVUFVYIVVBVUKTRVYJVVJUYHVUJTJY
        RYSVUFFUYBUXOVUKYNZUJFUYBUNUJUYDVUKYNUNVUFFUYBWUFUNVYNUXMUYGUVTZUXNUYHY
        NUNQWUFUNQVYNVYMVYKWUGVUFVYMVHVUFVYKVYMVYLWEUXMUYGUYBUWAWCUXMUYGUWBUXNU
        YHDVUJUWCUWGUWDFUYBUXOVUKWUCUWEFUYBUWHUWIVUFVWNUYDRZSAVWNUYORZHVVCRZAVU
        EWUHWDVUFUYDUYOVWNVUFVUBUYDUYOVDVYPFUYBCUXOUWJYTYPAWUISZVXIWUJFCAWUIFAF
        UMFBUYOFCUXOUWKUWLUWMWUKVVHSVXISZVWPWUJGDWULGUMGHVVCKGVVCWTUWQWULVVPSZV
        WPSZHEVVCVWPVWQWUMLVMWUNAVVHVVPVVSAWUIVVHVXIVVPVWPUWNWUKVVHVXIVVPVWPUWO
        WULVVPVWPUWROWPUWPVVHVXIVWPGDXDZWUKVVHVXIWUOGDCUXMVWNUWSUWTUXAUXGWUIVXI
        FCXDAFVWNCUXOUXBUXCUXDZWCVUFVWNVUKRZSAWUIWUJAVUEWUQWDVUFVUKUYOVWNVUFVVE
        VUKUYOVDVVGFCUXOUYGVUKFCWTFUYGWTWUCWUDUXEYTYPWUPWCYQUXFWEUXHWQPUXI $.
    $}

    $( Write a double extended sum as a sum over a two-dimensional region.
       Note that ` B ( j ) ` is a function of ` j ` .  This can be seen as
       "slicing" the relation ` A ` .  (Contributed by Thierry Arnoux,
       17-May-2020.) $)
    esum2d $p |- ( ph ->
      sum* j e. A sum* k e. B C = sum* z e. U_ j e. A ( { j } X. B ) F ) $=
      ( vc cxr clt wa wcel va vs vt vr vu cpw cfn cin cxrs cc0 cpnf co cress cv
      cicc cesum cmpt cgsu crn csup csn cxp ciun wor xrltso a1i wn wral wrex wi
      wbr wceq nfv nfcv nfmpt1 nfrn nfel nfan cle wss xrge0base xrge0cmn elin2d
      simpr simpll elin1d adantr sylib sseldd simp-5l simplr syl12anc r19.29af2
      elpw eqeltrd biimpa bilani r19.29af syl2anc ralrimiva gsummptcl ad3antrrr
      sselid eqid syl simpllr esumcl esumgsum adantlr esummono eqbrtrrd eqbrtrd
      cvv xrlenlt syl21anc ovex elrnmpti breq2d rspcedvd 3anassrs ex jca breq1d
      nfbr notbid ralbidv elpwi sselda adantrr eqidd esumval sstrd iunss sylibr
      cdm mpbir oveq2d ralrimi adantllr cima iccssxr ccmn vex nfiu1 cop simp-4r
      adantl elsnxp adantll eliun rnmptss vsnex sylancr iunexg elrnmpt1 nfesum1
      xpexg nfrexw ad2antrr 3ad2antr3 esumlub imbi1d anbi12d rspcedv mpd simprr
      supcl esum2dlem anassrs eqtr3d iunss1 wb mpbid mtbid mpbird nfel1 simpr1l
      nfsup w3a simpr1r breqtrd dmss dmiun sseqtrdi dmxpss snssi rgen dmex 3syl
      sstrdi dmfi elind mpteq1 elrnmpt1s nfov simp-4l nfpw nfin wrel xpss rgenw
      df-rel gsummpt2d imass1 iunsnima sseqtrd imaexg ax-mp mpan esumlef imafi2
      id mpteq2da eqtrd 3brtr3d xrltletrd biimpi ad2antlr suplub breq2 cbvrexvw
      imp r19.29a eqsupd 3eqtr4d ) AUACUFZUGUHZUIUJUKUOULZUMULZFUAUNZDEGUPZUQZU
      RULZUQZUSZQRUTPFCFUNZVAZDVBZVCZUFZUGUHZUYIBPUNZHUQZURULZUQZUSZQRUTZCUYKFU
      PUYSHBUPZAUBUCQUYOVUGRQRVDAVEVFZAUDUBUCQVUFRVUIAVUHUBUNZRVKZVGZUBVUFVHZVU
      JVUHRVKZVUJUCUNZRVKZUCVUFVIZVJZUBQVHZSZUDUNZVUJRVKZVGZUBVUFVHZVUJVVARVKZV
      UQVJZUBQVHZSZUDQVIAVUMVUSAVULUBVUFAVUJVUFTZSZVUJVUDVLZVULPVUAAVVIPAPVMZPV
      UJVUFPVUJVNZPVUEPVUAVUDVOVPZVQVRVVJVUBVUATZSZVVKSZVUJQTZVUHQTZVUJVUHVSVKZ
      VULVVQVUFQVUJAVUFQVTZVVIVVOVVKAVUDQTZPVUAVHVWAAVWBPVUAAVVOSZUYHQVUDUJUKUU
      AZVWCUYHBUYIVUBHWAUYIUUBTZVWCWBVFZVWCUYTUGVUBAVVOWDZWCZVWCHUYHTZBVUBVWCBU
      NZVUBTZSZAVWJUYSTZVWIAVVOVWKWEVWLVUBUYSVWJVWLVUBUYTTZVUBUYSVTZVWCVWNVWKVW
      CUYTUGVUBVWGWFZWGVUBUYSPUUCZWNZWHVWCVWKWDWIAVWMSZVWJUYRTZVWIFCAVWMFAFVMZF
      VWJUYSFVWJVNFCUYRUUDZVQVRVWSUYPCTZSVWTSZVWJUYPGUNZUUEVLZVWIGDVXDGVMGHUYHK
      GUYHVNVQVXDVXEDTZSZVXFSZHEUYHVXFHEVLVXHLUUGVXIAVXCVXGEUYHTZAVWMVXCVWTVXGV
      XFWJVWSVXCVWTVXGVXFUUFVXDVXGVXFWKOWLWOVXCVWTVXFGDVIZVWSVXCVWTVXKGDCUYPVWJ
      UUHWPUUIWMVWMVWTFCVIAFVWJCUYRUUJWQWRZWSZWTXAXCWTPVUAVUDQVUEVUEXDZUUKXEXBA
      VVIVVOVVKXFWIAVVSVVIVVOVVKAUYHQVUHVWDAUYSXMTZVWIBUYSVHVUHUYHTACITUYRXMTZF
      CVHVXOMAVXPFCAVXCSZUYQXMTDJTZVXPFUULNUYQDXMJUUQUUMWTFCUYRIXMUUNWSZAVWIBUY
      SVXLWTUYSHBXMBUYSVNZXGWSXCZXBVVQVUJVUDVUHVSVVPVVKWDVVPVUDVUHVSVKZVVKAVVOV
      YBVVIVWCVUBHBUPZVUDVUHVSVWCVUBHBVWCBVMZBVUBVNVWHVXMXHZVWCVUBHUYSBXMVYDAVX
      OVVOVXSWGAVWMVWIVVOVXLXIVWCVWNVWOVWPVWRWHZXJXKXIWGXLVVRVVSSVVTVULVUJVUHXN
      WPXOVVIVVKPVUAVIAPVUAVUDVUJVUEVXNUYIVUCURXPZXQWQWRWTAVURUBQAVVRSZVUNVUQVY
      HVUNSZVUJVYCRVKZVUQPVUAVYIPVMVUPPUCVUFVVNVUPPVMUURVYIVVOSZVYJSZVUPVYJUCVY
      CVUFVYLVYCVUDVUFVYKVYCVUDVLZVYJVYHVVOVYMVUNAVVOVYMVVRVYEXIXIWGVYLVVOVUDXM
      TZVUDVUFTVYIVVOVYJWKVYNVYLVYGVFPVUAVUDVUEXMVXNUUOWSWOVYLVUOVYCVLZSVUOVYCV
      UJRVYLVYOWDXRVYKVYJWDXSVYIUYSHBXMVUJPVYHVUNBVYHBVMZBVUJVUHRBVUJVNZBRVNZUY
      SHBVXTUUPYDVRAVXOVVRVUNVXSUUSAVVRVUNVWMVWIAVVRVWMVWIVUNVXLUUTXTAVVRVUNWKV
      YHVUNWDUVAWMYAWTYBAVVHVUTUDVUHQVYAAVVAVUHVLZSZVVDVUMVVGVUSVYTVVCVULUBVUFV
      YTVVBVUKVYTVVAVUHVUJRAVYSWDZYCYEYFVYTVVFVURUBQVYTVVEVUNVUQVYTVVAVUHVUJRWU
      AXRUVBYFUVCUVDUVEZUVGAVUJUYOTZSZVUJUYMVLZVUGVUJRVKZVGZUAUYGAWUCUAAUAVMUAV
      UJUYOUAVUJVNUAUYNUAUYGUYMVOVPVQVRWUDUYJUYGTZSZWUESZWUGVUGUYMRVKZVGZWUIWUL
      WUEAWUHWULWUCAWUHSZVUHUYMRVKZWUKWUMUYMVUHVSVKZWUNVGZWUMFUYJUYRVCZHBUPZUYM
      VUHVSWUMUYJUYKFUPWURUYMWUMBUYJDEFGHUYGJKLAWUHWDZWUMUYPUYJTZSZAVXCVXRAWUHW
      UTWEZWUMUYJCUYPWUMUYJUYFTUYJCVTZWUMUYFUGUYJWUSWFUYJCYGXEZYHZNWSWUMWUTVXGS
      SAVXCVXGVXJWUMWUTAVXGWVBYIWUMWUTVXCVXGWVEYIWUMWUTVXGUVFOWLWUMUYFUGUYJWUSW
      CZUVHWUMUYJUYKFWUMFVMFUYJVNWVFWVAAVXCUYKUYHTZWVBWVEVXQVXRVXJGDVHWVGNVXQVX
      JGDAVXCVXGVXJOUVIWTDEGJGDVNXGWSZWSZXHUVJWUMWUQHUYSBXMWUMBVMAVXOWUHVXSWGAV
      WMVWIWUHVXLXIWUMWVCWUQUYSVTWVDFUYJCUYRUVKXEXJXKWUMUYMQTVVSWUOWUPUVLWUMUYH
      QUYMVWDWUMUYHFUYIUYJUYKWAVWEWUMWBVFWVFWUMWVGFUYJWVIWTXAXCAVVSWUHVYAWGUYMV
      UHXNWSUVMWUMVUHVUGUYMRAVUHVUGVLWUHAPUYSHVUDBXMABVMVXTVXSVXLVWCVUDYJYKZWGY
      CUVNXIWGWUJWUFWUKWUJVUJUYMVUGRWUIWUEWDXRYEUVOWUCWUEUAUYGVIAUAUYGUYMVUJUYN
      UYNXDZUYIUYLURXPXQWQWRAVVRVUJVUGRVKZSZSZVUJUEUNZRVKZVUPUCUYOVIZUEVUFWVNWV
      OVUFTZSZWVPSZWVOVUDVLZWVQPVUAWVSWVPPWVNWVRPAWVMPVVLVVRWVLPPVUJQVVMUVPPVUJ
      VUGRVVMPRVNZPVUFQRVVNPQVNWWBUVRYDVRVRPWVOVUFPWVOVNVVNVQVRWVPPVMVRWVTVVOSZ
      WWASZVYHWVLSVUJVUDRVKZVVOWVQWWDVYHWVLWWDAVVRAWVMWVRWVPVVOWWAWJWVSWVPVVOWW
      AVVRAWVMWVRWVPVVOWWAUVSZVVRVVRWVLWVRWWFAUVQXTXTYBWVSWVPVVOWWAWVLAWVMWVRWW
      FWVLVVRWVLWVRWWFAUVTXTXTYBWWDVUJWVOVUDRWVSWVPVVOWWAXFWWCWWAWDUWAWVTVVOWWA
      WKVYHWWEVVOWVQWVLVYHWWESZVVOSZVUPVUJUYIFVUBYOZUYKUQZURULZRVKUCWWKUYOWWHWW
      IUYGTWWKXMTZWWKUYOTWWHUYFUGWWIWWHVWNVWOWWIUYFTZWWHUYTUGVUBWWGVVOWDZWFZVUB
      UYSYGZVWOWWICVTZWWMVWOWWIFCUYRYOZVCZCVWOWWIUYSYOWWSVUBUYSUWBFCUYRUWCUWDWW
      SCVTWWRCVTZFCVHWWTFCVXCWWRUYQCWWRUYQVTVXCUYQDUWEVFUYPCUWFYLUWGFCWWRCYMYPU
      WJZWWICVUBVWQUWHZWNYNUWIWWHVUBUGTZWWIUGTZWWHUYTUGVUBWWNWCZVUBUWKZXEZUWLWW
      LWWHUYIWWJURXPVFUAUYGUYMWWKWWIUYNXMWVKUYJWWIVLUYLWWJUYIURFUYJWWIUYKUWMYQU
      WNWSWWHVUOWWKVLZSVUOWWKVUJRWWHWXHWDXRWWHVUJVUDWWKAVVRWWEVVOXFWWHUYHQVUDVW
      DWWHUYHBUYIVUBHWAVWEWWHWBVFZWXEWWHVWIBVUBWWGVVOBVYHWWEBVYPBVUJVUDRVYQVYRB
      UYIVUCURBUYIVNBURVNBVUBHVOUWOYDVRVVOBVMVRWWHVWKVWIWWHVWKSAVWMVWIAVVRWWEVV
      OVWKUWPWWHVUBUYSVWJWWHVWNVWOWWOWWPXEYHVXLWSYAYRXAXCWWHUYHQWWKVWDWWHUYHFUY
      IWWIUYKWAWXIWXGWWHWVGFWWIWWGVVOFWWGFVMFVUBVUAFVUBVNFUYTUGFUYSVXBUWQFUGVNU
      WRVQZVRWWHUYPWWITZWVGVYHVVOWXKWVGWWEAVVOWXKWVGVVRVWCWXKSZAVXCWVGAVVOWXKWE
      ZVWCWWICUYPVWCVWOWWQVYFWXAXEYHZWVHWSZYSYSYAYRXAXCVYHWWEVVOWKVYHVVOVUDWWKV
      SVKZWWEAVVOWXPVVRVWCVUDUYIFWWIUYIGVUBUYQYTZEUQURULZUQZURULZWWKVSVWCBFGVUB
      UYHHEUYIKAVVOFVXAWXJVRZWALVWCVUBXMXMVBZVTZVUBUWSVWCVWOWYCVYFVWOVUBUYSWYBV
      WOUXLUYSWYBVTZVWOWYDUYRWYBVTZFCVHWYEFCUYQDUWTUXAFCUYRWYBYMYPVFYLXEVUBUXBY
      NVWHVWFVXMUXCVWCWWIWXQEGUPZFUPZWWIUYKFUPWXTWWKVSVWCWWIWYFUYKFXMWYAFWWIVNZ
      WWIXMTVWCWXBVFWXLVXJGWXQVHZWYFUYHTZWXLVXJGWXQWXLVXEWXQTZSAVXCVXGVXJWXLAWY
      KWXMWGWXLVXCWYKWXNWGWXLWXQDVXEWXLWXQUYSUYQYTZDWXLVWOWXQWYLVTVWCVWOWXKVYFW
      GVUBUYSUYQUXDXEWXLAVXCWYLDVLWXMWXNAFCDIJMNUXEWSUXFZYHOWLZWTWXQXMTZWYIWYJV
      UBXMTWYOVWQVUBUYQXMUXGUXHWXQEGXMGWXQVNZXGUXIXEZWXOWXLWXQEDGJWXLGVMZWXLAVX
      CVXRWXMWXNNWSWXLVXGSAVXCVXGVXJWXLAVXGWXMWGWXLVXCVXGWXNWGWXLVXGWDOWLWYMXJU
      XJVWCWYGUYIFWWIWYFUQZURULWXTVWCWWIWYFFWYAWYHVWCWXCWXDVWHWXFXEZWYQXHVWCWYS
      WXSUYIURVWCFWWIWYFWXRWYAWXLWXQEGWYRWYPWXLWXCWXQUGTVWCWXCWXKVWHWGVUBUYQUXK
      XEWYNXHUXMYQUXNVWCWWIUYKFWYAWYHWYTWXOXHUXOXLXIXIUXPXSYSXOWVRWWAPVUAVIZWVN
      WVPWVRXUAPVUAVUDWVOVUEVXNVYGXQUXQUXRWRWVNVUQWVPUEVUFVIAWVMVUQAUDUBUCQVUFV
      UJRVUIWUBUXSUYBVUPWVPUCUEVUFVUOWVOVUJRUXTUYAWHUYCUYDAUACUYKUYMFIVXAFCVNMW
      VHWUMUYMYJYKWVJUYE $.
  $}

  ${
    $d A f j k l z $.  $d B f k l z $.  $d C f j z $.  $d W j k $.
    $d f j k l z ph $.
    esumiun.0 $e |- ( ph -> A e. V ) $.
    esumiun.1 $e |- ( ( ph /\ j e. A ) -> B e. W ) $.
    esumiun.2 $e |- ( ( ( ph /\ j e. A ) /\ k e. B ) -> C e. ( 0 [,] +oo ) ) $.
    $( Sum over a nonnecessarily disjoint indexed union.  The inequality is
       strict in the case where the sets B(x) overlap.  (Contributed by Thierry
       Arnoux, 21-Sep-2019.) $)
    esumiun $p |- ( ph ->
        sum* k e. U_ j e. A B C <_ sum* j e. A sum* k e. B C ) $=
      ( vf vz cfv wceq wa cvv nfcv wcel syl2anc ciun crn wf1o c2nd wral csn cxp
      vl wss cesum cle wbr wf1 wex aciunf1 f1f1orn anim1i f1f frnd adantr eximi
      jca syl csb ccnv nfv nfcsb1v csbeq1a ralrimiva iunexg simprl f1ocnv nfiu1
      cv adantrlr nfrn nff1o nfralw nfan nfss simpr fveq2d simplr simpld simprd
      simp-4r ad2antrr 2fveq3 eqeq12d rspcva eqtr3d f1ocnvfv1 3eqtr2rd wfn wrex
      id f1ofn simpllr fvelrnb biimpa r19.29a simprr sselda eliun r19.29af cpnf
      sylib cc0 cicc co nfel adantllr bilani adantlr esumf1o eqcomd vsnex xpexd
      a1i c1st nfcsbw rspcsbela xp1st elsni xp2nd reximi sylbi adantl r19.29af2
      simplll esummono eqbrtrrd cop vex op2ndd anasss esum2d breqtrrd exlimddv
      ) AEBCUAZLVNZUBZUUAUCZUHVNZUUANUDNZUUDOZUHYTUEZPZUUBEBEVNZUFZCUGZUAZUIZPZ
      YTDFUJZBCDFUJEUJZUKULLAYTUULUUAUMZUUGPZLUNUUNLUNABCLEUHGHIJUOUURUUNLUURUU
      HUUMUUQUUCUUGYTUULUUAUPUQUUQUUMUUGUUQYTUULUUAYTUULUUAURUSUTVBVAVCAUUNPZUU
      OUULFMVNZUDNZDVDZMUJZUUPUKUUSUUBUVBMUJZUUOUVCUKUUSUUOUVDUUSYTDUUBUVBFMUUA
      VEZUVAQUUSMVFZMDRFUVADVGZMYTRMUUBRMUVERFUVADVHZAYTQSZUUNABGSZCHSZEBUEUVII
      AUVKEBJVIEBCGHVJTUTAUUCUUMUUBYTUVEUCZUUGAUUCUUMPPUUCUVLAUUCUUMVKYTUUBUUAV
      LVCVOUUSUUTUUBSZPZUUTUUKSZUUTUVENZUVAOZEBUUSUVMEAUUNEAEVFZUUHUUMEUUCUUGEE
      YTUUBUUAEUUARZEBCVMZEUUAUVSVPVQUUFEUHYTUVTUUFEVFVRVSEUUBUULEUUBREBUUKVMZV
      TVSVSUVMEVFVSUVNUUIBSZPUVOPZFVNZUUANZUUTOZUVQFYTUWCUWDYTSZPZUWFPZUVAUWDUW
      EUVENZUVPUWIUWEUDNZUVAUWDUWIUWEUUTUDUWHUWFWAZWBUWIUWGUUGUWKUWDOZUWCUWGUWF
      WCZUWCUUGUWGUWFUWCUUCUUGUWCUUHUUMAUUNUVMUWBUVOWFWDZWEWGUUFUWMUHUWDYTUUDUW
      DOZUUEUWKUUDUWDUUDUWDUDUUAWHUWPWPWIWJTWKUWIUUCUWGUWJUWDOUWCUUCUWGUWFUWCUU
      CUUGUWOWDZWGUWNYTUUBUWDUUAWLTUWIUWEUUTUVEUWLWBWMUWCUUAYTWNZUVMUWFFYTWOZUW
      CUUCUWRUWQYTUUBUUAWQVCUUSUVMUWBUVOWRUWRUVMUWSFYTUUTUUAWSWTTXAUVNUUTUULSZU
      VOEBWOZUUSUUBUULUUTAUUHUUMXBXCEUUTBUUKXDZXGXEAUWGDXHXFXIXJZSZUUNAUWGPUWDC
      SZUXDEBAUWGEUVREUWDYTEUWDRUVTXKVSAUWBUXEUXDUWGKXLUWGUXEEBWOAEUWDBCXDXMXEX
      NXOXPUUSUUBUVBUULMQUVFAUULQSZUUNAUVJUUKQSZEBUEUXFIAUXGEBAUWBPZUUJCQHUUJQS
      UXHEXQXSJXRVIEBUUKGQVJTUTAUWTUVBUXCSZUUNAUWTPZUUTXTNZUUIOZUVACSZPZUXIEBAU
      WTEUVREUUTUULEUUTRUWAXKVSEUVBUXCEFUVADEUVAREDRYAEUXCRXKUXJUWBPZUXNPZUXMUX
      DFCUEZUXIUXOUXLUXMXBUXPAUWBUXQAUWTUWBUXNYJUXJUWBUXNWCUXHUXDFCKVITFUVACDUX
      CYBTUWTUXNEBWOZAUWTUXAUXRUXBUVOUXNEBUVOUXLUXMUVOUXKUUJSUXLUUTUUJCYCUXKUUI
      YDVCUUTUUJCYEVBYFYGYHYIXNAUUCUUMUUMUUGAUUCUUMXBVOYKYLAUUPUVCOUUNAMBCDEFUV
      BGHUVGUUTUUIUWDYMOZDUVBUXSUWDUVAODUVBOUXSUVAUWDUUIUWDUUTEYNFYNYOXPUVHVCXP
      IJAUWBUXEUXDKYPYQUTYRYS $.
  $}

