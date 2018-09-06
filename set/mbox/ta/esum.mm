$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
     Extended sum
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c sum* $. $( Summation sign. $)

  $( Extend class notation to include infinite summations. $)
  cesum $a class sum* k e. A B $.

  ${
    $( Define a short-hand for the possibly infinite sum over the extended
       non-negative reals. ` sum* ` is relying on the properties of the
       ` tsums ` , developped by Mario Carneiro.  (Contributed by Thierry
       Arnoux, 21-Sep-2016.) $)
    df-esum $a |- sum* k e. A B =
      U. ( ( RR*s |`s ( 0 [,] +oo ) ) tsums ( k e. A |-> B ) ) $.
  $}

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
      a1i ccmn xrge0cmn ctps xrge0tps simpl nfel1 nfra1 nfan nfcv fmptdF tsmscl
      simpr r19.21bi cuni wceq df-esum xrge0tsmsbi mpbiri sseldd ) ADFZBGHIJZFZ
      CAKZLZMVANJZCABOZPJZVAABCQZVDAVAVFVEDRVEUAFVDUBTVEUCFVDUDTUTVCUEZVDCABVAV
      FUTVCCCADEUFVBCAUGUHECVAUIVDVBCAUTVCULUMVFSUJZUKVDVHVGFVHVGUNUOABCUPVDAVH
      VFVEDVESVIVJUQURUS $.
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

    $d A j k $.  $d B k $.  $d C j $.
    $( Change bound variable in an extended sum.  (Contributed by Thierry
       Arnoux, 19-Jun-2017.) $)
    cbvesumv $p |- sum* j e. A B = sum* k e. A C $=
      ( nfcv cbvesum ) ABCDEFEAGDAGEBGDCGH $.
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
      ( cxrs cc0 cpnf cicc co cress cmpt ctsu eqid cuni nfcv fmptdF xrge0tsmseq
      cesum df-esum syl6reqr ) ADLMNOPZQPZEBCRZSPUABCEUEABDUJUIFUITIAEBCUHUJGHE
      UHUBJUJTUCKUDBCEUFUG $.
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
      cc0 cress ctsu df-esum eqid nfcv fmptdF cv cres wcel wss wceq inss1 sseli
      wa elpwid adantl resmptf oveq2d eqtr2d mpteq2dva rneqd supeq1d xrge0tsmsd
      syl unieqd syl5eq xrltso supex unisn syl6eq ) ACDFUAZBCUBZMUCZENZOZPQUDZU
      EZRZWEAVTUFUIUGUHSZUJSZFCDNZUKSZRWGCDFULAWKWFACWEWJWIGBWIUMJAFCDWHWJHIFWH
      UNKWJUMUOAPWDBWBWIWJBUPZUQZTSZNZOQAWCWOABWBEWNAWLWBURZVCZWNWIFWLDNZTSEWQW
      MWRWITWQWLCUSZWMWRUTWPWSAWPWLCWBWAWLWAMVAVBVDVEFCWLDIFWLUNVFVMVGLVHVIVJVK
      VLVNVOWEPWDQVPVQVRVS $.
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
      cicc ctsu wral ex ralrimi esumcl syl2anc snidg fmptdF cres cpw cin wa wss
      wceq inss1 simpr sseldi elpwid resmptf eqcomd esumval xrge0tsmsd eleqtrrd
      oveq2d ) ABCDKZVKUAZUBUCUDUFLZUELZDBCMZUGLAVKVMNZVKVLNABENCVMNZDBUHVPHAVQ
      DBFADOBNVQIUIUJBCDEGUKULVKVMUMPABVKVOVNEJVNQHADBCVMVOFGDVMRIVOQUNAJBCVNVO
      JOZUOZSLDEFGHIAVRBUPZTUQZNZURZDVRCMZVSVNSWCVSWDWCVRBUSVSWDUTWCVRBWCWAVTVR
      VTTVAAWBVBVCVDDBVRCGDVRRVEPVFVJVGVHVI $.
  $}

  ${
    $d x y $.  $d y A $.
    $( Extended sum over the empty set.  (Contributed by Thierry Arnoux,
       19-Feb-2017.) $)
    esumnul $p |- sum* x e. (/) A = 0 $=
      ( vy c0 cfn cin cc0 cmpt cxr clt csup csn wceq wtru cvv wcel 0ex a1i cgsu
      co cesum cpw nftru nfcv cpnf cicc wral ral0 r19.21bi cv cxrs cress ineq1i
      crn pw0 0fin wss snssi df-ss sylib ax-mp eqtri eleq2i elsn biimpi mpteq1d
      bitri mpt0 syl6eq oveq2d xrge00 gsum0 adantl esumval cxp fconstmpt eqcomi
      trud wfn wne 0xr rgenw eqid fnmpt snnz eqnetri fconst5 mp2an mpbi supeq1i
      wb wor xrltso supsn 3eqtri ) DBAUAZCDUBZEFZGHZUNZIJKZGLZIJKZGWPXAMNCDBGAO
      AUCADUDDOPNQRNBGUEUFTZPZADXEADUGNXEAUHRUICUJZWRPZUKXDULTZAXFBHZSTZGMNXGXJ
      XHDSTGXGXIDXHSXGXIADBHDXGAXFDBXGXFDMZXGXFDLZPXKWRXLXFWRXLEFZXLWQXLEUOUMDE
      PZXMXLMZUPXNXLEUQXODEURXLEUSUTVAVBZVCCDVDVGVEVFABVHVIVJXHGVKVLVIVMVNVRIWT
      XBJWSWRXBVOZMZWTXBMZXQWSCWRGVPVQWSWRVSZWRDVTXRXSWKGIPZCWRUGXTYACWRWAWBCWR
      GWSIWSWCWDVAWRXLDXPDQWEWFWRGWSWGWHWIWJIJWLYAXCGMWMWAIGJWNWHWO $.
  $}

  ${
    esum0.k $e |- F/_ k A $.
    $d x y $.  $d x y A $.  $d k x V $.
    $( Extended sum of zero.  (Contributed by Thierry Arnoux, 3-Mar-2017.) $)
    esum0 $p |- ( A e. V -> sum* k e. A 0 = 0 ) $=
      ( vx wcel cc0 cfn cmpt cxr clt csup cpnf co 0xr ax-mp a1i wceq mp2an c0
      cesum cpw cin crn nfel1 id cicc cv cle wbr pnfxr pnfge lbicc2 mp3an cress
      wa cxrs cgsu cmnd cvv ccmn xrge0cmn cmnmnd xrge00 gsumz esumval fconstmpt
      vex csn cxp eqcomi wfn wne wral rgenw eqid fnmpt 0elpw 0fin elin mpbir2an
      wb ne0i fconst5 mpbi supeq1d wor xrltso supsn syl6eq eqtrd ) ACFZAGBUAEAU
      BZHUCZGIZUDZJKLZGWLEAGGBCBACDUEDWLUFGGMUGNZFZWLBUHAFUPGJFZMJFGMUIUJZWSOUK
      WTXAOGULPGMUMUNQUQWRUONZBEUHZGIURNGRZWLXCWNFUPXBUSFZXCUTFXDXBVAFXEVBXBVCP
      EVHXCBXBUTGVDVESQVFWLWQGVIZJKLZGWLJWPXFKWPXFRZWLWOWNXFVJZRZXHXIWOEWNGVGVK
      WOWNVLZWNTVMZXJXHWBWTEWNVNXKWTEWNOVOEWNGWOJWOVPVQPTWNFZXLXMTWMFTHFAVRVSTW
      MHVTWAWNTWCPWNGWOWDSWEQWFJKWGWTXGGRWHOJGKWISWJWK $.
  $}

  ${
    $d k n $.  $d k A $.  $d n B $.  $d k C $.  $d k D $.  $d k G $.
    $d k ph $.
    esumf1o.0 $e |- F/ n ph $.
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
      ( co cxrs cc0 cpnf cicc cress cmpt ctsu cuni ccom xrge0base ccmn xrge0cmn
      cesum wcel a1i ctps xrge0tps eqid fmptd tsmsf1o cv wa wf1o f1of ffvelrnda
      cfv wf syl eqeltrrd ralrimi feqmptdf mpteq2da eqtrd eqidd fmptcof2 oveq2d
      ex unieqd df-esum 3eqtr4g ) AUAUBUCUDTZUETZFBCUFZUGTZUHWBGDEUFZUGTZUHBCFU
      MDEGUMAWDWFAWDWBWCHUIZUGTWFABWADWCWBHJUJWBUKUNAULUOWBUPUNAUQUOPAFBCWAWCSW
      CURUSQUTAWGWEWBUGAGFDBICEHWCMLKAIBUNZGDKAGVAZDUNZWHAWJVBWIHVFZIBRADBWIHAD
      BHVCDBHVGQDBHVDVHZVEVIVQVJAHGDWKUFGDIUFAGDBHMNWLVKAGDWKIKRVLVMAWCVNOVOVPV
      MVRBCFVSDEGVSVT $.
  $}

  ${
    $d k y z $.  $d y z A $.  $d y B $.  $d k D $.  $d y z C $.  $d y ph $.
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
      ( cv wceq wcel wrex cab cesum cmpt cvv nfre1 nfab nfmpt1 syl abrexexd wfn
      elex ccnv wfun crn wf1o wral ex ralrimi fnmptf rnmpt a1i dff1o2 syl3anbrc
      eqid wa cfv simpr fvmpt2f syl2anc cc0 cpnf cicc co vex eqeq1 rexbidv elab
      reximi sylbi nfv wi eleq1 syl5ibrcom rexlimd imp sylan2 esumf1o eqcomd )
      ACRZFSZHDUAZCUBZGBUCDEHUCAWMGDEBHHDFUDZFUEKWLHCWKHDUFUGLHDFUHMAHCDFLADITD
      UETNDIULUIUJAWNDUKZWNUMUNWNUOWMSZDWMWNUPAFJTZHDUQWOAWQHDKAHRZDTZWQQURUSHD
      FJLUTUIOWPAHCDFWNWNVEVAVBDWMWNVCVDAWSVFZWSWQWRWNVGFSAWSVHQHDFJLVIVJBRZWMT
      ZAGESZHDUAZGVKVLVMVNZTZXBXAFSZHDUAZXDWLXHCXABVOWJXASWKXGHDWJXAFVPVQVRXGXC
      HDMVSVTAXDXFAXCXFHDKXFHWAAWSXCXFWBWTXFXCEXETPGEXEWCWDURWEWFWGWHWI $.
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
      ctmd xrge0tmd nfcv eqid fmptdF cres esumel wceq ssun1 resmptf mp1i oveq2d
      wss eleqtrrd ssun2 eqidd tsmssplit esumid ) ABCUAZDBDENZCDENZOPEQFEBCGHUB
      ZABQRCQRVRQRIJBCQQUCUDZEUEZVRRAWCBRZWCCRZUFDUIUGUHPZRZWCBCUJAWDWGWELMUKUL
      ZAVRWFBCOEVRDSZUMWFUNPZQVSVTUOUPWJUQRAURUSWJUTRAVAUSWBAEVRDWFWIFWAEWFVBWH
      WIVCVDAVSWJEBDSZTPWJWIBVEZTPABDEQFGILVFAWLWKWJTBVRVLWLWKVGABCVHEVRBDWAGVI
      VJVKVMAVTWJECDSZTPWJWICVEZTPACDEQFHJMVFAWNWMWJTCVRVLWNWMVGACBVNEVRCDWAHVI
      VJVKVMKAVRVOVPVQ $.
  $}

  ${
    $d k x y A $.  $d x y B $.  $d y C $.  $d k V $.  $d k x y ph $.
    esumadd.0 $e |- ( ph -> A e. V ) $.
    esumadd.1 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumadd.2 $e |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) ) $.
    $( Addition of infinite sums.  (Contributed by Thierry Arnoux,
       24-Mar-2017.) $)
    esumadd $p |- ( ph -> sum* k e. A ( B +e C ) =
                        ( sum* k e. A B +e sum* k e. A C ) ) $=
      ( cxad co cesum wcel cmpt ctsu a1i eqid fmptd esumel eqidd nfv nfcv cv wa
      cpnf cicc ge0xaddcl syl2anc cxrs cress xrge0base xrge0plusg ccmn xrge0cmn
      cc0 cof ctmd xrge0tmd tsmsadd offval2 oveq2d eleqtrd esumid ) ABCDJKZBCEL
      ZBDELZJKZEFAEUAZEBUBZGAEUCBMUDCUOUEUFKZMDVJMVDVJMHICDUGUHAVGUIVJUJKZEBCNZ
      EBDNZJUPKZOKVKEBVDNZOKABVJJVLVKVMFVEVFUKULVKUMMAUNPVKUQMAURPGAEBCVJVLHVLQ
      RAEBDVJVMIVMQRABCEFVHVIGHSABDEFVHVIGISUSAVNVOVKOAEBCDJVLVMFVJVJGHIAVLTAVM
      TUTVAVBVC $.

    esumle.3 $e |- ( ( ph /\ k e. A ) -> B <_ C ) $.
    $( If all of the terms of an extended sums compare, so do the sums.
       (Contributed by Thierry Arnoux, 8-Jun-2017.) $)
    esumle $p |- ( ph -> sum* k e. A B <_ sum* k e. A C ) $=
      ( cesum cxad co cle cxr wcel cc0 wbr cpnf syl2anc cxne cicc esumcl sseldi
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
    $d k A $.  $d k C $.
    esummono.f $e |- F/ k ph $.
    esummono.c $e |- ( ph -> C e. V ) $.
    esummono.b $e |- ( ( ph /\ k e. C ) -> B e. ( 0 [,] +oo ) ) $.
    esummono.a $e |- ( ph -> A C_ C ) $.
    $( Extended sum is monotonic.  (Contributed by Thierry Arnoux,
       19-Oct-2017.) $)
    esummono $p |- ( ph -> sum* k e. A B <_ sum* k e. C B ) $=
      ( cesum co cle cc0 wbr cpnf wcel cvv syl2anc cxr cdif cxad cicc difexg cv
      wral syl simpr eldifad syldan ralrimi nfcv esumcl elxrge0 simprbi iccssxr
      wa ex wi ssexd sselda sseldi xraddge02 mpd cun cin wceq disjdif esumsplit
      c0 a1i wss undif sylib esumeq1d eqtr3d breqtrd ) ABCEKZVRDBUAZCEKZUBLZDCE
      KZMANVTMOZVRWAMOZAVTNPUCLZQZWCAVSRQZCWEQZEVSUFWFADFQWGHDBFUDUGZAWHEVSGAEU
      EZVSQZWHAWKWJDQZWHAWKUQWJDBAWKUHUIIUJZURUKVSCEREVSULZUMSZWFVTTQZWCVTUNUOU
      GAVRTQWPWCWDUSAWETVRNPUPZABRQWHEBUFVRWEQABDFHJUTZAWHEBGAWJBQZWHAWSWLWHABD
      WJJVAIUJZURUKBCEREBULZUMSVBAWETVTWQWOVBVRVTVCSVDABVSVEZCEKWAWBABVSCEGXAWN
      WRWIBVSVFVJVGABDVHVKWTWMVIAXBDCEGABDVLXBDVGJBDVMVNVOVPVQ $.
  $}

  ${
    $d a k x y A $.  $d a x y B $.  $d y X $.  $d a x y ph $.
    gsumesum.0 $e |- F/ k ph $.
    gsumesum.1 $e |- ( ph -> A e. Fin ) $.
    gsumesum.2 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    $( Relate a group sum on ` ( RR*s |``s ( 0 [,] +oo ) ) ` to a finite
       extended sum.  (Contributed by Thierry Arnoux, 19-Oct-2017.) $)
    gsumesum $p |- ( ph -> ( ( RR*s |`s ( 0 [,] +oo ) ) gsum ( k e. A |-> B ) )
      = sum* k e. A B ) $=
      ( vx va cfn cc0 co cgsu cxr wcel wa a1i sseldi wceq syl2anc cesum cpw cin
      vy cxrs cpnf cicc cress cv cmpt crn clt csup eqidd esumval xrltso iccssxr
      nfcv wor xrge0base xrge00 ccmn xrge0cmn eqid fmptdF cvv csn cdif fisuppfi
      gsumcl wrex pwidg elin sylanbrc mpteq1 oveq2d eqeq2d rspcev ovex elrnmpti
      syl sylibr cle wbr wn wral simpr cbvmptv cxad vex nfv nfan wel simpll wss
      sylib inss1 sseli elpwid sseldd inss2 adantr difexg eldifad diffi elxrge0
      ad2antlr simprbi xraddge02 imp syl21anc adantlr adantl cres xrge0plusg wf
      ccnv cima c0 disjdif cun undif biimpi eqcomd gsumsplit resmpt difss ax-mp
      oveq2i oveq12d eqtrd breqtrrd ralrimiva r19.29r biimpar rexlimivw rnmptss
      breq1 wb sselda xrltnle con2bid mpbid supmax eqtr2d ) ABCDUAHBUBZJUCZUEKU
      FUGLZUHLZDHUIZCUJZMLZUJZUKZNULUMUUIDBCUJZMLZAHBCUULDJEDBURZFGAUUJUUGOZPZU
      ULUNUOAUDNUUNUUPULNULUSAUPQAUUHNUUPKUFUQZABUUHUUOUUIJKUTVAUUIVBOZAVCQFADB
      CUUHUUOEUUQDUUHURZGUUOVDVEZABUUHVFKVGVHZUUOFUVCVIZVJRZAUUPUULSZHUUGVKZUUP
      UUNOABUUGOZUUPUUPSZUVHABUUFOZBJOZUVIAUVLUVKFBJVLWAFBUUFJVMVNAUUPUNUVGUVJH
      BUUGUUJBSZUULUUPUUPUVMUUKUUOUUIMDUUJBCVOVPVQVRTHUUGUULUUPUUMUUMVDZUUIUUKM
      VSVTWBAUDUIZUUNOZPZUVOUUPWCWDZUUPUVOULWDZWEZUVQUVOUUIDIUIZCUJZMLZSZIUUGVK
      ZUWCUUPWCWDZIUUGWFZUVRUVQUVPUWEAUVPWGIUUGUWCUVOUUMHIUUGUULUWCUUJUWASUUKUW
      BUUIMDUUJUWACVOVPWHUUIUWBMVSVTWPUVQUWFIUUGUVQUWAUUGOZPZUWCUWCUUIDBUWAVHZC
      UJZMLZWILZUUPWCAUWHUWCUWMWCWDZUVPAUWHPZUWCNOZUWLNOZKUWLWCWDZUWNUWOUUHNUWC
      UUTUWOUWAUUHUWBUUIVFKUTVAUVAUWOVCQZUWAVFOUWOIWJQUWODUWACUUHUWBAUWHDEUWHDW
      KWLZDUWAURUVBUWODIWMZPZADUIZBOZCUUHOZAUWHUXAWNUXBUWABUXCUWHUWABWOZAUXAUWH
      UWABUUGUUFUWAUUFJWQZWRWSZXGUWOUXAWGWTGTUWBVDVEZUWOUWAUUHUVDUWBUWOUUGJUWAU
      UFJXAZAUWHWGRUXIVIVJRUWOUUHNUWLUUTUWOUWJUUHUWKUUIVFKUTVAUWSUWOUVLUWJVFOAU
      VLUWHFXBZBUWAJXCWAUWODUWJCUUHUWKUWTDUWJURUVBUWOUXCUWJOZPZAUXDUXEAUWHUXLWN
      UXMUXCBUWAUWOUXLWGXDGTUWKVDVEZUWOUWJUUHUVDUWKUWOUVLUWJJOUXKBUWAXEWAUXNVIV
      JZRUWOUWLUUHOZUWRUXOUXPUWQUWRUWLXFXHWAUWPUWQPUWRUWNUWCUWLXIXJXKXLUWIAUXFU
      UPUWMSAUVPUWHWNUWHUXFUVQUXHXMAUXFPZUUPUUIUUOUWAXNZMLZUUIUUOUWJXNZMLZWILUW
      MUXQBUUHUWAUWJWIUUOUUIJKUTVAXOUVAUXQVCQAUVLUXFFXBABUUHUUOXPUXFUVCXBAUUOXQ
      UVDXRJOUXFUVEXBUWAUWJUCXSSUXQUWABXTQUXFBUWAUWJYAZSAUXFUYBBUXFUYBBSUWABYBY
      CYDXMYEUXQUXSUWCUYAUWLWIUXFUXSUWCSAUXFUXRUWBUUIMDBUWACYFVPXMUYAUWLSUXQUXT
      UWKUUIMUWJBWOUXTUWKSBUWAYGDBUWJCYFYHYIQYJYKTYLYMUWEUWGPUWDUWFPZIUUGVKUVRU
      WDUWFIUUGYNUYCUVRIUUGUWDUVRUWFUVOUWCUUPWCYRYOYPWATUVQUUPNOZUVONOZUVRUVTYS
      AUYDUVPUVFXBAUUNNUVOAUULNOZHUUGWFUUNNWOAUYFHUUGUUSUUHNUULUUTUUSUUJUUHUUKU
      UIUUGKUTVAUVAUUSVCQAUURWGZUUSDUUJCUUHUUKAUURDEUURDWKWLDUUJURUVBUUSDHWMZPZ
      AUXDUXEAUURUYHWNUYIUUJBUXCUYIUUJBUURUUJUUFOAUYHUUGUUFUUJUXGWRXGWSUUSUYHWG
      WTGTUUKVDVEZUUSUUJUUHUVDUUKUUSUUGJUUJUXJUYGRUYJVIVJRYMHUUGUULNUUMUVNYQWAY
      TUYDUYEPUVSUVRUUPUVOUUAUUBTUUCUUDUUE $.
  $}

  ${
    $d a k x y A $.  $d a x y B $.  $d a y X $.  $d a x y ph $.
    esumlub.f $e |- F/ k ph $.
    esumlub.0 $e |- ( ph -> A e. V ) $.
    esumlub.1 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumlub.2 $e |- ( ph -> X e. RR* ) $.
    esumlub.3 $e |- ( ph -> X < sum* k e. A B ) $.
    $( The extended sum is the lowest upper bound for the partial sums.
       (Contributed by Thierry Arnoux, 19-Oct-2017.) $)
    esumlub $p |- ( ph -> E. a e. ( ~P A i^i Fin ) X < sum* k e. a B ) $=
      ( vx clt wbr cfn cxr wcel wa simpr vy cxrs cc0 cpnf cicc co cress cv cmpt
      cgsu cpw cin wrex cesum crn csup nfcv eqidd esumval breq2d wss wb iccssxr
      wral xrge0base xrge00 ccmn xrge0cmn a1i nfan simpll inss1 ad2antlr elpwid
      nfv sseli sseldd syl2anc eqid fmptdF cvv csn inss2 sseldi fisuppfi gsumcl
      cdif ralrimiva rnmptss syl supxrlub bitrd ovex wceq mpteq1 oveq2d cbvmptv
      mpbid elrnmpti rexxfr2d gsumesum biimpd reximdva mpd ) AFUBUCUDUEUFZUGUFZ
      DGUHZCUIZUJUFZNOZGBUKZPULZUMZFXGCDUNZNOZGXLUMAFUAUHZNOZUAMXLXFDMUHZCUIZUJ
      UFZUIZUOZUMZXMAFBCDUNZNOZYCLAYEFYBQNUPZNOZYCAYDYFFNAMBCXTDEHDBUQIJAXRXLRZ
      SZXTURUSUTAYBQVAZFQRYGYCVBAXTQRZMXLVDYJAYKMXLYIXEQXTUCUDVCYIXRXEXSXFXLUCV
      EVFXFVGRYIVHVIAYHTZYIDXRCXEXSAYHDHYHDVOVJDXRUQDXEUQYIDUHZXRRZSZAYMBRZCXER
      ZAYHYNVKYOXRBYMYOXRBYHXRXKRAYNXLXKXRXKPVLZVPVMVNYIYNTVQJVRXSVSVTZYIXRXEWA
      UCWBWGXSYIXLPXRXKPWCZYLWDYSWEWFWDWHMXLXTQYAYAVSWIWJKUAYBFWKVRWLWRAXQXJUAG
      XIYBXLWAXIWARAXGXLRZSZXFXHUJWMZVIXPYBRXPXIWNZGXLUMVBAGXLXIXPYAMGXLXTXIXRX
      GWNXSXHXFUJDXRXGCWOWPWQUUCWSVIAUUDSXPXIFNAUUDTUTWTWRAXJXOGXLUUBXJXOUUBXIX
      NFNUUBXGCDAUUADHUUADVOVJUUBXLPXGYTAUUATWDUUBYMXGRZSZAYPYQAUUAUUEVKUUFXGBY
      MUUFXGBUUAXGXKRAUUEXLXKXGYRVPVMVNUUBUUETVQJVRXAUTXBXCXD $.
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
      ( cxad co cesum wcel cmpt ctsu a1i eqid fmptdF cv cc0 cpnf cicc ge0xaddcl
      wa syl2anc cxrs cof xrge0base xrge0plusg ccmn xrge0cmn ctmd xrge0tmd nfcv
      cress esumel tsmsadd eqidd offval2f oveq2d eleqtrd esumid ) ABCDLMZBCENZB
      DENZLMZEFGHIAEUABOUFCUBUCUDMZODVIOVEVIOJKCDUEUGAVHUHVIUQMZEBCPZEBDPZLUIMZ
      QMVJEBVEPZQMABVILVKVJVLFVFVGUJUKVJULOAUMRVJUNOAUORIAEBCVIVKGHEVIUPZJVKSTA
      EBDVIVLGHVOKVLSTABCEFGHIJURABDEFGHIKURUSAVMVNVJQAEBCDLVKVLFVIVIGHIJKAVKUT
      AVLUTVAVBVCVD $.

    esumlef.3 $e |- ( ( ph /\ k e. A ) -> B <_ C ) $.
    $( If all of the terms of an extended sums compare, so do the sums.
       (Contributed by Thierry Arnoux, 8-Jun-2017.) $)
    esumlef $p |- ( ph -> sum* k e. A B <_ sum* k e. A C ) $=
      ( cesum co cle cxr wcel cc0 wbr cpnf cxne cxad cicc iccssxr cv ex ralrimi
      wral esumcl syl2anc sseldi wa xnegcld xaddcld wb xsubge0 mpbird pnfge syl
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
      sseldi eqid gsumconstf syl3anc cn0 syl xrge0mulgnn0 eqtrd esumval wss cle
      hashcl wral wrex wi cr csn cun nn0ssre ressxr sstri pnfxr snssi unssi cvv
      wf hashf vex ffvelrn mp2an sselii iccssxr adantr xmulcld hashxrcl elrnmpt
      fmptd frn wb biimpi 0xr iccgelb jca cdom inss1 sseli elpwi 3syl ralrimiva
      ssdomg r19.29r elin sylibr fveq2 oveq1d eqeq2d rspcev ovex adantl simp-4r
      breq2 c0 oveq2d xmul01 elrnmpti simpllr cn ex c1 hashdomi syl2anr eqbrtrd
      sylc xlemul1a syl31anc rexlimivw pwidg ancri mpan2 crp w3o elxrge02 sylib
      wn 0elpw 0fin mpbir2an hash0 eqeltri syl6req ad4antr breqtrd cdiv eqeltrd
      nnnn0 hashclb sylanbrc eqidd simp-8r nnred simp-5r ltdivmul2d mpbid rpred
      cmul rexmul breqtrrd rexlimdva impr rerpdivcld ishashinf ad2antlr r19.29a
      arch wex nfielex snelpwi snfi jctir hashsng 1re syl6eqel syl5breqr eqtr2d
      xmulpnf1 exlimddv adantll ltpnf 3jaodan mpdan pm2.61dan supxr2 syl22anc
      0lt1 ) ADHZBIJUFKZHZLZABCUGGAUHZMUIZGUJZNUKZBOKZULZUMZPQUNZANUKZBOKZUXIGA
      BUXNCDUXFUXHCCADEUOCBUXGFUOUPEUXFUXHUQZUXFUXHCUJAHUTUXIUXLUXKHZLZURUXGUSK
      ZCUXLBULVAKZUXMBUYCVBUKZKZUXNUYBUYCVCHZUXLMHZUXHUYDUYFRUYGUYBUYCVDHUYGVEU
      YCVFVGVHUYBUXKMUXLUXJMVIUXIUYAVJZVLZUXFUXHUYAUTZUXLUXGUYECUYCBFVKUYEVMVNV
      OUYBUXMVPHZUXHUYFUXNRUYBUYHUYLUYJUXLWCVQUYKUXMBVRSVSVTUXIUXPPWAZUXSPHUAUJ
      ZUXSWBTZUAUXPWDUYNUXSQTZUYNUBUJZQTZUBUXPWEZWFZUAWGWDUXQUXSRUXIUXKPUXOWQUY
      MUXIGUXKUXNPUXOUYBUXMBUXMPHZUYBVPJWHZWIZPUXMVPVUBPVPWGPWJWKWLJPHZVUBPWAWM
      JPWNVGWOWPVUCNWQUXLWPHUXMVUCHWRGWSWPVUCUXLNWTXAXBVHZUXIBPHZUYAUXIUXGPBIJX
      CUXFUXHVJVLZXDZXEUXOVMZXHUXKPUXOXIVQUXIUXRBUXFUXRPHZUXHADXFXDZVUGXEUXIUYO
      UAUXPUXIUYNUXPHZLUYNUXNRZUXNUXSWBTZLZGUXKWEZUYOVULVUMGUXKWEZVUNGUXKWDVUPU
      XIVULVUQUYNWPHVULVUQXJUAWSGUXKUXNUYNUXOWPVUIXGVGXKUXIVUNGUXKUYBVUAVUJVUFI
      BWBTZLUXMUXRWBTZVUNVUEUXIVUJUYAVUKXDUYBVUFVURVUHUYBIPHZVUDUXHVURVUTUYBXLV
      HVUDUYBWMVHUYKIJBXMVOXNUYBUXLAXOTZVUSUYBUXFUXLAWAZVVAUXIUXFUYAUXTXDUYBUYA
      UXLUXJHVVBUYIUXKUXJUXLUXJMXPXQUXLAXRXSUXLADYAUUDUXLAUUAVQUXMUXRBUUEUUFXTV
      UMVUNGUXKYBUUBVUOUYOGUXKVUOUYNUXNUXSWBVUMVUNUQVUMVUNVJUUCUUGVQXTUXIUYTUAW
      GUXIUYNWGHZLZUYPUYSVVDUYPLZAMHZUYSVVEVVFLUXSUXPHZUYPUYSVVFVVGVVEVVFAUXKHZ
      VVGVVFAUXJHZVVFLVVHVVFVVIAMUUHUUIAUXJMYCYDVVHUXSUXNRZGUXKWEZVVGVVHUXSUXSR
      ZVVKUXSVMVVJVVLGAUXKUXLARZUXNUXSUXSVVMUXMUXRBOUXLANYEYFYGYHUUJUXSWPHVVGVV
      KXJUXRBOYIGUXKUXNUXSUXOWPVUIXGVGYDVQYJVVDUYPVVFUTUYRUYPUBUXSUXPUYQUXSUYNQ
      YLYHSVVEVVFUUOZLZBIRZBUUKHZBJRZUULZUYSVVOUXHVVSUXFUXHVVCUYPVVNYKBUUMUUNVV
      OVVPUYSVVQVVRVVOVVPLZIUXPHZUYNIQTZUYSVVTIUXNRZGUXKWEZVWAVVTYMUXKHZIYMNUKZ
      BOKZRZVWDVWEVVTVWEYMUXJHYMMHAUUPUUQYMUXJMYCUURVHVVTVWGVWFIOKZIVVTBIVWFOVV
      OVVPVJZYNVWFPHVWIIRVWFIPUUSXLUUTVWFYOVGUVAVWCVWHGYMUXKUXLYMRZUXNVWGIVWKUX
      MVWFBOUXLYMNYEYFYGYHSGUXKUXNIUXOVUIUXMBOYIZYPYDVVTUYNUXSIQVVDUYPVVNVVPYQV
      VTUXSUXRIOKZIVVTBIUXROVWJYNVVTVUJVWMIRUXIVUJVVCUYPVVNVVPVUKUVBUXRYOVQVSUV
      CUYRVWBUBIUXPUYQIUYNQYLYHSVVOVVQLZUYNBUVDKZUCUJZQTZUDUJZNUKZVWPRZUDUXJWEZ
      LZUYSUCYRVWNVWPYRHZLZVWQVXAUYSVXDVWQLZVWTUYSUDUXJVXEVWRUXJHZLZVWTUYSVXGVW
      TLZVWSBOKZUXPHZUYNVXIQTZUYSVXHVXIUXNRZGUXKWEZVXJVXHVWRUXKHZVXIVXIRZVXMVXH
      VXFVWRMHZVXNVXEVXFVWTUTVXHVWSYRHZVXPVXHVWSVWPYRVXGVWTVJZVWNVXCVWQVXFVWTYK
      ZUVEVXQVWSVPHZVXPVWSUVFVWRWPHVXPVXTXJUDWSVWRWPUVGVGYDVQVWRUXJMYCUVHVXHVXI
      UVIVXLVXOGVWRUXKUXLVWRRZUXNVXIVXIVYAUXMVWSBOUXLVWRNYEYFYGYHSGUXKUXNVXIUXO
      VUIVWLYPYDVXHUYNVWPBUVPKZVXIQVXHVWQUYNVYBQTVXDVWQVXFVWTYQVXHUYNVWPBUXIVVC
      UYPVVNVVQVXCVWQVXFVWTUVJVXHVWPVXSUVKZVVOVVQVXCVWQVXFVWTUVLZUVMUVNVXHVXIVW
      PBOKZVYBVXHVWSVWPBOVXRYFVXHVWPWGHBWGHVYEVYBRVYCVXHBVYDUVOVWPBUVQSVSUVRUYR
      VXKUBVXIUXPUYQVXIUYNQYLYHSYSUVSUVTVWNVWQUCYRWEZVXAUCYRWDZVXBUCYRWEVWNVWOW
      GHVYFVWNUYNBUXIVVCUYPVVNVVQYKVVOVVQVJUWAVWOUCUWEVQVVNVYGVVEVVQUDAUCUWBUWC
      VWQVXAUCYRYBSUWDVVOVVRLZJUXPHZUYNJQTZUYSVYHJUXNRZGUXKWEZVYIVVNVVRVYLVVEVV
      NVVRLZUEUJZAHZVYLUEVVNVYOUEUWFVVRUEAUWGXDVYMVYOLZVYNWHZUXKHZJVYQNUKZBOKZR
      ZVYLVYOVYRVYMVYOVYQUXJHZVYQMHZLVYRVYOWUBWUCVYNAUWHVYNUWIUWJVYQUXJMYCYDYJV
      YPVYTVYSJOKZJVYPBJVYSOVVNVVRVYOUTYNVYOWUDJRZVYMVYOVYSPHIVYSQTWUEVYOVYSYTP
      VYNAUWKZWGPYTWKUWLXBUWMVYOIYTVYSQUXEWUFUWNVYSUWPSYJUWOVYKWUAGVYQUXKUXLVYQ
      RZUXNVYTJWUGUXMVYSBOUXLVYQNYEYFYGYHSUWQUWRGUXKUXNJUXOVUIVWLYPYDVYHVVCVYJU
      XIVVCUYPVVNVVRYKUYNUWSVQUYRVYJUBJUXPUYQJUYNQYLYHSUWTUXAUXBYSXTUAUBUXPUXSU
      XCUXDVS $.
  $}

  ${
    $d x A $.  $d k x B $.  $d k x M $.  $d k V $.  $d k x ph $.
    esumsn.1 $e |- ( ( ph /\ k = M ) -> A = B ) $.
    esumsn.2 $e |- ( ph -> M e. V ) $.
    esumsn.3 $e |- ( ph -> B e. ( 0 [,] +oo ) ) $.
    $( The extended sum of a singleton is the term.  (Contributed by Thierry
       Arnoux, 2-Jan-2017.) $)
    esumsn $p   |- ( ph -> sum* k e. { M } A = B ) $=
      ( vx cc0 co wceq a1i cfn wcel syl2anc cxr clt c0 csn cesum cxrs cpnf cicc
      cress cmpt ctsu cuni df-esum eqid snfi wf wss cop sylan2 mpteq2dva fmptsn
      cv elsni eqtr4d wb fsng mpbird fss cpr csup wbr cif cpw cin cres cgsu crn
      snssd wor xrltso 0xr cle wa elxrge0 sylib simpld syl3anc 0fin reseq2 res0
      suppr syl6eq oveq2d xrge00 gsum0 adantl ssid xrge0base ccmn cmnd xrge0cmn
      resmpt ax-mp cmnmnd gsumsn2 sylan9eqr pwsn prssi mp2an eqsstri df-ss mpbi
      fmptpr eqtri mpteq12i syl6eqr rneqd rnpropg eqtr3d supeq1d simprd xrlenlt
      wn mpbid eqidd jca olcd eqif sylibr 3eqtr4rd xrge0tsmsd unieqd unisng syl
      wo 3eqtrd ) AEUAZBDUBZUCKUDUELZUFLZDYNBUGZUHLZUIZCUAZUIZCYOYTMAYNBDUJNAYS
      UUAAYNCYRYQOJYQUKYNOPZAEULZNZAYNUUAYRUMZUUAYPUNYNYPYRUMAUUFYRECUOUAZMZAYR
      DYNCUGZUUGADYNBCDUSZYNPAUUJEMBCMUUJEUTGUPUQAEFPZCYPPZUUGUUIMHIDECFYPURQVA
      AUUKUULUUFUUHVBHIECFYPYRVCQVDACYPIVOYNUUAYPYRVEQAKCVFZRSVGZCKSVHZKCVIZJYN
      VJZOVKZYQYRJUSZVLZVMLZUGZVNZRSVGCARSVPZKRPZCRPZUUNUUPMUVDAVQNUVEAVRNZAUVF
      KCVSVHZAUULUVFUVHVTICWAWBZWCZRKCSWHWDARUVCUUMSATKUOYNCUOVFZVNZUVCUUMAUVKU
      VBAUVKJTYNVFZUVAUGUVBAJTYNKCUVAOORYPTOPZAWENZUUEUVGIUUSTMZUVAKMAUVPUVAYQT
      VMLKUVPUUTTYQVMUVPUUTYRTVLTUUSTYRWFYRWGWIWJYQKWKWLWIWMUUSYNMZAUVAYQYRVMLC
      UVQUUTYRYQVMUVQUUTYRYNVLZYRUUSYNYRWFYNYNUNUVRYRMYNWNDYNYNBWSWTWIWJABYPCDY
      QEFWOYQWPPYQWQPWRYQXAWTGHIXBXCXJJUURUVAUVMUVAUURUUQUVMUUQOUNUURUUQMUUQUVM
      OEXDZUVNUUCUVMOUNWEUUDTYNOXEXFXGUUQOXHXIUVSXKUVAUKXLXMXNAUVNUUCUVLUUMMUVO
      UUETYNKCOOXOQXPXQAUUOCKMVTZUUOXTZCCMZVTZYLCUUPMAUWCUVTAUWAUWBAUVHUWAAUVFU
      VHUVIXRAUVEUVFUVHUWAVBUVGUVJKCXSQYAACYBYCYDUUOCKCYEYFYGYHYIAUULUUBCMICYPY
      JYKYM $.
  $}

  ${
    $d A k x $.  $d B k x $.  $d C x $.  $d k D $.  $d k E $.  $d k ph $.
    $d k V $.  $d k W $.
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
        ( cxad wceq adantr cpnf cpr cesum co wa csn simpr dfsn2 syl5req esumeq1
        preq2 3syl esumsn eqtrd cc0 oveq2 cxr wcel 0xr eleq1 mpbiri xaddid1 syl
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
    $d i k n x $.  $d i n x F $.  $d i k N $.
    esumfzf.1 $e |- F/_ k F $.
    $( Formulating a partial extended sum over integers using the recursive
       sequence builder.  (Contributed by Thierry Arnoux, 18-Oct-2017.) $)
    esumfzf $p |- ( ( F : NN --> ( 0 [,] +oo ) /\ N e. NN )
      -> sum* k e. ( 1 ... N ) ( F ` k ) = ( seq 1 ( +e , F ) ` N ) ) $=
      ( vx cn wcel co c1 cfz cfv cesum cxad wceq wi nfv esumeq1d nfcv wa simpr
      vi vn cc0 cpnf cicc wf cseq caddc oveq2 fveq2 eqeq12d imbi2d nffv cbvesum
      cv csn cz fveq2d 1z a1i 1nn ffvelrn mpan2 esumsn syl5eq fzsn esumeq1 seq1
      ax-mp 3eqtr4g cuz simpl nnuz syl6eleq syl adantr oveq1d cun nfci nff nfan
      seqp1 fzsuc cvv ovex snex cin c0 fzp1disj simplr wss fzssnn ffvelrnd elsn
      sseldi sylib simpll peano2nnd eqeltrd esumsplit oveq2d 3eqtr2rd exp31 a2d
      3eqtrrd nnind impcom ) CFGFUCUDUEHZBUFZICJHZAUOZBKZALZCMBIUGZKZNZXIIUAUOZ
      JHZXLALZXQXNKZNZOXIIIJHZXLALZIXNKZNZOXIIUBUOZJHZXLALZYFXNKZNZOXIIYFIUHHZJ
      HZXLALZYKXNKZNZOXIXPOUAUBCXQINZYAYEXIYPXSYCXTYDYPXRYBXLAYPAPXQIIJUIQXQIXN
      UJUKULXQYFNZYAYJXIYQXSYHXTYIYQXRYGXLAYQAPXQYFIJUIQXQYFXNUJUKULXQYKNZYAYOX
      IYRXSYMXTYNYRXRYLXLAYRAPXQYKIJUIQXQYKXNUJUKULXQCNZYAXPXIYSXSXMXTXOYSXRXJX
      LAYSAPXQCIJUIQXQCXNUJUKULXIIUPZXLALZIBKZYCYDXIUUAYTEUOZBKZELUUBYTXLUUDAEX
      KUUCBUJZEYTRAYTREXLRZAUUCBDAUUCRUMZUNXIUUDUUBEIUQXIUUCINZSUUCIBXIUUHTURIU
      QGZXIUSUTXIIFGZUUBXHGVAFXHIBVBVCVDVEYBYTNZYCUUANUUIUUKUSIVFVIYBYTXLAVGVIU
      UIYDUUBNUSMBIVHVIVJYFFGZXIYJYOUULXIYJYOUULXISZYJSZYNYIYKBKZMHZYHUUOMHZYMU
      UMYNUUPNZYJUUMYFIVKKZGZUURUUMYFFUUSUULXIVLZVMVNZMBIYFWBVOVPUUNYHYIUUOMUUM
      YJTVQUUMUUQYMNYJUUMYMYGYKUPZVRZXLALYHUVCXLALZMHUUQUUMYLUVDXLAUULXIAUULAPZ
      AFXHBDAUBFUVFVSAXHRVTWAZUUMUUTYLUVDNUVBIYFWCVOQUUMYGUVCXLAUVGAYGRAUVCRZYG
      WDGUUMIYFJWEUTUVCWDGUUMYKWFUTYGUVCWGWHNUUMIYFWIUTUUMXKYGGZSZFXHXKBUULXIUV
      IWJUVJYGFXKUUJYGFWKVAIYFWLVIUUMUVITWOWMUUMXKUVCGZSZFXHXKBUULXIUVKWJUVLXKY
      KFUVLUVKXKYKNUUMUVKTAYKWNWPUVLYFUULXIUVKWQWRWSWMWTUUMUVEUUOYHMUUMUVEUVCUU
      DELUUOUVCXLUUDAEUUEEUVCRUVHUUFUUGUNUUMUUDUUOEYKFUUMUUCYKNZSUUCYKBUUMUVMTU
      RUUMYFUVAWRZUUMFXHYKBUULXITUVNWMVDVEXAXEVPXBXCXDXFXG $.
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
      ovex 1nn fzssnn sseldd ffvelrnd ex ralrimi esumcl sylancr eqeltrrd sseldi
      mp1i ralrimiva fnfvrnss nnex ffvelrn fvelrnb eqcom eqeq1d rexbidva bitr4d
      wb syl5bbr biimpa a1i adantlr esummono adantr jca r19.29r breq1 rexlimivw
      biimpar 3syl cpw cfn cin nfesum1 simplll sylancom simplr esumlub ssnnssfz
      nfbr rexrd r19.42v simp-4l reximi sylbir sylan2 rexbii sylibr syl2anc vex
      simp-4r nfel1 simp-5l simpllr inss1 sseli elpwi xrltletr syl3anc reximdva
      rexlimdva mpd breq2d rexxfr2d ad2antrr mpbird supxr2 syl22anc eqcomd ) GU
      BUCUDUEZBUFZUGBHUHZUIZIJUJZGAUKZBULZAUMZUUGUUIIUNZUUMIKDUKZUUMUOLZDUUIMUU
      OUUMJLZUUOUAUKZJLZUAUUINZUPZDUSMUUJUUMOUUGUUHGUQZEUKZUUHULZIKZEGMUUNUVBUU
      HHURULZUQZHUTKUVGVAUGBHVBVCGUVFUUHVDVEVFZUUGUVEEGUUGUVCGKZPZUUFIUVDUBUCVG
      ZUVJHUVCVHUEZUULAUMZUVDUUFABUVCCVIZUVJUVLQKZUULUUFKZAUVLMZUVMUUFKZHUVCVHV
      MZUVJUVPAUVLUUGUVIAAGUUFBCAGRZAUUFRVJZUVIAVKZSZUVJUUKUVLKZUVPUVJUWDPZGUUF
      UUKBUUGUVIUWDVLUWEUVLGUUKHGKZUVLGUNZUWEVNHUVCVOZWDUVJUWDTVPVQVRVSUVLUULAQ
      AUVLRVTZWAZWBWCWEEGIUUHWFWAUUGUUFIUUMUVKUUGGQKZUVPAGMUUMUUFKWGUUGUVPAGUWA
      UUGUUKGKZUVPGUUFUUKBWHZVRVSGUULAQUVTVTWAWCUUGUUPDUUIUUGUUOUUIKZPZUUOUVMOZ
      EGNZUVMUUMUOLZEGMZPUWPUWRPZEGNUUPUWOUWQUWSUUGUWNUWQUUGUWNUVDUUOOZEGNZUWQU
      VBUWNUXBWNUUGUVHEGUUOUUHWIWDUUGUWPUXAEGUWPUVMUUOOUVJUXAUVMUUOWJUVJUVMUVDU
      UOUVNWKWOWLWMWPUUGUWSUWNUUGUWREGUVJUVLUULGAQUWCUWKUVJWGWQUUGUWLUVPUVIUWMW
      RUWFUWGUVJVNUWHWDWSWEWTXAUWPUWREGXBUWTUUPEGUWPUUPUWRUUOUVMUUMUOXCXEXDXFWE
      UUGUVADUSUUGUUOUSKZPZUUQUUTUXDUUQPZUUTUUOUVMJLZEGNZUXEUUOFUKZUULAUMZJLZUX
      IUVMUOLZPZEGNZFGXGZXHXIZNZUXGUXEUXJFUXONZUXKEGNZFUXOMZUXPUXEGUULAQUUOFUXD
      UUQAUUGUXCAUWAUXCAVKSAUUOUUMJAUUORAJRGUULAUVTXJXPSZUWKUXEWGWQUXEUWLUUGUVP
      UUGUXCUUQUWLXKUWMXLUXEUUOUUGUXCUUQXMXQUXDUUQTXNUXEUXRFUXOUXHUXOKZUXEUXHUV
      LUNZEGNZUXRUXHEXOUXEUYCPUXEUYBPZEGNUXRUXEUYBEGXRUYDUXKEGUYDUXHUULUVLAQUXE
      UYBAUXTUYBAVKSUVOUYDUVSWQUYDUWDPZGUUFUUKBUUGUXCUUQUYBUWDXSUYEUVLGUUKUWFUW
      GVNUWHVCZUYDUWDTWCVQUXEUYBTWSXTYAYBWEUXQUXSPUXJUXRPZFUXONUXPUXJUXRFUXOXBU
      XMUYGFUXOUXJUXKEGXRYCYDYEUXEUXMUXGFUXOUXEUYAPZUXLUXFEGUYHUVIPZUUOIKUXIIKU
      VMIKUXLUXFUPUYIUUOUUGUXCUUQUYAUVIYGXQUYIUUFIUXIUVKUYIUXHQKUVPAUXHMUXIUUFK
      FYFUYIUVPAUXHUYHUVIAUXEUYAAUXTAUXHUXOAUXHRZYHSUWBSZUYIUUKUXHKZUVPUYIUYLPZ
      GUUFUUKBUUGUXCUUQUYAUVIUYLYIUYMUXHGUUKUYMUYAUXHUXNKUXHGUNUXEUYAUVIUYLYJUX
      OUXNUXHUXNXHYKYLUXHGYMXFUYIUYLTVPVQVRVSUXHUULAQUYJVTWAWCUYIUUFIUVMUVKUYIU
      VOUVQUVRUVSUYIUVPAUVLUYKUYIUWDUVPUYIUWDPZGUUFUUKBUUGUXCUUQUYAUVIUWDYIUYNU
      VLGUUKUYFUYIUWDTWCVQVRVSUWIWAWCUUOUXIUVMYNYOYPYQYRUUGUUTUXGWNUXCUUQUUGUUS
      UXFUAEUVMUUIGUUFUWJUUGUURUUIKZUVDUUROZEGNZUURUVMOZEGNUVBUYOUYQWNUUGUVHEGU
      URUUHWIWDUUGUYRUYPEGUYRUVMUUROUVJUYPUVMUURWJUVJUVMUVDUURUVNWKWOWLWMUUGUYR
      PUURUVMUUOJUUGUYRTYSYTUUAUUBVRWEDUAUUIUUMUUCUUDUUE $.

    $( Formulating an extended sum over integers using the recursive sequence
       builder.  This version is limited to real valued functions.
       (Contributed by Thierry Arnoux, 19-Oct-2017.) $)
    esumfsupre $p |- ( F : NN --> ( 0 [,) +oo )
      -> sum* k e. NN ( F ` k ) = sup ( ran seq 1 ( + , F ) , RR* , < ) ) $=
      ( vx vy cn cc0 cpnf co cv cfv cxad c1 cxr clt caddc wcel wa cr cmnf cesum
      cico wf cseq crn csup cicc wceq wss icossicc fss mpan2 esumfsup syl cz 1z
      a1i cuz elnnuz ffvelrn sylan2br ge0addcl adantl wbr cle mnfxr pnfxr mnflt
      0re ax-mp pnfge icossioo mp4an ioomax sseqtri simprl sseldi simprr rexadd
      cioo eqcomd syl2anc seqfeq3 rneqd supeq1d eqtr4d ) FGHUBIZBUCZFAJBKAUAZLB
      MUDZUEZNOUFZPBMUDZUEZNOUFWHFGHUGIZBUCZWIWLUHWHWGWOUIWPGHUJFWGWOBUKULABCUM
      UNWHNWNWKOWHWMWJWHDEPLWGBMMUOQWHUPUQDJZMURKQWHWQFQWQBKWGQWQUSFWGWQBUTVAWQ
      WGQZEJZWGQZRZWQWSPIZWGQWHWQWSVBVCWHXARZWQSQZWSSQZXBWQWSLIZUHXCWGSWQWGTHVT
      IZSTNQHNQZTGOVDZHHVEVDZWGXGUIVFVGGSQXIVIGVHVJXHXJVGHVKVJTHGHVLVMVNVOZWHWR
      WTVPVQXCWGSWSXKWHWRWTVRVQXDXERXFXBWQWSVSWAWBWCWDWEWF $.
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
      fmptdF suppss2f tsmsres eqtr3d unieqd df-esum 3eqtr4g ) AUANUBUCOZUDOZEBD
      PZQOZRVHECDPZQOZRBDESCDESAVJVLAVHVKBUEZQOVJVLAVMVIVHQABCUHVMVIUFJECBDIHUG
      UIUJACVGVKVHFBNUKULVHUMTAUNUOVHUPTAUQUOKAECDVGVKGIEVGURLVKUSUTACDEBNGIHMV
      AVBVCVDBDEVECDEVEVF $.
  $}

  ${
    $d k A $.  $d k V $.
    esumpinfval.0 $e |- F/ k ph $.
    esumpinfval.1 $e |- ( ph -> A e. V ) $.
    esumpinfval.2 $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumpinfval.3 $e |- ( ph -> E. k e. A B = +oo ) $.
    $( The value of the extended sum of non-negative terms, with at least one
       infinite term.  (Contributed by Thierry Arnoux, 19-Jun-2017.) $)
    esumpinfval $p |- ( ph -> sum* k e. A B = +oo ) $=
      ( cesum cxr wcel cpnf cle wbr wceq cc0 wa 0xr pnfxr cicc co iccssxr cv ex
      wral ralrimi nfcv esumcl syl2anc sseldi cif nfrab1 wss ssrab2 pnfge ax-mp
      crab a1i ubicc2 mp3an wn lbicc2 ifclda eldif rabid simplbi2 con3and sylbi
      cdif adantl iffalse syl esumss chash cfv cxmu simprbi iftrue esumeq12dvaf
      eqidd cvv ssexd esumcst sylancl clt hashxrcl c0 wrex rabn0 sylibr hashgt0
      xmulpnf1 3eqtrd eqtr3d breq1 breq2 mpbiri adantr iccgelb mp3an12 ifbothda
      wne esumlef eqbrtrrd xgepnf biimpd sylc ) ABCDJZKLZMXINOZXIMPZAQMUAUBZKXI
      QMUCABELCXMLZDBUFXIXMLGAXNDBFADUDZBLZXNHUEUGBCDEDBUHZUIUJUKABCMPZMQULZDJZ
      MXINAXRDBURZXSDJZXTMAYABXSDEFXRDBUMZXQYABUNAXRDBUOUSZGAXPRZXRMQXMMXMLZYEX
      RRQKLZMKLZQMNOZYFSTYGYISQUPUQZQMUTVAZUSQXMLZYEXRVBZRZYGYHYIYLSTYJQMVCVAUS
      VDZAXOBYAVJLZRYMXSQPYPYMAYPXPXOYALZVBRYMXOBYAVEXPXRYQYQXPXRXRDBVFZVGVHVIV
      KXRMQVLVMVNAYBYAMDJZYAVOVPZMVQUBZMAYAYAXSMDFAYAWAYQXSMPZAYQXRUUBYQXPXRYRV
      RXRMQVSVMVKVTAYAWBLZYFYSUUAPAYABEGYDWCZYKYAMDWBYCDMUHWDWEAYTKLZQYTWFOZUUA
      MPAUUCUUEUUDYAWBWGVMAUUCYAWHXCZUUFUUDAXRDBWIUUGIXRDBWJWKYAWBWLUJYTWMUJWNW
      OABXSCDEFXQGYOHXRMCNOZQCNOZXSCNOYEMQMXSCNWPQXSCNWPXRUUHYEXRUUHMMNOZYHUUJT
      MUPUQCMMNWQWRVKYNXNUUIYEXNYMHWSYGYHXNUUISTQMCWTXAVMXBXDXEXJXKXLXIXFXGXH
      $.
  $}

  ${
    $d x y A $.  $d x y F $.  $d x y V $.
    $( Lemma for ~ esumpfinval (Contributed by Thierry Arnoux, 28-Jun-2017.) $)
    esumpfinvallem $p |- ( ( A e. V /\ F : A --> ( 0 [,) +oo ) ) ->
      ( CCfld gsum F ) = ( ( RR*s |`s ( 0 [,] +oo ) ) gsum F ) ) $=
      ( wcel cc0 cpnf co wa ccnfld cress cxrs cvv ovex a1i wceq cxr ax-mp caddc
      cr cxad vy vx cico cgsu cicc fex ancoms cbs cfv wss cmnf cioo clt wbr cle
      wf cc mnfxr pnfxr 0re mnflt pnfge icossioo mp4an ioomax sseqtri ax-resscn
      sstri eqid cnfldbas ressbas2 xrsbas eqtr3i cplusg simprl syl6eleqr simprr
      icossxr cv ge0addcl cnfldadd ressplusg oveqi 3eltr3g syl2anc simpl sseldi
      simpr rexadd eqcomd xrsadd 3eqtr3g wfun ffun syl crn frn syl6sseq cnfldex
      gsumpropd2 0xr ltpnf lbico1 mp3an addid2d addid1d jca gsumress xrge0plusg
      xrge0base ressress mp2an incom icossicc dfss eqtr4i oveq2i eqtr2i iccssxr
      cin mpbi xaddid2 xaddid1 3eqtr4d ) ACDZAEFUCGZBUPZHZIYFJGZBUDGKYFJGZBUDGI
      BUDGKEFUEGZJGZBUDGYHUABYIYJLLLUBYGYEBLDAYFCBUFUGYILDYHIYFJMNYJLDYHKYFJMNY
      IUHUIZYJUHUIZOYHYFYMYNYFUQUJZYFYMOYFSUQYFUKFULGZSUKPDFPDZUKEUMUNZFFUOUNZY
      FYPUJURUSESDZYRUTEVAQYQYSUSFVBQUKFEFVCVDVEVFZVGVHZYFUQYIIYIVIZVJVKQZYFPUJ
      YFYNOEFVRYFPYJKYJVIZVLVKQVMNYHUBVSZYMDZUAVSZYMDZHHZUUFYFDZUUHYFDZUUFUUHYI
      VNUIZGZYMDUUJUUFYMYFYHUUGUUIVOUUDVPZUUJUUHYMYFYHUUGUUIVQUUDVPZUUKUULHZUUF
      UUHRGZYFUUNYMUUFUUHVTRUUMUUFUUHYFLDZRUUMOEFUCMZYFRIYILUUCWAWBQWCZUUDWDWEU
      UJUUKUULUUNUUFUUHYJVNUIZGZOUUOUUPUUQUURUUFUUHTGZUUNUVCUUQUUFSDZUUHSDZUURU
      VDOUUQYFSUUFUUAUUKUULWFWGUUQYFSUUHUUAUUKUULWHWGUVEUVFHUVDUURUUFUUHWIWJWEU
      VATUVBUUFUUHUUSTUVBOUUTYFTKYJLUUEWKWBQWCWLWEYHYGBWMYEYGWHZAYFBWNWOYHBWPZY
      FYMYHYGUVHYFUJUVGAYFBWQWOUUDWRWTYHUBAUQRYFBIYILCEVJWAUUCILDYHWSNYEYGWFZYO
      YHUUBNUVGEYFDZYHEPDYQEFUMUNZUVJXAUSYTUVKUTEXBQEFXCXDNZYHUUFUQDZHZEUUFRGUU
      FOUUFERGUUFOUVNUUFYHUVMWHZXEUVNUUFUVOXFXGXHYHUBAYKTYFBYLYJLCEXJXIYLYFJGZK
      YKYFXTZJGZYJYKLDUUSUVPUVROEFUEMUUTYKYFKLLXKXLUVQYFKJUVQYFYKXTZYFYKYFXMYFY
      KUJZYFUVSOEFXNZYFYKXOYAXPXQXRYLLDYHKYKJMNUVIUVTYHUWANUVGUVLYHUUFYKDZHZEUU
      FTGUUFOZUUFETGUUFOZUWCUUFPDZUWDUWCYKPUUFEFXSYHUWBWHWGZUUFYBWOUWCUWFUWEUWG
      UUFYCWOXGXHYD $.
  $}

  ${
    $d k A $.  $d k ph $.
    esumpfinval.a $e |- ( ph -> A e. Fin ) $.
    esumpfinval.b $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) ) $.
    $( The value of the extended sum of a finite set of non-negative finite
       terms (Contributed by Thierry Arnoux, 28-Jun-2017.) $)
    esumpfinval $p |- ( ph -> sum* k e. A B = sum_ k e. A B ) $=
      ( cc0 cpnf cicc co cgsu csn cuni cle cfn wcel a1i cvv cr cmnf cesum cress
      cxrs cmpt ccnfld csu ctsu df-esum cordt cfv crest xrge0base ccmn xrge0cmn
      xrge00 ctps xrge0tps cv wa cico icossicc sseldi eqid fmptd fisuppfi ctopn
      cdif xrge0topn eqcomi xrhaus ovex resthaus mp2an haustsmsid unieqd syl5eq
      cha unisn syl6eq wf wceq esumpfinvallem syl2anc cc cioo cxr clt wbr mnfxr
      wss pnfxr mnflt ax-mp pnfge icossioo mp4an ioomax sseqtri ax-resscn sstri
      0re gsumfsum 3eqtr2d ) ABCDUAZUCGHIJZUBJZDBCUDZKJZUEXGKJZBCDUFAXDXHLZMZXH
      AXDXFXGUGJZMXKBCDUHAXLXJABXEXGXFNUIUJZXEUKJZOGULUOXFUMPAUNQXFUPPAUQQEADBC
      XEXGADURBPUSZGHUTJZXECGHVAFVBXGVCZVDZABXERGLVGXGEXRVEXFVFUJXNVHVIXNVQPZAX
      MVQPXERPXSVJGHIVKXEXMRVLVMQVNVOVPXHXFXGKVKVRVSABOPBXPXGVTXIXHWAEADBCXPXGF
      XQVDBXGOWBWCABCDEXOXPWDCXPSWDXPTHWEJZSTWFPHWFPZTGWGWHZHHNWHZXPXTWJWIWKGSP
      YBXAGWLWMYAYCWKHWNWMTHGHWOWPWQWRWSWTFVBXBXC $.
  $}

  ${
    $d k l $.  $d l A $.  $d l B $.  $d l ph $.
    esumpfinvalf.1 $e |- F/_ k A $.
    esumpfinvalf.2 $e |- F/ k ph $.
    esumpfinvalf.a $e |- ( ph -> A e. Fin ) $.
    esumpfinvalf.b $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) ) $.
    $( Same as ~ esumpfinval , minus distinct variable restrictions.
       (Contributed by Thierry Arnoux, 28-Aug-2017.) $)
    esumpfinvalf $p |- ( ph -> sum* k e. A B = sum_ k e. A B ) $=
      ( vl cc0 cpnf co cgsu ccnfld wcel nfcv cvv cc wsb cmnf cxrs cicc cmpt csu
      cesum cress csn cuni ctsu df-esum cle cordt cfv cfn xrge0base xrge00 ccmn
      crest xrge0cmn a1i ctps xrge0tps cv cico icossicc sseldi eqid fmptdF cdif
      fisuppfi ctopn xrge0topn eqcomi cha xrhaus ovex resthaus mp2an haustsmsid
      wa unieqd syl5eq unisn syl6eq wf wceq esumpfinvallem syl2anc csb cioo cxr
      wi cr clt wbr wss mnfxr pnfxr 0re mnflt ax-mp pnfge icossioo mp4an ioomax
      sseqtri ax-resscn sstri sbt sbim sban sbf clelsb3f anbi12i bitri sbsbc wb
      wsbc sbcel1g imbi12i mpbi gsumfsum nfcsb1v csbeq1a cbvmptf oveq2i 3eqtr4g
      vex cbvsum 3eqtr2d ) ABCDUEZUAJKUBLZUFLZDBCUCZMLZNYNMLZBCDUDZAYKYOUGZUHZY
      OAYKYMYNUILZUHYSBCDUJAYTYRABYLYNYMUKULUMZYLURLZUNJUOUPYMUQOAUSUTYMVAOAVBU
      TGADBCYLYNFEDYLPADVCBOZVTZJKVDLZYLCJKVEHVFYNVGZVHZABYLQJUGVIYNGUUGVJYMVKU
      MUUBVLVMUUBVNOZAUUAVNOYLQOUUHVOJKUBVPYLUUAQVQVRUTVSWAWBYOYMYNMVPWCWDABUNO
      BUUEYNWEYPYOWFGADBCUUEYNFEDUUEPHUUFVHBYNUNWGWHANIBDIVCZCWIZUCZMLBUUJIUDYP
      YQABUUJIGUUDCROZWLZDISZAUUIBOZVTZUUJROZWLZUUMDIUUDUUERCUUEWMRUUETKWJLZWMT
      WKOKWKOZTJWNWOZKKUKWOZUUEUUSWPWQWRJWMOUVAWSJWTXAUUTUVBWRKXBXATKJKXCXDXEXF
      XGXHHVFXIUUNUUDDISZUULDISZWLUURUUDUULDIXJUVCUUPUVDUUQUVCADISZUUCDISZVTUUP
      AUUCDIXKUVEAUVFUUOADIFXLIDBEXMXNXOUVDUULDUUIXRZUUQUULDIXPUUIQOUVGUUQXQIYH
      DUUICRQXSXAXOXTXOYAYBYNUUKNMDIBCUUJEIBPZICPZDUUICYCZDUUICYDZYEYFBCUUJDIUV
      KUVHEUVIUVJYIYGYJ $.
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
    $( The value of the extended sum of infinitely many terms greater than
       one.  (Contributed by Thierry Arnoux, 29-Jun-2017.) $)
    esumpinfsum $p |- ( ph -> sum* k e. A B = +oo ) $=
      ( cxr wcel cpnf cle wbr cc0 cesum wceq cicc co iccssxr wral cv ex ralrimi
      esumcl syl2anc sseldi chash cfv cxmu clt 0xr xrltle sylancr mpd pnfge syl
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
      ( cn c1 cr wcel wa cc0 cpnf wceq cle wbr syl vb vx vy vs vm vz cpw cfn cv
      cin csu cmpt crn cxr clt csup caddc cseq cesum wor xrltso a1i nnuz cz cfv
      1z co weq eqcom 3imtr3i cbvmptv fmptd ffvelrnda elrege0 simplbi serfre wf
      cico adantr simpr peano2nnd ffvelrnd simprbi addge01d mpbid syl6eleq wral
      cuz wrex syl2anc cmnf wss pnfxr ax-mp sseldi cfz cdm simpll elfznn adantl
      recnd fsumser fzfid adantlr ralrimiva breq2 rspcev wn elrnmpti sylan2 imp
      eqid ex breq1 rexlimdva sylan2b simplr fsumrecl ad2antrr simprr wne mpbir
      c0 wfn eqeq2d simpr1r 3anassrs wb w3a 0xr elin mpbir2an sumeq1 xrlelttric
      mp2an wo mpan mpjaodan cvv cgsu seqp1 breqtrrd cioo mnfxr 0re mnflt pnfge
      fvmpt2 icossioo mp4an ioomax sseqtri feqmptd cc eqcomd mpteq2dva eqeltrrd
      eqtr2d isumrecl sseqtr4i isumless eqbrtrrd ralbidv climsup climrecl rexrd
      cli fzssuz sumex ssnnssfz fsumless reximdv rexbidv syl5ibrcom inss2 inss1
      elpwid sseldd eqeltrd frn 1nn ne0i dm0rn0 eqeq1d syl5bbr necon3bid mpbiri
      fdm seqfn fneq2i dffn5 mpbi r19.29 biimparc rexlimivw reximi fveq2 sylibr
      fvex ad2ant2r suprub syl31anc letrd rexlimddv lenltd pnfnlt notbid mpbird
      ad3antrrr pm2.21dd simplll simpr1l elico1 syl3anbrc simprl suprlub biimpa
      3jca syl21anc wi ssriv ovex elpw fzfi eqtr4d ssrdv ssrexv syldan syl12anc
      3imtr4g simplrl xgepnf orbi1d 0elpw 0fin sum0 eqcomi ad2antrl eqsupd nfcv
      nnex cicc icossicc ccnfld cxrs cress elex esumpfinvallem gsumfsum esumval
      nfv eqtr3d isumclim 3eqtr4d ) AUAJUGZUHUJZUAUIZBDUKZULZUMZUNUOUPUQFJCULZK
      URZUMZLUOUPZJBDUSJBDUKZAUBUCUNVUTVVDUOUNUOUTAVAVBAVVDAVVDEVVBKJVCKVDMZAVF
      VBZAUDEVVBKJVCVVGAUBVVAKJVCVVGAUBUIZJMNVVHVVAVEZOPVRVGZMZVVILMZAJVVJVVHVV
      AADJBVVJVVAGFDJCBDFVHBCQFDVHCBQHDUIZFUIVIBCVIVJVKZVLZVMVVKVVLOVVIRSVVIVNV
      OTVPZAEUIZJMZNZVVQVVBVEZVVTVVQKUQVGZVVAVEZUQVGZVWAVVBVEZRVVSOVWBRSZVVTVWC
      RSVVSVWBVVJMZVWEVVSJVVJVWAVVAAJVVJVVAVQVVRVVOVSVVSVVQAVVRVTZWAWBZVWFVWBLM
      ZVWEVWBVNZWCTVVSVVTVWBAJLVVQVVBVVPVMZVVSVWFVWIVWHVWFVWIVWEVWJVOTWDWEVVSVV
      QKWHVEZMVWDVWCQVVSVVQJVWLVWGVCWFZUQVVAKVVQUUATUUBAVVELMVVTVVERSZEJWGZVVTU
      DUIZRSZEJWGZUDLWIZABDVVAKJVCVVGAVVMJMZNZVWTBVVJMZVVMVVAVEBQZAVWTVTGDJBVVJ
      VVAVVNUUHWJZVXAVVJLBVVJWKPUUCVGZLWKUNMPUNMZWKOUOSZPPRSZVVJVXEWLUUDWMOLMVX
      GUUEOUUFWNVXFVXHWMPUUGWNWKPOPUUIUUJUUKUULZGWOZAEJKVVQWPVGZBDUKZULZVVBUVGW
      QZAVVBEJVVTULZVXMAEJLVVBVVPUUMAEJVVTVXLVVSVXLVVTVVSBDVVAKVVQVVSVVMVXKMZNZ
      AVWTVXCAVVRVXPWRZVXPVWTVVSVVMVVQWSZWTZVXDWJVWMVXQAVWTBUUNMVXRVXTVXABVXJXA
      ZWJXBZUUOUUPUURIUUQZUUSAVWNEJVVSVXLVVTVVERVYBVVSVXKBDVVAKJVCVVFVVSVFVBVVS
      KVVQXCVXKJWLZVVSVXKVWLJKVVQUVHVCUUTVBAVWTVXCVVRVXDXDAVWTBLMZVVRVXJXDVVSVW
      TNVXBOBRSZAVWTVXBVVRGXDVXBVYEVYFBVNZWCZTAVVBVXNMVVRVYCVSUVAUVBXEVWRVWOUDV
      VELVWPVVEQVWQVWNEJVWPVVEVVTRXFUVCXGWJZUVDZVWKUVEZUVFZAVVHVUTMZNZVVHVVDRSZ
      VVDVVHUOSXHVYNVVHKUEUIZWPVGZBDUKZRSZVYOUEJVYMAVVHVURQZUAVUPWIZVYSUEJWIZUA
      VUPVURVVHVUSVUSXLZVUQBDUVIZXIZAWUAWUBAVYTWUBUAVUPAVUQVUPMZNZWUBVYTVURVYRR
      SZUEJWIZWUFAVUQVYQWLZUEJWIZWUIVUQUEUVJAWUKWUIAWUJWUHUEJAWUJWUHAWUJNZVYQBV
      UQDWULKVYPXCAVVMVYQMZVYEWUJAWUMNZVXBVYEWUMAVWTVXBVVMVYPWSZGXJZVXBVYEVYFVY
      GVOZTZXDAWUMVYFWUJWUNVXBVYFWUPVYHTXDAWUJVTUVKXMUVLXKXJVYTVYSWUHUEJVVHVURV
      YRRXNUVMUVNXOXKXPVYNVYPJMZVYSNZNZVVHVYRVVDVYNVVHLMZWUTVYMAWUAWVBWUEAWUAWV
      BAVYTWVBUAVUPWUGVYTWVBWUGVYTNVVHVURLWUGVYTVTWUGVURLMVYTWUGVUQBDWUGVUPUHVU
      QVUOUHUVOAWUFVTWOZWUGVVMVUQMZNZVXBVYEWVEAVWTVXBAWUFWVDWRWVEVUQJVVMWVEVUQJ
      WVEVUPVUOVUQVUOUHUVPAWUFWVDXQWOUVQWUGWVDVTUVRGWJZWUQTZXRVSUVSXMXOXKXPZVSA
      VYRLMVYMWUTAVYQBDAKVYPXCWURXRXSAVVDLMZVYMWUTVYKXSVYNWUSVYSXTWVAVVCLWLZVVC
      YCYAZUFUIZVWPRSZUFVVCWGZUDLWIZVYRVVCMZVYRVVDRSAWVJVYMWUTAJLVVBVQZWVJVVPJL
      VVBUVTTZXSAWVKVYMWUTAWVKJYCYAZKJMWVSUWAJKUWBWNAVVCYCJYCVVCYCQVVBWQZYCQAJY
      CQVVBUWCAWVTJYCAWVQWVTJQVVPJLVVBUWHTUWDUWEUWFUWGZXSAWVOVYMWUTAVWSWVOVYIVW
      RWVNUDLVWRWVMUFVVCWVLVVCMVWRWVLVVTQZEJWIZWVMEJVVTWVLVVBVVBJYDZVVBVXOQWWDV
      VBVWLYDZVVFWWEVFUQVVAKUWIWNJVWLVVBVCUWJYBEJVVBUWKUWLZVVQVVBUWSZXIVWRWWCNV
      WQWWBNZEJWIWVMVWQWWBEJUWMWWHWVMEJWWBWVMVWQWVLVVTVWPRXNUWNUWOTXPXEUWPTZXSA
      WUSWVPVYMVYSAWUSNZVYRVVTQZEJWIZWVPWWJWUSVYRVYPVVBVEZQZWWLAWUSVTZWWJBDVVAK
      VYPWWJWUMNZAVWTVXCAWUSWUMWRZWUMVWTWWJWUOWTZVXDWJWWJVYPJVWLWWOVCWFWWPBWWPV
      XBVYEWWPAVWTVXBWWQWWRGWJWUQTXAXBWWKWWNEVYPJEUEVHVVTWWMVYRVVQVYPVVBUWQYEXG
      WJEJVVTVYRVVBWWFWWGXIUWRUWTUDUFVVCVYRUXAUXBUXCUXDVYNVVHVVDWVHAWVIVYMVYKVS
      UXEWEAVVHUNMZVVHVVDUOSZNZNZOVVHRSZVVHUCUIZUOSZUCVUTWIZVVHOUOSZWXBWXCNZVVH
      PQZWXFVVHPUOSZWXHWXINZWWTWXFAWXAWXCWXIWWTWWSWWTWXCWXIAYFYGWXKWWTXHZPVVDUO
      SZXHZWXKVVDUNMZWXNAWXOWXAWXCWXIVYLUXIVVDUXFTWXIWXLWXNYHWXHWXIWWTWXMVVHPVV
      DUOXNUXGWTUXHUXJWXHWXJNZAVVHVVJMZWWTWXFAWXAWXCWXJUXKWXPWWSWXCWXJWXQAWXAWX
      CWXJWWSWWSWWTWXCWXJAUXLYGWXBWXCWXJXQWXHWXJVTOUNMZVXFWXQWWSWXCWXJYIYHYJWMO
      PVVHUXMYOUXNAWXAWXCWXJWWTWWSWWTWXCWXJAYFYGAWXQWWTNZWXEUCVVCWIZWXFAWXSNZWV
      JWVKWVOYIZWVBWWTWXTWYAWVJWVKWVOAWVJWXSWVRVSAWVKWXSWWAVSAWVOWXSWWIVSUXRWYA
      VVJLVVHVXIAWXQWWTUXOWOAWXQWWTXTWYBWVBNWWTWXTUDUFUCVVCVVHUXPUXQUXSAWXTWXFA
      VVCVUTWLWXTWXFUXTAUCVVCVUTAWXDVVTQZEJWIWXDVURQZUAVUPWIZWXDVVCMWXDVUTMAWYC
      WYEEJVVSWYCWYEVVSWYCNZVXKVUPMZWXDVXLQZWYEWYGWYFWYGVXKVUOMZVXKUHMWYIVYDDVX
      KJVXSUYAVXKJKVVQWPUYBUYCYBKVVQUYDVXKVUOUHYKYLVBWYFWXDVVTVXLVVSWYCVTVVSVXL
      VVTQWYCVYBVSUYEWYDWYHUAVXKVUPVUQVXKQVURVXLWXDVUQVXKBDYMYEXGWJXMXOEJVVTWXD
      VVBWWFWWGXIUAVUPVURWXDVUSWUCWUDXIUYJUYFWXEUCVVCVUTUYGTXKUYHUYIWXHWWSWXIWX
      JYPZAWWSWWTWXCUYKWWSPVVHRSZWXJYPZWYJVXFWWSWYLWMPVVHYNYQWWSWYKWXIWXJVVHUYL
      UYMWETYRWXGWXFWXBOVUTMZWXGWXFWYMOVURQZUAVUPWIZYCVUPMZOYCBDUKZQZWYOWYPYCVU
      OMYCUHMJUYNUYOYCVUOUHYKYLWYQOBDUYPUYQWYNWYRUAYCVUPVUQYCQVURWYQOVUQYCBDYMY
      EXGYOUAVUPVUROVUSWUCWUDXIYBWXEWXGUCOVUTWXDOVVHUOXFXGYQWTWWSWXCWXGYPZAWWTW
      XRWWSWYSYJOVVHYNYQUYRYRUYSAUAJBVURDYSADVUKDJUYTJYSMAVUAVBVXAVVJOPVUBVGZBO
      PVUCGWOWUGVUDDVUQBULZYTVGZVUEWYTVUFVGXUAYTVGZVURWUGVUQYSMZVUQVVJXUAVQXUBX
      UCQWUFXUDAVUQVUPVUGWTWUGDVUQBVVJXUAWVFXUAXLVLVUQXUAYSVUHWJWUGVUQBDWVCWVEB
      WVGXAVUIVULVUJABVVDDVVAKJVCVVGVXDVYAVYJVUMVUN $.
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
      ( c1 cfz co cesum cc0 cle wbr cxr wcel cpnf cvv cn cxad cicc iccssxr wral
      caddc ovex cv elfznn wa cico icossicc sseldi sylan2 ralrimiva nfcv esumcl
      a1i syl2anc xrleid syl cuz adantr peano2nn nnuz syl6eleq fzss1 3syl simpr
      cfv wss sseldd syldan elxrge0 simprbi wi 0xr xle2add syl22anc mp2and wceq
      xaddid1 eqcomd cun eluzfz fzsplit esumeq1 nfv clt c0 nnre ltp1d esumsplit
      cin fzdisj eqtrd 3brtr4d ) AIDJKZBCLZMUAKZWRDIUEKZEJKZBCLZUAKZWRIEJKZBCLZ
      NAWRWRNOZMXBNOZWSXCNOZAWRPQZXFAMRUBKZPWRMRUCZAWQSQZBXJQZCWQUDWRXJQXLAIDJU
      FUQZAXMCWQCUGZWQQAXOTQZXMXODUHAXPUIMRUJKXJBMRUKHULZUMZUNWQBCSCWQUOZUPURUL
      ZWRUSUTAXBXJQZXGAXASQZXMCXAUDYAYBAWTEJUFUQZAXMCXAAXOXAQZXPXMAYDUIZXOXDQXP
      YEXAXDXOYEDTQZWTIVAVIZQXAXDVJAYFYDFVBYFWTTYGDVCVDVEWTIEVFVGAYDVHVKXOEUHUT
      XQVLZUNXABCSCXAUOZUPURZYAXBPQZXGXBVMVNUTAXIMPQZXIYKXFXGUIXHVOXTYLAVPUQXTA
      XJPXBXKYJULWRMWRXBVQVRVSAWSWRAXIWSWRVTXTWRWAUTWBAXEWQXAWCZBCLZXCADXDQZXDY
      MVTXEYNVTADYGQEDVAVIQYOADTYGFVDVEGDIEWDURDIEWEXDYMBCWFVGAWQXABCACWGXSYIXN
      YCAYFDWTWHOWQXAWMWIVTFYFDDWJWKIDWTEWNVGXRYHWLWOWP $.
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
       preserves extended sums (Contributed by Thierry Arnoux, 29-Jun-2017.) $)
    esumcocn $p |- ( ph -> ( C ` sum* k e. A B ) = sum* k e. A ( C ` B ) ) $=
      ( cfv wcel cc0 co xrge0base cesum nfv nfcv cv wa cpnf cicc ccn cxrs cress
      wf ctps cuni xrge0tps cle cordt crest ctopn xrge0topn eqtr4i tpsuni ax-mp
      wceq cnf adantr ffvelrnd cmpt ccom ctsu ccmn xrge0cmn cmnd cxad wral cmhm
      syl a1i cmnmnd 3expib ralrimivv w3a xrge0plusg xrge00 ismhm biimpri eqidd
      syl23anc fmpt3d esumel tsmsmhm cofmpt oveq2d eleqtrd esumid eqcomd ) ADEF
      PZGUADEGUAZFPZADWPWRGIAGUBZGDUCZKAGUDDQZUERUFUGSZXBEFAXBXBFUKZXAAFHHUHSQX
      CMFHHXBXBUIXBUJSZULQZXBHUMVCUNXBHXDTHUOUPPXBUQSXDURPJUSUTZVAVBZXGVDVPZVEL
      VFAWRXDFGDEVGZVHZVISXDGDWPVGZVISADXBFXIXDXDHHIWQTXFXFXDVJQZAVKVQZXEAUNVQZ
      XMXNAXDVLQZXOXCBUDZCUDZVMSFPXPFPXQFPVMSVCZCXBVNBXBVNZRFPRVCZFXDXDVOSQZXOA
      XLXOVKXDVRVBVQZYBXHAXRBCXBXBAXPXBQXQXBQXROVSVTNYAXOXOUEXCXSXTWAUEBCXBXBVM
      VMXDXDFRRTTWBWBWCWCWDWEWGMKAGDEXBXIAXIWFLWHADEGIWSWTKLWIWJAXJXKXDVIAGDEXB
      XBFXHLWKWLWMWNWO $.
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
      ( vz cc0 cpnf co cxmu cfv wceq wcel a1i fvmptd cvv vx cesum cicc cmpt cle
      vy cv cordt crest eqid xrge0mulc1cn eqidd oveq1 cxr icossxr sseldi xmul02
      cico syl sylan9eqr wbr 0xr pnfxr pnfge ax-mp lbicc2 mp3an w3a simp2 simp3
      cxad icossicc 3ad2ant1 xrge0adddir syl3anc simpr oveq1d ge0xaddcl 3adant1
      wa ovex oveq12d 3eqtr4d esumcocn wral ralrimiva syl2anc esumeq2dv 3eqtr3d
      nfcv esumcl ) ABCEUBZJKLUCMZJUGZDNMZUDZOBCWPOZEUBWLDNMZBCDNMZEUBAUAUFBCWP
      EUEUHOWMUIMZFWTUJZGHAJDWPWTXAWPUJIUKAJKWOKWMWPWMAWPULZWNKPAWOKDNMZKWNKDNU
      MADUNQXCKPAKLURMZUNDKLUOIUPDUQUSUTKWMQZAKUNQZLUNQKLUEVAZXEVBVCXFXGVBKVDVE
      KLVFVGRZXHSAUAUGZWMQZUFUGZWMQZVHZXIXKVKMZDNMZXIDNMZXKDNMZVKMZXNWPOXIWPOZX
      KWPOZVKMXMXJXLDWMQXOXRPAXJXLVIZAXJXLVJZXMXDWMDKLVLAXJDXDQXLIVMUPXIXKDVNVO
      XMJXNWOXOWMWPTXMWPULZXMWNXNPZVTWNXNDNXMYDVPVQXJXLXNWMQAXIXKVRVSXOTQXMXNDN
      WARSXMXSXPXTXQVKXMJXIWOXPWMWPTYCXMWNXIPZVTWNXIDNXMYEVPVQYAXPTQXMXIDNWARSX
      MJXKWOXQWMWPTYCXMWNXKPZVTWNXKDNXMYFVPVQYBXQTQXMXKDNWARSWBWCWDAJWLWOWRWMWP
      TXBAWNWLPZVTWNWLDNAYGVPVQABFQCWMQZEBWEWLWMQGAYHEBHWFBCEFEBWJWKWGWRTQAWLDN
      WARSABWQWSEAEUGBQVTZJCWOWSWMWPTYIWPULYIWNCPZVTWNCDNYIYJVPVQHWSTQYICDNWARS
      WHWI $.

    $( An extended sum multiplied by a constant.  (Contributed by Thierry
       Arnoux, 6-Jul-2017.) $)
    esummulc2 $p |- ( ph ->
                           ( C *e sum* k e. A B ) = sum* k e. A ( C *e B ) ) $=
      ( cesum cxmu co cxr wcel wceq cc0 cpnf sseldi syl2anc xmulcom cico esumcl
      icossxr cicc iccssxr wral ralrimiva nfcv esummulc1 cv wa adantr esumeq2dv
      3eqtrd ) ADBCEJZKLZUODKLZBCDKLZEJBDCKLZEJADMNZUOMNUPUQOAPQUALMDPQUCIRZAPQ
      UDLZMUOPQUEZABFNCVBNZEBUFUOVBNGAVDEBHUGBCEFEBUHUBSRDUOTSABCDEFGHIUIABURUS
      EAEUJBNZUKZCMNUTURUSOVFVBMCVCHRAUTVEVAULCDTSUMUN $.
  $}

  ${
    $d k A $.  $d x y k C $.  $d k V $.  $d x y k ph $.
    esumdivc.a $e |- ( ph -> A e. V ) $.
    esumdivc.b $e |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) ) $.
    esumdivc.c $e |- ( ph -> C e. RR+ ) $.
    $( An extended sum divided by a constant.  (Contributed by Thierry Arnoux,
       6-Jul-2017.) $)
    esumdivc $p |- ( ph -> ( sum* k e. A B /e C ) = sum* k e. A ( B /e C ) ) $=
      ( cesum c1 cxdiv co cc0 cpnf wcel wceq syl3anc sseldi cxr cxmu cr wne 1re
      cdiv cico a1i rpred rpne0d rexdiv cioo ioossico eqsstr3i rpreccld eqeltrd
      crp ioorp esummulc1 cicc iccssxr wral ralrimiva esumcl syl2anc xdivrec cv
      nfcv wa adantr esumeq2dv 3eqtr4d ) ABCEJZKDLMZUAMZBCVMUAMZEJVLDLMZBCDLMZE
      JABCVMEFGHAVMKDUEMZNOUFMZAKUBPZDUBPZDNUCZVMVRQVTAUDUGADIUHZADIUIZKDUJRAUP
      VSVRUPNOUKMVSUQNOULUMADIUNSUOURAVLTPWAWBVPVNQANOUSMZTVLNOUTZABFPCWEPZEBVA
      VLWEPGAWGEBHVBBCEFEBVGVCVDSWCWDVLDVERABVQVOEAEVFBPZVHZCTPWAWBVQVOQWIWETCW
      FHSAWAWHWCVIAWBWHWDVICDVERVJVK $.
  $}

  $( Lemma for ~ hasheuni (Contributed by Thierry Arnoux, 19-Nov-2016.) $)
  hashf2 $p |- # : _V --> ( 0 [,] +oo ) $=
    ( vx cvv cn0 cpnf csn cun chash wf cc0 cicc co wss hashf cv cxr cle wbr 0xr
    wcel ax-mp cz nn0z zre rexr 3syl nn0ge0 elxrge0 sylanbrc ssriv pnfxr ubicc2
    cr pnfge mp3an snssi unssi fss mp2an ) BCDEZFZGHUTIDJKZLBVAGHMCUSVAACVAANZC
    SZVBOSZIVBPQVBVASVCVBUASVBULSVDVBUBVBUCVBUDUEVBUFVBUGUHUIDVASZUSVALIOSZDOSI
    DPQZVERUJVFVGRIUMTIDUKUNDVAUOTUPBUTVAGUQUR $.

  ${
    $d x A $.  $d x V $.
    $( The cardinality of a disjoint union, not necessarily finite. cf.
       ~ hashuni .  (Contributed by Thierry Arnoux, 19-Nov-2016.)  (Revised by
       Thierry Arnoux, 2-Jan-2017.)  (Revised by Thierry Arnoux,
       20-Jun-2017.) $)
    hasheuni $p |- ( ( A e. V /\ Disj_ x e. A x )
                                   -> ( # ` U. A ) = sum* x e. A ( # ` x ) ) $=
      ( wcel wa cfn chash cesum wceq wss nfv cc0 cpnf co wral wn cvv a1i c0 c1
      cv wdisj cuni cfv w3a nfdisj1 nf3an simp2 simp3 simp1 hashunif simpl cico
      csu dfss3 cn0 hashcl cr cle nn0re nn0ge0 elrege0 sylanbrc ralimi r19.21bi
      wbr sylbi adantll esumpfinval 3adant1 eqtr4d 3adant1l 3expa uniexg notbii
      syl wrex rexnal bitr4i wi elssuni ssfi expcom rexlimiv hashinf syl2an vex
      con3d mpan reximi nfre1 nfan cicc hashf2 ffvelrn mp2an esumpinfval sylan2
      simpr 3adant2 3adant1r pm2.61dan cpw pwfi pwuni mpan2 con3i crab cxad cun
      wf wtru nftru wo unrab exmid rgenw rabid2 mpbir eqtr4i trud nfrab1 rabexg
      esumeq1d cin rabnc esumsplit syl5eqr adantr cdif csn dfrab3 hasheq0 ax-mp
      cab wb abbii syl2anc wne cxr df-sn ineq2i eqtri snfi inss2 eqeltri difinf
      notrab eleq1i sylnib rabid sylib simprd biimpri necon3bi hashge1 1re 0lt1
      rexri esumpinfsum oveq2d cmnf iccssxr ralrimiva esumcl sseldi xrge0neqmnf
      clt xaddpnf1 3eqtrd adantlr ) BCDZABAUAZUBZEZBFDZBUCZGUDZBUVMGUDZAHZIZUVO
      UVPEBFJZUWAUVOUVPUWBUWAUVNUVPUWBUWAUVLUVNUVPUWBUEZUVRBUVSAUNZUVTUWCABUVNU
      VPUWBAABUVMUFUVPAKUWBAKUGUVNUVPUWBUHUVNUVPUWBUIUVNUVPUWBUJUKUVPUWBUVTUWDI
      UVNUVPUWBEBUVSAUVPUWBULUWBUVMBDZUVSLMUMNDZUVPUWBUWFABUWBUVMFDZABOZUWFABOA
      BFUOZUWGUWFABUWGUVSUPDZUWFUVMUQUWJUVSURDLUVSUSVFUWFUVSUTUVSVAUVSVBVCVPVDV
      GVEVHVIVJVKVLVMUVOUVPUWBPZUWAUVLUVPUWKUWAUVNUVLUWKUWAUVPUVLUWKEUVRMUVTUVL
      UVQQDZUVQFDZPZUVRMIZUWKBCVNZUWKUWGPZABVQZUWNUWKUWHPUWRUWBUWHUWIVOUWGABVRV
      SZUWQUWNABUWEUVMUVQJZUWQUWNVTUVMBWAUWTUWMUWGUWMUWTUWGUVQUVMWBWCWHVPWDVGUV
      QQWEZWFUWKUVLUVSMIZABVQZUVTMIUWKUWRUXCUWSUWQUXBABUVMQDZUWQUXBAWGZUVMQWEWI
      WJVGUVLUXCEZBUVSACUVLUXCAUVLAKZUXBABWKWLUVLUXCULUVSLMWMNZDZUXFUWEEQUXHGXK
      UXDUXIWNUXEQUXHUVMGWOWPZRUVLUXCWSWQWRVKWTXAVMXBUVLUVPPZUWAUVNUVLUXKEZUVRM
      UVTUVLUWLUWNUWOUXKUWPUWMUVPUWMUVQXCZFDZUVPUVQXDUXNBUXMJUVPBXEUXMBWBXFVGXG
      UXAWFUXLUVTUVSLIZABXHZUVSAHZUXOPZABXHZUVSAHZXINZUXQMXINZMUVLUVTUYAIUXKUVL
      UVTUXPUXSXJZUVSAHZUYAUYDUVTIXLUYCBUVSAAXMUYCBIXLUYCUXOUXRXNZABXHZBUXOUXRA
      BXOBUYFIUYEABOUYEABUXOXPXQUYEABXRXSXTRYDYAUVLUXPUXSUVSAUXGUXOABYBZUXRABYB
      ZUXOABCYCZUXRABCYCZUXPUXSYESIUVLUXOABYFRUXIUVLUVMUXPDZEUXJRUXIUVLUVMUXSDZ
      EUXJRYGYHYIUXLUXTMUXQXIUXLUXSUVSATQUXLAKUYHUVLUXSQDUXKUYJYIUXLBUXPYJZFDZU
      XSFDUXLUXKUXPFDZUYNPUVLUXKWSUYOUXLUXPBSYKZYEZFUXPBUXOAYOZYEUYQUXOABYLUYRU
      YPBUYRUVMSIZAYOUYPUXOUYSAUXDUXOUYSYPUXEUVMQYMYNZYQASUUAXTUUBUUCUYPFDUYQUY
      PJUYQFDSUUDBUYPUUEUYPUYQWBWPUUFRBUXPUUGYRUYMUXSFUXOABUUHUUIUUJUXIUXLUYLEZ
      UXJRVUAUXDUVMSYSZTUVSUSVFUXDVUAUXERVUAUXRVUBVUAUWEUXRVUAUYLUWEUXREUXLUYLW
      SUXRABUUKUULUUMUXOUVMSUXOUYSUYTUUNUUOVPUVMQUUPYRTYTDUXLTUUQUUSRLTUVHVFUXL
      UURRUUTUVAUXLUXQYTDUXQUVBYSZUYBMIUXLUXHYTUXQLMUVCUXLUXPQDZUXIAUXPOUXQUXHD
      ZUVLVUDUXKUYIYIUXLUXIAUXPUXIUXLUYKEUXJRUVDUXPUVSAQUYGUVEYRZUVFUXLVUEVUCVU
      FUXQUVGVPUXQUVIYRUVJVKUVKXB $.
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
      ( vl cpnf wcel cn wbr wceq wa c1 vx vy vz cc0 cico co wral cesum clm wrex
      cfv cli csu nnuz cz 1z a1i simpr cv cc cmnf cxr clt cle pnfxr ax-mp pnfge
      cr wss wi weq eleq1d adantl imp sseldi adantlr cfz cmpt fzfid esumpfinval
      elfznn sylan2 syl5eq wf fmptd adantr simplll eqidd eqcom sylancom elrege0
      fvmptd sylib caddc wfn cvv ovex simpll syl2anc ralrimiva nfcv sylancr syl
      esumcl mpbir eqtrd wb mpbid breqtrrd nnzd uzid 3syl oveq2 esumeq1 simp-4l
      cuz cfn nfv nnex cgsu simplr eqid breq2d reximdva mp2an rspce cres anbi2d
      cxp eleq1 imbi12d nfan esumpinfval chvarv ex ctopon 0xr mp3an syldan wo
      cdm mnfxr 0re mnflt icossioo mp4an ioomax sseqtri ax-resscn sstri cbvralv
      cioo rsp sylbir mpteq2dva fsumcl fvmpt2d isumclim3 fsumrp0cl eqeltrd cicc
      3imtr3i simpld cseq ffn fneq2i syl6eleq fsumser eqfnfvd eqeltrrd isumrecl
      seqfn simprd isumge0 sylanbrc ssid lmlimxrge0 mpbird esumpcvgval peano2uz
      syl5eqelr wn esumpmono eqtr4d cbvmptv eqtr4i w3a simpr3 peano2nnd 3brtr4d
      3anassrs lmdvglim cpw cin crn csup ccnfld cxrs cress inss1 esumpfinvallem
      elpwid sseldd inss2 gsumfsum eqtr3d esumval lmdvg r19.21bi fveq2d reximia
      nnz rspcdv ad2antrr ffvelrnd ltle esumex sylibd fzssuz sseqtr4i elpw fzfi
      mpd elin mpbir2an sumex sumeq1 elrnmpt1s mpan rexlimivw adantllr fsumrecl
      breq2 rexrd frn supxrunb1 pm2.61dan csn reseq1i wsb anbi12d fveq2 reseq2d
      sbequ12r xpeq1d eqeq12d nfs1v simpllr elnnuz eluzfz sbequ12 mpteq12 sylan
      sylanb uznnssnn fconstmpt 3eqtr4d mpdan cordt crest ctopn xrge0topn eqtri
      resmpt letopon iccssxr eqeltri ubicc2 lmconst syl3anc breq1 biimprd mpan9
      resttopon cpm elfvexd cnex nnsscn elpm2r syl22anc lmres biimpar rexlimdva
      nfre1 eliccelico r19.30 eqeq1d cbvrexv orbi2i sylibr mpjaodan ) ACUDNUEUF
      ZOZEPUGZGPBDUHZHUIUKZQZBNRZDPUJZAVWNSZGULUUAZOZVWQVWTVXBSZGPBDUMZVWOVWPVX
      CGVXDVWPQGVXDULQVXCBFDGTPUNTUOOZVXCUPUQZVWTVXBURZVWTDUSZPOZBUTOZVXBVWTVXI
      SVWLUTBVWLVHUTVWLVANUULUFZVHVAVBONVBOZVAUDVCQZNNVDQZVWLVXKVIUUBVEUDVHOVXM
      UUCUDUUDVFVXLVXNVENVGVFVANUDNUUEUUFUUGUUHZUUIUUJZVWTVXIBVWLOZVWNVXIVXQVJZ
      AVWNVXQDPUGVXRVXQVWMDEPDEVKZBCVWLLVLUUKVXQDPUUMUUNVMVNZVOZVPVWTFUSZPOZVYB
      GUKZTVYBVQUFZBDUMZRVXBVWTFPVYFGUTVWTGFPVYEBDUHZVRZFPVYFVRZJVWTFPVYGVYFVWT
      VYCSZVYEBDVYJTVYBVSZVWTVXHVYEOZVXQVYCVYLVWTVXIVXQVXHVYBWAZVXTWBVPZVTZUUOZ
      WCVYJVYEBDVYKVYJVYLSVWLUTBVXPVYNVOZUUPUUQZVPUURVXCVXDGHVWLIVWTPVWLGWDZVXB
      VWTFPVYGVWLGVYJVYGVYFVWLVYOVYJVYEBDVYKVYNUUSUUTJWEZWFVXCVXDVHOUDVXDVDQVXD
      VWLOVXCBDEPCVRZTPUNVXFVXCVXIAVXHWUAUKBRZAVWNVXBVXIWGAVXISZEVXHCBPWUAUDNUV
      AUFZWUCWUAWHEDVKZCBRZWUCVXSBCRWUEWUFLVXHEUSZWIBCWIUVBVMAVXIURZKWLZWJZVXCV
      XISZBVHOZUDBVDQZWUKVXQWULWUMSVWTVXIVXQVXBVXTVPZBWKWMZUVCZVXCGWNWUATUVDZVX
      AVWTGWUQRVXBVWTFPGWUQAGPWOZVWNAPWUDGWDZWURAFPVYGWUDGAVYCSZVYEWPOZBWUDOZDV
      YEUGVYGWUDOTVYBVQWQZWUTWVBDVYEWUTVYLSAVXIWVBAVYCVYLWRVYLVXIWUTVYMVMKWSWTV
      YEBDWPDVYEXAXDXBJWEZPWUDGUVEXCWFWUQPWOZVWTWVEWUQTXPUKZWOZVXEWVGUPWNWUATUV
      LVFPWVFWUQUNUVFXEUQVYJVYDVYFVYBWUQUKVYRVYJBDWUATVYBVYJVYLAWUBAVWNVYCVYLWG
      VYLAVXIWUBVYMWUIWBWJVYJVYBPWVFVWTVYCURUNUVGVYQUVHXFUVIWFVXGUVJZUVKVXCBDWU
      ATPUNVXFWUJWUPWVHWUKWULWUMWUOUVMUVNVXDWKUVOVWLUVPUVQUVRVXCBCDFEWUNLVXCVYH
      VXAOZVYIVXAOZVXCVYHGVXAJVXGUWAVWTWVIWVJXGVXBVWTVYHVYIVXAVYPVLWFXHUVSXIVWT
      VXBUWBZSZGNVWOVWPWVLFGHIVWTVYSWVKVYTWFZWVLVYCSZVYGTVYBTWNUFZVQUFZBDUHZVYD
      WVOGUKVDWVNBDVYBWVOWVLVYCURZWVNVYBUOOVYBVYBXPUKZOWVOWVSOWVNVYBWVRXJVYBXKV
      YBVYBUVTXLWVNVXIVWTVXQVWTWVKVYCVXIWGVXTWJUWCVWTVYCVYDVYGRWVKVYJVYDVYFVYGV
      YRVYOUWDVPWVNMWVOTMUSZVQUFZBDUHZWVQPGWUDGMPWWBVRZRWVNGVYHWWCJMFPWWBVYGMFV
      KWWAVYERWWBVYGRWVTVYBTVQXMWWAVYEBDXNXCUWEUWFUQVWTWVKVYCWVTWVORZWWBWVQRZVW
      TWVKVYCWWDUWGSWWDWWAWVPRWWEVWTWVKVYCWWDUWHWVTWVOTVQXMWWAWVPBDXNXLUWKWVNVY
      BWVRUWIWVNWVPWPOWVBDWVPUGWVQWUDOTWVOVQWQWVNWVBDWVPWVNVXHWVPOZSAVXIWVBAVWN
      WVKVYCWWFXOWWFVXIWVNVXHWVOWAVMKWSWTWVPBDWPDWVPXAXDXBWLUWJZVWTWVKURZUWLWVL
      VWOUAPUWMZXQUWNZUAUSZBDUMZVRZUWOZVBVCUWPZNVWTVWOWWORWVKVWTUAPBWWLDWPVWTDX
      RDPXAPWPOZVWTXSUQAVXIWVBVWNKVPVWTWWKWWJOZSZUWQDWWKBVRZXTUFZUWRWUDUWSUFZWW
      SXTUFZWWLWWRWWQWWKVWLWWSWDWWTWXBRVWTWWQURZWWRDWWKBVWLWWSWWRVXHWWKOZSZVWTV
      XIVXQVWTWWQWXDWRZWXEWWKPVXHWXEWWKPWXEWWJWWIWWKWWIXQUWTVWTWWQWXDYAVOUXBWWR
      WXDURUXCZVXTWSZWWSYBWEWWKWWSWWJUXAWSWWRWWKBDWWRWWJXQWWKWWIXQUXDZWXCVOWXEV
      WTVXIVXJWXFWXGVYAWSUXEUXFUXGWFWVLUBUSZUCUSZVDQZUCWWNUJZUBVHUGZWWONRZWVLWX
      MUBVHWVLWXJVHOZSZWXJWWABDUMZVDQZMPUJZWXMWXQWXJWVTGUKZVCQZMPUJZWXTWXQWXJVY
      DVCQZFWVTXPUKZUGZMPUJZWYCWVLWYGUBVHWVLUBMFGWVMWWGWWHUXHUXIWYFWYBMPWVTPOZW
      YDWYBFWVTWYEWYHWVTUOOWVTWYEOWVTUXLWVTXKXCWYHFMVKZSZVYDWYAWXJVCWYJVYBWVTGW
      YHWYIURUXJYCUXMUXKXCWXQWYBWXSMPWXQWYHSZWYBWXJWYAVDQZWXSWYKWXPWYAVHOWYBWYL
      VJWVLWXPWYHYAWYKVWLVHWYAVXOWYKPVWLWVTGWVLVYSWXPWYHWVMUXNWXQWYHURZUXOVOWXJ
      WYAUXPWSWYKWYAWXRWXJVDWYKWYAWWBWXRWYKFWVTVYGWWBPGWPGVYHRWYKJUQWYIVYGWWBRZ
      WYKWYIVYEWWARWYNVYBWVTTVQXMVYEWWABDXNXCVMWYMWWBWPOWYKWWABDUXQUQWLWYKWWABD
      WYKTWVTVSWYKVXHWWAOZSVWTVXIVXQVWTWVKWXPWYHWYOXOWYOVXIWYKVXHWVTWAVMVXTWSVT
      XFYCUXRYDUYCWXSWXMMPWXRWWNOZWXSWXMWWAWWJOZWXRWPOWYPWYQWWAWWIOZWWAXQOWYRWW
      APVIWWAWVFPTWVTUXSUNUXTWWAPTWVTVQWQUYAXETWVTUYBWWAWWIXQUYDUYEWWABDUYFUAWW
      JWWLWXRWWAWWMWPWWMYBZWWKWWABDUYGUYHYEWXLWXSUCWXRWWNWXSUCXRWXKWXRWXJVDUYMY
      FUYIUYJXCWTWVLWWJVBWWMWDWWNVBVIWXNWXOXGWVLUAWWJWWLVBWWMWVLWWQSZWWLWYTWWKB
      DWYTWWJXQWWKWXIWVLWWQURVOWYTWXDSVWLVHBVXOVWTWWQWXDVXQWVKWXHUYKVOUYLUYNWYS
      WEWWJVBWWMUYOUBUCWWNUYPXLXHXFXIUYQAVWSSZGNVWOVWPAVWSGVXHXPUKZYGZXUBNUYRZY
      IZRZDPUJZGNVWPQZAVWSXUGAVWRXUFDPWUCVWRXUFWUCVWRSZXUCVYHXUBYGZXUEGVYHXUBJU
      YSAWYHSZVWRDMUYTZSZVYHWYEYGZWYEXUDYIZRZVJXUIXUJXUERZVJMDMDVKZXUMXUIXUPXUQ
      XURXUKWUCXULVWRXURWYHVXIAWVTVXHPYJYHVWRMDVUDVUAXURXUNXUJXUOXUEXURWYEXUBVY
      HWVTVXHXPVUBZVUCXURWYEXUBXUDXUSVUEVUFYKXUMVYGNRZFWYEUGZXUPXUMXUTFWYEXUMVY
      BWYEOZSZVYEBDWPXUMXVBDXUKXULDXUKDXRVWRDMVUGZYLXVBDXRYLWVAXVCWVCUQXVCVYLSA
      VXIWVBAWYHXULXVBVYLXOVYLVXIXVCVYMVMKWSXVCWVTVYEOZXULVWRDVYEUJXUMXVBWYHXVE
      AWYHXULXVBVUHWYHWVTWVFOXVBXVEWVTVUIWVTTVYBVUJVUNWJXUKXULXVBYAVWRXULDWVTVY
      EXVDVWRDMVUKYFWSYMWTXUMXVASZFWYEVYGVRZFWYENVRZXUNXUOXUMWYEWYERXVAXVGXVHRX
      UMWYEWHFWYEVYGWYENVULVUMXUMXUNXVGRZXVAXUMWYHWYEPVIXVIAWYHXULYAWVTVUOFPWYE
      VYGVVDXLWFXUOXVHRXVFFWYENVUPUQVUQVURYNWCYOYDVNAXUGXUHAXUFXUHDPWUCXUFXUHWU
      CXUFXUCNVWPQZXUHWUCXUENVWPQZXUFXVJWUCHWUDYPUKZOZNWUDOZVXHUOOXVKXVMWUCHVDV
      USUKZWUDVUTUFZXVLHWXAVVAUKXVPIVVBVVCXVOVBYPUKOWUDVBVIXVPXVLOVVEUDNVVFWUDX
      VOVBVVNYEVVGUQZXVNWUCUDVBOZVXLUDNVDQZXVNYQVEXVRXVSYQUDVGVFZUDNVVHYRUQWUCV
      XHWUHXJZNHVXHWUDXUBXUBYBVVIVVJXUFXVJXVKXUCXUENVWPVVKVVLVVMWUCXUHXVJWUCNGH
      VXHWUDXVQWUCWUDWPOUTWPOZWUSPUTVIZGWUDUTVVOUFOWUCHYPWUDXVQVVPXWBWUCVVQUQAW
      USVXIWVDWFXWCWUCVVRUQWUDUTPGWPWPVVSVVTXWAVWAVWBYSYOVWCVNYSXUAPBDWPAVWSDAD
      XRVWRDPVWDYLWWPXUAXSUQAVXIWVBVWSKVPAVWSURYMXIAVWNCNRZEPUJZYTZVWNVWSYTAVWM
      XWDYTZEPUGXWFAXWGEPAWUGPOZSZCWUDOZXWGWUCWVBVJXWIXWJVJDEVXSWUCXWIWVBXWJVXS
      VXIXWHAVXHWUGPYJYHVXSBCWUDLVLYKKYNXVRVXLXVSXWJXWGXGYQVEXVTUDNCVWEYRWMWTVW
      MXWDEPVWFXCVWSXWEVWNVWRXWDDEPVXSBCNLVWGVWHVWIVWJVWK $.
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
      ( vi cn c1 cv cfz cesum wceq co cmpt clm cfv cbvesumv esumeq1 syl syl5eqr
      oveq2 cbvmptv esumcvg syl5eqbrr ) AGOPGQZRUAZBESZUBNOPNQZRUAZDFSZUBZOBESH
      UCUDNGOURUOUPUMTZURUQBESZUOUQBDEFMUEUTUQUNTVAUOTUPUMPRUIUQUNBEUFUGUHUJZAB
      CEIGUSHJVBKLUKUL $.
  $}

